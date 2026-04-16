import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Transfer conserves the sum of sender and receiver balances.

After transfer(from, to, amount), `balances[from] + balances[to]` is unchanged.
This holds regardless of whether the sender has sufficient balance:
- Sufficient: from loses `amount`, to gains `amount` → sum preserved
- Insufficient: both balances unchanged → sum trivially preserved

This is the fundamental accounting invariant for any token.
-/
theorem transfer_conservation
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD)
    (hToNoWrap : s.storageMap 1 recipient + amount < UINT64_MOD) :
    let s' := ((ERC7984.transfer sender recipient amount).run s).snd
    transfer_conservation_spec sender recipient s s' := by
  have hSenderNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  have hSenderNZ : sender ≠ (0 : Address) := by
    simpa [zeroAddress] using hSenderNe
  have hRecipientNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  have hRecipientNZ : recipient ≠ (0 : Address) := by
    simpa [zeroAddress] using hRecipientNe
  unfold transfer_conservation_spec balanceOf
  by_cases hSufficient : s.storageMap 1 sender >= amount
  · dsimp
    have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
      simpa using hSufficient
    simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit, hSufficient',
      hDistinct, Ne.symm hDistinct]
    have hToAddMod : (s.storageMap 1 recipient + amount) % 18446744073709551616 =
        s.storageMap 1 recipient + amount := by
      cases hBal : s.storageMap 1 recipient + amount with
      | mk val hlt =>
          have hToNoWrap' : val < 18446744073709551616 := by
            simpa [hBal, UINT64_MOD] using hToNoWrap
          show (({ val := val, isLt := hlt } : Uint256) % 18446744073709551616) =
              ({ val := val, isLt := hlt } : Uint256)
          apply Verity.Core.Uint256.ext
          change (val % 18446744073709551616) % Verity.Core.Uint256.modulus = val
          rw [Nat.mod_eq_of_lt hToNoWrap']
          exact Nat.mod_eq_of_lt hlt
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [hToAddMod]
    calc
      sub (s.storageMap 1 sender) amount + (s.storageMap 1 recipient + amount)
          = (sub (s.storageMap 1 sender) amount + amount) + s.storageMap 1 recipient := by
              rw [Verity.Core.Uint256.add_comm (s.storageMap 1 recipient) amount]
              rw [← Verity.Core.Uint256.add_assoc]
      _ = s.storageMap 1 sender + s.storageMap 1 recipient := by
            change ((s.storageMap 1 sender - amount) + amount) + s.storageMap 1 recipient =
              s.storageMap 1 sender + s.storageMap 1 recipient
            rw [Verity.Core.Uint256.sub_add_cancel_left]
  · dsimp
    have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
      simpa using hSufficient
    simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit, hInsufficient',
      hDistinct, Ne.symm hDistinct, hToBal64]
    have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 = s.storageMap 1 recipient := by
      rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd, Verity.Core.Uint256.add_zero]
      cases hBal : s.storageMap 1 recipient with
      | mk val hlt =>
          have hToBal64' : val < 18446744073709551616 := by
            simpa [hBal, UINT64_MOD] using hToBal64
          show (({ val := val, isLt := hlt } : Uint256) % 18446744073709551616) =
              ({ val := val, isLt := hlt } : Uint256)
          apply Verity.Core.Uint256.ext
          change (val % 18446744073709551616) % Verity.Core.Uint256.modulus = val
          rw [Nat.mod_eq_of_lt hToBal64']
          exact Nat.mod_eq_of_lt hlt
    rw [hZeroAddMod]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
