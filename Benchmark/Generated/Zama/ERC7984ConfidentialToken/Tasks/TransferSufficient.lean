import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
When the sender has sufficient balance, transfer moves exactly `amount` tokens.

If `balances[from] >= amount`, then:
- `balances[from]` decreases by `amount`
- `balances[to]` increases by `amount` (mod 2^64)
-/
theorem transfer_sufficient
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hSufficient : s.storageMap 1 sender >= amount)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    let s' := ((ERC7984.transfer sender recipient amount).run s).snd
    transfer_sufficient_spec sender recipient amount s s' := by
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
  have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
    simpa using hSufficient
  unfold transfer_sufficient_spec balanceOf
  dsimp
  intro _
  constructor
  · simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit,
      hSufficient', hDistinct]
  · have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
    simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit,
      hSufficient', hDistinct, hDistinct']

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
