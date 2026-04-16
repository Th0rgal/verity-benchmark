import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Transfer never reverts based on balance sufficiency.

Given that all plaintext preconditions hold (non-zero addresses,
initialized sender balance), the transfer always succeeds — it
returns `ContractResult.success`, never `ContractResult.revert`.

This is the contract-level non-leakage invariant for ERC-7984:
an on-chain observer cannot learn whether the sender had sufficient
balance by checking if the transaction reverted. The only reverts
come from plaintext checks (zero address, uninitialized balance).

Note: NO hypothesis about `fromBalance >= amount` is provided.
The theorem must hold for BOTH sufficient and insufficient balances.
-/
theorem transfer_no_balance_revert
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    transfer_no_balance_revert_spec sender recipient amount s := by
  let _ := hDistinct
  let _ := hAmount64
  let _ := hFromBal64
  let _ := hToBal64
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
  unfold transfer_no_balance_revert_spec
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess,
    hSenderNZ, hRecipientNZ, hInit]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
