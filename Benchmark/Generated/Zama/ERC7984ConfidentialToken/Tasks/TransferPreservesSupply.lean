import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Transfer does not modify totalSupply.

The transfer function only writes to balances (storageMap slot 1) and
balanceInitialized (storageMap slot 2). It never touches slot 0 (totalSupply).
Only mint and burn paths modify totalSupply.
-/
theorem transfer_preserves_supply
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    let s' := ((ERC7984.transfer sender recipient amount).run s).snd
    transfer_preserves_supply_spec s s' := by
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
  unfold transfer_preserves_supply_spec supply
  simp [ERC7984.transfer, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
