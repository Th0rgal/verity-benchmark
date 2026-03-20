import Benchmark.Cases.Ethereum.DepositContractMinimal.Specs

namespace Benchmark.Cases.Ethereum.DepositContractMinimal

open Verity
open Verity.EVM.Uint256

private theorem slot_write_helper
    (depositAmount : Uint256) (s : ContractState)
    (hCount : s.storage 0 < 4294967295)
    (hMin : depositAmount >= 1000000000) :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    s'.storage 0 = add (s.storage 0) 1 := by
  simp [DepositContractMinimal.deposit,
        getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
        Contract.run, ContractResult.snd,
        hCount, hMin]

/--
Executing `deposit` on the successful path increments the total deposit counter
by exactly one.
-/
theorem deposit_increments_deposit_count
    (depositAmount : Uint256) (s : ContractState)
    (hCount : s.storage 0 < 4294967295)
    (hMin : depositAmount >= 1000000000) :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    deposit_increments_deposit_count_spec s s' := by
  unfold deposit_increments_deposit_count_spec
  simpa using slot_write_helper depositAmount s hCount hMin

end Benchmark.Cases.Ethereum.DepositContractMinimal
