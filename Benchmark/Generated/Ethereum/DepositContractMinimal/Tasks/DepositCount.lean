import Benchmark.Cases.Ethereum.DepositContractMinimal.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Ethereum.DepositContractMinimal

open Verity
open Verity.EVM.Uint256

private theorem deposit_small_slot_write
    (depositAmount : Uint256) (s : ContractState)
    (hCount : s.storage 0 < 4294967295)
    (hMin : depositAmount >= 1000000000)
    (hSmall : depositAmount < 32000000000) :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    s'.storage 0 = add (s.storage 0) 1 := by
  have hNotFull : ¬ 32000000000 ≤ depositAmount := Nat.not_le_of_lt hSmall
  simp [DepositContractMinimal.deposit, hCount, hMin, hNotFull,
    DepositContractMinimal.depositCount, getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]

private theorem deposit_full_slot_write
    (depositAmount : Uint256) (s : ContractState)
    (hCount : s.storage 0 < 4294967295)
    (hMin : depositAmount >= 1000000000)
    (hFull : depositAmount >= 32000000000) :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    s'.storage 0 = add (s.storage 0) 1 := by
  by_cases hThreshold : add (s.storage 1) 1 = 65536
  · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
      DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
      DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
      Bind.bind, Contract.run, ContractResult.snd]
  · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
      DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
      getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd]

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
  by_cases hFull : depositAmount >= 32000000000
  · exact deposit_full_slot_write depositAmount s hCount hMin hFull
  · have hSmall : depositAmount < 32000000000 := Nat.lt_of_not_ge hFull
    exact deposit_small_slot_write depositAmount s hCount hMin hSmall

end Benchmark.Cases.Ethereum.DepositContractMinimal
