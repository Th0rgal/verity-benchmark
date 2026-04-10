import Benchmark.Cases.NexusMutual.RammPriceBand.Proofs

namespace Benchmark.Cases.NexusMutual.RammPriceBand

open Verity
open Verity.EVM.Uint256

/--
Executing `syncPriceBand` stores the synchronized sell quote.
-/
theorem syncPriceBand_sets_sell_price
    (capital_ supply_ : Uint256) (s : ContractState)
    (hSupply : supply_ != 0) :
    let s' := ((RammPriceBand.syncPriceBand capital_ supply_).run s).snd
    syncPriceBand_sets_sell_price_spec capital_ supply_ s s' := by
  exact syncPriceBand_sets_sell_price_main capital_ supply_ s hSupply

end Benchmark.Cases.NexusMutual.RammPriceBand
