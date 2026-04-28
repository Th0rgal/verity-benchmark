import Benchmark.Cases.Reserve.AuctionPriceBand.Specs

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256

/--
At `currentTime = startTime`, `_price` returns `startPrice`.
-/
theorem price_at_start_time
    (sellLow sellHigh buyLow buyHigh startTime endTime : Uint256) :
    price_at_start_time_spec sellLow sellHigh buyLow buyHigh startTime endTime := by
  exact ?_

end Benchmark.Cases.Reserve.AuctionPriceBand
