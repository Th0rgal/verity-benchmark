import Benchmark.Cases.Reserve.AuctionPriceBand.Specs

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256

/--
At `currentTime = endTime` and `startTime ≠ endTime`, `_price` returns `endPrice`.
-/
theorem price_at_end_time
    (sellLow sellHigh buyLow buyHigh startTime endTime : Uint256)
    (hStartNeEnd : startTime ≠ endTime) :
    price_at_end_time_spec sellLow sellHigh buyLow buyHigh startTime endTime := by
  exact ?_

end Benchmark.Cases.Reserve.AuctionPriceBand
