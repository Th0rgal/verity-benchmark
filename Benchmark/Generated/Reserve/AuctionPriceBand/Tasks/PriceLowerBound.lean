import Benchmark.Cases.Reserve.AuctionPriceBand.Specs

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256

/--
The band invariant lower bound: `endPrice ≤ price` for any timestamp,
given a well-formed band `endPrice ≤ startPrice`.
-/
theorem price_lower_bound
    (sellLow sellHigh buyLow buyHigh startTime endTime currentTime : Uint256)
    (hBand : endPrice sellLow buyHigh ≤ startPrice sellHigh buyLow) :
    price_lower_bound_spec sellLow sellHigh buyLow buyHigh startTime endTime currentTime := by
  exact ?_

end Benchmark.Cases.Reserve.AuctionPriceBand
