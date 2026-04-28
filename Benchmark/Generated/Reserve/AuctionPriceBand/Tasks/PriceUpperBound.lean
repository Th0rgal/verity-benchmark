import Benchmark.Cases.Reserve.AuctionPriceBand.Specs

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256

/--
The band invariant upper bound: `price ≤ startPrice` for any timestamp,
given a well-formed band and the interior-branch overflow / fixed-point
safety bounds bundled in `InteriorSafe`.
-/
theorem price_upper_bound
    (sellLow sellHigh buyLow buyHigh startTime endTime currentTime : Uint256)
    (hBand : endPrice sellLow buyHigh ≤ startPrice sellHigh buyLow)
    (hSafe : InteriorSafe sellLow sellHigh buyLow buyHigh startTime endTime currentTime) :
    price_upper_bound_spec sellLow sellHigh buyLow buyHigh startTime endTime currentTime := by
  exact ?_

end Benchmark.Cases.Reserve.AuctionPriceBand
