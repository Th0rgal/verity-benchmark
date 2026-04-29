import Verity.Specs.Common
import Benchmark.Cases.Reserve.AuctionPriceBand.Contract

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Specs for `_price` (Reserve DTF Protocol RebalancingLib._price).

  Each spec re-states an invariant about the function's return value using
  the same identifier names as the Solidity source (per the Solidity-mirror
  convention). Spec expressions inline the same `mulDivUp sellPrices.high D27
  buyPrices.low` form that the Solidity uses; we do not introduce abbreviations.
-/

/--
Boundary exactness at `block.timestamp == auction.startTime`.
Solidity (L451-453): `if (block.timestamp == auction.startTime) return startPrice;`.
-/
def price_at_start_time_spec
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime : Uint256) : Prop :=
  _price sellPrices buyPrices auction_startTime auction_endTime auction_startTime
    = mulDivUp sellPrices.high D27 buyPrices.low

/--
Boundary exactness at `block.timestamp == auction.endTime` (when not also
the start, i.e. the auction is not atomic-swap).
Solidity (L457-459): `if (block.timestamp == auction.endTime) return endPrice;`.
-/
def price_at_end_time_spec
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime : Uint256) : Prop :=
  _price sellPrices buyPrices auction_startTime auction_endTime auction_endTime
    = mulDivUp sellPrices.low D27 buyPrices.high

/--
Lower bound of the band invariant: `endPrice ≤ p` for any timestamp.
Floor that protects the bidder side: the per-pair price never drops below
the `endPrice` the launcher published. In the interior branch the bound is
enforced by the explicit clamp `if (p < endPrice) p = endPrice;` (L472-474).
-/
def price_lower_bound_spec
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256) : Prop :=
  mulDivUp sellPrices.low D27 buyPrices.high
    ≤ _price sellPrices buyPrices auction_startTime auction_endTime block_timestamp

/--
Upper bound of the band invariant: `p ≤ startPrice` for any timestamp.
Ceiling that protects the protocol side: the per-pair price never rises
above the `startPrice` the launcher published. In the interior branch the
bound relies on `MathLib_exp_nonpositive_le_D18` plus `mulDivUp` ceil-division
algebra.
-/
def price_upper_bound_spec
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256) : Prop :=
  _price sellPrices buyPrices auction_startTime auction_endTime block_timestamp
    ≤ mulDivUp sellPrices.high D27 buyPrices.low

/--
Helper invariant: the band is well-formed (`endPrice ≤ startPrice`). Falls
out of the input bounds the auction launcher establishes in `openAuction` /
`startRebalance` (`sellPrices.low ≤ sellPrices.high`,
`buyPrices.low ≤ buyPrices.high`).
-/
def band_well_formed_spec
    (sellPrices buyPrices : PriceRange) : Prop :=
  mulDivUp sellPrices.low D27 buyPrices.high ≤ mulDivUp sellPrices.high D27 buyPrices.low

end Benchmark.Cases.Reserve.AuctionPriceBand
