import Verity.Specs.Common
import Benchmark.Cases.Reserve.AuctionPriceBand.Contract

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/--
  Boundary exactness at `startTime`.

  At `currentTime = startTime`, `_price` returns exactly `startPrice`
  (RebalancingLib.sol:451-453).
-/
def price_at_start_time_spec
    (sellLow sellHigh buyLow buyHigh startTime endTime : Uint256) : Prop :=
  price sellLow sellHigh buyLow buyHigh startTime endTime startTime
    = startPrice sellHigh buyLow

/--
  Boundary exactness at `endTime`.

  At `currentTime = endTime` (and `endTime ≠ startTime`), `_price`
  returns exactly `endPrice` (RebalancingLib.sol:457-459).
-/
def price_at_end_time_spec
    (sellLow sellHigh buyLow buyHigh startTime endTime : Uint256) : Prop :=
  price sellLow sellHigh buyLow buyHigh startTime endTime endTime
    = endPrice sellLow buyHigh

/--
  Lower bound of the band invariant: `endPrice ≤ price`.

  This is the floor that protects the bidder side: the per-pair price
  never drops below the `endPrice` the launcher published.

  In the interior branch the bound is enforced by the explicit
  `if (p < endPrice) p = endPrice;` clamp at line 472-474. In the
  boundary branches it is recovered from `hBand`.
-/
def price_lower_bound_spec
    (sellLow sellHigh buyLow buyHigh startTime endTime currentTime : Uint256) : Prop :=
  endPrice sellLow buyHigh
    ≤ price sellLow sellHigh buyLow buyHigh startTime endTime currentTime

/--
  Upper bound of the band invariant: `price ≤ startPrice`.

  This is the ceiling that protects the protocol side: the per-pair
  price never rises above the `startPrice` the launcher published.

  In the boundary branches the bound is recovered from the structure of
  `_price`. In the interior branch it relies on the algebraic axiom
  `exp_nonpositive_le_d18`: since `exp(-k * elapsed) ≤ D18`, the
  ceil-divided product `mulDivUp startPrice (exp ...) D18 ≤ startPrice`.
-/
def price_upper_bound_spec
    (sellLow sellHigh buyLow buyHigh startTime endTime currentTime : Uint256) : Prop :=
  price sellLow sellHigh buyLow buyHigh startTime endTime currentTime
    ≤ startPrice sellHigh buyLow

/--
  The band is well-formed: `endPrice ≤ startPrice`. This falls out of
  the input bounds the auction launcher establishes in `openAuction` /
  `startRebalance` (`sellLow ≤ sellHigh` and `buyLow ≤ buyHigh`).

  This is a *helper* spec that downstream proofs of the upper bound can
  consume to discharge their `hBand` precondition.
-/
def band_well_formed_spec
    (sellLow sellHigh buyLow buyHigh : Uint256) : Prop :=
  endPrice sellLow buyHigh ≤ startPrice sellHigh buyLow

end Benchmark.Cases.Reserve.AuctionPriceBand
