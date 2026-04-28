import Benchmark.Cases.Reserve.AuctionPriceBand.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-! ## Boundary exactness -/

/--
At `block_timestamp = auction_startTime`, `_price` returns the launcher-published
`startPrice` directly (RebalancingLib.sol:451-453). Holds unconditionally.
-/
theorem price_at_start_time_main
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime : Uint256) :
    price_at_start_time_spec sellPrices buyPrices auction_startTime auction_endTime := by
  unfold price_at_start_time_spec _price
  simp

/--
At `block_timestamp = auction_endTime` and `auction_startTime ≠ auction_endTime`,
`_price` returns the launcher-published `endPrice` directly (RebalancingLib.sol:
457-459). The hypothesis excludes the atomic-swap edge where the two timestamps
coincide; in that edge the function returns `startPrice` and the Solidity
launcher set `prices[i].low = prices[i].high`, making `startPrice = endPrice`.
-/
theorem price_at_end_time_main
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime : Uint256)
    (hStartNeEnd : auction_startTime ≠ auction_endTime) :
    price_at_end_time_spec sellPrices buyPrices auction_startTime auction_endTime := by
  unfold price_at_end_time_spec _price
  have h : (auction_endTime == auction_startTime) = false := by
    simpa [beq_iff_eq] using fun h => hStartNeEnd h.symm
  simp [h]

/-! ## Lower bound: endPrice ≤ p -/

/--
Band invariant lower bound: `endPrice ≤ p` for any timestamp, given a
well-formed band `endPrice ≤ startPrice`.

Branches:
- At `block_timestamp = auction_startTime`: result = `startPrice`, dominates
  `endPrice` by `hBand`.
- At `block_timestamp = auction_endTime`: result = `endPrice`, trivially.
- Interior: result = `if p < endPrice then endPrice else p`, ≥ `endPrice`
  by the explicit clamp at L472-474.
-/
theorem price_lower_bound_main
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256)
    (hBand :
      mulDivUp sellPrices.low D27 buyPrices.high
        ≤ mulDivUp sellPrices.high D27 buyPrices.low) :
    price_lower_bound_spec sellPrices buyPrices auction_startTime auction_endTime block_timestamp := by
  unfold price_lower_bound_spec _price
  by_cases h1 : block_timestamp == auction_startTime
  · simpa [h1] using hBand
  · by_cases h2 : block_timestamp == auction_endTime
    · simp [h1, h2]
    · simp [h1, h2]
      -- Interior: if p < endPrice then endPrice else p, with endPrice ≤ result
      split
      · exact Nat.le_refl _
      · rename_i hNotLt
        exact Nat.not_lt.mp hNotLt

/-! ## Upper bound: p ≤ startPrice -/

/--
Helper: `mulDivUp a b c ≤ a` whenever `b ≤ c`, the EVM ops do not wrap, and
`c > 0`. The algebraic core of the upper-bound proof on the interior branch.

TODO[Phase 3]: discharge via the Nat ceil-division algebra
`⌈a*b/c⌉ ≤ ⌈a*c/c⌉ = a` when `b ≤ c`.
-/
private theorem mulDivUp_le_self_of_le
    (a b c : Uint256)
    (_hBC : b ≤ c)
    (_hCPos : c.val > 0)
    (_hNoOverflow : a.val * c.val + c.val - 1 < Verity.Core.Uint256.modulus) :
    mulDivUp a b c ≤ a := by
  sorry

/--
Band invariant upper bound: `p ≤ startPrice` for any timestamp.

Branches:
- At `block_timestamp = auction_startTime`: result = `startPrice`, trivially.
- At `block_timestamp = auction_endTime`: result = `endPrice`, ≤ `startPrice`
  by `hBand`.
- Interior: result = `if p < endPrice then endPrice else p`. Both sub-cases:
  endPrice-branch ≤ startPrice by `hBand`; p-branch ≤ startPrice via
  `MathLib_exp_nonpositive_le_D18` + `mulDivUp_le_self_of_le`.

TODO[Phase 3]: case-split on the three branches and discharge using the
helpers above.
-/
theorem price_upper_bound_main
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256)
    (_hBand :
      mulDivUp sellPrices.low D27 buyPrices.high
        ≤ mulDivUp sellPrices.high D27 buyPrices.low)
    (_hSafe : InteriorSafe sellPrices buyPrices auction_startTime auction_endTime block_timestamp) :
    price_upper_bound_spec sellPrices buyPrices auction_startTime auction_endTime block_timestamp := by
  sorry

/-! ## Aliases expected by task manifests -/

abbrev price_at_start_time := @price_at_start_time_main
abbrev price_at_end_time := @price_at_end_time_main
abbrev price_lower_bound := @price_lower_bound_main
abbrev price_upper_bound := @price_upper_bound_main

end Benchmark.Cases.Reserve.AuctionPriceBand
