import Benchmark.Cases.Reserve.AuctionPriceBand.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-! ## Boundary exactness -/

/--
At `currentTime = startTime`, `_price` returns `startPrice` directly
(RebalancingLib.sol:451-453). Holds unconditionally.
-/
theorem price_at_start_time_main
    (sellLow sellHigh buyLow buyHigh startTime endTime : Uint256) :
    price_at_start_time_spec sellLow sellHigh buyLow buyHigh startTime endTime := by
  unfold price_at_start_time_spec price
  simp

/--
At `currentTime = endTime` and `startTime ≠ endTime`, `_price` returns
`endPrice` directly (RebalancingLib.sol:457-459). The hypothesis
excludes the atomic-swap edge where `startTime = endTime`; in that
edge the function returns `startPrice`, but `startPrice = endPrice`
holds because the auction launcher set `prices[i].low = prices[i].high`.
-/
theorem price_at_end_time_main
    (sellLow sellHigh buyLow buyHigh startTime endTime : Uint256)
    (hStartNeEnd : startTime ≠ endTime) :
    price_at_end_time_spec sellLow sellHigh buyLow buyHigh startTime endTime := by
  unfold price_at_end_time_spec price
  have h : (endTime == startTime) = false := by
    simpa [beq_iff_eq] using fun h => hStartNeEnd h.symm
  simp [h]

/-! ## Lower bound: endPrice ≤ price -/

/--
The band invariant lower bound: `endPrice ≤ price` for any timestamp.

Branch analysis:
- At `currentTime = startTime`: result = `startPrice`, which dominates
  `endPrice` by the `hBand` precondition.
- At `currentTime = endTime`: result = `endPrice`, trivially.
- Interior branch: result = `if lt p endPrice then endPrice else p`,
  which is `≥ endPrice` by the explicit clamp at line 472-474.
-/
theorem price_lower_bound_main
    (sellLow sellHigh buyLow buyHigh startTime endTime currentTime : Uint256)
    (hBand : endPrice sellLow buyHigh ≤ startPrice sellHigh buyLow) :
    price_lower_bound_spec sellLow sellHigh buyLow buyHigh startTime endTime currentTime := by
  unfold price_lower_bound_spec price
  by_cases h1 : currentTime == startTime
  · simp [h1]
    exact hBand
  · by_cases h2 : currentTime == endTime
    · simp [h1, h2]
    · simp [h1, h2]
      -- Interior branch: result = if p < eP then eP else p.
      -- In either sub-case, eP ≤ result.
      split
      · exact Nat.le_refl _
      · rename_i hNotLt
        exact Nat.not_lt.mp hNotLt

/-! ## Upper bound: price ≤ startPrice -/

/--
Helper: `mulDivUp a b c ≤ a` whenever `b ≤ c` and the EVM-mul / EVM-add
do not wrap.

This is the algebraic core of the upper-bound proof on the interior
branch: with `b = exp(-k * elapsed) ≤ D18 = c`, the ceil-div product
`mulDivUp startPrice b D18 ≤ startPrice`.
-/
private theorem mulDivUp_le_self_of_le
    (a b c : Uint256)
    (hBC : b ≤ c)
    (hCPos : c.val > 0)
    (hNoOverflow : a.val * c.val + c.val - 1 < Verity.Core.Uint256.modulus) :
    mulDivUp a b c ≤ a := by
  -- TODO[Phase 3]: discharge via the EVM Uint256 arithmetic in
  -- Verity.Core.Uint256 + Nat ceil-division algebra. Sketch:
  --   mulDivUp a b c = ⌈a * b / c⌉ (under hNoOverflow).
  --   Since b ≤ c and a * b ≤ a * c (under hNoOverflow), we get
  --   ⌈a * b / c⌉ ≤ ⌈a * c / c⌉ = a.
  -- The proof shape mirrors `Verity/Core/Uint256/mulDivUp_le_*` lemmas
  -- once they exist; for v1 we mark it as a Phase 3 TODO.
  sorry

/--
The band invariant upper bound: `price ≤ startPrice` for any timestamp,
given a well-formed band and interior-branch safety bounds.

Branch analysis:
- At `currentTime = startTime`: result = `startPrice`, trivially ≤.
- At `currentTime = endTime`: result = `endPrice`, ≤ `startPrice` by `hBand`.
- Interior branch: result = `if lt p eP then eP else p`.
  * eP-branch: ≤ `startPrice` by `hBand`.
  * p-branch: `p = mulDivUp startPrice (exp negKE) D18`. By
    `exp_nonpositive_le_d18` applied to `negKE` (which is ≤ 0 because
    `(k * elapsed).val ≤ MAX_INT256`), we have `exp negKE ≤ D18`. Then
    by `mulDivUp_le_self_of_le`, `p ≤ startPrice`.
-/
theorem price_upper_bound_main
    (sellLow sellHigh buyLow buyHigh startTime endTime currentTime : Uint256)
    (hBand : endPrice sellLow buyHigh ≤ startPrice sellHigh buyLow)
    (_hSafe : InteriorSafe sellLow sellHigh buyLow buyHigh startTime endTime currentTime) :
    price_upper_bound_spec sellLow sellHigh buyLow buyHigh startTime endTime currentTime := by
  -- TODO[Phase 3]: discharge using `mulDivUp_le_self_of_le` and
  -- `exp_nonpositive_le_d18`. Branch on `currentTime == startTime`,
  -- `currentTime == endTime`, and the interior path.
  sorry

/-! ## Aliases expected by task manifests -/

abbrev price_at_start_time := @price_at_start_time_main
abbrev price_at_end_time := @price_at_end_time_main
abbrev price_lower_bound := @price_lower_bound_main
abbrev price_upper_bound := @price_upper_bound_main

end Benchmark.Cases.Reserve.AuctionPriceBand
