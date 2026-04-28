import Benchmark.Cases.Reserve.AuctionPriceBand.Specs
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.Math
import Mathlib.Tactic.Set

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Verity.Proofs.Stdlib.Math

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
If a Uint256 fits inside the positive Int256 half-range, then casting it
to Int256 and negating produces a non-positive Int256 (in `toInt` form).

Used to discharge the precondition of `MathLib_exp_nonpositive_le_D18`
when the negation `Int256.neg (Int256.ofUint256 (mul k elapsed))` is
applied to a Uint256 bounded by `MAX_INT256`.
-/
private theorem neg_ofUint256_toInt_nonpositive
    (v : Uint256)
    (hFits : v.val ≤ Verity.EVM.MAX_INT256.toNat) :
    Verity.EVM.Int256.toInt
      (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)) ≤ 0 := by
  -- v.val ≤ MAX_INT256.toNat = signBit - 1, so v.val < signBit.
  have hSigBit : v.val < Verity.Core.Int256.signBit := by
    have h : Verity.EVM.MAX_INT256.toNat = Verity.Core.Int256.signBit - 1 := by
      decide
    rw [h] at hFits
    have : 0 < Verity.Core.Int256.signBit := by decide
    omega
  have hVLtMod : v.val < Verity.Core.Uint256.modulus := v.isLt
  have hMod : Verity.Core.Uint256.modulus = 2 * Verity.Core.Int256.signBit := by
    decide
  -- The word of `Int256.neg (Int256.ofUint256 v)` is `Uint256.ofNat (modulus - v.val)`.
  -- Branch on v.val = 0.
  by_cases hZero : v.val = 0
  · -- v.val = 0. modulus - 0 = modulus. Word val = modulus % modulus = 0 < signBit.
    -- toInt = 0.
    have hWordEqZero :
        (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val = 0 := by
      show (Verity.Core.Uint256.ofNat
              (Verity.Core.Int256.modulus
                - (Verity.Core.Int256.ofUint256 v).word.val)).val = 0
      have hOfUint : (Verity.Core.Int256.ofUint256 v).word = v := rfl
      rw [hOfUint, hZero]
      show (Verity.Core.Uint256.ofNat (Verity.Core.Int256.modulus - 0)).val = 0
      simp [Verity.Core.Uint256.ofNat, Verity.Core.Int256.modulus]
    have hLt :
        (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val
          < Verity.Core.Int256.signBit := by
      rw [hWordEqZero]; decide
    show Verity.Core.Int256.toInt _ ≤ 0
    have hSigBitPos : 0 < Verity.Core.Int256.signBit := by decide
    simp [Verity.Core.Int256.toInt, hLt, hWordEqZero, hSigBitPos]
  · -- 0 < v.val < signBit. modulus - v.val ∈ (signBit, modulus).
    -- Word val = modulus - v.val (no wrap), and ≥ signBit + 1 > signBit.
    -- toInt = (modulus - v.val) - modulus = -v.val ≤ 0.
    have hVPos : 0 < v.val := Nat.pos_of_ne_zero hZero
    have hSubLt :
        Verity.Core.Int256.modulus - v.val < Verity.Core.Uint256.modulus := by
      show Verity.Core.Uint256.modulus - v.val < Verity.Core.Uint256.modulus
      omega
    have hWordVal :
        (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val
          = Verity.Core.Int256.modulus - v.val := by
      show (Verity.Core.Uint256.ofNat
              (Verity.Core.Int256.modulus
                - (Verity.Core.Int256.ofUint256 v).word.val)).val
            = Verity.Core.Int256.modulus - v.val
      have hOfUint : (Verity.Core.Int256.ofUint256 v).word = v := rfl
      rw [hOfUint]
      show (Verity.Core.Uint256.ofNat
              (Verity.Core.Int256.modulus - v.val)).val
            = Verity.Core.Int256.modulus - v.val
      simp [Verity.Core.Uint256.ofNat,
            Nat.mod_eq_of_lt hSubLt]
    have hGe :
        Verity.Core.Int256.signBit
          ≤ (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val := by
      rw [hWordVal]
      show Verity.Core.Int256.signBit ≤ Verity.Core.Uint256.modulus - v.val
      omega
    show Verity.Core.Int256.toInt _ ≤ 0
    have hNotLt :
        ¬ ((Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val
              < Verity.Core.Int256.signBit) :=
      Nat.not_lt_of_ge hGe
    simp only [Verity.Core.Int256.toInt, hNotLt, if_false]
    -- Goal: Int.ofNat (...word.val) - Int.ofNat modulus ≤ 0
    rw [hWordVal]
    -- Goal: Int.ofNat (modulus - v.val) - Int.ofNat modulus ≤ 0
    have hVLe : v.val ≤ Verity.Core.Int256.modulus := by
      show v.val ≤ Verity.Core.Uint256.modulus
      omega
    -- The goal is `Int.ofNat (modulus - v.val) - Int.ofNat modulus ≤ 0`.
    -- Replace `Int.ofNat (modulus - v.val)` by `Int.ofNat modulus - Int.ofNat v.val`
    -- explicitly. The push_cast simp lemma `Int.ofNat_sub` is the right rewriter.
    have hCastEq :
        Int.ofNat (Verity.Core.Int256.modulus - v.val)
          = Int.ofNat Verity.Core.Int256.modulus - Int.ofNat v.val := by
      have := Int.ofNat_sub hVLe
      simpa using this
    rw [hCastEq]
    -- Goal: ↑modulus - ↑v.val - ↑modulus ≤ 0, simplifies to -v.val ≤ 0 in Int.
    have hVNonneg : (0 : Int) ≤ Int.ofNat v.val := Int.natCast_nonneg _
    omega

/--
Helper: `mulDivUp a b c ≤ a` whenever `b ≤ c`, the EVM ops do not wrap, and
`c > 0`. The algebraic core of the upper-bound proof on the interior branch.

TODO[Phase 3]: discharge via the Nat ceil-division algebra
`⌈a*b/c⌉ ≤ ⌈a*c/c⌉ = a` when `b ≤ c`.
-/
private theorem mulDivUp_le_self_of_le
    (a b c : Uint256)
    (hBC : b ≤ c)
    (hCPos : c.val > 0)
    (hNoOverflow : a.val * c.val + c.val - 1 < Verity.Core.Uint256.modulus) :
    mulDivUp a b c ≤ a := by
  -- Lift to Nat: (mulDivUp a b c).val ≤ a.val
  show (mulDivUp a b c).val ≤ a.val
  -- Key fact: mulDivUp evaluates exactly because the numerator does not wrap.
  have hC : c ≠ 0 := by
    intro h
    apply Nat.lt_irrefl 0
    have : c.val = 0 := by
      simpa using congrArg (fun x : Uint256 => x.val) h
    omega
  have hBC_nat : b.val ≤ c.val := hBC
  have hAB_le_AC : a.val * b.val ≤ a.val * c.val :=
    Nat.mul_le_mul_left a.val hBC_nat
  have hCPred : c.val - 1 + 1 = c.val := Nat.succ_pred_eq_of_pos hCPos
  have hMaxEq : Verity.Core.Uint256.modulus = MAX_UINT256 + 1 := by
    decide
  have hNumLeMax : a.val * b.val + (c.val - 1) ≤ MAX_UINT256 := by
    have hStep : a.val * b.val + (c.val - 1) ≤ a.val * c.val + (c.val - 1) :=
      Nat.add_le_add_right hAB_le_AC _
    -- hNoOverflow : a*c + c - 1 < modulus, i.e. a*c + c - 1 ≤ MAX_UINT256
    -- We want : a*b + c - 1 ≤ MAX_UINT256
    omega
  rw [mulDivUp_nat_eq a b c hC hNumLeMax]
  -- Goal: (a.val * b.val + (c.val - 1)) / c.val ≤ a.val
  -- Use: (n / k ≤ m) ↔ (n ≤ m * k + (k - 1)). So we need
  --      a.val * b.val + (c.val - 1) ≤ a.val * c.val + (c.val - 1).
  rw [Nat.div_le_iff_le_mul_add_pred hCPos, Nat.mul_comm c.val a.val]
  exact Nat.add_le_add_right hAB_le_AC _

set_option maxRecDepth 4096

/--
Band invariant upper bound: `p ≤ startPrice` for any timestamp.

Branches:
- At `block_timestamp = auction_startTime`: result = `startPrice`, trivially.
- At `block_timestamp = auction_endTime`: result = `endPrice`, ≤ `startPrice`
  by `hBand`.
- Interior: result = `if p < endPrice then endPrice else p`. Both sub-cases:
  endPrice-branch ≤ startPrice by `hBand`; p-branch ≤ startPrice via
  `MathLib_exp_nonpositive_le_D18` + `mulDivUp_le_self_of_le`.

The `maxRecDepth` bump accommodates the deeply-nested term that arises
when the interior branch's expression is unfolded.
-/
theorem price_upper_bound_main
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256)
    (hBand :
      mulDivUp sellPrices.low D27 buyPrices.high
        ≤ mulDivUp sellPrices.high D27 buyPrices.low)
    (hSafe : InteriorSafe sellPrices buyPrices auction_startTime auction_endTime block_timestamp) :
    price_upper_bound_spec sellPrices buyPrices auction_startTime auction_endTime block_timestamp := by
  unfold price_upper_bound_spec _price
  by_cases h1 : block_timestamp == auction_startTime
  · -- Solidity: returns startPrice; goal: startPrice ≤ startPrice.
    simp [h1]
  · by_cases h2 : block_timestamp == auction_endTime
    · -- Solidity: returns endPrice; goal: endPrice ≤ startPrice. Use hBand.
      simpa [h1, h2] using hBand
    · -- Interior: result = if p < endPrice then endPrice else p.
      -- Reduce the outer two ifs without unfolding `mulDivUp` at the goal.
      simp only [h1, h2, Bool.false_eq_true, if_false]
      -- Pull out the InteriorSafe components so we can feed them to helpers.
      have hKEFits := hSafe.hKElapsedFitsInt
      have hOverflow := hSafe.hMulNoOverflow
      simp only at hKEFits hOverflow  -- evaluate the let-bindings inside InteriorSafe
      -- Goal: (if mulDivUp startPrice (exp ...) D18 < endPrice then endPrice else ...) ≤ startPrice
      split
      · -- p < endPrice branch: result = endPrice, ≤ startPrice by hBand.
        exact hBand
      · -- p ≥ endPrice branch: result = mulDivUp startPrice (exp negKE) D18.
        rename_i _hNotLt
        have hNegKE_nonpos := neg_ofUint256_toInt_nonpositive _ hKEFits
        have hExpLeD18 := MathLib_exp_nonpositive_le_D18 _ hNegKE_nonpos
        have hD18Pos : D18.val > 0 := by show (1000000000000000000 : Nat) > 0; decide
        exact mulDivUp_le_self_of_le _ _ _ hExpLeD18 hD18Pos hOverflow

/-! ## Aliases expected by task manifests -/

abbrev price_at_start_time := @price_at_start_time_main
abbrev price_at_end_time := @price_at_end_time_main
abbrev price_lower_bound := @price_lower_bound_main
abbrev price_upper_bound := @price_upper_bound_main

end Benchmark.Cases.Reserve.AuctionPriceBand
