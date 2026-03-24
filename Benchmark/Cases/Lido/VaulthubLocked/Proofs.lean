import Benchmark.Cases.Lido.VaulthubLocked.Specs

namespace Benchmark.Cases.Lido.VaulthubLocked

open Verity.EVM.Uint256
open Verity.Core.Uint256

/-
  Reference proofs for the Lido VaultHub _locked() solvency properties.

  The F-01 proof proceeds by case split on whether the reserve-ratio-based
  reserve dominates the minimal reserve:

  Case 1 (reserve >= minimalReserve):
    locked = liability_max + ceil(liability_max * RR / (BP - RR))
    locked * (BP-RR) = liability_max*(BP-RR) + ceil(liability_max*RR/(BP-RR))*(BP-RR)
                     >= liability_max*(BP-RR) + liability_max*RR   [ceilDiv sandwich]
                     = liability_max * BP
                     >= liability * BP                              [monotonicity, maxLS >= LS]

  Case 2 (minimalReserve > reserve):
    locked = liability_max + minimalReserve
    Need: (liability_max + minReserve) * (BP-RR) >= liability * BP
    Since minReserve > ceil(liability_max * RR / (BP-RR)) >= liability_max * RR / (BP-RR):
      minReserve * (BP-RR) > liability_max * RR
    So: locked * (BP-RR) = liability_max*(BP-RR) + minReserve*(BP-RR)
                         > liability_max*(BP-RR) + liability_max*RR
                         = liability_max * BP >= liability * BP
-/

/-! ## Helper: ceilDiv at the Nat level -/

/-- When b > 0, ceilDiv a b at the Nat level equals ceil(a.val / b.val) mod modulus -/
private theorem ceilDiv_val (a b : Uint256) (hb : b > 0) :
    (ceilDiv a b).val = (a.val + b.val - 1) / b.val % modulus := by
  simp [ceilDiv]
  have hbne : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp [Verity.Core.Uint256.lt_def] at hb
  simp [hbne]

/--
  Supporting lemma: ceilDiv sandwich bound.
  For any x and d > 0, when ceilDiv(x,d) * d doesn't overflow:
    ceilDiv(x, d) * d >= x.
-/
theorem ceildiv_sandwich
    (x d : Uint256)
    (hd : d > 0)
    (hNoOverflow : (ceilDiv x d).val * d.val < modulus) :
    ceildiv_sandwich_spec x d := by
  unfold ceildiv_sandwich_spec
  intro hd' hNoOv
  -- Work at the Nat level
  simp [Verity.Core.Uint256.le_def]
  -- Expand mul with no-overflow
  have hMulEq : (mul (ceilDiv x d) d).val = (ceilDiv x d).val * d.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow
  rw [hMulEq]
  -- Expand ceilDiv
  have hCeilVal := ceilDiv_val x d hd
  -- Key: ceil(a/b) * b >= a for natural numbers
  have hdPos : 0 < d.val := by
    simp [Verity.Core.Uint256.lt_def] at hd
    exact hd
  -- ceil(x.val / d.val) = (x.val + d.val - 1) / d.val
  -- We need: ((x.val + d.val - 1) / d.val % modulus) * d.val >= x.val
  -- Since hNoOverflow tells us the product fits, the % modulus is a no-op on ceilDiv.val
  -- Actually we need: ceilDiv_val * d.val >= x.val
  -- ceilDiv.val = (x.val + d.val - 1) / d.val % modulus
  -- Let q = (x.val + d.val - 1) / d.val
  -- q * d.val >= x.val (standard ceil property)
  -- Since hNoOverflow: (ceilDiv x d).val * d.val < modulus
  -- and ceilDiv.val = q % modulus, if q < modulus then ceilDiv.val = q
  -- q ≤ (x.val + d.val - 1) / 1 = x.val + d.val - 1 < modulus (since both x, d < modulus)
  -- Actually q could be close to modulus, but hNoOverflow constrains it
  rw [hCeilVal]
  -- Let q = (x.val + d.val - 1) / d.val
  set q := (x.val + d.val - 1) / d.val with hq_def
  -- We know q % modulus * d.val < modulus from hNoOverflow rewritten with hCeilVal
  -- Need: (q % modulus) * d.val >= x.val
  -- Since q * d.val >= x.val (standard ceil), and q % modulus ≤ q
  -- we need q < modulus so q % modulus = q
  have hqLt : q < modulus := by
    by_contra h
    push_neg at h
    have : q % modulus ≤ q := Nat.mod_le q modulus
    -- q % modulus * d.val < modulus, but q >= modulus and d.val >= 1
    -- This gives us modulus * 1 ≤ q * d.val but q * d.val could wrap...
    -- Actually we just need: q ≤ (x.val + d.val - 1)
    -- and x.val < modulus, d.val < modulus, so x.val + d.val - 1 < 2 * modulus
    -- so q ≤ x.val + d.val - 1 < 2 * modulus
    -- Also q % modulus * d.val < modulus
    -- If q >= modulus, then q % modulus could be anything in [0, modulus)
    -- But actually: q = (x.val + d.val - 1) / d.val ≤ (x.val + d.val - 1) / 1 = x.val + d.val - 1
    -- x.val < modulus and d.val < modulus, so x.val + d.val - 1 < 2 * modulus - 1
    -- q / d.val ≤ x.val/d.val + 1 (roughly). More precisely:
    -- q = (x.val + d.val - 1) / d.val. Since d.val >= 1:
    -- q ≤ x.val + d.val - 1
    -- But we need q < modulus. x.val < modulus and d.val < modulus so
    -- x.val + d.val - 1 ≤ 2 * modulus - 2. So q could be up to 2*modulus-2.
    -- However: q * d.val >= x.val (the ceil property). Also q = ceil(x.val/d.val).
    -- If d.val >= 2, q ≤ (x.val + d.val - 1) / 2 < modulus.
    -- If d.val = 1, q = x.val + 0 = x.val < modulus.
    -- In general: q ≤ (x.val + d.val - 1) / d.val ≤ x.val / d.val + 1
    -- x.val / d.val < modulus / d.val ≤ modulus (since d.val >= 1)
    -- So x.val / d.val + 1 ≤ modulus. Could be = modulus if x.val = modulus - 1, d.val = 1.
    -- Wait: x.val < modulus and d.val = 1: q = (x.val + 0) / 1 = x.val < modulus. OK.
    -- d.val >= 2: q ≤ (modulus - 1 + modulus - 1) / 2 = (2*modulus - 2)/2 = modulus - 1 < modulus.
    -- So q < modulus always holds!
    have hxLt := x.isLt
    have hdLt := d.isLt
    have : q ≤ x.val + d.val - 1 := Nat.div_le_self _ _
    have : x.val + d.val - 1 < modulus + modulus - 1 := by omega
    -- More careful: if d.val = 1, q = x.val < modulus
    -- if d.val >= 2, q ≤ (x.val + d.val - 1) / d.val
    --   The numerator is < modulus + modulus = 2 * modulus
    --   Dividing by d.val >= 2 gives < modulus
    by_cases hd1 : d.val = 1
    · rw [hq_def, hd1]
      simp
      exact hxLt
    · have hdGe2 : d.val ≥ 2 := by omega
      have hNumLt : x.val + d.val - 1 < 2 * modulus := by omega
      have : q < modulus := by
        calc q ≤ (x.val + d.val - 1) / 2 := Nat.div_le_div_left (by omega) (by omega)
          _ < (2 * modulus) / 2 := Nat.div_lt_div_right (by omega) hNumLt
          _ = modulus := by omega
      omega
  rw [Nat.mod_eq_of_lt hqLt]
  -- Now need: q * d.val >= x.val
  -- This is the standard ceiling division property
  -- q = (x.val + d.val - 1) / d.val
  -- q * d.val >= x.val ↔ (x.val + d.val - 1) / d.val * d.val >= x.val
  -- Standard: for n, d > 0: ((n + d - 1) / d) * d >= n
  -- Proof: n = d * (n/d) + (n % d). n + d - 1 = d * (n/d) + (n % d) + d - 1.
  -- (n + d - 1) / d = n/d + (n%d + d - 1) / d.
  -- If n%d = 0: (n+d-1)/d = n/d + (d-1)/d = n/d. So q*d = (n/d)*d = n. Good.
  -- If n%d > 0: (n%d + d - 1) >= d, so (n%d+d-1)/d >= 1. So q >= n/d + 1.
  --   q*d >= (n/d + 1)*d = n - n%d + d > n. Good.
  -- Alternatively: q * d = ((x.val + d.val - 1) / d.val) * d.val
  --   >= x.val + d.val - 1 - (d.val - 1) = x.val  [using a / b * b >= a - (b-1)]
  -- The standard fact: (a / b) * b + a % b = a, so (a / b) * b = a - a % b >= a - (b - 1)
  have hStd : q * d.val ≥ x.val := by
    have hSum := Nat.div_add_mod (x.val + d.val - 1) d.val
    -- ((x.val + d.val - 1) / d.val) * d.val + (x.val + d.val - 1) % d.val = x.val + d.val - 1
    have hRem : (x.val + d.val - 1) % d.val < d.val := Nat.mod_lt _ hdPos
    -- q * d.val = x.val + d.val - 1 - (x.val + d.val - 1) % d.val
    -- >= x.val + d.val - 1 - (d.val - 1) = x.val
    have hGe1 : d.val ≥ 1 := hdPos
    omega
  exact hStd

/--
  Supporting lemma: share conversion monotonicity.
  getPooledEthBySharesRoundUp(a) >= getPooledEthBySharesRoundUp(b) when a >= b
  and a * totalPooledEther doesn't overflow.
-/
theorem shares_conversion_monotone
    (a b : Uint256)
    (totalPooledEther totalShares : Uint256)
    (hTS : totalShares > 0)
    (hNoOverflow : a.val * totalPooledEther.val < modulus) :
    shares_conversion_monotone_spec a b totalPooledEther totalShares := by
  unfold shares_conversion_monotone_spec
  intro hab hNoOv
  -- getPooledEthBySharesRoundUp s tpe ts = ceilDiv (mul s tpe) ts
  unfold getPooledEthBySharesRoundUp
  -- Need: ceilDiv (mul a tpe) ts >= ceilDiv (mul b tpe) ts
  -- Since a >= b and no overflow on a * tpe, also no overflow on b * tpe
  simp [Verity.Core.Uint256.le_def]
  -- Work at Nat level with the ceilDiv definition
  have hTSPos : totalShares.val > 0 := by
    simp [Verity.Core.Uint256.lt_def] at hTS
    exact hTS
  have hTSNe : totalShares ≠ 0 := by
    intro h; rw [h] at hTSPos; simp [Verity.Core.Uint256.val_zero] at hTSPos
  -- mul a tpe doesn't overflow
  have hMulA : (mul a totalPooledEther).val = a.val * totalPooledEther.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow
  -- b.val <= a.val and a * tpe < modulus implies b * tpe < modulus
  have habVal : b.val ≤ a.val := by
    simp [Verity.Core.Uint256.le_def] at hab; exact hab
  have hBNoOverflow : b.val * totalPooledEther.val < modulus := by
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ habVal) hNoOverflow
  have hMulB : (mul b totalPooledEther).val = b.val * totalPooledEther.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hBNoOverflow
  -- ceilDiv (mul a tpe) ts and ceilDiv (mul b tpe) ts
  -- ceilDiv x y = if y = 0 then 0 else ⟨(x.val + y.val - 1) / y.val % modulus⟩
  simp [ceilDiv, hTSNe]
  -- Now: (mul a tpe).val + ts.val - 1) / ts.val % modulus
  --   >= (mul b tpe).val + ts.val - 1) / ts.val % modulus
  rw [hMulA, hMulB]
  -- Need: (a.val * tpe.val + ts.val - 1) / ts.val % modulus
  --    >= (b.val * tpe.val + ts.val - 1) / ts.val % modulus
  -- Since a.val * tpe.val >= b.val * tpe.val, the ceiling divisions are monotone
  -- and both are < modulus (since a.val * tpe.val < modulus and ts.val >= 1)
  set qa := (a.val * totalPooledEther.val + totalShares.val - 1) / totalShares.val
  set qb := (b.val * totalPooledEther.val + totalShares.val - 1) / totalShares.val
  -- qa < modulus: qa ≤ (a.val * tpe.val + ts.val - 1) / 1 = a.val * tpe.val + ts.val - 1
  -- < modulus + modulus (since both < modulus)
  -- Actually: qa ≤ a.val * tpe.val + ts.val - 1 (div by ≥1 doesn't increase)
  -- and since tpe.val = 0 is possible... if tpe.val = 0 then mul = 0 and both sides are ceilDiv(0, ts)
  have hqaLt : qa < modulus := by
    have : qa ≤ a.val * totalPooledEther.val + totalShares.val - 1 := Nat.div_le_self _ _
    have : a.val * totalPooledEther.val < modulus := hNoOverflow
    have : totalShares.val < modulus := totalShares.isLt
    omega
  have hqbLt : qb < modulus := by
    have : qb ≤ b.val * totalPooledEther.val + totalShares.val - 1 := Nat.div_le_self _ _
    have : b.val * totalPooledEther.val < modulus := hBNoOverflow
    have : totalShares.val < modulus := totalShares.isLt
    omega
  rw [Nat.mod_eq_of_lt hqaLt, Nat.mod_eq_of_lt hqbLt]
  -- Now just: qa >= qb, i.e., Nat.div monotonicity
  exact Nat.div_le_div_right (by omega)

/--
  P-VH-04: maxLiabilityShares >= liabilityShares.
  In the real contract this is maintained by the minting and reporting logic.
  Here we state it as a theorem to be proven from the contract invariants.
-/
theorem max_liability_shares_bound
    (maxLiabilityShares liabilityShares : Uint256)
    (hBound : maxLiabilityShares ≥ liabilityShares) :
    max_liability_shares_bound_spec maxLiabilityShares liabilityShares := by
  unfold max_liability_shares_bound_spec
  exact hBound

/--
  P-VH-03: Reserve ratio is within valid bounds.
-/
theorem reserve_ratio_bounds
    (reserveRatioBP : Uint256)
    (hPos : reserveRatioBP > 0)
    (hLt : reserveRatioBP < TOTAL_BASIS_POINTS) :
    reserve_ratio_bounds_spec reserveRatioBP := by
  unfold reserve_ratio_bounds_spec
  exact ⟨hPos, hLt⟩

/--
  F-01: Locked funds solvency.
  The locked amount multiplied by the reserve ratio complement is at least
  the liability multiplied by total basis points.

  Proof strategy: Work entirely at the Nat level. The key insight is:
    locked = liability_max + max(ceil(liability_max * RR / (BP-RR)), minRes)
    locked * (BP-RR) >= liability_max * (BP-RR) + liability_max * RR
                      = liability_max * BP
                      >= liability * BP  (by monotonicity, since maxLS >= LS)
-/
theorem locked_funds_solvency
    (maxLiabilityShares liabilityShares : Uint256)
    (minimalReserve reserveRatioBP : Uint256)
    (totalPooledEther totalShares : Uint256)
    -- Axioms
    (hMaxLS : maxLiabilityShares ≥ liabilityShares)
    (hRR_pos : reserveRatioBP > 0)
    (hRR_lt : reserveRatioBP < TOTAL_BASIS_POINTS)
    (hTS : totalShares > 0)
    (hTPE : totalPooledEther > 0)
    -- No overflow: maxLiabilityShares * totalPooledEther fits in Uint256
    (hNoOverflow1 : maxLiabilityShares.val * totalPooledEther.val < modulus)
    -- No overflow: liability * reserveRatioBP fits in Uint256
    (hNoOverflow2 : (getPooledEthBySharesRoundUp maxLiabilityShares totalPooledEther totalShares).val
                    * reserveRatioBP.val < modulus)
    -- No overflow: the add inside locked (liability + effectiveReserve) fits in Uint256
    (hNoOverflow3 : let liab := getPooledEthBySharesRoundUp maxLiabilityShares totalPooledEther totalShares
                    let reserve := ceilDiv (mul liab reserveRatioBP) (sub TOTAL_BASIS_POINTS reserveRatioBP)
                    let eff := if reserve ≥ minimalReserve then reserve else minimalReserve
                    liab.val + eff.val < modulus)
    -- No overflow: locked * (BP - RR) fits in Uint256
    (hNoOverflow4 : (locked maxLiabilityShares minimalReserve reserveRatioBP totalPooledEther totalShares).val
                    * (sub TOTAL_BASIS_POINTS reserveRatioBP).val < modulus)
    -- No overflow: liability * BP fits in Uint256
    (hNoOverflow5 : (getPooledEthBySharesRoundUp liabilityShares totalPooledEther totalShares).val
                    * TOTAL_BASIS_POINTS.val < modulus) :
    locked_funds_solvency_spec maxLiabilityShares liabilityShares minimalReserve reserveRatioBP
      totalPooledEther totalShares := by
  unfold locked_funds_solvency_spec
  simp [Verity.Core.Uint256.le_def]
  -- Abbreviations
  set maxLS := maxLiabilityShares
  set ls := liabilityShares
  set minRes := minimalReserve
  set rrBP := reserveRatioBP
  set tpe := totalPooledEther
  set ts := totalShares
  set BP := TOTAL_BASIS_POINTS
  set complement := sub BP rrBP
  set liabilityMax := getPooledEthBySharesRoundUp maxLS tpe ts
  set liabilityLS := getPooledEthBySharesRoundUp ls tpe ts
  set lockedVal := locked maxLS minRes rrBP tpe ts

  -- Step 1: expand mul using no-overflow hypotheses
  have hLHSEq : (mul lockedVal complement).val = lockedVal.val * complement.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow4

  have hRHSEq : (mul liabilityLS BP).val = liabilityLS.val * BP.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow5

  rw [hLHSEq, hRHSEq]

  -- Step 2: expand locked definition
  unfold locked at lockedVal
  simp at lockedVal

  -- Step 3: By monotonicity, liabilityMax >= liabilityLS
  have hMonotone : liabilityMax.val ≥ liabilityLS.val := by
    have hmono := shares_conversion_monotone maxLS ls tpe ts hTS hNoOverflow1
    unfold shares_conversion_monotone_spec at hmono
    have hMono := hmono hMaxLS hNoOverflow1
    simp [Verity.Core.Uint256.le_def] at hMono
    exact hMono

  -- Step 4: Sufficient to show lockedVal * complement >= liabilityMax * BP
  suffices h : lockedVal.val * complement.val ≥ liabilityMax.val * BP.val by
    exact Nat.le_trans (Nat.mul_le_mul_right _ hMonotone) h

  -- Step 5: BP = complement + rrBP
  have hRRVal : rrBP.val > 0 := by
    simp [Verity.Core.Uint256.lt_def] at hRR_pos; exact hRR_pos
  have hRRLtBP : rrBP.val < BP.val := by
    simp [Verity.Core.Uint256.lt_def, TOTAL_BASIS_POINTS] at hRR_lt
    simp [BP, TOTAL_BASIS_POINTS]
    exact hRR_lt

  have hComplementVal : complement.val = BP.val - rrBP.val := by
    simp [complement, Verity.Core.Uint256.sub_eq_of_le (Nat.le_of_lt hRRLtBP)]

  have hCompPos : complement.val > 0 := by
    rw [hComplementVal]; omega

  have hBPEq : BP.val = complement.val + rrBP.val := by
    rw [hComplementVal]; omega

  -- Step 6: Set up intermediate values
  set reserve := ceilDiv (mul liabilityMax rrBP) complement
  set effectiveReserve := if reserve ≥ minRes then reserve else minRes

  -- Step 7: (mul liabilityMax rrBP) doesn't overflow
  have hMulLiabRR : (mul liabilityMax rrBP).val = liabilityMax.val * rrBP.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow2

  -- Step 8: Prove reserve.val * complement.val >= liabilityMax.val * rrBP.val
  -- via the ceiling division property: ceil(x/d) * d >= x
  set xn := liabilityMax.val * rrBP.val
  set dn := complement.val

  have hReserveVal : reserve.val = (xn + dn - 1) / dn % modulus := by
    simp [reserve, ceilDiv]
    have hCompNe : complement ≠ 0 := by
      intro h; rw [h] at hCompPos; simp [Verity.Core.Uint256.val_zero] at hCompPos
      exact (Nat.not_lt.mpr (Nat.le_refl 0)) hCompPos
    simp [hCompNe, hMulLiabRR, xn, dn]

  have hqLt : (xn + dn - 1) / dn < modulus := by
    have : (xn + dn - 1) / dn ≤ xn + dn - 1 := Nat.div_le_self _ _
    have hxnLt : xn < modulus := hNoOverflow2
    have hdnLt : dn < modulus := by simp [dn]; exact complement.isLt
    omega

  have hReserveEq : reserve.val = (xn + dn - 1) / dn := by
    rw [hReserveVal, Nat.mod_eq_of_lt hqLt]

  have hReserveProp : reserve.val * dn ≥ xn := by
    rw [hReserveEq]
    have hDnPos : dn > 0 := hCompPos
    have := Nat.div_add_mod (xn + dn - 1) dn
    have hRem : (xn + dn - 1) % dn < dn := Nat.mod_lt _ hDnPos
    omega

  -- Step 9: effectiveReserve.val >= reserve.val
  have hEffGe : effectiveReserve.val ≥ reserve.val := by
    simp [effectiveReserve]
    by_cases h : reserve ≥ minRes
    · simp [h]
    · simp [h]
      simp [Verity.Core.Uint256.le_def] at h ⊢
      omega

  -- Step 10: effectiveReserve.val * complement.val >= liabilityMax.val * rrBP.val
  have hEffProp : effectiveReserve.val * dn ≥ xn := by
    exact Nat.le_trans hReserveProp (Nat.mul_le_mul_right _ hEffGe)

  -- Step 11: The add doesn't overflow (from hNoOverflow3)
  have hNoAddOverflow : liabilityMax.val + effectiveReserve.val < modulus := by
    exact hNoOverflow3

  -- Step 12: lockedVal.val = liabilityMax.val + effectiveReserve.val
  have hLockedDef : lockedVal.val = (liabilityMax.val + effectiveReserve.val) % modulus := by
    simp [lockedVal, locked, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
    simp [effectiveReserve, reserve, dn, xn]

  rw [hLockedDef, Nat.mod_eq_of_lt hNoAddOverflow]

  -- Step 13: Final inequality
  -- (liab + eff) * complement = liab * complement + eff * complement
  -- >= liab * complement + xn  (by hEffProp, since eff * dn >= xn)
  -- = liab * (complement + rrBP) = liab * BP
  rw [hBPEq, Nat.mul_add]
  exact Nat.add_le_add_left hEffProp _

end Benchmark.Cases.Lido.VaulthubLocked
