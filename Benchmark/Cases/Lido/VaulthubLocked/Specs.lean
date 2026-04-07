import Verity.Specs.Common
import Benchmark.Cases.Lido.VaulthubLocked.Contract

namespace Benchmark.Cases.Lido.VaulthubLocked

open Verity
open Verity.EVM.Uint256

/-
  Specifications for the Lido VaultHub _locked() solvency properties.
  These correspond to findings and proven properties from the Certora
  formal verification report (December 2025).

  F-01 (Certora finding): The locked amount is sufficient to cover the vault's
  liability at the protocol level, i.e.:
    locked * (BP - RR) >= getPooledEthBySharesRoundUp(LS) * BP

  P-VH-04 (Certora proven): maxLiabilityShares >= liabilityShares
  P-VH-03 (Certora proven): 0 < reserveRatioBP < TOTAL_BASIS_POINTS

  Storage layout (from verity_contract VaultHubLocked):
    slot 0: maxLiabilityShares
    slot 1: liabilityShares
    slot 2: minimalReserve
    slot 3: reserveRatioBP
    slot 4: totalPooledEther
    slot 5: totalShares
    slot 6: lockedAmount (output)
-/

/--
  F-01: Locked funds solvency after executing `syncLocked`.
  The stored locked amount (slot 6), multiplied by the reserve ratio complement,
  is at least as large as the liability (for the current liabilityShares in slot 1)
  multiplied by the full basis points.

  `syncLocked` computes locked from maxLiabilityShares (slot 0), ensuring the
  locked amount covers even the peak obligation within the oracle period.
-/
def locked_funds_solvency_spec
    (_s s' : ContractState) : Prop :=
  let lockedAmount := s'.storage 6
  let liability := getPooledEthBySharesRoundUp (s'.storage 1) (s'.storage 4) (s'.storage 5)
  let complement := sub TOTAL_BASIS_POINTS (s'.storage 3)
  mul lockedAmount complement ≥ mul liability TOTAL_BASIS_POINTS

/--
  P-VH-04 (Certora proven): maxLiabilityShares is an upper bound on liabilityShares.
  This invariant is maintained by the VaultHub's minting and reporting logic.
-/
def max_liability_shares_bound_spec
    (maxLiabilityShares liabilityShares : Uint256) : Prop :=
  maxLiabilityShares ≥ liabilityShares

/--
  P-VH-03 (Certora proven): Reserve ratio is strictly between 0 and TOTAL_BASIS_POINTS.
  This is enforced by the vault connection validation logic.
-/
def reserve_ratio_bounds_spec
    (reserveRatioBP : Uint256) : Prop :=
  reserveRatioBP > 0 ∧ reserveRatioBP < TOTAL_BASIS_POINTS

/--
  Supporting lemma: ceilDiv sandwich bound.
  For any x and d > 0, provided the product does not overflow:
  ceilDiv(x, d) * d >= x.
  This is a key arithmetic fact used in the F-01 proof.
-/
def ceildiv_sandwich_spec
    (x d : Uint256) : Prop :=
  d > 0 →
  (ceilDiv x d).val * d.val < modulus →
  mul (ceilDiv x d) d ≥ x

/--
  Supporting lemma: getPooledEthBySharesRoundUp is monotone in shares.
  If a >= b then getPooledEthBySharesRoundUp(a) >= getPooledEthBySharesRoundUp(b),
  provided the larger multiplication does not overflow.
  This relies on ceilDiv monotonicity.
-/
def shares_conversion_monotone_spec
    (a b : Uint256)
    (totalPooledEther totalShares : Uint256) : Prop :=
  a ≥ b →
  a.val * totalPooledEther.val < modulus →
  getPooledEthBySharesRoundUp a totalPooledEther totalShares ≥
  getPooledEthBySharesRoundUp b totalPooledEther totalShares

end Benchmark.Cases.Lido.VaulthubLocked
