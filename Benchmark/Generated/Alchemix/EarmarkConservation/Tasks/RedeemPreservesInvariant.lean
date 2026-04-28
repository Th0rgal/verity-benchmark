import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`redeem(amount)`.

`redeem` multiplies `cumulativeEarmarked` and `_redemptionWeight` by
`ratioApplied`. Every account's `projectedEarmarked` is also scaled by
`ratioApplied` (via the redemption survival ratio). Linearity of
`mulQ128` (under Q128 idealization) then preserves the equality.
-/
theorem redeem_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256)
    (amount : Uint256) :
    let s' := ((AlchemistV3.redeem amount).run s).snd
    redeem_preserves_invariant_spec s s' ids := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
