import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
The claim path moves the computed amount from `totalUsdcAllocated` into
`roundUsdcClaimed`, so the combined accounting mass is preserved.
-/
theorem claimUsdc_claimed_plus_allocated_conserved
    (shareWad : Uint256) (s s' : ContractState) :
    claimUsdc_updates_round_claimed_spec shareWad s s' ->
    claimUsdc_updates_total_allocated_spec shareWad s s' ->
    add (s'.storage 1) (s'.storage 2) = add (s.storage 1) (s.storage 2) := by
  intro hClaimed hAllocated
  unfold claimUsdc_updates_round_claimed_spec at hClaimed
  unfold claimUsdc_updates_total_allocated_spec at hAllocated
  rw [hClaimed, hAllocated]
  rw [Verity.Core.Uint256.add_assoc]
  rw [Verity.Core.Uint256.add_comm (computedClaimAmount shareWad s) (s.storage 2 - computedClaimAmount shareWad s)]
  rw [← Verity.Core.Uint256.add_assoc]
  rw [Verity.Core.Uint256.sub_add_cancel_left (s.storage 2) (computedClaimAmount shareWad s)]

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
