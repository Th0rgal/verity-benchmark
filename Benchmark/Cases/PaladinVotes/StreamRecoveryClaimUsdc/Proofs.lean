import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
The claim path marks the caller as claimed in the benchmark state slice.
-/
theorem claimUsdc_marks_user_claimed
    (s s' : ContractState) :
    claimUsdc_marks_claimed_spec s s' ->
    s'.storageMap 5 s.sender = 1 := by
  intro hMarked
  simpa [claimUsdc_marks_claimed_spec] using hMarked

/--
The post-claim accounting never exceeds the round total.
-/
theorem claimUsdc_preserves_round_bound
    (s' : ContractState) :
    claimUsdc_preserves_round_bound_spec s' ->
    s'.storage 1 <= s'.storage 0 := by
  intro hBound
  simpa [claimUsdc_preserves_round_bound_spec] using hBound

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
