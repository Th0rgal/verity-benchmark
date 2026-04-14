import Verity.Specs.Common
import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Contract

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

def computedClaimAmount (shareWad : Uint256) (s : ContractState) : Uint256 :=
  div (mul shareWad (s.storage 0)) 1000000000000000000

def computedWethClaimAmount (shareWad : Uint256) (s : ContractState) : Uint256 :=
  div (mul shareWad (s.storage 6)) 1000000000000000000

def claimUsdc_marks_claimed_spec (s s' : ContractState) : Prop :=
  s'.storageMap 5 s.sender = 1

def claimUsdc_updates_round_claimed_spec (shareWad : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 1 = add (s.storage 1) (computedClaimAmount shareWad s)

def claimUsdc_updates_total_allocated_spec (shareWad : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 2 = sub (s.storage 2) (computedClaimAmount shareWad s)

def claimUsdc_claimed_plus_allocated_conserved_spec (_shareWad : Uint256) (s s' : ContractState) : Prop :=
  add (s'.storage 1) (s'.storage 2) = add (s.storage 1) (s.storage 2)

def claimUsdc_preserves_round_bound_spec (s' : ContractState) : Prop :=
  s'.storage 1 <= s'.storage 0

def claimUsdc_reverts_if_already_claimed_spec (s s' : ContractState) : Prop :=
  s' = s

def claimUsdc_reverts_if_exceeds_total_spec (s s' : ContractState) : Prop :=
  s' = s

def claimUsdc_preserves_weth_state_spec (s s' : ContractState) : Prop :=
  s'.storage 6 = s.storage 6 ∧
  s'.storage 7 = s.storage 7 ∧
  s'.storage 8 = s.storage 8 ∧
  s'.storageMap 9 = s.storageMap 9

def claimWeth_marks_claimed_spec (s s' : ContractState) : Prop :=
  s'.storageMap 9 s.sender = 1

def claimWeth_updates_round_claimed_spec (shareWad : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 7 = add (s.storage 7) (computedWethClaimAmount shareWad s)

def claimWeth_updates_total_allocated_spec (shareWad : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 8 = sub (s.storage 8) (computedWethClaimAmount shareWad s)

def claimWeth_claimed_plus_allocated_conserved_spec (_shareWad : Uint256) (s s' : ContractState) : Prop :=
  add (s'.storage 7) (s'.storage 8) = add (s.storage 7) (s.storage 8)

def claimWeth_preserves_round_bound_spec (s' : ContractState) : Prop :=
  s'.storage 7 <= s'.storage 6

def claimWeth_reverts_if_already_claimed_spec (s s' : ContractState) : Prop :=
  s' = s

def claimWeth_reverts_if_exceeds_total_spec (s s' : ContractState) : Prop :=
  s' = s

def claimWeth_preserves_usdc_state_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = s.storage 0 ∧
  s'.storage 1 = s.storage 1 ∧
  s'.storage 2 = s.storage 2 ∧
  s'.storageMap 5 = s.storageMap 5

def claimBoth_marks_both_claimed_spec (s s' : ContractState) : Prop :=
  s'.storageMap 5 s.sender = 1 ∧
  s'.storageMap 9 s.sender = 1

def claimBoth_updates_round_claimed_spec
    (usdcShareWad wethShareWad : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 1 = add (s.storage 1) (computedClaimAmount usdcShareWad s) ∧
  s'.storage 7 = add (s.storage 7) (computedWethClaimAmount wethShareWad s)

def claimBoth_updates_total_allocated_spec
    (usdcShareWad wethShareWad : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 2 = sub (s.storage 2) (computedClaimAmount usdcShareWad s) ∧
  s'.storage 8 = sub (s.storage 8) (computedWethClaimAmount wethShareWad s)

def claimBoth_claimed_plus_allocated_conserved_spec
    (_usdcShareWad _wethShareWad : Uint256) (s s' : ContractState) : Prop :=
  add (s'.storage 1) (s'.storage 2) = add (s.storage 1) (s.storage 2) ∧
  add (s'.storage 7) (s'.storage 8) = add (s.storage 7) (s.storage 8)

def claimBoth_preserves_round_bounds_spec (s' : ContractState) : Prop :=
  s'.storage 1 <= s'.storage 0 ∧
  s'.storage 7 <= s'.storage 6

def claimBoth_reverts_if_usdc_already_claimed_spec (s s' : ContractState) : Prop :=
  s' = s

def claimBoth_reverts_if_weth_already_claimed_spec (s s' : ContractState) : Prop :=
  s' = s

def claimBoth_reverts_if_usdc_exceeds_total_spec (s s' : ContractState) : Prop :=
  s' = s

def claimBoth_reverts_if_weth_exceeds_total_spec (s s' : ContractState) : Prop :=
  s' = s

def claimBoth_matches_independent_claims_spec
    (usdcShareWad wethShareWad : Uint256) (s s' : ContractState) : Prop :=
  let sUsdc := ((StreamRecoveryClaimUsdc.claimUsdc usdcShareWad true).run s).snd
  let sWeth := ((StreamRecoveryClaimUsdc.claimWeth wethShareWad true).run s).snd
  s'.storage 0 = sUsdc.storage 0 ∧
  s'.storageMap 5 s.sender = sUsdc.storageMap 5 s.sender ∧
  s'.storage 1 = sUsdc.storage 1 ∧
  s'.storage 2 = sUsdc.storage 2 ∧
  s'.storage 6 = sWeth.storage 6 ∧
  s'.storageMap 9 s.sender = sWeth.storageMap 9 s.sender ∧
  s'.storage 7 = sWeth.storage 7 ∧
  s'.storage 8 = sWeth.storage 8

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
