import Verity.Specs.Common
import Benchmark.Cases.Midas.CustomFeedGrowthSafe.Contract

namespace Benchmark.Cases.Midas.CustomFeedGrowthSafe

open Contracts
open Verity
open Verity.EVM.Uint256

/--
  Outcome of calling `setRoundDataSafe` with the submitted round values.
-/
def signedDeviationOfSafeCall
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Uint256 :=
  signedDeviationRaw (lastAnswerOf s blockTimestamp)
    (candidateLivePrice data dataTimestamp growthApr blockTimestamp)

def deviationOfSafeCall
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Uint256 :=
  deviationAbsRaw (lastAnswerOf s blockTimestamp)
    (candidateLivePrice data dataTimestamp growthApr blockTimestamp)

def safeCallResult
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) :=
  (CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s

/--
  Human-facing outcome helpers for the safe setter.
-/
def safeAccepted
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  (safeCallResult data dataTimestamp growthApr blockTimestamp s).isSuccess = true

def safeRejected
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  (safeCallResult data dataTimestamp growthApr blockTimestamp s).isSuccess = false

/--
  Primary guardrails exposed by `setRoundDataSafe`.
-/
def hasHistory (s : ContractState) : Prop :=
  lastTimestampOf s != 0

def withinDeviationBound
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s

def respectsTimeGap
    (blockTimestamp : Uint256) (s : ContractState) : Prop :=
  (blockTimestamp : Nat) - (lastTimestampOf s : Nat) > 3600

def advancesStartedAt
    (dataTimestamp : Uint256) (s : ContractState) : Prop :=
  dataTimestamp > lastStartedAtOf s

def respectsOnlyUp
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  (onlyUpWordOf s != 0) = true →
    slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false

def onlyUpAprNonnegative
    (growthApr : Uint256) (s : ContractState) : Prop :=
  (onlyUpWordOf s != 0) = true →
    slt growthApr 0 = false

def currentTimeAfterLastUpdate
    (blockTimestamp : Uint256) (s : ContractState) : Prop :=
  lastTimestampOf s <= blockTimestamp

def submittedTimestampBeforeCurrentTime
    (dataTimestamp blockTimestamp : Uint256) : Prop :=
  dataTimestamp < blockTimestamp

def historyChecksPass
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  hasHistory s →
    withinDeviationBound data dataTimestamp growthApr blockTimestamp s ∧
      (candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0) ∧
      (candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        respectsOnlyUp data dataTimestamp growthApr blockTimestamp s)

def answerInRange
    (data : Uint256) (s : ContractState) : Prop :=
  slt data (minAnswerOf s) = false ∧
    sgt data (maxAnswerOf s) = false

def aprInRange
    (growthApr : Uint256) (s : ContractState) : Prop :=
  slt growthApr (minGrowthAprOf s) = false ∧
    sgt growthApr (maxGrowthAprOf s) = false

/--
  High-level positive-path summary:
  the submitted round passes exactly the guardrails enforced by `setRoundDataSafe`.
-/
def safeInputsOk
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  historyChecksPass data dataTimestamp growthApr blockTimestamp s ∧
    onlyUpAprNonnegative growthApr s ∧
    currentTimeAfterLastUpdate blockTimestamp s ∧
    respectsTimeGap blockTimestamp s ∧
    advancesStartedAt dataTimestamp s ∧
    submittedTimestampBeforeCurrentTime dataTimestamp blockTimestamp ∧
    answerInRange data s ∧
    aprInRange growthApr s

/--
  On success, the next round should store exactly the submitted values.
-/
def writesSubmittedRound
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s s' : ContractState) : Prop :=
  let roundId := latestRoundOf s'
  roundId = nextRoundIdOf s ∧
    roundAnswerOf s' roundId = data ∧
    roundStartedAtOf s' roundId = dataTimestamp ∧
    roundUpdatedAtOf s' roundId = blockTimestamp ∧
    roundGrowthAprOf s' roundId = growthApr

/--
  Narrow rejection property currently justified by the existing proofs:
  when the feed has history and the strict deviation cap is below 101%, a zero answer is rejected.
-/
def zeroRejectedUnderStrictDeviation
    (dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  hasHistory s ∧ maxAnswerDeviationOf s < HUNDRED_ONE →
    safeRejected 0 dataTimestamp growthApr blockTimestamp s

/--
  Human-readable target spec for the success path.
  The current proof development still exposes finer-grained lemmas; this bundles the intended story.
-/
def setRoundDataSafe_accepts_and_writes_submitted_round_spec
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  let s' := (safeCallResult data dataTimestamp growthApr blockTimestamp s).snd
  safeInputsOk data dataTimestamp growthApr blockTimestamp s →
    safeAccepted data dataTimestamp growthApr blockTimestamp s ∧
      writesSubmittedRound data dataTimestamp growthApr blockTimestamp s s'

/--
  Human-readable target spec for the rejection path.
  This is intentionally broader than what is fully proved today.
-/
def setRoundDataSafe_rejects_outside_guardrails_spec
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  ¬ safeInputsOk data dataTimestamp growthApr blockTimestamp s →
    safeRejected data dataTimestamp growthApr blockTimestamp s

def setRoundDataSafe_rejects_zero_price_spec
    (dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  safeRejected 0 dataTimestamp growthApr blockTimestamp s

def setRoundDataSafe_deviation_bound_spec
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s _s' : ContractState) : Prop :=
  withinDeviationBound data dataTimestamp growthApr blockTimestamp s

def setRoundDataSafe_enforces_time_gap_spec
    (blockTimestamp : Uint256) (s _s' : ContractState) : Prop :=
  respectsTimeGap blockTimestamp s

def setRoundDataSafe_startedAt_monotonic_spec
    (_data _dataTimestamp _growthApr _blockTimestamp : Uint256) (s s' : ContractState) : Prop :=
  roundStartedAtOf s' (latestRoundOf s') > lastStartedAtOf s

def setRoundDataSafe_onlyUp_nonnegative_deviation_spec
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s _s' : ContractState) : Prop :=
  respectsOnlyUp data dataTimestamp growthApr blockTimestamp s

def setRoundDataSafe_propagates_band_guard_spec
    (_data _dataTimestamp _growthApr _blockTimestamp : Uint256) (s s' : ContractState) : Prop :=
  let roundId := latestRoundOf s'
  answerInRange (roundAnswerOf s' roundId) s ∧
    aprInRange (roundGrowthAprOf s' roundId) s

structure SetRoundDataSafeFullCorrectnessSpec
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s s' : ContractState) : Prop where
  rejectsZeroPrice :
    setRoundDataSafe_rejects_zero_price_spec dataTimestamp growthApr blockTimestamp s
  deviationBound :
    setRoundDataSafe_deviation_bound_spec data dataTimestamp growthApr blockTimestamp s s'
  timeGap :
    setRoundDataSafe_enforces_time_gap_spec blockTimestamp s s'
  startedAtMonotonic :
    setRoundDataSafe_startedAt_monotonic_spec data dataTimestamp growthApr blockTimestamp s s'
  onlyUpDeviation :
    setRoundDataSafe_onlyUp_nonnegative_deviation_spec data dataTimestamp growthApr blockTimestamp s s'
  bandGuard :
    setRoundDataSafe_propagates_band_guard_spec data dataTimestamp growthApr blockTimestamp s s'

end Benchmark.Cases.Midas.CustomFeedGrowthSafe
