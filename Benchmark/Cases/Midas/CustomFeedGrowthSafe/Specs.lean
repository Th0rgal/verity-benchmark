import Verity.Specs.Common
import Benchmark.Cases.Midas.CustomFeedGrowthSafe.Contract

namespace Benchmark.Cases.Midas.CustomFeedGrowthSafe

open Contracts
open Verity
open Verity.EVM.Uint256

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

def setRoundDataSafe_rejects_zero_price_spec
    (dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) : Prop :=
  (safeCallResult 0 dataTimestamp growthApr blockTimestamp s).isSuccess = false

def setRoundDataSafe_deviation_bound_spec
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s _s' : ContractState) : Prop :=
  deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s

def setRoundDataSafe_enforces_time_gap_spec
    (blockTimestamp : Uint256) (s _s' : ContractState) : Prop :=
  (blockTimestamp : Nat) - (lastTimestampOf s : Nat) > 3600

def setRoundDataSafe_startedAt_monotonic_spec
    (_data _dataTimestamp _growthApr _blockTimestamp : Uint256) (s s' : ContractState) : Prop :=
  roundStartedAtOf s' (latestRoundOf s') > lastStartedAtOf s

def setRoundDataSafe_onlyUp_nonnegative_deviation_spec
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s _s' : ContractState) : Prop :=
  (onlyUpWordOf s != 0) = true →
    slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false

def setRoundDataSafe_propagates_band_guard_spec
    (_data _dataTimestamp _growthApr _blockTimestamp : Uint256) (s s' : ContractState) : Prop :=
  let roundId := latestRoundOf s'
  slt (roundAnswerOf s' roundId) (minAnswerOf s) = false ∧
  sgt (roundAnswerOf s' roundId) (maxAnswerOf s) = false ∧
  slt (roundGrowthAprOf s' roundId) (minGrowthAprOf s) = false ∧
  sgt (roundGrowthAprOf s' roundId) (maxGrowthAprOf s) = false

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
