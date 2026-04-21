import Benchmark.Cases.Midas.CustomFeedGrowthSafe.Specs
import Verity.Proofs.Stdlib.Automation

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Benchmark.Cases.Midas.CustomFeedGrowthSafe

open Contracts
open Verity
open Verity.EVM.Uint256

private theorem latestRoundSlot : CustomFeedGrowthSafe.latestRound.slot = 5 := by native_decide
private theorem onlyUpSlot : CustomFeedGrowthSafe.onlyUp.slot = 6 := by native_decide
private theorem maxAnswerDeviationSlot : CustomFeedGrowthSafe.maxAnswerDeviation.slot = 0 := by native_decide
private theorem minAnswerSlot : CustomFeedGrowthSafe.minAnswer.slot = 1 := by native_decide
private theorem maxAnswerSlot : CustomFeedGrowthSafe.maxAnswer.slot = 2 := by native_decide
private theorem minGrowthAprSlot : CustomFeedGrowthSafe.minGrowthApr.slot = 3 := by native_decide
private theorem maxGrowthAprSlot : CustomFeedGrowthSafe.maxGrowthApr.slot = 4 := by native_decide
private theorem roundAnswerSlot : CustomFeedGrowthSafe.roundAnswer.slot = 7 := by native_decide
private theorem roundStartedAtSlot : CustomFeedGrowthSafe.roundStartedAt.slot = 8 := by native_decide
private theorem roundUpdatedAtSlot : CustomFeedGrowthSafe.roundUpdatedAt.slot = 9 := by native_decide
private theorem roundGrowthAprSlot : CustomFeedGrowthSafe.roundGrowthApr.slot = 10 := by native_decide

private def setRoundWrites
    (roundId data dataTimestamp growthApr blockTimestamp : Uint256) : Contract Unit := do
  setMappingUint CustomFeedGrowthSafe.roundAnswer roundId data
  setMappingUint CustomFeedGrowthSafe.roundStartedAt roundId dataTimestamp
  setMappingUint CustomFeedGrowthSafe.roundUpdatedAt roundId blockTimestamp
  setMappingUint CustomFeedGrowthSafe.roundGrowthApr roundId growthApr
  setStorage CustomFeedGrowthSafe.latestRound roundId

private def writeStorageAfterRound (s : ContractState) (storageSlot : Nat) : Uint256 :=
  if storageSlot = CustomFeedGrowthSafe.latestRound.slot then nextRoundIdOf s else s.storage storageSlot

private def writeMapUintAfterRound
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (mappingSlot : Nat) (k : Uint256) : Uint256 :=
  let roundId := nextRoundIdOf s
  if mappingSlot = CustomFeedGrowthSafe.roundGrowthApr.slot ∧ k = roundId then growthApr
  else if mappingSlot = CustomFeedGrowthSafe.roundUpdatedAt.slot ∧ k = roundId then blockTimestamp
  else if mappingSlot = CustomFeedGrowthSafe.roundStartedAt.slot ∧ k = roundId then dataTimestamp
  else if mappingSlot = CustomFeedGrowthSafe.roundAnswer.slot ∧ k = roundId then data
  else s.storageMapUint mappingSlot k

private theorem setRoundWrites_storage
    (roundId data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) (storageSlot : Nat) :
    (((setRoundWrites roundId data dataTimestamp growthApr blockTimestamp).run s).snd).storage storageSlot =
      if storageSlot = CustomFeedGrowthSafe.latestRound.slot then roundId else s.storage storageSlot := by
  simp [setRoundWrites, setStorage, setMappingUint, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem setRoundWrites_storageMapUint
    (roundId data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (mappingSlot : Nat) (k : Uint256) :
    (((setRoundWrites roundId data dataTimestamp growthApr blockTimestamp).run s).snd).storageMapUint mappingSlot k =
      if mappingSlot = CustomFeedGrowthSafe.roundGrowthApr.slot ∧ k = roundId then growthApr
      else if mappingSlot = CustomFeedGrowthSafe.roundUpdatedAt.slot ∧ k = roundId then blockTimestamp
      else if mappingSlot = CustomFeedGrowthSafe.roundStartedAt.slot ∧ k = roundId then dataTimestamp
      else if mappingSlot = CustomFeedGrowthSafe.roundAnswer.slot ∧ k = roundId then data
      else s.storageMapUint mappingSlot k := by
  simp [setRoundWrites, setStorage, setMappingUint, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem setRoundDataSafe_zero_history_onlyup_off_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : lastTimestampOf s = 0)
    (hOnlyUp0 : onlyUpWordOf s = 0)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdated0Num : s.storageMapUint 9 (s.storage 5) = 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hOnlyUp0Num : s.storage 6 = 0 := by
    simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hLastUpdatedBranch :
      ¬ ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hOnlyUpBranch : ¬ ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [hLastUpdated0, lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot]
      using hTimeGap
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStarted
  let _ := hTimeOrder
  unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
  simp only [getStorage, getMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run, ContractResult.snd]
  constructor
  · simp [hLastUpdatedBranch, hOnlyUpBranch, hDataLoBranch, hDataHiBranch, hGrowthLoBranch,
      hGrowthHiBranch, hTimestampUnderflowProp, hTimeGapProp, hStartedProp, hDataTsLt]
    simpa [writeStorageAfterRound] using
      setRoundWrites_storage (nextRoundIdOf s) data dataTimestamp growthApr blockTimestamp s storageSlot
  · simp [hLastUpdatedBranch, hOnlyUpBranch, hDataLoBranch, hDataHiBranch, hGrowthLoBranch,
      hGrowthHiBranch, hTimestampUnderflowProp, hTimeGapProp, hStartedProp, hDataTsLt]
    simpa [writeMapUintAfterRound] using
      setRoundWrites_storageMapUint (nextRoundIdOf s) data dataTimestamp growthApr blockTimestamp s mapSlot k

private theorem setRoundDataSafe_zero_history_onlyup_on_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : lastTimestampOf s = 0)
    (hOnlyUp0 : ¬ onlyUpWordOf s = 0)
    (hOnlyUpApr : slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdated0Num : s.storageMapUint 9 (s.storage 5) = 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hOnlyUp0Num : s.storage 6 ≠ 0 := by
    simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hLastUpdatedBranch :
      ¬ ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hOnlyUpBranch : ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hOnlyUpAprBranch : ¬ (slt growthApr 0 = true) := by simpa [hOnlyUpApr]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [hLastUpdated0, lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot]
      using hTimeGap
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStarted
  let _ := hTimeOrder
  unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
  simp only [getStorage, getMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run, ContractResult.snd]
  constructor
  · simp [hLastUpdatedBranch, hOnlyUpBranch, hOnlyUpAprBranch, hDataLoBranch, hDataHiBranch,
      hGrowthLoBranch, hGrowthHiBranch, hTimestampUnderflowProp, hTimeGapProp, hStartedProp, hDataTsLt]
    simpa [writeStorageAfterRound] using
      setRoundWrites_storage (nextRoundIdOf s) data dataTimestamp growthApr blockTimestamp s storageSlot
  · simp [hLastUpdatedBranch, hOnlyUpBranch, hOnlyUpAprBranch, hDataLoBranch, hDataHiBranch,
      hGrowthLoBranch, hGrowthHiBranch, hTimestampUnderflowProp, hTimeGapProp, hStartedProp, hDataTsLt]
    simpa [writeMapUintAfterRound] using
      setRoundWrites_storageMapUint (nextRoundIdOf s) data dataTimestamp growthApr blockTimestamp s mapSlot k

private theorem setRoundDataSafe_candidate_zero_onlyup_off_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : ¬ lastTimestampOf s = 0)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : dataTimestamp <= blockTimestamp)
    (hDeviationCap :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hCandidateZero : candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0)
    (hOnlyUp0 : onlyUpWordOf s = 0)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdatedNZNum : s.storageMapUint 9 (s.storage 5) ≠ 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hCandidateZeroNum :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) = 0 := by
    simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
  have hCandidateZeroDenom :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) = 0 := by
    simpa [GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS] using hCandidateZeroNum
  have hZeroDeviationCapNum : 10000000000 <= s.storage 0 := by
    have hZeroDeviationCapRaw :
        (if
              add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) = 0 then
            (mul 100 ONE).val
          else
            (absSignedWord
                (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                  (add data
                    (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))).val) ≤
          (s.storage 0).val := by
      simpa [deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw,
        deviationAbsRaw, maxAnswerDeviationOf] using hDeviationCap
    simpa [HUNDRED_ONE, ONE, hCandidateZeroDenom] using hZeroDeviationCapRaw
  have hOnlyUp0Num : s.storage 6 = 0 := by simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hLastUpdatedBranch :
      ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdatedNZNum]
  have hCandidateZeroBranch :
      ((add data
            (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ==
          0) =
        true) := by
    simpa [hCandidateZeroNum]
  have hOnlyUpBranch : ¬ ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hPrevStartedProp :
      s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStarted
  have hZeroDeviationCapProp :
      10000000000 ≤ s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
    simpa [maxAnswerDeviationSlot] using hZeroDeviationCapNum
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
  simp only [getStorage, getMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run, ContractResult.snd]
  constructor
  · simp [hLastUpdatedBranch, hCandidateZeroBranch, hOnlyUpBranch, hPrevStartedProp, hDataTsLe,
      hZeroDeviationCapProp, hTimestampUnderflowProp, hTimeGapProp, hStartedProp, hDataLoBranch,
      hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hDataTsLt]
    simpa [writeStorageAfterRound] using
      setRoundWrites_storage (nextRoundIdOf s) data dataTimestamp growthApr blockTimestamp s storageSlot
  · simp [hLastUpdatedBranch, hCandidateZeroBranch, hOnlyUpBranch, hPrevStartedProp, hDataTsLe,
      hZeroDeviationCapProp, hTimestampUnderflowProp, hTimeGapProp, hStartedProp, hDataLoBranch,
      hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hDataTsLt]
    simpa [writeMapUintAfterRound] using
      setRoundWrites_storageMapUint (nextRoundIdOf s) data dataTimestamp growthApr blockTimestamp s mapSlot k

private theorem setRoundDataSafe_candidate_zero_onlyup_on_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : ¬ lastTimestampOf s = 0)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : dataTimestamp <= blockTimestamp)
    (hDeviationCap :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hCandidateZero : candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0)
    (hOnlyUp0 : ¬ onlyUpWordOf s = 0)
    (hOnlyUpApr : slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdatedNZNum : s.storageMapUint 9 (s.storage 5) ≠ 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hCandidateZeroNum :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) = 0 := by
    simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
  have hCandidateZeroDenom :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) = 0 := by
    simpa [GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS] using hCandidateZeroNum
  have hZeroDeviationCapNum : 10000000000 <= s.storage 0 := by
    have hZeroDeviationCapRaw :
        (if
              add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) = 0 then
            (mul 100 ONE).val
          else
            (absSignedWord
                (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                  (add data
                    (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))).val) ≤
          (s.storage 0).val := by
      simpa [deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw,
        deviationAbsRaw, maxAnswerDeviationOf] using hDeviationCap
    simpa [HUNDRED_ONE, ONE, hCandidateZeroDenom] using hZeroDeviationCapRaw
  have hOnlyUp0Num : s.storage 6 ≠ 0 := by simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hLastUpdatedBranch :
      ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdatedNZNum]
  have hCandidateZeroBranch :
      ((add data
            (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ==
          0) =
        true) := by
    simpa [hCandidateZeroNum]
  have hOnlyUpBranch : ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hOnlyUpAprBranch : ¬ (slt growthApr 0 = true) := by simpa [hOnlyUpApr]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hPrevStartedProp :
      s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStarted
  have hZeroDeviationCapProp :
      10000000000 ≤ s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
    simpa [maxAnswerDeviationSlot] using hZeroDeviationCapNum
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
  simp only [getStorage, getMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run, ContractResult.snd]
  constructor
  · simp [hLastUpdatedBranch, hCandidateZeroBranch, hOnlyUpBranch, hOnlyUpAprBranch, hPrevStartedProp,
      hDataTsLe, hZeroDeviationCapProp, hTimestampUnderflowProp, hTimeGapProp, hStartedProp,
      hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hDataTsLt]
    simpa [writeStorageAfterRound] using
      setRoundWrites_storage (nextRoundIdOf s) data dataTimestamp growthApr blockTimestamp s storageSlot
  · simp [hLastUpdatedBranch, hCandidateZeroBranch, hOnlyUpBranch, hOnlyUpAprBranch, hPrevStartedProp,
      hDataTsLe, hZeroDeviationCapProp, hTimestampUnderflowProp, hTimeGapProp, hStartedProp,
      hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hDataTsLt]
    simpa [writeMapUintAfterRound] using
      setRoundWrites_storageMapUint (nextRoundIdOf s) data dataTimestamp growthApr blockTimestamp s mapSlot k

private theorem setRoundDataSafe_candidate_nonzero_onlyup_off_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : ¬ lastTimestampOf s = 0)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ : lastAnswerOf s blockTimestamp != 0)
    (hDeviationCap :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hCandidateZero : ¬ candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0)
    (hOnlyUp0 : onlyUpWordOf s = 0)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdatedNZNum : s.storageMapUint 9 (s.storage 5) ≠ 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hOnlyUp0Num : s.storage 6 = 0 := by simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hCandidateNZNum :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ≠ 0 := by
    simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
  have hCandidateNZDenom :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) ≠ 0 := by
    simpa [GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS] using hCandidateNZNum
  have hLastAnswerNZNum :
      add (s.storageMapUint 7 (s.storage 5))
          (sdiv
            (mul
              (mul (s.storageMapUint 7 (s.storage 5))
                (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
              (s.storageMapUint 10 (s.storage 5)))
            315360000000000000) ≠ 0 := by
    simpa [lastAnswerOf, applyGrowthNowRaw, applyGrowthAtRaw,
      lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf,
      latestRoundSlot, roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot] using hLastAnswerNZ
  have hLastUpdatedBranch :
      ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdatedNZNum]
  have hCandidateZeroBranch :
      ¬ ((add data
              (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ==
            0) =
          true) := by
    simp [hCandidateNZNum]
  have hLastAnswerNZBranch :
      ((add
              (s.storageMapUint CustomFeedGrowthSafe.roundAnswer.slot
                (s.storage CustomFeedGrowthSafe.latestRound.slot))
              (sdiv
                (mul
                  (mul
                    (s.storageMapUint CustomFeedGrowthSafe.roundAnswer.slot
                      (s.storage CustomFeedGrowthSafe.latestRound.slot))
                    (sub blockTimestamp
                      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                        (s.storage CustomFeedGrowthSafe.latestRound.slot))))
                  (s.storageMapUint CustomFeedGrowthSafe.roundGrowthApr.slot
                    (s.storage CustomFeedGrowthSafe.latestRound.slot)))
                315360000000000000) !=
            0) =
        true) := by
    simpa [latestRoundSlot, roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, hLastAnswerNZNum]
  have hOnlyUpBranch : ¬ ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hPrevStartedProp :
      s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStarted
  have hPrevStartedVal : (s.storageMapUint 8 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hPrevStarted
  have hDataTsLeVal : dataTimestamp.val ≤ blockTimestamp.val := by
    simpa using hDataTsLe
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowVal : (s.storageMapUint 9 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapVal : Core.Uint256.val 3600 < (sub blockTimestamp (s.storageMapUint 9 (s.storage 5))).val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedVal : (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  by_cases hNeg : slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = true
  · have hNegRaw :
        slt
            (signedDeviationRaw (lastAnswerOf s blockTimestamp)
              (add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))
            0 =
          true := by
      simpa [signedDeviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hNeg
    have hNegBranch :
        slt
            (sdiv
              (mul
                (mul
                  (sub
                    (add data
                      (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                        315360000000000000))
                    (add (s.storageMapUint 7 (s.storage 5))
                      (sdiv
                        (mul
                          (mul (s.storageMapUint 7 (s.storage 5))
                            (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                          (s.storageMapUint 10 (s.storage 5)))
                        315360000000000000)))
                  100000000)
                100)
              (add (s.storageMapUint 7 (s.storage 5))
                (sdiv
                  (mul
                    (mul (s.storageMapUint 7 (s.storage 5))
                      (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                    (s.storageMapUint 10 (s.storage 5)))
                  315360000000000000)))
            0 =
          true := by
      simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
        HUNDRED_ONE, ONE, YEAR_SECONDS] using hNeg
    have hNegCapProp :
        sub 0 (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) ≤
          s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
      simpa [signedDeviationOfSafeCall, deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, deviationAbsRaw, absSignedWord, maxAnswerDeviationOf, maxAnswerDeviationSlot,
        hCandidateNZDenom, hNegRaw] using hDeviationCap
    have hNegCapVal :
        (sub 0
              (sdiv
                (mul
                  (mul
                    (sub
                      (add data
                        (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                          315360000000000000))
                      (add (s.storageMapUint 7 (s.storage 5))
                        (sdiv
                          (mul
                            (mul (s.storageMapUint 7 (s.storage 5))
                              (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                            (s.storageMapUint 10 (s.storage 5)))
                          315360000000000000)))
                    100000000)
                  100)
                (add (s.storageMapUint 7 (s.storage 5))
                  (sdiv
                    (mul
                      (mul (s.storageMapUint 7 (s.storage 5))
                        (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                      (s.storageMapUint 10 (s.storage 5)))
                    315360000000000000)))).val ≤
          (s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot).val := by
      simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
        HUNDRED_ONE, ONE, YEAR_SECONDS] using hNegCapProp
    unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
    simp only [getStorage, getMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run, ContractResult.snd]
    constructor
    · simp [hLastUpdatedBranch, hPrevStartedProp, hDataTsLe, hCandidateZeroBranch, hLastAnswerNZBranch,
        hOnlyUpBranch, hNegBranch, hNegCapVal, hTimestampUnderflowProp, hTimeGapProp, hStartedProp,
        signedDeviationOfSafeCall, signedDeviationRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf,
        lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundUpdatedAtSlot, roundGrowthAprSlot,
        onlyUpSlot, GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS, hLastUpdatedNZNum, hOnlyUp0Num,
        hCandidateNZNum, hLastAnswerNZNum, candidateLivePrice,
        applyGrowthNowRaw, applyGrowthAtRaw, hNegRaw, hPrevStartedVal, hDataTsLeVal, hTimestampUnderflowVal,
        hTimeGapVal, hStartedVal, hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch,
        hDataTsLt, nextRoundIdOf, writeStorageAfterRound, setStorage, setMappingUint, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
    · simp [hLastUpdatedBranch, hPrevStartedProp, hDataTsLe, hCandidateZeroBranch, hLastAnswerNZBranch,
        hOnlyUpBranch, hNegBranch, hNegCapVal, hTimestampUnderflowProp, hTimeGapProp, hStartedProp,
        signedDeviationOfSafeCall, signedDeviationRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf,
        lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundUpdatedAtSlot, roundGrowthAprSlot,
        onlyUpSlot, GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS, hLastUpdatedNZNum, hOnlyUp0Num,
        hCandidateNZNum, hLastAnswerNZNum, candidateLivePrice,
        applyGrowthNowRaw, applyGrowthAtRaw, hNegRaw, hPrevStartedVal, hDataTsLeVal, hTimestampUnderflowVal,
        hTimeGapVal, hStartedVal, hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch,
        hDataTsLt, nextRoundIdOf, writeMapUintAfterRound, setStorage, setMappingUint, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
  · have hNegRaw :
        slt
            (signedDeviationRaw (lastAnswerOf s blockTimestamp)
              (add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))
            0 =
          false := by
      simpa [signedDeviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hNeg
    have hNegBranch :
        slt
            (sdiv
              (mul
                (mul
                  (sub
                    (add data
                      (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                        315360000000000000))
                    (add (s.storageMapUint 7 (s.storage 5))
                      (sdiv
                        (mul
                          (mul (s.storageMapUint 7 (s.storage 5))
                            (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                          (s.storageMapUint 10 (s.storage 5)))
                        315360000000000000)))
                  100000000)
                100)
              (add (s.storageMapUint 7 (s.storage 5))
                (sdiv
                  (mul
                    (mul (s.storageMapUint 7 (s.storage 5))
                      (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                    (s.storageMapUint 10 (s.storage 5)))
                  315360000000000000)))
            0 =
          false := by
      simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
        HUNDRED_ONE, ONE, YEAR_SECONDS] using hNeg
    have hPosCapProp :
        signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s ≤
          s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
      simpa [signedDeviationOfSafeCall, deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, deviationAbsRaw, absSignedWord, maxAnswerDeviationOf, maxAnswerDeviationSlot,
        hCandidateNZDenom, hNegRaw] using hDeviationCap
    have hPosCapVal :
        (sdiv
              (mul
                (mul
                  (sub
                    (add data
                      (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                        315360000000000000))
                    (add (s.storageMapUint 7 (s.storage 5))
                      (sdiv
                        (mul
                          (mul (s.storageMapUint 7 (s.storage 5))
                            (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                          (s.storageMapUint 10 (s.storage 5)))
                        315360000000000000)))
                  100000000)
                100)
              (add (s.storageMapUint 7 (s.storage 5))
                (sdiv
                  (mul
                    (mul (s.storageMapUint 7 (s.storage 5))
                      (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                    (s.storageMapUint 10 (s.storage 5)))
                  315360000000000000))).val ≤
          (s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot).val := by
      simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
        HUNDRED_ONE, ONE, YEAR_SECONDS] using hPosCapProp
    unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
    simp only [getStorage, getMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run, ContractResult.snd]
    constructor
    · simp [hLastUpdatedBranch, hPrevStartedProp, hDataTsLe, hCandidateZeroBranch, hLastAnswerNZBranch,
        hOnlyUpBranch, hNegBranch, hPosCapVal, hTimestampUnderflowProp, hTimeGapProp, hStartedProp,
        signedDeviationOfSafeCall, signedDeviationRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf,
        lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundUpdatedAtSlot, roundGrowthAprSlot,
        onlyUpSlot, GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS, hLastUpdatedNZNum, hOnlyUp0Num,
        hCandidateNZNum, hLastAnswerNZNum, candidateLivePrice,
        applyGrowthNowRaw, applyGrowthAtRaw, hNegRaw, hPrevStartedVal, hDataTsLeVal, hTimestampUnderflowVal,
        hTimeGapVal, hStartedVal, hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch,
        hDataTsLt, nextRoundIdOf, writeStorageAfterRound, setStorage, setMappingUint, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
    · simp [hLastUpdatedBranch, hPrevStartedProp, hDataTsLe, hCandidateZeroBranch, hLastAnswerNZBranch,
        hOnlyUpBranch, hNegBranch, hPosCapVal, hTimestampUnderflowProp, hTimeGapProp, hStartedProp,
        signedDeviationOfSafeCall, signedDeviationRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf,
        lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundUpdatedAtSlot, roundGrowthAprSlot,
        onlyUpSlot, GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS, hLastUpdatedNZNum, hOnlyUp0Num,
        hCandidateNZNum, hLastAnswerNZNum, candidateLivePrice,
        applyGrowthNowRaw, applyGrowthAtRaw, hNegRaw, hPrevStartedVal, hDataTsLeVal, hTimestampUnderflowVal,
        hTimeGapVal, hStartedVal, hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch,
        hDataTsLt, nextRoundIdOf, writeMapUintAfterRound, setStorage, setMappingUint, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, Contract.run, ContractResult.snd]

private theorem setRoundDataSafe_candidate_nonzero_onlyup_on_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : ¬ lastTimestampOf s = 0)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ : lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hCandidateZero : ¬ candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0)
    (hOnlyUp0 : ¬ onlyUpWordOf s = 0)
    (hOnlyUpApr : slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdatedNZNum : s.storageMapUint 9 (s.storage 5) ≠ 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hOnlyUp0Num : s.storage 6 ≠ 0 := by simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hCandidateNZNum :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ≠ 0 := by
    simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
  have hCandidateNZDenom :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) ≠ 0 := by
    simpa [GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS] using hCandidateNZNum
  have hLastAnswerNZNum :
      add (s.storageMapUint 7 (s.storage 5))
          (sdiv
            (mul
              (mul (s.storageMapUint 7 (s.storage 5))
                (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
              (s.storageMapUint 10 (s.storage 5)))
            315360000000000000) ≠ 0 := by
    simpa [lastAnswerOf, applyGrowthNowRaw, applyGrowthAtRaw,
      lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf,
      latestRoundSlot, roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot] using hLastAnswerNZ
  have hLastUpdatedBranch :
      ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdatedNZNum]
  have hCandidateZeroBranch :
      ¬ ((add data
              (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ==
            0) =
          true) := by
    simp [hCandidateNZNum]
  have hLastAnswerNZBranch :
      ((add
              (s.storageMapUint CustomFeedGrowthSafe.roundAnswer.slot
                (s.storage CustomFeedGrowthSafe.latestRound.slot))
              (sdiv
                (mul
                  (mul
                    (s.storageMapUint CustomFeedGrowthSafe.roundAnswer.slot
                      (s.storage CustomFeedGrowthSafe.latestRound.slot))
                    (sub blockTimestamp
                      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                        (s.storage CustomFeedGrowthSafe.latestRound.slot))))
                  (s.storageMapUint CustomFeedGrowthSafe.roundGrowthApr.slot
                    (s.storage CustomFeedGrowthSafe.latestRound.slot)))
                315360000000000000) !=
            0) =
        true) := by
    simpa [latestRoundSlot, roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, hLastAnswerNZNum]
  have hOnlyUpBranch : ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hOnlyUpAprBranch : ¬ (slt growthApr 0 = true) := by simpa [hOnlyUpApr]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hPrevStartedProp :
      s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStarted
  have hPrevStartedVal : (s.storageMapUint 8 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hPrevStarted
  have hDataTsLeVal : dataTimestamp.val ≤ blockTimestamp.val := by
    simpa using hDataTsLe
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowVal : (s.storageMapUint 9 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapVal : Core.Uint256.val 3600 < (sub blockTimestamp (s.storageMapUint 9 (s.storage 5))).val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedVal : (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hOnlyUpDeviationRaw :
      slt
          (signedDeviationRaw (lastAnswerOf s blockTimestamp)
            (add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))
          0 =
        false := by
    simpa [signedDeviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using
      hOnlyUpDeviation
  have hOnlyUpDeviationBranch :
      slt
          (sdiv
            (mul
              (mul
                (sub
                  (add data
                    (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                      315360000000000000))
                  (add (s.storageMapUint 7 (s.storage 5))
                    (sdiv
                      (mul
                        (mul (s.storageMapUint 7 (s.storage 5))
                          (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                        (s.storageMapUint 10 (s.storage 5)))
                      315360000000000000)))
                100000000)
              100)
            (add (s.storageMapUint 7 (s.storage 5))
              (sdiv
                (mul
                  (mul (s.storageMapUint 7 (s.storage 5))
                    (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                  (s.storageMapUint 10 (s.storage 5)))
                315360000000000000)))
          0 =
        false := by
    simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
      applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
      roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
      HUNDRED_ONE, ONE, YEAR_SECONDS] using hOnlyUpDeviation
  have hPosCapProp :
      signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s ≤
        s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
    simpa [signedDeviationOfSafeCall, deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw,
      applyGrowthAtRaw, deviationAbsRaw, absSignedWord, maxAnswerDeviationOf, maxAnswerDeviationSlot,
      hCandidateNZDenom, hOnlyUpDeviationRaw] using hDeviationCap
  have hPosCapVal :
      (sdiv
            (mul
              (mul
                (sub
                  (add data
                    (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                      315360000000000000))
                  (add (s.storageMapUint 7 (s.storage 5))
                    (sdiv
                      (mul
                        (mul (s.storageMapUint 7 (s.storage 5))
                          (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                        (s.storageMapUint 10 (s.storage 5)))
                      315360000000000000)))
                100000000)
              100)
            (add (s.storageMapUint 7 (s.storage 5))
              (sdiv
                (mul
                  (mul (s.storageMapUint 7 (s.storage 5))
                    (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                  (s.storageMapUint 10 (s.storage 5)))
                315360000000000000))).val ≤
        (s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot).val := by
    simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
      applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
      roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
      HUNDRED_ONE, ONE, YEAR_SECONDS] using hPosCapProp
  unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
  simp only [getStorage, getMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run, ContractResult.snd]
  constructor
  · simp [hLastUpdatedBranch, hPrevStartedProp, hDataTsLe, hCandidateZeroBranch, hLastAnswerNZBranch,
      hOnlyUpBranch, hOnlyUpDeviationBranch, hPosCapVal, hOnlyUpAprBranch, hTimestampUnderflowProp,
      signedDeviationOfSafeCall, signedDeviationRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf,
      lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
      roundAnswerSlot, roundStartedAtSlot, roundUpdatedAtSlot, roundGrowthAprSlot, onlyUpSlot,
      GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS, hLastUpdatedNZNum, hOnlyUp0Num, hCandidateNZNum,
      hLastAnswerNZNum, candidateLivePrice,
      applyGrowthNowRaw, applyGrowthAtRaw, hOnlyUpDeviationRaw, hPrevStartedVal, hDataTsLeVal,
      hTimestampUnderflowVal,
      hTimeGapVal, hStartedVal,
      hTimeGapProp, hStartedProp, hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch,
      hDataTsLt, nextRoundIdOf, writeStorageAfterRound, setStorage, setMappingUint, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contract.run, ContractResult.snd]
  · simp [hLastUpdatedBranch, hPrevStartedProp, hDataTsLe, hCandidateZeroBranch, hLastAnswerNZBranch,
      hOnlyUpBranch, hOnlyUpDeviationBranch, hPosCapVal, hOnlyUpAprBranch, hTimestampUnderflowProp,
      signedDeviationOfSafeCall, signedDeviationRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf,
      lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
      roundAnswerSlot, roundStartedAtSlot, roundUpdatedAtSlot, roundGrowthAprSlot, onlyUpSlot,
      GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS, hLastUpdatedNZNum, hOnlyUp0Num, hCandidateNZNum,
      hLastAnswerNZNum, candidateLivePrice,
      applyGrowthNowRaw, applyGrowthAtRaw, hOnlyUpDeviationRaw, hPrevStartedVal, hDataTsLeVal,
      hTimestampUnderflowVal,
      hTimeGapVal, hStartedVal,
      hTimeGapProp, hStartedProp, hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch,
      hDataTsLt, nextRoundIdOf, writeMapUintAfterRound, setStorage, setMappingUint, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contract.run, ContractResult.snd]

private theorem setRoundDataSafe_projected_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  by_cases hLastUpdated0 : lastTimestampOf s = 0
  · by_cases hOnlyUp0 : onlyUpWordOf s = 0
    · exact setRoundDataSafe_zero_history_onlyup_off_writes data dataTimestamp growthApr blockTimestamp s
        hLastUpdated0 hOnlyUp0 hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi
        hDataTsLt storageSlot mapSlot k
    · have hOnlyUpNZ : onlyUpWordOf s != 0 := by simpa using hOnlyUp0
      exact setRoundDataSafe_zero_history_onlyup_on_writes data dataTimestamp growthApr blockTimestamp s
        hLastUpdated0 hOnlyUp0 (hOnlyUpApr hOnlyUpNZ) hTimeOrder hTimeGap hStarted hDataLo hDataHi
        hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k
  · have hLastUpdatedNZ : lastTimestampOf s != 0 := by simpa using hLastUpdated0
    have hPrevStarted' : lastStartedAtOf s <= blockTimestamp := hPrevStarted hLastUpdatedNZ
    have hDataTsLe' : dataTimestamp <= blockTimestamp := hDataTsLe hLastUpdatedNZ
    have hDeviationCap' :
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s :=
      hDeviationCap hLastUpdatedNZ
    by_cases hCandidateZero' : candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0
    · by_cases hOnlyUp0 : onlyUpWordOf s = 0
      · exact setRoundDataSafe_candidate_zero_onlyup_off_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 hPrevStarted' hDataTsLe' hDeviationCap' hCandidateZero' hOnlyUp0
          hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k
      · have hOnlyUpNZ : onlyUpWordOf s != 0 := by simpa using hOnlyUp0
        exact setRoundDataSafe_candidate_zero_onlyup_on_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 hPrevStarted' hDataTsLe' hDeviationCap' hCandidateZero' hOnlyUp0
          (hOnlyUpApr hOnlyUpNZ) hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi
          hDataTsLt storageSlot mapSlot k
    · have hLastAnswerNZ' : lastAnswerOf s blockTimestamp != 0 :=
        hLastAnswerNZ hLastUpdatedNZ hCandidateZero'
      by_cases hOnlyUp0 : onlyUpWordOf s = 0
      · exact setRoundDataSafe_candidate_nonzero_onlyup_off_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 hPrevStarted' hDataTsLe' hLastAnswerNZ' hDeviationCap' hCandidateZero' hOnlyUp0
          hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k
      · have hOnlyUpNZ : onlyUpWordOf s != 0 := by simpa using hOnlyUp0
        exact setRoundDataSafe_candidate_nonzero_onlyup_on_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 hPrevStarted' hDataTsLe' hLastAnswerNZ'
          (hOnlyUpDeviation hLastUpdatedNZ hOnlyUpNZ) hDeviationCap' hCandidateZero' hOnlyUp0
          (hOnlyUpApr hOnlyUpNZ) hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi
          hDataTsLt storageSlot mapSlot k

private theorem setRoundDataSafe_writes_latestRound
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    latestRoundOf s' = nextRoundIdOf s := by
  dsimp [latestRoundOf]
  have hWrites := setRoundDataSafe_projected_writes data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
    CustomFeedGrowthSafe.latestRound.slot 0 0
  simpa [writeStorageAfterRound, nextRoundIdOf, latestRoundOf] using hWrites.1

private theorem setRoundDataSafe_writes_answer
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    roundAnswerOf s' (nextRoundIdOf s) = data := by
  dsimp [roundAnswerOf]
  have hWrites := setRoundDataSafe_projected_writes data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
    0 CustomFeedGrowthSafe.roundAnswer.slot (nextRoundIdOf s)
  simpa [writeMapUintAfterRound, nextRoundIdOf, roundAnswerSlot, roundStartedAtSlot,
    roundUpdatedAtSlot, roundGrowthAprSlot] using hWrites.2

private theorem setRoundDataSafe_writes_startedAt
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    roundStartedAtOf s' (nextRoundIdOf s) = dataTimestamp := by
  dsimp [roundStartedAtOf]
  have hWrites := setRoundDataSafe_projected_writes data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
    0 CustomFeedGrowthSafe.roundStartedAt.slot (nextRoundIdOf s)
  simpa [writeMapUintAfterRound, nextRoundIdOf, roundAnswerSlot, roundStartedAtSlot,
    roundUpdatedAtSlot, roundGrowthAprSlot] using hWrites.2

private theorem setRoundDataSafe_writes_growthApr
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    roundGrowthAprOf s' (nextRoundIdOf s) = growthApr := by
  dsimp [roundGrowthAprOf]
  have hWrites := setRoundDataSafe_projected_writes data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
    0 CustomFeedGrowthSafe.roundGrowthApr.slot (nextRoundIdOf s)
  simpa [writeMapUintAfterRound, nextRoundIdOf, roundAnswerSlot, roundStartedAtSlot,
    roundUpdatedAtSlot, roundGrowthAprSlot] using hWrites.2

theorem setRoundDataSafe_rejects_zero_price
    (dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLatest : latestRoundOf s >= 1)
    (hLastUpdated : lastTimestampOf s != 0)
    (hMaxDev : maxAnswerDeviationOf s < HUNDRED_ONE) :
    setRoundDataSafe_rejects_zero_price_spec dataTimestamp growthApr blockTimestamp s := by
  let _ := hLatest
  unfold setRoundDataSafe_rejects_zero_price_spec safeCallResult
  have hLastUpdatedNZNum : s.storageMapUint 9 (s.storage 5) ≠ 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated
  have hLastUpdatedSlot : ¬ s.storageMapUint 9 (s.storage 5) = 0 := by
    simpa using hLastUpdatedNZNum
  have hLastUpdatedBranch :
      ¬
        s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) =
          0 := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hLastUpdatedNZNum
  have hZeroMul :
      mul (mul 0 (sub blockTimestamp dataTimestamp)) growthApr = 0 := by
    simp [Verity.Core.Uint256.mul]
  have hZeroPriceNum :
      add 0 (sdiv (mul (mul 0 (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) = 0 := by
    rw [hZeroMul]
    native_decide
  have hZeroPriceBranch :
      ((add 0 (sdiv (mul (mul 0 (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ==
            0) =
          true) := by
    simpa [hZeroPriceNum]
  by_cases hPrevStarted : lastStartedAtOf s <= blockTimestamp
  · by_cases hDataTsLe : dataTimestamp <= blockTimestamp
    · have hNoCap : ¬ 10000000000 <= maxAnswerDeviationOf s := by
        simpa [HUNDRED_ONE] using hMaxDev
      have hPrevStartedVal : (s.storageMapUint 8 (s.storage 5)).val ≤ blockTimestamp.val := by
        simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
          hPrevStarted
      have hPrevStartedProp :
          s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
              (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
            blockTimestamp := by
        simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
          hPrevStarted
      have hPrevStartedValProp :
          (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
            blockTimestamp.val := by
        simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStartedVal
      have hDataTsLeVal : dataTimestamp.val ≤ blockTimestamp.val := by
        simpa using hDataTsLe
      have hNoCapNum : ¬ 10000000000 <= s.storage 0 := by
        simpa [maxAnswerDeviationOf, maxAnswerDeviationSlot] using hNoCap
      have hNoCapProp : ¬ 10000000000 <= s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
        simpa [maxAnswerDeviationSlot] using hNoCapNum
      have hNoCapVal :
          ¬ Core.Uint256.val 10000000000 ≤
              (s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot).val := by
        simpa using hNoCapProp
      simp [CustomFeedGrowthSafe.setRoundDataSafe, getStorage, getMappingUint, Verity.require, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess]
      rw [if_neg hLastUpdatedBranch]
      simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
        ContractResult.isSuccess, hPrevStartedValProp, hDataTsLeVal, hZeroPriceNum, hNoCapVal]
    · have hPrevStartedVal : (s.storageMapUint 8 (s.storage 5)).val ≤ blockTimestamp.val := by
        simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
          hPrevStarted
      have hPrevStartedProp :
          s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
              (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
            blockTimestamp := by
        simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
          hPrevStarted
      have hPrevStartedValProp :
          (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
            blockTimestamp.val := by
        simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStartedVal
      have hDataTsLeVal : ¬ dataTimestamp.val ≤ blockTimestamp.val := by
        simpa using hDataTsLe
      simp [CustomFeedGrowthSafe.setRoundDataSafe, getStorage, getMappingUint, Verity.require, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess]
      rw [if_neg hLastUpdatedBranch]
      simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
        ContractResult.isSuccess, hPrevStartedValProp, hDataTsLeVal]
  · have hPrevStartedVal : ¬ (s.storageMapUint 8 (s.storage 5)).val ≤ blockTimestamp.val := by
      simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
        hPrevStarted
    have hPrevStartedProp :
        ¬
          s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
              (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
            blockTimestamp := by
      simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
        hPrevStarted
    have hPrevStartedValProp :
        ¬
          (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
            blockTimestamp.val := by
      simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStartedVal
    simp [CustomFeedGrowthSafe.setRoundDataSafe, getStorage, getMappingUint, Verity.require, Verity.bind,
      Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess]
    rw [if_neg hLastUpdatedBranch]
    simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
      ContractResult.isSuccess, hPrevStartedValProp]

theorem setRoundDataSafe_deviation_bound
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLatest : latestRoundOf s >= 1)
    (hLastUpdated : lastTimestampOf s != 0)
    (hDeviation :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_deviation_bound_spec data dataTimestamp growthApr blockTimestamp s s' := by
  let _ := hLatest
  let _ := hLastUpdated
  simpa [setRoundDataSafe_deviation_bound_spec] using hDeviation

theorem setRoundDataSafe_enforces_time_gap
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_enforces_time_gap_spec blockTimestamp s s' := by
  unfold setRoundDataSafe_enforces_time_gap_spec
  have hTimeOrder' : (lastTimestampOf s : Nat) ≤ (blockTimestamp : Nat) := by
    simpa using hTimeOrder
  have hGap' : ((sub blockTimestamp (lastTimestampOf s) : Uint256) : Nat) > 3600 := by
    simpa using hTimeGap
  rw [Verity.EVM.Uint256.sub_eq_of_le hTimeOrder'] at hGap'
  simpa using hGap'

theorem setRoundDataSafe_startedAt_monotonic
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_startedAt_monotonic_spec data dataTimestamp growthApr blockTimestamp s s' := by
  unfold setRoundDataSafe_startedAt_monotonic_spec
  dsimp
  rw [setRoundDataSafe_writes_latestRound data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  rw [setRoundDataSafe_writes_startedAt data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  exact hStarted

theorem setRoundDataSafe_onlyUp_nonnegative_deviation
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLatest : latestRoundOf s >= 1)
    (hLastUpdated : lastTimestampOf s != 0)
    (hOnlyUpDeviation :
      (onlyUpWordOf s != 0) = true →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_onlyUp_nonnegative_deviation_spec data dataTimestamp growthApr blockTimestamp s s' := by
  let _ := hLatest
  let _ := hLastUpdated
  simpa [setRoundDataSafe_onlyUp_nonnegative_deviation_spec] using hOnlyUpDeviation

theorem setRoundDataSafe_propagates_band_guard
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_propagates_band_guard_spec data dataTimestamp growthApr blockTimestamp s s' := by
  unfold setRoundDataSafe_propagates_band_guard_spec
  dsimp
  rw [setRoundDataSafe_writes_latestRound data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  rw [setRoundDataSafe_writes_answer data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  rw [setRoundDataSafe_writes_growthApr data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  exact ⟨hDataLo, hDataHi, hGrowthLo, hGrowthHi⟩

theorem setRoundDataSafe_full_correctness
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLatest : latestRoundOf s >= 1)
    (hLastUpdated : lastTimestampOf s != 0)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (hRejectZero : maxAnswerDeviationOf s < HUNDRED_ONE) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    SetRoundDataSafeFullCorrectnessSpec data dataTimestamp growthApr blockTimestamp s s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact setRoundDataSafe_rejects_zero_price dataTimestamp growthApr blockTimestamp s
      hLatest hLastUpdated hRejectZero
  · exact setRoundDataSafe_deviation_bound data dataTimestamp growthApr blockTimestamp s
      hLatest hLastUpdated (hDeviationCap hLastUpdated)
  · exact setRoundDataSafe_enforces_time_gap data dataTimestamp growthApr blockTimestamp s
      hTimeOrder hTimeGap
  · exact setRoundDataSafe_startedAt_monotonic data dataTimestamp growthApr blockTimestamp s
      hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
      hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
  · exact setRoundDataSafe_onlyUp_nonnegative_deviation data dataTimestamp growthApr blockTimestamp s
      hLatest hLastUpdated (hOnlyUpDeviation hLastUpdated)
  · exact setRoundDataSafe_propagates_band_guard data dataTimestamp growthApr blockTimestamp s
      hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
      hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt

end Benchmark.Cases.Midas.CustomFeedGrowthSafe
