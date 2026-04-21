import Contracts.Common

namespace Benchmark.Cases.Midas.CustomFeedGrowthSafe

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused Verity slice of Midas `CustomAggregatorV3CompatibleFeedGrowth`.

  This benchmark models the `setRoundDataSafe` wrapper, the inner `setRoundData`
  write, both `applyGrowth` overloads, and `_getDeviation`.

  Simplifications:
  - Access control elided: `onlyAggregatorAdmin` is omitted because the benchmark
    targets the arithmetic and timestamp safety path of successful writes, not the
    admin-role plumbing in `WithMidasAccessControl`.
  - Events, description, versioning, and read-only interface methods omitted:
    they do not affect the state transition proved here.
  - Redundant struct fields `roundId` and `answeredInRound` omitted from storage:
    they are deterministically equal to the written round key and are unused by
    the target theorems.
  - Signed fields remain stored as raw `Uint256` words and are interpreted through
    `toInt256` / `toUint256`, matching Solidity storage layout for `int256`/`int80`.
  - Solidity panic-on-division-by-zero is modeled with explicit `require`s before
    signed division in `_getDeviation`, because Verity's raw `sdiv` follows EVM
    semantics and returns 0 on division-by-zero.
  - Signed overflow checks from Solidity 0.8 are not re-modeled; arithmetic uses
    Verity's native `Int256` word semantics. The benchmark therefore reasons about
    the real contract on the non-overflowing executions targeted by the tasks.
-/

def ONE : Uint256 := 100000000

def HUNDRED_ONE : Uint256 := mul 100 ONE

def YEAR_SECONDS : Uint256 := 31536000

def GROWTH_DENOMINATOR : Uint256 := mul HUNDRED_ONE YEAR_SECONDS

def absSignedWord (value : Uint256) : Uint256 :=
  if slt value 0 then sub 0 value else value

def applyGrowthAtRaw
    (answer growthApr timestampFrom timestampTo : Uint256) : Uint256 :=
  let passedSeconds := sub timestampTo timestampFrom
  let interest := sdiv (mul (mul answer passedSeconds) growthApr) GROWTH_DENOMINATOR
  add answer interest

def applyGrowthNowRaw
    (answer growthApr timestampFrom blockTimestamp : Uint256) : Uint256 :=
  applyGrowthAtRaw answer growthApr timestampFrom blockTimestamp

def signedDeviationRaw (lastPrice newPrice : Uint256) : Uint256 :=
  sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice

def deviationAbsRaw (lastPrice newPrice : Uint256) : Uint256 :=
  if newPrice == 0 then
    HUNDRED_ONE
  else
    absSignedWord (signedDeviationRaw lastPrice newPrice)

def maxAnswerDeviationOf (s : ContractState) : Uint256 := s.storage 0

def minAnswerOf (s : ContractState) : Uint256 := s.storage 1

def maxAnswerOf (s : ContractState) : Uint256 := s.storage 2

def minGrowthAprOf (s : ContractState) : Uint256 := s.storage 3

def maxGrowthAprOf (s : ContractState) : Uint256 := s.storage 4

def latestRoundOf (s : ContractState) : Uint256 := s.storage 5

def onlyUpWordOf (s : ContractState) : Uint256 := s.storage 6

def onlyUpEnabled (s : ContractState) : Prop := onlyUpWordOf s != 0

def roundAnswerOf (s : ContractState) (roundId : Uint256) : Uint256 :=
  s.storageMapUint 7 roundId

def roundStartedAtOf (s : ContractState) (roundId : Uint256) : Uint256 :=
  s.storageMapUint 8 roundId

def roundUpdatedAtOf (s : ContractState) (roundId : Uint256) : Uint256 :=
  s.storageMapUint 9 roundId

def roundGrowthAprOf (s : ContractState) (roundId : Uint256) : Uint256 :=
  s.storageMapUint 10 roundId

def lastTimestampOf (s : ContractState) : Uint256 :=
  roundUpdatedAtOf s (latestRoundOf s)

def lastStartedAtOf (s : ContractState) : Uint256 :=
  roundStartedAtOf s (latestRoundOf s)

def lastGrowthAprOf (s : ContractState) : Uint256 :=
  roundGrowthAprOf s (latestRoundOf s)

def lastRawAnswerOf (s : ContractState) : Uint256 :=
  roundAnswerOf s (latestRoundOf s)

def lastAnswerOf (s : ContractState) (blockTimestamp : Uint256) : Uint256 :=
  applyGrowthNowRaw (lastRawAnswerOf s) (lastGrowthAprOf s) (lastStartedAtOf s) blockTimestamp

def candidateLivePrice
    (data dataTimestamp growthApr blockTimestamp : Uint256) : Uint256 :=
  applyGrowthNowRaw data growthApr dataTimestamp blockTimestamp

def nextRoundIdOf (s : ContractState) : Uint256 := add (latestRoundOf s) 1

verity_contract CustomFeedGrowthSafe where
  storage
    maxAnswerDeviation : Uint256 := slot 0
    minAnswer : Uint256 := slot 1
    maxAnswer : Uint256 := slot 2
    minGrowthApr : Uint256 := slot 3
    maxGrowthApr : Uint256 := slot 4
    latestRound : Uint256 := slot 5
    onlyUp : Uint256 := slot 6
    roundAnswer : Uint256 → Uint256 := slot 7
    roundStartedAt : Uint256 → Uint256 := slot 8
    roundUpdatedAt : Uint256 → Uint256 := slot 9
    roundGrowthApr : Uint256 → Uint256 := slot 10

  function applyGrowthAt
      (answer : Uint256, growthApr : Uint256, timestampFrom : Uint256, timestampTo : Uint256) :
      Uint256 := do
    require (timestampFrom <= timestampTo) "CAG: timestampTo < timestampFrom"
    let passedSeconds := sub timestampTo timestampFrom
    let interest := sdiv (mul (mul answer passedSeconds) growthApr) 315360000000000000
    return (add answer interest)

  function applyGrowth
      (answer : Uint256, growthApr : Uint256, timestampFrom : Uint256, blockTimestamp : Uint256) :
      Uint256 := do
    require (timestampFrom <= blockTimestamp) "CAG: timestampTo < timestampFrom"
    let passedSeconds := sub blockTimestamp timestampFrom
    let interest := sdiv (mul (mul answer passedSeconds) growthApr) 315360000000000000
    return (add answer interest)

  function _getDeviation
      (lastPrice : Uint256, newPrice : Uint256, validateOnlyUp : Bool) : Uint256 := do
    if newPrice == 0 then
      return 10000000000
    else
      require (lastPrice != 0) "CAG: last price is zero"
      let deviation := sdiv (mul (mul (sub newPrice lastPrice) 100000000) 100) lastPrice
      if validateOnlyUp then
        if slt deviation 0 then
          require false "CAG: deviation is negative"
        else
          pure ()
      else
        pure ()
      if slt deviation 0 then
        return (sub 0 deviation)
      else
        return deviation

  function setRoundData
      (data : Uint256, dataTimestamp : Uint256, growthApr : Uint256, blockTimestamp : Uint256) :
      Unit := do
    let minAnswer_ ← getStorage minAnswer
    let maxAnswer_ ← getStorage maxAnswer
    let minGrowthApr_ ← getStorage minGrowthApr
    let maxGrowthApr_ ← getStorage maxGrowthApr
    let latestRound_ ← getStorage latestRound

    if slt data minAnswer_ then
      require false "CAG: out of [min;max]"
    else
      if sgt data maxAnswer_ then
        require false "CAG: out of [min;max]"
      else
        pure ()
    if slt growthApr minGrowthApr_ then
      require false "CAG: out of [min;max] growth"
    else
      if sgt growthApr maxGrowthApr_ then
        require false "CAG: out of [min;max] growth"
      else
        pure ()
    require (dataTimestamp < blockTimestamp) "CAG: timestamp >= now"

    let roundId := add latestRound_ 1
    setMappingUint roundAnswer roundId data
    setMappingUint roundStartedAt roundId dataTimestamp
    setMappingUint roundUpdatedAt roundId blockTimestamp
    setMappingUint roundGrowthApr roundId growthApr
    setStorage latestRound roundId

  function setRoundDataSafe
      (data : Uint256, dataTimestamp : Uint256, growthApr : Uint256, blockTimestamp : Uint256) :
      Unit := do
    let onlyUp_ ← getStorage onlyUp
    let latestRound_ ← getStorage latestRound
    let lastUpdatedAt ← getMappingUint roundUpdatedAt latestRound_
    let lastStartedAt ← getMappingUint roundStartedAt latestRound_
    let lastRawAnswer ← getMappingUint roundAnswer latestRound_
    let lastGrowthApr ← getMappingUint roundGrowthApr latestRound_
    let maxAnswerDeviation_ ← getStorage maxAnswerDeviation
    let minAnswer_ ← getStorage minAnswer
    let maxAnswer_ ← getStorage maxAnswer
    let minGrowthApr_ ← getStorage minGrowthApr
    let maxGrowthApr_ ← getStorage maxGrowthApr

    if lastUpdatedAt != 0 then
      require (lastStartedAt <= blockTimestamp) "CAG: timestampTo < timestampFrom"
      let lastPassedSeconds := sub blockTimestamp lastStartedAt
      let lastInterest := sdiv (mul (mul lastRawAnswer lastPassedSeconds) lastGrowthApr) 315360000000000000
      let lastAnswer_ := add lastRawAnswer lastInterest

      require (dataTimestamp <= blockTimestamp) "CAG: timestampTo < timestampFrom"
      let passedSeconds := sub blockTimestamp dataTimestamp
      let interest := sdiv (mul (mul data passedSeconds) growthApr) 315360000000000000
      let newLivePrice := add data interest
      let signedDeviation := sdiv (mul (mul (sub newLivePrice lastAnswer_) 100000000) 100) lastAnswer_

      if newLivePrice == 0 then
        require (10000000000 <= maxAnswerDeviation_) "CAG: !deviation"
      else
        require (lastAnswer_ != 0) "CAG: last price is zero"
        if onlyUp_ != 0 then
          if slt signedDeviation 0 then
            require false "CAG: deviation is negative"
          else
            pure ()
        else
          pure ()
        if slt signedDeviation 0 then
          require (sub 0 signedDeviation <= maxAnswerDeviation_) "CAG: !deviation"
        else
          require (signedDeviation <= maxAnswerDeviation_) "CAG: !deviation"
    else
      pure ()

    if onlyUp_ != 0 then
      if slt growthApr 0 then
        require false "CAG: negative apr"
      else
        pure ()
    else
      pure ()

    require (lastUpdatedAt <= blockTimestamp) "CAG: timestamp underflow"
    require (sub blockTimestamp lastUpdatedAt > 3600) "CAG: not enough time passed"
    require (dataTimestamp > lastStartedAt) "CAG: timestamp <= last startedAt"
    if slt data minAnswer_ then
      require false "CAG: out of [min;max]"
    else
      if sgt data maxAnswer_ then
        require false "CAG: out of [min;max]"
      else
        pure ()
    if slt growthApr minGrowthApr_ then
      require false "CAG: out of [min;max] growth"
    else
      if sgt growthApr maxGrowthApr_ then
        require false "CAG: out of [min;max] growth"
      else
        pure ()
    require (dataTimestamp < blockTimestamp) "CAG: timestamp >= now"

    let roundId := add latestRound_ 1
    setMappingUint roundAnswer roundId data
    setMappingUint roundStartedAt roundId dataTimestamp
    setMappingUint roundUpdatedAt roundId blockTimestamp
    setMappingUint roundGrowthApr roundId growthApr
    setStorage latestRound roundId

end Benchmark.Cases.Midas.CustomFeedGrowthSafe
