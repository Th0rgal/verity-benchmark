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

namespace CustomFeedGrowthSafe

def maxAnswerDeviation : StorageSlot Uint256 := ⟨0⟩

def minAnswer : StorageSlot Uint256 := ⟨1⟩

def maxAnswer : StorageSlot Uint256 := ⟨2⟩

def minGrowthApr : StorageSlot Uint256 := ⟨3⟩

def maxGrowthApr : StorageSlot Uint256 := ⟨4⟩

def latestRound : StorageSlot Uint256 := ⟨5⟩

def onlyUp : StorageSlot Uint256 := ⟨6⟩

def roundAnswer : StorageSlot (Uint256 → Uint256) := ⟨7⟩

def roundStartedAt : StorageSlot (Uint256 → Uint256) := ⟨8⟩

def roundUpdatedAt : StorageSlot (Uint256 → Uint256) := ⟨9⟩

def roundGrowthApr : StorageSlot (Uint256 → Uint256) := ⟨10⟩

def applyGrowthAt
    (answer : Uint256) (growthApr : Uint256) (timestampFrom : Uint256) (timestampTo : Uint256) :
    Contract Uint256 := do
  require (timestampFrom <= timestampTo) "CAG: timestampTo < timestampFrom"
  let passedSeconds := sub timestampTo timestampFrom
  let interest := sdiv (mul (mul answer passedSeconds) growthApr) GROWTH_DENOMINATOR
  return (add answer interest)

attribute [simp] applyGrowthAt

def applyGrowth
    (answer : Uint256) (growthApr : Uint256) (timestampFrom : Uint256) (blockTimestamp : Uint256) :
    Contract Uint256 := do
  applyGrowthAt answer growthApr timestampFrom blockTimestamp

attribute [simp] applyGrowth

def _getDeviation
    (lastPrice : Uint256) (newPrice : Uint256) (validateOnlyUp : Bool) : Contract Uint256 := do
  if newPrice == 0 then
    return HUNDRED_ONE
  else
    require (lastPrice != 0) "CAG: last price is zero"
    let deviation := sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice
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

attribute [simp] _getDeviation

def lastGrowthApr : Contract Uint256 := do
  let roundId ← getStorage latestRound
  getMappingUint roundGrowthApr roundId

attribute [simp] lastGrowthApr

def lastTimestamp : Contract Uint256 := do
  let roundId ← getStorage latestRound
  getMappingUint roundUpdatedAt roundId

attribute [simp] lastTimestamp

def lastStartedAt : Contract Uint256 := do
  let roundId ← getStorage latestRound
  getMappingUint roundStartedAt roundId

attribute [simp] lastStartedAt

def lastRawAnswer : Contract Uint256 := do
  let roundId ← getStorage latestRound
  getMappingUint roundAnswer roundId

attribute [simp] lastRawAnswer

def lastAnswer (blockTimestamp : Uint256) : Contract Uint256 := do
  let _lastRawAnswer ← lastRawAnswer
  let _lastGrowthApr ← lastGrowthApr
  let _lastStartedAt ← lastStartedAt
  applyGrowth _lastRawAnswer _lastGrowthApr _lastStartedAt blockTimestamp

attribute [simp] lastAnswer

def setRoundData
    (data : Uint256) (dataTimestamp : Uint256) (growthApr : Uint256) (blockTimestamp : Uint256) :
    Contract Unit := do
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

attribute [simp] setRoundData

def setRoundDataSafe
    (data : Uint256) (dataTimestamp : Uint256) (growthApr : Uint256) (blockTimestamp : Uint256) :
    Contract Unit := do
  let _onlyUp ← getStorage onlyUp
  let _lastUpdatedAt ← lastTimestamp

  if _lastUpdatedAt != 0 then
    let deviation ← _getDeviation
      (← lastAnswer blockTimestamp)
      (← applyGrowth data growthApr dataTimestamp blockTimestamp)
      (_onlyUp != 0)
    let maxAnswerDeviation_ ← getStorage maxAnswerDeviation
    require (deviation <= maxAnswerDeviation_) "CAG: !deviation"
  else
    pure ()

  if _onlyUp != 0 then
    if slt growthApr 0 then
      require false "CAG: negative apr"
    else
      pure ()
  else
    pure ()

  require (_lastUpdatedAt <= blockTimestamp) "CAG: timestamp underflow"
  require (sub blockTimestamp _lastUpdatedAt > 3600) "CAG: not enough time passed"
  require (dataTimestamp > (← lastStartedAt)) "CAG: timestamp <= last startedAt"

  setRoundData data dataTimestamp growthApr blockTimestamp

end CustomFeedGrowthSafe

end Benchmark.Cases.Midas.CustomFeedGrowthSafe
