import Contracts.Common

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Verity model of the Alchemix V3 earmarking accounting system.

  Upstream: alchemix-finance/v3 (master)
  Commit:   117c95b6ee11a75221d6fbdc79f16ac6acdb96f5
  File:     src/AlchemistV3.sol
  In scope: _earmark, _sync, _computeUnrealizedAccount, redeem,
            _subEarmarkedDebt, _subDebt

  The benchmark targets the lazy-projected earmark conservation invariant
  agreed with the Alchemix team (Ov3rkoalafied, 2026-04-24):

      Sum over active accounts of project(account, _earmarkWeight,
        _redemptionWeight, _survivalAccumulator).newEarmarked
        = cumulativeEarmarked

  where `project = _computeUnrealizedAccount`. The literal "sum of stored
  account.earmarked equals cumulativeEarmarked" is provably false on the
  deployed code (see source comment line 1014: "Global can lag local by
  rounding") because per-account earmarked is updated lazily inside
  _sync(tokenId), not eagerly by _earmark. The lazy-projected version is
  the property the design actually maintains.

  Simplifications
  ----------------
  What was simplified:
  - `mulQ128(a, b)` and `divQ128(a, b)` are modeled as `mulDivDown` against
    `2^128` and treated as exact (no floor-rounding drift) for the purposes
    of the conservation invariant.
  Why:
  - The deployed code uses floor-rounding Q128.128 fixed-point arithmetic,
    so the literal per-step sum can drift from `cumulativeEarmarked` by
    bounded ulp errors. The team confirmed they care about the design-level
    conservation property, not a bounded-drift bound. We absorb the rounding
    into an explicit linearity assumption surfaced in `Specs.lean` and the
    case-study article. A follow-up case can sharpen this into a quantitative
    bounded-drift theorem.

  What was simplified:
  - The set of active token IDs is passed as an explicit
    `activeIds : FiniteSet Uint256` rather than a ghost field of
    `ContractState`. `Verity.Core.ContractState` exposes
    `knownAddresses : Nat -> FiniteAddressSet` for `mapping(address => T)`
    cases (used by `Verity.Specs.Common.Sum.sumBalances`) but has no
    parallel `knownTokenIds : Nat -> FiniteSet Uint256` for
    `mapping(uint256 => T)` cases.
  Why:
  - Verity-gap, surfaced as a proposed issue. Workaround is purely
    spec-level: pass the finset explicitly. Semantics preserved.

  What was simplified:
  - The cross-epoch branch of `_computeUnrealizedAccount` (lines 1539-1564
    of the source: when the earmark epoch advances between an account's
    last sync and now, the projection splits at the boundary using the
    `_earmarkEpochStartRedemptionWeight` / `_earmarkEpochStartSurvivalAccumulator`
    snapshot mappings) is folded into the same-epoch path.
  Why:
  - This first-pass case targets the within-epoch conservation property,
    which is the dominant operational regime. The cross-epoch reconciliation
    logic is correctness-preserving but adds substantial proof surface
    around the boundary checkpoint mappings. A follow-up case can extend
    coverage.

  What was simplified:
  - The default same-epoch sub-branch of `_computeUnrealizedAccount`
    (source line 1517: `earmarkedUnredeemed = mulQ128(userExposure,
    unredeemedRatio)` via `_survivalAccumulator` diff) is collapsed into
    the telescoped same-epoch sub-branch (source line 1530:
    `earmarkedUnredeemed = mulQ128(earmarkRaw, survivalRatio)`).
  Why:
  - Under Q128 idealization the two branches coincide algebraically: the
    telescoped form is what the source uses when the survival accumulator
    matches the per-account-rounded computation, and idealizing rounding
    means it always matches. The default-path scaffolding (`earmarkSurvival`
    extraction, `survivalDiff` clamping) is purely there to absorb floor
    drift between the two formulas in the deployed contract.

  What was simplified:
  - The `if (newEarmarked > newDebt) newEarmarked = newDebt;` cap (source
    lines 1503 and 1578) is omitted from the projection.
  Why:
  - Under the conservation invariant pre-state and Q128 idealization, the
    cap is provably a no-op (one of the side-properties carried by the
    invariant is `account.earmarked ≤ account.debt`). The cap is a
    defensive guard against rounding drift, not a semantic feature of
    the lazy-accrual model.

  What was simplified:
  - When `redeem(amount)` is called with `amount == liveEarmarked` (full
    wipe), the source advances the redemption epoch and resets the index
    via `_packRed(oldEpoch + 1, ONE_Q128)`. The model writes
    `redemptionWeight := mulQ128(redemptionWeight, 0) = 0` instead.
  Why:
  - The model treats `redemptionWeight` as a flat Q128 weight, not a
    packed (epoch, index) pair. On every consumer path (the survival
    ratio `divQ128(rW, lastRW)` in `syncAccount`), both representations
    yield the same survival ratio of 0 once the wipe has happened, so
    the conservation invariant is preserved. The representation
    divergence is invisible to the invariant.

  What was simplified:
  - Early-returns and conditional state writes are encoded with pure `ite`
    over the new value (writing the unchanged value back) rather than
    monadic if/else.
  Why:
  - Multi-branch monadic if/else with reads is brittle inside
    `verity_contract` bodies. Keeping all writes unconditional with
    `ite`-computed new values preserves semantics and matches the pattern
    used in Wildcat BorrowLiquiditySafety.

  What was simplified:
  - External calls (`ITransmuter(transmuter).queryGraph(...)`,
    `TokenUtils.safeBalanceOf(myt, transmuter)`, `TokenUtils.safeTransfer`)
    are modeled as opaque ghost storage reads / no-ops.
  Why:
  - Standard benchmark practice (see Lido VaulthubLocked, Wildcat
    BorrowLiquiditySafety). The conservation invariant is internal
    accounting; external token movement is a trust boundary.

  What was simplified:
  - `Account` fields not relevant to the invariant (`collateralBalance`,
    `freeCollateral`, `lastCollateralWeight`, `lastMintBlock`,
    `lastRepayBlock`, `lastTotalRedeemedDebt`, `lastTotalRedeemedSharesOut`,
    `mintAllowances`, `allowancesVersion`) are dropped from the model.
  Why:
  - Of the 13 fields in the source `Account` struct, only 5 are read or
    written along paths that affect `cumulativeEarmarked` or
    `account.earmarked`: `debt`, `earmarked`, `lastAccruedEarmarkWeight`,
    `lastAccruedRedemptionWeight`, `lastSurvivalAccumulator`. Keeping
    only those preserves the invariant's semantics.

  What was simplified:
  - Modifiers (`onlyTransmuter`, `onlyAdmin`, etc.), `Initializable`,
    NFT ownership checks, and pause flags are dropped.
  Why:
  - These constrain who can call, not how state evolves. Irrelevant
    to the conservation property.

  What was simplified:
  - `_pendingCoverShares` cover-shares logic and `_syncEarmarkedTransmuterTransfer`
    are abstracted: `_earmark` reads a single opaque "this-window earmark
    amount" from a ghost slot. Cover shares simply reduce that amount
    upstream.
  Why:
  - Cover-shares logic feeds how much gets earmarked this window; it does
    not affect whether per-account earmarked sums to `cumulativeEarmarked`.
    Modeling it would inflate the model without adding to invariant proof
    surface.
-/

/-! ## Constants and Q128 helpers -/

/-- Q128 unit: `2^128`. Source: `AlchemistV3.sol:24` (`uint256(1) << 128`).
    Inlined as the literal `340282366920938463463374607431768211456` in
    `verity_contract` bodies because the macro does not see top-level
    `def`s (see verity issue #1749). The named def is kept here for
    `Specs.lean` and `Proofs.lean`. -/
def ONE_Q128 : Uint256 := 340282366920938463463374607431768211456

/-- `mulQ128(a, b) = floor(a * b / 2^128)`. Treated as exact under the
    Q128-idealization assumption (see `Specs.lean`).

    Source: `FixedPointMath.mulQ128`. -/
def mulQ128 (a b : Uint256) : Uint256 := div (mul a b) ONE_Q128

/-- `divQ128(a, b) = floor(a * 2^128 / b)`.

    Source: `FixedPointMath.divQ128`. -/
def divQ128 (a b : Uint256) : Uint256 := div (mul a ONE_Q128) b

/-! ## Storage layout

  Solidity slot mapping (model-side; not bit-faithful to deployment):

    Globals:
      slot 0 : cumulativeEarmarked
      slot 1 : totalDebt
      slot 2 : _earmarkWeight        (Q128 packed weight)
      slot 3 : _redemptionWeight     (Q128 packed weight)
      slot 4 : _survivalAccumulator  (Q128 accumulator)
      slot 5 : transmuterEarmarkAmount  (ghost: opaque external-call result)

    Per-account (mapping(uint256 => Account), each field at its own slot):
      slot 100 : accountDebt[id]
      slot 101 : accountEarmarked[id]
      slot 102 : accountLastAccruedEarmarkWeight[id]
      slot 103 : accountLastAccruedRedemptionWeight[id]
      slot 104 : accountLastSurvivalAccumulator[id]
-/

verity_contract AlchemistEarmark where
  storage
    -- Globals
    cumulativeEarmarked : Uint256 := slot 0
    totalDebt : Uint256 := slot 1
    earmarkWeight : Uint256 := slot 2
    redemptionWeight : Uint256 := slot 3
    survivalAccumulator : Uint256 := slot 4
    transmuterEarmarkAmount : Uint256 := slot 5

    -- Per-account fields (Uint256-keyed mappings)
    accountDebt : Uint256 → Uint256 := slot 100
    accountEarmarked : Uint256 → Uint256 := slot 101
    accountLastAccruedEarmarkWeight : Uint256 → Uint256 := slot 102
    accountLastAccruedRedemptionWeight : Uint256 → Uint256 := slot 103
    accountLastSurvivalAccumulator : Uint256 → Uint256 := slot 104

  /-
    Models `_earmark()` (AlchemistV3.sol:1582-1641), within-epoch path.

    The early-return on `totalDebt == 0` is encoded by computing
    `effectiveEarmarked = 0` in that case (an `ite` guard), so all writes
    are no-ops on the trivial path.

    Solidity (within-epoch path):
      if (totalDebt == 0) return;
      uint256 amount = transmuterEarmarkAmount;
      uint256 liveUnearmarked = totalDebt - cumulativeEarmarked;
      if (amount > liveUnearmarked) amount = liveUnearmarked;
      if (amount > 0 && liveUnearmarked != 0) {
        uint256 ratioWanted = (amount == liveUnearmarked) ? 0
          : divQ128(liveUnearmarked - amount, liveUnearmarked);
        // _simulateEarmarkPackedUpdate (within-epoch): ratioApplied = ratioWanted
        uint256 ratioApplied = ratioWanted;
        uint256 oldEarmarkWeight = earmarkWeight;
        earmarkWeight = mulQ128(oldEarmarkWeight, ratioApplied);
        uint256 earmarkedFraction = ONE_Q128 - ratioApplied;
        survivalAccumulator += mulQ128(oldEarmarkWeight, earmarkedFraction);
        uint256 newUnearmarked = mulQ128(liveUnearmarked, ratioApplied);
        uint256 effectiveEarmarked = liveUnearmarked - newUnearmarked;
        cumulativeEarmarked += effectiveEarmarked;
      }
  -/
  function earmark () : Unit := do
    let totalDebt_ ← getStorage totalDebt
    let cumulativeEarmarked_ ← getStorage cumulativeEarmarked
    let earmarkWeight_ ← getStorage earmarkWeight
    let survivalAccumulator_ ← getStorage survivalAccumulator
    let amountIn ← getStorage transmuterEarmarkAmount

    let liveUnearmarked := sub totalDebt_ cumulativeEarmarked_
    let amount := ite (amountIn > liveUnearmarked) liveUnearmarked amountIn

    -- Within-epoch: ratioApplied = ratioWanted, inline divQ128.
    let ratioWantedRaw := div (mul (sub liveUnearmarked amount) 340282366920938463463374607431768211456) liveUnearmarked
    let ratioApplied := ite (amount == liveUnearmarked) 0 ratioWantedRaw

    -- Active gate: totalDebt != 0 AND amount != 0 AND liveUnearmarked != 0.
    let active := totalDebt_ != 0 && amount != 0 && liveUnearmarked != 0

    let packedNew := div (mul earmarkWeight_ ratioApplied) 340282366920938463463374607431768211456
    let newEarmarkWeight := ite active packedNew earmarkWeight_

    let earmarkedFraction := sub 340282366920938463463374607431768211456 ratioApplied
    let survivalIncrement := div (mul earmarkWeight_ earmarkedFraction) 340282366920938463463374607431768211456
    let newSurvivalAccumulator :=
      ite active (add survivalAccumulator_ survivalIncrement) survivalAccumulator_

    let newUnearmarked := div (mul liveUnearmarked ratioApplied) 340282366920938463463374607431768211456
    let effectiveEarmarked := sub liveUnearmarked newUnearmarked
    let newCumulativeEarmarked :=
      ite active (add cumulativeEarmarked_ effectiveEarmarked) cumulativeEarmarked_

    setStorage earmarkWeight newEarmarkWeight
    setStorage survivalAccumulator newSurvivalAccumulator
    setStorage cumulativeEarmarked newCumulativeEarmarked

  /-
    Models `_sync(tokenId)` (AlchemistV3.sol:1442-1472), invariant-relevant
    fields only. Within-epoch / within-survival-window projection path.

    Solidity:
      Account storage account = _accounts[tokenId];
      (uint256 newDebt, uint256 newEarmarked, uint256 redeemedTotal) =
        _computeUnrealizedAccount(account, _earmarkWeight,
          _redemptionWeight, _survivalAccumulator);
      // [collateral debit logic — out of scope for invariant]
      account.earmarked = newEarmarked;
      account.debt = newDebt;
      account.lastAccruedEarmarkWeight = _earmarkWeight;
      account.lastAccruedRedemptionWeight = _redemptionWeight;
      account.lastSurvivalAccumulator = _survivalAccumulator;
  -/
  function syncAccount (tokenId : Uint256) : Unit := do
    let earmarkWeight_ ← getStorage earmarkWeight
    let redemptionWeight_ ← getStorage redemptionWeight
    let survivalAccumulator_ ← getStorage survivalAccumulator

    let accountDebt_ ← getMappingUint accountDebt tokenId
    let accountEarmarked_ ← getMappingUint accountEarmarked tokenId
    let lastEW_ ← getMappingUint accountLastAccruedEarmarkWeight tokenId
    let lastRW_ ← getMappingUint accountLastAccruedRedemptionWeight tokenId

    -- _earmarkSurvivalRatio(lastEW, earmarkWeight): ratio of unearmarked
    -- exposure that "stayed unearmarked" since last sync. Inline divQ128.
    let earmarkSurvivalQ := div (mul earmarkWeight_ 340282366920938463463374607431768211456) lastEW_
    let unearmarkSurvivalRatio :=
      ite (lastEW_ == earmarkWeight_) 340282366920938463463374607431768211456
        (ite (lastEW_ == 0) 340282366920938463463374607431768211456 earmarkSurvivalQ)

    -- _redemptionSurvivalRatio(lastRW, redemptionWeight): ratio of
    -- earmarked exposure that "survived" redemptions in this sync window.
    let redemptionSurvivalQ := div (mul redemptionWeight_ 340282366920938463463374607431768211456) lastRW_
    let redemptionSurvivalRatio :=
      ite (lastRW_ == redemptionWeight_) 340282366920938463463374607431768211456
        (ite (lastRW_ == 0) 340282366920938463463374607431768211456 redemptionSurvivalQ)

    -- userExposure = debt - earmarked (unearmarked portion of account debt)
    let userExposure :=
      ite (accountDebt_ > accountEarmarked_) (sub accountDebt_ accountEarmarked_) 0

    -- amount that stayed unearmarked, and the newly earmarked portion
    let unearmarkedRemaining := div (mul userExposure unearmarkSurvivalRatio) 340282366920938463463374607431768211456
    let earmarkRaw := sub userExposure unearmarkedRemaining

    -- Within-epoch redemption survival branch:
    -- newEarmarked = mulQ128(account.earmarked + earmarkRaw, redemptionSurvivalRatio)
    let totalEarmarkedNow := add accountEarmarked_ earmarkRaw
    let newEarmarked := div (mul totalEarmarkedNow redemptionSurvivalRatio) 340282366920938463463374607431768211456
    let redeemedFromAccount := sub totalEarmarkedNow newEarmarked
    let newDebt :=
      ite (accountDebt_ >= redeemedFromAccount) (sub accountDebt_ redeemedFromAccount) 0

    setMappingUint accountDebt tokenId newDebt
    setMappingUint accountEarmarked tokenId newEarmarked
    setMappingUint accountLastAccruedEarmarkWeight tokenId earmarkWeight_
    setMappingUint accountLastAccruedRedemptionWeight tokenId redemptionWeight_
    setMappingUint accountLastSurvivalAccumulator tokenId survivalAccumulator_

  /-
    Models `redeem(amount)` (AlchemistV3.sol:655-731), within-epoch path.
    Only the parts that affect `cumulativeEarmarked`, weights, and `totalDebt`.

    Solidity (after _earmark()):
      uint256 liveEarmarked = cumulativeEarmarked;
      if (amount > liveEarmarked) amount = liveEarmarked;
      if (liveEarmarked != 0 && amount != 0) {
        uint256 ratioWanted = (amount == liveEarmarked) ? 0
          : divQ128(liveEarmarked - amount, liveEarmarked);
        // _redemptionWeight packed update (within-epoch):
        //   ratioApplied = ratioWanted
        redemptionWeight = mulQ128(redemptionWeight, ratioApplied);
        survivalAccumulator = mulQ128(survivalAccumulator, ratioApplied);
        uint256 remainingEarmarked = mulQ128(liveEarmarked, ratioApplied);
        uint256 effectiveRedeemed = liveEarmarked - remainingEarmarked;
        cumulativeEarmarked = remainingEarmarked;
        totalDebt -= effectiveRedeemed;
      }
  -/
  function redeem (amount : Uint256) : Unit := do
    let cumulativeEarmarked_ ← getStorage cumulativeEarmarked
    let totalDebt_ ← getStorage totalDebt
    let redemptionWeight_ ← getStorage redemptionWeight
    let survivalAccumulator_ ← getStorage survivalAccumulator

    let liveEarmarked := cumulativeEarmarked_
    let amountClamped := ite (amount > liveEarmarked) liveEarmarked amount

    -- ratioApplied = ratioWanted (within-epoch); inline divQ128.
    let ratioWantedRaw := div (mul (sub liveEarmarked amountClamped) 340282366920938463463374607431768211456) liveEarmarked
    let ratioApplied := ite (amountClamped == liveEarmarked) 0 ratioWantedRaw

    -- Active gate: liveEarmarked != 0 AND amountClamped != 0.
    let active := liveEarmarked != 0 && amountClamped != 0

    -- Inline mulQ128 for each downstream value.
    let newRedemptionWeightActive := div (mul redemptionWeight_ ratioApplied) 340282366920938463463374607431768211456
    let newSurvivalAccumulatorActive := div (mul survivalAccumulator_ ratioApplied) 340282366920938463463374607431768211456
    let remainingEarmarked := div (mul liveEarmarked ratioApplied) 340282366920938463463374607431768211456
    let effectiveRedeemed := sub liveEarmarked remainingEarmarked

    let newRedemptionWeight := ite active newRedemptionWeightActive redemptionWeight_
    let newSurvivalAccumulator := ite active newSurvivalAccumulatorActive survivalAccumulator_
    let newCumulativeEarmarked := ite active remainingEarmarked cumulativeEarmarked_
    let newTotalDebt := ite active (sub totalDebt_ effectiveRedeemed) totalDebt_

    setStorage redemptionWeight newRedemptionWeight
    setStorage survivalAccumulator newSurvivalAccumulator
    setStorage cumulativeEarmarked newCumulativeEarmarked
    setStorage totalDebt newTotalDebt

  /-
    Models `_subEarmarkedDebt(amountInDebtTokens, accountId)`
    (AlchemistV3.sol:1002-1019).

    Solidity:
      uint256 debt = account.debt;
      uint256 earmarkedDebt = account.earmarked;
      uint256 credit = amountInDebtTokens > debt ? debt : amountInDebtTokens;
      uint256 earmarkToRemove = credit > earmarkedDebt ? earmarkedDebt : credit;
      account.earmarked = earmarkedDebt - earmarkToRemove;
      uint256 remove = earmarkToRemove > cumulativeEarmarked
                          ? cumulativeEarmarked : earmarkToRemove;
      cumulativeEarmarked -= remove;
  -/
  function subEarmarkedDebt (amountInDebtTokens : Uint256, accountId : Uint256) : Unit := do
    let cumulativeEarmarked_ ← getStorage cumulativeEarmarked
    let debt_ ← getMappingUint accountDebt accountId
    let earmarkedDebt_ ← getMappingUint accountEarmarked accountId

    let credit := ite (amountInDebtTokens > debt_) debt_ amountInDebtTokens
    let earmarkToRemove := ite (credit > earmarkedDebt_) earmarkedDebt_ credit

    setMappingUint accountEarmarked accountId (sub earmarkedDebt_ earmarkToRemove)

    let remove := ite (earmarkToRemove > cumulativeEarmarked_)
                    cumulativeEarmarked_ earmarkToRemove
    setStorage cumulativeEarmarked (sub cumulativeEarmarked_ remove)

  /-
    Models `_subDebt(tokenId, amount)` (AlchemistV3.sol:1300-1309), focused
    on the cumulativeEarmarked clamp at line 1306.

    Solidity:
      account.debt -= amount;
      totalDebt -= amount;
      if (cumulativeEarmarked > totalDebt) {
        cumulativeEarmarked = totalDebt;
      }
  -/
  function subDebt (tokenId : Uint256, amount : Uint256) : Unit := do
    let totalDebt_ ← getStorage totalDebt
    let cumulativeEarmarked_ ← getStorage cumulativeEarmarked
    let accountDebt_ ← getMappingUint accountDebt tokenId

    setMappingUint accountDebt tokenId (sub accountDebt_ amount)
    let newTotalDebt := sub totalDebt_ amount
    setStorage totalDebt newTotalDebt

    -- Clamp: if (cumulativeEarmarked > totalDebt) cumulativeEarmarked = totalDebt;
    let newCumulativeEarmarked :=
      ite (cumulativeEarmarked_ > newTotalDebt) newTotalDebt cumulativeEarmarked_
    setStorage cumulativeEarmarked newCumulativeEarmarked

end Benchmark.Cases.Alchemix.EarmarkConservation
