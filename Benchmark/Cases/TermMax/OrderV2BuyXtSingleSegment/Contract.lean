import Contracts.Common

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Verity slice of TermMax `TermMaxOrderV2` mirroring the Solidity source
  structure as faithfully as the current `verity_contract` macro path allows.

  Upstream: term-structure/termmax-contract-v2@64bd47b98e064c7fb91ab4a59b70520e0ec285d5
  Files:
    - contracts/v2/TermMaxOrderV2.sol      (entry, helper stack, _buyXtStep)
    - contracts/v1/lib/TermMaxCurve.sol    (buyXt, cutsReverseIter, calcIntervalProps)
    - contracts/v1/lib/MathLib.sol         (plusInt256)

  Solidity → Verity correspondence (each Solidity helper kept as a separate
  Verity function; storage reads happen in the same callers as in the
  Solidity source):

    swapExactTokenToToken (debtToken → xt branch)  ↔ swapDebtTokenToXtExactInSingleSegment
    _swapAndUpdateReserves(..., _buyXt)            ↔ swapAndUpdateReserves
    _buyXt                                         ↔ buyXt
    _buyToken(..., _buyXtStep)                     ↔ buyToken
    _buyXtStep                                     ↔ buyXtStep
    TermMaxCurve.buyXt                             ↔ buyXtCurve
    TermMaxCurve.cutsReverseIter (single iter.)    ↔ cutsReverseIter
    TermMaxCurve.calcIntervalProps                 ↔ calcIntervalProps

  Documented Verity DSL gaps that prevent further fidelity (each gap was
  verified against `Verity/Macro/Translate.lean` on the lakefile-pinned
  Verity revision):

  G1. `CurveCut[] memory cuts` cannot exist as a parameter or storage field.
      Memory/parameter side: `nested arrays are not supported`
      (Translate.lean:223). Storage side: `storage dynamic arrays currently
      support only one-word elements` (Translate.lean:276).
      ⇒ The single active cut is passed as scalar parameters, with the
         slice constraint `cuts.length == 1 ∧ cuts[0].xtReserve == 0` made
         explicit. The Solidity `for (i = cutId+1; i > 0; i--)` reverse
         iteration collapses to one iteration; the cross-cut branch becomes
         an explicit `revert InsufficientLiquidity()`.

  G2. Solidity `function(...) func` higher-order parameters cannot be passed
      to Verity functions. The only supported bind sources are `getStorage`
      and direct internal helper calls (Translate.lean:1889).
      ⇒ `_swapAndUpdateReserves` and `_buyToken` are specialized to their
         concrete `_buyXt` / `_buyXtStep` callees on this slice.

  G3. Solidity library calls (`TermMaxCurve.buyXt(...)`) cannot be expressed.
      Verity has no `import` / library-link concept; only direct internal
      helper calls within the same `verity_contract` block.
      ⇒ `TermMaxCurve.buyXt`, `cutsReverseIter`, `calcIntervalProps` are
         inlined as helper functions inside the contract.

  G4. Calls to external Lean `def`s from inside `verity_contract` function
      bodies are not supported (verity#1003; see also
      `Benchmark/Cases/Lido/VaulthubLocked/Contract.lean:62`).
      ⇒ `MathLib.plusInt256` is inlined as the `if (b < 0) return a -
         uint256(-b); return a + uint256(b);` ite below.

  G5. Named struct types (`OrderConfig memory config`, `CurveCut memory cut`,
      `FeeConfig memory feeConfig`) are not first-class. Verity provides
      positional `Tuple [...]` only and field names are lost
      (Translate.lean:228, 242).
      ⇒ The handful of relevant fields are passed as named scalar
         parameters so the function signatures remain readable.

  G6. `Int256` is fully supported as a parameter / return / local type with
      `+`, `-`, `*`, `/`, `<`, `>`, `isNeg`, `neg`, `toInt256`, `toUint256`
      — but **not** as a storage field (Translate.lean:340). The
      `cutOffset` value enters this slice as a function parameter, so the
      `Int256` typing is faithful here and the previous open-coded
      two's-complement decoding is no longer needed.

  G7. Solidity 0.8 checked arithmetic on `plusInt256` is not automatic in
      Verity. `add` / `sub` on `Uint256` wrap mod 2^256. Successful-execution
      preconditions in the proof (`signedAddDoesNotOverflow`) play the role
      of Solidity's `Panic(0x11)` revert on overflow.
-/

/-- Pure spec mirror of Solidity `MathLib.plusInt256` (MathLib.sol:146–151). -/
def plusInt256 (a : Uint256) (b : Int256) : Uint256 :=
  if b < 0 then sub a (toUint256 (-b)) else add a (toUint256 b)

/-- Pure spec mirror of the `liqSquare` line of `TermMaxCurve.calcIntervalProps`. -/
def singleSegmentScaledLiqSquare
    (daysToMaturity borrowTakerFeeRatio cutLiqSquare : Uint256) : Uint256 :=
  let nif := add 100000000 borrowTakerFeeRatio
  div (mul (mul cutLiqSquare daysToMaturity) nif) (mul 365 100000000)

/-- Pure spec mirror of the curve XT-output computation on the single-segment
    path (`buyTokenStepBase` first iteration with `oriDelta* = 0`). -/
def singleSegmentBuyXtTokenAmtOut
    (daysToMaturity oriXtReserve debtTokenAmtIn borrowTakerFeeRatio cutLiqSquare : Uint256)
    (cutOffset : Int256) : Uint256 :=
  let liqSquare := singleSegmentScaledLiqSquare daysToMaturity borrowTakerFeeRatio cutLiqSquare
  let vXtReserve := plusInt256 oriXtReserve cutOffset
  let vFtReserve := div liqSquare vXtReserve
  sub vXtReserve (div liqSquare (add vFtReserve debtTokenAmtIn))

verity_contract TermMaxOrderV2BuyXtSingleSegment where
  storage
    virtualXtReserve : Uint256 := slot 0
    nonReentrancyLock : Uint256 := slot 1

  errors
    -- Mirrors `revert UnexpectedAmount(uint256, uint256);`
    -- (TermMaxOrderV2.sol:1096 inside `_buyToken`)
    error UnexpectedAmount(Uint256, Uint256)
    -- Mirrors `revert InsufficientLiquidity();`
    -- (TermMaxCurve.sol:98, 145 — bottom of cutsForwardIter / cutsReverseIter)
    error InsufficientLiquidity()
    -- Solidity revert in `_swapAndUpdateReserves` for the
    -- `isNegetiveXt = false` branch (TermMaxOrderV2.sol:879). Declared
    -- here for completeness even though the `_buyXt` path always takes
    -- the `isNegetiveXt = true` branch and never triggers it.
    error XtReserveTooHigh()

  /-
    Mirrors `TermMaxCurve.calcIntervalProps` (TermMaxCurve.sol:38–49):

      liqSquare = (cut.liqSquare * daysToMaturity * netInterestFactor)
                  / (Constants.DAYS_IN_YEAR * Constants.DECIMAL_BASE);
      vXtReserve = xtReserve.plusInt256(cut.offset);
      vFtReserve = liqSquare / vXtReserve;

    `plusInt256(a, b)` is inlined per Solidity `MathLib.sol:146–151`:
      if (b < 0) return a - uint256(-b);
      return a + uint256(b);
  -/
  function calcIntervalProps
      (netInterestFactor : Uint256, daysToMaturity : Uint256,
       cutLiqSquare : Uint256, cutOffset : Int256, xtReserve : Uint256) :
      Tuple [Uint256, Uint256, Uint256] := do
    let liqSquare :=
      div (mul (mul cutLiqSquare daysToMaturity) netInterestFactor) (mul 365 100000000)
    let vXtReserve := ite (cutOffset < 0)
      (sub xtReserve (toUint256 (sub 0 cutOffset)))
      (add xtReserve (toUint256 cutOffset))
    let vFtReserve := div liqSquare vXtReserve
    return (liqSquare, vXtReserve, vFtReserve)

  /-
    Mirrors `TermMaxCurve.cutsReverseIter` (TermMaxCurve.sol:109–146)
    specialized to a single cut at index 0 with `cuts[0].xtReserve == 0`
    (per gap G1). The for-loop body executes exactly once. The Solidity
    cross-cut branch
        `oriXtReserve < uint(nX) + cuts[idx].xtReserve`
    becomes (with `cuts[0].xtReserve = 0`)
        `oriXtReserve < tokenAmtOut`,
    which we explicitly `revert InsufficientLiquidity()` on, matching the
    Solidity bottom-of-loop revert at line 145 (the cross-cut branch has
    nowhere to advance to in the single-cut slice).

    The inlined `buyXtStep` body (= `buyTokenStepBase` first iteration with
    `oriDeltaXt = 0`, `oriDeltaRhs = 0`) is just
        `tokenAmtOut := vXtReserve - liqSquare / (vFtReserve + debtTokenAmtIn)`
        `deltaFt := debtTokenAmtIn`
    per `TermMaxCurve.sol:284–296` and `:298–307`.
  -/
  function cutsReverseIter
      (netInterestFactor : Uint256, daysToMaturity : Uint256,
       cutLiqSquare : Uint256, cutOffset : Int256,
       oriXtReserve : Uint256, debtTokenAmtIn : Uint256) :
      Tuple [Uint256, Uint256] := do
    let (liqSquare, vXtReserve, vFtReserve) ←
      calcIntervalProps netInterestFactor daysToMaturity cutLiqSquare cutOffset oriXtReserve
    let tokenAmtOut := sub vXtReserve (div liqSquare (add vFtReserve debtTokenAmtIn))
    requireError (tokenAmtOut <= oriXtReserve) InsufficientLiquidity()
    return (tokenAmtOut, debtTokenAmtIn)

  /-
    Mirrors `TermMaxCurve.buyXt` (TermMaxCurve.sol:177–186):
      (negDeltaXt, deltaFt) =
          cutsReverseIter(netInterestFactor, daysToMaturity, cuts,
                          oriXtReserve, inputAmount, buyXtStep);
    The `buyXtStep` function pointer is specialized into `cutsReverseIter`
    above per gap G2.
  -/
  function buyXtCurve
      (netInterestFactor : Uint256, daysToMaturity : Uint256,
       cutLiqSquare : Uint256, cutOffset : Int256,
       oriXtReserve : Uint256, debtTokenAmtIn : Uint256) :
      Tuple [Uint256, Uint256] := do
    let (negDeltaXt, deltaFt) ←
      cutsReverseIter netInterestFactor daysToMaturity cutLiqSquare cutOffset
        oriXtReserve debtTokenAmtIn
    return (negDeltaXt, deltaFt)

  /-
    Mirrors `_buyXtStep` (TermMaxOrderV2.sol:1223–1238):

      FeeConfig memory feeConfig = config.feeConfig;
      CurveCut[] memory cuts = config.curveCuts.lendCurveCuts;
      uint256 nif = Constants.DECIMAL_BASE + uint256(feeConfig.borrowTakerFeeRatio);
      (tokenAmtOut, deltaFt) = TermMaxCurve.buyXt(nif, daysToMaturity,
                                                   cuts, oriXtReserve, debtTokenAmtIn);
      feeAmt = deltaFt
             - (deltaFt * (Constants.DECIMAL_BASE - uint256(feeConfig.lendMakerFeeRatio))) / nif;
      deltaFt -= feeAmt;
      deltaXt = tokenAmtOut;
      isNegetiveXt = true;        // dropped: constant true on this path

    `config.feeConfig.{borrowTakerFeeRatio, lendMakerFeeRatio}` are passed
    as scalar parameters (gap G5); `cuts` is replaced by `(cutLiqSquare,
    cutOffset)` (gap G1).
  -/
  function buyXtStep
      (daysToMaturity : Uint256, oriXtReserve : Uint256, debtTokenAmtIn : Uint256,
       borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutLiqSquare : Uint256, cutOffset : Int256) :
      Tuple [Uint256, Uint256, Uint256, Uint256] := do
    let nif := add 100000000 borrowTakerFeeRatio
    let (tokenAmtOut, curveDeltaFt) ←
      buyXtCurve nif daysToMaturity cutLiqSquare cutOffset oriXtReserve debtTokenAmtIn
    let feeAmt :=
      sub curveDeltaFt (div (mul curveDeltaFt (sub 100000000 lendMakerFeeRatio)) nif)
    let deltaFt := sub curveDeltaFt feeAmt
    let deltaXt := tokenAmtOut
    return (tokenAmtOut, feeAmt, deltaFt, deltaXt)

  /-
    Mirrors `_buyToken` (TermMaxOrderV2.sol:1085–1098) specialized to the
    `_buyXtStep` function-pointer argument. The storage read of
    `virtualXtReserve` happens here, exactly as in Solidity (line 1093:
    `func(_daysToMaturity(), virtualXtReserve, debtTokenAmtIn, config)`).
  -/
  function buyToken
      (daysToMaturity : Uint256, debtTokenAmtIn : Uint256, minTokenOut : Uint256,
       borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutLiqSquare : Uint256, cutOffset : Int256) :
      Tuple [Uint256, Uint256, Uint256, Uint256] := do
    let oriXtReserve ← getStorage virtualXtReserve
    let (tokenAmtOut, feeAmt, deltaFt, deltaXt) ←
      buyXtStep daysToMaturity oriXtReserve debtTokenAmtIn
        borrowTakerFeeRatio lendMakerFeeRatio cutLiqSquare cutOffset
    let netOut := add tokenAmtOut debtTokenAmtIn
    requireError (netOut >= minTokenOut) UnexpectedAmount(minTokenOut, netOut)
    return (netOut, feeAmt, deltaFt, deltaXt)

  /-
    Mirrors `_buyXt` (TermMaxOrderV2.sol:932–939). Solidity also carries an
    `onlyBorrowingIsAllowed(config)` modifier; that is access control that
    does not touch `virtualXtReserve`, so it is omitted on this slice.
  -/
  function buyXt
      (debtTokenAmtIn : Uint256, minTokenOut : Uint256,
       daysToMaturity : Uint256,
       borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutLiqSquare : Uint256, cutOffset : Int256) :
      Tuple [Uint256, Uint256, Uint256, Uint256] := do
    let (netOut, feeAmt, deltaFt, deltaXt) ←
      buyToken daysToMaturity debtTokenAmtIn minTokenOut
        borrowTakerFeeRatio lendMakerFeeRatio cutLiqSquare cutOffset
    return (netOut, feeAmt, deltaFt, deltaXt)

  /-
    Mirrors `_swapAndUpdateReserves` (TermMaxOrderV2.sol:859–884) on the
    `isNegetiveXt = true` branch (always taken on `_buyXt`):

        (netAmt, feeAmt, deltaFt, deltaXt, true) = func(...);
        uint256 newXtReserve = virtualXtReserve;
        virtualXtReserve = newXtReserve - deltaXt;
        return (netAmt, feeAmt, ...);

    The `else` branch (`newXtReserve += deltaXt`, `maxXtReserve` check,
    `revert XtReserveTooHigh()`) is unreachable on `_buyXt` so it is
    omitted. The constant `isNegetiveXt = true` flag is dropped. The
    `int256` return components `deltaFt.toInt256()` / `-deltaXt.toInt256()`
    are propagated as the same word values (the spec only constrains the
    `virtualXtReserve` write).
  -/
  function swapAndUpdateReserves
      (debtTokenAmtIn : Uint256, minTokenOut : Uint256,
       daysToMaturity : Uint256,
       borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutLiqSquare : Uint256, cutOffset : Int256) :
      Tuple [Uint256, Uint256, Uint256, Uint256] := do
    let (netAmt, feeAmt, deltaFt, deltaXt) ←
      buyXt debtTokenAmtIn minTokenOut daysToMaturity
        borrowTakerFeeRatio lendMakerFeeRatio cutLiqSquare cutOffset
    let newXtReserve ← getStorage virtualXtReserve
    setStorage virtualXtReserve (sub newXtReserve deltaXt)
    return (netAmt, feeAmt, deltaFt, deltaXt)

  /-
    Mirrors the `tokenIn == _debtToken && tokenOut == _xt` branch of
    `swapExactTokenToToken` (TermMaxOrderV2.sol:666–721).

    Omitted (declared, none touch `virtualXtReserve`):
    - `if (block.timestamp > deadline) revert DeadlineExpired();`
    - `if (tokenIn == tokenOut) revert CantSwapSameToken();`
    - the other 7 token-pair branches and `revert CantNotSwapToken(...)`
    - `_orderConfig` / `_getMarketConfigAndCache()` reads (replaced by
      direct `borrowTakerFeeRatio` / `lendMakerFeeRatio` / `daysToMaturity`
      parameters per gap G5)
    - `tokenIn.safeTransferFrom`, `swapTrigger.afterSwap`, `_rebalance`,
      `tokenOut.safeTransfer`, `emit SwapExactTokenToToken(...)`
      (all post-write; reentry blocked by `nonreentrant` below)

    The `nonreentrant(nonReentrancyLock)` modifier mirrors Solidity's
    `nonReentrant` from OpenZeppelin's `ReentrancyGuard` (which gates the
    function on a single uint256 storage slot).

    The Solidity `if (tokenAmtIn != 0) { ... }` no-op-on-zero pattern is
    represented by the model precondition `debtTokenAmtIn != 0`; on
    successful execution this is always satisfied.
  -/
  function nonreentrant(nonReentrancyLock) swapDebtTokenToXtExactInSingleSegment
      (debtTokenAmtIn : Uint256, minTokenOut : Uint256,
       daysToMaturity : Uint256,
       borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutLiqSquare : Uint256, cutOffset : Int256) : Uint256 := do
    let (netTokenOut, _feeAmt, _deltaFt, _deltaXt) ←
      swapAndUpdateReserves debtTokenAmtIn minTokenOut daysToMaturity
        borrowTakerFeeRatio lendMakerFeeRatio cutLiqSquare cutOffset
    return netTokenOut

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
