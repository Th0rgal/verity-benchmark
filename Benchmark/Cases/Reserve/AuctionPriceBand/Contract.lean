import Contracts.Common
import Verity.EVM.Int256

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Solidity-mirror translation of `RebalancingLib._price` (Reserve DTF Protocol).

  Upstream: reserve-protocol/dtfs
  Commit:   14f75d18856d587adfaff24e77e5b20dda7c7267
  File:     contracts/utils/RebalancingLib.sol
  Function: _price (lines 427-475)

  This file follows the Solidity-mirror translation convention (see the
  verity-prove-invariant skill, Phase 2b):
  - Local variable names match the Solidity verbatim
    (`startPrice`, `endPrice`, `sellPrices`, `buyPrices`, `elapsed`,
    `auctionLength`, `k`, `p`).
  - The Lean `PriceRange` structure mirrors `IFolio.PriceRange`.
  - Control flow mirrors the Solidity branch cascade via nested if-then-else,
    each guarded by an inline `-- Solidity: return X;` comment.
  - The Solidity require gate (lines 437-447) is encoded explicitly as the
    named `Prop` predicate `auctionOngoing` and consumed as a hypothesis on
    every theorem.
  - Inline Solidity expressions stay inline in Lean (no extracted helpers).
  - Constants `D18`, `D27` mirror `@utils/Constants.sol` by name and value.
  - Every divergence from a 1:1 translation carries an explicit `DEVIATES:`
    comment naming the Solidity construct and the concrete reason.

  Simplifications (each is a `DEVIATES:`-tagged divergence):

  | What was simplified                          | Why                                    |
  |----------------------------------------------|----------------------------------------|
  | Storage reads (`auction.prices[token]`,      | Verity pure helpers cannot read        |
  | `rebalance.details[token].inRebalance`,      | storage; we take the same values as    |
  | `auction.startTime`, `auction.endTime`,      | function parameters. Equivalent under  |
  | `rebalance.nonce`, `auction.rebalanceNonce`) | the trust assumption that callers      |
  | are passed as parameters of `_price`.        | (`bid`, `getBid`) supply the values    |
  |                                              | currently in storage. (Same posture as |
  |                                              | NexusMutual `RammSpotPrice`.)          |
  |----------------------------------------------|----------------------------------------|
  | The 8-clause `require(...)` at L437-447 is   | Pure functions cannot revert. The      |
  | encoded as `auctionOngoing : Prop` and       | gate's positive content is recovered   |
  | consumed as a hypothesis on every theorem.   | as a precondition.                     |
  |----------------------------------------------|----------------------------------------|
  | `MathLib.exp` and `MathLib.ln` (PRBMath      | Verity stdlib has no fixed-point       |
  | UD60x18 / SD59x18 wrappers) are declared as  | natural exp/ln. Proposed Verity issue: |
  | opaque axioms with one algebraic axiom       | "Stdlib axioms for fixed-point ln/exp  |
  | (`MathLib_exp_nonpositive_le_D18`).          | (PRBMath equivalents)".                |

  Trust assumptions:
  - `block.timestamp` is passed as a `block_timestamp` parameter.
  - PRBMath's bit-faithful Taylor-series implementation of exp/ln is treated
    as an opaque algebraic interface; only the property
    `exp x ≤ D18 for x ≤ 0` is consumed by the proofs.
-/

/-- Reserve fixed-point scale: 18 decimals.
    Mirrors `D18` at `contracts/utils/Constants.sol:25`. -/
def D18 : Uint256 := 1000000000000000000

/-- Reserve fixed-point scale: 27 decimals.
    Mirrors `D27` at `contracts/utils/Constants.sol:26`. -/
def D27 : Uint256 := 1000000000000000000000000000

/-- Mirrors `IFolio.PriceRange { uint256 low; uint256 high; }` at
    `contracts/interfaces/IFolio.sol:171-174`. -/
structure PriceRange where
  low : Uint256
  high : Uint256

/-- Opaque model of `MathLib.exp` at `contracts/utils/MathLib.sol:32-34`,
    PRBMath's `SD59x18.exp` returning a D18 fixed-point value.

    DEVIATES: Verity stdlib has no fixed-point natural exponential. We
    declare it opaque and expose only the algebraic property the band
    invariant proof needs (`MathLib_exp_nonpositive_le_D18`). -/
axiom MathLib_exp : Int256 → Uint256

/-- For non-positive inputs, `MathLib_exp` is at most `D18`. PRBMath rounds
    intermediate values, but rounding never pushes the output of `exp` strictly
    above `D18` for non-positive inputs (`exp(0) = D18`, `exp` is monotone). -/
axiom MathLib_exp_nonpositive_le_D18 (x : Int256) :
    Verity.EVM.Int256.toInt x ≤ 0 → MathLib_exp x ≤ D18

/-- Opaque model of `MathLib.ln` at `contracts/utils/MathLib.sol:26-28`,
    PRBMath's `UD60x18.ln`. Used only inside `_price` to compute the decay
    rate `k`; the proofs treat the value as fully opaque.

    DEVIATES: Verity stdlib has no fixed-point natural logarithm. -/
axiom MathLib_ln : Uint256 → Uint256

/--
The Solidity require clause at `RebalancingLib.sol:437-447`, encoded
byte-for-byte as a named precondition. Every theorem about `_price` consumes
this as a hypothesis to model the gate the function would have asserted.

DEVIATES: Solidity `require(cond, error)` aborts on falsity; pure Lean has no
abort, so the gate is encoded as a `Prop` and theorems take it as a hypothesis.
The conjuncts mirror the Solidity exactly:
  auction.rebalanceNonce == rebalance.nonce
  && sellToken != buyToken
  && rebalance.details[address(sellToken)].inRebalance
  && rebalance.details[address(buyToken)].inRebalance
  && sellPrices.low != 0
  && buyPrices.low != 0
  && block.timestamp >= auction.startTime
  && block.timestamp <= auction.endTime
-/
def auctionOngoing
    (auction_rebalanceNonce rebalance_nonce : Uint256)
    (sellToken buyToken : Uint256)               -- DEVIATES: Address modeled as Uint256 (ABI-equivalent)
    (sellInRebalance buyInRebalance : Uint256)   -- DEVIATES: Solidity bool modeled as Uint256 (1 = true, 0 = false)
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256) : Prop :=
  auction_rebalanceNonce = rebalance_nonce ∧
  sellToken ≠ buyToken ∧
  sellInRebalance ≠ 0 ∧ buyInRebalance ≠ 0 ∧
  sellPrices.low ≠ 0 ∧ buyPrices.low ≠ 0 ∧
  auction_startTime ≤ block_timestamp ∧ block_timestamp ≤ auction_endTime

/--
Pure model of `RebalancingLib._price` at `contracts/utils/RebalancingLib.sol:427-475`.

The body mirrors the Solidity line-by-line. Each `-- Solidity:` comment
shows the source line being translated; each `DEVIATES:` comment names a
divergence and its concrete reason.
-/
noncomputable def _price
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime : Uint256)
    (block_timestamp : Uint256) : Uint256 :=
  -- Solidity (L450):
  --   uint256 startPrice = Math.mulDiv(sellPrices.high, D27, buyPrices.low, Math.Rounding.Ceil);
  let startPrice := mulDivUp sellPrices.high D27 buyPrices.low
  -- Solidity (L451-453): if (block.timestamp == auction.startTime) return startPrice;
  if block_timestamp == auction_startTime then
    startPrice
  else
    -- Solidity (L456):
    --   uint256 endPrice = Math.mulDiv(sellPrices.low, D27, buyPrices.high, Math.Rounding.Ceil);
    let endPrice := mulDivUp sellPrices.low D27 buyPrices.high
    -- Solidity (L457-459): if (block.timestamp == auction.endTime) return endPrice;
    if block_timestamp == auction_endTime then
      endPrice
    else
      -- Solidity (L462): uint256 elapsed = block.timestamp - auction.startTime;
      let elapsed := sub block_timestamp auction_startTime
      -- Solidity (L463): uint256 auctionLength = auction.endTime - auction.startTime;
      let auctionLength := sub auction_endTime auction_startTime
      -- Solidity (L467):
      --   uint256 k = MathLib.ln(Math.mulDiv(startPrice, D18, endPrice)) / auctionLength;
      let k := div (MathLib_ln (mulDivDown startPrice D18 endPrice)) auctionLength
      -- Solidity (L471):
      --   p = Math.mulDiv(startPrice, MathLib.exp(-1 * int256(k * elapsed)), D18, Math.Rounding.Ceil);
      -- DEVIATES (subtle, not semantic): the cast `int256(k * elapsed)` is
      -- bit-preserving in Solidity; in Lean we model it via
      -- `Int256.ofUint256 (mul k elapsed)` and `Int256.neg` for the unary `-`.
      -- Equivalent under the precondition that `(k * elapsed).val ≤ MAX_INT256`,
      -- which is part of the interior-branch safety hypothesis bundled
      -- in `InteriorSafe` below.
      let p := mulDivUp startPrice
                 (MathLib_exp (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 (mul k elapsed))))
                 D18
      -- Solidity (L472-474): if (p < endPrice) p = endPrice;
      if p < endPrice then endPrice else p

/--
Bundled overflow / fixed-point safety hypotheses required for the
upper-bound proof on the interior decay branch.

These are conservative bounds that hold for any auction the AUCTION_LAUNCHER
could realistically open (UoA prices in the `1e27`-`1e30` range). The case
scopes itself to launcher-published bands realistic enough to fit; pushing
this bound to cover all `Constants.sol` extremes (`MAX_TOKEN_PRICE = 1e45`)
is future work.
-/
structure InteriorSafe
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256) : Prop where
  /-- The `mul k elapsed` at L471 fits inside the positive Int256 half-range,
      so the `int256(...)` cast does not flip its sign and `Int256.neg` produces
      a non-positive Int256. -/
  hKElapsedFitsInt :
      let startPrice := mulDivUp sellPrices.high D27 buyPrices.low
      let endPrice := mulDivUp sellPrices.low D27 buyPrices.high
      let auctionLength := sub auction_endTime auction_startTime
      let elapsed := sub block_timestamp auction_startTime
      let k := div (MathLib_ln (mulDivDown startPrice D18 endPrice)) auctionLength
      (mul k elapsed).val ≤ Verity.EVM.MAX_INT256.toNat
  /-- The Uint256 multiplication inside `mulDivUp startPrice exp(...) D18`
      at L471 does not overflow. With `MathLib_exp(...) ≤ D18`, this reduces
      to `startPrice * D18 + D18 - 1 < 2^256`, i.e. `startPrice < ~1.16e59`. -/
  hMulNoOverflow :
      let startPrice := mulDivUp sellPrices.high D27 buyPrices.low
      startPrice.val * D18.val + D18.val - 1 < Verity.Core.Uint256.modulus

end Benchmark.Cases.Reserve.AuctionPriceBand
