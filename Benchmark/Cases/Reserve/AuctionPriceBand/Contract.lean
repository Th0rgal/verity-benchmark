import Contracts.Common
import Verity.EVM.Int256

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Focused Verity slice of Reserve DTF Protocol's auction price computation.

  Upstream: reserve-protocol/dtfs
  Commit:   14f75d18856d587adfaff24e77e5b20dda7c7267
  File:     contracts/utils/RebalancingLib.sol
  Function: _price (lines 427-475)

  The real `_price` returns the per-pair auction price as the protocol
  decays it from a worst-for-bidder `startPrice` to a best-for-bidder
  `endPrice` over the auction window. The interior of the window uses an
  exponential decay `p = startPrice * exp(-k * elapsed) / D18`, with an
  explicit clamp at `endPrice`.

  This benchmark targets the *band invariant*:
      endPrice ≤ price ≤ startPrice
  for every valid timestamp in [startTime, endTime].

  Simplifications (each line is a deviation from a verbatim translation):

  | What was simplified                          | Why                                    |
  |----------------------------------------------|----------------------------------------|
  | Pure Lean function `price` instead of a      | The invariant is about the returned    |
  | `verity_contract` reading from storage       | value; storage layout is incidental.   |
  | mappings `auction.prices[token]` and         | Same posture as NexusMutual            |
  | `rebalance.details[token].inRebalance`.      | RammSpotPrice (pure helper).           |
  |----------------------------------------------|----------------------------------------|
  | The require gate (auction.rebalanceNonce ==  | A pure function cannot revert. The     |
  | rebalance.nonce, sellPrices.low ≠ 0,         | gate's positive content is encoded as  |
  | currentTime ∈ [startTime, endTime], etc.) is | an `hAuction` hypothesis on each       |
  | NOT modeled inside `price`.                  | theorem.                               |
  |----------------------------------------------|----------------------------------------|
  | `MathLib.ln` and `MathLib.exp` (PRBMath      | Verity stdlib has no fixed-point       |
  | UD60x18 / SD59x18 implementations) are       | ln/exp. We declare them as opaque      |
  | declared as opaque axioms, with one          | axioms with a single algebraic axiom   |
  | algebraic axiom (`exp_nonpositive_le_d18`)   | (`exp x ≤ D18` for `x ≤ 0`) — the      |
  | sufficient for the upper-bound proof.        | only property the band invariant       |
  |                                              | needs. See proposed Verity issue:      |
  |                                              | "Stdlib axioms for fixed-point ln/exp" |
  |----------------------------------------------|----------------------------------------|
  | `Math.mulDiv(_, _, _, Math.Rounding.Ceil)`   | `mulDivUp` is the Verity stdlib direct |
  | becomes `mulDivUp` (overflow-aware ceil-div  | port of the same EVM idiom; semantics  |
  | as in OpenZeppelin `Math256.mulDiv`).        | match for the input ranges of interest.|

  Trust assumptions:
  - The auction prerequisites enforced by the require at lines 437-447 of
    the Solidity (auction is OPEN, both tokens are in rebalance, prices
    are nonzero) are taken as preconditions on the pure function. They are
    enforced by callers (`bid`, `getBid`) before reaching `_price`.
  - `endPrice ≤ startPrice` is taken as a precondition (`hBand`). It is
    enforced by `openAuction` / `startRebalance` via the input-validation
    requires that establish `sellLow ≤ sellHigh` and `buyLow ≤ buyHigh`.
    A separate lemma `band_well_formed` proves this falls out of the
    component bounds and saves the caller from carrying `hBand` directly.
-/

/-- Reserve fixed-point scale: 18 decimals. -/
def D18 : Uint256 := 1000000000000000000

/-- Reserve fixed-point scale: 27 decimals. Used for `D27{buyTok/sellTok}` price quotes. -/
def D27 : Uint256 := 1000000000000000000000000000

/--
  Opaque model of PRBMath's `SD59x18.exp`, exposed by Reserve as
  `MathLib.exp(int256)`. Returns a `D18` fixed-point value.

  No constructive content — algebraic properties are exposed via the
  named axioms below. See proposed Verity issue:
  "Stdlib axioms for fixed-point ln/exp (PRBMath equivalents)".
-/
axiom exp : Int256 → Uint256

/--
  For non-positive inputs `x`, `exp x ≤ D18`. This captures the unique
  property of the natural exponential we rely on: the value never exceeds
  one in fixed-point form when the exponent is at most zero.

  PRBMath rounds intermediate values, but rounding never pushes the
  output of `exp` strictly above `D18` for non-positive inputs (PRBMath
  implements exp via `2^x` with monotone interpolation; at `x = 0` the
  output is exactly `D18`).
-/
axiom exp_nonpositive_le_d18 (x : Int256) :
    Verity.EVM.Int256.toInt x ≤ 0 → exp x ≤ D18

/--
  Opaque model of PRBMath's `UD60x18.ln`, exposed by Reserve as
  `MathLib.ln(uint256)`. Used only inside `price` to compute the decay
  rate `k`. No algebraic property of `ln` is required for the band
  invariant; the variable is opaque to the proofs.
-/
axiom ln : Uint256 → Uint256

/--
  `startPrice` matches the Solidity expression
      Math.mulDiv(sellPrices.high, D27, buyPrices.low, Math.Rounding.Ceil)
  at line 450 of RebalancingLib.sol.
-/
def startPrice (sellHigh buyLow : Uint256) : Uint256 :=
  mulDivUp sellHigh D27 buyLow

/--
  `endPrice` matches the Solidity expression
      Math.mulDiv(sellPrices.low, D27, buyPrices.high, Math.Rounding.Ceil)
  at line 456 of RebalancingLib.sol.
-/
def endPrice (sellLow buyHigh : Uint256) : Uint256 :=
  mulDivUp sellLow D27 buyHigh

/--
  Pure model of `RebalancingLib._price` (RebalancingLib.sol:427-475).

  Branch-by-branch correspondence to the Solidity source:

  | Solidity (RebalancingLib.sol)                                     | Lean                                     |
  |-------------------------------------------------------------------|------------------------------------------|
  | `if (block.timestamp == auction.startTime) return startPrice;`    | `if currentTime == startTime then sP`    |
  | `if (block.timestamp == auction.endTime) return endPrice;`        | `if currentTime == endTime then eP`      |
  | `uint256 elapsed = block.timestamp - auction.startTime;`          | `let elapsed := sub currentTime startTime` |
  | `uint256 auctionLength = auction.endTime - auction.startTime;`    | `let auctionLength := sub endTime startTime` |
  | `uint256 k = MathLib.ln(Math.mulDiv(startPrice, D18, endPrice)) / auctionLength;` | `let k := div (ln (mulDivDown sP D18 eP)) auctionLength` |
  | `p = Math.mulDiv(startPrice, MathLib.exp(-1 * int256(k * elapsed)), D18, Math.Rounding.Ceil);` | `let p := mulDivUp sP (exp negKE) D18` |
  | `if (p < endPrice) p = endPrice;`                                 | `if lt p eP then eP else p`              |
-/
noncomputable def price
    (sellLow sellHigh buyLow buyHigh : Uint256)
    (startTime endTime currentTime : Uint256) : Uint256 :=
  let sP := startPrice sellHigh buyLow
  let eP := endPrice sellLow buyHigh
  if currentTime == startTime then sP
  else if currentTime == endTime then eP
  else
    let elapsed := sub currentTime startTime
    let auctionLength := sub endTime startTime
    let k := div (ln (mulDivDown sP D18 eP)) auctionLength
    let kElapsed := mul k elapsed
    -- `Int256.ofUint256` is the bit-preserving cast that mirrors Solidity's
    -- `int256(uint256)` reinterpretation: the high bit becomes the sign bit.
    -- `Int256.neg` is two's-complement negation, matching unary `-` in Solidity.
    -- Together they faithfully model `int256(k * elapsed)` then `-1 *`.
    let negKE := Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 kElapsed)
    let p := mulDivUp sP (exp negKE) D18
    if p < eP then eP else p

/--
  Bundled overflow / fixed-point safety hypotheses required for the
  upper-bound proof on the interior decay branch.

  These are conservative bounds that hold for any auction the AUCTION_LAUNCHER
  could realistically open under the constants in `Constants.sol`
  (`MAX_TOKEN_PRICE = 1e45`, `MAX_TOKEN_PRICE_RANGE = 1e2`, etc.).
-/
structure InteriorSafe
    (sellLow sellHigh buyLow buyHigh : Uint256)
    (startTime endTime currentTime : Uint256) : Prop where
  /-- The `mul k elapsed` at line 471 fits inside the positive Int256
      half-range, so the `int256(...)` cast at line 471 does not flip
      its sign and `Int256.neg` produces a non-positive Int256. -/
  hKElapsedFitsInt :
      let sP := startPrice sellHigh buyLow
      let eP := endPrice sellLow buyHigh
      let auctionLength := sub endTime startTime
      let elapsed := sub currentTime startTime
      let k := div (ln (mulDivDown sP D18 eP)) auctionLength
      (mul k elapsed).val ≤ Verity.EVM.MAX_INT256.toNat
  /-- The Uint256 multiplication inside `mulDivUp startPrice exp(...) D18`
      at line 471 does not overflow. With `exp(...) ≤ D18`, this reduces
      to `startPrice * D18 + D18 - 1 < 2^256`, i.e. `startPrice <
      ~1.16e59`.

      For typical Reserve auctions (UoA prices in the `1e27`-`1e30` range,
      D27 fixed-point), this is met with multiple orders of magnitude of
      headroom. The launcher *could* theoretically open an auction with
      `sellHigh = MAX_TOKEN_PRICE = 1e45` and `buyLow = 1`, yielding
      `startPrice = 1e72`, which violates this bound. The case scopes
      itself to launcher-published bands realistic enough to fit; pushing
      this bound to cover all `Constants.sol` extremes is future work. -/
  hMulNoOverflow :
      let sP := startPrice sellHigh buyLow
      sP.val * D18.val + D18.val - 1 < Verity.Core.Uint256.modulus

end Benchmark.Cases.Reserve.AuctionPriceBand
