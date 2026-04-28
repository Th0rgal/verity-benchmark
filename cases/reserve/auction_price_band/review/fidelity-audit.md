# Solidity-Mirror Fidelity Audit (Phase 2e Part A)

Run automatically by an independent agent against `Contract.lean` and `Specs.lean`.

| # | Check | Result |
|---|---|---|
| 1 | Identifier inventory | **PASS** |
| 2 | Struct shape (`PriceRange`) | **PASS** |
| 3 | Control-flow shape | **PASS** |
| 4 | Require-gate presence (8 conjuncts) | **PASS** |
| 5 | Inline vs. extracted helpers | **PASS** |

**Overall verdict: Score 100% — ready.**

## Check 1 — Identifier inventory

Solidity locals / fields / constants in `_price`:
`sellPrices`, `buyPrices`, `startPrice`, `endPrice`, `elapsed`, `auctionLength`,
`k`, `p`, `low`, `high`, `D18`, `D27`, `MathLib.exp`, `MathLib.ln`, `PriceRange`,
`block.timestamp`, `auction.startTime`, `auction.endTime`, `auction.rebalanceNonce`,
`rebalance.nonce`, `sellToken`, `buyToken`, `inRebalance`, `Folio__AuctionNotOngoing`.

All appear verbatim in `Contract.lean`. Justified deviations:
- `MathLib.exp` → `MathLib_exp` (Lean disallows `.` in axiom names). DEVIATES-OK.
- `Folio__AuctionNotOngoing` folded into the `auctionOngoing : Prop` predicate.
  DEVIATES-OK — pure Lean cannot revert.
- `inRebalance` rendered as `sellInRebalance`/`buyInRebalance : Uint256`
  (bool-as-Uint256). DEVIATES-OK.

## Check 2 — Struct shape

`IFolio.PriceRange { uint256 low; uint256 high; }` (`IFolio.sol:171-174`)
↔ `structure PriceRange where low : Uint256; high : Uint256`. Same name,
same fields, same order.

## Check 3 — Control-flow shape

All ten Solidity constructs (require gate, `startPrice` decl, start-time
early-return, `endPrice` decl, end-time early-return, `elapsed`,
`auctionLength`, `k`, `p` assignment, clamp) appear in identical relative
order in the Lean `_price` body.

## Check 4 — Require gate (8 conjuncts)

Each Solidity conjunct in `RebalancingLib.sol:438-445` has a matching Lean
conjunct in `auctionOngoing`. Same order, same operators (modulo
`<=` ↔ `≤` syntax).

## Check 5 — Top-level `def`s

- `D18`, `D27` mirror `Constants.sol` ✓
- `PriceRange` mirrors `IFolio.sol` ✓
- `MathLib_exp`, `MathLib_exp_nonpositive_le_D18`, `MathLib_ln` mirror
  `MathLib.sol` (DEVIATES-OK)
- `auctionOngoing` encodes the require gate (DEVIATES-OK)
- `_price` mirrors `RebalancingLib._price` ✓
- `InteriorSafe` bundles overflow / safety preconditions for the upper-bound
  proof (DEVIATES-OK; Solidity reverts on overflow rather than
  precondition-checking).

No unjustified extracted helpers.
