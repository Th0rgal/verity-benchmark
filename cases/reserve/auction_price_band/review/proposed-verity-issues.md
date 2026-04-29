# Proposed Verity issues from this case

These are proposals only. They will not be filed without explicit user
confirmation during Phase 2e (human review).

## 1. Stdlib axioms for fixed-point `ln` / `exp` (PRBMath equivalents)

**What construct could not be expressed.**
Reserve's auction price decay uses PRBMath's fixed-point natural exp /
ln, exposed via `MathLib.exp` and `MathLib.ln` in
`reserve-protocol/dtfs@14f75d1:contracts/utils/MathLib.sol`. These wrap
`@prb/math/src/SD59x18.sol::exp` and `@prb/math/src/UD60x18.sol::ln`,
which approximate `e^x` and `ln(x)` over fixed-point inputs via
truncated polynomial / `2^x` decomposition.

`Verity.Stdlib.Math` (`Verity/Stdlib/Math.lean`) provides only `safeAdd`,
`safeSub`, `safeMul`, `safeDiv`, `mulDivDown`, `mulDivUp`, `wMulDown`,
`wDivUp`, and `ceilDiv`. There is no `ln` or fixed-point `exp`. The
EVM `EXP` opcode (modular `a^b`, available as a Verity builtin per
`docs/ARITHMETIC_PROFILE.md:43`) is unrelated semantically.

The Cork case (`Benchmark/Cases/Cork/PoolSolvency/Contract.lean:50`)
flagged the analogous gap for `pow`:

> "parameters (refScaleUp, colScaleUp) instead of runtime exponentiation.
>  Why: Verity has no Uint256 pow function. (Verity gap)"

and sidestepped it by parameterising. We cannot sidestep `exp` here:
the band invariant *is about* the exponential decay's clamp.

**What we did instead (workaround in this model).**
In `Benchmark/Cases/Reserve/AuctionPriceBand/Contract.lean` we declare:

```lean
axiom exp : Int256 → Uint256
axiom ln  : Uint256 → Uint256

axiom exp_nonpositive_le_d18 (x : Int256) :
    Verity.EVM.Int256.toInt x ≤ 0 → exp x ≤ D18
```

The single algebraic axiom `exp_nonpositive_le_d18` is sufficient for
the upper-bound proof of the band invariant. `ln` is opaque-only;
no algebraic property of `ln` is required by the proof.

**Proposed Verity improvement.**
Add `Verity.Stdlib.Math.exp : Int256 → Uint256` and
`Verity.Stdlib.Math.ln : Uint256 → Uint256` as opaque declarations,
together with the algebraic-property axiom ledger required for typical
Reserve / Compound III / Aave-V3 rate-strategy proofs:

- `exp_zero : exp 0 = D18`
- `exp_nonpositive_le_d18 : Int256.toInt x ≤ 0 → exp x ≤ D18`
- `exp_nonneg_ge_d18 : 0 ≤ Int256.toInt x → D18 ≤ exp x`
- `exp_monotone : Int256.toInt x ≤ Int256.toInt y → exp x ≤ exp y`
- `ln_d18 : ln D18 = 0`
- `ln_monotone : x ≤ y → ln x ≤ ln y` (with appropriate domain bound)

These cover the band, monotonicity, and equilibrium-fixed-point shapes
that arise across protocols. Each axiom is justified by the sign and
shape guarantees of PRBMath's implementation, independent of the
specific bit-faithful coefficients in the Taylor series.

**Severity.** Nice-to-have, proof-gap-only. The current case proves the
band invariant under the local axioms; upstreaming would unblock any
case touching PRBMath without each case re-declaring its own opaque
shims.

**Existing coverage check.**
None found. Searched:
- `Verity/Stdlib/Math.lean` — only basic arithmetic helpers.
- `docs/ARITHMETIC_PROFILE.md:43` — lists EVM `exp` opcode (modular
  exponentiation), not the fixed-point natural exponential.
- `docs/ROADMAP.md`, `docs/LANGUAGE_DESIGN_AXES.md`,
  `docs/PARITY_PACKS.md` — no PRBMath / fixed-point / ln / exp
  mention.
- The Cork case noted the gap for `pow` but not `exp` / `ln`.

No duplicate to comment on; this would be a new issue.

## 2. (No other gaps proposed)

Every other construct in `RebalancingLib._price` translated 1:1 into
Verity surface. Storage-mapping reads and the Solidity require gate
were folded into the pure-function model using established Lido
VaulthubLocked / NexusMutual RammSpotPrice patterns (not Verity gaps).
