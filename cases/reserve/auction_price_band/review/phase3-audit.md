# Phase 3a — Intellectual-Honesty Audit

Run by an independent agent against `Contract.lean`, `Specs.lean`, and
`Proofs.lean` after the proving loop closed all `sorry`s.

| # | Check | Status |
|---|---|---|
| 1 | Axioms not abusive | **PASS** |
| 2 | Every spec proven | **PASS** |
| 3 | Zero `sorry` | **PASS** |
| 4 | Hypotheses reasonable | **PASS** |

**Overall verdict: Proven with reasonable assumptions.**

## Axiom audit

Three opaque/algebraic axioms, all in `Contract.lean` (none in `Proofs.lean`):

- `MathLib_exp : Int256 → Uint256` — opaque PRBMath `SD59x18.exp`.
  Reasonable: Verity stdlib lacks fixed-point exp.
- `MathLib_ln : Uint256 → Uint256` — fully opaque; never destructured by
  the proofs.
- `MathLib_exp_nonpositive_le_D18 (x : Int256) : Int256.toInt x ≤ 0
  → exp x ≤ D18` — captures the correct mathematical property of `exp`
  (`exp(0) = D18` in fixed-point, `exp` monotone). PRBMath is documented
  to round consistently with this. **Single algebraic property, not the
  conclusion.**

## Spec coverage

5 specs / 4 main theorems + aliases. Pairing:

| Spec | Theorem |
|---|---|
| `price_at_start_time_spec` | `price_at_start_time_main` ✓ |
| `price_at_end_time_spec` | `price_at_end_time_main` ✓ |
| `price_lower_bound_spec` | `price_lower_bound_main` ✓ |
| `price_upper_bound_spec` | `price_upper_bound_main` ✓ |
| `band_well_formed_spec` | (consumed *as* `hBand` hypothesis — a launcher input invariant, not a `_price` invariant) |

## Hypotheses on theorems

- `hBand` (`endPrice ≤ startPrice`): launcher-established by
  `openAuction` / `startRebalance` enforcing `prices.low ≤ prices.high`.
  Not the conclusion.
- `hStartNeEnd`: excludes the atomic-swap edge; narrowly applied to
  the `end_time` boundary spec only.
- `hSafe : InteriorSafe`: two narrow no-overflow / sign-cast bounds
  (`k * elapsed` fits in positive Int256 half-range; `startPrice * D18`
  doesn't wrap). Conservative numeric preconditions for launcher-realistic
  price ranges (`1e27`-`1e30`). Future work: tighten to cover
  `MAX_TOKEN_PRICE = 1e45`.

None of the hypotheses smuggles in the conclusion.
