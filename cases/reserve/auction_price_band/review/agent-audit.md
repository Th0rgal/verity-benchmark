# Independent agent audit — Phase 2e Part A

A fresh agent reviewed the model, specs, and proofs without context
from the modeling session. Findings:

## Verity gap legitimacy
- CONFIRMED. `Verity.Stdlib.Math` only exposes basic helpers; no `exp`/`ln`.
  EVM `EXP` opcode (modular `a^b`) is unrelated.
- CONFIRMED. No prior art in roadmap, parity packs, or design axes.
- CONFIRMED. The proposed Verity issue is not a duplicate.

## Semantics preserved
- CONFIRMED. Boundary checks, mulDivUp ↔ ceil-mulDiv, mulDivDown ↔ floor-mulDiv,
  clamp `if p < eP then eP else p`.
- FLAGGED (subtle). `Int256.ofUint256 ∘ Int256.neg` is bit-faithful to
  `int256(uint256)` then unary `-`. The semantics matches Solidity *under*
  the hypothesis `hKElapsedFitsInt`. A one-line comment was added near the
  cast to make this explicit.

## Translation closeness
- All choices justified (storage as parameters, require gate as hypothesis,
  exp/ln axiomatised).
- Minor note: `noncomputable def` rather than `verity_contract` — matches
  NexusMutual `RammSpotPrice` precedent for pure helpers.

## Spec faithfulness
- CONFIRMED. All four primary specs encode real claims about `price`'s
  return value; none are vacuous. Together they capture the band invariant
  exactly.

## Hypotheses on theorems
- CONFIRMED. `hBand` is genuinely required on the `startTime` branch.
- CONFIRMED. `hStartNeEnd` is needed to exclude the atomic-swap edge.
- FLAGGED. `InteriorSafe.hMulNoOverflow` docstring was over-optimistic:
  it does not hold at the theoretical `MAX_TOKEN_PRICE = 1e45` extreme.
  Docstring updated to clarify the bound (`startPrice < ~1.16e59`) and
  scope the case to realistic launcher-published bands.

## Overall recommendation
**Ready for human review.** Two minor doc fixes were applied. No
fundamental issue. Two `sorry`s remain in `Proofs.lean` and are flagged
as Phase 3 proving targets.
