# Review Matrix

The skill requests orchestrator `batch_create_workers`, but this session exposes
Codex `spawn_agent` workers instead. Reviewer missions are spawned with
`model: gpt-5.5` and `reasoning_effort: high`, matching the required backend
model and effort as closely as the available tool surface permits.

| Phase | Reviewer | Status | Resolution |
| --- | --- | --- | --- |
| Research | Research Reviewer | fixed | Replaced `_transferFee` with `_calculateFee`; added Sourcify source evidence; stated no value-at-risk snapshot is claimed. |
| Research | Invariant Reviewer | fixed | Specs now use independent expected fee/return expressions; `swap_value_conservation` postcondition explicitly ties minted USD0 to `expectedSwapUsdQuote`; successful-call arithmetic hypotheses added. |
| Modelization | Modelization Reviewer | fixed | Added successful-call hypotheses for no-wrap arithmetic, fee/CBR bounds, nonzero quote, uint128 amount bound, and treasury collateral sufficiency; task metadata discloses these boundaries. |
| Modelization | Verity Reviewer | fixed | Verity macro limitations led to theorem-level preconditions rather than in-contract checked-arithmetic requires; targeted Contract/Specs/Proofs/Compile builds pass. |
| Modelization | Build Reviewer | fixed | Regenerated `benchmark-inventory.json` and `REPORT.md`; `validate_manifests.py` passes. |
| Proof | Proof Reviewer | fixed | `lake build Benchmark.Cases.Usual.DaoCollateral.Proofs` passes with no `sorry`/axiom in Usual files. |
| Proof | Final Red Team Reviewer | pending | pending final post-build review. |
| Article | Article Reviewer | fixed pending push | Reproduction command now checks out `usual-daocollateral-conservation`; benchmark source links resolve after branch push. |
| Article | Final Red Team Reviewer | pending | pending final post-push review. |
