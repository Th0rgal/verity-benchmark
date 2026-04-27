# Delegated Model-And-Prove Prompt

Use this when the user wants another agent to do **both**:

- the Verity modeling / benchmark scaffold
- the proof

Replace all placeholders.

---

**Task: Model and prove `<theorem_name>` for `<protocol>` in the Verity benchmark**

Workspace:

- `<absolute path>`

Pinned upstream source of truth:

- repo: `<repo url>`
- commit/tag: `<commit or tag>`
- files in scope:
  - `<file 1>`
  - `<file 2>`
  - `<file 3>`

Approved invariant:

- `<approved invariant>`

## Modeling bar

Preserve **semantics always**.

Subject to that, preserve the Solidity source shape as closely as possible:

- function boundaries
- helper names
- branch structure
- slot comments / layout intent
- packed-write intent
- external-call boundaries

Do **not** jump straight to a high-level abstraction if a near line-by-line Verity
translation is available.

If you must simplify or rewrite, document each item explicitly in the `Contract.lean`
simplifications block and classify it as:

1. no Verity issue, just an equivalent rewrite
2. proof-coverage gap only
3. Verity ergonomics / feature gap
4. hard blocker

## Verity context to verify before simplifying

Before you claim a limitation, check:

1. the local package at `.lake/packages/verity/`
2. any repo-local or user-provided Verity fork
3. `https://www.veritylang.com/`

Important distinction:

- "cannot express" is different from "can express but proof coverage is incomplete"

## Files to read first

- `Benchmark/Cases/<Project>/<Case>/Contract.lean` if it already exists
- `Benchmark/Cases/<Project>/<Case>/Specs.lean` if it already exists
- sibling benchmark cases for style:
  - `Benchmark/Cases/Safe/OwnerManagerReach/`
  - `Benchmark/Cases/Lido/VaulthubLocked/`
  - `Benchmark/Cases/Zama/ERC7984ConfidentialToken/`
- the upstream Solidity files listed above

## Required benchmark layout

Create or update:

```text
Benchmark/Cases/<Project>/<Case>/
├── Contract.lean
├── Specs.lean
├── Proofs.lean
└── Compile.lean

Benchmark/Generated/<Project>/<Case>/Tasks/
└── <TheoremName>.lean   ← placeholder only, body stays `exact ?_`

cases/<project>/<case>/
├── case.yaml
├── tasks/<theorem_name>.yaml
└── verity/{Contract,Specs,Compile}.lean
```

If needed, also update:

```text
families/<family>/
└── implementations/<impl>/implementation.yaml
```

## Contract.lean requirements

- Keep the source mapping obvious.
- Put a real simplifications block at the top:
  - what was simplified
  - why
  - whether this is a Verity limitation, proof-gap-only issue, or deliberate scope cut
- If you rewrite packed storage / assembly into higher-level Verity fields, retain the
  original slot / bit-layout intent in comments or helper definitions.

## Specs.lean requirements

State the target property minimally and clearly.

The theorem should match the approved invariant exactly enough to be meaningful of the
real contract, but not be inflated into a whole-system temporal claim unless the source
actually requires that.

## Build requirements before proof

Run:

```bash
cd <absolute path>
lake build Benchmark.Cases.<Project>.<Case>.Contract
lake build Benchmark.Cases.<Project>.<Case>.Specs
lake build
```

Only proceed to proof after those are green.

## Persistence rule

Do not stop until one of these terminal conditions holds:

1. **PROOF**: `lake build Benchmark.Cases.<Project>.<Case>.Proofs` succeeds and there
   is no `sorry`
2. **COUNTER-EXAMPLE**: you have a concrete `ContractState` + inputs that satisfy the
   hypotheses and falsify the conclusion
3. **AXIOM**: you add an `axiom` to `Proofs.lean` with a doc-comment explaining
   exactly what is assumed, whether it is true of the real contract, and why it
   could not be discharged mechanically

Do not stop at "I got stuck".

## Output requirements

When done, report:

1. files added / edited
2. exact simplifications used
3. build commands run
4. whether the result is PROOF / COUNTER-EXAMPLE / AXIOM
5. which hypotheses the final proof actually used
6. what the result guarantees about the real contract and what it does not
