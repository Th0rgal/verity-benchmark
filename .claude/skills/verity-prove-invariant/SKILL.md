---
name: verity-prove-invariant
description: >
  Four-phase workflow for adding a new Verity benchmark case: (1) research the protocol
  and confirm the invariant, (2) modelize in Verity as close to Solidity as possible
  with agent + human verification, (3) prove the invariant in a persistent loop with
  intellectual honesty checks, (4) write a case study article for lfglabs.dev.
  Trigger terms: verity prove, new benchmark case, prove invariant, formally verify,
  add verity case, verify protocol, model contract in verity, lean contract verification.
---

# Verity Prove Invariant

Add a new formal-verification case to the Verity benchmark. The workflow has four
phases, each **gated by explicit user acknowledgement** — never cross a phase boundary
silently.

---

## Phase 1 — Research, invariant alignment, and translation audit (before any code)

You will receive an entry point: a Solidity contract address, a GitHub repository, a
protocol name, or similar. Your first job is to find and read the actual Solidity source
code.

**Research the protocol first.** Use web fetches to read:
- The protocol's documentation and website
- The actual Solidity source on GitHub (raw.githubusercontent.com)
- Read enough source to identify the require checks, state variables, storage layout
  decisions, loops / queues, and external calls

Once you have done this research, output ONE text response covering all of the
following, then **stop and wait for user acknowledgement**. Do not proceed to Phase 2
until the user explicitly confirms.

1. **What the protocol does.** One-paragraph plain-English summary. Include: what it's
   for, who uses it, what's the unit of value at risk, and what function(s) the user
   is asking about.
2. **Candidate invariants.** Propose 1–3 invariants ordered from highest-value to
   least. For each, state what it prevents (e.g. "no tokens created out of thin air",
   "balance state cannot leak through revert"). Pick the minimum invariant that
   actually exercises the contract's non-trivial logic — not a tautology like "storage
   slot X is written".
3. **If the user proposed an invariant,** say explicitly whether it makes sense. If
   it's too weak (trivially true), too strong (requires modelling the whole world),
   or mis-targets the contract, say so and propose an adjustment.
4. **Translation fidelity audit.** For the exact Solidity files/functions in scope,
   identify the constructs that can be translated near line-by-line in Verity and the
   constructs that would require rewrites or trusted boundaries. For each non-trivial
   rewrite, include:
   - the exact Solidity construct / snippet / file path
   - the closest Verity surface you would use
   - the classification: no issue / proof-gap-only / Verity-gap / hard blocker
   - whether this changes syntax only, or also risks changing semantics

   To assess Verity capabilities, check in this order:
   - the current local package at `.lake/packages/verity/`
   - any repo-local or user-provided Verity fork (e.g. `.context/lfglabs-verity`)
   - the Verity documentation at [veritylang.com](https://veritylang.com)

   Distinguish clearly between "cannot express", "can express but proof story is
   incomplete", and "can express cleanly".
5. **Draft simplifications before code.** List every simplification you currently
   expect to make, or explicitly say "none yet". If a simplification is driven by
   Verity limitations, say whether:
   - there is a workaround in the current local package
   - there is a workaround in a repo-local or user-provided Verity fork
   - this should probably become a Verity issue
6. **Wait.** End with: "Confirm you're aligned on this invariant, the line-by-line
   modeling plan, and the listed simplifications / Verity gaps, and I'll start
   modelling."

---

## Phase 2 — Modelize in Verity

Only start after the user acknowledges Phase 1.

### 2a. File layout (match Safe/Lido/Zama)

```
Benchmark/Cases/<Project>/<Case>/
├── Contract.lean        ← verity_contract model
├── Specs.lean           ← spec definitions (Prop)
├── Proofs.lean          ← REFERENCE proofs (hidden from the agent)
└── Compile.lean         ← import Contract + Proofs

Benchmark/Generated/<Project>/<Case>/Tasks/
└── <TheoremName>.lean   ← AGENT-FACING placeholder; body = `exact ?_`

cases/<project>/<case>/
├── case.yaml
├── tasks/<theorem_name>.yaml    (one per theorem)
└── verity/{Contract,Specs,Compile}.lean   (re-export wrappers)

families/<family>/
├── family.yaml
└── implementations/<impl>/implementation.yaml
```

Inversion warning: the reference proof goes in `Cases/.../Proofs.lean`, NOT in the
`Generated/.../Tasks/*.lean` placeholder. The placeholder stays `exact ?_` forever.

### 2b. Write the Verity model as close to Solidity as possible

The goal is a near line-by-line translation of the Solidity source into Verity. Every
deviation from the source structure must be justified by a concrete Verity limitation.

**Translation preference order:**

1. Line-by-line Verity translation preserving function boundaries, branch structure,
   helper names, slot layout, and external-call boundaries.
2. Syntax-close rewrite that preserves semantics and keeps the source mapping obvious.
3. Narrower semantic model with explicit acknowledged simplifications — only as a last
   resort.

Do not silently jump from (1) to (3).

**If you discover a new simplification** that was not listed in Phase 1, do not stop.
Use your judgment to decide whether it makes sense, continue writing the model, but
**mention the new simplification at the end** when presenting the model to the user.

Before claiming any Verity limitation, verify it against the actual Verity surface:
- `.lake/packages/verity/` (the local package)
- any repo-local or user-provided Verity fork (e.g. `.context/lfglabs-verity`)
- the Verity documentation at [veritylang.com](https://veritylang.com)

**Write Contract.lean** with a doc-comment at the top listing every simplification in
two columns: "what was simplified" and "why (the concrete Verity limitation or semantic
reason)". Do not call something a simplification if you can model it faithfully.

**Write Specs.lean** with each property as a `def foo_spec (... : ContractState) : Prop`.
Keep specs minimal — one clear sentence of English each. Use `balanceOf`, `supply`, and
similar helpers to hide storage-slot indices from the spec surface.

**Write Generated placeholders + YAMLs** for each theorem:
- `Benchmark/Generated/<Project>/<Case>/Tasks/<Name>.lean` ending in `exact ?_`
- `cases/<project>/<case>/tasks/<name>.yaml` pointing at that file
- Matching entry in `case.yaml` selected_functions + abstraction_tags

### 2c. Proposed Verity issues

For every place where the model had to deviate from the Solidity source, produce a
section listing **proposed** Verity issues. For each:

- **What construct** could not be expressed (exact Solidity snippet + file path).
- **What you did instead** (the workaround in the model).
- **Proposed Verity improvement** — what the language/framework should support so that
  future models don't need this workaround.
- **Severity**: nice-to-have / proof-gap-only / blocks-faithful-modeling.

Group by theme (e.g. "missing DSL bind source", "packed storage", "external calls").

**Do not create issues on the Verity repository.** These are proposals only. The user
will review them in 2e and decide which ones to actually file.

### 2d. Build the scaffold

```bash
lake build Benchmark.Cases.<Project>.<Case>.Contract
lake build Benchmark.Cases.<Project>.<Case>.Specs
lake build   # default target builds Cases/ only, skips Generated placeholders
```

All three must be green BEFORE moving to verification.

### 2e. Verification

This is a two-part gate. Both parts must pass before moving to Phase 3.

#### Part A — Agent verification

Spawn a verification agent (or do it yourself in a separate pass) that independently
checks:

1. **Are the claimed Verity gaps legitimate?** For each gap listed in 2c, verify by
   reading the actual Verity source in `.lake/packages/verity/`, any repo-local or
   user-provided fork (e.g. `.context/lfglabs-verity`), and
   [veritylang.com](https://veritylang.com). Also check open issues and PRs on the
   Verity repo — the feature may already be in progress.
2. **Is semantics preserved?** Compare the Verity model against the Solidity source
   function-by-function. Flag any place where behavior differs (missing revert path,
   different overflow semantics, dropped external call, etc.).
3. **Is the Verity model as close to the Solidity as possible?** Flag any unnecessary
   abstraction or structural deviation that could have been avoided.

Report findings as a checklist: each gap either confirmed or disputed, each semantic
deviation either justified or flagged.

#### Part B — Human review

Present the modelization to the user so they can confirm it matches the Solidity source.
Make it easy to review:

- **Side-by-side snippets**: for each key function, show the Solidity source next to the
  Verity translation. Highlight where they differ and why.
- **File pointers**: give the user the exact file paths to open for comparison, e.g.:
  > Compare `contracts/src/Vault.sol:L42-L78` (Solidity) with
  > `Benchmark/Cases/Protocol/Case/Contract.lean:L15-L45` (Verity)
- **Simplification summary**: restate each simplification from the Contract.lean
  doc-comment in plain English, so the user doesn't need to parse Lean to evaluate them.
- **Proposed Verity issues**: present each proposed issue from 2c for the user to
  confirm or reject. Only confirmed issues should be filed on the Verity repository.

End with:

> "Does this modelization faithfully capture the Solidity logic? Which of the proposed
> Verity issues should we file? If anything looks off, point it out and I'll adjust
> before we move to proving."

Do not proceed to Phase 3 until the user confirms.

---

## Phase 3 — Proving (persistent loop)

Write `Proofs.lean` and do not come back until you reach one of three terminal
conditions. This is a loop — keep trying tactics, reading goal states, and making
progress. Never return with "I tried X and it didn't work".

### Terminal conditions

1. **PROOF**: `lake build Benchmark.Cases.<Project>.<Case>.Proofs` succeeds and there
   is no `sorry` in the file.
2. **COUNTER-EXAMPLE**: a concrete `ContractState` + inputs that satisfy the hypotheses
   AND falsify the conclusion. Write it out as a `#eval` or as a comment with exact
   values.
3. **AXIOM**: an `axiom` added to `Proofs.lean` that closes the gap, with a doc-comment
   explaining (a) what exactly the axiom assumes, (b) whether the assumption is true of
   the real contract, (c) why you couldn't discharge it mechanically.

If `simp` leaves a residual goal, read the goal state, identify the missing algebraic
fact or unfolding, and make progress. If truly stuck, add the axiom — don't hide it
behind `sorry`.

### Proving prompt template (for delegated agents)

> **Task: Prove `<theorem_name>` in `Benchmark/Cases/<Project>/<Case>/Proofs.lean`**
>
> Workspace: `<absolute path>`.
>
> **Read first:**
> - `Benchmark/Cases/<Project>/<Case>/Contract.lean` — the model
> - `Benchmark/Cases/<Project>/<Case>/Specs.lean` — the spec to satisfy
> - `Benchmark/Cases/<Project>/<Case>/Proofs.lean` — existing proofs; mirror their style
> - `Benchmark/Generated/<Project>/<Case>/Tasks/<Name>.lean` — the theorem signature you must match exactly
> - Any solved theorem in a sibling case (e.g. `Benchmark/Cases/Safe/OwnerManagerReach/Proofs.lean`) for style
>
> **Do not modify** the Generated placeholder. Only edit `Proofs.lean`.
>
> **Persistence**: never stop until ONE of:
> 1. `lake build Benchmark.Cases.<Project>.<Case>.Proofs` succeeds, no `sorry`.
> 2. You produce a concrete counter-example (values that satisfy hypotheses, falsify
>    the conclusion). Write it as a comment with exact field values.
> 3. You add an `axiom` to close the proof, with a doc-comment stating what was
>    assumed, whether it holds of the real contract, and why it wasn't mechanically
>    discharged.
>
> Do not return "I got stuck". If `simp` leaves a residual goal, read the goal and
> pick a tactic for that specific shape. If that fails, axiomatize with justification.

### 3a. Verification — intellectual honesty check

Once the proof lands, run a verification pass (spawn an agent or do it yourself in a
separate pass) that checks:

1. **Are axioms abusive?** For each axiom in `Proofs.lean`, assess whether it is a
   reasonable trust boundary or whether it smuggles in the conclusion. An axiom that
   restates the theorem in different words is abusive. An axiom that captures a
   well-known EVM property (e.g. "msg.value is paid by the caller") is reasonable.
   Flag any axiom that is doing too much work.
2. **Is every spec actually proven?** Cross-check the theorems in `Proofs.lean` against
   the specs in `Specs.lean`. Every spec must have a corresponding proof. Flag any
   missing coverage.
3. **Is there any `sorry`?** Grep the entire `Proofs.lean` for `sorry`. If any remain,
   the proof is not done — send it back to the proving loop.

Report findings to the user. If any check fails, the proof goes back into the loop.

### 3b. Open a PR on the verity-benchmark repository

Once the proof passes verification, open a pull request on
`https://github.com/lfglabs-dev/verity-benchmark` with the new case (Contract.lean,
Specs.lean, Proofs.lean, Compile.lean, Generated placeholders, YAMLs). Use `gh pr create`
with `--base main`.

### Quick reference: proving recipe

For state-transition theorems on monadic contracts, the proof skeleton is almost
always:

```lean
theorem my_theorem ... (hFrom : (addr != zeroAddress) = true) ... := by
  have hAddrNZ := address_ne_of_neq_zero hFrom   -- helper in Proofs.lean Part 0
  unfold my_spec balanceOf supply
  -- if the contract branches on a value-level condition:
  by_cases hCond : <condition>
  · dsimp
    simp [ContractName.fn, ContractName.fields..., helper_functions...,
          getStorage, setStorage, getMapping, setMapping, getMapping2, setMapping2,
          Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Contract.run, ContractResult.snd,
          <all the hypothesis names>]
    -- residual arithmetic goal on Uint256
    <calc / rw / Uint256 lemmas>
  · ... symmetric branch ...
```

If the residual goal involves `% 2^64`, use the `uint256_mod_uint64_of_lt` helper.
If it involves EVM-add vs hadd, `rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]`.
If it involves `sub + add` cancellation, use `Verity.Core.Uint256.sub_add_cancel_left`.

---

## Phase 4 — Article

Write a case study article following the format used on
[lfglabs.dev](https://github.com/lfglabs-dev/lfglabs.dev). The article is a JSX page
in `pages/research/` with a corresponding entry in `data/research.js`.

### 4a. Learn the existing components and patterns (mandatory before writing)

Before writing a single line of the article, **clone or fetch the lfglabs.dev repo**
and study the existing case studies to learn the exact components, props, and page
structure. Do not guess or improvise component APIs.

Read these files from `https://github.com/lfglabs-dev/lfglabs.dev`:

1. **Existing case study pages** — read at least 2–3 complete pages in `pages/research/`
   to understand the structure, section ordering, and tone. Good examples:
   - `pages/research/lido-vault-solvency.jsx`
   - `pages/research/safe-owner-reachability.jsx`
   - `pages/research/nexus-mutual-book-value.jsx`

2. **Reusable components** — read the source of each component in `components/research/`
   to learn the exact props, expected children, and rendering behavior:
   - `Guarantee.jsx` — how the English/math toggle works, how KaTeX formulas are passed
   - `Hypothesis.jsx` — the `name`, `constraint`, `source` props and how body text is
     rendered
   - `Disclosure.jsx` — collapsible sections, how title and children work
   - `CodeBlock.jsx` — code display for verification commands
   - `ExternalLink.jsx` — link styling
   - Any protocol-specific guarantee components (e.g. `SafeGuarantee.jsx`,
     `NexusMutualGuarantee.jsx`) to see how custom variants are built

3. **Data model** — read `data/research.js` to see the metadata structure (slug, title,
   subtitle, description, date, tag).

4. **Layout and shared components** — check how pages import shared layout, navigation
   (`ResearchCard`, back links), and head/meta tags.

**Do not write the article until you have read all of the above.** Your article must use
the same components with the same prop signatures — not approximations from memory.

### 4b. Specs readability check (before writing the article)

The article will display the invariant both in English and in math notation mirroring
`Specs.lean`. **The math part shown in the article must closely match what is in
`Specs.lean`** — they should be recognizably the same thing.

If the raw spec definition is too complex for a human to parse at a glance, **go back
and refactor `Specs.lean`** to introduce helper definitions that name sub-expressions.
The helpers become the vocabulary the article uses.

Example: instead of showing `state.balances[a] + state.balances[b] + state.balances[c]`
inline in the invariant, define a helper like:

```lean
def totalHeld (s : ContractState) (a b c : Address) : Uint256 :=
  balanceOf s a + balanceOf s b + balanceOf s c
```

Then the spec becomes `totalHeld s a b c ≤ supply s`, which is readable both in Lean
and in the article's math rendering.

**Rule:** if the article's math notation would need to diverge from `Specs.lean` to be
readable, that is a signal to improve `Specs.lean` first — not to show a simplified
version that doesn't match the actual code.

### 4c. Writing style

The article must sound human and concise. Follow these rules:

- **No em dashes.** Use commas, periods, parentheses, or colons instead.
- **No filler phrases.** Cut "it's worth noting that", "importantly", "in order to",
  "it should be noted", "essentially", "fundamentally". Just say the thing.
- **No inflated language.** Say "checks" not "validates", "uses" not "leverages",
  "shows" not "demonstrates". Prefer short everyday words.
- **No rule of three.** Don't list three adjectives or three parallel phrases for
  rhetorical effect. One specific detail beats three vague ones.
- **Short sentences.** If a sentence has more than one comma, split it.
- **Active voice.** "The proof shows X" not "X is shown by the proof".
- **Be specific.** "An attacker could drain the vault" not "security could be
  compromised".

After writing the article, re-read it and strip anything that sounds like it was
generated by an AI. If in doubt, cut it.

### 4d. Article structure

The article page must include these sections, in order. Use the exact components you
learned in 4a — match the prop signatures and patterns from the existing case studies.

1. **The Guarantee** — the invariant displayed with a `<Guarantee>` component (or a
   protocol-specific variant if the invariant needs custom visualization). Show both:
   - **English legend**: one sentence a non-technical reader can understand.
   - **Math notation**: KaTeX rendering that matches `Specs.lean` (using the same
     helper names if any were introduced in 4b).

2. **Context** — short explanation of the protocol and the specific contract/function
   being verified. What does it do, who uses it, what is the unit of value at risk.
   Keep it to 2–3 paragraphs max.

3. **Why This Matters** — what failure mode this invariant prevents. Be concrete: "If
   this invariant were violated, an attacker could mint tokens without depositing
   collateral" — not "this ensures correctness". Use `<Disclosure>` components for
   deeper technical details.

4. **How This Was Modeled & Proven** — explain the Verity modeling approach:
   - Link to the Contract.lean and Proofs.lean files on GitHub.
   - Briefly describe the proof strategy (induction, case split, etc.).
   - Include a `<CodeBlock>` with the `lake build` verification command.
   - Include a `<Disclosure>` "Verify it yourself" section with clone + build
     instructions.

5. **Proof Status** — one of:
   - "Proven" — all specs have corresponding proofs, no `sorry`, no abusive axioms.
   - "Proven with assumptions" — proofs complete but rely on axioms (list them).
   - "In progress" — some specs are not yet proven.

   If there are multiple theorems, show a table (function name / theorem / status).

6. **Assumptions** — list every axiom and hypothesis using `<Hypothesis>` components.
   For each:
   - `name`: the Lean hypothesis name (e.g. `hMaxLS`)
   - `constraint`: the human-readable constraint (e.g. `maxLiabilityShares ≥ liabilityShares`)
   - `source`: where this assumption comes from (audit report, EVM spec, contract invariant)
   - Body text: why this assumption is reasonable, and what breaks if it doesn't hold.

### 4e. Metadata entry

Add an entry to `data/research.js`:

```javascript
{
  slug: '<protocol>-<invariant-short-name>',
  title: '<Protocol> <What Was Proven>',
  subtitle: '<One sentence describing the formal verification>',
  description: '<2-3 sentence description for meta tags>',
  date: '<YYYY-MM-DD>',
  tag: 'Case study'
}
```

### 4f. Verification

Before marking the article as done:

- Confirm the math notation in the article matches `Specs.lean` (same helper names,
  same structure).
- Confirm every assumption listed in the article appears as a hypothesis or axiom in
  the proof.
- Confirm the proof status accurately reflects the state of `Proofs.lean`.
- Confirm you are using the real component APIs from the lfglabs.dev repo (not guessed
  prop names or invented components).
- Confirm there are no em dashes anywhere in the article text.
- Re-read the article and strip anything that sounds AI-generated (filler, inflated
  language, rhetorical patterns).
- Run the dev server and visually check the page renders correctly, KaTeX formulas
  display, and `<Disclosure>` / `<Hypothesis>` components work.

### 4g. Open a PR on the lfglabs.dev repository

Once the article passes verification, open a pull request on
`https://github.com/lfglabs-dev/lfglabs.dev` with the new case study page, any new
components, and the `data/research.js` entry. Use `gh pr create` with `--base main`.

---

## Anti-patterns — do not do these

- Starting `Contract.lean` before explicitly listing the expected simplifications and
  Verity friction points to the user.
- Writing the proof inside `Generated/.../Tasks/*.lean`. That file stays `exact ?_`.
- Batching simplification-reasons under one paragraph ("we simplified FHE"). Each
  simplification gets its own bullet with a concrete "why".
- Using `sorry` to "get something building". Add an `axiom` with justification, or
  stop and ask.
- Skipping Phase 1 because the user gave you an invariant. Still write the
  protocol summary + evaluate the invariant before you touch code.
- Prematurely abstracting the Solidity into a high-level toy model when a closer
  source-structured translation is available.
- Publishing an article saying "all N functions covered" when the theorem count
  doesn't actually cover them. Count proofs against the public function surface before
  claiming coverage.
- Showing math notation in the article that diverges from `Specs.lean`. If the spec
  is too complex to show directly, refactor `Specs.lean` with helpers first.
- Creating issues on the Verity repository without explicit user confirmation.
- Using em dashes in article text. Use commas, periods, or colons instead.
- Writing article prose that sounds AI-generated (filler phrases, inflated language,
  rhetorical rule-of-three patterns).
