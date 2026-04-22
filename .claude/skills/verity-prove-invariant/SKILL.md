---
name: verity-prove-invariant
description: >
  Three-phase workflow for adding a new Verity benchmark case: research the protocol
  and confirm the invariant, audit how close a line-by-line Verity translation can
  stay to the Solidity source, model the contract in Lean with explicit acknowledged
  simplifications, then prove a chosen invariant (or delegate modeling/proving to
  another agent). Trigger terms: verity prove, new benchmark case, prove invariant,
  formally verify, add verity case, verify protocol, model contract in verity, lean
  contract verification.
---

# Verity Prove Invariant

Add a new formal-verification case to the Verity benchmark. The workflow has three
phases, each **gated by explicit user acknowledgement** — never cross a phase boundary
silently.

Default modeling bias:

- Preserve **semantics always**.
- Subject to that, preserve the Solidity source shape as closely as possible:
  function boundaries, helper names, branch structure, slot comments, packed-layout
  intent, and external-call boundaries.
- Do **not** jump to a high-level abstraction if a near line-by-line Verity
  translation is available.
- If you must simplify or structurally rewrite, identify it before modeling and
  explain whether the reason is:
  1. no Verity issue, just a cleaner equivalent expression
  2. proof-coverage gap only
  3. Verity ergonomics / feature gap that should probably be fixed
  4. hard blocker

## When to use

- User asks to formally verify a Solidity contract with Lean/Verity
- User wants to add a new case to this repo's benchmark
- User says "let's prove X on protocol Y", "model Z in Verity"

## When NOT to use

- Scoping / outreach / lead work (that's `verity-scoping`)
- Only reading existing proofs without adding a new one

---

## Phase 1 — Research, invariant alignment, and translation audit (before any code)

Output ONE text response covering all of the following, then **stop and wait for user
acknowledgement**. Do not proceed to Phase 2 until the user explicitly confirms.

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
5. **Draft simplifications before code.** List every simplification you currently
   expect to make, or explicitly say "none yet". If a simplification is driven by
   Verity limitations, say whether:
   - there is a workaround in the current local package
   - there is a workaround in a repo-local or user-provided Verity fork
   - this should probably become a Verity issue
6. **Delegation option.** If the user wants another agent to do the implementation,
   say you can emit a full modeling+proof prompt in the format described in
   `references/delegated-model-and-prove-prompt.md`.
7. **Wait.** End with: "Confirm you're aligned on this invariant, the line-by-line
   modeling plan, and the listed simplifications / Verity gaps, and I'll start
   modelling."

Research the protocol using web fetches of its docs + the actual Solidity source
(raw.githubusercontent.com). Read enough source to identify the require checks, state
variables, storage layout decisions, loops / queues, and external calls you'll need
to decide about modelling fidelity.

Before you claim a Verity limitation, check in this order:

1. the current local package at `.lake/packages/verity/`
2. any repo-local or user-provided Verity fork (for example `.context/lfglabs-verity`)
3. [veritylang.com](https://veritylang.com)

Do not report a construct as unsupported if it is actually present but only has
partial proof coverage. Distinguish clearly between "cannot express", "can express but
proof story is incomplete", and "can express cleanly".

---

## Phase 2 — Line-by-line model scaffold & delegation

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

### 2b. Translation policy before the first edit

Use the following order of preference:

1. near line-by-line Verity translation that preserves source structure and semantics
2. syntax-close rewrite that preserves semantics and leaves the source mapping obvious
3. narrower semantic model with explicit acknowledged simplifications

Do not silently switch from (1) to (3).

If you discover a new simplification after Phase 1 that was not previously disclosed,
stop and tell the user before baking it into the model.

### 2c. Write Contract.lean with an explicit simplifications block

Put a doc-comment at the top listing every simplification you make, in two columns:
"what was simplified" and "why (concretely: the Verity feature that's missing, or the
semantics that would be lost)". Be honest — do not call something a simplification if
you can model it faithfully.

**Before you declare something unsupported, verify it against the current Verity
surface.** Verity evolves across branches. Check:

- `.lake/packages/verity/`
- any repo-local or user-provided Verity fork
- [veritylang.com](https://veritylang.com)

Current Verity gotchas as of this writing (re-check each time — these dated):
- **Lean reserved keywords** inside `verity_contract` parameter lists: `from`, `until`,
  `if`, `then`, `else`, `match`. Rename to `holder`, `expiry`, etc.
- **Allowed DSL bind sources**: `getStorage` / `getStorageAddr` / `getMapping` /
  `getMappingAddr` / `getMapping2` / `getMappingUint` / `msgSender` / `msgValue` /
  `tload` / `ecrecover` / `ecmCall`. **Do not assume `blockTimestamp` is absent**:
  support differs across branches, so verify the actual package/fork before threading
  it as a function parameter.
- **Nested mappings ARE supported** via `Address → Address → Uint256 := slot N` and
  `getMapping2` / `setMapping2`. Don't claim otherwise.
- **No `let (a, b) := pair` destructuring** inside a `verity_contract` function body.
  Inline the tuple fields instead, or compute them outside and pass them in.
- **External calls** often require ECMs, bounded low-level surfaces, or trusted
  boundaries. Preserve the call site structurally where possible; if you must abstract
  it away, say so explicitly.
- **Packed-slot / inline-assembly storage logic** may be representable semantically
  without preserving the exact source write shape. If you rewrite packed writes into
  ordinary fields, keep the original slot/bit-layout intent visible in comments or
  helper definitions.

### 2d. Write Specs.lean

State each property as a `def foo_spec (... : ContractState) : Prop`. Keep specs
minimal — each spec should be one clear sentence of English. Use `balanceOf`, `supply`,
and similar helpers to hide storage-slot indices from the spec surface.

### 2e. Write Generated placeholders + YAMLs

For each theorem, create:
- `Benchmark/Generated/<Project>/<Case>/Tasks/<Name>.lean` ending in `exact ?_`
- `cases/<project>/<case>/tasks/<name>.yaml` pointing at that file
- Matching entry in `case.yaml` selected_functions + abstraction_tags

### 2f. Verify the scaffold builds

```bash
lake build Benchmark.Cases.<Project>.<Case>.Contract
lake build Benchmark.Cases.<Project>.<Case>.Specs
lake build   # default target builds Cases/ only, skips Generated placeholders
```

All three must be green BEFORE you move to the proving step. A scaffold that
doesn't compile wastes every minute of proving time downstream.

### 2g. Delegated modeling+proof prompt (optional)

If the user wants to hand the whole task to another agent **before** or **instead of**
doing the implementation yourself, emit a prompt in the format described in
`references/delegated-model-and-prove-prompt.md`.

That prompt must include:

- absolute workspace path
- pinned upstream source links / commit
- approved invariant
- instruction to preserve source structure line-by-line where possible
- known Verity capability notes and possible simplification pressure points
- required file layout and build commands
- the same persistence rule used for proofs in this skill

### 2h. Hand over to the proving step

Ask the user:

> "The scaffold builds. For each theorem, do you want me to (1) write the proof now,
> or (2) give you a prompt to run in a separate agent? For small theorems I can batch;
> for hard ones you probably want to parallelize across agents."

If (1), proceed to Phase 3 inline. If (2), emit the prompt in `references/proving-prompt.md`
format (see below), then stop.

---

## Phase 3 — Proving (persistent loop)

Whoever is proving — you or a delegated agent — follows these rules:

### The persistence rule

Do not stop until one of three terminal conditions holds:

1. **PROOF**: the theorem compiles with `lake build Benchmark.Cases.<Project>.<Case>.Proofs`
   and there is no `sorry` in the file.
2. **COUNTER-EXAMPLE**: you have a concrete `ContractState` + inputs that satisfy the
   hypotheses AND falsify the conclusion. Write it out as a `#eval` or as a comment
   showing the exact values.
3. **AXIOM**: you add an `axiom` to `Proofs.lean` that closes the gap, with a doc
   comment explaining (a) what exactly the axiom assumes, (b) whether the assumption
   is true of the real contract, (c) why you couldn't discharge it mechanically.

Never return "I tried simp and it didn't close the goal". That is not a terminal
condition. Look at the remaining goal state, identify the missing algebraic fact or
missing unfolding, and make progress. If truly stuck, add the axiom — don't hide it
behind `sorry`.

### Proving prompt template (for delegated agents)

Emit this when the user picks option (2):

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

If the user instead wants a delegated agent to handle both the modeling and the proof,
use the separate template in `references/delegated-model-and-prove-prompt.md`, not the
proof-only prompt above.

### Post-proof review (mandatory)

Once any proof lands, write a short report back to the user:
1. Which hypotheses were actually USED (vs declared-but-unused, which the linter flags).
2. Any **non-obvious hypothesis** and what it rules out — e.g. `hToNoWrap` excludes
   the case where `balanceOf[to] + amount` wraps at 2^64.
3. Any **axiom added**, repeated verbatim with its justification.
4. One sentence: what the proof guarantees about the real contract, and what it
   doesn't.

**Do not mark the case as done until the user confirms they understand each of those
four points.** Completion = user ack, not green CI.

---

## Quick reference: proving recipe that works for this repo

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

## Anti-patterns — do not do these

- Claiming a Verity feature is unsupported without checking the current package first.
- Claiming a Verity feature is unsupported when it is really only a proof-coverage gap.
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
- Publishing an article, readme, or PR saying "all N functions covered" when the
  theorem count doesn't actually cover them. Count proofs against the public function
  surface before claiming coverage.
