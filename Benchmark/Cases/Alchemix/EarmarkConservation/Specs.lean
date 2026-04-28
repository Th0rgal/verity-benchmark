import Verity.Specs.Common
import Benchmark.Cases.Alchemix.EarmarkConservation.Contract

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

-- We use `FiniteSet` from `Verity.Core` without `open Verity.Core` to
-- avoid an ambiguity with `Verity.Uint256` vs `Verity.Core.Uint256`.
abbrev FiniteSet := Verity.Core.FiniteSet

/-
  Specifications for the Alchemix V3 earmark conservation property.

  The team's stated invariant (Ov3rkoalafied, 2026-04-24):
    "The sum of all accounts' earmarked debt equals cumulativeEarmarked
     at all times, across every operation"

  This file formalizes that statement as the *lazy-projected* invariant
  (see Contract.lean for why the literal "stored sum" version is false on
  the deployed code). The lazy-projected version is what the design
  guarantees and is the property whose violation would actually break
  the protocol's collateral accounting.

  Storage layout (from verity_contract AlchemistEarmark):
    slot 0 : cumulativeEarmarked
    slot 1 : totalDebt
    slot 2 : earmarkWeight
    slot 3 : redemptionWeight
    slot 4 : survivalAccumulator
    slot 5 : transmuterEarmarkAmount  (ghost)

    slot 100 : accountDebt[id]
    slot 101 : accountEarmarked[id]
    slot 102 : accountLastAccruedEarmarkWeight[id]
    slot 103 : accountLastAccruedRedemptionWeight[id]
    slot 104 : accountLastSurvivalAccumulator[id]
-/

/-! ## Storage accessors (article-readable surface) -/

/-- Global `cumulativeEarmarked` (slot 0). -/
def cumulativeEarmarked (s : ContractState) : Uint256 := s.storage 0

/-- Global `totalDebt` (slot 1). -/
def totalDebt (s : ContractState) : Uint256 := s.storage 1

/-- Global `_earmarkWeight` (slot 2). -/
def earmarkWeight (s : ContractState) : Uint256 := s.storage 2

/-- Global `_redemptionWeight` (slot 3). -/
def redemptionWeight (s : ContractState) : Uint256 := s.storage 3

/-- Global `_survivalAccumulator` (slot 4). -/
def survivalAccumulator (s : ContractState) : Uint256 := s.storage 4

/-- Per-account `account.debt`. -/
def accountDebt (s : ContractState) (id : Uint256) : Uint256 :=
  s.storageMapUint 100 id

/-- Per-account `account.earmarked` (the *stored* value; can be stale
    relative to `cumulativeEarmarked` between syncs — see `projectedEarmarked`
    for the lazy-projected current value). -/
def accountEarmarked (s : ContractState) (id : Uint256) : Uint256 :=
  s.storageMapUint 101 id

/-- Per-account `account.lastAccruedEarmarkWeight`. -/
def accountLastEarmarkWeight (s : ContractState) (id : Uint256) : Uint256 :=
  s.storageMapUint 102 id

/-- Per-account `account.lastAccruedRedemptionWeight`. -/
def accountLastRedemptionWeight (s : ContractState) (id : Uint256) : Uint256 :=
  s.storageMapUint 103 id

/-! ## Lazy projection — `_computeUnrealizedAccount`

  The Solidity `_computeUnrealizedAccount(account, eW, rW, sA)` returns
  a triple `(newDebt, newEarmarked, redeemedDebt)`. For the conservation
  invariant we only need the second component, so we expose
  `projectedEarmarked` as a single Uint256.

  This mirrors the within-epoch / within-survival-window path of the
  Solidity function (lines 1478-1579) — the same path the Contract.lean
  `syncAccount` function commits to storage. Conservation between the
  projection and the global is what `_sync` is designed to maintain.
-/

/-- Lazy-projected earmarked debt for an account at the current global
    weights, idealized (no Q128 floor-rounding drift).

    Mirrors `_computeUnrealizedAccount(...).newEarmarked` on the
    within-epoch / within-survival-window path. -/
def projectedEarmarked (s : ContractState) (id : Uint256) : Uint256 :=
  let eW := earmarkWeight s
  let rW := redemptionWeight s
  let lastEW := accountLastEarmarkWeight s id
  let lastRW := accountLastRedemptionWeight s id
  let dbt := accountDebt s id
  let earm := accountEarmarked s id

  let unearmarkSurvivalQ := div (mul eW ONE_Q128) lastEW
  let unearmarkSurvivalRatio :=
    if lastEW = eW then ONE_Q128
    else if lastEW = 0 then ONE_Q128
    else unearmarkSurvivalQ

  let redemptionSurvivalQ := div (mul rW ONE_Q128) lastRW
  let redemptionSurvivalRatio :=
    if lastRW = rW then ONE_Q128
    else if lastRW = 0 then ONE_Q128
    else redemptionSurvivalQ

  let userExposure := if dbt > earm then sub dbt earm else 0
  let unearmarkedRemaining := div (mul userExposure unearmarkSurvivalRatio) ONE_Q128
  let earmarkRaw := sub userExposure unearmarkedRemaining
  let totalEarmarkedNow := add earm earmarkRaw
  div (mul totalEarmarkedNow redemptionSurvivalRatio) ONE_Q128

/-! ## The lazy-projected sum -/

/-- Sum of `projectedEarmarked` over a finite set of active token IDs.

    Mirrors `Verity.Specs.Common.Sum.sumBalances` for the Uint256-keyed
    case. The local helper exists because `Verity.Specs.Common.Sum` only
    provides `sumBalances` for `FiniteAddressSet` (slot 0 of
    `s.knownAddresses`); there is no parallel `sumBalancesUint` keyed off
    `FiniteSet Uint256`. See proposed Verity issue. -/
def sumProjectedEarmarked (s : ContractState) (ids : FiniteSet Uint256) : Uint256 :=
  ids.sum (fun id => projectedEarmarked s id)

/-- Sum of stored `account.earmarked` values over `ids`. The team's
    "literal" reading of the invariant. Provably *not* equal to
    `cumulativeEarmarked` in general — it equals it only when every id
    in `ids` has been synced at the current global weights. See
    `synced_corollary_spec`. -/
def sumStoredEarmarked (s : ContractState) (ids : FiniteSet Uint256) : Uint256 :=
  ids.sum (fun id => accountEarmarked s id)

/-! ## The conservation invariant -/

/-- **Lazy-projected earmark conservation** (the headline invariant).

    The sum, over all active accounts, of the lazily-projected earmarked
    debt equals the global `cumulativeEarmarked`. The projection uses
    `_computeUnrealizedAccount` against the current global weights, so it
    reflects each account's "current" earmarked even when its stored field
    is stale.

    This is what the team meant by "the sum of all accounts' earmarked debt
    equals cumulativeEarmarked at all times, across every operation":
    the lazily-corrected sum, which is what every downstream consumer
    (`_calculateUnrealizedDebt`, redemption math, collateral debit) actually
    uses. -/
def earmark_conservation_spec
    (s : ContractState) (ids : FiniteSet Uint256) : Prop :=
  sumProjectedEarmarked s ids = cumulativeEarmarked s

/-- **Synced corollary** — the human-readable form, used in the case-study
    article alongside the lazy-projected statement.

    If every active account has been re-synced at the current global
    weights (so its stored earmarked equals its projection), then the
    literal sum of stored values equals `cumulativeEarmarked`. Implied by
    `earmark_conservation_spec` together with the assumption of full sync. -/
def synced_corollary_spec
    (s : ContractState) (ids : FiniteSet Uint256) : Prop :=
  (∀ id ∈ ids.elements, accountEarmarked s id = projectedEarmarked s id) →
  sumStoredEarmarked s ids = cumulativeEarmarked s

/-! ## Per-operation preservation specs

  The conservation invariant must hold "at all times, across every
  operation". The skill workflow proves this by per-operation preservation:
  each operation maps a state satisfying the invariant to a state still
  satisfying it.

  In-scope operations: `earmark`, `syncAccount`, `redeem`,
  `subEarmarkedDebt`, `subDebt`. (`_computeUnrealizedAccount` is pure
  read-only — it cannot violate the invariant.)
-/

/-- Preservation under `earmark()`. -/
def earmark_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256) : Prop :=
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-- Preservation under `syncAccount(id)`. -/
def syncAccount_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256) : Prop :=
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-- Preservation under `redeem(amount)`. -/
def redeem_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256) : Prop :=
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-- Preservation under `subEarmarkedDebt(amount, accountId)`.

    This requires `accountId ∈ ids` — the operation is invariant-preserving
    only when applied to an account that's actually being tracked. -/
def subEarmarkedDebt_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256)
    (accountId : Uint256) : Prop :=
  accountId ∈ ids.elements →
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-- Preservation under `subDebt(tokenId, amount)`. -/
def subDebt_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256)
    (tokenId : Uint256) : Prop :=
  tokenId ∈ ids.elements →
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-! ## Sanity properties (lemmas that should hold trivially) -/

/-- `cumulativeEarmarked ≤ totalDebt` — enforced by the clamp at
    AlchemistV3.sol:1306. Useful as a side-lemma in conservation proofs. -/
def cumulativeEarmarked_le_totalDebt_spec (s : ContractState) : Prop :=
  cumulativeEarmarked s ≤ totalDebt s

end Benchmark.Cases.Alchemix.EarmarkConservation
