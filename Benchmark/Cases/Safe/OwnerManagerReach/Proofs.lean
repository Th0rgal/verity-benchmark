import Benchmark.Cases.Safe.OwnerManagerReach.Specs

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/-
  Reference proofs for the Safe OwnerManager linked list invariants.

  Status:
  - `in_list_reachable` (addOwner, inListReachable): PROVEN
  - `removeOwner_inListReachable`: sorry (proof task)
  - `swapOwner_inListReachable`: sorry (proof task)
  - `setupOwners_establishes`: sorry (proof task)
  - `addOwner_ownerListInvariant`: sorry (proof task)
  - `removeOwner_ownerListInvariant`: sorry (proof task)
  - `swapOwner_ownerListInvariant`: sorry (proof task)
  - `setupOwners_ownerListInvariant`: sorry (proof task)
  - `addOwner_acyclicity`: sorry (proof task)
  - `removeOwner_acyclicity`: sorry (proof task)
  - `swapOwner_acyclicity`: sorry (proof task)
  - `setupOwners_acyclicity`: sorry (proof task)
-/

/-! ═══════════════════════════════════════════════════════════════════
    Part 1: Existing proof — addOwner preserves inListReachable
    (legacy spec, fully proven)
    ═══════════════════════════════════════════════════════════════════ -/

/-! ## Address/word roundtrip -/

-- The address→word→address roundtrip is the identity.
-- wordToAddress (addressToWord a) = a because Address.modulus ≤ Uint256.modulus.
@[simp] private theorem wordToAddress_addressToWord (a : Address) :
    wordToAddress (addressToWord a) = a := by
  simp [addressToWord, wordToAddress, Verity.Core.Address.ofNat, Verity.Core.Address.toNat,
    Verity.Core.Uint256.ofNat]
  ext
  change a.val % Verity.Core.Uint256.modulus % Verity.Core.Address.modulus = a.val
  simp only [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Verity.Core.Address.modulus, Verity.Core.ADDRESS_MODULUS]
  have hlt : a.val < 2 ^ 160 := a.isLt
  omega

/-! ## Post-state characterization -/

-- Characterize the storageMap of the post-state after addOwner.
-- The two setMappingAddr calls write:
--   storageMap 0 SENTINEL := addressToWord owner
--   storageMap 0 owner    := addressToWord (old head)
-- Everything else is unchanged.
set_option maxHeartbeats 6400000 in
private theorem addOwner_storageMap
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (sl : Nat) (addr : Address) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    s'.storageMap sl addr =
      if sl = 0 ∧ addr = SENTINEL then addressToWord owner
      else if sl = 0 ∧ addr = owner then addressToWord (wordToAddress (s.storageMap 0 SENTINEL))
      else s.storageMap sl addr := by
  have hNZ : owner ≠ (0 : Address) := by
    intro h; subst h; simp at hNotZero
  have hNS_ofNat : owner ≠ Verity.Core.Address.ofNat 1 := by
    intro h
    have : owner = SENTINEL := by simp [SENTINEL]; exact h
    simp [this] at hNotSentinel
  have hFr_ofNat : Verity.Core.Address.ofNat (s.storageMap 0 owner).val = (0 : Address) := by
    have := hFresh
    simp [BEq.beq, wordToAddress, zeroAddress] at this
    exact this
  simp [OwnerManager.addOwner, OwnerManager.owners, OwnerManager.sentinel,
    OwnerManager.ownerCount, SENTINEL,
    Contract.run, ContractResult.snd, Verity.require, Verity.bind, Bind.bind,
    getMappingAddr, setMappingAddr, setMapping,
    getStorage, setStorage,
    hNZ, hNS_ofNat, hFr_ofNat]
  rfl

-- Characterize the next-pointer map of the post-state directly.
-- After addOwner(owner) on state s (guards passing):
--   next s' SENTINEL = owner
--   next s' owner    = next s SENTINEL
--   next s' k        = next s k   for k ≠ SENTINEL, k ≠ owner
private theorem addOwner_next_eq
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (k : Address) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    next s' k =
      if k = SENTINEL then owner
      else if k = owner then next s SENTINEL
      else next s k := by
  simp only [next]
  rw [addOwner_storageMap owner s hNotZero hNotSentinel hFresh 0 k]
  simp only [true_and]
  split
  · -- k = SENTINEL: wordToAddress (addressToWord owner) = owner
    apply Verity.Core.Address.ext
    simp [Verity.Core.Address.toNat, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
      Verity.Core.Address.modulus, Verity.Core.ADDRESS_MODULUS, Verity.Core.Address.ofNat]
    have := owner.isLt
    simp only [Verity.Core.ADDRESS_MODULUS] at this
    omega
  · split
    · -- k = owner: word→address→word roundtrip simplifies
      apply Verity.Core.Address.ext
      simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
        Verity.Core.Address.modulus, Verity.Core.ADDRESS_MODULUS, Verity.Core.Address.ofNat,
        Verity.Core.Address.toNat]
    · -- k ≠ SENTINEL, k ≠ owner: unchanged
      rfl

/-! ## Reachability combinators -/

private theorem reachable_self (s : ContractState) (a : Address) :
    reachable s a a :=
  ⟨[a], rfl, rfl, trivial⟩

private theorem reachable_step (s : ContractState) (a b : Address) (h : next s a = b) :
    reachable s a b :=
  ⟨[a, b], rfl, rfl, h, trivial⟩

private theorem reachable_prepend (s : ContractState) (a b c : Address)
    (hab : next s a = b) (hbc : reachable s b c) :
    reachable s a c := by
  obtain ⟨chain, hHead, hLast, hValid⟩ := hbc
  cases chain with
  | nil => simp at hHead
  | cons d rest =>
    simp at hHead; subst hHead
    exact ⟨a :: d :: rest, rfl, hLast, hab, hValid⟩

/-! ## Chain lifting: pre-state chain → post-state chain -/

-- If no node in a chain is SENTINEL or owner, then the chain is still
-- valid in the post-state (because those nodes' next pointers are unchanged).
private theorem isChain_lift
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (chain : List Address)
    (hValid : isChain s chain)
    (hNoSent : ∀ a ∈ chain, a ≠ SENTINEL)
    (hNoOwner : ∀ a ∈ chain, a ≠ owner) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    isChain s' chain := by
  induction chain with
  | nil => exact trivial
  | cons hd tail ih =>
    match tail, hValid with
    | [], _ => exact trivial
    | b :: rest, hValid =>
      have ha_ne_sent : hd ≠ SENTINEL := hNoSent hd (by simp)
      have ha_ne_owner : hd ≠ owner := hNoOwner hd (by simp)
      have hNextA : next ((OwnerManager.addOwner owner).run s).snd hd = next s hd := by
        rw [addOwner_next_eq owner s hNotZero hNotSentinel hFresh hd]
        simp [ha_ne_sent, ha_ne_owner]
      have hab : next s hd = b := hValid.1
      have hRestValid : isChain s (b :: rest) := hValid.2
      constructor
      · rw [hNextA, hab]
      · exact ih hRestValid
          (fun x hx => hNoSent x (List.mem_cons_of_mem hd hx))
          (fun x hx => hNoOwner x (List.mem_cons_of_mem hd hx))

/-! ## addOwner: inListReachable preservation (proven) -/

/--
  Certora `inListReachable` invariant preservation under `addOwner`.
  Given the invariant holds on the pre-state, it holds on the post-state.

  Proof strategy:
  - SENTINEL: trivially reachable (reflexivity)
  - owner: reachable via [SENTINEL, owner] since next s' SENTINEL = owner
  - Other key with next s' key ≠ 0:
    Since key ≠ SENTINEL, key ≠ owner, we have next s' key = next s key ≠ 0.
    By the pre-state invariant, reachable s SENTINEL key with some chain.
    We adapt: s' path is SENTINEL → owner → (old head) → ... → key
    The subchain (old_head → ... → key) has no SENTINEL or owner,
    so their pointers are unchanged. We lift and prepend.
-/
theorem in_list_reachable
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    -- Pre-state invariant
    (_hPreSentNZ : next s SENTINEL ≠ zeroAddress)
    (hPreReach : ∀ key : Address, next s key ≠ zeroAddress → reachable s SENTINEL key)
    -- Acyclicity: SENTINEL does not appear in any chain from SENTINEL's successor.
    (hAcyclic : ∀ key : Address, ∀ chain : List Address,
      chain.head? = some (next s SENTINEL) →
      chain.getLast? = some key →
      isChain s chain →
      SENTINEL ∉ chain)
    -- owner is fresh (not in the list)
    (hOwnerFresh : ∀ key : Address, ∀ chain : List Address,
      chain.head? = some (next s SENTINEL) →
      chain.getLast? = some key →
      isChain s chain →
      owner ∉ chain) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    in_list_reachable_spec s s' := by
  have hNextEq := addOwner_next_eq owner s hNotZero hNotSentinel hFresh
  have hSent : next ((OwnerManager.addOwner owner).run s).snd SENTINEL = owner := by
    rw [hNextEq]; simp
  have hOwnerNZ : owner ≠ zeroAddress := by
    intro h; subst h; simp at hNotZero
  have hOwnerNS : owner ≠ SENTINEL := by
    intro h; subst h; simp at hNotSentinel
  unfold in_list_reachable_spec
  constructor
  -- Part 1: next s' SENTINEL ≠ 0
  · rw [hSent]; exact hOwnerNZ
  -- Part 2: ∀ key, next s' key ≠ 0 → reachable s' SENTINEL key
  · intro key hKeyNZ
    by_cases hKeySent : key = SENTINEL
    · subst hKeySent
      exact reachable_self ((OwnerManager.addOwner owner).run s).snd SENTINEL
    · by_cases hKeyOwner : key = owner
      · subst hKeyOwner
        exact reachable_step ((OwnerManager.addOwner key).run s).snd SENTINEL key hSent
      · -- key ≠ SENTINEL, key ≠ owner → next s' key = next s key
        have hNextK : next ((OwnerManager.addOwner owner).run s).snd key = next s key := by
          rw [hNextEq]; simp [hKeySent, hKeyOwner]
        have hPreNZ : next s key ≠ zeroAddress := by rwa [hNextK] at hKeyNZ
        -- Pre-state: reachable s SENTINEL key
        obtain ⟨chain, hHead, hLast, hValid⟩ := hPreReach key hPreNZ
        -- chain starts at SENTINEL. Extract the tail.
        match chain, hHead with
        | [], h => simp at h
        | [a], h =>
          simp at h hLast; subst h; subst hLast; exact absurd rfl hKeySent
        | a :: b :: rest, h =>
          simp at h; subst h
          -- chain = SENTINEL :: b :: rest, with next s SENTINEL = b
          have hNextSent : next s SENTINEL = b := hValid.1
          have hRestValid : isChain s (b :: rest) := hValid.2
          -- In s', owner → next s SENTINEL = b
          have hOwnerB : next ((OwnerManager.addOwner owner).run s).snd owner = b := by
            rw [hNextEq]; simp [hOwnerNS]; exact hNextSent
          -- The subchain b :: rest has no SENTINEL or owner
          have hNoSent : ∀ x ∈ (b :: rest), x ≠ SENTINEL :=
            fun x hx habs => hAcyclic key (b :: rest)
              (by simp [hNextSent]) hLast hRestValid (habs ▸ hx)
          have hNoOwner : ∀ x ∈ (b :: rest), x ≠ owner :=
            fun x hx habs => hOwnerFresh key (b :: rest)
              (by simp [hNextSent]) hLast hRestValid (habs ▸ hx)
          -- Lift the subchain to s'
          have hRest' : isChain ((OwnerManager.addOwner owner).run s).snd (b :: rest) :=
            isChain_lift owner s hNotZero hNotSentinel hFresh (b :: rest) hRestValid hNoSent hNoOwner
          -- Reachable: s' SENTINEL → owner → b → ... → key
          have hBK : reachable ((OwnerManager.addOwner owner).run s).snd b key :=
            ⟨b :: rest, rfl, hLast, hRest'⟩
          exact reachable_prepend ((OwnerManager.addOwner owner).run s).snd SENTINEL owner key hSent
            (reachable_prepend ((OwnerManager.addOwner owner).run s).snd owner b key hOwnerB hBK)

/-! ═══════════════════════════════════════════════════════════════════
    Part 2: New proof tasks — sorry stubs
    These are benchmark tasks for AI proof agents to complete.
    ═══════════════════════════════════════════════════════════════════ -/

/-! ## removeOwner: inListReachable preservation -/

/--
  Certora `inListReachable` invariant preservation under `removeOwner`.

  After removing `owner` (unlinking it from `prevOwner`), every node with
  a non-zero successor in the post-state must still be reachable from SENTINEL.

  Proof sketch:
  - The removed owner's mapping becomes 0, so it no longer triggers the invariant.
  - prevOwner now points to owner's old successor; the chain "skips" over owner.
  - All other next pointers are unchanged.
  - For any key reachable pre-state: if its witness chain didn't go through
    owner, it lifts directly. If it did, replace the [... → prevOwner → owner → X → ...]
    segment with [... → prevOwner → X → ...] since prevOwner now points to X.
-/
theorem removeOwner_inListReachable
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    -- Pre-state invariant
    (hPreInv : inListReachable s)
    -- Acyclicity
    (hAcyclic : acyclic s) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    inListReachable s' := by
  sorry

/-! ## swapOwner: inListReachable preservation -/

/--
  Certora `inListReachable` invariant preservation under `swapOwner`.

  swapOwner replaces oldOwner with newOwner in-place:
    owners[newOwner] = owners[oldOwner]
    owners[prevOwner] = newOwner
    owners[oldOwner] = 0

  Proof sketch:
  - newOwner inherits oldOwner's successor, so the chain is re-spliced.
  - For any key: if its pre-state chain went through oldOwner, replace
    that segment with newOwner (same successor, same downstream chain).
  - The chain [... → prevOwner → oldOwner → X → ...] becomes
    [... → prevOwner → newOwner → X → ...].
-/
theorem swapOwner_inListReachable
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    -- Pre-state invariant
    (hPreInv : inListReachable s)
    -- Acyclicity
    (hAcyclic : acyclic s)
    -- newOwner is fresh
    (hFresh : freshInList s newOwner) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    inListReachable s' := by
  sorry

/-! ## setupOwners: establishes inListReachable (base case) -/

/--
  setupOwners establishes the inListReachable invariant from a clean state.
  This is the base case: no pre-state invariant is required.

  After setupOwners(owner1, owner2, owner3), the linked list is:
    SENTINEL → owner1 → owner2 → owner3 → SENTINEL

  Every node with a non-zero successor (SENTINEL, owner1, owner2, owner3)
  is reachable from SENTINEL by construction.
-/
theorem setupOwners_inListReachable
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    inListReachable s' := by
  sorry

/-! ═══════════════════════════════════════════════════════════════════
    Part 3: ownerListInvariant (combined) preservation — sorry stubs
    These combine inListReachable + reachableInList into the unified
    ownerListInvariant property.
    ═══════════════════════════════════════════════════════════════════ -/

theorem addOwner_ownerListInvariant
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (hPreInv : ownerListInvariant s)
    (hAcyclic : acyclic s)
    (hFreshInList : freshInList s owner) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    ownerListInvariant s' := by
  sorry

theorem removeOwner_ownerListInvariant
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (hPreInv : ownerListInvariant s)
    (hAcyclic : acyclic s) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    ownerListInvariant s' := by
  sorry

theorem swapOwner_ownerListInvariant
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    (hPreInv : ownerListInvariant s)
    (hAcyclic : acyclic s)
    (hFresh : freshInList s newOwner) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    ownerListInvariant s' := by
  sorry

theorem setupOwners_ownerListInvariant
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    ownerListInvariant s' := by
  sorry

/-! ═══════════════════════════════════════════════════════════════════
    Part 4: Acyclicity preservation — sorry stubs
    Proving these would eliminate the hAcyclic / hOwnerFresh axioms
    from the reachability proofs above.
    ═══════════════════════════════════════════════════════════════════ -/

/--
  addOwner preserves acyclicity.

  Proof sketch: After addOwner(owner), the list is
    SENTINEL → owner → old_head → ... → SENTINEL
  The new node (owner) was fresh (not in any existing chain), and
  SENTINEL's new successor is owner (not SENTINEL). The rest of the
  chain is unchanged, and by pre-state acyclicity, SENTINEL did not
  appear in the old tail. So SENTINEL still doesn't appear in any
  post-state chain from SENTINEL's successor.
-/
theorem addOwner_acyclicity
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (hPreAcyclic : acyclic s)
    (hFreshInList : freshInList s owner) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    acyclic s' := by
  sorry

/--
  removeOwner preserves acyclicity.

  Proof sketch: Removing a node shortens the chain. If SENTINEL was not
  in any pre-state chain past the head, and removing a node only splices
  out one element (without introducing SENTINEL), SENTINEL remains absent
  from all post-state chains.
-/
theorem removeOwner_acyclicity
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (hPreAcyclic : acyclic s) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    acyclic s' := by
  sorry

/--
  swapOwner preserves acyclicity.

  Proof sketch: swapOwner replaces oldOwner with newOwner in-place.
  The chain length is preserved. Since newOwner was fresh (not in the
  pre-state chain) and oldOwner is removed, no new cycles are introduced.
-/
theorem swapOwner_acyclicity
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    (hPreAcyclic : acyclic s)
    (hFresh : freshInList s newOwner) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    acyclic s' := by
  sorry

/--
  setupOwners establishes acyclicity.

  The constructed list SENTINEL → o1 → o2 → o3 → SENTINEL has no
  internal cycles because all three owners are distinct, non-zero,
  and non-sentinel. SENTINEL appears only as the list head and the
  terminal pointer (o3 → SENTINEL), never in the interior.
-/
theorem setupOwners_acyclicity
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    acyclic s' := by
  sorry

end Benchmark.Cases.Safe.OwnerManagerReach
