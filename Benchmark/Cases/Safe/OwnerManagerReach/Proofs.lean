import Benchmark.Cases.Safe.OwnerManagerReach.Specs

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/-
  Reference proofs for the Safe OwnerManager linked list invariants.

  Status:
  - `in_list_reachable` (addOwner, inListReachable): PROVEN
  - additional theorem statements for future work live in `OpenProofs.lean`
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

end Benchmark.Cases.Safe.OwnerManagerReach
