import Uring.RecycleOnce

/-!
# Iocore.Slab — the generation-tagged pending-operation slab, verified

A completion reactor keys every in-flight operation by a small integer it hands
to the kernel as the completion correlator (`user_data`). On completion the
kernel echoes that integer back, and the reactor must map it to the operation
that was submitted. The danger is **ABA**: a slot freed and reused between
submit and completion would let a *stale* completion (referencing the previous
occupant) be mistaken for the new one. The running reactors avoid this with a
generation-tagged slab; here we make the safety a theorem.

## The model

A `Slab` is a list of `Slot`s; each slot carries a `gen` (generation counter)
and an optional `payload`. A `Key` is the reactor's correlator — an `(idx, gen)`
pair. The kernel-facing scalar (a `u64` in the running reactor) packs the
generation in the high half and the index in the low half; `Key.pack` /
`Key.unpack` model that packing and `Key.unpack_pack` proves it round-trips.

Operations:

* `insert v` — take the lowest free slot at index ≥ 1 (or grow by one), store
  `v`, and return a key tagged with that slot's current generation;
* `get k` / `remove k` — look up / take the payload, but **only if the slot's
  generation matches the key's**. `remove` bumps the generation, so every key
  minted before the removal is thereafter stale.

Index 0 is reserved (never allocated): the kernel's wakeup sentinel uses
correlator 0, so a real operation must never receive key index 0.

## What is proven (0 sorries)

* `slab_insert_get` — a fresh insert is retrievable under its returned key;
* `slab_remove_bumps_gen` — removal increments the slot generation;
* `slab_stale_key_none` — **ABA safety**: a `get` whose key generation does not
  match the slot returns `none`. A completion that references a recycled slot
  cannot be accepted;
* `slab_recycled_key_rejected` — the same key, applied to the slab *after* its
  slot was removed (recycled), is rejected;
* `slab_no_double_remove` — a key removes at most once (the slab-level analogue
  of `Uring.recycle_at_most_once`);
* `slab_insert_idx_ne_zero` / `slab_index0_reserved` — the wakeup-sentinel index
  0 is never allocated and never names a live operation.

## Model-refines-Rust

This is the SPEC; the running Rust reactor's slot table is its realization. The
`(gen, index)` key packing, the match-on-completion generation check, and the
generation bump on free are the executable form of `Key.pack`, `Slab.get`, and
`Slab.remove` here — exactly as the buffer ring realizes `Uring.RecycleOnce`.
The slab lifecycle *is* a lease: `insert` acquires, `remove` recycles, and
`slab_no_double_remove` is `Uring.recycle_at_most_once` read at the slot level.
-/

namespace Iocore

/-- A slab slot: a generation counter and, when occupied, its payload. Occupancy
is `payload.isSome` — no separate flag can drift out of sync with the payload. -/
structure Slot (α : Type) where
  /-- Generation counter; bumped on every free so stale keys stop matching. -/
  gen : Nat
  /-- The stored operation, or `none` when the slot is free. -/
  payload : Option α

/-- A slot is occupied exactly when it holds a payload. -/
def Slot.occupied (s : Slot α) : Bool := s.payload.isSome

/-- The reactor's completion correlator: a slot index tagged with the
generation the slot had at allocation time. -/
structure Key where
  /-- Slot index (the low half of the packed `u64`). -/
  idx : Nat
  /-- Generation tag (the high half of the packed `u64`). -/
  gen : Nat
deriving DecidableEq, Repr

/-- The generation shift: `2^32`, the boundary between the packed key's halves. -/
def genShift : Nat := 4294967296

/-- Pack a key into the kernel-facing scalar: generation in the high half,
index in the low half (`(gen << 32) | idx`). -/
def Key.pack (k : Key) : Nat := k.gen * genShift + k.idx

/-- Unpack the scalar back into `(idx, gen)`. -/
def Key.unpack (w : Nat) : Key := ⟨w % genShift, w / genShift⟩

/-- The packing round-trips whenever the index fits the low half (as it does:
indices are `u32`). This is why the reactor may carry the whole key in one
kernel correlator word. -/
theorem Key.unpack_pack (k : Key) (h : k.idx < genShift) : Key.unpack k.pack = k := by
  unfold Key.unpack Key.pack
  have hgt : 0 < genShift := by unfold genShift; omega
  have hmod : (k.gen * genShift + k.idx) % genShift = k.idx := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt h
  have hdiv : (k.gen * genShift + k.idx) / genShift = k.gen := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hgt, Nat.div_eq_of_lt h, Nat.zero_add]
  rw [hmod, hdiv]

/-- A generation-tagged slab: a positional list of slots. Index 0 is reserved
(the wakeup sentinel), so `insert` only ever hands out indices ≥ 1. -/
structure Slab (α : Type) where
  /-- Slot table; slot `i` lives at position `i`. -/
  slots : List (Slot α)

/-- A capacity-`n` empty slab: `max 1 n` free slots at generation 0, so the
reserved index 0 always exists. -/
def Slab.empty (α : Type) (n : Nat) : Slab α :=
  ⟨List.replicate (max 1 n) ⟨0, none⟩⟩

/-- Look up the payload at `k`: only if the slot exists **and** its generation
matches the key. A generation mismatch (a recycled slot) yields `none`. -/
def Slab.get (s : Slab α) (k : Key) : Option α :=
  match s.slots[k.idx]? with
  | some slot => if slot.gen = k.gen then slot.payload else none
  | none => none

/-- The allocation predicate: index `i` is allocatable iff it is ≥ 1 (index 0 is
reserved) and its slot is present and free. -/
def Slab.allocAt (s : Slab α) (i : Nat) : Bool :=
  decide (1 ≤ i) && (match s.slots[i]? with | some sl => !sl.occupied | none => false)

/-- The lowest allocatable slot index, if any. -/
def Slab.freeIndex (s : Slab α) : Option Nat :=
  (List.range s.slots.length).find? s.allocAt

/-- Insert a value: reuse the lowest free slot (keeping its current generation)
or grow by one fresh slot. Returns the generation-tagged key and the new slab. -/
def Slab.insert (s : Slab α) (v : α) : Key × Slab α :=
  match s.freeIndex with
  | some i =>
      let g := (s.slots[i]?.map Slot.gen).getD 0
      (⟨i, g⟩, ⟨s.slots.set i ⟨g, some v⟩⟩)
  | none =>
      let i := s.slots.length
      (⟨i, 0⟩, ⟨s.slots ++ [⟨0, some v⟩]⟩)

/-- Remove the value at `k`: only on a generation match with an occupied slot.
On success the slot generation is bumped, invalidating every prior key. -/
def Slab.remove (s : Slab α) (k : Key) : Option (α × Slab α) :=
  match s.slots[k.idx]? with
  | some slot =>
      if slot.gen = k.gen then
        match slot.payload with
        | some v => some (v, ⟨s.slots.set k.idx ⟨slot.gen + 1, none⟩⟩)
        | none => none
      else none
  | none => none

/-! ## ABA safety and the lease theorems -/

/-- **ABA safety.** A `get` whose key generation does not match the slot at its
index returns `none`: a completion referencing a recycled slot cannot be
accepted. -/
theorem slab_stale_key_none (s : Slab α) (k : Key) (slot : Slot α)
    (hslot : s.slots[k.idx]? = some slot) (hgen : slot.gen ≠ k.gen) :
    s.get k = none := by
  unfold Slab.get
  rw [hslot]
  simp [hgen]

/-- `freeIndex` yields an index that is in range and allocatable. -/
theorem Slab.freeIndex_spec (s : Slab α) {i : Nat} (h : s.freeIndex = some i) :
    i < s.slots.length ∧ 1 ≤ i := by
  unfold Slab.freeIndex at h
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  refine ⟨List.mem_range.mp hmem, ?_⟩
  unfold Slab.allocAt at hpred
  simp only [Bool.and_eq_true] at hpred
  exact of_decide_eq_true hpred.1

/-- **Fresh insert is retrievable**: the value just inserted is returned by
`get` under the key `insert` handed back. -/
theorem slab_insert_get (s : Slab α) (v : α) :
    (s.insert v).2.get (s.insert v).1 = some v := by
  unfold Slab.insert
  cases hf : s.freeIndex with
  | some i =>
      obtain ⟨hlt, _⟩ := s.freeIndex_spec hf
      simp [Slab.get, List.getElem?_set_self hlt]
  | none =>
      simp [Slab.get, List.getElem?_concat_length]

/-- **Insert never allocates index 0** — the wakeup-sentinel correlator. -/
theorem slab_insert_idx_ne_zero (s : Slab α) (v : α) (hcap : 1 ≤ s.slots.length) :
    (s.insert v).1.idx ≠ 0 := by
  unfold Slab.insert
  cases hf : s.freeIndex with
  | some i =>
      obtain ⟨_, h1⟩ := s.freeIndex_spec hf
      show i ≠ 0
      omega
  | none =>
      show s.slots.length ≠ 0
      omega

/-- **Removal bumps the generation** of the freed slot. -/
theorem slab_remove_bumps_gen (s : Slab α) (k : Key) (v : α) (s' : Slab α)
    (h : s.remove k = some (v, s')) :
    ∃ slot, s.slots[k.idx]? = some slot ∧
      s'.slots[k.idx]? = some ⟨slot.gen + 1, none⟩ := by
  unfold Slab.remove at h
  cases hslot : s.slots[k.idx]? with
  | none => rw [hslot] at h; dsimp only at h; exact absurd h (by simp)
  | some slot =>
      rw [hslot] at h; dsimp only at h
      by_cases hg : slot.gen = k.gen
      · rw [if_pos hg] at h
        cases hp : slot.payload with
        | none => rw [hp] at h; dsimp only at h; exact absurd h (by simp)
        | some w =>
            rw [hp] at h; dsimp only at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, hs'⟩ := h
            refine ⟨slot, rfl, ?_⟩
            have hlt : k.idx < s.slots.length := by
              obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp hslot
              exact hh
            rw [← hs']
            exact List.getElem?_set_self hlt
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-- If `remove` succeeds, `get` on the same slab agreed (returned the payload). -/
theorem Slab.get_of_remove (s : Slab α) (k : Key) (v : α) (s' : Slab α)
    (h : s.remove k = some (v, s')) : s.get k = some v := by
  unfold Slab.remove at h
  unfold Slab.get
  cases hslot : s.slots[k.idx]? with
  | none => rw [hslot] at h; dsimp only at h; exact absurd h (by simp)
  | some slot =>
      rw [hslot] at h; dsimp only at h ⊢
      by_cases hg : slot.gen = k.gen
      · rw [if_pos hg] at h ⊢
        cases hp : slot.payload with
        | none => rw [hp] at h; dsimp only at h; exact absurd h (by simp)
        | some w =>
            rw [hp] at h; dsimp only at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [h.1]
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-- If `get k` is live, `remove k` succeeds with the same payload. -/
theorem Slab.remove_of_get (s : Slab α) (k : Key) (v : α)
    (h : s.get k = some v) : ∃ s', s.remove k = some (v, s') := by
  unfold Slab.get at h
  unfold Slab.remove
  cases hslot : s.slots[k.idx]? with
  | none => rw [hslot] at h; dsimp only at h; exact absurd h (by simp)
  | some slot =>
      rw [hslot] at h; dsimp only at h; dsimp only
      by_cases hg : slot.gen = k.gen
      · rw [if_pos hg] at h ⊢
        cases hp : slot.payload with
        | none => rw [hp] at h; exact absurd h (by simp)
        | some w =>
            rw [hp] at h; dsimp only
            simp only [Option.some.injEq] at h
            rw [h]
            exact ⟨_, rfl⟩
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **The recycled key is rejected.** After `remove k` recycles the slot, the
same key `k` applied to the resulting slab returns `none` — the crisp ABA
statement composed over a full lease. -/
theorem slab_recycled_key_rejected (s : Slab α) (k : Key) (v : α) (s' : Slab α)
    (h : s.remove k = some (v, s')) : s'.get k = none := by
  obtain ⟨slot, hslot, hs'⟩ := slab_remove_bumps_gen s k v s' h
  -- the recycled slot has generation slot.gen + 1; the key still carries slot.gen
  have hgmatch : slot.gen = k.gen := by
    unfold Slab.remove at h
    rw [hslot] at h; dsimp only at h
    by_cases hg : slot.gen = k.gen
    · exact hg
    · rw [if_neg hg] at h; simp at h
  refine slab_stale_key_none s' k ⟨slot.gen + 1, none⟩ hs' ?_
  show slot.gen + 1 ≠ k.gen
  omega

/-- **No double removal** (the slab-level `Uring.recycle_at_most_once`): a key
removes at most once. The generation bump on the first removal makes the second
attempt stale. -/
theorem slab_no_double_remove (s : Slab α) (k : Key) (v : α) (s' : Slab α)
    (h : s.remove k = some (v, s')) : s'.remove k = none := by
  have hnone : s'.get k = none := slab_recycled_key_rejected s k v s' h
  -- if remove succeeded it would force get = some, contradicting hnone
  cases hr : s'.remove k with
  | none => rfl
  | some p =>
      obtain ⟨w, s''⟩ := p
      have := Slab.get_of_remove s' k w s'' hr
      rw [this] at hnone
      simp at hnone

/-! ## The reserved wakeup-sentinel index -/

/-- Index 0 is reserved: a slab where slot 0 is unoccupied never lets key index 0
name a live operation. -/
theorem slab_index0_reserved (s : Slab α) (k : Key) (hk : k.idx = 0)
    (h0 : ∀ sl, s.slots[0]? = some sl → sl.occupied = false) :
    s.get k = none := by
  unfold Slab.get
  rw [hk]
  cases hslot : s.slots[0]? with
  | none => rfl
  | some sl =>
      have hocc : sl.occupied = false := h0 sl hslot
      unfold Slot.occupied at hocc
      have hp : sl.payload = none := Option.not_isSome_iff_eq_none.mp (by simp [hocc])
      simp [hp]

/-- Reachability-friendly reserved-index invariant: slot 0 is unoccupied. -/
def Slab.Reserved (s : Slab α) : Prop :=
  ∀ sl, s.slots[0]? = some sl → sl.occupied = false

/-- The empty slab reserves index 0. -/
theorem Slab.empty_reserved (α : Type) (n : Nat) : (Slab.empty α n).Reserved := by
  intro sl hsl
  unfold Slab.empty at hsl
  have : (List.replicate (max 1 n) (⟨0, none⟩ : Slot α))[0]? = some ⟨0, none⟩ := by
    have hpos : 0 < max 1 n := by omega
    rw [List.getElem?_replicate]
    simp [hpos]
  rw [this] at hsl
  cases hsl
  rfl

/-- `insert` preserves the reserved-index invariant (it never writes index 0). -/
theorem Slab.insert_reserved (s : Slab α) (v : α) (hcap : 1 ≤ s.slots.length)
    (hr : s.Reserved) : (s.insert v).2.Reserved := by
  intro sl hsl
  unfold Slab.insert at hsl
  cases hf : s.freeIndex with
  | some i =>
      obtain ⟨_, h1⟩ := s.freeIndex_spec hf
      rw [hf] at hsl
      simp only [] at hsl
      have hne : i ≠ 0 := by omega
      rw [List.getElem?_set_ne (by omega)] at hsl
      exact hr sl hsl
  | none =>
      rw [hf] at hsl
      simp only [] at hsl
      have h0 : (s.slots ++ [(⟨0, some v⟩ : Slot α)])[0]? = s.slots[0]? := by
        rw [List.getElem?_append_left (by omega)]
      rw [h0] at hsl
      exact hr sl hsl

/-- `remove` preserves the reserved-index invariant. Because index 0 is never
allocated, a successful removal is at some index ≥ 1; but even a removal keyed at
index 0 only bumps a generation, never occupies. -/
theorem Slab.remove_reserved (s : Slab α) (k : Key) (v : α) (s' : Slab α)
    (hr : s.Reserved) (h : s.remove k = some (v, s')) : s'.Reserved := by
  intro sl hsl
  unfold Slab.remove at h
  cases hslot : s.slots[k.idx]? with
  | none => rw [hslot] at h; dsimp only at h; exact absurd h (by simp)
  | some slot =>
      rw [hslot] at h; dsimp only at h
      by_cases hg : slot.gen = k.gen
      · rw [if_pos hg] at h
        cases hp : slot.payload with
        | none => rw [hp] at h; dsimp only at h; exact absurd h (by simp)
        | some w =>
            rw [hp] at h; dsimp only at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, hs'⟩ := h
            subst hs'
            dsimp only at hsl
            by_cases hk0 : k.idx = 0
            · have hlt : (0 : Nat) < s.slots.length := by
                obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp hslot
                rw [hk0] at hh; exact hh
              rw [hk0, List.getElem?_set_self hlt] at hsl
              simp only [Option.some.injEq] at hsl
              rw [← hsl]; rfl
            · rw [List.getElem?_set_ne hk0] at hsl
              exact hr sl hsl
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## Non-vacuity: concrete slab traces

Truth-table checks on concrete op/key sequences: fresh accepted, sentinel index
never allocated, and the full ABA scenario (insert → remove → reinsert reuses
the slot, stale key rejected, fresh key accepted). -/

-- Fresh key accepted: the value inserted is retrievable under its key.
#guard (((Slab.empty Nat 4).insert 7).2.get ((Slab.empty Nat 4).insert 7).1) == some 7

-- The allocated index is never the reserved sentinel index 0.
#guard ((Slab.empty Nat 4).insert 7).1.idx != 0

-- Round-trip + ABA on a concrete slab: value recovered, slot reused, stale key
-- rejected, fresh key accepted, and the reserved sentinel key stays dead.
private def abaSlab : Option Bool :=
  let s0 := Slab.empty Nat 4
  let (k1, s1) := s0.insert 7
  (s1.remove k1).map (fun (v, s2) =>
    let (k2, s3) := s2.insert 99
    v == 7 && k2.idx == k1.idx && (s3.get k1 == none) && (s3.get k2 == some 99)
      && (s3.get ⟨0, 0⟩ == none))

-- The whole ABA scenario evaluates to `some true`.
#guard abaSlab == some true

-- The wakeup-sentinel key is dead on a fresh slab.
#guard (Slab.empty Nat 4).get ⟨0, 0⟩ == none

end Iocore
