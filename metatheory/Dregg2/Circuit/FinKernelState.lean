/-
# Dregg2.Circuit.FinKernelState — DEBT-B lane R1: the finite-map data refinement FOUNDATION.

The kernel (`Dregg2/Exec/RecordKernel.lean:309` `RecordKernelState`) models per-cell state as TOTAL
FUNCTIONS over the infinite `CellId` domain (`cell : CellId → Value`, `caps : Label → List Cap`,
`bal : CellId → AssetId → ℤ`, …). A commitment `RH : … → ℤ` cannot injectively bind an infinite-domain
function, so `RestHashIffFrame` and the whole-kernel binding downstream are unsatisfiable-in-application
(CARRIER-CENSUS.md DEBT B, ~250 uses). The deployed Rust ALREADY stores these sparsely (`HashMap`/
`BTreeMap`), and the deployed commitment folds a SORTED-canonical leaf list
(`cap_root.rs::CanonicalCapTree`, `StateCommit.lean:151`, `ListCommit.lean:34`). So we remodel the
function-valued fields as SORTED-NODUP finite maps — the exact object the impl commits over.

This file (lane R1) is the FOUNDATION: the `SortedMap` kernel with its canonical-form theorem
`SortedMap.ext` (PROVED — sorted+nodup ⇒ the entries list is determined by `lookup`), the `FinKernelState`
mirror, its `denote` into `RecordKernelState`, the load-bearing `denote_injective` (PROVED), the initial
state, and the surjectivity-on-reachable HONESTY GATE stated with the per-effect commuting square as an
EXPLICIT hypothesis to be discharged by lane R3 (never assumed as a carrier).

REPRESENTATION LOCKED (ember): a sorted-nodup association list, NOT Mathlib `Finmap`. Serialization is
DEFINITIONAL (it is what the deployed commitment sorts+folds), so injectivity is DIRECT.

NO carrier laundering: `SortedMap.ext`, `SortedMap.get_ext`, `denote_injective` are THEOREMS, not `def …Sound`.
-/
import Dregg2.Exec.RecordKernel
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex

namespace Dregg2.Circuit.FinKernelState

open Dregg2.Exec Dregg2.Authority

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

/-! ## §0 — the sorted-nodup association list `lookup`.

`lookupList k l` returns the value stored at key `k` (the FIRST match; on a nodup-key list the unique
one). Keys carry a `LinearOrder`, which supplies the `DecidableEq` the match needs. -/

variable {K : Type u} {V : Type v}

/-- Raw association-list lookup (first match). -/
def lookupList [DecidableEq K] (k : K) : List (K × V) → Option V
  | [] => none
  | (k', v) :: rest => if k' = k then some v else lookupList k rest

/-- A `lookupList` hit exhibits the pair in the list. -/
theorem mem_of_lookupList_eq_some [DecidableEq K] {k : K} {v : V} :
    ∀ {l : List (K × V)}, lookupList k l = some v → (k, v) ∈ l
  | [], h => by simp [lookupList] at h
  | (k', v') :: rest, h => by
      simp only [lookupList] at h
      by_cases hk : k' = k
      · rw [if_pos hk] at h; subst hk; cases h; exact List.mem_cons_self
      · rw [if_neg hk] at h; exact List.mem_cons_of_mem _ (mem_of_lookupList_eq_some h)

/-- On a list with NODUP keys, a member pair is exactly what `lookupList` returns at its key. -/
theorem lookupList_eq_some_of_mem [DecidableEq K] {k : K} {v : V} :
    ∀ {l : List (K × V)}, (l.map Prod.fst).Nodup → (k, v) ∈ l → lookupList k l = some v
  | [], _, h => by simp at h
  | (k', v') :: rest, hnd, hmem => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnotin, hndrest⟩ := hnd
      rcases List.mem_cons.mp hmem with heq | htail
      · cases heq; simp [lookupList]
      · have hkk : k' ≠ k := by
          intro h; apply hnotin; rw [h]
          exact List.mem_map.mpr ⟨(k, v), htail, rfl⟩
        simp only [lookupList, if_neg hkk]
        exact lookupList_eq_some_of_mem hndrest htail

/-! ## §1 — `SortedMap`: the sorted-nodup finite map + the CANONICAL-FORM theorem.

The invariant `(entries.map Prod.fst).Sorted (· < ·)` (strictly increasing keys) IMPLIES nodup keys
(`<` is irreflexive), so the entries list is the canonical form: `SortedMap.ext` proves two `SortedMap`s
with the same `lookup` are EQUAL. THIS is the reason for the representation — proved, not assumed. -/

/-- **`SortedMap K V`** — a sorted-nodup association list: `entries` whose keys are strictly increasing.
Strictly-increasing keys (`List.Pairwise (· < ·)`, the in-tree `Sorted` idiom — `NonMembership.lean:42`)
imply nodup keys, hence the canonical form. -/
structure SortedMap (K : Type u) (V : Type v) [LinearOrder K] where
  /-- The entries, sorted by strictly-increasing key. -/
  entries : List (K × V)
  /-- The invariant: keys strictly increasing (⇒ nodup keys ⇒ canonical). -/
  sortedKeys : (entries.map Prod.fst).Pairwise (· < ·)

namespace SortedMap

variable [LinearOrder K]

/-- `lookup m k` — the value at `k`, or `none`. -/
def lookup (m : SortedMap K V) (k : K) : Option V := lookupList k m.entries

/-- `get default m k` — the total read: the stored value, or the field's canonical `default`. -/
def get (default : V) (m : SortedMap K V) (k : K) : V := (m.lookup k).getD default

/-- The empty map. -/
def empty : SortedMap K V := ⟨[], by simp⟩

@[simp] theorem lookup_empty (k : K) : (empty : SortedMap K V).lookup k = none := rfl

/-- **`entries_ext` — the list-level canonical-form lemma.** Two strictly-key-sorted lists with the same
`lookupList` at every key are EQUAL. (Sorted ⇒ nodup keys ⇒ nodup pairs ⇒ equal lookups give equal
membership ⇒ permutation; both sorted ⇒ equal.) -/
theorem entries_ext {l l' : List (K × V)}
    (hs : (l.map Prod.fst).Pairwise (· < ·)) (hs' : (l'.map Prod.fst).Pairwise (· < ·))
    (h : ∀ k, lookupList k l = lookupList k l') : l = l' := by
  have hndk : (l.map Prod.fst).Nodup := hs.nodup
  have hndk' : (l'.map Prod.fst).Nodup := hs'.nodup
  -- same pair-membership (via the nodup-key `lookup`)
  have hmem : ∀ p : K × V, p ∈ l ↔ p ∈ l' := by
    rintro ⟨k, v⟩
    constructor
    · intro hp
      have h1 : lookupList k l = some v := lookupList_eq_some_of_mem hndk hp
      exact mem_of_lookupList_eq_some (by rw [← h k]; exact h1)
    · intro hp
      have h1 : lookupList k l' = some v := lookupList_eq_some_of_mem hndk' hp
      exact mem_of_lookupList_eq_some (by rw [h k]; exact h1)
  -- both strictly key-sorted + same membership ⇒ equal (`Pairwise.eq_of_mem_iff`)
  haveI : Std.Irrefl (fun a b : K × V => a.1 < b.1) := ⟨fun a => lt_irrefl a.1⟩
  have hp1 : l.Pairwise (fun a b => a.1 < b.1) := List.pairwise_map.mp hs
  have hp2 : l'.Pairwise (fun a b => a.1 < b.1) := List.pairwise_map.mp hs'
  exact List.Pairwise.eq_of_mem_iff hp1 hp2 hmem

/-- **`SortedMap.ext` — THE CANONICAL-FORM THEOREM.** Two `SortedMap`s with the same `lookup` are EQUAL.
The sorted-nodup representation is a canonical form: the map determines its entries. This is the load-bearing
reason for the representation (it makes "hash the entries" bind the map). PROVED. -/
@[ext] theorem ext {m m' : SortedMap K V} (h : ∀ k, m.lookup k = m'.lookup k) : m = m' := by
  obtain ⟨e, s⟩ := m
  obtain ⟨e', s'⟩ := m'
  have : e = e' := entries_ext s s' h
  subst this; rfl

/-! ### `insert` (reuses the sorted-insert discipline of `SortedTreeNonMembership.sortedInsert`, here on
`K × V` with OVERWRITE on an equal key). -/

/-- Insert/overwrite `(k, v)` into a key-sorted list, preserving order. -/
def insertList (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if k < k' then (k, v) :: (k', v') :: rest
      else if k = k' then (k, v) :: rest
      else (k', v') :: insertList k v rest

/-- The key set of an insert grows by exactly `k`. -/
theorem mem_keys_insertList (k : K) (v : V) (y : K) :
    ∀ l : List (K × V), y ∈ (insertList k v l).map Prod.fst ↔ y = k ∨ y ∈ l.map Prod.fst
  | [] => by simp [insertList]
  | (k', v') :: rest => by
      unfold insertList
      by_cases hlt : k < k'
      · simp only [hlt, if_true, List.map_cons, List.mem_cons]; tauto
      · rw [if_neg hlt]
        by_cases hkx : k = k'
        · rw [if_pos hkx, hkx]; simp only [List.map_cons, List.mem_cons]; tauto
        · rw [if_neg hkx]
          simp only [List.map_cons, List.mem_cons, mem_keys_insertList k v y rest]; tauto

/-- `insertList` preserves strictly-increasing keys. -/
theorem insertList_sorted (k : K) (v : V) :
    ∀ {l : List (K × V)}, (l.map Prod.fst).Pairwise (· < ·) →
      ((insertList k v l).map Prod.fst).Pairwise (· < ·)
  | [], _ => by simp [insertList]
  | (k', v') :: rest, hs => by
      have hstail : (rest.map Prod.fst).Sorted (· < ·) := (List.pairwise_cons.mp hs).2
      have hhead : ∀ y ∈ rest.map Prod.fst, k' < y := (List.pairwise_cons.mp hs).1
      unfold insertList
      by_cases hlt : k < k'
      · simp only [hlt, if_true, List.map_cons]
        refine List.pairwise_cons.mpr ⟨?_, hs⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hyt
        · exact hlt
        · exact hlt.trans (hhead y hyt)
      · rw [if_neg hlt]
        by_cases hkx : k = k'
        · rw [if_pos hkx]
          simp only [List.map_cons]
          refine List.pairwise_cons.mpr ⟨?_, hstail⟩
          intro y hy; rw [hkx]; exact hhead y hy
        · rw [if_neg hkx]
          have hxk : k' < k := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hkx h.symm)
          simp only [List.map_cons]
          refine List.pairwise_cons.mpr ⟨?_, insertList_sorted k v hstail⟩
          intro y hy
          rcases (mem_keys_insertList k v y rest).mp hy with rfl | hyt
          · exact hxk
          · exact hhead y hyt

/-- `insert k v m` — insert/overwrite, keeping the invariant. -/
def insert (m : SortedMap K V) (k : K) (v : V) : SortedMap K V :=
  ⟨insertList k v m.entries, insertList_sorted k v m.sortedKeys⟩

/-! ### `get_ext` — the CANONICAL (no-default-stored) bridge from `get` to `lookup`.

`get` (lookup-with-default) is injective on maps whose stored values never equal the default — the sparse
canonical form the deployed `BTreeMap` maintains (it does not store default/zero entries). This is the
HONEST content of "denote loses nothing": absence and a stored-default would denote identically, so the
faithful finite state forbids storing the default. `FinKernelState`'s value fields carry this via `CanonMap`. -/

/-- `Canonical default m` — no entry stores the field's `default` value (sparse/faithful form). -/
def Canonical (default : V) (m : SortedMap K V) : Prop := ∀ p ∈ m.entries, p.2 ≠ default

/-- **`get_ext`** — two `Canonical` maps with the same `get default` are EQUAL. The default-collision
(absent vs stored-default) is ruled out by `Canonical`, so `get`-agreement forces `lookup`-agreement. -/
theorem get_ext {default : V} {m m' : SortedMap K V}
    (hc : Canonical default m) (hc' : Canonical default m')
    (h : ∀ k, m.get default k = m'.get default k) : m = m' := by
  apply ext
  intro k
  have hk := h k
  simp only [get] at hk
  cases hml : m.lookup k with
  | none =>
      cases hml' : m'.lookup k with
      | none => rfl
      | some v' =>
          rw [hml, hml'] at hk
          simp only [Option.getD_none, Option.getD_some] at hk
          exact absurd hk (Ne.symm (hc' (k, v') (mem_of_lookupList_eq_some hml'))).symm
  | some v =>
      cases hml' : m'.lookup k with
      | none =>
          rw [hml, hml'] at hk
          simp only [Option.getD_none, Option.getD_some] at hk
          exact absurd hk (hc (k, v) (mem_of_lookupList_eq_some hml'.symm ▸ mem_of_lookupList_eq_some hml))
      | some v' =>
          rw [hml, hml'] at hk
          simp only [Option.getD_some] at hk
          rw [hml, hml', hk]

end SortedMap

/-! ## §2 — `CanonMap`: a `SortedMap` bundled with its no-default-stored proof.

Each function-valued `RecordKernelState` field has a canonical DEFAULT; the faithful finite model stores
NO entry at the default. `CanonMap K V d` bundles the map with that proof, giving an UNCONDITIONAL ext
(`CanonMap.ext`) that `denote_injective` uses field-wise. (The `delegate` field needs no `CanonMap`: its
`denote` is the raw `lookup`, already injective — `none ≠ some`.) -/

open SortedMap in
/-- A `SortedMap` in canonical (no-default-stored) form for default `d`. -/
structure CanonMap (K : Type u) (V : Type v) [LinearOrder K] (d : V) where
  /-- The underlying sorted map. -/
  toMap : SortedMap K V
  /-- No entry stores the default `d` (the sparse/faithful invariant). -/
  canon : SortedMap.Canonical d toMap

namespace CanonMap

variable [LinearOrder K] {d : V}

/-- The total read at the fixed default `d`. -/
def get (cm : CanonMap K V d) (k : K) : V := cm.toMap.get d k

/-- The empty canonical map. -/
def empty : CanonMap K V d := ⟨SortedMap.empty, by intro p hp; simp [SortedMap.empty] at hp⟩

@[simp] theorem get_empty (k : K) : (empty : CanonMap K V d).get k = d := rfl

/-- **`CanonMap.ext`** — two canonical maps (same default) with the same `get` are EQUAL. Unconditional
(the `Canonical` proofs are carried); the discharge of the default-collision. -/
theorem ext {a b : CanonMap K V d} (h : ∀ k, a.get k = b.get k) : a = b := by
  obtain ⟨ma, ca⟩ := a
  obtain ⟨mb, cb⟩ := b
  have : ma = mb := SortedMap.get_ext ca cb h
  subst this; rfl

end CanonMap

/-! ## §3 — `FinKernelState`: `RecordKernelState` with the 11 function-valued fields as finite maps.

The already-finite fields (`accounts`, `nullifiers`, `revoked`, `commitments`, `factories`) are carried
VERBATIM. `bal`'s two-level key `CellId → AssetId → ℤ` becomes a single `CellId ×ₗ AssetId` (lexicographic)
key. `delegate` (`CellId → Option CellId`) is a plain `SortedMap` (absence = `none`); the rest are `CanonMap`s
at their canonical defaults. -/

/-- The lexicographic product key type for `bal` (`CellId × AssetId`, canonically ordered). -/
abbrev BalKey : Type := CellId ×ₗ AssetId

/-- **`FinKernelState`** — the finite-map refinement of `RecordKernelState`. -/
@[ext] structure FinKernelState where
  /-- Live cells (verbatim). -/
  accounts : Finset CellId
  /-- Per-cell record state; default `.record []`. -/
  cell : CanonMap CellId Value (Value.record [])
  /-- Capability table (`Label → List Cap`); default `[]`. -/
  caps : CanonMap Label (List Cap) []
  /-- Spent-note nullifiers (verbatim). -/
  nullifiers : List Nat := []
  /-- Revocation registry (verbatim). -/
  revoked : List Nat := []
  /-- Note commitments (verbatim). -/
  commitments : List Nat := []
  /-- Per-(cell,asset) balance ledger; two-level key, default `0`. -/
  bal : CanonMap BalKey ℤ 0
  /-- Per-cell slot-caveat registry; default `[]`. -/
  slotCaveats : CanonMap CellId (List SlotCaveat) []
  /-- Factory registry (verbatim). -/
  factories : List (Nat × FactoryEntry) := []
  /-- Per-cell lifecycle discriminant; default `0` (Live). -/
  lifecycle : CanonMap CellId Nat 0
  /-- Per-cell death-certificate hash; default `0`. -/
  deathCert : CanonMap CellId Nat 0
  /-- Per-cell delegation parent pointer; absence = `none` (plain `SortedMap`, injective as-is). -/
  delegate : SortedMap CellId CellId
  /-- Per-cell delegation c-list snapshot; default `[]`. -/
  delegations : CanonMap CellId (List Cap) []
  /-- Per-cell delegation epoch; default `0`. -/
  delegationEpoch : CanonMap CellId Nat 0
  /-- Per-child snapshot-epoch stamp; default `0`. -/
  delegationEpochAt : CanonMap CellId Nat 0
  /-- Per-cell heap leaf list; default `[]`. -/
  heaps : CanonMap CellId (List (ℤ × ℤ)) []

/-! ## §4 — `denote`: the refinement `FinKernelState → RecordKernelState` (field-wise lookup-with-default). -/

/-- **`denote f`** — the total-function model of a finite kernel state: each finite field read as a total
function via lookup-with-default (`bal`/`delegate` per the two-level/`Option` shapes); the already-finite
fields identity. -/
def denote (f : FinKernelState) : RecordKernelState where
  accounts := f.accounts
  cell := fun c => f.cell.get c
  caps := fun l => f.caps.get l
  nullifiers := f.nullifiers
  revoked := f.revoked
  commitments := f.commitments
  bal := fun c a => f.bal.get (toLex (c, a))
  slotCaveats := fun c => f.slotCaveats.get c
  factories := f.factories
  lifecycle := fun c => f.lifecycle.get c
  deathCert := fun c => f.deathCert.get c
  delegate := fun c => f.delegate.lookup c
  delegations := fun c => f.delegations.get c
  delegationEpoch := fun c => f.delegationEpoch.get c
  delegationEpochAt := fun c => f.delegationEpochAt.get c
  heaps := fun c => f.heaps.get c

/-! ## §5 — `denote_injective`: THE LOAD-BEARING PROPERTY (hashing the finite state binds it, no loss). -/

/-- **`denote_injective` — THE LOAD-BEARING PROPERTY.** `denote f = denote f' → f = f'`. Equal denotations
⇒ equal per-field reads ⇒ (by `CanonMap.ext`/`SortedMap.ext`) equal finite maps ⇒ equal `FinKernelState`.
This is what makes "hash the `FinKernelState`" bind the abstract state with NO loss (the discharge target for
`RestHashIffFrame`). PROVED. -/
theorem denote_injective {f f' : FinKernelState} (h : denote f = denote f') : f = f' := by
  have hcell : ∀ c, f.cell.get c = f'.cell.get c := fun c => congrFun (congrArg RecordKernelState.cell h) c
  have hcaps : ∀ l, f.caps.get l = f'.caps.get l := fun l => congrFun (congrArg RecordKernelState.caps h) l
  have hbal : ∀ c a, f.bal.get (toLex (c, a)) = f'.bal.get (toLex (c, a)) := fun c a =>
    congrFun (congrFun (congrArg RecordKernelState.bal h) c) a
  have hslot : ∀ c, f.slotCaveats.get c = f'.slotCaveats.get c :=
    fun c => congrFun (congrArg RecordKernelState.slotCaveats h) c
  have hlife : ∀ c, f.lifecycle.get c = f'.lifecycle.get c :=
    fun c => congrFun (congrArg RecordKernelState.lifecycle h) c
  have hdeath : ∀ c, f.deathCert.get c = f'.deathCert.get c :=
    fun c => congrFun (congrArg RecordKernelState.deathCert h) c
  have hdel : ∀ c, f.delegate.lookup c = f'.delegate.lookup c :=
    fun c => congrFun (congrArg RecordKernelState.delegate h) c
  have hdels : ∀ c, f.delegations.get c = f'.delegations.get c :=
    fun c => congrFun (congrArg RecordKernelState.delegations h) c
  have hep : ∀ c, f.delegationEpoch.get c = f'.delegationEpoch.get c :=
    fun c => congrFun (congrArg RecordKernelState.delegationEpoch h) c
  have hepat : ∀ c, f.delegationEpochAt.get c = f'.delegationEpochAt.get c :=
    fun c => congrFun (congrArg RecordKernelState.delegationEpochAt h) c
  have hheaps : ∀ c, f.heaps.get c = f'.heaps.get c :=
    fun c => congrFun (congrArg RecordKernelState.heaps h) c
  ext1
  · exact congrArg RecordKernelState.accounts h
  · exact CanonMap.ext hcell
  · exact CanonMap.ext hcaps
  · exact congrArg RecordKernelState.nullifiers h
  · exact congrArg RecordKernelState.revoked h
  · exact congrArg RecordKernelState.commitments h
  · exact CanonMap.ext (fun key => by obtain ⟨c, a⟩ := key; exact hbal c a)
  · exact CanonMap.ext hslot
  · exact congrArg RecordKernelState.factories h
  · exact CanonMap.ext hlife
  · exact CanonMap.ext hdeath
  · exact SortedMap.ext hdel
  · exact CanonMap.ext hdels
  · exact CanonMap.ext hep
  · exact CanonMap.ext hepat
  · exact CanonMap.ext hheaps

/-! ## §6 — the initial state + `denote_finInit`. -/

/-- **`finInit`** — the empty finite kernel state (all maps empty; the already-finite fields empty). -/
def finInit : FinKernelState where
  accounts := ∅
  cell := CanonMap.empty
  caps := CanonMap.empty
  bal := CanonMap.empty
  slotCaveats := CanonMap.empty
  lifecycle := CanonMap.empty
  deathCert := CanonMap.empty
  delegate := SortedMap.empty
  delegations := CanonMap.empty
  delegationEpoch := CanonMap.empty
  delegationEpochAt := CanonMap.empty
  heaps := CanonMap.empty

/-- **`denote_finInit`** — `denote finInit` is the empty `RecordKernelState` (accounts `∅`, every total-field
its canonical default). Matches the field-default idiom used throughout `Exec/` (e.g. `kE0`). -/
theorem denote_finInit :
    denote finInit =
      ({ accounts := ∅
         cell := fun _ => Value.record []
         caps := fun _ => []
         nullifiers := []
         revoked := []
         commitments := []
         bal := fun _ _ => 0
         slotCaveats := fun _ => []
         factories := []
         lifecycle := fun _ => 0
         deathCert := fun _ => 0
         delegate := fun _ => none
         delegations := fun _ => []
         delegationEpoch := fun _ => 0
         delegationEpochAt := fun _ => 0
         heaps := fun _ => [] } : RecordKernelState) := by
  rfl

/-! ## §7 — THE SURJECTIVITY HONESTY GATE.

`denote` must be surjective onto reachable states, or a `FinKernelState` binding theorem is a new, smaller
vacuity. R1 owns EVERYTHING here except the per-effect commuting square, which enters as the EXPLICIT
hypothesis `hpres` — the interface lane R3 must DISCHARGE (`denote (finStep e f) = recStep e (denote f)`).
It is NOT assumed as a carrier and NOT left as a `def`. We prove the base case (`finInit`) and the inductive
lift GIVEN `hpres`. `finStep` is abstract here (R3 owns its construction). -/

section Reachability

variable {Eff : Type u}

/-- Fold a run of effects through the record-model step. -/
def recRun (recStep : Eff → RecordKernelState → RecordKernelState) :
    List Eff → RecordKernelState → RecordKernelState
  | [], s => s
  | e :: es, s => recRun recStep es (recStep e s)

/-- Fold a run of effects through the finite step. -/
def finRun (finStep : Eff → FinKernelState → FinKernelState) :
    List Eff → FinKernelState → FinKernelState
  | [], s => s
  | e :: es, s => finRun finStep es (finStep e s)

/-- A record-model state is REACHABLE from `init` if some effect run produces it. -/
def RecReachable (recStep : Eff → RecordKernelState → RecordKernelState)
    (init k : RecordKernelState) : Prop := ∃ es : List Eff, recRun recStep es init = k

/-- **The inductive lift.** GIVEN the per-effect commuting square `hpres` (R3's obligation), a whole finite
run denotes to the corresponding record run — the base case (`nil`) plus the step. -/
theorem denote_finRun
    (finStep : Eff → FinKernelState → FinKernelState)
    (recStep : Eff → RecordKernelState → RecordKernelState)
    (hpres : ∀ e f, denote (finStep e f) = recStep e (denote f)) :
    ∀ (es : List Eff) (f : FinKernelState),
      denote (finRun finStep es f) = recRun recStep es (denote f) := by
  intro es
  induction es with
  | nil => intro f; rfl
  | cons e es ih => intro f; simp only [finRun, recRun]; rw [ih (finStep e f), hpres]

/-- **`denote_surjective_on_reachable` — THE HONESTY GATE.** Every record-model state reachable from
`denote finInit` is a `denote` image. The base case (`finInit`) and the inductive lift are PROVED here; the
ONLY thing R1 does not own is the per-effect commuting square `hpres`, which is an EXPLICIT hypothesis for
lane R3 to discharge (never a carrier, never a `def`). -/
theorem denote_surjective_on_reachable
    (finStep : Eff → FinKernelState → FinKernelState)
    (recStep : Eff → RecordKernelState → RecordKernelState)
    (hpres : ∀ e f, denote (finStep e f) = recStep e (denote f))
    (k : RecordKernelState) (hr : RecReachable recStep (denote finInit) k) :
    ∃ f : FinKernelState, denote f = k := by
  obtain ⟨es, hes⟩ := hr
  exact ⟨finRun finStep es finInit, by rw [denote_finRun finStep recStep hpres]; exact hes⟩

end Reachability

/-! ## §8 — TEETH (`#guard`, both polarities). -/

section Teeth

/-- A concrete cell map: cell `1 ↦ record[("balance", 7)]`, cell `2 ↦ record[("balance", 9)]`. -/
private def demoCellEntries : List (CellId × Value) :=
  [(1, Value.record [("balance", Value.int 7)]), (2, Value.record [("balance", Value.int 9)])]

private def demoCell : CanonMap CellId Value (Value.record []) :=
  ⟨⟨demoCellEntries, by decide⟩, by decide⟩

-- `get default` returns the inserted value on PRESENT keys, the default on ABSENT keys:
#guard demoCell.get 1 == Value.record [("balance", Value.int 7)]   -- present
#guard demoCell.get 2 == Value.record [("balance", Value.int 9)]   -- present
#guard demoCell.get 3 == Value.record []                            -- absent ⇒ default

-- SortedMap.ext CANONICALITY: a PERMUTED-key list is NOT a valid `SortedMap` (the sorted invariant fails),
-- so the representation is canonical — there is exactly ONE valid entries list per key set.
#guard decide (([(2, (0:ℤ)), (1, 0)].map Prod.fst).Sorted (· < ·)) == false   -- permuted: INVALID
#guard decide (([(1, (0:ℤ)), (2, 0)].map Prod.fst).Sorted (· < ·)) == true     -- sorted: valid

-- A fresh `insert` adds the key; overwriting an existing key replaces the value (set grows by ≤ 1):
#guard (SortedMap.insert ⟨demoCellEntries, by decide⟩ 3 (Value.dig 5)).lookup 3 == some (Value.dig 5)
#guard (SortedMap.insert ⟨demoCellEntries, by decide⟩ 1 (Value.dig 5)).lookup 1 == some (Value.dig 5)

/-- Two concrete distinct `FinKernelState`s (differ only in `cell`). -/
private def fA : FinKernelState := { finInit with cell := demoCell }
private def fB : FinKernelState := finInit

/-- `denote_injective` bites: distinct finite states have distinct denotations (contrapositive witness —
`denote` does not collapse `fA` and `fB`). -/
private theorem demo_denote_distinct : denote fA ≠ denote fB := by
  intro h
  have := denote_injective h
  simp only [fA, fB] at this
  -- the `cell` fields differ (present key 1 vs default)
  have hc : demoCell.get 1 = (CanonMap.empty : CanonMap CellId Value (Value.record [])).get 1 := by
    have := congrArg (fun s => s.cell.get 1) this
    simpa using this
  simp [demoCell, CanonMap.get, SortedMap.get, SortedMap.lookup, lookupList, demoCellEntries,
    CanonMap.empty, SortedMap.empty] at hc

end Teeth

end Dregg2.Circuit.FinKernelState
