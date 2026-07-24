/-
# Dregg2.Circuit.MapOpWideKeyWeld — THE WELD the gate lane named and did not claim, plus the
  widened `ImtSorted`-preservation it unblocks.

`MapOpWideKeyGate` closed with two NAMED open items, in its own words:

  1. "This file's Merkle layer is the CONCRETE opening; `MapOpWideKey`'s `HoldsKindW` rides the
     ABSTRACT `Opens`. They are not yet connected — a `SpineCommitsW (opensToMerkleW …) r spine`
     bridge is one lemma and would make `insertW_absentW_jointly_unsat` bite directly on the gate
     rather than on the abstract denotation. I did not claim this weld; it is open."
  2. `ImtSorted`-preservation at the widened key THROUGH the gate (`imtInsert_preserves_digest8`
     composed with `aafiGatesW_force_imtAbsentW`), believed "blocked below IMT in the module DAG
     exactly as the narrow twin is".

Both are closed here.

## §A — THE WELD (item 1)

`opensAtW hash E dep r e` := "the leaf `e = (k, v)` opens at the depth-`dep` committed Merkle root
`r`", i.e. `opensToMerkleW hash E dep r e.1 (some e.2)`. `spineCommitsW_of_heap` DISCHARGES the
`SpineCommitsW` structure at that predicate from a committed sorted heap — the wrapper's crypto
residue ("a HYPOTHESIS, never an axiom") becomes a THEOREM at the concrete Merkle instantiation,
under the SAME named `Poseidon2SpongeCR` floor. Everything the abstract layer says about
`keysOfW` then transports, in both directions:

  * `absentGatesW_force_keysOfW_absence` — an ACCEPTING widened `.absent` gate forces
    `k ∉ keysOfW (opensAtW …) r`. The abstract non-membership target is now gate-forced.
  * `concrete_nonMembership_soundW` / `concrete_gap_forces_opensNone` — the abstract keystone
    `nonMembership_soundW` FIRES at the concrete predicate, and its conclusion transports BACK to
    the concrete `opensToMerkleW … none`.
  * `gates_force_holdsKindW_{absent,insert,aafiInsert}` — `MapOpWideKey.HoldsKindW` at the CONCRETE
    `Opens`, derived from gate acceptance.
  * `gates_insertW_absentW_jointly_unsat` and its `_via_abstract` twin — the design's blocker #1,
    re-derived so it bites on the EMITTED gate: two accepting widened rows (an insert of `k` and an
    `.absent` of the SAME 8-felt `k` at the resulting root) are jointly UNSAT under CR.

Honest labour report: "one lemma" was optimistic in the same way the gate lane's own estimate was.
The bridge itself is one lemma (`spineCommitsW_of_heap`); making the joint-unsat bite additionally
needed the two transport lemmas, the `Heap.set` growth/length bookkeeping
(`writesToMerkleW_forces_present`, `writesToMerkleW_forces_growth`) and the per-kind `HoldsKindW`
derivations — 9 supporting lemmas, no new mathematics.

★ A FINDING FELL OUT: `writesToMerkleW_forces_present`. At the map-tree layer the `.write` /
`.insert` / `.aafiInsert` denotation PINS the key already committed — `(Heap.set h k v).length =
2 ^ dep = h.length` is satisfiable only when `k ∈ Heap.keys h` (`Heap.length_set_fresh` grows the
heap by one otherwise). So the map-tree `.insert` kind is an in-place UPDATE; genuine fresh-key
GROWTH is the AAFI/IMT path (`AafiGatesAtW`), which is exactly the layer item 2 is about. That is
not a defect — it is why the two items are one piece of work.

## §B — `ImtSorted`-PRESERVATION AT THE WIDENED KEY (item 2)

The DAG blocker is an ARTIFACT, not real. `MapOpWideKeyGate` → `MapOpWideKey` →
`SortedTreeInsertWide8` → `Digest8KeySpike` → `IndexedMerkleTree`: `imtInsert`,
`imtInsert_preserves`, `imtInsert_preserves_digest8` and `imtAbsent_excludes_digest8` are ALL in
this file's import closure. The narrow twin (`IndexedMerkleTree.aafiGates_force_sortedKeys`) had to
live INSIDE `IndexedMerkleTree` because its input `MapOpsColumnLayout.aafiInsert_forces_imtInsert`
sits BELOW `imtInsert` in the DAG; the widened gate does not, because it was authored above both.
So the wide twin is available at its natural home and needs no re-placement:

  * `aafiGatesW_force_sortedChainW` — the widened twin, `ImtSorted (imtInsert c k v)` plus the
    `Heap.SortedKeys` projection at the 8-felt key.
  * `aafiGatesW_no_rewitnessW` — the chain-level double-spend refusal the preservation UNLOCKS: an
    AAFI-inserted key admits no subsequent pointer-bracket absence witness.
  * `aafiGatesW_post_chain_commitsW` — §A ∘ §B: the post-chain's forced sortedness is exactly the
    hypothesis the §A bridge consumes, so the AAFI insert side and the map-opening side are ONE
    object at the widened key.

## Non-vacuity

The gate lane's `demoAbsentGateW_accepts` (depth 1, arbitrary hash, every path obligation `rfl`) is
REUSED: `demoAbsentGateW_forces_keysOfW_absence` and `demo_concrete_excludes` derive the SAME
absence of `keyE` by two independent routes (emitted gate; abstract keystone) at the concrete
predicate. `demoInsertGateW_accepts` is a real ACCEPTING widened write row, and
`demoInsert_then_absent_unsat` REFUSES every `.absent` gate for its key at the post-root — the
double-spend witness at the concrete layer. `demoAafiGateW_accepts` is a real accepting widened AAFI
row over an arbitrary hash whose post-chain is `ImtSorted` and admits no re-witness.

## L3 (the canonically-keyed committed heap) — what moved here

`MapOpWideKeyGate.LaneEnc` now carries the ADMISSIBLE committed-heap shape as a field (`HeapOk`),
so every `Heap.SortedKeys h` premise in this file became `E.HeapOk h` — same statements at
`narrowEnc` (where `HeapOk` IS `SortedKeys`), strictly stronger at `wideEnc` (where it additionally
says the committed spine is canonically keyed). Two spots needed real work rather than a rename:

  * `writeW_then_absentW_unsat` now routes through `writesToMerkleW_forces_present` to learn that
    the written key is ALREADY on the spine, which is exactly what `heapOk_set` needs to carry
    admissibility across `Heap.set`. The file's own §A finding turned out to be the lemma its own
    L3 closure required.
  * `aafiGatesW_post_chain_commitsW` gained ONE hypothesis (`hc`: the post-chain's addresses are
    canonical) — the IMT layer's form of the same extraction premise, since the AAFI gate's bracket
    is a raw-order fact and cannot force it. `canonHeapW_imtToHeapW` / `heapOkW_imtToHeapW` are the
    bridge.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Crypto enters ONLY as the existing named
`Poseidon2SpongeCR` floor — NO new floor. Every import read-only; no
`sorry`/`admit`/`native_decide`. Nothing deployed is touched: no descriptor, no emit path, no JSON
face, no changed byte.
-/
import Dregg2.Circuit.MapOpWideKeyGate

namespace Dregg2.Circuit.MapOpWideKeyWeld

open Dregg2.Circuit.DescriptorIR2 (MapOpKind)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.MapMerkleRoot (mapNode perfectRoot)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs imtInsert
  imtSorted_addrs_sorted mem_imtAddrs_imtInsert)
open Dregg2.Crypto.NonMembership (Sorted Adjacent)
open Dregg2.Crypto.Digest8KeySpike (Digest8Key keyLo keyE keyHi keyLo_lt_keyE keyE_lt_keyHi
  keyLo_lt_keyHi spikeLeaves imtAbsent_excludes_digest8 imtInsert_preserves_digest8)
open Dregg2.Circuit.SortedTreeNonMembershipWide8 (keyOfW keysOfW keysOfW_eq_spine SpineCommitsW
  GapOpenW nonMembership_soundW proj0 lowfelt_collision)
open Dregg2.Circuit.MapOpWideKey (HoldsKindW KeyCanon)
open Dregg2.Circuit.MapOpWideKeyGate (LaneEnc wideEnc CanonHeapW heapOk_canon leafOfW mapRootW
  mapRootW_injective opensToMerkleW writesToMerkleW opensToMerkleW_some_excludes_none
  HoldsKindMerkleW ReconcileGatesW ReconcileGatesAtW reconcileGatesW_force_openingW aafiLeafHashW
  AafiGatesAtW aafiGatesW_force_imtAbsentW insertW_absentW_jointly_unsat
  insertW_absentW_jointly_unsat' demoHeapW demoHeapW_sorted demoHeapW_ok demoHeapW_length demoRootW
  demoAbsentGateW_accepts demoOpensW_keyLo)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false
-- `Heap.keys`/`imtAddrs` need no order; the order is in scope for the heap layer around them.
set_option linter.unusedSectionVars false

/-! ## §1 — THE WELD: the CONCRETE opening predicate, and `SpineCommitsW` DISCHARGED at it.

`SortedTreeNonMembershipWide8` left `Opens : Root → K × V → Prop` abstract on purpose ("its
realizing chip is the leaf-widening Rust re-emit"), and `MapOpWideKeyGate` built the CONCRETE
Merkle opening `opensToMerkleW` without connecting the two. This section connects them: the
abstract wrapper's `SpineCommitsW` — described there as "a HYPOTHESIS, never an axiom" — is a
THEOREM about a committed sorted heap, under the one named CR floor. -/

section Weld

variable {K : Type} [LinearOrder K]

/-- **`opensAtW hash E dep`** — the CONCRETE opening predicate: a leaf `e = (k, v)` "opens" at the
depth-`dep` committed binary-Merkle root `r` exactly when `opensToMerkleW` says the committed heap
reads `v` at `k`. This is the instantiation the abstract `Opens` was always a stand-in for; the
root type is the committed root felt `ℤ`. -/
def opensAtW (hash : List ℤ → ℤ) (E : LaneEnc K) (dep : Nat) : ℤ → K × ℤ → Prop :=
  fun r e => opensToMerkleW hash E dep r e.1 (some e.2)

/-- **★ THE WELD.** A committed sorted `2^dep`-leaf heap DISCHARGES the abstract wrapper's
`SpineCommitsW` at the concrete opening predicate: its key spine is the committed key spine, and a
leaf opens at `k` IFF `k` is on that spine. The forward direction is the anti-ghost
(`mapRootW_injective` — a second heap behind the same root IS the first heap); the backward
direction is `Heap.get_eq_none_iff`. This is the bridge `MapOpWideKeyGate` named and did not claim;
after it, every `keysOfW`/`nonMembership_soundW`/`HoldsKindW` statement is a statement about the
EMITTED gate's committed root, not about an abstract denotation. -/
theorem spineCommitsW_of_heap (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (E : LaneEnc K)
    (dep : Nat) (h : List (K × ℤ)) (hs : E.HeapOk h) (hlen : h.length = 2 ^ dep)
    {r : ℤ} (hroot : mapRootW hash E dep h = r) :
    SpineCommitsW (opensAtW hash E dep) r (Heap.keys h) := by
  refine ⟨E.heapOk_sorted h hs, fun k => ⟨?_, ?_⟩⟩
  · rintro ⟨e, he, hop⟩
    have he' : e.1 = k := he
    obtain ⟨h', hs', hlen', hroot', hget'⟩ := hop
    have hh : h' = h := mapRootW_injective hash hCR E dep hlen' hlen (hroot'.trans hroot.symm)
    have hgk : Heap.get h k = some e.2 := by rw [← hh, ← he']; exact hget'
    by_contra hk
    rw [(Heap.get_eq_none_iff h k).mpr hk] at hgk
    simp at hgk
  · intro hk
    cases hv : Heap.get h k with
    | none => exact absurd ((Heap.get_eq_none_iff h k).mp hv) (by simpa using hk)
    | some v => exact ⟨(k, v), rfl, ⟨h, hs, hlen, hroot, hv⟩⟩

/-- The committed key SET at the concrete predicate IS the heap's key spine. -/
theorem keysOfW_opensAtW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (E : LaneEnc K)
    (dep : Nat) (h : List (K × ℤ)) (hs : E.HeapOk h) (hlen : h.length = 2 ^ dep)
    {r : ℤ} (hroot : mapRootW hash E dep h = r) :
    ∀ k, k ∈ keysOfW (opensAtW hash E dep) r ↔ k ∈ Heap.keys h :=
  keysOfW_eq_spine (opensAtW hash E dep) r (Heap.keys h)
    (spineCommitsW_of_heap hash hCR E dep h hs hlen hroot)

/-- **Transport (⇐).** A CONCRETE non-membership opening is an ABSTRACT non-membership: nothing
opens at `k` under the committed root, so `k` is off the abstract committed key set. -/
theorem notMem_keysOfW_of_opensNone (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (dep : Nat) {r : ℤ} {k : K}
    (hnone : opensToMerkleW hash E dep r k none) : k ∉ keysOfW (opensAtW hash E dep) r := by
  rintro ⟨e, he, hop⟩
  have he' : e.1 = k := he
  have hop' : opensToMerkleW hash E dep r e.1 (some e.2) := hop
  rw [he'] at hop'
  exact opensToMerkleW_some_excludes_none hash hCR E dep hop' hnone

/-- **Transport (⇒), unconditional.** A concrete membership opening puts the key IN the abstract
committed set — no CR needed in this direction. -/
theorem mem_keysOfW_of_opensSome (hash : List ℤ → ℤ) (E : LaneEnc K) (dep : Nat) {r : ℤ} {k : K}
    {v : ℤ} (hsome : opensToMerkleW hash E dep r k (some v)) :
    k ∈ keysOfW (opensAtW hash E dep) r :=
  ⟨(k, v), rfl, hsome⟩

/-! ### §1a — the ABSTRACT KEYSTONE, fired at the CONCRETE predicate (both directions). -/

/-- **★ `nonMembership_soundW` AT THE CONCRETE INSTANTIATION.** The abstract wrapper's keystone
applies verbatim once the weld supplies `SpineCommitsW`: a covering-gap open against the committed
heap's key spine proves the key absent from the CONCRETE committed key set. Zero combinatorics
restated — the gap machinery never knew it was abstract. -/
theorem concrete_nonMembership_soundW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (dep : Nat) (h : List (K × ℤ)) (hs : E.HeapOk h)
    (hlen : h.length = 2 ^ dep) {r : ℤ} (hroot : mapRootW hash E dep h = r) (k : K)
    (g : GapOpenW (opensAtW hash E dep) r k) (hv : g.coversSpine (Heap.keys h)) :
    k ∉ keysOfW (opensAtW hash E dep) r :=
  nonMembership_soundW (opensAtW hash E dep) r k (Heap.keys h)
    (spineCommitsW_of_heap hash hCR E dep h hs hlen hroot) g hv

/-- **★ …AND ITS CONCLUSION TRANSPORTS BACK TO THE MERKLE LAYER.** The abstract gap witness yields
the CONCRETE `opensToMerkleW … none` — the object the widened AIR's `.absent` row denotes. So the
abstract wrapper is not a parallel universe: it decides the deployed opening. -/
theorem concrete_gap_forces_opensNone (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (dep : Nat) (h : List (K × ℤ)) (hs : E.HeapOk h)
    (hlen : h.length = 2 ^ dep) {r : ℤ} (hroot : mapRootW hash E dep h = r) (k : K)
    (g : GapOpenW (opensAtW hash E dep) r k) (hv : g.coversSpine (Heap.keys h)) :
    opensToMerkleW hash E dep r k none := by
  have hk := concrete_nonMembership_soundW hash hCR E dep h hs hlen hroot k g hv
  refine ⟨h, hs, hlen, hroot, (Heap.get_eq_none_iff h k).mpr ?_⟩
  intro hmem
  exact hk ((keysOfW_opensAtW hash hCR E dep h hs hlen hroot k).mpr hmem)

/-! ### §1b — THE GATE FORCES THE ABSTRACT DENOTATION (`HoldsKindW` at the concrete `Opens`). -/

/-- **★ AN ACCEPTING WIDENED `.absent` GATE FORCES ABSENCE FROM THE COMMITTED KEY SET.** The
emitted row's path obligations, through `reconcileGatesW_force_openingW` and the weld, land on
`k ∉ keysOfW` — the exact predicate `MapOpWideKey`'s `HoldsKindW`, `dosDelta_site20` and the whole
Wide8 wrapper layer speak in. Before the weld this held of an abstract `Opens`; now it holds of the
gate's own committed root. -/
theorem absentGatesW_force_keysOfW_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (dep : Nat) (r : ℤ) (k : K) (v r' : ℤ)
    (hg : ReconcileGatesAtW hash E dep r k v r' MapOpKind.absent) :
    k ∉ keysOfW (opensAtW hash E dep) r ∧ r' = r := by
  obtain ⟨hnone, hr⟩ :=
    reconcileGatesW_force_openingW hash hCR E dep r k v r' MapOpKind.absent hg
  exact ⟨notMem_keysOfW_of_opensNone hash hCR E dep hnone, hr⟩

/-- The `.absent` leg of `HoldsKindW`, at the CONCRETE opening predicate, forced by the gate.
(`MapOpWideKey.HoldsKindW` is pinned at `Digest8Key` — it is the widened denotation, not a generic
one — so this and its siblings live at `E : LaneEnc Digest8Key`; the lemmas they call are generic.) -/
theorem gates_force_holdsKindW_absent (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc Digest8Key) (dep : Nat) (r : ℤ) (k : Digest8Key) (v r' : ℤ)
    (hg : ReconcileGatesAtW hash E dep r k v r' MapOpKind.absent) :
    HoldsKindW (opensAtW hash E dep) r r' k v MapOpKind.absent :=
  absentGatesW_force_keysOfW_absence hash hCR E dep r k v r' hg

/-- The `.read` leg of `HoldsKindW`, at the CONCRETE opening predicate, forced by the gate. This
one is `reconcileGatesW_force_openingW` unchanged — `HoldsKindW`'s `.read` body IS
`opensAtW hash E dep pre (k, v) ∧ post = pre` definitionally, which is exactly what the widened
MapOps law already delivers. Recorded so the per-kind coverage of §1b is complete, not partial. -/
theorem gates_force_holdsKindW_read (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc Digest8Key) (dep : Nat) (r : ℤ) (k : Digest8Key) (v r' : ℤ)
    (hg : ReconcileGatesAtW hash E dep r k v r' MapOpKind.read) :
    HoldsKindW (opensAtW hash E dep) r r' k v MapOpKind.read :=
  reconcileGatesW_force_openingW hash hCR E dep r k v r' MapOpKind.read hg

/-- **★ THE FINDING: A MAP-TREE WRITE PINS ITS KEY ALREADY COMMITTED.** `writesToMerkleW` demands
the post-heap still hold `2 ^ dep` leaves; `Heap.length_set_fresh` grows an absent-key write by
exactly one leaf, so the only satisfiable case is `k ∈ Heap.keys h`. Consequence: at the MAP-TREE
layer the `.write` / `.insert` / `.aafiInsert` kinds denote an in-place UPDATE — genuine fresh-key
GROWTH lives at the AAFI/IMT layer (`AafiGatesAtW`, §3), where the free slot supplies the room.
This is a structural fact about the deployed denotation, surfaced by the weld, not a new
assumption. -/
theorem writesToMerkleW_forces_present (hash : List ℤ → ℤ) (E : LaneEnc K) (dep : Nat)
    {r : ℤ} {k : K} {v r' : ℤ} (hw : writesToMerkleW hash E dep r k v r') :
    ∃ h : List (K × ℤ), E.HeapOk h ∧ h.length = 2 ^ dep
      ∧ mapRootW hash E dep h = r ∧ k ∈ Heap.keys h
      ∧ r' = mapRootW hash E dep (Heap.set h k v) := by
  obtain ⟨h, hs, hlen, hlenset, hroot, hr'⟩ := hw
  refine ⟨h, hs, hlen, hroot, ?_, hr'⟩
  by_contra hk
  rw [Heap.length_set_fresh h k v hk, hlen] at hlenset
  exact Nat.succ_ne_self _ hlenset

/-- …hence the written key is a member of the CONCRETE committed key set BEFORE the write. -/
theorem writesToMerkleW_forces_keysOfW_membership (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (E : LaneEnc K) (dep : Nat) {r : ℤ} {k : K} {v r' : ℤ}
    (hw : writesToMerkleW hash E dep r k v r') : k ∈ keysOfW (opensAtW hash E dep) r := by
  obtain ⟨h, hs, hlen, hroot, hk, _⟩ := writesToMerkleW_forces_present hash E dep hw
  exact (keysOfW_opensAtW hash hCR E dep h hs hlen hroot k).mpr hk

/-- **★ THE WRITE LEG'S ABSTRACT DENOTATION, DERIVED.** After a widened write of `(k, v)` the
committed key set is the old one plus EXACTLY `k` — `MapOpWideKey.HoldsKindW`'s `.insert` body,
now a theorem about the concrete Merkle roots on both sides (`Heap.mem_keys_set_iff` through the
weld at BOTH the pre- and post-root). -/
theorem writesToMerkleW_forces_growth (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (dep : Nat) {r : ℤ} {k : K} {v r' : ℤ}
    (hw : writesToMerkleW hash E dep r k v r') :
    ∀ y, y ∈ keysOfW (opensAtW hash E dep) r'
      ↔ (y = k ∨ y ∈ keysOfW (opensAtW hash E dep) r) := by
  obtain ⟨h, hs, hlen, hroot, hk, hr'⟩ := writesToMerkleW_forces_present hash E dep hw
  have hlen' : (Heap.set h k v).length = 2 ^ dep := by
    rw [Heap.length_set_mem h k v (E.heapOk_sorted h hs) hk]; exact hlen
  have hbrPost := keysOfW_opensAtW hash hCR E dep (Heap.set h k v)
    (E.heapOk_set h k v hs hk) hlen' hr'.symm
  have hbrPre := keysOfW_opensAtW hash hCR E dep h hs hlen hroot
  intro y
  rw [hbrPost y, hbrPre y]
  exact Heap.mem_keys_set_iff h k y v

/-- The `.insert` leg of `HoldsKindW`, at the CONCRETE opening predicate, forced by the gate. -/
theorem gates_force_holdsKindW_insert (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc Digest8Key) (dep : Nat) (r : ℤ) (k : Digest8Key) (v r' : ℤ)
    (hg : ReconcileGatesAtW hash E dep r k v r' MapOpKind.insert) :
    HoldsKindW (opensAtW hash E dep) r r' k v MapOpKind.insert :=
  writesToMerkleW_forces_growth hash hCR E dep
    (reconcileGatesW_force_openingW hash hCR E dep r k v r' MapOpKind.insert hg)

/-- The `.aafiInsert` leg of `HoldsKindW`, at the CONCRETE opening predicate, forced by the gate. -/
theorem gates_force_holdsKindW_aafiInsert (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc Digest8Key) (dep : Nat) (r : ℤ) (k : Digest8Key) (v r' : ℤ)
    (hg : ReconcileGatesAtW hash E dep r k v r' MapOpKind.aafiInsert) :
    HoldsKindW (opensAtW hash E dep) r r' k v MapOpKind.aafiInsert :=
  writesToMerkleW_forces_growth hash hCR E dep
    (reconcileGatesW_force_openingW hash hCR E dep r k v r' MapOpKind.aafiInsert hg)

/-! ### §1c — BLOCKER #1, RE-DERIVED SO IT BITES ON THE GATE. -/

/-- The Merkle-layer core of the refusal: a write of `(k, v)` taking `r` to `r'` PRODUCES a
membership opening of `k` at `r'` (`Heap.get_set_self` on the post-heap the write commits), which
`opensToMerkleW_functional` cannot reconcile with a non-membership opening at the same root. -/
theorem writeW_then_absentW_unsat (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (dep : Nat) {r : ℤ} {k : K} {v r' : ℤ}
    (hw : writesToMerkleW hash E dep r k v r')
    (habs : opensToMerkleW hash E dep r' k none) : False := by
  obtain ⟨h, hs, hlen, hroot, hk, hr'⟩ := writesToMerkleW_forces_present hash E dep hw
  have hlenset : (Heap.set h k v).length = 2 ^ dep := by
    rw [Heap.length_set_mem h k v (E.heapOk_sorted h hs) hk]; exact hlen
  exact opensToMerkleW_some_excludes_none hash hCR E dep (v := v)
    ⟨Heap.set h k v, E.heapOk_set h k v hs hk, hlenset, hr'.symm, Heap.get_set_self h k v⟩ habs

/-- **★ THE DOUBLE-SPEND REFUSAL, ON THE EMITTED GATE (`.insert`).** Two ACCEPTING widened rows —
an `.insert` of the 8-felt key `k` moving `r` to `r'`, and an `.absent` of the SAME `k` against
`r'` — are jointly UNSAT under the single named CR floor. `MapOpWideKeyGate`'s
`insertW_absentW_jointly_unsat` said this of an abstract `Opens`; this says it of the gate. -/
theorem gates_insertW_absentW_jointly_unsat (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (dep : Nat) (r : ℤ) (k : K) (v r' v' : ℤ)
    (hins : ReconcileGatesAtW hash E dep r k v r' MapOpKind.insert)
    (habs : ReconcileGatesAtW hash E dep r' k v' r' MapOpKind.absent) : False :=
  writeW_then_absentW_unsat hash hCR E dep
    (reconcileGatesW_force_openingW hash hCR E dep r k v r' MapOpKind.insert hins)
    (reconcileGatesW_force_openingW hash hCR E dep r' k v' r' MapOpKind.absent habs).1

/-- The same, for the `.aafiInsert` kind. -/
theorem gates_aafiInsertW_absentW_jointly_unsat (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (E : LaneEnc K) (dep : Nat) (r : ℤ) (k : K) (v r' v' : ℤ)
    (hins : ReconcileGatesAtW hash E dep r k v r' MapOpKind.aafiInsert)
    (habs : ReconcileGatesAtW hash E dep r' k v' r' MapOpKind.absent) : False :=
  writeW_then_absentW_unsat hash hCR E dep
    (reconcileGatesW_force_openingW hash hCR E dep r k v r' MapOpKind.aafiInsert hins)
    (reconcileGatesW_force_openingW hash hCR E dep r' k v' r' MapOpKind.absent habs).1

/-- **★ THE SAME REFUSAL, ROUTED THROUGH THE ABSTRACT THEOREM.** The gate acceptances are turned
into `HoldsKindW` at the concrete `Opens` and handed to `MapOpWideKeyGate`'s ABSTRACT
`insertW_absentW_jointly_unsat` unchanged. This is the weld's whole point: the abstract blocker-#1
theorem is not a parallel statement, it is THIS one at a different instantiation — and the
instantiation is now inhabited by emitted rows. -/
theorem gates_jointly_unsat_via_abstract (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (r : ℤ) (k : Digest8Key) (v r' v' : ℤ)
    (hins : ReconcileGatesAtW hash wideEnc dep r k v r' MapOpKind.aafiInsert)
    (habs : ReconcileGatesAtW hash wideEnc dep r' k v' r' MapOpKind.absent) : False :=
  insertW_absentW_jointly_unsat (opensAtW hash wideEnc dep) r r' k v v'
    (gates_force_holdsKindW_aafiInsert hash hCR wideEnc dep r k v r' hins)
    (gates_force_holdsKindW_absent hash hCR wideEnc dep r' k v' r' habs)

/-- The `.insert` twin of `gates_jointly_unsat_via_abstract`. -/
theorem gates_jointly_unsat_via_abstract' (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (r : ℤ) (k : Digest8Key) (v r' v' : ℤ)
    (hins : ReconcileGatesAtW hash wideEnc dep r k v r' MapOpKind.insert)
    (habs : ReconcileGatesAtW hash wideEnc dep r' k v' r' MapOpKind.absent) : False :=
  insertW_absentW_jointly_unsat' (opensAtW hash wideEnc dep) r r' k v v'
    (gates_force_holdsKindW_insert hash hCR wideEnc dep r k v r' hins)
    (gates_force_holdsKindW_absent hash hCR wideEnc dep r' k v' r' habs)

end Weld

/-! ## §2 — NON-VACUITY AT THE CONCRETE LAYER: the gate lane's own accepting rows, welded.

Every witness below reuses `MapOpWideKeyGate`'s depth-1 committed heap `[(keyLo,1), (keyHi,2)]`
over an ARBITRARY hash, whose path obligations all close by `rfl`. -/

/-- **★ THE ABSTRACT `SpineCommitsW` HYPOTHESIS, DISCHARGED ON A CONCRETE COMMITTED ROOT.** The
committed spine is LITERALLY `Digest8KeySpike.spikeLeaves` — the same `[keyLo, keyHi]` the abstract
`demoOpens_spine` postulated. What was a hypothesis about an abstract predicate is now a theorem
about a real Merkle root. -/
theorem demoSpineCommitsW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    SpineCommitsW (opensAtW hash wideEnc 1) (demoRootW hash) spikeLeaves :=
  spineCommitsW_of_heap hash hCR wideEnc 1 demoHeapW demoHeapW_ok demoHeapW_length rfl

/-- The demo heap opens at the HIGH neighbour too (the second bracket leaf, for the gap witness). -/
theorem demoOpensW_keyHi (hash : List ℤ → ℤ) :
    opensToMerkleW hash wideEnc 1 (demoRootW hash) keyHi (some 2) :=
  ⟨demoHeapW, demoHeapW_ok, demoHeapW_length, rfl, by
    show Heap.get [(keyLo, (1 : ℤ)), (keyHi, (2 : ℤ))] keyHi = some 2
    rw [Heap.get_cons_ne (1 : ℤ) [(keyHi, (2 : ℤ))] keyLo_lt_keyHi.ne']
    exact Heap.get_cons_self keyHi 2 []⟩

/-- A REAL covering-gap open for `keyE` at the CONCRETE opening predicate: both neighbours are
genuine Merkle openings against the committed root, and the brackets are 8-limb lex compares
(`keyLo < keyE` decided at felt 7, `keyE < keyHi` at felt 0). -/
def demoGapW (hash : List ℤ → ℤ) : GapOpenW (opensAtW hash wideEnc 1) (demoRootW hash) keyE :=
  .inner (keyLo, 1) (keyHi, 2) (demoOpensW_keyLo hash) (demoOpensW_keyHi hash)
    keyLo_lt_keyE keyE_lt_keyHi

theorem demoGapW_covers (hash : List ℤ → ℤ) : (demoGapW hash).coversSpine spikeLeaves :=
  ⟨[], [], rfl⟩

/-- **★ ROUTE 1 — the ABSTRACT KEYSTONE fires on the CONCRETE root.** `nonMembership_soundW`,
instantiated at `opensAtW`, excludes `keyE` from the committed key set of a real Merkle root. -/
theorem demo_concrete_excludes (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    keyE ∉ keysOfW (opensAtW hash wideEnc 1) (demoRootW hash) :=
  concrete_nonMembership_soundW hash hCR wideEnc 1 demoHeapW demoHeapW_ok demoHeapW_length rfl
    keyE (demoGapW hash) (demoGapW_covers hash)

/-- **★ ROUTE 2 — the EMITTED GATE forces the SAME absence.** The gate lane's accepting
`.absent` row, pushed through the weld, lands on the identical statement. Two independent routes
(abstract gap keystone; emitted path gates) agreeing at one concrete instantiation. -/
theorem demoAbsentGateW_forces_keysOfW_absence (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) :
    keyE ∉ keysOfW (opensAtW hash wideEnc 1) (demoRootW hash) :=
  (absentGatesW_force_keysOfW_absence hash hCR wideEnc 1 (demoRootW hash) keyE 0 (demoRootW hash)
    (demoAbsentGateW_accepts hash)).1

/-- The gate lane's accepting `.absent` row also forces the FULL abstract `.absent` denotation at
the concrete predicate — `HoldsKindW`, no longer riding an abstract `Opens`. -/
theorem demoAbsentGateW_forces_holdsKindW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    HoldsKindW (opensAtW hash wideEnc 1) (demoRootW hash) (demoRootW hash) keyE 0
      MapOpKind.absent :=
  gates_force_holdsKindW_absent hash hCR wideEnc 1 (demoRootW hash) keyE 0 (demoRootW hash)
    (demoAbsentGateW_accepts hash)

/-! ### §2a — the CONCRETE DOUBLE-SPEND WITNESS: a real accepting write, and the refusal. -/

/-- The post-write committed heap: the same two keys, the low leaf's value updated. -/
def demoHeapW2 : List (Digest8Key × ℤ) := [(keyLo, 5), (keyHi, 2)]

theorem demoHeapW2_sorted : Heap.SortedKeys demoHeapW2 := demoHeapW_sorted

/-- The post-write heap has the SAME key spine as the pre-write one, so it is admissible for the
same reason: the L3 canonicity discipline costs the write side nothing either. -/
theorem demoHeapW2_ok : wideEnc.HeapOk demoHeapW2 := demoHeapW_ok

theorem demoHeapW2_length : demoHeapW2.length = 2 ^ 1 := rfl

/-- The post-write committed root. -/
noncomputable def demoRootW2 (hash : List ℤ → ℤ) : ℤ := mapRootW hash wideEnc 1 demoHeapW2

/-- **★ A REAL ACCEPTING WIDENED WRITE ROW.** The old leaf `(keyLo, 1)` and the new leaf
`(keyLo, 5)` recompute to the pre- and post-roots along the SAME sibling path; every obligation
closes by `rfl`, over an ARBITRARY hash. -/
theorem demoInsertGateW_accepts (hash : List ℤ → ℤ) :
    ReconcileGatesAtW hash wideEnc 1 (demoRootW hash) keyLo 5 (demoRootW2 hash)
      MapOpKind.insert :=
  ⟨demoHeapW, demoHeapW_ok, demoHeapW_length, rfl,
   [(false, leafOfW hash wideEnc (keyHi, 2))], 1, rfl, rfl, rfl⟩

/-- The post-root really commits the written key (the discrimination side of the refusal). -/
theorem demoRootW2_opens_keyLo (hash : List ℤ → ℤ) :
    opensToMerkleW hash wideEnc 1 (demoRootW2 hash) keyLo (some 5) :=
  ⟨demoHeapW2, demoHeapW2_ok, demoHeapW2_length, rfl, Heap.get_cons_self keyLo 5 [(keyHi, 2)]⟩

theorem demoRootW2_keyLo_in_keysOfW (hash : List ℤ → ℤ) :
    keyLo ∈ keysOfW (opensAtW hash wideEnc 1) (demoRootW2 hash) :=
  mem_keysOfW_of_opensSome hash wideEnc 1 (demoRootW2_opens_keyLo hash)

/-- **★ THE CONCRETE DOUBLE-SPEND REFUSAL.** Against the root that accepting write PRODUCED, NO
widened `.absent` gate for the written key can accept — for any claimed value, over an arbitrary
hash, under the one named CR floor. The witness pair is: an ACCEPTING insert row (above) and a
UNIVERSALLY REFUSED absent row (here). -/
theorem demoInsert_then_absent_unsat (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (v' : ℤ) :
    ¬ ReconcileGatesAtW hash wideEnc 1 (demoRootW2 hash) keyLo v' (demoRootW2 hash)
        MapOpKind.absent := fun habs =>
  gates_insertW_absentW_jointly_unsat hash hCR wideEnc 1 (demoRootW hash) keyLo 5
    (demoRootW2 hash) v' (demoInsertGateW_accepts hash) habs

/-- …and the same refusal routed through the ABSTRACT blocker-#1 theorem, so the abstract statement
is demonstrably inhabited by emitted rows rather than by a hypothesis. -/
theorem demoInsert_then_absent_unsat_via_abstract (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (v' : ℤ) :
    ¬ ReconcileGatesAtW hash wideEnc 1 (demoRootW2 hash) keyLo v' (demoRootW2 hash)
        MapOpKind.absent := fun habs =>
  gates_jointly_unsat_via_abstract' hash hCR 1 (demoRootW hash) keyLo 5 (demoRootW2 hash) v'
    (demoInsertGateW_accepts hash) habs

/-- **★ ANTI-DOS TOOTH — THE REFUSAL IS TARGETED, NOT BLANKET.** The SAME post-write root still
ACCEPTS a widened `.absent` gate for the genuinely-fresh 8-felt key `keyE` (bracket `keyLo < keyE`
decided at felt 7 — the limb the deployed projection discards). So `demoInsert_then_absent_unsat`
refuses the double spend, not absence proofs in general: the welded gate discriminates. -/
theorem demoAbsentGateW2_accepts (hash : List ℤ → ℤ) :
    ReconcileGatesAtW hash wideEnc 1 (demoRootW2 hash) keyE 0 (demoRootW2 hash)
      MapOpKind.absent :=
  ⟨demoHeapW2, demoHeapW2_ok, demoHeapW2_length, rfl,
   ⟨[(false, leafOfW hash wideEnc (keyHi, 2))], [(true, leafOfW hash wideEnc (keyLo, 5))],
    keyLo, 5, keyHi, 2, rfl, rfl, rfl, rfl, rfl, keyLo_lt_keyE, keyE_lt_keyHi⟩, rfl⟩

/-- …and it forces a genuine absence of `keyE` from the post-write committed key set. -/
theorem demoAbsentGateW2_forces_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    keyE ∉ keysOfW (opensAtW hash wideEnc 1) (demoRootW2 hash) :=
  (absentGatesW_force_keysOfW_absence hash hCR wideEnc 1 (demoRootW2 hash) keyE 0
    (demoRootW2 hash) (demoAbsentGateW2_accepts hash)).1

/-- **★ THE WAIST, ON THE WELDED ROWS.** The absent row (`keyE`, genuinely fresh at 8 felts) and
the written row (`keyLo`, present) carry the SAME value in the deployed one-felt key column: the
narrow gate decides both the same way, while the welded WIDE gate accepts the first and refuses the
second. That is kind-D's soundness delta, now stated about concrete Merkle roots. -/
theorem demoWeldedRows_indistinguishable_narrowly (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) :
    proj0 keyE = proj0 keyLo ∧ keyE ≠ keyLo
      ∧ keyE ∉ keysOfW (opensAtW hash wideEnc 1) (demoRootW hash)
      ∧ keyLo ∈ keysOfW (opensAtW hash wideEnc 1) (demoRootW2 hash) :=
  ⟨lowfelt_collision.1, lowfelt_collision.2, demo_concrete_excludes hash hCR,
   demoRootW2_keyLo_in_keysOfW hash⟩

/-! ## §3 — ITEM 2: `ImtSorted`-PRESERVATION AT THE WIDENED KEY, THROUGH THE GATE.

The gate lane recorded this as "blocked below IMT in the module DAG exactly as the narrow twin is".
That is an ARTIFACT of where the NARROW twin had to live, not a real constraint here: the narrow
composition had to sit inside `IndexedMerkleTree` because its input
(`MapOpsColumnLayout.aafiInsert_forces_imtInsert`) is BELOW `imtInsert` in the DAG. The widened
gate was authored ABOVE `IndexedMerkleTree` (this file's closure is
`MapOpWideKeyGate → MapOpWideKey → SortedTreeInsertWide8 → Digest8KeySpike → IndexedMerkleTree`),
so `imtInsert_preserves_digest8` and `aafiGatesW_force_imtAbsentW` are in scope TOGETHER and the
composition is one line at its natural home. -/

section ImtWide

variable {K : Type} [LinearOrder K] {V : Type}

/-- **`imtToHeapW`** — the widened twin of `IndexedMerkleTree.imtToHeap`: project the chain to its
openable `(addr, value)` map, dropping the pointer. Key-generic (the deployed `imtToHeap` is
`Heap.FeltHeap`-pinned, so it cannot be reused at `K := Digest8Key`). -/
def imtToHeapW (c : List (ImtLeaf K V)) : List (K × V) :=
  c.map (fun l => (l.addr, l.value))

theorem keys_imtToHeapW (c : List (ImtLeaf K V)) : Heap.keys (imtToHeapW c) = imtAddrs c := by
  simp [Heap.keys, imtToHeapW, imtAddrs, List.map_map, Function.comp]

/-- An `ImtSorted` chain at ANY key width projects to a `Heap.SortedKeys` map. -/
theorem imtSortedW_sortedKeys {c : List (ImtLeaf K V)} (hs : ImtSorted c) :
    Heap.SortedKeys (imtToHeapW c) := by
  rw [Heap.SortedKeys, keys_imtToHeapW]
  exact imtSorted_addrs_sorted hs

end ImtWide

/-- The IMT-layer form of the L3 discipline: a chain whose ADDRESSES are canonical projects to a
canonically-keyed heap. (Chain-address canonicity is the IMT layer's extraction premise, exactly as
`wideEnc.HeapOk` is the map layer's — the AAFI gate's bracket is a raw-order fact and cannot force
it, `MapOpWideKeyCanonDischarge.gate_teeth_cannot_force_canonicity`.) -/
theorem canonHeapW_imtToHeapW {c : List (ImtLeaf Digest8Key ℤ)}
    (hc : ∀ x ∈ imtAddrs c, KeyCanon (ofLex x)) : CanonHeapW (imtToHeapW c) := by
  intro k hk
  rw [keys_imtToHeapW] at hk
  exact hc k hk

/-- …hence an `ImtSorted`, canonically-addressed chain projects to an ADMISSIBLE wide heap. -/
theorem heapOkW_imtToHeapW {c : List (ImtLeaf Digest8Key ℤ)} (hs : ImtSorted c)
    (hc : ∀ x ∈ imtAddrs c, KeyCanon (ofLex x)) : wideEnc.HeapOk (imtToHeapW c) :=
  ⟨imtSortedW_sortedKeys hs, canonHeapW_imtToHeapW hc⟩

/-- **★ ITEM 2 — THE WIDENED GATE PRESERVES THE SORTED CHAIN.** The widened twin of
`IndexedMerkleTree.aafiGates_force_sortedKeys`: on an `ImtSorted` pre-chain, an ACCEPTING widened
AAFI row whose opened arity-17 low leaf is in the chain yields (i) an `ImtSorted` POST-chain at the
FULL 8-felt key and (ii) its `Heap.SortedKeys` projection. The `ImtAbsent` premise
`imtInsert_preserves_digest8` needs is GATE-FORCED (`aafiGatesW_force_imtAbsentW`, whose bracket is
the emitted 8-limb lex compare), never assumed. -/
theorem aafiGatesW_force_sortedChainW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {oldRoot newRoot : ℤ} {k : Digest8Key} {v : ℤ} {lowAddr : Digest8Key}
    {lowValue : ℤ} {lowNext : Digest8Key} {freeEmpty : ℤ} {c : List (ImtLeaf Digest8Key ℤ)}
    (hs : ImtSorted c)
    (hg : AafiGatesAtW hash dep oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    ImtSorted (imtInsert c k v) ∧ Heap.SortedKeys (imtToHeapW (imtInsert c k v)) := by
  have hpost : ImtSorted (imtInsert c k v) :=
    imtInsert_preserves_digest8 hs (aafiGatesW_force_imtAbsentW hash hCR dep hg hlow)
  exact ⟨hpost, imtSortedW_sortedKeys hpost⟩

/-- **★ THE WIDENED SPINE GROWS BY EXACTLY THE 8-FELT KEY.** `mem_imtAddrs_imtInsert` (key-generic,
composed not re-derived) on the gate-forced `ImtAbsent`: no ghost addresses, no lost addresses. -/
theorem aafiGatesW_force_spine_growthW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {oldRoot newRoot : ℤ} {k : Digest8Key} {v : ℤ} {lowAddr : Digest8Key}
    {lowValue : ℤ} {lowNext : Digest8Key} {freeEmpty : ℤ} {c : List (ImtLeaf Digest8Key ℤ)}
    (hg : AafiGatesAtW hash dep oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    ∀ x, x ∈ imtAddrs (imtInsert c k v) ↔ x = k ∨ x ∈ imtAddrs c :=
  mem_imtAddrs_imtInsert (aafiGatesW_force_imtAbsentW hash hCR dep hg hlow)

/-- **★ NO RE-WITNESS AT THE WIDENED KEY — the chain-level double-spend refusal.** After an
accepting widened AAFI insert of `k`, NO pointer-bracket absence witness for `k` exists against the
post-chain. This statement is only available BECAUSE of item 2: `imtAbsent_excludes_digest8`
consumes `ImtSorted` of the POST-chain, which is exactly what
`aafiGatesW_force_sortedChainW` supplies. -/
theorem aafiGatesW_no_rewitnessW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {oldRoot newRoot : ℤ} {k : Digest8Key} {v : ℤ} {lowAddr : Digest8Key} {lowValue : ℤ}
    {lowNext : Digest8Key} {freeEmpty : ℤ} {c : List (ImtLeaf Digest8Key ℤ)}
    (hs : ImtSorted c)
    (hg : AafiGatesAtW hash dep oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    ¬ ImtAbsent (imtInsert c k v) k := by
  intro hre
  have hpost := (aafiGatesW_force_sortedChainW hash hCR dep hs hg hlow).1
  have hgrow := aafiGatesW_force_spine_growthW hash hCR dep hg hlow
  exact imtAbsent_excludes_digest8 hpost hre ((hgrow k).mpr (Or.inl rfl))

/-- **★ §1 ∘ §3 — THE POST-CHAIN IS A COMMITTABLE WIDENED MAP.** The sortedness item 2 FORCES is
precisely the hypothesis the §1 weld consumes, so the AAFI insert side and the map-opening side are
ONE object at the widened key: the post-chain's projection, committed at a widened map root,
discharges `SpineCommitsW` with the chain's own address spine. Neither half is assumed. -/
theorem aafiGatesW_post_chain_commitsW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep d : Nat) {oldRoot newRoot : ℤ} {k : Digest8Key} {v : ℤ} {lowAddr : Digest8Key}
    {lowValue : ℤ} {lowNext : Digest8Key} {freeEmpty : ℤ} {c : List (ImtLeaf Digest8Key ℤ)}
    (hs : ImtSorted c)
    (hg : AafiGatesAtW hash dep oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c)
    (hlen : (imtToHeapW (imtInsert c k v)).length = 2 ^ d)
    (hc : ∀ x ∈ imtAddrs (imtInsert c k v), KeyCanon (ofLex x)) :
    SpineCommitsW (opensAtW hash wideEnc d)
      (mapRootW hash wideEnc d (imtToHeapW (imtInsert c k v))) (imtAddrs (imtInsert c k v)) := by
  have hsk := (aafiGatesW_force_sortedChainW hash hCR dep hs hg hlow).1
  have hb := spineCommitsW_of_heap hash hCR wideEnc d (imtToHeapW (imtInsert c k v))
    (heapOkW_imtToHeapW hsk hc) hlen rfl
  rwa [keys_imtToHeapW] at hb

/-! ### §3a — NON-VACUITY for item 2: a REAL accepting widened AAFI row at depth 1. -/

/-- The committed widened chain: one leaf `keyLo → keyHi`, `ImtSorted` at the 8-felt lex order. -/
def demoAafiChainW : List (ImtLeaf Digest8Key ℤ) := [⟨keyLo, 1, keyHi⟩]

theorem demoAafiChainW_sorted : ImtSorted demoAafiChainW := keyLo_lt_keyHi

theorem demoAafiChainW_low_mem :
    (⟨keyLo, 1, keyHi⟩ : ImtLeaf Digest8Key ℤ) ∈ demoAafiChainW := by
  simp [demoAafiChainW]

/-- The committed pre-root: the arity-17 low leaf in slot 0, the empty free slot in slot 1. -/
def demoAafiOldRootW (hash : List ℤ → ℤ) : ℤ :=
  perfectRoot hash 1 [aafiLeafHashW hash keyLo 1 keyHi, 0]

/-- The intermediate root after the low leaf's pointer is repointed at `keyE`. -/
def demoAafiR1W (hash : List ℤ → ℤ) : ℤ := mapNode hash (aafiLeafHashW hash keyLo 1 keyE) 0

/-- The post-root after the appended `keyE` leaf lands in the free slot. -/
def demoAafiNewRootW (hash : List ℤ → ℤ) : ℤ :=
  mapNode hash (aafiLeafHashW hash keyLo 1 keyE) (aafiLeafHashW hash keyE 7 keyHi)

/-- The two AAFI slots are DISTINCT positions (gate (d)'s `pathPos steps1 ≠ pathPos steps2`): the
low leaf sits at leaf 0, the free slot at leaf 1, whatever the siblings carry. -/
theorem demoAafi_pos_ne (x : ℤ) : pathPos [(false, (0 : ℤ))] ≠ pathPos [(true, x)] := by
  show (0 : Nat) ≠ 1
  decide

/-- **★ A REAL ACCEPTING WIDENED AAFI ROW.** Depth 1, two distinct slots, the arity-17 leaf schema,
the 8-felt pointer bracket `keyLo < keyE < keyHi` (decided at felts 7 and 0), over an ARBITRARY
hash — every path obligation `rfl`. -/
theorem demoAafiGateW_accepts (hash : List ℤ → ℤ) :
    AafiGatesAtW hash 1 (demoAafiOldRootW hash) (demoAafiNewRootW hash) keyE 7 keyLo 1 keyHi 0 :=
  ⟨demoAafiR1W hash, [aafiLeafHashW hash keyLo 1 keyHi, 0], [(false, 0)],
   [(true, aafiLeafHashW hash keyLo 1 keyE)], rfl, rfl, rfl,
   demoAafi_pos_ne (aafiLeafHashW hash keyLo 1 keyE), rfl, rfl,
   keyLo_lt_keyE, keyE_lt_keyHi, rfl, rfl, rfl⟩

/-- The accepting row FORCES the widened pointer-bracket absence of `keyE` from the pre-chain. -/
theorem demoAafiGateW_forces_absentW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ImtAbsent demoAafiChainW keyE :=
  aafiGatesW_force_imtAbsentW hash hCR 1 (demoAafiGateW_accepts hash) demoAafiChainW_low_mem

/-- **★ ITEM 2, FIRING ON A CONCRETE ACCEPTING ROW.** The post-chain is `ImtSorted` at the 8-felt
key and projects to a `Heap.SortedKeys` map — the widened preservation, gate-forced. -/
theorem demoAafiGateW_preserves_sortedW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ImtSorted (imtInsert demoAafiChainW keyE 7)
      ∧ Heap.SortedKeys (imtToHeapW (imtInsert demoAafiChainW keyE 7)) :=
  aafiGatesW_force_sortedChainW hash hCR 1 demoAafiChainW_sorted (demoAafiGateW_accepts hash)
    demoAafiChainW_low_mem

/-- **★ THE CHAIN-LEVEL DOUBLE-SPEND REFUSAL, CONCRETE.** After that accepting insert, `keyE`
admits NO pointer-bracket absence witness against the post-chain. -/
theorem demoAafiGateW_no_rewitnessW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ¬ ImtAbsent (imtInsert demoAafiChainW keyE 7) keyE :=
  aafiGatesW_no_rewitnessW hash hCR 1 demoAafiChainW_sorted (demoAafiGateW_accepts hash)
    demoAafiChainW_low_mem

/-- …and the widened spine grew by EXACTLY `keyE`. -/
theorem demoAafiGateW_spine_growthW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ x, x ∈ imtAddrs (imtInsert demoAafiChainW keyE 7) ↔ x = keyE ∨ x ∈ imtAddrs demoAafiChainW :=
  aafiGatesW_force_spine_growthW hash hCR 1 (demoAafiGateW_accepts hash) demoAafiChainW_low_mem

/-! ## §4 — axiom hygiene: every keystone rests on the kernel triple only, and on the SINGLE
existing named `Poseidon2SpongeCR` floor. No new floor was introduced. -/

#assert_axioms spineCommitsW_of_heap
#assert_axioms keysOfW_opensAtW
#assert_axioms notMem_keysOfW_of_opensNone
#assert_axioms mem_keysOfW_of_opensSome
#assert_axioms concrete_nonMembership_soundW
#assert_axioms concrete_gap_forces_opensNone
#assert_axioms absentGatesW_force_keysOfW_absence
#assert_axioms gates_force_holdsKindW_absent
#assert_axioms gates_force_holdsKindW_read
#assert_axioms writesToMerkleW_forces_present
#assert_axioms writesToMerkleW_forces_keysOfW_membership
#assert_axioms writesToMerkleW_forces_growth
#assert_axioms gates_force_holdsKindW_insert
#assert_axioms gates_force_holdsKindW_aafiInsert
#assert_axioms writeW_then_absentW_unsat
#assert_axioms gates_insertW_absentW_jointly_unsat
#assert_axioms gates_aafiInsertW_absentW_jointly_unsat
#assert_axioms gates_jointly_unsat_via_abstract
#assert_axioms gates_jointly_unsat_via_abstract'
#assert_axioms demoSpineCommitsW
#assert_axioms demoOpensW_keyHi
#assert_axioms demoGapW_covers
#assert_axioms demo_concrete_excludes
#assert_axioms demoAbsentGateW_forces_keysOfW_absence
#assert_axioms demoAbsentGateW_forces_holdsKindW
#assert_axioms demoInsertGateW_accepts
#assert_axioms demoRootW2_opens_keyLo
#assert_axioms demoRootW2_keyLo_in_keysOfW
#assert_axioms demoInsert_then_absent_unsat
#assert_axioms demoInsert_then_absent_unsat_via_abstract
#assert_axioms demoAbsentGateW2_accepts
#assert_axioms demoAbsentGateW2_forces_absence
#assert_axioms demoWeldedRows_indistinguishable_narrowly
#assert_axioms demoHeapW2_ok
#assert_axioms keys_imtToHeapW
#assert_axioms imtSortedW_sortedKeys
#assert_axioms canonHeapW_imtToHeapW
#assert_axioms heapOkW_imtToHeapW
#assert_axioms aafiGatesW_force_sortedChainW
#assert_axioms aafiGatesW_force_spine_growthW
#assert_axioms aafiGatesW_no_rewitnessW
#assert_axioms aafiGatesW_post_chain_commitsW
#assert_axioms demoAafiGateW_accepts
#assert_axioms demoAafiGateW_forces_absentW
#assert_axioms demoAafiGateW_preserves_sortedW
#assert_axioms demoAafiGateW_no_rewitnessW
#assert_axioms demoAafiGateW_spine_growthW

end Dregg2.Circuit.MapOpWideKeyWeld
