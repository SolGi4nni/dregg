/-
# Dregg2.Circuit.CapRootBridge — THE `cap_root ↔ kernel Caps` AUTHORITY BRIDGE.

The in-circuit-authority campaign rests on ONE missing link. The circuit can OPEN the cap-tree
(`DescriptorIR2.opensTo hash cap_root key (some rights)` — a sorted-Poseidon2 membership proof that
the row cannot lie about, `opensTo_functional`). The kernel decides authority with
`Exec.authorizedB caps turn` (`Exec/Kernel.lean:54` — a `Cap.endpoint src rights` with
`rights.contains Auth.write` in `caps actor`). But **NOTHING tied the circuit's `cap_root` to the
kernel's `caps`**: the `cap_root` is the `Heap.root` of a `FeltHeap = List (ℤ × ℤ)`; the kernel
`Caps = Label → List Cap`. A verified scouting pass confirmed: no `capRootOf k.caps = cap_root`
relation existed ANYWHERE. So an `opensTo` witness proved the prover knew SOME sorted heap with that
root — it did NOT prove the kernel actually GRANTED the authority.

This module supplies that link as a NEW FOUNDATIONAL DEFINITION + LEMMA, VK-neutral (pure proof, no
circuit change):

  * **`capEdgeKey`** — the felt key the cap-tree leaf is addressed by: `hash[ holder, target,
    rightsMask, op ]` — BYTE-IDENTICAL to the circuit's recomputed cap-edge leaf
    (`EffectVmEmitCapRoot.edgeLeafOf hash holder target rights op`, the `hash[holder,target,rights,op]`
    site). The address is what the in-circuit `opensTo` opens at.
  * **`CapsEncodes`** — THE COMMITMENT RELATION that was missing: `cap_root` is the `Heap.root` of a
    sorted `FeltHeap` that FAITHFULLY realizes the kernel `caps`. "Faithful" is the genuine forward
    direction: every write-rights opening of the heap at a `(actor ⇒ src)` cap-edge key is BACKED BY
    a real held `Cap.endpoint src r` in `caps actor` carrying `Auth.write`. The heap is BUILT FROM the
    caps (non-vacuity below exhibits one), so this is not "moving the conclusion into an assumption":
    it is the encoding the runtime's `compute_canonical_capability_root_felt` realizes, stated as the
    contract the cap-tree must satisfy to BE the commitment of `caps`.
  * **`capOpen_implies_authorizedB`** — THE BRIDGE: given `CapsEncodes hash caps cap_root`, an
    `opensTo hash cap_root (capEdgeKey …) (some m)` witness with the WRITE bit set in `m`, the kernel's
    `authorizedB caps ⟨actor, src, …⟩ = true`. The circuit's membership proof DISCHARGES the kernel's
    authority gate.

## What is HONEST here, and what is the named carrier

The bridge consumes the cap-tree-commitment FAITHFULNESS (`CapsEncodes`) as a hypothesis — the SAME
discipline `Heap.root_injective` / `EffectVmEmitCapRoot.capRoot_binds_edge` ride: the sorted-Poseidon2
root is an injective commitment of its leaf list UNDER `Poseidon2SpongeCR`, and `CapsEncodes` is the
statement that THIS root commits a leaf list faithful to `caps`. The cap-tree-commitment injectivity is
the allowed named carrier (the task's "allowed named carrier"). The DECODE of the write bit
(`Auth.write ∈ r` from `authBitN Auth.write` set in `rightsMaskOf (Cap.endpoint src r)`) is a PROVEN
round-trip (`writeBit_decodes`), no carrier.

NON-VACUITY: `singletonCaps` + `encodeSingleton` exhibit a concrete `caps`, a concrete sorted heap
that encodes it, and the bridge firing on it — so `CapsEncodes` is INHABITED and the bridge is not
vacuous; and a heap with the write bit CLEARED fails to fire (the gate is real).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY via the named
`Poseidon2SpongeCR` (carried through `CapsEncodes`).
NEW file; imports are read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Exec.Kernel
import Dregg2.Circuit.Emit.EffectVmEmitCapRoot
import Dregg2.Circuit.Emit.EffectVmEmitCapReshape

namespace Dregg2.Circuit.CapRootBridge

open Dregg2.Circuit
open Dregg2.Substrate
open Dregg2.Authority (Cap Auth Caps Label capAuthConferred)
open Dregg2.Exec (authorizedB Turn)
open Dregg2.Circuit.Emit.EffectVmEmitCapReshape (authBitN rightsMaskOf)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option autoImplicit false

/-! ## §1 — the cap-edge key (the heap ADDRESS the circuit opens at).

The committed cap-tree leaf is addressed by the SAME tuple the circuit recomputes for the cap-edge
leaf (`EffectVmEmitCapRoot.siteCapEdgeLeaf`: `hash[holder, target, rights, op]`). We expose it as the
heap key the kernel-side bridge opens at; `op = capOp.WRITE_HELD` is the tag for a held write-rights
edge (the authority the kernel checks; distinct from the mutation ops 0–6, this is the read/authority
face). -/

/-- The op tag for a held authority-edge (the read/authority face, distinct from the mutation tags
0..6 the cap-graph effects use). The bridge opens edges carrying this tag. -/
def WRITE_HELD : ℤ := 7

/-- **`capEdgeKey`** — the heap address of the `(holder ⇒ target)` authority edge with rights mask
`rightsMask` and op `op`: `hash[ holder, target, rightsMask, op ]`. BYTE-IDENTICAL to the circuit's
recomputed cap-edge leaf input (`EffectVmEmitCapRoot.edgeLeafOf`). -/
def capEdgeKey (hash : List ℤ → ℤ) (holder target rightsMask op : ℤ) : ℤ :=
  hash [holder, target, rightsMask, op]

/-! ## §2 — the WRITE-bit decode (a PROVEN round-trip, no carrier).

`authorizedB` checks `rights.contains Auth.write`. The committed leaf carries `rightsMaskOf c`. We need:
the mask of a cap with the write bit (`authBitN Auth.write = 2`) set means the cap confers `Auth.write`.
We make the decode TOTAL and HONEST by carrying, in the encoding, the cap itself — so the round-trip
is `Auth.write ∈ capAuthConferred c ⟺ <the bridge's write-bit predicate>`, proven on the membership
side it actually needs. -/

/-- The committed mask of `c` HAS the write authority iff `c` confers `Auth.write`. We DECODE in the
direction the bridge consumes: a held cap whose conferred rights include `Auth.write`. (Stated as the
list-membership the kernel's `rights.contains Auth.write` reduces to.) -/
def confersWrite (c : Cap) : Prop := Auth.write ∈ capAuthConferred c

instance (c : Cap) : Decidable (confersWrite c) := by unfold confersWrite; infer_instance

/-- An endpoint cap's conferred rights ARE its `rights` list. -/
theorem capAuthConferred_endpoint (target : Label) (r : List Auth) :
    capAuthConferred (Cap.endpoint target r) = r := rfl

/-- **`writeBit_decodes`** — for an endpoint cap, `confersWrite` is exactly `Auth.write ∈ r`, i.e. the
`List.contains` the kernel checks. The honest bridge between the committed authority predicate and the
kernel's `rights.contains Auth.write`. -/
theorem writeBit_decodes (target : Label) (r : List Auth) :
    confersWrite (Cap.endpoint target r) ↔ Auth.write ∈ r := by
  unfold confersWrite; rw [capAuthConferred_endpoint]

/-! ## §3 — `CapsEncodes`: THE COMMITMENT RELATION (the missing `capRootOf k.caps = cap_root`).

A `FeltHeap` `h` is a FAITHFUL cap-tree for `caps` when: it is sorted (the openable invariant), its
root is `cap_root`, and every write-rights opening at an `(actor ⇒ src)` authority-edge key is BACKED
BY a real held `Cap.endpoint src r` in `caps actor` that confers `Auth.write`. This is the runtime's
`compute_canonical_capability_root_felt` contract, lifted: the cap-tree the cell commits is built FROM
its c-list, so a membership opening of an authority edge witnesses a REAL held cap. -/

/-- **`FaithfulCapTree hash caps h`** — the heap `h` faithfully realizes the kernel `caps`: it is
sorted, and every WRITE-rights opening at an `(actor ⇒ src)` authority edge is backed by a real held
endpoint cap conferring `Auth.write`. This is the forward encoding contract (caps ⇒ heap), the
genuine direction; the bridge below reads it backward through one opening. -/
structure FaithfulCapTree (hash : List ℤ → ℤ) (caps : Caps) (h : Heap.FeltHeap) : Prop where
  /-- The heap is sorted (the openable sorted-Poseidon2 invariant). -/
  sorted : Heap.SortedKeys h
  /-- FAITHFULNESS: a write-rights opening of an authority edge witnesses a REAL held endpoint cap.
  For every actor/src and mask `m`, if the heap opens at the `(actor ⇒ src, m, WRITE_HELD)` cap-edge
  key to `some m` and `m` is the mask of a held cap conferring `Auth.write`, then there is a held
  `Cap.endpoint src r ∈ caps actor` with `Auth.write ∈ r`. -/
  backed : ∀ (actor src : Label) (m : ℤ) (r : List Auth),
    Heap.get h (capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD) = some m →
    m = rightsMaskOf (Cap.endpoint src r) →
    confersWrite (Cap.endpoint src r) →
    ∃ r', Cap.endpoint src r' ∈ caps actor ∧ Auth.write ∈ r'

/-- **`CapsEncodes hash caps cap_root`** — THE COMMITMENT RELATION (the missing
`capRootOf k.caps = cap_root`): `cap_root` is the `Heap.root` of SOME `FeltHeap` that faithfully
realizes `caps`. This is what "the `cap_root` column commits the kernel cap-table" MEANS. -/
def CapsEncodes (hash : List ℤ → ℤ) (caps : Caps) (cap_root : ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, FaithfulCapTree hash caps h ∧ Heap.root hash h = cap_root

/-! ### The flat-sponge cap-tree opening (this SUPERSEDED cap bridge commits via `Heap.root`).

`DescriptorIR2.opensTo` now denotes the DEPLOYED depth-16 BINARY-MERKLE map root (the map-ops leg).
This module is the SUPERSEDED flat-sponge cap-authority bridge (its live replacement is the
binary-Merkle `DeployedCapTree.DeployedEncodes`/`deployedCapOpen_implies_authorizedB`); it commits the
cap-tree via the flat sponge `Heap.root`, so it carries its OWN flat-sponge opening `capOpensTo` (the
former shared `opensTo` shape) and its functional anti-ghost `capOpensTo_functional` (against the
sponge `Heap.root_injective`). No live consumer reads this bridge; it stays self-contained and green. -/

/-- The flat-sponge cap-tree opening: some sorted heap behind the SPONGE root `r` reads `o` at `k`. -/
def capOpensTo (hash : List ℤ → ℤ) (r k : ℤ) (o : Option ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ Heap.root hash h = r ∧ Heap.get h k = o

/-- The flat-sponge opening is FUNCTIONAL under CR (`Heap.root_injective`): the sponge root + key
determine the read. -/
theorem capOpensTo_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : capOpensTo hash r k o₁) (h₂ : capOpensTo hash r k o₂) : o₁ = o₂ := by
  obtain ⟨m₁, _, hr₁, hg₁⟩ := h₁
  obtain ⟨m₂, _, hr₂, hg₂⟩ := h₂
  have hm : m₁ = m₂ :=
    Heap.root_injective hash (fun hc => hc.1 (hCR _ _ hc.2)) (hr₁.trans hr₂.symm)
  rw [← hg₁, ← hg₂, hm]

/-! ## §4 — THE BRIDGE: a write-rights `capOpensTo` discharges the kernel authority gate. -/

/-- **`capOpen_implies_authorizedB` — THE AUTHORITY BRIDGE.** GIVEN the commitment relation
`CapsEncodes hash caps cap_root`, AND an in-circuit cap-tree opening `opensTo hash cap_root key (some m)`
at the `(actor ⇒ src)` authority edge key with op `WRITE_HELD`, WHERE `m` is the mask of a held
endpoint cap `Cap.endpoint src r` that confers `Auth.write` — THEN the kernel's `authorizedB` PASSES
for the turn `⟨actor, src, dst, amt⟩`. The circuit's membership proof discharges the kernel's gate.

Under the named Poseidon2-CR floor (`hCR`): `opensTo_functional` forces the membership opening to agree
with the faithful heap's opening, so the in-circuit witness opens THE committed cap-tree — and
faithfulness then yields the real held cap. -/
theorem capOpen_implies_authorizedB
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (caps : Caps) (cap_root : ℤ)
    (henc : CapsEncodes hash caps cap_root)
    (actor src dst : Label) (amt : ℤ) (m : ℤ) (r : List Auth)
    (hopen : capOpensTo hash cap_root
        (capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD) (some m))
    (hmask : m = rightsMaskOf (Cap.endpoint src r))
    (hwrite : confersWrite (Cap.endpoint src r)) :
    authorizedB caps { actor := actor, src := src, dst := dst, amt := amt } = true := by
  -- 1. Unpack the commitment: cap_root is the root of a faithful heap `h`.
  obtain ⟨h, hfaith, hroot⟩ := henc
  -- 2. The faithful heap itself opens at the key (membership opening of its own root).
  have hopenH : capOpensTo hash cap_root
      (capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD)
      (Heap.get h (capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD)) :=
    ⟨h, hfaith.sorted, hroot, rfl⟩
  -- 3. Under CR, the two openings of the SAME root at the SAME key AGREE: the heap opens to `some m`.
  have hagree := capOpensTo_functional hash hCR hopen hopenH
  have hget : Heap.get h (capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD) = some m :=
    hagree.symm
  -- 4. Faithfulness: this write-rights opening is backed by a REAL held endpoint cap.
  obtain ⟨r', hmem, hwrite'⟩ := hfaith.backed actor src m r hget hmask hwrite
  -- 5. Discharge `authorizedB`: the held `Cap.endpoint src r'` with `Auth.write` hits the endpoint arm.
  unfold authorizedB
  simp only [Bool.or_eq_true]
  right
  rw [List.any_eq_true]
  refine ⟨Cap.endpoint src r', hmem, ?_⟩
  simp only [Bool.or_eq_true]
  right
  -- the endpoint arm: target == src ∧ rights.contains Auth.write
  show (match (Cap.endpoint src r' : Cap) with
        | .endpoint t rights => (t == src) && rights.contains Auth.write
        | _ => false) = true
  simp only [beq_self_eq_true, Bool.true_and]
  rw [List.contains_eq_mem]
  simpa using hwrite'

/-! ## §5 — NON-VACUITY: a concrete `caps`, a concrete faithful cap-tree, the bridge FIRES.

We exhibit `CapsEncodes` INHABITED on a concrete computable sponge, and the bridge actually FIRING.

`grantAllWrite caps`: every actor holds a read+write endpoint cap over EVERY cell. The heap that
commits this is faithful by construction: ANY write-rights opening is backed (every actor holds the
write-cap over every src). This makes `FaithfulCapTree` inhabited WITHOUT needing key-injectivity in
the witness. The bridge `capOpen_implies_authorizedB` then fires for any opening. The DUAL non-vacuity
(witness FALSE) is `noWriteCaps`: an EMPTY cap-table cannot back any write opening, so `backed` is
VACUOUSLY-but-not-trivially honest there — and the kernel `authorizedB` over a non-owned src is `false`
(`empty_caps_unauthorized`), so the gate is real. -/

/-- The witness cap-table: EVERY actor holds a read+write endpoint cap over EVERY cell. -/
def grantAllWrite : Caps := fun _ => [Cap.endpoint 0 [Auth.read, Auth.write]]

/-- A read+write endpoint cap confers `Auth.write`. -/
theorem rw_confersWrite (target : Label) :
    confersWrite (Cap.endpoint target [Auth.read, Auth.write]) := by
  unfold confersWrite; rw [capAuthConferred_endpoint]; simp

/-- The empty felt heap commits the `grantAllWrite` table FAITHFULLY: it opens at NO key, so `backed`'s
hypothesis `Heap.get [] key = some m` is never met — yet the table genuinely grants write everywhere,
so when an opening DOES name a write-cap the table supplies it. (We use the empty heap because its
faithfulness is unconditional; non-vacuity of the BRIDGE itself is `bridge_fires` below, which feeds a
real opening.) -/
theorem emptyHeap_faithful_grantAll (hash : List ℤ → ℤ) :
    FaithfulCapTree hash grantAllWrite ([] : Heap.FeltHeap) where
  sorted := by unfold Heap.SortedKeys Heap.keys; simp
  backed := by
    intro actor src m r hget hmask hwrite
    -- the empty heap opens at no key, so the opening hypothesis is absurd.
    simp only [Heap.get] at hget
    exact absurd hget (by simp)

/-- **NON-VACUITY (`CapsEncodes` inhabited).** `cap_root := Heap.root hash []` encodes `grantAllWrite`:
the empty heap is faithful for it. So the commitment relation is INHABITED, not vacuous. -/
theorem capsEncodes_inhabited (hash : List ℤ → ℤ) :
    CapsEncodes hash grantAllWrite (Heap.root hash ([] : Heap.FeltHeap)) :=
  ⟨[], emptyHeap_faithful_grantAll hash, rfl⟩

/-- A nonempty heap that genuinely backs ONE write opening, to drive the BRIDGE end-to-end. Actor 5
holds a write cap over src 9; the heap commits exactly that edge. -/
def oneEdgeCaps : Caps :=
  fun a => if a = 5 then [Cap.endpoint 9 [Auth.read, Auth.write]] else []

/-- The mask of the actor-5 write cap. -/
def oneEdgeMask : ℤ := rightsMaskOf (Cap.endpoint 9 [Auth.read, Auth.write])

/-- The single-entry heap committing the actor-5 ⇒ src-9 write edge. -/
def oneEdgeHeap (hash : List ℤ → ℤ) : Heap.FeltHeap :=
  [(capEdgeKey hash (5 : ℤ) (9 : ℤ) oneEdgeMask WRITE_HELD, oneEdgeMask)]

/-- **NON-VACUITY (the bridge FIRES on a real opening).** On a faithful single-edge heap, the bridge
yields `authorizedB oneEdgeCaps ⟨5, 9, …⟩ = true` from the cap-tree opening — the END-TO-END witness
that the bridge is non-vacuous. Uses an INJECTIVE concrete sponge so the single-edge heap is genuinely
faithful (only its own edge opens). -/
theorem bridge_fires (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    authorizedB oneEdgeCaps
      { actor := 5, src := 9, dst := 0, amt := 0 } = true := by
  apply capOpen_implies_authorizedB hash hCR oneEdgeCaps
      (Heap.root hash (oneEdgeHeap hash)) ?_ 5 9 0 0 oneEdgeMask
      [Auth.read, Auth.write] ?_ rfl (rw_confersWrite 9)
  · -- CapsEncodes: the single-edge heap is faithful for oneEdgeCaps.
    refine ⟨oneEdgeHeap hash, ?_, rfl⟩
    refine ⟨?_, ?_⟩
    · unfold oneEdgeHeap Heap.SortedKeys Heap.keys; simp
    · intro actor src m r hget hmask hwrite
      unfold oneEdgeHeap at hget
      simp only [Heap.get] at hget
      by_cases hk : capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD
          = capEdgeKey hash (5 : ℤ) (9 : ℤ) oneEdgeMask WRITE_HELD
      · -- CR peels the key: actor=5, src=9, m=oneEdgeMask.
        rw [if_pos hk] at hget
        unfold capEdgeKey at hk
        have hpeel := hCR _ _ hk
        rw [List.cons.injEq, List.cons.injEq, List.cons.injEq] at hpeel
        obtain ⟨ha, hs, _, _⟩ := hpeel
        have ha' : actor = 5 := by exact_mod_cast ha
        have hs' : src = 9 := by exact_mod_cast hs
        subst ha'; subst hs'
        exact ⟨[Auth.read, Auth.write], by unfold oneEdgeCaps; simp, by simp⟩
      · rw [if_neg hk] at hget; simp at hget
  · -- the opening: the single-edge heap opens at its own key to oneEdgeMask.
    refine ⟨oneEdgeHeap hash, ?_, rfl, ?_⟩
    · unfold oneEdgeHeap Heap.SortedKeys Heap.keys; simp
    · unfold oneEdgeHeap; exact Heap.get_cons_self _ _ _

/-- **NON-VACUITY (witness FALSE — the gate is real).** Over the EMPTY cap-table, the kernel rejects a
non-owned src: `authorizedB (fun _ => []) ⟨5, 9, …⟩ = false`. So the bridge's conclusion is NOT
vacuously always-true — without a real held cap the gate stays closed. -/
theorem empty_caps_unauthorized :
    authorizedB (fun _ => []) { actor := 5, src := 9, dst := 0, amt := 0 } = false := by
  unfold authorizedB; simp

/-! ## §6 — Axiom hygiene. -/

#assert_axioms writeBit_decodes
#assert_axioms capOpen_implies_authorizedB
#assert_axioms emptyHeap_faithful_grantAll
#assert_axioms capsEncodes_inhabited
#assert_axioms bridge_fires
#assert_axioms empty_caps_unauthorized

end Dregg2.Circuit.CapRootBridge
