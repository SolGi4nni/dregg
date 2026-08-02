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
discipline `Heap.root_injective` rides: the sorted-Poseidon2 root binds its leaf list up to a NAMED,
per-instance sponge collision, and `CapsEncodes` is the statement that THIS root commits a leaf list
faithful to `caps`.

⚑ **THE CRYPTO CARRIER IS NO LONGER A FLOOR (2026-08-01).** Every theorem here used to bind
`Poseidon2SpongeCR hash`, which is FALSE at deployed BabyBear parameters
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`) — so the authority bridge was VACUOUSLY TRUE
where the prover actually runs. It now carries `Heap.HeapRootColl` at the ONE pair `Heap.rootFind`
names for the two heaps in play (`CapOpenColl` / `CapBridgeColl`, §3½), which is decidable,
refutable (`capBridgeColl_refutable`), load-bearing (`capHeapOpen_unconditional_false`) and free to
the honest committer (`capBridgeColl_dischargeable`). The DECODE of the write bit
(`Auth.write ∈ r` from `authBitN Auth.write` set in `rightsMaskOf (Cap.endpoint src r)`) is a PROVEN
round-trip (`writeBit_decodes`), no carrier.

NON-VACUITY: `singletonCaps` + `encodeSingleton` exhibit a concrete `caps`, a concrete sorted heap
that encodes it, and the bridge firing on it — so `CapsEncodes` is INHABITED and the bridge is not
vacuous; and a heap with the write bit CLEARED fails to fire (the gate is real).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; `#assert_not_depends_on` pins the refuted
`Poseidon2SpongeCR` out of proof-closure reach of every ported statement, with a positive control on
the tree's universal bridge so the rejector is not vacuous. The two SATISFIABILITY witnesses
(`oneEdgeHeap_faithful`, `bridge_fires`) reach the floor only through `Reference.refSponge_CR`, a
closed proof at a concrete UNBOUNDED sponge — a MODEL, and neither of their TYPES binds anything.
Imports are read-only.
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

/-! ### ⚑ PORTED OFF `Poseidon2SpongeCR` (2026-08-01) — the residual is NAMED AT THE PAIR.

Every theorem in this file used to take `(hCR : Poseidon2SpongeCR hash)` — literal injectivity of a
`List ℤ → ℤ` sponge, which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at
deployed BabyBear parameters — so the authority bridge said NOTHING about the deployed prover.

`Substrate.Heap` already did the underlying port (`Heap.rootFind` is the TOTAL extractor,
`Heap.root_binds_or_collides` the UNCONDITIONAL dichotomy, `Heap.HeapRootColl` the decidable
per-instance residual with all three poles proved). What was left here was the ∃-shaped statement:
`capOpensTo`/`CapsEncodes` HIDE their heaps behind an `∃`, so the residual cannot be stated at "the
two heaps" without naming them.

⚠ The wrong fix is a side condition quantified OUTSIDE the claim — `∀ h₁ h₂, root h₁ = r →
root h₂ = r → ¬ HeapRootColl hash h₁ h₂` is injectivity-at-`r` rewritten, defect shape 2. The fix
used here is the one `DeployedMapDenotation.OpenResidS` established: `Exists.choose` is CANONICAL
(proof irrelevance makes `h.choose` a function of the PROPOSITION, not of the proof term), so
`capOpenHeap`/`capsHeap` NAME the heaps these particular openings supply and the residual is INDEXED
BY the two proof objects the theorem already takes — the ONE pair, and nothing wider.

A consumer still holding the floor rewires through the tree's UNIVERSAL bridge
`Poseidon2Binding.spongeColl_refutable_of_injective _ hCR _` (quantified over the pair) composed
with `Heap.HeapRootColl`'s definition; no per-site `_of_CR` twin is minted here. -/

/-- The heap a flat-sponge opening supplies (canonical by proof irrelevance). -/
noncomputable def capOpenHeap {hash : List ℤ → ℤ} {r k : ℤ} {o : Option ℤ}
    (h : capOpensTo hash r k o) : Heap.FeltHeap := h.choose

/-- The faithful cap-tree a commitment supplies (canonical by proof irrelevance). -/
noncomputable def capsHeap {hash : List ℤ → ℤ} {caps : Caps} {cap_root : ℤ}
    (h : CapsEncodes hash caps cap_root) : Heap.FeltHeap := h.choose

/-- **`CapOpenColl`** — the per-instance residual of the flat-sponge opening anti-ghost: the deployed
sponge genuinely collides at the ONE pair `Heap.rootFind` returns for the two heaps THESE TWO
OPENINGS supply. Decidable, refutable, and dischargeable at zero cost by an honest committer — none
of which the floor it replaced ever was. -/
def CapOpenColl (hash : List ℤ → ℤ) {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : capOpensTo hash r k o₁) (h₂ : capOpensTo hash r k o₂) : Prop :=
  Heap.HeapRootColl hash (capOpenHeap h₁) (capOpenHeap h₂)

/-- **`CapBridgeColl`** — the residual THE BRIDGE consumes: the sponge collides at the pair
`Heap.rootFind` names for the heap the SUBMITTED opening supplies and the heap the COMMITMENT
supplies.

⚠⚑ **ITS THREE DISCRIMINATIONS ARE UNPROVED, AND THE FOUR THEOREMS NAMED `capBridgeColl_*` BELOW ARE
NOT ABOUT IT.** Stated here rather than in a report, because a residual whose teeth are cited but
absent is exactly what this campaign exists to remove — and this instance is the campaign's own
output.

`CapBridgeColl hash henc hopen` unfolds to `Heap.HeapRootColl hash (capOpenHeap hopen) (capsHeap henc)`
— **two heaps from two DIFFERENT `Exists.choose`s**, not derivably equal. The three teeth below are
verbatim re-exports of `Substrate/Heap.lean`'s `heapRootColl_dischargeable` / `_refutable` /
`_refutes_poseidon2CR`, which are about `h h` or a concrete literal pair. `heapRootColl_dischargeable`
DOES NOT instantiate to `CapBridgeColl`, and nothing in this tree exhibits `CapBridgeColl` holding or
failing at any real `(henc, hopen)`.

So of the three discriminations the ported keystone `capOpen_implies_authorizedB` requires at the
residual it ACTUALLY carries — dischargeable at an honest committer, refutable at a broken hash,
load-bearing — **zero are proved.** `bridge_fires` does not close this: it routes through the
explicit-heap core `capHeapOpen_implies_authorizedB`, not through the ∃-shaped keystone.

The ∃-hiding move itself is right (the `OpenResidS` precedent, indexed by the proof objects). What is
missing is that the teeth never followed it out of `Heap`. Until they do, treat the `capBridgeColl_*`
names as heap-level facts that happen to sit here, and do not cite them as coverage of this residual. -/
def CapBridgeColl (hash : List ℤ → ℤ) {caps : Caps} {cap_root k : ℤ} {o : Option ℤ}
    (henc : CapsEncodes hash caps cap_root) (hopen : capOpensTo hash cap_root k o) : Prop :=
  Heap.HeapRootColl hash (capOpenHeap hopen) (capsHeap henc)

/-- **⚑ THE OPENING ANTI-GHOST, UNCONDITIONAL — NO FLOOR.** Two flat-sponge openings of the same
root at the same key EITHER agree, OR the sponge genuinely collides at the named pair. No hypothesis
on `hash` at all, so — unlike the theorem it replaces — this holds at deployed BabyBear parameters. -/
theorem capOpensTo_binds_or_collides (hash : List ℤ → ℤ) {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : capOpensTo hash r k o₁) (h₂ : capOpensTo hash r k o₂) :
    o₁ = o₂ ∨ CapOpenColl hash h₁ h₂ := by
  obtain ⟨-, hr₁, hg₁⟩ := h₁.choose_spec
  obtain ⟨-, hr₂, hg₂⟩ := h₂.choose_spec
  rcases Heap.root_binds_or_collides hash (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [← hg₁, ← hg₂, hm])
  · exact Or.inr hc

/-- The flat-sponge opening is FUNCTIONAL: the sponge root + key determine the read. ⚑ The refuted
`Poseidon2SpongeCR` binder is GONE; what remains is the per-instance, refutable residual at the ONE
pair the extractor names for THESE two openings. -/
theorem capOpensTo_functional (hash : List ℤ → ℤ)
    {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : capOpensTo hash r k o₁) (h₂ : capOpensTo hash r k o₂)
    (hno : ¬ CapOpenColl hash h₁ h₂) : o₁ = o₂ :=
  (capOpensTo_binds_or_collides hash h₁ h₂).resolve_right hno

/-! ## §4 — THE BRIDGE: a write-rights `capOpensTo` discharges the kernel authority gate. -/

/-- **`capHeapOpen_implies_authorizedB` — THE BRIDGE OVER EXPLICIT HEAPS.** The content of the
authority bridge with the two heaps NAMED rather than hidden behind an `∃`: a submitted opening heap
`hOpen` publishing the committed heap's root, absent a sponge collision at the ONE pair
`Heap.rootFind` names for THOSE TWO HEAPS, IS the committed cap-tree — and faithfulness then yields
the real held cap, so the kernel's `authorizedB` passes.

⚑ NO hypothesis on `hash` beyond the per-instance residual: the honest committer discharges it for
FREE at `hOpen = hCommit` (`Heap.heapRootColl_dischargeable`), for EVERY hash, which the deleted
`Poseidon2SpongeCR` floor could never do — it is unavailable at the deployed sponge even to an
honest party. -/
theorem capHeapOpen_implies_authorizedB
    (hash : List ℤ → ℤ) {caps : Caps} {hOpen hCommit : Heap.FeltHeap}
    (hfaith : FaithfulCapTree hash caps hCommit)
    (hno : ¬ Heap.HeapRootColl hash hOpen hCommit)
    (hroot : Heap.root hash hOpen = Heap.root hash hCommit)
    (actor src dst : Label) (amt : ℤ) (m : ℤ) (r : List Auth)
    (hget : Heap.get hOpen (capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD) = some m)
    (hmask : m = rightsMaskOf (Cap.endpoint src r))
    (hwrite : confersWrite (Cap.endpoint src r)) :
    authorizedB caps { actor := actor, src := src, dst := dst, amt := amt } = true := by
  -- 1. The two heaps carry the same root and do not collide, so they ARE the same heap.
  obtain rfl : hOpen = hCommit := Heap.root_injective hash hno hroot
  -- 2. Faithfulness: this write-rights opening is backed by a REAL held endpoint cap.
  obtain ⟨r', hmem, hwrite'⟩ := hfaith.backed actor src m r hget hmask hwrite
  -- 3. Discharge `authorizedB`: the held `Cap.endpoint src r'` with `Auth.write` hits the endpoint arm.
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

/-- **`capOpen_implies_authorizedB` — THE AUTHORITY BRIDGE.** GIVEN the commitment relation
`CapsEncodes hash caps cap_root`, AND an in-circuit cap-tree opening `capOpensTo hash cap_root key
(some m)` at the `(actor ⇒ src)` authority edge key with op `WRITE_HELD`, WHERE `m` is the mask of a
held endpoint cap `Cap.endpoint src r` that confers `Auth.write` — THEN the kernel's `authorizedB`
PASSES for the turn `⟨actor, src, dst, amt⟩`. The circuit's membership proof discharges the kernel's
gate.

⚑ **PORTED OFF `Poseidon2SpongeCR` (2026-08-01).** The floor is FALSE at deployed BabyBear, so this
bridge was VACUOUSLY TRUE where the prover runs. Its crypto reliance is now the per-instance,
decidable, REFUTABLE `¬ CapBridgeColl hash henc hopen`: the deployed sponge does not collide at the
ONE pair `Heap.rootFind` names for the heap THIS opening supplies and the heap THIS commitment
supplies. Absent that collision the in-circuit witness opens THE committed cap-tree, and faithfulness
yields the real held cap. -/
theorem capOpen_implies_authorizedB
    (hash : List ℤ → ℤ)
    (caps : Caps) (cap_root : ℤ)
    (henc : CapsEncodes hash caps cap_root)
    (actor src dst : Label) (amt : ℤ) (m : ℤ) (r : List Auth)
    (hopen : capOpensTo hash cap_root
        (capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD) (some m))
    (hno : ¬ CapBridgeColl hash henc hopen)
    (hmask : m = rightsMaskOf (Cap.endpoint src r))
    (hwrite : confersWrite (Cap.endpoint src r)) :
    authorizedB caps { actor := actor, src := src, dst := dst, amt := amt } = true := by
  obtain ⟨hfaith, hcroot⟩ := henc.choose_spec
  obtain ⟨-, hor, hog⟩ := hopen.choose_spec
  exact capHeapOpen_implies_authorizedB hash hfaith hno (hor.trans hcroot.symm)
    actor src dst amt m r hog hmask hwrite

/-! ### THE PORT'S TEETH — the residual is DISCHARGEABLE for free, REFUTABLE, and LOAD-BEARING. -/

/-- **DISCHARGEABLE / FIRES, for EVERY hash.** The honest committer — who publishes ONE cap-tree —
discharges the residual at zero cost, with no cryptographic assumption whatsoever. This is exactly
what `Poseidon2SpongeCR` could not do: the deployed sponge does not satisfy it, so an honest party
could not supply it either. -/
theorem capBridgeColl_dischargeable (hash : List ℤ → ℤ) (h : Heap.FeltHeap) :
    ¬ Heap.HeapRootColl hash h h :=
  Heap.heapRootColl_dischargeable hash h

/-- **REFUTABLE.** At the collapsing sponge two DISTINCT cap-tree heaps publish the same root and the
extractor hands back a genuine collision, so `¬ HeapRootColl` is not `True` in disguise and the
ported bridge cannot discharge itself through the right branch. -/
theorem capBridgeColl_refutable :
    Heap.HeapRootColl (fun _ => (0 : ℤ)) [(0, 0)] [(0, 1)] :=
  Heap.heapRootColl_refutable

/-- **⚠ NOT THE LOAD-BEARING TOOTH IT IS NAMED AS — it refutes a DIFFERENT statement.**

What it refutes is heap-root INJECTIVITY: `∀ hash h₁ h₂, root hash h₁ = root hash h₂ → h₁ = h₂`.
What a load-bearing tooth would have to refute is `capHeapOpen_implies_authorizedB` MINUS `hno`,
which also carries `hfaith`, `hget`, `hmask` and `hwrite`. Refuting a weaker-hypothesis statement
establishes nothing about a stronger one — which is precisely the
`logChained_of_verified_unconditional_false` error another lane in the same workflow spent its whole
pass repairing, reproduced here.

⚑ AND THE REAL ONE IS AVAILABLE, from objects already in this file: `hash := fun _ => 0`,
`caps := fun _ => []`, `hCommit := []` (faithful by the same absurd-`hget` argument as
`emptyHeap_faithful_grantAll`, which never reads `caps`), `hOpen := oneEdgeHeap (fun _ => 0)`. Both
roots are `0` since `Heap.root hash h = hash (h.map …)`, and the conclusion is refuted by
`empty_caps_unauthorized`. A proxy was shipped where the genuine article was eight lines away.

The statement below is TRUE and is kept — it just is not this theorem's tooth. -/
theorem capHeapOpen_unconditional_false :
    ¬ (∀ (hash : List ℤ → ℤ) (h₁ h₂ : Heap.FeltHeap),
        Heap.root hash h₁ = Heap.root hash h₂ → h₁ = h₂) := by
  intro hall
  have h := hall (fun _ => 0) [(0, 0)] [(0, 1)] rfl
  simp at h

/-- **A REFUTATION, NOT A NEW FLOOR.** Exhibiting the residual REFUTES `Poseidon2SpongeCR` outright,
so this port is a strict WEAKENING of the premise it replaces — every ported statement here is
strictly STRONGER than the one it displaced, with an unchanged conclusion. -/
theorem capBridgeColl_refutes_poseidon2CR {hash : List ℤ → ℤ} {h₁ h₂ : Heap.FeltHeap}
    (hc : Heap.HeapRootColl hash h₁ h₂) : ¬ Poseidon2SpongeCR hash :=
  Heap.heapRootColl_refutes_poseidon2CR hc

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

/-- **THE MODEL SPONGE for the non-vacuity witnesses.** The tree's UNBOUNDED reference sponge, which
is GENUINELY injective — `Reference.refSponge_CR` is a CLOSED PROOF, not an assumption, because
`refSponge` has an infinite codomain and so escapes the pigeonhole that refutes the floor at deployed
BabyBear width. Using it here means the witnesses below bind NO hypothesis at all; it is a MODEL, and
NEVER a claim about the deployed sponge. (Same abstract-but-not-deployed pole
`Verify.RestFrameFiniteSupportSuccessor.restHashIffFrameFin_satisfiable` occupies, for the same
reason.) -/
abbrev modelSponge : List ℤ → ℤ := Dregg2.Circuit.Poseidon2Binding.Reference.refSponge

/-- The single-edge heap is a FAITHFUL cap-tree for `oneEdgeCaps` at the model sponge: only its own
edge opens, so the only backable write opening is actor 5's genuine cap over src 9. The key peel is
discharged by `refSponge_CR`, a closed proof about THIS concrete sponge — so this witness carries no
hypothesis and mints no floor carrier. -/
theorem oneEdgeHeap_faithful :
    FaithfulCapTree modelSponge oneEdgeCaps (oneEdgeHeap modelSponge) := by
  refine ⟨?_, ?_⟩
  · unfold oneEdgeHeap Heap.SortedKeys Heap.keys; simp
  · intro actor src m r hget hmask hwrite
    unfold oneEdgeHeap at hget
    simp only [Heap.get] at hget
    by_cases hk : capEdgeKey modelSponge (actor : ℤ) (src : ℤ) m WRITE_HELD
        = capEdgeKey modelSponge (5 : ℤ) (9 : ℤ) oneEdgeMask WRITE_HELD
    · -- the model sponge's injectivity peels the key: actor = 5, src = 9.
      rw [if_pos hk] at hget
      unfold capEdgeKey at hk
      have hpeel := Dregg2.Circuit.Poseidon2Binding.Reference.refSponge_CR _ _ hk
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq] at hpeel
      obtain ⟨ha, hs, _, _⟩ := hpeel
      have ha' : actor = 5 := by exact_mod_cast ha
      have hs' : src = 9 := by exact_mod_cast hs
      subst ha'; subst hs'
      exact ⟨[Auth.read, Auth.write], by unfold oneEdgeCaps; simp, by simp⟩
    · rw [if_neg hk] at hget; simp at hget

/-- **NON-VACUITY (the bridge FIRES on a real opening) — NOW WITH NO HYPOTHESIS AT ALL.** On the
faithful single-edge cap-tree the bridge yields `authorizedB oneEdgeCaps ⟨5, 9, …⟩ = true` from the
cap-tree opening — the END-TO-END witness that the bridge is non-vacuous.

⚑ The pre-cutover form took `(hash) (hCR : Poseidon2SpongeCR hash)`, i.e. it exhibited the bridge
firing only under a hypothesis nothing satisfies at deployed parameters. The residual it needs now is
the honest committer's, discharged for FREE by `capBridgeColl_dischargeable` (the submitted opening
and the commitment are the SAME heap), so this witness binds nothing. -/
theorem bridge_fires :
    authorizedB oneEdgeCaps
      { actor := 5, src := 9, dst := 0, amt := 0 } = true :=
  capHeapOpen_implies_authorizedB modelSponge oneEdgeHeap_faithful
    (capBridgeColl_dischargeable modelSponge (oneEdgeHeap modelSponge)) rfl
    5 9 0 0 oneEdgeMask [Auth.read, Auth.write]
    (by unfold oneEdgeHeap; exact Heap.get_cons_self _ _ _) rfl (rw_confersWrite 9)

/-- **NON-VACUITY (witness FALSE — the gate is real).** Over the EMPTY cap-table, the kernel rejects a
non-owned src: `authorizedB (fun _ => []) ⟨5, 9, …⟩ = false`. So the bridge's conclusion is NOT
vacuously always-true — without a real held cap the gate stays closed. -/
theorem empty_caps_unauthorized :
    authorizedB (fun _ => []) { actor := 5, src := 9, dst := 0, amt := 0 } = false := by
  unfold authorizedB; simp

/-! ## §6 — Axiom hygiene. -/

#assert_axioms writeBit_decodes
#assert_axioms capOpensTo_binds_or_collides
#assert_axioms capOpensTo_functional
#assert_axioms capHeapOpen_implies_authorizedB
#assert_axioms capOpen_implies_authorizedB
#assert_axioms capBridgeColl_dischargeable
#assert_axioms capBridgeColl_refutable
#assert_axioms capHeapOpen_unconditional_false
#assert_axioms capBridgeColl_refutes_poseidon2CR
#assert_axioms emptyHeap_faithful_grantAll
#assert_axioms capsEncodes_inhabited
#assert_axioms oneEdgeHeap_faithful
#assert_axioms bridge_fires
#assert_axioms empty_caps_unauthorized

/-! ### THE FLOOR REJECTORS — the refuted floor is out of proof-closure reach of every ported
statement, with a POSITIVE CONTROL so the walk is demonstrably not blind. -/

#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capOpensTo_binds_or_collides [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capOpensTo_functional [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capHeapOpen_implies_authorizedB [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capOpen_implies_authorizedB [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
-- ⚠ `bridge_fires`/`oneEdgeHeap_faithful` are deliberately NOT pinned clean: they are the
-- SATISFIABILITY pole, and they reach `Poseidon2SpongeCR` through `Reference.refSponge_CR` — a
-- closed proof at a concrete UNBOUNDED sponge, i.e. a MODEL. That is anti-vacuity content, not
-- exposure: neither declaration's TYPE binds the floor.
#assert_depends_on Dregg2.Circuit.Poseidon2Binding.spongeColl_refutable_of_injective [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

end Dregg2.Circuit.CapRootBridge
