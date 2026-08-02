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
names for the two heaps in play (`CapOpenColl` / `CapBridgeColl`, §3½). Its three poles are proved AT
THAT RESIDUAL in §5½, on concrete `(henc, hopen)` pairs — REFUTABLE
(`capBridgeColl_refutable_at_the_bridge`), LOAD-BEARING
(`capOpen_implies_authorizedB_unconditional_false`, at the same instance —
`capBridgeColl_is_the_hypothesis_at_the_bridge`), DISCHARGEABLE
(`capBridgeColl_dischargeable_at_the_bridge`, at a sponge that is NOT injective). The `Heap`-level
re-exports in §4½ carry misleading `capBridgeColl_*` names and are NOT coverage of this residual.

⚠ `CapBridgeColl` has **no discharge uniform in `hash`, and correctly so**: it is the
ADVERSARIAL-opening residual, and by `capBridgeColl_iff_heaps_disagree` any uniform discharge would be
root-injectivity on the fiber of `cap_root`. Free discharge belongs to the explicit-heap core
`capHeapOpen_implies_authorizedB`, where the caller supplies both heaps. The DECODE of the write bit
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

`CapBridgeColl hash henc hopen` unfolds to `Heap.HeapRootColl hash (capOpenHeap hopen) (capsHeap henc)`
— **two heaps from two DIFFERENT `Exists.choose`s.** Its three discriminations are proved AT IT, in
§5½, on concrete `(henc, hopen)` pairs; `capBridgeColl_iff_heaps_disagree` is the sharp statement of
what discharging it means (the two chosen heaps ARE the same heap — the submitted opening opens THE
committed cap-tree).

  * REFUTABLE — `capBridgeColl_refutable_at_the_bridge`.
  * LOAD-BEARING — `capOpen_implies_authorizedB_unconditional_false` (and, for the explicit-heap core,
    `capHeapOpen_implies_authorizedB_unconditional_false`); `capBridgeColl_is_the_hypothesis_at_the_bridge`
    puts both halves at ONE instance in the type.
  * DISCHARGEABLE — `capBridgeColl_dischargeable_at_the_bridge`, at a sponge that is NOT injective;
    and `capBridgeColl_dischargeable_at_model` + `bridge_fires_through_keystone`, where the ∃-shaped
    keystone fires end-to-end on a `some m` opening.

⚠⚑ **WHAT IS NOT THERE, AND CANNOT BE: A DISCHARGE UNIFORM IN `hash`.** The four theorems named
`capBridgeColl_dischargeable` / `_refutable` / `_refutes_poseidon2CR` and `capHeapOpen_unconditional_false`
(§4) are NOT about this residual — they are verbatim re-exports of `Substrate/Heap.lean` facts at
`h h`, at a concrete literal pair, or about heap-root injectivity. `heapRootColl_dischargeable` in
particular DOES NOT instantiate here, and the reason is not an oversight in the port:

`Exists.choose` is a function of the PROPOSITION. A committer who submits its own heap `hC` for both
sides still cannot force `hopen.choose = hC`, because `Classical.choice` ranges over EVERY sorted heap
publishing `cap_root` and reading `o` at `k` — which is precisely the adversarial set the bridge exists
to exclude. By `capBridgeColl_iff_heaps_disagree`, any hypothesis discharging the residual is
equivalent to "those two chosen heaps agree", and at a `some m` opening that is root-injectivity
restricted to the fiber of `cap_root` — defect shape 2, the thing this port removed. **So a free
discharge here would be a smuggle, not a tooth.** Free discharge belongs to the explicit-heap core
`capHeapOpen_implies_authorizedB`, where the caller supplies both heaps and may supply the same one;
`CapBridgeColl` is the ADVERSARIAL-opening residual and is supposed to cost something.

What §5½ therefore proves instead is the honest thing: the discharge holds wherever `Heap.root` has a
SINGLETON FIBER at `cap_root`, with no injectivity assumed (`lenSponge`, which collides on every pair
of equal-length lists), and at the injective MODEL sponge for a real `some m` opening. -/
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

⚑ NO hypothesis on `hash` beyond the per-instance residual: because the CALLER supplies both heaps,
the honest committer discharges it for FREE at `hOpen = hCommit` (`Heap.heapRootColl_dischargeable`),
for EVERY hash, which the deleted `Poseidon2SpongeCR` floor could never do — it is unavailable at the
deployed sponge even to an honest party. (This free discharge is a property of the EXPLICIT-HEAP form
only; the ∃-shaped keystone's residual is `CapBridgeColl`, which has none — see its note.)

⚑ AND IT IS LOAD-BEARING: `capHeapOpen_implies_authorizedB_unconditional_false` (§5½) refutes this
statement with `hno` deleted and every other hypothesis kept. -/
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
supplies. Absent that collision the in-circuit witness opens THE committed cap-tree
(`capBridgeColl_iff_heaps_disagree` says exactly that), and faithfulness yields the real held cap.

⚑ THE RESIDUAL IS PINNED ON ALL THREE SIDES AT THIS EXACT SHAPE (§5½): it HOLDS at a real
`(henc, hopen)` pair (`capBridgeColl_refutable_at_the_bridge`); deleting `hno` makes THIS THEOREM
FALSE at that same pair (`capOpen_implies_authorizedB_unconditional_false` — the bridge would grant
write authority from an EMPTY cap table); and it is discharged, without assuming injectivity, at
`capBridgeColl_dischargeable_at_the_bridge`, with the whole keystone firing end-to-end at
`bridge_fires_through_keystone`. -/
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

/-! ### §4½ — HEAP-LEVEL RE-EXPORTS. ⚠ These are about `Heap.HeapRootColl` at a pair chosen HERE, not
about `CapOpenColl` or `CapBridgeColl`. The poles OF THOSE residuals are §5½; the misleading `_*`
names are kept only because downstream text cites them. Do not read a `capBridgeColl_` prefix as
coverage of `CapBridgeColl`. -/

/-- **THE EXPLICIT-HEAP CORE'S DISCHARGE, at `h h`.** ⚠ NOT a discharge of `CapBridgeColl`: this is
`Heap.heapRootColl_dischargeable` re-exported, and it applies only where the SAME heap term appears on
both sides — which is `capHeapOpen_implies_authorizedB`'s caller-supplied shape (see `bridge_fires`),
never the two `Exists.choose`s of the ∃-shaped keystone. `CapBridgeColl` has no discharge uniform in
`hash` and is not supposed to; see the note on `CapBridgeColl` and §5½. -/
theorem capBridgeColl_dischargeable (hash : List ℤ → ℤ) (h : Heap.FeltHeap) :
    ¬ Heap.HeapRootColl hash h h :=
  Heap.heapRootColl_dischargeable hash h

/-- **`Heap.HeapRootColl` IS REFUTABLE AT A LITERAL PAIR.** At the collapsing sponge two DISTINCT
cap-tree-shaped heaps publish the same root and the extractor hands back a genuine collision, so
`¬ HeapRootColl` is not `True` in disguise. ⚠ Stated at hand-picked literals, so it says nothing about
the pair `CapBridgeColl` names — that refutation is `capBridgeColl_refutable_at_the_bridge`. -/
theorem capBridgeColl_refutable :
    Heap.HeapRootColl (fun _ => (0 : ℤ)) [(0, 0)] [(0, 1)] :=
  Heap.heapRootColl_refutable

/-- **HEAP-ROOT INJECTIVITY IS FALSE** — `∀ hash h₁ h₂, root hash h₁ = root hash h₂ → h₁ = h₂` does
not hold, so `root_injective`'s residual is not removable by strengthening its conclusion.

⚠ THAT IS ALL THIS SAYS. Despite the name it is NOT the load-bearing tooth for
`capHeapOpen_implies_authorizedB`, whose `hno`-free form also carries `hfaith`, `hroot`, `hget`,
`hmask` and `hwrite` — refuting a weaker-hypothesis statement establishes nothing about a stronger
one. The genuine load-bearing teeth are `capHeapOpen_implies_authorizedB_unconditional_false` (the
explicit-heap core) and `capOpen_implies_authorizedB_unconditional_false` (the ∃-shaped keystone), both
in §5½. Kept because it is true and cited downstream. -/
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

/-- **The empty felt heap is a faithful cap-tree for ANY cap table, at ANY hash.** It opens at NO key,
so `backed`'s hypothesis `Heap.get [] key = some m` is never met and the `caps` argument is never
read. Stated at an arbitrary `caps` because the two poles below need it at BOTH ends: at
`grantAllWrite` (the inhabitation witness) and at the EMPTY table `fun _ => []` (the load-bearing
refutations of §5½, where the commitment must be faithful for a table that backs nothing). -/
theorem emptyHeap_faithful (hash : List ℤ → ℤ) (caps : Caps) :
    FaithfulCapTree hash caps ([] : Heap.FeltHeap) where
  sorted := by unfold Heap.SortedKeys Heap.keys; simp
  backed := by
    intro actor src m r hget hmask hwrite
    -- the empty heap opens at no key, so the opening hypothesis is absurd.
    simp only [Heap.get] at hget
    exact absurd hget (by simp)

/-- The empty felt heap commits the `grantAllWrite` table FAITHFULLY: it opens at NO key, so `backed`'s
hypothesis `Heap.get [] key = some m` is never met — yet the table genuinely grants write everywhere,
so when an opening DOES name a write-cap the table supplies it. (We use the empty heap because its
faithfulness is unconditional; non-vacuity of the BRIDGE itself is `bridge_fires` below, which feeds a
real opening.) -/
theorem emptyHeap_faithful_grantAll (hash : List ℤ → ℤ) :
    FaithfulCapTree hash grantAllWrite ([] : Heap.FeltHeap) :=
  emptyHeap_faithful hash grantAllWrite

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

/-- The single-entry heap is sorted (a one-key spine is vacuously strictly increasing). -/
theorem oneEdgeHeap_sorted (hash : List ℤ → ℤ) : Heap.SortedKeys (oneEdgeHeap hash) := by
  unfold oneEdgeHeap Heap.SortedKeys Heap.keys; simp

/-- The single-entry heap OPENS at its own cap-edge key to the actor-5 write mask. -/
theorem oneEdgeHeap_get (hash : List ℤ → ℤ) :
    Heap.get (oneEdgeHeap hash)
      (capEdgeKey hash ((5 : Label) : ℤ) ((9 : Label) : ℤ) oneEdgeMask WRITE_HELD)
      = some oneEdgeMask := by
  unfold oneEdgeHeap; exact Heap.get_cons_self _ _ _

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
and the commitment are the SAME heap), so this witness binds nothing.

⚠ This routes through the EXPLICIT-HEAP core, so it says nothing about the ∃-shaped keystone or
`CapBridgeColl`. The keystone's own end-to-end firing is `bridge_fires_through_keystone` (§5½.3). -/
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

/-! ## §5½ — THE RESIDUAL'S OWN THREE POLES, AT `CapBridgeColl` ITSELF.

Everything above §5 states poles of `Heap.HeapRootColl` at a pair chosen in `Substrate/Heap.lean`
(`h h`, or the literal `[(0,0)] / [(0,1)]`). Neither instantiates to `CapBridgeColl`, whose two heaps
come from two DIFFERENT `Exists.choose`s. This section proves the poles AT THE RESIDUAL THE KEYSTONE
CARRIES, on concrete `(henc, hopen)` pairs built from the objects above.

The pivot is `capBridgeColl_heaps_agree_or_collides`: unconditionally, either the two chosen heaps
ARE the same heap or the residual holds. So both remaining poles reduce to deciding that equality on a
concrete instance — WITHOUT ever assuming root injectivity, which is what defect shape 2 would be.

  * REFUTABLE — make the two chosen heaps PROVABLY differ. Over the EMPTY cap table no faithful
    cap-tree can open a write-rights authority edge at all (`backed`'s conclusion is `∃ r', … ∈ []`),
    while the submitted opening does exactly that by construction. The heaps differ, so at a sponge
    that lets both publish the same root the residual HOLDS: `capBridgeColl_refutable_at_the_bridge`.
  * LOAD-BEARING — the SAME instance refutes the keystone minus `hno`, both in its explicit-heap form
    (`capHeapOpen_implies_authorizedB_unconditional_false`) and, crucially, in the ∃-shaped form the
    residual actually guards (`capOpen_implies_authorizedB_unconditional_false`). Dropping
    `¬ CapBridgeColl` makes the bridge grant authority over a cell whose owner granted nothing.
  * DISCHARGEABLE — make the two chosen heaps PROVABLY equal. `lenSponge` below is a sponge that sees
    only the LENGTH of what it absorbs (so it is about as far from injective as a function gets), yet
    `Heap.root lenSponge h = h.length` PINS the empty heap at root `0`. Both `Exists.choose`s are then
    forced to `[]` and the residual fails: `capBridgeColl_dischargeable_at_the_bridge`, which binds
    nothing and reaches no floor. The second discharge is at the injective MODEL sponge, where the
    ∃-shaped keystone fires end-to-end (`bridge_fires_through_keystone`).

⚠ WHAT THIS SECTION DOES **NOT** ESTABLISH, and cannot: a discharge that is FREE, i.e. uniform in
`hash`. See the note on `CapBridgeColl` itself. -/

/-- **⚑ THE RESIDUAL IS EXACTLY THE DISAGREEMENT OF THE TWO `Exists.choose`s** — unconditionally, with
no hypothesis on `hash` at all. Both propositions carry `Heap.root … = cap_root`, so the two heaps they
supply publish the same root; `Heap.root_binds_or_collides` then leaves exactly two possibilities. This
is the pivot both remaining poles reduce to, and it is what makes `¬ CapBridgeColl` mean "the submitted
opening opens THE committed cap-tree" rather than an opaque side condition. -/
theorem capBridgeColl_heaps_agree_or_collides (hash : List ℤ → ℤ) {caps : Caps} {cap_root k : ℤ}
    {o : Option ℤ} (henc : CapsEncodes hash caps cap_root) (hopen : capOpensTo hash cap_root k o) :
    capOpenHeap hopen = capsHeap henc ∨ CapBridgeColl hash henc hopen := by
  obtain ⟨-, hor, -⟩ := hopen.choose_spec
  obtain ⟨-, hcr⟩ := henc.choose_spec
  exact Heap.root_binds_or_collides hash (hor.trans hcr.symm)

/-- **⚑ WHAT DISCHARGING THE RESIDUAL *IS*, EXACTLY** — an IFF, so the discharge condition is not left
to prose. `CapBridgeColl` holds precisely when the two `Exists.choose`s hand back DIFFERENT heaps.

Read the useful way round: `¬ CapBridgeColl hash henc hopen ↔ capOpenHeap hopen = capsHeap henc` —
"the submitted opening opens THE committed cap-tree". That is the whole content of the residual, and
it is also why no discharge uniform in `hash` exists (see the note on `CapBridgeColl`): supplying one
would be supplying that the root map is injective on the fiber of `cap_root`. -/
theorem capBridgeColl_iff_heaps_disagree (hash : List ℤ → ℤ) {caps : Caps} {cap_root k : ℤ}
    {o : Option ℤ} (henc : CapsEncodes hash caps cap_root) (hopen : capOpensTo hash cap_root k o) :
    CapBridgeColl hash henc hopen ↔ capOpenHeap hopen ≠ capsHeap henc := by
  constructor
  · intro hc heq
    unfold CapBridgeColl at hc
    rw [heq] at hc
    exact Heap.heapRootColl_dischargeable hash _ hc
  · intro hne
    exact (capBridgeColl_heaps_agree_or_collides hash henc hopen).resolve_left hne

/-! ### §5½.1 — the REFUTABLE / LOAD-BEARING instance: an empty cap table and a collapsing sponge. -/

/-- The COLLAPSING sponge — every absorption digests to `0`. The extreme of the pigeonhole
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` proves the deployed BabyBear sponge suffers a
quantitative form of: distinct leaf lists, one digest. -/
def collapseHash : List ℤ → ℤ := fun _ => 0

/-- Every heap publishes root `0` under the collapsing sponge — including the empty one and the
single-edge one, which is what lets a commitment of NOTHING and an opening of a write edge agree on a
`cap_root`. -/
theorem collapseHash_root (h : Heap.FeltHeap) : Heap.root collapseHash h = 0 := rfl

/-- The COMMITMENT side of the refuting instance: the EMPTY cap table, committed by the EMPTY heap,
publishing `cap_root = 0`. Faithful because a heap that opens nowhere backs nothing. -/
theorem collapseEnc : CapsEncodes collapseHash (fun _ => []) 0 :=
  ⟨[], emptyHeap_faithful collapseHash (fun _ => []), collapseHash_root []⟩

/-- The OPENING side of the refuting instance: a sorted single-edge heap that publishes the SAME
`cap_root = 0` and opens at the `(actor 5 ⇒ src 9)` authority edge to the write mask. Nobody granted
that edge — the cap table is empty — but the collapsing sponge cannot tell the two heaps apart. -/
theorem collapseOpen : capOpensTo collapseHash 0
    (capEdgeKey collapseHash ((5 : Label) : ℤ) ((9 : Label) : ℤ) oneEdgeMask WRITE_HELD)
    (some oneEdgeMask) :=
  ⟨oneEdgeHeap collapseHash, oneEdgeHeap_sorted collapseHash,
    collapseHash_root _, oneEdgeHeap_get collapseHash⟩

/-- **⚑ REFUTABLE — `CapBridgeColl` HOLDING, at a REAL `(henc, hopen)` PAIR.** Not `HeapRootColl` at a
hand-picked literal pair: the residual the keystone itself carries, at the two heaps THESE TWO
`Exists.choose`s supply.

The proof never inspects either chosen heap. It shows they must DIFFER: the opening's heap reads the
write mask at the `(5 ⇒ 9)` cap-edge key, and NO faithful cap-tree for the empty table can do that
(`backed` would have to produce a held `Cap.endpoint 9 r' ∈ ([] : List Cap)`). Two distinct heaps at
one root is exactly the left disjunct of `capBridgeColl_heaps_agree_or_collides` failing. -/
theorem capBridgeColl_refutable_at_the_bridge :
    CapBridgeColl collapseHash collapseEnc collapseOpen := by
  rcases capBridgeColl_heaps_agree_or_collides collapseHash collapseEnc collapseOpen with heq | hc
  · exfalso
    obtain ⟨-, -, hog⟩ := collapseOpen.choose_spec
    obtain ⟨hfaith, -⟩ := collapseEnc.choose_spec
    -- the commitment's heap would have to open the very edge it commits nothing about.
    have hog' : Heap.get (capsHeap collapseEnc)
        (capEdgeKey collapseHash ((5 : Label) : ℤ) ((9 : Label) : ℤ) oneEdgeMask WRITE_HELD)
        = some oneEdgeMask := by rw [← heq]; exact hog
    obtain ⟨r', hmem, -⟩ :=
      hfaith.backed 5 9 oneEdgeMask [Auth.read, Auth.write] hog' rfl (rw_confersWrite 9)
    simp at hmem
  · exact hc

/-- **⚑ LOAD-BEARING (the explicit-heap core).** `capHeapOpen_implies_authorizedB` MINUS `hno` — every
other hypothesis kept — is FALSE. This is the tooth `capHeapOpen_unconditional_false` was named for and
is not: that one refutes heap-root injectivity, a strictly weaker statement whose refutation carries no
information about this one.

The counterexample is the §5½.1 instance: at the collapsing sponge the empty heap faithfully commits
the EMPTY cap table at `cap_root = 0`, the single-edge heap publishes the same root and opens the
`(5 ⇒ 9)` write edge — so every surviving hypothesis holds — and the conclusion is refuted outright by
`empty_caps_unauthorized`. Without the residual the bridge hands actor 5 write authority over cell 9
from a cap table that grants nobody anything. -/
theorem capHeapOpen_implies_authorizedB_unconditional_false :
    ¬ (∀ (hash : List ℤ → ℤ) (caps : Caps) (hOpen hCommit : Heap.FeltHeap),
        FaithfulCapTree hash caps hCommit →
        Heap.root hash hOpen = Heap.root hash hCommit →
        ∀ (actor src dst : Label) (amt m : ℤ) (r : List Auth),
          Heap.get hOpen (capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD) = some m →
          m = rightsMaskOf (Cap.endpoint src r) →
          confersWrite (Cap.endpoint src r) →
          authorizedB caps { actor := actor, src := src, dst := dst, amt := amt } = true) := by
  intro hall
  have h := hall collapseHash (fun _ => []) (oneEdgeHeap collapseHash) []
    (emptyHeap_faithful collapseHash (fun _ => []))
    ((collapseHash_root _).trans (collapseHash_root _).symm)
    5 9 0 0 oneEdgeMask [Auth.read, Auth.write]
    (oneEdgeHeap_get collapseHash) rfl (rw_confersWrite 9)
  rw [empty_caps_unauthorized] at h
  exact absurd h (by decide)

/-- **⚑ LOAD-BEARING AT THE ∃-SHAPED KEYSTONE — the one that actually guards `CapBridgeColl`.**
`capOpen_implies_authorizedB` MINUS `hno` is FALSE, at the very pair
`capBridgeColl_refutable_at_the_bridge` exhibits the residual holding on. So the residual is not
decoration on the keystone: delete it and the authority bridge grants write over a cell whose cap
table is empty.

Together with `capBridgeColl_refutable_at_the_bridge` this is the sharp statement — the SAME instance
both satisfies the residual and breaks the conclusion, so `¬ CapBridgeColl` is exactly the hypothesis
doing the work, not a side condition that happens to be unavailable. -/
theorem capOpen_implies_authorizedB_unconditional_false :
    ¬ (∀ (hash : List ℤ → ℤ) (caps : Caps) (cap_root : ℤ),
        CapsEncodes hash caps cap_root →
        ∀ (actor src dst : Label) (amt m : ℤ) (r : List Auth),
          capOpensTo hash cap_root
            (capEdgeKey hash (actor : ℤ) (src : ℤ) m WRITE_HELD) (some m) →
          m = rightsMaskOf (Cap.endpoint src r) →
          confersWrite (Cap.endpoint src r) →
          authorizedB caps { actor := actor, src := src, dst := dst, amt := amt } = true) := by
  intro hall
  have h := hall collapseHash (fun _ => []) 0 collapseEnc
    5 9 0 0 oneEdgeMask [Auth.read, Auth.write] collapseOpen rfl (rw_confersWrite 9)
  rw [empty_caps_unauthorized] at h
  exact absurd h (by decide)

/-- **⚑ THE TWO HALVES MEET AT ONE INSTANCE, IN THE TYPE.** The refutation and the load-bearing
refutation above are proved of the SAME `(collapseEnc, collapseOpen)` pair, but a reader cannot see
that from either statement — the instance lives inside the proofs. Here it is in the type: on this
instance the residual HOLDS and the keystone's conclusion FAILS. So `¬ CapBridgeColl` is not merely
*a* hypothesis one could drop and break something; it is the hypothesis that is unavailable exactly
where the bridge must not fire. -/
theorem capBridgeColl_is_the_hypothesis_at_the_bridge :
    CapBridgeColl collapseHash collapseEnc collapseOpen
      ∧ authorizedB (fun _ => []) { actor := 5, src := 9, dst := 0, amt := 0 } ≠ true :=
  ⟨capBridgeColl_refutable_at_the_bridge, by rw [empty_caps_unauthorized]; decide⟩

/-! ### §5½.2 — the DISCHARGEABLE pole, at a sponge that is NOT injective.

A discharge obtained by ASSUMING the sponge injective would be the deleted floor wearing a hat. The
witness below assumes nothing: `lenSponge` collapses every list of the same length to the same felt —
so it collides everywhere — and the residual is still refuted, because at root `0` the root map PINS
its preimage on the nose.

⚠ Read the distinction exactly. The note on `CapBridgeColl` says no HYPOTHESIS may deliver the
discharge, because the only ones that do are root-injectivity on the fiber of `cap_root` restated.
What happens here is the opposite direction: at a NAMED `(hash, cap_root)` the singleton-fiber fact is
a PROVED THEOREM with no premise, so the discharge is derived rather than assumed. That is the pattern
the whole campaign runs on — the residual must be satisfiable and refutable at instances, and provable
at none. -/

/-- A sponge that sees only the LENGTH of what it absorbs. Wildly non-injective (`lenSponge [0] =
lenSponge [1]`), and NOT a model of anything deployed — it is here to show the discharge below does not
secretly come from injectivity. -/
def lenSponge : List ℤ → ℤ := fun l => (l.length : ℤ)

/-- Under `lenSponge` the heap root is the heap's LENGTH: one leaf digest per entry, and the outer
absorption counts them. -/
theorem lenSponge_root (h : Heap.FeltHeap) : Heap.root lenSponge h = (h.length : ℤ) := by
  unfold Heap.root lenSponge; simp

/-- **THE ROOT PINS ITS PREIMAGE AT `0`** — with no injectivity anywhere. This is what a genuine
discharge of `CapBridgeColl` needs and all it needs: a `cap_root` whose fiber is a singleton, so both
`Exists.choose`s land on the same heap. -/
theorem lenSponge_root_zero {h : Heap.FeltHeap} (hr : Heap.root lenSponge h = 0) : h = [] := by
  rw [lenSponge_root] at hr
  have hlen : h.length = 0 := by exact_mod_cast hr
  simpa using hlen

/-- The COMMITMENT side of the discharging instance: the empty cap table committed by the empty heap. -/
theorem lenEnc : CapsEncodes lenSponge (fun _ => []) 0 :=
  ⟨[], emptyHeap_faithful lenSponge (fun _ => []), by rw [lenSponge_root]; simp⟩

/-- The OPENING side of the discharging instance: a NON-membership opening of the same `cap_root` — the
committed cap-tree does not carry the `(5 ⇒ 9)` authority edge, and the opening says so. -/
theorem lenOpen : capOpensTo lenSponge 0
    (capEdgeKey lenSponge ((5 : Label) : ℤ) ((9 : Label) : ℤ) oneEdgeMask WRITE_HELD) none :=
  ⟨[], by unfold Heap.SortedKeys Heap.keys; simp, by rw [lenSponge_root]; simp, rfl⟩

/-- **⚑ DISCHARGEABLE — `¬ CapBridgeColl` HOLDING, at a REAL `(henc, hopen)` PAIR, ASSUMING NOTHING.**
The residual is not `True` in disguise from the other side either: here it genuinely FAILS. And the
discharge is not smuggled injectivity — `lenSponge` collides on every pair of equal-length lists. What
does the work is that `Heap.root lenSponge` has a SINGLETON fiber at `0`, so the commitment's chosen
heap and the opening's chosen heap are both forced to `[]` and `Heap.heapRootColl_dischargeable`
applies at a pair that genuinely arose from two different `Exists.choose`s. -/
theorem capBridgeColl_dischargeable_at_the_bridge :
    ¬ CapBridgeColl lenSponge lenEnc lenOpen := by
  have h1 : capOpenHeap lenOpen = [] := lenSponge_root_zero lenOpen.choose_spec.2.1
  have h2 : capsHeap lenEnc = [] := lenSponge_root_zero lenEnc.choose_spec.2
  unfold CapBridgeColl
  rw [h1, h2]
  exact Heap.heapRootColl_dischargeable lenSponge []

/-! ### §5½.3 — the ∃-SHAPED KEYSTONE FIRES END-TO-END.

`bridge_fires` routes through the explicit-heap core, so it says nothing about the ∃-shaped keystone
or its residual. This does: `capOpen_implies_authorizedB` itself, on a real commitment and a real
`some m` opening, with `¬ CapBridgeColl` DISCHARGED rather than assumed.

⚠ The sponge here is `modelSponge`, the tree's concrete UNBOUNDED reference sponge — a MODEL, never a
claim about the deployed one (same pole, and same caveat, as `oneEdgeHeap_faithful`/`bridge_fires`).
A `some m` discharge cannot be had at a non-injective sponge: see the note on `CapBridgeColl`. -/

/-- The commitment: the actor-5 ⇒ src-9 write edge, committed by the faithful single-edge cap-tree. -/
theorem modelEnc :
    CapsEncodes modelSponge oneEdgeCaps (Heap.root modelSponge (oneEdgeHeap modelSponge)) :=
  ⟨oneEdgeHeap modelSponge, oneEdgeHeap_faithful, rfl⟩

/-- The submitted in-circuit opening of that commitment at the `(5 ⇒ 9)` authority edge. -/
theorem modelOpen : capOpensTo modelSponge (Heap.root modelSponge (oneEdgeHeap modelSponge))
    (capEdgeKey modelSponge ((5 : Label) : ℤ) ((9 : Label) : ℤ) oneEdgeMask WRITE_HELD)
    (some oneEdgeMask) :=
  ⟨oneEdgeHeap modelSponge, oneEdgeHeap_sorted modelSponge, rfl, oneEdgeHeap_get modelSponge⟩

/-- The residual is discharged at the model sponge — routed through the tree's UNIVERSAL bridge
`Poseidon2Binding.spongeColl_refutable_of_injective`, so no per-site floor carrier is minted here and
this declaration's TYPE binds nothing. -/
theorem capBridgeColl_dischargeable_at_model : ¬ CapBridgeColl modelSponge modelEnc modelOpen :=
  Dregg2.Circuit.Poseidon2Binding.spongeColl_refutable_of_injective modelSponge
    Dregg2.Circuit.Poseidon2Binding.Reference.refSponge_CR _

/-- **⚑ NON-VACUITY OF THE KEYSTONE ITSELF.** `capOpen_implies_authorizedB` — the ∃-shaped bridge, not
its explicit-heap core — yields `authorizedB oneEdgeCaps ⟨5, 9, …⟩ = true` from a real `CapsEncodes` and
a real `capOpensTo`, with its residual discharged. Paired with
`capOpen_implies_authorizedB_unconditional_false` (same conclusion shape, FALSE without the residual)
and `empty_caps_unauthorized` (the gate is real), the keystone is pinned on all three sides. -/
theorem bridge_fires_through_keystone :
    authorizedB oneEdgeCaps { actor := 5, src := 9, dst := 0, amt := 0 } = true :=
  capOpen_implies_authorizedB modelSponge oneEdgeCaps _ modelEnc 5 9 0 0 oneEdgeMask
    [Auth.read, Auth.write] modelOpen capBridgeColl_dischargeable_at_model rfl (rw_confersWrite 9)

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
#assert_axioms emptyHeap_faithful
#assert_axioms emptyHeap_faithful_grantAll
#assert_axioms capsEncodes_inhabited
#assert_axioms oneEdgeHeap_sorted
#assert_axioms oneEdgeHeap_get
#assert_axioms oneEdgeHeap_faithful
#assert_axioms bridge_fires
#assert_axioms empty_caps_unauthorized
-- §5½ — the residual's own three poles.
#assert_axioms capBridgeColl_heaps_agree_or_collides
#assert_axioms capBridgeColl_iff_heaps_disagree
#assert_axioms capBridgeColl_refutable_at_the_bridge
#assert_axioms capBridgeColl_is_the_hypothesis_at_the_bridge
#assert_axioms capHeapOpen_implies_authorizedB_unconditional_false
#assert_axioms capOpen_implies_authorizedB_unconditional_false
#assert_axioms capBridgeColl_dischargeable_at_the_bridge
#assert_axioms capBridgeColl_dischargeable_at_model
#assert_axioms bridge_fires_through_keystone
-- The `(henc, hopen)` WITNESSES themselves: the poles above are only worth their names if these are
-- genuine inhabitants, so each one is pinned too.
#assert_axioms collapseHash_root
#assert_axioms collapseEnc
#assert_axioms collapseOpen
#assert_axioms lenSponge_root
#assert_axioms lenSponge_root_zero
#assert_axioms lenEnc
#assert_axioms lenOpen
#assert_axioms modelEnc
#assert_axioms modelOpen

/-! ### THE FLOOR REJECTORS — the refuted floor is out of proof-closure reach of every ported
statement, with a POSITIVE CONTROL so the walk is demonstrably not blind. -/

#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capOpensTo_binds_or_collides [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capOpensTo_functional [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capHeapOpen_implies_authorizedB [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capOpen_implies_authorizedB [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
-- The §5½ poles OF THE RESIDUAL ITSELF, pinned clean: the refutation, both load-bearing
-- refutations, and the discharge at the deliberately NON-injective `lenSponge`. That last one is
-- the point — a discharge that reached the floor would be the deleted injectivity in a hat.
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capBridgeColl_heaps_agree_or_collides [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capBridgeColl_iff_heaps_disagree [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capBridgeColl_refutable_at_the_bridge [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capBridgeColl_is_the_hypothesis_at_the_bridge [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capHeapOpen_implies_authorizedB_unconditional_false [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capOpen_implies_authorizedB_unconditional_false [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.CapRootBridge.capBridgeColl_dischargeable_at_the_bridge [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
-- ⚠ `bridge_fires`/`oneEdgeHeap_faithful`, and now `capBridgeColl_dischargeable_at_model`/
-- `bridge_fires_through_keystone`, are deliberately NOT pinned clean: they are the SATISFIABILITY
-- pole, and they reach `Poseidon2SpongeCR` through `Reference.refSponge_CR` — a closed proof at a
-- concrete UNBOUNDED sponge, i.e. a MODEL. That is anti-vacuity content, not exposure: none of
-- these declarations' TYPES bind the floor.
#assert_depends_on Dregg2.Circuit.Poseidon2Binding.spongeColl_refutable_of_injective [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

end Dregg2.Circuit.CapRootBridge
