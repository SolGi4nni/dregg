/-
# Dregg2.Circuit.ShieldedOnRampPin — the shielded VALUE ON-RAMP boundary: what Shield/Deshield
  must enforce, why the CURRENT `note_shielded` append cannot enforce it, and the exact aliasing
  hazard the two value encodings open at the boundary.

**The lane.** `docs/DESIGN-shielded-value-on-ramp.md` §4 names this file as the recommended next
byte-safe step: *"Lean `ShieldedOnRampPin.lean` (boundary conservation model + falsifier)"*, with §5.1
adding *"the on-ramp must either carry the value in the 16-lane wide encoding or cap shieldable
amounts. Not resolved by this design. **It is the first thing the Lean lane should model.**"* Both are
modeled here.

House-law-1 said out loud: **the on-ramp AIR is Lean-authored.** This module is the metatheory of the
boundary — the obligation and its falsifier. It authors no descriptor and touches no deployed byte;
the emitted objects it composes with (`Emit.ShieldedSpendDescriptor`, `Emit.ShieldedNoteAppendDescriptor`)
are already Lean-authored. Nothing here licenses a hand-written Rust gadget.

## What is proved

**§1 — the boundary transition and its conservation obligation, over ℤ.** A `Shield` moves one
cleartext note of `u64` value `v` out of `note_commitments` and mints the Poseidon2 note commitment
`hash_fact(v,[asset,owner,rand])` into `note_shielded`, with `v` PUBLIC at entry (Shield-A, DESIGN
§2.2). `step_conserves_supply` / `run_conserves_supply` prove the total supply
`Σ cleartext + Σ shielded` is invariant across any run of Shield/Deshield steps — as an **ℤ equality**,
not a congruence. `shield_leaving_eq_entering` states the per-step obligation exactly: the amount
leaving cleartext = the amount entering shielded = the public `v`, in ℤ. `modp_identity_is_not_the_obligation`
shows why the "as ℤ" is load-bearing: `0` and `p` are congruent mod p, both are `u64`, and they are
not equal — a mod-p identity is not a conservation identity.

**§2 — THE FALSIFIER: the current GATE-4 append cannot establish membership soundness.**
`apply.rs:1849` appends `ShieldedNoteCommitment(leg.commitment_bytes)` — the prover's wire bytes,
verbatim (a compressed Ristretto Pedersen *value* commitment). `deployed_append_leaf_is_wire_verbatim`
and `deployed_append_is_free` state that the appended membership leaf is an unconstrained function of
the wire: for every target the prover has a wire value that lands it. Consequently
`deployed_append_unsound` proves `AccumulatorSound` is **FALSE** for the resulting root, and
`deployed_append_unsound_today` proves it with **zero hypotheses** at the deployed reality (no `Shield`
effect exists, so the set of ledger-authorized shielded notes is EMPTY — DESIGN §0.1 *"value has never
entered the shielded pool"*). `l4_pin_over_deployed_append_relocates_15` is the load-bearing
composition: an L4 pin to *that* root is satisfied by a spend of a note no gate ever authorized — the
pin holds and the theft still lands. **#15 relocates one level up; it does not close.**

**§2.1 — a sharpening of the design's own claim (a partial refutation, reported not buried).** DESIGN
§3.3 prices the wound as *"`AccumulatorSound` is FALSE … that is exactly the `NoteAccumulatorCR`
hypothesis"*, where `NoteAccumulatorCR`'s note predicate is the ∃-image
`IsCommittedNote hash leaf := ∃ v as ow rd, leaf ≡ hash_fact(v,[as,ow,rd])`. That predicate **cannot**
price it: `noteAccumulatorCR_vacuous_of_c6Surjective` proves that if the C6 site is mod-p surjective in
its preimages — which a real Poseidon2 with four free field inputs onto a ~2^31 codomain is expected to
be — then `NoteAccumulatorCR` holds **for every root, including the prover-written one**. The
∃-image is satisfied by "some opening exists", never "an opening the ledger authorized". So the
falsifier is stated at the predicate that carries the content, `IsLedgerNote` (the leaf is the
commitment of a preimage the boundary gate approved), where it is unconditional; the literal
`IsCommittedNote` form is also proved (`deployed_append_breaks_noteAccumulatorCR`), under the
explicitly named non-surjectivity hypothesis it genuinely needs.

**§3 — THE FIX, SOUND.** Shield-A appends `noteLeaf hash n` for a preimage `n` the boundary gate
authorized, so `shieldAppend_is_ledger_note` is by construction (no crypto). Feeding that construction
fact into the landed `ShieldedSpendPortResidual.noteAccumulatorCR_of_hashFloor` gives
`shieldA_noteAccumulatorCR` — `NoteAccumulatorCR` **HOLDS** over the Shield-A accumulated set under the
single named Poseidon2 floor `FoldReachIsMember` (the Merkle-root binding floor, not a per-leaf
assumption). `shieldA_pin_spends_authorized` is the strictly stronger conclusion the `IsLedgerNote`
predicate buys: a pinned-and-accepted spend spends a note the ledger AUTHORIZED, not merely one that
has some opening. `shieldA_pin_closes_15` composes with the landed
`ShieldedSpendPortDischarge.pin_accept_is_note_committed`, and `deshield_publishes_an_entered_value`
is the exit statement: a `Deshield` can only publish the value of a note a `Shield` entered.

**§4 — THE VALUE-ALIASING TOOTH.** The two sides of the boundary reduce the same `u64` differently:
the committed CLEARTEXT leaf column carries `split_u64(value).0` = the **low 30 bits**
(`circuit/src/effect_vm/helpers.rs:13-17`, `cell/src/commitment_set.rs:262`), while the shielded C6
opening reduces the value **mod p** (`p = 2013265921 < 2^31`). `boundary_images_alias_both_ways`
exhibits `u64` pairs aliased by each image and separated by the other. `aliased_shield_inflates` is the
concrete inflation: a shield whose conservation check runs on the cleartext leaf's own value column
mints `2^30` units from a note worth `0`, and `supply` strictly increases — the ℤ-invariant of §1 is
broken by exactly `2^30`. Two closures are proved: `cap_closes_aliased_shield` (an amount cap
`v < 2^30` makes both images injective, so the aliased check IS the exact check) and
`wide4_injective_on_u64` (the deployed 16-bit-limb `u64` encoding — `U64_LIMBS = 4`, `LIMB_BITS = 16`,
`circuit-prove/src/shielded/wide_value_binding.rs:37-40` — is injective on the whole `u64` range, and
`wide4_separates_the_alias` shows it separates the very pair the leaf column conflates).

## Scope (honest)

This is the metatheory of the boundary, NOT the boundary. It does **not** implement `Effect::Shield` /
`Effect::Deshield` (wire + `effects_hash` + a descriptor rung = VK-affecting, ember-gated per DESIGN
§4), does **not** fix the GATE-4 append, and emits no descriptor. The `Shield-A` append modeled in §3
is the object `Emit.ShieldedNoteAppendDescriptor` (L2) forces in-AIR — the correspondence is a NAMING
here, not a bridge; bridging the AAFI/sorted-tree append model to this `foldPath` membership model is
the named next lane. Crypto enters only as NAMED hypotheses: `FoldReachIsMember` (Poseidon2
Merkle-binding, the landed floor — itself realized over a real committed accumulator under `HairCR` by
`ShieldedSpendFoldReachRealized.foldReachIsMember_realized`, so §3's floor is a reduction, not a fresh
assumption) and `C6Surjective` (a property OF Poseidon2, used only to show a hypothesis is not free).
No `sorry`, no `admit`, no `native_decide`.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Circuit.ShieldedOnRampPin`.
-/
import Dregg2.Circuit.ShieldedSpendPortResidual

set_option autoImplicit false

namespace Dregg2.Circuit.ShieldedOnRampPin

open Dregg2.Circuit.ShieldedMerkleRootPin
  (Level Payload foldPath membershipVerifies acceptsPinned AccumulatorSound)
open Dregg2.Circuit.ShieldedSpendPortDischarge
  (P Hair IsCommittedNote NoteAccumulatorCR pin_accept_is_note_committed)
open Dregg2.Circuit.ShieldedSpendPortResidual (FoldReachIsMember noteAccumulatorCR_of_hashFloor)
open Dregg2.Circuit.Emit.ShieldedSpendDescriptor (NS_FACT_MARK)

/-! ## §1 — the boundary transition and its conservation obligation, over ℤ.

Faithful to DESIGN §2.2 (Shield-A) and §2.5 (Deshield): a shield consumes ONE cleartext note through
the existing FNSP gates and mints ONE shielded note commitment, with the amount PUBLIC at entry; a
deshield is the mirror. The note's `u64` value is modeled as `ℕ` (the `u64` bound enters only where it
is load-bearing, §4); the other three fields are field elements, as the C6 opening sees them. -/

/-- A note preimage as the boundary gate sees it: the `u64` amount plus the three C6 fields. This is
the opening of the Poseidon2 note commitment `hash_fact(value, [asset, owner, randomness])` — the
`ShieldedSpendPortDischarge.IsCommittedNote` shape, DESIGN §2.4 C6. -/
structure Note where
  value : ℕ
  asset : ℤ
  owner : ℤ
  rand  : ℤ

/-- The **minted membership leaf** of a shielded note: the Poseidon2 note commitment
`hash_fact(value, [asset, owner, randomness])`, byte-for-byte the emitted C6 site
(`Emit.ShieldedSpendDescriptor`'s `cLEAF` relation, `NS_FACT_MARK`-marked, arity padded to 5). This is
what Shield-A appends to `note_shielded` — never a Pedersen point. -/
def noteLeaf (hash : List ℤ → ℤ) (n : Note) : ℤ :=
  hash [(n.value : ℤ), n.asset, n.owner, n.rand, 0, NS_FACT_MARK, 1]

/-- A minted Shield-A leaf IS an `IsCommittedNote` — by construction, no crypto: the appended object
is literally the C6 image of the opening the gate validated. -/
theorem noteLeaf_isCommittedNote (hash : List ℤ → ℤ) (n : Note) :
    IsCommittedNote hash (noteLeaf hash n) :=
  ⟨(n.value : ℤ), n.asset, n.owner, n.rand, Int.ModEq.refl _⟩

/-- The boundary state: the live cleartext notes (`note_commitments`, the side the shield spends from)
and the openings of the shielded set's leaves (`note_shielded`). The shielded list is the GHOST
opening record — on chain only the commitments are visible; conservation is a statement about the
openings, which is exactly why the boundary gate must FORCE the opening it appends. -/
structure Boundary where
  cleartext : List Note
  shielded  : List Note

/-- The ℤ total of a list of note values. Not a mod-p sum: the conservation obligation is an INTEGER
identity (§1's `modp_identity_is_not_the_obligation` prices the difference). -/
def totalZ (l : List Note) : ℤ := (l.map (fun n => (n.value : ℤ))).sum

/-- The system's total supply across the boundary: cleartext plus shielded, in ℤ. -/
def supply (b : Boundary) : ℤ := totalZ b.cleartext + totalZ b.shielded

theorem totalZ_append (l₁ l₂ : List Note) : totalZ (l₁ ++ l₂) = totalZ l₁ + totalZ l₂ := by
  simp [totalZ]

theorem totalZ_cons (n : Note) (l : List Note) : totalZ (n :: l) = (n.value : ℤ) + totalZ l := by
  simp [totalZ]

/-- **The boundary step relation.** `shield`: one cleartext note leaves `note_commitments` (its
nullifier consumed through the existing FNSP gates) and the SAME opening enters `note_shielded`, with
the public entry amount `v` tied to the note's value (`hpub` — DESIGN §2.2's *"`value_in == value` as a
plain `u64` equality the executor checks in the clear"*). `deshield` is the mirror (DESIGN §2.5). The
public amount is carried explicitly so the obligation is stated over the value the boundary PUBLISHES,
not over an unobservable one. -/
inductive Step : Boundary → Boundary → Prop where
  | shield (pre post sh : List Note) (n : Note) (v : ℕ) (hpub : v = n.value) :
      Step ⟨pre ++ n :: post, sh⟩ ⟨pre ++ post, n :: sh⟩
  | deshield (ct pre post : List Note) (n : Note) (v : ℕ) (hpub : v = n.value) :
      Step ⟨ct, pre ++ n :: post⟩ ⟨n :: ct, pre ++ post⟩

/-- **⚑ THE PER-STEP OBLIGATION, stated exactly (`shield_leaving_eq_entering`).** For a shield step:
the amount LEAVING the cleartext side equals the amount ENTERING the shielded side equals the PUBLIC
entry amount `v` — all three as **ℤ** equalities. This is the conservation content of the boundary in
one line; §2 is about the gate that must force it and §4 about the encoding that can defeat it. -/
theorem shield_leaving_eq_entering (pre post sh : List Note) (n : Note) (v : ℕ) (hpub : v = n.value) :
    totalZ (pre ++ n :: post) - totalZ (pre ++ post) = (v : ℤ)
    ∧ totalZ (n :: sh) - totalZ sh = (v : ℤ)
    ∧ totalZ (pre ++ n :: post) - totalZ (pre ++ post) = totalZ (n :: sh) - totalZ sh := by
  have hl : totalZ (pre ++ n :: post) - totalZ (pre ++ post) = (v : ℤ) := by
    rw [totalZ_append, totalZ_append, totalZ_cons, hpub]; ring
  have hr : totalZ (n :: sh) - totalZ sh = (v : ℤ) := by
    rw [totalZ_cons, hpub]; ring
  exact ⟨hl, hr, hl.trans hr.symm⟩

/-- **`step_conserves_supply`.** Every boundary step — shield or deshield — preserves the ℤ total
supply. The pool is a black box that publishes `Σ shielded-in` and `Σ shielded-out` in the clear
(DESIGN §2.5's *"resulting global property"*), and the box neither mints nor burns. -/
theorem step_conserves_supply (b b' : Boundary) (h : Step b b') : supply b' = supply b := by
  cases h with
  | shield pre post sh n v hpub =>
      simp only [supply, totalZ_append, totalZ_cons]; ring
  | deshield ct pre post n v hpub =>
      simp only [supply, totalZ_append, totalZ_cons]; ring

/-- **⚑ `run_conserves_supply` — the on-ramp's global invariant.** Over ANY run of shield/deshield
steps the ℤ supply is unchanged. This is the property the whole §2 falsifier is about: it holds for the
MODEL, and the deployed append is what fails to force the model. -/
theorem run_conserves_supply (b b' : Boundary) (h : Relation.ReflTransGen Step b b') :
    supply b' = supply b := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [step_conserves_supply _ _ hstep, ih]

/-- **`modp_identity_is_not_the_obligation`.** Why §1 insists on ℤ: `0` and `p` are congruent mod p,
both are representable `u64` amounts, and they are NOT equal. A boundary identity checked mod p
therefore admits a `p`-unit mint. (`2013265921 < 2^64`.) -/
theorem modp_identity_is_not_the_obligation :
    ∃ v₁ v₂ : ℕ, v₁ < 18446744073709551616 ∧ v₂ < 18446744073709551616 ∧
      ((v₁ : ℤ) ≡ (v₂ : ℤ) [ZMOD P]) ∧ (v₁ : ℤ) ≠ (v₂ : ℤ) := by
  refine ⟨2013265921, 0, by norm_num, by norm_num, ?_, by norm_num⟩
  show (2013265921 : ℤ) % P = (0 : ℤ) % P
  norm_num [P]

/-! ## §2 — THE FALSIFIER: the CURRENT append writes the prover's wire bytes, so the accumulated set
establishes nothing.

`turn/src/executor/apply.rs:1846-1854` (GATE 4):

```rust
for leg in &payload.output_legs {
    let commitment = ShieldedNoteCommitment(leg.commitment_bytes);   // ← THE WIRE BYTES, VERBATIM
    set.insert(commitment)…;
}
```

Ground-truthed at HEAD: GATE 1 (`verify_stark_with_wide_bindings`) proves the INPUTS' membership and
nullifiers against `payload.merkle_root` — itself a wire felt (#15). GATE 2
(`verify_full_conservation_bytes`) constrains the output legs only as **Pedersen** objects: a Ristretto
point with a Bulletproof range proof, summing to the inputs' commitments. The prover chooses the
blinding freely, so the appended 32 bytes are prover-determined; **nothing anywhere ties them to the
image of `hash_fact(value,[asset,owner,rand])`, and nothing ties them to a note any ledger gate
authorized.** -/

/-- **The predicate that carries the content: `IsLedgerNote`.** A leaf is a genuine shielded note iff it
is the C6 commitment of a preimage the boundary gate AUTHORIZED (`auth n` — the source cleartext note
was spent through the FNSP gates and the public entry amount checked). This is strictly stronger than
`IsCommittedNote`, which asks only that SOME opening exist — see §2.1 for why that difference is the
whole falsifier. -/
def IsLedgerNote (hash : List ℤ → ℤ) (auth : Note → Prop) (leaf : ℤ) : Prop :=
  ∃ n : Note, auth n ∧ leaf ≡ noteLeaf hash n [ZMOD P]

/-- The strengthening is a refinement: a ledger-authorized note is in particular an `IsCommittedNote`,
so every §3 conclusion at `IsLedgerNote` implies the corresponding one at `IsCommittedNote`. -/
theorem ledgerNote_isCommittedNote (hash : List ℤ → ℤ) (auth : Note → Prop) (leaf : ℤ)
    (h : IsLedgerNote hash auth leaf) : IsCommittedNote hash leaf := by
  obtain ⟨n, _, hcong⟩ := h
  exact ⟨(n.value : ℤ), n.asset, n.owner, n.rand, hcong⟩

/-- **The deployed GATE-4 append (`apply.rs:1849`), modeled.** The appended membership leaf IS the
prover's wire value — `ShieldedNoteCommitment(leg.commitment_bytes)`, verbatim, with no relation to any
note preimage. -/
def deployedAppendLeaf (wire : ℤ) : ℤ := wire

/-- After appending a leaf at a position with authentication path `path`, the accumulator root is the
fold of that leaf up that path: an appended leaf is, by the definition of an append, a member of the
resulting tree. `Hair hash` is the emitted per-level Poseidon2 site
(`ShieldedSpendPortDischarge.emitted_fold_step_row0`), so this is the SAME fold the spend gadget walks. -/
def rootAfterAppend (hash : List ℤ → ℤ) (leaf : ℤ) (path : List Level) : ℤ :=
  foldPath (Hair hash) leaf path

/-- The appended leaf is a member of the post-append tree (`rfl` — this is what "append" means). -/
theorem appended_leaf_is_member (hash : List ℤ → ℤ) (leaf : ℤ) (path : List Level) :
    membershipVerifies (Hair hash) leaf path (rootAfterAppend hash leaf path) := rfl

/-- **`deployed_append_leaf_is_wire_verbatim`.** The appended leaf is the wire value, unchanged. -/
theorem deployed_append_leaf_is_wire_verbatim (wire : ℤ) : deployedAppendLeaf wire = wire := rfl

/-- **`deployed_append_is_free`.** The prover can place ANY value in `note_shielded`: the append is a
surjection from the wire onto the leaf space. There is no image constraint to violate because there is
no image constraint. -/
theorem deployed_append_is_free (target : ℤ) : ∃ wire : ℤ, deployedAppendLeaf wire = target :=
  ⟨target, rfl⟩

/-- **⚑ THE FALSIFIER (`deployed_append_unsound`).** Append any wire value that is not a
ledger-authorized note's commitment, and `AccumulatorSound` is FALSE for the resulting root: the
witness is that very leaf, sitting in the tree with a genuine authentication path. This is the exact
hypothesis `pin_accept_is_note_committed` requires — so it cannot be discharged for `note_shielded` as
populated today. -/
theorem deployed_append_unsound (hash : List ℤ → ℤ) (auth : Note → Prop) (wire : ℤ)
    (path : List Level) (hnot : ¬ IsLedgerNote hash auth wire) :
    ¬ AccumulatorSound (Hair hash) (IsLedgerNote hash auth)
        (rootAfterAppend hash (deployedAppendLeaf wire) path) := by
  intro hsound
  exact hnot (hsound wire path rfl)

/-- The deployed reality, as a predicate: **no shielded note is ledger-authorized**, because there is
no `Shield` effect, no mint path, and no ledger object anywhere in a shielded note's provenance
(DESIGN §0.1, §1.1: *"There is no mint, no shield, no genesis, and no ledger read anywhere in an
input's provenance"*). -/
def noAuthorization : Note → Prop := fun _ => False

theorem nothing_is_authorized_today (hash : List ℤ → ℤ) (leaf : ℤ) :
    ¬ IsLedgerNote hash noAuthorization leaf := by
  rintro ⟨_, hfalse, _⟩; exact hfalse

/-- **⚑ THE FALSIFIER AT THE DEPLOYED PARAMETERS (`deployed_append_unsound_today`) — ZERO
hypotheses.** For every hash, every wire value and every path: the accumulator that today's GATE-4
append produces is UNSOUND. Not "unsound under an assumption about Poseidon2" — unsound because the
authorized set is empty, so **every** element of `note_shielded` is a leaf no gate ever authorized. -/
theorem deployed_append_unsound_today (hash : List ℤ → ℤ) (wire : ℤ) (path : List Level) :
    ¬ AccumulatorSound (Hair hash) (IsLedgerNote hash noAuthorization)
        (rootAfterAppend hash (deployedAppendLeaf wire) path) :=
  deployed_append_unsound hash noAuthorization wire path (nothing_is_authorized_today hash wire)

/-- **⚑ THE LOAD-BEARING COMPOSITION (`l4_pin_over_deployed_append_relocates_15`).** Suppose L1 lands
today's `note_shielded.root8()` as a carrier limb and L4 pins membership to it. The pin then HOLDS —
`acceptsPinned` is satisfied — for a spend of a leaf **no gate authorized**, and the accumulator
soundness the pin's conclusion needs is FALSE for that root. So the pin buys nothing: the trust that
was in the wire `merkle_root` is now in a tree the prover writes into. **Seam #15 relocates one level
up; it does not close.** (DESIGN §3.3.) -/
theorem l4_pin_over_deployed_append_relocates_15 (hash : List ℤ → ℤ) (auth : Note → Prop)
    (wire : ℤ) (path : List Level) (hnot : ¬ IsLedgerNote hash auth wire) :
    ∃ (committedRoot : ℤ) (p : Payload),
      acceptsPinned (Hair hash) committedRoot p
      ∧ p.leaf = deployedAppendLeaf wire
      ∧ ¬ IsLedgerNote hash auth p.leaf
      ∧ ¬ AccumulatorSound (Hair hash) (IsLedgerNote hash auth) committedRoot := by
  refine ⟨rootAfterAppend hash (deployedAppendLeaf wire) path,
          ⟨deployedAppendLeaf wire, path, rootAfterAppend hash (deployedAppendLeaf wire) path⟩,
          ⟨rfl, rfl⟩, rfl, hnot, ?_⟩
  exact deployed_append_unsound hash auth wire path hnot

/-- The same relocation at the deployed parameters — again with NO hypothesis. -/
theorem l4_pin_relocates_15_today (hash : List ℤ → ℤ) (wire : ℤ) (path : List Level) :
    ∃ (committedRoot : ℤ) (p : Payload),
      acceptsPinned (Hair hash) committedRoot p
      ∧ ¬ IsLedgerNote hash noAuthorization p.leaf
      ∧ ¬ AccumulatorSound (Hair hash) (IsLedgerNote hash noAuthorization) committedRoot := by
  obtain ⟨r, p, hacc, _, hnot, huns⟩ :=
    l4_pin_over_deployed_append_relocates_15 hash noAuthorization wire path
      (nothing_is_authorized_today hash wire)
  exact ⟨r, p, hacc, hnot, huns⟩

/-! ### §2.1 — the falsifier at the LITERAL `IsCommittedNote`, and why that predicate cannot carry it.

DESIGN §3.3 prices the wound as *"`AccumulatorSound` is FALSE … exactly the `NoteAccumulatorCR`
hypothesis `pin_accept_is_note_committed` requires"*. `NoteAccumulatorCR`'s note predicate is the
∃-image `IsCommittedNote`. The falsifier IS provable there — but only under a hypothesis that is NOT
free at a real Poseidon2, which is the honest sharpening this lane owes the design. -/

/-- **`deployed_append_breaks_noteAccumulatorCR` — the falsifier in the design's own words.** If the
appended wire value is outside the C6 image, `NoteAccumulatorCR` is FALSE for the post-append root:
the value in the set is not any note's commitment. Hash-agnostic, over all paths. -/
theorem deployed_append_breaks_noteAccumulatorCR (hash : List ℤ → ℤ) (wire : ℤ) (path : List Level)
    (hnot : ¬ IsCommittedNote hash wire) :
    ¬ NoteAccumulatorCR hash (rootAfterAppend hash (deployedAppendLeaf wire) path) := by
  intro hsound
  exact hnot (hsound wire path rfl)

/-- The C6 site is mod-p **surjective**: every field element is the note commitment of SOME preimage.
A property OF Poseidon2 (four free field inputs onto a ~2^31 codomain), stated as a hypothesis and used
only NEGATIVELY — to show that `¬ IsCommittedNote wire` is not a free hypothesis. -/
def C6Surjective (hash : List ℤ → ℤ) : Prop :=
  ∀ y : ℤ, ∃ v as ow rd : ℤ, y ≡ hash [v, as, ow, rd, 0, NS_FACT_MARK, 1] [ZMOD P]

theorem isCommittedNote_of_c6Surjective (hash : List ℤ → ℤ) (hsurj : C6Surjective hash) (leaf : ℤ) :
    IsCommittedNote hash leaf := hsurj leaf

/-- **⚑ THE SHARPENING (`noteAccumulatorCR_vacuous_of_c6Surjective`).** If the C6 site is surjective —
the expected behaviour of the real Poseidon2 — then `NoteAccumulatorCR` holds for **EVERY** root,
including the root of today's prover-written `note_shielded`. The ∃-image predicate is therefore
satisfied by the wound it was supposed to price: it asks that *some* opening exist, never that the
LEDGER authorized one. This does not weaken §2 — `deployed_append_unsound_today` stands with no
hypothesis — it relocates where the content lives, onto `IsLedgerNote`. -/
theorem noteAccumulatorCR_vacuous_of_c6Surjective (hash : List ℤ → ℤ) (hsurj : C6Surjective hash)
    (r : ℤ) : NoteAccumulatorCR hash r :=
  fun leaf _ _ => isCommittedNote_of_c6Surjective hash hsurj leaf

/-- The two facts side by side: under C6 surjectivity the design's stated falsifier is unavailable
(its hypothesis is false for every wire value) while the `IsLedgerNote` falsifier still fires. -/
theorem falsifier_survives_c6_surjectivity (hash : List ℤ → ℤ) (hsurj : C6Surjective hash)
    (wire : ℤ) (path : List Level) :
    (∀ w : ℤ, IsCommittedNote hash w)
    ∧ ¬ AccumulatorSound (Hair hash) (IsLedgerNote hash noAuthorization)
          (rootAfterAppend hash (deployedAppendLeaf wire) path) :=
  ⟨isCommittedNote_of_c6Surjective hash hsurj, deployed_append_unsound_today hash wire path⟩

/-! ## §3 — THE FIX, SOUND: the Shield-A append makes the accumulator sound, so the pin closes #15.

DESIGN §2.4: the minted object is `hash_fact(piVALUE,[piASSET, owner, randomness])` over an opening the
boundary gate validated, appended at the free index of `note_shielded` with `piROOT_BEFORE`
EXECUTOR-sourced. In-AIR this is `Emit.ShieldedNoteAppendDescriptor` (L2). Here: the construction fact
the append supplies, composed with the landed floor reduction. -/

/-- **The Shield-A append (DESIGN §2.4).** The minted leaf is the C6 commitment of the authorized
opening — never a wire byte string. -/
def shieldAppendLeaf (hash : List ℤ → ℤ) (n : Note) : ℤ := noteLeaf hash n

/-- **`shieldAppend_is_ledger_note` — the construction fact, no crypto.** What Shield-A appends is a
ledger-authorized note commitment, because the gate appends the commitment of the opening it just
authorized. This is precisely `noteAccumulatorCR_of_hashFloor`'s `members_are_notes` premise, and it is
exactly what the deployed append cannot supply. -/
theorem shieldAppend_is_ledger_note (hash : List ℤ → ℤ) (auth : Note → Prop) (n : Note) (hn : auth n) :
    IsLedgerNote hash auth (shieldAppendLeaf hash n) :=
  ⟨n, hn, Int.ModEq.refl _⟩

/-- Every member of the Shield-A accumulated set is an `IsCommittedNote` — the honest construction
premise of the landed floor reduction, discharged. -/
theorem shieldA_members_are_notes (hash : List ℤ → ℤ) (auth : Note → Prop) :
    ∀ leaf, IsLedgerNote hash auth leaf → IsCommittedNote hash leaf :=
  ledgerNote_isCommittedNote hash auth

/-- **⚑ THE FIX SOUND (`shieldA_noteAccumulatorCR`).** With the Shield-A append, `NoteAccumulatorCR`
**HOLDS** for the accumulated root under the SINGLE named Poseidon2 floor `FoldReachIsMember` (the
Merkle-root binding floor: only a genuine member folds to the committed root — the `SpineCommits8` /
`Compress8CR` shape, not an unbounded per-leaf assumption). The hypothesis `pin_accept_is_note_committed`
requires is now DISCHARGED, modulo one named hash floor — which is what "the pin closes #15" means. -/
theorem shieldA_noteAccumulatorCR (hash : List ℤ → ℤ) (auth : Note → Prop) (committedRoot : ℤ)
    (floor : FoldReachIsMember hash committedRoot (IsLedgerNote hash auth)) :
    NoteAccumulatorCR hash committedRoot :=
  noteAccumulatorCR_of_hashFloor hash committedRoot (IsLedgerNote hash auth)
    (shieldA_members_are_notes hash auth) floor

/-- **⚑ THE STRONGER CONCLUSION (`shieldA_pin_spends_authorized`).** Under the same floor, a pinned and
accepted spend spends a note the LEDGER AUTHORIZED — not merely one for which some opening exists. This
is the conclusion the deployed append cannot reach at any hash, and the one `IsLedgerNote` was
introduced to state. -/
theorem shieldA_pin_spends_authorized (hash : List ℤ → ℤ) (auth : Note → Prop) (committedRoot : ℤ)
    (floor : FoldReachIsMember hash committedRoot (IsLedgerNote hash auth))
    (p : Payload) (h : acceptsPinned (Hair hash) committedRoot p) :
    IsLedgerNote hash auth p.leaf := by
  obtain ⟨hmem, hpin⟩ := h
  exact floor p.leaf p.path (by rw [hmem, hpin])

/-- **⚑ THE COMPOSITION (`shieldA_pin_closes_15`).** Both halves at once, over the landed objects: a
pinned-accepted spend against the Shield-A accumulator spends a note that is (a) a genuine C6
commitment — via the landed `ShieldedSpendPortDischarge.pin_accept_is_note_committed`, whose
`NoteAccumulatorCR` floor is now discharged rather than assumed — and (b) ledger-authorized. -/
theorem shieldA_pin_closes_15 (hash : List ℤ → ℤ) (auth : Note → Prop) (committedRoot : ℤ)
    (floor : FoldReachIsMember hash committedRoot (IsLedgerNote hash auth))
    (p : Payload) (h : acceptsPinned (Hair hash) committedRoot p) :
    IsCommittedNote hash p.leaf ∧ IsLedgerNote hash auth p.leaf :=
  ⟨pin_accept_is_note_committed hash committedRoot
      (shieldA_noteAccumulatorCR hash auth committedRoot floor) p h,
   shieldA_pin_spends_authorized hash auth committedRoot floor p h⟩

/-- **`deshield_publishes_an_entered_value` (the exit, DESIGN §2.5).** A `Deshield` whose membership is
pinned to the Shield-A accumulator can only publish the value of a note a `Shield` actually entered:
the spent leaf opens to an authorized preimage. This is what makes L4's pin non-vacuous — and it is the
in-AIR half of §1's `run_conserves_supply`. -/
theorem deshield_publishes_an_entered_value (hash : List ℤ → ℤ) (auth : Note → Prop)
    (committedRoot : ℤ) (floor : FoldReachIsMember hash committedRoot (IsLedgerNote hash auth))
    (p : Payload) (h : acceptsPinned (Hair hash) committedRoot p) :
    ∃ n : Note, auth n ∧ p.leaf ≡ noteLeaf hash n [ZMOD P] :=
  shieldA_pin_spends_authorized hash auth committedRoot floor p h

/-! ## §4 — THE VALUE-ALIASING TOOTH: two encodings of one `u64` at one boundary.

DESIGN §5.1, the open tension this lane owes an answer to. The committed CLEARTEXT leaf carries
`split_u64(value).0` — the **low 30 bits** of the `u64`
(`circuit/src/effect_vm/helpers.rs:13-17`: `let lo = (val & 0x3FFF_FFFF) as u32;`, used at
`cell/src/commitment_set.rs:262` as the accumulator leaf's value column). The shielded C6 opening
carries the value as a BabyBear felt, i.e. reduced **mod p**, `p = 2013265921 < 2^31`. Neither
faithfully represents a `u64`, and they are DIFFERENT reductions. -/

/-- The image of a `u64` amount in the committed CLEARTEXT leaf's value column: the low 30 bits,
`split_u64(value).0`. -/
def clearLeafImage (v : ℕ) : ℕ := v % 1073741824

/-- The image of a `u64` amount in the SHIELDED C6 opening: the value reduced mod p. -/
def shieldFeltImage (v : ℕ) : ℤ := (v : ℤ) % P

/-- **⚑ THE ALIASING, both ways (`boundary_images_alias_both_ways`).** The two boundary images of a
`u64` amount conflate DIFFERENT pairs: `2^30` and `0` are identical to the cleartext leaf column and
distinct to the shielded opening; `p` and `0` are identical to the shielded opening and distinct to the
cleartext leaf column. So there is no single "boundary image" of a value, and a conservation check run
on either one alone admits an amount the other would reject. -/
theorem boundary_images_alias_both_ways :
    (∃ v₁ v₂ : ℕ, v₁ < 18446744073709551616 ∧ v₂ < 18446744073709551616 ∧ v₁ ≠ v₂ ∧
        clearLeafImage v₁ = clearLeafImage v₂ ∧ shieldFeltImage v₁ ≠ shieldFeltImage v₂)
    ∧ (∃ v₁ v₂ : ℕ, v₁ < 18446744073709551616 ∧ v₂ < 18446744073709551616 ∧ v₁ ≠ v₂ ∧
        shieldFeltImage v₁ = shieldFeltImage v₂ ∧ clearLeafImage v₁ ≠ clearLeafImage v₂) := by
  constructor
  · refine ⟨1073741824, 0, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · show (1073741824 : ℕ) % 1073741824 = 0 % 1073741824
      norm_num
    · show ((1073741824 : ℕ) : ℤ) % P ≠ ((0 : ℕ) : ℤ) % P
      norm_num [P]
  · refine ⟨2013265921, 0, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · show ((2013265921 : ℕ) : ℤ) % P = ((0 : ℕ) : ℤ) % P
      norm_num [P]
    · show (2013265921 : ℕ) % 1073741824 ≠ 0 % 1073741824
      norm_num

/-- **The aliased shield step.** The boundary gate's conservation check is performed on the value the
committed CLEARTEXT leaf can actually see — its low-30-bit column — rather than on the `u64`. The
spent note keeps its true value; the minted shielded note carries `vMint`, and the gate accepts because
the two agree in the leaf column. Everything else is the honest `Step.shield`. -/
inductive StepAliased : Boundary → Boundary → Prop where
  | shieldAliased (pre post sh : List Note) (n : Note) (vMint : ℕ)
      (halias : clearLeafImage n.value = clearLeafImage vMint) :
      StepAliased ⟨pre ++ n :: post, sh⟩ ⟨pre ++ post, { n with value := vMint } :: sh⟩

/-- **⚑ THE ALIASING TOOTH (`aliased_shield_inflates`).** A shield whose conservation check runs on the
cleartext leaf's own value column ACCEPTS a step that mints `2^30` units out of a note worth `0`: the
gate's check passes, and §1's ℤ supply invariant is broken by exactly `2^30`. Concrete, non-vacuous,
and unconditional. -/
theorem aliased_shield_inflates :
    ∃ b b' : Boundary, StepAliased b b' ∧ supply b' = supply b + 1073741824 := by
  refine ⟨⟨[⟨0, 0, 0, 0⟩], []⟩, ⟨[], [⟨1073741824, 0, 0, 0⟩]⟩, ?_, ?_⟩
  · exact StepAliased.shieldAliased [] [] [] ⟨0, 0, 0, 0⟩ 1073741824 (by norm_num [clearLeafImage])
  · simp [supply, totalZ]

/-- The same step is REJECTED by the honest ℤ obligation of §1: the leaving amount is `0` and the
entering amount is `2^30`, so no `Step.shield` relates these two states with a single public `v`. -/
theorem aliased_shield_violates_the_obligation :
    totalZ [(⟨0, 0, 0, 0⟩ : Note)] - totalZ ([] : List Note)
      ≠ totalZ [(⟨1073741824, 0, 0, 0⟩ : Note)] - totalZ ([] : List Note) := by
  simp [totalZ]

/-! ### §4.1 — what closes it. Two independent closures, both proved. -/

/-- **CLOSURE 1 — the amount cap (`cap_closes_clear_alias`).** Capping shieldable amounts below `2^30`
makes the cleartext leaf column injective, so the aliased check IS the exact check. -/
theorem cap_closes_clear_alias (v₁ v₂ : ℕ) (h₁ : v₁ < 1073741824) (h₂ : v₂ < 1073741824)
    (h : clearLeafImage v₁ = clearLeafImage v₂) : v₁ = v₂ := by
  simp only [clearLeafImage, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at h
  exact h

/-- The same cap also makes the shielded felt image injective (`2^30 < p`), so ONE cap closes both
sides of the boundary. -/
theorem cap_closes_felt_alias (v₁ v₂ : ℕ) (h₁ : v₁ < 1073741824) (h₂ : v₂ < 1073741824)
    (h : shieldFeltImage v₁ = shieldFeltImage v₂) : v₁ = v₂ := by
  have hp : (1073741824 : ℤ) < P := by norm_num [P]
  have c₁ : (v₁ : ℤ) < P := lt_trans (by exact_mod_cast h₁) hp
  have c₂ : (v₂ : ℤ) < P := lt_trans (by exact_mod_cast h₂) hp
  simp only [shieldFeltImage,
    Int.emod_eq_of_lt (Int.natCast_nonneg v₁) c₁,
    Int.emod_eq_of_lt (Int.natCast_nonneg v₂) c₂] at h
  exact_mod_cast h

/-- **⚑ CLOSURE 1, at the boundary (`cap_closes_aliased_shield`).** Under the cap, every aliased shield
step conserves the ℤ supply — the inflation of `aliased_shield_inflates` is unrepresentable. -/
theorem cap_closes_aliased_shield (pre post sh : List Note) (n : Note) (vMint : ℕ)
    (halias : clearLeafImage n.value = clearLeafImage vMint)
    (hcap₁ : n.value < 1073741824) (hcap₂ : vMint < 1073741824) :
    supply ⟨pre ++ post, { n with value := vMint } :: sh⟩ = supply ⟨pre ++ n :: post, sh⟩ := by
  have hv : vMint = n.value := (cap_closes_clear_alias n.value vMint hcap₁ hcap₂ halias).symm
  subst hv
  simp only [supply, totalZ_append, totalZ_cons]
  ring

/-- **CLOSURE 2 — the wide encoding.** The deployed full-`u64` carrier splits the value into FOUR
16-bit limbs (`U64_LIMBS = 4`, `LIMB_BITS = 16`,
`circuit-prove/src/shielded/wide_value_binding.rs:37-40`). -/
def wide4 (v : ℕ) : List ℕ :=
  [v % 65536, v / 65536 % 65536, v / 4294967296 % 65536, v / 281474976710656 % 65536]

/-- **⚑ CLOSURE 2, sound (`wide4_injective_on_u64`).** The 16-bit-limb encoding is INJECTIVE on the
whole `u64` range — no cap needed, and no aliasing anywhere in `[0, 2^64)`. Carrying the boundary value
in the wide encoding is therefore a complete closure of §4, where the cap is a partial one. -/
theorem wide4_injective_on_u64 (v₁ v₂ : ℕ) (h₁ : v₁ < 18446744073709551616)
    (h₂ : v₂ < 18446744073709551616) (h : wide4 v₁ = wide4 v₂) : v₁ = v₂ := by
  simp only [wide4, List.cons.injEq, and_true] at h
  obtain ⟨e0, e1, e2, e3⟩ := h
  omega

/-- The wide encoding SEPARATES the very pair the cleartext leaf column conflates (`2^30` vs `0`) — so
closure 2 is not merely injective in the abstract, it bites on the concrete alias of §4. -/
theorem wide4_separates_the_alias :
    clearLeafImage 1073741824 = clearLeafImage 0 ∧ wide4 1073741824 ≠ wide4 0 := by
  constructor
  · show (1073741824 : ℕ) % 1073741824 = 0 % 1073741824
    norm_num
  · simp [wide4]

/-! ## §5 — non-vacuity canaries (a false `#guard` is a build error). -/

-- The two boundary images of a `u64` really are different reductions: `2^30` is `0` to the cleartext
-- leaf column but `2^30` to the shielded opening.
#guard decide (clearLeafImage 1073741824 = 0) = true
#guard decide (shieldFeltImage 1073741824 = 1073741824) = true
-- … and `p` is `0` to the shielded opening but not to the cleartext leaf column.
#guard decide (shieldFeltImage 2013265921 = 0) = true
#guard decide (clearLeafImage 2013265921 = 939524097) = true
-- The cap makes the leaf column faithful on its own range (`2^30 - 1` survives).
#guard decide (clearLeafImage 1073741823 = 1073741823) = true
-- The wide encoding separates the aliased pair and round-trips a large `u64`.
#guard decide (wide4 1073741824 = [0, 16384, 0, 0]) = true
#guard decide (wide4 0 = [0, 0, 0, 0]) = true
#guard decide (wide4 18446744073709551615 = [65535, 65535, 65535, 65535]) = true
-- The supply of a two-note boundary is the ℤ sum of both sides — the §1 invariant is about a real
-- (inhabited, non-zero) quantity, not an empty model.
#guard decide (supply ⟨[⟨7, 0, 0, 0⟩], [⟨5, 0, 0, 0⟩]⟩ = 12) = true
#guard decide (supply ⟨[], [⟨12, 0, 0, 0⟩]⟩ = 12) = true

/-! ## §6 — axiom hygiene. -/

#assert_axioms noteLeaf_isCommittedNote
#assert_axioms shield_leaving_eq_entering
#assert_axioms step_conserves_supply
#assert_axioms run_conserves_supply
#assert_axioms modp_identity_is_not_the_obligation
#assert_axioms ledgerNote_isCommittedNote
#assert_axioms appended_leaf_is_member
#assert_axioms deployed_append_leaf_is_wire_verbatim
#assert_axioms deployed_append_is_free
#assert_axioms deployed_append_unsound
#assert_axioms nothing_is_authorized_today
#assert_axioms deployed_append_unsound_today
#assert_axioms l4_pin_over_deployed_append_relocates_15
#assert_axioms l4_pin_relocates_15_today
#assert_axioms deployed_append_breaks_noteAccumulatorCR
#assert_axioms isCommittedNote_of_c6Surjective
#assert_axioms noteAccumulatorCR_vacuous_of_c6Surjective
#assert_axioms falsifier_survives_c6_surjectivity
#assert_axioms shieldAppend_is_ledger_note
#assert_axioms shieldA_members_are_notes
#assert_axioms shieldA_noteAccumulatorCR
#assert_axioms shieldA_pin_spends_authorized
#assert_axioms shieldA_pin_closes_15
#assert_axioms deshield_publishes_an_entered_value
#assert_axioms boundary_images_alias_both_ways
#assert_axioms aliased_shield_inflates
#assert_axioms aliased_shield_violates_the_obligation
#assert_axioms cap_closes_clear_alias
#assert_axioms cap_closes_felt_alias
#assert_axioms cap_closes_aliased_shield
#assert_axioms wide4_injective_on_u64
#assert_axioms wide4_separates_the_alias

end Dregg2.Circuit.ShieldedOnRampPin
