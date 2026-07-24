/-
# Dregg2.Verify.ExistsImageVacuity — the STANDING FALSIFIER for the ∃-IMAGE HOLE CLASS:
  a predicate `∃ w, x = f w` read as if it established provenance / authorization / membership.

## The class

A predicate of the shape

    def IsGood (f : α → β) (x : β) : Prop := ∃ w : α, x = f w

says exactly one thing: **`x` is in the image of `f`**. It excludes precisely the elements OUTSIDE
`Set.range f` and nothing else (`inImage_excludes_exactly_offRange`). When `f` is a hash/commitment
site with enough free inputs to be surjective at the deployed parameters, `Set.range f` is
everything, the predicate holds of every `x` (`inImage_vacuous_of_surjective`), and every floor
whose CONCLUSION is that predicate is discharged at every root by surjectivity alone
(`imageFloor_vacuous_of_surjective`) — the floor prices nothing.

The class was found live in `Dregg2.Circuit.ShieldedSpendPortDischarge.IsCommittedNote:109`
(`∃ v as ow rd, leaf ≡ hash [v, as, ow, rd, 0, NS_FACT_MARK, 1] [ZMOD P]`) and priced by
`Dregg2.Circuit.ShieldedOnRampPin.noteAccumulatorCR_vacuous_of_c6Surjective:363`. §1–§4 here restate
that argument ONCE, abstractly, as the reusable tooth; §5 lands a SECOND live instance found by the
corpus sweep.

## The discriminator (why this is not a blanket indictment of every existential)

An ∃-image predicate carries content iff one of two things holds:

  * **an AUTHORIZATION conjunct** — `∃ w, auth w ∧ x = f w` (`InImageAuth`). Strictly stronger
    (`inImageAuth_strictly_stronger`), and NOT vacuated by surjectivity: with an empty `auth` it is
    false of everything (`inImageAuth_false_of_no_auth`). This is the `IsLedgerNote` repair
    (`ShieldedOnRampPin.lean:237`).
  * **INJECTIVITY of `f`** on the domain of interest — then the ∃ is a DECODE: the witness is unique
    and every property of it transfers (`inImage_determines_witness_of_injective`,
    `property_transfers_of_injective`). This is why `CircuitSoundness.StateDecode` (whose
    `CommitSurface` carries `commit_binds`) and `CapRootBridge.capOpensTo` (functional under
    `Poseidon2SpongeCR`) are NOT instances.

And the counting rule that decides "is `f` plausibly surjective at deployed parameters":

  * `k ≥ 2` free BabyBear inputs onto ONE BabyBear felt — domain `p^k`, codomain `p` — counting can
    never refute surjectivity (`counting_is_silent_when_domain_dominates`), so the predicate must be
    treated as vacuous, not hoped safe.
  * a BOUNDED domain onto a WIDE 8-felt codomain (`p` vs `p^8`) — surjectivity is REFUTED by counting
    (`exists_not_inImage_of_card_lt`, `narrow_into_wide_is_nonvacuous`), so those sites are NOT
    instances of the class.

## §5 — the second live instance: `ShieldedTransferStark.StarkResidual`

`Dregg2.Circuit.ShieldedTransferStark.StarkResidual:181` is the NAMED obligation of the deployed
`ShieldedTransfer` effect's `verify_stark_side` (`circuit-prove/src/shielded/transfer.rs:146`) over
the deployed 3-slot public-input tuple `[nullifier, merkle_root, value_binding]`:

    def StarkResidual (H : List Int → Int) (member : Int → Int → Prop) (pi : ShieldedSpendPI) : Prop :=
      ∃ (commitment key value randomness : Int),
        member commitment pi.merkleRoot
        ∧ pi.nullifier    = H [commitment, key]
        ∧ pi.valueBinding = H [value, randomness]
        ∧ 0 ≤ value

Its docstring reads the third conjunct as *"value-binding is the committed leaf value (C7a)"* and the
fourth as *"value is range-valid"*. Neither is what the `Prop` says. `value` and `randomness` occur
in **no conjunct that mentions `commitment`** — the only other place `value` occurs is its own
`0 ≤ value`, which the existential picks it to satisfy. So the bound value is tied neither to the
member commitment nor to the member leaf, and the range conjunct ranges over a value nothing pins:

  * `starkResidual_indep_of_valueBinding` — under `C7aSurjective` (the two-free-input analogue of
    `ShieldedOnRampPin.C6Surjective`), the residual's truth value does not depend on `pi[2]` at all:
    the deployed public input `value_binding` is unconstrained by the obligation.
  * `starkResidual_vacuous` — at any root that has ONE member whose nullifier site is surjective in
    its free `key`, `StarkResidual` holds for **EVERY** public-input triple, forged ones included, and
    `starkResidual_floor_prices_nothing` inhabits `starkResidual_of_floor`'s `extract` premise with no
    crypto whatsoever.
  * `StarkResidualTied` is the corrected shape — ONE opening `(value, asset, owner, rand)` both
    commits the member leaf AND opens the value binding — with
    `starkResidualTied_implies_starkResidual` (a refinement) and `starkResidual_not_tied` (strict:
    a concrete `H`/`member`/`pi` satisfying the residual and refuting the tied one).

This is NOT a rewrite of `ShieldedTransferStark`: the corrected predicate is authored alongside, and
§6 names the sites to fix.

## Scope

Abstract teeth plus one instantiation. No descriptor, no deployed byte, no other module's definition
touched. No `sorry`, no `admit`, no `native_decide`; `#assert_axioms` ⊆ {propext, Classical.choice,
Quot.sound}.
-/
import Dregg2.Circuit.ShieldedTransferStark
import Dregg2.Tactics
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

namespace Dregg2.Verify.ExistsImageVacuity

set_option autoImplicit false

universe u v

/-! ## §1 — the class, abstractly. -/

/-- **The ∃-image predicate**: `x` is in the image of `f`. This is the whole content of every
`def IsGood x := ∃ w, x = f w` in the corpus — no more, no less. -/
def InImage {α : Type u} {β : Type v} (f : α → β) (y : β) : Prop := ∃ w : α, y = f w

/-- **The repaired shape**: `x` is the image of a witness the ledger/gate AUTHORIZED. The conjunct
`auth w` is the content the bare image predicate never had. -/
def InImageAuth {α : Type u} {β : Type v} (f : α → β) (auth : α → Prop) (y : β) : Prop :=
  ∃ w : α, auth w ∧ y = f w

/-- **⚑ THE TOOTH (`inImage_vacuous_of_surjective`).** A surjective site makes its ∃-image predicate
true of EVERYTHING. This is `ShieldedOnRampPin.isCommittedNote_of_c6Surjective` with the hash and the
note shape abstracted away. -/
theorem inImage_vacuous_of_surjective {α : Type u} {β : Type v} (f : α → β)
    (hsurj : Function.Surjective f) (y : β) : InImage f y := by
  obtain ⟨w, hw⟩ := hsurj y
  exact ⟨w, hw.symm⟩

/-- The converse: an ∃-image predicate that holds of everything IS a surjectivity claim. So
"vacuous" and "surjective" are the same statement, and the class question is exactly the counting
question. -/
theorem inImage_vacuous_iff_surjective {α : Type u} {β : Type v} (f : α → β) :
    (∀ y, InImage f y) ↔ Function.Surjective f := by
  constructor
  · intro h y; obtain ⟨w, hw⟩ := h y; exact ⟨w, hw.symm⟩
  · intro h y; exact inImage_vacuous_of_surjective f h y

/-- **The exclusion power, exactly.** An ∃-image predicate refutes `y` iff `y` is off the range of
`f`. Whatever else the docstring claims it rules out — a forged leaf, an unauthorized note, a wrong
value — it does not. -/
theorem inImage_excludes_exactly_offRange {α : Type u} {β : Type v} (f : α → β) (y : β) :
    ¬ InImage f y ↔ y ∉ Set.range f := by
  constructor
  · intro h hmem; obtain ⟨w, hw⟩ := hmem; exact h ⟨w, hw.symm⟩
  · intro h hin; obtain ⟨w, hw⟩ := hin; exact h ⟨w, hw.symm⟩

/-- **⚑ THE FLOOR COLLAPSE (`imageFloor_vacuous_of_surjective`).** Generalizes
`ShieldedOnRampPin.noteAccumulatorCR_vacuous_of_c6Surjective`: whenever a named crypto floor has the
shape "everything REACHABLE from the committed object satisfies `Q`" and `Q` is an ∃-image predicate
over a surjective site, the floor holds — for EVERY reachability relation and at EVERY root,
including a root the prover wrote. The floor prices nothing. -/
theorem imageFloor_vacuous_of_surjective {α : Type u} {β : Type v} {ι : Type v} (f : α → β)
    (hsurj : Function.Surjective f) (Reach : ι → β → Prop) (r : ι) :
    ∀ y, Reach r y → InImage f y :=
  fun y _ => inImage_vacuous_of_surjective f hsurj y

/-- **⚑ THE POLARITY TOOTH (`hypothesis_guard_stripped`).** A vacuous ∃-image in HYPOTHESIS position
is not merely harmless: it strips the theorem of its guard. Whatever the theorem concludes under
"`y` is a genuine image", it concludes for every `y` — the forged ones included. -/
theorem hypothesis_guard_stripped {α : Type u} {β : Type v} (f : α → β)
    (hsurj : Function.Surjective f) (Q : β → Prop) (h : ∀ y, InImage f y → Q y) : ∀ y, Q y :=
  fun y => h y (inImage_vacuous_of_surjective f hsurj y)

/-! ## §2 — the counting discriminator: when is the site plausibly surjective at deployed params? -/

/-- Counting refutes surjectivity when the domain is strictly smaller than the codomain. -/
theorem not_surjective_of_card_lt {α β : Type} [Fintype α] [Fintype β] (f : α → β)
    (h : Fintype.card α < Fintype.card β) : ¬ Function.Surjective f := by
  intro hs
  exact absurd (Fintype.card_le_of_surjective f hs) (not_le.mpr h)

/-- **The (c)-classification, as a theorem.** A site whose domain is strictly smaller than its
codomain has an ∃-image predicate that REFUTES something — it is not an instance of the class. -/
theorem exists_not_inImage_of_card_lt {α β : Type} [Fintype α] [Fintype β] (f : α → β)
    (h : Fintype.card α < Fintype.card β) : ∃ y, ¬ InImage f y := by
  by_contra hcon
  push Not at hcon
  exact not_surjective_of_card_lt f h ((inImage_vacuous_iff_surjective f).mp hcon)

/-- **The wide-codomain non-instance, concretely.** A BOUNDED domain (one felt's worth of freedom)
into a WIDE 8-felt digest cannot be surjective — `p < p^8` for `p ≥ 2` — so an 8-felt commitment's
∃-image predicate has real exclusion power. This is why `MembersAt8`-shaped 8-felt sites are graded
(c) and the 1-felt shielded sites are graded (a). -/
theorem narrow_into_wide_is_nonvacuous (p : ℕ) (hp : 2 ≤ p) (f : Fin p → (Fin 8 → Fin p)) :
    ∃ y, ¬ InImage f y := by
  refine exists_not_inImage_of_card_lt f ?_
  have hcard : Fintype.card (Fin 8 → Fin p) = p ^ 8 := by
    simp
  rw [Fintype.card_fin, hcard]
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ 8 := Nat.pow_lt_pow_right hp (by norm_num)

/-- **The 1-felt case: counting is SILENT.** Two free BabyBear inputs onto one BabyBear felt give a
domain of `p * p` against a codomain of `p`, so `not_surjective_of_card_lt` cannot fire — no counting
argument will ever refute surjectivity there. A site where counting is silent must be treated as
surjective (hence its ∃-image predicate as vacuous), never as safe by default. -/
theorem counting_is_silent_when_domain_dominates (p : ℕ) (hp : 1 ≤ p) : p ≤ p * p :=
  Nat.le_mul_of_pos_left p hp

/-! ## §3 — repair 1: the authorization conjunct. -/

/-- The repaired predicate refines the bare one — every conclusion drawn at `InImageAuth` is in
particular a conclusion at `InImage`. (`ShieldedOnRampPin.ledgerNote_isCommittedNote`, abstracted.) -/
theorem inImageAuth_le_inImage {α : Type u} {β : Type v} (f : α → β) (auth : α → Prop) (y : β)
    (h : InImageAuth f auth y) : InImage f y := by
  obtain ⟨w, _, hw⟩ := h
  exact ⟨w, hw⟩

/-- **The authorization conjunct survives surjectivity.** With nothing authorized, the repaired
predicate is FALSE of every `y` — however surjective the site is. This is the abstract
`ShieldedOnRampPin.nothing_is_authorized_today`, and it is the whole reason the repair is a repair. -/
theorem inImageAuth_false_of_no_auth {α : Type u} {β : Type v} (f : α → β) {auth : α → Prop}
    (hnone : ∀ w, ¬ auth w) (y : β) : ¬ InImageAuth f auth y := by
  rintro ⟨w, hw, _⟩
  exact hnone w hw

/-- **⚑ STRICTLY STRONGER (`inImageAuth_strictly_stronger`).** A concrete separation: over the
identity site with an empty authorization, `InImage` holds of `0` and `InImageAuth` does not. The two
predicates are not interchangeable, so replacing one by the other is a real strengthening. -/
theorem inImageAuth_strictly_stronger :
    ∃ (f : ℤ → ℤ) (auth : ℤ → Prop) (y : ℤ), InImage f y ∧ ¬ InImageAuth f auth y := by
  refine ⟨id, fun _ => False, 0, ⟨0, rfl⟩, ?_⟩
  rintro ⟨_, hfalse, _⟩
  exact hfalse

/-! ## §4 — repair 2: injectivity turns the ∃ into a DECODE. -/

/-- Under injectivity the ∃-image predicate determines its witness — the existential is a decode, not
a shrug, and the site is not an instance of the class. -/
theorem inImage_determines_witness_of_injective {α : Type u} {β : Type v} {f : α → β}
    (hinj : Function.Injective f) {y : β} {w w' : α} (h : y = f w) (h' : y = f w') : w = w' :=
  hinj (h ▸ h')

/-- …and therefore every property of the genuine witness transfers to any witness the predicate
supplies. This is the content `CommitSurface.commit_binds` buys for `StateDecode`, and
`Poseidon2SpongeCR` buys for `CapRootBridge.capOpensTo`. -/
theorem property_transfers_of_injective {α : Type u} {β : Type v} {f : α → β}
    (hinj : Function.Injective f) (P : α → Prop) {w w' : α} (hP : P w) (h : f w' = f w) : P w' := by
  rwa [hinj h]

/-! ## §5 — THE SECOND LIVE INSTANCE: `ShieldedTransferStark.StarkResidual`. -/

section StarkResidualInstance

open Dregg2.Circuit.ShieldedTransferStark (ShieldedSpendPI StarkResidual)

/-- **The C7a site's surjectivity** — the two-free-input analogue of
`ShieldedOnRampPin.C6Surjective`. `value_binding = hash_fact(value, [randomness, 0, 0])` is a
Poseidon2 squeeze to ONE BabyBear felt (`p = 2013265921 < 2^31`) with TWO free field inputs, i.e. a
`p^2 → p` map: counting is silent (`counting_is_silent_when_domain_dominates`), so this is the
expected behaviour of the real permutation. Stated as a HYPOTHESIS, used only to price a predicate —
never as an axiom, exactly as `C6Surjective` is. The nonnegativity is carried inside because the
residual's fourth conjunct is `0 ≤ value`. -/
def C7aSurjective (H : List Int → Int) : Prop :=
  ∀ y : Int, ∃ value randomness : Int, 0 ≤ value ∧ y = H [value, randomness]

/-- The nullifier site's surjectivity AT a root that has at least one member: some member commitment
`c` exists whose nullifier site `H [c, ·]` covers the felt in its one free `key`. -/
def NullifierSiteSurjectiveAt (H : List Int → Int) (member : Int → Int → Prop) (root : Int) : Prop :=
  ∃ c : Int, member c root ∧ ∀ y : Int, ∃ key : Int, y = H [c, key]

/-- **⚑ THE RESIDUAL DOES NOT SEE `pi[2]` (`starkResidual_indep_of_valueBinding`).** Under
`C7aSurjective`, `StarkResidual` has the same truth value at any two public-input triples agreeing on
`nullifier` and `merkleRoot`. The deployed `value_binding` public input is therefore unconstrained by
the obligation the STARK is said to discharge: the docstring's *"value-binding is the committed leaf
value"* and *"value is range-valid"* are claims the `Prop` does not make. -/
theorem starkResidual_indep_of_valueBinding {H : List Int → Int} {member : Int → Int → Prop}
    (hsurj : C7aSurjective H) (pi pi' : ShieldedSpendPI)
    (hn : pi.nullifier = pi'.nullifier) (hr : pi.merkleRoot = pi'.merkleRoot)
    (h : StarkResidual H member pi) : StarkResidual H member pi' := by
  obtain ⟨c, key, _, _, hmem, hnf, _, _⟩ := h
  obtain ⟨v', r', hv0, hy⟩ := hsurj pi'.valueBinding
  exact ⟨c, key, v', r', hr ▸ hmem, hn ▸ hnf, hy, hv0⟩

/-- The same statement in the form that names the slot: swapping the published `value_binding` for an
arbitrary felt `y` preserves the residual, both ways. -/
theorem starkResidual_valueBinding_carries_nothing {H : List Int → Int}
    {member : Int → Int → Prop} (hsurj : C7aSurjective H) (pi : ShieldedSpendPI) (y : Int) :
    StarkResidual H member pi ↔ StarkResidual H member { pi with valueBinding := y } :=
  ⟨starkResidual_indep_of_valueBinding hsurj pi _ rfl rfl,
   starkResidual_indep_of_valueBinding hsurj _ pi rfl rfl⟩

/-- **⚑ THE VACUITY (`starkResidual_vacuous`).** At any root with ONE member whose nullifier site is
surjective, `StarkResidual` holds for **EVERY** public-input triple — a forged nullifier and a forged
value binding included. The mirror of `noteAccumulatorCR_vacuous_of_c6Surjective`, at the deployed
`ShieldedTransfer` obligation. -/
theorem starkResidual_vacuous {H : List Int → Int} {member : Int → Int → Prop}
    (hsurj : C7aSurjective H) (pi : ShieldedSpendPI)
    (hnf : NullifierSiteSurjectiveAt H member pi.merkleRoot) : StarkResidual H member pi := by
  obtain ⟨c, hmem, hall⟩ := hnf
  obtain ⟨key, hk⟩ := hall pi.nullifier
  obtain ⟨v, r, hv0, hvb⟩ := hsurj pi.valueBinding
  exact ⟨c, key, v, r, hmem, hk, hvb, hv0⟩

/-- **⚑ THE FLOOR PRICES NOTHING (`starkResidual_floor_prices_nothing`).**
`ShieldedTransferStark.starkResidual_of_floor` takes `extract : accepted → StarkResidual H member pi`
as the FRI/AIR floor at the hiding uni-STARK config. Under the two surjectivities that premise is
INHABITED with no crypto at all, for every `accepted` — so the floor, as stated, certifies nothing
about the nullifier or the value binding. What it can still certify is the membership conjunct, which
is why the repair is the tie, not the deletion. -/
theorem starkResidual_floor_prices_nothing {H : List Int → Int} {member : Int → Int → Prop}
    (hsurj : C7aSurjective H) (pi : ShieldedSpendPI)
    (hnf : NullifierSiteSurjectiveAt H member pi.merkleRoot) (accepted : Prop) :
    accepted → StarkResidual H member pi :=
  fun _ => starkResidual_vacuous hsurj pi hnf

/-- **THE CORRECTED SHAPE (`StarkResidualTied`).** ONE opening `(value, asset, owner, rand)` does all
the work: it commits the leaf `H [value, asset, owner, rand]` that is a `member` of the tree, that
leaf is what the nullifier is derived from, and the SAME `value`/`rand` open the published value
binding. This is what the C6/C7a constraints of `spend_circuit.rs` actually relate; the free-witness
version drops the ties. -/
def StarkResidualTied (H : List Int → Int) (member : Int → Int → Prop) (pi : ShieldedSpendPI) : Prop :=
  ∃ (value asset owner rand key : Int),
    member (H [value, asset, owner, rand]) pi.merkleRoot
    ∧ pi.nullifier = H [H [value, asset, owner, rand], key]
    ∧ pi.valueBinding = H [value, rand]
    ∧ 0 ≤ value

/-- The corrected shape REFINES the deployed one: every tied residual is a residual, so nothing
proved downstream of `StarkResidual` is lost by strengthening to `StarkResidualTied`. -/
theorem starkResidualTied_implies_starkResidual {H : List Int → Int} {member : Int → Int → Prop}
    (pi : ShieldedSpendPI) (h : StarkResidualTied H member pi) : StarkResidual H member pi := by
  obtain ⟨value, asset, owner, rand, key, hmem, hnf, hvb, hv0⟩ := h
  exact ⟨H [value, asset, owner, rand], key, value, rand, hmem, hnf, hvb, hv0⟩

/-- A separating site: a 2-argument hash that hits `7` and a 4-argument hash that never does. -/
def sepH : List Int → Int := fun xs => if xs.length = 2 then 7 else 0

/-- The membership predicate of the separating instance: only the commitment `7` is in the tree at
root `1`. -/
def sepMember : Int → Int → Prop := fun c r => c = 7 ∧ r = 1

/-- The separating public inputs: nullifier `7`, root `1`, value binding `7`. -/
def sepPi : ShieldedSpendPI := ⟨7, 1, 7⟩

/-- **⚑ STRICTLY STRONGER, CONCRETELY (`starkResidual_not_tied`).** The deployed residual HOLDS at
`(sepH, sepMember, sepPi)` while the tied residual FAILS: the free `value`/`randomness` satisfy the
value-binding conjunct through a 2-argument image, but no note opening commits a member leaf. So the
gap between the two predicates is real and inhabited — the ties are not a notational nicety. -/
theorem starkResidual_not_tied :
    StarkResidual sepH sepMember sepPi ∧ ¬ StarkResidualTied sepH sepMember sepPi := by
  constructor
  · exact ⟨7, 0, 0, 0, ⟨rfl, rfl⟩, by decide, by decide, by decide⟩
  · rintro ⟨value, asset, owner, rand, key, ⟨hc, _⟩, _, _, _⟩
    simp [sepH] at hc

end StarkResidualInstance

/-! ## §6 — the sites, graded.

**(a) GENUINELY VACUOUS — the class fires; the vacuity is proved.**

  1. `Dregg2.Circuit.ShieldedSpendPortDischarge.IsCommittedNote:109` — four free field inputs onto one
     BabyBear felt. Priced by `ShieldedOnRampPin.noteAccumulatorCR_vacuous_of_c6Surjective:363`; the
     repair `IsLedgerNote:237` is landed. Consumers still concluding at the bare predicate, and thus
     still to be re-pointed at `IsLedgerNote`:
     `ShieldedSpendPortDischarge.emitted_leaf_isCommittedNote:132`,
     `ShieldedSpendPortDischarge.emitted_accept_is_committed:156`,
     `ShieldedSpendPortDischarge.pin_accept_is_note_committed:182`,
     `ShieldedSpendPortResidual.emitted_membership_chain:281`,
     `ShieldedSpendPortResidual.noteAccumulatorCR_of_hashFloor:319`.
  2. `Dregg2.Circuit.ShieldedTransferStark.StarkResidual:181` — §5 above. The `value`/`randomness`
     witnesses appear in no other conjunct; the `key` witness appears in no other conjunct. Sites to
     fix: the `def` itself (strengthen to `StarkResidualTied`, or carry the tie as a separate named
     conjunct), and `starkResidual_of_floor:194`, whose `extract` premise is inhabited without crypto
     under `starkResidual_floor_prices_nothing`. The §5 floor list at `ShieldedTransferStark.lean:205`
     should gain the tie as a fourth named floor; it currently names only StarkSound,
     Pedersen/Bulletproofs, blake3-CR and the leaf↔leg link.

**(b) SAVED BY CONTEXT — the missing content is supplied at the use site.**

  * `Dregg2.Circuit.CircuitSoundness.WitnessDecodes:563` / `StateDecode:190` — the ∃ over `pre`/`post`
    is a DECODE, not a shrug: `CommitSurface.commit_binds` makes it functional
    (`stateDecode_pre_faithful:204`, `stateDecode_post_faithful:213`). §4's injectivity repair.
  * `Dregg2.Circuit.LightClientFusion.dProduced:90` — the apex ∃-body already carries the
    authorization conjunct `kstep pi.effect pre post` alongside the two commitment equations. This is
    the shape §3 prescribes, landed.
  * `Dregg2.Circuit.CapRootBridge.capOpensTo:154` / `CapsEncodes:141` — functional under
    `Poseidon2SpongeCR` (`capOpensTo_functional:157`); `CapsEncodes` additionally carries
    `FaithfulCapTree hash caps h`.
  * `Dregg2.Circuit.MapMerkleRoot.opensToMerkle:220` / `writesToMerkle:225` (and the `8` variants at
    `:561` / `:566`) — the existential is over a whole sorted heap with `Heap.get h k = o` pinned, and
    both root equations constrain the SAME heap.
  * `Dregg2.Circuit.Emit.EffectVmEmitCapReshape.ProductionAuthorized:374` — carries
    `IssuerEntry A e`, the authorization conjunct, next to the opening.
  * `Dregg2.Circuit.DeployedCapTree.DeployedEncodes:319` — the ∃ over `leafAt` is qualified by
    `DeployedFaithful`, and `deployedCapOpen_implies_authorizedB` draws its content from that
    faithfulness, not from the `MembersAt` opening.
  * `Dregg2.Crypto.Lattice.IsMLWESample:77` / `Fips204FullDim.IsSparseSign:650` /
    `FriWeightingTransfer.IsRSCodeword:381` — each ∃-image carries its bound (`nrm ≤ β`, `T.card = τ`,
    `p.degree < k`); the bound IS the content.

**(c) NOT AN INSTANCE.**

  * `Dregg2.Circuit.DeployedCapTree.MembersAt:211` / `MembersAt8:909`,
    `DeployedHeapTree.MembersAt8:203`, `DeployedFieldsTree.MembersAt8:203`,
    `ShieldedMerkleRootPin.inCommittedTree:121` — Merkle openings in PROVER-OBLIGATION polarity: the
    prover must EXHIBIT the path, so the content is computational (preimage/collision hardness), not
    the Prop-level image. The unbounded path length is a faithfulness defect already toothed at
    `Dregg2.Circuit.VacuitySweepTeeth` §2, not a vacuity.
  * `Dregg2.Circuit.AirChecksSatisfied.MainAirAccept:233` — the ∃ over `quot`/`zerofier` is pinned by
    `zerofier i = 0` on trace rows and FORCES the residual to vanish (`mainAirAccept_forces_residual`).
  * `Dregg2.Crypto.TurnAuthSignature.Authorized:76` — `AgentSigned` is `opaque` precisely so the ∃ is
    not an image predicate.
  * `Dregg2.Crypto.Rom*Eff` / `NarrowBreakEff` / `Sc*RomEff` / `Blake3Collision` /
    `SpongeCollision` — BREAK events in NEGATIVE polarity: easy satisfiability makes the floor
    `¬ Eff` stronger, not weaker.
  * `Dregg2.Crypto.Lattice.MSISHard:70` / `MLWESearchHard:86` — the dual defect (an existence
    REFUTATION used as hardness), already doc-marked BROKEN in place with its own teeth in
    `CryptoFloorTeeth`.
  * `Dregg2.Circuit.Emit.BlindedMembershipRefine.blindedMembership_exists_hidden:232` — the ∃ is
    deliberate unlinkability packaging of a trace the theorem already has, and it carries
    `MembersUnderRoot4` alongside the blinding image.
-/

/-! ## §7 — non-vacuity canaries (a false `#guard` is a build error). -/

-- The separating hash really does distinguish the arities the two predicates hash at.
#guard decide (sepH [7, 0] = 7) = true
#guard decide (sepH [0, 0, 0, 0] = 0) = true
#guard decide (sepH [0, 0] = 7) = true
-- …so no 4-argument opening can name the only member commitment `7`.
#guard decide (sepPi.nullifier = 7) = true
#guard decide (sepPi.merkleRoot = 1) = true
#guard decide (sepPi.valueBinding = 7) = true

/-! ## §8 — axiom hygiene. -/

#assert_axioms inImage_vacuous_of_surjective
#assert_axioms inImage_vacuous_iff_surjective
#assert_axioms inImage_excludes_exactly_offRange
#assert_axioms imageFloor_vacuous_of_surjective
#assert_axioms hypothesis_guard_stripped
#assert_axioms not_surjective_of_card_lt
#assert_axioms exists_not_inImage_of_card_lt
#assert_axioms narrow_into_wide_is_nonvacuous
#assert_axioms counting_is_silent_when_domain_dominates
#assert_axioms inImageAuth_le_inImage
#assert_axioms inImageAuth_false_of_no_auth
#assert_axioms inImageAuth_strictly_stronger
#assert_axioms inImage_determines_witness_of_injective
#assert_axioms property_transfers_of_injective
#assert_axioms starkResidual_indep_of_valueBinding
#assert_axioms starkResidual_valueBinding_carries_nothing
#assert_axioms starkResidual_vacuous
#assert_axioms starkResidual_floor_prices_nothing
#assert_axioms starkResidualTied_implies_starkResidual
#assert_axioms starkResidual_not_tied

end Dregg2.Verify.ExistsImageVacuity
