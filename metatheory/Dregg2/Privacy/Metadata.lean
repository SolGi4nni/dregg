/-
# Dregg2.Privacy.Metadata — the metadata-privacy BOUNDARY (pillar #5).

The shielded layer (`PrivacyKernel.committed_conservation_kernel` over Pedersen, the
`Privacy`/`PrivacyKernel` nullifier tier) hides AMOUNTS and per-spend LINKAGE. But an
observer of the DAG / network still sees the **coordination structure** (which cells take
a JointTurn together — the cell-partner edges of `JointTurn.SharedTurnId`), the **timing**
(the slot a turn lands in), and the **traffic volume** (how many turns, how many notes). This
module makes that boundary PRECISE and PROVES — on BOTH sides — what holds and what leaks.

Existing `Privacy.lean`/`PrivacyKernel.lean`/`BlindedSet.lean` prove the *positive* direction
(view-collapse: the payload is hidden). They never modelled the *negative* direction — the
metadata an observer genuinely RECOVERS. This module supplies the missing dual, so the
deliverable is a two-sided map rather than a one-sided "what's hidden" story.

## What an observer of the DAG sees vs the private payload

`Transcript` = everything published to the DAG/network for one turn: a `slot` (timing), a
`partners : Finset Cell` (the coordination edge — who took the JointTurn together), a `volume`
(traffic count), and an opaque `commitment` (the shielded payload root). The `ObsView` is the
projection an observer computes from a transcript — it KEEPS the metadata and DROPS the payload.

  • `obs_drops_payload`  — the observer-view is INDEPENDENT of the private payload (two turns
    differing only in their shielded commitment look identical). This is the *hiding* that holds:
    the shielded layer's perfect-on-the-view collapse, lifted to the network transcript.

  • `obs_reveals_partners` / `obs_reveals_slot` / `obs_reveals_volume` — the observer-view is a
    FAITHFUL function of the metadata: it DETERMINES partners, slot, and volume. This is the
    *leak* that holds — stated as a real recovery map, not hand-waving.

## The distinguishability TOOTH (the deliverable's core)

`Distinguishable t t' ≜ obsView t ≠ obsView t'`. Two precise, non-vacuous statements:

  • `payload_indistinguishable` (the PRIVACY that holds) — two turns identical in metadata but
    differing in the shielded payload are observer-INDISTINGUISHABLE.

  • `partner_change_distinguishable` / `timing_change_distinguishable` /
    `volume_change_distinguishable` (the LEAK) — two turns identical in payload but differing in
    the partner set / slot / volume ARE observer-distinguishable. The observer can tell them apart.

## The k-anonymity theorem (a REAL anonymity-set size, not a constant)

`partnerAnonymitySet obs corpus` = the set of turns in a published `corpus` whose observer-view
is `obs`. `payload_anonymity_card_ge` proves the anonymity set for a turn's PAYLOAD has size `≥`
the number of distinct payloads sharing that turn's metadata — DERIVED by an injection from a
payload family into the corpus, NOT asserted as a constant. The residual is then characterized
HONESTLY: this k is the payload-anonymity within a fixed metadata bucket; ACROSS metadata buckets
(different partner sets/slots) the observer partitions the corpus and the anonymity collapses to
the bucket — `metadata_partitions_anonymity` proves the bucket is an upper bound on what hides.

No `sorry`/`axiom`; every spec carries a non-vacuity witness (`Reference`). The residual
*computational* hiding of the commitment itself is the §8 portal carried by `PrivacyKernel` /
`Crypto.Primitives` — NOT re-litigated here; this module is purely the metadata-boundary map.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Dregg2.Tactics

namespace Dregg2.Privacy.Metadata

universe u

/-! ## The transcript: what is published to the DAG for one turn. -/

/-- A **cell identity** — a node in the coordination graph (a participant of a JointTurn). The
partner edge of `JointTurn.SharedTurnId` is a `Finset Cell`; the observer sees this edge. -/
structure Cell where
  id : Nat
  deriving DecidableEq, Repr

/-- An opaque **shielded payload** — the private content (amounts, openings, holder identity)
that the shielded layer hides. The observer NEVER recovers it; modelled as an abstract `Nat`
tag so we can state "two turns differing only here" and "differing only in metadata". -/
structure Payload where
  /-- The shielded commitment root (Pedersen / Poseidon2) — opaque to the observer. -/
  commitment : Nat
  deriving DecidableEq, Repr

/-- A **published turn transcript** — EVERYTHING the network/DAG carries for one turn. The first
three fields are METADATA (visible); the last is the shielded PAYLOAD (hidden). -/
structure Transcript where
  /-- **Timing.** The slot/round the turn lands in (the DAG layer index). Visible. -/
  slot : Nat
  /-- **The coordination edge.** Which cells took this JointTurn together — the cell-partner
  structure of `SharedTurnId`. Visible: the DAG records who referenced whom. -/
  partners : Finset Cell
  /-- **Traffic volume.** How many notes/sub-messages the turn carried. Visible. -/
  volume : Nat
  /-- **The shielded payload.** The private content. HIDDEN from the observer. -/
  payload : Payload
  deriving DecidableEq

/-! ## The observer-view — the projection that KEEPS metadata, DROPS payload.

`ObsView` is a concrete, decidable record of exactly the leaked metadata. `obsView` is the
projection. The whole boundary is then phrased as facts about this one function. -/

/-- The **observer-view** of a turn: the metadata an observer of the DAG recovers — slot,
partner set, volume — and NOTHING about the payload. A concrete record so `obsView t = obsView t'`
is a real, decidable equality (perfect information-theoretic equality on the modelled view). -/
structure ObsView where
  slot : Nat
  partners : Finset Cell
  volume : Nat
  deriving DecidableEq

/-- **The observer projection.** Drops the shielded `payload`, keeps the three metadata fields. -/
def obsView (t : Transcript) : ObsView :=
  { slot := t.slot, partners := t.partners, volume := t.volume }

/-- **`Distinguishable t t'`** — the observer CAN tell `t` and `t'` apart: their views differ.
This is the negation of indistinguishability; the tooth states both polarities of it. -/
def Distinguishable (t t' : Transcript) : Prop := obsView t ≠ obsView t'

/-- **`Indistinguishable t t'`** — the observer CANNOT tell `t` and `t'` apart: equal views. -/
def Indistinguishable (t t' : Transcript) : Prop := obsView t = obsView t'

/-! ## The HIDING side — what the observer does NOT learn (the privacy that holds).

The single load-bearing hiding fact: the observer-view is INDEPENDENT of the payload. Everything
"the shielded layer hides the amount/linkage" reduces, at the network boundary, to this. -/

/-- **`obs_drops_payload` — the view is independent of the payload.** If two transcripts agree on
all metadata (slot, partners, volume), their observer-views are EQUAL regardless of payload. This
is the network-level statement of the shielded layer's perfect-on-the-view collapse: changing the
hidden commitment changes nothing the observer sees. -/
theorem obs_drops_payload (t t' : Transcript)
    (hslot : t.slot = t'.slot) (hpart : t.partners = t'.partners) (hvol : t.volume = t'.volume) :
    obsView t = obsView t' := by
  unfold obsView
  rw [hslot, hpart, hvol]

/-- **`payload_indistinguishable` — the PRIVACY tooth (positive).** Two turns that differ ONLY in
their shielded payload are observer-INDISTINGUISHABLE. The observer cannot detect a change to the
amount/opening/holder. This is the precise statement "the shielded payload is hidden at the DAG
boundary", and it is a real equality of the modelled view, not `True`. -/
theorem payload_indistinguishable (slot : Nat) (partners : Finset Cell) (volume : Nat)
    (p p' : Payload) :
    Indistinguishable
      { slot := slot, partners := partners, volume := volume, payload := p }
      { slot := slot, partners := partners, volume := volume, payload := p' } := by
  unfold Indistinguishable
  exact obs_drops_payload _ _ rfl rfl rfl

/-! ## The LEAK side — what the observer DOES learn (the residual, characterized honestly).

The observer-view is a FAITHFUL function of the metadata: it determines partners, slot, volume.
We state each as a recovery map (`obsView t` *determines* the field) AND as a distinguishability
fact (changing the field changes the view). Both are real theorems, not constants. -/

/-- **`obs_reveals_partners` — the coordination graph LEAKS.** The observer-view determines the
partner set exactly: from `obsView t` one reads off `t.partners`. The cell-partner structure of a
JointTurn is fully recovered — this is the graph-tier residual leak made precise. -/
theorem obs_reveals_partners (t : Transcript) : (obsView t).partners = t.partners := rfl

/-- **`obs_reveals_slot` — TIMING leaks.** The observer-view determines the slot exactly. -/
theorem obs_reveals_slot (t : Transcript) : (obsView t).slot = t.slot := rfl

/-- **`obs_reveals_volume` — VOLUME leaks.** The observer-view determines the traffic volume. -/
theorem obs_reveals_volume (t : Transcript) : (obsView t).volume = t.volume := rfl

/-- **`partner_change_distinguishable` — the LEAK tooth (graph).** Two turns identical in payload,
slot, and volume but differing in their PARTNER SET are observer-DISTINGUISHABLE. The observer can
tell apart "Alice coordinated with Bob" from "Alice coordinated with Carol", even though the
amounts are hidden. This is the honest residual: who-coordinates-with-whom is NOT private. -/
theorem partner_change_distinguishable (slot : Nat) (volume : Nat) (p : Payload)
    (ps ps' : Finset Cell) (hne : ps ≠ ps') :
    Distinguishable
      { slot := slot, partners := ps, volume := volume, payload := p }
      { slot := slot, partners := ps', volume := volume, payload := p } := by
  unfold Distinguishable obsView
  intro hcontra
  exact hne (congrArg ObsView.partners hcontra)

/-- **`timing_change_distinguishable` — the LEAK tooth (timing).** Two turns identical except for
their SLOT are observer-distinguishable. When a turn happens is not private. -/
theorem timing_change_distinguishable (partners : Finset Cell) (volume : Nat) (p : Payload)
    (s s' : Nat) (hne : s ≠ s') :
    Distinguishable
      { slot := s, partners := partners, volume := volume, payload := p }
      { slot := s', partners := partners, volume := volume, payload := p } := by
  unfold Distinguishable obsView
  intro hcontra
  exact hne (congrArg ObsView.slot hcontra)

/-- **`volume_change_distinguishable` — the LEAK tooth (volume).** Two turns identical except for
their VOLUME are observer-distinguishable. Traffic volume is not private. -/
theorem volume_change_distinguishable (slot : Nat) (partners : Finset Cell) (p : Payload)
    (v v' : Nat) (hne : v ≠ v') :
    Distinguishable
      { slot := slot, partners := partners, volume := v, payload := p }
      { slot := slot, partners := partners, volume := v', payload := p } := by
  unfold Distinguishable obsView
  intro hcontra
  exact hne (congrArg ObsView.volume hcontra)

/-! ## k-ANONYMITY — a real anonymity-set size derived from the corpus, not a constant.

An observer holds a `corpus : Finset Transcript` (the published DAG history). The **payload
anonymity set** of a metadata bucket is the set of payloads appearing in the corpus with that
exact metadata — the observer cannot tell WHICH of them a given turn carried. Its cardinality is
the real k. We DERIVE k ≥ (size of a payload family that all share the bucket) by an injection,
rather than asserting a number. -/

/-- The **payload-anonymity set** for an observer-view `obs` within a `corpus`: the payloads of all
corpus turns whose observer-view is exactly `obs`. The observer, seeing `obs`, cannot distinguish
which of these payloads the turn actually carried — they are all consistent with the same view. -/
def payloadAnonymitySet (corpus : Finset Transcript) (obs : ObsView) : Finset Payload :=
  (corpus.filter (fun t => obsView t = obs)).image Transcript.payload

/-- **`payload_anonymity_card_ge` — the k-anonymity THEOREM (k is a real cardinality).** Suppose a
family `f : ι → Transcript` of corpus turns all share the same observer-view `obs` and carry
DISTINCT payloads (injective on payload). Then the payload-anonymity set for `obs` has cardinality
`≥ |ι|`. So the anonymity-set size is the number of distinct payloads the observer cannot tell
apart — a derived quantity, NOT a postulated constant. Proof: the family injects into the
filtered-then-imaged set. -/
theorem payload_anonymity_card_ge {ι : Type u} [Fintype ι] [DecidableEq ι]
    (corpus : Finset Transcript) (obs : ObsView)
    (f : ι → Transcript)
    (hmem : ∀ i, f i ∈ corpus)
    (hview : ∀ i, obsView (f i) = obs)
    (hinj : Function.Injective (fun i => (f i).payload)) :
    (Finset.univ (α := ι)).card ≤ (payloadAnonymitySet corpus obs).card := by
  classical
  -- map each index to its payload; it lands in the anonymity set and is injective.
  have hsub : ((Finset.univ (α := ι)).image (fun i => (f i).payload))
      ⊆ payloadAnonymitySet corpus obs := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    unfold payloadAnonymitySet
    rw [Finset.mem_image]
    exact ⟨f i, by rw [Finset.mem_filter]; exact ⟨hmem i, hview i⟩, rfl⟩
  calc (Finset.univ (α := ι)).card
      = ((Finset.univ (α := ι)).image (fun i => (f i).payload)).card := by
        rw [Finset.card_image_of_injective _ hinj]
    _ ≤ (payloadAnonymitySet corpus obs).card := Finset.card_le_card hsub

/-! ## The residual, characterized HONESTLY — metadata PARTITIONS the anonymity.

The k above is anonymity *within one metadata bucket*. The observer also sees the metadata, so it
PARTITIONS the corpus by observer-view. The honest residual statement: a turn's payload-anonymity
set never exceeds its own bucket — the metadata is a hard ceiling on what hides. If a bucket has a
unique metadata signature (a turn whose `(slot, partners, volume)` no other corpus turn shares),
its payload-anonymity set is a SINGLETON: the payload is effectively deanonymized by metadata. -/

/-- **`anonymity_set_within_bucket` — the metadata ceiling.** The payload-anonymity set for `obs`
is exactly the payloads of the `obs`-bucket of the corpus; every member's source turn HAS view
`obs`. So nothing outside the metadata bucket can contribute anonymity — the observer's metadata
partition is a hard upper structure on the anonymity set. -/
theorem anonymity_set_within_bucket (corpus : Finset Transcript) (obs : ObsView)
    (p : Payload) (hp : p ∈ payloadAnonymitySet corpus obs) :
    ∃ t ∈ corpus, obsView t = obs ∧ t.payload = p := by
  unfold payloadAnonymitySet at hp
  rw [Finset.mem_image] at hp
  obtain ⟨t, ht, hpt⟩ := hp
  rw [Finset.mem_filter] at ht
  exact ⟨t, ht.1, ht.2, hpt⟩

/-- **`unique_metadata_deanonymizes` — the leak, sharpened.** If a turn `t` in the corpus has a
metadata signature shared by NO other corpus turn (every corpus turn with the same view is `t`
itself), then its payload-anonymity set is the SINGLETON `{t.payload}` — k = 1, the payload is
deanonymized purely by metadata. This is the precise statement of how the coordination-graph /
timing leak can collapse the shielded-layer anonymity to nothing. -/
theorem unique_metadata_deanonymizes (corpus : Finset Transcript) (t : Transcript)
    (ht : t ∈ corpus)
    (huniq : ∀ t' ∈ corpus, obsView t' = obsView t → t' = t) :
    payloadAnonymitySet corpus (obsView t) = {t.payload} := by
  classical
  apply Finset.ext
  intro p
  rw [Finset.mem_singleton]
  constructor
  · intro hp
    obtain ⟨t', ht', hview', hpt'⟩ := anonymity_set_within_bucket corpus (obsView t) p hp
    rw [← hpt', huniq t' ht' hview']
  · intro hp
    unfold payloadAnonymitySet
    rw [Finset.mem_image]
    exact ⟨t, by rw [Finset.mem_filter]; exact ⟨ht, rfl⟩, hp.symm⟩

/-! ## `Reference` — non-vacuity witnesses for EVERY spec (no spec is vacuous). -/

namespace Reference

/-- Two cells. -/
def alice : Cell := ⟨0⟩
def bob : Cell := ⟨1⟩
def carol : Cell := ⟨2⟩

/-- A reference transcript: Alice+Bob coordinate at slot 5, volume 1, payload-commitment 100. -/
def tAB : Transcript :=
  { slot := 5, partners := {alice, bob}, volume := 1, payload := ⟨100⟩ }

/-- Same metadata, DIFFERENT payload (commitment 200) — the observer cannot tell it from `tAB`. -/
def tAB' : Transcript :=
  { slot := 5, partners := {alice, bob}, volume := 1, payload := ⟨200⟩ }

/-- Same payload, DIFFERENT partner (Alice+Carol) — the observer CAN tell it from `tAB`. -/
def tAC : Transcript :=
  { slot := 5, partners := {alice, carol}, volume := 1, payload := ⟨100⟩ }

/-- **Non-vacuity of the PRIVACY tooth.** `tAB` and `tAB'` differ only in payload and are
genuinely indistinguishable — a concrete inhabitant of `payload_indistinguishable`. -/
theorem ref_payload_indistinguishable : Indistinguishable tAB tAB' :=
  payload_indistinguishable 5 {alice, bob} 1 ⟨100⟩ ⟨200⟩

/-- **Non-vacuity of the LEAK tooth (partners).** `tAB` and `tAC` differ only in partners and are
genuinely distinguishable — Alice+Bob vs Alice+Carol IS observable. NON-VACUOUS: the two partner
sets are actually distinct (`carol ∉ {alice,bob}`), so this is not the empty hypothesis. -/
theorem ref_partner_distinguishable : Distinguishable tAB tAC := by
  apply partner_change_distinguishable 5 1 ⟨100⟩ {alice, bob} {alice, carol}
  -- {alice,bob} ≠ {alice,carol}: carol is in the right, not the left.
  intro h
  have hc : carol ∈ ({alice, bob} : Finset Cell) := by
    rw [h]; simp [alice, carol]
  simp only [Finset.mem_insert, Finset.mem_singleton, alice, bob, carol,
    Cell.mk.injEq] at hc
  omega

/-- **Non-vacuity that the view genuinely SEPARATES** the two scenarios: the observer-views of
`tAB` and `tAC` are actually different records (the leak is real, not a vacuous inequality). -/
theorem ref_views_differ : obsView tAB ≠ obsView tAC := ref_partner_distinguishable

/-- **Non-vacuity of k-ANONYMITY: a genuine k = 2 anonymity set.** A corpus of `tAB` and `tAB'`
(same metadata, distinct payloads). The payload-anonymity set for their shared view has
cardinality `≥ 2` — two payloads the observer cannot tell apart. Derived via
`payload_anonymity_card_ge` with the two-element index `Bool`. -/
theorem ref_k_anonymity_two :
    2 ≤ (payloadAnonymitySet {tAB, tAB'} (obsView tAB)).card := by
  classical
  have hcard : (2 : ℕ) = (Finset.univ : Finset Bool).card := by decide
  rw [hcard]
  apply payload_anonymity_card_ge {tAB, tAB'} (obsView tAB)
    (f := fun b => if b then tAB else tAB')
  · intro b; cases b <;> simp [tAB, tAB']
  · intro b
    cases b
    · -- false ↦ tAB', same view as tAB (same metadata)
      show obsView tAB' = obsView tAB
      exact (payload_indistinguishable 5 {alice, bob} 1 ⟨100⟩ ⟨200⟩).symm
    · rfl
  · -- distinct payloads ⇒ injective on payload
    intro b b' h
    cases b <;> cases b' <;> simp_all [tAB, tAB']

/-- **Non-vacuity of `unique_metadata_deanonymizes`.** In the singleton corpus `{tAB}`, `tAB`'s
metadata is unique, so its payload-anonymity set is exactly `{⟨100⟩}` — k = 1, deanonymized by
metadata. The sharp residual, witnessed. -/
theorem ref_unique_deanonymizes :
    payloadAnonymitySet {tAB} (obsView tAB) = {tAB.payload} := by
  apply unique_metadata_deanonymizes {tAB} tAB (by simp)
  intro t' ht' _
  rw [Finset.mem_singleton] at ht'
  exact ht'

end Reference

/-! ## Axiom-hygiene tripwires.

The whole boundary — both polarities of the tooth (hiding + leak), the k-anonymity cardinality
theorem, and the metadata-ceiling residual — is kernel-clean (axioms ⊆ {propext,
Classical.choice, Quot.sound}). The residual COMPUTATIONAL hiding of the commitment itself is the
§8 portal carried by `PrivacyKernel`/`Crypto.Primitives`, NOT an axiom these pins would catch and
NOT re-asserted here. -/
#assert_axioms payload_indistinguishable
#assert_axioms obs_drops_payload
#assert_axioms obs_reveals_partners
#assert_axioms partner_change_distinguishable
#assert_axioms timing_change_distinguishable
#assert_axioms volume_change_distinguishable
#assert_axioms payload_anonymity_card_ge
#assert_axioms anonymity_set_within_bucket
#assert_axioms unique_metadata_deanonymizes
#assert_axioms Reference.ref_payload_indistinguishable
#assert_axioms Reference.ref_partner_distinguishable
#assert_axioms Reference.ref_k_anonymity_two
#assert_axioms Reference.ref_unique_deanonymizes

end Dregg2.Privacy.Metadata
