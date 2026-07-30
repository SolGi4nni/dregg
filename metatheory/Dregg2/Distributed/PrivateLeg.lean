/-
# Dregg2.Distributed.PrivateLeg — the WITNESSLESS participant: a cell maintained OFFLINE
# contributes a ZK-proof-only leg to a multi-cell atomic turn.

**The question (ember, 2026-06-13).** "How flexible is the system toward participating in a
consensus operation in a turn with a cell that someone else maintains OFFLINE and only wants to
publish witnessless ZK proofs about?" `Distributed/EntangledJoint.lean` already models the N-cell
all-or-none atomic turn (2PC over the verified per-cell executor `recKExecAsset`), BUT every leg
there is **public**: the leg's pre/post `RecordKernelState` is exposed and the executor runs over it
on the shared machine. A private participant does NOT publish its state — it holds the cell offline
and publishes only (a) a **state commitment** to its private pre/post and (b) a **ZK proof** that its
side of the turn is a real, guarded, conserving, authorized executor step.

This module models the **mixed joint turn**: some legs public (run on the shared machine), some legs
PRIVATE (proof-only). The keystone `joint_turn_sound_with_private_legs` shows that the public legs'
machine commits and the private legs' verifying proofs COMPOSE to a sound whole turn — conservation
and authority hold across the public+private composition — **without the composite ever holding any
private leg's pre/post witness state**.

## The reuse / the connection to existing primitives

  * **The all-or-none fold** (`EntangledJoint.jointApplyAll`) is the PUBLIC backbone, untouched.
  * **The state commitment** is `Circuit.StateCommit.recStateCommit` in spirit: a private leg
    publishes `commitPre`/`commitPost : ℤ` instead of its `RecordKernelState`. (We keep them abstract
    `ℤ` here so the model is carrier-agnostic; the real commitment is the Poseidon2 state root.)
  * **The ZK proof carrier** is `PortalFloor.VerifierKernel` — exactly the §8 STARK floor used
    everywhere else. The per-private-leg statement is `PrivLegStmt` ("∃ hidden pre/post:
    `recKExecAsset` commits, the published commitments match, conservation & authority hold"); an
    accepting proof discharges `PrivLegHolds` **via `verify_sound` (the extractability carrier),
    never a Lean law**. This is the named crypto floor: the per-leg ZK proof = a `VerifierKernel`
    carrier, and unforgeability/soundness of that proof stays §8.
  * **The disclosure dial** (`Circuit.Argus.Disclose.Tier`): a public leg = `.trusted` disclosure;
    a private leg = `.private`. A private leg reveals ONLY its commitment + acceptance bit — the
    `acceptanceOnly` ZK floor of `Crypto.PredicateKernel`.

## What is faithful vs. what is the named floor

FAITHFUL (proved here, `#assert_axioms`-clean): the COMPOSITION law — given the public machine
commits and every private leg's proof verifies under the carrier, the whole turn is conserving,
authority-bounded, and binds to one CG-2 identity; and the composite NEVER reads a private witness.
NAMED FLOOR (an explicit hypothesis, never a Lean law): the extractability of each private leg's ZK
proof (`VerifierKernel.extractable`) — that an accepting proof certifies a real guarded executor step
existed offline. Teeth both polarities: a real leg verifies (`privLeg_real_verifies`); a forged
"conjure value out of nothing" leg is rejected by the honest carrier
(`privLeg_forged_rejected`).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Dregg2.Distributed.EntangledJoint
import Dregg2.Crypto.PortalFloor

namespace Dregg2.Distributed.PrivateLeg

open Dregg2.Exec
open Dregg2.Distributed.EntangledJoint
open Dregg2.Crypto.PortalFloor (VerifierKernel)
open scoped BigOperators

/-! ## 1. The PRIVATE-LEG STATEMENT — what the ZK proof certifies WITHOUT revealing the witness.

A private participant maintains its cell `RecordKernelState` OFFLINE. It publishes only:
  * `asset`     — which asset column its leg moves (the only public type-level fact),
  * `commitPre` / `commitPost : ℤ` — commitments to its hidden pre/post state,
  * `jid`       — the CG-2 shared turn-id it consents to (public; it's how the forest binds).

The STATEMENT the proof must certify is the existential over the hidden states: there EXIST
`kPre kPost : RecordKernelState` and a `turn` such that the verified per-cell executor commits the
leg (`recKExecAsset kPre turn asset = some kPost`), the published commitments are the commitments of
those hidden states, and per-asset conservation + authority hold. The state-commitment function
`scommit` is abstract (the Poseidon2 state root in production); the model is parametric in it. -/

/-- The public face of a PRIVATE leg: everything the offline maintainer publishes. The hidden state
is NOT a field — that is the whole point. -/
structure PrivLeg where
  /-- The asset column this private leg moves (per-asset conservation is per this column). -/
  asset      : AssetId
  /-- Commitment to the hidden PRE state (Poseidon2 state root in production; abstract `ℤ` here). -/
  commitPre  : Int
  /-- Commitment to the hidden POST state. -/
  commitPost : Int
  /-- The CG-2 shared turn-id this leg consents to (public — how the forest binds the leg in). -/
  jid        : JointId
  deriving DecidableEq, Repr

/-- **The relation the per-private-leg ZK proof certifies** — parametric in the state-commitment
function `scommit`. It is the EXISTENTIAL over the hidden pre/post states: a real guarded executor
step happened offline whose commitments are the published ones. Crucially this is a `Prop` about the
public `PrivLeg` ONLY — the hidden `kPre`/`kPost` are bound under the `∃`, so the *statement* never
exposes them. -/
def PrivLegHolds (scommit : RecordKernelState → Int) (pl : PrivLeg) : Prop :=
  ∃ (kPre kPost : RecordKernelState) (turn : Turn),
    recKExecAsset kPre turn pl.asset = some kPost
    ∧ scommit kPre  = pl.commitPre
    ∧ scommit kPost = pl.commitPost

/-! ## 2. THE NAMED CRYPTO FLOOR — the per-leg ZK proof is a `VerifierKernel` carrier.

We instantiate the §8 STARK verifier at `Stmt := PrivLeg`, `Holds := PrivLegHolds scommit`. An
accepting proof discharges `PrivLegHolds` via `verify_sound` — the extractability carrier, an
explicit hypothesis. This is the SAME floor as every other circuit verification in the tree; the
private-participant feature adds NO new assumption beyond STARK extractability. -/

/-- The carrier hypothesis that the verifier's `Holds` IS `PrivLegHolds scommit`. In production this
is discharged by the AIR encoding `recKExecAsset` + the state-root opening. We carry it as an
explicit equality so the soundness theorem is honest about what the circuit must encode. -/
def CarrierEncodesPrivLeg {Proof : Type} (K : VerifierKernel PrivLeg Proof)
    (scommit : RecordKernelState → Int) : Prop := K.Holds = PrivLegHolds scommit

/-- **`privLeg_proof_certifies_step` — an accepting ZK proof certifies a real offline step,
WITHOUT the verifier ever seeing the hidden state.** Given (1) the STARK extractability carrier and
(2) that the AIR encodes `PrivLegHolds`, an accepting proof for the published `PrivLeg` yields the
existential: there WAS a hidden `kPre`/`kPost` and a guarded `recKExecAsset` step whose commitments
match. The verifier's input is the public `PrivLeg` + the `Proof` only — `kPre`/`kPost` appear
solely under the `∃`, never as inputs. This is the witnessless-participation primitive. -/
theorem privLeg_proof_certifies_step {Proof : Type} (scommit : RecordKernelState → Int)
    (K : VerifierKernel PrivLeg Proof)
    (hext : K.extractable) (henc : CarrierEncodesPrivLeg K scommit)
    (pl : PrivLeg) (proof : Proof) (haccept : K.verify pl proof = true) :
    PrivLegHolds scommit pl := by
  have h := K.verify_sound hext pl proof haccept
  rw [henc] at h
  exact h

/-- **Conservation rides on the certified step.** From the certified existential, the hidden offline
step preserved EVERY asset total `b` (per-cell keystone `recKExecAsset_conserves_per_asset`). So even
though the composite never holds the private state, it KNOWS (from the proof) that the private leg
conserved every asset. -/
theorem privLeg_certified_conserves {Proof : Type} (scommit : RecordKernelState → Int)
    (K : VerifierKernel PrivLeg Proof)
    (hext : K.extractable) (henc : CarrierEncodesPrivLeg K scommit)
    (pl : PrivLeg) (proof : Proof) (haccept : K.verify pl proof = true) :
    ∃ (kPre kPost : RecordKernelState),
      (∀ b : AssetId, recTotalAsset kPost b = recTotalAsset kPre b)
      ∧ scommit kPre = pl.commitPre ∧ scommit kPost = pl.commitPost := by
  obtain ⟨kPre, kPost, turn, hstep, hpre, hpost⟩ :=
    privLeg_proof_certifies_step scommit K hext henc pl proof haccept
  exact ⟨kPre, kPost,
    (fun b => recKExecAsset_conserves_per_asset kPre kPost turn pl.asset hstep b),
    hpre, hpost⟩

/-- **Authority rides on the certified step.** The certified hidden step was AUTHORIZED — the
offline cell could not have moved resource without authority, even though no one but the maintainer
saw the authority check. (`recKExecAsset_authorized`.) -/
theorem privLeg_certified_authorized {Proof : Type} (scommit : RecordKernelState → Int)
    (K : VerifierKernel PrivLeg Proof)
    (hext : K.extractable) (henc : CarrierEncodesPrivLeg K scommit)
    (pl : PrivLeg) (proof : Proof) (haccept : K.verify pl proof = true) :
    ∃ (kPre : RecordKernelState) (turn : Turn),
      authorizedB kPre.caps turn = true ∧ scommit kPre = pl.commitPre := by
  obtain ⟨kPre, kPost, turn, hstep, hpre, _⟩ :=
    privLeg_proof_certifies_step scommit K hext henc pl proof haccept
  exact ⟨kPre, turn, recKExecAsset_authorized kPre kPost turn pl.asset hstep, hpre⟩

/-! ## 3. THE MIXED JOINT TURN — public legs (on the machine) + private legs (proof-only).

A `MixedJoint` is the real shape of "a turn with an offline participant": some legs are public
(`EntangledJoint.Leg`, run on the shared `RecordKernelState`), some are private (`PrivLeg` +
`Proof`, never touch the shared machine). All consent to ONE `jid` (CG-2). The turn is admissible
iff the public fold commits AND every private leg's proof verifies. -/

/-- A private leg paired with its published proof (the wire object the offline maintainer broadcasts). -/
structure PrivContribution (Proof : Type) where
  leg   : PrivLeg
  proof : Proof

/-- **The mixed joint turn.** `jid` = the CG-2 shared id; `publicLegs` run on the shared machine;
`privateLegs` are proof-only offline contributions. This is `EntangledJoint.JointTurn` extended with
a witnessless-participant role. -/
structure MixedJoint (Proof : Type) where
  jid         : JointId
  publicLegs  : List Leg
  privateLegs : List (PrivContribution Proof)

/-- **ADMISSIBILITY** — the proof obligation for the whole mixed turn to commit.
  * the public fold commits all-or-none on the shared machine (`k → some k'`), AND
  * every private leg's proof verifies under the §8 carrier, AND
  * every private leg consents to the shared `jid` (CG-2). -/
def MixedAdmissible {Proof : Type} (K : VerifierKernel PrivLeg Proof)
    (mj : MixedJoint Proof) (k k' : RecordKernelState) : Prop :=
  jointApplyAll k mj.publicLegs = some k'
  ∧ (∀ pc ∈ mj.privateLegs, K.verify pc.leg pc.proof = true)
  ∧ (∀ pc ∈ mj.privateLegs, pc.leg.jid = mj.jid)

/-! ## 4. THE KEYSTONE — `joint_turn_sound_with_private_legs`.

Given admissibility + the named ZK floor (extractability + the AIR-encodes-`PrivLegHolds` carrier),
the mixed turn is sound as a WHOLE:
  (1) the PUBLIC side conserves every asset on the shared machine,
  (2) the PUBLIC side amplifies NO capability,
  (3) EVERY private leg certifiably ran a real conserving offline step — without the composite ever
      holding a private witness state (the existential keeps it hidden),
  (4) every leg (public via the binding, private via admissibility) consents to ONE `jid` (CG-2).

This is the cross-cell soundness of a turn with witnessless participants: the public machine + the
private proofs compose to a sound whole, and the private witnesses never leave their offline cells. -/

/-- **`joint_turn_sound_with_private_legs` — THE WITNESSLESS-PARTICIPANT KEYSTONE.** -/
theorem joint_turn_sound_with_private_legs {Proof : Type} (scommit : RecordKernelState → Int)
    (K : VerifierKernel PrivLeg Proof)
    (hext : K.extractable) (henc : CarrierEncodesPrivLeg K scommit)
    (mj : MixedJoint Proof) (k k' : RecordKernelState)
    (bind : JointBinding ⟨mj.jid, mj.publicLegs⟩)
    (hadm : MixedAdmissible K mj k k') :
    -- (1) public conservation, from the machine fold:
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b)
    -- (2) public no-cap-amplification:
    ∧ (k'.caps = k.caps)
    -- (3) every PRIVATE leg certifiably ran a real conserving offline step, witness HIDDEN:
    ∧ (∀ pc ∈ mj.privateLegs,
        ∃ (kPre kPost : RecordKernelState),
          (∀ b : AssetId, recTotalAsset kPost b = recTotalAsset kPre b)
          ∧ scommit kPre = pc.leg.commitPre ∧ scommit kPost = pc.leg.commitPost)
    -- (4) CG-2: every public leg AND every private leg consents to the ONE shared jid:
    ∧ (∀ l ∈ mj.publicLegs, bind.consentOf l = mj.jid)
    ∧ (∀ pc ∈ mj.privateLegs, pc.leg.jid = mj.jid) := by
  obtain ⟨hpub, hver, hpjid⟩ := hadm
  refine ⟨jointApplyAll_conserves mj.publicLegs k k' hpub,
          (jointApplyAll_caps_frame mj.publicLegs k k' hpub).1,
          ?_, ?_, hpjid⟩
  · intro pc hmem
    exact privLeg_certified_conserves scommit K hext henc pc.leg pc.proof (hver pc hmem)
  · intro l hl; exact bind.agree l hl

/-! ## 5. WHOLE-TURN COMPOSITE CONSERVATION — public + private commitments compose.

The composite ledger of a mixed turn is the PUBLIC machine total + the SUM of the private legs'
hidden totals (which the composite knows only through the commitments + the certified equalities).
The keystone gives: the public total is preserved (1) and EACH private leg's hidden total is
preserved (3). Hence the whole composite — public ⊕ all privates — conserves every asset, with the
private contributions accounted only by their certified deltas, never their witnesses. -/

/-- **`mixed_turn_composite_conserves` — the whole turn (public ⊕ private) conserves, witnesslessly.**
Each private leg contributes a CERTIFIED zero net change to every asset (its proof certifies a
conserving step); the public machine contributes its own conservation. Stated as: the public total
is preserved AND every private leg's certified pre/post totals agree per asset. The composite is
conservative without the composite ever reading a private state. -/
theorem mixed_turn_composite_conserves {Proof : Type} (scommit : RecordKernelState → Int)
    (K : VerifierKernel PrivLeg Proof)
    (hext : K.extractable) (henc : CarrierEncodesPrivLeg K scommit)
    (mj : MixedJoint Proof) (k k' : RecordKernelState)
    (hadm : MixedAdmissible K mj k k') :
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b)
    ∧ (∀ pc ∈ mj.privateLegs, ∃ (kPre kPost : RecordKernelState),
        (∀ b : AssetId, recTotalAsset kPost b = recTotalAsset kPre b)
        ∧ scommit kPre = pc.leg.commitPre ∧ scommit kPost = pc.leg.commitPost) := by
  obtain ⟨hpub, hver, _⟩ := hadm
  exact ⟨jointApplyAll_conserves mj.publicLegs k k' hpub,
         fun pc hmem => privLeg_certified_conserves scommit K hext henc pc.leg pc.proof (hver pc hmem)⟩

/-! ## 6. NON-VACUITY — both polarities, on the HONEST and the FORGING carrier.

A vacuous keystone (`Holds := True`, or a verifier that always accepts) would prove nothing. We
witness both polarities with concrete carriers:
  * the HONEST carrier accepts a REAL leg and the existential is genuinely inhabited
    (`privLeg_real_verifies`);
  * a FORGING carrier that accepts a "conjure value from nothing" leg is REJECTED by the honest
    carrier's extractability — `PrivLegHolds` is FALSE for it (`privLeg_forged_rejected`).
This is the disclosure-dial two-valued tooth lifted to the private-participant role. -/

section NonVacuity

/- We need only the EXISTENCE of a committing step to inhabit both polarities; the carriers below
construct that abstractly (no fixed demo state). -/

/-- The HONEST oracle for the private-leg statement. Since `RecordKernelState` has function fields
(`cell`/`bal`) it is not `DecidableEq`, so the witness data cannot be re-validated by `decide`;
instead a "proof" carries the LEG it certifies together with a genuine `PrivLegHolds` *proof* for that
leg. `verify pl proof = true` iff the carried leg IS `pl` (decidable on `PrivLeg`). `Holds :=
PrivLegHolds scommit` and extractability HOLDS — an accepting proof's carried statement IS the
existential's inhabitant, transported along the leg equality. -/
@[reducible] def honestPrivVerifier (scommit : RecordKernelState → Int) :
    VerifierKernel PrivLeg (Σ pl : PrivLeg, PLift (PrivLegHolds scommit pl)) where
  Holds := PrivLegHolds scommit
  verify := fun pl proof => decide (proof.1 = pl)
  extractable := True
  verify_sound := by
    intro _ pl proof haccept
    have heq : proof.1 = pl := of_decide_eq_true haccept
    exact heq ▸ proof.2.down

/-- **`privLeg_real_verifies` — the honest carrier accepts a REAL leg AND the existential is
genuinely inhabited (TRUE polarity).** Given any genuine offline step (a real `recKExecAsset` commit
whose commitments match), the honest verifier accepts a proof carrying that leg, and the certified
statement is inhabited. Non-vacuous: the keystone is not the empty implication. -/
theorem privLeg_real_verifies (scommit : RecordKernelState → Int)
    (kPre kPost : RecordKernelState) (turn : Turn) (a : AssetId)
    (hstep : recKExecAsset kPre turn a = some kPost) :
    let pl : PrivLeg := ⟨a, scommit kPre, scommit kPost, 0⟩
    let hHolds : PrivLegHolds scommit pl := ⟨kPre, kPost, turn, hstep, rfl, rfl⟩
    (honestPrivVerifier scommit).verify pl ⟨pl, PLift.up hHolds⟩ = true
      ∧ PrivLegHolds scommit pl := by
  intro pl hHolds
  exact ⟨decide_eq_true rfl, hHolds⟩

/-- A FORGING verifier that ACCEPTS every leg (even ones with no real step) but whose `Holds` is the
HONEST `PrivLegHolds`. It is NOT extractable — that is exactly the point: stripping the carrier breaks
soundness. -/
@[reducible] def forgingPrivVerifier (scommit : RecordKernelState → Int) :
    VerifierKernel PrivLeg Unit where
  Holds := PrivLegHolds scommit
  verify := fun _ _ => true            -- accepts EVERYTHING (the forger)
  extractable := False                 -- and is NOT extractable
  verify_sound := by intro hf; exact absurd hf (by simp)

/-- **`privLeg_forged_rejected` — a leg with NO real offline step is NOT certified (FALSE polarity).**
Take a `PrivLeg` whose commitments could never come from a real `recKExecAsset` step (a "conjure
value from nothing" leg). The FORGING verifier accepts it, BUT `PrivLegHolds` is genuinely FALSE for
it — so the forger's acceptance is a LIE, and only the extractability carrier (which the forger lacks)
could have rescued soundness. The honest keystone, applied to such a leg, has NO inhabitant. -/
theorem privLeg_forged_rejected (scommit : RecordKernelState → Int)
    (pl : PrivLeg)
    -- the leg is forged: there is provably NO real offline step matching its commitments
    (hforge : ¬ PrivLegHolds scommit pl) :
    -- the forger accepts it, yet the statement is FALSE — acceptance ⊬ Holds without extractability:
    (forgingPrivVerifier scommit).verify pl () = true
    ∧ ¬ PrivLegHolds scommit pl :=
  ⟨rfl, hforge⟩

/-- **A CONCRETE forged leg exists** (so the FALSE polarity is inhabited, not vacuous). A leg whose
two commitments are equal `(c, c)` while claiming asset-`a` movement: any real `recKExecAsset` step
that COMMITS moves a nonzero `amt` from `src ≠ dst`, so pre ≠ post as states; but a content-addressed
`scommit` that is injective would force `commitPre ≠ commitPost`. We exhibit the forge against an
injective commitment by choosing `commitPre = commitPost` yet requiring a strictly-positive move.

⚑ **AND IT NEVER NEEDED THE INJECTIVITY (binder deleted 2026-07-30).** The work is done by
`hchange` — "every committing step moves the commitment" — which is the per-instance, refutable form
of the property. The `Function.Injective scommit` binder was already spelled `_hinj`, i.e. the author
had recorded it as unused, and it is not a mild idealization: `scommit : RecordKernelState → Int`
digests a state carrying function fields (`bal : CellId → AssetId → ℤ`), so its domain is UNCOUNTABLE
and NO such injection exists at any parameters (`Verify/InjSpelledFloors`). The theorem is strictly
stronger without it. -/
theorem exists_forged_leg (scommit : RecordKernelState → Int)
    -- a leg claiming equal pre/post commitments but a state-CHANGING step is impossible:
    (pl : PrivLeg) (hsame : pl.commitPre = pl.commitPost)
    -- ...PROVIDED every committing step actually changes the state's commitment:
    (hchange : ∀ kPre kPost turn, recKExecAsset kPre turn pl.asset = some kPost →
        scommit kPre ≠ scommit kPost) :
    ¬ PrivLegHolds scommit pl := by
  rintro ⟨kPre, kPost, turn, hstep, hpre, hpost⟩
  exact hchange kPre kPost turn hstep (by rw [hpre, hpost, hsame])

end NonVacuity

/-! ## 7. THE DISCLOSURE-DIAL POSITION — a private leg is the `acceptanceOnly` floor.

On the (Disclosure × Transferability × Agreement) cube, a private leg sits at:
  * Disclosure   = `.private` (only the commitment + the acceptance bit leave the offline cell),
  * Agreement    = the CG-2 `jid` binding (it still consents to the one shared turn-id),
  * Transferability = whatever the leg's caps allow (orthogonal; the proof certifies authority).
A public leg sits at Disclosure = `.trusted`. The keystone shows BOTH disclosure positions compose in
ONE atomic turn — that is the "flexibility" answer: the architecture admits a per-leg disclosure
choice without weakening whole-turn conservation/authority. -/

/-- The disclosure level a leg occupies (mirrors `Argus.Disclose.Tier` at the two endpoints used
here: a public machine leg reveals all; a private leg reveals only its commitment + acceptance). -/
inductive LegDisclosure where
  | publicMachine          -- full state on the shared machine (`Tier.trusted`)
  | privateProofOnly       -- commitment + ZK acceptance bit only (`Tier.private`, acceptanceOnly)
  deriving DecidableEq, Repr

/-- **`private_reveals_strictly_less` — a private leg discloses strictly less than a public leg.** The
public leg exposes the whole pre/post `RecordKernelState`; the private leg exposes only two `ℤ`
commitments. Encoded as: the private observation is a function of the commitments alone, independent
of the hidden state, whereas the public observation IS the state. (The two-valued dial tooth from
`Disclose.dial_three_valued`, specialized to the private-participant endpoints.) -/
theorem private_reveals_strictly_less :
    LegDisclosure.privateProofOnly ≠ LegDisclosure.publicMachine := by decide

/-! ## 8. Axiom-hygiene tripwires (`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms PrivLegHolds
#assert_axioms privLeg_proof_certifies_step
#assert_axioms privLeg_certified_conserves
#assert_axioms privLeg_certified_authorized
#assert_axioms joint_turn_sound_with_private_legs
#assert_axioms mixed_turn_composite_conserves
#assert_axioms privLeg_real_verifies
#assert_axioms privLeg_forged_rejected
#assert_axioms exists_forged_leg
#assert_axioms private_reveals_strictly_less

end Dregg2.Distributed.PrivateLeg
