/-
# `Dregg2.Crypto.CarrierContent` — the carrier-content TOOTH, fired at every repaired kernel.

`PremiseInhabitabilitySweep` §5 (row R11) found that thirteen `Dregg2/Crypto/` classes gate their
extraction on a self-chosen `extractable : Prop`, and that **every** in-tree reference instance of the
family discharged the carrier half of `CarrierLive` by writing `extractable := True`. It proved two
INDEPENDENT vacuity modes at the real `MerkleVerifierKernel`:

  * MODE 1 (`falseCarrierMerkleKernel_soundness_never_fires`) — `extractable := False` keeps the class
    inhabited, the gated theorem TRUE for an ARBITRARY conclusion, and unappliable, while the verifier
    accepts EVERY triple. `PremiseInhabitability` cannot see this: it is not about acceptance.
  * MODE 2 (`deadVerifierMerkleKernel_soundness_is_vacuous`) — the empty-acceptance wound.

`CarrierLive carrier acc := carrier ∧ AcceptsSome acc` excludes both. But — and this is what this
module exists for — `CarrierLive` is satisfied by writing `True`, so passing it is not evidence the
carrier says anything. The evidence `True` can NEVER produce is a **refutation**: the same carrier
SHAPE, instantiated at a broken sibling oracle, provably FALSE. That is exactly the discipline
`Crypto/PortalFloor.lean` already ran (`instVerifierKernel_extractable` proved,
`instVerifierForge_not_extractable` refuted), and this module makes it a reusable criterion.

## What is here

* `CarrierAudit O ι` — the tooth. It carries the carrier as a FUNCTION of the oracle
  (`shape : O → Prop`, in practice `fun K => K.extractable`), a reference oracle where the shape
  HOLDS, a broken sibling where it is REFUTED, and an accepting run of the reference oracle. A
  `True` carrier cannot inhabit this record: `carrierAudit_shape_is_not_true` derives a contradiction
  from `shape = fun _ => True`.
* `carrierAudit_live` — every audit yields the sweep's `CarrierLive` at the reference oracle, so the
  two vacuity modes are excluded by construction; `carrierAudit_fires` is the sweep's
  `carrierLive_fires` re-exported through the audit (the gated conclusion is reached on a real run).
* Nine audits, one per repaired reference kernel: Merkle, Temporal, Custom, Bridge, Pedersen,
  BlindedSet, NonMembership, Deco — the sweep's eight — plus `RangeProof`, a NINTH `extractable :=
  True` instance the sweep's list did not carry. Each is discharged by that file's PROVED carrier and
  its FORGE refutation — no `trivial`, no `True`. `rangeBindingAudit` shows the tooth is not specific
  to `extractable`: it audits the DLog `binding` carrier the same way.

## Honest ceiling

An audit says the carrier SHAPE is refutable and holds at a TOY reference oracle. It says NOTHING
about STARK extractability at any deployed verifier: those oracles are `opaque`/`extern`, no
instantiation exists in-tree, and R11 remains UNKNOWN at deployment. What is closed is the specific
hole the sweep found — that the family's own non-vacuity witnesses passed by writing `True`.
-/
import Dregg2.Circuit.PremiseInhabitabilitySweep
import Dregg2.Crypto.VerifierKernel
import Dregg2.Crypto.Temporal
import Dregg2.Crypto.Custom
import Dregg2.Crypto.Bridge
import Dregg2.Crypto.Pedersen
import Dregg2.Crypto.BlindedSet
import Dregg2.Crypto.NonMembership
import Dregg2.Crypto.Deco
import Dregg2.Crypto.RangeProof
import Dregg2.Tactics

namespace Dregg2.Crypto.CarrierContent

open Dregg2.Circuit.PremiseInhabitability
open Dregg2.Circuit.PremiseInhabitabilitySweep (CarrierLive carrierLive_fires)

universe u v

/-! ## §1 — the tooth. -/

/-- **`CarrierAudit O ι`** — the reusable criterion a carrier-gated kernel must exhibit.

`shape` is the class's carrier field READ AS A FUNCTION of the instance (`fun K => K.extractable`),
which is the whole point: a carrier written as `True` ignores its oracle, and this record forces the
carrier to distinguish two oracles. `ok` is the reference instance, `bad` the broken sibling with the
SAME carrier shape, `acc` the reference oracle's acceptance predicate.

Three obligations, and no `True` carrier can meet all three:

  * `holds` — the carrier is PROVED at the reference oracle (excludes vacuity MODE 1);
  * `accepts` — the reference oracle accepts something (excludes vacuity MODE 2);
  * `refuted` — the SAME shape is FALSE at the broken oracle (excludes `True`, which the first two
    do not: `referenceMerkleKernel_carrierLive` passed with a literally content-free carrier). -/
structure CarrierAudit (O : Type u) (ι : Type v) where
  /-- The class's carrier field, as a function of the instance. -/
  shape : O → Prop
  /-- The reference instance (the honest toy oracle). -/
  ok : O
  /-- The broken sibling instance carrying the SAME carrier shape. -/
  bad : O
  /-- The acceptance predicate of the reference instance's `verify` oracle. -/
  acc : Acc ι
  /-- The carrier HOLDS at the reference instance — a theorem, never `trivial`. -/
  holds : shape ok
  /-- The carrier is FALSE at the broken sibling — the evidence `True` can never produce. -/
  refuted : ¬ shape bad
  /-- The reference oracle accepts an exhibited run. -/
  accepts : AcceptsSome acc

variable {O : Type u} {ι : Type v}

/-- **THE TOOTH BITES.** No audit exists for a carrier written as `True`: `True` holds of every
oracle, so it can never be refuted at the broken sibling. This is the property `CarrierLive` lacks
and the reason eight reference kernels passed the sweep's criterion while saying nothing. -/
theorem carrierAudit_shape_is_not_true (A : CarrierAudit O ι) : A.shape ≠ fun _ => True := by
  intro h
  apply A.refuted
  rw [h]
  trivial

/-- Sharper than the previous, and constructive: an audited carrier is not constantly true, so it
DISCRIMINATES between oracles — which is what "this `Prop` says something about the oracle" means. -/
theorem carrierAudit_shape_not_constant (A : CarrierAudit O ι) : ¬ ∀ o, A.shape o :=
  fun h => A.refuted (h A.bad)

/-- Every audit yields the sweep's `CarrierLive` at the reference instance: both vacuity modes
excluded, by construction rather than by assumption. -/
theorem carrierAudit_live (A : CarrierAudit O ι) : CarrierLive (A.shape A.ok) A.acc :=
  ⟨A.holds, A.accepts⟩

/-- **WHAT THE AUDIT BUYS** — the sweep's `carrierLive_fires`, re-exported: the kernel's gated
soundness theorem DELIVERS on an actual accepting run. Neither vacuity mode can produce this, and
neither can a carrier that is `True` at an oracle whose verifier rejects everything. -/
theorem carrierAudit_fires {Q : ι → Prop} (A : CarrierAudit O ι)
    (hthm : A.shape A.ok → ∀ i, A.acc i → Q i) : ∃ i, Q i :=
  carrierLive_fires (carrierAudit_live A) hthm

#assert_axioms carrierAudit_shape_is_not_true
#assert_axioms carrierAudit_shape_not_constant
#assert_axioms carrierAudit_live
#assert_axioms carrierAudit_fires

/-! ## §2 — the repaired reference kernels, wired to the tooth.

Each audit's `holds`/`refuted` are the PROVED carrier and the FORGE refutation living in that
kernel's own file. Nothing here is `trivial`. -/

/-- Merkle membership (`Crypto/VerifierKernel.lean`) — the kernel the sweep machine-checked as
content-free. Run index: `(root, leaf, proof)`. -/
def merkleAudit : CarrierAudit (MerkleVerifierKernel Int Int) (Int × Int × Int) where
  shape K := K.extractable
  ok := Reference.instMerkleVerifierKernel
  bad := Reference.forgeMerkleKernel
  acc := ofBool fun r => Reference.instMerkleVerifierKernel.verify r.1 r.2.1 r.2.2
  holds := Reference.instMerkleVerifierKernel_extractable
  refuted := Reference.forgeMerkleKernel_not_extractable
  accepts := ⟨(2, 1, 2), rfl⟩

/-- Temporal window (`Crypto/Temporal.lean`). Run index: the disclosed `(lo, hi, t)` statement. -/
def temporalAudit :
    CarrierAudit (Temporal.TemporalVerifierKernel Int) (Temporal.Statement × Int) where
  shape K := K.extractable
  ok := Temporal.Reference.refKernel
  bad := Temporal.Reference.forgeKernel
  acc := ofBool fun r => Temporal.Reference.refKernel.verify r.1 r.2
  holds := Temporal.Reference.refKernel_extractable
  refuted := Temporal.Reference.forgeKernel_not_extractable
  accepts := ⟨(Temporal.Reference.sampleStmt, 0), rfl⟩

/-- Custom registered kind (`Crypto/Custom.lean`). The oracle here is the PAIR (registration, kernel),
because `CustomVerifierKernel` is indexed by its registration and the forge is a registration whose
relation holds of NOTHING — the kernels genuinely live at different types.

Read this one carefully: over the EQUALITY registration alone the carrier could not be refuted by any
oracle, because that relation is TOTAL (`∃ wit, stmt = wit` holds for every statement). So for
`Custom` the carrier's content is a property of the registration+oracle pair, not of the oracle
alone, and that is exactly what this audit's `shape` reads. -/
def customAudit :
    CarrierAudit ((R : Custom.CustomRegistration.{0}) × Custom.CustomVerifierKernel R Int)
      (Int × Int) where
  shape p := p.2.extractable
  ok := ⟨Custom.Reference.eqRegistration, Custom.Reference.refKernel⟩
  bad := ⟨Custom.Reference.emptyRegistration, Custom.Reference.forgeKernel⟩
  acc := ofBool fun r => Custom.Reference.refKernel.verify r.1 r.2
  holds := Custom.Reference.refKernel_extractable
  refuted := Custom.Reference.forgeKernel_not_extractable
  accepts := ⟨(5, 5), rfl⟩

/-- Cross-chain bridge observation (`Crypto/Bridge.lean`). -/
def bridgeAudit :
    CarrierAudit (Bridge.BridgeVerifierKernel Int Unit) (Bridge.Statement Int × Unit) where
  shape K := K.extractable
  ok := Bridge.Reference.refKernel
  bad := Bridge.Reference.forgeKernel
  acc := ofBool fun r => Bridge.Reference.refKernel.verify r.1 r.2
  holds := Bridge.Reference.refKernel_extractable
  refuted := Bridge.Reference.forgeKernel_not_extractable
  accepts := ⟨(Bridge.Reference.sampleStmt, ()), rfl⟩

/-- Pedersen conservation (`Crypto/Pedersen.lean`). NOTE: this audits `extractable` only — the same
kernel's `binding` carrier is STILL `True`, and cannot be repaired without a non-degenerate reference
commitment (see `Pedersen.Reference.refKernel`'s docstring). -/
def pedersenAudit :
    CarrierAudit (Pedersen.PedersenVerifierKernel Int Int) (Pedersen.Statement Int × Int) where
  shape K := K.extractable
  ok := Pedersen.Reference.refKernel
  bad := Pedersen.Reference.forgeKernel
  acc := ofBool fun r => Pedersen.Reference.refKernel.verify r.1 r.2
  holds := Pedersen.Reference.refKernel_extractable
  refuted := Pedersen.Reference.forgeKernel_not_extractable
  accepts := ⟨(Pedersen.Reference.balancedStmt, 0), rfl⟩

/-- Blinded issuer-set membership (`Crypto/BlindedSet.lean`). -/
def blindedSetAudit :
    CarrierAudit (BlindedSet.BlindedSetVerifierKernel Int Int) (BlindedSet.Statement Int × Int) where
  shape K := K.extractable
  ok := BlindedSet.Reference.refKernel
  bad := BlindedSet.Reference.forgeKernel
  acc := ofBool fun r => BlindedSet.Reference.refKernel.verify r.1 r.2
  holds := BlindedSet.Reference.refKernel_extractable
  refuted := BlindedSet.Reference.forgeKernel_not_extractable
  accepts := ⟨(BlindedSet.Reference.authStmt, 0), rfl⟩

/-- Sorted-tree non-membership (`Crypto/NonMembership.lean`). -/
def nonMembershipAudit :
    CarrierAudit (NonMembership.NonMembershipVerifierKernel Int Int)
      (NonMembership.Statement Int × Int) where
  shape K := K.extractable
  ok := NonMembership.Reference.refKernel
  bad := NonMembership.Reference.forgeKernel
  acc := ofBool fun r => NonMembership.Reference.refKernel.verify r.1 r.2
  holds := NonMembership.Reference.refKernel_extractable
  refuted := NonMembership.Reference.forgeKernel_not_extractable
  accepts := ⟨(NonMembership.Reference.absentStmt, 0), rfl⟩

/-- DECO / zkTLS payment attestation (`Crypto/Deco.lean`). -/
def decoAudit :
    CarrierAudit (Deco.DecoVerifierKernel Int Unit) (Deco.Statement Int × Unit) where
  shape K := K.extractable
  ok := Deco.Reference.refKernel
  bad := Deco.Reference.forgeKernel
  acc := ofBool fun r => Deco.Reference.refKernel.verify r.1 r.2
  holds := Deco.Reference.refKernel_extractable
  refuted := Deco.Reference.forgeKernel_not_extractable
  accepts := ⟨(Deco.Reference.sampleStmt, ()), rfl⟩

/-- Bulletproofs range (`Crypto/RangeProof.lean`) — a NINTH `extractable := True` instance, not in
the sweep's list of eight, found while repairing. Its forge is a range verifier that accepts
OUT-OF-RANGE statements. Run index: `(commitment, lo, hi, proof)`. -/
def rangeProofAudit :
    CarrierAudit (RangeProof.RangeProofKernel Int Int) (Int × Int × Int × Int) where
  shape K := K.extractable
  ok := RangeProof.Reference.refKernel
  bad := RangeProof.Reference.forgeKernel
  acc := ofBool fun r => RangeProof.Reference.refKernel.verifyRange r.1 r.2.1 r.2.2.1 r.2.2.2
  holds := RangeProof.Reference.refKernel_extractable
  refuted := RangeProof.Reference.forgeKernel_not_extractable
  accepts := ⟨(15, 10, 20, 0), rfl⟩

/-- **THE TOOTH IS NOT SPECIFIC TO `extractable`.** The same audit shape applies to the DLog
`binding` carrier, read as a function of the COMMITMENT: it holds for the reference commitment and is
FALSE for a colliding one. (The `acc` here is the same range verifier, since binding is a carrier of
the same kernel.) Pedersen's own `binding` could NOT get this treatment — see
`Pedersen.Reference.refKernel`'s docstring: its toy `commit v r := v + r` is genuinely not binding,
so the honest shape would be FALSE at the reference instance. -/
def rangeBindingAudit : CarrierAudit (Int → Int → Int) (Int × Int × Int × Int) where
  shape := RangeProof.Reference.BindingShape
  ok := RangeProof.Reference.refCommit
  bad := fun _ _ => 0
  acc := ofBool fun r => RangeProof.Reference.refKernel.verifyRange r.1 r.2.1 r.2.2.1 r.2.2.2
  holds := RangeProof.Reference.refCommit_binding
  refuted := RangeProof.Reference.collidingCommit_not_binding
  accepts := ⟨(15, 10, 20, 0), rfl⟩

/-! ## §3 — the tooth fired at all eight, and the family-level statement. -/

/-- **NONE OF THE REPAIRED CARRIERS IS `True`** — the eight of the sweep's finding, plus the ninth
(`RangeProof.extractable`) and its `binding` companion. Each shape is refutable at its own forge, so
none of them can be the constant-`True` carrier the sweep found family-wide. This is the theorem the
old reference instances could not have: `referenceMerkleKernel_carrier_is_content_free` proved the
opposite of it for the Merkle kernel. -/
theorem the_repaired_carriers_are_not_true :
    (merkleAudit.shape ≠ fun _ => True)
      ∧ (temporalAudit.shape ≠ fun _ => True)
      ∧ (customAudit.shape ≠ fun _ => True)
      ∧ (bridgeAudit.shape ≠ fun _ => True)
      ∧ (pedersenAudit.shape ≠ fun _ => True)
      ∧ (blindedSetAudit.shape ≠ fun _ => True)
      ∧ (nonMembershipAudit.shape ≠ fun _ => True)
      ∧ (decoAudit.shape ≠ fun _ => True)
      ∧ (rangeProofAudit.shape ≠ fun _ => True)
      ∧ (rangeBindingAudit.shape ≠ fun _ => True) :=
  ⟨carrierAudit_shape_is_not_true merkleAudit,
   carrierAudit_shape_is_not_true temporalAudit,
   carrierAudit_shape_is_not_true customAudit,
   carrierAudit_shape_is_not_true bridgeAudit,
   carrierAudit_shape_is_not_true pedersenAudit,
   carrierAudit_shape_is_not_true blindedSetAudit,
   carrierAudit_shape_is_not_true nonMembershipAudit,
   carrierAudit_shape_is_not_true decoAudit,
   carrierAudit_shape_is_not_true rangeProofAudit,
   carrierAudit_shape_is_not_true rangeBindingAudit⟩

/-- **ALL NINE ARE `CarrierLive`** — with carriers that are now theorems, not `True`. Compare
`referenceMerkleKernel_carrierLive`, which passed the same criterion by assumption. -/
theorem the_repaired_are_carrierLive :
    CarrierLive (merkleAudit.shape merkleAudit.ok) merkleAudit.acc
      ∧ CarrierLive (temporalAudit.shape temporalAudit.ok) temporalAudit.acc
      ∧ CarrierLive (customAudit.shape customAudit.ok) customAudit.acc
      ∧ CarrierLive (bridgeAudit.shape bridgeAudit.ok) bridgeAudit.acc
      ∧ CarrierLive (pedersenAudit.shape pedersenAudit.ok) pedersenAudit.acc
      ∧ CarrierLive (blindedSetAudit.shape blindedSetAudit.ok) blindedSetAudit.acc
      ∧ CarrierLive (nonMembershipAudit.shape nonMembershipAudit.ok) nonMembershipAudit.acc
      ∧ CarrierLive (decoAudit.shape decoAudit.ok) decoAudit.acc
      ∧ CarrierLive (rangeProofAudit.shape rangeProofAudit.ok) rangeProofAudit.acc :=
  ⟨carrierAudit_live merkleAudit, carrierAudit_live temporalAudit, carrierAudit_live customAudit,
   carrierAudit_live bridgeAudit, carrierAudit_live pedersenAudit,
   carrierAudit_live blindedSetAudit, carrierAudit_live nonMembershipAudit,
   carrierAudit_live decoAudit, carrierAudit_live rangeProofAudit⟩

/-- **THE GATED THEOREM FIRES, OFF A PROVED CARRIER.** `merkle_verify_sound` reaches a genuine
`MerkleMembers` conclusion on an actual accepting run — and the carrier it consumes is
`instMerkleVerifierKernel_extractable`, a theorem, not the `True` the old instance supplied. -/
theorem merkle_soundness_fires :
    ∃ r : Int × Int × Int,
      Merkle.MerkleMembers (Digest := Int) (fun a b => a + b) r.1 r.2.1 :=
  carrierAudit_fires (Q := fun r => Merkle.MerkleMembers (Digest := Int) (fun a b => a + b) r.1 r.2.1)
    merkleAudit
    (fun hext r hacc =>
      merkle_verify_sound (K := Reference.instMerkleVerifierKernel) hext r.1 r.2.1 r.2.2 hacc)

/-- The same for the temporal kernel: an accepted window statement really lands in the window. -/
theorem temporal_soundness_fires :
    ∃ r : Temporal.Statement × Int, Temporal.InWindow r.1.lo r.1.hi r.1.t :=
  carrierAudit_fires (Q := fun r => Temporal.InWindow r.1.lo r.1.hi r.1.t) temporalAudit
    (fun hext r hacc =>
      Temporal.temporal_verify_sound (K := Temporal.Reference.refKernel) hext r.1 r.2 hacc)

#assert_axioms the_repaired_carriers_are_not_true
#assert_axioms the_repaired_are_carrierLive
#assert_axioms merkle_soundness_fires
#assert_axioms temporal_soundness_fires

end Dregg2.Crypto.CarrierContent
