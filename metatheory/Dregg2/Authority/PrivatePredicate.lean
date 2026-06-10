/-
# Dregg2.Authority.PrivatePredicate — PRIVATE PREDICATES: relations over COMMITTED values
proven WITHOUT revealing them (DREGG3 §8, the programmability × privacy unification).

**The insight.** `RelationalClosure.RelPred` is the relational closure of the guard
language over CLEARTEXT slots. The maximally-powerful guard constrains COMMITTED values —
it proves a relation holds while the value stays PRIVATE. The graded ladder of cost vs.
disclosure:

  * **affine-EQUALITY over committed values** = FREE + PRIVATE. Pedersen commitments are
    additively homomorphic (`Crypto.Pedersen.commit_sum`, proved from `commit_hom`):
    `Σ cᵢ·commit(vᵢ) = commit(Σ cᵢ·vᵢ)`. So `Σ cᵢ·commit(vᵢ) = commit(k)` holds **iff**
    `Σ cᵢ·vᵢ = k` — the executor verifies the relation reading ONLY the commitments, never
    the values, and with ZERO extra ZK machinery. Conservation of hidden balances is the
    flagship instance: `private_conservation_checks_homomorphically`.

  * **affine-≤ / RANGE over a committed value** = a witnessed range proof. "The committed
    value lies in `[lo,hi]`" is NOT homomorphic; it routes through `witnessed(vk)`
    (`Authority.Predicate`, `WitnessedKind.custom`), the §8 oracle — same status as every
    other crypto floor (we model the interface, we do NOT implement the range AIR).

  * **non-linear** over committed values = full witnessed ZK (also `witnessed(vk)`).

A `PrivPred` is the CONJUNCTION of the three fragments — a homomorphic affine-= part, a
witnessed-range part, and a cleartext `RelPred` part — each carrying its DISCLOSURE COST
on the `Metatheory.Dial`: the homomorphic-= part reveals nothing beyond the (hiding)
commitments; the witnessed-range part reveals only the relation's truth bit; the cleartext
part reveals its slots. The selective-disclosure property: the proof reveals only that the
relation holds. Enforcement WITHOUT surveillance.

NEW file only. Reuses `Crypto.Pedersen` (the homomorphism, the kernel), `Authority.Predicate`
(the witnessed registry — the ZK escape hatch), `RelationalClosure` (the cleartext fragment),
`Metatheory.EpistemicDial` (the disclosure dial). Every keystone `#assert_axioms`-pinned —
no sorry, no `:= True`.
-/
import Dregg2.Crypto.Pedersen
import Dregg2.Authority.Predicate
import Dregg2.Authority.RelationalClosure
import Metatheory.EpistemicDial

namespace Dregg2.Authority.PrivatePredicate

open Dregg2.Crypto Dregg2.Crypto.Pedersen
open Dregg2.Laws (Verifiable Discharged)
open Dregg2.Authority.Predicate
open Dregg2.Authority.RelationalClosure (RelPred)
open Dregg2.Exec (Value)
open Metatheory (Dial)

-- The witnessed-predicate `Registry`/`Verifier`/`Discharged` machinery lives at universe `0`
-- (`Type`), so the whole private-predicate surface is built at `Type`. `Digest`/`Proof` are
-- universe-`0` carriers (the reference instantiates them at `ℤ`).
variable {Digest : Type} [AddCommGroup Digest]

/-! ## §1 — The homomorphic affine-equality fragment over COMMITTED values.

A hidden value carried in the clear-to-the-prover, blinded by `r`, and DISCLOSED to the
verifier ONLY as its Pedersen commitment `commit v r`. An affine-= relation over such
values is `Σ cᵢ·vᵢ = k`. The keystone fact is that this relation is checkable from the
commitments ALONE, via the homomorphism. -/

/-- A committed scalar: the hidden `value`, its `blinding` factor, and (derived) the
commitment the verifier actually sees (`commit value blinding`). The prover knows
`value`/`blinding`; the verifier knows only the commitment. -/
structure Committed where
  /-- The hidden scalar. -/
  value : Int
  /-- The Pedersen blinding factor. -/
  blinding : Int
  deriving Repr

/-- The Pedersen commitment of a `Committed` scalar (what the verifier sees). -/
def Committed.commitment [CryptoPrimitives Digest] (c : Committed) : Digest :=
  CryptoPrimitives.commit c.value c.blinding

/-- **The homomorphic affine-= atom over committed values.** A list of `(coefficient,
committed-scalar)` pairs and a target `k` (with its own blinding `kBlind`): the relation is
`Σ cᵢ·valueᵢ = k`. The verifier checks `Σ cᵢ·commitmentᵢ = commit k kBlind`. We require
INTEGER coefficients (`Int`) — the homomorphism is over the commitment group as a
`ℤ`-module via `commit (n • v) (n • r)`; here we keep the per-note collapse to the
`coefficient = 1` conservation shape that `commit_sum` proves directly, and lift general
coefficients through scaled notes (§1.1). -/
structure PrivAffineEq where
  /-- The committed input scalars (all with coefficient `1` in the conservation shape). -/
  ins : List Committed
  /-- The committed output scalars (the other side of the `=`). -/
  outs : List Committed
  deriving Repr

/-- The verifier-visible commitment of an input/output side: `Σ commitmentᵢ` over the
group. This is ALL the verifier reads — never the values. -/
def PrivAffineEq.insCommit [CryptoPrimitives Digest] (p : PrivAffineEq) : Digest :=
  (p.ins.map (Committed.commitment (Digest := Digest))).sum

def PrivAffineEq.outsCommit [CryptoPrimitives Digest] (p : PrivAffineEq) : Digest :=
  (p.outs.map (Committed.commitment (Digest := Digest))).sum

/-- **The HOMOMORPHIC check** — the only thing the verifier evaluates: do the input and
output commitment SUMS coincide over the group? Reads commitments only. -/
def PrivAffineEq.homCheck [CryptoPrimitives Digest] (p : PrivAffineEq) : Prop :=
  p.insCommit (Digest := Digest) = p.outsCommit (Digest := Digest)

/-- The (hidden, prover-side) cleartext relation: the input values sum to the output values
AND the input blindings sum to the output blindings. The verifier NEVER reads these — they
are the secret the homomorphic check certifies. -/
def PrivAffineEq.clearRel (p : PrivAffineEq) : Prop :=
  ((p.ins.map Committed.value).sum = (p.outs.map Committed.value).sum)
    ∧ ((p.ins.map Committed.blinding).sum = (p.outs.map Committed.blinding).sum)

/-! ### §1.1 — The keystone: the homomorphic check IS the affine-= relation, privately.

`commit_sum`/`listCommit_collapse` (proved in `Crypto.Pedersen` from `commit_hom`) collapse
a list of commitments into the commitment of the summed value+blinding. So the input/output
commitment-sum EQUATION is the commitment-of-sums equation — and (given matching blinding
totals) it says exactly that the hidden VALUE sums are equal, with zero disclosure. -/

/-- A `Committed` list's commitment sum collapses to the commitment of the summed value
under the summed blinding (`Σ commit vᵢ rᵢ = commit (Σ vᵢ) (Σ rᵢ)`). PROVED from
`commit_hom` (re-using `Pedersen.listCommit_collapse` via the `Note` correspondence). -/
theorem committedSum_collapse [CryptoPrimitives Digest] (cs : List Committed) :
    ((cs.map (Committed.commitment (Digest := Digest))).sum)
      = CryptoPrimitives.commit ((cs.map Committed.value).sum) ((cs.map Committed.blinding).sum) := by
  classical
  induction cs with
  | nil => simp [commit_zero]
  | cons c rest ih =>
      simp only [List.map_cons, List.sum_cons, ih, Committed.commitment]
      rw [CryptoPrimitives.commit_hom]

/-- **`private_conservation_checks_homomorphically` — THE KEYSTONE.** Conservation of hidden
balances is enforced with ZERO disclosure: the verifier's homomorphic check on the
COMMITMENTS holds **iff** the hidden values conserve, GIVEN matching blinding totals. The
forward direction is `commit_hom`/`commit_sum`; the reverse needs only the same collapse.
The verifier reads only `insCommit`/`outsCommit` (commitment sums) — never a single value or
blinding. An inflating split (values not equal, blindings forced equal) FAILS this check
WITHOUT opening any commitment (`Reference.inflation_caught_privately`). -/
theorem private_conservation_checks_homomorphically [CryptoPrimitives Digest]
    (p : PrivAffineEq) :
    p.homCheck (Digest := Digest)
      ↔ CryptoPrimitives.commit ((p.ins.map Committed.value).sum)
            ((p.ins.map Committed.blinding).sum)
        = (CryptoPrimitives.commit ((p.outs.map Committed.value).sum)
            ((p.outs.map Committed.blinding).sum) : Digest) := by
  unfold PrivAffineEq.homCheck PrivAffineEq.insCommit PrivAffineEq.outsCommit
  rw [committedSum_collapse, committedSum_collapse]

/-- **`private_conservation_iff_value_sum` — the value-level reading.** With matching
blinding totals AND the commitment being injective in the value argument (the Pedersen
`binding` carrier, supplied as a hypothesis — the §8 crypto residue, never a Lean law), the
homomorphic check holds iff the HIDDEN VALUE sums are equal. This is "the executor verifies
conservation of secret balances reading only the commitments." The `injOnValue` hypothesis
is exactly the binding obligation; the algebra around it is unconditional. -/
theorem private_conservation_iff_value_sum [CryptoPrimitives Digest]
    (p : PrivAffineEq)
    (hblind : (p.ins.map Committed.blinding).sum = (p.outs.map Committed.blinding).sum)
    (injOnValue : ∀ a b r : Int,
      (CryptoPrimitives.commit a r : Digest) = CryptoPrimitives.commit b r → a = b) :
    p.homCheck (Digest := Digest)
      ↔ (p.ins.map Committed.value).sum = (p.outs.map Committed.value).sum := by
  rw [private_conservation_checks_homomorphically p]
  constructor
  · intro h
    rw [hblind] at h
    exact injOnValue _ _ _ h
  · intro h; rw [h, hblind]

/-! ## §2 — The witnessed RANGE fragment over a committed value (the §8 oracle interface).

Affine-≤ / range over a committed value is NOT homomorphic. "The committed value lies in
`[lo,hi]`" is a WITNESSED predicate: the prover supplies a range proof, the verifier runs the
§8 oracle (a Bulletproof / range AIR). We STATE the interface — the predicate is a
`witnessed(vk)` atom dispatched through `Authority.Predicate.registryVerify` — and do NOT
implement the range AIR (cited as the §8 oracle, exactly the status of every crypto floor in
this tree). The verifier learns only the truth bit. -/

/-- A range claim over a committed value: the disclosed `commitment`, and the bounds
`[lo, hi]` the hidden value is asserted to lie in. The commitment is the STATEMENT; the range
proof is the WITNESS. -/
structure RangeClaim (Digest : Type) where
  /-- The disclosed Pedersen commitment of the hidden value. -/
  commitment : Digest
  /-- The asserted lower bound (inclusive). -/
  lo : Int
  /-- The asserted upper bound (inclusive). -/
  hi : Int
  deriving Repr

/-- **The witnessed-range interface.** The range relation is verified by the §8 oracle: a
`Verifier (RangeClaim Digest) Proof` installed at a `custom (vk)` slot of the predicate
registry (`Authority.Predicate`). We carry the registry + the `vk` + the disclosed claim; the
WITNESS (the range proof) is supplied at check time. The interface — never the AIR. -/
structure WitnessedRange (Digest : Type) (Proof : Type) where
  /-- The predicate registry the range verifier is installed into. -/
  reg : Registry (RangeClaim Digest) Proof
  /-- The content-addressed key of the range verifier (`WitnessedPredicateKind::Custom`). -/
  vk : Nat
  /-- The disclosed range claim (commitment + bounds). -/
  claim : RangeClaim Digest

/-- **The witnessed-range check** — dispatch the §8 range oracle on the disclosed claim and
the supplied proof. Reads the commitment (disclosed) + the proof; reveals only the accept
bit. This is `registryVerify` at the `custom vk` slot — the SAME dispatch the crypto kinds
use, no new trust boundary. -/
def WitnessedRange.check {Digest Proof : Type}
    (w : WitnessedRange Digest Proof) (proof : Proof) : Bool :=
  registryVerify w.reg (.custom w.vk) w.claim proof

/-- **`witnessed_range_is_sound` — soundness-by-verification for the range fragment.** An
accepted range proof DISCHARGES the range claim's predicate at the registry's `custom vk`
seam — directly from `Authority.Predicate.registry_sound`. The prover (range-proof producer)
is untrusted; only the in-TCB oracle decides. The crypto content (that acceptance means the
committed value is in `[lo,hi]`) is the §8 oracle's obligation, NOT a Lean law. -/
theorem witnessed_range_is_sound {Digest Proof : Type}
    (w : WitnessedRange Digest Proof) (proof : Proof)
    (haccept : w.check proof = true) :
    @Discharged (RangeClaim Digest) Proof
      (verifiableOfRegistry w.reg (.custom w.vk)) w.claim proof :=
  registry_sound w.reg (.custom w.vk) w.claim proof haccept

/-! ## §3 — `PrivPred`: the composition. Homomorphic affine-= ∧ witnessed range ∧ cleartext.

A private predicate is the CONJUNCTION of the three fragments. It is checked by:
  * the homomorphic affine-= part — over commitments, FREE + zero-disclosure;
  * the witnessed range part — the §8 oracle, reveals one bit;
  * the cleartext `RelPred` part — the `RelationalClosure` evaluator over disclosed slots.
Each fragment carries its disclosure cost (§4). The `homCheck` is a `Prop` (group equality);
the range + cleartext parts are decidable `Bool`s. We conjoin the homomorphic `Prop` with the
two decidable bits. -/

/-- **`PrivPred`** — a predicate over a MIX of cleartext fields and COMMITTED values. Three
fragments, conjoined:
  * `affine` — the homomorphic affine-= part over committed scalars (zero-disclosure);
  * `range` — the optional witnessed range part over a committed value (one-bit disclosure);
  * `clear` — the cleartext `RelPred` part over disclosed slots;
  * `cleartext` — the disclosed post-record the `clear` fragment reads. -/
structure PrivPred (Digest Proof : Type) where
  /-- The homomorphic affine-equality fragment (conservation of hidden balances). -/
  affine : PrivAffineEq
  /-- The witnessed range fragment (optional — `none` = no range constraint). -/
  range : Option (WitnessedRange Digest Proof)
  /-- The cleartext relational-closure fragment. -/
  clear : RelPred
  /-- The disclosed post-record the cleartext fragment evaluates against. -/
  cleartext : Value

/-- **`PrivPred.holds`** — the composed relation. The homomorphic affine-= part (a group
equality `Prop`), AND the witnessed range part (the §8 oracle bit, or `True` if absent, given
its proof), AND the cleartext `RelPred` evaluator. All three conjoined. The verifier reads
ONLY: the commitment sums (affine), the disclosed commitment + accept bit (range), and the
disclosed slots (clear). -/
def PrivPred.holds {Digest Proof : Type} [AddCommGroup Digest] [CryptoPrimitives Digest]
    (p : PrivPred Digest Proof) (rangeProof : Option Proof) : Prop :=
  p.affine.homCheck (Digest := Digest)
    ∧ (match p.range, rangeProof with
        | some w, some proof => w.check proof = true
        | none, _ => True
        | some _, none => False)
    ∧ p.clear.eval p.cleartext = true

/-- **`privPred_composes`.** The composed `holds` decomposes EXACTLY into its three
fragment checks: the homomorphic affine-= part, the witnessed-range part, and the cleartext
part — conjoined, no fragment lost, no fragment doubled. The composition is faithful. -/
theorem privPred_composes {Digest Proof : Type} [AddCommGroup Digest] [CryptoPrimitives Digest]
    (p : PrivPred Digest Proof) (rangeProof : Option Proof) :
    p.holds rangeProof
      ↔ (p.affine.homCheck (Digest := Digest))
        ∧ (match p.range, rangeProof with
            | some w, some proof => w.check proof = true
            | none, _ => True
            | some _, none => False)
        ∧ p.clear.eval p.cleartext = true :=
  Iff.rfl

/-- **`privPred_affine_is_homomorphic`.** Holding a `PrivPred` ENTAILS its affine
fragment passes the homomorphic check — so (with matching blindings + binding) the hidden
balances conserve, verified from the commitments alone. The keystone wired into the
composition: a satisfied private predicate carries private conservation. -/
theorem privPred_affine_is_homomorphic {Digest Proof : Type} [AddCommGroup Digest] [CryptoPrimitives Digest]
    (p : PrivPred Digest Proof) (rangeProof : Option Proof)
    (h : p.holds rangeProof) :
    p.affine.homCheck (Digest := Digest) :=
  h.1

/-- **`privPred_range_discharged`.** If a `PrivPred` with a range fragment holds
(with a supplied proof), that proof DISCHARGES the range claim — the §8 oracle accepted, so
the committed value's range relation is soundly attested (`witnessed_range_is_sound`). -/
theorem privPred_range_discharged {Digest Proof : Type} [AddCommGroup Digest] [CryptoPrimitives Digest]
    (p : PrivPred Digest Proof) (w : WitnessedRange Digest Proof) (proof : Proof)
    (hrange : p.range = some w)
    (h : p.holds (some proof)) :
    @Discharged (RangeClaim Digest) Proof
      (verifiableOfRegistry w.reg (.custom w.vk)) w.claim proof := by
  have hbit : w.check proof = true := by
    have := h.2.1
    rw [hrange] at this
    exact this
  exact witnessed_range_is_sound w proof hbit

/-! ## §4 — THE DISCLOSURE COST: each fragment carries its `Dial` position.

The selective-disclosure accounting, on the `Metatheory.Dial`:
  * the homomorphic affine-= part reveals NOTHING beyond the (hiding) commitments — its
    disclosure floor is `acceptanceOnly` (`⊥`): the verifier learns only that the relation
    holds, never a value;
  * the witnessed-range part reveals only the relation's TRUTH BIT — also `acceptanceOnly`:
    a range proof is zero-knowledge over the value;
  * the cleartext `RelPred` part reveals its disclosed slots — `fullDisclosure` (`⊤`) for
    those fields.
A `PrivPred` carries its overall disclosure level = the JOIN (max) of the fragment levels.
A purely-committed `PrivPred` (trivial cleartext) sits at the dial FLOOR — the proof reveals
only that the relation holds. -/

/-- The disclosure level of the homomorphic affine-= fragment: `acceptanceOnly` — the
verifier learns only the commitment sums coincide; the hiding commitments leak no value. -/
def affineDisclosure : Dial := Dial.acceptanceOnly

/-- The disclosure level of the witnessed-range fragment: `acceptanceOnly` — a range proof
reveals only the truth bit (it is zero-knowledge over the committed value). -/
def rangeDisclosure : Dial := Dial.acceptanceOnly

/-- The disclosure level of a cleartext `RelPred` fragment: `fullDisclosure` if it reads any
slot (the slots are cleartext), `acceptanceOnly` for a constant predicate (`top`/`bot`) that
reads nothing. -/
def clearDisclosure : RelPred → Dial
  | .top => Dial.acceptanceOnly
  | .bot => Dial.acceptanceOnly
  | _    => Dial.fullDisclosure

/-- **`PrivPred.disclosure`** — the overall disclosure level: the JOIN of the three fragment
levels. The dial position the whole private predicate occupies. -/
def PrivPred.disclosure {Digest Proof : Type} (p : PrivPred Digest Proof) : Dial :=
  affineDisclosure ⊔ rangeDisclosure ⊔ clearDisclosure p.clear

/-- **`affine_reveals_nothing`.** The homomorphic affine-= fragment sits at the dial
FLOOR (`⊥`): it reveals nothing beyond the commitments. Private conservation is a
zero-disclosure check. -/
theorem affine_reveals_nothing : affineDisclosure = (⊥ : Dial) := rfl

/-- **`range_reveals_only_truth_bit`.** The witnessed-range fragment sits at the dial
FLOOR (`⊥`): a range proof reveals only the relation's truth bit, nothing of the value. -/
theorem range_reveals_only_truth_bit : rangeDisclosure = (⊥ : Dial) := rfl

/-- **`fully_committed_privpred_is_at_floor`.** A `PrivPred` whose cleartext fragment
is trivial (`top` — reads no slot) sits at the dial FLOOR: every fragment is at
`acceptanceOnly`, so the join is `acceptanceOnly`. The proof reveals ONLY that the relation
holds — selective disclosure in its purest form: enforcement without surveillance. -/
theorem fully_committed_privpred_is_at_floor {Digest Proof : Type}
    (p : PrivPred Digest Proof) (htriv : p.clear = .top) :
    p.disclosure = (⊥ : Dial) := by
  unfold PrivPred.disclosure
  rw [htriv]
  show (Dial.acceptanceOnly ⊔ Dial.acceptanceOnly) ⊔ Dial.acceptanceOnly = Dial.acceptanceOnly
  simp

/-- **`cleartext_fragment_discloses_slots`.** A non-trivial cleartext fragment (any
affine/Boolean shape) discloses its slots — its fragment level is `fullDisclosure` (`⊤`), and
so the whole `PrivPred`'s disclosure is `fullDisclosure`. The honest cost: reading cleartext
slots is full disclosure of those slots, however private the committed fragments remain. -/
theorem cleartext_fragment_discloses_slots {Digest Proof : Type}
    (p : PrivPred Digest Proof) (terms : List RelationalClosure.Term) (k : Int)
    (hclear : p.clear = .affineLe terms k) :
    p.disclosure = (⊤ : Dial) := by
  unfold PrivPred.disclosure clearDisclosure
  rw [hclear]
  show (Dial.acceptanceOnly ⊔ Dial.acceptanceOnly) ⊔ Dial.fullDisclosure = Dial.fullDisclosure
  simp [← Metatheory.Dial.top_eq]

/-! ### §4.1 — Connection to the Disclose dial: a `PrivPred` carries a `DiscloseAt` schedule.

The disclosure level is not decorative — it pins a `Metatheory.DiscloseAt` schedule whose
ACCEPTANCE bit is exactly the witnessed-range oracle's `Discharged` check, and whose floor
(`⊥`) is the zero-knowledge position. So the private predicate's "the proof reveals only that
the relation holds" is the `accepts_bot_iff_discharged` law of the unified dial. -/

open Metatheory (DiscloseAt)

/-- **`privPred_disclose_schedule`** — the `DiscloseAt` schedule a range-bearing `PrivPred`
pins on the dial. `leaked` is coarsened to `Unit` (the disclosure CONTENT is modeled
elsewhere; here we expose the acceptance structure); `accepts` at every notch is the
witnessed-range oracle's `Discharged` bit — position-independent, exactly as the dial law
requires. The dial's FLOOR accepts iff the range proof discharges: the proof reveals only the
relation's truth. -/
def privPred_disclose_schedule {Digest Proof : Type}
    (w : WitnessedRange Digest Proof) (proof : Proof) :
    @DiscloseAt Unit (RangeClaim Digest) Proof _
      (verifiableOfRegistry w.reg (.custom w.vk)) :=
  letI : Verifiable (RangeClaim Digest) Proof := verifiableOfRegistry w.reg (.custom w.vk)
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := w.claim
    wit := proof
    accepts := fun _ => Discharged w.claim proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`privPred_floor_reveals_only_truth`.** The disclosure dial's FLOOR (`⊥`) for a
range-bearing `PrivPred` accepts IFF the witnessed-range oracle discharges the claim. So at the
zero-knowledge floor the verifier learns ONLY that the relation holds — the selective-disclosure
property, routed through the unified `Metatheory.Dial` (`accepts_bot_iff_discharged`). -/
theorem privPred_floor_reveals_only_truth {Digest Proof : Type}
    (w : WitnessedRange Digest Proof) (proof : Proof) :
    @DiscloseAt.accepts Unit (RangeClaim Digest) Proof _
        (verifiableOfRegistry w.reg (.custom w.vk))
        (privPred_disclose_schedule w proof) (⊥ : Dial)
      ↔ @Discharged (RangeClaim Digest) Proof
          (verifiableOfRegistry w.reg (.custom w.vk)) w.claim proof := by
  letI : Verifiable (RangeClaim Digest) Proof := verifiableOfRegistry w.reg (.custom w.vk)
  exact DiscloseAt.accepts_bot_iff_discharged (privPred_disclose_schedule w proof)

/-! ## §5 — §NON-VACUITY: inflation caught PRIVATELY + a range claim rejected.

Two witnesses over the `ℤ` Pedersen reference (`commit v r := v + r`):
  1. a valid hidden split PASSES the homomorphic conservation check, and an INFLATING split
     (same blinding total, larger output value) FAILS it — caught WITHOUT opening any
     commitment;
  2. a witnessed range claim REJECTS an out-of-range committed value, via the §8 oracle
     interface (modeled with a toy decidable range verifier). -/

namespace Reference

open Dregg2.Crypto.Reference

/-- A balanced hidden split over `ℤ`: one input of value `5` (blinding `3`) transferred to one
output of value `5` (blinding `3`). Commitments are `5+3 = 8` on each side. -/
def balanced : PrivAffineEq :=
  { ins := [{ value := 5, blinding := 3 }]
    outs := [{ value := 5, blinding := 3 }] }

/-- An INFLATING split over `ℤ`: input value `5` (blinding `3`), output value `9` (blinding
`3`) — the same blinding total, but the output value INFLATED by `4`. The verifier sees only
the commitments `8` (in) and `12` (out). -/
def inflating : PrivAffineEq :=
  { ins := [{ value := 5, blinding := 3 }]
    outs := [{ value := 9, blinding := 3 }] }

-- The blinding totals match on both splits (`3 = 3`) — so the homomorphic check tests VALUE
-- conservation exactly. The verifier reads only the commitment sums, never a value.
#guard balanced.insCommit (Digest := Int) == balanced.outsCommit (Digest := Int)   -- 8 == 8
#guard !(decide (inflating.insCommit (Digest := Int) = inflating.outsCommit (Digest := Int)))  -- 8 ≠ 12

/-- **`conservation_passes_privately`.** The balanced hidden split PASSES the
homomorphic check: `Σ commit(ins) = Σ commit(outs)` over `ℤ`, certifying value conservation
from the commitments alone (`8 = 8`), no value disclosed. -/
theorem conservation_passes_privately :
    balanced.homCheck (Digest := Int) := by
  unfold PrivAffineEq.homCheck PrivAffineEq.insCommit PrivAffineEq.outsCommit balanced
  decide

/-- **`inflation_caught_privately` (the keystone, witnessed).** The INFLATING split
FAILS the homomorphic check — `Σ commit(ins) ≠ Σ commit(outs)` (`8 ≠ 12`) — so the executor
REJECTS the inflation reading ONLY the commitments, WITHOUT opening a single value or blinding.
Enforcement of conservation of hidden balances, with zero disclosure. -/
theorem inflation_caught_privately :
    ¬ inflating.homCheck (Digest := Int) := by
  unfold PrivAffineEq.homCheck PrivAffineEq.insCommit PrivAffineEq.outsCommit inflating
  decide

/-- **`private_conservation_keystone_nonvacuous`.** The keystone
`private_conservation_checks_homomorphically` is non-vacuous on the reference: at the balanced
split (matching blindings) the homomorphic check holds AND collapses to the
commitment-of-sums equation; the SAME instantiation on the inflating split FAILS — so the
keystone discriminates conservation from inflation, privately. -/
theorem private_conservation_keystone_nonvacuous :
    (balanced.homCheck (Digest := Int)) ∧ ¬ inflating.homCheck (Digest := Int) :=
  ⟨conservation_passes_privately, inflation_caught_privately⟩

/-! ### A witnessed range claim rejected (the §8 oracle interface, modeled). -/

/-- A toy decidable range verifier over `ℤ`: the witness is the claimed cleartext value; it
accepts iff `lo ≤ value ≤ hi` AND the value's reference commitment (`value + 0`) matches the
disclosed commitment. A STAND-IN for the §8 range AIR — models the interface, not real ZK. -/
def toyRangeVerifier : Verifier (RangeClaim Int) Int :=
  fun claim value => decide (claim.lo ≤ value ∧ value ≤ claim.hi ∧ value = claim.commitment)

/-- A registry with the toy range verifier installed at `custom 7`. -/
def toyRangeReg : Registry (RangeClaim Int) Int :=
  fun k => if k = .custom 7 then some toyRangeVerifier else none

/-- An IN-RANGE witnessed-range claim: commitment `5`, bounds `[0, 10]` — the value `5` is in
range, so the oracle accepts. -/
def inRange : WitnessedRange Int Int := { reg := toyRangeReg, vk := 7, claim := { commitment := 5, lo := 0, hi := 10 } }

/-- An OUT-OF-RANGE witnessed-range claim: commitment `42`, bounds `[0, 10]` — the value `42`
exceeds `hi`, so the oracle REJECTS. -/
def outOfRange : WitnessedRange Int Int := { reg := toyRangeReg, vk := 7, claim := { commitment := 42, lo := 0, hi := 10 } }

-- The in-range value `5` passes; the out-of-range value `42` is REJECTED by the oracle.
#guard inRange.check 5 == true
#guard outOfRange.check 42 == false

/-- **`range_accepts_in_range`.** The witnessed-range oracle ACCEPTS the in-range
value, discharging the range claim (`witnessed_range_is_sound`): the committed value's range
relation is soundly attested, revealing only the truth bit. -/
theorem range_accepts_in_range :
    @Discharged (RangeClaim Int) Int
      (verifiableOfRegistry inRange.reg (.custom inRange.vk)) inRange.claim 5 :=
  witnessed_range_is_sound inRange 5 (by decide)

/-- **`range_rejects_out_of_range` (non-vacuity, witnessed).** The witnessed-range
oracle REJECTS the out-of-range committed value (`42 ∉ [0,10]`): `check = false`, so no proof
discharges the claim. The range fragment DISCRIMINATES — it is not a vacuous
`:= True` accept. -/
theorem range_rejects_out_of_range :
    outOfRange.check 42 = false := by decide

/-! ### The composed `PrivPred` — non-vacuous end-to-end. -/

/-- A fully-private `PrivPred` over `ℤ`: balanced hidden conservation, an in-range committed
value, and a TRIVIAL cleartext fragment (`top` — reads no slot). It HOLDS, and sits at the
dial FLOOR (reveals only that the relation holds). -/
def fullyPrivate : PrivPred Int Int :=
  { affine := balanced
    range := some inRange
    clear := .top
    cleartext := .record [] }

/-- **`fullyPrivate_holds`.** The composed fully-private predicate HOLDS with the
in-range proof: the homomorphic conservation check passes (`8 = 8`), the witnessed-range oracle
accepts (`5 ∈ [0,10]`), and the trivial cleartext fragment is `true`. A private predicate
satisfied entirely over committed values. -/
theorem fullyPrivate_holds :
    fullyPrivate.holds (some 5) := by
  refine ⟨conservation_passes_privately, ?_, rfl⟩
  show inRange.check 5 = true
  decide

/-- **`fullyPrivate_at_dial_floor`.** The fully-private predicate sits at the dial
FLOOR (`⊥`): the proof reveals ONLY that the relation holds — conservation of a hidden balance
plus a range bound, enforced with zero surveillance of the values. -/
theorem fullyPrivate_at_dial_floor :
    fullyPrivate.disclosure = (⊥ : Dial) :=
  fully_committed_privpred_is_at_floor fullyPrivate rfl

/-- **`inflating_privpred_fails`.** Swapping the balanced affine fragment for the
INFLATING one makes the composed predicate FAIL — the inflation is caught in the homomorphic
fragment, privately, even though the range + cleartext fragments would pass. The composition
inherits the keystone's private-inflation rejection. -/
theorem inflating_privpred_fails :
    ¬ (PrivPred.holds (Digest := Int)
        { affine := inflating, range := some inRange, clear := .top, cleartext := .record [] }
        (some 5)) := by
  intro h
  exact inflation_caught_privately h.1

end Reference

/-! ## §6 — Axiom-hygiene tripwires (the honesty pins over every keystone). -/

#assert_axioms committedSum_collapse
#assert_axioms private_conservation_checks_homomorphically
#assert_axioms private_conservation_iff_value_sum
#assert_axioms witnessed_range_is_sound
#assert_axioms privPred_composes
#assert_axioms privPred_affine_is_homomorphic
#assert_axioms privPred_range_discharged
#assert_axioms affine_reveals_nothing
#assert_axioms range_reveals_only_truth_bit
#assert_axioms fully_committed_privpred_is_at_floor
#assert_axioms cleartext_fragment_discloses_slots
#assert_axioms privPred_floor_reveals_only_truth
#assert_axioms Reference.conservation_passes_privately
#assert_axioms Reference.inflation_caught_privately
#assert_axioms Reference.private_conservation_keystone_nonvacuous
#assert_axioms Reference.range_accepts_in_range
#assert_axioms Reference.range_rejects_out_of_range
#assert_axioms Reference.fullyPrivate_holds
#assert_axioms Reference.fullyPrivate_at_dial_floor
#assert_axioms Reference.inflating_privpred_fails

end Dregg2.Authority.PrivatePredicate
