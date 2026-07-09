/-
# `Dregg2.Crypto.DowngradeResistance` — DOWNGRADE RESISTANCE, the post-quantum negotiation game
riding on the hybrid-signature keystone.

`HybridCombiner.lean` proved the KEYSTONE: the `ed25519 ∧ ML-DSA` hybrid signature is
EUF-CMA-unforgeable if EITHER the discrete-log floor `SchnorrDLHard` OR the Module-SIS floor
`MSISHard` holds (`hybrid_secure_if_either_floor`). `CapabilityChain.lean`/`RevocationSoundness.lean`
lifted that one-signature keystone to protocol games (attenuation soundness, revocation soundness) by
the same anchoring move. This file rides it to the exact threat the whole no-pre-quantum campaign is
ABOUT: an active man-in-the-middle cannot force two honest parties to accept a WEAKER (classical-only)
cipher suite than the strongest they both support.

The handshake is AUTHENTICATED: each party's view of the negotiation — both parties' supported-suite
sets and the chosen suite — is a transcript SIGNED by each party with its hybrid signature, and each
party VERIFIES the peer's transcript signature before accepting. An honest party signs ONLY a
transcript that records its own true supported set and the strongest common suite. So a successful
downgrade has ONE door, closed by a named carrier already in the tree:

* **Forge a transcript signature.** For both parties to accept a suite `s'` strictly weaker than their
  true strongest-common, some honest party (say A) must have verified the peer's (B's) signature over a
  transcript asserting `negotiated = s'`. But B signs only transcripts whose negotiated suite is the
  strongest common of the recorded sets — and A's acceptance pins the recorded classical set to A's true
  set, so B's honest choice would be the true strongest-common, not `s'`. A transcript B never signed yet
  verifying under B's key IS a `SigScheme.Forgery` on B's key (`downgrade_forces_forgery`), refuting B's
  `EufCma`.

So downgrade resistance reduces to `EufCma` (`downgrade_resistant`), and — because the transcript
authentication IS the HYBRID signature — `EufCma` is discharged by
`HybridCombiner.hybrid_secure_if_either_floor` down to `SchnorrDLHard ∨ MSISHard`
(`downgrade_resistant_under_floor`). No named-carrier laundering: the ONLY irreducible objects are the
discrete-log / Module-SIS floors; the forking reductions are hypotheses (theorems of the existing
forking machinery), never carriers.

**This is the theorem that says "you can't strip the PQ".** Even a QUANTUM adversary that has broken the
classical (ed25519) half cannot downgrade a hybrid handshake: the ML-DSA half keeps the negotiation
transcript unforgeable, so the strongest-common suite the parties would agree on stays authenticated. The
downgrade fails unless BOTH the discrete-log AND the lattice floors fall.

## Modelling notes (honest boundaries).

* **Suites carry a strength preorder.** `Suite` is any `[PartialOrder Suite]`; `weaker < stronger`
  (`Classical < Hybrid`). The strongest common suite of two supported sets is characterised by
  `IsStrongestCommon` (a member of both sets that is ≥ every common member) — unique by antisymmetry
  (`strongest_common_unique`), so no `Finset.max'`-nonemptiness bookkeeping is needed.
* **The transcript is a `SigScheme` body over `(aSupported ‖ bSupported ‖ negotiated)`.** `verify` is the
  `SigScheme.verify` of `HybridCombiner`, reused verbatim; each party's supported set rides INSIDE the
  signed body, so tampering a party's own set is caught by that party's acceptance check (mirrors
  `RevocationSoundness`' epoch-in-the-body).
* **`HonestSigner`** is the `HonestAttestation`/`honestDelegation` analogue: an honest party signs only a
  body recording its true supported set and the strongest-common negotiated suite. An active adversary
  that makes both accept a weaker suite therefore forces an unsigned-yet-verifying transcript — a forgery.
* **The authentication is exactly what buys it.** The load-bearing teeth exhibit an UNAUTHENTICATED
  negotiation (acceptance = "I support the suite", no signature) that IS freely downgradable, contrasted
  with the authenticated game where the same downgrade forces a `Forgery`.

Mirrors `RevocationSoundness.lean`'s anchoring style throughout.
-/
import Dregg2.Crypto.HybridCombiner
import Dregg2.Tactics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Basic

namespace Dregg2.Crypto.DowngradeResistance

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField

variable {SK PK Msg Sig : Type*}
variable {Suite : Type*}

/-! ## The suite strength order — the strongest common suite. -/

/-- **`IsStrongestCommon a b s`** — `s` is the strongest suite both parties support: it lies in BOTH
supported sets and is ≥ every commonly-supported suite. The negotiation target; `Classical < Hybrid`, so
the strongest common is the hybrid suite whenever both support it. -/
@[reducible] def IsStrongestCommon [PartialOrder Suite] (a b : Finset Suite) (s : Suite) : Prop :=
  s ∈ a ∧ s ∈ b ∧ ∀ x ∈ a, x ∈ b → x ≤ s

/-- **The strongest common suite is UNIQUE** — by antisymmetry of the strength order: two strongest
commons of the same supported sets are equal. This is what pins an honest party's negotiated choice. -/
theorem strongest_common_unique [PartialOrder Suite] (a b : Finset Suite) (s s' : Suite)
    (h : IsStrongestCommon a b s) (h' : IsStrongestCommon a b s') : s = s' := by
  obtain ⟨hsa, hsb, hmax⟩ := h
  obtain ⟨hsa', hsb', hmax'⟩ := h'
  exact le_antisymm (hmax' s hsa hsb) (hmax s' hsa' hsb')

/-! ## The authenticated handshake — a transcript signed by each party. -/

/-- **A signed handshake transcript.** Both parties' supported-suite sets, the negotiated suite, and each
party's signature over the body `(aSup ‖ bSup ‖ neg)`. The supported sets ride INSIDE the signed body, so
a party detects tampering of its own set. Mirrors `RevocationSoundness.AttestedRoot`. -/
structure SignedTranscript (Suite Sig : Type*) where
  /-- Party A's advertised supported-suite set (signed inside the body). -/
  aSup : Finset Suite
  /-- Party B's advertised supported-suite set (signed inside the body). -/
  bSup : Finset Suite
  /-- The negotiated suite both parties would accept. -/
  neg : Suite
  /-- Party A's signature over the body `(aSup ‖ bSup ‖ neg)`. -/
  aSig : Sig
  /-- Party B's signature over the body `(aSup ‖ bSup ‖ neg)`. -/
  bSig : Sig

/-- **`AAccepts` — party A accepts the negotiation.** A verifies the PEER (B)'s signature on the
transcript body under B's key, checks its OWN supported set was recorded faithfully (`aSup = aTrue`), and
that it supports the negotiated suite. The `SigScheme.verify` face of A's handshake-finish check. -/
@[reducible] def AAccepts (S : SigScheme SK PK Msg Sig)
    (bodyEnc : Finset Suite → Finset Suite → Suite → Msg)
    (bPk : PK) (aTrue : Finset Suite) (t : SignedTranscript Suite Sig) : Prop :=
  S.verify bPk (bodyEnc t.aSup t.bSup t.neg) t.bSig ∧ t.aSup = aTrue ∧ t.neg ∈ aTrue

/-- **`BAccepts` — party B accepts the negotiation.** Symmetrically: B verifies A's signature under A's
key, checks its own supported set was recorded faithfully (`bSup = bTrue`), and that it supports the
negotiated suite. -/
@[reducible] def BAccepts (S : SigScheme SK PK Msg Sig)
    (bodyEnc : Finset Suite → Finset Suite → Suite → Msg)
    (aPk : PK) (bTrue : Finset Suite) (t : SignedTranscript Suite Sig) : Prop :=
  S.verify aPk (bodyEnc t.aSup t.bSup t.neg) t.aSig ∧ t.bSup = bTrue ∧ t.neg ∈ bTrue

/-- **`HonestSigner bodyEnc Q bTrue`** — an honest party signs ONLY faithful, strongest-common
transcripts: any body it signed (`Q (bodyEnc a b n)`) records its true supported set (`b = bTrue`) and a
negotiated suite that is the strongest common of the recorded sets. The downgrade analogue of
`RevocationSoundness.HonestAttestation`: an honest party never signs off on a suite weaker than the
strongest one it and its (recorded) peer both support. -/
def HonestSigner [PartialOrder Suite] (bodyEnc : Finset Suite → Finset Suite → Suite → Msg)
    (Q : Msg → Prop) (bTrue : Finset Suite) : Prop :=
  ∀ (a b : Finset Suite) (n : Suite),
    Q (bodyEnc a b n) → b = bTrue ∧ IsStrongestCommon a b n

/-! ## Downgrade forgery — an accepted-but-unsigned transcript is a signature forgery. -/

/-- **`accepted_unsigned_is_forgery`.** A transcript that A accepts (B's signature verifies under B's key)
but that B NEVER signed (`¬ Q (body)`) is a fresh valid signature on a body outside B's signing oracle — a
`SigScheme.Forgery` on B's key. The `RevocationSoundness.forged_attestation_is_a_signature_forgery`
analogue. -/
theorem accepted_unsigned_is_forgery (S : SigScheme SK PK Msg Sig)
    (bodyEnc : Finset Suite → Finset Suite → Suite → Msg)
    (bPk : PK) (Q : Msg → Prop) (aTrue : Finset Suite) (t : SignedTranscript Suite Sig)
    (hA : AAccepts S bodyEnc bPk aTrue t)
    (hnever : ¬ Q (bodyEnc t.aSup t.bSup t.neg)) :
    Forgery S bPk Q :=
  ⟨bodyEnc t.aSup t.bSup t.neg, t.bSig, hnever, hA.1⟩

/-- **THE REDUCTION — `downgrade_forces_forgery`.** Suppose party A accepts a transcript whose negotiated
suite `t.neg` is STRICTLY WEAKER than the true strongest-common `best`. Then B's transcript signature IS a
forgery on B's key:

* if B had signed the body, `HonestSigner` forces the recorded sets to be `(aTrue, bTrue)` (A's check
  pinned `aSup = aTrue`; the signer pinned `bSup = bTrue`) and the negotiated suite to be the strongest
  common of those — uniquely `best`. But `t.neg < best`, so `t.neg ≠ best` — contradiction; B did not sign;
* an accepted transcript B never signed is a `Forgery`.

So a downgrade below the strongest-common suite is exactly a transcript-signature forgery. -/
theorem downgrade_forces_forgery [PartialOrder Suite] (S : SigScheme SK PK Msg Sig)
    (bodyEnc : Finset Suite → Finset Suite → Suite → Msg)
    (bPk : PK) (Q : Msg → Prop) (aTrue bTrue : Finset Suite) (best : Suite)
    (honest : HonestSigner bodyEnc Q bTrue)
    (hbest : IsStrongestCommon aTrue bTrue best)
    (t : SignedTranscript Suite Sig)
    (hA : AAccepts S bodyEnc bPk aTrue t)
    (hlt : t.neg < best) :
    Forgery S bPk Q := by
  obtain ⟨hverify, haSup, _hmem⟩ := hA
  by_cases hq : Q (bodyEnc t.aSup t.bSup t.neg)
  · exfalso
    obtain ⟨hbSup, hstrong⟩ := honest t.aSup t.bSup t.neg hq
    rw [haSup, hbSup] at hstrong
    have hneq : t.neg = best := strongest_common_unique aTrue bTrue t.neg best hstrong hbest
    exact absurd hneq (ne_of_lt hlt)
  · exact ⟨bodyEnc t.aSup t.bSup t.neg, t.bSig, hq, hverify⟩

/-- **THE HEADLINE — `downgrade_resistant`.** Under B's `EufCma` (its transcript signature is
unforgeable), no active adversary can make BOTH honest parties accept a suite strictly weaker than their
true strongest-common. A mutual downgrade (`AAccepts ∧ BAccepts` on a transcript with `t.neg < best`)
would, via `downgrade_forces_forgery`, exhibit a forgery on B's key — refuting `EufCma`. So the strongest
common suite both parties support is what they agree on; it cannot be stripped down. -/
theorem downgrade_resistant [PartialOrder Suite] (S : SigScheme SK PK Msg Sig)
    (bodyEnc : Finset Suite → Finset Suite → Suite → Msg)
    (aPk bPk : PK) (Qb : Msg → Prop) (aTrue bTrue : Finset Suite) (best : Suite)
    (honestB : HonestSigner bodyEnc Qb bTrue)
    (hbest : IsStrongestCommon aTrue bTrue best)
    (heufB : EufCma S bPk Qb)
    (t : SignedTranscript Suite Sig)
    (hlt : t.neg < best)
    (hAccept : AAccepts S bodyEnc bPk aTrue t ∧ BAccepts S bodyEnc aPk bTrue t) :
    False := by
  obtain ⟨hA, _hB⟩ := hAccept
  exact heufB (downgrade_forces_forgery S bodyEnc bPk Qb aTrue bTrue best honestB hbest t hA hlt)

/-! ## ANCHORING — downgrade resistance reduces to `SchnorrDLHard ∨ MSISHard` through the combiner.

The transcript authentication IS the `ed25519 ∧ ML-DSA` hybrid signature. So B's `EufCma` is not
assumed — it is DISCHARGED by `HybridCombiner.hybrid_secure_if_either_floor` from the discrete-log floor
OR the Module-SIS floor, exactly as `RevocationSoundness.revocation_sound_under_floor` discharges the
authority's key. Downgrade resistance therefore holds if EITHER cryptographic floor does. -/

/-- **"YOU CAN'T STRIP THE PQ" — `downgrade_resistant_under_floor`.** With the per-key forking reductions
(a hybrid transcript forgery ⟹ a `DLSolver` on the classical side, two SelfTargetMSIS solutions on the pq
side — the `HybridCombiner` reductions, not carriers), no active adversary can force both honest parties
onto a suite strictly weaker than their strongest-common provided `SchnorrDLHard C G ∨ MSISHard (augmented
A t) …`. B's `EufCma` is produced by `hybrid_secure_if_either_floor`; the ONLY floors invoked are discrete
log and Module-SIS.

This is the post-quantum statement: even a QUANTUM adversary that has broken the discrete-log (ed25519)
half — so `SchnorrDLHard` fails — still faces `MSISHard` on the ML-DSA half, which keeps the negotiation
transcript unforgeable and the strongest-common hybrid suite authenticated. The downgrade succeeds only if
BOTH floors fall. You cannot strip the post-quantum half of a hybrid handshake. -/
theorem downgrade_resistant_under_floor [PartialOrder Suite]
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (aPk : PKc × PKp) (pkc : PKc) (pkp : PKp)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (A : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (bodyEnc : Finset Suite → Finset Suite → Suite → Msg)
    (Qb : Msg → Prop) (aTrue bTrue : Finset Suite) (best : Suite)
    (dlFork : Forgery Cl pkc Qb → DLSolver C G)
    (msisFork : Forgery Pq pkp Qb →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((β + β) + (β + β)))
    (honestB : HonestSigner bodyEnc Qb bTrue)
    (hbest : IsStrongestCommon aTrue bTrue best)
    (tr : SignedTranscript Suite (Sigc × Sigp))
    (hlt : tr.neg < best)
    (hAccept : AAccepts (hybrid Cl Pq) bodyEnc (pkc, pkp) aTrue tr ∧
      BAccepts (hybrid Cl Pq) bodyEnc aPk bTrue tr) :
    False := by
  have heuf : EufCma (hybrid Cl Pq) (pkc, pkp) Qb :=
    hybrid_secure_if_either_floor Cl Pq pkc pkp Qb C G A t β dlFork msisFork hfloor
  exact downgrade_resistant (hybrid Cl Pq) bodyEnc aPk (pkc, pkp) Qb aTrue bTrue best
    honestB hbest heuf tr hlt hAccept

/-! ## Teeth — the guarantee FIRES on concrete data, and authentication is load-bearing.

Suites are `Bool` with `Classical := false < Hybrid := true`. Both parties support `{classical, hybrid}`,
so the strongest common suite is `hybrid`. Over the toy `SigScheme` (`sig = (pk, m)`, the demo oracle):

(a) an HONEST handshake agrees on the strongest common suite (`hybrid`) and A accepts it;
(b) an AUTHENTICATED downgrade to `classical` FORCES a `Forgery` (via the full `downgrade_forces_forgery`
    on concrete data with a provable `HonestSigner`);
(c) — LOAD-BEARING — an UNAUTHENTICATED negotiation (acceptance = "I support the suite", no transcript
    signature) IS freely downgradable: both parties accept `classical` though the strongest common is
    `hybrid`. So the transcript authentication is exactly what buys downgrade resistance. -/

section Teeth

/-- The toy negotiation message: `(aSupported, bSupported, negotiated)`. -/
@[reducible] def toyMsg := Finset Bool × Finset Bool × Bool

/-- The demo transcript-signing scheme over `toyMsg`: a signature is `(pk, m)`, valid iff it equals that
(the oracle of `RevocationSoundness`/`CapabilityChain`, stands in for `hybrid Cl Pq`). -/
@[reducible] def toyS : SigScheme ℕ ℕ toyMsg (ℕ × toyMsg) where
  pkOf sk := sk
  sign sk m := (sk, m)
  verify pk m s := s = (pk, m)

/-- The demo body encoding: the transcript body IS `(aSup, bSup, neg)` (a stand-in for `signing_message`,
injective so `HonestSigner` is provable). -/
@[reducible] def toyBodyEnc : Finset Bool → Finset Bool → Bool → toyMsg := fun a b n => (a, b, n)

/-- Party B's signing oracle: B honestly signed ONLY the strongest-common transcript — both parties
support `{classical, hybrid}` and the negotiated suite is `hybrid` (`true`). -/
@[reducible] def toyQb : toyMsg → Prop :=
  fun m => m = ({false, true}, {false, true}, true)

/-- **B is an honest signer.** Any body B signed records B's true supported set `{classical, hybrid}` and
the strongest-common negotiated suite. Provable because the body encoding is injective. -/
theorem toyHonest : HonestSigner toyBodyEnc toyQb ({false, true} : Finset Bool) := by
  intro a b n hq
  simp only [toyQb, toyBodyEnc, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl, rfl⟩ := hq
  exact ⟨rfl, by decide⟩

/-! ### (a) The honest handshake agrees on the strongest common suite. -/

/-- The honest transcript: both support `{classical, hybrid}`, negotiate `hybrid` (`true`), each signature
`(pk, body)` valid under its key (A = `200`, B = `100`). -/
def honestT : SignedTranscript Bool (ℕ × toyMsg) :=
  { aSup := {false, true}, bSup := {false, true}, neg := true,
    aSig := (200, ({false, true}, {false, true}, true)),
    bSig := (100, ({false, true}, {false, true}, true)) }

/-- **Honest handshake ACCEPTED.** A accepts the honest transcript: B's signature verifies under key
`100`, A's own supported set is intact, and A supports the negotiated `hybrid`. -/
theorem tooth_honest_A_accepts : AAccepts toyS toyBodyEnc 100 ({false, true} : Finset Bool) honestT := by
  decide

/-- **Honest handshake agrees on the STRONGEST common suite.** The negotiated suite of the honest
transcript is the strongest common (`hybrid`) of the two supported sets — no downgrade. -/
theorem tooth_honest_agrees_strongest :
    IsStrongestCommon ({false, true} : Finset Bool) {false, true} honestT.neg := by decide

/-! ### (b) An authenticated downgrade forces a forgery. -/

/-- The DOWNGRADED transcript: both support `{classical, hybrid}` but the negotiated suite is `classical`
(`false`) — a downgrade. B's signature `(100, body)` verifies on the wire, yet B never signed this body. -/
def dgT : SignedTranscript Bool (ℕ × toyMsg) :=
  { aSup := {false, true}, bSup := {false, true}, neg := false,
    aSig := (200, ({false, true}, {false, true}, false)),
    bSig := (100, ({false, true}, {false, true}, false)) }

/-- **The authenticated downgrade EXHIBITS a `Forgery` (the guarantee fires).** Running the full
`downgrade_forces_forgery` on concrete data: A accepts a `classical` negotiation strictly weaker than the
strongest common `hybrid`, so B's transcript signature is a fresh valid signature on a body B never signed
— a `SigScheme.Forgery` on B's key `100`, the object `downgrade_resistant` refutes via `EufCma`. -/
theorem toy_downgrade_forces_forgery : Forgery toyS 100 toyQb :=
  downgrade_forces_forgery toyS toyBodyEnc 100 toyQb {false, true} {false, true} true
    toyHonest (by decide) dgT (by decide) (by decide)

/-! ### (c) An UNAUTHENTICATED negotiation is freely downgradable — authentication is load-bearing. -/

/-- **Unauthenticated acceptance** — the party accepts any suite it supports, with NO transcript signature
to check. The straw handshake the authentication upgrades. -/
@[reducible] def AcceptsUnauth (supported : Finset Suite) (neg : Suite) : Prop := neg ∈ supported

/-- **THE LOAD-BEARING TOOTH (abstract) — without authentication, a downgrade is FREE.** If both parties
support a suite `weak` strictly weaker than their strongest-common `best`, then under UNauthenticated
acceptance BOTH accept `weak` — a successful downgrade with nothing to prevent it. Contrast
`downgrade_forces_forgery`: with the transcript signature, the SAME downgrade requires a `Forgery`. So the
authentication is exactly what buys downgrade resistance. -/
theorem unauthenticated_admits_downgrade [PartialOrder Suite]
    (aTrue bTrue : Finset Suite) (best weak : Suite)
    (_hbest : IsStrongestCommon aTrue bTrue best)
    (hwa : weak ∈ aTrue) (hwb : weak ∈ bTrue) (hlt : weak < best) :
    AcceptsUnauth aTrue weak ∧ AcceptsUnauth bTrue weak ∧ weak < best :=
  ⟨hwa, hwb, hlt⟩

/-- **THE LOAD-BEARING TOOTH (concrete).** Both parties support `{classical, hybrid}`; the strongest
common is `hybrid`; yet under unauthenticated acceptance BOTH accept `classical`, and `classical < hybrid`
— a real downgrade the unauthenticated handshake cannot stop. The authenticated handshake turns this exact
attack into a `Forgery` (`toy_downgrade_forces_forgery`). -/
theorem unauthenticated_is_downgradable :
    AcceptsUnauth ({false, true} : Finset Bool) false ∧
    AcceptsUnauth ({false, true} : Finset Bool) false ∧
    IsStrongestCommon ({false, true} : Finset Bool) {false, true} true ∧
    (false : Bool) < true := by decide

-- The strongest common suite of two both-supporting parties is HYBRID, not classical…
#guard decide (IsStrongestCommon ({false, true} : Finset Bool) {false, true} true)
#guard decide (¬ IsStrongestCommon ({false, true} : Finset Bool) {false, true} false)
-- …classical is strictly weaker than hybrid (the direction a downgrade moves).
#guard decide ((false : Bool) < true)
-- The forged downgrade signature verifies on the wire…
#guard decide (toyS.verify 100 (toyBodyEnc {false, true} {false, true} false)
  (100, ({false, true}, {false, true}, false)))
-- …yet B never signed a classical negotiation (the Forgery); it signed only the hybrid one.
#guard decide (¬ toyQb (toyBodyEnc {false, true} {false, true} false))
#guard decide (toyQb (toyBodyEnc {false, true} {false, true} true))
-- UNauthenticated: classical is freely accepted by a hybrid-supporting party — downgradable.
#guard decide (AcceptsUnauth ({false, true} : Finset Bool) false)

end Teeth

/-! ### Axiom hygiene. -/

#assert_all_clean [
  strongest_common_unique,
  accepted_unsigned_is_forgery,
  downgrade_forces_forgery,
  downgrade_resistant,
  downgrade_resistant_under_floor,
  toyHonest,
  tooth_honest_A_accepts,
  tooth_honest_agrees_strongest,
  toy_downgrade_forces_forgery,
  unauthenticated_admits_downgrade,
  unauthenticated_is_downgradable
]

end Dregg2.Crypto.DowngradeResistance
