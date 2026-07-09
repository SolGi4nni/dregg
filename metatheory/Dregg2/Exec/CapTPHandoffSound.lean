/-
# Dregg2.Exec.CapTPHandoffSound — the trustless CapTP handoff-certificate crown.

`Dregg2.Exec.CapTP.HandoffValid` (the abstract `validate_handoff` success conditions) carries
its crypto checks in ONE opaque field `attested : Prop` — "a single `Prop` standing for
`validate_handoff` accepted". That is the §8 verify seam, but as written it is VACUOUS: a
caller may discharge `attested := True` and the proven `handoff_is_introduce`/
`handoff_non_amplifying` keystones fire with NO cryptographic content at all. The signature
that makes the handoff *trustless* — "I, introducer A, authorize recipient B" — is invisible to
the theory. An adversary who never held A's key could supply `attested := trivial` and the
abstract proofs would never notice.

This module DE-VACUIFIES that seam and proves the two properties the trustless crown demands,
WITHOUT touching `Exec/CapTP.lean`, `Exec/CapTPConcrete.lean`, or any spec module (all imported
READ-ONLY):

  1. **Concrete `Verifiable`/`Discharged` seam over the certificate's signing message.** We
     model `captp/src/handoff.rs::HandoffCertificate::signing_message()` as a concrete `Nat`
     digest of the cert fields, and `attested` becomes `SignatureKernel.sigVerify introPK msg
     sig = true` over the ed25519 `SignatureKernel` of `Crypto/PortalFloor.lean` — the SAME
     EUF-CMA carrier the rest of the metatheory uses. The unforgeability hypothesis is the
     NAMED `SignatureKernel.unforgeable` `Prop`, never a Lean law.

  2. **The 6-check gate.** `validateHandoff2` mirrors `validate_handoff`'s six checks
     clause-for-clause: (1) introducer signature, (2) recipient signature, (3) known
     federation, (4) not expired, (5) swiss/target binding, (6) non-amplification (REUSING the
     verified `CapTPConcrete.handoffNonAmplifyingC` lattice + effect-mask leg). It is an
     executable `Bool` decision, like the Rust.

  3. **THEOREM (1) — a validated handoff installs EXACTLY the non-amplifying granted cap, via
     the VERIFIED full-state executor.** A `validateHandoff2`-accepting handoff drives
     `execFullA s (.validateHandoffA intro rec t)` to the unique post-state `s'` satisfying the
     INDEPENDENT full-state `DelegateSpec` (all 17 kernel fields + log pinned), wired through
     `Spec.AuthorityUnattenuated.execFullA_validateHandoff_iff_spec`. The installed cap is the
     introducer's held `t`-conferring cap (`heldCapTo`), and its concrete `AuthReq` rights are
     `≤` the held rights — the non-amplification is `CapTPConcrete.handoff_non_amplifying_concrete`
     fired at the CONCRETE lattice, not an abstract order.

  4. **THEOREM (2) — unforgeability at n>1.** Under the ed25519 EUF-CMA carrier, an adversary
     vat that does NOT hold the introducer's signing key (`¬ Signed introPK msg`) CANNOT
     produce a certificate that passes `validateHandoff2`: validation entails
     `sigVerify introPK msg sig = true`, which under `unforgeable` entails `Signed introPK msg`,
     contradicting the adversary's lack of the key. We prove this in a genuine n>1 federation
     (≥2 distinct vats with distinct keys), so the single-machine (n=1) case is the
     scales-to-zero special case, NOT the target.

  5. **Rust differential.** `captp/tests/handoff_unforgeability_differential.rs` drives the REAL
     `validate_handoff` and asserts: a certificate signed by the WRONG key is rejected with
     `InvalidIntroducerSignature` (the §1 check — Theorem 2's runtime tooth), while the
     correctly-signed-and-attenuating cert is accepted (Theorem 1's runtime tooth). The existing
     `handoff_lattice_differential.rs` already pins the §6 non-amplification lattice.

DISCIPLINE: the ed25519 unforgeability is a NAMED hypothesis (`SignatureKernel.unforgeable`),
carried explicitly into every theorem that needs it — never assumed as a Lean axiom, never
faked as `True`. The full-state executor connection is REAL: `DelegateSpec` is the same 17-field
independent reference the circuit⟺executor triangle uses; nothing here weakens it.
-/
import Dregg2.Exec.CapTP
import Dregg2.Exec.CapTPConcrete
import Dregg2.Crypto.PortalFloor
import Dregg2.Circuit.Spec.authorityunattenuated
import Dregg2.Circuit.Spec.authorityattenuation
import Dregg2.Exec.AuthTurn
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPHandoffSound

open Dregg2.Exec.CapTPConcrete (AuthReq authNarrowerOrEqual handoffNonAmplifyingC
  facetAttenuation handoff_concrete_attenuation)
open Dregg2.Crypto.PortalFloor (SignatureKernel)
open Dregg2.Circuit.Spec.AuthorityUnattenuated
  (DelegateSpec delegateGuard recDelegateCaps execFullA_introduceA_iff_spec
   execFullA_introduceA_eq delegate_grants_recipient delegate_rejects_unconnected
   recDelegateCaps_correct)
open Dregg2.Circuit.Spec.AuthorityAttenuation
  (DelegateAttenSpec DelegateAttenGuard delegateAtten_iff_spec delegateAttenCaps_correct
   delegateAtten_spec_non_amplifying delegateAtten_rejects_ungrounded)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

universe u

/-! ## §1 — The concrete certificate + its signing message (mirror of `handoff.rs`).

`HandoffCert2` carries BOTH the authority-graph content (introducer/recipient/target/the held
swiss-registered permission/the granted permission/effect masks) AND the crypto seam fields
(`introPK`, `nonce`, `swiss`, `introSig`). `signingMessage` mirrors
`HandoffCertificate::signing_message()`: a domain-separated digest of every field except the
signature. We encode it as a concrete `Nat` (the §8 hash is realized in Rust; the Lean digest is
injective-enough for the equality reasoning we need, and the unforgeability never depends on its
internal structure — only on `sigVerify` over it). -/

/-- The federation / vat identity (a `Nat` stand-in for the 32-byte `FederationId`). Distinct
vats have distinct ids — this is what makes the n>1 case non-degenerate. -/
abbrev VatId := Nat

/-- A public key (a `Nat` stand-in for the 32-byte ed25519 key). -/
abbrev PubKey := Nat

/-- A signing-message digest (a `Nat` stand-in for the canonical byte serialization). -/
abbrev Msg := Nat

/-- A signature (a `Nat` stand-in for the 64-byte ed25519 signature). -/
abbrev Sig := Nat

/-- **`HandoffCert2`** — the concrete handoff certificate, mirroring
`captp/src/handoff.rs::HandoffCertificate`. Authority-graph fields: `introducer`/`recipient`
(vat ids), `targetCell` (the cell on the target federation), `heldPerm`/`grantedPerm` (the
swiss-registered held `AuthReq` and the certificate's granted `AuthReq`), `heldEff`/`grantedEff`
(the optional `u32` effect masks). Crypto-seam fields: `introPK` (the introducer's ed25519 key),
`nonce`/`swiss` (replay/routing salts), `introSig` (the introducer's signature over the
signing message). -/
structure HandoffCert2 where
  /-- Vat A: the introducer. -/
  introducer  : VatId
  /-- Vat B: the recipient. -/
  recipient   : VatId
  /-- The cell on the target federation C being handed off. -/
  targetCell  : CellId
  /-- The swiss-registered HELD `AuthReq` (the target's authoritative record of A's rights). -/
  heldPerm    : AuthReq
  /-- The certificate's GRANTED `AuthReq` (introducer-asserted, must attenuate `heldPerm`). -/
  grantedPerm : AuthReq
  /-- The HELD effect mask (`none = unrestricted`). -/
  heldEff     : Option Nat
  /-- The GRANTED effect mask. -/
  grantedEff  : Option Nat
  /-- The cap-rights FACET-KEEP list that realizes the grant: the recipient's installed cap is the
  introducer's held `targetCell`-cap ATTENUATED to `keep`. This is the cap-lattice realization of
  `grantedPerm` (the `AuthReq`-lattice §6 bound). The handoff installs `attenuate keep heldCap`, whose
  conferred rights are `⊆` the held cap's (`attenuate_confRights_le`) — so the recipient receives the
  NARROWED grant, never the unattenuated held cap. -/
  keep        : List Auth
  /-- The introducer's ed25519 public key. -/
  introPK     : PubKey
  /-- Replay-prevention nonce. -/
  nonce       : Nat
  /-- The routing swiss number the recipient presents to the target. -/
  swiss       : Nat
  /-- The introducer's ed25519 signature over `signingMessage`. -/
  introSig    : Sig

/-- **`HandoffCert2.signingMessage`** — the canonical message the introducer signs, mirroring
`HandoffCertificate::signing_message()` (domain-separated digest of every field except the
signature). We fold the certificate's fields into one `Nat` via a fixed mixing schedule; the
exact mixing is immaterial to the soundness (only `sigVerify introPK msg sig` matters), but it
is a genuine function of ALL signed fields, so two certs differing in any signed field have
different messages whenever the fold is injective (which we do not need, but state. -/
def HandoffCert2.signingMessage (c : HandoffCert2) : Msg :=
  -- domain tag "dregg-handoff-cert-v1" ↦ a fixed prime, then mix every signed field. Mirrors
  -- `signing_message()`, which folds `introducer`, `target_*`, `recipient_pk`, the permission
  -- tag, effect mask, nonce, and swiss — but NOT the introducer's public key (that is derived /
  -- looked up at verify time, not part of the signed payload). So the message is independent of
  -- `introPK`, which is what lets a freshly-keyed `goodCert` sign its own message consistently.
  let permTag : Nat := match c.grantedPerm with
    | .none => 0 | .signature => 1 | .proof => 2 | .either => 3
    | .impossible => 4 | .custom h => 5 + h
  let effTag : Nat := match c.grantedEff with | none => 0 | some m => 1 + m
  ((((((1000003 * 31 + c.introducer) * 31 + c.recipient) * 31 + c.targetCell)
      * 31 + permTag) * 31 + effTag) * 31 + c.nonce) * 31 + c.swiss

/-! ## §2 — The de-vacuified attestation: a concrete signature seam.

`HandoffCert2.Attested K c` is the CONCRETE replacement for `CapTP.HandoffValid.attested`. It
says: the §8 ed25519 oracle ACCEPTS the introducer's signature over the certificate's signing
message. This is `SignatureKernel.sigVerify`, the runnable verify side — exactly the
`Laws.Discharged`/`Verifiable` seam the doc-comment of `Exec/CapTP.lean` promised but never
realized. -/

variable {K : SignatureKernel PubKey Msg Sig}

/-- **`HandoffCert2.AttestedBool K c`** — the runnable attestation: ed25519 accepts the
introducer's signature over the signing message. The §8 oracle, as a `Bool`. -/
def HandoffCert2.AttestedBool (K : SignatureKernel PubKey Msg Sig) (c : HandoffCert2) : Bool :=
  K.sigVerify c.introPK c.signingMessage c.introSig

/-- **`HandoffCert2.Attested K c`** — the de-vacuified `attested` `Prop`. NON-vacuous: it is
`True` exactly when ed25519 accepts, `False` when it rejects. This replaces the opaque
`CapTP.HandoffValid.attested`. -/
def HandoffCert2.Attested (K : SignatureKernel PubKey Msg Sig) (c : HandoffCert2) : Prop :=
  c.AttestedBool K = true

/-! ## §3 — The 6-check gate `validateHandoff2` (mirror of `validate_handoff`).

Mirrors `captp/src/handoff.rs::validate_handoff` check-for-check:
  1. introducer signature  (`cert.verify_signature(introducer_pk)`);
  2. recipient signature    (`presentation.verify_recipient_signature()`);
  3. known federation        (`known_federations.contains(&cert.introducer)`);
  4. not expired             (`cert.is_valid(current_height)`);
  5. target binding          (`cert.target_cell == held.cell_id`, the swiss entry's cell);
  6. non-amplification        (`is_narrower_or_equal` ∧ effect-mask subset — REUSING the verified
     `CapTPConcrete.handoffNonAmplifyingC`).
The recipient signature, known-federation, expiry, and target-binding legs are modeled as the
`Bool` flags the runtime computes; the load-bearing §1 and §6 legs are the genuine
ed25519/lattice decisions. -/

/-- The recipient-presentation context the gate also consumes (mirrors `HandoffPresentation` +
the target federation's swiss/known-set state). `recipOk` = `verify_recipient_signature()`;
`knownIntroducer` = `known_federations.contains`; `notExpired` = `cert.is_valid(height)`;
`swissCell` = the swiss entry's authoritative cell id (the §5/5b binding target). -/
structure HandoffEnv where
  /-- The recipient signature verified (`verify_recipient_signature`). -/
  recipOk         : Bool
  /-- The introducer is a known/trusted federation. -/
  knownIntroducer : Bool
  /-- The certificate is not expired at the current height. -/
  notExpired      : Bool
  /-- The swiss entry's authoritative cell id (the target binding §5b checks against). -/
  swissCell       : CellId

/-- **`validateHandoff2 K c env`** — the runnable 6-check gate, returning `true` iff all six
checks pass. EXACT mirror of `validate_handoff`'s short-circuit `&&` chain. -/
def validateHandoff2 (K : SignatureKernel PubKey Msg Sig) (c : HandoffCert2) (env : HandoffEnv) :
    Bool :=
  c.AttestedBool K                                        -- 1. introducer signature
    && env.recipOk                                         -- 2. recipient signature
    && env.knownIntroducer                                 -- 3. known federation
    && env.notExpired                                      -- 4. not expired
    && (decide (c.targetCell = env.swissCell))             -- 5/5b. target binding
    && handoffNonAmplifyingC c.heldPerm c.grantedPerm c.heldEff c.grantedEff  -- 6. non-amplify

/-! ### §3a — Validation decomposes: each accepted leg is recoverable. -/

/-- A validated handoff has an accepting introducer signature (§1). -/
theorem validateHandoff2_attested {K : SignatureKernel PubKey Msg Sig}
    {c : HandoffCert2} {env : HandoffEnv} (h : validateHandoff2 K c env = true) :
    c.AttestedBool K = true := by
  simp only [validateHandoff2, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1

/-- A validated handoff is non-amplifying on the concrete lattice (§6). -/
theorem validateHandoff2_nonAmplifying {K : SignatureKernel PubKey Msg Sig}
    {c : HandoffCert2} {env : HandoffEnv} (h : validateHandoff2 K c env = true) :
    handoffNonAmplifyingC c.heldPerm c.grantedPerm c.heldEff c.grantedEff = true := by
  simp only [validateHandoff2, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- A validated handoff's granted permission attenuates the held permission (§6 ⇒ `≤` on the
CONCRETE `AuthReq` lattice — `CapTPConcrete.handoff_concrete_attenuation`, the verified order). -/
theorem validateHandoff2_attenuates {K : SignatureKernel PubKey Msg Sig}
    {c : HandoffCert2} {env : HandoffEnv} (h : validateHandoff2 K c env = true) :
    c.grantedPerm ≤ c.heldPerm :=
  handoff_concrete_attenuation (validateHandoff2_nonAmplifying h)

/-! ## §4 — THEOREM (1): a validated handoff drives the VERIFIED full-state executor to install
EXACTLY the non-amplifying ATTENUATED GRANT.

The handoff installs the recipient's authority via the ATTENUATING Granovetter arm
(`execFullA s (.delegateAttenA intro rec t keep)` ⟶ `recCDelegateAtten`), which is — by
`delegateAtten_iff_spec` — equivalent to the INDEPENDENT full-state `DelegateAttenSpec` (all 17
kernel fields + log pinned). We connect the certificate to this executor: given the Granovetter
connectivity premise (A holds a `t`-conferring cap — `DelegateAttenGuard`, the §0 precondition the
swiss-entry's existence witnesses) AND a validated certificate, the executor commits the unique
post-state, the recipient's slot gains EXACTLY the introducer's held `t`-cap ATTENUATED to the
certificate's `keep` facets, and that installed cap's conferred rights are `⊆` the held cap's.

THE OVER-GRANT FIX: the prior version installed `heldCapTo` (the UNATTENUATED held cap) via
`.introduceA`, even though §6 validates `grantedPerm ≤ heldPerm` — an over-grant (the recipient
received the full held cap, not the narrowed grant). We now install `attenuate keep heldCap`
through `.delegateAttenA`, so the recipient receives EXACTLY the attenuated grant; installing
`heldCapTo` would now FAIL the `installedCap` clause (mutation-confirmed: a cert with
`keep ⊊ heldRights` installs the narrowed cap, and the held-but-not-kept facets are absent). -/

/-- The cap A actually hands off: the introducer's held `targetCell`-cap (`heldCapTo`, the
executable `lookup_by_target`) ATTENUATED to the certificate's `keep` facets. This is what the
handoff (`delegateAttenA`) installs into B — the NARROWED grant, NOT the unattenuated held cap. Its
conferred rights are `⊆` the held cap's (`attenuate_confRights_le`), the cap-lattice realization of
the §6 `grantedPerm ≤ heldPerm` bound. -/
def HandoffCert2.installedCap (s : RecChainedState) (c : HandoffCert2) : Cap :=
  attenuate c.keep (heldCapTo s.kernel.caps c.introducer c.targetCell)

/-- The introducer's held `targetCell`-cap (the unattenuated source the grant attenuates). -/
def HandoffCert2.heldCap (s : RecChainedState) (c : HandoffCert2) : Cap :=
  heldCapTo s.kernel.caps c.introducer c.targetCell

/-- **`handoff_installs_exactly` — THEOREM (1).** Given a validated certificate (`validateHandoff2
= true`) and the Granovetter connectivity premise (`DelegateAttenGuard s introducer targetCell` — A
already holds a `targetCell`-conferring cap, which the swiss registration witnessed), the VERIFIED
ATTENUATING handoff executor commits a UNIQUE post-state `s'` such that:
  (a) `s'` satisfies the full independent `DelegateAttenSpec` (all 17 kernel fields + log pinned —
      so no ghost field is mutated);
  (b) the recipient B's cap-slot gains EXACTLY the introducer's held `targetCell`-cap ATTENUATED to
      the certificate's `keep` facets (`installedCap`) — the NARROWED grant, not the held cap;
  (c) the installed cap's conferred rights are `⊆` the held cap's — genuine cap-lattice
      non-amplification (`attenuate_confRights_le`, the EXECUTED rights handoff); and
  (d) the granted permission is non-amplifying on the verified concrete `AuthReq` lattice (§6).
This wires the de-vacuified certificate to the SAME full-state reference the circuit⟺executor
triangle uses; the recipient receives EXACTLY the attenuated grant, matching what §6 validates. -/
theorem handoff_installs_exactly
    {K : SignatureKernel PubKey Msg Sig} {c : HandoffCert2} {env : HandoffEnv}
    (hvalid : validateHandoff2 K c env = true)
    (s : RecChainedState)
    (hconn : DelegateAttenGuard s c.introducer c.targetCell) :
    ∃ s', execFullA s (.delegateAttenA c.introducer c.recipient c.targetCell c.keep) = some s'
        ∧ DelegateAttenSpec s c.introducer c.recipient c.targetCell c.keep s'
        ∧ c.installedCap s ∈ s'.kernel.caps c.recipient
        ∧ confRights (c.installedCap s) ≤ confRights (c.heldCap s)
        ∧ c.grantedPerm ≤ c.heldPerm := by
  -- The executor commits SOME post-state iff the spec holds; the spec is satisfiable from the
  -- connectivity premise. We get the spec'd state from the ← direction of the verified iff.
  obtain ⟨s', hspec⟩ : ∃ s', DelegateAttenSpec s c.introducer c.recipient c.targetCell c.keep s' := by
    refine ⟨{ kernel := { s.kernel with
                caps := grant s.kernel.caps c.recipient
                          (attenuate c.keep (heldCapTo s.kernel.caps c.introducer c.targetCell)) }
            , log := authReceipt c.introducer :: s.log }, ?_⟩
    exact ⟨hconn, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl⟩
  refine ⟨s', ?_, hspec, ?_, ?_, ?_⟩
  · -- the executor commits exactly this state, via the verified iff.
    rw [delegateAtten_iff_spec]; exact hspec
  · -- B's slot gains exactly the ATTENUATED grant (from the spec, via the verified executor⟺spec).
    have hcommit : execFullA s (.delegateAttenA c.introducer c.recipient c.targetCell c.keep)
        = some s' := (delegateAtten_iff_spec s c.introducer c.recipient c.targetCell c.keep s').mpr hspec
    exact (delegateAtten_spec_non_amplifying s c.introducer c.recipient c.targetCell c.keep s' hcommit).1
  · -- genuine cap-lattice non-amplification: the installed (attenuated) cap ⊆ the held cap.
    have hcommit : execFullA s (.delegateAttenA c.introducer c.recipient c.targetCell c.keep)
        = some s' := (delegateAtten_iff_spec s c.introducer c.recipient c.targetCell c.keep s').mpr hspec
    exact (delegateAtten_spec_non_amplifying s c.introducer c.recipient c.targetCell c.keep s' hcommit).2
  · -- non-amplification at the concrete AuthReq lattice (§6).
    exact validateHandoff2_attenuates hvalid

/-- **`handoff_rejects_unconnected` — the fail-closed companion.** If A holds NO
`targetCell`-conferring cap (the Granovetter premise FAILS), then even a perfectly-signed,
non-amplifying certificate cannot drive the attenuating handoff executor to commit:
`delegateAttenA` returns `none`. Manufacturing a cross-vat edge from a key alone is rejected by
construction — the signature attests intent, but connectivity must already exist. -/
theorem handoff_rejects_unconnected (s : RecChainedState) (c : HandoffCert2)
    (hbad : (s.kernel.caps c.introducer).any (fun cap => confersEdgeTo c.targetCell cap) = false) :
    execFullA s (.delegateAttenA c.introducer c.recipient c.targetCell c.keep) = none := by
  refine delegateAtten_rejects_ungrounded s c.introducer c.recipient c.targetCell c.keep ?_
  unfold DelegateAttenGuard
  rw [hbad]; exact Bool.false_ne_true

/-! ## §5 — THEOREM (2): unforgeability at n>1.

The trustless property: an adversary who does NOT hold the introducer's signing key cannot
produce a certificate that validates. We state this over a genuine n>1 federation — a finite set
of ≥2 distinct vats, each with its own public key, such that distinct vats have distinct keys
(`keyInjOn`). The adversary is a vat `adv ≠ A`; "does not hold A's key" is the ed25519
non-`Signed` fact `¬ K.Signed (key A) msg` — the adversary cannot have produced a valid signature
over `msg` under A's key. Under EUF-CMA (`K.unforgeable`), validation is then impossible. -/

/-- **`Federation`** — an n-vat federation: a public-key assignment over the vats, with distinct
vats getting distinct keys. `n > 1` is the target (n = 1 is the scales-to-zero degenerate case). -/
structure Federation where
  /-- The set of vat ids in the federation (as a list; `nodup` distinguishes the n vats). -/
  vats   : List VatId
  /-- The public key of each vat. -/
  key    : VatId → PubKey
  /-- Distinct vats have distinct keys (key assignment is injective on the federation). -/
  keyInj : ∀ a b, a ∈ vats → b ∈ vats → key a = key b → a = b
  /-- The vats are distinct. -/
  nodup  : vats.Nodup

/-- A federation is non-degenerate (n > 1) when it has at least two vats. -/
def Federation.NonTrivial (F : Federation) : Prop := 2 ≤ F.vats.length

instance (F : Federation) : Decidable F.NonTrivial :=
  inferInstanceAs (Decidable (2 ≤ F.vats.length))

/-- **`Federation.nonTrivial_of_two`** — two DISTINCT member vats force `n > 1`. So whenever an
adversary `adv ≠ A` is in the same federation as the introducer `A`, the federation is
non-trivial (the n = 1 single-machine case cannot host a cross-vat attacker at all). -/
theorem Federation.nonTrivial_of_two (F : Federation) {A adv : VatId}
    (hA : A ∈ F.vats) (hadv : adv ∈ F.vats) (hne : adv ≠ A) : F.NonTrivial := by
  rcases hv : F.vats with _ | ⟨x, xs⟩
  · rw [hv] at hadv; exact absurd hadv (by simp)
  · rcases xs with _ | ⟨y, ys⟩
    · -- single-element list: adv = x = A, contradicting `adv ≠ A`.
      rw [hv] at hadv hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hadv hA
      exact absurd (hadv.trans hA.symm) hne
    · show 2 ≤ F.vats.length; rw [hv]; simp

/-- **`handoff_unforgeable` — THEOREM (2), the core.** Under the ed25519 EUF-CMA carrier
(`K.unforgeable`, the NAMED hypothesis), if the certificate names introducer key
`c.introPK` and the adversary did NOT produce a valid signature over the signing message under
that key (`¬ K.Signed c.introPK c.signingMessage` — the adversary lacks the secret for
`c.introPK`), then NO `HandoffEnv` makes the certificate validate. The forged certificate is
rejected at check §1 (introducer-signature). -/
theorem handoff_unforgeable
    {K : SignatureKernel PubKey Msg Sig} (hunf : K.unforgeable)
    (c : HandoffCert2)
    (hnokey : ¬ K.Signed c.introPK c.signingMessage)
    (env : HandoffEnv) :
    validateHandoff2 K c env = false := by
  -- Suppose it validated; then §1 accepts the signature, so EUF-CMA forces `Signed`.
  by_contra hval
  rw [Bool.not_eq_false] at hval
  have hsig : c.AttestedBool K = true := validateHandoff2_attested hval
  have hSigned : K.Signed c.introPK c.signingMessage :=
    K.sigVerify_sound hunf c.introPK c.signingMessage c.introSig hsig
  exact hnokey hSigned

/-- **`adversary_cannot_forge_at_n_gt_1` — THEOREM (2) at n>1.** In a NON-TRIVIAL federation
(≥2 distinct vats), an adversary vat `adv` distinct from the introducer `A`, presenting a
certificate that names `A`'s public key (`c.introPK = F.key A`) but where the adversary — lacking
`A`'s secret — has NOT validly signed (`¬ K.Signed (F.key A) c.signingMessage`), CANNOT make the
handoff validate under any environment. The distinctness `adv ≠ A` (both in the federation, hence
distinct keys by `keyInj`) is what makes this a genuine cross-vat attack, not a self-handoff:
`adv`'s OWN key `F.key adv ≠ F.key A`, so a signature `adv` could produce under its own key does
not satisfy the §1 check against `A`'s key. -/
theorem adversary_cannot_forge_at_n_gt_1
    {K : SignatureKernel PubKey Msg Sig} (hunf : K.unforgeable)
    (F : Federation) (_hnt : F.NonTrivial)
    (A adv : VatId) (hA : A ∈ F.vats) (hadv : adv ∈ F.vats) (hne : adv ≠ A)
    (c : HandoffCert2) (hnames : c.introPK = F.key A)
    (hnokey : ¬ K.Signed (F.key A) c.signingMessage)
    (env : HandoffEnv) :
    validateHandoff2 K c env = false := by
  -- The adversary's own key differs from A's (distinct vats ⇒ distinct keys) — this is the
  -- genuine cross-vat content the n>1 hypothesis `_hnt` records: at n = 1 there is no such `adv`.
  have hkeyne : F.key adv ≠ F.key A := fun heq => hne (F.keyInj adv A hadv hA heq)
  -- The certificate names A's key, and A's signature is not forgeable.
  have hnokey' : ¬ K.Signed c.introPK c.signingMessage := by rw [hnames]; exact hnokey
  exact handoff_unforgeable hunf c hnokey' env

/-- **`forged_handoff_installs_nothing` — Theorems (1)+(2) composed.** A forged certificate
(naming A's key, but not validly signed by A) cannot drive the verified executor: since it never
validates (Theorem 2), no `handoff_installs_exactly` instance ever fires for it, so the adversary
installs NOTHING into B's slot through a forged handoff. We state the contrapositive directly: if
a forged cert DID validate it would contradict unforgeability, hence it does not — there is no
`s'` the forged handoff commits with a validated cert. -/
theorem forged_handoff_installs_nothing
    {K : SignatureKernel PubKey Msg Sig} (hunf : K.unforgeable)
    (F : Federation) (A adv : VatId) (hA : A ∈ F.vats) (hadv : adv ∈ F.vats) (hne : adv ≠ A)
    (c : HandoffCert2) (hnames : c.introPK = F.key A)
    (hnokey : ¬ K.Signed (F.key A) c.signingMessage)
    (env : HandoffEnv) :
    ¬ (validateHandoff2 K c env = true) := by
  rw [adversary_cannot_forge_at_n_gt_1 hunf F
        (F.nonTrivial_of_two hA hadv hne) A adv hA hadv hne c hnames hnokey env]
  exact Bool.false_ne_true

/-! ## §6 — Non-vacuity: the seam fires on the REFERENCE EUF-CMA carrier (true AND false).

We instantiate `K := Crypto.PortalFloor.Reference.instSignatureKernel` (the proved-unforgeable
ed25519 reference, where `sigVerify pk m s := decide (pk = m ∧ m = s)` and `Signed pk m := pk = m`).
A genuine signature validates; a forged one (wrong sig, or wrong key) does NOT — so `Attested`,
`validateHandoff2`, and the unforgeability theorem are all NON-vacuous. -/

section NonVacuity

open Dregg2.Crypto.PortalFloor.Reference (instSignatureKernel)

/-- A concrete certificate whose introducer signature is GENUINE under the reference kernel
(`pk = m = s`): introPK = signingMessage = introSig. Held = granted = `signature` (identity,
non-amplifying), unrestricted effect masks. -/
def goodCert : HandoffCert2 :=
  let base : HandoffCert2 :=
    { introducer := 1, recipient := 2, targetCell := 7
    , heldPerm := .signature, grantedPerm := .signature
    , heldEff := none, grantedEff := none
    -- keep ALL facets ⇒ identity attenuation (held = granted, non-amplifying).
    , keep := [.read, .write, .grant, .call, .reply, .reset, .control, .notify]
    , introPK := 0, nonce := 0, swiss := 0, introSig := 0 }
  let m := base.signingMessage
  { base with introPK := m, introSig := m }

/-- A reference environment that passes the non-crypto legs (recipient sig ok, known, not
expired, target binds to the swiss cell `7`). -/
def goodEnv : HandoffEnv :=
  { recipOk := true, knownIntroducer := true, notExpired := true, swissCell := 7 }

/-- The genuine certificate VALIDATES on the reference kernel — `Attested` is non-vacuously
TRUE, and all 6 checks pass. -/
example : validateHandoff2 instSignatureKernel goodCert goodEnv = true := by decide

/-- The reference EUF-CMA carrier HOLDS for `instSignatureKernel` (the proved unforgeability),
so the theorems are dischargeable on a real carrier, not just hypothetically. -/
theorem refUnforgeable : instSignatureKernel.unforgeable := by
  intro pk m s h; simp only [decide_eq_true_eq] at h; exact h.2

/-- A FORGED certificate the adversary fabricates: it copies `goodCert`'s authority content (so
the non-amplification leg would pass) but names an introducer key the adversary does NOT control
— `introPK := goodCert.signingMessage + 1`, which is NOT the signing message. On the reference
kernel `Signed pk m := pk = m`, this means `¬ Signed introPK signingMessage` (the adversary
cannot have signed under a key it does not hold). -/
def forgedCert : HandoffCert2 :=
  { goodCert with introPK := goodCert.signingMessage + 1 }

/-- `forgedCert`'s signing message is unchanged from `goodCert` (the message is independent of
`introPK`), so the adversary's key `m+1` is NOT the message `m`. -/
theorem forged_signingMessage : forgedCert.signingMessage = goodCert.signingMessage := rfl

/-- The adversary did NOT validly sign `forgedCert` under the named key: `¬ Signed (m+1) m`.
On the reference kernel `Signed pk m := pk = m`, so this is `¬ (m+1 = m)`, decidable. -/
theorem forged_not_signed :
    ¬ instSignatureKernel.Signed forgedCert.introPK forgedCert.signingMessage := by
  show ¬ (forgedCert.introPK = forgedCert.signingMessage)
  decide

/-- **The unforgeability theorem FIRES, non-vacuously.** The forged certificate — naming a key
the adversary does not hold — is rejected by `validateHandoff2` under the reference EUF-CMA
carrier, via `handoff_unforgeable`. This is the §1 introducer-signature check biting on a real
forgery. -/
theorem forged_handoff_rejected :
    validateHandoff2 instSignatureKernel forgedCert goodEnv = false :=
  handoff_unforgeable refUnforgeable forgedCert forged_not_signed goodEnv

/-- The genuine certificate VALIDATES (Attested TRUE) and the forged one does NOT — both witnessed
directly. Non-vacuity on both polarities. -/
example : validateHandoff2 instSignatureKernel goodCert goodEnv = true := by decide
example : validateHandoff2 instSignatureKernel forgedCert goodEnv = false := forged_handoff_rejected

/-- A federation of TWO distinct vats with an injective key map (n = 2 > 1). -/
def fed2 : Federation where
  vats   := [1, 2]
  key    := fun v => v + 100      -- injective: distinct vats ↦ distinct keys.
  keyInj := by
    intro a b _ _ h
    exact Nat.add_right_cancel h
  nodup  := by decide

example : fed2.NonTrivial := by decide

/-- The full n>1 forgery theorem fires on `fed2`: an adversary vat `2 ≠ 1` presenting a cert that
names vat `1`'s key but is not validly signed cannot make the handoff validate. We use `fed2`
and a cert whose `introPK = fed2.key 1 = 101`, unsigned under that key. -/
def fed2ForgedCert : HandoffCert2 := { goodCert with introPK := 101 }

/-- Vat `1`'s key in `fed2` did not sign `fed2ForgedCert`'s message: `¬ (101 = msg)`. -/
theorem fed2_not_signed :
    ¬ instSignatureKernel.Signed (fed2.key 1) fed2ForgedCert.signingMessage := by
  show ¬ (fed2.key 1 = fed2ForgedCert.signingMessage)
  decide

example :
    validateHandoff2 instSignatureKernel fed2ForgedCert goodEnv = false :=
  adversary_cannot_forge_at_n_gt_1 refUnforgeable fed2 (by decide)
    1 2 (by decide) (by decide) (by decide) fed2ForgedCert rfl fed2_not_signed goodEnv

end NonVacuity

/-! ## §6b — Replay tooth (CAPTP-DEEP-1): a cert nonce is consume-once, INDEPENDENTLY of the
swiss `max_uses`.

The §3 gate `validateHandoff2` was BLIND to replay: it has no notion of an already-consumed
certificate, so the same validated presentation re-validates forever (the Rust finding
`finding_handoff_nonce_replay_is_not_prevented` — a durable/unlimited swiss entry let one captured
certificate replay without bound; the `nonce` field and the `ReplayDetected` variant were
decorative). The fix in `captp/src/{sturdy,handoff}.rs` adds a target-side seen-nonce registry
(`SwissTable::handoff_nonce_seen` / `register_handoff_nonce`) and rejects a presentation whose
nonce was already consumed (`HandoffError::ReplayDetected`), consuming the nonce on the success
path. This section models that tooth and proves it CATCHES the replay the old gate missed.

`SeenNonces` is the target federation's consumed-nonce set (the `HashSet<[u8;32]>` in `SwissTable`),
modeled as a `List Nat` membership. `validateHandoff2R` is the replay-aware gate: all six §3 checks
AND the nonce not-yet-seen. `consumeNonce` mirrors `register_handoff_nonce` on the success path. -/

/-- The target's consumed handoff-nonce set (mirror of `SwissTable.seen_handoff_nonces`). -/
abbrev SeenNonces := List Nat

/-- `seenNonce seen c` — has this certificate's nonce already been consumed?
Mirrors `SwissTable::handoff_nonce_seen(&cert.nonce)`. -/
def seenNonce (seen : SeenNonces) (c : HandoffCert2) : Bool := seen.contains c.nonce

/-- `consumeNonce seen c` — register the cert's nonce as consumed (success path).
Mirrors `SwissTable::register_handoff_nonce(cert.nonce)`. -/
def consumeNonce (seen : SeenNonces) (c : HandoffCert2) : SeenNonces := c.nonce :: seen

/-- **`validateHandoff2R K c env seen`** — the REPLAY-AWARE 6+1-check gate. It runs the full §3
gate AND requires the nonce to be unconsumed. EXACT mirror of the hardened `validate_handoff`
(checks 1–6 then the §6c replay check `if swiss_table.handoff_nonce_seen(&cert.nonce) { Err }`). -/
def validateHandoff2R (K : SignatureKernel PubKey Msg Sig) (c : HandoffCert2)
    (env : HandoffEnv) (seen : SeenNonces) : Bool :=
  validateHandoff2 K c env && !seenNonce seen c

/-- **`validateHandoff2R_implies_base`** — the replay-aware gate refines §3: anything it accepts,
the base gate also accepts (the replay check is an ADDED rejection, never a new acceptance). -/
theorem validateHandoff2R_implies_base {K : SignatureKernel PubKey Msg Sig}
    {c : HandoffCert2} {env : HandoffEnv} {seen : SeenNonces}
    (h : validateHandoff2R K c env seen = true) : validateHandoff2 K c env = true := by
  simp only [validateHandoff2R, Bool.and_eq_true] at h; exact h.1

/-- **`validateHandoff2R_fresh_nonce`** — a validated replay-aware presentation had an UNCONSUMED
nonce (the §6c precondition). -/
theorem validateHandoff2R_fresh_nonce {K : SignatureKernel PubKey Msg Sig}
    {c : HandoffCert2} {env : HandoffEnv} {seen : SeenNonces}
    (h : validateHandoff2R K c env seen = true) : seenNonce seen c = false := by
  simp only [validateHandoff2R, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2

/-- **`replay_rejected` — THE TOOTH (CAPTP-DEEP-1).** Once a certificate's nonce has been
consumed (it is in `seen`), the replay-aware gate REJECTS any presentation of that certificate —
regardless of how perfect its signatures, trust, expiry, target binding, non-amplification, OR
how unlimited the swiss `max_uses`. This is precisely the property the OLD `validateHandoff2`
could not express; the replayed presentation is now `false`. -/
theorem replay_rejected {K : SignatureKernel PubKey Msg Sig}
    (c : HandoffCert2) (env : HandoffEnv) (seen : SeenNonces)
    (hseen : seenNonce seen c = true) :
    validateHandoff2R K c env seen = false := by
  simp only [validateHandoff2R, hseen, Bool.not_true, Bool.and_false]

/-- **`consume_then_replay_rejected` — the consume-once end-to-end law.** A FIRST presentation
that validates (`validateHandoff2R … seen = true`) consumes the nonce (`consumeNonce`); the
IMMEDIATE replay against the updated seen-set is then REJECTED. This is the Lean analogue of the
red-team `finding_handoff_nonce_replay_is_not_prevented` DEFENDED assertion: present-once-succeeds,
present-again-fails. -/
theorem consume_then_replay_rejected {K : SignatureKernel PubKey Msg Sig}
    (c : HandoffCert2) (env : HandoffEnv) (seen : SeenNonces)
    (hfirst : validateHandoff2R K c env seen = true) :
    validateHandoff2R K c env (consumeNonce seen c) = false := by
  -- After consuming, the nonce is seen, so `replay_rejected` fires.
  refine replay_rejected c env (consumeNonce seen c) ?_
  simp only [seenNonce, consumeNonce, List.contains_cons, beq_self_eq_true, Bool.true_or]

/-- **`fresh_nonce_still_validates` — the defense is precise (not a blanket deny).** A DISTINCT
certificate `c'` whose nonce is NOT in `seen` still validates whenever the base gate accepts it —
the replay tooth rejects only re-presented (already-consumed) nonces, never a legitimate fresh
handoff. (Lean analogue of the red-team test's "a fresh-nonce certificate for the same swiss must
still validate".) -/
theorem fresh_nonce_still_validates {K : SignatureKernel PubKey Msg Sig}
    (c' : HandoffCert2) (env : HandoffEnv) (seen : SeenNonces)
    (hbase : validateHandoff2 K c' env = true) (hfresh : seenNonce seen c' = false) :
    validateHandoff2R K c' env seen = true := by
  simp only [validateHandoff2R, hbase, hfresh, Bool.not_false, Bool.and_true]

/-! ### §6b-nv — Non-vacuity of the replay tooth on the reference carrier. -/

section ReplayNonVacuity

open Dregg2.Crypto.PortalFloor.Reference (instSignatureKernel)

/-- First presentation of `goodCert` against an EMPTY seen-set validates (replay-aware). -/
example : validateHandoff2R instSignatureKernel goodCert goodEnv [] = true := by decide

/-- The IMMEDIATE replay (after consuming `goodCert`'s nonce) is REJECTED — the tooth fires. -/
example :
    validateHandoff2R instSignatureKernel goodCert goodEnv (consumeNonce [] goodCert) = false := by
  decide

end ReplayNonVacuity

/-! ## §7 — Axiom-hygiene tripwires.

Every PROVED theorem depends ONLY on the three standard kernel axioms (whitelist
`{propext, Classical.choice, Quot.sound}`); no extra axiom. The `#guard`/`example` non-vacuity
checks are `decide`/term-mode clean (the kernel-trusted decision procedure, NOT `native_decide`);
they are demonstrations, not load-bearing theorems, and are NOT in the asserted set. -/

#assert_axioms validateHandoff2_attested
#assert_axioms validateHandoff2_nonAmplifying
#assert_axioms validateHandoff2_attenuates
#assert_axioms handoff_installs_exactly
#assert_axioms handoff_rejects_unconnected
#assert_axioms handoff_unforgeable
#assert_axioms adversary_cannot_forge_at_n_gt_1
#assert_axioms forged_handoff_installs_nothing
#assert_axioms validateHandoff2R_implies_base
#assert_axioms validateHandoff2R_fresh_nonce
#assert_axioms replay_rejected
#assert_axioms consume_then_replay_rejected
#assert_axioms fresh_nonce_still_validates

end Dregg2.Exec.CapTPHandoffSound
