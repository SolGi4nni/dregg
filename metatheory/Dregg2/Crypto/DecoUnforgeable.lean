/-
# Dregg2.Crypto.DecoUnforgeable — DECO payment-attestation UNFORGEABILITY, as a game + reduction.

This is **rung 4** for DECO: the climb from *authenticity ASSUMED* (survey gap #1,
`docs/audit/SECURITY-PROPERTY-MAP.md`) to *authenticity PROVEN-unforgeable-under-standard-assumptions*.
It is the crypto floor beneath zkOracle's `authentic` leg and beneath the deployed DECO carrier
(`Circuit/DecoBindingFromFold.lean`).

`Dregg2/Crypto/Deco.lean` proved the SOUNDNESS refinement `deco_authenticates_payment`
(`Deco.lean:315`) — accept ⟹ the payment facts genuinely hold, given the §8 carriers. This module
re-reads that as an **ideal-functionality realization** and adds the missing half the auditor asks
for: the **reduction** — a forged DECO attestation of a session that DID NOT happen YIELDS a break of
a NAMED standard floor (ed25519 EUF-CMA / HMAC / Poseidon2 CR / STARK extractability). It mirrors
`Ed25519Reduction.lean` (the game-based forgery reduction) and `LightClientUC.lean` (the
ideal-functionality + soundness-game + reduction), applied to the DECO session-authentication chain.

## The three real things (each machine-checked)

  **(1) `F_attestation` — the IDEAL FUNCTIONALITY (§1).** Modelled on `F_LC` (`LightClientUC.lean:74`):
  an ideal oracle parametrized by the ground-truth predicate `Authenticated : Statement → Prop`
  ("a genuine Stripe TLS session disclosed exactly these facts to this serverKey"). `F_attestation
  Auth stmt := Auth stmt` — it emits an attestation ONLY when `Authenticated` holds, by fiat. The
  concrete DECO ground truth `decoAuthenticated` IS `deco_authenticates_payment`'s conclusion. The
  real DECO verifier `AttReal := verify` holds no `Authenticated` oracle; that it REALIZES the ideal
  (`AttRealizes`) is `deco_attestation_realizes`.

  **(2) THE UNFORGEABILITY GAME + REDUCTION (§2, the headline, PROVED).** `AttForgery` = a verified
  attestation of a session that did NOT happen (`verify = true ∧ ¬ Authenticated`); `AttUnforgeable`
  = no forgery exists. The reduction `forgery_yields_break`: any `AttForgery`, under STARK
  extractability, produces a CONCRETE ed25519 `SigForgery` OR HMAC `MacForgery` — the standard
  cryptographic reduction shape (`Ed25519Reduction.protocol_forgery_to_sig_forgery` generalized to
  the DECO auth-chain). The binding-uniqueness leg (`deco_binding_forgery_to_collision`) reduces two
  disclosed fact-sets sharing one transcript to a Poseidon2 collision. Closing under the named
  carriers gives `deco_attestation_unforgeable`.

  **(3) BOTH-POLARITY NON-VACUITY (§4).** `attestation_fires` — a genuine reference attestation IS
  `Authenticated` and verifies. `attestation_bites` — a DECO forge-kernel over which `AttForgery`
  concretely exists and the reduction extracts a genuine ed25519 `SigForgery`; the forge kernel does
  NOT realize `F_attestation`. Strip the carrier and a concrete payment forgery appears.

## The floor (§3) — STANDARD only, NO dregg-specific parked assumption

  ed25519 EUF-CMA (`Ed25519EufCma`) · HMAC unforgeability (`MacKernelE.unforgeable`) · Poseidon2 CR
  (`Poseidon2Kernel.collisionHard`) · STARK extractability (`DecoVerifierKernel.extractable`). These
  are EXACTLY the `deco_binds_payment` trust base (`Deco.lean:213-228`). No dregg-specific hardness is
  smuggled in; the one non-cryptographic item (Web-PKI/Stripe endpoint anchor: which key is Stripe's)
  is a deployment trust carried by the registration, not a reducible open — the same terminal status
  it holds today.

`#assert_axioms`-clean (⊆ `{propext, Classical.choice, Quot.sound}`) — the sole standing obligations
are the four named carriers on the Rust `@[extern]` oracles.
-/
import Dregg2.Crypto.Deco
import Dregg2.Crypto.Ed25519Reduction

namespace Dregg2.Crypto.DecoUnforgeable

open Dregg2.Crypto.Deco
open Dregg2.Crypto.PortalFloor
open Dregg2.Crypto.Ed25519Reduction

/-! ## §1 — `F_attestation`: the ideal functionality (modelled on `F_LC`, `LightClientUC.lean:74`).

The ground-truth predicate `Authenticated : Statement → Prop` is the DECO analog of `Produced`: the
ideal functionality holds the truth of which Stripe sessions actually happened, and the
environment/adversary cannot make it lie. For DECO the ground truth is NOT abstract — it decomposes
into the §8 facts, and that decomposition (`decoAuthenticated`) IS the conclusion of
`deco_authenticates_payment` (`Deco.lean:320-328`). -/

/-- **`decoAuthenticated SK MK compress encode stmt`** — the concrete DECO ground truth: there is a
genuine session witness whose session key Stripe SIGNED (ed25519), whose transcript was MAC'd under it
(HMAC), that opens to the encoding of exactly the disclosed facts, with a non-zero amount. This is
`deco_authenticates_payment`'s conclusion, named as the ideal predicate an honest session backs. -/
def decoAuthenticated {Dg : Type}
    (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (compress : Dg → Dg → Dg) (encode : PaymentFacts → Dg)
    (stmt : Statement Dg) : Prop :=
  ∃ w : CircuitIR Dg,
    SK.Signed stmt.serverKey w.sessionKey ∧
    MK.Tagged w.sessionKey w.transcriptCommit w.tag ∧
    w.transcriptCommit = compress (encode stmt.facts) w.salt ∧
    1 ≤ stmt.facts.amountCents

/-- **`F_attestation Auth stmt` — the IDEAL attestation functionality.** It emits an attestation for
`stmt` iff a genuine Stripe session backs it (`Auth stmt`). This is the functionality the deployed
DECO verifier must REALIZE — a UC-secure attestation oracle behaves indistinguishably from one that
simply consults the ground truth `Auth`. (Cf. `F_LC Produced s := Produced s`, `LightClientUC.lean:74`.) -/
def F_attestation {Dg : Type} (Auth : Statement Dg → Prop) (stmt : Statement Dg) : Prop := Auth stmt

/-- **`AttReal verify stmt proof` — the REAL DECO verifier.** Holding no `Auth` oracle, it accepts
`stmt` iff the attached `proof` makes the deployed §8 `verify` (the `DecoVerifierKernel.verify` STARK
check, `Deco.lean:282`) return `true`. One verifier call, no ground-truth consult. (Cf. `LCReal`,
`LightClientUC.lean:79`.) -/
def AttReal {Dg Proof : Type} (verify : Statement Dg → Proof → Bool)
    (stmt : Statement Dg) (proof : Proof) : Bool := verify stmt proof

/-- **`AttRealizes verify Auth` — the deployed verifier realizes `F_attestation`.** Whenever the real
verifier accepts `(stmt, proof)`, the ideal functionality also emits (`Auth stmt`) — the deployed
verifier is indistinguishable from `F_attestation`. (Cf. `Unfoolable`, `LightClientUC.lean:105`.) -/
def AttRealizes {Dg Proof : Type} (verify : Statement Dg → Proof → Bool)
    (Auth : Statement Dg → Prop) : Prop :=
  ∀ (stmt : Statement Dg) (proof : Proof), verify stmt proof = true → Auth stmt

/-! ## §2 — The UNFORGEABILITY game and the reduction.

`AttForgery` mirrors `Ed25519Reduction.SigForgery` (`Ed25519Reduction.lean:62`) /
`LightClientUC.Foolable` (`LightClientUC.lean:97`): a verified attestation of a session that did NOT
happen. `AttUnforgeable` = no such forgery, the negation of the win condition. -/

/-- **`AttForgery verify Auth stmt proof`** — the attestation forger's WIN: the deployed verifier
ACCEPTS `(stmt, proof)` yet no genuine session backs `stmt` (`¬ Auth stmt`) — a verified attestation
of a payment/session that did not happen. -/
def AttForgery {Dg Proof : Type} (verify : Statement Dg → Proof → Bool)
    (Auth : Statement Dg → Prop) (stmt : Statement Dg) (proof : Proof) : Prop :=
  verify stmt proof = true ∧ ¬ Auth stmt

/-- **`AttUnforgeable verify Auth`** — no environment forges: whenever the verifier accepts, the ideal
functionality would emit. Stated as the negation of the forger's win. -/
def AttUnforgeable {Dg Proof : Type} (verify : Statement Dg → Proof → Bool)
    (Auth : Statement Dg → Prop) : Prop :=
  ∀ (stmt : Statement Dg) (proof : Proof), ¬ AttForgery verify Auth stmt proof

/-- `AttUnforgeable` is exactly `AttRealizes` — the game and the realization are two faces of one
proposition (no slack). The exact `unfoolable_iff_not_foolable` equivalence (`LightClientUC.lean:111`),
reproved for DECO. -/
theorem attUnforgeable_iff_attRealizes {Dg Proof : Type}
    (verify : Statement Dg → Proof → Bool) (Auth : Statement Dg → Prop) :
    AttUnforgeable verify Auth ↔ AttRealizes verify Auth := by
  constructor
  · intro hU stmt proof hacc
    by_contra hn
    exact hU stmt proof ⟨hacc, hn⟩
  · intro hR stmt proof hforge
    exact hforge.2 (hR stmt proof hforge.1)

/-! ### §2a — The HMAC forgery predicate (the `SigForgery` analog for the MAC gate).

`Ed25519Reduction` names the ed25519 forgery `SigForgery`; the DECO auth-chain's gate 2 is an HMAC
gate, so we name its forgery `MacForgery` — the same "oracle accepts a tag the holder never MAC'd"
shape, and `MacEufCma` = "no such forgery". This is the `MacKernelE` analog of `Ed25519EufCma`
(`Ed25519Reduction.lean:70`), mechanical. -/

/-- **`MacForgery MK key msg t`** — the HMAC forger's WIN: the §8 MAC oracle accepts `(key, msg, t)`
yet the holder never MAC'd `msg` under `key` (`¬ MK.Tagged`). -/
def MacForgery {Key Msg Tag : Type} (MK : MacKernelE Key Msg Tag)
    (key : Key) (msg : Msg) (t : Tag) : Prop :=
  MK.verifyTag key msg t = true ∧ ¬ MK.Tagged key msg t

/-- **`MacEufCma MK`** — HMAC unforgeability as the negation of the forger's win: no `(key, msg, t)`
is a forgery. -/
def MacEufCma {Key Msg Tag : Type} (MK : MacKernelE Key Msg Tag) : Prop :=
  ∀ (key : Key) (msg : Msg) (t : Tag), ¬ MacForgery MK key msg t

/-- From the §8 `unforgeable` carrier, `MacEufCma` holds (the game form of `verifyTag_sound`). The
HMAC analog of `Ed25519Reduction.eufCma_of_unforgeable` (`Ed25519Reduction.lean:93`). -/
theorem macEufCma_of_unforgeable {Key Msg Tag : Type} (MK : MacKernelE Key Msg Tag)
    (hunf : MK.unforgeable) : MacEufCma MK := by
  intro key msg t hforge
  exact hforge.2 (MK.verifyTag_sound hunf key msg t hforge.1)

/-! ### §2b — `deco_attestation_realizes`: the deployed verifier realizes `F_attestation`.

This is `deco_authenticates_payment` re-read as an ideal-functionality realization: the correctness
leg ALREADY exists; what is new is naming it `AttRealizes` at the concrete DECO ground truth. -/

/-- **`deco_attestation_realizes`** — the deployed DECO verifier REALIZES `F_attestation`: given the
kernel's gate oracles ARE the §8 ed25519/HMAC oracles and the §8 carriers, an accepting DECO proof
means a genuine Stripe session backs the statement (`decoAuthenticated`). The `AttRealizes` re-read of
`deco_authenticates_payment` (`Deco.lean:315`). -/
theorem deco_attestation_realizes {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable) :
    AttRealizes KD.verify (decoAuthenticated SK MK KD.compress KD.encode) := by
  intro stmt proof haccept
  obtain ⟨w, h1, h2, h3, h4⟩ :=
    deco_authenticates_payment (KD := KD) (SK := SK) (MK := MK)
      hsigEq hmacEq hext hsig hmac stmt proof haccept
  exact ⟨w, h1, h2, h3, h4⟩

/-! ### §2c — THE REDUCTION (the new content): a forgery YIELDS a floor break.

`deco_verify_sound` (`Deco.lean:296`) is the soundness half (accept ⟹ `∃ w, DecoRelation`). The
missing half — the extractor/reduction — turns `DecoRelation ∧ ¬ decoAuthenticated` into a CONCRETE
break of a named floor. The auth-chain gates make this a clean case split: the extracted witness
satisfies the opening/amount conjuncts DEFINITIONALLY (gates 3/4/5), so a forgery must break the
signature gate (⟹ `SigForgery`) or the MAC gate (⟹ `MacForgery`). This is
`Ed25519Reduction.protocol_forgery_to_sig_forgery` (`Ed25519Reduction.lean:239`) generalized from one
primitive to the DECO chain's two authentication gates. -/

/-- **`forgery_yields_break` (THE REDUCTION).** Under STARK extractability, any `AttForgery` against
the DECO ground truth produces a CONCRETE ed25519 `SigForgery` OR HMAC `MacForgery`. The forward
direction of soundness (`deco_verify_sound`) extracts a satisfying witness; case-splitting on the two
carrier facts (`Signed`, `Tagged`) — the only conjuncts of `decoAuthenticated` not forced by the
runnable gates — yields the concrete floor break. -/
theorem forgery_yields_break {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (stmt : Statement Dg) (proof : Proof)
    (hforge : AttForgery KD.verify (decoAuthenticated SK MK KD.compress KD.encode) stmt proof) :
    (∃ pk m s, SigForgery SK pk m s) ∨ (∃ key msg t, MacForgery MK key msg t) := by
  obtain ⟨haccept, hnAuth⟩ := hforge
  obtain ⟨w, hrel⟩ := deco_verify_sound hext stmt proof haccept
  rw [hsigEq, hmacEq] at hrel
  obtain ⟨hsigOk, hmacOk, hopen, henc, hamt⟩ := hrel
  by_cases hSigned : SK.Signed stmt.serverKey w.sessionKey
  · by_cases hTagged : MK.Tagged w.sessionKey w.transcriptCommit w.tag
    · -- both carrier facts hold ⇒ w witnesses decoAuthenticated ⇒ contradicts ¬ Auth.
      exact absurd ⟨w, hSigned, hTagged, by rw [hopen, henc], hamt⟩ hnAuth
    · -- the MAC gate accepts a tag never MAC'd ⇒ a concrete HMAC forgery.
      exact Or.inr ⟨w.sessionKey, w.transcriptCommit, w.tag, hmacOk, hTagged⟩
  · -- Stripe's key "signed" a session key it never signed ⇒ a concrete ed25519 forgery.
    exact Or.inl ⟨stmt.serverKey, w.sessionKey, w.sig, hsigOk, hSigned⟩

/-- **`deco_attestation_unforgeable` (THE HEADLINE).** Under ed25519 EUF-CMA, HMAC unforgeability, and
STARK extractability, NO forger produces an accepting DECO attestation of a session that did not
happen. Closes gap #1: DECO authenticity is *proven-unforgeable-under-standard-assumptions*. Derived
from the reduction — a forgery would break one of the named carriers. -/
theorem deco_attestation_unforgeable {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : Ed25519EufCma SK) (hmac : MacEufCma MK) :
    AttUnforgeable KD.verify (decoAuthenticated SK MK KD.compress KD.encode) := by
  intro stmt proof hforge
  rcases forgery_yields_break SK MK hsigEq hmacEq hext stmt proof hforge with
    ⟨pk, m, s, hf⟩ | ⟨key, msg, t, hf⟩
  · exact hsig pk m s hf
  · exact hmac key msg t hf

/-- **`deco_attestation_unforgeable_of_carriers`** — the same headline stated over the §8 `unforgeable`
carriers directly (the shape a deployment holds), via the game↔carrier bridges. So a consumer holding
`SK.unforgeable`/`MK.unforgeable` gets `AttUnforgeable` with no game-form plumbing. -/
theorem deco_attestation_unforgeable_of_carriers {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable) :
    AttUnforgeable KD.verify (decoAuthenticated SK MK KD.compress KD.encode) :=
  deco_attestation_unforgeable SK MK hsigEq hmacEq hext
    (eufCma_of_unforgeable SK hsig) (macEufCma_of_unforgeable MK hmac)

/-! ### §2d — The binding-uniqueness leg: the Poseidon2 CR floor member.

The reduction above covers the ed25519/HMAC/STARK floors of the EXISTENCE forgery. The fourth
standard DECO floor — Poseidon2 collision-resistance — is the BINDING leg: it forbids two disclosed
fact-sets sharing one transcript commitment (the `deco_commitment_binds` contrapositive,
`Deco.lean:249`). A binding forgery (distinct openings of one commitment) IS a Poseidon2 collision. -/

/-- **`Poseidon2Collision PK a b a' b'`** — the CR adversary's WIN: `compress a b = compress a' b'`
with distinct inputs. `PK.collisionHard` is exactly "no such collision" (`Poseidon2Kernel`,
`PortalFloor.lean:149`). -/
def Poseidon2Collision {Dg : Type} (PK : Poseidon2Kernel Dg) (a b a' b' : Dg) : Prop :=
  PK.compress a b = PK.compress a' b' ∧ (a ≠ a' ∨ b ≠ b')

/-- **`deco_binding_forgery_to_collision` (the CR reduction).** Two DECO openings `(fd, salt)` and
`(fd', salt')` of the SAME transcript commitment `c` that differ in some component ARE a Poseidon2
collision. So a binding forgery (a transcript opening to two distinct disclosed-field digests) breaks
Poseidon2 CR. -/
theorem deco_binding_forgery_to_collision {Dg : Type} (PK : Poseidon2Kernel Dg)
    (fd fd' salt salt' c : Dg)
    (ho : c = PK.compress fd salt) (ho' : c = PK.compress fd' salt')
    (hne : fd ≠ fd' ∨ salt ≠ salt') :
    Poseidon2Collision PK fd salt fd' salt' :=
  ⟨by rw [← ho, ← ho'], hne⟩

/-- **`deco_binding_unforgeable` (the CR contrapositive).** Under Poseidon2 collision-resistance, NO
binding forgery exists: two openings of one transcript commitment agree on BOTH the field digest and
the salt — the disclosed facts are the transcript's UNIQUE content. Reuses `deco_commitment_binds`
(`Deco.lean:249`). -/
theorem deco_binding_unforgeable {Dg : Type} [PK : Poseidon2Kernel Dg]
    (hcr : PK.collisionHard) (fd fd' salt salt' c : Dg)
    (ho : c = PK.compress fd salt) (ho' : c = PK.compress fd' salt') :
    fd = fd' ∧ salt = salt' :=
  deco_commitment_binds hcr fd fd' salt salt' c ho ho'

/-! ## §3 — The floor, named. Each is STANDARD and is EXACTLY the `deco_binds_payment` trust base.

| carrier | shape | role |
|---|---|---|
| ed25519 EUF-CMA | `Ed25519EufCma SK` | gate-1 forgery target (`SigForgery`) |
| HMAC unforgeability | `MacEufCma MK` / `MK.unforgeable` | gate-2 forgery target (`MacForgery`) |
| Poseidon2 CR | `PK.collisionHard` | binding-uniqueness (`Poseidon2Collision`) |
| STARK extractability | `KD.extractable` | accept ⟹ satisfying trace |

`Web-PKI honest-endpoint` (which key is Stripe's; `encode`-is-the-schema) is a DEPLOYMENT trust anchor
carried by the registration, NOT a cryptographic hardness — the same terminal status it holds today.
**No dregg-specific parked assumption:** the reduction closes to these four standard floors and no
other. -/

/-! ## §4 — NON-VACUITY (both poles): a real attestation FIRES; a forged one BITES.

Reuses `Deco.Reference` (`Deco.lean:457`). (a) the genuine reference attestation IS `Authenticated`
and verifies; (b) a DECO forge-kernel admits a CONCRETE `AttForgery` whose reduction extracts a
genuine ed25519 `SigForgery` and which does NOT realize `F_attestation`. Not a `P → P`: strip the
carrier and a payment forgery concretely appears. -/

/-- **(FIRES)** a real authenticated payment attestation exists AND verifies: at the reference kernels,
the sample statement is genuinely `decoAuthenticated` (F_attestation would emit it) and the deployed
verifier accepts it. Reuses `reference_authenticates_payment` (`Deco.lean:532`). -/
theorem attestation_fires :
    decoAuthenticated Reference.refSigKernel Reference.refMacKernel
        Reference.refKernel.compress Reference.refKernel.encode Reference.sampleStmt
    ∧ Reference.refKernel.verify Reference.sampleStmt () = true :=
  ⟨Reference.reference_authenticates_payment, by decide⟩

/-- And it realizes `F_attestation` as an ideal emission: the ground truth emits on the sample. -/
theorem attestation_fires_emits :
    F_attestation
      (decoAuthenticated Reference.refSigKernel Reference.refMacKernel
        Reference.refKernel.compress Reference.refKernel.encode)
      Reference.sampleStmt :=
  Reference.reference_authenticates_payment

/-! ### §4b — the DECO forge kernel (the biting pole). -/

namespace Forge

open Dregg2.Crypto.Deco.Reference (refMac refCompress refEncode refMacKernel sampleStmt)

/-- A forgeable ed25519 sig oracle: accepts EVERY signature (the accept-everything §8 oracle). -/
def forgeSig : Int → Int → Int → Bool := fun _ _ _ => true

/-- A forgeable ed25519 `SignatureKernel`: `Signed` NEVER holds, yet the oracle accepts everything.
The `unforgeable` carrier is provably FALSE over it. Mirrors `PortalFloor.instSignatureForge`. -/
@[reducible] def forgeSigKernel : SignatureKernel Int Int Int where
  Signed _ _ := False
  sigVerify := forgeSig
  unforgeable := ∀ pk m s, forgeSig pk m s = true → (False : Prop)
  sigVerify_sound := fun h => h

/-- A DECO verifier whose sig gate is the FORGEABLE oracle (mac gate = the accept-all reference).
`verify` accepts any non-zero payment; `extract` rebuilds a satisfying trace (the gates are runnable
and pass). So the STARK accepts and extraction succeeds — but the LIFT to `Signed` fails: a forgery. -/
@[reducible] def forgeDeco : DecoVerifierKernel Int Unit where
  sigVerify := forgeSig
  macVerify := refMac
  compress := refCompress
  encode := refEncode
  verify stmt _ := decide (1 ≤ stmt.facts.amountCents)
  extractable := True
  extract := by
    intro _ stmt _ haccept
    have hamt : 1 ≤ stmt.facts.amountCents := of_decide_eq_true haccept
    refine deco_complete forgeSig refMac refCompress refEncode stmt
      { sessionKey := 0, sig := 0, transcriptCommit := refEncode stmt.facts + 7, tag := 0,
        fieldsDigest := refEncode stmt.facts, salt := 7, amtBits := [] } ?_
    exact ⟨rfl, rfl, rfl, rfl, hamt⟩

/-- **(BITES, the forgery exists)** a CONCRETE `AttForgery` on the forge kernel: the sample statement
verifies, yet no genuine session backs it (`decoAuthenticated` is FALSE — `Signed` never holds). -/
theorem forge_attestation_forgery :
    AttForgery forgeDeco.verify
      (decoAuthenticated forgeSigKernel refMacKernel forgeDeco.compress forgeDeco.encode)
      sampleStmt () := by
  refine ⟨by decide, ?_⟩
  rintro ⟨_, hSigned, _, _, _⟩
  exact hSigned

/-- **(BITES, the reduction fires)** the reduction extracts a concrete floor break from the forgery:
an ed25519 `SigForgery` OR an HMAC `MacForgery`. -/
theorem attestation_bites :
    (∃ pk m s, SigForgery forgeSigKernel pk m s) ∨
      (∃ key msg t, MacForgery refMacKernel key msg t) :=
  forgery_yields_break (KD := forgeDeco) forgeSigKernel refMacKernel rfl rfl trivial sampleStmt ()
    forge_attestation_forgery

/-- The bite is SHARP: it is a genuine ed25519 `SigForgery` (the accept-all reference MAC cannot be
forged — its `Tagged` is `True` — so the disjunction resolves to the signature break). Strip the
signature carrier and a concrete payment forgery appears. -/
theorem attestation_bites_is_sig_forgery :
    ∃ pk m s, SigForgery forgeSigKernel pk m s := by
  rcases attestation_bites with h | ⟨_, _, _, _, hnt⟩
  · exact h
  · exact absurd trivial hnt

/-- **(BITES, the ideal is not realized)** the forge kernel does NOT realize `F_attestation`: it
accepts the sample yet the ground truth would reject it. So `AttRealizes` is a real proposition the
sound floor earns and a forgeable oracle loses. -/
theorem forge_not_realizes :
    ¬ AttRealizes forgeDeco.verify
        (decoAuthenticated forgeSigKernel refMacKernel forgeDeco.compress forgeDeco.encode) := by
  intro hR
  exact forge_attestation_forgery.2 (hR sampleStmt () forge_attestation_forgery.1)

end Forge

/-! ## §5 — Axiom hygiene. The realization, the reduction, and both non-vacuity poles rest only on
`{propext, Classical.choice, Quot.sound}` plus their explicit named floor-carrier hypotheses. -/

#assert_axioms attUnforgeable_iff_attRealizes
#assert_axioms macEufCma_of_unforgeable
#assert_axioms deco_attestation_realizes
#assert_axioms forgery_yields_break
#assert_axioms deco_attestation_unforgeable
#assert_axioms deco_attestation_unforgeable_of_carriers
#assert_axioms deco_binding_forgery_to_collision
#assert_axioms deco_binding_unforgeable
#assert_axioms attestation_fires
#assert_axioms attestation_fires_emits
#assert_axioms Forge.forge_attestation_forgery
#assert_axioms Forge.attestation_bites
#assert_axioms Forge.attestation_bites_is_sig_forgery
#assert_axioms Forge.forge_not_realizes

end Dregg2.Crypto.DecoUnforgeable
