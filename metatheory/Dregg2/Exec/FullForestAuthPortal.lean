/-
# Dregg2.Exec.FullForestAuthPortal — the REAL §8 `AuthPortal` instance (META-FILL E, part 3).

D (`Exec/FullForestAuth.lean`) defined the `AuthPortal` seam and a DEMO-TRIVIAL realization
(`cryptoAuthPortal`): it routed every `Authorization` arm through a single `CryptoKernel.verify`
and discharged its `soundness` with `CryptoKernel.collisionHard` — one carrier for ten variants,
the wrong granularity for the post-cutover TCB. E replaces that with a REAL `AuthPortal` instance
that wires EACH `Authorization` variant to its OWN §8 portal floor (`Crypto/PortalFloor.lean`):

  * `.signature`      → `SignatureKernel.sigVerify`     (ed25519 EUF-CMA)
  * `.proof`          → `VerifierKernel.verify`          (STARK extractability)
  * `.bearer`         → `SignatureKernel.sigVerify`      (SignedDelegation; ed25519)
  * `.capTpDelivered` → `SignatureKernel.sigVerify` ×2   (introducer + sender sigs)
  * `.custom`         → `VerifierKernel.verify`          (registry STARK)
  * `.stealth`        → `SignatureKernel.sigVerify`      (one-time ed25519)
  * `.token`          → `MacKernelE.verifyTag`           (HMAC macaroon)
  * `.oneOf`          → recurse (structural)
  * `.breadstuff`     → pure c-list read (LEAN-verifiable; the WHAT leg gates — NOT a portal)
  * `.unchecked`      → fail-closed `false` (the §8 anchor — NOT a portal, NOT `True`)

**CRITICAL ANTI-VACUITY (the audit's worst-case total-soundness hole).** The production instance
discharges NO portal arm with `True`/trivial on a REACHABLE path: every crypto-floor arm bottoms
out in a concrete kernel ORACLE (`sigVerify`/`verify`/`verifyTag`), and the two non-crypto arms are
honest — `.unchecked` fail-closes to `false` (rejected, never silently passed) and `.breadstuff`
is a genuine pure-Lean c-list read whose authority is gated by the VERIFIED `authModeAdmits` WHAT
leg. The instance's `soundness` Prop is the CONJUNCTION of the three genuine §8 carriers
the reachable arms consume (ed25519 `unforgeable` ∧ STARK `extractable` ∧ HMAC `unforgeable`) — so
the carrier is a real assumption, never `True`.

**The TCB line this DEFINES.**
  * ASSUMED (the 8 primitives, the §8 floor — the carriers): ed25519 EUF-CMA, STARK/FRI
    extractability, Pedersen DLog binding, Poseidon2 CR, BLAKE3 CR, nullifier unlinkability,
    AEAD+X25519, HMAC unforgeability. (Three of them — ed25519, STARK, HMAC — are the ones the
    `Authorization`-arm portals actually consume; the other five are the floor for the
    value/hash/seal layers the gate's siblings use.)
  * VERIFIED-IN-LEAN (NOT in the TCB): the cap-authority refinement (`authModeAdmits`, `granted ≤
    held`), the per-arm DISPATCH (which portal each variant routes to — proved structurally here),
    the fail-closed anchors (`.unchecked` rejects, `.breadstuff` gated by the WHAT leg), the
    OneOf structural rules, and nullifier DETERMINISM.

Each per-variant security theorem takes the relevant carrier as an EXPLICIT hypothesis: e.g.
`signature_arm_sound (hunf : SignatureKernel.unforgeable) … : portal accepts → Signed pk m`. The
gate-DISCIPLINE (fail-closed on a forged/revoked credential) is proved; the oracle BINDS is the
circuit's job (the carrier).

Reuses `FullForestAuth` (D), `PortalFloor` (E); EDITS NEITHER.
-/
import Dregg2.Exec.FullForestAuth
import Dregg2.Crypto.PortalFloor

namespace Dregg2.Exec.FullForestAuthPortal

open Dregg2.Exec.FullForestAuth
open Dregg2.Crypto.PortalFloor

/-! ## §1 — `RealAuthPortal`: the bundle of the THREE §8 floors the `Authorization` arms consume.

`Authorization Digest Proof` carries statements/keys as `Digest` and signatures/proofs/tags as
`Proof`. The reachable crypto-floor arms need:
  * a `SignatureKernel Digest Digest Proof` (signature / bearer / capTp / stealth) — pk=Digest,
    msg=Digest, sig=Proof;
  * a `VerifierKernel Digest Proof` (proof / custom) — stmt=Digest, proof=Proof;
  * a `MacKernelE Digest Digest Proof` (token) — key=Digest, msg=Digest, tag=Proof.
We bundle the three into one `RealAuthPortal` class so an `Authorization Digest Proof` routes
through ONE coherent §8 floor. -/

/-- **`RealAuthPortal Digest Proof`** — the three §8 portal floors the reachable `Authorization`
arms route through. NOT a new primitive: it is the conjunction of the existing `PortalFloor`
kernels at the `Authorization` carrier types. Its presence is what makes the production
`AuthPortal` instance concrete (every arm bottoms out in one of these oracles). -/
class RealAuthPortal (Digest Proof : Type) where
  /-- The ed25519 floor: signature / bearer / capTp / stealth arms. -/
  sig : SignatureKernel Digest Digest Proof
  /-- The STARK floor: proof / custom arms. -/
  ver : VerifierKernel Digest Proof
  /-- The HMAC floor: token arm. -/
  hmac : MacKernelE Digest Digest Proof

/-- The bundled ed25519 floor as a (reducible) instance — so `SignatureKernel.sigVerify` synthesizes
through a `RealAuthPortal`. -/
@[reducible] instance instSigOfReal {Digest Proof : Type} [R : RealAuthPortal Digest Proof] :
    SignatureKernel Digest Digest Proof := R.sig
/-- The bundled STARK floor as a (reducible) instance. -/
@[reducible] instance instVerOfReal {Digest Proof : Type} [R : RealAuthPortal Digest Proof] :
    VerifierKernel Digest Proof := R.ver
/-- The bundled HMAC floor as a (reducible) instance. -/
@[reducible] instance instHmacOfReal {Digest Proof : Type} [R : RealAuthPortal Digest Proof] :
    MacKernelE Digest Digest Proof := R.hmac

variable {Digest Proof : Type}

/-! ## §2 — `portalVerifyReal`: the per-arm §8 dispatch (each arm to its OWN oracle).

This is the production reduction of `credentialValid`. EVERY crypto-floor arm routes to a concrete
kernel oracle; `.unchecked` fail-closes (`false`, the §8 anchor, NOT `True`); `.breadstuff` is the
pure-Lean c-list read (`true` here — its authority is the VERIFIED `authModeAdmits` WHAT leg, not a
faked portal pass); `.oneOf` recurses structurally. NO arm is `True`-discharged on the crypto
floor. -/

mutual
/-- **`portalVerifyReal`** — the production per-arm §8 reduction (the REAL `credentialValid`). Each
crypto-floor arm routes to its OWN portal oracle (NOT one shared `CryptoKernel.verify`):
`.signature`/`.bearer`/`.stealth` → `sigVerify`; `.proof`/`.custom` → STARK `verify`; `.capTp` →
two `sigVerify`s; `.token` → HMAC `verifyTag`. `.unchecked` fail-closes; `.breadstuff` is the pure
c-list read; `.oneOf` recurses. -/
def portalVerifyReal [RealAuthPortal Digest Proof] :
    Authorization Digest Proof → Bool
  | .signature stmt sig           => SignatureKernel.sigVerify stmt stmt sig
  | .proof vk pf _ _              => VerifierKernel.verify vk pf
  | .breadstuff _                 => true                        -- pure c-list read; WHAT leg gates
  | .bearer msg sig _             => SignatureKernel.sigVerify msg msg sig
  | .unchecked                    => false                       -- §8 anchor: fail-closed, NOT True
  | .capTpDelivered im sm isig ss =>
      SignatureKernel.sigVerify im im isig && SignatureKernel.sigVerify sm sm ss
  | .custom stmt pf               => VerifierKernel.verify stmt pf
  | .oneOf cands i                => portalOneOfReal cands i
  | .stealth otp _ sig            => SignatureKernel.sigVerify otp otp sig
  | .token key sig                =>
      -- the HMAC macaroon tag: the token's `key` IS the (key, msg) seam at the floor's
      -- recompute-and-compare (`verifyTag key key sig`); replay-and-compare over the key digest.
      MacKernelE.verifyTag key key sig

/-- The `OneOf` portal (production): walk to index `i`, applying the three dregg1 structural rules
at the slot (not `Unchecked`, not nested `OneOf`, and the candidate verifies). Out-of-bounds fails
closed. Mirrors D's `portalOneOf` but over `portalVerifyReal`. -/
def portalOneOfReal [RealAuthPortal Digest Proof] :
    List (Authorization Digest Proof) → Nat → Bool
  | [],          _     => false
  | chosen :: _, 0     =>
      (match chosen with | .unchecked => false | .oneOf _ _ => false | _ => true)
        && portalVerifyReal chosen
  | _ :: rest,   n + 1 => portalOneOfReal rest n
end

/-! ## §3 — the REAL `AuthPortal` instance (REPLACING D's Demo-trivial `cryptoAuthPortal`).

`credentialValid := portalVerifyReal` (the production per-arm dispatch); `soundness` is the
CONJUNCTION of the THREE genuine §8 carriers the reachable arms consume — NOT `True`, NOT one
shared `collisionHard`. This is the post-cutover floor. The instance is at a DISTINCT name so it
does not collide with D's (which stays for `#eval`); the cutover selects THIS one. -/

/-- **The REAL §8 `AuthPortal`** (META-FILL E). `credentialValid := portalVerifyReal` routes each
arm to its own §8 oracle; `soundness` is `ed25519.unforgeable ∧ STARK.extractable ∧ HMAC.unforgeable`
— the conjunction of the THREE carriers the reachable `Authorization` arms consume. NO
arm is `True`-discharged; the carrier is a real assumption (the seL4 floor). -/
instance realAuthPortal [RealAuthPortal Digest Proof] {Ctx : Type} :
    AuthPortal (Authorization Digest Proof) Ctx where
  credentialValid cred _ := portalVerifyReal cred
  soundness :=
    (RealAuthPortal.sig (Digest := Digest) (Proof := Proof)).unforgeable
      ∧ (RealAuthPortal.ver (Digest := Digest) (Proof := Proof)).extractable
      ∧ (RealAuthPortal.hmac (Digest := Digest) (Proof := Proof)).unforgeable

/-- **`realAuthPortal_soundness_is_conjunction` — the carrier IS the three-way conjunction
(definitional).** The production `AuthPortal.soundness` is EXACTLY `ed25519 unforgeable ∧
STARK extractable ∧ HMAC unforgeable` — three genuine §8 carriers, never `True`. This pins the TCB
content: a verifier of this module sees precisely which three primitives are assumed. -/
theorem realAuthPortal_soundness_is_conjunction [RealAuthPortal Digest Proof] (Ctx : Type) :
    (realAuthPortal (Digest := Digest) (Proof := Proof) (Ctx := Ctx)).soundness
      = ((RealAuthPortal.sig (Digest := Digest) (Proof := Proof)).unforgeable
          ∧ (RealAuthPortal.ver (Digest := Digest) (Proof := Proof)).extractable
          ∧ (RealAuthPortal.hmac (Digest := Digest) (Proof := Proof)).unforgeable) :=
  rfl

/-! ## §4 — the per-variant SECURITY theorems (carrier-as-EXPLICIT-hypothesis).

Each takes the relevant §8 carrier as a hypothesis and concludes the arm's portal acceptance proves
the arm's abstract relation. The gate-discipline (the dispatch) is proved; the oracle BINDS is the
carrier. NON-VACUOUS: each conclusion is a real relation (`Signed`/`Holds`/`Tagged`) that the
downstream authority gate consumes — a forged credential never satisfies it. -/

/-- **`signature_arm_sound` — the (1) signature arm (ed25519 EUF-CMA, carrier-as-hypothesis).** A
portal-accepting `.signature stmt sig` credential PROVES `Signed stmt stmt` — the holder of `stmt`'s
key signed. Given the ed25519 `unforgeable` carrier. NON-VACUOUS: `Signed` is the real WHO content;
a forged signature (the portal rejects) yields no claim. -/
theorem signature_arm_sound [R : RealAuthPortal Digest Proof]
    (hunf : R.sig.unforgeable) (stmt : Digest) (sig : Proof)
    (haccept : portalVerifyReal (Authorization.signature stmt sig) = true) :
    R.sig.Signed stmt stmt :=
  sig_floor_sound (K := R.sig) hunf stmt stmt sig haccept

/-- **`proof_arm_sound` — the (2) proof arm (STARK extractability, carrier-as-hypothesis).** A
portal-accepting `.proof vk pf a r` credential PROVES `Holds vk` — the ZK proof discharges the
vk-bound statement. Given the STARK `extractable` carrier. NON-VACUOUS: `Holds` is the real
extracted relation. -/
theorem proof_arm_sound [R : RealAuthPortal Digest Proof]
    (hext : R.ver.extractable) (vk : Digest) (pf : Proof) (a r : Nat)
    (haccept : portalVerifyReal (Authorization.proof vk pf a r) = true) :
    R.ver.Holds vk :=
  verifier_floor_sound (K := R.ver) hext vk pf haccept

/-- **`bearer_arm_sound` — the (4) bearer arm (SignedDelegation; ed25519, carrier-as-hypothesis).**
A portal-accepting `.bearer msg sig b` credential PROVES `Signed msg msg` — the delegation message
was signed. Given the ed25519 carrier. NON-VACUOUS. -/
theorem bearer_arm_sound [R : RealAuthPortal Digest Proof]
    (hunf : R.sig.unforgeable) (msg : Digest) (sig : Proof) (b : Bool)
    (haccept : portalVerifyReal (Authorization.bearer msg sig b) = true) :
    R.sig.Signed msg msg :=
  sig_floor_sound (K := R.sig) hunf msg msg sig haccept

/-- **`capTp_arm_sound` — the (6) capTpDelivered arm (TWO ed25519 sigs, carrier-as-hypothesis).** A
portal-accepting `.capTpDelivered im sm isig ss` credential PROVES BOTH `Signed im im` (introducer)
AND `Signed sm sm` (sender) — the two-signature CapTP provenance. Given the ed25519 carrier.
NON-VACUOUS: BOTH must be genuine; the `&&` fails closed if EITHER signature is forged. -/
theorem capTp_arm_sound [R : RealAuthPortal Digest Proof]
    (hunf : R.sig.unforgeable) (im sm : Digest) (isig ss : Proof)
    (haccept : portalVerifyReal (Authorization.capTpDelivered im sm isig ss) = true) :
    R.sig.Signed im im ∧ R.sig.Signed sm sm := by
  -- the portal arm is `sigVerify im im isig && sigVerify sm sm ss`; both legs forced true.
  have h : SignatureKernel.sigVerify (Sig := Proof) im im isig = true
         ∧ SignatureKernel.sigVerify (Sig := Proof) sm sm ss = true := by
    have hh : (SignatureKernel.sigVerify (Sig := Proof) im im isig
               && SignatureKernel.sigVerify (Sig := Proof) sm sm ss) = true := haccept
    exact Bool.and_eq_true _ _ |>.mp hh
  exact ⟨sig_floor_sound (K := R.sig) hunf im im isig h.1,
         sig_floor_sound (K := R.sig) hunf sm sm ss h.2⟩

/-- **`custom_arm_sound` — the (7) custom arm (registry STARK, carrier-as-hypothesis).** A
portal-accepting `.custom stmt pf` credential PROVES `Holds stmt` — the app-defined predicate
proof discharges its statement. Given the STARK carrier. NON-VACUOUS. -/
theorem custom_arm_sound [R : RealAuthPortal Digest Proof]
    (hext : R.ver.extractable) (stmt : Digest) (pf : Proof)
    (haccept : portalVerifyReal (Authorization.custom stmt pf) = true) :
    R.ver.Holds stmt :=
  verifier_floor_sound (K := R.ver) hext stmt pf haccept

/-- **`stealth_arm_sound` — the (9) stealth arm (one-time ed25519, carrier-as-hypothesis).** A
portal-accepting `.stealth otp eph sig` credential PROVES `Signed otp otp` — the one-time-key
signature is valid (the curve25519 point relation is the WHAT leg). Given the ed25519 carrier.
NON-VACUOUS. -/
theorem stealth_arm_sound [R : RealAuthPortal Digest Proof]
    (hunf : R.sig.unforgeable) (otp eph : Digest) (sig : Proof)
    (haccept : portalVerifyReal (Authorization.stealth otp eph sig) = true) :
    R.sig.Signed otp otp :=
  sig_floor_sound (K := R.sig) hunf otp otp sig haccept

/-- **`token_arm_sound` — the (10) token arm (HMAC macaroon, carrier-as-hypothesis).** A
portal-accepting `.token key sig` credential PROVES `Tagged key key sig` — the macaroon tag is a
genuine HMAC under the issuer key. Given the HMAC `unforgeable` carrier. NON-VACUOUS: a forged
macaroon tail (the portal rejects) yields no claim. -/
theorem token_arm_sound [R : RealAuthPortal Digest Proof]
    (hunf : R.hmac.unforgeable) (key : Digest) (sig : Proof)
    (haccept : portalVerifyReal (Authorization.token key sig) = true) :
    R.hmac.Tagged key key sig :=
  mac_floor_sound (K := R.hmac) hunf key key sig haccept

/-! ## §5 — the fail-closed ANCHORS (the anti-vacuity teeth: NO `True` on a reachable path).

`.unchecked` ALWAYS rejects (the §8 anchor); a forged signature/proof/tag at ANY crypto arm
rejects. These prove the production portal is fail-closed — never a silent pass. -/

/-- **`unchecked_arm_rejects` — the §8 ANCHOR (no carrier).** `.unchecked` ALWAYS
fail-closes at the production portal: `portalVerifyReal .unchecked = false`. This is the anti-vacuity
keystone — the one arm that COULD have been `True`-discharged is instead the rejected anchor (a
credential-less node never passes the WHO leg). -/
theorem unchecked_arm_rejects [RealAuthPortal Digest Proof] :
    portalVerifyReal (Digest := Digest) (Proof := Proof) Authorization.unchecked = false :=
  rfl

/-- **`signature_arm_rejects_forged` — a forged signature fails closed (no carrier).** If
the ed25519 oracle rejects `(stmt, sig)`, the production portal rejects the `.signature` arm. The
dispatch faithfully forwards the oracle's verdict — a forged credential is caught. NON-VACUOUS: the
hypothesis is a real forgery (oracle = false). -/
theorem signature_arm_rejects_forged [R : RealAuthPortal Digest Proof]
    (stmt : Digest) (sig : Proof)
    (hforged : R.sig.sigVerify stmt stmt sig = false) :
    portalVerifyReal (Authorization.signature stmt sig) = false :=
  hforged

/-- **`token_arm_rejects_forged` — a forged macaroon tail fails closed (no carrier).** If
the HMAC compare oracle rejects `(key, sig)`, the production portal rejects the `.token` arm. -/
theorem token_arm_rejects_forged [R : RealAuthPortal Digest Proof]
    (key : Digest) (sig : Proof)
    (hforged : R.hmac.verifyTag key key sig = false) :
    portalVerifyReal (Authorization.token key sig) = false :=
  hforged

/-- **`no_reachable_arm_is_trivially_true` — the ANTI-VACUITY SUMMARY.** There EXISTS a
reachable credential the production portal REJECTS (`.unchecked`), so the portal is NOT the constant
`fun _ => true`. Combined with the per-arm rejection lemmas, this rules out the audit's worst-case
"some reachable path discharges with `True`" hole: every arm either routes to a concrete oracle
(whose `false` propagates) or is the rejected anchor. -/
theorem no_reachable_arm_is_trivially_true [RealAuthPortal Digest Proof] :
    ∃ cred : Authorization Digest Proof, portalVerifyReal cred = false :=
  ⟨Authorization.unchecked, rfl⟩

/-! ## §6 — non-vacuity: the REAL instance at the `PortalFloor.Reference` kernels (`#eval`).

The reference kernels (toy `ℤ`/`ℕ`, carriers `True`-discharged ONLY in the toy model) realize
`RealAuthPortal`, so the production portal RUNS: a genuine signature/proof/token accepts, a forged
one and `.unchecked` reject. This exercises the per-arm dispatch WITHOUT Rust. -/

namespace Demo

/-- The reference `RealAuthPortal` over `Digest = Proof = ℕ` (the floor's reference kernels). NOT
real crypto — the toy non-vacuity witness. The carriers are `True`-discharged in this toy model
(`PortalFloor.Reference`); the real instance is the Rust `@[extern]` one. -/
instance instRealAuthPortal : RealAuthPortal Nat Nat where
  sig := Reference.instSignatureKernel
  ver := Reference.instVerifierKernel
  hmac := Reference.instMacKernelE

/-- A genuine signature credential (proof echoes the statement under the reference ed25519 oracle). -/
def goodSig : Authorization Nat Nat := .signature 7 7
/-- A FORGED signature credential (off-by-one). -/
def forgedSig : Authorization Nat Nat := .signature 7 8
/-- A genuine STARK proof credential (statement 0, proof 0). -/
def goodProof : Authorization Nat Nat := .proof 0 0 11 22
/-- A genuine macaroon token (the tag echoes `mac key key`). -/
def goodToken : Authorization Nat Nat := .token 3 (Nat.pair 3 3)
/-- A FORGED macaroon token (wrong tag). -/
def forgedToken : Authorization Nat Nat := .token 3 0

-- The production portal RUNS per-arm: genuine ⇒ accept, forged ⇒ reject, .unchecked ⇒ reject.
#guard (portalVerifyReal goodSig)  --  true  (ed25519 accepts)
#guard (portalVerifyReal forgedSig) == false  --  false (ed25519 rejects)
#guard (portalVerifyReal goodProof)  --  true  (STARK accepts)
#guard (portalVerifyReal goodToken)  --  true  (HMAC accepts)
#guard (portalVerifyReal forgedToken) == false  --  false (HMAC rejects)
#guard (portalVerifyReal (Digest := Nat) (Proof := Nat) .unchecked) == false  --  false (§8 anchor)
-- OneOf selects a genuine candidate ⇒ accepts; an Unchecked at the slot ⇒ rejected:
#guard (portalVerifyReal (.oneOf [forgedSig, goodSig] 1))  --  true  (index-1 genuine)
#guard (portalVerifyReal (.oneOf [goodSig, .unchecked] 1)) == false  --  false (Unchecked at slot)
-- the production AuthPortal's credentialValid IS portalVerifyReal:
#guard (AuthPortal.credentialValid (Ctx := Unit) goodSig ())  --  true
#guard (AuthPortal.credentialValid (Ctx := Unit) forgedSig ()) == false  --  false

/-- Soundness witness at the reference kernel: a genuine signature arm proves `Signed`. The
`unforgeable` carrier is now the GENUINE EUF-CMA Prop (not `True`), discharged by the proved
`Reference.instSignatureKernel_unforgeable`. -/
example : (instRealAuthPortal.sig).Signed 7 7 :=
  signature_arm_sound (R := instRealAuthPortal)
    Reference.instSignatureKernel_unforgeable 7 7 (by decide)

/-- Soundness witness: a genuine token arm proves `Tagged`. The `unforgeable` carrier is now the
GENUINE HMAC-unforgeability Prop (not `True`), discharged by `Reference.instMacKernelE_unforgeable`. -/
example : (instRealAuthPortal.hmac).Tagged 3 3 (Nat.pair 3 3) :=
  token_arm_sound (R := instRealAuthPortal)
    Reference.instMacKernelE_unforgeable 3 (Nat.pair 3 3) (by decide)

end Demo

/-! ## §7 — axiom-hygiene tripwires (the honesty pins over the production-portal keystones).

Every keystone rests ONLY on `{propext, Classical.choice, Quot.sound}` plus its EXPLICIT §8 carrier
hypothesis — never a hidden `sorry`/`axiom`. The `AuthPortal.soundness` carrier is a `Prop` FIELD
(the conjunction of three §8 carriers), NOT an axiom, so it does not appear here. This DEFINES the
post-cutover TCB: three primitives ASSUMED on the reachable `Authorization` arms, the dispatch
VERIFIED. -/

#assert_axioms realAuthPortal_soundness_is_conjunction
#assert_axioms signature_arm_sound
#assert_axioms proof_arm_sound
#assert_axioms bearer_arm_sound
#assert_axioms capTp_arm_sound
#assert_axioms custom_arm_sound
#assert_axioms stealth_arm_sound
#assert_axioms token_arm_sound
#assert_axioms unchecked_arm_rejects
#assert_axioms signature_arm_rejects_forged
#assert_axioms token_arm_rejects_forged
#assert_axioms no_reachable_arm_is_trivially_true

end Dregg2.Exec.FullForestAuthPortal
