/-
MtlsHybridCorrect — post-quantum HYBRID (ed25519 ∧ ML-DSA-65) for the two
mutual-TLS signature-verify seams:

  * **Seam A — the RFC 8446 §4.4.3 CertificateVerify peer-auth signature** (the
    proof the peer holds the leaf private key), the `Mtls.Env.cvVerify` boundary.
  * **Seam B — the RFC 5280 §6.1.3 certificate-chain signature** (a certificate
    signed under its issuer's public key), the `Mtls.Env.verifySig` boundary.

This is PQ-edge cut #3 (after the JWT signature #1 and the TLS X-Wing KEX #2). It
REUSES the proven JWT hybrid pattern (`Jwt.hybridVerify`, `Jwt.jwt_hybrid_sound`,
`Jwt.jwt_hybrid_no_downgrade`) and `Crypto.mlDsaVerify` VERBATIM: the classical
Ed25519 verify (`Crypto.ed25519Verify`, HACL*/EverCrypt) is composed with dregg's
proven FIPS-204 ML-DSA-65 verify (`Crypto.mlDsaVerify`, resting on the named
`Crypto.Assumptions.mlDsaVerify_authentic` = dregg's `MlDsaVerifyReal.verifyCore`).
Both halves must verify (fail-closed); the ML-DSA public key is PINNED (enrolled
roster, never self-carried), the FIPS-204 `ctx` domain-separates — matching dregg's
federation-core `Id = H(ed25519 ‖ ml_dsa)` construction, the same construction the
JWT cut matched.

dregg's ML-DSA-65 core is REUSED, not re-claimed: the forgery-resistance is
`Crypto.Assumptions.mlDsaVerify_authentic`, surfaced through
`Crypto.mlDsaVerify_authentic_at`. The orb's NEW results here are the per-seam
hybrid COMPOSITION (`mtls_cv_hybrid_sound`, `mtls_cert_hybrid_sound` — control-flow
facts, axiom-clean save `propext`, naming BOTH real primitives so non-vacuous),
the fail-closed both-verify carried onto the DEPLOYED `Mtls.authenticate`, and the
no-downgrade pinning (`mtls_cv_hybrid_no_downgrade`, `mtls_cert_hybrid_no_downgrade`):
a hybrid-pinned peer rejects an ed25519-only CertificateVerify / certificate
signature.
-/
import Crypto
import Mtls.Verify
import Mtls.Theorems

namespace Mtls
namespace Hybrid

/-! ## Seam A — the RFC 8446 §4.4.3 CertificateVerify peer-auth signature.

The client's proof-of-possession signature is hybridized: it verifies ONLY when
BOTH the classical Ed25519 signature AND the FIPS-204 ML-DSA-65 signature check
out over the §4.4.3 content, under the leaf's pinned ed25519 key and the leaf
identity's ENROLLED (pinned) ML-DSA-65 key. This is `Jwt.hybridVerify` for the
mTLS CertificateVerify shape (`Cert → ByteArray → ByteArray → Bool`). -/

/-- The pins for the CertificateVerify hybrid, mirroring `Jwt.Config`'s hybrid
fields: the leaf's classical ed25519 key, the leaf identity's ENROLLED ML-DSA-65
key (pinned roster, never taken from the wire), the FIPS-204 `ctx`, and the codec
that splits the CertificateVerify signature into its `(ed25519, ML-DSA-65)`
halves. A `none` split ⇒ classical-only / malformed ⇒ fail-closed. -/
structure CvPin where
  /-- The leaf certificate's classical ed25519 public key (the classical half). -/
  edPubKey     : Cert → ByteArray
  /-- The leaf identity's ENROLLED FIPS-204 ML-DSA-65 public key — the pinned
  roster half. Defaults empty (a leaf that has not enrolled a PQ half). -/
  mlDsaPubKey  : Cert → ByteArray := fun _ => ByteArray.empty
  /-- The FIPS-204 `ctx` domain-separation string for the ML-DSA-65 half. -/
  mlDsaCtx     : ByteArray := ByteArray.empty
  /-- Split a hybrid CertificateVerify signature into `(ed25519, ML-DSA-65)`
  halves; `none` (classical-only / malformed) ⇒ fail-closed. -/
  splitHybridSig : ByteArray → Option (ByteArray × ByteArray) := fun _ => none

/-- Ed25519 verify via the verified boundary (HACL*/EverCrypt). -/
def cvEdVerify (pub content sig : ByteArray) : Bool :=
  Crypto.ed25519Verify pub content sig

/-- ML-DSA-65 verify via dregg's proven boundary (`Crypto.mlDsaVerify`). -/
def cvMldsaVerify (pub content sig ctx : ByteArray) : Bool :=
  Crypto.mlDsaVerify pub content sig ctx

/-- **The hybrid CertificateVerify — ed25519 ∧ ML-DSA-65, fail-closed.** The
signature splits into its two halves; the proof-of-possession verifies ONLY when
BOTH the classical Ed25519 signature (under the leaf's pinned ed25519 key) AND the
ML-DSA-65 signature (under the leaf's pinned ML-DSA-65 key and the FIPS-204 `ctx`)
verify over the §4.4.3 content. Either half missing (`none` split) or bad ⇒
`false`. This is `Jwt.hybridVerify` for the `Env.cvVerify` shape. -/
def hybridCvVerify (pin : CvPin) (leaf : Cert) (content sig : ByteArray) : Bool :=
  match pin.splitHybridSig sig with
  | some (edSig, mldsaSig) =>
      cvEdVerify (pin.edPubKey leaf) content edSig
        && cvMldsaVerify (pin.mlDsaPubKey leaf) content mldsaSig pin.mlDsaCtx
  | none => false

/-- **`mtls_cv_hybrid_sound`.** The hybrid CertificateVerify accepts IFF BOTH the
classical Ed25519 signature AND the post-quantum ML-DSA-65 signature verify (once
the signature splits into its two halves). Non-vacuous: it names both real
primitives (`Crypto.ed25519Verify`, `Crypto.mlDsaVerify`). Axiom-clean save
`propext` — a statement about the composition's control flow, holding for every
behaviour of the two verifiers. Mirrors `Jwt.jwt_hybrid_sound`. -/
theorem mtls_cv_hybrid_sound (pin : CvPin) (leaf : Cert)
    (content sig edSig mldsaSig : ByteArray)
    (hsplit : pin.splitHybridSig sig = some (edSig, mldsaSig)) :
    hybridCvVerify pin leaf content sig = true ↔
      (Crypto.ed25519Verify (pin.edPubKey leaf) content edSig = true
        ∧ Crypto.mlDsaVerify (pin.mlDsaPubKey leaf) content mldsaSig pin.mlDsaCtx = true) := by
  simp only [hybridCvVerify, cvEdVerify, cvMldsaVerify, hsplit, Bool.and_eq_true]

/-- **`mtls_cv_hybrid_no_downgrade`.** A hybrid-pinned peer REJECTS an ed25519-only
(classical-only) CertificateVerify: a signature carrying no ML-DSA-65 half
(`splitHybridSig = none`) fails-closed, regardless of whether its classical half
would verify. The anti-downgrade property — a valid classical proof-of-possession
is not enough for a PQ-enrolled identity. Mirrors `Jwt.jwt_hybrid_no_downgrade`. -/
theorem mtls_cv_hybrid_no_downgrade (pin : CvPin) (leaf : Cert)
    (content sig : ByteArray)
    (hclassical : pin.splitHybridSig sig = none) :
    hybridCvVerify pin leaf content sig = false := by
  unfold hybridCvVerify
  rw [hclassical]

/-- **The ML-DSA half's authenticity is dregg's, cited not re-claimed.** Under a
pinned ML-DSA-65 key `mlDsaPubOf seed`, a hybrid CertificateVerify that accepts had
a GENUINE ML-DSA-65 signature by the matching seed — delivered by dregg's proven
verify core through `Crypto.mlDsaVerify_authentic_at`. Its `#print axioms` names
`Crypto.Assumptions.mlDsaVerify_authentic`, surfacing the dregg FIPS-204 dependency
honestly. -/
theorem mtls_cv_hybrid_mldsa_authentic (pin : CvPin) (leaf : Cert)
    (content sig edSig mldsaSig seed : ByteArray)
    (hsplit : pin.splitHybridSig sig = some (edSig, mldsaSig))
    (hpin : pin.mlDsaPubKey leaf = Crypto.Assumptions.mlDsaPubOf seed)
    (h : hybridCvVerify pin leaf content sig = true) :
    Crypto.Assumptions.mlDsaGenuine seed pin.mlDsaCtx content mldsaSig := by
  have hb := (mtls_cv_hybrid_sound pin leaf content sig edSig mldsaSig hsplit).mp h
  have hm := hb.2
  rw [hpin] at hm
  exact Crypto.mlDsaVerify_authentic_at seed pin.mlDsaCtx content mldsaSig hm

/-! ### Onto the DEPLOYED decision (`Mtls.authenticate`)

A hybrid-pinned `Env` instantiates `cvVerify` with `hybridCvVerify`. The deployed
decision then carries the fail-closed both-verify and the no-downgrade. -/

/-- A hybrid-pinned mTLS environment: `cvVerify` is the ed25519 ∧ ML-DSA-65 hybrid
CertificateVerify; the chain-signature and anchors are the deployment's. -/
def cvHybridEnv (pin : CvPin) (vsig : Cert → Cert → Bool) (anchors : List Cert) : Env :=
  { verifySig := vsig, cvVerify := hybridCvVerify pin, anchors := anchors }

/-- **Fail-closed on the deployed decision.** If the deployed `Mtls.authenticate`
under a hybrid-pinned `Env` establishes an identity, then BOTH the Ed25519 AND the
ML-DSA-65 halves of the client CertificateVerify verified over the §4.4.3 content
under the leaf's pinned keys — a classical-only (broken-PQ) or PQ-only
(broken-classical) proof-of-possession cannot authenticate. Mirrors
`Jwt.jwt_hybrid_fail_closed`. -/
theorem mtls_authenticate_cv_hybrid_both (pin : CvPin) (vsig : Cert → Cert → Bool)
    (anchors : List Cert) (now : Time) (chain : Chain)
    (transcriptHash cvSig edSig mldsaSig : ByteArray) (id : Name)
    (hsplit : pin.splitHybridSig cvSig = some (edSig, mldsaSig))
    (h : authenticate (cvHybridEnv pin vsig anchors) now chain transcriptHash cvSig = some id) :
    ∃ leaf rest, chain = leaf :: rest
      ∧ Crypto.ed25519Verify (pin.edPubKey leaf)
          (clientCertVerifyContent transcriptHash) edSig = true
      ∧ Crypto.mlDsaVerify (pin.mlDsaPubKey leaf)
          (clientCertVerifyContent transcriptHash) mldsaSig pin.mlDsaCtx = true := by
  obtain ⟨leaf, rest, hchain, _, _, hcv⟩ := authenticate_eq_some h
  have hb := (mtls_cv_hybrid_sound pin leaf
    (clientCertVerifyContent transcriptHash) cvSig edSig mldsaSig hsplit).mp hcv
  exact ⟨leaf, rest, hchain, hb.1, hb.2⟩

/-- **No-downgrade on the deployed decision.** A hybrid-pinned `Env` yields NO
identity for a classical-only (ed25519-only) CertificateVerify — even a fully
valid RFC 5280 path with a genuine classical proof-of-possession is rejected when
the ML-DSA-65 half is absent. Mirrors `Jwt.jwt_hybrid_admit_is_hybrid`. -/
theorem mtls_authenticate_cv_hybrid_no_downgrade (pin : CvPin)
    (vsig : Cert → Cert → Bool) (anchors : List Cert) (now : Time) (chain : Chain)
    (transcriptHash cvSig : ByteArray)
    (hclassical : pin.splitHybridSig cvSig = none) :
    authenticate (cvHybridEnv pin vsig anchors) now chain transcriptHash cvSig = none := by
  cases chain with
  | nil => rfl
  | cons leaf rest =>
    exact authenticate_no_possession
      (mtls_cv_hybrid_no_downgrade pin leaf
        (clientCertVerifyContent transcriptHash) cvSig hclassical)

/-! ## Seam B — the RFC 5280 §6.1.3 certificate-chain signature.

A certificate is validly signed by its issuer ONLY when BOTH the classical Ed25519
signature AND the FIPS-204 ML-DSA-65 signature over the child's to-be-signed bytes
verify, under the issuer's pinned ed25519 and ML-DSA-65 keys. Same construction as
Seam A, for the `Env.verifySig` shape. -/

/-- The pins for the certificate-signature hybrid: the issuer's classical ed25519
key, the issuer's ENROLLED ML-DSA-65 key, the FIPS-204 `ctx`, the child's TBS
bytes, and the codec that splits the child's signature into its two halves. -/
structure CertPin where
  /-- The issuer certificate's classical ed25519 public key. -/
  edPubKey     : Cert → ByteArray
  /-- The issuer's ENROLLED FIPS-204 ML-DSA-65 public key (pinned roster). -/
  mlDsaPubKey  : Cert → ByteArray := fun _ => ByteArray.empty
  /-- The FIPS-204 `ctx` domain-separation string. -/
  mlDsaCtx     : ByteArray := ByteArray.empty
  /-- The child certificate's to-be-signed (TBS) bytes. -/
  tbs          : Cert → ByteArray
  /-- Split the child's certificate signature into its `(ed25519, ML-DSA-65)`
  halves; `none` (classical-only / malformed) ⇒ fail-closed. -/
  splitCertSig : Cert → Option (ByteArray × ByteArray) := fun _ => none

/-- **The hybrid certificate-signature verify — ed25519 ∧ ML-DSA-65, fail-closed.**
The child's signature splits into two halves; the certificate is validly signed
ONLY when BOTH the classical Ed25519 signature AND the ML-DSA-65 signature verify
over the child's TBS bytes, under the issuer's pinned keys. -/
def hybridVerifySig (pin : CertPin) (issuer child : Cert) : Bool :=
  match pin.splitCertSig child with
  | some (edSig, mldsaSig) =>
      Crypto.ed25519Verify (pin.edPubKey issuer) (pin.tbs child) edSig
        && Crypto.mlDsaVerify (pin.mlDsaPubKey issuer) (pin.tbs child) mldsaSig pin.mlDsaCtx
  | none => false

/-- **`mtls_cert_hybrid_sound`.** The hybrid certificate signature accepts IFF BOTH
the classical Ed25519 AND the ML-DSA-65 signature verify over the child's TBS
bytes. Non-vacuous (names both real primitives); axiom-clean save `propext`. -/
theorem mtls_cert_hybrid_sound (pin : CertPin) (issuer child : Cert)
    (edSig mldsaSig : ByteArray)
    (hsplit : pin.splitCertSig child = some (edSig, mldsaSig)) :
    hybridVerifySig pin issuer child = true ↔
      (Crypto.ed25519Verify (pin.edPubKey issuer) (pin.tbs child) edSig = true
        ∧ Crypto.mlDsaVerify (pin.mlDsaPubKey issuer) (pin.tbs child) mldsaSig pin.mlDsaCtx = true) := by
  simp only [hybridVerifySig, hsplit, Bool.and_eq_true]

/-- **`mtls_cert_hybrid_no_downgrade`.** A hybrid-pinned issuer REJECTS an
ed25519-only certificate signature: a child signature carrying no ML-DSA-65 half
(`splitCertSig = none`) fails-closed, regardless of its classical half. -/
theorem mtls_cert_hybrid_no_downgrade (pin : CertPin) (issuer child : Cert)
    (hclassical : pin.splitCertSig child = none) :
    hybridVerifySig pin issuer child = false := by
  unfold hybridVerifySig
  rw [hclassical]

/-- The issuer's ML-DSA half authenticity is dregg's, cited: under a pinned key
`mlDsaPubOf seed`, a hybrid certificate signature that accepts had a GENUINE
ML-DSA-65 signature by the matching seed (via `Crypto.mlDsaVerify_authentic_at`). -/
theorem mtls_cert_hybrid_mldsa_authentic (pin : CertPin) (issuer child : Cert)
    (edSig mldsaSig seed : ByteArray)
    (hsplit : pin.splitCertSig child = some (edSig, mldsaSig))
    (hpin : pin.mlDsaPubKey issuer = Crypto.Assumptions.mlDsaPubOf seed)
    (h : hybridVerifySig pin issuer child = true) :
    Crypto.Assumptions.mlDsaGenuine seed pin.mlDsaCtx (pin.tbs child) mldsaSig := by
  have hb := (mtls_cert_hybrid_sound pin issuer child edSig mldsaSig hsplit).mp h
  have hm := hb.2
  rw [hpin] at hm
  exact Crypto.mlDsaVerify_authentic_at seed pin.mlDsaCtx (pin.tbs child) mldsaSig hm

/-- A hybrid-pinned mTLS environment for the certificate-chain signature. -/
def certHybridEnv (pin : CertPin) (cvv : Cert → ByteArray → ByteArray → Bool)
    (anchors : List Cert) : Env :=
  { verifySig := hybridVerifySig pin, cvVerify := cvv, anchors := anchors }

/-- **Fail-closed on the deployed decision (leaf link).** If the deployed
`Mtls.authenticate` under a hybrid cert-signature `Env` establishes an identity for
a chain `leaf :: issuer :: rest`, then the leaf's certificate signature had BOTH the
Ed25519 AND the ML-DSA-65 halves verify under the issuer's pinned keys over the
leaf's TBS — a classical-only certificate signature on the leaf cannot chain. -/
theorem mtls_authenticate_cert_hybrid_leaf_both (pin : CertPin)
    (cvv : Cert → ByteArray → ByteArray → Bool) (anchors : List Cert) (now : Time)
    (leaf issuer : Cert) (rest : Chain) (transcriptHash cvSig : ByteArray) (id : Name)
    (edSig mldsaSig : ByteArray)
    (hsplit : pin.splitCertSig leaf = some (edSig, mldsaSig))
    (h : authenticate (certHybridEnv pin cvv anchors) now (leaf :: issuer :: rest)
          transcriptHash cvSig = some id) :
    Crypto.ed25519Verify (pin.edPubKey issuer) (pin.tbs leaf) edSig = true
      ∧ Crypto.mlDsaVerify (pin.mlDsaPubKey issuer) (pin.tbs leaf) mldsaSig pin.mlDsaCtx = true := by
  obtain ⟨_, _, _, _, hv, _⟩ := authenticate_eq_some h
  have hls := verify_needs_linkedSigned hv
  have hsig : hybridVerifySig pin issuer leaf = true := hls.1
  exact (mtls_cert_hybrid_sound pin issuer leaf edSig mldsaSig hsplit).mp hsig

/-! ## My-hand tests — the deployed decision under a demo hybrid boundary

The real primitives (`Crypto.ed25519Verify`, `Crypto.mlDsaVerify`) are `opaque`
(they route to HACL* / dregg-pq at runtime) and do not kernel-reduce, so the
kernel-evaluated witnesses run `Mtls.authenticate` under a DEMO hybrid boundary
that mirrors the both-must-verify / fail-closed-on-missing-PQ-half control flow
exactly (the same structure the abstract theorems above cover, which name the real
primitives). Three outcomes are distinguished:

  * a hybrid CertificateVerify carrying BOTH halves VERIFIES (`some 7`);
  * a TAMPERED ML-DSA-65 half FAILS (`none`) — even with a good classical half;
  * an ed25519-ONLY CertificateVerify FAILS (`none`) against the hybrid-pinned
    peer — the no-downgrade. -/
namespace Demo

/-- A directly-trusted self-issued CA root: subject/issuer `0`, valid `[0,100]`. -/
def rootCert : Cert := ⟨0, 0, 0, 100, true⟩
/-- An end-entity leaf: subject `7`, issued by `0`, not a CA, valid `[0,100]`. -/
def leafCert : Cert := ⟨7, 0, 0, 100, false⟩
/-- Demo certificate-signature boundary: a child is signed iff its issuer name
matches the issuer's subject (stands in for the classical chain check). -/
def demoVerifySig (issuer child : Cert) : Bool := decide (child.issuer = issuer.subject)
/-- The handshake transcript hash the client CertificateVerify signs (opaque). -/
def demoTranscript : ByteArray := ByteArray.mk #[9]

/-- Demo hybrid CertificateVerify — the ed25519 ∧ ML-DSA-65 both-verify /
fail-closed control flow at the byte level, using `decide`-reducible `ByteArray`
`.size`/`.get!` byte reads (whole-`ByteArray` equality does not kernel-reduce). A
2-byte signature `[ed, mldsa]` is the hybrid form; a 1-byte signature is
classical-only. Three INDEPENDENT conjuncts, all required: the hybrid form is
present (2 bytes), the classical ed25519 half is valid (byte 0 = `1`), AND the
post-quantum ML-DSA-65 half is valid (byte 1 = `1`). A tampered ML-DSA half
(byte 1 ≠ `1`) fails the PQ conjunct; a 1-byte classical-only signature fails the
hybrid-form conjunct (no PQ half at all). -/
def demoHybridCv (_leaf : Cert) (_content sig : ByteArray) : Bool :=
  decide (sig.size = 2)        -- the hybrid form is present (an ed + an ML-DSA half)
    && decide (sig.get! 0 = 1) -- classical ed25519 half valid
    && decide (sig.get! 1 = 1) -- post-quantum ML-DSA-65 half valid

/-- The demo hybrid-pinned environment. -/
def demoHybridEnv : Env :=
  { verifySig := demoVerifySig, cvVerify := demoHybridCv, anchors := [rootCert] }

/-- A hybrid CertificateVerify carrying BOTH halves valid. -/
def goodHybridSig : ByteArray := ByteArray.mk #[1, 1]
/-- A hybrid CertificateVerify whose ML-DSA-65 half is TAMPERED (classical half ok). -/
def tamperedMldsaSig : ByteArray := ByteArray.mk #[1, 0]
/-- An ed25519-ONLY CertificateVerify (no PQ half) — the downgrade attempt. -/
def ed25519OnlySig : ByteArray := ByteArray.mk #[1]

/-- **VERIFY.** A valid chain with a hybrid CertificateVerify (both halves) at a
valid time authenticates the leaf subject (`7`). -/
example :
    authenticate demoHybridEnv 50 [leafCert, rootCert] demoTranscript goodHybridSig = some 7 := by
  decide

/-- **TAMPERED ML-DSA FAILS.** The same valid chain, but the ML-DSA-65 half of the
CertificateVerify is tampered — no identity, though the classical half is good. -/
example :
    authenticate demoHybridEnv 50 [leafCert, rootCert] demoTranscript tamperedMldsaSig = none := by
  decide

/-- **DOWNGRADE FAILS.** The same valid chain with an ed25519-only CertificateVerify
(no ML-DSA-65 half) is REJECTED by the hybrid-pinned peer — the no-downgrade. -/
example :
    authenticate demoHybridEnv 50 [leafCert, rootCert] demoTranscript ed25519OnlySig = none := by
  decide

/-- …and the only difference between the accepting and the downgrade case is the
missing PQ half: the tampered and the classical-only both fail, the full hybrid
succeeds — so the rejections are due precisely to the ML-DSA-65 requirement. -/
example :
    (authenticate demoHybridEnv 50 [leafCert, rootCert] demoTranscript goodHybridSig = some 7)
    ∧ (authenticate demoHybridEnv 50 [leafCert, rootCert] demoTranscript tamperedMldsaSig = none)
    ∧ (authenticate demoHybridEnv 50 [leafCert, rootCert] demoTranscript ed25519OnlySig = none) := by
  decide

end Demo

end Hybrid
end Mtls

#print axioms Mtls.Hybrid.mtls_cv_hybrid_sound
#print axioms Mtls.Hybrid.mtls_cv_hybrid_no_downgrade
#print axioms Mtls.Hybrid.mtls_cv_hybrid_mldsa_authentic
#print axioms Mtls.Hybrid.mtls_authenticate_cv_hybrid_both
#print axioms Mtls.Hybrid.mtls_authenticate_cv_hybrid_no_downgrade
#print axioms Mtls.Hybrid.mtls_cert_hybrid_sound
#print axioms Mtls.Hybrid.mtls_cert_hybrid_no_downgrade
#print axioms Mtls.Hybrid.mtls_cert_hybrid_mldsa_authentic
#print axioms Mtls.Hybrid.mtls_authenticate_cert_hybrid_leaf_both
