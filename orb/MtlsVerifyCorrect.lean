/-
MtlsVerifyCorrect — CORRECTNESS of the mutual-TLS client-certificate decision.

This module lifts the mutual-TLS client-authentication decision from a *safety*
statement (the validator never crashes; a rejected chain yields no identity) to
a *correctness* statement: the decision matches, on every input, an independent
specification written directly from the governing standards, and it establishes
a client identity in **exactly** the cases the standards permit — no more, no
less.

The function certified here is the one the running reactor calls.  When a client
presents a certificate chain, the reactor's PKI accept gate derives the client
identity through `Reactor.PkiWire.mtlsIdentity`, which is *definitionally*
`Mtls.authenticate env now chain` (`deployed_gate_eq_authenticate` below proves
the identity by `rfl`).  The headline theorem `authenticate_correct` is stated
over that same `Mtls.authenticate`, and `mtlsIdentity_correct` transports it onto
the reactor gate verbatim — so the refinement binds the deployed decision, not a
proof-local re-statement of it.

The standards fixed here:

  * **RFC 5280 §6.1 (Certification Path Validation).**  A leaf-first path
    `[c₀, c₁, …, cₙ]` is a valid certification path at verification time `now`
    against a set of trust anchors when: every certificate is inside its
    validity window (§6.1.3 (a)(2)); each non-top certificate's signature
    verifies under the public key of the next certificate up the path
    (§6.1.3 (a)(1)); every certificate that issues another asserts the CA basic
    constraint (§6.1.4, `basicConstraints` `cA = TRUE`); and the top of the path
    is a configured trust anchor (§6.1.1 (d), §6.1.4).

  * **RFC 8446 §4.4.3 (CertificateVerify).**  The client proves possession of
    the leaf (end-entity) private key by signing the handshake-transcript
    content — 64 space octets, the context string
    `"TLS 1.3, client CertificateVerify"`, a `0x00` separator, then the
    transcript hash — under the leaf certificate's public key.  Chain validation
    alone proves only that the presented certificates form a trusted path;
    without this check a peer presenting any publicly-visible chain would be
    authenticated as that identity without holding its private key.

Two cryptographic boundaries are threaded, never opened: `Env.verifySig`
(certificate signatures, RFC 5280 §6.1.3 (a)(1)) and `Env.cvVerify` (the
CertificateVerify proof-of-possession, RFC 8446 §4.4.3).  Every result holds
uniformly for every possible behaviour of those primitives — the correctness is
about the *composition* of the path-validation conditions, the proof-of-possession
check and the identity extraction, not about the cipher.

The specification (`Rfc5280Path`, `AuthIdentity`) is stated **from the standards,
in set-and-index vocabulary** — membership, adjacency via `List.zip … tail`, the
terminal element via `getLast?`, and the §4.4.3 proof-of-possession conjunct —
with no reference to the validator's recursion.  The headline theorem
`authenticate_correct` proves the deployed decision establishes an identity
**iff** the specification holds, and the concrete `example`s at the end witness
non-vacuity: an unverified chain, an expired certificate, a broken signature
link, and a valid chain with a **bad/absent CertificateVerify** each yield **no**
identity, while a well-formed chain carrying a valid CertificateVerify yields the
leaf subject.

## Binding the transcript and signature bytes to the live TLS state

The deployed decision (`Mtls.authenticate`) enforces **both** the RFC 5280
§6.1 certification-path checks and the RFC 8446 §4.4.3 `CertificateVerify`
proof-of-possession, and this refinement certifies exactly that conjunction.

The earlier residual was *plumbing*: the transcript-hash and CertificateVerify-
signature bytes were surfaced by opaque functions — first two independent
`TlsConn → Bytes → ByteArray` fields, then a single but still **free**
`clientAuthOf` field a caller could fill with arbitrary bytes.  That is now
closed: the client-auth view is **no longer a field of `PkiCfg`**.  It is
`Reactor.PkiWire.clientAuthOfConn`, a fixed function that reads the real client
handshake bytes out of the **live TLS connection state** — the buffer the
deployed `Tls.St` (which the `Proto.TlsConn` carries) holds in its
`accum`/`handshaking`/`estabUser` phase, via `Reactor.TlsWire.connHandshakeBytes`
— and splits the client's CertificateVerify message out of that flight with the
real RFC 8446 §4 framing (`Reactor.PkiWire.scanCV`).  Concretely:

  * `PkiCfg.cvSigOf` is the **real RFC 8446 §4.4.3 parse** (`PkiWire.parseCvSig`)
    of the CertificateVerify message `scanCV` locates in the connection's own
    handshake buffer — a pure function of the live state, no free value; and
  * `PkiCfg.transcriptOf` is the real `Crypto.sha256` over the handshake-context
    prefix that precedes that message in the same buffer,

so neither is a caller value and the two are forced to come from **one** real
buffer the TLS state carries (`transcriptOf_from_state` / `cvSigOf_from_state` in
`Reactor.Pki`).  `mtlsIdentity_state_bound_correct` below states the headline
refinement with those state bindings made explicit: the CertificateVerify
conjunct is over the *parsed* wire signature and the *hashed* transcript, both
drawn from the deployed `Tls.St`.

The earlier residual — that `connHandshakeBytes` surfaced only the client flight
the abstract `Tls.St` lifecycle handle *retained* (the second-flight messages in
its phase-buffer tail), so the transcript hash covered only that tail's
handshake-context prefix and **not** the earlier flights the opaque handshake
engine had already consumed and dropped — is now closed at its source. `Tls.St`
carries a running handshake transcript field, `Tls.St.transcript`, that `Tls.step`
accumulates as it processes **every** received flight (RFC 8446 §4.4.1:
`Transcript-Hash(M₁ ‖ … ‖ Mₙ)` over the accumulated messages), so a message
consumed off an earlier flight is retained in the connection's own state rather
than dropped.  `connHandshakeBytes tc buf` is now exactly `tc.st.transcript ++
buf` (`Reactor.TlsWire.connHandshakeBytes_eq`), so the handshake-context prefix
`scanCV` peels off — the bytes the client `CertificateVerify` is checked over — is
the **full accumulated transcript across all received flights** (`ClientHello ‖ …
‖ client Certificate`), no longer the retained tail alone.
`mtlsIdentity_state_bound_correct` below states the headline refinement with that
accumulated field made explicit (`tc.st.transcript ++ buf`).

The last accumulation step is now closed too: the **server** flight
(`ServerHello ‖ EncryptedExtensions ‖ server Certificate ‖ server CertificateVerify
‖ server Finished`).  Previously the opaque handshake engine emitted it only as
sealed record bytes and never surfaced its plaintext handshake messages to the
`Tls` record layer, so `Tls.St.transcript` accumulated the client-received bytes
but not the server flight's plaintext.  That is fixed at the source: the handshake
`HsOut` (`Tls.HsOut.more`/`.done`) now carries a `flightPlain` field — the
**plaintext** server-flight handshake messages the engine emitted this step — and
`Tls.step` interleaves it into `Tls.St.transcript` (`transcriptDelta`), right after
the `ClientHello` that triggered it and before the client's second flight.  So
`Tls.St.transcript` is now the full RFC 8446 §4.4.1 sequence
`ClientHello ‖ server flight ‖ client Certificate ‖ …` — plaintext handshake
messages, the same bytes the server's own `Established.thSF` hashes (built in
`TlsHandshake.buildFlight` from the identical `sh ‖ ee ‖ cert ‖ cv ‖ sFin`).
Because the transcript now contains **two** CertificateVerify messages (the
server's, inside the server flight, and the client's), `Reactor.PkiWire.scanCV`
locates the **client's** — the last `0x0f`, folding the server's into the signed
context exactly as RFC 8446 §4.4.3 requires — so the client CertificateVerify is
checked over the full §4.4.1 transcript, server flight included.

What remains is a single modeling **convention**, not a security assumption, and
it is the same one every earlier flight already obeys: the `Tls` layer treats each
handshake message — received or emitted — as its bare `msg_type ‖ len ‖ body` bytes
(record framing elided), matching how the server's transcript hashes are computed
over `chMsg = stripRecord buf` and the bare builder outputs.  The forgeability is
fully closed either way: `transcriptHash` and `certVerifyMsg` are the TLS state's
own accumulated transcript, not independently supplied, and cannot be varied by any
caller.
-/

import Mtls.Verify
import Mtls.Theorems
import Reactor.Pki

namespace Mtls
namespace Correct

/-! ## The independent specification

Written directly from RFC 5280 §6.1, in set-and-index vocabulary, with no
reference to the validator `verifyFrom`. -/

/-- **RFC 5280 §6.1 certification-path validity, stated independently.**

A leaf-first path `chain = [c₀=leaf, …, cₙ=top]` is a valid certification path at
verification time `now` under the trust-anchor set `anchors` and the
certificate-signature primitive `vsig`.  Each field is a declarative,
recursion-free condition citing its RFC 5280 clause; adjacency is expressed by
`List.zip chain chain.tail` (the pairs `(cᵢ, cᵢ₊₁)`), the terminal certificate by
`getLast?`. -/
structure Rfc5280Path (anchors : List Cert) (vsig : Cert → Cert → Bool)
    (now : Time) (chain : Chain) : Prop where
  /-- The path is non-empty: there is an end-entity (leaf) certificate. -/
  hasLeaf  : chain ≠ []
  /-- §6.1.3 (a)(2): every certificate in the path is inside its stated validity
  window at the verification time. -/
  inWindow : ∀ c ∈ chain, c.notBefore ≤ now ∧ now ≤ c.notAfter
  /-- §6.1.3 (a)(1): for each adjacent pair `(child, issuer)` — child then the
  next certificate up the path — the child's signature verifies under the
  issuer's public key. -/
  signed   : ∀ p ∈ chain.zip chain.tail, vsig p.2 p.1 = true
  /-- §6.1.4: every certificate that issues another — every non-leaf certificate,
  i.e. every element after the head — asserts the CA basic constraint. -/
  caChain  : ∀ c ∈ chain.tail, c.isCA = true
  /-- §6.1.1 (d) / §6.1.4: the top (terminal) certificate of the path is a
  configured trust anchor. -/
  anchored : ∃ top, chain.getLast? = some top ∧ top ∈ anchors

/-- **The client-identity predicate (RFC 5280 §6.1 + RFC 8446 §4.4.3).**  A
client identity `id` is established from a presented chain exactly when:

  * the chain is `leaf :: rest` and `id` is the leaf (end-entity) subject;
  * that chain is a valid RFC 5280 certification path to a configured trust
    anchor at the verification time; and
  * the client's RFC 8446 §4.4.3 `CertificateVerify` signature `cvSig` verifies,
    under the `cvVerify` boundary, over the transcript-derived content
    (`clientCertVerifyContent transcriptHash`) with the **leaf** certificate's
    public key — proof that the peer holds the leaf private key.

If any conjunct fails there is no established identity — the peer is
unauthenticated.  The third conjunct is what stops a peer that merely copied a
publicly-visible certificate chain from being authenticated as that identity. -/
def AuthIdentity (anchors : List Cert) (vsig : Cert → Cert → Bool)
    (cvVerify : Cert → ByteArray → ByteArray → Bool)
    (now : Time) (chain : Chain) (transcriptHash cvSig : ByteArray)
    (id : Name) : Prop :=
  ∃ leaf rest,
    chain = leaf :: rest
    ∧ Rfc5280Path anchors vsig now (leaf :: rest)
    ∧ cvVerify leaf (clientCertVerifyContent transcriptHash) cvSig = true
    ∧ id = leaf.subject

/-! ## Bridging lemmas: the recursive validator equals the declarative spec

Each impl-side predicate from `Mtls.Verify`/`Mtls.Theorems` is proved equal to
its independent, recursion-free counterpart above.  These are where a wrong
implementation would be caught: if `verifyFrom` skipped the CA check, the window
check, the signature link, or the anchor, one of these equivalences (and hence
`rfc5280_iff`) would fail. -/

/-- The terminal certificate `topOf` (impl, mirrors the validator recursion)
coincides with the declarative `getLast?`. -/
theorem topOf_eq_getLast? (chain : Chain) : topOf chain = chain.getLast? := by
  induction chain with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons next rest =>
      have h1 : topOf (c :: next :: rest) = topOf (next :: rest) := rfl
      rw [h1, List.getLast?_cons_cons, ih]

/-- Window condition: the declarative field inequalities agree with the impl's
`allValid`/`validAt`. -/
theorem inWindow_iff_allValid (now : Time) (chain : Chain) :
    (∀ c ∈ chain, c.notBefore ≤ now ∧ now ≤ c.notAfter) ↔ allValid now chain := by
  unfold allValid
  constructor
  · intro h c hc; exact validAt_iff.mpr (h c hc)
  · intro h c hc; exact validAt_iff.mp (h c hc)

/-- Adjacency signing: the declarative `zip … tail` pairwise condition agrees
with the impl's recursive `linkedSigned`. -/
theorem signedAdj_iff_linkedSigned (env : Env) (chain : Chain) :
    (∀ p ∈ chain.zip chain.tail, env.verifySig p.2 p.1 = true)
      ↔ linkedSigned env chain := by
  induction chain with
  | nil => simp [linkedSigned]
  | cons c cs ih =>
    cases cs with
    | nil => simp [linkedSigned]
    | cons next rest =>
      simp only [linkedSigned, List.tail_cons, List.zip_cons_cons,
        List.forall_mem_cons]
      rw [← ih]
      simp [List.tail_cons]

/-- CA condition: the declarative `chain.tail` condition agrees with the impl's
`nonLeafCA`. -/
theorem caChain_iff_nonLeafCA (chain : Chain) :
    (∀ c ∈ chain.tail, c.isCA = true) ↔ nonLeafCA chain := by
  cases chain with
  | nil => simp [nonLeafCA]
  | cons c rest => simp [nonLeafCA]

/-- Trust-anchor condition: the declarative `getLast?` condition agrees with the
impl's `topAnchored`. -/
theorem anchoredTop_iff_topAnchored (env : Env) (chain : Chain) :
    (∃ top, chain.getLast? = some top ∧ top ∈ env.anchors)
      ↔ topAnchored env chain := by
  unfold topAnchored
  rw [topOf_eq_getLast?]

/-- **The validator equals the independent RFC 5280 path specification.**  The
total recursive validator `verifyFrom` accepts a chain iff the declarative,
recursion-free `Rfc5280Path` holds of it. -/
theorem rfc5280_iff (env : Env) (now : Time) (chain : Chain) :
    verifyFrom env now chain = true
      ↔ Rfc5280Path env.anchors env.verifySig now chain := by
  rw [verify_iff]
  constructor
  · rintro ⟨hAll, hLink, hCA, hTop⟩
    have hAnchor := (anchoredTop_iff_topAnchored env chain).mpr hTop
    refine
      { hasLeaf := ?_
        inWindow := (inWindow_iff_allValid now chain).mpr hAll
        signed := (signedAdj_iff_linkedSigned env chain).mpr hLink
        caChain := (caChain_iff_nonLeafCA chain).mpr hCA
        anchored := hAnchor }
    obtain ⟨top, htop, _⟩ := hAnchor
    intro hnil; rw [hnil] at htop; simp at htop
  · intro hp
    exact
      ⟨(inWindow_iff_allValid now chain).mp hp.inWindow,
       (signedAdj_iff_linkedSigned env chain).mp hp.signed,
       (caChain_iff_nonLeafCA chain).mp hp.caChain,
       (anchoredTop_iff_topAnchored env chain).mp hp.anchored⟩

/-! ## The refinement theorem — over the DEPLOYED decision

`Mtls.authenticate` is the function the reactor's PKI gate calls to decide a
client identity.  The theorem proves it establishes an identity **exactly** when
the independent RFC 5280 specification holds — both directions, over all inputs,
uniformly in the certificate-signature boundary. -/

/-- **CORRECTNESS (refinement).**  The deployed mutual-TLS decision
`Mtls.authenticate` yields the client identity `id` **iff** `AuthIdentity` holds:
the chain is an RFC 5280 valid path to a configured trust anchor **and** the
client's RFC 8446 §4.4.3 `CertificateVerify` signature verifies under the leaf
key, with `id` the end-entity subject.  Neither direction is vacuous: an
unverified chain (bad link, expired certificate, or unanchored top) *or* a chain
whose CertificateVerify does not verify makes the right side false, and the
theorem then forces `authenticate = none`. -/
theorem authenticate_correct (env : Env) (now : Time) (chain : Chain)
    (transcriptHash cvSig : ByteArray) (id : Name) :
    authenticate env now chain transcriptHash cvSig = some id
      ↔ AuthIdentity env.anchors env.verifySig env.cvVerify now chain
          transcriptHash cvSig id := by
  unfold AuthIdentity
  cases chain with
  | nil =>
    constructor
    · intro h; simp [authenticate] at h
    · rintro ⟨leaf, rest, hnil, _⟩; exact absurd hnil (by simp)
  | cons leaf rest =>
    simp only [authenticate]
    constructor
    · intro h
      split at h
      · rename_i hcond
        obtain ⟨hv, hcv⟩ := Bool.and_eq_true_iff.mp hcond
        exact ⟨leaf, rest, rfl,
          (rfc5280_iff env now (leaf :: rest)).mp hv, hcv,
          (Option.some.inj h).symm⟩
      · exact absurd h (by simp)
    · rintro ⟨leaf', rest', hchain, hpath, hcv, hid⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj hchain
      have hv : verifyFrom env now (leaf :: rest) = true :=
        (rfc5280_iff env now (leaf :: rest)).mpr hpath
      subst hid
      rw [if_pos (by rw [hv, hcv]; rfl)]

/-! ## Binding the reactor gate

`Reactor.PkiWire.mtlsIdentity` is the exact function the running reactor invokes
to derive a client identity from a presented chain (its `mtlsOk` gate tests
`isSome` of it).  It is definitionally `Mtls.authenticate`, and the refinement
transports onto it with no gap. -/

/-- The reactor's mTLS identity gate is exactly `Mtls.authenticate` on the
surfaced chain — the deployed decision, made explicit as a definitional
equality. -/
theorem deployed_gate_eq_authenticate
    (pcfg : Reactor.PkiWire.PkiCfg) (tc : Proto.TlsConn) (buf : Proto.Bytes) :
    Reactor.PkiWire.mtlsIdentity pcfg tc buf
      = authenticate pcfg.mtlsEnv pcfg.now (pcfg.chainOf tc buf)
          (pcfg.transcriptOf tc buf) (pcfg.cvSigOf tc buf) := rfl

/-- **CORRECTNESS on the reactor gate.**  The identity the running reactor's PKI
gate derives is `some id` **iff** the RFC 5280 specification holds of the
surfaced chain with `id` the leaf subject — the headline refinement transported
verbatim onto the deployed `Reactor.PkiWire.mtlsIdentity`. -/
theorem mtlsIdentity_correct
    (pcfg : Reactor.PkiWire.PkiCfg) (tc : Proto.TlsConn) (buf : Proto.Bytes)
    (id : Name) :
    Reactor.PkiWire.mtlsIdentity pcfg tc buf = some id
      ↔ AuthIdentity pcfg.mtlsEnv.anchors pcfg.mtlsEnv.verifySig pcfg.mtlsEnv.cvVerify
          pcfg.now (pcfg.chainOf tc buf)
          (pcfg.transcriptOf tc buf) (pcfg.cvSigOf tc buf) id := by
  rw [deployed_gate_eq_authenticate]
  exact authenticate_correct pcfg.mtlsEnv pcfg.now (pcfg.chainOf tc buf)
    (pcfg.transcriptOf tc buf) (pcfg.cvSigOf tc buf) id

/-- **CORRECTNESS on the reactor gate, bytes bound.**  The same refinement as
`mtlsIdentity_correct`, but with the transcript/signature inputs shown as what
they now *are* — the transcript hash and the **real RFC 8446 §4.4.3 parse** of the
CertificateVerify message (`PkiWire.parseCvSig`), both projected from the single
**state-derived** view `Reactor.PkiWire.clientAuthOfConn tc buf` (equal to
`pcfg.clientAuthOf tc buf`, which now ignores `pcfg`).  So the deployed identity is
`some id` iff the chain is an RFC 5280 valid path **and** the client's
CertificateVerify — the parsed wire signature — verifies under the leaf key over
the surfaced transcript.  The `cvSig`/`transcriptHash` are no longer opaque caller
values. -/
theorem mtlsIdentity_bound_correct
    (pcfg : Reactor.PkiWire.PkiCfg) (tc : Proto.TlsConn) (buf : Proto.Bytes)
    (id : Name) :
    Reactor.PkiWire.mtlsIdentity pcfg tc buf = some id
      ↔ AuthIdentity pcfg.mtlsEnv.anchors pcfg.mtlsEnv.verifySig pcfg.mtlsEnv.cvVerify
          pcfg.now (pcfg.chainOf tc buf)
          (Reactor.PkiWire.clientAuthOfConn tc buf).transcriptHash
          (Reactor.PkiWire.parseCvSig
            (Reactor.PkiWire.clientAuthOfConn tc buf).certVerifyMsg) id :=
  mtlsIdentity_correct pcfg tc buf id

/-- **CORRECTNESS on the reactor gate, bound to the live TLS connection state.**
The strongest form: the transcript hash and CertificateVerify signature are shown
as the extraction from the **full accumulated handshake transcript** the deployed
`Tls.St` carries — written out here as the state field itself,
`tc.st.transcript ++ buf` (`= Reactor.TlsWire.connHandshakeBytes tc buf` by
`connHandshakeBytes_eq`) — split by the real RFC 8446 §4 framing
(`Reactor.PkiWire.scanCV`).  `tc.st.transcript` is the running transcript
`Tls.step` accumulates across **every** received flight **and** the emitted
plaintext server flight (RFC 8446 §4.4.1 — the server flight's plaintext, formerly
dropped as sealed-only record bytes, is now interleaved via `Tls.HsOut.flightPlain`
at the step that sends it).  So the handshake-context prefix `scanCV` peels off — by
walking past the server's CertificateVerify to the **client's** — is the full
§4.4.1 transcript `ClientHello ‖ server flight ‖ client Certificate`, not the
retained second-flight tail nor the client flight alone.  So the deployed reactor
derives a client identity `some id` **iff** the presented chain is an RFC 5280 valid
path **and** the client's CertificateVerify — the signature `parseCvSig` reads out
of the client CertificateVerify message located in the connection's *own full
accumulated transcript* — verifies under the leaf key over the transcript hashed
(`Crypto.sha256`) from that same transcript's complete §4.4.1 handshake-context
prefix (client **and** server flights).  Nothing on the right is a caller value:
both byte strings are fixed functions of the live `Tls.St.transcript` and the
received bytes. -/
theorem mtlsIdentity_state_bound_correct
    (pcfg : Reactor.PkiWire.PkiCfg) (tc : Proto.TlsConn) (buf : Proto.Bytes)
    (id : Name) :
    Reactor.PkiWire.mtlsIdentity pcfg tc buf = some id
      ↔ AuthIdentity pcfg.mtlsEnv.anchors pcfg.mtlsEnv.verifySig pcfg.mtlsEnv.cvVerify
          pcfg.now (pcfg.chainOf tc buf)
          (Crypto.sha256 (TlsHandshake.ofBytes
            (Reactor.PkiWire.scanCV (tc.st.transcript ++ buf).length
              [] (tc.st.transcript ++ buf)).1))
          (Reactor.PkiWire.parseCvSig
            (Reactor.PkiWire.scanCV (tc.st.transcript ++ buf).length
              [] (tc.st.transcript ++ buf)).2) id :=
  mtlsIdentity_correct pcfg tc buf id

/-! ## No identity without a valid RFC 5280 path -/

/-- No identity is established from a chain that is not a valid RFC 5280 path
(independently of the CertificateVerify signature). -/
theorem no_identity_of_not_path (env : Env) (now : Time) (chain : Chain)
    (transcriptHash cvSig : ByteArray)
    (h : ¬ Rfc5280Path env.anchors env.verifySig now chain) :
    authenticate env now chain transcriptHash cvSig = none := by
  cases hr : authenticate env now chain transcriptHash cvSig with
  | none => rfl
  | some id =>
    obtain ⟨leaf, rest, hchain, hpath, _, _⟩ :=
      (authenticate_correct env now chain transcriptHash cvSig id).mp hr
    exact absurd (hchain ▸ hpath) h

/-! ## Non-vacuity witnesses

Concrete, kernel-evaluated evidence that the refinement is real: acceptance and
each mode of rejection are distinguished.  A trivial `spec := impl` renaming
could not separate these. -/

/-- A directly-trusted, self-issued CA root (subject/issuer name `0`), valid over
`[0, 100]`. -/
def rootCert : Cert := ⟨0, 0, 0, 100, true⟩

/-- An end-entity (leaf) certificate: subject `7`, issued by name `0`, not a CA,
valid over `[0, 100]`. -/
def leafCert : Cert := ⟨7, 0, 0, 100, false⟩

/-- A plausible certificate-signature boundary: a child is signed by an issuer
iff the child's issuer name equals the issuer's subject name. -/
def demoVerifySig (issuer child : Cert) : Bool :=
  decide (child.issuer = issuer.subject)

/-- A plausible CertificateVerify boundary: the client's proof-of-possession is
accepted iff a present (non-empty) signature was supplied — standing in for the
Ed25519 verify under the leaf key over the §4.4.3 content that the deployment
installs.  An absent (empty) signature is the classic bypass attempt: a valid
chain with no proof the peer holds the leaf private key. -/
def demoCvVerify (_leaf : Cert) (_content sig : ByteArray) : Bool := !sig.isEmpty

/-- A present, valid client CertificateVerify signature. -/
def goodCv : ByteArray := ByteArray.mk #[1]

/-- An absent/invalid client CertificateVerify signature. -/
def badCv : ByteArray := ByteArray.empty

/-- The handshake transcript hash the client CertificateVerify signs (an opaque
value here; the demo boundary does not inspect it). -/
def demoTranscript : ByteArray := ByteArray.mk #[9]

/-- The verification environment: the demo signature and CertificateVerify
boundaries, and a single trust anchor, the self-issued root. -/
def demoEnv : Env := ⟨demoVerifySig, demoCvVerify, [rootCert]⟩

/-- A valid chain at a valid time, with a present CertificateVerify, establishes
the leaf subject (`7`). -/
example :
    authenticate demoEnv 50 [leafCert, rootCert] demoTranscript goodCv = some 7 := by decide

/-- The same valid chain and CertificateVerify, but the check time is **past the
validity window** (expired) → no identity. -/
example :
    authenticate demoEnv 200 [leafCert, rootCert] demoTranscript goodCv = none := by decide

/-- An **unverified chain** — the leaf presented alone, terminating in a
non-anchor → no identity. -/
example :
    authenticate demoEnv 50 [leafCert] demoTranscript goodCv = none := by decide

/-- A chain whose leaf is **not signed by its issuer** (the link fails the
certificate-signature boundary) → no identity. -/
example :
    authenticate demoEnv 50 [⟨7, 999, 0, 100, false⟩, rootCert] demoTranscript goodCv = none := by
  decide

/-- **The proof-of-possession is really required — the closed bypass.**  A fully
valid RFC 5280 path at a valid time, but with an **absent/bad** client
CertificateVerify (`badCv`), yields **no** identity.  This is exactly the auth
bypass this check closes: a peer presenting any publicly-visible certificate chain
without holding the leaf private key is not authenticated. -/
example :
    authenticate demoEnv 50 [leafCert, rootCert] demoTranscript badCv = none := by decide

/-- …and the *only* difference from the accepting case is the CertificateVerify:
the same valid chain and time **with** a present CertificateVerify does
authenticate, so the rejection above is due precisely to the missing proof of
possession. -/
example :
    authenticate demoEnv 50 [leafCert, rootCert] demoTranscript goodCv = some 7 := by decide

/-- The refinement really constrains the deployed decision: a valid path with a
valid CertificateVerify yields exactly the leaf subject through the spec side. -/
example :
    AuthIdentity demoEnv.anchors demoEnv.verifySig demoEnv.cvVerify 50
      [leafCert, rootCert] demoTranscript goodCv 7 :=
  (authenticate_correct demoEnv 50 [leafCert, rootCert] demoTranscript goodCv 7).mp (by decide)

end Correct
end Mtls
