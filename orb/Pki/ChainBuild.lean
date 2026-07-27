/-
# Pki.ChainBuild — X.509 certification path building & validation, verified.

RFC 5280 §6.1 defines the certification path validation algorithm: given an end-
entity ("leaf") certificate, a sequence of intermediate CA certificates, and a
store of trust anchors ("roots"), decide whether the leaf chains to a trusted
root. This module is the verified **decision logic** of that algorithm — the
path-building and constraint-checking half — over an abstract, honest model of
the cryptographic pieces.

The three structural obligations a valid path must satisfy (RFC 5280 §6.1.3):

  * **Signature chaining.** Each certificate is signed by the next certificate up
    the path (the leaf by an intermediate, each intermediate by the one above,
    the top by a trust anchor). The signature *check itself* is cryptography; we
    do NOT reinvent it. It is modeled as an **opaque oracle** `signatureValid
    parent child` — an uninterpreted total predicate whose outputs are never
    computed here, only threaded through as hypotheses. This is the faithful
    boundary: the proofs establish the path-building logic *around* a
    signature-verification primitive, never assuming anything about how it
    decides.
  * **Name chaining** (RFC 5280 §6.1.3(a)(4)). The `issuer` of each certificate
    equals the `subject` of the certificate that signed it.
  * **Basic constraints** (RFC 5280 §4.2.1.9 / §6.1.4(k)). Every certificate used
    as a CA — i.e. every non-leaf certificate in the path, and the trust anchor —
    must assert `basicConstraints: cA = TRUE`. A leaf presented as its own issuer
    must NOT be honored; the mutant below shows this check is load-bearing.

Plus temporal validity (RFC 5280 §6.1.3(a)(2)): every certificate on the path
must be within its `notBefore … notAfter` window at validation time `now`.

Headline theorems (core axioms only; the signature oracle is an opaque def, not
an axiom):

  * `chain_builds_to_root` — a leaf + intermediate that name-chain to a self-
    signed trusted root, all in-window, all CA flags set, and whose signatures
    verify under the oracle, is ACCEPTED. `chain_builds_to_root_example` pins it
    to concrete certificates so the only remaining hypotheses are the three
    opaque signature checks (maximally non-vacuous).
  * `chain_rejects_no_root` — a path whose terminal certificate is not a trusted
    root (not in the store, not self-signed, or not a CA) is REJECTED, for a path
    of ANY length.
  * `chain_rejects_expired` — a path containing ANY certificate outside its
    validity window at `now` is REJECTED.
  * `mutant_ca_is_load_bearing` / `mutant_noCA_accepts_forgery` — the mutant:
    dropping the basicConstraints CA check accepts a forged path through a non-CA
    "intermediate" that the real `verifyPath` rejects. Proves the CA constraint
    is not decorative.

Two soundness projections carry the weight:

  * `verifyPath_all_valid` — acceptance implies every certificate on the path is
    temporally valid.
  * `verifyPath_last_trusted` — acceptance implies the terminal certificate is a
    trusted root.
-/

namespace Pki.ChainBuild

/-! ## Model

Distinguished names, public keys, and times are abstract identifiers; the model
turns on the *relations* between them (name chaining, temporal ordering), not
their byte encodings, which are a separate parsing concern. -/

/-- A distinguished name (RFC 5280 §4.1.2.4/§4.1.2.6), abstractly an identifier.
Two certificates name-chain when one's `issuer` equals the other's `subject`. -/
abbrev Name := Nat

/-- A point in time (seconds since epoch, abstractly a `Nat`). -/
abbrev Time := Nat

/-- An X.509 certificate, reduced to the fields the path algorithm inspects. The
signature bytes and TBS encoding are abstracted behind the `signatureValid`
oracle, so no signature field appears here. -/
structure Cert where
  /-- The certificate's subject DN (RFC 5280 §4.1.2.6). -/
  subject   : Name
  /-- The issuing CA's DN (RFC 5280 §4.1.2.4); must equal the signer's `subject`. -/
  issuer    : Name
  /-- `basicConstraints: cA` (RFC 5280 §4.2.1.9): may this cert sign others? -/
  isCA      : Bool
  /-- Validity `notBefore` (RFC 5280 §4.1.2.5). -/
  notBefore : Time
  /-- Validity `notAfter` (RFC 5280 §4.1.2.5). -/
  notAfter  : Time
deriving DecidableEq, Repr

/-- **The opaque signature-verification oracle.** `signatureValid parent child`
means: `child`'s signature verifies under `parent`'s public key (RFC 5280
§6.1.3(a)(1)). This stands in for the real cryptographic primitive (RSA/ECDSA/
EdDSA). It is deliberately *uninterpreted*: this module proves nothing about how
signatures verify, only how the path algorithm composes the primitive's verdict.
As an `opaque` definition it contributes no axiom; its values enter proofs only
as explicit hypotheses. -/
opaque signatureValid : Cert → Cert → Bool

/-- Temporal validity (RFC 5280 §6.1.3(a)(2)): `now` is within the window. -/
def certValid (now : Time) (c : Cert) : Bool :=
  decide (c.notBefore ≤ now ∧ now ≤ c.notAfter)

/-- A single link `child → parent` up the path (RFC 5280 §6.1.3): `parent` signed
`child`, the names chain, and `parent` is a CA permitted to issue. -/
def linkOk (child parent : Cert) : Bool :=
  signatureValid parent child && (child.issuer == parent.subject) && parent.isCA

/-- The terminal certificate is an acceptable trust anchor (RFC 5280 §6.1.1(d)):
it is in the trust store, is a CA, is self-issued, and carries a valid self-
signature. `trusted` is the trust-store membership predicate over subject DNs. -/
def rootTrusted (trusted : Name → Bool) (root : Cert) : Bool :=
  trusted root.subject && root.isCA && (root.subject == root.issuer) &&
    signatureValid root root

/-- **Path validation.** A path is a list from leaf (head) to trust anchor
(last). The empty path has no anchor and is rejected; a singleton must be a
trusted root; otherwise the head must be in-window and link to the next, which is
itself a valid sub-path. -/
def verifyPath (now : Time) (trusted : Name → Bool) : List Cert → Bool
  | []          => false
  | [root]      => certValid now root && rootTrusted trusted root
  | c :: p :: t =>
      certValid now c && linkOk c p && verifyPath now trusted (p :: t)

/-! ## Unfolding lemmas (definitional; `rfl`) -/

@[simp] theorem verifyPath_nil (now trusted) :
    verifyPath now trusted [] = false := rfl

@[simp] theorem verifyPath_single (now trusted) (root : Cert) :
    verifyPath now trusted [root] = (certValid now root && rootTrusted trusted root) := rfl

@[simp] theorem verifyPath_cons_cons (now trusted) (c p : Cert) (t : List Cert) :
    verifyPath now trusted (c :: p :: t)
      = (certValid now c && linkOk c p && verifyPath now trusted (p :: t)) := rfl

/-! ## Soundness projections

Acceptance is a conjunction of local checks; these two lemmas extract the pieces
the rejection theorems need. -/

/-- **Soundness (temporal).** If a path is accepted, every certificate on it is
within its validity window at `now`. RFC 5280 §6.1.3(a)(2). -/
theorem verifyPath_all_valid (now : Time) (trusted : Name → Bool) :
    ∀ chain : List Cert, verifyPath now trusted chain = true →
      ∀ c ∈ chain, certValid now c = true := by
  intro chain
  induction chain with
  | nil => intro h; simp at h
  | cons c rest ih =>
      cases rest with
      | nil =>
          intro h d hd
          rw [verifyPath_single] at h
          have hc := (Bool.and_eq_true _ _).mp h |>.1
          rcases List.mem_singleton.mp hd with rfl
          exact hc
      | cons p t =>
          intro h d hd
          rw [verifyPath_cons_cons] at h
          obtain ⟨h12, hrest⟩ := (Bool.and_eq_true _ _).mp h
          obtain ⟨hc, _⟩ := (Bool.and_eq_true _ _).mp h12
          rcases List.mem_cons.mp hd with rfl | htl
          · exact hc
          · exact ih hrest d htl

/-- **Soundness (trust anchor).** If a path (of any length) ending in `root` is
accepted, then `root` is a trusted anchor. RFC 5280 §6.1.1(d)/§6.1.4. -/
theorem verifyPath_last_trusted (now : Time) (trusted : Name → Bool) :
    ∀ (chain : List Cert) (root : Cert),
      verifyPath now trusted (chain ++ [root]) = true → rootTrusted trusted root = true := by
  intro chain
  induction chain with
  | nil =>
      intro root h
      rw [List.nil_append, verifyPath_single] at h
      exact (Bool.and_eq_true _ _).mp h |>.2
  | cons c rest ih =>
      intro root h
      cases rest with
      | nil =>
          rw [List.cons_append, List.nil_append, verifyPath_cons_cons] at h
          obtain ⟨_, hrest⟩ := (Bool.and_eq_true _ _).mp h
          rw [verifyPath_single] at hrest
          exact (Bool.and_eq_true _ _).mp hrest |>.2
      | cons p t =>
          rw [List.cons_append, List.cons_append, verifyPath_cons_cons] at h
          obtain ⟨_, hrest⟩ := (Bool.and_eq_true _ _).mp h
          apply ih root
          rw [List.cons_append]
          exact hrest

/-! ## Headline theorems -/

/-- **`chain_builds_to_root`.** A leaf and an intermediate that name-chain to a
self-signed, trusted, in-window root — with every non-leaf carrying `cA = TRUE`
and every signature verifying under the oracle — is ACCEPTED. RFC 5280 §6.1. -/
theorem chain_builds_to_root
    (now : Time) (trusted : Name → Bool) (leaf int root : Cert)
    (hv_leaf : certValid now leaf = true)
    (hv_int  : certValid now int = true)
    (hv_root : certValid now root = true)
    (hlink1  : (leaf.issuer == int.subject) = true)
    (hca_int : int.isCA = true)
    (hlink2  : (int.issuer == root.subject) = true)
    (hca_root : root.isCA = true)
    (hself   : (root.subject == root.issuer) = true)
    (htrust  : trusted root.subject = true)
    (hsig1   : signatureValid int leaf = true)
    (hsig2   : signatureValid root int = true)
    (hsigr   : signatureValid root root = true) :
    verifyPath now trusted [leaf, int, root] = true := by
  simp only [verifyPath_cons_cons, verifyPath_single, linkOk, rootTrusted,
    hv_leaf, hv_int, hv_root, hlink1, hca_int, hlink2, hca_root, hself, htrust,
    hsig1, hsig2, hsigr, Bool.and_true, Bool.true_and, Bool.and_self]

/-- **`chain_rejects_no_root`.** A path whose terminal certificate is not a
trusted anchor (`rootTrusted … = false`: absent from the store, not self-issued,
or not a CA) is REJECTED — no length of valid links can rescue it. -/
theorem chain_rejects_no_root
    (now : Time) (trusted : Name → Bool) (chain : List Cert) (root : Cert)
    (hno : rootTrusted trusted root = false) :
    verifyPath now trusted (chain ++ [root]) = false := by
  cases hv : verifyPath now trusted (chain ++ [root]) with
  | false => rfl
  | true =>
      have := verifyPath_last_trusted now trusted chain root hv
      rw [this] at hno
      exact absurd hno (by decide)

/-- **`chain_rejects_expired`.** A path containing ANY certificate outside its
validity window at `now` is REJECTED (contrapositive of the temporal soundness
projection). RFC 5280 §6.1.3(a)(2). -/
theorem chain_rejects_expired
    (now : Time) (trusted : Name → Bool) (chain : List Cert) (c : Cert)
    (hmem : c ∈ chain) (hexp : certValid now c = false) :
    verifyPath now trusted chain = false := by
  cases hv : verifyPath now trusted chain with
  | false => rfl
  | true =>
      have := verifyPath_all_valid now trusted chain hv c hmem
      rw [this] at hexp
      exact absurd hexp (by decide)

/-! ## Concrete witnesses (non-vacuity)

Ground certificates so the structural obligations discharge by computation and
the *only* remaining hypotheses are the opaque signature checks. -/

/-- Leaf: subject DN 1, issued by DN 2, not a CA, window [0,100]. -/
def rLeaf : Cert := { subject := 1, issuer := 2, isCA := false, notBefore := 0, notAfter := 100 }
/-- Intermediate CA: subject DN 2, issued by DN 3, `cA = TRUE`. -/
def rInt  : Cert := { subject := 2, issuer := 3, isCA := true,  notBefore := 0, notAfter := 100 }
/-- Root CA: self-issued DN 3, `cA = TRUE`. -/
def rRoot : Cert := { subject := 3, issuer := 3, isCA := true,  notBefore := 0, notAfter := 100 }
/-- Trust store containing exactly DN 3. -/
def rTrusted : Name → Bool := fun n => n == 3

/-- **`chain_builds_to_root_example`.** The general theorem instantiated at
concrete certificates: with the store, names, CA flags, and windows all fixed,
acceptance rests solely on the three opaque signature verdicts. Demonstrates the
hypotheses of `chain_builds_to_root` are jointly satisfiable (non-vacuous). -/
theorem chain_builds_to_root_example
    (hsig1 : signatureValid rInt rLeaf = true)
    (hsig2 : signatureValid rRoot rInt = true)
    (hsigr : signatureValid rRoot rRoot = true) :
    verifyPath 50 rTrusted [rLeaf, rInt, rRoot] = true := by
  have hv_leaf : certValid 50 rLeaf = true := by decide
  have hv_int  : certValid 50 rInt  = true := by decide
  have hv_root : certValid 50 rRoot = true := by decide
  exact chain_builds_to_root 50 rTrusted rLeaf rInt rRoot
    hv_leaf hv_int hv_root (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hsig1 hsig2 hsigr

/-! ## The mutant: basicConstraints CA is load-bearing

A forged path routes the leaf through a non-CA "intermediate" (`fInt.isCA =
false`). The real `verifyPath` rejects it (`linkOk` demands the issuer be a CA);
a mutant validator that drops the CA check accepts the forgery. -/

/-- Forged leaf, issued by the non-CA DN 2. -/
def fLeaf : Cert := { subject := 1, issuer := 2, isCA := false, notBefore := 0, notAfter := 100 }
/-- A NON-CA certificate illegitimately used as an issuer (`cA = FALSE`). -/
def fInt  : Cert := { subject := 2, issuer := 3, isCA := false, notBefore := 0, notAfter := 100 }
/-- Legitimate self-signed root. -/
def fRoot : Cert := { subject := 3, issuer := 3, isCA := true,  notBefore := 0, notAfter := 100 }

/-- Mutant link check: identical to `linkOk` but WITHOUT the `parent.isCA`
basicConstraints requirement — the bug. -/
def linkOkNoCA (child parent : Cert) : Bool :=
  signatureValid parent child && (child.issuer == parent.subject)

/-- Mutant validator: `verifyPath` with `linkOkNoCA` in place of `linkOk`. -/
def verifyPathNoCA (now : Time) (trusted : Name → Bool) : List Cert → Bool
  | []          => false
  | [root]      => certValid now root && rootTrusted trusted root
  | c :: p :: t =>
      certValid now c && linkOkNoCA c p && verifyPathNoCA now trusted (p :: t)

/-- **`mutant_ca_is_load_bearing`.** The real validator REJECTS the forged path:
`fInt` is presented as `fLeaf`'s issuer but carries `cA = FALSE`, so `linkOk`
fails regardless of the (opaque) signature. -/
theorem mutant_ca_is_load_bearing :
    verifyPath 50 rTrusted [fLeaf, fInt, fRoot] = false := by
  simp only [verifyPath_cons_cons, linkOk, fInt, Bool.and_false, Bool.false_and]

/-- **`mutant_noCA_accepts_forgery`.** The mutant (CA check dropped) ACCEPTS the
exact forged path the real validator rejects — the difference is entirely the
basicConstraints check, so it is load-bearing. -/
theorem mutant_noCA_accepts_forgery
    (hsig1 : signatureValid fInt fLeaf = true)
    (hsig2 : signatureValid fRoot fInt = true)
    (hsigr : signatureValid fRoot fRoot = true) :
    verifyPathNoCA 50 rTrusted [fLeaf, fInt, fRoot] = true := by
  have hv_leaf : certValid 50 fLeaf = true := by decide
  have hv_int  : certValid 50 fInt  = true := by decide
  have hv_root : certValid 50 fRoot = true := by decide
  have hn1 : (fLeaf.issuer == fInt.subject) = true := by decide
  have hn2 : (fInt.issuer == fRoot.subject) = true := by decide
  have hself : (fRoot.subject == fRoot.issuer) = true := by decide
  have htr : rTrusted fRoot.subject = true := by decide
  have hca : fRoot.isCA = true := by decide
  simp only [verifyPathNoCA, linkOkNoCA, rootTrusted,
    hv_leaf, hv_int, hv_root, hn1, hn2, hself, htr, hca,
    hsig1, hsig2, hsigr, Bool.and_true, Bool.true_and, Bool.and_self]

/-! ## The runtime instance: an oracle-PARAMETERIZED path validator.

The theorems above reason about `verifyPath`, whose signature check is the
`opaque signatureValid` — the faithful abstract boundary. To actually RUN the
algorithm the verified TLS client (`TlsClient`) needs the SAME decision logic
with the signature verdict supplied by the real, audited primitive
(`Crypto.ecdsaP256Verify` / `Crypto.rsaPssVerify` — HACL* — or
`Crypto.rsaPkcs1Verify` — audited aws-lc — over each certificate's
TBSCertificate, dispatched by the child's `signatureAlgorithm`). `verifyPathW` is
exactly `verifyPath` with the oracle hoisted to a parameter:
`verifyPath = verifyPathW signatureValid` definitionally (`verifyPath_eq_W`), so
every abstract theorem above is the `signatureValid` instance of a fact about
`verifyPathW`, while the client instantiates the same function at the audited
oracle. The path-building LOGIC is verified once; only the signature verdict
changes hands to the audited crypto. -/

/-- Oracle-parameterized `linkOk`: `sig parent child` is the supplied signature
verdict (the runtime passes the real HACL* check over `child`'s TBSCertificate
under `parent`'s public key). -/
def linkOkW (sig : Cert → Cert → Bool) (child parent : Cert) : Bool :=
  sig parent child && (child.issuer == parent.subject) && parent.isCA

/-- Oracle-parameterized `rootTrusted`. -/
def rootTrustedW (sig : Cert → Cert → Bool) (trusted : Name → Bool) (root : Cert) : Bool :=
  trusted root.subject && root.isCA && (root.subject == root.issuer) && sig root root

/-- **Oracle-parameterized path validation** — the runnable form of `verifyPath`. -/
def verifyPathW (sig : Cert → Cert → Bool) (now : Time) (trusted : Name → Bool) :
    List Cert → Bool
  | []          => false
  | [root]      => certValid now root && rootTrustedW sig trusted root
  | c :: p :: t =>
      certValid now c && linkOkW sig c p && verifyPathW sig now trusted (p :: t)

@[simp] theorem verifyPathW_single (sig now trusted) (root : Cert) :
    verifyPathW sig now trusted [root]
      = (certValid now root && rootTrustedW sig trusted root) := rfl

@[simp] theorem verifyPathW_cons_cons (sig now trusted) (c p : Cert) (t : List Cert) :
    verifyPathW sig now trusted (c :: p :: t)
      = (certValid now c && linkOkW sig c p && verifyPathW sig now trusted (p :: t)) := rfl

/-- `verifyPath` is `verifyPathW` at the opaque oracle — so the abstract theorems
above are its `signatureValid` instance, and the runtime uses the same logic at a
real oracle. -/
theorem verifyPath_eq_W (now : Time) (trusted : Name → Bool) (chain : List Cert) :
    verifyPath now trusted chain = verifyPathW signatureValid now trusted chain := by
  induction chain with
  | nil => rfl
  | cons c rest ih =>
      cases rest with
      | nil => rfl
      | cons p t => simp only [verifyPath_cons_cons, verifyPathW_cons_cons,
                     linkOk, linkOkW, ih]

/-- **Soundness (temporal), parameterized.** Acceptance ⟹ every certificate on
the path is in-window — independent of the oracle. -/
theorem verifyPathW_all_valid (sig : Cert → Cert → Bool) (now : Time)
    (trusted : Name → Bool) :
    ∀ chain : List Cert, verifyPathW sig now trusted chain = true →
      ∀ c ∈ chain, certValid now c = true := by
  intro chain
  induction chain with
  | nil => intro h; simp [verifyPathW] at h
  | cons c rest ih =>
      cases rest with
      | nil =>
          intro h d hd
          rw [verifyPathW_single] at h
          have hc := (Bool.and_eq_true _ _).mp h |>.1
          rcases List.mem_singleton.mp hd with rfl
          exact hc
      | cons p t =>
          intro h d hd
          rw [verifyPathW_cons_cons] at h
          obtain ⟨h12, hrest⟩ := (Bool.and_eq_true _ _).mp h
          obtain ⟨hc, _⟩ := (Bool.and_eq_true _ _).mp h12
          rcases List.mem_cons.mp hd with rfl | htl
          · exact hc
          · exact ih hrest d htl

/-- **Soundness (trust anchor), parameterized.** Acceptance of a path ending in
`root` ⟹ `root` is a trusted anchor whose self-signature verified under the
supplied oracle (`rootTrustedW sig`). -/
theorem verifyPathW_last_trusted (sig : Cert → Cert → Bool) (now : Time)
    (trusted : Name → Bool) :
    ∀ (chain : List Cert) (root : Cert),
      verifyPathW sig now trusted (chain ++ [root]) = true →
      rootTrustedW sig trusted root = true := by
  intro chain
  induction chain with
  | nil =>
      intro root h
      rw [List.nil_append, verifyPathW_single] at h
      exact (Bool.and_eq_true _ _).mp h |>.2
  | cons c rest ih =>
      intro root h
      cases rest with
      | nil =>
          rw [List.cons_append, List.nil_append, verifyPathW_cons_cons] at h
          obtain ⟨_, hrest⟩ := (Bool.and_eq_true _ _).mp h
          rw [verifyPathW_single] at hrest
          exact (Bool.and_eq_true _ _).mp hrest |>.2
      | cons p t =>
          rw [List.cons_append, List.cons_append, verifyPathW_cons_cons] at h
          obtain ⟨_, hrest⟩ := (Bool.and_eq_true _ _).mp h
          apply ih root
          rw [List.cons_append]
          exact hrest

/-- Every adjacent `child → parent` link on a path has its signature verified. -/
def allLinksSigned (sig : Cert → Cert → Bool) : List Cert → Bool
  | []          => true
  | [_]         => true
  | c :: p :: t => sig p c && allLinksSigned sig (p :: t)

/-- **Soundness (signatures), parameterized — the load-bearing anti-MITM fact.**
Acceptance ⟹ EVERY adjacent link's signature verified under the supplied oracle.
Composed with `Crypto.ecdsaP256Verify_authentic` / `rsaPssVerify_authentic` /
`rsaPkcs1Verify_authentic` at the client, this says: an accepted chain is one where each certificate was genuinely
signed by the next — so a MITM's self-presented leaf, whose signature does not
verify under the pinned issuer's key, cannot be accepted. -/
theorem verifyPathW_links_signed (sig : Cert → Cert → Bool) (now : Time)
    (trusted : Name → Bool) :
    ∀ chain : List Cert, verifyPathW sig now trusted chain = true →
      allLinksSigned sig chain = true := by
  intro chain
  induction chain with
  | nil => intro h; simp [verifyPathW] at h
  | cons c rest ih =>
      cases rest with
      | nil => intro _; rfl
      | cons p t =>
          intro h
          rw [verifyPathW_cons_cons] at h
          obtain ⟨h12, hrest⟩ := (Bool.and_eq_true _ _).mp h
          obtain ⟨_, hlink⟩ := (Bool.and_eq_true _ _).mp h12
          have hsig : sig p c = true := by
            unfold linkOkW at hlink
            exact (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hlink).1 |>.1
          show (sig p c && allLinksSigned sig (p :: t)) = true
          rw [hsig, ih hrest]; rfl

end Pki.ChainBuild
