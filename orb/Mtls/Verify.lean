/-
Mtls — path validation and identity extraction.

`verifyFrom env now chain` is the total certificate-path validator: a single
`Bool`-valued structural recursion over the leaf-first chain.  It threads the
four path-validation conditions through the chain in one pass:

  * every certificate is inside its validity window at `now`;
  * every non-top certificate is signed (under the named `verifySig`) by its
    successor — the next certificate up the chain;
  * every certificate that *signs* another (i.e. every non-leaf certificate)
    carries the CA basic constraint;
  * the top of the chain is a member of the trust-anchor set.

The four declarative predicates (`allValid`, `linkedSigned`, `nonLeafCA`,
`topAnchored`) name those same conditions independently of the recursion; the
`Theorems` file proves `verifyFrom` is *exactly* their conjunction.

`authenticate` layers identity extraction on top.  Two independent proofs must
succeed before an identity is established:

  * the RFC 5280 §6.1 certificate path validates (`verifyFrom`); and
  * the client's RFC 8446 §4.4.3 `CertificateVerify` signature verifies under
    the leaf (end-entity) certificate's public key over the transcript-derived
    content (`env.cvVerify leaf (clientCertVerifyContent transcriptHash) cvSig`).

A verified path proves the presented certificates chain to a trust anchor; the
CertificateVerify proves the peer holds the leaf's *private key*.  Without the
second check a client presenting any publicly-visible certificate chain would be
authenticated as that identity without proving possession — an auth bypass.  A
verified chain with an absent or bad CertificateVerify therefore yields **no**
identity; anything else yields no identity too.  There is no path from a failed
verification to an identity — the no-bypass property.
-/

import Mtls.Basic

namespace Mtls

/-- The top of the chain (the element that must be a trusted anchor): the last
certificate, mirroring `verifyFrom`'s recursion so proofs share one shape.
`none` for the empty chain. -/
def topOf : Chain → Option Cert
  | [] => none
  | [c] => some c
  | _ :: next :: rest => topOf (next :: rest)

/-- **The path validator.**  Total by construction; each recursive call is on a
structural sub-chain, and the empty chain is a clean reject.

  * `[]`            — no chain: reject.
  * `[top]`         — a single certificate authenticates iff it is valid at
                      `now` and is itself a trusted anchor (a directly-trusted,
                      possibly self-issued, cert).  No CA constraint is imposed
                      on a lone leaf.
  * `c :: next ::…` — `c` must be valid at `now`, signed by its issuer `next`
                      (`verifySig next c`), and `next` — a signing, hence
                      non-leaf, certificate — must carry the CA constraint;
                      then recurse on the remainder. -/
def verifyFrom (env : Env) (now : Time) : Chain → Bool
  | [] => false
  | [top] => top.validAt now && decide (top ∈ env.anchors)
  | c :: next :: rest =>
      c.validAt now && env.verifySig next c && next.isCA
        && verifyFrom env now (next :: rest)

/-! ### The four named path-validation conditions

Stated declaratively, independent of `verifyFrom`.  `Theorems` proves the
validator accepts a chain iff all four hold. -/

/-- Every certificate is inside its validity window at the check time. -/
def allValid (now : Time) (chain : Chain) : Prop :=
  ∀ c ∈ chain, c.validAt now = true

/-- Every certificate except the top is signed, under the named `verifySig`, by
its successor (the next certificate up the chain). -/
def linkedSigned (env : Env) : Chain → Prop
  | [] => True
  | [_] => True
  | c :: next :: rest =>
      env.verifySig next c = true ∧ linkedSigned env (next :: rest)

/-- Every non-leaf certificate — every certificate that signs another, i.e. the
whole chain except the leaf head — carries the CA basic constraint. -/
def nonLeafCA : Chain → Prop
  | [] => True
  | _ :: rest => ∀ c ∈ rest, c.isCA = true

/-- The top of the chain is a member of the trust-anchor set (in particular the
chain is non-empty). -/
def topAnchored (env : Env) (chain : Chain) : Prop :=
  ∃ top, topOf chain = some top ∧ top ∈ env.anchors

/-! ### Identity extraction -/

/-- **Identity extraction.**  An identity is established for the leaf
(client-certificate) subject **iff both** the RFC 5280 §6.1 path validates
(`verifyFrom`) **and** the client's RFC 8446 §4.4.3 `CertificateVerify`
signature `cvSig` verifies under the leaf certificate's public key over the
transcript-derived content (proof of possession of the leaf private key).
`transcriptHash` is the handshake transcript hash and `cvSig` the client's
CertificateVerify signature, both surfaced from the handshake.  An unverified or
empty chain — or a chain whose CertificateVerify is absent or bad — yields no
identity.  There is no branch from a failed check to `some`: authentication
cannot be bypassed, and possession of the leaf private key is required. -/
def authenticate (env : Env) (now : Time) (chain : Chain)
    (transcriptHash cvSig : ByteArray) : Option Name :=
  match chain with
  | [] => none
  | leaf :: rest =>
      if verifyFrom env now (leaf :: rest)
          && env.cvVerify leaf (clientCertVerifyContent transcriptHash) cvSig
      then some leaf.subject else none

end Mtls
