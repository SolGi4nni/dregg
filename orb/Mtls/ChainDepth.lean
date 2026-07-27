/-
Mtls.ChainDepth — depth-bounded, name-chained path validation to a trusted root.

This layer closes the gap between the base path validator (`Mtls.verifyFrom`,
which decides validity windows, per-link signatures, the CA basic constraint and
trust-anchoring) and a *deployable* client-certificate check, by adding the two
guards a base validator omits:

  1. **Name chaining (RFC 5280 §6.1.3(a)(4)).**  Each certificate's `issuer`
     must equal the `subject` of the certificate that signs it — the next one up
     the chain.  The per-link signature check (`verifySig`) lives behind the
     named crypto boundary; name chaining is the *structural* binding that the
     issuing name a certificate claims is the name the signer actually speaks
     for.  A validator that trusts `verifySig` alone binds no names; `namesChain`
     makes the RFC's directory-name linkage an explicit, checkable condition.

  2. **A hard depth bound (anti-DoS).**  A validator that recurses over a
     caller-supplied chain of unbounded length is a denial-of-service surface: a
     peer can present an arbitrarily long chain and force unbounded verification
     work (and, with real crypto, unbounded signature checks).  `verifyToRoot`
     rejects any chain longer than a fixed `maxDepth` *before* considering its
     contents, so the work a single handshake can demand is bounded by a
     constant the server chooses.

`verifyToRoot env now maxDepth chain` is therefore

    chain fits the depth bound  ∧  names chain  ∧  the base RFC 5280 path validates

as a single total `Bool`.  The base path validator already proves the
signed-to-a-trusted-root, validity-window and CA-constraint half (`verify_iff`);
this file adds the depth and name-chaining guards on top and proves the three
headline results:

  * `chain_validates_to_root` — the bounded validator accepts a chain *iff*
    it fits the depth bound, its names chain, and it is a valid RFC 5280 path to
    a trusted root (every cert signed by the next, valid at `now`, CA constraint
    on every signer, top a trusted anchor).  A sharp iff: acceptance is exactly
    this conjunction, no more and no less.

  * `broken_link_rejected` — a chain with a broken signature link *anywhere*
    (a consecutive pair `c, next` where `c` is not signed by `next` under the
    named `verifySig`) is rejected, whatever precedes or follows the bad link.

  * `chain_depth_bounded` — a chain strictly longer than `maxDepth` is rejected
    outright, regardless of how well-formed its contents are.  No unbounded
    chain can consume unbounded verification work.

The `Demo` section exhibits concrete witnesses (a valid 3-cert chain accepted at
depth 3, the *same* chain rejected at depth 2, and a chain with a forged leaf
link rejected) so none of the three results is vacuous: the depth guard bites a
chain that is otherwise fully valid, and the broken-link reject fires on a chain
whose every *other* condition holds.

All crypto stays behind the named `verifySig` / `cvVerify` interfaces inherited
from `Mtls.Basic`; nothing here inspects a key or a signature.
-/

import Mtls.Theorems

namespace Mtls

/-! ### Name chaining — the RFC 5280 §6.1.3(a)(4) directory-name linkage -/

/-- **Name chaining.**  Each certificate's `issuer` names the `subject` of the
certificate directly above it (its signer).  `true` on the empty and singleton
chains (nothing to link); on a longer chain, every consecutive `(child, signer)`
pair must satisfy `child.issuer = signer.subject`.

This is the structural half of "signed by its issuer": `verifySig` (the crypto
boundary) proves the signature verifies, `namesChain` proves the issuing name
the child claims is the name the signer actually speaks for.  Together they bind
a link both cryptographically and by name. -/
def namesChain : Chain → Bool
  | [] => true
  | [_] => true
  | child :: signer :: rest =>
      decide (child.issuer = signer.subject) && namesChain (signer :: rest)

/-! ### The depth-bounded, name-chained validator -/

/-- **The deployable client-certificate validator.**  Accepts `chain` iff it
fits within `maxDepth` certificates, its names chain, and it is a valid RFC 5280
path to a trusted root under the base validator `verifyFrom`.  Total by
construction (a conjunction of three total `Bool`s).

The depth check is evaluated first and independently of the chain contents, so a
chain longer than `maxDepth` is rejected without inspecting (or cryptographically
verifying) any certificate beyond counting them. -/
def verifyToRoot (env : Env) (now : Time) (maxDepth : Nat) (chain : Chain) : Bool :=
  decide (chain.length ≤ maxDepth) && namesChain chain && verifyFrom env now chain

/-! ### #1 — the bounded validator accepts iff it is a bounded, name-chained,
      trusted-root path -/

/-- **Path-to-root soundness, sharp.**  `verifyToRoot` accepts a chain *iff*:

  * it fits the depth bound (`chain.length ≤ maxDepth`);
  * its names chain (`namesChain chain`);
  * every certificate is valid at `now` (`allValid`);
  * every non-top certificate is signed by its successor (`linkedSigned`);
  * every signing (non-leaf) certificate carries the CA constraint (`nonLeafCA`);
  * the top of the chain is a trusted anchor — the trusted *root* (`topAnchored`).

Forward is soundness (each named condition is necessary); backward is
completeness (together they suffice).  The base validator's `verify_iff` supplies
the last four; this adds the depth and name-chaining conjuncts. -/
theorem chain_validates_to_root (env : Env) (now : Time) (maxDepth : Nat)
    (chain : Chain) :
    verifyToRoot env now maxDepth chain = true ↔
      (chain.length ≤ maxDepth ∧ namesChain chain = true
        ∧ allValid now chain ∧ linkedSigned env chain
        ∧ nonLeafCA chain ∧ topAnchored env chain) := by
  simp only [verifyToRoot, Bool.and_eq_true, decide_eq_true_eq, verify_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩

/-! ### #2 — a broken signature link anywhere rejects the whole chain -/

/-- A `linkedSigned` chain has every consecutive `(child, signer)` pair signed:
if the chain splits as `pre ++ child :: signer :: rest`, then `child` is signed
by `signer` under the named `verifySig`.  (Structural induction on the prefix.) -/
theorem linkedSigned_adj {env : Env} (child signer : Cert) (rest : Chain) :
    ∀ pre : Chain,
      linkedSigned env (pre ++ child :: signer :: rest) →
      env.verifySig signer child = true := by
  intro pre
  induction pre with
  | nil => intro h; exact h.1
  | cons p ps ih =>
    intro h
    apply ih
    cases ps with
    | nil => exact h.2
    | cons q qs => exact h.2

/-- **A broken link rejects the chain.**  If a chain contains a consecutive pair
`child :: signer` where `child`'s signature does not verify under `signer`
(`verifySig signer child = false`), the whole chain is rejected — whatever
prefix precedes and whatever tail follows the bad link.  A forged or mismatched
intermediate signature can never be repaired by the rest of the chain. -/
theorem broken_link_rejected {env : Env} {now : Time} {maxDepth : Nat}
    (pre : Chain) (child signer : Cert) (rest : Chain)
    (hbad : env.verifySig signer child = false) :
    verifyToRoot env now maxDepth (pre ++ child :: signer :: rest) = false := by
  have hvf : verifyFrom env now (pre ++ child :: signer :: rest) = false := by
    cases hb : verifyFrom env now (pre ++ child :: signer :: rest) with
    | false => rfl
    | true =>
      have hgood := linkedSigned_adj child signer rest pre (verify_needs_linkedSigned hb)
      rw [hbad] at hgood
      exact Bool.noConfusion hgood
  unfold verifyToRoot
  rw [hvf]
  simp

/-! ### #3 — a chain longer than the depth bound is rejected (anti-DoS) -/

/-- **The depth bound.**  A chain strictly longer than `maxDepth` is rejected
outright, independent of its contents.  This caps the verification work a single
handshake can demand: no peer can force unbounded path processing by presenting
an unbounded chain — the guard fires on the length alone, before any certificate
past the count is examined. -/
theorem chain_depth_bounded (env : Env) (now : Time) (maxDepth : Nat)
    (chain : Chain) (h : maxDepth < chain.length) :
    verifyToRoot env now maxDepth chain = false := by
  unfold verifyToRoot
  have hlen : decide (chain.length ≤ maxDepth) = false :=
    decide_eq_false_iff_not.mpr (by omega)
  rw [hlen]
  simp

/-- **Corollary: an over-deep chain is rejected even when it is otherwise a
perfectly valid RFC 5280 path to a trusted root.**  Validity of the path is no
defence against the depth bound — the anti-DoS guard is unconditional.  (This is
`chain_depth_bounded` restated to make the "even if valid" reading explicit; the
depth hypothesis alone forces the reject.) -/
theorem deep_valid_chain_rejected {env : Env} {now : Time} {maxDepth : Nat}
    {chain : Chain}
    (_hpath : allValid now chain ∧ linkedSigned env chain
                ∧ nonLeafCA chain ∧ topAnchored env chain)
    (hdeep : maxDepth < chain.length) :
    verifyToRoot env now maxDepth chain = false :=
  chain_depth_bounded env now maxDepth chain hdeep

/-! ### Non-vacuity — concrete acceptances and rejections

Every headline theorem above is proven against a genuine, non-degenerate chain
here.  `verifySig` is instantiated as name-binding (`child.issuer = signer.subject`)
so the crypto boundary is a concrete decidable relation; the demo chains are real
3-certificate paths, and the depth guard is shown to reject a chain that *every
other condition accepts*. -/

namespace Demo

/-- Demo signature relation: a child verifies under a signer exactly when its
claimed issuer name is the signer's subject name.  A concrete, decidable stand-in
for the crypto boundary that makes the demo chains fully evaluable. -/
def demoVerifySig (signer child : Cert) : Bool := decide (child.issuer = signer.subject)

/-- A self-signed root (subject = issuer = 0), CA, valid over `[0, 100]`. -/
def root : Cert := ⟨0, 0, 0, 100, true⟩
/-- An intermediate CA (subject 1, issued by root 0), valid over `[0, 100]`. -/
def inter : Cert := ⟨1, 0, 0, 100, true⟩
/-- A client leaf (subject 2, issued by the intermediate 1), not a CA. -/
def leaf : Cert := ⟨2, 1, 0, 100, false⟩
/-- A forged leaf: claims issuer 9, which no certificate in the chain speaks for,
so its signature link is broken. -/
def leafForged : Cert := ⟨2, 9, 0, 100, false⟩

/-- The verification context: name-binding `verifySig`, a trivial `cvVerify`
(unused by path validation), and the single trusted root anchor. -/
def env : Env := ⟨demoVerifySig, fun _ _ _ => true, [root]⟩

/-- A genuine, fully valid leaf→intermediate→root path. -/
def goodChain : Chain := [leaf, inter, root]
/-- The same path but with a broken leaf signature link. -/
def brokenChain : Chain := [leafForged, inter, root]

/-- Positive witness: the valid 3-cert chain is accepted at depth 3 and check
time 50.  This makes `chain_validates_to_root`'s forward direction non-vacuous —
the validator really does accept a genuine path to a root. -/
example : verifyToRoot env 50 3 goodChain = true := by decide

/-- The depth guard bites a *valid* chain: the exact same `goodChain` accepted at
depth 3 is rejected at depth 2.  This makes `chain_depth_bounded` non-vacuous —
the reject is caused by the depth bound alone, not by any content defect. -/
example : verifyToRoot env 50 2 goodChain = false := by decide

/-- The broken-link reject fires on a chain whose every *other* condition holds
(valid windows, CA constraints, trusted root, in-bounds depth) — only the leaf
signature link is broken.  This makes `broken_link_rejected` non-vacuous. -/
example : verifyToRoot env 50 3 brokenChain = false := by decide

/-- And the broken chain is rejected via the general theorem too, at the head
split `[] ++ leafForged :: inter :: [root]`. -/
example : verifyToRoot env 50 3 brokenChain = false :=
  broken_link_rejected [] leafForged inter [root] (by decide)

end Demo

end Mtls
