/-
# Dregg2.Authority.Credential — verifiable credentials as keys-as-caps (issue / present / verify / revoke).

A credential is a keys-as-caps attestation — a claim about a subject issued by an issuer over a
schema, carrying an `attestation : Proof` (a signature / STARK). A holder presents it; a verifier
admits it iff (a) the attestation passes the §8 oracle (`CryptoKernel.verify` — it was genuinely
issued) AND (b) the credential is not revoked (non-membership in the revocation set). Revocation is
the lone consensus seam: a negative discharge against an attested revocation root. Only root-epoch
agreement is global; everything else is local.

Load-bearing content:
- `VC = { issuer, schema, subject, claim, attestation }` with a content-addressed `id`;
- `issue`, `present`, `revoke` (insert id into revocation set), `verify` (issued ∧ not-revoked);
- keystone `credential_verifies_iff_issued_and_not_revoked` — both directions;
- `revoke_blocks_verify` — after revocation the credential no longer verifies;
- `revocation_is_iconfluent` — the no-loss invariant (every revoked id stays revoked) is I-confluent,
  reusing `Exec.NullifierCell`'s monotone invariant, so revocation needs only root-epoch agreement.

§8 boundary: the attestation's signature/STARK soundness is the `CryptoKernel.verify` oracle — never
a Lean law. This module proves the issue/present/verify/revoke discipline; the circuits prove the oracle binds.

Pure, computable, `#eval`-able. No `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.CryptoKernel
import Dregg2.Exec.NullifierCell

namespace Dregg2.Authority.Credential

open Dregg2.Crypto (CryptoKernel)
open Dregg2.Exec
open Dregg2.Privacy (Nullifier)

/-! ## The credential — a keys-as-caps attestation.

We make the descriptive fields (`issuer`, `schema`, `subject`, `claim`) plain `Nat` codes (the
content-addressed identifiers the real PI surface hashes); `attestation : Proof` is the §8
witness. The credential's `id` is content-addressed off its descriptive fields via the kernel's
`hash`, and revocation is membership of that id (projected to a `Nullifier` tag — the revocation
set REUSES the nullifier G-Set). -/

variable {Digest Proof : Type}

/-- **A `Credential`** — a signed/proven attestation: an `issuer` makes a `claim` about a
`subject` under a `schema`, and the `attestation : Proof` is what `CryptoKernel.verify` checks
against the issuer's statement. This is the VC / biscuit-block object of `dregg2 §3`: a
keys-as-caps credential whose authority is *the verifiable attestation*, not a bearer secret. -/
structure VC (Digest Proof : Type) where
  /-- The issuing authority's identifier (the public key / DID code). -/
  issuer : Nat
  /-- The schema the claim conforms to (the credential type). -/
  schema : Nat
  /-- The subject the claim is about (the holder / DID code). -/
  subject : Nat
  /-- The asserted claim payload (the attribute value code). -/
  claim : Nat
  /-- The §8 witness: the issuer's signature / STARK over the statement, checked by the oracle. -/
  attestation : Proof

/-- **The issuer's statement** — the `Digest` the attestation must discharge. It content-addresses
the *descriptive* tuple `(issuer, schema, subject, claim)` via the kernel's collision-resistant
`hash`. `CryptoKernel.verify (issuerStmt cred) cred.attestation` asks: "did `issuer` really attest
this claim about this subject under this schema?" — the §8 oracle, never a Lean law. -/
def issuerStmt [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (cred : VC Digest Proof) : Digest :=
  CryptoKernel.hash (Digest := Digest) (Proof := Proof)
    [cred.issuer, cred.schema, cred.subject, cred.claim]

/-- **The credential's content-addressed id**, projected to a `Nullifier` tag so the revocation set
can REUSE the nullifier G-Set (`Exec.NullifierCell`). The tag is the `Nat`-encoded descriptive
tuple — content-addressed, so a re-presented credential yields the *same* revocation id (exactly
the determinism the nullifier discipline relies on). -/
def credId (cred : VC Digest Proof) : Nullifier :=
  { tag := Nat.pair cred.issuer (Nat.pair cred.schema (Nat.pair cred.subject cred.claim)) }

/-! ## issue / present.

`issue` is the issuer's mint: given the descriptive tuple and an `attestation` the issuer has
produced over `issuerStmt`, assemble the credential. `present` is the holder's show: it is the
identity on the credential together with its attestation (the holder cannot forge the attestation,
only relay it) — the object the verifier receives. -/

/-- **`issue`** — an issuer mints a credential over `(subject, claim)` under `schema`, carrying the
`attestation` it produced. (Soundness — that `attestation` actually discharges `issuerStmt` — is
the §8 oracle's job, checked at `verify`; minting is just assembly.) -/
def issue (issuer schema subject claim : Nat) (attestation : Proof) :
    VC Digest Proof :=
  { issuer := issuer, schema := schema, subject := subject, claim := claim,
    attestation := attestation }

/-- **`present`** — a holder shows the credential (with its attestation) to a verifier. The holder
relays, never forges: presentation is the identity on the credential. -/
def present (cred : VC Digest Proof) : VC Digest Proof := cred

/-- Presentation preserves the issuer statement and id — what the holder shows is exactly what was
issued (no forgery seam introduced by presentation). PROVED. -/
@[simp] theorem present_issuerStmt [AddCommGroup Digest] [CryptoKernel Digest Proof] (cred : VC Digest Proof) :
    issuerStmt (present cred) = issuerStmt cred := rfl

@[simp] theorem present_credId (cred : VC Digest Proof) :
    credId (present cred) = credId cred := rfl

/-! ## The revocation set — the negative-discharge cell (REUSED from `Exec.NullifierCell`).

Revocation REUSES the nullifier G-Set wholesale: the revocation set IS a
`NullifierCell.Cell` (an append-only `Finset Nullifier`), revoked-ids are members, `revoke` is
`NullifierCell.spend` of the credential's id. Non-membership is the *negative discharge*. -/

/-- **The revocation set** is exactly the nullifier G-Set — an append-only `Finset` of revoked ids
(the attested revocation root, modelled as the live set). We DEFINE nothing new; revocation is the
nullifier discipline applied to credential ids. -/
abbrev RevocationSet := NullifierCell.Cell

/-- The empty revocation set — nothing revoked yet (the genesis root). -/
def noRevocations : RevocationSet := NullifierCell.empty

/-- **`isRevoked`** — is this credential's id in the revocation set? Decidable membership against
the live root (the `MerkleMembership` query). Its *negation* is the non-membership the verifier
demands — the negative discharge. -/
def isRevoked (rev : RevocationSet) (cred : VC Digest Proof) : Bool :=
  decide (credId cred ∈ rev.spent)

/-- **`revoke`** — add the credential's id to the revocation set. This is `NullifierCell.spend` of
the id: insert-only, fail-closed on a re-revocation (already-revoked ⇒ `none`). Grow-only: once
revoked, forever revoked. -/
def revoke (rev : RevocationSet) (cred : VC Digest Proof) : Option RevocationSet :=
  NullifierCell.spend rev (credId cred)

/-- **The total revoke** — the idempotent "ensure revoked" form (insert, absorbing a
re-revocation). Useful when the caller does not care whether the id was already present; the
verify-blocking content (`revoke_blocks_verify`) is stated on this total form so it never depends
on freshness. -/
def revoke! (rev : RevocationSet) (cred : VC Digest Proof) : RevocationSet :=
  { spent := insert (credId cred) rev.spent }

/-! ## verify — the keys-as-caps admissibility decision.

A presentation is **admissible** iff the §8 oracle accepts the attestation (it was issued) AND the
credential's id is *not* in the revocation set (the negative discharge holds). Fail-closed on
either leg. -/

/-- **`verify`** — the credential admissibility decision: admit iff `CryptoKernel.verify` accepts
the attestation against the issuer's statement (it was *issued*) AND the id is *not* revoked
(non-membership — the negative discharge). The conjunction is fail-closed: a bad attestation OR a
revocation each reject. -/
def verify [AddCommGroup Digest] [CryptoKernel Digest Proof] (rev : RevocationSet) (cred : VC Digest Proof) :
    Bool :=
  CryptoKernel.verify (issuerStmt cred) cred.attestation && !(isRevoked rev cred)

/-! ## THE KEYSTONE — `credential_verifies_iff_issued_and_not_revoked` (both directions). -/

/-- **THE KEYSTONE** — a presentation `verify`s iff issued-and-not-revoked. A credential is
admissible iff (a) its attestation passes the §8 oracle (`CryptoKernel.verify (issuerStmt cred)
cred.attestation = true`) AND (b) its id is not in the revocation set (`isRevoked = false`). Both
directions. Authority = a verifiable attestation that has not been revoked. -/
theorem credential_verifies_iff_issued_and_not_revoked [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (rev : RevocationSet) (cred : VC Digest Proof) :
    verify rev (present cred) = true
      ↔ (CryptoKernel.verify (issuerStmt cred) cred.attestation = true
          ∧ isRevoked rev cred = false) := by
  unfold verify present
  rw [Bool.and_eq_true, Bool.not_eq_true']

/-! ## `revoke_blocks_verify` — the negative discharge fires.

Once the id is in the revocation set, non-membership fails ⇒ `verify` rejects, *regardless* of the
attestation. Revocation = "non-membership becomes membership ⇒ rejected". REUSES the nullifier-set
membership (`Finset.mem_insert_self`). -/

/-- **`isRevoked` after `revoke!` is `true`** — the id we just revoked is now a member. The bridge
fact for `revoke_blocks_verify`, resting on `Finset.mem_insert_self`. PROVED. -/
theorem isRevoked_revoke! (rev : RevocationSet) (cred : VC Digest Proof) :
    isRevoked (revoke! rev cred) cred = true := by
  unfold isRevoked revoke!
  exact decide_eq_true (Finset.mem_insert_self _ _)

/-- **`revoke_blocks_verify`** — after revoking (total form), the credential no longer `verify`s
regardless of its attestation: non-membership becomes membership, the negative-discharge leg fails,
and the fail-closed `&&` rejects. Revocation is the consensus seam because this flip must be globally
agreed (root-epoch agreement). -/
theorem revoke_blocks_verify [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (rev : RevocationSet) (cred : VC Digest Proof) :
    verify (revoke! rev cred) (present cred) = false := by
  unfold verify present
  rw [isRevoked_revoke!]
  simp

/-- **Companion (PROVED): the un-revoked direction.** If the id is *not* revoked, `verify` is
governed entirely by the §8 oracle — it accepts iff the attestation does. So before any revocation,
the credential is admissible exactly when issued; revocation is the only thing that can take a
genuinely-issued credential out of admissibility. -/
theorem verify_unrevoked_iff_issued [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (rev : RevocationSet) (cred : VC Digest Proof)
    (h : isRevoked rev cred = false) :
    verify rev (present cred) = CryptoKernel.verify (issuerStmt cred) cred.attestation := by
  unfold verify present
  rw [h]
  simp

/-! ## `revocation_is_iconfluent` — revocation needs only root-epoch agreement.

The revocation set is the nullifier G-Set, so its I-confluence / tier-1-eligibility is REUSED
verbatim from `Exec.NullifierCell`. Two issuers can revoke disjoint credentials offline and union
their revocation roots with **no coordination beyond the root epoch** — the "lone consensus seam"
is the *narrowest* possible: grow-only, partition-tolerant. -/

/-- **`revocation_is_iconfluent`** (reused from `NullifierCell`). For any baseline `rev₀`,
the no-loss invariant "every credential revoked in `rev₀` is still revoked" (`fun s => rev₀ ⊆ s`)
is I-confluent: two issuers may revoke disjoint credentials offline and union their roots, and no
revocation is ever lost (upward-closed sets are union-stable). This is a falsifiable safety property
(a root that drops a revocation breaks it), NOT the trivial carrier. Hence revocation needs only
root-epoch agreement, not full consensus. -/
theorem revocation_is_iconfluent (rev₀ : Finset Nullifier) :
    Dregg2.Confluence.IConfluent (S := Finset Nullifier) (fun s => rev₀ ⊆ s) :=
  NullifierCell.nullifierSet_monotone_iconfluent rev₀

/-- **`revocation_tier1_eligible`** (reused from `NullifierCell`). The revocation cell may run
at tier-1 (causal-only, coordination-free, partition-tolerant) for the genuine no-loss safety
property `fun s => rev₀ ⊆ s`. Full-consensus cost is paid only at the root epoch; revocation
content merges freely without ever dropping a revocation. -/
theorem revocation_tier1_eligible (rev₀ : Finset Nullifier) :
    Dregg2.Confluence.Tier1Eligible (S := Finset Nullifier) (fun s => rev₀ ⊆ s) :=
  NullifierCell.nullifierCell_monotone_tier1_eligible rev₀

/-- **Non-vacuity of the revocation invariant.** A baseline that has revoked credential-id `n`
satisfies `{n} ⊆ {n}` but fails for an empty root — so `revocation_is_iconfluent` protects a
real, falsifiable property, not `True`. -/
theorem revocation_invariant_nontrivial (n : Nullifier) :
    ({n} ⊆ ({n} : Finset Nullifier)) ∧ ¬ ({n} ⊆ (∅ : Finset Nullifier)) :=
  NullifierCell.nullifierSet_monotone_invariant_nontrivial n

/-- **Merging two revocation roots** is the CvRDT union (the tier-1 join). No revocation is lost,
none invented — `NullifierCell.merge_preserves_membership` gives membership in the merge iff
membership in either root. REUSED. -/
def mergeRevocations (a b : RevocationSet) : RevocationSet := NullifierCell.merge a b

theorem mergeRevocations_membership (a b : RevocationSet) (cred : VC Digest Proof) :
    isRevoked (mergeRevocations a b) cred = (isRevoked a cred || isRevoked b cred) := by
  unfold isRevoked mergeRevocations NullifierCell.merge
  by_cases ha : credId cred ∈ a.spent <;> by_cases hb : credId cred ∈ b.spent <;>
    simp [Finset.mem_union, ha, hb]

/-! ## It runs (`#eval`) — issue, present+verify, revoke, re-present, and a forged attestation.

Instantiated at the **Reference CryptoKernel** (`Crypto.Reference` — `D := Int`, `P := Int`,
`verify stmt proof := decide (stmt = proof)`: a proof is valid iff it *echoes* the statement). So a
genuine attestation is `issuerStmt cred`; a forged one is anything else. This exercises the full
issue → present → verify → revoke → reject cascade WITHOUT Rust. -/

section Demo

open Dregg2.Crypto.Reference

/-- The issuer's genuine attestation over `(issuer, schema, subject, claim)`: under the Reference
kernel, a valid proof *is* the statement (`verify stmt proof = decide (stmt = proof)`). -/
private def goodAttestation (issuer schema subject claim : Nat) : Crypto.Reference.P :=
  issuerStmt (Digest := Crypto.Reference.D) (Proof := Crypto.Reference.P)
    { issuer := issuer, schema := schema, subject := subject, claim := claim, attestation := 0 }

/-- A genuinely-issued credential: subject 42, claim 7, under schema 1 by issuer 99. -/
private def goodCred : VC Crypto.Reference.D Crypto.Reference.P :=
  issue 99 1 42 7 (goodAttestation 99 1 42 7)

/-- A forged credential: same descriptive tuple, but a bogus attestation (does NOT echo the
statement), so the §8 oracle rejects it. -/
private def forgedCred : VC Crypto.Reference.D Crypto.Reference.P :=
  issue 99 1 42 7 (goodAttestation 99 1 42 7 + 1)   -- off-by-one ⇒ not the statement

/-- The genesis revocation set, pinned at the Reference types for the demo (`noRevocations` is
non-parametric, but pinning here keeps the `#eval`s' implicit `Digest`/`Proof` determined). -/
private def rev0 : RevocationSet := noRevocations

-- issue + present + verify a genuine credential ⇒ accepted
#eval verify rev0 (present goodCred)                                 -- true
-- revoke it, then present again ⇒ rejected (the negative discharge)
#eval verify (revoke! rev0 goodCred) (present goodCred)             -- false
-- a forged attestation (bad proof) ⇒ rejected by the §8 oracle even un-revoked
#eval verify rev0 (present forgedCred)                               -- false
-- the id really is in the revocation set after revoke!
#eval isRevoked (revoke! rev0 goodCred) goodCred                    -- true
-- and not before
#eval isRevoked rev0 goodCred                                       -- false
-- revoke via the partial (fresh) form succeeds, re-revoke fails-closed (insert-only)
#eval (revoke rev0 goodCred).isSome                                 -- true
#eval ((revoke rev0 goodCred).bind
        (fun r => revoke r goodCred)).isNone                         -- true (already revoked)

end Demo

end Dregg2.Authority.Credential
