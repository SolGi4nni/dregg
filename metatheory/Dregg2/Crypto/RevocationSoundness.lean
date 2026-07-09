/-
# `Dregg2.Crypto.RevocationSoundness` — REVOCATION SOUNDNESS, the last protocol game, closing the
crypto tree into ONE connected proof.

`CapabilityChain.lean` rode the hybrid-signature keystone to prove credential attenuation soundness.
This file rides it — and the Merkle tree's collision-resistance carrier `HashCR` — to prove the
revocation guarantee `token/src/revocation.rs` (GAP #5) leans on: **you cannot pass a revoked token off
as un-revoked**. A service provider maintains a Merkle tree over the revoked token-ids; the ROOT is
signed by the revocation authority (`AttestedRevocationRoot`, the hybrid ed25519 ∧ ML-DSA attestation);
a client checks non-revocation against an attested root by presenting a (sorted-Merkle) *absence*
witness against that root.

A forged non-revocation of a genuinely-revoked id has exactly TWO doors, and both are closed by a named
carrier already in the tree:

* **Break the Merkle binding** — present an absence witness against the *honestly-attested* root that
  omits a revoked id. Under `HashCR` (the tree's collision-resistance carrier, reused verbatim from
  `HermineHintMLWE`) a root determines its member set (`merkle_root_binds`), so an absence witness
  against the true root opens it to the true revoked set — which *contains* the id. Hiding a revocation
  is exactly a hash collision (`revoked_cannot_prove_absence`).

* **Forge the authority's attestation** — get the client to accept a root the authority never signed.
  An `AttestedRoot` accepted under the enrolled authority key but never signed IS a
  `SigScheme.Forgery` on that key (`forged_attestation_is_a_signature_forgery`), refuting the
  authority's `EufCma`.

So revocation soundness reduces to `HashCR ∨ EufCma`, and — because the attestation is the HYBRID
signature — `EufCma` is discharged by `HybridCombiner.hybrid_secure_if_either_floor` down to
`SchnorrDLHard ∨ MSISHard` (`revocation_sound_under_floor`). No named-carrier laundering: the ONLY
irreducible objects are the tree's `HashCR` and the discrete-log / Module-SIS floors; the forking
reductions are hypotheses (theorems of the existing forking machinery), never carriers.

## Modelling notes (honest boundaries).

* **The tree's hash is abstract, via `HashCR`.** We reuse `HermineHintMLWE.CommitReveal`/`HashCR`
  verbatim: a `CommitReveal Unit (Finset Id) Digest` whose `H () s` is the Merkle root of the revoked
  set `s`. `HashCR` = injectivity of that map on the committed domain — exactly "a collision-resistant
  Merkle root binds its member set". This is the honest abstraction of `SortedRevocationTree::root`
  (the blake3 fold): the whole point of the collision-resistant fold is that distinct sets get distinct
  roots. No lower-level Merkle-path structure is needed for the *binding* the soundness rests on.
* **Non-revocation = a valid absence witness.** The client accepts `id` as NOT-revoked against a root
  iff an absence witness verifies: an opening of the root to a member set `s` (`H () s = root`) with
  `id ∉ s` — the denotational content of the sorted-Merkle `NonMembershipProof`
  (`verify_non_membership`). We pick the absence witness (not "no membership proof exists") because it
  is what the adversary actually presents and what makes the binding soundness clean and non-vacuous.
* **The attestation is a `SigScheme` signature over `(root ‖ epoch)`.** `verifyAttested` is the
  `SigScheme.verify` of `HybridCombiner`, reused verbatim. The epoch rides *inside* the signed body, so
  cross-epoch replay of a stale root is a forgery (`wrong_root_for_epoch_is_forgery`).

Mirrors `CapabilityChain.lean`'s style throughout (the `honestDelegation` invariant becomes
`HonestAttestation`; the toy `SigScheme` teeth become the toy attestation teeth).
-/
import Dregg2.Crypto.HybridCombiner
import Dregg2.Crypto.HermineHintMLWE
import Dregg2.Tactics
import Mathlib.Data.Finset.Basic

namespace Dregg2.Crypto.RevocationSoundness

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.HermineHintMLWE
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField

variable {SK PK Msg Sig : Type*}
variable {Id Digest Epoch : Type*}

/-! ## The Merkle model — a collision-resistant root committing the revoked-id set.

`tree : CommitReveal Unit (Finset Id) Digest` is the revocation tree: `tree.H () s` is the Merkle root
of the revoked set `s` (the single `Unit` index = one whole-tree commitment). Its collision-resistance
is `HashCR tree` — reused verbatim from `HermineHintMLWE`, the ONLY hash carrier this file invokes. -/

/-- **`Members tree root id`** — a Merkle *membership* proof for `id` against `root`: an opening of the
root to a revoked set containing `id`. The witness is the set; the ZK/Merkle proof realizes the
existential. -/
def Members (tree : CommitReveal Unit (Finset Id) Digest) (root : Digest) (id : Id) : Prop :=
  ∃ s : Finset Id, tree.H () s = root ∧ id ∈ s

/-- **`Absent tree root id`** — a Merkle *absence* (non-membership) witness for `id` against `root`: an
opening of the root to a revoked set NOT containing `id`. The client accepts `id` as un-revoked against
`root` iff `Absent tree root id`. The denotational content of `verify_non_membership`. -/
def Absent (tree : CommitReveal Unit (Finset Id) Digest) (root : Digest) (id : Id) : Prop :=
  ∃ s : Finset Id, tree.H () s = root ∧ id ∉ s

/-! ### Merkle binding — a root determines its member set. -/

/-- **`merkle_root_binds`.** Under `HashCR`, equal roots force equal member sets: the root is a binding
commitment to the revoked set. This is exactly `HashCR` on the committed domain. -/
theorem merkle_root_binds (tree : CommitReveal Unit (Finset Id) Digest) (hcr : HashCR tree)
    (s s' : Finset Id) (h : tree.H () s = tree.H () s') : s = s' :=
  hcr () s s' h

/-- **Distinct member sets with the same root ARE a hash collision** — the contrapositive of
`merkle_root_binds`: two different revoked sets hashing to one root break `HashCR`. -/
theorem distinct_sets_collide (tree : CommitReveal Unit (Finset Id) Digest)
    (s s' : Finset Id) (hne : s ≠ s') (h : tree.H () s = tree.H () s') : ¬ HashCR tree :=
  fun hcr => hne (merkle_root_binds tree hcr s s' h)

/-- **`revoked_cannot_prove_absence` (THE CORE) — you cannot hide a revocation.** If `id ∈ revoked`
(hence in the tree under the honest root `tree.H () revoked`), then NO absence witness against that same
root can exist while `HashCR` holds: such a witness would open the root to a set `s` with `id ∉ s`, but
binding forces `s = revoked ∋ id` — a contradiction. Presenting a valid absence for a revoked id against
its own root is exactly a hash collision. -/
theorem revoked_cannot_prove_absence (tree : CommitReveal Unit (Finset Id) Digest) (hcr : HashCR tree)
    (revoked : Finset Id) (id : Id) (hin : id ∈ revoked)
    (hAbs : Absent tree (tree.H () revoked) id) : False := by
  obtain ⟨s, hopen, hnotin⟩ := hAbs
  have hs : s = revoked := merkle_root_binds tree hcr s revoked hopen
  rw [hs] at hnotin
  exact hnotin hin

/-- **`absence_excludes_membership`.** Under `HashCR`, no root admits BOTH an absence witness and a
membership proof for the same id: they would open the root to one set both containing and not containing
`id`. (A client that accepts an absence proof is sound against a concurrent membership claim.) -/
theorem absence_excludes_membership (tree : CommitReveal Unit (Finset Id) Digest) (hcr : HashCR tree)
    (root : Digest) (id : Id) (hAbs : Absent tree root id) (hMem : Members tree root id) : False := by
  obtain ⟨s, hs, hns⟩ := hAbs
  obtain ⟨s', hs', hms⟩ := hMem
  have : s = s' := merkle_root_binds tree hcr s s' (hs.trans hs'.symm)
  rw [this] at hns
  exact hns hms

/-- **A genuinely-absent id has an absence witness** — the completeness/liveness direction: if
`id ∉ revoked`, the client legitimately accepts non-revocation against the honest root (the honest
revoked set is itself the witness). So `Absent` is not vacuously empty. -/
theorem nonrevoked_has_absence (tree : CommitReveal Unit (Finset Id) Digest)
    (revoked : Finset Id) (id : Id) (hout : id ∉ revoked) :
    Absent tree (tree.H () revoked) id :=
  ⟨revoked, rfl, hout⟩

/-! ## The attested root — the authority's hybrid signature over `(root ‖ epoch)`.

`AttestedRoot` mirrors `AttestedRevocationRoot`: a Merkle root, an epoch, and a signature over the body
`(root ‖ epoch)`. `verifyAttested` is `SigScheme.verify` under the ENROLLED authority key — reused
verbatim from `HybridCombiner`. -/

/-- **An attested revocation root**: the Merkle root, the epoch it was published at, and the authority's
signature over the body `bodyEnc root epoch`. Mirrors `AttestedRevocationRoot { merkle_root, /*epoch*/,
signature }`. -/
structure AttestedRoot (Digest Epoch Sig : Type*) where
  /-- The Merkle root of the revoked-id tree. -/
  root : Digest
  /-- The epoch (freshness marker) this root was attested at — signed INSIDE the body. -/
  epoch : Epoch
  /-- The authority's signature over `bodyEnc root epoch`. -/
  sig : Sig

/-- **`verifyAttested authorityPk att`** — the client's attestation check: the authority's signature on
the body `(root ‖ epoch)` verifies under the enrolled authority key. The `SigScheme.verify` face of
`AttestedRevocationRoot::verify_hybrid`. -/
@[reducible] def verifyAttested (S : SigScheme SK PK Msg Sig) (bodyEnc : Digest → Epoch → Msg)
    (authorityPk : PK) (att : AttestedRoot Digest Epoch Sig) : Prop :=
  S.verify authorityPk (bodyEnc att.root att.epoch) att.sig

/-- **`HonestAttestation`** — the authority signs ONLY the true root for each epoch: any body it signed,
`Q (bodyEnc root epoch)`, carries `root = tree.H () (trueRevoked epoch)`, the Merkle root of the true
revoked set at that epoch. The revocation analogue of `CapabilityChain.honestDelegation`: an honest
authority never attests a root that omits a token it has revoked. -/
def HonestAttestation (tree : CommitReveal Unit (Finset Id) Digest) (bodyEnc : Digest → Epoch → Msg)
    (Q : Msg → Prop) (trueRevoked : Epoch → Finset Id) : Prop :=
  ∀ (root : Digest) (epoch : Epoch),
    Q (bodyEnc root epoch) → root = tree.H () (trueRevoked epoch)

/-! ## Attestation forgery — an accepted-but-unsigned root is a signature forgery. -/

/-- **`forged_attestation_is_a_signature_forgery`.** An `AttestedRoot` that verifies under the honest
authority key but that the authority NEVER signed (`¬ Q (body)`) is a fresh valid signature on a body
outside the signing oracle — a `SigScheme.Forgery` on the authority key. So a client accepting a root
the authority never attested implies a signature forgery, refuting `EufCma`. -/
theorem forged_attestation_is_a_signature_forgery
    (S : SigScheme SK PK Msg Sig) (bodyEnc : Digest → Epoch → Msg)
    (authorityPk : PK) (Q : Msg → Prop) (att : AttestedRoot Digest Epoch Sig)
    (hverify : verifyAttested S bodyEnc authorityPk att)
    (hnever : ¬ Q (bodyEnc att.root att.epoch)) :
    Forgery S authorityPk Q :=
  ⟨bodyEnc att.root att.epoch, att.sig, hnever, hverify⟩

/-- **`wrong_root_for_epoch_is_forgery` (freshness / staleness).** The epoch is signed INSIDE the body,
so any attested root whose digest is NOT the true root for its claimed epoch — a replayed STALE root, or
any wrong root — could only be accepted via a forgery: the authority never signed `(wrongRoot ‖ epoch)`,
because by `HonestAttestation` it signs only the true root for each epoch. Hence a stale-root acceptance
either fails the epoch-bound signature check or IS a `Forgery`. -/
theorem wrong_root_for_epoch_is_forgery
    (S : SigScheme SK PK Msg Sig) (tree : CommitReveal Unit (Finset Id) Digest)
    (bodyEnc : Digest → Epoch → Msg) (authorityPk : PK) (Q : Msg → Prop)
    (trueRevoked : Epoch → Finset Id)
    (honest : HonestAttestation tree bodyEnc Q trueRevoked)
    (att : AttestedRoot Digest Epoch Sig)
    (hverify : verifyAttested S bodyEnc authorityPk att)
    (hwrong : att.root ≠ tree.H () (trueRevoked att.epoch)) :
    Forgery S authorityPk Q :=
  forged_attestation_is_a_signature_forgery S bodyEnc authorityPk Q att hverify
    (fun hq => hwrong (honest _ _ hq))

/-! ## SOUNDNESS — a forged non-revocation breaks `HashCR` OR forges the attestation. -/

/-- **THE DICHOTOMY — `forged_non_revocation_breaks_cr_or_forges`.** Suppose a client accepts a
genuinely-revoked id as un-revoked: an attested root `att` verifies under the authority key, `id` is in
the true revoked set at `att.epoch`, and an absence witness `witnessSet` opens `att.root` with
`id ∉ witnessSet`. Then EITHER the Merkle binding broke (`¬ HashCR tree`) OR the attestation was forged
(`Forgery S authorityPk Q`):

* if the authority DID sign `att`'s body, `HonestAttestation` pins `att.root` to the true root, so the
  absence witness opens the true root to a set omitting a revoked id — a collision (`¬ HashCR`);
* if the authority did NOT sign it, `att` is a `Forgery`.

The two doors, both closed by a named carrier. Mirrors `CapabilityChain.chain_forgery`'s case split. -/
theorem forged_non_revocation_breaks_cr_or_forges
    (S : SigScheme SK PK Msg Sig) (tree : CommitReveal Unit (Finset Id) Digest)
    (bodyEnc : Digest → Epoch → Msg) (authorityPk : PK) (Q : Msg → Prop)
    (trueRevoked : Epoch → Finset Id)
    (honest : HonestAttestation tree bodyEnc Q trueRevoked)
    (att : AttestedRoot Digest Epoch Sig) (witnessSet : Finset Id) (id : Id)
    (hverify : verifyAttested S bodyEnc authorityPk att)
    (hrevoked : id ∈ trueRevoked att.epoch)
    (hopen : tree.H () witnessSet = att.root)
    (habsent : id ∉ witnessSet) :
    ¬ HashCR tree ∨ Forgery S authorityPk Q := by
  by_cases hq : Q (bodyEnc att.root att.epoch)
  · -- Honest-signed: the attested root IS the true root; the absence witness collides with it.
    refine Or.inl ?_
    intro hcr
    have hr : att.root = tree.H () (trueRevoked att.epoch) := honest _ _ hq
    have hopen' : tree.H () witnessSet = tree.H () (trueRevoked att.epoch) := by rw [hopen, hr]
    have hs : witnessSet = trueRevoked att.epoch := merkle_root_binds tree hcr _ _ hopen'
    rw [hs] at habsent
    exact habsent hrevoked
  · -- Never-signed: the accepted attestation is a fresh forgery.
    exact Or.inr (forged_attestation_is_a_signature_forgery S bodyEnc authorityPk Q att hverify hq)

/-- **`revocation_sound` — under `HashCR` AND the authority's `EufCma`, no revoked token is accepted as
un-revoked.** The contrapositive of the dichotomy: if the Merkle tree is collision-resistant and the
authority's signature is unforgeable, a client CANNOT be made to accept a genuinely-revoked id. This is
revocation soundness relative to the two named carriers. -/
theorem revocation_sound
    (S : SigScheme SK PK Msg Sig) (tree : CommitReveal Unit (Finset Id) Digest)
    (bodyEnc : Digest → Epoch → Msg) (authorityPk : PK) (Q : Msg → Prop)
    (trueRevoked : Epoch → Finset Id)
    (hcr : HashCR tree) (heuf : EufCma S authorityPk Q)
    (honest : HonestAttestation tree bodyEnc Q trueRevoked)
    (att : AttestedRoot Digest Epoch Sig) (witnessSet : Finset Id) (id : Id)
    (hverify : verifyAttested S bodyEnc authorityPk att)
    (hrevoked : id ∈ trueRevoked att.epoch)
    (hopen : tree.H () witnessSet = att.root)
    (habsent : id ∉ witnessSet) :
    False :=
  (forged_non_revocation_breaks_cr_or_forges S tree bodyEnc authorityPk Q trueRevoked honest
      att witnessSet id hverify hrevoked hopen habsent).elim
    (fun hbreak => hbreak hcr) heuf

/-! ## ANCHORING — revocation soundness reduces to `HashCR ∨ (SchnorrDLHard ∨ MSISHard)`.

The attestation IS the `ed25519 ∧ ML-DSA` hybrid signature. So the authority's `EufCma` is not assumed —
it is DISCHARGED by `HybridCombiner.hybrid_secure_if_either_floor` from the discrete-log floor OR the
Module-SIS floor, exactly as `CapabilityChain.chain_unforgeable_under_hybrid_floor` discharges its
chain's keys. Revocation soundness therefore holds if `HashCR` holds AND EITHER cryptographic floor
does — the last protocol game bottoming out at the SAME floors as the whole tree. -/

/-- **THE HEADLINE — `revocation_sound_under_floor`.** With the per-key forking reductions (a hybrid
forgery ⟹ a `DLSolver` on the classical side, two SelfTargetMSIS solutions on the pq side — the
`HybridCombiner` reductions, not carriers), a client cannot accept a genuinely-revoked id as un-revoked
provided `HashCR tree` holds AND `SchnorrDLHard C G ∨ MSISHard (augmented A t) …`. The authority's
`EufCma` is produced by `hybrid_secure_if_either_floor`; the ONLY irreducible objects are the tree's
`HashCR` and the discrete-log / Module-SIS floors. This CLOSES the crypto tree: forging non-revocation
requires breaking the Merkle hash OR the hybrid signature, and the latter needs BOTH the discrete-log
and lattice floors to fall. -/
theorem revocation_sound_under_floor
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (A : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (tree : CommitReveal Unit (Finset Id) Digest) (bodyEnc : Digest → Epoch → Msg)
    (Q : Msg → Prop) (trueRevoked : Epoch → Finset Id)
    (dlFork : Forgery Cl pkc Q → DLSolver C G)
    (msisFork : Forgery Pq pkp Q →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w)
    (hcr : HashCR tree)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((β + β) + (β + β)))
    (honest : HonestAttestation tree bodyEnc Q trueRevoked)
    (att : AttestedRoot Digest Epoch (Sigc × Sigp)) (witnessSet : Finset Id) (id : Id)
    (hverify : verifyAttested (hybrid Cl Pq) bodyEnc (pkc, pkp) att)
    (hrevoked : id ∈ trueRevoked att.epoch)
    (hopen : tree.H () witnessSet = att.root)
    (habsent : id ∉ witnessSet) :
    False := by
  have heuf : EufCma (hybrid Cl Pq) (pkc, pkp) Q :=
    hybrid_secure_if_either_floor Cl Pq pkc pkp Q C G A t β dlFork msisFork hfloor
  exact revocation_sound (hybrid Cl Pq) tree bodyEnc (pkc, pkp) Q trueRevoked hcr heuf honest
    att witnessSet id hverify hrevoked hopen habsent

/-! ## Teeth — the guarantees FIRE on concrete data, and each carrier is load-bearing.

(a) Merkle side, over `Id = Digest = Finset ℕ` with the identity commitment (`H () s = s`, a binding
    tree): an honest non-revoked id is ACCEPTED; a revoked id has NO absence witness (`HashCR` fires);
    and under a COLLIDING tree the same revoked id CAN be hidden — so `HashCR` is load-bearing.
(b) Attestation side, over the toy `SigScheme` (`sig = pk + m`, the demo oracle of `CapabilityChain`):
    an attestation under an attacker key is REJECTED; an accepted-but-unsigned root exhibits the
    `Forgery`. -/

section Teeth

/-! ### (a) Merkle-binding teeth. -/

/-- A BINDING revocation tree over `Finset ℕ`: `H () s = s` is injective on the committed domain (the
identity commitment, à la `HermineHintMLWE.exCR`/`NonMembership.refCompress`). -/
@[reducible] def bindTree : CommitReveal Unit (Finset ℕ) (Finset ℕ) := ⟨fun _ s => s⟩

/-- The binding tree genuinely satisfies `HashCR`. -/
theorem bindTree_hashcr : HashCR bindTree := fun _ _ _ h => h

/-- **Honest non-revoked id ACCEPTED.** `2 ∉ {1}`, so the client legitimately accepts non-revocation of
`2` against the honest root — the honest revoked set `{1}` is the absence witness. -/
theorem tooth_nonrevoked_accepted : Absent bindTree (bindTree.H () ({1} : Finset ℕ)) 2 :=
  nonrevoked_has_absence bindTree {1} 2 (by decide)

/-- **Revoked id's absence-proof REJECTED (the `HashCR` tooth fires).** With `1 ∈ {1}` revoked, NO
absence witness against the honest root can exist — `revoked_cannot_prove_absence` turns any such
witness into a collision, contradicting `bindTree_hashcr`. You cannot hide the revocation of `1`. -/
theorem tooth_revoked_no_absence : ¬ Absent bindTree (bindTree.H () ({1} : Finset ℕ)) 1 :=
  fun h => revoked_cannot_prove_absence bindTree bindTree_hashcr {1} 1 (by decide) h

/-- A COLLIDING revocation tree: `H () s = 0` for every set — every root is `0`, so distinct sets
collide (`equivocation`-style, à la `HermineHintMLWE.badCR`). -/
@[reducible] def collTree : CommitReveal Unit (Finset ℕ) ℕ := ⟨fun _ _ => 0⟩

/-- `collTree` is NOT collision-resistant: `{1}` and `∅` both hash to `0`. -/
theorem collTree_not_hashcr : ¬ HashCR collTree :=
  distinct_sets_collide collTree {1} ∅ (by decide) rfl

/-- **THE LOAD-BEARING TOOTH — without `HashCR`, a revocation CAN be hidden.** Under the colliding tree,
the REVOKED id `1` (∈ `{1}`) HAS a valid absence witness: the empty set `∅` opens the root (`0`) and
omits `1`. So `revoked_cannot_prove_absence`'s `HashCR` hypothesis is exactly what rules this out — the
soundness genuinely fails when collision-resistance does. -/
theorem tooth_collision_hides_revocation : Absent collTree (collTree.H () ({1} : Finset ℕ)) 1 :=
  ⟨∅, rfl, by decide⟩

-- The binding tree's root IS the set (identity commitment); membership/absence are decidable facts.
#guard decide (bindTree.H () ({1} : Finset ℕ) = ({1} : Finset ℕ))
#guard decide ((1 : ℕ) ∈ ({1} : Finset ℕ))          -- `1` is revoked …
#guard decide ((2 : ℕ) ∉ ({1} : Finset ℕ))          -- … `2` is not (honestly absent).
-- The colliding tree crushes every set to root `0` — the collision that hides a revocation.
#guard decide (collTree.H () ({1} : Finset ℕ) = collTree.H () (∅ : Finset ℕ))

/-! ### (b) Attestation teeth — the toy `SigScheme` (`sig = pk + m`). -/

/-- The demo signing "hash": a signature is valid iff `sig = pk + m` (the oracle of `CapabilityChain`). -/
@[reducible] def toyS : SigScheme ℕ ℕ ℕ ℕ where
  pkOf sk := sk
  sign sk m := sk + m
  verify pk m sig := sig = pk + m

/-- The demo attestation body: `bodyEnc root epoch = root + epoch` (a stand-in for `signing_message`). -/
@[reducible] def toyBodyEnc : ℕ → ℕ → ℕ := fun root epoch => root + epoch

/-- The authority (pk `100`) HONESTLY attested root `5` at epoch `0`: `sig = 100 + (5 + 0) = 105`. -/
@[reducible] def honestAtt : AttestedRoot ℕ ℕ ℕ := { root := 5, epoch := 0, sig := 105 }

/-- The honest attestation VERIFIES under the enrolled authority key `100`. -/
theorem honestAtt_verifies : verifyAttested toyS toyBodyEnc 100 honestAtt := by decide

/-- **Attestation under an ATTACKER key REJECTED.** The honest attestation does not verify under a
different key `999` (`105 ≠ 999 + 5`) — a client pinning the enrolled authority rejects it. -/
theorem tooth_attacker_key_rejected : ¬ verifyAttested toyS toyBodyEnc 999 honestAtt := by decide

/-- The authority's signing oracle: it signed ONLY the honest body `bodyEnc 5 0`. -/
@[reducible] def toyQ : ℕ → Prop := fun m => m = toyBodyEnc 5 0

/-- A FORGED attested root: root `7` at epoch `0`, carrying a signature `107 = 100 + (7 + 0)` that
verifies under the authority key `100` — yet the authority never signed `bodyEnc 7 0`. -/
@[reducible] def forgedAtt : AttestedRoot ℕ ℕ ℕ := { root := 7, epoch := 0, sig := 107 }

/-- The forged root VERIFIES under the authority key (the whole danger: the wire check passes). -/
theorem forgedAtt_verifies : verifyAttested toyS toyBodyEnc 100 forgedAtt := by decide

/-- **The forged root EXHIBITS the `Forgery`.** Accepted under the authority key but never signed by it,
`forgedAtt` is a fresh valid signature on `bodyEnc 7 0 ∉ toyQ` — a `SigScheme.Forgery` on the authority
key `100`, the object `revocation_sound` refutes via `EufCma`. -/
theorem tooth_forged_root_is_forgery : Forgery toyS 100 toyQ :=
  forged_attestation_is_a_signature_forgery toyS toyBodyEnc 100 toyQ forgedAtt forgedAtt_verifies
    (by decide)

-- The honest attestation verifies under the enrolled key, but NOT under an attacker key…
#guard decide (verifyAttested toyS toyBodyEnc 100 honestAtt)
#guard decide (¬ verifyAttested toyS toyBodyEnc 999 honestAtt)
-- …and the forged root verifies on the wire yet was never signed (the `Forgery` witness).
#guard decide (verifyAttested toyS toyBodyEnc 100 forgedAtt)
#guard decide (¬ toyQ (toyBodyEnc 7 0))

end Teeth

/-! ### Axiom hygiene. -/

#assert_all_clean [
  merkle_root_binds,
  distinct_sets_collide,
  revoked_cannot_prove_absence,
  absence_excludes_membership,
  nonrevoked_has_absence,
  forged_attestation_is_a_signature_forgery,
  wrong_root_for_epoch_is_forgery,
  forged_non_revocation_breaks_cr_or_forges,
  revocation_sound,
  revocation_sound_under_floor,
  bindTree_hashcr,
  tooth_nonrevoked_accepted,
  tooth_revoked_no_absence,
  collTree_not_hashcr,
  tooth_collision_hides_revocation,
  honestAtt_verifies,
  tooth_attacker_key_rejected,
  forgedAtt_verifies,
  tooth_forged_root_is_forgery
]

end Dregg2.Crypto.RevocationSoundness
