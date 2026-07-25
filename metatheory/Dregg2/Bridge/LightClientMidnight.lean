/-
# Dregg2.Bridge.LightClientMidnight — the VERIFIED Midnight (Substrate GRANDPA-finality) light client.

This AUTHORS the Midnight consensus-verification RULES in Lean and proves `mid_no_forgery`, closing the
FOURTH interchain gap. Until now the Midnight bridge was a TRUSTED MIRROR: the observer
(`bridge/src/midnight_observer.rs`) FOLLOWS the RPC's `chain_getFinalizedHead` (GRANDPA-rooted) and
never yields an un-finalized block, so its finality gate is STRUCTURAL — it TRUSTS the RPC's finalized
commitment; it does NOT itself verify a GRANDPA justification. The mint path is a federation-quorum
attestation (`bridge/src/midnight.rs`) and `midnight_inclusion.rs` is a BLAKE3 placeholder mirror tree
(`TODO(mirror-hash)`). There was NO light client, NO threshold check, NO theorem behind "block B is
GRANDPA-final". This file replaces the trusted mirror with a real MODEL and a real supermajority theorem.

Midnight is a Substrate chain (Cardano partner) using GRANDPA finality — a BFT finality gadget, like
Polkadot: a block is finalized when a GRANDPA COMMIT carries PRECOMMIT votes from a STRICT supermajority
(> 2/3) of the AUTHORITY-SET weight, each signed (Ed25519) over the target `(hash, number)` for a
specific ROUND and SET_ID (era). The formalization here is faithful to that gadget.

TWO LAYERS, kept distinct + honest (the `VerifiedLightClient` posture):

  * RULES (formalized + proven here, pure `Nat`/`Bool`/equality — the Nomad-class bug locus):
      - the DENOMINATOR is `totalWeight`, the SUM of the authority weights in the WS-ANCHORED authority
        set (`VoterSet::total_weight` in `finality-grandpa`) — NOT a supplied hint;
      - an authority's weight is counted iff a PRECOMMIT for it names the exact target `(hash H, number
        N)`, is for the claimed ROUND, and carries the ANCHORED SET_ID — summed over DISTINCT authorities;
      - the STRICT > 2/3 supermajority in multiply form `3·signed > 2·total` (`finality-grandpa`'s
        `threshold() = total − (total−1)/3` is EXACTLY `3·w > 2·t` for every `t ≥ 1`), with the
        `total > 0` floor (the Nomad-law tooth against a zero denominator). NOTE the STRICT `<` — GRANDPA,
        like Tendermint (and UNLIKE Solana's `≥`), rejects EXACTLY-2/3.
  * CRYPTO (honest, NAMED, MINIMAL leaves — the `MidLeaf` fields):
      - `edSound` : Ed25519 verify soundness — a verifying signature over the precommit message
        `(targetHash, targetNumber, round, setId)` entails the authority genuinely authorized it
        (`Signed`). The ONLY signature assumption; discharged by a verified Ed25519 realization.
      - `authSetCR` : the authority-set ROOT collision-resistance CARRIER (a `Prop`, the
        `PortalFloor.Blake3Kernel.collisionHard` pattern) on `authSetCommit` — the domain-separated
        commitment over the sorted `(authorityId, weight)` rows. Unpacked by `noSetCollision`: GIVEN the
        CR floor, a set opening the governance-pinned WS anchor root is THE set — so the weight
        DENOMINATOR is pinned and cannot be swapped for a shrunk / forged authority set. NOT stated as
        unconditional injectivity (pigeonhole-false for a real compressing hash); binding is
        RELATIVE to the carrier.
    Both are EXPLICIT VISIBLE STRUCTURE FIELDS (never a global `axiom`), and `modelLeaf` PROVES both — so
    the file is genuinely axiom-clean end to end and the leaves demonstrably do not trivialise the
    theorems (a forged signer / a collapsing commitment REFUTE the carriers — both polarities witnessed).

THE CLOSED HOLES (each a load-bearing conjunct + a non-vacuity discriminator):

  * STALE ERA (authority-set-change): the justification's SET_ID must equal the ANCHORED set id, and
    every counted precommit must carry that set id. A stale/forged authority set (an OLD era still
    holding keys) finalizes NOTHING for the current era — `mid_stale_era_rejected`. This is GRANDPA's
    analogue of Tendermint's `next_validators` overlap / Solana's denominator-shrink pin.
  * DENOMINATOR-SHRINK: the denominator is the WS-ANCHOR-BOUND authority set's total weight. A shrunk
    set has a different `authSetCommit`, so `authSetOk` fails (`mid_shrunk_set_rejected`); and at the
    true total a minority never clears the strict > 2/3 (`mid_minority_rejected`).
  * CROSS-ROUND: a counted precommit must name the CLAIMED round R. Precommits from a different round
    cannot be aggregated into a round-R commit (`mid_wrong_round_rejected`).

NON-VACUITY: the gate accepts a genuine strict-supermajority GRANDPA commit AND the just-over-2/3
boundary, and REJECTS the exactly-2/3 update, the sub-2/3 update, the empty authority set, the stale-era
update, the cross-round update, the shrunk-set update, and the forged-signature update
(`mid_gate_discriminates`).

Kernel-clean: `#assert_axioms` hard-gates every theorem; the model leaf PROVES its two carriers.
-/
import Dregg2.Bridge.VerifiedLightClient
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Bridge.LightClientMidnight

/-! ## §1 — The HONEST crypto leaf: Ed25519 soundness + the authority-set-root CR carrier, as VISIBLE
fields. `MidLeaf` is the Midnight refinement of the foundation `CryptoLeaf` shape: the signature
primitive is a PER-AUTHORITY Ed25519 verify over the precommit message `(targetHash, targetNumber,
round, setId)`, and the hash primitive is the domain-separated authority-set root `authSetCommit` the WS
anchor binds. -/

/-- **`MidLeaf`** — the named, minimal verified-primitive bundle for Midnight/GRANDPA. `edSound` is THE
signature leaf; `authSetCR` + `noSetCollision` are the authority-set-root CR carrier. All are visible
structure fields an instance must supply. -/
structure MidLeaf where
  /-- Ed25519 authority public key (32 bytes in production). -/
  PubKey : Type
  /-- 32-byte digest — a target block hash `H`, and the authority-set root. -/
  Digest : Type
  /-- Ed25519 signature (64 bytes in production). -/
  Sig : Type
  /-- Pubkey equality is decidable (the byte `==`). Computability, not a crypto fact. -/
  pkeq : DecidableEq PubKey
  /-- Digest equality is decidable. -/
  deqD : DecidableEq Digest
  /-- Ed25519 verify: authority key, the precommit message `(targetHash, targetNumber, round, setId)`,
  signature. Opaque; a verified Ed25519 realizes it. -/
  edVerify : PubKey → (Digest × Nat × Nat × Nat) → Sig → Bool
  /-- The DENOTATION: the authority key holder genuinely authorized the precommit message. -/
  Signed : PubKey → (Digest × Nat × Nat × Nat) → Prop
  /-- **THE ED25519 LEAF (named, minimal).** A verifying signature entails the authority authorized the
  precommit — unforgeability, nothing more. -/
  edSound : ∀ pk m s, edVerify pk m s = true → Signed pk m
  /-- The authority-set root: a domain-separated commitment over the sorted `(authorityId, weight)`
  rows of the GRANDPA authority set. Opaque. -/
  authSetCommit : List (PubKey × Nat) → Digest
  /-- **CARRIER — THE AUTHORITY-SET-ROOT CR LEAF (named, minimal).** A `Prop`, NOT idealized injectivity
  (pigeonhole-false for a compressing hash). Mirrors `PortalFloor.Blake3Kernel.collisionHard`: a
  production instance supplies the named CR floor; the model PROVES it; a collapsing commitment REFUTES
  it. -/
  authSetCR : Prop
  /-- The CR carrier unpacked: GIVEN the CR floor, two authority sets with the same root ARE the same set
  — so the WS-anchor-pinned root pins the weight DENOMINATOR. -/
  noSetCollision : authSetCR →
    ∀ t₁ t₂ : List (PubKey × Nat), authSetCommit t₁ = authSetCommit t₂ → t₁ = t₂
  /-- The all-zero signature — the fail-closed probe's signature slot. -/
  zeroSig : Sig
  /-- The all-zero 32-byte digest. -/
  zeroDigest : Digest

/-- Decidable pubkey equality as a `Bool`. -/
def MidLeaf.pkBeq (L : MidLeaf) (a b : L.PubKey) : Bool := @decide (a = b) (L.pkeq a b)
theorem MidLeaf.pkBeq_iff (L : MidLeaf) {a b : L.PubKey} : L.pkBeq a b = true ↔ a = b := by
  letI := L.pkeq; unfold MidLeaf.pkBeq; exact decide_eq_true_iff

/-- Decidable digest equality as a `Bool`. -/
def MidLeaf.dBeq (L : MidLeaf) (a b : L.Digest) : Bool := @decide (a = b) (L.deqD a b)
theorem MidLeaf.dBeq_iff (L : MidLeaf) {a b : L.Digest} : L.dBeq a b = true ↔ a = b := by
  letI := L.deqD; unfold MidLeaf.dBeq; exact decide_eq_true_iff

/-- **`MidLeaf.set_inj` (the floor theorem shape; mirrors `CryptoLeaf.hash_inj`).** GIVEN the CR carrier,
an authority-set-root equality pins the whole set. -/
theorem MidLeaf.set_inj (L : MidLeaf) (hcr : L.authSetCR)
    {t₁ t₂ : List (L.PubKey × Nat)} (h : L.authSetCommit t₁ = L.authSetCommit t₂) : t₁ = t₂ :=
  L.noSetCollision hcr t₁ t₂ h

/-! ## §2 — The data types (`finality-grandpa` / Substrate justification shapes). -/

/-- A GRANDPA authority-set row: an authority public key and its voting weight (usually `1`; Substrate
allows weights). -/
structure Authority (L : MidLeaf) where
  /-- The authority public key (Ed25519). -/
  authId : L.PubKey
  /-- The authority's voting weight. -/
  weight : Nat

/-- A GRANDPA PRECOMMIT vote inside a justification: which authority it is attributed to, the target it
finalizes `(hash, number)`, the round + set-id it was cast under, and the signature. -/
structure Precommit (L : MidLeaf) where
  /-- The authority this precommit is attributed to (its Ed25519 key). -/
  authId : L.PubKey
  /-- The target block hash `H` (`Precommit::target_hash`). -/
  targetHash : L.Digest
  /-- The target block number `N` (`Precommit::target_number`). -/
  targetNumber : Nat
  /-- The GRANDPA round this precommit was cast in. -/
  round : Nat
  /-- The authority-set id (era) this precommit was signed under. A precommit from a different era is
  bound (via Ed25519) to that OTHER set id and cannot count for the current era. -/
  setId : Nat
  /-- The Ed25519 signature over `(targetHash, targetNumber, round, setId)`. -/
  sig : L.Sig

/-- A GRANDPA finality justification (`GrandpaJustification`): the WS-anchor-derived authority set, the
precommits, and the claimed finalized target `(hash H, number N)` at round R under set id E. -/
structure MidUpdate (L : MidLeaf) where
  /-- The WS-anchor-bound authority set (its root is checked against the pinned anchor). -/
  authSet : List (Authority L)
  /-- The submitted precommits. -/
  precommits : List (Precommit L)
  /-- The claimed finalized block hash `H`. -/
  targetHash : L.Digest
  /-- The claimed finalized block number `N`. -/
  targetNumber : Nat
  /-- The GRANDPA round `R` this commit is for. -/
  round : Nat
  /-- The claimed authority-set id (era) `E`. -/
  setId : Nat

/-- The TRUSTED STATE: the governance-pinned weak-subjectivity anchor — the authority-set ROOT the weight
denominator is trusted relative to, AND the anchored set id (era). Advanced by the light client's
authority-set-change tracking; frozen here as the trust root. -/
structure MidTrustedState (L : MidLeaf) where
  /-- The pinned WS authority-set root. -/
  anchorRoot : L.Digest
  /-- The pinned WS authority-set id (the current era the light client is anchored to). -/
  anchorSetId : Nat

/-! ## §3 — THE RULES: the round/era-bound authority weight tally + the strict > 2/3 threshold. -/

/-- The row projection the authority-set root commits over. -/
def authRow {L : MidLeaf} (e : Authority L) : L.PubKey × Nat := (e.authId, e.weight)

/-- The precommit message the Ed25519 signature binds — `(targetHash, targetNumber, round, setId)`, built
from the target of the update `u` and the precommit's OWN round/set id (what was actually signed). -/
def precommitMsg (L : MidLeaf) (u : MidUpdate L) (v : Precommit L) : L.Digest × Nat × Nat × Nat :=
  (u.targetHash, u.targetNumber, v.round, v.setId)

/-- A precommit is a target `(H, N)` attestation for authority `e` iff it is attributed to that authority
and names the exact hash and number. The round + set-id + signature are the SEPARATE carriers below. -/
def isAttestedBy (L : MidLeaf) (H : L.Digest) (N : Nat) (e : Authority L) (v : Precommit L) : Bool :=
  L.pkBeq v.authId e.authId && decide (v.targetNumber = N) && L.dBeq v.targetHash H

/-- THE matched precommit for authority `e` at `(H, N)` (`find?` = the first attestation). -/
def matchVote (L : MidLeaf) (H : L.Digest) (N : Nat) (e : Authority L) (votes : List (Precommit L)) :
    Option (Precommit L) :=
  votes.find? (isAttestedBy L H N e)

/-- Authority `e` is attested at the update's target iff some precommit names it. -/
def attests (L : MidLeaf) (u : MidUpdate L) (e : Authority L) : Bool :=
  (matchVote L u.targetHash u.targetNumber e u.precommits).isSome

/-- The attesting authorities (DISTINCT — a filter over the set, so no double-count). -/
def attesters (L : MidLeaf) (u : MidUpdate L) : List (Authority L) :=
  u.authSet.filter (fun e => attests L u e)

/-- **The counted signed authority weight** — summed over DISTINCT attesting authorities. -/
def signedWeight (L : MidLeaf) (u : MidUpdate L) : Nat :=
  ((attesters L u).map (fun e => e.weight)).sum

/-- **The total authority weight** — the WS-anchor-bound set's `total_weight()`, the > 2/3 DENOMINATOR. -/
def totalWeight (L : MidLeaf) (u : MidUpdate L) : Nat :=
  (u.authSet.map (fun e => e.weight)).sum

/-- **CARRIER (Ed25519, aggregate)** — every attested authority's matched precommit signature verifies
over its precommit message. The named per-authority `edVerify` results, ANDed (a failed sig fails
closed). -/
def edOk (L : MidLeaf) (u : MidUpdate L) : Bool :=
  u.authSet.all (fun e =>
    match matchVote L u.targetHash u.targetNumber e u.precommits with
    | some v => L.edVerify e.authId (precommitMsg L u v) v.sig
    | none => true)

/-- **CARRIER (authority-set root)** — the derived authority set binds to the pinned WS anchor root
(`root() == anchor.authority_set_root`). This is what pins the DENOMINATOR (denominator-shrink). -/
def authSetOk (L : MidLeaf) (ts : MidTrustedState L) (u : MidUpdate L) : Bool :=
  L.dBeq (L.authSetCommit (u.authSet.map authRow)) ts.anchorRoot

/-- **GATE (round binding, cross-round)** — every attested authority's matched precommit names the
claimed round `R`. Precommits from a different round cannot be aggregated into a round-R commit. -/
def roundOk (L : MidLeaf) (u : MidUpdate L) : Bool :=
  u.authSet.all (fun e =>
    match matchVote L u.targetHash u.targetNumber e u.precommits with
    | some v => decide (v.round = u.round)
    | none => true)

/-- **GATE (era binding, stale-authority-set)** — the update's claimed set id equals the ANCHORED set id,
AND every attested authority's matched precommit carries the update's set id. A stale/forged authority
set (an old era) is rejected: its precommits carry a different set id, and its claimed era differs from
the anchor. This is the GRANDPA analogue of Tendermint's `next_validators` overlap. -/
def eraOk (L : MidLeaf) (ts : MidTrustedState L) (u : MidUpdate L) : Bool :=
  decide (u.setId = ts.anchorSetId)
  && u.authSet.all (fun e =>
      match matchVote L u.targetHash u.targetNumber e u.precommits with
      | some v => decide (v.setId = u.setId)
      | none => true)

/-- **`midVerifyDecision`** — THE scalar verify-logic decision, over the six projections a deployed node
computes (two crypto carriers `edOk`/`authSetOk`, two logic gates `roundOk`/`eraOk`, the counted weight,
the total). The denominator must be nonzero, the signed weight must meet the STRICT multiply-form > 2/3
threshold, and every carrier/gate holds. This is the object the AIR (`LightClientMidnightAir`) emits and
`mid_no_forgery` is proven over. -/
def midVerifyDecision (signedW totalW : Nat) (edB authsetB roundB eraB : Bool) : Bool :=
  decide (0 < totalW)
  && decide (2 * totalW < 3 * signedW)
  && edB && authsetB && roundB && eraB

/-- **THE VERIFY RULES**, as the scalar decision over the update's true projections. -/
def midVerify (L : MidLeaf) (ts : MidTrustedState L) (u : MidUpdate L) : Bool :=
  midVerifyDecision (signedWeight L u) (totalWeight L u)
    (edOk L u) (authSetOk L ts u) (roundOk L u) (eraOk L ts u)

/-- The empty / uninitialized update — no authorities, no precommits, zeroed fields: the Nomad
fail-closed probe (empty authority set ⇒ zero denominator ⇒ reject). -/
def emptyUpdate (L : MidLeaf) : MidUpdate L := ⟨[], [], L.zeroDigest, 0, 0, 0⟩

/-! ## §4 — THE FOREIGN-VALIDITY denotation: what a verify-accepted update genuinely IS. -/

/-- **`MidValidAt L ts u`** — Midnight's OWN GRANDPA-finality validity, relative to the pinned WS anchor
`ts`:

  * `finalitySupermajority` — a set of DISTINCT authorities, meeting the STRICT multiply-form > 2/3
    threshold against the total authority weight, each of whose Ed25519 key GENUINELY signed (the
    `Signed` denotation, via the Ed25519 leaf) a precommit for the target `(H, N)` at round `R` under
    the ANCHORED era, and each of whose precommit is for that round and era;
  * `anchorBinds` — the authority set binds to the pinned WS anchor root, and that binding is BINDING
    (NO other set opens the anchor root) — exactly what the CR carrier buys, pinning the DENOMINATOR
    against a shrunk/forged set;
  * `eraBinds` — the claimed era is the anchored era. -/
structure MidValidAt (L : MidLeaf) (ts : MidTrustedState L) (u : MidUpdate L) : Prop where
  finalitySupermajority :
    ∃ atts : List (Authority L),
      (∀ e ∈ atts, e ∈ u.authSet)
      ∧ 2 * totalWeight L u < 3 * (atts.map (fun e => e.weight)).sum
      ∧ (∀ e ∈ atts, L.Signed e.authId (u.targetHash, u.targetNumber, u.round, ts.anchorSetId))
      ∧ (∀ e ∈ atts, ∃ v ∈ u.precommits, isAttestedBy L u.targetHash u.targetNumber e v = true
            ∧ v.round = u.round ∧ v.setId = ts.anchorSetId)
  anchorBinds :
    L.authSetCommit (u.authSet.map authRow) = ts.anchorRoot
    ∧ (∀ t, L.authSetCommit t = ts.anchorRoot → t = u.authSet.map authRow)
  eraBinds : u.setId = ts.anchorSetId

/-! ## §5 — Supporting extraction lemmas over the matched-precommit aggregates. -/

/-- For an attesting authority `e`, its matched precommit EXISTS, is in the precommit list, and satisfies
`isAttestedBy`. -/
theorem attester_matchVote (L : MidLeaf) (u : MidUpdate L) {e : Authority L}
    (he : e ∈ attesters L u) :
    ∃ v, matchVote L u.targetHash u.targetNumber e u.precommits = some v
      ∧ v ∈ u.precommits ∧ isAttestedBy L u.targetHash u.targetNumber e v = true := by
  have hmem := (List.mem_filter.mp he)
  have hatt : attests L u e = true := hmem.2
  unfold attests at hatt
  cases hmv : matchVote L u.targetHash u.targetNumber e u.precommits with
  | none => rw [hmv] at hatt; simp at hatt
  | some v =>
    refine ⟨v, rfl, ?_, ?_⟩
    · exact List.mem_of_find?_eq_some hmv
    · exact List.find?_some hmv

/-- Every attesting authority `e` is a set member. -/
theorem attester_mem_set (L : MidLeaf) (u : MidUpdate L) {e : Authority L}
    (he : e ∈ attesters L u) : e ∈ u.authSet :=
  (List.mem_filter.mp he).1

/-! ## §6 — THE THREE OBLIGATIONS: NoForgery, FailClosed, NonVacuous. -/

/-- **NO FORGERY (the strong, ts-relative statement), GIVEN the authority-set CR carrier.** For every
leaf, pinned WS anchor and update: IF the CR carrier holds (`hcr` — the named crypto floor, an explicit
hypothesis), then verify-acceptance entails the update is Midnight-GRANDPA-VALID relative to that anchor
— a STRICT > 2/3 subset of the authority weight, each authority genuinely signed a precommit for the
target at the claimed round under the ANCHORED era (via the Ed25519 leaf), and the denominator is the
anchor-BOUND authority set. The proof CONSUMES `L.edSound` on the signature leg and `noSetCollision hcr`
on the `anchorBinds` leg: strip the Ed25519 check, the round gate, the era gate, or the anchor carrier,
and this theorem is unprovable. -/
theorem mid_no_forgery (L : MidLeaf) (hcr : L.authSetCR) :
    ∀ (ts : MidTrustedState L) (u : MidUpdate L), midVerify L ts u = true → MidValidAt L ts u := by
  intro ts u h
  unfold midVerify midVerifyDecision at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_htot, hthr⟩, hed⟩, hauthset⟩, hround⟩, hera⟩ := h
  -- unpack the aggregates to ∀-over-set form
  simp only [edOk, List.all_eq_true] at hed
  simp only [roundOk, List.all_eq_true] at hround
  simp only [eraOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hera
  obtain ⟨heraAnchor, heraVotes⟩ := hera
  have hbind : L.authSetCommit (u.authSet.map authRow) = ts.anchorRoot := L.dBeq_iff.mp hauthset
  refine ⟨⟨attesters L u, ?_, ?_, ?_, ?_⟩, ⟨hbind, ?_⟩, heraAnchor⟩
  · intro e he; exact attester_mem_set L u he
  · -- 2·total < 3·signedWeight, and signedWeight is DEFINITIONALLY (attesters.map weight).sum
    exact hthr
  · -- each attester's authority genuinely Signed the target at (round R, anchored era)
    intro e he
    obtain ⟨v, hmv, _hvmem, _hab⟩ := attester_matchVote L u he
    have hmemT := attester_mem_set L u he
    -- signature soundness over the precommit message
    have hedE := hed e hmemT
    simp only [hmv] at hedE
    have hsigned := L.edSound e.authId (precommitMsg L u v) v.sig hedE
    -- round + era: rewrite the precommit's own round/setId to the update's, then to the anchor era
    have hrE := hround e hmemT
    simp only [hmv, decide_eq_true_eq] at hrE
    have heE := heraVotes e hmemT
    simp only [hmv, decide_eq_true_eq] at heE
    unfold precommitMsg at hsigned
    rw [hrE, heE, heraAnchor] at hsigned
    exact hsigned
  · -- each attester has a round/era-consistent matched precommit in the list
    intro e he
    obtain ⟨v, hmv, hvmem, hab⟩ := attester_matchVote L u he
    have hmemT := attester_mem_set L u he
    have hrE := hround e hmemT
    simp only [hmv, decide_eq_true_eq] at hrE
    have heE := heraVotes e hmemT
    simp only [hmv, decide_eq_true_eq] at heE
    exact ⟨v, hvmem, hab, hrE, heE.trans heraAnchor⟩
  · -- anchor binding is BINDING via the CR carrier
    intro t ht
    exact L.set_inj hcr (ht.trans hbind.symm)

/-- **FAIL CLOSED (the Nomad-law tooth) — UNCONDITIONAL.** The empty update is rejected under EVERY
pinned anchor and EVERY leaf, with NO crypto hypothesis: its empty authority set has total weight `0`,
failing the `0 < totalW` floor. Fail-closed never leans on the CR floor. -/
theorem mid_fail_closed (L : MidLeaf) :
    ∀ ts : MidTrustedState L, midVerify L ts (emptyUpdate L) = false := by
  intro ts
  unfold midVerify midVerifyDecision emptyUpdate totalWeight
  simp

/-! ## §7 — THE SCALAR DECISION TIE (the deployed accept/reject IS the proven object). -/

/-- **`midProjectedDecision`** — the six projections a node hands the scalar gate for update `u` under
pinned anchor `ts`. DEFINITIONALLY `midVerify L ts u`. -/
def midProjectedDecision (L : MidLeaf) (ts : MidTrustedState L) (u : MidUpdate L) : Bool :=
  midVerifyDecision (signedWeight L u) (totalWeight L u)
    (edOk L u) (authSetOk L ts u) (roundOk L u) (eraOk L ts u)

/-- **THE TRANSLATION-VALIDATION TIE.** Fed an update's true projections, the scalar decision is
DEFINITIONALLY `midVerify L ts u`. So gating a deployed node on `midVerifyDecision` (with Ed25519 + the
authority-set root computed in Rust) gates it on the decision `mid_no_forgery` is proven over. -/
theorem midVerifyDecision_refines (L : MidLeaf) (ts : MidTrustedState L) (u : MidUpdate L) :
    midProjectedDecision L ts u = midVerify L ts u := rfl

/-- **THE PAYOFF: acceptance by the scalar decision entails Midnight GRANDPA-validity.** GIVEN the CR
carrier, if the projected `midVerifyDecision` accepts `u`, then `u` is Midnight-GRANDPA-VALID relative to
the pinned WS anchor. This is `mid_no_forgery` routed through the deployed decision object. -/
theorem midVerifyDecision_no_forgery (L : MidLeaf) (hcr : L.authSetCR)
    (ts : MidTrustedState L) (u : MidUpdate L)
    (h : midProjectedDecision L ts u = true) : MidValidAt L ts u :=
  mid_no_forgery L hcr ts u ((midVerifyDecision_refines L ts u) ▸ h)

/-! ## §8 — The strict > 2/3 boundary tooth (GRANDPA rejects EXACTLY-2/3, unlike Solana). -/

/-- **The strict-supermajority boundary** (`finality-grandpa` `threshold`): at total `3`, `signed = 2`
is EXACTLY 2/3 and is REJECTED (`3·2 = 6 = 2·3`, not strictly greater); `signed = 3` is accepted. This is
the STRICT `<` — GRANDPA (like Tendermint) needs > 2/3, not ≥ 2/3. -/
theorem strict_supermajority_boundary :
    ¬ (2 * 3 < 3 * 2) ∧ (2 * 3 < 3 * 3) := by decide

/-! ## §9 — The PROVED model leaf — a perfectly-binding realization (axiom-clean, non-laundering). A
PRODUCTION instance replaces `modelLeaf` with the verified Ed25519 + authority-set-root realization,
whose `edSound`/`authSetCR` are the named library assumptions (the leaf fields ARE the audit surface —
`#assert_axioms` cannot see hypothesis-carried assumptions). -/

/-- The model digest: a perfectly-binding "authority-set root" — `authSetCommit` is a free constructor, so
CR is constructor injectivity. `raw` carries opaque digests (block hashes). (Production: 32-byte hash.) -/
inductive ModelDigest
  | raw : Nat → ModelDigest
  | commit : List (Nat × Nat) → ModelDigest
deriving DecidableEq, Repr

/-- The model `Signed` denotation: a genuine authority is any NONZERO key. Discriminates — the zero key
is not a genuine signer. -/
def ModelSigned (pk : Nat) (_m : ModelDigest × Nat × Nat × Nat) : Prop := pk ≠ 0

/-- The model Ed25519 verifier: an authority `pk` signs with its own key value as the signature (a real
Ed25519 sig is unforgeably key-derived), and the key is nonzero. Message binding is modeled by the
`isAttestedBy` target filter + the round/era gates upstream. -/
def modelEdVerify (pk : Nat) (_m : ModelDigest × Nat × Nat × Nat) (s : Nat) : Bool :=
  decide (s = pk) && decide (pk ≠ 0)

/-- **The Ed25519 leaf, PROVED for the model**: a verifying model signature entails a genuine (nonzero)
authority key. -/
theorem modelEdSound : ∀ pk m s, modelEdVerify pk m s = true → ModelSigned pk m := by
  intro pk m s h
  simp only [modelEdVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The model leaf: `edSound` PROVED, and the authority-set CR CARRIER supplied as the GENUINE
injectivity `Prop` over `ModelDigest.commit` (NOT `True`). Inhabitable here (a free constructor) and
FALSE for the collapsing leaf below — both polarities witnessed, so every theorem is kernel-axiom-clean
AND the carrier demonstrably discriminates. -/
@[reducible] def modelLeaf : MidLeaf where
  PubKey := Nat
  Digest := ModelDigest
  Sig := Nat
  pkeq := inferInstance
  deqD := inferInstance
  edVerify := modelEdVerify
  Signed := ModelSigned
  edSound := modelEdSound
  authSetCommit := ModelDigest.commit
  authSetCR := ∀ t₁ t₂ : List (Nat × Nat),
    ModelDigest.commit t₁ = ModelDigest.commit t₂ → t₁ = t₂
  noSetCollision := fun h => h
  zeroSig := 0
  zeroDigest := ModelDigest.raw 0

/-- **The model CR carrier HOLDS (positive polarity).** `commit` is a free constructor, so collision
resistance is constructor injectivity — dischargeable exactly as a production instance discharges the
named CR floor. -/
theorem modelLeaf_authSetCR : modelLeaf.authSetCR :=
  fun _ _ h => by injection h

/-! ### The collapse FALSIFIER — the carrier is load-bearing, not `True` in disguise. -/

/-- The collapsing commitment: every authority set roots to `raw 0` (the badCompress). -/
def collapseCommit (_ : List (Nat × Nat)) : ModelDigest := ModelDigest.raw 0

/-- A lawful `MidLeaf` over the COLLAPSING commitment — same Ed25519 primitives, same genuine-CR-Prop
carrier SHAPE, stated over `collapseCommit`. Only the carrier separates it from the sound leaf. -/
@[reducible] def collapseLeaf : MidLeaf :=
  { modelLeaf with
    authSetCommit := collapseCommit
    authSetCR := ∀ t₁ t₂ : List (Nat × Nat),
      collapseCommit t₁ = collapseCommit t₂ → t₁ = t₂
    noSetCollision := fun h => h }

/-- **The collapsing CR carrier is FALSE (negative polarity).** Two DIFFERENT authority sets share the
root — the carrier REFUTES a broken commitment, so it is a real discriminating hypothesis: the
denominator would be swappable. Both polarities witnessed. -/
theorem collapseLeaf_not_authSetCR : ¬ collapseLeaf.authSetCR := by
  intro h
  exact absurd (h [(1, 2)] [(2, 3)] rfl) (by decide)

/-! ## §10 — Concrete witnesses + the NON-VACUITY discriminators (the holes bite). -/

/-- Three authorities: `1` and `2` at weight `2`, `3` at weight `1` — total weight `5`. A strict > 2/3
supermajority needs `3·signed > 10`, i.e. `signed ≥ 4` — met by `{1, 2}` (weight `4`), so authority `3`
may abstain (a genuine supermajority, not unanimity). -/
def modelAuthSet : List (Authority modelLeaf) := [⟨1, 2⟩, ⟨2, 2⟩, ⟨3, 1⟩]

/-- The claimed finalized block hash `H`. -/
def modelTargetHash : ModelDigest := ModelDigest.raw 42
/-- The claimed finalized block number `N`. -/
def modelTargetNumber : Nat := 1000
/-- The anchored round `R`. -/
def modelRound : Nat := 10
/-- The anchored era (authority-set id) `E`. -/
def modelSetId : Nat := 5

/-- The pinned WS anchor: the genuine set's root + the genuine era `5`. -/
def modelAnchor : MidTrustedState modelLeaf :=
  ⟨ModelDigest.commit (modelAuthSet.map authRow), modelSetId⟩

/-- A GENUINE precommit by authority `pk`: for the target `(H, N)` at round/era, signed with its own key
value `pk`. -/
def goodPrecommit (pk round setId : Nat) : Precommit modelLeaf :=
  ⟨pk, modelTargetHash, modelTargetNumber, round, setId, pk⟩

/-- The GENUINE justification: authorities `1` and `2` (weight `4` of `5`) precommit the target at the
anchored round `10` and era `5` ⇒ strict > 2/3 supermajority. -/
def goodUpdate : MidUpdate modelLeaf :=
  ⟨modelAuthSet, [goodPrecommit 1 modelRound modelSetId, goodPrecommit 2 modelRound modelSetId],
   modelTargetHash, modelTargetNumber, modelRound, modelSetId⟩

/-- **THE GATE ACCEPTS THE GENUINE GRANDPA COMMIT.** -/
theorem mid_good_accepted : midVerify modelLeaf modelAnchor goodUpdate = true := by decide

/-- **STALE ERA (authority-set-change).** The SAME precommits but under an OLD era `4` (both the claimed
set id and the precommits' set id) are REJECTED — `eraOk` fails against the anchored era `5`. -/
def staleEraUpdate : MidUpdate modelLeaf :=
  ⟨modelAuthSet, [goodPrecommit 1 modelRound 4, goodPrecommit 2 modelRound 4],
   modelTargetHash, modelTargetNumber, modelRound, 4⟩
theorem mid_stale_era_rejected : midVerify modelLeaf modelAnchor staleEraUpdate = false := by decide

/-- **CROSS-ROUND.** The SAME precommits but cast in round `9` while the commit claims round `10` are
REJECTED — `roundOk` fails. -/
def wrongRoundUpdate : MidUpdate modelLeaf :=
  ⟨modelAuthSet, [goodPrecommit 1 9 modelSetId, goodPrecommit 2 9 modelSetId],
   modelTargetHash, modelTargetNumber, modelRound, modelSetId⟩
theorem mid_wrong_round_rejected : midVerify modelLeaf modelAnchor wrongRoundUpdate = false := by decide

/-- **DENOMINATOR-SHRINK.** A shrunk set (dropping authority `3` so `{1,2}` looks like the whole set) has
a DIFFERENT `authSetCommit`, so `authSetOk` fails against the pinned anchor — the denominator cannot be
shrunk. -/
def shrunkUpdate : MidUpdate modelLeaf :=
  ⟨[⟨1, 2⟩, ⟨2, 2⟩], [goodPrecommit 1 modelRound modelSetId, goodPrecommit 2 modelRound modelSetId],
   modelTargetHash, modelTargetNumber, modelRound, modelSetId⟩
theorem mid_shrunk_set_rejected : midVerify modelLeaf modelAnchor shrunkUpdate = false := by decide

/-- **DENOMINATOR-SHRINK (the threshold half).** At the TRUE total `5`, a lone `2`-weight attester is a
minority (`3·2 = 6 < 10 = 2·5`) — rejected even with a valid signed precommit. -/
def minorityUpdate : MidUpdate modelLeaf :=
  ⟨modelAuthSet, [goodPrecommit 1 modelRound modelSetId],
   modelTargetHash, modelTargetNumber, modelRound, modelSetId⟩
theorem mid_minority_rejected : midVerify modelLeaf modelAnchor minorityUpdate = false := by decide

/-- **EMPTY AUTHORITY SET (Nomad-law default).** A zero-denominator update is rejected. -/
theorem mid_empty_rejected : midVerify modelLeaf modelAnchor (emptyUpdate modelLeaf) = false := by
  decide

/-- **FORGED SIGNATURE.** The genuine precommits but with a bad signature (`sig = 0 ≠ authId`) are
REJECTED — `edOk` fails. -/
def forgedPrecommit (pk round setId : Nat) : Precommit modelLeaf :=
  ⟨pk, modelTargetHash, modelTargetNumber, round, setId, 0⟩
def forgedSigUpdate : MidUpdate modelLeaf :=
  ⟨modelAuthSet, [forgedPrecommit 1 modelRound modelSetId, forgedPrecommit 2 modelRound modelSetId],
   modelTargetHash, modelTargetNumber, modelRound, modelSetId⟩
theorem mid_forged_sig_rejected : midVerify modelLeaf modelAnchor forgedSigUpdate = false := by decide

/-- **THE STRICT-2/3 BOUNDARY.** A weighted set `{authority 1 : weight 2, authority 2 : weight 1}` (total
`3`): authority `1` alone is EXACTLY 2/3 (`3·2 = 6 = 2·3`) and is REJECTED (strict `<`); both authorities
(`weight 3`) are accepted. GRANDPA's strict-supermajority tooth in the gate itself. -/
def boundaryAuthSet : List (Authority modelLeaf) := [⟨1, 2⟩, ⟨2, 1⟩]
def boundaryAnchor : MidTrustedState modelLeaf :=
  ⟨ModelDigest.commit (boundaryAuthSet.map authRow), modelSetId⟩
def boundaryAcceptUpdate : MidUpdate modelLeaf :=
  ⟨boundaryAuthSet, [goodPrecommit 1 modelRound modelSetId, goodPrecommit 2 modelRound modelSetId],
   modelTargetHash, modelTargetNumber, modelRound, modelSetId⟩
def boundaryRejectUpdate : MidUpdate modelLeaf :=
  ⟨boundaryAuthSet, [goodPrecommit 1 modelRound modelSetId],
   modelTargetHash, modelTargetNumber, modelRound, modelSetId⟩
theorem mid_boundary_accept : midVerify modelLeaf boundaryAnchor boundaryAcceptUpdate = true := by decide
theorem mid_boundary_reject : midVerify modelLeaf boundaryAnchor boundaryRejectUpdate = false := by decide

/-- **THE DISCRIMINATOR, ASSEMBLED.** Under the SAME pinned anchor and authority set, the gate accepts
the genuine strict-supermajority GRANDPA commit and REJECTS every closed-hole attack: stale-era,
cross-round, shrunk-set, minority, empty, forged-signature. Not a `True`-carrier. -/
theorem mid_gate_discriminates :
    midVerify modelLeaf modelAnchor goodUpdate = true
    ∧ midVerify modelLeaf modelAnchor staleEraUpdate = false
    ∧ midVerify modelLeaf modelAnchor wrongRoundUpdate = false
    ∧ midVerify modelLeaf modelAnchor shrunkUpdate = false
    ∧ midVerify modelLeaf modelAnchor minorityUpdate = false
    ∧ midVerify modelLeaf modelAnchor (emptyUpdate modelLeaf) = false
    ∧ midVerify modelLeaf modelAnchor forgedSigUpdate = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **NO FORGERY, END TO END on the model.** The genuine update is accepted AND that acceptance entails
`MidValidAt` — a real strict > 2/3 weight-supermajority under the anchored era, via `mid_no_forgery`
under the proved model CR carrier. -/
theorem mid_good_valid : MidValidAt modelLeaf modelAnchor goodUpdate :=
  mid_no_forgery modelLeaf modelLeaf_authSetCR modelAnchor goodUpdate mid_good_accepted

/-! It runs (`#guard`): the gate discriminates on concrete data. -/

#guard midVerify modelLeaf modelAnchor goodUpdate == true
#guard midVerify modelLeaf modelAnchor staleEraUpdate == false
#guard midVerify modelLeaf modelAnchor wrongRoundUpdate == false
#guard midVerify modelLeaf modelAnchor shrunkUpdate == false
#guard midVerify modelLeaf modelAnchor minorityUpdate == false
#guard midVerify modelLeaf modelAnchor forgedSigUpdate == false
#guard midVerify modelLeaf boundaryAnchor boundaryAcceptUpdate == true
#guard midVerify modelLeaf boundaryAnchor boundaryRejectUpdate == false

/-! ## §11 — Axiom hygiene (CI hard-gate). The Ed25519 + authority-set CR leaves are the visible
`MidLeaf` fields / the `hcr` hypothesis, invisible to `#assert_axioms` exactly because they ARE the audit
surface; the model PROVES both carriers, so the file is kernel-clean end to end. -/

#assert_axioms mid_no_forgery
#assert_axioms mid_fail_closed
#assert_axioms midVerifyDecision_refines
#assert_axioms midVerifyDecision_no_forgery
#assert_axioms modelLeaf_authSetCR
#assert_axioms collapseLeaf_not_authSetCR
#assert_axioms mid_good_valid
#assert_axioms mid_gate_discriminates

#print axioms mid_no_forgery
#print axioms midVerifyDecision_no_forgery
#print axioms mid_gate_discriminates

end Dregg2.Bridge.LightClientMidnight
