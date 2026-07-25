/-
# Dregg2.Bridge.LightClientSolana — the VERIFIED Solana (Tower-BFT rooted-finality) light client.

This AUTHORS the Solana consensus-verification RULES in Lean and proves `sol_no_forgery`, closing
the biggest interchain gap: until now the Solana instance in `Dregg2.Bridge.ProofOfHoldings` was a
TRUE-INSTANCE — the foreign chain's finality was an ASSUMED oracle `finalized : Slot → Prop`, and the
"stake-weighted ≥2/3 supermajority over a finalized bank hash" was only a `TrustTier` enum TAG with NO
theorem behind it. This file replaces that tag with a real MODEL and a real supermajority theorem.

The verification formalized here is the SHIPPED Rust one — `bridge/src/solana_{trustless,consensus,
provenance}.rs`, the stake-weighted, authorized-voter-bound, ROOTED Ed25519 tally against a bank-state-
derived stake table trusted only to a governance-pinned weak-subjectivity (WS) anchor. That is
Solana's Tower-BFT rooted-finality: a slot is finalized when ≥2/3 of the ACTIVE stake has submitted an
authorized-voter-bound vote whose tower ROOT reaches the slot (not merely optimistically confirmed).

TWO LAYERS, kept distinct + honest (the `VerifiedLightClient` posture):

  * RULES (formalized + proven here, pure `Nat`/`Bool`/equality — the Nomad-class bug locus):
      - the DENOMINATOR is `totalStake`, the SUM of the ACTIVE stake in the WS-ANCHORED table
        (`EpochStakeTable::total_stake`, `solana_consensus.rs:171`) — NOT a supplied hint;
      - a validator's stake is counted iff a vote for it names the exact `(slot S, bankHash B)`, is
        bound to the on-chain AUTHORIZED voter, and is ROOTED — summed over DISTINCT vote accounts
        (`tally_authorized_rooted`, `solana_provenance.rs:724`);
      - the ≥2/3 supermajority in multiply form `3·rooted ≥ 2·total` (`is_supermajority`,
        `solana_consensus.rs:332` — u128 saturating, so wrap-free), with the `total > 0` floor
        (`EmptyStakeTable`, the Nomad-law tooth against a zero denominator).
  * CRYPTO (honest, NAMED, MINIMAL leaves — the `SolLeaf` fields):
      - `edSound` : ed25519 (`ed25519_dalek`) verify soundness — a verifying signature over the vote
        message `(slot, bankHash)` entails the key holder genuinely authorized it (`Signed`). This is
        the ONLY signature assumption; discharged in production by a verified ed25519 (EverCrypt-grade)
        realization. It does NOT say "the update is valid".
      - `stakeTableCR` : the stake-table ROOT collision-resistance CARRIER (a `Prop`, the
        `PortalFloor.Blake3Kernel.collisionHard` pattern) on `tableCommit` (`EpochStakeTable::root`,
        the domain-separated SHA-256 over the sorted `(pubkey, stake)` entries, `solana_consensus.rs:196`).
        Unpacked by `noTableCollision`: GIVEN the CR floor, a table opening the governance-pinned WS
        anchor root is THE table — so the ACTIVE-STAKE DENOMINATOR is pinned and cannot be swapped for a
        self-stake distribution. NOT stated as unconditional injectivity (pigeonhole-false for a real
        compressing hash); binding holds RELATIVE to the carrier.
    Both are EXPLICIT VISIBLE STRUCTURE FIELDS (never a global `axiom`, never a laundered `def FooHard`),
    and the `modelLeaf` instance PROVES both — so this file is genuinely axiom-clean end to end and the
    leaves demonstrably do not trivialise the theorems (a forged signer / a collapsing commitment
    REFUTE the carriers — both polarities witnessed).

THE THREE CLOSED HOLES (the red-team BR value-holes, each captured as a load-bearing conjunct + a
non-vacuity discriminator):

  * HOLE-1 (optimistic ≠ rooted, `solana_trustless.rs:864`): a counted vote must be ROOTED — its tower
    root reaches `S` (`v.rootSlot = some r ∧ S ≤ r`). An optimistically-confirmed vote (`rootSlot =
    none`) never counts; `sol_optimistic_rejected` witnesses the reject.
  * HOLE-2 (denominator-shrink, `solana_provenance.rs:531`): the denominator is the WS-ANCHOR-BOUND
    active table's total. A shrunk table has a different `tableCommit`, so `stakeTableOk` fails
    (`sol_shrunk_denominator_rejected`); and at the true total a minority never clears 2/3
    (`sol_minority_rejected`).
  * BR-2-A (imposter voter, `solana_provenance.rs:676`): a counted vote's signer must equal the vote
    account's on-chain AUTHORIZED voter (`v.signer = e.authorizedVoter`). An imposter key contributes
    nothing (`sol_imposter_rejected`).

NON-VACUITY: the gate accepts a genuine rooted supermajority AND the exact-2/3 boundary, and REJECTS
the sub-2/3 update, the empty stake table, the optimistic-only update, the imposter-signer update, the
shrunk-denominator update, and the forged-signature update (`sol_gate_discriminates`).

Kernel-clean: `#assert_axioms` hard-gates every theorem; the model leaf PROVES its two carriers.
-/
import Dregg2.Bridge.VerifiedLightClient
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Bridge.LightClientSolana

/-! ## §1 — The HONEST crypto leaf: ed25519 soundness + the stake-table-root CR carrier, as VISIBLE
fields. `SolLeaf` is the Solana refinement of the foundation `CryptoLeaf` shape: the signature
primitive is a PER-VOTER ed25519 verify over the vote message `(slot, bankHash)`, and the hash
primitive is the domain-separated stake-table root `tableCommit` from which the WS anchor binds. -/

/-- **`SolLeaf`** — the named, minimal verified-primitive bundle for Solana. `edSound` is THE
signature leaf; `stakeTableCR` + `noTableCollision` are the stake-table-root CR carrier. All are
visible structure fields an instance must supply. -/
structure SolLeaf where
  /-- ed25519 public key (32 bytes in production) — a vote account and its authorized voter. -/
  PubKey : Type
  /-- 32-byte digest — a bank hash `B`, and the stake-table root. -/
  Digest : Type
  /-- ed25519 signature (64 bytes in production). -/
  Sig : Type
  /-- Pubkey equality is decidable (the Rust `==` on `[u8; 32]`). Computability, not a crypto fact. -/
  pkeq : DecidableEq PubKey
  /-- Digest equality is decidable. -/
  deqD : DecidableEq Digest
  /-- `ed25519_dalek` verify: key, the vote message `(slot, bankHash)`, signature (`verify_signature`,
  `solana_consensus.rs:281`). Opaque; a verified ed25519 realizes it. -/
  edVerify : PubKey → (Nat × Digest) → Sig → Bool
  /-- The DENOTATION: the key holder genuinely authorized the vote message. -/
  Signed : PubKey → (Nat × Digest) → Prop
  /-- **THE ED25519 LEAF (named, minimal).** A verifying signature entails the key holder authorized
  the message — unforgeability, nothing more. -/
  edSound : ∀ pk m s, edVerify pk m s = true → Signed pk m
  /-- The stake-table root `EpochStakeTable::root` (`solana_consensus.rs:196`): a domain-separated
  SHA-256 over the sorted `(votePubkey, authorizedVoter, stake)` rows. Opaque. -/
  tableCommit : List (PubKey × PubKey × Nat) → Digest
  /-- **CARRIER — THE STAKE-TABLE-ROOT CR LEAF (named, minimal).** A `Prop`, NOT idealized
  injectivity (pigeonhole-false for the compressing SHA-256). Mirrors
  `PortalFloor.Blake3Kernel.collisionHard`: a production instance supplies the named SHA-256 CR floor;
  the model PROVES it; a collapsing commitment REFUTES it. -/
  stakeTableCR : Prop
  /-- The CR carrier unpacked: GIVEN the CR floor, two tables with the same root ARE the same table —
  so the WS-anchor-pinned root pins the active-stake DENOMINATOR. -/
  noTableCollision : stakeTableCR →
    ∀ t₁ t₂ : List (PubKey × PubKey × Nat), tableCommit t₁ = tableCommit t₂ → t₁ = t₂
  /-- The all-zero signature — the fail-closed probe's signature slot. -/
  zeroSig : Sig
  /-- The all-zero 32-byte digest. -/
  zeroDigest : Digest

/-- Decidable pubkey equality as a `Bool` (the Rust `==` on `[u8;32]`). -/
def SolLeaf.pkBeq (L : SolLeaf) (a b : L.PubKey) : Bool := @decide (a = b) (L.pkeq a b)
theorem SolLeaf.pkBeq_iff (L : SolLeaf) {a b : L.PubKey} : L.pkBeq a b = true ↔ a = b := by
  letI := L.pkeq; unfold SolLeaf.pkBeq; exact decide_eq_true_iff

/-- Decidable digest equality as a `Bool`. -/
def SolLeaf.dBeq (L : SolLeaf) (a b : L.Digest) : Bool := @decide (a = b) (L.deqD a b)
theorem SolLeaf.dBeq_iff (L : SolLeaf) {a b : L.Digest} : L.dBeq a b = true ↔ a = b := by
  letI := L.deqD; unfold SolLeaf.dBeq; exact decide_eq_true_iff

/-- **`SolLeaf.table_inj` (the floor theorem shape; mirrors `CryptoLeaf.hash_inj`).** GIVEN the CR
carrier, a stake-table-root equality pins the whole table. -/
theorem SolLeaf.table_inj (L : SolLeaf) (hcr : L.stakeTableCR)
    {t₁ t₂ : List (L.PubKey × L.PubKey × Nat)} (h : L.tableCommit t₁ = L.tableCommit t₂) : t₁ = t₂ :=
  L.noTableCollision hcr t₁ t₂ h

/-! ## §2 — The data types (`solana_consensus.rs` / `solana_provenance.rs` shapes). -/

/-- A stake-table row (`EpochStakeTable` entry + its `authorized_voters` binding): a vote account, its
on-chain authorized voter, and its ACTIVE stake (lamports). -/
structure StakeEntry (L : SolLeaf) where
  /-- The vote account pubkey. -/
  votePubkey : L.PubKey
  /-- The on-chain AUTHORIZED voter for the epoch (`decode_authorized_voter`) — the ONLY key whose
  signature may be counted for this account (BR-2-A). -/
  authorizedVoter : L.PubKey
  /-- The account's active stake (`effective_stake`), in lamports. -/
  stake : Nat

/-- A `ValidatorVote` + its ingested tower fields (`solana_consensus.rs:255`, `parse_verified_vote_tx`):
who it votes for, who actually SIGNED it, the slot/bank-hash it names, the tower ROOT it reaches, and
the signature. -/
structure SolVote (L : SolLeaf) where
  /-- The vote account this vote is for (`ingested.vote_account`). -/
  votePubkey : L.PubKey
  /-- The key that actually signed the vote transaction (`ingested.authorized_voter`). Counted only
  when it equals the account's on-chain authorized voter. -/
  signer : L.PubKey
  /-- The voted slot (`ingested.voted_slot`). -/
  slot : Nat
  /-- The voted bank hash (`ingested.voted_bank_hash`). -/
  bankHash : L.Digest
  /-- The tower ROOT this vote reaches (`ingested.root : Option u64`). `none` = a plain vote that never
  roots (optimistic only). -/
  rootSlot : Option Nat
  /-- The ed25519 signature over `(slot, bankHash)`. -/
  sig : L.Sig

/-- The update a Solana rooted-finality proof carries: the WS-anchor-derived stake table, the votes,
and the claimed rooted `(slot S, bankHash B)`. -/
structure SolUpdate (L : SolLeaf) where
  /-- The derived, WS-anchor-bound active stake table (its root is checked against the pinned anchor). -/
  table : List (StakeEntry L)
  /-- The submitted votes. -/
  votes : List (SolVote L)
  /-- The lock slot `S` claimed rooted-final. -/
  slot : Nat
  /-- The claimed bank hash `B` at slot `S`. -/
  bankHash : L.Digest

/-- The TRUSTED STATE: the governance-pinned weak-subjectivity anchor — the stake-table ROOT the
active-stake denominator is trusted relative to (`WeakSubjectivityAnchor.stake_table_root`,
`solana_provenance.rs:574`; the pin is enforced by `check_pinned_anchor`, `solana_trustless.rs:986`). -/
structure SolTrustedState (L : SolLeaf) where
  /-- The pinned WS stake-table root. -/
  anchorRoot : L.Digest

/-! ## §3 — THE RULES: the rooted authorized-voter stake tally + the ≥2/3 threshold.
(`tally_authorized_rooted` `solana_provenance.rs:724`, `is_supermajority` `solana_consensus.rs:332`.) -/

/-- The row projection the stake-table root commits over. -/
def entryRow {L : SolLeaf} (e : StakeEntry L) : L.PubKey × L.PubKey × Nat :=
  (e.votePubkey, e.authorizedVoter, e.stake)

/-- A vote is a `(S, B)` attestation for entry `e` iff it is for that vote account and names the exact
slot and bank hash (`v.slot == S && v.bank_hash == B` — the tally's exact-slot filter). The
authorized-voter binding + rooted flag + signature are the SEPARATE carriers below. -/
def isAttestedBy (L : SolLeaf) (S : Nat) (B : L.Digest) (e : StakeEntry L) (v : SolVote L) : Bool :=
  L.pkBeq v.votePubkey e.votePubkey && decide (v.slot = S) && L.dBeq v.bankHash B

/-- THE matched vote for entry `e` at `(S, B)` (`find?` = the first attestation for that account). -/
def matchVote (L : SolLeaf) (S : Nat) (B : L.Digest) (e : StakeEntry L) (votes : List (SolVote L)) :
    Option (SolVote L) :=
  votes.find? (isAttestedBy L S B e)

/-- Entry `e` is attested at `(S, B)` iff some vote names it. -/
def attests (L : SolLeaf) (u : SolUpdate L) (e : StakeEntry L) : Bool :=
  (matchVote L u.slot u.bankHash e u.votes).isSome

/-- The attesting entries (DISTINCT vote accounts — a filter over the table, so no double-count). -/
def attesters (L : SolLeaf) (u : SolUpdate L) : List (StakeEntry L) :=
  u.table.filter (fun e => attests L u e)

/-- **The counted rooted authorized voting stake** — summed over DISTINCT attesting vote accounts
(`voted_stake`). -/
def rootedStake (L : SolLeaf) (u : SolUpdate L) : Nat :=
  ((attesters L u).map (fun e => e.stake)).sum

/-- **The total ACTIVE stake** — the WS-anchor-bound table's `total_stake()`, the 2/3 DENOMINATOR. -/
def totalStake (L : SolLeaf) (u : SolUpdate L) : Nat :=
  (u.table.map (fun e => e.stake)).sum

/-- **CARRIER (ed25519, aggregate)** — every attested entry's matched vote signature verifies over the
vote message `(S, B)`. The named per-voter `edVerify` results, ANDed (a failed sig fails closed). -/
def edOk (L : SolLeaf) (u : SolUpdate L) : Bool :=
  u.table.all (fun e =>
    match matchVote L u.slot u.bankHash e u.votes with
    | some v => L.edVerify v.signer (u.slot, u.bankHash) v.sig
    | none => true)

/-- **CARRIER (stake-table root)** — the derived table binds to the pinned WS anchor root
(`root() == anchor.stake_table_root`, `VerifiedStakeTable::from_anchor`). This is what pins the
DENOMINATOR (HOLE-2). -/
def stakeTableOk (L : SolLeaf) (ts : SolTrustedState L) (u : SolUpdate L) : Bool :=
  L.dBeq (L.tableCommit (u.table.map entryRow)) ts.anchorRoot

/-- **GATE (authorized-voter binding, BR-2-A)** — every attested entry's matched vote is signed by the
account's on-chain AUTHORIZED voter (`ingested.authorized_voter == expected`). -/
def authOk (L : SolLeaf) (u : SolUpdate L) : Bool :=
  u.table.all (fun e =>
    match matchVote L u.slot u.bankHash e u.votes with
    | some v => L.pkBeq v.signer e.authorizedVoter
    | none => true)

/-- **GATE (rooted, HOLE-1)** — every attested entry's matched vote is ROOTED: its tower root reaches
the slot (`ingested.root = some r ∧ r ≥ S`). An optimistic vote (`rootSlot = none`) fails. -/
def rootedOk (L : SolLeaf) (u : SolUpdate L) : Bool :=
  u.table.all (fun e =>
    match matchVote L u.slot u.bankHash e u.votes with
    | some v => match v.rootSlot with | some r => decide (u.slot ≤ r) | none => false
    | none => true)

/-- **`solVerifyDecision`** — THE scalar verify-logic decision, over the six projections a deployed
node computes (two crypto carriers `edOk`/`stakeTableOk`, two logic gates `rootedOk`/`authOk`, the
counted stake, the total). The active-stake denominator must be nonzero (`EmptyStakeTable`), the
rooted authorized stake must meet the multiply-form 2/3 threshold, and every carrier/gate holds. This
is the object the AIR (`LightClientSolanaAir`) emits and `sol_no_forgery` is proven over. -/
def solVerifyDecision (rootedStk totalStk : Nat) (edB stakeB rootedB authB : Bool) : Bool :=
  decide (0 < totalStk)
  && decide (2 * totalStk ≤ 3 * rootedStk)
  && edB && stakeB && rootedB && authB

/-- **THE VERIFY RULES**, as the scalar decision over the update's true projections. -/
def solVerify (L : SolLeaf) (ts : SolTrustedState L) (u : SolUpdate L) : Bool :=
  solVerifyDecision (rootedStake L u) (totalStake L u)
    (edOk L u) (stakeTableOk L ts u) (rootedOk L u) (authOk L u)

/-- The empty / uninitialized update — no table, no votes, zeroed slot/hash: the Nomad fail-closed
probe (empty stake table ⇒ zero denominator ⇒ reject). -/
def emptyUpdate (L : SolLeaf) : SolUpdate L := ⟨[], [], 0, L.zeroDigest⟩

/-! ## §4 — THE FOREIGN-VALIDITY denotation: what a verify-accepted update genuinely IS. -/

/-- **`SolValidAt L ts u`** — Solana's OWN rooted-finality validity, relative to the pinned WS anchor
`ts`:

  * `rootedSupermajority` — a set of DISTINCT active vote accounts, meeting the multiply-form 2/3
    threshold against the ACTIVE-stake total, each of whose ON-CHAIN AUTHORIZED voter GENUINELY signed
    (the `Signed` denotation, via the ed25519 leaf) the bank hash `B` at slot `S`, and each of whose
    vote is ROOTED (its tower root reaches `S`) — not merely optimistically confirmed;
  * `anchorBinds` — the active table binds to the pinned WS anchor root, and that binding is BINDING
    (NO other table opens the anchor root) — exactly what the stake-table CR carrier buys, and what
    pins the DENOMINATOR against a self-stake substitution. -/
structure SolValidAt (L : SolLeaf) (ts : SolTrustedState L) (u : SolUpdate L) : Prop where
  rootedSupermajority :
    ∃ atts : List (StakeEntry L),
      (∀ e ∈ atts, e ∈ u.table)
      ∧ 2 * totalStake L u ≤ 3 * (atts.map (fun e => e.stake)).sum
      ∧ (∀ e ∈ atts, L.Signed e.authorizedVoter (u.slot, u.bankHash))
      ∧ (∀ e ∈ atts, ∃ v ∈ u.votes, isAttestedBy L u.slot u.bankHash e v = true
            ∧ ∃ r, v.rootSlot = some r ∧ u.slot ≤ r)
  anchorBinds :
    L.tableCommit (u.table.map entryRow) = ts.anchorRoot
    ∧ (∀ t, L.tableCommit t = ts.anchorRoot → t = u.table.map entryRow)

/-! ## §5 — Supporting extraction lemmas over the matched-vote aggregates. -/

/-- For an attesting entry `e` (in the filtered `attesters`), its matched vote EXISTS, is in the vote
list, and satisfies `isAttestedBy`. -/
theorem attester_matchVote (L : SolLeaf) (u : SolUpdate L) {e : StakeEntry L}
    (he : e ∈ attesters L u) :
    ∃ v, matchVote L u.slot u.bankHash e u.votes = some v
      ∧ v ∈ u.votes ∧ isAttestedBy L u.slot u.bankHash e v = true := by
  have hmem := (List.mem_filter.mp he)
  have hatt : attests L u e = true := hmem.2
  unfold attests at hatt
  cases hmv : matchVote L u.slot u.bankHash e u.votes with
  | none => rw [hmv] at hatt; simp at hatt
  | some v =>
    refine ⟨v, rfl, ?_, ?_⟩
    · exact List.mem_of_find?_eq_some hmv
    · exact List.find?_some hmv

/-- Every attesting entry `e` is a table entry. -/
theorem attester_mem_table (L : SolLeaf) (u : SolUpdate L) {e : StakeEntry L}
    (he : e ∈ attesters L u) : e ∈ u.table :=
  (List.mem_filter.mp he).1

/-! ## §6 — THE THREE OBLIGATIONS: NoForgery, FailClosed, NonVacuous. -/

/-- **NO FORGERY (the strong, ts-relative statement), GIVEN the stake-table CR carrier.** For every
leaf, pinned WS anchor and update: IF the CR carrier holds (`hcr` — the named crypto floor, an explicit
hypothesis), then verify-acceptance entails the update is Solana-ROOTED-VALID relative to that anchor —
a ≥2/3 subset of the ACTIVE stake, each account's ON-CHAIN AUTHORIZED voter genuinely signed the bank
hash at the slot (via the ed25519 leaf), each vote is ROOTED, and the denominator is the anchor-BOUND
active table. The proof CONSUMES `L.edSound` on the signature leg and `noTableCollision hcr` on the
`anchorBinds` leg: strip the ed25519 check, the rooted flag, the authorized binding, or the anchor
carrier, and this theorem is unprovable. -/
theorem sol_no_forgery (L : SolLeaf) (hcr : L.stakeTableCR) :
    ∀ (ts : SolTrustedState L) (u : SolUpdate L), solVerify L ts u = true → SolValidAt L ts u := by
  intro ts u h
  unfold solVerify solVerifyDecision at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_htot, hthr⟩, hed⟩, hstk⟩, hroot⟩, hauth⟩ := h
  -- unpack the aggregates to ∀-over-table form
  simp only [edOk, List.all_eq_true] at hed
  simp only [authOk, List.all_eq_true] at hauth
  simp only [rootedOk, List.all_eq_true] at hroot
  have hbind : L.tableCommit (u.table.map entryRow) = ts.anchorRoot := L.dBeq_iff.mp hstk
  refine ⟨⟨attesters L u, ?_, ?_, ?_, ?_⟩, hbind, ?_⟩
  · intro e he; exact attester_mem_table L u he
  · -- 2·total ≤ 3·rootedStake, and rootedStake is DEFINITIONALLY (attesters.map stake).sum
    exact hthr
  · -- each attester's authorized voter genuinely Signed (S, B)
    intro e he
    obtain ⟨v, hmv, _hvmem, hab⟩ := attester_matchVote L u he
    have hmemT := attester_mem_table L u he
    -- authorized-voter binding: v.signer = e.authorizedVoter
    have hauthE := hauth e hmemT
    simp only [hmv] at hauthE
    have hsigner : v.signer = e.authorizedVoter := L.pkBeq_iff.mp hauthE
    -- signature soundness: the signer genuinely signed (S, B)
    have hedE := hed e hmemT
    simp only [hmv] at hedE
    have hsigned := L.edSound v.signer (u.slot, u.bankHash) v.sig hedE
    rw [hsigner] at hsigned
    exact hsigned
  · -- each attester has a ROOTED matched vote in the vote list
    intro e he
    obtain ⟨v, hmv, hvmem, hab⟩ := attester_matchVote L u he
    have hmemT := attester_mem_table L u he
    have hrootE := hroot e hmemT
    simp only [hmv] at hrootE
    cases hrs : v.rootSlot with
    | none => simp [hrs] at hrootE
    | some r =>
      simp only [hrs, decide_eq_true_eq] at hrootE
      exact ⟨v, hvmem, hab, r, hrs, hrootE⟩
  · -- anchor binding is BINDING via the CR carrier
    intro t ht
    exact L.table_inj hcr (ht.trans hbind.symm)

/-- **FAIL CLOSED (the Nomad-law tooth) — UNCONDITIONAL.** The empty update is rejected under EVERY
pinned anchor and EVERY leaf, with NO crypto hypothesis: its empty table has total stake `0`, failing
the `0 < totalStk` floor (`EmptyStakeTable`). Fail-closed never leans on the CR floor. -/
theorem sol_fail_closed (L : SolLeaf) :
    ∀ ts : SolTrustedState L, solVerify L ts (emptyUpdate L) = false := by
  intro ts
  unfold solVerify solVerifyDecision emptyUpdate totalStake
  simp

/-! ## §7 — THE SCALAR DECISION TIE (the deployed accept/reject IS the proven object). -/

/-- **`solProjectedDecision`** — the six projections a node hands the scalar gate for update `u` under
pinned anchor `ts`: the counted rooted stake, the total, the two crypto carriers, the two logic gates.
DEFINITIONALLY `solVerify L ts u`. -/
def solProjectedDecision (L : SolLeaf) (ts : SolTrustedState L) (u : SolUpdate L) : Bool :=
  solVerifyDecision (rootedStake L u) (totalStake L u)
    (edOk L u) (stakeTableOk L ts u) (rootedOk L u) (authOk L u)

/-- **THE TRANSLATION-VALIDATION TIE.** Fed an update's true projections, the scalar decision is
DEFINITIONALLY `solVerify L ts u`. So gating a deployed node on `solVerifyDecision` (with ed25519 +
the stake-table root computed in Rust) gates it on the decision `sol_no_forgery` is proven over. -/
theorem solVerifyDecision_refines (L : SolLeaf) (ts : SolTrustedState L) (u : SolUpdate L) :
    solProjectedDecision L ts u = solVerify L ts u := rfl

/-- **THE PAYOFF: acceptance by the scalar decision entails Solana rooted-validity.** GIVEN the CR
carrier, if the projected `solVerifyDecision` accepts `u`, then `u` is Solana-ROOTED-VALID relative to
the pinned WS anchor. This is `sol_no_forgery` routed through the deployed decision object. -/
theorem solVerifyDecision_no_forgery (L : SolLeaf) (hcr : L.stakeTableCR)
    (ts : SolTrustedState L) (u : SolUpdate L)
    (h : solProjectedDecision L ts u = true) : SolValidAt L ts u :=
  sol_no_forgery L hcr ts u ((solVerifyDecision_refines L ts u) ▸ h)

/-! ## §8 — The 2/3 boundary tooth (the Solana analog of the ETH 342/341 Nomad boundary). -/

/-- **The no-rounding-trap boundary** (`is_supermajority`, multiply form): at total `3`, `rooted = 2`
meets the multiply-form 2/3 threshold, `rooted = 1` does not. `2 = ⌈2·3/3⌉` exactly. -/
theorem supermajority_boundary :
    (2 * 3 ≤ 3 * 2) ∧ ¬ (2 * 3 ≤ 3 * 1) := by decide

/-! ## §9 — The PROVED model leaf — a perfectly-binding realization (axiom-clean, non-laundering). A
PRODUCTION instance replaces `modelLeaf` with the verified ed25519 + SHA-256 stake-table realization,
whose `edSound`/`stakeTableCR` are the named library assumptions (the leaf fields ARE the audit
surface — `#assert_axioms` cannot see hypothesis-carried assumptions). -/

/-- The model digest: a perfectly-binding "stake-table root" — `tableCommit` is a free constructor, so
CR is constructor injectivity. `raw` carries opaque digests (bank hashes). (Production: 32-byte
SHA-256.) -/
inductive ModelDigest
  | raw : Nat → ModelDigest
  | commit : List (Nat × Nat × Nat) → ModelDigest
deriving DecidableEq, Repr

/-- The model `Signed` denotation: the genuine authorized voter is key `7`. Discriminates — an imposter
key `3` is NOT a genuine signer. (Mirrors the ETH `modelLeaf` `k = 7` core.) -/
def ModelSigned (pk : Nat) (_m : Nat × ModelDigest) : Prop := pk = 7

/-- The model ed25519 verifier: the signer is the genuine key `7` and the signature is the genuine
value `7` (message binding is modeled by the `isAttestedBy` slot/hash filter upstream). -/
def modelEdVerify (pk : Nat) (_m : Nat × ModelDigest) (s : Nat) : Bool :=
  decide (pk = 7) && decide (s = 7)

/-- **The ed25519 leaf, PROVED for the model**: a verifying model signature entails the genuine key. -/
theorem modelEdSound : ∀ pk m s, modelEdVerify pk m s = true → ModelSigned pk m := by
  intro pk m s h
  simp only [modelEdVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- The model leaf: `edSound` PROVED, and the stake-table CR CARRIER supplied as the GENUINE
injectivity `Prop` over `ModelDigest.commit` (NOT `True`). Inhabitable here (pairing is a free
constructor) and FALSE for the collapsing leaf below — both polarities witnessed, so every theorem is
kernel-axiom-clean AND the carrier demonstrably discriminates. -/
@[reducible] def modelLeaf : SolLeaf where
  PubKey := Nat
  Digest := ModelDigest
  Sig := Nat
  pkeq := inferInstance
  deqD := inferInstance
  edVerify := modelEdVerify
  Signed := ModelSigned
  edSound := modelEdSound
  tableCommit := ModelDigest.commit
  stakeTableCR := ∀ t₁ t₂ : List (Nat × Nat × Nat),
    ModelDigest.commit t₁ = ModelDigest.commit t₂ → t₁ = t₂
  noTableCollision := fun h => h
  zeroSig := 0
  zeroDigest := ModelDigest.raw 0

/-- **The model CR carrier HOLDS (positive polarity).** `commit` is a free constructor, so collision
resistance is constructor injectivity — dischargeable exactly as a production instance discharges the
named SHA-256 CR floor. -/
theorem modelLeaf_stakeTableCR : modelLeaf.stakeTableCR :=
  fun _ _ h => by injection h

/-! ### The collapse FALSIFIER — the carrier is load-bearing, not `True` in disguise. -/

/-- The collapsing commitment: every table roots to `raw 0` (the badCompress). -/
def collapseCommit (_ : List (Nat × Nat × Nat)) : ModelDigest := ModelDigest.raw 0

/-- A lawful `SolLeaf` over the COLLAPSING commitment — same ed25519 primitives, same genuine-CR-Prop
carrier SHAPE, stated over `collapseCommit`. Only the carrier separates it from the sound leaf. -/
@[reducible] def collapseLeaf : SolLeaf :=
  { modelLeaf with
    tableCommit := collapseCommit
    stakeTableCR := ∀ t₁ t₂ : List (Nat × Nat × Nat),
      collapseCommit t₁ = collapseCommit t₂ → t₁ = t₂
    noTableCollision := fun h => h }

/-- **The collapsing CR carrier is FALSE (negative polarity).** Two DIFFERENT tables share the root —
the carrier REFUTES a broken commitment, so it is a real discriminating hypothesis: the denominator
would be swappable. Both polarities witnessed. -/
theorem collapseLeaf_not_stakeTableCR : ¬ collapseLeaf.stakeTableCR := by
  intro h
  exact absurd (h [(1, 7, 50)] [(2, 7, 50)] rfl) (by decide)

/-! ## §10 — Concrete witnesses + the NON-VACUITY discriminators (the three holes bite). -/

/-- Two genuine active accounts (`1`, `2`), each authorized to key `7`, each staking `50` — total `100`. -/
def modelTable : List (StakeEntry modelLeaf) :=
  [⟨1, 7, 50⟩, ⟨2, 7, 50⟩]

/-- The claimed rooted bank hash `B` at slot `S = 100`. -/
def modelBankHash : ModelDigest := ModelDigest.raw 42

/-- The pinned WS anchor: the genuine table's root. -/
def modelAnchor : SolTrustedState modelLeaf := ⟨ModelDigest.commit (modelTable.map entryRow)⟩

/-- A GENUINE rooted vote for account `pk`: signed by the authorized voter `7`, at `(100, B)`, tower
root `100 ≥ 100` (rooted), signature `7`. -/
def rootedVote (pk : Nat) : SolVote modelLeaf := ⟨pk, 7, 100, modelBankHash, some 100, 7⟩

/-- The GENUINE update: both accounts submit rooted authorized votes ⇒ rooted stake `100` of total
`100`, well over 2/3. -/
def goodUpdate : SolUpdate modelLeaf :=
  ⟨modelTable, [rootedVote 1, rootedVote 2], 100, modelBankHash⟩

/-- **THE GATE ACCEPTS THE GENUINE ROOTED SUPERMAJORITY.** -/
theorem sol_good_accepted : solVerify modelLeaf modelAnchor goodUpdate = true := by decide

/-- **HOLE-1 (optimistic ≠ rooted).** The SAME votes but with NO tower root (`rootSlot = none`, an
optimistically-confirmed vote) are REJECTED — `rootedOk` fails. -/
def optimisticVote (pk : Nat) : SolVote modelLeaf := ⟨pk, 7, 100, modelBankHash, none, 7⟩
def optimisticUpdate : SolUpdate modelLeaf :=
  ⟨modelTable, [optimisticVote 1, optimisticVote 2], 100, modelBankHash⟩
theorem sol_optimistic_rejected : solVerify modelLeaf modelAnchor optimisticUpdate = false := by decide

/-- **BR-2-A (imposter voter).** The SAME rooted votes but SIGNED BY key `3` (not the on-chain
authorized voter `7`) are REJECTED — `authOk` fails (and `edOk`, since `3 ≠ 7`). -/
def imposterVote (pk : Nat) : SolVote modelLeaf := ⟨pk, 3, 100, modelBankHash, some 100, 7⟩
def imposterUpdate : SolUpdate modelLeaf :=
  ⟨modelTable, [imposterVote 1, imposterVote 2], 100, modelBankHash⟩
theorem sol_imposter_rejected : solVerify modelLeaf modelAnchor imposterUpdate = false := by decide

/-- **HOLE-2 (denominator-shrink).** A shrunk table (dropping account `2` to make a minority a
majority) has a DIFFERENT `tableCommit`, so `stakeTableOk` fails against the pinned anchor — the
denominator cannot be shrunk. -/
def shrunkUpdate : SolUpdate modelLeaf :=
  ⟨[⟨1, 7, 50⟩], [rootedVote 1], 100, modelBankHash⟩
theorem sol_shrunk_denominator_rejected :
    solVerify modelLeaf modelAnchor shrunkUpdate = false := by decide

/-- **HOLE-2 (the threshold half).** At the TRUE total `100`, a lone `50`-stake attester is a minority
(`3·50 = 150 < 200 = 2·100`) — rejected even with a valid rooted authorized vote. A minority never
clears 2/3 of the genuine active stake. -/
def minorityUpdate : SolUpdate modelLeaf :=
  ⟨modelTable, [rootedVote 1], 100, modelBankHash⟩
theorem sol_minority_rejected : solVerify modelLeaf modelAnchor minorityUpdate = false := by decide

/-- **EMPTY STAKE TABLE (Nomad-law default).** A zero-denominator update is rejected. -/
theorem sol_empty_rejected : solVerify modelLeaf modelAnchor (emptyUpdate modelLeaf) = false := by
  decide

/-- **FORGED SIGNATURE.** The genuine rooted votes but with a bad signature (`sig = 0 ≠ 7`) are
REJECTED — `edOk` fails. -/
def forgedSigVote (pk : Nat) : SolVote modelLeaf := ⟨pk, 7, 100, modelBankHash, some 100, 0⟩
def forgedSigUpdate : SolUpdate modelLeaf :=
  ⟨modelTable, [forgedSigVote 1, forgedSigVote 2], 100, modelBankHash⟩
theorem sol_forged_sig_rejected : solVerify modelLeaf modelAnchor forgedSigUpdate = false := by decide

/-- **THE EXACT-2/3 BOUNDARY.** A table of total `3` with a rooted attester of stake `2` is accepted
(`3·2 = 6 ≥ 6 = 2·3`); dropping to `1` is rejected — the Solana `is_supermajority` 2/3 tooth in the
gate itself. -/
def boundaryTable : List (StakeEntry modelLeaf) := [⟨1, 7, 2⟩, ⟨2, 7, 1⟩]
def boundaryAnchor : SolTrustedState modelLeaf := ⟨ModelDigest.commit (boundaryTable.map entryRow)⟩
def boundaryAcceptUpdate : SolUpdate modelLeaf :=
  ⟨boundaryTable, [rootedVote 1], 100, modelBankHash⟩
def boundaryRejectUpdate : SolUpdate modelLeaf :=
  ⟨boundaryTable, [rootedVote 2], 100, modelBankHash⟩
theorem sol_boundary_accept : solVerify modelLeaf boundaryAnchor boundaryAcceptUpdate = true := by decide
theorem sol_boundary_reject : solVerify modelLeaf boundaryAnchor boundaryRejectUpdate = false := by decide

/-- **THE DISCRIMINATOR, ASSEMBLED.** Under the SAME pinned anchor and active table, the gate accepts
the genuine rooted supermajority and REJECTS every one of the closed-hole attacks: optimistic-only,
imposter-signer, shrunk-denominator, minority, empty, forged-signature. Not a `True`-carrier. -/
theorem sol_gate_discriminates :
    solVerify modelLeaf modelAnchor goodUpdate = true
    ∧ solVerify modelLeaf modelAnchor optimisticUpdate = false
    ∧ solVerify modelLeaf modelAnchor imposterUpdate = false
    ∧ solVerify modelLeaf modelAnchor shrunkUpdate = false
    ∧ solVerify modelLeaf modelAnchor minorityUpdate = false
    ∧ solVerify modelLeaf modelAnchor (emptyUpdate modelLeaf) = false
    ∧ solVerify modelLeaf modelAnchor forgedSigUpdate = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **NO FORGERY, END TO END on the model.** The genuine update is accepted AND that acceptance
entails `SolValidAt` — a real rooted stake-weighted supermajority, via `sol_no_forgery` under the
proved model CR carrier. -/
theorem sol_good_valid : SolValidAt modelLeaf modelAnchor goodUpdate :=
  sol_no_forgery modelLeaf modelLeaf_stakeTableCR modelAnchor goodUpdate sol_good_accepted

/-! It runs (`#guard`): the gate discriminates on concrete data. -/

#guard solVerify modelLeaf modelAnchor goodUpdate == true
#guard solVerify modelLeaf modelAnchor optimisticUpdate == false
#guard solVerify modelLeaf modelAnchor imposterUpdate == false
#guard solVerify modelLeaf modelAnchor shrunkUpdate == false
#guard solVerify modelLeaf modelAnchor minorityUpdate == false
#guard solVerify modelLeaf modelAnchor forgedSigUpdate == false
#guard solVerify modelLeaf boundaryAnchor boundaryAcceptUpdate == true
#guard solVerify modelLeaf boundaryAnchor boundaryRejectUpdate == false

/-! ## §11 — Axiom hygiene (CI hard-gate). The ed25519 + stake-table CR leaves are the visible
`SolLeaf` fields / the `hcr` hypothesis, invisible to `#assert_axioms` exactly because they ARE the
audit surface; the model PROVES both carriers, so the file is kernel-clean end to end. -/

#assert_axioms sol_no_forgery
#assert_axioms sol_fail_closed
#assert_axioms solVerifyDecision_refines
#assert_axioms solVerifyDecision_no_forgery
#assert_axioms modelLeaf_stakeTableCR
#assert_axioms collapseLeaf_not_stakeTableCR
#assert_axioms sol_good_valid
#assert_axioms sol_gate_discriminates

#print axioms sol_no_forgery
#print axioms solVerifyDecision_no_forgery
#print axioms sol_gate_discriminates

end Dregg2.Bridge.LightClientSolana
