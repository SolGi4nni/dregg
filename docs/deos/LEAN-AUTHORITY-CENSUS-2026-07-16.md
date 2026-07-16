# Lean-authority census: Rust deciders that should be Lean-with-a-portal

A repo-wide sweep (9 lanes, each adversarially verified — refuted findings dropped)
for the zkoracle pattern: Rust that **authors a soundness-relevant accept/reject**
where the decision should be Lean-authored and `@[export]`ed, Rust calling it —
versus legitimate Rust (fast crypto, IO, trace-gen, proving, glue).

**The headline:** the pattern is not zkoracle-local. It concentrates in the
**verification and authorization accept paths** — the exact places where a
Rust-authored decision is most dangerous, because a light client / mint gate /
authorizer relies on the boolean directly. Two verified Lean deciders
(`QuorumThreshold.supermajorityThreshold`, the sorted-Merkle accumulator) already
exist and are **hand-reimplemented in Rust in multiple crates** without a portal.

Verdicts: CONFIRMED by the verify pass, DOWNGRADE (real but lower criticality),
`?` (verify did not clearly match — treat as candidate, re-check before porting).

## ⚠ Scoping the campaign — three portability tiers

Not every finding is portable now. Classify each by whether the Lean *exists*:

- **PORT-NOW** — a verified, exportable Lean decider exists today; the work is
  `@[export]` + shim + wire + delete-Rust + differential-test. (The DUAL_AUTHORED
  findings whose `lean_ref` is real: derives, the sorted-Merkle accumulator,
  `QuorumThreshold` for non-Solana consumers, `grantWeightCore`.)
- **AUTHOR-NEW** — no Lean yet, but authorable now (not chain-gated): a Lean
  decider must be written first, then ported. (Datalog evaluator; DFA acceptance if
  not covered by `derives`.) Bigger lanes.
- **🔒 GRANT-GATED HOLD** — the Solana consensus/provenance/rooting/rotation model
  (**Cluster B**, and the Solana-specific sites inside Cluster A). This is
  DELIBERATELY not-yet-Lean: the formal Solana work is held pending the Solana
  Foundation grant decision (yes → do it; no → pivot to a different chain). These
  are **not wounds** — do NOT port them now. The chain-agnostic `QuorumThreshold`
  arithmetic underneath them CAN be ported for the *non-Solana* consumers
  (persist, lightclient, verifier-net); the Solana tally/rooting/rotation waits.

## Leverage clusters — port by shared decider, not file-by-file

### Cluster A — the quorum/supermajority tally (HIGHEST leverage)
The same `voted*3 ≥ total*2` threshold decision is hand-rolled across **six**
soundness-critical sites, while `metatheory/Dregg2/Distributed/QuorumThreshold.lean::supermajorityThreshold`
(verified, with `two_quorums_share_honest` intersection) and
`Bridge/HoldingWeightedTally.lean::passes` sit unused:
- `bridge/src/solana_consensus.rs::is_supermajority` / `tally_votes` (~320L, HIGH, CONFIRMED)
- `bridge/src/solana_provenance.rs` tally_authorized / rooted / rotate (~780L, HIGH, CONFIRMED)
- `bridge/src/solana_trustless.rs` the composed lock-proof mint gate (~650L, HIGH, CONFIRMED)
- `persist/src/federation.rs::verify_finalization_quorum` (~90L, HIGH, `?`)
- lightclient FinalityCert quorum (`distinct_committee_signers`, ~120L, HIGH, DOWNGRADE)
- verifier-net hybrid attested-root quorum admission (~140L, HIGH, `?`)

**Port:** `@[export]` a stake-weighted `supermajority (voted total : Nat) : Bool`
from QuorumThreshold; every tally calls it for the threshold decision. Ed25519
verify + hashing stay Rust; only the accept *arithmetic* moves. One portal, six
consumers, and the deployed tallies become the verified formula.

### Cluster B — the Solana consensus model (biggest single lane, HIGH)
Beyond the threshold, the entire Solana provenance/rooting/rotation model is
hand-authored Rust with **no Lean at all**: stake-table derivation + completeness
floor, authorized-voter binding, rooted-vs-exact-slot finality, weak-subjectivity
rotation. This is THE trustless-bridge accept path (value release).
**Port:** author `metatheory/Dregg2/Bridge/SolanaProvenance.lean` (stake table +
authorized-voter map + rooted-tally decider reusing Cluster A's intersection
theorems + `rotate_preserves_anchor_trust`), `@[export]` the deciders, route
`verify_lock_proof_consensus_anchored` through them. Wire decoders
(`decode_stake_delegation` etc.) stay LEGIT_RUST marshalling.

### Cluster C — biscuit/Datalog authorization (the through-line)
`token/src/datalog_verify.rs::verify_token_datalog_full` + `full_policy` (~800L,
HIGH, CONFIRMED) authors the biscuit-Datalog policy-satisfaction decision in Rust —
this **is** the "biscuit Datalog = the derivation circuit" through-line, and it is
the authorization accept the whole macaroon/cap model rests on.
**Port:** a Lean Datalog evaluator (the derivation-circuit semantics) authored +
`@[export]`ed; Rust calls it. The largest conceptual lane, but the most central.

### Cluster D — non-membership / revocation (reuse the deployed accumulator)
Revocation non-membership is decided in Rust in two crates while the **deployed
Lean sorted-Merkle accumulator** (the VK-epoch nullifier flip, canonical 3-accumulator
roots) is the verified authority for exactly this:
- `token/src/revocation.rs::verify_non_membership` / `verify_membership` (~120L, HIGH, CONFIRMED)
- `credentials/src/revocation.rs::verify_non_revocation` (~100L, MED, CONFIRMED)
- `credentials/src/verification.rs::verify_inner` (~140L, MED, CONFIRMED)
**Port:** `@[export]` the accumulator membership/non-membership decider; both crates call it.

### Cluster E — the derives matcher (the approved zkoracle port, generalized)
`Crypto/Deriv`'s verified computable `derives` is reimplemented in Rust in:
- zkoracle `injection.rs` (~87L, HIGH, CONFIRMED — **approved to port**)
- `dfa/src/air.rs::verify_acceptance` out-of-circuit DFA acceptance (~130L, HIGH, CONFIRMED)
**Port:** `@[export] derives`/`InjectionFree` once (byte-wire); both consumers call it.
Do injection first (approved, cheapest), dfa second on the same portal.

### Cluster F — commitment/root structure deciders (MED/LOW, discern carefully)
`storage/src/bucket_commitment.rs` content_root/object_leaf (~200L, HIGH, CONFIRMED),
`cell/src/commitment.rs` (~400L, LOW, `?`), `persist` canonical_ledger_root (~35L, HIGH, `?`).
Note: the BLAKE3/Poseidon2 *hashing* is fast-crypto LEGIT_RUST; only the *tree
structure / root-acceptance* logic is a candidate. Discern per-file before porting.

## Other confirmed candidates (own lanes, verify before porting)
- `turn/src/executor/authorize.rs::verify_authorization` (~800L, HIGH, `?`) — the
  authorization accept; the executor core is already Lean-FFI, so check whether this
  is a peripheral bypass.
- `blocklace/src/constitution.rs` self-amending Constitution + VoteTracker (~500L, HIGH, `?`).
- `turn/src/conditional.rs::resolve_inner` ProofCondition satisfaction (~200L, MED, `?`)
  — note this session already fixed the TurnExecuted decider here; the whole
  resolver is a should-be-Lean candidate.
- `coord/src/budget.rs` StingrayCounter rebalance (~200L, MED), `token/src/dregg_caveats.rs::verify_caveats`
  (~480L, MED, DOWNGRADE), `turn/src/verify.rs` receipt-chain (~300L, MED, DOWNGRADE).

## Exemplars — the pattern already works here (don't touch, copy)
- ML-KEM / ML-DSA / X25519 / FIPS-204: Lean-authored + `@[export]` + Rust calls them.
- `Bridge/ProofOfHoldings.lean::grantWeightCore` is `@[export]`ed as `grantWeightFFI`
  and dregg-governance calls it — BUT the bridge re-authors `is_consensus_proven`
  in Rust (DUAL_AUTHORED, HIGH, DOWNGRADE); route the bridge through the export too.
- The consensus-ordering lane found a STRONG-FORM export-swap already deployed for
  tau/2pc — the blocklace portal precedent to imitate.

## Recommended sequence (leverage × readiness, grant-gating respected)
PORT-NOW first (verified Lean exists), AUTHOR-NEW next, Solana HELD:
1. **Cluster E injection** (approved) → dfa — PORT-NOW, cheapest; deletes Rust
   against the verified `derives`; proves the byte-wire matcher portal end-to-end.
2. **Cluster A quorum portal — NON-Solana consumers only** — PORT-NOW; `@[export]`
   `QuorumThreshold.supermajorityThreshold`, wire persist/lightclient/verifier-net.
   (The Solana bridge tally sites are 🔒 grant-gated — they inherit the same portal
   later, for free, when the grant lands.)
3. **Cluster D revocation** — PORT-NOW; reuse the already-deployed sorted-Merkle
   accumulator; two crates (token + credentials).
4. **Cluster C Datalog** — AUTHOR-NEW; the through-line, largest conceptual effort;
   author the Lean Datalog evaluator, then port. Not chain-gated.
5. **🔒 Cluster B Solana model** — HELD pending the Solana Foundation grant. When
   it lands, it is the biggest single win (the trustless-bridge accept becomes a
   verified Lean object) and it inherits the Cluster A quorum portal already built.

Each port follows the ML-KEM shape: author/`@[export]` the Lean decider (byte-wire
or `lean_object*` boundary), a `dregg-lean-ffi` shim, install it as the authority,
delete the Rust reimpl, differential-test Lean-vs-old-Rust agree. The win is
structural: once the decider IS the Lean object, the theorem and the deployed
behavior cannot drift.
