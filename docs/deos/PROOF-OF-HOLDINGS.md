# Proof-of-Holdings — participate by proving what you hold, not by surrendering it

*Design note — 2026-07-11. The primary way a `$DREGG` holder participates in dregg
governance. Companion to `docs/deos/TOKEN-MIRROR-BRIDGE.md` (the lock/mirror path,
which is the exception — value-import and slashable bonds) and
`docs/FINDING-chain-participation-census.md` §5 (the spine this closes).*

## The claim

To vote — or to carry governance weight — you prove you hold `$DREGG`, over your OWN
Solana account, and you keep it. No vault, no lock, no wrapped token, no transfer.
dregg is already a Solana light client, so it reads a finalized snapshot of the
holder's own SPL token account, verifies the balance against a real stake-weighted
super-majority, and grants governance weight *by proof*. Custody never moves.

As ember put it: *"why should you need to move your DREGG into a special wrap bridge
wallet that isn't even your own custody, just to be able to vote with it? there is no
reason for this except bad system design."* The lock-and-mirror path
(`TOKEN-MIRROR-BRIDGE.md`) still exists — but it is for *importing spendable value* or
posting a *slashable bond*, the cases where an escrow genuinely prevents a
double-spend. It is the wrong mechanism for participation, and it is no longer the
front door.

## The three moves

**Prove it.** `bridge/src/solana_holdings.rs::prove_holding_consensus_anchored`
— the production entry — takes a `HoldingProof` (the holder's own SPL token
account plus the Tower-BFT consensus evidence for its finalized slot), a
governance-pinned `WeakSubjectivityAnchor`, and the proof's `StakeProvenance`,
and returns a `ProvenHolding` at `LockProofTrust::ConsensusVerified`. It
verifies, fail-closed (any failure is an `Err`, never a trusted holding):

1. the account is owned by the **SPL Token program** (`owner_program`), or its
   165-byte `data` is not an authoritative balance — a load-bearing forgery check
   (below);
2. the `data` decodes as an SPL token `Account` (`decode_spl_token_account`:
   `mint(32) ‖ owner(32) ‖ amount_le(8)`) and the mint is the configured `$DREGG` mint;
3. the `EpochStakeTable` + authorized voters are **derived from Solana's own bank
   state** and admitted only against the pinned anchor (`from_anchor` +
   `tally_authorized`) — never supplied by the caller (the other load-bearing
   forgery check, below);
4. ≥ 2/3 of the epoch's active stake validly voted `(slot, bank_hash)` — real per-vote
   Ed25519 + stake-weighted sum (`solana_consensus::verify_supermajority`);
5. the `bank_hash` recomputes from its committed components (binding the accounts hash);
6. the holder account's per-account hash includes into that accounts hash via the SAME
   16-ary fan-out the `$DREGG` mint path proves the vault with
   (`solana_wire::verify_account_inclusion_16ary`);
7. if a PoH segment is required, its tick chain links from the anchored checkpoint
   blockhash under the bounded `PohAnchorPolicy`.

So the claim is precise: the holding proof is trustless **over a
governance-pinned weak-subjectivity anchor** — the standard light-client trust
model — not trustless from nothing. The deployed configuration must pin the
real governance-chosen `(epoch, stake_table_root)`; the path fails closed
without one.

**Keep it.** Nothing in that path moves a lamport. The account observed is the
holder's own — `HoldingAccount`, never a vault. The Lean model makes this a theorem,
not a comment: `grantWeight` returns `(weight assignment, chain state)` and the state
component is *definitionally* the pre-state (`grant_preserves_custody : … .2 = pre :=
rfl`). Custody is preserved by construction.

**Vote with it.** `dregg-governance/src/holding_weight.rs::grant_weight` turns a
`ProvenHolding` into a `WeightGrant` for a dregg `VoterId`, and
`HoldingWeightRegistry::grant_and_cast` casts a weighted ballot into the real
`CollectiveChoice` tally.

## The weight binding

**Owner → voter.** A Solana wallet pubkey is an Ed25519 key; a dregg `VoterId` is an
Ed25519 key. The binding is the simplest sound one: an Ed25519 signature *by the
holding's owner wallet* over a domain-separated message committing to the target voter
(`binding_message = BIND_DOMAIN ‖ owner ‖ voter`, `BIND_DOMAIN =
b"dregg-holding-weight-bind-v1"`). Verifying it (`verify_binding`, strict /
malleability-rejecting) proves the owner authorized that voter to wield the weight — no
registry, no trusted third party, self-verifiable from the proof alone. A missing or
wrong-key signature is `GrantError::UnboundOwner` and grants nothing.

**Snapshot.** The granted weight is the balance proven *as of the finalized snapshot
slot* (`ProvenHolding.slot`), carried on the `WeightGrant` so a poll can pin an
as-of-S electorate. A poll fixes ONE snapshot slot (`open_snapshot`); a holding proven
at any other slot is `GrantError::WrongSnapshot`.

**No double-count.** `HoldingWeightRegistry` keeps a per-`(poll, token_account)`
nullifier set. Re-presenting the same account into the same poll is
`GrantError::AlreadyCounted`. The snapshot pin closes the move-the-same-tokens attack:
proving balance in account A at slot S, then moving A→B and proving B at a later slot,
would otherwise mint two distinct nullifiers — but at a single finalized slot the
tokens sit in exactly one account, so only one counts. (The vote engine's own
one-vote-per-voter rule is a complementary second guard: the nullifier stops the same
*account* voting twice; the engine's voted-set stops the same *voter* voting twice.)

## Fail-closed (the Nomad-law analog)

Weight is granted ONLY when the holding is `ConsensusVerified`. The SAME account read
over plain RPC yields `LockProofTrust::StructureOnly`
(`observe_holding_structure`) — exactly what a forged or MITM RPC node can fabricate —
and `is_consensus_proven()` is `false`, so `grant_weight` refuses with
`GrantError::NotConsensusProven` *before it even examines the signature*. A zero balance
is `GrantError::ZeroAmount`. Every refusal grants ZERO and, in the registry, spends no
nullifier (so a genuinely-later valid proof of the same account can still be counted).

### The load-bearing forgery check

An attacker can put arbitrary bytes — `mint ‖ their_wallet ‖ u64::MAX` — into an
account owned by *their own* program and get it into a genuine finalized accounts hash.
So the owner-**program** check (step 1) is not optional: only accounts owned by the SPL
Token program are real token balances. This is a program-*owner* binding, not a custody
surrender — every wallet's own token account already is owned by the SPL Token program,
and the holder still controls it via the SPL `Account.owner` field (that owner is the
wallet that gets the weight). Dropping the check reintroduces the exact forgery the
vault path defends against; `NotSplTokenProgram` refuses it.

### The second load-bearing forgery check: no caller-supplied stake table

An adversarial audit (2026-07-12) found that the originally shipped path —
`prove_holding_consensus` over a caller-supplied `EpochStakeTable` — was itself
a **forgery**: "≥ 2/3 of stake" over a table the attacker wrote is vacuous (a
1-key attacker table plus one self-signed vote clears its own supermajority,
yielding a `ConsensusVerified` holding of `u64::MAX` — and the owner-program
check is vacuous under a forged table too). The fix routes every production
`ConsensusVerified` through the anchored provenance path (step 3 above); the
bare-table entries are `#[cfg(test)]`/`test-utils`-gated. Verified: the
attacker's 1-key stake table rejects (`AnchorRootMismatch`) on both the bridge
path and the production watcher (`dregg-pay/src/watcher.rs::verify_consensus`,
which calls `prove_holding_consensus_anchored`), and a plain build has no
bare-table→`ConsensusVerified` path.

## The decision is the verified Lean object (Lean-first, `@[export]`)

The weight VERDICT is not decided by Rust. The ed25519 binding verify, the
consensus-proof read, and the positive-amount check are fast-Rust **pre-checks** — they
establish the facts. The fail-closed verdict itself is rendered by the extracted,
axiom-clean Lean core:

- `metatheory/Dregg2/Bridge/ProofOfHoldings.lean::grantWeightCore
  (isConsensusProven slotFinal : Bool) (amount : Weight) : Weight :=
  if isConsensusProven && slotFinal then amount else 0` — the executable verdict,
  `@[export dregg_holding_grant_weight]` as `grantWeightFFI`.
- `grantWeightCore_eq_grantsWeight` proves the core REALIZES the `grantsWeight` spec
  (grants the full proven weight iff the predicate holds), so routing through it
  computes exactly the backed grant, not a weaker or divergent mirror.
- `weight_backed_and_noncustodial` is the top theorem: a granted `w` for `v` is backed
  by a consensus-proven holding of `≥ w` at a finalized slot owned by `v`, AND the grant
  leaves on-chain state definitionally unchanged. Real AND non-custodial.
- Non-vacuity is proven on both axes: `gate_discriminates_both_axes` — the same holding
  on the `rpc` tier grants nothing, and a weight over the proven amount is never
  grantable; `emptyOracle_grants_nothing` is the fail-closed default (`finalized ≡
  False`). Every theorem is `#assert_axioms`-clean.

Rust marshals the two facts + the amount onto a wire and calls the exported core via
`dregg_lean_ffi::shadow_holding_grant_weight`
(`dregg-governance/src/holding_weight.rs::grant_weight`). If the archive lacks the
export, it is `GrantError::LeanCoreUnavailable` — there is NO Rust fallback for the
DECISION by design. This is the `grain-verify` / `fips204-verify` discipline: the
decision is the Lean-proven object or it is not made.

## What is real and tested vs. residual — honestly

**Real and tested (default gate, both polarities):**

- The non-custodial verifier: `prove_holding_consensus_anchored` (production;
  the bare-table `prove_holding_consensus` is test-gated) and the
  forgery/mint/decode refusals, including the forged-stake-table reject.
  `bridge/tests/solana_holdings.rs` runs, by default, a holder's own 165-byte
  SPL account included under an 80%-stake finalized bank hash proving a
  `ConsensusVerified` holding (a); the SAME account over RPC yielding only
  `StructureOnly` (b); a 40% sub-super-majority refused (c); wrong-mint (d), too-short
  blob (e), non-SPL-Token-program owner, tampered accounts hash, and unbound bank hash
  all refused. Fixtures are built from the REAL crate constructors (`EpochStakeTable`,
  `ValidatorVote::sign`, `BankHashComponents`, `solana_account_hash`,
  `AccountsInclusionProof16`) — the same machinery the mint path uses, pointed at the
  holder's own account.
- The weight binding: the reject-polarity tests in
  `dregg-governance/src/holding_weight.rs` run by default — `StructureOnly` grants zero,
  wrong-key/wrong-voter binding refused, zero amount refused, wrong-snapshot refused,
  poll-not-open does not burn the nullifier. (The *positive* grant-path tests skip
  cleanly when the Lean verdict core is not yet linked — see the FFI residual — rather
  than assert a Rust decision we deliberately do not have.)
- The Lean soundness model: `metatheory/Dregg2/Bridge/ProofOfHoldings.lean`, axiom-clean, with
  the `#guard` executable checks and the top/non-vacuity theorems above.
- The Solana-side lock program named-not-built earlier IS now built:
  `solana-lock/` (`dregg-solana-lock` — `processor.rs`, `state.rs`, `instruction.rs`,
  `attestation.rs`, `record.rs`, with `solana-lock/tests/lock_flow.rs` / `solana-lock/tests/unlock_flow.rs`).
  It belongs to the lock/mirror exception, not this path, but it is no longer a name.

**Residual (named, not yet closed):**

- **Live-feed ingestion.** The consensus fixtures are constructed in-test. The
  *machinery* is built (real vote-`Transaction` parsing, bank-state-derived
  stake tables + rotation, the real 16-ary accounts-hash format, the anchored
  PoH policy — `solana_wire.rs` / `solana_provenance.rs`); the residual is
  wiring a live Solana feed into it (a geyser/snapshot source for the
  accounts-hash inclusion proofs and harvested vote transactions —
  `SOLANA-DEVNET.md` names what RPC hides), plus the operator pinning the real
  governance-chosen anchor.
- **In-circuit fold.** The consensus verify is real but *off-circuit* —
  re-executing-validator grade, not yet folded into an AIR so a succinct dregg light
  client (rather than a re-executor) attests it. That is the succinct wrapper
  (`docs/deos/SOLANA-SUCCINCT-WRAPPER.md`), the multi-month item.
- **The FFI link-up — LINKED and VERIFIED (not a residual).** `grantWeightCore`/
  `grantWeightFFI` are built, proven, `@[export]`ed as `dregg_holding_grant_weight`,
  and — after relocating the module from `Metatheory/Bridge/` to
  `Dregg2/Bridge/ProofOfHoldings.lean` so its IR emits where the archive splice walks
  (`Dregg2/**/*.c`, like every other exported decision) — the symbol is spliced into
  the archive. Verified on hbox with a real archive build: `nm` finds
  `dregg_holding_grant_weight` in `libdregg_lean.a`,
  `holding_grant_weight_core_available()` returns **true**, and
  `cargo test -p dregg-governance holding` runs **9/9** — the six grant-path tests that
  previously skipped now execute the verified-Lean-called-from-Rust path end to end.
  The proof governs the running decision, not just the spec.

## Non-goals

- No new bridge token, no wrapped-asset custody, no vote-wallet. Holdings stay in the
  holder's own account; weight is granted by proof over it.
- Not a replacement for the lock/mirror path — that path is retained for its real
  purpose (importing spendable value, slashable bonds), just no longer conflated with
  participation.
