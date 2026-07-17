# Token Mirror Bridge — mirroring a Solana/pump.fun SPL token into dregg's value layer

> **Locking is the EXCEPTION, not how you participate.** This bridge exists to *import
> spendable value* into dregg's value layer (or to post a *slashable bond*) — the cases
> where an escrow genuinely prevents a double-spend, so surrendering custody into a vault
> is the point. It is the WRONG mechanism for *participation*. To vote or to carry
> governance weight, you do NOT lock: you PROVE you hold `$DREGG` over your own account,
> keep custody, and vote by proof. That is the front door —
> `docs/deos/PROOF-OF-HOLDINGS.md` (primitive built + Lean-verified). Reach for this
> mirror only when you actually need the tokens to become spendable *inside* dregg or to
> back a bond; never to acquire weight.

## What this is

A **mirror** brings an external token (`$DREGG`, an SPL token launched on
Solana via pump.fun) *into* dregg's value layer as a first-class conserved
asset. Once mirrored, the asset is an ordinary dregg `AssetId` and is `Payable`:
it pays for on-substrate services (the execution-lease / ToolGateway) over the
*existing* rails, with no new kernel verb.

This is the asset analogue of the chain bridges already in this crate
(`midnight`, `ethereum`, `mina`): those settle dregg *state proofs* onto other
chains; the mirror brings another chain's *value* into dregg.

```text
  Solana (pump.fun SPL $DREGG)                    dregg value layer
  ────────────────────────────                    ─────────────────────────
  user locks N $DREGG  ──lock event──►  oracle/validator-set attests the lock
  into the lock vault                              │
                                                   ▼
                                       MirrorState::mint_against_lock + Effect::Mint
                                       (verify_lock → credit_lock → mints N
                                        mirror-$DREGG to recipient,
                                        well-debited dual ⇒ per-asset Σδ=0)
                                                   │
                                                   ▼  (ordinary dregg asset)
                                       Payable::pay / resolve_pay
                                                   │   Effect::Transfer (Σδ=0)
                                                   ▼
                                       pays an execution-lease / ToolGateway charge

  redeem:  Effect::Burn (mirror) ──unlock request──► oracle unlocks N $DREGG on Solana
```

## The two halves

### Mirror (Solana → dregg)

1. A holder locks `N` $DREGG into a lock vault on Solana (an SPL program /
   token account the bridge controls; the Solana-side program is now built —
   `solana-lock/` (`dregg-solana-lock`) — see the honest-gap section).
2. The oracle / validator-set observes the lock and produces a **threshold
   attestation** over the canonical lock payload
   `(lock_id, spl_mint, amount, dregg_recipient, epoch)`.
3. dregg verifies the attestation against the oracle key for that epoch, checks
   the `lock_id` has not been seen (replay), checks `amount ∈ [min, max]`, and
   credits `currently_locked += amount` (`MirrorState::verify_lock` →
   `credit_lock`; the finer-grained `record_escrow` raises `currently_locked`
   ahead of `draw_mint` drawing against it).
4. The mirror mints `N` mirror-$DREGG to the recipient via
   `MirrorState::mint_against_lock`, which produces the existing
   `Effect::Mint { target, slot: 0, amount }`. `Mint` is `Generative`: the
   asset's *issuer well* is debited as the conserving dual, so the turn is
   per-asset `Σδ = 0` (`turn/src/action.rs` — `Effect::Mint`, `LinearityClass`).

### Redeem (dregg → Solana)

1. The holder burns `N` mirror-$DREGG via the existing
   `Effect::Burn { target, slot: 0, amount }` (`Annihilative`; the `was_burn`
   disclosure binds into the receipt).
2. dregg decrements `live_supply` and `currently_locked` and emits a
   `SolanaUnlockRequest { spl_mint, amount, solana_recipient, redeem_id }`.
3. The oracle / validator-set unlocks `N` $DREGG from the lock vault on Solana
   to the named recipient.

## Conservation invariant

The mirror enforces, after every operation:

```
live_supply ≤ currently_locked
```

— the mirror-$DREGG in circulation inside dregg never exceeds the $DREGG locked
on Solana. Each attested lock raises `currently_locked` by exactly its amount
and authorizes exactly that much mint; each redeem lowers both
`live_supply` and `currently_locked` by the burned amount. A mint that would
push `live_supply` past `currently_locked` is rejected
(`MirrorError::InsufficientLocked`) — so an unbacked mint is structurally
impossible, *given a truthful attestation*. The kernel's per-asset `Σδ = 0` is
a separate, independent guarantee on the `Mint`/`Burn`/`Transfer` effects
themselves (the executor's conservation checker, not the mirror).

## Trust model — be honest

**This first slice is a TRUSTED-ORACLE / validator-set bridge.** The dregg side
trusts that the threshold attestation over a lock is honest: i.e. that a quorum
of the oracle set will not sign a lock that did not happen, and will not refuse
to sign a real unlock. This is the *same* trust posture as the `midnight`
bridge's `FederationAttestation` (a Schnorr/Ed25519 threshold signature
aggregated to one epoch key), reused here directly. An optional **watchtower**
(permissionless fraud challenge, as in `midnight_gateway::Watchtower`) can turn
"trust the quorum" into "trust the quorum *unless* anyone proves fraud", but it
still rests on at least one honest watching party and an on-Solana fraud oracle.

**The trustless path (BUILT to `ConsensusVerified` — anchored only):** a real
trustless mirror needs dregg to *verify the Solana lock itself*, not trust an
attestation. This is now the **Solana light client** route, and its
cryptography + consensus arithmetic are real (no longer a stub). The trustless
production entry is `verify_lock_proof_consensus_anchored`
(`bridge/src/solana_trustless.rs`): it takes **no caller-supplied stake table**
— the `EpochStakeTable` + authorized voters are *derived from Solana's own bank
state* and admitted only against a governance-pinned `WeakSubjectivityAnchor`.
It then checks that ≥ 2/3 of effective stake validly voted the claimed
`bank_hash` (real per-vote Ed25519 + stake-weighted sum + duplicate collapse),
that the `bank_hash` recomputes from its committed components (binding the
accounts hash + PoH tail), that the vault account's lock record is included in
that accounts hash, and — when required — that the PoH tick chain links to the
anchored checkpoint. It routes through the SAME `credit_lock` conservation
accounting as the trusted path.

⚠ **The anchor requirement is load-bearing, not decoration** (adversarial
audit, fixed 2026-07-12): `ConsensusVerified` over a *caller-supplied* stake
table was a forgery (an attacker's 1-key table clears its own "≥ 2/3");
the bare-table entries are now `#[cfg(test)]`/`test-utils`-gated and every
production path is anchored. "Trustless" here means the standard light-client
trust model: trustless over a pinned recent checkpoint the operator must
configure. Full design + the honest residuals:
`docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.

The **zk proof of the lock** (a SNARK/STARK attesting "account X held ≥ N $DREGG
locked at slot S under program P") is the *other* route and remains distinct: the
**Ethereum** side of this repo already has the STARK→SNARK→EVM *settlement*
pattern (`bridge/src/ethereum.rs` + the `chain/gnark` Groth16 wrap — real, with
a dev-ceremony trusted setup; residuals in `WRAP-NATIVE-HASH-DECISION.md`
§CURRENT STATE), but the *inbound* zk-proof-of-lock for Solana is **not**
reusable from the ETH settlement path.

**The honest gaps that remain on the trustless path.** The wire-format adapter
layer is built (real vote-`Transaction` parsing, bank-state-derived stake tables
with rotation, the real 16-ary accounts-hash format, the anchored PoH policy;
`bridge/src/solana_wire.rs` + `solana_provenance.rs`). What stays open:

- the governance-pinned anchor itself is the irreducible operator-configured
  trust root;
- the lock-record account layout is a deploy-time choice;
- bank-hash version extras (EAH slots, lt-hash) are unmodeled;
- the Option-B succinct wrapper (O(1) on-dregg verify) is the named
  optimization;

and three **open soundness suspects** on the consensus path itself (named and
unresolved at HEAD):

1. **Rotation counts votes without authorized-voter binding.** `rotate`
   (`bridge/src/solana_provenance.rs:706`) attests the next epoch's bank state
   with the *plain* `verify_supermajority` over the trusted table — its own
   doc-comment says so — while the anchored lock verification tallies with the
   authorized-voter-bound check. A rotation vote signed by a key other than the
   vote account's on-chain authorized voter still counts toward the ≥ 2/3.
2. **Stake-table derivation proves membership, never completeness.**
   `derive_stake_table` (`solana_provenance.rs:457`) verifies each *supplied*
   stake account's inclusion in the accounts hash, but nothing forces the
   supplied set to be the complete delegation set — a rotation that omits stake
   accounts shrinks the ≥ 2/3 denominator for every later epoch.
3. **"Finalized" is documented; exact-slot supermajority is checked.**
   `ConsensusEvidence.slot` is doc-labeled the slot the lock was *finalized* in
   (`bridge/src/solana_trustless.rs:73`), but the check is a supermajority of
   votes for that exact slot's bank hash — supermajority-voted is a weaker claim
   than rooted/finalized.

The `LockProofTrust` dial tells the caller exactly which level a verification
achieved, so the structural check (`StructureOnly`) can never be mistaken for
the consensus check.

## The payment path (end-to-end, real rails)

Once minted, mirror-$DREGG is an ordinary `AssetId`. Paying for a service is the
existing `Payable` desugar — the *same* `resolve_pay` route the SDK metered
ToolGateway charge uses (`sdk/src/tool_gateway.rs` →
`dregg_payable::resolve_pay`):

```rust
// bridged $DREGG (asset = mirror.asset) pays a lease/provider cell
let (action, _sig) = dregg_payable::resolve_pay(
    consumer_cell,     // holder of mirror-$DREGG
    mirror.asset,      // the mirrored AssetId
    lease_price,
    lease_provider,
    InvokeAuthority::Signature,
)?;
// → exactly one conserving Effect::Transfer { from, to, amount } (Σδ = 0)
```

No new verb, no `Effect::Invoke`, no new commitment field: the bridged asset
flows through the one verified value rail.

## What is real vs modeled (this slice)

- **Real:** the dregg-side mirror mechanism — attestation verification (Ed25519
  threshold sig + epoch key + replay dedup + amount bounds), the conservation
  invariant `live_supply ≤ currently_locked`, mirror-mint producing the real
  kernel `Effect::Mint`, redeem producing the real `Effect::Burn` + unlock
  request, and the proof that bridged $DREGG pays an execution-lease through
  `resolve_pay` (one conserving `Effect::Transfer`).
- **Trusted (this first slice):** the attestation itself (trusted-oracle). The
  trustless replacement is now built to `ConsensusVerified` (see above /
  `solana_trustless.rs` + `solana_consensus.rs`); this doc's *slice* is still the
  trusted-oracle path, with the light client as its now-real successor.
- **Real (trustless successor):** the Solana-consensus verification —
  stake-weighted Ed25519 vote check, bank-hash recompute/binding, sorted-Merkle
  accounts inclusion, PoH tick-chain linking — reaching
  `LockProofTrust::ConsensusVerified` **only via the anchored path** (a
  governance-pinned `WeakSubjectivityAnchor`; caller-supplied stake tables are
  test-gated — see the ⚠ note above) (`bridge/src/solana_trustless.rs`,
  `bridge/src/solana_consensus.rs`; design `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`).
  The three open soundness suspects above (rotation voter-binding, stake-table
  completeness, finalized-vs-voted) qualify this bullet.
- **Real:** the Solana-side lock-vault SPL program — `solana-lock/`
  (`dregg-solana-lock`: `processor.rs`, `state.rs`, `instruction.rs`,
  `attestation.rs`, `record.rs`, with `solana-lock/tests/lock_flow.rs` / `solana-lock/tests/unlock_flow.rs`).
- **Not built (named gaps):** the Option-B succinct zk-proof-of-lock route
  (the relayer consensus AIR; the wire-format adapter layer under it is built —
  `solana_wire.rs` real vote-`Transaction` parsing, `solana_provenance.rs`
  bank-state-derived stake tables + rotation, the real 16-ary accounts-hash
  format, the anchored PoH policy);
  the executor wiring that grants the mirror cell `EFFECT_MINT` authority
  over its own issuer well in a live `World` (the effect is produced here;
  minting it requires the mirror cell to hold mint authority — see
  `turn/src/executor/apply.rs`, `holds_mint_authority`).
