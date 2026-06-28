# Token Mirror Bridge — mirroring a Solana/pump.fun SPL token into dregg's value layer

## What this is

A **mirror** brings an external token (`$DREGG`, an SPL token launched on
Solana via pump.fun) *into* dregg's value layer as a first-class conserved
asset. Once mirrored, the asset is an ordinary dregg `AssetId` and is `Payable`:
it pays for DreggNet services (the execution-lease / ToolGateway) over the
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
                                       MirrorState.observe + Effect::Mint
                                       (mints N mirror-$DREGG to recipient,
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
   token account the bridge controls; the Solana-side program is *named, not
   built here* — see the honest-gap section).
2. The oracle / validator-set observes the lock and produces a **threshold
   attestation** over the canonical lock payload
   `(lock_id, spl_mint, amount, dregg_recipient, epoch)`.
3. dregg verifies the attestation against the oracle key for that epoch, checks
   the `lock_id` has not been seen (replay), checks `amount ∈ [min, max]`, and
   credits `currently_locked += amount`.
4. The mirror mints `N` mirror-$DREGG to the recipient via the existing
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

**The trustless path (named, not built):** a real trustless mirror needs dregg
to *verify the Solana lock itself*, not trust an attestation. Two routes:

- A **Solana light client** in dregg: verify Tower BFT / PoH consensus (a large
  Ed25519 vote-signature set) plus an inclusion proof of the lock account's
  post-state in Solana's accounts hash. This is materially harder than an
  Ethereum light client: Solana has no compact header chain like Ethereum's
  MPT-rooted headers, and the validator set / vote accounting is large.
- A **zk proof of the lock**: a SNARK/STARK attesting "account X held ≥ N
  $DREGG locked at slot S under program P". The **Ethereum** side of this repo
  already has the STARK→SNARK→EVM *settlement* pattern
  (`bridge/src/ethereum.rs`, gap = the gnark Groth16 STARK-verifier circuit);
  the *inbound* zk-proof-of-lock for Solana is a distinct, unbuilt artifact and
  is **not** reusable from the ETH settlement path. This is the honest gap.

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
- **Modeled / trusted:** the attestation itself (trusted-oracle, not yet a
  Solana light client or zk-proof-of-lock).
- **Not built (named gaps):** the Solana-side lock-vault SPL program; the
  trustless Solana light client / inbound zk-proof-of-lock; the executor wiring
  that grants the mirror cell `EFFECT_MINT` authority over its own issuer well
  in a live `World` (the effect is produced here; minting it requires the
  mirror cell to hold mint authority — see `turn/src/executor/apply.rs`,
  `holds_mint_authority`).
