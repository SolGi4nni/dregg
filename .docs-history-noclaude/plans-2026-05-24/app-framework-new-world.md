# App Framework: New World Architecture

How the app-framework crate and the shared app infrastructure must evolve to support the upgraded apps and the 5 new apps identified in `app-upgrade-roadmap.md`.

## Current State

`app-framework/src/` provides:
- `server.rs` — AppServer builder (health, CORS, admin auth, persistence)
- `auth.rs` — AdminAuth extractor (Bearer token)
- `persistence.rs` — JsonPersistence (atomic write-tmp-rename)
- `dispute.rs` — Disputable trait + OptimisticSettlement

Apps use these for HTTP serving, admin endpoints, and state persistence. But the new world has capabilities that the framework doesn't expose yet.

## What Apps Need Now

### 1. Queue Integration (ALL apps)

Every app that processes requests should use programmable queues instead of direct HTTP handlers for non-trivial operations. The framework should make this ergonomic.

```rust
impl AppServer {
    /// Attach a programmable queue to an endpoint.
    /// Incoming requests are enqueued (with deposit), processed by the queue program,
    /// and results returned asynchronously.
    pub fn with_queue_endpoint(
        self,
        path: &str,
        program: QueueProgram,
        handler: impl Fn(QueueEntry) -> Effect + Send + Sync,
    ) -> Self { ... }
}
```

**Who needs this:** compute-exchange (job submission), bounty-board (qualification queue), gallery (bid submission), orderbook (order matching queue).

### 2. Ring Trade Participation (DeFi apps)

DeFi apps (AMM, orderbook, lending, stablecoin) should be able to register as participants in the ring trade solver. The framework should provide:

```rust
/// Register this app's capabilities with the intent engine.
/// Enables automatic participation in multi-party ring trades.
pub trait RingTradeParticipant {
    /// What this app offers (e.g., AMM offers token swaps)
    fn exchange_offers(&self) -> Vec<ExchangeSpec>;
    /// Settle a ring trade leg involving this app
    fn settle_leg(&mut self, settlement: Settlement) -> Result<(), AppError>;
}
```

**Who needs this:** AMM (liquidity provision as offer), orderbook (limit orders as offers), lending (collateral swaps), stablecoin (minting as offer).

### 3. Blinded Queue Support (Fair Distribution apps)

Apps that distribute resources fairly (gallery auctions, bounty-board assignments, compute-exchange job matching) should use blinded queues.

```rust
/// Framework support for fair unique withdrawal.
pub struct FairDistributionEndpoint {
    queue: BlindedQueue,
    distribution: FairDistribution,
    /// HTTP endpoints auto-generated: POST /commit, POST /consume, GET /status
}
```

**Who needs this:** gallery (sealed-bid reveal), compute-exchange (fair job assignment), bounty-board (fair reviewer selection).

### 4. CapTP-Native Endpoints

Instead of HTTP-only, apps should be accessible via CapTP (sturdy refs, pipelining). The framework should support dual-protocol serving.

```rust
impl AppServer {
    /// Expose this app's functionality via CapTP (alongside HTTP).
    /// External systems can interact via sturdy refs without HTTP.
    pub fn with_captp(self, swiss_table: SwissTable) -> Self { ... }
    
    /// Register a cell-based endpoint (accessible via capability, not just URL).
    pub fn with_cap_endpoint(
        self,
        cell_id: CellId,
        handler: impl Fn(Action) -> Effect + Send + Sync,
    ) -> Self { ... }
}
```

**Who needs this:** ALL apps. CapTP access means the Discord bot, CLI, other apps, and cross-federation users can interact without HTTP.

### 5. Executor Delegation Support

Apps that serve many users (AMM, orderbook) should be able to act as delegated executors — batching user turns for amortized proving.

```rust
/// Framework support for acting as a delegated executor.
pub trait BatchExecutor {
    /// Collect pending turns from delegated clients
    fn collect_batch(&mut self, max_size: usize) -> Vec<ClientTurnRequest>;
    /// Execute and prove the batch
    fn execute_batch(&mut self, batch: Vec<ClientTurnRequest>) -> BatchExecution;
}
```

**Who needs this:** AMM (batch swaps), orderbook (batch matching), lending (batch interest accrual).

### 6. Multi-Group Awareness

Apps in the unified lace may serve users from MULTIPLE reference groups. The framework should handle group-aware routing.

```rust
impl AppServer {
    /// Serve users from multiple reference groups.
    /// DFA routing determines which group a request belongs to.
    pub fn with_multi_group(self, groups: Vec<GovernedReferenceGroup>) -> Self { ... }
}
```

**Who needs this:** nameservice (cross-federation resolution), governed-namespace (multi-group directory), identity (credentials valid across groups).

### 7. Nameservice Registration

Every app should auto-register in the nameservice on startup, making it discoverable.

```rust
impl AppServer {
    /// Register this app in the federation's nameservice on startup.
    /// Deregisters on shutdown.
    pub fn with_name(self, name: &str, tags: &[&str]) -> Self { ... }
}
```

**Who needs this:** ALL apps. `dregg name resolve amm` → finds the AMM. `dregg namespace discover --tag defi` → finds all DeFi apps.

### 8. Multi-Asset Fee Acceptance

Apps should be able to accept fees in various tokens, not just computrons.

```rust
impl AppServer {
    /// Configure accepted payment denominations.
    pub fn with_fee_policy(self, policy: FeePolicy) -> Self { ... }
}
```

**Who needs this:** ALL apps that charge fees (compute-exchange, relay, nameservice).

### 9. Dispute Integration (Enhanced)

The existing `Disputable` trait works but should integrate with the blinded queue (for anonymous dispute filing) and the ring trade solver (for multi-party dispute resolution).

```rust
/// Enhanced dispute that works with blinded evidence submission.
pub trait BlindedDisputable: Disputable {
    /// File a dispute with blinded evidence (commitment, revealed later).
    fn file_blinded_dispute(&mut self, evidence_commitment: [u8; 32]) -> DisputeId;
    /// Reveal evidence (after challenge window opens).
    fn reveal_evidence(&mut self, id: DisputeId, evidence: Evidence, randomness: [u8; 32]) -> Result<(), DisputeError>;
}
```

### 10. Store-and-Forward Inbox

Apps serving offline users should have built-in inbox support — messages queue while the user is offline, delivered on reconnect.

```rust
impl AppServer {
    /// Enable inbox for offline users.
    /// Messages to offline users are queued and delivered on reconnect.
    pub fn with_inbox(self, capacity_per_user: usize, ttl_blocks: u64) -> Self { ... }
}
```

**Who needs this:** gallery (bid notifications), bounty-board (assignment notifications), identity (credential issuance).

## Implementation Priority

### Phase 1: Foundational (enables ALL app upgrades)
1. Queue endpoint integration (with_queue_endpoint)
2. CapTP-native serving (with_captp)
3. Nameservice auto-registration (with_name)
4. Multi-asset fees (with_fee_policy)

### Phase 2: DeFi-specific
5. Ring trade participant trait
6. Batch executor support
7. Multi-group awareness

### Phase 3: Privacy-specific
8. Blinded queue endpoints (FairDistributionEndpoint)
9. Blinded dispute (BlindedDisputable)
10. Store-and-forward inbox

## Cross-App Composition Patterns

### Pattern A: DeFi Ring
```
User intent: "swap 100 USDC for ETH"
  → Intent engine finds ring: AMM has ETH, Orderbook has buyer at good price
  → Ring solver produces atomic settlement
  → AppServer's RingTradeParticipant.settle_leg() executes on each app
  → One STARK proof covers the entire multi-app settlement
```

### Pattern B: Credential-Gated Access
```
User wants to trade on orderbook:
  → DFA router classifies: /orderbook/* requires "verified" credential
  → Identity app's CapTP endpoint validates credential (ZK proof)
  → Router grants access to orderbook endpoints
  → All apps share the same DFA commitment (governance-controlled)
```

### Pattern C: Fair Auction with Delivery
```
Gallery auction ends:
  → Blinded queue reveals winner (fair unique withdrawal)
  → Winner's capability grant = right to claim the NFT
  → Compute-exchange job queue: render high-res version for winner
  → Store-and-forward: deliver NFT to winner's inbox (even if offline)
  → Dispute window: if NFT not delivered, slash gallery's bond
```

### Pattern D: Cross-Group Liquidity
```
AMM on group A has ETH/USDC pool
Orderbook on group B has ETH/BTC orders
User on group C wants BTC for USDC:
  → Cross-reference: C references A and B
  → Ring solver finds: USDC→ETH (via A's AMM) + ETH→BTC (via B's orderbook)
  → Atomic settlement via cross-group proof delivery (DagDeliveredProof)
  → One multi-group STARK covers the entire cross-chain swap
```

## What Changes in app-framework/

```
app-framework/src/
  server.rs          — extend with queue, captp, nameservice, multi-group builders
  auth.rs            — keep (admin auth still needed)
  persistence.rs     — keep (JSON persistence still useful)
  dispute.rs         — extend with BlindedDisputable
  queue_endpoint.rs  — NEW: queue-backed endpoint handler
  captp_server.rs    — NEW: CapTP serving alongside HTTP
  ring_trade.rs      — NEW: RingTradeParticipant trait + solver integration
  batch_executor.rs  — NEW: BatchExecutor trait + delegation integration
  discovery.rs       — NEW: nameservice auto-registration + deregistration
  fee_policy.rs      — NEW: multi-asset fee configuration
  inbox.rs           — NEW: store-and-forward inbox per user
```

## Migration Path for Existing Apps

Each app migrates incrementally:
1. Add `with_name("appname", &["tag1", "tag2"])` to AppServer builder (5 min)
2. Add `with_captp(swiss_table)` for CapTP access (30 min)
3. Convert high-value endpoints to queue-backed (1-2 hours per endpoint)
4. Implement RingTradeParticipant if DeFi (2-4 hours)
5. Add blinded queue for fair distribution scenarios (2-4 hours)
6. Add executor delegation for batch proving (4-8 hours)

Total per app: 1-2 days for full upgrade. ~52 agent-hours for all apps combined (matches roadmap estimate).
