# The node & server-host

`dregg-node` is the federation node daemon: it hosts an agent cipherclerk, participates in
consensus, and serves a localhost HTTP/WS API for submitting turns and reading committed
state. Its package description: "Federation node daemon — hosts an agent cipherclerk,
participates in consensus, and serves a localhost API" (`node/Cargo.toml:11`).

This doc covers the node's request surface — the router, the turn-submission ingress paths,
the receipt SSE stream — and the **deos-host**, the userspace deos-js "private server" the
node can host inside its own process.

## Boot & serving

The `Run` subcommand (`node/src/main.rs:90`) starts the daemon. It binds `127.0.0.1` by
default; `--bind 0.0.0.0` exposes it to the network and logs a warning that the faucet /
cipherclerk / bridge endpoints become reachable (`node/src/main.rs:952`). The HTTP API
listens on `--port` (default `8420`, `node/src/main.rs:94`).

`run_node` builds the router via `api::router_with_cors(...)`, wraps it
`.into_make_service_with_connect_info::<SocketAddr>()` (so handlers see the peer IP), binds a
`tokio::net::TcpListener`, and runs `axum::serve(listener, app).with_graceful_shutdown(...)`
(`node/src/main.rs:939`, `:963`, `:1018`). On shutdown it persists state
(`node/src/main.rs:1024`).

## The router

`router_with_cors(state, enable_faucet, metrics_handle, cors_origins)` assembles three route
groups (`node/src/api.rs:1549`):

- **public_routes** — no auth (`node/src/api.rs:1565`): `/status`, `/health`,
  `/api/node/producer`, `/api/cells`, `/api/cell/{id}`, `/api/receipts`,
  `/api/server/{cell}/affordances` (deos-host discovery), `/api/turn/{hash}/proof`,
  `/api/events`, `/api/events/stream` (the SSE receipt stream, `node/src/api.rs:1623`),
  `/checkpoint/*`, `/pir/*`, and more.
- **protected_routes** — gated by the `require_auth` middleware layer
  (`node/src/api.rs:1784`): `/turn/submit`, `/turns/submit`, `/turns/submit-encrypted`,
  `/turns/aggregate`, `/ws`, `/cipherclerk/*`, `/intents*`, `/cells/*`, `/turn/atomic/*`,
  conditional-turn routes, and the merged ORGANS service routers (storage gateway,
  trustlines, channels, equivocation court, DKG — `node/src/api.rs:1765`–`:1782`).
- **path_aliases** — `/api/node/*` and `/api/turns/*` prefixed duplicates for bot/app
  compatibility (`node/src/api.rs:1794`).

Two rate limiters are constructed: passphrase/unlock (5 attempts / 60s,
`node/src/api.rs:1559`) and turn submission (`DEFAULT_TURN_RATE_LIMIT` = 60 / 60s per IP,
`node/src/api.rs:1241`, `:1562`). The turn limiter is cloned into each submit closure.

### Auth

`require_auth` (`node/src/api.rs:1318`) runs as a `middleware::from_fn_with_state` layer over
the protected routes. Before any passphrase is set, it restricts access to loopback (resolving
the real client IP through `X-Forwarded-For` only when `DREGG_TRUSTED_PROXIES` names the
direct peer, `node/src/api.rs:1338`–`:1359`). Once a `bearer_seed` exists, it requires
`Authorization: Bearer <token>` where the token is `blake3::derive_key("dregg-api-bearer-v1",
bearer_seed)` (`node/src/api.rs:1371`).

## Node state

`NodeState` is a `Clone` handle wrapping `Arc<RwLock<NodeStateInner>>` plus an `events_tx`
broadcast channel, a gossip handle, and the async prove pool (`node/src/state.rs:97`).
`read()`/`write()` return the tokio `RwLock` guards (`node/src/state.rs:1044`, `:1049`).

`NodeStateInner` (`node/src/state.rs:115`) holds the live system: `cclerk:
AgentCipherclerk` (identity, wallet, the receipt chain), `ledger: Ledger`, `store:
PersistentStore`, `unlocked: bool`, the intent pool, the consensus queue, pending
conditionals, federation registry, the SSE `event_log: VecDeque<CommittedEvent>`
(`node/src/state.rs:330`), `lean_producer_enabled` (`:217`), `full_turn_proving_enabled`
(`:205`), `solo_consensus` (`:356`), and `deos_server_surfaces` — the discoverable deos-host
affordance surfaces (`:362`).

`NodeEvent` (`node/src/state.rs:78`) is the broadcast payload: `Root`, `Revocation`,
`Receipt { hash }`, `InvalidBlocklaceBundle`, `Intent`. `subscribe_events()` hands out a
receiver; `emit(event)` fans out (errors ignored — no subscribers is fine,
`node/src/state.rs:1066`, `:1071`).

## Turn submission ingress

There are three distinct submit handlers, all rate-limited per real client IP and all
requiring `s.unlocked`.

### `/turns/submit` — signed-envelope ingress (the remote-agent path)

`post_submit_signed_turn` (`node/src/api.rs:3064`) is the canonical path for a remote agent's
turn. The body is a postcard-encoded `dregg_sdk::SignedTurn` (`node/src/api.rs:3079`). It:

1. Verifies `signed.signer.verify(turn_hash, signature)` and rejects with `accepted:false` on
   failure (`node/src/api.rs:3085`).
2. Derives the expected agent `CellId::derive_raw(signer, blake3("default"))` and rejects if
   `signed.turn.agent` does not match it (`node/src/api.rs:3098`).
3. Checks the optional `previous_receipt_hash` against the cipherclerk chain head
   (`node/src/api.rs:3124`).
4. Snapshots `pre_ledger`, builds a submit executor, and executes through the **one producer
   gate**: `executor_setup::execute_via_producer(executor, &signed.turn, &mut s.ledger,
   lean_producer_enabled)` (`node/src/api.rs:3146`–`:3154`).
5. On `TurnResult::Committed`, appends the receipt to the cipherclerk chain (rolling back the
   ledger to `pre_ledger` if the append fails, `node/src/api.rs:3177`), prepares an
   asynchronous rotatable attestation (`prepare_rotatable_turn`, `node/src/api.rs:3193`),
   pushes a committed event, drops the write lock, then **off the lock** enqueues async
   proving, emits `NodeEvent::Receipt`, gossips the turn, and submits the
   `TurnArtifactBundle` to the blocklace (`node/src/api.rs:3236`–`:3277`).

The response is `SubmitSignedTurnResponse { accepted, turn_hash, signer, action_count,
proof_status, has_witness, witness_count, error }` (`node/src/api.rs:399`).

### The one producer gate

`execute_via_producer` (`node/src/executor_setup.rs:120`) is the single entry every committed
turn passes through. When `lean_producer_enabled` is false it is exactly
`executor.execute(turn, ledger)` (the legacy Rust producer). When enabled it calls
`dregg_exec_lean::produce_via_lean`, making the verified Lean executor authoritative for the
covered turn-set: a Lean↔Rust disagreement on a covered turn is logged as a Rust bug (the
verified verdict was committed, not overridden, `node/src/executor_setup.rs:150`–`:167`); a
turn outside the covered set is explicitly fenced onto the legacy Rust path
(`node/src/executor_setup.rs:169`). The submit executor itself
(`new_submit_executor`) is a `TurnExecutor` with the `LeanShadowObserver` injected and block
height set to `Next` (`node/src/executor_setup.rs:261`).

### Proof status

Proving runs **off the commit path** (F-DOS-1). After commit the handler builds the rotatable
turn and reports `ActivityProofStatus::ProofPending` if witness material was produced,
`NotRequired` otherwise (`node/src/api.rs:3209`). `enqueue_async_proof` hands a `ProveJob` to
the prove pool and marks the receipt proof-pending; if no pool is installed the committed
receipt is left unattested (the executor already validated + committed it, so the commit is
sound, `node/src/api.rs:2671`–`:2700`). `ActivityProofStatus` variants: `Proved`,
`ProofPending`, `NotRequired`, `MissingPreState`, `ProofGenerationFailed`, `NotCommitted`
(`node/src/state.rs:514`).

### `/turn/submit` — the operator's thin local path

`post_submit_turn` (`node/src/api.rs:2741`) takes a JSON `SubmitTurnRequest` of action specs.
It **ignores the body's `agent`** and derives the agent from the node's own cipherclerk pubkey
(`CellId::derive_raw(s.cclerk.public_key(), blake3("default"))`) — closing a confused-deputy
attack where a caller targeted a victim cell's c-list with the operator's signature
(`node/src/api.rs:2763`–`:2771`). Each action is signed by the operator's cipherclerk over the
executor's verifying federation id (`federation_id_for_executor`, which on a solo node is
`blake3(pubkey)`, `node/src/api.rs:2790`). Response: `SubmitTurnResponse`
(`node/src/api.rs:389`).

### `/turns/submit-encrypted` — encrypted-turn ingress

`post_submit_encrypted_turn` (`node/src/api.rs:3521`) takes a raw postcard
`dregg_turn::EncryptedTurn` (octet-stream, not JSON). The executor's X25519 unsealer secret is
derived from the cipherclerk (`derive_symmetric_key("dregg-turn-unsealer-v1")`); the matching
public key is served at `GET /turns/encryption-key` so a sender can encrypt to the executor
(`node/src/api.rs:419`–`:441`). Only the receipt's `was_encrypted: true` bit is disclosed after
commit (`node/src/api.rs:445`).

### `/turns/aggregate` — cross-node bilateral aggregate

`post_aggregate_bundle` (`node/src/api.rs:3369`) accepts a canonical `SignedTurn` plus ≥2
independently-sourced per-cell `WitnessedReceipt` artifacts, runs `prove_aggregated_bundle`
to produce a real outer STARK proof, then `verify_aggregated_bundle` before returning. Per-WR
soundness gates (`require_scope2_witness`, `verify_bilateral_chain`) run inside the aggregator
(`node/src/api.rs:3355`–`:3368`).

## The receipt SSE stream — `GET /api/events/stream`

`events_stream` (`node/src/events.rs:141`) is the node's "nervous system" edge: a
Server-Sent-Events broadcast of every receipt the node commits. The **broadcast is only a
wake-up**; the cipherclerk receipt chain is the cursor's source of truth, so a lagged
broadcast subscriber loses nothing — the cursor re-reads the chain and catches up
(`node/src/events.rs:10`–`:16`, `:198`–`:204`).

Mechanics:
- Subscribe to the broadcast **before** reading the chain head, so anything committed between
  the snapshot and the first `recv()` still wakes the cursor (`node/src/events.rs:146`).
- A reconnecting client sends `Last-Event-ID: <chain_index>`; the stream resumes from the next
  chain entry (a fresh connection tails from the current head, `node/src/events.rs:152`–`:159`).
  Delivery is exactly-once per connection, at-least-once across reconnects
  (`node/src/events.rs:14`).
- The `unfold` loop drains the chain from `next` to the chain length, emitting each
  `ReceiptEvent` as an SSE `event("receipt")` with `id` = chain index; when drained it sleeps
  on the broadcast until the next commit (`node/src/events.rs:167`–`:207`).
- Filters: `?cell=<hex id>` (agent cell or any cell named by the receipt's emitted events /
  commit record) and `?kind=<effect kind>` (matched against effect summaries),
  `node/src/events.rs:112`–`:130`.
- A 30s keep-alive comment keeps proxies from closing the stream (`node/src/events.rs:210`).

`ReceiptEvent` (`node/src/events.rs:46`) carries `chain_index`, `receipt_hash`, `turn_hash`,
touched `cells`, effect `kinds`, `height`, `has_proof` (true if a witnessed receipt or
persisted full-turn proof exists **at send time** — proofs land asynchronously,
`node/src/events.rs:90`–`:96`), `finality`, `timestamp`, and the full canonical
`dregg_turn::TurnReceipt`.

A separate WebSocket handler (`/ws`, `node/src/ws.rs`) pushes the same `NodeEvent` topics and
accepts commands (subscribe, authorize); message/frame sizes are capped at 1 MiB / 256 KiB
(`node/src/ws.rs:29`–`:31`).

## The deos-host — a userspace private server inside the node

The deos-host (`node/src/deos_host.rs`, opt-in `deos-host` Cargo feature) lets the node host a
headless userspace deos-js "private server": a JS program that holds state in real cells on the
node's ledger and offers cap-gated affordances clients connect to and fire
(`node/src/deos_host.rs:1`–`:6`). The cockpit is then just one client of this; the node is a
headless deos-js-server-host.

### The persistent SpiderMonkey thread

deos-js links SpiderMonkey (`mozjs`); engine init is process-global + one-shot, and the engine
must never be dropped (re-init on a later thread is rejected `AlreadyShutDown`). So the host is
a **single long-lived thread** (`HOST_THREAD: OnceLock<mpsc::Sender<HostJob>>`,
`node/src/deos_host.rs:65`) owning one `JsRuntime` for the process lifetime, running every
hosted program over a job channel (`node/src/deos_host.rs:68`–`:100`). This makes hosting
repeatable: a setup program, then reactive ticks.

### The world sink

`NodeWorldSink` (`node/src/deos_host.rs:131`) implements `deos_js::WorldSink` over the node's
`NodeState`. It runs on the dedicated (non-worker) SpiderMonkey thread, so `block_on` over the
async `RwLock` is sound (`node/src/deos_host.rs:128`–`:130`). Its operations:
- `with_ledger` reads the live ledger (`node/src/deos_host.rs:143`).
- `fire_effects(agent, method, effects)` commits through
  `executor_setup::commit_effects_as` — the same producer-gated commit core the signed-turn
  HTTP ingress runs, minus the wire shell (`node/src/deos_host.rs:148`–`:156`).
- `mint_open_cell(seed, funding)` mints an open-perms funded cell directly onto the ledger —
  the GM superpower of standing up a world vessel, idempotent on an existing id
  (`node/src/deos_host.rs:166`–`:179`).

`commit_effects_as` (`node/src/executor_setup.rs:198`) is the factored core: it builds a `Turn`
under the agent's current nonce + chain head, sizes the fee to `estimate_cost`, executes
through `execute_via_producer`, and appends the committed `TurnReceipt` to the cipherclerk
chain — identical to the HTTP path's committed-turn semantics minus the signature/HTTP/gossip
shell (`node/src/executor_setup.rs:183`–`:247`).

### The boot

`host_server_program(state, seed_label, held, program_js)` (`node/src/deos_host.rs:193`):
1. Mints the server cell (open-perms, funded `1_000_000`, deterministic id from the seed
   label) onto the ledger, idempotent on re-boot (`node/src/deos_host.rs:199`–`:217`).
2. Dispatches a `HostJob` to the persistent thread, which resets the server registry, attaches
   an `AttachedApplet` as the server agent under `held`, evals the program (which registers
   cells + affordances + forks via `deos.server.*`), and drains the registry
   (`node/src/deos_host.rs:275`–`:301`).
3. Publishes the discoverable surface into `NodeState::deos_server_surfaces`: the root surface
   (instance-less affordances) keyed by the server cell, each forked instance keyed by its own
   cell carrying exactly the affordances scoped to it (`node/src/deos_host.rs:245`–`:265`).

`main.rs` invokes this on boot if `--deos-program <path>` is given (and the `deos-host` feature
is built — otherwise the flag is inert and warns, `node/src/main.rs:982`–`:1015`). The flag is
defined at `node/src/main.rs:260`.

### Discovery — `GET /api/server/{cell}/affordances`

`get_server_affordances` (`node/src/api.rs:2409`) is public: discovery confers no authority —
the cap tooth is the executor on the fire, not the read (`node/src/api.rs:1577`–`:1579`). It
looks up the cell's published specs, projects them per `?viewer=<auth label>` through the
proven attenuation lattice (`deos_reflect::AffordanceSurface::project_for`,
`node/src/api.rs:2432`–`:2450`), and returns the visible affordances plus the
`executor_federation_id` a client needs to build + sign a fire turn in one round-trip
(`node/src/api.rs:2425`–`:2456`). A client then fires an affordance through the node's
`/turns/submit` ingress as a real verified turn.
