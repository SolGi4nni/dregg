# The SDK & embedding

The agent SDK is split into two crates: **`dregg-sdk`** (the offline core) and
**`dregg-sdk-net`** (the networked layer built on top of it).

`dregg-sdk` is the OFFLINE CORE: it carries no `tokio`/`reqwest`/`dregg-wire`/
`dregg-captp`/`dregg-federation` networking surface and builds on `wasm32`
(`sdk/src/lib.rs:100`). It manages keys, tokens, turn-building, and proof
generation entirely client-locally. `dregg-sdk-net` adds CapTP, the silo/HTTP
clients, the hosted-mailbox crank, receipt event streams, PIR discovery, and the
wire codec, and depends on the core crate (`dregg-sdk-net/src/lib.rs:1`).

## Trust level

The core crate "operates at the **CLIENT-LOCAL** trust level": it runs on the
user's device, manages private keys/token chains/proof generation locally, and
trusts only the user's own device and the SDK's correct implementation
(`sdk/src/lib.rs:24`). It does NOT trust remote silos (verified via TLS + receipt
chains), federation state (verified via attested roots + STARK proofs), or other
agents (mediated by capabilities) (`sdk/src/lib.rs:43`).

## Which executor runs a deployed turn

The SDK builds and signs turns; the federation node executes them
(`sdk/src/lib.rs:3`). On native builds the SDK's `AgentRuntime` makes the
**verified Lean executor the authoritative state producer** by default (THE SWAP),
runtime-gated by `DREGG_LEAN_PRODUCER` (`sdk/Cargo.toml:23`,
`sdk/src/runtime.rs:35` `lean_producer_env_enabled`). The Rust `TurnExecutor` is
demoted to a parallel differential cross-check; a covered Lean↔Rust disagreement
is surfaced as a Rust bug, not a fallback (`sdk/src/runtime.rs:461`
`AgentRuntime::run_turn`). The one opt-out is the `no-lean-link` platform feature
(wasm32/zkvm — targets that cannot link `libdregg_lean.a`)
(`sdk/Cargo.toml:103`); there the legacy Rust producer runs.

## The two public nouns

The crate root advertises a deliberately small headline surface
(`sdk/src/lib.rs:165`):

- **`Receipt`** — proof-of-execution for one committed turn, with a composed
  STARK lazily attached (`sdk/src/lib.rs:177`, `sdk/src/receipt.rs:89`).
- **`AttestedHistory`** — the light-client artifact: the verdict from verifying
  ONE succinct whole-history aggregate, re-witnessing nothing
  (`sdk/src/lib.rs:182`, re-exported from `dregg-lightclient`).

## The authorized turn flow

The public turn shape is `identity → runtime.turn() → typed verbs → .sign() →
.submit() → Receipt` (`sdk/src/lib.rs:166`).

- **`AgentCipherclerk`** (`sdk/src/cipherclerk.rs:1011`) is the agent's
  cryptographic clerk / credential holder: an Ed25519 signing identity
  (`signing_key`/`public_key`), a wallet of `HeldToken`s, the receipt chain
  (`receipt_chain`), an optional IVC builder, stealth keys, and local sovereign
  cell state. `AgentCipherclerk::new()` generates a random Ed25519 identity
  (`sdk/src/cipherclerk.rs:1122`). The legacy name "wallet" was a poor fit —
  dregg clerks mostly manage capabilities, not balances
  (`sdk/src/cipherclerk.rs:14`). Aliased `AgentCClerk` (`sdk/src/lib.rs:219`).

- **`AgentRuntime`** (`sdk/src/runtime.rs:186`) ties together the cipherclerk
  (behind `Arc<RwLock>`), a local ledger (`Arc<Mutex<Ledger>>`), and a
  `TurnExecutor`. `AgentRuntime::new` funds the agent's cell with 1,000,000
  computrons and installs the real STARK-backed witnessed-predicate registry so
  `SenderAuthorized { PublicRoot }` enforces for real
  (`sdk/src/runtime.rs:245`, `sdk/src/runtime.rs:78`
  `executor_with_real_verifiers`).

- **`TurnBuilder`** (`sdk/src/turns.rs:55`) is the typed verb surface opened by
  `runtime.turn()` (`sdk/src/runtime.rs:525`). Verbs: `transfer`/`transfer_from`
  (`Effect::Transfer`), `write`/`write_u64` (`Effect::SetField`), `grant`
  (`Effect::GrantCapability`), `increment_nonce`, `reveal` (a 32-byte preimage
  `WitnessBlob` covered by the signature), `effect`/`effects` (splice in
  prebuilt effect lists from the `factories`/`polis`/`program` plan builders)
  (`sdk/src/turns.rs:117`). `.on(target)` and `.as_cell(cell, fee)` select the
  acting mode (`sdk/src/turns.rs:90`, `sdk/src/turns.rs:98`).

- **`.sign()`** refuses an empty turn, then binds the action to the identity's
  Ed25519 key over the canonical federation-bound signing message
  (`sdk/src/turns.rs:200`), yielding **`AuthorizedTurn`**. After this point "an
  unauthorized act is inexpressible here" (`sdk/src/turns.rs:18`).
  `AuthorizedTurn::explain()` renders the clerk's faithful, total reading of
  exactly what was signed — the anti-blind-signing affordance
  (`sdk/src/turns.rs:235`, delegating to `crate::explain::explain_action`).

- **`.submit()`** executes and returns a `Receipt`. An agent/`On` turn is
  agent-paid and appended to the identity's receipt chain; an `as_cell` turn is
  paid by the cell and belongs to the cell's own history
  (`sdk/src/turns.rs:250`).

The legacy `execute*` methods are the same authorized flow without the staging
surface: `execute` (agent pays, fee 10,000), `execute_on` (agent pays, action
targets another administered cell), `execute_as` (the cell pays from its own
balance — the one-time factory adopt bootstrap) (`sdk/src/runtime.rs:692`,
`sdk/src/runtime.rs:744`, `sdk/src/runtime.rs:721`). All carry
`#[must_use = "dropping the TurnReceipt silently discards proof of execution"]`.

### The raw escape hatch

Raw `Action`/`Turn` construction — including the genesis-only
`Authorization::Unchecked` — lives only behind the sealed `raw` module
(`sdk/src/raw.rs:1`). It is sanctioned for three uses only: genesis
construction, the signing flow itself (zeroing the authorization field before
computing the signing message via `unsigned_action`), and sovereign/proof-
carrying turns whose authority is a witness/STARK, not a signature
(`sdk/src/raw.rs:9`). An action built here and submitted as-is presents no
credential (`sdk/src/raw.rs:64`).

## Sub-agents (attenuated delegation, executor-enforced)

`AgentRuntime::spawn_sub_agent` / `spawn_sub_agent_scoped` create a fresh
cipherclerk + cell with capabilities derived from the parent's token, narrowed
by an `Attenuation` (`sdk/src/runtime.rs:833`, `sdk/src/runtime.rs:850`). The
sub-agent's ENFORCED credential is a public-key biscuit granting
`service(sub_cell, method)` for exactly the allowed method verbs, minted under a
fresh issuer keypair whose public key is recorded as the sub-cell's
`verification_key` (`sdk/src/runtime.rs:135` `mint_subagent_cap_token`,
`sdk/src/runtime.rs:963`). The worker presents the biscuit as
`Authorization::Token` with a `TokenKeyRef::BiscuitIssuer` anchor on every turn,
so the EXECUTOR's `verify_token_authorization` — not an out-of-band
`cap.verify()` — is the admission gate: a method outside the granted set is
rejected with `TokenInsufficientCapability` (`sdk/src/runtime.rs:1163`
`SubAgent::cap_authorization`, `sdk/src/runtime.rs:1194` `execute_method`). Each
sub-agent maintains its own receipt chain via `previous_receipt_hash`, seeded
into the fresh per-call executor so chained worker turns hold across calls
(`sdk/src/runtime.rs:1232`).

## `DreggEngine` — the no-I/O embed core

`embed::DreggEngine` (`sdk/src/embed.rs:211`) is a zero-I/O, "sans-io" facade
over the turn executor and ledger for embedding dregg into any existing service
without its networking/consensus/storage (`sdk/src/embed.rs:1`). All methods are
synchronous; the caller handles transport, persistence, and scheduling. It is
NOT `Sync` by default (wraps a `Ledger`, a `BTreeMap`); wrap in `Mutex`/`RwLock`
to share (`sdk/src/embed.rs:209`).

`EngineConfig` deliberately does NOT implement `Default`: the `timestamp` field
is load-bearing for proof freshness, so callers must use `EngineConfig::new(ts)`
(production) or `EngineConfig::for_testing()` (`sdk/src/embed.rs:122`). It also
carries `costs` (`ComputronCosts`), `federation_id`, `block_height`, and
`max_proof_age_secs` (default 300s) (`sdk/src/embed.rs:131`).

The engine's bytes-oriented API:

- **Turn execution**: `execute_turn_bytes` (postcard-decode then execute),
  `execute_turn`, `validate_turn` (dry-run, no apply), `estimate_cost`
  (`sdk/src/embed.rs:257`–`296`).
- **Proof gen/verify**: `prove_presentation` (builds a
  `BridgePresentationBuilder`, refuses to generate with timestamp 0 rather than
  fail silently at verification) (`sdk/src/embed.rs:309`);
  `verify_presentation_bytes` / `verify_presentation_against` (delegate to the
  canonical `present::verify_proof_complete`: zero-root reject, STARK validity,
  root binding, action binding, freshness, composition commitment, Production
  tier) (`sdk/src/embed.rs:375`, `sdk/src/embed.rs:406`);
  `verify_membership_proof` / `verify_membership_proof_outcome` (membership-only,
  no action/freshness binding) (`sdk/src/embed.rs:446`).
- **Token ops** (pure crypto): `mint_token` and `attenuate_token` over
  `em2_`-encoded `MacaroonToken`s (`sdk/src/embed.rs:505`, `sdk/src/embed.rs:517`).
- **State management**: `state_snapshot` serializes the ledger as postcard
  `Vec<Cell>` plus a trailing 32-byte BLAKE3 integrity hash; `load_state`
  recomputes and compares the hash, returning `EmbedError::IntegrityCheckFailed`
  on tamper (`sdk/src/embed.rs:543`, `sdk/src/embed.rs:558`). The caller persists
  the bytes wherever it likes.
- **Federation root / executor config**: `set_federation_root`,
  `set_block_height`, `set_timestamp`, `executor_mut`, `ledger_mut`. Note:
  `ledger_mut` and `set_federation_root` carry in-source `AUDIT[P2]` notes —
  they expose raw ledger mutation and operator-trusted root setting that bypass
  executor invariants; both assume the caller already has full process trust
  (`sdk/src/embed.rs:592`, `sdk/src/embed.rs:616`).

`EmbedError` covers turn decode/rejection, state serde, integrity-check failure,
token, and proof gen/decode errors (`sdk/src/embed.rs:69`).

## Receipts and full-turn proofs

A `Receipt` (`sdk/src/receipt.rs:95`) wraps the wire-level `TurnReceipt`
(deref-transparent) and a lazily-attachable `TurnProof` (`OnceLock`). A receipt
is born proofless — the commit decision is the executor's; the STARK is additive
attestation (`sdk/src/receipt.rs:1`). `attach_proof` is idempotent-at-first-
writer and refuses a proof whose `turn_hash` differs from the receipt's
(`sdk/src/receipt.rs:127`). `proof_or_attach` produces-and-attaches lazily, also
rejecting a wrong-turn proof (`sdk/src/receipt.rs:138`).

`TurnProof` wraps a `FullTurnProof`: a single composed STARK that in one
verification covers the state transition (Effect VM), authorization (derivation
chain), c-list membership, conservation, and non-revocation
(`sdk/src/receipt.rs:32`, `sdk/src/full_turn_proof.rs:1`). The prove/verify entry
points re-exported at the crate root are `prove_full_turn`, `verify_full_turn`,
`verify_full_turn_bound` (the freshness-critical no-double-spend verifier),
`prove_turn_self_sovereign`, and `prove_turn_self_sovereign_rotated`
(`sdk/src/lib.rs:277`, `sdk/src/full_turn_proof.rs:2985`,
`sdk/src/full_turn_proof.rs:3408`). The rest of the composition API is plumbing
behind `full_turn_proof`.

## Verification modes

`AgentCipherclerk::authorize` presents credentials in one of three
`VerificationMode`s (`sdk/src/cipherclerk.rs:92`): **Trusted** (local Datalog
evaluation, full visibility), **SelectiveDisclosure** (STARK proof revealing only
chosen facts by `FactIndex`), and **FullyPrivate** (STARK revealing only
allow/deny). Per-fact disclosure (`FactDisclosure`) supports reveal, predicate-
over-value, committed-threshold (hidden threshold behind a Poseidon2 commitment),
arithmetic predicate over multiple values, and hidden
(`sdk/src/cipherclerk.rs:127`).

## The tool gateway (ORGAN 4)

`tool_gateway::ToolGateway` turns an inbound untrusted tool-call into a cap-
gated, metered, receipted DELEGATED turn — or an in-band refusal — through one
method, `invoke` (`sdk/src/tool_gateway.rs:1`, `sdk/src/lib.rs:140`). The gateway
holds no policy; the grantor pins a `ToolGrant` mandate at delegation time. Both
enforcement surfaces are load-bearing: `deleg_admit` decides SCOPE ∧ DEADLINE ∧
RATE in-band before submission (a false verdict is a `GatewayRefusal` error, no
turn submitted), and `mandate_program` (`FieldLte { calls_made ≤ rateLimit }` ∧
`Monotonic`) binds the rate ceiling into the committed transition so the executor
rejects an over-rate write even if the in-band check was bypassed
(`sdk/src/tool_gateway.rs:28`). `deleg_admit` is the byte-faithful Rust mirror of
the verified Lean predicate in `Dregg2/Apps/ToolAccessDelegation.lean`
(`sdk/src/tool_gateway.rs:13`). It also offers a data-plane shape:
`enqueue`/`drive_executor`/`resolve` route the admitted call as a `RoutedHandle`
promise with a `DeliveryReceipt` (`sdk/src/tool_gateway.rs:48`).

## Additional core modules

The crate root re-exports a wider compatibility surface (`sdk/src/lib.rs:224`),
backed by these app/organ modules:

- **`factories`** — settlement-cell plan builders (escrow, obligation, bridge
  lock) emitting effect lists that ride `runtime.turn().effects(..)`
  (`sdk/src/lib.rs:243`).
- **`flashwell`** — the flash-well ring builder (zero-duration credit;
  settlement enforced by the well's installed program) (`sdk/src/lib.rs:249`).
- **`council_seal` + `sealed_governance`** — the threshold council seal (DKG
  group-key hashed-ElGamal) and the sealed-bid auction / unlinkable sealed-ballot
  ceremonies over it: eligibility via anonymous nullifier, double-votes/early-
  peeks/ballot-substitutions fail-closed (`sdk/src/lib.rs:256`,
  `sdk/src/lib.rs:107`).
- **`mnemonic`** — `generate_mnemonic` for identity backup (`sdk/src/lib.rs:253`).
- **`verify`** — standalone credential verification (`verify_authorization_proof`,
  `verify_committed_threshold`) (`sdk/src/lib.rs:291`).
- **`witness_artifact`** — receipt-witness artifact codecs (DWR1 format)
  (`sdk/src/lib.rs:284`).
- Plus `identity`, `device_pairing`, `guardian_rotation`, `committed_turn`,
  `hatchery_mint`, `job_escrow`, `trustline`, `polis`, `privacy`, `program`,
  `hints_onboarding`, `profiles` (non-wasm) (`sdk/src/lib.rs:105`).

## The networked layer: `dregg-sdk-net`

`dregg-sdk-net` adds the transport/distributed surface over the offline core
(`dregg-sdk-net/src/lib.rs:1`):

- **`NetClerk`** (`dregg-sdk-net/src/lib.rs:99`) pairs an `AgentCipherclerk` with
  a `CapTpClient` (the CapTP state was lifted off the core so it stays net-free
  and wasm-buildable, `dregg-sdk-net/src/lib.rs:20`). It hosts the CapTP
  convenience methods — `share_capability` (export a `dregg://` sturdy ref),
  `accept_capability` (enliven a URI to a `LiveRef`), `delegate_offline` (a
  `HandoffCertificate` for out-of-band delegation) — and the federation HTTP
  methods `register_with_federation`, `deregister_from_federation`, and
  `deploy_program` (POSTs a postcard `CircuitDescriptor` to `/programs/deploy`,
  returns the 32-byte VK hash) (`dregg-sdk-net/src/lib.rs:146`,
  `dregg-sdk-net/src/lib.rs:187`, `dregg-sdk-net/src/lib.rs:288`).

- **`RemoteRuntime`** (`dregg-sdk-net/src/remote.rs:140`) holds the agent's
  cipherclerk locally but runs all state reads and authoritative execution on a
  node base URL. `connect` derives the agent cell from the pubkey; federation-id
  binding is discovered lazily and cached (`dregg-sdk-net/src/remote.rs:152`,
  `dregg-sdk-net/src/remote.rs:193`). It mirrors the local `TurnBuilder` verbs
  via `RemoteTurnBuilder` (`dregg-sdk-net/src/remote.rs:285`).

- **`SiloClient`** (`dregg-sdk-net/src/client.rs:71`) is a TCP client to a remote
  silo for cross-silo authorization: connect/handshake (Hello/Welcome), present
  tokens with ZK proofs, and check revocation via non-membership proofs. The
  federation root used for verification MUST come from the authenticated
  handshake, not from token-derived data; `connect_pinned` adds MITM protection
  against a chosen root (`dregg-sdk-net/src/client.rs:78`,
  `dregg-sdk-net/src/client.rs:137`).

- **`WireCodec`** (`dregg-sdk-net/src/wire_codec.rs:16`) is the networked face of
  `DreggEngine`: no-I/O `encode`/`decode` of the dregg wire protocol (4-byte LE
  length-prefix framing) plus server-side `process_message` (Hello→Welcome,
  PresentToken→PresentationResult, RequestAttestedRoot→AttestedRoot, Ping→Pong)
  over an engine (`dregg-sdk-net/src/wire_codec.rs:45`).

- Other modules: `captp_client` (sturdy refs, GC, handoff, pipelining),
  `channels`, `names` (petname resolution), `mailbox` (the hosted-mailbox crank),
  `discharge` (third-party caveat discharge), `discovery`
  (`discover_intents_privately`, PIR), `events` (`ReceiptStream`), `deos_server`
  (private-server affordance discover + fire) (`dregg-sdk-net/src/lib.rs:31`).
