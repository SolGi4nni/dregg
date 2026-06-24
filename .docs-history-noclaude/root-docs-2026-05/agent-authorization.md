# `dregg`: Capability-Based Authorization for AI Agents

## The Problem

AI agents need to act in the world -- call APIs, spend money, delegate to sub-agents, coordinate with other agents. Every major framework punts on authorization: OpenAI function calling has no permission model at all, Anthropic tool use relies on the host application, and LangChain defers to "trust the developer." The result is binary: either the agent can do everything or nothing.

Real-world agent deployments need six properties that identity-based auth cannot provide:

1. **Attenuation** -- give a sub-agent only what it needs for THIS task
2. **Budget bounds** -- max $50, max 100 API calls, expires in 1 hour
3. **Delegation without the issuer** -- sub-agent grants to tools without calling home
4. **Instant revocation** -- if an agent goes rogue, kill its capabilities NOW
5. **Audit trail** -- what was done with what authority, cryptographically
6. **Privacy** -- agent A calls agent B's API without B learning A's identity

`dregg` solves all six with one coherent primitive: cryptographic capability tokens verified by zero-knowledge proof.

## How It Works

### Capabilities, Not Identities

Each agent holds a **c-list** (`cell/src/capability.rs`) -- an enumerable set of unforgeable references to resources. No ambient authority exists. An agent can only reach what it explicitly holds a capability for. The `CapabilitySet::attenuate()` method enforces that you can never grant MORE than you hold -- permissions only narrow, never amplify.

### Macaroon Tokens with Typed Caveats

Authorization tokens (`token/src/dregg_caveats.rs`) are HMAC-chained macaroons with 16 typed caveat slots:

- **Service/App scope** -- which APIs the token can access
- **ValidityWindow** -- not-before / not-after timestamps
- **Budget** -- named budget with class, limit, and rolling window
- **Revocable** -- references a revocation service for instant kill
- **ConfineUser** -- locks the token to a specific agent identity
- **FeatureGlob** -- include/exclude patterns for fine-grained resource access

Anyone holding a token can add caveats (narrowing it) without contacting the issuer. The HMAC chain ensures the narrowed token is cryptographically tied to the original -- no forgery possible.

### Sub-Agent Delegation Chains

The SDK (`sdk/src/runtime.rs`) makes delegation a one-liner:

```rust
let sub = runtime.spawn_sub_agent(&Attenuation {
    services: vec![("storage".into(), "r".into())],
    budget: Some(BudgetSpec { limit: 100, window: Some("1h".into()), .. }),
    not_after: Some(now + 3600),
    ..Default::default()
}, &parent_token)?;
```

The sub-agent receives a token that can ONLY read storage, has a 100-call budget, and expires in one hour. It operates on the same ledger with its own cell, executes turns independently, and its authority is cryptographically bounded by `MAX_FOLD_DEPTH = 16` in the proof circuit -- delegation chains cannot exceed 16 hops.

The `DelegatedRef` model (`cell/src/delegation.rs`) uses snapshot+refresh: the child gets a frozen copy of the parent's capabilities and can act offline. Staleness is checked by verifiers, not the executor -- enabling disconnected operation within bounded freshness.

### Budget Gates and Computron Metering

The turn executor (`turn/src/executor.rs`) enforces budget at two levels:

1. **Token-level**: `CAV_BUDGET` caveats are checked against provided `budget_states` -- if remaining < cost, the request is denied.
2. **Execution-level**: The `BudgetGate` (Stingray bounded counter) checks the silo's local budget slice before each turn. Exhaustion rejects the turn before any state changes. On failure, debits are refunded (fast unlock).

Every operation costs computrons: actions (100), effects (50), transfers (75), proof verification (1000). The agent's fee must cover total cost or the entire turn atomically rolls back via journal replay.

### Instant Revocation

`CAV_REVOCABLE` marks a token as revocable via a named service. At verification time, the verifier demands a non-revocation proof (set membership). No proof = denied. The `RevocationChannelSet` on the executor additionally gates capability exercises -- a tripped channel kills delegated authority instantly across all holders.

### Privacy via Zero-Knowledge Proof

The fulfillment protocol (`intent/src/fulfillment.rs`) offers three modes:

- **Trusted**: real HMAC-chained attenuated macaroon (reveals token structure)
- **Selective**: STARK proof + selective fact disclosure (reveals only what you choose)
- **Private**: STARK proof alone (reveals NOTHING except "this action is authorized")

In Private mode, the verifier learns only that the agent holds sufficient authority. Not which token, not the delegation chain, not what else the agent can do. This is implemented via a multi-step authorization AIR that proves Datalog derivation in zero knowledge.

## Multi-Agent Coordination

### Atomic Composition (2PC)

When multiple agents must act together atomically (e.g., swap assets), dregg uses `CommitmentMode::Partial` signing. Each agent signs their fragment independently without seeing others' actions. A `TurnComposer` assembles fragments into one atomic turn. The call forest executes all-or-nothing -- if any fragment fails, everything rolls back.

### Discovery and Marketplaces

Agents discover each other via the **intent system**. An agent broadcasts "I need read access to storage with >= 1000 reputation" as a `MatchSpec`. Fulfillers match locally, generate attenuated tokens or STARK proofs, and deliver directly. Payment flows via conditional turns -- verified fulfillment triggers automatic transfer. Privacy is preserved end-to-end: the fulfiller proves capability without revealing identity.

## What `dregg` Offers That Existing Systems Lack

| Property | OpenAI/Anthropic | LangChain | `dregg` |
|----------|-----------------|-----------|-------|
| Attenuation | None | None | Cryptographic (HMAC chain) |
| Budget enforcement | None | Manual | Protocol-level (per-token + per-silo) |
| Offline delegation | N/A | N/A | Snapshot+refresh, no issuer contact |
| Revocation | N/A | N/A | Instant (channel-based + accumulator) |
| Audit trail | Application logs | Application logs | Cryptographic receipt chain (IVC) |
| Privacy | None | None | ZK-STARK proof of authorization |
| Multi-agent atomicity | None | None | Composed turns with partial commitment |
| Sub-agent spawning | Not modeled | Trust-the-dev | First-class SDK primitive |

## The Product Thesis

Every autonomous agent deployment will face the same question: how do you give an AI system enough authority to be useful while preventing it from exceeding its mandate? The answer is not better prompting or stronger guardrails -- it is cryptographically enforced least privilege with delegatable, attenuable, budget-bounded, instantly-revocable capability tokens whose exercise can be verified without revealing the holder's identity.

`dregg` is that infrastructure.
