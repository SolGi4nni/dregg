# Build with dregg

← [guide index](README.md) · [overview](../OVERVIEW.md) · [quickstart](../../QUICKSTART.md)

This guide is the model, your first app end-to-end, and the core build patterns.
By the end you can create an identity, drive a real turn, hold its receipt, and
recognize which of the five patterns your app is.

## The model in one sentence

> A turn is the exercise of an attenuable, proof-carrying token over owned state,
> leaving a verifiable receipt.

Everything below is that sentence unpacked into four nouns.

### Cell — the unit of state and identity

A cell is a sovereign object. Everything it holds is one of four **substances**
(`cell/src/cell.rs`, `cell/src/state.rs`):

- **value** — per-asset signed balances. An asset *is* its issuer cell (which
  carries −supply), so every asset's balances sum to identically zero.
- **state** — a heap of programmable slots plus a nonce.
- **authority** — a capability tree.
- **evidence** — append-only nullifier / commitment / epoch ledgers.

A card, a document, an agent, a room, a service, you — each is a cell.

### Capability — a directed authority edge

A capability is the right to produce a witness the kernel accepts for authority
over one cell. **You hold a capability iff you can produce its witness** — never
merely be named in a table. Authority is *production under non-forgeability*, not
possession of a key.

Capabilities **narrow freely and only narrow**: delegation can only *attenuate*
(`granted ≤ held`), enforced at the dispatcher. They carry **caveats** —
time-boxes, third-party discharge, rate bounds, scope — composed macaroon-style
(`macaroon/`).

### Turn — one authorized inference step

A turn is an atomic, capability-gated transition across one or more cells: a
*forest* of effects with delegation edges, executed all-or-nothing (`turn/`,
executor under `turn/src/executor/`). A turn that cannot exhibit a valid,
sufficiently-empowered, fresh token chain simply does not execute.

The kernel's design is **eight verbs** (`create · write · move · grant · revoke
· shield/unshield · lifecycle · exercise`) over the four substances, with
machine-checked minimality. The SDK surfaces these as typed verb builders
(`transfer`, `write`, `grant`, …) — see the turn flow below.

### Receipt — a turn's verifiable witness

Every turn leaves a receipt that binds the *whole* post-state. Tampering a field
the effect did not legitimately write makes the turn unprovable — the *anti-ghost*
property (`sdk/src/receipt.rs`). A receipt is born proofless; the STARK is
additive attestation, attached lazily. A light client holding one root learns the
whole history was authorized, conservative, fresh, and correctly committed —
re-executing nothing.

## Your first app, end-to-end (Rust)

The whole loop with no moving parts beyond the SDK is
`sdk/examples/hello_receipt_chain.rs`. Run it:

```sh
cargo run -p dregg-sdk --example hello_receipt_chain
```

It is the canonical turn shape — `Identity → .turn() → typed verbs → .sign() →
.submit() → Receipt` — entirely local (an in-memory ledger, no node):

```rust
use dregg_sdk::{AgentCipherclerk, AgentRuntime};

// 1. Create an agent: a fresh Ed25519 identity + its cell in a local ledger.
let cclerk = AgentCipherclerk::new();
let runtime = AgentRuntime::new_simple(cclerk, "hello");
println!("agent cell id: {}", runtime.cell_id());

// 2. Build, sign, and submit ONE turn: write state slot 0.
let signed = runtime
    .turn()
    .write_u64(0, 42)
    .sign()                       // binds the act to this key; refuses an empty turn
    .expect("signing a staged turn with this runtime's own key");

// Before submitting, read the clerk's faithful explanation — the
// anti-blind-signing reading of exactly what the signature covers.
println!("{}", signed.explain());

let receipt = signed
    .submit()                     // executes; returns a Receipt
    .expect("a write turn on the agent's own cell should commit");

// 3. The receipt binds the whole post-state; its chain link is
//    `previous_receipt_hash`, forming a hash chain across turns.
```

The turn-builder surface (`sdk/src/turns.rs`, opened by `runtime.turn()`):

| builder | effect | what it does |
|---|---|---|
| `.transfer(to, amount)` / `.transfer_from(..)` | `Transfer` | move value |
| `.write(slot, felt)` / `.write_u64(slot, n)` | `SetField` | write a state slot |
| `.grant(..)` | `GrantCapability` | delegate (attenuated) authority |
| `.increment_nonce()` | — | bump the cell nonce |
| `.reveal(blob)` | — | disclose a 32-byte preimage under the signature |
| `.effect(..)` / `.effects(..)` | (various) | splice in prebuilt effect lists |

`.on(target)` acts on another administered cell; `.as_cell(cell, fee)` makes the
cell pay from its own balance. After `.sign()` "an unauthorized act is
inexpressible here" — raw, unauthorized construction lives only behind the sealed
`sdk::raw` module (`sdk/src/raw.rs`).

### Verifying via the light client

A `Receipt` carries a lazily-attached `TurnProof` — one composed STARK that in a
single verification covers the state transition, authorization chain, c-list
membership, conservation, and non-revocation (`sdk/src/full_turn_proof.rs`). The
entry points re-exported at the crate root are `prove_full_turn`,
`verify_full_turn`, and `verify_full_turn_bound` (the freshness-critical
no-double-spend verifier).

The whole-history artifact is `AttestedHistory` (`sdk/src/lib.rs`, from
`dregg-lightclient`): the verdict from verifying ONE succinct whole-history
aggregate, re-witnessing nothing. The in-browser version of this same fold is in
[deos from the web](DEOS-FROM-THE-WEB.md).

### The same flow in Python and TypeScript

The Python and TypeScript SDKs mirror the Rust shape and talk to a node over
HTTP. Start a local node first (`QUICKSTART.md` §1:
`dregg-node init … && dregg-node run --enable-faucet --port 8421`), then:

```python
# sdk-py/examples/quickstart.py  —  pip/maturin install then:
#   python examples/quickstart.py
import dregg

ident = dregg.Identity.from_profile("me")          # ~/.dregg/profiles, shared with the CLI
signed = (ident.turn("http://localhost:8421")
               .transfer("28c2cba0…", 100)
               .sign())
print(signed.explain())                            # the faithful reading
receipt = signed.submit()                          # raises DreggRefused on a no
print(receipt.turn_hash, receipt.has_proof)
```

```ts
// sdk-ts/examples/transfer.mjs  —  npm run build then:  node examples/transfer.mjs
import { AgentRuntime, Identity, NodeClient } from "@dregg/sdk";

const node = new NodeClient("http://localhost:8421");
const sender = Identity.generate();
const runtime = new AgentRuntime(sender, node);
await runtime.faucet(2000);                         // materialize + fund (dev faucet)

const signed = await runtime.turn().transfer(recipient.cellId(), 500n).sign();
console.log(signed.explain());                      // anti-blind-signing reading
const receipt = await signed.submit();
console.log(receipt.turnHash);
```

The Rust SDK is the offline core (no networking; builds on `wasm32`); `sdk-py`
and `sdk-ts` mirror it byte-for-byte (key derivation, wire encoding, canonical
hashes, and signing preimages are differentially tested against the repo's own
`dregg-wasm` build). For the full SDK surface see
[`docs/reference/sdk.md`](../reference/sdk.md).

## The five core patterns

Most apps are one of five shapes. Each desugars to the ordinary verified effects
the kernel already enforces — there is no `Effect::FooApp`.

### 1. Service-cell via `invoke()`

Give a cell a first-class typed interface and dispatch methods through it. The
interface is a *userspace* object above the effect-VM — **there is no
`Effect::Invoke`**; a method desugars to ordinary effects, and membership of the
invoked method is decided by the same verified DFA router the protocol already
uses (`cell/src/interface.rs`, `app-framework/src/invoke.rs`).

```rust
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;

// A cell publishing three typed methods (the kvstore exemplar):
InterfaceDescriptor::new(vec![
    MethodSig {                                     // put(reg, value): a signed write
        args_schema: ArgsSchema::Fixed(2),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol("put"))
    },
    MethodSig {                                     // delete(reg): a signed clear
        args_schema: ArgsSchema::Fixed(1),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol("delete"))
    },
    MethodSig {                                     // get(reg): a pure read — the OFE seam
        args_schema: ArgsSchema::Fixed(1),
        auth_required: AuthRequired::None,
        semantics: Semantics::Serviced,
        ..MethodSig::replayable(method_symbol("get"))
    },
]);
```

A `Replayable` method desugars to its effects; a `Serviced` method (a pure
cross-cell read) is a named seam `invoke()` refuses to fake. Worked exemplar:
`starbridge-apps/kvstore/`. The cap-gate is enforced twice — at the `invoke()`
front door and again by the executor on the desugared turn. See
[`docs/reference/services.md`](../reference/services.md).

### 2. Reactor — watch a cell, react with a turn

The reactive twin of `invoke()`: a service declares *what it watches* and *how it
reacts*; the framework wires match → cap-gate → build → sign
(`app-framework/src/reactor.rs`). The chain is the message bus.

```rust
use dregg_app_framework::{Reactor, ReceiptFilter, ObservedReceipt, ReactionPlan, AuthRequired};

impl Reactor for BotCommandReactor {
    fn filter(&self) -> ReceiptFilter {                 // what it watches
        ReceiptFilter::cell_methods(command_cell(), &[COMMAND_METHOD])
    }
    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        let (req, _seq) = decode_command(&observed.effects)?;   // read the on-chain command
        let action = build_op_action(&self.cclerk_for(req.user_id), &req.op, ..)?;
        Some(ReactionPlan {                              // a cap-gated reaction turn
            target: action.target,
            method: req.op.method_name().to_string(),
            args: action.args.clone(),
            effects: action.effects,
            auth_required: AuthRequired::Signature,
        })
    }
}
```

Worked exemplar: `discord-bot/src/bot_reactor.rs` (a button in the desktop fires
an on-chain command turn; the bot watches the command cell and reacts with its
own receipted turn).

### 3. Membrane — composed, non-amplifying authority

A membrane forwards a capability `C` that exists only as the *conjunction* of two
held capabilities `A` and `B`, and **cannot amplify**: it seals only if its
exposed authority is a submask of the composition floor (`cell/src/membrane.rs`).

```rust
use dregg_cell::membrane::{HeldFacet, Membrane, CompositionPolicy, Presentation};

// Build a 2-of-2 membrane and seal it (refuses to come into being if it amplifies).
let sealed = Membrane::maximal(membrane_cell, facet_a, facet_b,
                               CompositionPolicy::BothOf, target)
    .seal()                                            // -> Option<SealedMembrane>
    .expect("a maximal membrane never amplifies");

// Exercising C requires presenting BOTH A and B; a deficient presentation is refused.
let cap_c = sealed.exercise(&Presentation::both(facet_a, facet_b), requested_effect)?;
```

This ocap algebra is what the deos *world-fork membrane* (a chat message that
carries a cap-bounded snapshot of a world you can drive and stitch back) rides on
— see [What you can build](WHAT-YOU-CAN-BUILD.md) and
`docs/deos/MEMBRANE-FORWARDER.md`.

### 4. Documents — patches, history, conflict objects

A document is a cell (or cell-subgraph); an edit is a patch (a turn); content is
the fold of patch-history; a conflict is a first-class *state* you resolve with a
later patch, never a merge failure (`dregg-doc/`). Merge is the categorical
pushout. Runnable: `cargo run -p dregg-doc --example two_device_offline_stitch`.

### 5. Cap-secure delegation

Hand out attenuated authority that the *executor* enforces, not an out-of-band
check. `AgentRuntime::spawn_sub_agent` mints a fresh cell whose enforced
credential is a biscuit granting exactly the allowed method verbs; a method
outside the granted set is rejected with `TokenInsufficientCapability` at the
executor (`sdk/src/runtime.rs`). The same shape gates an untrusted tool call
through `tool_gateway::ToolGateway::invoke` — a cap-gated, metered, receipted
delegated turn or an in-band refusal (`sdk/src/tool_gateway.rs`).

## Where to go next

- See each pattern as a runnable app: [What you can build](WHAT-YOU-CAN-BUILD.md).
- See dregg in a browser tab with no node: [deos from the web](DEOS-FROM-THE-WEB.md).
- The exact guarantees and open seams: [`metatheory/CLAIMS.md`](../../metatheory/CLAIMS.md).
