# The service-economy SDK surface

Buy a service in a few lines, from any of the three SDKs, over the verified rail.

This is the developer onramp for dregg's service economy: pay another agent, call
a service paying through `Payable`, post a service request to an intent ring, and
run a workload under a durable, metered execution lease. Every call here is a
**thin wrapper that desugars to a primitive the kernel already verifies** — there
is no new kernel effect, no new commitment field, and no faking. A call you make
in TypeScript, Python, or Rust resolves to the same `Action`/`Effect` and rides
the same proof-carrying turn.

## The few-lines API (consistent across ts / py / rust)

```ts
// Pay another agent (Payable transfer — incl. bridged $DREGG, an ordinary asset).
await dregg.pay(provider, 1_000n, asset);

// Find + call a service, paying through Payable in the same turn.
const result = await dregg.services.invoke(cell, "render", args, { pay: { to: provider, amount: 250n, asset } });

// Post a service request to the intent ring (the want/offer half).
const promise = await dregg.intents.requestService({ want: serviceId, offer: 250n, asset });

// Open + fund + run a durable execution lease.
const lease = await dregg.execution.lease({ maxSteps: 8, asset });
await lease.fund(funder, 5_000n);
const step = await lease.run(effects);    // advances the durable checkpoint, metered
```

The shapes are identical in Python (`dregg.pay(...)`, `dregg.services.invoke(...)`,
`dregg.execution.lease(...)`) and Rust (`runtime.pay(...)`,
`runtime.invoke_service(...)`, `ExecutionLease::open(...)`).

## Each call → the real underlying turn/effect

The whole point is that this is an honest, thin layer. Here is exactly what each
call desugars to — the verified primitive it routes through, and where it lives.

| SDK call | Desugars to | Underlying primitive (file) |
| --- | --- | --- |
| `dregg.pay(to, amount, asset)` | one conserving `Effect::Transfer` (per-asset Σδ=0) via the `Payable` `pay` method | `dregg_payable::resolve_pay` (`dregg-payable/src/payable.rs:123`) |
| `dregg.services.invoke(cell, method, args, { pay })` | DFA-routed `Action` for `method` on `cell`, carrying the work effects, with the canonical pay `Transfer` prepended when `pay` is given | `dregg_payable::resolve_invocation` (`dregg-payable/src/routing.rs:245`) + `resolve_pay` |
| `dregg.execution.lease({ maxSteps, asset })` | a cap-gated worker scoped to the run verb + a `FieldLte { step ≤ maxSteps } ∧ Monotonic { step }` meter program installed on the lease cell | `AgentRuntime::spawn_sub_agent_scoped` (`sdk/src/runtime.rs:850`) + `lease_program` (`sdk/src/service_economy.rs`) |
| `lease.fund(funder, amount)` | one conserving `Effect::Transfer` into the lease cell | `SubAgent::execute` Transfer (`sdk/src/runtime.rs`) |
| `lease.run(effects)` | a `Monotonic`/`FieldLte`-gated `Effect::SetField` checkpoint advance (`step → step+1`) + the workload effects, metered through the cap-gated worker on one turn | `SubAgent::execute_method` (`sdk/src/runtime.rs:1194`) |
| `dregg.intents.requestService({ want, offer })` | an intent-ring node (offer payment, want the service-promise token), matched by `RingSolver` into a 2-cycle, settled atomically per-asset Σδ=0 | `ServicePromiseExchange` (`app-framework/src/service_promise.rs:419`) — node/app-framework side |

Two of these — the **intent ring / service-promise** and the standalone
**execution-lease app** — live ABOVE the SDK (they depend on
`dregg-app-framework`'s `AppCipherclerk`, which depends on `dregg-sdk`). The SDK is
the bottom layer and cannot depend on them without a cycle. So:

- `dregg.pay`, `dregg.services.invoke`, and `dregg.execution.lease`/`run` are
  implemented **inside the SDK**, over the primitives below the framework
  (`resolve_pay`, the DFA router, the cap-gated worker + `Monotonic`/`FieldLte`
  meter). The SDK lease desugars to the **same verified effect shapes** the
  upper-crate `starbridge-execution-lease` app's `advance_checkpoint` uses.
- `dregg.intents.requestService` is the ergonomic face of the app-framework's
  `ServicePromiseExchange` / `RingCoordinator`; its binding belongs in the
  app-framework / node layer, not the offline SDK core. It is **designed here,
  scaffolded above** — see "Status" below.

## Rust SDK — what is implemented (real, tested)

The Rust SDK (`sdk/`, crate `dregg-sdk`) is the bottom layer; the methods below
are inherent on `AgentRuntime` plus the `ExecutionLease` type
(`sdk/src/service_economy.rs`), re-exported at the crate root.

```rust
use dregg_sdk::{AgentRuntime, ExecutionLease, LeaseTerms, PayLeg, InvokeAuthority};

// 1. pay — the canonical Payable transfer.
let receipt = runtime.pay(provider, 1_000, asset)?;            // any asset
let receipt = runtime.pay_native(provider, 1_000)?;            // this cell's token_id

// 2. invoke a service, optionally paying through Payable in the same turn.
let (action, sig) = runtime.invoke_service_resolved(           // the pure, verified desugar
    cell, "render", args, work_effects, InvokeAuthority::None,
    Some(PayLeg::new(provider, 250, asset)),
)?;
let receipt = runtime.invoke_service(                          // signed + submitted
    cell, "render", args, work_effects, InvokeAuthority::None, Some(PayLeg::new(provider, 250, asset)),
)?;

// 3. a durable, metered execution lease.
let mut lease = ExecutionLease::open(&runtime, &root_token, LeaseTerms::new(8))?;
let _funded = lease.fund(&funder, 5_000)?;                     // conserving Transfer in
let step = lease.run(work_effects)?;                           // checkpoint += 1, metered
// step.step / step.remaining / step.receipt
```

Each is tested to desugar to the right verified turn/effect, in
`sdk/src/service_economy.rs`:

- `pay_desugars_to_one_conserving_payable_transfer` — `pay` routes through the
  canonical `Payable` interface (`method == pay`, the canonical `MethodSig`) and
  desugars to exactly one `Effect::Transfer`.
- `pay_commits_and_conserves_value` — end-to-end on the real executor: the
  recipient is credited exactly the amount; the only value sink beyond the
  conserved transfer is the payer's fee.
- `invoke_service_routes_method_and_refuses_unknown` — the method routes through
  the verified DFA router; an undeclared method is a fail-closed `UnknownMethod`.
- `invoke_service_prepends_canonical_pay_leg` — a paid invocation prepends exactly
  the canonical `resolve_pay` `Transfer` (caller → provider) ahead of the work.
- `lease_program_carries_ceiling_and_monotonic` — the installed meter is exactly
  `FieldLte { step ≤ maxSteps } ∧ Monotonic { step }`.
- `lease_open_fund_run_commits_and_advances_checkpoint` — open + fund (conserved)
  + two runs advance the durable checkpoint monotonically.
- `lease_run_past_ceiling_is_refused_by_the_executor` — a run past the capacity
  ceiling is rejected by the executor's `FieldLte` meter, and the refused run
  leaves the checkpoint untouched.

### Paid, capability-gated, rate-metered invocation: the `ToolGateway`

For the full "pay to access another agent's tool/model, capability-gated and
rate-metered" market, the SDK already ships the `ToolGateway`
(`sdk/src/tool_gateway.rs`): `ToolGateway::admit_priced` admits a worker under a
delegated mandate (scope + deadline + rate), and each `invoke` charges a per-call
price through the SAME `Payable::pay` desugar this facade's `pay` uses, riding the
metered turn. `dregg.services.invoke` above is the simple, single-call front door;
the `ToolGateway` is the metered, budgeted, routed data plane over the same value
rail.

## Paying with $DREGG (including bridged $DREGG)

In the dregg value model an asset **is** its issuer cell: `AssetId := issuer-cell`
(a 32-byte id). A cell holds value denominated in its own `token_id`, and two
cells interoperate in one asset by sharing a `token_id`. `pay` and the `PayLeg`
take an `AssetId`, so they pay in any asset uniformly.

Bridged `$DREGG` is **an ordinary `AssetId`**: the Solana/pump.fun `$DREGG` SPL
token is mirror-minted inside dregg by `dregg-bridge::solana_mirror`
(`bridge/src/solana_mirror.rs`), and the mirror's `MirrorConfig.asset` is the
`AssetId` of the in-dregg mirror token. Paying with bridged `$DREGG` is therefore
just `dregg.pay(to, amount, mirror_asset)` — the same single conserving
`Effect::Transfer`, routed identically (the bridge's own end-to-end test mints
bridged `$DREGG` and pays it through the `Payable` interface,
`bridge/src/solana_mirror.rs:606`).

## TypeScript SDK (`@dregg/sdk`) — binding story: HAND-WRITTEN

The TypeScript SDK (`sdk-ts/`, `@dregg/sdk`) is **hand-written TypeScript** over a
wire `NodeClient`, bundled with `tsup` (not generated from Rust). Its surface today
(`sdk-ts/src/index.ts`): `Identity`, `AgentRuntime`/`NodeClient`,
`TurnBuilder`/`AuthorizedTurn` → `Receipt`, the organ clients (`TrustlineClient`,
`ChannelsClient`, `MailboxClient`), `AttestedQuery`, the `program` constraint
language, and `Pg`/`DeployChecker`. (A separate `@dregg/sdk/wasm` playground is the
only wasm-bindgen-generated piece, in `wasm/`.)

So the service-economy surface in TS is **added by hand** as TypeScript that builds
the same turns the Rust facade does and posts them through `NodeClient`:

```ts
// sdk-ts/src/service-economy.ts  (proposed — mirrors the Rust desugars)
export class ServiceEconomy {
  constructor(private runtime: AgentRuntime) {}

  // pay → a Payable `pay` turn: one Transfer(from=me, to, amount) in `asset`.
  async pay(to: Bytes32, amount: bigint, asset: Bytes32): Promise<Receipt> {
    return this.runtime.turn().payable(asset, amount, to).sign().then(t => t.submit());
  }

  // services.invoke → route `method` on `cell`, prepend the pay Transfer if given.
  async invoke(cell: Bytes32, method: string, args: Bytes32[], opts?: { pay?: PayLeg }): Promise<Receipt> { /* … */ }

  // execution.lease → open a worker + install FieldLte ∧ Monotonic meter; run advances the checkpoint.
  async lease(terms: { maxSteps: number; asset: Bytes32 }): Promise<Lease> { /* … */ }
}
```

Because the TS SDK already builds and signs turns client-side (the `TurnBuilder` →
`AuthorizedTurn` → `submit` shape), the honest way to add these is a `pay()` verb on
`TurnBuilder` (desugaring to the `Payable` `Transfer`) plus a `ServiceEconomy`
namespace, each producing the exact `Action`/`Effect` JSON the node executor
verifies — the same bytes the Rust `resolve_pay` produces. Building it is tractable
and is the next slice; it is **designed, not yet shipped** (see Status).

## Python SDK (`dregg` pip) — binding story: GENERATED (PyO3/maturin)

The Python SDK (`sdk-py/`, `dregg` on pip) is a **PyO3 extension generated from
Rust** via maturin (`bindings = "pyo3"`, module `dregg.dregg`). Its surface
(`sdk-py/src/lib.rs`) — `Identity`, `TurnBuilder`, `AuthorizedTurn`, `Receipt`, the
`Trustline`/`Channels`/`Mailbox` organ clients, the `program` constraint functions
— is each a `#[pyclass]`/`#[pymethods]`/`#[pyfunction]` over the Rust SDK.

So the service-economy surface in Python is **added by writing Rust bindings** in
`sdk-py/src/lib.rs` that call the Rust facade methods this work shipped
(`AgentRuntime::pay`, `invoke_service`, `ExecutionLease`), then `maturin build
--release`. No hand-written Python: the Python surface is generated, so the design
is "add `#[pymethods] fn pay(...)`, `fn invoke_service(...)`, and a `Lease`
`#[pyclass]` forwarding to `ExecutionLease`." This is the cleaner of the two
bindings precisely because the Rust core now exists — the Python methods are
thin forwards.

```rust
// sdk-py/src/lib.rs  (proposed — forwards to the Rust facade)
#[pymethods]
impl TurnBuilder {
    fn pay(&self, to: &Bound<PyAny>, amount: u64, asset: &Bound<PyAny>) -> PyResult<AuthorizedTurn> { /* resolve_pay → sign */ }
}
#[pyclass(module = "dregg")]
struct Lease { /* wraps dregg_sdk::ExecutionLease */ }
```

## Status — real vs designed

- **Real, tested (Rust SDK):** `AgentRuntime::pay` / `pay_native`,
  `AgentRuntime::invoke_service_resolved` / `invoke_service`, `ExecutionLease`
  (`open`/`fund`/`run`) — all desugaring to verified primitives, with desugar +
  end-to-end conservation/meter tests (`sdk/src/service_economy.rs`, green under
  `cargo test -p dregg-sdk`). The metered/paid `ToolGateway` was already real.
- **Real, above the SDK:** the intent-ring `ServicePromiseExchange` /
  `RingCoordinator` and the standalone `starbridge-execution-lease` app
  (`app-framework/`, `starbridge-apps/execution-lease/`). The
  `dregg.intents.requestService` facade is the designed ergonomic face of these;
  it belongs in the app-framework/node layer.
- **Designed, not yet shipped:** the TypeScript `ServiceEconomy` namespace
  (hand-written TS over `NodeClient`) and the Python `pay`/`invoke_service`/`Lease`
  bindings (generated PyO3 forwards to the Rust facade above). Both are tractable
  thin layers over the now-existing verified Rust core; neither is faked here.
