# The DSL & apps

Three crates form the "author a constraint / author an app" surface of dregg:

- **`dregg-dsl/`** — a proc-macro crate compiling one constraint function into multiple proof/eval backends.
- **`app-framework/` (`dregg-app-framework`)** — the production application framework: the affordance model, the embedded executor seam, the deos-app composition, scaffolding.
- **`starbridge-apps/`** — concrete userspace apps built from dregg-native primitives only (no domain-specific `Effect` variants).

Everything below is what is at HEAD, with receipts.

---

## 1. `dregg-dsl` — the constraint DSL

`dregg-dsl` is a `proc-macro` crate (`dregg-dsl/Cargo.toml:7`). It exposes three attribute macros that each compile a single constraint function (or circuit module) into multiple target backends.

### Macros

- **`#[dregg_caveat]`** (`dregg-dsl/src/lib.rs:68`) — a function body of `require!(expr)` checks, where each `expr` is a binary comparison or a `.contains()` membership check (`lib.rs:50-67`).
- **`#[dregg_effect]`** (`dregg-dsl/src/lib.rs:127`) — a constraint *with state mutation*: `&mut` params and `*balance -= amount` mutation statements, plus `require!()` and `match` arms (`lib.rs:100-126`). Takes an optional `requires = "Send"` permission attribute parsed by `parse_effect_attr` (`lib.rs:212`).
- **`#[dregg_circuit]`** (`dregg-dsl/src/lib.rs:198`) — a "Level 2" DSL over a module declaring `WIDTH`/`DEGREE`/`PI_COUNT`, a `col` index module, and `constraints`/`transitions`/`boundaries` functions; emits a struct + `impl StarkAir` (`lib.rs:164-209`).

### The eight backends

A `#[dregg_caveat]`/`#[dregg_effect]` macro expands the parsed IR into eight code generators (`lib.rs:1-21`, expansion at `lib.rs:77-94` and `lib.rs:139-158`):

| Backend | Module | Emits |
|---|---|---|
| `gen_rust` | `dregg-dsl/src/gen_rust.rs` | `{name}_check(...) -> Result<(), ConstraintError>` evaluator (`gen_rust.rs:49`) — the differential **oracle** |
| `gen_air` | `gen_air.rs` | `{name}_air_constraints() -> AirConstraintSet` topology descriptor |
| `gen_datalog` | `gen_datalog.rs` | `{name}_datalog() -> &'static str` Datalog rule |
| `gen_kimchi` | `gen_kimchi.rs` | `{name}_kimchi() -> KimchiCircuitDescriptor` gate descriptor |
| `gen_plonky3` | `gen_plonky3.rs` | `{Name}P3Air` native Plonky3 AIR struct |
| `emit_stark` | `emit_stark_impl.rs` | `{Name}Circuit` compile-time STARK AIR |
| `gen_midnight` | `gen_midnight.rs` | `{name}_midnight_zkir() -> &'static str` Midnight ZKIR v3 program |
| `gen_sp1` | `gen_sp1.rs` | `{name}_sp1_guest() -> &'static str` SP1 guest source |

For an `#[dregg_effect]` an additional `{name}_effect_descriptor() -> EffectDescriptor` is emitted (`gen_rust::generate_effect_descriptor`, `lib.rs:143`).

### The IR

All backends consume `ConstraintIr` (`dregg-dsl/src/ir.rs:11`): name, typed `params`, `statements`, an `is_effect` flag, and `required_permission`. The restricted type system is `ParamType` (`ir.rs:86`): `U64`, `ByteArray32`, `ByteMatrix32(N)` (Merkle siblings), `Set`, and `UserDefined(String)` (enums like `Direction`). Statements are `Require` / `Mutate` / `Match` (`ir.rs:100`); mutation ops are `SubAssign`/`AddAssign`/`Assign` (`ir.rs:128`).

Requirement shapes are classified by `RequirementKind` (`ir.rs:146`): `LessEqual`, `GreaterEqual`, `Equal`, `NotEqual`, `Membership` (in-memory set), `BitRange` (`in_range!(value, N)` — `value < 2^N` via bit decomposition), `MerkleAtPosition` (`merkle_member!` — Poseidon2 `hash_2_to_1` inclusion proof, sibling order driven by `position` bits, `ir.rs:165`), and `Poseidon2Hash` (`poseidon2_assert!` — `output == poseidon2_hash([inputs])`, `ir.rs:176`).

### Cross-validation (the agreement set)

Five backends — `gen_rust`, `gen_datalog`, `gen_air`, `gen_kimchi`, `gen_plonky3` — form the **agreement set** cross-checked in-process by `dregg-dsl-differential` (`dregg-dsl-differential/src/lib.rs:5-13`), with `gen_rust` as the accept/reject oracle. `emit_stark` is exercised separately by `dregg-dsl-tests` prove/verify tests, not the differential harness. `gen_midnight` and `gen_sp1` are STRING emitters validated by **lint only** (their proof systems need external toolchains — a Midnight proof server, the SP1 RISC-V toolchain) and cast no agreement vote (`lib.rs:14-21`, `dregg-dsl-differential/src/lib.rs:15-23`).

Range checks (`<=`, `>=`, `in_range!`) compile to a genuine bit-decomposition in both `emit_stark` and `gen_plonky3`: the difference is bound to `RANGE_CHECK_BITS` binary witness columns, the reconstruction is enforced, and top bits forced to zero, so a field-wrapped negative difference is unsatisfiable (`lib.rs:23-29`). `emit_stark` additionally range-checks inequality *operands* to `< 2^29` (`dregg-dsl-differential/src/lib.rs` backend table).

`dregg-dsl` is a workspace-wide dependency: it is referenced from `Cargo.toml`, `circuit/Cargo.toml`, `cell/Cargo.toml`, `turn/Cargo.toml`, `commit/Cargo.toml`, `bridge/Cargo.toml`, and more.

---

## 2. `dregg-app-framework` — the application framework

`dregg-app-framework` (`app-framework/Cargo.toml`) is the production framework: server infra, admin auth, persistence, proof middleware, content stores, and the deos affordance/app model (`app-framework/src/lib.rs:1-46`). It depends on `dregg-sdk`, `dregg-turn`, `dregg-circuit`, `dregg-circuit-prove`, `dregg-cell`, `dregg-captp`, and the real transclusion primitive crate `starbridge-web-surface`.

### The affordance model — "htmx on crack"

The core interaction primitive is the **cell affordance** (`app-framework/src/affordance.rs:1-50`): a cell declares named effect-templates, and an interaction is a verified turn. The "button" is a cap-gated `dregg_turn::Effect`, and *who may press it* is decided by held capabilities, not a session cookie.

- **`CellAffordance`** (`affordance.rs:75`) — a `name`, the `required_rights: AuthRequired` a viewer must HOLD, and the real `effect_template: Effect` it fires. `Effect` is not `PartialEq` (carries STARK proofs / eventual refs), so it is identified by `name` + `required_rights` and compared via `EffectSummary` (`affordance.rs:130`).
- The cap-gate is `CellAffordance::authorized_for` (`affordance.rs:113`), which is the GENUINE `dregg_cell::is_attenuation(held, required)` (`required ⊆ held`) — the same predicate the firmament runs for every capability, not a parallel role check (`affordance.rs:52`, `106-115`).
- **`AffordanceSurface`** — a cell's published set, with per-viewer projection `project_for` (`affordance.rs:372`) returning only the affordances a holder's caps authorize, and the cap-gated fire.

**The dispatch seam is closed.** `AffordanceSurface::fire` (`affordance.rs:401`) runs the cap-gate and returns an `AffordanceIntent` (unauthorized ⇒ `FireError::Unauthorized`, nothing submitted). `AffordanceSurface::fire_through_executor` (`affordance.rs:443`) runs the gate FIRST (anti-ghost: an unauthorized fire never reaches the executor), wraps the gated effect in a signed `Turn` through the `AppCipherclerk` (a real `Authorization::Signature`, action targeting the surface cell + the affordance name as method), submits it via `EmbeddedExecutor::submit_turn`, and returns the executor's OWN `TurnReceipt` (`affordance.rs:443-466`).

### Gated affordances — the cap ∧ state conjunction

A `GatedAffordance` (`affordance.rs:530`) pairs the cap-gate with a *live-state* gate: a real `dregg_cell::CellProgram` evaluated by `CellProgram::evaluate(new, Some(old), None)` (`affordance.rs:576`) — the SAME evaluator the executor runs, authoring no new semantics. A gated button lights for a viewer IFF caps AND state both pass; a stale-state fire is refused in-band as `FireError::StateConditionUnmet` (`affordance.rs:270`, `594-612`) *before* any dispatch. `GatedSurface::project_gated_for` (`affordance.rs:791`) is the state-aware per-viewer projection.

### The userspace SDK surface

- **`AppCipherclerk`** (`cipherclerk.rs:67`) — the narrow ~6-method handle apps see, wrapping the SDK's broad `AgentCipherclerk` and a `federation_id`. Exposes `cell_id`, `public_key`, `make_action`, `make_turn`, `sign_action`, `sign_turn` (`cipherclerk.rs:13-25`); exposes NO key-export and cannot mutate the receipt chain (`cipherclerk.rs:27-35`). The `federation_id` (carried in action signatures to prevent cross-federation replay) is threaded into every call and never seen by apps (`cipherclerk.rs:49-56`).
- **`EmbeddedExecutor`** (`cipherclerk.rs:319`) — wraps an `AgentRuntime` (which holds a local `dregg_cell::Ledger`) behind a `Mutex`; `submit_turn` (`cipherclerk.rs:499`) is the verified-turn dispatch. `set_lean_producer` (`cipherclerk.rs:387`) is THE SWAP: when enabled, every submitted turn is committed by the verified Lean executor (`produce_via_lean`) and the Rust `TurnExecutor` is demoted to a logged differential.

### The deos-app composition

`DeosApp` (`app-framework/src/deos_app.rs:1-21`) composes the framework's separate pieces into ONE registration. A **`DeosCell`** (`deos_app.rs:89`) bundles a backing cell with its `AffordanceSurface`, its `GatedSurface`, an optional publish authority, and a route prefix. `DeosApp::builder(...).cell(...).build()` becomes the `register(ctx)`; `app.register(&ctx)` folds each cell's surface into the shared host context; `app.mount()` yields the whole axum surface (per-cell affordance routers + the app manifest + web-of-cells snapshot endpoints) (`deos_app.rs:17-42`). A published cell is exported as a `dregg://` sturdyref through `CapTpServer` and registered in the nameservice; `DeosCell::snapshot` mints a rehydratable `Sturdyref` peers rehydrate per-viewer through a `Membrane` (`deos_app.rs:44-56`). Durable verified state is a documented `PersistenceSeam` (the pg-dregg layer plugs in here; the in-process executor is the state today — marked honestly, `deos_app.rs:56-58`).

### The scaffold — "a deos app in an afternoon"

`scaffold.rs` (`app-framework/src/scaffold.rs:1-16`) is the `dregg new deos-app` generator. An `AppSpec` (app name + cells + affordances + rights + effects, `scaffold.rs:62-82`) goes two ways (`scaffold.rs:18-28`): `AppSpec::into_app` builds a live `DeosApp` in-process (the fast loop, no codegen), or `Scaffold::render`/`write_to` emits a complete buildable crate — `Cargo.toml`, `src/lib.rs`, `src/main.rs`, and the web-component surface — onto the `DeosApp` composition. The spec effect kinds are deliberately small: `AffordanceEffect::Emit { topic }` (`Effect::EmitEvent`) and `AffordanceEffect::SetField { index }` (`scaffold.rs:76-82`).

### The StarbridgeAppContext mount point

`StarbridgeAppContext` (re-exported, `lib.rs:176`) is the host-side mount point holding the `FactoryRegistry`, `InspectorRegistry`, and `AffordanceRegistry` (`affordance.rs:41-45`). A host calls `app::register(&ctx)` to plug a starbridge-app into a running federation.

### Anti-drift JS constants

`webgen::ConstantsModule` (`lib.rs:271`) renders an app's slot layout + event-topic vocabulary to a canonical `constants.generated.js` the web pages import — so the JS surface cannot drift from the Rust source of truth (`starbridge-apps/README.md` §"Anti-drift").

---

## 3. `starbridge-apps` — userspace apps

A starbridge-app is a Rust crate of `FactoryDescriptor`s + signed turn-builder helpers built from **dregg-native primitives only** — the hard rule is "the answer is never `Effect::FooApp`" (`starbridge-apps/README.md` §"The userspace stance"). When an app wants a domain effect, the missing primitive is the generic one (Caveat, StateConstraint, Authorization, Factory) it composes from.

Each app crate depends on `dregg-app-framework` (+ `dregg-cell`, `dregg-turn`, `dregg-types`) and exports a `FACTORY_DESCRIPTORS` slice plus turn-builders that take an `AppCipherclerk` and produce signed `Action`s — **no `Authorization::Unchecked`, no `[0u8; 64]` placeholder signatures, no reaching past the framework into `dregg_turn::builder::*`** (`starbridge-apps/nameservice/src/lib.rs:1-7`; `starbridge-apps/README.md` §"How a starbridge-app crate plugs in").

There are 21 directories under `starbridge-apps/` (incl. `shared/`). The README's inventory marks eight apps as "real, fully-implemented" each with a passing test suite (`starbridge-apps/README.md:59`), plus `compute-exchange` and `gallery` documented in follow-on tables. Examples:

- **`nameservice`** — register → resolve / set-target → renew → transfer → revoke. "Register a name" is userspace policy, expressed as `Effect::SetField(NAME_HASH_SLOT)` + `Effect::EmitEvent("name-registered")` — no new `Effect::RegisterName` (`nameservice/src/lib.rs:53-77`). Uniqueness is a `WriteOnce` cell-program caveat, not a new effect.
- **`escrow-market`** — a single **factory-born** cell whose installed `CellProgram` IS the rules, re-checked by the verified executor on every turn (`escrow-market/src/lib.rs:1-30`). Composes slot caveats: a bounded credit line (`FieldLteField`), a `WriteOnce` sealed-delivery digest, a conserving settlement, and a one-way `LISTED→FUNDED→SHIPPED→SETTLED` lifecycle (`StrictMonotonic`).

The slot caveats are real `StateConstraint` variants (`cell/src/program/types.rs:915`): `FieldEquals`, `FieldGte`, `FieldLte`, `FieldLteField` (`types.rs:925`), `FieldLteOther` (`types.rs:939`), `SumEquals` (`types.rs:942`), `WriteOnce` (`types.rs:951`), `Immutable` (`types.rs:956`), `Monotonic` (`types.rs:960`), `StrictMonotonic` (`types.rs:964`), `BoundedBy` (`types.rs:968`), `FieldDelta`, and more. A factory-born cell installs these as its `CellProgram`, so they bite on every subsequent turn — a rejected second claim or an over-budget bid is the caveat firing on the verified commit path.

---

## How they compose

1. **`dregg-dsl`** authors a *predicate* once (`#[dregg_caveat]`/`#[dregg_effect]`) and emits the cross-validated multi-backend forms consumed downstream by `circuit`/`cell`/`turn`.
2. **`dregg-app-framework`** turns dregg primitives (`FactoryDescriptor`, `StateConstraint`, `Effect`, `is_attenuation`, `CellProgram::evaluate`) into the affordance/deos-app developer surface, closing the dispatch seam onto the real `EmbeddedExecutor`.
3. **`starbridge-apps`** are the userspace proof that apps compose from generic primitives — factory-born cells whose installed `CellProgram` is enforced by the verified executor, with turn-builders that never bypass the framework.
