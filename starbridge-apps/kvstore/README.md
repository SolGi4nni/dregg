# starbridge-kvstore

**A verified key-value register store — a rollback-proof config/KV primitive whose every mutation is a receipted turn a light client can replay.**

A single cell holds a small **register file**: slot `0` is a monotone store version,
slots `1..=15` are the key-addressed value registers (the "key" is the register
index). Every `put`/`delete` is a signed turn the **verified executor** checks
against the store's `CellProgram` — so the store version never rolls back, and a
replayed or reordered mutation is an executor refusal, not a userspace check.

This crate is also a worked exemplar of the **unified starbridge-app template**: the
four axes a modern deos app follows, each demonstrated end-to-end and tested. The
SAME `store_program()` backs every axis, so the same invariant bites whether a turn
arrives as an `invoke()` method call or a gated `DeosApp` fire.

## The four axes (the template)

| Axis | What it is | Where | Test |
|---|---|---|---|
| **1. Verified core** | `store_program()` — a `CellProgram::Cases` whose `put`/`delete` cases carry `StateConstraint::Monotonic` on `VERSION_SLOT`; the executor refuses any rollback | `src/lib.rs` | `src/lib.rs::tests`, `tests/service.rs` |
| **2. deos surface** | the store composed as a `DeosApp` — per-viewer projection, cap-gated fires, web-of-cells publish, manifest | `src/deos.rs` (`kvstore_app`, `register_deos`) | `src/deos.rs::tests` |
| **3. Service cell** | a typed `InterfaceDescriptor` driven through the `invoke()` front door — the store as named methods (cells-as-service-objects) | `src/lib.rs` (`KvStore`, `invoke()`) | `tests/service.rs` |
| **4. deos-view card** | the UI as a renderer-independent `deos.ui.*` view-tree (native gpui / web HTML / discord — one piece of data) | `src/card.rs` | `src/card.rs::tests` |

These compose: the SAME `store_program()` backs all four, so the `Monotonic`
invariant bites whether a turn arrives as an `invoke()` desugar or a `DeosApp` fire.
Soundness lives in the verified core (axis 1); axes 2–4 are faces onto it.

## Axis 1 — the verified core (`store_program`)

The store cell's `CellProgram` is the method-dispatch plus the verified invariant. A
`CellProgram::Cases` whose `MethodIs` guards expose `put`/`delete`/`get`, and whose
`put`/`delete` cases carry `StateConstraint::Monotonic` on `VERSION_SLOT`:

| Slot | Constant     | Caveat      | What it guarantees |
|:---:|--------------|-------------|--------------------|
| `0` | `VERSION_SLOT` | `Monotonic` | the store version never rolls back — a replayed/reordered mutation that would lower it is an executor refusal |
| `1..=15` | `REG_MIN..=REG_MAX` | (key-addressed) | the value registers a `put`/`delete`/`get` addresses |

It is built from dregg primitives only — `Effect::SetField`, `Authorization::Signature`
from `AppCipherclerk::make_action`, and `StateConstraint` caveats. There is **no**
domain-specific store `Effect`, **no** `Authorization::Unchecked`, **no** placeholder
signature.

## Axis 2 — the deos surface (`kvstore_app` / `register_deos`, `src/deos.rs`)

The store composed as a `DeosApp`: `view` is a cap-only read (`Signature`); `put` /
`delete` are cap-only writer affordances (`Either`) on the reader ⊂ writer ladder.
The fire (`fire_put` / `fire_delete`) reads the live `VERSION` off the cell, bumps it
by one, and submits the FULL two-effect turn (bump `VERSION` + write/clear the
register) the executor re-enforces `store_program()` on — so a rollback bites in the
deos fire path too. `register_deos(ctx)` seeds the cell and folds the surface into the
context's affordance registry; `DeosApp::mount` yields the axum router (per-viewer
projection, `/manifest`, `/surface.js`, `dregg://` publish). See `src/deos.rs::tests`.

## Axis 3 — the service cell (`invoke()`, `src/lib.rs`)

The store as a first-class typed interface, driven through the `invoke()` front door
(cells-as-service-objects — no `Effect::Invoke`, no kernel change; a method desugars
to the ordinary verified effects it names, routed by the SAME verified DFA router the
protocol uses):

| method | semantics | auth | args | desugars to |
|---|---|---|---|---|
| `put(reg, value)` | Replayable | `Signature` | `(reg, value)` | bump `VERSION` + `SetField(reg, value)` |
| `delete(reg)` | Replayable | `Signature` | `(reg)` | bump `VERSION` + `SetField(reg, 0)` |
| `get(reg)` | **Serviced** | `None` | `(reg)` | — (the named OFE read seam: a read, not a turn) |

```rust
use starbridge_kvstore::KvStore;
use dregg_app_framework::InvokeAuthority;

let store = KvStore::new(store_cell);
let turn = store.put(&cclerk, 1, value, 1, InvokeAuthority::Signature)?; // routed + cap-gated + signed
executor.submit_turn(&turn)?;                                           // the executor re-enforces store_program()
```

The cap-gate bites twice (at the front door AND the executor); a `put` that would roll
the store version back is an executor refusal (`Monotonic(VERSION)`); `get` refuses to
desugar (it names the serviced OFE read seam honestly). Register the interface with
`register_interface(&mut registry, store)` so the Service Explorer resolves the real
`Signature`/`Serviced` shape.

## Axis 4 — the deos-view card (`src/card.rs`)

The app's UI as a renderer-independent `deos.ui.*` view-tree: a `vstack` of a header,
a live `bind` on `VERSION_SLOT` (re-reads the store version off the ledger), and one
`button` per service method carrying its `onClick = {turn, arg}` (the button `turn`
names ARE the service method symbols `METHOD_PUT` / `METHOD_DELETE` / `METHOD_GET`).
The SAME tree renders three ways via `deos-view` — native gpui pixels, a
browser-loadable HTML document, and a discord embed.

```rust
let card_json = starbridge_kvstore::card::kvstore_card_json(); // serializable deos.ui.* JSON
```

The card is pure `serde_json` data (no dependency on the `deos-view` renderer crate,
which pulls the mozjs + gpui elephants and is a standalone excluded workspace). The
deos world's renderers consume the JSON; this crate owns the card definition and
proves it well-formed.

## What this crate exports

```rust
// Axis 1 — verified core
store_program()        -> CellProgram   // Monotonic(VERSION) scoped to put/delete
interface_descriptor() -> InterfaceDescriptor
register_interface(&mut registry, store)
VERSION_SLOT / REG_MIN / REG_MAX / METHOD_PUT / METHOD_DELETE / METHOD_GET

// Axis 2 — deos surface
deos::kvstore_app(cclerk, executor) -> DeosApp
deos::register_deos(ctx) -> DeosApp                 // seed + mount the composed surface
deos::seed_store / deos::fire_put / deos::fire_delete

// Axis 3 — service cell
KvStore                                             // .put / .delete / .get

// Axis 4 — deos-view card
card::kvstore_card_value() -> serde_json::Value
card::kvstore_card_json()  -> String
```

## Tests

```sh
cargo test -p starbridge-kvstore
```

| Test | Surface | What it pins |
|---|---|---|
| `src/lib.rs::tests` | the interface + program directly | the three typed methods, dispatch, register-range rejection |
| `src/deos.rs::tests` | the composed `DeosApp` + real executor | the three affordances; `fire_put` commits and bumps `VERSION` to 1; `register_deos` seeds + registers |
| `src/card.rs::tests` | the view-tree | the card is a well-formed `deos.ui.*` tree whose buttons carry the service methods |
| `tests/service.rs` | **the real executor** | the store through `invoke()`: resolvable interface, authorized commit + version bump, front-door cap-gate, executor rollback refusal, serviced `get` seam, route-membership witness |
| `tests/coherent_stack_demo.rs` | the live `Ledger` | the document fork/diverge/stitch/resolve narrative rides the SAME world as the invoke() turns |

## See also

- `../bounty-board/` — the reference template (all four axes, the gated-lifecycle exemplar).
- `../escrow-market/src/service.rs` — another `invoke()` service-cell exemplar (axis 3).
- `../../deos-view/` — the card renderers (native / web / discord); `docs/reference/deos-view.md`.
- `../../docs/deos/DEOS-APPS.md` — the deos app model and the rebuild plan.
