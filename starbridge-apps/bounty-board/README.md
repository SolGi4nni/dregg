# starbridge-bounty-board

**Bounties as a one-way state machine, enforced by the verified executor, settling in a real conserving `Effect::Transfer` — and the reference template for a modern deos app.**

A poster opens a bounty promising a reward; a worker claims it (first-claimer-wins);
the worker submits work; the poster pays out. Every transition is a signed turn the
**verified executor** checks against slot-caveats installed on the bounty cell — so a
bounty cannot be stolen, replayed, re-priced, or paid twice.

This crate is also **the worked exemplar of the unified starbridge-app template**: the
four axes every modern deos app should follow, each demonstrated end-to-end and tested.
Read it as the paint-by-numbers shape for the other apps.

## The four axes (the template)

| Axis | What it is | Where | Test |
|---|---|---|---|
| **1. Verified core** | a `FactoryDescriptor` + `CellProgram` whose slot-caveats ARE the lifecycle rules; the executor refuses any illegal turn | `src/lib.rs` | `tests/factory_birth.rs`, `src/lib.rs::tests` |
| **2. deos surface** | the lifecycle composed as a `DeosApp` — per-viewer projection, cap∧state gated fires, web-of-cells publish, rehydratable snapshot, manifest, generated web component | `src/lib.rs` (`bounty_app`, `register_deos`) | `tests/deos_seam.rs`, `tests/reexpress_deos_app.rs` |
| **3. Service cell** | a typed `InterfaceDescriptor` driven through the `invoke()` front door — the lifecycle as named methods (cells-as-service-objects) | `src/service.rs` | `tests/service.rs` |
| **4. deos-view card** | the UI as a renderer-independent `deos.ui.*` view-tree (native gpui / web HTML / discord — one piece of data) | `src/card.rs` | `src/card.rs::tests` |

These compose: the SAME `bounty_cell_program()` backs all four, so the same caveats bite
whether a turn arrives as a raw `build_*_action`, a gated `DeosApp` fire, or an `invoke()`
method call. Soundness lives in the verified core (axis 1); axes 2–4 are faces onto it.

## Axis 1 — the lifecycle, enforced by caveats (not asserted)

Each bounty lives in a sovereign cell whose state machine is its installed `CellProgram`:

```
OPEN ──claim──▶ CLAIMED ──submit──▶ SUBMITTED ──payout──▶ PAID
```

| Slot | Constant            | Caveat            | What it guarantees |
|:---:|---------------------|-------------------|--------------------|
| `2` | `TITLE_HASH_SLOT`     | `WriteOnce`       | the title is fixed at posting |
| `3` | `REWARD_SLOT`         | `WriteOnce`       | the promised reward cannot be re-priced after a worker commits |
| `4` | `STATE_SLOT`          | `StrictMonotonic` | `OPEN→CLAIMED→SUBMITTED→PAID`, no going back, no re-entering a state (so: no double-claim, no re-open, no double-payout) |
| `5` | `CLAIMANT_HASH_SLOT`  | `WriteOnce`       | **first-claimer-wins** — a claim cannot be overwritten to steal the bounty |
| `6` | `SUBMISSION_HASH_SLOT` | `WriteOnce`      | the submitted artifact hash is fixed at submission |

`StrictMonotonic` on `STATE_SLOT` is doing a lot of work: because a transition must move
to a **strictly greater** code, re-writing the same code is rejected. That single caveat
gives no-double-claim, no-re-open, and no-double-payout for free.

It is built from dregg primitives only — `FactoryDescriptor`, `Effect::SetField` /
`Effect::EmitEvent`, `Authorization::Signature` from `AppCipherclerk::make_action`, and
`StateConstraint` slot caveats. There is **no** domain-specific bounty `Effect`, **no**
`Authorization::Unchecked`, **no** placeholder signature.

## Axis 2 — the deos surface (`bounty_app` / `register_deos`)

The lifecycle composed as a `DeosApp`: `view_bounty` is a cap-only read; `claim` /
`submit` / `payout` are **gated** affordances carrying a live-state precondition (the cell
is in exactly the state the op advances FROM), so a worker sees `claim` LIT on an OPEN
bounty and DARK the instant it is claimed (the htmx tooth). The fire is a real verified
turn the executor re-enforces the full program on. `register_deos(ctx)` seeds the cell and
mounts the whole axum surface (per-viewer projection, `/manifest`, `/surface.js`,
`dregg://` publish, rehydratable snapshot). See `tests/deos_seam.rs` (the
fire→full-`CellProgram` seam) and `tests/reexpress_deos_app.rs`.

## Axis 3 — the service cell (`invoke()`, `src/service.rs`)

The lifecycle as a first-class typed interface, driven through the `invoke()` front door
(cells-as-service-objects — no `Effect::Invoke`, no kernel change; a method desugars to
the ordinary verified effects it names, routed by the SAME verified DFA router the protocol
uses):

| method | semantics | auth | desugars to |
|---|---|---|---|
| `post(title, reward)` | Replayable | `Signature` | `SetField(TITLE, REWARD, STATE=OPEN)` |
| `claim(claimant)` | Replayable | `Signature` | `SetField(CLAIMANT, STATE=CLAIMED)` |
| `submit(artifact)` | Replayable | `Signature` | `SetField(SUBMISSION, STATE=SUBMITTED)` |
| `payout()` | Replayable | `Signature` | `SetField(STATE=PAID)` |
| `view()` | **Serviced** | `None` | — (the named OFE seam: a read, not a turn) |

```rust
use starbridge_bounty_board::service::BountyService;
use dregg_app_framework::InvokeAuthority;

let svc = BountyService::new(bounty_cell);
let turn = svc.claim(&cclerk, "bob", InvokeAuthority::Signature)?; // routed + cap-gated + signed
executor.submit_turn(&turn)?;                                      // the executor re-enforces the program
```

The cap-gate bites twice (at the front door AND the executor); a competing second `claim`
is an executor refusal (`WriteOnce(CLAIMANT)`); `view` refuses to desugar (it names the
serviced seam honestly). Register the interface with `service::register_interface(&mut
registry, cell)` so the Service Explorer resolves the real `Signature`/`Serviced` shape.

## Axis 4 — the deos-view card (`src/card.rs`)

The app's UI as a renderer-independent `deos.ui.*` view-tree: a `vstack` of a header, a
live `bind` on `STATE_SLOT` (re-reads the lifecycle off the ledger), and one `button` per
lifecycle method carrying its `onClick = {turn, arg}` (the button `turn` names ARE the
service method symbols). The SAME tree renders three ways via `deos-view` — native gpui
pixels, a browser-loadable HTML document, and a discord embed.

```rust
let card_json = starbridge_bounty_board::card::bounty_card_json(); // serializable deos.ui.* JSON
```

The card is pure `serde_json` data (no dependency on the `deos-view` renderer crate, which
pulls the mozjs + gpui elephants and is a standalone excluded workspace). The deos world's
renderers consume the JSON; this crate owns the card definition and proves it well-formed.

## A payout MOVES VALUE, and the reward is a PROMISE

⚑ Until 2026-07-28 all three payout builders here carried `SetField` + `EmitEvent`
and **no `Effect::Transfer` at all**, so `/bounty payout` rendered "Bounty Paid",
emitted `bounty-paid`, advanced `STATE` to PAID, and moved no balance anywhere. A
claimant held a receipt for a payment that never happened.

`build_payout_actions` now returns the payment leg and the settle leg as roots of
**one turn**: a conserving kernel `Effect::Transfer` (from the shared `Payable`
desugar, `dregg_app_framework::pay_effects` — the same one `BountyTreasury::payout`
resolves to) and the `STATE=PAID` advance. They commit or roll back together, so
there is no accepted turn in which the bounty reads PAID and nobody was paid. A
payer who cannot cover the reward is an `InsufficientBalance` refusal that takes
the PAID stamp down with it; a zero amount is `RewardRefused::NothingToPay` before
a turn exists.

⚠ **The reward is not held in escrow, and this crate no longer says it is.** The
bounty cell CANNOT hold it: the executor evaluates a touched cell's `CellProgram`
per action over *every cell any effect touches*, including a `Transfer`
destination, so `StrictMonotonic(STATE)` demands that any action crediting the
bounty cell also strictly advance its `STATE` — while a `Transfer` whose `from` is
not the action's target requires the source cell's `send` permission to be
`AuthRequired::None` (a user cell's is `Signature`). Those two rules have no common
solution. The poster therefore settles from its own balance, and between `post` and
`payout` nothing stops it spending the money: a claimant is protected against a
payout that LIES, not against a poster who goes broke. Real escrow needs a separate
holding cell with no `StrictMonotonic` on it — the shape `BountyTreasury` already
is — and that is a design fork (who mints it, who holds its cap, what happens to an
abandoned bounty), not wiring.

⚠ Nothing binds the payee to the committed `CLAIMANT_HASH` at the executor: no
`StateConstraint` relates a `Transfer` destination to a state slot. The Discord and
CLI surfaces check it against the node's committed field view before submitting.
Making it an executor refusal needs a new constraint atom, which is Lean-authored
work on the constraint language.

## What this crate exports

```rust
// Axis 1 — verified core
bounty_factory_descriptor() -> FactoryDescriptor
bounty_cell_program()       -> CellProgram
build_post_action / build_claim_action / build_submit_action / build_payout_actions
payment_effects / settle_effects / payout_effects   // the value leg + the state leg
register(ctx: &StarbridgeAppContext) -> [u8; 32]   // mount factory + inspector + deos surface

// Axis 2 — deos surface
bounty_app(cclerk, executor) -> DeosApp
register_deos(ctx) -> DeosApp                       // seed + mount the composed surface
fire_claim / fire_submit / fire_payout

// Axis 3 — service cell
service::BountyService                              // .post / .claim / .submit / .payout / .view
service::interface_descriptor() / service::register_interface(...)

// Axis 4 — deos-view card
card::bounty_card_value() -> serde_json::Value
card::bounty_card_json()  -> String
```

## Tests

```sh
cargo test -p starbridge-bounty-board
```

| Test | Surface | What it pins |
|---|---|---|
| `src/lib.rs::tests::*` | `CellProgram::evaluate` directly | descriptor shape + every slot caveat in isolation |
| `src/service.rs::tests` | the `invoke()` builder | typed interface shape + front-door refusals |
| `src/card.rs::tests` | the view-tree | the card is a well-formed `deos.ui.*` tree whose buttons carry the service methods |
| `tests/factory_birth.rs` | **the real executor** | birth → full lifecycle accepted; theft / replay / re-price / re-open / double-payout REFUSED |
| `tests/service.rs` | **the real executor** | the lifecycle through `invoke()`: authorized commit, front-door cap-gate, executor re-enforcement, serviced seam |
| `tests/deos_seam.rs` | **the real executor** | the gated fires + the fire→full-`CellProgram` seam |
| `tests/reexpress_deos_app.rs` | the axum surface | per-viewer projection, web-of-cells publish, rehydration, manifest, web component |

## See also

- `../kvstore/`, `../escrow-market/src/service.rs` — the other `invoke()` service-cell exemplars (axis 3).
- `../../deos-view/` — the card renderers (native / web / discord); `docs/reference/deos-view.md`.
- `../../docs/deos/DEOS-APPS.md` — the deos app model and the rebuild plan.
- `../../docs/guide/` — the learn-by-example guide this app set is tied to.
