# starbridge-apps: full-featuredness + interoperability census

> **STATUS — PARTLY SUPERSEDED (the keystone gap is CLOSED).** This census (2026-06-27)
> concluded the apps did NOT interoperate — 0 `Transfer`/`Mint`, no shared value medium, no
> DSI. That verdict has since been overtaken by the build. The **`Payable` DSI now exists**
> (`app-framework/src/payable.rs`, re-exported `app-framework/src/lib.rs` — `Payable`, `pay`,
> `pay_effects`, `PAY_METHOD`, `BALANCE_METHOD`, `payable_descriptor`), and the census's own §5
> "cleanest first interop win" is **BUILT**: `bounty-board` pays out a real `Effect::Transfer`
> into an `escrow-market` escrow cell that **settles it onward** over the same interface
> (`bounty-board/src/lib.rs`, `escrow-market/src/lib.rs`). Real `Effect::Transfer` now fires in
> `billing`, `bounty-board`, `escrow-market`, `execution-lease`, `subscription`; `first-room`
> emits `Effect::Mint`. The §1 histogram and §3 verdict below are the pre-DSI snapshot — read
> them as the "before". The one gap in §4 that is **still genuinely open**: no starbridge-app
> implements `RingTradeParticipant` (atomic multi-party ring barter — gap #5). Sections are
> annotated inline; verify code vs HEAD.

A read-only census of the ~28 app crates under `starbridge-apps/` (plus `shared/`),
answering one direct question: **how full-featured is each app, and do they
INTEROPERATE — does token/asset VALUE flow between them?**

The short answer, up front and honest (as of the census; superseded points marked):

- **Full-featuredness:** most apps are *real, individually sound* state
  machines — a factory-born cell whose installed `CellProgram` is re-checked by
  the verified executor on every touching turn, plus a service (`invoke()`)
  face, a deos card, and a real test suite. ~15 grade FULL, ~4 PARTIAL, ~2
  SKELETON.
- **Interop (SUPERSEDED — was NONE, now the value layer is wired):** at census
  time the apps did NOT interoperate — no value flowed between apps, no cap
  delegated across apps. That is **no longer true for value**: apps now transact
  over the shared per-asset ledger through the `Payable` DSI (real
  `Effect::Transfer` across an app boundary — `bounty-board` → `escrow-market`).
  What remains: no app yet implements `RingTradeParticipant` (atomic multi-party
  barter). The rest of this section is the pre-DSI diagnosis, kept as the record
  of what the gap *was* and how it was closed.

This *was* a gallery of isolated demos; the value-flow gap it diagnosed has since
been closed (the `Payable` DSI + the built `bounty-board`→`escrow-market` path).
The census's own thesis held: the substrate already existed (one verified per-asset
ledger, the shared-`World` launcher), and the fix was wiring, not primitives — that
wiring has now largely landed.

---

## 1. The shape every app shares (the AX3/AX4 pattern)

Each app is a Rust crate with a near-uniform skeleton:

- `src/lib.rs` — the **CellProgram** (the verified core): a method-dispatched
  `CellProgram::Cases([...])` whose `Always` case carries perpetual invariants
  (`WriteOnce`, `Monotonic`) and whose per-method cases bind the lifecycle teeth
  (`StrictMonotonic`, `AffineEq`, `FieldLteField`). Born from a
  `FactoryDescriptor` (`CreateCellFromFactory`) so the slot caveats are baked
  onto the cell *for life* and re-enforced by the executor on every turn.
- `src/service.rs` — the **AX3 invoke face**: a typed `InterfaceDescriptor` +
  method dispatch via `dregg_app_framework::invoke()`. Crucially **there is no
  `Effect::Invoke`** (it was killed; every app's service.rs says so in its
  header) — `invoke()` *desugars* a method call into the underlying ordinary
  verified effects on the **one target cell**.
- `src/card.rs` — the **AX4 deos card**: a renderer-independent `deos.ui.*`
  view-tree.
- `src/reactor.rs` (8 apps) — the AX5 reactive twin: watches a cell and
  re-fires effects.

**Effect vocabulary, across ALL apps (histogram — PRE-DSI snapshot, 2026-06-27):**

```
 385  Effect::SetField
 188  Effect::EmitEvent
  29  Effect::GrantCapability
   8  Effect::React
   6  Effect::RevokeDelegation
   2  Effect::RevokeCapability
   1  Effect::RegisterName / IssueCredential / CastVote
   0  Effect::Transfer
   0  Effect::Mint
   0  Effect::Burn
```

**At census time this histogram was the whole interop story in one glance** — every
app modelled its world as `SetField` (scalar state) + `EmitEvent`, and not a single
app emitted a `Transfer`, `Mint`, or `Burn`. **That has since changed:** real
`Effect::Transfer` now fires in `billing`, `bounty-board`, `escrow-market`,
`execution-lease`, and `subscription`, and `first-room` emits `Effect::Mint` —
so the three bottom rows are no longer zero. dregg's per-asset Σδ=0 conservation
(`turn/src/action.rs`) is the value layer the apps were supposed to transact over,
and the value-carrying apps now *do* touch it (via the `Payable` DSI). "Value" in
the apps the census still leaves untouched remains a *scalar field on the app's own
cell*, not yet a conserved asset that can move to another cell.

---

## 2. Full-featuredness census (graded)

Grades: **FULL** = rich multi-method lifecycle + meaningful state + real test
suite; **PARTIAL** = a working but thin flow; **SKELETON** = stub / exemplar.

| App | Methods (CellProgram) | Grade | Core flow |
|---|---|---|---|
| `nameservice` | ~8 | FULL | register → resolve/set-target → renew → transfer → revoke (WriteOnce/Monotonic) |
| `governed-namespace` | ~6 (DFA-routed) | FULL | propose table update → vote (threshold) → commit → register service |
| `identity` | ~5 | FULL | issue credential → present (selective disclosure) → verify → revoke |
| `subscription` | ~5 | FULL | grant pub/consumer → publish → consume (bounded ring buffer) |
| `sealed-auction` | commit/close/reveal/settle | FULL | commit-reveal sealed-bid auction, **settles over a real per-asset ledger** |
| `gallery` | submit/close/reveal/curate | FULL | commit-reveal art curation (WriteOnce board + StrictMonotonic phase) |
| `compute-exchange` | post/bid/settle | FULL | escrow/budget gate (`FieldLteField(BID≤BUDGET)`, `AffineEq(PAID+REFUNDED==BUDGET)`) |
| `escrow-market` | list/fund/ship/settle | FULL | escrow lifecycle; **value is scalar fields, not a real asset ledger** |
| `bounty-board` | post/claim/submit/payout | FULL | StrictMonotonic state machine, first-claimer-wins (claimant WriteOnce) |
| `privacy-voting` | open/tally/close | FULL | poll lifecycle + per-voter one-vote-per-cell ballot (WriteOnce) |
| `compartment-workflow-mandate` | init/advance | FULL | clearance-graph + spend-policy admission mandate |
| `storage-gateway-mandate` | get/put/list | FULL | volume-ceiling mandate |
| `swarm-orchestration` | ~6 | FULL | multi-agent orchestration mandate (~30 tests) |
| `tool-access-delegation` | ~5 | FULL | attenuated tool-cap delegation + budget |
| `tussle` | commit/reveal | FULL | joint-turn fog-of-war commit-reveal (no service.rs/card.rs — pure turn demo) |
| `agent-orchestration` | 1 symbol | PARTIAL | mandate engine (23 tests, full infra, thin method surface) |
| `agent-provenance` | append-only | PARTIAL | tamper-evident provenance chain |
| `supply-chain-provenance` | ~3 | PARTIAL | single-custody-law provenance (1 slot, 21 tests) |
| `polis` | 0 (reactor-driven) | PARTIAL | governance-as-protocol; 5 sub-cell families, reactor→service certify |
| `kvstore` | put/get/delete | SKELETON | the first `invoke()`-front-door demo; no factory cell |
| `first-room` | — | SKELETON | **composition exemplar** (runs cwm + escrow side-by-side; see §3) |

Test depth is real where it's claimed: governed-namespace ~56, nameservice ~51,
subscription ~46, sealed-auction/swarm ~30 each. The FULL apps' teeth genuinely
bite on the verified commit path (a swapped sealed submission, an over-budget
bid, a rewound phase are real executor refusals — see each app's
`tests/deos_seam.rs` / `tests/factory_birth.rs`).

**Verdict on full-featuredness:** as *individual* apps, this is a strong
collection — not toy demos. Each FULL app is a verified lifecycle with biting
caveats. The thinness is not in the apps; it is *between* them.

---

## 3. The interop verdict (the key question)

> **SUPERSEDED for value flow.** §3a's "NONE" was true at census time and is now false:
> the `Payable` DSI (`app-framework/src/payable.rs`) and the built
> `bounty-board`→`escrow-market` `Transfer` path give a real cross-app value flow.
> §3b (cap/service interop) and §3c/§3d largely still stand as written. Kept below as the
> diagnosis that drove the fix.

### 3a. Token/asset value flow between apps: **was NONE at census time; now WIRED via the `Payable` DSI.**

- **No app emits `Transfer`/`Mint`/`Burn`** (§1 histogram). The kernel value
  layer (`AssetId := issuer-cell`, per-asset Σδ=0, `turn/src/action.rs`) is
  almost entirely unused by the apps.
- The apps that *model* money model it as **scalar fields on their own cell**.
  `escrow-market`'s "conservation" is an `AffineEq` over three slots of *one*
  escrow cell (`escrow-market/src/lib.rs:154-161`: `RELEASED + REFUNDED −
  ESCROWED = 0`) written with `Effect::SetField`
  (`escrow-market/src/lib.rs:386-401`). It does **not** use
  `dregg_intent::verified_settle` / `VerifiedLedger` / `settle_ring_verified`
  (grep: zero references). It is decorative in-cell arithmetic, not an asset
  that can leave the cell.
- **The lone exception** is `sealed-auction`: it *does* fold its award through
  the real verified per-asset executor —
  `dregg_intent::verified_settle::settle_ring_verified`
  (`sealed-auction/src/lib.rs:77-78, 323`) over a `VerifiedLedger`, a balanced
  two-leg ring (winner pays seller; slot delivers task-token —
  `sealed-auction/src/lib.rs:286-304`). This is *genuine* Σδ=0 value flow. **But
  that `VerifiedLedger` is the auction's OWN in-process ledger**, funded by its
  own `fund_ledger()` helper (`sealed-auction/src/lib.rs:342`) — not a shared
  ledger that any *other* app's cell holds a balance in. The value conserves
  *within sealed-auction*; it never crosses an app boundary.

There is **no path** by which a payment held in one app (gallery's submission, a
bounty's reward, an escrow's funds) becomes a balance another app's cell can
spend. A `Transfer` *could* move an asset between any two cells of one `World`
(they're all cells in one ledger) — but no app builds that effect, and no app
references another app's cell id or asset id.

### 3b. Cap / service interop across apps: **NONE.**

- Each app grants its caps to **its own operating cipherclerk** (e.g.
  `first-room/src/scenario.rs:236-240, 264-268` grant both cells' owner caps to
  the *same* `payer`). No cap is ever delegated *from* one app *to* another.
- `invoke()` (`app-framework/src/invoke.rs:30-59`) is **single-cell** method
  dispatch: resolve interface → cap-gate → desugar to *that cell's own*
  effects. It is **not** a path for one app to call another app's service. There
  is no cross-cell call semantics.
- `polis`'s reactor→service "composition" is **intra-app**: the reactor
  (`polis/src/reactor.rs`) watches polis's own council cell and re-fires polis's
  own `certify` effects. The `starbridge_polis::…` imports are polis's *own*
  library crate, not sibling apps. polis's five sub-cell families share **one**
  cipherclerk cell id and explicitly cannot run concurrently
  (`polis/src/deos.rs:1080-1090`).

### 3c. Shared World: **physically shared, transactionally inert.**

The cockpit launcher is `starbridge-v2/src/app_registry.rs`
(`AppRegistry`/`AppSubstrate`), driven by `powerbox.rs::launch_on_world`.

- **Framework-substrate mode isolates each app:** `AppSubstrate::new`
  (`starbridge-v2/src/app_registry.rs:74-83`) mints a **fresh** cipherclerk + a
  **fresh** `EmbeddedExecutor` per app. The comment says why, plainly: *"gallery
  / sealed-auction / bounty-board all back their primary cell on the executor's
  OWN cell (`cipherclerk.cell_id()`), so two apps on one shared executor would
  collide on that cell."* This is the **structural root** of the non-interop:
  every app pins its primary cell to *its* cipherclerk's identity cell, so two
  apps literally cannot share an executor without colliding.
- **`launch_on_world` mode** *can* place multiple apps' distinct cells on one
  `World` ledger (`app_registry.rs:528`, `powerbox.rs:1063`) — but each app
  still seeds a *distinct* cell from its *own* fresh cipherclerk, and **no entry
  wires any cross-app transfer or cap grant.** The only thing genuinely shared
  is the ledger between a *fire and its inspector* (one app's writer→reader),
  per the module header (`app_registry.rs:19-34`).

So: when co-launched, the apps co-reside on one `World` (value/caps *could*
flow), but nothing is wired to make them flow.

### 3d. `first-room` — the composition exemplar that doesn't compose value

`first-room` depends on `starbridge-compartment-workflow-mandate` +
`starbridge-escrow-market` (Cargo path deps) and runs both cells on **one**
`EmbeddedExecutor` (`first-room/src/scenario.rs:287-305`) — real shared ledger.
But the coupling stops there:

- **The "job funds the pay" link is a Rust `if`, not an enforced constraint:**
  `scenario.rs:326` — `if job_done { … settle … }`, where `job_done` is computed
  in Rust (`:320`). Nothing in the escrow cell's program references the job
  cell's cursor; you could settle with the job incomplete and the executor would
  commit it. The gating is the orchestrator's control flow, not a cap or a
  cross-cell caveat.
- **The pay is never credited:** the released amount is just a field on the
  escrow cell (`scenario.rs:341` reads `RELEASED_SLOT`); the colonist's
  `paid` is set from it **for rendering only** (`scenario.rs:511`). No
  `Transfer`, no balance movement between the two cells.
- The README is candid (`first-room/README.md:11-28`): "a COMPOSITION EXEMPLAR,
  not a four-axis app," with "no verified primitive of its own"; the real
  hand-off ("David's Door") is an unbuilt stub (`scenario.rs:607-608`).

`first-room` is a nice *teaching scenario* (two organs on one executor) but the
apps don't transact — completion and value are stitched in Rust, not in the
protocol.

### 3e. The framework already has the interop primitive — unused

`app-framework/src/ring_trade.rs:48` defines `RingTradeParticipant`, a trait
wrapping `dregg_intent::solver` with `exchange_offers`/`settle_leg`/`rollback_leg`
for **atomic multi-party ring settlement** — *exactly* the cross-app
value-exchange primitive that would make interop real. It is implemented in the
`intent` crate (`intent/src/cross_fed.rs`, `intent/src/generalized.rs`) but **no
starbridge-app implements it.** It is an unused door. (`multi_group.rs` is just a
federation allow-list, not a value/cap primitive.)

---

## 4. The interop gaps, ranked

What was missing to turn the gallery of isolated demos into an interoperating
ecosystem, most-foundational first. **Status flags added post-build:** #1 and #3
are now BUILT; #5 is the one still genuinely open.

1. **[BUILT] A shared asset/value layer the apps actually transact over.** At
   census time value was per-app scalar fields. This is **now done**: apps emit
   real `Effect::Transfer` over shared `AssetId`s (`billing`, `bounty-board`,
   `escrow-market`, `execution-lease`, `subscription`), so a payment in one app
   is a balance another can spend. The substrate always existed (Σδ=0 executor);
   the apps now *use* it instead of `SetField` for money. This was the keystone
   gap, and it is closed.

2. **A common currency / treasury cell.** For value to flow, apps need a shared
   denominating asset (a `dregg`/credit issuer cell whose `AssetId` every app
   references). Right now each app would invent its own. Mint once, let all apps
   price/pay/escrow in it.

3. **[BUILT] DSI — dregg standard interfaces (the #1 ERC lesson).** The
   `Payable` interface is **now real** (`app-framework/src/payable.rs`,
   re-exported from `app-framework/src/lib.rs`): `pay`/`pay_effects` desugar to a
   real conserving `Effect::Transfer`, `payable_descriptor` + `PAY_METHOD` /
   `BALANCE_METHOD` are the agreed method signatures, so any app holding a cap to
   a `Payable` cell can pay it without bespoke wiring. Consumed by `bounty-board`,
   `escrow-market`, `billing`, `subscription`, `execution-lease`, `first-room`,
   `vat`. Further DSIs (`Escrowable`, `Ownable`/transfer-of-control) are the
   natural follow-ons; `Payable` proved the shape.

4. **A cross-app invoke / cap-delegation path.** `invoke()` is single-cell
   today. Add the ability for app A's turn to (a) hold a cap to app B's cell and
   (b) invoke B's service as one effect in A's turn — so a bounty payout can
   *call* an escrow's `release`, or a gallery sale can *call* a treasury's
   `credit`. Cap delegation across apps is the authorization half of this.

5. **[STILL OPEN] Wire `RingTradeParticipant` into the apps.** The atomic
   multi-party ring primitive (`app-framework/src/ring_trade.rs`) is built and
   **still unused** (`grep 'impl RingTradeParticipant' starbridge-apps/` = 0 hits
   at HEAD). Having ≥2 apps implement it gives atomic cross-app barter (e.g.
   gallery-piece ⇄ escrow-funds in one all-or-nothing ring) with real Σδ=0
   conservation. This is the surviving gap in this list — the `Payable` DSI (#3)
   gives one-directional pay; the ring gives all-or-nothing multi-leg barter.

6. **A real shared-`World` co-launch that wires inter-app caps.** Extend
   `app_registry.rs`/`launch_on_world` so co-launched apps can be granted caps to
   each other's cells (today each app is pinned to its own cipherclerk cell and
   isolated). Decouple "an app's primary cell" from "the cipherclerk's identity
   cell" so apps can address *each other's* cells.

7. **Make `first-room`'s weld real.** Replace the Rust-`if` job→pay link with a
   cross-cell caveat (the escrow cell's `settle` precondition reads the job
   cell's completion cursor) and an actual `Transfer` crediting the colonist.
   This converts the exemplar from "two organs side by side" into the reference
   cross-app value flow.

---

## 5. The cleanest first interop win — **BUILT**

**Prove a single token value flow across two apps, end to end.** This is **done**:
a `bounty-board` payout emits a real `Effect::Transfer` into an `escrow-market`
escrow cell that **settles it onward** to the payee over the shared `Payable`
interface (`bounty-board/src/lib.rs`, `escrow-market/src/lib.rs` — "escrow receives
value as a real `Effect::Transfer` and settles it onward to the payee through the
shared `Payable` interface, so per-asset Σδ=0 holds"). The plan that landed:

> Mint a shared credit asset on a treasury cell. Co-launch `escrow-market` and
> `bounty-board` onto ONE `World`. Have a bounty payout in `bounty-board` emit a
> real `Effect::Transfer` of that asset into an `escrow-market` escrow cell,
> then have the escrow `settle` move it onward — and assert per-asset Σδ=0
> across the whole `World` (the kernel conservation check) at the end.

Why this one first:

- It is **small and self-contained** — two existing FULL apps, one new shared
  asset, ~one `Transfer` effect added to each side, one co-launch onto a shared
  `World` (the launcher already supports `launch_on_world`).
- It **exercises the keystone gap (#1) directly** — replacing `SetField`-money
  with real `Transfer`-money — and proves the conservation invariant holds
  *across* an app boundary, which is the thing that does not exist today.
- It **needs no kernel change**: `Effect::Transfer`, `AssetId`, the shared
  `World`, and the Σδ=0 executor all already exist. It is pure wiring.
- Once it's green, the same path generalizes: standardize it as a `Payable` DSI
  interface (#3), then any app can pay any other, and the `RingTradeParticipant`
  atomic-barter follow-on (#5) becomes the natural next step.

A second, complementary win is a **cross-app invoke**: give `bounty-board` a cap
to an `escrow-market` cell and have its payout *invoke* the escrow's `fund`
method (rather than emitting the transfer directly) — proving the service-compose
path (#4). But the value-flow win above is the cleaner first: it lights up the
asset layer the whole ecosystem was built to share, and it is the one that turns
"strangers in one building" into "parties that transact."

---

*Census basis: read-only across `starbridge-apps/*`, `app-framework/src/`,
`starbridge-v2/src/app_registry.rs`, `turn/src/action.rs`. Effect histogram and
grep counts are over `starbridge-apps/*/src/`. Grades reflect CellProgram method
count, state-slot count, and `#[test]` depth at HEAD; verify code vs HEAD as the
tree moves.*
