# Service Discovery / Announcement — the desktop surface

A deos desktop surface for **service discovery + announcement**: browse the
services a live image (and, ahead, the federation) publishes, read an announced
cell's interface, announce a service of your own as a verified turn, and
discover + invoke a service by interface. This is the user-facing face of
dregg's *cells-as-service-objects* directory.

This document grounds the existing backend (file:line), states what UI exists
today, designs the surface, maps every UI action to a real backend call, and
names the first slice (built) + the cleanest next builds.

---

## 1. The backend that exists (grounded)

Service discovery in dregg is assembled from four real, separately-grounded
pieces. None of them had a directory-browsing / announcement *desktop surface*
before this work.

### 1.1 The directory primitive — `dregg-directory`

`directory/src/directory.rs` is the canonical named-capability directory: a
`Directory` trait with the four operations the whole design rests on
(`directory/src/directory.rs:90`):

- `register(name, entry) -> Version` — bind a name to a `ResourceHandle`
  (`:97`); idempotent on exact match, conflicts on a different value
  (`:228`).
- `lookup(name, height) -> &DirectoryEntry` — resolve, with revocation +
  expiry errors (`:102`, `:252`).
- `revoke(name) -> Version` — mark revoked; subsequent lookups fail (`:106`,
  `:268`).
- `discover(filter) -> Listing` — search by `name_prefix` / `required_tags` /
  `kind` / `include_revoked` (`:109`, `:282`; `DiscoveryFilter` at `:125`).

A `DirectoryEntry` (`directory/src/directory.rs:40`) carries a
`ResourceHandle` (federation + cell + swiss, `directory/src/lib.rs:74` — a
`dregg://` sturdy-ref), an `EntryKind` (`Service` / `SubDirectory` /
`DataSource` / `Factory` / `Capability`, `:25`), a description, tags, a
registration height, an optional expiry, and a `revoked` flag. The reference
implementation is `InMemoryDirectory` (`:161`); `DfaRoutedDirectory`
(`directory/src/dfa_routed.rs`) adds governance-bound atomic table swaps;
`MetaDirectory` (`directory/src/meta.rs`) is the directory-of-directories for
federation peer discovery.

It is a **userspace primitive**, not a wire protocol and not a cell program
(`directory/src/lib.rs:40`). Its stated stance: a directory *"emits standard
`Effect::SetField` + `Effect::EmitEvent` actions rather than introducing a new
effect variant"* (`directory/src/lib.rs:21`). The crate is lifted from
`rbg::directory::DirectoryCell` (`rbg/src/directory.rs:1` — "a directory IS a
capability"; holding a reference grants list / get / post authority, scoped to
a federation's constitution membership).

### 1.2 The interface registry — `InterfaceDescriptor`

`cell/src/interface.rs` is how a cell *announces what service it offers* and
another *discovers it*:

- `InterfaceDescriptor` (`cell/src/interface.rs:215`) — a named set of
  `MethodSig`s, content-addressed by `interface_id` (the sorted-Poseidon2 root
  over the method leaves — the same machinery the cap-root uses, `:246`).
- `MethodSig` (`:134`) — one method: its `symbol` (BLAKE3 method-name hash),
  `args_schema` (arity), `auth_required`, and `semantics`
  (`Replayable` vs `Serviced`, `:73`).
- `InterfaceDescriptor::derive_replayable(program)` (`:294`) — **auto-derives
  the interface a cell already implements**: every `MethodIs` guard in the
  cell's `Cases` program becomes a `Replayable` method, for free, no extra
  authoring.
- `to_route_table()` / `route_method()` / `route_membership_witness()`
  (`:339`, `:361`, `:395`) — a cell's interface IS a verified `dregg-dfa`
  route table; method dispatch is the AIR-provable router classification, and
  membership is light-client-witnessable.

The interface is a **non-committed userspace object** (`cell/src/lib.rs:40`):
the service-object / `invoke()` layer lives *above* the effectvm, so the
descriptor is not folded into the cell commitment. Discovery is therefore over
the program (derive), not over a commitment.

### 1.3 The service front door — `invoke()`

`app-framework/src/invoke.rs` is the service-object front door at the app
layer. `invoke()` is NOT a kernel effect (`Effect::Invoke` was killed —
MEMORY: cells-as-service-objects); an invocation **desugars** to an ordinary
method-targeting turn carrying the underlying effects, with the one extra fact
("the invoked method is a member of the cell's committed interface") decided by
the verified DFA router. Found-by-interface, invoked-as-a-turn.

### 1.4 Federation discovery — `discovery.yml`

`.github/workflows/discovery.yml` is node↔node discovery across the federation:
every 30 min (or on a `node-state-updated` dispatch) it reads each node's JSON
off the `federation-state` branch and assembles a `discovery.json` (node
endpoints + intent-service). `dfa-federation/src/lib.rs` backs governed
route-table swaps with the `FederationCommittee` BLS threshold verifier;
`net/src/gossip.rs` is the gossip plane. `app-framework/src/discovery.rs`'s
`NameserviceClient` is the HTTP client an app uses to `register` /`deregister`
itself in a running federation's nameservice (`POST /register`).

### 1.5 Summary table

| Concern | Backend | Where |
| --- | --- | --- |
| named directory (register/lookup/revoke/discover) | `dregg-directory` | `directory/src/directory.rs` |
| directory-as-capability, scoped to constitution | `rbg::directory` | `rbg/src/directory.rs` |
| a cell's typed published interface | `InterfaceDescriptor` | `cell/src/interface.rs` |
| find-by-interface + invoke | `invoke()` (desugars, no kernel effect) | `app-framework/src/invoke.rs` |
| federation node discovery | discovery workflow + nameservice client | `.github/workflows/discovery.yml`, `app-framework/src/discovery.rs` |

---

## 2. What UI exists today

**Per-cell, yes; directory-wide / announcement, no.**

- `Tab::ServiceExplorer` (🛰 SERVICES, `starbridge-v2/src/cockpit/mod.rs:322`,
  rendered by `panels_workspace.rs:228`) is the **Postman for ONE focused
  cell**: it discovers a cell's published interface
  (`ServiceExplorer::build` → `derive_replayable`,
  `starbridge-v2/src/service_explorer.rs:140`), lists each method with arity /
  auth / semantics / cap badge, and INVOKES a replayable method as a real
  verified turn.
- `Tab::InspectAct` (INSPECT-ACT) is its affordance-vocabulary sibling
  (`peek/touch/write/grant`).

There is **no surface that lists the directory** — no "every service in the
image / federation", no announced-interface catalog, and no announce
affordance. `grep` over `starbridge-v2/src/cockpit/` finds directory/announce
references only inside the app-launcher and web panels, none of them a service
directory. That gap is what this surface fills.

---

## 3. The surface design

A **Service Directory** surface — the whole-image (and, ahead,
whole-federation) sibling of the per-cell Service Explorer. Four affordances,
each mapped to a real backend call.

### (a) BROWSE the directory / discovered services

A list of every service the image publishes: one row per discovered service
with its label, kind, `interface_id` (short-hex), method count, and an
`ANNOUNCED` badge. A filter bar (prefix / kind / only-announced) drives the
`discover` call. A "local ⇄ federation" toggle scopes the source.

> Backend: `ServiceDirectory::discover(world, filter)` — scans `World::ledger()`
> (`starbridge-v2/src/world.rs:525`), derives each cell's
> `InterfaceDescriptor::derive_replayable`, and presents the
> interface-publishing cells. Federation scope ahead: `MetaDirectory` +
> `discovery.json`.

### (b) READ an announced cell's INTERFACE

Selecting a row opens its interface: the method list (name/symbol, arity,
`auth_required`, `Replayable`/`Serviced`), the `interface_id`, and — for the
viewer — a cap badge per method. This *is* the existing Service Explorer body;
the directory hands it a selected cell.

> Backend: reuse `ServiceExplorer::build(world, cell, viewer, rights)`
> (`starbridge-v2/src/service_explorer.rs:140`). No new code; the directory is
> the *index*, the explorer is the *detail*.

### (c) ANNOUNCE a service (publish an interface — a verified turn)

An "announce" affordance on any service-publishing cell: it publishes that
cell's interface to the directory as the operator's own verified turn. The
outcome (committed receipt / in-band refusal) is shown inline; the row's
`ANNOUNCED` badge lights on the next refresh.

> Backend: `ServiceDirectory::announce(world, announcer, service)` — emits an
> `Effect::EmitEvent` (topic `dregg.directory.announce`, data = service
> `interface_id` + service cell id + method count) as the announcer's turn
> through `World::commit_turn` (the directory crate's "emit standard effects"
> stance, `directory/src/lib.rs:21`). **Design note (load-bearing):** the
> announcement is the *announcer's* turn referencing the service, NOT a
> method-call on the service cell — a service cell with a strict `Cases`
> program default-denies any undeclared method (Cav-Codex Block 4
> operation-discrimination, `cell/src/program/eval.rs:87`), so impersonating
> the service program would be refused. The executor still gates the
> announcer's own program + permissions.

### (d) DISCOVER + connect/invoke by interface

From an announced service, "open" routes to the Service Explorer focused on it;
"invoke" fires a replayable method as a real verified turn. Find-by-interface:
filter the directory to a target `interface_id` (or `required_tags`) and the
matching services surface, ready to open.

> Backend: `ServiceExplorer::invoke(world, symbol, args, effects, rights)`
> (`starbridge-v2/src/service_explorer.rs:234`) — the verified DFA router
> resolves the method, semantics + cap gate, desugar to a method-targeting
> turn, commit. Serviced methods are surfaced honestly as the named OFE seam,
> never silently invoked.

### Renderer-independence (the liberation principle)

The surface is specified as a **deos-view card** — `section` (the filter bar +
counts), `list` (the discovered services, each row a `tile`/`button`),
`menu` (kind/scope filters), `button` (announce / open / invoke) — so it
renders identically in gpui, on seL4, or on android, and the buttons fire real
turns through the same `World`. The model
(`starbridge-v2/src/service_directory.rs`) is already gpui-free and produces a
flat `all_text()` projection, so the deos-view card binding is a pure
view-layer mapping with no model change. (The deos-view card vocabulary itself
— `list`/`section`/`menu`/`button`/`tile` → real turns — is carried by the
now-landed card-mounting lane: `starbridge-v2/src/card_pane.rs` mounts a
`deos_view` view-tree as a live gpui surface, hosted as a dock pane via
`starbridge-v2/src/dock/card_surface.rs`. See §5 and `docs/reference/deos-view.md`.)

---

## 4. The first slice (built this pass)

`starbridge-v2/src/service_directory.rs` — a gpui-free, `cargo test`-able model,
the sibling of `service_explorer.rs`, registered in `lib.rs` under
`embedded-executor`:

- **`ServiceDirectory::discover(world, filter)`** — BROWSE: scans the live
  ledger, derives each cell's interface, lists the service-publishing cells
  with `interface_id` / method count / kind, and marks each `announced` by
  reading committed announce events back out of the recorded turn history
  (`announced_interface_ids`). Filters: `label_prefix`, `kind`,
  `only_announced`, `include_non_services`.
- **`ServiceDirectory::announce(world, announcer, service)`** — ANNOUNCE: a real
  verified turn (`Effect::EmitEvent`, announce topic) through the embedded
  executor; refuses in-band when the service is absent / publishes no interface,
  and surfaces the executor's own refusal (`by_executor`) when the announcer's
  program/permissions reject the turn.
- **`ServiceDirectory::all_text()`** — the flat projection for the deos-view
  card binding + headless bakes + tests.

Seven tests cover: discover reads the real ledger; **announce commits a real
turn and discover reads it back** (the loop closes over the ledger); non-service
and absent-cell refusals are in-band; prefix/kind filtering; and the
non-services widening. The model is verified clean (`cargo check`).

---

## 4b. The directory backend (built this pass) — service-factory crafting + deepened discovery

The first slice (§4) lives *inside* the cockpit's embedded `World`
(`starbridge-v2`). This pass deepens the **renderer-independent backend** in the
canonical `dregg-directory` crate, so the model the card reads is grounded where
the directory primitive itself lives. Three new pieces, all gpui-free,
`cargo test`-able (40 tests green in `dregg-directory`), no `dregg-turn`
dependency.

### (i) Service-FACTORY crafting — `directory/src/service_factory.rs`

You can now **craft a factory whose creations ARE services.**
`ServiceFactory::craft(&["send", "dequeue"], CellMode::Hosted)` builds:

1. the **interface-publishing child program** — a `CellProgram::Cases` whose
   `MethodIs` guards are exactly the crafted methods (plus an `Always` catch-all),
2. the `InterfaceDescriptor` that program publishes (auto-derived), and
3. a `dregg_cell::factory::FactoryDescriptor` bound to it
   (`child_program_vk = canonical_program_vk(child_program)`). The `factory_vk` is
   `derive_key(interface_id ‖ mode)`, so **a service factory's identity is a
   function of the service it produces** — same interface + mode ⇒ same factory.

`ServiceFactory::birth(owner, token, height)` validates the creation against the
real `FactoryDescriptor::validate_creation` gate (a forged child VK / out-of-
template cap / mode mismatch is refused *before any cell is born*), derives the
new cell id exactly as the executor does (`CellId::derive_raw(owner, token)`), and
returns a `BornService` carrying the program, the published interface, and a
factory `Provenance`. The key fact is *checked, not trusted*:
`BornService::publishes(interface_id)` re-derives the interface from the born
cell's live program. `BornService::announce(announcer)` then yields an
`AnnounceRecord` whose `event_data()` (`[interface_id, cell, method_count]`,
topic `dregg.directory.announce`) is **byte-identical to the `starbridge-v2`
slice's announce payload** — the two announce models agree.

> **The honest seam (named).** The deployed `Effect::CreateCellFromFactory` arm
> (`turn/src/executor/apply.rs:2233`) installs the born cell's `program` from the
> descriptor's *perpetual slot caveats* as `CellProgram::Predicate(...)` plus the
> child-VK identifier — it does **not** yet install a `Cases` interface-publishing
> program, so a literal on-ledger birth would publish the *empty* interface. The
> service-factory models the birth at the crafting layer (binding the `Cases`
> program by VK, carrying it on `BornService`); installing the child program
> through the executor (a VK-touching change) is the named follow-on.

### (ii) Discover by INTERFACE + by METHOD — `directory/src/service_index.rs`

`ServiceIndex` keys announced services by name (like the base directory) but each
record carries the service's `InterfaceDescriptor`, so discovery deepens past
name/tag:

- `discover_by_interface(interface_id, height)` — every live service whose
  interface content-address matches.
- `discover_by_method(&symbol, height)` — every live service that offers a method,
  resolved through the **same verified `dregg-dfa` router** the executor's
  dispatch uses (`InterfaceDescriptor::route_method`), not an ad-hoc scan; an
  undeclared method finds nothing (fail-closed).
- `membership_witness(name, method, height)` — the **light-client-witnessable**
  proof a discovered service genuinely offers a method (the existing DFA
  route-membership `AirTrace` + route-table root), so discovery is not a trusted
  claim.
- `announce` carries the anti-forgery tooth `InterfaceDescriptor::verify_id`: a
  record whose carried `interface_id` does not match its own methods is refused
  (`ServiceIndexError::ForgedInterface`). `announce_born` is the slice-1↔slice-2
  weld: a crafted factory births a service, the service announces itself in.
- `discover(filter, height)` (kind / tags / prefix), `revoke`, `lookup`, and
  `gc_expired` mirror the base directory's revocation + expiry semantics.

### (iii) Federation scope — `FederatedServiceIndex`

`FederatedServiceIndex` composes a local `ServiceIndex` with peer indices
catalogued by `MetaDirectory` (the directory-of-directories). `add_peer(peer,
index)` registers the peer in the meta-directory and attaches its index;
`discover_by_interface` / `discover_by_method` then sweep the local image **and
every peer federation** in the meta-directory's peer order, tagging each
`FederatedHit` with its origin federation (`local: bool` + `federation_id`). This
is the model the "local ⇄ federation" toggle (§3a) reads — the same query, widened
to peers, ready to be fed by the assembled `discovery.json` (§1.4).

## 5. The cleanest next builds (named, ordered)

1. **The cockpit panel + tab** — LANDED: `panels_service_directory.rs` renders
   `ServiceDirectory` as `Tab::ServiceDirectory` (📇 DIRECTORY,
   `starbridge-v2/src/cockpit/mod.rs` — the tab, label, and panel are registered),
   a list of rows each with "announce" + "open in 🛰 SERVICES". The coordinated
   `Tab` registration (`mod.rs`/`nav.rs`/`panels_workspace.rs`) + `deos-js`
   surface-count edit was made in a quiet window as planned.
2. **The deos-view card binding** — express the panel as a real deos-view card
   (mount on the sibling lane's `card_pane`/`card_surface`) so the surface is
   renderer-independent and the buttons fire `announce`/`invoke` turns.
3. **Canonical `dregg-directory` backing** — the backend landed (§4b):
   `ServiceIndex` (`directory/src/service_index.rs`) gives announce / named
   lookup / revocation / expiry / discover-by-interface / discover-by-method over
   `dregg_directory::{EntryKind, DiscoveryFilter}`. Remaining: bind the cockpit
   `ServiceDirectory` view-model to it (replace the local `ServiceKind` mirror).
4. **Cap-gated announce** — gate `announce` on the announcer holding authority
   over the service (the attenuation lattice `service_explorer` already
   threads), so announcement is an authorized act, not ambient.
5. **Service-factory crafting** — landed (§4b): `ServiceFactory`
   (`directory/src/service_factory.rs`) crafts a factory whose creations are
   services, births them, and auto-announces. Remaining: install the `Cases`
   child program through the executor's `CreateCellFromFactory` arm (the named
   VK-touching seam) so an on-ledger birth publishes the interface, not just the
   Predicate caveats.
6. **Federation scope** — backend landed (§4b): `FederatedServiceIndex` sweeps
   the local image + peer federations via `MetaDirectory`. Remaining: a
   "federation" toggle feeding it the assembled `discovery.json` (§1.4).
