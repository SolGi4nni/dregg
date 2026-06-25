# The cockpit, membrane & desktop

Reference for the `starbridge-v2` shell subsystem: the cap-confined window
manager, the verified-scene compositor, the confined-fork membrane, the
distributed-card carry, the NT/Pharo desktop workbench, and the login ceremony.
Everything here is gpui-free and `cargo test`-able except the named gpui layers
(`cockpit`, `deos_desktop`, `login`), which paint over it.

All claims below cite `starbridge-v2/src/<file>.rs:<line>` or a Lean
`Module.decl`.

---

## Surfaces — cap-confined cell views

A **surface** is a window. Every dregg cell can be opened as its own surface, and
authority over a surface is a REAL `dregg_firmament` capability — not a bearer
secret (`surface.rs:60-83`).

- `SurfaceId(pub u64)` — a monotonic window handle, distinct from the backing
  `CellId` so a closed-then-reopened cell gets a fresh, non-confusable surface
  (`surface.rs:40-41`). `SurfaceId::region()` maps the surface to the compositor
  region (tile) it owns, keyed by the id so two surfaces own disjoint regions
  (`surface.rs:55-57`).
- `SurfaceCapability` pairs a `SurfaceId` with `authority: Capability` whose
  target is `Target::Surface { cell }` on the genuine `AuthRequired` lattice
  (`surface.rs:84-90`). `backing_cell()` reads that target (`surface.rs:109-114`).
  The constructor is crate-private — only the shell mints caps the firmament's
  `granted ⊆ held` gate will admit (`surface.rs:125-127`).
- `SurfaceKind` is `Console` (the privileged master-console, the cockpit's own
  trusted root) or `CellView` (a cap-confined view of one cell) (`surface.rs:132-141`).
- `Surface` holds NO copy of cell state — only the cell id, re-read from the live
  ledger on render, plus window-manager geometry/z/minimized fields whose mutators
  are crate-private (`surface.rs:192-277`).
- `Rect::translated` clamps the top-left to `>= 0`, so a surface you own cannot be
  dragged off the top/left of the shell (`surface.rs:175-182`).

The cap narrows by the real `is_attenuation` lattice and refuses to widen (a
read-only mirror cannot promote itself), tested at `surface.rs:298-333`.

---

## The Shell — the cap-first window manager

`Shell` (`shell.rs:190-251`) owns the surfaces, z-order, focus, layout, a REAL
firmament surface-fabric (`SurfaceBacking`), and the verified-scene `Compositor`.
It is two distinct gates: the **fabric** decides who may *drive* a window
(focus/move/share); the **compositor** decides what a surface may *paint* and
where input goes (`shell.rs:221-229`).

### Opening — minting authority

`open_console` / `open_cell_view` route to the single `open_surface` path
(`shell.rs:288-301`), which: allocates an id; seeds a fresh backing surface-cell
and an owner holder in the fabric at distinct deterministic seeds (so surfaces are
never confusable); installs the owner's full (`AuthRequired::None`) grant over the
backing cell; and hands back the REAL `Capability::surface(backing_cell, full)`
the opener now holds (`shell.rs:311-350`). The shell keeps NO secret.

### `authorize` — the gate every op runs first

`authorize` (`shell.rs:984-1006`) checks three things in order: (1) the surface is
live + registered; (2) anti cap-confusion — the cap's authority must target THIS
surface's backing cell (a cap minted for another window is refused); (3) the REAL
`fabric.invoke(owner, backing_cell, cap.rights())` — the `granted ⊆ held`
resolution. A fabricated or over-rights cap is refused by the genuine
`is_attenuation` gate. `close` additionally protects the console
(`shell.rs:357-375`); a closed surface's authority binding is dropped, so its cap
goes dead.

Every window op (`focus`, `raise`, `move_by`, `resize`, `set_minimized`,
`set_title`) authenticates the cap first (`shell.rs:382-455`).

### `share` — no-amplification at the window layer

`share` (`shell.rs:477-538`) authenticates the held cap, then delegates `narrower`
rights over the SAME backing cell to a recipient app via a genuine
`fabric.delegate` (an `Effect::GrantCapability` turn on the real executor). A
**widening share is rejected** (`ShellError::ShareDenied`); a narrowing share
commits, registering a NEW surface over the same backing cell, owned by the
recipient at the narrowed rights, and returns the recipient's handle.

### Migration — glass follows the cap (`process-pd`, unix)

`migrate_surface` (`shell.rs:843-860`) re-mints a held surface's cap onto a
confined child PD (`Target::HostPd`, the attenuating `migrate` verb that refuses a
widening) and installs a `PresentTransport`. Thereafter `present` / `route_input`
for that surface cross the firmament Endpoint to the child, which renders in its
own MMU-isolated memory; the in-process compositor never sees it again
(`shell.rs:710-728`, `shell.rs:868-919`). The migration registry and lookups are
unconditional; only the live dispatch is gated on `process-pd`.

---

## The Compositor — the verified scene (T1/T2/T3)

`compositor.rs` is the Rust realization of the Lean `Dregg2.Apps.Compositor`
`AppSpec` — the SAME `Scene`/`Surface` tuple and the SAME three scene-authority
teeth (`compositor.rs:1-5`). It casts output-integrity as unfoolability one hop
out: can the human at the glass be fooled? The pale ghost paints another cell's
region, labels a window as a cell it is not, or steals the focused keystroke. Each
tooth refuses one:

- **T1 NON-OVERLAP** (`t1_non_overlap`, `compositor.rs:301-316`) — a present's
  target region-set must be `⊆` the presenter's owned regions AND disjoint from
  every foreign surface. `granted ⊆ held` at the pixel layer.
- **T2 LABEL-BINDING** (`t2_label_bound`, `compositor.rs:348-355`) — the declared
  label must equal `label_of(presenter, source_state_root)`, the genuine
  owner-binding the SHELL computes, never the app's self-description. `label_of`
  is a deterministic mix over the owner id + the root (`compositor.rs:62-73`).
- **T3 FOCUS-EXCLUSIVITY** (`t3_focus_exclusive`, `compositor.rs:360-362`;
  `t3_input_routed`, `compositor.rs:385-387`) — at-most-one focused surface; input
  routes only to the unique focus holder. A double-focus scene rejects every
  present.

`scene_admit` (`compositor.rs:395-437`) folds the conjunction (T3-scene ∧ T1 ∧ T2
∧ T3-input ∧ a genuine frame advance, `new_digest != current`) into one admission,
mirroring the Lean `sceneAdmit`. `present` (`compositor.rs:448-469`) commits IFF
every tooth admits — advancing the frame digest and recording a `FrameCommit` in
the append-only frame log — and changes NOTHING on a refusal (fail-closed). A
refused present logs no frame (`compositor.rs:694-730`). `PresentError` carries the
specific tooth (`Overpaint`/`LabelSpoof`/`InputMisroute`/`DoubleFocus`/`NoSurface`/
`NoFrameAdvance`) with an operator-legible `explain()` (`compositor.rs:148-219`).

### Shell ↔ compositor wiring

`Shell::compose_scene` (`shell.rs:670-689`) rebuilds the `CompositorScene` each
present from the live (non-minimized) surfaces: each surface owns exactly its
`SurfaceId::region()`, its `source_state_root` and label are computed by the shell
from the live world (the T2 binding), and the focus flag is the shell's single
focus (T3 at-most-one by construction). `source_state_root`
(`shell.rs:1016-1041`) folds the owning cell's real balance ⊕ nonce ⊕ cap-count ⊕
lifecycle-tag; a missing cell folds to a distinct sentinel.

`Shell::present` (`shell.rs:710-761`) fires two gates in order: the window-cap gate
(`authorize`) then the scene-authority gate (`compositor.present`). A present that
holds a valid window cap and OVERPAINTS / SPOOFS / STEALS FOCUS is still refused.
`Shell::route_input` (`shell.rs:768-791`) delivers input only to the unique focus
holder through the compositor's T3 gate.

### Lean grounding

`metatheory/Dregg2/Apps/Compositor.lean` defines `t1NonOverlap`, `t2LabelBound`,
`t3FocusExclusive`, `t3InputRouted`, `labelOf`, `sceneAdmit` (`Compositor.lean:139-214`)
and proves the teeth: `present_rejected` (the generic tooth, `Compositor.lean:307`),
`present_overpaint_rejected` (`:325`), `present_label_spoof_rejected` (`:342`),
`present_double_focus_rejected` (`:358`), `present_input_misroute_rejected` (`:375`),
plus the keystones `present_conserves` (`:403`), `present_no_amplify` (`:414`),
`present_authorized` (`:424`), and `output_integrity_eq_unfoolability_on_scene`
(`:281`).

---

## The membrane — `shared_fork` (the confined fork with graduated consent)

"Invite someone to my computer." `shared_fork.rs` hands another principal a
confined fork of my world (`World::fork`, a deep-clone + the firmament
`Confinement`) whose culled cap-subgraph is graduated into three tiers
(`shared_fork.rs:1-40`). It reinvents no machinery — it is a partitioning + flow
over `powerbox`, `ReadCap`, `ConditionalTurn`, and `branch_stitch`.

### The three tiers

- **EMBEDDED** (`EmbeddedCap`, `shared_fork.rs:55-66`) — a real `CapabilityRef`
  granted into the guest's fork c-list via a genuine `Powerbox::grant`. The guest
  exercises it locally with no consent.
- **STUDYREF** (`StudyRef`, `shared_fork.rs:68-102`) — a read-only `ReadCap`; the
  guest can `open` exposed slots but holds no write cap. To mutate it must raise
  `upgrade_request` (a powerbox `CapabilityRequest` for write rights).
- **NETWORKBOUNDARY** (`NetworkBoundary`, `shared_fork.rs:104-155`) — no cap rides
  into the c-list. An attempted exercise opens a `ConsentRequest` shaped as a
  `ConditionalTurn` whose `ProofCondition::TurnExecuted` is the owner's grant,
  bound to a SPECIFIC grant-turn hash so a stray receipt cannot fire an arbitrary
  boundary.

### Construction

`SharedFork::construct` (`shared_fork.rs:321-362`) births the confined guest and
grants the embedded subgraph via real powerbox turns: an over-grant or unheld
target is simply DROPPED from the fork (never amplified, fail-closed). The
returned `embedded` vec carries exactly the caps that landed.

### The compulsion gate

`commit_turn_gated` (`shared_fork.rs:413-537`) is the single mandatory entry — the
guest drives turns through it, never `fork.commit_turn` directly. It classifies a
turn over the SAME `touched_cells` the live commit path uses:
- touches no boundary → commits locally, no consent door;
- touches a boundary with no consent → `GatedCommit::Refused` carrying the
  `ConsentRequest`; the turn does NOT run;
- touches a boundary with a valid `ConsentWitness` → the gate opens, a REAL
  attenuated `Powerbox::grant` of the boundary cap lands on the fork (its own two
  gates fire, so consent can never mint wider than the owner holds), the consented
  turn commits, and the boundary's nullifier is recorded — it fires exactly once.

`verify_consent_witness` (`shared_fork.rs:633-694`) applies three teeth: (a)
turn-hash binding to the bound grant; (b) the one-shot proof nullifier over
`compute_proof_hash` (checked before signature, so a replay is rejected
regardless); (c) executor-signature authenticity under a trusted key in the
executor's own signing domain (`canonical_executor_signed_message`, the v3
domain). `resolve_consent` (`shared_fork.rs:573`) lets the owner mint the witness
by running a real powerbox grant over the LIVE world — the documented "closed
finding" is that a real World-grant receipt is signed in the v3 domain, not the
bare `receipt_hash` the generic `resolve_condition` `TurnExecuted` arm checks, so
this resolver verifies in the executor's own domain (`shared_fork.rs:553-565`).

### The real membrane — `MembraneFrustum`

`MembraneFrustum` (`shared_fork.rs:729-742`) is a serializable, travel-able
cap-bounded `Cell` subgraph — genuine `dregg_cell::Cell`s, the SAME postcard codec
the image root commits over, not a synthetic table (`shared_fork.rs:696-728`).
- `mint` (`shared_fork.rs:754-786`) BFS's capability edges from the focus (the
  guest) to `max_depth`, snapshotting exactly the in-view subgraph — the embedded
  targets are reachable, the boundary targets are not (confinement by omission).
- `frustum_root` (`shared_fork.rs:793-807`) is a domain-separated blake3
  commitment over the sorted culled cells — the anti-substitution tooth.
- `rehydrate` (`shared_fork.rs:832-858`) installs exactly the culled cells into a
  fresh signing-keyed `World`, fail-closed on a root mismatch BEFORE a single cell
  is trusted, and re-mints to confirm the install was faithful. The recipient
  drives real turns on it through the SAME verified executor; the fork holds no cap
  to mainline until stitched.
- `driven_graphs` (`shared_fork.rs:872-931`) reads back the ACTUAL diverged cells
  as `branch_stitch` atoms so the stitch folds the real mutation, with the
  settlement gate governing whether a conferred cap is admitted or lossy-dropped.

`MembraneError` (`shared_fork.rs:939-952`) enumerates the fail-closed paths
(`MalformedSnapshot`, `RootMismatch`, `NoSuchFork`, `MalformedTurn`,
`DriveRefused`).

---

## `distributed_card` — two principals, one card, different instances

`distributed_card.rs` joins the local card stitch (`deos_js::coauthored_card`, a
`dregg_doc` pushout) with the membrane carry, so two principals on DIFFERENT
instances co-drive ONE shared card (`distributed_card.rs:1-40`).

`CardForkEnvelope` (`distributed_card.rs:57-72`) makes a non-serializable
`CardFork` portable by carrying exactly the strings the stitch consumes: the
shared seed `view_source`, this principal's driven `view_source`, its blame author
(`who`), and the `edit_authority`. `fork_root` (`distributed_card.rs:93-106`) is a
domain-separated blake3 commitment over those fields — the anti-substitution tooth,
mirroring `MembraneFrustum::frustum_root`.

The full distributed loop (`distributed_card.rs:30-34`):
- `seal_fork` (`:133-141`) — A drives its fork, freezes the driven view into
  envelope bytes + the claimed root.
- `open_envelope` (`:150-159`) — B fires the anti-substitution root tooth
  (`RootMismatch` fail-closed on a tampered/substituted envelope).
- `rehydrate_fork` (`:176-194`) — B rebuilds the shared card from the CARRIED seed
  and takes its own live `CardFork`, bounded by B's `held` (the cap tooth lives in
  deos-js's `CardEditor` — an unauthorized B may take the fork but every edit is
  refused in-band, contributing no patch).
- `stitch_with_fork` / `stitch_envelopes` (`:206-239`) — the `dregg_doc` pushout:
  disjoint edits fold clean (both kept), an overlap surfaces a first-class
  `dregg_doc::ConflictRegion` (both attributed alternatives live, never silent
  last-writer-wins).

`DistributedCardError` (`distributed_card.rs:244-257`) carries `MalformedEnvelope`
/ `RootMismatch` / `Unauthorized`. The four fail-closed teeth (clean merge,
conflict region, the cap tooth, anti-substitution) are tested at
`distributed_card.rs:316-513`.

---

## `deos_desktop` — the NT/Pharo workbench (gpui)

`DeosDesktop` (`deos_desktop.rs:287-303`, gated on `gpui-ui` + `embedded-executor`)
is a Windows-NT / Pharo-Smalltalk workbench over the live verified `World`, built
beside the cockpit (`deos_desktop.rs:1-30`). Icons ARE cells read off the live
ledger; right-click context menus are the actuation; drag-to-compose acts across
two cells.

Every fired action commits a REAL `dregg_turn` through
`World::commit_turn` (`deos_desktop.rs:543`, `:558-560`, `:578-580`): a
context-menu transfer fires `transfer(cell, user, amount)`, a grant fires
`grant_capability(...)`, and compose drops one icon on another to
transfer/grant across them (`deos_desktop.rs:608-628`). The status bar shows the
receipt height — the user sees their "do it" landed a real verified turn.

Spatial persistence is real state: `DesktopLayout` (`deos_desktop.rs:118-122`) holds
`IconPos` + `WinGeom` (`:94-111`), serialized to a sidecar JSON
(`DesktopLayout::default_path`, `:127`) on every drag/move/resize and reloaded on
open — windows the layout remembers are re-opened at boot (`deos_desktop.rs:337-344`).

---

## `login` / `session` — login = receiving your root capability

The model: **login = receiving your root capability · a session = the cap-tree you
hold · logout = revoking it** (`session.rs:11-18`). A session is not an object kept
in sync with the ledger — it IS a c-list (`session.rs:16-18`).

`session.rs` is the gpui-free, `cargo test`-able ceremony; `login.rs` is the gpui
surface that boots first (deos boots into the login picker, not the cockpit) and
paints the click → ceremony → root-swap (`login.rs:1-22`).

The ceremony (`session.rs:20-36`), each step a real receipted turn:
1. **AUTHENTICATE** — `LoginManager::authenticate` proves possession of the
   principal's key (`session.rs:381-387`); a `Challenge` carries the
   signed-challenge variant (`session.rs:268-320`).
2. **DERIVE** the root cell — `Principal::root_cell()` is
   `CellId::derive_raw(&pubkey, &ROOT_TOKEN)`, the content-address of the key
   (`session.rs:95`, `:24-28`).
3. **GRANT** — `LoginManager::login` (`session.rs:399-478`) mints the root cell on
   first login (a confined genesis cell, empty c-list) then grants each
   `CapTemplate` entry FROM the system principal via a real
   `Effect::GrantCapability` turn. The executor is the authority: an entry the
   system principal cannot legitimately confer makes the login
   `LoginOutcome::Denied` — never partially granted.
4. The **session** = the resulting root-cell c-list (`Session`, `session.rs:170-191`).
5. **LOGOUT** — `LoginManager::logout` (`session.rs:488-505`) revokes each granted
   slot via `Effect::RevokeCapability`; at `n = 1` this is synchronous + transitive
   (`sel4/dregg-firmament/src/surface.rs:407`), so the whole cap-tree darkens the
   instant the revoke returns.

Sessions are durable: login writes a `SessionRecord` (principal + granted c-list
snapshot) into the per-user image's redb store so a relaunch restores the session
without re-running the grant ceremony; logout overwrites it with a revoked marker,
so a revoked session does not silently resume (`session.rs:508-525`).

---

## The cockpit (gpui)

`starbridge-v2/src/cockpit/` (gated on `gpui-ui`/`gpui-web`) is the visual master
interface — the dock + surfaces rendering the embedded `World` across four axes
(cell-world, inspector, blocklace/provenance, composer, dynamics, image/federation)
(`cockpit/mod.rs:1-22`). gpui is single-threaded; the `World` is shared as
`Rc<RefCell<World>>` and every verb button mutates it through `World::commit_turn`
(the REAL executor), re-rendering from the post-state next frame. The cockpit is
itself ONE privileged `Console` surface in the shell (`surface.rs:130-141`).
