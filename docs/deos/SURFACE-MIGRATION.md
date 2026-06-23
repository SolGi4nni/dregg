# SURFACE MIGRATION

Robigalia's networked seL4 carries a process across machines. deos generalizes
that into one operation: **relocate a surface along the firmament distance axis,
with its capability identity preserved.** A surface is a capability; "where it
runs" is a point on that axis; migration moves the cap from one point to another
without changing what it is or the cell behind it.

This document grounds the full migration story — Local ↔ Surface ↔ HostPd ↔
Distributed — in the primitives that already exist, and states honestly what is
built versus what is wiring. The first concrete migration (Local→Surface, the
multi-window tear-off) ships with this doc.

## 1. The primitives migration relocates

### A surface IS a capability

A surface is not a window with a cap attached; it is a cap whose rendered face is
a window. The authority over a surface is the REAL `dregg_firmament` capability
the shell mints when it opens the surface:

- `starbridge-v2/src/shell.rs:299` `Shell::open_surface` seeds a fresh backing
  surface-cell + owner holder in the firmament fabric, installs the owner's full
  grant, and mints `SurfaceCapability::new(id, Capability::surface(backing_cell,
  full))` — the ONLY authority over the new surface.
- `starbridge-v2/src/shell.rs:772` `Shell::authorize` is the ocap heart: every
  window op (focus/move/resize/share/present) resolves the presented cap through
  `SurfaceBacking::invoke` — the genuine `granted ⊆ held`
  (`dregg_firmament::is_attenuation`) gate. There is NO bearer-secret; naming the
  `SurfaceId` is not enough (`shell.rs:1025` `a_forged_capability_is_refused_every_op`).
- A window-SHARE is a GENUINE `Effect::GrantCapability` turn:
  `sel4/dregg-firmament/src/surface.rs:169` `SurfaceBacking::delegate` runs the
  real executor, so a WIDENING share is REJECTED (`shell.rs:470` `Shell::share`,
  the `DelegationDenied` surfaced as `ShareDenied`).

The consequence the migration leans on: **to move a surface is to move a cap.**
Everything migration must respect — gating, attenuation, conservation — is already
the law of caps.

### "Where it runs" is the firmament DISTANCE AXIS

`sel4/dregg-firmament/src/lib.rs:229` `Target` is the distance parameter made into
a type. The SAME `(target, rights)` handle resolves to a different backing
depending on where the resource sits:

- `Target::Local { slot }` (`lib.rs:232`) — an seL4 CNode slot; invocation is a
  syscall, attenuation is `seL4_CNode_Mint`, revoke is synchronous.
- `Target::Surface { cell }` (`lib.rs:253`) — a dregg cell rendered as a window;
  invocation is a present/draw turn, the same `granted ⊆ held` gate as a
  distributed cell.
- `Target::HostPd { pd }` (`lib.rs:266`) — a forked, OS-sandboxed child PD whose
  only channel is its firmament Endpoint; invocation is a validated round-trip on
  that control socket (`sel4/dregg-firmament/src/host_pd.rs:99`
  `HostPdBacking::invoke`).
- `Target::Distributed { cell }` (`lib.rs:241`) — a (possibly remote) dregg cell;
  invocation is a real executor turn, attenuation is `recKDelegateAtten`.

The app holds a `Capability`; it does NOT name a backing — `Capability::attenuate`
(`lib.rs:376`) gates on the real `is_attenuation` regardless of where the target
lives, and the router dispatches. **Migration is changing the `Target` of a
surface cap while keeping its rights and the cell it points at.** The four
targets are the four migration destinations.

### Network handoff: CapTP sturdyrefs + three-party handoff

When the destination is another vat over the network, the cap travels by the
existing CapTP machinery:

- `captp/src/sturdy.rs` — the swiss-number table (`SwissTable`): a surface cell is
  EXPORTED to a 32-byte swiss number (`sturdy.rs:140` `export`); presenting it to
  the target federation enlivens a live reference.
- `captp/src/handoff.rs` — the three-party handoff: the introducer signs "I
  authorize <recipient> to reach <swiss>", the recipient presents it, the target
  validates. Two invariants matter for migration and are already enforced:
  `HandoffError::Amplifies` (`handoff.rs`, the `granted ≤ held`
  `handoff_non_amplifying` spec) and `HandoffError::TargetMismatch` (the
  `handoff_same_target` spec — a handoff re-shares the SAME cell, it cannot
  redirect a swiss entry to a different one). Replay is refused by the handoff
  nonce table (`sturdy.rs:121` `handoff_nonce_seen` / `register_handoff_nonce`).

### The membrane carries live state

The cap is the authority; the live WORLD-STATE the surface renders travels as a
portable snapshot — `starbridge-v2/src/shared_fork.rs` (the shared confined fork
with graduated consent: an EMBEDDED tier granting a real `CapabilityRef`, a
STUDYREF read-only tier, a NETWORKBOUNDARY tier whose exercise elaborates
elsewhere). A migrated surface that needs its rendered content on the far side
ships a membrane fork; the cap and the membrane are distinct objects (authority
vs content), exactly as a surface and its cap are distinct.

### The n=1 collapse

At one machine the distributed bounds collapse to strong-local
(`sel4/dregg-firmament/src/lib.rs:35`, `Bounds::distributed(1) == Bounds::LOCAL`,
`lib.rs:510` `n_equals_one_collapse`): immediate revocation, synchronous commit,
consistent checkpoint. So a Local↔Surface↔HostPd migration on one box is
instantaneous and consistent — the migrated surface reflects the same live world
the moment the move returns. Only a →Distributed migration to a genuinely remote
vat (`n>1`) relaxes those bounds.

## 2. The three concrete migrations

### (a) Tear-off to an OS window — Local→Surface — **BUILT (this slice)**

Relocate the active surface from "composited inside the cockpit's one window" to
"its own OS window." gpui hosts multiple windows (`App::open_window`); the
tear-off:

- `starbridge-v2/src/dock/tearoff.rs` — `WindowRegistry` (the record of which
  surfaces are torn off, keyed by the stable `SurfaceId` the dock pane used — the
  identity the migration preserves) + `TornOffWindow` (the new window's root view,
  which re-renders the surface's body by re-entering the host through a stored
  callback).
- The render callback is the identity-preserving seam: it re-enters the cockpit
  (weak handle) and dispatches the SAME `Cockpit::panel_for_tab(tab)` the in-dock
  `TabSurface` calls (`starbridge-v2/src/cockpit/panels_workspace.rs`,
  `tear_off_tab`). So the torn-off window paints the LIVE surface over the SAME
  cell — never a snapshot copy. Pop-back (`WindowRegistry::pop_back`) closes the
  window; the dock pane was never removed (a non-destructive mirror), so the
  surface keeps its identity and its in-dock seat throughout.
- On-demand + windowed-only: the ⌘K commands `TearOffActiveSurface` /
  `PopBackActiveSurface` (`starbridge-v2/src/palette.rs`) and the pane tab-bar
  "↗ pop out" control fire it; the headless bake never opens a second window.

Identity is preserved structurally: the surface keeps its `SurfaceId`, its
`SurfaceCapability`, and its backing cell. The torn-off window is a second
`Target::Surface` face of the same cap — the firmament distance axis with two
window points at `n=1`.

### (b) Migrate a pane's processing to a HostPd — Local→HostPd — **DESIGN (wiring)**

Move a surface's *processing* (not just its glass) into a confined, OS-sandboxed
child PD whose only channel is its firmament Endpoint. What exists:

- `Target::HostPd` + `HostPdBacking` (`host_pd.rs`) already resolve a cap to a
  confined child over its control socket, with attenuation on the same
  `granted ⊆ held` gate (`host_pd.rs:99` `invoke`), bounds strong-local at `n=1`,
  and the held Endpoint load-bearing (drop it and the cap is gone).
- The compositor-PD already routes `present()`/`route_input()` over an Endpoint
  with the T1/T2/T3 verified-scene teeth (`sel4/dregg-firmament/src/compositor_pd.rs`,
  mirrored by `starbridge-v2/src/shell.rs:699` `Shell::present` /
  `shell.rs:745` `route_input`).
- `process_kernel` + `sandbox` (`--features process-pd[-sandbox]`) fork the child,
  enforce MMU isolation, and confine ambient OS authority.

The wiring needed: a `migrate(surface_cap, Target::HostPd(pd))` that (1) spawns or
selects the child PD, (2) re-homes the surface's backing so its `present`/
`route_input` round-trip over that PD's Endpoint instead of the in-process
compositor, and (3) re-mints the surface cap with `Target::HostPd` while preserving
the rights and the backing cell. The cap operation is a delegate turn (the child
gets exactly the delegated rights); the transport changes from in-process call to
Endpoint round-trip. The honest distance: the firmament has every PIECE (the
target, the backing, the Endpoint present/route, the sandbox); no single
`migrate` verb ties them into a surface re-home yet.

### (c) Hand a surface to another vat over the network — →Distributed — **DESIGN (wiring)**

Give a surface to a remote vat so it renders/drives it there. What exists:

- CapTP export + three-party handoff (`sturdy.rs` / `handoff.rs`) already carry a
  cell reference to a third party with the non-amplification and same-target
  invariants enforced (§1).
- The membrane (`shared_fork.rs`) already travels as a portable, cap-bounded
  world-snapshot with graduated consent tiers.
- `Target::Distributed` already resolves a cap to a remote executor turn with the
  `n>1` relaxed bounds (`lib.rs:241`).

The wiring needed: a `migrate(surface_cap, Target::Distributed(remote))` that (1)
exports the surface's backing cell to a swiss number, (2) performs the three-party
handoff of the SURFACE cap to the recipient vat (the introducer = the current
holder; the cert carries the attenuated rights), (3) ships a membrane fork for the
live rendered content, and (4) the recipient enlivens the swiss ref into a live
`Target::Surface` on its side. The handoff's `granted ≤ held` and `same_target`
invariants give exactly the migration soundness §3 wants — for free, because a
network surface handoff IS a CapTP handoff. The honest distance: the handoff
moves a cell reference today; threading the SURFACE cap (the `Target::Surface`
wrapper + the membrane content) through it, and enlivening it back into a live
compositor surface on the recipient, is the unbuilt seam.

## 3. Soundness

Migration is a cap operation, so it inherits the cap discipline whole — it does
not add a new trust surface, it reuses the one that already holds.

- **You cannot migrate authority you don't hold.** A tear-off / HostPd-move /
  network-handoff begins by authorizing the presented surface cap through
  `Shell::authorize` (the `granted ⊆ held` gate). You can only relocate a surface
  you actually hold — the same check every window op runs.
- **The receiving end gets exactly the delegated rights.** A migration that
  narrows (hand a read-only mirror to a remote vat) is a genuine
  `Effect::GrantCapability` / CapTP handoff at the narrowed rights; a WIDENING
  migration is REJECTED by the real executor (`ShareDenied` /
  `HandoffError::Amplifies`). Migration cannot amplify authority — the
  no-amplification law fires identically at the desktop, the host-PD Endpoint, and
  the network handoff, because all three gate on the SAME `is_attenuation`.
- **A migration cannot redirect the cap to a different cell.** The handoff
  `same_target` invariant (`handoff.rs`, `handoff_same_target`) means a migrated
  surface still points at the SAME backing cell — identity is preserved by the
  same rule that stops a swiss entry being redirected.
- **Settlement Soundness applies to a migrated turn.** A turn exercised on a
  migrated surface (a present/draw on the far side) is authority-live-at-settlement
  exactly as a local one: the light client's "verifyBatch accept ⟹ ∃ genuine
  kernel transition" extends across the move because the move did not change the
  cap's authority, only its transport. At `n=1` the bounds are strong-local
  (immediate/consistent); at `n>1` the relaxed distributed bounds are the only
  difference, and they are the honest, named cost of distance — never a hole.

The through-line: a surface is a proof-carrying token over an owned cell;
migration exercises that token to relocate the token itself, leaving the cell, its
caps, and its history untouched and a verifiable receipt behind. "Where it runs"
became a value you can attenuate.
