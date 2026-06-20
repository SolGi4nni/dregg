# CROSS-DEVICE-FIRMAMENT — your sovereign image across phone, laptop, and cloud

*Design frontier doc. Present-tense where the machinery is real (the firmament
distance parameter, the blocklace, attested roots, cell migration, the in-browser
light client, the persistence spine all ship today); clearly-scoped frontier where
it isn't (the mobile client app, Willow, seL4-on-a-phone). First-principles, no
trajectory narrative. This is the **device-distance** instance of the firmament:
where `docs/FIRMAMENT.md` and `sel4/dregg-firmament/src/lib.rs` parametrize
distance by an integer `n` abstractly, this doc makes `n` concrete as the number
of **your own devices** a cell spans. Companion to
`docs/DISTRIBUTED-SERVO.md` (the federation/render-distance face this reuses
wholesale), `docs/deos/{DISTRIBUTED-TIMETRAVEL-SEMANTICS,BRANCH-AND-STITCH-PROTOCOL,
WORLD-PERSISTENCE-PLAN}.md` (the branch/merge/persistence machinery cross-device
sync IS), and `project-firmament-sel4-boots` (the one-cap-across-distance thesis).*

---

## 0. The one-paragraph thesis

deos is ember's **daily-driver sovereign OS**, and a daily OS lives across
*devices* — the phone in a pocket, the laptop on the desk, the always-on node in
the cloud. The firmament already says an seL4 kernel capability and a dregg
federation capability are the **same abstraction at different points on a distance
parameter `n`** (`sel4/dregg-firmament/src/lib.rs:35-47`, the `Bounds {
revocation_immediate, commit_synchronous, n }` triple at `lib.rs:310-322`). This
doc reads `n` as **device-distance**: `n = 1` when a cell is being touched on the
one device that holds it (strong-local — immediate revoke, synchronous commit,
consistent checkpoint, `Bounds::LOCAL` at `lib.rs:327`); `n > 1` when the same
cell is replicated and concurrently reachable across your devices (the bounds
relax — eventual revoke, quorum/merge commit, `Bounds::distributed(n)` at
`lib.rs:335`). The headline consequence: **a window, a cell, and a capability are
the same object whether it lives on your phone or your laptop, and moving it
between them is not a new subsystem — it is the cell migration, the blocklace
merge, and the branch-and-stitch protocol the federation already runs, with your
two devices as the two parties.** Nothing here invents a sync protocol or a second
authority model; it *relabels the distance parameter from "machines in a
federation" to "my own machines" and walks the same `Bounds`.*

### The one model, four kinds of device-distance

| kind | what spans devices | the firmament walk | shipped substrate |
|---|---|---|---|
| **the held cell** (§1) | a domain/UI cell replicated phone↔laptop↔cloud | `Distributed{cell}` reachable from each device; `n` = how many of *my* devices hold it | `node`/blocklace replication, `AttestedRoot` |
| **sync / reconcile** (§2) | the two devices' divergent histories rejoin | the blocklace DAG merge + Willow range-reconcile + I-confluent union | `blocklace/`, `merkle_root_of_receipt_hashes`, rhizomatic |
| **handoff** (§2.3) | a live session/surface moves laptop→phone | the surface **cell migrates**, carrying its `state_root`; receipt-chain continuity | `cell/tests/integration_migration.rs`, `CellLifecycle::Migrated` |
| **offline-then-stitch** (§2.4) | a device works offline, rejoins, merges | the **branch-and-stitch** protocol: offline = a branch; reconnect = a gated `Stitch` | `BRANCH-AND-STITCH-PROTOCOL.md`, conservation/nullifiers |

The unifying sentence: **`Local{slot}` on one device → `Distributed{cell}` across
your devices → handing a `Surface{cell}` from laptop to phone — each is one more
point on `n`, reached by relaxing `Bounds`, with the capability semantics held
fixed.**

---

## 1. THE MODEL — your sovereign image as cells that live across your devices

### 1.1 The image is a cell graph, not a disk

deos's state is not a filesystem image; it is a **graph of sovereign cells** — the
`World` the desktop embeds (`starbridge-v2/src/world.rs:71-123`: the engine
ledger, the receipts provenance log, the dynamics stream, the replayable
`History`). Each cell is content-addressed (`CellId`), conserves value
(BALANCE_SUM = 0 across the four substances), and carries its own receipt chain.
"Your image across devices" therefore means: **the same cell graph, reachable and
mutable from more than one device**, with each device holding caps into it.

### 1.2 `n` is device-distance; the bounds relax exactly as on the federation

The firmament `Bounds` are agnostic about *what* the machines are — federation
peers or your own devices. So device-distance is the federation distance with the
peer set narrowed to *yours*:

- **`n = 1` — one device, strong-local.** A cell only your laptop holds, touched
  on your laptop, is `Bounds::LOCAL` (`lib.rs:327-331`): a revoke is dead the
  instant the call returns, a commit is final the moment it commits, the
  checkpoint is consistent. This is ember's single-machine principle as code
  (`project-dregg4-vision`): on one box, the distributed bounds *collapse* to the
  strong-local ones. The desktop you run today is this case — `World::commit_turn`
  (`world.rs:585`) is a synchronous local transaction.

- **`n > 1` — the cell spans your devices, bounds relax.** The same cell,
  replicated to your phone and cloud node, is `Bounds::distributed(n)`
  (`lib.rs:335-347`): a revoke must *propagate* (eventual), a commit is
  *quorum/merge-gated* (the devices must agree it is final), the checkpoint is
  per-device-consistent-then-reconciled. **The verbs are unchanged** — you still
  `attenuate` (`lib.rs:293`, the genuine `is_attenuation` gate), still `delegate`,
  still `revoke` — only the bounds the `Resolution` reports (`lib.rs:355-364`)
  differ. The app cannot tell which device resolved it (`Backing` is informational,
  `lib.rs:368-374`); that is the whole point.

### 1.3 A cap spans phone↔laptop↔cloud the same way a window does

A deos window **is** a `Capability{ target: Surface{cell}, rights }`
(`lib.rs:198-210`, `surface()` at `lib.rs:278`) — holding/attenuating/delegating/
revoking the window is exactly doing so to the backing cell, through the same
`granted ⊆ held` gate and the same executor. Cross-device, this is the lever: **a
window open on your laptop is a cap into a cell; that same cap, exported to your
phone, opens the same window there.** No "window protocol" — the surface rides the
generic backing-agnostic machinery (`lib.rs:272-283`), and the export across
devices is the same sturdy-ref / handoff path the federation uses
(`DISTRIBUTED-SERVO.md §1.1`, `captp/src/sturdy.rs::SwissTable::export_with_options`
minting an attenuated, `max_uses`/`expires_at`-bounded facet). Your phone holding a
read-only display facet and your laptop holding the actuating cap is just two
attenuations of one cap — §4.2's thin-client split (`DISTRIBUTED-SERVO.md:865`).

---

## 2. SYNC / HANDOFF — cross-device sync IS the distributed merge

This is the load-bearing claim of the whole doc: **there is no "device sync"
subsystem to build, because syncing your devices is the distributed merge the
federation already runs.** The four pieces below are all *existing* machinery with
your two devices substituted for two federation peers.

### 2.1 The substrate — the blocklace DAG + attested roots (shipped)

Cross-device state replication is the **blocklace** (`blocklace/src/lib.rs`): a
content-addressed DAG of signed blocks, each carrying `creator` (the device's
key), a monotone `sequence`, `predecessors` (the causal dependencies), and a
`payload` (the turn receipt). Two devices reconcile their DAGs by **Cordial
Dissemination** (`blocklace/src/dissemination.rs`: `Push`/`Pull`/`PullResponse`/
`HaveFrontier`, `Subscription` strand-filtering, `PeerKnowledge` tracking what the
other device already has). Each device commits the other's finalized turns into its
own blocklace as signed blocks (`node/src/blocklace_sync.rs`), and the join is
proven sound: the receipt set folds to a canonical `merkle_root_of_receipt_hashes`
(`types/src/lib.rs:357`, balanced domain-separated BLAKE3) bound into a
quorum-signed `AttestedRoot` (`types/src/lib.rs:281-335`, carrying
`receipt_stream_root` + `blocklace_block_id` + `finality_round`). **Every state a
device receives from another carries its own proof** (the §1.2.1 self-verifying
envelope of `DISTRIBUTED-SERVO.md`) — so a device trusts the *content*, never the
*peer*. Your phone pulling state from your laptop, or from a relay, or from a CDN
mirror, all verify identically; this is the light-client unfoolability the protocol
already proves (`AssuranceCase.lean::unfoolability_guarantee`).

### 2.2 Reconciliation — Willow range-reconcile + the I-confluent fragment

When two of your devices have diverged (different turns committed offline), they
reconcile efficiently rather than by re-shipping everything:

- **Willow range-reconciliation** (`DISTRIBUTED-SERVO.md §1.4`, lines 262-294):
  two devices exchange `fingerprint(range)` over the receipt-stream Merkle tree;
  equal → done, unequal → split and recurse — `O(diff·log)` not `O(state)`.
  Willow's `(namespace, subspace, path)` maps onto `(my-device-set, cell, receipt-
  stream-range)`. **Honest scope:** there is *no Willow code today* (zero
  `willow`/`range_reconcil` in the tree); what ships is the substrate that makes it
  a bounded build — the canonical-ordered receipt tree, the self-verifying
  envelope, and the `Netlayer`+`relay` transport. The work is the range-fingerprint
  protocol as a new `pipeline` conversation.

- **The I-confluent / rhizomatic fragment merges by pure union.** The subset of
  state that is *monotone* (grows-only, conflict-free — `~/dev/rhizomatic`'s
  content-free `Delta` set-union, `project-rhizomatic-dregg-slotting`) reconciles
  with **no consensus at all**: two devices' deltas combine by set union
  (`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md §3.8`, "the monotone merge sub-algebra").
  This is most read/query/annotation/document state — it just merges. Confluence is
  *invariant-relative* (`Confluence.lean`): `balance ≥ 0` is **not** I-confluent
  (two offline withdrawals can merge to negative), so value-moving turns escalate to
  consensus/settlement; monotone increments do not.

### 2.3 Handoff — move a live surface laptop→phone (cell migration, shipped)

Handing a live session from one device to another is **migrating the surface's
backing cell** — the existing `cell/tests/integration_migration.rs` path and the
`CellLifecycle::Migrated` lifecycle the shell renders as a badge
(`DISTRIBUTED-SERVO.md §2.4` lines 448-489, §4.3 lines 904-958). Because a window
*is* a cell:

- `migrate(surface_cell, laptop → phone)` is an `Effect::GrantCapability`-shaped
  turn (`DISTRIBUTED-SERVO.md:915`): the laptop delegates the surface cap to the
  phone and revokes its own — a **receipted** turn (provable who-handed-what), and
  the receipt chain commits `(surface CellId, state_root_before @ laptop,
  state_root_after @ phone)` so **continuity is a theorem about the receipt chain**,
  not a hope (`DISTRIBUTED-SERVO.md:923`). The `state_root` is monotone across the
  handoff; a phone display-cap or input-grant **survives** migration because they
  point at the `CellId` (`:931`).
- **Honest scope (named seam, `DISTRIBUTED-SERVO.md:473-489`):** today's handoff is
  **suspend-checkpoint-resume**, not live-VM teleport. What migrates is the
  *resumable description* (URL, storage-partition cell, the macaroon, the committed
  `state_root`) — enough to *reopen* the surface equivalently on the phone. What
  does *not* migrate is live in-renderer state (a half-loaded page, a JS heap),
  which is not in the committed root. The lever for true live handoff is the
  Servo-on-seL4 PD address-space migration (`EMBEDDED-WEB-SURFACE.md §5`) — gated on
  the same Servo-on-seL4 blocker, a named artifact, not research. **Atomicity of
  migrate-then-revoke across two devices** is a 2-phase commit over the surface cell
  (the `coord/src/atomic.rs::Coordinator`, `DISTRIBUTED-SERVO.md:949`); a device
  crashing mid-handoff is bounded by the coordinator's abort/timeout.

### 2.4 Offline-then-reconcile IS branch-and-stitch

A device working **offline and rejoining** is *exactly* the branch-and-stitch
protocol (`BRANCH-AND-STITCH-PROTOCOL.md`), with "offline" as the branch:

- **Going offline = opening a branch.** A device that loses the network and keeps
  working is a `Virtual/Branch` world off the last shared `WitnessCursor`. It is
  honestly typed (`Rehydration = Virtual/Branch`, never `Main/Live`, by
  construction) — the cell cannot lie about being a not-yet-reconciled fork. Its
  side-effects are *structurally imaginary* w.r.t. the shared image until it stitches
  (firmament confinement: the offline branch holds no cap to settled-main state it
  has not seen).
- **Reconnecting = the gated `Stitch`.** On reconnect, the device authors a
  reconciliation that merges its offline work into the shared image through *one
  door* — the **Settlement Soundness gate** (`BRANCH-AND-STITCH-PROTOCOL.md §3`):
  conserves (no value conjured offline), current-authority (against the *settled
  tip's* revocation set, not the device's stale offline authority), no-conflict (an
  offline spend of value the other device already spent = a **nullifier collision =
  rejected**). **The conflict boundary is the conservation/nullifier boundary** —
  exactly the double-spend non-membership the circuit already enforces.
- **The merge is two-regime, automatically.** The I-confluent parts (§2.2,
  monotone) merge cleanly with no user involvement; only the genuinely-conflicting
  parts (two devices both spent the same coin, both edited the same field
  destructively) surface for explicit resolution, with **linear-logic forcing an
  explicit drop** (you cannot silently lose data; lossy is deliberate, typed loss).
  "Spaceage = semi-automated": auto-merge the confluent, surface only the real
  conflicts.

So **offline-edit-on-the-train then rejoin-at-home is the branch-and-stitch demo**,
and conflict resolution UX is the stitch's "surface the genuine conflicts" UX —
the same one the distributed-time-travel work designs.

---

## 3. THE MOBILE SUBSTRATE — reality, not aspiration

### 3.1 seL4-on-aarch64 — boots in QEMU, far from a real phone

The phone substrate *is* seL4 on ARM, and it **boots today in QEMU-aarch64**: the
boot ladder (`sel4/README.md`) runs M0 (a Rust PD prints on aarch64), M1 (the
verifier PD), M2 (the rbg `DirectoryCell` PD), and **M-STARK** (a real
BabyBear+BLAKE3+FRI STARK proved + verified *on-device*, anti-ghost teeth, no Lean)
— all aarch64, plus M5 on riscv64. The GPU path is a virtio-gpu driver-PD (clone
the booting net-PD, swap virtio-net→virtio-gpu; `sel4/gpu-driver-vm/README.md`,
`docs/desktop-os-research/EXPLORATIONS.md`), today bootable as a Linux-guest-under-
VMM on QEMU-aarch64 but **"not turnkey on macOS-QEMU" (no host Vulkan)** and with
real-GPU accel deferred to real hardware.

**Honest verdict: seL4-on-a-real-phone is far.** There is *zero* in-tree real-ARM-
hardware work. A real device needs seL4 board support for the SoC (some boards are
upstream-supported — Pi, certain dev boards), device-tree/MMIO for the phone's
GPU/display, verified bootloader/firmware porting. This is "port your board to
seL4" infrastructure (the seL4 Foundation agenda), **not a dregg protocol blocker**
— QEMU is sufficient for development. But it is **years, not months**, for deos to
*natively* run on a phone.

### 3.2 The cross-platform UI faces — gpui-native vs the web/wasm face

deos has two UI faces, and only one crosses to mobile near-term:

- **gpui-native (the desktop master interface).** `starbridge-v2` is the native
  shell embedding the verified executor (`world.rs`), built on gpui (Metal on
  macOS / Vulkan on Linux). The gpui-offscreen render path is **proven** — it
  reaches the seL4 framebuffer (`project-deos-desktop-frontier`, the #1 precious
  closed; `docs/desktop-os-research/SEL4-INTERACTIVE-COCKPIT.md`). But gpui is
  *native-only*: it does **not** run on wasm or mobile browsers, and its heavy
  native dep tree is why `starbridge-v2` is a separate workspace. **gpui is not the
  mobile face.**

- **The web/wasm face (the cross-platform one).** This is real and runs in a
  browser today: the `wasm/` crate ships an **in-browser light client**
  (`wasm/src/bindings_lightclient.rs::verify_history` — folds a finalized history
  into a recursive aggregate proof), **transclusion** verification
  (`bindings_transclusion.rs`), and the **web-surface** resolve/render path
  (`bindings_surface.rs`). `site/` serves the playground + studio (the v1 IDE/
  inspector, static-built). `deos-leptos/` is an *exploratory* Leptos-runtime probe
  (signals ↔ the Reactive rung; hydration ↔ frustum-rehydration), and
  `deos-web-cells/` publishes web bundles as content-addressed `dregg://` cells.
  **The light client and the surface fetch are wasm-real and would run in a mobile
  browser; a full interactive deos OS UI on the web is the aspirational frontier
  (deos-leptos is a probe, not a shipped UI engine).**

### 3.3 The realistic near-term mobile story — a thin web client to the home image

The mobile story that is **buildable in months, not years** is the **thin client**
(`DISTRIBUTED-SERVO.md §4.2`, lines 865-902): the phone holds **strictly a
display-cap** (read-only) to a surface rendered on your **home node** (laptop or
cloud), plus an *optional, separately-attenuable* input-grant-cap. The compute,
the macaroons, the fetches stay home; the phone scans out attested frames (each
frame Ed25519-attested to the cell's committed root, `net-client/src/turn_gate.rs::
verify_strict`) and sends **attested input** (signed gestures the home executor
requires). A revoke darkens the phone in one round-trip; a borrowed/café phone gets
the display-cap and *not* the input-grant — it can watch, not act. This is the
cap-secure realization of "your phone is a window into your home image."

**Status:** the *protocol and capability model exist in the code*
(`is_attenuation`, `AuthRequired`, frame attestation, the display/input cap split);
what's missing is the **mobile client app** that speaks it — a phone client that
dials the home node (CapTP relay or REST/SSE), holds a display-cap, renders frame
attestations, and signs input. That is ~1–2k lines for a proof-of-concept; the hard
part is distribution and polish, not the protocol. Until then, the **mobile-browser
light client** (wasm, real today) is the immediately-shippable face: a phone browser
can already *verify* a `dregg://` cell is unforged.

---

## 4. THE DESIGN + the first buildable milestone

### 4.1 The shape

Three devices, one image: a **home node** (always-on, the render/compute authority
— laptop or cloud), a **phone** (thin display + attested input near-term; a full
peer long-term), and the **laptop** (a full peer that holds caps and can go
offline). The image is the shared cell graph; each device holds caps into it; they
stay converged by the blocklace merge (§2.1) + Willow reconcile (§2.2); a device
that goes offline branches and stitches on reconnect (§2.4); a live surface hands
off by cell migration (§2.3); a phone watches via a display-cap (§3.3). **`n` is
how many of your devices currently hold the cell live; the bounds relax as it
rises, the verbs never change.**

### 4.2 The first milestone — two devices, one image, offline-branch-then-stitch

The smallest end-to-end thing that proves the model and is buildable on shipped
substrate:

1. **Persist the image** (the prerequisite, already planned). Wire
   `dregg-persist`'s redb commit log into the `World` per
   `WORLD-PERSISTENCE-PLAN.md` (§A–C: dual-write at `commit_turn`, `World::open`
   recovery via checkpoint⊕overlay, fail-closed convergence on the canonical root).
   A device that can't durably hold its image can't sync one. **This is the
   first concrete task** — it is fully specified and independent of everything else.

2. **Two devices replicate one image's cells** over the existing blocklace +
   `node/src/blocklace_sync.rs` + the `AttestedRoot`/`merkle_root_of_receipt_hashes`
   binding. Device B pulls device A's finalized turns, verifies each against the
   attested root (no trust in A), commits them to its own blocklace. Demo:
   `BALANCE_SUM = 0` holds on both; A's turn shows up on B with its proof.

3. **Offline-branch-then-stitch as the headline demo.** Device B disconnects, runs
   turns offline (a `Virtual/Branch` world off the last shared cursor), reconnects,
   and authors a `Stitch` through the Settlement Soundness gate. Show: the
   I-confluent parts auto-merge; a deliberate conflict (B spends offline a coin A
   also spent) is **rejected at the nullifier boundary**, surfaced for explicit
   linear-drop resolution. This is the branch-and-stitch protocol with two devices
   as the two parties — and it validates the entire cross-device thesis on one
   demo.

4. **(stretch) Handoff a surface laptop→phone-browser.** Migrate a surface cell to
   a phone-browser light-client holding a display-cap; show the `Migrated` receipt
   and the continuity-of-`state_root` theorem; the phone renders the attested
   frame. This needs the thin-client mobile shim (§3.3) but reuses cell migration
   (§2.3) entirely.

Milestone 1–3 ride **only shipped machinery** (persist, blocklace, attested roots,
branch-and-stitch's gate) plus the *two new branch-and-stitch turns*
(`EnterVirtualization`, `Stitch`) the distributed-time-travel work already scopes.
The Willow range-reconcile (§2.2) is an efficiency layer on top — not a milestone-1
blocker (a small image reconciles by full pull). Milestone 4 needs the mobile
client shim.

---

## 5. Honest hard parts (named, with their levers)

- **seL4-on-a-real-phone is years away** (§3.1). Native deos on a phone needs SoC
  board support, GPU/display device-tree, and verified-bootloader porting — "port
  your board to seL4" infrastructure. **Lever:** it is *not a protocol blocker* —
  the near-term mobile face is the thin web client (§3.3) to a home node running on
  hardware seL4 *does* support (or just a laptop/cloud node), so deos reaches your
  phone long before seL4 does.

- **No mobile client app exists** (§3.3). The display-cap thin-client *protocol* is
  in the code; the phone app that holds a display-cap, renders attested frames, and
  signs input is unbuilt. **Lever:** ~1–2k-line PoC over CapTP-relay/REST; the wasm
  light client already runs in a mobile browser as the interim face.

- **Battery / network / latency.** A phone is intermittently connected and
  power-constrained, so it cannot be a synchronous `n = 1` peer. **Lever:** this is
  *why* offline = a branch (§2.4) and the phone defaults to a thin display-cap
  (§3.3) — the bounds *are designed* to relax under poor connectivity; eventual
  revoke / merge-commit is the honest contract, not a degradation.

- **Live handoff is suspend-resume, not teleport** (§2.3). Mid-render Servo/JS state
  doesn't migrate today. **Lever:** the resumable description migrates cleanly
  (reopen-equivalent); true live handoff is the named Servo-on-seL4 PD address-space
  migration, a bounded artifact gated on one upstream blocker.

- **Conflict-resolution UX is unsolved at the surface.** The *mechanism* is exact
  (nullifier collision = conflict, linear-drop = explicit resolution); the
  *interface* a human uses to drop-or-transform a genuine conflict is design work.
  **Lever:** "spaceage = semi-automated" — auto-merge the I-confluent majority,
  surface only the rare genuine conflict; the moldable-inspector epoch
  (`project-moldable-inspector-epoch`) is where that UI gets built.

- **The handoff UX (which device am I on, what did I just move?).** Moving a live
  window between devices must be *legible* — the `Migrated` lifecycle badge and the
  honest `Virtual/Branch` vs `Main/Live` liveness-type are the substrate for it, but
  the gesture/affordance ("send this to my phone") is deos UX-vision work
  (`project-deos-ux-vision`: the 4-year-old-wonder + Pharo-liveness bar).

---

*( ◕‿◕ ) the closing couplet, since the cell already knows how to be two places:*
*one cap, two devices — the distance is just `n`;*
*go dark on the train, come home, and stitch it back again.*
