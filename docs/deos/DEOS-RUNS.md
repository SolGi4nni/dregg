# deos runs — the reproduce index

A single index of what RUNS in deos, with the exact command to reproduce each
demonstration, the proof it emits, and the screenshot it captures (if any).

Each entry is real-by-running: a `cargo test` / bake you can copy and watch
produce its artifact. The proof is the executor's own receipt, a hard assertion
in the bake, or a named test — not a description. Where a screenshot is
committed, its path is given.

The source-of-truth record for what landed (with commit hashes) is the top
section of `HORIZONLOG.md`; this file is the runnable surface of that record.

Conventions: paths are repo-relative. A `cargo test` runs from the named crate
dir. Bakes that write a PNG print their proofs to stdout and exit non-zero on
failure (they hard-assert). Several demonstrations link the verified Lean
executor, so a real proving run can take tens of seconds.

---

## Self-hosting — develop dregg inside deos

The loop where a source edit inside deos is a receipted ledger turn AND the
deos terminal's toolchain compiles that very edit.

### The self-hosting loop (both halves, one view)
- **What it is:** the firmament editor (a save is a cap-gated `SetField` turn on
  the live `World` ledger) beside a live alacritty PTY running real `cargo` —
  both inside the deos image, under the live image header.
- **Reproduce:**
  ```sh
  cd starbridge-v2
  cargo build --features native-full --bin starbridge-v2
  ./target/debug/starbridge-v2 --render-self-hosting self-hosting-loop --render-size 1600x1000
  ```
- **Proof:** the bake hard-asserts BOTH (exits non-zero otherwise) and prints:
  `PROOF (a) editor: save fired a real turn — receipts 5 -> 6 on-ledger`;
  `PROOF (b) terminal: live alacritty PTY ran cargo --version INSIDE deos`.
- **Screenshot:** `starbridge-v2/self-hosting-loop.png` (3200×2000).
- **Doc:** `docs/deos/SELF-HOSTING-LOOP.md`.

### The FULL single loop (edit → receipt → disk-mirror → toolchain compiles it)
- **What it is:** the FirmamentFs↔disk dual-write closes the gap — the editor
  save commits the verified turn (the cell is the receipted source of truth),
  then mirrors the new content to disk, where a live `sh` PTY's `rustc`/`./prog`
  compiles and runs THAT edit.
- **Reproduce:**
  ```sh
  cd starbridge-v2
  cargo build --features native-full --bin starbridge-v2
  ./target/debug/starbridge-v2 --render-self-hosting-full self-hosting-loop-full
  ```
- **Proof:** three hard asserts — `PROOF (receipt)`: save fired a real
  cap-gated `SetField` turn (receipts 5→6 on-ledger); `PROOF (disk-mirror)`:
  the cell's v2 content was dual-written to `<dir>/main.rs`;
  `PROOF (terminal-sees-it)`: the live `sh` PTY ran `rustc main.rs && ./prog` →
  printed `v2`.
- **Screenshot:** `starbridge-v2/self-hosting-loop-full.png` (line-numbered
  syntax-highlighted code beside the terminal that compiled it).

---

## The desktop / cockpit

The deos cockpit (`starbridge-v2`) over the embedded verified image. The
moldable-inspector surfaces, the dock, the bakes the atlas crawls.

### The cockpit, baked per-surface (the atlas bake)
- **What it is:** the real gpui `Cockpit` element tree over the live `World`,
  rendered headless to a PNG (the same bake the dregg-atlas crawls).
- **Reproduce (any single surface):**
  ```sh
  cd starbridge-v2
  cargo build --release --features native-full --bin dregg-mcp
  cargo build --release --features headless-render --bin starbridge-v2
  # then drive the MCP `screenshot` tool, e.g. via the atlas:
  ( cd ../dregg-atlas && python3 shoot.py )
  ```
- **Proof:** a real PNG per cockpit surface; the MCP `survey`/`inspect`/`act`
  trail is replayed into the bake (every `act` is a real turn).
- **Screenshots:** `dregg-atlas/screenshots/*.png` (home, inspector, graph,
  proofs, …); the atlas's Surfaces pillar pages each embed one.
- **Doc:** `docs/deos/DREGG-MCP.md`, `dregg-atlas/README.md`.

---

## The IDE (the full Zed workspace over the cell ledger)

A real `zed::Workspace` whose filesystem IS the dregg cell ledger — Zed's own
project/outline/terminal panels, a save through the IDE is a verified turn.

### Full Zed workspace over FirmamentFs
- **What it is:** a real `workspace::Workspace` over a `Project` whose `Fs` is
  the cell ledger; Zed's own `project_panel` + `outline_panel` + `terminal_panel`
  dock and resolve; the project panel lists cells-as-files; a cell opened as a
  `language::Buffer`, edited, and `project.save_buffer`'d fires a `TurnReceipt`.
- **Reproduce:**
  ```sh
  cd deos-zed-full
  cargo test --features full-zed
  ```
- **Proof:** the full-zed tests are green — the workspace instantiates, the
  panels `Panel::load`+dock+resolve (all `Some`), a save through the workspace
  fires a verified `TurnReceipt`. Nested-dir expansion (a 2-deep cell tree
  materializes via the real scan) and a real OS PTY shell in the docked
  `TerminalPanel` are closed in the same suite.

### The Hermes agent panel in the workspace
- **What it is:** a real `workspace::Panel` wrapping deos-hermes's live
  `AgentDockView`, docked alongside project/outline/terminal — a confined agent
  over the cell ledger inside the IDE.
- **Reproduce:**
  ```sh
  cd deos-zed-full
  cargo test --features full-zed hermes_panel
  ```
- **Proof:** `workspace.panel::<HermesPanel>()` is `Some`; a 3-turn session
  through the panel's persistent `HermesGateway` admits in-mandate calls with
  real receipts, depletes a rate-3 budget to ceiling, refuses over-rate +
  out-of-mandate in-band.
- **Seam:** the agent brain is the faithful mock ACP peer (a live model needs an
  `acp` install + creds, absent here); gate/executor/receipts/ACP-wire are real.

---

## Apps on the live World ledger

The framework-shaped apps, each launched onto the cockpit `World` ledger, firing
a representative receipted affordance.

### 19/20 apps launch + fire real turns
- **What it is:** the `AppRegistry` wires the DeosApps (gallery, tussle,
  sealed-auction, bounty-board, identity, nameservice, escrow-market, …) plus
  polis (a `Program` backend) onto the live `World`; each launches over an
  `AppWorldSpine` and fires ONE representative affordance → a real `TurnReceipt`
  (`receipt.agent == backing cell`), visible to a second reader of the ledger.
- **Reproduce:**
  ```sh
  cd starbridge-v2
  cargo test --features app-registry,native-full
  ```
- **Proof:** the whole-set test iterates all 18 DeosApps (each lands its cell on
  `World::ledger()` + a receipt on `World::receipts()`); polis seeds a real
  2-of-3 `CouncilCharter` cell and fires a `propose` (DRAFT→PROPOSED).
- **Seam:** `first-room` is a multi-cell scenario/weld shim, not a `DeosApp` —
  it would become a launchable scenario, not an app.

---

## Web — the cockpit in a browser

The same gpui cockpit, bundled for wasm32 + WebGPU, painting a real frame in a
browser tab over the same in-tab verified executor.

### Web-deos paints in the browser
- **What it is:** the REAL `starbridge_v2::cockpit::Cockpit` bundled to
  `wasm32-unknown-unknown` on the `gpui_web` platform; in headless Chrome it
  initializes WebGPU and paints a real cockpit frame on a live canvas.
- **Reproduce (bundle):**
  ```sh
  cd starbridge-v2/web
  ./build-gpui.sh         # cargo build --release --target wasm32-unknown-unknown
                          #   -p starbridge-web --features gpui-web → wasm-bindgen
  # then serve web/ and open web/cockpit_gpui.html (it imports pkg-gpui + calls boot_cockpit)
  ```
- **Proof:** the headless-Chrome harness reports `WebGPU context initialized
  successfully`, `canvas backing max : 2560x1640 (PAINTED a real frame)`,
  `run-loop reentrancy : false`.
- **Screenshot:** `starbridge-v2/web/cockpit-gpui-web-painted.png`.
- **Doc:** `docs/deos/WEB-DEOS.md`.
- **Needs:** the first-paint fix lives in a LOCAL `emberian/zed` fork checkout
  wired via a `[patch]` in `starbridge-v2/Cargo.toml`; the cutover is to push the
  one-line `std::mem::forget(self)` fix upstream, bump the rev, drop the `[patch]`
  block. The wasm web-bundle build also needs `app-registry` made
  `cfg(not(wasm32))`-clean.

---

## Federation

Real multi-node `dregg-node` federations over QUIC gossip + blocklace consensus.

### A real two-node federation (n=2, cross-node finalize)
- **What it is:** two `dregg-node` procs sharing a 2-validator genesis form an
  n=2 committee; a faucet turn on A gossips to B and both DAGs converge
  byte-identically.
- **Reproduce:** the full staged recipe is in
  `docs/deos/DEV-NODE-RUNBOOK.md` → "A REAL two-node federation" (mint a
  2-validator genesis, build two data dirs, run both `--federation-mode full`
  with cross-pointing gossip ports, faucet on A).
- **Proof:** both `/api/blocklace/blocks` return the IDENTICAL 6-block DAG,
  `latest_height=1` on both, `dregg_consensus_attested_total 1` on BOTH (the
  turn block super-ratified cross-node), alice balance = 5000 on both.

### Quorum votes + reconnect/late-join + gossip-of-peers discovery (the tests)
- **What it is:** the consensus-attested vote path, the reconnect prober (a peer
  down at boot still converges), and authenticated gossip-of-peers (learn the
  mesh transitively from one seed).
- **Reproduce:**
  ```sh
  cd net  && cargo test late_join_prober
  cd net  && cargo test gossip_of_peers_transitive
  cd node && cargo test --bin dregg-node gossip_of_peers_accepts_committee_rejects_forged
  cd node && cargo test --bin dregg-node quorum_crossing_is_reported_on_whichever_vote_is_second
  ```
- **Proof:** named tests pass — a recovered QUIC link carries gossip both ways;
  a committee address is learned while a forged Sybil binding is rejected; the
  quorum transition fires exactly once on whichever vote crosses.
- **Doc:** `docs/deos/DEV-NODE-RUNBOOK.md` (late-join + gossip-of-peers sections).

### Network-portable process — cross-node CapTP cap handoff
- **What it is:** a `PresentHandoff` routes over the node↔node transport: A
  frames an introducer-signed handoff, B validates it against its OWN swiss table
  (never reads `held` from the cert) and resolves a live `SendCap`.
- **Reproduce:**
  ```sh
  cd captp && cargo test handoff
  cd node  && cargo test --bin dregg-node captp_handoff_e2e
  ```
- **Proof:** demonstrated over the real relay HTTP routes (A POSTs a sealed
  frame → B drains/unseals/validates/uses it on a `Bus`); no-amplification
  proven (over-broad handoffs + untrusted introducers refused before any cap
  installs; the `Bus` re-checks `admits` on every enqueue).

---

## Membrane / multiplayer (the fork-and-stitch primitive)

### The multiplayer membrane
- **What it is:** ONE `MembraneFrustum` (a cap-bounded `World::fork` cull, the
  screenshot-of-the-moment) carried over the postcard wire shape, rehydrated into
  TWO independent real `World`s under TWO distinct principals (both
  `frustum_root`-matched = anti-substitution), each driving a real verified
  `commit_turn`, then stitched via `Stitch::settle`.
- **Reproduce:**
  ```sh
  cd starbridge-v2
  cargo test --features native-full shared_fork
  ```
- **Proof:** 21 `shared_fork` tests on the real embedded executor — disjoint
  pushout-merge clean, the overlapping divergence resolves by the linear
  Dead-wins join transparently (not silent LWW), an over-authorized confer is
  REFUSED (`SettleOutcome::Refused`); Σδ=0 + authority sound.

---

## Agent (the confined Hermes loop)

### Confined Hermes agent loop
- **What it is:** an agent loop = `HermesGateway::admit_call`
  (delegAdmit SCOPE∧DEADLINE∧RATE → metered turn) + `AcpClient` (real ndjson
  JSON-RPC ACP) + confinement (a Rust ACP peer in an OS-sandboxed firmament
  host-PD).
- **Reproduce:**
  ```sh
  cd deos-hermes
  cargo test agent_loop_acceptance
  ```
- **Proof:** a 5-prompt session through ONE persistent gateway — in-mandate
  calls admitted each with a real turn receipt on the embedded Lean executor;
  budget depletes monotonically; over-budget refused in-band (names the rate
  leg); past-deadline refused (names the deadline leg, no turn); out-of-mandate
  tool refused first-try.
- **Seam:** tested over the faithful mock ACP peer; the live `hermes-acp`
  subprocess transport is built but needs an `acp` install + model creds (absent
  here) — only the agent brain is stood in.

---

## Chat (a live Matrix homeserver)

### Chat on a live homeserver — dregg-pilled round-trip
- **What it is:** two distinct Matrix clients (separate logins/stores/sync) A→B
  against a REAL Conduit homeserver: a plain `m.text` round-trips, a
  `MembraneEnvelope` (a forked-subrealm dregg object) round-trips byte-intact and
  rehydrates on B, a generalized `DreggObject` round-trips.
- **Reproduce:**
  ```sh
  cd deos-matrix
  ./scripts/live-test.sh           # boots a Conduit homeserver in Docker, runs the 3 live tests
  cargo test                       # green without Docker (the creds-gated live tests no-op)
  ```
- **Proof:** 3 live tests pass — the envelope survives a real server and
  rehydrates (anti-substitution holds across the real server).
- **Seam:** the envelope payload is the mock-host sample (deos-matrix can't link
  the Lean executor); the WIRE leg (envelope survives a real server + rehydrates)
  is proven on a real server.

---

## MUD (multi-inhabitant, physics is the proof)

### MUD multi-inhabitant
- **What it is:** 3 inhabitants / 2 connected rooms over the real embedded
  executor; the refusals are the executor's own gates via real receipts, not Rust
  bookkeeping.
- **Reproduce:**
  ```sh
  cd starbridge-v2
  cargo test --features native-full mud
  ```
- **Proof:** 9 tests (~76s real proving) — movement cap-gated (`move_through`
  writes the dest room cell; no door cap → `CapabilityNotHeld`, "a door is a cap
  you lack"); an item conserved across a multi-hop trade, exactly one contender
  wins (no dupe); authority-amplification on a `give` refused; value Σδ=0
  (overdraft refused).
- **Seam:** presence is the door-cap-gated write (entry cap-gating proven; a
  fuller presence-token move/grant is future).

---

## Co-driven multiplayer cards (two principals, one card, a membrane between)

### Distributed card fork→stitch
- **What it is:** two principals on DIFFERENT instances co-drive ONE shared card
  across a membrane boundary: `seal_fork` → `open_envelope` (anti-substitution
  root tooth) → `rehydrate_fork` → `stitch_envelopes`; both principals' edits
  survive (co-drive, not last-writer-wins).
- **Reproduce:**
  ```sh
  cd starbridge-v2
  cargo test --features native-full distributed_card
  # the runnable 3-beat app form:
  cargo run -p starbridge-branch-stitch-multiplayer
  ```
- **Proof:** 5 tests in `src/distributed_card.rs` — envelope substitution refused
  at the root tooth; both edits present post-stitch; a true conflict surfaces as a
  `ConflictRegion`, never a stomp.
- **Seam:** the envelope crosses an in-test boundary; carrying `CardForkEnvelope`
  between two RUNNING cockpits over the Matrix `MembraneEnvelope` is the named
  transport wire.

---

## The document rides the cell substrate

### dregg-doc `substrate` + executor-drive
- **What it is:** a `DocGraph` commits via the production sorted-Poseidon2 heap
  root; a document edit runs through the genuine `TurnExecutor` (cap-gated,
  finalized, journaled); a reopened doc re-seeds its text from the committed
  umem-heap.
- **Reproduce:**
  ```sh
  cd dregg-doc          # own workspace (root-excluded)
  cargo test --features substrate
  ```
- **Proof:** 8 substrate tests incl. anti-forge-provenance,
  construction-order-independence, stability-under-remerge; executor-drive makes
  per-region edit caps enforceable (editor cell vs region cell).
- **Seam:** the heap carries the current text + per-leaf provenance; the
  blame/patch CHAIN as first-class heap state (reopen reconstructs history, not
  just text) is the named next slice.

---

## Data plane (the Bus is the spine)

### Data-plane Bus — the real spine
- **What it is:** the `channels_service` rides the `Bus` (POST→enqueue→drain→SSE
  in lockstep); a multi-party flow proves 4 spine properties, all Bus-enforced.
- **Reproduce:**
  ```sh
  cd captp && cargo test data_plane
  cd node  && cargo test --bin dregg-node channels
  ```
- **Proof:** receipt-identity (Ed25519 `CustodyReceipt`, tamper flips
  `sig_verifies`, root chains old→new); cap-gated enqueue (`SendCap::admits`
  refuses over-auth before any box/cursor/receipt); ordered pub-sub to ≥2
  subscribers (causal_sequence 1,2,3; node SSE replays seq 0,1,2); drain lockstep
  (`drain_one` FIFO, sticky witness, no double-delivery). 199 captp + 246 node
  tests green.

---

## Document language (Xanadu)

### Xanadu document language
- **What it is:** doc-as-Pijul-patches with branch + MERGE (a same-position
  conflict yields ONE first-class `ConflictRegion` carrying both authors'
  alternatives, not silent overwrite), transclusion (darkens for an under-capped
  reader, provenance surviving), and bidirectional links (the quote registers in
  the `Backlinks` witness-graph).
- **Reproduce:**
  ```sh
  cd starbridge-v2
  cargo test --features native-full xanadu_e2e
  ```
- **Proof:** 3 `xanadu_e2e` tests pass; the executor-driven variant
  (`DocEditor`) makes each edit a cap-gated turn (an unauthorized edit refused
  in-band).

---

## Web engine (a real Servo page)

### Servo real page rasterizes
- **What it is:** a real Servo page laid out and rasterized (the surfman /
  event-loop / SWGL ceilings cleared).
- **Reproduce:**
  ```sh
  cd servo-render
  cargo test
  ```
- **Proof:** 17/17 green (the once-`#[ignore]`d render test RUNS); a `data:` page
  lays out (a CSS box measured 160×120) and "dregg" renders as 212-color
  antialiased glyphs.
- **Screenshots:** `servo-render/servo_real_page_render.png` +
  `servo-render/servo_real_text_render.png`.
- **Needs:** http(s) bytes still ride servo's hyper — fetching a remote page over
  the net needs a `net` fork; the 1-field vendored servo-paint fork reverts when
  upstream carries a SWGL `RenderingContext`.

---

## Not yet / needs X — the honest seams

These are the named ceilings on the runs above (each tracked in `HORIZONLOG.md`):

- **Servo http(s) over the net.** A page rasterizes locally; fetching a remote
  URL needs servo's hyper replaced by a `net` fork behind the net-cap gate.
- **Live ACP model in the agent loop.** The Hermes gate/executor/receipts/ACP
  wire/confinement are all real; the agent "brain" is the faithful mock ACP peer
  because a live model needs an `acp` install + model creds (absent here).
- **Web-deos cutover.** The browser paints, but the first-paint fix lives in a
  LOCAL `emberian/zed` fork checkout wired via `[patch]`; the cutover is to push
  the one-line fix upstream, bump the rev, drop the `[patch]`. The wasm web-bundle
  build also needs `app-registry` made `cfg(not(wasm32))`-clean.
- **deos-matrix executor mint.** The membrane envelope survives a real Matrix
  server + rehydrates (the wire leg is proven); the envelope payload is the
  mock-host sample because deos-matrix can't link the Lean executor.
- **Workspace dev panes on web.** The terminal/editor/chat gpui UI is web-ready;
  the backends are native resources (a PTY-over-WebSocket to `node/`, a
  firmament-backed `Arc<dyn Fs>`, a wasm-native `matrix-sdk`) — the wires per the
  app map in `docs/deos/WEB-DEOS.md`.
- **App registry (the long tail).** 19/20 apps launch + fire on the live ledger;
  `first-room` is a multi-cell scenario/weld shim (would become a launchable
  scenario, not an app).
- **MUD presence.** Entry cap-gating is proven; a fuller presence-token
  move/grant is future.
