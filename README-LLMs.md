# README-LLMs.md — dregg, for machines

This file is written for language models of every tier — large and small. It is
not a human document: no story, no hero image, no marketing. It is a dense,
declarative, navigable description of the dregg system so that a model reading it
can understand the architecture and operate on the codebase correctly. Facts are
stated flatly. Paths are exact. Commands are runnable. When a fact is point-in-time,
verify it against the code at `HEAD` (the durable record is `REORIENT.md` →
`HORIZONLOG.md`).

Names: **robigalia** is the project, **dregg** is the kernel, **deos** is the
desktop userlayer. deos runs on dregg runs in robigalia.

---

## 1. The one sentence

> A turn is the exercise of an attenuable, proof-carrying token over owned state,
> leaving a verifiable receipt.

Everything below is that sentence given algebra. If you remember one thing:
**the Lean kernel IS the executor the node runs**, and **all circuits are emitted
from Lean** — Rust authors zero constraint semantics.

## 2. The nouns and verbs

- **Cell** — the unit of isolation. Holds FOUR SUBSTANCES: **value** (per-asset
  i64 balances; an asset IS its issuer cell, which carries −supply, so every
  asset's sum is identically 0), **state** (programmable slots + nonce),
  **authority** (a capability tree / c-list), **evidence** (monotone nullifier /
  commitment / epoch ledgers). A cell also carries a **program**: a predicate over
  its own transitions, enforced on every turn touching it.
- **CellId** — `derive_raw(pubkey, token) = blake3::derive_key("dregg-cell-id-v1", pubkey||token)`.
  A cell id is a commitment to a public key; a random id is an unspendable bare
  address. Default agent-cell token = `blake3("default")`.
- **Eight verbs** — `create · write · move · grant · revoke · shield/unshield ·
  lifecycle · exercise`. Specified in Lean with machine-checked minimality (each
  irreplaceable) and completeness (they cover every effect). Source of truth:
  `metatheory/Dregg2/Substrate/VerbRegistry.lean`. Everything else (queues,
  escrows, auctions, namespaces, councils, bridges, channels) is a CELL-PROGRAM
  PATTERN over these verbs, not a kernel primitive.
- **Turn** — an atomic, capability-gated transition across one or more cells,
  shaped as a FOREST of effects with delegation edges. Authorization is structural:
  a turn that cannot exhibit a valid, sufficiently-empowered, fresh token chain
  does not execute. Delegation only attenuates: `granted ≤ held`.
- **Pred algebra** — all four guard polarities are one predicate language: caveat
  (on delegated power), program (on self), precondition (required of a turn),
  intent-demand (wanted of the world). Capabilities carry macaroon-style caveat
  chains; holding a capability = being able to exhibit the witness that discharges
  the caveats. The kernel checks the witness; it never takes the caller's word.

## 3. The architectural laws (ember-set, non-negotiable)

1. **ZERO Rust-authored constraints or AIRs.** All circuits/constraint semantics
   are EMITTED FROM LEAN as byte-pinned descriptor artifacts (SHA-256-fingerprinted
   registry, drift-rejected in CI). Rust only INTERPRETS them. Coverage gaps →
   emit from a proved Lean module, never author Rust.
2. **Green or bust.** No CI fallbacks, no last-good artifact pins, no
   continue-on-error masking. Fail loudly, fix the root.
3. **Rise to meet the claim.** An overclaim found = fix the text AND open the
   closure lane in the same breath. "Named / characterized / honest about a gap" is
   NOT "closed."
4. **Teach what-is.** Outward docs: present tense, first principles. No trajectory
   narration ("52→8 shrank" is banned). History lives in git.
5. **Correspondence is half of assurance.** The deployed system must sit inside the
   theorems' hypotheses. Named deployment seams are tracked, not assumed away.
6. **We do not name — we ship.** A logged/honest gap is never a deliverable; every
   caveat arrives with its closure lane already running.
7. **Conservation ≠ correctness.** Specs must be sufficient, not merely true. Prove
   every load-bearing spec non-vacuous (can be both true AND false). No quick fixes.

These are restated in `REORIENT.md` (read it first after any context loss).

## 4. The execution + proof architecture

- **The verified executor IS the executor.** The node's state producer is the Lean
  function `execFullForestG` (credential- and caveat-gated, proven sound), compiled
  to `dregg-lean-ffi/libdregg_lean.a` and linked into the node over a C ABI. It is
  not a model of the node; it is the function the node calls. Entry symbol:
  `dregg_exec_full_forest_auth` (see `dregg-lean-ffi/src/`).
- **The executor is a memory program.** Every kernel field + the receipt log
  projects onto one domain-tagged universal address space (`uproj`); a verb's
  effect provably equals the fold of its emitted memory trace. "The receipt binds
  the whole post-state" is constructive (the anti-ghost property): tampering a
  field the effect did not legitimately touch makes the turn unprovable.
- **Witness modes (symbolic / full).** `turn/src/collapse.rs`. A turn applies its
  state transition (the abstract semantics — balances, caps, nonces) independently
  of materializing its witness (Merkle roots, commitments, proofs). `WitnessMode::
  Symbolic` defers the witness layer, so a local UI/terminal turn pays effectively
  zero hashing; `collapse` re-runs deferred turns through full execution to
  materialize the exact witnesses on demand (determinism is discharged, so collapse
  reproduces precisely what `Full` would have witnessed). The admission gates
  (authority, conservation, freshness) are NEVER deferred — only the witness. A
  symbolic turn is therefore structurally local and unpublishable (it produces no
  `verifyBatch`-acceptable artifact); collapse is the only path to a publishable
  receipt. Grounded in the `Exec ⊑ Abstract` refinement
  (`metatheory/Dregg2/Spec/ExecRefinement.lean`): the abstract state is witness-free,
  and the deferred layer is exactly what the refinement throws away.
- **Circuits.** The live proof path is a single rotated multi-table circuit
  (IR-v2, R=24): a heterogeneous turn splits into maximal homogeneous cohort-runs,
  proven as a chain of rotated legs (`docs/PATH-PRESERVE.md`). STARKs: Plonky3,
  BabyBear field, Poseidon2 hash (the audited p3-poseidon2-air chip), FRI,
  Fiat-Shamir — post-quantum assumptions only. Proofs attest turns ADDITIVELY
  (verifying never re-executes history); recursive aggregation folds a whole
  history into one root a light client checks.
- **Plonky3 + the recursion fork.** Core p3 is pinned to rev `82cfad73` (in the
  root `[workspace.dependencies]`); the recursion fork
  (`github.com/emberian/plonky3-recursion` rev `72ffc56`, branch `update-plonky3-rev`)
  carries `RecursionInput::NativeBatchStark`. These are PURE git deps — no
  `[patch]`, no sibling checkout; a fresh clone resolves identically.

## 5. The crate map

| Path | What |
|------|------|
| `metatheory/` | The system in Lean 4 (library `Dregg2`): kernel, gated executor, circuit IR + descriptor emission, assurance case, deos modeling (`Dregg2/Deos/`), apps (`Dregg2/Apps/`). l4v-shaped. |
| `dregg-lean-ffi/` | Compiles the Lean executor → `libdregg_lean.a`; exports the node entry. `build.rs` splices the closure into a per-`OUT_DIR` archive (swarm-safe). |
| `node/` | The daemon: HTTP/MCP API, gossip + blocklace sync, block production driven by the Lean producer. |
| `circuit/` | The STARK stack: the Lean-descriptor interpreter (the prover), Plonky3, recursive aggregation, the light-client verifier. NO hand-authored AIRs. |
| `cell/`, `cell-crypto/`, `turn/`, `wire/` | `cell` is a ZERO-crypto types crate (the four substances + programs); `cell-crypto` holds the crypto (notes, value-commitments, seal/stealth, oblivious-transfer, read-caps). `turn` = turn types + the executor (`turn/src/executor/`) + witness-mode/collapse (`turn/src/collapse.rs`); `wire` = the codec. The Rust data plane. |
| `dregg-doc/` | The document language: a Pijul-shaped patch core (changes as first-class objects; conflicts-as-OBJECTS, not text markers; the branch-and-stitch pushout merge) + a `ropey`↔patch bridge. An editor buffer becomes a mergeable document; a save becomes a patch; multi-author becomes a merge. Standalone workspace. Merge correctness proved: `metatheory/Dregg2/Deos/DocMerge.lean`. |
| `blocklace/`, `federation/`, `captp/`, `coord/` | The signed equivocation-detecting DAG (BFT-final), committee machinery, capability transport (OCapN), coordination protocols. |
| `sdk/`, `sdk-ts/`, `sdk-py/`, `cli/` | The three SDKs (`.turn().sign().submit()`) + the `dregg` CLI. sdk-py embeds the real Lean kernel via FFI. |
| `app-framework/`, `starbridge-apps/` | The deos app framework (GatedAffordance, DeosApp) + 21 apps. |
| `starbridge-v2/`, `starbridge-web-surface/`, `servo-render/` | deos: the native gpui cockpit (embeds the real executor; `src/dock/` = the resizable/splittable/dockable pane workspace, vendored+adapted from Zed's `workspace`; `src/session.rs` = login=root-cap; `src/powerbox.rs`, `src/shared_fork.rs`), the web-surface/affordance/rehydration stack, the SWGL/servo render path (libservo default via the `web-shell` feature). |
| `deos-zed/`, `deos-terminal/`, `deos-matrix/`, `deos-hermes/` | The deos dev-loop apps (own workspaces, same gpui fork → one gpui resolves): a gpui code editor (`Fs` trait + the FirmamentFs seam), a real terminal (alacritty PTY + grid), a Matrix client (matrix-rust-sdk + the rehydratable-membrane seam), a ToolGateway-gated agent bridge (Hermes over ACP — every tool-call a cap-gated receipted turn). Mount as cockpit dock panes (the `dev-surfaces` feature). The system editing/building/operating itself. |
| `~/dev/gpui-component` | Vendored fork (`emberian/gpui-component`, Apache-2.0, repointed at the gpui fork) — the cockpit's widget kit (text `Input`, lists, tables, the code editor). |
| `pg-dregg/` | dregg caps + durable verified workflows as a PostgreSQL extension (RLS + the verified-write spine). Standalone workspace (excluded from root). |
| `sel4/` | The Robigalia/seL4 embedding: protection-domain crates, the Microkit assembly, the booting executor PD, the crypto-floor. |
| `site/` | The web Studio/Playground/Explorer + the wasm executor. |
| `wasm/` | The in-browser executor (standalone workspace; `no-lean-link`). |
| `dregg-deploy/` | DreggDL: declarative deployment specs; over-grant = in-forest cap amplification, caught pre-deploy. |
| `docs/` | Design documents. `REORIENT.md` + `HORIZONLOG.md` (repo root) are the live record. |

## 6. Build, test, verify

- **Lean kernel:** `cd metatheory && lake build` (warm mathlib; keep LOCAL — do not
  build Lean on a remote). Apex: `Dregg2/AssuranceCase.lean`. Keystones pin axioms
  via `#assert_all_clean` / `#assert_axioms` to exactly `{propext, Classical.choice,
  Quot.sound}` — no extra axioms.
- **Rust workspace:** `cargo build` / `cargo test`. The embedded-executor crates are
  pathologically slow in debug — use `--release` for `starbridge-v2`, the proof
  suites, and gauntlet runs. Default features include `recursion`; the
  `--no-default-features` floor build is a known separate path (do not assume it).
- **Remote scale:** `scripts/pbuild <lane> <cmd>` runs workspace-scale cargo on
  persvati (24-core). The `tee|tail` exit code is tail's, not cargo's — always grep
  the SAVED log for `test result:` / `error[`.
- **First contact:** no public server (the former `devnet.dregg.fg-goose.online` is
  offline). Run locally — `cargo build -p dregg-node && ./target/debug/dregg-node init
  --data-dir /tmp/d && ./target/debug/dregg-node run --data-dir /tmp/d --enable-faucet
  --port 8421 &` then `curl -s http://localhost:8421/status`. Full path: `QUICKSTART.md`.
- **Release:** `dist` (formerly cargo-dist), config in root `Cargo.toml`
  `[workspace.metadata.dist]`. `dist plan` shows the artifact matrix. The dev
  pre-release tag is `v0.0.0-dev` (NOT `v0.0.0~dev` — `~` is illegal SemVer). `cli`
  (bin `dregg`) + `node` (bin `dregg-node`) opt into shipping; node narrows to
  x86_64 host-native targets (it links the Lean archive, cannot cross-compile).

## 7. The assurance case

Stated in `metatheory/Dregg2/AssuranceCase.lean` + `docs/ASSURANCE.md`. Five
guarantees to a light client, plus the running entry:

- **A — Authority.** Every state change has an unforgeable, non-amplified, fresh
  token chain. Production (mint) is gated on holding the issuer's capability; the
  gate discriminates (it is not `:= True`).
- **B — Conservation.** Per asset, the resource sum is identically 0 on every
  reachable state. `AssetId := CellId`; mint/burn/fees are moves against
  negative-capable wells.
- **C — Integrity.** A receipt binds the whole post-state; circuit and executor
  provably produce the same receipt (the anti-ghost tooth).
- **D — Freshness.** No replay/double-spend; nullifier non-membership in a sorted
  tree; revocation at finality; stored caps cannot outlive the grantor's revocation
  (retrieval-epoch rule).
- **E — Unfoolability.** A light client checking only the aggregate root learns A–D
  for the whole history, re-witnessing nothing; a tampered aggregate cannot bind.
- **R — Running entry.** A∧B∧C hold over `execFullForestG` itself, not an abstract
  model. Apex `deployed_system_secure` conjoins all five over one committed forest.

**Crypto floor (assumed, typed hypotheses, never `axiom`):** Poseidon2 CR, BLAKE3
CR, Ed25519 EUF-CMA, HMAC/PRF, AEAD, FRI/STARK soundness, BLS quorum certs,
post-GST synchrony. The largest open distance from l4v-grade is the deployed-binary
bridge (Lean→C/.a link correspondence + wire-codec translation validation in
`dregg-lean-ffi/src/marshal.rs`), stated as obligations. Named seams live in
`docs/ASSURANCE.md` §3. NOT security-critical-ready; no independent audit.

**Adversary / key leak.** A leaked private key = a compromised principal, i.e. an
arbitrary opaque CONTROLLER — exactly what `polis_safety` already quantifies over
("verify the cage, not the animal"). So the blast radius is bounded by the deployed
proofs, not new machinery: the attacker reaches only the attenuation-closure of the
leaked c-list (no amplification), conservation forbids minting, confinement +
membrane-isolation bound the reach, and revocation kills it (topology-bounded;
immediate at n=1). `metatheory/Metatheory/KeyLeak.lean` (kernel-clean). The one named
open construction is **Settlement Soundness** — a revoke must bind into the finalized
commitment before settlement (so a leaked-then-revoked cap cannot settle against a
stale branch-time view); it is a composition of deployed pieces, and the same theorem
the distributed-time-travel and membrane-merge frontiers converge on.

## 8. The deos userlayer

deos adds ZERO new trust: every visual/interactive primitive reduces to a kernel
theorem. Key constructs (Lean models in `metatheory/Dregg2/Deos/`):

- **Affordance** — a cell declares named, typed, cap-gated verified-turn templates.
  The "button" is a cap-gated effect; who may press it is decided by held
  capabilities (the proven `is_attenuation` lattice: `required ⊆ held`).
  `GatedAffordance` pairs the cap-gate with a live cell-program state-gate.
- **Transclusion** — Xanadu, shipped. A quote IS a first-class provenanced citation
  of a source cell's committed field value; per-viewer, unforgeable. `Transclusion.lean`.
- **Powerbox (CapDesk)** — designate-then-attenuate; hand over a strictly weaker
  capability, never ambient authority. `starbridge-v2/src/powerbox.rs`.
- **Rehydratable frustum-snapshots** — a "screenshot" embeds a sturdyref behind a
  membrane; opening it re-attaches a live, per-viewer, attenuated, liveness-typed
  surface. `Rehydration.lean`.
- **A deos app** = a cap-mandated, verified, durable workflow: runs to completion
  exactly once across crashes (DBOS-style), each step admitted by a held capability
  (ocap), each step a verified turn (dregg), each step a fireable affordance (web).
  Four surfaces of one kernel. `Protocol/Workflow.lean`, `Deos/WorkflowBridge.lean`.

### 8a. The desktop (L5–L8)

deos is a desktop OS, not just a UI library. The layer stack
(`docs/DREGG-DESKTOP-OS.md`; the running build realizes a growing subset of it):

- **Compositor (L5) — the only new TCB.** Sole holder of the framebuffer + HID
  caps; its scene is a verified cell; it admits a surface's pixels only through a
  `present(region, contentDigest)` gate enforcing non-overlap, label-binding (the
  compositor computes the label from cell lineage, never the app's word), and
  focus/input-exclusivity. A window IS a `Capability{Surface(cell), rights}`.
  `sel4/dregg-firmament/src/{compositor_pd,surface}.rs` (+ a gpui-free mirror
  `starbridge-v2/src/compositor.rs`).
- **Window manager + shell (L6, untrusted).** A resizable/splittable/dockable pane
  workspace (`starbridge-v2/src/dock/`); surfaces are panes you split/dock/float.
  The cockpit is ONE privileged shell client, not the WM root.
- **Session / login = root capability.** Login = authenticate a key → derive the
  root cell (`CellId::derive_raw`) → grant the per-user `CapTemplate`; a session IS
  the resulting c-list; logout = `Effect::RevokeCapability` (synchronous + transitive
  at n=1). An agent (e.g. Hermes) logging in is the IDENTICAL ceremony with a
  narrower template — `polis_safety`'s controller-blindness makes human and agent
  inhabitants the same case. `starbridge-v2/src/session.rs`, `docs/deos/SESSION-LOGIN.md`.
- **The dev-loop apps as confined surfaces.** A code editor, a terminal, a Matrix
  chat client, a Hermes agent — deos editing/building/operating itself. Apps are
  not silos: an app's durable core is a CELL, its mutations are TURNS, its documents
  speak the document language → apps are VIEWS over one cell graph (a terminal runs
  `Symbolic` so it need not pay a witness per keystroke; collapses on demand).
  `docs/deos/APPS-AS-CELLS.md`.
- **Sandboxed firmament (the OS jail).** A confined host-PD: a subprocess whose ONLY
  channel is the firmament Endpoint, with confinement OS-kernel-enforced (macOS
  Seatbelt / Linux user+net+mount+pid namespaces + seccomp-bpf + Landlock; Windows
  job-object/AppContainer) — "no ambient authority" enforced by the host kernel, not
  merely by cap-discipline in one address space. `Target::HostPd`,
  `sel4/dregg-firmament/src/{sandbox,host_pd}.rs`. The DUAL — host fs/net/devices and
  OS containers GRANTED back as caps (a bridge = the sandbox read backwards) — is
  `docs/deos/HOST-AND-CONTAINER-BRIDGES.md`. The host backings prefigure native-seL4
  deos: same cap model, swappable backing.
- **Shared forks + the membrane.** A rehydratable frustum-snapshot is a cap-bounded
  FORK of the world that a message can carry; graduated rights — `embedded` (granted
  in, exercised locally), `studyref` (read-only, exercise = an upgrade request),
  `networkboundary` (exercise opens an owner-consent request, modeled as a
  `ConditionalTurn` whose hole is the owner's signed grant) — let you invite another
  principal into a confined fork of your computer. Merging diverged forks is the
  branch-and-stitch PUSHOUT where dregg's linearity (conservation, nullifiers,
  non-amplification) makes inconsistent events LOSSY-DROPPED. Matrix is the
  multiplayer transport. `docs/deos/{SHARED-FORK-CONSENT,BRANCH-AND-STITCH-PROTOCOL,
  DISTRIBUTED-TIMETRAVEL-SEMANTICS}.md`.
- **A deos distribution** is one self-contained bundle (cockpit + editor + terminal
  + chat + agent + web-shell + executor + firmament + compositor + a durable redb
  image), two targets one codebase: a host app-bundle (apps as confined host-PDs) or
  an seL4 `deos.img`. "The image IS your world" — portable; carry it between hosts.
  `docs/deos/DEOS-DISTRIBUTION.md`.

## 9. The surfaces (all route authorization through the same kernel)

- **SDKs:** `sdk/` (Rust, `AgentRuntime` embeds the executor), `@dregg/sdk` (TS,
  browser-parsable), `sdk-py/` (embeds the real Lean kernel). Inescapable auth step.
- **MCP server:** `node/src/mcp.rs` — every AI tool-call carries a biscuit-style
  capability the node admits/refuses through the Lean producer gate.
- **CLI:** `dregg` (`cli/`). **Discord bot:** `discord-bot/` (a first-class devnet
  citizen). **Site:** `site/` (Studio/Playground/Explorer + wasm executor).
- **pg-dregg:** caps as PostgreSQL RLS + durable workflows; `dregg_admits('read', id)`
  is the same decision the kernel makes.
- **seL4/firmament:** `sel4/` + `docs/FIRMAMENT.md`. The Robigalia v0 demo boots
  Rust userspace PDs, a real on-device STARK verifier PD, AND the executor PD (the
  Lean kernel runs inside a real seL4 protection domain), under QEMU. A real gpui
  browser): the gpui-offscreen render reaches the seL4 framebuffer — a real gpui
  `Scene` driven through the actual renderer (`render_scene_to_image` on lavapipe, no
  GPU) blitted onto ramfb (`docs/desktop-os-research/GPUI-OFFSCREEN-FORK.md`). The
  frontier is making that hosted image INTERACTIVE (input boots; live-repaint-on-turn
  is the next step — `docs/desktop-os-research/SEL4-INTERACTIVE-COCKPIT.md`). The "one
  true blocker" (libuv-free single-threaded Lean runtime) is closed
  (`docs/EMBEDDABLE-LEAN-RUNTIME.md`). An seL4 capability and a dregg capability are
  the same abstraction at two distances (the firmament axis: Local / Distributed /
  Surface / HostPd); at n=1 the distributed bounds collapse to strong local
  properties (immediate revoke, consistent checkpoint, synchronous present).

## 10. Working conventions (for agents operating here)

- **The main loop commits; subagents never run git.** Agents draft changes in the
  working tree and report; the orchestrator commits by explicit file-set (never
  `git add -A`). Verify the reflog — agents draft-and-return.
- **Swarm-safety:** never `git stash`, never `git checkout` to discard WIP (WIP-commit
  instead). The working tree is shared by parallel agents. `dregg-lean-ffi/build.rs`
  splices the archive per-`OUT_DIR` so concurrent multi-feature builds don't race.
- **Commits:** unsigned OK (`-c commit.gpgsign=false`); trailer
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.
- **The buggy oracle:** the legacy Rust `turn/` executor is the SUBJECT-UNDER-TEST
  that dregg2 replaces, never an oracle. Lean is the source of truth.
- **Read CODE for STATE, the record for SHAPE.** `.md` files can be stale and are
  dated/point-in-time; verify against `HEAD`. Orient: `REORIENT.md` → `HORIZONLOG.md`
  (the named-follow-up burn-down) → topic docs.
- **A fail-closed site is often just an unimplemented one.** When a verifier returns
  reject "because not yet wired," that is a maturation item, not a design choice;
  distinguish genuine default-deny from unwired stubs.

---

*Generated for machine readers. The human tour is `README.md` (above the
`(end-of-human-text)` marker is ember's; below it is ours).*
