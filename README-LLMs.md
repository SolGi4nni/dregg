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
| `cell/`, `turn/`, `wire/` | Cell state, turn types + the executor (`turn/src/executor/`), the wire codec. The Rust data plane. |
| `blocklace/`, `federation/`, `captp/`, `coord/` | The signed equivocation-detecting DAG (BFT-final), committee machinery, capability transport (OCapN), coordination protocols. |
| `sdk/`, `sdk-ts/`, `sdk-py/`, `cli/` | The three SDKs (`.turn().sign().submit()`) + the `dregg` CLI. sdk-py embeds the real Lean kernel via FFI. |
| `app-framework/`, `starbridge-apps/` | The deos app framework (GatedAffordance, DeosApp) + 19 apps. |
| `starbridge-v2/`, `starbridge-web-surface/`, `servo-render/` | deos: the native gpui cockpit (embeds the real executor), the web-surface/affordance/rehydration stack, the SWGL/servo render path. |
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
  Quot.sound}` — no `sorry`, no extra axioms.
- **Rust workspace:** `cargo build` / `cargo test`. The embedded-executor crates are
  pathologically slow in debug — use `--release` for `starbridge-v2`, the proof
  suites, and gauntlet runs. Default features include `recursion`; the
  `--no-default-features` floor build is a known separate path (do not assume it).
- **Remote scale:** `scripts/pbuild <lane> <cmd>` runs workspace-scale cargo on
  persvati (24-core). The `tee|tail` exit code is tail's, not cargo's — always grep
  the SAVED log for `test result:` / `error[`.
- **First contact (no build):** `curl -s https://devnet.dregg.fg-goose.online/status`.
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
  render is on the seL4 framebuffer too (a TAB-switchable mode beside the live cell
  browser): a cockpit-shaped gpui `Scene` driven through the actual gpui renderer
  (`render_scene_to_image` on lavapipe, no GPU) and blitted onto ramfb — the render
  path is proven; swapping in the live `cockpit::Cockpit` element tree is the one
  named frontier (`docs/desktop-os-research/GPUI-OFFSCREEN-FORK.md`). The "one true
  blocker" (libuv-free single-threaded Lean runtime) is
  closed (`docs/EMBEDDABLE-LEAN-RUNTIME.md`). An seL4 capability and a dregg
  capability are the same abstraction at two distances; at n=1 the distributed
  bounds collapse to strong local properties.

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
