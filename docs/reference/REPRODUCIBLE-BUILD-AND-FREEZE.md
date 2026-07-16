# REPRODUCIBLE-BUILD-AND-FREEZE — Track D: getting off ember's laptop, then freezing the protocol

**Status of this document:** design. It changes no code. Every current-state claim below is cited to a
file:line at repo HEAD (`09c9d3f`, 2026-07-16) and labelled by maturity (RUNS / BUILT / NAMED / VISION).
Where the launch-readiness workstream text in `HORIZONLOG.md` (the P0/P1 bullets) has gone stale against
the tree, this document states the tree, not the bullet, and says so.

## 1. The through-line

Everything the math earns is worth zero to an outsider until a stranger can `git clone` the repo into an
empty home directory and get the same green the author gets — and until the artifact that stranger's
light client verifies is pinned to a value nobody can silently recompute. Track D is those two things, in
that order: first make the build **reproducible off the laptop** (the real system today lives partly in
ember's `~/dev` sibling layout, a rolling nightly, one mutable branch ref, and a Lean seed that exists
only on `nextop`), then **freeze the protocol** (a real VK ceremony whose output is pinned as a hex
constant, one final descriptor registry, one committed commitment width) so the breaking changes all land
now, while no community state exists to migrate. The reproducible-build rung is the enabler; its keystone
is a CI gate that clones bare into an empty `~/dev` and builds — the one check that makes "works on my
machine" a test failure instead of a discovery. The freeze rung has a hard dependency on Track B: the
ceremony must pin the **proven-120** FRI configuration, not the deployed 57.98-bit calculator config,
which means the FRI degree cutover has to land *before* the ceremony, not after — sequenced so we pay the
multi-GB Groth16 re-setup exactly once.

## 2. Current resolution (cited, at HEAD)

### 2.1 Reproducible build — what is already closed

Several P0 items the launch-readiness bullet names as open are, at HEAD, **done**. State from code:

- **The plonky3-recursion sibling-path `[patch]` is GONE.** `Cargo.toml:157-162` documents that the
  2026-07-02 temporary determinism-fix path-patch was removed 2026-07-15; the four recursion crates
  (`p3-recursion`, `p3-circuit`, `p3-circuit-prover`, `p3-poseidon2-circuit-air`) now resolve purely from
  git rev `0a4a554` (`Cargo.toml:236-239`). There is no `[patch]`-to-sibling override for them. The
  bullet's "its own comment falsely claims 'pure git deps'" is stale — the comment is now true. **RUNS.**
- **The three main forks are pushed and rev-pinned.** Verified by `git ls-remote` at authoring time:
  `emberian/plonky3-recursion` `0a4a554` (`refs/heads/main` HEAD) ✓; `emberian/proof-systems` `c5305e63`
  (`relax-rayon-pin`, `Cargo.toml:174-176`) ✓. Both resolve for a fresh clone. **RUNS.**
- **The core plonky3 revs are one pinned commit:** `82cfad73` across all 18 upstream `p3-*` crates
  (`Cargo.toml:213-230`). **RUNS.**
- **`federation_id` is already deterministic** (the `HORIZONLOG.md` "non-deterministic today" is stale).
  `node/src/genesis.rs:243-252` derives it as `H(sorted committee pubkeys ‖ ml-dsa ‖ epoch=0)` via
  `dregg_federation::derive_federation_id_hybrid_with_epoch`, closing audit F1 — "a commitment to the
  committee, not random bytes." **RUNS.**
- **Staged TSV registries are LFS-tracked and CI checks out with `lfs: true`** on every `ci.yml` job
  (`.github/workflows/ci.yml:19,38,58,131,169,186,234,284,296,311,358`). A fresh clone gets the emitted
  descriptors. **RUNS.**
- **Sub-workspace lockfiles exist and are committed** for every standalone workspace (`solana-lock`,
  `solana-settlement`, `wasm`, `sdk-py`, `pg-dregg`, `deos-zed-full`, `discord-bot`, `dregg-tui`,
  `deos-homeserver`, `durable-workflow`, `forge-ci-runner` — `Cargo.toml:68`, all carry a `Cargo.lock`).
  (`dregg-doc` no longer has its own lock because it was folded into the root workspace as a member,
  `Cargo.toml:16,51`; that is correct, not a gap.) **BUILT** — but see 2.2: nothing forces `--locked`,
  and only one of the eleven is CI-exercised.

### 2.2 Reproducible build — what is genuinely open

- **The toolchain is a rolling `nightly`, not date-pinned.** `rust-toolchain.toml` pins `channel =
  "nightly"` with a prose floor ("≥ 2026-02-14"), which a fresh clone resolves to *today's* nightly — a
  moving target that can red the tree on a day with zero code changes. CI compounds it: every job installs
  `toolchain: nightly` via `dtolnay/rust-toolchain@master` (`ci.yml:23,41,75,…`) except clippy, which
  alone dates it (`nightly-2026-06-21`, `ci.yml:158`, with a comment admitting a floating nightly "can
  introduce new clippy lints that red the gate on a day with zero code changes"). **NAMED (open).**
- **`ark-serialize` / `ark-serialize-derive` are pinned by a MUTABLE BRANCH.** `Cargo.toml:180-181` pins
  `emberian/algebra` `branch = "serde-integration"`. `git ls-remote` shows that branch at `814047cb` —
  but a branch ref can move under the pin, so two clones a week apart can resolve different source. This is
  the "one pinned by BRANCH" the P0 bullet names, and it is the last non-immutable dependency ref.
  **NAMED (open).**
- **CI resolution is not `--locked`.** The `check` job runs `cargo check --workspace --all-targets`
  (`ci.yml:25`) and the `test` jobs run bare `cargo test` (`ci.yml:80,104,113`) — none pass `--locked` /
  `--frozen`, so CI can silently regenerate `Cargo.lock` (re-floating the mutable branch ref above)
  instead of proving the committed lock resolves. **NAMED (open).**
- **Ten of the eleven excluded sub-workspaces are never CI-exercised.** Only `solana-lock` has a job
  (`ci.yml:32-46`); a `wasm` job is proposed but unlanded (HORIZONLOG). The other locks
  (`sdk-py`, `discord-bot`, `dregg-tui`, `pg-dregg`, …) rot invisibly — the committed lock is present but
  nothing proves it still resolves. **NAMED (open).**
- **The Lean seed is CUT + VERIFIED but NOT PUBLISHED.** `dregg-lean-ffi/lean-seed.pin` has `TAG=`
  (empty); its `NOTE` records that a HEAD-matching seed was built and verified on `nextop` (Darwin-arm64,
  sha256 `58295f98…`) and a compressed asset is *staged* but unpublished because publishing is a
  public-remote push (ember-gated). Consequence: the `lean-marshal-gate` job (`ci.yml:215-276`) is
  self-arming — with `TAG` empty it prints "NOTHING WAS CHECKED" and asserts nothing (`ci.yml:250`,
  `:271-276`). The faithfulness gate is a green that means nothing until a seed release exists. And
  `nextop` is Darwin-arm64 only; the hosted Linux-x86_64 runner needs its *own* native seed cut on a
  Linux box. **BUILT (staged); publish is NAMED + ember-gated.**
- **There is NO bare-clone-into-empty-`~/dev` CI gate.** None of the 21 workflows in
  `.github/workflows/` clones fresh into an empty home with no `~/dev` and asserts the build resolves;
  `ci.yml`'s `check` job runs on a checkout that inherits the runner's cache and never proves the
  sibling-`~/dev` layout is unneeded. This is the keystone item, **NAMED (open)** — the single check that
  would surface every item in 2.1/2.2 as a red instead of a discovery.
- **Precondition: the published `main` lags the working tree by 3 commits.** Local HEAD is 3 ahead of
  `origin/main` (`7789990`); a fresh clone gets the older tip. The reproducible-build story is only true
  of a *pushed* commit. **Operational (open).**

### 2.3 Freeze — the four targets, at current resolution

- **The recursion VK is a self-recompute tautology.** `circuit-prove/src/recursive_witness_bundle.rs:180-186`:
  `lookup_recursive_vk(hash)` returns `Some(())` iff `hash == &compute_recursive_vk_hash()` — and
  `compute_recursive_vk_hash()` (`:135`) derives that hash from `RECURSION_P3_REV` and the verifier
  fingerprint at call time; the producer sets exactly that value (`:302`) and the verify path checks it
  (`:363`). Nothing is pinned to an externally-frozen ceremony output; the "registry" has one entry that
  is recomputed from the same inputs it checks. (Aside: the hashed `RECURSION_P3_REV = "c14b5fc0…"`
  (`:111`) is a *different* rev than the `Cargo.toml:236` pin `0a4a554` — the embedded proving-system id
  is decoupled from the actual dep rev, and should be reconciled in the same edit.) The settlement
  Groth16 VK *beneath* it IS a real external pin (`DREGG_APEX_RECURSION_VK`,
  `apex_shrink_gnark_export.rs:219-220`, fail-closed by `check_apex_vk_identity_pin`, mirrored by
  `chain/gnark/settlement_circuit.go:122`), but it is produced by a toxic-waste dev ceremony
  (launch-readiness audit). **Two VK jobs: kill the recursion tautology; re-run the apex ceremony.
  BUILT (tautological / dev-ceremony) — the freeze target.**
- **The descriptor registry still carries `-staged` names.** Thirteen staged artifacts remain under
  `circuit/descriptors/` (e.g. `rotation-v3-staged-registry.tsv`, `rotation-wide-registry-staged.tsv`,
  `rotation-wide-transfer-staged.tsv`, `rotation-wide-umem-welded-registry-staged.tsv`,
  `dregg-effectvm-rotation-state-v3-staged{,-r24,-r32}.json`, `umem-cohort-v1-staged-registry.tsv`).
  `docs/VK-REGEN-LOG.md` shows four generations of churn across these names. The name "staged" is a lie
  an outsider reads as "not real." **BUILT — the rename/retire target.**
- **The 8-felt faithful commitment RUNS and is tooth-guarded; the 1-felt projection is fenced but not yet
  impossible.** `circuit/src/faithful8.rs` is the 8-felt encoding; `circuit/src/ivc.rs:175,184` define
  `ACCUMULATED_HASH_WIDTH = 8`; `ivc.rs:1423` is the anti-laundering tooth (`assert_eq!(…, 8, "the
  faithful floor is 8 felts")`). The `no-degraded-felt` CI job (`ci.yml:287-299`) is an ast-grep tripwire
  against a lossy 256→31-bit fold reaching a commitment position. The freeze target is to make 8 the
  *sole* committed width everywhere the apex binds and delete the last 1-felt escape. **RUNS (8-felt
  path) — freeze = retire the residual 1-felt path.**
- **The non-regression differential (Control 4) is design-only.** `docs/VK-REGEN-CONTROLS.md:92`
  ("Control 4 — DIFFERENTIAL … **Not implemented**") specifies member-for-member, name-stable,
  no-narrowing cover between old and new descriptor sets, with a proposed `emit_descriptors.py
  --differential <old-rev>` entry point; leg (iv) — the old constraint set embeds in the new — is the real
  work, and "faking it with a name-only diff would launder regressions as green." Controls 1-3 (ack-gating,
  drift-report-only, append-only `VK-REGEN-LOG.md`) RUN (`VK-REGEN-CONTROLS.md:70-95`). **NAMED
  (design-only).**

### 2.4 The Track B dependency, stated precisely

The deployed FRI posture is **57.98 proven bits** at the apex (`d=4`; `PROVEN-120-CONFIG.md` §3.1, apex
row `ir2_leaf_wrap` = 57.00). Proven-120 needs the extension-degree cutover to **`d=8, lb=6, q=36,
pow=16, WRAP_LOG_CEIL=15` → λ = 122.60 on every shipped config** (`PROVEN-120-CONFIG.md` §3.4). That
cutover **re-keys the apex VK** at its Phase 4 (`FRI-CUTOVER-PLAN.md` §2 Phase 4: Groth16 re-setup, re-key
the `DREGG_APEX_RECURSION_VK` / `DreggApexRecursionVk` pinned pair, regenerate the Solidity verifier). The
MPC VK ceremony this document sequences **also** produces the apex VK. These are the same artifact: run
the ceremony at `d=4` and the frozen hex KAT pins the 57.98-bit config, and the `d=8` cutover then throws
that ceremony away and demands a second one. **The ceremony is Phase 4 of the FRI cutover, not a separate
event.**

## 3. The target

A stranger clones `github.com/emberian/dregg` into an empty home directory on a stock CI runner and gets
the same green ember gets — enforced by a CI gate that does exactly that on every push. Every dependency
resolves to an immutable ref (rev, not branch; date, not "nightly"), under `--locked`; the verified Lean
seed is a published release the faithfulness gate actually consumes. On top of that reproducible floor,
the protocol is frozen: the apex VK is a real multi-party ceremony output pinned as a hex constant that
`lookup_recursive_vk` checks *against* (not recomputes), the ceremony having been run at the proven-120
`d=8` config; there is one descriptor registry with honest names guarded by an implemented Control-4
differential; one committed commitment width; a committed genesis that is byte-deterministic. All breaking
changes land now.

## 4. Staged rungs (smallest first; each with its gate)

Rungs D0-D3 are degree-independent and land immediately. D4 (the ceremony + consumer flip) is gated on
Track B's FRI cutover (§5).

### Rung D0 — immutable every dependency ref (hours; no ceremony)

The cheap, purely-additive reproducibility fixes that need no VK work.

1. **Push canonical `main`** so a fresh clone gets the tree these rungs describe (the working tip is 3
   ahead of `origin/main`).
2. **Date-pin the toolchain:** `rust-toolchain.toml` `channel = "nightly"` → `"nightly-YYYY-MM-DD"` at a
   date ≥ 2026-02-14 that builds the whole tree today; change every CI `toolchain: nightly`
   (`ci.yml:23,41,75,…`) to the same dated pin. Keep the prose floor as a comment.
3. **Rev-pin `ark-serialize` / `ark-serialize-derive`:** `Cargo.toml:180-181` `branch = "serde-integration"`
   → `rev = "814047cb…"` (the current branch tip). This is the last mutable ref.
4. **Add `--locked`** to the CI build/test invocations (`ci.yml:25,80,104,113`) so a lock that drifts from
   the manifest is a red, not a silent regen; add a `wasm` (and other still-excluded) sub-workspace
   `cargo check --locked` job on the `solana-lock` template (`ci.yml:32-46`) so the nine uncovered locks
   stop rotting invisibly.

**Gate D0:** the `check`/`test` jobs pass with `--locked`; a scripted `git ls-remote` preflight over every
git dependency in `Cargo.toml` (and `starbridge-v2/Cargo.toml`'s zed fork) resolves each pin to a commit
that exists — grep for `branch =` under `[patch]`/`[workspace.dependencies]` returns nothing.

### Rung D1 — publish the Lean seed, arm the faithfulness gate (ember-gated push)

1. Cut the Linux-x86_64 seed on a Linux build host (the staged asset is Darwin-arm64 only; the hosted
   runner is ELF x86_64 — `lean-seed.pin` NOTE names this). `lean-seed.yml` is the publish workflow.
2. `gh release create` the seed tag, upload both platform assets + `.sha256`, and set `TAG=` in
   `dregg-lean-ffi/lean-seed.pin` (the publish job rewrites it).

**Gate D1:** the `lean-marshal-gate` job (`ci.yml:215-276`) reports `armed=1` (`ci.yml:245`) and runs
`check-lean-marshal.sh` against the fetched seed with `DREGG_REQUIRE_LEAN_GATE=1`; a deliberately
mismatched Rust executor makes it RED (proving it can fail). Until this rung, the gate asserts nothing —
so this rung is what makes the faithfulness gate load-bearing.

### Rung D2 — the bare-clone keystone gate (the falsifier for "works on my machine")

Add a `reproducible-build` workflow job (mirrored by a local `scripts/bare-clone-gate.sh`): on a clean
runner with `HOME` set to an empty temp dir and no sibling `~/dev`, `git clone` the repo fresh, then
`cargo metadata --locked` + `cargo build --workspace --locked` (fetch allowed, sibling paths not). The job
must NOT restore the shared `rust-cache`. It builds the `default-members` set first (the light
protocol/circuit spine), then `--workspace`.

**Gate D2 (the keystone):** green-on-clean, and — the standing canary, per the `mirror-gates` discipline —
**red-on-injected**: a canary that reintroduces a `path = "../sibling"` `[patch]`, an unpushed fork rev,
or a re-floated branch ref must turn this job RED, so the gate cannot rot into a checkmark that can't fail
(the `lean-marshal-gate` `TAG=` empty lesson). This gate is what keeps D0/D1 fixed: a regression reds here
on the PR that introduces it. **This gate is the whole point of Track D's first rung.**

### Rung D3 — freeze the descriptor registry and commitment width (breaking; no ceremony)

1. **Retire the `-staged` names:** promote the thirteen staged registries/JSONs to `v-final` names,
   update the Lean emitters and `include_str!` sites, re-emit via `scripts/emit-descriptors.sh`, append
   the `VK-REGEN-LOG.md` row (Control 3). Degree-independent — descriptor AIR shapes do not change with
   the FRI degree (`FRI-CUTOVER-PLAN.md` §4.3).
2. **Make 8 the sole committed commitment width:** confirm no 1-felt projection reaches an apex-bound
   position; the `no-degraded-felt` gate (`ci.yml:287`) plus the `ivc.rs:1423` tooth stay green; delete
   any dead 1-felt commitment path.
3. **Implement Control 4** (`VK-REGEN-CONTROLS.md:92`): `emit_descriptors.py --differential <old-rev>`
   enforcing (i) every old key present, (ii) per-member `piCount` + PI-offset stable, (iii) trace width
   monotone, (iv) old constraint set **embeds** in the new via descriptor-IR2 structured embedding (never
   a name-only diff — reuse the `EffectVmEmitUMemWeldWide` `#guard` cover shape at `metatheory/Dregg2.lean:637`
   lifted to registry granularity).

**Gate D3:** `descriptor-drift` (`ci.yml:343-379`) green on the renamed registry; the Control-4
differential run over the D3 rename reports name-stable, no-narrowing cover (it must, since a rename is
not a narrowing — that is the differential's first real exercise); a canary that drops an old member's
constraints reds it.

### Rung D4 — the VK ceremony, at the proven-120 config (the tail; depends on Track B)

This rung **is `FRI-CUTOVER-PLAN.md` Phases 4-5**, not a parallel event. It runs only after that plan's
Phases 0-3 have landed (`d=8` Rust flip + gnark wrap rewrite verified end-to-end against fixtures,
gate G3).

1. Run the **multi-party** Groth16 setup at the `d=8` circuit (`FRI-CUTOVER-PLAN.md` §2 Phase 4.1; on hbox
   under `swarm-build`, peak bounded by the plan's gate G1 measurement). Keep old VK artifacts in place.
   Choreography: publish the exact circuit commitment participants sign over; ≥1-honest-party sequential
   contribution with each transcript + attestation published; a public transcript verifier anyone can run
   to confirm the final key derives from the full contribution chain and no toxic waste survives.
2. **Kill the tautology:** pin the ceremony output as a hex KAT constant and change `lookup_recursive_vk`
   (`recursive_witness_bundle.rs:180`) to compare `hash` against that frozen constant instead of
   `compute_recursive_vk_hash()`; reconcile `RECURSION_P3_REV` (`:111`) with the real dep rev. Re-key the
   `DREGG_APEX_RECURSION_VK` / `DreggApexRecursionVk` pinned pair and `fixtures/apex_vk_identity.json` in
   one commit (`FRI-CUTOVER-PLAN.md` §2 Phase 4.2).
3. **Freeze the rest of genesis:** `federation_id` is already deterministic (`genesis.rs:247`); freeze the
   remaining genesis config (seed ledger, issuer well) to a committed, byte-reproducible artifact so a
   published genesis is reproducible from source.
4. Append the `VK-REGEN-LOG.md` row from a **clean** tree (`source dirty = no`).

**Gate D4:** `check_apex_vk_identity_pin` / `loadApexVkIdentity` REJECT the old artifact after the re-pin
(fail-closed both directions, `FRI-CUTOVER-PLAN.md` gate G4); the published ceremony transcript verifies;
`lookup_recursive_vk` accepts the frozen constant and rejects a recomputed-but-different hash (proving the
tautology is gone); an end-to-end turn on the devnet path settles under the new VK and the old-VK proof is
rejected (`FRI-CUTOVER-PLAN.md` gate G5). **ember-gated** (deployment flips are not lane-autonomous).

## 5. Dependencies on other tracks

- **Track B (FRI soundness) — HARD, blocking, and it dictates the sequence.** Rung D4's ceremony MUST pin
  the proven-120 `d=8` config, never the deployed `d=4` 57.98-bit config. Therefore D4 = Phases 4-5 of
  `FRI-CUTOVER-PLAN.md`, and Phases 0-3 of that plan (the free `WRAP_LOG_CEIL 16→15` both-win, the three
  ledger-artifact corrections, the `d=8` Rust flip, the 2-4-week gnark wrap rewrite, gate G3) are
  prerequisites of D4. If instead the freeze pinned `d=4` now, the cutover would force a **second**
  ceremony, a second re-key, and a re-publish of the "frozen" genesis and consumers — breaking exactly the
  artifact the freeze exists to make immovable. If the cutover's go/no-go gate G1 (Groth16 setup memory,
  currently ESTIMATED) fails, the fallback is `PROVEN-120-CONFIG.md` §7's Phase-0 59-bit posture or the
  BCSS25 mechanization route, and D4 waits on whichever resolves. **D0-D3 have no Track B dependency and
  proceed immediately.**
- **Node / devnet (deployment).** D4's gate G5 needs the persistent systemd node the launch-readiness
  bullet names (the hbox devnet ledger was lost on a hard kill). Deployment flips are ember-gated.
- **Value-path holes (P1).** Independent of Track D's correctness but shares the "before holding real
  value" deadline; sequence D-freeze and the value-hole closures into the same breaking-change window.

## 6. Risks and the load-bearing falsifier

**The load-bearing assumption is that a bare clone into an empty `~/dev` actually builds** — i.e. that the
sibling-path dependencies really are all gone and §2.1's "done" items are done. It is stated so it can be
attacked, and Rung D2 is its falsifier: the bare-clone gate either goes green (the assumption holds) or
reds on the first uncaught sibling path or mutable ref. Do not assert reproducibility from reading
`Cargo.toml`; assert it from a green D2 plus a red D2-canary. A design that trusts the manifest over the
gate is the "green on ember's laptop" disease one level up.

Other risks, each with its check:

- **A `[patch].crates-io` entry with a relative `path =` reaches the graph on a real build.** `Cargo.toml`
  still has vendored-path patches (`pathfinder_simd` `:190`, `servo-paint` `:197`, `servo-net` `:200`),
  documented as inert outside the gpui/servo elephant graph and pointing at **in-repo** vendored dirs
  (`starbridge-v2/vendor/`, `servo-render/vendor/`), so they travel with the clone. Falsifier: D2 builds
  `--workspace`, which pulls those crates — a missing vendored path reds D2.
- **The ceremony pins the wrong config.** Guarded structurally by §5: D4 cannot run until the cutover's
  Phase 3 gate G3 (a real `d=8` apex-shrink proof verifies in the gnark circuit) is green, so the ceremony
  physically operates on the `d=8` circuit.
- **The ceremony's honesty is unverifiable.** A Groth16 MPC is trustless only under ≥1-honest-party AND a
  verifiable transcript. Check: D4's public transcript verifier — if it cannot confirm the final key
  derives from the full contribution chain, the ceremony is re-run; the fail-closed
  `check_apex_vk_identity_pin` rejecting the old key is the on-chain half.
- **Control 4 laundered as a name diff.** A rename-only differential (D3) would pass while silently
  narrowing a capability. Check: leg (iv)'s constraint-embedding, with a dropped-member canary that must
  red.
- **The Lean seed drifts from HEAD.** `lean-seed.pin`'s provenance triple (`LEAN_TOOLCHAIN` /
  `MATHLIB_REV` / `DREGG_TREE_HASH`) is compared by `fetch-lean-seed.sh`; a drifted seed warns loudly
  rather than silently linking stale. D1's gate requires a HEAD-matching seed.
- **Publishing is the one irreversibly-public step.** D1 and D4 push to public remotes; both are
  ember-gated by design. A governance gate, not an engineering risk — named so it is not mistaken for an
  incomplete lane.

## Provenance

| claim | label | source (file:line @ HEAD `09c9d3f`) |
|---|---|---|
| sibling-path `[patch]` removed; p3-recursion pure git dep | RUNS (fixed) | `Cargo.toml:157-162,236-239` |
| proof-systems / p3-recursion revs PUSHED | VERIFIED (ls-remote) | `git ls-remote emberian/{proof-systems,plonky3-recursion}` |
| upstream plonky3 one rev `82cfad73` ×18 | RUNS | `Cargo.toml:213-230` |
| `federation_id` deterministic (F1 closed) | RUNS | `node/src/genesis.rs:243-252` |
| staged tsv LFS-tracked; CI `lfs: true` | RUNS | `.github/workflows/ci.yml:19,38,58,…` |
| 11 excluded workspaces, locks committed, 1 CI-covered | BUILT / NAMED | `Cargo.toml:68`; `ci.yml:32-46` |
| rolling `nightly` in repo + CI | NAMED (open) | `rust-toolchain.toml`; `ci.yml:23,41,75,158` |
| ark-serialize BRANCH-pinned (tip `814047cb`) | NAMED (open) | `Cargo.toml:180-181`; ls-remote |
| CI resolve not `--locked` | NAMED (open) | `ci.yml:25,80,104,113` |
| no bare-clone gate | NAMED (open) | absence in `.github/workflows/` |
| local `main` +3 ahead of `origin/main` | operational | `git rev-list --count origin/main..HEAD` |
| lean-seed `TAG=` empty → gate skips | BUILT, unpublished | `dregg-lean-ffi/lean-seed.pin`; `ci.yml:240-276` |
| recursion VK self-recompute tautology | BUILT (tautological) | `recursive_witness_bundle.rs:111,135,180-186,302,363` |
| apex VK pinned but toxic-waste dev setup | BUILT; ceremony NAMED | `apex_shrink_gnark_export.rs:219-220`; `settlement_circuit.go:122` |
| 13 `-staged` deployed registries | BUILT | `circuit/descriptors/*staged*`; `docs/VK-REGEN-LOG.md` |
| 8-felt commitment RUNS + tooth; 1-felt fenced | RUNS | `circuit/src/faithful8.rs`; `ivc.rs:175,184,1423`; `ci.yml:287-299` |
| Control 4 differential design-only; 1-3 run | NAMED (design-only) | `docs/VK-REGEN-CONTROLS.md:92,70-95` |
| deployed 57.98 bits (d=4); proven target d=8 λ=122.60 | DERIVED (Track B) | `PROVEN-120-CONFIG.md` §3.1,§3.4 |
| ceremony = FRI-CUTOVER Phases 4-5; consumes d=8 | DERIVED | `FRI-CUTOVER-PLAN.md` §2 Phases 4-5, §4.3 |
