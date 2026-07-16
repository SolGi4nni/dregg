# Reproducible-build gate (Rung D2) — the bare-clone falsifier

**What it proves:** the tree builds from a **bare clone into an empty home with no
sibling `~/dev` repos and no warm cargo cache**. This is the one check that turns
"works on ember's laptop" into a test failure instead of a discovery weeks later. It is
the load-bearing falsifier of the reproducible-build campaign
(`docs/FORWARD-CAMPAIGN-2026-07.md` §7; `docs/reference/REPRODUCIBLE-BUILD-AND-FREEZE.md`
Rung D2, §4).

**Do not assert reproducibility by reading `Cargo.toml`.** Assert it from a green gate
plus a red canary. A design that trusts the manifest over the gate is the same disease
one level up (`REPRODUCIBLE-BUILD-AND-FREEZE.md` §6).

Artifacts:

| Artifact | Path |
|---|---|
| The gate script | `scripts/bare-clone-repro-gate.sh` |
| The CI workflow (this is a NEW file; **`ci.yml` is a different lane's**) | `.github/workflows/repro-gate.yml` |

---

## What the gate catches

Every reproducibility escape the design names reds this gate:

- a `[patch]` with a `path = "../sibling"` that isn't in the (empty) `~/dev` — the exact
  escape the plonky3-recursion determinism-patch was, removed 2026-07-15
  (`Cargo.toml:157-162`);
- an **unpushed** fork rev — a fresh `CARGO_HOME` forces a real fetch, and a rev that was
  never pushed fails to fetch;
- a **re-floated mutable branch ref** (`ark-serialize` is still branch-pinned today —
  `Cargo.toml:180-181`; `--locked` freezes it to the committed lock so a drift reds);
- a `Cargo.lock` that has drifted from the manifest (`--locked` refuses to regenerate);
- a whole-tree escape in the `--full` mode: an in-repo vendored `[patch]` path
  (`pathfinder_simd` `Cargo.toml:190`, `servo-paint` `:197`, `servo-net` `:200`) that
  didn't travel with the clone.

## How the isolation works

The script (`scripts/bare-clone-repro-gate.sh`) runs every `cargo` invocation under a
throwaway env:

| Var | Value | Why |
|---|---|---|
| `HOME` | a fresh **empty** temp dir | so `~/dev` has **no sibling repos** |
| `$HOME/dev` | created **empty** | a `path = "../sibling"` escape cannot resolve |
| `CARGO_HOME` | a fresh **empty** temp dir | forces a **real fetch** of every git dep; an unpushed rev fails |
| `RUSTUP_HOME` | **preserved** | the installed toolchain isn't the variable under test |
| rust-cache | **never restored** | a cached artifact could mask an escape |

The clone captures the **committed HEAD**, never your dirty working tree — a stranger
gets commits, not unsaved edits. That is why running it **before you push** (default
source = your local HEAD) catches an escape a push would ship.

---

## Run it locally

Executable today against your local HEAD (no push needed):

```bash
# The gate: bare clone → resolve under --locked → build the light spine (default-members)
./scripts/bare-clone-repro-gate.sh

# Cheapest sharpest falsifier — resolve the whole graph under --locked, no compile:
./scripts/bare-clone-repro-gate.sh --metadata-only

# Prove the gate can BARK: inject a sibling path, require it to go RED:
./scripts/bare-clone-repro-gate.sh --canary

# The whole tree, elephants included (HEAVY: gpui/servo/mozjs, no cache):
./scripts/bare-clone-repro-gate.sh --full

# Debug a red without losing the sandbox:
./scripts/bare-clone-repro-gate.sh --keep      # prints the temp path; cd in and re-run cargo
```

**Requires network** (a fresh `CARGO_HOME` fetches every git dep cold) and an installed
nightly toolchain (resolved from `rust-toolchain.toml`).

Stages, in order:

1. **`cargo metadata --locked`** — resolves the entire workspace graph against the
   committed lock. The cheapest, sharpest catch for a sibling path / unpushed rev / lock
   drift.
2. **`cargo build --locked`** (default-members — the light protocol/circuit spine,
   `Cargo.toml:19-23`) — proves the spine actually compiles + links from a bare clone.
3. **`cargo build --workspace --locked`** (`--full` only) — the elephants; proves the
   in-repo vendored `[patch]` paths travelled with the clone.

---

## In CI

`.github/workflows/repro-gate.yml` runs on every push to `main` and every PR.

### Executable today (armed on every push/PR)

Job **`repro-gate`** — the light-spine gate:

1. checkout (`lfs: true` — staged descriptor TSVs are LFS, `REPRODUCIBLE-BUILD-AND-FREEZE.md`
   §2.1);
2. install nightly (`dtolnay/rust-toolchain@master`, matching `ci.yml:39-41`);
3. **no `Swatinem/rust-cache`** — the gate must fetch cold;
4. **canary first** (`--canary`) — a green is not trusted until the canary proves the gate
   can red (the `check-mirror-gates.sh` discipline: a gate that cannot bark is worse than
   none);
5. **the gate** (`--source "$GITHUB_WORKSPACE"`) — clones the pushed commit under test,
   resolves under `--locked`, builds the light spine.

### Pending (labeled, not silently missing)

- **Full `--workspace` on every push** — job `repro-gate-full-workspace` exists but is
  **`workflow_dispatch` (manual)**, not per-push. *(pending: needs a per-push CI budget —
  a cold no-cache whole-tree build overruns the hosted runner's disk exactly as
  `ci.yml:104-113` documents; it carries the same disk-reclaim + debuginfo-off treatment.)*
  Run it before a freeze or on demand: **Actions ▸ Reproducible Build Gate ▸ Run workflow**.
- **Toolchain date-pin** — the gate installs a **rolling `nightly`**, so it can still red on
  a day with zero code changes. *(pending: needs Rung D0 — date-pin `rust-toolchain.toml`
  and every CI `toolchain: nightly` together; `REPRODUCIBLE-BUILD-AND-FREEZE.md` §2.2.)*
- **Sub-workspace `--locked` checks** — this gate is the **root** workspace only. The nine
  uncovered sub-workspace locks (`solana-lock`, `wasm`, `sdk-py`, `discord-bot`,
  `dregg-tui`, …) rot invisibly. *(pending: Rung D0 item 4 — a `cargo check --locked` job
  per sub-workspace on the `ci.yml:32-46` template.)*

### What this gate does NOT assert

- **Faithfulness (Lean↔Rust)** — that is `ci.yml`'s `lean-marshal-gate`, self-arming until
  the Lean seed is **published** (Rung D1, an ember-gated public push). A green here says
  nothing about the Lean↔Rust executor.
- **The published `main` reproduces** — the gate proves a *bare clone of the commit under
  test* builds; the reproducibility story is only true of a **pushed** commit, and local
  HEAD runs ahead of `origin/main`. Push, then let the push-triggered run confirm it.

---

## The relationship to the campaign

This gate is Rung D2 of Track D. D0 (date-pin the toolchain, rev-pin `ark-serialize`, add
`--locked` to `ci.yml`, cover the sub-workspace locks) and D1 (publish the Lean seed) are
the rungs whose regressions **this gate keeps fixed**: once they land, a PR that
reintroduces a sibling path, an unpushed rev, or a lock drift reds here on the PR that
introduces it. The freeze rungs (D3/D4) ride on this reproducible floor. Full staging:
`docs/reference/REPRODUCIBLE-BUILD-AND-FREEZE.md` §4.
