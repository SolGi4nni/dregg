# AGENTS.md — how to test (and build) dregg without melting your session

*(For any agent — Claude, Codex, grok-build, whoever. The single most common way
to waste an hour here is running the whole test gauntlet in debug mode. Don't.
Read this first. Deeper state lives in `REORIENT.md`; this is just "how do I run
things.")*

## Orient before you answer — the durable record, not the summary

The other expensive mistake (beside the debug-mode gauntlet): in a fresh or
post-compaction window, answering a *vision-level* or "how's X?" question from the
**compaction summary + a shallow shell probe**, instead of reading the durable
record. It flattens this (deeply layered, mature) project into a wrong one-liner —
which then gets written back as if it were authoritative.

**Read order — at window-start, and before any vision-level claim:**
1. `REORIENT.md` — the git-tracked continuity anchor (laws / lanes / gates / board).
2. `HORIZONLOG.md` — the live named-follow-up burn-down.
3. the memory index whole, then its flagged (⚑) topic files.
4. the relevant `docs/` + the **captured artifacts** for the question.

**Probes lie.** `which microkit` ("not found") + `rustup target list` ("no sel4
target") once "proved" the seL4 toolchain absent — while the Robigalia v0 demo
BOOTS in QEMU (the SDK is at `~/sel4-sdk`, the target is a `-Z build-std` JSON
spec, boot logs are at `/tmp/sel4-boot-*.log`). Absent-on-PATH ≠ absent; a probe ≠
a doc. Read the doc + the captured artifact (boot/test logs), and verify a dated
memory's `file:line` against HEAD before asserting it. The summary is a map drawn
from a moving train; the record is the territory — and the reading IS the job.

## Two traps grep + memory hide

- **`grep -c "sorry\|admit"` over `metatheory/` lies** — `admit` ⊂ `admitGuard`/`admits`,
  `sorry` ⊂ "sorry-free" docstrings. Proof-completeness = `lake env lean
  metatheory/Dregg2/Claims.lean` + the `Verify/*Lint.lean` gates. If you grep, `-nw` and
  read each hit.
- **A memory/doc note about STATE is a hypothesis — verify at HEAD**, especially
  pessimistic ones ("X is undone / a hole"). Truth = `CLAIMS.md`, the `Dregg2.lean`
  annotations, `lake … Claims.lean` — not a memory's mood. A named residual ≠ a hole.

## Use `cargo nextest`, not bare `cargo test`

`cargo-nextest` is installed. It gives per-test timing, parallelism, and — the
important part — **profiles that keep the slow proof tests out of your way**. The
config is `.config/nextest.toml` (the source of truth for the exact profile names
+ filters; read it).

```
cargo nextest run -p <crate>                  # one crate, fast — your default reflex
cargo nextest run -p <crate> -E 'test(/name/)'# a filter expression (one test/pattern)
cargo nextest run                             # the DEFAULT profile = the FAST set
cargo nextest run --profile heavy --release   # the SLOW set, ON DEMAND (see below)
cargo nextest list -p <crate>                 # list tests without running (validate filters)
```

- **The `default` profile is the fast gauntlet.** The >60s tests (the proof /
  recursion / IVC-fold / dispute-timeout suites) are EXCLUDED from it via a
  `default-filter`. So `cargo nextest run` is the everyday green check.
- **The `heavy` profile is the slow set, run on demand only** (CI-full / pre-release /
  when you specifically touched the prover). It is NOT in the normal loop. Run it in
  `--release` — these are proof-heavy and **debug mode is the main reason they crawl**
  (the IVC recursion fold is *minutes* in debug). The wrapper is
  `scripts/test-gauntlet.sh heavy-release` (also `default | ci | full | list-heavy`);
  full detail — the profile table + the heavy-set list — is in `docs/TESTING.md`.
  Offload it to the build node: `scripts/pbuild test scripts/test-gauntlet.sh heavy-release`.
- A few tests are `#[ignore]`'d outright (e.g. `t3_ivc_root_k2/k3`, "recursion fold
  is slow (minutes)") — run those with `--run-ignored`/`--ignored` only when needed.

## Heavy CARGO builds go to persvati; LEAN stays local

- **Rust (cargo) — offload to persvati** (24-core build node), per-lane isolated:
  `scripts/pbuild <lane-name> cargo nextest run -p <crate> …`. It rsyncs your WIP
  (gitignored target/.lake excluded) and builds there. Use this for the CPU-heavy
  crypto/circuit/lightclient builds. Do NOT run a full `--workspace` debug build
  locally to "check one thing" — it's minutes.
- **Lean (`lake build`) — keep LOCAL** (cwd `metatheory/`): the local `.lake/mathlib`
  cache is warm; a fresh persvati lane would re-download mathlib (catastrophic).
  `lake build Dregg2` is the axiom-clean gate.

## Searching: `sg` (ast-grep) for STRUCTURE, grep for text

`ast-grep` 0.40.5 is installed (run it as `sg` or `ast-grep`; no repo ruleset — it's
ad-hoc CLI). Reach for it whenever you're searching by **code shape**, not a literal
string — it matches the Rust AST, so it never false-positives on comments, doc
examples, or strings, and it's `$metavariable`-aware. This is the right tool for the
work we do constantly: finding the real call-sites of a symbol (cutover / grep-zero),
surveying trait impls, and codemod-style rewrites.

```sh
sg -p 'generate_effect_vm_trace($$$)' -l rust .      # every REAL call-site (grep-zero, no doc/comment noise)
sg -p 'impl $T for $X { $$$ }' -l rust turn sdk      # survey trait impls
sg -p 'WitnessedReceipt { $$$ }' -l rust             # every struct literal of a type (find producers)
sg -p '$X.bilateral_schedule' -l rust node turn      # every field/method access on any receiver
sg -p 'fn $F($$$) -> Result<$T, SdkError>' -l rust   # shape queries (all fns returning a given error)
```
- Metavariables: `$X` = one node, `$$$` = zero-or-more (args, fields, stmts), `$$$NAME`
  = a captured variadic. `-l rust` sets the language; pass paths to scope it.
- **Rewrites (codemods):** `sg -p '<pat>' --rewrite '<new>' -l rust <paths>` previews a
  diff; add `-U` to apply. ⚠ ALWAYS review the diff and scope it tight — never blind
  `-U` across a crate the cutover is mid-rewriting.
- **When grep still wins:** a literal symbol/string existence check, scanning logs,
  or non-Rust files. ast-grep has no Lean grammar — for `metatheory/` (`.lean`) use
  text grep / ripgrep, not `sg`.
- Prefer `sg` over `grep -r SomeFn` when you're about to DELETE or MIGRATE `SomeFn`:
  the grep count is inflated by comments/docs; the `sg` count is the real consumers.

## Don'ts that cost real time

- Don't run the whole-workspace suite to verify one change — `-p <crate>` + a filter.
- Don't re-run a build just to read its output — `… 2>&1 | tee /tmp/x.log | tail`,
  then `grep -nE 'test result:|error\[|FAILED' /tmp/x.log`. **The `tee | tail` exit
  code is `tail`'s, not cargo's** — always grep the log for `test result: ok` to
  confirm green; a pipeline "exit 0" lies.
- Don't add a slow (>60s) test to the default path. If a new test is heavy, route it
  to the `heavy` profile (a name/`package`/`test()` filter in `.config/nextest.toml`),
  don't `#[ignore]` it silently.

## Test-only imports belong inside `#[cfg(test)]`

A `use` at module scope that is only consumed by `#[test]`/`proptest!` code (or by
`#[cfg(test)] mod tests`) is genuinely unused in the non-test build, so `cargo fix`
and `cargo clippy --fix` will (correctly!) strip it — silently breaking the test
target. We are not writing programs that fight clippy; put each import where it is
actually used:

- A `src/*.rs` with a `#[cfg(test)] mod tests { … }`: put the test-only `use`
  **inside** that module (or write `#[cfg(test)] use …;`), never at module scope.
- A whole `src/*.rs` module that is pure test scaffolding (helpers + `#[test]`/
  `proptest!` only, no production API — e.g. `tests/src/*`, `protocol-tests/
  src/invariants/*`): gate the **module declaration** with `#[cfg(test)]` so the
  non-test build skips it entirely; module-scope `use` is then correct.
- An integration test (`tests/*.rs` — the whole target is test code): module-scope
  `use` is fine; just don't leave dead ones.
- A feature-gated symbol: gate the `use` with the same `#[cfg(feature = …)]` as its
  consumer.

Run `cargo fix` / `cargo clippy --fix` with `--all-targets` if you must, so the test
build is in scope; and check `cargo test --workspace --no-run --all-targets` before
trusting an import cleanup.

## Swarm-safety (if you're a subagent in a fleet)

- The **main loop commits**; subagents don't run git (unless explicitly deputized).
  Never `git stash`, never `git checkout`/revert to discard WIP — it is not
  swarm-safe (every parallel agent shares the working tree).
- **Never branch or worktree.** Commit to the current branch (`main`) — never
  `git checkout -b` / `switch -c` / `worktree add`. It strands work and drifts the
  shared HEAD off `main` for every other terminal on this tree. If
  `git branch --show-current` ≠ `main` after you commit, you branched by mistake.
- **Don't edit a file another lane is in.** If a cutover/HARDSWAP is rewriting a
  crate, segregate or work elsewhere; report a needed change rather than racing it.
- Concurrent persvati build collisions are normal — sleep 60s and retry, don't roll
  anything back.

*(Pair with `~/.claude/CLAUDE.md` (global prefs) + `REORIENT.md` (current state).
The verification economy: trust a lane's own narrow green; full gauntlets are
deliberate, on-demand `heavy`-profile / persvati acts, not per-turn taxes.)*
