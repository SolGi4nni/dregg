# ASSESS — the cold-build silent-export generator

**Date:** 2026-07-24 · **Mode:** read-only (no build was run; the shared `target/` had ~7 lanes on the lock)
**Subject:** `dregg-lean-ffi/build.rs` — the archive splice, the 24 `cargo:rustc-cfg=*_present` flags it
emits, and the `#[cfg]`-gated test modules that vanish when it does not emit them.

Everything below was obtained by reading (`grep`, `git`, the workflow YAML, the build script) and by
running `nm` over **archives that already existed on disk**. No `cargo` invocation was made.

---

## 0. Verdict in four lines

1. **CI builds cold — and worse than "cold": with no Lean archive at all.** `libdregg_lean.a` is
   *gitignored and has never been tracked*. Every GitHub-hosted runner checks out a tree without it.
2. In the **debug** profile — which is what `ci.yml`'s `cargo test --workspace` uses — an absent
   archive is a `cargo:warning` and an early `return`, so **all 24 cfg flags go unset** and every
   `@[export]`-backed test compiles out. `cargo test` exits 0.
3. In the **release** profile the same absence is a hard panic. The fail-loud tier *works*; it is the
   highest-signal job (debug `cargo test`) that sits in the one profile where it is disarmed.
4. **The prompt's stated mechanism is not the CI generator, but it is a real second generator**, and it
   is the one that explains the reported 0-vs-1 symptom on a warm shared tree. Both are documented in §3.

The headline is therefore **confirmed and broader than reported**, with one premise corrected: the seed
archive is not "git-tracked" (the build script's own header comment says it is, and that comment is false).

---

## 1. ⚑ Does CI build cold?

### 1.1 The archive is not in the repository

```
$ git ls-files dregg-lean-ffi/ | grep '\.a$'          # → nothing
$ git check-ignore -v dregg-lean-ffi/libdregg_lean.a
  dregg-lean-ffi/.gitignore:7:*.a   dregg-lean-ffi/libdregg_lean.a
$ git log --oneline -- dregg-lean-ffi/libdregg_lean.a # → nothing; never tracked
```

The local 106 MB `dregg-lean-ffi/libdregg_lean.a` (mtime Jul 16 16:54) is a **local artifact only**.
`dregg-lean-ffi/build.rs:7-9` claims "the git-tracked SEED archive lives next to this build.rs" — that
comment is **stale and false**, and it is load-bearing for how every reader reasons about this crate.

### 1.2 With no archive, no cfg is emitted

`dregg-lean-ffi/build.rs:1784-1802` returns **before** any cfg emission:

```rust
if !build_archive.exists() {
    println!("cargo:warning=dregg-lean-ffi: libdregg_lean.a absent (no git-tracked seed AND no \
              prior per-OUT_DIR working archive) — building MARSHAL-ONLY: ...");
    degrade_guard(require_lean_native, "libdregg_lean.a absent — ...");
    return;                                    // ← before line 1825
}
```

`println!("cargo:rustc-cfg=lean_lib_present")` is at `build.rs:1825`; the other 23
`dregg_*_present` emissions are at `build.rs:1845-2260`. All are downstream of that `return`.
A second early return at `build.rs:1808-1821` (Lean sysroot unresolvable) has the same effect.

The arming condition, `build.rs:1636-1638`:

```rust
let is_release = std::env::var("PROFILE").as_deref() == Ok("release");
let require_lean_native = require_lean || (is_release && !require_lean_off);
```

**Release ⇒ `degrade_guard` panics. Debug ⇒ warning, and cargo hides build-script warnings for
dependency crates unless you pass `-vv`.**

### 1.3 Proof from a real CI log

`ci.yml` job `Test (ubuntu-latest)` (run 29920321232, job 88940110393, 2026-07-22) — **with
`Swatinem/rust-cache@v2` active at `ci.yml:361`**:

```
warning: dregg-lean-ffi@0.1.0: dregg-lean-ffi: cannot resolve the Lean sysroot
  (no DREGG_LEAN_SYSROOT and `lake env` failed in metatheory/) — skipping the archive refresh
warning: dregg-lean-ffi@0.1.0: dregg-lean-ffi: libdregg_lean.a absent
  (no git-tracked seed AND no prior per-OUT_DIR working archive) — building MARSHAL-ONLY:
  lean_available() will be false and the node falls back to the UNVERIFIED Rust executor.
```

This settles the cache question empirically rather than by inference: **rust-cache does not restore the
per-`OUT_DIR` working archive** (it prunes workspace-member artifacts on save). Every rust-cache job is
category **(a) genuinely cold** for `dregg-lean-ffi`. There is no stale-OUT_DIR risk in CI because there
is never a warm OUT_DIR — category (b) does not occur.

### 1.4 Cache posture by job

Only jobs that build `dregg-lean-ffi` are listed. It is both a `members` and a `default-members` entry
(`Cargo.toml:16`, `Cargo.toml:23`), and `dregg-turn → dregg-pq → dregg-lean-ffi`
(`turn/Cargo.toml:43`, `dregg-pq/Cargo.toml:36`), so a bare `cargo test` builds it.

| Workflow | Job | `runs-on` | Profile | Posture |
|---|---|---|---|---|
| **`ci.yml:332`** | **`test` (ubuntu)** — `cargo test --workspace --exclude deos-zed` `:389` | `ubuntu-latest` | **debug** | **COLD → vacuous (proven §1.3)** |
| **`ci.yml:332`** | **`test` (macos)** — `cargo test --workspace` `:365` | `macos-latest` | **debug** | **COLD → vacuous** |
| `ci.yml:36` | `check` — `cargo check --workspace --all-targets` | `ubuntu-latest` | debug | cold (no tests run) |
| `ci.yml:525` | `lean-marshal-gate` — fetches the seed `:606` | `ubuntu-latest` | debug | **RED at fetch** (see §1.5) |
| `ci.yml:410/425` | `live-brain`, `clippy` | `ubuntu-latest` | debug | cold |
| `ci-invariants.yml:49/75` | `tree-builds`, `falsifiers` | `ubuntu-latest` | debug | cold |
| `bench.yml:11` | `bench` | `ubuntu-latest` | — | cold |
| `armed-teeth.yml:55` | `binding-teeth` `--release` | `ubuntu-latest` | **release** | **PANICS** (observed at `build.rs:1753:44`) |
| `armed-teeth.yml:159` | `lean-hard-mode`, `DREGG_TEST_REQUIRE_LEAN=1` | hosted | release | **RED at seed fetch**; nightly-only |
| `demos.yml`, `federation-node-{1,2,3}.yml`, `intent-service.yml` | `--release` builds | `ubuntu-latest` | release | fail-loud gate fires |
| **`lean-seed.yml:103`** | **`seed` — BUILDS the archive** | **`["self-hosted","lean-seed",…]`** | — | **the only category (c) warm tree in the repo** |
| `repro-gate.yml:41/78` | `repro-gate` | `ubuntu-latest` | — | **deliberately uncached** (`:62`) |
| `starbridge-v2-installers.yml:76/292` | macos/linux installers | `macos-14/13`, `ubuntu` | release | builds via `bootstrap.sh`; **caches the archive** (`:141-149`, `:351`) — the only archive-cached jobs, and they run no tests |

### 1.5 The seed pipeline exists but is not currently delivering

`lean-seed.yml` builds and publishes a content-keyed asset from a self-hosted runner. Only two hosted
jobs consume it (`ci.yml:606`, `armed-teeth.yml:190`), and both are **red at the fetch step**:

```
expected release asset: libdregg_lean-Linux-x86_64-v4.30.0-17f9aee9af0dacd3.a.zst
  (no asset named '...' on release 'lean-seed' — is a seed published for THIS platform + Lean HEAD?
```

There is a **structural race**: the key is content-hashed over the Dregg2 tree and the seed for commit
N is published *after* CI for commit N runs, so any `metatheory/**` change guarantees that commit's CI
fetches nothing. This is a design issue independent of the cfg hazard, and it is why the two lanes that
*would* have armed the gates have never armed them.

### 1.6 Statement of the headline

> **Every `@[export]`-backed test behind a `#[cfg(dregg_*_present)]` gate has been passing vacuously in
> CI, on every hosted runner, for as long as the archive has been absent — which is always, because the
> archive has never been in the repository.** In debug the absence is a hidden warning; in release it is
> a hard failure. The `--release` lanes are red, not vacuous — the fail-loud tier is working. The gap is
> exactly the debug `cargo test --workspace` lane, which is the single highest-signal job in the repo.

---

## 2. Blast radius — the cfg-gate inventory

**Containment (good news): all 24 flags are consumed only inside `dregg-lean-ffi`.** A tree-wide grep for
`#[cfg]`/`#[cfg_attr]`/`cfg!` over all 24 names found exactly one hit outside the crate, and it is prose:
`dreggnet-web/src/overlay.rs:500` (a comment). **No always-dead cross-crate code exists.**

### 2.1 The count that matters

**9 test functions vanish**, all in `dregg-lean-ffi/src/lib.rs:1516-1772`, and all **doubly nested**: each
sits in `#[cfg(all(test, <flag>))] mod …` inside `#[cfg(lean_lib_present)] mod ffi {` (opens `lib.rs:790`,
closes `lib.rs:1773`). So `lean_lib_present` alone takes all 9.

The crate has 20 unit tests. With every flag unset, `cargo test -p dregg-lean-ffi --lib` reports
**`11 passed`, not `0`**. That is worse than the reported symptom: a zero gets noticed; eleven green tests
look like a healthy crate while every verified-crypto and verified-decision assertion has evaporated.

**Correction to a premise:** `grain-verify/` and `dregg-lean-ffi/tests/` contain **zero** cfg-gated items.
They gate at *runtime* on `*_core_available()` and self-skip — a different failure mode, covered in §2.3.

### 2.2 Ranked by what is lost

Fallback quality is uniformly correct: **every `#[cfg(not(...))]` arm returns `Err` or `false`. None
returns `Ok(true)`, `Ok(false)`, or a permissive default at a security boundary.** The danger is not the
fallback bodies — it is that `*_present() → false` is a *silent* signal callers translate into "install
nothing, use the Rust twin" or "skip the test".

| Rank | Flag | Tests lost | What is lost |
|---|---|---|---|
| 1 | `lean_lib_present` | **9 (all)** | Master switch. All 18 bridge fns → `Err`, all 14 `*_present()` → `false` (`lib.rs:1775-1948`). Every verified decision falls back to a Rust twin in one move. |
| 2 | `dregg_grain_r3_verify_present` | 1 | **The wound-#22 anti-forgery teeth.** `lib.rs:1549` is the *only* place the 8-lane width tooth (`lib.rs:1574`, the ~2^31-grind attack) and the anti-self-anchor tooth (`lib.rs:1580`) are exercised. Losing it deletes the only automated proof that the grind is closed. |
| 3 | `dregg_fips204_verify_real_present` | 1 | Real ML-DSA-65 verify leaves the verified TCB; `dregg-pq` answers with the **unaudited `fips204` 0.4 crate**. |
| 4 | `dregg_cross_cell_conserves_present` | **0** | Hidden mint/burn detection. `exec-lean/src/conservation_oracle.rs:41` declines to install the oracle; the executor keeps the hand-written Rust `BlockConservation` twin. **No test guards this flag at all.** |
| 5 | `dregg_interchain_reached_consensus_present` | **0** | Bridge trust verdict. Fail-closed by design, but `bridge/src/interchain_adapter.rs:331` *skips both polarities* — its own comment admits a `false` assertion "would pass VACUOUSLY". |
| 6 | `dregg_distributed_exports_present` | **0** | **Six verified gates on one flag** (`distributed_ffi.rs:432`): CapTP handoff/drop/pipeline + coord 2PC/causal/budget. Downstream is *inconsistent*: `captp/src/handoff.rs:756` fails closed, but `coord/src/atomic.rs:305` "falls back to the native Rust (never break the live coordinator path)" — the 2PC decision silently reverts to an unverified decider. |
| 7 | `dregg_constraint_admits_present` | **0** | Deployed-constraint admission; `exec-lean/src/constraint_oracle.rs:818` keeps the Rust admission. |
| 8 | `dregg_holding_grant_weight_present` | **0** | Governance weight. Fail-closed, but the whole positive grant path becomes untestable (`holding_weight.rs:1273` skips every grant test). |
| 9 | `dregg_finalize_gate_present` | **0** | Finality + τ-order. Best-defended minor: `node/src/finality_gate.rs` uses `demand_lean` at 7 sites. |
| 10-12 | `dregg_fips204_sign_real`, `dregg_mlkem_decaps_real`, `dregg_mlkem_encaps_real` | 1 each | Deployed sign / KEM revert to unaudited `fips204` / `ml-kem` 0.2.3. |
| 13 | `dregg_strand_admit_present` | 0 | Federation admission falls back to `admitted_no_gate` (seeds-only). |
| 14-15 | `dregg_mldsa_keygen_real`, `dregg_mlkem_keygen_real` | **0** | **The untested crypto pair** — real KAT-anchored keygen cores in the identity/KEM TCBs with *no gated test module*, unlike all six sign/verify/encaps/decaps siblings. A genuine coverage gap independent of this hazard. |
| 16-19 | `dregg_fips204_verify/sign`, `dregg_fips203_encaps/decaps` | 4 | The most assertion-dense tests (tampered c̃, out-of-range z, round-trips, implicit-reject divergence). `lib.rs:1670` is `all(test, encaps, decaps)` — **either** flag alone kills it. |
| 20 | `dregg_storage_content_root_present` | 1 | **Structurally unique: the only flag with no `#[cfg(not(...))]` arm anywhere.** No stub, no runtime probe. The feature is 100% invisible when off, and the `#[used]` Poseidon2 linker anchor (`lib.rs:38`) disappears with it. |
| 21-22 | `dregg_decide_refines`, `dregg_handler` | 0 | Deploy refinement mirror; handler documented non-load-bearing (`build.rs:1851` panics under `require_lean_native`). |
| 23 | `dregg_direct_present` | 0 | Perf path only (JSON fallback). Most cfg sites (11), lowest stakes. |

### 2.3 The amplifier: runtime self-skip

The 9 vanishing tests are the smaller half. **~56 sites across 20 files gate on `*_core_available()` at
runtime and quietly skip**, including `grain-verify/tests/r3_whole_history.rs:162`,
`r3_width_falsification.rs:63`, `dregg-pq/tests/mldsa_lean_verify.rs:76`, `node/tests/mldsa_live_sign.rs:81`,
`sdk/tests/mlkem_sdk_kem_verified.rs:98`, `exec-lean/tests/constraint_oracle_differential.rs:2116`.

The countermeasure exists and is exactly right — `demand_lean` (`dregg-lean-ffi/src/lib.rs:110-126`):

```rust
assert!(!armed,
  "DREGG_TEST_REQUIRE_LEAN=1 but the linked archive lacks the {what} — this test would have \
   SILENTLY SKIPPED its verified-gate assertion and reported `ok`. ...");
```

But it is used at only ~45 sites in 22 files, and **`grain-verify`, `dregg-pq`, `dregg-governance`,
`bridge`, `sdk`, `dregg-interchain-gov`, `grain-turn` use it zero times** — precisely the crates guarding
the PQ cores, the R3 falsifier, governance weight and bridge trust. And `DREGG_TEST_REQUIRE_LEAN=1` is set
in exactly one workflow (`armed-teeth.yml:209,226`), which is nightly-only and currently red at fetch.

`demand_lean` cannot help the 9 cfg-gated tests at all: they do not exist to be run.

---

## 3. The two generators (the prompt's mechanism, corrected and confirmed)

### 3.1 Generator A — no archive (dominant in CI)

Covered in §1. Not an mtime problem: there is simply nothing to splice.

### 3.2 Generator B — re-seed wipes the splice while the object cache stays warm (the warm-tree hazard)

The prompt described this as "the splice only recompiles `.c` newer than the freshly-copied OUT_DIR
archive". The literal comparison is `.c` vs the cached `.o` in `$OUT_DIR/dregg2_closure_objs/`
(`build.rs:528-534`), not vs the archive — so on a *truly* cold OUT_DIR every `.c` does recompile. But the
hazard is real, one level up:

- `seed_build_archive` (`build.rs:234-272`) re-copies the seed over the working archive whenever the seed
  is newer — **wiping the previously spliced Dregg2 members**.
- The splice is then gated by `build.rs:591`:
  ```rust
  let needs_splice = recompiled || !archive_has_dregg2(archive);
  ```
- `archive_has_dregg2` (`build.rs:1383-1390`) only asks whether *any* `Dregg2_*.o` member exists. **The
  seed already contains Dregg2 members** (it exports 142 `dregg_*` symbols — see §4), so it returns `true`.
- If the `.o` cache is warm, `recompiled == false`. Therefore `needs_splice == false`: the freshly-copied
  seed is linked **without re-splicing**, and the ~53 splice-only exports are absent — *while the `.o`
  files that define them sit right there in `dregg2_closure_objs/`.*

This is exactly the reported symptom — the same feature hash, the symbol present in one OUT_DIR and
absent in another — and §4 reproduces it from disk. `archive_has_dregg2` being an existence check rather
than a *completeness* check is the specific defect.

Every degrade path in `build_dregg2_archive` (lake failure `:433-452`, leanc failure `:574-586`, splice
failure `:606-616`) reports via `cargo:warning=` and returns. The build script says so itself at
`build.rs:2118-2121`: *"cargo HIDES build-script warnings for dependency crates unless you pass `-vv`. The
degrade is invisible in a normal log."*

---

## 4. `nm` evidence, obtained without building

20 archives exist on disk. Extraction: `nm -g --defined-only <a> | grep -oE '_dregg_[a-z0-9_]+$'`.

**Total `dregg_*` exports range from 142 (pure seed) to 195 (fully spliced).**

The decisive result — **identical cargo feature hash, divergent exports**, which isolates OUT_DIR state as
the only variable:

```
--- hash 3de8b430d8f6dc09 (debug) ---
   142 exports  deploy/gateway-ask/target/debug/build/dregg-lean-ffi-3de8b430d8f6dc09/out/
   164 exports  dregg-interchain-gov/target/debug/build/dregg-lean-ffi-3de8b430d8f6dc09/out/
   185 exports  host-gateway/target/debug/build/dregg-lean-ffi-3de8b430d8f6dc09/out/

--- hash f9b781ed3fea623d (release) ---
   193 exports  sdk-ts/test/rust-verifier/target/release/build/dregg-lean-ffi-f9b781ed3fea623d/out/
   142 exports  target/release/build/dregg-lean-ffi-f9b781ed3fea623d/out/
```

And the reported symptom, reproduced exactly, at the same feature hash `f9b781ed3fea623d`:

```
dregg_grain_r3_verify   present in sdk-ts/…/out/libdregg_lean.a          → 1
dregg_grain_r3_verify   present in target/release/…/out/libdregg_lean.a  → 0
```

Per-symbol matrix (`1` = exported, `.` = absent), 22 probed symbols:

| exports | archive (OUT_DIR) | strand | decide | storage | fips204 v/vR/s/sR | fips203 e/d | mlkem D/E/K | mldsa K | grain | hold | inter | cadm | xcell |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 142 | **`dregg-lean-ffi/libdregg_lean.a` (THE SEED)** | . | . | . | . . . . | . . | . . . | . | **.** | . | . | . | . |
| 142 | `deploy/gateway-ask/…debug/3de8b430…` | . | . | . | . . . . | . . | . . . | . | **.** | . | . | . | . |
| 142 | `target/release/…f9b781ed…` | . | . | . | . . . . | . . | . . . | . | **.** | . | . | . | . |
| 147 | `auditable-fund`, `collective-choice`, `confined-swarm`, `mud-dregg` (debug) | 1 | 1 | . | . . . . | . . | . . . | . | **.** | . | . | . | . |
| 164 | `dregg-interchain-gov/…debug/3de8b430…` | 1 | 1 | 1 | 1 1 1 1 | 1 1 | 1 . . | . | **1** | 1 | 1 | . | . |
| 174 | `discord-bot`, `target/debug/{5f86ad8d,cb318241,d3b9287a}` | 1 | 1 | 1 | 1 1 1 1 | 1 1 | 1 1 1 | 1 | **1** | 1 | 1 | 1 | 1 |
| 185 | `host-gateway/…3de8b430…`, `dreggnet-gear` | 1 | 1 | 1 | 1 1 1 1 | 1 1 | 1 . . | . | **1** | 1 | 1 | . | . |
| 192-195 | `target/debug/b251a847`, `target/release/{34b74c5a,374971d1,7b4e2178}` | 1 | 1 | 1 | 1 1 1 1 | 1 1 | 1 1 1 | 1 | **1** | 1 | 1 | 1 | 1 |

Two facts worth stating plainly:

- **The seed exports none of the security-critical splice-only symbols.** It has `dregg_exec_full_forest_auth_direct`, `dregg_captp_validate_handoff`, `dregg_coord_2pc_decide`, the `dregg_d_*` marshalling family — but **zero** of `grain_r3_verify`, `fips204_*`, `fips203_*`, `mlkem_*`, `mldsa_*`, `constraint_admits`, `cross_cell_conserves`, `holding_grant_weight`, `interchain_reached_consensus`, `storage_content_root`. This corroborates `build.rs:2203` ("the git-tracked seed archive exports NONE of these") and means **a seed-only build is a fully disarmed build.**
- **Three OUT_DIRs are at exactly seed level (142)** — they were seeded and never spliced, i.e. Generator B caught in the act on this very disk.

---

## 5. The fix shape — and the fact that it already exists

### 5.1 It is already implemented, for 6 of 24 symbols

`build.rs:2143-2217` is **precisely the recommended fix**: a manifest of required symbols, re-probed on
the artifact after the splice, hard-failing the build. It even diagnoses this exact class in its own
comment (`build.rs:2113-2126`):

> *"In such a build every `*_real_core_available()` probe returns false … and `dregg-pq` answers
> security-critical operations with the UNAUDITED `fips204` 0.4 / `ml-kem` 0.2.3 crates. **Nothing errors.
> The build is green. The deployed binary runs crypto nobody audited.** … This gate checks the ARTIFACT
> rather than the control flow … That catches every degrade path at once, including ones added later, and
> cannot be bypassed by a new early `return` upstream."*

**Two gaps, both narrow:**

- **Coverage:** the manifest holds 6 PQ `*_real_*` symbols. `grain_r3_verify`, `cross_cell_conserves`,
  `constraint_admits`, `holding_grant_weight`, `interchain_reached_consensus`, `finalize_gate`,
  `storage_content_root` have **no build-time enforcement** — `build.rs:2225`, `:2244`, `:2259` are bare
  `if present { println!(…) }` with no `else`.
- **Arming:** `require_pq_cores = require_pq_on || (require_lean_native && !require_pq_off)`
  (`build.rs:2142`), and `require_lean_native` needs `--release`. **`cargo test` is debug — the gate is off
  in exactly the configuration that produces the vacuous green.**

### 5.2 Recommendation (not implemented here)

**Preferred — extend the existing artifact-probe manifest.** Cheapest and most robust: the mechanism,
the message style, and the opt-out convention already exist; this is adding rows and widening one
condition, not new machinery.

1. **Widen the manifest** from the 6 PQ cores to all symbols whose absence silently swaps a *verified
   decision* for a Rust twin: `+grain_r3_verify, +cross_cell_conserves, +constraint_admits,
   +holding_grant_weight, +interchain_reached_consensus, +finalize_gate, +storage_content_root`.
   Keep `direct` (perf-only) and `handler` (documented non-load-bearing) out — those are the *legitimately
   optional* exports, and the manifest must distinguish "optional" from "absent" or it will be turned off.
2. **Arm it in test profiles too**, keyed on the existing `DREGG_TEST_REQUIRE_LEAN` rather than `PROFILE`,
   so CI's debug `cargo test` lane is covered without making every developer debug build fail.
3. **Fix Generator B independently of the manifest**: make `archive_has_dregg2` a *completeness* check
   (does the archive contain every member named in `expected`, `build.rs:513`) instead of an existence
   check, or simply force `needs_splice = true` whenever `seed_build_archive` actually copied. The current
   existence check is the specific defect.
4. **Do not** convert the cfg-gated modules to runtime-asserting as the primary fix. It is more invasive
   (the `extern "C"` blocks genuinely cannot exist without the symbol — that is what the cfg is *for*), it
   would require a link-time stub for every export, and it fixes only the test-visibility symptom while
   leaving the deployed binary silently degraded. Runtime asserting is the right shape only for the
   *runtime* self-skip sites (§2.3), where the tool is `demand_lean` and the work is wiring, not design.
5. **Register the vanishing tests as falsifiers** (see §6) so "0 tests ran" becomes structurally red.

**Legitimate configurations that must keep working**, and how each survives: `wasm32`/`no-lean-link`
builds (platform gate returns at `build.rs:1690`, before the manifest); `sdk-py`'s `light` feature;
deliberately core-less dev builds (`DREGG_REQUIRE_PQ_CORES=0`); bare-metal sel4 targets. All four are
already handled by the existing gate's structure — which is the strongest argument for extending it
rather than inventing a parallel mechanism.

### 5.3 Owner

**This is `dregg-lean-ffi`'s build script and is not ours to change unilaterally.** Recent authorship of
`dregg-lean-ffi/build.rs` is the verified-PQ-cores / reality-gate lane:

```
7ebe7b7d4b  no-silent-fallback: two gates make unaudited PQ substitution IMPOSSIBLE …
88d7e3f82d  ML-DSA-65 keygen VERIFIED core dispatched …
fbe236f32b  THE REALITY-GATE: one Lean constraint evaluator, @[export]'d …
ecdec12b91  lean-ffi: the archive trim silently NO-OPPED on every Linux/CI build …
8f14676c32  lean-ffi: re-splice the closure after an out-of-band re-seed …
```

That lane authored the `DREGG_REQUIRE_PQ_CORES` gate and has already fixed two adjacent silent-no-op bugs
(`ecdec12b91`, `8f14676c32`). The seed/CI plumbing (`lean-seed.yml`, `fetch-lean-seed.sh`) is the same
lane's (`227853b8bd`, `3891f5e990`). **Route both the manifest widening and the `archive_has_dregg2` fix
there.** The `#[cfg]` inventory and the `demand_lean` wiring in `grain-verify`/`dregg-pq`/`bridge`/`sdk`
are separable and can go to those crates' owners.

---

## 6. Prior art — the canary pattern exists, in three forms

**Yes, and the repo already has the right shape in three places. None of them is currently pointed at
FFI export vacuity.**

**(a) The canary doctrine — `scripts/check-mirror-gates.sh` + `scripts/mirror-gates/canary.sh`.**
The doctrine is stated exactly as reported:

> *"THE GATE ITSELF IS GATED: `canary.sh` reintroduces a known mirror per gate and requires each to go RED
> naming both sites, then GREEN once removed. … **a gate that cannot bark is worse than none**, so CI runs
> the canary FIRST and refuses to trust a silent gate."* — `scripts/check-mirror-gates.sh:19-23`

> *"A falsifier that was never red proves nothing."* — `scripts/mirror-gates/canary.sh:11`

`canary.sh` also carries a `canary/clean/` false-positive half. This is the correct pattern and it is
**mirror-specific — there is no FFI-export equivalent.**

**(b) The anti-vacuity instrument — `scripts/ci-invariants.sh:186-193`**, which reds on exactly the
symptom in this report:

```bash
elif grep -Eq "test .*${fn}[^A-Za-z0-9_]* \.\.\. ok" "$log" && [ "$rc" -eq 0 ]; then
  ok "$crate :: $fn"
else
  bad "$crate :: $fn — DID NOT RUN (filtered to zero, compile error, or the binary aborted)."
```

**It is the right tool and it is not aimed here.** `scripts/ci-invariants/falsifiers.tsv` has 62 rows and
**no `dregg-lean-ffi` row**. Its one Lean-adjacent row is a trap worth naming:

```
dregg-coord  test:twin_fail_closed  twoc_pc_fails_closed_without_gate
             twin#3 coord 2PC fails closed (Abort) when the verified Lean gate is absent
```

That falsifier asserts the **absent-gate** behaviour — so it is green *precisely in the broken
configuration*. It is not a catcher for this hazard; it is a test of the degraded path.

**(c) An `nm` export check already exists — but only on the producer side.** `lean-seed.yml:200-213`
refuses to *publish* a seed missing any of ~10 named exports:

```yaml
*) echo "::error::archive lacks the verified-executor export '$sym' — refusing to publish a seed
     that fetch-lean-seed.sh would reject."; exit 1 ;;
```

**So the repo already knows how to do this — it checks exports when publishing a seed, but not when
consuming one.** Combined with `build.rs:2143`'s artifact-probe manifest and `demand_lean`'s runtime
assert, all three layers of the correct fix exist in-tree and are simply not wired to these 24 symbols.
The recommendation in §5.2 is therefore **coverage work, not design work** — which is the cheapest
possible form this fix could take.

---

## 7. What would falsify this assessment

Stated so the next lane can check rather than re-derive:

- Any CI log showing `cargo:rustc-cfg=lean_lib_present` emitted on a hosted runner would refute §1.
- A `git ls-files` hit for a `.a` under `dregg-lean-ffi/` would refute §1.1.
- A `lean-seed` release asset matching the current `scripts/lean-seed-key.sh` output would mean the two
  seed-consuming lanes are armed and §1.5 is stale.
- `cargo test -p dregg-lean-ffi --lib` reporting 20 passed (not 11) on a given host means that host's
  archive is fully spliced and §2.1's count does not apply there.

**No claim here rests on a build.** The `nm` counts in §4 are reproducible from the archives on disk with
the command given at the top of that section.
