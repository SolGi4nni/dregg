// build.rs — wire the Rust binary to the compiled Lean kernel + Lean runtime.
//
// We link against:
//   * libdregg_lean.a — a single static archive of the native objects emitted by the
//     Lean compiler for `Dregg2.Exec.FFI` and its ENTIRE transitive dependency
//     closure (Dregg2 modules + mathlib + batteries + aesop + Qq + … — ~8200 .o).
//     The SEED archive lives next to this build.rs at `dregg-lean-ffi/libdregg_lean.a`;
//     it was produced by compiling each module's `.c` (lake's `:c` facet) with
//     `leanc -c` and archiving with `llvm-ar` (see `scripts/seed-dregg2-closure.sh`).
//
//     ⚠ THE SEED IS **NOT** IN THE REPOSITORY. `dregg-lean-ffi/.gitignore:7` ignores
//     `*.a` and `git log -- dregg-lean-ffi/libdregg_lean.a` is EMPTY: the file has
//     never been tracked. (This header claimed "git-tracked" until 2026-07-24; several
//     warning strings below still say "no git-tracked seed" and mean the same thing —
//     no seed on disk.) A fresh checkout — every GitHub-hosted runner included — has
//     NO archive, so the `!build_archive.exists()` guard in `main` fires and this
//     script returns BEFORE emitting a single `cargo:rustc-cfg`. Get one with
//     `scripts/fetch-lean-seed.sh` (prebuilt, minutes) or `./scripts/bootstrap.sh`
//     (from source, hours). See `docs/ASSESS-cold-build-silent-export.md`.
//
// ── SWARM-SAFE ARCHIVE (the per-OUT_DIR working copy) ──
// The seed `libdregg_lean.a` is treated as a READ-ONLY SEED. A `cargo build`
// NEVER mutates it. Instead, each build copies the seed into a per-`OUT_DIR` working
// archive (`$OUT_DIR/libdregg_lean.a`) and does its splice → closure-completion →
// reachability-GC against THAT copy, then links against it. Because `OUT_DIR` is
// per-(crate, feature-set, profile) — cargo's own fingerprint dir — concurrent lanes
// with DIFFERENT feature sets each splice/prune their OWN archive and never tear a
// shared file. (Before this split the shared seed was rewritten from every build
// script invocation: two concurrent multi-feature lanes raced it into a torn /
// wrong-feature archive → `Undefined symbols: _initialize_Dregg2_*` across the swarm.)
// The seed is (re)produced ONLY out-of-band by `scripts/seed-dregg2-closure.sh` /
// `scripts/rebuild-dregg2-closure.sh` — never by a `cargo build`.
//   * the Lean runtime + stdlib in the elan toolchain `lib/lean` dir — STATIC by default
//     (leancpp/Init/Std/Lean/leanrt + gmp/uv/c++), or SHARED (libleanshared + Lake_shared)
//     when `DREGG_LEAN_LINK=shared` (the cdylib link mode, see `shared_link_mode`).
//
// Toolchain paths are discovered from `lake env` (LEAN_SYSROOT) with a fallback to the
// pinned elan toolchain, so this stays robust to elan being on PATH.

use std::path::{Path, PathBuf};
use std::process::Command;

mod build_parallel;

// ── THE REQUIRED-EXPORT MANIFEST ────────────────────────────────────────────────────────────
// The symbols whose ABSENCE silently swaps a Lean-PROVEN decision for an unverified Rust twin (or
// an unaudited crate). "the archive links" is NOT evidence that any of them is there — every
// on-disk seed measured before 2026-07-29 exports NONE of them (`nm`: 126-142 `dregg_*` exports,
// of which only `dregg_captp_validate_handoff`, `dregg_coord_2pc_decide` and
// `dregg_exec_full_forest_auth_direct` are on this list's radar).
//
// ⚑ THAT WAS CALLED "SPLICE-ONLY" HERE AND IN `docs/ASSESS-cold-build-silent-export.md` §4, AND
// IT WAS THE WRONG READING — corrected 2026-07-29. Nothing about these symbols makes them
// unseedable. `scripts/bootstrap.sh`, `dregg-lean-ffi/scripts/seed-dregg2-closure.sh` and
// `scripts/lean-ffi-closure.py` each `lake build`-ed a hand-maintained NINE-ROOT list that was a
// strict subset of `Dregg2/FFI.lean`'s closure — 95 modules short, every one of them a decision
// module — so a seeding host emitted no `:c` facet for them and no seed could carry them however
// often it was regenerated. All three now build the one boundary root, and `lean-seed.yml` scrapes
// THIS manifest to refuse publishing a seed that lacks any of it. A future seed carries them; the
// already-published assets do not, and a build against one is a fully disarmed build.
//
// The manifest is the ARTIFACT-PROBED gate: it re-reads the archive we are actually about to link
// instead of trusting control flow, which catches every degrade path at once (including ones added
// later) and cannot be bypassed by a new early `return` upstream. It is used TWICE:
//
//   * BEFORE the splice — `archive_dregg2_complete` makes a missing export force `needs_splice`,
//     so a warm `.o` cache can never leave a freshly re-seeded archive un-spliced (see that fn).
//   * AFTER the splice — the `DREGG_REQUIRE_PQ_CORES` / `DREGG_REQUIRE_VERIFIED_EXPORTS` gates
//     below turn a missing export into a hard build FAILURE when armed.
//
// DELIBERATELY NOT ON THE LIST (they are the legitimately-optional exports, and a manifest that
// cannot distinguish "optional" from "absent" is a manifest someone turns off):
//   * `dregg_exec_handler_turn`   — has its OWN require_lean_native panic at the probe site.
//   * `dregg_exec_full_forest_auth_direct` — PERF only; absent ⇒ the JSON marshalling path, same
//     verified decision. (It is in the seed anyway.)

/// The verified post-quantum CORES. Absent ⇒ `dregg-pq` answers with an UNAUDITED crate.
/// Gate: `DREGG_REQUIRE_PQ_CORES` (opt-out `=0`).
const REQUIRED_PQ_CORE_EXPORTS: &[(&str, &str)] = &[
    (
        "dregg_fips204_verify_real",
        "ML-DSA-65 verify would be answered by the UNAUDITED `fips204` 0.4 crate",
    ),
    (
        "dregg_fips204_sign_real",
        "ML-DSA-65 sign would be answered by the UNAUDITED `fips204` 0.4 crate",
    ),
    (
        "dregg_mlkem_encaps_real",
        "ML-KEM-768 encaps would be answered by the UNAUDITED `ml-kem` 0.2.3 crate",
    ),
    (
        "dregg_mlkem_decaps_real",
        "ML-KEM-768 decaps would be answered by the UNAUDITED `ml-kem` 0.2.3 crate",
    ),
    (
        "dregg_mlkem_keygen_real",
        "ML-KEM-768 keygen would be answered by the UNAUDITED `ml-kem` 0.2.3 crate",
    ),
    (
        "dregg_mldsa_keygen_real",
        "ML-DSA-65 IDENTITY keygen would be answered by the UNAUDITED `fips204` 0.4 crate",
    ),
];

/// The verified DECISION exports — every one gates a `#[cfg(dregg_*_present)]` bridge whose absent
/// arm reverts a proven verdict to a Rust twin, a fail-closed refusal, or (worse) a test module
/// that simply ceases to exist. Gate: `DREGG_REQUIRE_VERIFIED_EXPORTS` (opt-out `=0`).
const REQUIRED_DECISION_EXPORTS: &[(&str, &str)] = &[
    (
        "dregg_grain_r3_verify",
        "the R3 whole-history verdict loses its ONLY anti-forgery teeth (the 8-lane width \
         ~2^31-grind falsifier and the anti-self-anchor tooth compile out entirely)",
    ),
    (
        "dregg_cross_cell_conserves",
        "the per-asset Σδ=0 conservation ORACLE is uninstallable — hidden mint/burn detection \
         reverts to the hand-written Rust `BlockConservation` twin",
    ),
    (
        "dregg_constraint_admits",
        "deployed-constraint admission stays on the Rust guest-path evaluator",
    ),
    (
        "dregg_holding_grant_weight",
        "the non-custodial proof-of-holdings → governance-weight verdict is unverifiable",
    ),
    (
        "dregg_interchain_reached_consensus",
        "the bridge-trust verdict is unverifiable (both polarities go untested)",
    ),
    (
        "dregg_eth_lc_verify",
        "the ETHEREUM light-client verify gate compiles out — `eth_lc_verify_available()` goes \
         constantly false and every ETH verify entry point REFUSES (fail-closed, no twin): \
         sync-committee quorum, branch depth and the BLS/SHA-256 result bits get no verdict at \
         all rather than an unverified one",
    ),
    (
        "dregg_eth_committee_rotation",
        "the ETHEREUM COMMITTEE-ROTATION gate compiles out — `verify_committee_update` REFUSES, \
         so the light client's TRUSTED SYNC COMMITTEE (its trust root, not just its chain view) \
         cannot advance at all. Absent, `WeakSubjectivityStore::bootstrap_committee`/`advance` \
         fail closed; present, the 5|6 depth admissibility and the reconstruction compose in \
         `committeeRotationDecision`, not in Rust",
    ),
    (
        "dregg_tm_lc_verify",
        "the TENDERMINT/COSMOS ADJACENT-advance gate compiles out — `cosmos_lightclient::\
         verified_gate::available()` goes constantly false and `verify_cosmos_header` REFUSES \
         every adjacent header with `HeaderVerifyError::VerifiedGateUnavailable` (fail-closed, no \
         twin): the strict `2·tot < 3·sp` stake threshold, the chain-id match, the trusting window \
         and the `next_validators_hash` epoch binding get no verdict at all rather than an \
         unverified one. (ROUTED 2026-07-29. The prior note here — `NOTHING OUTSIDE THIS CRATE \
         CALLS IT`, absence consequence `no change` — was accurate for ~5 months and is what this \
         entry now records as closed.)",
    ),
    (
        "dregg_tm_skip_verify",
        "the TENDERMINT/COSMOS NON-ADJACENT (skipping) gate compiles out — \
         `verify_cosmos_header` REFUSES every skip with `HeaderVerifyError::\
         VerifiedGateUnavailable`, so a light client can only advance block-by-block. Absent, the \
         trust-OVERLAP threshold (strictly more than `trust_threshold` of the TRUSTED epoch's \
         power signed the target) gets no verdict; present, it composes in `tmSkipVerifyDecision`, \
         not in Rust. Probed INDEPENDENTLY of `dregg_tm_lc_verify`: an archive spliced before \
         2026-07-29 exports the adjacent gate and NOT this one",
    ),
    (
        "dregg_mpt_lc_verify",
        "the EVM state-inclusion (EIP-1186) verify gate compiles out — `verify_erc20_holding` \
         REFUSES every holding (`Erc20ProofError::VerifiedGateUnavailable`), so the Nomad-law \
         nonzero-balance floor and the state-root/token/slot anchor bindings get no verdict at all \
         rather than an unverified one (the Rust `&&`-composition that used to decide them was \
         deleted, `eth-lightclient/src/evm.rs`)",
    ),
    (
        "dregg_blocklace_finalize",
        "the finality + τ-order gate compiles out and the node runs the un-gated path",
    ),
    (
        "dregg_storage_content_root",
        "the verified content-root is 100% invisible (this flag has NO `cfg(not(...))` arm \
         anywhere, and the `#[used]` Poseidon2 linker anchor disappears with it)",
    ),
    (
        "dregg_strand_admit",
        "federation admission falls back to the seeds-only Rust gate",
    ),
    (
        "dregg_captp_validate_handoff",
        "SIX verified gates go at once (CapTP handoff/GC-drop/pipeline + coord 2PC/causal/\
         shared-budget); the 2PC decider silently reverts on the live coordinator path",
    ),
    (
        "dregg_decide_refines",
        "the deploy refinement gate falls back to its in-process σ-free mirror",
    ),
    (
        "dregg_fips204_verify",
        "the verified ML-DSA verify core is unexercised (the tampered-c̃ / out-of-range-z \
         assertions compile out)",
    ),
    (
        "dregg_fips204_sign",
        "the verified ML-DSA sign core is unexercised (the sign→verify round-trip compiles out)",
    ),
    (
        "dregg_fips203_encaps",
        "the verified ML-KEM encaps core is unexercised (the KEM round-trip compiles out)",
    ),
    (
        "dregg_fips203_decaps",
        "the verified ML-KEM decaps core is unexercised (the implicit-reject divergence \
         assertion compiles out)",
    ),
    (
        "dregg_automatafl_rules",
        "the automatafl GAME ORACLE compiles out: board resolution, move legality, the conflict \
         set and the win have no answer source at all, so `dregg-automatafl` cannot fill a \
         witness or run a match (there is no Rust twin left to fall back to — `reference.rs` was \
         DELETED because it carried the non-canonical experiment's 2-cycle and path-check bugs)",
    ),
    (
        "dregg_multiway_tug_rules",
        "the multiway-tug RULES ORACLE compiles out: row control, the tallies, the ADJUDICATED \
         round winner and the CLAUSE of the terminal rule that named it have no answer source at \
         all, so `dregg-multiway-tug` cannot score a round — `Engine::score` returns `Err` and the \
         surface refuses the turn. There is NO Rust twin left to fall back to: `winner_of` was the \
         model's `roundWinner` truncated to its two threshold branches (it answered 'no winner' on \
         every sub-threshold round the model adjudicates, `undecidedState_adjudicates`, for a \
         MEASURED 78.5% played draw rate against 5.1%) and it is DELETED",
    ),
    (
        "dregg_deleg_admit",
        "the DELEGATED TOOL/MCP-ACCESS admission verdict has no answer source: the SDK tool \
         gateway, the starbridge tool-access-delegation app and the dreggnet offerings session \
         all REFUSE every invocation (fail-closed). There is no Rust twin left to fall back to — \
         all three hand-maintained `deleg_admit`/`play_admit` re-implementations were DELETED when \
         the decision was routed to `Dregg2.Apps.DelegAdmit.delegAdmit`, the predicate \
         `tool_invocation_commit_iff_admit` and its three rejection teeth are proven over",
    ),
    (
        "dregg_mina_lc_verify",
        "the MINA (Ouroboros Samasika) anchored-segment gate compiles out — \
         `mina_lc_verify_available()` goes constantly false and `MinaObserver::observe_settlement` \
         returns `ObserveError::VerifiedGateUnavailable` for EVERY settlement, so Mina cannot \
         settle at all. Fail-closed with NO Rust twin: the non-empty segment, the anchor-below-tip \
         ordering and the WITNESSED confirmation depth get no verdict rather than an unverified one",
    ),
    (
        "dregg_mina_wrap_shape_ok",
        "the PER-BLOCK Pickles Wrap-proof PREAMBLE gate compiles out — the observer refuses every \
         settlement rather than reverting to the `NEUTRAL_PICKLES_OK = true` constant it retired, \
         so the block's own proof shape (`KimchiVerify.shapeOkRec` plus the two length agreements a \
         RECURSIVE Wrap proof owes) is never checked",
    ),
    (
        "dregg_mina_proof_chain_ok",
        "the PER-ADJACENT-PAIR Pickles PROOF-CHAIN gate compiles out — the observer refuses every \
         settlement rather than admitting an unbound proof, so the ONE binding a served Wrap proof \
         has to anything outside its own bytes (block N's proof names block N-1's `sg` and its 16 \
         IPA challenges) is never checked, and one real Mina proof replayed under a whole \
         fabricated segment would pass every remaining check",
    ),

    (
        "dregg_mina_state_hash_word_ok",
        "the PER-BLOCK proof↔`stateHash` DERIVATION compiles out — the observer refuses every \
         settlement rather than admitting a header it never hashed, so public-input words 11 and \
         12 (the 93-element Poseidon over `[VK ‖ state_hash ‖ accumulators]`, the ONLY place the \
         served block enters a Wrap verification) are never computed from the served header",
    ),
    (
        "dregg_mina_better_tip",
        "the SAMASIKA FORK-CHOICE decision compiles out — `verified_mina_better_tip` returns `Err` \
         for every pair, so the client keeps whatever tip it already holds and cannot choose \
         between two equally-valid k-deep segments under different anchors. There is NO Rust twin \
         and there must not be one: a hand-written `select` is the drift this gate deletes, and the \
         pre-gate behaviour was asking a peer's `bestChain` which chain it liked",
    ),
    (
        "dregg_mina_head_advance",
        "the ROLLING VERIFIED HEAD compiles out — `verified_mina_head_advance` returns `Err`, the \
         persisted head never moves and the FINALIZED height never rises, so the client degrades \
         from following a chain to verifying whatever segment it is handed. Fail-closed and \
         stalled, which is the refusal: a client that guesses its own head is silently forked",
    ),
    (
        "dregg_mina_checkpoint_advance",
        "the PER-CHECKPOINT LOOP compiles out — the two-tier head has no verdict, so a client can \
         only fall back to per-block verification it cannot afford or to a single-tier head whose \
         ratchet moves on CHEAP checks alone. The theorem that is lost is the one the whole cadence \
         design rests on (`provisional_never_ratchets`: a block accepted between checkpoints \
         CANNOT raise the finalized height), and with it the density window re-derived from the \
         parent rather than bound-checked from the served value",
    ),
    (
        "dregg_mina_wrap_challenges",
        "the PER-BLOCK Wrap CHALLENGE DERIVATION compiles out — `mina_opening_check.rs` is back to \
         `PINNED_CHALLENGES`' ONE height (devnet 539508) and returns `ChallengesUnavailable` for \
         every other block, so no checkpoint at any cadence can be verified. Fail-closed with NO \
         Rust twin and there must not be one: a Rust Fq-sponge is a re-rendering of a transcript, \
         i.e. of the meaning of `these are the proof's own challenges`",
    ),
    (
        "dregg_mina_wrap_ft_eval0",
        "the PER-BLOCK `ft_eval0` DERIVATION compiles out — the linearization constant term goes \
         back to being a CARRIER, so neither `public_comm` nor `cipShifted` can be computed and \
         `dregg_mina_wrap_challenges` above has two arguments nobody can supply. Fail-closed with \
         NO Rust twin and there must not be one: the six gate constraint bodies ARE the circuit's \
         meaning, and a Rust rendering of them would carry no proof and no differential",
    ),
];

/// One bounded worker budget for every independent `leanc` phase.  The env
/// override is intentionally shared: operators should not have to discover
/// that the initial Dregg2 facets parallelise while closure completion remains
/// a serial, single-core tail.
/// The jobs flag THIS `lake` actually understands, or `None` — a SECONDARY cap, kept for the day a
/// future lake grows one back. The cap that actually applies today is the `LEAN_NUM_THREADS` task
/// pool (`build_parallel::LAKE_FANOUT_ENV`); neither toolchain on this box has a jobs flag at all.
///
/// Lake's job control has moved across versions (`-j`/`--jobs` existed, then did not); passing a
/// flag the binary rejects turns `lake build` into an immediate hard failure rather than a bounded
/// one. Probe `lake help` once and believe it. `DREGG_LAKE_JOBS_FLAG` overrides (empty ⇒ none).
///
/// ⚠ PROBE THE LAKE THAT WILL RUN. `lake` is an elan proxy: the toolchain it resolves comes from the
/// CWD's `lean-toolchain`, so probing from the build script's own directory asks the elan DEFAULT
/// (here Lake 5.0.0-src+f054605 / Lean 4.32.1) while the build itself runs in `metatheory/` under
/// that directory's pin (Lake 5.0.0-src+d024af0 / Lean 4.30.0). Two different binaries. Hence `meta`.
fn lake_jobs_flag(meta: &Path) -> Option<String> {
    if let Ok(explicit) = std::env::var("DREGG_LAKE_JOBS_FLAG") {
        let trimmed = explicit.trim();
        return if trimmed.is_empty() {
            None
        } else {
            Some(trimmed.to_string())
        };
    }
    let help = Command::new("lake")
        .arg("help")
        .current_dir(meta)
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&help.stdout);
    // Only a line that DOCUMENTS jobs counts. Substring-matching the raw help is a trap: `-j` is a
    // substring of `--json`, which every lake has, so a naive `text.contains("-j")` "finds" a jobs
    // flag on a lake that has none — and then passes it, and then every `lake build` dies with
    // `unknown short option '-j'`. That is the exact bug this probe exists to prevent.
    for line in text.lines() {
        if !line.to_ascii_lowercase().contains("jobs") {
            continue;
        }
        if line.contains("--jobs") {
            return Some("--jobs".to_string());
        }
        if line
            .split(|c: char| c.is_whitespace() || c == ',' || c == '=')
            .any(|tok| tok == "-j")
        {
            return Some("-j".to_string());
        }
    }
    None
}

/// Report what the fan-out cap ACTUALLY did, and bark if it did nothing.
///
/// This is the teeth. The regression it exists to catch is not "the build was slow", it is "a
/// containment knob was passed for 95 minutes while bounding nothing, and no one could tell from the
/// outside". A cap that cannot report on itself is the same failure waiting for the next toolchain
/// bump, so every build now measures the children `lake` spawned and says which of three things
/// happened: the bound held, the bound DID NOT APPLY, or this host could not be measured.
fn report_lake_fanout(run: &build_parallel::BoundedRun, budget: usize) {
    match build_parallel::fanout_verdict(run.peak_children, budget) {
        // Nothing to bound (warm/no-op build) or bounded as asked: silent. Cargo warnings are a
        // scarce channel; spending one on "everything is fine" is how the real ones get missed.
        build_parallel::FanoutVerdict::Held { .. } => {}
        build_parallel::FanoutVerdict::Exceeded { peak, budget } => println!(
            "cargo:warning=dregg-lean-ffi: ⚠ THE LEAN BUILD FAN-OUT CAP DID NOT APPLY — asked for \
             {budget} concurrent `lean` processes via {env}, measured {peak}. This `lake` no longer \
             takes its job-pool size from {env}, so `lake build` is running UNBOUNDED (one `lean` \
             per ready module, GBs each: the 2026-07-25 stampede was 55 jobs / ~35 GB / 54 GB of \
             swap). Re-measure the mechanism for this toolchain before running a cold closure — see \
             build_parallel::LAKE_FANOUT_ENV for the measurement harness — and until then bound the \
             build from outside (cgroups / `swarm-build` on hbox).",
            env = build_parallel::LAKE_FANOUT_ENV,
        ),
        build_parallel::FanoutVerdict::Unverified => println!(
            "cargo:warning=dregg-lean-ffi: the Lean build fan-out cap ({env}={budget}) was applied \
             but could NOT be verified on this host (no `pgrep` to count `lake`'s children). It is \
             an unchecked knob here — exactly the state that let a broken `-j` bound nothing for 95 \
             minutes — so prefer external containment for a cold closure.",
            env = build_parallel::LAKE_FANOUT_ENV,
        ),
    }
}

fn configured_leanc_workers() -> usize {
    let available = std::thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(4);
    let override_value = std::env::var("DREGG_LEANC_JOBS").ok();
    build_parallel::worker_count(override_value.as_deref(), available)
}

/// Replay captured compiler diagnostics only after the parallel phase joins,
/// in input order.  This keeps build logs deterministic instead of letting
/// multiple `leanc` children interleave bytes on stderr.
fn emit_command_diagnostics(output: &std::io::Result<std::process::Output>) {
    match output {
        Ok(output) => {
            for line in String::from_utf8_lossy(&output.stdout).lines() {
                println!("cargo:warning=dregg-lean-ffi: leanc stdout: {line}");
            }
            for line in String::from_utf8_lossy(&output.stderr).lines() {
                println!("cargo:warning=dregg-lean-ffi: leanc stderr: {line}");
            }
        }
        Err(error) => println!("cargo:warning=dregg-lean-ffi: could not launch leanc: {error}"),
    }
}

// ── ARCHIVE-TOOL NAMES (the binutils trio) ──────────────────────────────────────
// The archive splice / closure-completion / reachability-GC below shell out to the
// `ar` / `nm` / `ranlib` trio. On macOS / Linux these resolve to the host binutils
// (or their llvm aliases) on PATH — UNCHANGED. On Windows the Lean toolchain is the
// LLVM-MinGW distribution (`x86_64-w64-windows-gnu`): its archives are GNU `.a` of
// `coff-x86-64` objects, read/written by `llvm-ar` and inspected by `llvm-nm` (plain
// `ar`/`nm`/`ranlib` are not on a stock Windows PATH). These helpers centralise the
// name so every `Command::new(ar_tool())` etc. picks the right binary per-OS. On
// non-Windows they return exactly `"ar"`/`"nm"`/`"ranlib"`, so the unix paths are
// byte-identical to before. See `windows_gnu_link_env` for the matching link arm.
fn ar_tool() -> &'static str {
    if cfg!(windows) {
        "llvm-ar"
    } else {
        "ar"
    }
}
fn nm_tool() -> &'static str {
    if cfg!(windows) {
        "llvm-nm"
    } else {
        "nm"
    }
}

/// Split one `nm -A <archive>` row into `(member, symbol columns)` without
/// assuming one platform's archive spelling.  The three forms we encounter are:
///
/// * GNU nm:       `<archive>:<member.o>:<addr> T symbol`
/// * BSD/llvm-nm:  `<archive>:<member.o>: <addr> T symbol`
/// * bracket form: `<archive>[<member.o>]: <addr> T symbol`
///
/// The old `split_once(": ")` parser accepted only the latter two.  On GNU nm it
/// silently skipped every DEFINED row (there is no space after the member's
/// colon), so archive GC/runtime trimming became a no-op on Linux build hosts.
fn nm_archive_member_row(line: &str) -> Option<(String, &str)> {
    let obj_end = line.find(".o")? + 2;
    let prefix = &line[..obj_end];
    let member_start = prefix
        .rfind(['/', ':', '['])
        .map(|index| index + 1)
        .unwrap_or(0);
    let member = &prefix[member_start..];
    if !member.ends_with(".o") {
        return None;
    }
    let rest = line[obj_end..]
        .strip_prefix(']')
        .unwrap_or(&line[obj_end..])
        .strip_prefix(':')?
        .trim_start();
    Some((member.to_string(), rest))
}

const LEAN_INIT_PREFIXES: [&str; 3] = ["initialize_", "runtime_initialize_", "meta_initialize_"];

fn lean_init_suffix(symbol: &str) -> Option<&str> {
    LEAN_INIT_PREFIXES
        .iter()
        .find_map(|prefix| symbol.strip_prefix(prefix))
}
/// `ranlib` regenerates an archive's symbol index. `llvm-ar` writes the index on
/// every `rcs`/`r` op (and `llvm-ranlib` may not be on PATH), so on Windows we run
/// `llvm-ar s <archive>` — the explicit "regenerate symbol table" op — instead.
fn run_ranlib(archive: &Path) -> std::io::Result<std::process::ExitStatus> {
    if cfg!(windows) {
        Command::new(ar_tool()).arg("s").arg(archive).status()
    } else {
        Command::new("ranlib").arg(archive).status()
    }
}

/// Locate the project's `metatheory` Lean directory relative to this crate, so
/// `lake env` runs against the project's pinned toolchain regardless of the host
/// (no hardcoded absolute paths — works on macOS dev boxes and the Linux deploy
/// box alike). `CARGO_MANIFEST_DIR` is `.../dregg-lean-ffi`; the sibling is
/// `.../metatheory`. An explicit `DREGG_METATHEORY_DIR` override wins if set.
fn metatheory_dir() -> Option<PathBuf> {
    // ⚑ RESTORED 2026-07-25. Dropped by 7ebe7b7d4b (a build.rs rewrite whose subject was PQ
    // substitution) along with DREGG_LEAN_SYSROOT's and DREGG_LEAN_FFI_NO_ARCHIVE_GC's. Cargo
    // auto-tracks only env read through the `env!`/`option_env!` MACROS; a runtime
    // `std::env::var` is invisible to it, and this script already declares SOME
    // `rerun-if-env-changed`, which replaces the default heuristic with exactly the declared
    // set. Without this line, repointing the build at another metatheory checkout does NOT
    // re-run build.rs: every `archive_exports` verdict and every `dregg_*_present` cfg stays
    // CACHED from the previous tree — the failure mode being a build that silently keeps the
    // old tree's gate decisions. Same convention as `shared_link_mode`: declared where it is read.
    println!("cargo:rerun-if-env-changed=DREGG_METATHEORY_DIR");
    if let Ok(dir) = std::env::var("DREGG_METATHEORY_DIR") {
        let p = PathBuf::from(dir);
        if p.join("lean-toolchain").exists() {
            return Some(p);
        }
    }
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let candidate = crate_dir.parent().map(|p| p.join("metatheory"));
    candidate.filter(|p| p.join("lean-toolchain").exists())
}

fn lean_sysroot() -> Option<PathBuf> {
    // Prefer `lake env` (authoritative for the project's toolchain). `DREGG_LEAN_SYSROOT`
    // overrides for environments where `lake` is not on PATH at build time.
    // ⚑ RESTORED 2026-07-25 (dropped by 7ebe7b7d4b — see `metatheory_dir`). This one is the
    // sharpest of the three: the sysroot decides whether `lean_lib_present` is emitted AT ALL,
    // so an untracked change to it can leave a build linked against one toolchain while every
    // cached probe verdict describes another.
    println!("cargo:rerun-if-env-changed=DREGG_LEAN_SYSROOT");
    if let Ok(s) = std::env::var("DREGG_LEAN_SYSROOT") {
        if !s.trim().is_empty() {
            return Some(PathBuf::from(s.trim()));
        }
    }
    if let Some(meta) = metatheory_dir() {
        if let Ok(out) = Command::new("lake")
            .args(["env", "printenv", "LEAN_SYSROOT"])
            .current_dir(&meta)
            .output()
        {
            let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
            if !s.is_empty() {
                return Some(PathBuf::from(s));
            }
        }
    }
    None
}

/// The Lean module an emitted IR `.c` belongs to: `<ir>/Dregg2/Exec/FFI.c` → `Dregg2.Exec.FFI`.
fn module_name_of_ir_c(ir_root: &Path, c: &Path) -> Option<String> {
    let rel = c.strip_prefix(ir_root).ok()?;
    Some(
        rel.with_extension("")
            .components()
            .map(|comp| comp.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("."),
    )
}

/// The transitive `import` closure of `metatheory/Dregg2/FFI.lean` — THE Lean⟷Rust boundary module.
///
/// This is the set of modules whose compiled objects belong in the runtime archive. We walk the
/// `.lean` sources rather than asking Lake, because it must work from a build script with no
/// toolchain round-trip and because the answer is exactly a text-level import graph. Modules that
/// resolve to no source file in `metatheory/` (Mathlib, Batteries, Std, …) are recorded and their
/// edges are not followed: they are not ours to splice, and `complete_initializer_closure` pulls
/// back whichever of them the spliced objects actually reference.
///
/// `None` means the boundary file could not be read at all — callers fall back to the old
/// splice-everything behaviour rather than shipping an under-populated archive.
fn boundary_closure(meta: &Path) -> Option<std::collections::HashSet<String>> {
    let root = "Dregg2.FFI".to_string();
    let source_of = |module: &str| -> PathBuf {
        let mut p = meta.to_path_buf();
        for seg in module.split('.') {
            p.push(seg);
        }
        p.set_extension("lean");
        p
    };
    // The boundary module itself must exist; anything less is a misconfigured tree, not a closure.
    std::fs::read_to_string(source_of(&root)).ok()?;

    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![root];
    while let Some(module) = stack.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(source_of(&module)) else {
            // Out-of-tree (dependency package or toolchain): recorded, edges not followed.
            continue;
        };
        for line in text.lines() {
            // Imports precede every declaration in Lean, but a doc block may mention the word;
            // only a line whose FIRST token is `import` (optionally qualified) is one.
            //
            // ⚑ THE GRAMMAR MUST MATCH `scripts/lean-ffi-closure.py`, which walks this SAME
            // import graph to pick the seed archive's members. This is the third walk of one
            // graph (Python for the seed cut, Python again for `scripts/check-lean-seed-
            // closure.sh`, Rust here for the splice filter), and a form one accepts and another
            // drops is a module whose object the seed carries and the splice never refreshes —
            // silently stale, and green. Until 2026-07-30 this side accepted only
            // `import` / `meta import` / `public import`; `private import` was dropped outright
            // and `import all Foo` parsed as a module literally named `all`. Zero occurrences
            // in-tree today, which is exactly why it would have been found late.
            let trimmed = line.trim_start();
            let rest = trimmed
                .strip_prefix("import ")
                .or_else(|| trimmed.strip_prefix("meta import "))
                .or_else(|| trimmed.strip_prefix("public import "))
                .or_else(|| trimmed.strip_prefix("private import "));
            let Some(rest) = rest else { continue };
            // `import all Foo` re-exports Foo's whole environment; the MODULE is still `Foo`.
            let rest = rest.trim_start();
            let rest = rest.strip_prefix("all ").unwrap_or(rest);
            let name: String = rest
                .trim()
                .chars()
                .take_while(|c| {
                    c.is_alphanumeric() || *c == '_' || *c == '.' || *c == '«' || *c == '»'
                })
                .collect();
            if !name.is_empty() {
                stack.push(name);
            }
        }
    }
    Some(seen)
}

/// Flatten an IR-relative `.c` path into the splice object name the archive uses, matching the
/// shell script: `Dregg2/Exec/FFI.c` → `Dregg2_Exec_FFI.o` (path separators → `_`). Keeping the
/// exact same naming is what lets us REPLACE (not duplicate) the old Dregg2 members on re-splice.
fn splice_obj_name(ir_root: &Path, c: &Path) -> String {
    let rel = c.strip_prefix(ir_root).unwrap_or(c);
    let stem = rel.with_extension("");
    let mut name: String = stem
        .components()
        .map(|comp| comp.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("_");
    name.push_str(".o");
    name
}

/// `true` iff `target` is missing or older than `src` (the "recompile this" predicate — mirrors the
/// script's `[ ! -f "$out" ] || [ "$c" -nt "$out" ]`). Treats unreadable mtimes as "stale" so we
/// fail toward recompiling rather than shipping a stale object.
fn newer_than(src: &Path, target: &Path) -> bool {
    let Ok(target_meta) = std::fs::metadata(target) else {
        return true;
    };
    let (Ok(src_m), Ok(tgt_m)) = (
        std::fs::metadata(src).and_then(|m| m.modified()),
        target_meta.modified(),
    ) else {
        return true;
    };
    src_m > tgt_m
}

/// Recursively collect every regular file under `dir` (used to emit `rerun-if-changed` for the
/// whole Lean `Dregg2` source tree, so a no-op cargo build truly skips the closure rebuild).
fn collect_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_files(&path, out);
        } else {
            out.push(path);
        }
    }
}

/// Seed the per-OUT_DIR WORKING archive (`build`) from the SEED (`seed`), so the splice/closure/GC
/// steps below mutate the working copy and NEVER the shared seed (the swarm-safe split — see the
/// top-of-file note). The seed is treated as read-only input.
///
/// We (re)copy when the working archive is missing OR older than the seed (an out-of-band re-seed
/// via `scripts/seed-dregg2-closure.sh` must take effect). When the working copy is at least as new
/// as the seed we leave it — its spliced Dregg2 slice + GC pruning are the incremental steady state
/// for THIS feature set and must survive a no-op rebuild. The copy is staged to a sibling temp and
/// renamed into place so a working archive is never observed half-written. If the seed is absent we
/// do nothing: a prior working copy (if any) is reused; otherwise the `!build_archive.exists()`
/// guard in `main` degrades to marshal-only.
///
/// ⚑ RETURNS `true` iff it actually re-copied the seed — i.e. iff it just WIPED whatever Dregg2
/// slice the working archive had spliced in. The caller MUST force a re-splice on that, because a
/// warm `$OUT_DIR/dregg2_closure_objs/` cache otherwise leaves `recompiled == false` and the
/// un-spliced seed gets linked (see `archive_dregg2_complete`).
fn seed_build_archive(seed: &Path, build: &Path) -> bool {
    if !seed.exists() {
        return false;
    }
    // Decide whether to (re)seed. Copy iff the working archive is missing or strictly older than
    // the seed (mtime). `newer_than(seed, build)` ⇒ seed is newer (or build absent) ⇒ copy.
    if build.exists() && !newer_than(seed, build) {
        return false;
    }
    let Some(parent) = build.parent() else {
        return false;
    };
    // Stage to a unique-ish temp in the SAME dir (so the final rename is same-filesystem & atomic),
    // keyed on the build OUT_DIR's own path hash via the process id — one build script runs per
    // OUT_DIR at a time, but this keeps a crashed prior attempt from colliding.
    let tmp = parent.join(format!("libdregg_lean.a.seed-tmp.{}", std::process::id()));
    let _ = std::fs::remove_file(&tmp);
    match std::fs::copy(seed, &tmp) {
        Ok(_) => {}
        Err(e) => {
            println!(
                "cargo:warning=dregg-lean-ffi: could not stage the seed copy into OUT_DIR ({e}) — \
                 the build will use the existing working archive if present."
            );
            let _ = std::fs::remove_file(&tmp);
            return false;
        }
    }
    if let Err(e) = std::fs::rename(&tmp, build) {
        // Same-dir rename should never cross devices; fall back to a copy if it somehow fails.
        if std::fs::copy(&tmp, build).is_err() {
            println!(
                "cargo:warning=dregg-lean-ffi: could not install the working archive in OUT_DIR \
                 ({e}) — using the existing working archive if present."
            );
            let _ = std::fs::remove_file(&tmp);
            return false;
        }
        let _ = std::fs::remove_file(&tmp);
    }
    true
}

/// Produce / refresh `libdregg_lean.a` IN OUT_DIR by (1) `lake build`-ing the FFI module's
/// `:c` facet, (2) `leanc -c`-compiling each freshly-emitted `Dregg2/**/*.c` whose `.c` is newer
/// than its cached `.o`, and (3) splicing ONLY those `Dregg2_*.o` back into the (seeded) working
/// archive — preserving the ~5600 expensive mathlib/batteries/aesop dependency objects untouched.
/// `archive` here is the PER-OUT_DIR working copy, never the seed.
///
/// Incremental + cached: `lake` is itself incremental, the `leanc` step is guarded on
/// `.c`-newer-than-`.o`, and the (relatively expensive) `ar` extract/repack only runs when at least
/// one Dregg2 object actually changed, the caller just RE-SEEDED the working archive (`reseeded`,
/// which wipes the previous splice), or the archive's Dregg2 slice is incomplete. `rerun-if-changed`
/// is emitted by the caller for the source tree + toolchain marker, so a genuine no-op cargo build
/// does not even re-enter this function.
/// ⚑ RETURNS `true` iff the archive left in place is NOT built from the current Lean source — a
/// PROVENANCE DOWNGRADE. Every early `return` below is such a path: the Lean build was skipped,
/// refused, failed to elaborate, failed to compile, or failed to splice, and what remains linkable
/// is a seed or a previous build. The caller MUST NOT advertise a downgraded archive as a verified
/// runtime (see `main`'s provenance gate) — a `cargo:warning` cannot carry that, because cargo
/// HIDES build-script warnings for dependency crates, and `dregg-lean-ffi` is always a dependency.
///
/// This return value is load-bearing and was measured into existence (2026-07-28). Without it a
/// debug `cargo test` linked a THREE-DAY-OLD seed, `finality_gate_available()` stayed true (the old
/// seed exports the symbol), and `node/src/finality_gate.rs`'s enrollment falsifier ran against the
/// PRE-`c6f00c228` `tauOrder` — the one with no `enrolledId` filter — and reported "the VERIFIED
/// rule FINALIZED a block created by an UNENROLLED identity. The gate is OPEN." The gate was not
/// open; the test was reading last week's rule. A stale archive and a broken rule were, at the
/// point of measurement, the same observation.
fn build_dregg2_archive(
    meta: &Path,
    sysroot: &Path,
    archive: &Path,
    out_dir: &Path,
    seed: &Path,
    require_current_source: bool,
    reseeded: bool,
) -> bool {
    // ── COLD-LANE GUARD (2026-07-25) — check the archive BEFORE spending a Lean build ─────────
    //
    // This function used to `lake build` FIRST and only then discover, ~700 lines later, that the
    // base archive was absent and give up with "building marshal-only for now". In a lane with no
    // seed that ordering spends the ENTIRE mathlib build to reach a branch that throws it away.
    //
    // It is not a theoretical cost. On 2026-07-25 a plain `cargo check -p dungeon-on-dregg` in a
    // cold scratchpad `CARGO_TARGET_DIR` reached this line, and one build script became **55
    // concurrent `lake env leanc` jobs at ~642 MB each — about 35 GB** on a laptop with no cgroup
    // containment (`swarm-build` is an hbox tool; there is no local equivalent). Load average hit
    // 154, swap reached 54 GB, every other lane measured ~7% CPU efficiency, and NOTHING on the
    // machine could finish — including the Lean work itself. All of it was destined for the
    // marshal-only branch regardless, because that lane had no seed to splice into.
    //
    // So: if there is nothing to splice into, do not build. Marshal-only is the same outcome the
    // old code reached; this just declines to burn a mathlib build to get there.
    //
    // `DREGG_LEAN_COLD_BUILD=1` is the explicit opt-in for the paths that genuinely want a cold
    // build (`scripts/bootstrap.sh`, seed publication in CI). Fail-closed on purpose: the cheap,
    // safe behaviour is the default, and the expensive one must be asked for by name.
    if !archive.exists() && !seed.exists() {
        if std::env::var("DREGG_LEAN_COLD_BUILD").as_deref() != Ok("1") {
            println!(
                "cargo:warning=dregg-lean-ffi: no base archive at {} and no seed at {} — SKIPPING \
                 the Lean build entirely and linking marshal-only. A cold `lake build` here would \
                 compile the whole mathlib closure (observed: 55 concurrent leanc jobs, ~35 GB) \
                 only to be discarded, since there is nothing to splice into. To seed properly run \
                 `./scripts/bootstrap.sh` from the repo root. To force the cold build anyway set \
                 DREGG_LEAN_COLD_BUILD=1 — and bound it, e.g. DREGG_LEANC_JOBS=4.",
                archive.display(),
                seed.display()
            );
            return true;
        }
        println!(
            "cargo:warning=dregg-lean-ffi: DREGG_LEAN_COLD_BUILD=1 — running a COLD Lean build. \
             This compiles the mathlib closure and can hold tens of GB. Bound it with \
             DREGG_LEANC_JOBS=<n> (default {}) and prefer a machine with cgroup containment.",
            configured_leanc_workers()
        );
    }

    // (1) Refresh the Lean `:c` facets. `lake build` is incremental; building the FFI module pulls
    // in (and emits `:c` for) its whole Dregg2 transitive closure.
    let inc = sysroot.join("include");
    let ir_root = meta.join(".lake/build/ir");
    let dregg2_ir = ir_root.join("Dregg2");

    // ONE TARGET. `Dregg2.FFI` (metatheory/Dregg2/FFI.lean) IS the Lean⟷Rust boundary: it imports
    // every module that carries an `@[export]` Rust can call, and nothing else roots this build.
    //
    // This replaced a hand-maintained 24-entry list of "modules that live OUTSIDE the FFI import
    // closure". That list was the drift surface: a module absent from it emitted no `:c` facet, so
    // its symbol never entered the archive, so the Rust `#[cfg(dregg_*_present)]` bridge compiled its
    // ABSENT arm and the node ran the un-gated path — green, silent, wrong. Three light-client gates
    // (`dregg_{eth,mpt,tm}_lc_verify`) were dark exactly that way; they were the only Lean exports
    // missing from the built archive. An import closure cannot drift from itself.
    //
    // Adding an export is now: put the `@[export]` next to its proof, add ONE `import` line to
    // `Dregg2/FFI.lean`. Nothing here changes.
    let lake_targets = ["Dregg2.FFI"];
    // BOUNDED FAN-OUT, MEASURED (2026-07-25). Unbounded, `lake build` spawns one `lean` per ready
    // module, each elaborating a proof module and holding GBs — the 55-job / ~35 GB stampede that
    // took a laptop to load average 154 and 54 GB of swap.
    //
    // The cap is the `LEAN_NUM_THREADS` task-pool size, applied and then VERIFIED by
    // `build_parallel::run_bounded_lake` (that constant carries the measurement which decided it:
    // 24 independent modules, peak 10 concurrent `lean` uncapped, exactly 4 at 4, exactly 2 at 2).
    //
    // ⚠ It is NOT `-j`. This `lake` has no jobs flag at all, so the `-j <n>` that stood here for
    // ~95 minutes on 2026-07-25 bounded nothing: it made EVERY `lake build` from this script fail
    // instantly, which sent every non-strict build down the restore-the-seed path — and the seed
    // exports no PQ core — while every strict build panicked blaming an IR tree that was fine. A
    // containment measure that silently disarms the verified runtime is worse than none, which is
    // why the budget is now checked against the children `lake` actually spawned rather than
    // trusted because it was passed.
    //
    // `configured_leanc_workers()` (default: half the cores, ≤ 8; `DREGG_LEANC_JOBS` overrides) is
    // the SAME budget the `leanc` phases below use, because it is one MEMORY budget wearing a CPU
    // budget's clothes. An outer `LEAN_NUM_THREADS` is an operator decision and is honoured as-is.
    let fanout_budget = configured_leanc_workers();
    let mut lake_cmd = Command::new("lake");
    lake_cmd.arg("build");
    // Belt and braces: if a future `lake` grows a REAL jobs flag back, pass it too — both mechanisms
    // are then live and `report_lake_fanout` still verifies the result. Today this is `None`.
    if let Some(flag) = lake_jobs_flag(meta) {
        lake_cmd.arg(flag).arg(fanout_budget.to_string());
    }
    lake_cmd.args(lake_targets).current_dir(meta);
    let lake_run = build_parallel::run_bounded_lake(&mut lake_cmd, fanout_budget);
    match lake_run {
        Ok(run) if run.status.success() => report_lake_fanout(&run, fanout_budget),
        Ok(run) => {
            let s = run.status;
            report_lake_fanout(&run, fanout_budget);
            // `lake build` FAILED. When this happens the metatheory `.lake/build/ir` tree is NOT
            // guaranteed internally coherent: some modules' `:c` facets are freshly re-emitted while
            // others (the ones whose module elaboration aborted — e.g. a WIP proof regression tripping
            // an `#assert_axioms` hygiene gate) keep their STALE `.c` or have none at all. Splicing
            // that partial fresh set over the seed produces a torn archive whose cross-module
            // SPECIALIZATIONS don't resolve: a freshly-recompiled `Dregg2_Exec_Handler.o` references
            // `_lp_…_TurnExecutorFull_*` specialized symbols that the un-rebuilt `TurnExecutorFull.o`
            // never emitted → `Undefined symbols` at the final link of every downstream binary
            // (dregg-node included). The git-tracked SEED archive is, by construction, a coherent
            // linkable set. A non-strict developer build may therefore discard any prior
            // (possibly incoherent) working archive and restore that consistent seed. A strict
            // verification/release build must instead fail: an older coherent kernel is not
            // evidence that the current checkout's Turn semantics were compiled.
            //
            // ⚠ NAME THE ACTUAL CAUSE. "the IR tree is not coherent" is ONE of the reasons `lake`
            // can exit non-zero, and for ~95 minutes on 2026-07-25 it was reported for a completely
            // different one: `lake` REJECTED this script's own command line (`unknown short option
            // '-j'`) and never elaborated a module, while `lake build --no-build` exited 0 — the
            // tree was fine and the error was lying about why. A lane lost an hour to that. So
            // separate "lake refused the invocation" (a bug in THIS file, nothing to do with Lean)
            // from "a module failed to elaborate", and quote what lake said either way.
            let said = build_parallel::stderr_tail(&run.stderr, 8);
            let reason = if build_parallel::is_cli_rejection(&run.stderr) {
                format!(
                    "`lake` REFUSED this build script's own invocation (exit {s}) — a CLI mismatch \
                     in dregg-lean-ffi/build.rs, NOT a Lean or IR problem: no module was \
                     elaborated and the IR tree is untouched. Fix the `lake build` arguments here. \
                     lake said: {said}"
                )
            } else {
                format!(
                    "`lake build` of the FFI + gate modules exited {s} (a module failed to \
                     elaborate), so the current-source IR tree is not coherent enough to produce a \
                     verified runtime archive. lake said: {said}"
                )
            };
            if require_current_source {
                panic!(
                    "dregg-lean-ffi: DREGG_REQUIRE_LEAN/current release gate refuses a stale \
                     verified runtime: {reason}. Fix the Lean build; do not satisfy a current-source \
                     verification claim by restoring an older seed."
                );
            }
            // Say the substitution OUT LOUD, in the words the reader needs: what is linked is no
            // longer this checkout. A quiet "restored the seed" line reads like housekeeping; it is
            // a PROVENANCE DOWNGRADE, and every green measured against the result is a green
            // measured against something other than what HEAD would ship.
            println!(
                "cargo:warning=dregg-lean-ffi: ⚠ VERIFIED-RUNTIME PROVENANCE DOWNGRADE — {reason}. \
                 This non-strict (debug) build LINKS THE PRE-BUILT SEED ARCHIVE INSTEAD OF THIS \
                 CHECKOUT: the Lean objects about to be linked do NOT correspond to HEAD, the seed \
                 exports no PQ core, and any test that passes against it has NOT exercised the \
                 current Lean sources. It does not splice a partial fresh set (that would tear the \
                 archive). Set DREGG_REQUIRE_LEAN=1 to make this a hard failure, or \
                 DREGG_TEST_REQUIRE_LEAN=1 to make the debug test lane refuse the missing exports."
            );
            // Force the working archive back to the seed (overwrite any prior incoherent splice).
            let _ = std::fs::remove_file(archive);
            let _ = seed_build_archive(seed, archive);
            return true;
        }
        Err(e) => {
            if require_current_source {
                panic!(
                    "dregg-lean-ffi: DREGG_REQUIRE_LEAN/current release gate could not run the \
                     current-source Lean build ({e}); refusing to link an older seed as if it \
                     represented this checkout"
                );
            }
            println!(
                "cargo:warning=dregg-lean-ffi: could not run `lake build` ({e}) — is elan/lake on \
                 PATH? Falling back to the existing archive (if any)."
            );
            return true;
        }
    }

    // The `:c` facet must have landed for us to compile anything.
    if !dregg2_ir.exists() {
        if require_current_source {
            panic!(
                "dregg-lean-ffi: DREGG_REQUIRE_LEAN/current release gate found no current-source \
                 Dregg2 C IR at {} after a successful lake build",
                dregg2_ir.display()
            );
        }
        println!(
            "cargo:warning=dregg-lean-ffi: no `:c` IR at {} after `lake build` — cannot compile the \
             Dregg2 native objects. Run `lake build Dregg2.Exec.FFI` in metatheory and re-check.",
            dregg2_ir.display()
        );
        return true;
    }

    // Persistent object cache (so the `.c`-newer-than-`.o` guard survives across cargo builds).
    let obj_dir = out_dir.join("dregg2_closure_objs");
    if let Err(e) = std::fs::create_dir_all(&obj_dir) {
        if require_current_source {
            panic!(
                "dregg-lean-ffi: cannot create the current-source Lean object cache {} ({e})",
                obj_dir.display()
            );
        }
        println!(
            "cargo:warning=dregg-lean-ffi: cannot create {} ({e})",
            obj_dir.display()
        );
        return true;
    }

    // (2) Compile each Dregg2 `.c` newer than its cached `.o`, in parallel up to the CPU count.
    //
    // SCOPED TO THE BOUNDARY CLOSURE. This used to splice EVERY `Dregg2/**/*.c` present in the IR
    // tree — i.e. whatever any lane had ever `lake build`-t, which is the whole proof tree. Measured
    // on the 2026-07-24 release archive: 1701 of our 1893 spliced objects (63.4 MB) were NOT in the
    // export closure at all, and they are what dragged most of the 200 MB of Mathlib in behind them
    // (an object's `initialize_` hard-calls its imports' initializers, so an off-closure proof module
    // pulls its whole `import Mathlib.…` chain into the link). The archive is the RUNTIME, not the
    // build directory's history.
    //
    // The closure is read from `Dregg2/FFI.lean`'s imports, transitively, over the `.lean` sources —
    // the same graph Lake used to decide what to elaborate. Anything genuinely referenced but not
    // spliced here is still recovered afterwards by `complete_initializer_closure`, which chases
    // undefined `initialize_*` edges; scoping the initial splice cannot lose a needed object, it can
    // only stop shipping objects nothing links to.
    let boundary = boundary_closure(meta);
    let mut c_files = Vec::new();
    collect_files(&dregg2_ir, &mut c_files);
    c_files.retain(|p| p.extension().map(|e| e == "c").unwrap_or(false));
    if let Some(closure) = &boundary {
        let before = c_files.len();
        c_files.retain(|p| {
            module_name_of_ir_c(&ir_root, p)
                .map(|m| closure.contains(&m))
                .unwrap_or(true)
        });
        println!(
            "cargo:warning=dregg-lean-ffi: splicing the Dregg2.FFI boundary closure — {} of {} \
             emitted Dregg2 C facets ({} off-closure proof modules not shipped in the runtime \
             archive).",
            c_files.len(),
            before,
            before - c_files.len()
        );
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: could not read the Dregg2.FFI import closure from {} — \
             splicing every emitted Dregg2 C facet (larger archive, same symbols).",
            meta.join("Dregg2/FFI.lean").display()
        );
    }
    c_files.sort();

    // The exact set of object names we expect from the CURRENT source. Used to (a) drive the
    // splice and (b) prune STALE cached objects whose `.c` was deleted/renamed — otherwise a
    // removed module's old `Dregg2_*.o` would keep getting spliced back in (dangling/duplicate
    // symbols). We treat such a prune as a change so the splice picks up the removal.
    let expected: std::collections::HashSet<String> = c_files
        .iter()
        .map(|c| splice_obj_name(&ir_root, c))
        .collect();
    let mut pruned = false;
    if let Ok(entries) = std::fs::read_dir(&obj_dir) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if name.starts_with("Dregg2_") && name.ends_with(".o") && !expected.contains(&name) {
                let _ = std::fs::remove_file(entry.path());
                pruned = true;
            }
        }
    }

    let mut jobs: Vec<(PathBuf, PathBuf)> = Vec::new();
    for c in &c_files {
        let obj = obj_dir.join(splice_obj_name(&ir_root, c));
        if newer_than(c, &obj) {
            jobs.push((c.clone(), obj));
        }
    }

    let recompiled = !jobs.is_empty() || pruned;
    if !jobs.is_empty() {
        let workers = configured_leanc_workers();
        println!(
            "cargo:warning=dregg-lean-ffi: compiling {} changed Dregg2 C facet(s) via {workers} \
             bounded leanc worker(s) …",
            jobs.len(),
        );
        let outcomes = build_parallel::run_indexed(&jobs, workers, |(c, obj)| {
            // `-fPIC` so the spliced objects are position-independent: the SAME archive
            // then serves both link modes (static bins AND the `DREGG_LEAN_LINK=shared`
            // cdylib link, e.g. the sdk-py pyo3 module). No-op on macOS (PIC is the
            // default); on Linux it guards against a leanc default change (leanc
            // currently compiles PIC there too — Lean plugins are dlopen'd).
            Command::new("lake")
                .args(["env", "leanc", "-c", "-fPIC", "-I"])
                .arg(&inc)
                .arg(c)
                .arg("-o")
                .arg(obj)
                .current_dir(meta)
                .output()
        });
        let mut failed = false;
        for ((c, obj), outcome) in jobs.iter().zip(&outcomes) {
            if !matches!(outcome, Ok(output) if output.status.success()) {
                // Drop a stale/partial object so the next build retries this `.c`.
                let _ = std::fs::remove_file(obj);
                failed = true;
                println!(
                    "cargo:warning=dregg-lean-ffi: leanc failed on {}",
                    c.display()
                );
            }
            // Preserve warnings from successful compiles too; replaying after join keeps them
            // deterministic while avoiding concurrent child-process stderr interleaving.
            emit_command_diagnostics(outcome);
        }
        if failed {
            if require_current_source {
                panic!(
                    "dregg-lean-ffi: at least one current-source Dregg2 C facet failed to compile; \
                     DREGG_REQUIRE_LEAN/current release gate refuses the older archive"
                );
            }
            println!(
                "cargo:warning=dregg-lean-ffi: at least one Dregg2 C facet failed to compile — \
                 NOT re-splicing the archive (it keeps its previous, consistent contents)."
            );
            return true;
        }
    }

    // (3) Splice. Only pay the extract/repack cost when something actually changed, when the caller
    // just RE-SEEDED (which wipes the previous splice), or when the archive's Dregg2 slice is
    // INCOMPLETE — i.e. it does not export every symbol in the required-export manifest.
    //
    // ⚑ Both of the last two conditions are the 2026-07-24 fix for the warm-cache silent-degrade
    // (`docs/ASSESS-cold-build-silent-export.md` §3.2). This used to read
    // `recompiled || !archive_has_dregg2(archive)`, where `archive_has_dregg2` asked only whether
    // ANY `Dregg2_*.o` member existed — which is TRUE of the un-spliced seed. A re-seed + a warm
    // `.o` cache therefore produced `needs_splice == false` and linked the seed with every
    // security-critical splice-only export ABSENT, while the objects defining them sat unused in
    // `dregg2_closure_objs/`. See `archive_dregg2_complete` for the full note.
    // (`archive.exists()` first so an absent base skips a pointless `nm` and reports itself through
    // the ABSENT branch just below, not as an "incomplete slice".)
    let slice_complete = archive.exists() && archive_dregg2_complete(archive);
    let needs_splice = recompiled || reseeded || !slice_complete;
    if archive.exists() && !recompiled && (reseeded || !slice_complete) {
        println!(
            "cargo:warning=dregg-lean-ffi: forcing a re-splice with a WARM object cache \
             (reseeded={reseeded}, dregg2-slice-complete={slice_complete}) — a re-seeded or \
             export-incomplete archive must not be linked just because it carries some Dregg2 \
             members."
        );
    }

    if !archive.exists() {
        println!(
            "cargo:warning=dregg-lean-ffi: base archive {} is ABSENT — it must hold the ~5600 \
             precompiled mathlib/batteries/aesop dependency objects, which are EXPENSIVE to \
             regenerate. Run `./scripts/bootstrap.sh` from the repo root: it checks the toolchain \
             + mathlib pin, lake-builds the executor, seeds this archive once, and verifies the \
             link (afterwards plain `cargo build` keeps it fresh automatically). Building \
             marshal-only for now.",
            archive.display()
        );
        return true;
    }

    if needs_splice {
        if let Err(e) = splice_objects(archive, &obj_dir, out_dir) {
            if require_current_source {
                panic!(
                    "dregg-lean-ffi: current-source archive splice failed ({e}); \
                     DREGG_REQUIRE_LEAN/current release gate refuses the previous archive"
                );
            }
            println!(
                "cargo:warning=dregg-lean-ffi: archive splice failed ({e}) — the archive was left \
                 unchanged; a previous-but-consistent build will be linked."
            );
            return true;
        }
    }

    // (4) Closure-completion. The freshly-built Dregg2 objects may import NEW dependency modules
    // (e.g. a `Mathlib.Order.Extension.Linear` that a concurrent edit just added) whose initializer
    // objects are NOT in the frozen base archive's dependency closure. Splicing in only the Dregg2
    // objects would then leave a dangling `_initialize_<dep>` undefined symbol and the FINAL Rust
    // link fails. So we close the archive: detect undefined `_initialize_*` symbols, compile the
    // matching `.c` from the Lean source/dependency IR trees, splice them in, and repeat until the
    // archive is self-contained (or no resolvable `.c` remains — which we surface loudly). This MUST
    // run even when no Dregg2 facet changed: a prior fail-closed build may have banked several closure
    // passes in the OUT_DIR working archive and needs to resume from that coherent checkpoint.
    complete_initializer_closure(meta, sysroot, archive, out_dir, require_current_source);

    // (5) Reachability GC. Closure-completion makes the archive self-LINKING, but the base still
    // carries every dependency object it was ever seeded with — including the mathlib CategoryTheory/
    // Tactic objects the import-trimmed FFI closure no longer references. Drop every member NOT
    // reachable, by symbol, from the `dregg_*` exports. This is the durable payoff of the import-graph
    // split: without it the next splice would re-bloat the archive back to its seeded size.
    //
    // ESCAPE HATCH (`DREGG_LEAN_FFI_NO_ARCHIVE_GC=1`): the GC's symbol-reachability BFS chases only
    // UNDEFINED-symbol edges, so if the closure-completion pass (step 4) seeded an archive whose
    // dependency members reference mathlib FUNCTION symbols that no kept member leaves UNDEFINED (e.g.
    // after a hand re-seed of the FULL dependency closure), the GC can drop the very mathlib members
    // those functions need — leaving `_lp_mathlib_*` unresolved at the final Rust link. When a FULL
    // archive was just restored out-of-band, set this to keep EVERY member (correct, larger) rather
    // than risk the destructive prune. Off by default (the GC stays the steady-state size payoff).
    // ⚑ RESTORED 2026-07-25 (dropped by 7ebe7b7d4b — see `metatheory_dir`). Without it, setting
    // the escape hatch after a failed link does NOT re-run this script, so the operator's fix
    // appears not to work — the destructive prune stays cached.
    println!("cargo:rerun-if-env-changed=DREGG_LEAN_FFI_NO_ARCHIVE_GC");
    if std::env::var("DREGG_LEAN_FFI_NO_ARCHIVE_GC").as_deref() == Ok("1") {
        println!(
            "cargo:warning=dregg-lean-ffi: DREGG_LEAN_FFI_NO_ARCHIVE_GC=1 — skipping archive \
             reachability GC, keeping every member (full self-linking archive)."
        );
    } else {
        gc_unreachable_members(archive, out_dir);
    }
    // Reached only on the SUCCESS path: the archive holds this checkout's Dregg2 objects.
    false
}

/// Discover every `.lake/build/ir` directory that can supply a `.c` for the dependency closure:
/// the project's own IR, each git-package IR (`.lake/packages/*/.lake/build/ir`), and each
/// `type:path` dependency's IR (its `dir` is recorded in `lake-manifest.json`; we scan the manifest
/// text for `"dir": "..."` rather than pull a JSON crate into build-deps).
fn discover_ir_roots(meta: &Path) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    let project_ir = meta.join(".lake/build/ir");
    if project_ir.is_dir() {
        roots.push(project_ir);
    }
    let pkgs = meta.join(".lake/packages");
    if let Ok(entries) = std::fs::read_dir(&pkgs) {
        for entry in entries.flatten() {
            let ir = entry.path().join(".lake/build/ir");
            if ir.is_dir() {
                roots.push(ir);
            }
        }
    }
    // `type:path` deps (e.g. a local mathlib checkout): pull their `dir` from the manifest.
    if let Ok(text) = std::fs::read_to_string(meta.join("lake-manifest.json")) {
        for raw in text.split("\"dir\":") {
            // The value is the first quoted string after the key.
            if let Some(start) = raw.find('"') {
                if let Some(end) = raw[start + 1..].find('"') {
                    let dir = &raw[start + 1..start + 1 + end];
                    let p = meta.join(dir).join(".lake/build/ir");
                    if p.is_dir() && !roots.iter().any(|r| r == &p) {
                        roots.push(p);
                    }
                }
            }
        }
    }
    roots
}

/// Lean's C-symbol mangling of a module path: each path component has its INTERNAL underscores
/// doubled (`_`→`__`), then the components are joined with a single `_`. So `A/B/CommMon_.c` →
/// `A_B_CommMon__` — which is exactly the `<flat>` that appears in `_initialize_<lib>_<flat>`. This
/// is what lets the resolver match modules whose name itself contains `_` (e.g. mathlib's `CommMon_`,
/// `Mon_`), which a naive `/`→`_` flatten would get wrong (one `_` instead of two).
fn lean_mangle_relpath(rel: &Path) -> String {
    rel.with_extension("")
        .components()
        .map(|comp| comp.as_os_str().to_string_lossy().replace('_', "__"))
        .collect::<Vec<_>>()
        .join("_")
}

/// Index every `.c` under the IR roots by its Lean-mangled module name (see `lean_mangle_relpath`,
/// e.g. `Mathlib/Order/Extension/Linear.c` → `Mathlib_Order_Extension_Linear`). An undefined
/// `_initialize_<lib>_<flat>` symbol then resolves by stripping the `_initialize_` prefix and
/// matching some suffix of the remainder against this index (the leading `<lib>` token is dropped).
fn build_cfile_index(roots: &[PathBuf]) -> std::collections::HashMap<String, PathBuf> {
    let mut index = std::collections::HashMap::new();
    for root in roots {
        let mut files = Vec::new();
        collect_files(root, &mut files);
        for c in files {
            if c.extension().map(|e| e == "c").unwrap_or(false) {
                if let Ok(rel) = c.strip_prefix(root) {
                    let flat = lean_mangle_relpath(rel);
                    // First writer wins; module names are unique across roots in practice.
                    index.entry(flat).or_insert(c);
                }
            }
        }
    }
    index
}

/// The Lean module initializers that are UNDEFINED in the archive AS A WHOLE: referenced (`U`) by
/// some member but DEFINED (`T`) by NO member. (`nm -u` is unreliable on archives — it lists symbols
/// undefined in individual members even when another member defines them — so we run full `nm` once
/// and compute the U-minus-T set ourselves.) These are the genuine dangling dependency edges the
/// final Rust link would fail on; closure-completion must supply each one's defining object.
fn undefined_initializers(archive: &Path) -> Vec<String> {
    let Ok(out) = Command::new(nm_tool()).arg(archive).output() else {
        return Vec::new();
    };
    let text = String::from_utf8_lossy(&out.stdout);
    let mut defined = std::collections::HashSet::new();
    let mut referenced = std::collections::HashSet::new();
    for line in text.lines() {
        // `nm` archive symbol lines come in two shapes:
        //   "                 U _sym"   (undefined: type letter, then symbol)
        //   "0000000000001234 T _sym"   (defined: address, type letter, symbol)
        // Other lines (blank, "archive.a:", "obj.o:") have no type+symbol and are skipped.
        let toks: Vec<&str> = line.split_whitespace().collect();
        let (ty, sym) = match toks.as_slice() {
            [ty, sym] if ty.len() == 1 => (*ty, *sym), // undefined / no-address
            [_addr, ty, sym] if ty.len() == 1 => (*ty, *sym), // defined / with-address
            _ => continue,
        };
        let name = sym.trim_start_matches('_');
        // Closure completion follows the ordinary module initializer graph only. The generated
        // `runtime_initialize_` / `meta_initialize_` graph contains elaborator/proof imports that
        // are intentionally severed by the runtime archive boundary; chasing those edges attempts
        // to compile essentially all of Mathlib. Runtime trimming still classifies all three
        // families, but only `initialize_` is a link-required project closure edge here.
        if let Some(rest) = name.strip_prefix("initialize_") {
            // The toolchain stdlib initializers (Init/Std/Lean/Lake) are supplied by the sysroot
            // static libs the FINAL Rust link pulls in (rustc-link-lib=static={Init,Std,Lean,Lake});
            // they have no `.c` in the project/dependency IR and are NOT ours to splice. Skip them so
            // closure-completion chases only genuinely-missing in-closure modules.
            let toolchain = ["Init", "Std", "Lean", "Lake"]
                .iter()
                .any(|lib| rest == *lib || rest.starts_with(&format!("{lib}_")));
            if toolchain {
                continue;
            }
            if ty == "U" {
                referenced.insert(name.to_string());
            } else {
                defined.insert(name.to_string());
            }
        }
    }
    let mut missing: Vec<String> = referenced.difference(&defined).cloned().collect();
    missing.sort();
    missing
}

/// Map a bare initializer symbol (`{initialize,runtime_initialize,meta_initialize}_<lib>_<flat>`)
/// to its source `.c` via the index. The `<lib>` token is a single library name (no
/// internal-underscore doubling); we strip the initializer family, then strip a KNOWN library token
/// + `_`, leaving exactly the Lean-mangled `<flat>` index key. This is unambiguous (vs
/// suffix-guessing, which breaks on `__`-mangled names like `CommMon__`). We try the known tokens
/// longest-first so e.g. `LeanSearchClient` is preferred over a shorter prefix.
fn resolve_initializer_cfile<'a>(
    sym: &str,
    index: &'a std::collections::HashMap<String, PathBuf>,
) -> Option<(String, &'a PathBuf)> {
    let rest = lean_init_suffix(sym)?;
    // Library tokens that prefix a module initializer (the project libs + every dependency package).
    // `Init`/`Std`/`Lean`/`Lake` are filtered out earlier (sysroot-provided), so they need not appear.
    let mut libs = [
        "Dregg2",
        "Metatheory",
        "mathlib",
        "aesop",
        "batteries",
        "importGraph",
        "LeanSearchClient",
        "plausible",
        "proofwidgets",
        "Qq",
        "Cli",
    ];
    libs.sort_by_key(|l| std::cmp::Reverse(l.len()));
    for lib in libs {
        if let Some(flat) = rest.strip_prefix(lib).and_then(|r| r.strip_prefix('_')) {
            if let Some(cfile) = index.get(flat) {
                return Some((flat.to_string(), cfile));
            }
        }
    }
    None
}

/// Iteratively add the dependency-closure objects the freshly-spliced Dregg2 objects need, until the
/// archive has no resolvable undefined `_initialize_*` edge left. Each pass compiles the missing
/// `.c` (cached by flattened name under OUT_DIR) and splices them in; new objects can introduce
/// further deps, hence the loop. Bounded to avoid runaway; strict/release builds fail closed if
/// compilation, source resolution, archive mutation, or closure exhaustion is incomplete.
fn complete_initializer_closure(
    meta: &Path,
    sysroot: &Path,
    archive: &Path,
    out_dir: &Path,
    require_current_source: bool,
) {
    const MAX_CLOSURE_PASSES: usize = 64;
    let inc = sysroot.join("include");
    let dep_dir = out_dir.join("dregg2_closure_deps");
    if let Err(error) = std::fs::create_dir_all(&dep_dir) {
        let reason = format!(
            "cannot create dependency-closure object cache {} ({error})",
            dep_dir.display()
        );
        if require_current_source {
            panic!("dregg-lean-ffi: {reason}");
        }
        println!("cargo:warning=dregg-lean-ffi: {reason}");
        return;
    }
    let roots = discover_ir_roots(meta);
    let index = build_cfile_index(&roots);

    for pass in 0..MAX_CLOSURE_PASSES {
        let undefined = undefined_initializers(archive);
        if undefined.is_empty() {
            return;
        }
        // Resolve as many as we can to source `.c`. Compilation jobs and the archive-add list both
        // retain the sorted undefined-symbol order, regardless of worker completion order.
        let mut to_add: Vec<(String, PathBuf)> = Vec::new(); // (objname, objpath)
        let mut compile_jobs: Vec<(String, PathBuf, PathBuf)> = Vec::new(); // (sym, cfile, obj)
        let mut unresolved = Vec::new();
        for sym in &undefined {
            match resolve_initializer_cfile(sym, &index) {
                Some((flat, cfile)) => {
                    let obj = dep_dir.join(format!("{flat}.o"));
                    if newer_than(cfile, &obj) {
                        compile_jobs.push((sym.clone(), cfile.clone(), obj.clone()));
                    }
                    to_add.push((format!("{flat}.o"), obj));
                }
                None => unresolved.push(sym.clone()),
            }
        }

        if !compile_jobs.is_empty() {
            let workers = configured_leanc_workers();
            println!(
                "cargo:warning=dregg-lean-ffi: closure pass {pass}: compiling {} dependency \
                 object(s) via {workers} bounded leanc worker(s) …",
                compile_jobs.len(),
            );
            let outcomes =
                build_parallel::run_indexed(&compile_jobs, workers, |(_sym, cfile, obj)| {
                    // `-fPIC` for the same shared-link-compatibility reason as the splice
                    // compile above (one archive, both link modes).
                    Command::new("lake")
                        .args(["env", "leanc", "-c", "-fPIC", "-I"])
                        .arg(&inc)
                        .arg(cfile)
                        .arg("-o")
                        .arg(obj)
                        .current_dir(meta)
                        .output()
                });
            let mut failed = 0_usize;
            for ((sym, cfile, obj), outcome) in compile_jobs.iter().zip(&outcomes) {
                if !matches!(outcome, Ok(output) if output.status.success()) {
                    let _ = std::fs::remove_file(obj);
                    failed += 1;
                    println!(
                        "cargo:warning=dregg-lean-ffi: closure leanc failed on {} (dep of {sym})",
                        cfile.display()
                    );
                }
                // Preserve warnings from successful compiles too; replaying after join keeps them
                // deterministic while avoiding concurrent child-process stderr interleaving.
                emit_command_diagnostics(outcome);
            }
            if failed != 0 {
                let reason = format!(
                    "closure pass {pass} failed to compile {failed} of {} dependency object(s); \
                     refusing to splice a partial pass",
                    compile_jobs.len()
                );
                if require_current_source {
                    panic!("dregg-lean-ffi: {reason}");
                }
                println!("cargo:warning=dregg-lean-ffi: {reason}");
                return;
            }
        }

        if to_add.is_empty() {
            if !unresolved.is_empty() {
                let reason = format!(
                    "{} undefined initializer(s) could not be resolved to a `.c` in the IR trees \
                     (e.g. {}); the archive does not self-link. Re-seed the closure \
                     (scripts/seed-dregg2-closure.sh) if the dependency set changed substantially",
                    unresolved.len(),
                    unresolved.first().map(|s| s.as_str()).unwrap_or("?")
                );
                if require_current_source {
                    panic!("dregg-lean-ffi: {reason}");
                }
                println!("cargo:warning=dregg-lean-ffi: {reason}");
            }
            return;
        }

        if let Err(e) = add_objects_to_archive(archive, &to_add, out_dir) {
            let reason = format!("closure splice failed on pass {pass} ({e})");
            if require_current_source {
                panic!("dregg-lean-ffi: {reason}");
            }
            println!("cargo:warning=dregg-lean-ffi: {reason}");
            return;
        }
        println!(
            "cargo:warning=dregg-lean-ffi: closure pass {pass}: added {} dependency object(s).",
            to_add.len()
        );
    }
    let remaining = undefined_initializers(archive);
    if remaining.is_empty() {
        return;
    }
    let reason = format!(
        "closure completion hit the {MAX_CLOSURE_PASSES}-pass bound with {} undefined \
         initializer(s) remaining (e.g. {}); archive is incomplete",
        remaining.len(),
        remaining.first().map(|s| s.as_str()).unwrap_or("?")
    );
    if require_current_source {
        panic!("dregg-lean-ffi: {reason}");
    }
    println!("cargo:warning=dregg-lean-ffi: {reason}");
}

/// **Archive reachability GC — the import-graph-trim payoff made durable.**
///
/// After the splice + closure-completion the archive self-links, but it still carries every
/// dependency object the BASE archive was ever seeded with — including the thousands of mathlib
/// `CategoryTheory`/`Tactic` objects that the (now import-trimmed) FFI closure no longer references.
/// Lean runs an `initialize_` per ARCHIVED module at boot, so those dead members are not just dead
/// weight — they inflate the linked binary and the wasm executor. `-Oz`/`--gc-sections` cannot strip
/// them (each module's initializer is reachable from its own object's ctor), so we garbage-collect at
/// the ARCHIVE level: keep only members reachable, by symbol, from the `dregg_*` FFI exports.
///
/// Reachability is exact and conservative: a member is kept iff it is the export-defining root, or it
/// defines a symbol that some kept member leaves undefined (`U`). Toolchain-supplied symbols (resolved
/// by the final Rust link against the sysroot `Init`/`Std`/`Lean`/`Lake` static libs) need no archive
/// member, so members that ONLY serve them drop out. If `nm` is unavailable or the computed reachable
/// set looks implausibly small (a parse failure), we SKIP the GC and keep the (correct, larger) archive
/// — never risk a broken link to save bytes.
fn gc_unreachable_members(archive: &Path, out_dir: &Path) {
    let Ok(out) = Command::new(nm_tool()).arg("-A").arg(archive).output() else {
        return;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    use std::collections::{HashMap, HashSet};
    // member -> (defined syms, undefined syms);  symbol -> members defining it.
    let mut undef: HashMap<String, HashSet<String>> = HashMap::new();
    let mut sym_def_in: HashMap<String, HashSet<String>> = HashMap::new();
    let mut members: HashSet<String> = HashSet::new();
    let mut roots: HashSet<String> = HashSet::new();
    for line in text.lines() {
        let Some((member, rest)) = nm_archive_member_row(line) else {
            continue;
        };
        let toks: Vec<&str> = rest.split_whitespace().collect();
        let (ty, sym) = match toks.as_slice() {
            [ty, sym] if ty.len() == 1 => (*ty, *sym),
            [_addr, ty, sym] if ty.len() == 1 => (*ty, *sym),
            _ => continue,
        };
        members.insert(member.clone());
        if ty == "U" || ty == "u" {
            undef
                .entry(member.clone())
                .or_default()
                .insert(sym.to_string());
        } else {
            sym_def_in
                .entry(sym.to_string())
                .or_default()
                .insert(member.clone());
            // Root: any member defining a `_dregg_*` FFI export (the C-ABI entry points).
            if sym.trim_start_matches('_').starts_with("dregg_") {
                roots.insert(member);
            }
        }
    }
    if members.is_empty() || roots.is_empty() {
        println!(
            "cargo:warning=dregg-lean-ffi: archive GC could not parse members/roots from `nm -A` \
             (members={}, roots={}); refusing to prune rather than silently pretending GC ran.",
            members.len(),
            roots.len()
        );
        return;
    }
    // BFS: keep a member, then chase each of its undefined symbols to the member(s) defining them.
    let mut reach: HashSet<String> = HashSet::new();
    let mut queue: Vec<String> = roots.iter().cloned().collect();
    while let Some(member) = queue.pop() {
        if !reach.insert(member.clone()) {
            continue;
        }
        if let Some(us) = undef.get(&member) {
            for u in us {
                if let Some(defs) = sym_def_in.get(u) {
                    for dm in defs {
                        if !reach.contains(dm) {
                            queue.push(dm.clone());
                        }
                    }
                }
            }
        }
    }
    let unreachable = members.len().saturating_sub(reach.len());
    if unreachable == 0 {
        return; // already minimal.
    }
    // Sanity floor: the FFI closure genuinely needs hundreds of dependency members; if the reachable
    // set collapsed below a plausible floor the `nm` parse misfired — keep the larger, correct archive.
    if reach.len() < 200 {
        println!(
            "cargo:warning=dregg-lean-ffi: archive GC computed only {} reachable members (< floor) — \
             skipping the prune to avoid a destructive parse error.",
            reach.len()
        );
        return;
    }
    // Repack keeping only reachable members. Extract to scratch, delete the unreachable, `ar rcs`.
    let work = out_dir.join("dregg2_gc_work");
    if work.exists() {
        let _ = std::fs::remove_dir_all(&work);
    }
    if std::fs::create_dir_all(&work).is_err() {
        return;
    }
    if !matches!(Command::new(ar_tool()).arg("x").arg(archive).current_dir(&work).status(), Ok(s) if s.success())
    {
        return;
    }
    let mut kept: Vec<String> = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&work) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if !name.ends_with(".o") {
                continue;
            }
            if reach.contains(&name) {
                kept.push(name);
            } else {
                let _ = std::fs::remove_file(entry.path());
            }
        }
    }
    if kept.is_empty() {
        return;
    }
    kept.sort();
    let tmp = out_dir.join("libdregg_lean.a.gc");
    let _ = std::fs::remove_file(&tmp);
    if !matches!(
        Command::new(ar_tool()).arg("rcs").arg(&tmp).args(&kept).current_dir(&work).status(),
        Ok(s) if s.success()
    ) {
        return;
    }
    let _ = run_ranlib(&tmp);
    if std::fs::rename(&tmp, archive).is_err() {
        // Cross-device rename fallback: copy.
        if std::fs::copy(&tmp, archive).is_ok() {
            let _ = std::fs::remove_file(&tmp);
        } else {
            return;
        }
    }
    println!(
        "cargo:warning=dregg-lean-ffi: archive GC pruned {unreachable} unreachable dependency \
         object(s) (kept {} reachable from the `dregg_*` exports).",
        kept.len()
    );
}

/// **The PRINCIPLED elaborator / proof-time TRIM (docs/EMBEDDABLE-LEAN-RUNTIME.md §4.2).**
///
/// `gc_unreachable_members` keeps every member reachable by ANY undefined-symbol edge — and the
/// per-module `initialize_*` chain is such an edge. So the executor's import closure drags in the
/// initializer of every TRANSITIVELY-imported module: `Dregg2.Exec.Kernel`'s init alone chains into
/// `initialize_Dregg2_Dregg2_Tactics` (→ `initialize_Lean`, the whole elaborator) AND the mathlib
/// `Tactic.Ring` / `Algebra.BigOperators` inits, which in turn chain across ~2600 mathlib members.
/// None of that proof-time code is CALLED by the executor's compute path (`Exec.recKExec` /
/// `execFullForestG`) — it enters ONLY through the init chain. The measured shape: the executor's
/// true runtime-FUNCTION closure is ~960 members / ~67 MB; the init-chain inflates the kept archive
/// to ~3000 members / ~138 MB (the elaborator + the proof-time mathlib/aesop).
///
/// This pass severs the init-chain edge at the SHAPE of the closure. It computes the
/// runtime-function/data reachable set from the `dregg_*` exports (following EVERY edge EXCEPT the
/// `initialize_*` ones, which are the boundary), keeps exactly those members in a separate trimmed
/// archive, and supplies a boundary NO-OP for each runtime-DEAD module initializer the kept members'
/// own init-chains still reference (the same mechanism the seL4 lane proved with `init-stubs.c` —
/// generalized from the single `Dregg2.Tactics` leaf to the whole runtime-dead frontier). The result
/// is a dead-stripped static embed of the VERIFIED executor at a fraction of the size, with the
/// elaborator/Mathlib never init-pulled.
///
/// Soundness: a module is dropped ONLY when no live member references any of its function/data
/// symbols — i.e. the executor never calls into it. Its initializer (which only built proof-time
/// constants) is replaced by an idempotent no-op so the live init-chain still links. The verified
/// `def`s and their proofs are untouched (proofs build in the full metatheory; this trims the RUNTIME
/// embed only). The kernel probe (`embeddable_runtime_probe`) drives a real transfer through the
/// trimmed archive as the empirical safety check. OPT-IN (`DREGG_LEAN_FFI_RUNTIME_TRIM=1`) and written
/// to a SEPARATE archive so the default verified link (node / dregg-turn) is byte-for-byte unchanged.
///
/// Returns `Some(stub_c_path)` when the trim ran — the caller compiles that stub into the whole-archive
/// shim and links `dregg_lean_trim` instead of `dregg_lean`. Returns `None` (fall back to the full
/// archive) on any parse failure / implausibly-small live set / no-members-dead.
fn runtime_dead_init_trim(
    full_archive: &Path,
    trim_archive: &Path,
    out_dir: &Path,
) -> Option<PathBuf> {
    use std::collections::{HashMap, HashSet};
    let out = Command::new(nm_tool())
        .arg("-A")
        .arg(full_archive)
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    // member -> undefined NON-init syms / undefined init syms;  sym -> members defining it.
    let mut undef_func: HashMap<String, HashSet<String>> = HashMap::new();
    let mut undef_init: HashMap<String, HashSet<String>> = HashMap::new();
    let mut sym_def_in: HashMap<String, HashSet<String>> = HashMap::new();
    let mut members: HashSet<String> = HashSet::new();
    let mut roots: HashSet<String> = HashSet::new();
    for line in text.lines() {
        let Some((member, rest)) = nm_archive_member_row(line) else {
            continue;
        };
        let toks: Vec<&str> = rest.split_whitespace().collect();
        let (ty, sym) = match toks.as_slice() {
            [ty, sym] if ty.len() == 1 => (*ty, *sym),
            [_addr, ty, sym] if ty.len() == 1 => (*ty, *sym),
            _ => continue,
        };
        members.insert(member.clone());
        let bare = sym.trim_start_matches('_');
        let is_init = lean_init_suffix(bare).is_some();
        if ty == "U" || ty == "u" {
            if is_init {
                undef_init
                    .entry(member.clone())
                    .or_default()
                    .insert(sym.to_string());
            } else {
                undef_func
                    .entry(member.clone())
                    .or_default()
                    .insert(sym.to_string());
            }
        } else {
            sym_def_in
                .entry(sym.to_string())
                .or_default()
                .insert(member.clone());
            if bare.starts_with("dregg_") {
                roots.insert(member);
            }
        }
    }
    if members.is_empty() || roots.is_empty() {
        println!(
            "cargo:warning=dregg-lean-ffi: runtime trim could not parse members/roots from `nm -A` \
             (members={}, roots={}); refusing to fall back silently.",
            members.len(),
            roots.len()
        );
        return None;
    }

    // RUNTIME-FUNCTION reachability: chase ONLY non-init edges. A module reached purely through an
    // `initialize_*` chain (never by a call/data reference) is runtime-dead and excluded.
    let mut live: HashSet<String> = HashSet::new();
    let mut queue: Vec<String> = roots.iter().cloned().collect();
    while let Some(member) = queue.pop() {
        if !live.insert(member.clone()) {
            continue;
        }
        if let Some(us) = undef_func.get(&member) {
            for u in us {
                if let Some(defs) = sym_def_in.get(u) {
                    for dm in defs {
                        if !live.contains(dm) {
                            queue.push(dm.clone());
                        }
                    }
                }
            }
        }
    }
    // Plausibility floor (mirrors gc_unreachable_members): a misfired parse must not silently
    // produce a tiny broken archive. And if nothing is dead the trim is a no-op — fall back.
    if live.len() < 200 || live.len() >= members.len() {
        return None;
    }

    // The dangling init edges AFTER the trim: an `initialize_*` referenced by a KEPT member but
    // defined only by a DROPPED member needs a boundary no-op so the kept init-chain links.
    // Toolchain inits (Init/Std/Lean/Lake) come from the sysroot static libs the final link pulls,
    // so never no-op those — if a live member genuinely references `initialize_Lean`, let the real
    // (sysroot) init run rather than silently skip it.
    let is_toolchain = |bare: &str| -> bool {
        match lean_init_suffix(bare) {
            Some(rest) => ["Init", "Std", "Lean", "Lake"]
                .iter()
                .any(|lib| rest == *lib || rest.starts_with(&format!("{lib}_"))),
            None => false,
        }
    };
    let mut dangling: HashSet<String> = HashSet::new();
    for m in &live {
        if let Some(us) = undef_init.get(m) {
            for u in us {
                let bare = u.trim_start_matches('_').to_string();
                if is_toolchain(&bare) {
                    continue;
                }
                let defined_by_kept = sym_def_in
                    .get(u)
                    .map(|d| d.iter().any(|dm| live.contains(dm)))
                    .unwrap_or(false);
                if defined_by_kept {
                    continue;
                }
                dangling.insert(bare);
            }
        }
    }

    // Repack the trimmed archive: extract the full archive into scratch, keep only live members.
    let work = out_dir.join("dregg2_runtime_trim_work");
    let _ = std::fs::remove_dir_all(&work);
    std::fs::create_dir_all(&work).ok()?;
    if !matches!(Command::new(ar_tool()).arg("x").arg(full_archive).current_dir(&work).status(), Ok(s) if s.success())
    {
        return None;
    }
    let mut kept: Vec<String> = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&work) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if !name.ends_with(".o") {
                continue;
            }
            if live.contains(&name) {
                kept.push(name);
            } else {
                let _ = std::fs::remove_file(entry.path());
            }
        }
    }
    if kept.is_empty() {
        return None;
    }
    kept.sort();
    let _ = std::fs::remove_file(trim_archive);
    if !matches!(
        Command::new(ar_tool()).arg("rcs").arg(trim_archive).args(&kept).current_dir(&work).status(),
        Ok(s) if s.success()
    ) {
        return None;
    }
    let _ = run_ranlib(trim_archive);
    let _ = std::fs::remove_dir_all(&work);

    // Generate the boundary no-op stub for the runtime-dead module inits the kept chain references.
    let stub = out_dir.join("runtime_trim_init_stubs.c");
    let mut sorted: Vec<&String> = dangling.iter().collect();
    sorted.sort();
    let mut body = String::new();
    body.push_str(
        "/* GENERATED by dregg-lean-ffi/build.rs::runtime_dead_init_trim — the\n\
         * EMBEDDABLE-LEAN-RUNTIME §4.2 principled elaborator/proof-time trim.\n\
         *\n\
         * Boundary no-op initializers for the RUNTIME-DEAD modules (the proof-time tactics, the\n\
         * Lean elaborator, and the mathlib/aesop the verified executor never CALLS) that were\n\
         * dropped from the trimmed archive. The kept (runtime-live) members' own init-chains still\n\
         * reference these symbols; resolving them HERE severs the elaborator/Mathlib init-pull at\n\
         * the closure boundary. Linked +whole-archive, so these win over any archive definition.\n\
         *\n\
         * Init ABI (Lean v4.30.0): lean_object* initialize_X(uint8_t builtin); idempotent. */\n\
         #include <lean/lean.h>\n\
         #define NOOP_INIT(name)                                            \\\n\
           static uint8_t name##_done = 0;                                  \\\n\
           lean_object *name(uint8_t builtin) {                             \\\n\
             (void)builtin;                                                 \\\n\
             if (name##_done) return lean_io_result_mk_ok(lean_box(0));     \\\n\
             name##_done = 1;                                               \\\n\
             return lean_io_result_mk_ok(lean_box(0));                      \\\n\
           }\n",
    );
    for d in &sorted {
        body.push_str(&format!("NOOP_INIT({d})\n"));
    }
    std::fs::write(&stub, body).ok()?;

    println!(
        "cargo:warning=dregg-lean-ffi: RUNTIME TRIM (EMBEDDABLE §4.2) — kept {} runtime-live of {} \
         members (dropped {} runtime-dead: elaborator + proof-time mathlib/aesop), {} boundary init \
         no-ops. Linking libdregg_lean_trim.a.",
        kept.len(),
        members.len(),
        members.len() - kept.len(),
        sorted.len(),
    );
    Some(stub)
}

/// Add (replace) the given objects into the archive, preserving everything else. Like `splice_objects`
/// but for an arbitrary object set (the dependency-closure additions), and incremental — it does NOT
/// re-extract the whole archive; it uses `ar r` to insert/replace members by name, then `ranlib`.
fn add_objects_to_archive(
    archive: &Path,
    objs: &[(String, PathBuf)],
    out_dir: &Path,
) -> std::io::Result<()> {
    // Stage the objects under their archive member names in a scratch dir, then `ar r` them in.
    let stage = out_dir.join("dregg2_closure_stage");
    if stage.exists() {
        std::fs::remove_dir_all(&stage)?;
    }
    std::fs::create_dir_all(&stage)?;
    let mut names = Vec::new();
    for (name, path) in objs {
        std::fs::copy(path, stage.join(name))?;
        names.push(name.clone());
    }
    // `ar r <archive> *.o` inserts or replaces the named members in place (preserving the other
    // ~6100 members). We pass the absolute archive path and run in the stage dir for clean names.
    let r = Command::new(ar_tool())
        .arg("r")
        .arg(archive)
        .args(&names)
        .current_dir(&stage)
        .status()?;
    if !r.success() {
        return Err(std::io::Error::other(format!("`ar r` exited {r}")));
    }
    let _ = run_ranlib(archive);
    let _ = std::fs::remove_dir_all(&stage);
    Ok(())
}

/// Whether the archive contains any `Dregg2_*.o` member (via `ar t`). NOT a splice-completeness
/// predicate on its own — the SEED already has Dregg2 members. See `archive_dregg2_complete`.
fn archive_has_dregg2_member(archive: &Path) -> bool {
    let Ok(out) = Command::new(ar_tool()).arg("t").arg(archive).output() else {
        return false;
    };
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .any(|l| l.trim().starts_with("Dregg2_") && l.trim().ends_with(".o"))
}

/// Whether the archive's Dregg2 slice is COMPLETE: it has `Dregg2_*.o` members AND it exports
/// every symbol in the required-export manifest (`REQUIRED_PQ_CORE_EXPORTS` +
/// `REQUIRED_DECISION_EXPORTS`).
///
/// ⚑ WHY THIS IS NOT `archive_has_dregg2` ANY MORE (the warm-cache silent-degrade generator, fixed
/// 2026-07-24 — `docs/ASSESS-cold-build-silent-export.md` §3.2). The old predicate asked only "does
/// ANY `Dregg2_*.o` member exist", and it drove
///
/// ```text
/// let needs_splice = recompiled || !archive_has_dregg2(archive);
/// ```
///
/// The SEED archive already carries Dregg2 members. So after `seed_build_archive` re-copied the
/// seed over the working archive — WIPING the previously spliced Dregg2 slice — the old predicate
/// answered `true`, and if the persistent `.o` cache was warm (`recompiled == false`) then
/// `needs_splice` was **false**: the build LINKED THE UN-SPLICED SEED while the very objects that
/// define the missing exports sat in `$OUT_DIR/dregg2_closure_objs/`. Every splice-only export was
/// then absent, every `#[cfg(dregg_*_present)]` module compiled out, and the build was green.
/// (Reproduced from disk: three OUT_DIRs sitting at exactly seed level, one of them at the SAME
/// cargo feature hash as a sibling with the full export set.)
///
/// Asking for the EXPORTS rather than for member names is deliberate and is what keeps this cheap
/// and stable: the manifest symbols are `dregg_*` FFI entry points, i.e. exactly the roots the
/// step-5 reachability GC never prunes. A member-set completeness check would go false after every
/// GC (the GC legitimately drops unreachable `Dregg2_*.o`) and would re-splice on every rerun.
fn archive_dregg2_complete(archive: &Path) -> bool {
    archive_has_dregg2_member(archive) && missing_required_exports(archive).is_empty()
}

/// Every `dregg_*` symbol the archive DEFINES, from a single `nm` pass (the leading Mach-O
/// underscore is stripped, so the set is platform-uniform).
fn archive_dregg_exports(archive: &Path) -> std::collections::HashSet<String> {
    let mut found = std::collections::HashSet::new();
    let Ok(out) = Command::new(nm_tool()).arg(archive).output() else {
        return found;
    };
    for line in String::from_utf8_lossy(&out.stdout).lines() {
        // A DEFINED symbol shows in the text section as `<addr> T <name>` — the exact shape
        // `archive_exports` matches one symbol at a time. Mach-O (macOS) mangles the C name with a
        // leading underscore, ELF (Linux) does not; strip it so the set is platform-uniform.
        let trimmed = line.trim_end();
        let Some(idx) = trimmed.rfind(" T ") else {
            continue;
        };
        let sym = trimmed[idx + 3..].trim().trim_start_matches('_');
        if sym.starts_with("dregg_") {
            found.insert(sym.to_string());
        }
    }
    found
}

/// The manifest entries the archive does NOT export, in ONE `nm` pass over both tables.
fn missing_required_exports(archive: &Path) -> Vec<(&'static str, &'static str)> {
    let defined = archive_dregg_exports(archive);
    REQUIRED_PQ_CORE_EXPORTS
        .iter()
        .chain(REQUIRED_DECISION_EXPORTS.iter())
        .filter(|(sym, _)| !defined.contains(*sym))
        .copied()
        .collect()
}

/// The subset of `required` absent from an ALREADY-COMPUTED export set. Takes the set rather than
/// the path so the two gates in `main` share a single `nm` pass over the (~150 MB) archive instead
/// of paying one each — `archive_exports` already runs one pass per probed symbol, so this stays
/// cheap by construction.
fn missing_in(
    defined: &std::collections::HashSet<String>,
    required: &[(&'static str, &'static str)],
) -> Vec<(&'static str, &'static str)> {
    required
        .iter()
        .filter(|(sym, _)| !defined.contains(*sym))
        .copied()
        .collect()
}

/// The set of archive MEMBER names (e.g. `Await.o`, `Dregg2_Spec_Await.o`) that define a project
/// module initializer (`_initialize_Dregg2_*` / `_initialize_Metatheory_*`). Computed with `nm -A`,
/// which prefixes each symbol line with the member location. The prefix format differs by platform:
///   * macOS/llvm-nm: `<archive>:<member.o>: <addr> T <sym>`
///   * GNU/binutils:  `<archive>[<member.o>]: <addr> T <sym>`
///
/// We extract the member by taking the basename of the path segment ending in `.o`, so the splice can
/// purge stale project objects regardless of how they were named when the base archive was seeded.
fn members_defining_project_initializers(archive: &Path) -> std::collections::HashSet<String> {
    let mut members = std::collections::HashSet::new();
    let Ok(out) = Command::new(nm_tool()).arg("-A").arg(archive).output() else {
        return members;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    for line in text.lines() {
        // Only DEFINING (`T`) lines for a project initializer; skip undefined (`U`) references.
        // The C symbol carries a leading `_` on Mach-O (macOS) but NOT on ELF/COFF (Linux,
        // Windows-MinGW), so accept both `T _initialize_*` and `T initialize_*`.
        let is_project_init = |stem: &str| {
            line.contains(&format!("T _{stem}")) || line.contains(&format!("T {stem}"))
        };
        if !(is_project_init("initialize_Dregg2_") || is_project_init("initialize_Metatheory_")) {
            continue;
        }
        let Some((member, _rest)) = nm_archive_member_row(line) else {
            continue;
        };
        members.insert(member);
    }
    members
}

/// Splice the freshly-built `Dregg2_*.o` into `archive`, preserving every non-project dependency
/// object. Extract → purge stale project members (by defined symbol, see above) → drop in the fresh
/// `Dregg2_*.o` → `ar rcs` + `ranlib`. Works in a scratch dir under `OUT_DIR` (writable, local).
fn splice_objects(archive: &Path, obj_dir: &Path, out_dir: &Path) -> std::io::Result<()> {
    let work = out_dir.join("dregg2_splice_work");
    if work.exists() {
        std::fs::remove_dir_all(&work)?;
    }
    std::fs::create_dir_all(&work)?;

    // Extract the existing archive (all ~6100 members) into the scratch dir.
    let extract = Command::new(ar_tool())
        .arg("x")
        .arg(archive)
        .current_dir(&work)
        .status()?;
    if !extract.success() {
        return Err(std::io::Error::other(format!("`ar x` exited {extract}")));
    }

    // Purge EVERY stale project-module object, by DEFINED SYMBOL not just filename. The base archive
    // was historically seeded with SHORT member names (`Await.o`, `Transfer.o`, …) while our splice
    // uses flattened names (`Dregg2_Spec_Await.o`); a filename-only purge would leave the short-named
    // stale copies behind as DUPLICATE definitions — and, when a concurrent edit renames/deletes a
    // module, those stale copies carry dangling references to the old name (the empirical cause of the
    // `_initialize_…burnAWitness` / `_initialize_Metatheory_Metatheory_Core` link failures). So we
    // drop every extracted member that defines a `_initialize_Dregg2_*` or `_initialize_Metatheory_*`
    // symbol, then re-add ONLY the freshly compiled objects.
    let stale_members = members_defining_project_initializers(archive);
    for entry in std::fs::read_dir(&work)?.flatten() {
        let fname = entry.file_name();
        let name = fname.to_string_lossy();
        let is_flattened_project = (name.starts_with("Dregg2_") || name.starts_with("Metatheory_"))
            && name.ends_with(".o");
        if is_flattened_project || stale_members.contains(name.as_ref()) {
            std::fs::remove_file(entry.path())?;
        }
    }
    let mut dregg2_count = 0usize;
    for entry in std::fs::read_dir(obj_dir)?.flatten() {
        let name = entry.file_name();
        let name_s = name.to_string_lossy();
        if name_s.starts_with("Dregg2_") && name_s.ends_with(".o") {
            std::fs::copy(entry.path(), work.join(&name))?;
            dregg2_count += 1;
        }
    }

    // Repack into a fresh archive next to build.rs, then atomically swap it into place. `ar rcs`
    // over the entire member set (Dregg2 + preserved dependency closure) followed by `ranlib`
    // rebuilds the symbol index. We pass the member list explicitly to keep ordering deterministic.
    let members: Vec<PathBuf> = std::fs::read_dir(&work)?
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().map(|e| e == "o").unwrap_or(false))
        .collect();
    if members.is_empty() {
        return Err(std::io::Error::other(
            "no .o members after extract — refusing to repack",
        ));
    }

    let tmp_archive = out_dir.join("libdregg_lean.a.new");
    let _ = std::fs::remove_file(&tmp_archive);
    // `ar rcs <out> *.o` — build with relative paths from `work` to keep member names clean.
    let rel_members: Vec<String> = members
        .iter()
        .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    let rcs = Command::new(ar_tool())
        .arg("rcs")
        .arg(&tmp_archive)
        .args(&rel_members)
        .current_dir(&work)
        .status()?;
    if !rcs.success() {
        return Err(std::io::Error::other(format!("`ar rcs` exited {rcs}")));
    }
    let ranlib = run_ranlib(&tmp_archive);
    // ranlib is advisory: `ar s`/`rcs` already wrote a symbol table on most toolchains. Only warn.
    if !matches!(ranlib, Ok(s) if s.success()) {
        println!(
            "cargo:warning=dregg-lean-ffi: ranlib on the new archive did not succeed (continuing)."
        );
    }

    std::fs::rename(&tmp_archive, archive)?;
    let _ = std::fs::remove_dir_all(&work);
    println!(
        "cargo:warning=dregg-lean-ffi: spliced {dregg2_count} Dregg2 objects into {} ({} total members).",
        archive.display(),
        rel_members.len()
    );
    Ok(())
}

/// Probe the archive for an exported symbol via `nm`, so the C shim only declares string
/// bridges whose underlying Lean `@[export]` actually exists in THIS archive. A stale
/// archive missing a later export (e.g. `dregg_exec_handler_turn`) would otherwise leave a
/// dangling reference that `-dead_strip` resolves by dropping the WHOLE shim object — taking
/// the forest-auth + init bridges with it. We fail-closed: absent ⇒ the bridge is compiled out.
fn archive_exports(archive: &std::path::Path, symbol: &str) -> bool {
    let Ok(out) = Command::new(nm_tool()).arg(archive).output() else {
        return false;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    // A DEFINED symbol shows in the text section as `T <name>`. The C symbol name is mangled
    // with a leading underscore on Mach-O (macOS) but NOT on ELF (Linux), so accept both
    // ` T _<symbol>` and ` T <symbol>`.
    let mach_o = format!(" T _{symbol}");
    let elf = format!(" T {symbol}");
    text.lines()
        .any(|l| l.trim_end().ends_with(&mach_o) || l.trim_end().ends_with(&elf))
}

/// Whether the SHARED link mode is selected (`DREGG_LEAN_LINK=shared`).
///
/// An ENV VAR, deliberately NOT a cargo feature: features UNIFY across a workspace
/// dependency graph (a cdylib member asking for shared linkage would flip every native
/// crate in the same build), while an env var stays local to the invoking build. The one
/// consumer today is the standalone sdk-py workspace (a pyo3 cdylib), whose
/// `.cargo/config.toml` `[env]` sets it.
///
/// WHY a cdylib cannot use the static mode on ELF: rustc BUNDLES `static=`-linked native
/// libraries into the rlib, and `libleanrt.a`'s mimalloc objects (`static.c.o`:
/// `mi_heap_default` & co.) use local-exec TLS — `R_X86_64_TPOFF32` relocations that the
/// linker rejects under `-shared` (Convergence round 7). The Lean toolchain ships the
/// whole runtime+stdlib built FOR shared use as `libleanshared.{so,dylib}` in
/// `$LEAN_SYSROOT/lib/lean`; shared mode links that instead of the static
/// {leancpp,Init,Std,Lean,leanrt,Lake,gmp,uv} set. Our spliced `libdregg_lean.a` is still
/// linked statically in both modes — it holds ONLY Lean-compiled MODULE objects (Dregg2 +
/// the mathlib/batteries/… dependency closure; never runtime members), all compiled
/// `-fPIC`, so its symbols are disjoint from leanshared's.
fn shared_link_mode() -> bool {
    println!("cargo:rerun-if-env-changed=DREGG_LEAN_LINK");
    match std::env::var("DREGG_LEAN_LINK") {
        Ok(v) if v == "shared" => true,
        Ok(v) if v.is_empty() || v == "static" => false,
        Ok(v) => {
            println!(
                "cargo:warning=dregg-lean-ffi: unknown DREGG_LEAN_LINK={v:?} (expected \
                 `shared` or `static`) — defaulting to the static link."
            );
            false
        }
        Err(_) => false,
    }
}

fn main() {
    println!("cargo:rerun-if-env-changed=DREGG_LEANC_JOBS");
    println!("cargo::rustc-check-cfg=cfg(lean_lib_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_lean_stale_archive)");
    println!("cargo::rustc-check-cfg=cfg(dregg_handler_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_finalize_gate_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_strand_admit_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_distributed_exports_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_decide_refines_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_direct_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_storage_content_root_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_fips204_verify_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_fips204_verify_real_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_fips204_sign_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_fips204_sign_real_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_fips203_encaps_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_fips203_decaps_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mlkem_decaps_real_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mlkem_encaps_real_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mlkem_keygen_real_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mldsa_keygen_real_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_grain_r3_verify_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_holding_grant_weight_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_interchain_reached_consensus_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_constraint_admits_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_cross_cell_conserves_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_eth_lc_verify_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_eth_committee_rotation_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_tm_lc_verify_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_tm_skip_verify_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mpt_lc_verify_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mina_lc_verify_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mina_wrap_shape_ok_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mina_proof_chain_ok_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mina_state_hash_word_ok_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mina_better_tip_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mina_head_advance_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mina_checkpoint_advance_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mina_wrap_challenges_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_mina_wrap_ft_eval0_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_fri_ledger_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_automatafl_rules_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_multiway_tug_rules_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_deleg_admit_present)");

    // ── FAIL-LOUD GATE (DREGG_REQUIRE_LEAN) — see docs/BUILD-LEAN-LINKED-NODE.md ─────────────
    // A distribution / CI / validator build REFUSES a silent degrade to the marshal-only shell
    // (`lean_available()==false`, the UN-verified Rust executor). Historically every marshal-only
    // degrade below emitted only a `cargo:warning=…`, which is trivially lost in a release/CI log —
    // so a build whose Lean seed was stale or gitignored could ship as if verified.
    //
    // The gate now has TWO tiers:
    //
    //   * EXPLICIT (`DREGG_REQUIRE_LEAN=1`) — `require_lean`: forces EVERY marshal-only degrade to
    //     a hard build FAILURE, INCLUDING the platform-incapable targets (wasm32 / zkvm /
    //     windows-msvc / no-lean-link). Use it to assert "this build must be a verified node" and
    //     fail loudly if the target can't be one.
    //
    //   * RELEASE-DEFAULT — `require_lean_native`: for a NATIVE, archive-linkable target, a
    //     `--release` (distribution) build defaults the fail-loud gate ON so a release binary can
    //     never SILENTLY ship marshal-only. This covers the archive-absent / sysroot-unresolvable
    //     degrades (the real "ships as verified but isn't" cases). It does NOT fire on the
    //     platform-incapable early return (those targets legitimately can't link Lean; only the
    //     EXPLICIT tier forces them). The opt-out for a deliberately-marshal-only release build
    //     (dev / benchmarks / a non-node crate) is `DREGG_REQUIRE_LEAN=0` (or `false`/`off`).
    //
    //   * TEST-LANE OPT-IN — `DREGG_TEST_REQUIRE_LEAN=1`: the SAME variable `lib.rs`'s
    //     `demand_lean` already reads to turn a runtime self-skip into a panic, now also armed at
    //     BUILD time. Without this, a `cargo test` lane was structurally unable to arm anything:
    //     `cargo test` is a DEBUG build, `require_lean_native` needed `--release`, so an absent /
    //     un-spliced archive emitted a `cargo:warning=` (which cargo HIDES for dependency crates),
    //     returned before every `cargo:rustc-cfg=` below, and each `#[cfg(dregg_*_present)]` test
    //     module simply CEASED TO EXIST. `cargo test -p dregg-lean-ffi --lib` then reported
    //     `11 passed` — not `0` — while all 9 verified-crypto/verified-decision assertions had
    //     evaporated. An opt-in rather than a debug default, because a legitimate local dev build
    //     with no Lean toolchain must keep working; the CI test lane opts in
    //     (`.github/workflows/ci.yml`, the `test` job). `docs/ASSESS-cold-build-silent-export.md`.
    //
    // Debug/dev builds keep the historical warn-and-degrade behavior unless `DREGG_REQUIRE_LEAN=1`
    // or `DREGG_TEST_REQUIRE_LEAN=1`.
    println!("cargo:rerun-if-env-changed=DREGG_REQUIRE_LEAN");
    println!("cargo:rerun-if-env-changed=DREGG_TEST_REQUIRE_LEAN");
    println!("cargo:rerun-if-env-changed=PROFILE");
    let require_lean_env = std::env::var("DREGG_REQUIRE_LEAN").ok();
    let require_lean = matches!(
        require_lean_env.as_deref(),
        Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
    );
    let require_lean_off = matches!(
        require_lean_env.as_deref(),
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF")
    );
    // The test-lane opt-in. Same grammar as DREGG_REQUIRE_LEAN and as `lib.rs`'s
    // `armed_from_env_value`, so "1"/"true"/"on" arm and anything else (including "0") does not.
    let require_lean_test = matches!(
        std::env::var("DREGG_TEST_REQUIRE_LEAN").ok().as_deref(),
        Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
    );
    // Cargo sets PROFILE to "release" for `--release` (and any release-profile) builds.
    let is_release = std::env::var("PROFILE").as_deref() == Ok("release");
    // Native-target release builds — and any lane that opted the test gate in — fail loud on a
    // marshal-only degrade unless explicitly opted out with DREGG_REQUIRE_LEAN=0.
    let require_lean_native =
        require_lean || ((is_release || require_lean_test) && !require_lean_off);
    let degrade_guard = |forced: bool, reason: &str| {
        if forced {
            panic!(
                "dregg-lean-ffi: the Lean-required gate is ACTIVE (DREGG_REQUIRE_LEAN=1, \
                 DREGG_TEST_REQUIRE_LEAN=1, or a --release/distribution build on a native \
                 archive-linkable target) but this build would degrade to MARSHAL-ONLY \
                 (lean_available()==false): {reason}. A marshal-only binary runs the UN-verified \
                 Rust executor and must NEVER ship as a verified node; a marshal-only TEST binary \
                 silently compiles out every #[cfg(dregg_*_present)] module and reports the \
                 remaining tests as green. Fix the cause (usually: install elan+lake and the \
                 mathlib pin, and (re)seed a HEAD-matching dregg-lean-ffi/libdregg_lean.a via \
                 ./scripts/bootstrap.sh, or fetch a prebuilt one with \
                 ./scripts/fetch-lean-seed.sh — the seed must match the current Lean HEAD or the \
                 closure link fails; see docs/BUILD-LEAN-LINKED-NODE.md), or set \
                 DREGG_REQUIRE_LEAN=0 to allow a deliberately-marshal-only (degraded) build."
            );
        }
    };

    // ── PLATFORM GATE (polarity inversion, docs/FEATURE-HYGIENE.md §Lean): the link is
    // UNCONDITIONAL on native; the ONE opt-out is the `no-lean-link` platform feature, set
    // only by builds whose target cannot link libdregg_lean.a (wasm32, the SP1 zkvm guest,
    // and Windows-MSVC). We also hard-skip on those targets regardless of the feature — a
    // build that forgot to wire `no-lean-link` should degrade to the marshal-only stubs,
    // never attempt a native-archive link. No archive refresh, no shim, no link directives:
    // the crate builds marshal-only and `lean_available()` is false.
    //
    // WINDOWS — TWO DISTINCT TARGETS, only ONE links (measured empirically, docs/desktop-os-
    // research/WINDOWS-PORT.md §lever):
    //
    //   * `x86_64-pc-windows-MSVC` — HARD WALL, hard-skips. The Lean Windows toolchain is the
    //     LLVM-MinGW distribution (`x86_64-w64-windows-gnu`); it ships its runtime+stdlib ONLY
    //     as MinGW `.a` archives of GNU-flavoured `coff-x86-64` objects. MSVC `link.exe`
    //     STRUCTURALLY cannot consume those — every precompiled runtime member (e.g.
    //     `libleanrt.a(object.cpp.obj)`) triggers `LNK1143: no symbol for COMDAT section`
    //     (the GNU-vs-MSVC COMDAT encoding divergence). No MSVC-ABI Lean runtime exists, so an
    //     MSVC native-full build can only be the marshal-only shell. Skip ⇒ `lean_available()==false`.
    //
    //   * `x86_64-pc-windows-GNU` — THE LEVER, proceeds. The MinGW ABI matches the Lean toolchain
    //     exactly: the spliced archive is a GNU `.a` of `coff-x86-64` objects, driven by the LLVM
    //     `llvm-ar`/`llvm-nm`/`leanc` trio (see `ar_tool`/`nm_tool`), and the final link pulls the
    //     Lean MinGW system-lib closure + an ntdll import-lib shim (see `windows_gnu_link_env`).
    //     A trivial Rust-gnu binary statically linking the real Lean runtime LINKS AND RUNS the
    //     embedded `lean_initialize_runtime_module()` under Windows-on-ARM x64 emulation.
    //
    // wasm32 and the SP1 zkvm guest always skip (no native archive at all). The `no-lean-link`
    // platform feature is the explicit opt-out. See docs/FEATURE-HYGIENE.md §Lean.
    let no_lean_link = std::env::var_os("CARGO_FEATURE_NO_LEAN_LINK").is_some();
    let gate_arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    let gate_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let gate_env = std::env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();
    let windows_msvc = gate_os == "windows" && gate_env != "gnu";
    if no_lean_link || gate_arch == "wasm32" || gate_os == "zkvm" || windows_msvc {
        // Platform-incapable targets legitimately cannot link Lean — only the EXPLICIT tier
        // (DREGG_REQUIRE_LEAN=1) forces a failure here, NOT the release-default.
        degrade_guard(
            require_lean,
            &format!(
                "target {gate_arch}/{gate_os} (env {gate_env}) cannot link libdregg_lean.a \
             (no-lean-link feature / wasm32 / zkvm / windows-msvc) — a verified node must be \
             built for a native archive-linkable target"
            ),
        );
        return;
    }

    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR set by cargo"));
    // The git-tracked SEED archive (read-only input; a `cargo build` never writes it).
    let seed_archive = crate_dir.join("libdregg_lean.a");
    // The per-OUT_DIR WORKING archive: where splice / closure-completion / GC happen and
    // what we link against. Per-(crate,feature-set,profile) ⇒ concurrent multi-feature
    // lanes never tear a shared file. See the SWARM-SAFE ARCHIVE note at the top of file.
    let build_archive = out_dir.join("libdregg_lean.a");
    // The SEPARATE trimmed archive (the EMBEDDABLE §4.2 elaborator/proof-time trim). Written ONLY
    // when `DREGG_LEAN_FFI_RUNTIME_TRIM=1`; the default link never touches it, so the verified node /
    // dregg-turn closure is byte-for-byte unchanged.
    let trim_archive = out_dir.join("libdregg_lean_trim.a");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/lean_init.c");
    println!("cargo:rerun-if-changed=src/lean_init_st.cpp");
    // OPT-IN runtime trim. rerun-if-env-changed so toggling it re-runs build.rs (and re-derives the
    // trimmed archive / restores the full link).
    println!("cargo:rerun-if-env-changed=DREGG_LEAN_FFI_RUNTIME_TRIM");
    let runtime_trim_requested = std::env::var("DREGG_LEAN_FFI_RUNTIME_TRIM").as_deref() == Ok("1");

    // Resolve the toolchain + metatheory location up front so we can both (a) refresh the archive
    // from the Lean source when it changed and (b) drive the link below. `lean_sysroot()` honours
    // `DREGG_LEAN_SYSROOT`; `metatheory_dir()` honours `DREGG_METATHEORY_DIR`.
    let sysroot_opt = lean_sysroot();
    let meta_opt = metatheory_dir();

    // ── SEED the per-OUT_DIR working archive from the seed (read-only input, NOT in git). This
    // copies the seed into `$OUT_DIR/libdregg_lean.a` once (and re-copies whenever the seed is
    // newer than the working copy, e.g. after an out-of-band re-seed). All splice / closure /
    // GC mutation below targets `build_archive`, never the seed — so concurrent multi-feature
    // lanes never tear the shared file. `cargo:rerun-if-changed` on the seed re-runs build.rs
    // when the seed is re-produced out-of-band, picking up the fresh base.
    //
    // `reseeded` is load-bearing: a re-copy WIPES the working archive's spliced Dregg2 slice, so it
    // must force the re-splice below even when the persistent `.o` cache is warm.
    println!("cargo:rerun-if-changed={}", seed_archive.display());
    let reseeded = seed_build_archive(&seed_archive, &build_archive);

    // ⚑ PROVENANCE, not merely PRESENCE. Set by every path that leaves an archive which is NOT
    // built from this checkout's Lean source. Consumed by the provenance gate below, which then
    // refuses to emit `lean_lib_present` / any `dregg_*_present` — see that gate for the wound.
    let mut provenance_downgraded = false;

    // ── PRODUCE / REFRESH the archive from the Lean source (the linchpin). We watch the whole
    // `metatheory/Dregg2` source tree + the toolchain marker; when any of those change, build.rs
    // reruns and `build_dregg2_archive` does the incremental `lake build` → `leanc -c` → `ar`
    // splice INTO THE PER-OUT_DIR WORKING ARCHIVE. A genuine no-op cargo build does NOT rerun
    // build.rs (no watched file changed), so the ~6000-object closure is never needlessly
    // regenerated. The working archive (`build_archive`) is our OWN per-build output; we do not
    // `rerun-if-changed` it (it lives in OUT_DIR and watching it would loop).
    if let Some(meta) = &meta_opt {
        let mut watched = Vec::new();
        collect_files(&meta.join("Dregg2"), &mut watched);
        for f in &watched {
            println!("cargo:rerun-if-changed={}", f.display());
        }
        println!(
            "cargo:rerun-if-changed={}",
            meta.join("lean-toolchain").display()
        );

        match &sysroot_opt {
            Some(sysroot) => {
                provenance_downgraded = build_dregg2_archive(
                    meta,
                    sysroot,
                    &build_archive,
                    &out_dir,
                    &seed_archive,
                    require_lean_native,
                    reseeded,
                );
            }
            None if require_lean_native => panic!(
                "dregg-lean-ffi: DREGG_REQUIRE_LEAN/current release gate cannot resolve the Lean \
                 sysroot (no DREGG_LEAN_SYSROOT and `lake env` failed in metatheory/); refusing to \
                 reuse an older archive as current-source evidence. Install the pinned Lean \
                 toolchain/mathlib dependencies or provide DREGG_LEAN_SYSROOT."
            ),
            None => {
                // No toolchain ⇒ the archive was NOT refreshed from this checkout, whatever it is.
                provenance_downgraded = true;
                println!(
                    "cargo:warning=dregg-lean-ffi: cannot resolve the Lean sysroot (no \
                     DREGG_LEAN_SYSROOT and `lake env` failed in metatheory/) — skipping the \
                     archive refresh; the existing archive (if any) is used as-is. The two common \
                     causes: (1) elan/lake is not installed or not on PATH; (2) the mathlib \
                     LOCAL-PATH dependency pinned in metatheory/lakefile.toml is missing on this \
                     machine. `./scripts/bootstrap.sh` (repo root) checks both and teaches the \
                     exact fix."
                );
            }
        }
    } else {
        // No metatheory/ at all ⇒ nothing could have been refreshed from source.
        provenance_downgraded = true;
        println!(
            "cargo:warning=dregg-lean-ffi: metatheory/ not found (set DREGG_METATHEORY_DIR) — \
             cannot refresh libdregg_lean.a from Lean source; using the existing archive if present."
        );
    }

    if !build_archive.exists() {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a absent (no git-tracked seed AND no \
             prior per-OUT_DIR working archive) — building MARSHAL-ONLY: lean_available() will be \
             false and the node falls back to the UNVERIFIED Rust executor. To link the verified \
             Lean kernel, run `./scripts/bootstrap.sh` from the repo root (one command: it checks \
             elan + the mathlib pin, lake-builds the executor, seeds the archive once, and \
             verifies the link). Afterwards plain `cargo build` copies the seed into OUT_DIR and \
             keeps its Dregg2 slice fresh automatically."
        );
        // The real "ships as verified but isn't" case on a native target — the release-default
        // tier fails loud here so a distribution binary can never silently be marshal-only.
        degrade_guard(
            require_lean_native,
            "libdregg_lean.a absent — no seed and no prior per-OUT_DIR working archive (run \
             ./scripts/bootstrap.sh to lake-build + seed the Lean archive)",
        );
        return;
    }

    // Resolve the Lean sysroot BEFORE committing to the `lean_lib_present` cfg: linking the
    // archive requires the Lean runtime/stdlib from the toolchain. If we cannot find it, we must
    // NOT advertise `lean_lib_present` (that cfg drives `lean_available()` and the FFI link), or
    // the build would either fail to link or falsely claim the Lean kernel is available.
    let Some(sysroot) = sysroot_opt else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a present but could not resolve the Lean \
             sysroot (no DREGG_LEAN_SYSROOT and `lake env` failed) — building marshal-only. \
             Install elan + the project toolchain (`./scripts/bootstrap.sh` checks everything \
             and teaches the fix), or set DREGG_LEAN_SYSROOT to the toolchain root."
        );
        degrade_guard(
            require_lean_native,
            "the Lean sysroot could not be resolved (no DREGG_LEAN_SYSROOT and `lake env` failed) \
             — install elan + the pinned toolchain so the archive can be linked",
        );
        return;
    };
    let lean_lib = sysroot.join("lib").join("lean");
    let lean_include = sysroot.join("include");

    // ── ⚑ PROVENANCE GATE — A STALE ARCHIVE MAY NOT BE ADVERTISED AS A VERIFIED RUNTIME ─────────
    //
    // The archive exists and the toolchain resolves, but it was NOT produced from this checkout
    // (`build_dregg2_archive` returned a downgrade: the Lean build was skipped, could not run,
    // failed to elaborate, failed to compile a facet, or failed to splice). Until 2026-07-28 that
    // situation emitted a `cargo:warning` and then fell straight through to the export probes
    // below — which duly found `dregg_blocklace_finalize` in the OLD archive and emitted
    // `dregg_finalize_gate_present`. So `finality_gate_available()` returned TRUE, `demand_lean`
    // did not refuse, and the verified-rule tests RAN — against a rule from another day.
    //
    // MEASURED, and it cost a full investigation. `node/src/finality_gate.rs`'s enrollment
    // falsifier fired with "the VERIFIED rule FINALIZED a block (seq 0) created by an UNENROLLED
    // identity — The gate is OPEN", `5 passed; 1 failed`, all three of its anti-vacuity guards
    // passing, on a tree where the gate is CLOSED and green. The linked archive was 3 days old and
    // predated `c6f00c228` — the commit that put `enrolledId` in the rule — and carried ZERO
    // `enrolledId` symbols. The falsifier was correct about what it was handed. It was handed the
    // wrong rule. A stale archive and a broken verified rule produced the SAME observation, and the
    // only thing distinguishing them was a `cargo:warning`, which cargo HIDES for dependency
    // crates — and `dregg-lean-ffi` is a dependency of everything that tests a verified gate.
    //
    // So the downgrade is now carried in the ONE channel the test can read: the cfgs are withheld.
    // `lean_available()` and every `*_available()` go FALSE, and `demand_lean` — ARMED BY DEFAULT —
    // turns each verified-gate test into a loud, correctly-named refusal instead of a verdict about
    // last week's Lean. That is strictly a subtraction: it removes claims, it weakens no check.
    // (This is also the FALSE-GREEN direction: a stale archive could equally have hidden a real
    // regression by passing. Both readings are now refused.)
    if provenance_downgraded {
        degrade_guard(
            require_lean_native,
            "the linked libdregg_lean.a was NOT built from this checkout's Lean source (see the \
             VERIFIED-RUNTIME PROVENANCE DOWNGRADE warning above) — a verified node must link the \
             Lean it ships",
        );
        println!("cargo:rustc-cfg=dregg_lean_stale_archive");
        return;
    }

    println!("cargo:rustc-cfg=lean_lib_present");

    // ── THE PRINCIPLED ELABORATOR / PROOF-TIME TRIM (docs/EMBEDDABLE-LEAN-RUNTIME.md §4.2) ──
    // OPT-IN (`DREGG_LEAN_FFI_RUNTIME_TRIM=1`): derive a SEPARATE trimmed archive holding only the
    // executor's runtime-FUNCTION closure (the elaborator + proof-time mathlib/aesop, reachable only
    // via the per-module init-chain, are dropped), plus a boundary no-op stub for the dead inits the
    // kept chain references. Returns the stub path on success; falls back to the full archive on any
    // snag. The DEFAULT (env unset) path skips this entirely — the verified link is unchanged.
    let runtime_trim_stub = if runtime_trim_requested {
        runtime_dead_init_trim(&build_archive, &trim_archive, &out_dir)
    } else {
        None
    };

    // Report a probe MISS uniformly, reading the consequence straight out of the required-export
    // manifest so there is ONE source of truth. Fourteen of the probes below used to be a bare
    // `if present { println!("cargo:rustc-cfg=…") }` with NO `else` at all — an absent export left
    // literally no trace anywhere in the build, not even the (already-hidden) warning stream. The
    // HARD failure is the manifest gate further down; this is the visible-in-`-vv` half.
    let absent_export_warn = |symbol: &str| {
        let consequence = REQUIRED_PQ_CORE_EXPORTS
            .iter()
            .chain(REQUIRED_DECISION_EXPORTS.iter())
            .find(|(s, _)| *s == symbol)
            .map(|(_, c)| *c)
            .unwrap_or("the Rust extern + C shim bridge it gates is compiled out");
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `{symbol}` — {consequence}. \
             Re-splice a current archive (./scripts/bootstrap.sh) or fetch a HEAD-matching seed \
             (./scripts/fetch-lean-seed.sh). To make this a BUILD FAILURE instead of a warning, \
             build --release or set DREGG_REQUIRE_LEAN=1 / DREGG_TEST_REQUIRE_LEAN=1."
        );
    };

    // The handler-cutover export is the credential-preserving handler-registry shadow. Older
    // archives predate its safe (non-`eraseAuth`) ABI, so a non-strict developer build may compile
    // the bridge out. A Lean-required/current release build must contain it: silently linking an
    // older archive would claim handler-cutover coverage that the binary cannot exercise.
    let handler_present = archive_exports(&build_archive, "dregg_exec_handler_turn");
    if handler_present {
        println!("cargo:rustc-cfg=dregg_handler_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_exec_handler_turn` — \
             the credential-preserving handler-cutover bridge is compiled out (forest-auth gate \
             unaffected). Rebuild the current Lean archive to enable shadow_exec_handler_turn."
        );
        if require_lean_native {
            panic!(
                "dregg-lean-ffi: the Lean-required/current release gate requires the safe \
                 `dregg_exec_handler_turn` export, but the linked archive lacks it. Refusing to \
                 advertise a verified handler cutover backed only by an older seed; rebuild \
                 Dregg2.Exec.FFI from this checkout and splice the current object."
            );
        }
    }

    // The verified FINALITY GATE export (`dregg_blocklace_finalize`) lives in
    // `Dregg2.Distributed.FinalityGate`, a module OUTSIDE the FFI module's import closure. The
    // archive splice compiles every `Dregg2/**/*.c` present in the IR tree, so once the module has
    // been `lake build`- t its object is spliced in and this symbol appears. Until then (e.g. a
    // stale archive) we compile the bridge out and the node falls back to the un-gated path.
    let finalize_gate_present = archive_exports(&build_archive, "dregg_blocklace_finalize");
    if finalize_gate_present {
        println!("cargo:rustc-cfg=dregg_finalize_gate_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_blocklace_finalize` — \
             the verified finality-gate bridge is compiled out (executor gate unaffected). \
             Rebuild the archive (it splices Dregg2.Distributed.FinalityGate) to enable the gate."
        );
    }

    // The verified STRAND-ADMISSION GATE export (`dregg_strand_admit`) lives in
    // `Dregg2.Distributed.StrandAdmission`, also OUTSIDE the FFI module's import closure. Same
    // splice/probe discipline as the finality gate: once the module is `lake build`-t its object is
    // spliced in (the self-linking closure follows the C shim's `initialize_…_StrandAdmission` ref)
    // and this symbol appears; until then we compile the bridge out and the federation falls back to
    // the Rust admission gate.
    let strand_admit_present = archive_exports(&build_archive, "dregg_strand_admit");
    if strand_admit_present {
        println!("cargo:rustc-cfg=dregg_strand_admit_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_strand_admit` — \
             the verified strand-admission bridge is compiled out (federation falls back to the \
             Rust gate). Rebuild the archive (it splices Dregg2.Distributed.StrandAdmission) to \
             enable the Lean-backed F-4 admission gate."
        );
    }

    // The verified CapTP+coord DISTRIBUTED-EXPORTS module (`dregg_captp_validate_handoff` and its five
    // siblings) lives in `Dregg2.Exec.DistributedExports`, also OUTSIDE the FFI module's import
    // closure. Same splice/probe discipline: once the module is `lake build`-t its object is spliced
    // in (the self-linking closure follows the C shim's `initialize_…_DistributedExports` ref) and the
    // symbols appear; until then we compile the six bridges out and the captp/coord runtime falls back
    // to its native Rust gates. We probe a single representative export — they are all defined in the
    // same module, so they are present/absent together.
    let distributed_exports_present =
        archive_exports(&build_archive, "dregg_captp_validate_handoff");
    if distributed_exports_present {
        println!("cargo:rustc-cfg=dregg_distributed_exports_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_captp_validate_handoff` — \
             the verified CapTP+coord decision bridges are compiled out (captp/coord fall back to \
             native Rust gates). Rebuild the archive (it splices Dregg2.Exec.DistributedExports) to \
             enable the Lean-backed handoff / GC-drop / pipeline / 2PC / causal / shared-budget gates."
        );
    }

    // The verified FLOW-REFINEMENT DECISION export (`dregg_decide_refines`) lives in
    // `Dregg2.Deos.FlowRefine`, also OUTSIDE the FFI module's import closure. Same splice/probe
    // discipline: once the module is `lake build`-t (it is in `lake_targets` above) its object is
    // spliced in (the self-linking closure follows the C shim's `initialize_…_FlowRefine` ref) and
    // the symbol appears; until then the `dregg_decide_refines_str` bridge is compiled out and
    // `dregg-deploy/src/refine.rs` falls back to its in-process σ-free mirror of `decideRefines`.
    let decide_refines_present = archive_exports(&build_archive, "dregg_decide_refines");
    if decide_refines_present {
        println!("cargo:rustc-cfg=dregg_decide_refines_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_decide_refines` — \
             the verified flow-refinement decision bridge is compiled out (dregg-deploy's refine \
             gate falls back to its in-process mirror). Rebuild the archive (it splices \
             Dregg2.Deos.FlowRefine) to run the PROVEN decideRefines at the deploy gate."
        );
    }

    // `Dregg2.Exec.DeployedConstraint` is outside the main FFI import closure.
    // Probe before emitting either the Rust extern or C bridge so a stale archive
    // degrades to the existing Rust evaluator without leaving a dangling symbol.
    let constraint_admits_present = archive_exports(&build_archive, "dregg_constraint_admits");
    if constraint_admits_present {
        println!("cargo:rustc-cfg=dregg_constraint_admits_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_constraint_admits` — \
             the verified deployed-constraint evaluator bridge is compiled out (the ConstraintOracle \
             install is unavailable; the pure-subset admission stays on the Rust guest-path evaluator). \
             Rebuild the archive to run the proven Lean evaluator."
        );
    }

    // `Dregg2.Circuit.CrossCellConserveDecision` (the runtime per-asset `Σδ=0` conservation decision)
    // is outside the main FFI import closure. Probe before emitting the Rust extern + C bridge so a stale
    // archive lacking the export leaves the CONSERVATION ORACLE uninstallable — and the deployed
    // executor's conservation gate fails CLOSED (`PerAssetConservationViolation`) on a full node rather
    // than silently reviving the hand-written Rust `BlockConservation` twin. Its refinement against the
    // committed AIR is `CrossCellConserveRefine.decision_conserves_iff_air_boundary`.
    let cross_cell_conserves_present =
        archive_exports(&build_archive, "dregg_cross_cell_conserves");
    if cross_cell_conserves_present {
        println!("cargo:rustc-cfg=dregg_cross_cell_conserves_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_cross_cell_conserves` — \
             the verified cross-cell conservation decision bridge is compiled out (the conservation \
             oracle is uninstallable; a full node's per-asset Σδ=0 gate fails closed). Rebuild the \
             archive (it splices Dregg2.Circuit.CrossCellConserveDecision) to run the proven Lean \
             conservation decision."
        );
    }

    // The NO-COPY DIRECT boundary export (`dregg_exec_full_forest_auth_direct`) + its builder/reader
    // family live in `Dregg2.Exec.FFIDirect`. FFIDirect IMPORTS `Dregg2.Exec.FFI` (not the reverse),
    // so its module initializer is OUTSIDE the FFI closure: `dregg_ffi_init` must run
    // `initialize_Dregg2_Dregg2_Exec_FFIDirect` explicitly (gated on DREGG_DIRECT in the C shim).
    // We probe + gate the Rust `extern "C"` block AND the C shim define so a stale archive lacking the
    // export degrades to the JSON path rather than dangling at link time.
    let direct_present = archive_exports(&build_archive, "dregg_exec_full_forest_auth_direct");
    if direct_present {
        println!("cargo:rustc-cfg=dregg_direct_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_exec_full_forest_auth_direct` \
             — the no-copy direct boundary is compiled out (the JSON marshalling path is used). \
             Rebuild the archive (it splices Dregg2.Exec.FFIDirect) to enable the lean_object* path."
        );
    }

    // Compile the C init shim (it uses the `static inline` runtime helpers from
    // <lean/lean.h>, which have no linkable symbol and so must be used from C).
    //
    // We suppress cc's automatic `rustc-link-lib` directive (`cargo_metadata(false)`)
    // and emit our own `+whole-archive` directive below. Reason: the final link runs
    // under `-Wl,-dead_strip` with `-nodefaultlibs`, and on macOS ld64 the shim's
    // single object is otherwise dead-stripped before the linker has recorded the
    // binary's undefined references to `dregg_ffi_init` / `dregg_exec_full_forest_auth_str`
    // (an archive-member-ordering hazard). Forcing the whole archive in guarantees the
    // bridge symbols are present regardless of link order — the empirical fix for the
    // `marshal_roundtrip` / `full_turn_differential` link failures.
    let storage_content_root_present =
        archive_exports(&build_archive, "dregg_storage_content_root");
    if storage_content_root_present {
        println!("cargo:rustc-cfg=dregg_storage_content_root_present");
    } else {
        absent_export_warn("dregg_storage_content_root");
    }

    // FIPS-204-VERIFY extraction: probe the spliced archive for the `@[export] dregg_fips204_verify`
    // symbol (the extracted, Lean-verified ML-DSA verify core). Present ⇒ gate the Rust `extern "C"`
    // block, the C shim string bridge, and the module initializer.
    let fips204_verify_present = archive_exports(&build_archive, "dregg_fips204_verify");
    if fips204_verify_present {
        println!("cargo:rustc-cfg=dregg_fips204_verify_present");
    } else {
        absent_export_warn("dregg_fips204_verify");
    }

    // FIPS-204-VERIFY-REAL extraction (BRICK 8): probe the spliced archive for the
    // `@[export] dregg_fips204_verify_real` symbol — the FULL-BYTE, full-dimension ML-DSA-65 verify
    // (`MlDsaVerifyReal.verifyCore` over the real 1952/3309-byte key/signature, not the `A=id` scalar
    // toy). Co-located in `Dregg2.Crypto.Fips204Verify`, so its initializer is the SAME
    // `initialize_Dregg2_Dregg2_Crypto_Fips204Verify` already run under DREGG_FIPS204_VERIFY. Present ⇒
    // gate the Rust `extern "C"` block, the C shim string bridge, and the module define. This is the
    // export `dregg-pq::ml_dsa_verify` routes through to take the `fips204` crate OUT of the verify TCB.
    let fips204_verify_real_present = archive_exports(&build_archive, "dregg_fips204_verify_real");
    if fips204_verify_real_present {
        println!("cargo:rustc-cfg=dregg_fips204_verify_real_present");
    } else {
        absent_export_warn("dregg_fips204_verify_real");
    }

    // FIPS-204-SIGN extraction: probe the spliced archive for the `@[export] dregg_fips204_sign`
    // symbol (the extracted, Lean-verified ML-DSA sign core — the Fiat–Shamir-with-aborts signer,
    // co-located in `Dregg2.Crypto.Fips204Verify` with the verify core). Present ⇒ gate the Rust
    // `extern "C"` block, the C shim string bridge, and the module define. Its initializer is the SAME
    // `initialize_Dregg2_Dregg2_Crypto_Fips204Verify` the verify core uses (same module), run under
    // DREGG_FIPS204_VERIFY, so no separate init is needed.
    let fips204_sign_present = archive_exports(&build_archive, "dregg_fips204_sign");
    if fips204_sign_present {
        println!("cargo:rustc-cfg=dregg_fips204_sign_present");
    } else {
        absent_export_warn("dregg_fips204_sign");
    }

    // FIPS-204-SIGN-REAL extraction (the brick-8 SIGN analog): probe the spliced archive for the
    // `@[export] dregg_fips204_sign_real` symbol — the FULL-BYTE, full-dimension ML-DSA-65 sign
    // (`MlDsaSignReal.signCore` over the real 4032/3309-byte key/signature, not the `A=id` scalar toy).
    // Its module is `Dregg2.Crypto.MlDsaSignReal` (its OWN module, distinct from `Fips204Verify`), so like
    // the K6 decaps core DREGG_FIPS204_SIGN_REAL gates BOTH the per-export extern+bridge AND the module
    // initializer. Present ⇒ gate the Rust `extern "C"` block, the C shim string bridge, and the module init.
    let fips204_sign_real_present = archive_exports(&build_archive, "dregg_fips204_sign_real");
    if fips204_sign_real_present {
        println!("cargo:rustc-cfg=dregg_fips204_sign_real_present");
    } else {
        absent_export_warn("dregg_fips204_sign_real");
    }

    // FIPS-203-KEM extraction: probe the spliced archive for the `@[export] dregg_fips203_encaps` /
    // `dregg_fips203_decaps` symbols (the extracted, Lean-verified ML-KEM encaps/decaps cores). Present ⇒
    // gate the Rust `extern "C"` block, the C shim string bridges, and the module initializer. Both are
    // co-located in `Dregg2.Crypto.Fips203Kem`, so a single module define/init serves both.
    let fips203_encaps_present = archive_exports(&build_archive, "dregg_fips203_encaps");
    if fips203_encaps_present {
        println!("cargo:rustc-cfg=dregg_fips203_encaps_present");
    } else {
        absent_export_warn("dregg_fips203_encaps");
    }
    let fips203_decaps_present = archive_exports(&build_archive, "dregg_fips203_decaps");
    if fips203_decaps_present {
        println!("cargo:rustc-cfg=dregg_fips203_decaps_present");
    } else {
        absent_export_warn("dregg_fips203_decaps");
    }

    // ML-KEM-768-DECAPS-REAL extraction (BRICK K6): probe the spliced archive for the
    // `@[export] dregg_mlkem_decaps_real` symbol — the FULL-BYTE, full-dimension ML-KEM-768 decaps
    // (`Dregg2.Crypto.MlKemDecaps.mlkemDecapsRealFFI` over `mlkemDecaps`, the real 2400/1088-byte dk/ct FO
    // pipeline, not the `A=1,n=1` scalar toy). Its module is `Dregg2.Crypto.MlKemDecaps` (its OWN module, a
    // separate initializer from `Fips203Kem`). Present ⇒ gate the Rust `extern "C"` block, the C shim string
    // bridge, and the module define/init. This is the export `dregg-pq::HybridResponder::finish` routes
    // through to take the `ml-kem` crate OUT of the deployed KEM-decaps TCB.
    let mlkem_decaps_real_present = archive_exports(&build_archive, "dregg_mlkem_decaps_real");
    if mlkem_decaps_real_present {
        println!("cargo:rustc-cfg=dregg_mlkem_decaps_real_present");
    } else {
        absent_export_warn("dregg_mlkem_decaps_real");
    }

    // ML-KEM-768-ENCAPS-REAL extraction (BRICK K5 — the ENCAPS mirror of K6): probe the spliced archive for
    // the `@[export] dregg_mlkem_encaps_real` symbol — the FULL-BYTE, full-dimension ML-KEM-768 encaps
    // (`Dregg2.Crypto.MlKemEncaps.mlkemEncapsRealFFI` over `mlkemEncaps`, the deterministic FIPS 203 Alg 16 FO
    // encaps over the real 1184/1088-byte ek/ct, not the `A=1,n=1` scalar toy). Its module is
    // `Dregg2.Crypto.MlKemEncaps` (its OWN module, a separate initializer from `MlKemDecaps`/`Fips203Kem`).
    // Present ⇒ gate the Rust `extern "C"` block, the C shim string bridge, and the module define/init. This is
    // the export `dregg-pq::hybrid_kem::initiate` routes through to take the `ml-kem` crate OUT of the encaps TCB.
    let mlkem_encaps_real_present = archive_exports(&build_archive, "dregg_mlkem_encaps_real");
    if mlkem_encaps_real_present {
        println!("cargo:rustc-cfg=dregg_mlkem_encaps_real_present");
    } else {
        absent_export_warn("dregg_mlkem_encaps_real");
    }

    // ML-KEM-768-KEYGEN-REAL extraction (BRICK K7 — the KEYGEN mirror of K5/K6): probe the spliced archive
    // for the `@[export] dregg_mlkem_keygen_real` symbol — the FULL-BYTE, full-dimension ML-KEM-768 keygen
    // (`Dregg2.Crypto.MlKemKeygen.mlkemKeygenRealFFI` over `mlkemKeygen`, the deterministic FIPS 203
    // ML-KEM.KeyGen_internal from a 64-byte (d ‖ z) seed, KAT-anchored vs NIST ACVP keyGen). Its module is
    // `Dregg2.Crypto.MlKemKeygen` (its OWN module, a separate initializer from MlKemDecaps/MlKemEncaps).
    // Present ⇒ gate the Rust `extern "C"` block, the C shim string bridge, and the module define/init. This
    // is the export `dregg-pq::ml_kem768_keygen` routes through to take the `ml-kem` crate OUT of the keygen TCB.
    let mlkem_keygen_real_present = archive_exports(&build_archive, "dregg_mlkem_keygen_real");
    if mlkem_keygen_real_present {
        println!("cargo:rustc-cfg=dregg_mlkem_keygen_real_present");
    } else {
        absent_export_warn("dregg_mlkem_keygen_real");
    }

    // ML-DSA-65-KEYGEN-REAL extraction (the identity-key KEYGEN mirror): probe the spliced archive for the
    // `@[export] dregg_mldsa_keygen_real` symbol — the FULL-BYTE, full-dimension ML-DSA-65 keygen
    // (`Dregg2.Crypto.MlDsaKeygen.mldsaKeygenRealFFI` over `mldsaKeygenInternal`, the deterministic FIPS 204
    // ML-DSA.KeyGen_internal from a 32-byte ξ seed, KAT-anchored vs NIST ACVP ML-DSA-65 keyGen). Present ⇒
    // gate the Rust `extern "C"` block, the C shim string bridge, and the module define/init. This is the
    // export `dregg-pq::MlDsaKey::from_ed25519_seed` routes through to take the `fips204` crate OUT of the
    // IDENTITY-KEY keygen TCB.
    let mldsa_keygen_real_present = archive_exports(&build_archive, "dregg_mldsa_keygen_real");
    if mldsa_keygen_real_present {
        println!("cargo:rustc-cfg=dregg_mldsa_keygen_real_present");
    } else {
        absent_export_warn("dregg_mldsa_keygen_real");
    }

    // ── PQ-CORE EXPORT GATE (DREGG_REQUIRE_PQ_CORES) ────────────────────────────────────────
    // The DREGG_REQUIRE_LEAN gate above asks only "is a Lean archive linked at all"
    // (`lean_available()`). That question passes for an archive that links perfectly and
    // exports ZERO verified PQ cores — which is EXACTLY the state of the git-tracked
    // `dregg-lean-ffi/libdregg_lean.a` seed (`nm -g --defined-only` finds 0 of the 3). The
    // existing gate therefore does not see the failure that actually matters here.
    //
    // In such a build every `*_real_core_available()` probe returns false, each
    // `dregg_pq::install_verified_*` returns `ExportAbsent`, and `dregg-pq` answers
    // security-critical operations with the UNAUDITED `fips204` 0.4 / `ml-kem` 0.2.3 crates.
    // Nothing errors. The build is green. The deployed binary runs crypto nobody audited.
    //
    // Worse, EVERY degrade path in `build_dregg2_archive` above (a `lake build` failure, a
    // `leanc` failure, an archive-splice failure, an absent base archive) reports itself with
    // `cargo:warning=` and then `return`s to the seed — and cargo HIDES build-script warnings
    // for dependency crates unless you pass `-vv`. The degrade is invisible in a normal log.
    //
    // This gate checks the ARTIFACT rather than the control flow: it re-probes the archive we
    // are actually about to link for every real core `dregg-pq` routes through. That catches
    // every degrade path at once, including ones added later, and cannot be bypassed by a new
    // early `return` upstream.
    //
    // Tier policy is deliberately the SAME as DREGG_REQUIRE_LEAN (`require_lean_native`): ON
    // for a native `--release`/distribution build or an explicit `DREGG_REQUIRE_LEAN=1`, so a
    // release binary can never silently ship without the verified cores. The opt-out for a
    // deliberately core-less build is `DREGG_REQUIRE_PQ_CORES=0`.
    // ONE `nm` pass over the final artifact, shared by both export gates below.
    let linked_exports = archive_dregg_exports(&build_archive);
    println!("cargo:rerun-if-env-changed=DREGG_REQUIRE_PQ_CORES");
    let require_pq_env = std::env::var("DREGG_REQUIRE_PQ_CORES").ok();
    let require_pq_off = matches!(
        require_pq_env.as_deref(),
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF")
    );
    let require_pq_on = matches!(
        require_pq_env.as_deref(),
        Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
    );
    let require_pq_cores = require_pq_on || (require_lean_native && !require_pq_off);
    if require_pq_cores {
        // The manifest moved to the `REQUIRED_PQ_CORE_EXPORTS` const at the top of this file so the
        // SAME table also drives (a) the pre-splice completeness check in `archive_dregg2_complete`
        // and (b) the per-probe `absent_export_warn` text. Same 6 symbols, same consequences, one
        // `nm` pass instead of six.
        let missing = missing_in(&linked_exports, REQUIRED_PQ_CORE_EXPORTS);
        if !missing.is_empty() {
            let detail = missing
                .iter()
                .map(|(sym, consequence)| format!("  * {sym} — ABSENT: {consequence}"))
                .collect::<Vec<_>>()
                .join("\n");
            let archive_path = build_archive.display();
            let n_missing = missing.len();
            let n_total = REQUIRED_PQ_CORE_EXPORTS.len();
            panic!(
                "\n\
                 ================================================================================\n\
                 dregg-lean-ffi: REFUSING to link an archive without the verified PQ cores.\n\
                 ================================================================================\n\
                 The PQ-core export gate is ACTIVE (DREGG_REQUIRE_PQ_CORES=1, or a --release /\n\
                 distribution build / DREGG_TEST_REQUIRE_LEAN=1 on a native archive-linkable\n\
                 target), but the archive this build would link:\n\
                 \n    {archive_path}\n\n\
                 does NOT export {n_missing} of the {n_total} Lean-verified post-quantum cores:\n\
                 {detail}\n\
                 \n\
                 A binary linked against this archive would look identical, build green, and\n\
                 answer one or more post-quantum operations with UNAUDITED crate primitives — the exact\n\
                 silent substitution this gate exists to prevent.\n\
                 \n\
                 CAUSE: the seed archive exports NONE of these; they are produced by THIS build\n\
                 script splicing freshly-compiled Dregg2 objects in. If they are\n\
                 missing, a degrade path above fired and reported itself only as a\n\
                 `cargo:warning=` (which cargo HIDES for dependency crates). Re-run with\n\
                 `cargo build -vv` and read the `dregg-lean-ffi:` warnings — the usual causes are\n\
                 a `lake build` failure in metatheory/ (a module failed to elaborate), a `leanc`\n\
                 failure, an archive-splice failure, or NO ARCHIVE AT ALL (the seed is gitignored\n\
                 and has never been in the repository — fetch one with\n\
                 ./scripts/fetch-lean-seed.sh).\n\
                 \n\
                 VERIFY BY HAND:\n\
                 \n    nm -g --defined-only {archive_path} | grep dregg_fips204_verify_real\n\n\
                 To allow a deliberately core-less build (dev, benches, a non-PQ crate) set\n\
                 DREGG_REQUIRE_PQ_CORES=0 — such a build MUST NOT ship as verified.\n\
                 ================================================================================\n"
            );
        }
    }

    // GRAIN R3 whole-history verify extraction: probe the spliced archive for the
    // `@[export] dregg_grain_r3_verify` symbol (the extracted, Lean-verified R3-accept decision over
    // the whole-chain STARK verified-status + the R1 head binding). Present ⇒ gate the Rust
    // `extern "C"` block, the C shim string bridge, and the module initializer. `grain-verify::r3_verify`
    // marshals the fold's verified-status + heads through this to run the LEAN-PROVEN R3 decision.
    let grain_r3_verify_present = archive_exports(&build_archive, "dregg_grain_r3_verify");
    if grain_r3_verify_present {
        println!("cargo:rustc-cfg=dregg_grain_r3_verify_present");
    } else {
        absent_export_warn("dregg_grain_r3_verify");
    }

    // HOLDING grant-weight verdict extraction: probe the spliced archive for the
    // `@[export] dregg_holding_grant_weight` symbol (the extracted, Lean-verified non-custodial
    // proof-of-holdings → governance-weight decision — `if isConsensusProven && slotFinal then amount
    // else 0`, proved to realize `grantsWeight`). Present ⇒ gate the Rust `extern "C"` block, the C shim
    // string bridge, and the module initializer. `dregg-governance::holding_weight::grant_weight` marshals
    // the fast-Rust pre-checks' facts + the amount through this to run the LEAN-PROVEN weight verdict.
    //
    // `grantWeightFFI` lives in `Dregg2.Bridge.ProofOfHoldings` (relocated under `Dregg2/` from the
    // original `Metatheory/` home precisely so its IR emits under `.lake/build/ir/Dregg2/` and the
    // `build_dregg2_archive` splice — which walks `Dregg2/**/*.c` — picks up `dregg_holding_grant_weight`
    // like every other exported decision (R3Verify, DistributedExports, FlowRefine, Fips204Verify). Once
    // the archive builds (hbox/local), this probe reads true and the linked decision path lights up.
    let holding_grant_weight_present =
        archive_exports(&build_archive, "dregg_holding_grant_weight");
    if holding_grant_weight_present {
        println!("cargo:rustc-cfg=dregg_holding_grant_weight_present");
    } else {
        absent_export_warn("dregg_holding_grant_weight");
    }

    // INTERCHAIN reached-consensus verdict extraction: probe the spliced archive for the
    // `@[export] dregg_interchain_reached_consensus` symbol (the extracted, Lean-verified bridge-trust
    // decision — `proof`/resolved-watchtower/quorum-committee reach, `rpc`/fraud/no-quorum/unknown-tag
    // refuse, proved to realize `reachesConsensusSpec`). Present ⇒ gate the Rust `extern "C"` block,
    // the C shim string bridge, and (self-contained core — like R3/holding) NO module initializer.
    // `dregg-bridge::interchain_adapter`'s `TrustRung::reached_consensus` marshals the rung wire through
    // this to run the LEAN-PROVEN trust verdict. `reachedConsensusFFI` lives under `Dregg2/`
    // (`Dregg2.Bridge.InterchainAdapterDecision`), so its IR emits under `.lake/build/ir/Dregg2/` and the
    // `build_dregg2_archive` splice picks up the symbol like every other exported decision.
    let interchain_reached_consensus_present =
        archive_exports(&build_archive, "dregg_interchain_reached_consensus");
    if interchain_reached_consensus_present {
        println!("cargo:rustc-cfg=dregg_interchain_reached_consensus_present");
    } else {
        absent_export_warn("dregg_interchain_reached_consensus");
    }

    // FRI SOUNDNESS LEDGER (`Dregg2.Circuit.FriLedger.friLedgerFFI`): the computable per-config FRI
    // soundness ledger. Same shape as the decisions above — probe the spliced archive, gate the
    // extern + the C shim string bridge, and (self-contained core — like R3/holding/interchain) NO
    // module initializer. `circuit-prove/tests/fri_params_soundness_budget.rs` and
    // `circuit-prove/tests/fri_regrid_post_s2_measure.rs` marshal each DEPLOYED knob set through this
    // so the gate reports the numbers `Dregg2.Circuit.FriLedgerSound` proves, rather than re-deriving
    // the capacity/Johnson/per-fold/ε_C arithmetic in hand-written Rust (the twin that gate used to
    // be). `friLedgerFFI` is in the `Dregg2.FFI` import closure (§1.5), so its IR emits under
    // `.lake/build/ir/Dregg2/` and the `build_dregg2_archive` splice picks up the symbol like every
    // other export.
    //
    // ⚑ RESTORED 2026-07-25. This probe, its check-cfg, the `DREGG_FRI_LEDGER` shim define, the
    // `lean_init.c` bridge and the whole `dregg-lean-ffi` wrapper were removed as collateral by two
    // PQ-lane commits that never mentioned FRI (7ebe7b7d4b, 0f2802a0ca — a shared-tree clobber from a
    // stale base). The Lean `@[export]` survived, so nothing went red in metatheory; what went red was
    // `cargo test -p dregg-circuit-prove`, which could not COMPILE its test targets because two
    // committed tests import symbols that had ceased to exist. That took the law-1 ratchet and ~25
    // emit gates off the board for five days without a single failing check.
    let fri_ledger_present = archive_exports(&build_archive, "dregg_fri_ledger");
    if fri_ledger_present {
        println!("cargo:rustc-cfg=dregg_fri_ledger_present");
    } else {
        absent_export_warn("dregg_fri_ledger");
    }

    // DELEGATED TOOL/MCP-ACCESS ADMISSION (`Dregg2.Apps.DelegAdmit.delegAdmitFFI`): the five-conjunct
    // verdict — SCOPE (`tool = toolId`) ∧ DEADLINE (`now ≤ deadline`) ∧ STEP (`new = old + 1`) ∧ SANE
    // (`0 ≤ old`) ∧ RATE (`new ≤ rateLimit`) — that `Dregg2.Apps.ToolAccessDelegation`'s
    // `tool_invocation_commit_iff_admit` and its over-rate / past-deadline / out-of-scope teeth are
    // proven over. Init-only module (no Mathlib), self-contained like R3/holding/interchain/FRI, so
    // NO module initializer is referenced.
    //
    // ⚑ THERE IS NO FALLBACK ARM. Three Rust re-implementations of these same five conjuncts shipped
    // beside the Lean for months — `sdk/src/tool_gateway.rs::deleg_admit`,
    // `starbridge-apps/tool-access-delegation/src/lib.rs::deleg_admit`, and
    // `dreggnet-offerings/src/session.rs::play_admit` — each documented as "the byte-faithful Rust
    // mirror" of `delegAdmit`, each independently maintained, each provable of nothing (there is no
    // formal semantics of Rust, so their differential tests pinned drift and not correctness). All
    // three are DELETED. Absent ⇒ the gateways refuse every invocation rather than re-grow a twin.
    let deleg_admit_present = archive_exports(&build_archive, "dregg_deleg_admit");
    if deleg_admit_present {
        println!("cargo:rustc-cfg=dregg_deleg_admit_present");
    } else {
        absent_export_warn("dregg_deleg_admit");
    }

    // AUTOMATAFL GAME ORACLE (`Dregg2.Games.AutomataflFFI.rulesFFI`): the verb-dispatched wire over
    // the rules-faithful spec `Dregg2.Games.AutomataflRules` — board resolution (`mid`), the
    // automaton step and its whole decision (`step` / `sense`), move legality, the round's conflict
    // set, `roundStep`, the stock 11x11 opening, the stock two-player goals, and the win. Same shape
    // as the decisions above: probe the spliced archive, gate the extern + the C shim string bridge.
    //
    // ⚑ THIS ONE **IS** INITIALIZED in `lean_init.c` (unlike R3/holding/interchain/FRI): the `stock`
    // verb reads `AutomataflRules.stockTwoPlayer`, a nullary def the generated C compiles to a module
    // global that only the module initializer fills.
    //
    // ⚑ AND THERE IS NO FALLBACK ARM. `dregg-automatafl/src/reference.rs` — the hand transcription of
    // `~/dev/automatafl/logic` this replaces — is DELETED, because the conformance audit found that
    // lineage divergent from the Creator-Approved ruleset on 2-cycles (it SWAPPED the pair) and on
    // the path check (its occlusion scan skipped the DESTINATION, so a mover DESTROYED a stationary
    // piece). Absent ⇒ the crate's oracle calls return `Err` and the surface refuses; it does not
    // quietly answer with a twin, because there is no twin.
    let automatafl_rules_present = archive_exports(&build_archive, "dregg_automatafl_rules");
    if automatafl_rules_present {
        println!("cargo:rustc-cfg=dregg_automatafl_rules_present");
    } else {
        absent_export_warn("dregg_automatafl_rules");
    }

    // MULTIWAY-TUG RULES ORACLE (`Dregg2.Games.MultiwayTugFFI.rulesFFI`): the verb-dispatched wire
    // over the proven pure-transition spec `Dregg2.Games.MultiwayTug` — action legality (`legal`),
    // response legality and the anti-self-deal interlock (`legalresp`), the open action-kinds
    // (`kinds`), the escrow split (`split`), the two transitions (`act` / `respond`), row control
    // (`control`), the per-row tally including the scored Secret (`count`), the charm/row scores
    // (`score`), the win predicate (`won`) and the ADJUDICATED round winner (`winner`).
    //
    // ⚑ THIS ONE **IS** INITIALIZED in `lean_init.c` (like automatafl, unlike R3/FRI): the `charm`
    // verb reads `MultiwayTug.charm`, and every `#guard` witness state reads `blankState` — nullary
    // defs the generated C compiles to module globals that only the module initializer fills.
    //
    // ⚑ WHY THE ABSENT ARM IS A HARD REFUSAL, NOT A QUIETER ANSWER. The twin this replaced —
    // `dregg-multiway-tug/src/reference.rs::winner_of` — was a SPEC-twin (the twin-deletion sweep
    // hunted AIR twins, so it was filed "not a twin" and survived), and it had already DRIFTED:
    // `winner_of` was `roundWinner` truncated to its two absolute-threshold branches, with no charm
    // tie-break and no row tie-break. On every round where neither seat cleared the bar it answered
    // "no winner" where the model ADJUDICATES a seat — a MEASURED 78.5% played draw rate against
    // the model's 5.1%. It is DELETED, with no fallback of any kind, so an absent export now means
    // the game cannot score at all rather than scoring wrongly and quietly.
    let multiway_tug_rules_present = archive_exports(&build_archive, "dregg_multiway_tug_rules");
    if multiway_tug_rules_present {
        println!("cargo:rustc-cfg=dregg_multiway_tug_rules_present");
    } else {
        absent_export_warn("dregg_multiway_tug_rules");
    }

    // LIGHT-CLIENT verify-logic gate extraction: probe the spliced archive for the three
    // `@[export] dregg_{eth,tm,mpt}_lc_verify` symbols (the extracted, Lean-verified foreign-chain
    // admission decisions from `Dregg2.Bridge.LightClient{Eth,Tendermint,Mpt}Gate`). Present ⇒ gate
    // the Rust `extern "C"` block in `bridge_lc_ffi.rs` AND the C `_str` bridge in `lean_init.c`;
    // absent ⇒ `{eth,tm,mpt}_lc_verify_available()` is constantly false and the caller FAILS CLOSED.
    // Self-contained cores (static-const string literals, an assign-nothing module initializer), so
    // like R3/holding/interchain: NO module initializer is referenced from the shim.
    //
    // ⚠ THIS PROBE IS THE THIRD OF THREE LAYERS, and all three were dark at once. The gates were
    // absent from the archive (no `:c` facet — fixed by rooting the build on `Dregg2.FFI`'s import
    // closure), this cfg was never declared OR set, and `dregg_eth_lc_verify_str` was CALLED from
    // `bridge_lc_ffi.rs` but DEFINED NOWHERE. Any one of the three suffices to keep the ETH relayer
    // running with its verification gate compiled out, green and silent. They are on
    // REQUIRED_DECISION_EXPORTS now, so a strict build cannot re-enter that state quietly.
    let eth_lc_verify_present = archive_exports(&build_archive, "dregg_eth_lc_verify");
    if eth_lc_verify_present {
        println!("cargo:rustc-cfg=dregg_eth_lc_verify_present");
    } else {
        absent_export_warn("dregg_eth_lc_verify");
    }
    // The ETH COMMITTEE-ROTATION gate — the SECOND export from `LightClientEthGate`, probed
    // INDEPENDENTLY of the verify gate. They ship from the same module today, but an archive
    // predating this export carries one and not the other, and conflating them would let a stale
    // seed advertise a trust-root gate it cannot render. Absent ⇒ `verify_committee_update`
    // refuses and the trusted sync committee cannot advance (fail-closed; no Rust twin remains).
    let eth_committee_rotation_present =
        archive_exports(&build_archive, "dregg_eth_committee_rotation");
    if eth_committee_rotation_present {
        println!("cargo:rustc-cfg=dregg_eth_committee_rotation_present");
    } else {
        absent_export_warn("dregg_eth_committee_rotation");
    }
    let tm_lc_verify_present = archive_exports(&build_archive, "dregg_tm_lc_verify");
    if tm_lc_verify_present {
        println!("cargo:rustc-cfg=dregg_tm_lc_verify_present");
    } else {
        absent_export_warn("dregg_tm_lc_verify");
    }
    // The TENDERMINT SKIPPING gate — the second Cosmos export, from
    // `Dregg2.Bridge.LightClientTendermintSkip`, probed INDEPENDENTLY of the adjacent one for the
    // same reason the ETH rotation gate is: they cover DISJOINT height ranges, so an archive that
    // carries only the adjacent gate must make `cosmos-lightclient` refuse SKIPS while still
    // advancing block-by-block — not advertise a skip gate it cannot render. Every archive spliced
    // before 2026-07-29 is exactly that archive.
    let tm_skip_verify_present = archive_exports(&build_archive, "dregg_tm_skip_verify");
    if tm_skip_verify_present {
        println!("cargo:rustc-cfg=dregg_tm_skip_verify_present");
    } else {
        absent_export_warn("dregg_tm_skip_verify");
    }
    let mpt_lc_verify_present = archive_exports(&build_archive, "dregg_mpt_lc_verify");
    if mpt_lc_verify_present {
        println!("cargo:rustc-cfg=dregg_mpt_lc_verify_present");
    } else {
        absent_export_warn("dregg_mpt_lc_verify");
    }
    // MINA (Ouroboros Samasika / Pickles) anchored-segment gate. ⚑ NOW ON `REQUIRED_DECISION_EXPORTS`
    // (2026-07-29). It was deliberately off it while nothing could supply the symbol — but the
    // reason recorded here for that was WRONG, and the wrongness is worth keeping: it said
    // "`LightClientMinaGate` is not imported by `metatheory/Dregg2.lean`". Rooting in `Dregg2.lean`
    // is not what puts an export in the archive. THIS build script builds exactly one Lake target,
    // `Dregg2.FFI`, and splices exactly `Dregg2/FFI.lean`'s import closure — so the gate stayed
    // absent even after `Dregg2.lean:1536-1537` rooted it, which is layer 1 of `Dregg2/FFI.lean` §4
    // re-entered. CLOSED by the two `import` lines in `Dregg2/FFI.lean`. FLAG DAY: a strict build
    // (`--release`, `DREGG_REQUIRE_VERIFIED_EXPORTS=1`, or `DREGG_TEST_REQUIRE_LEAN=1`) against an
    // archive spliced before those imports now FAILS instead of degrading quietly. The remedy is a
    // plain `cargo build` — build.rs re-lake-builds and re-splices in place; no fetch, no migration.
    let mina_lc_verify_present = archive_exports(&build_archive, "dregg_mina_lc_verify");
    if mina_lc_verify_present {
        println!("cargo:rustc-cfg=dregg_mina_lc_verify_present");
    } else {
        absent_export_warn("dregg_mina_lc_verify");
    }
    // The PER-BLOCK Pickles Wrap-proof preamble gate (`Dregg2.Bridge.PicklesWrapShapeGate`). Same
    // manifest treatment and the same flag day as the gate above — it rode the same absent import
    // and lands with it.
    let mina_wrap_shape_ok_present = archive_exports(&build_archive, "dregg_mina_wrap_shape_ok");
    if mina_wrap_shape_ok_present {
        println!("cargo:rustc-cfg=dregg_mina_wrap_shape_ok_present");
    } else {
        absent_export_warn("dregg_mina_wrap_shape_ok");
    }
    // The PER-ADJACENT-PAIR Pickles PROOF-CHAIN gate (`Dregg2.Bridge.PicklesProofChainGate`).
    // Same manifest treatment and the same flag day as the two gates above.
    let mina_proof_chain_ok_present = archive_exports(&build_archive, "dregg_mina_proof_chain_ok");
    if mina_proof_chain_ok_present {
        println!("cargo:rustc-cfg=dregg_mina_proof_chain_ok_present");
    } else {
        absent_export_warn("dregg_mina_proof_chain_ok");
    }
    // The PER-BLOCK proof↔`stateHash` DERIVATION (`Dregg2.Bridge.MinaStateHashWordGate`) — public
    // input words 11 and 12 recomputed from the SERVED header and the served proof bytes. Same
    // manifest treatment and the same flag day as the three gates above; it rides the `import` line
    // added to `Dregg2/FFI.lean` on 2026-07-29.
    let mina_state_hash_word_ok_present =
        archive_exports(&build_archive, "dregg_mina_state_hash_word_ok");
    if mina_state_hash_word_ok_present {
        println!("cargo:rustc-cfg=dregg_mina_state_hash_word_ok_present");
    } else {
        absent_export_warn("dregg_mina_state_hash_word_ok");
    }
    // The SAMASIKA FORK-CHOICE pair (`Dregg2.Bridge.MinaForkChoiceGate`): the pairwise tip
    // comparison and the head roll that drives it. They ride the `import` line in `Dregg2/FFI.lean`
    // exactly as the four gates above do — a module rooted only in `Dregg2.lean` elaborates but
    // emits no `:c` facet, so the archive would carry the theorems and none of the entry points.
    // Absent, the light client keeps its head and its finalized height frozen rather than choosing
    // a fork with arithmetic nobody proved.
    let mina_better_tip_present = archive_exports(&build_archive, "dregg_mina_better_tip");
    if mina_better_tip_present {
        println!("cargo:rustc-cfg=dregg_mina_better_tip_present");
    } else {
        absent_export_warn("dregg_mina_better_tip");
    }
    let mina_head_advance_present = archive_exports(&build_archive, "dregg_mina_head_advance");
    if mina_head_advance_present {
        println!("cargo:rustc-cfg=dregg_mina_head_advance_present");
    } else {
        absent_export_warn("dregg_mina_head_advance");
    }
    // The PER-CHECKPOINT LOOP (`Dregg2.Bridge.MinaCheckpoint`) and the PER-BLOCK Wrap CHALLENGE
    // DERIVATION (`Dregg2.Bridge.MinaWrapChallenges`). ⚑ These two are what make Mina verification
    // affordable at all: Pickles recursion means verifying ONE block attests the chain behind it,
    // so the client verifies at a CHECKPOINT cadence it chooses and the cost of a longer cadence is
    // latency, not safety — provided the cheap between-checkpoint tier can never move the ratchet,
    // which is `provisional_never_ratchets`. Absent, there is no tier that can and the client is
    // back to `PINNED_CHALLENGES`' one height. Same `Dregg2/FFI.lean` layer-1 reasoning as the six
    // gates above; measured closure cost is +1 module and +0 modules respectively.
    let mina_checkpoint_advance_present =
        archive_exports(&build_archive, "dregg_mina_checkpoint_advance");
    if mina_checkpoint_advance_present {
        println!("cargo:rustc-cfg=dregg_mina_checkpoint_advance_present");
    } else {
        absent_export_warn("dregg_mina_checkpoint_advance");
    }
    let mina_wrap_challenges_present =
        archive_exports(&build_archive, "dregg_mina_wrap_challenges");
    if mina_wrap_challenges_present {
        println!("cargo:rustc-cfg=dregg_mina_wrap_challenges_present");
    } else {
        absent_export_warn("dregg_mina_wrap_challenges");
    }
    // ⚑ The PER-BLOCK `ft_eval0` DERIVATION (`Dregg2.Bridge.MinaWrapFtEval0`). Probed exactly like
    // the gate above, and for a reason that gate's history makes concrete: on 2026-07-30
    // `dregg_mina_wrap_challenges` was rooted in `Dregg2/FFI.lean` and probed HERE, and had no
    // `_str` bridge in `lean_init.c` and no wrapper in `lib.rs` — so the cfg was set, the archive
    // carried the symbol, and nothing on earth could call it. Both halves of the plumbing land
    // together now.
    let mina_wrap_ft_eval0_present = archive_exports(&build_archive, "dregg_mina_wrap_ft_eval0");
    if mina_wrap_ft_eval0_present {
        println!("cargo:rustc-cfg=dregg_mina_wrap_ft_eval0_present");
    } else {
        absent_export_warn("dregg_mina_wrap_ft_eval0");
    }

    // ── VERIFIED-DECISION EXPORT GATE (DREGG_REQUIRE_VERIFIED_EXPORTS) ──────────────────────
    // The PQ-core gate above is the SAME instrument, and it says the quiet part out loud:
    // "Nothing errors. The build is green. The deployed binary runs crypto nobody audited."
    // That was true of exactly 6 of the 23 exports that carry a proven verdict. This block is the
    // other 17 — everything whose absence silently reverts a Lean-PROVEN decision to a Rust twin,
    // a fail-closed refusal, or (for the `#[cfg(all(test, …))]` modules) to a test that no longer
    // EXISTS TO RUN. Nine test functions vanish that way, and the crate then reports `11 passed`,
    // not `0` — a zero gets noticed, eleven green tests look like a healthy crate. The worst
    // individual loss is `dregg_grain_r3_verify`: it carries the ONLY automated falsifier for the
    // ~2^31-grind width forgery.
    //
    // Deliberately a SEPARATE gate from DREGG_REQUIRE_PQ_CORES rather than a widening of it: the
    // two opt-outs mean different things ("this build has no verified PQ crypto" vs "this build
    // has no verified decisions"), and silently changing the scope of an existing `=0` would
    // disarm more than its user asked for. Same arming tier as the PQ gate.
    println!("cargo:rerun-if-env-changed=DREGG_REQUIRE_VERIFIED_EXPORTS");
    let require_dec_env = std::env::var("DREGG_REQUIRE_VERIFIED_EXPORTS").ok();
    let require_dec_off = matches!(
        require_dec_env.as_deref(),
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF")
    );
    let require_dec_on = matches!(
        require_dec_env.as_deref(),
        Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
    );
    if require_dec_on || (require_lean_native && !require_dec_off) {
        let missing = missing_in(&linked_exports, REQUIRED_DECISION_EXPORTS);
        if !missing.is_empty() {
            let detail = missing
                .iter()
                .map(|(sym, consequence)| format!("  * {sym} — ABSENT: {consequence}"))
                .collect::<Vec<_>>()
                .join("\n");
            let archive_path = build_archive.display();
            let n_missing = missing.len();
            let n_total = REQUIRED_DECISION_EXPORTS.len();
            let first = missing[0].0;
            panic!(
                "\n\
                 ================================================================================\n\
                 dregg-lean-ffi: REFUSING to link an archive without the verified DECISION exports.\n\
                 ================================================================================\n\
                 The verified-export gate is ACTIVE (DREGG_REQUIRE_VERIFIED_EXPORTS=1, or a\n\
                 --release / distribution build / DREGG_TEST_REQUIRE_LEAN=1 on a native\n\
                 archive-linkable target), but the archive this build would link:\n\
                 \n    {archive_path}\n\n\
                 does NOT export {n_missing} of the {n_total} Lean-verified decision cores:\n\
                 {detail}\n\
                 \n\
                 WHAT WOULD HAVE HAPPENED INSTEAD: this build script would have emitted no\n\
                 `cargo:rustc-cfg=dregg_*_present` for each missing symbol, every\n\
                 `#[cfg(dregg_*_present)]` bridge would compile out, every\n\
                 `#[cfg(all(test, dregg_*_present))]` test module would CEASE TO EXIST, and\n\
                 `cargo test` would report the SURVIVING tests as green. No error, no failure,\n\
                 no zero-test count — just a smaller, quieter, unverified system.\n\
                 \n\
                 CAUSE: these are SPLICE-ONLY exports. The seed archive exports none of them (it\n\
                 is also gitignored and has NEVER been in the repository, so a fresh checkout has\n\
                 no archive at all). They appear only when this script compiles the current\n\
                 Dregg2 `:c` facets and splices them in. If they are missing, either there is no\n\
                 archive, or a degrade path above fired and reported itself only as a\n\
                 `cargo:warning=` — which cargo HIDES for dependency crates. Re-run with\n\
                 `cargo build -vv` and read the `dregg-lean-ffi:` warnings.\n\
                 \n\
                 VERIFY BY HAND:\n\
                 \n    nm -g --defined-only {archive_path} | grep {first}\n\n\
                 GET AN ARCHIVE:\n\
                 \n    ./scripts/fetch-lean-seed.sh     # prebuilt, minutes\n\
                 \n    ./scripts/bootstrap.sh           # from source, hours\n\n\
                 To allow a deliberately decision-less build (a dev build with no Lean toolchain,\n\
                 a bench, a non-node crate) set DREGG_REQUIRE_VERIFIED_EXPORTS=0 — such a build\n\
                 MUST NOT ship as verified and MUST NOT be trusted as a test gate.\n\
                 ================================================================================\n"
            );
        }
    }

    let mut shim = cc::Build::new();
    shim.file("src/lean_init.c").include(&lean_include);
    // The SINGLE-THREADED / libuv-thread-free init (docs/EMBEDDABLE-LEAN-RUNTIME.md).
    // A C++ TU (it calls the namespaced `lean::initialize_*` runtime initializers
    // directly, skipping `initialize_libuv` so the libuv event-loop thread is never
    // spawned — the pg-Tier-D-embeddable path). Compiled into the SAME shim archive so
    // its `dregg_ffi_init_st` symbol propagates with the C bridges; purely additive (the
    // default `dregg_ffi_init` path is unchanged). `.cpp` ⇒ cc drives the C++ compiler.
    shim.file("src/lean_init_st.cpp");
    // The runtime-trim boundary no-op initializers (only present under DREGG_LEAN_FFI_RUNTIME_TRIM=1):
    // resolves the runtime-dead module inits the trimmed archive's kept chain still references, so the
    // elaborator/Mathlib init-pull is severed at the closure boundary. Compiled into the SAME
    // whole-archive shim so the no-ops win over any archive definition.
    if let Some(stub) = &runtime_trim_stub {
        shim.file(stub);
    }
    // SHARED link mode (the cdylib path, `DREGG_LEAN_LINK=shared`): `libleanshared`
    // exports the C-ABI `lean_initialize_runtime_module` but HIDES the individual
    // `lean::initialize_*` C++ symbols `dregg_ffi_init_st` calls. Supplying them from
    // a static `libleanrt.a` copy creates a fatal SPLIT-BRAIN runtime (two copies of
    // the runtime's global state — the in-backend SIGSEGV). So under shared linkage
    // the ST init MUST route through the single exported runtime: `DREGG_LEAN_SHARED`
    // makes `lean_init_st.cpp` call `lean_initialize_runtime_module` (one runtime
    // copy). NOTE: that exported init pulls libuv, so the shared-mode `dregg_ffi_init_st`
    // is NOT libuv-thread-free — the libuv-free property holds only on the STATIC link
    // (the host probe + the standalone node). See `docs/EMBEDDABLE-LEAN-RUNTIME.md` §5.
    let shared = shared_link_mode();
    if shared {
        shim.define("DREGG_LEAN_SHARED", None);
    }
    if handler_present {
        shim.define("DREGG_HANDLER_TURN", None);
    }
    if finalize_gate_present {
        shim.define("DREGG_FINALIZE_GATE", None);
    }
    if strand_admit_present {
        shim.define("DREGG_STRAND_ADMIT", None);
    }
    if distributed_exports_present {
        shim.define("DREGG_DISTRIBUTED_EXPORTS", None);
    }
    if decide_refines_present {
        shim.define("DREGG_DECIDE_REFINES", None);
    }
    if storage_content_root_present {
        shim.define("DREGG_STORAGE_CONTENT_ROOT", None);
    }
    if fips204_verify_present {
        shim.define("DREGG_FIPS204_VERIFY", None);
    }
    if fips204_verify_real_present {
        shim.define("DREGG_FIPS204_VERIFY_REAL", None);
    }
    if fips204_sign_present {
        shim.define("DREGG_FIPS204_SIGN", None);
    }
    // FIPS-204-SIGN-REAL (the brick-8 SIGN analog): its own module `Dregg2.Crypto.MlDsaSignReal`, so
    // DREGG_FIPS204_SIGN_REAL gates BOTH the per-export extern+bridge AND the module initializer (unlike the
    // co-located `dregg_fips204_sign` which shares the verify module's init).
    if fips204_sign_real_present {
        shim.define("DREGG_FIPS204_SIGN_REAL", None);
    }
    // Either ML-KEM export present ⇒ define DREGG_FIPS203 (one module init serves both cores).
    if fips203_encaps_present || fips203_decaps_present {
        shim.define("DREGG_FIPS203", None);
    }
    if fips203_encaps_present {
        shim.define("DREGG_FIPS203_ENCAPS", None);
    }
    if fips203_decaps_present {
        shim.define("DREGG_FIPS203_DECAPS", None);
    }
    // ML-KEM-768-DECAPS-REAL (BRICK K6): its own module `Dregg2.Crypto.MlKemDecaps`, so DREGG_MLKEM_DECAPS_REAL
    // gates BOTH the per-export extern+bridge AND the module initializer (unlike the `Fips203Kem` cores which
    // share their module's init).
    if mlkem_decaps_real_present {
        shim.define("DREGG_MLKEM_DECAPS_REAL", None);
    }
    // ML-KEM-768-ENCAPS-REAL (BRICK K5): its own module `Dregg2.Crypto.MlKemEncaps`, so DREGG_MLKEM_ENCAPS_REAL
    // gates BOTH the per-export extern+bridge AND the module initializer (like the K6 decaps core).
    if mlkem_encaps_real_present {
        shim.define("DREGG_MLKEM_ENCAPS_REAL", None);
    }
    // ML-KEM-768-KEYGEN-REAL (BRICK K7): its own module `Dregg2.Crypto.MlKemKeygen`, so DREGG_MLKEM_KEYGEN_REAL
    // gates BOTH the per-export extern+bridge AND the module initializer (like the K5/K6 cores).
    if mlkem_keygen_real_present {
        shim.define("DREGG_MLKEM_KEYGEN_REAL", None);
    }
    // ML-DSA-65-KEYGEN-REAL: its own module `Dregg2.Crypto.MlDsaKeygen`, so DREGG_MLDSA_KEYGEN_REAL gates
    // BOTH the per-export extern+bridge AND the module initializer (like the ML-KEM keygen core).
    if mldsa_keygen_real_present {
        shim.define("DREGG_MLDSA_KEYGEN_REAL", None);
    }
    if grain_r3_verify_present {
        shim.define("DREGG_GRAIN_R3_VERIFY", None);
    }
    if holding_grant_weight_present {
        shim.define("DREGG_HOLDING_GRANT_WEIGHT", None);
    }
    if interchain_reached_consensus_present {
        shim.define("DREGG_INTERCHAIN_REACHED_CONSENSUS", None);
    }
    // FRI SOUNDNESS LEDGER: `DREGG_FRI_LEDGER` gates BOTH the extern decl and the `_str` bridge in
    // `lean_init.c` (no module initializer — see the extern-decl note there).
    if fri_ledger_present {
        shim.define("DREGG_FRI_LEDGER", None);
    }
    // AUTOMATAFL GAME ORACLE: `DREGG_AUTOMATAFL_RULES` gates the extern decls, the `_str` bridge AND
    // the explicit `initialize_Dregg2_Dregg2_Games_AutomataflFFI` call in `lean_init.c` (this export
    // DOES need its module initializer — see the extern-decl note there).
    if automatafl_rules_present {
        shim.define("DREGG_AUTOMATAFL_RULES", None);
    }
    // MULTIWAY-TUG RULES ORACLE: `DREGG_MULTIWAY_TUG_RULES` gates the extern decls, the `_str`
    // bridge AND the explicit `initialize_Dregg2_Dregg2_Games_MultiwayTugFFI` call in `lean_init.c`
    // (this export DOES need its module initializer — see the extern-decl note there).
    if multiway_tug_rules_present {
        shim.define("DREGG_MULTIWAY_TUG_RULES", None);
    }
    // DELEGATED TOOL-ACCESS ADMISSION: `DREGG_DELEG_ADMIT` gates BOTH the extern decl and the `_str`
    // bridge in `lean_init.c` (no module initializer — `Dregg2.Apps.DelegAdmit` is Init-only and its
    // generated C is self-contained, same as the FRI ledger's).
    if deleg_admit_present {
        shim.define("DREGG_DELEG_ADMIT", None);
    }
    // The FOUR light-client gates (ETH / Tendermint / MPT / Mina): each define gates BOTH the extern
    // decl and the `_str` bridge in `lean_init.c` (no module initializer — see the extern-decl note
    // there). Independently probed, because an archive can carry one and not the others — and today
    // NO archive carries the Mina one (its gate module is not yet rooted in `Dregg2.lean`).
    if eth_lc_verify_present {
        shim.define("DREGG_ETH_LC_VERIFY", None);
    }
    if eth_committee_rotation_present {
        shim.define("DREGG_ETH_COMMITTEE_ROTATION", None);
    }
    if tm_lc_verify_present {
        shim.define("DREGG_TM_LC_VERIFY", None);
    }
    if tm_skip_verify_present {
        shim.define("DREGG_TM_SKIP_VERIFY", None);
    }
    if mpt_lc_verify_present {
        shim.define("DREGG_MPT_LC_VERIFY", None);
    }
    if mina_lc_verify_present {
        shim.define("DREGG_MINA_LC_VERIFY", None);
    }
    if mina_wrap_shape_ok_present {
        shim.define("DREGG_MINA_WRAP_SHAPE_OK", None);
    }
    if mina_proof_chain_ok_present {
        shim.define("DREGG_MINA_PROOF_CHAIN_OK", None);
    }
    if mina_state_hash_word_ok_present {
        shim.define("DREGG_MINA_STATE_HASH_WORD_OK", None);
    }
    // ⚑ THE TWO PER-BLOCK DERIVATION GATES. `DREGG_MINA_WRAP_CHALLENGES` was MISSING here while its
    // cfg probe above was already live — the export entered the archive and no `_str` bridge was
    // ever compiled, which is a gate that cannot go red because it cannot be called at all.
    if mina_wrap_challenges_present {
        shim.define("DREGG_MINA_WRAP_CHALLENGES", None);
    }
    if mina_wrap_ft_eval0_present {
        shim.define("DREGG_MINA_WRAP_FT_EVAL0", None);
    }
    // The FORK-CHOICE pair. Independently probed like every gate above, but they share ONE module
    // initializer in `lean_init.c` (both are `Dregg2.Bridge.MinaForkChoiceGate`, and the gate reads
    // the pinned `mainnet` constants record out of initialized module data).
    if mina_better_tip_present {
        shim.define("DREGG_MINA_BETTER_TIP", None);
    }
    if mina_head_advance_present {
        shim.define("DREGG_MINA_HEAD_ADVANCE", None);
    }
    if direct_present {
        shim.define("DREGG_DIRECT", None);
    }
    if constraint_admits_present {
        shim.define("DREGG_CONSTRAINT_ADMITS", None);
    }
    // CROSS-CELL CONSERVATION: its own module `Dregg2.Circuit.CrossCellConserveDecision`, so
    // DREGG_CROSS_CELL_CONSERVES gates BOTH the `_str` bridge AND the module initializer.
    if cross_cell_conserves_present {
        shim.define("DREGG_CROSS_CELL_CONSERVES", None);
    }
    // We drive the link with `rustc-link-lib` / `rustc-link-search` directives, NOT
    // `rustc-link-arg`. WHY: with the package's `links = "dregg_lean"` key, build-script
    // `rustc-link-lib` / `rustc-link-search` directives PROPAGATE to every DOWNSTREAM binary
    // (the `dregg-turn` lean-shadow tests, the node, …) — whereas `rustc-link-arg` is local
    // to this crate's own targets only. The cross-crate propagation is exactly what the
    // shadow harness needs to resolve `dregg_ffi_init` / `dregg_exec_full_forest_auth_str`.
    //
    // The shim is linked `+whole-archive` so its single bridge object survives the final
    // `-Wl,-dead_strip` regardless of archive-member ordering (the empirical fix for the
    // earlier `Undefined symbols` link failures). `+whole-archive` is a link-LIB modifier,
    // so it propagates too.
    shim.cargo_metadata(false);
    shim.compile("dregg_ffi_shim");
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let shim_archive = out_dir.join("libdregg_ffi_shim.a");

    // We drive the link with `rustc-link-lib` / `rustc-link-search` directives ONLY. With the
    // package's `links = "dregg_lean"` key these PROPAGATE to EVERY target that links this
    // crate's rlib — the `dregg-turn` lean-shadow tests + node (downstream) AND this crate's
    // own bins/tests (which `use dregg_lean_ffi` and so link the rlib). Emitting `rustc-link-arg`
    // in ADDITION would DOUBLE-link the shim for the FFI-crate-internal consumers (they'd see
    // the shim both via the propagated lib AND the arg) → "duplicate symbol" errors. So: one
    // mechanism. The standalone differential bins each carry `use dregg_lean_ffi as _;` to force
    // the rlib edge so they inherit these propagated directives.
    //
    // The shim is linked `+whole-archive` so its single bridge object survives the final
    // `-Wl,-dead_strip` regardless of archive-member ordering (the empirical link-failure fix).
    let _ = shim_archive;
    // BOTH the shim AND the spliced Lean archive resolve from `OUT_DIR` (the per-build working
    // copy of `libdregg_lean.a`, seeded from the git-tracked seed and then spliced/GC'd HERE).
    // We deliberately do NOT add `crate_dir` to the search path: pointing the linker at the
    // git-tracked seed would (a) reintroduce the wrong-feature-set race this split closes and
    // (b) link a non-GC'd (full-closure) archive. One search root for our static libs: OUT_DIR.
    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static:+whole-archive=dregg_ffi_shim");
    // Under the runtime trim, link the SEPARATE trimmed archive (`libdregg_lean_trim.a`); otherwise
    // the full verified closure (`libdregg_lean.a`). The trimmed archive holds the same verified
    // executor objects (the `dregg_*` exports + their runtime-function closure), only without the
    // proof-time elaborator/Mathlib members.
    if runtime_trim_stub.is_some() {
        println!("cargo:rustc-link-lib=static=dregg_lean_trim");
    } else {
        println!("cargo:rustc-link-lib=static=dregg_lean");
    }
    println!("cargo:rustc-link-search=native={}", lean_lib.display());
    println!(
        "cargo:rustc-link-search=native={}",
        sysroot.join("lib").display()
    );
    if shared {
        // ── SHARED runtime link (`DREGG_LEAN_LINK=shared`, see `shared_link_mode`) ──
        // The runtime+stdlib come from the toolchain's shared libraries instead of the
        // static archives (whose leanrt/mimalloc members are illegal in a `-shared` ELF
        // link). Link, in leanc's own order, every shared shell the sysroot ships:
        //   * Init_shared / leanshared_1 / leanshared_2 — the symbol-partition shells
        //     (real partitions on Windows; export-empty alongside the full libleanshared
        //     on macOS, where nm shows the whole runtime in libleanshared itself). We
        //     link whichever exist so the set is right on every platform.
        //   * leanshared — the runtime + Init/Std/Lean + leancpp + gmp + uv.
        //   * Lake_shared — Lake lives OUTSIDE leanshared, and the dependency closure
        //     references it (importGraph → `initialize_Lake_Util_Casing`), mirroring the
        //     `static=Lake` line of the static mode.
        // No c++/gmp/uv directives: leanshared bundles gmp+uv and carries its own libc++
        // dependency.
        for name in [
            "Init_shared",
            "leanshared_1",
            "leanshared_2",
            "leanshared",
            "Lake_shared",
        ] {
            let dylib = lean_lib.join(format!("lib{name}.dylib"));
            let so = lean_lib.join(format!("lib{name}.so"));
            if dylib.exists() || so.exists() {
                println!("cargo:rustc-link-lib=dylib={name}");
            }
        }
        // rpath so THIS crate's own bins/tests resolve libleanshared at run time.
        // `rustc-link-arg` does NOT propagate through the `links` key (unlike the
        // link-lib/link-search directives above), so downstream cdylibs — sdk-py — emit
        // their own rpath from their own build.rs.
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());
        println!(
            "cargo:rustc-link-arg=-Wl,-rpath,{}",
            sysroot.join("lib").display()
        );
    } else if target_os == "windows" {
        // ── WINDOWS-MinGW (`x86_64-pc-windows-gnu`) STATIC LINK ──────────────────────
        // The Lean LLVM-MinGW toolchain ships its runtime+stdlib AND a near-complete MinGW
        // system-lib sysroot under `$SYSROOT/lib` (sibling to `lib/lean`). The exact lib set
        // below MIRRORS what `leanc -###` itself passes to the linker for a Windows link
        // (lean modules + runtime + the `gmp/uv/icu/...` deps + the Win32 import libs + the
        // clang_rt builtins). `windows_gnu_link_env` has already put both lib dirs + the
        // `clang/19/lib/windows` builtins dir on the search path and generated the ntdll/gcc
        // shim. Proven end-to-end: a Rust-gnu binary linking exactly this set statically links
        // the real Lean runtime and runs `lean_initialize_runtime_module()` under x64 emulation.
        windows_gnu_link_env(&sysroot);
        // Lean modules + runtime core (leancpp before Lean/Std/Init before leanrt, matching
        // leanc's order — the C++ elaborator core resolves against later-listed members).
        for name in [
            "leancpp",
            "Lean",
            "Std",
            "Init",
            "leanrt",
            "Lake",
            "leanmanifest",
        ] {
            println!("cargo:rustc-link-lib=static={name}");
        }
        // Lean's bundled LLVM libc++ (the `std::__1::` ABI the runtime is compiled against),
        // its math/number deps, then the Win32 import libs the runtime + libuv reference.
        for name in [
            "c++", "c++abi", "gmp", "uv", "icu", "m", "unwind", "psapi", "user32", "advapi32",
            "iphlpapi", "userenv", "ws2_32", "dbghelp", "ole32", "shell32", "bcrypt", "ucrtbase",
            "moldname", "mingwex", "pthread",
            // ntdll — Rust std's `Nt*` syscalls (NtCreateFile/NtWriteFile/...) resolve from the
            // generated import lib; the MinGW sysroot omits it.
            "ntdll",
        ] {
            println!("cargo:rustc-link-lib=static={name}");
        }
        // compiler-rt builtins (clang's libgcc equivalent) — note the lib stem carries the arch.
        println!("cargo:rustc-link-lib=static=clang_rt.builtins-x86_64");
    } else {
        for name in [
            "leancpp", "Init", "Std", "Lean", "leanrt", "Lake", "gmp", "uv",
        ] {
            println!("cargo:rustc-link-lib=static={name}");
        }
        if target_os == "macos" {
            println!("cargo:rustc-link-lib=dylib=c++");
        } else {
            // Lean's Linux toolchain compiles its C++ (leancpp et al.) against the
            // BUNDLED LLVM libc++ (`std::__1::` ABI), shipped as static archives in
            // the sysroot's lib/ (already on the search path above). Linking the
            // GNU libstdc++ instead leaves `std::__1::cout` & friends undefined —
            // the first-ever Linux link of the full archive (Convergence round 6)
            // caught exactly that. Order matters: c++ before c++abi.
            println!("cargo:rustc-link-lib=static=c++");
            println!("cargo:rustc-link-lib=static=c++abi");
        }
    }
}

/// Emit the Windows-MinGW (`x86_64-pc-windows-gnu`) link SEARCH PATHS + generate the
/// import-lib shim the Rust-gnu link needs beyond what the Lean LLVM-MinGW sysroot ships.
///
/// The Lean Windows toolchain bundles a near-complete MinGW sysroot in `$SYSROOT/lib`
/// (kernel32/user32/ws2_32/advapi32/... import libs + libc++/gmp/uv/icu + the runtime),
/// plus the compiler-rt builtins under `lib/clang/19/lib/windows`. Two libs Rust-gnu's
/// `std` + the `crt2.o` startup reference are NOT in that sysroot:
///   * `libntdll.a` — std's `Nt*` syscall imports. We synthesise a full import lib from the
///     live `ntdll.dll` export table via `llvm-dlltool` (the 2500-symbol set).
///   * `libgcc.a` / `libgcc_eh.a` — GCC's builtins/unwinder. LLVM-MinGW uses compiler-rt +
///     libunwind instead, so empty stub archives satisfy the `-lgcc`/`-lgcc_eh` the Rust-gnu
///     driver always emits (the real builtins come from `clang_rt.builtins`, the real EH from
///     `libunwind`, both linked above).
///
/// The generated shims live in `$OUT_DIR/mingw-shim`. Idempotent (regenerated each build is
/// cheap). All paths use the sysroot discovered by `lean_sysroot()`; nothing is hardcoded.
fn windows_gnu_link_env(sysroot: &Path) {
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR set by cargo"));
    let lib = sysroot.join("lib");
    let lean_lib = lib.join("lean");
    let builtins = lib.join("clang").join("19").join("lib").join("windows");
    for dir in [&lean_lib, &lib, &builtins] {
        println!("cargo:rustc-link-search=native={}", dir.display());
    }

    let shim = out_dir.join("mingw-shim");
    let _ = std::fs::create_dir_all(&shim);
    println!("cargo:rustc-link-search=native={}", shim.display());

    // Empty libgcc / libgcc_eh stubs (LLVM-MinGW has no GCC builtins; satisfy the driver's
    // unconditional `-lgcc -lgcc_eh`).
    for stub in ["libgcc.a", "libgcc_eh.a"] {
        let p = shim.join(stub);
        if !p.exists() {
            let _ = Command::new(ar_tool()).arg("rcs").arg(&p).status();
        }
    }

    // libntdll.a — synthesise from the live ntdll.dll export table. We need `llvm-dlltool`;
    // it ships in both the Lean toolchain `bin/` and a stock LLVM install. Skip (leave any
    // prior shim) if it is absent — the link then surfaces the missing `Nt*` loudly.
    let ntdll = shim.join("libntdll.a");
    if !ntdll.exists() {
        let sysntdll = PathBuf::from(r"C:\Windows\System32\ntdll.dll");
        if let Ok(out) = Command::new("llvm-objdump")
            .arg("-p")
            .arg(&sysntdll)
            .output()
        {
            let text = String::from_utf8_lossy(&out.stdout);
            let mut names = Vec::new();
            let mut in_table = false;
            for line in text.lines() {
                if line.contains("Ordinal") && line.contains("RVA") && line.contains("Name") {
                    in_table = true;
                    continue;
                }
                if in_table {
                    let toks: Vec<&str> = line.split_whitespace().collect();
                    if toks.len() >= 3
                        && toks[2]
                            .chars()
                            .next()
                            .map(|c| c.is_ascii_alphabetic() || c == '_')
                            .unwrap_or(false)
                    {
                        names.push(toks[2].to_string());
                    }
                }
            }
            if !names.is_empty() {
                let def = shim.join("ntdll.def");
                let mut body = String::from("LIBRARY ntdll.dll\nEXPORTS\n");
                for n in &names {
                    body.push_str(n);
                    body.push('\n');
                }
                if std::fs::write(&def, body).is_ok() {
                    let _ = Command::new("llvm-dlltool")
                        .args(["-d"])
                        .arg(&def)
                        .arg("-l")
                        .arg(&ntdll)
                        .args(["-m", "i386:x86-64"])
                        .status();
                }
            }
        }
        if !ntdll.exists() {
            println!(
                "cargo:warning=dregg-lean-ffi: could not synthesise libntdll.a (llvm-dlltool / \
                 llvm-objdump on PATH? ntdll.dll readable?) — the Windows-gnu link may fail on \
                 std's Nt* imports."
            );
        }
    }
}
