//! ⚑ THE LINKED ARCHIVE MUST NOT PREDATE THE LEAN IT CLAIMS TO BE.
//!
//! ── THE WOUND (measured 2026-08-07, and it had been open for a week) ─────────────────────────
//! `deployed_constraint_probe` — the REALITY-GATE canary for `@[export] dregg_constraint_admits` —
//! reported `8 passed` every day from 2026-07-30 to 08-06 while SIX of its eight assertions were
//! false. The admission wire's header grew from 6 tokens to 17 on 07-30/08-01; the probe's builder
//! still emitted six. The evaluator refused every one of those wires, and
//! `DeployedConstraint.admitsWire` THEN rendered a refusal-to-parse as `"1"` — the same string as
//! `ConstraintViolated` — so the probe could not tell. (That collision is closed as of the same
//! day: an unreadable wire renders `"7 <stage>"` and decodes to
//! `ProgramError::ConstraintOracleWireMalformed`. This gate is still the one that catches a STALE
//! object, which is a different failure — a stale evaluator can be perfectly self-consistent.)
//! It went green anyway because the archive
//! linked on the box carried a **2026-07-25** `Dregg2_Exec_DeployedConstraint.o`: a six-token
//! evaluator, agreeing with a six-token builder. Re-splicing the archive refreshed the evaluator
//! alone and the six reds surfaced at once.
//!
//! ── WHY NOTHING EXISTING CAUGHT IT ───────────────────────────────────────────────────────────
//! Three gates already look at this archive and NONE of them can see one stale member:
//!   * `build.rs`'s PROVENANCE DOWNGRADE is whole-archive and control-flow-shaped — it fires when
//!     the Lean build did not run. The Lean build ran. The `.c` was current. The splice ran.
//!   * `scripts/check-lean-seed-closure.sh` asks whether a module has a MEMBER. It had one.
//!   * `scripts/check-lean-seed-freshness.sh` compares the pin's `DREGG_CLOSURE_HASH` — a fact
//!     about a published seed asset, not about the archive this binary linked.
//! The missing question is per-member and it is the cheap one: **is this object older than the
//! `.lean` it was compiled from?** `ar` records a member's mtime; `metatheory/` records the
//! source's. One `ar tv` and a stat answer it in about a second.
//!
//! ── AND THE SEED, WHICH THIS TEST CANNOT REACH ───────────────────────────────────────────────
//! This test's subject is whatever archive `build.rs` LINKED. That is the right subject for a
//! build, and it left the SEED (`dregg-lean-ffi/libdregg_lean.a`) unwatched — the artifact every
//! new `OUT_DIR` is copied from, that arrives by fetch/rsync/bootstrap and is inherited across
//! checkouts, and that NO process links directly. On 2026-08-07 the working archive was clean and
//! the seed was 56 stale of 188 against this comparison (174 of 197 once the emitted `.c` counts
//! too). The seed's gate is `scripts/check-lean-seed-member-freshness.py` — same question, fixed
//! path, no cargo, and a local-gates row (`lean-seed-member-freshness`) with its own `-red` run.
//! Its comparison is `max(.lean, .lake/build/ir/*.c)`: the `.lean` half is this file's, unchanged;
//! the `.c` half only ever fires more, because lake regenerates a module's C when its compiled
//! image changes for reasons the module's own source file cannot show.
//!
//! ── WHAT THIS REFUSES ────────────────────────────────────────────────────────────────────────
//! Every `Dregg2_<Mod>.o` member of the archive `build.rs` actually linked, mapped back to
//! `metatheory/Dregg2/<Mod>.lean` by inverting the flattened object name against the real source
//! tree (so a module name containing `_` cannot be mis-split). A member older than its source is
//! named, with both timestamps, and the run FAILS. Measured on this checkout at landing: the
//! per-`OUT_DIR` working archive is CLEAN (0 of 323), and the git-ignored SEED at
//! `dregg-lean-ffi/libdregg_lean.a` carried **56 stale members of 188** — `Dregg2_Exec_
//! DeployedConstraint.o` among them. That is the artifact that hid the six reds, and this test
//! names it whenever a build links it un-refreshed. (The seed itself was re-spliced to 0 stale
//! the same day and now has its own always-on gate; see the section above.)
//!
//! ⚠ A GATE WHOSE INPUT IS ABSENT IS A FAULT, NOT A PASS. An unset `DREGG_LEAN_LINKED_ARCHIVE`,
//! an unresolvable `metatheory/`, an unreadable archive, no `ar` on PATH, a member listing this
//! cannot parse, or fewer than [`MIN_DREGG2_MEMBERS`] resolvable members all FAIL. The one
//! honest quiet path is "this build did not link the archive at all", which routes through
//! `demand_lean` exactly like every other Lean-gated test in this crate — loud under
//! `DREGG_TEST_REQUIRE_LEAN=1`, and never printing `ok` for a check that did not run.
//!
//! Run:  cargo nextest run -p dregg-lean-ffi --features lean-lib --test linked_archive_freshness
#![cfg(feature = "lean-lib")]

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::SystemTime;

/// A reader that harvests nothing must not read as clean. The `Dregg2.FFI` boundary closure is
/// ~243 modules and the seed carries 188 of them; a working archive carries 323. Anything under
/// this means the member listing or the source mapping broke, not that the tree got smaller.
const MIN_DREGG2_MEMBERS: usize = 100;

/// Clock slack, in seconds. `ar` records member mtimes at ONE-MINUTE resolution (no seconds
/// field in `ar tv`'s output), so a member written in the same minute as its source rounds down
/// and would read as stale. Two minutes covers that rounding and nothing else — this is a
/// rounding allowance, NOT a staleness budget, and it must never be raised to make a real
/// finding go away.
const AR_MTIME_RESOLUTION_SLACK_SECS: u64 = 120;

/// The archive `build.rs` emitted a link directive for (the per-`OUT_DIR` working copy, or the
/// runtime-trim archive when `DREGG_LEAN_FFI_RUNTIME_TRIM=1`). Absent when the Lean link was
/// skipped entirely.
const LINKED_ARCHIVE: Option<&str> = option_env!("DREGG_LEAN_LINKED_ARCHIVE");
/// The `metatheory/` directory `build.rs` compiled from (honours `DREGG_METATHEORY_DIR`).
const METATHEORY_DIR: Option<&str> = option_env!("DREGG_LEAN_METATHEORY_DIR");

/// List an archive's members with `ar tv`, falling back to `llvm-ar` (`build.rs::ar_tool` picks
/// between the same pair). PROBED BY DOING THE JOB, not by `--version`: Apple's `ar` does not
/// accept `--version` and prints a usage banner at exit 0, so a version probe selects a binary
/// that then cannot list anything — and this test would have failed on every macOS box.
fn ar_listing(archive: &Path) -> Result<(&'static str, String), String> {
    let mut tried = Vec::new();
    for candidate in ["ar", "llvm-ar"] {
        match Command::new(candidate).arg("tv").arg(archive).output() {
            Ok(out) if out.status.success() && !out.stdout.is_empty() => {
                return Ok((candidate, String::from_utf8_lossy(&out.stdout).into_owned()));
            }
            Ok(out) => tried.push(format!(
                "{candidate}: exit {} ({})",
                out.status,
                String::from_utf8_lossy(&out.stderr).trim()
            )),
            Err(e) => tried.push(format!("{candidate}: {e}")),
        }
    }
    Err(tried.join(" · "))
}

/// One `Dregg2_*.o` member and the epoch-seconds mtime `ar` recorded for it.
struct Member {
    name: String,
    mtime: SystemTime,
}

/// Parse `ar tv`'s listing. Each line ends `… <size> <Mon> <D> <HH:MM> <YYYY> <name>`; anything
/// that does not match that tail is skipped, and the caller's floor turns "skipped everything"
/// into a failure rather than a pass.
fn parse_ar_listing(listing: &str) -> Vec<Member> {
    let mut out = Vec::new();
    for line in listing.lines() {
        let f: Vec<&str> = line.split_whitespace().collect();
        if f.len() < 8 {
            continue;
        }
        let name = f[f.len() - 1];
        if !name.starts_with("Dregg2_") || !name.ends_with(".o") {
            continue;
        }
        // `Mon D HH:MM YYYY` — the four fields before the name.
        let stamp = f[f.len() - 5..f.len() - 1].join(" ");
        let Some(mtime) = parse_ar_stamp(&stamp) else {
            continue;
        };
        out.push(Member {
            name: name.to_string(),
            mtime,
        });
    }
    out
}

/// `Mon D HH:MM YYYY` in LOCAL time (what `ar tv` prints) to a `SystemTime`. Deliberately hand-
/// rolled: pulling `chrono` into this crate's dev-dependencies to read four fields would be a
/// larger change than the check.
fn parse_ar_stamp(s: &str) -> Option<SystemTime> {
    let f: Vec<&str> = s.split_whitespace().collect();
    if f.len() != 4 {
        return None;
    }
    const MONTHS: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    let month = MONTHS.iter().position(|m| *m == f[0])? as i64 + 1;
    let day: i64 = f[1].parse().ok()?;
    let (hh, mm) = f[2].split_once(':')?;
    let (hh, mm): (i64, i64) = (hh.parse().ok()?, mm.parse().ok()?);
    let year: i64 = f[3].parse().ok()?;

    // Days since the Unix epoch (civil-from-days, Howard Hinnant's algorithm).
    let y = if month <= 2 { year - 1 } else { year };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let mp = (month + 9) % 12;
    let doy = (153 * mp + 2) / 5 + day - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    let days = era * 146_097 + doe - 719_468;

    // `ar` prints LOCAL time; recover the offset from a same-instant comparison the platform
    // makes for us. `SystemTime` has no timezone, so we ask the filesystem: `build.rs` writes
    // the archive, and its own mtime is in the same local frame. Rather than guess an offset,
    // compare in UTC and let the caller's slack absorb it — see `local_offset_secs`.
    let utc = days * 86_400 + hh * 3_600 + mm * 60;
    let secs = utc.checked_sub(local_offset_secs())?;
    if secs < 0 {
        return None;
    }
    Some(SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(secs as u64))
}

/// Seconds that local time is AHEAD of UTC, recovered from the platform rather than assumed.
/// `date +%z` is the portable answer on both macOS and Linux; a failure yields 0, which shifts
/// every member timestamp in the SAFE direction (a member reads OLDER than it is, so the test
/// can over-report but never under-report).
fn local_offset_secs() -> i64 {
    let Ok(out) = Command::new("date").arg("+%z").output() else {
        return 0;
    };
    let s = String::from_utf8_lossy(&out.stdout);
    let s = s.trim();
    if s.len() != 5 {
        return 0;
    }
    let sign = if s.starts_with('-') { -1 } else { 1 };
    let hh: i64 = s[1..3].parse().unwrap_or(0);
    let mm: i64 = s[3..5].parse().unwrap_or(0);
    sign * (hh * 3_600 + mm * 60)
}

/// Every `Dregg2/**/*.lean` under `metatheory/`, keyed by the FLATTENED object name `build.rs`'s
/// `splice_obj_name` produces (`Dregg2/Exec/DeployedConstraint.lean` → `Dregg2_Exec_
/// DeployedConstraint.o`). Built by walking the real tree, so a module whose own name contains
/// `_` maps correctly — inverting the flattening by splitting on `_` would not.
fn source_index(meta: &Path) -> HashMap<String, PathBuf> {
    fn walk(dir: &Path, root: &Path, out: &mut HashMap<String, PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, root, out);
            } else if p.extension().map(|x| x == "lean").unwrap_or(false) {
                if let Ok(rel) = p.strip_prefix(root) {
                    let flat = rel
                        .with_extension("")
                        .components()
                        .map(|c| c.as_os_str().to_string_lossy().into_owned())
                        .collect::<Vec<_>>()
                        .join("_");
                    out.insert(format!("{flat}.o"), p.clone());
                }
            }
        }
    }
    let mut out = HashMap::new();
    walk(&meta.join("Dregg2"), meta, &mut out);
    out
}

/// THE COMPARISON, factored out so the red-proof below can drive the WHOLE assembly — reader,
/// name mapping and staleness test — instead of only the reader. Returns `(resolved, findings)`:
/// `resolved` is how many members mapped to a live `.lean` (the floor the caller applies, so a
/// broken mapping cannot report "nothing stale"), `findings` one line per stale object.
fn stale_members(
    members: &[Member],
    sources: &HashMap<String, PathBuf>,
    meta: &Path,
) -> (usize, Vec<String>) {
    let slack = std::time::Duration::from_secs(AR_MTIME_RESOLUTION_SLACK_SECS);
    let mut resolved = 0usize;
    let mut stale = Vec::new();
    for m in members {
        // A member whose module no longer exists in the tree is not a staleness finding — the
        // splice prunes those — and not silently ignored either: the caller's `resolved` floor
        // fails the run if the mapping stops resolving in general.
        let Some(src) = sources.get(&m.name) else {
            continue;
        };
        resolved += 1;
        let Ok(src_mtime) = src.metadata().and_then(|md| md.modified()) else {
            continue;
        };
        if src_mtime > m.mtime + slack {
            stale.push(format!(
                "  {} — member {} < source {} {}",
                m.name,
                fmt(m.mtime),
                src.strip_prefix(meta).unwrap_or(src).display(),
                fmt(src_mtime),
            ));
        }
    }
    (resolved, stale)
}

#[test]
fn the_linked_archive_is_not_older_than_its_lean_sources() {
    // The one honest quiet path: this build did not link the Lean archive at all. Routed through
    // `demand_lean` so it PANICS under `DREGG_TEST_REQUIRE_LEAN=1` rather than printing `ok`.
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available() && LINKED_ARCHIVE.is_some(),
        "a linked libdregg_lean.a (DREGG_LEAN_LINKED_ARCHIVE, emitted by build.rs)",
    ) {
        return;
    }

    let archive = PathBuf::from(LINKED_ARCHIVE.expect("checked above"));
    assert!(
        archive.is_file(),
        "build.rs said it linked {} and there is no file there. This test cannot measure what \
         shipped, which is a FAULT, not a pass.",
        archive.display()
    );

    let meta = METATHEORY_DIR.unwrap_or("");
    assert!(
        !meta.is_empty(),
        "build.rs could not resolve a metatheory/ directory, so there is nothing to compare the \
         archive's objects against. An absent input is a FAULT, not `no drift`."
    );
    let meta = PathBuf::from(meta);
    let sources = source_index(&meta);
    assert!(
        sources.len() >= MIN_DREGG2_MEMBERS,
        "indexed only {} Dregg2 .lean sources under {} — the source walk is broken, not the tree",
        sources.len(),
        meta.display()
    );

    let (_ar, listing) = ar_listing(&archive).unwrap_or_else(|why| {
        panic!(
            "neither `ar` nor `llvm-ar` could list {} — so this test cannot see what shipped, \
             which is a FAULT, not a pass. Tried: {why}",
            archive.display()
        )
    });
    let members = parse_ar_listing(&listing);
    assert!(
        members.len() >= MIN_DREGG2_MEMBERS,
        "parsed only {} Dregg2_*.o members out of {}. A listing this cannot read is a broken \
         READER, and a broken reader reports zero findings — which is why this floor exists.",
        members.len(),
        archive.display()
    );

    let (resolved, stale) = stale_members(&members, &sources, &meta);
    assert!(
        resolved >= MIN_DREGG2_MEMBERS,
        "only {resolved} of {} archive members mapped to a .lean source — the NAME MAPPING is \
         broken, and a broken mapping finds nothing stale by construction",
        members.len()
    );

    assert!(
        stale.is_empty(),
        "{} of {resolved} Dregg2 objects in the archive this binary LINKED are older than the \
         .lean they were compiled from:\n{}\n\n\
         Every verified-gate test in this crate is deciding against those objects, so a green \
         from one of them is a claim about that older Lean — which is exactly how six \
         `deployed_constraint_probe` assertions reported `ok` for a week (see this file's \
         header).\n\
         FIX: re-splice — `cargo build -p dregg-lean-ffi --features lean-lib` re-runs build.rs, \
         which recompiles each changed `.c` and rewrites the working archive. If that does not \
         clear it, the seed at `dregg-lean-ffi/libdregg_lean.a` is being linked un-refreshed: \
         `./scripts/bootstrap.sh` or `scripts/fetch-lean-seed.sh` for a HEAD-matching one.\n\
         Do NOT raise AR_MTIME_RESOLUTION_SLACK_SECS to clear a finding — it is a rounding \
         allowance for `ar`'s minute-resolution stamps, not a staleness budget.",
        stale.len(),
        stale.join("\n"),
    );
}

/// ⚑ THE RED PROOF, and it is not optional: the headline is a NEGATIVE assertion, which passes
/// just as happily when its own reader is broken. Everything here runs on strings and on a
/// scratch archive built in this test's own temp dir, so the shared tree is never mutated and no
/// window exists in which a sibling lane compiles a disarmed guard.
///
/// Leg 1 proves the `ar tv` line reader actually extracts a timestamp (a reader that returns
/// `None` for every line reports zero stale members forever). Leg 2 proves the staleness
/// comparison fires. Leg 3 proves the slack does not swallow a real finding.
#[test]
fn the_freshness_reader_can_go_red() {
    // 1 · THE READER. A real `ar tv` line — the exact shape measured on the seed in this
    //     checkout, including the `Dregg2_Exec_DeployedConstraint.o` that hid the six reds.
    let listing =
        "rw-r--r--     501/20       620280 Jul 25 03:02 2026 Dregg2_Exec_DeployedConstraint.o\n\
                   rw-r--r--     501/20        11128 Aug  7 09:19 2026 Dregg2_FFI.o\n\
                   rw-r--r--     501/20         4096 Aug  7 09:19 2026 Mathlib_Order_Basic.o\n";
    let members = parse_ar_listing(listing);
    assert_eq!(
        members.len(),
        2,
        "the reader must take both Dregg2 members and leave the Mathlib one — it took {:?}",
        members.iter().map(|m| &m.name).collect::<Vec<_>>()
    );
    let old = &members[0];
    let new = &members[1];
    assert!(
        new.mtime > old.mtime,
        "the reader did not order two members thirteen days apart — it is not extracting a \
         timestamp, and a reader that extracts no timestamp finds nothing stale, forever"
    );
    let gap = new
        .mtime
        .duration_since(old.mtime)
        .expect("ordered above")
        .as_secs();
    assert!(
        (12 * 86_400..=14 * 86_400).contains(&gap),
        "Jul 25 03:02 to Aug 7 09:19 is ~13 days; the reader made it {gap} s"
    );

    // 2 · THE COMPARISON. A source NEWER than its member is the finding; the reverse is not.
    let slack = std::time::Duration::from_secs(AR_MTIME_RESOLUTION_SLACK_SECS);
    assert!(
        new.mtime > old.mtime + slack,
        "a source 13 days newer than its object must be STALE past the rounding slack"
    );
    assert!(
        !(old.mtime > new.mtime + slack),
        "an object NEWER than its source is the healthy direction and must never be a finding"
    );

    // 3 · THE SLACK IS A ROUNDING ALLOWANCE, NOT A BUDGET. Same-minute is forgiven; an hour
    //     is not.
    let same_minute = parse_ar_listing(
        "rw-r--r--     501/20         4096 Aug  7 09:19 2026 Dregg2_A.o\n\
         rw-r--r--     501/20         4096 Aug  7 09:19 2026 Dregg2_B.o\n",
    );
    assert_eq!(same_minute.len(), 2);
    assert!(
        !(same_minute[1].mtime > same_minute[0].mtime + slack),
        "two members stamped in the SAME minute must not read as stale"
    );
    let an_hour = parse_ar_listing(
        "rw-r--r--     501/20         4096 Aug  7 09:19 2026 Dregg2_A.o\n\
         rw-r--r--     501/20         4096 Aug  7 10:19 2026 Dregg2_B.o\n",
    );
    assert_eq!(an_hour.len(), 2);
    assert!(
        an_hour[1].mtime > an_hour[0].mtime + slack,
        "one hour must NOT be inside the rounding allowance — if it is, the slack has become a \
         staleness budget and this gate no longer fires on a same-day drift"
    );

    // 4 · A LISTING THE READER CANNOT PARSE MUST YIELD NOTHING, so the caller's floor turns it
    //     into a FAILURE rather than a clean run.
    assert!(
        parse_ar_listing("garbage\nrw-r--r-- 1 2 3 Dregg2_X.o\n").is_empty(),
        "an unreadable listing must produce zero members (the floor then fails the run), never \
         members with invented timestamps"
    );

    // 5 · THE WHOLE ASSEMBLY, against a REAL scratch source tree in this test's own temp dir —
    //     reader, name mapping and comparison together. Legs 1-4 prove the reader can see a
    //     difference; only this proves `stale_members` REPORTS one. Without it the gate could
    //     read every timestamp correctly and still return an empty finding list forever.
    let tmp = std::env::temp_dir().join(format!(
        "dregg-freshness-redproof-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    let nested = tmp.join("Dregg2/Exec");
    std::fs::create_dir_all(&nested).expect("scratch tree");
    // A module whose NAME CONTAINS AN UNDERSCORE, on purpose: inverting the flattened object
    // name by splitting on `_` would map `Dregg2_Exec_Deployed_Constraint.o` to a path that does
    // not exist, `resolved` would drop, and the gate would find nothing. The mapping is built by
    // walking the tree precisely so this case resolves.
    for name in ["DeployedConstraint.lean", "Deployed_Constraint.lean"] {
        std::fs::write(nested.join(name), "-- red-proof fixture\n").expect("scratch source");
    }
    let sources = source_index(&tmp);
    assert_eq!(
        sources.len(),
        2,
        "the source walk did not index the scratch tree it was handed: {sources:?}"
    );
    assert!(
        sources.contains_key("Dregg2_Exec_Deployed_Constraint.o"),
        "a module name containing `_` must still map — it is the case a split-on-`_` inverse gets \
         wrong, and getting it wrong finds nothing stale by construction"
    );

    // The sources were written JUST NOW; the members claim 2026-07-25, the seed's own stamp.
    let old_members = parse_ar_listing(
        "rw-r--r--     501/20       620280 Jul 25 03:02 2026 Dregg2_Exec_DeployedConstraint.o\n\
         rw-r--r--     501/20       620280 Jul 25 03:02 2026 Dregg2_Exec_Deployed_Constraint.o\n",
    );
    assert_eq!(old_members.len(), 2);
    let (resolved, findings) = stale_members(&old_members, &sources, &tmp);
    assert_eq!(resolved, 2, "both members must map to a source");
    assert_eq!(
        findings.len(),
        2,
        "an archive member from 2026-07-25 against a source written this second MUST be reported \
         stale — this is the 2026-08-07 wound, reproduced. Findings: {findings:?}"
    );
    assert!(
        findings[0].contains("Dregg2_Exec_Deployed") && findings[0].contains("2026-07-25"),
        "a finding must NAME the object and print the member's date, or a reader cannot act on \
         it: {:?}",
        findings[0]
    );

    // ...and the healthy direction stays quiet: a member stamped in the future is not a finding.
    let fresh_members = parse_ar_listing(
        "rw-r--r--     501/20       620280 Jan  1 00:00 2099 Dregg2_Exec_DeployedConstraint.o\n\
         rw-r--r--     501/20       620280 Jan  1 00:00 2099 Dregg2_Exec_Deployed_Constraint.o\n",
    );
    let (resolved, findings) = stale_members(&fresh_members, &sources, &tmp);
    assert_eq!(resolved, 2);
    assert!(
        findings.is_empty(),
        "an object NEWER than its source is the healthy direction; a gate that reports it is a \
         wall, not a gate: {findings:?}"
    );

    let _ = std::fs::remove_dir_all(&tmp);
}

/// `SystemTime` to `YYYY-MM-DDTHH:MM:SSZ`. A finding whose two timestamps are unreadable is a
/// finding a reader cannot act on, so this is part of the check, not decoration.
fn fmt(t: SystemTime) -> String {
    let Ok(d) = t.duration_since(SystemTime::UNIX_EPOCH) else {
        return "pre-epoch".to_string();
    };
    let secs = d.as_secs() as i64;
    let (days, rem) = (secs.div_euclid(86_400), secs.rem_euclid(86_400));
    // civil-from-days (Howard Hinnant), the inverse of `parse_ar_stamp`'s days-from-civil.
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = if month <= 2 { y + 1 } else { y };
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        rem / 3_600,
        (rem % 3_600) / 60,
        rem % 60
    )
}
