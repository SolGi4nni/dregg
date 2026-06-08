//! # Differential: Lean `DirectoryLaws` model  ⟺  the REAL `InMemoryDirectory`.
//!
//! This is the Rust side of the differential for
//! `metatheory/Dregg2/Distributed/DirectoryLaws.lean` — the faithful executable Lean model of the
//! canonical named-capability directory (`directory.rs::{register, lookup, revoke}`) and its
//! bind/resolve/unbind MONOTONE laws. It closes the **P3 directory GAP** named in
//! `_SILVER-COVERAGE-LEDGER.md`: the Lean now models the real four-operation discipline (not a generic
//! CRDT deflection), and this differential pins that the verified Lean semantics IS the semantics the
//! `dregg-directory` crate actually computes — same discipline as `coord_diff` / `threshold_decrypt_diff`.
//!
//! The Lean proves, axiom-clean (⊆ {propext, Classical.choice, Quot.sound}):
//!
//!  * `register_version_monotone` / `revoke_version_monotone` — the CAS version counter only ever
//!    climbs; a *new* bind / *first* revoke raise it by exactly one, an idempotent op leaves it fixed.
//!  * `register_idempotent_noop` — re-binding the SAME (kind, handle) to a live name is a no-op
//!    returning the existing version (bind is idempotent on exact match).
//!  * `register_conflict_rejected` — binding a DIFFERENT value to a live name is REJECTED
//!    (`AlreadyRegistered`) and does not mutate (names don't silently re-bind).
//!  * `lookup_resolves_iff` — resolve succeeds iff present ∧ ¬revoked ∧ ¬expired.
//!  * `revoke_is_final` — THE unbind monotone law: once revoked, the name never resolves again at ANY
//!    height (the monotone tombstone).
//!  * `revoke_then_register_conflicts` — a revoked name is conflict-locked against a plain re-bind.
//!
//! This differential drives the GENUINE `InMemoryDirectory` (`register`/`lookup`/`revoke` — the same
//! code path the `governed-namespace` app + `cli` resolve names through) and asserts every law holds on
//! the real engine, plus a `lean_*` mirror of the Lean ops checked to agree decision-for-decision over
//! a grid of operations.

#![cfg(test)]

use crate::directory::{
    Directory, DirectoryEntry, DirectoryError, EntryKind, InMemoryDirectory, Version,
};
use crate::ResourceHandle;

// ───────────────────────────── Lean-mirror model (a tiny Rust transcription) ─────────────────────────────
//
// `DirectoryLaws.lean`'s `Dir`/`register`/`lookup`/`revoke` over the resolution-relevant fields
// (handle, kind, version, revoked, expiresAt). Names/handles/kinds are opaque ids — only equality
// matters (the conflict gate). We re-run this against the REAL engine below.

#[derive(Clone, PartialEq, Eq)]
struct LeanEntry {
    handle: u64,
    kind: u64,
    version: u64,
    revoked: bool,
    expires_at: Option<u64>,
}

#[derive(Clone, Default)]
struct LeanDir {
    version: u64,
    entries: Vec<(u64, LeanEntry)>, // keyed list = the BTreeMap
}

#[derive(Debug, PartialEq, Eq)]
enum LeanReg {
    Ok(u64),
    Conflict,
}

#[derive(Debug, PartialEq, Eq)]
enum LeanLookup {
    Found,
    NotFound,
    Revoked,
    Expired,
}

#[derive(Debug, PartialEq, Eq)]
enum LeanRev {
    Ok(u64),
    NotFound,
}

impl LeanDir {
    fn get(&self, name: u64) -> Option<&LeanEntry> {
        self.entries.iter().find(|(n, _)| *n == name).map(|(_, e)| e)
    }

    /// `DirectoryLaws.register` — idempotent exact-match / conflict / bind-new, in source order.
    fn register(&mut self, name: u64, handle: u64, kind: u64) -> LeanReg {
        if let Some(e) = self.get(name) {
            if e.kind == kind && e.handle == handle && !e.revoked {
                return LeanReg::Ok(e.version); // idempotent
            }
            return LeanReg::Conflict; // AlreadyRegistered
        }
        let v = self.version + 1;
        self.version = v;
        self.entries.push((
            name,
            LeanEntry { handle, kind, version: v, revoked: false, expires_at: None },
        ));
        LeanReg::Ok(v)
    }

    /// `DirectoryLaws.lookup` — NotFound / Revoked / Expired / Found, in source order.
    fn lookup(&self, name: u64, h: u64) -> LeanLookup {
        match self.get(name) {
            None => LeanLookup::NotFound,
            Some(e) => {
                if e.revoked {
                    LeanLookup::Revoked
                } else if let Some(exp) = e.expires_at {
                    if h > exp { LeanLookup::Expired } else { LeanLookup::Found }
                } else {
                    LeanLookup::Found
                }
            }
        }
    }

    fn resolves(&self, name: u64, h: u64) -> bool {
        matches!(self.lookup(name, h), LeanLookup::Found)
    }

    /// `DirectoryLaws.revoke` — NotFound / idempotent / flip-revoked, in source order.
    fn revoke(&mut self, name: u64) -> LeanRev {
        let v = self.version + 1;
        if let Some(idx) = self.entries.iter().position(|(n, _)| *n == name) {
            if self.entries[idx].1.revoked {
                return LeanRev::Ok(self.entries[idx].1.version); // idempotent
            }
            self.version = v;
            self.entries[idx].1.revoked = true;
            self.entries[idx].1.version = v;
            LeanRev::Ok(v)
        } else {
            LeanRev::NotFound
        }
    }
}

// ───────────────────────────── real-engine fixtures ─────────────────────────────

fn handle(seed: u8) -> ResourceHandle {
    ResourceHandle {
        federation_id: [seed; 32],
        cell_id: [seed.wrapping_add(1); 32],
        swiss: [seed.wrapping_add(2); 32],
    }
}

fn entry(h: ResourceHandle, expires_at: Option<u64>) -> DirectoryEntry {
    DirectoryEntry {
        handle: h,
        version: 0,
        kind: EntryKind::Service,
        description: None,
        tags: vec![],
        registered_at: 0,
        expires_at,
        revoked: false,
    }
}

fn real_resolves(dir: &InMemoryDirectory, name: &str, h: u64) -> bool {
    matches!(dir.lookup(name, h), Ok(_))
}

// ═══════════════════════ Differential 1: register_version_monotone + idempotent + conflict ═══════════════════════

#[test]
fn diff_register_monotone_idempotent_conflict() {
    let mut real = InMemoryDirectory::new();
    let mut lean = LeanDir::default();

    // new bind → both raise version by one and return it.
    let rv = real.register("alice", entry(handle(1), None)).unwrap();
    let lv = lean.register(1, 1 /*handle*/, 0 /*Service*/);
    assert_eq!(rv, 1, "real: new bind returns version 1");
    assert_eq!(lv, LeanReg::Ok(1), "lean agrees");
    assert_eq!(real.version(), lean.version, "version counters agree");

    // idempotent re-bind of the SAME (kind, handle) → no-op, returns existing version.
    let before_real = real.version();
    let rv = real.register("alice", entry(handle(1), None)).unwrap();
    let lv = lean.register(1, 1, 0);
    assert_eq!(rv, 1, "real: idempotent returns existing version");
    assert_eq!(lv, LeanReg::Ok(1));
    assert_eq!(real.version(), before_real, "real: idempotent did NOT bump version");
    assert_eq!(lean.version, before_real, "lean: idempotent did NOT bump version");

    // conflict: a DIFFERENT handle to the live name → AlreadyRegistered, no mutation.
    let before_real = real.version();
    let re = real.register("alice", entry(handle(2), None)).unwrap_err();
    let le = lean.register(1, 2 /*different handle*/, 0);
    assert!(matches!(re, DirectoryError::AlreadyRegistered(_)), "real: conflict rejected");
    assert_eq!(le, LeanReg::Conflict, "lean agrees: conflict");
    assert_eq!(real.version(), before_real, "real: conflict did NOT mutate version");
    assert_eq!(lean.version, before_real, "lean: conflict did NOT mutate version");

    // version monotone across every op so far: counter only ever climbed.
    assert!(real.version() >= 1 && lean.version >= 1);
}

// ═══════════════════════ Differential 2: lookup_resolves_iff (present ∧ ¬revoked ∧ ¬expired) ═══════════════════════

#[test]
fn diff_lookup_resolves_iff() {
    let mut real = InMemoryDirectory::new();
    let mut lean = LeanDir::default();

    // absent name: neither resolves.
    assert!(!real_resolves(&real, "ghost", 100));
    assert!(!lean.resolves(99, 100));

    // bound, no expiry: resolves at every height.
    real.register("svc", entry(handle(3), None)).unwrap();
    lean.register(7, 3, 0);
    for h in [0u64, 1, 100, u64::MAX] {
        assert_eq!(real_resolves(&real, "svc", h), lean.resolves(7, h), "resolve agrees @ {h}");
        assert!(real_resolves(&real, "svc", h), "no-expiry: resolves @ {h}");
    }

    // bound with expiry at 150: resolves at <=150, not past it (h > exp is strict).
    real.register("rent", entry(handle(4), Some(150))).unwrap();
    // mirror the expiry in the Lean dir (register has no expiry param; set it directly).
    lean.register(8, 4, 0);
    lean.entries.iter_mut().find(|(n, _)| *n == 8).unwrap().1.expires_at = Some(150);
    for h in [0u64, 150, 151, 200] {
        assert_eq!(real_resolves(&real, "rent", h), lean.resolves(8, h), "expiry resolve agrees @ {h}");
    }
    assert!(real_resolves(&real, "rent", 150), "at boundary: still resolves");
    assert!(!real_resolves(&real, "rent", 200), "past expiry: not resolved");
}

// ═══════════════════════ Differential 3: revoke_is_final + revoke_version_monotone + tombstone-lock ═══════════════════════

#[test]
fn diff_revoke_is_final_and_monotone() {
    let mut real = InMemoryDirectory::new();
    let mut lean = LeanDir::default();

    real.register("bob", entry(handle(5), None)).unwrap();
    lean.register(11, 5, 0);
    assert!(real_resolves(&real, "bob", 100));

    // revoke: version bumps by one, agrees.
    let before = real.version();
    let rv = real.revoke("bob").unwrap();
    let lv = lean.revoke(11);
    assert_eq!(rv, before + 1, "real: revoke bumped version");
    assert_eq!(lv, LeanRev::Ok(before + 1), "lean agrees on revoke version");
    assert_eq!(real.version(), lean.version);

    // revoke_is_final: never resolves again at ANY height (the monotone unbind tombstone).
    for h in [0u64, 100, u64::MAX] {
        assert!(!real_resolves(&real, "bob", h), "real: revoked never resolves @ {h}");
        assert!(!lean.resolves(11, h), "lean: revoked never resolves @ {h}");
    }
    assert!(matches!(real.lookup("bob", 100), Err(DirectoryError::Revoked(_))), "real: Revoked error");

    // revoke is idempotent: a second revoke is a no-op (version stable).
    let before = real.version();
    let rv = real.revoke("bob").unwrap();
    let lv = lean.revoke(11);
    assert_eq!(rv, before, "real: idempotent revoke, version unchanged");
    assert_eq!(lv, LeanRev::Ok(before));
    assert_eq!(real.version(), before, "real: double-revoke did NOT bump version");
    assert_eq!(lean.version, before);

    // revoke_then_register_conflicts: a revoked name cannot be re-bound by a plain register.
    let re = real.register("bob", entry(handle(5), None)).unwrap_err();
    let le = lean.register(11, 5, 0);
    assert!(matches!(re, DirectoryError::AlreadyRegistered(_)), "real: tombstone conflict-locks rebind");
    assert_eq!(le, LeanReg::Conflict, "lean agrees: tombstone conflict-locks rebind");

    // revoking an absent name → NotFound, both.
    let re = real.revoke("nope").unwrap_err();
    let le = lean.revoke(999);
    assert!(matches!(re, DirectoryError::NotFound(_)));
    assert_eq!(le, LeanRev::NotFound);
}

// ═══════════════════════ Differential 4: an op-sequence grid — Lean ⟺ real agree decision-for-decision ═══════════════════════

#[test]
fn diff_op_sequence_grid_agrees() {
    // Drive a mixed sequence of register/lookup/revoke against BOTH engines over several names and
    // assert the version counter and resolve decisions agree at every step. This is the
    // "Lean semantics IS what the crate computes" pin.
    let names = ["n0", "n1", "n2"];
    let lean_names = [20u64, 21, 22];

    let mut real = InMemoryDirectory::new();
    let mut lean = LeanDir::default();

    // bind all three.
    for (i, (rn, ln)) in names.iter().zip(lean_names.iter()).enumerate() {
        let rv = real.register(rn, entry(handle(i as u8 + 1), None)).unwrap();
        let lv = lean.register(*ln, i as u64 + 1, 0);
        assert_eq!(LeanReg::Ok(rv), lv, "bind {rn} agrees");
        assert_eq!(real.version(), lean.version, "version agrees after binding {rn}");
    }

    // revoke the middle one.
    let rv = real.revoke("n1").unwrap();
    let lv = lean.revoke(21);
    assert_eq!(LeanRev::Ok(rv), lv);
    assert_eq!(real.version(), lean.version);

    // resolve grid: every (name, height) decision agrees.
    for (rn, ln) in names.iter().zip(lean_names.iter()) {
        for h in [0u64, 50, 1000] {
            assert_eq!(
                real_resolves(&real, rn, h),
                lean.resolves(*ln, h),
                "resolve decision agrees for {rn} @ {h}"
            );
        }
    }

    // n0 + n2 still resolve, n1 (revoked) does not.
    assert!(real_resolves(&real, "n0", 100) && lean.resolves(20, 100));
    assert!(!real_resolves(&real, "n1", 100) && !lean.resolves(21, 100));
    assert!(real_resolves(&real, "n2", 100) && lean.resolves(22, 100));

    // the cell version equals the count of mutating ops (3 binds + 1 revoke = 4) — the CAS counter.
    let v: Version = real.version();
    assert_eq!(v, 4, "version == number of successful mutations");
    assert_eq!(lean.version, 4);
}

// ═══════════════════════ Differential 5: governance commit-swap (DfaRoutedDirectory) ═══════════════════════
//
// The Rust side of `DirectoryLaws.lean §7b` — the `GovDir` commit-swap commitment binding. This is the
// load-bearing AUTHORITY property the `governed-namespace` app relies on: a staged route table installs
// ATOMICALLY iff the governance proof's commitment EQUALS the staged table id; on mismatch the swap is
// rejected and BOTH the active table and the pending proposal are preserved (fail-closed). We drive the
// GENUINE `DfaRoutedDirectory::{propose_swap, commit_swap}` and assert it agrees with the Lean `GovDir`
// model decision-for-decision (`commit_swap_requires_matching_commitment` / `_mismatch_preserves_active`
// / `_match_activates` / `_no_pending` / `propose_preserves_active`).

use crate::dfa_routed::{DfaRoutedDirectory, RouteTableId};
use dregg_dfa::router::{RouteTableBuilder, RouteTarget};

/// Lean `GovDir` (the swap-authority skeleton: active id + optional staged id).
#[derive(Clone, PartialEq, Eq, Debug)]
struct LeanGovDir {
    active_id: u64,
    pending: Option<u64>,
}

#[derive(Debug, PartialEq, Eq)]
enum LeanSwap {
    Committed(u64),
    NoPending,
    Mismatch,
}

impl LeanGovDir {
    /// `GovDir.propose` — stage; active unchanged.
    fn propose(&mut self, new_id: u64) {
        self.pending = Some(new_id);
    }
    /// `GovDir.commitSwap` — NoPending / Mismatch(preserve) / install, in source order.
    fn commit_swap(&mut self, commitment: u64) -> LeanSwap {
        match self.pending {
            None => LeanSwap::NoPending,
            Some(staged) => {
                if staged == commitment {
                    self.active_id = staged;
                    self.pending = None;
                    LeanSwap::Committed(staged)
                } else {
                    LeanSwap::Mismatch // active + pending preserved
                }
            }
        }
    }
}

/// Map a real 32-byte `RouteTableId` to the Lean `u64` id by its first 8 bytes (a stable, injective-
/// enough projection for the equality decision the gate makes — distinct tables ⇒ distinct ids).
fn id_u64(id: RouteTableId) -> u64 {
    u64::from_le_bytes(id.0[..8].try_into().unwrap())
}

fn table_a() -> dregg_dfa::router::RouteTable {
    RouteTableBuilder::new()
        .route("system.*", RouteTarget::handler("dir:system"))
        .route("*", RouteTarget::handler("local"))
        .compile()
}

fn table_b() -> dregg_dfa::router::RouteTable {
    RouteTableBuilder::new()
        .route("blocked.*", RouteTarget::drop())
        .route("*", RouteTarget::handler("local"))
        .compile()
}

#[test]
fn diff_governance_commit_swap_binding() {
    let mut real = DfaRoutedDirectory::new(table_a());
    let active0 = id_u64(real.active_table_id());
    let mut lean = LeanGovDir { active_id: active0, pending: None };

    // commit with nothing staged → NoPending, both, no mutation.
    let before = real.active_table_id();
    let le = lean.commit_swap(0xdead);
    assert_eq!(le, LeanSwap::NoPending, "lean: no pending");
    let re = real.commit_swap(RouteTableId([0xAB; 32]));
    assert!(re.is_err(), "real: commit with nothing staged is rejected");
    assert_eq!(real.active_table_id(), before, "real: active unchanged when no pending");

    // propose stages table_b without changing the active table (propose_preserves_active).
    let staged = real.propose_swap(table_b());
    let staged_u = id_u64(staged);
    lean.propose(staged_u);
    assert!(real.has_pending_swap(), "real: pending staged");
    assert_eq!(id_u64(real.active_table_id()), active0, "real: active unchanged after propose");
    assert_eq!(lean.active_id, active0, "lean: active unchanged after propose");
    assert_eq!(lean.pending, Some(staged_u));

    // WRONG commitment → mismatch, active + pending BOTH preserved (commit_swap_mismatch_preserves_active).
    let bad = RouteTableId([0xFF; 32]);
    let le = {
        let mut l = lean.clone();
        l.commit_swap(id_u64(bad))
    };
    assert_eq!(le, LeanSwap::Mismatch, "lean: wrong commitment rejected");
    let re = real.commit_swap(bad);
    assert!(re.is_err(), "real: wrong governance commitment rejected");
    assert_eq!(id_u64(real.active_table_id()), active0, "real: mismatch did NOT change active");
    assert!(real.has_pending_swap(), "real: mismatch preserved the pending proposal");

    // RIGHT commitment → committed, active becomes the staged table, pending cleared
    // (commit_swap_match_activates + commit_swap_requires_matching_commitment).
    let le = lean.commit_swap(staged_u);
    assert_eq!(le, LeanSwap::Committed(staged_u), "lean: matching commitment commits");
    let committed = real.commit_swap(staged).expect("real: matching governance commitment commits");
    assert_eq!(id_u64(committed), staged_u, "real ⟺ lean: committed id agrees");
    assert_eq!(id_u64(real.active_table_id()), staged_u, "real: active is now the staged table");
    assert_eq!(lean.active_id, staged_u, "lean: active is now the staged table");
    assert!(!real.has_pending_swap(), "real: pending cleared after commit");
    assert_eq!(lean.pending, None, "lean: pending cleared after commit");
}
