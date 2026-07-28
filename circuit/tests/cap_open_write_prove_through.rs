//! # THE CAP-OPEN *WRITE* PROVE-THROUGHS — the §10 cap-tree write tail, end-to-end.
//!
//! Seven deployed `<effect>WriteCapOpenVmDescriptor2R24` members had NO prove+verify roundtrip
//! anywhere; `producer_descriptor_coverage_gate` carried each as `Uncovered("no cap-open write
//! prove-through test exists for this member")`. These are the members that make the post-cap-root
//! LIGHT-CLIENT verifiable rather than host-trusted: the authority-only twin proves the actor HELD
//! the authority, the write twin additionally forces the resulting cap-tree root, so a forged
//! post-root is UNSAT rather than accepted. Nothing was exercising that.
//!
//! Each test resolves its member from the COMMITTED registry (`V3_STAGED_REGISTRY_TSV`), builds a
//! genuine rotated base trace, rebuilds a real `CanonicalCapTree` from a 7-field c-list, takes the
//! deployed INSERT / REMOVE / UPDATE witness off THAT tree, widens the cap-open READ appendix from
//! the shape-matched witness, lays the deployed after-spine, and drives the result through
//! `prove_vm_descriptor2` + `verify_vm_descriptor2`.
//!
//! LAW #1: this file fills COLUMNS only. Every constraint is the Lean-declared chip lookup / base
//! gate the IR-v2 interpreter realizes generically from the committed descriptor (the AIR is
//! authored in `metatheory/Dregg2/Circuit/Emit/{CapOpenEmit,CapInsertEmit,CapRemoveEmit}.lean`).
//! No constraint, gadget or descriptor is hand-written here.
//!
//! ## The three write shapes, read off the committed constraints
//!
//!   * **INSERT** (`delegate`, `delegateAtten`, `introduce`, `spawn` — `…-v3-insert-capopen`). The
//!     READ appendix's `capRoot` group is bound to the **AFTER** rotated cap-root group
//!     (`c1934..c1941 == c452, c479..c485`), so the appendix opens the SPLICED (conferred) leaf
//!     against the REBUILT tree. The BEFORE group carries the genuine pre-insert root. Produced by
//!     `CanonicalCapTree::insert_witness` + `apply_rotated_cap_write_after_spine`.
//!   * **REMOVE** (`revokeDelegation`, `revokeCapability` — `…-v3-remove-capopen`). The `capRoot`
//!     group is bound to the **BEFORE** group (`c1934..c1941 == c213, c240..c246`): the appendix
//!     opens the REMOVED leaf against BEFORE, and the AFTER group carries the tombstone zero-fold
//!     (`CAP_ZERO8` folded up the SAME path — positions do not shift).
//!   * **UPDATE-at-key** (`refreshDelegation` — `…-v3-write-capopen`, the ONLY write twin at
//!     `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN` = 2119). The READ opens the held leaf against
//!     BEFORE; the 143-column after-spine re-opens the SAME leaf with `mask_lo := KEEP_MASK`
//!     (`c1979 == c73`) against AFTER (`c2111..c2118 == the AFTER group`), and the read leaf's
//!     `slot_hash` is pinned to `CAP_KEY` (`c1647 == c71`).
//!
//! Every write twin rides the nonce-TICK face — including `delegate`/`delegateAtten`/
//! `revokeCapability`, whose AUTHORITY-only twins are nonce-FREEZE. ⚠ So
//! `patch_attenuate_base_for_cap_open` must NOT be applied to any of these: it freezes the nonce
//! against the wrapper's own tick gate. That is the measured `#10` half of the old `[#4, #10]`
//! row-0 UNSAT, and the deployed SDK leg skips the patch for exactly this reason.
//!
//! Run: `cargo test -p dregg-circuit --test cap_open_write_prove_through -- --test-threads=4`.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::cap_root::{CAP_TREE_DEPTH, CAP_ZERO8, CanonicalCapTree, CapLeaf};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_COMMITTED_HEIGHT, B_STATE_COMMIT, BEFORE_BASE, C_CAVEAT_COMMIT,
    CAP_OPEN_AFTER_SPINE_SPAN, CAP_OPEN_BASE, CAP_OPEN_WIDTH, CAVEAT_BASE, CapOpenWitness,
    DFA_RC_LEN, RotatedBlockWitness, SIGNATURE_AUTH_TAG, V1_PI_COUNT,
    apply_rotated_cap_write_after_spine, empty_caveat_manifest,
    generate_rotated_cap_attenuate_after_spine,
    generate_rotated_create_cell_trace_with_accounts_tree, generate_rotated_effect_vm_trace,
    widen_to_cap_open,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::rotation_witness as rw;

// ── The deployed `cell/facet.rs` effect-kind bits the WRITE wrappers bind. Note these are the
//    WRITE wrapper's facets, which DIFFER from the authority-only twin's for the grant family:
//    `delegateWriteCapOpen` binds DELEGATION_OPS (1<<16) while `grantCapCapOpen` binds
//    GRANT_CAPABILITY (1<<2) — a delegate IS a delegation op.
const EFFECT_REVOKE_CAPABILITY: u32 = 1 << 3;
const EFFECT_INTRODUCE: u32 = 1 << 13;
const EFFECT_DELEGATION_OPS: u32 = 1 << 16;

/// The absolute `effBit` column (`CAP_OPEN_BASE + 296`) — what `effBitGateFor` pins.
const EFF_BIT_COL: usize = CAP_OPEN_BASE + 296;
/// The absolute `cap_root` group base (`CAP_OPEN_BASE + 287`, 8 lanes) — what `rootPinGate` binds.
const CAP_ROOT_COL: usize = CAP_OPEN_BASE + 287;

/// The turn's `src` felt — the conferred edge every leaf here targets (`targetBindGate`).
const SRC_FELT: u32 = 5_555;
/// The held-authority ANCHOR's c-list key.
const ANCHOR_KEY: u32 = 0xA1_1CE;
/// The FRESH conferred edge's key (INSERT) — absent from the BEFORE tree, so the sorted splice has
/// a genuine non-membership bracket. A present key is REFUSED by `insert_witness` (fail closed).
const FRESH_KEY: u32 = 0xD0_0D5;
/// The conferred / narrowed value the write binds (`KEEP_MASK`, col 73). A genuine submask of the
/// anchor's `HELD_MASK` (col 72) — `delegateAttenWrite`'s `granted ⊑ held` lookup reads this pair.
const KEEP_MASK: u32 = 0x52;
/// The anchor's held mask: `EFFECT_ALL`'s low limb. Broad, so it permits every fan-out bit.
const HELD_MASK: u32 = 0xFFFF;

/// Resolve a registry descriptor JSON by key from the COMMITTED staged TSV.
fn reg_json(name: &str) -> &'static str {
    dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64, epoch_bumps: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 9;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    // `revokeDelegationWriteCapOpen` carries the gate `sel[REVOKE_DELEGATION]·((c457 − c218) − 1)`
    // — the rotated EPOCH limb (`B_EPOCH = 30`) must tick by one on a revoke row. `rw::produce`
    // fills that limb from `cell.state.delegation_epoch()`, so the AFTER cell must carry the bump.
    for _ in 0..epoch_bumps {
        let _ = cell.state.bump_delegation_epoch();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// Re-read the FOUR rotated commit PIs (`V1_PI_COUNT..+4`) off the trace. MUST be called after
/// anything that rewrites a rotated block commit — the UPDATE after-spine overrides both cap-root
/// GROUPS and re-runs `recompute_block_commit`, which moves `BEFORE_BASE + B_STATE_COMMIT` (col
/// 367), the exact column the descriptor's first-row `piBinding` pins to PI 42. (The INSERT/REMOVE
/// helper `apply_rotated_cap_write_after_spine` re-derives the two commit PIs itself.)
fn refresh_rotated_commit_pis(trace: &[Vec<BabyBear>], dpis: &mut [BabyBear]) {
    let last = trace.len() - 1;
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT];
    dpis[V1_PI_COUNT + 1] = trace[last][AFTER_BASE + B_STATE_COMMIT];
    dpis[V1_PI_COUNT + 2] = trace[last][AFTER_BASE + B_COMMITTED_HEIGHT];
    dpis[V1_PI_COUNT + 3] = trace[last][CAVEAT_BASE + C_CAVEAT_COMMIT];
}

/// Build the rotated base trace + the UNWRAPPED cap-open PI vector + the map-op heaps.
///
/// ⚠ NO `patch_attenuate_base_for_cap_open` anywhere in this file: EVERY write twin rides the
/// nonce-TICK face, and the patch freezes the nonce against that gate.
#[allow(clippy::type_complexity)]
fn build_write_base(
    effects: Vec<Effect>,
    accounts_tree: bool,
    epoch_bump: bool,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<HeapLeaf>>) {
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0, 0);
    let after_cell = producer_cell(before_balance, 1, u64::from(epoch_bump));
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];

    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &rw::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);

    let caveat = empty_caveat_manifest();
    let (trace, mut pis, heaps) = if accounts_tree {
        // spawn is the one write twin that is ALSO a birth leg: its committed descriptor carries
        // the cells-tree accounts grow-gate (`absent` then `aafi_insert` at the new-cell key, col
        // 68) ALONGSIDE the cap-tree handoff, so the base needs the accounts producer + a real heap.
        let before_accounts: Vec<HeapLeaf> = Vec::new();
        generate_rotated_create_cell_trace_with_accounts_tree(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
            &before_accounts,
        )
        .expect("the rotated spawn base trace + accounts grow-gate must generate")
    } else {
        let (trace, pis) = generate_rotated_effect_vm_trace(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
        )
        .expect("the rotated write base trace must generate");
        (trace, pis, Vec::new())
    };
    // The cap-open family was never rc-wrapped in the Lean emit; lift the dsl rc tail off exactly
    // as the deployed SDK cap-open leg builder does.
    pis.truncate(pis.len() - DFA_RC_LEN);
    (trace, pis, heaps)
}

/// The held-authority ANCHOR leaf: a BROAD honest cap (`EFFECT_ALL`) conferring an edge to the
/// turn's `src`. The fan-out `capOpenConstraintsEff` appendix DECODES the tier off `auth_tag`
/// rather than pinning Signature, so any committed tier opens.
fn anchor_leaf() -> CapLeaf {
    CapLeaf {
        slot_hash: BabyBear::new(ANCHOR_KEY),
        target: BabyBear::new(SRC_FELT),
        auth_tag: BabyBear::new(SIGNATURE_AUTH_TAG),
        mask_lo: BabyBear::new(HELD_MASK),
        mask_hi: BabyBear::new(0xFFFF),
        expiry: BabyBear::new(0x00FF_FFFF),
        breadstuff: BabyBear::new(77),
    }
}

/// A second, distinct live leaf so the c-list is non-trivial (the spliced/removed key rides a real
/// bracket rather than the degenerate single-leaf tree).
fn other_leaf() -> CapLeaf {
    CapLeaf {
        slot_hash: BabyBear::new(0x00BE_EF00),
        target: BabyBear::new(321),
        auth_tag: BabyBear::new(1),
        mask_lo: BabyBear::new(1),
        mask_hi: BabyBear::new(0),
        expiry: BabyBear::new(9),
        breadstuff: BabyBear::new(0),
    }
}

fn before_tree() -> CanonicalCapTree {
    CanonicalCapTree::new(vec![anchor_leaf(), other_leaf()], CAP_TREE_DEPTH)
}

/// Assert a MUTATED trace is refused, and report the exact diagnostic.
fn assert_refused(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    map_heaps: &[Vec<HeapLeaf>],
    what: &str,
) {
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, dpis, &MemBoundaryWitness::default(), map_heaps)
            .and_then(|p| verify_vm_descriptor2(desc, &p, dpis))
    }));
    let diag = match outcome {
        Err(_) => "prover PANICKED (constraint unsatisfied)".to_string(),
        Ok(Err(e)) => format!("{e:?}"),
        Ok(Ok(())) => panic!(
            "[{}] TOOTHLESS: {what} still proved AND verified. A cap-write test that cannot be \
             made to fail is not a test.",
            desc.name
        ),
    };
    eprintln!("    RED-PROOF [{}] {what}: {diag}", desc.name);
}

/// Prove + verify the honest write trace, then prove it can go RED. `root_group_base` is the
/// rotated block whose cap-root GROUP the READ appendix is welded to — `AFTER_BASE` for the INSERT
/// shape, `BEFORE_BASE` for REMOVE / UPDATE — so the "forge the written root" mutation hits the
/// root the member actually binds.
fn finish_and_prove_red(
    key: &str,
    desc: &EffectVmDescriptor2,
    trace: Vec<Vec<BabyBear>>,
    dpis: Vec<BabyBear>,
    map_heaps: Vec<Vec<HeapLeaf>>,
    eff_bit: u32,
    written_root_group_base: usize,
) {
    assert_eq!(
        trace[0].len(),
        desc.trace_width,
        "[{key}] the produced trace width must be the committed descriptor's"
    );
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "[{key}] the PI vector must be the committed PI count"
    );

    let proof = prove_vm_descriptor2(
        desc,
        &trace,
        &dpis,
        &MemBoundaryWitness::default(),
        &map_heaps,
    )
    .unwrap_or_else(|e| {
        panic!(
            "[{key}] the honest cap-WRITE trace does NOT prove against the committed descriptor \
             `{}`: {e:?}",
            desc.name
        )
    });
    verify_vm_descriptor2(desc, &proof, &dpis).unwrap_or_else(|e| {
        panic!(
            "[{key}] the honest cap-WRITE proof does NOT light-client-verify against `{}`: {e:?}",
            desc.name
        )
    });
    eprintln!(
        "[{key}] CAP-OPEN WRITE GREEN ({}, width {}): proved + verified.",
        desc.name, desc.trace_width
    );

    // ── PROVEN ABLE TO GO RED.
    // (A) effBit off the member's own pinned bit.
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[EFF_BIT_COL] = BabyBear::new(eff_bit + 1);
        }
        assert_refused(
            desc,
            &t,
            &dpis,
            &map_heaps,
            "effBit off the member's pinned bit",
        );
    }
    // (B) one felt of the opened cap leaf (the target) — the `targetBind` edge + leaf digest.
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[CAP_OPEN_BASE + 1] += BabyBear::ONE;
        }
        assert_refused(
            desc,
            &t,
            &dpis,
            &map_heaps,
            "one felt of the cap leaf (target)",
        );
    }
    // (C) Forge the cap-tree root in the rotated block group the member welds the READ appendix
    //     to — AFTER for the INSERT/UPDATE shapes (that IS the write tooth: the post-root is
    //     forced, not host-trusted), BEFORE for REMOVE (there the weld is to the pre-state root,
    //     and the post-root is NOT forced at all — see the dedicated measurement below).
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[written_root_group_base + 25] += BabyBear::ONE; // the cap-root limb (B_CAP_ROOT)
        }
        assert_refused(
            desc,
            &t,
            &dpis,
            &map_heaps,
            if written_root_group_base == AFTER_BASE {
                "FORGED written cap-tree root (the write tooth)"
            } else {
                "FORGED welded BEFORE cap-tree root (the read weld)"
            },
        );
    }
    // (D) one lane of the cap-open appendix's committed cap_root — `rootPinGate`.
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[CAP_ROOT_COL] += BabyBear::ONE;
        }
        assert_refused(
            desc,
            &t,
            &dpis,
            &map_heaps,
            "one lane of the appendix cap_root",
        );
    }
    // (E) a corrupted public input.
    {
        let mut bad = dpis.clone();
        bad[0] += BabyBear::ONE;
        assert!(
            verify_vm_descriptor2(desc, &proof, &bad).is_err(),
            "[{key}] a corrupted public input MUST be rejected by verify_vm_descriptor2"
        );
        eprintln!(
            "    RED-PROOF [{}] corrupted PI[0]: verify_vm_descriptor2 rejected",
            desc.name
        );
    }
}

/// The INSERT shape (`delegate` / `delegateAtten` / `introduce` / `spawn`). The READ appendix opens
/// the SPLICED conferred leaf against the REBUILT AFTER tree; the BEFORE group carries the genuine
/// pre-insert root. `insert_witness` fails closed on a present / sentinel-colliding key, so the
/// after-root can never be fabricated.
fn prove_insert_member(key: &str, effects: Vec<Effect>, eff_bit: u32, accounts_tree: bool) {
    let desc = parse_vm_descriptor2(reg_json(key))
        .unwrap_or_else(|e| panic!("[{key}] the committed V3 descriptor must parse: {e}"));

    // ⚑ THE SELF-CONSISTENT POST-ROOT FORGE, run FIRST so a green cannot mask it. Smudging a
    // column after the fact is a weak tooth — it also breaks the block-commit chain, so a refusal
    // proves nothing about the WRITE. This is the real attack: a prover who fabricates the
    // post-insert cap-root and then rebuilds every commitment AROUND it, so the trace is
    // internally consistent and only the cap-tree write is a lie.
    {
        let (t, d, h) = build_insert_trace(key, &effects, eff_bit, accounts_tree, true);
        assert_refused(
            &desc,
            &t,
            &d,
            &h,
            "FABRICATED post-insert cap-root, commitments rebuilt around it",
        );
    }

    let (trace, dpis, map_heaps) = build_insert_trace(key, &effects, eff_bit, accounts_tree, false);
    finish_and_prove_red(key, &desc, trace, dpis, map_heaps, eff_bit, AFTER_BASE);
}

/// Build the INSERT-shaped trace. When `forge_post_root`, the AFTER cap-root welded into the
/// rotated blocks is a FABRICATION (`new_root` with lane 0 moved) and every block commitment is
/// recomputed around it by the deployed override — an internally consistent trace whose only lie
/// is the written cap-tree root.
#[allow(clippy::type_complexity)]
fn build_insert_trace(
    key: &str,
    effects: &[Effect],
    eff_bit: u32,
    accounts_tree: bool,
    forge_post_root: bool,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<HeapLeaf>>) {
    let (mut trace, mut dpis, map_heaps) = build_write_base(effects.to_vec(), accounts_tree, false);

    let tree = before_tree();
    let before_root8 = tree.root();
    let anchor = anchor_leaf();
    // The conferred edge, spliced at the FRESH key: same target / tier / mask / expiry as the
    // delegator's held (anchor) leaf — a delegation confers the held edge, so the crown facet the
    // descriptor binds on the spliced leaf is permitted exactly when the anchor permits it. The
    // conferred payload datum rides `breadstuff`, binding it into the spliced digest.
    let spliced = CapLeaf {
        slot_hash: BabyBear::new(FRESH_KEY),
        breadstuff: BabyBear::new(KEEP_MASK),
        ..anchor
    };
    let iw = tree
        .insert_witness(spliced)
        .expect("the fresh conferred key splices into the sorted BEFORE tree");
    assert_eq!(
        iw.old_root, before_root8,
        "[{key}] the insert witness's old root IS the tree's"
    );

    let spliced_open =
        CapOpenWitness::from_membership_for(&spliced, &iw.siblings, &iw.directions, eff_bit)
            .expect("the spliced (conferred) leaf satisfies the insert crown");
    assert_eq!(
        spliced_open.cap_root, iw.new_root,
        "[{key}] the spliced witness recomposes the REBUILT after-root"
    );

    widen_to_cap_open(&mut trace, &spliced_open).expect("widen to the cap-open READ crown");
    let mut welded_after = iw.new_root;
    if forge_post_root {
        welded_after[0] += BabyBear::ONE;
    }
    apply_rotated_cap_write_after_spine(
        &mut trace,
        &mut dpis,
        before_root8,
        welded_after,
        BabyBear::new(FRESH_KEY), // CAP_KEY   @ 71 — the inserted key
        BabyBear::new(HELD_MASK), // HELD_MASK @ 72 — the anchor's held mask (submask RHS)
        BabyBear::new(KEEP_MASK), // KEEP_MASK @ 73 — the conferred mask (submask LHS)
        anchor.slot_hash,         // ANCHOR_KEY   @ 74
        anchor.mask_lo,           // ANCHOR_MASK  @ 75
    )
    .expect("the INSERT after-spine override applies");
    (trace, dpis, map_heaps)
}

/// The REMOVE shape (`revokeDelegation` / `revokeCapability`). The READ appendix opens the REMOVED
/// leaf against BEFORE; the AFTER group carries the deployed tombstone zero-fold — `CAP_ZERO8`
/// folded up the SAME sibling path, so positions do not shift and every other capability's witness
/// stays valid. `remove_witness` fails closed on an absent key or an already-ghosted position.
fn prove_remove_member(key: &str, effects: Vec<Effect>, eff_bit: u32, epoch_bump: bool) {
    let desc = parse_vm_descriptor2(reg_json(key))
        .unwrap_or_else(|e| panic!("[{key}] the committed V3 descriptor must parse: {e}"));

    // ⚠ NO self-consistent post-root forge here, and NOT because it was forgotten: on these two
    // members it PASSES. See `remove_write_twins_do_not_bind_the_post_remove_cap_root` below,
    // which measures exactly that. Claiming a write tooth here would be claiming a tooth that is
    // not in the committed bytes.
    let (trace, dpis, map_heaps) = build_remove_trace(key, &effects, eff_bit, epoch_bump, false);
    finish_and_prove_red(key, &desc, trace, dpis, map_heaps, eff_bit, BEFORE_BASE);
}

/// Build the REMOVE-shaped trace; `forge_post_root` fabricates the tombstone AFTER root.
#[allow(clippy::type_complexity)]
fn build_remove_trace(
    key: &str,
    effects: &[Effect],
    eff_bit: u32,
    epoch_bump: bool,
    forge_post_root: bool,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<HeapLeaf>>) {
    let (mut trace, mut dpis, map_heaps) = build_write_base(effects.to_vec(), false, epoch_bump);

    let tree = before_tree();
    let anchor = anchor_leaf();
    let rmw = tree
        .remove_witness(anchor.slot_hash)
        .expect("the revoked key is live in the BEFORE c-list");
    let cap_open =
        CapOpenWitness::from_membership_for(&anchor, &rmw.siblings, &rmw.directions, eff_bit)
            .expect("the removed leaf satisfies the remove crown");
    assert_eq!(
        cap_open.cap_root, rmw.old_root,
        "[{key}] the removed leaf's path recomposes the BEFORE root"
    );
    assert_eq!(
        rmw.new_root,
        dregg_circuit::cap_root::recompose_membership(CAP_ZERO8, &rmw.siblings, &rmw.directions),
        "[{key}] the AFTER root IS the tombstone zero-fold over the same path"
    );
    assert_ne!(
        rmw.new_root, rmw.old_root,
        "[{key}] a remove that does not move the root would make the write tooth vacuous"
    );

    widen_to_cap_open(&mut trace, &cap_open).expect("widen to the cap-open READ crown");
    let mut welded_after = rmw.new_root;
    if forge_post_root {
        welded_after[0] += BabyBear::ONE;
    }
    apply_rotated_cap_write_after_spine(
        &mut trace,
        &mut dpis,
        cap_open.cap_root,
        welded_after,
        anchor.slot_hash, // CAP_KEY @ 71 — the removed key
        anchor.mask_lo,   // HELD_MASK @ 72 — the read value
        BabyBear::ZERO,   // KEEP_MASK @ 73 — a remove confers nothing
        BabyBear::ZERO,   // ANCHOR_KEY @ 74
        BabyBear::ZERO,   // ANCHOR_MASK @ 75
    )
    .expect("the REMOVE after-spine override applies");
    (trace, dpis, map_heaps)
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE SEVEN WRITE TWINS
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// `delegateWriteCapOpenVmDescriptor2R24` (`…-v3-insert-capopen`) — the plain cross-vat grant. The
/// WRITE wrapper binds `EFFECT_DELEGATION_OPS` (`1<<16`), NOT the authority-only twin's
/// `EFFECT_GRANT_CAPABILITY`: a delegate IS a delegation op.
#[test]
fn delegate_write_cap_open_proves_and_verifies() {
    prove_insert_member(
        "delegateWriteCapOpenVmDescriptor2R24",
        vec![Effect::GrantCapability {
            cap_entry: [BabyBear::new(0x71); 8],
            phase_b: None,
        }],
        EFFECT_DELEGATION_OPS,
        false,
    );
}

/// `delegateAttenWriteCapOpenVmDescriptor2R24` — the SAME insert base PLUS the surviving
/// `granted ⊑ held` non-amplification lookup over the param columns (`KEEP` col 73 ⊑ `HELD` col
/// 72). An attenuated grant NARROWS the delegator's authority; a grant exceeding held is UNSAT.
#[test]
fn delegate_atten_write_cap_open_proves_and_verifies() {
    prove_insert_member(
        "delegateAttenWriteCapOpenVmDescriptor2R24",
        vec![Effect::GrantCapability {
            cap_entry: [BabyBear::new(0x71); 8],
            phase_b: None,
        }],
        EFFECT_DELEGATION_OPS,
        false,
    );
}

/// `introduceWriteCapOpenVmDescriptor2R24` — the 3-party introduction's fresh edge, sorted-INSERTed
/// against the held-authority anchor. Crown facet `EFFECT_INTRODUCE` (`1<<13`).
#[test]
fn introduce_write_cap_open_proves_and_verifies() {
    prove_insert_member(
        "introduceWriteCapOpenVmDescriptor2R24",
        vec![Effect::Introduce {
            intro_hash: [BabyBear::new(0x23); 8],
        }],
        EFFECT_INTRODUCE,
        false,
    );
}

/// `spawnWriteCapOpenVmDescriptor2R24` — the parent→child capability handoff (an INSERT of the
/// conferred edge at the child key) running ALONGSIDE the cells-tree accounts grow-gate: 47 PIs and
/// two `map_op`s over the rotated cells-root, so this one carries a genuine map heap as well as the
/// cap-tree write. Crown facet `EFFECT_DELEGATION_OPS`.
#[test]
fn spawn_write_cap_open_proves_and_verifies() {
    prove_insert_member(
        "spawnWriteCapOpenVmDescriptor2R24",
        vec![Effect::SpawnWithDelegation {
            spawn_hash: [BabyBear::new(0x99); 8],
        }],
        EFFECT_DELEGATION_OPS,
        true,
    );
}

/// `revokeDelegationWriteCapOpenVmDescriptor2R24` (`…-v3-remove-capopen`) — the tombstone remove.
/// This member carries one gate no sibling does: `sel[REVOKE_DELEGATION]·((c457 − c218) − 1) == 0`,
/// the acting parent's `delegation_epoch` (rotated limb 30) ticking by one, so the AFTER producer
/// cell must carry the bump.
#[test]
fn revoke_delegation_write_cap_open_proves_and_verifies() {
    prove_remove_member(
        "revokeDelegationWriteCapOpenVmDescriptor2R24",
        vec![Effect::RevokeDelegation {
            child_hash: [BabyBear::new(0x5C); 8],
        }],
        EFFECT_DELEGATION_OPS,
        true,
    );
}

/// `revokeCapabilityWriteCapOpenVmDescriptor2R24` — the same tombstone zero-fold as
/// `revokeDelegation`, on the `REVOKE_CAPABILITY` selector and WITHOUT the epoch gate. Crown facet
/// `EFFECT_REVOKE_CAPABILITY` (`1<<3`).
#[test]
fn revoke_capability_write_cap_open_proves_and_verifies() {
    prove_remove_member(
        "revokeCapabilityWriteCapOpenVmDescriptor2R24",
        vec![Effect::RevokeCapability {
            slot_hash: [BabyBear::new(0x18); 8],
            phase_b: None,
        }],
        EFFECT_REVOKE_CAPABILITY,
        false,
    );
}

/// ⚑⚑⚑ **THE MEASURED HOLE — the two REMOVE write twins DO NOT BIND THE POST-REMOVE CAP-ROOT.**
///
/// This test asserts what the committed bytes DO, which is not what the write twins exist to do.
/// It is a wound sentinel, not a tooth: **when it starts FAILING, the hole has been CLOSED and this
/// test should be deleted** (and the two `assert_refused` calls restored in `prove_remove_member`).
///
/// ## What the committed descriptors actually bind
///
/// Resolve the AFTER rotated cap-root group (`c452` + the seven completion limbs `c479..c485`)
/// against every constraint of each member:
///
/// | member | gates/pins on the AFTER cap-root group |
/// |---|---|
/// | `delegateWriteCapOpen` / `introduceWrite` / `delegateAttenWrite` / `spawnWrite` (INSERT) | **8** — the appendix `capRoot` (forced by the depth-16 fold from the SPLICED leaf) is welded to it |
/// | `refreshDelegationWriteCapOpen` (UPDATE) | **8** — the after-spine's recomposed top root is welded to it |
/// | `revokeDelegationWriteCapOpen` (REMOVE) | **0** |
/// | `revokeCapabilityWriteCapOpen` (REMOVE) | **0** |
///
/// On the REMOVE members the appendix `capRoot` is welded to the **BEFORE** group (`c1934..c1941 ==
/// c213, c240..c246`), and the gates the AUTHORITY-only twin used to constrain the after side with
/// (`c452 == c87`, `c87 == c65`) were DROPPED with nothing put in their place. The `map_op` the SDK
/// route documents ("the `map_op` checks `after = remove(before, key)`") is not in the committed
/// JSON either — these members declare ZERO map-ops. So the deployed tombstone zero-fold
/// (`CAP_ZERO8` folded up the removed leaf's path) is **not forced anywhere in-circuit**.
///
/// ## Consequence, stated at the resolution it was measured
///
/// A prover may publish ANY 8-felt post-remove cap-root — including one that leaves the "revoked"
/// capability LIVE — and `prove_vm_descriptor2` + `verify_vm_descriptor2` accept. The only thing
/// that moves is the AFTER block state-commitment (PI 43), because the fabricated root is absorbed
/// into the commitment chain. So the post-root is exactly as HOST-TRUSTED as it was on the
/// authority-only twin: a verifier that independently recomputes the honest post-state commitment
/// catches it; a ledgerless light client — the threat model these members were introduced for —
/// does not. The second half of this test measures that boundary precisely.
///
/// `sdk/src/full_turn_proof.rs` states the opposite in the present tense on both routes ("the
/// genuine post-cap-root is on-the-wire light-client-verifiable (a wrong post-root is UNSAT)").
///
/// ## The fix is NOT in this file, and not in Rust
///
/// The AFTER-group weld is an AIR constraint. It belongs in the Lean emitter
/// (`Dregg2/Circuit/Emit/CapRemoveEmit.lean` — `effCapRemoveV3_forces_write8`), emitted exactly as
/// `CapInsertEmit` and the attenuate after-spine already emit theirs, followed by a descriptor
/// regen + VK rotation. Writing it in Rust would be authoring an AIR constraint in Rust.
#[test]
fn remove_write_twins_do_not_bind_the_post_remove_cap_root() {
    let cases: [(&str, Effect, u32, bool); 2] = [
        (
            "revokeDelegationWriteCapOpenVmDescriptor2R24",
            Effect::RevokeDelegation {
                child_hash: [BabyBear::new(0x5C); 8],
            },
            EFFECT_DELEGATION_OPS,
            true,
        ),
        (
            "revokeCapabilityWriteCapOpenVmDescriptor2R24",
            Effect::RevokeCapability {
                slot_hash: [BabyBear::new(0x18); 8],
                phase_b: None,
            },
            EFFECT_REVOKE_CAPABILITY,
            false,
        ),
    ];

    for (key, effect, eff_bit, epoch_bump) in cases {
        let desc = parse_vm_descriptor2(reg_json(key))
            .unwrap_or_else(|e| panic!("[{key}] the committed V3 descriptor must parse: {e}"));
        let effects = vec![effect];

        // The HONEST trace, and its published AFTER state commit (PI 43 — the only PI the forgery
        // moves).
        let (_honest_trace, honest_dpis, _) =
            build_remove_trace(key, &effects, eff_bit, epoch_bump, false);

        // The FORGED trace: the tombstone AFTER root is a fabrication and every commitment is
        // rebuilt around it, so the trace is internally consistent and its only lie is the
        // post-remove cap-tree root.
        let (forged_trace, forged_dpis, forged_heaps) =
            build_remove_trace(key, &effects, eff_bit, epoch_bump, true);

        let proof = prove_vm_descriptor2(
            &desc,
            &forged_trace,
            &forged_dpis,
            &MemBoundaryWitness::default(),
            &forged_heaps,
        )
        .unwrap_or_else(|_| {
            panic!(
                "[{key}] ⚑ GOOD NEWS, ACT ON IT: the fabricated post-remove cap-root is now \
                 REFUSED by the prover. The hole this sentinel pins is CLOSED — delete this test \
                 and restore the `assert_refused` post-root forge in `prove_remove_member`."
            )
        });
        verify_vm_descriptor2(&desc, &proof, &forged_dpis).unwrap_or_else(|_| {
            panic!(
                "[{key}] ⚑ GOOD NEWS, ACT ON IT: the fabricated post-remove cap-root now fails to \
                 verify. The hole this sentinel pins is CLOSED — delete this test and restore the \
                 `assert_refused` post-root forge in `prove_remove_member`."
            )
        });
        eprintln!(
            "⚑ [{key}] MEASURED HOLE: a FABRICATED post-remove cap-root PROVES and VERIFIES \
             against `{}` — the AFTER cap-root group carries ZERO binding gates in the committed \
             descriptor, so the tombstone zero-fold is not forced in-circuit.",
            desc.name
        );

        // THE BOUNDARY. The forgery is not entirely free: the fabricated root is absorbed into the
        // AFTER block commitment chain, so PI 43 moves. A verifier that carries the HONEST
        // post-state commitment therefore still rejects — which is exactly the host-trusted
        // posture the write twin was introduced to eliminate, not a substitute for the missing
        // constraint.
        assert_ne!(
            forged_dpis[V1_PI_COUNT + 1],
            honest_dpis[V1_PI_COUNT + 1],
            "[{key}] the fabricated root must at least move the published AFTER commit"
        );
        assert!(
            verify_vm_descriptor2(&desc, &proof, &honest_dpis).is_err(),
            "[{key}] the forged proof must not verify against the HONEST published PIs"
        );
        eprintln!(
            "   BOUNDARY [{key}]: the forgery moves the published AFTER state-commit (PI {}), so a \
             verifier that RECOMPUTES the honest post-state still rejects. The check is HOST-side, \
             not in-circuit — the authority-only posture, on the member that exists to replace it.",
            V1_PI_COUNT + 1
        );
    }
}

/// `refreshDelegationWriteCapOpenVmDescriptor2R24` (`…-v3-write-capopen`) — the ONLY write twin
/// with a real 143-column AFTER-SPINE (width `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN` = 2119).
/// The DELEG-tree UPDATE-at-key: the READ opens the held leaf against BEFORE, the after-spine
/// re-opens the SAME leaf with `mask_lo := KEEP_MASK` against AFTER. Because the after-spine
/// re-runs `recompute_block_commit` on BOTH blocks, the four rotated commit PIs go stale and must
/// be refreshed — the measured `#4` half of the old `[#4, #10]` row-0 UNSAT.
#[test]
fn refresh_delegation_write_cap_open_proves_and_verifies() {
    const KEY: &str = "refreshDelegationWriteCapOpenVmDescriptor2R24";
    let desc = parse_vm_descriptor2(reg_json(KEY))
        .unwrap_or_else(|e| panic!("[{KEY}] the committed V3 descriptor must parse: {e}"));
    assert_eq!(
        desc.trace_width,
        CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN,
        "[{KEY}] the UPDATE twin is the read appendix PLUS the after-spine"
    );

    // ⚑ THE SELF-CONSISTENT KEY FORGE, run FIRST. The UPDATE member pins the READ leaf's
    //   `slot_hash` to `CAP_KEY` (`c1647 == c71`) — i.e. the DELEG write must land at the key the
    //   actor actually opened. Here the after-spine is laid at a DIFFERENT key: the producer fills
    //   col 71 with it, recomputes BOTH block commits around it, and the commit PIs are refreshed,
    //   so the trace is internally consistent and its only lie is WHERE the write landed. This is
    //   a real attack, not a column smudge — an unbound `CAP_KEY` would let a prover re-arm a
    //   delegation he never opened.
    {
        let (t, d, h) = build_refresh_trace(BabyBear::new(ANCHOR_KEY + 1));
        assert_refused(
            &desc,
            &t,
            &d,
            &h,
            "the DELEG UPDATE laid at a key the actor never opened (commits rebuilt around it)",
        );
    }

    let (trace, dpis, map_heaps) = build_refresh_trace(BabyBear::new(ANCHOR_KEY));
    finish_and_prove_red(
        KEY,
        &desc,
        trace,
        dpis,
        map_heaps,
        EFFECT_DELEGATION_OPS,
        BEFORE_BASE,
    );
}

/// Build the UPDATE-at-key (`refreshDelegationWrite`) trace, laying the after-spine at `cap_key`.
/// The honest value is the opened leaf's own `slot_hash`.
#[allow(clippy::type_complexity)]
fn build_refresh_trace(
    cap_key: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<HeapLeaf>>) {
    let (mut trace, mut dpis, map_heaps) = build_write_base(
        vec![Effect::RefreshDelegation {
            child_hash: [BabyBear::new(0x5D); 8],
            snapshot_value: [BabyBear::new(0x5E); 8],
        }],
        false,
        false,
    );

    let tree = before_tree();
    let anchor = anchor_leaf();
    let mw = tree
        .membership_witness(anchor.slot_hash)
        .expect("the re-armed key is live in the BEFORE delegations leaf-set");
    let cap_open = CapOpenWitness::from_membership_for(
        &anchor,
        &mw.siblings,
        &mw.directions,
        EFFECT_DELEGATION_OPS,
    )
    .expect("the re-armed leaf satisfies the update crown");
    assert_eq!(
        cap_open.cap_root,
        tree.root(),
        "the re-armed leaf's path recomposes the BEFORE DELEG root"
    );

    widen_to_cap_open(&mut trace, &cap_open).expect("widen to the cap-open READ crown");
    // The UPDATE-at-key after-spine: re-open the SAME leaf with `mask_lo := KEEP_MASK` (the genuine
    // refreshed snapshot felt) and weld its recomposed root into the AFTER cap-root group. It also
    // recomputes both rotated block commits — which is why the commit PIs must be refreshed below.
    generate_rotated_cap_attenuate_after_spine(
        &mut trace,
        &cap_open,
        cap_key, // CAP_KEY   @ 71 — pinned to the read leaf's slot_hash (c1647 == c71)
        BabyBear::new(HELD_MASK), // HELD_MASK @ 72
        BabyBear::new(KEEP_MASK), // KEEP_MASK @ 73 — the after-spine leaf's mask_lo (c1979 == c73)
    )
    .expect("the UPDATE-at-key after-spine lays");
    refresh_rotated_commit_pis(&trace, &mut dpis);
    (trace, dpis, map_heaps)
}
