//! # FOLD-CLAIM PIN LIVENESS — the dual of the unforced-pin census, on the committed bytes.
//!
//! ## Why this file exists (the hole that let a live wound land green)
//!
//! `circuit/tests/unforced_pi_pin_census.rs` measures pins that bind NOTHING and asserts the count
//! is zero. `UnforcedPiPins.unforcedPins_dropUnforcedPins` makes that zero **by theorem**, so the
//! census is green for two completely different reasons:
//!
//!   * the pin's column became FORCED (a non-pin constraint reads it) — the repair; or
//!   * the pin was **DELETED** — the subtraction.
//!
//! The census cannot tell those apart, and a deletion is invisible to it *by construction*. So when
//! `dropUnforcedPins` removed a claim pin that a fold arm locates its slot BY, the census stayed
//! green, the emit stayed green, and the arm went **fail-closed on every deployed leg** — silently,
//! because fail-closed. That happened to the four `withDfaRcPins` rc pins (repaired at `96001f909`
//! + `c02675665`) and it is happening RIGHT NOW to two more sites, measured below.
//!
//! This test is the missing half: for every claim slot a carrier fold arm reads BY INDEX, assert the
//! committed descriptor actually carries a `PiBinding` there, and that the pinned column is read by
//! a NON-PIN constraint (i.e. it would survive `dropUnforcedPins`). A slot that is merely *published*
//! — a `piCount` big enough to contain it, with no pin — is a verifier-supplied input the AIR
//! ignores, and the arm that reads it is dead.
//!
//! ## Measured 2026-07-31 on `rotation-wide-registry-staged.tsv` +
//! ## `rotation-wide-umem-welded-registry-staged.tsv` (both identical on every site)
//!
//! | carrier | member | slots | verdict |
//! |---|---|---|---|
//! | factory `child_vk8` | `factoryVmDescriptor2R24` | 47..54 | PINNED, forced |
//! | hatchery `contract_hash8` | `factoryVmDescriptor2R24` | 55..62 | PINNED, forced |
//! | sovereign `KEY_COMMIT` | `makeSovereignVmDescriptor2R24` | 58..61 | PINNED, forced (in-AIR chip gate) |
//! | **membership teeth** | `transferVmDescriptor2R24` | **50..51** | **NO PIN — dead** |
//! | **bridge `mint_hash`** | `mintVmDescriptor2R24` | **46** | **NO PIN — dead** |
//! | **DECO `payment_hash`** | `mintVmDescriptor2R24` | **46** | **NO PIN — dead (same slot)** |
//!
//! The three live sites are live for the RIGHT reason and this file pins that: sovereign's teeth
//! columns are read by the `withSovereignKeyCommit` chip gate, factory/hatchery's by the AFTER-block
//! absorption chain. The two dead ones were `.piBinding col pi` with the prover choosing both sides,
//! so `dropUnforcedPins` deleted them — correctly. **The repair is to force the columns, never to
//! exempt the pins**; until it lands, THIS test is the loud form of a wound that is otherwise only
//! visible as a fold arm that never fires.
//!
//! ⚠ `LIVE_SITES` is the assertion; `KNOWN_DEAD_SITES` is a MEASUREMENT with an expiry: each entry
//! asserts the site is *still* dead, so the day a repair lands this test goes red and the entry must
//! move to `LIVE_SITES`. A dead site cannot be quietly re-forgotten, and a repair cannot be quietly
//! half-landed.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, VmConstraint2, WindowExpr, parse_vm_descriptor2,
};
use dregg_circuit::effect_vm_descriptors::{WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV};
use dregg_circuit::lean_descriptor_air::{HashInput, LeanExpr, VmConstraint};
use dregg_circuit_prove::factory_leaf_adapter::FACTORY_CHILD_VK_CLAIM_LEN;
use dregg_circuit_prove::ivc_turn_chain::{
    BRIDGE_MINT_HASH_CLAIM_LEN, BRIDGE_MINT_HASH_PI, DECO_PAYMENT_HASH_CLAIM_LEN,
    DECO_PAYMENT_HASH_PI, FACTORY_CHILD_VK_PI_LO, HATCHERY_CONTRACT_HASH_PI_LO,
    MEMBERSHIP_CLAIM_PI_LO, SOVEREIGN_KEY_COMMIT_PI_LO,
};
use dregg_circuit_prove::membership_leaf_adapter::MEMBERSHIP_CLAIM_LEN;

// ============================================================================
// Committed-bytes helpers (the same surface the LIGHT CLIENT resolves)
// ============================================================================

fn member(tsv: &str, wire: &str) -> EffectVmDescriptor2 {
    let json = tsv
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(wire) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{wire} not in the staged wide registry"));
    parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{wire} must parse: {e:?}"))
}

fn expr_cols(e: &LeanExpr, out: &mut Vec<usize>) {
    match e {
        LeanExpr::Var(c) => out.push(*c),
        LeanExpr::Const(_) => {}
        LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
            expr_cols(a, out);
            expr_cols(b, out);
        }
    }
}

fn wexpr_cols(e: &WindowExpr, out: &mut Vec<usize>) {
    match e {
        WindowExpr::Loc(c) | WindowExpr::Nxt(c) => out.push(*c),
        WindowExpr::Const(_) => {}
        WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => {
            wexpr_cols(a, out);
            wexpr_cols(b, out);
        }
    }
}

/// The Rust twin of Lean's `UnforcedPiPins.forcedCols`: every column some NON-PIN constraint, hash
/// site or range tooth reads. A pinned column outside this set is one `dropUnforcedPins` deletes.
///
/// ⚠ `.transition hi lo` stores FACE OFFSETS on the wire, not columns — Lean's `refsC` resolves them
/// through `sbCol`/`saCol`. Resolving them here too is what makes this agree with the Lean fixpoint
/// theorem: measured over both wide registries, every surviving pin's column is in this set, exactly
/// as `unforcedPins_dropUnforcedPins` says it must be.
fn forced_cols(d: &EffectVmDescriptor2) -> Vec<usize> {
    use dregg_circuit::effect_vm::columns::{STATE_AFTER_BASE, STATE_BEFORE_BASE};
    let mut out = Vec::new();
    for c in &d.constraints {
        match c {
            VmConstraint2::Base(VmConstraint::PiBinding { .. }) => {}
            VmConstraint2::Base(VmConstraint::Gate(b))
            | VmConstraint2::Base(VmConstraint::Boundary { body: b, .. }) => expr_cols(b, &mut out),
            VmConstraint2::Base(VmConstraint::Transition { hi, lo }) => {
                out.push(STATE_BEFORE_BASE + *hi);
                out.push(STATE_AFTER_BASE + *lo);
            }
            VmConstraint2::WindowGate(w) => wexpr_cols(&w.body, &mut out),
            VmConstraint2::Lookup(l) => {
                for e in &l.tuple {
                    expr_cols(e, &mut out);
                }
            }
            VmConstraint2::MapOp(m) => {
                expr_cols(&m.guard, &mut out);
                expr_cols(&m.key, &mut out);
                expr_cols(&m.value, &mut out);
                for e in m.root.iter().chain(m.new_root.iter()) {
                    expr_cols(e, &mut out);
                }
            }
            VmConstraint2::MemOp(m) => {
                for e in [&m.guard, &m.addr, &m.value, &m.prev_value, &m.prev_serial] {
                    expr_cols(e, &mut out);
                }
            }
            VmConstraint2::UMemOp(m) => {
                for e in [
                    &m.guard,
                    &m.key,
                    &m.present,
                    &m.value,
                    &m.prev_present,
                    &m.prev_value,
                    &m.prev_serial,
                ] {
                    expr_cols(e, &mut out);
                }
            }
            VmConstraint2::ProofBind(p) => {
                for e in [&p.guard, &p.commit, &p.vk] {
                    expr_cols(e, &mut out);
                }
            }
        }
    }
    for s in &d.hash_sites {
        out.push(s.digest_col);
        for i in &s.inputs {
            if let HashInput::Col(c) = i {
                out.push(*c);
            }
        }
    }
    for r in &d.ranges {
        out.push(r.wire);
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// The column a `PiBinding` on `pi_index` pins, if any.
fn pinned_col(d: &EffectVmDescriptor2, pi_index: usize) -> Option<usize> {
    d.constraints.iter().find_map(|c| match c {
        VmConstraint2::Base(VmConstraint::PiBinding {
            col, pi_index: k, ..
        }) if *k == pi_index => Some(*col),
        _ => None,
    })
}

/// `(label, member key, claim PI base, claim length)`.
type Site = (&'static str, &'static str, usize, usize);

/// The carrier claim sites whose deployed pins are LIVE — pinned AND forced.
const LIVE_SITES: &[Site] = &[
    (
        "factory child_vk8",
        "factoryVmDescriptor2R24",
        FACTORY_CHILD_VK_PI_LO,
        FACTORY_CHILD_VK_CLAIM_LEN,
    ),
    (
        "hatchery contract_hash8",
        "factoryVmDescriptor2R24",
        HATCHERY_CONTRACT_HASH_PI_LO,
        8,
    ),
    (
        "sovereign KEY_COMMIT",
        "makeSovereignVmDescriptor2R24",
        SOVEREIGN_KEY_COMMIT_PI_LO,
        4,
    ),
];

/// ⚑ The carrier claim sites whose deployed pins are **DEAD** — the slot is inside `piCount` and NO
/// `PiBinding` names it, so the arm that locates it by index fails closed on every deployed leg.
/// Each entry is a live wound with an expiry: when the fold lands, the site moves to `LIVE_SITES`.
const KNOWN_DEAD_SITES: &[Site] = &[
    (
        "membership teeth (sender_leaf, authorized_root)",
        "transferVmDescriptor2R24",
        MEMBERSHIP_CLAIM_PI_LO,
        MEMBERSHIP_CLAIM_LEN,
    ),
    (
        "bridge mint_hash",
        "mintVmDescriptor2R24",
        BRIDGE_MINT_HASH_PI,
        BRIDGE_MINT_HASH_CLAIM_LEN,
    ),
    (
        "DECO payment_hash (the SAME slot as bridge)",
        "mintVmDescriptor2R24",
        DECO_PAYMENT_HASH_PI,
        DECO_PAYMENT_HASH_CLAIM_LEN,
    ),
];

const REGISTRIES: &[(&str, &str)] = &[
    ("wide", WIDE_REGISTRY_STAGED_TSV),
    ("welded", WIDE_UMEM_WELD_REGISTRY_TSV),
];

/// **THE LIVENESS GATE.** Every claim slot a carrier fold arm reads by index must be PINNED on the
/// committed bytes, and its column must be FORCED (read by a non-pin constraint) — otherwise the pin
/// is one `dropUnforcedPins` will delete on the next emit, and the arm is one emit from dead.
#[test]
fn every_live_fold_claim_slot_is_pinned_and_forced() {
    for (label, tsv) in REGISTRIES {
        for (name, key, lo, len) in LIVE_SITES {
            let d = member(tsv, key);
            let forced = forced_cols(&d);
            assert!(
                lo + len <= d.public_input_count,
                "{label}/{key}: {name} claims PI {lo}..{} but piCount is {}",
                lo + len,
                d.public_input_count
            );
            for k in *lo..lo + len {
                let col = pinned_col(&d, k).unwrap_or_else(|| {
                    panic!(
                        "{label}/{key}: {name} slot PI {k} carries NO PiBinding — the fold arm \
                         locates this slot BY the pin and is fail-closed on every deployed leg"
                    )
                });
                assert!(
                    forced.binary_search(&col).is_ok(),
                    "{label}/{key}: {name} slot PI {k} pins column {col}, which NO non-pin \
                     constraint reads — the prover chooses both sides, and the next emit's \
                     `dropUnforcedPins` deletes this pin (that is exactly how the membership and \
                     bridge sites died). Force the column; never exempt the pin."
                );
            }
        }
    }
}

/// **THE WOUND, MEASURED AND HELD OPEN.** Each entry asserts the site is STILL dead. This is not a
/// tolerance — it is a tripwire with the opposite polarity: the day the fold lands and the pin comes
/// back, this test goes red and the entry must be moved to `LIVE_SITES`. A repair cannot land
/// half-way, and a wound cannot be quietly re-forgotten.
///
/// ⚠ It also refuses the WRONG repair. If a future edit brings the pin back while the column is
/// still unforced — an exemption from the census rather than a forcing of the column — the
/// `LIVE_SITES` gate above catches it on the `forced` assertion, and this one catches the move.
#[test]
fn the_dead_fold_claim_slots_are_still_dead_and_named() {
    let mut report = Vec::new();
    for (label, tsv) in REGISTRIES {
        for (name, key, lo, len) in KNOWN_DEAD_SITES {
            let d = member(tsv, key);
            for k in *lo..lo + len {
                assert!(
                    k < d.public_input_count,
                    "{label}/{key}: {name} names PI {k} past piCount {} — the slot is not even \
                     published; the constant and the member have diverged",
                    d.public_input_count
                );
                let pin = pinned_col(&d, k);
                assert!(
                    pin.is_none(),
                    "{label}/{key}: {name} slot PI {k} IS pinned now (column {:?}) — the repair \
                     landed. Move this entry to `LIVE_SITES` so the forcing is asserted, and \
                     verify the column is forced rather than the pin exempted.",
                    pin
                );
                report.push(format!("{label}/{key} {name} PI {k}: UNPINNED"));
            }
        }
    }
    eprintln!(
        "FOLD-CLAIM LIVENESS verdict: {} dead claim slot(s) on the committed bytes.\n  {}\n\
         Each is a fold arm that refuses every deployed leg. The published PI survives as what it \
         always was — a verifier-supplied input the AIR ignores.",
        report.len(),
        report.join("\n  ")
    );
}
