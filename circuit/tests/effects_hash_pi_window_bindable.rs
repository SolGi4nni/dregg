//! # `PI[16..20)` — the `effects_hash` window: WHO PUBLISHES IT, AND WHO COULD BIND IT
//!
//! ## The wound this measures
//!
//! `circuit/src/effect_vm/pi.rs::EFFECTS_HASH_BASE` reserves four published slots for the felt-domain
//! `effects_hash` — the digest of *which effects this turn applied*. Across every deployed member of
//! every deployed registry, **no constraint binds any of them.** The value is written by the prover's
//! own trace generator (`trace.rs:1289`, the only non-test caller of `compute_effects_hash_4`) into
//! the PI vector, and nothing in the AIR relates it to a trace column.
//!
//! On a **full node** that is invisible, because `verify_and_commit_proof_rotated` regenerates the
//! whole PI vector from the ledger and substitutes its own, so the proof adds nothing the host did
//! not already compute. On the **ledgerless** path the PI vector comes off the wire, and a light
//! client reading those four slots is reading the prover. The two witness felts that used to carry
//! the value in-trace (`AUX_BASE + 4/5` = cols 94/95) are in the E1 kill-set of all 57 wide members,
//! under a criterion that IS the machine-derived proof nothing read them.
//!
//! The Lean-authored repair exists and is proved:
//! `metatheory/Dregg2/Circuit/Emit/EffectVmEffectsHashPin.lean` (`withEffectsHashPin`, 65 columns and
//! 27 constraints per member, `piCount` unchanged, `#assert_axioms`-clean on all eight rungs). It is
//! **not wired into the emit**, so nothing below has changed yet. This file is the pair of standing
//! measurements that (a) make the wound falsifiable and (b) keep the wiring from wedging.
//!
//! ## ⚑ Why (b) exists — a measured landmine, found before it was stepped on
//!
//! `withEffectsHashPin` pins `PI[16..20)` unconditionally, and its prose precondition — *"`PI[16..20)`
//! is already inside the rotated window"* — is true of 171 members and **false of three**. Applying it
//! at the emit chokepoints as written would have broken all three, two of them silently:
//!
//!   * the **v3** `heapWriteVmDescriptor2R24` declares `public_input_count = 4`, so a pin at PI 16
//!     is out of bounds and `check_descriptor2` (`descriptor_ir2.rs:1604`) refuses the member — the
//!     whole v3 registry then fails to load;
//!   * the **wide** and **welded** `heapWriteVmDescriptor2R24` declare 20 slots and **already pin
//!     16,17,18,19** to cols 2127..2130 (the heap-splice roots) on the last row. A second pin on the
//!     same slot forces two unrelated columns equal, so an honest heap-write trace becomes
//!     UNSATISFIABLE — **and the member still parses**, which is the dangerous half.
//!
//! [`effects_hash_pi_window_bindability_is_pinned`] is the census that names those three and refuses
//! to let a fourth appear unnoticed. The Lean side now carries the same predicate as
//! `EffectVmEffectsHashPin.ehPiWindowBindable`, and its emit-facing combinator
//! `withEffectsHashPinChecked` is an `Except` rather than a silent skip: a member quietly emitted
//! WITHOUT the pin is indistinguishable from one that never needed it, and that is the fail-open
//! twin of this whole class.
//!
//! ## The inversion, written down before it happens — WITH THE NUMBERS, MEASURED
//!
//! When the pin is wired, [`effects_hash_pi_window_is_bound_by_nothing`] must **flip**: `bound` goes
//! 0 → 4 per bindable member and the assertion becomes `bound == 4 * bindable`. It is written as an
//! equality over a named set, not a `> 0`, precisely so it cannot keep passing while the residue
//! changes character.
//!
//! ⚑ **The flip is not hypothetical — it was measured.** On 2026-07-31 `EmitWideRegistryProbe` was
//! wired to `withEffectsHashPin` on a scratch clone (never installed; `metatheory/Dregg2` was dirty
//! from three live lanes and the emit driver correctly refuses that) and run over all 57 wide
//! members. Against the committed `rotation-wide-registry-staged.tsv`:
//!
//!   * **56 of 57 take the pin**; `heapWrite` is skipped with `Δwidth = 0`, `Δconstraints = 0` —
//!     this file's exemption list is exactly the emit's;
//!   * `public_input_count` moves on **zero** members;
//!   * `Δconstraints = +27` on 54 members (the designed budget), +28 on `mint` and +33 on `custom`
//!     — the budget plus the pins the free-pin closure brings back.
//!   * ⚑ `Δwidth` was reported as +65/+53/+56/0, with the non-uniformity "recorded, not smoothed".
//!     **Re-measured 2026-07-31 on an independent decoder: the non-uniformity is a DEFECT.** The
//!     9–12 columns are the gentian refuse block's dead stride-tail, deleted because the pin lands
//!     ABOVE that block and slides `EmitWideRegistryProbe.e1Ceiling` (`traceWidth − 3·REFUSE_STRIDE`)
//!     65 columns up into it — on all 36 bare-cohort members and no others. The deployed producer
//!     runs `compact_e1_columns` on the PRE-gentian row, so it then refuses fail-closed (`mint`:
//!     "row width 1819 < E1 band end 1867"). Re-emitted with the ceiling also subtracting `EH_SPAN`:
//!     **Δwidth is +65 uniformly on all 56 bindable members, 0 on `heapWrite`, and the emitted
//!     `e1compact` kill-sets are byte-identical to the committed ones.** The real price is 65
//!     columns / 27 constraints, flat. See `EffectVmEffectsHashPin.lean` §Cost ⚑⚑.
//!   * ⚑⚑ **and the free-pin residue closes as a side effect.** `ehFreshCols` absorbs `prmCol 0..7`,
//!     so every effect-parameter column becomes read by a chip lookup: wide-registry pins go
//!     1628 → **1859**, row-local-free pins 6 → **0**, and the two `proof_bind`-only
//!     declaration pins on `customVmDescriptor2R24` go to **0** — the residue
//!     `unforced_pi_pin_census.rs::proof_bind_is_the_only_reader_of_the_custom_exposure_columns`
//!     names. `mintVmDescriptor2R24`'s mint-identity pin and six of `custom`'s octet limbs come
//!     BACK, kept by the same unchanged `dropUnforcedPins` because their columns are now forced.
//!     ⚑ CONFIRMED by re-measurement on a second decoder, 2026-07-31, and the restored pins are
//!     named: `mint` PI 46 → col 68; `custom` PI 47,48,49 → cols 73,74,75 and PI 55,56,57 → cols
//!     69,70,71. And the ANTI-VACUITY leg the closure needs: all **228** window pins across the 57
//!     wide members (224 new + `heapWrite`'s 4 pre-existing) are in `forcedCols`, in
//!     `forcedColsDenoting`, AND read by a chip lookup — FORCED, not declared. Every count here was
//!     taken against a baseline emit that reproduced the committed
//!     `rotation-wide-registry-staged.tsv` BYTE-IDENTICALLY, so the deltas are the pin's and not
//!     drift's.
//!     ⚠ Those two sibling tests must then flip too, and they must flip to "forced", never to an
//!     exemption.
//! ⚠ Whoever flips it must also flip `vk_epoch_misc_light_client_binding.rs`'s three
//! `hash_accepted` assertions — that file is green *because* a forged declared hash is accepted.
//!
//! Read-only w.r.t. `circuit/src`: this file authors no constraint and fixes nothing. The AIR is
//! Lean-authored.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, parse_vm_descriptor2};
use dregg_circuit::effect_vm::pi::{EFFECTS_HASH_BASE, EFFECTS_HASH_LEN};
use dregg_circuit::effect_vm_descriptors::{
    V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, welded_wide_members,
};
use dregg_circuit::lean_descriptor_air::VmConstraint;

/// The three deployed registries, by the label their emit driver uses. The welded set is DERIVED
/// from the bare wide registry plus the Lean-emitted contract table (`welded_wide_members`), not
/// read out of a committed TSV.
fn registries() -> Vec<(&'static str, Vec<(String, EffectVmDescriptor2)>)> {
    vec![
        ("v3", members(V3_STAGED_REGISTRY_TSV).collect()),
        ("wide", members(WIDE_REGISTRY_STAGED_TSV).collect()),
        (
            "welded",
            welded_wide_members()
                .into_iter()
                .map(|(key, d)| (key.to_string(), d))
                .collect(),
        ),
    ]
}

fn members(tsv: &str) -> impl Iterator<Item = (String, EffectVmDescriptor2)> + '_ {
    tsv.lines().filter(|l| !l.is_empty()).map(|line| {
        let mut it = line.splitn(3, '\t');
        let key = it.next().expect("registry key").to_string();
        let _name = it.next().expect("member name");
        let json = it.next().expect("member json");
        let d = parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{key} must parse: {e}"));
        (key, d)
    })
}

/// Every PI slot this member pins, with the column it names.
fn pinned_slots(d: &EffectVmDescriptor2) -> Vec<(usize, usize)> {
    d.constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) => {
                Some((*pi_index, *col))
            }
            _ => None,
        })
        .collect()
}

/// The effects-hash window as `pi.rs` declares it — derived, never transcribed, so a PI-layout move
/// re-aims this file instead of silently leaving it pointed at the wrong four slots.
fn window() -> std::ops::Range<usize> {
    EFFECTS_HASH_BASE..EFFECTS_HASH_BASE + EFFECTS_HASH_LEN
}

/// Why a member cannot take the pin. `None` = it can.
#[derive(Debug, PartialEq, Eq)]
enum NotBindable {
    /// `piCount` does not reach the window: a pin there is out of bounds and `check_descriptor2`
    /// refuses the member outright.
    OutOfRange { pi_count: usize },
    /// The window is already pinned to other columns: a second pin double-binds the slot and forces
    /// two unrelated columns equal, so an honest trace becomes unsatisfiable — and it still parses.
    AlreadyPinned { slots: Vec<(usize, usize)> },
}

fn bindability(d: &EffectVmDescriptor2) -> Option<NotBindable> {
    let w = window();
    if d.public_input_count < w.end {
        return Some(NotBindable::OutOfRange {
            pi_count: d.public_input_count,
        });
    }
    let mut taken: Vec<(usize, usize)> = pinned_slots(d)
        .into_iter()
        .filter(|(pi, _)| w.contains(pi))
        .collect();
    if taken.is_empty() {
        None
    } else {
        taken.sort_unstable();
        Some(NotBindable::AlreadyPinned { slots: taken })
    }
}

/// **THE APPLICABILITY CENSUS.** Which deployed members can carry the Lean-authored
/// `withEffectsHashPin`, and — the part that matters — exactly which cannot, and why.
///
/// This is not bookkeeping. The three exceptions below are the difference between the effects-hash
/// flag day landing and the flag day emitting one member that refuses to load and two that stop
/// proving. Both failure modes were measured on the committed bytes before any wiring existed.
///
/// It goes red three ways, all of which a future emitter needs to hear about:
///   * a **fourth** member leaves the EffectVM PI layout — the pin must then be refused on it too;
///   * one of the three **rejoins** it (e.g. `heapWrite` grows a full rotated PI vector) — the pin
///     becomes applicable and the Lean exemption is now the thing that is wrong;
///   * the wide `heapWrite`'s window pins **move off cols 2127..2130** — then whatever now occupies
///     `PI[16..20)` there is a different claim, and the double-pin analysis has to be redone.
#[test]
fn effects_hash_pi_window_bindability_is_pinned() {
    let w = window();
    assert_eq!(
        (w.start, w.len()),
        (16, 4),
        "the effects-hash PI window moved in `pi.rs`; every count below is about a different window"
    );

    let mut total = 0usize;
    let mut bindable = 0usize;
    let mut refused: Vec<(String, String, NotBindable)> = Vec::new();
    for (label, ms) in registries() {
        for (key, d) in ms {
            total += 1;
            match bindability(&d) {
                None => bindable += 1,
                Some(why) => refused.push((label.to_string(), key, why)),
            }
        }
    }
    refused.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
    eprintln!("effects-hash window {w:?}: {bindable} of {total} deployed members can take the pin");
    for r in &refused {
        eprintln!("   REFUSED {}/{}: {:?}", r.0, r.1, r.2);
    }

    assert_eq!(
        refused,
        vec![
            (
                "v3".to_string(),
                "heapWriteVmDescriptor2R24".to_string(),
                NotBindable::OutOfRange { pi_count: 4 }
            ),
            (
                "welded".to_string(),
                "heapWriteVmDescriptor2R24".to_string(),
                NotBindable::AlreadyPinned {
                    slots: vec![(16, 2127), (17, 2128), (18, 2129), (19, 2130)]
                }
            ),
            (
                "wide".to_string(),
                "heapWriteVmDescriptor2R24".to_string(),
                NotBindable::AlreadyPinned {
                    slots: vec![(16, 2127), (17, 2128), (18, 2129), (19, 2130)]
                }
            ),
        ],
        "the members the effects-hash pin must be REFUSED on, and the reason for each. \
         `heapWriteVmDescriptor2R24` is the one deployed member not on the EffectVM PI layout: the \
         v3 row publishes 4 slots (a pin at PI 16 is out of bounds and `check_descriptor2` refuses \
         the member), and the two wide rows publish 20 with the window already carrying the \
         heap-splice roots (a second pin forces `local[2127] = local[ehAccOut 0]`, so an honest \
         heap-write trace is UNSATISFIABLE — and it still parses, so it would land). The Lean twin \
         of this predicate is `EffectVmEffectsHashPin.ehPiWindowBindable`; if this list and that \
         predicate ever disagree, the emit is the thing to believe."
    );
    assert_eq!(
        (total, bindable),
        (174, 171),
        "174 deployed members across the three registries, 171 of them on the EffectVM PI layout"
    );
}

/// **THE WOUND, STANDING AND FALSIFIABLE.** Not one deployed member binds any slot of the
/// effects-hash window to any column. The four slots are published, carried through the rotated PI
/// vector, folded by `ivc_turn_chain`, and forced by nothing.
///
/// ⚑ **THIS TEST MUST INVERT, NOT BE DELETED.** When `withEffectsHashPinChecked` is wired into the
/// three emit drivers, `bound` becomes 171 and the assertion below becomes
/// `assert_eq!(bound, bindable)`. Whoever lands that must:
///   * flip the count here and say so in the commit;
///   * flip `circuit/tests/vk_epoch_misc_light_client_binding.rs` — it asserts `hash_accepted` in
///     three places and its helper prints the residual in words, so it is green *because* a forged
///     declared hash verifies. Until those flip, the pin has changed nothing observable.
///   * write the producer. `circuit/src/effect_vm/trace_rotated.rs` has **zero** `effects_hash`
///     references today, and `prove_vm_descriptor2` zero-extends short rows *before* its width
///     check — so an un-updated producer folds the IV over 65 zero columns and proves green.
#[test]
fn effects_hash_pi_window_is_bound_by_nothing() {
    let w = window();
    let mut bindable = 0usize;
    let mut bound = 0usize;
    let mut bound_detail: Vec<(String, String, usize, usize)> = Vec::new();
    for (label, ms) in registries() {
        for (key, d) in ms {
            if bindability(&d).is_some() {
                continue; // the three named exceptions; their window is a different claim
            }
            bindable += 1;
            for (pi, col) in pinned_slots(&d) {
                if w.contains(&pi) {
                    bound += 1;
                    bound_detail.push((label.to_string(), key.clone(), pi, col));
                }
            }
        }
    }
    eprintln!(
        "effects-hash window {w:?}: {bound} pins across the {bindable} members that could carry one"
    );
    assert_eq!(
        (bindable, bound),
        (171, 0),
        "MEASURED: of the 171 deployed members whose `PI[16..20)` is a free window, NONE binds it \
         to a trace column — the felt-domain `effects_hash` is host-only, and a ledgerless verifier \
         reading those four slots is reading the prover. The repair is Lean-authored and proved \
         (`Emit/EffectVmEffectsHashPin.lean`) and is NOT WIRED. When it is, this becomes \
         (171, 171·4) and the message says so. Found bound: {bound_detail:?}"
    );
}

/// **The other half of "host-only", so the first test cannot be satisfied by a decoder that stopped
/// looking.** The window's slots really are inside every bindable member's declared PI vector — they
/// are published, not absent. A census that mis-parsed and found no pins anywhere would pass
/// `bound == 0` for the wrong reason; this fails unless the slots exist to be pinned.
#[test]
fn the_effects_hash_slots_are_published_by_every_bindable_member() {
    let w = window();
    let mut checked = 0usize;
    for (label, ms) in registries() {
        for (key, d) in ms {
            if bindability(&d).is_some() {
                continue;
            }
            assert!(
                d.public_input_count >= w.end,
                "{label}/{key}: declares {} PI slots, which does not reach the effects-hash window \
                 {w:?} — then it should have been classified NOT bindable",
                d.public_input_count
            );
            checked += 1;
        }
    }
    assert_eq!(
        checked, 171,
        "every bindable member publishes the four slots it does not bind"
    );
}
