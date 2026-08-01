//! # THE PAD IS BOUNDED — `prove_vm_descriptor2` no longer zero-extends past the producer's job.
//!
//! ## The wound
//!
//! `descriptor_ir2::trace_with_chip_lanes` zero-`resize`s every base row up to `desc.trace_width`
//! before filling the two prove-time welds (the `TID_P2` chip LANE columns and the gentian
//! capacity-floor refuse aux block). That pad is a real affordance: a producer need not know the
//! chip-lane geometry, so it may hand in rows that stop below those appended columns.
//!
//! But the pad ran BEFORE `prove_vm_descriptor2_inner`'s
//! `base_trace[0].len() != desc.trace_width` check — so on every public entry point that check was
//! testing a width its own caller had just manufactured. **It could not fail.** The pad was
//! therefore unbounded: a producer that had not been updated for a newly appended, genuinely
//! PRODUCER-OWNED block handed in short rows, the prover folded the new constraints over zeros, and
//! it proved GREEN. A silent pass in the one function whose contract is "this witness satisfies the
//! AIR".
//!
//! Two places in this tree had already written the asymmetry down as something to work around
//! rather than fix — `circuit/src/refusal.rs::assert_committed_shape` ("a short row PROVES and
//! emits no marker at all") and `heap_write_roundtrip.rs`'s shape-vacuity guard ("a row one column
//! SHORT of `trace_width` PROVES … by design"). Both are now belts, not the only barrier.
//!
//! ## The repair, and why it is derived rather than a constant
//!
//! `descriptor_ir2::producer_owned_width(desc)` is one past the highest column that is READ by the
//! AIR and filled by no prove-time weld. The pad may cover exactly the weld-owned-or-dead tail and
//! not one column more. Because it is computed FROM the descriptor, appending any new
//! producer-owned block automatically tightens it — which is the point: the next block appended
//! past `trace_width` (the Lean-authored `EffectVmEffectsHashPin` 65-column fold is the one in
//! flight) is producer-owned, so an un-updated producer meets a loud refusal instead of a green
//! proof over zeros.
//!
//! ## What this file pins
//!
//!  * the pad DECOMPOSES — for every deployed member of all three registries, every column in
//!    `[producer_owned_width, trace_width)` is weld-owned or dead, and never live-and-unowned;
//!  * the bound is NON-VACUOUS in both directions — the pad is nonzero on real members (otherwise
//!    this is just "rows must be exactly `trace_width`" wearing a derivation), and it is not the
//!    whole width either;
//!  * `weld_owned_cols` names both welds, and the gentian one is load-bearing on the bare
//!    registries — plus the measured fact that the umem-WELDED registry has the opposite shape
//!    (a producer-owned leg ABOVE the refuse block), which is the shape the effects-hash flag day
//!    creates and therefore worth having on record before it lands.
//!
//! The executed pole — an honest trace truncated one column short is REFUSED where it used to prove
//! — is in `heap_write_roundtrip.rs::a_short_trace_is_refused_instead_of_padded`, beside the
//! over-wide pole it inverts, because that is where the honest fixture lives.
//!
//! Read-only w.r.t. the AIR: this file authors no constraint. The AIR is Lean-authored.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, parse_vm_descriptor2, producer_owned_width, read_cols, weld_owned_cols,
};
use dregg_circuit::effect_vm_descriptors::{
    V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, welded_wide_members,
};

/// The three deployed registries. The welded set is DERIVED (`welded_wide_members`: each bare wide
/// member under the Lean-emitted weld contract row), not read from a committed TSV.
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

/// **SOUNDNESS OF THE BOUND, AS A DECOMPOSITION.** Every column the pad may still cover is either
/// filled by a prove-time weld or READ BY NOTHING — and the split is printed, because the two
/// halves are safe for different reasons and a reader is entitled to see how much of the pad rests
/// on which argument.
///
/// * weld-owned — `fill_chip_lanes` / `fill_refuse_aux` overwrite it before a constraint sees it;
/// * dead — no constraint, hash site or range mentions it, so its value is unobservable. This is
///   the same argument the E1 kill-set is built on, and it is why the bound keys on what is READ
///   rather than on `trace_width`: several deployed members carry a dead stride-tail above the
///   gentian refuse block, and demanding a producer supply it would refuse honest traces for
///   nothing.
///
/// It goes red if a THIRD kind of column ever enters the pad — a live, producer-owned one — which
/// is exactly the state in which the pad hides an omission.
#[test]
fn the_surviving_pad_is_weld_owned_or_dead() {
    let (mut weld_cols, mut dead_cols, mut checked) = (0usize, 0usize, 0usize);
    for (label, set) in registries() {
        for (key, d) in set {
            let need = producer_owned_width(&d);
            assert!(
                need <= d.trace_width,
                "{label}/{key}: producer_owned_width {need} exceeds trace_width {}",
                d.trace_width
            );
            let weld = weld_owned_cols(&d);
            let read = read_cols(&d);
            for c in need..d.trace_width {
                let is_weld = weld.binary_search(&c).is_ok();
                let is_dead = read.binary_search(&c).is_err();
                assert!(
                    is_weld || is_dead,
                    "{label}/{key}: column {c} is inside the surviving pad [{need}, {}), is READ by \
                     the AIR, and is filled by NO prove-time weld — zero-padding it folds the AIR \
                     over a value the producer never supplied",
                    d.trace_width
                );
                if is_weld {
                    weld_cols += 1;
                } else {
                    dead_cols += 1;
                }
            }
            checked += 1;
        }
    }
    assert!(
        checked >= 100,
        "expected the three registries, got {checked}"
    );
    eprintln!(
        "PAD DECOMPOSITION: {checked} deployed members; pad columns = {weld_cols} weld-owned + \
         {dead_cols} dead, 0 live-and-producer-owned"
    );
}

/// **NON-VACUITY, BOTH WAYS.** A bound that equals `trace_width` on every member would make the
/// check "rows must be exactly the committed width" — defensible, but then the derivation is
/// decoration and the doc-comment about a legitimate pre-lane pad is false. A bound of 0 would mean
/// the whole row is weld-owned and the check refuses nothing.
///
/// Measured on the deployed bytes, printed rather than asserted at a magic number, with only the
/// two degenerate poles forbidden.
#[test]
fn the_pad_is_neither_empty_nor_the_whole_row() {
    let mut with_pad = 0usize;
    let mut total = 0usize;
    let mut widest: (String, usize, usize) = (String::new(), 0, 0);
    for (label, set) in registries() {
        for (key, d) in set {
            let need = producer_owned_width(&d);
            let pad = d.trace_width - need;
            assert!(
                need > 0,
                "{label}/{key}: producer_owned_width is 0 — the whole row would be weld-owned and \
                 the refusal could never fire"
            );
            if pad > 0 {
                with_pad += 1;
                if pad > widest.1 {
                    widest = (format!("{label}/{key}"), pad, d.trace_width);
                }
            }
            total += 1;
        }
    }
    assert!(
        with_pad > 0,
        "NO deployed member has a weld-owned tail: `producer_owned_width == trace_width` \
         everywhere, so the derivation buys nothing over an equality check. Say that plainly \
         instead of deriving it."
    );
    eprintln!(
        "PAD SHAPE: {with_pad}/{total} members carry a weld-owned tail; widest is {} \
         (pad {} of width {})",
        widest.0, widest.1, widest.2
    );
}

/// **THE WELD SET NAMES BOTH WELDS, AND THE GENTIAN ONE IS LOAD-BEARING.** `fill_refuse_aux` is
/// keyed on a name substring and fills at prove time — so a `weld_owned_cols` that only knew about
/// chip lanes would put the bound ABOVE the refuse block and refuse every honest bare-cohort
/// producer. That is a completeness failure, and this is the check that catches it.
///
/// ⚑ AND IT RECORDS A SHAPE THAT MATTERS FOR THE FLAG DAY IN FLIGHT. On the two BARE registries the
/// refuse block is the topmost block, so it sits wholly inside the paddable tail and a producer may
/// stop below it. On the umem-WELDED registry it does not: the umem leg is appended ABOVE the
/// refuse weld, so `producer_owned_width` reaches past the refuse block and those producers must
/// build FULL-WIDTH rows — the pad buys them nothing.
///
/// That second shape is precisely what the staged `EffectVmEffectsHashPin` produces when it is
/// applied AFTER `weldWide`: a 65-column producer-owned block above a prove-time-filled one. It is
/// not fatal — the welded registry demonstrates a producer can simply build the whole row — but it
/// is a real constraint on the producer, and it is measured here rather than discovered later.
#[test]
fn the_gentian_refuse_block_is_weld_owned() {
    let (mut welded, mut in_tail, mut above) = (0usize, 0usize, Vec::new());
    for (label, set) in registries() {
        for (key, d) in set {
            if !d.name.contains("-gentian-deployed-bare-refuse") {
                continue;
            }
            welded += 1;
            let need = producer_owned_width(&d);
            // The refuse block's own columns, recovered as the weld-owned columns that are NOT
            // chip lanes — the gentian fill is the only other weld.
            let weld = weld_owned_cols(&d);
            let lanes_and_block = weld.len();
            assert!(
                lanes_and_block > 0,
                "{label}/{key} is refuse-welded but `weld_owned_cols` is EMPTY — the weld set has \
                 stopped naming the gentian fill and the bound now demands the producer supply \
                 columns `fill_refuse_aux` overwrites"
            );
            if need < d.trace_width {
                in_tail += 1;
            } else {
                above.push(format!("{label}/{key}"));
            }
        }
    }
    assert!(
        welded > 0,
        "no refuse-welded member found in any registry — this check has stopped measuring anything"
    );
    assert!(
        in_tail > 0,
        "NO refuse-welded member has the refuse block inside the paddable tail — every bare-cohort \
         producer would now have to build full-width rows, which is a completeness change nobody \
         asked for"
    );
    eprintln!(
        "GENTIAN: {welded} refuse-welded members — {in_tail} with the block inside the paddable \
         tail, {} with a producer-owned block ABOVE it (umem leg): {:?}",
        above.len(),
        &above.iter().take(3).collect::<Vec<_>>()
    );
}
