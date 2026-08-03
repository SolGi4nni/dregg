//! ⚑ **THE SECOND PEER-CHAIN LIGHT CLIENT EVER PROVED IN RUST — AND THE WIDTH REPAIR, EXHIBITED.**
//!
//! # What had never happened
//!
//! Five peer chains have a Lean-authored light-client verify AIR routed through `EmitByName.lean`
//! into `circuit/src/descriptor_by_name.rs`. Measured 2026-08-02, **none of the four
//! non-Mina ones had ever been proved**: `grep -rl lightclient-verify --include='*.rs'` returned
//! only `descriptor_by_name.rs`. "Producible by a node" was a claim about DISPATCH — a descriptor
//! that decodes and a name that resolves, with no prover ever having run the object. Mina closed on
//! 2026-08-02 (`turn/tests/mina_anchored_head_lands.rs`). This file closes Tendermint.
//!
//! # The wound it exhibits, and it is not incidental to the proving
//!
//! `dregg-tm-lightclient-verify::v1` shipped `bits: 64` on its range table. BabyBear is
//! `p = 2013265921 < 2^31 < 2^64`, so the declared interval `[0, 2^64)` **already contained every
//! field element** and all four range lookups refused nothing
//! (`Dregg2.Circuit.RangeFieldContainment.range_vacuous_at_or_above_31`, over all widths `≥ 31` and
//! all field elements — a theorem, not a witness).
//!
//! The four lookups are where every INEQUALITY in this AIR lives — the strict `>2/3` voting-power
//! threshold and the three time-window bounds — because a field has no order and each `≤` rides as
//! a non-negative slack. At 64 bits every one of them was satisfied by any assignment, so the AIR
//! enforced its equalities and NONE of its inequalities.
//!
//! ⚑ The concrete consequence, which `the_exactly_two_thirds_sub_quorum_is_refused` exhibits: the
//! exactly-2/3 sub-quorum (`signedPow = 2` of `totalPow = 3`) fills `TDIFF = 3·2 − 2·3 − 1 = −1`,
//! which on the wire is `p − 1 = 2013265920`. Tendermint's threshold is STRICT and that commit must
//! be rejected. `TM_BITS` is now 29 — the maximum wrap-free width at BabyBear
//! (`RangeFieldContainment.wrap_free_iff_le_29`; 30 already fails) — and `2013265920 >= 2^29`, so
//! the prover refuses it.
//!
//! `the_exactly_two_thirds_sub_quorum_is_admitted_at_a_vacuous_width` proves the OTHER half against
//! the running prover rather than asserting it: it hands the same forged row to a descriptor whose
//! only difference is a declared width whose interval covers the field, and that descriptor PROVES
//! AND VERIFIES it. Without that leg the repair would be a renumbering with a test that passes for
//! the wrong reason.
//!
//! # ⚑ AND A SECOND DEFECT, FOUND BY RUNNING IT: AT 64 BITS NOTHING PROVES AT ALL
//!
//! The vacuity above is what the DENOTATION says (`rangeRows 64` contains every field element). The
//! DEPLOYED prover does the opposite. Its layout bound is `(v as u64) >= (1u64 << rb.bits)`
//! (`circuit/src/descriptor_ir2.rs:4310`), and a `u64` shift by 64 is masked to a shift by 0 in a
//! release build — so the test collapses to `v >= 1` and EVERY nonzero value on a ranged wire is
//! refused. `the_shipped_64_bit_width_refuses_even_an_honest_header` measures exactly that: the
//! honest header that proves at 29 bits cannot be proved at the width that shipped. The same
//! masking hits the two 128-bit siblings (`128 % 64 == 0`).
//!
//! ⚑ **That is the mechanical reason this descriptor had never been proved: the first honest
//! attempt would have been refused by the prover's own layout code.** A descriptor can be emitted,
//! byte-pinned, name-dispatched, decoded and served, and still be an object no prover can run — and
//! the only thing that detects it is running one. The vacuity exhibit therefore runs at 32 bits,
//! which isolates the denotational defect from this separate `1u64 << bits` overflow.
//!
//! # Scope, said plainly
//!
//! `ED_OK` / `VSET_OK` / `EPOCH_OK` are witnessed carrier bits, not in-AIR Ed25519 and SHA-256; the
//! dregg-side STARK inherits the undischarged FRI floor; and the mod-`p` ↔ ℤ reading of the gates is
//! the shared field-soundness residual every Emit descriptor carries. This is a prover running the
//! served object with both polarities exhibited — **not** "Tendermint-valid", and not
//! "machine-checked".
//!
//! ⚠ And the residual the repair EXPOSED rather than closed: at 29 bits, completeness needs
//! `3·signedPow < 2^29`. Real Tendermint allows `MaxTotalVotingPower ≈ 2^60`. Those tallies never
//! fit a BabyBear column at any declared width — `TOTAL_POW` is one felt and one felt holds 30.9
//! bits. The 64-bit declaration did not make them fit, it made the shortfall invisible.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;

const TM_LC_VERIFY_DESCRIPTOR: &str = "dregg-tm-lightclient-verify::v1";

// Trace column layout — pinned to `LightClientTendermintAir`'s Lean `def`s (§1).
const CHAIN_ID: usize = 0;
const TS_CHAIN_ID: usize = 1;
const HEIGHT: usize = 2;
const TS_HEIGHT: usize = 3;
const HEADER_TIME: usize = 4;
const TIME: usize = 5;
const NOW: usize = 6;
const CLOCK_DRIFT: usize = 7;
const TRUSTING_PERIOD: usize = 8;
const TOTAL_POW: usize = 9;
const SIGNED_POW: usize = 10;
const TDIFF: usize = 11;
const TW_MONO: usize = 12;
const TW_DRIFT: usize = 13;
const TW_TRUST: usize = 14;
const ED_OK: usize = 15;
const VSET_OK: usize = 16;
const EPOCH_OK: usize = 17;
const TRUSTED_NEXT_VALS_ROOT: usize = 18;
const COMMITTED_APP_HASH_0: usize = 19;
const APP_HASH_LIMBS: usize = 9;
const CHAIN_ID_DOMAIN: usize = 28;

const TM_LC_WIDTH: usize = 29;
const TM_PI_COUNT: usize = 11;

/// The repaired declared width. `2^29 = 536870912`.
const TM_BITS: usize = 29;

/// The width that SHIPPED.
///
/// ⚑ In the DENOTATION (`DescriptorIR2.rangeRows 64`) this interval contains every BabyBear
/// element, so it refuses nothing. In the DEPLOYED Rust prover it refuses EVERYTHING — see
/// `the_shipped_64_bit_width_refuses_even_an_honest_header`. The two readings of the same declared
/// constant disagree maximally, and nothing had ever run to notice.
const SHIPPED_TM_BITS: usize = 64;

/// The smallest FULLY VACUOUS width (`2^32 > p`, so `[0, 2^32)` covers the field) that the
/// deployed prover can still execute — `1u64 << 32` is well-defined where `1u64 << 64` is not.
///
/// This is the width the vacuity exhibit runs at, because it isolates the denotational defect
/// (a range table that eliminates no assignment) from the separate `1u64 << bits` overflow.
const VACUOUS_BITS: usize = 32;

/// `LightClientTendermintAir` pads to a FRI-shaped power-of-two row count; the gates are single-row
/// and the pins are first-row, so every row is the same logical row.
const TRACE_ROWS: usize = 8;

const P: i64 = 2_013_265_921;

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(TM_LC_VERIFY_DESCRIPTOR).unwrap_or_else(|| {
        panic!(
            "{TM_LC_VERIFY_DESCRIPTOR} must dispatch: the Lean-emitted descriptor is routed through \
             EmitByName.lean and included by circuit/src/descriptor_by_name.rs"
        )
    })
}

/// The SAME served descriptor with the range table's declared width set to `bits`.
///
/// ⚑ This is the control. A repair that only shows the NEW width refusing a value has not shown the
/// value was ever admitted; this hands the identical trace to the identical AIR under the identical
/// prover, differing in exactly one integer.
fn desc_at_width(bits: usize) -> EffectVmDescriptor2 {
    let mut d = desc();
    for t in d.tables.iter_mut() {
        if let TableSem::Range { bits: b } = &mut t.sem {
            *b = bits;
        }
    }
    d
}

/// Field-encode a possibly-negative slack: in BabyBear a negative value IS `p − k`, which is the
/// element a range tooth must refuse. This is the whole subject of the file in one function.
fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(P) as u32)
}

/// One logical row of the Tendermint verify decision.
#[derive(Clone, Copy)]
struct Header {
    chain_id: u32,
    ts_chain_id: u32,
    height: u32,
    ts_height: u32,
    header_time: u32,
    time: u32,
    now: u32,
    clock_drift: u32,
    trusting_period: u32,
    total_pow: u32,
    signed_pow: u32,
    ed_ok: u32,
    vset_ok: u32,
    epoch_ok: u32,
}

/// An HONEST header: every slack is COMPUTED from the identity its gate forces, never claimed.
/// A caller cannot hand this a slack; it can only hand it the facts the slack is derived from.
fn honest(
    height: u32,
    ts_height: u32,
    header_time: u32,
    time: u32,
    now: u32,
    clock_drift: u32,
    trusting_period: u32,
    total_pow: u32,
    signed_pow: u32,
) -> Header {
    Header {
        chain_id: 0x0c05_0001,
        ts_chain_id: 0x0c05_0001,
        height,
        ts_height,
        header_time,
        time,
        now,
        clock_drift,
        trusting_period,
        total_pow,
        signed_pow,
        ed_ok: 1,
        vset_ok: 1,
        epoch_ok: 1,
    }
}

/// The 32-byte anchors this descriptor publishes, as the nine radix-`2^31` MSB-first limbs the
/// Lean module pins (`COMMITTED_APP_HASH_LIMBS = 9`, `⌈256/31⌉ = 9`).
fn limbs9(seed: u32) -> [u32; APP_HASH_LIMBS] {
    let mut out = [0u32; APP_HASH_LIMBS];
    for (i, o) in out.iter_mut().enumerate() {
        // Any in-field limb values will do: this leg is the PI-binding shape, not the hash.
        *o = seed.wrapping_mul(2_654_435_761).wrapping_add(i as u32 * 7) % 0x7fff_ffff;
    }
    out
}

/// Build the trace + public inputs. The four slacks are the genuine differences the gate identities
/// force — including when they are NEGATIVE, which is exactly the case the range teeth exist for.
fn trace_and_pis(h: Header) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let app_hash = limbs9(0xa17c_0de1);
    let next_vals = 0x51a7_e001u32;
    let domain = 0x0c05_0001u32;

    let mut r = vec![BabyBear::new(0); TM_LC_WIDTH];
    r[CHAIN_ID] = BabyBear::new(h.chain_id);
    r[TS_CHAIN_ID] = BabyBear::new(h.ts_chain_id);
    r[HEIGHT] = BabyBear::new(h.height);
    r[TS_HEIGHT] = BabyBear::new(h.ts_height);
    r[HEADER_TIME] = BabyBear::new(h.header_time);
    r[TIME] = BabyBear::new(h.time);
    r[NOW] = BabyBear::new(h.now);
    r[CLOCK_DRIFT] = BabyBear::new(h.clock_drift);
    r[TRUSTING_PERIOD] = BabyBear::new(h.trusting_period);
    r[TOTAL_POW] = BabyBear::new(h.total_pow);
    r[SIGNED_POW] = BabyBear::new(h.signed_pow);

    // The four slack identities, verbatim from `LightClientTendermintAir` §2.
    r[TDIFF] = felt(3 * h.signed_pow as i64 - 2 * h.total_pow as i64 - 1);
    r[TW_MONO] = felt(h.time as i64 - h.header_time as i64 - 1);
    r[TW_DRIFT] = felt(h.now as i64 + h.clock_drift as i64 - h.time as i64);
    r[TW_TRUST] = felt(h.header_time as i64 + h.trusting_period as i64 - h.now as i64 - 1);

    r[ED_OK] = BabyBear::new(h.ed_ok);
    r[VSET_OK] = BabyBear::new(h.vset_ok);
    r[EPOCH_OK] = BabyBear::new(h.epoch_ok);

    r[TRUSTED_NEXT_VALS_ROOT] = BabyBear::new(next_vals);
    for (i, l) in app_hash.iter().enumerate() {
        r[COMMITTED_APP_HASH_0 + i] = BabyBear::new(*l);
    }
    r[CHAIN_ID_DOMAIN] = BabyBear::new(domain);

    let mut pis = vec![BabyBear::new(0); TM_PI_COUNT];
    pis[0] = BabyBear::new(next_vals);
    for (i, l) in app_hash.iter().enumerate() {
        pis[1 + i] = BabyBear::new(*l);
    }
    pis[10] = BabyBear::new(domain);

    (vec![r; TRACE_ROWS], pis)
}

/// `Ok(())` iff the descriptor ACCEPTS this witness — PROVE and VERIFY, both legs.
///
/// A refusal has three shapes and all three are refusals: an `Err` from the prover (how the RANGE
/// teeth refuse — `row 0: range wire N value V >= 2^29`), a panic out of plonky3's debug constraint
/// check (how the ALGEBRAIC gates refuse in a debug build), and an `Err` from the verifier. Caught
/// the same way the deployed consumer catches it, so a forged witness is a fail-closed REJECTION and
/// never an unwind through the caller.
fn descriptor_accepts_under(d: &EffectVmDescriptor2, h: Header) -> Result<(), String> {
    let (trace, pis) = trace_and_pis(h);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mem = MemBoundaryWitness::default();
        let heaps: Vec<Vec<HeapLeaf>> = vec![];
        let proof = prove_vm_descriptor2(d, &trace, &pis, &mem, &heaps)
            .map_err(|e| format!("prover refused: {e}"))?;
        verify_vm_descriptor2(d, &proof, &pis).map_err(|e| format!("verifier refused: {e:?}"))
    }));
    match outcome {
        Ok(r) => r,
        Err(_) => {
            Err("prover/verifier PANICKED — an emitted gate is unsatisfied on this row".to_string())
        }
    }
}

fn descriptor_accepts(h: Header) -> Result<(), String> {
    descriptor_accepts_under(&desc(), h)
}

/// Quieten the default panic printer for the refusal cases; restored on `Drop`.
struct QuietPanics(Option<Box<dyn Fn(&std::panic::PanicHookInfo<'_>) + Sync + Send + 'static>>);

impl QuietPanics {
    fn new() -> Self {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        Self(Some(prev))
    }
}

impl Drop for QuietPanics {
    fn drop(&mut self) {
        // ⚠ `set_hook` PANICS if called from a panicking thread, and a panic inside a `Drop` during
        // unwind is a NON-UNWINDING panic: the process aborts and the harness reports
        // `signal: 6, SIGABRT` with no failing assertion named. Measured on this file's first run —
        // an ordinary `expect` failure was rendered as a process abort. Restore only when we are
        // not already unwinding.
        if std::thread::panicking() {
            return;
        }
        if let Some(h) = self.0.take() {
            std::panic::set_hook(h);
        }
    }
}

/// An honest adjacent header: height 1001 on trust at 1000, second-resolution times, a genuine
/// supermajority (`signedPow = 700` of `totalPow = 1000` — comfortably over 2/3).
fn honest_header() -> Header {
    honest(
        1001,
        1000,
        1_700_000_000,
        1_700_000_006,
        1_700_000_010,
        5,
        1_209_600,
        1000,
        700,
    )
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The served object
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The descriptor this tree serves is the one the Lean module declares — width, PI count,
/// constraint count, and the REPAIRED range width.
#[test]
fn the_served_descriptor_is_the_lean_emitted_one() {
    let d = desc();
    assert_eq!(d.name, TM_LC_VERIFY_DESCRIPTOR);
    assert_eq!(d.trace_width, TM_LC_WIDTH);
    assert_eq!(d.public_input_count, TM_PI_COUNT);
    // 13 gates + 4 range lookups + 11 PI pins.
    assert_eq!(d.constraints.len(), 24);
    assert_eq!(d.tables.len(), 1);

    // ⚑ THE REPAIR, ON THE SERVED OBJECT. `bits` is 29, not the shipped 64.
    let bits = match d.tables[0].sem {
        TableSem::Range { bits } => bits,
        _ => panic!("table 0 must be a range table"),
    };
    assert_eq!(
        bits, TM_BITS,
        "the served range table must be at the repaired width"
    );
    assert!(
        (1i64 << bits) < P,
        "the declared interval must sit INSIDE the field — this is the containment leg, and it was \
         FALSE at 64 bits where 2^64 > p and the table contained every field element"
    );
    assert!(
        (1i64 << (bits + 1)) <= P,
        "and it must be WRAP-FREE: p - 2^bits >= 2^bits, so a negative slack of any magnitude the \
         interval can itself reach lands outside it. False at 30, false at 64."
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// Positive polarity — without this every refusal below is satisfied by a descriptor that
// refuses everything.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **A PROVER HAS NOW RUN THIS DESCRIPTOR.** An honest adjacent Tendermint header with a genuine
/// supermajority PROVES and VERIFIES against the served, Lean-emitted AIR.
#[test]
fn an_honest_supermajority_header_proves_and_verifies() {
    let h = honest_header();
    // The honest slacks are all non-negative — the header really is inside every window.
    assert_eq!(3 * h.signed_pow as i64 - 2 * h.total_pow as i64 - 1, 99);
    descriptor_accepts(h).expect("an honest Tendermint header must prove and verify");
}

/// A header at the very edge of honesty still proves: the smallest strictly-over-2/3 commit
/// (`signedPow = 3` of `totalPow = 4` — `3·3 − 2·4 − 1 = 0`) fills `TDIFF = 0`, the interval's floor.
#[test]
fn the_minimal_strict_supermajority_proves() {
    let mut h = honest_header();
    h.total_pow = 4;
    h.signed_pow = 3;
    assert_eq!(3 * h.signed_pow as i64 - 2 * h.total_pow as i64 - 1, 0);
    descriptor_accepts(h).expect("the minimal strict supermajority must prove");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE WIDTH REPAIR, both halves, on the running prover
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **THE TOOTH.** The exactly-2/3 sub-quorum (`signedPow = 2` of `totalPow = 3`) is REFUSED by
/// the repaired descriptor. `TDIFF` fills to `−1`, which is the field element `p − 1 = 2013265920`,
/// and `2013265920 >= 2^29`. Tendermint's threshold is STRICT; this commit must not finalize.
///
/// The refusal is the RANGE tooth, not a gate: `tdiffBody` VANISHES on this row
/// (`Dregg2.Circuit.Emit.LightClientTendermintAir.tdiff_fills_to_minus_one_at_exactly_two_thirds`),
/// so every algebraic constraint is satisfied and only the lookup has no table row.
#[test]
fn the_exactly_two_thirds_sub_quorum_is_refused() {
    let _q = QuietPanics::new();
    let mut h = honest_header();
    h.total_pow = 3;
    h.signed_pow = 2;

    let slack = 3 * h.signed_pow as i64 - 2 * h.total_pow as i64 - 1;
    assert_eq!(slack, -1, "the exactly-2/3 commit fills TDIFF to -1");
    assert_eq!(
        felt(slack).as_u32() as i64,
        P - 1,
        "which on the wire is p - 1"
    );

    let err = descriptor_accepts(h)
        .expect_err("the exactly-2/3 sub-quorum must be refused by the repaired descriptor");
    eprintln!("exactly-2/3 sub-quorum refused: {err}");
    assert!(
        err.contains(&format!("{}", P - 1)) || err.contains("range wire"),
        "the refusal must be the RANGE tooth on the wrapped slack, got: {err}"
    );
}

/// ⚑ **AND THE OTHER HALF: A VACUOUS WIDTH ADMITS THE FORGERY.** The identical forged row, the
/// identical AIR, the identical prover, with `bits` at 32 — a width whose interval `[0, 2^32)`
/// covers the whole field, exactly as the shipped 64 did. It PROVES AND VERIFIES.
///
/// This is what makes the narrowing a repair rather than a renumbering, and it is measured on the
/// running prover rather than asserted. The exactly-2/3 sub-quorum finalizes.
#[test]
fn the_exactly_two_thirds_sub_quorum_is_admitted_at_a_vacuous_width() {
    let mut h = honest_header();
    h.total_pow = 3;
    h.signed_pow = 2;

    assert!(
        (1u64 << VACUOUS_BITS) > P as u64,
        "the control width must actually be vacuous — its interval must cover the field"
    );
    let d = desc_at_width(VACUOUS_BITS);
    assert!(matches!(d.tables[0].sem, TableSem::Range { bits } if bits == VACUOUS_BITS));

    descriptor_accepts_under(&d, h).expect(
        "⚑ THE VACUITY, EXHIBITED ON THE RUNNING PROVER: at a width whose interval covers the \
         field, the exactly-2/3 sub-quorum PROVES AND VERIFIES. If this starts failing, the \
         vacuity premise needs re-measuring.",
    );
}

/// ⚑ **WHAT THE SHIPPED WIDTH ACTUALLY DID, AND IT IS NOT WHAT THE DENOTATION SAYS.**
///
/// `dregg-tm-lightclient-verify::v1` shipped `bits: 64`. In Lean's `rangeRows 64` that interval
/// contains every field element and the tooth refuses NOTHING. In the deployed Rust prover it
/// refuses EVERYTHING: the layout filler's bound is `(v as u64) >= (1u64 << rb.bits)`
/// (`circuit/src/descriptor_ir2.rs:4310`), and a `u64` shift by 64 is masked to a shift by 0 in a
/// release build, so the test becomes `v >= 1` and every nonzero value on a ranged wire is refused.
///
/// So an HONEST Tendermint header — the positive polarity that proves at 29 bits — could not be
/// proved at all at the width that shipped. **That is the mechanical reason no prover had ever run
/// this descriptor: the first honest attempt would have been refused.** The same masking applies to
/// the two 128-bit siblings (`128 % 64 == 0`).
///
/// ⚠ Stated at the resolution it was measured: this is the observed behaviour of THIS prover on
/// THIS descriptor, in a release build. It is not a claim about what any `bits >= 31` descriptor
/// does — 32 through 63 shift fine and are vacuous in both readings, which is what the test above
/// exhibits.
#[test]
fn the_shipped_64_bit_width_refuses_even_an_honest_header() {
    let _q = QuietPanics::new();
    let h = honest_header();
    // The very witness that PROVES at the repaired width.
    descriptor_accepts(h).expect("the honest header proves at 29 bits");

    let shipped = desc_at_width(SHIPPED_TM_BITS);
    let err = descriptor_accepts_under(&shipped, h).expect_err(
        "⚑ at the SHIPPED bits=64 the honest header must be REFUSED — the u64 shift masks and the \
         range bound collapses to `v >= 1`",
    );
    eprintln!("honest header at the shipped bits=64: {err}");
    assert!(
        err.contains("range wire"),
        "the refusal must come from the range layout bound, got: {err}"
    );
}

/// The same pairing on the OTHER kind of tooth: a header from the FUTURE. `time` beyond
/// `now + clockDrift` fills `TW_DRIFT` negative — refused at 29, admitted at a vacuous width.
#[test]
fn a_header_from_the_future_is_refused_and_is_admitted_when_vacuous() {
    let _q = QuietPanics::new();
    let mut h = honest_header();
    h.time = h.now + h.clock_drift + 7; // seven seconds past the drift bound

    let slack = h.now as i64 + h.clock_drift as i64 - h.time as i64;
    assert_eq!(slack, -7);
    assert_eq!(felt(slack).as_u32() as i64, P - 7);

    let err = descriptor_accepts(h).expect_err("a future header must be refused at 29 bits");
    eprintln!("header from the future refused: {err}");

    descriptor_accepts_under(&desc_at_width(VACUOUS_BITS), h)
        .expect("⚑ and at a vacuous width the SAME future header proves and verifies");
}

/// And on the trusting-period tooth: a header older than the trusting period fills `TW_TRUST`
/// negative. Refused at 29, admitted at a vacuous width.
#[test]
fn an_expired_trusting_period_is_refused_and_is_admitted_when_vacuous() {
    let _q = QuietPanics::new();
    let mut h = honest_header();
    // now sits one second past headerTime + trustingPeriod
    h.now = h.header_time + h.trusting_period;
    h.time = h.header_time + 1;
    h.clock_drift = h.now - h.time; // keep the drift tooth satisfied so only TW_TRUST bites

    let slack = h.header_time as i64 + h.trusting_period as i64 - h.now as i64 - 1;
    assert_eq!(slack, -1);

    let err = descriptor_accepts(h).expect_err("an expired trusting period must be refused");
    eprintln!("expired trusting period refused: {err}");

    descriptor_accepts_under(&desc_at_width(VACUOUS_BITS), h)
        .expect("⚑ and at a vacuous width the SAME expired header proves and verifies");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The ALGEBRAIC teeth still bite — the narrowing did not become the only check
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// A cross-chain replay is refused by the chain-id gate at BOTH widths — this refusal never
/// depended on the range table, and the test says so by exercising both descriptors.
#[test]
fn a_cross_chain_replay_is_refused_at_both_widths() {
    let _q = QuietPanics::new();
    let mut h = honest_header();
    h.chain_id = 0x0c05_0002; // a different chain's header against this trust store

    descriptor_accepts(h).expect_err("a foreign chain-id must be refused");
    descriptor_accepts_under(&desc_at_width(VACUOUS_BITS), h)
        .expect_err("and the chain-id gate never needed the range table");
}

/// A non-adjacent height is refused by the height gate at both widths.
#[test]
fn a_non_adjacent_height_is_refused_at_both_widths() {
    let _q = QuietPanics::new();
    let mut h = honest_header();
    h.height = h.ts_height + 5; // skipping verification is not this descriptor's shape

    descriptor_accepts(h).expect_err("a non-adjacent height must be refused");
    descriptor_accepts_under(&desc_at_width(VACUOUS_BITS), h).expect_err("at either width");
}

/// A forged carrier — the Ed25519 batch-verify bit cleared — is refused by its gate at both widths.
#[test]
fn a_cleared_ed25519_carrier_is_refused_at_both_widths() {
    let _q = QuietPanics::new();
    let mut h = honest_header();
    h.ed_ok = 0;

    descriptor_accepts(h).expect_err("a cleared Ed25519 carrier must be refused");
    descriptor_accepts_under(&desc_at_width(VACUOUS_BITS), h).expect_err("at either width");
}
