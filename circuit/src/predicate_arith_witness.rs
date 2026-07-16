//! Rust witness builder for the emitted **arithmetic threshold** descriptor
//! (`dregg-predicate-arith-ge::threshold-v1`, authored in
//! `metatheory/Dregg2/Circuit/Emit/PredicatesArithmeticEmit.lean`).
//!
//! The arithmetic-threshold descriptor proves ONE statement: *the value covered by the public
//! `fact_commitment` — which the verifier sources from trusted token state — satisfies
//! `value ≥ threshold` for a PUBLIC `threshold`.*
//!
//! That statement is a conjunction with a SHARED variable. `value ≥ threshold` alone is worthless:
//! it is a claim about a number the prover chose. What makes it a claim about TOKEN STATE is the
//! second conjunct,
//! `fact_commitment = hash_4_to_1([hash_fact(pred, [value, t1, t2]), state_root, blinding, 0])`,
//! binding the compared column to the committed fact. Both conjuncts are in the circuit, and the
//! variable they share is `INPUT` (col 0).
//!
//! ## Privacy and soundness are NOT a tradeoff here
//!
//! The commitment is BLINDED by a private witness column ([`BLINDING`], col 24) that the prover
//! draws fresh per presentation, so two proofs about the SAME fact carry DIFFERENT public
//! `fact_commitment`s and colluding verifiers cannot correlate them. This costs the weld nothing:
//! blinding moves the commitment within the image of `hash_4_to_1([fact_hash, state_root, ·, 0])`,
//! while leg 1 pins `fact_hash` to the compared `INPUT`. Every commitment any blinding can reach
//! still opens to the value being compared. Unlinkability rerandomizes WHICH commitment names the
//! fact; the weld fixes WHICH fact is named. The two properties touch different arguments of the
//! same hash, which is why the earlier "blinding and the weld are mutually exclusive" reading was
//! wrong — and why the descriptor carries both at once. See [`Blinding`].
//!
//! ## The layout (a single logical row, repeated to a power-of-two height)
//!
//! Mirrors `PredicatesArithmeticEmit.lean` §1 — that file is the SOURCE OF TRUTH for these indices.
//!
//! | col     | name                | meaning                                                        |
//! |---------|---------------------|----------------------------------------------------------------|
//! | 0       | `INPUT`             | the private compared value; ALSO `terms[0]` of the hashed fact  |
//! | 1       | `SLOT_A`            | the compiled expression-A result slot (`= INPUT` for bare-Input)|
//! | 2       | `THRESHOLD`         | the public comparison target, PI-bound to `PI_THRESHOLD`        |
//! | 3       | `DIFF`              | `value − threshold`, range-proved into `[0, 2^29)`              |
//! | 4       | `FACT_COMMITMENT`   | the fact commitment, PI-bound — and the weld's leg-2 DIGEST     |
//! | 5       | `PREDICATE_SYM`     | the predicate symbol entering `hash_fact`                       |
//! | 6       | `TERM1`             | the fact's second term                                          |
//! | 7       | `TERM2`             | the fact's third term                                           |
//! | 8       | `STATE_ROOT`        | the token state root the commitment covers                      |
//! | 9       | `FACT_HASH`         | `hash_fact(pred, [INPUT, t1, t2])` — the weld's leg-1 DIGEST    |
//! | 10..=16 | `FACTHASH_LANES`    | out-lanes 1..7 of the arity-7 fact-hash chip lookup             |
//! | 17..=23 | `FACTCOMMIT_LANES`  | out-lanes 1..7 of the arity-4 fact-commitment chip lookup       |
//! | 24      | `BLINDING`          | the PRIVATE per-presentation blinding factor (leg-2 input 2)   |
//!
//! The diff range-decomposition limbs the hand AIR lays down as ~30 explicit bit columns are NOT
//! base columns here: the descriptor's `⟨range, [DIFF]⟩` lookup makes the IR-v2 assembler
//! (`descriptor_ir2.rs::build_traces`) append the `decomp_cols(29)` limbs past `trace_width`.
//! The 2×7 chip LANES are base columns (10..23) but this builder leaves them zero — the prover's
//! `trace_with_chip_lanes` fills them (`descriptor_ir2.rs::fill_chip_lanes`). What a producer MUST
//! fill is the two DIGEST columns (4 and 9); those are this builder's job, and they are the weld.
//!
//! ## The teeth
//!
//! [`predicate_arith_witness`] is purely MECHANICAL — it does NOT enforce `value ≥ threshold`; it
//! computes `DIFF = value − threshold` in the field and lets the DESCRIPTOR be the judge:
//!   * C3 (`SLOT_A − INPUT == 0`) and C5 (`DIFF − SLOT_A + THRESHOLD == 0`) hold BY CONSTRUCTION
//!     on every row this builder emits (so a forge that keeps them consistent isolates C6);
//!   * C6 (`DIFF ∈ [0, 2^29)`) is the LOAD-BEARING comparison tooth — a `value < threshold` witness
//!     wraps `DIFF` to `p − (threshold − value)`, far outside the interval, with no valid limb
//!     decomposition (UNSAT), which is exactly how the descriptor refuses a `<` claim;
//!   * C1 / C2 pin `THRESHOLD` / `FACT_COMMITMENT` to the public inputs, so a forged public
//!     `(threshold, fact_commitment)` is refused at verify;
//!   * **the two Poseidon2 chip lookups are the VALUE↔FACT WELD** — leg 1 forces
//!     `FACT_HASH = hash_fact(PREDICATE_SYM, [INPUT, TERM1, TERM2])` over the SAME `INPUT` column
//!     the comparison bounds, and leg 2 forces
//!     `FACT_COMMITMENT = hash_4_to_1([FACT_HASH, STATE_ROOT, BLINDING, 0])`. Together they make
//!     col 4's constraint
//!     set intersect col 0's, which is the whole point: without them the AIR is the FREE CONJUNCTION
//!     of "some value is ≥ threshold" and "here is a commitment I was handed", and a prover can
//!     satisfy the comparison on a value of its choosing while presenting the honest,
//!     verifier-expected commitment for an unrelated value. (Lean proves the leg enforces its hash
//!     equation: `DescriptorIR2.lean::chip_lookup_sound`.)
//!
//! Accordingly the fact commitment is **not an argument to this builder — it is an OUTPUT.** A
//! caller supplies the fact's identity ([`FactBinding`]) and the value; the commitment is COMPUTED.
//! There is no signature through which "the value I compare" and "the commitment I present" can
//! disagree. The returned `pis[PI_FACT_COMMITMENT]` is byte-equal to the production out-of-circuit
//! binding ([`crate::dsl::predicates::arithmetic::compute_arithmetic_fact_commitment`] over
//! [`crate::poseidon2::hash_fact`]) — pinned by a KAT assert in this module's tests, so the
//! in-circuit chip image and the production binding are proven equal rather than assumed.

use crate::field::BabyBear;
use crate::poseidon2::hash_fact;

// --- Trace column layout (must match `PredicatesArithmeticEmit.lean` §1). ---
/// The private input value being compared (`arithmetic.rs` input slot 0). ALSO `terms[0]` of the
/// hashed fact — the column the weld's leg 1 feeds into `hash_fact`.
pub const INPUT: usize = 0;
/// The compiled expression-A result slot; for a bare-`Input` expression C3 forces `SLOT_A = INPUT`.
pub const SLOT_A: usize = 1;
/// The public comparison target (`arithmetic.rs` `threshold_col`), PI-bound to `PI_THRESHOLD`.
pub const THRESHOLD: usize = 2;
/// The comparison difference (`arithmetic.rs` `diff_col`); range-proved into `[0, 2^29)`.
pub const DIFF: usize = 3;
/// The fact commitment (`arithmetic.rs` `fact_commitment_col`), PI-bound to `PI_FACT_COMMITMENT`
/// AND forced by the weld's leg 2 to be `hash_4_to_1([FACT_HASH, STATE_ROOT, BLINDING, 0])`.
pub const FACT_COMMITMENT: usize = 4;
/// The predicate symbol entering `hash_fact` (the weld's leg-1 input 0).
pub const PREDICATE_SYM: usize = 5;
/// The hashed fact's second term.
pub const TERM1: usize = 6;
/// The hashed fact's third term.
pub const TERM2: usize = 7;
/// The token state root the fact commitment covers (the weld's leg-2 input 1).
pub const STATE_ROOT: usize = 8;
/// `hash_fact(PREDICATE_SYM, [INPUT, TERM1, TERM2])` — leg 1's digest, leg 2's input 0.
pub const FACT_HASH: usize = 9;
/// The seven out-lanes 1..7 of the arity-7 fact-hash chip lookup (filled by the prover).
pub const FACTHASH_LANES: std::ops::RangeInclusive<usize> = 10..=16;
/// The seven out-lanes 1..7 of the arity-4 fact-commitment chip lookup (filled by the prover).
pub const FACTCOMMIT_LANES: std::ops::RangeInclusive<usize> = 17..=23;
/// The commitment BLINDING factor — a PRIVATE witness column, the weld's leg-2 input 2.
/// See [`Blinding`] for why it costs the weld nothing.
pub const BLINDING: usize = 24;
/// Total base-trace width (the diff limbs are appended by the assembler, not counted here): the 5
/// predicate columns + 5 fact witness columns + 2×7 fact chip lanes + the blinding factor.
pub const PRED_WIDTH: usize = 25;

/// PI slot: the public threshold (`arithmetic.rs::PI_THRESHOLD`).
pub const PI_THRESHOLD: usize = 0;
/// PI slot: the public fact commitment (`arithmetic.rs::PI_FACT_COMMITMENT`).
pub const PI_FACT_COMMITMENT: usize = 1;
/// Public-input count.
pub const PRED_PI_COUNT: usize = 2;

/// The effective diff range width: the hand AIR's `NUM_BITS = 30` bits with the top bit forced to
/// zero leaves `diff ∈ [0, 2^29)` (`arithmetic.rs` @736); the emitted `range` table is 29 bits.
pub const DIFF_BITS: usize = 29;

/// `hash_fact`'s `state[5]` domain marker (`0xFACF`); the arity-7 chip absorb of
/// `[pred, value, term1, term2, 0, FACT_MARK, 1]` reproduces `hash_fact`
/// (`PredicatesArithmeticEmit.lean:108`; the chip-side KAT is `circuit-prove`'s
/// `fact_arith_arity7_chip_absorb_matches_hash_fact`).
pub const FACT_MARK: u32 = 0xFACF;

/// The dispatched AIR-name of this descriptor (the [`crate::descriptor_by_name`] key).
pub const PREDICATE_ARITH_NAME: &str = "dregg-predicate-arith-ge::threshold-v1";

/// **The per-presentation commitment BLINDING factor** — the privacy half of the weld.
///
/// A newtype rather than a bare `BabyBear` for two reasons: it cannot be swapped with a `term`/
/// `state_root` argument by position, and [`Blinding::NONE`] makes "I am deliberately not blinding
/// this" an explicit, greppable choice instead of an anonymous `BabyBear::ZERO`.
///
/// It is deliberately NOT a field of [`FactBinding`]. `FactBinding` is the fact's IDENTITY — what
/// the commitment covers, fixed by token state. The blinding factor is per-PRESENTATION randomness,
/// freshly drawn each time the SAME fact is presented; that is precisely what makes two
/// presentations unlinkable. Folding it into the identity type would conflate "which fact" with
/// "which showing of it".
///
/// ## Why this costs the weld nothing
///
/// The blinding factor is a private witness column the prover chooses freely. That freedom lets it
/// move the commitment anywhere in the image of `hash_4_to_1([fact_hash, state_root, ·, 0])` — but
/// leg 1 independently forces `fact_hash = hash_fact(pred, [INPUT, ..])` over the SAME `INPUT`
/// column the comparison bounds, so every commitment reachable by any choice of blinding still
/// opens to the value being compared. Blinding rerandomizes WHICH commitment names this fact; it
/// cannot change WHICH fact is named. Privacy and soundness are independent here, not traded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Blinding(pub BabyBear);

impl Blinding {
    /// The DEGENERATE, non-private blinding (`0`): the commitment becomes a deterministic function
    /// of the fact, so two presentations of it are CORRELATABLE. Sound — the weld holds exactly as
    /// it does under a random blinding — but not unlinkable. Use it only where linkability is
    /// intended (fixtures, KATs, a deliberately public fact).
    pub const NONE: Blinding = Blinding(BabyBear::ZERO);

    /// The underlying field element (the value written into the [`BLINDING`] column).
    pub fn as_field(self) -> BabyBear {
        self.0
    }
}

/// The identity of the fact whose value the predicate speaks about — everything the commitment
/// covers EXCEPT the value itself and the per-presentation [`Blinding`].
///
/// The value is deliberately NOT a field here: it is passed separately to
/// [`predicate_arith_witness`] and becomes `terms[0]` of the hashed fact, so a caller cannot pair a
/// commitment with a value the commitment does not cover. This type is the reason the forgery
/// (`prove value ≥ threshold against someone else's commitment`) is unrepresentable at the API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FactBinding {
    /// The predicate symbol (`hash_fact`'s first argument).
    pub predicate_sym: BabyBear,
    /// The fact's second term (`terms[1]`).
    pub term1: BabyBear,
    /// The fact's third term (`terms[2]`).
    pub term2: BabyBear,
    /// The token state root the fact commitment covers.
    pub state_root: BabyBear,
}

impl FactBinding {
    /// The genuine `hash_fact(predicate_sym, [value, term1, term2])` for `value` — the fact hash
    /// this binding commits to when the compared value is `value`. Byte-identical to the production
    /// bridge path (`bridge/src/present.rs` builds `terms` then calls
    /// [`crate::poseidon2::hash_fact`]).
    pub fn fact_hash_of(&self, value: BabyBear) -> BabyBear {
        hash_fact(self.predicate_sym, &[value, self.term1, self.term2])
    }

    /// The genuine BLINDED fact commitment for `value` under `blinding`:
    /// `hash_4_to_1([fact_hash_of(value), state_root, blinding, 0])`. This is what the descriptor's
    /// weld FORCES col 4 to equal.
    ///
    /// Note the shape of the verifier's side: under a random `blinding` the commitment is NOT
    /// re-derivable from token state alone (that is the point — an unlinkable commitment is not a
    /// deterministic function of the fact). Deriving-and-comparing is available only at
    /// [`Blinding::NONE`]. What the weld gives a verifier at any blinding is the binding itself:
    /// whatever commitment is presented, the compared value is the one it covers.
    pub fn commitment_of(&self, value: BabyBear, blinding: Blinding) -> BabyBear {
        crate::dsl::predicates::arithmetic::compute_arithmetic_fact_commitment(
            self.fact_hash_of(value),
            self.state_root,
            blinding.as_field(),
        )
    }
}

/// Build the 24-column arithmetic-threshold base trace + the 2-element public-input vector
/// `[threshold, fact_commitment]` for the emitted `dregg-predicate-arith-ge::threshold-v1`
/// descriptor.
///
/// `value` / `threshold` are the integers being compared (reduced into the field); `fact` is the
/// identity of the fact the predicate speaks about. **The fact commitment is COMPUTED from `value`
/// and `fact`, and returned as `pis[PI_FACT_COMMITMENT]`** — it is not an input, so the compared
/// value and the committed fact cannot be made to disagree through this API.
///
/// The single logical predicate row is repeated to `height` (a power of two ≥ 2 — the trace-height
/// requirement). Every row carries `INPUT = SLOT_A = value`, `THRESHOLD = threshold`,
/// `DIFF = value − threshold` (field), the fact witness columns, and both weld DIGESTS
/// (`FACT_HASH` = col 9, `FACT_COMMITMENT` = col 4). The 2×7 chip LANE columns (10..23) are left
/// zero for the prover's `fill_chip_lanes`, and the range-decomposition limbs are appended by
/// `prove_vm_descriptor2`'s assembler.
///
/// This builder does NOT pre-judge `value ≥ threshold`: it computes the field diff and the
/// descriptor's `⟨range, [DIFF]⟩` lookup is the judge. For an HONEST `≥` witness pass
/// `value ≥ threshold` with `value − threshold < 2^29` (then `DIFF ∈ [0, 2^29)` and the proof
/// verifies); a `value < threshold` wraps `DIFF` out of range and the descriptor rejects it.
pub fn predicate_arith_witness(
    value: u64,
    threshold: u64,
    fact: FactBinding,
    blinding: Blinding,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if height < 2 || !height.is_power_of_two() {
        return Err(format!(
            "predicate-arith trace height {height} must be a power of two ≥ 2 (the trace-height requirement)"
        ));
    }

    let value_f = BabyBear::from_u64(value);
    let threshold_f = BabyBear::from_u64(threshold);
    // DIFF = value − threshold in the field. For value ≥ threshold (small operands) this is the
    // genuine nonneg difference and lands in [0, 2^29); for value < threshold it wraps to
    // p − (threshold − value), which the descriptor's range lookup refuses. C3 (SLOT_A = INPUT) and
    // C5 (DIFF = SLOT_A − THRESHOLD) hold by construction on this row.
    let diff_f = value_f - threshold_f;

    // THE WELD, producer side: the two digest columns the chip lookups bind. Computed from `value`
    // — which is what makes the commitment a statement ABOUT the compared number.
    let fact_hash = fact.fact_hash_of(value_f);
    let fact_commitment = fact.commitment_of(value_f, blinding);

    let mut row = vec![BabyBear::ZERO; PRED_WIDTH];
    row[INPUT] = value_f;
    row[SLOT_A] = value_f;
    row[THRESHOLD] = threshold_f;
    row[DIFF] = diff_f;
    row[FACT_COMMITMENT] = fact_commitment;
    row[PREDICATE_SYM] = fact.predicate_sym;
    row[TERM1] = fact.term1;
    row[TERM2] = fact.term2;
    row[STATE_ROOT] = fact.state_root;
    row[FACT_HASH] = fact_hash;
    // THE BLINDING FACTOR REACHES THE PROOF. Leg 2 is an arity-4 chip lookup over
    // `[FACT_HASH, STATE_ROOT, BLINDING, 0]`: this column is a genuine input to the constrained
    // permutation, not decoration. Drop it (leave the column zero while computing a blinded
    // commitment) and the lookup's image no longer matches col 4 — the proof is REFUSED, not
    // silently unblinded. That is the canary in `blinding_reaches_the_proof`.
    row[BLINDING] = blinding.as_field();
    // Cols 10..=23 (the 2×7 chip out-lanes) stay zero: `prove_vm_descriptor2`'s
    // `trace_with_chip_lanes` fills them from the genuine permutation.

    let trace = vec![row; height];
    let pis = vec![threshold_f, fact_commitment];
    Ok((trace, pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, TID_P2, TID_RANGE, VmConstraint2,
        prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::refusal::{Outcome, classify};

    /// The scenario's fact identity, shared by the tests below.
    fn fact() -> FactBinding {
        FactBinding {
            predicate_sym: BabyBear::new(0x9E),
            term1: BabyBear::new(0x11),
            term2: BabyBear::new(0x22),
            state_root: BabyBear::new(0x57A7E),
        }
    }

    /// A REAL, non-zero per-presentation blinding — the DEFAULT these tests are driven under, so
    /// every tooth below is exercised in the deployed (blinded) posture rather than at the
    /// degenerate [`Blinding::NONE`]. Not a `const` because `BabyBear::new` is not a `const fn`.
    fn test_blinding() -> Blinding {
        Blinding(BabyBear::new(0xB11D1))
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails
    /// to verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
            // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
            // debug_assert), which used to land here and read as "rejected".
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// The dispatched descriptor decodes, carries the expected name, and has the LEAN-EMITTED shape:
    /// width 25 (the 24 welded columns + the BLINDING witness column), 2 PIs, one range lookup (C6) AND **both Poseidon2 weld legs**.
    ///
    /// The `poseidon2_lookups == 2` assert is the structural anti-fork gate. Its predecessor
    /// asserted `trace_width == 5` / `range_lookups == 1` with no chip check — which RATIFIED the
    /// absence of the weld, so restoring the Lean descriptor would have turned a green test red.
    /// A shape assert must pin the shape the SOURCE OF TRUTH emits, never the shape that happens to
    /// be on disk.
    #[test]
    fn predicate_arith_dispatches_with_expected_shape() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");
        assert_eq!(desc.name, PREDICATE_ARITH_NAME);
        assert_eq!(desc.trace_width, PRED_WIDTH);
        assert_eq!(
            desc.trace_width, 25,
            "PRED_WIDTH must be the Lean-emitted 25 (24 welded columns + the BLINDING column)"
        );
        assert_eq!(desc.public_input_count, PRED_PI_COUNT);
        // exactly one range lookup (C6) on the diff column.
        let range_lookups = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_RANGE))
            .count();
        assert_eq!(range_lookups, 1, "the single diff range lookup (C6)");
        // BOTH weld legs: hash_fact -> FACT_HASH, and hash_4_to_1([FACT_HASH, STATE_ROOT,
        // BLINDING, 0]) -> col 4.
        let poseidon2_lookups = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(
            poseidon2_lookups, 2,
            "the VALUE<->FACT WELD: leg 1 (fact hash) + leg 2 (fact commitment)"
        );
    }

    /// THE KAT: the commitment this builder computes for the in-circuit weld is byte-equal to the
    /// production out-of-circuit binding a verifier derives from token state. Without this, the
    /// circuit could be self-consistently welded to a hash nobody else computes.
    #[test]
    fn computed_commitment_matches_production_binding() {
        let f = fact();
        let value = BabyBear::from_u64(100);
        let (_, pis) = predicate_arith_witness(100, 40, f, test_blinding(), 4).expect("witness");

        let expected_fact_hash =
            crate::poseidon2::hash_fact(f.predicate_sym, &[value, f.term1, f.term2]);
        let expected = crate::dsl::predicates::arithmetic::compute_arithmetic_fact_commitment(
            expected_fact_hash,
            f.state_root,
            test_blinding().as_field(),
        );
        assert_eq!(
            pis[PI_FACT_COMMITMENT], expected,
            "the witness's computed fact commitment must equal the production binding"
        );
        assert_eq!(
            pis[PI_FACT_COMMITMENT],
            f.commitment_of(value, test_blinding())
        );
    }

    /// THE POSITIVE POLE: an honest `value ≥ threshold` witness proves through the DISPATCHED
    /// descriptor and re-verifies against the public `[threshold, fact_commitment]`.
    #[test]
    fn honest_ge_proves_and_verifies_via_dispatch() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let f = fact();

        for height in [2usize, 4, 8] {
            let (trace, pis) = predicate_arith_witness(100, 40, f, test_blinding(), height)
                .expect("witness builds");
            assert_eq!(trace.len(), height);
            assert_eq!(trace[0].len(), PRED_WIDTH);
            assert_eq!(pis[PI_THRESHOLD], BabyBear::new(40));
            assert_eq!(
                pis[PI_FACT_COMMITMENT],
                f.commitment_of(BabyBear::from_u64(100), test_blinding()),
                "the computed fact commitment is the pinned public input (C2)"
            );

            let proof =
                prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
                    .unwrap_or_else(|e| panic!("honest height-{height} witness must prove: {e}"));
            verify_vm_descriptor2(&desc, &proof, &pis)
                .unwrap_or_else(|e| panic!("honest height-{height} proof must verify: {e}"));
        }
    }

    /// THE LOAD-BEARING C6 TOOTH: a `value < threshold` witness (diff wraps out of `[0, 2^29)`) is
    /// REFUSED by the range lookup, and the refusal is provably the RANGE mechanism (the error names
    /// the range wire / the `2^bits` bound). Non-vacuous: the honest `value ≥ threshold` accepts.
    #[test]
    fn value_below_threshold_refuses_on_range() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let f = fact();

        // non-vacuity: value 100 ≥ threshold 40 is ACCEPTED.
        let (ok_trace, ok_pis) =
            predicate_arith_witness(100, 40, f, test_blinding(), 4).expect("witness");
        assert!(
            !rejects(&desc, &ok_trace, &ok_pis),
            "honest value ≥ threshold must be accepted — else the canary is vacuous"
        );

        // value 30 < threshold 40 ⇒ diff = p − 10, out of [0, 2^29). C3 and C5 still hold; ONLY C6 fails.
        let (bad_trace, bad_pis) =
            predicate_arith_witness(30, 40, f, test_blinding(), 4).expect("witness");
        let err = match prove_vm_descriptor2(
            &desc,
            &bad_trace,
            &bad_pis,
            &MemBoundaryWitness::default(),
            &[],
        ) {
            Ok(_) => panic!("value < threshold must be REFUSED (diff out of range, C6 tooth)"),
            Err(e) => e,
        };
        assert!(
            err.contains("range") || err.contains("2^"),
            "the refusal must be the RANGE mechanism (diff ∉ [0, 2^29)), got: {err}"
        );
        assert!(rejects(&desc, &bad_trace, &bad_pis));
    }

    /// C5 diff gate: a TAMPERED, in-range but inconsistent `diff` (59 where `value − threshold = 60`)
    /// passes the range proof and C3 but violates C5 → REJECTED. Non-vacuous: the honest trace accepts.
    #[test]
    fn tampered_diff_refuses_on_c5() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let (mut trace, pis) =
            predicate_arith_witness(100, 40, fact(), test_blinding(), 4).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepts (non-vacuity)"
        );
        for row in &mut trace {
            row[DIFF] = BabyBear::new(59); // should be 60; still in range but breaks C5
        }
        assert!(
            rejects(&desc, &trace, &pis),
            "an in-range diff that violates diff = value − threshold must be REJECTED (C5 gate)"
        );
    }

    /// C3 slot identity: a TAMPERED `slot_a ≠ input` (with `diff` re-consistent so C5 and the range
    /// proof still hold) violates only C3 → REJECTED.
    #[test]
    fn tampered_slot_refuses_on_c3() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let (mut trace, pis) =
            predicate_arith_witness(100, 40, fact(), test_blinding(), 4).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepts (non-vacuity)"
        );
        for row in &mut trace {
            row[SLOT_A] = BabyBear::new(101); // ≠ input 100 → C3 broken
            row[DIFF] = BabyBear::new(101 - 40); // keep C5 satisfied (61 ∈ range), isolate C3
        }
        assert!(
            rejects(&desc, &trace, &pis),
            "slot_a ≠ input must be REJECTED (C3 slot-identity gate)"
        );
    }

    /// C1 threshold PI binding: honest trace, forged public `threshold` (41 ≠ the witness 40) →
    /// REJECTED at verify. Non-vacuous: the correct threshold PI accepts.
    #[test]
    fn forged_threshold_pi_refuses_on_c1() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let (trace, pis) =
            predicate_arith_witness(100, 40, fact(), test_blinding(), 4).expect("witness");
        assert!(!rejects(&desc, &trace, &pis));
        let forged = vec![BabyBear::new(41), pis[PI_FACT_COMMITMENT]];
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged public threshold must be REJECTED (C1 PI binding)"
        );
    }

    /// C2 fact-commitment PI binding: honest trace, forged public `fact_commitment` → REJECTED.
    #[test]
    fn forged_fact_pi_refuses_on_c2() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let (trace, pis) =
            predicate_arith_witness(100, 40, fact(), test_blinding(), 4).expect("witness");
        assert!(!rejects(&desc, &trace, &pis));
        let forged = vec![BabyBear::new(40), BabyBear::new(99999)];
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged public fact_commitment must be REJECTED (C2 PI binding)"
        );
    }

    /// AUDIT (independent forge): tamper the TRACE-side `FACT_COMMITMENT` column (honest PI kept) →
    /// the first-row `pi_binding` (col4 ↔ PI[1]) no longer holds → REJECTED. Distinct from
    /// `forged_fact_pi_refuses_on_c2` (which tampers the PI side); this probes the trace side.
    #[test]
    fn audit_tampered_trace_fact_refuses() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let (mut trace, pis) =
            predicate_arith_witness(100, 40, fact(), test_blinding(), 4).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepts (non-vacuity)"
        );
        for row in &mut trace {
            row[FACT_COMMITMENT] = BabyBear::new(0xDEAD); // trace col4 ≠ honest PI[1]
        }
        assert!(
            rejects(&desc, &trace, &pis),
            "a tampered trace fact_commitment (≠ honest PI) must be REJECTED (C1 first-row binding)"
        );
    }

    /// THE WELD, leg 1: a tampered `FACT_HASH` (col 9) that is not `hash_fact(pred, [input, ..])`
    /// breaks the arity-7 chip lookup → REJECTED. Non-vacuous: the honest trace accepts.
    ///
    /// The tamper is propagated to col 4 (so leg 2 stays self-consistent) and to the PI, isolating
    /// leg 1 as the only violated relation.
    #[test]
    fn tampered_fact_hash_refuses_on_weld_leg1() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let f = fact();
        let (mut trace, pis) =
            predicate_arith_witness(100, 40, f, test_blinding(), 4).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepts (non-vacuity)"
        );

        let forged_hash = BabyBear::new(0xBADF00D);
        let forged_commit = crate::dsl::predicates::arithmetic::compute_arithmetic_fact_commitment(
            forged_hash,
            f.state_root,
            test_blinding().as_field(),
        );
        for row in &mut trace {
            row[FACT_HASH] = forged_hash;
            row[FACT_COMMITMENT] = forged_commit;
        }
        let forged_pis = vec![pis[PI_THRESHOLD], forged_commit];
        assert!(
            rejects(&desc, &trace, &forged_pis),
            "a FACT_HASH that is not hash_fact(PREDICATE_SYM, [INPUT, TERM1, TERM2]) must be \
             REJECTED (weld leg 1)"
        );
    }

    /// THE BLINDING CANARY (named by this module's header): the [`BLINDING`] column is a genuine
    /// constrained input to leg 2's arity-4 chip lookup, not decoration.
    ///
    /// Zero the column while leaving the blinded commitment (and its PI) honest — the shape a
    /// "the blinding never reaches the circuit" bug would produce. Leg 2's image becomes
    /// `hash_4_to_1([FACT_HASH, STATE_ROOT, 0, 0])`, which is not col 4, so the lookup names a chip
    /// row no genuine permutation serves → REFUSED. The proof is never silently unblinded.
    ///
    /// Non-vacuous in both directions: the untampered blinded witness ACCEPTS, and a
    /// [`Blinding::NONE`] witness (zero column AND the matching zero-blinded commitment) also
    /// ACCEPTS — so the refusal is the column/commitment DISAGREEMENT, not "a zero column".
    #[test]
    fn blinding_reaches_the_proof() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let f = fact();

        // Pole 1 (non-vacuity): the honest BLINDED witness proves and verifies.
        let (trace, pis) =
            predicate_arith_witness(100, 40, f, test_blinding(), 4).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "the honest blinded witness must be ACCEPTED — else this canary proves nothing"
        );

        // Pole 2 (non-vacuity): the DEGENERATE blinding is sound too — a zero BLINDING column is
        // fine when the commitment is the zero-blinded one. So a zero column is not itself the
        // refusal.
        let (none_trace, none_pis) =
            predicate_arith_witness(100, 40, f, Blinding::NONE, 4).expect("witness");
        assert!(
            !rejects(&desc, &none_trace, &none_pis),
            "a Blinding::NONE witness must be ACCEPTED (sound, merely correlatable)"
        );
        assert_ne!(
            pis[PI_FACT_COMMITMENT], none_pis[PI_FACT_COMMITMENT],
            "a non-zero blinding must move the commitment — else it is not blinding anything"
        );

        // THE TAMPER: drop the blinding from the trace, keep the blinded commitment + PI.
        let mut dropped = trace.clone();
        for row in &mut dropped {
            row[BLINDING] = BabyBear::ZERO;
        }
        assert!(
            rejects(&desc, &dropped, &pis),
            "a BLINDING column that disagrees with the commitment it blinded must be REJECTED — \
             the blinding is a constrained input to weld leg 2, not decoration"
        );
    }

    /// UNLINKABILITY, producer side: the SAME fact and the SAME value presented under two different
    /// blindings carry DIFFERENT public fact commitments, so colluding verifiers holding both
    /// presentations cannot correlate them on the commitment. (The weld is unaffected — see
    /// [`Blinding`] — which `blinding_reaches_the_proof` exercises.)
    #[test]
    fn distinct_blindings_rerandomize_the_commitment() {
        let f = fact();
        let (_, pis_a) = predicate_arith_witness(100, 40, f, test_blinding(), 4).expect("witness");
        let (_, pis_b) = predicate_arith_witness(100, 40, f, Blinding(BabyBear::new(0x5EED)), 4)
            .expect("witness");
        assert_eq!(
            pis_a[PI_THRESHOLD], pis_b[PI_THRESHOLD],
            "the same public threshold — only the commitment rerandomizes"
        );
        assert_ne!(
            pis_a[PI_FACT_COMMITMENT], pis_b[PI_FACT_COMMITMENT],
            "two presentations of the SAME fact under different blindings must be UNLINKABLE"
        );
    }

    /// Malformed heights (non-power-of-two, < 2) are refused at build time.
    #[test]
    fn malformed_witness_refuses() {
        assert!(predicate_arith_witness(100, 40, fact(), test_blinding(), 3).is_err()); // not a power of two
        assert!(predicate_arith_witness(100, 40, fact(), test_blinding(), 1).is_err()); // < 2
        assert!(predicate_arith_witness(100, 40, fact(), test_blinding(), 0).is_err());
    }
}
