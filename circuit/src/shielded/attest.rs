//! M2-d: **ZK attestations over hidden cell state** — the privacy jewel.
//!
//! A private programmable cell publishes a single **commitment**
//! `C = hash_fact(attr, [salt, 0, 0, 0])` over a HIDDEN attribute felt `attr`
//! (its age, its balance, its membership tag, …) blinded by a hidden `salt`. The
//! cell can then issue a **verifiable ZK attestation** that a PREDICATE holds of
//! that hidden attribute — `attr >= 18`, `attr > 0`, `attr ∈ S`, `attr == v` —
//! and a third party verifies the attestation against the *published* `C`,
//! learning ONLY the predicate's truth and NOTHING about `attr` (or `salt`).
//!
//! This is M2-c's general shielded transition specialized to a *read-only
//! predicate over committed cell state*: instead of moving value, the cell
//! proves a fact about its own hidden field. It reuses the M2 machinery exactly:
//! the sorted-Poseidon2 `hash_fact` commitment (same primitive the commitment
//! tree and `shielded_spend` leaf use), and the **hiding** uni-STARK path
//! ([`crate::dsl::dsl_p3_air::prove_dsl_zk`], `HidingFriPcs`), so the openings
//! reveal nothing about the witness beyond the public `(commitment, predicate
//! parameters)`.
//!
//! # The two soundness obligations the circuit binds in-witness
//!
//! 1. **Opening.** `C == hash_fact(attr, [salt,0,0,0])`, with `attr` and `salt`
//!    HIDDEN and `C` a public input. Without this the prover could attest a
//!    predicate over a value that is not the one the cell published — the
//!    attestation would be about *nothing*.
//! 2. **Predicate.** The chosen predicate holds of `attr`, encoded as DSL
//!    constraints the audited `DslP3Air` supports (`Binary`, `Polynomial`,
//!    `Gated`, `AtLeastOne`) — **zero hand-written AIR**.
//!
//! The verifier accepts iff BOTH hold. A cell WITHOUT the attribute cannot forge
//! an accepting attestation: either it cannot open `C` to a satisfying `attr`
//! (commitment binding) or, if it opens `C` to the real `attr`, the predicate
//! constraint is violated and the self-verifying prover refuses to emit a proof.
//!
//! # The non-negativity subtlety (why threshold predicates bit-decompose)
//!
//! BabyBear is a prime field: `attr - threshold >= 0` is meaningless mod `p`
//! (every element has a "negative" representative). A threshold predicate
//! `attr >= threshold` is therefore proven by witnessing `diff = attr -
//! threshold` and a **bit decomposition** `diff = Σ bit_i · 2^i` over
//! `RANGE_BITS` binary columns: each `bit_i` is `Binary`-constrained, and a
//! `Polynomial` constraint pins `Σ bit_i·2^i - diff == 0` (in the field).
//!
//! For this gadget to BITE, `RANGE_BITS` must be strictly less than the field's
//! bit width. BabyBear's modulus `p = 2^31 - 2^27 + 1 ≈ 2^31` has a 31-bit
//! canonical representation, so **every** canonical felt already fits in 31
//! bits — a 31-or-32-bit decomposition exists for *every* element, including the
//! field rep of a "negative" diff, and the gadget would be VACUOUS (the
//! reconstruction `Σ bit_i·2^i ≡ diff (mod p)` holds for all diffs). The bound
//! must instead carve out a window `[0, 2^RANGE_BITS)` that the negative reps
//! cannot reach. A "negative" `diff` (i.e. `attr < threshold`) has field rep
//! `p - (threshold - attr)`, whose smallest possible magnitude is `p - 1 ≈
//! 2^31`. With `RANGE_BITS = 30` the honest range `[0, 2^30)` lies strictly
//! below every negative rep (`2^30 < p - 1`), so a negative diff has no valid
//! `RANGE_BITS`-bit decomposition and the constraint bites. Honest attributes
//! and thresholds (ages, balances, counters, timestamps) sit far under `2^30 ≈
//! 1.07e9`. This is the standard small-field range-proof gadget, authored as DSL
//! data.
//!
//! # No Rust-authored AIR (standing law)
//!
//! Every constraint here is a `ConstraintExpr` the audited `DslP3Air` symbolic
//! arithmetization already supports; this module emits descriptors (data) and
//! assembles witnesses. It writes no AIR.
//!
//! # Worked examples (see the tests + `mod.rs` re-exports)
//!
//! - **prove-over-18**: a cell committing `attr = 21` issues a `Threshold{18}`
//!   attestation that verifies against `C`; a cell committing `attr = 16`
//!   cannot (the `diff = -2` decomposition fails). Neither discloses the age.
//! - **prove-solvent**: a cell committing `attr = balance` issues a `Positive`
//!   attestation (`balance >= 1`) that verifies; a zero-balance cell cannot.

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2::hash_fact;

/// Number of bits a threshold-predicate `diff = attr - threshold` is range-proven
/// to lie within: `diff ∈ [0, 2^RANGE_BITS)`. **Must be < 31** so the honest
/// window lies strictly below BabyBear's negative reps: a "negative" diff (i.e.
/// `attr < threshold`) has field rep `p - (threshold - attr)`, whose smallest
/// magnitude is `p - 1 ≈ 2^31`; with `RANGE_BITS = 30` (`2^30 < p - 1`) no
/// negative diff has a 30-bit decomposition, so the gadget BITES. A value `>= 31`
/// would make EVERY canonical felt representable (every elt fits in 31 bits) and
/// the range check VACUOUS — see the module docs' non-negativity subtlety.
///
/// 30 bits covers honest ages, balances, counters, and timestamps (`< 2^30 ≈
/// 1.07e9`). The attested attribute and threshold are expected to be honest
/// fields whose difference stays in `[0, 2^30)`.
pub const RANGE_BITS: usize = 30;

/// The predicate an attestation proves of the hidden committed attribute `attr`.
///
/// Each variant is a *family*; the concrete bound/set/value is carried as a
/// parameter that becomes a PUBLIC input of the attestation (the verifier and
/// prover agree on WHICH predicate; only `attr` itself stays hidden).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Predicate {
    /// `attr >= threshold` (e.g. age ≥ 18). Range-proven via `diff = attr -
    /// threshold` bit decomposition.
    Threshold { threshold: u64 },
    /// `attr >= 1` (e.g. balance > 0 = solvent). The `Threshold{1}` specialization
    /// with its own name because "prove-solvent" is the canonical use.
    Positive,
    /// `attr ∈ {members...}` (e.g. member-of-allowlist). Proven by an
    /// `AtLeastOne` over per-member equality selectors, each gating `attr - m_i`.
    Membership { members: Vec<u64> },
    /// `attr == value` (e.g. field equals a publicly committed value). The
    /// disclosed-equality attestation: the value is public, `attr` is bound to it
    /// AND to the commitment, so the verifier learns `C` opens to exactly `value`.
    Equality { value: u64 },
}

impl Predicate {
    /// The threshold as a felt, for `Threshold`/`Positive`.
    fn threshold_felt(&self) -> Option<BabyBear> {
        match self {
            Predicate::Threshold { threshold } => Some(felt(*threshold)),
            Predicate::Positive => Some(BabyBear::ONE),
            _ => None,
        }
    }
}

fn felt(v: u64) -> BabyBear {
    BabyBear::new((v % (BABYBEAR_P as u64)) as u32)
}

// ============================================================================
// Trace layout
// ============================================================================
//
// The attestation is a SINGLE-row statement (a predicate over one committed
// value — no transition chain). We still emit a 2-row trace (a power of two,
// the minimum p3 trace height) by duplicating the witness row; every constraint
// is row-local and holds identically on both, and the boundary pins row 0.

/// Fixed columns shared by every predicate (indices 0..BASE_WIDTH).
pub mod col {
    /// The HIDDEN attribute felt (age / balance / tag / value). Bound by the
    /// commitment opening; the predicate constrains it.
    pub const ATTR: usize = 0;
    /// The HIDDEN commitment blinding salt.
    pub const SALT: usize = 1;
    /// The commitment `C = hash_fact(attr, [salt,0,0,0])`, pinned to PI[COMMITMENT].
    pub const COMMITMENT: usize = 2;
    /// Constant-zero padding felts so the opening hash absorbs exactly
    /// `[salt, 0, 0, 0]` (the 4 `hash_fact` terms). Pinned to 0 by Polynomial.
    pub const PAD0: usize = 3;
    pub const PAD1: usize = 4;
    pub const PAD2: usize = 5;
    /// First predicate-specific column.
    pub const PRED_BASE: usize = 6;
}

/// Width of the fixed (predicate-independent) prefix.
pub const BASE_WIDTH: usize = col::PRED_BASE;

/// Public-input layout. PI[0] is always the commitment; the predicate parameter
/// (threshold / claimed value) follows when the predicate has a scalar param.
pub mod pi {
    /// The published cell-state commitment the attestation is verified against.
    pub const COMMITMENT: usize = 0;
    /// The predicate's scalar parameter (threshold for `Threshold`, value for
    /// `Equality`). Absent (count 1) for `Positive`/`Membership`.
    pub const PARAM: usize = 1;
}

// ============================================================================
// Descriptor
// ============================================================================

/// Build the attestation circuit descriptor for `predicate`.
///
/// Common constraints (every predicate):
/// - **OPEN**: `commitment == hash_fact(attr, [salt, pad0, pad1, pad2])`
///   (a `Hash` constraint over `[attr, salt, pad0, pad1, pad2]`), with `pad*`
///   pinned to 0 by `Polynomial` so the absorbed terms are exactly `[salt,0,0,0]`.
/// - boundary **COMMITMENT**: row-0 `commitment == pi[COMMITMENT]`.
///
/// Predicate-specific constraints are appended over `PRED_BASE..` columns; see
/// each predicate arm.
pub fn attest_descriptor(predicate: &Predicate) -> CircuitDescriptor {
    let p = BABYBEAR_P;
    let mut constraints = Vec::new();
    let mut columns = vec![
        ColumnDef { name: "attr".into(), index: col::ATTR, kind: ColumnKind::Value },
        ColumnDef { name: "salt".into(), index: col::SALT, kind: ColumnKind::Value },
        ColumnDef { name: "commitment".into(), index: col::COMMITMENT, kind: ColumnKind::Hash },
        ColumnDef { name: "pad0".into(), index: col::PAD0, kind: ColumnKind::Value },
        ColumnDef { name: "pad1".into(), index: col::PAD1, kind: ColumnKind::Value },
        ColumnDef { name: "pad2".into(), index: col::PAD2, kind: ColumnKind::Value },
    ];

    // OPEN: commitment == hash_fact(attr, [salt, pad0, pad1, pad2]).
    constraints.push(ConstraintExpr::Hash {
        output_col: col::COMMITMENT,
        input_cols: vec![col::ATTR, col::SALT, col::PAD0, col::PAD1, col::PAD2],
    });
    // The three pad terms are constant-zero (so the absorbed terms are [salt,0,0,0]).
    for pad in [col::PAD0, col::PAD1, col::PAD2] {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm { coeff: BabyBear::ONE, col_indices: vec![pad] }],
        });
    }

    let mut public_input_count = 1; // PI[COMMITMENT] always present.

    match predicate {
        Predicate::Threshold { .. } | Predicate::Positive => {
            // diff = attr - threshold, range-proven in [0, 2^RANGE_BITS).
            // Columns: DIFF, then RANGE_BITS bit columns.
            let diff_col = col::PRED_BASE;
            let bit0 = diff_col + 1;
            columns.push(ColumnDef {
                name: "diff".into(),
                index: diff_col,
                kind: ColumnKind::Value,
            });
            for i in 0..RANGE_BITS {
                columns.push(ColumnDef {
                    name: format!("bit{i}"),
                    index: bit0 + i,
                    kind: ColumnKind::Binary,
                });
                constraints.push(ConstraintExpr::Binary { col: bit0 + i });
            }

            // DIFF binding: `attr - diff == threshold`. For `Positive` the
            // threshold is the constant 1 (no PI); for `Threshold` it is PI[PARAM].
            match predicate {
                Predicate::Positive => {
                    // attr - diff - 1 == 0
                    constraints.push(ConstraintExpr::Polynomial {
                        terms: vec![
                            PolyTerm { coeff: BabyBear::ONE, col_indices: vec![col::ATTR] },
                            PolyTerm { coeff: BabyBear::new(p - 1), col_indices: vec![diff_col] },
                            PolyTerm { coeff: BabyBear::new(p - 1), col_indices: vec![] },
                        ],
                    });
                }
                Predicate::Threshold { .. } => {
                    public_input_count = 2; // PI[PARAM] = threshold.
                    // attr - diff == pi[PARAM]  →  enforced as boundary PiBinding on
                    // an auxiliary "attr_minus_diff" is heavier; instead bind via a
                    // Polynomial that equals (attr - diff) and a PiBinding boundary
                    // on a dedicated column. Simpler: introduce THRESHOLD column,
                    // pin it to PI[PARAM] (boundary), and constrain attr-diff-thr==0.
                    let thr_col = bit0 + RANGE_BITS;
                    columns.push(ColumnDef {
                        name: "threshold".into(),
                        index: thr_col,
                        kind: ColumnKind::Value,
                    });
                    constraints.push(ConstraintExpr::Polynomial {
                        terms: vec![
                            PolyTerm { coeff: BabyBear::ONE, col_indices: vec![col::ATTR] },
                            PolyTerm { coeff: BabyBear::new(p - 1), col_indices: vec![diff_col] },
                            PolyTerm { coeff: BabyBear::new(p - 1), col_indices: vec![thr_col] },
                        ],
                    });
                }
                _ => unreachable!(),
            }

            // RANGE reconstruction: Σ bit_i·2^i - diff == 0.
            let mut terms = Vec::with_capacity(RANGE_BITS + 1);
            let mut pow = BabyBear::ONE;
            let two = BabyBear::new(2);
            for i in 0..RANGE_BITS {
                terms.push(PolyTerm { coeff: pow, col_indices: vec![bit0 + i] });
                pow = pow * two;
            }
            terms.push(PolyTerm { coeff: BabyBear::new(p - 1), col_indices: vec![diff_col] });
            constraints.push(ConstraintExpr::Polynomial { terms });
        }

        Predicate::Membership { members } => {
            // One equality-selector flag per member; flag_i gates (attr - m_i),
            // and AtLeastOne(flags) forces some flag set → attr equals some member.
            // Each member is a FIXED constant baked into the descriptor (the set is
            // public; only `attr` is hidden).
            let flag0 = col::PRED_BASE;
            let mut flag_cols = Vec::with_capacity(members.len());
            for (i, &m) in members.iter().enumerate() {
                let flag = flag0 + i;
                flag_cols.push(flag);
                columns.push(ColumnDef {
                    name: format!("sel{i}"),
                    index: flag,
                    kind: ColumnKind::Binary,
                });
                // flag_i is binary.
                constraints.push(ConstraintExpr::Binary { col: flag });
                // flag_i * (attr - m_i) == 0: if the flag is set, attr == m_i.
                constraints.push(ConstraintExpr::Gated {
                    selector_col: flag,
                    inner: Box::new(ConstraintExpr::Polynomial {
                        terms: vec![
                            PolyTerm { coeff: BabyBear::ONE, col_indices: vec![col::ATTR] },
                            PolyTerm { coeff: BabyBear::new(p - (felt(m).as_u32() % p)), col_indices: vec![] },
                        ],
                    }),
                });
            }
            // At least one selector is set (so attr equals at least one member).
            constraints.push(ConstraintExpr::AtLeastOne { flag_cols });
        }

        Predicate::Equality { .. } => {
            public_input_count = 2; // PI[PARAM] = claimed value.
            // A dedicated VALUE column pinned to PI[PARAM] (boundary), with
            // attr - value == 0 binding `attr` to the publicly disclosed value.
            let val_col = col::PRED_BASE;
            columns.push(ColumnDef {
                name: "value".into(),
                index: val_col,
                kind: ColumnKind::Value,
            });
            constraints.push(ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm { coeff: BabyBear::ONE, col_indices: vec![col::ATTR] },
                    PolyTerm { coeff: BabyBear::new(p - 1), col_indices: vec![val_col] },
                ],
            });
        }
    }

    let trace_width = columns.len();

    let mut boundaries = vec![BoundaryDef::PiBinding {
        row: BoundaryRow::First,
        col: col::COMMITMENT,
        pi_index: pi::COMMITMENT,
    }];
    // Pin the predicate's scalar-param column to PI[PARAM] for Threshold/Equality.
    match predicate {
        Predicate::Threshold { .. } => {
            let thr_col = col::PRED_BASE + 1 + RANGE_BITS;
            boundaries.push(BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: thr_col,
                pi_index: pi::PARAM,
            });
        }
        Predicate::Equality { .. } => {
            boundaries.push(BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: col::PRED_BASE,
                pi_index: pi::PARAM,
            });
        }
        _ => {}
    }

    CircuitDescriptor {
        name: format!("dregg-zk-attestation-v1-{}", predicate_tag(predicate)),
        trace_width,
        max_degree: 4,
        columns,
        constraints,
        boundaries,
        public_input_count,
        lookup_tables: vec![],
    }
}

fn predicate_tag(p: &Predicate) -> &'static str {
    match p {
        Predicate::Threshold { .. } => "threshold",
        Predicate::Positive => "positive",
        Predicate::Membership { .. } => "membership",
        Predicate::Equality { .. } => "equality",
    }
}

/// The attestation DSL circuit for `predicate`.
pub fn attest_circuit(predicate: &Predicate) -> DslCircuit {
    DslCircuit::new(attest_descriptor(predicate))
}

// ============================================================================
// Witness + trace
// ============================================================================

/// A hidden witness for an attestation: the committed attribute and its salt.
/// The predicate parameters live in the [`Predicate`] (public); only these are
/// hidden.
#[derive(Clone, Debug)]
pub struct AttestWitness {
    /// The hidden committed attribute felt (age / balance / tag / value).
    pub attr: BabyBear,
    /// The hidden commitment blinding salt.
    pub salt: BabyBear,
}

impl AttestWitness {
    /// The published commitment this attestation is verified against:
    /// `hash_fact(attr, [salt, 0, 0, 0])`.
    pub fn commitment(&self) -> BabyBear {
        hash_fact(self.attr, &[self.salt, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO])
    }
}

/// Generate the attestation trace + public inputs for `(witness, predicate)`.
///
/// Returns `(trace, public_inputs)`. The trace is 2 rows (the minimal p3
/// power-of-two height); both rows carry the identical witness assignment and
/// every constraint is row-local, so the duplication is sound and the boundary
/// pins row 0. `public_inputs` is `[commitment]` for `Positive`/`Membership`,
/// `[commitment, threshold]` for `Threshold`, `[commitment, value]` for
/// `Equality`.
pub fn generate_attest_trace(
    witness: &AttestWitness,
    predicate: &Predicate,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let descriptor = attest_descriptor(predicate);
    let width = descriptor.trace_width;
    let commitment = witness.commitment();

    let mut row = vec![BabyBear::ZERO; width];
    row[col::ATTR] = witness.attr;
    row[col::SALT] = witness.salt;
    row[col::COMMITMENT] = commitment;
    // pads already zero.

    let mut public_inputs = vec![commitment];

    match predicate {
        Predicate::Threshold { .. } | Predicate::Positive => {
            let threshold = predicate.threshold_felt().unwrap();
            let diff_col = col::PRED_BASE;
            let bit0 = diff_col + 1;
            // diff = attr - threshold (field subtraction; honest attr >= threshold
            // gives a small non-negative diff with a clean bit decomposition).
            let diff = witness.attr - threshold;
            row[diff_col] = diff;
            // Bit-decompose diff's canonical u32 representative.
            let diff_u = diff.as_u32();
            for i in 0..RANGE_BITS {
                let bit = (diff_u >> i) & 1;
                row[bit0 + i] = BabyBear::new(bit);
            }
            if let Predicate::Threshold { threshold: t } = predicate {
                let thr_col = bit0 + RANGE_BITS;
                row[thr_col] = threshold;
                public_inputs.push(felt(*t));
            }
        }
        Predicate::Membership { members } => {
            let flag0 = col::PRED_BASE;
            // Set the flag for the FIRST member equal to attr (if any).
            for (i, &m) in members.iter().enumerate() {
                if witness.attr == felt(m) {
                    row[flag0 + i] = BabyBear::ONE;
                    break;
                }
            }
        }
        Predicate::Equality { value } => {
            let val_col = col::PRED_BASE;
            row[val_col] = felt(*value);
            public_inputs.push(felt(*value));
        }
    }

    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dsl::dsl_p3_air::{DslP3Air, prove_dsl_zk, verify_dsl_zk};

    /// Treat both "prover returns Err" and "debug constraint check panics" as
    /// rejection — the soundness property is "no verifying proof is produced".
    fn proving_rejects(circuit: &DslCircuit, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_dsl_zk(circuit, trace, pis)
        }));
        match r {
            Err(_) => true,
            Ok(Err(_)) => true,
            Ok(Ok(_)) => false,
        }
    }

    /// Every predicate's descriptor must route through the audited `DslP3Air`
    /// symbolic arithmetization (no unsupported constraint form).
    #[test]
    fn all_predicates_p3_clean() {
        for pred in [
            Predicate::Threshold { threshold: 18 },
            Predicate::Positive,
            Predicate::Membership { members: vec![3, 7, 11] },
            Predicate::Equality { value: 42 },
        ] {
            let dsl = attest_circuit(&pred);
            DslP3Air::try_from_dsl(&dsl)
                .unwrap_or_else(|e| panic!("{pred:?} must be DslP3Air-clean: {e:?}"));
        }
    }

    /// PROVE-OVER-18: a cell committing age = 21 issues an accepting `Threshold{18}`
    /// attestation against its published commitment, disclosing nothing but "≥ 18".
    /// A cell committing age = 16 CANNOT forge one (the diff = -2 fails the range).
    #[test]
    fn prove_over_18_worked_example() {
        let pred = Predicate::Threshold { threshold: 18 };
        let circuit = attest_circuit(&pred);

        // TRUE: age 21 ≥ 18. The attestation verifies against the commitment and
        // the public inputs are only [commitment, 18] — the age 21 stays hidden.
        let w = AttestWitness { attr: BabyBear::new(21), salt: BabyBear::new(0x5EED) };
        let (trace, pis) = generate_attest_trace(&w, &pred);
        assert_eq!(pis[pi::COMMITMENT], w.commitment());
        assert_eq!(pis[pi::PARAM], BabyBear::new(18));
        let proof = prove_dsl_zk(&circuit, &trace, &pis)
            .expect("age 21 ≥ 18 must produce an accepting attestation");
        verify_dsl_zk(&circuit, &proof, &pis).expect("the over-18 attestation must verify");

        // FALSE: age 16 < 18. The honest trace generator produces diff = -2 (field
        // rep ≈ p-2, a ~31-bit number) whose RANGE_BITS(=30)-bit decomposition
        // reconstructs (p-2) mod 2^30 ≠ p-2 → the range constraint bites; no
        // verifying proof exists. (The diff column itself is pinned to attr-threshold
        // by the linking constraint, and attr is pinned by the opening, so the prover
        // cannot substitute a small fake diff.)
        let under = AttestWitness { attr: BabyBear::new(16), salt: BabyBear::new(0x1234) };
        let (bad_trace, bad_pis) = generate_attest_trace(&under, &pred);
        assert!(
            proving_rejects(&circuit, &bad_trace, &bad_pis),
            "a cell aged 16 must NOT be able to forge an over-18 attestation"
        );
    }

    /// RANGE GADGET NON-VACUITY (the soundness regression guard). The threshold
    /// range proof is only meaningful if `RANGE_BITS` carves a window BELOW the
    /// field's negative reps. This pins the invariant two ways:
    ///
    /// 1. `RANGE_BITS < 31`: every BabyBear felt fits in 31 bits, so a 31-bit (or
    ///    wider) window would make EVERY diff decomposable and the check vacuous.
    /// 2. Boundary adversary: a cell exactly ONE below the threshold (`diff = -1`,
    ///    field rep `p - 1 ≈ 2^31`, the smallest-magnitude negative rep) must be
    ///    rejected — if even this just-barely-negative diff were representable, the
    ///    gadget would pass everyone.
    #[test]
    fn threshold_range_gadget_is_not_vacuous() {
        // (1) The structural invariant: the window must lie below the field width.
        assert!(
            RANGE_BITS < 31,
            "RANGE_BITS={RANGE_BITS} >= 31 makes the threshold range proof VACUOUS \
             (every BabyBear felt fits in 31 bits → every diff decomposes)"
        );
        // 2^RANGE_BITS must be strictly below the smallest negative rep (p-1).
        assert!(
            (1u64 << RANGE_BITS) < (BABYBEAR_P as u64) - 1,
            "the honest window [0,2^{RANGE_BITS}) must lie strictly below p-1"
        );

        // (2) The boundary adversary: attr = threshold - 1 (the tightest miss).
        let pred = Predicate::Threshold { threshold: 1_000 };
        let circuit = attest_circuit(&pred);
        let just_under =
            AttestWitness { attr: BabyBear::new(999), salt: BabyBear::new(0xBEE5) };
        let (bad_trace, bad_pis) = generate_attest_trace(&just_under, &pred);
        assert!(
            proving_rejects(&circuit, &bad_trace, &bad_pis),
            "attr=999 (one below threshold 1000) must NOT attest >= 1000 — \
             diff = -1 (rep p-1) has no {RANGE_BITS}-bit decomposition"
        );

        // And the honest just-at-threshold case (diff = 0) DOES attest, so the
        // gadget is not merely rejecting everything (non-vacuity from the other side).
        let at = AttestWitness { attr: BabyBear::new(1_000), salt: BabyBear::new(0xBEE6) };
        let (ok_trace, ok_pis) = generate_attest_trace(&at, &pred);
        let proof = prove_dsl_zk(&circuit, &ok_trace, &ok_pis)
            .expect("attr=1000 >= threshold 1000 (diff=0) must attest");
        verify_dsl_zk(&circuit, &proof, &ok_pis)
            .expect("the at-threshold attestation must verify");
    }

    /// PROVE-SOLVENT: a cell committing balance = 500 issues an accepting
    /// `Positive` (balance ≥ 1) attestation; a zero-balance cell cannot.
    #[test]
    fn prove_solvent_worked_example() {
        let pred = Predicate::Positive;
        let circuit = attest_circuit(&pred);

        // TRUE: balance 500 ≥ 1. Only [commitment] is public — the balance is hidden.
        let w = AttestWitness { attr: BabyBear::new(500), salt: BabyBear::new(0xBA1) };
        let (trace, pis) = generate_attest_trace(&w, &pred);
        assert_eq!(pis.len(), 1, "Positive discloses only the commitment");
        let proof = prove_dsl_zk(&circuit, &trace, &pis)
            .expect("balance 500 ≥ 1 must produce an accepting solvency attestation");
        verify_dsl_zk(&circuit, &proof, &pis).expect("the solvency attestation must verify");

        // FALSE: balance 0. diff = 0 - 1 = -1 (field rep p-1 ≈ 2^31) has no
        // 30-bit decomposition (2^30 < p-1) → no verifying proof.
        let broke = AttestWitness { attr: BabyBear::new(0), salt: BabyBear::new(0xDEAD) };
        let (bad_trace, bad_pis) = generate_attest_trace(&broke, &pred);
        assert!(
            proving_rejects(&circuit, &bad_trace, &bad_pis),
            "a zero-balance cell must NOT be able to forge a solvency attestation"
        );
    }

    /// MEMBERSHIP: a cell committing tag = 7 proves `tag ∈ {3,7,11}`; a cell
    /// committing tag = 5 cannot (no selector can fire without violating its gate).
    #[test]
    fn prove_membership_worked_example() {
        let pred = Predicate::Membership { members: vec![3, 7, 11] };
        let circuit = attest_circuit(&pred);

        let w = AttestWitness { attr: BabyBear::new(7), salt: BabyBear::new(0xCAFE) };
        let (trace, pis) = generate_attest_trace(&w, &pred);
        let proof = prove_dsl_zk(&circuit, &trace, &pis)
            .expect("tag 7 ∈ {3,7,11} must produce an accepting membership attestation");
        verify_dsl_zk(&circuit, &proof, &pis).expect("the membership attestation must verify");

        // FALSE: tag 5 ∉ {3,7,11}. No flag can be set: setting any flag forces
        // attr == that member (gate), which is false; leaving all flags 0 fails
        // AtLeastOne. The honest generator leaves all flags 0 → AtLeastOne bites.
        let outsider = AttestWitness { attr: BabyBear::new(5), salt: BabyBear::new(0xF00D) };
        let (bad_trace, bad_pis) = generate_attest_trace(&outsider, &pred);
        assert!(
            proving_rejects(&circuit, &bad_trace, &bad_pis),
            "tag 5 ∉ {{3,7,11}} must NOT produce a membership attestation"
        );
        // And forging a flag for a non-matching member also fails (the gate bites):
        // set sel0 (member 3) while attr = 5 → 1*(5-3) = 2 ≠ 0.
        let mut forged = bad_trace.clone();
        forged[0][col::PRED_BASE] = BabyBear::ONE;
        forged[1][col::PRED_BASE] = BabyBear::ONE;
        assert!(
            proving_rejects(&circuit, &forged, &bad_pis),
            "forging a membership selector for a non-matching member must fail the gate"
        );
    }

    /// EQUALITY: a cell committing field = 42 proves `field == 42` (disclosing the
    /// value); a cell committing field = 41 cannot claim `field == 42`.
    #[test]
    fn prove_equality_worked_example() {
        let pred = Predicate::Equality { value: 42 };
        let circuit = attest_circuit(&pred);

        let w = AttestWitness { attr: BabyBear::new(42), salt: BabyBear::new(0xABBA) };
        let (trace, pis) = generate_attest_trace(&w, &pred);
        let proof = prove_dsl_zk(&circuit, &trace, &pis)
            .expect("field == 42 must produce an accepting equality attestation");
        verify_dsl_zk(&circuit, &proof, &pis).expect("the equality attestation must verify");

        // FALSE: the cell committed 41 but tries to claim == 42. The opening binds
        // attr = 41 (to its real commitment), and attr - value == 0 then fails
        // against value = 42.
        let other = AttestWitness { attr: BabyBear::new(41), salt: BabyBear::new(0xBEEF) };
        let real_commitment = other.commitment();
        // Build a trace that opens the REAL commitment (attr=41) but pins value=42.
        let (mut bad_trace, _) = generate_attest_trace(&other, &Predicate::Equality { value: 41 });
        // Re-point the public param to 42 and the value column to 42; the opening
        // still binds attr=41, so attr - value = -1 ≠ 0.
        let val_col = col::PRED_BASE;
        bad_trace[0][val_col] = BabyBear::new(42);
        bad_trace[1][val_col] = BabyBear::new(42);
        let bad_pis = vec![real_commitment, BabyBear::new(42)];
        assert!(
            proving_rejects(&circuit, &bad_trace, &bad_pis),
            "a cell committing 41 must NOT attest field == 42"
        );
    }

    /// The commitment-OPENING binds the attestation to the published commitment:
    /// a prover cannot attest a predicate over an `attr` that does not open the
    /// public commitment. (Tamper attr in the trace but keep the published
    /// commitment PI → the Hash opening constraint bites.)
    #[test]
    fn opening_binds_to_published_commitment() {
        let pred = Predicate::Positive;
        let circuit = attest_circuit(&pred);
        let w = AttestWitness { attr: BabyBear::new(500), salt: BabyBear::new(0xBA1) };
        let (trace, pis) = generate_attest_trace(&w, &pred);

        // Swap in a DIFFERENT attr (still ≥ 1) but keep the published commitment PI
        // (which is hash_fact(500, ...)). The opening hash now disagrees with the
        // pinned commitment → no verifying proof.
        let mut bad = trace.clone();
        bad[0][col::ATTR] = BabyBear::new(499);
        bad[1][col::ATTR] = BabyBear::new(499);
        // (diff/bits left as the 500-derived decomposition; even if they matched,
        // the OPENING is what bites here — the commitment is hash_fact(500,..).)
        assert!(
            proving_rejects(&circuit, &bad, &pis),
            "an attr that does not open the published commitment must not attest"
        );
    }
}
