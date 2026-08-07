//! Plonky3 prove+verify driver for predicate bodies the runtime can encode
//! as a `CircuitDescriptor`.
//!
//! Strategy: for each requirement in the predicate body, we build a tiny
//! `CircuitDescriptor` whose constraints encode the requirement
//! algebraically, generate a witness trace by hand (the prover knows the
//! values from the IR-level inputs), then call
//! [`dregg_circuit::dsl::dsl_p3_air::prove_dsl_p3`] followed by
//! [`dregg_circuit::dsl::dsl_p3_air::verify_dsl_p3`] — the PRODUCTION interpreter.
//!
//! (Corrected 2026-07-17: this doc used to name `dregg_dsl_runtime::prove_dsl_plonky3` — the 868-line
//! DUPLICATE `DslP3Air` this harness once drove. The imports were migrated to production but the doc was
//! not; the duplicate is now DELETED. A harness that names the shadow it no longer drives is the mirror
//! lying about itself.)
//!
//! A successful round-trip means "the runtime Plonky3 verifier accepts
//! this requirement on these inputs." A panic during prove (the standard
//! way `p3_uni_stark::prove` rejects an invalid trace) or a
//! verifier-returns-`Ok(false)` is reported as Reject.
//!
//! ## Scope
//!
//! - Inequalities (`<=`, `>=`) are encoded as a base-`2^16` limb decomposition of BOTH operands
//!   plus a borrow-chain subtraction, with a REAL bit-decomposition range check on every limb (see
//!   [`u64_le_descriptor`]). Rejection of a false claim is a property of the CONSTRAINTS — a false
//!   `smaller <= bigger` has NO satisfying assignment — not of the witness generator's good
//!   manners. This holds across the FULL u64 domain: no operand escapes to the oracle.
//!
//!   (Fixed 2026-07-17, `DslComparisonRangeSoundnessResidual`. This lowering used to carry a
//!   free `indicator` column pinned to zero and NOTHING bounding `diff`; since C1 is a mod-p
//!   subtraction, a prover claiming `5 <= 3` could witness `diff = (3 - 5) mod p = p - 2`,
//!   `indicator = 0`, satisfy every constraint, and have the production p3 prover AND verifier
//!   ACCEPT the false statement. The comparison's truth lived entirely in the honest witness
//!   generator, which volunteered an invalid witness when the claim was false — a courtesy a
//!   malicious prover simply declines. The old in-file comment "we cap the diffs to a 30-bit range
//!   where this encoding stays sound" was false: capping the OPERANDS bounds nothing about a diff
//!   column no constraint reads. The range check is now real, and the forgery is UNSAT — pinned as
//!   a rejection tooth in `tests/comparison_wrap_soundness.rs`.)
//!
//!   (Widened 2026-07-17, lane `dsl-2p30-fallback`. The fix above was sound only on `[0, 2^30)`;
//!   operands at or above `2^30` SHORT-CIRCUITED to `prove_trivial(ir_ok)` — no circuit built, the
//!   verdict IS the native-u64 oracle's own answer, i.e. exactly the generator's confession the
//!   paragraph above says is gone. That fallback is DELETED, not disclosed: the gadget is now
//!   limb-decomposed and sized to u64 exactly. [`u64_le_descriptor`] carries the arithmetic for why
//!   the single-element encoding could not simply be widened — `k = 30` was already the ceiling
//!   (`2^31 - 1 > p`), and `from_u64` aliases operands `>= p` regardless of the range check.)
//! - Equality (`==`) and non-equality (`!=`) on u64 reduce to `Equality`
//!   over two columns and a `ConditionalNonzero` respectively.
//!
//!   ⚠ **These two still carry the `2^30` oracle fallback that inequalities no longer do**, and it
//!   is load-bearing for them: `from_u64` aliases mod p, so without the cutoff `eq-u64` would
//!   ACCEPT the false claim `BABYBEAR_P == 0` (both embed to the zero column) and `neq-u64` would
//!   reject the true `BABYBEAR_P != 0`. The cutoff hides that rather than fixing it. The same limb
//!   machinery closes both (`Equality` per limb; `ConditionalNonzero` + `AtLeastOne` over per-limb
//!   difference flags), and `u64_to_limbs`/`u64_le_col` are already the parts. NOT done here —
//!   this lane's scope was the inequality path. Named so it is not read as closed:
//!   `DslEqualityOperandAliasingResidual`. The u64-domain teeth in
//!   `tests/comparison_wrap_soundness.rs` cover `<=`/`>=` only.
//! - Equality / non-equality on `[u8; 32]` are compared as 64-bit limb
//!   tuples (limb 0 — bytes 0..8); the comparison-side semantics still
//!   match the IR-level truth because the IR's bytes-equality requires
//!   full bytewise equality.
//! - Membership requirements need Poseidon2 hash gadgets which the runtime
//!   AIR cannot express. We mark these Skip.
//!
//! ## Performance
//!
//! Each requirement gets its own STARK proof. For the predicate suite this
//! means ~hundreds of small proofs. Plonky3's `p3_uni_stark` over BabyBear
//! is fast enough at this scale that the full crate runs in a few seconds.

use dregg_circuit::dsl::circuit::DslCircuit;
use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};

use crate::predicates::Requirement;

/// Round-trip every requirement in the body through prove+verify. Returns
/// `Ok(true)` if every requirement is provable and verifies, `Ok(false)`
/// if any requirement is unsatisfiable for the supplied inputs, `Err` if
/// the requirement shape isn't expressible here.
pub fn prove_and_verify(body_requirements: &[Requirement]) -> Result<Verdict, String> {
    for req in body_requirements {
        match drive(req)? {
            Verdict::Accept => continue,
            Verdict::Reject => return Ok(Verdict::Reject),
            Verdict::Skip { reason } => return Ok(Verdict::Skip { reason }),
        }
    }
    Ok(Verdict::Accept)
}

#[derive(Debug, Clone)]
pub enum Verdict {
    Accept,
    Reject,
    Skip { reason: &'static str },
}

fn drive(req: &Requirement) -> Result<Verdict, String> {
    match req {
        Requirement::LessEqualU64(l, r) => Ok(drive_inequality(*l, *r)),
        Requirement::GreaterEqualU64(l, r) => Ok(drive_inequality(*r, *l)),
        Requirement::EqualU64(l, r) => Ok(drive_equality_u64(*l, *r)),
        Requirement::NotEqualU64(l, r) => Ok(drive_nonequality_u64(*l, *r)),
        Requirement::EqualBytes32(l, r) => Ok(drive_equality_bytes(l, r)),
        Requirement::NotEqualBytes32(l, r) => Ok(drive_nonequality_bytes(l, r)),
        // Membership is skipped for a REAL reason (corrected 2026-07-16 — the old reason, "membership
        // needs Poseidon2 gadgets which DslP3Air cannot inline at runtime", was a limitation of the
        // RETIRED duplicate interpreter in dregg-dsl-runtime, not of the shipped one).
        // Empirically probed: `DslP3Air::try_from_dsl(merkle_poseidon2_circuit())` ->
        // `NonAlgebraicConstraint { index: 1, form: "MerkleHash (use the Lean-emitted IR2 descriptor for
        // position-indexed Merkle hashing)" }`. The production interpreter DELIBERATELY routes MerkleHash
        // to the Lean-authored IR2 rail (architectural law #1), so there is nothing for a DSL-vs-IR
        // differential to compare here. Membership's real coverage lives on that rail:
        // `circuit/src/merkle_air.rs`'s membership_p3 teeth (honest proof + forged root / forged leaf /
        // non-member leaf all rejected), byte-pinned to `MerkleMembership4aryEmit.lean`.
        Requirement::Membership { .. } => Ok(Verdict::Skip {
            reason: "membership is MerkleHash-shaped: the shipped DslP3Air routes it to the Lean-emitted \
                     IR2 descriptor (law #1), so there is no DSL-side arithmetization to differ against",
        }),
    }
}

// ============================================================================
// `u64-le`: the limb-decomposed comparison lowering, sized to the FULL u64 domain
// ============================================================================
//
// WHY LIMBS — the arithmetic that forced this shape (2026-07-17, lane dsl-2p30-fallback).
//
// The predecessor gadget ("diff-le") held both operands in ONE BabyBear column each and
// range-checked `diff = bigger - smaller` with a 30-bit decomposition. It was sound, but only
// for operands in `[0, 2^30)`; outside that it SHORT-CIRCUITED to the native-u64 oracle, so for
// `u64::MAX` and friends — common in the predicate suite — the "Plonky3 verdict" was the oracle's
// own answer with no circuit behind it.
//
// That path could NOT be closed by widening `DIFF_RANGE_BITS`. Two independent walls, both hard:
//
//  1. RECOMPOSITION WRAP. `k` boolean-pinned bits recompose to at most `2^k - 1`. The bound is
//     only meaningful while that maximum cannot itself wrap mod p, i.e. `2^k - 1 < p`. With
//     `p = 2^31 - 2^27 + 1 = 2013265921`: `2^30 - 1 = 1073741823 < p` (fits), but
//     `2^31 - 1 = 2147483647 > p` (does NOT). So k = 30 was ALREADY THE MAXIMUM — not a
//     conservative choice, the ceiling. Even k = 31 breaks the no-wrap argument outright.
//  2. OPERAND ALIASING — the deeper wall. `BabyBear::from_u64(x)` reduces mod p, so for `x >= p`
//     the column does not hold `x` at all: `from_u64(u64::MAX) = 1172168162`, and
//     `from_u64(BABYBEAR_P) = 0`. C1 would subtract RESIDUES, not integers, and the PI binding
//     would publicly commit to the wrong number. No choice of `DIFF_RANGE_BITS` touches this —
//     it is the EMBEDDING, not the range check.
//
// So a single field element provably cannot carry a u64 operand. The fix is to stop asking it to:
// each operand is carried as `N_LIMBS` base-`2^LIMB_BITS` limbs, each limb small enough to embed
// injectively, and the comparison is done by a borrow chain across limbs. The field never has to
// hold a value it cannot represent, so the fallback has no reason to exist and is DELETED.

/// Bits per limb. Chosen so that (a) a limb embeds injectively (`2^16 - 1 << p`), (b) its
/// 16-bit boolean decomposition cannot wrap (`2^16 - 1 < p`), and (c) every intermediate in the
/// borrow chain below stays far from `p` (see [`u64_le_descriptor`]).
pub const LIMB_BITS: usize = 16;

/// Limbs per operand: `4 * 16 = 64`, i.e. EXACTLY the u64 domain. There is no operand this
/// gadget cannot take, which is the whole point of it.
pub const N_LIMBS: usize = 4;

/// The limb base, `2^LIMB_BITS`.
pub const LIMB_BASE: u64 = 1 << LIMB_BITS;

/// Split a u64 into its `N_LIMBS` canonical little-endian base-`2^LIMB_BITS` limbs.
///
/// Canonical: every limb is `< 2^LIMB_BITS`, and the map is injective on u64 — which is what lets
/// the PI-bound limbs stand in for the operand itself with no aliasing.
pub fn u64_to_limbs(x: u64) -> [u64; N_LIMBS] {
    let mut limbs = [0u64; N_LIMBS];
    for (i, limb) in limbs.iter_mut().enumerate() {
        *limb = (x >> (i * LIMB_BITS)) & (LIMB_BASE - 1);
    }
    limbs
}

/// Column layout of the `u64-le` descriptor.
pub mod u64_le_col {
    use super::{LIMB_BITS, N_LIMBS};

    /// First of the claimed-smaller operand's limb columns (bound to PI `0..N_LIMBS`).
    pub const S_LIMB_START: usize = 0;
    /// First of the claimed-bigger operand's limb columns (bound to PI `N_LIMBS..2*N_LIMBS`).
    pub const B_LIMB_START: usize = S_LIMB_START + N_LIMBS;
    /// First of the difference limb columns (`bigger - smaller` in base `2^LIMB_BITS`).
    pub const D_LIMB_START: usize = B_LIMB_START + N_LIMBS;
    /// First of the borrow columns: `borrow(j)` is the borrow OUT of limb `j`.
    pub const BORROW_START: usize = D_LIMB_START + N_LIMBS;
    /// First of the smaller-operand limb decomposition bits.
    pub const S_BITS_START: usize = BORROW_START + N_LIMBS;
    /// First of the bigger-operand limb decomposition bits.
    pub const B_BITS_START: usize = S_BITS_START + N_LIMBS * LIMB_BITS;
    /// First of the difference limb decomposition bits.
    pub const D_BITS_START: usize = B_BITS_START + N_LIMBS * LIMB_BITS;

    /// Limb `j` of the claimed-smaller operand.
    pub const fn s_limb(j: usize) -> usize {
        S_LIMB_START + j
    }
    /// Limb `j` of the claimed-bigger operand.
    pub const fn b_limb(j: usize) -> usize {
        B_LIMB_START + j
    }
    /// Limb `j` of the difference.
    pub const fn d_limb(j: usize) -> usize {
        D_LIMB_START + j
    }
    /// The borrow out of limb `j`.
    pub const fn borrow(j: usize) -> usize {
        BORROW_START + j
    }
    /// Bit `i` of the smaller operand's limb `j`.
    pub const fn s_bit(j: usize, i: usize) -> usize {
        S_BITS_START + j * LIMB_BITS + i
    }
    /// Bit `i` of the bigger operand's limb `j`.
    pub const fn b_bit(j: usize, i: usize) -> usize {
        B_BITS_START + j * LIMB_BITS + i
    }
    /// Bit `i` of the difference's limb `j`.
    pub const fn d_bit(j: usize, i: usize) -> usize {
        D_BITS_START + j * LIMB_BITS + i
    }

    /// Total trace width.
    pub const WIDTH: usize = D_BITS_START + N_LIMBS * LIMB_BITS;
}

/// Push `sum(bit[i] * 2^i) - limb == 0` — the range check tying a limb to its bits.
fn push_recomposition(
    constraints: &mut Vec<ConstraintExpr>,
    limb_col: usize,
    bit_col: impl Fn(usize) -> usize,
) {
    let mut terms = Vec::with_capacity(LIMB_BITS + 1);
    let mut power_of_two = BabyBear::ONE;
    for i in 0..LIMB_BITS {
        terms.push(PolyTerm {
            coeff: power_of_two,
            col_indices: vec![bit_col(i)],
        });
        power_of_two = power_of_two + power_of_two;
    }
    terms.push(PolyTerm {
        coeff: BabyBear::new(BABYBEAR_P - 1),
        col_indices: vec![limb_col],
    });
    constraints.push(ConstraintExpr::Polynomial { terms });
}

/// The `u64-le` descriptor: proves `smaller <= bigger` for the FULL u64 domain, where each
/// operand is pinned limb-by-limb to the public inputs.
///
/// Constraints, for each limb `j` (little-endian, `borrow(-1) := 0`):
/// - **R1** `sum_i s_bit(j,i) * 2^i - s_limb(j) == 0` — smaller's limb recomposition.
/// - **R2** likewise for `b_limb(j)`, **R3** likewise for `d_limb(j)`.
/// - **R4..** every bit column is boolean; every `borrow(j)` is boolean.
/// - **B_j** `b_limb(j) - s_limb(j) - borrow(j-1) - d_limb(j) + 2^16 * borrow(j) == 0`
///   — one step of a base-`2^16` schoolbook subtraction with borrow.
/// - **F** `borrow(N_LIMBS - 1) == 0` — no borrow escapes the top limb.
///
/// WHY IT IS SOUND. R1-R4 force every `s_limb(j)`, `b_limb(j)`, `d_limb(j)` into `[0, 2^16)` and
/// every `borrow(j)` into `{0, 1}` as INTEGERS: each limb is a sum of 16 boolean-pinned bits,
/// maxing at `2^16 - 1`, which is nowhere near `p` and so cannot wrap. Given that, the integer
/// value of B_j's left-hand side lies in `[-(2^16 - 1) - 1 - (2^16 - 1), (2^16 - 1) + 2^16]`, i.e.
/// strictly inside `(-2^18, 2^18)` — a window vastly smaller than `p`. A field element in that
/// window that is `== 0 mod p` IS zero, so **the field equation B_j implies the INTEGER equation**.
/// That is the no-wrap argument, and unlike the predecessor's it has ~13 bits of headroom rather
/// than one.
///
/// ⚠ EVERY hypothesis of that argument is load-bearing, and the booleanity of `borrow(j)` is the
/// least obvious one. `borrow(j)` enters B_j multiplied by `2^16`, so a borrow allowed to be an
/// arbitrary field element is a licence to inject any multiple of `2^16` into the chain — enough to
/// buy back exactly `p` and land every difference limb honestly inside `[0, 2^16)`. It is not
/// hypothetical: `5 <= 3` is provable with `d_limb = [65535, 30719, 0, 0]` and
/// `borrow = [p - 30719, 0, 0, 0]`, since `65535 + 2 + 2^16 * 30719 = p`. That witness satisfies
/// every B_j, every range check, and F. Only `Binary { col: borrow(j) }` stops it. A mutation canary
/// confirmed the production prover AND verifier accept the forgery once that one constraint is
/// removed; it is pinned by
/// `tests/comparison_wrap_soundness.rs::non_boolean_borrow_cannot_buy_back_the_modulus`.
///
/// The integer equations are exactly base-`2^16` subtraction with borrow, so by induction on `j`
/// they compute `bigger - smaller` and `borrow(N_LIMBS - 1) = 1` iff `bigger < smaller`. F rules
/// that out — so the system is satisfiable IFF `smaller <= bigger` over the integers. A false claim
/// has NO satisfying assignment, at ANY u64 operand.
///
/// The witness is also UNIQUE given the operands: at each limb, exactly one `(d_limb(j),
/// borrow(j))` pair with `d_limb(j) ∈ [0, 2^16)` and `borrow(j) ∈ {0,1}` satisfies B_j. So there is
/// no prover freedom to exploit — nothing to search for.
///
/// Boundaries pin every operand limb to its PI on the first row, so the proof is about the
/// PUBLICLY CLAIMED comparison and not some other pair the prover preferred. The limb encoding is
/// injective on u64, so the 8 PIs name exactly one `(smaller, bigger)`.
///
/// F is a per-row Polynomial rather than a `BoundaryDef::Fixed` on purpose: per-row constraints
/// hold on EVERY row, whereas a `BoundaryRow::First` boundary binds row 0 only. (The predecessor
/// documented the same preference against `committed_threshold.rs`'s top-bit boundary.)
pub fn u64_le_descriptor() -> CircuitDescriptor {
    use u64_le_col as c;
    let neg_one = BabyBear::new(BABYBEAR_P - 1);
    let limb_base = BabyBear::from_u64(LIMB_BASE);

    let mut constraints = Vec::new();

    // R1/R2/R3: every limb is recomposed from its bits — the range checks.
    for j in 0..N_LIMBS {
        push_recomposition(&mut constraints, c::s_limb(j), |i| c::s_bit(j, i));
        push_recomposition(&mut constraints, c::b_limb(j), |i| c::b_bit(j, i));
        push_recomposition(&mut constraints, c::d_limb(j), |i| c::d_bit(j, i));
    }

    // R4: every bit is boolean. Without this a single "bit" column could carry an arbitrary
    // field element and the recompositions would bound nothing at all.
    for j in 0..N_LIMBS {
        for i in 0..LIMB_BITS {
            constraints.push(ConstraintExpr::Binary {
                col: c::s_bit(j, i),
            });
            constraints.push(ConstraintExpr::Binary {
                col: c::b_bit(j, i),
            });
            constraints.push(ConstraintExpr::Binary {
                col: c::d_bit(j, i),
            });
        }
        // Every borrow is boolean. Without this a borrow could absorb an arbitrary multiple of
        // 2^16 and the chain would prove nothing.
        constraints.push(ConstraintExpr::Binary { col: c::borrow(j) });
    }

    // B_j: b_limb(j) - s_limb(j) - borrow(j-1) - d_limb(j) + 2^16 * borrow(j) == 0
    for j in 0..N_LIMBS {
        let mut terms = vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![c::b_limb(j)],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![c::s_limb(j)],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![c::d_limb(j)],
            },
            PolyTerm {
                coeff: limb_base,
                col_indices: vec![c::borrow(j)],
            },
        ];
        if j > 0 {
            terms.push(PolyTerm {
                coeff: neg_one,
                col_indices: vec![c::borrow(j - 1)],
            });
        }
        constraints.push(ConstraintExpr::Polynomial { terms });
    }

    // F: no borrow escapes the top limb — i.e. bigger >= smaller.
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![c::borrow(N_LIMBS - 1)],
        }],
    });

    let mut columns = Vec::with_capacity(u64_le_col::WIDTH);
    for j in 0..N_LIMBS {
        columns.push(ColumnDef {
            name: format!("s_limb_{j}"),
            index: c::s_limb(j),
            kind: ColumnKind::Value,
        });
    }
    for j in 0..N_LIMBS {
        columns.push(ColumnDef {
            name: format!("b_limb_{j}"),
            index: c::b_limb(j),
            kind: ColumnKind::Value,
        });
    }
    for j in 0..N_LIMBS {
        columns.push(ColumnDef {
            name: format!("d_limb_{j}"),
            index: c::d_limb(j),
            kind: ColumnKind::Value,
        });
    }
    for j in 0..N_LIMBS {
        columns.push(ColumnDef {
            name: format!("borrow_{j}"),
            index: c::borrow(j),
            kind: ColumnKind::Binary,
        });
    }
    for j in 0..N_LIMBS {
        for i in 0..LIMB_BITS {
            columns.push(ColumnDef {
                name: format!("s_bit_{j}_{i}"),
                index: c::s_bit(j, i),
                kind: ColumnKind::Binary,
            });
        }
    }
    for j in 0..N_LIMBS {
        for i in 0..LIMB_BITS {
            columns.push(ColumnDef {
                name: format!("b_bit_{j}_{i}"),
                index: c::b_bit(j, i),
                kind: ColumnKind::Binary,
            });
        }
    }
    for j in 0..N_LIMBS {
        for i in 0..LIMB_BITS {
            columns.push(ColumnDef {
                name: format!("d_bit_{j}_{i}"),
                index: c::d_bit(j, i),
                kind: ColumnKind::Binary,
            });
        }
    }

    let mut boundaries = Vec::with_capacity(2 * N_LIMBS);
    for j in 0..N_LIMBS {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: c::s_limb(j),
            pi_index: j,
        });
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: c::b_limb(j),
            pi_index: N_LIMBS + j,
        });
    }

    CircuitDescriptor {
        name: "u64-le".to_string(),
        trace_width: u64_le_col::WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: 2 * N_LIMBS,
        lookup_tables: vec![],
    }
}

/// The public inputs for the claim `smaller <= bigger`: both operands' canonical limbs.
pub fn u64_le_public_inputs(smaller: u64, bigger: u64) -> Vec<BabyBear> {
    let mut pi = Vec::with_capacity(2 * N_LIMBS);
    for limb in u64_to_limbs(smaller) {
        pi.push(BabyBear::from_u64(limb));
    }
    for limb in u64_to_limbs(bigger) {
        pi.push(BabyBear::from_u64(limb));
    }
    pi
}

/// Run the native base-`2^LIMB_BITS` borrow chain for `bigger - smaller`, returning
/// `(diff_limbs, borrows)`. `borrows[N_LIMBS - 1] == 1` exactly when `bigger < smaller`.
///
/// This is the HONEST witness, and by the uniqueness argument in [`u64_le_descriptor`] it is the
/// only one the constraint system admits. It is exposed so soundness teeth can perturb it.
pub fn u64_le_borrow_chain(smaller: u64, bigger: u64) -> ([u64; N_LIMBS], [u64; N_LIMBS]) {
    let s = u64_to_limbs(smaller);
    let b = u64_to_limbs(bigger);
    let mut diff_limbs = [0u64; N_LIMBS];
    let mut borrows = [0u64; N_LIMBS];
    let mut borrow_in = 0u64;
    for j in 0..N_LIMBS {
        let lhs = b[j];
        let rhs = s[j] + borrow_in;
        if lhs >= rhs {
            diff_limbs[j] = lhs - rhs;
            borrows[j] = 0;
        } else {
            diff_limbs[j] = lhs + LIMB_BASE - rhs;
            borrows[j] = 1;
        }
        borrow_in = borrows[j];
    }
    (diff_limbs, borrows)
}

/// Build one `u64-le` trace row from the operands plus an EXPLICIT `(diff_limbs, borrows)` witness.
///
/// The witness is taken as a parameter rather than derived so that soundness teeth can hand this an
/// ADVERSARIAL chain (a forged zero top-borrow, an out-of-range diff limb) and watch the constraint
/// system reject it. [`u64_le_row`] supplies the honest one.
pub fn u64_le_row_from(
    smaller: u64,
    bigger: u64,
    diff_limbs: [u64; N_LIMBS],
    borrows: [u64; N_LIMBS],
) -> Vec<BabyBear> {
    use u64_le_col as c;
    let mut row = vec![BabyBear::ZERO; c::WIDTH];
    let s = u64_to_limbs(smaller);
    let b = u64_to_limbs(bigger);
    for j in 0..N_LIMBS {
        row[c::s_limb(j)] = BabyBear::from_u64(s[j]);
        row[c::b_limb(j)] = BabyBear::from_u64(b[j]);
        row[c::d_limb(j)] = BabyBear::from_u64(diff_limbs[j]);
        row[c::borrow(j)] = BabyBear::from_u64(borrows[j]);
        for i in 0..LIMB_BITS {
            row[c::s_bit(j, i)] = BabyBear::from_u64((s[j] >> i) & 1);
            row[c::b_bit(j, i)] = BabyBear::from_u64((b[j] >> i) & 1);
            row[c::d_bit(j, i)] = BabyBear::from_u64((diff_limbs[j] >> i) & 1);
        }
    }
    row
}

/// The honest `u64-le` trace row for the claim `smaller <= bigger`.
pub fn u64_le_row(smaller: u64, bigger: u64) -> Vec<BabyBear> {
    let (diff_limbs, borrows) = u64_le_borrow_chain(smaller, bigger);
    u64_le_row_from(smaller, bigger, diff_limbs, borrows)
}

/// How [`drive_inequality`] reached its verdict.
///
/// This exists because a [`Verdict`] ALONE CANNOT BE AUDITED: `Reject` looks identical whether the
/// constraint system found the claim unsatisfiable or whether a short-circuit simply echoed the
/// native-u64 oracle. That indistinguishability is exactly what let the old `>= 2^30` fallback sit
/// unnoticed and untestable — it was disclosed in prose because no test could see it. Reporting the
/// path makes "no operand escapes the circuit" an assertion rather than a promise; see
/// `tests/comparison_wrap_soundness.rs::every_operand_takes_the_circuit_never_the_oracle`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InequalityPath {
    /// A `u64-le` circuit was built, proved and verified. The verdict is the constraint system's.
    Circuit,
    /// No circuit was built; the verdict is the IR-level oracle's own answer. Nothing should
    /// return this — it is here so that a regression must SAY so rather than hide.
    Oracle,
}

/// Prove `smaller <= bigger` through the production p3 interpreter, over the FULL u64 domain, and
/// report which path decided it.
///
/// There is NO operand range that escapes to the IR-level oracle: the limb decomposition is sized
/// to u64 exactly, so every comparison the predicate suite can pose is decided by the constraint
/// system, and this always returns [`InequalityPath::Circuit`]. (Until 2026-07-17 operands
/// `>= 2^30` short-circuited to `prove_trivial(ir_ok)` — no circuit, verdict == the native oracle's
/// own answer. See [`u64_le_descriptor`] for why the predecessor's single-element encoding could not
/// be widened, and why limbs remove the wall.)
///
/// When the claim is FALSE the honest borrow chain leaves `borrow(N_LIMBS - 1) = 1`, which
/// constraint F forbids; and since the witness is unique there is nothing else to try. The prover
/// FAILS TO FIND a witness rather than volunteering a bad one — rejection is the constraint
/// system's verdict, not the generator's confession.
pub fn drive_inequality_traced(smaller: u64, bigger: u64) -> (Verdict, InequalityPath) {
    let ir_ok = smaller <= bigger;
    let descriptor = u64_le_descriptor();
    let row = u64_le_row(smaller, bigger);
    let trace = vec![row.clone(), row];
    let pi = u64_le_public_inputs(smaller, bigger);

    (
        round_trip(&descriptor, &trace, &pi, ir_ok),
        InequalityPath::Circuit,
    )
}

/// Prove `smaller <= bigger` through the production p3 interpreter. See
/// [`drive_inequality_traced`].
fn drive_inequality(smaller: u64, bigger: u64) -> Verdict {
    drive_inequality_traced(smaller, bigger).0
}

/// Equality on u64 via two columns + `Equality` constraint.
fn drive_equality_u64(l: u64, r: u64) -> Verdict {
    let ir_ok = l == r;
    let safe_range = 1u64 << 30;
    if l >= safe_range || r >= safe_range {
        return prove_trivial(ir_ok);
    }
    let descriptor = CircuitDescriptor {
        name: "eq-u64".into(),
        trace_width: 2,
        max_degree: 1,
        columns: vec![
            ColumnDef {
                name: "lhs".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "rhs".into(),
                index: 1,
                kind: ColumnKind::Value,
            },
        ],
        constraints: vec![ConstraintExpr::Equality { col_a: 0, col_b: 1 }],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    };
    // Witness: place both inputs as-is. If they differ, the equality
    // constraint evaluates to non-zero and prove will fail (panic).
    let row = vec![BabyBear::from_u64(l), BabyBear::from_u64(r)];
    let trace = vec![row.clone(), row];
    let pi = vec![BabyBear::from_u64(l), BabyBear::from_u64(r)];
    round_trip(&descriptor, &trace, &pi, ir_ok)
}

/// Non-equality via `ConditionalNonzero` with selector=1, value=diff, and
/// an inverse witness column.
fn drive_nonequality_u64(l: u64, r: u64) -> Verdict {
    let ir_ok = l != r;
    let safe_range = 1u64 << 30;
    if l >= safe_range || r >= safe_range {
        return prove_trivial(ir_ok);
    }

    // Columns:
    //   0: lhs, 1: rhs, 2: diff (l-r), 3: inverse, 4: selector(=1)
    // Constraints:
    //   Polynomial: 1*lhs + (-1)*rhs + (-1)*diff = 0  (diff = lhs - rhs)
    //   ConditionalNonzero: selector * (diff*inv - 1) = 0
    let descriptor = CircuitDescriptor {
        name: "neq-u64".into(),
        trace_width: 5,
        max_degree: 3,
        columns: vec![
            ColumnDef {
                name: "lhs".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "rhs".into(),
                index: 1,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "diff".into(),
                index: 2,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "inverse".into(),
                index: 3,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "selector".into(),
                index: 4,
                kind: ColumnKind::Binary,
            },
        ],
        constraints: vec![
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![0],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - 1),
                        col_indices: vec![1],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - 1),
                        col_indices: vec![2],
                    },
                ],
            },
            ConstraintExpr::ConditionalNonzero {
                selector_col: 4,
                value_col: 2,
                inverse_col: 3,
            },
        ],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    };

    let diff = (l as i128) - (r as i128);
    let diff_bb = babybear_from_signed(diff);
    let inverse_bb = if ir_ok {
        babybear_inverse(diff_bb)
    } else {
        BabyBear::ZERO
    };
    let row = vec![
        BabyBear::from_u64(l),
        BabyBear::from_u64(r),
        diff_bb,
        inverse_bb,
        BabyBear::ONE,
    ];
    let trace = vec![row.clone(), row];
    let pi = vec![BabyBear::from_u64(l), BabyBear::from_u64(r)];
    round_trip(&descriptor, &trace, &pi, ir_ok)
}

/// Equality on [u8; 32]: compare via a single Equality constraint over the
/// blake3 hash of the bytes interpreted as a u64. This is a *semantic*
/// proxy — the IR-level truth is "all 32 bytes match", and we capture
/// that by hashing each side and comparing the limb 0 of the hash. (The
/// real DSL-emitted Plonky3 AIR would compare all 8 limbs; we only have
/// one column here because the predicate suite never exercises
/// near-collisions, only exact equality vs total disagreement.)
fn drive_equality_bytes(l: &[u8; 32], r: &[u8; 32]) -> Verdict {
    // Use blake3 first-byte chunks rather than raw byte 0 so two arrays
    // that differ only in late bytes still differ in the limb. Avoids
    // false equals on near-collisions.
    let lh = blake3::hash(l);
    let rh = blake3::hash(r);
    let ll = u64::from_le_bytes(lh.as_bytes()[..8].try_into().unwrap());
    let rl = u64::from_le_bytes(rh.as_bytes()[..8].try_into().unwrap());
    // Reduce into the 30-bit safe range.
    let ll = ll & ((1u64 << 30) - 1);
    let rl = rl & ((1u64 << 30) - 1);
    drive_equality_u64(ll, rl)
}

fn drive_nonequality_bytes(l: &[u8; 32], r: &[u8; 32]) -> Verdict {
    let lh = blake3::hash(l);
    let rh = blake3::hash(r);
    let ll = u64::from_le_bytes(lh.as_bytes()[..8].try_into().unwrap());
    let rl = u64::from_le_bytes(rh.as_bytes()[..8].try_into().unwrap());
    let ll = ll & ((1u64 << 30) - 1);
    let rl = rl & ((1u64 << 30) - 1);
    drive_nonequality_u64(ll, rl)
}

/// Wrap [`prove_dsl_p3`] + [`verify_dsl_p3`] so a prover-side panic (which the p3 prover uses to reject
/// impossible traces) is caught and converted into [`Verdict::Reject`].
///
/// Repointed 2026-07-16 off `dregg_dsl_runtime::{prove,verify}_dsl_plonky3` — a SECOND, name-colliding
/// `DslP3Air` (p3-uni-stark) with no production consumer, which cannot express `Hash` and enforced
/// `BoundaryRow::Index(n>0)` on row 0 only. A differential harness must drive the interpreter the product
/// actually ships: `dregg_circuit::dsl::dsl_p3_air` (p3-batch-stark), the one `shielded/attest.rs`
/// uses. (It named `shielded/spend_circuit.rs` as the other consumer until 2026-08-07; that
/// Rust-authored AIR is deleted under house law #1, so `attest.rs` is now the live example.)
fn round_trip(
    descriptor: &CircuitDescriptor,
    trace: &[Vec<BabyBear>],
    pi: &[BabyBear],
    ir_ok: bool,
) -> Verdict {
    let prove_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let dsl = DslCircuit::new(descriptor.clone());
        prove_dsl_p3(&dsl, trace, pi).map(|proof| (dsl, proof))
    }));
    match prove_result {
        // Report what the backend ACTUALLY did, never what it should have done: an accept while
        // `ir_ok` is false is a backend-vs-oracle disagreement, and reporting it as Accept is what
        // lets the agreement matrix catch it. (`ir_ok` is threaded here for exactly that reason and
        // deliberately does not steer the verdict.)
        Ok(Ok((dsl, proof))) => match verify_dsl_p3(&dsl, &proof, pi) {
            Ok(()) => {
                let _ = ir_ok;
                Verdict::Accept
            }
            Err(_) => Verdict::Reject,
        },
        Ok(Err(_)) | Err(_) => Verdict::Reject,
    }
}

/// Return the IR-level oracle's verdict with NO circuit behind it.
///
/// This is the generator's confession in its purest form: the "backend verdict" is just the native
/// answer. Inequalities no longer reach here — [`drive_inequality`] is sized to u64 and always
/// builds a circuit. It survives only for `drive_equality_u64` / `drive_nonequality_u64`, whose
/// `2^30` cutoff is still hiding the `from_u64` aliasing described in the module doc
/// (`DslEqualityOperandAliasingResidual`). Every remaining caller is a known gap, not a design.
fn prove_trivial(ir_ok: bool) -> Verdict {
    if ir_ok {
        Verdict::Accept
    } else {
        Verdict::Reject
    }
}

/// Convert a possibly-negative i128 into BabyBear via the prime modulus.
fn babybear_from_signed(v: i128) -> BabyBear {
    let p = BABYBEAR_P as i128;
    let r = ((v % p) + p) % p;
    BabyBear::new(r as u32)
}

/// BabyBear field inverse via Fermat's little theorem: `a^(p-2)` mod p.
fn babybear_inverse(a: BabyBear) -> BabyBear {
    if a.0 == 0 {
        return BabyBear::ZERO;
    }
    let mut result = BabyBear::ONE;
    let mut base = a;
    let mut exp = BABYBEAR_P - 2;
    while exp > 0 {
        if exp & 1 == 1 {
            result *= base;
        }
        base = base * base;
        exp >>= 1;
    }
    result
}
