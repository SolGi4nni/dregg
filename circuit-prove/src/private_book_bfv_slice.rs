//! Exact native-field BFV same-opening slice for the private Dark Bazaar.
//!
//! The AIR is authored in Lean by
//! `Market/PrivateBookBfvSliceDescriptor.lean`.  This module only validates the
//! fixed production shape, fills the emitted 4,096-row witness, and invokes the
//! HidingFRI backend.  The proved equation is the complete negacyclic
//! coefficient-zero equation for order 0 / ciphertext polynomial 0 / modulus
//! 0.  It is one exact member of the 98,304-equation production family, not a
//! randomized projection.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
    chip_absorb_all_lanes, ir2_eval_accepts, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;

use crate::dark_bazaar_private::{
    DIGEST_WIDTH, MAX_QTY, ORDER_COUNT, PRICE_COUNT, PrivateBookWitness,
    PublicStatement as BookPublicStatement, RULE_ID, build_row,
};

pub const PRIVATE_BOOK_BFV_SLICE_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/private-book-bfv-slice-o0-c0-q0-k0.json");

pub const DEGREE: usize = 4096;
pub const MODULUS: u64 = 68_719_403_009;
pub const PRODUCTION_EQUATION_COUNT: usize = 4 * 2 * 3 * DEGREE;
pub const MATERIALIZED_EQUATION_COUNT: usize = 1;
pub const REMAINING_EQUATION_COUNT: usize = PRODUCTION_EQUATION_COUNT - MATERIALIZED_EQUATION_COUNT;
const RADIX: i128 = 1 << 15;
const MODULUS_LIMBS: [i128; 3] = [24_577, 32_765, 63];
const MODULUS_MINUS_ONE_LIMBS: [i128; 3] = [24_576, 32_765, 63];
const PK_CHAIN_DOMAIN: u32 = 1_346_523_979;
const SLICE_TAG: u32 = 1_111_903_040;

const DB_TRACE_WIDTH: usize = 181;
const QTY_SEL_BASE: usize = DB_TRACE_WIDTH;
const NEG: usize = 245;
const LAST: usize = 246;
const INDEX: usize = 247;
const U_SHIFT: usize = 248;
const U_BIT_BASE: usize = 249;
const ERROR_SHIFT: usize = 255;
const ERROR_BIT_BASE: usize = 256;
const REDUCTION_SHIFT: usize = 262;
const REDUCTION_BIT_BASE: usize = 263;
const PK_BASE: usize = 270;
const PK_SLACK_BASE: usize = 273;
const PK_CAN_CARRY_BASE: usize = 276;
pub(crate) const ACC_BEFORE_BASE: usize = 278;
const ACC_AFTER_BASE: usize = 281;
const ACC_SLACK_BASE: usize = 284;
const ACC_CAN_CARRY_BASE: usize = 287;
const ARITH_CARRY_SHIFT_BASE: usize = 289;
const PREV_PK_ROOT_BASE: usize = 292;
const NEXT_PK_ROOT_BASE: usize = 300;
const PK_BIT_BASE: usize = 308;
const PK_SLACK_BIT_BASE: usize = 353;
const ACC_AFTER_BIT_BASE: usize = 398;
const ACC_SLACK_BIT_BASE: usize = 443;
const ARITH_CARRY_BIT_BASE: usize = 488;
pub(crate) const TRACE_WIDTH: usize = 515;

#[inline]
const fn qty_sel(order: usize, qty: usize) -> usize {
    QTY_SEL_BASE + 16 * order + qty
}

#[inline]
const fn limb_col(base: usize, limb: usize) -> usize {
    base + limb
}

#[inline]
pub(crate) fn split_15(mut value: u64) -> [u32; 3] {
    core::array::from_fn(|_| {
        let limb = (value & 0x7fff) as u32;
        value >>= 15;
        limb
    })
}

#[inline]
fn set_bits(row: &mut [BabyBear], value: u32, bits: usize, base: usize) {
    for bit in 0..bits {
        row[base + bit] = BabyBear::new((value >> bit) & 1);
    }
}

#[inline]
fn set_limb_bits(row: &mut [BabyBear], limbs: [u32; 3], base: usize) {
    for (limb, value) in limbs.into_iter().enumerate() {
        set_bits(row, value, 15, base + 15 * limb);
    }
}

fn fill_canonical(
    row: &mut [BabyBear],
    value: u64,
    value_base: usize,
    slack_base: usize,
    carry_base: usize,
    value_bit_base: Option<usize>,
    slack_bit_base: usize,
) -> Result<(), String> {
    if value >= MODULUS {
        return Err(format!(
            "BFV residue {value} is noncanonical for modulus {MODULUS}"
        ));
    }
    let limbs = split_15(value);
    let slack = split_15(MODULUS - 1 - value);
    for limb in 0..3 {
        row[value_base + limb] = BabyBear::new(limbs[limb]);
        row[slack_base + limb] = BabyBear::new(slack[limb]);
    }
    if let Some(base) = value_bit_base {
        set_limb_bits(row, limbs, base);
    }
    set_limb_bits(row, slack, slack_bit_base);

    let carry0 = (i128::from(limbs[0]) + i128::from(slack[0]) - MODULUS_MINUS_ONE_LIMBS[0]) / RADIX;
    let carry1 =
        (i128::from(limbs[1]) + i128::from(slack[1]) + carry0 - MODULUS_MINUS_ONE_LIMBS[1]) / RADIX;
    let top = i128::from(limbs[2]) + i128::from(slack[2]) + carry1 - MODULUS_MINUS_ONE_LIMBS[2];
    if !(0..=1).contains(&carry0) || !(0..=1).contains(&carry1) || top != 0 {
        return Err("internal canonical-residue carry construction failed".to_owned());
    }
    row[carry_base] = BabyBear::new(carry0 as u32);
    row[carry_base + 1] = BabyBear::new(carry1 as u32);
    Ok(())
}

/// Public values for the one exact slice.  The first twelve entries are the
/// existing Dark Bazaar statement.  The remaining entries are the all-eight-
/// lane ordered-public-key chain root and the exact ciphertext residue limbs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBookBfvSlicePublic {
    pub book: BookPublicStatement,
    pub public_key_root: [u32; DIGEST_WIDTH],
    pub ciphertext_limbs: [u32; 3],
}

impl PrivateBookBfvSlicePublic {
    pub(crate) fn as_felts(self) -> Result<[BabyBear; 23], String> {
        if self.book.session >= BABYBEAR_P
            || self.book.rule != RULE_ID
            || self.book.p_star as usize >= PRICE_COUNT
            || self.book.v_star > ORDER_COUNT as u32 * u32::from(MAX_QTY)
        {
            return Err("invalid fixed Dark Bazaar public statement".to_owned());
        }
        let mut public = [BabyBear::ZERO; 23];
        public[0] = BabyBear::new(self.book.session);
        public[1] = BabyBear::new(self.book.rule);
        for (lane, value) in self.book.order_root.into_iter().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!("order-root lane {lane} is noncanonical"));
            }
            public[2 + lane] = BabyBear::new(value);
        }
        public[10] = BabyBear::new(self.book.p_star);
        public[11] = BabyBear::new(self.book.v_star);
        for (lane, value) in self.public_key_root.into_iter().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!("public-key-root lane {lane} is noncanonical"));
            }
            public[12 + lane] = BabyBear::new(value);
        }
        for (limb, value) in self.ciphertext_limbs.into_iter().enumerate() {
            if value >= (1 << 15) {
                return Err(format!("ciphertext limb {limb} is not 15-bit"));
            }
            public[20 + limb] = BabyBear::new(value);
        }
        Ok(public)
    }
}

/// Private data needed by the exact coefficient-zero equation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBookBfvSliceOpening {
    /// Natural power-basis public-key coefficients.  The trace performs the
    /// exact coefficient-zero negacyclic reversal/sign schedule itself.
    pub public_key_coefficients: Vec<u64>,
    pub u_coefficients: Vec<i64>,
    pub error_coefficient: i64,
    /// Exact real-encoder lift for the private order selected by the book.
    pub message_coefficient: u64,
    pub ciphertext_coefficient: u64,
}

pub struct PrivateBookBfvSliceProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl PrivateBookBfvSliceProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private-book BFV slice proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private-book BFV slice proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(PRIVATE_BOOK_BFV_SLICE_DESCRIPTOR_JSON)?;
    if descriptor.name != "private-book-bfv-slice-o0-c0-q0-k0::exact-wide-v1"
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != 23
    {
        return Err("private-book BFV slice descriptor shape drifted".to_owned());
    }
    Ok(descriptor)
}

/// Compute the verifier-owned commitment to all 4,096 public-key coefficients
/// in the exact order consumed by the coefficient-zero negacyclic equation.
pub fn public_key_root(coefficients: &[u64]) -> Result<[u32; DIGEST_WIDTH], String> {
    if coefficients.len() != DEGREE {
        return Err(format!(
            "public-key row has {} coefficients, expected {DEGREE}",
            coefficients.len()
        ));
    }
    let mut root = [BabyBear::ZERO; DIGEST_WIDTH];
    for row_index in 0..DEGREE {
        let coefficient_index = if row_index == 0 {
            0
        } else {
            DEGREE - row_index
        };
        let coefficient = coefficients[coefficient_index];
        if coefficient >= MODULUS {
            return Err(format!(
                "public-key coefficient {coefficient_index}={coefficient} is noncanonical"
            ));
        }
        let limbs = split_15(coefficient);
        let mut input = Vec::with_capacity(16);
        input.extend([
            BabyBear::new(PK_CHAIN_DOMAIN),
            BabyBear::new(SLICE_TAG),
            BabyBear::new(row_index as u32),
            BabyBear::new(limbs[0]),
            BabyBear::new(limbs[1]),
            BabyBear::new(limbs[2]),
        ]);
        input.extend(root);
        input.extend([BabyBear::ZERO; 2]);
        root = chip_absorb_all_lanes(input.len(), &input);
    }
    Ok(root.map(BabyBear::as_u32))
}

pub(crate) fn build_trace(
    session: u32,
    book: &PrivateBookWitness,
    opening: &PrivateBookBfvSliceOpening,
) -> Result<(Vec<Vec<BabyBear>>, PrivateBookBfvSlicePublic), String> {
    if opening.public_key_coefficients.len() != DEGREE || opening.u_coefficients.len() != DEGREE {
        return Err(format!(
            "slice vectors must both have degree {DEGREE} (pk={}, u={})",
            opening.public_key_coefficients.len(),
            opening.u_coefficients.len()
        ));
    }
    if !(-32..=31).contains(&opening.error_coefficient) {
        return Err("error coefficient is outside the proved signed six-bit range".to_owned());
    }
    if opening.message_coefficient >= MODULUS || opening.ciphertext_coefficient >= MODULUS {
        return Err("message/ciphertext coefficient is noncanonical".to_owned());
    }

    let (book_row, book_public) = build_row(session, book)?;
    let mut rows = Vec::with_capacity(DEGREE);
    let mut accumulator = 0u64;
    let mut previous_root = [BabyBear::ZERO; DIGEST_WIDTH];

    for row_index in 0..DEGREE {
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        row[..DB_TRACE_WIDTH].copy_from_slice(&book_row);
        for (order_index, order) in book.orders.iter().enumerate() {
            row[qty_sel(order_index, usize::from(order.qty))] = BabyBear::ONE;
        }

        let is_last = row_index + 1 == DEGREE;
        row[NEG] = BabyBear::new(u32::from(row_index != 0));
        row[LAST] = BabyBear::new(u32::from(is_last));
        row[INDEX] = BabyBear::new(row_index as u32);

        let u = opening.u_coefficients[row_index];
        if !(-32..=31).contains(&u) {
            return Err(format!(
                "u[{row_index}]={u} is outside signed six-bit range"
            ));
        }
        let u_shift = u + 32;
        row[U_SHIFT] = BabyBear::new(u_shift as u32);
        set_bits(&mut row, u_shift as u32, 6, U_BIT_BASE);
        let error_shift = opening.error_coefficient + 32;
        row[ERROR_SHIFT] = BabyBear::new(error_shift as u32);
        set_bits(&mut row, error_shift as u32, 6, ERROR_BIT_BASE);

        let coefficient_index = if row_index == 0 {
            0
        } else {
            DEGREE - row_index
        };
        let pk = opening.public_key_coefficients[coefficient_index];
        fill_canonical(
            &mut row,
            pk,
            PK_BASE,
            PK_SLACK_BASE,
            PK_CAN_CARRY_BASE,
            Some(PK_BIT_BASE),
            PK_SLACK_BIT_BASE,
        )?;

        let before_limbs = split_15(accumulator);
        for limb in 0..3 {
            row[limb_col(ACC_BEFORE_BASE, limb)] = BabyBear::new(before_limbs[limb]);
        }
        let effective_u = i128::from(u) * if row_index == 0 { 1 } else { -1 };
        let terminal = if is_last {
            i128::from(opening.error_coefficient) + i128::from(opening.message_coefficient)
        } else {
            0
        };
        let unreduced = i128::from(accumulator) + effective_u * i128::from(pk) + terminal;
        let after = unreduced.rem_euclid(i128::from(MODULUS)) as u64;
        let reduction = (unreduced - i128::from(after)) / i128::from(MODULUS);
        if !(-64..=63).contains(&reduction) {
            return Err(format!(
                "row {row_index} quotient {reduction} exceeds seven bits"
            ));
        }
        let reduction_shift = reduction + 64;
        row[REDUCTION_SHIFT] = BabyBear::new(reduction_shift as u32);
        set_bits(&mut row, reduction_shift as u32, 7, REDUCTION_BIT_BASE);
        fill_canonical(
            &mut row,
            after,
            ACC_AFTER_BASE,
            ACC_SLACK_BASE,
            ACC_CAN_CARRY_BASE,
            Some(ACC_AFTER_BIT_BASE),
            ACC_SLACK_BIT_BASE,
        )?;

        let after_limbs = split_15(after);
        let message_limbs = split_15(opening.message_coefficient);
        let pk_limbs = split_15(pk);
        let mut carry_in = 0i128;
        for limb in 0..3 {
            let terminal_limb = if is_last {
                i128::from(message_limbs[limb])
                    + if limb == 0 {
                        i128::from(opening.error_coefficient)
                    } else {
                        0
                    }
            } else {
                0
            };
            let raw = i128::from(before_limbs[limb]) + effective_u * i128::from(pk_limbs[limb])
                - reduction * MODULUS_LIMBS[limb]
                + carry_in
                + terminal_limb
                - i128::from(after_limbs[limb]);
            if raw % RADIX != 0 {
                return Err(format!(
                    "row {row_index} limb {limb} has a nonintegral carry"
                ));
            }
            let carry_out = raw / RADIX;
            if !(-256..=255).contains(&carry_out) {
                return Err(format!(
                    "row {row_index} limb {limb} carry {carry_out} exceeds signed nine bits"
                ));
            }
            let shifted = carry_out + 256;
            row[ARITH_CARRY_SHIFT_BASE + limb] = BabyBear::new(shifted as u32);
            set_bits(&mut row, shifted as u32, 9, ARITH_CARRY_BIT_BASE + 9 * limb);
            carry_in = carry_out;
        }
        if carry_in != 0 {
            return Err(format!("row {row_index} left top carry {carry_in}"));
        }

        for lane in 0..DIGEST_WIDTH {
            row[PREV_PK_ROOT_BASE + lane] = previous_root[lane];
        }
        let mut root_input = Vec::with_capacity(16);
        root_input.extend([
            BabyBear::new(PK_CHAIN_DOMAIN),
            BabyBear::new(SLICE_TAG),
            BabyBear::new(row_index as u32),
            BabyBear::new(pk_limbs[0]),
            BabyBear::new(pk_limbs[1]),
            BabyBear::new(pk_limbs[2]),
        ]);
        root_input.extend(previous_root);
        root_input.extend([BabyBear::ZERO; 2]);
        let next_root = chip_absorb_all_lanes(root_input.len(), &root_input);
        for lane in 0..DIGEST_WIDTH {
            row[NEXT_PK_ROOT_BASE + lane] = next_root[lane];
        }
        previous_root = next_root;
        accumulator = after;
        rows.push(row);
    }

    if accumulator != opening.ciphertext_coefficient {
        return Err(format!(
            "exact slice opening produced coefficient {accumulator}, public ciphertext has {}",
            opening.ciphertext_coefficient
        ));
    }
    let public = PrivateBookBfvSlicePublic {
        book: book_public,
        public_key_root: previous_root.map(BabyBear::as_u32),
        ciphertext_limbs: split_15(opening.ciphertext_coefficient),
    };
    Ok((rows, public))
}

/// Run the deployed row-local AIR evaluator over an exact slice witness and
/// report the first rejected emitted constraint and row.  This is intentionally
/// separate from proving: it is a deterministic diagnostic for descriptor /
/// witness drift and does not replace the batch verifier or its lookup buses.
#[doc(hidden)]
pub fn audit_row_local_constraints(
    session: u32,
    book: &PrivateBookWitness,
    opening: &PrivateBookBfvSliceOpening,
) -> Result<(), String> {
    let (trace, public) = build_trace(session, book, opening)?;
    let desc = descriptor()?;
    let p3_trace = trace
        .iter()
        .map(|row| {
            row.iter()
                .map(|value| P3BabyBear::from_u32(value.as_u32()))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let p3_public = public
        .as_felts()?
        .into_iter()
        .map(|value| P3BabyBear::from_u32(value.as_u32()))
        .collect::<Vec<_>>();
    if ir2_eval_accepts(&desc, &p3_trace, &p3_public) {
        return Ok(());
    }

    // Assertions do not cancel one another. Binary isolation therefore finds
    // the first failing emitted assertion in O(log constraints) evaluator
    // passes without weakening or reimplementing its polynomial semantics.
    let mut lo = 0usize;
    let mut hi = desc.constraints.len();
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        let mut left = desc.clone();
        left.constraints = desc.constraints[lo..mid].to_vec();
        if ir2_eval_accepts(&left, &p3_trace, &p3_public) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let index = lo;
    let constraint = &desc.constraints[index];
    let mut isolated = desc.clone();
    isolated.constraints = vec![constraint.clone()];
    let row = match constraint {
        VmConstraint2::Base(VmConstraint::Gate(_)) => (0..p3_trace.len() - 1).find(|&row| {
            !ir2_eval_accepts(
                &isolated,
                &[p3_trace[row].clone(), p3_trace[row].clone()],
                &p3_public,
            )
        }),
        VmConstraint2::Base(VmConstraint::Transition { .. })
        | VmConstraint2::WindowGate(dregg_circuit::descriptor_ir2::WindowGateSpec {
            on_transition: true,
            ..
        }) => (0..p3_trace.len() - 1).find(|&row| {
            !ir2_eval_accepts(
                &isolated,
                &[p3_trace[row].clone(), p3_trace[row + 1].clone()],
                &p3_public,
            )
        }),
        VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::First, ..
        })
        | VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First, ..
        }) => Some(0),
        VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::Last, ..
        })
        | VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::Last, ..
        }) => Some(p3_trace.len() - 1),
        _ => None,
    };
    Err(format!(
        "deployed row-local evaluator rejected emitted constraint {index} at row {row:?} ({})",
        match constraint {
            VmConstraint2::Base(VmConstraint::Gate(_)) => "gate",
            VmConstraint2::Base(VmConstraint::Transition { .. }) => "transition",
            VmConstraint2::Base(VmConstraint::Boundary { .. }) => "boundary",
            VmConstraint2::Base(VmConstraint::PiBinding { .. }) => "pi-binding",
            VmConstraint2::WindowGate(_) => "window-gate",
            VmConstraint2::Lookup(_) => "lookup",
            VmConstraint2::MemOp(_) => "mem-op",
            VmConstraint2::MapOp(_) => "map-op",
            VmConstraint2::UMemOp(_) => "umem-op",
            VmConstraint2::ProofBind(_) => "proof-bind",
        }
    ))
}

pub fn prove_zk(
    session: u32,
    book: &PrivateBookWitness,
    opening: &PrivateBookBfvSliceOpening,
) -> Result<(PrivateBookBfvSliceProof, PrivateBookBfvSlicePublic), String> {
    let (trace, public) = build_trace(session, book, opening)?;
    let config = create_zk_config();
    let proof = prove_vm_descriptor2_for_config(
        &descriptor()?,
        &trace,
        &public.as_felts()?,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )?;
    Ok((PrivateBookBfvSliceProof { proof }, public))
}

pub fn verify_zk(
    proof: &PrivateBookBfvSliceProof,
    public: PrivateBookBfvSlicePublic,
) -> Result<(), String> {
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(&descriptor()?, &proof.proof, &public.as_felts()?, &config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dark_bazaar_private::PrivateOrder;

    fn book() -> PrivateBookWitness {
        PrivateBookWitness::try_from_orders_with_blinding(
            &[
                PrivateOrder::bid(10, 2),
                PrivateOrder::bid(6, 1),
                PrivateOrder::ask(5, 0),
                PrivateOrder::ask(8, 1),
            ],
            core::array::from_fn(|lane| 17_000 + lane as u32),
        )
        .expect("private book")
    }

    #[test]
    fn exact_integer_witness_has_all_local_teeth() {
        assert_eq!(PRODUCTION_EQUATION_COUNT, 98_304);
        assert_eq!(REMAINING_EQUATION_COUNT, 98_303);
        let mut pk = vec![0u64; DEGREE];
        pk[0] = 17;
        pk[1] = MODULUS - 3;
        pk[DEGREE - 1] = 29;
        let mut u = vec![0i64; DEGREE];
        u[0] = 2;
        u[1] = -3;
        // The message is NOT free: the Lean-emitted last-row limb gates derive it IN-AIR from
        // the book's order-0 `(kind, quantity)` one-hots (columns 21..28 x the qty selectors),
        // so only the deployed table entry satisfies the descriptor.  `book()`'s order 0 is
        // `bid(qty = 10, limit = 2)`, i.e. `kind = 2`, so this is `MESSAGE_COEFF0[2 * 16 + 10]`
        // — the same constant `fused::tests::fixture` already carries for the same book.  It was
        // `0` here, which no book satisfies: `build_trace` does not bind the message to the book,
        // so the trace assembled fine and only the AIR rejected it (constraint 1258, row 4095).
        let message = 34_437_628_850;
        let error = 5;
        let mut coefficient = 0i128;
        for i in 0..DEGREE {
            let j = if i == 0 { 0 } else { DEGREE - i };
            coefficient += i128::from(u[i]) * i128::from(pk[j]) * if i == 0 { 1 } else { -1 };
        }
        coefficient += i128::from(error) + i128::from(message);
        let ciphertext = coefficient.rem_euclid(i128::from(MODULUS)) as u64;
        let opening = PrivateBookBfvSliceOpening {
            public_key_coefficients: pk,
            u_coefficients: u,
            error_coefficient: error,
            message_coefficient: message,
            ciphertext_coefficient: ciphertext,
        };
        let (trace, public) = build_trace(0xDBA2, &book(), &opening).expect("exact trace");
        assert_eq!(trace.len(), DEGREE);
        assert_eq!(
            public.public_key_root,
            public_key_root(&opening.public_key_coefficients).unwrap()
        );
        assert_eq!(public.ciphertext_limbs, split_15(ciphertext));

        audit_row_local_constraints(0xDBA2, &book(), &opening)
            .expect("deployed row-local evaluator");

        let mut wrong_pk = opening.clone();
        wrong_pk.public_key_coefficients[0] += 1;
        assert!(build_trace(0xDBA2, &book(), &wrong_pk).is_err());

        let mut wrong_u = opening.clone();
        wrong_u.u_coefficients[0] += 1;
        assert!(build_trace(0xDBA2, &book(), &wrong_u).is_err());

        let mut wrong_error = opening.clone();
        wrong_error.error_coefficient += 1;
        assert!(build_trace(0xDBA2, &book(), &wrong_error).is_err());

        let mut wrong_message = opening.clone();
        wrong_message.message_coefficient += 1;
        assert!(build_trace(0xDBA2, &book(), &wrong_message).is_err());

        let mut wrong_ciphertext = opening;
        wrong_ciphertext.ciphertext_coefficient = (ciphertext + 1) % MODULUS;
        assert!(build_trace(0xDBA2, &book(), &wrong_ciphertext).is_err());
    }
}
