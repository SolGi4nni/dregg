//! One-proof private weld for the first production BFV terminal coordinate.
//!
//! The public q0 butterfly carrier in the parent module cannot authenticate a
//! hidden terminal product: making its rows verifier-visible would reveal the
//! product, while hashing the public rows beside an independently supplied
//! product proves no same opening.  This module takes the smallest honest cut.
//! It fuses the existing Lean-authored 4,096-term exact slice
//! `(order=0, ciphertext=0, modulus=0, coefficient=0)` and the Lean-authored
//! threshold terminal into one HidingFRI trace.  A last-row radix-2^15 limb/carry
//! gate binds the terminal's private radix-2^14 product to the exact
//! negacyclic-convolution coefficient computed from the *same* private `u`
//! opening and committed public-key row.
//!
//! The verifier supplies session, party, DKG commitment, collective-key root,
//! and the typed coordinate as ordinary public fields.  No compressing context
//! hash is treated as injective.  The collective-key root is the exact eight
//! lanes already opened by the slice's in-proof key chain; the terminal context
//! columns are pinned to those same PI slots.  Privacy rests on the pinned
//! HidingFRI configuration.  Public-key opening authority rests on the deployed
//! Poseidon2 commitment's collision resistance.  This first cut is one exact
//! coordinate, not the complete 98,304-equation NTT-family proof.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, LookupSpec, MemBoundaryWitness, UMemBoundaryWitness,
    VmConstraint2, WindowExpr, WindowGateSpec, ir2_eval_accepts, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::private_book_bfv_tables::ThresholdDecryptTerminalRow;
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;

use crate::dark_bazaar_private::PrivateBookWitness;
use crate::private_book_bfv_slice::{
    self as slice, ACC_BEFORE_BASE, DEGREE, MODULUS, PrivateBookBfvSliceOpening,
    PrivateBookBfvSlicePublic,
};

use super::{
    BfvThresholdTerminalPublic, TRACE_WIDTH as TERMINAL_WIDTH, decode_limbs,
    descriptor as terminal_descriptor, trace_and_public, validate_hiding_proof_shape,
};

const SLICE_PI_COUNT: usize = 23;
const LAMBDA_PI_BASE: usize = SLICE_PI_COUNT;
const H_PI_BASE: usize = LAMBDA_PI_BASE + 3;
const PARTY_PI: usize = H_PI_BASE + 3;
const DKG_PI_BASE: usize = PARTY_PI + 1;
const COORDINATE_PI_BASE: usize = DKG_PI_BASE + 8;
pub const PUBLIC_INPUT_COUNT: usize = COORDINATE_PI_BASE + 4;

const TERMINAL_BASE: usize = slice::TRACE_WIDTH;
const AUX_BASE: usize = TERMINAL_BASE + TERMINAL_WIDTH;

// Last-row product-weld auxiliary columns, relative to AUX_BASE.
const PRODUCT15: usize = 0;
const PRODUCT_BITS: usize = PRODUCT15 + 3;
const PRODUCT_BIT_COUNT: usize = 42;
const REDUCTION_SHIFT: usize = PRODUCT_BITS + PRODUCT_BIT_COUNT;
const REDUCTION_BITS: usize = REDUCTION_SHIFT + 1;
const CARRY_SHIFT: usize = REDUCTION_BITS + 7;
const CARRY_BITS: usize = CARRY_SHIFT + 3;
const AUX_WIDTH: usize = CARRY_BITS + 27;

const DOMAIN_BASE: usize = AUX_BASE + AUX_WIDTH;
const DOMAIN_PARTY: usize = DOMAIN_BASE;
const DOMAIN_DKG: usize = DOMAIN_PARTY + 1;
const DOMAIN_COORDINATE: usize = DOMAIN_DKG + 8;
pub const TRACE_WIDTH: usize = DOMAIN_COORDINATE + 4;

const TERMINAL_LAMBDA: usize = TERMINAL_BASE;
const TERMINAL_PRODUCT: usize = TERMINAL_BASE + 3;
const TERMINAL_H: usize = TERMINAL_BASE + 6;
const TERMINAL_CONTEXT: usize = TERMINAL_BASE + 40;

const RADIX15: i128 = 1 << 15;
const MODULUS_LIMBS15: [i128; 3] = [24_577, 32_765, 63];

/// The only coordinate materialized by this first fused executable cut.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BfvTerminalCoordinate {
    pub order: u32,
    pub ciphertext: u32,
    pub modulus: u32,
    pub coefficient: u32,
}

impl BfvTerminalCoordinate {
    pub const O0_C0_Q0_K0: Self = Self {
        order: 0,
        ciphertext: 0,
        modulus: 0,
        coefficient: 0,
    };

    const fn as_u32s(self) -> [u32; 4] {
        [self.order, self.ciphertext, self.modulus, self.coefficient]
    }
}

/// Exact deployment identity not already present in the slice statement.
/// Session is `slice.book.session`; the collective-key commitment is
/// `slice.public_key_root`.  Keeping those fields single-source prevents a
/// detached duplicate from acquiring authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BfvTerminalDomain {
    pub party: u32,
    pub dkg_commitment: [u32; 8],
}

/// Complete public statement of the fused relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BfvTerminalFusedPublic {
    pub slice: PrivateBookBfvSlicePublic,
    pub lambda: [u32; 3],
    pub h: [u32; 3],
    pub domain: BfvTerminalDomain,
    pub coordinate: BfvTerminalCoordinate,
}

impl BfvTerminalFusedPublic {
    fn as_felts(self) -> Result<[BabyBear; PUBLIC_INPUT_COUNT], String> {
        if self.domain.party >= BABYBEAR_P {
            return Err("BFV terminal party is noncanonical for BabyBear".to_owned());
        }
        for (lane, value) in self.domain.dkg_commitment.iter().copied().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "BFV terminal DKG commitment lane {lane} is noncanonical for BabyBear"
                ));
            }
        }
        if self.coordinate != BfvTerminalCoordinate::O0_C0_Q0_K0 {
            return Err("unsupported BFV terminal coordinate (expected o0/c0/q0/k0)".to_owned());
        }
        // Reuse the terminal's strict canonical q0 decoding.  Context is the
        // exact slice public-key root, not a separately hashed metadata packet.
        BfvThresholdTerminalPublic {
            lambda: self.lambda,
            h: self.h,
            carrier_context: self.slice.public_key_root,
        }
        .as_felts()?;

        let mut public = [BabyBear::ZERO; PUBLIC_INPUT_COUNT];
        public[..SLICE_PI_COUNT].copy_from_slice(&self.slice.as_felts()?);
        public[LAMBDA_PI_BASE..LAMBDA_PI_BASE + 3].copy_from_slice(&self.lambda.map(BabyBear::new));
        public[H_PI_BASE..H_PI_BASE + 3].copy_from_slice(&self.h.map(BabyBear::new));
        public[PARTY_PI] = BabyBear::new(self.domain.party);
        for (lane, value) in self.domain.dkg_commitment.into_iter().enumerate() {
            public[DKG_PI_BASE + lane] = BabyBear::new(value);
        }
        for (lane, value) in self.coordinate.as_u32s().into_iter().enumerate() {
            public[COORDINATE_PI_BASE + lane] = BabyBear::new(value);
        }
        Ok(public)
    }
}

/// Opaque fused proof.  Decode refuses a non-hiding proof shape and trailing
/// bytes before the verifier sees it.
pub struct BfvTerminalFusedProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl BfvTerminalFusedProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("fused BFV terminal proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let (proof, trailing) =
            postcard::take_from_bytes::<Ir2BatchProof<DreggZkStarkConfig>>(bytes)
                .map_err(|error| format!("fused BFV terminal proof decode failed: {error}"))?;
        if !trailing.is_empty() {
            return Err(format!(
                "fused BFV terminal proof has {} trailing bytes",
                trailing.len()
            ));
        }
        validate_hiding_proof_shape(&proof)?;
        Ok(Self { proof })
    }
}

fn shift_expr(expression: &LeanExpr, by: usize) -> LeanExpr {
    match expression {
        LeanExpr::Var(column) => LeanExpr::Var(column + by),
        LeanExpr::Const(value) => LeanExpr::Const(*value),
        LeanExpr::Add(left, right) => LeanExpr::add(shift_expr(left, by), shift_expr(right, by)),
        LeanExpr::Mul(left, right) => LeanExpr::mul(shift_expr(left, by), shift_expr(right, by)),
    }
}

fn shifted_terminal_constraint(
    constraint: &VmConstraint2,
) -> Result<Option<VmConstraint2>, String> {
    let shifted = match constraint {
        VmConstraint2::Base(VmConstraint::Gate(body)) => {
            VmConstraint2::Base(VmConstraint::Gate(shift_expr(body, TERMINAL_BASE)))
        }
        VmConstraint2::Base(VmConstraint::Boundary { row, body }) => {
            VmConstraint2::Base(VmConstraint::Boundary {
                row: *row,
                body: shift_expr(body, TERMINAL_BASE),
            })
        }
        // Replaced below: λ/h bind to new fused PIs and the eight context
        // columns bind directly to the slice key-root PI slots.
        VmConstraint2::Base(VmConstraint::PiBinding { .. }) => return Ok(None),
        VmConstraint2::Lookup(lookup) => VmConstraint2::Lookup(LookupSpec {
            table: lookup.table,
            tuple: lookup
                .tuple
                .iter()
                .map(|expression| shift_expr(expression, TERMINAL_BASE))
                .collect(),
        }),
        VmConstraint2::Base(VmConstraint::Transition { hi, lo }) => {
            VmConstraint2::Base(VmConstraint::Transition {
                hi: hi + TERMINAL_BASE,
                lo: lo + TERMINAL_BASE,
            })
        }
        VmConstraint2::WindowGate(window) => VmConstraint2::WindowGate(WindowGateSpec {
            body: shift_window_expr(&window.body, TERMINAL_BASE),
            on_transition: window.on_transition,
        }),
        VmConstraint2::MemOp(_)
        | VmConstraint2::MapOp(_)
        | VmConstraint2::UMemOp(_)
        | VmConstraint2::ProofBind(_) => {
            return Err(
                "terminal descriptor acquired an unsupported stateful constraint".to_owned(),
            );
        }
    };
    Ok(Some(shifted))
}

fn shift_window_expr(expression: &WindowExpr, by: usize) -> WindowExpr {
    match expression {
        WindowExpr::Loc(column) => WindowExpr::Loc(column + by),
        WindowExpr::Nxt(column) => WindowExpr::Nxt(column + by),
        WindowExpr::Const(value) => WindowExpr::Const(*value),
        WindowExpr::Add(left, right) => WindowExpr::Add(
            Box::new(shift_window_expr(left, by)),
            Box::new(shift_window_expr(right, by)),
        ),
        WindowExpr::Mul(left, right) => WindowExpr::Mul(
            Box::new(shift_window_expr(left, by)),
            Box::new(shift_window_expr(right, by)),
        ),
    }
}

fn constant(value: i64) -> LeanExpr {
    LeanExpr::constant(value)
}

fn var(column: usize) -> LeanExpr {
    LeanExpr::var(column)
}

fn add(left: LeanExpr, right: LeanExpr) -> LeanExpr {
    LeanExpr::add(left, right)
}

fn mul(left: LeanExpr, right: LeanExpr) -> LeanExpr {
    LeanExpr::mul(left, right)
}

fn neg(value: LeanExpr) -> LeanExpr {
    mul(constant(-1), value)
}

fn sub(left: LeanExpr, right: LeanExpr) -> LeanExpr {
    add(left, neg(right))
}

fn sum(expressions: impl IntoIterator<Item = LeanExpr>) -> LeanExpr {
    expressions.into_iter().fold(constant(0), add)
}

fn boundary_last(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::Last,
        body,
    })
}

fn append_bits(
    constraints: &mut Vec<VmConstraint2>,
    value_column: usize,
    bit_base: usize,
    bit_count: usize,
) {
    constraints.push(boundary_last(sub(
        sum((0..bit_count).map(|bit| mul(constant(1i64 << bit), var(bit_base + bit)))),
        var(value_column),
    )));
    for bit in 0..bit_count {
        constraints.push(boundary_last(mul(
            var(bit_base + bit),
            sub(var(bit_base + bit), constant(1)),
        )));
    }
}

fn append_product_weld(constraints: &mut Vec<VmConstraint2>) {
    // One canonical bit opening feeds both radix representations.  Therefore
    // the terminal product cannot exploit a mixed-radix field alias.
    for bit in 0..PRODUCT_BIT_COUNT {
        constraints.push(boundary_last(mul(
            var(AUX_BASE + PRODUCT_BITS + bit),
            sub(var(AUX_BASE + PRODUCT_BITS + bit), constant(1)),
        )));
    }
    for limb in 0..3 {
        let start = 15 * limb;
        let count = PRODUCT_BIT_COUNT.saturating_sub(start).min(15);
        constraints.push(boundary_last(sub(
            sum((0..count).map(|bit| {
                mul(
                    constant(1i64 << bit),
                    var(AUX_BASE + PRODUCT_BITS + start + bit),
                )
            })),
            var(AUX_BASE + PRODUCT15 + limb),
        )));
    }
    for limb in 0..3 {
        let start = 14 * limb;
        constraints.push(boundary_last(sub(
            sum((0..14).map(|bit| {
                mul(
                    constant(1i64 << bit),
                    var(AUX_BASE + PRODUCT_BITS + start + bit),
                )
            })),
            var(TERMINAL_PRODUCT + limb),
        )));
    }

    append_bits(
        constraints,
        AUX_BASE + REDUCTION_SHIFT,
        AUX_BASE + REDUCTION_BITS,
        7,
    );
    for limb in 0..3 {
        append_bits(
            constraints,
            AUX_BASE + CARRY_SHIFT + limb,
            AUX_BASE + CARRY_BITS + 9 * limb,
            9,
        );
    }

    let effective_u = sub(constant(32), var(slice_u_shift()));
    let reduction = sub(var(AUX_BASE + REDUCTION_SHIFT), constant(64));
    for limb in 0..3 {
        let carry_in = if limb == 0 {
            constant(0)
        } else {
            sub(var(AUX_BASE + CARRY_SHIFT + limb - 1), constant(256))
        };
        let carry_out = sub(var(AUX_BASE + CARRY_SHIFT + limb), constant(256));
        constraints.push(boundary_last(sum([
            var(ACC_BEFORE_BASE + limb),
            mul(effective_u.clone(), var(slice_pk_base() + limb)),
            neg(mul(
                reduction.clone(),
                constant(MODULUS_LIMBS15[limb] as i64),
            )),
            carry_in,
            neg(var(AUX_BASE + PRODUCT15 + limb)),
            neg(mul(constant(RADIX15 as i64), carry_out)),
        ])));
    }
    constraints.push(boundary_last(sub(
        var(AUX_BASE + CARRY_SHIFT + 2),
        constant(256),
    )));
}

// Kept as functions so the constants remain visibly tied to the Lean slice
// layout without making its entire internal column inventory public API.
const fn slice_u_shift() -> usize {
    248
}

const fn slice_pk_base() -> usize {
    270
}

/// Deterministic fused descriptor.  It composes two Lean-emitted descriptors
/// and adds only the explicit last-row product/domain weld described above.
pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let slice_descriptor = slice::descriptor()?;
    let terminal_descriptor = terminal_descriptor()?;
    if slice_descriptor.trace_width != slice::TRACE_WIDTH
        || slice_descriptor.public_input_count != SLICE_PI_COUNT
        || !slice_descriptor.tables.is_empty()
        || !slice_descriptor.hash_sites.is_empty()
        || !slice_descriptor.ranges.is_empty()
        || !terminal_descriptor.hash_sites.is_empty()
        || !terminal_descriptor.ranges.is_empty()
    {
        return Err("BFV fused input descriptor ABI drifted".to_owned());
    }

    let mut constraints = slice_descriptor.constraints;
    for constraint in &terminal_descriptor.constraints {
        if let Some(shifted) = shifted_terminal_constraint(constraint)? {
            constraints.push(shifted);
        }
    }
    for lane in 0..3 {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::Last,
            col: TERMINAL_LAMBDA + lane,
            pi_index: LAMBDA_PI_BASE + lane,
        }));
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::Last,
            col: TERMINAL_H + lane,
            pi_index: H_PI_BASE + lane,
        }));
    }
    for lane in 0..8 {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::Last,
            col: TERMINAL_CONTEXT + lane,
            pi_index: 12 + lane,
        }));
    }

    append_product_weld(&mut constraints);

    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::Last,
        col: DOMAIN_PARTY,
        pi_index: PARTY_PI,
    }));
    for lane in 0..8 {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::Last,
            col: DOMAIN_DKG + lane,
            pi_index: DKG_PI_BASE + lane,
        }));
    }
    for lane in 0..4 {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::Last,
            col: DOMAIN_COORDINATE + lane,
            pi_index: COORDINATE_PI_BASE + lane,
        }));
        constraints.push(boundary_last(var(DOMAIN_COORDINATE + lane)));
    }

    Ok(EffectVmDescriptor2 {
        name: "private-book-bfv-terminal-fused-o0-c0-q0-k0::exact-private-v1".to_owned(),
        trace_width: TRACE_WIDTH,
        public_input_count: PUBLIC_INPUT_COUNT,
        tables: terminal_descriptor.tables,
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    })
}

fn exact_private_product(opening: &PrivateBookBfvSliceOpening) -> Result<u64, String> {
    if opening.public_key_coefficients.len() != DEGREE || opening.u_coefficients.len() != DEGREE {
        return Err("fused BFV product opening has the wrong production degree".to_owned());
    }
    let mut product = 0i128;
    for index in 0..DEGREE {
        let key_index = if index == 0 { 0 } else { DEGREE - index };
        let sign = if index == 0 { 1 } else { -1 };
        product += i128::from(opening.u_coefficients[index])
            * i128::from(opening.public_key_coefficients[key_index])
            * sign;
    }
    Ok(product.rem_euclid(i128::from(MODULUS)) as u64)
}

fn fill_bits(row: &mut [BabyBear], value: u32, bit_base: usize, bit_count: usize) {
    for bit in 0..bit_count {
        row[bit_base + bit] = BabyBear::new((value >> bit) & 1);
    }
}

fn build_trace(
    session: u32,
    book: &PrivateBookWitness,
    opening: &PrivateBookBfvSliceOpening,
    terminal: &ThresholdDecryptTerminalRow,
    domain: BfvTerminalDomain,
    coordinate: BfvTerminalCoordinate,
) -> Result<(Vec<Vec<BabyBear>>, BfvTerminalFusedPublic), String> {
    if coordinate != BfvTerminalCoordinate::O0_C0_Q0_K0 {
        return Err("unsupported BFV terminal coordinate (expected o0/c0/q0/k0)".to_owned());
    }
    let (mut trace, slice_public) = slice::build_trace(session, book, opening)?;
    let (terminal_trace, terminal_public) =
        trace_and_public(terminal, slice_public.public_key_root)?;
    let terminal_row = terminal_trace
        .into_iter()
        .next()
        .ok_or_else(|| "terminal trace unexpectedly empty".to_owned())?;

    let product = exact_private_product(opening)?;
    if decode_limbs(&terminal.product)? != u128::from(product) {
        return Err("terminal product differs from the exact private slice coefficient".to_owned());
    }

    let last = DEGREE - 1;
    let before = u64::from(trace[last][ACC_BEFORE_BASE].as_u32())
        + (u64::from(trace[last][ACC_BEFORE_BASE + 1].as_u32()) << 15)
        + (u64::from(trace[last][ACC_BEFORE_BASE + 2].as_u32()) << 30);
    let effective_u = -i128::from(opening.u_coefficients[last]);
    let key = opening.public_key_coefficients[1];
    let unreduced = i128::from(before) + effective_u * i128::from(key);
    let reduction = (unreduced - i128::from(product)) / i128::from(MODULUS);
    if unreduced - i128::from(product) != reduction * i128::from(MODULUS)
        || !(-64..=63).contains(&reduction)
    {
        return Err(
            "fused BFV product reduction is not the exact signed seven-bit quotient".to_owned(),
        );
    }

    for row in &mut trace {
        row.reserve(TERMINAL_WIDTH + AUX_WIDTH + 13);
        row.extend_from_slice(&terminal_row);
        row.extend((0..AUX_WIDTH).map(|_| BabyBear::ZERO));
        row.push(BabyBear::new(domain.party));
        row.extend(domain.dkg_commitment.map(BabyBear::new));
        row.extend(coordinate.as_u32s().map(BabyBear::new));
    }

    let row = &mut trace[last];
    let product15 = slice::split_15(product);
    for (limb, value) in product15.into_iter().enumerate() {
        row[AUX_BASE + PRODUCT15 + limb] = BabyBear::new(value);
    }
    for bit in 0..PRODUCT_BIT_COUNT {
        row[AUX_BASE + PRODUCT_BITS + bit] = BabyBear::new(((product >> bit) & 1) as u32);
    }
    let reduction_shift = (reduction + 64) as u32;
    row[AUX_BASE + REDUCTION_SHIFT] = BabyBear::new(reduction_shift);
    fill_bits(row, reduction_shift, AUX_BASE + REDUCTION_BITS, 7);

    let before_limbs = slice::split_15(before);
    let key_limbs = slice::split_15(key);
    let mut carry_in = 0i128;
    for limb in 0..3 {
        let raw = i128::from(before_limbs[limb]) + effective_u * i128::from(key_limbs[limb])
            - reduction * MODULUS_LIMBS15[limb]
            + carry_in
            - i128::from(product15[limb]);
        if raw % RADIX15 != 0 {
            return Err(format!("fused BFV product carry {limb} is not integral"));
        }
        let carry_out = raw / RADIX15;
        if !(-256..=255).contains(&carry_out) {
            return Err(format!(
                "fused BFV product carry {limb} exceeds signed nine bits"
            ));
        }
        let shifted = (carry_out + 256) as u32;
        row[AUX_BASE + CARRY_SHIFT + limb] = BabyBear::new(shifted);
        fill_bits(row, shifted, AUX_BASE + CARRY_BITS + 9 * limb, 9);
        carry_in = carry_out;
    }
    if carry_in != 0 {
        return Err("fused BFV product top carry does not close".to_owned());
    }

    let public = BfvTerminalFusedPublic {
        slice: slice_public,
        lambda: terminal_public.lambda,
        h: terminal_public.h,
        domain,
        coordinate,
    };
    public.as_felts()?;
    Ok((trace, public))
}

/// Deterministic row-local audit of the exact fused relation.  This is a
/// diagnostic/tooth, not a replacement for HidingFRI verification.
pub fn audit_fused_relation(
    session: u32,
    book: &PrivateBookWitness,
    opening: &PrivateBookBfvSliceOpening,
    terminal: &ThresholdDecryptTerminalRow,
    domain: BfvTerminalDomain,
) -> Result<BfvTerminalFusedPublic, String> {
    let (trace, public) = build_trace(
        session,
        book,
        opening,
        terminal,
        domain,
        BfvTerminalCoordinate::O0_C0_Q0_K0,
    )?;
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
    if !ir2_eval_accepts(&descriptor()?, &p3_trace, &p3_public) {
        return Err("fused BFV terminal row-local evaluator refused honest witness".to_owned());
    }
    Ok(public)
}

/// Mint one privacy-preserving product-bound terminal proof.  No public
/// transform rows or hidden product leave this call.
pub fn prove_zk(
    session: u32,
    book: &PrivateBookWitness,
    opening: &PrivateBookBfvSliceOpening,
    terminal: &ThresholdDecryptTerminalRow,
    domain: BfvTerminalDomain,
) -> Result<(BfvTerminalFusedProof, BfvTerminalFusedPublic), String> {
    let (trace, public) = build_trace(
        session,
        book,
        opening,
        terminal,
        domain,
        BfvTerminalCoordinate::O0_C0_Q0_K0,
    )?;
    let proof = prove_vm_descriptor2_for_config(
        &descriptor()?,
        &trace,
        &public.as_felts()?,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &create_zk_config(),
    )?;
    validate_hiding_proof_shape(&proof)?;
    Ok((BfvTerminalFusedProof { proof }, public))
}

/// Verify the one-coordinate fused relation against the exact typed public
/// domain.  Changed product is impossible without breaking the in-proof weld;
/// changed domain changes a directly bound PI.
pub fn verify_zk(
    proof: &BfvTerminalFusedProof,
    public: BfvTerminalFusedPublic,
) -> Result<(), String> {
    validate_hiding_proof_shape(&proof.proof)?;
    verify_vm_descriptor2_with_config(
        &descriptor()?,
        &proof.proof,
        &public.as_felts()?,
        &create_zk_config(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dark_bazaar_private::PrivateOrder;

    fn fixture() -> (
        PrivateBookWitness,
        PrivateBookBfvSliceOpening,
        ThresholdDecryptTerminalRow,
        BfvTerminalDomain,
    ) {
        let book = PrivateBookWitness::try_from_orders_with_blinding(
            &[
                PrivateOrder::bid(10, 2),
                PrivateOrder::bid(6, 1),
                PrivateOrder::ask(5, 0),
                PrivateOrder::ask(8, 1),
            ],
            core::array::from_fn(|lane| 17_000 + lane as u32),
        )
        .expect("private book");
        let mut public_key_coefficients = vec![0u64; DEGREE];
        public_key_coefficients[0] = 17;
        public_key_coefficients[1] = MODULUS - 3;
        public_key_coefficients[DEGREE - 1] = 29;
        let mut u_coefficients = vec![0i64; DEGREE];
        u_coefficients[0] = 2;
        u_coefficients[1] = -3;
        let error_coefficient = 5;
        // Exact q0/order-0 coefficient for bid(kind = 2, quantity = 10).
        // This is the deployed Lean table entry MESSAGE_COEFF0[2 * 16 + 10],
        // not an arbitrary witness chosen to make the ciphertext equation fit.
        let message_coefficient = 34_437_628_850;
        let mut product = 0i128;
        for index in 0..DEGREE {
            let key_index = if index == 0 { 0 } else { DEGREE - index };
            product += i128::from(u_coefficients[index])
                * i128::from(public_key_coefficients[key_index])
                * if index == 0 { 1 } else { -1 };
        }
        let product = product.rem_euclid(i128::from(MODULUS)) as u64;
        let ciphertext =
            (i128::from(product) + i128::from(error_coefficient) + i128::from(message_coefficient))
                .rem_euclid(i128::from(MODULUS)) as u64;
        let opening = PrivateBookBfvSliceOpening {
            public_key_coefficients,
            u_coefficients,
            error_coefficient,
            message_coefficient,
            ciphertext_coefficient: ciphertext,
        };
        let lambda = 41_337_119_221u64;
        let smudge = (1i128 << 79) + 17_123;
        let h = (i128::from(lambda) * i128::from(product) + smudge).rem_euclid(i128::from(MODULUS))
            as u64;
        let terminal =
            ThresholdDecryptTerminalRow::from_values(MODULUS, lambda, product, smudge, h, 80)
                .expect("honest terminal");
        let domain = BfvTerminalDomain {
            party: 2,
            dkg_commitment: core::array::from_fn(|lane| 0xD600 + lane as u32),
        };
        (book, opening, terminal, domain)
    }

    fn to_p3(trace: &[Vec<BabyBear>]) -> Vec<Vec<P3BabyBear>> {
        trace
            .iter()
            .map(|row| {
                row.iter()
                    .map(|value| P3BabyBear::from_u32(value.as_u32()))
                    .collect()
            })
            .collect()
    }

    fn public_to_p3(public: BfvTerminalFusedPublic) -> Vec<P3BabyBear> {
        public
            .as_felts()
            .unwrap()
            .into_iter()
            .map(|value| P3BabyBear::from_u32(value.as_u32()))
            .collect()
    }

    #[test]
    fn exact_private_product_and_typed_domain_are_load_bearing() {
        let (book, opening, terminal, domain) = fixture();
        let (trace, public) = build_trace(
            0xDBA2,
            &book,
            &opening,
            &terminal,
            domain,
            BfvTerminalCoordinate::O0_C0_Q0_K0,
        )
        .expect("honest fused trace");
        let descriptor = descriptor().expect("fused descriptor");
        let p3_trace = to_p3(&trace);
        let p3_public = public_to_p3(public);
        if !ir2_eval_accepts(&descriptor, &p3_trace, &p3_public) {
            for (index, constraint) in descriptor.constraints.iter().enumerate() {
                let mut isolated = descriptor.clone();
                isolated.constraints = vec![constraint.clone()];
                assert!(
                    ir2_eval_accepts(&isolated, &p3_trace, &p3_public),
                    "honest fused witness first isolated rejection at constraint {index}: {constraint:?}"
                );
            }
            panic!("honest fused witness rejected only through a constraint interaction");
        }

        // Change product but keep the standalone terminal equation honest by
        // recomputing h.  Only the new same-opening weld can reject this.
        let honest_product = exact_private_product(&opening).unwrap();
        let changed_product = (honest_product + 1) % MODULUS;
        let lambda = decode_limbs(&terminal.lambda).unwrap() as u64;
        let smudge = (1i128 << 79) + 17_123;
        let changed_h = (i128::from(lambda) * i128::from(changed_product) + smudge)
            .rem_euclid(i128::from(MODULUS)) as u64;
        let changed_terminal = ThresholdDecryptTerminalRow::from_values(
            MODULUS,
            lambda,
            changed_product,
            smudge,
            changed_h,
            80,
        )
        .unwrap();
        let (changed_row, changed_terminal_public) =
            trace_and_public(&changed_terminal, public.slice.public_key_root).unwrap();
        let mut changed_trace = trace.clone();
        for row in &mut changed_trace {
            row[TERMINAL_BASE..TERMINAL_BASE + TERMINAL_WIDTH].copy_from_slice(&changed_row[0]);
        }
        let mut changed_public = public;
        changed_public.h = changed_terminal_public.h;
        assert!(!ir2_eval_accepts(
            &descriptor,
            &to_p3(&changed_trace),
            &public_to_p3(changed_public),
        ));

        let mut wrong_domain = public;
        wrong_domain.domain.party += 1;
        assert!(!ir2_eval_accepts(
            &descriptor,
            &to_p3(&trace),
            &public_to_p3(wrong_domain),
        ));

        let mut wrong_dkg = public;
        wrong_dkg.domain.dkg_commitment[3] ^= 1;
        assert!(!ir2_eval_accepts(
            &descriptor,
            &to_p3(&trace),
            &public_to_p3(wrong_dkg),
        ));

        let mut wrong_coordinate = public;
        wrong_coordinate.coordinate.coefficient = 1;
        assert!(wrong_coordinate.as_felts().is_err());
    }

    #[test]
    fn fused_builder_refuses_free_product_before_proving() {
        let (book, opening, terminal, domain) = fixture();
        let product = (exact_private_product(&opening).unwrap() + 1) % MODULUS;
        let lambda = decode_limbs(&terminal.lambda).unwrap() as u64;
        let smudge = (1i128 << 79) + 17_123;
        let h = (i128::from(lambda) * i128::from(product) + smudge).rem_euclid(i128::from(MODULUS))
            as u64;
        let free_terminal =
            ThresholdDecryptTerminalRow::from_values(MODULUS, lambda, product, smudge, h, 80)
                .unwrap();
        assert!(
            build_trace(
                0xDBA2,
                &book,
                &opening,
                &free_terminal,
                domain,
                BfvTerminalCoordinate::O0_C0_Q0_K0,
            )
            .is_err()
        );
    }
}
