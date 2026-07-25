//! Hiding threshold-decryption terminal for the production q0 BFV carrier.
//!
//! The arithmetic relation and its fixed 53-column schema are emitted by Lean
//! (`Market.PrivateBookBfvButterflyAir.thresholdTerminalQ0Descriptor`).  Rust
//! only constructs the exact limb/carry witness and invokes the pinned
//! HidingFRI prover.  The arithmetic prototype reveals `lambda`, `h`, and an
//! eight-felt commitment to a q0/N=4096 transform carrier; product, smudge,
//! quotient, complements, slack, and carries remain private.
//!
//! Critically, the descriptor does **not yet equate that private product to a
//! coefficient of the carrier**.  Context hashing only prevents metadata
//! substitution; it cannot prove a same opening.  The public composite
//! producer/verifier are therefore fail-closed quarantined.  The internal
//! prover is retained solely as arithmetic/proof-engineering substrate until a
//! committed hidden transform opening (or one fused HidingFRI relation) binds
//! secret, ciphertext, index/role, product, DKG, and collective key.

use crate::joint_turn_aggregation::CustomIr2VkRecipe;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, TableSem, UMemBoundaryWitness,
    VmConstraint2, chip_absorb_all_lanes, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::private_book_bfv_tables::{
    BfvButterflyRow, BfvFaithfulTableClaim, ThresholdDecryptTerminalRow,
    VerifiedBfvTransformBoundaries,
};
use dregg_circuit::stark_zk::{
    DreggZkStarkConfig, ZK_EXT_DEGREE, ZK_FRI_LOG_BLOWUP, ZK_FRI_LOG_FINAL_POLY_LEN,
    ZK_FRI_MAX_LOG_ARITY, ZK_FRI_NUM_QUERIES, ZK_FRI_QUERY_POW_BITS, create_zk_config,
};

/// The privacy-preserving one-coordinate product weld.  The legacy public
/// butterfly composite below remains quarantined; this child module instead
/// fuses the exact 4,096-term private slice and terminal arithmetic into one
/// HidingFRI proof.
pub mod fused;

/// Exact Lean-emitted program bytes. They are the canonical-v2 VK program.
pub const DESCRIPTOR_JSON: &str = include_str!(
    "../../circuit/descriptors/by-name/private-book-bfv-threshold-terminal-q0-b80.json"
);

pub const TRACE_WIDTH: usize = 53;
pub const PUBLIC_INPUT_COUNT: usize = 14;
pub const EXPECTED_CONSTRAINT_COUNT: usize = 103;
pub const MODULUS: u64 = 68_719_403_009;
pub const SMUDGE_BITS: u32 = 80;
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";

/// Fail-closed quarantine: the terminal AIR does not yet equate its private
/// `product` witness to an authenticated hidden transform coefficient.  A
/// commitment-context match is metadata binding, not a same-opening proof.
pub const UNLINKED_PRODUCT_CARRIER_AUTHORITY: &str =
    "BFV terminal authority quarantined: unlinked product/carrier authority";

/// Stable manifest of the exact hiding verifier/config family.
pub const HIDING_VERIFIER_MANIFEST: &str = "private-book-bfv-threshold-terminal-q0-b80-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";

const RADIX: i128 = 1 << 14;
const CARRY_SHIFT: i128 = 32_768;
const Q_LIMBS: [i128; 3] = [8_193, 16_379, 255];
const Q_MINUS_ONE_LIMBS: [i128; 3] = [8_192, 16_379, 255];
const OFFSET_LIMBS: [i128; 8] = [0, 0, 0, 0, 128, 14_784, 16_383, 1];
const DOUBLE_BOUND_LIMBS: [i128; 6] = [0, 0, 0, 0, 0, 2_048];
const CONTEXT_DOMAIN: u32 = 1_178_752_322;

const LAMBDA: usize = 0;
const PRODUCT: usize = 3;
const H: usize = 6;
const SMUDGE_SHIFT: usize = 9;
const SMUDGE_COMPLEMENT: usize = 15;
const QUOTIENT_SHIFT: usize = 21;
const EQ_CARRY_SHIFT: usize = 26;
const COMPLEMENT_CARRY: usize = 34;
const CONTEXT: usize = 40;
const PRODUCT_SLACK: usize = 48;
const PRODUCT_CAN_CARRY: usize = 51;

/// Public statement for one hidden threshold-share terminal coefficient.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BfvThresholdTerminalPublic {
    pub lambda: [u32; 3],
    pub h: [u32; 3],
    pub carrier_context: [u32; 8],
}

impl BfvThresholdTerminalPublic {
    pub fn as_u32s(self) -> [u32; PUBLIC_INPUT_COUNT] {
        let mut out = [0u32; PUBLIC_INPUT_COUNT];
        out[..3].copy_from_slice(&self.lambda);
        out[3..6].copy_from_slice(&self.h);
        out[6..].copy_from_slice(&self.carrier_context);
        out
    }

    fn as_felts(self) -> Result<[BabyBear; PUBLIC_INPUT_COUNT], String> {
        let lambda = decode_limbs(&self.lambda)?;
        let h = decode_limbs(&self.h)?;
        if lambda >= u128::from(MODULUS) || h >= u128::from(MODULUS) {
            return Err("terminal lambda/h is not a canonical q0 residue".to_string());
        }
        if let Some((lane, value)) = self
            .carrier_context
            .iter()
            .copied()
            .enumerate()
            .find(|(_, value)| *value >= BABYBEAR_P)
        {
            return Err(format!(
                "terminal carrier-context lane {lane}={value} is noncanonical for BabyBear"
            ));
        }
        Ok(self.as_u32s().map(BabyBear::new))
    }
}

/// Opaque proof: callers cannot substitute a non-hiding STARK config.
pub struct BfvThresholdTerminalZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl BfvThresholdTerminalZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("BFV terminal HidingFRI proof encode failed: {error}"))
    }

    /// Strict decode: reject trailing bytes and any proof lacking HidingFRI
    /// random-polynomial commitments/openings before ordinary verification.
    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let (proof, trailing) =
            postcard::take_from_bytes::<Ir2BatchProof<DreggZkStarkConfig>>(bytes)
                .map_err(|error| format!("BFV terminal HidingFRI proof decode failed: {error}"))?;
        if !trailing.is_empty() {
            return Err(format!(
                "BFV terminal HidingFRI proof has {} trailing bytes",
                trailing.len()
            ));
        }
        validate_hiding_proof_shape(&proof)?;
        Ok(Self { proof })
    }
}

/// Parse and fail closed on every fixed descriptor ABI boundary used below.
pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(DESCRIPTOR_JSON)?;
    if descriptor.name != "private-book-bfv-threshold-terminal-q0-b80::exact-limb-v1"
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != PUBLIC_INPUT_COUNT
        || descriptor.constraints.len() != EXPECTED_CONSTRAINT_COUNT
        || !descriptor.hash_sites.is_empty()
        || !descriptor.ranges.is_empty()
    {
        return Err("BFV terminal Lean-emitted descriptor shape drifted".to_string());
    }

    let expected_tables = [
        (781usize, "bfv_terminal_range_8", 8usize),
        (785, "bfv_terminal_range_12", 12),
        (787, "bfv_terminal_range_14", 14),
        (789, "bfv_terminal_range_16", 16),
    ];
    if descriptor.tables.len() != expected_tables.len()
        || !descriptor
            .tables
            .iter()
            .zip(expected_tables)
            .all(|(table, (id, name, bits))| {
                table.id == id
                    && table.name == name
                    && table.arity == 1
                    && table.sem == TableSem::Range { bits }
            })
    {
        return Err("BFV terminal range-table ABI drifted".to_string());
    }

    let lookup_count = descriptor
        .constraints
        .iter()
        .filter(|constraint| matches!(constraint, VmConstraint2::Lookup(_)))
        .count();
    if lookup_count != 37 {
        return Err(format!(
            "BFV terminal descriptor has {lookup_count} lookups, expected 37"
        ));
    }
    let mut pins = descriptor
        .constraints
        .iter()
        .filter_map(|constraint| match constraint {
            VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) => {
                Some((*row, *col, *pi_index))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    pins.sort_by_key(|(_, _, pi)| *pi);
    let mut expected_pins = Vec::with_capacity(PUBLIC_INPUT_COUNT);
    expected_pins.extend((0..3).map(|i| (VmRow::First, LAMBDA + i, i)));
    expected_pins.extend((0..3).map(|i| (VmRow::First, H + i, 3 + i)));
    expected_pins.extend((0..8).map(|i| (VmRow::First, CONTEXT + i, 6 + i)));
    if pins != expected_pins {
        return Err("BFV terminal public-input pins drifted".to_string());
    }
    Ok(descriptor)
}

/// Descriptor/AIR fingerprint: exact emitted bytes, domain-separated.
pub fn air_fingerprint() -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg-private-book-bfv-terminal-air-v1");
    h.update(DESCRIPTOR_JSON.as_bytes());
    *h.finalize().as_bytes()
}

/// Pinned HidingFRI verifier family, including every exported FRI knob.
pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut h =
        blake3::Hasher::new_derive_key("dregg-private-book-bfv-terminal-hiding-verifier-config-v1");
    h.update(HIDING_VERIFIER_MANIFEST.as_bytes());
    h.update(PLONKY3_REV.as_bytes());
    for knob in [
        ZK_FRI_LOG_BLOWUP,
        ZK_FRI_LOG_FINAL_POLY_LEN,
        ZK_FRI_MAX_LOG_ARITY,
        ZK_FRI_NUM_QUERIES,
        ZK_FRI_QUERY_POW_BITS,
        ZK_EXT_DEGREE,
    ] {
        h.update(&(knob as u64).to_le_bytes());
    }
    h.update(&air_fingerprint());
    *h.finalize().as_bytes()
}

/// Canary identity for the forbidden non-hiding family.
pub fn non_hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(
        "dregg-private-book-bfv-terminal-non-hiding-verifier-config-v1",
    );
    h.update(b"DreggStarkConfig|non-hiding FriPcs");
    h.update(PLONKY3_REV.as_bytes());
    h.update(&air_fingerprint());
    *h.finalize().as_bytes()
}

pub fn proving_system_canonical_bytes() -> Vec<u8> {
    let mut out = vec![0];
    out.extend_from_slice(&(PLONKY3_REV.len() as u64).to_le_bytes());
    out.extend_from_slice(PLONKY3_REV.as_bytes());
    out
}

/// Canonical-v2 registry seam for this exact relation and hiding verifier.
pub fn vk_recipe() -> CustomIr2VkRecipe {
    CustomIr2VkRecipe::source_hash(
        DESCRIPTOR_JSON.as_bytes().to_vec(),
        air_fingerprint(),
        hiding_verifier_config_fingerprint(),
        proving_system_canonical_bytes(),
    )
}

pub fn canonical_vk_hash() -> [u8; 32] {
    vk_recipe().canonical_vk_hash()
}

/// Derive the eight public context lanes from an authority that can only be
/// constructed by exact schedule/bus and real ingress/egress verification.
///
/// Each byte commitment is injected faithfully as sixteen little-endian u16
/// felts.  Eight data felts at a time are compressed with the preceding
/// eight-lane state by the deployed Poseidon2 node8 operation.  Domain and
/// exact input length make padding unambiguous.
pub fn carrier_context(authority: &VerifiedBfvTransformBoundaries) -> [u32; 8] {
    let geometry = authority.tables().geometry();
    let commitments = [
        authority.tables().descriptor_commitment(),
        authority.tables().main_trace_commitment(),
        authority.tables().schedule_commitment(),
        authority.tables().bus_commitment(),
        authority.input_commitment(),
        authority.output_commitment(),
    ];
    let mut data = Vec::with_capacity(2 + 12 + commitments.len() * 16);
    data.extend([BabyBear::new(CONTEXT_DOMAIN), BabyBear::new(110)]);
    data.extend([
        BabyBear::new(geometry.degree),
        BabyBear::new(u32::from(geometry.log_degree)),
        BabyBear::new(u32::from(geometry.direction)),
        BabyBear::new(u32::from(geometry.modulus_row)),
        BabyBear::new(u32::from(geometry.transform)),
    ]);
    for value in [geometry.modulus, geometry.psi] {
        for shift in [0, 16, 32, 48] {
            data.push(BabyBear::new(((value >> shift) & 0xffff) as u32));
        }
    }
    for commitment in commitments {
        for bytes in commitment.chunks_exact(2) {
            data.push(BabyBear::new(u32::from(u16::from_le_bytes([
                bytes[0], bytes[1],
            ]))));
        }
    }
    debug_assert_eq!(data.len(), 111);
    // The exact length is already carried as data[1]; update it here rather
    // than duplicating a hand-maintained constant in the commitment domain.
    data[1] = BabyBear::new(data.len() as u32);

    let mut root = [BabyBear::ZERO; 8];
    for chunk in data.chunks(8) {
        let mut block = [BabyBear::ZERO; 16];
        block[..8].copy_from_slice(&root);
        block[8..8 + chunk.len()].copy_from_slice(chunk);
        root = chip_absorb_all_lanes(16, &block);
    }
    root.map(BabyBear::as_u32)
}

/// Internal arithmetic prototype only.  It is deliberately not exported:
/// product is still an unconstrained private opening relative to the carrier.
fn prove_zk(
    authority: &VerifiedBfvTransformBoundaries,
    terminal: &ThresholdDecryptTerminalRow,
) -> Result<(BfvThresholdTerminalZkProof, BfvThresholdTerminalPublic), String> {
    let context = carrier_context(authority);
    let (trace, public) = trace_and_public(terminal, context)?;
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
    validate_hiding_proof_shape(&proof)?;
    Ok((BfvThresholdTerminalZkProof { proof }, public))
}

fn verify_zk(
    proof: &BfvThresholdTerminalZkProof,
    public: BfvThresholdTerminalPublic,
) -> Result<(), String> {
    validate_hiding_proof_shape(&proof.proof)?;
    verify_vm_descriptor2_with_config(
        &descriptor()?,
        &proof.proof,
        &public.as_felts()?,
        &create_zk_config(),
    )
}

/// Quarantined composite producer.  It cannot mint authority until the hidden
/// terminal product is equated to an arithmetic-authenticated transform
/// coefficient (including coefficient index, ciphertext role, and DKG/key
/// domain) inside one proof or a sound recursive opening join.
pub fn prove_bound_to_transform(
    claim: &BfvFaithfulTableClaim,
    expected_butterfly_descriptor: [u8; 32],
    main_rows: &[BfvButterflyRow],
    input: &[u64],
    output: &[u64],
    terminal: &ThresholdDecryptTerminalRow,
) -> Result<(BfvThresholdTerminalZkProof, BfvThresholdTerminalPublic), String> {
    let _ = (
        claim,
        expected_butterfly_descriptor,
        main_rows,
        input,
        output,
        terminal,
    );
    Err(UNLINKED_PRODUCT_CARRIER_AUTHORITY.to_string())
}

/// Quarantined composite verifier.  A previously generated prototype proof is
/// never accepted as product/carrier authority.
pub fn verify_bound_to_transform(
    claim: &BfvFaithfulTableClaim,
    expected_butterfly_descriptor: [u8; 32],
    main_rows: &[BfvButterflyRow],
    input: &[u64],
    output: &[u64],
    proof: &BfvThresholdTerminalZkProof,
    public: BfvThresholdTerminalPublic,
) -> Result<(), String> {
    let _ = (
        claim,
        expected_butterfly_descriptor,
        main_rows,
        input,
        output,
        proof,
        public,
    );
    Err(UNLINKED_PRODUCT_CARRIER_AUTHORITY.to_string())
}

fn validate_hiding_proof_shape(proof: &Ir2BatchProof<DreggZkStarkConfig>) -> Result<(), String> {
    if proof.degree_bits.is_empty()
        || proof.degree_bits.len() != proof.opened_values.instances.len()
        || proof.commitments.random.is_none()
        || proof
            .opened_values
            .instances
            .iter()
            .any(|instance| instance.base_opened_values.random.is_none())
    {
        return Err("BFV terminal proof is not a well-shaped HidingFRI proof".to_string());
    }
    Ok(())
}

fn decode_limbs(limbs: &[u32]) -> Result<u128, String> {
    let mut value = 0u128;
    for (index, limb) in limbs.iter().copied().enumerate().rev() {
        if limb >= 1 << 14 {
            return Err(format!("radix-2^14 limb {index}={limb} is noncanonical"));
        }
        value = value
            .checked_mul(RADIX as u128)
            .and_then(|value| value.checked_add(u128::from(limb)))
            .ok_or_else(|| "radix-2^14 limb decode overflowed u128".to_string())?;
    }
    Ok(value)
}

fn split_limbs<const N: usize>(mut value: u128) -> Result<[u32; N], String> {
    let limbs = core::array::from_fn(|_| {
        let limb = (value & ((RADIX as u128) - 1)) as u32;
        value >>= 14;
        limb
    });
    if value != 0 {
        return Err(format!("value does not fit {N} radix-2^14 limbs"));
    }
    Ok(limbs)
}

fn trace_and_public(
    terminal: &ThresholdDecryptTerminalRow,
    context: [u32; 8],
) -> Result<(Vec<Vec<BabyBear>>, BfvThresholdTerminalPublic), String> {
    terminal
        .verify(MODULUS, SMUDGE_BITS)
        .map_err(|error| format!("BFV terminal witness refused: {error}"))?;
    let mut row = [0u32; TRACE_WIDTH];
    row[LAMBDA..LAMBDA + 3].copy_from_slice(&terminal.lambda);
    row[PRODUCT..PRODUCT + 3].copy_from_slice(&terminal.product);
    row[H..H + 3].copy_from_slice(&terminal.h);
    row[SMUDGE_SHIFT..SMUDGE_SHIFT + 6].copy_from_slice(&terminal.smudge_shift);
    row[SMUDGE_COMPLEMENT..SMUDGE_COMPLEMENT + 6].copy_from_slice(&terminal.smudge_complement);
    row[QUOTIENT_SHIFT..QUOTIENT_SHIFT + 5].copy_from_slice(&terminal.quotient_shift);
    row[CONTEXT..CONTEXT + 8].copy_from_slice(&context);

    let product = decode_limbs(&terminal.product)?;
    let slack = split_limbs::<3>(u128::from(MODULUS - 1) - product)?;
    row[PRODUCT_SLACK..PRODUCT_SLACK + 3].copy_from_slice(&slack);
    let mut canonical_carry = 0i128;
    for degree in 0..3 {
        let raw =
            i128::from(terminal.product[degree]) + i128::from(slack[degree]) + canonical_carry
                - Q_MINUS_ONE_LIMBS[degree];
        if degree < 2 {
            if raw % RADIX != 0 {
                return Err("product-canonical carry is not integral".to_string());
            }
            canonical_carry = raw / RADIX;
            if !(0..=1).contains(&canonical_carry) {
                return Err("product-canonical carry is not boolean".to_string());
            }
            row[PRODUCT_CAN_CARRY + degree] = canonical_carry as u32;
        } else if raw != 0 {
            return Err("product-canonical top limb does not close".to_string());
        }
    }

    let mut complement_carry = 0i128;
    for degree in 0..6 {
        let raw = i128::from(terminal.smudge_shift[degree])
            + i128::from(terminal.smudge_complement[degree])
            + complement_carry
            - DOUBLE_BOUND_LIMBS[degree];
        if raw % RADIX != 0 {
            return Err(format!(
                "smudge-complement carry at degree {degree} is not integral"
            ));
        }
        complement_carry = raw / RADIX;
        if !(0..=1).contains(&complement_carry) {
            return Err(format!(
                "smudge-complement carry at degree {degree} is not boolean"
            ));
        }
        row[COMPLEMENT_CARRY + degree] = complement_carry as u32;
    }

    let mut equation_carry = 0i128;
    for degree in 0usize..8 {
        let convolution = (0..3)
            .filter_map(|left| {
                degree
                    .checked_sub(left)
                    .filter(|right| *right < 3)
                    .map(|right| (left, right))
            })
            .map(|(left, right)| {
                i128::from(terminal.lambda[left]) * i128::from(terminal.product[right])
            })
            .sum::<i128>();
        let quotient_times_q = (0..3)
            .filter_map(|q_limb| {
                degree
                    .checked_sub(q_limb)
                    .filter(|quotient_limb| *quotient_limb < 5)
                    .map(|quotient_limb| (q_limb, quotient_limb))
            })
            .map(|(q_limb, quotient_limb)| {
                Q_LIMBS[q_limb] * i128::from(terminal.quotient_shift[quotient_limb])
            })
            .sum::<i128>();
        let smudge = terminal
            .smudge_shift
            .get(degree)
            .copied()
            .map(i128::from)
            .unwrap_or_default();
        let h = terminal
            .h
            .get(degree)
            .copied()
            .map(i128::from)
            .unwrap_or_default();
        let raw =
            convolution + smudge + OFFSET_LIMBS[degree] - h - quotient_times_q + equation_carry;
        if raw % RADIX != 0 {
            return Err(format!(
                "terminal equation carry at degree {degree} is not integral"
            ));
        }
        equation_carry = raw / RADIX;
        let shifted = equation_carry + CARRY_SHIFT;
        if !(0..=u16::MAX as i128).contains(&shifted) {
            return Err(format!(
                "terminal equation carry at degree {degree} exceeds signed-u16 encoding"
            ));
        }
        row[EQ_CARRY_SHIFT + degree] = shifted as u32;
    }
    if equation_carry != 0 {
        return Err("terminal equation top carry does not close".to_string());
    }

    let public = BfvThresholdTerminalPublic {
        lambda: terminal.lambda,
        h: terminal.h,
        carrier_context: context,
    };
    public.as_felts()?;
    Ok((vec![row.map(BabyBear::new).to_vec()], public))
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, UMemBoundaryWitness, prove_vm_descriptor2_for_config,
    };
    use dregg_circuit::private_book_bfv_tables::{
        BfvButterflyGeometry, BfvFaithfulTableClaim, build_bfv_transform_rows,
        commit_bfv_butterfly_descriptor,
    };

    use super::*;

    fn terminal() -> ThresholdDecryptTerminalRow {
        let lambda = 41_337_119_221u64;
        let product = 62_911_771_003u64;
        let smudge = (1i128 << 79) + 17_123;
        let unreduced = i128::from(lambda) * i128::from(product) + smudge;
        let h = unreduced.rem_euclid(i128::from(MODULUS)) as u64;
        ThresholdDecryptTerminalRow::from_values(MODULUS, lambda, product, smudge, h, SMUDGE_BITS)
            .expect("honest terminal")
    }

    fn carrier(
        salt: u64,
    ) -> (
        [u8; 32],
        Vec<u64>,
        Vec<BfvButterflyRow>,
        Vec<u64>,
        BfvFaithfulTableClaim,
    ) {
        let geometry = BfvButterflyGeometry::Q0_N4096;
        let input = (0..geometry.degree as usize)
            .map(|index| {
                (index as u64 * 1_000_003 + (index as u64).pow(2) * 17 + salt) % geometry.modulus
            })
            .collect::<Vec<_>>();
        let (rows, output) = build_bfv_transform_rows(geometry, &input).expect("q0/N4096 rows");
        let descriptor = commit_bfv_butterfly_descriptor(
            b"private-book-bfv-odd-ntt-butterfly-q0-n4096::exact-48-v1",
        );
        let claim = BfvFaithfulTableClaim::prove_public_trace(descriptor, geometry, &rows)
            .expect("faithful carrier");
        (descriptor, input, rows, output, claim)
    }

    #[test]
    fn descriptor_and_vk_are_fixed_and_hiding_distinct() {
        let descriptor = descriptor().expect("fixed descriptor");
        vk_recipe()
            .require_exact_descriptor(&descriptor)
            .expect("VK program equals exact emitted bytes");
        assert_ne!(
            hiding_verifier_config_fingerprint(),
            non_hiding_verifier_config_fingerprint()
        );
        assert_ne!(canonical_vk_hash(), [0; 32]);
    }

    #[test]
    fn q0_n4096_composite_authority_is_fail_closed_quarantined() {
        let (butterfly_descriptor, input, rows, output, claim) = carrier(29);
        let terminal = terminal();
        let prove_error = match prove_bound_to_transform(
            &claim,
            butterfly_descriptor,
            &rows,
            &input,
            &output,
            &terminal,
        ) {
            Ok(_) => panic!("unlinked product/carrier must not mint authority"),
            Err(error) => error,
        };
        assert_eq!(prove_error, UNLINKED_PRODUCT_CARRIER_AUTHORITY);

        // The internal arithmetic prototype may still be exercised while the
        // weld is repaired, but the public composite verifier refuses it.
        let authority = claim
            .verify_boundaries(butterfly_descriptor, &rows, &input, &output)
            .expect("prototype public carrier");
        let prove_at = Instant::now();
        let (proof, public) = prove_zk(&authority, &terminal).expect("internal prototype proof");
        let prove_elapsed = prove_at.elapsed();
        let verify_error = verify_bound_to_transform(
            &claim,
            butterfly_descriptor,
            &rows,
            &input,
            &output,
            &proof,
            public,
        )
        .expect_err("prototype proof cannot cross quarantined authority boundary");
        assert_eq!(verify_error, UNLINKED_PRODUCT_CARRIER_AUTHORITY);
        eprintln!("q0/N4096 quarantined terminal prototype prove={prove_elapsed:?}");

        let encoded = proof.to_postcard().expect("encode");
        let decoded = BfvThresholdTerminalZkProof::from_postcard(&encoded).expect("strict decode");
        assert_eq!(
            verify_bound_to_transform(
                &claim,
                butterfly_descriptor,
                &rows,
                &input,
                &output,
                &decoded,
                public,
            )
            .unwrap_err(),
            UNLINKED_PRODUCT_CARRIER_AUTHORITY
        );
        let mut overlong = encoded;
        overlong.push(0);
        assert!(BfvThresholdTerminalZkProof::from_postcard(&overlong).is_err());

        let mut wrong_h = public;
        wrong_h.h[0] ^= 1;
        assert!(verify_zk(&proof, wrong_h).is_err());
    }

    /// A mutated hidden quotient / equality carry has no satisfying assembly.
    ///
    /// REFUSAL MECHANISM: both mutations violate ordinary AIR gates of the Main instance, and
    /// p3's debug-gated `check_constraints` PANICS inside `prove_batch` before
    /// `prove_vm_descriptor2_inner`'s self-verify can return `Err` — `check: true` replays the
    /// mem/map/umem/exact-public witnesses, not the algebra.  A bare `assert!(….is_err())`
    /// therefore cannot survive its own tooth biting; `must_refuse_or_unsat_panic` is the
    /// discriminator that can (and it additionally REDs on a shape/arity `Err`, which the old
    /// `is_err()` would have swallowed).
    #[test]
    fn hidden_quotient_and_carry_mutations_are_unsatisfiable() {
        use dregg_circuit::refusal::must_refuse_or_unsat_panic;

        let context = [7u32; 8];
        let (trace, public) = trace_and_public(&terminal(), context).expect("honest trace");
        let mut wrong_quotient = trace.clone();
        wrong_quotient[0][QUOTIENT_SHIFT] += BabyBear::ONE;
        let refusal = must_refuse_or_unsat_panic("a mutated hidden BFV terminal quotient", || {
            prove_vm_descriptor2_for_config(
                &descriptor().unwrap(),
                &wrong_quotient,
                &public.as_felts().unwrap(),
                &MemBoundaryWitness::default(),
                &[],
                &UMemBoundaryWitness::default(),
                &create_zk_config(),
            )
        });
        let reason = refusal.reason();
        assert!(
            reason.contains("constraints not satisfied on row"),
            "the mutated quotient must be refused by a VIOLATED CONSTRAINT: {reason}"
        );

        let mut wrong_carry = trace;
        wrong_carry[0][EQ_CARRY_SHIFT + 3] += BabyBear::ONE;
        let refusal = must_refuse_or_unsat_panic("a mutated hidden BFV equality carry", || {
            prove_vm_descriptor2_for_config(
                &descriptor().unwrap(),
                &wrong_carry,
                &public.as_felts().unwrap(),
                &MemBoundaryWitness::default(),
                &[],
                &UMemBoundaryWitness::default(),
                &create_zk_config(),
            )
        });
        let reason = refusal.reason();
        assert!(
            reason.contains("constraints not satisfied on row"),
            "the mutated equality carry must be refused by a VIOLATED CONSTRAINT: {reason}"
        );
    }
}
