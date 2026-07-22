//! Verifier-enforced exact-table carrier for the Lean-authored BFV butterfly relation.
//!
//! `Market.PrivateBookBfvButterflyFaithful` strengthens the descriptor's ordinary
//! membership lookups: the schedule table is the canonical table, and every boundary
//! table is an exact permutation of both the preceding writes and following reads.  The
//! generic IR2 consumer does not yet admit prover-supplied custom tables.  This module is
//! the smallest strict wire cut at that seam: it commits the two tables, binds them to an
//! exact descriptor identity and main-trace commitment, and replays the Lean condition at
//! verification.  Duplicate, omitted, substituted, and out-of-boundary rows are refused
//! even when the checksum and table commitments are recomputed.
//!
//! This v1 carrier takes the main butterfly rows as verifier input.  It is therefore useful
//! for the public q0/N=8 differential and public/certificate-mode transforms, but it is not
//! the final zero-knowledge N=4096 carrier: that must move these same multiset equalities
//! into committed IR2 LogUp instances (and add non-power-of-two logical-row padding).

use std::collections::BTreeSet;

use crate::descriptor_ir2::{EffectVmDescriptor2, parse_vm_descriptor2};
use crate::descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes;

/// The BabyBear prime. Every value transported into the IR2 table must be canonical.
pub const BABYBEAR_MODULUS: u32 = 2_013_265_921;

/// Exact width of `Market.PrivateBookBfvButterflyAir`'s main row.
pub const BFV_BUTTERFLY_TRACE_WIDTH: usize = 48;
/// Exact width of the canonical schedule lookup tuple.
pub const BFV_BUTTERFLY_SCHEDULE_WIDTH: usize = 17;
/// Exact width of one boundary-bus row: tag plus three radix-2^14 limbs.
pub const BFV_BUTTERFLY_BUS_WIDTH: usize = 4;

/// Verbatim Lean-emitted provenance for the executable q0/N=8 relation.  The
/// carrier identity is *not* a hash of these JSON source bytes: callers must
/// use [`bfv_q0_n8_descriptor_commitment`], which parses the typed descriptor
/// and commits its canonical schema encoding.
pub const BFV_Q0_N8_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/by-name/private-book-bfv-odd-ntt-butterfly-q0-n8.json");

const BFV_Q0_N8_DESCRIPTOR_NAME: &str = "private-book-bfv-odd-ntt-butterfly-q0-n8::exact-48-v1";

const MAGIC: &[u8; 8] = b"FHBFM001";
const CHECKSUM_LEN: usize = 32;
const MAX_DEGREE: usize = 4096;
const RADIX: u64 = 1 << 14;
const CARRY_SHIFT: i128 = 32_768;

const DIRECTION: usize = 0;
const STAGE: usize = 1;
const BUTTERFLY: usize = 2;
const MODULUS_ROW: usize = 3;
const TRANSFORM: usize = 4;
const LEFT_INDEX: usize = 5;
const RIGHT_INDEX: usize = 6;
const TWIDDLE_INDEX: usize = 7;
const LEFT_INPUT: usize = 8;
const RIGHT_INPUT: usize = 11;
const TWIDDLE: usize = 14;
const TWIDDLED_RIGHT: usize = 17;
const LEFT_OUTPUT: usize = 20;
const RIGHT_OUTPUT: usize = 23;
const PRODUCT_QUOTIENT: usize = 26;
const ADD_REDUCE: usize = 29;
const SUB_REDUCE: usize = 30;
const PRODUCT_CARRY: usize = 31;
const ADD_CARRY: usize = 36;
const SUB_CARRY: usize = 39;
const READ_LEFT_TAG: usize = 42;
const READ_RIGHT_TAG: usize = 43;
const WRITE_LEFT_TAG: usize = 44;
const WRITE_RIGHT_TAG: usize = 45;
const FIRST_STAGE: usize = 46;
const LAST_STAGE: usize = 47;

/// Geometry and fixed public schedule parameters of one odd-NTT butterfly family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BfvButterflyGeometry {
    /// Polynomial degree (`2^log_degree`).
    pub degree: u32,
    /// Number of radix-2 stages.
    pub log_degree: u8,
    /// Direction tag carried by every row (0 forward, 1 inverse in the family plan).
    pub direction: u8,
    /// RNS-modulus row tag.
    pub modulus_row: u8,
    /// Transform-instance tag.
    pub transform: u8,
    /// Odd BFV coefficient modulus.
    pub modulus: u64,
    /// Primitive `2*degree`-th root used by the odd transform.
    pub psi: u64,
}

impl BfvButterflyGeometry {
    /// The exact q0/N=8 geometry used by the executable Lean tooth.
    pub const Q0_N8: Self = Self {
        degree: 8,
        log_degree: 3,
        direction: 0,
        modulus_row: 0,
        transform: 0,
        modulus: 68_719_403_009,
        psi: 54_271_157_817,
    };

    /// Production-degree q0 geometry already pinned by
    /// `Market.PrivateBookBfvNttFamily.deployed_psi0_negacyclic_root`.
    pub const Q0_N4096: Self = Self {
        degree: 4096,
        log_degree: 12,
        direction: 0,
        modulus_row: 0,
        transform: 0,
        modulus: 68_719_403_009,
        psi: 5_546_991_020,
    };

    /// Inverse companion of the executable q0/N=8 tooth.  The same primitive
    /// `2N`-th root identifies the odd domain; direction selects inverse
    /// twiddles plus the post-butterfly `psi^-i / N` normalization.
    pub const Q0_N8_INVERSE: Self = Self {
        direction: 1,
        ..Self::Q0_N8
    };

    /// Production-degree inverse q0 geometry.
    pub const Q0_N4096_INVERSE: Self = Self {
        direction: 1,
        ..Self::Q0_N4096
    };

    fn validate(self) -> Result<(), BfvTableError> {
        let degree = self.degree as usize;
        if degree < 2 || degree > MAX_DEGREE || !degree.is_power_of_two() {
            return Err(BfvTableError::Geometry(format!(
                "degree {degree} must be a power of two in 2..={MAX_DEGREE}"
            )));
        }
        if self.log_degree as u32 != self.degree.ilog2() {
            return Err(BfvTableError::Geometry(format!(
                "log_degree {} does not match degree {degree}",
                self.log_degree
            )));
        }
        if self.direction > 1 {
            return Err(BfvTableError::Geometry(format!(
                "direction {} is neither forward (0) nor inverse (1)",
                self.direction
            )));
        }
        if self.modulus < 3 || self.modulus >= RADIX.pow(3) || self.modulus % 2 == 0 {
            return Err(BfvTableError::Geometry(
                "modulus must be odd and fit the three radix-2^14 limbs".to_string(),
            ));
        }
        if self.psi == 0 || self.psi >= self.modulus {
            return Err(BfvTableError::Geometry(
                "psi must be a nonzero canonical modulus residue".to_string(),
            ));
        }
        if mod_pow(self.psi, self.degree as u64, self.modulus) != self.modulus - 1
            || mod_pow(self.psi, 2 * self.degree as u64, self.modulus) != 1
        {
            return Err(BfvTableError::Geometry(
                "psi is not a primitive 2*degree-th odd-NTT root".to_string(),
            ));
        }
        Ok(())
    }

    fn main_row_count(self) -> usize {
        (self.degree as usize / 2) * self.log_degree as usize
    }

    fn schedule_row_count(self) -> usize {
        self.main_row_count()
    }

    fn bus_row_count(self) -> usize {
        self.degree as usize * (self.log_degree as usize + 1)
    }
}

/// One canonical 48-column butterfly row.
pub type BfvButterflyRow = [u32; BFV_BUTTERFLY_TRACE_WIDTH];
/// One canonical schedule table row.
pub type BfvScheduleRow = [u32; BFV_BUTTERFLY_SCHEDULE_WIDTH];
/// One canonical boundary table row.
pub type BfvBusRow = [u32; BFV_BUTTERFLY_BUS_WIDTH];

/// Unverified strict-wire claim. It becomes authoritative only through [`verify`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BfvFaithfulTableClaim {
    descriptor_commitment: [u8; 32],
    geometry: BfvButterflyGeometry,
    main_trace_commitment: [u8; 32],
    schedule_commitment: [u8; 32],
    bus_commitment: [u8; 32],
    schedule_rows: Vec<BfvScheduleRow>,
    bus_rows: Vec<BfvBusRow>,
}

/// Authority type returned only after all descriptor, commitment, schedule, and boundary
/// multiset checks have succeeded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedBfvFaithfulTables {
    descriptor_commitment: [u8; 32],
    geometry: BfvButterflyGeometry,
    main_trace_commitment: [u8; 32],
    schedule_commitment: [u8; 32],
    bus_commitment: [u8; 32],
}

/// Authority returned after the strict table carrier has additionally been
/// joined to the transform's real ingress and egress.
///
/// The strict carrier replays every 48-column integer butterfly equation as
/// well as the exact schedule/bus and ingress/egress.  This is public native
/// verification, not zero knowledge and not an IR2/FRI proof, but forged
/// arithmetic rows do not acquire authority.  In inverse mode the final
/// comparison includes exact `psi^-i / N` normalization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedBfvTransformBoundaries {
    tables: VerifiedBfvFaithfulTables,
    input_commitment: [u8; 32],
    output_commitment: [u8; 32],
}

impl VerifiedBfvTransformBoundaries {
    pub fn tables(&self) -> &VerifiedBfvFaithfulTables {
        &self.tables
    }

    pub fn input_commitment(&self) -> [u8; 32] {
        self.input_commitment
    }

    pub fn output_commitment(&self) -> [u8; 32] {
        self.output_commitment
    }
}

/// One AIR-shaped terminal coefficient for a threshold decryption share.
///
/// All large integers are represented in radix `2^14`, the same limb system
/// as the butterfly AIR.  `smudge_shift = smudge + 2^b` and
/// `smudge_complement = 2^b - smudge`; their exact sum proves the inclusive
/// signed interval without revealing a sign bit.  `quotient_shift` uses the
/// existing `2^63` protocol offset.  The row checks the integer identity
///
/// `lambda * product + smudge - h = q * quotient`
///
/// without embedding a 37-by-37-bit multiplication in BabyBear.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdDecryptTerminalRow {
    pub lambda: [u32; 3],
    pub product: [u32; 3],
    pub h: [u32; 3],
    pub smudge_shift: [u32; 6],
    pub smudge_complement: [u32; 6],
    pub quotient_shift: [u32; 5],
}

impl ThresholdDecryptTerminalRow {
    /// Construct one honest terminal row from exact signed integers.  The
    /// modular quotient is derived rather than caller-supplied.
    pub fn from_values(
        modulus: u64,
        lambda: u64,
        product: u64,
        smudge: i128,
        h: u64,
        smudge_bits: u32,
    ) -> Result<Self, BfvTableError> {
        validate_terminal_public(modulus, lambda, product, h, smudge_bits)?;
        let bound = 1i128 << smudge_bits;
        if smudge < -bound || smudge > bound {
            return Err(BfvTableError::ThresholdTerminal(format!(
                "smudge {smudge} is outside [-2^{smudge_bits}, 2^{smudge_bits}]"
            )));
        }
        let numerator = i128::from(lambda)
            .checked_mul(i128::from(product))
            .and_then(|value| value.checked_add(smudge))
            .and_then(|value| value.checked_sub(i128::from(h)))
            .ok_or_else(|| {
                BfvTableError::ThresholdTerminal("terminal numerator overflowed i128".to_string())
            })?;
        if numerator.rem_euclid(i128::from(modulus)) != 0 {
            return Err(BfvTableError::ThresholdTerminal(
                "lambda*product+smudge-h is not divisible by q".to_string(),
            ));
        }
        let quotient = numerator / i128::from(modulus);
        let quotient_shift = quotient.checked_add(1i128 << 63).ok_or_else(|| {
            BfvTableError::ThresholdTerminal("signed quotient offset overflow".to_string())
        })?;
        if !(0..(1i128 << 64)).contains(&quotient_shift) {
            return Err(BfvTableError::ThresholdTerminal(
                "signed quotient does not fit the protocol's offset-u64 range".to_string(),
            ));
        }
        let smudge_shift = smudge + bound;
        let smudge_complement = bound - smudge;
        let row = Self {
            lambda: encode_radix_limbs::<3>(u128::from(lambda))?,
            product: encode_radix_limbs::<3>(u128::from(product))?,
            h: encode_radix_limbs::<3>(u128::from(h))?,
            smudge_shift: encode_radix_limbs::<6>(smudge_shift as u128)?,
            smudge_complement: encode_radix_limbs::<6>(smudge_complement as u128)?,
            quotient_shift: encode_radix_limbs::<5>(quotient_shift as u128)?,
        };
        row.verify(modulus, smudge_bits)?;
        Ok(row)
    }

    /// Verify canonical limbs, the inclusive signed-smudge complement, and
    /// the exact integer modular equation.  This is the row-local relation the
    /// production IR2 terminal gate must arithmetize.
    pub fn verify(&self, modulus: u64, smudge_bits: u32) -> Result<(), BfvTableError> {
        let lambda = decode_radix_limbs(&self.lambda)?;
        let product = decode_radix_limbs(&self.product)?;
        let h = decode_radix_limbs(&self.h)?;
        let smudge_shift = decode_radix_limbs(&self.smudge_shift)?;
        let smudge_complement = decode_radix_limbs(&self.smudge_complement)?;
        let quotient_shift = decode_radix_limbs(&self.quotient_shift)?;
        let lambda = u64::try_from(lambda)
            .map_err(|_| BfvTableError::ThresholdTerminal("lambda does not fit u64".to_string()))?;
        let product = u64::try_from(product).map_err(|_| {
            BfvTableError::ThresholdTerminal("product does not fit u64".to_string())
        })?;
        let h = u64::try_from(h)
            .map_err(|_| BfvTableError::ThresholdTerminal("h does not fit u64".to_string()))?;
        validate_terminal_public(modulus, lambda, product, h, smudge_bits)?;

        let bound = 1u128 << smudge_bits;
        if smudge_shift
            .checked_add(smudge_complement)
            .filter(|sum| *sum == 2 * bound)
            .is_none()
        {
            return Err(BfvTableError::ThresholdTerminal(
                "smudge shift/complement do not sum to 2^(b+1)".to_string(),
            ));
        }
        if quotient_shift >= (1u128 << 64) {
            return Err(BfvTableError::ThresholdTerminal(
                "offset quotient is not a canonical u64".to_string(),
            ));
        }
        let smudge = i128::try_from(smudge_shift).expect("six 14-bit limbs fit i128")
            - i128::try_from(bound).expect("smudge bound fits i128");
        let quotient =
            i128::try_from(quotient_shift).expect("five 14-bit limbs fit i128") - (1i128 << 63);
        let left = i128::from(lambda) * i128::from(product) + smudge - i128::from(h);
        let right = i128::from(modulus) * quotient;
        if left != right {
            return Err(BfvTableError::ThresholdTerminal(
                "exact lambda*product+smudge-h=q*quotient relation failed".to_string(),
            ));
        }
        Ok(())
    }
}

impl VerifiedBfvFaithfulTables {
    /// Exact descriptor identity authorized by this carrier.
    pub fn descriptor_commitment(&self) -> [u8; 32] {
        self.descriptor_commitment
    }

    /// Exact public geometry checked by this carrier.
    pub fn geometry(&self) -> BfvButterflyGeometry {
        self.geometry
    }

    /// Commitment to the verifier-supplied main rows.
    pub fn main_trace_commitment(&self) -> [u8; 32] {
        self.main_trace_commitment
    }

    /// Commitment to the exact canonical schedule table.
    pub fn schedule_commitment(&self) -> [u8; 32] {
        self.schedule_commitment
    }

    /// Commitment to the exact source/sink boundary table.
    pub fn bus_commitment(&self) -> [u8; 32] {
        self.bus_commitment
    }
}

/// Strict verification failures. There is no permissive/fallback decode path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BfvTableError {
    /// Geometry is malformed or inconsistent.
    Geometry(String),
    /// Strict wire shape/version/checksum failure.
    Wire(String),
    /// Descriptor identity substitution.
    DescriptorCommitment,
    /// The Lean-emitted IR2 descriptor failed typed parsing/canonicalization or
    /// drifted away from the q0/N=8 carrier's pinned outer shape.
    Descriptor(String),
    /// Main trace shape/order/canonical-field failure.
    MainTrace(String),
    /// A committed digest does not match its canonical rows.
    Commitment(&'static str),
    /// The schedule table differs from the exact family schedule.
    Schedule(String),
    /// A boundary table is not the exact source and sink multiset.
    Boundary { boundary: usize, reason: String },
    /// The faithful transform starts from or finishes at a different
    /// polynomial than the caller supplied.
    TransformBoundary(String),
    /// A threshold-share terminal limb row is noncanonical or does not satisfy
    /// the exact signed modular equation.
    ThresholdTerminal(String),
}

impl std::fmt::Display for BfvTableError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Geometry(s) => write!(f, "BFV butterfly geometry: {s}"),
            Self::Wire(s) => write!(f, "BFV faithful-table wire: {s}"),
            Self::DescriptorCommitment => write!(f, "BFV descriptor commitment mismatch"),
            Self::Descriptor(s) => write!(f, "BFV typed descriptor: {s}"),
            Self::MainTrace(s) => write!(f, "BFV main trace: {s}"),
            Self::Commitment(which) => write!(f, "BFV {which} commitment mismatch"),
            Self::Schedule(s) => write!(f, "BFV schedule table: {s}"),
            Self::Boundary { boundary, reason } => {
                write!(f, "BFV boundary {boundary}: {reason}")
            }
            Self::TransformBoundary(s) => write!(f, "BFV transform boundary: {s}"),
            Self::ThresholdTerminal(s) => write!(f, "threshold terminal limb: {s}"),
        }
    }
}

impl std::error::Error for BfvTableError {}

impl BfvFaithfulTableClaim {
    /// Build the canonical exact-table claim for a verifier-visible butterfly trace.
    pub fn prove_public_trace(
        descriptor_commitment: [u8; 32],
        geometry: BfvButterflyGeometry,
        main_rows: &[BfvButterflyRow],
    ) -> Result<Self, BfvTableError> {
        geometry.validate()?;
        validate_main_rows(geometry, main_rows)?;
        let schedule_rows = canonical_schedule(geometry)?;
        let bus_rows = canonical_bus_from_source(geometry, main_rows)?;
        let claim = Self {
            descriptor_commitment,
            geometry,
            main_trace_commitment: commit_main_rows(main_rows),
            schedule_commitment: commit_schedule_rows(&schedule_rows),
            bus_commitment: commit_bus_rows(&bus_rows),
            schedule_rows,
            bus_rows,
        };
        // The producer uses the same fail-closed replay as the consumer. This is a guard,
        // never the authority boundary; consumers must call `verify` themselves.
        claim.verify(descriptor_commitment, main_rows)?;
        Ok(claim)
    }

    /// Verify descriptor identity, every committed byte, the exact schedule, and both
    /// permutations at every boundary. The main rows are explicit verifier input in v1.
    pub fn verify(
        &self,
        expected_descriptor_commitment: [u8; 32],
        main_rows: &[BfvButterflyRow],
    ) -> Result<VerifiedBfvFaithfulTables, BfvTableError> {
        self.geometry.validate()?;
        if self.descriptor_commitment != expected_descriptor_commitment {
            return Err(BfvTableError::DescriptorCommitment);
        }
        validate_main_rows(self.geometry, main_rows)?;
        if self.main_trace_commitment != commit_main_rows(main_rows) {
            return Err(BfvTableError::Commitment("main-trace"));
        }
        if self.schedule_commitment != commit_schedule_rows(&self.schedule_rows) {
            return Err(BfvTableError::Commitment("schedule-table"));
        }
        if self.bus_commitment != commit_bus_rows(&self.bus_rows) {
            return Err(BfvTableError::Commitment("boundary-table"));
        }

        let expected_schedule = canonical_schedule(self.geometry)?;
        if self.schedule_rows.len() != expected_schedule.len() {
            return Err(BfvTableError::Schedule(format!(
                "row count {} != exact {}",
                self.schedule_rows.len(),
                expected_schedule.len()
            )));
        }
        let mut got_schedule = self.schedule_rows.clone();
        got_schedule.sort_unstable();
        let mut want_schedule = expected_schedule;
        want_schedule.sort_unstable();
        if got_schedule != want_schedule {
            return Err(BfvTableError::Schedule(
                "committed rows are not the canonical schedule multiset".to_string(),
            ));
        }

        verify_boundaries(self.geometry, main_rows, &self.bus_rows)?;
        Ok(VerifiedBfvFaithfulTables {
            descriptor_commitment: self.descriptor_commitment,
            geometry: self.geometry,
            main_trace_commitment: self.main_trace_commitment,
            schedule_commitment: self.schedule_commitment,
            bus_commitment: self.bus_commitment,
        })
    }

    /// Conjoin the exact-table replay with the real transform ingress and
    /// egress.  Forward ingress is `bit_reverse(input[i] * psi^i)`; inverse
    /// ingress is `bit_reverse(input)`.  Forward egress is direct, while
    /// inverse egress is multiplied coefficient-wise by `psi^-i / N`.
    pub fn verify_boundaries(
        &self,
        expected_descriptor_commitment: [u8; 32],
        main_rows: &[BfvButterflyRow],
        input: &[u64],
        output: &[u64],
    ) -> Result<VerifiedBfvTransformBoundaries, BfvTableError> {
        let tables = self.verify(expected_descriptor_commitment, main_rows)?;
        verify_transform_boundaries(self.geometry, main_rows, input, output)?;
        Ok(VerifiedBfvTransformBoundaries {
            tables,
            input_commitment: commit_residues(b"dregg/bfv-ntt/input/v1", input),
            output_commitment: commit_residues(b"dregg/bfv-ntt/output/v1", output),
        })
    }

    /// Canonical strict wire bytes. The final BLAKE3 checksum is corruption detection;
    /// verification still recomputes all exactness conditions after a valid decode.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            188 + self.schedule_rows.len() * BFV_BUTTERFLY_SCHEDULE_WIDTH * 4
                + self.bus_rows.len() * BFV_BUTTERFLY_BUS_WIDTH * 4,
        );
        out.extend_from_slice(MAGIC);
        out.extend_from_slice(&self.descriptor_commitment);
        out.extend_from_slice(&self.geometry.degree.to_le_bytes());
        out.push(self.geometry.log_degree);
        out.push(self.geometry.direction);
        out.push(self.geometry.modulus_row);
        out.push(self.geometry.transform);
        out.extend_from_slice(&self.geometry.modulus.to_le_bytes());
        out.extend_from_slice(&self.geometry.psi.to_le_bytes());
        out.extend_from_slice(&self.main_trace_commitment);
        out.extend_from_slice(&self.schedule_commitment);
        out.extend_from_slice(&self.bus_commitment);
        out.extend_from_slice(&(self.schedule_rows.len() as u32).to_le_bytes());
        let mut schedule_rows = self.schedule_rows.clone();
        schedule_rows.sort_unstable();
        for row in &schedule_rows {
            for value in row {
                out.extend_from_slice(&value.to_le_bytes());
            }
        }
        out.extend_from_slice(&(self.bus_rows.len() as u32).to_le_bytes());
        let mut bus_rows = self.bus_rows.clone();
        bus_rows.sort_unstable();
        for row in &bus_rows {
            for value in row {
                out.extend_from_slice(&value.to_le_bytes());
            }
        }
        let checksum = blake3::hash(&out);
        out.extend_from_slice(checksum.as_bytes());
        out
    }

    /// Strict, allocation-bounded decoder. It does not confer authority; call [`verify`].
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, BfvTableError> {
        if bytes.len() < 8 + 32 + 4 + 4 + 8 + 8 + 32 * 3 + 4 + 4 + CHECKSUM_LEN {
            return Err(BfvTableError::Wire("truncated header".to_string()));
        }
        let (body, checksum) = bytes.split_at(bytes.len() - CHECKSUM_LEN);
        if blake3::hash(body).as_bytes() != checksum {
            return Err(BfvTableError::Wire("checksum mismatch".to_string()));
        }
        let mut reader = Reader { bytes: body, at: 0 };
        if reader.take(8)? != MAGIC {
            return Err(BfvTableError::Wire("unsupported magic/version".to_string()));
        }
        let descriptor_commitment = reader.array32()?;
        let geometry = BfvButterflyGeometry {
            degree: reader.u32()?,
            log_degree: reader.u8()?,
            direction: reader.u8()?,
            modulus_row: reader.u8()?,
            transform: reader.u8()?,
            modulus: reader.u64()?,
            psi: reader.u64()?,
        };
        geometry.validate()?;
        let main_trace_commitment = reader.array32()?;
        let schedule_commitment = reader.array32()?;
        let bus_commitment = reader.array32()?;
        let schedule_count = reader.u32()? as usize;
        if schedule_count > geometry.schedule_row_count() + 1 {
            return Err(BfvTableError::Wire(format!(
                "schedule row count {schedule_count} exceeds bounded geometry"
            )));
        }
        let mut schedule_rows = Vec::with_capacity(schedule_count);
        for _ in 0..schedule_count {
            let mut row = [0u32; BFV_BUTTERFLY_SCHEDULE_WIDTH];
            for value in &mut row {
                *value = reader.canonical_felt()?;
            }
            schedule_rows.push(row);
        }
        if !schedule_rows.windows(2).all(|rows| rows[0] <= rows[1]) {
            return Err(BfvTableError::Wire(
                "schedule rows are not in canonical order".to_string(),
            ));
        }
        let bus_count = reader.u32()? as usize;
        if bus_count > geometry.bus_row_count() + 1 {
            return Err(BfvTableError::Wire(format!(
                "bus row count {bus_count} exceeds bounded geometry"
            )));
        }
        let mut bus_rows = Vec::with_capacity(bus_count);
        for _ in 0..bus_count {
            let mut row = [0u32; BFV_BUTTERFLY_BUS_WIDTH];
            for value in &mut row {
                *value = reader.canonical_felt()?;
            }
            bus_rows.push(row);
        }
        if !bus_rows.windows(2).all(|rows| rows[0] <= rows[1]) {
            return Err(BfvTableError::Wire(
                "bus rows are not in canonical order".to_string(),
            ));
        }
        if reader.at != body.len() {
            return Err(BfvTableError::Wire("trailing bytes".to_string()));
        }
        Ok(Self {
            descriptor_commitment,
            geometry,
            main_trace_commitment,
            schedule_commitment,
            bus_commitment,
            schedule_rows,
            bus_rows,
        })
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], BfvTableError> {
        let end = self
            .at
            .checked_add(n)
            .ok_or_else(|| BfvTableError::Wire("length overflow".to_string()))?;
        let value = self
            .bytes
            .get(self.at..end)
            .ok_or_else(|| BfvTableError::Wire("truncated field".to_string()))?;
        self.at = end;
        Ok(value)
    }

    fn u8(&mut self) -> Result<u8, BfvTableError> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, BfvTableError> {
        let mut out = [0u8; 4];
        out.copy_from_slice(self.take(4)?);
        Ok(u32::from_le_bytes(out))
    }

    fn canonical_felt(&mut self) -> Result<u32, BfvTableError> {
        let value = self.u32()?;
        if value >= BABYBEAR_MODULUS {
            return Err(BfvTableError::Wire(format!(
                "non-canonical BabyBear value {value}"
            )));
        }
        Ok(value)
    }

    fn u64(&mut self) -> Result<u64, BfvTableError> {
        let mut out = [0u8; 8];
        out.copy_from_slice(self.take(8)?);
        Ok(u64::from_le_bytes(out))
    }

    fn array32(&mut self) -> Result<[u8; 32], BfvTableError> {
        let mut out = [0u8; 32];
        out.copy_from_slice(self.take(32)?);
        Ok(out)
    }
}

fn commit_rows<const W: usize>(domain: &[u8], rows: &[[u32; W]]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(domain);
    h.update(&(W as u64).to_le_bytes());
    h.update(&(rows.len() as u64).to_le_bytes());
    for row in rows {
        for value in row {
            h.update(&value.to_le_bytes());
        }
    }
    *h.finalize().as_bytes()
}

fn commit_residues(domain: &[u8], values: &[u64]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(domain);
    h.update(&(values.len() as u64).to_le_bytes());
    for value in values {
        h.update(&value.to_le_bytes());
    }
    *h.finalize().as_bytes()
}

/// Low-level domain-separated byte commitment.  A Lean-authored relation must
/// pass canonical typed `EffectVmDescriptor2` bytes here, never JSON source or
/// a display name.  Prefer [`commit_bfv_butterfly_typed_descriptor`] and the
/// fixed [`bfv_q0_n8_descriptor_commitment`] entry point.
pub fn commit_bfv_butterfly_descriptor(descriptor_bytes: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg/bfv-butterfly/descriptor/v1");
    h.update(&(descriptor_bytes.len() as u64).to_le_bytes());
    h.update(descriptor_bytes);
    *h.finalize().as_bytes()
}

/// Commit the schema-canonical encoding of a parsed typed IR2 relation.
/// Whitespace and JSON object-key order therefore cannot change identity,
/// while any represented typed-field mutation does.
pub fn commit_bfv_butterfly_typed_descriptor(
    descriptor: &EffectVmDescriptor2,
) -> Result<[u8; 32], BfvTableError> {
    let bytes = canonical_effect_vm_descriptor2_bytes(descriptor)
        .map_err(|error| BfvTableError::Descriptor(error.to_string()))?;
    Ok(commit_bfv_butterfly_descriptor(&bytes))
}

/// Canonical typed-object identity of the exact Lean-emitted q0/N=8 relation.
pub fn bfv_q0_n8_descriptor_commitment() -> Result<[u8; 32], BfvTableError> {
    let descriptor =
        parse_vm_descriptor2(BFV_Q0_N8_DESCRIPTOR_JSON).map_err(BfvTableError::Descriptor)?;
    if descriptor.name != BFV_Q0_N8_DESCRIPTOR_NAME
        || descriptor.trace_width != BFV_BUTTERFLY_TRACE_WIDTH
        || descriptor.public_input_count != 0
    {
        return Err(BfvTableError::Descriptor(
            "Lean q0/N=8 descriptor outer shape drifted".to_string(),
        ));
    }
    commit_bfv_butterfly_typed_descriptor(&descriptor)
}

/// Canonical commitment used to bind this carrier to its verifier-supplied main trace.
pub fn commit_main_rows(rows: &[BfvButterflyRow]) -> [u8; 32] {
    commit_rows(b"dregg/bfv-butterfly/main/v1", rows)
}

fn commit_schedule_rows(rows: &[BfvScheduleRow]) -> [u8; 32] {
    let mut rows = rows.to_vec();
    rows.sort_unstable();
    commit_rows(b"dregg/bfv-butterfly/schedule/v1", &rows)
}

fn commit_bus_rows(rows: &[BfvBusRow]) -> [u8; 32] {
    let mut rows = rows.to_vec();
    rows.sort_unstable();
    commit_rows(b"dregg/bfv-butterfly/bus/v1", &rows)
}

fn validate_main_rows(
    geometry: BfvButterflyGeometry,
    rows: &[BfvButterflyRow],
) -> Result<(), BfvTableError> {
    if rows.len() != geometry.main_row_count() {
        return Err(BfvTableError::MainTrace(format!(
            "row count {} != exact {}",
            rows.len(),
            geometry.main_row_count()
        )));
    }
    for (row_index, row) in rows.iter().enumerate() {
        for (column, value) in row.iter().enumerate() {
            if *value >= BABYBEAR_MODULUS {
                return Err(BfvTableError::MainTrace(format!(
                    "row {row_index} column {column} is non-canonical BabyBear {value}"
                )));
            }
        }
        let stage = row_index / (geometry.degree as usize / 2);
        let butterfly = row_index % (geometry.degree as usize / 2);
        if row[STAGE] as usize != stage || row[BUTTERFLY] as usize != butterfly {
            return Err(BfvTableError::MainTrace(format!(
                "row {row_index} is not in canonical stage/butterfly order"
            )));
        }
        let expected = schedule_row(geometry, stage, butterfly)?;
        if extract_schedule(row) != expected {
            return Err(BfvTableError::MainTrace(format!(
                "row {row_index} schedule tuple differs from the canonical family"
            )));
        }
        validate_butterfly_arithmetic(geometry, row_index, row)?;
    }
    Ok(())
}

/// Native replay of the exact radix-2^14 equations authored in
/// `Market.PrivateBookBfvButterflyAir`.  This closes the previous seam where a
/// schedule- and bus-consistent row could carry arbitrary arithmetic values.
fn validate_butterfly_arithmetic(
    geometry: BfvButterflyGeometry,
    row_index: usize,
    row: &BfvButterflyRow,
) -> Result<(), BfvTableError> {
    let decode = |base: usize, label: &'static str| -> Result<u64, BfvTableError> {
        let value = decode_limbs3([row[base], row[base + 1], row[base + 2]]).map_err(|_| {
            BfvTableError::MainTrace(format!(
                "row {row_index} {label} has a noncanonical radix-2^14 limb"
            ))
        })?;
        if value >= geometry.modulus {
            return Err(BfvTableError::MainTrace(format!(
                "row {row_index} {label}={value} is not canonical modulo {}",
                geometry.modulus
            )));
        }
        Ok(value)
    };
    let left = decode(LEFT_INPUT, "left input")?;
    let right = decode(RIGHT_INPUT, "right input")?;
    let twiddle = decode(TWIDDLE, "twiddle")?;
    let product = decode(TWIDDLED_RIGHT, "twiddled right")?;
    let left_output = decode(LEFT_OUTPUT, "left output")?;
    let right_output = decode(RIGHT_OUTPUT, "right output")?;
    let quotient = decode(PRODUCT_QUOTIENT, "product quotient")?;
    let add_reduce = row[ADD_REDUCE];
    let sub_reduce = row[SUB_REDUCE];
    if add_reduce > 1 || sub_reduce > 1 {
        return Err(BfvTableError::MainTrace(format!(
            "row {row_index} reduction selectors are not boolean"
        )));
    }

    let q = u128::from(geometry.modulus);
    if u128::from(right) * u128::from(twiddle) != u128::from(product) + q * u128::from(quotient) {
        return Err(BfvTableError::MainTrace(format!(
            "row {row_index} product/quotient equation failed"
        )));
    }
    if u128::from(left) + u128::from(product)
        != u128::from(left_output) + q * u128::from(add_reduce)
    {
        return Err(BfvTableError::MainTrace(format!(
            "row {row_index} modular-add equation failed"
        )));
    }
    if u128::from(left) + q * u128::from(sub_reduce)
        != u128::from(product) + u128::from(right_output)
    {
        return Err(BfvTableError::MainTrace(format!(
            "row {row_index} modular-subtract equation failed"
        )));
    }

    let expected_product = product_carries(right, twiddle, product, quotient, geometry.modulus);
    let expected_add = add_carries(left, product, left_output, add_reduce, geometry.modulus);
    let expected_sub = sub_carries(left, product, right_output, sub_reduce, geometry.modulus);
    for (base, label, expected) in [
        (PRODUCT_CARRY, "product", expected_product.as_slice()),
        (ADD_CARRY, "add", expected_add.as_slice()),
        (SUB_CARRY, "subtract", expected_sub.as_slice()),
    ] {
        for (offset, carry) in expected.iter().copied().enumerate() {
            if !(-CARRY_SHIFT..CARRY_SHIFT).contains(&carry)
                || row[base + offset] != (carry + CARRY_SHIFT) as u32
            {
                return Err(BfvTableError::MainTrace(format!(
                    "row {row_index} {label} carry {offset} is not the exact signed carry"
                )));
            }
        }
    }
    Ok(())
}

fn canonical_schedule(
    geometry: BfvButterflyGeometry,
) -> Result<Vec<BfvScheduleRow>, BfvTableError> {
    let mut rows = Vec::with_capacity(geometry.schedule_row_count());
    for stage in 0..geometry.log_degree as usize {
        for butterfly in 0..geometry.degree as usize / 2 {
            rows.push(schedule_row(geometry, stage, butterfly)?);
        }
    }
    Ok(rows)
}

fn schedule_row(
    geometry: BfvButterflyGeometry,
    stage: usize,
    butterfly: usize,
) -> Result<BfvScheduleRow, BfvTableError> {
    let n = geometry.degree as usize;
    let half = 1usize << stage;
    let len = 2 * half;
    let left = (butterfly / half) * len + butterfly % half;
    let right = left + half;
    let twiddle_index = (butterfly % half) * (n / len);
    let root = if geometry.direction == 0 {
        geometry.psi
    } else {
        mod_inverse_prime(geometry.psi, geometry.modulus)
    };
    let twiddle = mod_pow(root, 2 * twiddle_index as u64, geometry.modulus);
    let limbs = limbs3(twiddle)?;
    let values = [
        geometry.direction as u32,
        stage as u32,
        butterfly as u32,
        geometry.modulus_row as u32,
        geometry.transform as u32,
        left as u32,
        right as u32,
        twiddle_index as u32,
        limbs[0],
        limbs[1],
        limbs[2],
        (stage * n + left) as u32,
        (stage * n + right) as u32,
        ((stage + 1) * n + left) as u32,
        ((stage + 1) * n + right) as u32,
        u32::from(stage == 0),
        u32::from(stage + 1 == geometry.log_degree as usize),
    ];
    if values.iter().any(|value| *value >= BABYBEAR_MODULUS) {
        return Err(BfvTableError::Geometry(
            "canonical schedule exceeds the BabyBear table domain".to_string(),
        ));
    }
    Ok(values)
}

fn extract_schedule(row: &BfvButterflyRow) -> BfvScheduleRow {
    [
        row[DIRECTION],
        row[STAGE],
        row[BUTTERFLY],
        row[MODULUS_ROW],
        row[TRANSFORM],
        row[LEFT_INDEX],
        row[RIGHT_INDEX],
        row[TWIDDLE_INDEX],
        row[TWIDDLE],
        row[TWIDDLE + 1],
        row[TWIDDLE + 2],
        row[READ_LEFT_TAG],
        row[READ_RIGHT_TAG],
        row[WRITE_LEFT_TAG],
        row[WRITE_RIGHT_TAG],
        row[FIRST_STAGE],
        row[LAST_STAGE],
    ]
}

fn bus_item(row: &BfvButterflyRow, tag: usize, residue: usize) -> BfvBusRow {
    [row[tag], row[residue], row[residue + 1], row[residue + 2]]
}

fn decode_limbs3(limbs: [u32; 3]) -> Result<u64, BfvTableError> {
    if limbs[0] as u64 >= RADIX || limbs[1] as u64 >= RADIX || limbs[2] as u64 >= RADIX {
        return Err(BfvTableError::TransformBoundary(
            "noncanonical radix-2^14 residue limb".to_string(),
        ));
    }
    Ok(u64::from(limbs[0]) + u64::from(limbs[1]) * RADIX + u64::from(limbs[2]) * RADIX * RADIX)
}

fn boundary_values(
    geometry: BfvButterflyGeometry,
    rows: &[BfvButterflyRow],
    first: bool,
) -> Result<Vec<u64>, BfvTableError> {
    let stage = if first {
        0
    } else {
        geometry.log_degree as usize - 1
    };
    let image = if first {
        stage_reads(geometry, rows, stage)
    } else {
        stage_writes(geometry, rows, stage)
    };
    let n = geometry.degree as usize;
    let boundary = if first {
        0
    } else {
        geometry.log_degree as usize
    };
    let mut values = vec![None; n];
    for row in image {
        let tag = row[0] as usize;
        let expected_lo = boundary * n;
        if tag < expected_lo || tag >= expected_lo + n {
            return Err(BfvTableError::TransformBoundary(format!(
                "tag {tag} is outside boundary {boundary}"
            )));
        }
        let index = tag - expected_lo;
        let value = decode_limbs3([row[1], row[2], row[3]])?;
        if value >= geometry.modulus {
            return Err(BfvTableError::TransformBoundary(format!(
                "boundary {boundary} residue {index} is noncanonical"
            )));
        }
        if values[index].replace(value).is_some() {
            return Err(BfvTableError::TransformBoundary(format!(
                "boundary {boundary} repeats residue {index}"
            )));
        }
    }
    values
        .into_iter()
        .enumerate()
        .map(|(index, value)| {
            value.ok_or_else(|| {
                BfvTableError::TransformBoundary(format!(
                    "boundary {boundary} omits residue {index}"
                ))
            })
        })
        .collect()
}

fn verify_transform_boundaries(
    geometry: BfvButterflyGeometry,
    rows: &[BfvButterflyRow],
    input: &[u64],
    output: &[u64],
) -> Result<(), BfvTableError> {
    geometry.validate()?;
    let n = geometry.degree as usize;
    if input.len() != n || output.len() != n {
        return Err(BfvTableError::TransformBoundary(format!(
            "input/output lengths {}/{} do not equal degree {n}",
            input.len(),
            output.len()
        )));
    }
    if input
        .iter()
        .chain(output)
        .any(|value| *value >= geometry.modulus)
    {
        return Err(BfvTableError::TransformBoundary(
            "input or output contains a noncanonical residue".to_string(),
        ));
    }

    let ingress = boundary_values(geometry, rows, true)?;
    let egress = boundary_values(geometry, rows, false)?;
    let bits = geometry.log_degree as u32;
    let psi_inverse = mod_inverse_prime(geometry.psi, geometry.modulus);
    let n_inverse = mod_inverse_prime(geometry.degree as u64, geometry.modulus);

    let mut expected_ingress = vec![0u64; n];
    for (index, slot) in expected_ingress.iter_mut().enumerate() {
        let source = index.reverse_bits() >> (usize::BITS - bits);
        *slot = if geometry.direction == 0 {
            mod_mul(
                input[source],
                mod_pow(geometry.psi, source as u64, geometry.modulus),
                geometry.modulus,
            )
        } else {
            input[source]
        };
    }
    if ingress != expected_ingress {
        let index = ingress
            .iter()
            .zip(&expected_ingress)
            .position(|(actual, expected)| actual != expected)
            .unwrap_or(0);
        return Err(BfvTableError::TransformBoundary(format!(
            "ingress residue {index} is not the canonical twist/bit-reversal"
        )));
    }

    let expected_output = if geometry.direction == 0 {
        egress
    } else {
        egress
            .into_iter()
            .enumerate()
            .map(|(index, value)| {
                let untwist = mod_mul(
                    mod_pow(psi_inverse, index as u64, geometry.modulus),
                    n_inverse,
                    geometry.modulus,
                );
                mod_mul(value, untwist, geometry.modulus)
            })
            .collect()
    };
    if output != expected_output {
        let index = output
            .iter()
            .zip(&expected_output)
            .position(|(actual, expected)| actual != expected)
            .unwrap_or(0);
        return Err(BfvTableError::TransformBoundary(format!(
            "egress residue {index} does not match the normalized output"
        )));
    }
    Ok(())
}

fn stage_reads(
    geometry: BfvButterflyGeometry,
    rows: &[BfvButterflyRow],
    stage: usize,
) -> Vec<BfvBusRow> {
    let per_stage = geometry.degree as usize / 2;
    rows[stage * per_stage..(stage + 1) * per_stage]
        .iter()
        .flat_map(|row| {
            [
                bus_item(row, READ_LEFT_TAG, LEFT_INPUT),
                bus_item(row, READ_RIGHT_TAG, RIGHT_INPUT),
            ]
        })
        .collect()
}

fn stage_writes(
    geometry: BfvButterflyGeometry,
    rows: &[BfvButterflyRow],
    stage: usize,
) -> Vec<BfvBusRow> {
    let per_stage = geometry.degree as usize / 2;
    rows[stage * per_stage..(stage + 1) * per_stage]
        .iter()
        .flat_map(|row| {
            [
                bus_item(row, WRITE_LEFT_TAG, LEFT_OUTPUT),
                bus_item(row, WRITE_RIGHT_TAG, RIGHT_OUTPUT),
            ]
        })
        .collect()
}

fn source_image(
    geometry: BfvButterflyGeometry,
    rows: &[BfvButterflyRow],
    boundary: usize,
) -> Vec<BfvBusRow> {
    if boundary == 0 {
        stage_reads(geometry, rows, 0)
    } else {
        stage_writes(geometry, rows, boundary - 1)
    }
}

fn sink_image(
    geometry: BfvButterflyGeometry,
    rows: &[BfvButterflyRow],
    boundary: usize,
) -> Vec<BfvBusRow> {
    if boundary == geometry.log_degree as usize {
        stage_writes(geometry, rows, boundary - 1)
    } else {
        stage_reads(geometry, rows, boundary)
    }
}

fn canonical_bus_from_source(
    geometry: BfvButterflyGeometry,
    rows: &[BfvButterflyRow],
) -> Result<Vec<BfvBusRow>, BfvTableError> {
    let mut out = Vec::with_capacity(geometry.bus_row_count());
    for boundary in 0..=geometry.log_degree as usize {
        let mut source = source_image(geometry, rows, boundary);
        let mut sink = sink_image(geometry, rows, boundary);
        source.sort_unstable();
        sink.sort_unstable();
        if source != sink {
            return Err(BfvTableError::Boundary {
                boundary,
                reason: "preceding writes and following reads are different multisets".to_string(),
            });
        }
        out.extend(source);
    }
    out.sort_unstable();
    Ok(out)
}

fn verify_boundaries(
    geometry: BfvButterflyGeometry,
    rows: &[BfvButterflyRow],
    bus_rows: &[BfvBusRow],
) -> Result<(), BfvTableError> {
    if bus_rows.len() != geometry.bus_row_count() {
        return Err(BfvTableError::Boundary {
            boundary: 0,
            reason: format!(
                "total committed row count {} != exact {}",
                bus_rows.len(),
                geometry.bus_row_count()
            ),
        });
    }
    let mut seen_tags = BTreeSet::new();
    for row in bus_rows {
        let tag = row[0] as usize;
        if tag >= geometry.bus_row_count() {
            return Err(BfvTableError::Boundary {
                boundary: geometry.log_degree as usize + 1,
                reason: format!("tag {tag} is outside every boundary"),
            });
        }
        if !seen_tags.insert(tag) {
            return Err(BfvTableError::Boundary {
                boundary: tag / geometry.degree as usize,
                reason: format!("duplicate canonical tag {tag}"),
            });
        }
    }
    if seen_tags.len() != geometry.bus_row_count() {
        return Err(BfvTableError::Boundary {
            boundary: 0,
            reason: "a canonical boundary tag is omitted".to_string(),
        });
    }

    let n = geometry.degree as usize;
    for boundary in 0..=geometry.log_degree as usize {
        let lo = boundary * n;
        let hi = (boundary + 1) * n;
        let mut committed: Vec<_> = bus_rows
            .iter()
            .copied()
            .filter(|row| lo <= row[0] as usize && (row[0] as usize) < hi)
            .collect();
        let mut source = source_image(geometry, rows, boundary);
        let mut sink = sink_image(geometry, rows, boundary);
        committed.sort_unstable();
        source.sort_unstable();
        sink.sort_unstable();
        if committed != source {
            return Err(BfvTableError::Boundary {
                boundary,
                reason: "committed slice is not the exact source multiset".to_string(),
            });
        }
        if committed != sink {
            return Err(BfvTableError::Boundary {
                boundary,
                reason: "committed slice is not the exact sink multiset".to_string(),
            });
        }
    }
    Ok(())
}

fn limbs3(value: u64) -> Result<[u32; 3], BfvTableError> {
    if value >= RADIX.pow(3) {
        return Err(BfvTableError::Geometry(format!(
            "residue {value} does not fit three radix-2^14 limbs"
        )));
    }
    Ok([
        (value % RADIX) as u32,
        ((value / RADIX) % RADIX) as u32,
        ((value / (RADIX * RADIX)) % RADIX) as u32,
    ])
}

fn encode_radix_limbs<const N: usize>(mut value: u128) -> Result<[u32; N], BfvTableError> {
    let mut limbs = [0u32; N];
    for limb in &mut limbs {
        *limb = (value % u128::from(RADIX)) as u32;
        value /= u128::from(RADIX);
    }
    if value != 0 {
        return Err(BfvTableError::ThresholdTerminal(format!(
            "integer does not fit {N} radix-2^14 limbs"
        )));
    }
    Ok(limbs)
}

fn decode_radix_limbs<const N: usize>(limbs: &[u32; N]) -> Result<u128, BfvTableError> {
    let mut value = 0u128;
    let mut place = 1u128;
    for (index, limb) in limbs.iter().enumerate() {
        if u64::from(*limb) >= RADIX {
            return Err(BfvTableError::ThresholdTerminal(format!(
                "limb {index}={limb} is not a canonical 14-bit value"
            )));
        }
        value = value
            .checked_add(u128::from(*limb) * place)
            .ok_or_else(|| {
                BfvTableError::ThresholdTerminal("radix recomposition overflow".to_string())
            })?;
        place = place
            .checked_mul(u128::from(RADIX))
            .ok_or_else(|| BfvTableError::ThresholdTerminal("radix place overflow".to_string()))?;
    }
    Ok(value)
}

fn validate_terminal_public(
    modulus: u64,
    lambda: u64,
    product: u64,
    h: u64,
    smudge_bits: u32,
) -> Result<(), BfvTableError> {
    if modulus < 3 || modulus >= RADIX.pow(3) || modulus % 2 == 0 {
        return Err(BfvTableError::ThresholdTerminal(
            "q must be an odd canonical three-limb modulus".to_string(),
        ));
    }
    if lambda >= modulus || product >= modulus || h >= modulus {
        return Err(BfvTableError::ThresholdTerminal(
            "lambda, product, and h must be canonical modulo q".to_string(),
        ));
    }
    // Six radix-2^14 limbs hold 84 bits. `2B` must fit because the complement
    // equation materializes it exactly.
    if smudge_bits == 0 || smudge_bits >= 83 {
        return Err(BfvTableError::ThresholdTerminal(
            "smudge_bits must lie in 1..=82 for the six-limb v1 row".to_string(),
        ));
    }
    Ok(())
}

fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut acc = 1u64;
    while exponent != 0 {
        if exponent & 1 == 1 {
            acc = ((acc as u128 * base as u128) % modulus as u128) as u64;
        }
        base = ((base as u128 * base as u128) % modulus as u128) as u64;
        exponent >>= 1;
    }
    acc
}

fn mod_mul(left: u64, right: u64, modulus: u64) -> u64 {
    ((u128::from(left) * u128::from(right)) % u128::from(modulus)) as u64
}

fn mod_inverse_prime(value: u64, modulus: u64) -> u64 {
    mod_pow(value, modulus - 2, modulus)
}

fn conv3(left: [u32; 3], right: [u32; 3], degree: usize) -> i128 {
    let mut out = 0i128;
    for i in 0..3 {
        if degree >= i && degree - i < 3 {
            out += i128::from(left[i]) * i128::from(right[degree - i]);
        }
    }
    out
}

fn product_carries(
    right: u64,
    twiddle: u64,
    product: u64,
    quotient: u64,
    modulus: u64,
) -> [i128; 5] {
    let r = limbs3(right).expect("validated modulus");
    let t = limbs3(twiddle).expect("validated modulus");
    let p = limbs3(product).expect("validated modulus");
    let q = limbs3(quotient).expect("validated quotient");
    let m = limbs3(modulus).expect("validated modulus");
    let mut carries = [0i128; 5];
    for degree in 0..5 {
        let carry_in = if degree == 0 { 0 } else { carries[degree - 1] };
        let residue = if degree < 3 { i128::from(p[degree]) } else { 0 };
        carries[degree] =
            (conv3(r, t, degree) + carry_in - residue - conv3(q, m, degree)) / i128::from(RADIX);
    }
    carries
}

fn add_carries(left: u64, product: u64, output: u64, reduce: u32, modulus: u64) -> [i128; 3] {
    let l = limbs3(left).expect("validated modulus");
    let p = limbs3(product).expect("validated modulus");
    let o = limbs3(output).expect("validated modulus");
    let m = limbs3(modulus).expect("validated modulus");
    let mut carries = [0i128; 3];
    for limb in 0..3 {
        let carry_in = if limb == 0 { 0 } else { carries[limb - 1] };
        carries[limb] = (i128::from(l[limb]) + i128::from(p[limb]) + carry_in
            - i128::from(o[limb])
            - i128::from(reduce) * i128::from(m[limb]))
            / i128::from(RADIX);
    }
    carries
}

fn sub_carries(left: u64, product: u64, output: u64, reduce: u32, modulus: u64) -> [i128; 3] {
    let l = limbs3(left).expect("validated modulus");
    let p = limbs3(product).expect("validated modulus");
    let o = limbs3(output).expect("validated modulus");
    let m = limbs3(modulus).expect("validated modulus");
    let mut carries = [0i128; 3];
    for limb in 0..3 {
        let carry_in = if limb == 0 { 0 } else { carries[limb - 1] };
        carries[limb] = (i128::from(l[limb]) - i128::from(p[limb])
            + carry_in
            + i128::from(reduce) * i128::from(m[limb])
            - i128::from(o[limb]))
            / i128::from(RADIX);
    }
    carries
}

/// Construct the canonical 48-column butterfly rows and normalized transform
/// output for one RNS polynomial.  This is the typed producer for the strict
/// table/boundary carrier; the independent IR2 arithmetic proof remains the
/// authority for the row equations.
pub fn build_bfv_transform_rows(
    geometry: BfvButterflyGeometry,
    input: &[u64],
) -> Result<(Vec<BfvButterflyRow>, Vec<u64>), BfvTableError> {
    geometry.validate()?;
    let n = geometry.degree as usize;
    if input.len() != n {
        return Err(BfvTableError::TransformBoundary(format!(
            "input length {} does not equal degree {n}",
            input.len()
        )));
    }
    if input.iter().any(|value| *value >= geometry.modulus) {
        return Err(BfvTableError::TransformBoundary(
            "input contains a noncanonical residue".to_string(),
        ));
    }
    let mut initial = vec![0u64; n];
    for (index, slot) in initial.iter_mut().enumerate() {
        let source = index.reverse_bits() >> (usize::BITS - geometry.log_degree as u32);
        *slot = if geometry.direction == 0 {
            mod_mul(
                input[source],
                mod_pow(geometry.psi, source as u64, geometry.modulus),
                geometry.modulus,
            )
        } else {
            input[source]
        };
    }
    let mut states = vec![initial];
    let butterfly_root = if geometry.direction == 0 {
        geometry.psi
    } else {
        mod_inverse_prime(geometry.psi, geometry.modulus)
    };
    for stage in 0..geometry.log_degree as usize {
        let mut next = states[stage].clone();
        let half = 1usize << stage;
        let len = 2 * half;
        for butterfly in 0..n / 2 {
            let left = (butterfly / half) * len + butterfly % half;
            let right = left + half;
            let twiddle_index = (butterfly % half) * (n / len);
            let twiddle = mod_pow(butterfly_root, 2 * twiddle_index as u64, geometry.modulus);
            let product = ((states[stage][right] as u128 * twiddle as u128)
                % geometry.modulus as u128) as u64;
            next[left] = (states[stage][left] + product) % geometry.modulus;
            next[right] = (states[stage][left] + geometry.modulus - product) % geometry.modulus;
        }
        states.push(next);
    }

    let mut rows = Vec::with_capacity(geometry.main_row_count());
    for stage in 0..geometry.log_degree as usize {
        for butterfly in 0..n / 2 {
            let schedule = schedule_row(geometry, stage, butterfly).expect("fixed geometry");
            let left_index = schedule[5] as usize;
            let right_index = schedule[6] as usize;
            let left = states[stage][left_index];
            let right = states[stage][right_index];
            let twiddle = u64::from(schedule[8])
                + u64::from(schedule[9]) * RADIX
                + u64::from(schedule[10]) * RADIX * RADIX;
            let wide_product = right as u128 * twiddle as u128;
            let product = (wide_product % geometry.modulus as u128) as u64;
            let quotient = ((wide_product - product as u128) / geometry.modulus as u128) as u64;
            let left_output = (left + product) % geometry.modulus;
            let right_output = (left + geometry.modulus - product) % geometry.modulus;
            let add_reduce = u32::from(geometry.modulus <= left + product);
            let sub_reduce = u32::from(left < product);
            let pc = product_carries(right, twiddle, product, quotient, geometry.modulus);
            let ac = add_carries(left, product, left_output, add_reduce, geometry.modulus);
            let sc = sub_carries(left, product, right_output, sub_reduce, geometry.modulus);

            let mut row = [0u32; BFV_BUTTERFLY_TRACE_WIDTH];
            row[..8].copy_from_slice(&schedule[..8]);
            for (base, value) in [
                (LEFT_INPUT, left),
                (RIGHT_INPUT, right),
                (TWIDDLE, twiddle),
                (TWIDDLED_RIGHT, product),
                (LEFT_OUTPUT, left_output),
                (RIGHT_OUTPUT, right_output),
                (PRODUCT_QUOTIENT, quotient),
            ] {
                row[base..base + 3].copy_from_slice(&limbs3(value).expect("fixed geometry"));
            }
            row[ADD_REDUCE] = add_reduce;
            row[SUB_REDUCE] = sub_reduce;
            for (base, carries) in [
                (PRODUCT_CARRY, pc.as_slice()),
                (ADD_CARRY, ac.as_slice()),
                (SUB_CARRY, sc.as_slice()),
            ] {
                for (offset, carry) in carries.iter().enumerate() {
                    row[base + offset] = (carry + CARRY_SHIFT) as u32;
                }
            }
            row[READ_LEFT_TAG..=LAST_STAGE].copy_from_slice(&schedule[11..]);
            rows.push(row);
        }
    }
    let mut output = states
        .last()
        .expect("one initial state plus at least one stage")
        .clone();
    if geometry.direction == 1 {
        let psi_inverse = mod_inverse_prime(geometry.psi, geometry.modulus);
        let n_inverse = mod_inverse_prime(geometry.degree as u64, geometry.modulus);
        for (index, value) in output.iter_mut().enumerate() {
            let scale = mod_mul(
                mod_pow(psi_inverse, index as u64, geometry.modulus),
                n_inverse,
                geometry.modulus,
            );
            *value = mod_mul(*value, scale, geometry.modulus);
        }
    }
    Ok((rows, output))
}

/// Independent Rust construction of the exact Lean q0/N=8 witness. The focused KAT pins
/// its canonical commitment to the value computed by Lean's `honestRows` evaluator.
pub fn q0_n8_lean_rows() -> Vec<BfvButterflyRow> {
    let geometry = BfvButterflyGeometry::Q0_N8;
    let input = (0..geometry.degree as usize)
        .map(|index| (3 * index * index + 5 * index + 7) as u64 % geometry.modulus)
        .collect::<Vec<_>>();
    build_bfv_transform_rows(geometry, &input)
        .expect("fixed Lean q0/N8 geometry")
        .0
}

#[cfg(test)]
mod tests {
    use super::*;

    // Computed by Lean from
    // `honestRows.map (fun row => (List.range TRACE_WIDTH).map row)` using the
    // canonical `commit_main_rows` byte encoding. This pins the independent Rust builder
    // to the executable q0/N=8 witness, not merely to another Rust implementation.
    const LEAN_Q0_N8_MAIN_COMMITMENT: [u8; 32] = [
        159, 129, 79, 87, 104, 101, 175, 93, 191, 227, 154, 18, 108, 157, 215, 113, 11, 138, 44,
        24, 200, 47, 233, 235, 34, 252, 227, 1, 54, 214, 11, 90,
    ];
    const BFV_Q0_N8_DESCRIPTOR_HEADER: &str = concat!(
        "{\"name\":\"private-book-bfv-odd-ntt-butterfly-q0-n8::exact-48-v1\",",
        "\"ir\":2,\"trace_width\":48,\"public_input_count\":0,"
    );
    const LEAN_Q0_N8_ROWS: [[u32; 48]; 12] = [
        [
            0, 0, 0, 0, 0, 0, 1, 0, 7, 0, 0, 1218, 3648, 52, 1, 0, 0, 1218, 3648, 52, 1225, 3648,
            52, 6982, 12731, 203, 0, 0, 0, 0, 1, 32768, 32768, 32768, 32768, 32768, 32768, 32768,
            32768, 32768, 32768, 32768, 0, 1, 8, 9, 1, 0,
        ],
        [
            0, 0, 1, 0, 0, 2, 3, 0, 9683, 514, 151, 1129, 15635, 211, 1, 0, 0, 1129, 15635, 211,
            2619, 16154, 106, 363, 1259, 195, 0, 0, 0, 1, 1, 32768, 32768, 32768, 32768, 32768,
            32768, 32767, 32768, 32769, 32768, 32768, 2, 3, 10, 11, 1, 0,
        ],
        [
            0, 0, 2, 0, 0, 4, 5, 0, 7500, 10490, 216, 9515, 14846, 26, 1, 0, 0, 9515, 14846, 26,
            631, 8953, 243, 14369, 12027, 189, 0, 0, 0, 0, 0, 32768, 32768, 32768, 32768, 32768,
            32769, 32769, 32768, 32767, 32767, 32768, 4, 5, 12, 13, 1, 0,
        ],
        [
            0, 0, 3, 0, 0, 6, 7, 0, 12549, 14134, 122, 3238, 4540, 183, 1, 0, 0, 3238, 4540, 183,
            7594, 2295, 50, 1120, 9590, 195, 0, 0, 0, 1, 1, 32768, 32768, 32768, 32768, 32768,
            32768, 32768, 32768, 32769, 32769, 32768, 6, 7, 14, 15, 1, 0,
        ],
        [
            0, 1, 0, 0, 0, 0, 2, 0, 1225, 3648, 52, 2619, 16154, 106, 1, 0, 0, 2619, 16154, 106,
            3844, 3418, 159, 6799, 3873, 201, 0, 0, 0, 0, 1, 32768, 32768, 32768, 32768, 32768,
            32768, 32769, 32768, 32768, 32768, 32768, 8, 10, 16, 18, 0, 0,
        ],
        [
            0, 1, 1, 0, 0, 1, 3, 2, 6982, 12731, 203, 363, 1259, 195, 2747, 9660, 24, 4401, 8990,
            29, 11383, 5337, 233, 2581, 3741, 174, 9720, 12087, 18, 0, 0, 27968, 17431, 21299,
            32678, 32768, 32768, 32769, 32768, 32768, 32768, 32768, 9, 11, 17, 19, 0, 0,
        ],
        [
            0, 1, 2, 0, 0, 4, 6, 0, 631, 8953, 243, 7594, 2295, 50, 1, 0, 0, 7594, 2295, 50, 32,
            11253, 37, 9421, 6657, 193, 0, 0, 0, 1, 0, 32768, 32768, 32768, 32768, 32768, 32768,
            32767, 32768, 32767, 32768, 32768, 12, 14, 20, 22, 0, 0,
        ],
        [
            0, 1, 3, 0, 0, 5, 7, 2, 14369, 12027, 189, 1120, 9590, 195, 2747, 9660, 24, 7631,
            10626, 109, 13807, 6274, 43, 6738, 1401, 80, 13393, 12887, 18, 1, 0, 26258, 15202,
            25355, 32678, 32768, 32768, 32768, 32768, 32768, 32768, 32768, 13, 15, 21, 23, 0, 0,
        ],
        [
            0, 2, 0, 0, 0, 0, 4, 0, 3844, 3418, 159, 32, 11253, 37, 1, 0, 0, 32, 11253, 37, 3876,
            14671, 196, 3812, 8549, 121, 0, 0, 0, 0, 0, 32768, 32768, 32768, 32768, 32768, 32768,
            32768, 32768, 32768, 32767, 32768, 16, 20, 24, 28, 0, 1,
        ],
        [
            0, 2, 1, 0, 0, 1, 5, 1, 11383, 5337, 233, 13807, 6274, 43, 10786, 16, 67, 11951, 11723,
            147, 15141, 681, 125, 15816, 9997, 85, 4367, 5805, 11, 1, 0, 39673, 29643, 26982,
            32692, 32768, 32768, 32768, 32768, 32767, 32767, 32768, 17, 21, 25, 29, 0, 1,
        ],
        [
            0, 2, 2, 0, 0, 2, 6, 2, 6799, 3873, 201, 9421, 6657, 193, 2747, 9660, 24, 14583, 4611,
            47, 4998, 8485, 248, 8600, 15645, 153, 10952, 9458, 18, 0, 0, 28870, 23760, 27104,
            32726, 32768, 32769, 32768, 32768, 32767, 32767, 32768, 18, 22, 26, 30, 0, 1,
        ],
        [
            0, 2, 3, 0, 0, 3, 7, 3, 2581, 3741, 174, 6738, 1401, 80, 7522, 9824, 45, 15411, 6283,
            3, 1608, 10025, 177, 3554, 13841, 170, 305, 4344, 14, 0, 0, 35708, 34974, 29309, 32738,
            32768, 32769, 32768, 32768, 32767, 32767, 32768, 19, 23, 27, 31, 0, 1,
        ],
    ];
    fn descriptor_commitment() -> [u8; 32] {
        bfv_q0_n8_descriptor_commitment()
            .expect("checked-in Lean q0/N8 descriptor parses and canonicalizes")
    }

    fn honest() -> (Vec<BfvButterflyRow>, BfvFaithfulTableClaim) {
        let rows = q0_n8_lean_rows();
        let claim = BfvFaithfulTableClaim::prove_public_trace(
            descriptor_commitment(),
            BfvButterflyGeometry::Q0_N8,
            &rows,
        )
        .expect("honest q0/N8 tables");
        (rows, claim)
    }

    fn refresh_commitments(claim: &mut BfvFaithfulTableClaim) {
        claim.schedule_commitment = commit_schedule_rows(&claim.schedule_rows);
        claim.bus_commitment = commit_bus_rows(&claim.bus_rows);
    }

    #[test]
    fn lean_q0_n8_differential_and_strict_wire_roundtrip() {
        let (rows, claim) = honest();
        assert_eq!(rows.as_slice(), &LEAN_Q0_N8_ROWS);
        assert_eq!(commit_main_rows(&rows), LEAN_Q0_N8_MAIN_COMMITMENT);
        let bytes = claim.to_bytes();
        let decoded = BfvFaithfulTableClaim::from_bytes(&bytes).expect("strict decode");
        let verified = decoded
            .verify(descriptor_commitment(), &rows)
            .expect("exact table verification");
        assert_eq!(verified.geometry(), BfvButterflyGeometry::Q0_N8);
        assert_eq!(verified.main_trace_commitment(), commit_main_rows(&rows));
    }

    #[test]
    fn q0_n8_identity_is_canonical_typed_semantics_not_json_or_display_text() {
        let descriptor =
            parse_vm_descriptor2(BFV_Q0_N8_DESCRIPTOR_JSON).expect("Lean q0/N8 JSON parses");

        // Move the first four top-level fields while preserving every nested
        // Lean-emitted object byte-for-byte.  The descriptor parser's nested
        // tagged-object grammar is deliberately ordered, so a generic JSON
        // reserializer would test a different property.
        let body = BFV_Q0_N8_DESCRIPTOR_JSON
            .strip_prefix(BFV_Q0_N8_DESCRIPTOR_HEADER)
            .expect("q0/N8 descriptor header remains recognized");
        let alternate_json = format!(
            "{{\n  \"public_input_count\" : 0,\n  \"trace_width\" : 48,\n  \
             \"name\" : \"{BFV_Q0_N8_DESCRIPTOR_NAME}\",\n  \"ir\" : 2,\n  {body}\n"
        );
        assert_ne!(alternate_json, BFV_Q0_N8_DESCRIPTOR_JSON);
        let alternate = parse_vm_descriptor2(&alternate_json).expect("alternate JSON parses");
        assert_eq!(alternate, descriptor);
        assert_eq!(
            commit_bfv_butterfly_typed_descriptor(&alternate).unwrap(),
            descriptor_commitment()
        );

        // The historical display-name digest is not relation identity.
        let display_name_digest =
            commit_bfv_butterfly_descriptor(BFV_Q0_N8_DESCRIPTOR_NAME.as_bytes());
        assert_ne!(display_name_digest, descriptor_commitment());

        // Conversely, a typed semantic mutation changes identity and cannot
        // authorize a claim committed to the exact Lean relation.
        let mut typed_mutation = descriptor;
        typed_mutation.trace_width += 1;
        let mutated = commit_bfv_butterfly_typed_descriptor(&typed_mutation).unwrap();
        assert_ne!(mutated, descriptor_commitment());
        let (rows, claim) = honest();
        assert!(matches!(
            claim.verify(mutated, &rows),
            Err(BfvTableError::DescriptorCommitment)
        ));
    }

    #[test]
    fn duplicate_schedule_and_bus_rows_refuse_after_recommit() {
        let (rows, claim) = honest();

        let mut duplicate_schedule = claim.clone();
        duplicate_schedule
            .schedule_rows
            .push(duplicate_schedule.schedule_rows[0]);
        refresh_commitments(&mut duplicate_schedule);
        assert!(matches!(
            duplicate_schedule.verify(descriptor_commitment(), &rows),
            Err(BfvTableError::Schedule(_))
        ));

        let mut duplicate_bus = claim;
        duplicate_bus.bus_rows.push(duplicate_bus.bus_rows[0]);
        refresh_commitments(&mut duplicate_bus);
        assert!(matches!(
            duplicate_bus.verify(descriptor_commitment(), &rows),
            Err(BfvTableError::Boundary { .. })
        ));
    }

    #[test]
    fn same_length_duplicate_omission_and_substitution_refuse() {
        let (rows, claim) = honest();

        let mut schedule_duplicate = claim.clone();
        schedule_duplicate.schedule_rows[7] = schedule_duplicate.schedule_rows[0];
        refresh_commitments(&mut schedule_duplicate);
        assert!(
            schedule_duplicate
                .verify(descriptor_commitment(), &rows)
                .is_err()
        );

        let mut bus_duplicate = claim.clone();
        bus_duplicate.bus_rows[7] = bus_duplicate.bus_rows[0];
        refresh_commitments(&mut bus_duplicate);
        assert!(
            bus_duplicate
                .verify(descriptor_commitment(), &rows)
                .is_err()
        );

        let mut bus_substitution = claim;
        bus_substitution.bus_rows[9][1] ^= 1;
        refresh_commitments(&mut bus_substitution);
        assert!(matches!(
            bus_substitution.verify(descriptor_commitment(), &rows),
            Err(BfvTableError::Boundary { .. })
        ));
    }

    #[test]
    fn trace_descriptor_and_wire_mutations_refuse() {
        let (rows, claim) = honest();

        let mut changed_rows = rows.clone();
        changed_rows[4][LEFT_INPUT] ^= 1;
        assert!(
            claim
                .verify(descriptor_commitment(), &changed_rows)
                .is_err()
        );
        assert!(matches!(
            claim.verify([0x43; 32], &rows),
            Err(BfvTableError::DescriptorCommitment)
        ));

        let mut corrupt = claim.to_bytes();
        corrupt[120] ^= 1;
        assert!(matches!(
            BfvFaithfulTableClaim::from_bytes(&corrupt),
            Err(BfvTableError::Wire(_))
        ));
        let mut trailing = claim.to_bytes();
        trailing.push(0);
        assert!(matches!(
            BfvFaithfulTableClaim::from_bytes(&trailing),
            Err(BfvTableError::Wire(_))
        ));
    }

    #[test]
    fn arithmetic_forgery_refuses_before_it_can_acquire_table_authority() {
        let mut forged_rows = q0_n8_lean_rows();
        // TWIDDLED_RIGHT is deliberately absent from the schedule and bus
        // tuples.  Before native arithmetic replay this mutation therefore
        // survived every carrier check after the claim was recomputed.
        forged_rows[0][TWIDDLED_RIGHT] ^= 1;
        assert!(matches!(
            BfvFaithfulTableClaim::prove_public_trace(
                descriptor_commitment(),
                BfvButterflyGeometry::Q0_N8,
                &forged_rows,
            ),
            Err(BfvTableError::MainTrace(_))
        ));
    }

    #[test]
    fn production_q0_geometry_builds_the_exact_schedule_shape() {
        let geometry = BfvButterflyGeometry::Q0_N4096;
        geometry.validate().expect("Lean-pinned production root");
        let schedule = canonical_schedule(geometry).expect("production schedule");
        assert_eq!(schedule.len(), 12 * 2048);
        assert_eq!(geometry.bus_row_count(), 13 * 4096);
        assert_eq!(schedule.first().unwrap()[STAGE], 0);
        assert_eq!(schedule.first().unwrap()[BUTTERFLY], 0);
        assert_eq!(schedule.last().unwrap()[STAGE], 11);
        assert_eq!(schedule.last().unwrap()[BUTTERFLY], 2047);
        assert_eq!(schedule.last().unwrap()[14], 13 * 4096 - 1);
    }

    #[test]
    fn table_faithful_transform_boundaries_bind_twist_and_inverse_normalization() {
        let input = (0..8)
            .map(|index| (97 * index * index + 31 * index + 11) as u64)
            .collect::<Vec<_>>();
        let (forward_rows, spectrum) =
            build_bfv_transform_rows(BfvButterflyGeometry::Q0_N8, &input).expect("forward rows");
        let forward_descriptor = commit_bfv_butterfly_descriptor(b"q0-n8-forward-bound-v1");
        let forward_claim = BfvFaithfulTableClaim::prove_public_trace(
            forward_descriptor,
            BfvButterflyGeometry::Q0_N8,
            &forward_rows,
        )
        .expect("forward faithful tables");
        forward_claim
            .verify_boundaries(forward_descriptor, &forward_rows, &input, &spectrum)
            .expect("forward ingress and egress bind");

        let (inverse_rows, roundtrip) =
            build_bfv_transform_rows(BfvButterflyGeometry::Q0_N8_INVERSE, &spectrum)
                .expect("inverse rows");
        assert_eq!(roundtrip, input, "odd NTT inverse normalization");
        let inverse_descriptor = commit_bfv_butterfly_descriptor(b"q0-n8-inverse-bound-v1");
        let inverse_claim = BfvFaithfulTableClaim::prove_public_trace(
            inverse_descriptor,
            BfvButterflyGeometry::Q0_N8_INVERSE,
            &inverse_rows,
        )
        .expect("inverse faithful tables");
        let verified = inverse_claim
            .verify_boundaries(inverse_descriptor, &inverse_rows, &spectrum, &roundtrip)
            .expect("inverse ingress and normalized egress bind");
        assert_ne!(verified.input_commitment(), verified.output_commitment());

        let mut wrong_input = spectrum.clone();
        wrong_input[3] += 1;
        assert!(matches!(
            inverse_claim.verify_boundaries(
                inverse_descriptor,
                &inverse_rows,
                &wrong_input,
                &roundtrip,
            ),
            Err(BfvTableError::TransformBoundary(_))
        ));
        let mut wrong_normalization = roundtrip.clone();
        wrong_normalization[5] += 1;
        assert!(matches!(
            inverse_claim.verify_boundaries(
                inverse_descriptor,
                &inverse_rows,
                &spectrum,
                &wrong_normalization,
            ),
            Err(BfvTableError::TransformBoundary(_))
        ));
    }

    #[test]
    fn production_q0_boundary_carrier_covers_every_real_coefficient() {
        let geometry = BfvButterflyGeometry::Q0_N4096;
        let input = (0..geometry.degree as usize)
            .map(|index| {
                (index as u64 * 1_000_003 + (index as u64).pow(2) * 17 + 29) % geometry.modulus
            })
            .collect::<Vec<_>>();
        let (rows, output) = build_bfv_transform_rows(geometry, &input).expect("production rows");
        assert_eq!(rows.len(), 12 * 2048);
        let descriptor = commit_bfv_butterfly_descriptor(b"q0-n4096-forward-bound-v1");
        let claim = BfvFaithfulTableClaim::prove_public_trace(descriptor, geometry, &rows)
            .expect("production exact boundary tables");
        claim
            .verify_boundaries(descriptor, &rows, &input, &output)
            .expect("all 4096 ingress and egress residues bind");
    }

    #[test]
    fn threshold_terminal_q0_limb_relation_is_exact_and_mutation_strict() {
        let q = BfvButterflyGeometry::Q0_N4096.modulus;
        let lambda = 41_337_119_221u64;
        let product = 62_911_771_003u64;
        let smudge = (1i128 << 79) + 17_123;
        let unreduced = i128::from(lambda) * i128::from(product) + smudge;
        let h = unreduced.rem_euclid(i128::from(q)) as u64;
        let row = ThresholdDecryptTerminalRow::from_values(q, lambda, product, smudge, h, 80)
            .expect("honest production-q0 terminal row");
        row.verify(q, 80).expect("exact terminal relation");

        let mut changed_product = row.clone();
        changed_product.product[0] += 1;
        assert!(matches!(
            changed_product.verify(q, 80),
            Err(BfvTableError::ThresholdTerminal(_))
        ));

        let mut changed_smudge_same_interval = row.clone();
        changed_smudge_same_interval.smudge_shift[0] += 1;
        changed_smudge_same_interval.smudge_complement[0] -= 1;
        assert!(matches!(
            changed_smudge_same_interval.verify(q, 80),
            Err(BfvTableError::ThresholdTerminal(_))
        ));

        let mut changed_quotient = row.clone();
        changed_quotient.quotient_shift[0] += 1;
        assert!(matches!(
            changed_quotient.verify(q, 80),
            Err(BfvTableError::ThresholdTerminal(_))
        ));

        let mut noncanonical_limb = row;
        noncanonical_limb.h[0] = RADIX as u32;
        assert!(matches!(
            noncanonical_limb.verify(q, 80),
            Err(BfvTableError::ThresholdTerminal(_))
        ));
    }
}
