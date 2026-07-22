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

/// The BabyBear prime. Every value transported into the IR2 table must be canonical.
pub const BABYBEAR_MODULUS: u32 = 2_013_265_921;

/// Exact width of `Market.PrivateBookBfvButterflyAir`'s main row.
pub const BFV_BUTTERFLY_TRACE_WIDTH: usize = 48;
/// Exact width of the canonical schedule lookup tuple.
pub const BFV_BUTTERFLY_SCHEDULE_WIDTH: usize = 17;
/// Exact width of one boundary-bus row: tag plus three radix-2^14 limbs.
pub const BFV_BUTTERFLY_BUS_WIDTH: usize = 4;

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
    /// Main trace shape/order/canonical-field failure.
    MainTrace(String),
    /// A committed digest does not match its canonical rows.
    Commitment(&'static str),
    /// The schedule table differs from the exact family schedule.
    Schedule(String),
    /// A boundary table is not the exact source and sink multiset.
    Boundary { boundary: usize, reason: String },
}

impl std::fmt::Display for BfvTableError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Geometry(s) => write!(f, "BFV butterfly geometry: {s}"),
            Self::Wire(s) => write!(f, "BFV faithful-table wire: {s}"),
            Self::DescriptorCommitment => write!(f, "BFV descriptor commitment mismatch"),
            Self::MainTrace(s) => write!(f, "BFV main trace: {s}"),
            Self::Commitment(which) => write!(f, "BFV {which} commitment mismatch"),
            Self::Schedule(s) => write!(f, "BFV schedule table: {s}"),
            Self::Boundary { boundary, reason } => {
                write!(f, "BFV boundary {boundary}: {reason}")
            }
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

/// Domain-separated commitment to the exact Lean-emitted descriptor bytes consumed by IR2.
/// Callers should derive the relation identity with this function rather than inventing a
/// display-name digest.
pub fn commit_bfv_butterfly_descriptor(descriptor_bytes: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg/bfv-butterfly/descriptor/v1");
    h.update(&(descriptor_bytes.len() as u64).to_le_bytes());
    h.update(descriptor_bytes);
    *h.finalize().as_bytes()
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
    let twiddle = mod_pow(geometry.psi, 2 * twiddle_index as u64, geometry.modulus);
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

/// Independent Rust construction of the exact Lean q0/N=8 witness. The focused KAT pins
/// its canonical commitment to the value computed by Lean's `honestRows` evaluator.
pub fn q0_n8_lean_rows() -> Vec<BfvButterflyRow> {
    let geometry = BfvButterflyGeometry::Q0_N8;
    let n = geometry.degree as usize;
    let mut initial = vec![0u64; n];
    for (index, slot) in initial.iter_mut().enumerate() {
        let source = index.reverse_bits() >> (usize::BITS - geometry.log_degree as u32);
        let input = (3 * source * source + 5 * source + 7) as u64 % geometry.modulus;
        *slot = ((input as u128 * mod_pow(geometry.psi, source as u64, geometry.modulus) as u128)
            % geometry.modulus as u128) as u64;
    }
    let mut states = vec![initial];
    for stage in 0..geometry.log_degree as usize {
        let mut next = states[stage].clone();
        let half = 1usize << stage;
        let len = 2 * half;
        for butterfly in 0..n / 2 {
            let left = (butterfly / half) * len + butterfly % half;
            let right = left + half;
            let twiddle_index = (butterfly % half) * (n / len);
            let twiddle = mod_pow(geometry.psi, 2 * twiddle_index as u64, geometry.modulus);
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
    rows
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
        commit_bfv_butterfly_descriptor(b"private-book-bfv-odd-ntt-butterfly-q0-n8::exact-48-v1")
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
}
