//! Exact certificate for uniform-price clearing and deterministic allocation.
//!
//! [`crate::clearing::clear`] and [`crate::clearing::allocate`] are finders.  In
//! particular, [`crate::clearing::Allocation::validate`] checks conservation,
//! caps, and individual rationality, but deliberately accepts more than one
//! allocation: moving a unit between two active orders can still pass it.  A
//! relying party that needs the specified largest-remainder allocation must not
//! treat that weaker predicate as an optimization certificate.
//!
//! This module supplies the verify-not-find boundary.  A worker may emit a
//! [`UniformAllocationCertificate`], but [`verify_uniform_allocation`] decides
//! acceptance independently.  It recomputes, without calling `fold_curves`,
//! `crossing`, `allocate`, or `Allocation::validate`:
//!
//! * the caller-supplied price-grid size (never a certificate-selected grid);
//! * the volume-maximising price, including the lowest-index tie rule;
//! * the exact cleared volume;
//! * inactivity and per-order caps;
//! * both side sums at that volume; and
//! * the unique integer pro-rata allocation selected by largest remainder,
//!   with original order index as the deterministic tie-break.
//!
//! The side witness is compact: it carries the active total, floor sum, bonus
//! count, and (when bonuses exist) the last winning remainder/index.  The
//! verifier checks that every bonus fill lies at or above that cutoff and every
//! non-bonus lies below it.  This is a certificate of the current public
//! allocation rule, not a privacy mechanism.  The source orders remain inputs
//! to the checker; a shielded deployment must evaluate the same relation under
//! a hiding proof and bind it to the private order root.

use crate::clearing::{Allocation, Clearing, Order, Side};

const CERTIFICATE_MAGIC: &[u8; 8] = b"FHUAC001";
pub const UNIFORM_ALLOCATION_CERTIFICATE_VERSION: u16 = 1;
pub const MAX_UNIFORM_ALLOCATION_ORDERS: usize = 1_000_000;
pub const MAX_UNIFORM_PRICE_LEVELS: usize = 65_536;
pub const MAX_UNIFORM_VERIFY_TERMS: usize = 64 * 1024 * 1024;

const FIXED_HEADER_LEN: usize = 8 + 2 + 4 + 4 + 8 + 4;
const SIDE_WITNESS_LEN: usize = 8 + 8 + 4 + 1 + 4 + 8;
const FIXED_WIRE_LEN: usize = FIXED_HEADER_LEN + 2 * SIDE_WITNESS_LEN;
pub const MAX_UNIFORM_ALLOCATION_CERTIFICATE_BYTES: usize =
    FIXED_WIRE_LEN + MAX_UNIFORM_ALLOCATION_ORDERS * 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BonusCutoff {
    order_index: u32,
    remainder: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct RationWitness {
    active_total: u64,
    floor_sum: u64,
    bonus_count: u32,
    cutoff: Option<BonusCutoff>,
}

/// Canonical worker output for one uniform-price clearing.
///
/// Fields are private so normal callers cannot accidentally bless a partially
/// checked carrier.  Untrusted bytes enter through [`Self::from_wire_bytes`]
/// and gain authority only through [`verify_uniform_allocation`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniformAllocationCertificate {
    version: u16,
    k: u32,
    clearing_price: u32,
    cleared_volume: u64,
    fills: Vec<u64>,
    bid: RationWitness,
    ask: RationWitness,
}

/// Capability produced only after the independent exact checker accepts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedUniformAllocation {
    k: u32,
    clearing_price: u32,
    cleared_volume: u64,
    fills: Vec<u64>,
}

impl VerifiedUniformAllocation {
    pub fn price_levels(&self) -> u32 {
        self.k
    }

    pub fn clearing_price(&self) -> u32 {
        self.clearing_price
    }

    pub fn cleared_volume(&self) -> u64 {
        self.cleared_volume
    }

    pub fn fills(&self) -> &[u64] {
        &self.fills
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UniformAllocationCertificateError {
    InvalidPriceLevelCount,
    TooManyPriceLevels {
        actual: usize,
        maximum: usize,
    },
    TooManyOrders {
        actual: usize,
        maximum: usize,
    },
    VerificationWorkLimit {
        actual: usize,
        maximum: usize,
    },
    DimensionOverflow,
    ShapeMismatch {
        orders: usize,
        fills: usize,
    },
    AggregateOverflow,
    MalformedWire,
    WireTooLarge {
        actual: usize,
        maximum: usize,
    },
    UnsupportedVersion {
        found: u16,
    },
    WrongPriceLevelCount {
        expected: u32,
        found: u32,
    },
    WrongClearingPrice {
        expected: u32,
        found: u32,
    },
    WrongClearedVolume {
        expected: u64,
        found: u64,
    },
    ActiveTotalMismatch {
        side: Side,
        expected: u64,
        found: u64,
    },
    FloorSumMismatch {
        side: Side,
        expected: u64,
        found: u64,
    },
    BonusCountMismatch {
        side: Side,
        expected: u32,
        found: u32,
    },
    CutoffMismatch {
        side: Side,
    },
    TargetExceedsActive {
        side: Side,
        target: u64,
        active: u64,
    },
    InactiveFill {
        index: usize,
    },
    FillExceedsQuantity {
        index: usize,
        quantity: u64,
        fill: u64,
    },
    NonCanonicalFill {
        index: usize,
        expected: u64,
        found: u64,
    },
    SideVolumeMismatch {
        side: Side,
        expected: u64,
        found: u64,
    },
}

impl std::fmt::Display for UniformAllocationCertificateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for UniformAllocationCertificateError {}

impl UniformAllocationCertificate {
    /// Package one solver result.  This constructs certificate witnesses but
    /// does not confer authority; callers must still run
    /// [`verify_uniform_allocation`].
    pub fn from_solver_output(
        orders: &[Order],
        clearing: &Clearing,
        allocation: &Allocation,
    ) -> Result<Self, UniformAllocationCertificateError> {
        validate_dimensions(orders.len(), clearing.k)?;
        if allocation.fills.len() != orders.len() {
            return Err(UniformAllocationCertificateError::ShapeMismatch {
                orders: orders.len(),
                fills: allocation.fills.len(),
            });
        }
        let k = u32::try_from(clearing.k)
            .map_err(|_| UniformAllocationCertificateError::DimensionOverflow)?;
        let clearing_price = u32::try_from(clearing.clearing_price)
            .map_err(|_| UniformAllocationCertificateError::DimensionOverflow)?;
        let (bid, ask) = if clearing.cleared_volume == 0 {
            (RationWitness::default(), RationWitness::default())
        } else {
            (
                build_side_witness(
                    orders,
                    &allocation.fills,
                    Side::Bid,
                    clearing_price,
                    clearing.cleared_volume,
                )?,
                build_side_witness(
                    orders,
                    &allocation.fills,
                    Side::Ask,
                    clearing_price,
                    clearing.cleared_volume,
                )?,
            )
        };
        Ok(Self {
            version: UNIFORM_ALLOCATION_CERTIFICATE_VERSION,
            k,
            clearing_price,
            cleared_volume: clearing.cleared_volume,
            fills: allocation.fills.clone(),
            bid,
            ask,
        })
    }

    pub fn price_levels(&self) -> u32 {
        self.k
    }

    pub fn clearing_price(&self) -> u32 {
        self.clearing_price
    }

    pub fn cleared_volume(&self) -> u64 {
        self.cleared_volume
    }

    pub fn fills(&self) -> &[u64] {
        &self.fills
    }

    /// Strict, canonical binary encoding.  It is a transport representation,
    /// not an authentication claim; an outer protocol must bind these bytes to
    /// its request/session before invoking the checker.
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, UniformAllocationCertificateError> {
        validate_dimensions(self.fills.len(), self.k as usize)?;
        if self.version != UNIFORM_ALLOCATION_CERTIFICATE_VERSION {
            return Err(UniformAllocationCertificateError::UnsupportedVersion {
                found: self.version,
            });
        }
        let count = u32::try_from(self.fills.len())
            .map_err(|_| UniformAllocationCertificateError::DimensionOverflow)?;
        let mut out = Vec::with_capacity(FIXED_WIRE_LEN + self.fills.len() * 8);
        out.extend_from_slice(CERTIFICATE_MAGIC);
        out.extend_from_slice(&self.version.to_be_bytes());
        out.extend_from_slice(&self.k.to_be_bytes());
        out.extend_from_slice(&self.clearing_price.to_be_bytes());
        out.extend_from_slice(&self.cleared_volume.to_be_bytes());
        out.extend_from_slice(&count.to_be_bytes());
        encode_side_witness(&mut out, self.bid);
        encode_side_witness(&mut out, self.ask);
        for fill in &self.fills {
            out.extend_from_slice(&fill.to_be_bytes());
        }
        Ok(out)
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, UniformAllocationCertificateError> {
        if bytes.len() > MAX_UNIFORM_ALLOCATION_CERTIFICATE_BYTES {
            return Err(UniformAllocationCertificateError::WireTooLarge {
                actual: bytes.len(),
                maximum: MAX_UNIFORM_ALLOCATION_CERTIFICATE_BYTES,
            });
        }
        if bytes.len() < FIXED_WIRE_LEN {
            return Err(UniformAllocationCertificateError::MalformedWire);
        }
        let mut cursor = Cursor::new(bytes);
        if cursor.take::<8>()? != *CERTIFICATE_MAGIC {
            return Err(UniformAllocationCertificateError::MalformedWire);
        }
        let version = u16::from_be_bytes(cursor.take::<2>()?);
        if version != UNIFORM_ALLOCATION_CERTIFICATE_VERSION {
            return Err(UniformAllocationCertificateError::UnsupportedVersion { found: version });
        }
        let k = u32::from_be_bytes(cursor.take::<4>()?);
        let clearing_price = u32::from_be_bytes(cursor.take::<4>()?);
        let cleared_volume = u64::from_be_bytes(cursor.take::<8>()?);
        let count_u32 = u32::from_be_bytes(cursor.take::<4>()?);
        let count = usize::try_from(count_u32)
            .map_err(|_| UniformAllocationCertificateError::DimensionOverflow)?;
        validate_dimensions(count, k as usize)?;
        let expected_len = FIXED_WIRE_LEN
            .checked_add(
                count
                    .checked_mul(8)
                    .ok_or(UniformAllocationCertificateError::DimensionOverflow)?,
            )
            .ok_or(UniformAllocationCertificateError::DimensionOverflow)?;
        if expected_len != bytes.len() {
            return Err(UniformAllocationCertificateError::MalformedWire);
        }
        let bid = decode_side_witness(&mut cursor)?;
        let ask = decode_side_witness(&mut cursor)?;
        let mut fills = Vec::with_capacity(count);
        for _ in 0..count {
            fills.push(u64::from_be_bytes(cursor.take::<8>()?));
        }
        if !cursor.is_finished() {
            return Err(UniformAllocationCertificateError::MalformedWire);
        }
        let certificate = Self {
            version,
            k,
            clearing_price,
            cleared_volume,
            fills,
            bid,
            ask,
        };
        if certificate.to_wire_bytes()?.as_slice() != bytes {
            return Err(UniformAllocationCertificateError::MalformedWire);
        }
        Ok(certificate)
    }
}

/// Independently check one exact uniform-price optimization result.
pub fn verify_uniform_allocation(
    orders: &[Order],
    expected_k: usize,
    certificate: &UniformAllocationCertificate,
) -> Result<VerifiedUniformAllocation, UniformAllocationCertificateError> {
    validate_dimensions(orders.len(), expected_k)?;
    let expected_k = u32::try_from(expected_k)
        .map_err(|_| UniformAllocationCertificateError::DimensionOverflow)?;
    if certificate.k != expected_k {
        return Err(UniformAllocationCertificateError::WrongPriceLevelCount {
            expected: expected_k,
            found: certificate.k,
        });
    }
    if certificate.version != UNIFORM_ALLOCATION_CERTIFICATE_VERSION {
        return Err(UniformAllocationCertificateError::UnsupportedVersion {
            found: certificate.version,
        });
    }
    if certificate.fills.len() != orders.len() {
        return Err(UniformAllocationCertificateError::ShapeMismatch {
            orders: orders.len(),
            fills: certificate.fills.len(),
        });
    }
    let (expected_price, expected_volume) = independently_recompute_optimum(orders, expected_k)?;
    if certificate.clearing_price != expected_price {
        return Err(UniformAllocationCertificateError::WrongClearingPrice {
            expected: expected_price,
            found: certificate.clearing_price,
        });
    }
    if certificate.cleared_volume != expected_volume {
        return Err(UniformAllocationCertificateError::WrongClearedVolume {
            expected: expected_volume,
            found: certificate.cleared_volume,
        });
    }

    for (index, (order, fill)) in orders.iter().zip(&certificate.fills).enumerate() {
        if *fill > order.qty {
            return Err(UniformAllocationCertificateError::FillExceedsQuantity {
                index,
                quantity: order.qty,
                fill: *fill,
            });
        }
    }

    if expected_volume == 0 {
        if certificate.bid != RationWitness::default() {
            return Err(UniformAllocationCertificateError::CutoffMismatch { side: Side::Bid });
        }
        if certificate.ask != RationWitness::default() {
            return Err(UniformAllocationCertificateError::CutoffMismatch { side: Side::Ask });
        }
        for (index, fill) in certificate.fills.iter().copied().enumerate() {
            if fill != 0 {
                return Err(UniformAllocationCertificateError::InactiveFill { index });
            }
        }
    } else {
        verify_side(
            orders,
            &certificate.fills,
            Side::Bid,
            expected_price,
            expected_volume,
            certificate.bid,
        )?;
        verify_side(
            orders,
            &certificate.fills,
            Side::Ask,
            expected_price,
            expected_volume,
            certificate.ask,
        )?;
    }

    Ok(VerifiedUniformAllocation {
        k: expected_k,
        clearing_price: expected_price,
        cleared_volume: expected_volume,
        fills: certificate.fills.clone(),
    })
}

fn validate_dimensions(
    order_count: usize,
    k: usize,
) -> Result<(), UniformAllocationCertificateError> {
    if k == 0 {
        return Err(UniformAllocationCertificateError::InvalidPriceLevelCount);
    }
    if k > MAX_UNIFORM_PRICE_LEVELS {
        return Err(UniformAllocationCertificateError::TooManyPriceLevels {
            actual: k,
            maximum: MAX_UNIFORM_PRICE_LEVELS,
        });
    }
    if order_count > MAX_UNIFORM_ALLOCATION_ORDERS {
        return Err(UniformAllocationCertificateError::TooManyOrders {
            actual: order_count,
            maximum: MAX_UNIFORM_ALLOCATION_ORDERS,
        });
    }
    let terms = order_count
        .checked_mul(k)
        .ok_or(UniformAllocationCertificateError::DimensionOverflow)?;
    if terms > MAX_UNIFORM_VERIFY_TERMS {
        return Err(UniformAllocationCertificateError::VerificationWorkLimit {
            actual: terms,
            maximum: MAX_UNIFORM_VERIFY_TERMS,
        });
    }
    Ok(())
}

/// Deliberately uses the direct definition at every price, rather than the
/// finder's histogram/scan implementation.  This differential shape makes a
/// shared range-add or scan bug less likely to bless itself.
fn independently_recompute_optimum(
    orders: &[Order],
    k: u32,
) -> Result<(u32, u64), UniformAllocationCertificateError> {
    let mut best_price = 0u32;
    let mut best_volume = 0u64;
    for price in 0..k {
        let mut demand = 0u128;
        let mut supply = 0u128;
        for order in orders {
            match order.side {
                Side::Bid if order.limit >= price => demand += order.qty as u128,
                Side::Ask if order.limit <= price => supply += order.qty as u128,
                _ => {}
            }
        }
        let demand = u64::try_from(demand)
            .map_err(|_| UniformAllocationCertificateError::AggregateOverflow)?;
        let supply = u64::try_from(supply)
            .map_err(|_| UniformAllocationCertificateError::AggregateOverflow)?;
        let volume = demand.min(supply);
        if volume > best_volume {
            best_volume = volume;
            best_price = price;
        }
    }
    Ok((best_price, best_volume))
}

fn is_active(order: &Order, side: Side, price: u32) -> bool {
    order.side == side
        && match side {
            Side::Bid => order.limit >= price,
            Side::Ask => order.limit <= price,
        }
}

fn build_side_witness(
    orders: &[Order],
    fills: &[u64],
    side: Side,
    price: u32,
    target: u64,
) -> Result<RationWitness, UniformAllocationCertificateError> {
    let active_total_u128: u128 = orders
        .iter()
        .filter(|order| is_active(order, side, price))
        .map(|order| order.qty as u128)
        .sum();
    let active_total = u64::try_from(active_total_u128)
        .map_err(|_| UniformAllocationCertificateError::AggregateOverflow)?;
    if active_total <= target {
        return Ok(RationWitness {
            active_total,
            floor_sum: active_total,
            bonus_count: 0,
            cutoff: None,
        });
    }
    let mut floor_sum = 0u128;
    let mut bonuses: Vec<BonusCutoff> = Vec::new();
    for (index, (order, fill)) in orders.iter().zip(fills).enumerate() {
        if !is_active(order, side, price) {
            continue;
        }
        let numerator = (order.qty as u128) * (target as u128);
        let floor = (numerator / active_total_u128) as u64;
        let remainder = (numerator % active_total_u128) as u64;
        floor_sum += floor as u128;
        if *fill == floor.saturating_add(1) {
            bonuses.push(BonusCutoff {
                order_index: u32::try_from(index)
                    .map_err(|_| UniformAllocationCertificateError::DimensionOverflow)?,
                remainder,
            });
        }
    }
    let floor_sum = u64::try_from(floor_sum)
        .map_err(|_| UniformAllocationCertificateError::AggregateOverflow)?;
    let bonus_count = u32::try_from(bonuses.len())
        .map_err(|_| UniformAllocationCertificateError::DimensionOverflow)?;
    let cutoff = bonuses.into_iter().min_by(|left, right| {
        left.remainder
            .cmp(&right.remainder)
            .then_with(|| right.order_index.cmp(&left.order_index))
    });
    Ok(RationWitness {
        active_total,
        floor_sum,
        bonus_count,
        cutoff,
    })
}

fn verify_side(
    orders: &[Order],
    fills: &[u64],
    side: Side,
    price: u32,
    target: u64,
    witness: RationWitness,
) -> Result<(), UniformAllocationCertificateError> {
    let active_total_u128: u128 = orders
        .iter()
        .filter(|order| is_active(order, side, price))
        .map(|order| order.qty as u128)
        .sum();
    let active_total = u64::try_from(active_total_u128)
        .map_err(|_| UniformAllocationCertificateError::AggregateOverflow)?;
    if witness.active_total != active_total {
        return Err(UniformAllocationCertificateError::ActiveTotalMismatch {
            side,
            expected: active_total,
            found: witness.active_total,
        });
    }
    if active_total < target {
        return Err(UniformAllocationCertificateError::TargetExceedsActive {
            side,
            target,
            active: active_total,
        });
    }

    if active_total == target {
        if witness.floor_sum != active_total {
            return Err(UniformAllocationCertificateError::FloorSumMismatch {
                side,
                expected: active_total,
                found: witness.floor_sum,
            });
        }
        if witness.bonus_count != 0 {
            return Err(UniformAllocationCertificateError::BonusCountMismatch {
                side,
                expected: 0,
                found: witness.bonus_count,
            });
        }
        if witness.cutoff.is_some() {
            return Err(UniformAllocationCertificateError::CutoffMismatch { side });
        }
        let mut side_sum = 0u128;
        for (index, (order, fill)) in orders.iter().zip(fills).enumerate() {
            if order.side != side {
                continue;
            }
            let expected = if is_active(order, side, price) {
                order.qty
            } else {
                0
            };
            if *fill != expected {
                return Err(if expected == 0 {
                    UniformAllocationCertificateError::InactiveFill { index }
                } else {
                    UniformAllocationCertificateError::NonCanonicalFill {
                        index,
                        expected,
                        found: *fill,
                    }
                });
            }
            side_sum += *fill as u128;
        }
        let side_sum = u64::try_from(side_sum)
            .map_err(|_| UniformAllocationCertificateError::AggregateOverflow)?;
        if side_sum != target {
            return Err(UniformAllocationCertificateError::SideVolumeMismatch {
                side,
                expected: target,
                found: side_sum,
            });
        }
        return Ok(());
    }

    let mut floor_sum = 0u128;
    for order in orders {
        if is_active(order, side, price) {
            floor_sum += ((order.qty as u128) * (target as u128)) / active_total_u128;
        }
    }
    let floor_sum = u64::try_from(floor_sum)
        .map_err(|_| UniformAllocationCertificateError::AggregateOverflow)?;
    if witness.floor_sum != floor_sum {
        return Err(UniformAllocationCertificateError::FloorSumMismatch {
            side,
            expected: floor_sum,
            found: witness.floor_sum,
        });
    }
    let expected_bonus_count_u64 = target
        .checked_sub(floor_sum)
        .ok_or(UniformAllocationCertificateError::AggregateOverflow)?;
    let expected_bonus_count = u32::try_from(expected_bonus_count_u64)
        .map_err(|_| UniformAllocationCertificateError::DimensionOverflow)?;
    if witness.bonus_count != expected_bonus_count {
        return Err(UniformAllocationCertificateError::BonusCountMismatch {
            side,
            expected: expected_bonus_count,
            found: witness.bonus_count,
        });
    }

    let cutoff = match (expected_bonus_count, witness.cutoff) {
        (0, None) => None,
        (0, Some(_)) | (_, None) => {
            return Err(UniformAllocationCertificateError::CutoffMismatch { side });
        }
        (_, Some(cutoff)) => {
            let index = usize::try_from(cutoff.order_index)
                .map_err(|_| UniformAllocationCertificateError::DimensionOverflow)?;
            let Some(order) = orders.get(index) else {
                return Err(UniformAllocationCertificateError::CutoffMismatch { side });
            };
            if !is_active(order, side, price) {
                return Err(UniformAllocationCertificateError::CutoffMismatch { side });
            }
            let expected_remainder =
                (((order.qty as u128) * (target as u128)) % active_total_u128) as u64;
            if cutoff.remainder != expected_remainder {
                return Err(UniformAllocationCertificateError::CutoffMismatch { side });
            }
            Some(cutoff)
        }
    };

    let mut actual_bonus_count = 0u32;
    let mut side_sum = 0u128;
    for (index, (order, fill)) in orders.iter().zip(fills).enumerate() {
        if order.side != side {
            continue;
        }
        if !is_active(order, side, price) {
            if *fill != 0 {
                return Err(UniformAllocationCertificateError::InactiveFill { index });
            }
            continue;
        }
        let numerator = (order.qty as u128) * (target as u128);
        let floor = (numerator / active_total_u128) as u64;
        let remainder = (numerator % active_total_u128) as u64;
        let gets_bonus = cutoff.is_some_and(|cutoff| {
            remainder > cutoff.remainder
                || (remainder == cutoff.remainder && (index as u32) <= cutoff.order_index)
        });
        let expected = floor + u64::from(gets_bonus);
        if *fill != expected {
            return Err(UniformAllocationCertificateError::NonCanonicalFill {
                index,
                expected,
                found: *fill,
            });
        }
        actual_bonus_count += u32::from(gets_bonus);
        side_sum += *fill as u128;
    }
    if actual_bonus_count != expected_bonus_count {
        return Err(UniformAllocationCertificateError::BonusCountMismatch {
            side,
            expected: expected_bonus_count,
            found: actual_bonus_count,
        });
    }
    let side_sum = u64::try_from(side_sum)
        .map_err(|_| UniformAllocationCertificateError::AggregateOverflow)?;
    if side_sum != target {
        return Err(UniformAllocationCertificateError::SideVolumeMismatch {
            side,
            expected: target,
            found: side_sum,
        });
    }
    Ok(())
}

fn encode_side_witness(out: &mut Vec<u8>, witness: RationWitness) {
    out.extend_from_slice(&witness.active_total.to_be_bytes());
    out.extend_from_slice(&witness.floor_sum.to_be_bytes());
    out.extend_from_slice(&witness.bonus_count.to_be_bytes());
    match witness.cutoff {
        None => {
            out.push(0);
            out.extend_from_slice(&0u32.to_be_bytes());
            out.extend_from_slice(&0u64.to_be_bytes());
        }
        Some(cutoff) => {
            out.push(1);
            out.extend_from_slice(&cutoff.order_index.to_be_bytes());
            out.extend_from_slice(&cutoff.remainder.to_be_bytes());
        }
    }
}

fn decode_side_witness(
    cursor: &mut Cursor<'_>,
) -> Result<RationWitness, UniformAllocationCertificateError> {
    let active_total = u64::from_be_bytes(cursor.take::<8>()?);
    let floor_sum = u64::from_be_bytes(cursor.take::<8>()?);
    let bonus_count = u32::from_be_bytes(cursor.take::<4>()?);
    let tag = cursor.take::<1>()?[0];
    let order_index = u32::from_be_bytes(cursor.take::<4>()?);
    let remainder = u64::from_be_bytes(cursor.take::<8>()?);
    let cutoff = match tag {
        0 if order_index == 0 && remainder == 0 => None,
        1 => Some(BonusCutoff {
            order_index,
            remainder,
        }),
        _ => return Err(UniformAllocationCertificateError::MalformedWire),
    };
    Ok(RationWitness {
        active_total,
        floor_sum,
        bonus_count,
        cutoff,
    })
}

struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], UniformAllocationCertificateError> {
        let end = self
            .position
            .checked_add(N)
            .ok_or(UniformAllocationCertificateError::DimensionOverflow)?;
        let slice = self
            .bytes
            .get(self.position..end)
            .ok_or(UniformAllocationCertificateError::MalformedWire)?;
        self.position = end;
        slice
            .try_into()
            .map_err(|_| UniformAllocationCertificateError::MalformedWire)
    }

    fn is_finished(&self) -> bool {
        self.position == self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clearing::{allocate, clear};

    fn work_book() -> Vec<Order> {
        vec![
            Order::bid(6, 2),
            Order::bid(4, 1),
            Order::ask(3, 0),
            Order::ask(5, 1),
        ]
    }

    fn honest_certificate(orders: &[Order], k: usize) -> UniformAllocationCertificate {
        let clearing = clear(orders, k);
        let allocation = allocate(orders, &clearing);
        UniformAllocationCertificate::from_solver_output(orders, &clearing, &allocation).unwrap()
    }

    #[test]
    fn workbook_certificate_checks_and_roundtrips_canonically() {
        let orders = work_book();
        let cert = honest_certificate(&orders, 3);
        let verified = verify_uniform_allocation(&orders, 3, &cert).unwrap();
        assert_eq!(
            (verified.clearing_price(), verified.cleared_volume()),
            (1, 8)
        );
        assert_eq!(verified.fills(), [5, 3, 3, 5]);
        assert!(
            cert.bid.cutoff.is_some(),
            "the workbook must exercise the Some(cutoff) wire arm"
        );
        let bytes = cert.to_wire_bytes().unwrap();
        assert_eq!(
            bytes.len(),
            FIXED_WIRE_LEN + orders.len() * std::mem::size_of::<u64>(),
            "a Some(cutoff) side witness has the same fixed wire width as None"
        );
        let decoded = UniformAllocationCertificate::from_wire_bytes(&bytes).unwrap();
        assert_eq!(decoded, cert);
        assert_eq!(decoded.to_wire_bytes().unwrap(), bytes);
    }

    #[test]
    fn conservation_only_unit_move_is_refused() {
        let orders = work_book();
        let clearing = clear(&orders, 3);
        let mut allocation = allocate(&orders, &clearing);
        allocation.fills[0] += 1;
        allocation.fills[1] -= 1;
        assert!(allocation.validate(&orders, &clearing));
        let certificate =
            UniformAllocationCertificate::from_solver_output(&orders, &clearing, &allocation)
                .unwrap();
        assert!(matches!(
            verify_uniform_allocation(&orders, 3, &certificate),
            Err(UniformAllocationCertificateError::NonCanonicalFill { .. })
                | Err(UniformAllocationCertificateError::BonusCountMismatch { .. })
        ));
    }

    #[test]
    fn price_volume_fill_and_cutoff_substitutions_refuse() {
        let orders = work_book();
        let cert = honest_certificate(&orders, 3);

        let mut wrong_price = cert.clone();
        wrong_price.clearing_price = 2;
        assert!(matches!(
            verify_uniform_allocation(&orders, 3, &wrong_price),
            Err(UniformAllocationCertificateError::WrongClearingPrice { .. })
        ));

        let mut wrong_volume = cert.clone();
        wrong_volume.cleared_volume = 7;
        assert!(matches!(
            verify_uniform_allocation(&orders, 3, &wrong_volume),
            Err(UniformAllocationCertificateError::WrongClearedVolume { .. })
        ));

        let mut inactive_fill = cert.clone();
        inactive_fill.fills[1] = 0;
        inactive_fill.fills[0] = 8;
        assert!(matches!(
            verify_uniform_allocation(&orders, 3, &inactive_fill),
            Err(UniformAllocationCertificateError::FillExceedsQuantity { index: 0, .. })
        ));

        let mut wrong_cutoff = cert;
        let cutoff = wrong_cutoff.bid.cutoff.as_mut().unwrap();
        cutoff.remainder ^= 1;
        assert!(matches!(
            verify_uniform_allocation(&orders, 3, &wrong_cutoff),
            Err(UniformAllocationCertificateError::CutoffMismatch { .. })
        ));
    }

    #[test]
    fn certificate_cannot_select_a_different_price_grid() {
        let orders = work_book();
        let cert_for_two_levels = honest_certificate(&orders, 2);
        assert!(matches!(
            verify_uniform_allocation(&orders, 3, &cert_for_two_levels),
            Err(UniformAllocationCertificateError::WrongPriceLevelCount {
                expected: 3,
                found: 2,
            })
        ));
    }

    #[test]
    fn equal_remainders_use_original_index_as_exact_tie_break() {
        let orders = vec![
            Order::bid(1, 0),
            Order::bid(1, 0),
            Order::bid(1, 0),
            Order::ask(2, 0),
        ];
        let cert = honest_certificate(&orders, 1);
        assert_eq!(cert.fills, [1, 1, 0, 2]);
        verify_uniform_allocation(&orders, 1, &cert).unwrap();

        let mut later_wins = cert;
        later_wins.fills.swap(1, 2);
        assert!(matches!(
            verify_uniform_allocation(&orders, 1, &later_wins),
            Err(UniformAllocationCertificateError::NonCanonicalFill { .. })
        ));
    }

    #[test]
    fn no_clear_requires_zero_fills_and_zero_witnesses() {
        let orders = vec![Order::bid(9, 0), Order::ask(9, 2)];
        let cert = honest_certificate(&orders, 2);
        assert_eq!(cert.cleared_volume, 0);
        verify_uniform_allocation(&orders, 2, &cert).unwrap();

        let mut forged = cert;
        forged.fills[0] = 1;
        assert!(matches!(
            verify_uniform_allocation(&orders, 2, &forged),
            Err(UniformAllocationCertificateError::InactiveFill { index: 0 })
        ));
    }

    #[test]
    fn aggregate_overflow_refuses_instead_of_wrapping() {
        let orders = vec![
            Order::bid(u64::MAX, 0),
            Order::bid(1, 0),
            Order::ask(u64::MAX, 0),
            Order::ask(1, 0),
        ];
        let mut cert = UniformAllocationCertificate {
            version: UNIFORM_ALLOCATION_CERTIFICATE_VERSION,
            k: 1,
            clearing_price: 0,
            cleared_volume: u64::MAX,
            fills: vec![u64::MAX, 0, u64::MAX, 0],
            bid: RationWitness::default(),
            ask: RationWitness::default(),
        };
        assert_eq!(
            verify_uniform_allocation(&orders, 1, &cert),
            Err(UniformAllocationCertificateError::AggregateOverflow)
        );
        cert.cleared_volume = 0;
        assert_eq!(
            verify_uniform_allocation(&orders, 1, &cert),
            Err(UniformAllocationCertificateError::AggregateOverflow)
        );
    }

    #[test]
    fn every_wire_truncation_and_trailing_byte_refuses() {
        let orders = work_book();
        let cert = honest_certificate(&orders, 3);
        let bytes = cert.to_wire_bytes().unwrap();
        for end in 0..bytes.len() {
            assert!(UniformAllocationCertificate::from_wire_bytes(&bytes[..end]).is_err());
        }
        let mut trailing = bytes;
        trailing.push(0);
        assert_eq!(
            UniformAllocationCertificate::from_wire_bytes(&trailing),
            Err(UniformAllocationCertificateError::MalformedWire)
        );
    }

    #[test]
    fn exhaustive_small_books_differential_against_the_live_finder() {
        let atoms: Vec<Order> = [Side::Bid, Side::Ask]
            .into_iter()
            .flat_map(|side| {
                (0..=2).flat_map(move |qty| (0..=2).map(move |limit| Order { side, qty, limit }))
            })
            .collect();
        for k in 1..=3 {
            for a in &atoms {
                for b in &atoms {
                    for c in &atoms {
                        let orders = [*a, *b, *c];
                        let clearing = clear(&orders, k);
                        let allocation = allocate(&orders, &clearing);
                        let cert = UniformAllocationCertificate::from_solver_output(
                            &orders,
                            &clearing,
                            &allocation,
                        )
                        .unwrap();
                        let verified = verify_uniform_allocation(&orders, k, &cert).unwrap();
                        assert_eq!(verified.clearing_price() as usize, clearing.clearing_price);
                        assert_eq!(verified.cleared_volume(), clearing.cleared_volume);
                        assert_eq!(verified.fills(), allocation.fills);
                    }
                }
            }
        }
    }
}
