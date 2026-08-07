//! Traits and markers distinguishing different rounds of a protocol.

/// Indicates that a type marks a particular round.
pub trait Round: sealed::Sealed {}

/// Marks the shares produced in round 1
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct R1;
/// Marks the aggregated shares from round 1
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct R1Aggregated;
/// Marks the shares produced in round 2
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct R2;

impl Round for R1 {}
impl Round for R1Aggregated {}
impl Round for R2 {}

/// DREGG ADDITIVE SEAM — a one-byte discriminant for a round marker.
///
/// A canonical share encoding must be able to REFUSE a round-1 share offered
/// where a round-2 share is expected: the two are the same shape (two poly
/// vectors) and differ only in the type parameter, so without a tag on the wire
/// a coordinator would aggregate a replayed round-1 share into the final key
/// and never notice. [`Round`] is sealed, so this trait can only ever have the
/// three impls below.
#[cfg(feature = "mbfv-share-codec")]
pub trait RoundTag: Round {
    /// The wire discriminant. Stable; changing one is a wire flag day.
    const TAG: u8;
}

#[cfg(feature = "mbfv-share-codec")]
impl RoundTag for R1 {
    const TAG: u8 = 1;
}
#[cfg(feature = "mbfv-share-codec")]
impl RoundTag for R1Aggregated {
    const TAG: u8 = 2;
}
#[cfg(feature = "mbfv-share-codec")]
impl RoundTag for R2 {
    const TAG: u8 = 3;
}

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::R1 {}
    impl Sealed for super::R1Aggregated {}
    impl Sealed for super::R2 {}
}
