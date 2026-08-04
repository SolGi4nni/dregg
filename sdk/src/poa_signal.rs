//! Path of Angels Signal claim transport.
//!
//! A public claim deliberately contains only a mission id and one bounded
//! Signal code.  Identity and state authority ride outside the event in the
//! signed/finalized turn; there is no slot here for a signer key, actor root,
//! Canon/config, or a replay counter.

use dregg_cell::{FieldElement, field_from_u64, field_to_u64};
use dregg_turn::action::{Event, symbol};

/// Exact reserved event topic for a version-1 Signal claim.
pub const SIGNAL_CLAIM_TOPIC_V1: &str = "pathofangels.network/signal-claim/v1";

/// Signal codes use three base-six bands.
pub const SIGNAL_BAND_MAX: u64 = 5;

/// The public mission-id wire is the same bounded id lane as the Lean judge.
pub const SIGNAL_MISSION_ID_MAX: u64 = u32::MAX as u64;

/// A bounded Signal Triangulation code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignalCode {
    low: u8,
    mid: u8,
    high: u8,
}

impl SignalCode {
    /// Construct a code, refusing rather than truncating any non-base-six band.
    pub fn new(low: u64, mid: u64, high: u64) -> Result<Self, SignalClaimError> {
        for (name, value) in [("low", low), ("mid", mid), ("high", high)] {
            if value > SIGNAL_BAND_MAX {
                return Err(SignalClaimError::BandOutOfRange { name, value });
            }
        }
        Ok(Self {
            low: low as u8,
            mid: mid as u8,
            high: high as u8,
        })
    }

    pub fn low(self) -> u8 {
        self.low
    }

    pub fn mid(self) -> u8 {
        self.mid
    }

    pub fn high(self) -> u8 {
        self.high
    }
}

/// The complete public Signal claim.  It intentionally has no authority fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignalClaimV1 {
    mission_id: u32,
    code: SignalCode,
}

impl SignalClaimV1 {
    /// Construct a claim without narrowing or wrapping its mission id.
    pub fn new(mission_id: u64, code: SignalCode) -> Result<Self, SignalClaimError> {
        if mission_id > SIGNAL_MISSION_ID_MAX {
            return Err(SignalClaimError::MissionIdOutOfRange(mission_id));
        }
        Ok(Self {
            mission_id: mission_id as u32,
            code,
        })
    }

    pub fn mission_id(self) -> u32 {
        self.mission_id
    }

    pub fn code(self) -> SignalCode {
        self.code
    }
}

/// Classification result for an event at the reserved ingress seam.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignalEventRoute {
    /// The event does not use the reserved Signal topic.
    Ordinary,
    /// An exact version-1 Signal claim.
    Signal(SignalClaimV1),
}

/// Construction/classification refusal.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SignalClaimError {
    #[error("Signal band {name}={value} exceeds the base-six bound")]
    BandOutOfRange { name: &'static str, value: u64 },
    #[error("Signal mission id {0} exceeds the 32-bit wire bound")]
    MissionIdOutOfRange(u64),
    #[error("reserved Signal claim marker is malformed: {0}")]
    MalformedReserved(&'static str),
}

/// Construct the exact reserved event.
///
/// The four canonical field lanes are `(mission_id, low, mid, high)`.  The
/// emitting cell and the outer turn signature identify the actor; duplicating
/// either here would turn authority into caller-authored payload.
pub fn signal_claim_event(claim: SignalClaimV1) -> Event {
    Event::new(
        symbol(SIGNAL_CLAIM_TOPIC_V1),
        vec![
            field_from_u64(u64::from(claim.mission_id)),
            field_from_u64(u64::from(claim.code.low)),
            field_from_u64(u64::from(claim.code.mid)),
            field_from_u64(u64::from(claim.code.high)),
        ],
    )
}

/// Classify an event without permitting malformed reserved events to fall
/// through to an ordinary-event consumer.
pub fn classify_signal_event(event: &Event) -> Result<SignalEventRoute, SignalClaimError> {
    if event.topic != symbol(SIGNAL_CLAIM_TOPIC_V1) {
        return Ok(SignalEventRoute::Ordinary);
    }
    if event.data.len() != 4 {
        return Err(SignalClaimError::MalformedReserved(
            "expected exactly four data fields",
        ));
    }

    let mission_id = exact_u64_lane(&event.data[0])?;
    let low = exact_u64_lane(&event.data[1])?;
    let mid = exact_u64_lane(&event.data[2])?;
    let high = exact_u64_lane(&event.data[3])?;
    let code = SignalCode::new(low, mid, high)?;
    let claim = SignalClaimV1::new(mission_id, code)?;
    Ok(SignalEventRoute::Signal(claim))
}

fn exact_u64_lane(field: &FieldElement) -> Result<u64, SignalClaimError> {
    let value = field_to_u64(field);
    if *field != field_from_u64(value) {
        return Err(SignalClaimError::MalformedReserved(
            "data field is not a canonical unsigned-64 lane",
        ));
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn claim() -> SignalClaimV1 {
        SignalClaimV1::new(7, SignalCode::new(2, 4, 1).unwrap()).unwrap()
    }

    #[test]
    fn constructor_and_classifier_are_exact_inverses() {
        let expected = claim();
        let event = signal_claim_event(expected);
        assert_eq!(event.topic, symbol(SIGNAL_CLAIM_TOPIC_V1));
        assert_eq!(event.data.len(), 4, "no authority field fits in the claim");
        assert_eq!(
            classify_signal_event(&event),
            Ok(SignalEventRoute::Signal(expected))
        );
    }

    #[test]
    fn ordinary_event_is_not_captured() {
        let event = Event::new(symbol("ordinary"), vec![field_from_u64(7)]);
        assert_eq!(
            classify_signal_event(&event),
            Ok(SignalEventRoute::Ordinary)
        );
    }

    #[test]
    fn malformed_reserved_marker_never_falls_through() {
        let reserved = symbol(SIGNAL_CLAIM_TOPIC_V1);
        for data in [vec![], vec![field_from_u64(1)], vec![field_from_u64(1); 5]] {
            assert!(matches!(
                classify_signal_event(&Event::new(reserved, data)),
                Err(SignalClaimError::MalformedReserved(_))
            ));
        }
    }

    #[test]
    fn noncanonical_and_out_of_range_reserved_fields_refuse() {
        let mut noncanonical = signal_claim_event(claim());
        noncanonical.data[0][0] = 1;
        assert!(matches!(
            classify_signal_event(&noncanonical),
            Err(SignalClaimError::MalformedReserved(_))
        ));

        let mut bad_band = signal_claim_event(claim());
        bad_band.data[3] = field_from_u64(6);
        assert!(matches!(
            classify_signal_event(&bad_band),
            Err(SignalClaimError::BandOutOfRange { .. })
        ));

        let mut bad_mission = signal_claim_event(claim());
        bad_mission.data[0] = field_from_u64(SIGNAL_MISSION_ID_MAX + 1);
        assert!(matches!(
            classify_signal_event(&bad_mission),
            Err(SignalClaimError::MissionIdOutOfRange(_))
        ));
    }
}
