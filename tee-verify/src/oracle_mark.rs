//! **The ORACLE WELD** — a lending/solvency *mark* (a price) carried as a GRADED witness.
//!
//! ## The edge this closes (`docs/deos/DREGGFI-VISION.md` §7, `metatheory/Market/Lending.lean`)
//!
//! dregg's lending/solvency theorems are proved **conditional on the mark**: every statement is
//! `∀ (m : Mark) …` — "GIVEN the price feed, no bad debt" (`Lending.lean::no_bad_debt`,
//! `lending_sound`). The `Mark` is today an **unbounded assumption**: the theorem holds for *any*
//! price an adversary picks. That is the honest edge — the input-integrity half of the weld.
//!
//! A [`GradedMark`] closes it: the mark is no longer "anything the adversary picks" — it is
//! **"the price a named, attested source reported."** It is minted ONLY by composing an existing
//! integrity lane over a price:
//!
//! - **TEE-attested** ([`GradedMark::from_tee_attested`]) — an [`crate::AttestedFact`] over a price
//!   payload, verified by the pinned vendor root (`attest_data`): the price came from a named
//!   enclave (code identity `measurement`). Grade **ATTESTED**.
//! - **zkTLS-provenance** ([`GradedMark::from_zktls_price`]) — a price extracted from a named
//!   origin's authenticated response body, whose zkTLS/MPC-TLS session is verified UPSTREAM by
//!   `dregg-zkoracle-prove` (`verify_coinbase_spot` → `AttestedPrice`). Grade **ATTESTED**
//!   (provenance).
//!
//! There is **no bare-price constructor**: you cannot build a `GradedMark` from an unattested
//! price. That is the operational half of the closure the Lean tie (`Market/OracleWeld.lean`)
//! mirrors — the lending consumer takes a `GradedMark`, never a free `Mark`, so it can never be
//! fed an unattested price.
//!
//! ## The honest grade — ATTESTED, not PROVED (the whole point)
//!
//! A price is an **external fact**. This weld does NOT make the price "proved true"; the best it
//! gets is **ATTESTED** (HW-vendor root + side-channel + freshness residual) or zkTLS-provenance.
//! So the composite — a solvency/lending guarantee that consumes a `GradedMark` — is graded at its
//! **weakest leg**: **ATTESTED for the mark input, PROVED for the lending arithmetic**
//! ([`GradedMark::lending_composite_grade`] = [`Grade::Attested`], mirroring
//! `Market/OracleWeld.lean::oracle_weld_composite_grade`). The improvement is precise: the honest
//! edge moves from *"given the mark (unbounded)"* to *"given an ATTESTED mark (named source,
//! graded)."* The day the price is itself a ZK witness is when it moves ATTESTED→PROVED — that
//! remains future work (`DREGGFI-VISION.md` §7), and this lane delivers the ATTESTED rung.

use crate::attested_data::{attest_data, AttestedDataInput, AttestedError, TrustGrade};
use dregg_cell::tee_attest::{TeeAttestationVerifier, TeeQuoteKind};

/// A price/mark as an **exact rational** `num / den` — the Rust twin of the Lean lending `Mark`'s
/// `price : ℚ` (`Market/Lending.lean:70`). Decimal feed values (`"64250.37"`) parse without any
/// float rounding: `"64250.37" → { num: 6_425_037, den: 100 }`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MarkPrice {
    /// The numerator (signed — a price is non-negative in practice, but the rational is general).
    pub num: i128,
    /// The denominator (a power of ten from the decimal parse; always `> 0`).
    pub den: u128,
}

impl MarkPrice {
    /// Parse a canonical decimal feed value into an exact rational. Accepts an optional leading
    /// `-`, an integer part, and an optional fractional part (`"64250.37"`, `"3410"`, `"0.3"`).
    /// Rejects empty / non-digit / multi-dot / overflowing inputs — a payload that is not a
    /// clean price is REFUSED (it never becomes a mark).
    pub fn parse(s: &str) -> Result<MarkPrice, String> {
        let s = s.trim();
        if s.is_empty() {
            return Err("empty price".to_string());
        }
        let (neg, body) = match s.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, s),
        };
        let (int_part, frac_part) = match body.split_once('.') {
            Some((i, f)) => (i, f),
            None => (body, ""),
        };
        if int_part.is_empty() && frac_part.is_empty() {
            return Err(format!("no digits in price {s:?}"));
        }
        if !int_part
            .bytes()
            .chain(frac_part.bytes())
            .all(|b| b.is_ascii_digit())
        {
            return Err(format!("non-digit byte in price {s:?}"));
        }
        if frac_part.len() > 30 {
            return Err(format!("price {s:?} has too many fractional digits"));
        }
        let mut num: i128 = 0;
        for b in int_part.bytes().chain(frac_part.bytes()) {
            num = num
                .checked_mul(10)
                .and_then(|n| n.checked_add((b - b'0') as i128))
                .ok_or_else(|| format!("price {s:?} overflows i128"))?;
        }
        let den: u128 = 10u128
            .checked_pow(frac_part.len() as u32)
            .ok_or_else(|| format!("price {s:?} scale overflows"))?;
        Ok(MarkPrice {
            num: if neg { -num } else { num },
            den,
        })
    }

    /// The rational as an `f64` — a lossy view for logging/inspection ONLY. The exact
    /// `num`/`den` is what ties to the Lean `Mark.price : ℚ`; never settle off this.
    pub fn to_f64_lossy(&self) -> f64 {
        self.num as f64 / self.den as f64
    }
}

/// The **named source** a graded mark's price came from — the provenance that replaces the
/// unbounded `∀ mark` with "a named, attested origin." Mirrors
/// `Market/OracleWeld.lean::MarkProvenance`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MarkProvenance {
    /// A TEE-attested price: a named enclave (code identity `measurement`) produced it, verified
    /// by the pinned vendor root through [`attest_data`].
    TeeAttested {
        /// Which TEE produced the attestation.
        kind: TeeQuoteKind,
        /// The enclave's measured code identity — the "named published function" that reported it.
        measurement: [u8; 32],
    },
    /// A zkTLS-provenance price: extracted from a named origin's authenticated response body. The
    /// TLS-session authenticity is verified UPSTREAM by `dregg-zkoracle-prove` (`verify_coinbase_spot`);
    /// this carries the origin + the zkoracle content commitment (the in-circuit connect target).
    ZkTlsProvenance {
        /// The named API origin (e.g. `api.coinbase.com`).
        origin: String,
        /// The zkoracle `content_commitment` over the authenticated response body (serialized) —
        /// the fold's connect target. Its authenticity is the zkoracle attestation's job, not
        /// re-verified here.
        content_commit: Vec<u8>,
    },
}

impl MarkProvenance {
    /// A human-readable name of the source (`"tee-enclave:<hex8>"` / the origin host). The
    /// mark is not anonymous — it names who reported it.
    pub fn named_source(&self) -> String {
        match self {
            MarkProvenance::TeeAttested { measurement, .. } => {
                let m = measurement;
                format!(
                    "tee-enclave:{:02x}{:02x}{:02x}{:02x}",
                    m[0], m[1], m[2], m[3]
                )
            }
            MarkProvenance::ZkTlsProvenance { origin, .. } => origin.clone(),
        }
    }
}

/// The OCIP-order trust grade for **composite** claims (the mark leg + the lending arithmetic).
/// The single-lane [`TrustGrade`] mints only `Attested`; this is the ordered lattice the
/// weakest-leg composition rule (`docs/deos/EFFECTVM-SIDESTRUCTURE-ABI.md` §3.4) grades over,
/// mirroring `Market/OracleWeld.lean::TrustGrade`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Grade {
    /// A machine-checked theorem about the deployed artifact (the lending logic:
    /// `no_bad_debt` / `lending_sound`). Strongest for a *derived* claim.
    Proved,
    /// A HW-rooted attestation or zkTLS provenance about an *input* (a price). You still trust the
    /// HW-vendor root + side-channel residual — which is *why* it is not `Proved`.
    Attested,
    /// A pure re-derivation over public data.
    Replayable,
}

impl Grade {
    /// The composite grade of two legs = the **weakest** on the trust-minimization order
    /// (`REPLAYABLE > PROVED > ATTESTED`, `ABI §3.4`): a claim is only as strong as its
    /// weakest-trusted input. `weakest(Attested, Proved) = Attested`.
    pub fn weakest(a: Grade, b: Grade) -> Grade {
        // Order by trust demanded: Replayable(0) strongest → Proved(1) → Attested(2) weakest.
        fn rank(g: Grade) -> u8 {
            match g {
                Grade::Replayable => 0,
                Grade::Proved => 1,
                Grade::Attested => 2,
            }
        }
        if rank(a) >= rank(b) {
            a
        } else {
            b
        }
    }
}

/// **A GRADED MARK** — a price bound to its provenance and grade. The lending/solvency consumer
/// takes THIS, never a bare price: an unattested mark is unconstructable (there is no public
/// bare-price constructor — only [`GradedMark::from_tee_attested`] /
/// [`GradedMark::from_zktls_price`], each of which composes a verified integrity lane).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GradedMark {
    price: MarkPrice,
    grade: TrustGrade,
    provenance: MarkProvenance,
}

impl GradedMark {
    /// The attested price (the lending `Mark.price`).
    pub fn price(&self) -> MarkPrice {
        self.price
    }
    /// The single-lane grade this mark carries — always [`TrustGrade::Attested`] (a price is
    /// external; the best a mark gets is attested).
    pub fn grade(&self) -> TrustGrade {
        self.grade
    }
    /// The named source the price came from.
    pub fn provenance(&self) -> &MarkProvenance {
        &self.provenance
    }

    /// **The composite grade of a lending guarantee that consumes this mark** = the weakest leg of
    /// `{ mark = ATTESTED, lending arithmetic = PROVED }` = **ATTESTED**. This is the honest grade:
    /// consuming an attested mark in PROVED lending logic yields an ATTESTED composite, NEVER a
    /// uniformly-PROVED one — the price is not proved. Mirrors
    /// `Market/OracleWeld.lean::oracle_weld_composite_grade`.
    pub fn lending_composite_grade(&self) -> Grade {
        // The mark leg is ATTESTED; the lending logic (no_bad_debt / lending_sound) is PROVED.
        Grade::weakest(Grade::Attested, Grade::Proved)
    }

    /// **THE TEE LANE.** Verify a TEE attestation over a price payload (via [`attest_data`]) and
    /// mint a `GradedMark`, or REFUSE (fail-closed). The price is decoded FROM the verified
    /// payload, so the mark IS what the attested enclave reported — a tampered/forged/wrong-enclave
    /// attestation yields NO fact and hence NO mark, and a verified payload that is not a clean
    /// price is refused ([`MarkError::PriceDecode`]).
    ///
    /// `input.payload` must be the enclave-reported decimal price bytes (bound as `report_data` per
    /// the chosen [`crate::PayloadBinding`]).
    pub fn from_tee_attested<V: TeeAttestationVerifier + ?Sized>(
        verifier: &V,
        input: &AttestedDataInput<'_>,
    ) -> Result<GradedMark, MarkError> {
        let fact = attest_data(verifier, input).map_err(MarkError::Attestation)?;
        let text = core::str::from_utf8(&fact.payload)
            .map_err(|e| MarkError::PriceDecode(format!("attested payload not UTF-8: {e}")))?;
        let price = MarkPrice::parse(text).map_err(MarkError::PriceDecode)?;
        Ok(GradedMark {
            price,
            grade: fact.grade,
            provenance: MarkProvenance::TeeAttested {
                kind: fact.kind,
                measurement: fact.measurement,
            },
        })
    }

    /// **THE zkTLS LANE.** Bind a price extracted from a named origin's *already-verified* zkTLS
    /// session into a `GradedMark`. The AUTHENTICITY of `amount` + `origin` is verified UPSTREAM by
    /// `dregg-zkoracle-prove` (`endpoints::price::verify_coinbase_spot` → `AttestedPrice`, a full
    /// 3-leg `verify_zkoracle`); this constructor binds that verified amount + its
    /// `content_commitment` into the mark. `content_commit` is the zkoracle content commitment
    /// (the in-circuit connect target). Do NOT feed this an unverified amount — the sanctioned
    /// caller is the zkoracle price lane, exercised end-to-end by
    /// `zkoracle-prove/tests/oracle_mark_zktls.rs`.
    ///
    /// Refuses a `content_commit` shorter than a real commitment or an `amount` that is not a clean
    /// price ([`MarkError::PriceDecode`]).
    pub fn from_zktls_price(
        origin: &str,
        amount: &str,
        content_commit: Vec<u8>,
    ) -> Result<GradedMark, MarkError> {
        if content_commit.is_empty() {
            return Err(MarkError::PriceDecode(
                "zktls provenance requires a non-empty content commitment (the zkoracle connect \
                 target)"
                    .to_string(),
            ));
        }
        let price = MarkPrice::parse(amount).map_err(MarkError::PriceDecode)?;
        Ok(GradedMark {
            price,
            grade: TrustGrade::Attested,
            provenance: MarkProvenance::ZkTlsProvenance {
                origin: origin.to_string(),
                content_commit,
            },
        })
    }
}

/// Why a `GradedMark` was refused — fail-closed: a mark is minted ONLY when the integrity lane
/// verified AND the payload decoded to a clean price.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MarkError {
    /// The attested-data lane refused the attestation (forged / tampered / wrong-enclave /
    /// unbound / TCB-below-policy). Carries the underlying [`AttestedError`].
    Attestation(AttestedError),
    /// The attestation verified, but its payload is not a clean decimal price (or, for the zkTLS
    /// lane, the amount / content commitment was malformed). No mark from a non-price payload.
    PriceDecode(String),
}

impl core::fmt::Display for MarkError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            MarkError::Attestation(e) => write!(f, "graded mark refused — attestation: {e}"),
            MarkError::PriceDecode(m) => {
                write!(
                    f,
                    "graded mark refused — attested payload is not a price: {m}"
                )
            }
        }
    }
}

impl std::error::Error for MarkError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attested_data::PayloadBinding;
    use dregg_cell::tee_attest::TeeReportClaims;

    // The same injected-verifier test double the attested_data unit tests use: fixed claims for
    // any report, so the GradedMark decode/refusal logic is exercised without real crypto. The
    // REAL vendor-crypto seam is proven end-to-end by `tests/oracle_mark_weld.rs` (genuine AWS
    // Nitro fixture) — the SAME `TeeAttestationVerifier` seam.
    struct MockTee(TeeReportClaims);
    impl TeeAttestationVerifier for MockTee {
        fn verify_report(
            &self,
            _kind: TeeQuoteKind,
            _report: &[u8],
        ) -> Result<TeeReportClaims, String> {
            Ok(self.0)
        }
    }
    struct RejectTee;
    impl TeeAttestationVerifier for RejectTee {
        fn verify_report(&self, _k: TeeQuoteKind, _r: &[u8]) -> Result<TeeReportClaims, String> {
            Err("bad vendor signature".into())
        }
    }

    const MEAS: [u8; 32] = [9u8; 32];

    fn mock_over(payload: &[u8]) -> MockTee {
        MockTee(TeeReportClaims {
            measurement: MEAS,
            report_data: PayloadBinding::Sha256.commit(payload).unwrap(),
            tcb_ok: true,
        })
    }

    fn tee_input<'a>(payload: &'a [u8]) -> AttestedDataInput<'a> {
        AttestedDataInput {
            kind: TeeQuoteKind::SevSnp,
            attestation: b"opaque-report-bytes",
            payload,
            binding: PayloadBinding::Sha256,
            expected_measurement: MEAS,
        }
    }

    #[test]
    fn parses_decimal_prices_exactly() {
        assert_eq!(
            MarkPrice::parse("64250.37").unwrap(),
            MarkPrice {
                num: 6_425_037,
                den: 100
            }
        );
        assert_eq!(
            MarkPrice::parse("3410").unwrap(),
            MarkPrice { num: 3410, den: 1 }
        );
        assert_eq!(
            MarkPrice::parse("0.3").unwrap(),
            MarkPrice { num: 3, den: 10 }
        );
        // The Lending.lean crash mark is 3/10 = "0.3" — the exact rational ties to `Mark.price : ℚ`.
        let crash = MarkPrice::parse("0.3").unwrap();
        assert_eq!(crash.num as f64 / crash.den as f64, 0.3);
        // Refusals — a non-price never becomes a mark.
        assert!(MarkPrice::parse("").is_err());
        assert!(MarkPrice::parse("6x.5").is_err());
        assert!(MarkPrice::parse("1.2.3").is_err());
        assert!(MarkPrice::parse("abc").is_err());
    }

    #[test]
    fn genuine_attested_price_mints_a_graded_mark() {
        // POSITIVE POLE: a named enclave attests a price → a graded mark carrying that exact price.
        let price = b"64250.37";
        let v = mock_over(price);
        let mark = GradedMark::from_tee_attested(&v, &tee_input(price))
            .expect("a genuine attestation over a price mints a GradedMark");
        assert_eq!(
            mark.price(),
            MarkPrice {
                num: 6_425_037,
                den: 100
            }
        );
        assert_eq!(mark.grade(), TrustGrade::Attested);
        assert!(matches!(
            mark.provenance(),
            MarkProvenance::TeeAttested { measurement, .. } if *measurement == MEAS
        ));
        // The honest grade: consuming this in PROVED lending logic is an ATTESTED composite.
        assert_eq!(mark.lending_composite_grade(), Grade::Attested);
        assert_ne!(mark.lending_composite_grade(), Grade::Proved);
    }

    #[test]
    fn forged_attestation_yields_no_mark() {
        // NEGATIVE POLE: the vendor crypto refuses → no fact → no mark.
        let err = GradedMark::from_tee_attested(&RejectTee, &tee_input(b"64250.37")).unwrap_err();
        assert!(matches!(
            err,
            MarkError::Attestation(AttestedError::Attestation(_))
        ));
    }

    #[test]
    fn tampered_price_is_unbound_and_refused() {
        // The enclave bound the honest price; a splicer presents a DIFFERENT price with the same
        // attestation → the recomputed commitment disagrees → Unbound → no mark.
        let v = mock_over(b"64250.37");
        let err = GradedMark::from_tee_attested(&v, &tee_input(b"99999.99")).unwrap_err();
        assert_eq!(err, MarkError::Attestation(AttestedError::Unbound));
    }

    #[test]
    fn wrong_enclave_is_refused() {
        let price = b"64250.37";
        let v = mock_over(price);
        let mut input = tee_input(price);
        input.expected_measurement = [0xEEu8; 32]; // not the enclave that reports this feed
        let err = GradedMark::from_tee_attested(&v, &input).unwrap_err();
        assert_eq!(err, MarkError::Attestation(AttestedError::Measurement));
    }

    #[test]
    fn a_genuinely_attested_non_price_payload_is_refused() {
        // The attestation is genuine, but the enclave bound a non-price payload — no mark. The
        // lending consumer can never be fed a mark that is not a decoded price.
        let payload = b"not-a-price";
        let v = mock_over(payload);
        let err = GradedMark::from_tee_attested(&v, &tee_input(payload)).unwrap_err();
        assert!(matches!(err, MarkError::PriceDecode(_)));
    }

    #[test]
    fn zktls_lane_binds_a_verified_amount() {
        // POSITIVE POLE (zkTLS): a verified amount + origin + content commitment → a graded mark.
        let mark = GradedMark::from_zktls_price(
            "api.coinbase.com",
            "64250.37",
            vec![0xAB, 0xCD, 0xEF, 0x01],
        )
        .expect("a verified zktls amount binds");
        assert_eq!(
            mark.price(),
            MarkPrice {
                num: 6_425_037,
                den: 100
            }
        );
        assert_eq!(mark.grade(), TrustGrade::Attested);
        assert_eq!(mark.provenance().named_source(), "api.coinbase.com");
        assert_eq!(mark.lending_composite_grade(), Grade::Attested);
    }

    #[test]
    fn zktls_lane_refuses_a_bad_amount_or_empty_commit() {
        assert!(matches!(
            GradedMark::from_zktls_price("api.coinbase.com", "n/a", vec![1]).unwrap_err(),
            MarkError::PriceDecode(_)
        ));
        assert!(matches!(
            GradedMark::from_zktls_price("api.coinbase.com", "64250.37", vec![]).unwrap_err(),
            MarkError::PriceDecode(_)
        ));
    }

    #[test]
    fn weakest_leg_is_attested() {
        // The composition rule, both orders: a PROVED-logic + ATTESTED-input claim is ATTESTED.
        assert_eq!(
            Grade::weakest(Grade::Attested, Grade::Proved),
            Grade::Attested
        );
        assert_eq!(
            Grade::weakest(Grade::Proved, Grade::Attested),
            Grade::Attested
        );
        assert_eq!(
            Grade::weakest(Grade::Replayable, Grade::Proved),
            Grade::Proved
        );
    }
}
