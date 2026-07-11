//! **The price oracle** — prove a public price quote trustlessly, behind a clean interface.
//!
//! `GET https://api.coinbase.com/v2/prices/{asset}/spot` returns a public spot quote
//! `{"data":{"amount":"…","base":"BTC","currency":"USD"}}`. The zkOracle attestation
//! certifies a genuine `api.coinbase.com` TLS session (authentic) whose body is well-formed
//! JSON (real CFG cert) bound to ONE response (the weld); the extracted fact is: `{asset}`
//! quoted at `{amount}` at `{time}`.
//!
//! `{time}` is the TLS session time (`connection_info.time`), which the notary signs — the
//! quote's timestamp is authenticated as the moment the session happened, not a body field
//! (Coinbase spot returns no timestamp in the body).
//!
//! ## The `PriceOracle` interface — the contract for the auditable-fund lane
//!
//! [`PriceOracle`] is the downstream contract: `price(asset) -> AttestedPrice { amount,
//! time, attestation }`. A consumer (the auditable-fund lane) depends on THIS trait, not on
//! the prover internals; it can re-verify the carried attestation with [`verify_coinbase_spot`]
//! to trust the amount trustlessly. [`CoinbaseSpotOracle`] is the real (fixture-backed)
//! implementation; a live implementation swaps the fixture for the [`crate::tlsn_live`]
//! roundtrip against `api.coinbase.com`, same interface.
//!
//! The injection-free leg is n/a (a read-only quote has no user-supplied field), exactly as
//! for the GitHub commit oracle — the empty field is vacuously injection-free.

use std::collections::HashMap;

use serde::Deserialize;

use crate::attestation::{ProveError, ZkOracleAttestation, prove_zkoracle, verify_zkoracle};
use crate::authentic::{EndpointConfig, EndpointPresentation, EndpointSpec, FixtureNotary};
use crate::endpoints::request_target;

/// The pinned Coinbase API host.
pub const COINBASE_SERVER_NAME: &str = "api.coinbase.com";

/// **The Coinbase spot-price endpoint spec** — pin `api.coinbase.com`, `GET`, no secret
/// header (public, read-only).
pub fn coinbase_spot_spec() -> EndpointSpec {
    EndpointSpec {
        id: "coinbase-spot".to_string(),
        server_name: COINBASE_SERVER_NAME.to_string(),
        method: "GET".to_string(),
        secret_header: None,
    }
}

/// The request path for a spot quote: `/v2/prices/{asset}/spot` (asset e.g. `BTC-USD`).
pub fn coinbase_spot_path(asset: &str) -> String {
    format!("/v2/prices/{asset}/spot")
}

/// A canned Coinbase spot response body (the disclosed evidence). The live body has this
/// same schema.
pub fn coinbase_spot_body(asset: &str, amount: &str) -> String {
    let (base, currency) = split_asset(asset).unwrap_or((asset.to_string(), String::new()));
    serde_json::json!({
        "data": { "amount": amount, "base": base, "currency": currency }
    })
    .to_string()
}

/// **An attested price** — the fact the downstream fund lane consumes, carrying the
/// attestation it can re-verify.
#[derive(Clone, Debug)]
pub struct AttestedPrice {
    /// The asset pair quoted (e.g. `BTC-USD`), from the authenticated request target.
    pub asset: String,
    /// The quoted amount, as the API returns it (a decimal string — no float rounding).
    pub amount: String,
    /// The quote time — the authenticated TLS session time (unix seconds).
    pub time: u64,
    /// The zkOracle attestation this price is extracted from (re-verifiable trustlessly).
    pub attestation: ZkOracleAttestation,
}

/// Why a price attestation is refused.
#[derive(Clone, Debug)]
pub enum PriceError {
    /// The underlying zkOracle attestation refused.
    NotVerified(crate::attestation::ZkOracleError),
    /// The prover could not produce an attestation (bad session / malformed body).
    NotProduced(ProveError),
    /// The authenticated request target is not a `/v2/prices/{asset}/spot` path.
    BadRequestTarget { got: String },
    /// The response body is not the expected spot-price schema.
    BadSchema { reason: String },
    /// The requested asset and the response's `base-currency` disagree.
    AssetMismatch { requested: String, got: String },
    /// The oracle has no quote for the requested asset.
    UnknownAsset { asset: String },
}

impl core::fmt::Display for PriceError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PriceError::NotVerified(e) => write!(f, "price attestation not verified: {e}"),
            PriceError::NotProduced(e) => write!(f, "price attestation not produced: {e}"),
            PriceError::BadRequestTarget { got } => {
                write!(
                    f,
                    "authenticated request target {got:?} is not a spot-price path"
                )
            }
            PriceError::BadSchema { reason } => write!(f, "spot-price schema: {reason}"),
            PriceError::AssetMismatch { requested, got } => {
                write!(
                    f,
                    "response asset {got:?} does not match requested {requested:?}"
                )
            }
            PriceError::UnknownAsset { asset } => write!(f, "no quote for asset {asset:?}"),
        }
    }
}

impl std::error::Error for PriceError {}

// The response schema.
#[derive(Deserialize)]
struct SpotData {
    amount: String,
    base: String,
    currency: String,
}
#[derive(Deserialize)]
struct SpotResponse {
    data: SpotData,
}

/// **The downstream contract** — a source of attested prices. The auditable-fund lane
/// depends on THIS, not on the prover internals: it receives an [`AttestedPrice`] whose
/// carried attestation it can re-verify with [`verify_coinbase_spot`].
pub trait PriceOracle {
    /// Quote `asset` (e.g. `BTC-USD`) → an attested price.
    fn price(&self, asset: &str) -> Result<AttestedPrice, PriceError>;
}

/// **PRODUCE a Coinbase spot attestation** from a presentation of the quote session. The
/// injection-free leg is n/a (empty field).
pub fn prove_coinbase_spot(
    presentation: EndpointPresentation,
    config: &EndpointConfig,
) -> Result<ZkOracleAttestation, ProveError> {
    prove_zkoracle(presentation, Vec::new(), config)
}

/// **VERIFY a Coinbase spot attestation** → the [`AttestedPrice`]. Runs the full
/// [`verify_zkoracle`], parses the asset from the authenticated request target and the
/// amount from the authenticated body, and cross-checks the response `base-currency` equals
/// the requested asset.
pub fn verify_coinbase_spot(
    att: &ZkOracleAttestation,
    config: &EndpointConfig,
) -> Result<AttestedPrice, PriceError> {
    let verified = verify_zkoracle(att, config).map_err(PriceError::NotVerified)?;

    let target = request_target(&att.presentation.sent)
        .ok_or_else(|| PriceError::BadRequestTarget { got: String::new() })?;
    let asset = parse_spot_target(&target).ok_or_else(|| PriceError::BadRequestTarget {
        got: target.clone(),
    })?;

    let parsed: SpotResponse =
        serde_json::from_slice(&verified.session.response_body).map_err(|e| {
            PriceError::BadSchema {
                reason: e.to_string(),
            }
        })?;

    // The response must be about the asset that was requested.
    let response_asset = format!("{}-{}", parsed.data.base, parsed.data.currency);
    if response_asset != asset {
        return Err(PriceError::AssetMismatch {
            requested: asset,
            got: response_asset,
        });
    }

    Ok(AttestedPrice {
        asset,
        amount: parsed.data.amount,
        time: verified.session.connection_time,
        attestation: att.clone(),
    })
}

/// **The real (fixture-backed) [`PriceOracle`] implementation.** Holds a notary + a quote
/// book; `price(asset)` produces a genuine attestation over the quote session and returns
/// the attested price. A live implementation swaps `build_endpoint_fixture` for the
/// `tlsn-live` roundtrip against `api.coinbase.com` — the same `PriceOracle` interface.
pub struct CoinbaseSpotOracle {
    notary: FixtureNotary,
    config: EndpointConfig,
    quotes: HashMap<String, String>,
    time: u64,
}

impl CoinbaseSpotOracle {
    /// A price oracle over a quote book (`asset -> amount`) at session time `time`.
    pub fn new(notary: FixtureNotary, quotes: HashMap<String, String>, time: u64) -> Self {
        let config = EndpointConfig::new(coinbase_spot_spec(), notary.verifying_key());
        CoinbaseSpotOracle {
            notary,
            config,
            quotes,
            time,
        }
    }

    /// The pinned config a consumer re-verifies against.
    pub fn config(&self) -> &EndpointConfig {
        &self.config
    }
}

impl PriceOracle for CoinbaseSpotOracle {
    fn price(&self, asset: &str) -> Result<AttestedPrice, PriceError> {
        let amount = self
            .quotes
            .get(asset)
            .ok_or_else(|| PriceError::UnknownAsset {
                asset: asset.to_string(),
            })?;
        let spec = coinbase_spot_spec();
        let body = coinbase_spot_body(asset, amount);
        let path = coinbase_spot_path(asset);
        let pres =
            crate::authentic::build_endpoint_fixture(&self.notary, &spec, &path, &body, self.time);
        let att = prove_coinbase_spot(pres, &self.config).map_err(PriceError::NotProduced)?;
        verify_coinbase_spot(&att, &self.config)
    }
}

/// Parse `/v2/prices/{asset}/spot` → `asset`.
fn parse_spot_target(target: &str) -> Option<String> {
    let segs: Vec<&str> = target.trim_start_matches('/').split('/').collect();
    // ["v2", "prices", asset, "spot"]
    if segs.len() == 4 && segs[0] == "v2" && segs[1] == "prices" && segs[3] == "spot" {
        Some(segs[2].to_string())
    } else {
        None
    }
}

/// Split `BASE-CURRENCY` (e.g. `BTC-USD`) → `(BASE, CURRENCY)`.
fn split_asset(asset: &str) -> Option<(String, String)> {
    let (base, currency) = asset.split_once('-')?;
    Some((base.to_string(), currency.to_string()))
}

/// **PRODUCE a Coinbase spot attestation from a LIVE MPC-TLS session** against the real
/// `api.coinbase.com` (feature `tlsn-live`).
///
/// Runs the genuine 2PC roundtrip ([`crate::tlsn_live::run_coinbase_roundtrip_blocking`]) — a
/// real TLS session with `api.coinbase.com`, its cert chain verified against the Mozilla roots
/// by a SEPARATE hosted notary — issuing `GET /v2/prices/{asset}/spot`, then binds the
/// authenticated body into a [`ZkOracleAttestation`] whose:
///
/// - **leg 1 (authentic)** is the REAL `tlsn` `Presentation` carried in
///   [`ZkOracleAttestation::tlsn_presentation`] — verified trustlessly by
///   [`verify_coinbase_live`] via the real `presentation.verify()`;
/// - **legs 2–4** (well-formed JSON CFG certificate, empty injection field, cross-leg content
///   commitment) are over that SAME authenticated body.
///
/// The modeled `presentation` carrier is an UNSIGNED envelope ([`EndpointPresentation`] with a
/// zero `notary_sig`): the live path never checks it (the real authentication is the `tlsn`
/// presentation), but it carries the authenticated request line so the asset is recoverable
/// from `presentation.sent`. A verifier MUST use [`verify_coinbase_live`], NOT the modeled
/// [`verify_coinbase_spot`], on a live attestation.
///
/// Returns the portable attestation + the notary's `tlsn` verifying key: because the ephemeral
/// notary mints a fresh key per run, that key is the out-of-band trust anchor the honest prover
/// PUBLISHES alongside the proof so a third party can pin it.
#[cfg(feature = "tlsn-live")]
pub fn prove_coinbase_live(
    asset: &str,
) -> Result<
    (
        ZkOracleAttestation,
        tlsn::attestation::signing::VerifyingKey,
    ),
    crate::attestation::ZkOracleError,
> {
    use crate::attestation::{FieldSpan, ZkOracleError, content_commitment};
    use crate::authentic::TlsnVerifyingKey;
    use crate::cfg::prove_cfg_compact;

    // The REAL MPC-TLS roundtrip: local separate notary + prover pointed at
    // api.coinbase.com:443, GET /v2/prices/{asset}/spot, selective disclosure, Presentation.
    let rt = crate::tlsn_live::run_coinbase_roundtrip_blocking(asset)
        .map_err(|e| ZkOracleError::NotAuthenticLive(e.to_string()))?;

    let body = rt.verified.response_body.clone();

    // Leg 2 — well-formed JSON CFG certificate over the AUTHENTICATED body.
    let cfg_cert = prove_cfg_compact(&body).map_err(ZkOracleError::NotWellFormed)?;

    // The cross-leg weld + the (vacuous) injection leg: a read-only quote has no user field.
    let content_commit = content_commitment(&body);
    let field_span = FieldSpan { offset: 0, len: 0 };

    // The unsigned modeled carrier — carries the authenticated request line (for asset
    // recovery) + a reconstructed response envelope; the REAL authentication is
    // `tlsn_presentation`.
    let recv = {
        let mut v = b"HTTP/1.1 200 OK\r\ncontent-type: application/json\r\n\r\n".to_vec();
        v.extend_from_slice(&body);
        v
    };
    let presentation = EndpointPresentation {
        verifying_key: TlsnVerifyingKey {
            alg: rt.notary_pin.verifying_key.alg.to_string(),
            data: rt.notary_pin.verifying_key.data.clone(),
        },
        server_name: rt.verified.server_name.clone(),
        connection_time: rt.verified.connection_time,
        sent: rt.verified.sent_redacted.clone(),
        recv,
        notary_sig: [0u8; 64],
    };

    let att = ZkOracleAttestation {
        presentation,
        cfg_cert,
        field_span,
        content_commit,
        zk_injection: None,
        tlsn_presentation: Some(rt.presentation_bytes),
    };
    Ok((att, rt.notary_pin.verifying_key))
}

/// **VERIFY a LIVE Coinbase spot attestation** (feature `tlsn-live`) → the [`AttestedPrice`].
///
/// Leg 1 is authenticated by the REAL `tlsn` `presentation.verify()` against the genuine
/// `api.coinbase.com` cert chain (Mozilla roots), pinning both the host
/// ([`COINBASE_SERVER_NAME`]) and `expected_notary_key` (the separate notary's published key);
/// legs 2–4 run over the SAME authenticated body. Parses the asset from the authenticated
/// request target and the amount from the authenticated body, cross-checking the response
/// `base-currency` equals the requested asset.
#[cfg(feature = "tlsn-live")]
pub fn verify_coinbase_live(
    att: &ZkOracleAttestation,
    expected_notary_key: &tlsn::attestation::signing::VerifyingKey,
) -> Result<AttestedPrice, PriceError> {
    let verified = crate::attestation::verify_zkoracle_live_host(
        att,
        COINBASE_SERVER_NAME,
        expected_notary_key,
    )
    .map_err(PriceError::NotVerified)?;

    let target = request_target(&att.presentation.sent)
        .ok_or_else(|| PriceError::BadRequestTarget { got: String::new() })?;
    let asset = parse_spot_target(&target).ok_or_else(|| PriceError::BadRequestTarget {
        got: target.clone(),
    })?;

    let parsed: SpotResponse =
        serde_json::from_slice(&verified.session.response_body).map_err(|e| {
            PriceError::BadSchema {
                reason: e.to_string(),
            }
        })?;

    let response_asset = format!("{}-{}", parsed.data.base, parsed.data.currency);
    if response_asset != asset {
        return Err(PriceError::AssetMismatch {
            requested: asset,
            got: response_asset,
        });
    }

    Ok(AttestedPrice {
        asset,
        amount: parsed.data.amount,
        time: verified.session.connection_time,
        attestation: att.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attestation::ZkOracleError;
    use crate::authentic::{AuthenticError, build_endpoint_fixture};

    fn book() -> HashMap<String, String> {
        HashMap::from([
            ("BTC-USD".to_string(), "64250.37".to_string()),
            ("ETH-USD".to_string(), "3410.11".to_string()),
        ])
    }

    /// THE DELIVERABLE — the `PriceOracle` interface yields an attested price the consumer
    /// re-verifies trustlessly.
    #[test]
    fn price_oracle_yields_a_reverifiable_attested_price() {
        let notary = FixtureNotary::from_seed(&[81u8; 32]);
        let oracle = CoinbaseSpotOracle::new(notary, book(), 1_700_000_200);

        let quote = oracle.price("BTC-USD").expect("a BTC-USD quote");
        assert_eq!(quote.asset, "BTC-USD");
        assert_eq!(quote.amount, "64250.37");
        assert_eq!(quote.time, 1_700_000_200);

        // The downstream consumer re-verifies the carried attestation itself.
        let reverified =
            verify_coinbase_spot(&quote.attestation, oracle.config()).expect("re-verifies");
        assert_eq!(reverified.amount, "64250.37");

        // An unknown asset is refused by the interface.
        assert!(matches!(
            oracle.price("DOGE-USD"),
            Err(PriceError::UnknownAsset { .. })
        ));
    }

    /// A FORGED/tampered session (a flipped authenticated amount digit) is refused — the
    /// notary signature breaks, so a wrong price cannot be attested.
    #[test]
    fn tampered_price_is_refused() {
        let notary = FixtureNotary::from_seed(&[82u8; 32]);
        let spec = coinbase_spot_spec();
        let config = EndpointConfig::new(spec.clone(), notary.verifying_key());
        let body = coinbase_spot_body("BTC-USD", "64250.37");
        let path = coinbase_spot_path("BTC-USD");
        let mut pres = build_endpoint_fixture(&notary, &spec, &path, &body, 1);
        // Flip a byte inside the authenticated amount.
        let amt_pos = pres
            .recv
            .windows(5)
            .position(|w| w == b"64250")
            .expect("amount present");
        pres.recv[amt_pos] ^= 0xFF;
        let att = ZkOracleAttestation {
            presentation: pres,
            cfg_cert: crate::cfg::prove_cfg_compact(body.as_bytes()).unwrap(),
            field_span: crate::attestation::FieldSpan { offset: 0, len: 0 },
            content_commit: crate::attestation::content_commitment(body.as_bytes()),
            zk_injection: None,
            tlsn_presentation: None,
        };
        assert!(matches!(
            verify_coinbase_spot(&att, &config),
            Err(PriceError::NotVerified(ZkOracleError::NotAuthentic(
                AuthenticError::BadNotarySignature
            )))
        ));
    }

    /// A response for a DIFFERENT asset than requested is refused by the asset cross-check.
    #[test]
    fn wrong_asset_is_refused() {
        let notary = FixtureNotary::from_seed(&[83u8; 32]);
        let spec = coinbase_spot_spec();
        let config = EndpointConfig::new(spec.clone(), notary.verifying_key());
        // Request BTC-USD, but the response authenticates an ETH-USD quote.
        let body = coinbase_spot_body("ETH-USD", "3410.11");
        let path = coinbase_spot_path("BTC-USD");
        let pres = build_endpoint_fixture(&notary, &spec, &path, &body, 1);
        let att = prove_coinbase_spot(pres, &config).expect("authentic session");
        assert!(matches!(
            verify_coinbase_spot(&att, &config),
            Err(PriceError::AssetMismatch { .. })
        ));
    }
}
