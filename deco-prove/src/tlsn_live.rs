//! **Layer 2, the REAL MPC-TLS realization — vendored TLSNotary, run live-local.**
//!
//! Where [`crate::tlsn_attest`] MODELS the shape a verified `tlsn` presentation takes and
//! exercises the DECO binding over an in-tree fixture, THIS module runs the genuine thing:
//! a real [`tlsn`] Prover + a real local Notary perform the **MPC-TLS 2PC** handshake
//! against a test HTTPS server, the Prover **selectively discloses** the Stripe payment
//! facts (hiding the `Authorization: Bearer` secret), the Notary signs a real
//! `Attestation`, the Prover builds a real `Presentation`, and `presentation.verify()`
//! yields a real `PresentationOutput`. The disclosed facts are extracted from the
//! **authenticated** transcript and fed to the origin-agnostic DECO layer unchanged
//! ([`crate::prover::StripePaymentFacts`] → [`dregg_bridge::DecoPaymentAttestation`] →
//! `bridge::stripe_deco` mint).
//!
//! This is gated behind the `tlsn-live` cargo feature (the heavy `mpz` 2PC + tokio +
//! rustls backend). The whole flow is self-contained: the test HTTPS server, the Notary,
//! and the Prover all run in-process over `tokio::io::duplex` channels — no external
//! notary binary, no network.
//!
//! ## What is REAL here vs the operational live-Stripe remainder
//!
//! - **REAL (this module + `tests/tlsn_live_roundtrip.rs`):** the vendored tlsn stack, the
//!   MPC-TLS 2PC session (the Notary co-derives session keys and sees no plaintext), the
//!   signed `Attestation`, selective disclosure, the `Presentation`, `presentation.verify()`,
//!   and the extracted facts driving a conserved DECO mint through the real bridge verifier.
//!   A tampered `Presentation` fails the real `verify()`.
//! - **Operational remainder (a deploy step, NOT built here):** pointing the Prover at the
//!   live `api.stripe.com` (a real Stripe TLS session with a real merchant key, and a
//!   deployed/pinned notary). The machinery below is exactly that path with the server
//!   swapped: the local test server presents the `tlsn-server-fixture` cert for
//!   `test-server.io`, so the server pin here is `test-server.io`; live-Stripe pins
//!   [`crate::tlsn_attest::STRIPE_SERVER_NAME`] (`api.stripe.com`).

#![cfg(feature = "tlsn-live")]

use std::future::IntoFuture;
use std::sync::Arc;

use anyhow::{Context, Result, anyhow};
use dregg_types::CellId;
use futures::io::{AsyncReadExt as _, AsyncWriteExt as _};
use http_body_util::{Empty, Full};
use hyper::body::Bytes;
use hyper::{Request, Response, StatusCode};
use hyper_util::rt::TokioIo;
use tokio_util::compat::{FuturesAsyncReadCompatExt, TokioAsyncReadCompatExt};

use tlsn::{
    Session,
    attestation::{
        Attestation, AttestationConfig, CryptoProvider,
        presentation::{Presentation, PresentationOutput},
        request::{Request as AttestationRequest, RequestConfig},
        signing::Secp256k1Signer,
    },
    config::{
        prove::ProveConfig, prover::ProverConfig, tls::TlsClientConfig,
        tls_commit::mpc::MpcTlsConfig, verifier::VerifierConfig,
    },
    connection::{CertBinding, ConnectionInfo, HandshakeData, ServerName, TranscriptLength},
    prover::ProverOutput,
    transcript::{ContentType, TranscriptCommitConfig},
    verifier::{ServerCertVerifier, VerifierCommitStart, VerifierOutput},
    webpki::{CertificateDer, RootCertStore},
};
use tlsn_formats::http::{DefaultHttpCommitter, HttpCommit, HttpTranscript};
use tlsn_server_fixture_certs::{CA_CERT_DER, SERVER_CERT_DER, SERVER_DOMAIN, SERVER_KEY_DER};

use crate::prover::StripePaymentFacts;

/// The `status` value a settled Stripe PaymentIntent discloses.
pub const STATUS_SUCCEEDED: &str = crate::tlsn_attest::STRIPE_STATUS_SUCCEEDED;

/// The metadata key carrying the dregg recipient cell (matches the modeled adapter /
/// HMAC webhook path).
pub const RECIPIENT_METADATA_KEY: &str = crate::tlsn_attest::RECIPIENT_METADATA_KEY;

/// The `Authorization` value the merchant sends — a secret that MUST be redacted (never
/// authenticated) in the presentation. An obvious placeholder so no real-key shape lands
/// in the tree; the redaction is identical regardless of the token's contents.
const MERCHANT_SECRET: &str = "Bearer MERCHANT-STRIPE-SECRET-KEY-PLACEHOLDER";

// MPC-TLS preprocessing bounds (mirror `crates/examples`): the amount of data the 2PC
// preprocesses. The Stripe request/response are far under these.
const MAX_SENT_DATA: usize = 1 << 12;
const MAX_RECV_DATA: usize = 1 << 14;

/// The settled Stripe payment the test server discloses.
#[derive(Clone, Debug)]
pub struct LivePayment {
    /// The payment-intent id (the consume-once replay nonce).
    pub payment_intent_id: String,
    /// Amount in cents.
    pub amount_cents: u64,
    /// ISO-4217 currency (lowercase).
    pub currency: String,
    /// The `status` value (`succeeded` for a settled payment).
    pub status: String,
    /// The dregg recipient cell (placed in `metadata.dregg_recipient` as 64-hex).
    pub recipient: CellId,
}

impl LivePayment {
    /// A settled `$25.00 usd` payment to `recipient`.
    pub fn settled(payment_intent_id: &str, amount_cents: u64, recipient: CellId) -> Self {
        LivePayment {
            payment_intent_id: payment_intent_id.to_string(),
            amount_cents,
            currency: "usd".to_string(),
            status: STATUS_SUCCEEDED.to_string(),
            recipient,
        }
    }

    /// The exact JSON body the test server returns — a Stripe PaymentIntent shape.
    fn response_json(&self) -> String {
        format!(
            "{{\"id\":\"{id}\",\"object\":\"payment_intent\",\"amount\":{amount},\
             \"amount_received\":{amount},\"currency\":\"{currency}\",\
             \"customer\":\"cus_hidden\",\"payment_method\":\"pm_hidden\",\
             \"status\":\"{status}\",\"metadata\":{{\"{rkey}\":\"{rhex}\"}}}}",
            id = self.payment_intent_id,
            amount = self.amount_cents,
            currency = self.currency,
            status = self.status,
            rkey = RECIPIENT_METADATA_KEY,
            rhex = hex64(&self.recipient),
        )
    }
}

/// The disclosed facts + the transcript views a verified presentation yields.
#[derive(Clone, Debug)]
pub struct VerifiedPayment {
    /// The extracted Stripe payment facts (origin-agnostic; feed straight to Layer 1).
    pub facts: StripePaymentFacts,
    /// The authenticated server identity (must be the pinned host).
    pub server_name: String,
    /// The session time (`connection_info.time`, unix seconds).
    pub connection_time: u64,
    /// The delivered *sent* (request) bytes, unauthenticated positions set to `X`.
    pub sent_redacted: Vec<u8>,
    /// The delivered *received* (response) bytes, unauthenticated positions set to `X`.
    pub recv_redacted: Vec<u8>,
}

impl VerifiedPayment {
    /// Whether the `Authorization` secret was hidden (selective disclosure worked): the
    /// secret token does not survive into the authenticated sent bytes.
    pub fn authorization_hidden(&self) -> bool {
        !contains_subslice(&self.sent_redacted, MERCHANT_SECRET.as_bytes())
            && !contains_subslice(&self.sent_redacted, b"MERCHANT-STRIPE-SECRET")
    }
}

/// A completed real roundtrip: the verified payment + the raw `Presentation` bytes (so a
/// caller can tamper them and confirm the real `verify()` refuses).
#[derive(Clone, Debug)]
pub struct LiveRoundtrip {
    /// The verified, extracted payment.
    pub verified: VerifiedPayment,
    /// The bincode-serialized real `tlsn` `Presentation`.
    pub presentation_bytes: Vec<u8>,
    /// The server host the presentation was verified against (the local cert domain).
    pub pinned_server: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// The test HTTPS server — a controllable server returning the Stripe-shaped JSON over
// TLS, presenting the tlsn-server-fixture cert (domain test-server.io). Reuses the exact
// futures-rustls path the fixture uses, so it is MPC-TLS-compatible.
// ─────────────────────────────────────────────────────────────────────────────

async fn serve_stripe_once<S>(server_socket: S, payment: LivePayment) -> Result<()>
where
    S: tokio::io::AsyncRead + tokio::io::AsyncWrite + Send + Unpin + 'static,
{
    use futures_rustls::TlsAcceptor;
    use futures_rustls::pki_types::{
        CertificateDer as RustlsCert, PrivateKeyDer as RustlsKey, PrivatePkcs8KeyDer,
    };
    use futures_rustls::rustls::{ServerConfig, crypto::ring, version::TLS12};

    let cert = RustlsCert::from(SERVER_CERT_DER);
    let key = RustlsKey::Pkcs8(PrivatePkcs8KeyDer::from(SERVER_KEY_DER));

    let config = ServerConfig::builder_with_provider(Arc::new(ring::default_provider()))
        .with_protocol_versions(&[&TLS12])
        .context("server: TLS1.2 provider")?
        .with_no_client_auth()
        .with_single_cert(vec![cert], key)
        .context("server: single cert")?;

    let acceptor = TlsAcceptor::from(Arc::new(config));
    // futures-rustls speaks the futures AsyncRead/Write traits; the tokio duplex end is
    // adapted via `.compat()`.
    let tls = acceptor.accept(server_socket.compat()).await?;
    let io = TokioIo::new(tls.compat());

    let body = payment.response_json();
    let service = hyper::service::service_fn(move |_req: Request<hyper::body::Incoming>| {
        let body = body.clone();
        async move {
            Ok::<_, std::convert::Infallible>(
                Response::builder()
                    .status(StatusCode::OK)
                    .header("content-type", "application/json")
                    .header("connection", "close")
                    .body(Full::new(Bytes::from(body)))
                    .unwrap(),
            )
        }
    });

    hyper::server::conn::http1::Builder::new()
        .keep_alive(false)
        .serve_connection(io, service)
        .await
        .map_err(|e| anyhow!("server: serve_connection: {e}"))?;
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// The Notary — a real local tlsn verifier that runs the MPC-TLS commitment protocol and
// signs an `Attestation` (secp256k1). Mirrors `crates/examples/attestation/prove.rs`.
// ─────────────────────────────────────────────────────────────────────────────

async fn notary<S>(socket: S) -> Result<()>
where
    S: tokio::io::AsyncRead + tokio::io::AsyncWrite + Send + Sync + Unpin + 'static,
{
    let session = Session::new(socket.compat());
    let (driver, mut handle) = session.split();
    let driver_task = tokio::spawn(driver);

    let verifier_config = VerifierConfig::builder()
        .root_store(RootCertStore {
            roots: vec![CertificateDer(CA_CERT_DER.to_vec())],
        })
        .build()?;

    let verifier = match handle.new_verifier(verifier_config)?.commit().await? {
        VerifierCommitStart::Mpc(verifier) => verifier.accept().await?.run().await?,
        VerifierCommitStart::Proxy(verifier) => {
            verifier.reject(Some("expecting MPC-TLS")).await?;
            return Err(anyhow!("notary rejected non-MPC configuration"));
        }
    };

    let (
        VerifierOutput {
            transcript_commitments,
            ..
        },
        verifier,
    ) = verifier.verify().await?.accept().await?;

    let tls_transcript = verifier.tls_transcript().clone();
    verifier.close().await?;

    let sent_len: usize = tls_transcript
        .sent()
        .iter()
        .filter_map(|r| match r.typ {
            ContentType::ApplicationData => Some(r.ciphertext.len()),
            _ => None,
        })
        .sum();
    let recv_len: usize = tls_transcript
        .recv()
        .iter()
        .filter_map(|r| match r.typ {
            ContentType::ApplicationData => Some(r.ciphertext.len()),
            _ => None,
        })
        .sum();

    handle.close();
    let mut socket = driver_task.await??;

    let mut request_bytes = Vec::new();
    socket.read_to_end(&mut request_bytes).await?;
    let request: AttestationRequest = bincode::deserialize(&request_bytes)?;

    // The notary's signing key (a fixed test key; a deployed notary manages its own).
    let signing_key = k256::ecdsa::SigningKey::from_bytes(&[1u8; 32].into())?;
    let signer = Box::new(Secp256k1Signer::new(&signing_key.to_bytes())?);
    let mut provider = CryptoProvider::default();
    provider.signer.set_signer(signer);

    let mut att_config_builder = AttestationConfig::builder();
    att_config_builder.supported_signature_algs(Vec::from_iter(provider.signer.supported_algs()));
    let att_config = att_config_builder.build()?;

    let CertBinding::V1_2(binding) = tls_transcript.certificate_binding() else {
        return Err(anyhow!("unsupported cert binding version"));
    };
    let mut builder = Attestation::builder(&att_config).accept_request(request)?;
    builder
        .connection_info(ConnectionInfo {
            time: tls_transcript.time(),
            version: tls_transcript.version(),
            transcript_length: TranscriptLength {
                sent: sent_len as u32,
                received: recv_len as u32,
            },
        })
        .server_ephemeral_key(binding.server_ephemeral_key.clone())
        .transcript_commitments(transcript_commitments);

    let attestation = builder.build(&provider)?;

    let attestation_bytes = bincode::serialize(&attestation)?;
    socket.write_all(&attestation_bytes).await?;
    socket.close().await?;
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// The Prover — connects to the notary + the server, runs MPC-TLS, GETs the PaymentIntent,
// selectively discloses (hiding Authorization), and builds a real `Presentation`.
// ─────────────────────────────────────────────────────────────────────────────

async fn prove_stripe_presentation(payment: &LivePayment) -> Result<Vec<u8>> {
    // Prover <-> Notary session channel, and Prover <-> Server TLS transport channel.
    let (notary_socket, prover_notary_socket) = tokio::io::duplex(1 << 23);
    let (server_socket, prover_server_socket) = tokio::io::duplex(1 << 16);

    let notary_task = tokio::spawn(notary(notary_socket));
    let server_task = tokio::spawn(serve_stripe_once(server_socket, payment.clone()));

    let session = Session::new(prover_notary_socket.compat());
    let (driver, mut handle) = session.split();
    let driver_task = tokio::spawn(driver);

    let prover = handle
        .new_prover(ProverConfig::builder().build()?)?
        .commit(
            MpcTlsConfig::builder()
                .max_sent_data(MAX_SENT_DATA)
                .max_recv_data(MAX_RECV_DATA)
                .build()?,
        )
        .await?;

    // Bind the prover to the (in-process) server connection over MPC-TLS.
    let (tls_connection, prover) = prover.connect(
        TlsClientConfig::builder()
            .server_name(ServerName::Dns(SERVER_DOMAIN.try_into()?))
            .root_store(RootCertStore {
                roots: vec![CertificateDer(CA_CERT_DER.to_vec())],
            })
            .build()?,
        prover_server_socket.compat(),
    )?;
    let tls_connection = TokioIo::new(tls_connection.compat());
    let prover_task = tokio::spawn(prover.into_future());

    let (mut request_sender, connection) =
        hyper::client::conn::http1::handshake(tls_connection).await?;
    tokio::spawn(connection);

    let uri = format!("/v1/payment_intents/{}", payment.payment_intent_id);
    let request = Request::builder()
        .uri(uri)
        .header("Host", SERVER_DOMAIN)
        .header("Accept", "*/*")
        .header("Accept-Encoding", "identity")
        .header("Connection", "close")
        .header("Authorization", MERCHANT_SECRET)
        .method("GET")
        .body(Empty::<Bytes>::new())?;
    let response = request_sender.send_request(request).await?;
    if response.status() != StatusCode::OK {
        return Err(anyhow!("server returned {}", response.status()));
    }

    let mut prover = prover_task.await??;

    // Commit to the transcript (per-field HTTP commitments).
    let transcript = HttpTranscript::parse(prover.transcript())?;
    let mut commit_builder = TranscriptCommitConfig::builder(prover.transcript());
    DefaultHttpCommitter::default().commit_transcript(&mut commit_builder, &transcript)?;
    let transcript_commit = commit_builder.build()?;

    let mut req_cfg_builder = RequestConfig::builder();
    req_cfg_builder.transcript_commit(transcript_commit);
    let request_config = req_cfg_builder.build()?;

    let mut prove_builder = ProveConfig::builder(prover.transcript());
    if let Some(config) = request_config.transcript_commit() {
        prove_builder.transcript_commit(config.clone());
    }
    let disclosure_config = prove_builder.build()?;

    let ProverOutput {
        transcript_commitments,
        transcript_secrets,
        ..
    } = prover.prove(&disclosure_config).await?;

    let prover_transcript = prover.transcript().clone();
    let tls_transcript = prover.tls_transcript().clone();
    prover.close().await?;

    // Build the attestation request (carries the server identity + handshake data).
    let mut att_req_builder = AttestationRequest::builder(&request_config);
    att_req_builder
        .server_name(ServerName::Dns(SERVER_DOMAIN.try_into()?))
        .handshake_data(HandshakeData {
            certs: tls_transcript
                .server_cert_chain()
                .context("server cert chain present")?
                .to_vec(),
            sig: tls_transcript
                .server_signature()
                .context("server signature present")?
                .clone(),
            binding: tls_transcript.certificate_binding().clone(),
        })
        .transcript(prover_transcript)
        .transcript_commitments(transcript_secrets, transcript_commitments);
    let (att_request, secrets) = att_req_builder.build(&CryptoProvider::default())?;

    // Hand the request to the notary and receive the signed attestation.
    handle.close();
    let mut socket = driver_task.await??;
    socket.write_all(&bincode::serialize(&att_request)?).await?;
    socket.close().await?;
    let mut attestation_bytes = Vec::new();
    socket.read_to_end(&mut attestation_bytes).await?;
    let attestation: Attestation = bincode::deserialize(&attestation_bytes)?;
    att_request.validate(&attestation, &CryptoProvider::default())?;

    // ── Build the PRESENTATION with selective disclosure.
    let http = HttpTranscript::parse(secrets.transcript())?;
    let mut builder = secrets.transcript_proof_builder();

    // Request: reveal structure + target + every header EXCEPT the Authorization VALUE
    // (the killer property — prove the payment without revealing the Stripe secret key).
    let req = &http.requests[0];
    builder.reveal_sent(req.without_data())?;
    builder.reveal_sent(&req.request.target)?;
    for header in &req.headers {
        if header
            .name
            .as_str()
            .eq_ignore_ascii_case(hyper::header::AUTHORIZATION.as_str())
        {
            builder.reveal_sent(header.without_value())?;
        } else {
            builder.reveal_sent(header)?;
        }
    }

    // Response: reveal it entirely — the payment facts are the disclosed public evidence.
    let resp = &http.responses[0];
    builder.reveal_recv(resp)?;
    let transcript_proof = builder.build()?;

    let provider = CryptoProvider::default();
    let mut pres_builder = attestation.presentation_builder(&provider);
    pres_builder
        .identity_proof(secrets.identity_proof())
        .transcript_proof(transcript_proof);
    let presentation: Presentation = pres_builder.build()?;

    let bytes = bincode::serialize(&presentation)?;

    // Reclaim the notary + server tasks (surface any error).
    notary_task.await??;
    server_task.await??;
    Ok(bytes)
}

/// **Verify a real `tlsn` presentation** (the verifier side) and extract the disclosed
/// Stripe facts from the AUTHENTICATED transcript.
///
/// Runs `presentation.verify()` (real crypto — a tampered presentation fails here), pins
/// the server host, gates `status == succeeded`, and reads the facts out of the
/// authenticated response body. A tampered/forged presentation is refused by the real
/// `verify()` before any fact is trusted.
pub fn verify_stripe_presentation(
    presentation_bytes: &[u8],
    expected_server: &str,
) -> Result<VerifiedPayment> {
    let presentation: Presentation =
        bincode::deserialize(presentation_bytes).context("presentation does not deserialize")?;

    let root_cert_store = RootCertStore {
        roots: vec![CertificateDer(CA_CERT_DER.to_vec())],
    };
    let crypto_provider = CryptoProvider {
        cert: ServerCertVerifier::new(&root_cert_store)?,
        ..Default::default()
    };

    // THE REAL VERIFY — a tampered presentation errors here.
    let PresentationOutput {
        server_name,
        connection_info,
        transcript,
        ..
    } = presentation
        .verify(&crypto_provider)
        .map_err(|e| anyhow!("presentation.verify() refused: {e}"))?;

    let server_name = server_name.context("presentation did not authenticate a server name")?;
    let ServerName::Dns(server_dns) = server_name;
    let server_name = server_dns.as_str().to_string();
    if server_name != expected_server {
        return Err(anyhow!(
            "server pin: got {server_name:?}, expected {expected_server:?}"
        ));
    }

    let mut partial = transcript.context("presentation revealed no transcript")?;
    partial.set_unauthed(b'X');
    let sent_redacted = partial.sent_unsafe().to_vec();
    let recv_redacted = partial.received_unsafe().to_vec();

    let facts = extract_facts_from_response(&recv_redacted)?;

    Ok(VerifiedPayment {
        facts,
        server_name,
        connection_time: connection_info.time,
        sent_redacted,
        recv_redacted,
    })
}

/// Parse the authenticated response body into [`StripePaymentFacts`], gating `succeeded`.
/// Any redacted (unauthenticated) fact leaves an `X` in the body and fails JSON parse or
/// the field read — fail-closed.
fn extract_facts_from_response(recv: &[u8]) -> Result<StripePaymentFacts> {
    let body_start =
        find_subslice(recv, b"\r\n\r\n").context("no header/body separator in response")? + 4;
    let body = &recv[body_start..];
    let value: serde_json::Value = serde_json::from_slice(body)
        .context("authenticated response body does not parse as JSON (a fact was redacted)")?;

    let status = value
        .get("status")
        .and_then(|v| v.as_str())
        .context("status not disclosed")?;
    if status != STATUS_SUCCEEDED {
        return Err(anyhow!(
            "payment status {status:?} is not {STATUS_SUCCEEDED:?}"
        ));
    }

    let payment_intent_id = value
        .get("id")
        .and_then(|v| v.as_str())
        .context("id not disclosed")?
        .to_string();
    let amount_cents = value
        .get("amount")
        .and_then(|v| v.as_u64())
        .context("amount not disclosed")?;
    let currency = value
        .get("currency")
        .and_then(|v| v.as_str())
        .context("currency not disclosed")?
        .to_string();
    let recipient_hex = value
        .get("metadata")
        .and_then(|m| m.get(RECIPIENT_METADATA_KEY))
        .and_then(|v| v.as_str())
        .context("recipient not disclosed")?;
    let recipient = parse_recipient_hex(recipient_hex)?;

    Ok(StripePaymentFacts {
        payment_intent_id,
        amount_cents,
        currency,
        recipient,
    })
}

/// **Run the full REAL local MPC-TLS roundtrip** (server + notary + prover in-process),
/// producing a signed presentation, then verify it and extract the payment. Blocking: it
/// stands up its own multi-thread tokio runtime, so callers (sync tests) need no runtime.
pub fn run_local_roundtrip_blocking(payment: &LivePayment) -> Result<LiveRoundtrip> {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    let presentation_bytes = rt.block_on(prove_stripe_presentation(payment))?;
    let verified = verify_stripe_presentation(&presentation_bytes, SERVER_DOMAIN)?;
    Ok(LiveRoundtrip {
        verified,
        presentation_bytes,
        pinned_server: SERVER_DOMAIN.to_string(),
    })
}

// ── small helpers ────────────────────────────────────────────────────────────

fn hex64(cell: &CellId) -> String {
    let mut s = String::with_capacity(64);
    for b in cell.0 {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn parse_recipient_hex(hex: &str) -> Result<CellId> {
    let hex = hex.trim();
    if hex.len() != 64 {
        return Err(anyhow!("recipient is not 64 hex chars"));
    }
    let mut out = [0u8; 32];
    for (i, chunk) in hex.as_bytes().chunks(2).enumerate() {
        let s = core::str::from_utf8(chunk)?;
        out[i] = u8::from_str_radix(s, 16)?;
    }
    Ok(CellId::from_bytes(out))
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

fn contains_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    find_subslice(haystack, needle).is_some()
}
