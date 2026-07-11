//! **Phase-E: a REAL MPC-TLS 2PC session against LIVE AWS Bedrock — the model-provenance leg.**
//!
//! Where [`crate::tlsn_live`] runs the genuine tlsn stack against a LOCAL test server returning a
//! SCRIPTED body (the narration passed in as `reply`), THIS module points the SAME real prover +
//! notary at **`bedrock-runtime.<region>.amazonaws.com:443`** over a real TCP socket and
//! discloses the body **Bedrock genuinely returned in-session** — closing the exact hole the
//! plan (Phase E) names: the attested body is Claude's real output, not a passed-in string.
//!
//! Only FOUR things change from the proven [`crate::tlsn_live`] path; everything else (the 2PC,
//! the notary, `presentation.verify()`, selective disclosure) is identical:
//!   1. the prover connects to a real `TcpStream`, not `tokio::io::duplex` to a local server;
//!   2. the root store is the Mozilla/webpki set (`RootCertStore::mozilla`), so Amazon's real
//!      cert chain verifies and the server name pins `bedrock-runtime.<region>.amazonaws.com`;
//!   3. the request is **SigV4-signed** ([`crate::sigv4`]) — the `Authorization` header is the
//!      secret, replacing `x-api-key`;
//!   4. selective disclosure hides the `Authorization` VALUE (the credential) while revealing the
//!      response body — Claude's genuine completion.
//!
//! Bedrock negotiates **TLS 1.2 / ECDHE-RSA-AES128-GCM-SHA256** (probed live), which is exactly
//! the suite the vendored TLS1.2-only tlsn MPC-TLS backend implements — so the make-or-break TLS
//! wall is NOT present. The non-streaming `converse` endpoint returns a single JSON body (not
//! SSE), so disclosure reads it exactly as the local path does.
//!
//! **Separate hosted notary (Phase-E gap closed).** The notary is now a SEPARATE party
//! ([`crate::notary_server`]): it runs as a distinct tokio task on a real TCP socket, owns a
//! signing key the prover never sees, and the prover reaches it only by address. A verifier
//! trusts an attestation iff its embedded verifying key equals the notary's **pinned** public
//! key ([`verify_bedrock_presentation`] enforces this — a wrong/unpinned notary is rejected),
//! so a dishonest prover can no longer sign its own attestation. The residual is pure infra:
//! hosting that notary at a real internet address and distributing its key out-of-band.

#![cfg(feature = "tlsn-live")]

use std::future::IntoFuture;
use std::net::SocketAddr;

use anyhow::{Context, Result, anyhow};
use futures::io::{AsyncReadExt as _, AsyncWriteExt as _};
use http_body_util::{BodyExt, Full};
use hyper::body::Bytes;
use hyper::{Request, StatusCode};
use hyper_util::rt::TokioIo;
use tokio_util::compat::{FuturesAsyncReadCompatExt, TokioAsyncReadCompatExt};

use tlsn::{
    Session,
    attestation::{
        Attestation, CryptoProvider,
        presentation::{Presentation, PresentationOutput},
        request::{Request as AttestationRequest, RequestConfig},
        signing::VerifyingKey,
    },
    config::{
        prove::ProveConfig, prover::ProverConfig, tls::TlsClientConfig,
        tls_commit::mpc::MpcTlsConfig,
    },
    connection::{HandshakeData, ServerName},
    prover::ProverOutput,
    transcript::TranscriptCommitConfig,
    verifier::ServerCertVerifier,
    webpki::RootCertStore,
};
use tlsn_formats::http::{DefaultHttpCommitter, HttpCommit, HttpTranscript};

use crate::notary_server::{HostedNotary, NotaryPin, generate_notary_key, spawn_hosted_notary};
use crate::sigv4::{AwsCredentials, SignRequest, sign};
use crate::tlsn_live::VerifiedResponse;

// The 2PC preprocesses these bounds; cost (OT/garbling volume, memory, wall-clock) scales
// ~linearly with them. The request is a small signed POST, so `MAX_SENT_DATA` stays at 4 KiB.
// `MAX_RECV_DATA` is raised to 64 KiB (from the earlier 32 KiB) so a FULL-LENGTH narration
// (512–1024 output tokens ≈ a few KiB of body + Amazon's response headers) fits with generous
// headroom — the tradeoff is ~2× the preprocessing of the old bound, still tractable for the
// ignored live test.
const MAX_SENT_DATA: usize = 1 << 12;
const MAX_RECV_DATA: usize = 1 << 16;

/// A live Bedrock `converse` exchange to attest. The model id, region, and prompt are the app's;
/// the credential is the secret hidden by selective disclosure.
#[derive(Clone, Debug)]
pub struct BedrockExchange {
    /// The region host, e.g. `bedrock-runtime.us-east-1.amazonaws.com`.
    pub host: String,
    /// The AWS region, e.g. `us-east-1`.
    pub region: String,
    /// The RAW model id (wire path uses the raw `:`; the signer canonicalizes to `%3A`), e.g.
    /// `us.anthropic.claude-haiku-4-5-20251001-v1:0`.
    pub model_id: String,
    /// The Converse request body (JSON: messages/system/inferenceConfig).
    pub request_body: String,
    /// Static AWS credentials (no session token — the `commonquant-ember` profile is static).
    pub creds: AwsCredentials,
    /// The `X-Amz-Date` value (`YYYYMMDDTHHMMSSZ`, UTC, within AWS's 5-minute skew of now).
    pub amz_date: String,
}

impl BedrockExchange {
    /// The wire request target (raw `:` in the model id — AWS re-encodes it to `%3A` when
    /// canonicalizing the received path).
    fn wire_uri(&self) -> String {
        format!("/model/{}/converse", self.model_id)
    }
    /// The signed canonical URI (`:` → `%3A`).
    fn signed_uri(&self) -> String {
        format!("/model/{}/converse", self.model_id.replace(':', "%3A"))
    }
}

/// A completed real roundtrip against live Bedrock: the verified response + the raw
/// presentation + the SEPARATE notary's pin (address + pinned verifying key) it was attested
/// under.
#[derive(Clone, Debug)]
pub struct BedrockRoundtrip {
    pub verified: VerifiedResponse,
    pub presentation_bytes: Vec<u8>,
    pub pinned_server: String,
    /// The separate hosted notary's pin (socket + pinned public key) this attestation binds to.
    pub notary_pin: NotaryPin,
    /// Architectural marker: the notary ran as a SEPARATE party over a socket (never in-process).
    pub separate_notary: bool,
}

/// **Run the REAL MPC-TLS 2PC prover against live Bedrock**, connecting to a SEPARATE hosted
/// notary at `notary_addr` (over a real TCP socket — the prover never holds the notary's key),
/// and produce a signed presentation.
async fn prove_bedrock_presentation(
    ex: &BedrockExchange,
    notary_addr: SocketAddr,
) -> Result<Vec<u8>> {
    // Connect to the SEPARATE notary party over a real socket (not an in-process duplex).
    let prover_notary_socket = tokio::net::TcpStream::connect(notary_addr)
        .await
        .with_context(|| format!("connect to separate notary at {notary_addr}"))?;

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

    // The ONLY networking change vs tlsn_live: a REAL TCP socket to Bedrock.
    let server_socket = tokio::net::TcpStream::connect((ex.host.as_str(), 443u16))
        .await
        .with_context(|| format!("TCP connect to {}:443", ex.host))?;

    let (tls_connection, prover) = prover.connect(
        TlsClientConfig::builder()
            .server_name(ServerName::Dns(ex.host.as_str().try_into()?))
            .root_store(RootCertStore::mozilla())
            .build()?,
        server_socket.compat(),
    )?;
    let tls_connection = TokioIo::new(tls_connection.compat());
    let prover_task = tokio::spawn(prover.into_future());

    let (mut request_sender, connection) =
        hyper::client::conn::http1::handshake(tls_connection).await?;
    tokio::spawn(connection);

    // SigV4-sign the request (Authorization = the secret to hide).
    let signed = sign(
        &SignRequest {
            method: "POST",
            host: &ex.host,
            canonical_uri: &ex.signed_uri(),
            content_type: "application/json",
            body: ex.request_body.as_bytes(),
            region: &ex.region,
            service: "bedrock",
            amz_date: &ex.amz_date,
        },
        &ex.creds,
    );

    let request = Request::builder()
        .uri(ex.wire_uri())
        .method("POST")
        .header("Host", &ex.host)
        .header("Accept", "*/*")
        .header("Accept-Encoding", "identity")
        .header("Connection", "close")
        .header("content-type", "application/json")
        .header("x-amz-date", &signed.amz_date)
        .header("authorization", &signed.authorization)
        .body(Full::<Bytes>::new(Bytes::from(ex.request_body.clone())))?;

    let response = request_sender.send_request(request).await?;
    let status = response.status();
    let _ = response.into_body().collect().await?;
    if status != StatusCode::OK {
        return Err(anyhow!(
            "Bedrock returned {status} (see disclosed body for detail)"
        ));
    }

    let mut prover = prover_task.await??;

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

    let mut att_req_builder = AttestationRequest::builder(&request_config);
    att_req_builder
        .server_name(ServerName::Dns(ex.host.as_str().try_into()?))
        .handshake_data(HandshakeData {
            certs: tls_transcript
                .server_cert_chain()
                .context("server cert chain")?
                .to_vec(),
            sig: tls_transcript
                .server_signature()
                .context("server signature")?
                .clone(),
            binding: tls_transcript.certificate_binding().clone(),
        })
        .transcript(prover_transcript)
        .transcript_commitments(transcript_secrets, transcript_commitments);
    let (att_request, secrets) = att_req_builder.build(&CryptoProvider::default())?;

    handle.close();
    let mut socket = driver_task.await??;
    socket.write_all(&bincode::serialize(&att_request)?).await?;
    socket.close().await?;
    let mut attestation_bytes = Vec::new();
    socket.read_to_end(&mut attestation_bytes).await?;
    let attestation: Attestation = bincode::deserialize(&attestation_bytes)?;
    att_request.validate(&attestation, &CryptoProvider::default())?;

    // Selective disclosure: reveal the request structure + every header EXCEPT the
    // `authorization` VALUE (the SigV4 credential), and reveal the whole response body.
    let http = HttpTranscript::parse(secrets.transcript())?;
    let mut builder = secrets.transcript_proof_builder();
    let req = &http.requests[0];
    builder.reveal_sent(req.without_data())?;
    builder.reveal_sent(&req.request.target)?;
    for header in &req.headers {
        if header.name.as_str().eq_ignore_ascii_case("authorization") {
            builder.reveal_sent(header.without_value())?; // name only — SIGNATURE HIDDEN
        } else {
            builder.reveal_sent(header)?;
        }
    }
    let resp = &http.responses[0];
    builder.reveal_recv(resp)?; // the genuine Claude completion is the disclosed evidence
    let transcript_proof = builder.build()?;

    let provider = CryptoProvider::default();
    let mut pres_builder = attestation.presentation_builder(&provider);
    pres_builder
        .identity_proof(secrets.identity_proof())
        .transcript_proof(transcript_proof);
    let presentation: Presentation = pres_builder.build()?;
    let bytes = bincode::serialize(&presentation)?;

    Ok(bytes)
}

/// Verify a real Bedrock presentation against the Mozilla roots, **pin the SEPARATE notary's
/// verifying key** (reject any attestation not signed by the trusted notary), pin the Bedrock
/// host, and extract the authenticated response body (Claude's genuine completion) with the
/// SigV4 `authorization` value redacted to `X`.
///
/// `expected_notary_key` is the out-of-band trust anchor: `presentation.verify()` only checks
/// the attestation's signature is self-consistent with its *embedded* key, so THIS function is
/// where the notary is actually trusted — a wrong/unpinned notary key is refused before the
/// body is believed.
pub fn verify_bedrock_presentation(
    presentation_bytes: &[u8],
    expected_host: &str,
    expected_notary_key: &VerifyingKey,
) -> Result<VerifiedResponse> {
    let presentation: Presentation =
        bincode::deserialize(presentation_bytes).context("presentation does not deserialize")?;

    // PIN THE NOTARY: the embedded verifying key must be exactly the notary we trust.
    let presented_key = presentation.verifying_key().clone();
    if &presented_key != expected_notary_key {
        return Err(anyhow!(
            "notary pin: presentation signed by an untrusted notary key (got alg={} len={}, expected alg={} len={})",
            presented_key.alg,
            presented_key.data.len(),
            expected_notary_key.alg,
            expected_notary_key.data.len(),
        ));
    }

    let crypto_provider = CryptoProvider {
        cert: ServerCertVerifier::mozilla(),
        ..Default::default()
    };

    let PresentationOutput {
        server_name,
        connection_info,
        transcript,
        attestation,
        ..
    } = presentation
        .verify(&crypto_provider)
        .map_err(|e| anyhow!("presentation.verify() refused: {e}"))?;

    // Defense in depth: after verify(), re-confirm the (now signature-checked) key is the pin.
    if attestation.body.verifying_key() != expected_notary_key {
        return Err(anyhow!(
            "notary pin: verified attestation key does not match the pinned notary key"
        ));
    }

    let server_name = server_name.context("no authenticated server name")?;
    let ServerName::Dns(dns) = server_name;
    let server_name = dns.as_str().to_string();
    if server_name != expected_host {
        return Err(anyhow!(
            "server pin: got {server_name:?}, expected {expected_host:?}"
        ));
    }

    let mut partial = transcript.context("presentation revealed no transcript")?;
    partial.set_unauthed(b'X');
    let sent_redacted = partial.sent_unsafe().to_vec();
    let recv_redacted = partial.received_unsafe().to_vec();

    let body_start = recv_redacted
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .context("no header/body separator")?
        + 4;
    let response_body = recv_redacted[body_start..].to_vec();

    Ok(VerifiedResponse {
        response_body,
        server_name,
        connection_time: connection_info.time,
        sent_redacted,
    })
}

/// **Run the full REAL Bedrock MPC-TLS roundtrip against a SEPARATE hosted notary**, then
/// verify (pinning the notary's key + the Bedrock host) and extract the disclosed body.
/// Blocking: stands up its own multi-thread runtime. Requires live network + AWS creds.
///
/// The notary is spawned as a distinct party on a real localhost socket, owning a fresh
/// OS-random signing key the prover never sees; the returned [`BedrockRoundtrip::notary_pin`]
/// carries the pinned public key the attestation was verified under.
pub fn run_bedrock_roundtrip_blocking(ex: &BedrockExchange) -> Result<BedrockRoundtrip> {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    rt.block_on(async {
        // Stand up the SEPARATE notary party: it owns a fresh key; we only learn its address
        // and its public (pinned) key.
        let notary_key = generate_notary_key()?;
        let notary: HostedNotary = spawn_hosted_notary(notary_key, 1).await?;
        let pin = notary.pin().clone();

        // The prover reaches the notary ONLY by address.
        let presentation_bytes = prove_bedrock_presentation(ex, pin.addr).await?;
        notary.join().await?;

        // Verify under the PINNED notary key (a wrong key would be rejected).
        let verified =
            verify_bedrock_presentation(&presentation_bytes, &ex.host, &pin.verifying_key)?;

        Ok(BedrockRoundtrip {
            verified,
            presentation_bytes,
            pinned_server: ex.host.clone(),
            notary_pin: pin,
            separate_notary: true,
        })
    })
}

/// Whether the SigV4 `authorization` credential was hidden by selective disclosure.
pub fn authorization_hidden(sent_redacted: &[u8]) -> bool {
    // The revealed `authorization:` header name remains; its VALUE (AWS4-HMAC-SHA256 …) must not.
    !sent_redacted.windows(16).any(|w| w == b"AWS4-HMAC-SHA256")
}
