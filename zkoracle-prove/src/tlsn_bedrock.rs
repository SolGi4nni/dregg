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
//! **Honest spike caveat:** the notary here runs IN-PROCESS (a real 2PC party that co-derives the
//! session keys and sees no plaintext — still a genuine MPC-TLS attestation of the Bedrock
//! session). Production provenance additionally needs the notary hosted as a SEPARATE party
//! (a deploy step, not a crypto gap): the Bedrock session itself is 100% real here.

#![cfg(feature = "tlsn-live")]

use std::future::IntoFuture;

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
    webpki::RootCertStore,
};
use tlsn_formats::http::{DefaultHttpCommitter, HttpCommit, HttpTranscript};

use crate::sigv4::{AwsCredentials, SignRequest, sign};
use crate::tlsn_live::VerifiedResponse;

// The 2PC preprocesses these bounds. A short (maxTokens-capped) Claude completion + Amazon's
// response headers fit well under 32 KiB; the request is a small signed POST.
const MAX_SENT_DATA: usize = 1 << 12;
const MAX_RECV_DATA: usize = 1 << 15;

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

/// A completed real roundtrip against live Bedrock: the verified response + the raw presentation.
#[derive(Clone, Debug)]
pub struct BedrockRoundtrip {
    pub verified: VerifiedResponse,
    pub presentation_bytes: Vec<u8>,
    pub pinned_server: String,
}

/// The in-process notary — a real tlsn verifier running the MPC-TLS commitment protocol and
/// signing a secp256k1 `Attestation`. Verifies the server cert against the Mozilla roots (so it
/// binds an attestation to the REAL Amazon-authenticated session). Identical in spirit to
/// [`crate::tlsn_live`]'s notary, but with the webpki root store.
async fn notary<S>(socket: S) -> Result<()>
where
    S: tokio::io::AsyncRead + tokio::io::AsyncWrite + Send + Sync + Unpin + 'static,
{
    let session = Session::new(socket.compat());
    let (driver, mut handle) = session.split();
    let driver_task = tokio::spawn(driver);

    let verifier_config = VerifierConfig::builder()
        .root_store(RootCertStore::mozilla())
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
        .filter_map(|r| (r.typ == ContentType::ApplicationData).then_some(r.ciphertext.len()))
        .sum();
    let recv_len: usize = tls_transcript
        .recv()
        .iter()
        .filter_map(|r| (r.typ == ContentType::ApplicationData).then_some(r.ciphertext.len()))
        .sum();

    handle.close();
    let mut socket = driver_task.await??;

    let mut request_bytes = Vec::new();
    socket.read_to_end(&mut request_bytes).await?;
    let request: AttestationRequest = bincode::deserialize(&request_bytes)?;

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
    socket.write_all(&bincode::serialize(&attestation)?).await?;
    socket.close().await?;
    Ok(())
}

/// **Run the REAL MPC-TLS 2PC prover against live Bedrock** and produce a signed presentation.
async fn prove_bedrock_presentation(ex: &BedrockExchange) -> Result<Vec<u8>> {
    let (notary_socket, prover_notary_socket) = tokio::io::duplex(1 << 24);
    let notary_task = tokio::spawn(notary(notary_socket));

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

    notary_task.await??;
    Ok(bytes)
}

/// Verify a real Bedrock presentation against the Mozilla roots and pin the Bedrock host,
/// extracting the authenticated response body (Claude's genuine completion) with the SigV4
/// `authorization` value redacted to `X`.
pub fn verify_bedrock_presentation(
    presentation_bytes: &[u8],
    expected_host: &str,
) -> Result<VerifiedResponse> {
    let presentation: Presentation =
        bincode::deserialize(presentation_bytes).context("presentation does not deserialize")?;

    let crypto_provider = CryptoProvider {
        cert: ServerCertVerifier::mozilla(),
        ..Default::default()
    };

    let PresentationOutput {
        server_name,
        connection_info,
        transcript,
        ..
    } = presentation
        .verify(&crypto_provider)
        .map_err(|e| anyhow!("presentation.verify() refused: {e}"))?;

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

/// **Run the full REAL Bedrock MPC-TLS roundtrip**, then verify + extract the disclosed body.
/// Blocking: stands up its own multi-thread runtime. Requires live network + AWS creds.
pub fn run_bedrock_roundtrip_blocking(ex: &BedrockExchange) -> Result<BedrockRoundtrip> {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    let presentation_bytes = rt.block_on(prove_bedrock_presentation(ex))?;
    let verified = verify_bedrock_presentation(&presentation_bytes, &ex.host)?;
    Ok(BedrockRoundtrip {
        verified,
        presentation_bytes,
        pinned_server: ex.host.clone(),
    })
}

/// Whether the SigV4 `authorization` credential was hidden by selective disclosure.
pub fn authorization_hidden(sent_redacted: &[u8]) -> bool {
    // The revealed `authorization:` header name remains; its VALUE (AWS4-HMAC-SHA256 …) must not.
    !sent_redacted.windows(16).any(|w| w == b"AWS4-HMAC-SHA256")
}
