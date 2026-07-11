//! **A SEPARATELY-HOSTED notary party** — the Phase-E provenance seam that closes the
//! "prover controls the notary" gap.
//!
//! In the earlier spike the notary ran IN-PROCESS, wired to the prover over a
//! `tokio::io::duplex` in the *same* function that produced the presentation. It was a
//! genuine 2PC party (it co-derived the session keys, saw no plaintext), but it was not a
//! SEPARATE one: the prover instantiated it and held its signing key, so nothing stopped a
//! dishonest prover from signing its own attestation.
//!
//! This module hosts the notary as a **distinct party on a real TCP socket**. It owns its
//! secp256k1 signing key (generated from OS entropy — the prover never learns it), listens on
//! a socket, and runs the MPC-TLS commitment + attestation-signing protocol for each prover
//! that connects. The only thing published to a verifier is its **public verifying key**
//! (the pin, distributed out-of-band). A presentation is trusted iff its embedded
//! verifying key equals that pin — [`crate::tlsn_bedrock::verify_bedrock_presentation`]
//! enforces exactly that, so a wrong/unpinned notary is rejected.
//!
//! `presentation.verify()` in the vendored tlsn only checks the attestation's signature is
//! self-consistent with its *embedded* verifying key; it does NOT decide which notary to
//! trust. Trust-anchoring is the caller's job — pinning [`NotaryPin::verifying_key`].

#![cfg(feature = "tlsn-live")]

use std::io::Read as _;
use std::net::SocketAddr;

use anyhow::{Result, anyhow};
use futures::io::{AsyncReadExt as _, AsyncWriteExt as _};
use tokio::net::TcpListener;
use tokio_util::compat::TokioAsyncReadCompatExt;

use tlsn::{
    Session,
    attestation::{
        Attestation, AttestationConfig, CryptoProvider,
        request::Request as AttestationRequest,
        signing::{Secp256k1Signer, Signer as _, VerifyingKey},
    },
    config::verifier::VerifierConfig,
    connection::{CertBinding, ConnectionInfo, TranscriptLength},
    transcript::ContentType,
    verifier::{VerifierCommitStart, VerifierOutput},
    webpki::RootCertStore,
};

/// The out-of-band trust anchor for a hosted notary: where to reach it + its **pinned**
/// secp256k1 verifying key. A verifier that trusts this notary pins [`Self::verifying_key`];
/// the prover is handed only [`Self::addr`].
#[derive(Clone, Debug, PartialEq)]
pub struct NotaryPin {
    /// The socket the prover connects to (localhost for the driven test; a public address in
    /// a real deployment).
    pub addr: SocketAddr,
    /// The notary's public verifying key — the value a verifier pins.
    pub verifying_key: VerifyingKey,
}

impl NotaryPin {
    /// A short hex fingerprint of the pinned SEC1 public key, for display/logging.
    pub fn key_fingerprint(&self) -> String {
        let hex: String = self
            .verifying_key
            .data
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        // First and last 8 hex chars — enough to eyeball a pin without dumping 66 chars.
        if hex.len() > 20 {
            format!("{}…{}", &hex[..8], &hex[hex.len() - 8..])
        } else {
            hex
        }
    }
}

/// A running, separately-hosted notary party (a distinct tokio task on a real TCP socket).
/// Drop or [`Self::join`] to reclaim it.
pub struct HostedNotary {
    pin: NotaryPin,
    task: tokio::task::JoinHandle<Result<()>>,
}

impl HostedNotary {
    /// The pin (address + pinned verifying key) to hand a prover / a verifier.
    pub fn pin(&self) -> &NotaryPin {
        &self.pin
    }

    /// Await the notary task (after the prover(s) it was sized for have completed).
    pub async fn join(self) -> Result<()> {
        self.task.await?
    }
}

/// Provision a notary signing key from OS entropy. This is the notary operator's secret; it
/// is generated INSIDE the notary boundary and never crosses to the prover — that is the
/// whole point of the separate party. In a real deployment the notary persists this key and
/// publishes only its public half.
pub fn generate_notary_key() -> Result<k256::ecdsa::SigningKey> {
    // Rejection-sample a 32-byte scalar in `[1, n)` from `/dev/urandom` (portable on
    // darwin/linux, zero extra deps). A non-canonical/zero draw is astronomically rare;
    // retry a handful of times to be safe.
    let mut urandom = std::fs::File::open("/dev/urandom")?;
    for _ in 0..8 {
        let mut bytes = [0u8; 32];
        urandom.read_exact(&mut bytes)?;
        if let Ok(key) = k256::ecdsa::SigningKey::from_slice(&bytes) {
            return Ok(key);
        }
    }
    Err(anyhow!(
        "failed to sample a canonical secp256k1 signing key"
    ))
}

/// The public verifying key for a signing key, in the tlsn `VerifyingKey` shape (SEC1).
pub fn verifying_key_of(signing_key: &k256::ecdsa::SigningKey) -> Result<VerifyingKey> {
    Ok(Secp256k1Signer::new(&signing_key.to_bytes())?.verifying_key())
}

/// **Spawn a separate hosted notary** on `127.0.0.1:<ephemeral>`. It owns `signing_key`
/// (the prover only ever receives `pin().addr`), and serves exactly `max_sessions` prover
/// connections before its task returns (`1` for the driven single-roundtrip test).
///
/// Localhost keeps the driven test hermetic; the architecture — a distinct party reached
/// over a socket, its key never shared, its public key pinned by the verifier — is identical
/// to a notary hosted at a public internet address.
pub async fn spawn_hosted_notary(
    signing_key: k256::ecdsa::SigningKey,
    max_sessions: usize,
) -> Result<HostedNotary> {
    let verifying_key = verifying_key_of(&signing_key)?;
    let listener = TcpListener::bind(("127.0.0.1", 0)).await?;
    let addr = listener.local_addr()?;
    let pin = NotaryPin {
        addr,
        verifying_key,
    };

    let task = tokio::spawn(async move {
        for _ in 0..max_sessions {
            let (socket, _peer) = listener.accept().await?;
            run_notary_session(socket, &signing_key).await?;
        }
        Ok(())
    });

    Ok(HostedNotary { pin, task })
}

/// One notary session: run the MPC-TLS commitment protocol with the connected prover, receive
/// its attestation request, and sign an [`Attestation`] with the notary's own key. The server
/// certificate is verified against the Mozilla roots, binding the attestation to the REAL
/// Amazon-authenticated Bedrock session. This is the same protocol the in-process spike ran —
/// but the key is the notary's alone and the transport is a real socket.
pub async fn run_notary_session<S>(socket: S, signing_key: &k256::ecdsa::SigningKey) -> Result<()>
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

    // The notary's OWN signing key — never shared with the prover.
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
