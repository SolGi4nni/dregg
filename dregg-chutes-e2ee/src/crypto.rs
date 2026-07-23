//! The Chutes E2EE crypto core — an EXACT port of the authoritative reference
//! `chutes_e2ee/crypto.py` (ML-KEM-768 → HKDF-SHA256 → ChaCha20-Poly1305 (IETF) over gzip).
//!
//! This module is transport-free and deterministic given its RNG draws, so it is fully
//! unit-testable offline. Every framing/KDF/AEAD decision below is annotated with the
//! reference `crypto.py` line it mirrors, because the enclave decrypts what we produce: a
//! byte-level divergence in the mlkem_ct/nonce/ct/tag layout, the HKDF salt/info, or the
//! AEAD would make the response undecryptable.
//!
//! What must match byte-for-byte (and does): the KEM ciphertext wire format (PQClean C, same
//! as the reference), the HKDF salt (`mlkem_ct[:16]`) + info strings, the ChaCha20-Poly1305
//! IETF construction with NO AAD and a 12-byte nonce, and the blob layout
//! `mlkem_ct(1088) ‖ nonce(12) ‖ ciphertext ‖ tag(16)`. What need NOT match byte-for-byte
//! (and is free to differ): the JSON key order / whitespace and the exact gzip byte stream —
//! both live *inside* the AEAD and are re-parsed / re-inflated by the enclave, so only their
//! decoded value matters (a JSON object with the same fields, inflating to the same bytes).

use base64::Engine as _;
use chacha20poly1305::aead::Aead;
use chacha20poly1305::{ChaCha20Poly1305, KeyInit, Nonce};
use hkdf::Hkdf;
use pqcrypto_mlkem::mlkem768;
use pqcrypto_traits::kem::{Ciphertext as _, PublicKey as _, SecretKey as _, SharedSecret as _};
use sha2::Sha256;
use std::io::{Read, Write};

/// ML-KEM-768 ciphertext length (`crypto.py` `MLKEM_CT_SIZE = 1088`).
pub const MLKEM_CT_SIZE: usize = 1088;
/// ML-KEM-768 public-key length.
pub const MLKEM_PK_SIZE: usize = 1184;
/// ML-KEM-768 secret-key length.
pub const MLKEM_SK_SIZE: usize = 2400;
/// ML-KEM-768 shared-secret length.
pub const SHARED_SECRET_SIZE: usize = 32;
/// Poly1305 tag length (`crypto.py` `TAG_SIZE = 16`).
pub const TAG_SIZE: usize = 16;
/// ChaCha20-Poly1305 IETF nonce length (12 bytes — `os.urandom(12)` in `crypto.py`).
pub const AEAD_NONCE_SIZE: usize = 12;

/// HKDF `info` for the request key (`crypto.py` `INFO_REQ = b"e2e-req-v1"`).
pub const INFO_REQ: &[u8] = b"e2e-req-v1";
/// HKDF `info` for the (non-stream) response key (`crypto.py` `INFO_RESP = b"e2e-resp-v1"`).
pub const INFO_RESP: &[u8] = b"e2e-resp-v1";
/// HKDF `info` for the streaming key (`crypto.py` `INFO_STREAM = b"e2e-stream-v1"`).
pub const INFO_STREAM: &[u8] = b"e2e-stream-v1";

/// Crypto-layer errors. All are fail-closed (a decrypt/verify failure is an `Err`, never a
/// partial or default value).
#[derive(Debug, thiserror::Error)]
pub enum CryptoError {
    #[error("base64 decode: {0}")]
    Base64(#[from] base64::DecodeError),
    #[error("ML-KEM key/ciphertext byte length invalid: {0}")]
    MlKem(String),
    #[error("payload must be a JSON object (got a non-object value)")]
    PayloadNotObject,
    #[error("JSON: {0}")]
    Json(#[from] serde_json::Error),
    #[error("gzip: {0}")]
    Gzip(#[from] std::io::Error),
    #[error("ChaCha20-Poly1305 {0} failed (bad key length or authentication tag)")]
    Aead(&'static str),
    #[error("RNG failure: {0}")]
    Rng(String),
    #[error("response blob too short: {0} bytes (need >= {1})")]
    ShortBlob(usize, usize),
}

/// `derive_key(shared_secret, mlkem_ct, info)` — HKDF-SHA256, `length=32`,
/// `salt=mlkem_ct[:16]`, `info=info` (`crypto.py:28-34`). The salt is the FIRST 16 bytes of
/// the KEM ciphertext, not the whole ciphertext.
pub fn derive_key(shared_secret: &[u8], mlkem_ct: &[u8], info: &[u8]) -> [u8; 32] {
    let salt = &mlkem_ct[..16];
    let hk = Hkdf::<Sha256>::new(Some(salt), shared_secret);
    let mut okm = [0u8; 32];
    // Only fails if the requested length > 255*HashLen; 32 <= 255*32, so this is infallible.
    hk.expand(info, &mut okm)
        .expect("HKDF-SHA256 expand of 32 bytes is always valid");
    okm
}

/// `gzip.compress(data)` (`crypto.py:65`). Produces a gzip container (header + DEFLATE +
/// CRC). The exact bytes are compressor-dependent and need not match Python — the enclave
/// gunzips it, so only round-trip-inflatability matters (proven in tests).
pub fn gzip_compress(data: &[u8]) -> Result<Vec<u8>, std::io::Error> {
    let mut enc = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
    enc.write_all(data)?;
    enc.finish()
}

/// `gzip.decompress(data)` (`crypto.py:83`). Inflates a gzip container produced by ANY
/// conforming gzip compressor (Python's included) — this is the response path.
pub fn gzip_decompress(data: &[u8]) -> Result<Vec<u8>, std::io::Error> {
    let mut dec = flate2::read::GzDecoder::new(data);
    let mut out = Vec::new();
    dec.read_to_end(&mut out)?;
    Ok(out)
}

/// `ChaCha20Poly1305(key).encrypt(nonce, plaintext, None)` → `ct ‖ tag`
/// (`crypto.py:37-39`). NO associated data (the Python `None` == RFC 8439 zero-length AAD,
/// which the `chacha20poly1305` crate's `encrypt(nonce, &[u8])` also uses). Returns the
/// combined `ciphertext ‖ tag(16)`, exactly the bytes appended to the blob. Public so the
/// AEAD wiring can be pinned by a known-answer test against the reference lib.
pub fn chacha_encrypt(
    key: &[u8; 32],
    nonce: &[u8; 12],
    plaintext: &[u8],
) -> Result<Vec<u8>, CryptoError> {
    let cipher = ChaCha20Poly1305::new_from_slice(key).map_err(|_| CryptoError::Aead("init"))?;
    cipher
        .encrypt(Nonce::from_slice(nonce), plaintext)
        .map_err(|_| CryptoError::Aead("encrypt"))
}

/// `ChaCha20Poly1305(key).decrypt(nonce, ciphertext + tag, None)` (`crypto.py:42-43`).
/// `ct_and_tag` is the combined `ciphertext ‖ tag(16)`.
pub fn chacha_decrypt(
    key: &[u8; 32],
    nonce: &[u8; 12],
    ct_and_tag: &[u8],
) -> Result<Vec<u8>, CryptoError> {
    let cipher = ChaCha20Poly1305::new_from_slice(key).map_err(|_| CryptoError::Aead("init"))?;
    cipher
        .decrypt(Nonce::from_slice(nonce), ct_and_tag)
        .map_err(|_| CryptoError::Aead("decrypt"))
}

fn fill_random(buf: &mut [u8]) -> Result<(), CryptoError> {
    getrandom::fill(buf).map_err(|e| CryptoError::Rng(e.to_string()))
}

/// The result of [`build_e2ee_request`]: the binary blob to POST as the request body, and
/// the ephemeral ML-KEM-768 secret key needed to decrypt the response
/// (`crypto.py` `E2EERequestResult`).
#[derive(Clone)]
pub struct E2eeRequest {
    /// `mlkem_ct(1088) ‖ nonce(12) ‖ ciphertext ‖ tag(16)`.
    pub blob: Vec<u8>,
    /// The 2400-byte ephemeral response secret key. KEEP PRIVATE — it decrypts the response.
    pub response_sk: Vec<u8>,
}

/// `build_e2ee_request(e2e_pubkey_b64, payload)` — EXACT port of `crypto.py:52-71`.
///
/// 1. generate a FRESH client ephemeral ML-KEM-768 keypair `(response_pk, response_sk)`;
/// 2. `mlkem_ct, shared = MLKEM768.encapsulate(e2e_pubkey)` (NB: the Rust crate returns
///    `(shared, ct)`, the Python `(ct, shared)` — same values, we bind them by name);
/// 3. `sym_key = derive_key(shared, mlkem_ct, b"e2e-req-v1")`;
/// 4. `payload["e2e_response_pk"] = base64(response_pk)`;
/// 5. `compressed = gzip(json(payload))`;
/// 6. `nonce = 12 random bytes`;
/// 7. `ct ‖ tag = ChaCha20Poly1305(sym_key).encrypt(nonce, compressed)`;
/// 8. `blob = mlkem_ct ‖ nonce ‖ ct ‖ tag`.
pub fn build_e2ee_request(
    e2e_pubkey_b64: &str,
    payload: &serde_json::Value,
) -> Result<E2eeRequest, CryptoError> {
    // (1) fresh response keypair.
    let (response_pk, response_sk) = mlkem768::keypair();

    // (2) encapsulate to the instance's e2e pubkey.
    let e2e_pubkey_bytes =
        base64::engine::general_purpose::STANDARD.decode(e2e_pubkey_b64.trim())?;
    let server_pk = mlkem768::PublicKey::from_bytes(&e2e_pubkey_bytes)
        .map_err(|e| CryptoError::MlKem(format!("instance e2e pubkey: {e}")))?;
    let (shared, ct) = mlkem768::encapsulate(&server_pk);
    let mlkem_ct = ct.as_bytes();

    // (3) request key.
    let sym_key = derive_key(shared.as_bytes(), mlkem_ct, INFO_REQ);

    // (4) payload with the response pk (inserted last, mirroring `{**payload, ...}`; key
    //     order is irrelevant to the enclave's json.loads).
    let mut obj = payload
        .as_object()
        .ok_or(CryptoError::PayloadNotObject)?
        .clone();
    obj.insert(
        "e2e_response_pk".to_string(),
        serde_json::Value::String(
            base64::engine::general_purpose::STANDARD.encode(response_pk.as_bytes()),
        ),
    );
    let json_bytes = serde_json::to_vec(&serde_json::Value::Object(obj))?;

    // (5) gzip.
    let compressed = gzip_compress(&json_bytes)?;

    // (6) random 12-byte AEAD nonce.
    let mut nonce = [0u8; AEAD_NONCE_SIZE];
    fill_random(&mut nonce)?;

    // (7) encrypt (no AAD) → ct ‖ tag.
    let ct_and_tag = chacha_encrypt(&sym_key, &nonce, &compressed)?;

    // (8) assemble the blob.
    let mut blob = Vec::with_capacity(MLKEM_CT_SIZE + AEAD_NONCE_SIZE + ct_and_tag.len());
    blob.extend_from_slice(mlkem_ct);
    blob.extend_from_slice(&nonce);
    blob.extend_from_slice(&ct_and_tag);

    Ok(E2eeRequest {
        blob,
        response_sk: response_sk.as_bytes().to_vec(),
    })
}

/// `decrypt_response(response_blob, response_sk)` — EXACT port of `crypto.py:74-84`.
///
/// `blob = mlkem_ct(1088) ‖ nonce(12) ‖ ciphertext ‖ tag(16)`;
/// `shared = MLKEM768.decapsulate(response_sk, mlkem_ct)`;
/// `key = derive_key(shared, mlkem_ct, b"e2e-resp-v1")`;
/// `json = gzip_decompress(ChaCha20Poly1305(key).decrypt(nonce, ct ‖ tag))`.
pub fn decrypt_response(
    response_blob: &[u8],
    response_sk: &[u8],
) -> Result<serde_json::Value, CryptoError> {
    let min = MLKEM_CT_SIZE + AEAD_NONCE_SIZE + TAG_SIZE;
    if response_blob.len() < min {
        return Err(CryptoError::ShortBlob(response_blob.len(), min));
    }
    let mlkem_ct = &response_blob[..MLKEM_CT_SIZE];
    let nonce_bytes = &response_blob[MLKEM_CT_SIZE..MLKEM_CT_SIZE + AEAD_NONCE_SIZE];
    // ciphertext ‖ tag = everything after the nonce (the crate splits the trailing 16-byte tag).
    let ct_and_tag = &response_blob[MLKEM_CT_SIZE + AEAD_NONCE_SIZE..];

    let sk = mlkem768::SecretKey::from_bytes(response_sk)
        .map_err(|e| CryptoError::MlKem(format!("response secret key: {e}")))?;
    let ct = mlkem768::Ciphertext::from_bytes(mlkem_ct)
        .map_err(|e| CryptoError::MlKem(format!("response mlkem_ct: {e}")))?;
    let shared = mlkem768::decapsulate(&ct, &sk);
    let sym_key = derive_key(shared.as_bytes(), mlkem_ct, INFO_RESP);

    let mut nonce = [0u8; AEAD_NONCE_SIZE];
    nonce.copy_from_slice(nonce_bytes);
    let plaintext = chacha_decrypt(&sym_key, &nonce, ct_and_tag)?;
    let json_bytes = gzip_decompress(&plaintext)?;
    Ok(serde_json::from_slice(&json_bytes)?)
}

/// `decrypt_stream_init(response_sk, mlkem_ct_b64)` — derive the streaming symmetric key
/// from the `e2e_init` SSE event (`crypto.py:87-91`, `info=b"e2e-stream-v1"`).
pub fn decrypt_stream_init(
    response_sk: &[u8],
    mlkem_ct_b64: &str,
) -> Result<[u8; 32], CryptoError> {
    let mlkem_ct = base64::engine::general_purpose::STANDARD.decode(mlkem_ct_b64.trim())?;
    let sk = mlkem768::SecretKey::from_bytes(response_sk)
        .map_err(|e| CryptoError::MlKem(format!("response secret key: {e}")))?;
    let ct = mlkem768::Ciphertext::from_bytes(&mlkem_ct)
        .map_err(|e| CryptoError::MlKem(format!("stream init mlkem_ct: {e}")))?;
    let shared = mlkem768::decapsulate(&ct, &sk);
    Ok(derive_key(shared.as_bytes(), &mlkem_ct, INFO_STREAM))
}

/// `decrypt_stream_chunk(enc_chunk_b64, stream_key)` — decrypt one streaming chunk
/// (`crypto.py:94-100`): base64 → `nonce(12) ‖ ciphertext ‖ tag(16)` → ChaCha20-Poly1305.
pub fn decrypt_stream_chunk(
    enc_chunk_b64: &str,
    stream_key: &[u8; 32],
) -> Result<Vec<u8>, CryptoError> {
    let raw = base64::engine::general_purpose::STANDARD.decode(enc_chunk_b64.trim())?;
    if raw.len() < AEAD_NONCE_SIZE + TAG_SIZE {
        return Err(CryptoError::ShortBlob(
            raw.len(),
            AEAD_NONCE_SIZE + TAG_SIZE,
        ));
    }
    let mut nonce = [0u8; AEAD_NONCE_SIZE];
    nonce.copy_from_slice(&raw[..AEAD_NONCE_SIZE]);
    let ct_and_tag = &raw[AEAD_NONCE_SIZE..];
    chacha_decrypt(stream_key, &nonce, ct_and_tag)
}

/// Generate a fresh ML-KEM-768 keypair, returned as raw bytes `(public_key, secret_key)`
/// (1184, 2400). Exposed for tests that need to stand up a local "server" keypair, and for
/// callers who want to pre-generate the response keypair.
pub fn mlkem_keypair() -> (Vec<u8>, Vec<u8>) {
    let (pk, sk) = mlkem768::keypair();
    (pk.as_bytes().to_vec(), sk.as_bytes().to_vec())
}

/// Decapsulate `mlkem_ct` with `sk` to recover the 32-byte shared secret. Exposed so tests
/// can play the enclave's side of the request path.
pub fn mlkem_decapsulate(mlkem_ct: &[u8], sk: &[u8]) -> Result<[u8; 32], CryptoError> {
    let sk = mlkem768::SecretKey::from_bytes(sk)
        .map_err(|e| CryptoError::MlKem(format!("secret key: {e}")))?;
    let ct = mlkem768::Ciphertext::from_bytes(mlkem_ct)
        .map_err(|e| CryptoError::MlKem(format!("ciphertext: {e}")))?;
    let ss = mlkem768::decapsulate(&ct, &sk);
    let mut out = [0u8; 32];
    out.copy_from_slice(ss.as_bytes());
    Ok(out)
}

/// Encapsulate to `pk` (raw 1184 bytes), returning `(mlkem_ct(1088), shared(32))` — the
/// name order of `crypto.py`'s `mlkem_encrypt`. Exposed so tests can play the enclave's side
/// of the response path (encrypt a response to the client's `response_pk`).
pub fn mlkem_encapsulate(pk: &[u8]) -> Result<(Vec<u8>, [u8; 32]), CryptoError> {
    let pk = mlkem768::PublicKey::from_bytes(pk)
        .map_err(|e| CryptoError::MlKem(format!("public key: {e}")))?;
    let (ss, ct) = mlkem768::encapsulate(&pk);
    let mut shared = [0u8; 32];
    shared.copy_from_slice(ss.as_bytes());
    Ok((ct.as_bytes().to_vec(), shared))
}

/// Build a non-stream E2EE RESPONSE blob (the enclave's side of `decrypt_response`), for
/// tests: `mlkem_ct ‖ nonce ‖ ct ‖ tag`, key derived with `info=b"e2e-resp-v1"`. Not used
/// on the request path.
pub fn encrypt_response_for_test(
    response_pk: &[u8],
    payload: &serde_json::Value,
) -> Result<Vec<u8>, CryptoError> {
    let (mlkem_ct, shared) = mlkem_encapsulate(response_pk)?;
    let sym_key = derive_key(&shared, &mlkem_ct, INFO_RESP);
    let compressed = gzip_compress(&serde_json::to_vec(payload)?)?;
    let mut nonce = [0u8; AEAD_NONCE_SIZE];
    fill_random(&mut nonce)?;
    let ct_and_tag = chacha_encrypt(&sym_key, &nonce, &compressed)?;
    let mut blob = Vec::with_capacity(MLKEM_CT_SIZE + AEAD_NONCE_SIZE + ct_and_tag.len());
    blob.extend_from_slice(&mlkem_ct);
    blob.extend_from_slice(&nonce);
    blob.extend_from_slice(&ct_and_tag);
    Ok(blob)
}
