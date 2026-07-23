//! OFFLINE tests (no network). These prove the crypto core matches the Chutes reference:
//!
//! 1. request roundtrip — `build_e2ee_request` then play the enclave's side (decapsulate +
//!    HKDF(info=e2e-req-v1) + ChaCha20-Poly1305 + gunzip) to recover the exact OpenAI JSON;
//! 2. response roundtrip — encrypt a response to the client's `response_pk` (info=e2e-resp-v1)
//!    then `decrypt_response` recovers it;
//! 3. primitive sanity — ML-KEM sizes (1184/1088/2400/32), gzip header present;
//! 4. cross-implementation KATs vs the reference `cryptography` lib — HKDF-SHA256 derive_key,
//!    ChaCha20-Poly1305 (no AAD), and gzip cross-decompress (Rust inflates Python's gzip).
//!    These are the strongest interop checks short of a live call for the symmetric stack;
//!    ML-KEM interop is guaranteed structurally by using the SAME PQClean C.

use dregg_chutes_e2ee::crypto::{
    build_e2ee_request, chacha_decrypt, chacha_encrypt, decrypt_response, derive_key,
    encrypt_response_for_test, gzip_compress, gzip_decompress, mlkem_decapsulate, mlkem_keypair,
    INFO_REQ,
};
use dregg_chutes_e2ee::{
    MLKEM_CT_SIZE, MLKEM_PK_SIZE, MLKEM_SK_SIZE, SHARED_SECRET_SIZE, TAG_SIZE,
};
use serde_json::json;

fn sample_openai_request() -> serde_json::Value {
    json!({
        "model": "unsloth/Llama-3.2-1B-Instruct",
        "messages": [{"role": "user", "content": "Say 'hello world' and nothing else."}],
        "temperature": 0.0,
        "max_tokens": 16
    })
}

/// (1) The request-encrypt path is decryptable by an enclave holding the server sk.
#[test]
fn request_roundtrip_recovers_exact_json() {
    // Stand up a local "server" (enclave) ML-KEM-768 keypair.
    let (server_pk, server_sk) = mlkem_keypair();
    let server_pk_b64 =
        base64::Engine::encode(&base64::engine::general_purpose::STANDARD, &server_pk);

    let payload = sample_openai_request();
    let built = build_e2ee_request(&server_pk_b64, &payload).expect("build request");

    // Blob layout: mlkem_ct(1088) ‖ nonce(12) ‖ ct ‖ tag(16).
    assert!(built.blob.len() > MLKEM_CT_SIZE + 12 + TAG_SIZE);
    let mlkem_ct = &built.blob[..MLKEM_CT_SIZE];
    let nonce = &built.blob[MLKEM_CT_SIZE..MLKEM_CT_SIZE + 12];
    let ct_and_tag = &built.blob[MLKEM_CT_SIZE + 12..];
    assert_eq!(built.response_sk.len(), MLKEM_SK_SIZE);

    // Play the enclave: decapsulate → HKDF(info=e2e-req-v1) → ChaCha20-Poly1305 decrypt → gunzip.
    let shared = mlkem_decapsulate(mlkem_ct, &server_sk).expect("decapsulate");
    let sym_key = derive_key(&shared, mlkem_ct, INFO_REQ);
    let mut nbuf = [0u8; 12];
    nbuf.copy_from_slice(nonce);
    let compressed = chacha_decrypt(&sym_key, &nbuf, ct_and_tag).expect("aead decrypt");
    let json_bytes = gzip_decompress(&compressed).expect("gunzip");
    let recovered: serde_json::Value = serde_json::from_slice(&json_bytes).expect("json");

    // Every field of the original payload survives, and e2e_response_pk was appended (base64
    // of the client's 1184-byte response public key).
    for (k, v) in payload.as_object().unwrap() {
        assert_eq!(recovered.get(k), Some(v), "field {k} must round-trip");
    }
    let resp_pk_b64 = recovered
        .get("e2e_response_pk")
        .and_then(|v| v.as_str())
        .expect("e2e_response_pk present");
    let resp_pk = base64::Engine::decode(&base64::engine::general_purpose::STANDARD, resp_pk_b64)
        .expect("valid base64");
    assert_eq!(
        resp_pk.len(),
        MLKEM_PK_SIZE,
        "response pk is a 1184-byte ML-KEM-768 key"
    );
}

/// (2) The response-decrypt path is self-consistent with the documented response framing.
#[test]
fn response_roundtrip_recovers_exact_json() {
    // The client generated a response keypair inside build_e2ee_request; here we mint one
    // directly and exercise decrypt_response against a response encrypted to its pk.
    let (response_pk, response_sk) = mlkem_keypair();
    let response_json = json!({
        "id": "chatcmpl-abc",
        "object": "chat.completion",
        "choices": [{"index": 0, "message": {"role": "assistant", "content": "hello world"}}],
        "usage": {"prompt_tokens": 9, "completion_tokens": 2, "total_tokens": 11}
    });

    let blob = encrypt_response_for_test(&response_pk, &response_json).expect("encrypt response");
    let recovered = decrypt_response(&blob, &response_sk).expect("decrypt response");
    assert_eq!(recovered, response_json);
}

/// A tampered response tag must fail authentication (fail-closed).
#[test]
fn tampered_response_fails_auth() {
    let (response_pk, response_sk) = mlkem_keypair();
    let mut blob = encrypt_response_for_test(&response_pk, &json!({"ok": true})).unwrap();
    let last = blob.len() - 1;
    blob[last] ^= 0xFF; // flip a tag byte
    assert!(decrypt_response(&blob, &response_sk).is_err());
}

/// (3) Primitive sanity: ML-KEM-768 sizes + gzip header.
#[test]
fn primitive_sanity_sizes_and_gzip_header() {
    assert_eq!(MLKEM_PK_SIZE, 1184);
    assert_eq!(MLKEM_CT_SIZE, 1088);
    assert_eq!(MLKEM_SK_SIZE, 2400);
    assert_eq!(SHARED_SECRET_SIZE, 32);
    assert_eq!(TAG_SIZE, 16);

    let (pk, sk) = mlkem_keypair();
    assert_eq!(pk.len(), 1184);
    assert_eq!(sk.len(), 2400);

    // A real KEM cycle: encapsulate to pk, decapsulate with sk → same shared secret.
    let (ct, ss_enc) = dregg_chutes_e2ee::crypto::mlkem_encapsulate(&pk).expect("encapsulate");
    assert_eq!(ct.len(), 1088);
    assert_eq!(ss_enc.len(), 32);
    let ss_dec = mlkem_decapsulate(&ct, &sk).expect("decapsulate");
    assert_eq!(ss_enc, ss_dec, "ML-KEM shared secrets agree");

    // gzip magic bytes 0x1f 0x8b present in our compressed output.
    let gz = gzip_compress(b"hello dregg").unwrap();
    assert_eq!(&gz[..2], &[0x1f, 0x8b], "gzip magic header present");
    assert_eq!(gzip_decompress(&gz).unwrap(), b"hello dregg");
}

/// (4a) HKDF-SHA256 derive_key KAT vs the reference `cryptography` lib.
/// `HKDF(SHA256, len=32, salt=ct[:16], info=b"e2e-req-v1").derive(shared)` for the fixed
/// inputs below was computed by Python `cryptography` 49.0.0 (the reference's exact HKDF).
#[test]
fn hkdf_derive_key_matches_reference_kat() {
    let shared: Vec<u8> = (0..32u32).map(|i| ((i * 3 + 1) % 256) as u8).collect();
    // salt = ct[:16] where ct[i] = (i*7)%256; derive_key only reads mlkem_ct[..16].
    let ct16: Vec<u8> = (0..16u32).map(|i| ((i * 7) % 256) as u8).collect();
    let okm = derive_key(&shared, &ct16, INFO_REQ);
    let expected = hex_lit("9213332654d1331f4fae5db42171dbf44d7269e4df97757d715a93062c81c6aa");
    assert_eq!(
        okm.to_vec(),
        expected,
        "derive_key must match Python cryptography HKDF"
    );
}

/// (4b) ChaCha20-Poly1305 (IETF, no AAD) KAT vs the reference `cryptography` lib.
/// `ChaCha20Poly1305(key).encrypt(nonce, pt, None)` for the fixed inputs below.
#[test]
fn chacha20poly1305_matches_reference_kat() {
    let key = hex_lit("9213332654d1331f4fae5db42171dbf44d7269e4df97757d715a93062c81c6aa");
    let mut k = [0u8; 32];
    k.copy_from_slice(&key);
    let nonce: [u8; 12] = std::array::from_fn(|i| ((i as u32 * 5) % 256) as u8);
    let pt = b"hello dregg e2ee \x00\x01\x02 payload";

    let ct_tag = chacha_encrypt(&k, &nonce, pt).expect("encrypt");
    let expected = hex_lit(
        "3e85072eda553dfe2e221671dc71b0361d8fee121057c54d0230fd6f8e6fc20ba903750c359da5a708df7003",
    );
    assert_eq!(
        ct_tag, expected,
        "AEAD ct‖tag must match Python cryptography"
    );

    // And our own decrypt inverts it.
    let back = chacha_decrypt(&k, &nonce, &ct_tag).expect("decrypt");
    assert_eq!(back, pt);
}

/// (4c) gzip cross-decompress: Rust (flate2) inflates a gzip stream produced by Python
/// `gzip.compress` (the enclave's compressor). This is the response path — the enclave
/// gzips, we gunzip.
#[test]
fn gzip_decompresses_python_stream() {
    let py_gzip: [u8; 139] = [
        0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x3d, 0xcd, 0x41, 0x0a, 0x02,
        0x31, 0x0c, 0x05, 0xd0, 0xab, 0x94, 0xac, 0x55, 0xdc, 0x09, 0x5e, 0x45, 0x44, 0x6a, 0x1a,
        0xa6, 0xd5, 0x4c, 0x22, 0xd3, 0x88, 0x03, 0xa5, 0x77, 0x37, 0x1d, 0xd0, 0xdd, 0x4f, 0x1e,
        0x3f, 0x69, 0x50, 0x12, 0x9c, 0x03, 0x60, 0x8e, 0x86, 0xf3, 0x8b, 0xf7, 0x2b, 0xec, 0x02,
        0xe8, 0xfd, 0x41, 0x68, 0xbf, 0xfd, 0x01, 0xd5, 0x85, 0xac, 0xa8, 0x0c, 0xc4, 0xac, 0x05,
        0xa9, 0xba, 0x5e, 0x1a, 0x14, 0x49, 0xb4, 0x7a, 0x3c, 0x3a, 0xcc, 0x54, 0x6b, 0x9c, 0xc8,
        0xa7, 0x06, 0x8b, 0xf2, 0x08, 0x10, 0x6b, 0x2d, 0xd5, 0xa2, 0xd8, 0xd6, 0x54, 0x31, 0x92,
        0xed, 0x6e, 0x26, 0x66, 0x0d, 0x1f, 0x5d, 0x38, 0x41, 0xef, 0x57, 0xc7, 0xf7, 0xbf, 0x6b,
        0x6a, 0x91, 0x6f, 0xa6, 0x4f, 0x92, 0xf1, 0xe5, 0xd4, 0xfb, 0x17, 0xf2, 0xa0, 0xd5, 0x51,
        0xa6, 0x00, 0x00, 0x00,
    ];
    let inflated = gzip_decompress(&py_gzip).expect("inflate python gzip");
    let v: serde_json::Value = serde_json::from_slice(&inflated).expect("json");
    assert_eq!(
        v,
        json!({
            "id": "chatcmpl-x",
            "object": "chat.completion",
            "choices": [{"index": 0, "message": {"role": "assistant", "content": "hello world"}}],
            "usage": {"total_tokens": 7}
        })
    );
}

fn hex_lit(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}
