//! ⚑ **THE COSMOS VK COMMITMENT: A HASH OF A LABEL, THEN AN UNCHECKED FIELD.**
//!
//! Two defects, closed on two different days, and the second one was hiding
//! behind the first.
//!
//! **2026-07-28 — the VALUE.** Every chain in this repo pinned its
//! "verifying-key commitment" as `keccak256("dregg-settlement-vk-dev-setup")` =
//! `0x18f57474…31e1ff76`. The preimage contains **zero VK bytes**, so that is
//! the value for the dev key, for an MPC ceremony key, for a key an attacker
//! generated, and for every key anyone will ever generate. A VK regeneration
//! left all three chains' pins byte-identical: they matched **by construction**,
//! not by agreement about a key. The pin became [`vk::VK_DIGEST`], keccak256
//! over the canonical serialization of the actual key.
//!
//! **2026-07-30 — the COMPARISON.** Fixing the value left the pin **inert on
//! this chain**. `instantiate` checked
//!
//! ```text
//! msg.verifying_key_hash.trim_start_matches("0x").trim_matches('0').is_empty()
//! ```
//!
//! — i.e. it refused all-zero strings and accepted `"0x1"`, the superseded label
//! hash, and every other 32 bytes — then wrote the value to `Config`, where
//! `settle` never read it and one query served it back. A commitment the
//! committer chooses freely is not a commitment. `instantiate` now REFUSES any
//! declaration but the digest of the key this wasm actually verifies against,
//! matching Solana `processor.rs::init` and the EVM `DreggSettlement`
//! constructor.
//!
//! ## What actually gates acceptance here (it is NOT the pin)
//!
//! `settle` accepts iff `verifier::verify` passes against the constants in
//! `vk.rs`, which are **compiled into the wasm**. The pin cannot be that gate on
//! any of the three chains, because the key is in the code, not in the pin. What
//! the pin CAN be — and now is — is a **deployment-time refusal**: an instance
//! cannot come into existence declaring a key other than the one it verifies
//! against.

use cosmwasm_std::testing::{message_info, mock_dependencies, mock_env};
use cosmwasm_std::{from_json, Addr};

use cosmos_settlement::error::ContractError;
use cosmos_settlement::msg::{InstantiateMsg, QueryMsg, RootResponse};
use cosmos_settlement::{hex_digest, instantiate, query, vk};

/// The superseded pin, kept as a literal so the flag day stays findable.
const OLD_LABEL_PIN: &str = "0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76";

/// The canonical genesis anchor for these tests (8 canonical BabyBear lanes).
const GENESIS: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

fn try_instantiate(vk_hash: &str) -> Result<(), ContractError> {
    let mut deps = mock_dependencies();
    let info = message_info(&Addr::unchecked("deployer"), &[]);
    instantiate(
        deps.as_mut(),
        mock_env(),
        info,
        InstantiateMsg {
            genesis_root: GENESIS,
            verifying_key_hash: vk_hash.to_string(),
        },
    )
    .map(|_| ())
}

// ---------------------------------------------------------------------------
// The commitment is a FUNCTION OF THE KEY
// ---------------------------------------------------------------------------

/// The generated constant is the keccak256 of the canonical serialization of
/// the key in `vk.rs`, and byte-identical to the EVM `DreggSettlementVK.VK_DIGEST`
/// and Solana `vk::VK_DIGEST` — all three emitted from `chain/codegen/dregg_vk.json`.
/// Cross-chain pin equality therefore means "the same key"; under the label hash
/// it meant "the same string literal".
#[test]
fn the_pin_is_the_cross_chain_key_digest() {
    assert_eq!(
        hex_digest(&vk::VK_DIGEST),
        "0xcfda612f472e998d1f1bad1bf545ec5b39ca99b64db94e46edf2e8d3790a37cc",
        "must equal DreggSettlementVK.VK_DIGEST (EVM) and solana vk::VK_DIGEST"
    );
    assert_ne!(
        hex_digest(&vk::VK_DIGEST),
        OLD_LABEL_PIN,
        "the key-derived pin must differ from the label hash it replaced"
    );
}

/// ⚑ **THE FIRST POLE, AND THE ONE THAT MATTERS.** Two DIFFERENT verifying keys
/// must produce DIFFERENT commitments. Digest every single-word perturbation of
/// the deployed key and require the pin to move for every one — then show the
/// label hash moves for NONE of them, which is the defect stated as a
/// measurement rather than as prose.
#[test]
fn every_verifying_key_word_moves_the_pin_and_the_label_moves_for_none() {
    let base = vk_digest_of(&VkWords::deployed());
    assert_eq!(
        base,
        vk::VK_DIGEST,
        "the digest routine must reproduce the pin"
    );

    let mut seen = vec![base];
    let n = VkWords::deployed().words.len();
    assert_eq!(
        n, 76,
        "alpha(2) + 5 G2 (4 each) + ic0(2) + 26 IC bases (2 each)"
    );

    for i in 0..n {
        // A different key: one field-element word incremented.
        let mut k = VkWords::deployed();
        k.words[i] = bump_decimal(&k.words[i]);
        let moved = vk_digest_of(&k);
        assert!(
            !seen.contains(&moved),
            "word {i}: a different verifying key must not reuse a commitment"
        );
        seen.push(moved);

        // The superseded pin, over the very same 76 different keys.
        assert_eq!(
            hex_digest(&keccak(b"dregg-settlement-vk-dev-setup")),
            OLD_LABEL_PIN,
            "word {i}: the label hash is a CONSTANT function of the key"
        );
    }

    assert_eq!(seen.len(), 77, "77 keys, 77 pairwise-distinct commitments");
}

// ---------------------------------------------------------------------------
// The commitment is COMPARED (the 2026-07-30 half)
// ---------------------------------------------------------------------------

/// The accept pole: the key's own digest instantiates, in either case and with
/// or without the `0x` prefix. Comparison is over BYTES — two spellings of the
/// same key must not be able to disagree about it.
#[test]
fn the_keys_own_digest_instantiates_in_every_spelling() {
    let canonical = hex_digest(&vk::VK_DIGEST);
    let bare = canonical.trim_start_matches("0x").to_string();
    for spelling in [
        canonical.clone(),
        bare.clone(),
        canonical.to_uppercase().replace("0X", "0x"),
        bare.to_uppercase(),
    ] {
        try_instantiate(&spelling).unwrap_or_else(|e| {
            panic!("the correct key digest must instantiate ({spelling}): {e}")
        });
    }
}

/// ⚑ **THE REFUSAL.** Every one of these was ACCEPTED before 2026-07-30, when
/// the only constraint was "the string is not all zeros" — including the
/// superseded cross-chain pin, which is the whole point: the artifact whose job
/// is to notice the key changed used to accept a value that never mentioned it.
#[test]
fn a_declaration_that_is_not_the_keys_digest_is_refused() {
    let expected = hex_digest(&vk::VK_DIGEST);

    let mut wrong = vec![
        OLD_LABEL_PIN.to_string(),
        // The old check's own escape hatch: non-zero, and otherwise arbitrary.
        format!("0x{}", "0".repeat(63) + "1"),
        hex_digest(&keccak(b"dregg-settlement-vk-v1")),
        hex_digest(&keccak(b"test-vk")),
    ];
    // The right answer with a single bit flipped.
    let mut off_by_one = vk::VK_DIGEST;
    off_by_one[31] ^= 1;
    wrong.push(hex_digest(&off_by_one));

    for w in &wrong {
        assert_ne!(w, &expected, "the foil must actually be wrong");
        match try_instantiate(w) {
            Err(ContractError::VkDigestMismatch { expected: e, given }) => {
                assert_eq!(e, expected);
                assert_eq!(&given, w);
            }
            other => panic!("expected VkDigestMismatch for {w}, got {other:?}"),
        }
    }
}

/// The all-zero case the old check DID catch still fails — subsumed, with a
/// reason. A keccak256 over a 2458-byte preimage is never zero.
#[test]
fn the_zero_declaration_is_still_refused_now_with_a_reason() {
    let zero = format!("0x{}", "0".repeat(64));
    assert!(
        matches!(
            try_instantiate(&zero),
            Err(ContractError::VkDigestMismatch { .. })
        ),
        "zero is refused as a wrong key, not as a special case"
    );
    assert_ne!(hex_digest(&vk::VK_DIGEST), zero);
}

/// A declaration that is not 32 bytes of hex cannot denote a key at all, and is
/// refused before any comparison.
#[test]
fn a_malformed_declaration_is_refused() {
    for bad in ["", "0x", "not-hex", "0xdeadbeef", &"0xab".repeat(40)] {
        assert!(
            matches!(
                try_instantiate(bad),
                Err(ContractError::MalformedVkDigest(_))
            ),
            "malformed declaration {bad:?} must be refused"
        );
    }
}

/// ⚑ ANTI-VACUITY / READ-THROUGH. The query answers from `vk::VK_DIGEST`, not
/// from a stored copy of what the instantiator typed — so the reported
/// commitment is the key this contract verifies against by construction, and
/// there is no second copy that could go stale or disagree.
#[test]
fn the_query_reports_the_compiled_in_key_not_a_stored_string() {
    let mut deps = mock_dependencies();
    let info = message_info(&Addr::unchecked("deployer"), &[]);
    instantiate(
        deps.as_mut(),
        mock_env(),
        info,
        InstantiateMsg {
            genesis_root: GENESIS,
            // Deliberately the NON-canonical spelling: uppercase, no prefix.
            verifying_key_hash: hex::encode_upper(vk::VK_DIGEST),
        },
    )
    .expect("the same key in a different spelling must instantiate");

    let raw = query(deps.as_ref(), mock_env(), QueryMsg::VerifyingKeyHash {}).unwrap();
    let got: RootResponse = from_json(raw).unwrap();
    assert_eq!(
        got.root,
        hex_digest(&vk::VK_DIGEST),
        "the query must answer from the key, canonically, not echo the input string"
    );
}

// ---------------------------------------------------------------------------
// A local, independent re-implementation of the digest.
//
// Deliberately NOT calling the contract's own serializer: this hashes the key
// out of `vk.rs`'s decimal strings by a separate route, so `vk::VK_DIGEST`
// agreeing with it is a measurement of the key rather than a restatement of the
// constant. The preimage is pinned in `solana-settlement/src/vk_digest.rs`.
// ---------------------------------------------------------------------------

struct VkWords {
    /// The 76 field-element words as decimal strings, in the digest's pinned
    /// order: alpha(2) | betaNeg,gammaNeg,deltaNeg,pedersenG,pedersenGSigma
    /// (4 each, EIP-197 imaginary-first) | ic0(2) | ic[i](2 each).
    words: Vec<String>,
}

impl VkWords {
    fn deployed() -> Self {
        let mut w: Vec<String> = Vec::with_capacity(76);
        w.push(vk::ALPHA_G1.0.to_string());
        w.push(vk::ALPHA_G1.1.to_string());
        for g2 in [
            vk::BETA_NEG_G2,
            vk::GAMMA_NEG_G2,
            vk::DELTA_NEG_G2,
            vk::PEDERSEN_G_G2,
            vk::PEDERSEN_GSIGMA_G2,
        ] {
            // Stored as ((x.c0, x.c1), (y.c0, y.c1)); the digest takes the
            // imaginary coordinate first (EIP-197): x1, x0, y1, y0.
            w.push(g2.0 .1.to_string());
            w.push(g2.0 .0.to_string());
            w.push(g2.1 .1.to_string());
            w.push(g2.1 .0.to_string());
        }
        w.push(vk::CONSTANT_G1.0.to_string());
        w.push(vk::CONSTANT_G1.1.to_string());
        for p in vk::PUB_G1.iter() {
            w.push(p.0.to_string());
            w.push(p.1.to_string());
        }
        VkWords { words: w }
    }
}

/// keccak256("dregg-groth16-vk/1" || u32be(25) || u32be(26) || 76 words BE32).
fn vk_digest_of(k: &VkWords) -> [u8; 32] {
    let mut pre: Vec<u8> = Vec::with_capacity(2458);
    pre.extend_from_slice(b"dregg-groth16-vk/1");
    pre.extend_from_slice(&25u32.to_be_bytes());
    pre.extend_from_slice(&26u32.to_be_bytes());
    for w in &k.words {
        pre.extend_from_slice(&be32(w));
    }
    assert_eq!(pre.len(), 2458, "the pinned preimage length");
    keccak(&pre)
}

/// A decimal field element as 32 big-endian bytes.
fn be32(dec: &str) -> [u8; 32] {
    let mut acc = [0u8; 32];
    for ch in dec.bytes() {
        let d = (ch - b'0') as u16;
        // acc = acc * 10 + d, big-endian, wrapping is impossible for Fq < 2^254.
        let mut carry = d;
        for byte in acc.iter_mut().rev() {
            let v = (*byte as u16) * 10 + carry;
            *byte = (v & 0xff) as u8;
            carry = v >> 8;
        }
        assert_eq!(carry, 0, "field element overflowed 32 bytes");
    }
    acc
}

/// Increment a decimal string by one (a genuinely different key word).
fn bump_decimal(dec: &str) -> String {
    let mut digits: Vec<u8> = dec.bytes().map(|b| b - b'0').collect();
    let mut i = digits.len();
    loop {
        if i == 0 {
            digits.insert(0, 1);
            break;
        }
        i -= 1;
        if digits[i] == 9 {
            digits[i] = 0;
        } else {
            digits[i] += 1;
            break;
        }
    }
    digits.into_iter().map(|d| (d + b'0') as char).collect()
}

fn keccak(bytes: &[u8]) -> [u8; 32] {
    use sha3::{Digest, Keccak256};
    let d = Keccak256::digest(bytes);
    let mut out = [0u8; 32];
    out.copy_from_slice(&d);
    out
}
