//! ⚑ THE CROSS-SURFACE IDENTITY TOOTH — the same 24 words name the same person in the
//! browser as they do in the CLI, or this goes red.
//!
//! ## What broke, and why a test shaped like this exists
//!
//! `wasm/src/lib.rs::derive_keypair_from_mnemonic` used to carry its OWN derivation. Its doc
//! said "the same BLAKE3-based derivation as `dregg-sdk`'s `mnemonic_to_seed` +
//! `derive_keypair`". It was not: it fed `blake3::hash(mnemonic.as_bytes())` to the KDF in
//! place of the BIP39-validated **entropy**, and it never checked the checksum. Same words,
//! different key — `900be4c3…` in the browser where every other surface said `dd2219e9…`.
//!
//! That mattered more than a wrong constant usually does, because the browser extension is
//! the ONLY surface that reaches `Attribution::Signed` + `Custody::UserHeld`. A page can only
//! ever produce `Attribution::Asserted`. So a person whose extension derived key X while the
//! CLI and `dreggnet-web`'s `/identity` derived key Y had their **signed** play filed under a
//! different identity than their **asserted** play — on a product that ships "enter your 24
//! words anywhere and get your games back".
//!
//! ## Why the previous tooth did not catch it
//!
//! `extension/test/derivation.test.mjs` pins `blake3::derive_key("dregg/0", 00..3f)` → the
//! Ed25519 public key `335840a9…`, cross-checked against `sdk/src/profiles.rs` and
//! `cli/src/commands/id.rs`. That is the SECOND half of the pipeline, starting from an
//! arbitrary 64-byte seed. The split lived in the FIRST half — phrase → 64-byte seed — which
//! nothing tested from the words in. A golden vector that starts downstream of the wound is
//! green while the wound is open. This test starts at the 24 words.
//!
//! ## What is asserted
//!
//! 1. **Agreement, not just stability.** The wasm's [`dregg_wasm::derive_identity_keypair`]
//!    equals the SDK pipeline (`mnemonic_to_seed` + `derive_keypair`) AND
//!    `AgentCipherclerk::from_mnemonic` — the entry the `dregg` CLI actually uses — for the
//!    same words. Three call paths, one key.
//! 2. **A pinned value, so a SHARED change is still caught.** Equality alone would stay green
//!    if someone changed `dregg_sdk::mnemonic` itself: both sides move together and every
//!    already-issued phrase silently renames its owner. The hex constants below were computed
//!    by an INDEPENDENT implementation (a from-scratch single-chunk BLAKE3 in JS +
//!    `node:crypto` Ed25519, grounded first against the official BLAKE3 vectors and against
//!    this repo's own `335840a9…` golden), not read off a Rust run.
//! 3. **The old value is a tripwire.** `assert_ne!` against `900be4c3…` — the pre-fix key for
//!    the same phrase — so reintroducing the phrase-hash shortcut fails loudly rather than
//!    quietly re-splitting the fleet.
//! 4. **Refusal, not silent renaming.** One mistyped word, a word outside the list, and a
//!    wrong word count are all REFUSED. A checksum failure is the difference between "check
//!    that word" and "here is a stranger's empty history".
//! 5. **The extension's second wordlist is the same wordlist.** `extension/bip39_english.txt`
//!    is shipped in the extension package and is a SEPARATE copy of the 2048 words. Order IS
//!    the encoding (each word is an 11-bit index), so a reordered copy is a silent identity
//!    split with no error anywhere. Pinned word-for-word against `dregg_sdk::wordlist`.
//!
//! Run: `cargo test --manifest-path wasm/Cargo.toml --test mnemonic_derivation_matches_the_sdk`
//! (the `wasm/` crate is a STANDALONE cargo workspace — `-p dregg-wasm` from the repo root
//! does not see it). This runs on the HOST target; the same claim is asserted through the real
//! `#[wasm_bindgen]` export under `wasm-pack test` by
//! `lib.rs::audit_tests::adversarial_derive_keypair_agrees_with_the_sdk_and_refuses_a_non_phrase`.

use dregg_sdk::mnemonic::{MnemonicError, derive_keypair, mnemonic_to_seed, validate_mnemonic};
use dregg_wasm::{DERIVATION_PATH, derive_identity_keypair};

/// The canonical all-zero-entropy 24-word BIP39 phrase: 23 × `abandon` + the checksum word
/// `art` (checksum byte `0x66`). The same fixture
/// `extension/tests/passkey-sign/run.mjs` drives the shipped bundle with.
const PHRASE_ZERO: &str = "abandon abandon abandon abandon abandon abandon abandon abandon \
                           abandon abandon abandon abandon abandon abandon abandon abandon \
                           abandon abandon abandon abandon abandon abandon abandon art";

/// The dregg identity `PHRASE_ZERO` names at `dregg/0`, no BIP39 passphrase.
const PUBKEY_ZERO: &str = "dd2219e93ac26578be7d4677fa2d6de7ac0d78f196438f445ebbae7fcfd7ef95";

/// ⚑ What the PRE-FIX wasm produced for `PHRASE_ZERO` — `blake3::hash(phrase_bytes)` used as
/// the entropy. Present only so it can never be the answer again.
const PUBKEY_ZERO_PRE_FIX: &str =
    "900be4c39477e441a3f28635bb668224df12c7a242040dfe312ef7c08fa94bdd";

/// A second phrase, entropy `00 01 02 … 1f` — a different word at nearly every position, so a
/// bug that happens to be right on the degenerate all-`abandon` case has nowhere to hide.
const PHRASE_INCREMENTING: &str = "abandon amount liar amount expire adjust cage candy arch \
                                   gather drum bullet absurd math era live bid rhythm alien \
                                   crouch range attend journey unaware";

const PUBKEY_INCREMENTING: &str =
    "8589c9a7f6660cbd75111f918156aa29918494925f6e93108cd4e751cefa133c";

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The wasm crate's derivation, the SDK's raw pipeline, and the cipherclerk the CLI uses all
/// yield the SAME key — and it is the pinned one.
#[test]
fn the_wasm_derivation_is_the_sdk_derivation() {
    for (phrase, expected) in [
        (PHRASE_ZERO, PUBKEY_ZERO),
        (PHRASE_INCREMENTING, PUBKEY_INCREMENTING),
    ] {
        let (wasm_pubkey, wasm_secret) = derive_identity_keypair(phrase, "", DERIVATION_PATH)
            .expect("a checksum-valid phrase derives");

        // (a) The pinned value — computed off-Rust, so a shared change to
        //     `dregg_sdk::mnemonic` cannot move it silently.
        assert_eq!(
            hex(&wasm_pubkey),
            expected,
            "the browser's identity for a phrase moved; every already-written-down phrase \
             now names a different person"
        );

        // (b) The SDK's raw pipeline.
        let seed = mnemonic_to_seed(phrase, "").expect("valid phrase");
        let (sdk_pubkey, sdk_secret) = derive_keypair(&seed, DERIVATION_PATH);
        assert_eq!(wasm_pubkey, sdk_pubkey, "wasm public key != dregg_sdk's");
        assert_eq!(
            wasm_secret[..],
            sdk_secret[..],
            "wasm signing seed != dregg_sdk's (would sign as a different key)"
        );

        // (c) The entry the CLI uses (`dregg id import` → `AgentCipherclerk::from_mnemonic`),
        //     which is what makes a phrase claimed in a browser SIGN as this identity on
        //     `/offerings/{key}/session/{id}/act-signed`.
        let cclerk = dregg_sdk::AgentCipherclerk::from_mnemonic(phrase, "")
            .expect("the cipherclerk accepts a valid phrase");
        assert_eq!(
            hex(&cclerk.public_key().0),
            expected,
            "AgentCipherclerk::from_mnemonic disagrees with the wasm — the CLI and the \
             extension would be two different players"
        );

        // (d) The phrase-hash shortcut must never return.
        assert_ne!(
            hex(&wasm_pubkey),
            PUBKEY_ZERO_PRE_FIX,
            "the pre-fix blake3(phrase) entropy is back"
        );
    }
}

/// A BIP39 passphrase and a derivation path each change the identity — so neither may be
/// dropped on the floor. (`derive_keypair_from_mnemonic`'s third argument WAS dropped:
/// `extension/src/custody.ts` passed `DREGG_KEY_PATH` and wasm-bindgen discarded it.)
#[test]
fn the_passphrase_and_the_path_are_both_load_bearing() {
    let (base, _) = derive_identity_keypair(PHRASE_ZERO, "", DERIVATION_PATH).expect("valid");
    let (with_passphrase, _) =
        derive_identity_keypair(PHRASE_ZERO, "hunter2", DERIVATION_PATH).expect("valid");
    let (sub_agent, _) = derive_identity_keypair(PHRASE_ZERO, "", "dregg/1").expect("valid");

    assert_ne!(base, with_passphrase, "the BIP39 passphrase is ignored");
    assert_ne!(base, sub_agent, "the derivation path is ignored");
    assert_eq!(
        DERIVATION_PATH, "dregg/0",
        "the cross-surface path constant moved; cli/src/commands/id.rs and \
         dreggnet-web/src/seed_identity.rs pin the same string"
    );
}

/// ⚑ A phrase that is not a phrase is REFUSED. The pre-fix code accepted `word0 word1 …
/// word23` and happily derived a key from it, which is the same failure as accepting one
/// mistyped word: the person is handed a different, empty identity and told nothing.
#[test]
fn a_broken_phrase_is_refused_rather_than_renaming_the_player() {
    let mut words: Vec<&str> = PHRASE_ZERO.split(' ').collect();

    // One wrong (but real) word — the checksum's whole job.
    words[5] = "ability";
    assert!(
        matches!(
            derive_identity_keypair(&words.join(" "), "", DERIVATION_PATH),
            Err(MnemonicError::InvalidChecksum)
        ),
        "one mistyped word must fail the checksum"
    );

    // A word outside the 2048.
    words[5] = "xyzzyplugh";
    assert!(matches!(
        derive_identity_keypair(&words.join(" "), "", DERIVATION_PATH),
        Err(MnemonicError::UnknownWord(_))
    ));

    // The exact fixture the pre-fix tests used, which USED to derive a key.
    let nonsense = (0..24)
        .map(|i| format!("word{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    assert!(
        derive_identity_keypair(&nonsense, "", DERIVATION_PATH).is_err(),
        "24 arbitrary tokens must not derive an identity"
    );

    // Wrong counts, either side.
    assert!(matches!(
        derive_identity_keypair("one two three", "", DERIVATION_PATH),
        Err(MnemonicError::InvalidWordCount(3))
    ));
    assert!(derive_identity_keypair("", "", DERIVATION_PATH).is_err());

    // And the phrases we DO accept validate.
    assert!(validate_mnemonic(PHRASE_ZERO).is_ok());
    assert!(validate_mnemonic(PHRASE_INCREMENTING).is_ok());
}

/// ⚑ THE EXTENSION'S SECOND WORDLIST. `extension/bip39_english.txt` is shipped in the
/// extension package (`manifest.json` `web_accessible_resources`, `build.sh`'s `BASE_FILES`)
/// as a copy of the same 2048 words `dregg_sdk::wordlist::WORDLIST` holds. Each word is an
/// 11-bit index, so **the order IS the encoding**: a single transposed pair would make some
/// phrases decode to different entropy on one surface than the other, with no error raised
/// anywhere. Two copies of an ordered list is exactly the shape that rots silently, so it is
/// pinned here word-for-word rather than trusted.
///
/// (No extension script READS it any more — `background.ts`'s TypeScript BIP39 encoder, its
/// only consumer, was retired in favour of the wasm's `generate_mnemonic` /
/// `validate_mnemonic` exports. It is still packaged, so this stays a live pin until the file
/// is dropped from `manifest.json` + `build.sh`, which is a packaging decision.)
#[test]
fn the_extensions_shipped_wordlist_is_the_sdks_wordlist() {
    let shipped = include_str!("../../extension/bip39_english.txt");
    let words: Vec<&str> = shipped.split_whitespace().collect();

    assert_eq!(
        words.len(),
        dregg_sdk::wordlist::WORDLIST.len(),
        "extension/bip39_english.txt does not have 2048 words"
    );
    for (index, (shipped_word, sdk_word)) in words
        .iter()
        .zip(dregg_sdk::wordlist::WORDLIST.iter())
        .enumerate()
    {
        assert_eq!(
            shipped_word, sdk_word,
            "extension/bip39_english.txt diverges from dregg_sdk::wordlist at index {index} \
             ({shipped_word:?} vs {sdk_word:?}) — every phrase touching this index decodes to \
             different entropy in the extension than in the SDK"
        );
    }
}
