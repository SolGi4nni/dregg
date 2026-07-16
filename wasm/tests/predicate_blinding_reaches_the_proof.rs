//! **The wasm predicate surface, driven as REAL wasm** — the gate on the bug this surface actually
//! had.
//!
//! ## What went wrong here, and why nothing caught it
//!
//! `wasm/src/lib.rs`'s `generate_predicate_proof` did not compile against the circuit for some time
//! (`E0308: expected FactBinding, found BabyBear`, every predicate arm). It was invisible TWICE
//! over:
//!
//!   1. `wasm` sits in the root workspace `exclude` list (root `Cargo.toml`), so
//!      `cargo check --workspace` never looks at it; and
//!   2. the only workflows that build it (`pages.yml`, `publish-sdk-ts.yml`) are
//!      `workflow_dispatch`-only / tag-triggered — `ci.yml` (push + PR) has no `wasm32` step at all.
//!
//! So an API change lands, CI goes green, and this surface rots until someone hand-dispatches a
//! Pages deploy. These tests are only a gate if something RUNS them (see HORIZONLOG: the proposed
//! `wasm (standalone workspace)` CI job, mirroring the existing `solana-lock` one).
//!
//! ## The bug the fix nearly shipped
//!
//! The in-flight repair pointed all five predicate arms at an UNBLINDED fact binding while
//! `getrandom` still drew a blinding factor — which was computed into a commitment and then
//! DISCARDED. That compiles, proves, and verifies. It also silently unblinds every predicate type on
//! this surface: the public `fact_commitment` becomes a deterministic function of the attribute, so
//! any two verifiers who see two showings can correlate them. A privacy regression that no
//! type-checker and no green test would ever mention.
//!
//! [`two_showings_of_the_same_attribute_are_unlinkable`] is the falsifier for exactly that: it drives
//! the REAL `#[wasm_bindgen]` entry point twice over identical arguments and demands the emitted
//! commitments DIFFER. Discard the blinding again and it goes red.

use dregg_wasm::generate_predicate_proof;
use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

// A BROWSER test, like `card_fires_a_verified_turn.rs`: this crate's `perf_now()` reads
// `web_sys::window()`, and the bundle carries static DOM accessors, so a bare node runner dies at
// module init (`ReferenceError: document is not defined`) before any assertion runs.
//
//   wasm-pack test --headless --chrome wasm --test predicate_blinding_reaches_the_proof
wasm_bindgen_test_configure!(run_in_browser);

/// Pull `fact_commitment` out of the surface's returned JSON result.
///
/// This reads the commitment the PROOF binds (`generate_predicate_proof` reports
/// `pis[PI_FACT_COMMITMENT]`, not a pre-computed local), so what this test observes is what a
/// verifier actually receives — the only thing unlinkability is a property of.
fn fact_commitment_of(v: &JsValue) -> u64 {
    let json = js_sys::JSON::stringify(v).expect("result serializes");
    let s: String = json.into();
    let parsed: serde_json::Value = serde_json::from_str(&s).expect("result is JSON");
    parsed["fact_commitment"]
        .as_u64()
        .unwrap_or_else(|| panic!("result must carry a fact_commitment: {parsed}"))
}

/// NON-VACUITY — the surface proves and self-verifies an honest `100 >= 40`.
#[wasm_bindgen_test]
fn honest_predicate_proof_verifies_on_the_wasm_surface() {
    let out = generate_predicate_proof("gte", 100, 40, "age", 0x57A7E).expect("100 >= 40 proves");
    let json = js_sys::JSON::stringify(&out).expect("serializes");
    let s: String = json.into();
    let parsed: serde_json::Value = serde_json::from_str(&s).expect("JSON");
    assert_eq!(
        parsed["verified"], true,
        "the wasm surface must self-verify an honest predicate proof: {parsed}"
    );
}

/// A FALSE comparison is REFUSED by the descriptor (the range tooth), not smuggled through.
#[wasm_bindgen_test]
fn false_predicate_is_refused_on_the_wasm_surface() {
    assert!(
        generate_predicate_proof("gte", 5, 40, "age", 0x57A7E).is_err(),
        "5 >= 40 is FALSE and must be refused — the descriptor's range tooth is the judge"
    );
}

/// **THE FALSIFIER — the blinding factor reaches the PROOF, not the bin.**
///
/// Two showings with IDENTICAL arguments. Everything a verifier sees is the same except the
/// commitment, which must differ because each call draws a fresh blinding factor that leg 2 of the
/// weld constrains (`fact_commitment = hash_4_to_1([fact_hash, state_root, blinding, 0])`).
///
/// If the blinding is ever computed-and-discarded again, both calls emit the SAME commitment and this
/// test goes red — which is the whole point of it existing.
#[wasm_bindgen_test]
fn two_showings_of_the_same_attribute_are_unlinkable() {
    let s1 = generate_predicate_proof("gte", 100, 40, "age", 0x57A7E).expect("showing 1");
    let s2 = generate_predicate_proof("gte", 100, 40, "age", 0x57A7E).expect("showing 2");

    assert_ne!(
        fact_commitment_of(&s1),
        fact_commitment_of(&s2),
        "UNLINKABILITY LOST on the wasm surface — two showings of the SAME attribute emitted the \
         SAME public fact_commitment. The blinding factor is being drawn and then discarded, so \
         every presentation of this credential is correlatable by colluding verifiers."
    );
}

/// Unlinkability must hold for EVERY predicate type this surface dispatches, not just `>=`.
///
/// The near-miss fix unblinded all five arms at once by pointing them at a shared unblinded binding,
/// so a gate that only covered `gte` would have missed four of them. A surface where one operator is
/// linkable and its peers are not is worse than uniformly linkable: the odd one out identifies its
/// users.
#[wasm_bindgen_test]
fn every_predicate_type_is_unlinkable() {
    // (op, value, threshold) — each statement TRUE, so each genuinely proves.
    for (op, v, t) in [
        ("gte", 100u32, 40u32),
        ("lte", 40, 100),
        ("gt", 100, 40),
        ("lt", 40, 100),
        ("neq", 100, 40),
    ] {
        let s1 = generate_predicate_proof(op, v, t, "age", 0x57A7E)
            .unwrap_or_else(|_| panic!("{op}: showing 1 must prove"));
        let s2 = generate_predicate_proof(op, v, t, "age", 0x57A7E)
            .unwrap_or_else(|_| panic!("{op}: showing 2 must prove"));
        assert_ne!(
            fact_commitment_of(&s1),
            fact_commitment_of(&s2),
            "UNLINKABILITY LOST for `{op}` — two showings emitted the same fact_commitment. \
             Every predicate type on this surface must be blinded, not just `gte`."
        );
    }
}
