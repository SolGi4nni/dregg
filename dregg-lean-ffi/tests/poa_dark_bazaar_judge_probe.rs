//! Native linked probe for the Lean-owned Dark Bazaar v1 evaluator.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::poa_dark_bazaar_ffi::{
    judge_poa_dark_bazaar, poa_dark_bazaar_judge_available, PoaDarkBazaarVerdict,
};

const INPUT: &str = include_str!("fixtures/poa-dark-bazaar-input-v1.json");
const OUTPUT: &str = include_str!("fixtures/poa-dark-bazaar-output-v1.json");

fn fixture(bytes: &'static str) -> &'static str {
    bytes
        .strip_suffix('\n')
        .expect("fixture file must have exactly one trailing newline")
}

#[test]
fn frozen_lean_settlement_is_linked_and_exact() {
    assert!(
        poa_dark_bazaar_judge_available(),
        "Dark Bazaar Lean export is absent or initialization failed"
    );
    assert_eq!(
        judge_poa_dark_bazaar(fixture(INPUT)).expect("linked evaluator must be callable"),
        PoaDarkBazaarVerdict::Accepted(fixture(OUTPUT).to_owned())
    );
}

#[test]
fn trailing_byte_is_a_semantic_refusal() {
    let mut input = fixture(INPUT).to_owned();
    input.push('\n');
    assert_eq!(
        judge_poa_dark_bazaar(&input).expect("linked evaluator must be callable"),
        PoaDarkBazaarVerdict::Rejected
    );
}

#[test]
fn plaintext_with_forged_clearing_is_not_authorization() {
    let forged = fixture(INPUT).replacen(
        "\"output\":{\"bucket\":1,\"volume\":13}",
        "\"output\":{\"bucket\":2,\"volume\":13}",
        1,
    );
    assert_eq!(
        judge_poa_dark_bazaar(&forged).expect("linked evaluator must be callable"),
        PoaDarkBazaarVerdict::Rejected
    );
}
