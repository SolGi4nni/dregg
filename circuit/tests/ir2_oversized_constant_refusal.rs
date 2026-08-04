//! # An AIR coefficient that does not fit a felt is REFUSED, and the escape is a counted list.
//!
//! Until 2026-08-03 `JsonCursor::parse_int_field` silently folded any gate coefficient wider than
//! `i64` down to its residue mod BabyBear. That fold is exactly what let a Pasta `9×30` multiply
//! gate — whose body reaches `2^508` — be proved as though its integer semantics fitted the field.
//! `pasta_field_felt_soundness.rs::the_deployed_prover_accepts_a_nonzero_integer_body` exhibits
//! the consequence: a witness with a nonzero 285-bit integer body that the deployed prover proves
//! and the deployed verifier accepts.
//!
//! The strict default is now the refusal. The named escape
//! `parse_vm_descriptor2_unsound_oversized` still exists, because the nine `pasta-rcb-*`
//! descriptors and five `pasta-rcb-sg-derive-*` artifacts have not been re-emitted on the sound
//! encoding — and the point of this file is that the list is **enumerated, counted, and can only
//! shrink**, instead of being a Horner loop nobody reads.
//!
//! ⚠ The census the old docblock carried said "14 checked-in descriptors" and named only Pasta
//! ones. Measured here: **15**, and the fifteenth is not Pasta —
//! `dregg-shielded-wide-value-link-conserve-v1.json` carries a 49-bit coefficient. A silent fold
//! is silent about everything, including its own extent.

use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2, parse_vm_descriptor2_unsound_oversized};

/// Every checked-in descriptor whose gate coefficients exceed `p_babybear`. **This list may only
/// shrink.** Each entry is a descriptor whose gate bodies cannot round-trip a felt, which means
/// no ℤ-level forcing lemma about it constrains any proof object over it.
const OVERSIZED_CONSTANT_DESCRIPTORS: &[(&str, &str)] = &[
    // 495 bits — the Pasta 9×30 cone. Replaced for the multiply by `dregg-pasta-fpmul-sound::v1`;
    // the RCB / MSM / derive layers above it have not been re-emitted.
    (
        "pasta-rcb-windowed",
        include_str!("../descriptors/by-name/pasta-rcb-windowed.json"),
    ),
    (
        "pasta-rcb-sg-slice-0-of-4",
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-0-of-4.json"),
    ),
    (
        "pasta-rcb-sg-slice-1-of-4",
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-1-of-4.json"),
    ),
    (
        "pasta-rcb-sg-slice-2-of-4",
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-2-of-4.json"),
    ),
    (
        "pasta-rcb-sg-slice-3-of-4",
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-3-of-4.json"),
    ),
    (
        "pasta-rcb-sg-slice-0-of-4-w8",
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-0-of-4-w8.json"),
    ),
    (
        "pasta-rcb-sg-slice-1-of-4-w8",
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-1-of-4-w8.json"),
    ),
    (
        "pasta-rcb-sg-slice-2-of-4-w8",
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-2-of-4-w8.json"),
    ),
    (
        "pasta-rcb-sg-slice-3-of-4-w8",
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-3-of-4-w8.json"),
    ),
    // 49 bits — NOT Pasta, and NOT in the old docblock's census of 14.
    (
        "dregg-shielded-wide-value-link-conserve-v1",
        include_str!("../descriptors/by-name/dregg-shielded-wide-value-link-conserve-v1.json"),
    ),
];

/// The five `metatheory/emitted/mina-opening/pasta-rcb-sg-derive-*.json` artifacts are the rest of
/// the 15; they live outside `circuit/descriptors` and are `include_str!`ed by
/// `pasta_derive_prove.rs` / `pasta_bound_sg_prove.rs`, which already route through the escape.
const OVERSIZED_OUT_OF_TREE: usize = 5;

/// ⚑ **THE RATCHET.** `10 + 5 = 15`. When the RCB / MSM cone is re-emitted on the felt-sized
/// encoding these entries come out, the count drops, and this assertion is what forces the number
/// to be restated rather than drifting.
#[test]
fn ir2_oversized_constant_escape_is_a_shrinking_list() {
    assert_eq!(
        OVERSIZED_CONSTANT_DESCRIPTORS.len() + OVERSIZED_OUT_OF_TREE,
        15,
        "the oversized-constant escape list changed — restate it, do not widen it"
    );
}

/// ⚑ **THE REFUSAL BITES.** Every listed descriptor is REFUSED by the strict default and ACCEPTED
/// by the named escape. A refusal that nothing triggers is decoration; this is the pre-image.
#[test]
fn strict_parse_refuses_every_oversized_descriptor() {
    for (name, json) in OVERSIZED_CONSTANT_DESCRIPTORS {
        let strict = parse_vm_descriptor2(json);
        assert!(
            strict.is_err(),
            "{name}: the strict parser must REFUSE a coefficient wider than a felt"
        );
        let msg = strict.unwrap_err();
        assert!(
            msg.contains("does not fit a BabyBear felt"),
            "{name}: the refusal must name the reason, got {msg}"
        );
        parse_vm_descriptor2_unsound_oversized(json)
            .unwrap_or_else(|e| panic!("{name}: the named escape must still parse it: {e}"));
    }
}

/// ⚑ **AND THE SOUND ENCODING NEEDS NO ESCAPE.** `dregg-pasta-fpmul-sound::v1` — the felt-sized
/// Pasta multiply (`Dregg2.Circuit.Emit.PastaFieldSound`) — parses through the STRICT default. Its
/// largest coefficient is `2^23`. That is the whole difference between a gate whose ℤ semantics
/// survive the prover's field and one whose do not.
#[test]
fn the_sound_pasta_multiply_parses_strict() {
    let d = parse_vm_descriptor2(include_str!(
        "../descriptors/by-name/pasta-fpmul-sound.json"
    ))
    .expect("the sound Pasta multiply carries no oversized constant");
    assert_eq!(d.name, "dregg-pasta-fpmul-sound::v1");
    let d = parse_vm_descriptor2(include_str!(
        "../descriptors/by-name/pasta-fqmul-sound.json"
    ))
    .expect("…and neither does the Fq one");
    assert_eq!(d.name, "dregg-pasta-fqmul-sound::v1");
}
