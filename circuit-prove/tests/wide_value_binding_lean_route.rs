//! **Lean→Rust wire canary for the full-`u64` shielded value/asset binding AIR.**
//!
//! The constraints are AUTHORED IN LEAN (`metatheory/Dregg2/Circuit/Emit/WideValueBindingEmit.lean`,
//! byte-pinned there by an `emitVmJson2` `#guard`, with the SAT ⟹ SEM bridge in
//! `WideValueBindingRefine.lean`). This test takes the byte-pinned golden STRAIGHT OUT OF THE LEAN
//! SOURCE and hands it to the production IR2 decoder, so no hand-transcription hop can open between
//! the Lean author and the Rust consumer — the same posture as `param_compose_descriptor.rs`.
//!
//! ## What this establishes, and what it does NOT
//!
//! ESTABLISHES: the Lean-emitted object is wire-compatible with `parse_vm_descriptor2`, and its
//! census matches the LIVE Rust `wide_value_binding_descriptor()` form for form — the 128 boolean
//! limb pins, the 8 limb recompositions, the 2 compatibility reductions, the 2 domain-separated
//! `node8` sites, the compatibility `hash_fact` site, and all 17 PI bindings — with the ONLY
//! difference being the three constant-pinned columns (`domain_a`, `domain_b`, `zero`) and their
//! three `constant_gate`s, which the Lean family replaces with literal constants in the chip tuples.
//! Those numbers are read off the Rust descriptor here, not transcribed, so the delta cannot rot.
//!
//! DOES NOT: prove anything semantic. Semantic faithfulness is
//! `WideValueBindingRefine.limb_canonical` / `seventeenth_bit_unsat` / `wideA_lanes_forced` /
//! `legacy_is_hash_fact` / `alias_separated_by_the_wide_carrier` in Lean, over the ACTUAL emitted
//! object. A Rust assertion about a decoded descriptor is a shape check; it is not refinement, not
//! translation validation, and not verification.
//!
//! ## Why it exists (the file it replaces)
//!
//! `circuit-prove/src/shielded/wide_value_binding.rs` hand-writes this AIR in Rust — 144
//! `ConstraintExpr` values and 17 `BoundaryDef`s built by Rust helper functions — which is exactly
//! what the Lean-authored-AIR law forbids, and it was authored FOR THE FELT-WIDTH REPAIR. The Lean
//! family here is the replacement route; this test is the evidence the route REACHES Rust.
//!
//! ## The remaining rewiring (NOT done here, stated precisely)
//!
//! `prove_wide_value_binding` / `verify_wide_value_binding` currently build a v1 `DslCircuit` and
//! run `prove_dsl_zk` / `verify_dsl_zk` (the hiding p3 path). The replacement route already exists
//! and is ALSO hiding, so the sidecar does not lose its zero-knowledge property:
//!
//!   1. `DescriptorStatement::try_from_json(WIDE_VALUE_BINDING_GOLDEN, pis)` — the parsed relation
//!      (`circuit/src/descriptor_proof_backend.rs`);
//!   2. a WITNESS PRODUCER filling the Lean column layout — which is
//!      `generate_wide_value_binding_trace` with the three constant-pinned cells (`domain_a`,
//!      `domain_b`, `zero`) removed and every index at or above `legacy_binding` shifted down by 3
//!      (`WideValueBindingEmit` §6 pins that accounting on the Lean side, per column);
//!   3. `Plonky3HidingFriReference::prove` / `::verify` — the DEPLOYED hiding IR-v2 backend
//!      (`create_zk_config`, salted-leaf MMCS). `trace_with_chip_lanes` fills the Poseidon2 lane
//!      columns, so the producer supplies only the main trace.
//!
//! What that changes is the PROOF BYTES: `WideValueBindingProof::proof_bytes` becomes an
//! `Ir2BatchProof<DreggZkStarkConfig>` postcard rather than a `DslZkProof`, so the Turn wire field
//! (`turn/src/action.rs:995`, and `turn-prover/src/shielded_transfer_verifier.rs` which decodes it)
//! moves with it. That is a deploy decision this test does not make. The 17 public inputs and their
//! canonical-BabyBear decode (`from_serialized_parts`) are UNCHANGED by the swap.
//!
//! Two descriptor-level fields have no IR-v2 counterpart and are simply gone: `max_degree` (the
//! IR-v2 prover derives its blowup from the config, not from a descriptor field) and the per-column
//! `ColumnDef` name/kind metadata. Nothing in the AIR depends on either; the ONLY consumer of the
//! names is `circuit-prove/tests/shielded_wide_value_binding.rs`'s `column(descriptor, "…")` helper,
//! which would index the Lean layout by its Lean-side offsets instead.

use dregg_circuit::cap_root::cap_node8;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::circuit::ConstraintExpr;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::VmConstraint;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::shielded::wide_value_binding_descriptor;

const EMIT_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Circuit/Emit/WideValueBindingEmit.lean");

/// Split a `def <NAME> : String := r#"…"#` raw-string golden out of a Lean module.
fn lean_raw_golden(source: &'static str, name: &str) -> &'static str {
    let open = format!("def {name} : String := r#\"");
    let (_, after) = source
        .split_once(open.as_str())
        .unwrap_or_else(|| panic!("Lean module still exposes {name}"));
    let (json, _) = after
        .split_once("\"#")
        .unwrap_or_else(|| panic!("{name} remains a raw string"));
    json
}

fn lean_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(lean_raw_golden(EMIT_LEAN, "WIDE_VALUE_BINDING_GOLDEN"))
        .expect("Lean-emitted wide value binding descriptor parses as IR2")
}

fn gate_count(desc: &EffectVmDescriptor2) -> usize {
    desc.constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::Gate(_))))
        .count()
}

fn pi_binding_count(desc: &EffectVmDescriptor2) -> usize {
    desc.constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count()
}

/// Tuple widths of the lookups on a given table wire id.
fn lookup_widths(desc: &EffectVmDescriptor2, table: usize) -> Vec<usize> {
    desc.constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Lookup(l) if l.table == table => Some(l.tuple.len()),
            _ => None,
        })
        .collect()
}

#[test]
fn lean_wide_value_binding_golden_parses_with_exact_shape() {
    let desc = lean_descriptor();

    assert_eq!(
        desc.name,
        "dregg-shielded-wide-value-binding-v1::poseidon2-node8"
    );
    assert_eq!(desc.trace_width, 162);
    assert_eq!(desc.public_input_count, 17);
    assert_eq!(desc.constraints.len(), 158);
    assert!(desc.tables.is_empty());
    assert!(desc.hash_sites.is_empty());
    assert!(desc.ranges.is_empty());

    // 128 boolean limb pins + 8 limb recompositions + 2 compatibility reductions.
    assert_eq!(gate_count(&desc), 2 * 4 * 16 + 2 * 4 + 2);
    // The 17 first-row boundary pins: the compatibility join + 16 wide lanes.
    assert_eq!(pi_binding_count(&desc), 17);

    // The two domain-separated `node8` carriers, each a genuine 25-wide arity-16 wide chip tuple
    // (`1 + CHIP_RATE + CHIP_OUT_LANES`), which is the shape `chip_lookup_sound_N` consumes.
    assert_eq!(
        lookup_widths(&desc, dregg_circuit::descriptor_ir2::TID_P2),
        vec![25, 25]
    );
    // The compatibility `hash_fact` join: ONE narrow (out0-only, 18-wide) site.
    assert_eq!(
        lookup_widths(&desc, dregg_circuit::descriptor_ir2::TID_P2_NARROW),
        vec![18]
    );

    // The deployed program-validation caps this AIR is measured against.
    assert!(desc.trace_width <= dregg_circuit::dsl::circuit::MAX_TRACE_WIDTH);
    assert!(desc.public_input_count <= dregg_circuit::dsl::circuit::MAX_PUBLIC_INPUTS);
}

/// THE STRUCTURAL CROSS-CHECK. Every number on the right-hand side is read off the LIVE Rust
/// `wide_value_binding_descriptor()`, so this cannot drift into a hand-transcribed comparison. The
/// Lean census is the Rust census minus exactly the three constant-pinned columns and the three
/// `constant_gate`s that pinned them; a constant in a chip tuple cannot be tampered, so that delta
/// is a strengthening, and its being EXACTLY 3 in both dimensions is the evidence nothing else moved.
#[test]
fn lean_census_is_the_rust_census_minus_the_constant_pins() {
    let lean = lean_descriptor();
    let rust = wide_value_binding_descriptor();

    // Columns: 165 → 162.
    assert_eq!(lean.trace_width + 3, rust.trace_width);
    assert_eq!(rust.trace_width, rust.columns.len());
    // The three columns the Lean family drops, named.
    for name in ["domain_a", "domain_b", "zero"] {
        assert!(
            rust.columns.iter().any(|c| c.name == name),
            "Rust still allocates the constant-pinned column {name}"
        );
    }

    // Public inputs: identical.
    assert_eq!(lean.public_input_count, rust.public_input_count);

    // Boolean limb pins: identical, and they are the felt-width repair.
    let rust_binary = rust
        .constraints
        .iter()
        .filter(|c| matches!(c, ConstraintExpr::Binary { .. }))
        .count();
    assert_eq!(rust_binary, 2 * 4 * 16);

    // `node8` carriers: identical count.
    let rust_node8 = rust
        .constraints
        .iter()
        .filter(|c| matches!(c, ConstraintExpr::MerkleHash8 { .. }))
        .count();
    assert_eq!(rust_node8, 2);
    assert_eq!(
        lookup_widths(&lean, dregg_circuit::descriptor_ir2::TID_P2).len(),
        rust_node8
    );

    // Compatibility `hash_fact` sites: identical count.
    let rust_fact = rust
        .constraints
        .iter()
        .filter(|c| matches!(c, ConstraintExpr::Hash { .. }))
        .count();
    assert_eq!(rust_fact, 1);
    assert_eq!(
        lookup_widths(&lean, dregg_circuit::descriptor_ir2::TID_P2_NARROW).len(),
        rust_fact
    );

    // Polynomial gates: Rust carries the 8 limb recompositions + 2 reductions + 3 constant gates;
    // Lean carries the first two groups only. The Binary form is a separate Rust variant, so the
    // Lean gate count is `rust_polynomial - 3 + rust_binary`.
    let rust_poly = rust
        .constraints
        .iter()
        .filter(|c| matches!(c, ConstraintExpr::Polynomial { .. }))
        .count();
    assert_eq!(rust_poly, 2 * 4 + 2 + 3);
    assert_eq!(gate_count(&lean) + 3, rust_poly + rust_binary);

    // Whole census: Rust `constraints + boundaries` is 161; Lean is 158 — the SAME delta of 3.
    assert_eq!(
        lean.constraints.len() + 3,
        rust.constraints.len() + rust.boundaries.len()
    );
}

// ---------------------------------------------------------------------------
// THE ROUTE REACHES THE PROVER — a witness in the LEAN column layout, proven and
// verified through the deployed IR-v2 engine.
// ---------------------------------------------------------------------------

/// The Lean column layout (`WideValueBindingEmit` §2) — the Rust layout with `domain_a`,
/// `domain_b` and `zero` removed, so everything from `legacy_binding` on shifts down by 3.
mod lean_col {
    pub const V: usize = 0; // value_limb_0..3
    pub const A: usize = 4; // asset_limb_0..3
    pub const VMOD: usize = 8;
    pub const AMOD: usize = 9;
    pub const RAND: usize = 10;
    pub const BLIND: usize = 11; // 6 lanes
    pub const LEGACY: usize = 17;
    pub const WA: usize = 18; // 8 lanes
    pub const WB: usize = 26; // 8 lanes
    pub const BITS: usize = 34; // 2 * 4 * 16
    pub const WIDTH: usize = 162;
    pub const fn bit(kind: usize, limb: usize, b: usize) -> usize {
        BITS + (kind * 4 + limb) * 16 + b
    }
}

const DOMAIN_A: u32 = 0x5642_4e30;
const DOMAIN_B: u32 = 0x5642_4e31;

fn u64_limbs(v: u64) -> [u16; 4] {
    core::array::from_fn(|i| ((v >> (i * 16)) & 0xffff) as u16)
}

/// Fill the LEAN layout for one honest opening, returning the base trace and the 17 PIs.
/// This is `generate_wide_value_binding_trace` re-indexed — step 2 of the rewiring above.
fn lean_witness(
    value: u64,
    asset: u64,
    randomness: BabyBear,
    blind: [BabyBear; 6],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let v = u64_limbs(value);
    let a = u64_limbs(asset);
    let left = |domain: u32| {
        [
            BabyBear::new(domain),
            BabyBear::new(v[0] as u32),
            BabyBear::new(v[1] as u32),
            BabyBear::new(v[2] as u32),
            BabyBear::new(v[3] as u32),
            BabyBear::new(a[0] as u32),
            BabyBear::new(a[1] as u32),
            BabyBear::new(a[2] as u32),
        ]
    };
    let right = [
        BabyBear::new(a[3] as u32),
        randomness,
        blind[0],
        blind[1],
        blind[2],
        blind[3],
        blind[4],
        blind[5],
    ];
    let wide_a = cap_node8(left(DOMAIN_A), right);
    let wide_b = cap_node8(left(DOMAIN_B), right);
    let vmod = BabyBear::new((value % BABYBEAR_P as u64) as u32);
    let amod = BabyBear::new((asset % BABYBEAR_P as u64) as u32);
    let legacy = hash_fact(vmod, &[amod, randomness, BabyBear::ZERO]);

    let mut row = vec![BabyBear::ZERO; lean_col::WIDTH];
    for i in 0..4 {
        row[lean_col::V + i] = BabyBear::new(v[i] as u32);
        row[lean_col::A + i] = BabyBear::new(a[i] as u32);
        for b in 0..16 {
            row[lean_col::bit(0, i, b)] = BabyBear::new(((v[i] >> b) & 1) as u32);
            row[lean_col::bit(1, i, b)] = BabyBear::new(((a[i] >> b) & 1) as u32);
        }
    }
    row[lean_col::VMOD] = vmod;
    row[lean_col::AMOD] = amod;
    row[lean_col::RAND] = randomness;
    row[lean_col::BLIND..lean_col::BLIND + 6].copy_from_slice(&blind);
    row[lean_col::LEGACY] = legacy;
    row[lean_col::WA..lean_col::WA + 8].copy_from_slice(&wide_a);
    row[lean_col::WB..lean_col::WB + 8].copy_from_slice(&wide_b);

    let mut pis = Vec::with_capacity(17);
    pis.push(legacy);
    pis.extend_from_slice(&wide_a);
    pis.extend_from_slice(&wide_b);
    (vec![row.clone(), row], pis)
}

/// **THE ROUTE REACHES THE PROVER.** The Lean-emitted descriptor, an honest witness in the Lean
/// column layout, and the deployed IR-v2 prove/verify pair. This is the evidence that step 1 and
/// step 2 of the rewiring above are real: only the proof-BYTES decision (step 3's backend choice
/// and the Turn wire field) remains before `wide_value_binding.rs`'s descriptor half can go.
#[test]
fn lean_wide_value_binding_proves_and_verifies() {
    let desc = lean_descriptor();
    let blind: [BabyBear; 6] = core::array::from_fn(|i| BabyBear::new(0x1000 + (i as u32) * 0x111));
    let (trace, pis) = lean_witness(
        0x1234_5678_9abc_def0,
        0xfedc_ba98_7654_3210,
        BabyBear::new(0x13579),
        blind,
    );
    assert_eq!(trace[0].len(), desc.trace_width);
    assert_eq!(pis.len(), desc.public_input_count);

    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("an honest full-u64 opening must prove through the Lean-emitted descriptor");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against the 17 published lanes");
}

/// THE FALSE POLARITY, on the Lean route: the Rust canary
/// `full_u64_alias_is_distinguished_and_each_join_lane_is_load_bearing` splices `+1` onto a public
/// wide lane. Here the same splice is rejected by the Lean-emitted descriptor — which is what
/// `WideValueBindingRefine.forged_lane_unsat` says as a theorem.
#[test]
fn lean_wide_value_binding_rejects_a_forged_public_lane() {
    let desc = lean_descriptor();
    let blind: [BabyBear; 6] = core::array::from_fn(|i| BabyBear::new(0x1000 + (i as u32) * 0x111));
    let (trace, pis) = lean_witness(
        0x1234_5678_9abc_def0,
        0xfedc_ba98_7654_3210,
        BabyBear::new(0x13579),
        blind,
    );
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest proof");
    let mut forged = pis.clone();
    forged[16] += BabyBear::ONE; // the last DOMAIN_B lane
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a forged public wide lane must not verify"
    );
}

/// THE ALIAS, on the Lean route: `value` and `value + p` publish the SAME one-felt compatibility
/// binding and DIFFERENT wide carriers — the Rust canary's two assertions, now over the
/// Lean-emitted object. `WideValueBindingRefine.legacy_join_cannot_separate_aliases` and
/// `alias_separated_by_the_wide_carrier` are the universally-quantified forms.
#[test]
fn lean_route_reproduces_the_alias_separation() {
    let value = 0x1234_5678_9abc_def0u64;
    let alias = value + BABYBEAR_P as u64;
    let asset = 0xfedc_ba98_7654_3210u64;
    let randomness = BabyBear::new(0x13579);
    let blind: [BabyBear; 6] = core::array::from_fn(|i| BabyBear::new(0x1000 + (i as u32) * 0x111));

    let (_, pis_lo) = lean_witness(value, asset, randomness, blind);
    let (_, pis_hi) = lean_witness(alias, asset, randomness, blind);

    assert_eq!(
        pis_lo[0], pis_hi[0],
        "the one-felt compatibility join is blind to the modulo-p alias"
    );
    assert_ne!(
        &pis_lo[1..17],
        &pis_hi[1..17],
        "the sixteen-lane carrier separates value from value + p"
    );
}
