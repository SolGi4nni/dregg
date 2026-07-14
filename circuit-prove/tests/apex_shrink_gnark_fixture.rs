//! THE WRAP FIXTURE EXPORT: serialize a REAL shrink proof's FRI layer +
//! transcript prefix into the gnark fixture
//! `chain/gnark/fixtures/apex_shrink_fri_real.json`.
//!
//! Same real objects as `apex_shrink_bn254_tooth.rs` (a 2-turn rotated
//! chain → `ir2_leaf_wrap` apex → BN254-native shrink proof) — except the
//! turn BODY is `IncrementNonce`, not the tooth's `Transfer` (see
//! [`make_turn`] for why), plus:
//!
//! 1. the shrink proof is CACHED (postcard, under `target/`) so re-exports
//!    skip the ~20-minute fold+shrink when a verified cache exists;
//! 2. `export_real_shrink_fri_fixture` mirrors the batch verifier's pre-FRI
//!    transcript and re-runs the FRI core host-side with real p3 components —
//!    the export FAILS unless the real `pcs.verify` accepts from the mirrored
//!    transcript state AND every fold chain reaches the final polynomial
//!    (see the module doc of `apex_shrink_gnark_export` for the argument);
//! 3. the fixture JSON is written for the gnark tests
//!    (`chain/gnark/apex_shrink_real_fixture_test.go`) to load.
//!
//! Run:
//!   cargo test -p dregg-circuit-prove --release --test apex_shrink_gnark_fixture -- --ignored --nocapture

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::apex_shrink::verify_shrink_proof;
use dregg_circuit_prove::apex_shrink_gnark_export::{
    DREGG_APEX_RECURSION_VK, export_real_shrink_fri_fixture, shrink_apex_to_outer_exposed,
};
use dregg_circuit_prove::dregg_outer_config::{DreggOuterConfig, create_outer_config};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_batch_proof_with_config;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;
use p3_circuit_prover::BatchStarkProof;
use p3_field::PrimeField32;

/// OPEN permissions (the audited Bucket-F mint fixture, as in the tooth).
fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// One `IncrementNonce` turn (the `apex_shrink_blowup_sweep.rs` fixture).
///
/// HONEST LABEL: the tooth's fixture uses `Effect::Transfer`, but the working
/// tree currently carries a mid-flight sibling flag-day (GAP #4 wide-registry
/// cutover — the v3-staged registry's transfer display name is
/// `dregg-effectvm-transfer-v1-avail-…` while the wide registry the mint reads
/// still says `dregg-effectvm-transfer-v1-…`), so a transfer leg fails host
/// admission (`not a known R=24 cohort member`). `IncrementNonce`'s rows AGREE
/// across both registries, and the export doesn't care WHICH effect the apex
/// folds — only that the apex is real. The transfer-bodied version of this
/// fixture runs unchanged once the sibling regenerates the wide registry.
fn make_turn(balance: u64, nonce: u32) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::IncrementNonce];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell(balance as i64, nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        None,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// The fixed 2-turn chain (`recursion_vk_determinism.rs`'s fixture shape,
/// `IncrementNonce`-bodied — see [`make_turn`]; the same chain
/// `apex_shrink_blowup_sweep.rs` folds).
fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0), make_turn(1000, 1)]
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("circuit-prove has a parent")
        .to_path_buf()
}

/// Cache v3: the EXPOSED-claim shrink proof (shrink_apex_to_outer_exposed,
/// now WITH the apex-VK pin + 8 re-exposed VK-core lanes) plus the chain's
/// expected 33-lane channel, so cache-hit runs can still assert the binding
/// without re-folding the apex. (v2 cached the 25-lane pre-pin proof — the
/// filename bump retires it.)
///
/// LANE-INDEPENDENT + VK-EPOCH-KEYED: the cache lives OUTSIDE the per-lane
/// build tree so the ~20-min fold+shrink is reused ACROSS lanes (a fresh
/// `pbuild`/`hbuild` lane no longer re-pays it), not just within one
/// `target/`. The directory is, in order of preference:
///   1. `$DREGG_SHRINK_CACHE_DIR` (explicit override), else
///   2. `$HOME/.cache/dregg-shrink`, else
///   3. the old lane-local `target/` (last-resort fallback if HOME is unset).
///
/// The filename is KEYED on the governance-pinned apex VK epoch
/// (`DREGG_APEX_RECURSION_VK`): that constant changes exactly when the apex
/// circuit / VK epoch is re-pinned, so a VK-flip mints a NEW cache filename and
/// the stale proof is NOT reused (invalidation by construction, on top of the
/// existing load-time `verify_shrink_proof` + claim-match self-check). The key
/// is the first 16 hex chars of the pin — enough to separate epochs, short
/// enough for a readable filename.
fn shrink_cache_dir() -> PathBuf {
    if let Some(dir) = std::env::var_os("DREGG_SHRINK_CACHE_DIR") {
        return PathBuf::from(dir);
    }
    if let Some(home) = std::env::var_os("HOME") {
        return PathBuf::from(home).join(".cache/dregg-shrink");
    }
    // HOME unset (unusual): fall back to the lane-local target so we never panic.
    repo_root().join("target")
}

fn cache_path() -> PathBuf {
    let vk_key: String = DREGG_APEX_RECURSION_VK.chars().take(16).collect();
    shrink_cache_dir().join(format!(
        "apex_shrink_exposed_proof_cache_v3_{vk_key}.postcard"
    ))
}

fn fixture_path() -> PathBuf {
    repo_root().join("chain/gnark/fixtures/apex_shrink_fri_real.json")
}

fn apex_vk_identity_path() -> PathBuf {
    repo_root().join("chain/gnark/fixtures/apex_vk_identity.json")
}

type CachedShrink = (Vec<u8>, Vec<u32>); // (postcard proof bytes, expected 25-lane claim)

/// The proof's own re-exposed claim lanes (canonical u32), from its
/// expose_claim table.
fn proof_claim_lanes(proof: &BatchStarkProof<DreggOuterConfig>) -> Vec<u32> {
    proof
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .expect("exposed shrink proof carries an expose_claim table")
        .public_values
        .iter()
        .map(|v| v.as_canonical_u32())
        .collect()
}

/// Load a cached exposed shrink proof if present AND it still verifies AND its
/// re-exposed claim matches the cached expectation; otherwise regenerate from
/// the real 2-turn chain and cache it.
fn real_shrink_proof(outer_config: &DreggOuterConfig) -> BatchStarkProof<DreggOuterConfig> {
    let cache = cache_path();
    if let Ok(bytes) = std::fs::read(&cache) {
        if let Ok((proof_bytes, expected_claim)) = postcard::from_bytes::<CachedShrink>(&bytes) {
            if let Ok(proof) =
                postcard::from_bytes::<BatchStarkProof<DreggOuterConfig>>(&proof_bytes)
            {
                if verify_shrink_proof(&proof, outer_config).is_ok()
                    && proof_claim_lanes(&proof) == expected_claim
                {
                    println!("using cached exposed shrink proof: {}", cache.display());
                    return proof;
                }
                println!("cached shrink proof no longer verifies/matches — regenerating");
            } else {
                println!("cached shrink proof no longer deserializes — regenerating");
            }
        } else {
            println!("cache envelope no longer deserializes — regenerating");
        }
    }

    // ---- the REAL apex (same flow as apex_shrink_bn254_tooth.rs) ----------
    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    println!("apex fold time     : {:?}", t0.elapsed());

    let inner_config = ir2_leaf_wrap_config();
    verify_recursive_batch_proof_with_config(&whole.root.0, &inner_config)
        .expect("the real apex verifies under ir2_leaf_wrap_config");

    // The chain's expected 25-lane settlement claim, in the pinned order
    // genesis_root8 ++ final_root8 ++ num_turns ++ chain_digest8 — FOLLOWED BY
    // the 8 apex VK-core lanes (the REAL apex's preprocessed commitment, the
    // RecursionVk-fingerprinted value the shrink pins + re-exposes).
    let mut expected_claim: Vec<u32> = Vec::with_capacity(33);
    expected_claim.extend(whole.genesis_root.iter().map(|v| v.0));
    expected_claim.extend(whole.final_root.iter().map(|v| v.0));
    expected_claim.push(whole.num_turns as u32);
    expected_claim.extend(whole.chain_digest.iter().map(|v| v.0));
    let apex_vk: Vec<u32> = whole
        .root
        .running_preprocessed_commit()
        .expect("the real apex carries a preprocessed commitment (its VK core)")
        .roots()
        .iter()
        .flat_map(|r| r.iter().map(|v| v.as_canonical_u32()))
        .collect();
    assert_eq!(apex_vk.len(), 8, "apex VK core is one 8-felt W16 root");
    println!("apex VK-core lanes : {apex_vk:?}");
    expected_claim.extend(&apex_vk);

    let t1 = Instant::now();
    let shrink = shrink_apex_to_outer_exposed(&whole.root, &inner_config, outer_config)
        .expect("the real apex shrinks (with exposed claim) under DreggOuterConfig");
    println!("shrink prove time  : {:?}", t1.elapsed());

    verify_shrink_proof(&shrink.proof, outer_config)
        .expect("the BN254-native exposed shrink proof verifies");

    // THE CLAIM TOOTH: the shrink proof's own expose_claim public values ARE
    // the chain's 25-lane claim ++ the apex's 8 VK-core lanes, lane for lane.
    assert_eq!(
        proof_claim_lanes(&shrink.proof),
        expected_claim,
        "re-exposed shrink lanes != the chain's 25-lane claim ++ apex VK core"
    );

    let proof_bytes =
        postcard::to_allocvec(&shrink.proof).expect("shrink proof postcard-serializes");
    let bytes =
        postcard::to_allocvec(&(proof_bytes, expected_claim)).expect("cache envelope serializes");
    if let Some(dir) = cache.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    std::fs::write(&cache, &bytes).expect("write shrink proof cache");
    println!(
        "cached exposed shrink proof ({} bytes): {}",
        bytes.len(),
        cache.display()
    );
    shrink.proof
}

/// THE DEPLOYED-IDENTITY DERIVATION + DIFFERENTIAL (the apex-VK pin's VALUE
/// authority): derive the deployed dregg apex's VK identity — its
/// `RecursionVk` fingerprint (asserted against the governance-pinned
/// `DREGG_APEX_RECURSION_VK` anchor) plus the
/// `ApexVkLanes` preprocessed-commitment lanes that fingerprint hashes — from
/// a FRESH fold of the apex circuit at HEAD, WITHOUT reading the proof
/// fixture. Then:
///
///  1. DIFFERENTIAL: assert the gnark proof fixture's baked apex VK-core
///     (`apex_shrink_fri_real.json` `apex_preprocessed_commit`) equals the
///     HEAD-derived deployed value — proving the fixture was minted over the
///     REAL deployed apex, so the SettlementCircuit's baked pin does not rest
///     on trusting whoever compiled the fixture;
///  2. GOVERNANCE PIN: assert the derived fingerprint equals the
///     governance-pinned `DREGG_APEX_RECURSION_VK` (weak-subjectivity anchor)
///     — fail-closed BEFORE emitting; a circuit change stops here until
///     governance re-pins;
///  3. emit `chain/gnark/fixtures/apex_vk_identity.json` — the derived
///     identity artifact the gnark side bakes its `apexPreprocessedCommit`
///     constant from (fingerprint-bound: the JSON carries the RecursionVk hex
///     the lanes hash into, and every consumer asserts that hex against the
///     pinned anchor at load; see `ApexVkIdentity` /
///     `check_apex_vk_identity_pin`).
///
/// VK material is content-independent and (WRAP on) depth-invariant, so the
/// fixed 2-turn chain's fresh fold carries the deployed circuit's identity —
/// the derivation depends only on the circuit definition at HEAD.
#[test]
#[ignore = "SLOW (one real 2-turn fold, ~4 min): derives the deployed apex VK identity at HEAD, \
            asserts the gnark fixture matches it, and (re)writes \
            chain/gnark/fixtures/apex_vk_identity.json"]
fn derive_deployed_apex_vk_identity_and_check_fixture() {
    use dregg_circuit_prove::apex_shrink_gnark_export::{
        APEX_VK_LANES, check_apex_vk_identity_pin, derive_apex_vk_identity,
    };

    // The deployed apex circuit at HEAD: a fresh fold (NOT the cached shrink,
    // NOT the fixture). Verified before the identity is read off it.
    let inner_config = ir2_leaf_wrap_config();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    verify_recursive_batch_proof_with_config(&whole.root.0, &inner_config)
        .expect("the fresh apex verifies under ir2_leaf_wrap_config");

    let id = derive_apex_vk_identity(&whole.root).expect("the real apex yields a VK identity");
    assert_eq!(id.apex_preprocessed_commit.len(), APEX_VK_LANES);
    // THE GOVERNANCE PIN (the anchor's teeth, where the VK material exists):
    // the freshly derived fingerprint must equal the governance-pinned
    // DREGG_APEX_RECURSION_VK before the artifact is emitted. Fingerprint and
    // lanes come off the SAME gp.commitment (the recursion_vk_fingerprint
    // self-binding pair), so passing this pin means the emitted lanes are the
    // ones the pinned anchor hashes. If the apex circuit changed, this fails
    // closed until governance re-pins (update the Rust constant AND
    // chain/gnark/settlement_circuit.go DreggApexRecursionVk).
    check_apex_vk_identity_pin(&id)
        .unwrap_or_else(|e| panic!("HEAD-derived apex identity fails the governance pin: {e}"));
    println!("recursion_vk (deployed anchor) : {}", id.recursion_vk_hex);
    println!(
        "apex VK-core lanes (derived)   : {:?}",
        id.apex_preprocessed_commit
    );

    // (1) THE DIFFERENTIAL: the proof fixture's baked apex VK-core equals the
    // independently HEAD-derived deployed value.
    let raw = std::fs::read_to_string(fixture_path())
        .expect("the gnark proof fixture exists (export_real_shrink_fri_fixture_for_gnark)");
    let fx: serde_json::Value = serde_json::from_str(&raw).expect("fixture JSON parses");
    let fixture_lanes: Vec<u32> = fx["apex_preprocessed_commit"]
        .as_array()
        .expect("fixture carries apex_preprocessed_commit")
        .iter()
        .map(|v| u32::try_from(v.as_u64().expect("lane is a u64")).expect("lane fits u32"))
        .collect();
    assert_eq!(
        fixture_lanes, id.apex_preprocessed_commit,
        "the gnark fixture's apex VK-core does NOT equal the deployed apex derived at HEAD — \
         either the apex circuit changed since the fixture was minted (re-export the fixture) \
         or the fixture was minted over a NON-deployed apex (the forgery the pin exists to block)"
    );

    // (2) Emit the derived identity artifact (the gnark bake source).
    let json = serde_json::to_string_pretty(&id).expect("identity serializes");
    std::fs::write(apex_vk_identity_path(), &json).expect("write apex VK identity");
    println!("wrote {}", apex_vk_identity_path().display());
}

/// THE ANCHOR-CHECK CANARY (fast, no proving — the Rust half; the gnark half
/// is `TestApexVkIdentityAnchorRejectsMismatchedFingerprint`): the COMMITTED
/// identity artifact matches the governance-pinned `DREGG_APEX_RECURSION_VK`
/// anchor (ACCEPT), and an identity carrying any OTHER fingerprint REJECTS —
/// so the anchor is a real fail-closed check, not a decorative field.
#[test]
fn apex_vk_identity_pin_rejects_mismatched_fingerprint() {
    use dregg_circuit_prove::apex_shrink_gnark_export::{
        ApexVkIdentity, DREGG_APEX_RECURSION_VK, check_apex_vk_identity_pin,
    };

    let raw = std::fs::read_to_string(apex_vk_identity_path())
        .expect("the committed apex VK identity artifact exists");
    let id: ApexVkIdentity = serde_json::from_str(&raw).expect("identity JSON parses");

    // ACCEPT: the honest deployed identity matches the governance pin.
    check_apex_vk_identity_pin(&id)
        .expect("the committed deployed identity must match the governance-pinned anchor");
    assert_eq!(id.recursion_vk_hex, DREGG_APEX_RECURSION_VK);

    // REJECT: one flipped nibble — a valid-shape 32-byte fingerprint that is
    // NOT the pinned anchor — must fail the check.
    let mut doctored = id.clone();
    let mut hex = doctored.recursion_vk_hex.into_bytes();
    hex[0] = if hex[0] == b'0' { b'1' } else { b'0' };
    doctored.recursion_vk_hex = String::from_utf8(hex).expect("still ASCII hex");
    assert!(
        check_apex_vk_identity_pin(&doctored).is_err(),
        "an identity with a NON-pinned recursion_vk_hex was ACCEPTED — the governance anchor \
         is decorative"
    );
}

/// THE APEX-VK-PIN REJECT CANARY (Rust half — the gnark half is
/// `TestSettlementCircuitPinsApexPreprocessedCommitment`): a shrink pinned to
/// a DIFFERENT apex preprocessed commitment than the apex actually proved
/// must FAIL — this is what a same-shape malicious apex looks like to the
/// pinned shrink circuit (`pin_preprocessed_commit` connects the apex
/// verification's preprocessed-commitment inputs to baked constants; a value
/// mismatch is unsatisfiable). The ACCEPT half (honest pin proves) is the
/// exporter test above, which mints the fixture through the same
/// `shrink_apex_to_outer_exposed_pinned_to(honest)` path.
#[test]
#[ignore = "SLOW (one real 2-turn fold, ~4 min): run with --ignored — the apex-VK-pin REJECT canary"]
fn shrink_pinned_to_foreign_apex_vk_rejects() {
    use dregg_circuit_prove::apex_shrink_gnark_export::{
        ApexVkCommit, shrink_apex_to_outer_exposed_pinned_to,
    };
    use p3_field::PrimeCharacteristicRing;

    let outer_config = create_outer_config();
    let inner_config = ir2_leaf_wrap_config();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    let honest = whole
        .root
        .running_preprocessed_commit()
        .expect("the real apex carries a preprocessed commitment");

    // Doctor ONE felt of the expected commitment — the deployed-apex pin a
    // settlement service would hold when handed a same-shape FOREIGN apex.
    let mut roots = honest.roots().to_vec();
    roots[0][0] += p3_baby_bear::BabyBear::ONE;
    let foreign = ApexVkCommit::from(roots);

    match shrink_apex_to_outer_exposed_pinned_to(&whole.root, &inner_config, &outer_config, foreign)
    {
        Ok(_) => panic!("a shrink pinned to a foreign apex VK-core must NOT witness/prove"),
        Err(err) => println!("apex-VK pin mismatch rejected: {err}"),
    }
}

#[test]
#[ignore = "SLOW unless the shrink-proof cache exists (one real 2-turn fold + BN254-native shrink \
            prove, ~20 min); run with --ignored — emits chain/gnark/fixtures/apex_shrink_fri_real.json"]
fn export_real_shrink_fri_fixture_for_gnark() {
    let outer_config = create_outer_config();
    let proof = real_shrink_proof(&outer_config);

    // The export self-checks: real pcs.verify from the mirrored transcript
    // state + full host-side FRI-core re-verification (fold chains, Merkle
    // openings, PoW, final poly) over exactly the data being exported.
    let t = Instant::now();
    let fixture = export_real_shrink_fri_fixture(&proof, &outer_config)
        .expect("fixture export (with host-side self-checks) succeeds");
    println!("export+selfcheck   : {:?}", t.elapsed());

    let json = serde_json::to_string(&fixture).expect("fixture serializes");
    let path = fixture_path();
    std::fs::write(&path, &json).expect("write gnark fixture");

    println!("=== REAL SHRINK FRI FIXTURE ===");
    println!("path               : {}", path.display());
    println!("bytes              : {}", json.len());
    println!("degree_bits        : {:?}", fixture.degree_bits);
    println!(
        "rounds/queries     : {} / {}",
        fixture.fri.rounds,
        fixture.queries.len()
    );
    println!("log_max_height     : {}", fixture.fri.log_global_max_height);
    println!("roll_in_rounds     : {:?}", fixture.roll_in_rounds);
    println!("prefix events      : {}", fixture.prefix_events.len());
    println!("claim_instance     : {}", fixture.claim_instance);
    println!(
        "claim lanes        : {:?}",
        fixture.table_publics[fixture.claim_instance]
    );

    // The fixture's claim channel is the proof's re-exposed 25-lane claim ++
    // the 8 apex VK-core lanes, and the labeled apex_preprocessed_commit copy
    // matches the channel tail.
    assert_eq!(fixture.table_publics[fixture.claim_instance].len(), 33);
    assert_eq!(
        fixture.table_publics[fixture.claim_instance],
        proof_claim_lanes(&proof),
        "fixture claim lanes drifted from the proof's expose_claim public values"
    );
    assert_eq!(fixture.apex_preprocessed_commit.len(), 8);
    assert_eq!(
        fixture.apex_preprocessed_commit[..],
        fixture.table_publics[fixture.claim_instance][25..],
        "labeled apex VK-core copy drifted from the claim-channel tail"
    );
    println!(
        "apex_preprocessed_commit: {:?}",
        fixture.apex_preprocessed_commit
    );

    // Shape sanity the gnark loader will re-assert.
    assert_eq!(fixture.fri.rounds, fixture.commit_roots.len());
    assert_eq!(fixture.queries.len(), fixture.fri.num_queries);
    for q in &fixture.queries {
        assert_eq!(q.siblings.len(), fixture.fri.rounds);
        assert_eq!(q.roll_ins.len(), fixture.roll_in_rounds.len());
        for (r, path) in q.merkle_paths.iter().enumerate() {
            assert_eq!(path.len(), fixture.fri.log_global_max_height - r - 1);
        }
    }
}
