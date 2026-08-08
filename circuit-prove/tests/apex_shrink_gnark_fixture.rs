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
    APEX_CLAIM_LANES, APEX_VK_LANES, DREGG_APEX_RECURSION_VK, EXPOSED_SHRINK_CLAIM_LANES,
    SETTLEMENT_CLAIM_LANES, VK_SPINE_LANES, apex_root_vk_spine, export_real_shrink_fri_fixture,
    shrink_apex_to_outer_exposed,
};
use dregg_circuit_prove::dregg_outer_config::{DreggOuterConfig, create_outer_config};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, prove_turn_chain_recursive, turn_chain_root_config,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_batch_proof_with_config;
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;
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

/// The deployed apex circuit's VK identity, derived from a FRESH FOLD AT HEAD —
/// not from the cached shrink proof, and not from either fixture. The fold is
/// verified before any identity is read off it.
///
/// Shared by the CHECK (`derive_deployed_apex_vk_identity_and_check_fixture`)
/// and the EMITTER (`emit_deployed_apex_vk_identity_artifact`), which is the
/// whole point of the split: both must derive the same way, and only one of
/// them may write.
fn head_apex_vk_identity() -> dregg_circuit_prove::apex_shrink_gnark_export::ApexVkIdentity {
    use dregg_circuit_prove::apex_shrink_gnark_export::{APEX_VK_LANES, derive_apex_vk_identity};

    // ⚑ **THE APEX ROOT IS READ AT THE TOWER'S ROOT CONFIG, NOT AT THE LEAF WRAP'S.** A turn-chain
    // leaf now MINTS at `create_recursion_config`'s engine, so every fold above it — the apex
    // included — emits `(lb 3, q 38)`. Verifying the apex under `ir2_leaf_wrap_config()` was
    // correct before the mint split and is now exactly the failure `config.rs` predicts for taking
    // the pre-split config: `QueryProofCountMismatch { expected: 19, got: 38 }`. It fired here on
    // 2026-08-08, the first time this lane was run after the switch, and it fails BEFORE the
    // identity is derived — so the apex VK-identity flag day could not even be started.
    let root_config = turn_chain_root_config();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    verify_recursive_batch_proof_with_config(&whole.root.0, &root_config)
        .expect("the fresh apex verifies under the turn chain's ROOT config");

    let id = derive_apex_vk_identity(&whole.root).expect("the real apex yields a VK identity");
    assert_eq!(id.apex_preprocessed_commit.len(), APEX_VK_LANES);
    println!("recursion_vk (HEAD-derived)    : {}", id.recursion_vk_hex);
    println!(
        "apex VK-core lanes (HEAD-derived): {:?}",
        id.apex_preprocessed_commit
    );
    id
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

    // ⚑ **THE APEX IS MINTED AT THE TOWER ROOT CONFIG, SO THE SHRINK MUST VERIFY IT AT THAT ONE.**
    // `inner_config` is not a bystander: `shrink_apex_to_outer_exposed` takes it as *the engine the
    // shrink circuit verifies the apex at IN-CIRCUIT*, so a stale config here does not merely fail
    // the host-side pre-check — it would build a shrink circuit for a verifier that no apex is
    // minted under. Post leaf-wrap-mint-split the apex is `(lb 3, q 38)`; `ir2_leaf_wrap_config()`
    // is `(lb 6, q 19)` and yields `QueryProofCountMismatch { expected: 19, got: 38 }`.
    let inner_config = turn_chain_root_config();
    verify_recursive_batch_proof_with_config(&whole.root.0, &inner_config)
        .expect("the real apex verifies under the turn chain's ROOT config");

    // The apex's expected claim, in the pinned order: the 25-lane settlement segment
    // (genesis_root8 ++ final_root8 ++ num_turns ++ chain_digest8), then the 8-lane root VK
    // SPINE — FOLLOWED BY the 8 apex VK-core lanes (the REAL apex's preprocessed commitment,
    // the RecursionVk-fingerprinted value the shrink pins + re-exposes).
    //
    // ⚑ The spine block is not optional padding: the root has exposed it since `e1d8ab9bc`
    // (07-30), and building the expectation without it is what made this lane's assertion read
    // "re-exposed shrink lanes != the chain's 25-lane claim ++ apex VK core" the first time the
    // lane could run at all.
    let mut expected_claim: Vec<u32> = Vec::with_capacity(EXPOSED_SHRINK_CLAIM_LANES);
    expected_claim.extend(whole.genesis_root.iter().map(|v| v.0));
    expected_claim.extend(whole.final_root.iter().map(|v| v.0));
    expected_claim.push(whole.num_turns as u32);
    expected_claim.extend(whole.chain_digest.iter().map(|v| v.0));
    let spine = apex_root_vk_spine(&whole.root).expect("the real apex exposes a root VK spine");
    assert_eq!(spine.len(), VK_SPINE_LANES);
    println!("root VK spine      : {spine:?}");
    expected_claim.extend(&spine);
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
        "re-exposed shrink lanes != the apex's claim (settlement segment ++ root VK spine) ++ \
         apex VK core"
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
/// a FRESH fold of the apex circuit at HEAD, WITHOUT reading either fixture.
/// Then, asserting only — nothing here writes:
///
///  1. GOVERNANCE PIN: the derived fingerprint equals the governance-pinned
///     `DREGG_APEX_RECURSION_VK` (weak-subjectivity anchor) — fail-closed; a
///     circuit change stops here until governance re-pins;
///  2. ARTIFACT DIFFERENTIAL: the COMMITTED
///     `chain/gnark/fixtures/apex_vk_identity.json` — the artifact the gnark
///     side bakes its `apexPreprocessedCommit` constant from — equals the
///     HEAD derivation, fingerprint and all eight lanes. The old form
///     OVERWROTE this file, so no test in the tree ever asked whether it was
///     still true;
///  3. PROOF-FIXTURE DIFFERENTIAL: the gnark proof fixture's baked apex VK-core
///     (`apex_shrink_fri_real.json` `apex_preprocessed_commit`) equals the
///     HEAD-derived deployed value — proving the fixture was minted over the
///     REAL deployed apex, so the SettlementCircuit's baked pin does not rest
///     on trusting whoever compiled the fixture.
///
/// VK material is content-independent and (WRAP on) depth-invariant, so the
/// fixed 2-turn chain's fresh fold carries the deployed circuit's identity —
/// the derivation depends only on the circuit definition at HEAD.
///
/// ⚑ **THE WRITE USED TO LIVE HERE, AND IT IS WHY THIS PIN RAN NOWHERE.**
/// Until 2026-08-08 this one test both *asserted* the fixture matched **and**
/// `(re)wrote chain/gnark/fixtures/apex_vk_identity.json`. That is a check
/// reading its own input: arming it on any lane would have made the lane
/// rewrite the artifact it was meant to check, so the roster correctly routed
/// it `fixture-mint` — "NOT ARMED, its effect is to WRITE a fixture into the
/// tree" — and the deployed apex VK pin, the one governance anchor with real
/// teeth, was executed by nothing at all.
///
/// The write is now [`emit_deployed_apex_vk_identity_artifact`] below, which
/// keeps the `fixture-mint` route. What is left here is a PURE CHECK, and it
/// gained the differential the write was papering over: the COMMITTED
/// `apex_vk_identity.json` must equal the HEAD derivation, rather than being
/// silently re-stamped to whatever HEAD says.
#[test]
#[ignore = "SLOW (one real 2-turn fold, ~4 min): derives the deployed apex VK identity at HEAD \
            and asserts the governance pin, the committed identity artifact and the gnark proof \
            fixture all agree with it. WRITES NOTHING — the emitter is \
            emit_deployed_apex_vk_identity_artifact"]
fn derive_deployed_apex_vk_identity_and_check_fixture() {
    use dregg_circuit_prove::apex_shrink_gnark_export::{
        ApexVkIdentity, check_apex_vk_identity_pin,
    };

    let id = head_apex_vk_identity();
    // THE GOVERNANCE PIN (the anchor's teeth, where the VK material exists):
    // the freshly derived fingerprint must equal the governance-pinned
    // DREGG_APEX_RECURSION_VK. Fingerprint and lanes come off the SAME
    // gp.commitment (the recursion_vk_fingerprint self-binding pair), so
    // passing this pin means the committed lanes are the ones the pinned
    // anchor hashes. If the apex circuit changed, this fails closed until
    // governance re-pins (update the Rust constant AND
    // chain/gnark/settlement_circuit.go DreggApexRecursionVk).
    check_apex_vk_identity_pin(&id)
        .unwrap_or_else(|e| panic!("HEAD-derived apex identity fails the governance pin: {e}"));

    // (1) THE ARTIFACT DIFFERENTIAL — the half the old write made unaskable.
    // The COMMITTED identity artifact (what `chain/gnark` bakes from, and what
    // the fast `apex_vk_identity_pin_rejects_mismatched_fingerprint` canary
    // checks against the constant only) must equal the HEAD derivation, lane
    // for lane. A stale artifact whose fingerprint still matches the pinned
    // anchor passes that canary and fails here.
    let raw = std::fs::read_to_string(apex_vk_identity_path())
        .expect("the committed apex VK identity artifact exists");
    let committed: ApexVkIdentity =
        serde_json::from_str(&raw).expect("committed identity JSON parses");
    assert_eq!(
        committed.recursion_vk_hex, id.recursion_vk_hex,
        "the COMMITTED apex_vk_identity.json fingerprint does not equal the apex derived at \
         HEAD — re-mint it with emit_deployed_apex_vk_identity_artifact and re-pin governance"
    );
    assert_eq!(
        committed.apex_preprocessed_commit, id.apex_preprocessed_commit,
        "the COMMITTED apex_vk_identity.json VK-core lanes do not equal the apex derived at HEAD"
    );

    // (2) THE PROOF-FIXTURE DIFFERENTIAL: the gnark proof fixture's baked apex
    // VK-core equals the independently HEAD-derived deployed value, so the
    // SettlementCircuit's baked pin does not rest on trusting whoever compiled
    // the fixture.
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
}

/// **THE MEASUREMENT THAT DECIDES HOW THE VK SPINE MAY BE BOUND ON THE SETTLEMENT PATH.**
///
/// The apex's exposed claim is `[settlement segment(25) ‖ vk_spine(8)]`. The segment is the
/// statement; the spine is subtree circuit identity. The gnark `SettlementCircuit` can bind an
/// identity block in exactly one of two ways, and they are not interchangeable:
///
///  * **BAKE it** as circuit constants, the way `apexPreprocessedCommit` is baked. Legitimate
///    only if the value is the SAME for every chain the deployed settlement circuit is meant to
///    accept — otherwise baking silently narrows the verifier to one chain length.
///  * **PUBLISH it** as further Groth16 public inputs, which keeps the verifier length-generic
///    and moves the on-chain arity 25 → 33 (three chains' verifiers re-emit).
///
/// The apex `RecursionVk` is depth-INVARIANT (WRAP), so the settlement circuit is otherwise
/// length-generic — a 2-turn and a 3-turn chain shrink to the same shape. Whether the SPINE is
/// too is a fact about `combine_vk_spine`'s fold, not a matter of taste, so this test MEASURES it
/// instead of arguing: fold a 2-turn chain and a 3-turn chain and compare the root spines.
///
/// ⚠ HONEST LABEL: this is a MEASUREMENT over two concrete chain lengths — a Rust case-test. It
/// is not a proof that the spine varies for every pair of lengths, and it carries no formal
/// content. It is here because it answers the design question with an observation instead of an
/// assumption, and because it will fail loudly if the fold is ever made shape-invariant.
#[test]
#[ignore = "SLOW (two real folds, ~30s): MEASURES whether the root VK spine varies with chain \
            length — the fact that decides whether the settlement path may BAKE the spine"]
fn root_vk_spine_varies_with_chain_length() {
    use dregg_circuit_prove::apex_shrink_gnark_export::{
        APEX_CLAIM_LANES, VK_SPINE_LANES, apex_root_vk_spine, derive_apex_vk_identity,
    };

    println!("apex claim lanes   : {APEX_CLAIM_LANES} (segment 25 ++ spine {VK_SPINE_LANES})");
    let mut rows: Vec<(usize, String, Vec<u32>, Vec<u32>)> = Vec::new();
    for n in 2..=5usize {
        let chain: Vec<FinalizedTurn> = (0..n).map(|i| make_turn(1000, i as u32)).collect();
        let whole = prove_turn_chain_recursive(&chain)
            .unwrap_or_else(|e| panic!("the {n}-turn chain folds: {e}"));
        let spine = apex_root_vk_spine(&whole.root).expect("root exposes a VK spine");
        assert_eq!(spine.len(), VK_SPINE_LANES);
        let id = derive_apex_vk_identity(&whole.root).expect("identity derives");
        println!("--- {n} turns ---");
        println!("  recursion_vk : {}", id.recursion_vk_hex);
        println!("  apex VK core : {:?}", id.apex_preprocessed_commit);
        println!("  root spine   : {spine:?}");
        rows.push((n, id.recursion_vk_hex, id.apex_preprocessed_commit, spine));
    }

    // THE TWO INVARIANCE QUESTIONS, reported as a table rather than asserted one pair at a time
    // (an early panic on the first pair hides the shape of the answer).
    let n0 = rows[0].0;
    for r in &rows[1..] {
        println!(
            "{n0} vs {}: recursion_vk {}  apex_vk_core {}  spine {}",
            r.0,
            if r.1 == rows[0].1 { "SAME" } else { "DIFFERS" },
            if r.2 == rows[0].2 { "SAME" } else { "DIFFERS" },
            if r.3 == rows[0].3 { "SAME" } else { "DIFFERS" },
        );
    }

    assert_ne!(
        rows[0].3, rows[1].3,
        "the root VK spine is IDENTICAL across chain lengths — combine_vk_spine has become \
         shape-invariant, and the settlement path may bake it as a constant after all. Re-decide \
         the binding before trusting this test's name."
    );
}

/// THE EMITTER (the write half of the split above). Derives the deployed apex
/// VK identity from a fresh fold at HEAD, asserts the governance pin — the
/// artifact is never stamped with an unpinned fingerprint — and writes
/// `chain/gnark/fixtures/apex_vk_identity.json`, the source the gnark side
/// bakes its `apexPreprocessedCommit` constant from.
///
/// ⚠ Its effect is to WRITE A FIXTURE INTO THE TREE, so it is routed
/// `fixture-mint` and is NOT armed on any lane: a nightly that mints fixtures
/// is a nightly that edits the repository. Run it by hand, as step 3 of the
/// apex-VK flag day (`apex_shrink_gnark_export::DREGG_APEX_RECURSION_VK`).
#[test]
#[ignore = "SLOW (one real 2-turn fold, ~4 min) and it WRITES \
            chain/gnark/fixtures/apex_vk_identity.json — run by hand during an apex-VK flag day"]
fn emit_deployed_apex_vk_identity_artifact() {
    use dregg_circuit_prove::apex_shrink_gnark_export::check_apex_vk_identity_pin;

    let id = head_apex_vk_identity();
    // Fail closed BEFORE emitting: an identity whose fingerprint is not the
    // governance-pinned anchor must never be stamped into the tree.
    check_apex_vk_identity_pin(&id)
        .unwrap_or_else(|e| panic!("refusing to emit an unpinned apex identity: {e}"));

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
    // Same rotation as `real_shrink_proof`: the apex mints at the tower root config, so the
    // pinned-shrink REJECT canary must build its shrink circuit against that verifier — otherwise
    // it would "reject" for a query-count mismatch rather than for the foreign VK pin, which is a
    // canary that passes for the wrong reason.
    let inner_config = turn_chain_root_config();
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

    // The fixture's claim channel is the proof's re-exposed apex claim (25-lane settlement
    // segment ++ 8-lane root VK spine) ++ the 8 apex VK-core lanes, and BOTH labeled copies
    // match their blocks of the channel.
    assert_eq!(
        fixture.table_publics[fixture.claim_instance].len(),
        EXPOSED_SHRINK_CLAIM_LANES
    );
    assert_eq!(
        fixture.table_publics[fixture.claim_instance],
        proof_claim_lanes(&proof),
        "fixture claim lanes drifted from the proof's expose_claim public values"
    );
    assert_eq!(fixture.root_vk_spine.len(), VK_SPINE_LANES);
    assert_eq!(
        fixture.root_vk_spine[..],
        fixture.table_publics[fixture.claim_instance][SETTLEMENT_CLAIM_LANES..APEX_CLAIM_LANES],
        "labeled root VK-spine copy drifted from the claim channel's spine block"
    );
    assert_eq!(fixture.apex_preprocessed_commit.len(), APEX_VK_LANES);
    assert_eq!(
        fixture.apex_preprocessed_commit[..],
        fixture.table_publics[fixture.claim_instance][APEX_CLAIM_LANES..],
        "labeled apex VK-core copy drifted from the claim-channel tail"
    );
    println!("root_vk_spine           : {:?}", fixture.root_vk_spine);
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
