//! RECURSION-VK DETERMINISM TOOTH.
//!
//! The `RecursionVk` fingerprint is the light client's distributed trust anchor: an
//! honest setup party extracts it ONCE from a locally produced fold and ships it. That
//! property is VOID if an honest re-fold of the same chain can mint a DIFFERENT
//! fingerprint — then the "anchor" cannot be reproduced, and every same-shape
//! precondition (e.g. `carried_binding_proof_unlinked_to_root_is_rejected`'s
//! same-fingerprint assert) is a coin flip.
//!
//! THE BUG THIS PINS AGAINST (found 2026-07-02, fixed in the plonky3-recursion fork):
//! `verify_p3_batch_proof_circuit` grouped global-lookup cumulative sums in a
//! `hashbrown::HashMap<&String, _>` and EMITTED the `verify_global_final_value_circuit`
//! ops in `.values()` order. hashbrown seeds each map instance separately, so the
//! verifier op-list — and hence dedup/fusion outcomes, primitive-table row counts
//! (observed: 521 vs 529 / 142831 vs 142837), the preprocessed commitment, and the VK
//! fingerprint — was random per circuit build, EVEN WITHIN ONE PROCESS. Fork fix:
//! BTreeMap (rev on the `update-plonky3-rev` branch after be52a51).
//!
//! This tooth folds the IDENTICAL 2-turn chain three times in-process and once in a
//! CHILD PROCESS (fresh hasher seeds, fresh address space) and requires all four
//! fingerprints equal. Real folds take minutes; `#[ignore]`, run with:
//!   cargo test -p dregg-circuit-prove --test recursion_vk_determinism -- --ignored --nocapture

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::ivc_turn_chain::{FinalizedTurn, prove_turn_chain_recursive};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

/// OPEN permissions so the rotated producer-witness path admits the actor cell
/// without auth gating (the audited Bucket-F mint fixture, as in
/// `ivc_turn_chain_rotated.rs`).
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

fn make_turn(balance: u64, nonce: u32, amount: u64) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &[0u8; 32],
        &[0u8; 32],
        &receipt_log,
        None,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// The one FIXED chain every fold in this tooth uses: 2 transfer turns,
/// balance 1000, amount 7.
fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0, 7), make_turn(1000 - 7, 1, 7)]
}

/// Fold the fixed chain once and return the root VK fingerprint (hex).
fn fold_fingerprint() -> String {
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed chain folds");
    whole.root_vk_fingerprint().to_hex()
}

/// Env var that flips this test binary into CHILD mode: compute one fingerprint,
/// print it, exit. The parent test spawns itself with this set to get a genuinely
/// separate-process fold (fresh hasher seeds / ASLR / allocator state).
const CHILD_ENV: &str = "DREGG_VK_DETERMINISM_CHILD";
/// Marker the child prefixes its fingerprint line with on stdout.
const CHILD_MARKER: &str = "CHILD_VK_FINGERPRINT=";

#[test]
#[ignore = "SLOW: four real recursion folds (~minutes); run with --ignored — the VK-as-trust-anchor determinism tooth"]
fn recursion_vk_fingerprint_deterministic_in_process_and_cross_process() {
    // CHILD MODE: one fold, print, done.
    if std::env::var_os(CHILD_ENV).is_some() {
        println!("{}{}", CHILD_MARKER, fold_fingerprint());
        return;
    }

    // IN-PROCESS: three folds of the IDENTICAL chain must agree. (The pre-fix engine
    // failed this with high probability: 2 global-lookup bus names ⇒ a per-build coin
    // flip between two op-list orders ⇒ two distinct fingerprints.)
    let fp0 = fold_fingerprint();
    for i in 1..3 {
        let fp_i = fold_fingerprint();
        assert_eq!(
            fp0, fp_i,
            "in-process fold #{i} minted a DIFFERENT recursion-VK fingerprint for the \
             identical chain — the root circuit build is nondeterministic and the VK \
             cannot serve as a distributed trust anchor"
        );
    }

    // CROSS-PROCESS: spawn this same test binary in child mode. A fresh process gets
    // fresh hash seeds and a fresh address space, so this catches per-process-seed and
    // pointer-keyed nondeterminism that in-process repetition can miss.
    let exe = std::env::current_exe().expect("test binary path");
    let out = std::process::Command::new(exe)
        .args([
            "--ignored",
            "--exact",
            "recursion_vk_fingerprint_deterministic_in_process_and_cross_process",
            "--nocapture",
        ])
        .env(CHILD_ENV, "1")
        .output()
        .expect("child fold process runs");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "child fold process failed: status {:?}\nstdout:\n{stdout}\nstderr:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let child_fp = stdout
        .lines()
        .find_map(|l| l.strip_prefix(CHILD_MARKER))
        .unwrap_or_else(|| panic!("child printed no {CHILD_MARKER} line; stdout:\n{stdout}"));
    assert_eq!(
        fp0, child_fp,
        "a SEPARATE PROCESS folding the identical chain minted a different recursion-VK \
         fingerprint — cross-process nondeterminism breaks the distributed trust anchor"
    );
}
