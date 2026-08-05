//! Native linked probe for the Lean-owned Path of Angels Records read model.
//!
//! It calls the real linked symbol over the frozen live epoch-1 genesis blobs with **no finalized
//! rows** — the state a node is in before its first turn settles — and asserts the emitted view is
//! a real world rather than an empty page: the exact federation, content epoch, curator, world
//! meters and playable mission the ceremony installed.
//!
//! It also asserts the things the view must NOT contain, which is more than one and was
//! previously understated. `POA-RECORDS-OUT-2` has no `target` field — but omitting `target`
//! was never sufficient, because a mission carries `run_seed` and
//! `SignalTriangulation.targetFromSeed` is a public total function: a published live seed IS the
//! answer, three modulo operations away. The view therefore publishes a seedless mission, and
//! this probe fails if `run_seed` ever reappears anywhere in the document.
//!
//! It also fails if `transcript_digest` reappears. That field was never a digest —
//! `SignalTriangulation.transcriptDigest` is a fixed-width plaintext encoding whose tail is the
//! submitted code — and hashing it would not help, because an accepted transcript is at most five
//! guesses from 216, about `2^39`, which brute-force inverts trivially.
//!
//! ⚠ The frozen genesis config is a mission TEMPLATE: its `run_seed` is the all-zero
//! `Emit.UNBOUND_RUN_SEED` and its `target` is that sentinel's target, not any live instance's
//! answer. Lean refuses to project a config whose seed is not the sentinel; the precise,
//! attributable form of that refusal is `RecordsRuntime.hostile_live_run_seed_config_refused`.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::poa_records_ffi::{
    poa_records_project_available, project_poa_records, PoaRecordsVerdict,
};
use serde_json::Value;

const CONFIG_FILE: &str = include_str!("fixtures/poa-network-genesis-config-v1.json");
const CANON_FILE: &str = include_str!("fixtures/poa-network-genesis-canon-v1.json");

fn fixture(bytes: &'static str) -> &'static str {
    bytes
        .strip_suffix('\n')
        .expect("frozen PoA genesis fixture must have exactly one file newline")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Exactly `RecordsRuntime.RequestWire.toJson`: compact, this field order, blobs as lowercase
/// hexadecimal of their UTF-8 bytes. Any other spelling is refused by Lean's canonical seal.
fn genesis_only_request(config: &str, canon: &str, federation_id: &str) -> String {
    format!(
        "{{\"format\":\"POA-RECORDS-IN-1\",\"federation_id\":\"{federation_id}\",\
         \"genesis_canon\":\"{}\",\"config\":\"{}\",\"rows\":[]}}",
        hex(canon.as_bytes()),
        hex(config.as_bytes())
    )
}

fn project(request: &str) -> PoaRecordsVerdict {
    project_poa_records(request).expect("linked Lean Records read model must be callable")
}

#[test]
fn genesis_only_records_view_is_a_real_world_and_omits_the_signal_target() {
    assert!(
        poa_records_project_available(),
        "dregg_poa_records_project is absent or initialization failed; this is refusal, not skip"
    );

    let config = fixture(CONFIG_FILE);
    let canon = fixture(CANON_FILE);
    let canon_value: Value = serde_json::from_str(canon).expect("frozen Canon is JSON");
    let config_value: Value = serde_json::from_str(config).expect("frozen config is JSON");
    let federation_id = canon_value["federation_id"]
        .as_str()
        .expect("Canon names its federation");

    let request = genesis_only_request(config, canon, federation_id);
    let PoaRecordsVerdict::Projected(projected) = project(&request) else {
        panic!("Lean refused the frozen live genesis with no finalized rows");
    };
    assert!(
        projected.was_projected_for(request.as_bytes()),
        "the carrier must be bound to this exact request"
    );

    let view: Value = serde_json::from_str(projected.as_str()).expect("Lean emitted valid JSON");
    // ⚑ `-2`, not `-1`: the published mission lost `run_seed`, the run record lost
    // `transcript_digest`, and the coordinate moved under `chain`. A reader pinned to the old
    // tag must fail its format check rather than silently find fields missing.
    assert_eq!(view["format"].as_str(), Some("POA-RECORDS-OUT-2"));

    // The world a run would land in — decoded from the bytes the ceremony installed.
    assert_eq!(view["federation_id"], canon_value["federation_id"]);
    assert_eq!(view["content_root"], canon_value["content_root"]);
    assert_eq!(view["activation_digest"], canon_value["activation_digest"]);
    assert_eq!(view["content_session"], canon_value["content_session"]);
    assert_eq!(view["content_epoch"], canon_value["content_epoch"]);
    assert_eq!(view["curator_key"], canon_value["curator_key"]);
    assert_eq!(view["world"], canon_value["world"]);
    assert_eq!(view["canon_revision"], canon_value["revision"]);

    // The playable mission and its exact reward, not a summary of them — except that the
    // published mission is deliberately SEEDLESS. Every other field is byte-identical to the
    // installed config, so this is a projection and not a re-description.
    let mut expected_mission = config_value["mission"].clone();
    let stripped = expected_mission
        .as_object_mut()
        .expect("the installed mission is a JSON object")
        .remove("run_seed");
    assert!(
        stripped.is_some(),
        "the frozen config's mission must carry a run_seed for this comparison to mean anything"
    );
    assert_eq!(view["mission"], expected_mission);
    assert!(
        view["mission"].get("run_seed").is_none(),
        "the published mission must have no run_seed field"
    );
    assert_eq!(view["reward"], config_value["reward"]);

    // Before the first turn settles the view says so in one word, rather than leaving a reader
    // to infer it from an empty array.
    assert_eq!(view["stage"].as_str(), Some("awaiting-first-run"));

    // Nothing has landed yet, and the view says so in every projection at once.
    assert_eq!(view["runs"].as_array().map(Vec::len), Some(0));
    assert_eq!(view["catalog"].as_array().map(Vec::len), Some(0));
    for counted in [
        "archive_entries",
        "locker_entries",
        "attendant_notices",
        "editorial_inbox",
        "consumed_runs",
        "players",
    ] {
        assert_eq!(view[counted].as_u64(), Some(0), "{counted}");
    }

    // ⚠ Each needle is checked to be a real needle in the SOURCE before its absence is read in
    // the OUTPUT. An absence assertion whose needle was never there to begin with passes while
    // exercising nothing.
    assert!(
        config_value.get("target").is_some(),
        "the frozen config carries a target field"
    );
    assert!(
        config_value["mission"].get("run_seed").is_some(),
        "the frozen config's mission carries a run_seed field"
    );
    for forbidden in ["\"target\"", "\"run_seed\"", "\"transcript_digest\""] {
        assert!(
            !projected.as_str().contains(forbidden),
            "the Records view must never publish {forbidden}: the target is the answer, the run \
             seed computes it, and the transcript spells it"
        );
    }
    assert!(view.get("target").is_none());
}

/// The refusal that keeps the seedless mission from being one edit away from a leak: a config
/// whose mission carries a LIVE run seed is refused outright, not rendered with the seed dropped.
///
/// ⚠ This asserts the mutation actually happened before reading the verdict. The precise
/// attribution — that it is the seed gate and not the canonical seal doing the refusing — is
/// `RecordsRuntime.hostile_live_run_seed_config_refused`, which substitutes a fully coherent
/// live config.
#[test]
fn a_config_carrying_a_live_run_seed_is_refused() {
    assert!(
        poa_records_project_available(),
        "dregg_poa_records_project is absent or initialization failed; this is refusal, not skip"
    );

    let config = fixture(CONFIG_FILE);
    let canon = fixture(CANON_FILE);
    let canon_value: Value = serde_json::from_str(canon).expect("frozen Canon is JSON");
    let federation_id = canon_value["federation_id"]
        .as_str()
        .expect("Canon names its federation");

    let sentinel = "0".repeat(64);
    assert!(
        config.contains(&sentinel),
        "the frozen config must carry the all-zero UNBOUND_RUN_SEED sentinel"
    );
    let live = "7".repeat(64);
    let mutated = config.replacen(&sentinel, &live, 1);
    assert_ne!(
        mutated, config,
        "the live-seed substitution must have happened"
    );
    assert!(
        mutated.contains(&live),
        "the mutated config must carry the live seed"
    );

    assert_eq!(
        project(&genesis_only_request(&mutated, canon, federation_id)),
        PoaRecordsVerdict::Rejected
    );
}

#[test]
fn a_non_canonical_genesis_blob_is_refused_not_canonicalized() {
    assert!(
        poa_records_project_available(),
        "dregg_poa_records_project is absent or initialization failed; this is refusal, not skip"
    );

    let config = fixture(CONFIG_FILE);
    let canon = fixture(CANON_FILE);
    let canon_value: Value = serde_json::from_str(canon).expect("frozen Canon is JSON");
    let federation_id = canon_value["federation_id"]
        .as_str()
        .expect("Canon names its federation");

    // One space inside the stored Canon bytes: still valid JSON, not the canonical encoding.
    let loosened = canon.replacen("{\"federation_id\"", "{ \"federation_id\"", 1);
    assert_ne!(loosened, canon);
    assert_eq!(
        project(&genesis_only_request(config, &loosened, federation_id)),
        PoaRecordsVerdict::Rejected
    );

    // An authority that is not the one inside the installed Canon.
    assert_eq!(
        project(&genesis_only_request(config, canon, &"ab".repeat(32))),
        PoaRecordsVerdict::Rejected
    );

    // Uppercase hex for a blob: one spelling only.
    let request = genesis_only_request(config, canon, federation_id);
    assert_eq!(
        project(&request.replace(
            &hex(canon.as_bytes()),
            &hex(canon.as_bytes()).to_uppercase()
        )),
        PoaRecordsVerdict::Rejected
    );
}
