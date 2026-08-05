//! Native linked probe for the Lean-owned Path of Angels Records read model.
//!
//! It calls the real linked symbol over the frozen live epoch-1 genesis blobs with **no finalized
//! rows** — the state a node is in before its first turn settles — and asserts the emitted view is
//! a real world rather than an empty page: the exact federation, content epoch, curator, world
//! meters and playable mission the ceremony installed.
//!
//! It also asserts the one thing the view must NOT contain. The live config carries the Signal
//! answer (`target`); `POA-RECORDS-OUT-1` has no field for it, and this probe fails if that ever
//! stops being true. That is not a fix for the descriptor, which still publishes the target
//! (`games/signal-triangulation.json`) — it keeps the Records read from becoming a second copy.
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
    assert_eq!(view["format"].as_str(), Some("POA-RECORDS-OUT-1"));

    // The world a run would land in — decoded from the bytes the ceremony installed.
    assert_eq!(view["federation_id"], canon_value["federation_id"]);
    assert_eq!(view["content_root"], canon_value["content_root"]);
    assert_eq!(view["activation_digest"], canon_value["activation_digest"]);
    assert_eq!(view["content_session"], canon_value["content_session"]);
    assert_eq!(view["content_epoch"], canon_value["content_epoch"]);
    assert_eq!(view["curator_key"], canon_value["curator_key"]);
    assert_eq!(view["world"], canon_value["world"]);
    assert_eq!(view["canon_revision"], canon_value["revision"]);

    // The playable mission and its exact reward, not a summary of them.
    assert_eq!(view["mission"], config_value["mission"]);
    assert_eq!(view["reward"], config_value["reward"]);

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

    // The answer is in the config this view was built from and must not be in the view.
    assert!(
        config_value.get("target").is_some(),
        "the frozen live config carries the target"
    );
    assert!(view.get("target").is_none());
    assert!(
        !projected.as_str().contains("\"target\""),
        "the Records view must never republish the Signal target"
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
