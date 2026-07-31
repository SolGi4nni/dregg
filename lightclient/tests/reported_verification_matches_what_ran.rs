//! **THE PERMANENT FALSIFIERS for "a surface reports a verification that did not happen".**
//!
//! Measured 2026-07-30 by a consumer audit: three live surfaces reported a verification
//! stronger than the one they ran. Two of the three are covered here; the third (the node's
//! MCP self-anchored verify) is covered by `node/tests/mcp_verification_claims_are_earned.rs`.
//!
//! **Why this file lives in `lightclient/` and not next to the code it guards.** The wire
//! envelope and the light-client bindings used to live in `wasm/`, which is EXCLUDED from the
//! workspace (`Cargo.toml`'s `exclude` list). A `#[cfg(test)]` guard there never ran in a
//! `cargo test --workspace` green pass — an unguarded wire format with the appearance of a
//! guarded one. `dregg-lightclient` is a member, so everything below runs whenever the
//! workspace does.
//!
//! **Why they are controls and not injections.** This campaign has learned that a fault an
//! operator must remember to inject gets silently unpointed — ten did, across four lanes.
//! Every assertion here is evaluated on every green pass, against the real artifact and the
//! real published page, and goes RED the moment the check it guards stops happening.

use dregg_lightclient::external_envelope::{
    EXTERNAL_HISTORY_ENVELOPE_VERSION, ExternalHistoryEnvelope,
};

/// The repo root, from this crate's manifest dir.
fn repo_root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("lightclient/ has a parent")
        .to_path_buf()
}

/// **FALSIFIER 1 — the envelope may carry ONLY values a verify consumes.**
///
/// Through v1 the envelope also carried `genesis_root` / `final_root` / `chain_digest` /
/// `num_turns`. None was ever an argument to a verify: the verify path passes only
/// `proof_bytes_b64` to `verify_history_bytes`, and the publics tooth 2 re-attests are the
/// INNER `WholeChainProofBytes` copy — never compared to the outer one. Any reader of the
/// JSON that was not the wasm success path (an indexer, a relay, a pre-verify summary, the
/// verifier's own refusal arms) was reading unbound producer input and presenting it as a
/// fact about a history.
///
/// This goes RED if anyone re-adds a carried field, i.e. exactly when the defect returns.
#[test]
fn the_wire_envelope_carries_only_values_a_verify_consumes() {
    let env = ExternalHistoryEnvelope::new("ab".repeat(32), "Zm9v".to_string());
    let json = serde_json::to_string(&env).expect("the envelope serializes");
    let map: serde_json::Map<String, serde_json::Value> =
        serde_json::from_str(&json).expect("the envelope is a JSON object");

    let mut keys: Vec<&str> = map.keys().map(String::as_str).collect();
    keys.sort_unstable();
    assert_eq!(
        keys,
        vec![
            "finality_cert",
            "proof_bytes_b64",
            "version",
            "vk_fingerprint_hex",
        ],
        "THE ENVELOPE GREW A FIELD. Every value on this wire must be an argument to a \
         verify. `genesis_root` / `final_root` / `chain_digest` / `num_turns` were carried \
         and checked against NOTHING — a producer could set them to anything and any reader \
         that was not the success path rendered them as fact. If you are adding a field, \
         first make it an argument to `verify_history_bytes`; if you cannot, it does not \
         belong on the wire. Got: {keys:?}"
    );
}

/// **FALSIFIER 2 — the deleted shape must REFUSE TO LOAD, not be silently reinterpreted.**
///
/// Deleting a field from a Rust struct is not enough on its own: a permissive serde would
/// keep parsing every old artifact with the unbound publics quietly dropped, which is the
/// "reinterpret rather than refuse" failure the project doctrine names. `deny_unknown_fields`
/// plus the version pin make it a hard refusal, twice over.
#[test]
fn a_v1_artifact_carrying_the_deleted_publics_refuses_to_load() {
    let v1 = r#"{"version":1,"vk_fingerprint_hex":"00","proof_bytes_b64":"",
        "genesis_root":[1,2,3],"final_root":[4,5,6],"chain_digest":[7],"num_turns":9}"#;
    let err = serde_json::from_str::<ExternalHistoryEnvelope>(v1).expect_err(
        "a v1 artifact carrying the four deleted publics must REFUSE to parse — reading it \
         with them silently dropped is exactly the reinterpretation the v2 bump exists to \
         prevent",
    );
    assert!(
        err.to_string().contains("unknown field"),
        "the refusal must name the unknown field so a stale artifact is diagnosable, got: {err}"
    );

    // And a well-formed envelope at the WRONG version is refused by name, with the flag day
    // spelled out rather than left as a mystery.
    let mut wrong = ExternalHistoryEnvelope::new("ab".repeat(32), String::new());
    wrong.version = EXTERNAL_HISTORY_ENVELOPE_VERSION - 1;
    let msg = wrong
        .check_version()
        .expect_err("an old version must be refused");
    assert!(
        msg.contains("never checked") && msg.contains("Re-emit"),
        "the version refusal must say WHAT changed and what to do, got: {msg}"
    );
    assert!(
        ExternalHistoryEnvelope::new(String::new(), String::new())
            .check_version()
            .is_ok(),
        "the current version must pass — a gate that cannot go green is not a gate either"
    );
}

/// **FALSIFIER 3 — the published light-client page may not claim more than it runs.**
///
/// The page at `site/light-client/` is outward-facing. Measured 2026-07-30: its
/// `history.json` served the trust anchor byte-identical to `envelope.vk_fingerprint_hex`,
/// in the same fetch as the proof, while the page rendered a ✓ over it. The verifier's
/// anchor discipline is real; the demo did not exercise it, and the copy did not say so.
///
/// Each assertion below is a claim the page MADE and the code did not support, or a
/// disclosure that must not quietly disappear the next time someone edits the copy. This
/// reads the real committed file — no fixture, no mock.
#[test]
fn the_published_light_client_page_states_its_anchor_provenance() {
    let path = repo_root().join("site/light-client/index.html");
    let page = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the published page must be readable at {path:?}: {e}"));

    // (a) THE BARE `attested` BIT IS GONE from the consumer. It was `true` for a legs-1+2
    //     verify and a legs-1+2+3 verify alike, so a page branching on it could not tell a
    //     correctly-proven fork from a quorum-ratified head.
    assert!(
        !page.contains("view.attested") && !page.contains("verdict.attested"),
        "the page must branch on a PER-LEG flag: `attested` was one bit meaning two \
         different verdicts, and the difference lived only in free text"
    );
    assert!(
        page.contains("aggregate_attested") && page.contains("finality_attested"),
        "both legs must be rendered — whether finality was checked is not a footnote"
    );

    // (b) THE ANCHOR'S PROVENANCE IS PRINTED WITH EVERY VERDICT. The served anchor is not a
    //     trust decision and the page must never let a ✓ be read as one.
    assert!(
        page.contains("provenanceOf"),
        "every verdict must carry the provenance of the anchor it was checked against"
    );
    assert!(
        page.contains("anchor provenance: SERVED BY US"),
        "when the anchor came from our own history.json, the verdict must SAY so"
    );

    // (c) AN OUT-OF-BAND PATH EXISTS. The claim "the anchor is a separate input" becomes
    //     true for a visitor who supplies one; the page must offer that, not only apologise.
    assert!(
        page.contains("urlAnchor") && page.contains("'anchor'"),
        "the page must accept a visitor-supplied `?anchor=` the producer does not control"
    );

    // (d) THE PAGE MUST NOT RENDER THE ENVELOPE'S PUBLICS. It used to print the carried
    //     genesis/final root, chain digest and turn count into a summary BEFORE any verify
    //     ran, off fields no verify ever read. Those fields are gone from the wire; a page
    //     reaching for them again is reaching for producer input.
    for field in [
        "e.genesis_root",
        "e.final_root",
        "e.chain_digest",
        "e.num_turns",
    ] {
        assert!(
            !page.contains(field),
            "the page reads `{field}` off the served envelope. Numbers about a history may \
             only be rendered from a VERIFIED verdict, never from the wrapper."
        );
    }

    // (e) THE HONEST DISCLOSURE MUST SURVIVE COPY EDITS. This is the sentence a future
    //     rewrite is most likely to smooth away.
    assert!(
        page.contains("we handed you both halves"),
        "the page must keep disclosing that the anchor and the proof arrive together"
    );
    assert!(
        !page.contains("config anchor you control"),
        "the meta description claimed an anchor the visitor controls; by default they do not"
    );
}

/// **FALSIFIER 4 — the baked artifact must match the wire format the verifier speaks.**
///
/// The committed `site/light-client/history.json` is what the published page fetches. If the
/// envelope format moves and the artifact does not, the page ships a demo the visitor's tab
/// refuses — and (the reason this is a test and not a deploy check) the mismatch is invisible
/// to everyone who does not open the page.
///
/// This is a SHAPE check, deliberately: it does not fold or verify a proof (that needs the
/// wasm bundle and lives in `scripts/check-web-surface-teeth.sh`). It catches the cheap,
/// silent half — a stale wrapper — on every green pass.
#[test]
fn the_baked_site_artifact_speaks_the_current_envelope_format() {
    let path = repo_root().join("site/light-client/history.json");
    let raw = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the baked artifact must be readable at {path:?}: {e}"));
    let baked: serde_json::Value =
        serde_json::from_str(&raw).expect("the baked artifact is valid JSON");

    let env_json = baked
        .get("envelope")
        .expect("the baked artifact carries an `envelope`");
    let env: ExternalHistoryEnvelope =
        serde_json::from_value(env_json.clone()).unwrap_or_else(|e| {
            panic!(
                "the baked `site/light-client/history.json` does NOT parse as the current wire \
             envelope: {e}\n\nRegenerate it from the repo root:\n  cargo run --release -p \
             dregg-lightclient --bin produce_history_envelope --features prover -- 3 7 > \
             site/light-client/history.json\n\nThis is a REBUILD, not a migration: no VK \
             rotation and no re-proving are involved."
            )
        });
    env.check_version()
        .unwrap_or_else(|e| panic!("the baked artifact is a stale envelope version: {e}"));
    assert!(
        !env.proof_bytes_b64.is_empty(),
        "the baked artifact must carry proof bytes — an empty envelope verifies nothing"
    );

    // ⚑ THE ANCHOR CO-LOCATION IS DISCLOSED IN THE ARTIFACT ITSELF, not only on the page
    // that happens to render it. Measured 2026-07-30: `anchor_hex` is byte-identical to
    // `envelope.vk_fingerprint_hex`, because the producer minted both from the same fold.
    // That is honest for a demo and dishonest if unlabelled — an indexer or a second page
    // consuming this file would otherwise read `anchor_hex` as an independent config value.
    let anchor = baked
        .get("anchor_hex")
        .and_then(|v| v.as_str())
        .expect("the baked artifact carries an `anchor_hex`");
    if anchor.eq_ignore_ascii_case(&env.vk_fingerprint_hex) {
        let prov = baked
            .get("anchor_provenance")
            .and_then(|v| v.as_str())
            .unwrap_or("");
        assert!(
            prov.contains("SERVED BY THE PRODUCER"),
            "`anchor_hex` is byte-identical to the envelope's own claimed fingerprint, so \
             this artifact CANNOT demonstrate anchor discipline — only that the verifier \
             enforces whatever anchor it is handed. When the two are equal the artifact \
             must carry an `anchor_provenance` saying so, so that a reader who never sees \
             the page cannot mistake it for an independently held config anchor. \
             Regenerate with the `produce_history_envelope` bin, which emits it."
        );
    }
}
