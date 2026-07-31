//! **THE PERMANENT CONTROL for the node's MCP verification claims.**
//!
//! Measured 2026-07-30: `dregg_compress_history` folded the node's retained turns,
//! recomputed the VK fingerprint *of the fold it had just produced*, verified against
//! THAT, and reported `"verification": "valid"`. Tooth 1 — the VK pin, whose entire
//! purpose is that the anchor is configuration the verifier held BEFOREHAND — compared a
//! value with itself and **could not fail**. Every caller of the tool was told a proof
//! verified against an anchor that came from the thing under test.
//!
//! A tooth that compares a value with itself is worse than no tooth. The two rules below
//! are what makes the self-anchored case unreachable rather than discouraged, and this
//! file is what keeps them true:
//!
//!   1. the anchor is a REQUIRED caller parameter, refused before any work happens;
//!   2. the `verification` key is written in exactly ONE place, and only when an
//!      anchored verify held.
//!
//! **Why these are testable at all.** The handler's decision points are split into two
//! pure functions (`required_config_anchor`, `compress_history_report`) precisely so the
//! rule can be checked without a node, a ledger, or an hour of recursive proving — i.e.
//! so the control can run on EVERY green pass instead of being a heavyweight integration
//! test someone disables. This campaign has learned that a check which must be remembered
//! gets silently unpointed; ten did, across four lanes.

use serde_json::json;

/// Rule 1: **no anchor, no fold.** The tool must refuse before it does any work, so a
/// caller cannot discover the node's own fingerprint and hand it straight back.
#[test]
fn compress_history_refuses_without_a_caller_supplied_anchor() {
    let params = json!({ "cell_id": "00".repeat(32) });
    let err = dregg_node::mcp::test_hooks::required_config_anchor(&params)
        .expect_err("a missing vk_anchor must be REFUSED, never defaulted or self-minted");

    // The refusal has to teach, or the next caller works around it by passing back a value
    // this node minted — which is the same defect wearing a parameter.
    assert!(
        err.contains("vk_anchor"),
        "the refusal must name the missing parameter, got: {err}"
    );
    assert!(
        err.contains("compare a value with itself"),
        "the refusal must say WHY a self-derived anchor is not an anchor, got: {err}"
    );

    // A malformed anchor is a hard error too — never a silent zero-fill, which would be a
    // real fingerprint an adversary could target.
    for bad in ["dead", &"a".repeat(63), &format!("{}z", "a".repeat(63))] {
        assert!(
            dregg_node::mcp::test_hooks::required_config_anchor(&json!({ "vk_anchor": bad }))
                .is_err(),
            "a malformed anchor ({bad:.8}…) must be refused, never zero-filled"
        );
    }

    // NON-VACUITY: the gate can go green. A gate that cannot pass is not a gate either.
    let good = "ab".repeat(32);
    let parsed = dregg_node::mcp::test_hooks::required_config_anchor(&json!({ "vk_anchor": good }))
        .expect("a well-formed 64-hex anchor is accepted");
    assert_eq!(
        parsed, [0xabu8; 32],
        "the anchor decodes to the caller's bytes"
    );
    // …and the `0x` prefix a human will paste is tolerated rather than mysteriously rejected.
    assert_eq!(
        dregg_node::mcp::test_hooks::required_config_anchor(
            &json!({ "vk_anchor": format!("0x{good}") })
        )
        .expect("an 0x-prefixed anchor parses"),
        [0xabu8; 32]
    );
}

/// Rule 2: **the word "valid" is written in one place, and only when it was earned.**
///
/// This is the assertion that would go RED if someone reintroduced a self-anchored path,
/// because any such path must reach the report through this function with
/// `anchored_verify_held = false` — and then there is no `verification` key to read.
/// Absent is the right shape rather than `"verification": "unverified"`: a consumer doing
/// `result.verification === "valid"` gets `undefined`, which is falsy in every language
/// that reads this JSON, and a consumer that pattern-matches gets nothing to match.
#[test]
fn the_verification_key_exists_only_when_an_anchored_verify_held() {
    let fold = |()| {
        let mut m = serde_json::Map::new();
        m.insert("turns_compressed".into(), json!(3));
        m.insert("proof_size_bytes".into(), json!(4096));
        m
    };

    // (a) The anchored verify HELD — and only then does the claim appear.
    let ok = dregg_node::mcp::test_hooks::compress_history_report(fold(()), "cafe", true);
    assert_eq!(
        ok.get("verification").and_then(|v| v.as_str()),
        Some("valid"),
        "an anchored verify that held must report it"
    );
    assert_eq!(
        ok.get("anchor_source").and_then(|v| v.as_str()),
        Some("caller-supplied config anchor"),
        "the report must name WHERE the anchor came from, so a reader never has to guess"
    );

    // (b) No anchored verify — NO claim. Not a softer word, not a status string a reader
    //     might skim past: the key is simply not there.
    let none = dregg_node::mcp::test_hooks::compress_history_report(fold(()), "cafe", false);
    assert!(
        none.get("verification").is_none(),
        "without an anchored verify there must be NO `verification` key at all — the \
         self-anchored path used to write `\"valid\"` here, and a tooth that compares a \
         value with itself is worse than no tooth. Report: {none}"
    );
    assert!(
        !none.to_string().contains("valid"),
        "no field anywhere in the un-anchored report may read as a verification verdict. \
         Report: {none}"
    );

    // (c) The fold's own summary still rides on both paths — refusing to CLAIM a
    //     verification is not refusing to report what was computed.
    for r in [&ok, &none] {
        assert_eq!(r.get("turns_compressed").and_then(|v| v.as_u64()), Some(3));
        assert_eq!(r.get("compressed").and_then(|v| v.as_bool()), Some(true));
        assert_eq!(r.get("cell_id").and_then(|v| v.as_str()), Some("cafe"));
    }
}

/// The tool CATALOGUE an agent reads must not advertise the retired self-anchored shape,
/// and must state that the anchor is required. An agent plans from `tools/list`, not from
/// the handler source; a description that outruns the handler is the same defect one layer
/// out. (Two neighbouring tools were also advertising retired capabilities — see the
/// `RETIRED (fail-closed)` prefixes.)
#[test]
fn the_tool_catalogue_states_the_anchor_requirement_and_no_retired_capability() {
    let defs = dregg_node::mcp::test_hooks::tool_catalogue();
    let defs = defs.as_array().expect("the catalogue is a list");
    let find = |name: &str| {
        defs.iter()
            .find(|d| d["name"] == name)
            .unwrap_or_else(|| panic!("tool {name} is in the catalogue"))
    };
    let desc = |d: &serde_json::Value| d["description"].as_str().unwrap_or("").to_string();

    let compress = find("dregg_compress_history");
    assert!(
        desc(compress).contains("vk_anchor` is REQUIRED")
            || desc(compress).contains("vk_anchor is REQUIRED"),
        "the catalogue must tell an agent the anchor is required, got: {}",
        desc(compress)
    );
    let required = compress["inputSchema"]["required"]
        .as_array()
        .expect("the schema declares `required`");
    assert!(
        required.iter().any(|v| v == "vk_anchor"),
        "`vk_anchor` must be REQUIRED in the schema, not optional-with-a-default: an \
         optional trust anchor is a self-anchor waiting to happen. Got: {required:?}"
    );

    // The two retired lanes must announce that they are retired, rather than advertising a
    // prove/verify capability whose handler always answers false.
    for name in ["dregg_prove_sovereign_turn", "dregg_verify_sovereign_proof"] {
        let d = find(name);
        assert!(
            desc(d).starts_with("RETIRED"),
            "{name} always fails closed at runtime; the catalogue must say so rather than \
             advertise a capability an agent will plan around. Got: {}",
            desc(d)
        );
    }
}
