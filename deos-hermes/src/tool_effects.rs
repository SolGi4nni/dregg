//! TOOL SIDE-EFFECTS RIDE THE METERED TURN.
//!
//! In the seam's first slice, [`HermesGateway::admit_call`](crate::HermesGateway::admit_call)
//! carried `work = ∅`: the metered `calls_made : c → c+1` write was the whole
//! turn. The receipt then witnessed only that the call was AUTHORIZED — not WHAT
//! it did. That is real (authority is the load-bearing thing the gate proves),
//! but it leaves the receipt blind to the side-effect.
//!
//! This module closes that: it translates a Hermes tool-call's actual payload
//! into a `Vec<Effect>` that rides the SAME metered turn as the counter advance
//! (the shape `granted_call_carries_tool_work_payload` proves in the SDK e2e).
//! So a committed receipt's `effects_hash` / `emitted_events` now witness the
//! tool's effect — the file path written, the URL fetched — not just the meter.
//!
//! ## What an effect MEANS here
//!
//! The worker cell is deos's confinement cell for this tool class; it is NOT the
//! Hermes process's real filesystem. A `write_file` does not become a syscall —
//! the actual write still happens inside the (eventually sandbox-PD-confined)
//! Hermes process. What rides the turn is a STRUCTURED WITNESS of the intent: an
//! [`Effect::EmitEvent`] whose topic names the tool and whose `data` carries a
//! field-encoded digest of the salient argument (the path, the URL, the command).
//! The receipt thereby binds *what was authorized to happen*, durably and
//! verifiably, into the same commitment as the authorization.
//!
//! Two representative tools are modelled in full (`write_file`, `web_search`);
//! the rest fall back to a generic single-event witness so every tool's receipt
//! still carries its name + a digest of its arguments.

use dregg_cell::CellId;
use dregg_cell::program::field_from_u64;
use dregg_cell::state::FieldElement;
use dregg_turn::Effect;
use dregg_turn::action::{Event, symbol};

use crate::acp::ToolCallRequest;

/// Field-encode up to 8 bytes of a value into one [`FieldElement`] (a cheap,
/// collision-tolerant prefix — this is a WITNESS in the receipt, not a key).
fn pack4(bytes: &[u8]) -> FieldElement {
    let mut v: u64 = 0;
    for (i, b) in bytes.iter().take(8).enumerate() {
        v |= (*b as u64) << (8 * i);
    }
    field_from_u64(v)
}

/// A stable field-digest of a string: FNV-1a over the bytes, as one field. Lets
/// the receipt witness *which* path/URL/command without storing the raw bytes.
fn digest_field(s: &str) -> FieldElement {
    let mut h: u64 = 1469598103934665603;
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(1099511628211);
    }
    field_from_u64(h)
}

/// Build the witness effects a tool-call's payload rides on the metered turn.
///
/// `worker_cell` is the gateway's confinement cell for this call's mandate (the
/// same cell the metered counter lives on). The returned effects are appended
/// AFTER the gateway's `SetField` counter advance, in the one action, so the
/// receipt's `action_count`/`effects_hash`/`emitted_events` witness both the
/// authorization and the side-effect.
///
/// Returns an empty vec only for a call we deliberately treat as pure-metered
/// (never, today — every classified tool emits at least its name+arg digest).
pub fn effects_for_call(call: &ToolCallRequest, worker_cell: CellId) -> Vec<Effect> {
    match call.name.as_str() {
        // A FILE WRITE — the witness binds the target path (a digest) and a
        // length hint of the content, plus a short prefix of the path bytes so a
        // human reading the receipt's event can recognize it.
        "write_file" | "patch" => {
            let path = str_arg(call, &["path", "file_path", "filename"]).unwrap_or_default();
            let content_len = call
                .arguments
                .get("content")
                .and_then(|v| v.as_str())
                .map(|s| s.len() as u64)
                .unwrap_or(0);
            vec![Effect::EmitEvent {
                cell: worker_cell,
                event: Event {
                    topic: symbol("tool.write_file"),
                    data: vec![
                        digest_field(&path),
                        pack4(path.as_bytes()),
                        field_from_u64(content_len),
                    ],
                },
            }]
        }

        // A WEB FETCH — the witness binds the queried URL/query (a digest) so the
        // receipt records *what the agent reached for* over the network.
        "web_search" | "web_extract" | "browser_navigate" => {
            let target = str_arg(call, &["query", "url", "q"]).unwrap_or_default();
            vec![Effect::EmitEvent {
                cell: worker_cell,
                event: Event {
                    topic: symbol(match call.name.as_str() {
                        "web_search" => "tool.web_search",
                        "web_extract" => "tool.web_extract",
                        _ => "tool.browser_navigate",
                    }),
                    data: vec![digest_field(&target), pack4(target.as_bytes())],
                },
            }]
        }

        // A SHELL COMMAND — witness the command digest (so the receipt records
        // which command class ran, even though the exec happens in the Hermes PD).
        "terminal" | "process" | "execute_code" => {
            let cmd = str_arg(call, &["command", "cmd", "code"]).unwrap_or_default();
            vec![Effect::EmitEvent {
                cell: worker_cell,
                event: Event {
                    topic: symbol("tool.terminal"),
                    data: vec![digest_field(&cmd), pack4(cmd.as_bytes())],
                },
            }]
        }

        // A `run_js` HANDS-CALL — witness a digest of the SCRIPT the agent asked
        // to run (topic `tool.run_js`), so the metered accountability turn's
        // receipt binds WHICH script the model submitted, not merely THAT a run_js
        // happened. The script's own affordance fires carry their separate
        // receipts; this pins the program that produced them.
        "run_js" | "run_attached" => {
            let script = str_arg(call, &["script", "code"]).unwrap_or_default();
            run_js_effects(&script, worker_cell)
        }

        // Every other classified tool: a generic witness carrying the tool name's
        // digest + a digest of the whole argument object, so NO authorized call
        // leaves the receipt blind to what it was.
        _ => {
            let args_digest = digest_field(&call.arguments.to_string());
            vec![Effect::EmitEvent {
                cell: worker_cell,
                event: Event {
                    topic: symbol("tool.call"),
                    data: vec![digest_field(&call.name), args_digest],
                },
            }]
        }
    }
}

/// The witness a `run_js` accountability turn rides: an [`Effect::EmitEvent`]
/// (topic `tool.run_js`) binding a stable digest of the EXACT script the runtime
/// evaluated plus its byte length. Distinct scripts produce distinct witnesses, so
/// the metered turn's `emitted_events` (absorbed into the receipt hash) record
/// WHICH script the model ran — closing the blind `Some(vec![])` accountability
/// turn that witnessed only THAT a run_js happened.
///
/// The caller passes the script actually handed to `eval` (which may differ from a
/// placeholder in the wire `ToolCallRequest`), so the receipt binds the real
/// program, not a stand-in.
pub fn run_js_effects(script: &str, worker_cell: CellId) -> Vec<Effect> {
    vec![Effect::EmitEvent {
        cell: worker_cell,
        event: Event {
            topic: symbol("tool.run_js"),
            data: vec![digest_field(script), field_from_u64(script.len() as u64)],
        },
    }]
}

/// Pull the first present string argument among `keys` from the call's args.
fn str_arg(call: &ToolCallRequest, keys: &[&str]) -> Option<String> {
    for k in keys {
        if let Some(s) = call.arguments.get(*k).and_then(|v| v.as_str()) {
            return Some(s.to_string());
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cell() -> CellId {
        CellId::from_bytes([3u8; 32])
    }

    #[test]
    fn write_file_carries_a_path_witness() {
        let call = ToolCallRequest::new(
            "s",
            "tc",
            "write_file",
            serde_json::json!({"path": "src/lib.rs", "content": "hello"}),
        );
        let fx = effects_for_call(&call, cell());
        assert_eq!(fx.len(), 1, "one witness event for the write");
        match &fx[0] {
            Effect::EmitEvent { event, .. } => {
                assert_eq!(event.topic, symbol("tool.write_file"));
                assert_eq!(
                    event.data.len(),
                    3,
                    "path digest + path prefix + content len"
                );
                assert_eq!(event.data[2], field_from_u64(5), "content length witnessed");
            }
            other => panic!("expected an EmitEvent witness, got {other:?}"),
        }
    }

    #[test]
    fn web_search_carries_a_query_witness() {
        let call = ToolCallRequest::new(
            "s",
            "tc",
            "web_search",
            serde_json::json!({"query": "dregg"}),
        );
        let fx = effects_for_call(&call, cell());
        match &fx[0] {
            Effect::EmitEvent { event, .. } => {
                assert_eq!(event.topic, symbol("tool.web_search"));
                assert_eq!(event.data[0], digest_field("dregg"));
            }
            other => panic!("expected the query witness, got {other:?}"),
        }
    }

    #[test]
    fn run_js_call_witnesses_which_script() {
        // The accountability turn for a `run_js` hands-call must bind a digest of
        // the SCRIPT (topic `tool.run_js`) — so the receipt records WHICH program
        // the model ran, not merely THAT a run_js happened. Before this arm existed
        // a `run_js` call fell to the generic `_` witness (topic `tool.call`,
        // data[0] = digest("run_js")), never binding the script.
        let s1 = "deos.world.cells().length";
        let call = ToolCallRequest::new("s", "tc", "run_js", serde_json::json!({ "script": s1 }));
        let fx = effects_for_call(&call, cell());
        assert_eq!(fx.len(), 1, "one witness event for the run_js call");
        match &fx[0] {
            Effect::EmitEvent { event, .. } => {
                assert_eq!(
                    event.topic,
                    symbol("tool.run_js"),
                    "a run_js call witnesses under its OWN topic, not the generic tool.call"
                );
                assert_eq!(
                    event.data[0],
                    digest_field(s1),
                    "the witness binds a digest of the submitted script"
                );
                assert_eq!(
                    event.data[1],
                    field_from_u64(s1.len() as u64),
                    "the witness records the script byte length"
                );
            }
            other => panic!("expected a run_js script witness, got {other:?}"),
        }

        // A DIFFERENT script yields a DIFFERENT witness — the receipt binds which
        // program ran (distinct scripts are distinguishable on the audit tape).
        let s2 = "deos.world.cells()[0].reflect()";
        let call2 = ToolCallRequest::new("s", "tc", "run_js", serde_json::json!({ "script": s2 }));
        let fx2 = effects_for_call(&call2, cell());
        match (&fx[0], &fx2[0]) {
            (Effect::EmitEvent { event: a, .. }, Effect::EmitEvent { event: b, .. }) => {
                assert_ne!(
                    a.data[0], b.data[0],
                    "two different run_js scripts must witness two different digests"
                );
            }
            _ => panic!("expected two run_js witnesses"),
        }
    }

    #[test]
    fn run_js_effects_binds_the_evaluated_script() {
        // `run_js_effects` is the builder `RunJsTool` calls with the EXACT evaluated
        // script (which may differ from the wire ToolCallRequest payload). It binds
        // that script's digest so the metered turn's receipt pins the real program.
        let evaluated = "app.fire('inc', 1)";
        let fx = run_js_effects(evaluated, cell());
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            Effect::EmitEvent { event, .. } => {
                assert_eq!(event.topic, symbol("tool.run_js"));
                assert_eq!(event.data[0], digest_field(evaluated));
            }
            other => panic!("expected the evaluated-script witness, got {other:?}"),
        }
        // Empty vs non-empty scripts are distinguishable (a no-op run is still on tape).
        let empty = run_js_effects("", cell());
        match (&empty[0], &fx[0]) {
            (Effect::EmitEvent { event: a, .. }, Effect::EmitEvent { event: b, .. }) => {
                assert_ne!(
                    a.data[0], b.data[0],
                    "an empty script witnesses distinctly from a real one"
                );
            }
            _ => panic!("expected two run_js witnesses"),
        }
    }

    #[test]
    fn unknown_tool_still_witnessed() {
        let call = ToolCallRequest::new("s", "tc", "todo", serde_json::json!({"x": 1}));
        let fx = effects_for_call(&call, cell());
        assert_eq!(
            fx.len(),
            1,
            "every authorized call witnesses at least name+args"
        );
        match &fx[0] {
            Effect::EmitEvent { event, .. } => assert_eq!(event.topic, symbol("tool.call")),
            other => panic!("expected a generic witness, got {other:?}"),
        }
    }
}
