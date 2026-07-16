//! The RUST VERIFIER, driven against TS-produced bytes.
//!
//! The wire differential (`test/wire.test.mjs`) proves the TS SDK's bytes are
//! byte-identical to Rust's. That is necessary but NOT sufficient: it compares
//! an encoder against an encoder. This harness closes the loop by asking the
//! question that actually matters — **does the real Rust verifier ACCEPT a turn
//! the TypeScript SDK signed?** — through the genuine public executor entry
//! (`TurnExecutor::execute`), the same call the node makes.
//!
//! It is deliberately NOT a re-implementation of anything: it decodes the TS
//! bytes with the real `postcard` + the real `dregg_turn::Turn` type, seeds a
//! real `Ledger` with a real `Cell`, and runs the real executor at
//! `require_pq` OFF and ON. Nothing here can bless a TS bug: every accept/reject
//! verdict is computed by `dregg-turn` itself.
//!
//! Protocol (stdin → stdout, JSON):
//!   in:  { turn_bytes_hex, federation_id_hex, public_key_hex, token_id_hex, balance }
//!   out: { decoded, require_pq_off: {...}, require_pq_on: {...}, ... }
//!
//! A standalone workspace so it never feature-unifies onto the repo's resolve;
//! `test/hybrid-verify.test.mjs` builds + drives it via `--manifest-path`.

use std::io::Read;

use dregg_cell::cell::Cell;
use dregg_cell::ledger::Ledger;
use dregg_turn::action::Authorization;
use dregg_turn::executor::{ComputronCosts, TurnExecutor};
use dregg_turn::turn::{Turn, TurnResult};

fn hex_decode(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("valid hex"))
        .collect()
}

fn arr32(v: &[u8]) -> [u8; 32] {
    <[u8; 32]>::try_from(v).expect("expected 32 bytes")
}

/// Run the REAL executor over `turn` at a given `require_pq` setting.
fn run(turn: &Turn, fed: [u8; 32], cell: &Cell, require_pq: bool) -> (bool, String) {
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.local_federation_id = fed;
    executor.set_require_pq(require_pq);

    let mut ledger = Ledger::new();
    ledger.insert_cell(cell.clone()).expect("insert agent cell");

    match executor.execute(turn, &mut ledger) {
        TurnResult::Committed { .. } => (true, "committed".to_string()),
        TurnResult::Rejected { reason, at_action } => {
            (false, format!("rejected at {at_action:?}: {reason}"))
        }
        TurnResult::Expired => (false, "expired".to_string()),
        TurnResult::Pending => (false, "pending".to_string()),
    }
}

fn main() {
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .expect("read stdin");
    let req: serde_json::Value = serde_json::from_str(&input).expect("parse request json");

    let get = |k: &str| -> String {
        req[k]
            .as_str()
            .unwrap_or_else(|| panic!("missing field {k}"))
            .to_string()
    };

    let turn_bytes = hex_decode(&get("turn_bytes_hex"));
    let fed = arr32(&hex_decode(&get("federation_id_hex")));
    let public_key = arr32(&hex_decode(&get("public_key_hex")));
    let token_id = arr32(&hex_decode(&get("token_id_hex")));
    let balance = req["balance"].as_i64().unwrap_or(1_000_000);

    // (1) DECODE with the real postcard + the real `dregg_turn::Turn`. A TS
    //     encoder that drifts by even one byte desyncs here (postcard is
    //     positional and non-self-describing) — this alone kills the M30 class.
    let turn: Turn = match postcard::from_bytes(&turn_bytes) {
        Ok(t) => t,
        Err(e) => {
            println!(
                "{}",
                serde_json::json!({ "decoded": false, "decode_error": e.to_string() })
            );
            return;
        }
    };

    // (2) Report the authorization shape the Rust type system actually sees —
    //     so the TS side cannot merely *claim* it emitted a hybrid.
    let auth = &turn.call_forest.roots[0].action.authorization;
    let (variant, ed_len, ml_dsa_len, ml_dsa_pk_len) = match auth {
        Authorization::HybridSignature {
            ed25519,
            ml_dsa,
            ml_dsa_pk,
        } => (
            "HybridSignature",
            ed25519.len(),
            ml_dsa.len(),
            ml_dsa_pk.len(),
        ),
        Authorization::Signature(r, s) => ("Signature", r.len() + s.len(), 0, 0),
        other => (
            match other {
                Authorization::Unchecked => "Unchecked",
                _ => "other",
            },
            0,
            0,
            0,
        ),
    };

    let cell = Cell::with_balance(public_key, token_id, balance);

    // (3) THE GATE: the real executor, at require_pq OFF (today's node) and ON
    //     (the post-flip node). A hybrid-signed TS turn must be accepted by BOTH.
    let (ok_off, why_off) = run(&turn, fed, &cell, false);
    let (ok_on, why_on) = run(&turn, fed, &cell, true);

    println!(
        "{}",
        serde_json::json!({
            "decoded": true,
            "authorization": variant,
            "ed25519_len": ed_len,
            "ml_dsa_len": ml_dsa_len,
            "ml_dsa_pk_len": ml_dsa_pk_len,
            "turn_hash": turn.hash().iter().map(|b| format!("{b:02x}")).collect::<String>(),
            "agent_cell": cell.id().0.iter().map(|b| format!("{b:02x}")).collect::<String>(),
            "require_pq_off": { "accepted": ok_off, "detail": why_off },
            "require_pq_on": { "accepted": ok_on, "detail": why_on },
        })
    );
}
