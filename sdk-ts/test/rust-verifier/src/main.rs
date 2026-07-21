//! The RUST VERIFIER, driven against TS-produced bytes.
//!
//! The wire differential (`test/wire.test.mjs`) proves the TS SDK's bytes are
//! byte-identical to Rust's. That is necessary but NOT sufficient: it compares
//! an encoder against an encoder. This harness closes the loop by asking the
//! questions that actually matter — **does Rust accept the complete hybrid
//! envelope, and does the real executor accept the enclosed turn?**
//!
//! It decodes with the real `postcard`, `dregg_turn::Turn`, and canonical
//! `dregg_types::{Signature, PublicKey}` wire types. The outer check calls the
//! canonical Rust Ed25519 and ML-DSA verifiers against an independently supplied
//! enrolled key; the inner check is the real `TurnExecutor::execute` entry.
//!
//! Protocol (stdin → stdout, JSON):
//!   in:  { signed_turn_bytes_hex, federation_id_hex, public_key_hex, pq_public_key_hex,
//!          token_id_hex, balance }
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
use dregg_types::{PublicKey, Signature};

/// The exact field sequence of `dregg_sdk::SignedTurn`, expressed only from
/// its canonical dependency types so this tiny fixture does not pull the SDK's
/// prover/Lean production graph into a wire test.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct SignedTurnEnvelope {
    turn: Turn,
    signature: Signature,
    signer: PublicKey,
    #[serde(default)]
    pq_signature: Vec<u8>,
    #[serde(default)]
    pq_signer: Vec<u8>,
}

fn hex_decode(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("valid hex"))
        .collect()
}

fn arr32(v: &[u8]) -> [u8; 32] {
    <[u8; 32]>::try_from(v).expect("expected 32 bytes")
}

fn verify_outer(
    signed: &SignedTurnEnvelope,
    enrolled_ed25519: [u8; 32],
    enrolled_pq: &[u8],
) -> (bool, &'static str) {
    let turn_hash = signed.turn.hash();
    if signed.signer.0 != enrolled_ed25519 {
        return (false, "substituted Ed25519 public key");
    }
    if !signed.signer.verify(&turn_hash, &signed.signature) {
        return (false, "invalid Ed25519 signature");
    }
    let expected_agent =
        dregg_cell::CellId::derive_raw(&enrolled_ed25519, blake3::hash(b"default").as_bytes());
    if signed.turn.agent != expected_agent {
        return (false, "signer does not own turn.agent");
    }
    if signed.pq_signature.is_empty() || signed.pq_signer.is_empty() {
        return (false, "missing outer ML-DSA signature or public key");
    }
    if signed.pq_signer.as_slice() != enrolled_pq {
        return (false, "substituted outer ML-DSA public key");
    }
    if !dregg_turn::pq::ml_dsa_verify(enrolled_pq, &turn_hash, &signed.pq_signature) {
        return (false, "invalid outer ML-DSA signature");
    }
    (true, "hybrid envelope verified")
}

/// Run the REAL executor over `turn` at a given `require_pq` setting.
fn run(
    turn: &Turn,
    fed: [u8; 32],
    cell: &Cell,
    enrolled_pq_public_key: &[u8],
    require_pq: bool,
) -> (bool, String) {
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.local_federation_id = fed;
    // This key arrives as independently provisioned test-fixture state, not by
    // inspecting the action's self-carried `ml_dsa_pk`.  That distinction is
    // the native-PQ identity boundary the real host must preserve.
    executor
        .enroll_pq_identity(
            cell.id(),
            *cell.public_key(),
            cell.state.delegation_epoch(),
            enrolled_pq_public_key.to_vec(),
        )
        .expect("enroll fixture ML-DSA identity");
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
    // This fixture tests TS↔Rust byte/protocol interoperability, not the
    // separately gated Lean verifier installation. Linking the Lean host here
    // would rebuild the entire extracted Mathlib closure for a tiny standalone
    // binary. Opt into dregg-pq's Rust FIPS-204 backend explicitly and locally;
    // the production verifier-core gate remains fail-closed and unchanged.
    unsafe { std::env::set_var("DREGG_ALLOW_UNAUDITED_PQ", "1") };

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

    let signed_turn_bytes = hex_decode(&get("signed_turn_bytes_hex"));
    let fed = arr32(&hex_decode(&get("federation_id_hex")));
    let public_key = arr32(&hex_decode(&get("public_key_hex")));
    let pq_public_key = hex_decode(&get("pq_public_key_hex"));
    let token_id = arr32(&hex_decode(&get("token_id_hex")));
    let balance = req["balance"].as_i64().unwrap_or(1_000_000);

    // (1) Decode the complete envelope with `take_from_bytes`, then require an
    // empty remainder; postcard's convenient `from_bytes` accepts trailing data.
    let signed: SignedTurnEnvelope = match postcard::take_from_bytes(&signed_turn_bytes) {
        Ok((t, [])) => t,
        Ok((_t, trailing)) => {
            println!(
                "{}",
                serde_json::json!({
                    "decoded": false,
                    "decode_error": format!("{} unconsumed trailing bytes", trailing.len())
                })
            );
            return;
        }
        Err(e) => {
            println!(
                "{}",
                serde_json::json!({ "decoded": false, "decode_error": e.to_string() })
            );
            return;
        }
    };

    let roundtrip = postcard::to_stdvec(&signed).expect("re-encode SignedTurn envelope");
    let (outer_ok, outer_why) = verify_outer(&signed, public_key, &pq_public_key);
    let turn = &signed.turn;

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
    let (ok_off, why_off) = if outer_ok {
        run(turn, fed, &cell, &pq_public_key, false)
    } else {
        (false, format!("outer envelope rejected: {outer_why}"))
    };
    let (ok_on, why_on) = if outer_ok {
        run(turn, fed, &cell, &pq_public_key, true)
    } else {
        (false, format!("outer envelope rejected: {outer_why}"))
    };

    println!(
        "{}",
        serde_json::json!({
            "decoded": true,
            "authorization": variant,
            "ed25519_len": ed_len,
            "ml_dsa_len": ml_dsa_len,
            "ml_dsa_pk_len": ml_dsa_pk_len,
            "outer_pq_signature_len": signed.pq_signature.len(),
            "outer_pq_signer_len": signed.pq_signer.len(),
            "outer": { "accepted": outer_ok, "detail": outer_why },
            "roundtrip_hex": roundtrip.iter().map(|b| format!("{b:02x}")).collect::<String>(),
            "turn_hash": turn.hash().iter().map(|b| format!("{b:02x}")).collect::<String>(),
            "agent_cell": cell.id().0.iter().map(|b| format!("{b:02x}")).collect::<String>(),
            "require_pq_off": { "accepted": ok_off, "detail": why_off },
            "require_pq_on": { "accepted": ok_on, "detail": why_on },
        })
    );
}
