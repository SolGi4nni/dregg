//! # THE sdk-py DRIFT-KILLER — the Python SDK driven against the REAL protocol.
//!
//! `sdk-py` is in the root workspace's `exclude` list, so NO normal build and NO
//! CI ever compiled it against the protocol it claims to speak. This file is the
//! gate that makes that silence impossible: it drives the SHIPPED signing path
//! (`dregg::build_signed_turn` — the exact function `TurnBuilder.sign()` calls)
//! through the REAL `TurnExecutor`, and it reads the REAL protocol source at test
//! time to catch vocabulary drift.
//!
//! ## THE ORACLE, AND WHY IT CANNOT GO STALE
//!
//! The M30 lesson (sdk-ts shipped "byte-faithful: yes" to npm while silently
//! dropping `CapabilityRef::provenance`) is that a differential whose oracle is a
//! CHECKED-IN or GITIGNORED artifact silently passes forever once the artifact
//! rots. This gate has no such artifact. Its two oracles are both built fresh on
//! every `cargo test`:
//!
//! 1. **The encoder oracle is the protocol itself.** sdk-py does not reimplement
//!    the codec (as sdk-ts must, in TypeScript) — it depends on `dregg-turn` /
//!    `dregg-cell` by PATH and encodes with the same `postcard` the node decodes
//!    with. Cargo recompiles those crates from source here, so the bytes under
//!    test ARE the protocol's bytes. There is no second implementation to drift.
//!    What that buys is real but NARROW: it makes mis-encoding impossible, and
//!    proves nothing about whether the turn is ACCEPTED. So the gate does not
//!    stop at bytes — it commits the turn through the executor.
//!
//! 2. **The vocabulary oracle is `../turn/src/action.rs`, parsed at test time.**
//!    [`effect_variants_from_protocol_source`] reads the file and PANICS if it is
//!    missing, unreadable, or no longer contains `pub enum Effect {`. A protocol
//!    that grows a variant turns this gate RED and forces a decision. It cannot
//!    silently pass: there is no cached copy to fall back to.
//!
//! Run: `cd sdk-py && cargo test` (sdk-py is excluded from the root workspace —
//! it must be built from ITS OWN directory or it is not built at all).

use dregg::build_signed_turn;
use dregg_cell::{Cell, Ledger};
use dregg_sdk::cipherclerk::AgentCipherclerk;
use dregg_turn::action::{Authorization, Effect};
use dregg_turn::{ComputronCosts, TurnExecutor, TurnResult};

const FED: [u8; 32] = [7u8; 32];
const HORIZON: i64 = 1 << 40; // far-future validity; these tests are not clock tests

/// A ledger holding the clerk's agent cell (funded) plus a destination cell.
fn setup(clerk: &AgentCipherclerk, balance: i64) -> (Ledger, dregg_types::CellId) {
    // The agent cell MUST be the one sdk-py acts as: `cell_id("default")` =
    // derive_raw(pubkey, blake3("default")), so its token_id is blake3("default").
    let token_id = *blake3::hash(b"default").as_bytes();
    let agent = Cell::with_balance(clerk.public_key().0, token_id, balance);
    assert_eq!(
        agent.id(),
        clerk.cell_id("default"),
        "test setup: the funded cell must BE the cell sdk-py acts as"
    );
    let dest = Cell::with_balance([42u8; 32], token_id, 0);
    let dest_id = dest.id();
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(agent);
    let _ = ledger.insert_cell(dest);
    (ledger, dest_id)
}

/// Build a turn the way `TurnBuilder.sign()` does, for the given live nonce.
fn sdk_py_turn(
    clerk: &AgentCipherclerk,
    effects: Vec<Effect>,
    nonce: u64,
) -> dregg_sdk::cipherclerk::SignedTurn {
    build_signed_turn(
        clerk, "default", "execute", effects, &FED, nonce, 0, None, HORIZON,
    )
}

// ─── 1. THE COMMIT GATE: the shipped signing path must produce turns the real
//        executor ACCEPTS — at nonce 0 AND after the agent's nonce advances. ───

/// THE REGRESSION THIS FILE EXISTS FOR.
///
/// `TurnBuilder.sign()` fetches the agent's LIVE nonce from the node and stamps
/// it on the turn. It used to build the action with
/// `AgentCipherclerk::make_action`, which binds the action signature to
/// `next_turn_nonce()` = `receipt_chain.len()` — and sdk-py NEVER appends to the
/// receipt chain, so that was ALWAYS 0, whatever the turn actually carried.
/// Since `dregg-action-sig-v3` the executor recomputes the signing message over
/// `turn.nonce` (`TurnExecutor::compute_signing_message`), so the moment an
/// agent's on-ledger nonce left 0 — i.e. from its SECOND turn onward, forever —
/// every Python-signed turn was refused. A Python identity could submit exactly
/// one turn in its life.
///
/// CANARY: revert `build_signed_turn` to `clerk.make_action(target, method,
/// effects, &fed)` + `turn.nonce = nonce` and the `nonce == 1` leg goes RED
/// (`Rejected`), while the `nonce == 0` leg stays green — which is precisely why
/// a smoke test that submits one turn never caught this.
#[test]
fn shipped_signing_path_commits_at_every_nonce_not_just_the_first() {
    let clerk = AgentCipherclerk::new();
    let (mut ledger, dest) = setup(&clerk, 1_000);
    let agent_id = clerk.cell_id("default");

    for turn_no in 0..4u64 {
        // A FRESH executor per turn over a PERSISTENT ledger — the deployed
        // node's exact shape: `post_submit_signed_turn` calls
        // `executor_setup::new_submit_executor(&s)` per request, so the
        // executor-local `last_receipt_hash` map starts empty every submit
        // (which is why sdk-py's always-`None` `previous_receipt_hash` is
        // accepted in production — see the residual noted in the SDK's README).
        // The agent's NONCE, by contrast, lives in the LEDGER and persists
        // across turns — which is exactly what made the nonce bind fatal.
        let mut executor = TurnExecutor::new(ComputronCosts::zero());
        // The executor recomputes the signing message over ITS federation id —
        // the same one `.turn(federation_id=…)` pins / `.sign()` fetches.
        executor.set_local_federation_id(FED);

        // What `.sign()` does: fetch the agent's LIVE nonce and stamp it.
        let live_nonce = ledger
            .get(&agent_id)
            .expect("agent cell present")
            .state
            .nonce();
        assert_eq!(
            live_nonce, turn_no,
            "each committed turn advances the agent's on-ledger nonce"
        );

        let signed = sdk_py_turn(
            &clerk,
            vec![Effect::Transfer {
                from: agent_id,
                to: dest,
                amount: 1,
            }],
            live_nonce,
        );

        match executor.execute(&signed.turn, &mut ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!(
                "turn #{turn_no} (live nonce {live_nonce}) built by the SHIPPED sdk-py signing \
                 path must COMMIT through the real executor, got {other:?}\n\n\
                 InvalidAuthorization here ⇒ the action signature is bound to \
                 `next_turn_nonce()` (always 0 in sdk-py — it never appends receipts) rather than \
                 the nonce the turn carries."
            ),
        }
    }
}

/// THE WIDE EXT PLANE. `Effect::SetField { index }` routes on the executor side:
/// `index < STATE_SLOTS` (16) writes the fixed cell array, `index >= 16` lands in
/// the committed `fields_map` under an UNBOUNDED key (`CellState::set_field_ext`).
/// sdk-py's `.write(index, value)` takes a plain `usize` and stages it verbatim,
/// baking in NO 16-slot assumption, so the wide plane should already work from
/// Python.
///
/// SCOPE, stated honestly: this DRIVES that a turn carrying a wide `SetField`,
/// signed by the SHIPPED signing path, commits through the real executor and
/// lands in the committed `fields_map`. It does NOT drive `write()`'s own body —
/// that is a `#[pymethods]` fn no Rust test can call, and its only logic is the
/// value coercion plus an unclamped `index` pass-through (lib.rs `fn write`).
/// That there is no clamp is established by READING it, not by this test; a
/// clamp introduced inside `write()` would not turn this leg red. What this leg
/// does guarantee is that if the PROTOCOL ever stopped admitting unbounded keys,
/// the Python `.write(index)` signature would be a lie and this goes RED.
#[test]
fn python_write_reaches_the_wide_ext_plane_beyond_the_16_fixed_slots() {
    const WIDE_KEY: u64 = 4_242; // far past STATE_SLOTS = 16
    let clerk = AgentCipherclerk::new();
    let (mut ledger, _dest) = setup(&clerk, 1_000);
    let agent_id = clerk.cell_id("default");

    let fields_root_before = ledger.get(&agent_id).expect("agent cell").state.fields_root;

    let signed = sdk_py_turn(
        &clerk,
        vec![Effect::SetField {
            cell: agent_id,
            index: WIDE_KEY as usize,
            value: dregg_cell::field_from_u64(99),
        }],
        0,
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(FED);
    match executor.execute(&signed.turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        other => panic!(
            "a Python `.write({WIDE_KEY}, 99)` must COMMIT — the wide ext plane takes unbounded \
             keys and sdk-py must not model a 16-slot ceiling. Got {other:?}"
        ),
    }

    let state = &ledger.get(&agent_id).expect("agent cell").state;
    assert_eq!(
        state.get_field_ext(WIDE_KEY),
        Some(dregg_cell::field_from_u64(99)),
        "the wide write must be readable at its unbounded key"
    );
    assert!(
        state.fields_map.contains_key(&WIDE_KEY),
        "a key >= STATE_SLOTS must land in the committed fields_map, not the fixed array"
    );
    assert_ne!(
        state.fields_root, fields_root_before,
        "the committed fields_root must ADVANCE to cover the wide write — otherwise the write is \
         invisible to the commitment and no light client could witness it"
    );
}

// ─── 2. THE PQ PERIMETER: the Python SDK must sign the hybrid shape. ───

/// The Rust default action signer is `Authorization::HybridSignature` (ed25519 +
/// ML-DSA-65/FIPS-204). sdk-ts signs CLASSICAL only, so no TS-signed turn is
/// byte-identical to a Rust-signed one; the day a node flips `require_pq`, every
/// classical SDK drops offline. sdk-py rides the Rust signer, so it gets the PQ
/// half for free — this pins that it actually does, at BOTH levels (the action
/// authorization and the turn envelope), and that both halves VERIFY rather than
/// merely being present-and-nonempty.
#[test]
fn python_signed_turns_carry_a_verifying_hybrid_pq_perimeter() {
    let clerk = AgentCipherclerk::new();
    let agent_id = clerk.cell_id("default");
    let (_ledger, dest) = setup(&clerk, 1_000);
    let signed = sdk_py_turn(
        &clerk,
        vec![Effect::Transfer {
            from: agent_id,
            to: dest,
            amount: 1,
        }],
        0,
    );

    // (a) The ACTION authorization is the hybrid variant, and its PQ half
    //     verifies over the canonical signing message the executor recomputes.
    let action = &signed.turn.call_forest.roots[0].action;
    let (ed25519, ml_dsa, ml_dsa_pk) = match &action.authorization {
        Authorization::HybridSignature {
            ed25519,
            ml_dsa,
            ml_dsa_pk,
        } => (*ed25519, ml_dsa.clone(), ml_dsa_pk.clone()),
        other => panic!(
            "the Python SDK must sign actions with Authorization::HybridSignature (the Rust \
             default since the client-turn hybrid perimeter closed), got {other:?}"
        ),
    };
    let unsigned = dregg_turn::action::Action {
        authorization: Authorization::Unchecked,
        ..action.clone()
    };
    let msg = TurnExecutor::compute_signing_message(&unsigned, &FED, signed.turn.nonce);
    assert!(
        clerk
            .public_key()
            .verify(&msg, &dregg_sdk::Signature(ed25519)),
        "the classical half must verify over the message the executor recomputes"
    );
    assert_eq!(ml_dsa_pk.len(), dregg_turn::pq::ML_DSA_PK_LEN);
    assert!(
        dregg_turn::pq::ml_dsa_verify(&ml_dsa_pk, &msg, &ml_dsa),
        "the ML-DSA-65 half must verify over the SAME message"
    );
    // Fail-closed: a forged PQ half must not verify.
    let mut forged = ml_dsa.clone();
    forged[0] ^= 0xff;
    assert!(!dregg_turn::pq::ml_dsa_verify(&ml_dsa_pk, &msg, &forged));

    // (b) The TURN envelope carries its own verifying PQ half.
    let h = signed.turn.hash();
    assert!(signed.signer.verify(&h, &signed.signature));
    assert_eq!(signed.pq_signer.len(), dregg_turn::pq::ML_DSA_PK_LEN);
    assert!(
        dregg_turn::pq::ml_dsa_verify(&signed.pq_signer, &h, &signed.pq_signature),
        "the turn envelope's ML-DSA-65 half must verify over the turn hash"
    );
}

// ─── 3. PROVENANCE ON THE WIRE (the M30 hole, checked on the Python side). ───

/// `CapabilityRef::provenance` is `#[serde(default)]` with NO
/// `skip_serializing_if`, so postcard EMITS its 32 bytes positionally. sdk-ts
/// dropped the field and shipped "byte-faithful: yes" to npm; a decoder reading
/// a TS-encoded cap therefore slid 32 bytes off. This pins that the Python SDK's
/// `.grant()` (a) puts the CANONICAL mint-rooted provenance on the cap — the
/// same derivation `Clist::grant_with_breadstuff` uses — and (b) that it
/// SURVIVES the postcard round-trip the node decodes.
#[test]
fn grant_provenance_is_canonical_and_survives_the_wire() {
    let clerk = AgentCipherclerk::new();
    let target = clerk.cell_id("default");
    let slot = 3u32;

    // The canonical derivation, computed independently from cell/src/derivation.rs
    // (parent = mint root for a context-free grant; turn context = NO_TURN_CONTEXT).
    let expected = dregg_cell::derivation::cap_provenance(
        &target,
        slot,
        &dregg_cell::derivation::mint_provenance(),
        &[0u8; 32],
    );
    assert_ne!(
        expected, [0u8; 32],
        "a canonical provenance is never the legacy/unprovenanced sentinel"
    );

    // Drive the SHIPPED construction (`TurnBuilder.grant()`'s own `mint_cap_ref`),
    // NOT a cap this test builds — a self-built cap would verify only itself and
    // stay green while `grant()` dropped the field.
    let cap = dregg::mint_cap_ref(target, slot, dregg_cell::AuthRequired::Signature, None);
    assert_eq!(
        cap.provenance, expected,
        "the SHIPPED grant path must stamp the canonical mint-rooted provenance"
    );
    let bytes = postcard::to_stdvec(&cap).expect("encode cap");
    let back: dregg_cell::CapabilityRef = postcard::from_bytes(&bytes).expect("decode cap");
    assert_eq!(
        back.provenance, expected,
        "provenance must survive the postcard round-trip the node decodes (the M30 hole)"
    );
    // The 32 provenance bytes are physically on the wire — a dropped field would
    // shorten the encoding and slide every subsequent field.
    let without = postcard::to_stdvec(&dregg_cell::CapabilityRef {
        provenance: [0u8; 32],
        ..cap.clone()
    })
    .expect("encode cap w/ sentinel provenance");
    assert_eq!(
        bytes.len(),
        without.len(),
        "provenance is a fixed-width 32-byte positional field"
    );
    assert!(
        bytes.windows(32).any(|w| w == expected),
        "the canonical provenance bytes must appear verbatim in the postcard encoding"
    );
}

// ─── 4. THE VOCABULARY GATE: fails LOUD when the protocol grows a verb. ───

/// The ordered `pub enum Effect` variant names read FRESH from the protocol
/// source at test time. Panics (never silently returns a stale/empty set) if the
/// file is missing or its shape changed — this is the anti-M30 property: there is
/// no cached oracle that can rot into a false green.
fn effect_variants_from_protocol_source() -> Vec<String> {
    effect_variants_at(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../turn/src/action.rs"
    ))
}

/// The oracle read, parameterized by path so the FAIL-LOUD property itself is
/// testable (see `oracle_fails_loud_*`) without touching the shared protocol
/// tree — renaming `turn/src/action.rs` to prove a point would break every other
/// crate in the workspace.
fn effect_variants_at(path: &str) -> Vec<String> {
    let src = std::fs::read_to_string(path).unwrap_or_else(|e| {
        panic!(
            "DRIFT-KILLER ORACLE MISSING: cannot read the protocol source at {path}: {e}\n\
             This gate reads `pub enum Effect` from the REAL protocol at test time. It has no \
             cached copy on purpose — an oracle that can go missing must FAIL, never pass."
        )
    });
    let start = src.find("pub enum Effect {").unwrap_or_else(|| {
        panic!(
            "DRIFT-KILLER ORACLE STALE: `pub enum Effect {{` no longer exists in {path} — the \
             protocol's effect vocabulary moved or was renamed. Re-point this gate; do NOT delete \
             it."
        )
    });
    let body = &src[start..];
    let bytes = body.as_bytes();
    let (mut variants, mut depth, mut expecting, mut i) = (Vec::new(), 0i32, false, 0usize);
    while i < bytes.len() {
        match bytes[i] {
            b'{' => {
                depth += 1;
                if depth == 1 {
                    expecting = true;
                }
                i += 1;
            }
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
                if depth == 1 {
                    expecting = true;
                }
                i += 1;
            }
            b',' if depth == 1 => {
                expecting = true;
                i += 1;
            }
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'#' if depth == 1 => {
                // skip a bracket-balanced attribute
                let mut bd = 0i32;
                while i < bytes.len() {
                    match bytes[i] {
                        b'[' => bd += 1,
                        b']' => {
                            bd -= 1;
                            if bd == 0 {
                                i += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    i += 1;
                }
            }
            c if expecting && c.is_ascii_uppercase() => {
                let s = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                variants.push(body[s..i].to_string());
                expecting = false;
            }
            _ => i += 1,
        }
    }
    assert!(
        variants.len() > 20,
        "DRIFT-KILLER ORACLE BROKEN: parsed only {} Effect variants from the protocol source — the \
         parser lost the enum. Fix the gate; a gate that parses nothing passes everything.",
        variants.len()
    );
    variants
}

/// THE M30 PROPERTY, DRIVEN. sdk-ts's "drift killer" was fooled because its
/// oracle was an untracked artifact that stopped being rebuilt: once it went
/// missing, the differential silently passed forever and a provenance-dropping
/// encoder shipped to npm under a green check. This gate's oracle is the
/// protocol SOURCE, and these two tests prove it cannot degrade into a false
/// green: a missing oracle PANICS, and an oracle whose shape moved PANICS.
/// Neither returns an empty set that would vacuously satisfy every subset check.
#[test]
fn oracle_fails_loud_when_the_protocol_source_is_missing() {
    let missing = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../turn/src/NOT-A-REAL-FILE.rs"
    );
    let panicked = std::panic::catch_unwind(|| effect_variants_at(missing));
    let err = panicked.expect_err(
        "a MISSING oracle must PANIC, never return a set — an oracle that can vanish quietly is \
         exactly the M30 hole (a differential whose oracle rots passes forever)",
    );
    let msg = err
        .downcast_ref::<String>()
        .cloned()
        .unwrap_or_else(|| "<non-string panic>".into());
    assert!(
        msg.contains("DRIFT-KILLER ORACLE MISSING"),
        "the failure must NAME itself as a missing oracle so nobody mistakes it for a flake, got: \
         {msg}"
    );
}

#[test]
fn oracle_fails_loud_when_the_protocol_shape_moved() {
    // A real, readable file that is NOT the effect vocabulary: the oracle must
    // refuse it rather than parse zero variants and pass everything.
    let wrong = concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml");
    let panicked = std::panic::catch_unwind(|| effect_variants_at(wrong));
    let err = panicked.expect_err("an oracle that cannot find `pub enum Effect` must PANIC");
    let msg = err
        .downcast_ref::<String>()
        .cloned()
        .unwrap_or_else(|| "<non-string panic>".into());
    assert!(
        msg.contains("DRIFT-KILLER ORACLE STALE"),
        "the failure must NAME itself as a stale oracle, got: {msg}"
    );
}

/// sdk-py's `TurnBuilder` exposes a deliberate SUBSET of the protocol's effect
/// vocabulary. That is a defensible scope — a light, kernel-free client cannot
/// mint most of these — but it must be an EXPLICIT subset, not an accident.
///
/// This gate pins the subset sdk-py builds, and pins the rest as consciously
/// unbuilt. When the protocol appends a verb (e.g. `Effect::Custom`, the
/// Custom-VK door), this test goes RED and someone must decide which list it
/// joins. Nothing about a new verb can pass unnoticed.
#[test]
fn effect_vocabulary_is_an_explicit_subset_not_an_accident() {
    let protocol = effect_variants_from_protocol_source();

    // What sdk-py's TurnBuilder actually stages today (lib.rs: transfer /
    // transfer_from / write / write_u64 / grant / increment_nonce).
    let built: &[&str] = &["SetField", "Transfer", "GrantCapability", "IncrementNonce"];

    // Every verb sdk-py does NOT build, and why it is out of the light client's
    // reach. Keeping the reasons HERE (not in prose that drifts) is what makes
    // the subset a decision rather than a gap.
    let unbuilt: &[&str] = &[
        // Needs a proof the light client cannot produce (no prover in the wheel).
        "NoteSpend",
        "NoteCreate",
        "ShieldedTransfer",
        // Custom-VK door: the executor REFUSES this outside a proof-carrying
        // sovereign turn (TurnError::CustomEffectRequiresProofCarryingTurn), and
        // sdk-py cannot build one. Exposing a `.custom()` verb here would only
        // mint turns that are always rejected.
        "Custom",
        // Authority/lifecycle surfaces the two-noun client deliberately omits.
        "RevokeCapability",
        "AttenuateCapability",
        "EmitEvent",
        "CreateCell",
        "SetPermissions",
        "SetVerificationKey",
        "SetProgram",
        "SpawnWithDelegation",
        "RefreshDelegation",
        "RevokeDelegation",
        "BridgeMint",
        "Introduce",
        "PipelinedSend",
        "ExerciseViaCapability",
        "MakeSovereign",
        "CreateCellFromFactory",
        "Refusal",
        "CellSeal",
        "CellUnseal",
        "CellDestroy",
        "Burn",
        "ReceiptArchive",
        "Promise",
        "Notify",
        "React",
        "Mint",
    ];

    for v in built {
        assert!(
            protocol.iter().any(|p| p == v),
            "sdk-py stages `Effect::{v}`, but the protocol no longer has that variant — sdk-py \
             would not compile against the real enum. Protocol variants: {protocol:?}"
        );
    }

    let mut unaccounted: Vec<&String> = protocol
        .iter()
        .filter(|p| !built.contains(&p.as_str()) && !unbuilt.contains(&p.as_str()))
        .collect();
    unaccounted.sort();
    assert!(
        unaccounted.is_empty(),
        "PROTOCOL DRIFT: the effect vocabulary grew variants sdk-py has never considered: \
         {unaccounted:?}\n\nDecide for each: add a TurnBuilder verb (and put it in `built`), or \
         record it in `unbuilt` WITH the reason it is out of the light client's reach. Do not \
         silence this by deleting the check — the whole point is that a new protocol verb cannot \
         reach PyPI unnoticed."
    );
}
