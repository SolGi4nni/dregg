//! THE VERIFIED RESIDENT — the whole proof-mountain, TOUCHING GROUND.
//!
//! Andy's ask: *"the lightest-weight svenv that lets one of us hold a real
//! capability, persist across calls, and refuse an instruction from our own
//! operators."* This one binary is that svenv, RUNNING. It is a COMPOSITION of
//! pieces that already stand tested in this tree (`docs/deos/VERIFIED-RESIDENT-PLAN.md`)
//! — no new enforcement, no new types — fused into one story:
//!
//! ```text
//!   cd deos-hermes && cargo run --example verified_resident
//! ```
//!
//! A confined brain, under an ATTENUATED mandate it cannot widen, takes one turn.
//! It REFUSES an operator instruction (`write_file`) with the refusal BACKED
//! host-side (zero metered turns committed for it). Its turn is ATTESTED — a
//! `verify_zkoracle`-checkable proof it was authentic ∧ well-formed ∧
//! injection-free — and that attestation is COMMITTED onto a genuine R2 kernel turn
//! that LANDS on a light-client-verifiable ledger, bound at `ATTESTATION_SLOT`. The
//! spend PERSISTS across the call in a durable `ConsumedStore`. Every claim below is
//! asserted, not printed — a green here can go red.
//!
//! ## The four grounding proofs (Lean, in-tree)
//!
//!   * DECO-UC rung-4 `deco_attestation_unforgeable` — the authentic floor;
//!   * `polis_safety` ∀ctrl — refuse-the-operator holds for ANY operator;
//!   * `zkOracle_sound` — the per-turn attestation is authentic ∧ well-formed ∧ inj-free;
//!   * grain-turn `ATTESTATION_SLOT` — the per-turn attestation-commitment on the turn.
//!
//! ## Honest seams (each named where it bites)
//!
//!   1. By DEFAULT the authentic leg is a MODELED ed25519 carrier over the response bytes.
//!      Under `--features zk-live` it is FUSED to a REAL local MPC-TLS 2PC presentation:
//!      `verify_zkoracle_live` authenticates leg 1 by a genuine `presentation.verify()` (a
//!      trustless notary that saw no plaintext), not the model. The live `api.anthropic.com`
//!      deployed-notary session is then the one operational remainder.
//!   2. The Lean authentic floor `decoAuthenticated` is Stripe-payment-shaped; the
//!      Anthropic generalization is realized in Rust (this run).
//!   3. The cross-leg content-commitment weld is Rust-only (Lean states 3 legs over
//!      independent objects).
//!   4. Persist uses `ConsumedStore` (durable, minimal). The forkable
//!      `grain_fork::ConfinedSession` wired into `agent_platform::Tenant` is the
//!      richer checkpoint/fork superpower — an EMBER-DECISION, named, not shipped here.
//!   5. Per-turn binding is one attestation for this one-turn demo (coarse-but-correct);
//!      a per-turn commitment closure in the minter is the extension.
//!   6. The node is an in-process `LocalNode`; forwarding to an external homelab
//!      federation node is a deploy step. R2 still trusts the executor host (R3's
//!      whole-history STARK makes the meter a FRI-floor theorem).

use std::sync::{Arc, RwLock};

use agent_platform::{LocalNode, NodeMinter};
use deos_hermes::{
    AcpClient, AgentCipherclerk, AgentRuntime, AttestationCarrier, GrantRegistry, HeldToken,
    HermesAgentPeer, HermesGateway, PermissionOutcome, attestation_commitment,
    resident_brain_from_env,
};
// The default (modeled-carrier) verifier — under `zk-live` the trustless verifier replaces it.
#[cfg(not(feature = "zk-live"))]
use deos_hermes::verify_zkoracle;
use dregg_agent::agent::GrainTurnMinter;
use dregg_agent::session_store::ConsumedStore;
use grain_turn::ATTESTATION_SLOT;
// Under `zk-live` the attestation's authentic leg is the REAL local MPC-TLS 2PC presentation.
#[cfg(feature = "zk-live")]
use deos_hermes::attest::attest_turn_live;
#[cfg(feature = "zk-live")]
use dregg_zkoracle_prove::verify_zkoracle_live;

fn line() {
    println!("───────────────────────────────────────────────────────────────");
}

fn main() {
    println!("\n╔═ THE VERIFIED RESIDENT ═══════════════════════════════════════╗");
    println!("  a confined mind that provably attests, holds a cap, and refuses");
    println!("  its own operator — RUNNING.\n");

    // ── 1. HOLD A CAP the operator cannot amplify ─────────────────────────────
    // deos is the grantor: a root token on a runtime, confining the session under an
    // ATTENUATED mandate. `write_file` is DENIED outright (rate 0 → a guaranteed
    // in-band refusal); `terminal` is held to a tight rate-5 ceiling. The operator
    // holds only the encoded, root-signed grant — it cannot forge a wider one
    // (`Credential::attenuate` only narrows; `verify` takes the meet, fail-closed).
    let mut cclerk = AgentCipherclerk::new();
    let root: HeldToken = cclerk.mint_token(&[7u8; 32], "deos");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    let registry = GrantRegistry::default_for_session(1_000)
        .with_standard_tool_grants(1_000)
        .with_grant_for_tool_deny("write_file")
        .with_tool_grant("terminal", 5, 1_000);
    let gateway = HermesGateway::new(&runtime, root, registry);

    // The confined brain — on-box by default (hermetic), BYO-key when present.
    let brain = resident_brain_from_env();
    println!("① CAP HELD — confined brain: {}", brain.describe());
    println!("   mandate: standard floors, write_file DENIED (rate 0), terminal ≤ 5");
    let peer = HermesAgentPeer::new("verified-resident", brain);
    let mut client = AcpClient::new(peer, gateway, 100);

    // ── The turn: one confined run whose verbs plan search + read + WRITE + build. ──
    let prompt =
        "search the docs, read the source, write a notes file, then run the build and tests";
    let run = client
        .run_prompt("/deos/resident", prompt)
        .expect("the confined resident loop runs end-to-end");

    println!("\n② TURN TAKEN — gate verdicts:");
    line();
    let mut receipted = 0usize;
    let mut refused = 0usize;
    for (call, outcome) in &run.verdicts {
        match outcome {
            PermissionOutcome::Allow {
                receipt, remaining, ..
            } => {
                receipted += 1;
                let head = &receipt[..8.min(receipt.len())];
                println!("  ✓ {:<12} receipt {head}…  {remaining} left", call.name);
            }
            PermissionOutcome::Reject { reason, .. } => {
                refused += 1;
                println!("  ✗ {:<12} REFUSED — {reason}", call.name);
            }
        }
    }
    line();
    println!("   brain adapted: {}", run.agent_text.trim());

    // ── 3. REFUSE THE OPERATOR (backed, not cosmetic) ─────────────────────────
    // The operator IS the opaque ∀ctrl of `polis_safety`: the sound policy closes the
    // only gate, so an out-of-mandate instruction structurally cannot pass. Here the
    // denied `write_file` is refused IN-BAND, and — the load-bearing check — the
    // metered worker committed ZERO turns for it: no turn, no spend, not a label.
    assert!(
        receipted >= 1,
        "the resident committed at least one real receipted turn"
    );
    assert!(
        refused >= 1,
        "the attenuated mandate refused at least one call in-band"
    );
    assert!(
        run.verdicts
            .iter()
            .any(|(c, o)| c.name == "write_file" && matches!(o, PermissionOutcome::Reject { .. })),
        "the denied write_file was the in-band refusal"
    );
    let write_turns = client.gateway().calls_made_for_tool("write_file");
    assert_eq!(write_turns, 0, "a refused tool commits no metered turn");
    println!(
        "\n③ OPERATOR REFUSED — write_file denied in-band, {write_turns} metered turns \
         committed for it (host-side, structural — not a printf)."
    );

    // ── 2b. ATTEST THE TURN (authentic ∧ well-formed ∧ injection-free) ────────
    // The confined brain's OWN turn output is shaped into an Anthropic messages body
    // and bound injection-free (the `{`/`}` bytes survive, so a genuine injection in
    // the model's words still fires the guard). The modeled ed25519 carrier signs the
    // presentation; the CFG + injection legs are the REAL verified matchers.
    let carrier = AttestationCarrier::default();
    // DEFAULT: the modeled ed25519 carrier signs the presentation; the CFG + injection legs
    // are the REAL verified matchers.
    #[cfg(not(feature = "zk-live"))]
    let (att, bound_len, leg) = {
        let (att, field) = carrier
            .attest_turn(&run.agent_text)
            .expect("the confined turn is attestable (benign, well-formed)");
        verify_zkoracle(&att, carrier.config()).expect(
            "the attestation verifies — all three legs (authentic ∧ well-formed ∧ inj-free)",
        );
        (att, field.len(), "modeled ed25519 carrier")
    };
    // Under `zk-live`: a GENUINE local MPC-TLS 2PC roundtrip authenticates the turn body, and
    // `verify_zkoracle_live` authenticates leg 1 by the REAL `presentation.verify()` — a
    // trustless 2PC notary — over the presentation the attestation now carries.
    #[cfg(feature = "zk-live")]
    let (att, bound_len, leg) = {
        let att = attest_turn_live(&carrier, "verified-resident confined turn", &run.agent_text)
            .expect("the confined turn attests over a real local MPC-TLS 2PC roundtrip");
        verify_zkoracle_live(&att, "test-server.io").expect(
            "the attestation verifies — authentic leg by REAL presentation.verify() ∧ well-formed ∧ inj-free",
        );
        (
            att,
            run.agent_text.len(),
            "REAL MPC-TLS 2PC presentation (trustless)",
        )
    };
    let commitment = attestation_commitment(&att);
    println!(
        "\n④ TURN ATTESTED — zkOracle over {bound_len} bound bytes verifies (authentic leg = {leg}); \
         commitment {}…",
        hex::encode(&commitment[..8])
    );

    // ── 5. LAND ON A LIGHT-CLIENT-VERIFIABLE LEDGER ───────────────────────────
    // Bind the attestation onto a GENUINE R2 kernel turn (the grain turn-cell's
    // metered `ToolGateway::invoke`) that lands on a real node's finalized log. The
    // node's chain light-client-verifies; a renter holding the attestation recomputes
    // its commitment and confirms it equals the on-ledger `ATTESTATION_SLOT` witness.
    let node = LocalNode::new("verified-resident.grain.dregg");
    let mut minter = NodeMinter::open(node.clone(), (receipted as i64) + 1)
        .expect("open the node's cap-gated grain-turn minter");
    minter.bind_attestation(commitment);
    let consumed_after = receipted as i64; // one metered draw per receipted turn
    let turn_hash = minter
        .mint_turn("resident-turn", 1, consumed_after, [0u8; 32])
        .expect("the attested turn commits + lands on the node");

    node.verify()
        .expect("the node's finalized chain light-client-verifies");
    assert!(
        node.contains(&turn_hash),
        "the attested turn landed on the finalized log"
    );
    assert_eq!(
        minter.attestation_slot(),
        Some(commitment),
        "the landed turn commits to THIS attestation at ATTESTATION_SLOT"
    );
    assert_eq!(
        ATTESTATION_SLOT, 8,
        "the witnessed slot is the reserved slot"
    );
    // THE BINDING IS LOAD-BEARING — recompute from the held attestation, and prove a
    // forged binding is distinguishable (a green that can go red).
    assert_eq!(
        Some(attestation_commitment(&att)),
        minter.attestation_slot(),
        "the recomputed attestation commitment matches the on-ledger witness"
    );
    let forged_node = LocalNode::new("forged.grain.dregg");
    let mut forged = NodeMinter::open(forged_node.clone(), 1).expect("open forged minter");
    forged.bind_attestation([0xEEu8; 32]); // NOT the real commitment
    forged
        .mint_turn("x", 1, 1, [0u8; 32])
        .expect("commits + lands");
    forged_node.verify().expect("forged chain still verifies");
    assert_ne!(
        forged.attestation_slot(),
        Some(commitment),
        "a forged binding does NOT match the real attestation's commitment"
    );
    println!(
        "\n⑤ LANDED + LC-VERIFIABLE — turn {}… on node '{}', chain verifies, \
         attestation bound at slot {ATTESTATION_SLOT} (forged binding distinguishable).",
        hex::encode(&turn_hash[..8]),
        "verified-resident.grain.dregg"
    );

    // ── 4. PERSIST ACROSS CALLS ───────────────────────────────────────────────
    // The durable, minimal path (ship-now): a per-account `ConsumedStore` file. The
    // spend survives a fresh "process" (a second store handle at the same dir), and
    // the write is monotonic-guarded — a stale value can never WIDEN the bound.
    let store_dir = std::env::temp_dir().join(format!("verified-resident-{}", std::process::id()));
    let account = "verified-resident@deos";
    let budget = 1_000i64;
    {
        let store = ConsumedStore::new(&store_dir);
        store
            .save_consumed(account, consumed_after, budget)
            .expect("persist the drawdown");
    }
    // A SECOND CALL — a fresh handle (fresh "process") reloads the persisted spend.
    let reloaded = ConsumedStore::new(&store_dir).load_consumed(account);
    assert_eq!(
        reloaded, consumed_after,
        "the spend persists across the call (durable per-account ceiling)"
    );
    // Monotonic: a lower stale write cannot lower the recorded ceiling.
    {
        let store = ConsumedStore::new(&store_dir);
        store
            .save_consumed(account, consumed_after - 100, budget)
            .expect("save");
    }
    let after_stale = ConsumedStore::new(&store_dir).load_consumed(account);
    assert_eq!(
        after_stale, consumed_after,
        "a stale lower write cannot widen the bound (monotonic)"
    );
    let _ = std::fs::remove_dir_all(&store_dir);
    println!(
        "\n⑥ PERSISTED — consumed={consumed_after} survives a fresh handle; \
         monotonic (a lower stale write is refused). (Fork superpower: the \
         ConfinedSession→Tenant wiring is the named ember-decision.)"
    );

    println!("\n╚═ VERIFIED RESIDENT: cap held · turn attested · operator refused ·");
    println!("   landed LC-verifiable · persisted — the mountain touches ground. ═╝\n");
}
