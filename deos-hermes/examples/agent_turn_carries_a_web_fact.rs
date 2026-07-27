//! **Proof-of-QA weld** — an agent's grain turn carries a proof of a real external
//! web fact, re-verifiable by a light client.
//!
//! Composes three real pieces:
//!   1. `zkoracle-prove`'s real-host prover — a genuine MPC-TLS 2PC against
//!      `api.github.com`, proving a commit exists (`prove_github_live`).
//!   2. `deos_hermes::attestation_commitment` — the canonical 32-byte commitment to
//!      that attestation (the same hash the grain-turn R2 rail uses).
//!   3. `grain_turn::ToolGatewayMinter::bind_attestation` — binds it into a genuine
//!      committed kernel turn at `ATTESTATION_SLOT`.
//!
//! Then a *light client* re-verifies the fact and recomputes the commitment, and we
//! assert it equals what the turn actually carries. So "the agent says it saw this
//! GitHub commit" becomes a receipt a stranger checks, trusting no one.
//!
//! Run: `cargo run -p deos-hermes --features zk-live --example agent_turn_carries_a_web_fact`

use std::collections::BTreeMap;

use deos_hermes::attest::attestation_commitment;
use dregg_agent::agent::{AgentAction, AgentSpec, PlannedBrain, ToolKit, ToolOutcome};
use dregg_agent::session::Session;
use dregg_zkoracle_live::endpoints::github::{prove_github_live, verify_github_live};
use grain_turn::{ATTESTATION_SLOT, ToolGatewayMinter};

struct NoKit;
impl ToolKit for NoKit {
    fn invoke(
        &self,
        _service: &str,
        _amount_cents: Option<i64>,
        _cells: &BTreeMap<String, String>,
    ) -> ToolOutcome {
        ToolOutcome::pass("ok")
    }
}

fn one_action() -> PlannedBrain {
    PlannedBrain::new(vec![AgentAction::Invoke {
        service: "work".into(),
    }])
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // A real, public commit (octocat/Hello-World).
    let (owner, repo, sha) = (
        "octocat",
        "Hello-World",
        "762941318ee16e59dabbacb1b4049eec22f0d303",
    );

    // 1. The agent proves the external fact — a genuine MPC-TLS session with GitHub.
    eprintln!(
        "== proving api.github.com commit {owner}/{repo}@{} via MPC-TLS …",
        &sha[..12]
    );
    let (att, notary_key) =
        prove_github_live(owner, repo, sha).map_err(|e| format!("prove: {e:?}"))?;

    // 2. The canonical commitment to that attestation (the grain-turn rail's own hash).
    let commitment = attestation_commitment(&att);

    // 3. Bind it into a GENUINE committed kernel turn.
    let budget = 10;
    let mut minter = ToolGatewayMinter::open("web-fact", budget)?;
    let spec = AgentSpec::new("ignored", budget).with_service("work");
    let mut sess = Session::open_seeded([71u8; 32], "dga1_renter", spec)?;
    minter.bind_attestation(commitment);
    let gr = sess.run_goal_minted(
        "attest a web fact",
        &mut one_action(),
        &NoKit,
        Some(&mut minter),
    );
    if gr.admitted != 1 {
        return Err(format!("expected 1 admitted turn, got {}", gr.admitted).into());
    }

    // The turn REALLY carries the commitment at ATTESTATION_SLOT.
    let landed = minter
        .read_slot(ATTESTATION_SLOT)
        .ok_or("no attestation landed at ATTESTATION_SLOT")?;
    assert_eq!(
        landed, commitment,
        "the committed turn carries the fact commitment"
    );
    let turn_hash = minter
        .committed_turns()
        .last()
        .copied()
        .ok_or("no committed turn")?;

    // 4. LIGHT CLIENT: re-verify the fact from the attestation + recompute the commitment,
    //    and check it matches what the turn carries. Trusting no one but GitHub's cert
    //    chain + the pinned notary key.
    let fact = verify_github_live(&att, &notary_key).map_err(|e| format!("verify: {e:?}"))?;
    let recomputed = attestation_commitment(&att);
    assert_eq!(
        recomputed, landed,
        "light-client commitment matches the landed slot"
    );

    println!();
    println!("VERIFIED — an agent's grain turn carries a re-checkable web fact:");
    println!("  turn hash        {}", hex(&turn_hash));
    println!("  ATTESTATION_SLOT {}", hex(&landed));
    println!(
        "  the fact         {}/{}@{} — {}",
        fact.owner,
        fact.repo,
        &fact.sha[..12],
        fact.message.lines().next().unwrap_or("").trim()
    );
    println!("  by               {} ({})", fact.author, fact.date);
    println!();
    println!("  A light client re-verified the MPC-TLS proof and recomputed the exact");
    println!("  32-byte commitment the turn carries. The agent's claim is now a receipt.");
    Ok(())
}

fn hex(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
