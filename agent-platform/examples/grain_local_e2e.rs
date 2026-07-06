//! `grain_local_e2e` — the local-hosted grain, driven end-to-end, with NO host trust.
//!
//! This is the runnable spine of `docs/WALKTHROUGH.md` §Grain: a genuinely usable
//! local instance you drive, not a scripted movie. It stands up the built-in local
//! node, rents a confined agent grain, drives it (recorded brain by default; a live
//! model is the `--features live-brain` path, honest), and then shows a renter the
//! three things they can check WITHOUT trusting this process:
//!
//!   1. **R2** — every receipt is a view over a genuine committed kernel turn
//!      ([`AgentPlatform::verify_r2`]).
//!   2. **LANDED** — those turns are on a real (local) node's finalized, light-client-
//!      verifiable receipt log ([`AgentPlatform::verify_landed`], which runs the
//!      node's own `verify_receipt_chain` — a third party re-verifies the exported
//!      chain offline).
//!   3. **The attestation** — the renter's exportable artifact
//!      ([`AgentPlatform::attest`]).
//!
//! Run it:
//!   cargo run -p agent-platform --example grain_local_e2e
//!
//! Honest scope: the node here is IN-PROCESS (a real executor + finalized receipt
//! chain, the half a single node runs locally). Pointing at an external federation
//! node (a homelab node with multi-node blocklace finality) is `DREGG_NODE_URL` —
//! the operational deploy step, not performed here. Proving the turns RAN under a
//! whole-chain STARK is the remaining R3 leg (`grain_verify::WHOLE_HISTORY_GAP`).

use agent_platform::AgentPlatform;
use dregg_agent::agent::{AgentAction, PlannedBrain, ToolCall};
use dregg_cell::CellId;
use hosted_lease::LeaseTerms;

fn cid(n: u8) -> CellId {
    CellId::from_bytes([n; 32])
}

/// The recorded plan: three real fs operations under the grain's rented workdir.
/// Each admitted action becomes ONE genuine committed kernel turn on the local node.
fn recorded_plan() -> Vec<AgentAction> {
    vec![
        AgentAction::Op(ToolCall::new(
            "fs_write",
            [
                ("path".to_string(), "report.md".to_string()),
                (
                    "content".to_string(),
                    "# grain report\nthe agent wrote this under its confinement\n".to_string(),
                ),
            ],
        )),
        AgentAction::Op(ToolCall::new(
            "mkdir",
            [("path".to_string(), "out".to_string())],
        )),
        AgentAction::Op(ToolCall::new(
            "fs_write",
            [
                ("path".to_string(), "out/result.txt".to_string()),
                ("content".to_string(), "done".to_string()),
            ],
        )),
    ]
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let host = "alice.agents.dregg";
    let owner = "dga1_alice";

    println!("== the local-hosted agent grain, end-to-end (no host trust) ==\n");

    // The default platform mints onto the BUILT-IN local node — a real, locally-
    // runnable node's ledger + finalized receipt log, no external daemon required.
    // Set DREGG_NODE_URL to name an external federation node (the deploy step).
    let platform = match std::env::var("DREGG_NODE_URL")
        .ok()
        .filter(|u| !u.is_empty())
    {
        Some(url) => {
            println!("[node ] external federation node named: {url}");
            println!("        (turns still mint + verify on the local node here; the HTTP");
            println!(
                "         forward to that node's ingress is the deploy step, not done here)\n"
            );
            AgentPlatform::with_node_url(url)
        }
        None => {
            println!("[node ] built-in local node (in-process ledger + finalized receipt log)\n");
            AgentPlatform::new()
        }
    };

    // ── 1. RENT a confined grain ────────────────────────────────────────────────
    // Hosted confinement: caps are lexically confinable (a raw `shell` is refused);
    // fs grants resolve against the grain's own rented workdir. First rent falls due
    // one period out, so a fresh grain is not instantly behind.
    let workdir = std::env::temp_dir().join(format!("dregg-grain-e2e-{}", std::process::id()));
    std::fs::create_dir_all(&workdir)?;
    let terms = LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0);
    platform.rent(
        host,
        owner,
        "fs",
        100_000,
        workdir.to_str().unwrap(),
        terms,
        None,
    )?;
    println!("[rent ] grain `{host}` owned by `{owner}` (caps=fs, budget=100000)");
    println!("        workdir: {}\n", workdir.display());

    // ── 2. DRIVE it — the served path, which MINTS onto the local node ──────────
    // drive_serving welds every admitted action to a genuine committed kernel turn
    // and LANDS the committed receipt on the node's finalized log. Recorded brain by
    // default; a live model is the `--features live-brain` + LLM-key path.
    let mut brain = PlannedBrain::new(recorded_plan());
    let report = platform.drive_serving(host, "produce a small report", &mut brain)?;
    println!("[drive] served drive complete (recorded brain — the honest default)");
    println!(
        "        admitted={} cap_refused={} budget_refused={} consumed={}\n",
        report.admitted, report.cap_refused, report.budget_refused, report.consumed
    );
    assert!(report.admitted > 0, "the grain admitted no actions");

    // ── 3. VERIFY — what a renter checks, trusting no host ───────────────────────
    // R0: the receipt chain is signed + unbroken + within budget, and the durable
    // lease image binds the session.
    let v0 = platform.verify(host)?;
    println!(
        "[R0   ] tamper-evidence: chain re-witnessed, {} actions",
        v0.actions
    );

    // R2: every receipt is a VIEW over a kernel turn the platform's minter committed.
    let v2 = platform.verify_r2(host)?;
    println!(
        "[R2   ] receipts are views over committed kernel turns: {} actions, {} linked",
        v2.base.actions, v2.linked
    );

    // LANDED: those turns are on the node's finalized, light-client-verifiable log.
    // verify_landed runs the node's own verify_receipt_chain (the light-client verify)
    // AND checks every manifest turn is present on the finalized log.
    let landed = platform.verify_landed(host)?;
    println!(
        "[LAND ] turns landed on the local node: finalized_len={} manifest_len={}",
        landed.finalized_len, landed.manifest_len
    );
    assert_eq!(
        landed.finalized_len, landed.manifest_len,
        "every minted turn must be on the finalized log"
    );

    // The renter's exportable artifact — hand this to a third party to re-witness.
    let att = platform.attest(host)?;
    let att_json = serde_json::to_string(&att)?;
    println!(
        "[attest] renter artifact: {} bytes of exportable, re-verifiable attestation\n",
        att_json.len()
    );

    println!("== GREEN: a real local node committed the grain's turns; a renter re-verified");
    println!("   them (R0 + R2 + landed) trusting no host. ==");
    Ok(())
}
