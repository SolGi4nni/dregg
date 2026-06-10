//! Polis commands — read-only inspection of governance cells over a live node.
//!
//! `dregg polis council --cell <id>` decodes a council proposal cell (the
//! `starbridge-polis` council machine) straight from the node's public cell
//! read: lifecycle state, staged proposal hash, per-member approval bits,
//! the certified-threshold flag, and the published membership commitment.
//!
//! The slot schema mirrors `starbridge-apps/polis/src/lib.rs` (`council`
//! module) byte-for-byte; the THRESHOLD itself is not a cell slot — it is
//! content-addressed into the factory descriptor (and committed, with the
//! member list, under the `members commit` shown here), so the cell shows
//! the approval COUNT and the certified flag the executor enforced.

use clap::Subcommand;

use crate::config::Config;
use crate::output::Context;

use super::get_json;

// Council proposal-cell slot schema — mirrors starbridge_polis::council.
const STATE_SLOT: usize = 0;
const PROPOSAL_HASH_SLOT: usize = 1;
const APPROVED_FLAG_SLOT: usize = 2;
const FIRST_APPROVAL_SLOT: usize = 3;
const MAX_MEMBERS: usize = 3;
const MEMBERS_COMMIT_SLOT: usize = 6;

#[derive(Subcommand)]
pub enum PolisCommand {
    /// Show a council proposal cell: state, staged hash, approvals, certification.
    ///
    ///   dregg polis council --cell <proposal_cell>
    Council {
        /// The council proposal cell id.
        #[arg(long)]
        cell: String,
        /// Number of charter members (bounds the approval slots shown).
        #[arg(long, default_value_t = MAX_MEMBERS)]
        members: usize,
    },
}

pub async fn run(
    command: PolisCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match command {
        PolisCommand::Council { cell, members } => council(cfg, ctx, &cell, members).await,
    }
}

fn state_name(code: u64) -> &'static str {
    match code {
        0 => "DRAFT",
        1 => "PROPOSED",
        2 => "REJECTED (terminal)",
        3 => "APPROVED",
        4 => "EXECUTED (terminal)",
        _ => "UNKNOWN",
    }
}

async fn council(
    cfg: &Config,
    ctx: &Context,
    cell: &str,
    members: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let members = members.min(MAX_MEMBERS);
    let detail = get_json(cfg, &format!("/api/cell/{cell}")).await?;
    let found = detail["found"].as_bool().unwrap_or(false);
    let fields = detail["fields"].as_array().cloned().unwrap_or_default();
    let slot = |i: usize| -> String {
        fields
            .get(i)
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string()
    };
    let u64_at = |i: usize| u64_from_field_hex(&slot(i));

    let state = u64_at(STATE_SLOT);
    let approvals: Vec<bool> = (0..members)
        .map(|i| u64_at(FIRST_APPROVAL_SLOT + i) == 1)
        .collect();
    let approval_count = approvals.iter().filter(|a| **a).count();
    let certified = u64_at(APPROVED_FLAG_SLOT) == 1;

    if cfg.is_json() {
        ctx.json_stdout(&serde_json::json!({
            "cell": cell,
            "found": found,
            "state": state,
            "state_name": state_name(state),
            "proposal_hash": slot(PROPOSAL_HASH_SLOT),
            "approvals": approvals,
            "approval_count": approval_count,
            "certified": certified,
            "members_commit": slot(MEMBERS_COMMIT_SLOT),
        }));
        return Ok(());
    }

    ctx.header("Council proposal");
    ctx.kv("Cell", &crate::output::abbrev_hex(cell, 8, 4));
    if !found {
        ctx.error("Cell not found in the ledger.");
        return Ok(());
    }
    ctx.kv("State", state_name(state));
    ctx.kv(
        "Proposal",
        &crate::output::abbrev_hex(&slot(PROPOSAL_HASH_SLOT), 8, 4),
    );
    for (i, a) in approvals.iter().enumerate() {
        ctx.kv(
            &format!("Member {i}"),
            if *a { "APPROVED" } else { "—" },
        );
    }
    ctx.kv("Approvals", &approval_count.to_string());
    ctx.kv("Certified", if certified { "YES (threshold met)" } else { "no" });
    ctx.kv(
        "Members commit",
        &crate::output::abbrev_hex(&slot(MEMBERS_COMMIT_SLOT), 8, 4),
    );
    Ok(())
}

fn u64_from_field_hex(hexstr: &str) -> u64 {
    if hexstr.len() != 64 {
        return 0;
    }
    let tail = &hexstr[48..];
    u64::from_str_radix(tail, 16).unwrap_or(0)
}
