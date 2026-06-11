//! Bounty-board commands — the demoable starbridge-app flow over a live node.
//!
//! These drive a `starbridge-bounty-board` bounty cell through the node's
//! `/turn/submit` JSON ingress (a real signed call-forest on the verified
//! commit path). A bounty is a single factory-born cell whose slot caveats *are*
//! the lifecycle state machine:
//!
//! | Slot | Meaning          | Caveat            |
//! |:---:|-------------------|-------------------|
//! | 2   | title hash        | `WriteOnce`       |
//! | 3   | reward            | `WriteOnce`       |
//! | 4   | state code        | `StrictMonotonic` |
//! | 5   | claimant hash     | `WriteOnce`       |
//! | 6   | submission hash   | `WriteOnce`       |
//!
//! State codes: OPEN(1) → CLAIMED(2) → SUBMITTED(3) → PAID(4). Because `state`
//! is `StrictMonotonic` and `claimant` is `WriteOnce`, a second claim on a
//! claimed bounty is rejected — first-claimer-wins, enforced by the substrate.
//! Pass `--cell <id>` for the seeded bounty cell (`bounty-board-bounty`).

use clap::Subcommand;

use crate::config::Config;
use crate::output::Context;

use super::name::{field_from_bytes_hex, field_from_u64_hex};
use super::{get_json, post_json};

// Bounty-cell slot schema — mirrors starbridge-apps/bounty-board/src/lib.rs.
const TITLE_HASH_SLOT: usize = 2;
const REWARD_SLOT: usize = 3;
const STATE_SLOT: usize = 4;
const CLAIMANT_HASH_SLOT: usize = 5;
const SUBMISSION_HASH_SLOT: usize = 6;

const STATE_OPEN: u64 = 1;
const STATE_CLAIMED: u64 = 2;
const STATE_SUBMITTED: u64 = 3;
const STATE_PAID: u64 = 4;

#[derive(Subcommand)]
pub enum BountyCommand {
    /// Post a bounty: write title + reward + STATE=OPEN, emit `bounty-posted`.
    ///
    ///   dregg bounty post "Fix the parser bug" --reward 500 --cell <bounty_cell>
    Post {
        /// The bounty title.
        title: String,
        /// The escrowed reward amount.
        #[arg(long)]
        reward: u64,
        /// The bounty cell (the factory-born `bounty-board-bounty` cell).
        #[arg(long)]
        cell: String,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Claim a bounty: bind the claimant (write-once → first-claimer-wins) and
    /// advance STATE to CLAIMED. A second claim is rejected by the caveats.
    ///
    ///   dregg bounty claim bob --cell <bounty_cell>
    Claim {
        /// Claimant identifier (e.g. an agent handle or pubkey).
        claimant: String,
        /// The bounty cell.
        #[arg(long)]
        cell: String,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Submit work: bind the artifact URI and advance STATE to SUBMITTED.
    Submit {
        /// The work-artifact URI.
        artifact: String,
        /// The bounty cell.
        #[arg(long)]
        cell: String,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Pay out: advance STATE to PAID (terminal).
    Payout {
        /// The bounty cell.
        #[arg(long)]
        cell: String,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Show a bounty's state: title binding, reward, lifecycle state, claimant.
    Show {
        /// The bounty cell.
        #[arg(long)]
        cell: String,
    },
}

pub async fn run(
    command: BountyCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match command {
        BountyCommand::Post {
            title,
            reward,
            cell,
            fee,
        } => post(cfg, ctx, &title, reward, &cell, fee).await,
        BountyCommand::Claim {
            claimant,
            cell,
            fee,
        } => claim(cfg, ctx, &claimant, &cell, fee).await,
        BountyCommand::Submit {
            artifact,
            cell,
            fee,
        } => submit(cfg, ctx, &artifact, &cell, fee).await,
        BountyCommand::Payout { cell, fee } => payout(cfg, ctx, &cell, fee).await,
        BountyCommand::Show { cell } => show(cfg, ctx, &cell).await,
    }
}

async fn submit_effects(
    cfg: &Config,
    target: &str,
    method: &str,
    effects: Vec<serde_json::Value>,
    fee: u64,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    use serde_json::json;
    let req = json!({
        "agent": "00".repeat(32),
        "nonce": 0,
        "fee": fee,
        "memo": serde_json::Value::Null,
        "actions": [{ "target": target, "method": method, "effects": effects }],
    });
    // `/api/turns/submit` = the `/turn/submit` alias that also passes
    // gateway proxies which only forward `/api/*` (the public devnet).
    let data = post_json(cfg, "/api/turns/submit", &req).await?;
    Ok(data)
}

fn render_turn(ctx: &Context, data: &serde_json::Value, action: &str) {
    let accepted = data["accepted"].as_bool().unwrap_or(false);
    let turn_hash = data["turn_hash"].as_str().unwrap_or("?");
    if accepted {
        ctx.success(&format!("{action} committed"));
    } else {
        let err = data["error"].as_str().unwrap_or(turn_hash);
        ctx.error(&format!("{action} rejected: {err}"));
    }
    ctx.kv("Turn", &crate::output::abbrev_hex(turn_hash, 8, 4));
}

async fn post(
    cfg: &Config,
    ctx: &Context,
    title: &str,
    reward: u64,
    cell: &str,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let title_h = field_from_bytes_hex(title.as_bytes());
    let reward_h = field_from_u64_hex(reward);
    let effects = vec![
        json!({ "kind": "set_field", "index": TITLE_HASH_SLOT, "value": title_h }),
        json!({ "kind": "set_field", "index": REWARD_SLOT, "value": reward_h }),
        json!({ "kind": "set_field", "index": STATE_SLOT, "value": field_from_u64_hex(STATE_OPEN) }),
        json!({ "kind": "emit_event", "topic": "bounty-posted", "data": [title_h, reward_h] }),
    ];
    if !cfg.is_json() {
        ctx.header(&format!("Post bounty '{title}'"));
        ctx.kv("Cell", &crate::output::abbrev_hex(cell, 8, 4));
        ctx.kv("Reward", &reward.to_string());
    }
    let spinner = ctx.spinner("Posting bounty (sign → execute → prove)...");
    let data = submit_effects(cfg, cell, "post_bounty", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    render_turn(ctx, &data, "Post");
    Ok(())
}

async fn claim(
    cfg: &Config,
    ctx: &Context,
    claimant: &str,
    cell: &str,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let claimant_h = field_from_bytes_hex(claimant.as_bytes());
    let effects = vec![
        json!({ "kind": "set_field", "index": CLAIMANT_HASH_SLOT, "value": claimant_h }),
        json!({ "kind": "set_field", "index": STATE_SLOT, "value": field_from_u64_hex(STATE_CLAIMED) }),
        json!({ "kind": "emit_event", "topic": "bounty-claimed", "data": [claimant_h] }),
    ];
    if !cfg.is_json() {
        ctx.header(&format!("Claim bounty as '{claimant}'"));
        ctx.kv("Cell", &crate::output::abbrev_hex(cell, 8, 4));
    }
    let spinner = ctx.spinner("Claiming (WriteOnce/StrictMonotonic-gated)...");
    let data = submit_effects(cfg, cell, "claim_bounty", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    render_turn(ctx, &data, "Claim");
    if !data["accepted"].as_bool().unwrap_or(false) {
        ctx.info("  A rejection here is the caveats biting: first-claimer-wins (the bounty is already claimed).");
    }
    Ok(())
}

async fn submit(
    cfg: &Config,
    ctx: &Context,
    artifact: &str,
    cell: &str,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let artifact_h = field_from_bytes_hex(artifact.as_bytes());
    let effects = vec![
        json!({ "kind": "set_field", "index": SUBMISSION_HASH_SLOT, "value": artifact_h }),
        json!({ "kind": "set_field", "index": STATE_SLOT, "value": field_from_u64_hex(STATE_SUBMITTED) }),
        json!({ "kind": "emit_event", "topic": "bounty-submitted", "data": [artifact_h] }),
    ];
    let spinner = ctx.spinner("Submitting work...");
    let data = submit_effects(cfg, cell, "submit_work", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    ctx.header("Submit work");
    ctx.kv("Artifact", artifact);
    render_turn(ctx, &data, "Submit");
    Ok(())
}

async fn payout(
    cfg: &Config,
    ctx: &Context,
    cell: &str,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let paid = field_from_u64_hex(STATE_PAID);
    let effects = vec![
        json!({ "kind": "set_field", "index": STATE_SLOT, "value": paid }),
        json!({ "kind": "emit_event", "topic": "bounty-paid", "data": [paid] }),
    ];
    let spinner = ctx.spinner("Paying out...");
    let data = submit_effects(cfg, cell, "payout_bounty", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    ctx.header("Payout");
    render_turn(ctx, &data, "Payout");
    Ok(())
}

async fn show(cfg: &Config, ctx: &Context, cell: &str) -> Result<(), Box<dyn std::error::Error>> {
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
    let zero = "0".repeat(64);
    let state = u64_at(STATE_SLOT);
    let state_name = match state {
        STATE_OPEN => "OPEN",
        STATE_CLAIMED => "CLAIMED",
        STATE_SUBMITTED => "SUBMITTED",
        STATE_PAID => "PAID",
        _ => "(unset)",
    };
    let claimant = slot(CLAIMANT_HASH_SLOT);
    let has_claimant = !claimant.is_empty() && claimant != zero;

    if cfg.is_json() {
        ctx.json_stdout(&serde_json::json!({
            "cell": cell,
            "found": found,
            "reward": u64_at(REWARD_SLOT),
            "state": state,
            "state_name": state_name,
            "claimant_hash": claimant,
        }));
        return Ok(());
    }

    ctx.header("Bounty");
    ctx.kv("Cell", &crate::output::abbrev_hex(cell, 8, 4));
    if !found {
        ctx.error("Cell not found in the ledger.");
        return Ok(());
    }
    ctx.kv("Reward", &u64_at(REWARD_SLOT).to_string());
    ctx.kv("State", state_name);
    if has_claimant {
        ctx.kv("Claimant", &crate::output::abbrev_hex(&claimant, 8, 4));
    } else {
        ctx.kv_dim("Claimant", "(unclaimed)");
    }
    Ok(())
}

fn u64_from_field_hex(hexstr: &str) -> u64 {
    if hexstr.len() != 64 {
        return 0;
    }
    let tail = &hexstr[48..];
    u64::from_str_radix(tail, 16).unwrap_or(0)
}
