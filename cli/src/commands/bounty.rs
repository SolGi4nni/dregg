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
//!
//! ## `payout` MOVES VALUE
//!
//! Until 2026-07-28 `payout` here submitted a `set_field` and an `emit_event`
//! and nothing else — the same wound as the crate's Rust builders and the
//! Discord command. It now submits TWO actions in ONE turn: a `transfer` from
//! the submitting operator cell to `--claimant`, and the `STATE=PAID` advance on
//! the bounty. They are roots of one call forest, so a payment the executor
//! refuses (`InsufficientBalance`) rolls the PAID stamp back with it, and there
//! is no run of this command that reports a settled bounty over a payment that
//! did not happen.
//!
//! The reward is a PROMISE, not an escrow: `reward` is a `WriteOnce` slot on the
//! bounty cell and the bounty cell cannot hold the money (see the crate docs —
//! `StrictMonotonic(STATE)` refuses any action that credits the cell without
//! advancing its state). Whoever settles pays from their own balance.

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

    /// Pay out: transfer the promised reward to the claimant and advance STATE
    /// to PAID (terminal), atomically in one turn.
    ///
    ///   dregg bounty payout --cell <bounty_cell> --claimant <payee_cell>
    Payout {
        /// The bounty cell.
        #[arg(long)]
        cell: String,
        /// The cell to pay (the claimant's cell id, 64 hex chars).
        #[arg(long)]
        claimant: String,
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
        BountyCommand::Payout {
            cell,
            claimant,
            fee,
        } => payout(cfg, ctx, &cell, &claimant, fee).await,
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
    submit_actions(
        cfg,
        vec![json!({ "target": target, "method": method, "effects": effects })],
        fee,
    )
    .await
}

/// Submit several actions as roots of ONE turn. They commit or roll back
/// together, which is what makes a payment and its `STATE=PAID` stamp one
/// outcome rather than two independently-failing writes.
///
/// An action with no `target` defaults to the node operator's own agent cell,
/// and a `transfer` with no `from` defaults to its action's target — so the
/// payment leg below is a same-cell send the executor admits without a
/// cross-cell `Send` check.
async fn submit_actions(
    cfg: &Config,
    actions: Vec<serde_json::Value>,
    fee: u64,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    use serde_json::json;
    let req = json!({
        "agent": "00".repeat(32),
        "nonce": 0,
        "fee": fee,
        "memo": serde_json::Value::Null,
        "actions": actions,
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
    if reward == 0 {
        ctx.error(
            "A bounty must promise a reward greater than zero: a zero-reward bounty \
             can only ever settle by moving nothing.",
        );
        return Ok(());
    }
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
    claimant: &str,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;

    // Read the bounty BEFORE building anything. Every reason this cannot pay is
    // a refusal that submits no turn.
    let detail = get_json(cfg, &format!("/api/cell/{cell}")).await?;
    if !detail["found"].as_bool().unwrap_or(false) {
        ctx.error("No such bounty cell in the ledger. Nothing was paid.");
        return Ok(());
    }
    let fields = detail["fields"].as_array().cloned().unwrap_or_default();
    let slot = |i: usize| -> String {
        fields
            .get(i)
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string()
    };
    let stage = u64_from_field_hex(&slot(STATE_SLOT));
    if stage != STATE_SUBMITTED {
        ctx.error(&format!(
            "This bounty is {}. Only submitted work can be paid out, and a bounty is \
             paid once. Nothing was paid.",
            state_name(stage)
        ));
        return Ok(());
    }
    // The claimant was bound WriteOnce when the bounty was claimed. Recompute the
    // committed hash from the cell named here and refuse a mismatch, so a payment
    // cannot be routed away from the worker who earned it.
    let bound = slot(CLAIMANT_HASH_SLOT);
    if bound.is_empty() || bound == "0".repeat(64) {
        ctx.error("This bounty binds no claimant, so there is nobody to pay.");
        return Ok(());
    }
    if bound != field_from_bytes_hex(claimant.trim().as_bytes()) {
        ctx.error("That cell is not the claimant this bounty is bound to. Nothing was paid.");
        return Ok(());
    }
    let reward = u64_from_field_hex(&slot(REWARD_SLOT));
    if reward == 0 {
        ctx.error("This bounty records no reward, so there is nothing to hand over.");
        return Ok(());
    }

    // TWO actions, ONE turn. The payment targets the submitting operator cell (a
    // `transfer` whose `from` is not its action's target needs the source cell's
    // `send` permission to be `None`, which a user cell's is not); the settle
    // targets the bounty and advances STATE.
    let paid = field_from_u64_hex(STATE_PAID);
    let actions = vec![
        json!({
            "method": "pay_bounty_reward",
            "effects": [
                { "kind": "transfer", "to": claimant.trim(), "amount": reward },
            ],
        }),
        json!({
            "target": cell,
            "method": "payout_bounty",
            "effects": [
                { "kind": "set_field", "index": STATE_SLOT, "value": paid },
                { "kind": "emit_event", "topic": "bounty-paid",
                  "data": [paid, field_from_u64_hex(reward), claimant.trim()] },
            ],
        }),
    ];
    let spinner = ctx.spinner("Paying the claimant and closing the bounty...");
    let data = submit_actions(cfg, actions, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    ctx.header("Payout");
    ctx.kv("Paid", &reward.to_string());
    ctx.kv("To", &crate::output::abbrev_hex(claimant.trim(), 8, 4));
    render_turn(ctx, &data, "Payout");
    if !data["accepted"].as_bool().unwrap_or(false) {
        ctx.info(
            "  Nothing moved: the payment and the PAID stamp are one turn, so a refused \
             payment takes the stamp with it.",
        );
    }
    Ok(())
}

/// The lifecycle stage as a word.
fn state_name(code: u64) -> &'static str {
    match code {
        STATE_OPEN => "open for claims",
        STATE_CLAIMED => "claimed, waiting on the work",
        STATE_SUBMITTED => "submitted, waiting on payment",
        STATE_PAID => "already paid and closed",
        _ => "not posted yet",
    }
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
