//! Privacy-voting commands — the demoable starbridge-app flow over a live node.
//!
//! These drive the `starbridge-privacy-voting` poll/ballot cells through the
//! node's `/turn/submit` JSON ingress (a real signed call-forest on the
//! verified commit path). Polls and ballots are factory-born cells whose slot
//! caveats *are* the voting rules:
//!
//! | Poll slot | Meaning   | Caveat      |    | Ballot slot | Meaning  | Caveat     |
//! |:--------:|------------|-------------|----|:----------:|----------|------------|
//! | 2        | question   | `WriteOnce` |    | 2          | poll_ref | `WriteOnce`|
//! | 3/4/5    | tallies    | `Monotonic` |    | 3          | vote     | `WriteOnce`|
//! | 6        | closed     | `WriteOnce` |    |            |          |            |
//!
//! The encodings mirror `starbridge_privacy_voting` + `app-framework`'s
//! `field_from_bytes` / `field_from_u64` byte-for-byte. Pass `--cell <id>` for
//! the seeded poll cell (`privacy-voting-poll` in genesis); the gating bites
//! when you, e.g., try to shrink a tally (`Monotonic`) or re-write a closed
//! poll (`WriteOnce`).

use clap::Subcommand;

use crate::config::Config;
use crate::output::Context;

use super::name::{field_from_bytes_hex, field_from_u64_hex};
use super::{get_json, post_json};

// Poll-cell slot schema — mirrors starbridge-apps/privacy-voting/src/lib.rs.
const QUESTION_HASH_SLOT: usize = 2;
const TALLY_YES_SLOT: usize = 3;
const TALLY_NO_SLOT: usize = 4;
const TALLY_ABSTAIN_SLOT: usize = 5;
const CLOSED_SLOT: usize = 6;

// Vote choice codes.
const VOTE_YES: u64 = 1;
const VOTE_NO: u64 = 2;
const VOTE_ABSTAIN: u64 = 3;
const CLOSED_MARKER: u64 = 1;

#[derive(Subcommand)]
pub enum VotingCommand {
    /// Open a poll: write its question (write-once) and emit `poll-opened`.
    ///
    ///   dregg voting open "Ship the release?" --cell <poll_cell>
    Open {
        /// The poll question text.
        question: String,
        /// The poll cell (the factory-born `privacy-voting-poll` cell).
        #[arg(long)]
        cell: String,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Record a vote: bump the matching tally to `--tally` (monotone).
    ///
    /// `--tally` is the post-increment count (read the current tally, add one).
    /// The poll's `Monotonic` caveat rejects any value below the current tally,
    /// so a stale/replayed value cannot shrink the board.
    ///
    ///   dregg voting tally yes --tally 1 --cell <poll_cell>
    Tally {
        /// The choice: `yes`, `no`, or `abstain`.
        choice: String,
        /// The post-increment tally value to write.
        #[arg(long)]
        tally: u64,
        /// The poll cell.
        #[arg(long)]
        cell: String,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Close the poll (one-way `closed` slot) and emit `poll-closed`.
    Close {
        /// The poll cell.
        #[arg(long)]
        cell: String,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Show a poll's state: question binding, tallies, closed flag.
    Show {
        /// The poll cell.
        #[arg(long)]
        cell: String,
    },
}

pub async fn run(
    command: VotingCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match command {
        VotingCommand::Open {
            question,
            cell,
            fee,
        } => open(cfg, ctx, &question, &cell, fee).await,
        VotingCommand::Tally {
            choice,
            tally,
            cell,
            fee,
        } => record_tally(cfg, ctx, &choice, tally, &cell, fee).await,
        VotingCommand::Close { cell, fee } => close(cfg, ctx, &cell, fee).await,
        VotingCommand::Show { cell } => show(cfg, ctx, &cell).await,
    }
}

fn choice_code(choice: &str) -> Result<(u64, usize, &'static str), Box<dyn std::error::Error>> {
    match choice.to_lowercase().as_str() {
        "yes" | "y" => Ok((VOTE_YES, TALLY_YES_SLOT, "YES")),
        "no" | "n" => Ok((VOTE_NO, TALLY_NO_SLOT, "NO")),
        "abstain" | "a" => Ok((VOTE_ABSTAIN, TALLY_ABSTAIN_SLOT, "ABSTAIN")),
        other => Err(format!("unknown choice '{other}' (use yes / no / abstain)").into()),
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
    let data = post_json(cfg, "/turn/submit", &req).await?;
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

async fn open(
    cfg: &Config,
    ctx: &Context,
    question: &str,
    cell: &str,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let q = field_from_bytes_hex(question.as_bytes());
    let effects = vec![
        json!({ "kind": "set_field", "index": QUESTION_HASH_SLOT, "value": q }),
        json!({ "kind": "emit_event", "topic": "poll-opened", "data": [q] }),
    ];
    if !cfg.is_json() {
        ctx.header("Open poll");
        ctx.kv("Cell", &crate::output::abbrev_hex(cell, 8, 4));
        ctx.kv("Question", question);
    }
    let spinner = ctx.spinner("Opening poll (sign → execute → prove)...");
    let data = submit_effects(cfg, cell, "open_poll", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    render_turn(ctx, &data, "Open");
    Ok(())
}

async fn record_tally(
    cfg: &Config,
    ctx: &Context,
    choice: &str,
    tally: u64,
    cell: &str,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let (code, slot, label) = choice_code(choice)?;
    let effects = vec![
        json!({ "kind": "set_field", "index": slot, "value": field_from_u64_hex(tally) }),
        json!({ "kind": "emit_event", "topic": "vote-cast", "data": [field_from_u64_hex(code)] }),
    ];
    if !cfg.is_json() {
        ctx.header(&format!("Record {label} tally"));
        ctx.kv("Cell", &crate::output::abbrev_hex(cell, 8, 4));
        ctx.kv("New tally", &tally.to_string());
    }
    let spinner = ctx.spinner("Recording tally (Monotonic-gated)...");
    let data = submit_effects(cfg, cell, "record_tally", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    render_turn(ctx, &data, "Tally");
    if !data["accepted"].as_bool().unwrap_or(false) {
        ctx.info("  A rejection here is the Monotonic caveat biting: a tally cannot decrease.");
    }
    Ok(())
}

async fn close(
    cfg: &Config,
    ctx: &Context,
    cell: &str,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let marker = field_from_u64_hex(CLOSED_MARKER);
    let effects = vec![
        json!({ "kind": "set_field", "index": CLOSED_SLOT, "value": marker }),
        json!({ "kind": "emit_event", "topic": "poll-closed", "data": [marker] }),
    ];
    let spinner = ctx.spinner("Closing poll (one-way)...");
    let data = submit_effects(cfg, cell, "close_poll", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    ctx.header("Close poll");
    render_turn(ctx, &data, "Close");
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
    let closed = !slot(CLOSED_SLOT).is_empty() && slot(CLOSED_SLOT) != zero;

    if cfg.is_json() {
        ctx.json_stdout(&serde_json::json!({
            "cell": cell,
            "found": found,
            "tally_yes": u64_at(TALLY_YES_SLOT),
            "tally_no": u64_at(TALLY_NO_SLOT),
            "tally_abstain": u64_at(TALLY_ABSTAIN_SLOT),
            "closed": closed,
        }));
        return Ok(());
    }

    ctx.header("Poll");
    ctx.kv("Cell", &crate::output::abbrev_hex(cell, 8, 4));
    if !found {
        ctx.error("Cell not found in the ledger.");
        return Ok(());
    }
    ctx.kv("YES", &u64_at(TALLY_YES_SLOT).to_string());
    ctx.kv("NO", &u64_at(TALLY_NO_SLOT).to_string());
    ctx.kv("ABSTAIN", &u64_at(TALLY_ABSTAIN_SLOT).to_string());
    if closed {
        ctx.kv("Status", "CLOSED");
    } else {
        ctx.kv("Status", "open");
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
