//! `/buy-credits` and `/credits` — the `$DREGG` earning surface.
//!
//! * **`/buy-credits`** issues the caller's deterministic per-user Solana deposit address
//!   (`dregg_pay::HdDeposit::deposit_address(discord_user_id)` — same user ⇒ same address), shows
//!   the price per run and the network, and explains how paying credits a run. It polls first so a
//!   payment that already landed is reflected immediately.
//! * **`/credits`** polls the watcher for the caller's deposit address (crediting any new payment,
//!   idempotently) then shows their persisted run-credit balance. (Formerly `/balance` — renamed:
//!   "balance" collided with the wallet's on-network DEC balance, a different money.)
//!
//! **Display honesty:** a payment-poll failure (real RPC outages exist now that the real
//! [`dregg_pay::SolanaWatcher`] is selectable) and a ledger-read failure are each surfaced as
//! "couldn't check right now — funds safe, retry", NEVER rendered as a `0` balance. A shown zero
//! is always a genuine ledger zero.
//!
//! A run-credit is spent by a paid `/dungeon` room narration (real Bedrock under a per-run budget);
//! an empty balance falls back to the free ollama/scripted tier. See [`crate::pay`].

use serenity::all::{
    CommandInteraction, Context, CreateCommand, CreateEmbed, CreateEmbedFooter,
    CreateInteractionResponse, CreateInteractionResponseMessage,
};

use crate::BotState;
use dregg_pay::{ChainId, CreditOutcome, Network, WatchError};

/// The bot-branded purple (matches the dungeon surface).
const PAY_COLOR: u32 = 0x7B2CBF;

/// Register `/buy-credits`.
pub fn register() -> CreateCommand {
    register_buy()
}

/// Register `/buy-credits`.
pub fn register_buy() -> CreateCommand {
    CreateCommand::new("buy-credits").description(
        "Get your $DREGG deposit address to buy real-AI dungeon run-credits (devnet/mock by default)",
    )
}

/// Register `/credits` (formerly `/balance` — the DEC wallet balance lives on
/// `/cipherclerk balance` and the `/start` **Wallet (DEC)** button; this is game credits).
pub fn register_balance() -> CreateCommand {
    CreateCommand::new("credits").description(
        "Show your $DREGG run-credits for real-AI dungeon runs (game credits, not DEC)",
    )
}

/// Register `/treasury`.
pub fn register_treasury() -> CreateCommand {
    CreateCommand::new("treasury").description(
        "Report the game treasury: the two-balance fuel/pile + its proven cross-chain holdings",
    )
}

/// A human name for a declared position's chain.
fn chain_label(chain: ChainId) -> String {
    match chain {
        ChainId::Solana => "Solana".to_string(),
        ChainId::ETHEREUM => "Ethereum".to_string(),
        ChainId::BASE => "Base".to_string(),
        ChainId::Evm(id) => format!("EVM chain {id}"),
        ChainId::Cosmos(_) => "Cosmos".to_string(),
    }
}

async fn respond_ephemeral(ctx: &Context, command: &CommandInteraction, embed: CreateEmbed) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

fn network_label(n: Network) -> &'static str {
    match n {
        Network::Devnet => "devnet (safe · mock)",
        Network::Mainnet => "mainnet (real funds)",
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Display honesty — a poll failure or a ledger-read failure is NEVER a "0".
// A user who just sent real $DREGG during an RPC outage must see "couldn't
// check right now, funds safe, retry", not "you have 0 credits".
// ─────────────────────────────────────────────────────────────────────────────

/// What the pre-display payment poll actually established — kept as a three-way
/// fact so "the watcher failed" can never collapse into "nothing new landed".
enum PollStatus {
    /// The poll succeeded and credited this many new run(s) (> 0).
    Credited(u64),
    /// The poll succeeded; no new payment had landed. (An honest nothing.)
    NothingNew,
    /// The poll FAILED (RPC outage / transport / refused account) — whether a
    /// payment landed is UNKNOWN right now. Funds are safe: crediting is
    /// idempotent by payment reference and the next successful poll picks it up.
    CheckFailed(WatchError),
}

/// Classify a [`crate::pay::PayState::poll_and_credit`] result for display.
fn poll_status(result: Result<Vec<CreditOutcome>, WatchError>) -> PollStatus {
    match result {
        Ok(outs) => {
            let credited: u64 = outs
                .iter()
                .map(|o| match o {
                    CreditOutcome::Credited { runs, .. } => *runs,
                    _ => 0,
                })
                .sum();
            if credited > 0 {
                PollStatus::Credited(credited)
            } else {
                PollStatus::NothingNew
            }
        }
        Err(e) => PollStatus::CheckFailed(e),
    }
}

/// The user-facing note for a poll outcome, appended to the embed description.
/// `None` when there is honestly nothing to say (a successful poll that found
/// nothing new).
fn poll_note(status: &PollStatus) -> Option<String> {
    match status {
        PollStatus::Credited(runs) => Some(format!(
            "\n\n✅ Just credited **{runs}** run(s) from a payment."
        )),
        PollStatus::NothingNew => None,
        PollStatus::CheckFailed(e) => Some(format!(
            "\n\n⚠️ **Couldn't check for new payments right now** — the payment watcher \
             errored (`{}`). **Your funds are safe:** a payment you already sent is still \
             on-chain, crediting is idempotent (never doubled, never lost), and the next \
             successful check picks it up. Retry `/credits` in a moment.",
            truncate_reason(&e.to_string()),
        )),
    }
}

/// The "Your balance" field text for a checked ledger read — a storage failure
/// says so instead of impersonating a zero.
fn balance_field(balance: &Result<u64, sqlx::Error>) -> String {
    match balance {
        Ok(b) => format!("{b} run(s)"),
        Err(_) => "unavailable right now (not a zero — retry)".to_string(),
    }
}

/// Bound an internal error string for embed copy (single line, capped length).
fn truncate_reason(reason: &str) -> String {
    let one_line = reason.replace('\n', " ");
    let mut out: String = one_line.chars().take(140).collect();
    if one_line.chars().count() > 140 {
        out.push('…');
    }
    out
}

/// `/buy-credits` — issue the caller's deposit address, price, and pay instructions.
pub async fn handle_buy(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let embed = execute_buy(state, command.user.id.get()).await;
    respond_ephemeral(ctx, command, embed).await;
}

/// Build the buy-credits surface (deposit address + price + poll outcome) —
/// the same read behind `/cipherclerk buy-credits` and the menus' button.
pub(crate) async fn execute_buy(state: &BotState, user_id: u64) -> CreateEmbed {
    let discord_id = user_id.to_string();
    let pay = &state.pay;

    // Persist the user→deposit-index map (stable address), then reflect any payment already
    // landed. The poll outcome is kept three-way (credited / nothing-new / CHECK FAILED) so an
    // RPC outage is surfaced honestly instead of masquerading as "nothing landed".
    let _ = pay.record_deposit_assignment(&discord_id).await;
    let poll = poll_status(pay.poll_and_credit(&discord_id));

    let address = pay.deposit_address_base58(&discord_id);
    let price = pay.price_per_run();
    let balance = pay.balance_checked(&discord_id).await;

    let mut desc = format!(
        "Send **$DREGG** to your personal deposit address below. Each **{price}** atomic $DREGG buys **one** real-AI dungeon run. Your address is deterministic — it is always the same for you.\n\n**Your deposit address**\n```\n{address}\n```\nNetwork: **{}**\n\nAfter you pay, run `/credits` (or `/buy-credits` again) to credit it. A paid `/dungeon` room is narrated by real Bedrock; with no credits you get the free (ollama/scripted) narrator.",
        network_label(pay.network()),
    );
    if let Some(note) = poll_note(&poll) {
        desc.push_str(&note);
    }

    CreateEmbed::new()
        .title("Buy real-AI dungeon credits")
        .description(desc)
        .color(PAY_COLOR)
        .field("Price per run", format!("{price} atomic $DREGG"), true)
        .field("Your balance", balance_field(&balance), true)
        .footer(CreateEmbedFooter::new(
            "custodial HD-deposit (\"B\") model · devnet/mock by default · mainnet is an operator flip",
        ))
}

/// `/credits` — poll for new payments, then show the caller's run-credit balance.
pub async fn handle_balance(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let embed = execute_balance(state, command.user.id.get()).await;
    respond_ephemeral(ctx, command, embed).await;
}

/// Build the caller's run-credit balance (poll + checked ledger read) — the
/// same read behind `/cipherclerk credits` and the menus' button.
pub(crate) async fn execute_balance(state: &BotState, user_id: u64) -> CreateEmbed {
    let discord_id = user_id.to_string();
    let pay = &state.pay;

    // Three-way poll status + checked ledger read: an RPC outage or a storage failure is
    // told to the user as exactly that — never rendered as "you have 0 credits".
    let poll = poll_status(pay.poll_and_credit(&discord_id));
    let balance = pay.balance_checked(&discord_id).await;
    let price = pay.price_per_run();

    let mut desc = match &balance {
        Ok(b) => format!(
            "You have **{b}** run-credit(s). Each paid `/dungeon` room narration by real Bedrock spends one; with none you get the free (ollama/scripted) narrator.\n\nBuy more with `/buy-credits` — send **{price}** atomic $DREGG per run to your deposit address."
        ),
        Err(_) => format!(
            "⚠️ **Your balance can't be read right now** (a storage hiccup on our side — this is NOT a zero). Your credits are persisted in the ledger and are safe; retry `/credits` in a moment.\n\nBuying still works the same: `/buy-credits` — **{price}** atomic $DREGG per run to your deposit address."
        ),
    };
    if let Some(note) = poll_note(&poll) {
        desc.push_str(&note);
    }

    CreateEmbed::new()
        .title("Your $DREGG run-credits")
        .description(desc)
        .color(PAY_COLOR)
        .field(
            "The three monies",
            "**DEC** — the on-network devnet currency your cipherclerk holds \
             (`/cipherclerk balance`). **$DREGG** — the token; buys these run-credits. \
             **computrons** — the metered unit of compute a turn consumes.",
            false,
        )
        .footer(CreateEmbedFooter::new(
            "credits persist across restarts (sqlite) · devnet/mock by default",
        ))
}

/// `/treasury` — report the two-balance treasury (the revenue that landed) and the
/// treasury's declared cross-chain positions + proven cross-chain holdings.
///
/// The fuel/pile are the LIVE revenue-landing accounting: a detected USDC payment fuels the
/// tank (burned per real-AI run), a `$DREGG` payment grows the pile (see [`crate::pay`]). The
/// multichain view is the non-custodial cross-chain report: it counts only proof-of-holdings
/// facts that bind to the treasury's own declared addresses and carry a real consensus proof.
/// A live proof-of-holdings relayer feed is a named residual — until one is wired the proven
/// total reflects the facts currently available (none in the interim), while the DECLARED
/// positions are always shown.
pub async fn handle_treasury(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let embed = execute_treasury(state).await;
    respond_ephemeral(ctx, command, embed).await;
}

/// Build the two-balance treasury report — the same read behind `/cipherclerk
/// treasury` and the menus' button.
pub(crate) async fn execute_treasury(state: &BotState) -> CreateEmbed {
    let pay = &state.pay;

    let fuel = pay.treasury_fuel();
    let pile = pay.treasury_pile();

    let mut desc = format!(
        "**The two-balance treasury** — where detected game revenue lands.\n\n• **Fuel (USDC):** `{fuel}` atomic — burned per real-AI run; fails closed (must-refuel) on empty.\n• **Pile ($DREGG):** `{pile}` atomic — the accumulating illiquid holding.\n\nA USDC payment fuels the tank; a $DREGG payment grows the pile. Every run burns USD fuel regardless of how it was paid.\n\n**Declared cross-chain positions** (non-custodial — proven, not held):"
    );

    let slots = pay.treasury_slots();
    if slots.is_empty() {
        desc.push_str("\n_(none declared)_");
    } else {
        for s in slots {
            desc.push_str(&format!("\n• `{}` — {}", chain_label(s.chain), s.label));
        }
    }

    // Report proven cross-chain holdings over whatever facts are currently available. With
    // no live proof-of-holdings relayer wired yet (a named residual), this is the empty set
    // in the interim; the accessor is the exposed surface a relayer feeds.
    let held = pay.treasury_holdings(&[]);
    desc.push_str(&format!(
        "\n\n**Proven cross-chain holdings:** {} position(s) proven across {} chain(s), total `{}` atomic.\n_Proven holdings require a proof-of-holdings relayer pointed at these addresses (a named residual); the declared positions above are the treasury's non-custodial claim._",
        held.holdings.len(),
        held.chains_proven(),
        held.total_amount(),
    ));

    CreateEmbed::new()
        .title("Game treasury")
        .description(desc)
        .color(PAY_COLOR)
        .field("Fuel (USDC atomic)", format!("{fuel}"), true)
        .field("Pile ($DREGG atomic)", format!("{pile}"), true)
        .footer(CreateEmbedFooter::new(
            "revenue-landing accounting persists across restart (sqlite) · non-custodial cross-chain view · devnet/mock by default",
        ))
}
