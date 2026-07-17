//! `/export` — **mint your VERIFIED Descent win as a 1-of-1 SPL NFT** (backlog #17).
//!
//! "Earned-ness travels": the NFT is refused unless it carries a real dregg proof —
//! [`dregg_pay::DreggAchievementProof`] MUST hold a non-zero commitment + a non-empty
//! cheevo id ([`dregg_pay::nft_mint`]'s own fail-closed gate). The commitment we carry is
//! the invoker's **verified board completion id** — the content address of a run that the
//! `/descent` no-cheat board re-executed to the win ([`ugc_dregg::verify_completion`]);
//! nothing self-asserted ever reaches the memo.
//!
//! The mint pipeline is the committed [`dregg_pay::NftMinter`] (HD custody off the SAME
//! operator seed the sweeper uses): build + sign the 1-of-1 export transaction
//! (create mint → init → ATA → mint EXACTLY 1 → revoke mint authority → proof memo),
//! then submit it through the configured Solana RPC (`DREGG_PAY_RPC`, devnet default).
//!
//! **Verify it yourself** (the `/send` register): the response shows the mint address,
//! the proof memo (`dregg-nft/v1|<cheevo>|<base58 commitment>`), the custody authority,
//! and whether the authority signature over the exact transaction message verifies —
//! and an RPC refusal (an unfunded devnet authority, a down node) is reported as ITS OWN
//! words, never smoothed into a fake success.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption,
};

use base64::Engine as _;
use dregg_pay::{DreggAchievementProof, MintNftRequest, NftMinter};

use crate::BotState;
use crate::commands::{ack, descent};
use crate::embeds;

/// The Solana RPC the export talks to: the operator's (`DREGG_PAY_RPC`) or devnet.
fn rpc_url() -> String {
    std::env::var("DREGG_PAY_RPC").unwrap_or_else(|_| "https://api.devnet.solana.com".to_string())
}

/// Register `/export` — export your best verified Descent win as a 1-of-1 SPL NFT.
pub fn register() -> CreateCommand {
    CreateCommand::new("export")
        .description(
            "Export your best VERIFIED Descent win as a 1-of-1 SPL NFT carrying the proof memo",
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "wallet",
                "The Solana wallet (base58) that will OWN the NFT",
            )
            .required(true),
        )
}

/// The `wallet` option (a top-level option — `/export` has no subcommands).
fn wallet_option(command: &CommandInteraction) -> Option<String> {
    command
        .data
        .options
        .iter()
        .find(|o| o.name == "wallet")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

/// Route `/export`: verified win → proof memo → built+signed 1-of-1 → RPC submit.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    ack::defer_slash(ctx, command, true).await;

    let raw_wallet = wallet_option(command).unwrap_or_default();
    let recipient = match dregg_pay::parse_pubkey_base58(raw_wallet.trim()) {
        Ok(pk) => pk,
        Err(e) => {
            let embed = embeds::error_embed(
                "Not a Wallet",
                &format!("`{raw_wallet}` did not parse as a base58 Solana pubkey: {e}"),
            );
            ack::edit_slash(ctx, command, embed, Vec::new()).await;
            return;
        }
    };

    // THE EARNED-NESS GATE: the invoker's best VERIFIED completion on the live no-cheat
    // board (read on the descent store thread — the board only holds re-executed wins).
    let player = command.user.name.clone();
    let win = tokio::task::spawn_blocking(move || descent::verified_win_of(&player))
        .await
        .ok()
        .flatten();
    let Some(win) = win else {
        let embed = embeds::warning_embed(
            "Nothing Verified To Export",
            "You hold no VERIFIED win on the `/descent` no-cheat board — the NFT only ever \
             carries a re-executed win, never a claim. Win `/descent play` first.",
        );
        ack::edit_slash(ctx, command, embed, Vec::new()).await;
        return;
    };

    let short_universe = &win.universe_id_hex[..16.min(win.universe_id_hex.len())];
    let proof = DreggAchievementProof {
        commitment: win.completion_id,
        cheevo_id: format!("descent:daily-win:{short_universe}"),
    };

    // A fresh blockhash from the RPC — the message signs over it, so it must be real.
    let rpc = rpc_url();
    let recent_blockhash = match fetch_latest_blockhash(&rpc).await {
        Ok(bh) => bh,
        Err(e) => {
            let embed = embeds::error_embed(
                "No Recent Blockhash",
                &format!(
                    "The Solana RPC at `{rpc}` did not supply a blockhash: {e}\n\nA signed \
                     export must commit to a live blockhash; nothing was built."
                ),
            );
            ack::edit_slash(ctx, command, embed, Vec::new()).await;
            return;
        }
    };

    // Build + sign through the committed HD-custody minter (fail-closed: a zero
    // commitment, a non-1 supply, or a bad recipient is the builder's own refusal).
    let minter = NftMinter::new(&state.pay.config);
    let nonce = u64::from_le_bytes(
        win.completion_id[..8]
            .try_into()
            .expect("8 bytes off a 32-byte commitment"),
    );
    let request = MintNftRequest {
        recipient,
        supply: 1,
        proof,
        recent_blockhash,
    };
    let built = match minter.build(&request, nonce) {
        Ok(b) => b,
        Err(e) => {
            let embed = embeds::error_embed(
                "Export Refused",
                &format!("The 1-of-1 builder refused: {e}"),
            );
            ack::edit_slash(ctx, command, embed, Vec::new()).await;
            return;
        }
    };

    let sig_verifies = built.authority_signature_verifies();
    let memo = String::from_utf8_lossy(&built.proof_memo).to_string();
    let submit = send_transaction(&rpc, &built.tx_bytes).await;

    let mut embed = embeds::success_embed("Verified Win → 1-of-1 SPL NFT")
        .description(format!(
            "**{}** — your verified {}‑turn win, exported as a single-unit SPL mint whose \
             mint authority is revoked in the same transaction (provably 1-of-1).",
            win.universe_name, win.turns
        ))
        .field(
            "Mint",
            format!("`{}`", bs58::encode(built.mint).into_string()),
            true,
        )
        .field(
            "Owner (your ATA)",
            format!("`{}`", bs58::encode(built.recipient_ata).into_string()),
            true,
        )
        .field("Proof memo", format!("`{memo}`"), false)
        .field(
            "Verify it yourself",
            format!(
                "The custody authority `{}` signed the exact transaction message — \
                 re-checked here: **{}**. The memo's commitment is your board completion \
                 id; anyone can `/descent board` and re-verify the run it names.",
                bs58::encode(built.authority).into_string(),
                if sig_verifies {
                    "signature verifies"
                } else {
                    "SIGNATURE DID NOT VERIFY (refuse this export)"
                }
            ),
            false,
        );

    embed = match submit {
        Ok(sig) => embed.field(
            "Submitted",
            format!("transaction `{sig}` via `{rpc}`"),
            false,
        ),
        Err(why) => embed.field(
            "Not Landed (the RPC's own words)",
            format!(
                "`{rpc}` refused the submit: {why}\n\nThe build + signature above are \
                 still real and inspectable; a funded custody authority re-submits the \
                 same bytes."
            ),
            false,
        ),
    };

    ack::edit_slash(ctx, command, embed, Vec::new()).await;
}

// ─────────────────────────────────────────────────────────────────────────────
// Minimal Solana JSON-RPC (reqwest) — getLatestBlockhash + sendTransaction.
// ─────────────────────────────────────────────────────────────────────────────

/// `getLatestBlockhash` → the 32-byte blockhash.
async fn fetch_latest_blockhash(rpc: &str) -> Result<[u8; 32], String> {
    let body = serde_json::json!({
        "jsonrpc": "2.0", "id": 1, "method": "getLatestBlockhash",
        "params": [{"commitment": "finalized"}]
    });
    let v = rpc_call(rpc, body).await?;
    let hash = v
        .pointer("/result/value/blockhash")
        .and_then(|h| h.as_str())
        .ok_or_else(|| format!("no blockhash in response: {v}"))?;
    let bytes = bs58::decode(hash)
        .into_vec()
        .map_err(|e| format!("blockhash `{hash}` is not base58: {e}"))?;
    bytes
        .try_into()
        .map_err(|_| format!("blockhash `{hash}` is not 32 bytes"))
}

/// `sendTransaction` (base64) → the transaction signature.
async fn send_transaction(rpc: &str, tx_bytes: &[u8]) -> Result<String, String> {
    let encoded = base64::engine::general_purpose::STANDARD.encode(tx_bytes);
    let body = serde_json::json!({
        "jsonrpc": "2.0", "id": 1, "method": "sendTransaction",
        "params": [encoded, {"encoding": "base64"}]
    });
    let v = rpc_call(rpc, body).await?;
    if let Some(err) = v.pointer("/error/message").and_then(|m| m.as_str()) {
        return Err(err.to_string());
    }
    v.get("result")
        .and_then(|r| r.as_str())
        .map(|s| s.to_string())
        .ok_or_else(|| format!("no signature in response: {v}"))
}

/// One JSON-RPC POST, honest transport errors.
async fn rpc_call(rpc: &str, body: serde_json::Value) -> Result<serde_json::Value, String> {
    let client = reqwest::Client::new();
    let resp = client
        .post(rpc)
        .json(&body)
        .send()
        .await
        .map_err(|e| format!("transport: {e}"))?;
    resp.json::<serde_json::Value>()
        .await
        .map_err(|e| format!("bad JSON from the RPC: {e}"))
}
