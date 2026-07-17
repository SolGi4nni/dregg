//! **The subscription DM dispatcher** — the delivery the Subscription panel promised but no
//! code performed (backlog 2026-07-17 #6).
//!
//! Before this module, `Subscribe` inserted a row that only a COUNT ever read, and `Publish`
//! enqueued a `message_hash` on the node queue while the message BODY went nowhere — "You will
//! receive DMs" was fiction. Now a successful publish fans the body out as DMs to every
//! subscriber of the queue's namespace path, and the publisher's receipt reports exactly how
//! many were delivered/failed.
//!
//! HONEST SCOPE (stated on the panel too): the node queue commits only the message HASH (the
//! integrity anchor); the body rides this bot's Discord DM fan-out, so delivery is bot-local —
//! a publish made while the bot is down is not replayed, and a subscriber whose DMs are closed
//! is reported as failed, not silently dropped.

use serenity::all::{Context, CreateMessage, UserId};

use crate::BotState;
use crate::embeds;

/// The facts of one successful publish — built by the dashboard's publish submit, consumed by
/// [`fan_out`].
pub struct PublishFanout {
    /// The queue's namespace path (`/discord/<guild>/<name>`), the subscription key.
    pub namespace_path: String,
    /// The queue's short name.
    pub queue_name: String,
    /// The message body the publisher typed.
    pub message: String,
    /// The blake3 hash the node queue committed (the integrity anchor a subscriber can check).
    pub message_hash: String,
    /// The enqueue position the node reported.
    pub position: u64,
    /// The publisher's Discord id (excluded from the fan-out — they hold the receipt).
    pub publisher: String,
}

/// DM the message to every subscriber of the path. Returns the honest one-line delivery note
/// the publisher's receipt embed carries.
pub async fn fan_out(ctx: &Context, state: &BotState, fanout: PublishFanout) -> String {
    let subscribers = match state
        .db
        .list_starbridge_queue_subscribers(&fanout.namespace_path)
        .await
    {
        Ok(subs) => subs,
        Err(e) => return format!("subscriber lookup failed ({e}) — nobody was DMed"),
    };

    let mut delivered = 0usize;
    let mut failed = 0usize;
    let mut skipped_self = 0usize;
    for discord_id in &subscribers {
        if *discord_id == fanout.publisher {
            skipped_self += 1;
            continue;
        }
        let Ok(uid) = discord_id.parse::<u64>() else {
            failed += 1;
            continue;
        };
        let embed = embeds::dregg_embed(&format!("New message in {}", fanout.queue_name))
            .description(body_preview(&fanout.message))
            .field("Queue", format!("`{}`", fanout.namespace_path), false)
            .field("Position", fanout.position.to_string(), true)
            .field(
                "Committed hash (verify: blake3 of the body)",
                format!("`{}`", fanout.message_hash),
                false,
            );
        let sent = match UserId::new(uid).create_dm_channel(&ctx.http).await {
            Ok(chan) => chan
                .id
                .send_message(&ctx.http, CreateMessage::new().embed(embed))
                .await
                .is_ok(),
            Err(_) => false,
        };
        if sent {
            delivered += 1;
        } else {
            failed += 1;
        }
    }

    match (subscribers.len(), delivered, failed) {
        (0, _, _) => "no subscribers yet — nobody to DM".to_string(),
        (_, d, 0) => format!(
            "DMed {d} subscriber(s){}",
            if skipped_self > 0 {
                " (you hold this receipt instead)"
            } else {
                ""
            }
        ),
        (_, d, f) => format!(
            "DMed {d} subscriber(s); {f} undeliverable (DMs closed or unknown user) — \
             the queue entry itself committed either way"
        ),
    }
}

/// The DM body: the full message when short, truncated with an honest marker when long.
fn body_preview(message: &str) -> String {
    const MAX: usize = 1800;
    if message.chars().count() <= MAX {
        message.to_string()
    } else {
        let mut out: String = message.chars().take(MAX).collect();
        out.push_str("\n… (truncated — the committed hash covers the FULL body)");
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A short body rides whole; a long one is truncated with the honest marker (never a
    /// silent cut — the hash covers the full body and the DM says so).
    #[test]
    fn the_dm_body_is_honest_about_truncation() {
        assert_eq!(body_preview("hello"), "hello");
        let long = "x".repeat(4000);
        let preview = body_preview(&long);
        assert!(preview.chars().count() < 2000);
        assert!(preview.contains("truncated"));
        assert!(preview.contains("FULL body"));
    }
}
