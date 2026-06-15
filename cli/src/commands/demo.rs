//! `dregg demo` — a guided quickstart a newcomer can run against a live node.
//!
//! It drives the full nameservice lifecycle end-to-end through the node's
//! verified commit path, narrating each step:
//!
//!   1. check the node + verified-execution surface
//!   2. unlock the cipherclerk (so turns can be signed)        [needs --passphrase]
//!   3. read the operator identity + fund its cell via the faucet
//!   4. register a name (SetField + EmitEvent on the verified path)
//!   5. resolve it (read the slots back)
//!   6. transfer it to a new owner
//!   7. revoke it (one-way tombstone) and resolve again to see the change
//!
//! Every mutation is a real signed turn ordered into the blocklace and
//! (when proving is on) proven with a STARK. This is the same path a human
//! operator uses; nothing here is a mock.

use crate::config::Config;
use crate::output::Context;

use super::name;
use super::{get_json, post_json};

/// Run the quickstart. `passphrase` unlocks the node's cipherclerk; without it
/// we still demo the read-only surface and explain what's needed.
pub async fn run(
    cfg: &Config,
    ctx: &Context,
    name_arg: Option<String>,
    passphrase: Option<String>,
    faucet_amount: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    let the_name = name_arg.unwrap_or_else(|| "alice.dregg".to_string());

    ctx.header("dregg demo — nameservice quickstart");
    ctx.info("  A real turn flows: CLI → node /turn/submit → verified commit path → proof.");
    ctx.info(&format!("  Node: {}\n", cfg.node.url));

    // ── 1. Node health + verified-execution surface ─────────────────────────
    step(ctx, 1, "Checking the node");
    let status = get_json(cfg, "/status").await.map_err(|e| {
        format!(
            "cannot reach node at {} — start one with `dregg-node run --enable-faucet --prove-turns` ({e})",
            cfg.node.url
        )
    })?;
    let producer = status["state_producer"].as_str().unwrap_or("rust");
    let proving = status["full_turn_proving"].as_bool().unwrap_or(false);
    let covered = status["producer_covered_effects"].as_u64().unwrap_or(0);
    ctx.kv(
        "Health",
        if status["healthy"].as_bool().unwrap_or(false) {
            "healthy"
        } else {
            "unhealthy"
        },
    );
    ctx.kv(
        "State producer",
        &format!(
            "{} ({} effects on the verified path)",
            if producer == "lean" {
                "LEAN (verified)"
            } else {
                "rust (legacy — set DREGG_LEAN_PRODUCER=1)"
            },
            covered
        ),
    );
    ctx.kv(
        "Full-turn proving",
        if proving {
            "on (STARK per turn)"
        } else {
            "off"
        },
    );

    // ── 2. Unlock ───────────────────────────────────────────────────────────
    step(ctx, 2, "Unlocking the cipherclerk");
    let mut cfg = cfg.clone();
    // A gateway-fronted node (like the public devnet) does not expose
    // /cipherclerk/unlock — it is unlocked at boot and you carry its bearer
    // token instead (--token / DREGG_API_TOKEN). Detect that case up front.
    let has_token = cfg.node.token.as_deref().is_some_and(|t| !t.is_empty());
    let already_unlocked = || async {
        get_json(&cfg, "/api/node/identity")
            .await
            .map(|i| i["unlocked"].as_bool().unwrap_or(false))
            .unwrap_or(false)
    };
    match passphrase {
        Some(ref pass) => {
            match post_json(
                &cfg,
                "/cipherclerk/unlock",
                &serde_json::json!({ "passphrase": pass }),
            )
            .await
            {
                Ok(unlock) => {
                    let token = unlock["bearer_token"].as_str().unwrap_or("").to_string();
                    if token.is_empty() {
                        return Err("unlock did not return a bearer token".into());
                    }
                    cfg.node.token = Some(token);
                    ctx.success("Cipherclerk unlocked (bearer token acquired).");
                }
                Err(e) if has_token && already_unlocked().await => {
                    ctx.warn(&format!(
                        "unlock endpoint unavailable ({e}) — node is already unlocked; \
                         continuing with your configured bearer token."
                    ));
                }
                Err(e) => return Err(format!("unlock failed: {e}").into()),
            }
        }
        None if has_token && already_unlocked().await => {
            ctx.success("Node already unlocked; using your configured bearer token.");
        }
        None => {
            ctx.warn("No --passphrase given; cannot sign turns.");
            ctx.info(
                "  Re-run with `dregg demo --passphrase <pass>` to drive the full mutating flow,",
            );
            ctx.info("  or set DREGG_API_TOKEN if the node is already unlocked (public devnet).");
            ctx.info("  (On a fresh node, the first unlock SETS the passphrase.)");
            return Ok(());
        }
    }

    // ── 3. Identity + faucet ────────────────────────────────────────────────
    step(ctx, 3, "Funding the operator cell");
    let ident = get_json(&cfg, "/api/node/identity").await?;
    let pubkey = ident["public_key"].as_str().unwrap_or("").to_string();
    let agent_cell = ident["agent_cell"].as_str().unwrap_or("").to_string();
    if pubkey.is_empty() || agent_cell.is_empty() {
        return Err("node did not return an operator identity".into());
    }
    ctx.kv(
        "Operator cell",
        &crate::output::abbrev_hex(&agent_cell, 8, 4),
    );
    let faucet = post_json(
        &cfg,
        "/api/faucet",
        &serde_json::json!({ "recipient": agent_cell, "amount": faucet_amount, "public_key": pubkey }),
    )
    .await
    .map_err(|e| format!("faucet request failed (is the node started with --enable-faucet?): {e}"))?;
    if faucet["success"].as_bool().unwrap_or(false) {
        ctx.success(&format!("Funded {faucet_amount} computrons."));
    } else {
        let err = faucet["error"].as_str().unwrap_or("unknown");
        // Already funded is fine; only hard-fail on real errors.
        ctx.warn(&format!(
            "faucet: {err} (continuing — cell may already be funded)"
        ));
    }

    // ── 3b. Recycle the demo cell if a previous run tombstoned it ──────────
    // A revoke is one-way on a programmed registry cell; the demo cell carries
    // no registry program, so a re-run may clear the previous run's tombstone
    // and host a fresh lifecycle. Without this, every demo after the first
    // resolves as REVOKED at step 5.
    let detail = get_json(&cfg, &format!("/api/cell/{agent_cell}")).await?;
    let revoked_slot = detail["fields"]
        .as_array()
        .and_then(|f| f.get(name::REVOKED_SLOT))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    if !revoked_slot.is_empty() && !revoked_slot.trim_start_matches('0').is_empty() {
        let clear = post_json(
            &cfg,
            "/api/turns/submit",
            &serde_json::json!({
                "agent": agent_cell,
                "nonce": 0,
                "fee": 1000,
                "memo": "demo: recycle (clear previous tombstone)",
                "actions": [{ "effects": [
                    { "kind": "set_field", "index": name::REVOKED_SLOT, "value": "0" }
                ]}],
            }),
        )
        .await?;
        if clear["accepted"].as_bool().unwrap_or(false) {
            ctx.info("  Recycled the demo cell (cleared a previous run's tombstone).");
        } else {
            ctx.warn(&format!(
                "could not recycle the demo cell: {} — the resolve step may show REVOKED",
                clear["error"].as_str().unwrap_or("unknown")
            ));
        }
    }

    // ── 4. Register ─────────────────────────────────────────────────────────
    step(ctx, 4, &format!("Registering '{the_name}'"));
    name::run(
        name::NameCommand::Register {
            name: the_name.clone(),
            expiry: 1_000_000,
            owner: None,
            cell: Some(agent_cell.clone()),
            fee: 1000,
        },
        &cfg,
        ctx,
    )
    .await?;

    // ── 5. Resolve ──────────────────────────────────────────────────────────
    step(ctx, 5, &format!("Resolving '{the_name}'"));
    name::run(
        name::NameCommand::Resolve {
            name: the_name.clone(),
            cell: Some(agent_cell.clone()),
        },
        &cfg,
        ctx,
    )
    .await?;

    // ── 6. Transfer ─────────────────────────────────────────────────────────
    step(ctx, 6, &format!("Transferring '{the_name}' to bob"));
    name::run(
        name::NameCommand::Transfer {
            name: the_name.clone(),
            new_owner: "bob".to_string(),
            cell: Some(agent_cell.clone()),
            fee: 1000,
        },
        &cfg,
        ctx,
    )
    .await?;

    // ── 7. Revoke + resolve again ───────────────────────────────────────────
    step(ctx, 7, &format!("Revoking '{the_name}' (one-way)"));
    name::run(
        name::NameCommand::Revoke {
            name: the_name.clone(),
            cell: Some(agent_cell.clone()),
            fee: 1000,
        },
        &cfg,
        ctx,
    )
    .await?;
    name::run(
        name::NameCommand::Resolve {
            name: the_name.clone(),
            cell: Some(agent_cell.clone()),
        },
        &cfg,
        ctx,
    )
    .await?;

    ctx.header("Demo complete");
    ctx.success("A full nameservice lifecycle ran end-to-end on the verified commit path.");
    ctx.info("  Try it yourself:");
    ctx.info("    dregg name register myname.dregg --expiry 2000000");
    ctx.info("    dregg name resolve  myname.dregg");
    ctx.info("    dregg turn status <turn-hash>");
    Ok(())
}

fn step(ctx: &Context, n: usize, title: &str) {
    ctx.header(&format!("Step {n}: {title}"));
}
