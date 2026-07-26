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
    let covered = status["producer_root_agreeing_effects"]
        .as_u64()
        .unwrap_or(0);
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
    ensure_funded(&cfg, ctx, &agent_cell, &pubkey, faucet_amount).await?;

    // ── 3b. Recycle the demo cell if a previous run tombstoned it ──────────
    // A revoke is one-way on a programmed registry cell; the demo cell carries
    // no registry program, so a re-run may clear the previous run's tombstone
    // and host a fresh lifecycle. Without this, every demo after the first
    // resolves as REVOKED at step 5.
    let detail = get_json(&cfg, &format!("/api/cell/{agent_cell}")).await?;
    // Every turn this demo commits ticks the agent cell's nonce when it is
    // APPLIED. That is the signal the steps below wait on; see `await_applied`.
    let mut applied_nonce = detail["nonce"].as_u64().unwrap_or(0);
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
                "fee": RECYCLE_FEE,
                "memo": "demo: recycle (clear previous tombstone)",
                "actions": [{ "effects": [
                    { "kind": "set_field", "index": name::REVOKED_SLOT, "value": "0" }
                ]}],
            }),
        )
        .await?;
        if clear["accepted"].as_bool().unwrap_or(false) {
            ctx.info("  Recycled the demo cell (cleared a previous run's tombstone).");
            applied_nonce = await_applied(&cfg, ctx, &agent_cell, applied_nonce, "recycle").await?;
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
            fee: STEP_FEE,
        },
        &cfg,
        ctx,
    )
    .await?;
    applied_nonce = await_applied(&cfg, ctx, &agent_cell, applied_nonce, "registration").await?;

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
            fee: STEP_FEE,
        },
        &cfg,
        ctx,
    )
    .await?;
    applied_nonce = await_applied(&cfg, ctx, &agent_cell, applied_nonce, "transfer").await?;

    // ── 7. Revoke + resolve again ───────────────────────────────────────────
    step(ctx, 7, &format!("Revoking '{the_name}' (one-way)"));
    name::run(
        name::NameCommand::Revoke {
            name: the_name.clone(),
            cell: Some(agent_cell.clone()),
            fee: STEP_FEE,
        },
        &cfg,
        ctx,
    )
    .await?;
    let _ = await_applied(&cfg, ctx, &agent_cell, applied_nonce, "revocation").await?;
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

/// The budget cap each of the three mutating name turns carries. `register` is
/// the dearest of them — three `set_field`s plus an `emit_event` measured at
/// 1108 computrons against a live node on 2026-07-26 — and the fee is charged in
/// FULL from the cell, so this is the size of the whole demo's appetite. It sat
/// at 1000 and every register was refused `computron budget exceeded:
/// limit=1000, used=1108`; that had been invisible behind the two failures that
/// fired earlier in the run.
const STEP_FEE: u64 = 1500;

/// Clearing one tombstone slot is a single `set_field`; it does not need a
/// name-turn's budget and charging one would halve how many demos a grant covers.
const RECYCLE_FEE: u64 = 100;

/// What one full run spends: recycle + register + transfer + revoke.
const RUN_BUDGET: u64 = RECYCLE_FEE + 3 * STEP_FEE;

/// How long to wait for a submitted turn to be applied to the ledger.
const APPLY_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(60);

/// Wait until the agent cell's nonce moves past `previous`, i.e. until the turn
/// just submitted has actually been APPLIED. Returns the new nonce.
///
/// `accepted: true` from `/api/turns/submit` means the turn was admitted and
/// ordered, not that it ran. Application happens at finalization, and a turn can
/// be refused THERE, silently — the HTTP surface has already answered. That is
/// not hypothetical: before this wait existed, steps 6 and 7 of this demo both
/// printed "committed" while the node's log recorded
///
///   finalized SignedTurn failed agent-scoped receipt continuity before mutation
///   (deterministic rejection recorded) … expected Some(..) got None
///
/// for each of them. Nothing moved: same nonce, same balance, same slots, and a
/// green demo. Waiting for each step to land before narrating the next one both
/// makes the narration true and lets the next turn bind to a receipt head that
/// exists.
async fn await_applied(
    cfg: &Config,
    ctx: &Context,
    cell: &str,
    previous: u64,
    what: &str,
) -> Result<u64, Box<dyn std::error::Error>> {
    let deadline = std::time::Instant::now() + APPLY_TIMEOUT;
    loop {
        let detail = get_json(cfg, &format!("/api/cell/{cell}")).await?;
        let nonce = detail["nonce"].as_u64().unwrap_or(0);
        if nonce > previous {
            ctx.info(&format!("  Applied on the ledger (cell nonce {nonce})."));
            return Ok(nonce);
        }
        if std::time::Instant::now() >= deadline {
            return Err(format!(
                "the {what} turn was accepted but never applied: the cell's nonce is still \
                 {previous} after {}s.\n  \
                 The node admitted the turn and then refused it at finalization. Its log will \
                 name the reason — look for \"deterministic rejection recorded\" or \
                 \"failed agent-scoped receipt continuity\".",
                APPLY_TIMEOUT.as_secs(),
            )
            .into());
        }
        tokio::time::sleep(std::time::Duration::from_millis(500)).await;
    }
}

/// How long to keep trying to get the cell funded before calling it a failure.
///
/// Long enough to outlast the node's per-cell faucet limit (one request a
/// minute), because the second consecutive demo run is exactly the case that
/// trips it.
const FUNDING_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(90);

/// Get the operator cell to `RUN_BUDGET`, from the LEDGER's point of view.
///
/// Two things this has to survive, both of which used to end the demo:
///
///   * The faucet's `success: true` is the SUBMISSION answering, not the money
///     arriving — the grant is applied when the block carrying it finalizes.
///     Reading the ledger straight after the acknowledgement is why a first run
///     against a fresh node died at step 4 with `insufficient balance on cell …:
///     need 1000, have 0`.
///   * The faucet allows one request per cell per minute. A second consecutive
///     run that needs a top-up gets refused, so a single request-then-give-up is
///     not enough; keep asking while we wait.
///
/// Timing out here is a real finding, not a hiccup: the node either is not
/// finalizing or is refusing to fund. Say which, and what the ledger actually
/// held.
async fn ensure_funded(
    cfg: &Config,
    ctx: &Context,
    cell: &str,
    pubkey: &str,
    faucet_amount: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    let deadline = std::time::Instant::now() + FUNDING_TIMEOUT;
    let want = i64::try_from(RUN_BUDGET).unwrap_or(i64::MAX);
    let mut ledger_state = String::from("no answer from /api/cell yet");
    let mut faucet_state = String::from("not asked yet");
    let mut announced = false;
    loop {
        // The ledger is the authority on whether we can proceed.
        match get_json(cfg, &format!("/api/cell/{cell}")).await {
            Ok(detail) => {
                let found = detail["found"].as_bool().unwrap_or(false);
                let balance = detail["balance"].as_i64().unwrap_or(0);
                if found && balance >= want {
                    ctx.success(&format!(
                        "Operator cell holds {balance} computrons on the ledger \
                         ({RUN_BUDGET} needed for this run)."
                    ));
                    return Ok(());
                }
                ledger_state = if found {
                    format!("cell holds {balance}, needs {want}")
                } else {
                    "cell does not exist on the ledger yet".to_string()
                };
            }
            Err(e) => ledger_state = format!("/api/cell read failed: {e}"),
        }

        // Under-funded: ask the faucet. Re-asking is deliberate — the per-cell
        // rate limit is a WAIT, not a refusal, and the grant needs a block to land.
        let faucet = post_json(
            cfg,
            "/api/faucet",
            &serde_json::json!({
                "recipient": cell, "amount": faucet_amount, "public_key": pubkey,
            }),
        )
        .await
        .map_err(|e| {
            format!("faucet request failed (is the node started with --enable-faucet?): {e}")
        })?;
        if faucet["success"].as_bool().unwrap_or(false) {
            if !announced {
                ctx.success(&format!(
                    "Faucet accepted a {faucet_amount}-computron grant; waiting for it to finalize."
                ));
                announced = true;
            }
            faucet_state = format!("granted {faucet_amount}");
        } else {
            let err = faucet["error"].as_str().unwrap_or("unknown").to_string();
            if !announced {
                ctx.info(&format!("  Faucet says: {err} — waiting on the ledger."));
                announced = true;
            }
            faucet_state = err;
        }

        if std::time::Instant::now() >= deadline {
            return Err(format!(
                "could not get {RUN_BUDGET} computrons onto the operator cell within {}s.\n  \
                 Ledger: {ledger_state}\n  Faucet: {faucet_state}\n  \
                 If the faucet granted and the ledger never moved, the node accepted a turn it \
                 did not apply: check `curl {}/status` for `consensus_live` and a rising \
                 `dag_height`, and the node log for \"failed application authorization\" or \
                 \"faithful note-root attestation\".",
                FUNDING_TIMEOUT.as_secs(),
                cfg.node.url,
            )
            .into());
        }
        tokio::time::sleep(std::time::Duration::from_millis(500)).await;
    }
}
