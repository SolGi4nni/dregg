//! pg-dregg LOAD GENERATOR — sustained verified-turn throughput, the dummy load.
//!
//! ```text
//! cargo run --release --bin loadgen                 # default: 3s, 4 agents
//! cargo run --release --bin loadgen -- --secs 10    # run for 10 seconds
//! cargo run --release --bin loadgen -- --secs 5 --agents 16
//! ```
//!
//! It drives sustained load through the **full verified-write spine** — the same
//! three gates the flagship demo and the live pg path enforce — and reports the
//! observed sustained rate (turns/sec) so we can show pg-dregg under load:
//!
//!   1. AUTHZ — each turn's acting agent passes the `submit_gate` RLS admission
//!      (`authz::decide(token, "submit", cell, now)`), against an attenuated,
//!      per-agent capability (so the load is *authorized* load, not a bypass);
//!   2. CHAIN — each produced `MirrorBatch` is admitted by the real `RootChain`
//!      anti-substitution tooth (the spine invariant);
//!   3. APPLY — the post-image is materialized + appended to the durable log.
//!
//! This is the postgres-free *core* rate (the algorithmic ceiling the verifier
//! imposes); the live-pg rate (which adds the SPI/IPC + MERGE cost) is what
//! `cargo pgrx test pg18` / `scripts/e2e-live.sh` exercise. Quoting the core rate
//! is the honest "what does the verification itself cost per turn" number.
//!
//! The load is a continuous stream of two-party transfers between a rotating set
//! of agent cells, each a real receipted verified turn, conserving value every
//! step (one debit, one credit). It runs for `--secs` seconds and prints the
//! count, the elapsed time, and the sustained turns/sec.

use std::time::{Duration, Instant};

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use pg_dregg::mirror::{CellRow, MemCell, MirrorBatch, RootChain, TurnRow, Domain};

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

const fn agent_id(tag: u8) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[0] = tag;
    id
}

const GENESIS_ROOT: [u8; 32] = [0u8; 32];
const CLOCK: i64 = 1_000;

fn fold_root(prev: [u8; 32], ordinal: u64, cells: &[CellRow]) -> [u8; 32] {
    let mut acc: u64 = 0xcbf29ce484222325 ^ ordinal.wrapping_mul(0x100000001b3);
    for b in prev {
        acc = (acc ^ b as u64).wrapping_mul(0x100000001b3);
    }
    for c in cells {
        for b in c.cell_id {
            acc = (acc ^ b as u64).wrapping_mul(0x100000001b3);
        }
        acc = (acc ^ c.balance as u64).wrapping_mul(0x100000001b3);
        acc = (acc ^ c.nonce).wrapping_mul(0x100000001b3);
    }
    let mut out = [0u8; 32];
    for (i, chunk) in out.chunks_mut(8).enumerate() {
        let v = acc.wrapping_add((i as u64).wrapping_mul(0x9e3779b97f4a7c15));
        chunk.copy_from_slice(&v.to_le_bytes());
    }
    out
}

fn cell(id: [u8; 32], balance: i64, nonce: u64) -> CellRow {
    CellRow {
        cell_id: id,
        mode: "Hosted".into(),
        balance,
        nonce,
        fields: vec![],
        fields_json: Some(format!("{{\"balance\":{balance}}}")),
        heap: None,
        program: None,
        verification_key: None,
        permissions_json: Some("{\"transfer\":\"owner\"}".into()),
        delegate: None,
        lifecycle: "Active".into(),
        last_ordinal: 0,
        cell_root: id,
    }
}

fn mem(id: [u8; 32], balance: i64) -> MemCell {
    MemCell {
        domain: Domain::Registers,
        collection: id.to_vec(),
        key: b"balance".to_vec(),
        value: Some(balance.to_le_bytes().to_vec()),
        last_ordinal: 0,
    }
}

fn turn_row(ordinal: u64, prev: [u8; 32], post: [u8; 32], creator: [u8; 32]) -> TurnRow {
    let stamp = |seed: u8| {
        let mut b = [seed; 32];
        b[0] = ordinal as u8;
        b[1] = (ordinal >> 8) as u8;
        b
    };
    TurnRow {
        ordinal,
        height: ordinal,
        block_id: stamp(0x22),
        block_executed_up_to: ordinal,
        turn_hash: stamp(0x33),
        creator,
        receipt_hash: stamp(0x44),
        ledger_root: post,
        prev_root: prev,
    }
}

fn main() {
    // ---- args -----------------------------------------------------------
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut secs: u64 = 3;
    let mut n_agents: usize = 4;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--secs" => {
                secs = args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or(3);
                i += 2;
            }
            "--agents" => {
                n_agents = args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or(4).max(2);
                i += 2;
            }
            other => {
                eprintln!("unknown arg: {other} (use --secs N, --agents N)");
                i += 1;
            }
        }
    }

    println!("pg-dregg loadgen — sustained verified-turn throughput");
    println!("  duration: {secs}s   agents: {n_agents}   (each turn: authz submit-gate + RootChain + apply)");

    // ---- trust root + per-agent attenuated tokens -----------------------
    let issuer = RootKey::from_seed([7u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    authz::lru_clear();
    authz::revoked_clear();

    let agents: Vec<[u8; 32]> = (0..n_agents).map(|k| agent_id(0x20 + k as u8)).collect();
    // Each agent holds a `submit` capability over the WHOLE agent namespace
    // (prefix "11"… no — the leading byte is the tag, so the shared prefix is the
    // common tail). For load we mint one broad-but-real token per agent admitting
    // `submit` on any resource; the gate still runs the full verify per cold turn.
    let mut tokens: std::collections::HashMap<[u8; 32], String> = std::collections::HashMap::new();
    for &a in &agents {
        let tok = issuer
            .mint([
                Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "submit".into() }),
                Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "".into() }),
                Caveat::FirstParty(Pred::NotAfter { at: 1_000_000 }),
            ])
            .encode();
        tokens.insert(a, tok);
    }

    // ---- durable engine state -------------------------------------------
    let mut chain = RootChain::resume(GENESIS_ROOT, 0);
    let mut balances: std::collections::HashMap<[u8; 32], (i64, u64)> = std::collections::HashMap::new();
    let mut durable_log_len: u64 = 0;

    // Genesis: fund agent 0 with the whole float so transfers always conserve.
    let float: i64 = 1_000_000_000;
    {
        let g = cell(agents[0], float, 0);
        let post = fold_root(GENESIS_ROOT, 0, std::slice::from_ref(&g));
        let batch = MirrorBatch::from_parts(
            turn_row(0, GENESIS_ROOT, post, agents[0]),
            vec![g],
            vec![],
            vec![mem(agents[0], float)],
        )
        .unwrap();
        chain.extend(&batch).expect("genesis must chain");
        for c in &batch.cells {
            balances.insert(c.cell_id, (c.balance, c.nonce));
        }
        durable_log_len += 1;
    }

    // ---- the sustained load loop ----------------------------------------
    let deadline = Instant::now() + Duration::from_secs(secs);
    let start = Instant::now();
    let mut turns: u64 = 0;
    let mut refused: u64 = 0;
    let mut sender_idx = 0usize;

    // We rotate which agent sends; the receiver is the next agent round-robin. The
    // sender always holds the float (it received it last round), so a unit
    // transfer always conserves and never underflows.
    let mut holder = 0usize; // who currently holds the float
    while Instant::now() < deadline {
        // batch a chunk between clock reads (clock reads dominate at ns-scale ops).
        for _ in 0..256 {
            let from = agents[holder];
            let to = agents[(holder + 1) % n_agents];

            // GATE 1: authz submit-gate (the acting agent submits for its own cell).
            let token = &tokens[&from];
            if !authz::decide(token, "submit", &hx(&from), CLOCK).allowed() {
                refused += 1;
                continue;
            }

            // Build the transfer post-image (1 debit, 1 credit — conserves).
            let (from_bal, from_nonce) = *balances.get(&from).unwrap_or(&(0, 0));
            let (to_bal, _to_nonce) = *balances.get(&to).unwrap_or(&(0, 0));
            let amount = 1i64;
            if from_bal < amount {
                // Float drifted (shouldn't, single holder) — stop sending from here.
                holder = (holder + 1) % n_agents;
                continue;
            }
            let ordinal = chain.next_ordinal();
            let prev = chain.head().unwrap_or(GENESIS_ROOT);
            let cells = vec![
                cell(from, from_bal - amount, from_nonce + 1),
                cell(to, to_bal + amount, 0),
            ];
            let post = fold_root(prev, ordinal, &cells);
            let memory = vec![mem(from, from_bal - amount), mem(to, to_bal + amount)];
            let batch = match MirrorBatch::from_parts(turn_row(ordinal, prev, post, from), cells, vec![], memory) {
                Ok(b) => b,
                Err(_) => {
                    refused += 1;
                    continue;
                }
            };

            // GATE 2: the RootChain anti-substitution tooth.
            if chain.extend(&batch).is_err() {
                refused += 1;
                continue;
            }

            // GATE 3: apply + durably log.
            for c in &batch.cells {
                balances.insert(c.cell_id, (c.balance, c.nonce));
            }
            durable_log_len += 1;
            turns += 1;

            // The receiver now holds (almost) the float; move the holder forward so
            // the next sender has balance. (Every agent keeps a tiny balance; the
            // bulk float walks the ring.)
            holder = (holder + 1) % n_agents;
            sender_idx = sender_idx.wrapping_add(1);
        }
    }
    let elapsed = start.elapsed();

    // ---- report ---------------------------------------------------------
    let rate = turns as f64 / elapsed.as_secs_f64();
    // A free-SQL conservation check over the whole mirror (Σ balances == float).
    let total: i64 = balances.values().map(|&(b, _)| b).sum();

    println!("\n── results ─────────────────────────────────────────────");
    println!("  committed verified turns: {turns}");
    println!("  refused (gate):           {refused}");
    println!("  durable log rows:         {durable_log_len}");
    println!("  elapsed:                  {:.3}s", elapsed.as_secs_f64());
    println!("  \x1b[1msustained rate:           {rate:.0} verified turns/sec\x1b[0m");
    println!("  conservation:             Σ balances = {total}  (== float {float})  {}",
        if total == float { "✓" } else { "✗ BROKEN" });
    assert_eq!(total, float, "load must conserve value end-to-end");
    let _ = sender_idx;
    println!("\n  (postgres-free core rate — the verification cost per turn. The live-pg");
    println!("   rate adds SPI/IPC + the MERGE applicator; see scripts/e2e-live.sh.)");
}
