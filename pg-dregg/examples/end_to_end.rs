//! pg-dregg end-to-end demonstration — on SYNTHETIC committed turns, no live
//! node and no postgres required.
//!
//! Run it:
//!
//! ```text
//! cargo run --example end_to_end
//! ```
//!
//! It walks the whole pg-dregg arc in plain Rust (the postgres-free cores that
//! `cargo test` proves), narrating each step and asserting the load-bearing
//! property so the run is a real artifact, not a print job. The SAME behaviour
//! is exercised THROUGH real SQL by the `#[pg_test]`s in `src/lib.rs` (run with
//! `cargo pgrx test pg18`); this example is the cores' story end to end.
//!
//! The arc:
//!   1. The mirror ingests a chain of synthetic committed turns (genesis,
//!      transfer, grant, organ op) — `MirrorBatch`es projected exactly as the
//!      node's M2 writer will project them.
//!   2. The mirror's `RootChain` tooth ACCEPTS the well-formed chain and REFUSES
//!      a tampered/substituted batch (the anti-substitution demonstration).
//!   3. The Tier-B DDL is emitted from the same Rust that defines the rows, and
//!      the accepted batches' rows are rendered as the INSERTs a writer runs.
//!   4. A reader presents a dregg capability TOKEN; the authz core decides which
//!      `dregg.cells` rows the RLS policy admits — and an ATTENUATED token sees a
//!      STRICT SUBSET (the no-amplify property), exactly what RLS will narrow.

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use pg_dregg::mirror::{MirrorBatch, RootChain};
use pg_dregg::synth::{self, ALICE, BOB, GENESIS_ROOT, TREASURY};

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn rule(title: &str) {
    println!(
        "\n\x1b[1m── {title} {}\x1b[0m",
        "─".repeat(60usize.saturating_sub(title.len()))
    );
}

fn main() {
    println!("\x1b[1mpg-dregg — end-to-end on synthetic turns (no node, no postgres)\x1b[0m");

    // =======================================================================
    // 1. THE MIRROR INGESTS A CHAIN OF SYNTHETIC COMMITTED TURNS.
    // =======================================================================
    rule("1. mirror ← synthetic committed turns");
    let story: Vec<MirrorBatch> = synth::ledger_story();
    println!(
        "the node committed {} turns; the mirror replays them:",
        story.len()
    );

    let mut chain = RootChain::resume(GENESIS_ROOT, 0);
    for b in &story {
        // The mirror runs check_ordinals (inside extend) + the root-chain tooth.
        chain
            .extend(b)
            .unwrap_or_else(|e| panic!("a well-formed batch was refused: {e}"));
        let post = hx(&b.turn.ledger_root);
        let what = match (b.cells.len(), b.caps.len()) {
            (1, 0) if b.turn.ordinal == 0 => "genesis: TREASURY funded to 1_000_000".to_string(),
            (3, 0) => "transfer: TREASURY → ALICE 400, TREASURY → BOB 100".to_string(),
            (_, 1) => "grant: ALICE delegates a capability to BOB (slot 0)".to_string(),
            _ => "organ op: ALICE seals a field (nonce bump)".to_string(),
        };
        println!("  ord {}  root {}…  {}", b.turn.ordinal, &post[..12], what);
    }
    assert_eq!(chain.next_ordinal(), 4, "all four turns must chain");
    println!(
        "→ all {} turns CHAINED; head root {}…",
        story.len(),
        &hx(&chain.head().unwrap())[..12]
    );

    // Conservation across the transfer (a property the explorer can re-check in
    // SQL: SELECT sum(balance) over the touched cells).
    let transfer = &story[1];
    let total: i64 = transfer.cells.iter().map(|c| c.balance).sum();
    assert_eq!(total, 1_000_000, "the transfer must conserve value");
    println!("→ conservation holds at ord 1: Σ balances = {total}");

    // =======================================================================
    // 2. THE ROOT-CHAIN TOOTH REFUSES A TAMPERED / SUBSTITUTED BATCH.
    // =======================================================================
    rule("2. anti-substitution: a tampered batch is REFUSED");
    // Re-run the chain up to ord 1, then offer a forged ord-2 batch whose
    // prev_root has been substituted.
    let mut chain2 = RootChain::resume(GENESIS_ROOT, 0);
    chain2.extend(&story[0]).unwrap();
    chain2.extend(&story[1]).unwrap();
    let head_before = chain2.head();
    let tampered = synth::tampered_batch_at_2();
    match chain2.extend(&tampered) {
        Ok(()) => panic!("SECURITY FAILURE: a tampered batch was accepted"),
        Err(e) => println!("  the mirror REFUSED the forged ord-2 batch: {e}"),
    }
    assert_eq!(
        chain2.head(),
        head_before,
        "a refused batch must not move the head"
    );
    println!("→ the chain head did NOT move; forged state cannot enter the mirror");

    // =======================================================================
    // 3. THE TIER-B DDL + THE ACCEPTED ROWS, AS SQL.
    // =======================================================================
    rule("3. the Tier-B schema + rows the writer materializes");
    let ddl = pg_dregg::mirror::ddl::tier_b();
    let creates = ddl.matches("CREATE TABLE").count();
    let views = ddl.matches("CREATE OR REPLACE VIEW").count();
    let policies = ddl.matches("CREATE POLICY").count();
    println!(
        "  mirror::ddl::tier_b() emits {creates} tables, {views} views, {policies} RLS policies"
    );
    println!("  (it AGREES with sql/schema-tierB.sql — pinned by the anti-drift test)");
    println!("  the accepted rows, as the writer's INSERTs (excerpt):");
    for b in &story {
        for c in &b.cells {
            println!(
                "    INSERT dregg.cells (cell={}…, balance={}, nonce={}, ord={});",
                &hx(&c.cell_id)[..4],
                c.balance,
                c.nonce,
                c.last_ordinal
            );
        }
        for cap in &b.caps {
            println!(
                "    INSERT dregg.capabilities (holder={}…, slot={}, target={}…, perms={});",
                &hx(&cap.holder)[..4],
                cap.slot,
                &hx(&cap.target)[..4],
                cap.permissions_json
            );
        }
    }

    // =======================================================================
    // 4. A READER PRESENTS A CAP TOKEN; RLS NARROWS THE VISIBLE CELLS.
    // =======================================================================
    rule("4. RLS under a cap token — and attenuation NARROWS the rows");

    // The database trust root: a fixed issuer key (in postgres this is the
    // dregg.issuer_pubkey GUC; here we install it directly).
    let issuer = RootKey::from_seed([7u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    println!(
        "  issuer key installed: {}…",
        &issuer.public().to_hex()[..12]
    );

    // A read capability over ANY cell (the operator's token): action=read,
    // resource prefix "" (every cell-id hex).
    let operator = issuer
        .mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            }),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "".into(),
            }),
        ])
        .encode();

    // An ATTENUATED token confined to ALICE's cell only (resource prefix "a1",
    // the hex prefix of ALICE's cell-id). This is what a delegated reader holds.
    let alice_only = issuer
        .mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            }),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "".into(),
            }),
        ])
        .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
            key: "resource".into(),
            prefix: "a1".into(),
        })])
        .encode();

    // The RLS policy on dregg.cells is: USING (dregg_admits('read',
    // encode(cell_id,'hex'))). We evaluate exactly that decision, per row, for
    // each token — which is what postgres does per row under the policy.
    let cells = [("TREASURY", TREASURY), ("ALICE", ALICE), ("BOB", BOB)];
    let now = 1_000i64;
    let visible = |tok: &str| -> Vec<&'static str> {
        cells
            .iter()
            .filter(|(_, id)| authz::decide(tok, "read", &hx(id), now).allowed())
            .map(|(name, _)| *name)
            .collect()
    };

    let op_sees = visible(&operator);
    let alice_sees = visible(&alice_only);
    println!(
        "  operator token   → SELECT FROM dregg.cells sees: {:?}",
        op_sees
    );
    println!(
        "  alice-only token → SELECT FROM dregg.cells sees: {:?}",
        alice_sees
    );

    assert_eq!(op_sees.len(), 3, "the operator sees all three cells");
    assert_eq!(
        alice_sees,
        vec!["ALICE"],
        "the attenuated token sees ONLY ALICE"
    );
    // The no-amplify property, observed through the RLS decision: the child's
    // visible set is a STRICT subset of the parent's.
    for s in &alice_sees {
        assert!(op_sees.contains(s), "child saw a row the parent could not");
    }
    assert!(
        alice_sees.len() < op_sees.len(),
        "attenuation must strictly narrow"
    );
    println!(
        "→ attenuation NARROWED the visible rows {} → {} (strict subset; no amplification)",
        op_sees.len(),
        alice_sees.len()
    );

    // Instant revocation: revoke the operator's exact credential; it now sees
    // nothing on the very next decision.
    rule("4b. instant revocation — rows vanish on the next query");
    let id = authz::cap_id(&operator).expect("operator token decodes");
    authz::revoke(&id);
    let after = visible(&operator);
    assert!(after.is_empty(), "a revoked token must see zero rows");
    println!(
        "  revoked the operator credential ({}…); it now sees: {:?}",
        &id[..12],
        after
    );
    println!("→ revocation is INSTANT — the next SELECT returns zero rows");
    authz::unrevoke(&id);

    rule("DONE");
    println!("\x1b[1m✓ end-to-end: mirror→chain→DDL→RLS-narrowing + anti-substitution + revocation, all green.\x1b[0m");
    println!("  the SAME arc, through real SQL on pg18: cargo pgrx test pg18");
}
