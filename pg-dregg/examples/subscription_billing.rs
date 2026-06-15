//! THE REVOCATION FLAGSHIP — a recurring subscription-billing settlement whose
//! every charge is a VERIFIED, capability-gated turn, and where **cancelling a
//! subscription INSTANTLY refuses the next charge** because cancellation is a
//! capability revocation the spine consults on the very next turn.
//!
//! ```text
//! cargo run --example subscription_billing
//! ```
//!
//! ## Why this demo exists (and how it differs from `supply_chain`)
//!
//! `examples/supply_chain` is the four-party purchase-order flagship: it shows
//! crash-recovery, conservation, the forged-write refusal, and federation. This
//! demo is the **instant-revocation** flagship — the headline pg-dregg property
//! `supply_chain` does NOT exercise:
//!
//!   * a recurring charge runs as a verified turn (`PROCESSOR` debits the
//!     subscriber, credits the merchant — Σδ = 0, value conserved);
//!   * the subscriber's "active subscription" IS a dregg capability;
//!   * **`dregg_revoke(token)` — the subscriber hits "cancel" — and the VERY
//!     NEXT billing turn for that subscriber is REFUSED** by the AUTHZ gate, with
//!     no polling, no TTL, no bounded staleness (`docs/PG-DREGG.md` §3; ember
//!     decision #1 — revocation is instant). The merchant cannot bill a
//!     cancelled subscriber even by replaying last month's signed turn;
//!   * **re-subscription (`dregg_unrevoke`) restores billing on the next turn** —
//!     the capability never changed, only the revocation registry did;
//!   * then a **crash mid-billing-run** + recovery re-validates the whole charge
//!     history and resumes exactly-once (so a crash never double-charges and
//!     never silently drops a charge).
//!
//! ## The pitch: "Stripe Billing's durability — but a cancelled card CANNOT be charged, provably"
//!
//! A conventional billing system (DBOS-style durable or not) enforces "is this
//! subscription active?" in *application code* that issues an ordinary `UPDATE`.
//! A bug, a stale cache, a replayed job, or an SQL-injection in that code can
//! charge a cancelled customer — the authorization is advisory. Here the
//! authorization is the **capability the charge turn must present**: revoke it
//! and the database engine's verified-write spine refuses the charge on the next
//! turn. "Was this charge authorized?" is not a code path you can get wrong; it
//! is a verified gate the turn cannot pass without a live capability.
//!
//! ## What this drives (NOT a reimplementation)
//!
//! The whole orchestration is the shipped, reusable [`pg_dregg::workflow`] API
//! (`Workflow` / `Step` / `WorkflowEngine` / `run_durable` / `recover_from_durable`
//! / `resume_durable`), over the REAL pg-dregg cores `cargo test` proves and the
//! `#[pg_test]`s exercise through live pg18 SQL:
//!
//!   * [`pg_dregg::authz`]  — the verified capability decision, attenuation, AND
//!                            the instant-revocation registry ([`authz::revoke`] /
//!                            [`authz::unrevoke`], consulted on EVERY `decide`);
//!   * [`pg_dregg::mirror`] — `MirrorBatch` (the verified-turn unit), `RootChain`
//!                            (the anti-substitution chain tooth).
//!
//! The only synthesized piece is the node-side commit-log projection (the
//! [`Projector`] seam — here the default deterministic fold, in production the
//! kernel's `ledger_root`). The authz decision, the revocation, the conservation,
//! the durability, the chain tooth are all the shipped cores, unchanged.

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use pg_dregg::mirror::{MirrorBatch, RootChain};
use pg_dregg::workflow::{
    cell_row, recover_from_durable, turn_row, DurableLog, FoldProjector, MapTokens, MemLog,
    Projector, Step, Workflow, WorkflowEngine, GENESIS_ROOT,
};

// ===========================================================================
// Cosmetics
// ===========================================================================

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn rule(title: &str) {
    println!(
        "\n\x1b[1m\x1b[36m── {title} {}\x1b[0m",
        "─".repeat(64usize.saturating_sub(title.len()))
    );
}

fn note(text: &str) {
    println!("    \x1b[2m({text})\x1b[0m");
}

// ===========================================================================
// The parties. Each cell-id is prefix-stable so a capability attenuated to the
// party's hex prefix admits exactly that party's cell as an RLS resource.
// ===========================================================================

const fn party_id(tag: u8) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[0] = tag;
    id
}

/// The settlement bank — the genesis float that funds the subscribers.
const BANK: [u8; 32] = party_id(0xba);
/// The SaaS merchant who gets paid each cycle.
const MERCHANT: [u8; 32] = party_id(0x33);
/// Subscriber A — stays subscribed throughout.
const ALICE: [u8; 32] = party_id(0xa1);
/// Subscriber B — CANCELS mid-stream (the revocation beat), then re-subscribes.
const BOB: [u8; 32] = party_id(0xb0);

fn name_of(id: [u8; 32]) -> &'static str {
    match id[0] {
        0xba => "BANK",
        0x33 => "MERCHANT",
        0xa1 => "ALICE",
        0xb0 => "BOB",
        _ => "?",
    }
}

// The monthly subscription price (in the settlement unit) + the clock the AUTHZ
// gate evaluates time caveats against (process-local, like a backend's `now()`).
const PRICE: i64 = 1_000;
const CLOCK: i64 = 1_000;

/// The node-side running view of each cell's `(balance, nonce)` — what a real
/// node's commit-log projection reads from state to build each charge's
/// post-image. The demo tracks it here so every charge's post-image is internally
/// consistent and the turns chain. Mutated ONLY when a charge actually commits;
/// a refused charge is built from a read-only [`Self::charge_step`] that does not
/// advance it (a refused turn moves nothing, including our model of the state).
struct BillingBook {
    bal: std::collections::BTreeMap<[u8; 32], i64>,
    nonce: std::collections::BTreeMap<[u8; 32], u64>,
}

impl BillingBook {
    fn new(initial: &[([u8; 32], i64)]) -> Self {
        let mut bal = std::collections::BTreeMap::new();
        let mut nonce = std::collections::BTreeMap::new();
        for &(cell, b) in initial {
            bal.insert(cell, b);
            nonce.insert(cell, 0u64);
        }
        BillingBook { bal, nonce }
    }

    fn balance(&self, cell: [u8; 32]) -> i64 {
        *self.bal.get(&cell).unwrap_or(&0)
    }

    /// Build ONE monthly charge as the SUBSCRIBER's verified turn (debit the
    /// subscriber by `PRICE`, credit the merchant) from the CURRENT book state,
    /// WITHOUT mutating it. The subscriber is the actor, so the AUTHZ gate decides
    /// on the subscriber's capability — the one a cancel revokes. Pure, so it is
    /// safe to build a charge that may be refused (the book is unchanged).
    fn charge_step(&self, subscriber: [u8; 32], merchant: [u8; 32], label: &str) -> Step {
        let new_sub = self.balance(subscriber) - PRICE;
        let new_merch = self.balance(merchant) + PRICE;
        let sub_n = self.nonce.get(&subscriber).copied().unwrap_or(0) + 1;
        let merch_n = self.nonce.get(&merchant).copied().unwrap_or(0) + 1;
        Step::new(label, subscriber)
            .set(subscriber, new_sub, sub_n)
            .set(merchant, new_merch, merch_n)
    }

    /// Commit a charge into the book (call ONLY after the engine accepted the
    /// turn): advance the subscriber's and the merchant's `(balance, nonce)` to
    /// match the post-image [`Self::charge_step`] produced.
    fn commit_charge(&mut self, subscriber: [u8; 32], merchant: [u8; 32]) {
        let new_sub = self.balance(subscriber) - PRICE;
        let new_merch = self.balance(merchant) + PRICE;
        let sub_n = self.nonce.get(&subscriber).copied().unwrap_or(0) + 1;
        let merch_n = self.nonce.get(&merchant).copied().unwrap_or(0) + 1;
        self.bal.insert(subscriber, new_sub);
        self.bal.insert(merchant, new_merch);
        self.nonce.insert(subscriber, sub_n);
        self.nonce.insert(merchant, merch_n);
    }
}

fn main() {
    println!(
        "\x1b[1mpg-dregg REVOCATION FLAGSHIP — recurring billing where a cancelled subscription CANNOT be charged\x1b[0m"
    );
    println!("\x1b[2m\"Durable billing like Stripe/DBOS — but 'is this subscription active?' is a VERIFIED capability gate,\x1b[0m");
    println!("\x1b[2m  not advisory application code: revoke the capability and the next charge turn is refused by the spine.\"\x1b[0m");
    println!("\x1b[2m  (expressed on the reusable pg_dregg::workflow API — Workflow / Step / run_durable / resume_durable)\x1b[0m");

    // =======================================================================
    // 0. THE TRUST ROOT + PER-PARTY CAPABILITIES.
    //
    // The merchant holds a `charge` capability scoped to its own merchant cell.
    // Each SUBSCRIBER holds a capability that authorizes the recurring charge on
    // ITS OWN cell — and THAT is the "active subscription". Cancelling = revoking
    // it. We model the recurring charge as the SUBSCRIBER's own verified turn
    // (the subscriber's standing authorization to be debited), which is exactly
    // the cell whose capability the cancel revokes.
    // =======================================================================
    rule("0. issuer key + per-party capabilities (a subscription IS a capability)");
    let issuer = RootKey::from_seed([7u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    authz::lru_clear();
    authz::revoked_clear();
    println!(
        "  issuer (the dregg.issuer_pubkey trust root): {}…",
        &issuer.public().to_hex()[..16]
    );

    // A capability admitting submit/read on ANY resource, ATTENUATED to the
    // party's own cell prefix (granted ⊆ held — no amplification). The same shape
    // `examples/supply_chain` mints. CRUCIAL: each party's token is minted EXACTLY
    // ONCE and stored, because `RootKey::mint` assigns a fresh random nonce per
    // call (so two `mint(...)` of the "same" caveats are DIFFERENT credentials with
    // DIFFERENT tails / `dregg_cap_id`s). The revocation key must be the cap-id of
    // the SAME token the engine holds — minting a second "equivalent" token and
    // revoking ITS id would revoke a credential nobody is presenting. (This is the
    // real instant-revocation contract: you revoke the exact credential in
    // circulation, keyed on its stable tail.)
    let mint_token = |party: [u8; 32]| -> String {
        issuer
            .mint([
                Caveat::FirstParty(Pred::AnyOf(vec![
                    Pred::AttrEq {
                        key: "action".into(),
                        value: "submit".into(),
                    },
                    Pred::AttrEq {
                        key: "action".into(),
                        value: "read".into(),
                    },
                ])),
                Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "".into(),
                }),
            ])
            .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: hx(&party)[..2].to_string(),
            })])
            .encode()
    };

    // Mint each party's token ONCE; this map is the single source of truth for the
    // bind, the cap-id revocation key, and the post-recovery rebind.
    let party_tokens: std::collections::BTreeMap<[u8; 32], String> = [BANK, MERCHANT, ALICE, BOB]
        .into_iter()
        .map(|p| (p, mint_token(p)))
        .collect();

    let mut tokens = MapTokens::new();
    for (&p, tok) in &party_tokens {
        tokens.bind(p, tok.clone());
        println!(
            "  {:<9} cap: submit/read attenuated to resource prefix \"{}\" (its own cell)",
            name_of(p),
            &hx(&p)[..2]
        );
    }
    // BOB's capability id — the stable revocation key (`dregg_cap_id`, the
    // credential tail) of the EXACT token the engine holds for him. Cancelling his
    // subscription revokes precisely this id.
    let bob_tok = party_tokens[&BOB].clone();
    let bob_cap_id = authz::cap_id(&bob_tok).expect("bob's token decodes to a stable cap id");
    println!(
        "  BOB's subscription capability id (the dregg_revoke key): {}…",
        &bob_cap_id[..16]
    );
    note(
        "a subscription is not a boolean column an app checks — it is the capability the \
          recurring charge turn must present. Cancel = revoke that capability.",
    );

    // =======================================================================
    // 1. FUND THE SUBSCRIBERS — the settlement bank funds Alice and Bob.
    //    (genesis float, then two funding turns; reads are free SQL.)
    // =======================================================================
    rule("1. the bank funds the subscribers (verified turns; reads are free SQL)");
    let mut engine = WorkflowEngine::new(tokens).with_clock(CLOCK);
    let mut durable = MemLog::new();

    let funding = Workflow::new("fund subscribers")
        .then(Step::new("genesis: BANK float 1_000_000", BANK).set(BANK, 1_000_000, 0))
        .then(
            Step::new("fund ALICE 5_000", BANK)
                .set(BANK, 995_000, 1)
                .set(ALICE, 5_000, 0),
        )
        .then(
            Step::new("fund BOB 5_000", BANK)
                .set(BANK, 990_000, 2)
                .set(BOB, 5_000, 0),
        );
    engine
        .run_durable(&funding, &mut durable)
        .expect("the funding turns commit");
    for p in [BANK, ALICE, BOB] {
        println!("    {:<9} balance = {}", name_of(p), engine.balance(p));
    }
    assert_eq!(engine.balance(ALICE), 5_000);
    assert_eq!(engine.balance(BOB), 5_000);

    // The node-side running view of cell balances/nonces — what a real node's
    // commit-log projection reads from state to build each charge's post-image.
    // Mutated only when a charge COMMITS; a refused charge is built read-only.
    let mut book = BillingBook::new(&[(ALICE, 5_000), (BOB, 5_000), (MERCHANT, 0)]);

    // =======================================================================
    // 2. CYCLE 1 — both subscribers are charged. Value is conserved each turn.
    // =======================================================================
    rule("2. billing cycle 1 — both subscribers charged (Σδ = 0 per charge)");
    let total_before = engine.total_value();
    for sub in [ALICE, BOB] {
        let step = book.charge_step(sub, MERCHANT, "cycle1 charge");
        engine
            .submit(&step)
            .unwrap_or_else(|e| panic!("cycle 1 must charge {}: {e}", name_of(sub)));
        durable.append(engine.log().last().unwrap()).unwrap();
        book.commit_charge(sub, MERCHANT);
    }
    println!(
        "    ALICE balance = {}   MERCHANT balance = {}",
        engine.balance(ALICE),
        engine.balance(MERCHANT)
    );
    println!("    BOB   balance = {}", engine.balance(BOB));
    assert_eq!(engine.balance(ALICE), 4_000, "alice charged once");
    assert_eq!(engine.balance(BOB), 4_000, "bob charged once");
    assert_eq!(
        engine.balance(MERCHANT),
        2_000,
        "merchant collected both charges"
    );
    assert_eq!(
        engine.total_value(),
        total_before,
        "a charge MOVES value, never creates it (Σ conserved)"
    );
    println!("→ each charge is a verified turn: the merchant was paid {PRICE}×2, the subscribers debited, Σ value unchanged.");

    // =======================================================================
    // 3. ✸ THE REVOCATION BEAT ✸ — BOB cancels. The next charge is REFUSED.
    // =======================================================================
    rule("3. ✸ BOB CANCELS — revoke the capability; the next charge is REFUSED instantly ✸");
    // BOB hits "cancel subscription". In SQL this is `SELECT dregg_revoke(:bob_token)`
    // (or an INSERT into dregg.revoked); here it is the core it wraps. From this
    // instant, BOB's capability is revoked — and `authz::decide` consults the
    // revocation registry on EVERY call, including warm-LRU calls, so the effect is
    // immediate on the next turn (no polling, no TTL).
    authz::revoke(&bob_cap_id);
    println!(
        "  BOB pressed cancel ⇒ dregg_revoke(BOB's capability id {}…)",
        &bob_cap_id[..12]
    );

    // The merchant now tries to run cycle 2: charge ALICE (still active) and BOB
    // (cancelled). ALICE's charge commits; BOB's is REFUSED by the AUTHZ gate.
    // We submit each charge individually so we can show the per-subscriber verdict.
    println!("  the merchant runs cycle 2's charges:");
    use pg_dregg::workflow::StepError;

    // ALICE — still subscribed ⇒ the charge commits.
    let alice_c2 = book.charge_step(ALICE, MERCHANT, "cycle2: charge ALICE 1_000");
    match engine.submit(&alice_c2) {
        Ok(_) => {
            durable.append(engine.log().last().unwrap()).unwrap();
            book.commit_charge(ALICE, MERCHANT);
            println!(
                "    ✓ ALICE charged (subscription active)   → balance {}",
                engine.balance(ALICE)
            );
        }
        Err(e) => panic!("ALICE's active subscription must still bill: {e}"),
    }

    // BOB — cancelled ⇒ the charge turn is REFUSED. `charge_step` is read-only, so
    // the book is NOT advanced for the refused turn (a refused turn moves nothing,
    // including our model of the state — no rollback needed).
    let bob_attempt = book.charge_step(BOB, MERCHANT, "cycle2: charge BOB 1_000 (CANCELLED)");
    match engine.submit(&bob_attempt) {
        Ok(_) => panic!("SECURITY FAILURE: a CANCELLED subscriber was charged"),
        Err(StepError::Unauthorized { actor, reason }) => {
            assert_eq!(actor, BOB);
            assert_eq!(
                reason, "revoked",
                "the refusal reason must name the revocation"
            );
            println!("    ✗ BOB REFUSED — reason: \"{reason}\" (the capability was revoked; the charge cannot pass the AUTHZ gate)");
        }
        Err(other) => panic!("expected an Unauthorized/revoked refusal, got {other}"),
    }
    // The refused charge moved NOTHING: Bob's balance and the merchant's are
    // exactly what they were before the cancelled attempt.
    assert_eq!(
        engine.balance(BOB),
        4_000,
        "a refused charge does not debit the cancelled subscriber"
    );
    assert_eq!(
        engine.balance(MERCHANT),
        3_000,
        "the merchant collected ONLY Alice's cycle-2 charge"
    );
    println!("→ a cancelled subscription CANNOT be charged: the revocation is consulted on the very next turn, fail-closed.");
    note("vs a conventional biller: 'is the subscription active?' is application code issuing an UPDATE — \
          a bug/stale-cache/replayed-job can charge a cancelled card. Here it is a verified gate the turn cannot pass.");

    // 3b. A REPLAY of Bob's last good (cycle-1) charge is ALSO refused — the
    // merchant cannot resurrect a cancelled subscriber by re-submitting an old
    // signed turn. Two independent gates refuse it: (a) AUTHZ (the capability is
    // revoked) and (b) the CHAIN tooth (an old ordinal cannot chain onto the head).
    rule("3b. a REPLAY of Bob's last good charge is refused too (revoked cap AND stale chain)");
    {
        // Reach under the API to push a stale ordinal-3-shaped batch (Bob's cycle-1
        // charge) straight at the chain, to show the chain backstop independently.
        let head = engine.head().unwrap();
        let next = engine.next_ordinal();
        // Build a batch at an OLD ordinal (a replay): it cannot chain.
        let stale_cells = vec![cell_row(BOB, 4_000, 1), cell_row(MERCHANT, 1_000, 1)];
        let stale_prev = GENESIS_ROOT; // a stale prev that is not the head
        let stale_post = FoldProjector.ledger_root(stale_prev, 4, &stale_cells);
        let stale = MirrorBatch::from_parts(
            turn_row(4, stale_prev, stale_post, BOB),
            stale_cells,
            vec![],
            vec![],
        )
        .unwrap();
        let mut probe = RootChain::resume(head, next);
        use pg_dregg::mirror::ChainRefusal;
        match probe.extend(&stale) {
            Err(ChainRefusal::OrdinalGap { expected, got }) => println!(
                "    a replayed charge (ordinal {got}) is REFUSED by the chain (head expects {expected}) — \
                 no double-charge, even before authz."
            ),
            Err(ChainRefusal::RootMismatch { .. }) => {
                println!("    a replayed charge is REFUSED by the chain (root does not chain onto the head).")
            }
            other => panic!("a replayed charge must be refused by the chain, got {other:?}"),
        }
        // And the AUTHZ gate would refuse it too (Bob's cap is revoked): the
        // capability decision denies the replay independent of the chain.
        assert!(
            !authz::decide(&bob_tok, "submit", &hx(&BOB), CLOCK).allowed(),
            "Bob's revoked capability denies any new charge turn (the AUTHZ backstop)"
        );
        println!("    …and the AUTHZ gate ALSO denies it (Bob's capability is revoked): two gates, both refuse.");
    }

    // =======================================================================
    // 4. RE-SUBSCRIBE — BOB comes back. dregg_unrevoke restores billing.
    // =======================================================================
    rule("4. BOB re-subscribes — dregg_unrevoke restores billing on the NEXT turn");
    // BOB re-subscribes. In SQL: `SELECT dregg_unrevoke(:bob_cap_id)` (or DELETE
    // from dregg.revoked). The capability never changed — only the revocation
    // registry did — so the very next charge commits again.
    authz::unrevoke(&bob_cap_id);
    println!(
        "  BOB re-subscribed ⇒ dregg_unrevoke({}…)",
        &bob_cap_id[..12]
    );
    // Bob's book entry is still at (4_000, the nonce committed in cycle 1) — the
    // refused cycle-2 attempt never advanced it — so the re-subscribe charge
    // chains correctly off his last good state.
    let bob_resub = book.charge_step(BOB, MERCHANT, "re-subscribe: charge BOB 1_000");
    match engine.submit(&bob_resub) {
        Ok(_) => {
            durable.append(engine.log().last().unwrap()).unwrap();
            book.commit_charge(BOB, MERCHANT);
            println!(
                "    ✓ BOB charged again (re-subscribed)   → balance {}",
                engine.balance(BOB)
            );
        }
        Err(e) => panic!("a re-subscribed customer must bill again: {e}"),
    }
    assert_eq!(
        engine.balance(BOB),
        3_000,
        "bob billed once more after re-subscribing"
    );
    println!("→ re-subscription is instant too: the capability was never reissued; lifting the revocation restored billing on the next turn.");

    // =======================================================================
    // 5. ✸ CRASH mid-run ✸ — drop the engine; recover from the durable sink.
    // =======================================================================
    rule("5. ✸ CRASH — the biller dies; recover from the durable sink (re-validates the whole charge history) ✸");
    let turns_before = engine.turn_count();
    let head_before = engine.head().unwrap();
    let merchant_before = engine.balance(MERCHANT);
    drop(engine); // the in-memory chain head + balances are GONE
    println!(
        "  the billing process died after {turns_before} verified turns. In-memory state: LOST."
    );
    println!(
        "  what survived: the durable sink ({} rows = dregg.commit_log).",
        durable.len()
    );

    // Recover: rebuild from the durable sink, re-validating every persisted charge
    // on the way up (a restored billing ledger is self-checking). Rebind the SAME
    // party tokens the live engine held (so any post-recovery charge presents the
    // identical capability — and Bob, re-subscribed above, can still bill).
    let mut tokens2 = MapTokens::new();
    for (&p, tok) in &party_tokens {
        tokens2.bind(p, tok.clone());
    }
    // NB: the recovered engine re-validates the chain (the FoldProjector re-derives
    // every root). It does NOT re-run authz on the recovered prefix — those turns
    // already committed; recovery's job is to re-validate the chain and resume.
    let engine = recover_from_durable(tokens2, FoldProjector, &durable)
        .expect("the durable charge history re-validates on recovery")
        .with_clock(CLOCK);
    println!(
        "  recovered: {} charges replayed + re-validated; chain resumed at ordinal {}, head {}…",
        engine.turn_count(),
        engine.next_ordinal(),
        &hx(&engine.head().unwrap())[..12]
    );
    assert_eq!(
        engine.turn_count(),
        turns_before,
        "every committed charge survived the crash"
    );
    assert_eq!(
        engine.head(),
        Some(head_before),
        "the head root was restored exactly"
    );
    assert_eq!(
        engine.balance(MERCHANT),
        merchant_before,
        "the merchant's collected total restored exactly"
    );
    println!("→ recovery is exactly-once: no charge lost, no charge double-applied — the crash is invisible to the books.");

    // =======================================================================
    // 6. END-TO-END INVARIANTS — conservation + the revocation audit.
    // =======================================================================
    rule("6. end-to-end — value conserved across every charge; the revocation is auditable");
    let mut total = 0i64;
    println!("  final balances (free SQL over dregg.cells):");
    for p in [BANK, MERCHANT, ALICE, BOB] {
        let b = engine.balance(p);
        total += b;
        println!("    {:<9} balance = {}", name_of(p), b);
    }
    assert_eq!(
        total, 1_000_000,
        "TOTAL VALUE CONSERVED across genesis→fund→charges→cancel→re-subscribe"
    );
    assert_eq!(
        engine.total_value(),
        1_000_000,
        "the free-SQL aggregate agrees: Σ balances = the genesis float"
    );
    // The merchant collected exactly the AUTHORIZED charges: ALICE ×2 (cycle 1 +
    // cycle 2) + BOB ×2 (cycle 1 + re-subscribe). Bob's cycle-2 charge was REFUSED
    // (cancelled), so it was never billed. 2 + 2 = 4 charges × PRICE.
    const AUTHORIZED_CHARGES: i64 = 4;
    assert_eq!(
        engine.balance(MERCHANT),
        AUTHORIZED_CHARGES * PRICE,
        "merchant collected exactly the 4 AUTHORIZED charges (Bob's cancelled cycle was NOT billed)"
    );
    println!("  Σ balances across ALL cells = {total}  (== the genesis 1_000_000)");
    println!(
        "  the merchant collected {} = exactly {AUTHORIZED_CHARGES} charges × {PRICE} — the CANCELLED charge was never billed.",
        engine.balance(MERCHANT)
    );

    // The provenance trail names who acted on every charge — the audit surface.
    rule("7. provenance — every charge names its subscriber (the audit trail)");
    for (ordinal, creator, _receipt) in engine.provenance() {
        // Only the charge turns (subscriber-acted) and funding turns appear.
        println!(
            "  ord {:>2}  charged/acted by = {}",
            ordinal,
            name_of(creator)
        );
    }
    println!(
        "→ every verified charge is attributable to the subscriber whose capability authorized it."
    );

    // =======================================================================
    // DONE.
    // =======================================================================
    rule("DONE — the integrated revocation story, all green");
    println!(
        "\x1b[1m\x1b[32m✓ a recurring subscription-billing settlement ran through pg-dregg:\x1b[0m"
    );
    println!("    • each charge a \x1b[1mverified, conserving turn\x1b[0m (Σδ = 0; the merchant cannot be over- or under-paid);");
    println!("    • a subscription IS a \x1b[1mcapability\x1b[0m — cancelling it is \x1b[1mdregg_revoke\x1b[0m;");
    println!("    • a \x1b[1mcancelled subscriber's next charge was REFUSED\x1b[0m instantly (revocation consulted on the very next turn);");
    println!("    • a \x1b[1mreplay of an old charge was refused\x1b[0m too (revoked capability AND stale chain — two gates);");
    println!("    • \x1b[1mre-subscription restored billing\x1b[0m on the next turn (the capability never changed — only the registry);");
    println!("    • the biller \x1b[1msurvived a crash\x1b[0m and resumed \x1b[1mexactly-once\x1b[0m (no charge lost, none double-applied);");
    println!("    • \x1b[1mvalue was conserved\x1b[0m end-to-end; the merchant collected exactly the AUTHORIZED charges.");
    println!("\n  Durable billing like DBOS/Stripe — \x1b[1mand\x1b[0m a cancelled card provably cannot be charged.");
    println!("  \x1b[2mThe same surface, through real pg18 SQL: SELECT dregg_revoke(token);  then the next INSERT into dregg.submit_queue is RLS-refused.\x1b[0m");
}
