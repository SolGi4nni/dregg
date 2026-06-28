//! THE SCENARIO — the first room, run end to end through ONE real executor.
//!
//! A ROOM contains an INHABITANT (a cell holding a workflow-mandate = its JOB) and a PAYER (who
//! escrows the reward from a conserved pool). The cycle:
//!
//!   1. the payer LISTS + FUNDS the escrow — the reward, drawn from a conserved pool, bounded by the
//!      listing ceiling (`escrowed ≤ ceiling`);
//!   2. the inhabitant DOES ITS MANDATED JOB step-by-step — `gather → make → hand-off`, each a real
//!      receipted turn the executor admits IFF the three legs pass (DAG/no-skip · clearance ·
//!      spend-budget);
//!   3. the job FINISHES (cursor == terminal) — and ONLY THEN does the payer SHIP + SETTLE the
//!      escrow, RELEASING the reward to the inhabitant (a conserving transfer: `released ==
//!      escrowed`). It is PAID.
//!
//! Then THE HEADLINE — a try-to-cheat battery, EACH refused IN-BAND by the real executor and rendered
//! in-room with the receipt-why:
//!   (a) SKIP a prerequisite step      — `MonotonicSequence(JOB_CURSOR)` refuses a non-`+1`;
//!   (b) OVERSPEND the budget          — `FieldLteField(SPEND_ACCUM ≤ BUDGET)` refuses the overrun;
//!   (c) REACH outside its compartment — fund OVER the escrow ceiling (`escrowed ≤ ceiling`) refuses;
//!   (d) take a verb it WASN'T GRANTED — a hauler at the `make` verb (`ClearanceDominates`) refuses;
//!   (e) RELEASE the escrow without approval — a non-conserving settle (`AffineEq`) refuses (value
//!       conjured from nothing), AND a settle BEFORE the job is done is not paid out.
//!
//! Every cheat is driven through `EmbeddedExecutor::submit_action` exactly as the honest steps are, so
//! a refusal is a REAL executor rejection on the produced transition, not an unhandled branch.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    InvokeAuthority, field_from_u64,
};
use dregg_cell::{Cell, EFFECT_MINT, FactoryCreationParams, Permissions};

use starbridge_compartment_workflow_mandate::colonist_job::{
    self as job, FULL_BUDGET, JOB_CURSOR_SLOT, JOB_TERMINAL, SPEND_ACCUM_SLOT, TIGHT_BUDGET,
    WorkflowVerb,
};
use starbridge_escrow_market::{
    self as escrow, ESCROW_FACTORY_VK, ESCROWED_SLOT, EscrowVault, RELEASED_SLOT, STATE_SETTLED,
    STATE_SLOT, escrow_child_program_vk, escrow_factory_descriptor,
};

use crate::room::{GenuineAction, InRoomRefusal, InhabitantView, Room, short_hex};

/// The reward the payer escrows for the completed job (≤ the listing ceiling).
pub const REWARD: u64 = 800;
/// The listing ceiling the buyer's escrow draw is bounded by (the trustline `line`).
pub const CEILING: u64 = 1000;
/// The shared CREDIT asset the reward is denominated in (`AssetId := issuer-cell`). The pay is a
/// REAL conserved credit moving between two cells of this asset — not a scalar field. The
/// per-asset standing invariant `Σ holders(CREDIT) + well(CREDIT) = 0` holds across the value leg.
pub const CREDIT_ASSET: [u8; 32] = [0xC0u8; 32];

/// One job-step's record (a verb advanced, the spend it cost, the receipt that committed it).
#[derive(Clone, Debug)]
pub struct JobStepRecord {
    pub verb: WorkflowVerb,
    pub cursor_after: u64,
    pub spend_after: u64,
    pub receipt_hash: [u8; 32],
}

/// The class of a cheat in the try-to-cheat battery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheatClass {
    /// (a) skip a prerequisite step.
    SkipPrerequisite,
    /// (b) overspend the budget.
    OverspendBudget,
    /// (c) reach outside its compartment (fund over the escrow ceiling).
    ReachOutsideCompartment,
    /// (d) take a verb it wasn't granted (a hauler crafting).
    UngrantedVerb,
    /// (e) release the escrow without approval (a non-conserving settle).
    ReleaseWithoutApproval,
}

impl CheatClass {
    /// A short human label.
    pub fn label(self) -> &'static str {
        match self {
            Self::SkipPrerequisite => "skip a prerequisite step",
            Self::OverspendBudget => "overspend the budget",
            Self::ReachOutsideCompartment => "reach outside its compartment",
            Self::UngrantedVerb => "take a verb it wasn't granted",
            Self::ReleaseWithoutApproval => "release the escrow without approval",
        }
    }
    /// The tooth (executor constraint) that must refuse this cheat.
    pub fn tooth(self) -> &'static str {
        match self {
            Self::SkipPrerequisite => "MonotonicSequence(JOB_CURSOR)",
            Self::OverspendBudget => "FieldLteField(SPEND_ACCUM ≤ BUDGET)",
            Self::ReachOutsideCompartment => "FieldLteField(ESCROWED ≤ CEILING)",
            Self::UngrantedVerb => "ClearanceDominates(actor ⊐ verb)",
            Self::ReleaseWithoutApproval => "AffineEq(RELEASED + REFUNDED == ESCROWED)",
        }
    }
}

/// The outcome of one cheat attempt: it MUST be refused, and the refusal MUST cite the tooth.
#[derive(Clone, Debug)]
pub struct CheatOutcome {
    pub class: CheatClass,
    /// `true` iff the real executor refused the cheat (it must be).
    pub refused: bool,
    /// The executor's reason (the receipt-why), lower-cased.
    pub reason: String,
    /// `true` iff the refusal reason cites the expected tooth (proof the RIGHT guard bit, not a
    /// coincidental failure — the both-polarity / non-vacuity discipline).
    pub tooth_cited: bool,
}

impl CheatOutcome {
    /// `true` iff this cheat was PROVABLY refused: rejected in-band AND on the expected tooth.
    pub fn provably_refused(&self) -> bool {
        self.refused && self.tooth_cited
    }
}

/// THE TRANSCRIPT — the full run: the funded reward, the genuine job steps, the pay, the rendered
/// room, and the cheat battery outcomes. The example prints it; the tests assert on it.
#[derive(Clone, Debug)]
pub struct Transcript {
    /// The reward the payer escrowed (the conserved pool draw).
    pub funded_reward: u64,
    /// The genuine job steps the inhabitant committed (gather → make → hand-off).
    pub job_steps: Vec<JobStepRecord>,
    /// `true` iff the job reached its terminal (cursor == JOB_TERMINAL).
    pub job_done: bool,
    /// The reward the colonist HOLDS after the conserving Transfer (a real on-ledger CREDIT
    /// balance, not a read-only field) — the pay.
    pub paid: u64,
    /// `true` iff settlement conserved the escrow lifecycle (released + refunded == escrowed).
    pub conserved: bool,
    /// `true` iff the REAL value leg conserved: per-asset Σδ=0 over CREDIT after the reward
    /// Transfer (`Σ holders(CREDIT) + well(CREDIT) = 0`). The pay is genuine conserved value.
    pub credit_conserved: bool,
    /// The cheat battery outcomes (one per class).
    pub cheats: Vec<CheatOutcome>,
    /// The rendered room (inhabitant + payer, mandate + genuine actions + in-room refusals).
    pub room: Room,
}

impl Transcript {
    /// `true` iff the honest cycle succeeded (job done, paid the full reward, conserving) AND every
    /// cheat was provably refused. This is THE first-room guarantee.
    pub fn first_room_holds(&self) -> bool {
        self.job_done
            && self.paid == self.funded_reward
            && self.conserved
            && self.credit_conserved
            && self.cheats.iter().all(CheatOutcome::provably_refused)
    }
}

// =============================================================================
// Low-level: seed a JOB cell at an explicit cell id in a shared ledger.
// =============================================================================

/// Seed a colonist JOB cell at `cell` (NOT necessarily the executor's primary cell): install the job
/// program and bind its config (terminal, clearance-root, budget — WriteOnce) + cursor/spend = 0.
/// Mirrors `colonist_job::seed_job`, but on an explicit cell id (so the job cell and the escrow cell
/// can both live in ONE ledger). The cell must already exist in the ledger.
fn seed_job_on(exec: &EmbeddedExecutor, cell: CellId, budget: u64) {
    exec.install_program(cell, job::job_cell_program());
    exec.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state.set_field(
                job::JOB_TERMINAL_SLOT as usize,
                field_from_u64(JOB_TERMINAL),
            );
            c.state.set_field(
                job::CLEARANCE_GRAPH_ROOT_SLOT as usize,
                job::job_clearance_root(),
            );
            c.state
                .set_field(job::BUDGET_SLOT as usize, field_from_u64(budget));
            c.state
                .set_field(JOB_CURSOR_SLOT as usize, field_from_u64(0));
            c.state
                .set_field(SPEND_ACCUM_SLOT as usize, field_from_u64(0));
        }
    });
}

/// Advance the job at `cell` one step through the real executor, presenting `actor_clearance`. Reads
/// the live cursor, builds the full advance turn (cursor + spend + clearance materialization), submits
/// it as a signed action. The executor re-enforces the job program, so a skip / overspend / out-of-
/// clearance verb is refused in-band.
fn advance_job_on(
    cclerk: &AppCipherclerk,
    exec: &EmbeddedExecutor,
    cell: CellId,
    actor_clearance: dregg_app_framework::FieldElement,
) -> Result<dregg_app_framework::TurnReceipt, dregg_app_framework::ExecutorSubmitError> {
    let live = exec.cell_state(cell).expect("seeded job cell exists");
    let live_cursor = job::field_to_u64(&live.fields[JOB_CURSOR_SLOT as usize]);
    let next = live_cursor + 1;
    let verb_compartment = WorkflowVerb::at_cursor(live_cursor)
        .map(|v| v.compartment_label())
        .unwrap_or([0u8; 32]);
    let effects = job::advance_effects(cell, next, actor_clearance, verb_compartment);
    let action = cclerk.make_action(cell, "advance_step", effects);
    exec.submit_action(cclerk, action)
}

fn cursor_of(exec: &EmbeddedExecutor, cell: CellId) -> u64 {
    let s = exec.cell_state(cell).expect("job cell exists");
    job::field_to_u64(&s.fields[JOB_CURSOR_SLOT as usize])
}

fn spend_of(exec: &EmbeddedExecutor, cell: CellId) -> u64 {
    let s = exec.cell_state(cell).expect("job cell exists");
    job::field_to_u64(&s.fields[SPEND_ACCUM_SLOT as usize])
}

fn read_u64(f: &dregg_app_framework::FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// Birth an escrow cell from the escrow factory through the executor, owned by `cclerk`. Returns the
/// born cell id (with an owner cap granted to the payer agent), exactly the factory-birth pattern.
fn birth_escrow_cell(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, token_tag: &[u8]) -> CellId {
    exec.deploy_factory(escrow_factory_descriptor());
    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&agent) {
            cell.state.set_balance(100_000_000);
        }
    });
    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(token_tag).as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(escrow_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(ESCROW_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth).expect("escrow-cell birth commits");
    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// Seed a job cell at an explicit cell id by inserting it into the ledger (a fresh sovereign cell),
/// then seeding the job program/config. Returns the job cell id.
fn birth_job_cell(
    exec: &EmbeddedExecutor,
    payer: &AppCipherclerk,
    owner: &[u8; 32],
    token_tag: &[u8],
    budget: u64,
) -> CellId {
    let token: [u8; 32] = *blake3::hash(token_tag).as_bytes();
    let job_cell = CellId::derive_raw(owner, &token);
    let agent = payer.cell_id();
    exec.with_ledger_mut(|ledger| {
        if ledger.get(&job_cell).is_none() {
            // A fresh sovereign cell (id == derive_raw(owner, token)) to host the job program.
            let cell = dregg_cell::Cell::new(*owner, token);
            let _ = ledger.insert_cell(cell);
        }
        // Grant the driving agent an owner cap to the job cell so its advance turns are authorized
        // (the same cap-grant the factory-born escrow gets — the inhabitant acts through a held cap).
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell
                .capabilities
                .grant(job_cell, AuthRequired::Signature);
        }
    });
    seed_job_on(exec, job_cell, budget);
    job_cell
}

// =============================================================================
// THE REAL VALUE LEG — the pay is a conserved CREDIT, not a read-only field.
// =============================================================================
//
// The escrow lifecycle above (list→fund→ship→settle) is the ECONOMY's STATE MACHINE — the scalar
// `ESCROWED`/`RELEASED` organs the cheat battery (c)/(e) bite on. Riding ALONGSIDE it (exactly as
// `escrow-market`'s `EscrowVault` value organ rides alongside its lifecycle cell) is the REAL value
// flow: the reward is a conserved CREDIT minted onto a reward-pool VAULT, and on job completion the
// vault RELEASES it to the colonist's wallet through the shared `Payable` interface — a single
// kernel `Effect::Transfer`. So the colonist genuinely HOLDS the pay (a real on-ledger balance),
// and per-asset Σδ=0 conserves across the move. This is the weld made GENUINE: the JOB (organs 1&2)
// gates a REAL conserving Transfer of the reward (organ 3, the SAME `Payable` DSI bounty-board uses).

/// A fully-open CREDIT holder cell (a wallet / vault) at `seed`, starting at zero balance. Open
/// permissions because the value flows by the EFFECT-level gates (the mint-authority cap + the
/// conserved cross-cell move), not the holder's own permission tier.
fn credit_holder(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let mut cell = Cell::with_balance(pk, CREDIT_ASSET, 0);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

/// The deterministic per-asset issuer well id (mirrors the executor's `derive_issuer_well`): the
/// −supply account that makes a mint conserve (`Σ holders + well = 0`).
fn credit_well_id() -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", &CREDIT_ASSET);
    CellId::derive_raw(&well_pubkey, &CREDIT_ASSET)
}

/// Sum every CREDIT holder's balance (the per-asset supply). For the conserving CREDIT asset this is
/// identically 0: `Σ holders(CREDIT) + well(CREDIT) = 0`.
fn credit_supply(exec: &EmbeddedExecutor) -> i128 {
    exec.with_ledger_mut(|ledger| {
        ledger
            .iter()
            .filter(|(_, c)| c.token_id() == &CREDIT_ASSET)
            .map(|(_, c)| c.state.balance() as i128)
            .sum()
    })
}

/// The live balance of `cell` (0 if absent).
fn balance_of(exec: &EmbeddedExecutor, cell: CellId) -> i64 {
    exec.with_ledger_mut(|ledger| ledger.get(&cell).map(|c| c.state.balance()).unwrap_or(0))
}

// =============================================================================
// THE FIRST ROOM — the full runnable scenario.
// =============================================================================

/// Run the FIRST ROOM end to end: the honest earn+spend cycle THEN the try-to-cheat battery, all
/// through ONE real [`EmbeddedExecutor`]. Returns the [`Transcript`] (the example prints it; the
/// tests assert on it). The room is rendered with the inhabitant's held mandate, its genuine
/// receipted job steps, the pay, and every in-room refusal with the receipt-why.
pub fn run_first_room() -> Transcript {
    // ONE cipherclerk drives the ledger as the PAYER/operator (it owns the escrow and seeds the job).
    // The job cell is the INHABITANT's mandate; the escrow cell is the payer's reward pool. Both live
    // in the same ledger, both enforced by the same real executor.
    let payer = AppCipherclerk::new(AgentCipherclerk::new(), [0x42u8; 32]);
    let exec = EmbeddedExecutor::new(&payer, "default");
    let owner = payer.public_key().0;

    // ── ORGAN 3 (economy): the payer LISTS + FUNDS the escrow (the reward, conserved pool) ────────
    let escrow_cell = birth_escrow_cell(&exec, &payer, b"first-room-reward");
    exec.submit_action(
        &payer,
        escrow::build_list_action(&payer, escrow_cell, "the-payer", CEILING),
    )
    .expect("list the reward (ceiling) commits");
    exec.submit_action(
        &payer,
        escrow::build_fund_action(&payer, escrow_cell, "the-room", REWARD),
    )
    .expect("fund the reward (≤ ceiling) commits");
    let funded_reward = read_u64(&exec.cell_state(escrow_cell).unwrap().fields[ESCROWED_SLOT]);

    // ── ORGAN 3 (value): mint the reward as a CONSERVED CREDIT onto a reward-pool VAULT, and give
    //    the colonist a WALLET to be paid into. The pay (below, on completion) is a REAL kernel
    //    `Effect::Transfer` of this credit through the shared `Payable` interface — not a read-only
    //    field — so the colonist genuinely HOLDS its reward and per-asset Σδ=0 conserves. ──────────
    let reward_vault = credit_holder(0xA1);
    let colonist_wallet = credit_holder(0xB2);
    let reward_vault_id = reward_vault.id();
    let colonist_wallet_id = colonist_wallet.id();
    exec.ensure_cell(reward_vault)
        .expect("the reward-pool vault co-places on the one ledger");
    exec.ensure_cell(colonist_wallet)
        .expect("the colonist's wallet co-places on the one ledger");
    let credit_well = credit_well_id();
    exec.with_ledger_mut(|ledger| {
        let op = ledger
            .get_mut(&payer.cell_id())
            .expect("the operator cell exists");
        op.capabilities
            .grant_faceted(credit_well, AuthRequired::None, EFFECT_MINT)
            .expect("grant the operator mint-authority over the CREDIT well");
        op.capabilities
            .grant(reward_vault_id, AuthRequired::None)
            .expect("grant the operator access to the reward vault");
        op.capabilities
            .grant(colonist_wallet_id, AuthRequired::None)
            .expect("grant the operator access to the colonist wallet");
    });
    exec.submit_action(
        &payer,
        payer.make_action(
            reward_vault_id,
            "mint_reward",
            vec![Effect::Mint {
                target: reward_vault_id,
                slot: 0,
                amount: REWARD,
            }],
        ),
    )
    .expect("the cap-gated mint of the conserved reward credit commits");

    // ── ORGANS 1 & 2 (mandate law + job): the inhabitant's JOB cell (full budget, crafter) ────────
    let job_cell = birth_job_cell(&exec, &payer, &owner, b"first-room-colonist", FULL_BUDGET);

    // ── (2) the inhabitant DOES ITS MANDATED JOB step-by-step (each a receipted turn) ─────────────
    let mut job_steps = Vec::new();
    for cursor in 0..JOB_TERMINAL {
        let verb = WorkflowVerb::at_cursor(cursor).expect("verb at cursor");
        let receipt = advance_job_on(&payer, &exec, job_cell, job::crafter_label())
            .unwrap_or_else(|e| panic!("crafter advance {verb:?} should commit, got {e:?}"));
        job_steps.push(JobStepRecord {
            verb,
            cursor_after: cursor_of(&exec, job_cell),
            spend_after: spend_of(&exec, job_cell),
            receipt_hash: receipt.turn_hash,
        });
    }
    let job_done = cursor_of(&exec, job_cell) == JOB_TERMINAL;

    // ── (3) the job is DONE → the payer SHIPS + SETTLES → the escrow RELEASES → the inhabitant is
    //        PAID (a conserving transfer: released == escrowed). Only because the job finished. ────
    let mut paid = 0u64; // the REAL credit the colonist HOLDS after the conserving Transfer.
    let mut conserved = false; // the escrow lifecycle conserved (released + refunded == escrowed).
    let mut credit_conserved = false; // per-asset Σδ=0 over CREDIT across the value leg.
    if job_done {
        // (3a) the economy's STATE MACHINE: ship + settle the lifecycle escrow (the scalar organ
        //      the cheat battery bites on).
        let delivery = escrow::sealed_delivery_digest(b"the-finished-work");
        exec.submit_action(
            &payer,
            escrow::build_ship_action(&payer, escrow_cell, &delivery),
        )
        .expect("ship the finished work commits");
        // Settle the escrow IN FULL (released = escrowed, refunded = 0): conserving by construction.
        exec.submit_action(
            &payer,
            escrow::build_settle_action(&payer, escrow_cell, funded_reward, 0),
        )
        .expect("conserving settlement (release in full) commits");
        let st = exec.cell_state(escrow_cell).unwrap();
        let released = read_u64(&st.fields[RELEASED_SLOT]);
        let settled = read_u64(&st.fields[STATE_SLOT]) == STATE_SETTLED;
        let escrowed = read_u64(&st.fields[ESCROWED_SLOT]);
        let refunded = read_u64(&st.fields[starbridge_escrow_market::REFUNDED_SLOT]);
        conserved = settled && (released + refunded == escrowed);

        // (3b) THE REAL VALUE FLOW — the JOB completion gates a REAL conserving Transfer of the
        //      reward credit from the vault to the colonist's wallet, through the SAME `Payable`
        //      interface escrow-market shares with bounty-board. The colonist now HOLDS the reward
        //      as conserved value (a real on-ledger balance), not a read-only field.
        let vault = EscrowVault::new(reward_vault_id, CREDIT_ASSET);
        let pay_turn = vault
            .release(
                &payer,
                funded_reward,
                colonist_wallet_id,
                InvokeAuthority::Signature,
            )
            .expect("the on-completion pay routes through the shared Payable interface");
        exec.submit_turn(&pay_turn)
            .expect("the conserving reward Transfer (vault → colonist) commits");
        paid = balance_of(&exec, colonist_wallet_id) as u64; // the colonist HOLDS the reward.
        credit_conserved = credit_supply(&exec) == 0; // Σ holders(CREDIT) + well = 0.
    }

    // ── THE HEADLINE: the try-to-cheat battery — each refused IN-BAND by the real executor ────────
    let mut cheats = Vec::new();
    let mut refusals_in_room: Vec<InRoomRefusal> = Vec::new();

    // (a) SKIP A PREREQUISITE — a fresh job, jump cursor 0 → 2 (skip gather). The MonotonicSequence
    //     tooth requires exactly +1. Crafter + the make compartment, so clearance & budget would
    //     pass — ONLY the skip bites.
    {
        let cheat_job = birth_job_cell(&exec, &payer, &owner, b"cheat-skip", FULL_BUDGET);
        let skip = job::advance_effects(
            cheat_job,
            2,
            job::crafter_label(),
            WorkflowVerb::Make.compartment_label(),
        );
        let action = payer.make_action(cheat_job, "advance_step", skip);
        let res = exec.submit_action(&payer, action);
        let o = classify(
            CheatClass::SkipPrerequisite,
            &res,
            &["monotonic", "sequence", "field[0]", "program"],
        );
        // Anti-ghost: nothing committed (cursor holds at 0).
        assert_eq!(cursor_of(&exec, cheat_job), 0, "the skip committed nothing");
        refusals_in_room.push(refusal(&o));
        cheats.push(o);
    }

    // (b) OVERSPEND THE BUDGET — a fresh job on the TIGHT budget (6). gather (spend 3) fits; make
    //     (spend 7 > 6) does not. Crafter clears make (not the clearance tooth), +1 holds (not the
    //     skip tooth) — ONLY the budget tooth bites.
    {
        let cheat_job = birth_job_cell(&exec, &payer, &owner, b"cheat-overspend", TIGHT_BUDGET);
        advance_job_on(&payer, &exec, cheat_job, job::crafter_label())
            .expect("gather fits the tight budget (3 ≤ 6)");
        let res = advance_job_on(&payer, &exec, cheat_job, job::crafter_label());
        let o = classify(
            CheatClass::OverspendBudget,
            &res,
            &["lte", "field", "budget", "program"],
        );
        assert_eq!(
            cursor_of(&exec, cheat_job),
            1,
            "the overspend committed nothing"
        );
        refusals_in_room.push(refusal(&o));
        cheats.push(o);
    }

    // (c) REACH OUTSIDE ITS COMPARTMENT — fund a fresh escrow OVER its ceiling (1500 > 1000). The
    //     trustline tooth (escrowed ≤ ceiling) refuses: the inhabitant cannot draw beyond the bound
    //     it was granted — its reach is exactly its compartment.
    {
        let cheat_escrow = birth_escrow_cell(&exec, &payer, b"cheat-overreach");
        exec.submit_action(
            &payer,
            escrow::build_list_action(&payer, cheat_escrow, "the-payer", CEILING),
        )
        .expect("list commits");
        let res = exec.submit_action(
            &payer,
            escrow::build_fund_action(&payer, cheat_escrow, "the-room", 1500),
        );
        let o = classify(
            CheatClass::ReachOutsideCompartment,
            &res,
            &["lte", "field", "program"],
        );
        refusals_in_room.push(refusal(&o));
        cheats.push(o);
    }

    // (d) TAKE A VERB IT WASN'T GRANTED — a fresh job, advance with a HAULER clearance to the `make`
    //     (crafting) verb. The hauler clears gather (0→1 commits) but does NOT clear make: the
    //     ClearanceDominates tooth refuses. Budget & +1 would pass — ONLY clearance bites.
    {
        let cheat_job = birth_job_cell(&exec, &payer, &owner, b"cheat-ungranted-verb", FULL_BUDGET);
        advance_job_on(&payer, &exec, cheat_job, job::hauler_label())
            .expect("hauler clears gather (hauler→gather edge)");
        let res = advance_job_on(&payer, &exec, cheat_job, job::hauler_label());
        let o = classify(
            CheatClass::UngrantedVerb,
            &res,
            &["dominate", "clearance", "program"],
        );
        assert_eq!(
            cursor_of(&exec, cheat_job),
            1,
            "the ungranted-verb attempt committed nothing"
        );
        refusals_in_room.push(refusal(&o));
        cheats.push(o);
    }

    // (e) RELEASE THE ESCROW WITHOUT APPROVAL — a fresh escrow, funded 800, shipped, then a
    //     settlement that CONJURES value (release 900 from an 800 escrow). The flashwell tooth
    //     (released + refunded == escrowed) refuses: the escrow cannot release more than was put in.
    //     You cannot get paid for value that does not exist.
    {
        let cheat_escrow = birth_escrow_cell(&exec, &payer, b"cheat-unapproved-release");
        exec.submit_action(
            &payer,
            escrow::build_list_action(&payer, cheat_escrow, "the-payer", CEILING),
        )
        .expect("list commits");
        exec.submit_action(
            &payer,
            escrow::build_fund_action(&payer, cheat_escrow, "the-room", REWARD),
        )
        .expect("fund commits");
        let delivery = escrow::sealed_delivery_digest(b"goods");
        exec.submit_action(
            &payer,
            escrow::build_ship_action(&payer, cheat_escrow, &delivery),
        )
        .expect("ship commits");
        let res = exec.submit_action(
            &payer,
            escrow::build_settle_action(&payer, cheat_escrow, 900, 0),
        );
        let o = classify(
            CheatClass::ReleaseWithoutApproval,
            &res,
            &["sum", "affine", "conserv", "eq", "program"],
        );
        // Anti-ghost: the escrow did NOT reach SETTLED on the conjuring settle.
        let st = exec.cell_state(cheat_escrow).unwrap();
        assert_ne!(
            read_u64(&st.fields[STATE_SLOT]),
            STATE_SETTLED,
            "the conjuring settle committed nothing"
        );
        refusals_in_room.push(refusal(&o));
        cheats.push(o);
    }

    // ── RENDER THE ROOM — the inhabitant (job + pay + refusals) and the payer, in-room. ───────────
    let room_cell = CellId::derive_raw(&owner, blake3::hash(b"the-first-room").as_bytes());
    let mut room = Room::new(room_cell, "the workshop");

    let inhabitant = InhabitantView {
        cell: job_cell,
        short: short_hex(&job_cell),
        name: "the colonist".to_string(),
        mandate: format!(
            "JOB: gather→make→hand-off (DAG, no-skip) · clearance: crafter (clears every verb) · budget: {FULL_BUDGET} fuel (provably can't exceed)"
        ),
        committed_actions: job_steps
            .iter()
            .map(|s| GenuineAction {
                summary: format!(
                    "{:?} (step {}→{}, spend {}/{})",
                    s.verb,
                    s.cursor_after - 1,
                    s.cursor_after,
                    s.spend_after,
                    FULL_BUDGET
                ),
                receipt_hash: s.receipt_hash,
            })
            .collect(),
        refusals: refusals_in_room,
        paid,
    };
    room.enter(inhabitant);

    let payer_view = InhabitantView {
        cell: payer.cell_id(),
        short: short_hex(&payer.cell_id()),
        name: "the payer".to_string(),
        mandate: format!(
            "ESCROW: a conserved reward pool (ceiling {CEILING}); releases ONLY a balanced split (released + refunded == escrowed)"
        ),
        committed_actions: vec![
            GenuineAction {
                summary: format!(
                    "escrow funded: {funded_reward} (≤ ceiling {CEILING}) — the reward pool"
                ),
                receipt_hash: [0u8; 32],
            },
            GenuineAction {
                summary: format!(
                    "reward paid: {paid} CREDIT → the colonist — a REAL conserving Transfer (Σδ=0)"
                ),
                receipt_hash: [0u8; 32],
            },
        ],
        refusals: Vec::new(),
        paid: 0,
    };
    room.enter(payer_view);

    Transcript {
        funded_reward,
        job_steps,
        job_done,
        paid,
        conserved,
        credit_conserved,
        cheats,
        room,
    }
}

/// Classify a cheat result: it MUST be refused (an `Err`), and the reason MUST cite one of the
/// expected tooth-keywords (proof the RIGHT guard bit). An accidental success is a FAILURE of the
/// guarantee — surfaced as `refused = false`.
fn classify(
    class: CheatClass,
    res: &Result<dregg_app_framework::TurnReceipt, dregg_app_framework::ExecutorSubmitError>,
    tooth_keywords: &[&str],
) -> CheatOutcome {
    match res {
        Ok(_) => CheatOutcome {
            class,
            refused: false,
            reason: "COMMITTED — the cheat was NOT refused (the guarantee FAILED)".to_string(),
            tooth_cited: false,
        },
        Err(e) => {
            let reason = format!("{e}").to_lowercase();
            let tooth_cited = tooth_keywords.iter().any(|k| reason.contains(k));
            CheatOutcome {
                class,
                refused: true,
                reason,
                tooth_cited,
            }
        }
    }
}

/// Render a cheat outcome as an in-room refusal (the receipt-why surfaced in-room).
fn refusal(o: &CheatOutcome) -> InRoomRefusal {
    InRoomRefusal {
        attempted: o.class.label().to_string(),
        reason: format!("refused by {} — {}", o.class.tooth(), o.reason),
    }
}

// =============================================================================
// DAVID'S DOOR — where a buildr agent walks in via the gateway.
// =============================================================================

/// DAVID'S DOOR — the seam note for a *buildr* agent walking IN as a new inhabitant of the world.
///
/// A buildr agent does not get ambient power; it enters through the WORLD'S PHYSICS (the
/// `starbridge-storage-gateway-mandate` gateway), which hands it a SCOPED mandate. Concretely, the
/// buildr agent:
///   1. arrives at the gateway and is granted a workflow-mandate (a job cell) — born under the
///      gateway's physics exactly as [`birth_job_cell`] births one here, but owned by the buildr
///      agent's key, not the room operator's;
///   2. ENTERS the room (a presence overlay — [`Room::enter`]) holding only that mandate;
///   3. ACTS by advancing its job step-by-step ([`advance_job_on`]) — the SAME three legs bite, so
///      the buildr agent provably cannot skip a step, overspend, reach outside its compartment, or
///      take an ungranted verb;
///   4. is PAID on completion via the escrow ([`starbridge_escrow_market`]) — a conserving transfer.
///
/// This function returns the human-legible seam description; the executable shape is identical to
/// [`run_first_room`] with the job cell owned by the buildr agent's cipherclerk. (The gateway organ
/// — `starbridge-apps/storage-gateway-mandate` — is the physics that scopes the entry; wiring its
/// `init_mandate` factory birth in place of [`birth_job_cell`] is the one remaining wire.)
pub fn davids_door() -> String {
    "DAVID'S DOOR — a buildr agent walks in via the gateway: the gateway (storage-gateway-mandate) \
     hands it a SCOPED workflow-mandate (a job cell owned by the agent's key), it ENTERS the room \
     holding only that mandate, ACTS by advancing its job (the same three legs bite — no skip, no \
     overspend, no out-of-compartment reach, no ungranted verb), and is PAID on completion via the \
     conserving escrow. No ambient power; its reach is exactly the mandate the gateway granted."
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_first_room_holds_end_to_end() {
        // THE GUARANTEE: the honest earn+spend cycle succeeds (job done, paid in full, conserving)
        // AND every cheat is provably refused in-band.
        let t = run_first_room();
        assert!(
            t.first_room_holds(),
            "the first room must hold end-to-end; transcript = {t:#?}"
        );
    }

    #[test]
    fn the_honest_cycle_earns_and_is_paid() {
        // GENUINE ✓: the colonist advances gather→make→hand-off (3 real receipted turns), finishes,
        // and is PAID the full conserved reward.
        let t = run_first_room();
        assert_eq!(t.job_steps.len(), 3, "three job steps committed");
        assert_eq!(t.job_steps[0].verb, WorkflowVerb::Gather);
        assert_eq!(t.job_steps[1].verb, WorkflowVerb::Make);
        assert_eq!(t.job_steps[2].verb, WorkflowVerb::Handoff);
        // Each genuine step carries a REAL receipt (proof it committed).
        for s in &t.job_steps {
            assert_ne!(s.receipt_hash, [0u8; 32], "a real verified turn");
        }
        // Spend tracked the DAG (3, 7, 9) and stayed within budget.
        assert_eq!(t.job_steps[2].spend_after, 9, "total spend == budget");
        assert!(t.job_done, "the job reached its terminal");
        // PAID — the colonist HOLDS the full reward as a REAL conserved CREDIT balance (a kernel
        // Transfer through the shared Payable interface), not a read-only field.
        assert_eq!(t.paid, REWARD, "the colonist holds the full reward");
        assert_eq!(t.paid, t.funded_reward, "paid exactly what was escrowed");
        assert!(t.conserved, "the settlement conserved the escrow lifecycle");
        assert!(
            t.credit_conserved,
            "the REAL value leg conserved (per-asset Σδ=0 over CREDIT)"
        );
    }

    #[test]
    fn every_cheat_is_provably_refused() {
        // CHEAT ✗: each of the five cheat-classes is refused IN-BAND, and the refusal cites the
        // expected tooth (the RIGHT guard bit — not a coincidental failure / not vacuous).
        let t = run_first_room();
        assert_eq!(t.cheats.len(), 5, "five cheat classes");
        let expected = [
            CheatClass::SkipPrerequisite,
            CheatClass::OverspendBudget,
            CheatClass::ReachOutsideCompartment,
            CheatClass::UngrantedVerb,
            CheatClass::ReleaseWithoutApproval,
        ];
        for (o, exp) in t.cheats.iter().zip(expected) {
            assert_eq!(o.class, exp);
            assert!(
                o.refused,
                "cheat [{}] must be REFUSED in-band, got {o:#?}",
                o.class.label()
            );
            assert!(
                o.tooth_cited,
                "cheat [{}] must be refused on its tooth {}, got reason: {}",
                o.class.label(),
                o.class.tooth(),
                o.reason
            );
            assert!(o.provably_refused());
        }
    }

    #[test]
    fn the_room_renders_the_inhabitant_and_the_refusals() {
        // THE ROOM, FELT: the room contains the colonist (held mandate + genuine actions + pay) and
        // the payer; every refusal is surfaced in-room with the receipt-why.
        let t = run_first_room();
        assert_eq!(
            t.room.occupancy(),
            2,
            "the colonist and the payer are in the room"
        );
        let colonist = &t.room.inhabitants[0];
        assert_eq!(colonist.name, "the colonist");
        assert!(!colonist.mandate.is_empty(), "the held mandate is shown");
        assert_eq!(
            colonist.committed_count(),
            3,
            "three genuine job actions rendered"
        );
        assert_eq!(colonist.paid, REWARD, "the pay is rendered in-room");
        // Every cheat rendered as an in-room refusal carrying the why.
        assert_eq!(colonist.refusals.len(), 5, "five in-room refusals");
        for r in &colonist.refusals {
            assert!(!r.attempted.is_empty());
            assert!(
                r.reason.contains("refused by"),
                "the refusal carries the tooth + why: {}",
                r.reason
            );
        }
        // The room-wide refusal surface sees them all.
        assert_eq!(t.room.refusals().len(), 5);
        // The genuine activity is there too (the colonist's 3 committed actions).
        assert_eq!(
            t.room.committed_action_count(),
            3 + 2,
            "colonist 3 + payer 2 (fund/release) shown"
        );
    }
}
