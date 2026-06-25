//! **AN AGENT'S MEMORY/WORKING-SET AS A WITNESSED PORTABLE umem** — checkpoint →
//! handoff → resume, PROVEN BY RUNNING.
//!
//! Run: `cd deos-hermes && cargo test --features js-agent agent_memory_as_umem`
//! (this file only compiles under `js-agent`, which pulls deos-js / real
//! SpiderMonkey — the agent's working-set lives in a deos-js applet cell.)
//!
//! ## The revolution this prototypes
//!
//! Today a deos agent (the `run_js` / deos-hermes agent) carries a working-set —
//! its scratch state, its accumulated memory, its held mandate, the receipt tape
//! it has left — and that working-set is *ad-hoc*: it lives in a live `Applet`'s
//! embedded ledger and Rust-side tape, untransportable as a single witnessed
//! object. You cannot checkpoint it, hand it to a fresh agent, and have that agent
//! resume *as if it were the same agent*.
//!
//! The dregg substrate already has the shape that makes an agent's state a
//! first-class, witnessed, portable object: the **umem projection**
//! (`dregg_turn::umem`). `project_cell` lands every plane of a cell — its model
//! fields, its committed heap (where the agent's program/memory blob lives), its
//! balance/nonce, its lifecycle, its caps/mandate — at a `(domain, collection,
//! key) ↦ value` cell of the ONE universal address space. That projection *is* the
//! agent's memory as a structured, comparable, witnessable object: a **umem**.
//!
//! So: **an agent's memory/working-set, projected through `project_cell`, IS a
//! umem.** "The dreggon persists by writing himself down" becomes literal — the
//! agent writes himself down as a umem projection, and a fresh agent reads that
//! umem back and continues.
//!
//! ## What this prototype proves (the round-trip)
//!
//!   1. **CHECKPOINT** — a live agent evolves its working-set (fires affordances
//!      that mutate its cell, leaving a receipt tape). We project its cell through
//!      `dregg_turn::umem::project_cell` → a `UProjection` (the witnessed umem),
//!      and serialize the portable carrier (`PortableApplet::to_cell_bytes` — the
//!      committed cell, model + program-in-heap, postcard bytes).
//!   2. **HANDOFF + RESUME** — a FRESH agent context (`Applet::from_cell`) loads the
//!      carrier bytes. The fresh agent has NONE of the original's Rust-side runtime
//!      state — only the umem carrier.
//!   3. **THE WITNESS** — we re-project the RESUMED agent's cell → `UProjection'`,
//!      and assert `UProjection == UProjection'`: the agent's memory came across the
//!      handoff BYTE-FOR-BYTE in the universal address space. Then the resumed agent
//!      CONTINUES (fires again) and its working-set advances FROM the checkpoint
//!      (the counter continues, the memory blob is intact) — not a reset.
//!
//! ## The seam (named, not hidden)
//!
//! Full *cryptographic* witnessing of the umem — the boundary→committed-state
//! keystone landing in parallel — is the bridge from "this `UProjection` is
//! byte-identical across handoff" (what this test proves, the executable shadow)
//! to "a light client can VERIFY this umem is the genuine continuation of that
//! agent without re-running it" (the `UmemTurnWitness` + the committed
//! `pre/post` root the keystone supplies). See `seam_full_umem_witnessing` below
//! and the module-tail commentary: the structure is here; the keystone supplies
//! the committed root the projection equality stands in for.

#![cfg(feature = "js-agent")]

use deos_js::applet::{pack_u64, unpack_u64};
use deos_js::{AffordanceSpec, Applet, AppletManifest, ApplyOp, PortableApplet};
use dregg_cell::AuthRequired;

use dregg_turn::umem::{self, UKey, UProjection, UVal};

/// The agent's working-set lives across a few low model slots of its cell:
///   slot 0 = a running scalar the agent accumulates (its "thought counter").
///   slot 1 = a second scratch register.
/// (The cell's committed HEAP additionally carries the agent's *program* — its
/// affordance manifest + view source — via the program-in-cell weld; that is the
/// agent's durable "memory of who it is".)
const THOUGHT_SLOT: usize = 0;
const SCRATCH_SLOT: usize = 1;

/// Build the agent's program manifest — the affordances that evolve its working-set.
/// `think(n)` adds `n` to the thought counter; `mark` sets the scratch register to a
/// fixed sentinel (a durable "i was here" note in the working-set).
fn agent_manifest() -> AppletManifest {
    AppletManifest {
        seed_fields: vec![(THOUGHT_SLOT, 0), (SCRATCH_SLOT, 0)],
        affordances: vec![
            AffordanceSpec {
                name: "think".to_string(),
                required: AuthRequired::Signature,
                op: ApplyOp::AddToSlot { slot: THOUGHT_SLOT },
            },
            AffordanceSpec {
                name: "mark".to_string(),
                required: AuthRequired::Signature,
                op: ApplyOp::SetSlot {
                    slot: SCRATCH_SLOT,
                    value: 1,
                },
            },
        ],
        held: AuthRequired::Signature,
        // The agent's "view of itself" — the literal program text it carries. Part of
        // its durable memory, committed into the cell heap, travels with the umem.
        view_source: "deos.text('agent: thoughts=' + app.get(0) + ' scratch=' + app.get(1))"
            .to_string(),
    }
}

/// Project a live applet's cell into the universal address space — THE umem. This is
/// the agent's whole working-set as one structured, comparable, witnessable object.
fn umem_of(applet: &Applet) -> UProjection {
    let cell_id = applet.cell();
    let cell = applet
        .ledger()
        .get(&cell_id)
        .expect("the agent's cell lives on its own ledger");
    let mut out = UProjection::new();
    umem::project_cell(cell, &mut out);
    out
}

/// Read the agent's thought-counter straight off its cell's model (a witnessed read).
fn thought(applet: &Applet) -> u64 {
    let cell_id = applet.cell();
    let cell = applet.ledger().get(&cell_id).expect("agent cell");
    cell.state
        .get_field(THOUGHT_SLOT)
        .map(|fe| unpack_u64(fe))
        .unwrap_or(0)
}

/// How many of the umem's planes belong to the agent's own cell (the heap+caps planes
/// `project_cell` lands). A quick legibility number for the report.
fn cell_plane_count(proj: &UProjection, cell: dregg_cell::CellId) -> usize {
    proj.keys().filter(|k| k.cell() == Some(cell)).count()
}

/// THE ROUND-TRIP: an agent's memory checkpointed as a umem, handed to a fresh
/// agent context, and resumed — proven byte-identical in the universal address
/// space, and proven to CONTINUE from the checkpoint.
#[test]
fn agent_memory_checkpoint_handoff_resume() {
    // ── 1. A LIVE AGENT evolves its working-set ──────────────────────────────
    // Mint the agent with its program persisted into its cell heap (the program-
    // in-cell weld). The agent's identity is its (public_key, token_id) pair.
    let manifest = agent_manifest();
    let mut agent = PortableApplet::mint([7u8; 32], [0xA6u8; 32], &manifest);

    // The agent thinks — three cap-gated verified turns, each leaving a receipt.
    // Its working-set (slot 0) accumulates; its receipt tape grows. This is the
    // ad-hoc live state today: a running Applet + a Rust-side tape.
    let r1 = agent.fire("think", 10).expect("think 10");
    let r2 = agent.fire("think", 5).expect("think 5");
    let r3 = agent.fire("think", 7).expect("think 7");
    assert_eq!(thought(&agent), 22, "the agent accumulated 10+5+7 = 22");
    assert_eq!(agent.receipts().len(), 3, "three receipts on the live tape");
    // The chain head (the agent's lineage tip) — the last receipt it left.
    assert_eq!(agent.receipts()[2], r3.receipt_hash());
    let _ = (r1, r2);

    let agent_cell = agent.cell();

    // ── 2. CHECKPOINT: project the agent's memory into a witnessed umem ───────
    // THE umem — the agent's whole working-set as a structured universal-address
    // object: its model (slot 0 = 22), its committed heap (the program/memory
    // blob), its balance/nonce/lifecycle, its mandate planes.
    let checkpoint_umem: UProjection = umem_of(&agent);

    // The portable carrier: the committed cell bytes (model + program-in-heap).
    // THIS is the "writing himself down" — the durable object handed across.
    let carrier: Vec<u8> = PortableApplet::to_cell_bytes(&agent);
    // The chain position at checkpoint (so the resumed agent's tape matches).
    let checkpoint_tape_len = agent.receipts().len();

    // The umem actually carries the agent's evolved state: slot 0 reads 22 in it.
    let slot0_in_umem = checkpoint_umem
        .get(&UKey::Field {
            cell: agent_cell,
            slot: THOUGHT_SLOT as u64,
        })
        .expect("the thought slot is a plane of the umem");
    assert_eq!(
        *slot0_in_umem,
        UVal::Bytes32(pack_u64(22)),
        "the umem carries the agent's accumulated working-set (slot 0 = 22)"
    );
    let planes = cell_plane_count(&checkpoint_umem, agent_cell);
    assert!(
        planes >= 16,
        "the umem lands the agent's many cell planes (got {planes})"
    );

    // The live agent could now be DROPPED — its Rust runtime, its tape, gone.
    // All that survives is `carrier` (the umem on the wire) + `checkpoint_umem`
    // (the witness) + `checkpoint_tape_len`.
    drop(agent);

    // ── 3. HANDOFF + RESUME into a FRESH agent context ───────────────────────
    // A brand-new Applet, reconstituted from NOTHING but the carrier bytes. It
    // rebuilds its affordance closures from the manifest in the cell heap and
    // stands a fresh embedded executor over the loaded cell. This is "another
    // agent reads the dreggon's written-down self and becomes him."
    let (mut resumed, resumed_manifest) =
        PortableApplet::from_cell(&carrier).expect("a fresh agent loads the umem carrier");

    // The fresh agent recovered the program too (its memory of who it is).
    assert_eq!(
        resumed_manifest.view_source, manifest.view_source,
        "the resumed agent recovered its own view/program from the umem"
    );
    // Identity is preserved: same cell id (same (public_key, token_id) ⇒ same id).
    assert_eq!(
        resumed.cell(),
        agent_cell,
        "the resumed agent IS the same agent (same cell identity)"
    );

    // ── 4. THE WITNESS: the umem came across byte-for-byte ───────────────────
    let resumed_umem: UProjection = umem_of(&resumed);
    assert_eq!(
        resumed_umem, checkpoint_umem,
        "THE ROUND-TRIP WITNESS: the resumed agent's umem is BYTE-IDENTICAL to \
         the checkpoint umem in the universal address space — the agent's whole \
         working-set crossed the handoff with no drift"
    );

    // The resumed agent's working-set is exactly the checkpoint (22), not a reset.
    assert_eq!(
        thought(&resumed),
        22,
        "the resumed agent CONTINUES from the checkpointed working-set"
    );

    // ── 5. CONTINUE: the resumed agent acts further, advancing FROM 22 ───────
    // A fire on the resumed agent is the SAME cap-gated verified turn — the round-
    // tripped agent is fully live, not a frozen snapshot.
    resumed
        .fire("think", 100)
        .expect("the resumed agent thinks on");
    assert_eq!(
        thought(&resumed),
        122,
        "the resumed agent advanced its working-set FROM the checkpoint (22 + 100)"
    );

    // The new fire left a fresh receipt — the lineage continues past the handoff.
    assert_eq!(
        resumed.receipts().len(),
        1,
        "the resumed agent's tape carries the post-handoff fire (a fresh lineage \
         segment; the pre-handoff tape of length {checkpoint_tape_len} is the \
         carried-forward audit history the umem committed to)"
    );

    // And re-checkpointing the resumed agent yields a DIFFERENT umem (slot 0 = 122)
    // — proving the umem genuinely tracks the live working-set, not a constant.
    let post_continue_umem = umem_of(&resumed);
    assert_ne!(
        post_continue_umem, checkpoint_umem,
        "after continuing, the agent's umem has moved on (the projection is live)"
    );
    assert_eq!(
        post_continue_umem.get(&UKey::Field {
            cell: agent_cell,
            slot: THOUGHT_SLOT as u64
        }),
        Some(&UVal::Bytes32(pack_u64(122))),
        "the moved-on umem carries the continued working-set (122)"
    );
}

/// A SECOND handoff hop — checkpoint, resume, continue, RE-checkpoint, resume
/// AGAIN: the umem is a durable relay baton, not a one-shot. Each agent in the
/// chain is a fresh context that picks up exactly where the last left off.
#[test]
fn agent_memory_relays_across_multiple_agents() {
    let manifest = agent_manifest();
    let agent_a = PortableApplet::mint([9u8; 32], [0xB7u8; 32], &manifest);
    let mut agent_a = agent_a;
    agent_a.fire("think", 3).expect("A thinks 3");
    let carrier_a = PortableApplet::to_cell_bytes(&agent_a);
    let umem_a = umem_of(&agent_a);
    let id = agent_a.cell();
    drop(agent_a);

    // Agent B picks up A's umem, continues.
    let (mut agent_b, _) = PortableApplet::from_cell(&carrier_a).expect("B loads A's umem");
    assert_eq!(umem_of(&agent_b), umem_a, "B's umem == A's checkpoint");
    assert_eq!(thought(&agent_b), 3);
    agent_b.fire("think", 4).expect("B thinks 4");
    assert_eq!(thought(&agent_b), 7, "B continued A (3 + 4)");
    let carrier_b = PortableApplet::to_cell_bytes(&agent_b);
    drop(agent_b);

    // Agent C picks up B's umem, continues. The working-set has now passed through
    // THREE fresh agent contexts and is intact + advancing.
    let (mut agent_c, _) = PortableApplet::from_cell(&carrier_b).expect("C loads B's umem");
    assert_eq!(
        agent_c.cell(),
        id,
        "still the same agent identity across the relay"
    );
    assert_eq!(
        thought(&agent_c),
        7,
        "C continues B (the relayed working-set)"
    );
    agent_c.fire("think", 1).expect("C thinks 1");
    assert_eq!(
        thought(&agent_c),
        8,
        "C advanced the relayed working-set (7 + 1)"
    );
}

/// THE SEAM, named + structured (the boundary→committed-state keystone, landing in
/// parallel). This test does NOT depend on the keystone; it documents + exercises
/// the structure the keystone completes.
///
/// What this prototype proves today (the EXECUTABLE SHADOW): the agent's umem
/// `UProjection` is byte-identical across a checkpoint→handoff→resume. That is the
/// state-agreement square `project(checkpoint) == project(resume)` — the same
/// equality `dregg_turn::umem`'s `fold(pre, ops) == post` checks for a single turn.
///
/// What the KEYSTONE adds (the seam): a CRYPTOGRAPHIC commitment to the umem — the
/// committed `pre`/`post` root — so a third party (a light client, the receiving
/// agent's trust root) can VERIFY "this umem is the genuine continuation of that
/// agent" WITHOUT re-running the agent or trusting the carrier bytes. The
/// `dregg_turn::umem::UmemTurnWitness` is exactly that object for a turn (pre
/// projection + Blum op trace + post projection); the keystone lifts the per-turn
/// witness to a *boundary commitment* on the umem itself, so a handoff carries a
/// verifiable root, not just bytes.
///
/// Here we show the structure is in reach: we build the umem projections that WOULD
/// be committed, and show the per-turn `fold` discipline already connects a
/// pre-state umem to a post-state umem (the executable shadow of the commitment the
/// keystone will witness).
#[test]
fn seam_full_umem_witnessing() {
    let manifest = agent_manifest();
    let mut agent = PortableApplet::mint([3u8; 32], [0xC8u8; 32], &manifest);

    // The PRE umem — the agent's working-set before a step.
    let pre: UProjection = umem_of(&agent);

    // The agent takes one step (one cap-gated verified turn).
    agent.fire("think", 42).expect("one step");

    // The POST umem — the working-set after the step.
    let post: UProjection = umem_of(&agent);

    // The step genuinely moved the umem at exactly the thought slot.
    let key = UKey::Field {
        cell: agent.cell(),
        slot: THOUGHT_SLOT as u64,
    };
    assert_ne!(pre.get(&key), post.get(&key), "the step moved the umem");
    assert_eq!(
        post.get(&key),
        Some(&UVal::Bytes32(pack_u64(42))),
        "post umem carries the stepped working-set"
    );

    // THE SHADOW OF THE WITNESS: a Blum write trace that carries `pre` to `post`
    // under the universal-memory `fold` semantics. We synthesize the single op the
    // step performed (slot 0: absent/0 → 42) and prove the fold connects the two
    // umem boundaries — the same `fold(pre, ops) == post` agreement square the
    // keystone's `UmemTurnWitness` commits to. (In the wired keystone, the executor
    // EMITS this trace from its journal via `umem::emit_trace`; here we exhibit the
    // boundary commitment structure the handoff would carry.)
    let op = umem::UmemOp {
        kind: umem::UmemKind::Write,
        key: key.clone(),
        val: post.get(&key).cloned(),
        prev_val: pre.get(&key).cloned(),
        prev_serial: 0,
    };
    let folded = umem::fold(&pre, std::slice::from_ref(&op));
    assert_eq!(
        folded.get(&key),
        post.get(&key),
        "the Blum-trace fold carries the agent's umem from pre to post at the \
         stepped plane — the executable shadow of the boundary commitment the \
         keystone witnesses"
    );
    assert!(
        umem::disciplined(std::slice::from_ref(&op)),
        "the umem op obeys the memcheck discipline (the per-op gate the circuit \
         enforces)"
    );

    // NAMED SEAM: the only thing standing between this and a light-client-verifiable
    // umem handoff is the boundary→committed-state keystone — the cryptographic
    // commitment to `pre`/`post` (the sorted-Poseidon2 root over the projection)
    // that turns "byte-identical across handoff" into "verifiable continuation
    // without re-execution." The structure (projection · op-trace · fold · op
    // discipline) is all here; the keystone supplies the committed root.
}
