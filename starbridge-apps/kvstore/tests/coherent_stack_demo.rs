//! # The coherent end-to-end deos demo — ONE story, ONE live `World`.
//!
//! This walks the now-proven stack as a SINGLE narrative over one live
//! [`EmbeddedExecutor`] (one `AgentRuntime` → one `dregg_cell::Ledger` + one
//! `TurnExecutor`), proving the session's pieces compose into one system. Every
//! mutating step is an ordinary cap-gated turn (no GM self-grant superpower — the
//! producer SWAP-vetoes that; we only ever use ordinary effects + the published
//! service interface) leaving a real receipt, and the document + time-travel
//! steps ride the SAME ledger the turns drive.
//!
//! The five movements (each asserted, and narrated to stdout — run with
//! `--nocapture` to read the transcript):
//!
//! 1. **Mint a couple of cells.** Two real `Effect::CreateCell` turns birth a
//!    `companion` cell and a locked `vault` cell into the live ledger, each with
//!    a receipt.
//! 2. **Invoke a service-cell method, and watch the invariant bite.** The agent
//!    cell IS a key-value store ([`KvStore`], the cells-as-service-objects
//!    exemplar): `put` is driven through the `invoke()` front door, desugars to
//!    ordinary verified `SetField`s, and commits. Then a `put` that would roll
//!    the store version BACK is refused on the verified `StateConstraint::Monotonic`
//!    invariant by the EXECUTOR — not a userspace check.
//! 3. **Fork → diverge → stitch → resolve a document, on the umem-heap.** A
//!    document is forked into two branches; the branches diverge (a clashing
//!    title); the stitch (the categorical pushout `merge`) yields a FIRST-CLASS
//!    CONFLICT held off-heap as a `DocGraph`; that conflict is PUBLISHED to the
//!    umem-heap (a sovereign `DocHeapCell` whose committed `heap_root` binds BOTH
//!    alternatives) and inserted into the same live `World`; then a resolving
//!    patch collapses the conflict and the boundary moves, re-published into the
//!    ledger.
//! 4. **Scrub time-travel.** Snapshot the whole-ledger umem boundary at height H
//!    ([`project_ledger`]), advance the World with a real turn, then restore the
//!    past boundary ([`reify_ledger`]) — byte-identical, cell-for-cell, to the
//!    height-H world.
//! 5. **An unauthorized op refused by the executor's authority gate.** The agent
//!    submits a `SetField` against the `vault` it does not own; the executor's
//!    authority gate refuses it on the verified commit path, and the vault is
//!    untouched (anti-ghost).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    field_from_u64,
};
use dregg_cell::Cell;
use dregg_doc::{Author, DocGraph, Op, Patch, content, merge, resolve_field};
use dregg_doc::{COLL_FIELDS, DocHeapCell};
use dregg_turn::action::Effect;
use dregg_turn::umem::{project_ledger, reify_ledger};
use dregg_types::CellId;
use starbridge_kvstore::{KvStore, REG_MIN, VERSION_SLOT, register_interface, store_program};

/// The id a `CreateCell` turn births for `(public_key, token_id)` — the executor
/// inserts `Cell::with_balance(pk, token, 0)`, whose id is this.
fn minted_id(public_key: [u8; 32], token_id: [u8; 32]) -> CellId {
    Cell::with_balance(public_key, token_id, 0).id()
}

#[test]
fn the_whole_stack_coheres_into_one_world() {
    // ── ONE live World: a cipherclerk, an embedded executor (its own ledger +
    //    TurnExecutor), and the agent cell installed as a key-value SERVICE cell. ──
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0xC0; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let store_cell = cclerk.cell_id();

    println!(
        "\n=== ONE live World — store cell {} ===",
        short(&store_cell)
    );

    // ===================================================================
    // 1. MINT A COUPLE OF CELLS — two real CreateCell turns.
    //    (Done before the store cell becomes a method-dispatching SERVICE
    //    cell, whose Cases program would default-deny a non-service method.)
    // ===================================================================
    let companion_pk = [0xC1; 32];
    let vault_pk = [0xA7u8; 32]; // a distinct owner the agent cannot sign for
    let token = [0u8; 32];
    let companion_id = minted_id(companion_pk, token);
    let vault_id = minted_id(vault_pk, token);

    for (label, pk) in [("companion", companion_pk), ("vault", vault_pk)] {
        let action = cclerk.make_self_action(
            "mint",
            vec![Effect::CreateCell {
                public_key: pk,
                token_id: token,
                balance: 0,
            }],
        );
        let turn = cclerk.make_turn(action);
        let receipt = executor
            .submit_turn(&turn)
            .unwrap_or_else(|e| panic!("minting {label} must commit: {e}"));
        assert_ne!(receipt.turn_hash, [0u8; 32], "a real mint receipt");
        println!(
            "1. minted {label} = {} (receipt {})",
            short_id(pk, token),
            short_hash(&receipt.turn_hash)
        );
    }
    assert!(
        executor.cell_state(companion_id).is_some(),
        "companion is in the World"
    );
    assert!(
        executor.cell_state(vault_id).is_some(),
        "vault is in the World"
    );

    // Install the published key-value SERVICE interface on the agent cell — it is
    // now a cells-as-service-object store. The Service Explorer resolves its typed
    // interface from a userspace registry (NOT a committed cell field).
    executor.install_program(store_cell, store_program());
    let store = KvStore::new(store_cell);
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, store.cell);
    assert!(registry.get(&store.cell).is_some(), "interface published");

    // ===================================================================
    // 2. INVOKE A SERVICE METHOD — and the Monotonic invariant bites.
    // ===================================================================
    // An authorized put through invoke(): desugars to ordinary SetFields, commits.
    let put1 = store
        .put(&cclerk, REG_MIN, [9u8; 32], 1, InvokeAuthority::Signature)
        .expect("a Signature holder builds put(REG_MIN, .., v=1)");
    executor
        .submit_turn(&put1)
        .expect("put commits a verified turn");
    let st = executor.cell_state(store.cell).unwrap();
    assert_eq!(
        st.fields[REG_MIN], [9u8; 32],
        "the register holds the value"
    );
    assert_eq!(st.fields[VERSION_SLOT], field_from_u64(1), "version → 1");
    println!("2. invoke put(reg={REG_MIN}) committed; store version = 1");

    // A forward bump commits (Monotonic permits it).
    let put2 = store
        .put(
            &cclerk,
            REG_MIN + 1,
            [7u8; 32],
            2,
            InvokeAuthority::Signature,
        )
        .unwrap();
    executor
        .submit_turn(&put2)
        .expect("forward version bump commits");
    assert_eq!(
        executor.cell_state(store.cell).unwrap().fields[VERSION_SLOT],
        field_from_u64(2)
    );

    // A put that would roll the version BACK builds (front door passes), but the
    // EXECUTOR refuses on the verified Monotonic(VERSION) caveat — protocol, not
    // userspace. Anti-ghost: it commits nothing.
    let rollback = store
        .put(
            &cclerk,
            REG_MIN + 2,
            [2u8; 32],
            1,
            InvokeAuthority::Signature,
        )
        .expect("the rollback invocation BUILDS");
    let rejected = executor.submit_turn(&rollback);
    assert!(
        rejected.is_err(),
        "the executor must refuse a version rollback"
    );
    println!(
        "   rollback put refused by the executor: {}",
        oneline(&rejected.unwrap_err())
    );
    let st = executor.cell_state(store.cell).unwrap();
    assert_eq!(st.fields[REG_MIN + 2], [0u8; 32], "rollback wrote nothing");
    assert_eq!(
        st.fields[VERSION_SLOT],
        field_from_u64(2),
        "version held at 2"
    );

    // ===================================================================
    // 3. FORK → DIVERGE → STITCH → RESOLVE — a document on the umem-heap.
    // ===================================================================
    // Fork: one base document, two branches that share it.
    let base = DocGraph::new();
    let branch_a = base.clone();
    let branch_b = base.clone();

    // Diverge: each branch sets the canonical title differently — a clash.
    let diverged_a = Patch::by(
        Author(1),
        [Op::SetField {
            name: "title".into(),
            value: "Cats".into(),
            superseding: false,
        }],
    )
    .apply_to(&branch_a);
    let diverged_b = Patch::by(
        Author(2),
        [Op::SetField {
            name: "title".into(),
            value: "Dogs".into(),
            superseding: false,
        }],
    )
    .apply_to(&branch_b);

    // Stitch: the categorical pushout (merge). The missing order is not a failure
    // — it becomes a FIRST-CLASS CONFLICT, held off-heap as a DocGraph.
    let stitched = merge(&diverged_a, &diverged_b);
    assert_eq!(
        content(&stitched).field_conflicts().count(),
        1,
        "the stitch yields exactly one first-class field conflict (held off-heap)"
    );
    println!("3. fork→diverge→stitch: 1 first-class conflict (Cats vs Dogs), held off-heap");

    // Publish the conflict to the umem-heap: a sovereign DocHeapCell whose
    // committed heap_root binds BOTH alternatives. Insert it into the SAME World.
    let mut doc = DocHeapCell::from_graph(0x3D, stitched);
    let conflict_boundary = doc.commitment();
    assert_eq!(
        conflict_boundary,
        doc.cell().state.heap_root,
        "commitment IS the umem boundary"
    );
    assert!(
        doc.heap_membership(COLL_FIELDS, 0).is_some()
            && doc.heap_membership(COLL_FIELDS, 1).is_some(),
        "BOTH clashing alternatives are leaves bound by the umem boundary"
    );
    let doc_id = doc.cell_id();
    executor
        .ensure_cell(doc.cell().clone())
        .expect("the sovereign document cell joins the live World");
    assert_eq!(
        executor.cell_state(doc_id).unwrap().heap_root,
        conflict_boundary,
        "the published conflict's umem boundary is committed in the live ledger"
    );
    println!(
        "   published conflict to umem-heap: doc cell {} boundary {}",
        short(&doc_id),
        short_hash(&conflict_boundary)
    );

    // Resolve: a later patch (a superseding field write) collapses the conflict.
    // The umem boundary MOVES; re-publish it into the live World.
    let resolve = resolve_field(Author(1), "title", "Cats");
    let resolved_boundary = doc.apply(resolve);
    assert_ne!(
        resolved_boundary, conflict_boundary,
        "resolution moved the umem boundary"
    );
    assert_eq!(
        content(doc.graph()).field_conflicts().count(),
        0,
        "the conflict is resolved — the document is conflict-free"
    );
    executor.with_ledger_mut(|l| {
        l.get_mut(&doc_id).unwrap().state = doc.cell().state.clone();
    });
    assert_eq!(
        executor.cell_state(doc_id).unwrap().heap_root,
        resolved_boundary,
        "the resolved umem boundary is re-published in the live ledger"
    );
    println!(
        "   resolve: 0 conflicts; boundary moved to {}",
        short_hash(&resolved_boundary)
    );

    // ===================================================================
    // 4. SCRUB TIME-TRAVEL — snapshot H, advance, restore (byte-identical).
    // ===================================================================
    // Snapshot the whole-ledger umem boundary at height H (a clone of the world
    // at H, and its projection).
    let ledger_h = executor.with_ledger_mut(|l| l.clone());
    let boundary_h = project_ledger(&ledger_h);
    let h_ids: Vec<CellId> = vec![store_cell, companion_id, vault_id, doc_id];

    // Advance: a real verified put past H — the World genuinely moves.
    let put3 = store
        .put(
            &cclerk,
            REG_MIN + 3,
            [5u8; 32],
            3,
            InvokeAuthority::Signature,
        )
        .unwrap();
    executor.submit_turn(&put3).expect("advancing put commits");
    let boundary_now = project_ledger(&executor.with_ledger_mut(|l| l.clone()));
    assert_ne!(
        boundary_now, boundary_h,
        "advancing moved the umem boundary"
    );
    assert_eq!(
        executor.cell_state(store.cell).unwrap().fields[VERSION_SLOT],
        field_from_u64(3),
        "the live World advanced to store version 3"
    );
    println!("4. snapshot at H (version 2) → advanced to version 3");

    // Restore: reify the H boundary back into a live, byte-identical Ledger.
    let restored = reify_ledger(&boundary_h).expect("the H boundary reifies to a live ledger");
    for id in &h_ids {
        assert_eq!(
            restored.get(id),
            ledger_h.get(id),
            "reified cell {} is byte-identical to the height-H world",
            short(id)
        );
    }
    // The restored store version is the PAST value (2), not the advanced one (3).
    assert_eq!(
        restored.get(&store_cell).unwrap().state.fields[VERSION_SLOT],
        field_from_u64(2),
        "time-travel restored the PAST store version (2), reversing the advance"
    );
    // The restored document still binds the resolved boundary it had at H.
    assert_eq!(
        restored.get(&doc_id).unwrap().state.heap_root,
        resolved_boundary,
        "the restored document's umem boundary is exactly its height-H boundary"
    );
    println!(
        "   reify_ledger restored {} cells byte-identical to height H",
        h_ids.len()
    );

    // ===================================================================
    // 5. AN UNAUTHORIZED OP — refused by the executor's authority gate.
    // ===================================================================
    // The agent submits a SetField against the `vault` it does not own. The front
    // door is bypassed (this is a raw effect, not an invoke); the EXECUTOR's
    // authority gate refuses it on the verified commit path.
    let vault_before = executor.cell_state(vault_id).unwrap().fields[REG_MIN];
    let trespass = cclerk.make_action(
        vault_id,
        "trespass",
        vec![Effect::SetField {
            cell: vault_id,
            index: REG_MIN,
            value: [0xEE; 32],
        }],
    );
    let trespass_turn = cclerk.make_turn(trespass);
    let refused = executor.submit_turn(&trespass_turn);
    assert!(
        refused.is_err(),
        "the executor's authority gate must refuse a write to a cell the agent does not own"
    );
    println!(
        "5. unauthorized write to vault refused by the executor: {}",
        oneline(&refused.unwrap_err())
    );

    // Anti-ghost: the vault is untouched.
    assert_eq!(
        executor.cell_state(vault_id).unwrap().fields[REG_MIN],
        vault_before,
        "the refused write committed nothing — the vault is untouched"
    );

    println!("=== all five movements cohere on ONE live World ===\n");
}

// ── transcript helpers ──
fn short(id: &CellId) -> String {
    short_hash(&id.0)
}
fn short_id(pk: [u8; 32], token: [u8; 32]) -> String {
    short(&minted_id(pk, token))
}
fn short_hash(b: &[u8; 32]) -> String {
    b[..4].iter().map(|x| format!("{x:02x}")).collect()
}
fn oneline(e: &impl std::fmt::Display) -> String {
    e.to_string().lines().next().unwrap_or("").to_string()
}
