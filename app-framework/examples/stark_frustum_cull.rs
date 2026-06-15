//! `stark_frustum_cull` — frustum-culling the semantic graph with a **REAL STARK**, and
//! the **non-amplification proof obligation made concrete**: a darkened per-viewer
//! snapshot provably **cannot even prove** the fuller view.
//!
//! This is the sharper sibling of `examples/stark_rehydrate.rs`. That example shows a
//! STARK-gated snapshot re-expanding per-viewer (the root sees the full surface, a
//! weaker viewer a narrower one) and the anti-ghost teeth (a tampered PI 35, a foreign
//! descriptor, both rejected). This example presses on the ONE claim a screenshot of the
//! semantic graph has to earn to be more than a pretty lattice projection:
//!
//!   > A *darkened* frustum-snapshot — the per-viewer slice a weaker membrane re-expands —
//!   > carries a real STARK that attests **only the darkened endpoint**. Holding that
//!   > proof, the weaker viewer **cannot forge the fuller view**: there is no way to
//!   > present the darkened proof as a proof of the fuller surface's endpoint. You
//!   > provably cannot even *prove* the stronger view.
//!
//! ## Why this is "frustum culling the semantic graph", with teeth
//!
//! A graphics frustum cull throws away geometry outside the view volume; a deos
//! frustum-snapshot throws away the slice of the **semantic graph** the viewer's
//! capability does not admit. The novelty over a dead screenshot is that the surviving
//! slice re-expands into a *live, verifiable* interactive fragment. The novelty over a
//! mere cap-projection is the gate: the slice's faithfulness is a **STARK** of the turn
//! that produced it (Tier B), not a walk over a receipt log (Tier A). This example makes
//! the *cull itself non-amplifying in the proof system*:
//!
//!   - The **fuller** surface ends at endpoint commitment `Cfull` (PI 35 of its leg).
//!   - The **darkened** surface ends at a DIFFERENT endpoint commitment `Cdark` (PI 35
//!     of *its* leg) — a genuinely smaller state transition (a smaller debit).
//!   - The descriptor's in-circuit Poseidon2 hash sites FORCE PI 35 to be the genuine
//!     post-state commitment of whatever execution the proof witnesses. So the darkened
//!     proof can attest `Cdark` and ONLY `Cdark`. Splicing `Cfull` into the darkened
//!     proof's PI 35 and re-verifying is UNSAT — the exact shape of the anti-ghost
//!     tamper tooth, but here it is *the forgery of a stronger view* that it forecloses.
//!
//! Two independent walls therefore stand between the weaker viewer and the fuller view,
//! and we exhibit BOTH:
//!   (W1) the **STARK** wall — the darkened proof cannot be made to attest `Cfull`
//!        (`verify_stark_proof_against` rejects the spliced PI vector); and
//!   (W2) the **membrane** wall — the weaker holder's authority cannot project the
//!        fuller lineage at all (`is_attenuation` refuses; no projection is minted).
//! Either alone would suffice; together they are the non-amplification proof obligation,
//! concrete and runnable.
//!
//! Everything load-bearing is an EXISTING function composed, nothing reinvented:
//!   - `mint_transfer_leg` (mints a real rotated `Ir2BatchProof` over genuine cells),
//!   - `StarkSnapshot` / `rehydrate_for` (the frustum-snapshot + per-viewer membrane),
//!   - `verify_stark_leg` / `verify_stark_proof_against` (the Lean-free STARK verify),
//!   - `Membrane` + `dregg_cell::is_attenuation` (the real cap lattice),
//!   - `EmbeddedExecutor` (a real committed turn supplies the surface state).
//!
//! Run it:
//!
//! ```sh
//! cargo run -p dregg-app-framework --example stark_frustum_cull
//! ```
//!
//! It narrates, mints + verifies TWO real STARKs, exhibits the two non-amplification
//! walls, and exits 0 iff every prove→verify and every must-reject landed as designed.

use dregg_app_framework::stark_rehydrate::{
    mint_transfer_leg, verify_stark_leg, verify_stark_proof_against, StarkRehydrateError,
    StarkSnapshot, TransferTurn, PI_NEW_COMMIT, PI_OLD_COMMIT,
};
use dregg_app_framework::{
    AffordanceSpec, AgentCipherclerk, AppCipherclerk, AppSpec, AuthRequired, CellSpec,
    EmbeddedExecutor, Membrane, RehydrateError,
};
use dregg_cell::Cell;
use dregg_circuit::field::BabyBear;

/// A "gallery" cell with three tiers of affordance — the surface we frustum-cull.
/// `view@signature` is the darkened (weak-viewer) slice; `curate@either` and
/// `admin@none` are the fuller slices only the owner's lineage admits.
fn gallery_spec() -> AppSpec {
    AppSpec::new("stark-gallery")
        .cell(
            CellSpec::new("gallery")
                .affordance(AffordanceSpec::emit("view", "signature", "frame-viewed"))
                .affordance(AffordanceSpec::edit("curate", "either", 1))
                .affordance(AffordanceSpec::emit("admin", "none", "gallery-admin"))
                .publish("signature"),
        )
        .discoverable(vec!["gallery".into()])
}

/// Open permissions so the rotated producer-witness path admits the actor cell without
/// auth gating (the audited rotated-mint shape — same as the sibling example).
fn open_permissions() -> dregg_cell::Permissions {
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// Mint a real rotated transfer leg debiting `amount` from `(balance, nonce)` — genuine
/// before/after cells, a genuine self-verifying `Ir2BatchProof`. The leg's PI 35 is the
/// Poseidon2 commitment of the resulting `(balance - amount, nonce)` post-state.
fn mint_leg(balance: u64, nonce: u32, amount: u64) -> dregg_app_framework::stark_rehydrate::RotatedParticipantLeg {
    let before = producer_cell(balance as i64, nonce as u64);
    let after = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let turn = TransferTurn { balance, nonce, amount };
    mint_transfer_leg(&turn, &before, &after).expect("the rotated transfer leg mints + self-verifies")
}

fn main() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5A; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let app = gallery_spec()
        .into_app(cclerk.clone(), executor.clone())
        .expect("the gallery spec is valid");
    let gallery = app.cells()[0].clone();
    let actor = cclerk.cell_id();

    println!("== {} — frustum-culling the semantic graph with a REAL STARK ==\n", app.name());
    println!(
        "  the claim under test: a DARKENED per-viewer snapshot carries a STARK of ONLY the\n  \
         darkened endpoint — the weaker viewer provably CANNOT prove the fuller view.\n"
    );

    // ── 1) A real committed turn supplies the surface state ─────────────────────
    println!("(1) a real verified turn through the embedded executor (the surface state is its output):");
    let receipt = executor
        .submit_action(&cclerk, cclerk.make_self_action("open-gallery", vec![]))
        .expect("the executor commits the turn");
    assert_ne!(receipt.turn_hash, [0u8; 32]);
    let live = executor
        .cell_state(actor)
        .expect("the executor's actor cell is live in the ledger");
    let balance = live.balance().max(0) as u64;
    let nonce = live.nonce() as u32;
    println!(
        "    committed turn {}…; the live actor cell: balance {}, nonce {}\n",
        hex8(&receipt.turn_hash),
        balance,
        nonce
    );

    // ── 2) Two REAL STARKs: the FULLER endpoint and the DARKENED endpoint ───────
    // The owner's lineage proves the fuller state transition; the per-viewer darkened
    // slice proves a genuinely SMALLER transition. Two distinct executions ⇒ two distinct
    // genuine PI-35 endpoint commitments. (Both are real Ir2BatchProofs, minted + self-
    // verified on the executor's live balance/nonce.)
    println!("(2) mint TWO real STARKs over the executor's genuine state (this is the prove half):");
    let full_amount = 70u64; // the fuller view's larger state change
    let dark_amount = 7u64; // the darkened view's smaller state change
    println!("    minting the FULLER-view leg   (debit {full_amount}) …");
    let full_leg = mint_leg(balance, nonce, full_amount);
    println!("    minting the DARKENED-view leg (debit {dark_amount}) …");
    let dark_leg = mint_leg(balance, nonce, dark_amount);

    let c_full = full_leg.new_root();
    let c_dark = dark_leg.new_root();
    println!("    FULLER   endpoint commitment Cfull = {}…  (PI {PI_NEW_COMMIT})", felt8(&c_full));
    println!("    DARKENED endpoint commitment Cdark = {}…  (PI {PI_NEW_COMMIT})", felt8(&c_dark));
    println!(
        "    (both share the OLD-state commit at PI {PI_OLD_COMMIT} = {}… — same before-state,\n     \
         genuinely DIFFERENT after-states ⇒ Cfull ≠ Cdark)",
        felt8(&full_leg.old_root())
    );
    assert_ne!(
        c_full, c_dark,
        "a fuller and a darkened transition MUST commit to different post-states"
    );
    println!();

    // ── 3) The frustum-snapshot: capture the surface behind a membrane ──────────
    // The owner publishes a STARK-gated snapshot. The FULL snapshot's lineage is `None`
    // (the whole surface); we will hand a weaker viewer a DARKENED snapshot whose lineage
    // is `Signature` (only the `view` slice) and whose proof is the darkened leg.
    println!("(3) capture frustum-snapshots behind the membrane (the screenshot of the graph):");
    let full_snap = StarkSnapshot::new(gallery.cell(), AuthRequired::None, full_leg.clone());
    let dark_snap = StarkSnapshot::new(gallery.cell(), AuthRequired::Signature, dark_leg.clone());
    println!("    owner's FULL snapshot:     lineage=None,      proof attests Cfull");
    println!("    viewer's DARKENED snapshot: lineage=Signature, proof attests Cdark\n");

    // ── 4) Rehydrate by VERIFYING the STARK, per-viewer (the verify half) ───────
    println!("(4) rehydrate by VERIFYING the STARK — light-client style, per-viewer:");
    let owner = Membrane::new(AuthRequired::None);
    let viewer = Membrane::new(AuthRequired::Signature);

    // The owner re-expands the full surface from the full snapshot (STARK verifies first).
    let owner_view = full_snap
        .rehydrate_for(&owner, gallery.surface())
        .expect("the owner's STARK verifies and the full surface re-expands");
    // The weaker viewer re-expands ONLY the darkened slice from the darkened snapshot.
    let viewer_view = dark_snap
        .rehydrate_for(&viewer, gallery.surface())
        .expect("the viewer's STARK verifies and the darkened slice re-expands");
    println!("    owner  (root)      STARK: OK → reacquires {:?}", owner_view.visible_names());
    println!("    viewer (Signature) STARK: OK → reacquires {:?}  (the culled slice)", viewer_view.visible_names());
    println!("    liveness-type: {} \n", viewer_view.liveness.badge());
    assert_ne!(
        owner_view.visible_names(),
        viewer_view.visible_names(),
        "the cull must darken the weaker viewer's surface"
    );

    // ── 5) THE NON-AMPLIFICATION OBLIGATION, CONCRETE: the weaker viewer ────────
    //       provably CANNOT prove the fuller view. Two independent walls.
    println!("(5) the proof obligation made concrete — the weaker viewer CANNOT forge the fuller view:");

    // (W1) The STARK wall. The viewer holds ONLY the darkened proof (`dark_leg`). To
    //      "prove the fuller view" they would have to present a STARK whose PI 35 = Cfull.
    //      The only artifact they hold is the darkened proof; splicing Cfull into its PI
    //      vector and re-verifying is UNSAT — the descriptor's hash sites force PI 35 to
    //      be the genuine post-state the proof witnessed, which is Cdark, not Cfull.
    let mut forged_pis = dark_leg.public_inputs.clone();
    forged_pis[PI_NEW_COMMIT] = c_full; // claim the darkened proof attests the FULLER endpoint
    match verify_stark_proof_against(&dark_leg.descriptor, &dark_leg.proof, &forged_pis) {
        Err(_) => println!(
            "    (W1) STARK wall:   the darkened proof CANNOT attest Cfull — UNSAT (forgery rejected)."
        ),
        Ok(()) => panic!("FORGERY: the darkened proof must NOT verify against the fuller endpoint Cfull"),
    }
    // The darkened proof of course still verifies against its OWN (darkened) endpoint —
    // the refusal above was the lie, not collateral damage.
    verify_stark_leg(&dark_leg).expect("the darkened proof still verifies against its own Cdark");

    // (W2) The membrane wall. Independently of the proof, the weaker holder's authority
    //      (Signature) cannot even PROJECT the fuller lineage. We model the fuller view as
    //      a `Proof`-gated lineage (incomparable to Signature): the membrane mints NO
    //      projection — there is no view to forge a proof *for*, capability-wise.
    let fuller_snap = StarkSnapshot::new(gallery.cell(), AuthRequired::Proof, full_leg.clone());
    match fuller_snap.rehydrate_for(&viewer, gallery.surface()) {
        Err(StarkRehydrateError::Membrane(RehydrateError::Amplification { .. })) => println!(
            "    (W2) membrane wall: the Signature viewer cannot PROJECT the fuller (Proof) lineage — \
             no projection minted."
        ),
        other => panic!("the membrane must refuse to project the fuller lineage to a weaker viewer; got {other:?}"),
    }

    println!(
        "\n  both walls stand: the cull is non-amplifying IN THE PROOF SYSTEM, not just in the\n  \
         affordance set. A darkened screenshot of the semantic graph cannot be re-expanded\n  \
         into the fuller graph — you provably cannot even prove the stronger view.\n"
    );

    // ── 6) Anti-ghost sanity: a tampered darkened endpoint also fails closed ────
    println!("(6) anti-ghost sanity (the STARK fails closed on the viewer's OWN endpoint too):");
    let mut tampered = dark_snap.clone();
    let honest = tampered.endpoint_commitment();
    tampered.proof.public_inputs[PI_NEW_COMMIT] = honest + BabyBear::ONE;
    match tampered.rehydrate_for(&viewer, gallery.surface()) {
        Err(StarkRehydrateError::StarkInvalid(_)) => {
            println!("    tampered darkened endpoint (PI {PI_NEW_COMMIT} flipped): REJECTED — no projection minted.")
        }
        other => panic!("a tampered darkened endpoint must be rejected; got {other:?}"),
    }

    // ── close ───────────────────────────────────────────────────────────────────
    println!(
        "\n  PASS — two real STARKs minted + verified; the darkened cull provably cannot prove the\n  \
         fuller view (STARK wall + membrane wall); fail-closed on tamper. The frustum-snapshot is a\n  \
         verifiable interactive slice of the semantic graph, non-amplifying by a real proof."
    );
    println!(
        "  (the multi-turn ROOT — a WholeChainProof verified by verify_turn_chain_recursive — is the\n  \
         same weld one proof up; see stark_rehydrate::stark_chain_snapshot.)"
    );
    // The binary exits 0 here: every prove→verify succeeded and every must-reject was
    // refused. A failed prove, a failed verify, or a *successful* forgery would have
    // panicked above (non-zero exit) — so exit 0 IS the prove→verify+non-amplification
    // attestation a CI gate can read.
}

fn hex8(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(16);
    for b in bytes.iter().take(8) {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn felt8(f: &BabyBear) -> String {
    format!("{:08x}", f.0)
}
