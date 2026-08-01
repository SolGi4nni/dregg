//! TRUSTLINE STEP ORACLE probe + PROVENANCE canary (the ANTI-REPLAY class).
//!
//! Proves the `@[export] dregg_trustline_step` symbol (over the PROVEN
//! `Dregg2.Apps.TrustlineCore`, which `Dregg2.Apps.Trustline`'s 101 kernel-clean theorems are
//! stated about) is LINKED into the archive this build actually links, and that the draw /
//! repay / settle verdicts are COMPUTED BY THE LEAN SOURCE.
//!
//! Run:  cargo test -p dregg-lean-ffi --features lean-lib --test trustline_step_oracle_probe -- --nocapture
//!   or: DREGG_REQUIRE_LEAN=1 cargo test -p dregg-lean-ffi --features lean-lib --test trustline_step_oracle_probe
//!
//! ── WHY THIS EXISTS ──────────────────────────────────────────────────────────────────────────
//! The spend authority this export decides is re-implemented ~16 times in Rust
//! (`coord/src/budget.rs`, `turn/src/budget_gate.rs`, `node/src/trustline_service.rs` — whose own
//! header calls the Lean a "twin" — `narrator/src/ledger.rs`, `cell/src/allowance.rs`,
//! `dregg-agent/src/{budget,meter}.rs`, …). The 2026-07-23 twin-deletion sweep hunted twins of
//! Lean **AIR** and closed them; it never asked the question of `Dregg2/Apps/`, so the whole
//! economic layer was structurally invisible to it. NOTHING is routed through this export yet —
//! this probe exists so the rooting cannot regress in the window BEFORE routing lands, which is
//! precisely the window in which a rooting disappears with nobody watching.
//!
//! ── THE PROVENANCE CANARY (this is the part that makes a pass mean something) ────────────────
//! `budget_gate_rs_try_debit` below is the LIVE `turn/src/budget_gate.rs::BudgetSlice::try_debit`
//! algorithm transcribed verbatim: it checks the ceiling, adds to `spent`, and PUSHES the digest
//! onto `debits` — a field it writes and NEVER READS. There is no `debit_set`, no
//! `DuplicateDebit`, no freshness check anywhere in that file; the anti-replay leg lives only in
//! `coord/src/budget.rs::try_debit_fresh`, and `turn` is the crate that gates real turn execution.
//!
//! So on a REPLAYED digest with ample remaining line the two objects DISAGREE: the transcribed
//! Rust ADMITS (it cannot see the replay), the oracle REFUSES
//! (`Dregg2.Apps.Trustline.draw_replay_refused`). `replayed_digest_splits_the_oracle_from_the_
//! budget_gate_twin` asserts BOTH halves on the same input, so a pass is evidence about
//! PROVENANCE and not merely liveness — no configuration of the Rust gate can produce the answer
//! this test observes.
//!
//! ── THE REALITY-GATE CANARY ──────────────────────────────────────────────────────────────────
//! To prove the answer goes THROUGH the Lean source: edit
//! `metatheory/Dregg2/Apps/TrustlineCore.lean` and delete `draw`'s freshness guard (the
//! `if digest ∈ t.draws then none` arm), rebuild — and
//! `replayed_digest_splits_the_oracle_from_the_budget_gate_twin` FLIPS RED, because the oracle now
//! agrees with the transcribed twin. Revert and it greens. A behaviour change in the linked
//! archive caused only by a Lean-source edit is the proof the oracle is the source, not a
//! parallel copy.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::{trustline_step, trustline_step_available, TrustlineChannel, TrustlineOp};

/// The probe gate. `demand_lean` PANICS when the capability is absent (default-on
/// `DREGG_TEST_REQUIRE_LEAN`), so an unlinked archive cannot report a hollow `ok`.
fn lean_answers() -> bool {
    dregg_lean_ffi::demand_lean(
        trustline_step_available(),
        "dregg_trustline_step (the trustline draw/repay/settle oracle)",
    )
}

fn digest(n: u8) -> [u8; 32] {
    let mut d = [0u8; 32];
    // Fill the HIGH bytes too: a digest is an arbitrary-precision `Nat` on the Lean side, and a
    // caller that folded it to 64 bits would collide distinct debits onto one burned digest. A
    // value that does not fit in a u64 keeps this test honest about that.
    d[0] = 0xC0;
    d[1] = 0xFF;
    d[31] = n;
    d
}

fn fresh_line(ceiling: u64) -> TrustlineChannel {
    TrustlineChannel {
        ceiling,
        drawn: 0,
        settled: 0,
        holder_acct: 0,
        issuer_well: 0,
        draws: Vec::new(),
    }
}

// ── THE DELETED-CHECK TRANSCRIPTION ──────────────────────────────────────────────────────────
// `turn/src/budget_gate.rs::BudgetSlice::try_debit`, verbatim in behaviour: ceiling check, add to
// spent, RECORD the digest — and never consult the record. Reproduced here so the disagreement
// below is a statement about two named objects, not a hypothetical.
struct BudgetGateSlice {
    ceiling: u64,
    spent: u64,
    debits: Vec<[u8; 32]>,
}

impl BudgetGateSlice {
    fn try_debit(&mut self, amount: u64, digest: [u8; 32]) -> Result<(), u64> {
        let remaining = self.ceiling - self.spent;
        if amount > remaining {
            return Err(remaining);
        }
        self.spent += amount;
        self.debits.push(digest); // written, never read — there is no freshness check in that file
        Ok(())
    }
}

/// ⚑ THE PROVENANCE CANARY. Same input, two objects, opposite answers.
#[test]
fn replayed_digest_splits_the_oracle_from_the_budget_gate_twin() {
    if !lean_answers() {
        return;
    }
    let d = digest(7);

    // The oracle: draw 30 of 100, then REPLAY the same digest for 1 with 70 still available.
    let line = fresh_line(100);
    let after = trustline_step(
        &line,
        TrustlineOp::Draw {
            digest: d,
            amount: 30,
        },
    )
    .expect("first draw reached a verdict")
    .expect("a within-line draw on a fresh digest COMMITS");
    assert_eq!(after.drawn, 30);
    assert_eq!(after.draws.len(), 1, "the digest was burned");

    let replay = trustline_step(
        &after,
        TrustlineOp::Draw {
            digest: d,
            amount: 1,
        },
    )
    .expect("the replay reached a verdict");
    assert!(
        replay.is_none(),
        "the oracle must REFUSE a replayed digest (Trustline.draw_replay_refused); got {replay:?}"
    );

    // The transcribed `turn/src/budget_gate.rs` gate, on the SAME sequence: it ADMITS the replay.
    let mut slice = BudgetGateSlice {
        ceiling: 100,
        spent: 0,
        debits: Vec::new(),
    };
    slice.try_debit(30, d).expect("first debit fits");
    assert!(
        slice.try_debit(1, d).is_ok(),
        "the transcription must ADMIT the replay — if this fails the transcription has drifted \
         from turn/src/budget_gate.rs and the canary below proves nothing"
    );

    // The two objects disagree on this exact input. That disagreement IS the provenance evidence.
}

#[test]
fn over_line_and_boundary_draws() {
    if !lean_answers() {
        return;
    }
    let line = fresh_line(100);
    assert!(
        trustline_step(
            &line,
            TrustlineOp::Draw {
                digest: digest(1),
                amount: 101
            }
        )
        .expect("reached a verdict")
        .is_none(),
        "over-line draw must REFUSE (Trustline.over_line_draw_refused)"
    );
    assert!(
        trustline_step(
            &line,
            TrustlineOp::Draw {
                digest: digest(2),
                amount: 100
            }
        )
        .expect("reached a verdict")
        .is_some(),
        "the BOUNDARY draw must COMMIT — the bound is tight, not conservative"
    );
}

#[test]
fn repay_restores_the_line_but_never_the_digest() {
    if !lean_answers() {
        return;
    }
    let d = digest(9);
    let drawn = trustline_step(
        &fresh_line(100),
        TrustlineOp::Draw {
            digest: d,
            amount: 40,
        },
    )
    .expect("verdict")
    .expect("commits");
    assert_eq!(drawn.holder_acct, 40);
    assert_eq!(
        drawn.issuer_well, -40,
        "the draw is PRODUCTION at the issuer's well, not a mint"
    );

    assert!(
        trustline_step(&drawn, TrustlineOp::Repay { amount: 41 })
            .expect("verdict")
            .is_none(),
        "over-repay must REFUSE (Trustline.over_repay_refused) — it would MINT at the issuer's well"
    );

    let repaid = trustline_step(&drawn, TrustlineOp::Repay { amount: 40 })
        .expect("verdict")
        .expect("commits");
    assert_eq!(repaid.drawn, 0, "the line is restored");
    assert_eq!(
        repaid.holder_acct + repaid.issuer_well,
        0,
        "bilateral_conserved"
    );
    assert_eq!(
        repaid.draws.len(),
        1,
        "the spent digest STAYS burned across settlement"
    );

    assert!(
        trustline_step(
            &repaid,
            TrustlineOp::Draw {
                digest: d,
                amount: 10
            }
        )
        .expect("verdict")
        .is_none(),
        "repayment must not resurrect a spent digest (Trustline.repay_draws_fixed)"
    );
}

/// ⚑ THE SETTLED FLOOR — the tooth this export exists to carry, and the reason the wire
/// dispatches the settled verbs rather than the two-register ones.
///
/// The deployed gate is `amt <= drawn - settled` (`node/src/trustline_service.rs:1155-1161`),
/// STRICTLY TIGHTER than `amt <= drawn`. If this test ever passes with plain-repay semantics,
/// the export has silently become a WEAKER gate than the node it replaces and every routed
/// repay would widen a money check.
#[test]
fn settled_credit_cannot_be_repaid_back() {
    if !lean_answers() {
        return;
    }
    let drawn = trustline_step(
        &fresh_line(100),
        TrustlineOp::Draw {
            digest: digest(4),
            amount: 30,
        },
    )
    .expect("verdict")
    .expect("commits");
    let settled = trustline_step(&drawn, TrustlineOp::Settle { paid: 20 })
        .expect("verdict")
        .expect("settling within the outstanding draw commits");

    // settleS marches the redemption register and leaves drawn and the registry in place.
    assert_eq!(settled.settled, 20);
    assert_eq!(settled.drawn, 30, "the deployed settle does NOT zero drawn");
    assert_eq!(settled.outstanding(), 10);
    assert_eq!(
        settled.draws.len(),
        1,
        "a settle epoch does not touch the registry"
    );

    // The boundary repay admits...
    assert!(trustline_step(&settled, TrustlineOp::Repay { amount: 10 })
        .expect("verdict")
        .is_some());
    // ...and ONE ABOVE IT REFUSES, even though 11 <= drawn (30). This is the whole point.
    assert!(
        trustline_step(&settled, TrustlineOp::Repay { amount: 11 })
            .expect("verdict")
            .is_none(),
        "11 <= drawn(30) but > outstanding(10): the SETTLED FLOOR must refuse it. A pass here \
         under a two-register model would mean the export widened the deployed check."
    );
    // Over-settle is gated the same way.
    assert!(
        trustline_step(&settled, TrustlineOp::Settle { paid: 11 })
            .expect("verdict")
            .is_none(),
        "settling beyond the outstanding draw would redeem value never drawn"
    );
    // A digest burned before the settle epoch is still burned after it.
    assert!(
        trustline_step(
            &settled,
            TrustlineOp::Draw {
                digest: digest(4),
                amount: 1
            }
        )
        .expect("verdict")
        .is_none(),
        "the forever-carrier law: a settle epoch never resurrects a burned digest"
    );
}

/// A digest whose value exceeds `u64::MAX` must round-trip intact. If the marshalling ever folds a
/// digest to 64 bits, two distinct debits collide onto one burned entry and the anti-replay leg
/// this whole export exists for is silently defeated.
#[test]
fn wide_digests_round_trip_without_truncation() {
    if !lean_answers() {
        return;
    }
    let a = digest(1);
    let mut b = a;
    b[15] ^= 0xFF; // differs only in a byte far above the low 64 bits

    let after_a = trustline_step(
        &fresh_line(100),
        TrustlineOp::Draw {
            digest: a,
            amount: 10,
        },
    )
    .expect("verdict")
    .expect("commits");
    let after_b = trustline_step(
        &after_a,
        TrustlineOp::Draw {
            digest: b,
            amount: 10,
        },
    )
    .expect("verdict")
    .expect("a DISTINCT digest must still draw");

    assert_eq!(
        after_b.draws.len(),
        2,
        "two distinct digests, two burned entries"
    );
    assert_eq!(after_b.drawn, 20);
}
