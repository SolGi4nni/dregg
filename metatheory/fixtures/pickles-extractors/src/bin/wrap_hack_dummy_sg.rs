//! ⚑⚑ **THE WRAP RECORD'S PADDED SLOT, EXPORTED AS ITS PREIMAGE AND NOT ONLY AS ITS DIGEST.**
//!
//! `wrap.rs:476-491`, read at source:
//!
//! ```ignore
//! fn pad_messages_for_next_wrap_proof(mut msgs: Vec<MessagesForNextWrapProof>) -> Vec<…> {
//!     while msgs.len() < 2 {
//!         msgs.insert(0, MessagesForNextWrapProof {
//!             challenge_polynomial_commitment: InnerCurve::from(dummy_ipa_step_sg()),
//!             old_bulletproof_challenges: vec![MessagesForNextWrapProof::dummy_padding(); 2],
//!         });
//!     }
//!     msgs
//! }
//! ```
//!
//! and `wrap.rs:2832-2846` hands exactly that list to the wrap circuit as `prev_step_accs` /
//! `old_bp_chals`, which `wrap.rs:2919-2932` hashes with `hash_checked` per slot. So the wrap
//! circuit's slot-0 `hash_messages_for_next_wrap_proof` is not a fixture and not a constant it is
//! told: it is a SPONGE over a preimage upstream fixes, whose squeeze is
//! `messages_for_next_wrap_proof_padding()` (`transaction.rs:3691-3700`).
//!
//! ⚑ **THAT IS WHY THIS BINARY EXPORTS THE PREIMAGE.** A Lean side handed only the digest would
//! TRANSCRIBE the pad — one more literal standing for an object the assembly can derive, which is
//! the defect `KimchiWrapHackDigest` exists to refuse. Handed the preimage AND the digest, the Lean
//! side derives the first into the second and
//! `KimchiWrapMain.the_pad_slot_derives_minas_own_padding_digest` is that agreement as a theorem —
//! our Fq sponge against openmina's `hash_fields`, on openmina's own inputs.
//!
//! Four facts this settles, three of which the Lean side had wrong while `actual_proofs_verified`
//! happened to equal `MAX_PROOFS_VERIFIED_N`:
//!
//!   1. **The padding is a PREPEND.** Slot 0 is the DUMMY and the real accumulators are at the END.
//!      `KimchiStepMainFixture.chainSlot0` already says slot 0 is the `Wrap_hack` dummy; nothing on
//!      the wrap side did.
//!   2. **`Max_proofs_verified` and `actual_proofs_verified` are TWO numbers.** `wrap.rs:666` sets
//!      `actual_proofs_verified = <the record>.old_bulletproof_challenges.len()` — 1 for dregg's
//!      one-`verify_one` step rule — while this padding runs to `MAX_PROOFS_VERIFIED_N` = 2.
//!      `KimchiWrapMainCore.shapeWrap.prevs` served BOTH until 2026-08-07, when the field was
//!      renamed `maxPrevs` and fixed at `Max_proofs_verified`; `actual` lives on `WH_REAL_SLOTS`
//!      and on `BranchData.fz`.
//!   3. ⚑ **THE PAD'S COMMITMENT IS `Dummy.Ipa.STEP.sg`, NOT `Dummy.Ipa.WRAP.sg`**, and this file
//!      said the wrong one until 2026-08-07. They pad two DIFFERENT records: `dummy_ipa_wrap_sg()`
//!      pads `messages_for_next_step_proof.challenge_polynomial_commitments` at `wrap.rs:736` (the
//!      accumulator list), `dummy_ipa_step_sg()` pads `messages_for_next_wrap_proof` at
//!      `wrap.rs:484` (the record packed statement words 55/56 carry). Both are exported so the
//!      distinction is legible rather than remembered.
//!   4. **The pad's challenge vectors are `Dummy.Ipa.Wrap.challenges_computed`**, which openmina
//!      carries as fifteen literals (`messages.rs:114-134`). ⚠ `KimchiWrapHackDigest.WH_MLMB`'s
//!      docblock declared these "an OCaml random-oracle draw this tree has no independent source
//!      for" and used that to justify emitting only the `mlmb = 2` case. There IS a source; it is
//!      this export.
//!
//! ⚠ Until this export existed, `KimchiWrapHackDigest.whSgOld` read
//! `STEP_PREVCOMM_XY.getD (2*p) (wrapFixtureQ 1 (2*p))` — so a `STEP_PREVCOMM_XY` that carried
//! fewer points than the record has slots did not REFUSE, it silently hashed a `wrapFixtureQ`
//! filler into packed statement words 55/56. That fallback is the defect this binary retires.
//!
//! RUN: `cargo run --release --bin wrap_hack_dummy_sg [out_dir]`

use ark_ec::AffineRepr;
use ledger::proofs::public_input::messages::{dummy_ipa_step_sg, MessagesForNextWrapProof};
use ledger::proofs::transaction::messages_for_next_wrap_proof_padding;
use ledger::proofs::wrap::dummy_ipa_wrap_sg;

fn main() {
    let out_dir = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/tmp/pickles-kimchi-marshal".to_string());
    std::fs::create_dir_all(&out_dir).expect("out dir");

    let p = dummy_ipa_wrap_sg();
    let (wx, wy) = p
        .xy()
        .expect("Dummy.Ipa.Wrap.sg is not the point at infinity");
    println!("[dummy] Dummy.Ipa.Wrap.sg = ({wx}, {wy})");

    // ⚑ …and the OTHER dummy point, which is the one packed statement words 55/56 actually need.
    let (sx, sy) = dummy_ipa_step_sg();
    println!("[dummy] Dummy.Ipa.Step.sg = ({sx}, {sy})");

    // ⚑ `Dummy.Ipa.Wrap.challenges_computed` — ONE vector of fifteen; the pad carries TWO of them.
    let chals = MessagesForNextWrapProof::dummy_padding();
    assert_eq!(chals.len(), 15, "Tock.Rounds.n");
    println!(
        "[dummy] Dummy.Ipa.Wrap.challenges_computed[0] = {}",
        chals[0]
    );

    // ⚑⚑ …and the digest the preimage above must produce.
    // `step.rs:2764-2772`:
    //     let n_padding = 2 - expanded_proofs.len();
    //     if i < n_padding { messages_for_next_wrap_proof_padding() }
    //     else { messages_for_next_wrap_proof[i - n_padding] }
    // So the record is `[Fp; 2]` of DIGESTS, the pad goes at the FRONT, and a rule with one
    // `verify_one` publishes `[pad, real]` — not two real previous-proof digests.
    let pad = messages_for_next_wrap_proof_padding();
    println!("[dummy] messages_for_next_wrap_proof_padding() = {pad}");

    let chal_list = {
        let mut s = String::new();
        for (i, c) in chals.iter().enumerate() {
            s.push_str(if i == 0 { "  [ " } else { "  , " });
            s.push_str(&c.to_string());
            s.push('\n');
        }
        s.push_str("  ]");
        s
    };

    // ⚑⚑ **AND THE PRECHALLENGE FORM, WHICH IS WHAT A PACKED STATEMENT WORD HOLDS.**
    // `DUMMY_PAD_CHALS` above is `Dummy.Ipa.Wrap.challenges_computed` — already endo-expanded, and
    // the expansion is one-way, so it cannot be put in a statement word. `dummy_ipa_wrap_challenges()`
    // (`unfinalized.rs:286-290`, `std::array::from_fn(|i| ro::chal(15 - i).inner)`) is
    // `Dummy.Ipa.Wrap.challenges` — the fifteen 128-bit draws themselves, which IS the shape
    // `spec.ml:374-392` packs and the shape `bin/pickles_kimchi_marshal`'s
    // `step_statement_prechallenges` reads back out of the emitted step statement.
    let pre = ledger::proofs::unfinalized::dummy_ipa_wrap_challenges();
    let expanded_matches = {
        use ledger::proofs::public_input::scalar_challenge::ScalarChallenge;
        use ledger::proofs::transaction::endos;
        let (_, endo) = endos::<mina_curves::pasta::Fp>();
        pre.iter()
            .map(|c| ScalarChallenge::from(*c).to_field(&endo))
            .collect::<Vec<_>>()
            == chals.to_vec()
    };
    println!(
        "[dummy] Dummy.Ipa.Wrap.challenges (prechallenge form) endo-expands to \
         challenges_computed : {expanded_matches}"
    );
    assert!(
        expanded_matches,
        "Dummy.Ipa.Wrap.challenges must be the preimage of Dummy.Ipa.Wrap.challenges_computed — \
         if they are two unrelated constants, a statement word carrying the former does not \
         reconstruct the latter and the pad slot cannot close"
    );
    let pre_list = {
        let mut s = String::new();
        for (i, c) in pre.iter().enumerate() {
            let v = (u128::from(c[1]) << 64) | u128::from(c[0]);
            s.push_str(if i == 0 { "  [ " } else { "  , " });
            s.push_str(&v.to_string());
            s.push('\n');
        }
        s.push_str("  ]");
        s
    };

    let body = format!(
        "/-\n\
         # MinaWrapHackDummySg — ⚑ THE WRAP RECORD'S PADDED SLOT, PREIMAGE AND DIGEST.\n\n\
         ⚑ GENERATED by `pickles-extractors/src/bin/wrap_hack_dummy_sg.rs` out of openmina's own\n\
         `dummy_ipa_wrap_sg()`, `dummy_ipa_step_sg()`, `MessagesForNextWrapProof::dummy_padding()`\n\
         and `messages_for_next_wrap_proof_padding()`. Do not hand-edit.\n\n\
         ⚠ **TWO RECORDS, TWO DUMMY POINTS, AND THEY ARE NOT INTERCHANGEABLE.**\n\
         `wrap.rs:729-737` pads `messages_for_next_step_proof.challenge_polynomial_commitments` — the\n\
         ACCUMULATOR list — by inserting `Dummy.Ipa.Wrap.sg` at index 0. `wrap.rs:476-491` pads\n\
         `messages_for_next_wrap_proof` — the record packed statement words 55/56 carry — by\n\
         inserting a whole `MessagesForNextWrapProof` whose commitment is `Dummy.Ipa.STEP.sg` and\n\
         whose challenge vectors are two copies of `Dummy.Ipa.Wrap.challenges_computed`. Both pads\n\
         are PREPENDS, so on a rule whose `actual_proofs_verified` is 1 both lists are\n\
         `[dummy, real]` and NOT `[real, dummy]`.\n\n\
         ⚑ **THE PAD SLOT IS A DERIVATION, NOT A CONSTANT THIS TREE IS TOLD.** `wrap.rs:2919-2932`\n\
         hashes every slot of the PADDED record in circuit, so the wrap circuit computes the pad's\n\
         digest out of the preimage below. `NEXT_WRAP_PROOF_PADDING` is here as the ORACLE that\n\
         derivation is checked against — `KimchiWrapMain.the_pad_slot_derives_minas_own_padding\n\
         _digest` — and not as the value the assembly emits.\n\n\
         ⚠ WHAT THIS RETIRED: `KimchiWrapHackDigest.whSgOld`'s `getD … (wrapFixtureQ 1 …)`\n\
         fallback, which turned a too-short `STEP_PREVCOMM_XY` into a hashed filler instead of a\n\
         refusal.\n\
         -/\n\
         namespace Dregg2.Circuit.Emit.MinaWrapHackDummySg\n\n\
         /-- `Dummy.Ipa.Wrap.sg`'s affine `x` — the ACCUMULATOR list's pad (`wrap.rs:736`). ⚠ NOT\n\
         the wrap record's; see `DUMMY_STEP_SG`. -/\n\
         def DUMMY_WRAP_SG_X : Nat := {wx}\n\n\
         /-- …and its `y`. -/\n\
         def DUMMY_WRAP_SG_Y : Nat := {wy}\n\n\
         /-- …as a point. -/\n\
         def DUMMY_WRAP_SG : Nat × Nat := (DUMMY_WRAP_SG_X, DUMMY_WRAP_SG_Y)\n\n\
         /-- ⚑ `Dummy.Ipa.Step.sg`'s affine `x` — the WRAP RECORD's pad commitment\n\
         (`wrap.rs:484`), i.e. `prev_step_accs.(0)` on a one-`verify_one` rule. -/\n\
         def DUMMY_STEP_SG_X : Nat := {sx}\n\n\
         /-- …and its `y`. -/\n\
         def DUMMY_STEP_SG_Y : Nat := {sy}\n\n\
         /-- …as a point. -/\n\
         def DUMMY_STEP_SG : Nat × Nat := (DUMMY_STEP_SG_X, DUMMY_STEP_SG_Y)\n\n\
         /-- ⚑ **`Dummy.Ipa.Wrap.challenges_computed`** (`wrap_hack.ml:37`,\n\
         `messages.rs:114-134`) — ONE `Tock.Rounds.n = 15` vector. The pad carries TWO copies.\n\n\
         ⚠ These are `Ipa.Wrap.compute_challenge` of `Ro.scalar_chal ()`, i.e. an OCaml\n\
         random-oracle draw. `KimchiWrapHackDigest.WH_MLMB` used to call that \"a value this tree\n\
         has no independent source for\" and declined to emit the `mlmb < 2` opening state because\n\
         of it. openmina carries them as literals; this is that source. -/\n\
         def DUMMY_PAD_CHALS : List Nat :=\n{chal_list}\n\n\
         /-- ⚑⚑⚑ **`Dummy.Ipa.Wrap.challenges` — THE PRECHALLENGE FORM, AND THE ONE A PACKED\n\
         STATEMENT WORD CAN HOLD.** `unfinalized.rs:286-290`, `from_fn(|i| ro::chal(15 - i).inner)`.\n\n\
         `DUMMY_PAD_CHALS` above is the endo-EXPANDED vector and the expansion is one-way, so a\n\
         statement word cannot carry it; these fifteen 128-bit draws are its preimage — asserted in\n\
         the generator, not assumed — and they are what the padding block's fifteen\n\
         `bpChallenge` words must be.\n\n\
         ⚠ **THIS IS WHAT `KimchiStepMainCore.stmtDummyVal` DOES NOT YET EMIT.** It fills every\n\
         128-bit padding slot with `(7 + 1000003·j) % 2^127` — 24-25 bits — so the wrap proof's\n\
         PAD recursion slot commits a challenge polynomial that is not Mina's, while\n\
         `prover.rs:130-140` front-pads the reader's list with `DUMMY_WRAP_SG`. `gate_a2` reports\n\
         that slot RED, and `marshal::ACCUMULATOR_PRECHALLENGE_MIN_BITS` refuses the same shape\n\
         wherever it reaches a slot the record PUBLISHES.\n\
         -/\n\
         def DUMMY_WRAP_PRECHALS : List Nat :=\n{pre_list}\n\n\
         /-- ⚑⚑ **`messages_for_next_wrap_proof_padding()`** (`transaction.rs:3691-3700`) — the\n\
         `hash()` of the padded record's slot-0 entry, i.e. the squeeze over\n\
         `DUMMY_PAD_CHALS ++ DUMMY_PAD_CHALS ++ [DUMMY_STEP_SG_X, DUMMY_STEP_SG_Y]`.\n\n\
         ⚠ **THIS IS AN ORACLE, NOT AN INPUT.** The assembly DERIVES this value; the theorem\n\
         `KimchiWrapMain.the_pad_slot_derives_minas_own_padding_digest` is the two agreeing. A use\n\
         site that emitted this literal instead of the sponge would be transcribing an object it\n\
         can compute, which is what `KimchiWrapHackDigest`'s whole docblock refuses. -/\n\
         def NEXT_WRAP_PROOF_PADDING : Nat := {pad}\n\n\
         end Dregg2.Circuit.Emit.MinaWrapHackDummySg\n"
    );
    let path = format!("{out_dir}/MinaWrapHackDummySg.lean");
    std::fs::write(&path, body).expect("write the dummy-sg module");
    println!("[dummy] wrote {path}");
}
