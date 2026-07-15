//! # `cap_delegation_nonamp_descriptor` — the GENUINE-NON-AMP cap-graph descriptor loader.
//!
//! The ARGUS linchpin on the DELEGATION family (`delegate`, `delegateAtten`, `attenuate`, `introduce`,
//! `revoke`, `refresh`). One Lean-verified `EffectVmDescriptor` that, on a cap-graph row, enforces BOTH:
//!
//!   * **genuine cap-root recompute** — `new_cap_root = hash[edge_leaf, old_cap_root]` with
//!     `edge_leaf = hash[holder, target, rights, op]` (the §G prepend-accumulator advance, op-tagged), so
//!     the post `cap_root` is a FORCED function of the bound cap-edge mutation, not an opaque digest
//!     parameter — and the recomputed root is absorbed into `state_commit` (tamper ⇒ UNSAT);
//!   * **per-bit non-amplification** — the submask gates force `granted_bit ≤ held_bit` on each of the
//!     8 delegation bit carriers (`dcol.grantedBit i` = col 128+i, `dcol.heldBit i` = col 120+i). An
//!     over-grant (a granted bit set where the held bit is clear) fails the submask gate. Both legs are
//!     emitted from the proved Lean module and both are witnessed behaviourally by the tests below.
//!
//! ## ⚠ THE TWO LEGS DO NOT INTERLOCK — the emitted gates bind the WRONG columns (2026-07-15)
//!
//! This module's header USED to claim: "the per-bit submask gates … over the **SAME `rights` felt** the
//! recompute hashes into the edge leaf", and "the two legs INTERLOCK on one `rights` felt: tamper it to
//! dodge the submask gate and the recomputed `cap_root` moves ⇒ UNSAT". **That is false as emitted**, and
//! the committed JSON is the witness — read the two mask-reconstruction gates:
//!
//! ```text
//! gate 54:  v7 − Σ_{i<8} v(120+i)·2ⁱ     (held mask recon)
//! gate 55:  v4 − Σ_{i<8} v(128+i)·2ⁱ     (granted mask recon)
//! ```
//!
//! The granted bits reconstruct **column 4**, and the held bits **column 7**. The `rights` felt the
//! edge-leaf site hashes is **column 72**. Columns 4 and 7 are EFFECT-SELECTOR columns (the selector
//! block is `0..54`); they are not the rights param and nothing else in the descriptor relates them to it.
//!
//! The cause is a param-index/column conflation in the Lean emit. `EffectVmEmitCapReshape.dcol.GRANTED_MASK
//! := EffectVmEmitCapRoot.cp.RIGHTS`, and `cp.RIGHTS = 4` is a **param INDEX** — the column is
//! `prmCol 4 = PARAM_BASE + 4 = 72`. But `gMaskRecon` consumes a raw COLUMN (`eCol maskCol`), so the
//! emitted gate reads `v4`. `dcol.HELD_MASK := 7` has the same shape (intended param 7 = col 75; emitted
//! `v7`). The mint-flavour `col.HELD_MASK`/`col.SLOT`/`col.TARGET` in the same namespace are built the
//! same way, so `cap_reshape_descriptor` is very likely to carry the identical defect.
//!
//! What survives: `capDeleg_nonAmp_in_circuit` / `capDeleg_rejects_amplify` are PROVED and TRUE — they
//! quantify over `dcol.grantedBit i` / `dcol.heldBit i`, which really are cols 128+i / 120+i, and the
//! submask gate really does force `gᵢ ≤ hᵢ` there. `nonamp_submask_gate_refuses_an_amplifying_witness`
//! witnesses that behaviourally. What does NOT survive is the LINK from those bits to the rights the
//! recomputed `cap_root` commits. The Lean doc-comment on `capDeleg_nonAmp_in_circuit` asserts that link
//! ("Since the granted bits reconstruct `cp.RIGHTS` … this binds the very rights the recomputed
//! `cap_root` commits") and it is not what the emit produces.
//!
//! `nonamp_leg_does_not_bind_the_hashed_rights_felt` PINS this behaviourally, so the defect cannot be
//! silently inherited: it proves an amplifying `rights` felt is ACCEPTED. **That test is designed to go
//! RED when the emit is fixed** — that red is the signal the fix landed, not a regression.
//!
//! A second, independent emit defect on the same descriptor: its state-commit site's `Digest k` indices
//! were never rebased when the two cap-root sites were PREPENDED to the site list. Site 5 (`digest_col`
//! 88 = `state_commit`) reads digests `0,1,2` = cols `102, 87, 98` — the edge leaf, the cap root, and
//! `hash[state_after[0..3]]` — where the GROUP-4 chain intends cols `98, 99, 100`. So `state_after[4..10]`
//! (cols 80..86) are NOT committed by `state_commit`, and sites 3/4 (cols 99/100) are dead carriers.
//! `state_commit_group4_chain_is_misindexed` pins it. All 27 other emitted descriptors index correctly;
//! this one is unique — the prepend shifted the ordinals and the `Digest k` literals stayed.
//!
//! Neither defect is live: nothing routes to this descriptor (see NOT WIRED below). Both must be fixed in
//! the Lean emit — `prmCol`-wrapping the mask columns and rebasing the digest ordinals — then re-emitted
//! (`scripts/emit-descriptors.sh`), re-pinned (`GENUINE_NONAMP_FP`), and drift-gated. That work is Lean-side
//! and out of scope for the test lane that found it; it is in HORIZONLOG.
//!
//! ## Provenance (anti-drift, the LAW#1 way)
//!
//! `dregg-effectvm-attenuateA-v1-genuine-nonamp.json` is the **byte-exact** output of the verified Lean
//! emit `Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNonAmp` (via
//! `emitVmJson`, the `EmitAllJson` registry line). The Rust prover INTERPRETS this descriptor via
//! `parse_vm_descriptor` (it AUTHORS NO CONSTRAINT — the gates are emitted from the proved Lean module:
//! `capDeleg_nonAmp_in_circuit` / `capDeleg_rejects_amplify` are the in-circuit teeth, both polarities).
//! The test below re-parses the JSON into the prover's structure; the Lean↔JSON drift gate is
//! generate-fresh `scripts/check-descriptor-drift.sh` (`GENUINE_NONAMP_FP` is a cache-freshness pin,
//! NOT a faithfulness check). ONE descriptor object backs all six effects (the `op` tag distinguishes the mutation,
//! so the JSON is shared — selector→JSON fan-out, like the v1 cap-graph face).
//!
//! This is a STANDALONE loader (its own module + test), NOT registered in the locked
//! `effect_vm_descriptors` registry (whose count assertions would otherwise break) — exactly as
//! `cap_reshape_descriptor` is standalone.
//!
//! ## ⚠ NOT WIRED — this descriptor is dead code at HEAD (named seam, 2026-07-15)
//!
//! Nothing routes cap-graph rows to this descriptor. `GENUINE_NONAMP_NAME` / `GENUINE_NONAMP_JSON`
//! have **zero consumers** outside this module and its own test; the delegation family proves under
//! the opaque-digest `attenuateA` face instead. So the in-circuit teeth described above are real and
//! Lean-verified, but they do **not** gate any deployed proof: the good descriptor is dead while the
//! weaker one is deployed.
//!
//! Closing this needs a selector→JSON dispatcher that routes the six cap-graph effects here (or a
//! decision to delete both standalone cap loaders). The closure lane is
//! `docs/deos/CRATE-EXCELLENCE-PLAN.md` §4 MOVE 5 ("resolve the cap-descriptor orphans — do not
//! leave the good one dead and the weak one deployed").
//!
//! ⚠ HORIZONLOG's "cap-crown IR non-amp LANDED, 2026-06-15" entry still describes the two legs as
//! INTERLOCKING on one `rights` felt. That claim is false as emitted (see above) and the entry is
//! owed a correction; it is not swept here because that file is mid-flight in another lane.

use crate::lean_descriptor_air::{EffectVmDescriptor, parse_vm_descriptor};

/// The verified-Lean JSON cache for the genuine-non-amp cap-graph descriptor (Lean is the
/// source of truth; regenerated by `scripts/emit-descriptors.sh`).
pub const GENUINE_NONAMP_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-attenuateA-v1-genuine-nonamp.json");

/// SHA-256 cache-freshness pin for the committed bytes (re-pinned by the emit script; NOT a
/// faithfulness check — the Lean↔JSON gate is generate-fresh `scripts/check-descriptor-drift.sh`).
pub const GENUINE_NONAMP_FP: &str =
    "5cdb03f341ed0b0f33af193f15827c536195d929ad94fe3c22a48cfc3c456e58";

/// The descriptor name (the canonical wire identity — shared across the six cap-graph effects).
pub const GENUINE_NONAMP_NAME: &str = "dregg-effectvm-attenuateA-v1-genuine-nonamp";

/// The `Auth` rights-mask bit width (8 atoms ⇒ 8 bits): mirrors Lean `EffectVmEmitCapReshape.MASK_BITS`.
pub const MASK_BITS: usize = 8;

/// The DELEGATION held-mask bit columns. Mirrors Lean `dcol.heldBit i = 120 + i`
/// (`col.GRANTED_BIT_BASE + MASK_BITS = 112 + 8 = 120`), past the mint-flavour bit block.
pub const DELEG_HELD_BIT_BASE: usize = 120;

/// The DELEGATION granted-mask bit columns. Mirrors Lean `dcol.grantedBit i = 128 + i`
/// (`col.GRANTED_BIT_BASE + 2·MASK_BITS = 112 + 16 = 128`).
///
/// ⚠ These reconstruct **column 4**, NOT `cp.RIGHTS`'s column. `dcol.GRANTED_MASK := cp.RIGHTS` is a
/// param INDEX (4) used as a raw column by `gMaskRecon`; the rights felt the edge leaf hashes is
/// `prmCol 4` = [`DELEG_HASHED_RIGHTS_COL`] = 72. See the module header's ⚠ section.
pub const DELEG_GRANTED_BIT_BASE: usize = 128;

/// The column the granted-mask bit recon ACTUALLY binds (Lean `dcol.GRANTED_MASK` = `cp.RIGHTS` = 4,
/// consumed as a raw column). This is an effect-SELECTOR column, not a rights param — the defect the
/// module header names.
pub const DELEG_GRANTED_MASK_RECON_COL: usize = 4;

/// The column the held-mask bit recon ACTUALLY binds (Lean `dcol.HELD_MASK` = 7, consumed as a raw
/// column rather than `prmCol 7` = 75). Also an effect-selector column.
pub const DELEG_HELD_MASK_RECON_COL: usize = 7;

/// The `rights` felt the cap-root edge-leaf site genuinely hashes: `prmCol cp.RIGHTS` = `PARAM_BASE + 4`
/// = 72. The non-amp leg does NOT reach this column — that absence is the module header's ⚠ finding.
pub const DELEG_HASHED_RIGHTS_COL: usize = 72;

/// The full EffectVM base trace width (Lean `EFFECT_VM_WIDTH`).
pub const EFFECT_VM_WIDTH: usize = 188;

/// Parse the genuine-non-amp cap-graph descriptor through the running EffectVM interpreter.
/// (The same `parse_vm_descriptor` the cutover dispatcher uses; the descriptor drives the verified
/// circuit for the delegation-family row.)
pub fn cap_delegation_nonamp_descriptor() -> Result<EffectVmDescriptor, String> {
    parse_vm_descriptor(GENUINE_NONAMP_JSON)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::BabyBear;
    use crate::lean_descriptor_air::{
        HashInput, LeanExpr, VmConstraint, prove_vm_descriptor, vm_site_digest_concrete,
    };

    // ── The EffectVM base layout (Lean `EffectVmEmit`; these ARE the prover's column indices). ──
    /// `STATE_BEFORE_BASE = NUM_EFFECTS = 54`.
    const SB: usize = 54;
    /// `PARAM_BASE = STATE_BEFORE_BASE + STATE_SIZE = 68`.
    const PB: usize = 68;
    /// `STATE_AFTER_BASE = PARAM_BASE + NUM_PARAMS = 76`.
    const SA: usize = 76;
    /// `STATE_SIZE = 14`.
    const STATE_SIZE: usize = 14;
    /// The state slot the cap-root accumulator lives in (`state_before[11]` = col 65,
    /// `state_after[11]` = col 87) — one of the only two slots the frame-freeze gates leave free.
    const CAP_ROOT_SLOT: usize = 11;
    /// The state slot the state-commitment lives in (`state_after[12]` = col 88) — the other free slot.
    const STATE_COMMIT_SLOT: usize = 12;
    /// `aux_off.STATE_RECORD_DIGEST` absolute (`auxCol 96`): the record digest the state-commit absorbs.
    const RECORD_DIGEST_COL: usize = 186;

    fn bb(v: u32) -> BabyBear {
        BabyBear::new(v)
    }

    /// A witness the honest producer would lay down for a delegation row: `held` is the delegator's
    /// mask, `granted` the conferred mask. Rows form a real accumulator CHAIN — each row's
    /// `state_after` is the next row's `state_before`, and the cap-root advances
    /// `cap_root' = hash[edge_leaf, cap_root]` per row, exactly as the §G prepend-accumulator does.
    ///
    /// The trace is built to SATISFY the descriptor, not to mirror it: every digest cell is filled by
    /// [`vm_site_digest_concrete`] — the same resolution + extraction `extend_vm_trace` uses — so the
    /// hash sites are pinned by the AIR's own arithmetic rather than by this test's.
    struct DelegWitness {
        rows: Vec<Vec<BabyBear>>,
        pis: Vec<BabyBear>,
    }

    /// The trace height. Gates are enforced on the transition domain (rows `0..n-2`); hash sites on
    /// EVERY row. 4 rows means 3 gated rows and a real 3-step accumulator chain — not a single row
    /// that could satisfy the transition constraints by being its own successor.
    const N_ROWS: usize = 4;

    fn honest_witness(desc: &EffectVmDescriptor, held: u32, granted: u32) -> DelegWitness {
        assert_eq!(granted & !held, 0, "honest_witness requires granted ⊑ held");

        // The frozen part of the state: every slot except cap_root(11) and state_commit(12), which the
        // frame-freeze gates deliberately leave free (they are what a delegation MUTATES).
        let frozen: Vec<BabyBear> = (0..STATE_SIZE).map(|i| bb(1000 + i as u32)).collect();
        let mut cap_root = bb(777); // the genesis cap-root the chain advances from
        let mut state_commit = bb(0); // row 0's state_before[12]; unconstrained on the first row

        let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(N_ROWS);
        for r in 0..N_ROWS {
            let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];

            // state_before: frozen slots, plus the accumulator's running values.
            for i in 0..STATE_SIZE {
                row[SB + i] = frozen[i];
            }
            row[SB + CAP_ROOT_SLOT] = cap_root;
            row[SB + STATE_COMMIT_SLOT] = state_commit;

            // The cap-edge params (holder, target, rights, op) at cols 70..73. `rights` is the felt the
            // edge leaf hashes; a real producer would put the granted mask here — and the module
            // header's ⚠ section is that NOTHING in this descriptor forces it to.
            row[PB + 2] = bb(0xA11CE + r as u32); // holder
            row[PB + 3] = bb(0xB0B); // target
            row[PB + 4] = bb(granted); // rights  (= DELEG_HASHED_RIGHTS_COL, col 72)
            row[PB + 5] = bb(1); // op = delegate
            row[PB + 7] = bb(held); // param 7 — what dcol.HELD_MASK *intended* (col 75)

            // The mask-recon gates bind cols 4 and 7 (see the module header). Satisfy them where they
            // actually are, or every test here reds on the recon gate instead of the gate under test.
            row[DELEG_GRANTED_MASK_RECON_COL] = bb(granted);
            row[DELEG_HELD_MASK_RECON_COL] = bb(held);

            // The bit carriers the submask gates read.
            for i in 0..MASK_BITS {
                row[DELEG_HELD_BIT_BASE + i] = bb((held >> i) & 1);
                row[DELEG_GRANTED_BIT_BASE + i] = bb((granted >> i) & 1);
            }

            row[RECORD_DIGEST_COL] = bb(0xD16E57 + r as u32);

            // state_after: frame-frozen slots equal state_before (the 12 freeze gates).
            for i in 0..STATE_SIZE {
                row[SA + i] = row[SB + i];
            }

            // Fill the digest cells the AIR pins, in site order (later sites read earlier digests).
            // state_after[11] (col 87) and state_after[12] (col 88) ARE digest cells, so this is what
            // makes the row's post-state a FORCED function of the edge mutation rather than a choice.
            fill_digests(desc, &mut row);

            cap_root = row[SA + CAP_ROOT_SLOT];
            state_commit = row[SA + STATE_COMMIT_SLOT];
            rows.push(row);
        }

        // The 4 PI bindings are all `first`: col 56→pi41, col 54→pi20, col 55→pi21, col 66→pi0.
        let mut pis = vec![BabyBear::ZERO; desc.public_input_count];
        pis[41] = rows[0][56];
        pis[20] = rows[0][54];
        pis[21] = rows[0][55];
        pis[0] = rows[0][66];

        DelegWitness { rows, pis }
    }

    /// Recompute every hash site's digest cell for a row, in site order. Called after any edit to a
    /// column a site reads, so a forgery under test is the ONLY unsatisfied constraint.
    fn fill_digests(desc: &EffectVmDescriptor, row: &mut [BabyBear]) {
        let mut digests: Vec<BabyBear> = Vec::with_capacity(desc.hash_sites.len());
        for site in &desc.hash_sites {
            let d = vm_site_digest_concrete(site, row, &digests);
            row[site.digest_col] = d;
            digests.push(d);
        }
    }

    /// Run the prover and classify the outcome, DISTINGUISHING an unsatisfied constraint from a crash.
    ///
    /// `prove_vm_descriptor`'s documented refusal mechanism for an unsatisfiable witness is the p3
    /// debug constraint checker's PANIC (debug_assertions are on under `cargo test`). Per
    /// CRATE-EXCELLENCE-PLAN S1 a bare "any panic counts" match is the P1b anti-pattern, so this
    /// returns the panic's MESSAGE for the caller to assert on: a stray `unwrap` in trace assembly
    /// produces a different message and must not be mistaken for the tooth firing.
    enum Outcome {
        Accepted,
        /// The prover returned `Err` (the stringly boundary — CRATE-EXCELLENCE-PLAN Move 5 types it).
        Refused(String),
        /// The p3 debug constraint checker panicked: the witness violates a constraint.
        ConstraintPanic(String),
    }

    fn run(desc: &EffectVmDescriptor, w: &DelegWitness) -> Outcome {
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {})); // the forgery panics are expected; keep output readable
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor(desc, &w.rows, &w.pis)
        }));
        std::panic::set_hook(hook);
        match r {
            Ok(Ok(_)) => Outcome::Accepted,
            Ok(Err(e)) => Outcome::Refused(e),
            Err(p) => {
                let msg = p
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_string()))
                    .unwrap_or_else(|| "<non-string panic payload>".to_string());
                Outcome::ConstraintPanic(msg)
            }
        }
    }

    /// Require a refusal that is an UNSATISFIED CONSTRAINT — never a crash, never an arbitrary `Err`.
    /// The p3 debug builder's message names the constraint failure; anything else (an `unwrap`, an
    /// index panic, a shape error) is a BUG in the test or the prover, not the tooth, and reds here.
    fn assert_constraint_refusal(desc: &EffectVmDescriptor, w: &DelegWitness, what: &str) {
        match run(desc, w) {
            Outcome::Accepted => panic!("{what} was ACCEPTED — the gate is OPEN"),
            Outcome::ConstraintPanic(msg) => {
                let m = msg.to_ascii_lowercase();
                assert!(
                    m.contains("constraint") || m.contains("assert") || m.contains("nonzero"),
                    "{what} refused, but NOT via an unsatisfied constraint — the panic was {msg:?}. \
                     A crash is not a refusal: it cannot distinguish `rejected the forgery` from \
                     `the prover fell over`, which is exactly the P1b anti-pattern this test avoids."
                );
            }
            Outcome::Refused(e) => {
                let m = e.to_ascii_lowercase();
                assert!(
                    m.contains("verify") || m.contains("constraint") || m.contains("oodevaluation"),
                    "{what} refused, but with an error that does not look like a constraint/verify \
                     failure: {e:?}. Assert the REASON, not that something went wrong."
                );
            }
        }
    }

    /// **THE BEHAVIOURAL NON-AMP TOOTH — an amplifying witness is REFUSED by the running prover.**
    ///
    /// This is what `genuine_nonamp_carries_anti_amplify_teeth` (below) cannot do. That test
    /// pattern-matches the descriptor AST for a gate-SHAPED subtree; it constructs no witness and asks
    /// no prover to refuse one, so it is green against an interpreter that parses the gate and never
    /// enforces it. Here the forgery is built and the prover is required to refuse it — mirroring
    /// `descriptor_ir2::ir2_amplified_submask_refuses`, but asserting the REASON rather than accepting
    /// any panic (CRATE-EXCELLENCE-PLAN S1 vs the P1b idiom the reference still uses).
    ///
    /// Every bit is forged INDEPENDENTLY (`i in 0..MASK_BITS`). One amplifying bit would leave a
    /// descriptor that gates only bit 0 fully green — the per-bit sweep is what makes all 8 submask
    /// gates load-bearing, the same reason `every_forged_commitment_lane_is_rejected_by_the_fold`
    /// forges each of its 8 lanes separately.
    ///
    /// SCOPE (see the module header's ⚠): this proves `granted_bit ≤ held_bit` on cols 128+i / 120+i.
    /// It does NOT prove the granted bits govern the `rights` felt the cap-root commits — they do not;
    /// `nonamp_leg_does_not_bind_the_hashed_rights_felt` is the honest statement of that gap.
    #[test]
    fn nonamp_submask_gate_refuses_an_amplifying_witness() {
        let d = cap_delegation_nonamp_descriptor().expect("descriptor parses");

        // held = 0b0110_0111: bits 3 and 4 are CLEAR, so a granted bit there is an over-grant.
        let held: u32 = 0b0110_0111;

        // ── HONEST POLE FIRST. A genuine submask must PROVE. Without this the per-bit refusals below
        //    are satisfied by a descriptor that refuses everything — the vacuous canary.
        let honest = honest_witness(&d, held, 0b0010_0101);
        match run(&d, &honest) {
            Outcome::Accepted => {}
            Outcome::Refused(e) => panic!(
                "the HONEST submask witness (granted 0b0010_0101 ⊑ held {held:#010b}) was REFUSED: \
                 {e}. Every amplification refusal below is vacuous until this passes."
            ),
            Outcome::ConstraintPanic(m) => panic!(
                "the HONEST submask witness (granted 0b0010_0101 ⊑ held {held:#010b}) violated a \
                 constraint: {m}. Every amplification refusal below is vacuous until this passes."
            ),
        }

        // ── THE FORGERY, one bit at a time. Set granted bit `i` where held bit `i` is CLEAR.
        for i in 0..MASK_BITS {
            if (held >> i) & 1 == 1 {
                continue; // not an over-grant: held already confers this right
            }
            let granted = 1u32 << i;
            assert_ne!(
                granted & !held,
                0,
                "bit {i} must be an over-grant by construction"
            );

            // Build the amplifying witness with the mask recon KEPT CONSISTENT — the granted mask
            // column carries the amplified value and the bits decode it. So the ONLY unsatisfied
            // constraint is submask gate `i` (`gᵢ·(1−hᵢ) = 0`), not the recon gate. A test that let
            // the recon break would red for the wrong reason and would stay green if every submask
            // gate were deleted.
            let mut w = honest_witness(&d, held, 0);
            for row in &mut w.rows {
                row[DELEG_GRANTED_MASK_RECON_COL] = bb(granted);
                for j in 0..MASK_BITS {
                    row[DELEG_GRANTED_BIT_BASE + j] = bb((granted >> j) & 1);
                }
                fill_digests(&d, row);
            }
            // The chained accumulator + PI bindings do not depend on the granted bits (cols 128..135
            // feed no hash site), so re-chaining is unnecessary — but assert that, rather than assume:
            assert!(
                !d.hash_sites.iter().any(|s| {
                    s.inputs.iter().any(|inp| {
                        matches!(inp, HashInput::Col(c)
                        if (DELEG_GRANTED_BIT_BASE..DELEG_GRANTED_BIT_BASE + MASK_BITS).contains(c))
                    })
                }),
                "a granted BIT column feeds a hash site — this forgery would then break the digest \
                 chain too, and the refusal could not be attributed to the submask gate"
            );

            assert_constraint_refusal(
                &d,
                &w,
                &format!(
                    "an AMPLIFYING witness (granted bit {i} set, held bit {i} clear — held \
                     {held:#010b}, granted {granted:#010b})"
                ),
            );
        }
    }

    /// **⚠ THE DEFECT PIN — the non-amp leg does NOT bind the `rights` felt the cap-root commits.**
    ///
    /// This test asserts the CURRENT, WRONG behaviour on purpose, so the gap cannot be re-inherited by
    /// a reader who trusts the doc. **It is designed to go RED when the Lean emit is fixed** — that red
    /// is the signal the fix landed. Do not "repair" it by deleting it; delete it when the emit
    /// `prmCol`-wraps `dcol.GRANTED_MASK`, and the amplify tooth above will then cover this case.
    ///
    /// The claim under test is the module header's original one: "tamper the `rights` felt to dodge the
    /// submask gate and the recomputed `cap_root` moves ⇒ `state_commit` moves ⇒ UNSAT". The witness
    /// below does exactly that tamper — sets col 72 (the felt `siteCapEdgeLeaf` hashes) to a mask the
    /// delegator does NOT hold — while leaving the granted BITS at an honest submask. If the legs
    /// interlocked, this would be refused. It is ACCEPTED, because the granted bits reconstruct col 4
    /// and the edge leaf hashes col 72, and no constraint relates the two.
    ///
    /// Consequence, stated plainly: were this descriptor wired, a prover could confer ANY rights it
    /// liked through the cap-root — the in-circuit non-amplification would not touch them. It is not
    /// wired (see NOT WIRED), so this is a latent defect, not a live hole.
    #[test]
    fn nonamp_leg_does_not_bind_the_hashed_rights_felt() {
        let d = cap_delegation_nonamp_descriptor().expect("descriptor parses");
        let held: u32 = 0b0000_0011; // the delegator holds only rights 0 and 1

        // HONEST POLE — the honest witness proves, so an ACCEPT below means "this forgery slipped
        // through", not "this descriptor accepts anything".
        let honest = honest_witness(&d, held, 0b0000_0001);
        assert!(
            matches!(run(&d, &honest), Outcome::Accepted),
            "the honest witness must prove before this test can say anything about the forgery"
        );

        // Structural premise, asserted rather than assumed: the granted-bit recon binds col 4 and the
        // edge leaf hashes col 72. If a future emit changes either, this test's reasoning is stale and
        // it must red rather than quietly test nothing.
        let recon_binds = d.constraints.iter().any(|c| {
            matches!(c, VmConstraint::Gate(LeanExpr::Add(l, _))
                if matches!(**l, LeanExpr::Var(v) if v == DELEG_GRANTED_MASK_RECON_COL))
        });
        assert!(
            recon_binds,
            "the granted-mask recon gate no longer binds col {DELEG_GRANTED_MASK_RECON_COL} — the \
             emit changed. Re-derive this test (and delete it if the recon now binds col \
             {DELEG_HASHED_RIGHTS_COL})."
        );
        let leaf = d
            .hash_sites
            .first()
            .expect("the edge-leaf site is site 0 on this descriptor");
        assert!(
            leaf.inputs
                .contains(&HashInput::Col(DELEG_HASHED_RIGHTS_COL)),
            "the edge-leaf site no longer hashes col {DELEG_HASHED_RIGHTS_COL} — re-derive this test"
        );
        assert_ne!(
            DELEG_GRANTED_MASK_RECON_COL, DELEG_HASHED_RIGHTS_COL,
            "if these are equal the legs DO interlock and this defect pin must be deleted"
        );

        // THE FORGERY: honest granted BITS (⊑ held), but the hashed `rights` felt confers EVERYTHING.
        let mut w = honest_witness(&d, held, 0b0000_0001);
        for row in &mut w.rows {
            row[DELEG_HASHED_RIGHTS_COL] = bb(0xFF); // all 8 rights, none of them held
            fill_digests(&d, row); // the edge leaf + cap root + state commit all move, honestly
        }
        // Re-chain the accumulator so state_before[11]/[12] track the new digests — otherwise the
        // transition constraints would break and we would be observing the wrong refusal.
        rechain(&d, &mut w);

        match run(&d, &w) {
            Outcome::Accepted => { /* the expected, defective behaviour — see this test's doc */ }
            Outcome::Refused(e) => panic!(
                "the rights-felt tamper was REFUSED ({e}) — the legs INTERLOCK after all. If the Lean \
                 emit was fixed to bind the granted bits to prmCol(cp.RIGHTS)=\
                 {DELEG_HASHED_RIGHTS_COL}, DELETE this defect pin and drop the ⚠ section from the \
                 module header: the tooth is real now."
            ),
            Outcome::ConstraintPanic(m) => panic!(
                "the rights-felt tamper violated a constraint ({m}) — the legs INTERLOCK after all. \
                 If the Lean emit was fixed to bind the granted bits to prmCol(cp.RIGHTS)=\
                 {DELEG_HASHED_RIGHTS_COL}, DELETE this defect pin and drop the ⚠ section from the \
                 module header: the tooth is real now."
            ),
        }
    }

    /// **⚠ THE SECOND DEFECT PIN — the state-commit's GROUP-4 digest indices were never rebased.**
    ///
    /// Structural, not behavioural, and deliberately so: this pins WHICH sites the state-commit reads,
    /// which is the thing that is wrong. Site 5 (`digest_col` 88 = `state_commit`) reads digests
    /// `0,1,2`. On every OTHER emitted descriptor those are the GROUP-4 chain (cols 98/99/100); here
    /// the two cap-root sites were PREPENDED, so digests `0,1,2` resolve to cols `102, 87, 98` and
    /// `state_after[4..10]` never reaches the commitment. Sites 3/4 (cols 99/100) became dead carriers.
    ///
    /// Like the pin above, this is EXPECTED to red when the emit is fixed — that red is the fix
    /// landing. All 27 other descriptors are correct; this descriptor is the only one affected.
    #[test]
    fn state_commit_group4_chain_is_misindexed() {
        let d = cap_delegation_nonamp_descriptor().expect("descriptor parses");
        let cols: Vec<usize> = d.hash_sites.iter().map(|s| s.digest_col).collect();
        let commit = d
            .hash_sites
            .iter()
            .find(|s| s.digest_col == 88)
            .expect("the state-commit site (digest col 88) must exist");

        let resolved: Vec<usize> = commit
            .inputs
            .iter()
            .filter_map(|inp| match inp {
                HashInput::Digest(k) => Some(cols[*k]),
                _ => None,
            })
            .collect();

        // What the GROUP-4 chain intends, and what every other descriptor emits.
        let intended = vec![98usize, 99, 100];
        assert_ne!(
            resolved, intended,
            "the state-commit now absorbs the GROUP-4 chain {intended:?} — the misindexing is FIXED. \
             DELETE this defect pin and the corresponding paragraph in the module header."
        );
        assert_eq!(
            resolved,
            vec![102usize, 87, 98],
            "the state-commit's digest ordinals resolve to an unexpected set — re-derive this pin \
             against the current emit"
        );
        // The concrete consequence: state_after[4..10] is uncommitted, and two sites feed nothing.
        for dead in [99usize, 100] {
            assert!(
                !resolved.contains(&dead),
                "site with digest_col {dead} now feeds the state-commit — re-derive this pin"
            );
        }
    }

    /// Re-run the accumulator chain after a per-row edit: each row's `state_before[11]`/`[12]` must be
    /// the previous row's `state_after[11]`/`[12]` (the 14 transition constraints), and the digests
    /// must then be recomputed because the cap-root site reads `state_before[11]`.
    fn rechain(desc: &EffectVmDescriptor, w: &mut DelegWitness) {
        for r in 1..w.rows.len() {
            let (prev_cap, prev_commit) = (
                w.rows[r - 1][SA + CAP_ROOT_SLOT],
                w.rows[r - 1][SA + STATE_COMMIT_SLOT],
            );
            w.rows[r][SB + CAP_ROOT_SLOT] = prev_cap;
            w.rows[r][SB + STATE_COMMIT_SLOT] = prev_commit;
            w.rows[r][SA + CAP_ROOT_SLOT] = prev_cap;
            w.rows[r][SA + STATE_COMMIT_SLOT] = prev_commit;
            let row = &mut w.rows[r];
            fill_digests(desc, row);
        }
        w.pis[41] = w.rows[0][56];
        w.pis[20] = w.rows[0][54];
        w.pis[21] = w.rows[0][55];
        w.pis[0] = w.rows[0][66];
    }

    /// The committed JSON re-parses through the interpreter into the structure the prover consumes.
    /// The Lean↔JSON drift gate is generate-fresh `scripts/check-descriptor-drift.sh`, not a
    /// self-consistent FP rehash.
    ///
    /// The constraint-COUNT and hash-site-COUNT assertions this test used to carry are GONE on
    /// purpose (CRATE-EXCELLENCE-PLAN Move 3): a count catches nothing an adversary does — swap a gate
    /// for another of equal count and the count is unchanged — while reddening on a benign re-emit.
    /// That is churn, not a tooth. The behavioural teeth above are what protect the gates.
    #[test]
    fn genuine_nonamp_parses() {
        let d = cap_delegation_nonamp_descriptor()
            .expect("genuine-non-amp descriptor must parse via interpreter");
        assert_eq!(d.name, GENUINE_NONAMP_NAME, "parsed name != wire identity");
        assert_eq!(
            d.trace_width, EFFECT_VM_WIDTH,
            "the genuine-non-amp cap-graph row shares the 188-col EffectVM base trace (P0-2 \
             record-digest + asset-class)"
        );
    }

    /// Helper: does the per-bit NON-AMP submask gate body `g·(1 − h)` (a `mul` of `var(g)` with
    /// `add(const 1, mul(const -1, var(h)))`) appear in the constraint list for the given (granted,
    /// held) bit columns? Finding it for every bit confirms `granted ⊑ held` is enforced in-circuit.
    fn has_submask_gate(d: &EffectVmDescriptor, granted_col: usize, held_col: usize) -> bool {
        d.constraints.iter().any(|c| match c {
            VmConstraint::Gate(LeanExpr::Mul(l, r)) => {
                let lhs_is_granted = matches!(**l, LeanExpr::Var(v) if v == granted_col);
                let rhs_is_one_minus_held = match &**r {
                    LeanExpr::Add(a, b) => {
                        let a_is_one = matches!(**a, LeanExpr::Const(1));
                        let b_is_neg_held = matches!(&**b, LeanExpr::Mul(x, y)
                            if matches!(**x, LeanExpr::Const(-1))
                                && matches!(**y, LeanExpr::Var(v) if v == held_col));
                        a_is_one && b_is_neg_held
                    }
                    _ => false,
                };
                lhs_is_granted && rhs_is_one_minus_held
            }
            _ => false,
        })
    }

    /// THE ANTI-AMPLIFY TOOTH is present on the cap-graph family: for EVERY mask bit, the descriptor
    /// carries the submask gate `granted_bit·(1 − held_bit) = 0` over the DELEGATION bit columns
    /// (held `[120,128)`, granted `[128,136)`). So the interpreted circuit ENFORCES `granted ⊑ held`
    /// bitwise — in-circuit non-amplification on every delegation effect, not an executor side-check.
    #[test]
    fn genuine_nonamp_carries_anti_amplify_teeth() {
        let d = cap_delegation_nonamp_descriptor().unwrap();
        for i in 0..MASK_BITS {
            assert!(
                has_submask_gate(&d, DELEG_GRANTED_BIT_BASE + i, DELEG_HELD_BIT_BASE + i),
                "non-amp submask gate missing for bit {i} (granted {} ≤ held {})",
                DELEG_GRANTED_BIT_BASE + i,
                DELEG_HELD_BIT_BASE + i
            );
        }
    }

    /// THE GENUINE CAP-ROOT RECOMPUTE is present (NOT an opaque digest): the descriptor carries the two
    /// recompute hash-sites — the edge leaf `hash[holder, target, rights, op]` (arity 4) into the leaf
    /// carrier (col 102) and the advance `hash[edge_leaf, old_cap_root]` (arity 2) into the cap-root
    /// after-column (col 87). So the post `cap_root` is FORCED by the bound edge mutation, interlocking
    /// with the non-amp gate on the same `rights` felt (col 72).
    #[test]
    fn genuine_nonamp_carries_caproot_recompute() {
        let d = cap_delegation_nonamp_descriptor().unwrap();
        // the edge-leaf recompute site: arity 4, digest into col 102 (CAP_EDGE_LEAF), reading params
        // holder/target/rights/op (cols 70/71/72/73).
        let leaf_site = d
            .hash_sites
            .iter()
            .find(|s| s.digest_col == 102)
            .expect("cap-edge-leaf recompute site (digest col 102) missing");
        assert_eq!(
            leaf_site.arity, 4,
            "edge leaf is hash[holder,target,rights,op]"
        );
        assert_eq!(leaf_site.inputs.len(), 4);
        // the advance site: arity 2, digest into col 87 (saCol CAP_ROOT), reading the leaf (102) + the
        // old cap-root column (65 = sbCol CAP_ROOT).
        let adv_site = d
            .hash_sites
            .iter()
            .find(|s| s.digest_col == 87)
            .expect("cap-root advance site (digest col 87 = saCol CAP_ROOT) missing");
        assert_eq!(
            adv_site.arity, 2,
            "advance is hash[edge_leaf, old_cap_root]"
        );
        assert_eq!(adv_site.inputs.len(), 2);
    }
}
