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
//! ## THE TWO LEGS INTERLOCK — the granted recon and the cap-root recompute bind ONE felt (fixed 2026-07-17)
//!
//! The per-bit submask gates constrain `granted ⊑ held`, and the granted bits reconstruct the SAME
//! `rights` felt the recompute hashes into the edge leaf. The two mask-reconstruction gates read:
//!
//! ```text
//! gate 54:  v75 − Σ_{i<8} v(120+i)·2ⁱ     (held mask recon,    prmCol 7)
//! gate 55:  v72 − Σ_{i<8} v(128+i)·2ⁱ     (granted mask recon, prmCol cp.RIGHTS)
//! ```
//!
//! Column 72 (`prmCol cp.RIGHTS`) is exactly the felt `siteCapEdgeLeaf` hashes into `cap_root`. So
//! tampering that felt to confer rights outside the held mask breaks gate 55 ⇒ UNSAT — the interlock is
//! real. `nonamp_leg_binds_the_hashed_rights_felt` exercises it: the tamper is REFUSED.
//!
//! ### The two emit defects this used to carry (both fixed 2026-07-17)
//!
//! **Defect 1 — a param-index/column conflation.** `EffectVmEmitCapReshape.dcol.GRANTED_MASK :=
//! EffectVmEmitCapRoot.cp.RIGHTS`, and `cp.RIGHTS = 4` is a **param INDEX** — its column is
//! `prmCol 4 = 72`. `gMaskRecon` consumes a raw COLUMN, so the gate read `v4` (an effect-SELECTOR
//! column, block `0..54`) and `dcol.HELD_MASK := 7` read `v7`. Nothing related those to the rights
//! param, so a prover could confer ARBITRARY rights through a perfectly-bound `cap_root`. Fixed by
//! `prmCol`-wrapping both `gMaskRecon` call sites in `capDelegNonAmpGates`.
//!
//! **Defect 2 — the state-commit's `Digest k` ordinals were never rebased on the prepend.** Site 5
//! (`digest_col` 88 = `state_commit`) read digests `0,1,2` = cols `102, 87, 98` (edge leaf, cap root,
//! inter1) where the GROUP-4 chain intends `98, 99, 100`, so `state_after[4..10]` never reached the
//! commitment and sites 3/4 were dead carriers. Fixed by
//! `attenuateHashSites.map (shiftSiteDigests capRecomputeSites.length)` at the prepend in
//! `EffectVmEmitAttenuateA.attenuateGenuineHashSites`. `state_commit_absorbs_group4_chain` asserts it.
//!
//! Both were found by the Rust differentials below, not by Lean — `capDeleg_nonAmp_in_circuit` /
//! `capDeleg_rejects_amplify` quantify over the BIT CARRIERS (cols 128+i / 120+i) and were true either
//! way; only the PROSE claimed the felt link, and `#assert_axioms` cannot see a false sentence. Neither
//! defect was ever live — nothing routes to this descriptor (see NOT WIRED below), so both were LATENT.
//!
//! ⚠ RESIDUAL — the HELD mask (col 75 = `prmCol dcol.HELD_MASK`) is a FREE PARAM: no hash-site absorbs
//! it, no PI binds it. The interlock refutes rights-felt FORGERY, but `granted ⊑ held` bounds the
//! committed rights only by a mask the PROVER CHOSE. Binding col 75 to an opened parent cap is the next
//! rung (see `EffectVmEmitCapReshape` §4D's RESIDUAL). ⚠ The mint-flavour `capReshapeVmDescriptor`
//! (a SEPARATE emitted JSON, consumed by `cap_reshape_descriptor.rs`) still carries the identical
//! Defect-1 conflation on its own `nonAmpGates` — verified, in HORIZONLOG, out of this module's scope.
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
    "0d84e70fd0f9dd6f52d0353c948eeb8b03ffc25f7d777dfcc496bbf3c7b74315";

/// The descriptor name (the canonical wire identity — shared across the six cap-graph effects).
pub const GENUINE_NONAMP_NAME: &str = "dregg-effectvm-attenuateA-v1-genuine-nonamp";

/// The `Auth` rights-mask bit width (8 atoms ⇒ 8 bits): mirrors Lean `EffectVmEmitCapReshape.MASK_BITS`.
pub const MASK_BITS: usize = 8;

/// The DELEGATION held-mask bit columns. Mirrors Lean `dcol.heldBit i = 120 + i`
/// (`col.GRANTED_BIT_BASE + MASK_BITS = 112 + 8 = 120`), past the mint-flavour bit block.
pub const DELEG_HELD_BIT_BASE: usize = 120;

/// The DELEGATION granted-mask bit columns. Mirrors Lean `dcol.grantedBit i = 128 + i`
/// (`col.GRANTED_BIT_BASE + 2·MASK_BITS = 112 + 16 = 128`). These reconstruct
/// [`DELEG_GRANTED_MASK_RECON_COL`] = 72 = `prmCol cp.RIGHTS` — the SAME felt the edge leaf hashes, the
/// load-bearing tie (fixed 2026-07-17; was col 4).
pub const DELEG_GRANTED_BIT_BASE: usize = 128;

/// The column the granted-mask bit recon binds: `prmCol dcol.GRANTED_MASK` = `prmCol cp.RIGHTS` = 72
/// (Lean `gMaskRecon (prmCol dcol.GRANTED_MASK) …`). This IS [`DELEG_HASHED_RIGHTS_COL`] — the rights
/// felt the cap-root edge leaf hashes — so the non-amp leg and the cap-root recompute interlock on one
/// felt. Until 2026-07-17 this was col 4 (the param INDEX used raw), an effect-selector column.
pub const DELEG_GRANTED_MASK_RECON_COL: usize = 72;

/// The column the held-mask bit recon binds: `prmCol dcol.HELD_MASK` = `prmCol 7` = 75 (fixed
/// 2026-07-17; was col 7, the index used raw).
pub const DELEG_HELD_MASK_RECON_COL: usize = 75;

/// The `rights` felt the cap-root edge-leaf site genuinely hashes: `prmCol cp.RIGHTS` = `PARAM_BASE + 4`
/// = 72. The granted-mask recon now binds exactly this column ([`DELEG_GRANTED_MASK_RECON_COL`]).
pub const DELEG_HASHED_RIGHTS_COL: usize = 72;

/// The full EffectVM base trace width — re-exported from the canonical layout
/// (`effect_vm::columns`, which Lean `EffectVmEmit` mirrors), NOT re-typed here. A literal `188`
/// would drift silently the moment the layout moved; this way a layout change is a compile error.
pub use crate::effect_vm::columns::EFFECT_VM_WIDTH;

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
    use crate::plonky3_prover::DreggStarkConfig;
    use crate::refusal::{Outcome, classify, must_accept};
    use p3_batch_stark::BatchProof;

    // ── The EffectVM base layout, taken from the CANONICAL column module rather than re-typed as
    //    literals. Lean `EffectVmEmit`'s bases are defined to be these same numbers, and the emitted
    //    descriptor's `Var` indices ARE prover column indices — so if the layout ever moves, this
    //    witness builder must move with it, and binding to the constants makes that a compile error
    //    instead of a silently-wrong trace that reds in some unrelated gate.
    use crate::effect_vm::columns::{PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE};
    /// `STATE_BEFORE_BASE` (= `NUM_EFFECTS` = 54).
    const SB: usize = STATE_BEFORE_BASE;
    /// `PARAM_BASE` (= 68).
    const PB: usize = PARAM_BASE;
    /// `STATE_AFTER_BASE` (= 76).
    const SA: usize = STATE_AFTER_BASE;
    /// The state-block width (`state::SIZE` = 14).
    const STATE_SIZE: usize = crate::effect_vm::columns::state::SIZE;
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

    /// Prove `w` under `desc`, classified three ways by the SHARED reject-idiom helper
    /// (`crate::refusal`, CRATE-EXCELLENCE-PLAN Move 3's "kill the idiom" lane).
    ///
    /// We use `classify` rather than a private catch_unwind for one reason worth stating: it pins the
    /// EXACT p3 marker strings (`P3_UNSAT_PANIC_MARKERS`) and REDS on any panic that is not the
    /// documented unsat verdict. A stray `unwrap` in trace assembly, an index panic, a shape
    /// `assert_eq!` — none of those are the constraint system refusing, and a private helper matching
    /// on `"constraint"`/`"assert"` substrings (what this module first grew) would have laundered them
    /// straight back into the P1b anti-pattern the plan exists to kill.
    fn run(
        desc: &EffectVmDescriptor,
        w: &DelegWitness,
        what: &str,
    ) -> Outcome<BatchProof<DreggStarkConfig>, String> {
        classify(what, || prove_vm_descriptor(desc, &w.rows, &w.pis))
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
    /// SCOPE: this proves `granted_bit ≤ held_bit` on cols 128+i / 120+i (the bit carriers). The
    /// companion `nonamp_leg_binds_the_hashed_rights_felt` exercises the OTHER half — that the granted
    /// bits reconstruct the `rights` felt the cap-root commits, so the two legs interlock.
    #[test]
    fn nonamp_submask_gate_refuses_an_amplifying_witness() {
        let d = cap_delegation_nonamp_descriptor().expect("descriptor parses");

        // held = 0b0110_0111: bits 3 and 4 are CLEAR, so a granted bit there is an over-grant.
        let held: u32 = 0b0110_0111;

        // ── HONEST POLE FIRST. A genuine submask must PROVE. Without this the per-bit refusals below
        //    are satisfied by a descriptor that refuses everything — the vacuous canary.
        let honest = honest_witness(&d, held, 0b0010_0101);
        must_accept(
            "the honest submask witness (granted 0b0010_0101 ⊑ held 0b0110_0111)",
            || prove_vm_descriptor(&d, &honest.rows, &honest.pis),
        );

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

            // `must_refuse_or_unsat_panic` semantics, via the shared classifier: an `Ok` is an OPEN
            // tooth, and a panic that is not the p3 debug prover's DOCUMENTED unsat verdict reds
            // inside `classify` rather than being laundered as a refusal.
            let what = format!(
                "an AMPLIFYING witness (granted bit {i} set, held bit {i} clear — held \
                 {held:#010b}, granted {granted:#010b})"
            );
            match run(&d, &w, &what) {
                Outcome::Accepted(_) => panic!(
                    "{what} was ACCEPTED — the per-bit non-amp submask gate is OPEN on bit {i}"
                ),
                // The refusal we expect: the row violates submask gate `i`, so the p3 debug
                // constraint checker names it. `classify` has already proved the panic is the
                // documented unsat marker and not a crash.
                Outcome::UnsatPanic(_) => {}
                // Also a genuine fail-closed refusal (prove_vm_descriptor self-verifies before
                // returning Ok, so a forged witness can surface here instead).
                Outcome::Err(_) => {}
            }
        }
    }

    /// **THE INTERLOCK TOOTH — the non-amp leg BINDS the `rights` felt the cap-root commits.**
    ///
    /// The dual of `nonamp_submask_gate_refuses_an_amplifying_witness`: that test forges the granted
    /// BITS; this one forges the `rights` FELT the edge leaf hashes into `cap_root` while leaving the
    /// granted bits at an honest submask. The two legs now interlock on ONE felt (col 72 =
    /// `prmCol cp.RIGHTS` = [`DELEG_GRANTED_MASK_RECON_COL`] = [`DELEG_HASHED_RIGHTS_COL`]), so a
    /// `rights` felt outside the held mask breaks the granted-recon gate ⇒ UNSAT.
    ///
    /// Until 2026-07-17 this test PINNED THE OPPOSITE: the emit read a raw param INDEX (col 4) instead
    /// of `prmCol cp.RIGHTS`, so nothing related the granted bits to col 72 and this forgery was
    /// ACCEPTED — a prover could confer ANY rights through a perfectly-bound `cap_root`. The Lean fix
    /// (`gMaskRecon (prmCol dcol.GRANTED_MASK) …` in `EffectVmEmitCapReshape.capDelegNonAmpGates`)
    /// closed it; this test now asserts the REFUSAL.
    ///
    /// ⚠ SCOPE: the HELD mask (col 75) is still a free param on this descriptor, so this proves the
    /// committed rights are a submask of a PROVER-CHOSEN mask — it refutes rights-felt forgery, not
    /// non-amplification against an opened parent cap. See the module header's RESIDUAL.
    #[test]
    fn nonamp_leg_binds_the_hashed_rights_felt() {
        let d = cap_delegation_nonamp_descriptor().expect("descriptor parses");
        let held: u32 = 0b0000_0011; // the delegator holds only rights 0 and 1

        // HONEST POLE — the honest witness proves, so a REFUSAL below means "this forgery was caught",
        // not "this descriptor refuses everything".
        let honest = honest_witness(&d, held, 0b0000_0001);
        must_accept(
            "the honest delegation witness (granted 0b01 ⊑ held 0b11) — this test cannot say \
             anything about the forgery below until the honest pole proves",
            || prove_vm_descriptor(&d, &honest.rows, &honest.pis),
        );

        // Structural premise, asserted rather than assumed: the granted-bit recon binds the SAME column
        // the edge leaf hashes (col 72). This is the interlock; if a future emit breaks it, this test's
        // reasoning is stale and it must red rather than quietly test nothing.
        let recon_binds = d.constraints.iter().any(|c| {
            matches!(c, VmConstraint::Gate(LeanExpr::Add(l, _))
                if matches!(**l, LeanExpr::Var(v) if v == DELEG_GRANTED_MASK_RECON_COL))
        });
        assert!(
            recon_binds,
            "the granted-mask recon gate no longer binds col {DELEG_GRANTED_MASK_RECON_COL} — the \
             emit changed. Re-derive this test."
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
        assert_eq!(
            DELEG_GRANTED_MASK_RECON_COL, DELEG_HASHED_RIGHTS_COL,
            "the granted recon and the edge-leaf rights felt must be the SAME column — that identity IS \
             the interlock this test exercises. If they differ, the emit regressed."
        );
        assert!(
            DELEG_HASHED_RIGHTS_COL >= PARAM_BASE,
            "the hashed rights felt must be in the param block — re-derive this pin"
        );

        // THE FORGERY: honest granted BITS (⊑ held), but the hashed `rights` felt confers EVERYTHING.
        // Because the granted bits now reconstruct col 72, setting col 72 = 0xFF while the bits decode
        // 0b01 makes the granted-recon gate `v72 − Σ bitᵢ·2ⁱ = 0xFF − 1 ≠ 0` — UNSAT.
        let mut w = honest_witness(&d, held, 0b0000_0001);
        for row in &mut w.rows {
            row[DELEG_HASHED_RIGHTS_COL] = bb(0xFF); // all 8 rights, none of them held
            fill_digests(&d, row); // the edge leaf + cap root + state commit all move, honestly
        }
        // Re-chain the accumulator so state_before[11]/[12] track the new digests — otherwise the
        // transition constraints would break and we would be observing the wrong refusal.
        rechain(&d, &mut w);

        match run(&d, &w, "the rights-felt tamper") {
            // The tooth: the interlock catches the tamper. A constraint-violation panic (the p3 unsat
            // marker, already classified by `run`) or a fail-closed self-verify error are both refusals.
            Outcome::UnsatPanic(_) => {}
            Outcome::Err(_) => {}
            Outcome::Accepted(_) => panic!(
                "the rights-felt tamper was ACCEPTED — the interlock is OPEN. The granted-recon gate \
                 must bind prmCol(cp.RIGHTS)={DELEG_HASHED_RIGHTS_COL}; if the Lean emit regressed to a \
                 raw param index this test is meaningless. Check \
                 EffectVmEmitCapReshape.capDelegNonAmpGates uses `gMaskRecon (prmCol dcol.GRANTED_MASK)`."
            ),
        }
    }

    /// **THE STATE-COMMIT ABSORBS THE GROUP-4 CHAIN — the prepend-rebased digest ordinals.**
    ///
    /// Structural: this pins WHICH sites the state-commit reads. Site 5 (`digest_col` 88 =
    /// `state_commit`) reads digests `2,3,4`, which resolve to the GROUP-4 chain cols `98/99/100` — so
    /// `state_after[4..10]` reaches the commitment and no site is a dead carrier.
    ///
    /// Until 2026-07-17 the state-commit read digests `0,1,2` — the ordinals were never rebased when
    /// the two cap-root sites were PREPENDED, so they resolved to `102, 87, 98` (edge leaf, cap root,
    /// inter1) and `state_after[4..10]` never reached the commitment. The Lean fix
    /// (`attenuateHashSites.map (shiftSiteDigests capRecomputeSites.length)` in
    /// `EffectVmEmitAttenuateA.attenuateGenuineHashSites`) rebased them; this test now asserts the
    /// GROUP-4 chain is absorbed.
    #[test]
    fn state_commit_absorbs_group4_chain() {
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

        // The GROUP-4 chain — what every emitted descriptor absorbs into state_commit.
        let intended = vec![98usize, 99, 100];
        assert_eq!(
            resolved, intended,
            "the state-commit must absorb the GROUP-4 chain {intended:?}. If it resolves to \
             [102, 87, 98] the prepend-rebase regressed — check \
             EffectVmEmitAttenuateA.attenuateGenuineHashSites shifts the chain's digest ordinals by \
             capRecomputeSites.length."
        );
        // The pre-fix ordinals (edge leaf, cap root, inter1) must NOT be what state_commit reads.
        assert_ne!(
            resolved,
            vec![102usize, 87, 98],
            "the state-commit resolves to the pre-rebase set — the misindexing regressed"
        );
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
