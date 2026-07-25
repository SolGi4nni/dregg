//! # `cap_reshape_descriptor` — the OPENABLE `capability_root` descriptor loader (the ARGUS linchpin).
//!
//! The cap-reshape crown (#103): the Lean-verified `EffectVmDescriptor` that checks, IN-CIRCUIT, the
//! two capability-security openings a light client must trust WITHOUT re-running history:
//!
//!   * **non-amplification** — a granted cap is `≤` a held cap (the in-row submask gates
//!     `granted_bit ≤ held_bit` per bit, over the opened held leaf);
//!   * **production-authority** — a mint is gated on OPENING the issuer cap from the producer's held-set
//!     root (the held `target` binds the minted-asset PI + the control/mint bit is set).
//!
//! ## Provenance (anti-drift, the LAW#1 way)
//!
//! `dregg-effectvm-capreshape-v1.json` is the output of the verified Lean emit
//! `Dregg2.Circuit.Emit.EffectVmEmitCapReshape.capReshapeJson` (`emitVmJson capReshapeVmDescriptor`),
//! a CACHE of that emission (Lean is the source of truth). The Rust prover INTERPRETS this descriptor
//! via `parse_vm_descriptor` (it AUTHORS NO CONSTRAINT — the constraints are emitted from the proved
//! Lean module). The test below re-parses the JSON into the prover's structure; the Lean↔JSON drift
//! gate is generate-fresh `scripts/check-descriptor-drift.sh` (`CAPRESHAPE_V1_FP` is a cache-freshness
//! pin, NOT a faithfulness check).
//!
//! This is a STANDALONE loader (its own module + test), NOT registered in the locked
//! `effect_vm_descriptors` registry (whose count assertions would otherwise break). The descriptor is
//! the openable-`capability_root` check the sdk authority-binding (the Phase-D payoff) routes to; this
//! module proves it parses + carries the anti-amplify + anti-unauthorized-mint teeth.
//!
//! ## THE HELD BITS BIND THE HASHED HELD-MASK FELT — the mint-flavour interlock (fixed 2026-07-24)
//!
//! The submask gates and the production control-bit gate both read the HELD BIT carriers
//! (cols 104..112). Those bits are meaningful only if they decode the mask the opened held leaf
//! COMMITS, and that is the job of the held mask-reconstruction gate:
//!
//! ```text
//! gate 24:  v72 − Σ_{i<8} v(104+i)·2ⁱ     (held mask recon,    prmCol col.HELD_MASK)
//! gate 25:  v74 − Σ_{i<8} v(112+i)·2ⁱ     (granted mask recon, prmCol col.GRANTED_MASK)
//! ```
//!
//! Column 72 is exactly the felt Lean's `siteHeldLeaf`
//! (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean`)
//! hashes into the held leaf (`hash[slot, target, held_mask, 0]`, cols 70/71/72). So inflating the
//! held bits breaks gate 24 ⇒ UNSAT. `held_bits_bind_the_hashed_held_mask_felt` exercises it BOTH
//! ways: the pre-fix bytes ACCEPT the forgery, the fixed bytes REFUSE it.
//!
//! ### The defect this used to carry (the same param-index/column conflation as the delegation flavour)
//!
//! `gMaskRecon` consumes a raw COLUMN, but `col.HELD_MASK := cp.RIGHTS = 4` and
//! `col.GRANTED_MASK := 6` are param INDICES — their columns are `prmCol 4 = 72` / `prmCol 6 = 74`.
//! Emitted unwrapped, gates 24/25 read `v4`/`v6`, both inside the effect-SELECTOR block (`0..54`),
//! which this descriptor does not constrain at all. Nothing then related the held BITS to col 72,
//! and BOTH teeth came apart at once: a prover sets every `held_bit[i] = 1`, which makes every
//! submask gate `g·(1−h) = g·0 = 0` vacuously true AND satisfies the production control-bit gate
//! `held_bit[6] = 1` for free, while col 72 — the mask the membership opening actually commits —
//! carries an honest read-only mask. So a proof could confer ALL EIGHT rights, mint authority
//! included, off an opened read-only cap. Deployed in `dregg-effectvm-capreshape-v1.json`
//! (sha256 `594ab88a…`) until 2026-07-24; the fix `prmCol`-wraps both `gMaskRecon` call sites in
//! `EffectVmEmitCapReshape.nonAmpGates`, exactly as `capDelegNonAmpGates` was fixed on 2026-07-17.
//!
//! As with the delegation flavour, no Lean proof and no `#assert_axioms` flagged it:
//! `capReshape_nonAmp_in_circuit` / `capReshape_production_in_circuit` quantify over the BIT
//! CARRIERS and were true either way. It was the PROSE that was false, and only a witness put to
//! the running prover can say so.
//!
//! ⚠ RESIDUAL (unchanged by this fix) — col 72 is bound to the held LEAF (site 0), but this
//! descriptor does not bind that leaf to any published cap-root: the leaf digest (col 103) feeds no
//! further site and no PI. The membership opening of the held leaf against the producer's
//! authenticated `cap_root` is the turn-level binding (`full_turn_proof.rs`), cited not carried
//! here. So the tooth this JSON emits is "the granted mask and the mint right are bounded by the
//! mask the recomputed held leaf commits" — a felt-level interlock, not yet an opening.
//!
//! ## The carried hypothesis (honest seam)
//!
//! The descriptor checks the SUBMASK shadow of non-amplification (`granted_bit ≤ held_bit`, bit by bit)
//! and binds the rights digest into the opened held leaf; the bridge to the genuine `Finset Auth`
//! lattice is the Lean `entryEncodes` correspondence (`EffectVmEmitCapReshape` §2′). The turn-level
//! binding of the opened `cap_root` to the producer's authenticated cell-root is the sdk
//! authority-binding (`full_turn_proof.rs`), cited not duplicated here.

use crate::lean_descriptor_air::{EffectVmDescriptor, parse_vm_descriptor};

/// The verified-Lean JSON cache for the openable-`capability_root` descriptor (Lean is the
/// source of truth; regenerated by `scripts/emit-descriptors.sh`).
pub const CAPRESHAPE_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-capreshape-v1.json");

/// SHA-256 cache-freshness pin for the committed bytes (re-pinned by the emit script; NOT a
/// faithfulness check — the Lean↔JSON gate is generate-fresh `scripts/check-descriptor-drift.sh`).
pub const CAPRESHAPE_V1_FP: &str =
    "621f9d0f81fca703fc4dda7cc02b9537133152126af79b22acd7ffaa64cad522";

/// The descriptor name (the canonical wire identity).
pub const CAPRESHAPE_V1_NAME: &str = "dregg-effectvm-capreshape-v1";

/// The `Auth` rights-mask bit width (8 atoms ⇒ 8 bits): mirrors Lean `EffectVmEmitCapReshape.MASK_BITS`.
pub const MASK_BITS: usize = 8;

/// The held-mask bit columns (aux block, `[104, 112)` on the 186-col layout). Mirrors Lean
/// `col.heldBit i = 104 + i`.
pub const HELD_BIT_BASE: usize = 104;

/// The granted-mask bit columns (`[112, 120)`). Mirrors Lean `col.grantedBit i = 112 + i`.
pub const GRANTED_BIT_BASE: usize = 112;

/// The control-bit position (`authBit control = 64 = 2^6`). Mirrors Lean `CONTROL_BIT_POS`.
pub const CONTROL_BIT_POS: usize = 6;

/// The column the HELD-mask bit recon binds: `prmCol col.HELD_MASK` = `prmCol cp.RIGHTS` = 72
/// (Lean `gMaskRecon (prmCol col.HELD_MASK) …`). This IS [`HASHED_HELD_MASK_COL`] — the felt the
/// held-leaf site hashes — so the submask/control teeth and the membership opening interlock on one
/// felt. Until 2026-07-24 this was col 4 (the param INDEX used raw), an effect-selector column.
pub const HELD_MASK_RECON_COL: usize = 72;

/// The column the GRANTED-mask bit recon binds: `prmCol col.GRANTED_MASK` = `prmCol 6` = 74 (fixed
/// 2026-07-24; was col 6, the index used raw).
pub const GRANTED_MASK_RECON_COL: usize = 74;

/// The `held_mask` felt the held-leaf site genuinely hashes: `prmCol cp.RIGHTS` = `PARAM_BASE + 4`
/// = 72. The held-mask recon now binds exactly this column ([`HELD_MASK_RECON_COL`]).
pub const HASHED_HELD_MASK_COL: usize = 72;

/// The `slot` param the held-leaf site hashes (`prmCol col.SLOT` = `prmCol cp.HOLDER` = 70).
pub const SLOT_COL: usize = 70;

/// The `target` param the held-leaf site hashes AND the production PI binding pins to PI[0]
/// (`prmCol col.TARGET` = 71).
pub const TARGET_COL: usize = 71;

/// Parse the openable-`capability_root` descriptor through the running EffectVM interpreter.
/// (The same `parse_vm_descriptor` the cutover dispatcher uses; the descriptor drives the verified
/// circuit for the cap-reshape row.)
pub fn cap_reshape_descriptor() -> Result<EffectVmDescriptor, String> {
    parse_vm_descriptor(CAPRESHAPE_V1_JSON)
}

#[cfg(test)]
mod tests {
    use super::*;
    // The constraint AST forms inspected by the anti-amplify / production-authority teeth.
    // These live in `lean_descriptor_air` (plonky3-gated, same as this module's descriptor
    // types) and are not part of this module's runtime surface, so they're imported here.
    use crate::lean_descriptor_air::{LeanExpr, VmConstraint};

    /// The committed JSON re-parses through the interpreter into the structure the prover
    /// consumes (name, width, PI count, constraint count, hash site). The Lean↔JSON drift gate
    /// is generate-fresh `scripts/check-descriptor-drift.sh`, not a self-consistent FP rehash.
    #[test]
    fn capreshape_parses() {
        let d =
            cap_reshape_descriptor().expect("cap-reshape descriptor must parse via interpreter");
        assert_eq!(d.name, CAPRESHAPE_V1_NAME, "parsed name != wire identity");
        assert_eq!(
            d.trace_width, 188,
            "cap-reshape shares the 188-col EffectVM base trace (P0-2 record-digest + asset-class)"
        );
        assert_eq!(d.public_input_count, 1, "the minted-asset PI");
        // 8 held-bool + 8 granted-bool + 8 submask + 2 recon + 1 PI binding + 1 control gate = 28.
        assert_eq!(d.constraints.len(), 3 * MASK_BITS + 2 + 2);
        // one held-leaf recompute site (`hash[slot, target, held_mask, 0]`, arity 4).
        assert_eq!(d.hash_sites.len(), 1);
        assert_eq!(d.hash_sites[0].inputs.len(), 4);
        assert_eq!(d.hash_sites[0].arity, 4);
    }

    /// Helper: does the gate body `g·(1 − h)` (a `mul` of `var(g)` with `add(const 1, mul(const -1,
    /// var(h)))`) appear in the constraint list for the given (granted, held) bit columns? This is the
    /// per-bit NON-AMP submask tooth; finding it for every bit confirms `granted ⊑ held` is enforced.
    fn has_submask_gate(d: &EffectVmDescriptor, granted_col: usize, held_col: usize) -> bool {
        d.constraints.iter().any(|c| match c {
            VmConstraint::Gate(LeanExpr::Mul(l, r)) => {
                let lhs_is_granted = matches!(**l, LeanExpr::Var(v) if v == granted_col);
                // r = add(const 1, mul(const -1, var held))
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

    /// THE ANTI-AMPLIFY TOOTH is present in the circuit: for EVERY mask bit, the descriptor carries the
    /// submask gate `granted_bit·(1 − held_bit) = 0` (a granted bit may be set only where the held bit
    /// is). So the interpreted circuit ENFORCES `granted ⊑ held` bitwise — non-amplification in-circuit,
    /// not an executor-trusted side-check.
    #[test]
    fn capreshape_carries_anti_amplify_teeth() {
        let d = cap_reshape_descriptor().unwrap();
        for i in 0..MASK_BITS {
            assert!(
                has_submask_gate(&d, GRANTED_BIT_BASE + i, HELD_BIT_BASE + i),
                "non-amp submask gate missing for bit {i} (granted {} ≤ held {})",
                GRANTED_BIT_BASE + i,
                HELD_BIT_BASE + i
            );
        }
    }

    /// THE ANTI-UNAUTHORIZED-MINT TOOTH is present: the descriptor carries (a) a first-row PI binding
    /// pinning the held cap's `target` param (col 71) to the minted-asset PI (index 0) — the opened
    /// issuer cap must target the asset — and (b) the control-bit gate `held_bit[6] − 1 = 0` forcing the
    /// mint right. So a mint WITHOUT the held issuer cap is rejected in-circuit.
    #[test]
    fn capreshape_carries_production_authority_teeth() {
        let d = cap_reshape_descriptor().unwrap();
        // (a) the asset-binding PI: target param (col 71) == PI[0] on the first row.
        let has_asset_pi = d.constraints.iter().any(|c| {
            matches!(c, VmConstraint::PiBinding { col, pi_index, .. } if *col == 71 && *pi_index == 0)
        });
        assert!(
            has_asset_pi,
            "production-authority asset PI binding missing"
        );
        // (b) the control-bit gate: add(var held_bit[6], mul(const -1, const 1)) = 0, i.e. h6 = 1.
        let has_control_gate = d.constraints.iter().any(|c| match c {
            VmConstraint::Gate(LeanExpr::Add(l, r)) => {
                matches!(**l, LeanExpr::Var(v) if v == HELD_BIT_BASE + CONTROL_BIT_POS)
                    && matches!(&**r, LeanExpr::Mul(x, y)
                        if matches!(**x, LeanExpr::Const(-1)) && matches!(**y, LeanExpr::Const(1)))
            }
            _ => false,
        });
        assert!(
            has_control_gate,
            "production-authority control-bit gate (held_bit[6] = 1) missing"
        );
    }

    // ── THE BEHAVIOURAL CANARY (both polarities, and both descriptor GENERATIONS).
    //
    // Everything above pattern-matches the descriptor AST for a gate-SHAPED subtree. That is
    // exactly the class of test the pre-2026-07-24 bytes passed while the teeth were decoupled:
    // all 8 submask gates and the control gate were PRESENT, over bit carriers nothing tied to the
    // committed mask. Below, a witness is built and the running prover is required to refuse it —
    // and the SAME witness is run against the deployed pre-fix bytes, where it must be ACCEPTED.
    // Without that second leg this test cannot distinguish "the tooth bites" from "the tooth was
    // never missing".

    use crate::field::BabyBear;
    use crate::lean_descriptor_air::{HashInput, prove_vm_descriptor, vm_site_digest_concrete};
    use crate::refusal::{Outcome, classify, must_accept};

    /// The trace height. Gates bind on the transition domain (rows `0..n-2`); hash sites on EVERY
    /// row. 4 rows means 3 gated rows, not a single row that is its own successor.
    const N_ROWS: usize = 4;

    fn bb(v: u32) -> BabyBear {
        BabyBear::new(v)
    }

    /// A cap-reshape witness: the trace rows plus the single minted-asset public input.
    struct ReshapeWitness {
        rows: Vec<Vec<BabyBear>>,
        pis: Vec<BabyBear>,
    }

    /// Recompute every hash site's digest cell for a row, in site order — the same resolution
    /// `extend_vm_trace` uses, so the sites are pinned by the AIR's own arithmetic and a forgery
    /// under test is the only unsatisfied constraint.
    fn fill_digests(desc: &EffectVmDescriptor, row: &mut [BabyBear]) {
        let mut digests: Vec<BabyBear> = Vec::with_capacity(desc.hash_sites.len());
        for site in &desc.hash_sites {
            let d = vm_site_digest_concrete(site, row, &digests);
            row[site.digest_col] = d;
            digests.push(d);
        }
    }

    /// The witness an honest producer lays down for a cap-reshape row.
    ///
    /// `leaf_held` is the mask the held LEAF commits (col 72 — what `siteHeldLeaf` hashes);
    /// `bit_held` is what the held BIT carriers decode. On an honest row they are equal, and the
    /// forgery below is exactly the row where they are not.
    ///
    /// `legacy_index_cols` additionally writes the masks at the raw param INDICES (cols 4 and 6).
    /// Those columns are unconstrained by the fixed descriptor and are what the PRE-FIX descriptor
    /// read; writing them lets ONE witness be run against both generations unchanged.
    fn witness(
        desc: &EffectVmDescriptor,
        leaf_held: u32,
        bit_held: u32,
        granted: u32,
        legacy_index_cols: bool,
    ) -> ReshapeWitness {
        let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(N_ROWS);
        for _ in 0..N_ROWS {
            let mut row = vec![BabyBear::ZERO; desc.trace_width];

            // The opened held entry's content, as the leaf site hashes it: hash[slot, target,
            // held_mask, 0]. `target` is also the column the production PI binding pins to PI[0].
            row[SLOT_COL] = bb(5);
            row[TARGET_COL] = bb(9); // the minted asset
            row[HASHED_HELD_MASK_COL] = bb(leaf_held);
            row[GRANTED_MASK_RECON_COL] = bb(granted);

            // The bit carriers the submask gates and the production control-bit gate read.
            for i in 0..MASK_BITS {
                row[HELD_BIT_BASE + i] = bb((bit_held >> i) & 1);
                row[GRANTED_BIT_BASE + i] = bb((granted >> i) & 1);
            }

            if legacy_index_cols {
                // The effect-SELECTOR columns the pre-fix recon gates mistakenly read. The fixed
                // descriptor constrains neither, so this is inert against it.
                row[4] = bb(bit_held);
                row[6] = bb(granted);
            }

            fill_digests(desc, &mut row);
            rows.push(row);
        }

        let pis = vec![rows[0][TARGET_COL]];
        ReshapeWitness { rows, pis }
    }

    fn run(
        desc: &EffectVmDescriptor,
        w: &ReshapeWitness,
        what: &str,
    ) -> Outcome<p3_batch_stark::BatchProof<crate::plonky3_prover::DreggStarkConfig>, String> {
        classify(what, || prove_vm_descriptor(desc, &w.rows, &w.pis))
    }

    /// The DEPLOYED PRE-FIX descriptor, reconstructed byte-exactly from the fixed artifact.
    ///
    /// The whole difference between the two committed JSONs is the two recon gates' column reads:
    /// `"v":72` → `"v":4` and `"v":74` → `"v":6`, 5803 bytes vs 5801, nothing else. Applying that
    /// substitution to `CAPRESHAPE_V1_JSON` therefore reproduces
    /// `dregg-effectvm-capreshape-v1.json` @ sha256 `594ab88a9c4198557b1283cb0749445b…` — the bytes
    /// that were in HEAD until 2026-07-24 — rather than a hand-made approximation of them.
    /// Each anchor must occur EXACTLY ONCE or the reconstruction is not what this test claims.
    fn deployed_prefix_descriptor() -> EffectVmDescriptor {
        const HELD_ANCHOR: &str = r#"{"t":"gate","body":{"t":"add","l":{"t":"var","v":72},"#;
        const GRANTED_ANCHOR: &str = r#"{"t":"gate","body":{"t":"add","l":{"t":"var","v":74},"#;
        assert_eq!(
            CAPRESHAPE_V1_JSON.matches(HELD_ANCHOR).count(),
            1,
            "the held-recon anchor is not unique in the committed JSON — the emit moved and this \
             pre-fix reconstruction is stale. Re-derive it against the artifact this commit replaced."
        );
        assert_eq!(
            CAPRESHAPE_V1_JSON.matches(GRANTED_ANCHOR).count(),
            1,
            "the granted-recon anchor is not unique in the committed JSON — re-derive it."
        );
        let legacy = CAPRESHAPE_V1_JSON
            .replace(
                HELD_ANCHOR,
                r#"{"t":"gate","body":{"t":"add","l":{"t":"var","v":4},"#,
            )
            .replace(
                GRANTED_ANCHOR,
                r#"{"t":"gate","body":{"t":"add","l":{"t":"var","v":6},"#,
            );
        let d = parse_vm_descriptor(&legacy).expect("the pre-fix descriptor must parse");
        // The reconstruction IS the defect: both recon gates read effect-selector columns.
        let reads = |c: usize| {
            d.constraints.iter().any(|k| {
                matches!(k, VmConstraint::Gate(LeanExpr::Add(l, _))
                    if matches!(**l, LeanExpr::Var(v) if v == c))
            })
        };
        assert!(
            reads(4) && reads(6),
            "the pre-fix reconstruction does not read cols 4/6 — it is not the descriptor that was \
             deployed, and the 'was SAT before' leg below would prove nothing"
        );
        d
    }

    /// **THE MINT-FLAVOUR INTERLOCK, BOTH WAYS — the held bits bind the felt the leaf hashes.**
    ///
    /// The mint mirror of the delegation flavour's `nonamp_leg_binds_the_hashed_rights_felt`. The
    /// forgery: every held BIT set (`0xFF`) while the held-mask FELT the leaf commits (col 72) is an
    /// honest read-only `0b1`. All eight held bits set makes every submask gate `g·(1−h) = g·0 = 0`
    /// vacuously true AND satisfies the production control-bit gate `held_bit[6] = 1` — so this one
    /// witness defeats the anti-amplification tooth and the anti-unauthorized-mint tooth together,
    /// granting all 8 rights (mint included) off an opened read-only cap.
    ///
    /// Three legs, in the order that makes the verdict mean something:
    ///
    /// 1. **honest pole** (fixed bytes) — a genuine row PROVES, so a refusal in leg 3 is not "this
    ///    descriptor refuses everything";
    /// 2. **was it SAT before?** (deployed PRE-FIX bytes, same witness) — ACCEPTED. This is what
    ///    makes leg 3 a demonstration that the tooth BITES rather than that it is merely present;
    /// 3. **is it UNSAT after?** (fixed bytes, same witness) — REFUSED: gate 24 is
    ///    `v72 − Σ h_i·2ⁱ = 1 − 255 ≠ 0`.
    #[test]
    fn held_bits_bind_the_hashed_held_mask_felt() {
        let fixed = cap_reshape_descriptor().expect("descriptor parses");

        // Structural premises, asserted rather than assumed: the held-mask recon binds the SAME
        // column the leaf site hashes. That identity IS the interlock under test.
        let recon_binds_72 = fixed.constraints.iter().any(|c| {
            matches!(c, VmConstraint::Gate(LeanExpr::Add(l, _))
                if matches!(**l, LeanExpr::Var(v) if v == HELD_MASK_RECON_COL))
        });
        assert!(
            recon_binds_72,
            "the held-mask recon gate no longer binds col {HELD_MASK_RECON_COL} — the emit changed. \
             Re-derive this test."
        );
        let leaf = fixed
            .hash_sites
            .first()
            .expect("the held-leaf site is site 0 on this descriptor");
        assert!(
            leaf.inputs.contains(&HashInput::Col(HASHED_HELD_MASK_COL)),
            "the held-leaf site no longer hashes col {HASHED_HELD_MASK_COL} — re-derive this test"
        );
        assert_eq!(
            HELD_MASK_RECON_COL, HASHED_HELD_MASK_COL,
            "the held recon and the leaf's held-mask felt must be the SAME column — that identity IS \
             the interlock. If they differ, the emit regressed to the raw param index."
        );

        // ── LEG 1: the honest pole. Held = {read, control} = 0b0100_0001 (the issuer cap for the
        //    asset), granted = {read} = 0b0000_0001. h6 = 1, granted ⊑ held, both recons decode.
        let honest = witness(&fixed, 0b0100_0001, 0b0100_0001, 0b0000_0001, true);
        must_accept(
            "the honest cap-reshape witness (held {read,control}, granted {read}) — this test can \
             say nothing about the forgery until the honest pole proves",
            || prove_vm_descriptor(&fixed, &honest.rows, &honest.pis),
        );

        // ── THE FORGERY. The leaf commits a read-only mask; the bits claim everything.
        const LEAF_HELD: u32 = 0b0000_0001; // what the opened held leaf actually commits
        const FORGED_BITS: u32 = 0xFF; // what the held bit carriers claim
        const GRANTED: u32 = 0xFF; // all eight rights conferred, mint included
        assert_ne!(
            GRANTED & !LEAF_HELD,
            0,
            "the forgery must confer rights the committed mask does not hold"
        );
        assert_eq!(
            (FORGED_BITS >> CONTROL_BIT_POS) & 1,
            1,
            "the forgery must also satisfy the production control-bit gate — that is the second \
             tooth it defeats"
        );

        // ── LEG 2: was it SAT before? Run the SAME forgery against the deployed pre-fix bytes.
        let legacy = deployed_prefix_descriptor();
        let w_legacy = witness(&legacy, LEAF_HELD, FORGED_BITS, GRANTED, true);
        match run(
            &legacy,
            &w_legacy,
            "the held-bit inflation vs the PRE-FIX bytes",
        ) {
            // ACCEPTED — the pre-fix bytes prove the forgery: held bits 0b1111_1111 over a committed
            // mask of 0b0000_0001, conferring all 8 rights incl. mint. The tooth was OPEN. (The other
            // two arms panic, so this test PASSING is the record of that acceptance.)
            Outcome::Accepted(_) => {}
            Outcome::UnsatPanic(m) => panic!(
                "the PRE-FIX descriptor REFUSED the held-bit inflation ({m}) — then the defect this \
                 test documents was not what was deployed, and leg 3's refusal proves nothing about \
                 the fix. Re-derive the reconstruction in deployed_prefix_descriptor()."
            ),
            Outcome::Err(e) => panic!(
                "the PRE-FIX descriptor REFUSED the held-bit inflation ({e}) — see above; the \
                 both-ways canary is broken, not the tooth."
            ),
        }

        // ── LEG 3: is it UNSAT after? The same forgery, the fixed bytes.
        let w_fixed = witness(&fixed, LEAF_HELD, FORGED_BITS, GRANTED, true);
        match run(
            &fixed,
            &w_fixed,
            "the held-bit inflation vs the FIXED bytes",
        ) {
            // REFUSED — the constraint system rejects the SAME witness under the fixed bytes
            // (`classify` has already proved a panic here is p3's documented unsat verdict and not
            // a crash). Gate 24 is `v72 − Σ h_i·2ⁱ = 1 − 255 ≠ 0`.
            Outcome::UnsatPanic(_) => {}
            Outcome::Err(_) => {}
            Outcome::Accepted(_) => panic!(
                "the held-bit inflation was ACCEPTED — BOTH the anti-amplification and the \
                 anti-unauthorized-mint teeth are OPEN. The held-mask recon gate must bind \
                 prmCol(col.HELD_MASK)={HASHED_HELD_MASK_COL}; if the Lean emit regressed to a raw \
                 param index this descriptor grants all rights off a read-only cap. Check \
                 EffectVmEmitCapReshape.nonAmpGates uses `gMaskRecon (prmCol col.HELD_MASK)`."
            ),
        }
    }
}
