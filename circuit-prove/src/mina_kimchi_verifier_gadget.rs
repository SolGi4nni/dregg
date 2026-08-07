//! ⚑⚑ **A KIMCHI VERIFIER GADGET, IN PLONKY3'S OWN RECURSION — THE CHALLENGE THE FINALIZE
//! CONJUNCTS CHECK IS THE ONE THE BLOCK'S OWN SPONGE SQUEEZED.**
//!
//! ⚠⚠ **LABEL, FIRST, BEFORE ANYTHING ELSE IN THIS FILE IS READ.** This is **an implementation,
//! unverified, with a named path to verification** (§"THE VERIFICATION PATH", below). It proves on
//! a box. That is **not** verified and **not** sound: it inherits the undischarged FRI/STARK floor,
//! and the tests in `circuit-prove/tests/mina_kimchi_verifier_gadget.rs` are Rust **case-tests** —
//! they are not translation validation, not refinement, and not verification, because there is no
//! formal semantics of Rust and a case-test says nothing about all inputs.
//!
//! ⚑ **NOT ONE AIR CONSTRAINT IS AUTHORED IN RUST HERE, AND THAT IS NOT A RELAXATION.** House law
//! #1 holds unchanged in this module: every AIR the tower proves comes out of Lean
//! (`dregg-pasta-fq-chainlink::v1`, `dregg-mina-xi-endo-lift::v1`, `dregg-mina-wrap-conjunction::v1`).
//! What this file authors is **recursion-circuit wiring** — `cb.connect` over targets the child
//! verifiers already bound — which is the same category as
//! [`crate::mina_phase2_chain_leaf::fold_chain_links`] and
//! [`crate::mina_wrap_finalize_fold::fold_endo_into_finalize`], not a hand-written `Builder` gadget.
//!
//! # ⚑ THE HOLE THIS CLOSES, QUOTED FROM THE FILE THAT DECLARED IT
//!
//! `mina_wrap_finalize_fold.rs` §"WHAT THE ROOT DOES NOT SAY", reason 3:
//!
//! > *"**`v′` is published, not derived.** Tying it to the block's own Fq transcript is
//! > [`connect_chain_root_v_prime`]'s job, and that leg needs the 46-leaf chain fold … Until a
//! > caller runs that fold and connects it, `v′` is a prover-chosen 128-bit value and the root is
//! > quantified over it."*
//!
//! [`crate::mina_wrap_finalize_fold::connect_chain_root_v_prime`] existed as a **declared seam with
//! no caller**: `git grep` finds it in a docblock, its own definition, and a test that says it is
//! *not* what the test does. This module is the caller. It runs the 46-leaf chain fold's ROOT and
//! the endo/conjunction fold's ROOT into one more aggregation layer, verifies both **in-circuit**,
//! and issues the connects.
//!
//! # ⚑ WHAT IS CARRIED, AND WHY IT IS `cb.connect` AND NOT A RE-PIN
//!
//! > *"A fold that just re-pins the same public inputs closes nothing."* — `mina_phase2_chain_leaf`
//!
//! Every lane below is read from a child's OWN FRI-bound `air_public_targets`, never from a free
//! scalar the aggregation circuit invents. **128 in-circuit constraints**, in three groups:
//!
//! 1. **The fresh-sponge pin — 96 connects.** `chain.in_state[k] == 0` for all 96 limbs. Before
//!    this, `ChainClaim::starts_from_a_fresh_sponge` was a HOST predicate: a prover could publish a
//!    chain root that starts from a sponge state of its choosing and the finalize root would never
//!    notice. It is now a constraint of the parent proof.
//! 2. **The `v′` weld — 16 connects.** `chain.out_state` lane 0's low 16 limbs ARE the endo-lift's
//!    `v′` limbs `0..16`. This is the one that makes `v′` derived rather than chosen.
//! 3. **The truncation pin — 16 connects.** `v′` limbs `16..32` are pinned to zero. Without it,
//!    "the low 128 bits of the terminal squeeze" is not what the weld enforces — a prover picks 128
//!    free high bits and the reading is false. Groups 2 and 3 are both
//!    [`crate::mina_wrap_finalize_fold::connect_chain_root_v_prime`], reused rather than re-typed,
//!    so there is ONE definition of this seam in the workspace.
//!
//! ⚑ A `cb.connect` to a `define_const` **is** a pin at the pinned fork rev, and that was MEASURED,
//! not read: `circuit-prove/tests/const_pin_probe.rs` records the answer flipping at `fc3c6df`,
//! where `ConstAir`'s preprocessed row gained `value[0..D]` and its `eval` gained the `D` degree-1
//! constraints `main.value[i] == prep.value[i]`
//! (`circuit-prover/src/air/const_air.rs`, the `Air::eval` impl). At the previous rev groups 1 and 3
//! would have forced nothing. This is exactly the kind of capability that must be checked at source
//! rather than taken from a docblock.
//!
//! # WHAT THE ROOT CLAIM SAYS
//!
//! ```text
//!   transcript_acc(8) ‖ v'(32) ‖ zeta(32) ‖ zetaw(32) ‖ r(32) ‖ b0(32)      = 168 lanes
//! ```
//!
//! > **Starting from a FRESH Kimchi `fq_sponge` `(0,0,0)`, absorbing exactly the ordered tape that
//! > `transcript_acc` commits to, the squeezed polyscale prechallenge is `v′`; `ScalarChallenge(v′)`
//! > lifts by the endomorphism to a ξ; and against THAT ξ, this ζ, this ζω and this evalscale `r`,
//! > the published `b0` equals `bEval ζ chals + r · bEval ζω chals` for the fifteen IPA challenges
//! > the conjunction's own rows supplied, each welded to its inverse.**
//!
//! ξ is deliberately NOT republished — it is internal to the aggregation two layers down, and
//! `v′` is now internal-by-derivation but IS republished, because a consumer must be able to
//! compare it against the block's own `proof.oracles(…)` output and that comparison is now a
//! comparison against a DERIVED value rather than a free one.
//!
//! # ⚠ WHAT THE ROOT DOES **NOT** SAY — five, named, not summarised
//!
//! 0. ⚑ **NOT THAT THE TAPE IS BLOCK 539508's — the root is QUANTIFIED over the tape.** Read
//!    precisely, the claim is *"there EXISTS an ordered tape, committed by `transcript_acc`, which
//!    absorbs from a fresh sponge to a squeeze whose low 128 bits are this `v′`."* Nothing
//!    **inside** the circuit names a block. What names it is a HOST comparison of the exposed
//!    `transcript_acc` against
//!    [`crate::mina_phase2_chain_leaf::host_chain_transcript_acc`] over the block's real tape, and
//!    **a consumer that skips that comparison holds a root about some tape, not this one.** This is
//!    listed first because it is the item most likely to be lost in a summary: the other four are
//!    about STRENGTH, this one is about SUBJECT.
//! 1. **Not that the Kimchi/Pickles proof is valid. The IPA opening is not in circuit.**
//!    `Dregg2.Circuit.Emit.PastaIpaDeferral.opening_is_vacuous_when_sg_is_free` is a Lean theorem
//!    that the closing check accepts at **every** value of everything else while `sg` is a free
//!    witness. Nothing in this fold moves that, and nothing in this fold binds `sg`. ⚑ Read
//!    §"WHERE THE PASTA ARITHMETIC LIVES" for what would.
//! 2. **Not finalize.** Upstream Pickles' `finalize_other_proof` is a FOUR-way AND; the conjunction
//!    child forces TWO conjuncts (`xiCorrect`, `bCorrect`). `cipCorrect` and `plonkChecksPassed` are
//!    absent BY CONSTRUCTION, not stubbed — `MinaWrapConjunctionAir` §"WHAT THIS OBJECT FORCES"
//!    states that comparing `cip` against a ξ-fold with a FREE `ft_eval0` column forces nothing.
//! 3. ⚑ **NEITHER CHILD'S VK IDENTITY IS PINNED IN-CIRCUIT — measured at source, not inferred.**
//!    [`RecursionOutput::into_recursion_input`] passes `expected_preprocessed_commit: None`
//!    (`recursion/src/recursion.rs`, the `into_recursion_input` body), and `RecursionInput::
//!    BatchStark`'s own docblock on that field says what that costs: *"without this pin its VALUE is
//!    unconstrained — a from-scratch prover could fold a proof of a DIFFERENT circuit."* The parent
//!    circuit's SHAPE is still derived from each child's `CommonData`, so a child with different
//!    AIRs moves the parent's VK and a consumer's fingerprint pin refuses it. What is NOT excluded
//!    is a child of **identical table shape and different preprocessed CONTENT** — and since
//!    `ConstAir` puts constant values in the preprocessed commitment
//!    (`circuit-prover/src/air/const_air.rs`), that means a chain-link descriptor with the same
//!    constraint structure and **different sponge round constants** would be accepted here.
//!    ⚠ This is **not new to this gadget** — no fold in this tower pins
//!    (`fold_chain_links`, `fold_endo_into_finalize`, this one) — and pinning only the TOP fold
//!    would close almost nothing, because the substitution is available at any of the 45 chain folds
//!    beneath it. The fix is `into_recursion_input_pinned` at EVERY fold, with each layer's own
//!    [`RecursionOutput::running_preprocessed_commit`] extracted once from a reference honest run.
//!    That is **wiring across four call sites plus a reference-extraction step**, not research, and
//!    it is the first item of follow-on work rather than a later phase.
//! 4. **ζ, ζω and `r` are still published and derived by nothing.** The chain root's outgoing lane 1
//!    is the block's `u′` (evalscale prechallenge) and its low 128 bits are available on the left
//!    child at exactly the same cost as `v′` — but the endo lift `u′ → r` needs a SECOND instance of
//!    `dregg-mina-xi-endo-lift::v1`'s trace, which is Lean emit output this module does not
//!    generate. That is the next leg and it is one `regen` away, not a redesign. ζ / ζω come from
//!    the phase-1 (Fp) transcript, whose chain descriptor exists (`pasta-fp-chainlink.json`) with no
//!    weld to this object.
//!
//! # ⚑ WHERE THE PASTA ARITHMETIC LIVES — the question this design is an answer to
//!
//! Kimchi verifies natively in Pasta because Pallas/Vesta are a 2-cycle. **We have no cycle**: the
//! recursion circuit's native field is `BinomialExtensionField<BabyBear, 4>`, and a 255-bit Pasta
//! element does not fit a lane. So the question is not "how do we avoid Pasta ops" but *which ones
//! are in-circuit and which are a leaf's witness with the recursion carrying the claim*. As built:
//!
//! | Kimchi verifier step | Where it lives | What binds it |
//! |---|---|---|
//! | Fq sponge absorb/squeeze (46 permutations) | **in-AIR**, Lean `dregg-pasta-fq-chainlink::v1` | 45×96 `cb.connect`s carry the state; per-leaf Poseidon commitment over the absorbed limbs folds into `transcript_acc` |
//! | `ScalarChallenge(v′) → ξ` endo lift | **in-AIR**, Lean `dregg-mina-xi-endo-lift::v1` | 32 `cb.connect`s to the conjunction's ξ block |
//! | `v′` provenance | **in-circuit HERE** | the 16+16 connects of this module |
//! | `bEval`, `xiCorrect`, challenge/inverse reciprocity | **in-AIR**, Lean `dregg-mina-wrap-conjunction::v1` | its own constraints |
//! | `cip`, `ft_eval0`, `plonkChecks` | **NOWHERE** | nothing — absent by construction |
//! | **IPA opening / the `sg` MSM** | **NOWHERE** | nothing — and `opening_is_vacuous_when_sg_is_free` is the theorem that says so |
//!
//! ⚠ **"Put it in the witness" is only sound if something else binds it, and for `sg` nothing does.**
//! The Pasta *scalar* arithmetic is the tractable half: it is field arithmetic over a 255-bit
//! modulus, which the emitted sound ALU row (`dregg-pasta-alu-sound::v1`, 226 columns) already does
//! in-AIR. The Pasta *curve* arithmetic is the wall: `dregg-pasta-pallas-rcb-thread::v1` is 3 048
//! columns for one complete addition. ⚠ **This module inherits NO cost figure from that cone** — a
//! sibling lane is separately establishing that the standing numbers were trace-independent
//! artifacts. Nothing here is priced against them; §"MEASURED" reports only what this module ran.
//!
//! # ⚑ THE VERIFICATION PATH — what a Lean refinement of this gadget would have to say
//!
//! This is the deliverable that makes "implementation first" honest rather than a slide back into
//! Rust AIRs, so it is stated as an obligation with a subject, not as an aspiration.
//!
//! The gadget is a function from two child claim vectors to a parent claim vector plus a constraint
//! set. A refinement of it must be a theorem **about that emitted object**, and there are three
//! statements, in dependency order:
//!
//! * **R1 — the wiring denotes the seam.** Today `connect_chain_root_v_prime`'s index arithmetic
//!   (`0..16` welded, `16..32` zeroed, at claim offsets `STATE_WIDTH + 0·SK` and `KV_VPRIME`) is
//!   Rust. Lean must EMIT it: a `chainToFinalizePins : List (Nat × Nat)` beside
//!   `MinaPhase2Chain.chainPins`, with `theorem the_v_prime_seam_is_the_terminal_squeeze` proving
//!   the pin list is exactly the low-128-bit truncation of outgoing lane 0. The Rust side then
//!   *reads* that list instead of computing offsets — the same move
//!   `mina_phase2_chain_leaf` made for `chainPins`. **This is the only leg that removes hand-written
//!   Rust from the trusted path, and it is the one to do first.**
//! * **R2 — the composition denotes the conjunction.** A theorem that the parent claim of the fold
//!   is the AND of the two child claims under the seam substitution: `chainClaim c ∧ finalizeClaim f
//!   ∧ seam c f → kimchiClaim (fold c f)`, over the SAME `Dregg2` predicates
//!   `the_chain_ends_at_the_blocks_challenges` and `MinaWrapConjunctionAir`'s conjuncts are stated
//!   against. ⚠ This must be stated so it is **refutable**: drop the seam hypothesis and it must
//!   fail to prove. A `P → P` here would be worth nothing and this repo has shipped one.
//! * **R3 — the claim is Kimchi's.** The terminal obligation, and the honest one to name as far
//!   away: `kimchiClaim` implies the Kimchi verifier's own predicate. It **cannot be discharged
//!   while the opening is out of circuit** — R3 is exactly `cipCorrect ∧ plonkChecksPassed ∧
//!   openingCheck`, and `opening_is_vacuous_when_sg_is_free` is a proof that the third conjunct is
//!   unavailable at any `sg` binding we currently have. **Naming R3 is not progress toward R3.**
//!
//! ⚠ And the floor under all three: a refinement of the GADGET is not a proof that the PROVER is
//! sound. The FRI/STARK soundness floor is undischarged in this tree
//! (`project-fri-soundness-reality`: conjectured 130 / proven 51–73 bits), and no theorem about
//! this wiring touches it.

use p3_recursion::{BatchOnly, RecursionOutput, Target};

use crate::gpu_backend::prove_recursion_aggregation_auto_with_expose;
use crate::ivc_turn_chain::expose_claim_instance_index;
use crate::mina_phase2_chain_leaf::{CHAIN_CLAIM_LEN, STATE_WIDTH};
use crate::mina_wrap_finalize_fold::{
    CLAIM_VPRIME, FINALIZE_CLAIM_LEN, SK, connect_chain_root_v_prime,
};
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

// ⚑ THE CLAIM SHAPE AND ITS READER LIVE IN `dregg-recursion-verify`, NOT HERE — a node that
// consumes this root must read it without linking the prover crate.
pub use dregg_recursion_verify::kimchi_root::{
    KIMCHI_CLAIM_LEN, KV_ACC, KV_B0, KV_R, KV_VPRIME, KV_ZETA, KV_ZETAW, KimchiClaim,
    V_PRIME_LIMBS, kimchi_root_config, read_kimchi_claim_from_proof,
};

/// ⚑ TWO INDEPENDENT SOURCES, PINNED. The verify crate declares the finalize root's claim length so
/// it can state the pairwise-distinctness assertion without a prover-crate edge; the prover crate
/// declares it because `fold_endo_into_finalize` builds it. A constant checked against its own
/// definition is decoration — this is the other kind, and it is what stops the two crates drifting
/// into "two shapes that agree today".
const _: () =
    assert!(FINALIZE_CLAIM_LEN == dregg_recursion_verify::kimchi_root::FINALIZE_CLAIM_LEN);

/// ⚑ AND THE SAME PIN FOR THE TRUNCATION WIDTH. `V_PRIME_LIMBS` is declared on BOTH sides for the
/// same reason: the verify crate needs it to read `v′` back as 128 bits, the prover crate needs it
/// to emit the pins. Two constants that agree today are two constants that disagree later, and this
/// pair decides how many limbs of a 255-bit lane the weld covers — a disagreement would silently
/// widen or narrow the claim.
const _: () = assert!(V_PRIME_LIMBS == crate::mina_wrap_finalize_fold::V_PRIME_LIMBS);

/// Claim offset of the chain root's OUTGOING sponge state.
pub const CHAIN_OUT_LO: usize = STATE_WIDTH;
/// …and of its outgoing lane 0, whose low 128 bits are the block's `v′`.
pub const CHAIN_OUT_LANE0: usize = CHAIN_OUT_LO;
/// Claim offset of the chain root's ordered transcript commitment.
pub const CHAIN_ACC_LO: usize = 2 * STATE_WIDTH;
/// Width of that commitment.
pub const CHAIN_ACC_WIDTH: usize = CHAIN_CLAIM_LEN - CHAIN_ACC_LO;

/// The number of in-circuit `connect`s this gadget issues: 96 fresh-sponge + 16 weld + 16 zero-pin.
///
/// Stated as a constant because "how many constraints does the gadget add" is the first question a
/// reader has and the answer should not require counting loops.
pub const GADGET_CONNECTS: usize = STATE_WIDTH + V_PRIME_LIMBS + (SK - V_PRIME_LIMBS);

/// ⚑⚑ **THE GADGET.** Fold a phase-2 transcript chain ROOT and an endo/conjunction finalize ROOT
/// into one claim, welding `v′` to the transcript's terminal squeeze inside the recursion circuit.
///
/// Both children are verified **in-circuit** by the aggregation layer before the expose hook runs,
/// so the targets the connects act on are FRI-bound, not prover-supplied.
///
/// # Refusals
///
/// Refuses before proving if either child's `expose_claim` table is the wrong width — a
/// 200-lane left child and a 160-lane right child are the only shapes whose lane offsets this
/// module's index arithmetic is about, and folding some other root would be reading a claim as a
/// sentence it does not say.
pub fn fold_transcript_into_finalize(
    chain_root: &RecursionOutput<DreggRecursionConfig>,
    finalize_root: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let chain_idx = require_claim(chain_root, "phase-2 chain root", CHAIN_CLAIM_LEN)?;
    let fin_idx = require_claim(
        finalize_root,
        "endo/conjunction finalize root",
        FINALIZE_CLAIM_LEN,
    )?;

    let chain_input = chain_root.into_recursion_input::<BatchOnly>();
    let fin_input = finalize_root.into_recursion_input::<BatchOnly>();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       chain_apt: &[Vec<Target>],
                       fin_apt: &[Vec<Target>],
                       _chain_vk_cap: &[Target],
                       _fin_vk_cap: &[Target]| {
        let c = chain_apt
            .get(chain_idx)
            .expect("chain root expose_claim instance present");
        let f = fin_apt
            .get(fin_idx)
            .expect("finalize root expose_claim instance present");
        debug_assert_eq!(c.len(), CHAIN_CLAIM_LEN);
        debug_assert_eq!(f.len(), FINALIZE_CLAIM_LEN);

        // The one constant this gadget needs. `alloc_const` is a PIN at the pinned fork rev —
        // `ConstAir`'s `eval` constrains `main.value[i] == prep.value[i]` — measured in
        // `const_pin_probe.rs`, not read off a docblock.
        let zero = cb.alloc_const(
            <RecursionChallenge as p3_field::PrimeCharacteristicRing>::ZERO,
            "kimchi gadget: the zero the fresh sponge and the v' truncation are pinned to",
        );

        // ⚑ GROUP 1 — THE FRESH-SPONGE PIN. The chain started at `(0,0,0)`, as a constraint of this
        // proof rather than as a host predicate a reader may forget to call.
        for k in 0..STATE_WIDTH {
            cb.connect(c[k], zero);
        }

        // ⚑ GROUPS 2 AND 3 — THE `v′` WELD AND ITS TRUNCATION PIN, through the ONE definition of
        // this seam in the workspace.
        connect_chain_root_v_prime(
            cb,
            &c[CHAIN_OUT_LANE0..CHAIN_OUT_LANE0 + SK],
            &f[CLAIM_VPRIME..CLAIM_VPRIME + SK],
            zero,
        );

        let mut parent: Vec<Target> = Vec::with_capacity(KIMCHI_CLAIM_LEN);
        // The tape this whole sentence is about, carried up from the left child.
        parent.extend_from_slice(&c[CHAIN_ACC_LO..CHAIN_ACC_LO + CHAIN_ACC_WIDTH]);
        // …and the finalize root's five blocks, `v′` first — now a DERIVED value.
        parent.extend_from_slice(&f[..FINALIZE_CLAIM_LEN]);
        debug_assert_eq!(parent.len(), KIMCHI_CLAIM_LEN);
        cb.expose_as_public_output(&parent);
    };

    prove_recursion_aggregation_auto_with_expose(&chain_input, &fin_input, config, Some(&expose))
        .map_err(|e| format!("transcript -> finalize fold failed: {e}"))
}

/// Read the kimchi-verifier claim this gadget's root publishes.
///
/// ⚑ Delegates to the VERIFY crate's reader — the same function a node runs over a decoded root, so
/// a fold measured here and a root consumed there cannot read the claim differently.
pub fn read_kimchi_claim(output: &RecursionOutput<DreggRecursionConfig>) -> Option<KimchiClaim> {
    read_kimchi_claim_from_proof(&output.0)
}

/// The config every leaf, fold and root in this tower runs at — the SAME one the phase-2 chain and
/// the finalize fold use, because an aggregation of two proofs minted at different FRI engines does
/// not build.
pub fn kimchi_config() -> DreggRecursionConfig {
    kimchi_root_config()
}

fn require_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
    role: &str,
    want: usize,
) -> Result<usize, String> {
    let len = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map_or(0, |e| e.public_values.len());
    if len != want {
        return Err(format!(
            "{role} exposes {len} claim lane(s), expected exactly {want}; refusing to read a claim \
             as a sentence it does not say"
        ));
    }
    expose_claim_instance_index(&output.0).ok_or_else(|| {
        format!("{role} carries no expose_claim instance despite its claimed layout")
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The claim layout has no aliasing, and the offsets this module indexes with are the ones the
    /// two child modules publish.
    #[test]
    fn the_gadget_layout_agrees_with_both_children() {
        // The LEFT child's layout, as `mina_phase2_chain_leaf` defines it.
        assert_eq!(CHAIN_OUT_LO, 96);
        assert_eq!(CHAIN_OUT_LANE0, 96);
        assert_eq!(CHAIN_ACC_LO, 192);
        assert_eq!(CHAIN_ACC_WIDTH, 8);
        assert_eq!(CHAIN_ACC_LO + CHAIN_ACC_WIDTH, CHAIN_CLAIM_LEN);

        // The RIGHT child's, as `mina_wrap_finalize_fold` defines it. `v′` is its FIRST block, which
        // is why the parent claim can be `acc ‖ <the whole finalize claim>`.
        assert_eq!(CLAIM_VPRIME, 0);
        assert_eq!(FINALIZE_CLAIM_LEN, 160);

        // …and the parent's.
        assert_eq!(KV_ACC, 0);
        assert_eq!(KV_VPRIME, CHAIN_ACC_WIDTH);
        assert_eq!(KIMCHI_CLAIM_LEN, CHAIN_ACC_WIDTH + FINALIZE_CLAIM_LEN);
        assert_eq!(KIMCHI_CLAIM_LEN, 168);

        // The concatenation is only correct because the finalize claim's block order is
        // `v' ‖ zeta ‖ zetaw ‖ r ‖ b0` and the parent's tail repeats it verbatim.
        assert_eq!(KV_VPRIME + SK, KV_ZETA);
        assert_eq!(KV_ZETA + SK, KV_ZETAW);
        assert_eq!(KV_ZETAW + SK, KV_R);
        assert_eq!(KV_R + SK, KV_B0);
        assert_eq!(KV_B0 + SK, KIMCHI_CLAIM_LEN);
    }

    /// The constraint count this gadget adds, stated so a reader does not have to count loops.
    #[test]
    fn the_gadget_issues_one_hundred_and_twenty_eight_connects() {
        assert_eq!(GADGET_CONNECTS, 128);
        assert_eq!(GADGET_CONNECTS, STATE_WIDTH + SK);
        assert!(
            V_PRIME_LIMBS < SK,
            "v' is 128 of 255 bits — if it were the whole field the truncation pin would be empty \
             and group 3 would force nothing"
        );
    }
}
