//! ⚑⚑ **THE IPA CLOSING CHAIN, AS A RECURSION TREE — and the leg that binds `sg` folded into it.**
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-mina-wrap-closing-{seg,final,srs}::v1` are
//! `EffectLower.lowerAir` of `Dregg2.Circuit.Emit.MinaWrapClosingAir.{closingSegAir,
//! closingFinalAir, closingRoutedAirOn}`. Not one constraint is authored here: the descriptors,
//! their pins, their manifest and their traces all come out of Lean. Rust proves the artifact and
//! folds it.
//!
//! ## WHAT THIS IS THE OTHER SIDE OF
//!
//! `MinaWrapOpeningGate` proves the IPA opening relation on Mina devnet block 539508 in the
//! KERNEL, and `MinaWrapVerifierAir.opening_is_vacuous_when_sg_is_free` is a theorem that it
//! refutes nothing while `sg` is free. `MinaAccumulatorAir` put the STEP-side accumulator check in
//! a circuit; the closing group equation had none. This is the closing equation, in a circuit, at
//! `ipa.rs`'s own combined MSM with `sg_rand_base = −z₁·rand_base` — the coefficient at which the
//! `sg` base drops out of the equation entirely (`MinaWrapClosingAir.the_combined_check_is_
//! constant_in_sg`) and the SRS leg carries `−z₁·s_r` instead.
//!
//! ## ⚑ THE PI LAYOUT IS THE ACCUMULATOR'S, ON PURPOSE
//!
//! A leaf publishes `acc_in ‖ acc_out` — 96 limbs each, contiguous, in that order — which is
//! `MinaAccumulatorAir`'s layout unchanged, so a fold node `cb.connect`s the left child's outgoing
//! 96 limbs to the right child's incoming ones and the two chains compose with ONE adapter.
//! [`crate::mina_accumulator_fold::ACC_PI_COUNT`] is re-used rather than re-declared: a second
//! spelling of 192 is the "two shapes that agree today" failure in its purest form.
//!
//! ## ⚑ THE ENGINE IS DERIVED, NEVER NAMED
//!
//! [`prove_closing_segment`] takes the engine its CHILD is minted at and derives its own wrap
//! engine with [`recursion_layer_over`]; [`prove_closing_fold`] applies it twice — the fixed point,
//! which is `create_recursion_config()`. No config constant is named at a call site. That is the
//! rule that landed 2026-08-07 and took an accumulator leaf from `298.08 s / 117.79 GiB / LDE 2^26`
//! to `21.63 s / 23.23 GiB / LDE 2^23`, and `recursion-verify/tests/tower_config_law.rs` is what
//! proves the measured object is the deployed one.
//!
//! ## ⚠ WHAT THIS DOES NOT ESTABLISH
//!
//! Every residual of `MinaWrapClosingAir`'s docblock, unchanged and not softened here:
//!
//! 1. The scaling `−z₁·s_r·G_r` runs in the EMITTER, not in the AIR. Circuit / emitter / nowhere,
//!    and there is no fourth place.
//! 2. `c·Q` enters as the published `PI[0..95]`. That it is the block's is a CONSUMER refusal.
//! 3. The challenges `u⃗` are not transcript-bound by anything here.
//! 4. P10 — that passing the closing check implies knowing an opening — is untouched.
//! 5. ⚑ **The row is `PastaCurveSound`'s 3 048-column one, NOT `PastaCurveScheduled`'s 481-column
//!    one.** The scheduled row is 6.34× narrower and 7.18× cheaper in committed cells, and the
//!    recursion cost law is linear in COLUMNS — so this leaf is roughly 7× more expensive than it
//!    needs to be. What blocks the port is that the scheduled layout puts one op per row with a
//!    33-phase shift register, so an accumulator crossing complete-additions needs a carry gated by
//!    the phase selector plus a re-run of `AirCrossRow`'s composition over a chain. That is real
//!    work this module does not do, and it is UNDONE WORK, not a theorem of the model.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_recursion::{BatchOnly, RecursionInput, RecursionOutput, Target};

use crate::fold_vk_pin::FoldVkPins;
use crate::gpu_backend::{
    prove_recursion_aggregation_auto_with_expose, prove_recursion_layer_auto_with_expose,
};
use crate::ivc_turn_chain::{expose_claim_instance_index, ir2_leaf_wrap_config};
use crate::mina_accumulator_fold::{ACC_PI_COUNT, IN_PI_LO, POINT_WIDTH};
use crate::plonky3_recursion_impl::recursive::{DreggRecursionConfig, recursion_layer_over};

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// `PastaCurveSound.RCB_WIDTH`.
pub const CLOSING_WIDTH: usize = 3048;
/// `MinaAccumulatorAir.ROUTED_WIDTH`.
pub const CLOSING_ROUTED_WIDTH: usize = CLOSING_WIDTH + 1;

/// Which rung of the closing chain a segment is. The distinction is a DESCRIPTOR, not a flag: an
/// interior segment under the final descriptor would be forced to vanish (and could not), and a
/// final segment under the interior one would not be forced to vanish at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClosingRung {
    /// An interior segment. Publishes its endpoints; says nothing about vanishing.
    Interior,
    /// The LAST segment. Its own AIR forces the terminal accumulator to be the point at infinity.
    Final,
    /// ⚑ The last segment PLUS the routing: the addends are the descriptor's declared
    /// `closingAddends`, in which there is no `sg` slot.
    Routed,
    /// ⚑⚑ The routed rung PLUS the transcript weld — `MinaWrapClosingAir.closingFsAirOn`. It
    /// carries the `delta-absorb-pis` PORT and publishes the squeezed sponge lane, which is the
    /// only reason this rung exists as a separate one: a fold cannot reach an unpublished column.
    Fs,
}

impl ClosingRung {
    /// The descriptor name this rung must resolve to. Checked rather than trusted — a display name
    /// is not a key, and this tree has already shipped three wrong lookups in one day.
    #[must_use]
    pub const fn expected_name(self) -> &'static str {
        match self {
            ClosingRung::Interior => "dregg-mina-wrap-closing-seg::v1",
            ClosingRung::Final => "dregg-mina-wrap-closing-final::v1",
            ClosingRung::Routed => "dregg-mina-wrap-closing-srs::v1",
            ClosingRung::Fs => "dregg-mina-wrap-closing-fs::v1",
        }
    }

    /// The trace width the rung declares.
    #[must_use]
    pub const fn expected_width(self) -> usize {
        match self {
            ClosingRung::Interior | ClosingRung::Final => CLOSING_WIDTH,
            ClosingRung::Routed => CLOSING_ROUTED_WIDTH,
            ClosingRung::Fs => FS_WIDTH,
        }
    }

    /// The public-input arity the rung declares. ⚑ The `-fs` rung is the only one that is not the
    /// accumulator's 192: it APPENDS the 32 squeeze limbs, which is what makes the weld reachable.
    #[must_use]
    pub const fn expected_pi_count(self) -> usize {
        match self {
            ClosingRung::Interior | ClosingRung::Final | ClosingRung::Routed => ACC_PI_COUNT,
            ClosingRung::Fs => FS_PI_COUNT,
        }
    }
}

/// Parse a Lean-emitted closing descriptor and REFUSE anything whose name, width or PI count is not
/// the rung's.
///
/// ⚠ The descriptor JSON is not compiled in. `-srs`'s manifest carries the proof's own `delta`, so
/// there is one descriptor per opening proof and a by-name registry entry would be a lie about what
/// is fixed. The caller supplies the bytes; this refuses the ones that are not the rung's.
///
/// # Errors
/// Returns `Err` if the JSON does not parse, or if the parsed object's name, declared trace width
/// or public-input count is not the rung's.
pub fn closing_descriptor(rung: ClosingRung, json: &str) -> Result<EffectVmDescriptor2, String> {
    let desc =
        parse_vm_descriptor2(json).map_err(|e| format!("closing descriptor parse failed: {e}"))?;
    if desc.name != rung.expected_name() {
        return Err(format!(
            "the {rung:?} rung resolved to `{}`, expected `{}`; refusing a look-alike descriptor",
            desc.name,
            rung.expected_name()
        ));
    }
    if desc.trace_width != rung.expected_width() {
        return Err(format!(
            "closing descriptor `{}` declares width {}, expected {}",
            desc.name,
            desc.trace_width,
            rung.expected_width()
        ));
    }
    if desc.public_input_count != rung.expected_pi_count() {
        return Err(format!(
            "closing descriptor `{}` declares {} PIs, expected {}; refusing an ambiguous endpoint \
             layout",
            desc.name,
            desc.public_input_count,
            rung.expected_pi_count()
        ));
    }
    Ok(desc)
}

/// Prove one closing segment as a recursion leaf, minting at the engine derived from the child's.
///
/// # Errors
/// Propagates every refusal of [`prove_closing_segment_split`].
pub fn prove_closing_segment(
    rung: ClosingRung,
    json: &str,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    prove_closing_segment_split(
        rung,
        json,
        trace,
        public_inputs,
        config,
        &recursion_layer_over(config),
    )
}

/// ⚑ The split form: verify the child at `inner_config`'s knobs and MINT this layer at
/// `wrap_config`'s. `prove_closing_segment` passes `recursion_layer_over(inner)` for the second,
/// which is the rule; a caller that names a config constant here is the thing that rule replaced.
///
/// # Errors
/// Returns `Err` if the public-input vector is not `ACC_PI_COUNT` long, if the descriptor is not
/// the rung's, if the inner IR-v2 proof fails, or if the wrap layer fails.
pub fn prove_closing_segment_split(
    rung: ClosingRung,
    json: &str,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    inner_config: &DreggRecursionConfig,
    wrap_config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let pi_count = rung.expected_pi_count();
    if public_inputs.len() != pi_count {
        return Err(format!(
            "a {rung:?} closing segment carries exactly {pi_count} public inputs, got {}",
            public_inputs.len()
        ));
    }
    let desc = closing_descriptor(rung, json)?;

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        inner_config,
    )?;
    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, public_inputs, inner_config)?;

    let input = RecursionInput::NativeBatchStark {
        airs: &airs,
        proof: &inner,
        common_data: &common,
        table_public_inputs,
    };

    // ⚑ THE CLAIM IS THE CHILD'S OWN FRI-BOUND PI LANES, never a host scalar. `apt[0]` is the main
    // instance and the 192 lanes `acc_in ‖ acc_out` are contiguous by the Lean pin layout.
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>],
                       _vk_cap: &[Target]| {
        let main = apt
            .first()
            .expect("a closing segment has a main instance carrying the descriptor PIs");
        assert!(
            main.len() >= pi_count,
            "main instance must carry all {pi_count} closing PI slots"
        );
        let claim: Vec<Target> = (0..pi_count).map(|k| main[IN_PI_LO + k]).collect();
        cb.expose_as_public_output(&claim);
    };

    prove_recursion_layer_auto_with_expose(&input, wrap_config, Some(&expose))
}

/// ⚑⚑ **THE FOLD, AND THE CARRY IS `cb.connect`, NOT A RE-PIN.**
///
/// The left sub-chain's TERMINAL accumulator is the right sub-chain's INITIAL one, limb for limb,
/// enforced in-circuit on the two children's own `expose_claim` instances. If this were replaced by
/// "both children publish the same PI vector", a prover would pick both sides and the node would
/// close nothing — the lesson `mina_phase2_chain_leaf` already paid for.
///
/// # Errors
/// Returns `Err` if either child's exposed claim is not `ACC_PI_COUNT` lanes, or if the aggregation
/// layer fails.
pub fn fold_closing_segments(
    left: &RecursionOutput<DreggRecursionConfig>,
    right: &RecursionOutput<DreggRecursionConfig>,
    pins: &FoldVkPins,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let left_idx = require_closing_claim(left, "left sub-chain")?;
    let right_idx = require_closing_claim(right, "right sub-chain")?;

    let left_input = left.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right_input = right.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _l_vk: &[Target],
                       _r_vk: &[Target]| {
        let l = left_apt
            .get(left_idx)
            .expect("the left child's exposed claim instance");
        let r = right_apt
            .get(right_idx)
            .expect("the right child's exposed claim instance");

        // ⚑ THE CARRY.
        for k in 0..POINT_WIDTH {
            cb.connect(l[POINT_WIDTH + k], r[k]);
        }

        let mut parent: Vec<Target> = Vec::with_capacity(ACC_PI_COUNT);
        parent.extend_from_slice(&l[..POINT_WIDTH]);
        parent.extend_from_slice(&r[POINT_WIDTH..2 * POINT_WIDTH]);
        debug_assert_eq!(parent.len(), ACC_PI_COUNT);
        cb.expose_as_public_output(&parent);
    };

    prove_recursion_aggregation_auto_with_expose(&left_input, &right_input, config, Some(&expose))
}

fn require_closing_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
    role: &str,
) -> Result<usize, String> {
    require_claim_of_width(output, role, ACC_PI_COUNT)
}

/// The shape gate every fold child goes through: it exposes EXACTLY `want` claim lanes, and it has
/// an `expose_claim` instance to read them from. A child of the wrong width is refused rather than
/// indexed into — reading a 224-lane claim at a 192-lane layout would connect the wrong limbs and
/// still build.
fn require_claim_of_width(
    output: &RecursionOutput<DreggRecursionConfig>,
    role: &str,
    want: usize,
) -> Result<usize, String> {
    let lanes = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map_or(0, |e| e.public_values.len());
    if lanes != want {
        return Err(format!(
            "the {role} exposes {lanes} claim lane(s), expected exactly {want}; refusing an \
             ambiguous closing-chain layout"
        ));
    }
    expose_claim_instance_index(&output.0).ok_or_else(|| {
        format!("the {role} carries no `expose_claim` instance despite its claimed layout")
    })
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// ⚑⚑⚑ THE `delta-absorb-pis` PORT'S COVER.  KIND: **SEAM** — in-circuit `cb.connect`s inside a
// recursion aggregation node.  NOT an AIR constraint of `dregg-mina-wrap-closing-fs::v1` and NOT a
// host comparison.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// `MinaWrapClosingAir.FS_WIDTH` — the routed row, the bind guard, nine program lanes, the squeeze.
pub const FS_WIDTH: usize = 3091;
/// `MinaWrapClosingAir.SK` — eight-bit limbs per Pasta `Fp` element.
pub const SK: usize = 32;
/// `MinaWrapClosingAir.FS_PI_COUNT` — `acc_in(96) ‖ acc_out(96) ‖ squeeze(32)`.
pub const FS_PI_COUNT: usize = ACC_PI_COUNT + SK;
/// `MinaWrapClosingAir.FS_TROUT_PI 0` — where the squeezed sponge lane is published. APPENDED, so
/// no accumulator slot moved.
pub const FS_PI_TROUT_LO: usize = ACC_PI_COUNT;

/// `MinaWrapVerifierSpongeFp.SPONGE_PI_COUNT` — `dregg-pasta-fp-absorb::v1`'s whole public surface.
pub const ABSORB_PI_COUNT: usize = 6 * SK;
/// The absorb program's INCOMING sponge state: three `Fp` lanes, `96` limbs.
pub const ABSORB_PI_IN_LO: usize = 0;
/// Width of that block.
pub const ABSORB_PI_IN_WIDTH: usize = 3 * SK;
/// The two ABSORBED elements — for this weld, `delta.x ‖ delta.y`.
pub const ABSORB_PI_ABSORBED_LO: usize = ABSORB_PI_IN_WIDTH;
/// Width of that block.
pub const ABSORB_PI_ABSORBED_WIDTH: usize = 2 * SK;
/// The SQUEEZED lane the permutation lands on.
pub const ABSORB_PI_OUT_LO: usize = ABSORB_PI_ABSORBED_LO + ABSORB_PI_ABSORBED_WIDTH;
/// Width of that block.
pub const ABSORB_PI_OUT_WIDTH: usize = SK;

/// ⚑ **THE WELD IS WHOLE-VECTOR, ASSERTED AT COMPILE TIME.** The bind's commitment IS the absorb
/// program's public-input vector (`MinaWrapClosingAir.
/// the_weld_commit_is_the_absorb_programs_public_input_vector`), so the three blocks below must
/// exactly tile it. A future re-block that leaves a limb uncovered fails to COMPILE rather than
/// silently connecting two thirds of the claim — the shape of refusal 10's wraplink mistake, made
/// unrepresentable.
const _: () = assert!(ABSORB_PI_OUT_LO + ABSORB_PI_OUT_WIDTH == ABSORB_PI_COUNT);
const _: () = assert!(FS_PI_TROUT_LO + ABSORB_PI_OUT_WIDTH == FS_PI_COUNT);

/// The two CONSTANT halves of the `delta-absorb-pis` commitment, read out of the `-fs` descriptor's
/// own emitted bytes. Nothing here is transcribed: [`delta_absorb_pins`] recovers both from the
/// descriptor the leaf is proven against.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeltaAbsorbPins {
    /// The 96 limbs of `TR_IN` — the incoming sponge state, which the bind declares as descriptor
    /// CONSTANTS (`MinaWrapClosingAir.trInLanes`).
    pub tr_in: Vec<u32>,
    /// The 64 limbs of the absorbed pair `delta.x ‖ delta.y`. Trace COLUMNS in the descriptor, but
    /// `.first`-pinned to constants by `deltaPinLegs`, which is where these are read from.
    pub delta: Vec<u32>,
}

/// ⚑ **RECOVER THE BIND'S CONSTANT LANES FROM THE DESCRIPTOR'S OWN BYTES.**
///
/// * `TR_IN` is read straight off the commitment's first 96 lanes, which the bind declares as
///   `Expr::Const`.
/// * The absorbed pair's 64 lanes are `Expr::Var(ADD_X + j)` — trace columns, so a fold cannot
///   reach them and they are not read from the commitment. They are recovered from the `.first`
///   BOUNDARY constraints `deltaPinLegs` emits (`col − c ≡ 0` on row 0), which is the only place
///   the descriptor states what those cells must be.
///
/// A commitment lane of the wrong SHAPE (a var where a const is declared, or a var with no `.first`
/// pin) is refused rather than defaulted: a missing pin would make the connect below tie the absorb
/// child to a value nobody fixed.
///
/// # Errors
/// Returns `Err` unless the descriptor carries exactly one `proof_bind` whose commitment is
/// [`ABSORB_PI_COUNT`] lanes shaped `const×96 ‖ var×64 ‖ var×32`, and every one of the 64 var lanes
/// has a `.first` boundary pin.
pub fn delta_absorb_pins(desc: &EffectVmDescriptor2) -> Result<DeltaAbsorbPins, String> {
    use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

    let binds: Vec<&dregg_circuit::descriptor_ir2::ProofBindSpec> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            dregg_circuit::descriptor_ir2::VmConstraint2::ProofBind(p) => Some(p),
            _ => None,
        })
        .filter(|p| p.commit.len() == ABSORB_PI_COUNT)
        .collect();
    if binds.len() != 1 {
        return Err(format!(
            "`{}` declares {} proof_bind(s) committing {ABSORB_PI_COUNT} lanes; the delta-absorb \
             weld is identified by that width and this consumer refuses to pick one of several",
            desc.name,
            binds.len()
        ));
    }
    let bind = binds[0];

    // ── the incoming sponge state: DECLARED CONSTANTS.
    let mut tr_in = Vec::with_capacity(ABSORB_PI_IN_WIDTH);
    for (j, e) in bind.commit[ABSORB_PI_IN_LO..][..ABSORB_PI_IN_WIDTH]
        .iter()
        .enumerate()
    {
        match e {
            LeanExpr::Const(v) => tr_in.push(field_limb(*v, "TR_IN", j)?),
            other => {
                return Err(format!(
                    "delta-absorb commit lane {j} of the incoming state is {other:?}, not a \
                     constant: with a FREE incoming state the seam is vacuous and not weakly so — \
                     `perm` is a permutation, so a prover picks the state that lands anywhere"
                ));
            }
        }
    }

    // ── the absorbed pair: trace columns, recovered from their `.first` pins.
    let mut want_cols = Vec::with_capacity(ABSORB_PI_ABSORBED_WIDTH);
    for (j, e) in bind.commit[ABSORB_PI_ABSORBED_LO..][..ABSORB_PI_ABSORBED_WIDTH]
        .iter()
        .enumerate()
    {
        match e {
            LeanExpr::Var(c) => want_cols.push(*c),
            other => {
                return Err(format!(
                    "delta-absorb commit lane {j} of the absorbed pair is {other:?}, not a trace \
                     column: this consumer reads the pair off `deltaPinLegs` and has nowhere to \
                     read a lane that names no column"
                ));
            }
        }
    }

    let mut delta = Vec::with_capacity(ABSORB_PI_ABSORBED_WIDTH);
    for (j, col) in want_cols.iter().enumerate() {
        let pinned = desc.constraints.iter().find_map(|c| match c {
            dregg_circuit::descriptor_ir2::VmConstraint2::Base(VmConstraint::Boundary {
                row: VmRow::First,
                body,
            }) => first_row_pin_value(body, *col),
            _ => None,
        });
        match pinned {
            Some(v) => delta.push(field_limb(v, "delta", j)?),
            None => {
                return Err(format!(
                    "absorbed-pair limb {j} is column {col}, which carries NO `.first` boundary \
                     pin: the descriptor does not say what that cell is, so a connect against it \
                     would tie the absorb child to a value the prover chose"
                ));
            }
        }
    }

    Ok(DeltaAbsorbPins { tr_in, delta })
}

/// `deltaPinLeg` lowers to a `.first` boundary whose body is `var(col) + const(−c)`. Recover `c`,
/// and only for the column asked about — a pin on some other column says nothing about this one.
fn first_row_pin_value(
    body: &dregg_circuit::lean_descriptor_air::LeanExpr,
    col: usize,
) -> Option<i64> {
    use dregg_circuit::lean_descriptor_air::LeanExpr;
    match body {
        LeanExpr::Add(l, r) => match (&**l, &**r) {
            (LeanExpr::Var(c), LeanExpr::Const(k)) if *c == col => Some(-*k),
            (LeanExpr::Const(k), LeanExpr::Var(c)) if *c == col => Some(-*k),
            _ => None,
        },
        LeanExpr::Var(c) if *c == col => Some(0),
        _ => None,
    }
}

/// A descriptor constant is an `i64`; a limb of a claim is a canonical BabyBear `u32`. Refuse
/// anything that is not one rather than wrapping it — a silently reduced constant is the
/// `parse_int_field` defect this tree already carries once.
fn field_limb(v: i64, what: &str, j: usize) -> Result<u32, String> {
    u32::try_from(v)
        .ok()
        .filter(|x| *x < 0x7800_0001)
        .ok_or_else(|| format!("delta-absorb {what} limb {j} is {v}, not a canonical BabyBear value"))
}

/// ⚑⚑⚑ **THE COVER OF `dregg-mina-wrap-closing-fs::v1`'s `delta-absorb-pis` PORT — and it
/// COMPARES, lane for lane, all 192.**
///
/// # What the port owes, and what this pays
///
/// `MinaWrapClosingAir.deltaAbsorbBindLeg` declares a commitment
/// `TR_IN(96) ‖ delta.x ‖ delta.y(64) ‖ squeeze(32)` against `dregg-pasta-fp-absorb::v1`'s
/// fingerprint, and — being a `.port` — emits **no polynomial over those lanes**
/// (`CommitBinding::Port`). Until this function existed the declaration named an absorb program and
/// nothing anywhere compared its public inputs to the lanes the bind declared: the `-fs` leaf could
/// publish any squeeze at all and no object in the tree noticed.
///
/// This is the comparison, as **192 in-circuit `cb.connect`s** in a recursion aggregation node that
/// verifies both children:
///
/// * **96** — the absorb child's incoming sponge state is welded to the `-fs` descriptor's OWN
///   declared `TR_IN` constants. ⚑ Load-bearing exactly as `check_body_chain_binding`'s refusal
///   16c: `perm` is a permutation, so against a free incoming state a prover picks the state whose
///   image is whatever it already published, and the weld would refuse nothing.
/// * **64** — the absorbed pair is welded to the constants `deltaPinLegs` `.first`-pins the `ADD_X`
///   / `ADD_Y` cells to. So the pair the sponge absorbed is the pair the RCB row folded, not a
///   sibling copy of it.
/// * **32** — the `-fs` leaf's PUBLISHED squeeze (`PI 192..223`) is welded to the absorb child's
///   squeezed lane. This is the half a fold could not reach before the squeeze was published.
///
/// Both sides are read from each child's own FRI-bound `expose_claim` lanes, never from a scalar
/// the aggregation circuit invents — the distinction `mina_phase2_chain_leaf` paid for.
///
/// # ⚠ SAY THE KIND OUT LOUD: THIS IS A **SEAM**, NOT AN AIR CONSTRAINT
///
/// A `cb.connect` emits nothing into `dregg-mina-wrap-closing-fs::v1`. It is a constraint of the
/// AGGREGATION circuit — a prover whose absorb child disagrees has no satisfying assignment, so
/// there is no parent proof — and it rides the same undischarged FRI/STARK floor every fold in this
/// tree does. Do not read "the port is covered" as "the descriptor forces it".
///
/// ⚠ And it does not make the `-fs` leaf's `delta` the block's: that the pinned `delta` is the
/// opening proof's own is residual (2) of this module's header, untouched here.
///
/// # Errors
/// Returns `Err` if either claim is the wrong width or the pins are not the declared block sizes.
pub fn connect_delta_absorb_pis(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    fs_claim: &[Target],
    absorb_claim: &[Target],
    pins: &DeltaAbsorbPins,
) -> Result<(), String> {
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_field::PrimeCharacteristicRing;

    if fs_claim.len() != FS_PI_COUNT {
        return Err(format!(
            "the `-fs` child exposes {} claim lanes, expected {FS_PI_COUNT}",
            fs_claim.len()
        ));
    }
    if absorb_claim.len() != ABSORB_PI_COUNT {
        return Err(format!(
            "the absorb child exposes {} claim lanes, expected {ABSORB_PI_COUNT}",
            absorb_claim.len()
        ));
    }
    if pins.tr_in.len() != ABSORB_PI_IN_WIDTH || pins.delta.len() != ABSORB_PI_ABSORBED_WIDTH {
        return Err(format!(
            "the delta-absorb pins are {}/{} limbs; the bind declares \
             {ABSORB_PI_IN_WIDTH}/{ABSORB_PI_ABSORBED_WIDTH}",
            pins.tr_in.len(),
            pins.delta.len()
        ));
    }

    // ── 96: the incoming sponge state IS the descriptor's declared `TR_IN`.
    for (j, v) in pins.tr_in.iter().enumerate() {
        let k = cb.define_const(RecursionChallenge::from(P3BabyBear::from_u64(u64::from(*v))));
        cb.connect(absorb_claim[ABSORB_PI_IN_LO + j], k);
    }
    // ── 64: the absorbed pair IS the chain's own `.first`-pinned addend cells.
    for (j, v) in pins.delta.iter().enumerate() {
        let k = cb.define_const(RecursionChallenge::from(P3BabyBear::from_u64(u64::from(*v))));
        cb.connect(absorb_claim[ABSORB_PI_ABSORBED_LO + j], k);
    }
    // ── 32: the published squeeze IS the absorb program's own output.
    for j in 0..ABSORB_PI_OUT_WIDTH {
        cb.connect(
            fs_claim[FS_PI_TROUT_LO + j],
            absorb_claim[ABSORB_PI_OUT_LO + j],
        );
    }
    Ok(())
}

/// ⚑⚑ **THE FOLD THAT RUNS THE COVER.** Verifies the `-fs` closing leaf and the absorb leaf
/// in-circuit, applies [`connect_delta_absorb_pis`], and republishes the `-fs` leaf's accumulator
/// endpoints — the squeeze itself is deliberately NOT re-published, because it is now an internal
/// wire of the aggregation and a root that re-published it would read as though the two halves were
/// still separately checkable. Same discipline as `mina_wrap_finalize_fold::fold_endo_into_finalize`.
///
/// ⚠ `pins` fixes each child's preprocessed commitment in-circuit; without it the two claim-width
/// checks are the only gate and a same-shape/different-constants child passes them.
///
/// # Errors
/// Returns `Err` if either child's exposed claim is the wrong width, if the descriptor's pins
/// cannot be recovered, or if the aggregation layer fails.
pub fn fold_delta_absorb_into_closing(
    fs_leaf: &RecursionOutput<DreggRecursionConfig>,
    absorb_leaf: &RecursionOutput<DreggRecursionConfig>,
    fs_desc: &EffectVmDescriptor2,
    vk_pins: &FoldVkPins,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let fs_idx = require_claim_of_width(fs_leaf, "`-fs` closing leaf", FS_PI_COUNT)?;
    let absorb_idx = require_claim_of_width(absorb_leaf, "absorb leaf", ABSORB_PI_COUNT)?;
    let pins = delta_absorb_pins(fs_desc)?;

    let left = fs_leaf.into_recursion_input_pinned::<BatchOnly>(vk_pins.left.clone());
    let right = absorb_leaf.into_recursion_input_pinned::<BatchOnly>(vk_pins.right.clone());

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _l_vk: &[Target],
                       _r_vk: &[Target]| {
        let f = left_apt
            .get(fs_idx)
            .expect("the `-fs` child's exposed claim instance");
        let a = right_apt
            .get(absorb_idx)
            .expect("the absorb child's exposed claim instance");
        connect_delta_absorb_pis(cb, f, a, &pins).expect("the delta-absorb cover wires");
        cb.expose_as_public_output(&f[..ACC_PI_COUNT]);
    };

    prove_recursion_aggregation_auto_with_expose(&left, &right, config, Some(&expose))
}

/// The engine a closing LEAF's inner IR-v2 batch proof is minted at.
#[must_use]
pub fn closing_inner_config() -> DreggRecursionConfig {
    ir2_leaf_wrap_config()
}

/// ⚑ Fold a whole closing chain left-to-right. The last segment is the one whose own AIR forces the
/// terminal accumulator to vanish; everything before it is `Interior`.
///
/// # Errors
/// Returns `Err` on an empty chain, or on any leaf or fold refusal.
pub fn prove_closing_fold(
    segments: &[(ClosingRung, &'static str, Vec<Vec<BabyBear>>, Vec<BabyBear>)],
    config: &DreggRecursionConfig,
    mut progress: impl FnMut(usize, &str),
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if segments.is_empty() {
        return Err("a closing chain has at least one segment".to_string());
    }
    // ⚑ THE FOLD ENGINE, DERIVED. A leaf wrap emits at `recursion_layer_over(config)`'s mint knobs,
    // so a node ABOVE a leaf verifies at those and mints at one more layer — the fixed point.
    let fold_config = recursion_layer_over(&recursion_layer_over(config));

    let mut acc: Option<RecursionOutput<DreggRecursionConfig>> = None;
    for (i, (rung, json, trace, pis)) in segments.iter().enumerate() {
        progress(i, "leaf");
        let leaf = prove_closing_segment(*rung, json, trace, pis, config)?;
        acc = Some(match acc {
            None => leaf,
            Some(prev) => {
                progress(i, "fold");
                let pins = FoldVkPins::tracked(&prev, &leaf)?;
                fold_closing_segments(&prev, &leaf, &pins, &fold_config)?
            }
        });
    }
    Ok(acc.expect("the chain is non-empty"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ⚑ The closing leaf's PI layout IS the accumulator's, so the two chains fold with one
    /// adapter. A constant checked against its own definition is decoration; this is the other
    /// kind — it is the reason `mina_accumulator_fold`'s constants are imported rather than
    /// respelled.
    #[test]
    fn the_closing_claim_layout_is_the_accumulators() {
        assert_eq!(IN_PI_LO, 0);
        assert_eq!(POINT_WIDTH, 96);
        assert_eq!(ACC_PI_COUNT, 192);
        assert_eq!(CLOSING_ROUTED_WIDTH, CLOSING_WIDTH + 1);
    }

    /// A display name is not a key: every rung names a distinct descriptor and a distinct width.
    #[test]
    fn the_three_rungs_name_three_objects() {
        let names = [
            ClosingRung::Interior.expected_name(),
            ClosingRung::Final.expected_name(),
            ClosingRung::Routed.expected_name(),
        ];
        let mut sorted = names;
        sorted.sort_unstable();
        sorted.iter().zip(sorted.iter().skip(1)).for_each(|(a, b)| {
            assert_ne!(a, b, "two rungs share a descriptor name");
        });
        assert_eq!(ClosingRung::Interior.expected_width(), CLOSING_WIDTH);
        assert_eq!(ClosingRung::Routed.expected_width(), CLOSING_ROUTED_WIDTH);
    }

    // ────────────────────────────────────────────────────────────────────────────────────────
    // ⚑⚑ BOTH POLARITIES ON THE `delta-absorb-pis` COVER, at the level where it is decidable in
    // milliseconds: the connect set is built into a bare circuit whose two children's claim lanes
    // are public inputs, and driven with honest and forged values. `cb.connect` is witness-slot
    // ALIASING, so a broken weld is a witness that DOES NOT EXIST — not a soft constraint a
    // clever prover satisfies another way.
    //
    // ⚠ SAY WHAT THIS DOES AND DOES NOT SETTLE, and do not name a test that does not exist. It
    // settles that the 192 connects BITE and which lanes they name — on the SAME constraint set
    // `fold_delta_absorb_into_closing` installs, since both call `connect_delta_absorb_pis` and
    // nothing else authors those constraints. It does NOT settle that a full deployed fold of a
    // forged `-fs`/absorb pair fails end to end: **that has NOT been run**, because a 3 091-column
    // leaf wrap plus a 469-column absorb leaf is minutes and tens of GiB, and the honest pair of
    // traces for it does not exist in this tree yet. Same split, and the same wording, as
    // `ivc_turn_chain`'s board-window canaries, which say so about their own deployed leg.
    // ────────────────────────────────────────────────────────────────────────────────────────

    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_circuit::CircuitBuilder;
    use p3_field::PrimeCharacteristicRing;

    const FS_JSON: &str = include_str!("../../circuit/tests/fixtures/mina-wrap-closing-fs.json");

    /// Build a bare circuit carrying the two children's exposed claims as public inputs, wire ONLY
    /// the delta-absorb cover between them, and try to drive it. `Ok` iff a witness exists.
    fn run_cover(
        fs_claim: &[u32],
        absorb_claim: &[u32],
        pins: &DeltaAbsorbPins,
    ) -> Result<(), p3_circuit::errors::CircuitError> {
        let mut cb: CircuitBuilder<RecursionChallenge> = CircuitBuilder::new();
        let f: Vec<Target> = cb.alloc_public_inputs(fs_claim.len(), "fs_claim");
        let a: Vec<Target> = cb.alloc_public_inputs(absorb_claim.len(), "absorb_claim");
        connect_delta_absorb_pis(&mut cb, &f, &a, pins).expect("the cover wires");
        let circuit = cb.build().expect("the cover-only circuit builds");
        let mut runner = circuit.runner();
        let pubs: Vec<RecursionChallenge> = fs_claim
            .iter()
            .chain(absorb_claim.iter())
            .map(|v| RecursionChallenge::from(P3BabyBear::from_u64(u64::from(*v))))
            .collect();
        runner.set_public_inputs(&pubs)?;
        runner.run().map(|_| ())
    }

    fn fs_descriptor() -> EffectVmDescriptor2 {
        closing_descriptor(ClosingRung::Fs, FS_JSON).expect("the `-fs` fixture is the Fs rung")
    }

    /// An honest pair, built FROM THE DESCRIPTOR'S OWN PINS so the fixture and the claim cannot
    /// drift: the absorb child's incoming state and absorbed pair are the descriptor's constants,
    /// its squeeze is an arbitrary but SHARED value, and the `-fs` child publishes that same
    /// squeeze at `FS_PI_TROUT_LO`.
    fn honest_pair(pins: &DeltaAbsorbPins, squeeze: &[u32]) -> (Vec<u32>, Vec<u32>) {
        let mut fs = vec![0u32; FS_PI_COUNT];
        // the accumulator half is untouched by this weld; give it distinct non-zero values so a
        // connect that wandered into it would be visible rather than accidentally satisfied.
        for (k, slot) in fs.iter_mut().take(ACC_PI_COUNT).enumerate() {
            *slot = 1_000 + k as u32;
        }
        fs[FS_PI_TROUT_LO..].copy_from_slice(squeeze);

        let mut ab = vec![0u32; ABSORB_PI_COUNT];
        ab[ABSORB_PI_IN_LO..][..ABSORB_PI_IN_WIDTH].copy_from_slice(&pins.tr_in);
        ab[ABSORB_PI_ABSORBED_LO..][..ABSORB_PI_ABSORBED_WIDTH].copy_from_slice(&pins.delta);
        ab[ABSORB_PI_OUT_LO..][..ABSORB_PI_OUT_WIDTH].copy_from_slice(squeeze);
        (fs, ab)
    }

    /// The 32-limb squeeze the honest pole shares. Every limb non-zero so that a forgery which
    /// zeroes one is a move of a REAL value, and every limb inside the declared 8-bit width so
    /// nothing is refused for being out of range instead of for disagreeing.
    fn squeeze_lanes() -> Vec<u32> {
        (0..ABSORB_PI_OUT_WIDTH).map(|j| 1 + (j as u32 % 251)).collect()
    }

    /// ⚑ **THE PINS ARE READ, NOT INVENTED — and they are not all zero.** If
    /// [`delta_absorb_pins`] silently returned zeros, every forgery below would still be refused
    /// and the suite would look identical while measuring nothing.
    #[test]
    fn the_cover_pins_are_recovered_from_the_descriptors_own_bytes() {
        let pins = delta_absorb_pins(&fs_descriptor()).expect("the `-fs` fixture declares its pins");
        assert_eq!(pins.tr_in.len(), ABSORB_PI_IN_WIDTH);
        assert_eq!(pins.delta.len(), ABSORB_PI_ABSORBED_WIDTH);
        assert!(
            pins.tr_in.iter().any(|v| *v != 0),
            "an all-zero `TR_IN` would make refusal-by-salt vacuous"
        );
        assert!(
            pins.delta.iter().any(|v| *v != 0),
            "an all-zero absorbed pair would make the addend weld vacuous"
        );
    }

    /// **THE HONEST POLE.** A `-fs` claim publishing the squeeze the absorb child produced, at the
    /// descriptor's own incoming state and addend pair, HAS a witness. Non-vacuous: the two claims
    /// are DISTINCT public inputs — distinct expressions, distinct witness slots until the connect
    /// unions them — so `connect`'s `a == b` early-out never fires and all 192 are real unions.
    #[test]
    fn an_honest_delta_absorb_pair_has_a_witness() {
        let pins = delta_absorb_pins(&fs_descriptor()).expect("pins");
        let sq = squeeze_lanes();
        let (fs, ab) = honest_pair(&pins, &sq);
        run_cover(&fs, &ab, &pins).expect("the honest cover must be satisfiable");
    }

    /// ⚑⚑ **THE LOAD-BEARING NEGATIVE — every one of the 192 lanes is load-bearing.** Each block is
    /// forged in turn, ONE limb at a time, by a move that is non-zero and stays inside the declared
    /// eight-bit width, and each is a witness conflict.
    ///
    /// This is the forgery the port names: a `-fs` leaf whose published squeeze is not the absorb
    /// program's output, an absorb child that started from a sponge state the `-fs` descriptor did
    /// not declare, and one that absorbed a pair the RCB row did not fold.
    #[test]
    fn every_forged_delta_absorb_lane_is_a_witness_conflict() {
        let pins = delta_absorb_pins(&fs_descriptor()).expect("pins");
        let sq = squeeze_lanes();

        // (i) the published squeeze is not the absorb child's output.
        for j in 0..ABSORB_PI_OUT_WIDTH {
            let (mut fs, ab) = honest_pair(&pins, &sq);
            let before = fs[FS_PI_TROUT_LO + j];
            fs[FS_PI_TROUT_LO + j] = before ^ 1;
            assert_ne!(fs[FS_PI_TROUT_LO + j], before, "the mutation must move a value");
            assert!(
                run_cover(&fs, &ab, &pins).is_err(),
                "a `-fs` squeeze limb {j} the absorb child did not produce must be UNSAT"
            );
        }
        // (ii) the incoming sponge state is not the descriptor's declared `TR_IN`.
        for j in [0usize, 17, 64, 95] {
            let (fs, mut ab) = honest_pair(&pins, &sq);
            let before = ab[ABSORB_PI_IN_LO + j];
            ab[ABSORB_PI_IN_LO + j] = before ^ 1;
            assert_ne!(ab[ABSORB_PI_IN_LO + j], before);
            assert!(
                run_cover(&fs, &ab, &pins).is_err(),
                "an incoming-state limb {j} the `-fs` descriptor did not declare must be UNSAT"
            );
        }
        // (iii) the absorbed pair is not the chain's own `.first`-pinned addend cells.
        for j in [0usize, 31, 32, 63] {
            let (fs, mut ab) = honest_pair(&pins, &sq);
            let before = ab[ABSORB_PI_ABSORBED_LO + j];
            ab[ABSORB_PI_ABSORBED_LO + j] = before ^ 1;
            assert_ne!(ab[ABSORB_PI_ABSORBED_LO + j], before);
            assert!(
                run_cover(&fs, &ab, &pins).is_err(),
                "an absorbed-pair limb {j} the RCB row did not fold must be UNSAT"
            );
        }
    }

    /// ⚑ **THE FIXTURE ACTUALLY CARRIES THE PORT.** Both `-fs` fixtures carried the RETIRED
    /// `"bound":null` until 2026-08-10 and `parse_vm_descriptor2` refuses that by name, so this
    /// resolves the port cover the registry gate counts.
    #[test]
    fn the_fs_descriptor_declares_the_delta_absorb_port() {
        let d = fs_descriptor();
        let covers = d
            .constraints
            .iter()
            .filter_map(|c| match c {
                dregg_circuit::descriptor_ir2::VmConstraint2::ProofBind(p) => p.bound.cover(),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(covers.len(), 1, "the `-fs` descriptor declares one port");
        assert_eq!(covers[0].port, "delta-absorb-pis");
        assert_eq!(
            covers[0].seam,
            "dregg_circuit_prove::mina_wrap_closing_fold::connect_delta_absorb_pis"
        );
    }

    /// The resolver refuses a look-alike rather than proving the wrong claim.
    #[test]
    fn a_wrong_named_descriptor_is_refused() {
        let json = include_str!("../../circuit/tests/fixtures/mina-wrap-closing-final.json");
        assert!(closing_descriptor(ClosingRung::Final, json).is_ok());
        let err = closing_descriptor(ClosingRung::Routed, json)
            .expect_err("the final descriptor is not the routed rung");
        assert!(err.contains("refusing a look-alike"), "{err}");
    }
}
