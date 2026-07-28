//! **THE SOVEREIGN CARRIER CLAIM SLOTS ARE A PROPERTY OF THE SOVEREIGN MEMBER, NOT OF "a wide
//! leg" — AND THE PiBinding CHECK IS NOT WHAT SEPARATES THEM.** Both poles, read straight off the
//! committed staged WIDE registry — no proving, milliseconds.
//!
//! ## Why this tooth exists
//!
//! `ivc_turn_chain::mint_rotated_turn_leaf`'s `CarrierWitness::Sovereign` arm opens with
//! `carrier_claim_pins_admitted(desc, pis, SOVEREIGN_KEY_COMMIT_PI_LO, SOVEREIGN_KEY_CLAIM_LEN,
//! "sovereign", None)`. That gate is private, it is the FIRST thing the arm does, and a leg it
//! refuses never reaches a prover. Its three conditions are reproduced here against the committed
//! descriptors, so *"which leg shapes can carry a sovereign carrier witness?"* has a millisecond
//! answer instead of a several-minute fold.
//!
//! Written 2026-07-28 while retiring `dregg_sdk::carrier_witness_attach`. That module projected
//! turn-build material into a `CarrierWitness` and attached it to a `RotatedParticipantLeg`; its
//! own test header called the result *"the ARM-ADMISSIBLE honest shape"*. It was not admissible.
//! The only leg the SDK could reach is what `dregg_turn_prover::rotation_witness::
//! mint_rotated_participant_leg` mints for a value cohort — `transferVmDescriptor2R24`, **68
//! public inputs** — and the deployed fold answered:
//!
//! ```text
//! TurnProofInvalid { index: 0, reason: "carrier 'sovereign': the claim slice [58..62) overlaps
//!   the 16 wide anchor PIs of the 68-PI leg — the leg does not publish the carrier claim slots
//!   (the STEP-3 octet-pin descriptor rides the big-bang regen); refusing to fold (fail-closed)" }
//! ```
//!
//! ## ⚑ The load-bearing measurement: the pin check would have let it through
//!
//! The obvious reading of that refusal is "the transfer member does not publish teeth there".
//! **It does.** Measured on the committed descriptor: `transferVmDescriptor2R24` carries a real
//! `PiBinding` at every one of PIs 58, 59, 60, 61 — because on a 68-PI leg the last 16 PIs
//! (`52..68`) ARE the two 8-felt wide state anchors, so the sovereign claim slice lands on
//! **before-anchor lanes 6-7 and after-anchor lanes 0-1**.
//!
//! So condition 3 (`a genuine PiBinding at every claim slot`) is satisfied by a value-cohort leg,
//! and the ONLY thing refusing it is condition 2, the claim/anchor overlap arithmetic. Had the
//! gate been written as the pin check alone, a sovereign authority tuple would have been folded
//! against four lanes of the leg's own state commitment read as a key commitment. The deployed
//! sovereign member is sized to clear this exactly: 78 PIs = `claim.end (62) + 16`, with the
//! teeth at columns 93..96 — nowhere near its anchor columns.
//!
//! ## The anti-vacuity pole is load-bearing too
//!
//! A test that only asserts "the transfer member is refused" passes just as happily if
//! `SOVEREIGN_KEY_COMMIT_PI_LO` drifts off the end of every descriptor in the tree, or if the
//! `PiBinding` scan stops matching anything. So the ADMIT pole runs in the same process: the
//! deployed sovereign member must satisfy all three conditions, with a genuine `PiBinding` found
//! at every one of the four claim slots.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, parse_vm_descriptor2};
use dregg_circuit::effect_vm::trace_rotated::WIDE_PI_COUNT;
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::lean_descriptor_air::VmConstraint;
use dregg_circuit_prove::ivc_turn_chain::{SEG_ANCHOR_WIDTH, SOVEREIGN_KEY_COMMIT_PI_LO};
use dregg_circuit_prove::sovereign_leaf_adapter::SOVEREIGN_KEY_CLAIM_LEN;

/// The deployed member `mint_rotated_participant_leg` dispatches for a single-`Transfer` value
/// cohort — the ONLY leg shape the retired SDK attach could ever have been handed.
const TRANSFER_MEMBER: &str = "transferVmDescriptor2R24";
/// The deployed member that carries the `SOVEREIGN_WITNESS_KEY_COMMIT` teeth rider.
const SOVEREIGN_MEMBER: &str = "makeSovereignVmDescriptor2R24";

fn member(key: &str) -> EffectVmDescriptor2 {
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(key) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("'{key}' has no row in the committed staged WIDE registry"));
    parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("'{key}' does not parse: {e}"))
}

/// The claim slots the sovereign arm demands, as a half-open range.
fn claim_range() -> std::ops::Range<usize> {
    SOVEREIGN_KEY_COMMIT_PI_LO..SOVEREIGN_KEY_COMMIT_PI_LO + SOVEREIGN_KEY_CLAIM_LEN
}

/// `true` iff `desc` binds public input `pi` to a real trace tooth.
fn pins(desc: &EffectVmDescriptor2, pi: usize) -> bool {
    desc.constraints.iter().any(|c| {
        matches!(
            c,
            VmConstraint2::Base(VmConstraint::PiBinding { pi_index, .. }) if *pi_index == pi
        )
    })
}

/// The three conditions `carrier_claim_pins_admitted` applies, in its order, reproduced against a
/// committed descriptor. `Ok(())` iff the descriptor could carry a sovereign carrier witness.
fn sovereign_claim_admissible(desc: &EffectVmDescriptor2) -> Result<(), String> {
    let n = desc.public_input_count;
    let claim = claim_range();
    if n < WIDE_PI_COUNT {
        return Err(format!("not a WIDE leaf ({n} PIs < {WIDE_PI_COUNT})"));
    }
    if claim.end + 2 * SEG_ANCHOR_WIDTH > n {
        return Err(format!(
            "the claim slice [{}..{}) overlaps the {} wide anchor PIs of the {n}-PI descriptor",
            claim.start,
            claim.end,
            2 * SEG_ANCHOR_WIDTH
        ));
    }
    for pi in claim {
        if !pins(desc, pi) {
            return Err(format!("no PiBinding for claim PI {pi}"));
        }
    }
    Ok(())
}

/// **ADMIT POLE (the anti-vacuity guard).** The deployed sovereign member satisfies all three
/// conditions, with a real `PiBinding` at every claim slot, and its claim slots sit CLEAR of its
/// own wide anchors. If this ever fails, the refusal pole below is green for the wrong reason and
/// must not be believed.
#[test]
fn deployed_sovereign_member_publishes_the_carrier_claim_slots() {
    let desc = member(SOVEREIGN_MEMBER);
    let claim = claim_range();
    let n = desc.public_input_count;

    assert!(
        n >= claim.end + 2 * SEG_ANCHOR_WIDTH,
        "{SOVEREIGN_MEMBER} publishes {n} PIs, too few to hold the sovereign claim slice \
         [{}..{}) clear of the {} wide anchor PIs — the carrier arm could admit NO leg and the \
         refusal pole would be vacuous",
        claim.start,
        claim.end,
        2 * SEG_ANCHOR_WIDTH,
    );

    // The claim slots must be teeth of their OWN, not lanes of the state anchors — the exact
    // confusion the refusal pole below shows a value-cohort leg falling into. The anchors are the
    // last 16 PIs; the claim must end at or before where they begin.
    assert!(
        claim.end <= n - 2 * SEG_ANCHOR_WIDTH,
        "{SOVEREIGN_MEMBER}'s claim slice [{}..{}) reaches into its own wide anchors \
         [{}..{n}) — the teeth would BE anchor lanes",
        claim.start,
        claim.end,
        n - 2 * SEG_ANCHOR_WIDTH,
    );

    for pi in claim.clone() {
        assert!(
            pins(&desc, pi),
            "{SOVEREIGN_MEMBER} carries NO PiBinding for sovereign claim PI {pi} — the teeth \
             rider is gone from the committed descriptor and the sovereign carrier arm can \
             admit nothing"
        );
    }

    assert_eq!(
        sovereign_claim_admissible(&desc),
        Ok(()),
        "the deployed sovereign member must be ADMISSIBLE on the sovereign carrier arm"
    );
}

/// **REFUSE POLE.** The deployed transfer member — the one and only leg shape
/// `mint_rotated_participant_leg` produces for a value cohort, and therefore the only leg the
/// retired `dregg_sdk::carrier_witness_attach` could ever have attached to — CANNOT carry a
/// sovereign carrier witness. Asserted on the specific reason, not merely on `is_err`.
///
/// ⚑ And asserted on the reason that is NOT the obvious one: the member DOES pin every claim slot
/// (they are its own anchor lanes), so the pin check passes and only the overlap arithmetic bites.
#[test]
fn deployed_transfer_member_cannot_carry_a_sovereign_carrier_witness() {
    let desc = member(TRANSFER_MEMBER);
    let claim = claim_range();
    let n = desc.public_input_count;

    // It IS a wide leg — condition 1 passes, so the refusal below is not "wrong leg class".
    assert!(
        n >= WIDE_PI_COUNT,
        "{TRANSFER_MEMBER} must be a WIDE member ({n} PIs < {WIDE_PI_COUNT}); otherwise this \
         pole refuses for a reason that has nothing to do with the carrier claim"
    );

    // The measured shape the retired SDK attach handed the fold.
    assert!(
        n < claim.end + 2 * SEG_ANCHOR_WIDTH,
        "{TRANSFER_MEMBER} now publishes {n} PIs, enough to clear the sovereign claim slice \
         [{}..{}) — a value-cohort leg has become geometrically able to carry a sovereign \
         carrier claim. That is a deliberate change, not a passing one: re-read \
         `carrier_claim_pins_admitted` before relaxing this.",
        claim.start,
        claim.end,
    );

    let refusal = sovereign_claim_admissible(&desc)
        .expect_err("a transfer leg must be REFUSED on the sovereign carrier arm");
    assert!(
        refusal.contains("overlaps"),
        "the refusal must be the claim-slice/anchor overlap the deployed fold reports, not some \
         other failure: {refusal}"
    );

    // ⚑ THE POINT. Every claim slot IS pinned on this member — to a lane of its own 8-felt state
    // anchors (the last 16 PIs). So the `PiBinding` condition does NOT separate these two members
    // and must never be mistaken for the thing that does.
    let anchors_lo = n - 2 * SEG_ANCHOR_WIDTH;
    let unpinned: Vec<usize> = claim.clone().filter(|pi| !pins(&desc, *pi)).collect();
    assert!(
        unpinned.is_empty(),
        "expected {TRANSFER_MEMBER} to pin EVERY sovereign claim slot (they are its own wide \
         anchor lanes) — PIs {unpinned:?} are unpinned. If the member genuinely stopped \
         publishing there, the note in this file's header about the pin check being \
         insufficient is now wrong and must be rewritten, not deleted."
    );
    for pi in claim.clone() {
        assert!(
            pi >= anchors_lo,
            "{TRANSFER_MEMBER} pins sovereign claim PI {pi} OUTSIDE its wide anchors \
             [{anchors_lo}..{n}) — it is publishing a tooth of its own at a sovereign claim \
             slot, which is a stronger collision than the anchor-lane overlap this file \
             documents"
        );
    }
}
