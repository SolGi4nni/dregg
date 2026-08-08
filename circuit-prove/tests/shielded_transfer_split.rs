//! Both-polarity gate for the shielded transfer's **SPLIT WITH CHANGE**, at the circuit layer.
//!
//! **SAY THE SUBSTRATE OUT LOUD: the AIR is AUTHORED IN LEAN.** The relation under test is
//! `dregg-shielded-transfer-value-link-2out::v1`
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedTransferValueLink2OutEmit.lean`, 309 columns, 18 PIs
//! `wide[16] ++ [outCm1, outCm2]`, 305 constraints, byte-pinned there by `link2_emits_golden`).
//! This file authors no constraint: it builds witnesses, proves, and reads verdicts. These are
//! behaviour tests over the DEPLOYED path — not refinement, not translation validation, not
//! verification. The conservation THEOREM is `link2_conservation` in the Lean file; what is
//! measured here is that the deployed prover and verifier behave as that theorem says.
//!
//! ## What was impossible before
//!
//! `dregg-shielded-transfer-value-link::v1` binds one spent note to one minted note of EQUAL
//! value. A shielded note was therefore all-or-nothing: spendable, but never divisible. Holding
//! `1000` and owing `7`, the only stated move was to hand over the whole `1000`.
//!
//! ## The attack these tests are built around
//!
//! A limbwise carry chain has exactly one interesting hole, and the Lean `carry_chain_sums` names
//! it with `c_3` free:
//!
//! ```text
//! o1 + o2 = v + 2^64 * c_3
//! ```
//!
//! Every one of the four chain gates is satisfied by a witness with `c_3 = 1` — the limb equations
//! balance perfectly, because absorbing an overflow is what a carry is FOR. So the interesting
//! negative is not "outputs that obviously exceed the input"; it is **two outputs whose sum wraps
//! `u64` back onto the input**, which satisfies every gate except the terminal carry pin.
//!
//! [`the_carry_chain_is_the_only_thing_between_a_wrapped_sum_and_a_mint`] asserts that attack is
//! REAL before any prover is consulted: it shows the four chain gates evaluate to zero on the
//! wrapped witness and that `c_3` is `1`. Without that assertion, a negative test that merely
//! observes "the proof was refused" cannot tell a working `carryTopZero` from a witness the trace
//! generator happened to mangle.

use dregg_cell::{ShieldedNoteCommitment, ShieldedNoteSet, felt_to_bytes32};
use dregg_circuit::exact_nullifier_aafi::TaggedKeyWire;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::shielded::transfer_link_2out::col;
use dregg_circuit_prove::shielded::{
    BINDING_BLIND_LANES, DEPLOYED_INPUTS, LINK_2OUT_OUTPUTS, SUPPORTED_OUTPUTS,
    ShieldedLink2OutMint, ShieldedSpendCompleteClaim, ShieldedSpendCompleteWitness,
    ShieldedSpendMembership, ShieldedTransferLink2OutWitness, ShieldedTransferSplitWitness,
    TREE_DEPTH, generate_shielded_transfer_link_2out_trace, prove_shielded_spend_complete,
    prove_shielded_transfer_link_2out, prove_shielded_transfer_link_2out_from_trace,
    prove_shielded_transfer_split, shielded_transfer_value_link_2out_descriptor,
    verify_shielded_spend_complete_parts, verify_shielded_transfer_link_2out,
};

const ASSET: u64 = 3;

fn blind(seed: u32) -> [BabyBear; BINDING_BLIND_LANES] {
    core::array::from_fn(|i| BabyBear::new(seed + (i as u32) * 0x111 + 1))
}

/// A recipient: a four-limb spending key and the owner felt it derives. Deriving the owner from the
/// key (rather than picking one) is what lets the minted note actually be SPENT below — the
/// complete-spend relation recomputes `cOWNER = hash_fact(key0,[key1..3])` and pins it.
fn recipient(seed: u32) -> ([BabyBear; 4], BabyBear) {
    let key: [BabyBear; 4] =
        core::array::from_fn(|i| BabyBear::new(seed.wrapping_mul(37) + i as u32 + 3));
    (key, hash_fact(key[0], &[key[1], key[2], key[3]]))
}

/// The four chain-gate residuals `v_i - o1_i - o2_i + 65536*c_i - c_{i-1}` and the four carries, as
/// **integers**, read straight off a generated trace.
///
/// This is the Lean `carryChain_eval` read back over the deployed trace generator. It consults no
/// prover, so it is free — and it is what makes the negatives below non-vacuous.
fn chain_residuals_and_carries(witness: &ShieldedTransferLink2OutWitness) -> ([i64; 4], [i64; 4]) {
    let (trace, _pis) = generate_shielded_transfer_link_2out_trace(witness);
    let row = &trace[0];
    let at = |c: usize| row[c].as_u32() as i64;
    let carries: [i64; 4] = core::array::from_fn(|i| at(col::CARRY + i));
    let residuals: [i64; 4] = core::array::from_fn(|i| {
        let carry_in = if i == 0 { 0 } else { carries[i - 1] };
        at(col::VALUE_LIMBS + i) - at(col::out_limb(0, i)) - at(col::out_limb(1, i))
            + 65536 * carries[i]
            - carry_in
    });
    (residuals, carries)
}

/// The emitted index of each gate this file's negatives expect to fire, derived from the Lean
/// emission order in `shieldedTransferValueLink2OutConstraints`:
///
/// ```text
///   0..271  16 limb blocks of (16 boolean pins + 1 recomposition)
/// 272..274  the three reductions (asset, mint 1, mint 2)
/// 275..278  ⚑ the four CARRY CHAIN gates, limb 0..3
/// 279..281  the carry booleanity pins, c_0..c_2
///      282  ⚑ carryTopZero — `1 * c_3 = 0`
/// 283..286  two carrier sites, two note-commitment sites
/// 287..304  the eighteen PI pins
/// ```
///
/// Naming the index is what turns "the proof was refused" into "the proof was refused BY THE GATE
/// THIS TEST IS ABOUT". A mutation that started tripping some unrelated constraint would fail here
/// rather than pass as a green negative.
const GATE_CHAIN_LIMB0: &str = "#275";
const GATE_CARRY0_BOOLEAN: &str = "#279";
const GATE_CARRY_TOP_ZERO: &str = "#282";

/// Drive a proving attempt that must be REFUSED, and return the refusal's text.
///
/// A trace that does not satisfy the AIR is refused in one of two ways: plonky3's constraint check
/// PANICS naming the failed constraint indices (`failed constraints = [#N]`), or proving /
/// verification returns an `Err`. Both are refusals. The one outcome that is NOT a refusal — a
/// proof that verifies against the spent note's carrier — fails the test here.
fn refusal_text(
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
    carrier: &[BabyBear; 16],
    what: &str,
) -> String {
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_shielded_transfer_link_2out_from_trace(trace, pis)
    }));
    match outcome {
        Err(payload) => payload
            .downcast_ref::<&str>()
            .map(|s| (*s).to_string())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "<non-string panic>".to_string()),
        Ok(Err(e)) => e.to_string(),
        Ok(Ok(bad)) => {
            let cms: [BabyBear; LINK_2OUT_OUTPUTS] = core::array::from_fn(|k| pis[16 + k]);
            match verify_shielded_transfer_link_2out(&bad.proof_bytes(), carrier, &cms) {
                Ok(()) => panic!(
                    "{what} produced a proof that VERIFIES against the spent note's carrier — the \
                     relation admits a mint it must not"
                ),
                Err(e) => e.to_string(),
            }
        }
    }
}

fn split_witness(
    value: u64,
    payee_value: u64,
    payee_owner: BabyBear,
    change_owner: BabyBear,
) -> ShieldedTransferLink2OutWitness {
    ShieldedTransferLink2OutWitness::split(
        value,
        ASSET,
        BabyBear::new(0x4242),
        blind(0x1000),
        ShieldedLink2OutMint {
            value: payee_value,
            owner: payee_owner,
            randomness: BabyBear::new(0x9991),
        },
        change_owner,
        BabyBear::new(0x9992),
    )
    .expect("an honest split")
}

/// The relation the deployed path loads IS the Lean-emitted one, at the shape the Lean file's named
/// theorems pin. A drift in either direction (Lean moves, or Rust's mirror moves) shows up here.
#[test]
fn the_deployed_2out_relation_is_the_lean_emitted_one() {
    let desc = shielded_transfer_value_link_2out_descriptor();
    assert_eq!(desc.name, "dregg-shielded-transfer-value-link-2out::v1");
    assert_eq!(
        desc.trace_width, 309,
        "LINK2_WIDTH — ShieldedTransferValueLink2OutEmit.LINK2_WIDTH_eq"
    );
    assert_eq!(
        desc.public_input_count, 18,
        "wide[16] ++ [outCm1, outCm2] — ShieldedTransferValueLink2OutEmit.LINK2_PI_COUNT_eq"
    );
    assert_eq!(
        desc.constraints.len(),
        305,
        "256 boolean pins + 16 limb recompositions + 3 reductions + 4 chain gates + 3 carry \
         booleanity pins + 1 terminal zero + 2 carriers + 2 fact sites + 18 pins — \
         ShieldedTransferValueLink2OutEmit.constraint_census"
    );
}

/// ⚑ **THE CARRY-CHAIN ATTACK, ASSERTED PRESENT — before any prover is consulted.**
///
/// Three witnesses, read at the trace level:
///
/// 1. an HONEST split — every chain residual is zero and the terminal carry is zero;
/// 2. a WRAPPED sum (`o1 + o2 == v + 2^64`) — **every chain residual is STILL zero** and the
///    terminal carry is `1`. This is the whole `u64` range minted from nothing, sitting in a trace
///    that satisfies all four limb equations. Only `carryTopZero` refuses it;
/// 3. an ORDINARY inflation by 1 — at least one chain residual is nonzero.
///
/// Case 2 is the reason this test exists. A negative test that only reads "the proof was refused"
/// cannot distinguish a working terminal-carry gate from a trace generator that happened to produce
/// garbage; this shows the trace is otherwise perfectly well-formed.
#[test]
fn the_carry_chain_is_the_only_thing_between_a_wrapped_sum_and_a_mint() {
    let (_ka, owner_a) = recipient(1);
    let (_kb, owner_b) = recipient(2);

    // ── 1. HONEST: 1000 = 700 + 300.
    let honest = split_witness(1000, 700, owner_a, owner_b);
    assert_eq!(
        honest.outputs[0].value + honest.outputs[1].value,
        honest.value,
        "the honest split conserves"
    );
    let (res, carries) = chain_residuals_and_carries(&honest);
    assert_eq!(res, [0; 4], "every chain gate vanishes on an honest split");
    assert_eq!(carries[3], 0, "and nothing carries out of the top limb");

    // ── 2. ⚑ THE WRAPPED SUM. o1 + o2 = 2^64 + 1000, which wraps to the input value.
    let o0 = 1u64 << 63;
    let o1 = (1u64 << 63) + 1000;
    let wrapped = ShieldedTransferLink2OutWitness {
        value: 1000,
        asset_type: ASSET,
        in_randomness: BabyBear::new(0x4242),
        in_binding_blind: blind(0x1000),
        outputs: [
            ShieldedLink2OutMint {
                value: o0,
                owner: owner_a,
                randomness: BabyBear::new(0x9991),
            },
            ShieldedLink2OutMint {
                value: o1,
                owner: owner_b,
                randomness: BabyBear::new(0x9992),
            },
        ],
    };
    // ── THE MUTATION, ASSERTED PRESENT. ──
    assert!(
        o0.checked_add(o1).is_none(),
        "VACUITY GUARD: the two outputs must genuinely overflow u64, or there is no 2^64 to smuggle"
    );
    assert_eq!(
        o0.wrapping_add(o1),
        wrapped.value,
        "VACUITY GUARD: and they must wrap back exactly onto the input value, or an ordinary limb \
         gate would refuse this and the terminal carry pin would never be reached"
    );
    let (res, carries) = chain_residuals_and_carries(&wrapped);
    assert_eq!(
        res, [0; 4],
        "⚑ EVERY chain gate STILL vanishes on the wrapped sum — the limb equations balance, \
         because absorbing an overflow is exactly what a carry is for"
    );
    assert_eq!(
        carries[3], 1,
        "⚑ and the terminal carry is 1: this trace mints 2^64 and satisfies every gate but \
         carryTopZero (Lean carry_chain_sums)"
    );

    // ── 3. ORDINARY INFLATION: 700 + 301 out of 1000.
    let inflated = ShieldedTransferLink2OutWitness {
        outputs: [
            honest.outputs[0],
            ShieldedLink2OutMint {
                value: 301,
                ..honest.outputs[1]
            },
        ],
        ..honest
    };
    assert_ne!(
        inflated.outputs[0].value + inflated.outputs[1].value,
        inflated.value,
        "VACUITY GUARD: the inflated split must not conserve"
    );
    let (res, _carries) = chain_residuals_and_carries(&inflated);
    assert!(
        res.iter().any(|r| *r != 0),
        "an ordinary inflation must break a limb equation: {res:?}"
    );
}

/// ⚑ **THE POSITIVE POLE.** An honest split proves and verifies, the two minted notes are distinct,
/// and — the part that matters — **BOTH are SPENDABLE**: each is a `hash_fact(v,[a,owner,rand])`
/// leaf that the complete-spend relation opens, driven here through a real proof against a real
/// committed accumulator.
///
/// The change note is then SPLIT AGAIN, which is the whole point of the descriptor: value that
/// arrives as change is ordinary value.
///
/// Also folded in (free, once the proof exists): an honest proof cannot be re-pointed at different
/// commitments.
#[test]
fn an_honest_split_verifies_and_both_minted_notes_are_spendable() {
    let (key_a, owner_a) = recipient(11);
    let (key_b, owner_b) = recipient(12);
    let witness = split_witness(1000, 700, owner_a, owner_b);
    assert_eq!(
        witness.outputs[1].value, 300,
        "the change is DERIVED, not stated"
    );

    // ── PROVE + VERIFY the split.
    let proof = prove_shielded_transfer_link_2out(&witness).expect("the honest split proves");
    let cms = witness.out_note_commitment_felts();
    assert_ne!(cms[0], cms[1], "two different notes, two different leaves");
    verify_shielded_transfer_link_2out(&proof.proof_bytes(), &witness.in_wide_binding(), &cms)
        .expect("the honest split verifies against the spent carrier and both minted leaves");

    // ── NEGATIVE (free): the same proof, re-pointed at a swapped pair of commitments.
    assert!(
        verify_shielded_transfer_link_2out(
            &proof.proof_bytes(),
            &witness.in_wide_binding(),
            &[cms[1], cms[0]],
        )
        .is_err(),
        "the outputs are ORDERED — a proof cannot be spliced onto the same leaves in the other \
         slots (they carry different values)"
    );

    // ── SPENDABILITY. Build the complete-spend witness for each mint and check, first, that the
    //    leaf the split published IS the leaf that relation opens.
    let mint_spend =
        |value: u64, key: [BabyBear; 4], rand: BabyBear| ShieldedSpendCompleteWitness {
            value,
            asset_type: ASSET,
            randomness: rand,
            spending_key: key,
            binding_blind: blind(0x2000),
            membership: ShieldedSpendMembership {
                positions: [0; TREE_DEPTH],
                siblings: [[[BabyBear::ZERO; 8]; 3]; TREE_DEPTH],
                next_addr: TaggedKeyWire::top(),
            },
        };
    let payee = mint_spend(700, key_a, witness.outputs[0].randomness);
    let change = mint_spend(300, key_b, witness.outputs[1].randomness);
    assert_eq!(
        payee.note_commitment_felt(),
        cms[0],
        "⚑ the payee's minted leaf IS what the complete-spend relation opens — same hash_fact site"
    );
    assert_eq!(
        change.note_commitment_felt(),
        cms[1],
        "⚑ and so is the CHANGE leaf"
    );

    // ── Commit both mints to a real accumulator and drive a real spend of EACH.
    let mut set = ShieldedNoteSet::new();
    set.insert(ShieldedNoteCommitment(felt_to_bytes32(BabyBear::new(
        0x0A0A_0001,
    ))))
    .expect("decoy inserts");
    for cm in cms {
        set.insert(ShieldedNoteCommitment(felt_to_bytes32(cm)))
            .expect("the minted note is committed");
    }
    let committed = set.root8().limbs();
    let with_path = |probe: ShieldedSpendCompleteWitness| {
        let cm = ShieldedNoteCommitment(felt_to_bytes32(probe.note_commitment_felt()));
        let path = set
            .membership_path(&cm)
            .expect("the committed mint has a membership path");
        ShieldedSpendCompleteWitness {
            membership: ShieldedSpendMembership {
                positions: path.path.positions,
                siblings: path.path.siblings,
                next_addr: path.leaf.next_addr().wire(),
            },
            ..probe
        }
    };

    let payee_spend = prove_shielded_spend_complete(&with_path(payee))
        .expect("⚑ the PAYEE's minted note spends: the value that arrived can leave again");
    verify_shielded_spend_complete_parts(
        &ShieldedSpendCompleteClaim {
            committed_root: committed,
            ..payee_spend.claim
        },
        &payee_spend.proof,
    )
    .expect("and its spend proof verifies under the committed root");

    // ── The CHANGE note, spent by being SPLIT AGAIN — 300 into 120 + 180. This is the whole
    //    descriptor: change is ordinary value, divisible like any other note.
    let (_kc, owner_c) = recipient(13);
    let (_kd, owner_d) = recipient(14);
    let resplit = prove_shielded_transfer_split(&ShieldedTransferSplitWitness {
        spend: with_path(change),
        payee_value: 120,
        payee_owner: owner_c,
        payee_randomness: BabyBear::new(0x7771),
        change_owner: owner_d,
        change_randomness: BabyBear::new(0x7772),
    })
    .expect("⚑ the CHANGE note splits again");
    resplit
        .verify(committed)
        .expect("and the re-split verifies under the committed root");
    assert_eq!(resplit.outputs.len(), 2);
}

/// ⚑ **THE NEGATIVE POLE — the carry-chain attacks, and ordinary inflation, all refused.**
///
/// Each mutation is asserted PRESENT (at the trace level, by
/// [`chain_residuals_and_carries`]) before its verdict is read, so a generator change that quietly
/// disarmed one of these adversaries would fail here rather than pass silently.
#[test]
fn inflating_and_carry_chain_splits_are_refused() {
    let (_ka, owner_a) = recipient(21);
    let (_kb, owner_b) = recipient(22);

    let refuse = |witness: &ShieldedTransferLink2OutWitness, what: &str| -> String {
        let (trace, pis) = generate_shielded_transfer_link_2out_trace(witness);
        refusal_text(&trace, &pis, &witness.in_wide_binding(), what)
    };

    // ── 1. ORDINARY INFLATION: 700 + 301 out of 1000.
    let inflated = ShieldedTransferLink2OutWitness {
        outputs: [
            ShieldedLink2OutMint {
                value: 700,
                owner: owner_a,
                randomness: BabyBear::new(0x9991),
            },
            ShieldedLink2OutMint {
                value: 301,
                owner: owner_b,
                randomness: BabyBear::new(0x9992),
            },
        ],
        ..split_witness(1000, 700, owner_a, owner_b)
    };
    assert!(
        inflated.outputs[0].value + inflated.outputs[1].value > inflated.value,
        "MUTATION ASSERTED PRESENT: the outputs sum to MORE than the input"
    );
    let text = refuse(&inflated, "an inflating split (1000 -> 700 + 301)");
    assert!(
        text.contains(GATE_CHAIN_LIMB0),
        "an inflating split must break the limb-0 CHAIN gate {GATE_CHAIN_LIMB0}, not something          else: {text}"
    );

    // ── 2. ⚑ THE 2^64 SMUGGLE: a wrapped sum, every limb gate satisfied, terminal carry 1.
    let wrapped = ShieldedTransferLink2OutWitness {
        outputs: [
            ShieldedLink2OutMint {
                value: 1u64 << 63,
                owner: owner_a,
                randomness: BabyBear::new(0x9991),
            },
            ShieldedLink2OutMint {
                value: (1u64 << 63) + 1000,
                owner: owner_b,
                randomness: BabyBear::new(0x9992),
            },
        ],
        ..split_witness(1000, 700, owner_a, owner_b)
    };
    let (res, carries) = chain_residuals_and_carries(&wrapped);
    assert_eq!(
        (res, carries[3]),
        ([0; 4], 1),
        "MUTATION ASSERTED PRESENT: the wrapped trace satisfies all four limb gates and carries \
         2^64 out of the top limb — only carryTopZero stands between it and a mint"
    );
    let text = refuse(&wrapped, "the 2^64 terminal-carry smuggle");
    assert!(
        text.contains(GATE_CARRY_TOP_ZERO),
        "⚑ the 2^64 smuggle must be refused by carryTopZero {GATE_CARRY_TOP_ZERO} — that is the          ONE gate standing between a wrapped sum and a mint: {text}"
    );
    for chain_gate in ["#275", "#276", "#277", "#278"] {
        assert!(
            !text.contains(chain_gate),
            "⚑ and NO chain gate may appear in the refusal: if a limb equation had also broken,              this witness would not have been the pure terminal-carry attack it claims to be              ({chain_gate} in {text})"
        );
    }

    // ── 3. A NON-BOOLEAN CARRY, poked directly into an otherwise honest trace.
    let honest = split_witness(1000, 700, owner_a, owner_b);
    let (mut trace, pis) = generate_shielded_transfer_link_2out_trace(&honest);
    let before = trace[0][col::CARRY].as_u32();
    for row in trace.iter_mut() {
        row[col::CARRY] = BabyBear::new(2);
    }
    // ── THE MUTATION, ASSERTED PRESENT. ──
    assert_ne!(
        before,
        trace[0][col::CARRY].as_u32(),
        "MUTATION ASSERTED PRESENT: carry 0 actually changed"
    );
    let poked = trace[0][col::CARRY].as_u32();
    assert!(
        poked != 0 && poked != 1,
        "MUTATION ASSERTED PRESENT: carry 0 is now non-boolean ({poked})"
    );
    let text = refusal_text(
        &trace,
        &pis,
        &honest.in_wide_binding(),
        "a non-boolean carry",
    );
    assert!(
        text.contains(GATE_CARRY0_BOOLEAN),
        "a non-boolean carry must be refused by the booleanity pin {GATE_CARRY0_BOOLEAN}: {text}"
    );
}

/// The transfer object's arity gate: `1-in/2-out` is now ADMITTED, and every other arity still
/// REFUSES by name.
///
/// The refusal must name the family rather than a single arity — a message that still said
/// "1-in/1-out" after this descriptor landed would be a documented wound rather than a detected
/// one.
#[test]
fn transfer_admits_one_in_two_out_and_refuses_every_other_arity_by_name() {
    assert_eq!(DEPLOYED_INPUTS, 1);
    assert_eq!(SUPPORTED_OUTPUTS, [1, 2]);
    assert_eq!(LINK_2OUT_OUTPUTS, 2);

    let (key, owner) = recipient(31);
    let (_kb, change_owner) = recipient(32);
    let probe = ShieldedSpendCompleteWitness {
        value: 500,
        asset_type: ASSET,
        randomness: BabyBear::new(0x777),
        spending_key: key,
        binding_blind: blind(0x3000),
        membership: ShieldedSpendMembership {
            positions: [0; TREE_DEPTH],
            siblings: [[[BabyBear::ZERO; 8]; 3]; TREE_DEPTH],
            next_addr: TaggedKeyWire::top(),
        },
    };
    let commitment = ShieldedNoteCommitment(felt_to_bytes32(probe.note_commitment_felt()));
    let mut set = ShieldedNoteSet::new();
    set.insert(ShieldedNoteCommitment(felt_to_bytes32(BabyBear::new(
        0x0A0A_0002,
    ))))
    .expect("decoy inserts");
    set.insert(commitment).expect("the spent note is committed");
    let path = set
        .membership_path(&commitment)
        .expect("the committed note has a membership path");
    let spend = ShieldedSpendCompleteWitness {
        membership: ShieldedSpendMembership {
            positions: path.path.positions,
            siblings: path.path.siblings,
            next_addr: path.leaf.next_addr().wire(),
        },
        ..probe
    };

    let mut transfer = prove_shielded_transfer_split(&ShieldedTransferSplitWitness {
        spend,
        payee_value: 120,
        payee_owner: owner,
        payee_randomness: BabyBear::new(0x321),
        change_owner,
        change_randomness: BabyBear::new(0x322),
    })
    .expect("a 1-in/2-out transfer proves");

    // ⚑ THE INVERSION: this arity used to be a refusal.
    transfer
        .verify(set.root8().limbs())
        .expect("⚑ 1-in/2-out is ADMITTED — the split has a stated conservation now");
    assert!(
        transfer
            .verify(ShieldedNoteSet::new().root8().limbs())
            .is_err(),
        "and it is still judged under the EXECUTOR's committed root (seam #15)"
    );

    // 1-in/3-out has no descriptor and must refuse BY NAME.
    let spare = transfer.outputs[0];
    transfer.outputs.push(spare);
    let err = transfer
        .verify(set.root8().limbs())
        .expect_err("1-in/3-out has no stated conservation and must refuse");
    assert!(
        err.to_string().contains("not stated by the deployed"),
        "the refusal must name the missing descriptor: {err}"
    );
    assert!(
        err.to_string().contains("[1, 2]"),
        "and must name the arities that ARE stated, or it becomes stale the moment the family \
         grows: {err}"
    );
    transfer.outputs.truncate(2);

    // 1-in/0-out likewise.
    let saved = std::mem::take(&mut transfer.outputs);
    assert!(
        transfer.verify(set.root8().limbs()).is_err(),
        "1-in/0-out has no stated conservation and must refuse"
    );
    transfer.outputs = saved;

    // A split that pays out more than the note holds refuses at CONSTRUCTION.
    // (`let Err(..) else` rather than `expect_err`: `ShieldedTransfer` holds `Ir2BatchProof`s and
    // is deliberately not `Debug`.)
    let Err(err) = prove_shielded_transfer_split(&ShieldedTransferSplitWitness {
        spend: ShieldedSpendCompleteWitness { value: 10, ..probe },
        payee_value: 11,
        payee_owner: owner,
        payee_randomness: BabyBear::new(0x321),
        change_owner,
        change_randomness: BabyBear::new(0x322),
    }) else {
        panic!("paying 11 out of a note worth 10 must refuse");
    };
    assert!(
        err.to_string().contains("no change amount that conserves"),
        "the refusal must say why: {err}"
    );
}
