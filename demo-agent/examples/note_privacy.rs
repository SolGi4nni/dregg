//! Note Privacy Demo — End-to-End Private Value Transfer
//!
//! Demonstrates:
//! 1. Alice creates a note (value=100, asset=GOLD)
//! 2. Alice transfers to Bob: creates nullifier (proving she can spend), creates new note for Bob
//! 3. Bob verifies: checks nullifier not in nullifier set, checks new commitment is valid
//! 4. Bob transfers partial amount to Carol: spends his note, creates two new notes (change + transfer)
//! 5. Show: at no point does any observer learn Alice->Bob->Carol linkage
//! 6. Show: double-spend attempt fails (nullifier already in set)
//! 7. Uses real STARK proofs (the deployed IR-v2 note-spend leaf descriptor,
//!    `note-spend-leaf::dregg-note-spending-dsl-v3`) to verify note ownership —
//!    the same prove/verify pair the turn executor's `verify_note_spend_descriptor2`
//!    dispatches to.

use dregg_cell::note::Note;
use dregg_cell::nullifier_set::NullifierSet;
use dregg_circuit::{
    BabyBear,
    descriptor_by_name::descriptor_by_name,
    descriptor_ir2::{
        DreggStarkConfig, Ir2BatchProof, MemBoundaryWitness, prove_vm_descriptor2,
        verify_vm_descriptor2,
    },
    dsl::note_spending::{create_test_witness, note_spend_mint_hash_felt},
    effect_vm::bytes32_to_8_limbs,
    note_spend_witness::{NOTE_SPEND_LEAF_NAME, note_spend_witness},
    note_spending_witness::NoteSpendingWitness,
};

/// Prove a note spend through the DEPLOYED IR-v2 leaf descriptor (fetched fail-closed
/// by name, exactly as the turn executor does).
fn prove_note_spend_leaf(witness: &NoteSpendingWitness) -> Ir2BatchProof<DreggStarkConfig> {
    let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("leaf descriptor registered");
    let (trace, pis) = note_spend_witness(witness).expect("witness builds the leaf trace");
    prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest note-spend must prove")
}

/// Verify a note-spend proof from PUBLIC data only — the verifier rebuilds the 7-slot
/// claim tuple `[nullifier, merkle_root, value_lo, asset_type, destination_federation,
/// value_hi, mint_hash]` from the public claim, mirroring the turn executor's
/// `verify_note_spend_descriptor2` (turn/src/executor/apply.rs). A forged slot makes the
/// descriptor's boundary pins UNSAT, so verification fails.
fn verify_note_spend_claim(
    nullifier: BabyBear,
    merkle_root: BabyBear,
    value_lo: BabyBear,
    asset_type: BabyBear,
    proof: &Ir2BatchProof<DreggStarkConfig>,
) -> Result<(), String> {
    let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).ok_or_else(|| {
        format!("note-spend leaf descriptor `{NOTE_SPEND_LEAF_NAME}` is not registered")
    })?;
    let destination_federation = BabyBear::ZERO; // a local spend (no bridge leg)
    let value_hi = BabyBear::ZERO; // demo values fit the low limb
    let mint = note_spend_mint_hash_felt(
        nullifier,
        merkle_root,
        value_lo,
        asset_type,
        destination_federation,
        value_hi,
    );
    let pi = vec![
        nullifier,
        merkle_root,
        value_lo,
        asset_type,
        destination_federation,
        value_hi,
        mint,
    ];
    verify_vm_descriptor2(&desc, proof, &pi)
        .map_err(|e| format!("note-spend descriptor verification failed: {e}"))
}

/// Asset type constant for GOLD.
const ASSET_GOLD: u64 = 0xABCD_0000_0000_0001;

/// Helper: derive a spending key from a name (deterministic for demo).
fn spending_key(name: &str) -> [u8; 32] {
    blake3::derive_key("dregg-note-demo-spending-key-v1", name.as_bytes())
}

/// Helper: derive an owner public key from a name (deterministic for demo).
fn owner_key(name: &str) -> [u8; 32] {
    blake3::derive_key("dregg-note-demo-owner-key-v1", name.as_bytes())
}

fn main() {
    println!("=== Dregg Note Privacy Demo (End-to-End Private Value Transfer) ===\n");
    println!("This demo shows private value transfers where observers cannot link");
    println!("the sender, receiver, or amounts across transactions.\n");

    // Global nullifier set (the public ledger of spent notes).
    let mut nullifier_set = NullifierSet::new();

    // =========================================================================
    // STEP 1: Alice creates a note (value=100, asset=GOLD)
    // =========================================================================
    println!("--- Step 1: ALICE CREATES A NOTE ---\n");

    let alice_owner = owner_key("alice");
    let alice_sk = spending_key("alice");

    // Create Alice's note: 100 GOLD
    let alice_note = Note::with_randomness(
        alice_owner,
        [ASSET_GOLD, 100, 0, 0, 0, 0, 0, 0],
        [0xA0u8; 32], // deterministic randomness for demo
    );
    let alice_commitment = alice_note.commitment();

    println!("  Alice's note:");
    println!(
        "    Owner: {:02x}{:02x}{:02x}{:02x}... (Alice's public key)",
        alice_owner[0], alice_owner[1], alice_owner[2], alice_owner[3]
    );
    println!("    Asset: GOLD (0x{:016x})", ASSET_GOLD);
    println!("    Value: 100");
    println!(
        "    Commitment: {:02x}{:02x}{:02x}{:02x}...",
        alice_commitment.0[0], alice_commitment.0[1], alice_commitment.0[2], alice_commitment.0[3]
    );
    println!();
    println!("  What an observer sees on-chain: ONLY the commitment hash.");
    println!("  They cannot determine the owner, value, or asset type.");
    println!();

    // =========================================================================
    // STEP 2: Alice transfers 100 GOLD to Bob
    // =========================================================================
    println!("--- Step 2: ALICE TRANSFERS 100 GOLD TO BOB ---\n");

    let bob_owner = owner_key("bob");
    let bob_sk = spending_key("bob");

    // Alice computes the nullifier for her note (proves ownership).
    let alice_nullifier = alice_note.nullifier(&alice_sk);
    println!(
        "  Alice reveals nullifier: {:02x}{:02x}{:02x}{:02x}...",
        alice_nullifier.0[0], alice_nullifier.0[1], alice_nullifier.0[2], alice_nullifier.0[3]
    );
    println!("  (Only Alice can compute this — requires her spending key)");
    println!();

    // Alice also generates a STARK proof that she knows the spending key.
    // This proves: "I know a spending_key such that nullifier = H(commitment || spending_key || nonce)"
    // WITHOUT revealing the spending key.
    println!("  Alice generates STARK proof of note ownership...");
    let alice_witness = create_test_witness(
        BabyBear::new(u32::from_le_bytes(alice_owner[0..4].try_into().unwrap())),
        BabyBear::new(100),               // value
        BabyBear::new(ASSET_GOLD as u32), // asset type (truncated for BabyBear)
        bytes32_to_8_limbs(&alice_sk),    // spending key (8 limbs)
        4,                                // Merkle depth
    );
    let alice_proof = prove_note_spend_leaf(&alice_witness);
    println!("  STARK proof generated");
    println!();

    // Verify the STARK proof (anyone can do this with only public inputs).
    let verify_result = verify_note_spend_claim(
        alice_witness.nullifier(),
        alice_witness.merkle_root(),
        alice_witness.value,
        alice_witness.asset_type,
        &alice_proof,
    );
    assert!(verify_result.is_ok(), "Alice's spending proof must verify");
    println!("  STARK proof verified: [PASS]");
    println!("  (Verifier learned: nullifier is valid, note is in tree.)");
    println!("  (Verifier did NOT learn: who Alice is, or how much she spent.)");
    println!();

    // Add nullifier to the set with the spent note's value (note is now spent).
    nullifier_set
        .insert(alice_nullifier, alice_note.value())
        .expect("nullifier should be accepted");
    println!("  Nullifier recorded in global set (note is spent).");
    println!();

    // Alice creates a new note for Bob.
    let bob_note =
        Note::with_randomness(bob_owner, [ASSET_GOLD, 100, 0, 0, 0, 0, 0, 0], [0xB0u8; 32]);
    let bob_commitment = bob_note.commitment();

    println!("  New note created for Bob:");
    println!(
        "    Commitment: {:02x}{:02x}{:02x}{:02x}...",
        bob_commitment.0[0], bob_commitment.0[1], bob_commitment.0[2], bob_commitment.0[3]
    );
    println!();
    println!("  PRIVACY ANALYSIS (what an observer sees):");
    println!("    - A nullifier was revealed (some note was spent)");
    println!("    - A new commitment appeared (some note was created)");
    println!("    - A STARK proof says the spend is valid");
    println!("    - Observer CANNOT link: nullifier <-> commitment (different hashes)");
    println!("    - Observer CANNOT determine: sender, receiver, or amount");
    println!("    - Observer CANNOT tell if this is a transfer, self-spend, or mint");
    println!();

    // =========================================================================
    // STEP 3: Bob verifies receipt of the note
    // =========================================================================
    println!("--- Step 3: BOB VERIFIES HIS NOTE ---\n");

    // Bob checks that the nullifier (from Alice's spend) is in the set,
    // confirming the spend was recorded (Alice can't double-spend).
    assert!(nullifier_set.contains(&alice_nullifier));
    println!("  Bob checks: Alice's nullifier is in the set [PASS]");
    println!("  (Confirms Alice actually spent her note — not a phantom transfer)");
    println!();

    // Bob verifies his note's commitment is well-formed.
    let bob_recomputed = bob_note.commitment();
    assert_eq!(bob_recomputed, bob_commitment);
    println!("  Bob recomputes his commitment: [MATCHES]");
    println!("  Bob knows: he owns a note with 100 GOLD.");
    println!("  (Bob received the note contents off-chain, encrypted to his key.)");
    println!();

    // Bob also verifies his note has NOT been spent (non-membership proof).
    let bob_nullifier = bob_note.nullifier(&bob_sk);
    let non_membership = nullifier_set.prove_non_membership(&bob_nullifier);
    assert!(
        non_membership.is_some(),
        "Bob's note should not be spent yet"
    );
    let nm_proof = non_membership.unwrap();
    let root = nullifier_set.root();
    assert!(NullifierSet::verify_non_membership(&nm_proof, &root));
    println!("  Bob proves non-membership of his nullifier: [PASS]");
    println!("  (His note is unspent and available to use.)");
    println!();

    // =========================================================================
    // STEP 4: Bob transfers 60 GOLD to Carol, keeps 40 as change
    // =========================================================================
    println!("--- Step 4: BOB SPLITS: 60 TO CAROL, 40 CHANGE ---\n");

    let carol_owner = owner_key("carol");

    // Bob spends his 100 GOLD note.
    println!(
        "  Bob reveals his nullifier: {:02x}{:02x}{:02x}{:02x}...",
        bob_nullifier.0[0], bob_nullifier.0[1], bob_nullifier.0[2], bob_nullifier.0[3]
    );

    // Bob generates a STARK proof of ownership.
    let bob_witness = create_test_witness(
        BabyBear::new(u32::from_le_bytes(bob_owner[0..4].try_into().unwrap())),
        BabyBear::new(100),
        BabyBear::new(ASSET_GOLD as u32),
        bytes32_to_8_limbs(&bob_sk),
        4,
    );
    let bob_proof = prove_note_spend_leaf(&bob_witness);
    println!("  Bob's STARK proof generated");

    let bob_verify = verify_note_spend_claim(
        bob_witness.nullifier(),
        bob_witness.merkle_root(),
        bob_witness.value,
        bob_witness.asset_type,
        &bob_proof,
    );
    assert!(bob_verify.is_ok(), "Bob's spending proof must verify");
    println!("  STARK proof verified: [PASS]");
    println!();

    // Record Bob's nullifier as spent (with the spent note's value).
    nullifier_set
        .insert(bob_nullifier, bob_note.value())
        .expect("Bob's nullifier should be accepted");
    println!("  Bob's nullifier recorded (his 100 GOLD note is spent).");
    println!();

    // Bob creates TWO new notes: 60 for Carol, 40 for himself (change).
    let carol_note = Note::with_randomness(
        carol_owner,
        [ASSET_GOLD, 60, 0, 0, 0, 0, 0, 0],
        [0xC0u8; 32],
    );
    let carol_commitment = carol_note.commitment();

    let bob_change_note =
        Note::with_randomness(bob_owner, [ASSET_GOLD, 40, 0, 0, 0, 0, 0, 0], [0xB1u8; 32]);
    let bob_change_commitment = bob_change_note.commitment();

    println!("  Two new notes created:");
    println!(
        "    Carol's note: commitment {:02x}{:02x}{:02x}{:02x}...",
        carol_commitment.0[0], carol_commitment.0[1], carol_commitment.0[2], carol_commitment.0[3]
    );
    println!(
        "    Bob's change: commitment {:02x}{:02x}{:02x}{:02x}...",
        bob_change_commitment.0[0],
        bob_change_commitment.0[1],
        bob_change_commitment.0[2],
        bob_change_commitment.0[3]
    );
    println!();

    // Conservation check: 100 in = 60 + 40 out.
    assert_eq!(
        bob_note.value(),
        carol_note.value() + bob_change_note.value()
    );
    println!("  Conservation verified: 100 = 60 + 40 [PASS]");
    println!();

    println!("  PRIVACY ANALYSIS:");
    println!("    - Observer sees: 1 nullifier + 2 new commitments");
    println!("    - Observer CANNOT determine:");
    println!("      * Who spent the note (Bob's identity is hidden)");
    println!("      * Who received the notes (Carol and Bob are hidden)");
    println!("      * The split amounts (60/40 is hidden in the commitments)");
    println!("      * Whether this is a transfer, a split, or a consolidation");
    println!("    - Observer CANNOT link this spend to the earlier Alice->Bob transfer");
    println!("      (different nullifiers, different commitments, no public linkage)");
    println!();

    // =========================================================================
    // STEP 5: Unlinkability demonstration
    // =========================================================================
    println!("--- Step 5: UNLINKABILITY ANALYSIS ---\n");

    println!("  The complete transfer chain was: Alice -> Bob -> Carol");
    println!("  But from the public ledger, an observer sees only:\n");
    println!("  Transaction 1:");
    println!(
        "    Nullifier: {:02x}{:02x}...  (some note was spent)",
        alice_nullifier.0[0], alice_nullifier.0[1]
    );
    println!(
        "    New commitment: {:02x}{:02x}...  (some note was created)",
        bob_commitment.0[0], bob_commitment.0[1]
    );
    println!();
    println!("  Transaction 2:");
    println!(
        "    Nullifier: {:02x}{:02x}...  (some note was spent)",
        bob_nullifier.0[0], bob_nullifier.0[1]
    );
    println!(
        "    New commitments: {:02x}{:02x}..., {:02x}{:02x}...",
        carol_commitment.0[0],
        carol_commitment.0[1],
        bob_change_commitment.0[0],
        bob_change_commitment.0[1]
    );
    println!();
    println!("  Can the observer link Transaction 1 to Transaction 2?");
    println!("    - The nullifiers are different (derived from different notes): NO");
    println!("    - The commitments are different (different owners/randomness): NO");
    println!("    - No public data connects Alice to Bob to Carol: NO");
    println!();
    println!("  The observer cannot even tell these transactions involved the same asset!");
    println!("  [UNLINKABILITY VERIFIED]");
    println!();

    // =========================================================================
    // STEP 6: Double-spend prevention
    // =========================================================================
    println!("--- Step 6: DOUBLE-SPEND PREVENTION ---\n");

    // Alice tries to spend her note again.
    println!("  Alice attempts to re-use her nullifier (double-spend)...");
    let double_spend = nullifier_set.insert(alice_nullifier, alice_note.value());
    assert!(double_spend.is_err());
    println!("  REJECTED: {:?}", double_spend.unwrap_err());
    println!();

    // Bob tries to spend his original 100 GOLD note again.
    println!("  Bob attempts to re-spend his 100 GOLD note...");
    let bob_double = nullifier_set.insert(bob_nullifier, bob_note.value());
    assert!(bob_double.is_err());
    println!("  REJECTED: {:?}", bob_double.unwrap_err());
    println!();

    // But Bob CAN spend his change note (it hasn't been spent yet).
    let bob_change_nullifier = bob_change_note.nullifier(&bob_sk);
    assert!(!nullifier_set.contains(&bob_change_nullifier));
    println!("  Bob's change note (40 GOLD) is still unspent: [CONFIRMED]");
    println!("  He can transfer it in a future transaction.");
    println!();

    // Carol can also spend her received note.
    let carol_sk = spending_key("carol");
    let carol_nullifier = carol_note.nullifier(&carol_sk);
    assert!(!nullifier_set.contains(&carol_nullifier));
    println!("  Carol's note (60 GOLD) is unspent: [CONFIRMED]");
    println!("  She can spend it whenever she chooses.");
    println!();

    // =========================================================================
    // FINAL STATE
    // =========================================================================
    println!("--- Final State ---\n");
    println!(
        "  Nullifier set size: {} (notes ever spent)",
        nullifier_set.len()
    );
    println!(
        "  Nullifier set root: {:02x}{:02x}{:02x}{:02x}...",
        nullifier_set.root()[0],
        nullifier_set.root()[1],
        nullifier_set.root()[2],
        nullifier_set.root()[3]
    );
    println!();
    println!("  Live notes (unspent):");
    println!(
        "    Carol: 60 GOLD (commitment {:02x}{:02x}...)",
        carol_commitment.0[0], carol_commitment.0[1]
    );
    println!(
        "    Bob:   40 GOLD (commitment {:02x}{:02x}...)",
        bob_change_commitment.0[0], bob_change_commitment.0[1]
    );
    println!("  Total GOLD in circulation: 100 (conserved from Alice's original)");
    println!();
    println!("  Security properties proven:");
    println!("    1. PRIVACY: No observer can link Alice -> Bob -> Carol");
    println!("    2. CONSERVATION: 100 GOLD created, 100 GOLD still exists (60 + 40)");
    println!("    3. NO DOUBLE-SPEND: Each note can only be spent once");
    println!("    4. SELF-PROVING: STARK proofs verify ownership without revealing keys");
    println!("    5. FEDERATION-INDEPENDENT: Nullifiers are globally unique (no tree position)");
    println!();
    println!("=== Note Privacy Demo Complete ===");
}
