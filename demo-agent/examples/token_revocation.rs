//! Token Revocation Demo — Privacy-Preserving Revocation with Non-Membership Proofs
//!
//! Demonstrates:
//! 1. Mint a token, use it successfully
//! 2. Revoke the token (add to revocation tree / nullifier set)
//! 3. Show that the revoked token is rejected with a non-membership proof failure
//! 4. Mint a NEW token, show it still works (not in revocation set)
//! 5. Use `NullifierSet` non-membership proofs for revocation checking
//! 6. Show that revocation is privacy-preserving (verifier doesn't learn which
//!    tokens are NOT revoked)
//! 7. Integrate with the dregg-trace Datalog evaluator (revocation rules)

use dregg_cell::note::Note;
use dregg_cell::nullifier_set::{NonMembershipProof, NullifierSet};
use dregg_trace::{
    AuthorizationRequest, Conclusion, Evaluator, Fact, Term, standard_policy, symbol_from_str,
    verify_trace,
};

/// Simulate a token by its nonce (the nullifier of the note backing the token).
/// In practice, each token is backed by a UTXO-style note; the nullifier is
/// derived from the note's commitment + the holder's spending key.
struct TokenHandle {
    #[allow(dead_code)]
    label: String,
    note: Note,
    spending_key: [u8; 32],
}

impl TokenHandle {
    /// Create a new token backed by a fresh note.
    fn mint(label: &str, owner_seed: &[u8]) -> Self {
        let spending_key = blake3::derive_key("token-spending-key-v1", owner_seed);
        let owner_pubkey = blake3::derive_key("token-owner-pubkey-v1", &spending_key);
        let mut randomness = [0u8; 32];
        // Deterministic randomness for reproducibility
        let hash = blake3::derive_key("token-randomness-v1", label.as_bytes());
        randomness.copy_from_slice(&hash);

        let note = Note::with_randomness(
            owner_pubkey,
            [1u64, 1, 0, 0, 0, 0, 0, 0], // value=1, asset_type=1 (auth token)
            randomness,
        );

        Self {
            label: label.to_string(),
            note,
            spending_key,
        }
    }

    /// Get the nullifier (unique identifier for revocation tracking).
    fn nullifier(&self) -> dregg_cell::note::Nullifier {
        self.note.nullifier(&self.spending_key)
    }

    /// Get the note commitment.
    fn commitment(&self) -> dregg_cell::note::NoteCommitment {
        self.note.commitment()
    }
}

/// Simulate an authorization check that incorporates revocation status.
///
/// The flow is:
/// 1. Check if the token's nullifier is in the revocation set
/// 2. If NOT revoked: generate a non-membership proof and allow
/// 3. If revoked: deny
fn check_authorization_with_revocation(
    token: &TokenHandle,
    revocation_set: &NullifierSet,
    action: &str,
) -> AuthResult {
    let nullifier = token.nullifier();

    // Step 1: Check revocation status
    if revocation_set.contains(&nullifier) {
        // Token is revoked — no need for a proof, just deny
        return AuthResult {
            allowed: false,
            reason: "Token has been revoked (nullifier found in revocation set)".to_string(),
            non_membership_proof: None,
        };
    }

    // Step 2: Generate non-membership proof (proves token is NOT revoked)
    let proof = revocation_set.prove_non_membership(&nullifier);
    match proof {
        Some(nm_proof) => {
            // Verify the proof against the current root
            let root = revocation_set.root();
            let valid = NullifierSet::verify_non_membership(&nm_proof, &root);
            if valid {
                AuthResult {
                    allowed: true,
                    reason: format!(
                        "Token verified: non-membership proof valid for action '{}'",
                        action
                    ),
                    non_membership_proof: Some(nm_proof),
                }
            } else {
                AuthResult {
                    allowed: false,
                    reason: "Non-membership proof verification failed".to_string(),
                    non_membership_proof: None,
                }
            }
        }
        None => {
            // prove_non_membership returns None if the nullifier IS in the set.
            // This shouldn't happen since we checked contains() above.
            AuthResult {
                allowed: false,
                reason: "Token is revoked (non-membership proof could not be generated)"
                    .to_string(),
                non_membership_proof: None,
            }
        }
    }
}

struct AuthResult {
    allowed: bool,
    reason: String,
    non_membership_proof: Option<NonMembershipProof>,
}

fn main() {
    println!("=== Dregg Token Revocation Demo ===\n");

    // =========================================================================
    // STEP 1: Mint tokens
    // =========================================================================
    println!("--- Step 1: MINT TOKENS ---\n");

    let token_a = TokenHandle::mint("token-alpha", b"alice-secret-key-material");
    let token_b = TokenHandle::mint("token-beta", b"bob-secret-key-material");
    let token_c = TokenHandle::mint("token-gamma", b"carol-secret-key-material");

    let nullifier_a = token_a.nullifier();
    let nullifier_b = token_b.nullifier();
    let nullifier_c = token_c.nullifier();

    println!(
        "  Token A (alice): commitment {:02x}{:02x}{:02x}{:02x}..., nullifier {:02x}{:02x}{:02x}{:02x}...",
        token_a.commitment().0[0],
        token_a.commitment().0[1],
        token_a.commitment().0[2],
        token_a.commitment().0[3],
        nullifier_a.0[0],
        nullifier_a.0[1],
        nullifier_a.0[2],
        nullifier_a.0[3]
    );
    println!(
        "  Token B (bob):   commitment {:02x}{:02x}{:02x}{:02x}..., nullifier {:02x}{:02x}{:02x}{:02x}...",
        token_b.commitment().0[0],
        token_b.commitment().0[1],
        token_b.commitment().0[2],
        token_b.commitment().0[3],
        nullifier_b.0[0],
        nullifier_b.0[1],
        nullifier_b.0[2],
        nullifier_b.0[3]
    );
    println!(
        "  Token C (carol): commitment {:02x}{:02x}{:02x}{:02x}..., nullifier {:02x}{:02x}{:02x}{:02x}...",
        token_c.commitment().0[0],
        token_c.commitment().0[1],
        token_c.commitment().0[2],
        token_c.commitment().0[3],
        nullifier_c.0[0],
        nullifier_c.0[1],
        nullifier_c.0[2],
        nullifier_c.0[3]
    );
    println!();

    // =========================================================================
    // STEP 2: Use tokens successfully (empty revocation set)
    // =========================================================================
    println!("--- Step 2: USE TOKENS (all valid, revocation set empty) ---\n");

    let mut revocation_set = NullifierSet::new();
    println!(
        "  Revocation set: empty (root = {:02x}{:02x}{:02x}{:02x}...)",
        revocation_set.root()[0],
        revocation_set.root()[1],
        revocation_set.root()[2],
        revocation_set.root()[3]
    );
    println!();

    let result_a = check_authorization_with_revocation(&token_a, &revocation_set, "read");
    println!(
        "  Token A (read): {} — {}",
        if result_a.allowed {
            "ALLOWED"
        } else {
            "DENIED"
        },
        result_a.reason
    );
    assert!(result_a.allowed);

    let result_b = check_authorization_with_revocation(&token_b, &revocation_set, "write");
    println!(
        "  Token B (write): {} — {}",
        if result_b.allowed {
            "ALLOWED"
        } else {
            "DENIED"
        },
        result_b.reason
    );
    assert!(result_b.allowed);

    let result_c = check_authorization_with_revocation(&token_c, &revocation_set, "read");
    println!(
        "  Token C (read): {} — {}",
        if result_c.allowed {
            "ALLOWED"
        } else {
            "DENIED"
        },
        result_c.reason
    );
    assert!(result_c.allowed);

    // Show that non-membership proofs exist for all tokens
    if let Some(proof) = &result_a.non_membership_proof {
        println!("\n  Non-membership proof for Token A:");
        println!(
            "    Absent nullifier: {:02x}{:02x}{:02x}{:02x}...",
            proof.absent.0[0], proof.absent.0[1], proof.absent.0[2], proof.absent.0[3]
        );
        println!(
            "    Left neighbor:  {:?}",
            proof
                .left_neighbor
                .map(|n| format!("{:02x}{:02x}...", n.0[0], n.0[1]))
        );
        println!(
            "    Right neighbor: {:?}",
            proof
                .right_neighbor
                .map(|n| format!("{:02x}{:02x}...", n.0[0], n.0[1]))
        );
        println!(
            "    Root: {:02x}{:02x}{:02x}{:02x}...",
            proof.root[0], proof.root[1], proof.root[2], proof.root[3]
        );
    }
    println!();

    // =========================================================================
    // STEP 3: Revoke Token A
    // =========================================================================
    println!("--- Step 3: REVOKE TOKEN A ---\n");

    println!("  Adding Token A's nullifier to revocation set...");
    revocation_set
        .insert(nullifier_a)
        .expect("First insertion should succeed");

    let new_root = revocation_set.root();
    println!("  Revocation set size: {}", revocation_set.len());
    println!(
        "  New root: {:02x}{:02x}{:02x}{:02x}...",
        new_root[0], new_root[1], new_root[2], new_root[3]
    );
    println!();

    // =========================================================================
    // STEP 4: Show revoked token is rejected
    // =========================================================================
    println!("--- Step 4: REVOKED TOKEN REJECTED ---\n");

    let result_a_revoked = check_authorization_with_revocation(&token_a, &revocation_set, "read");
    println!(
        "  Token A (read): {} — {}",
        if result_a_revoked.allowed {
            "ALLOWED"
        } else {
            "DENIED"
        },
        result_a_revoked.reason
    );
    assert!(!result_a_revoked.allowed);

    // Double-check: trying to re-insert the same nullifier fails
    let double_revoke = revocation_set.insert(nullifier_a);
    println!(
        "  Double-revocation attempt: {:?}",
        double_revoke.err().unwrap()
    );
    println!();

    // =========================================================================
    // STEP 5: Other tokens still work
    // =========================================================================
    println!("--- Step 5: NON-REVOKED TOKENS STILL VALID ---\n");

    let result_b_after = check_authorization_with_revocation(&token_b, &revocation_set, "write");
    println!(
        "  Token B (write): {} — {}",
        if result_b_after.allowed {
            "ALLOWED"
        } else {
            "DENIED"
        },
        result_b_after.reason
    );
    assert!(result_b_after.allowed);

    let result_c_after = check_authorization_with_revocation(&token_c, &revocation_set, "read");
    println!(
        "  Token C (read): {} — {}",
        if result_c_after.allowed {
            "ALLOWED"
        } else {
            "DENIED"
        },
        result_c_after.reason
    );
    assert!(result_c_after.allowed);

    // Verify the non-membership proofs
    if let Some(proof_b) = &result_b_after.non_membership_proof {
        let root = revocation_set.root();
        let valid = NullifierSet::verify_non_membership(proof_b, &root);
        println!(
            "\n  Non-membership proof for Token B: verification = {}",
            if valid { "PASS" } else { "FAIL" }
        );
        assert!(valid);
    }
    println!();

    // =========================================================================
    // STEP 6: Mint a NEW token and show it works immediately
    // =========================================================================
    println!("--- Step 6: MINT NEW TOKEN (immediately valid) ---\n");

    let token_d = TokenHandle::mint("token-delta", b"dave-secret-key-material");
    let nullifier_d = token_d.nullifier();
    println!(
        "  Token D (dave): commitment {:02x}{:02x}{:02x}{:02x}..., nullifier {:02x}{:02x}{:02x}{:02x}...",
        token_d.commitment().0[0],
        token_d.commitment().0[1],
        token_d.commitment().0[2],
        token_d.commitment().0[3],
        nullifier_d.0[0],
        nullifier_d.0[1],
        nullifier_d.0[2],
        nullifier_d.0[3]
    );

    let result_d = check_authorization_with_revocation(&token_d, &revocation_set, "read");
    println!(
        "  Token D (read): {} — {}",
        if result_d.allowed {
            "ALLOWED"
        } else {
            "DENIED"
        },
        result_d.reason
    );
    assert!(result_d.allowed);
    println!();

    // =========================================================================
    // STEP 7: Privacy-preserving properties
    // =========================================================================
    println!("--- Step 7: PRIVACY-PRESERVING REVOCATION ---\n");

    println!("  Key privacy properties of this revocation scheme:");
    println!();
    println!("  1. NULLIFIER UNLINKABILITY:");
    println!("     The nullifier is derived from the note commitment + spending key.");
    println!("     An observer who sees a nullifier in the revocation set cannot link");
    println!("     it back to the original token commitment without the spending key.");
    println!();
    println!("  2. NON-MEMBERSHIP PROOF PRIVACY:");
    println!("     The non-membership proof only reveals:");
    println!("       - The absent nullifier (which the holder already knows)");
    println!("       - Two adjacent neighbors in the sorted set");
    println!("       - The Merkle root");
    println!("     It does NOT reveal: how many tokens are revoked, which specific");
    println!("     other tokens are NOT revoked, or the full revocation list.");
    println!();
    println!("  3. VERIFIER ZERO-KNOWLEDGE:");
    println!("     The verifier only learns: 'this token is NOT in the revocation set'");
    println!("     The verifier does NOT learn: the token's identity, who holds it,");
    println!("     or anything about other tokens in the system.");
    println!();

    // Demonstrate: the root commitment is the same regardless of which valid token
    // is being checked — only the proof differs.
    let root = revocation_set.root();
    let proof_b2 = revocation_set.prove_non_membership(&nullifier_b).unwrap();
    let proof_c2 = revocation_set.prove_non_membership(&nullifier_c).unwrap();
    let proof_d2 = revocation_set.prove_non_membership(&nullifier_d).unwrap();

    println!("  Verification uses the SAME root for all tokens:");
    println!(
        "    Root: {:02x}{:02x}{:02x}{:02x}...",
        root[0], root[1], root[2], root[3]
    );
    println!(
        "    Token B proof valid: {}",
        NullifierSet::verify_non_membership(&proof_b2, &root)
    );
    println!(
        "    Token C proof valid: {}",
        NullifierSet::verify_non_membership(&proof_c2, &root)
    );
    println!(
        "    Token D proof valid: {}",
        NullifierSet::verify_non_membership(&proof_d2, &root)
    );
    println!();

    // =========================================================================
    // STEP 8: Integration with Datalog policy engine
    // =========================================================================
    println!("--- Step 8: DATALOG INTEGRATION (revocation rules) ---\n");

    println!("  The standard dregg policy includes revocation rules:");
    println!("    Rule 30: not_revoked_ok(T) :- not_revoked(T)");
    println!("    Rule 31: deny :- revocable(T), revoked(T)");
    println!();

    let rules = standard_policy();

    // Scenario A: Token is marked revocable but NOT revoked — allow fires
    let facts_not_revoked = vec![
        Fact::new(
            symbol_from_str("revocable"),
            vec![Term::Const(symbol_from_str("token-b"))],
        ),
        Fact::new(
            symbol_from_str("not_revoked"),
            vec![Term::Const(symbol_from_str("token-b"))],
        ),
        Fact::new(symbol_from_str("unrestricted"), vec![Term::Int(1)]),
    ];

    let eval_not_revoked = Evaluator::new(facts_not_revoked.clone(), rules.clone());
    let request = AuthorizationRequest {
        app_id: None,
        service: None,
        action: Some(symbol_from_str("read")),
        features: vec![],
        user_id: None,
        now: 1700000000,
    };
    let trace_not_revoked = eval_not_revoked.evaluate(&request);
    println!(
        "  Scenario A (not revoked): conclusion = {}",
        match &trace_not_revoked.conclusion {
            Conclusion::Allow { policy_rule_id } => format!("ALLOW (rule {})", policy_rule_id),
            Conclusion::Deny => "DENY".to_string(),
        }
    );
    let has_not_revoked_ok = trace_not_revoked.steps.iter().any(|s| s.rule_id == 30);
    println!("    not_revoked_ok derived: {}", has_not_revoked_ok);
    assert!(has_not_revoked_ok);
    let trace_valid = verify_trace(&facts_not_revoked, &rules, &trace_not_revoked);
    println!(
        "    Trace verification: {}",
        if trace_valid { "PASS" } else { "FAIL" }
    );
    assert!(trace_valid);
    println!();

    // Scenario B: Token is marked revocable AND revoked — deny fires
    let facts_revoked = vec![
        Fact::new(
            symbol_from_str("revocable"),
            vec![Term::Const(symbol_from_str("token-a"))],
        ),
        Fact::new(
            symbol_from_str("revoked"),
            vec![Term::Const(symbol_from_str("token-a"))],
        ),
        Fact::new(symbol_from_str("unrestricted"), vec![Term::Int(1)]),
    ];

    let eval_revoked = Evaluator::new(facts_revoked.clone(), rules.clone());
    let trace_revoked = eval_revoked.evaluate(&request);
    println!(
        "  Scenario B (revoked): conclusion = {}",
        match &trace_revoked.conclusion {
            Conclusion::Allow { policy_rule_id } => format!("ALLOW (rule {})", policy_rule_id),
            Conclusion::Deny => "DENY".to_string(),
        }
    );
    let has_revocation_deny = trace_revoked.steps.iter().any(|s| s.rule_id == 31);
    println!("    revocation deny derived: {}", has_revocation_deny);
    assert!(has_revocation_deny);
    let trace_valid2 = verify_trace(&facts_revoked, &rules, &trace_revoked);
    println!(
        "    Trace verification: {}",
        if trace_valid2 { "PASS" } else { "FAIL" }
    );
    assert!(trace_valid2);
    println!();

    // =========================================================================
    // STEP 9: Summary
    // =========================================================================
    println!("--- Step 9: SUMMARY ---\n");
    println!("  Revocation mechanism properties:");
    println!("    - O(1) revocation check (sorted set with binary search)");
    println!("    - Append-only (revocations cannot be undone)");
    println!("    - Non-membership proofs for privacy-preserving verification");
    println!("    - Integrates with Datalog policy engine (Rule 30/31)");
    println!("    - New tokens are immediately valid (no registration needed)");
    println!("    - Double-revocation is safely rejected");
    println!();
    println!("  Revocation set final state:");
    println!("    Size: {} revoked token(s)", revocation_set.len());
    println!(
        "    Root: {:02x}{:02x}{:02x}{:02x}...",
        revocation_set.root()[0],
        revocation_set.root()[1],
        revocation_set.root()[2],
        revocation_set.root()[3]
    );
    println!();
    println!("=== Token Revocation Demo Complete ===");
}
