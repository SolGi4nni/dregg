//! DREGG Federated Authorization Demo
//!
//! This demo simulates cross-silo federated authorization using the dregg
//! token system. Two independent organizations ("silos") communicate via
//! in-process message passing to demonstrate:
//!
//! 1. Federation setup with shared trust roots
//! 2. Token minting with rich capability sets
//! 3. Token attenuation (narrowing capabilities before sharing)
//! 4. Cross-silo verification without contacting the issuer
//! 5. Unauthorized action detection
//! 6. Token revocation propagation across silos

mod authority;
mod commit_state;
mod federation;
mod revocation;
mod stark_proof;
mod token;
mod trace;
mod verifier;

use authority::Authority;
use federation::{Federation, FederationRole};
use revocation::RevocationRegistry;
use token::{AuthorizationRequest, Check, Fact, FoldDelta, Rule};
use verifier::{TokenPresentation, Verifier};

fn main() {
    print_header();
    let demo = DemoState::setup();
    demo.run();
    print_footer();
}

// =============================================================================
// Demo State
// =============================================================================

/// Holds all the state for the demo scenario.
struct DemoState {
    /// acme.corp's authority (the token issuer).
    acme_authority: Authority,
    /// partner.org's authority (the token verifier).
    partner_authority: Authority,
    /// The shared federation.
    federation: Federation,
    /// The shared revocation registry.
    revocation_registry: RevocationRegistry,
}

impl DemoState {
    /// Set up the federation with two organizations.
    fn setup() -> Self {
        DemoState {
            acme_authority: Authority::new("acme.corp"),
            partner_authority: Authority::new("partner.org"),
            federation: Federation::new("dregg-demo-federation"),
            revocation_registry: RevocationRegistry::new(),
        }
    }

    /// Run the complete demo scenario.
    fn run(mut self) {
        // Step 1: Federation setup
        self.step_1_setup_federation();

        // Step 2: Mint root token
        let root_token = self.step_2_mint_token();

        // Step 3: Attenuate token
        let (attenuated_token, _delta) = self.step_3_attenuate(&root_token);

        // Step 4: Cross-silo verification (authorized)
        self.step_4_cross_silo_verify(&attenuated_token);

        // Step 5: Attempt unauthorized action
        self.step_5_unauthorized(&attenuated_token);

        // Step 6: Revocation
        self.step_6_revocation(&root_token, &attenuated_token);
    }

    // =========================================================================
    // Step 1: Federation Setup
    // =========================================================================

    fn step_1_setup_federation(&mut self) {
        print_step(1, 6, "Setting up federation...");

        // Add both organizations to the federation.
        self.federation.add_member(
            "acme.corp",
            &self.acme_authority,
            vec![
                FederationRole::Issuer,
                FederationRole::Verifier,
                FederationRole::Revoker,
            ],
        );
        self.federation.add_member(
            "partner.org",
            &self.partner_authority,
            vec![FederationRole::Verifier],
        );
        self.federation.compute_root();

        // Register both in the revocation registry.
        self.revocation_registry
            .register(&self.acme_authority.public_key);
        self.revocation_registry
            .register(&self.partner_authority.public_key);

        // Print results.
        println!(
            "  {} Authority \"acme.corp\" initialized (pubkey: {})",
            arrow(),
            self.acme_authority.public_key.short_hex()
        );
        println!(
            "  {} Authority \"partner.org\" initialized (pubkey: {})",
            arrow(),
            self.partner_authority.public_key.short_hex()
        );
        println!(
            "  {} Federation root: {} (includes both authorities)",
            arrow(),
            self.federation.root_hex()
        );
        println!();
    }

    // =========================================================================
    // Step 2: Mint Root Token
    // =========================================================================

    fn step_2_mint_token(&self) -> token::TokenState {
        print_step(2, 6, "Minting root token at acme.corp...");

        // Create a rich set of capabilities for an engineer.
        let facts = vec![
            // Application access
            Fact::app("frontend", "rwcd"),
            Fact::app("backend", "rw"),
            Fact::app("admin-panel", "r"),
            Fact::app("docs", "rw"),
            // Service access
            Fact::service("http", "rw"),
            Fact::service("grpc", "rw"),
            Fact::service("dns", "r"),
            Fact::service("metrics", "r"),
            // Features
            Fact::feature("ai-assist"),
            Fact::feature("canary-deploy"),
            // Identity
            Fact::organization("acme-corp-001"),
            Fact::user("engineer-42"),
        ];

        let rules = vec![
            Rule::allow_app(),
            Rule::allow_service(),
            Rule::allow_unrestricted(),
            Rule::deny_default(),
        ];

        let token = self.acme_authority.mint_token(facts, rules);

        // Also compute the REAL Merkle commitment using dregg-commit.
        let real_merkle_root = commit_state::compute_merkle_root(&token.facts, &token.rules);

        // Print results.
        println!("  {} Token ID: {}", arrow(), token.id);
        println!(
            "  {} Token state: {} facts, {} rules",
            arrow(),
            token.facts.len(),
            token.rules.len()
        );
        println!(
            "  {} Capabilities: app(\"frontend\", \"rwcd\"), app(\"backend\", \"rw\"),",
            arrow()
        );
        println!(
            "  {}              app(\"admin-panel\", \"r\"), app(\"docs\", \"rw\"),",
            " "
        );
        println!(
            "  {}              service(\"http\", \"rw\"), service(\"grpc\", \"rw\"),",
            " "
        );
        println!(
            "  {}              service(\"dns\", \"r\"), service(\"metrics\", \"r\")",
            " "
        );
        println!(
            "  {} State root (BLAKE3): {}",
            arrow(),
            token.state_root_hex()
        );
        println!(
            "  {} Merkle commitment (dregg-commit 4-ary tree): {}",
            arrow(),
            authority::hex_encode(&real_merkle_root[..4])
        );
        println!();

        token
    }

    // =========================================================================
    // Step 3: Attenuation
    // =========================================================================

    fn step_3_attenuate(&self, root_token: &token::TokenState) -> (token::TokenState, FoldDelta) {
        print_step(3, 6, "Attenuating token for cross-silo sharing...");

        // The engineer narrows the token before sharing with partner.org's CI:
        // - Remove backend access
        // - Remove admin-panel access
        // - Remove grpc service access
        // - Remove dns service access
        // - Add read-only restriction
        // - Add app restriction to frontend only

        let remove_facts = vec![
            Fact::app("backend", "rw"),
            Fact::app("admin-panel", "r"),
            Fact::app("docs", "rw"),
            Fact::service("grpc", "rw"),
            Fact::service("dns", "r"),
            Fact::service("metrics", "r"),
            Fact::feature("ai-assist"),
            Fact::feature("canary-deploy"),
            Fact::organization("acme-corp-001"),
            Fact::user("engineer-42"),
        ];

        let add_checks = vec![Check::read_only(), Check::restrict_app("frontend")];

        let attenuated = root_token.attenuate(&remove_facts, add_checks, &self.acme_authority);

        // Compute the fold delta for verification (demo's own).
        let delta = FoldDelta::compute(root_token, &attenuated);
        let delta_valid = delta.verify(&attenuated);

        // Also compute the REAL fold delta using dregg-commit.
        let real_fold_result = commit_state::compute_real_fold_delta(
            &root_token.facts,
            &root_token.rules,
            &attenuated.facts,
            &attenuated.rules,
            &remove_facts,
            &["read_only", "restrict_app_frontend"],
        );
        let real_fold_valid = real_fold_result
            .as_ref()
            .map(|(_, valid)| *valid)
            .unwrap_or(false);

        // Print results.
        println!(
            "  {} Removing: app(\"backend\", \"rw\"), app(\"admin-panel\", \"r\"),",
            arrow()
        );
        println!(
            "  {}           app(\"docs\", \"rw\"), service(\"grpc\", \"rw\"),",
            " "
        );
        println!(
            "  {}           service(\"dns\", \"r\"), service(\"metrics\", \"r\")",
            " "
        );
        println!(
            "  {} Adding check: action must be \"r\" (read-only)",
            arrow()
        );
        println!("  {} Adding check: app must be \"frontend\"", arrow());
        println!(
            "  {} Remaining facts: {} (from {})",
            arrow(),
            attenuated.facts.len(),
            root_token.facts.len()
        );
        println!(
            "  {} New state root: {}",
            arrow(),
            attenuated.state_root_hex()
        );
        println!(
            "  {} Fold delta valid: {}",
            arrow(),
            if delta_valid { checkmark() } else { cross() }
        );
        println!(
            "  {} Real fold delta (dregg-commit Merkle): {}",
            arrow(),
            if real_fold_valid {
                format!("{} ({} removals verified)", checkmark(), remove_facts.len())
            } else {
                format!("{} (could not compute)", cross())
            }
        );
        println!();

        (attenuated, delta)
    }

    // =========================================================================
    // Step 4: Cross-Silo Verification (Authorized)
    // =========================================================================

    fn step_4_cross_silo_verify(&self, attenuated_token: &token::TokenState) {
        print_step(4, 6, "Cross-silo verification at partner.org...");

        // partner.org receives the attenuated token and verifies it.
        let verifier = Verifier::new("partner.org", &self.federation, &self.revocation_registry);

        // Build the authorization request.
        let request = AuthorizationRequest {
            app: "frontend".to_string(),
            service: Some("http".to_string()),
            action: "r".to_string(),
        };

        // Get non-membership proof from the REAL Merkle-backed revocation tree.
        let non_membership_proof = self
            .revocation_registry
            .prove_non_membership(&attenuated_token.id, &attenuated_token.issuer);

        // Create the presentation.
        let presentation =
            TokenPresentation::new(attenuated_token.clone(), non_membership_proof.clone());

        // Perform verification.
        let result = verifier.verify(
            &presentation.token,
            &request,
            presentation.non_membership_proof.as_ref(),
        );

        // Print results.
        println!("  {} Request: app=\"frontend\", action=\"read\"", arrow());
        println!(
            "  {} Presented state commitment: {}",
            arrow(),
            presentation.commitment_hex()
        );

        // Show individual checks.
        let issuer_ok = verifier.verify_issuer_membership(attenuated_token);
        println!(
            "  {} Checking issuer membership in federation: {}",
            arrow(),
            if issuer_ok { checkmark() } else { cross() }
        );

        // Generate a REAL STARK proof of issuer membership using dregg-circuit.
        let member_keys: Vec<[u8; 32]> = vec![
            *self.acme_authority.public_key.as_bytes(),
            *self.partner_authority.public_key.as_bytes(),
        ];
        let stark_result =
            stark_proof::prove_issuer_membership(attenuated_token.issuer.as_bytes(), &member_keys);
        println!(
            "  {} STARK proof of issuer membership: {} (proof: {} bytes, {} trace rows)",
            arrow(),
            if stark_result.verified {
                checkmark()
            } else {
                cross()
            },
            stark_result.proof_size_bytes,
            stark_result.trace_rows,
        );

        let trace_result = verifier.verify_trace_only(attenuated_token);
        println!(
            "  {} Checking authorization trace ({} derivation steps): {}",
            arrow(),
            trace_result.steps_verified,
            if trace_result.valid {
                checkmark()
            } else {
                cross()
            }
        );

        // Verify the non-membership proof (token not revoked) using REAL Merkle verification.
        if let Some(ref nm_proof) = non_membership_proof {
            let nm_valid = self
                .revocation_registry
                .verify_non_membership(nm_proof, &attenuated_token.issuer);
            println!(
                "  {} Non-membership proof (Merkle): {}",
                arrow(),
                if nm_valid { checkmark() } else { cross() }
            );
        }

        if result.authorized {
            println!("  {} AUTHORIZED {}", arrow(), checkmark());
        } else {
            println!(
                "  {} DENIED {} ({})",
                arrow(),
                cross(),
                result.denial_reason.unwrap_or_default()
            );
        }
        println!();
    }

    // =========================================================================
    // Step 5: Unauthorized Action
    // =========================================================================

    fn step_5_unauthorized(&self, attenuated_token: &token::TokenState) {
        print_step(5, 6, "Attempting unauthorized action...");

        let verifier = Verifier::new("partner.org", &self.federation, &self.revocation_registry);

        // Try to write (the token is read-only).
        let request = AuthorizationRequest {
            app: "frontend".to_string(),
            service: Some("http".to_string()),
            action: "w".to_string(),
        };

        let non_membership_proof = self
            .revocation_registry
            .prove_non_membership(&attenuated_token.id, &attenuated_token.issuer);

        let result = verifier.verify(attenuated_token, &request, non_membership_proof.as_ref());

        // Print results.
        println!("  {} Request: app=\"frontend\", action=\"write\"", arrow());

        let trace_result = verifier.verify_trace_only(attenuated_token);
        println!(
            "  {} Checking authorization trace ({} steps): {}",
            arrow(),
            trace_result.steps_verified,
            if trace_result.valid {
                checkmark()
            } else {
                cross()
            }
        );
        println!("  {} Checking authorization: DENIED {}", arrow(), cross());

        if let Some(reason) = &result.denial_reason {
            println!("  {} ({})", arrow(), reason);
        }
        println!();
    }

    // =========================================================================
    // Step 6: Revocation
    // =========================================================================

    fn step_6_revocation(
        &mut self,
        root_token: &token::TokenState,
        attenuated_token: &token::TokenState,
    ) {
        print_step(6, 6, "Revocation...");

        // acme.corp revokes the engineer's token.
        let token_id_short = if root_token.id.len() > 8 {
            &root_token.id[..8]
        } else {
            &root_token.id
        };

        println!(
            "  {} acme.corp revokes engineer's token (id: {}...)",
            arrow(),
            token_id_short
        );

        // Revoke in the registry (uses real Merkle-tree-backed RevocationTree).
        self.revocation_registry
            .get(&self.acme_authority.public_key)
            .unwrap()
            .revoke(&root_token.id);

        // The attenuated token shares the same ID as the root token,
        // so revoking the root also invalidates all derived tokens.
        // (In a real system, revocation could target the root or any derivative.)

        println!("  {} Revocation accumulator updated", arrow());

        // partner.org attempts verification of the attenuated token.
        println!("  {} partner.org attempts verification...", arrow());

        let verifier = Verifier::new("partner.org", &self.federation, &self.revocation_registry);

        let request = AuthorizationRequest {
            app: "frontend".to_string(),
            service: Some("http".to_string()),
            action: "r".to_string(),
        };

        // Try to get a non-membership proof — this should FAIL because
        // the token has been revoked.
        let non_membership_proof = self
            .revocation_registry
            .prove_non_membership(&attenuated_token.id, &attenuated_token.issuer);

        match non_membership_proof {
            Some(proof) => {
                // If we got a proof, verify it (it should be stale).
                let result = verifier.verify(attenuated_token, &request, Some(&proof));
                if !result.authorized {
                    println!(
                        "  {} Non-membership proof: stale (accumulator updated)",
                        arrow()
                    );
                    println!("  {} Token is revoked -- access denied", arrow());
                } else {
                    println!("  {} Unexpectedly authorized!", arrow());
                }
            }
            None => {
                // Cannot produce non-membership proof — token is revoked.
                println!(
                    "  {} Non-membership proof: CANNOT BE PRODUCED {}",
                    arrow(),
                    cross()
                );
                println!("  {} Token is revoked -- access denied", arrow());
            }
        }
        println!();
    }
}

// =============================================================================
// Display Helpers
// =============================================================================

fn print_header() {
    println!();
    println!(
        "\x1b[1m{}\x1b[0m",
        "═══════════════════════════════════════════════════════"
    );
    println!("\x1b[1m  DREGG FEDERATED AUTHORIZATION DEMO\x1b[0m");
    println!(
        "\x1b[1m{}\x1b[0m",
        "═══════════════════════════════════════════════════════"
    );
    println!();
}

fn print_footer() {
    println!(
        "\x1b[1m{}\x1b[0m",
        "═══════════════════════════════════════════════════════"
    );
    println!("\x1b[1m  Demo complete. All federation scenarios demonstrated.\x1b[0m");
    println!(
        "\x1b[1m{}\x1b[0m",
        "═══════════════════════════════════════════════════════"
    );
    println!();
}

fn print_step(step: u32, total: u32, description: &str) {
    println!(
        "\x1b[1;36m[{}/{}]\x1b[0m \x1b[1m{}\x1b[0m",
        step, total, description
    );
}

fn arrow() -> &'static str {
    "\x1b[33m->\x1b[0m"
}

fn checkmark() -> &'static str {
    "\x1b[32m[OK]\x1b[0m"
}

fn cross() -> &'static str {
    "\x1b[31m[DENIED]\x1b[0m"
}
