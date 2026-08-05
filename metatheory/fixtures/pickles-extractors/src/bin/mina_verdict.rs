//! **THE VERDICT — hand a proof we produced to MINA'S OWN SIDE-LOADED VERIFIER and print what it
//! says, check by named check.**
//!
//! ## The gap this closes
//!
//! This tree could DERIVE a key Mina parses (`pickles-vk-derive`; one is devnet account state),
//! ENCODE a proof Mina parses (`bin/pickles_proof_wire.rs`), and MARSHAL a kimchi proof we produced
//! into that encoding (`src/marshal.rs`, `bin/pickles_kimchi_marshal.rs`). Every one of those is a
//! READER gate: `vkToCircuit` and `proofOfBase64` reconstruct a record and consult no key, no
//! public input and no field arithmetic. Nothing in the tree had ever run Mina's actual side-loaded
//! **verification** on an artifact of ours.
//!
//! This binary does. `ledger::proofs::verification::verify_zkapp` (openmina
//! `crates/ledger/src/proofs/verification.rs:829`) is the function
//! `Verifier::verify_commands` calls for every zkApp proof on the network
//! (`crates/ledger/src/verifier/mod.rs:175-178`). It is called here with:
//!
//!   * the **verification key the devnet account holds** — the 1796 bytes read back over GraphQL,
//!     not a local copy — parsed by openmina's own `MinaBaseVerificationKeyWireStableV1::from_base64`
//!     and `TryFrom` into `ledger::account::VerificationKey`;
//!   * a **proof marshalled from a kimchi proof of the Lean-emitted `wrap_main` circuit**
//!     (`Dregg2.Circuit.Emit.KimchiWrapMain`), read back through openmina's own `binprot_read`.
//!
//! ## ⚑ What the run prints, and why it is printed in this order
//!
//! `verify_zkapp` is `accumulator_check && verify_impl`, and `verify_impl` is a chain. Reported as
//! a chain, because "false" from the top names nothing:
//!
//!   1. **the verifier index Mina builds from those 1796 bytes** — `make_zkapp_verifier_index`
//!      (`verifiers.rs:396`). The account carries only 28 curve points and two enum tags; the
//!      domain, `public`, `prev_challenges`, `zk_rows`, `max_poly_size` and every feature flag are
//!      SYNTHESIZED by that function. Printing them is printing Mina's demand at its source, rather
//!      than reciting it from a comment.
//!   2. **the shape of the proof we handed it**, beside that demand.
//!   3. **`accumulator_check`** (`accumulator_check.rs:10`) on its own — the Vesta-side dlog
//!      accumulator check, which runs before anything else and is `&&`-ed in.
//!   4. **`verify_zkapp` itself.** Its inner `run_checks` and `verify_with` print their own
//!      diagnostics to stderr (`verification.rs:557-674`, `:889-891`), which is the literal text
//!      this binary exists to surface. Run it with stderr attached.
//!
//! ## Scope — read before quoting
//!
//! Everything here is openmina's code operating on our bytes. A `false` is Mina's verdict on this
//! artifact and nothing more; it is not a statement about `wrap_main`, about the Lean assembly, or
//! about any other artifact. A `true` would likewise be a statement about exactly this pair.
//!
//! RUN
//!   cargo run --release --manifest-path metatheory/fixtures/pickles-extractors/Cargo.toml \
//!     --bin mina_verdict -- --vk <vk.json> --proof <marshalled.binprot>

use std::sync::Arc;

use ark_ec::AffineRepr;
use ledger::proofs::accumulator_check::accumulator_check;
use ledger::proofs::verification::verify_zkapp;
use ledger::proofs::verifiers::make_zkapp_verifier_index;
use ledger::scan_state::transaction_logic::zkapp_statement::{
    TransactionCommitment, ZkappStatement,
};
use ledger::verifier::get_srs;
use mina_curves::pasta::Fp;
use mina_p2p_messages::binprot::BinProtRead;
use mina_p2p_messages::v2::{
    MinaBaseVerificationKeyWireStableV1, PicklesProofProofsVerified2ReprStableV2,
};

/// The devnet account whose verification key was derived from the Lean-emitted gates.
/// Recorded in `bridge/mina-zkapp/devnet-foreign-vk-registration.json`.
const REGISTERED_ACCOUNT: &str = "B62qrKdXQqNnhmszatQHMX9cLTKZUSYqadrBcmAHGAHQANm2b7Td1rm";

#[derive(serde::Deserialize)]
struct VkJson {
    data: String,
    #[serde(default)]
    hash: String,
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut vk_path = None;
    let mut proof_path = None;
    let mut label = String::from("(unlabelled)");
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--vk" => {
                vk_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--proof" => {
                proof_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--label" => {
                label = args[i + 1].clone();
                i += 2;
            }
            "--probe-vesta-generator" => i += 1,
            other => panic!("unknown argument {other}"),
        }
    }
    let vk_path = vk_path.expect("--vk <vk.json> (a {data, hash} record)");
    let proof_path = proof_path.expect("--proof <marshalled.binprot>");
    // ⚑ A PROBE, AND IT IS NOT THE VERDICT. `StatementProofState::try_from` ABORTS the process on
    // an off-Vesta `messages_for_next_wrap_proof.challenge_polynomial_commitment`, so the refusal
    // it raises HIDES every check after it. This flag substitutes the Vesta GENERATOR — an
    // obviously-not-real point, chosen so nothing can mistake the result for a working artifact —
    // purely to let the conversion complete and reveal what Mina objects to NEXT. It makes the
    // accumulator check false, which it already was. Any verdict printed under this flag is a
    // verdict about a HAND-ALTERED record and is labelled as such wherever it is quoted.
    let probe_vesta_generator = std::env::args().any(|a| a == "--probe-vesta-generator");

    println!("MINA VERDICT — openmina `verify_zkapp`, the function the network calls for every zkApp proof");
    println!("  openmina : ledger::proofs::verification::verify_zkapp (crates/ledger/src/proofs/verification.rs:829)");
    println!("  case     : {label}");
    println!("  vk       : {vk_path}");
    println!("  proof    : {proof_path}");
    println!("  (the registered devnet account for the Lean-derived key is {REGISTERED_ACCOUNT})");

    // ── the key, through openmina's own reader ────────────────────────────────────────────────
    let vk_json: VkJson =
        serde_json::from_str(&std::fs::read_to_string(&vk_path).expect("read vk json"))
            .expect("vk json");
    let wire = MinaBaseVerificationKeyWireStableV1::from_base64(&vk_json.data)
        .expect("openmina refused the base64 verification key");
    let vk: ledger::account::VerificationKey = (&wire)
        .try_into()
        .expect("openmina refused to build a VerificationKey from the wire record");
    println!(
        "\n[key] openmina parsed it: max_proofs_verified={:?} actual_wrap_domain_size={:?}  (stored hash {})",
        vk.max_proofs_verified, vk.actual_wrap_domain_size, vk_json.hash
    );

    // ── (1) the demand, read off the index MINA builds from those bytes ───────────────────────
    let index = make_zkapp_verifier_index(&vk);
    println!("\n[1] the verifier index MINA synthesizes from the account's 28 points + 2 tags");
    println!(
        "      (make_zkapp_verifier_index, verifiers.rs:396 — none of this comes from the account)"
    );
    println!(
        "      domain            = 2^{}",
        index.domain.log_size_of_group
    );
    println!("      public            = {}", index.public);
    println!("      prev_challenges   = {}", index.prev_challenges);
    println!("      zk_rows           = {}", index.zk_rows);
    println!(
        "      max_poly_size     = 2^{}",
        (index.max_poly_size as f64).log2() as u32
    );
    let g = index.sigma_comm[0].chunks[0];
    println!(
        "      sigma_comm[0]     = ({}, {})   [the key's own first commitment, so the index is this key's]",
        g.x, g.y
    );

    // ── (2) the proof we produced ─────────────────────────────────────────────────────────────
    let bytes = std::fs::read(&proof_path).expect("read proof binprot");
    let mut cursor = bytes.as_slice();
    let mut proof = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut cursor)
        .expect("openmina refused to read the proof");
    if probe_vesta_generator {
        let g = mina_curves::pasta::Vesta::generator();
        proof
            .statement
            .proof_state
            .messages_for_next_wrap_proof
            .challenge_polynomial_commitment = (g.x.into(), g.y.into());
        println!("\n⚠ PROBE ACTIVE: messages_for_next_wrap_proof.challenge_polynomial_commitment");
        println!("   replaced by the VESTA GENERATOR so the conversion does not abort. Everything");
        println!(
            "   below this line is a verdict about a HAND-ALTERED record, not about our artifact."
        );
    }
    let proof = proof;
    println!(
        "\n[2] the proof, through openmina's own binprot_read: {} bytes, {} trailing",
        bytes.len(),
        cursor.len()
    );
    println!(
        "      bulletproof lr rounds      = {}",
        proof.proof.bulletproof.lr.len()
    );
    println!(
        "      deferred bulletproof chals = {}",
        proof
            .statement
            .proof_state
            .deferred_values
            .bulletproof_challenges
            .len()
    );
    println!(
        "      old_bulletproof_challenges = {}",
        proof
            .statement
            .proof_state
            .messages_for_next_wrap_proof
            .old_bulletproof_challenges
            .len()
    );

    // ── (2b) WHICH CURVE is the next-wrap accumulator on? ─────────────────────────────────────
    // Measured against a REAL Mina block proof, because `messages_for_next_wrap_proof.
    // challenge_polynomial_commitment` is two bare BigInts on the wire and BOTH readers this tree
    // already gates on (`binprot_read`, `Pickles.proofOfBase64`) accept it without ever asking
    // whether the pair is a point. `StatementProofState::try_from` (step.rs) is where Mina decides,
    // and it decides by CONSTRUCTING an `Affine<VestaParameters>` — which panics off-curve rather
    // than erroring. So the group is not a convention to look up; it is measurable.
    let on_curve = |x: &mina_p2p_messages::bigint::BigInt,
                    y: &mina_p2p_messages::bigint::BigInt| {
        let vesta = match (
            x.to_field::<mina_curves::pasta::Fq>(),
            y.to_field::<mina_curves::pasta::Fq>(),
        ) {
            (Ok(x), Ok(y)) => mina_curves::pasta::Vesta::new_unchecked(x, y).is_on_curve(),
            _ => false,
        };
        let pallas = match (
            x.to_field::<mina_curves::pasta::Fp>(),
            y.to_field::<mina_curves::pasta::Fp>(),
        ) {
            (Ok(x), Ok(y)) => mina_curves::pasta::Pallas::new_unchecked(x, y).is_on_curve(),
            _ => false,
        };
        (vesta, pallas)
    };
    let ours = &proof
        .statement
        .proof_state
        .messages_for_next_wrap_proof
        .challenge_polynomial_commitment;
    let (v, p) = on_curve(&ours.0, &ours.1);
    println!(
        "\n[2b] statement.proof_state.messages_for_next_wrap_proof.challenge_polynomial_commitment"
    );
    println!("      OURS  : on Vesta = {v}   on Pallas = {p}");
    for f in std::env::var("MINA_VERDICT_REAL_PROOFS")
        .unwrap_or_default()
        .split(':')
        .filter(|s| !s.is_empty())
    {
        let bytes = std::fs::read(f).expect("read real proof binprot");
        let mut c = bytes.as_slice();
        let rp = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut c)
            .expect("openmina refused a real block proof");
        let r = &rp
            .statement
            .proof_state
            .messages_for_next_wrap_proof
            .challenge_polynomial_commitment;
        let (v, p) = on_curve(&r.0, &r.1);
        println!(
            "      REAL  : on Vesta = {v}   on Pallas = {p}   ({})",
            std::path::Path::new(f)
                .file_name()
                .unwrap()
                .to_string_lossy()
        );
    }

    // ── (3) the accumulator check, alone ──────────────────────────────────────────────────────
    let srs = get_srs::<Fp>();
    let acc = accumulator_check(&srs, &[&proof]);
    println!(
        "\n[3] accumulator_check (accumulator_check.rs:10, the Vesta-side dlog check, &&-ed first)"
    );
    println!("      = {acc:?}");

    // ── (4) the whole thing ───────────────────────────────────────────────────────────────────
    // The app state a zkApp proof is verified against is two field elements (`ZkappStatement`,
    // zkapp_statement.rs:50-63). They are the account-update and calls commitments of the
    // transaction the proof would authorize. We are not authorizing a transaction, so there is no
    // true value to supply; zero is used and SAID, because the two words are hashed into
    // `messages_for_next_step_proof` and therefore into the public input, so they are part of what
    // is being checked and not a free parameter.
    let zkapp_statement = ZkappStatement {
        account_update: TransactionCommitment(Fp::from(0u64)),
        calls: TransactionCommitment(Fp::from(0u64)),
    };
    println!("\n[4] verify_zkapp(vk, zkapp_statement = (0, 0), proof, srs)");
    println!(
        "      stderr below is openmina's own diagnostics (run_checks + the kimchi VerifyError)"
    );
    println!("      ------------------------------------------------------------------");
    let srs_ref: &poly_commitment::ipa::SRS<mina_curves::pasta::Vesta> = Arc::as_ref(&srs);
    // ⚑ CATCH THE PANIC. `StatementProofState::try_from` builds curve points with
    // `Affine::new`, which ASSERTS on-curve rather than returning an error — so a wire record Mina
    // rejects for that reason aborts the process instead of producing a verdict. Catching it is
    // what makes the refusal reportable; the panic message is still printed by the default hook.
    let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify_zkapp(&vk, &zkapp_statement, &proof, srs_ref)
    }));
    println!("      ------------------------------------------------------------------");
    match &ok {
        Ok(v) => println!("      verify_zkapp = {v}"),
        Err(_) => println!(
            "      verify_zkapp PANICKED — see the assertion above; Mina refused by aborting, not by returning false"
        ),
    }

    println!(
        "\nMINA_VERDICT={}",
        match ok {
            Ok(true) => "ACCEPT",
            Ok(false) => "REFUSE",
            Err(_) => "REFUSE-BY-PANIC",
        }
    );
}
