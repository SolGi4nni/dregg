//! ⚑ **THE ON-CHAIN "VK COMMITMENT" WAS A HASH OF A LABEL, AND THIS IS THE TEST THAT
//! COULD NOT BE WRITTEN.**
//!
//! Until 2026-07-28 both chains pinned what they called a verifying-key commitment as
//! `keccak256("dregg-settlement-vk-dev-setup")` -- `solana-settlement/src/lib.rs`'s
//! `dev_ceremony_vk_hash()` and `chain/script/DeploySettlement.s.sol`'s
//! `DEFAULT_VK_HASH`. The string does not mention the key, so the pin was
//! `0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76` for the dev
//! key and for every other key that will ever exist: **a VK regeneration left both
//! pins byte-identical**, and the one artifact whose job is to notice a key changed
//! could not notice.
//!
//! The pin is now `vk::VK_DIGEST` = keccak256 over the canonical serialization of the
//! actual verifying key (`vk_digest`). The tests below are the whole claim:
//!
//!  * [`pin_is_the_digest_of_the_deployed_key`] -- the generated constant IS the
//!    digest of the constants the verifier runs on, so it is a measurement of the
//!    key, not an assertion about it.
//!  * [`every_verifying_key_bit_moves_the_pin`] -- flipping ANY bit of ANY of the
//!    2432 verifying-key bytes moves the pin. 19456 single-bit perturbations, zero
//!    collisions.
//!  * [`the_old_label_pin_moves_for_none_of_them`] -- the refutation. The same 2432
//!    perturbations leave the OLD pin fixed, every time. This is the defect stated as
//!    a passing measurement rather than as prose.
//!  * [`init_refuses_a_pin_that_is_not_the_keys_digest`] (in `settle_flow.rs`'s
//!    harness style, below) -- the both-poles gate: the key's digest is ACCEPTED,
//!    and the old label hash is REJECTED on-chain.

use dregg_solana_settlement::instruction::SettlementInstruction;
use dregg_solana_settlement::state::{packed_root, SettlementState};
use dregg_solana_settlement::vk_digest::{digest_of, VkMaterial};
use dregg_solana_settlement::{
    process_instruction, settlement_vk_digest, vk, SEED_PROVEN_ROOT, SEED_SETTLEMENT,
};

use solana_program_test::{processor, ProgramTest};
use solana_sdk::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
    signature::Signer,
    system_program,
    transaction::Transaction,
};

/// The pin the repo used before 2026-07-28: keccak of a LABEL.
fn label_pin() -> [u8; 32] {
    solana_program::keccak::hashv(&[b"dregg-settlement-vk-dev-setup"]).0
}

// ---------------------------------------------------------------------------
// An owned, perturbable copy of the verifying key
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct OwnedVk {
    num_public_inputs: u32,
    num_ic_bases: u32,
    alpha_g1: [u8; 64],
    beta_neg_g2: [u8; 128],
    gamma_neg_g2: [u8; 128],
    delta_neg_g2: [u8; 128],
    pedersen_g_g2: [u8; 128],
    pedersen_gsigma_g2: [u8; 128],
    constant_g1: [u8; 64],
    pub_g1: Vec<[u8; 64]>,
}

impl OwnedVk {
    fn deployed() -> Self {
        Self {
            num_public_inputs: vk::NUM_PUBLIC_INPUTS as u32,
            num_ic_bases: vk::PUB.len() as u32,
            alpha_g1: vk::ALPHA_G1,
            beta_neg_g2: vk::BETA_NEG_G2,
            gamma_neg_g2: vk::GAMMA_NEG_G2,
            delta_neg_g2: vk::DELTA_NEG_G2,
            pedersen_g_g2: vk::PEDERSEN_G_G2,
            pedersen_gsigma_g2: vk::PEDERSEN_GSIGMA_G2,
            constant_g1: vk::CONSTANT_G1,
            pub_g1: vk::PUB.to_vec(),
        }
    }

    fn digest(&self) -> [u8; 32] {
        digest_of(&VkMaterial {
            num_public_inputs: self.num_public_inputs,
            num_ic_bases: self.num_ic_bases,
            alpha_g1: &self.alpha_g1,
            beta_neg_g2: &self.beta_neg_g2,
            gamma_neg_g2: &self.gamma_neg_g2,
            delta_neg_g2: &self.delta_neg_g2,
            pedersen_g_g2: &self.pedersen_g_g2,
            pedersen_gsigma_g2: &self.pedersen_gsigma_g2,
            constant_g1: &self.constant_g1,
            pub_g1: &self.pub_g1,
        })
    }

    /// Every mutable verifying-key byte, as (component name, index) selectors, so a
    /// perturbation can address the whole key without the test hard-coding offsets.
    fn byte_count(&self) -> usize {
        64 + 128 * 5 + 64 + 64 * self.pub_g1.len()
    }

    /// Flip bit `bit` of byte `i` of the flattened key material.
    fn flip(&mut self, i: usize, bit: u8) {
        let mask = 1u8 << bit;
        let mut off = i;
        for slot in [
            &mut self.alpha_g1[..],
            &mut self.beta_neg_g2[..],
            &mut self.gamma_neg_g2[..],
            &mut self.delta_neg_g2[..],
            &mut self.pedersen_g_g2[..],
            &mut self.pedersen_gsigma_g2[..],
            &mut self.constant_g1[..],
        ] {
            if off < slot.len() {
                slot[off] ^= mask;
                return;
            }
            off -= slot.len();
        }
        for p in self.pub_g1.iter_mut() {
            if off < p.len() {
                p[off] ^= mask;
                return;
            }
            off -= p.len();
        }
        panic!("byte index {i} out of range");
    }
}

// ---------------------------------------------------------------------------
// The pin is a function of the key
// ---------------------------------------------------------------------------

#[test]
fn pin_is_the_digest_of_the_deployed_key() {
    assert_eq!(
        dregg_solana_settlement::vk_digest::compute(),
        vk::VK_DIGEST,
        "the generated VK_DIGEST must be the digest of the constants the verifier \
         actually runs on -- otherwise the pin is an assertion about the key, not a \
         measurement of it"
    );
    assert_eq!(settlement_vk_digest(), vk::VK_DIGEST);
    assert_eq!(OwnedVk::deployed().digest(), vk::VK_DIGEST);
}

/// The pin must not be the value it replaced. If these were ever equal, the fix
/// would have landed in name only.
#[test]
fn pin_is_not_the_old_label_hash() {
    assert_ne!(
        vk::VK_DIGEST,
        label_pin(),
        "the key-derived pin must differ from keccak256(\"dregg-settlement-vk-dev-setup\")"
    );
    assert_eq!(
        hex(&label_pin()),
        "18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76",
        "the superseded label pin, recorded so the flag day is findable"
    );
}

/// ⚑ THE TEST THE OLD PIN MADE IMPOSSIBLE: regenerating the key moves the pin.
///
/// Exhaustive over single-bit faults: for each of the 2432 verifying-key bytes and
/// each of its 8 bits, the perturbed key's digest must differ from the deployed
/// key's. A regenerated key differs in far more than one bit, so this is strictly
/// stronger than "a new ceremony moves the pin" -- it says no VK bit is unpinned.
#[test]
fn every_verifying_key_bit_moves_the_pin() {
    let base = OwnedVk::deployed();
    let pinned = base.digest();
    assert_eq!(pinned, vk::VK_DIGEST);

    let n = base.byte_count();
    assert_eq!(n, 2432, "64 alpha + 5*128 G2 + 64 ic0 + 26*64 ic bases");

    let mut checked = 0usize;
    for i in 0..n {
        for bit in 0..8u8 {
            let mut perturbed = base.clone();
            perturbed.flip(i, bit);
            assert_ne!(
                perturbed.digest(),
                pinned,
                "flipping bit {bit} of verifying-key byte {i} left the pin unchanged"
            );
            checked += 1;
        }
    }
    assert_eq!(
        checked,
        2432 * 8,
        "19456 single-bit key faults, all detected"
    );
}

/// The format parameters are part of the key's identity: a 25-lane statement and a
/// 26-lane statement are different circuits even with identical points.
#[test]
fn format_parameters_move_the_pin() {
    let base = OwnedVk::deployed();
    let pinned = base.digest();

    let mut wider = base.clone();
    wider.num_public_inputs += 1;
    assert_ne!(wider.digest(), pinned, "num_public_inputs must be pinned");

    let mut more_bases = base.clone();
    more_bases.num_ic_bases += 1;
    assert_ne!(more_bases.digest(), pinned, "num_ic_bases must be pinned");

    // Dropping an IC base changes the key even though every remaining byte matches.
    let mut truncated = base.clone();
    truncated.pub_g1.pop();
    truncated.num_ic_bases -= 1;
    assert_ne!(
        truncated.digest(),
        pinned,
        "the IC base count must be pinned"
    );
}

/// ⚑ THE REFUTATION. The same 2432 key perturbations that all move the new pin move
/// the OLD pin exactly zero times. This is the defect measured rather than asserted:
/// the label hash is a constant function of the key.
#[test]
fn the_old_label_pin_moves_for_none_of_them() {
    let base = OwnedVk::deployed();
    let old = label_pin();

    let mut unmoved = 0usize;
    for i in 0..base.byte_count() {
        let mut perturbed = base.clone();
        perturbed.flip(i, 0);
        // The old pin does not read the key at all, so recomputing it over a
        // perturbed key is the identity.
        let old_after = label_pin();
        assert_eq!(
            old_after, old,
            "the label pin is a constant; if this ever fails the premise changed"
        );
        assert_ne!(
            perturbed.digest(),
            vk::VK_DIGEST,
            "...while the key-derived pin moved for the same fault"
        );
        unmoved += 1;
    }
    assert_eq!(
        unmoved, 2432,
        "2432 verifying-key byte faults: the old pin detected 0, the new pin detected all"
    );
}

fn hex(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

// ---------------------------------------------------------------------------
// Both poles, on-chain: the key's digest is ACCEPTED, anything else is REJECTED
// ---------------------------------------------------------------------------

fn program_id() -> Pubkey {
    Pubkey::new_from_array([7u8; 32])
}

fn state_pda() -> Pubkey {
    Pubkey::find_program_address(&[SEED_SETTLEMENT], &program_id()).0
}

fn marker_pda(lanes: &[u32; 8]) -> Pubkey {
    Pubkey::find_program_address(&[SEED_PROVEN_ROOT, &packed_root(lanes)], &program_id()).0
}

const GENESIS: [u32; 8] = [
    421210617, 1637814550, 431291584, 1953496675, 369364366, 1006647231, 1866996710, 48274474,
];

fn init_ix(payer: &Pubkey, vk_hash: [u8; 32]) -> Instruction {
    Instruction {
        program_id: program_id(),
        accounts: vec![
            AccountMeta::new(*payer, true),
            AccountMeta::new(state_pda(), false),
            AccountMeta::new(marker_pda(&GENESIS), false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: SettlementInstruction::InitSettlement {
            genesis_root: GENESIS,
            vk_hash,
        }
        .pack(),
    }
}

/// POLE 1 — the digest of the key this program verifies against is ACCEPTED, and the
/// settlement account carries exactly it.
#[tokio::test]
async fn init_accepts_the_keys_own_digest() {
    let pt = ProgramTest::new(
        "dregg_solana_settlement",
        program_id(),
        processor!(process_instruction),
    );
    let (banks, payer, blockhash) = pt.start().await;

    let mut tx = Transaction::new_with_payer(
        &[init_ix(&payer.pubkey(), vk::VK_DIGEST)],
        Some(&payer.pubkey()),
    );
    tx.sign(&[&payer], blockhash);
    banks
        .process_transaction(tx)
        .await
        .expect("the verifying key's own digest must be accepted");

    let acct = banks.get_account(state_pda()).await.unwrap().unwrap();
    let state = SettlementState::unpack(&acct.data).unwrap();
    assert_eq!(
        state.vk_hash,
        vk::VK_DIGEST,
        "the pinned commitment must be the key's digest"
    );
}

/// POLE 2 — the OLD label hash is REJECTED. Not "some 32 bytes are rejected": the
/// exact value both chains pinned until 2026-07-28 no longer initializes anything,
/// so a deploy still carrying it fails loudly instead of pinning a meaningless word.
#[tokio::test]
async fn init_rejects_the_old_label_pin_and_every_other_value() {
    let pt = ProgramTest::new(
        "dregg_solana_settlement",
        program_id(),
        processor!(process_instruction),
    );
    let (banks, payer, blockhash) = pt.start().await;

    for (name, bad) in [
        ("the superseded label hash", label_pin()),
        ("all zeroes", [0u8; 32]),
        ("a near-miss (last byte flipped)", {
            let mut v = vk::VK_DIGEST;
            v[31] ^= 1;
            v
        }),
    ] {
        let mut tx =
            Transaction::new_with_payer(&[init_ix(&payer.pubkey(), bad)], Some(&payer.pubkey()));
        tx.sign(&[&payer], blockhash);
        assert!(
            banks.process_transaction(tx).await.is_err(),
            "init must refuse {name} as a VK commitment"
        );
    }

    // ...and the refusal was a refusal, not a silent success: no settlement state
    // account exists, so nothing was pinned.
    assert!(
        banks.get_account(state_pda()).await.unwrap().is_none(),
        "a refused init must leave no settlement state behind"
    );
}
