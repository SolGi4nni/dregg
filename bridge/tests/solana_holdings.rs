//! **Non-custodial proof-of-holdings** — the load-bearing invariant: a holder's
//! governance weight is proven over their OWN Solana token account by a real
//! stake-weighted super-majority, with **no vault, no lock, no transfer**. The holder
//! never surrenders custody; only a genuine consensus observation reaches
//! [`LockProofTrust::ConsensusVerified`].
//!
//! Both polarities run by default:
//! - (a) a holder's own SPL token account (real 165-byte layout) included under a
//!   finalized bank hash with an 80% stake super-majority proves a `ConsensusVerified`
//!   holding carrying the right owner/mint/amount/slot;
//! - (b) the SAME account observed over plain RPC yields only `StructureOnly`
//!   (`is_consensus_proven == false`) — the state a forged/MITM node can fabricate;
//! - (c) a 40% sub-super-majority does NOT reach `ConsensusVerified` (the stake teeth);
//! - (d) a wrong-mint account is refused;
//! - (e) a too-short / non-token blob is refused (decode `None`).
//!
//! Every fixture is built from the REAL crate constructors (`EpochStakeTable`,
//! `ValidatorVote::sign`, `BankHashComponents`, `solana_account_hash`,
//! `accounts_merkle_node`, `AccountsInclusionProof16`) — the SAME accounts-hash
//! inclusion + super-majority machinery the `$DREGG` mint path verifies the vault with,
//! here pointed at the holder's own account instead of a vault.

use dregg_bridge::solana_consensus::{
    BankHashComponents, EpochStakeTable, PohSegment, ValidatorVote,
};
use dregg_bridge::solana_holdings::{
    HoldingAccount, HoldingProof, HoldingProofError, SPL_ACCOUNT_LEN, SPL_AMOUNT_OFFSET,
    SPL_MINT_OFFSET, SPL_OWNER_OFFSET, observe_holding_structure, prove_holding_consensus,
};
use dregg_bridge::solana_trustless::{ConsensusEvidence, LockProofTrust};
use dregg_bridge::solana_wire::{
    AccountsInclusionProof16, MerkleLevel, accounts_merkle_node, solana_account_hash,
};
use ed25519_dalek::SigningKey;

/// The configured `$DREGG` SPL mint the holdings verifier binds to.
const DREGG_MINT: [u8; 32] = [0xABu8; 32];
/// The SPL Token program that owns every token account (the account's owner *program*,
/// not the holder wallet).
const SPL_TOKEN_PROGRAM: [u8; 32] = [0x06u8; 32];
/// The holder's own token account pubkey.
const HOLDER_ACCOUNT: [u8; 32] = [0x42u8; 32];
/// The holder wallet (SPL `Account.owner`) that controls `HOLDER_ACCOUNT`.
const HOLDER_WALLET: [u8; 32] = [0x99u8; 32];
const EPOCH: u64 = 5;
const SLOT: u64 = 12_345;
const LAMPORTS: u64 = 2_039_280; // a rent-exempt SPL token account
const RENT_EPOCH: u64 = 99;

fn vk(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

/// Three validators, 400/400/200 stake (total 1000). The top pair (800/1000 = 80%)
/// clears 2/3; a single 400-stake validator (40%) does not.
fn stake_table() -> EpochStakeTable {
    EpochStakeTable::from_entries(
        EPOCH,
        [
            (vk(11).verifying_key().to_bytes(), 400),
            (vk(12).verifying_key().to_bytes(), 400),
            (vk(13).verifying_key().to_bytes(), 200),
        ],
    )
}

/// The real 165-byte SPL `Account` layout: `mint(32) ‖ owner(32) ‖ amount_le(8) ‖ …`.
fn spl_account_data(mint: [u8; 32], owner: [u8; 32], amount: u64) -> Vec<u8> {
    let mut d = vec![0u8; SPL_ACCOUNT_LEN];
    d[SPL_MINT_OFFSET..SPL_MINT_OFFSET + 32].copy_from_slice(&mint);
    d[SPL_OWNER_OFFSET..SPL_OWNER_OFFSET + 32].copy_from_slice(&owner);
    d[SPL_AMOUNT_OFFSET..SPL_AMOUNT_OFFSET + 8].copy_from_slice(&amount.to_le_bytes());
    d
}

/// Build the holder's own SPL token account with a real 16-ary accounts-hash inclusion:
/// its per-account leaf sits at position 2 among 5 chunk children. Returns the account
/// (with proof) and the accounts hash the leaf opens into.
fn holder_account(data: Vec<u8>) -> (HoldingAccount, [u8; 32]) {
    let leaf = solana_account_hash(
        LAMPORTS,
        &SPL_TOKEN_PROGRAM,
        false,
        RENT_EPOCH,
        &data,
        &HOLDER_ACCOUNT,
    );
    // A real 16-ary chunk: the leaf at position 2 among 4 siblings.
    let sibs = [[0x01u8; 32], [0x02u8; 32], [0x03u8; 32], [0x04u8; 32]];
    let position = 2usize;
    let mut chunk = Vec::new();
    chunk.extend_from_slice(&sibs[..position]);
    chunk.push(leaf);
    chunk.extend_from_slice(&sibs[position..]);
    let accounts_hash = accounts_merkle_node(&chunk);
    let proof = AccountsInclusionProof16 {
        levels: vec![MerkleLevel {
            position: position as u8,
            siblings: sibs.to_vec(),
        }],
    };
    (
        HoldingAccount {
            token_account: HOLDER_ACCOUNT,
            lamports: LAMPORTS,
            owner_program: SPL_TOKEN_PROGRAM,
            executable: false,
            rent_epoch: RENT_EPOCH,
            data,
            inclusion: proof,
        },
        accounts_hash,
    )
}

/// Consensus evidence over `accounts_hash`, signed by `signers`, with a real PoH tick
/// chain when `with_poh`. The bank hash recomputes from its components.
fn consensus_signed_by(
    accounts_hash: [u8; 32],
    signers: &[SigningKey],
    with_poh: bool,
) -> ConsensusEvidence {
    let (last_blockhash, poh) = if with_poh {
        use sha2::{Digest, Sha256};
        let anchor = [0x55u8; 32];
        let mut tail = anchor;
        for _ in 0..256u64 {
            let mut h = Sha256::new();
            h.update(tail);
            tail = h.finalize().into();
        }
        (
            tail,
            Some(PohSegment {
                anchor_hash: anchor,
                num_hashes: 256,
                tail_hash: tail,
            }),
        )
    } else {
        ([0u8; 32], None)
    };
    let bank_components = BankHashComponents {
        parent_bank_hash: [0x01u8; 32],
        accounts_hash,
        signature_count: signers.len() as u64,
        last_blockhash,
    };
    let bank_hash = bank_components.compute();
    let votes = signers
        .iter()
        .map(|s| ValidatorVote::sign(s, SLOT, bank_hash))
        .collect();
    ConsensusEvidence {
        slot: SLOT,
        bank_hash,
        epoch: EPOCH,
        // Claimed scalars — the consensus path recounts real stake from `votes`.
        voted_stake: 0,
        total_stake: 1000,
        votes,
        bank_components,
        poh,
    }
}

/// The full super-majority holder proof (validators 11 + 12 = 800/1000), with PoH.
fn supermajority_holding(amount: u64) -> HoldingProof {
    let data = spl_account_data(DREGG_MINT, HOLDER_WALLET, amount);
    let (account, accounts_hash) = holder_account(data);
    let consensus = consensus_signed_by(accounts_hash, &[vk(11), vk(12)], true);
    HoldingProof { account, consensus }
}

// ─────────────────────────────────────────────────────────────────────────────
// (a) A holder's OWN account, consensus-proven → ConsensusVerified holding.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn holder_own_account_proves_consensus_verified_holding() {
    let amount = 1_234_567u64;
    let proof = supermajority_holding(amount);

    let holding = prove_holding_consensus(
        &proof,
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        &stake_table(),
        true,
    )
    .expect("a holder's own account under an 80% super-majority proves a holding");

    assert!(
        holding.is_consensus_proven(),
        "a real stake-weighted super-majority is genuinely verified"
    );
    assert_eq!(holding.trust, LockProofTrust::ConsensusVerified);
    assert_eq!(
        holding.token_account, HOLDER_ACCOUNT,
        "the holder's own account"
    );
    assert_eq!(
        holding.owner, HOLDER_WALLET,
        "the SPL owner wallet keeps custody"
    );
    assert_eq!(holding.mint, DREGG_MINT);
    assert_eq!(holding.amount, amount, "the proven balance");
    assert_eq!(holding.slot, SLOT, "the finalized snapshot slot");
}

// ─────────────────────────────────────────────────────────────────────────────
// (b) SAME account over plain RPC → StructureOnly (NOT consensus-proven).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn same_account_over_plain_rpc_is_structure_only() {
    let amount = 1_234_567u64;
    let proof = supermajority_holding(amount);

    let holding = observe_holding_structure(&proof.account, &DREGG_MINT, &SPL_TOKEN_PROGRAM, SLOT)
        .expect("the plain-RPC read still surfaces the balance");

    assert_eq!(
        holding.trust,
        LockProofTrust::StructureOnly,
        "a plain-RPC observation is NOT consensus-verified"
    );
    assert!(
        !holding.is_consensus_proven(),
        "structure-only MUST NOT grant weight (fail closed)"
    );
    // Same decoded facts, but unproven.
    assert_eq!(holding.owner, HOLDER_WALLET);
    assert_eq!(holding.mint, DREGG_MINT);
    assert_eq!(holding.amount, amount);
}

// ─────────────────────────────────────────────────────────────────────────────
// (c) A 40% sub-super-majority CANNOT reach ConsensusVerified (stake teeth).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn sub_supermajority_does_not_reach_consensus() {
    let amount = 500u64;
    let data = spl_account_data(DREGG_MINT, HOLDER_WALLET, amount);
    let (account, accounts_hash) = holder_account(data);
    // Signed by ONLY validator 11 (400/1000 = 40% < 2/3). Every vote is a valid
    // Ed25519 signature over the real bank hash; the ONLY defect is insufficient stake.
    let consensus = consensus_signed_by(accounts_hash, &[vk(11)], false);
    let proof = HoldingProof { account, consensus };

    let err = prove_holding_consensus(
        &proof,
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        &stake_table(),
        false,
    )
    .expect_err("a 40% vote set cannot reach consensus");
    match err {
        HoldingProofError::StakeBelowThreshold { voted, total } => {
            assert!(
                voted.saturating_mul(3) < total.saturating_mul(2),
                "the refused tally is genuinely below the 2/3 super-majority: {voted}/{total}"
            );
            assert_eq!(voted, 400, "only validator 11's real stake was counted");
            assert_eq!(total, 1000, "against the full epoch stake");
        }
        other => panic!("expected StakeBelowThreshold, got {other:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// (d) A wrong-mint account is refused (even with a real super-majority).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn wrong_mint_is_refused() {
    let amount = 500u64;
    let other_mint = [0xCDu8; 32];
    let data = spl_account_data(other_mint, HOLDER_WALLET, amount);
    let (account, accounts_hash) = holder_account(data);
    let consensus = consensus_signed_by(accounts_hash, &[vk(11), vk(12)], false);
    let proof = HoldingProof { account, consensus };

    assert_eq!(
        prove_holding_consensus(
            &proof,
            &DREGG_MINT,
            &SPL_TOKEN_PROGRAM,
            &stake_table(),
            false
        )
        .unwrap_err(),
        HoldingProofError::WrongMint,
        "a non-$DREGG token account grants no $DREGG weight"
    );
    // The plain-RPC path refuses it too.
    assert_eq!(
        observe_holding_structure(&proof.account, &DREGG_MINT, &SPL_TOKEN_PROGRAM, SLOT)
            .unwrap_err(),
        HoldingProofError::WrongMint,
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// (d2) THE FORGERY: an account owned by the ATTACKER'S program, carrying a valid
//      SPL layout with a huge fake balance, GENUINELY included in a 2/3-signed
//      finalized accounts hash — must be refused, because SPL `data` is only an
//      authoritative balance when the SPL Token program owns the account.
// ─────────────────────────────────────────────────────────────────────────────

/// An attacker's account: same inclusion machinery as `holder_account`, but owned by
/// an arbitrary `owner_program` (their OWN program, not the SPL Token program). The
/// leaf/accounts-hash/consensus are all VALID — getting your own account into the
/// accounts hash is permissionless — so the ONLY defect is the owner program.
fn account_owned_by(data: Vec<u8>, owner_program: [u8; 32]) -> (HoldingAccount, [u8; 32]) {
    let leaf = solana_account_hash(
        LAMPORTS,
        &owner_program,
        false,
        RENT_EPOCH,
        &data,
        &HOLDER_ACCOUNT,
    );
    let sibs = [[0x01u8; 32], [0x02u8; 32], [0x03u8; 32], [0x04u8; 32]];
    let position = 2usize;
    let mut chunk = Vec::new();
    chunk.extend_from_slice(&sibs[..position]);
    chunk.push(leaf);
    chunk.extend_from_slice(&sibs[position..]);
    let accounts_hash = accounts_merkle_node(&chunk);
    let proof = AccountsInclusionProof16 {
        levels: vec![MerkleLevel {
            position: position as u8,
            siblings: sibs.to_vec(),
        }],
    };
    (
        HoldingAccount {
            token_account: HOLDER_ACCOUNT,
            lamports: LAMPORTS,
            owner_program,
            executable: false,
            rent_epoch: RENT_EPOCH,
            data,
            inclusion: proof,
        },
        accounts_hash,
    )
}

#[test]
fn account_not_owned_by_spl_token_program_is_refused() {
    let attacker_program = [0x99u8; 32]; // the attacker's OWN program, != SPL Token
    // Correct $DREGG mint, attacker's wallet, a forged u64::MAX balance.
    let data = spl_account_data(DREGG_MINT, HOLDER_WALLET, u64::MAX);
    let (account, accounts_hash) = account_owned_by(data, attacker_program);
    // A REAL supermajority genuinely signs this finalized accounts hash.
    let consensus = consensus_signed_by(accounts_hash, &[vk(11), vk(12)], false);
    let proof = HoldingProof { account, consensus };

    // Despite genuine consensus + inclusion, the forged balance grants NO weight:
    // the account is not owned by the SPL Token program.
    assert_eq!(
        prove_holding_consensus(
            &proof,
            &DREGG_MINT,
            &SPL_TOKEN_PROGRAM,
            &stake_table(),
            false
        )
        .unwrap_err(),
        HoldingProofError::NotSplTokenProgram {
            owner_program: attacker_program
        },
        "an account under the attacker's own program is not an authoritative balance"
    );
    assert_eq!(
        observe_holding_structure(&proof.account, &DREGG_MINT, &SPL_TOKEN_PROGRAM, SLOT)
            .unwrap_err(),
        HoldingProofError::NotSplTokenProgram {
            owner_program: attacker_program
        },
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// (e) A too-short / non-token blob is refused (decode None).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn too_short_blob_is_refused() {
    // 100 bytes < the 165-byte SPL Account minimum: decode_spl_token_account → None.
    let short = vec![0u8; 100];
    let (account, accounts_hash) = holder_account(short);
    let consensus = consensus_signed_by(accounts_hash, &[vk(11), vk(12)], false);
    let proof = HoldingProof { account, consensus };

    assert_eq!(
        prove_holding_consensus(
            &proof,
            &DREGG_MINT,
            &SPL_TOKEN_PROGRAM,
            &stake_table(),
            false
        )
        .unwrap_err(),
        HoldingProofError::NotTokenAccount,
        "a non-token blob is not a holding"
    );
    assert_eq!(
        observe_holding_structure(&proof.account, &DREGG_MINT, &SPL_TOKEN_PROGRAM, SLOT)
            .unwrap_err(),
        HoldingProofError::NotTokenAccount,
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Extra teeth: a tampered inclusion / bank binding must not reach ConsensusVerified.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn tampered_accounts_hash_is_refused() {
    let mut proof = supermajority_holding(500);
    // Corrupt the committed accounts hash so the (unchanged) inclusion no longer opens
    // into it — the bank hash still recomputes from the corrupted components, so this
    // fails at the account-inclusion step, not the bank binding.
    proof.consensus.bank_components.accounts_hash = [0xFFu8; 32];
    proof.consensus.bank_hash = proof.consensus.bank_components.compute();
    // Re-sign the votes over the new bank hash so the super-majority still passes and
    // the ONLY defect is the inclusion.
    proof.consensus.votes = vec![
        ValidatorVote::sign(&vk(11), SLOT, proof.consensus.bank_hash),
        ValidatorVote::sign(&vk(12), SLOT, proof.consensus.bank_hash),
    ];

    assert_eq!(
        prove_holding_consensus(
            &proof,
            &DREGG_MINT,
            &SPL_TOKEN_PROGRAM,
            &stake_table(),
            false
        )
        .unwrap_err(),
        HoldingProofError::AccountsInclusionInvalid,
        "an account not included in the voted accounts hash is not proven"
    );
}

#[test]
fn unbound_bank_hash_is_refused() {
    let mut proof = supermajority_holding(500);
    // Flip the voted bank hash away from what the components recompute to, and re-sign
    // the votes over that dishonest hash. The super-majority passes on the fake hash,
    // but the components no longer bind it.
    proof.consensus.bank_hash = [0x77u8; 32];
    proof.consensus.votes = vec![
        ValidatorVote::sign(&vk(11), SLOT, proof.consensus.bank_hash),
        ValidatorVote::sign(&vk(12), SLOT, proof.consensus.bank_hash),
    ];

    assert_eq!(
        prove_holding_consensus(
            &proof,
            &DREGG_MINT,
            &SPL_TOKEN_PROGRAM,
            &stake_table(),
            false
        )
        .unwrap_err(),
        HoldingProofError::BankHashMismatch,
        "the voted bank hash must bind its committed accounts hash"
    );
}
