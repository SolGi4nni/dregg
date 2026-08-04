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
    AcceptedTokenProgram, DREGG_MAINNET_DECIMALS, DREGG_MAINNET_MINT, HoldingAccount,
    HoldingAssetPolicy, HoldingProof, HoldingProofError, SPL_ACCOUNT_LEN, SPL_AMOUNT_OFFSET,
    SPL_MINT_OFFSET, SPL_OWNER_OFFSET, decode_token_account, fixtures, observe_holding_structure,
    prove_holding_consensus, prove_holding_consensus_anchored, prove_holding_consensus_with_policy,
};
use dregg_bridge::solana_provenance::ProvenanceError;
use dregg_bridge::solana_trustless::{ConsensusEvidence, LockProofTrust};
use dregg_bridge::solana_wire::{
    AccountsInclusionProof16, MerkleLevel, accounts_merkle_node, solana_account_hash,
};
use ed25519_dalek::SigningKey;

/// The configured `$DREGG` SPL mint the holdings verifier binds to.
const DREGG_MINT: [u8; 32] = [0xABu8; 32];
/// The SPL Token program that owns every token account (the account's owner *program*,
/// not the holder wallet).
const SPL_TOKEN_PROGRAM: [u8; 32] = [
    0x06, 0xdd, 0xf6, 0xe1, 0xd7, 0x65, 0xa1, 0x93, 0xd9, 0xcb, 0xe1, 0x46, 0xce, 0xeb, 0x79, 0xac,
    0x1c, 0xb4, 0x85, 0xed, 0x5f, 0x5b, 0x37, 0x91, 0x3a, 0x8c, 0xf5, 0x85, 0x7e, 0xff, 0x00, 0xa9,
];
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
    d[108] = 1; // AccountState::Initialized
    d
}

/// Token-2022 account with a real extension header: AccountType::Account followed
/// by the zero-sized ImmutableOwner TLV (ExtensionType discriminant 7).
fn token_2022_account_data(mint: [u8; 32], owner: [u8; 32], amount: u64) -> Vec<u8> {
    let mut d = spl_account_data(mint, owner, amount);
    d.resize(170, 0);
    d[165] = 2; // AccountType::Account
    d[166..168].copy_from_slice(&7u16.to_le_bytes()); // ImmutableOwner
    d[168..170].copy_from_slice(&0u16.to_le_bytes());
    d
}

#[test]
fn token_2022_extension_account_decodes_exact_fields() {
    let data = token_2022_account_data(DREGG_MINT, HOLDER_WALLET, 98_765);
    let decoded = decode_token_account(&data, AcceptedTokenProgram::Token2022)
        .expect("valid extension-bearing Token-2022 account");
    assert_eq!(decoded.mint, DREGG_MINT);
    assert_eq!(decoded.owner, HOLDER_WALLET);
    assert_eq!(decoded.amount, 98_765);
    assert!(
        decode_token_account(&data, AcceptedTokenProgram::Legacy).is_err(),
        "legacy policy never reinterprets extension-bearing bytes"
    );
}

#[test]
fn token_2022_truncated_wrong_kind_and_duplicate_extensions_are_refused() {
    let valid = token_2022_account_data(DREGG_MINT, HOLDER_WALLET, 1);

    let mut truncated = valid.clone();
    truncated[168..170].copy_from_slice(&4u16.to_le_bytes());
    assert_eq!(
        decode_token_account(&truncated, AcceptedTokenProgram::Token2022).unwrap_err(),
        HoldingProofError::NotTokenAccount
    );

    let mut mint_kind = valid.clone();
    mint_kind[166..168].copy_from_slice(&1u16.to_le_bytes()); // TransferFeeConfig is mint-only
    assert_eq!(
        decode_token_account(&mint_kind, AcceptedTokenProgram::Token2022).unwrap_err(),
        HoldingProofError::NotTokenAccount
    );

    let mut wrong_account_type = valid.clone();
    wrong_account_type[165] = 1; // AccountType::Mint
    wrong_account_type.resize(382, 0); // the live mint's size is not a holder-account layout
    assert_eq!(
        decode_token_account(&wrong_account_type, AcceptedTokenProgram::Token2022).unwrap_err(),
        HoldingProofError::NotTokenAccount
    );

    let mut duplicate = valid;
    duplicate.extend_from_slice(&7u16.to_le_bytes());
    duplicate.extend_from_slice(&0u16.to_le_bytes());
    assert_eq!(
        decode_token_account(&duplicate, AcceptedTokenProgram::Token2022).unwrap_err(),
        HoldingProofError::NotTokenAccount
    );
}

#[test]
fn uninitialized_frozen_native_and_invalid_base_states_are_refused() {
    let mut uninitialized = spl_account_data(DREGG_MINT, HOLDER_WALLET, 1);
    uninitialized[108] = 0;
    assert_eq!(
        decode_token_account(&uninitialized, AcceptedTokenProgram::Token2022).unwrap_err(),
        HoldingProofError::NotTokenAccount
    );

    let mut frozen = spl_account_data(DREGG_MINT, HOLDER_WALLET, 1);
    frozen[108] = 2;
    assert_eq!(
        decode_token_account(&frozen, AcceptedTokenProgram::Token2022).unwrap_err(),
        HoldingProofError::FrozenTokenAccount
    );

    let mut native = spl_account_data(DREGG_MINT, HOLDER_WALLET, 1);
    native[109..113].copy_from_slice(&1u32.to_le_bytes());
    native[113..121].copy_from_slice(&2_039_280u64.to_le_bytes());
    assert_eq!(
        decode_token_account(&native, AcceptedTokenProgram::Token2022).unwrap_err(),
        HoldingProofError::NativeTokenAccount
    );

    let mut invalid_option = spl_account_data(DREGG_MINT, HOLDER_WALLET, 1);
    invalid_option[72..76].copy_from_slice(&2u32.to_le_bytes());
    assert_eq!(
        decode_token_account(&invalid_option, AcceptedTokenProgram::Token2022).unwrap_err(),
        HoldingProofError::NotTokenAccount
    );
}

#[test]
fn live_dregg_policy_is_exactly_token_2022() {
    let policy = HoldingAssetPolicy::dregg_mainnet();
    assert_eq!(policy.mint(), &DREGG_MAINNET_MINT);
    assert_eq!(policy.token_program(), AcceptedTokenProgram::Token2022);
    assert_eq!(DREGG_MAINNET_DECIMALS, 6);
    assert_eq!(
        bs58::encode(DREGG_MAINNET_MINT).into_string(),
        "XkeTXo1125vz5H9svJpGiw4JvLbN8VmMu9cmMvspump"
    );
    assert_eq!(
        HoldingAssetPolicy::new(DREGG_MAINNET_MINT, AcceptedTokenProgram::Legacy).unwrap_err(),
        HoldingProofError::DreggProgramMismatch
    );
    assert!(matches!(
        HoldingAssetPolicy::from_program_id(DREGG_MINT, [0xAA; 32]),
        Err(HoldingProofError::UnsupportedTokenProgram { .. })
    ));
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
    HoldingProof {
        account,
        consensus,
        stake_provenance: None,
    }
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
    let proof = HoldingProof {
        account,
        consensus,
        stake_provenance: None,
    };

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
    let proof = HoldingProof {
        account,
        consensus,
        stake_provenance: None,
    };

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

#[test]
fn owner_and_amount_bytes_are_bound_by_finalized_inclusion() {
    for (label, offset) in [("owner", SPL_OWNER_OFFSET), ("amount", SPL_AMOUNT_OFFSET)] {
        let mut proof = supermajority_holding(500);
        proof.account.data[offset] ^= 1;
        assert_eq!(
            prove_holding_consensus(
                &proof,
                &DREGG_MINT,
                &SPL_TOKEN_PROGRAM,
                &stake_table(),
                false,
            )
            .unwrap_err(),
            HoldingProofError::AccountsInclusionInvalid,
            "tampered {label} must not survive the finalized account-hash proof"
        );
    }
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
    let proof = HoldingProof {
        account,
        consensus,
        stake_provenance: None,
    };

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

#[test]
fn token_2022_extension_account_reaches_consensus_verified_pipeline() {
    let amount = 77_123u64;
    let data = token_2022_account_data(DREGG_MINT, HOLDER_WALLET, amount);
    let token_2022_program = AcceptedTokenProgram::Token2022.program_id();
    let (account, accounts_hash) = account_owned_by(data, token_2022_program);
    let proof = HoldingProof {
        account,
        consensus: consensus_signed_by(accounts_hash, &[vk(11), vk(12)], false),
        stake_provenance: None,
    };
    let policy = HoldingAssetPolicy::new(DREGG_MINT, AcceptedTokenProgram::Token2022).unwrap();
    let holding = prove_holding_consensus_with_policy(&proof, &policy, &stake_table(), false)
        .expect("Token-2022 account verifies through the consensus-proven path");
    assert!(holding.is_consensus_proven());
    assert_eq!(holding.owner, HOLDER_WALLET);
    assert_eq!(holding.mint, DREGG_MINT);
    assert_eq!(holding.amount, amount);
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
    let proof = HoldingProof {
        account,
        consensus,
        stake_provenance: None,
    };

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

// ─────────────────────────────────────────────────────────────────────────────
// ANCHORED path — the ONLY production route to ConsensusVerified. The stake
// table is DERIVED from bank-state provenance and trusted back to a
// governance-pinned anchor; a caller/attacker-supplied table does not exist as
// an input at all.
// ─────────────────────────────────────────────────────────────────────────────

/// The honest cluster: validators with 700/300 stake, authorized voters proven
/// from bank state. Returns `(proof, anchor, policy)` where `anchor` pins the
/// genuine distribution.
fn honest_anchored(
    amount: u64,
) -> (
    HoldingProof,
    dregg_bridge::solana_provenance::WeakSubjectivityAnchor,
    dregg_bridge::solana_consensus::PohAnchorPolicy,
) {
    fixtures::anchored_holding_with_cluster(
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        HOLDER_ACCOUNT,
        HOLDER_WALLET,
        amount,
        &[(11, 700), (12, 300)],
    )
}

#[test]
fn anchored_honest_holding_is_consensus_verified() {
    let amount = 1_234_567u64;
    let (proof, anchor, policy) = honest_anchored(amount);
    let holding = prove_holding_consensus_anchored(
        &proof,
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        &anchor,
        true, // PoH required, against the bounded-anchor policy
        Some(&policy),
    )
    .expect("a genuine holding under the pinned anchor verifies");
    assert!(holding.is_consensus_proven());
    assert_eq!(holding.trust, LockProofTrust::ConsensusVerified);
    assert_eq!(holding.owner, HOLDER_WALLET, "the holder keeps custody");
    assert_eq!(holding.amount, amount);
    assert_eq!(holding.mint, DREGG_MINT);
}

/// **THE CRITIC'S EXACT FORGERY, now closed.** The attacker fabricates a 1-key
/// stake distribution (their key = 100% of the stake), builds an internally
/// CONSISTENT holding proof over it — real accounts, real inclusion, real
/// signed votes by their own key, which their own bank-state provenance even
/// "proves" — and submits it. On the legacy trusted-table path this minted a
/// ConsensusVerified holding (governance weight from thin air). On the anchored
/// path the verifier's trust root is the GOVERNANCE-PINNED anchor: the
/// attacker's derived table roots to a different value, so the proof is refused
/// with `AnchorRootMismatch` before any stake is counted.
#[test]
fn attacker_supplied_one_key_stake_table_is_rejected() {
    // The attacker controls everything about this proof INCLUDING its stake
    // distribution: one key (seed 66) holding 100% of the stake.
    let (evil_proof, evil_anchor, evil_policy) = fixtures::anchored_holding_with_cluster(
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        HOLDER_ACCOUNT,
        HOLDER_WALLET,
        u64::MAX, // the forged balance the attacker wants weight for
        &[(66, 1_000)],
    );

    // Sanity: the forgery is REAL — under the attacker's OWN anchor the proof
    // verifies (this is exactly what the un-anchored trusted-table path let
    // through). Only the governance pin stands between this and minted weight.
    prove_holding_consensus_anchored(
        &evil_proof,
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        &evil_anchor,
        true,
        Some(&evil_policy),
    )
    .expect("internally consistent — the attack is real, the pin is load-bearing");

    // The verifier pins the HONEST governance anchor. The attacker's derived
    // 1-key table cannot reconstruct its root → REFUSED, no weight minted.
    let (_, honest_anchor, _) = honest_anchored(1);
    let err = prove_holding_consensus_anchored(
        &evil_proof,
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        &honest_anchor,
        true,
        Some(&evil_policy),
    )
    .expect_err("an attacker-supplied stake distribution must not mint weight");
    assert!(
        matches!(
            err,
            HoldingProofError::Provenance(ProvenanceError::AnchorRootMismatch { .. })
        ),
        "refused at the anchor-root binding, got: {err:?}"
    );
}

/// A sub-2/3 tally on the anchored path rejects: drop the 700-stake validator's
/// vote, leaving 300/1000.
#[test]
fn anchored_sub_supermajority_is_rejected() {
    let (mut proof, anchor, policy) = honest_anchored(500);
    proof.consensus.votes.remove(0); // the 700-stake vote
    assert_eq!(
        prove_holding_consensus_anchored(
            &proof,
            &DREGG_MINT,
            &SPL_TOKEN_PROGRAM,
            &anchor,
            true,
            Some(&policy),
        )
        .unwrap_err(),
        HoldingProofError::StakeBelowThreshold {
            voted: 300,
            total: 1000
        }
    );
}

/// A vote re-signed by an imposter (not the vote account's proven on-chain
/// authorized voter) contributes ZERO stake — the authorized-voter binding the
/// legacy supplied-table tally lacked.
#[test]
fn anchored_unauthorized_voter_contributes_no_stake() {
    let (mut proof, anchor, policy) = honest_anchored(500);
    let imposter = dregg_bridge::solana_provenance::fixtures::sk(99);
    let va1 = [11u8 ^ 0xA5; 32]; // validator 1's vote account (seed 11)
    proof.consensus.votes[0] = dregg_bridge::solana_provenance::fixtures::tower_sync_tx(
        &imposter,
        &va1,
        proof.consensus.slot,
        proof.consensus.bank_hash,
    );
    assert_eq!(
        prove_holding_consensus_anchored(
            &proof,
            &DREGG_MINT,
            &SPL_TOKEN_PROGRAM,
            &anchor,
            true,
            Some(&policy),
        )
        .unwrap_err(),
        HoldingProofError::StakeBelowThreshold {
            voted: 300,
            total: 1000
        }
    );
}

/// Without bank-state provenance there is nothing verifiable to tally against —
/// the anchored path refuses rather than accepting any bare table.
#[test]
fn anchored_without_provenance_is_rejected() {
    let (mut proof, anchor, policy) = honest_anchored(500);
    proof.stake_provenance = None;
    assert_eq!(
        prove_holding_consensus_anchored(
            &proof,
            &DREGG_MINT,
            &SPL_TOKEN_PROGRAM,
            &anchor,
            false,
            Some(&policy),
        )
        .unwrap_err(),
        HoldingProofError::StakeProvenanceMissing
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
