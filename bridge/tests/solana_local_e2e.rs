//! `solana_local_e2e`: drive the trustless Solana bridge against a **real local
//! `solana-test-validator`** — for free, no real SOL.
//!
//! This test is **gated on `SOLANA_LOCAL=1`**. Without it the test returns
//! immediately (a clean skip), so the default `cargo test -p dregg-bridge` suite
//! and CI stay green with no validator present.
//!
//! # What it does (when enabled)
//!
//! It consumes the artifact bundle produced by `scripts/solana-local-harness.sh`
//! (which boots a local validator, mints a stand-in `$DREGG` SPL token, locks an
//! amount into a vault account, and harvests the validator's real artifacts into
//! a manifest). It then constructs a [`SolanaLockProof`] and feeds it through
//! [`verify_lock_proof_consensus_anchored`] + [`MirrorState::mint_against_lock_proof_anchored`],
//! proving the bridge verifies a real local Solana lock end-to-end and mints
//! conserved mirror credit.
//!
//! # Harvested-real vs adapter-shaped (honest accounting)
//!
//! **Harvested real from the local cluster:**
//! - the SPL `$DREGG` mint + the on-chain locked amount (the conserved quantity);
//! - the vote account's real `VoteState` bytes → decoded authorized voter
//!   ([`decode_authorized_voter`]);
//! - the stake account's real `StakeStateV2` bytes → decoded delegation
//!   (the effective-stake the 2/3 threshold is measured against);
//! - the `StakeHistory` sysvar's real bytes → the warmup/cooldown curve input;
//! - the validator's real authorized-voter **keypair** (from the ledger dir), so
//!   every counted vote carries a genuine Ed25519 signature by the on-chain
//!   authority over the slot's bank hash.
//!
//! **Adapter-shaped (the named, documented seams — `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`):**
//! - the **accounts-hash 16-ary Merkle tree** is reconstructed here around the
//!   real account leaves (Solana RPC exposes neither the bank-hash-committed
//!   accounts Merkle proofs nor the real bank hash, so a real vote signature and
//!   a real inclusion path cannot both be obtained off-chain today);
//! - the **bank-hash components** are assembled around that accounts hash;
//! - the **vault lock-record layout** ([`encode_lock_record`]) is the adapter's
//!   account schema (a deploy-time choice; no lock program is deployed here);
//! - the **leader-schedule snapshot offset** (the ±1–2 epoch shift) is evaluated
//!   at the table's epoch, as in the core verifier.
//!
//! So: real Solana account *state* + real authorized-voter *signatures* + the
//! real bank-state *decoders/derivation*, with the consensus Merkle commitment
//! and the lock-record schema reconstructed by the adapter.

use dregg_bridge::midnight::EpochKey;
use dregg_bridge::solana_consensus::{BankHashComponents, ValidatorVote};
use dregg_bridge::solana_mirror::{MirrorConfig, MirrorState};
use dregg_bridge::solana_provenance::{
    ProvenAccount, STAKE_HISTORY_SYSVAR_ID, WeakSubjectivityAnchor, decode_authorized_voter,
    derive_stake_table,
};
use dregg_bridge::solana_trustless::{
    AccountInclusionProof, ConsensusEvidence, LockProofTrust, MainnetAccountInclusion,
    SolanaLockProof, StakeProvenance, verify_lock_proof_consensus_anchored,
};
use dregg_bridge::solana_wire::{
    AccountsInclusionProof16, MerkleLevel, accounts_merkle_node, encode_lock_record,
    ingest_vote_transaction, solana_account_hash,
};
use dregg_types::CellId;
use ed25519_dalek::SigningKey;

const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32];

fn enabled() -> bool {
    matches!(
        std::env::var("SOLANA_LOCAL").ok().as_deref(),
        Some("1") | Some("true")
    )
}

fn manifest_path() -> String {
    std::env::var("DREGG_SOLANA_ARTIFACTS")
        .unwrap_or_else(|_| "/tmp/dregg-solana-local/manifest.json".to_string())
}

fn b58_32(s: &str) -> [u8; 32] {
    let v = bs58::decode(s)
        .into_vec()
        .unwrap_or_else(|e| panic!("base58 decode of `{s}`: {e}"));
    assert_eq!(
        v.len(),
        32,
        "pubkey `{s}` is not 32 bytes ({} bytes)",
        v.len()
    );
    let mut out = [0u8; 32];
    out.copy_from_slice(&v);
    out
}

/// A harvested account from the manifest: its real on-chain fields + its raw
/// data bytes (read from the side-car file the harness wrote with
/// `solana account --output-file`).
struct HarvestedAccount {
    pubkey: [u8; 32],
    lamports: u64,
    owner: [u8; 32],
    executable: bool,
    rent_epoch: u64,
    data: Vec<u8>,
}

impl HarvestedAccount {
    fn from_json(v: &serde_json::Value) -> Self {
        let data_file = v["data_file"].as_str().expect("data_file");
        let data = std::fs::read(data_file)
            .unwrap_or_else(|e| panic!("read account data file `{data_file}`: {e}"));
        Self {
            pubkey: b58_32(v["pubkey"].as_str().expect("pubkey")),
            lamports: v["lamports"].as_u64().expect("lamports"),
            owner: b58_32(v["owner"].as_str().expect("owner")),
            executable: v["executable"].as_bool().unwrap_or(false),
            rent_epoch: v["rent_epoch"].as_u64().unwrap_or(0),
            data,
        }
    }

    fn leaf(&self) -> [u8; 32] {
        solana_account_hash(
            self.lamports,
            &self.owner,
            self.executable,
            self.rent_epoch,
            &self.data,
            &self.pubkey,
        )
    }
}

/// A 16-ary inclusion proof placing `leaves[i]` in a single chunk among the rest.
fn single_chunk_proof(leaves: &[[u8; 32]], i: usize) -> AccountsInclusionProof16 {
    let siblings: Vec<[u8; 32]> = leaves
        .iter()
        .enumerate()
        .filter(|(j, _)| *j != i)
        .map(|(_, h)| *h)
        .collect();
    AccountsInclusionProof16 {
        levels: vec![MerkleLevel {
            position: i as u8,
            siblings,
        }],
    }
}

fn proven(acct: &HarvestedAccount, proof: AccountsInclusionProof16) -> ProvenAccount {
    ProvenAccount {
        pubkey: acct.pubkey,
        lamports: acct.lamports,
        owner: acct.owner,
        executable: acct.executable,
        rent_epoch: acct.rent_epoch,
        data: acct.data.clone(),
        proof,
    }
}

/// Read a Solana CLI keypair file (a JSON array of 64 bytes: 32-byte seed ‖
/// 32-byte public) into an `ed25519_dalek::SigningKey`.
fn read_keypair(path: &str) -> SigningKey {
    let bytes =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read keypair `{path}`: {e}"));
    let arr: Vec<u8> =
        serde_json::from_str(&bytes).unwrap_or_else(|e| panic!("parse keypair `{path}`: {e}"));
    assert_eq!(arr.len(), 64, "keypair `{path}` is not 64 bytes");
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&arr[..32]);
    SigningKey::from_bytes(&seed)
}

/// Build a real-wire Solana vote `Transaction` (legacy layout) voting `(slot,
/// bank_hash)` for `vote_account`, signed by `authority` — the same wire shape
/// `parse_verified_vote_tx` ingests. The signature is genuine (by the real
/// on-chain authorized voter); the bank hash is the reconstructed one (see the
/// module header).
fn build_vote_tx(
    authority: &SigningKey,
    vote_account: [u8; 32],
    slot: u64,
    bank_hash: [u8; 32],
) -> Vec<u8> {
    use ed25519_dalek::Signer;
    use solana_vote_interface::instruction::VoteInstruction;
    use solana_vote_interface::state::TowerSync;

    fn push_compact_u16(out: &mut Vec<u8>, mut v: u16) {
        loop {
            let mut byte = (v & 0x7f) as u8;
            v >>= 7;
            if v != 0 {
                byte |= 0x80;
            }
            out.push(byte);
            if v == 0 {
                break;
            }
        }
    }

    let auth_pk = authority.verifying_key().to_bytes();
    let vote_program = solana_vote_interface::program::id().to_bytes();
    let account_keys: Vec<[u8; 32]> = vec![auth_pk, vote_account, vote_program];

    let mut tower = TowerSync::default();
    tower.hash = solana_hash::Hash::new_from_array(bank_hash);
    tower
        .lockouts
        .push_back(solana_vote_interface::state::Lockout::new(slot));
    let ix = VoteInstruction::TowerSync(tower);
    let ix_data = bincode::serialize(&ix).expect("serialize vote ix");

    let mut message = Vec::new();
    message.push(1u8); // num_required_signatures
    message.push(0u8); // num_readonly_signed
    message.push(1u8); // num_readonly_unsigned (the vote program)
    push_compact_u16(&mut message, account_keys.len() as u16);
    for k in &account_keys {
        message.extend_from_slice(k);
    }
    message.extend_from_slice(&[0u8; 32]); // recent blockhash
    push_compact_u16(&mut message, 1); // one instruction
    message.push(2u8); // program_id_index (vote program)
    push_compact_u16(&mut message, 2); // accounts len
    message.push(1u8); // vote account meta
    message.push(0u8); // authority meta
    push_compact_u16(&mut message, ix_data.len() as u16);
    message.extend_from_slice(&ix_data);

    let sig = authority.sign(&message).to_bytes();
    let mut tx = Vec::new();
    push_compact_u16(&mut tx, 1);
    tx.extend_from_slice(&sig);
    tx.extend_from_slice(&message);
    tx
}

#[test]
fn local_solana_lock_verifies_and_mints() {
    if !enabled() {
        eprintln!(
            "SKIP solana_local_e2e: set SOLANA_LOCAL=1 and run \
             `scripts/solana-local-harness.sh` first (boots a free local \
             solana-test-validator). Skipping cleanly."
        );
        return;
    }

    let mp = manifest_path();
    let raw = std::fs::read_to_string(&mp).unwrap_or_else(|e| {
        panic!(
            "SOLANA_LOCAL=1 but the artifact manifest `{mp}` is missing ({e}). \
             Run `scripts/solana-local-harness.sh` to produce it."
        )
    });
    let m: serde_json::Value = serde_json::from_str(&raw).expect("parse manifest json");

    let slot = m["slot"].as_u64().expect("slot");
    let epoch = m["epoch"].as_u64().expect("epoch");
    let spl_mint = b58_32(m["spl_mint"].as_str().expect("spl_mint"));
    let vault_pubkey = b58_32(m["vault_account"].as_str().expect("vault_account"));
    let locked_amount = m["locked_amount"].as_u64().expect("locked_amount");
    let new_rate = m["new_rate_activation_epoch"].as_u64();

    let vote = HarvestedAccount::from_json(&m["vote_account"]);
    let stake = HarvestedAccount::from_json(&m["stake_account"]);
    let stake_history = HarvestedAccount::from_json(&m["stake_history"]);
    let vault_lamports = m["vault_account_lamports"].as_u64().unwrap_or(1_000_000);
    let vault_owner = b58_32(
        m["vault_account_owner"]
            .as_str()
            .unwrap_or("11111111111111111111111111111111"),
    );

    assert_eq!(
        stake_history.pubkey, STAKE_HISTORY_SYSVAR_ID,
        "harvested stake-history account is not the StakeHistory sysvar"
    );

    // The authorized voter we must sign with is the vote account's *on-chain*
    // authorized voter, decoded from its real VoteState bytes.
    let onchain_voter = decode_authorized_voter(&vote.data, epoch)
        .expect("decode authorized voter from real VoteState");
    let authority = read_keypair(
        m["authority_keypair_file"]
            .as_str()
            .expect("authority_keypair"),
    );
    let auth_pk = authority.verifying_key().to_bytes();
    assert_eq!(
        auth_pk, onchain_voter,
        "the harvested authority keypair is not the vote account's on-chain \
         authorized voter for epoch {epoch}"
    );

    // The dregg-side lock record (adapter layout): the recipient cell + a lock id
    // deterministically derived from the real (vault, slot, mint).
    let recipient = CellId::from_bytes([0x11u8; 32]);
    let lock_id: [u8; 32] = {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-solana-local-lock");
        h.update(&vault_pubkey);
        h.update(&slot.to_le_bytes());
        h.update(&spl_mint);
        *h.finalize().as_bytes()
    };
    let vault_data = encode_lock_record(&lock_id, &recipient, locked_amount);
    let vault_leaf = solana_account_hash(
        vault_lamports,
        &vault_owner,
        false,
        0,
        &vault_data,
        &vault_pubkey,
    );

    // Reconstruct the accounts-hash 16-ary tree over the real account leaves +
    // the (adapter) vault leaf, all in one chunk. Order: stake, vote, sh, vault.
    let leaves = [stake.leaf(), vote.leaf(), stake_history.leaf(), vault_leaf];
    let accounts_hash = accounts_merkle_node(&leaves);

    let stake_pa = proven(&stake, single_chunk_proof(&leaves, 0));
    let vote_pa = proven(&vote, single_chunk_proof(&leaves, 1));
    let sh_pa = proven(&stake_history, single_chunk_proof(&leaves, 2));
    let vault_proof = single_chunk_proof(&leaves, 3);

    // Derive the stake table from the real bank-state accounts to get its root,
    // then pin the weak-subjectivity anchor to that root (the lock is at the
    // anchor epoch — no rotation needed for a single-epoch local lock).
    let derived = derive_stake_table(
        epoch,
        &accounts_hash,
        std::slice::from_ref(&stake_pa),
        std::slice::from_ref(&vote_pa),
        &sh_pa,
        new_rate,
    )
    .expect("derive stake table from real local bank state");
    assert!(
        derived.table.stake_of(&vote.pubkey) > 0,
        "real stake account did not contribute effective stake to its vote account"
    );
    let anchor = WeakSubjectivityAnchor {
        epoch,
        stake_table_root: derived.table.root(),
    };

    // Real authorized-voter signature over the reconstructed bank hash.
    let bank_components = BankHashComponents {
        parent_bank_hash: [0u8; 32],
        accounts_hash,
        signature_count: 1,
        last_blockhash: [0u8; 32],
    };
    let bank_hash = bank_components.compute();
    let vote_tx = build_vote_tx(&authority, vote.pubkey, slot, bank_hash);
    let validator_vote: ValidatorVote =
        ingest_vote_transaction(&vote_tx).expect("ingest the signed vote transaction");

    let proof = SolanaLockProof {
        lock_id,
        spl_mint,
        amount: locked_amount,
        dregg_recipient: recipient,
        consensus: ConsensusEvidence {
            slot,
            bank_hash,
            epoch,
            voted_stake: derived.table.total_stake(),
            total_stake: derived.table.total_stake(),
            votes: vec![validator_vote],
            bank_components,
            poh: None,
        },
        inclusion: AccountInclusionProof {
            vault_account: vault_pubkey,
            recorded_amount: locked_amount,
            recorded_recipient: recipient,
            recorded_lock_id: lock_id,
            accounts_hash,
            merkle_path: vec![],
            mainnet: Some(MainnetAccountInclusion {
                lamports: vault_lamports,
                owner: vault_owner,
                executable: false,
                rent_epoch: 0,
                data: vault_data,
                proof: vault_proof,
            }),
        },
        stake_provenance: Some(StakeProvenance {
            anchor_accounts_hash: accounts_hash,
            anchor_stake_accounts: vec![stake_pa],
            anchor_vote_accounts: vec![vote_pa],
            anchor_stake_history_account: sh_pa,
            new_rate_activation_epoch: new_rate,
            rotation: vec![],
        }),
    };

    // (1) the trustless anchored verify accepts the real local lock.
    let trust =
        verify_lock_proof_consensus_anchored(&proof, &spl_mint, 1, u64::MAX, &anchor, false, None)
            .expect("anchored consensus verify of the real local lock");
    assert_eq!(trust, LockProofTrust::ConsensusVerified);

    // (2) minting conserved mirror credit through the same accounting rail.
    let mut mirror = MirrorState::new(MirrorConfig {
        spl_mint,
        asset: MIRROR_ASSET,
        oracle_keys: Vec::<EpochKey>::new(),
        min_amount: 1,
        max_amount: u64::MAX,
        // The anchored trustless mint requires the lock to escrow into THIS
        // bridge's vault: bind the config to the real harvested vault + owner.
        vault_account: vault_pubkey,
        lock_program: vault_owner,
        pinned_anchor_epoch: None,
        pinned_anchor_root: None,
    });
    let (mint, mint_trust) = mirror
        .mint_against_lock_proof_anchored(&proof, &anchor, false, None)
        .expect("mint against the verified local lock");
    assert_eq!(mint_trust, LockProofTrust::ConsensusVerified);
    assert_eq!(mint.amount, locked_amount);
    assert_eq!(mirror.live_supply, locked_amount);
    assert_eq!(mirror.currently_locked, locked_amount);
    assert!(mirror.invariant_holds());

    // (3) replay safety: the same lock cannot mint twice.
    assert!(
        mirror
            .mint_against_lock_proof_anchored(&proof, &anchor, false, None)
            .is_err(),
        "a second mint of the same lock id must be rejected"
    );

    eprintln!(
        "solana_local_e2e OK: real local lock of {locked_amount} (mint {}) at slot {slot} \
         epoch {epoch} verified (ConsensusVerified) + minted conserved mirror credit; \
         effective stake {} from real bank state.",
        bs58::encode(spl_mint).into_string(),
        derived.table.total_stake(),
    );
}
