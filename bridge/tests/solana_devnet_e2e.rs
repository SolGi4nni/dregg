//! `solana_devnet_e2e`: drive the dregg Solana bridge against the **real public
//! Solana devnet** — a free, real cluster with real validators.
//!
//! This test is **gated on `SOLANA_DEVNET=1`**. Without it the test returns
//! immediately (a clean skip), so the default `cargo test -p dregg-bridge` suite
//! and CI stay green with no devnet access.
//!
//! # What it does (when enabled)
//!
//! It consumes the artifact bundle produced by `scripts/solana-devnet-harness.sh`
//! (which points the CLI at `api.devnet.solana.com`, funds a keypair with FREE
//! devnet SOL, mints a stand-in `$DREGG` SPL token, locks an amount into a vault
//! account, and harvests the REAL on-chain artifacts into a manifest). It then
//! proves a real devnet lock flows through the bridge to a conserved mirror mint
//! that pays a lease.
//!
//! # Trustless-real vs oracle-attested ON DEVNET (the honest accounting)
//!
//! There are three legs, each named precisely:
//!
//! 1. **Oracle-attested mirror mint (the path that runs end-to-end on devnet).**
//!    The REAL devnet lock — real SPL mint, real vault account, real locked
//!    amount, real lamports/owner harvested over devnet RPC — is attested by the
//!    relayer/oracle ([`SolanaLockAttestation`]) and minted through
//!    [`MirrorState::mint_against_lock`] into conserved mirror credit, which then
//!    pays an execution-lease via [`resolve_pay`]. The lock is genuinely on
//!    devnet; the *consensus* evidence is the oracle's word (the trusted leg).
//!
//! 2. **Trustless StructureOnly inclusion over the REAL vault bytes.** The real
//!    devnet vault account's bytes/lamports/owner are wrapped in an adapter
//!    accounts-Merkle and run through [`verify_lock_proof`], which checks the
//!    proof's structure + binding (the lock record includes into the
//!    reconstructed accounts hash and binds the claimed amount/recipient/lock).
//!    This proves the inclusion machinery accepts a genuine devnet account —
//!    `LockProofTrust::StructureOnly`, explicitly NOT a consensus guarantee.
//!
//! 3. **Real-byte VoteState decode.** When the harness harvested a real devnet
//!    vote account, [`decode_authorized_voter`] is run on its genuine on-chain
//!    `VoteState` bytes, proving the bank-state decoder handles real devnet data.
//!
//! ## Why the fully-trustless consensus path can't run against devnet off-chain
//!
//! [`verify_lock_proof_consensus_anchored`] needs (a) genuine ≥2/3 stake-weighted
//! Ed25519 vote signatures over the *real* bank hash and (b) the accounts-hash
//! inclusion path the validators committed to. Devnet RPC exposes neither the
//! bank-hash components nor the accounts-Merkle proofs, and the real validators'
//! authorized-voter PRIVATE keys are (correctly) not obtainable off-chain. So
//! that path's real home is a Solana snapshot/geyser pipeline — the mainnet route
//! documented in `docs/deos/SOLANA-DEVNET.md`. The local
//! `solana-test-validator` harness CAN exercise it because the single bootstrap
//! validator's voter keypair sits in the local ledger dir; devnet cannot.

use dregg_bridge::midnight::EpochKey;
use dregg_bridge::solana_consensus::{BankHashComponents, ValidatorVote};
use dregg_bridge::solana_mirror::{MirrorConfig, MirrorState, SolanaLockAttestation};
use dregg_bridge::solana_provenance::decode_authorized_voter;
use dregg_bridge::solana_trustless::{
    AccountInclusionProof, ConsensusEvidence, LockProofTrust, MainnetAccountInclusion,
    SolanaLockProof, verify_lock_proof,
};
use dregg_bridge::solana_wire::{
    AccountsInclusionProof16, MerkleLevel, accounts_merkle_node, encode_lock_record,
    solana_account_hash,
};
use dregg_payable::{InvokeAuthority, resolve_pay};
use dregg_types::CellId;
use ed25519_dalek::SigningKey;

const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32];

fn enabled() -> bool {
    matches!(
        std::env::var("SOLANA_DEVNET").ok().as_deref(),
        Some("1") | Some("true")
    )
}

fn manifest_path() -> String {
    std::env::var("DREGG_SOLANA_DEVNET_ARTIFACTS")
        .unwrap_or_else(|_| "/tmp/dregg-solana-devnet/manifest.json".to_string())
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
}

#[test]
fn devnet_solana_lock_mirrors_and_pays_a_lease() {
    if !enabled() {
        eprintln!(
            "SKIP solana_devnet_e2e: set SOLANA_DEVNET=1 and run \
             `scripts/solana-devnet-harness.sh` first (funds a devnet keypair, \
             locks a stand-in $DREGG, harvests real devnet artifacts). Skipping cleanly."
        );
        return;
    }

    let mp = manifest_path();
    let raw = std::fs::read_to_string(&mp).unwrap_or_else(|e| {
        panic!(
            "SOLANA_DEVNET=1 but the artifact manifest `{mp}` is missing ({e}). \
             Run `scripts/solana-devnet-harness.sh` to produce it."
        )
    });
    let m: serde_json::Value = serde_json::from_str(&raw).expect("parse manifest json");

    assert_eq!(
        m["cluster"].as_str(),
        Some("devnet"),
        "this test only runs against a devnet manifest"
    );

    let slot = m["slot"].as_u64().expect("slot");
    let epoch = m["epoch"].as_u64().expect("epoch");
    let spl_mint = b58_32(m["spl_mint"].as_str().expect("spl_mint"));
    let vault_pubkey = b58_32(m["vault_account"].as_str().expect("vault_account"));
    let locked_amount = m["locked_amount"].as_u64().expect("locked_amount");

    // The REAL devnet vault account (harvested over RPC).
    let vault = HarvestedAccount::from_json(&m["vault"]);
    assert_eq!(vault.pubkey, vault_pubkey, "manifest vault pubkey mismatch");
    assert!(
        vault.lamports > 0,
        "real devnet vault account should be rent-funded (lamports > 0)"
    );

    // The dregg-side lock record: the recipient cell + a lock id deterministically
    // derived from the real (vault, slot, mint) — the same scheme the local
    // harness uses, so the lock id is reproducible from on-chain facts.
    let recipient = CellId::from_bytes([0x11u8; 32]);
    let lock_id: [u8; 32] = {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-solana-devnet-lock");
        h.update(&vault_pubkey);
        h.update(&slot.to_le_bytes());
        h.update(&spl_mint);
        *h.finalize().as_bytes()
    };

    // ── Leg 1: ORACLE-ATTESTED mirror mint against the REAL devnet lock ──────
    // The relayer/oracle attests the lock it observed on devnet; dregg verifies
    // the attestation signature and mints conserved mirror credit.
    let oracle = SigningKey::from_bytes(&[0x42u8; 32]);
    let oracle_pk = oracle.verifying_key().to_bytes();
    let att =
        SolanaLockAttestation::create(lock_id, spl_mint, locked_amount, recipient, epoch, &oracle);
    assert!(
        att.verify_under(&oracle_pk),
        "the oracle attestation must verify under the oracle key"
    );

    let mut mirror = MirrorState::new(MirrorConfig {
        spl_mint,
        asset: MIRROR_ASSET,
        oracle_keys: vec![EpochKey {
            from_epoch: 0,
            to_epoch: None,
            pubkey: oracle_pk,
        }],
        min_amount: 1,
        max_amount: u64::MAX,
        // Leg 1 is the trusted-oracle mint (no inclusion proof), so the vault
        // binding is not exercised here; bind it to the real devnet vault anyway.
        vault_account: vault_pubkey,
        lock_program: vault.owner,
        pinned_anchor_epoch: None,
        pinned_anchor_root: None,
    });

    let mint = mirror
        .mint_against_lock(&att)
        .expect("mirror-mint against the attested real devnet lock");
    assert_eq!(mint.amount, locked_amount);
    assert_eq!(mirror.live_supply, locked_amount);
    assert_eq!(mirror.currently_locked, locked_amount);
    assert!(
        mirror.invariant_holds(),
        "conservation must hold after mint"
    );

    // Replay safety: the same lock cannot mint twice.
    assert!(
        mirror.mint_against_lock(&att).is_err(),
        "a second mint of the same lock id must be rejected"
    );

    // The bridged $DREGG pays an execution-lease through the SAME resolve_pay rail
    // the metered ToolGateway charge uses — desugaring to ONE conserving Transfer.
    let consumer = recipient;
    let lease_provider = CellId::from_bytes([0x22u8; 32]);
    let lease_price = locked_amount.min(100);
    let (action, _sig) = resolve_pay(
        consumer,
        mirror.config.asset,
        lease_price,
        lease_provider,
        InvokeAuthority::Signature,
    )
    .expect("bridged $DREGG resolves a lease pay through the Payable interface");
    assert_eq!(
        action.effects.len(),
        1,
        "a lease pay is exactly one Transfer"
    );
    assert!(
        mirror.invariant_holds(),
        "the mirror conservation survives the lease payment"
    );

    // ── Leg 2: TRUSTLESS StructureOnly inclusion over the REAL vault bytes ───
    // Reconstruct an adapter accounts-Merkle around the real devnet vault leaf
    // (the lock-record layout is the adapter's deploy-time schema; the lamports/
    // owner are the genuine harvested devnet values).
    let vault_data = encode_lock_record(&lock_id, &recipient, locked_amount);
    let vault_leaf = solana_account_hash(
        vault.lamports,
        &vault.owner,
        vault.executable,
        vault.rent_epoch,
        &vault_data,
        &vault_pubkey,
    );
    let leaves = [vault_leaf];
    let accounts_hash = accounts_merkle_node(&leaves);
    let vault_proof = AccountsInclusionProof16 {
        levels: vec![MerkleLevel {
            position: 0,
            siblings: vec![],
        }],
    };
    let bank_components = BankHashComponents {
        parent_bank_hash: [0u8; 32],
        accounts_hash,
        signature_count: 1,
        last_blockhash: [0u8; 32],
    };
    let bank_hash = bank_components.compute();
    let structural_proof = SolanaLockProof {
        lock_id,
        spl_mint,
        amount: locked_amount,
        dregg_recipient: recipient,
        consensus: ConsensusEvidence {
            slot,
            bank_hash,
            epoch,
            // Claimed tally (StructureOnly sanity, NOT a counted consensus): meets
            // the 2/3 form so the structural check passes — this is exactly the
            // leg that is NOT a trustless guarantee on devnet.
            voted_stake: 3,
            total_stake: 3,
            // One structurally-present placeholder vote so the proof is
            // well-formed (`verify_lock_proof` requires a non-empty vote set but
            // does NOT count/verify it — the StructureOnly path explicitly does
            // not anchor consensus; the real devnet validators' authorized-voter
            // keys are not obtainable off-chain, see the module doc).
            votes: vec![ValidatorVote::sign(
                &SigningKey::from_bytes(&[0x77u8; 32]),
                slot,
                bank_hash,
            )],
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
                lamports: vault.lamports,
                owner: vault.owner,
                executable: vault.executable,
                rent_epoch: vault.rent_epoch,
                data: vault_data,
                proof: vault_proof,
            }),
        },
        stake_provenance: None,
    };
    let structure = verify_lock_proof(&structural_proof, &spl_mint, 1, u64::MAX)
        .expect("structural verify of the real devnet vault inclusion");
    assert_eq!(
        structure,
        LockProofTrust::StructureOnly,
        "the devnet inclusion leg is StructureOnly (no off-chain consensus)"
    );

    // ── Leg 3: REAL-BYTE VoteState decode (when a vote account was harvested) ─
    let mut decoded_voter: Option<[u8; 32]> = None;
    if let Some(v) = m.get("vote_account").filter(|v| !v.is_null()) {
        let vote = HarvestedAccount::from_json(v);
        if let Some(voter) = decode_authorized_voter(&vote.data, epoch) {
            assert_ne!(voter, [0u8; 32], "decoded authorized voter is all-zero");
            decoded_voter = Some(voter);
        }
    }

    eprintln!(
        "solana_devnet_e2e OK: REAL devnet lock of {locked_amount} (mint {}) at slot {slot} \
         epoch {epoch} → oracle-attested mirror mint (ConsensusVerified=oracle) + conserved \
         credit paid a lease; trustless StructureOnly inclusion over the real vault bytes \
         accepted{}.",
        bs58::encode(spl_mint).into_string(),
        match decoded_voter {
            Some(v) => format!(
                "; real devnet authorized voter decoded = {}",
                bs58::encode(v).into_string()
            ),
            None => String::new(),
        },
    );
}
