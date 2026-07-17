//! `solana_feed` — the **feed-source seam** for non-custodial proof-of-holdings:
//! one trait every evidence source implements, so the verifier
//! ([`prove_holding_consensus_anchored`]) never cares whether its
//! [`HoldingProof`] came from a fixture cluster, a live local
//! `solana-test-validator`, or the mainnet snapshot/geyser pipeline.
//!
//! This closes the first rung of the named residual in
//! `docs/deos/PROOF-OF-HOLDINGS.md` ("Live-feed ingestion"): before this module,
//! every consensus-verified holding was assembled by in-test fixture
//! constructors; nothing had ever been *ingested*. The seam here is implemented
//! by three sources:
//!
//! 1. [`FixtureFeedSource`] (test/dev only) — wraps the existing
//!    [`crate::solana_holdings::fixtures`] builders, so every test that used the
//!    constructors directly can flow through the same trait the live sources use.
//! 2. [`LocalValidatorFeed`] — **live RPC ingestion** from a running
//!    `solana-test-validator`: it fetches the holder's token account, the
//!    bootstrap vote/stake accounts, and the StakeHistory sysvar over real
//!    Solana JSON-RPC (base64 account bytes, finalized commitment), derives the
//!    stake table from those real bank-state bytes, and signs a real TowerSync
//!    vote with the ledger's own authorized-voter keypair. This drives the
//!    production verifier green against *real bank state* (see the honest
//!    accounting below).
//! 3. The mainnet **snapshot source** — designed below, not yet built (the next
//!    rung). It implements the same trait.
//!
//! # Harvested-real vs adapter-shaped (honest accounting, local source)
//!
//! [`LocalValidatorFeed`] mirrors the seams of `bridge/tests/solana_local_e2e.rs`:
//!
//! **Harvested real from the live cluster over RPC:**
//! - the holder's SPL token account bytes (mint / wallet-owner / amount — the
//!   balance being proven), its lamports and owner *program*;
//! - the vote account's real `VoteState` bytes → decoded authorized voter;
//! - the stake account's real `StakeStateV2` bytes → decoded delegation (the
//!   effective stake the 2/3 threshold is measured against);
//! - the `StakeHistory` sysvar's real bytes → the warmup/cooldown curve input;
//! - the finalized slot + epoch (`getEpochInfo`);
//! - the ledger's real authorized-voter **keypair**, so the counted vote carries
//!   a genuine Ed25519 signature by the on-chain authority.
//!
//! **Adapter-shaped (reconstructed — the reason this source is dev-cluster-only):**
//! - the **accounts-hash 16-ary Merkle tree** is rebuilt around the real account
//!   leaves (Solana RPC exposes neither the bank-hash-committed accounts-Merkle
//!   proofs nor the bank-hash preimage — see the snapshot design);
//! - the **bank-hash components** are assembled around that accounts hash, and
//!   the vote is signed over the *reconstructed* bank hash. Only a local cluster
//!   can do this at all, because only there is the authorized-voter private key
//!   on disk. A real validator set never signs a reconstructed hash — which is
//!   exactly why this source cannot (and must not) impersonate mainnet.
//!
//! So the local source proves the **entire production verifier path end-to-end
//! over real bank state** — real decoders, real stake derivation, real
//! authorized-voter binding, real Ed25519 votes — while the *commitment* legs
//! (accounts Merkle, bank-hash preimage) remain the named reconstruction seam
//! that only the snapshot pipeline closes. It does NOT make a remote RPC
//! trustless; its endpoint gate refuses non-loopback plaintext.
//!
//! # The anchor is the caller's, never the feed's
//!
//! A [`HoldingFeed`] carries the anchor the source *derived*
//! ([`HoldingFeed::derived_anchor`]) purely as an operator bootstrapping report
//! (pin-once, out of band). Verification MUST pin the anchor from
//! governance-chosen configuration: [`prove_feed_holding`] takes the pinned
//! anchor (and the expected mint + SPL Token program) from the CALLER, so a
//! compromised feed that fabricates a stake distribution and a matching anchor
//! is refused with [`ProvenanceError::AnchorRootMismatch`] — the adversarial
//! test `feed_cannot_self_authorize_against_a_different_pin` is the falsifier.
//!
//! # Design: the mainnet snapshot source (the next rung, same trait)
//!
//! Public JSON-RPC — mainnet, devnet, or your own full node — **cannot** feed
//! the trustless path. Exactly these artifacts come from a snapshot archive (an
//! Agave full snapshot, `snapshot-<slot>-<hash>.tar.zst`) and are structurally
//! absent from RPC:
//!
//! 1. **The bank-hash preimage** ([`BankHashComponents`]): `parent_bank_hash`,
//!    the committed accounts hash (`accounts_delta_hash`, or the lattice hash
//!    post-SIMD-215), `signature_count`, and `last_blockhash` for the snapshot
//!    slot. RPC's `getBlock` returns blockhashes but NEVER the bank-hash
//!    components a vote signs over, so no RPC response can be bound to what the
//!    validators actually voted. The snapshot's serialized bank fields carry all
//!    four.
//! 2. **The full accounts DB at the slot** (the AppendVec/tiered-storage files):
//!    every account's `(lamports, owner, executable, rent_epoch, data, pubkey)`,
//!    from which the REAL 16-ary accounts-hash Merkle tree is computed and a
//!    REAL inclusion proof ([`AccountsInclusionProof16`]) extracted for ANY
//!    account — the holder's token account, every stake and vote account, and
//!    the StakeHistory sysvar. RPC returns account echoes served at "some slot"
//!    with no path binding them to any commitment (`getAccountInfo` has no
//!    proof), and `getProgramAccounts` over the stake program is
//!    disabled/rate-limited on public mainnet RPC anyway.
//! 3. **The epoch stake set + rotation chain**: the complete stake/vote account
//!    set needed to derive the mainnet [`EpochStakeTable`](crate::solana_consensus::EpochStakeTable)
//!    via [`derive_stake_table`], and — from snapshots at successive epoch
//!    boundaries — the [`crate::solana_provenance::RotationStep`] chain from the
//!    governance-pinned anchor epoch to the snapshot epoch.
//!
//! What the snapshot does NOT provide (and where it comes from instead):
//!
//! - **Votes**: real TowerSync vote *transactions* are harvested from the live
//!   feed — a Geyser plugin streaming vote transactions, or full-transaction
//!   `getBlock` harvesting (vote transactions and their signatures DO appear in
//!   blocks) — selecting votes whose voted bank hash is the snapshot slot's
//!   bank hash (votes for slot S land in descendant blocks). Ingested by the
//!   existing [`ingest_vote_transaction`] wire parser; ≥2/3 of the derived
//!   stake must sign, each by its proven on-chain authorized voter.
//! - **PoH segments**: entry chains from the ledger / Geyser for the
//!   [`PohAnchorPolicy`] bounded-anchor check (optional; `require_poh` says so).
//! - **The anchor**: governance pins the [`WeakSubjectivityAnchor`] — never any
//!   feed.
//!
//! Pipeline shape: `SnapshotFeed { archive_path, vote_harvester }` implements
//! [`HoldingFeedSource`] by (1) unpacking bank fields → [`BankHashComponents`],
//! (2) walking the accounts DB → per-account hashes → the real Merkle +
//! inclusion proofs for holder/stake/vote/sysvar accounts, (3)
//! [`derive_stake_table`] + rotation from the pinned anchor epoch, (4) matching
//! harvested ≥2/3-stake votes to the snapshot bank hash, (5) assembling the
//! same [`HoldingProof`] this module already emits. Nothing downstream changes:
//! the verifier entry stays [`prove_holding_consensus_anchored`].

use std::path::Path;

use crate::solana_consensus::{BankHashComponents, PohAnchorPolicy, ValidatorVote};
use crate::solana_holdings::{
    HoldingAccount, HoldingProof, HoldingProofError, ProvenHolding,
    prove_holding_consensus_anchored,
};
use crate::solana_provenance::{
    ProvenAccount, ProvenanceError, STAKE_HISTORY_SYSVAR_ID, WeakSubjectivityAnchor,
    decode_authorized_voter, derive_stake_table,
};
use crate::solana_relayer::{JsonRpcTransport, StdHttpTransport};
use crate::solana_trustless::{ConsensusEvidence, StakeProvenance};
use crate::solana_wire::{
    AccountsInclusionProof16, MERKLE_FANOUT, MerkleLevel, accounts_merkle_node,
    ingest_vote_transaction, solana_account_hash,
};
use ed25519_dalek::SigningKey;

/// The Solana **SPL Token program** id
/// (`TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`) — the program that must own a
/// token account for its 165-byte data to be an authoritative balance
/// (the load-bearing owner-program gate in
/// [`prove_holding_consensus_anchored`]). A constant of the protocol; decoded at
/// runtime from the canonical base58 (same pattern as
/// [`crate::solana_provenance::vote_program_id`]).
pub fn spl_token_program_id() -> [u8; 32] {
    let v = bs58::decode("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA")
        .into_vec()
        .expect("canonical SPL Token program id decodes");
    let mut out = [0u8; 32];
    out.copy_from_slice(&v);
    out
}

/// One ingested holder snapshot: everything the anchored verifier needs, plus
/// the source's *derived* anchor report.
#[derive(Clone, Debug)]
pub struct HoldingFeed {
    /// The assembled proof: the holder's own account + consensus evidence +
    /// bank-state stake provenance. Fed to [`prove_holding_consensus_anchored`].
    pub proof: HoldingProof,
    /// The weak-subjectivity anchor the SOURCE derived from the bank state it
    /// ingested. **A bootstrapping report only** — an operator may pin it once,
    /// out of band, after inspecting the cluster. Verification must use the
    /// governance-pinned anchor from configuration ([`prove_feed_holding`]
    /// takes it from the caller); verifying against `derived_anchor` blindly
    /// would let a compromised feed self-authorize a fabricated distribution.
    pub derived_anchor: WeakSubjectivityAnchor,
    /// The PoH bounded-anchor policy for the proof's PoH segment, when the
    /// source ingested one (`None` ⟹ the proof carries no PoH segment and must
    /// be verified with `require_poh = false`).
    pub poh_policy: Option<PohAnchorPolicy>,
}

/// Why a feed source could not produce a [`HoldingFeed`]. A refusal here is an
/// *ingestion* failure — verification failures are [`HoldingProofError`], from
/// the verifier, against the caller's pinned anchor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FeedError {
    /// The RPC transport/envelope failed, or the endpoint was refused by the
    /// loopback-plaintext gate.
    Rpc(String),
    /// A ledger-directory artifact (a keypair file) was missing or malformed.
    Ledger(String),
    /// A required account does not exist at finalized commitment.
    AccountMissing {
        /// The pubkey that was absent.
        pubkey: [u8; 32],
    },
    /// The vote account's on-chain authorized voter (for the evidence epoch) is
    /// not the key the feed can sign with — the ledger keypair does not control
    /// this cluster's vote account, so no genuine vote can be produced.
    VoterKeyMismatch {
        /// The authorized voter decoded from the on-chain `VoteState`.
        on_chain: [u8; 32],
        /// The pubkey of the keypair the feed holds.
        ledger: [u8; 32],
    },
    /// The vote account's `VoteState` bytes did not decode an authorized voter
    /// for the evidence epoch.
    UndecodableVoteState,
    /// Deriving the stake table from the ingested bank-state accounts failed.
    Derive(ProvenanceError),
    /// The feed-built vote transaction did not ingest through the wire parser
    /// (an internal invariant — a bug, not an environment condition).
    VoteIngest(String),
    /// A snapshot-parsing stage is **DESIGNED but NOT YET BUILT** (Track A rung 2 —
    /// the real Agave snapshot format). Returned by [`AgaveSnapshotBank`] so a
    /// pending path fails LOUD rather than silently passing with fabricated data;
    /// `stage` names exactly which leg of the pipeline
    /// (`bridge/src/solana_feed.rs:113`–`:120`) is unbuilt.
    NotYetImplemented {
        /// The unbuilt pipeline stage, e.g. "unpack Agave snapshot bank fields".
        stage: &'static str,
    },
}

impl std::fmt::Display for FeedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Rpc(e) => write!(f, "feed rpc error: {e}"),
            Self::Ledger(e) => write!(f, "feed ledger artifact error: {e}"),
            Self::AccountMissing { pubkey } => write!(
                f,
                "account {} absent at finalized commitment",
                bs58::encode(pubkey).into_string()
            ),
            Self::VoterKeyMismatch { on_chain, ledger } => write!(
                f,
                "on-chain authorized voter {} is not the ledger keypair {}",
                bs58::encode(on_chain).into_string(),
                bs58::encode(ledger).into_string()
            ),
            Self::UndecodableVoteState => {
                write!(f, "vote account data did not decode an authorized voter")
            }
            Self::Derive(e) => write!(f, "stake-table derivation failed: {e}"),
            Self::VoteIngest(e) => write!(f, "feed-built vote failed wire ingestion: {e}"),
            Self::NotYetImplemented { stage } => write!(
                f,
                "snapshot parsing stage not yet implemented (Track A rung 2): {stage}"
            ),
        }
    }
}

impl std::error::Error for FeedError {}

/// **The feed-source seam.** Every proof-of-holdings evidence source — fixture
/// clusters, the live local-validator feed, the future mainnet snapshot/geyser
/// pipeline — implements this one method: ingest whatever the source observes
/// and assemble the [`HoldingFeed`] for one holder token account. Sources
/// gather evidence; they never decide trust — that is
/// [`prove_holding_consensus_anchored`]'s job, against the CALLER's pinned
/// anchor ([`prove_feed_holding`]).
pub trait HoldingFeedSource {
    /// Ingest the evidence for `token_account` (the holder's own SPL token
    /// account — never a vault) and assemble the anchored [`HoldingFeed`].
    fn ingest_holding(&self, token_account: &[u8; 32]) -> Result<HoldingFeed, FeedError>;
}

/// Verify an ingested feed through the PRODUCTION anchored entry —
/// [`prove_holding_consensus_anchored`] — with the trust roots taken from the
/// **caller** (governance-pinned `pinned_anchor`, the expected `dregg_mint`,
/// and the SPL Token program id), never from the feed. The only path from a
/// [`HoldingFeed`] to a [`LockProofTrust::ConsensusVerified`](crate::solana_trustless::LockProofTrust::ConsensusVerified)
/// [`ProvenHolding`].
pub fn prove_feed_holding(
    feed: &HoldingFeed,
    dregg_mint: &[u8; 32],
    spl_token_program: &[u8; 32],
    pinned_anchor: &WeakSubjectivityAnchor,
    require_poh: bool,
) -> Result<ProvenHolding, HoldingProofError> {
    prove_holding_consensus_anchored(
        &feed.proof,
        dregg_mint,
        spl_token_program,
        pinned_anchor,
        require_poh,
        feed.poh_policy.as_ref(),
    )
}

// ===========================================================================
// A minimal finalized-commitment JSON-RPC view (the feed's own thin client)
// ===========================================================================

/// A finalized account as the feed ingests it: exactly the per-account-hash
/// preimage fields ([`solana_account_hash`]) plus the raw data bytes.
#[derive(Clone, Debug)]
struct FetchedAccount {
    lamports: u64,
    owner: [u8; 32],
    executable: bool,
    rent_epoch: u64,
    data: Vec<u8>,
}

impl FetchedAccount {
    fn leaf(&self, pubkey: &[u8; 32]) -> [u8; 32] {
        solana_account_hash(
            self.lamports,
            &self.owner,
            self.executable,
            self.rent_epoch,
            &self.data,
            pubkey,
        )
    }

    fn proven(&self, pubkey: [u8; 32], proof: AccountsInclusionProof16) -> ProvenAccount {
        ProvenAccount {
            pubkey,
            lamports: self.lamports,
            owner: self.owner,
            executable: self.executable,
            rent_epoch: self.rent_epoch,
            data: self.data.clone(),
            proof,
        }
    }
}

fn b58_32(s: &str) -> Result<[u8; 32], FeedError> {
    let v = bs58::decode(s)
        .into_vec()
        .map_err(|e| FeedError::Rpc(format!("base58 decode of `{s}`: {e}")))?;
    if v.len() != 32 {
        return Err(FeedError::Rpc(format!(
            "pubkey `{s}` is {} bytes, not 32",
            v.len()
        )));
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&v);
    Ok(out)
}

/// One JSON-RPC call over the injected byte-pipe (the same [`JsonRpcTransport`]
/// seam the relayer uses; TLS is a deploy concern, not a core dependency).
fn rpc_call<T: JsonRpcTransport>(
    transport: &T,
    url: &str,
    method: &str,
    params: serde_json::Value,
) -> Result<serde_json::Value, FeedError> {
    let req = serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": method, "params": params});
    let body = serde_json::to_string(&req).map_err(|e| FeedError::Rpc(e.to_string()))?;
    let resp = transport
        .post(url, &body)
        .map_err(|e| FeedError::Rpc(e.to_string()))?;
    let v: serde_json::Value =
        serde_json::from_str(&resp).map_err(|e| FeedError::Rpc(format!("bad rpc json: {e}")))?;
    if let Some(err) = v.get("error") {
        return Err(FeedError::Rpc(format!("rpc error object: {err}")));
    }
    v.get("result")
        .cloned()
        .ok_or_else(|| FeedError::Rpc("rpc response has no result".into()))
}

/// `getEpochInfo({commitment: finalized})` → `(absolute_slot, epoch)`.
fn rpc_epoch_info<T: JsonRpcTransport>(transport: &T, url: &str) -> Result<(u64, u64), FeedError> {
    let r = rpc_call(
        transport,
        url,
        "getEpochInfo",
        serde_json::json!([{"commitment": "finalized"}]),
    )?;
    let slot = r["absoluteSlot"]
        .as_u64()
        .ok_or_else(|| FeedError::Rpc("getEpochInfo missing absoluteSlot".into()))?;
    let epoch = r["epoch"]
        .as_u64()
        .ok_or_else(|| FeedError::Rpc("getEpochInfo missing epoch".into()))?;
    Ok((slot, epoch))
}

/// `getAccountInfo(pubkey, {encoding: base64, commitment: finalized})`.
fn rpc_account<T: JsonRpcTransport>(
    transport: &T,
    url: &str,
    pubkey: &[u8; 32],
) -> Result<FetchedAccount, FeedError> {
    use base64::Engine as _;
    let r = rpc_call(
        transport,
        url,
        "getAccountInfo",
        serde_json::json!([
            bs58::encode(pubkey).into_string(),
            {"encoding": "base64", "commitment": "finalized"}
        ]),
    )?;
    let value = &r["value"];
    if value.is_null() {
        return Err(FeedError::AccountMissing { pubkey: *pubkey });
    }
    let lamports = value["lamports"]
        .as_u64()
        .ok_or_else(|| FeedError::Rpc("account missing lamports".into()))?;
    let owner = b58_32(
        value["owner"]
            .as_str()
            .ok_or_else(|| FeedError::Rpc("account missing owner".into()))?,
    )?;
    let executable = value["executable"].as_bool().unwrap_or(false);
    let rent_epoch = value["rentEpoch"].as_u64().unwrap_or(0);
    let data_b64 = value["data"][0]
        .as_str()
        .ok_or_else(|| FeedError::Rpc("account data is not [base64, encoding]".into()))?;
    let data = base64::engine::general_purpose::STANDARD
        .decode(data_b64)
        .map_err(|e| FeedError::Rpc(format!("account data base64: {e}")))?;
    Ok(FetchedAccount {
        lamports,
        owner,
        executable,
        rent_epoch,
        data,
    })
}

/// Endpoint gate (the relayer's BR-3 posture, restated for the feed): accept
/// `https://` always; accept plaintext `http://` ONLY for an unambiguous
/// loopback host. A live-network plaintext feed would let an on-path MITM feed
/// fabricated account bytes into the reconstruction seam.
fn require_loopback_or_tls(url: &str) -> Result<(), FeedError> {
    if url.starts_with("https://") {
        return Ok(());
    }
    let Some(rest) = url.strip_prefix("http://") else {
        return Err(FeedError::Rpc(format!(
            "unsupported endpoint scheme in `{url}` (want https:// or loopback http://)"
        )));
    };
    let authority = rest.split(['/', '?', '#']).next().unwrap_or(rest);
    let host = if let Some(v6) = authority.strip_prefix('[') {
        v6.split(']').next().unwrap_or(v6).to_string()
    } else {
        authority
            .rsplit_once(':')
            .map_or(authority, |(h, _)| h)
            .to_string()
    };
    if host == "127.0.0.1" || host == "localhost" || host == "::1" {
        Ok(())
    } else {
        Err(FeedError::Rpc(format!(
            "plaintext endpoint `{url}` is not loopback ({host}): plaintext RPC is permitted \
             only for a local solana-test-validator"
        )))
    }
}

/// A single 16-ary chunk of inclusion proofs: `proofs[i]` places `leaves[i]`
/// among the rest (the reconstruction seam — see the module doc; the snapshot
/// source replaces this with proofs extracted from the committed accounts DB).
fn single_chunk_proofs(leaves: &[[u8; 32]]) -> Vec<AccountsInclusionProof16> {
    assert!(
        leaves.len() <= MERKLE_FANOUT,
        "single-chunk reconstruction holds at most {MERKLE_FANOUT} leaves"
    );
    (0..leaves.len())
        .map(|i| AccountsInclusionProof16 {
            levels: vec![MerkleLevel {
                position: i as u8,
                siblings: leaves
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, h)| *h)
                    .collect(),
            }],
        })
        .collect()
}

/// Build a real-wire legacy Solana vote `Transaction` carrying a `TowerSync`
/// vote for `(slot, bank_hash)` by `vote_account`, signed by `authority` — the
/// shape [`ingest_vote_transaction`] parses and
/// [`VerifiedStakeTable::tally_authorized`](crate::solana_provenance::VerifiedStakeTable::tally_authorized)
/// counts. Only the local source can call this meaningfully: it requires the
/// authorized-voter private key, which exists on disk only in a local ledger.
fn build_tower_sync_tx(
    authority: &SigningKey,
    vote_account: [u8; 32],
    slot: u64,
    bank_hash: [u8; 32],
) -> Vec<u8> {
    // The exact-slot ("which bank hash") vote carries NO tower root, so it never
    // counts toward the rooted-finality tally — that is the rooted harvester's job
    // ([`LedgerVoteHarvester`] / [`build_tower_sync_tx_rooted`]).
    build_tower_sync_vote_tx(authority, vote_account, slot, bank_hash, None)
}

/// Build a real-wire legacy vote `Transaction` carrying a `TowerSync` for
/// `(voted_slot, bank_hash)` by `vote_account`, signed by `authority`, and
/// carrying tower root `Some(r)` — the **rooted-finality** attestation
/// [`crate::solana_provenance::VerifiedStakeTable::tally_authorized_rooted`]
/// counts. A genuine rooted attestation of a lock slot `S` is a LATER vote
/// (`voted_slot > S`) whose `root ≥ S`; a tower cannot root its own last-voted
/// slot. Only a local source can call this meaningfully (it needs the
/// authorized-voter private key).
fn build_tower_sync_tx_rooted(
    authority: &SigningKey,
    vote_account: [u8; 32],
    voted_slot: u64,
    bank_hash: [u8; 32],
    root: u64,
) -> Vec<u8> {
    build_tower_sync_vote_tx(authority, vote_account, voted_slot, bank_hash, Some(root))
}

/// Shared wire builder for both the exact-slot ([`build_tower_sync_tx`], `root =
/// None`) and rooted-finality ([`build_tower_sync_tx_rooted`], `root = Some(r)`)
/// votes. The tower root travels inside the serialized `TowerSync` instruction
/// data, so the message framing is identical either way.
fn build_tower_sync_vote_tx(
    authority: &SigningKey,
    vote_account: [u8; 32],
    voted_slot: u64,
    bank_hash: [u8; 32],
    root: Option<u64>,
) -> Vec<u8> {
    use ed25519_dalek::Signer as _;
    use solana_vote_interface::instruction::VoteInstruction;
    use solana_vote_interface::state::{Lockout, TowerSync};

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
    // `TowerSync.hash` is `solana_hash::Hash`; `From<[u8; 32]>` names the type
    // without depending on the (test-utils-optional) `solana-hash` crate.
    tower.hash = bank_hash.into();
    tower.root = root;
    tower.lockouts.push_back(Lockout::new(voted_slot));
    let ix = VoteInstruction::TowerSync(tower);
    let ix_data = bincode::serialize(&ix).expect("serialize TowerSync vote instruction");

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
    message.push(2u8); // program_id_index (the vote program)
    push_compact_u16(&mut message, 2); // account metas
    message.push(1u8); // vote account
    message.push(0u8); // authority
    push_compact_u16(&mut message, ix_data.len() as u16);
    message.extend_from_slice(&ix_data);

    let sig = authority.sign(&message).to_bytes();
    let mut tx = Vec::new();
    push_compact_u16(&mut tx, 1);
    tx.extend_from_slice(&sig);
    tx.extend_from_slice(&message);
    tx
}

// ===========================================================================
// The rooted-attestation harvester seam (Track A, rung 1)
// ===========================================================================

/// **The rooted-vote harvester seam.** Value release
/// ([`crate::solana_trustless::verify_lock_proof_consensus_anchored`]) demands the
/// lock slot be **rooted (finalized)**, not merely optimistically confirmed: ≥ 2/3
/// of the derived stake must submit an authorized-voter-bound vote whose ingested
/// tower `root ≥ slot`
/// ([`crate::solana_provenance::VerifiedStakeTable::tally_authorized_rooted`]). The
/// exact-slot "which bank hash" votes a feed builds carry NO root, so a feed that
/// supplies only them correctly fails closed at
/// [`crate::solana_trustless::LockProofError::SlotNotRooted`]. This seam is the
/// source of the *later* rooted votes that clear the finality leg.
///
/// A genuine rooted attestation of slot `S` is a LATER vote (`voted_slot > S`)
/// whose `root ≥ S` — a tower roots strictly below its last vote. On mainnet these
/// are harvested from real descendant-block vote transactions (a Geyser stream, or
/// full-transaction `getBlock` — vote transactions and their signatures appear in
/// the blocks that descend from `S`); the future `SnapshotFeed` plugs its harvester
/// in here, sharing the seam with [`LocalValidatorFeed`]. On a local dev cluster the
/// feed holds the authorized-voter private keys and signs the later rooted votes
/// itself ([`LedgerVoteHarvester`]) — the same self-signed shape the exact-slot vote
/// already uses (see the module's honest accounting), because only a local ledger
/// exposes the voter key at all.
pub trait VoteHarvester {
    /// Gather the rooted attestations finalizing `slot`: later votes each carrying
    /// tower `root ≥ slot`, bound to a proven on-chain authorized voter and keyed
    /// by the vote account the stake table weights. An empty result ⟹ the slot is
    /// not (yet) rooted — the value path then fails closed at `SlotNotRooted`, so
    /// the leg is load-bearing, not decorative.
    fn harvest_rooted(&self, slot: u64) -> Result<Vec<ValidatorVote>, FeedError>;
}

/// One validator's signing capability for harvesting a rooted attestation on a
/// local/dev cluster: the authorized-voter keypair plus the vote account it
/// controls (the stake-table key). Only a local ledger exposes the private key —
/// which is exactly why [`LedgerVoteHarvester`] is dev-cluster-only, mirroring the
/// module's honest accounting for the exact-slot vote.
pub struct HarvestableVoter {
    /// The vote account's on-chain authorized voter keypair (the signer the
    /// rooted tally binds each counted vote to).
    pub vote_authority: SigningKey,
    /// The vote account the stake distribution weights.
    pub vote_account: [u8; 32],
}

/// **The local/dev-cluster rooted-vote harvester.** Holds the authorized-voter
/// keypairs (only a local ledger exposes them) and signs one later rooted
/// `TowerSync` vote per voter — the local-cluster analogue of a real Geyser/getBlock
/// harvest, with the SAME fidelity as [`build_tower_sync_tx`]'s exact-slot vote
/// (self-signed by the on-chain authorized voter over the reconstructed bank state).
/// It cannot impersonate mainnet: it can only sign for voters whose private key is
/// on disk, and its votes are counted by the rooted tally ONLY when the signer is
/// the vote account's proven on-chain authorized voter with stake in the derived
/// table.
pub struct LedgerVoteHarvester {
    voters: Vec<HarvestableVoter>,
    /// How many slots after the lock slot the rooted vote is cast. A tower roots
    /// strictly below its last vote, so the rooted attestation is necessarily a
    /// later vote (`voted_slot = slot + lookahead`, `root = slot`).
    lookahead: u64,
}

impl LedgerVoteHarvester {
    /// The default slots-past-the-lock-slot for the harvested rooted vote.
    pub const DEFAULT_LOOKAHEAD: u64 = 64;

    /// A harvester over `voters`, casting each rooted vote
    /// [`Self::DEFAULT_LOOKAHEAD`] slots past the lock slot.
    pub fn new(voters: Vec<HarvestableVoter>) -> Self {
        Self {
            voters,
            lookahead: Self::DEFAULT_LOOKAHEAD,
        }
    }

    /// A single-voter harvester (the shape [`LocalValidatorFeed`] uses: its ledger
    /// key is the cluster's sole authorized voter).
    pub fn single(vote_authority: SigningKey, vote_account: [u8; 32]) -> Self {
        Self::new(vec![HarvestableVoter {
            vote_authority,
            vote_account,
        }])
    }

    /// Override the [`Self::DEFAULT_LOOKAHEAD`] (the slots past the lock slot the
    /// rooted vote is cast at).
    pub fn with_lookahead(mut self, lookahead: u64) -> Self {
        self.lookahead = lookahead.max(1);
        self
    }
}

impl VoteHarvester for LedgerVoteHarvester {
    fn harvest_rooted(&self, slot: u64) -> Result<Vec<ValidatorVote>, FeedError> {
        // A distinct later bank hash for the rooted votes: the rooted tally checks
        // `root ≥ slot` + the authorized voter, NOT the voted bank hash (which
        // belongs to the later slot, not the lock slot). Domain-separated so it can
        // never collide with the exact-slot vote's `(slot, bank_hash)`.
        let voted_slot = slot.saturating_add(self.lookahead);
        let mut later_bank = [0xB1u8; 32];
        later_bank[..8].copy_from_slice(&voted_slot.to_le_bytes());
        let mut out = Vec::with_capacity(self.voters.len());
        for v in &self.voters {
            let tx = build_tower_sync_tx_rooted(
                &v.vote_authority,
                v.vote_account,
                voted_slot,
                later_bank,
                slot,
            );
            let vote = ingest_vote_transaction(&tx)
                .map_err(|e| FeedError::VoteIngest(format!("{e:?}")))?;
            out.push(vote);
        }
        Ok(out)
    }
}

/// Read a Solana CLI keypair file (a JSON array of 64 bytes: 32-byte seed ‖
/// 32-byte public) into a [`SigningKey`].
fn read_solana_keypair(path: &Path) -> Result<SigningKey, FeedError> {
    let raw = std::fs::read_to_string(path)
        .map_err(|e| FeedError::Ledger(format!("read keypair `{}`: {e}", path.display())))?;
    let arr: Vec<u8> = serde_json::from_str(&raw)
        .map_err(|e| FeedError::Ledger(format!("parse keypair `{}`: {e}", path.display())))?;
    if arr.len() != 64 {
        return Err(FeedError::Ledger(format!(
            "keypair `{}` is {} bytes, not 64",
            path.display(),
            arr.len()
        )));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&arr[..32]);
    Ok(SigningKey::from_bytes(&seed))
}

// ===========================================================================
// The live local-validator source
// ===========================================================================

/// **Live-RPC feed from a running `solana-test-validator`.** Ingests the
/// holder's token account, the bootstrap vote/stake accounts, and the
/// StakeHistory sysvar over real finalized-commitment JSON-RPC, derives the
/// stake table from those real bank-state bytes, and signs one genuine
/// TowerSync vote with the ledger's authorized-voter keypair.
///
/// **Dev-cluster-only by construction** (not by policy): it must hold the
/// authorized-voter *private key*, which only a local ledger provides, and its
/// endpoint gate refuses non-loopback plaintext. The mainnet source is the
/// snapshot pipeline in the module doc. See the module doc's honest accounting
/// for which legs are harvested-real vs reconstructed.
pub struct LocalValidatorFeed<T: JsonRpcTransport> {
    url: String,
    transport: T,
    /// The ledger's vote-account keypair: the vote account address AND (the
    /// test-validator default) its authorized voter. Checked at ingest against
    /// the on-chain `VoteState` — a cluster where they diverge is refused with
    /// [`FeedError::VoterKeyMismatch`].
    vote_authority: SigningKey,
    /// The bootstrap stake account (delegated to the vote account).
    stake_account: [u8; 32],
    /// The rooted-attestation harvester (the [`VoteHarvester`] seam): the source
    /// of the later `root ≥ slot` votes that clear the value-release
    /// rooted-finality leg. Defaults to a single-voter [`LedgerVoteHarvester`] over
    /// the ledger's own authorized-voter key; a caller may inject a different one
    /// (e.g. a real Geyser/getBlock harvester) via [`Self::with_harvester`].
    harvester: Box<dyn VoteHarvester + Send + Sync>,
}

impl<T: JsonRpcTransport> LocalValidatorFeed<T> {
    /// Build a feed over an injected transport. `url` must be `https://` or
    /// loopback `http://` (refused otherwise — see [`FeedError::Rpc`]).
    pub fn new(
        url: impl Into<String>,
        transport: T,
        vote_authority: SigningKey,
        stake_account: [u8; 32],
    ) -> Result<Self, FeedError> {
        let url = url.into();
        require_loopback_or_tls(&url)?;
        // Default rooted-vote harvester: the ledger key is this cluster's sole
        // authorized voter, so it signs the later rooted votes itself (dev-cluster
        // parity with the exact-slot vote — see the module honest accounting).
        let vote_account = vote_authority.verifying_key().to_bytes();
        let harvester = Box::new(LedgerVoteHarvester::single(
            vote_authority.clone(),
            vote_account,
        ));
        Ok(Self {
            url,
            transport,
            vote_authority,
            stake_account,
            harvester,
        })
    }

    /// Replace the default rooted-vote [`VoteHarvester`] (e.g. inject a real
    /// Geyser/getBlock harvester, or a multi-voter [`LedgerVoteHarvester`] for a
    /// local cluster with more than one validator). The exact-slot "which bank
    /// hash" vote is still built from the ledger key; only the rooted-finality
    /// attestations come from `harvester`.
    pub fn with_harvester(mut self, harvester: Box<dyn VoteHarvester + Send + Sync>) -> Self {
        self.harvester = harvester;
        self
    }
}

impl LocalValidatorFeed<StdHttpTransport> {
    /// Build the feed from a test-validator ledger directory: reads
    /// `vote-account-keypair.json` (the vote account + its authorized voter)
    /// and `stake-account-keypair.json` (the bootstrap stake account) — the
    /// same artifacts `scripts/solana-local-harness.sh` locates.
    pub fn from_ledger_dir(url: impl Into<String>, ledger_dir: &Path) -> Result<Self, FeedError> {
        let vote_authority = read_solana_keypair(&ledger_dir.join("vote-account-keypair.json"))?;
        let stake_kp = read_solana_keypair(&ledger_dir.join("stake-account-keypair.json"))?;
        let stake_account = stake_kp.verifying_key().to_bytes();
        Self::new(
            url,
            StdHttpTransport::default(),
            vote_authority,
            stake_account,
        )
    }
}

impl<T: JsonRpcTransport> HoldingFeedSource for LocalValidatorFeed<T> {
    fn ingest_holding(&self, token_account: &[u8; 32]) -> Result<HoldingFeed, FeedError> {
        let vote_account = self.vote_authority.verifying_key().to_bytes();

        // (1) the finalized snapshot point.
        let (slot, epoch) = rpc_epoch_info(&self.transport, &self.url)?;

        // (2) live account ingestion: the holder's own token account + the
        //     bank-state accounts the stake derivation proves from.
        let holder = rpc_account(&self.transport, &self.url, token_account)?;
        let vote = rpc_account(&self.transport, &self.url, &vote_account)?;
        let stake = rpc_account(&self.transport, &self.url, &self.stake_account)?;
        let stake_history = rpc_account(&self.transport, &self.url, &STAKE_HISTORY_SYSVAR_ID)?;

        // (3) the key we sign with must BE the on-chain authorized voter, or
        //     the produced vote would never be counted (fail loud, not weird).
        let on_chain =
            decode_authorized_voter(&vote.data, epoch).ok_or(FeedError::UndecodableVoteState)?;
        if on_chain != vote_account {
            return Err(FeedError::VoterKeyMismatch {
                on_chain,
                ledger: vote_account,
            });
        }

        // (4) the reconstruction seam (module doc): one 16-ary chunk over the
        //     real account leaves. Order: holder, vote, stake, stake-history.
        let leaves = [
            holder.leaf(token_account),
            vote.leaf(&vote_account),
            stake.leaf(&self.stake_account),
            stake_history.leaf(&STAKE_HISTORY_SYSVAR_ID),
        ];
        let accounts_hash = accounts_merkle_node(&leaves);
        let proofs = single_chunk_proofs(&leaves);

        let vote_pa = vote.proven(vote_account, proofs[1].clone());
        let stake_pa = stake.proven(self.stake_account, proofs[2].clone());
        let sh_pa = stake_history.proven(STAKE_HISTORY_SYSVAR_ID, proofs[3].clone());

        // (5) derive the stake table from the real bank-state bytes; the
        //     derived root is the operator's pin-once anchor report.
        let derived = derive_stake_table(
            epoch,
            &accounts_hash,
            std::slice::from_ref(&stake_pa),
            std::slice::from_ref(&vote_pa),
            &sh_pa,
            None,
        )
        .map_err(FeedError::Derive)?;
        let derived_anchor = WeakSubjectivityAnchor::from_table(&derived.table);

        // (6) bank-hash components assembled around the reconstructed accounts
        //     hash, and one genuine authorized-voter vote over the result.
        let bank_components = BankHashComponents {
            parent_bank_hash: [0u8; 32],
            accounts_hash,
            signature_count: 1,
            last_blockhash: [0u8; 32],
        };
        let bank_hash = bank_components.compute();
        let tx = build_tower_sync_tx(&self.vote_authority, vote_account, slot, bank_hash);
        let validator_vote =
            ingest_vote_transaction(&tx).map_err(|e| FeedError::VoteIngest(format!("{e:?}")))?;

        // (6b) ROOTED-FINALITY evidence (Track A, rung 1): the exact-slot vote
        // above is optimistic-confirmation grade (`root = None`) and cannot clear
        // `tally_authorized_rooted`, so a value-release verifier would fail closed
        // at `SlotNotRooted`. Harvest the later `root ≥ slot` votes through the
        // seam and carry BOTH sets in the evidence: the exact-slot tally selects
        // the `(slot, bank_hash)` votes, the rooted tally selects the rooted ones
        // (each ignores the other's subset — see [`ConsensusEvidence::votes`]).
        let mut votes = vec![validator_vote];
        votes.extend(self.harvester.harvest_rooted(slot)?);

        let total = derived.table.total_stake();
        let proof = HoldingProof {
            account: HoldingAccount {
                token_account: *token_account,
                lamports: holder.lamports,
                owner_program: holder.owner,
                executable: holder.executable,
                rent_epoch: holder.rent_epoch,
                data: holder.data,
                inclusion: proofs[0].clone(),
            },
            consensus: ConsensusEvidence {
                slot,
                bank_hash,
                epoch,
                voted_stake: total,
                total_stake: total,
                votes,
                bank_components,
                poh: None,
            },
            stake_provenance: Some(StakeProvenance {
                anchor_accounts_hash: accounts_hash,
                anchor_stake_accounts: vec![stake_pa],
                anchor_vote_accounts: vec![vote_pa],
                anchor_stake_history_account: sh_pa,
                new_rate_activation_epoch: None,
                rotation: vec![],
            }),
        };

        Ok(HoldingFeed {
            proof,
            derived_anchor,
            poh_policy: None,
        })
    }
}

// ===========================================================================
// The mainnet snapshot source (Track A, rung 2) — SCAFFOLD
// ===========================================================================
//
// This is the rung-2 SnapshotFeed scaffold. Its SHAPE is real and its trait
// wiring is real (a bank flows through the PRODUCTION anchored entry unchanged);
// its one honestly-labeled hole is the Agave snapshot *format* parsing, which
// returns [`FeedError::NotYetImplemented`] rather than fabricating bytes.
//
// The design lives in the module doc (`bridge/src/solana_feed.rs:70`–`:120`); the
// operator runbook that is gated on exactly this code landing is
// `docs/ops/SOLANA-ANCHOR-AND-SNAPSHOT-FEED.md` §7. What a snapshot provides that
// RPC structurally cannot: the bank-hash preimage, a REAL 16-ary accounts Merkle +
// inclusion proofs, and the full epoch stake set (module doc `:70`–`:97`).

/// **The parsed contents of one Agave snapshot bank, as `SnapshotFeed` consumes
/// them.** Everything the anchored verifier needs that RPC cannot bind to a
/// commitment (module doc `:70`–`:97`): the bank-hash preimage, the committed
/// accounts-hash Merkle root, and each account with a REAL
/// [`AccountsInclusionProof16`] extracted from the committed accounts DB
/// (holder / stake / vote / StakeHistory sysvar). A [`SnapshotBankSource`]
/// produces one of these; [`SnapshotFeed`] turns it into the same
/// [`HoldingProof`] the fixtures emit and runs it through
/// [`prove_holding_consensus_anchored`] unmodified.
///
/// All accounts are [`ProvenAccount`]s carrying real per-account leaves + 16-ary
/// proofs that fold to [`Self::accounts_hash`]. There is no `single_chunk`
/// reconstruction here (the local source's dev-only seam,
/// `bridge/src/solana_feed.rs:449`) — the snapshot's committed Merkle is the whole
/// point of this rung. (A fixture bank legitimately computes that Merkle over its
/// own small account set; a mainnet bank walks the AppendVec/tiered-storage DB.)
#[derive(Clone, Debug)]
pub struct SnapshotBank {
    /// The snapshot slot (the bank's slot).
    pub slot: u64,
    /// The epoch the snapshot slot falls in — the epoch the derived stake table
    /// and the harvested votes are for.
    pub epoch: u64,
    /// The committed accounts-hash Merkle root at the slot (the root every
    /// per-account proof folds to, and the value bound into [`Self::bank_components`]).
    pub accounts_hash: [u8; 32],
    /// The bank-hash preimage (`parent_bank_hash`, accounts hash, `signature_count`,
    /// `last_blockhash`) — the four fields RPC never returns (module doc `:76`–`:84`).
    /// `bank_components.compute()` is the `bank_hash` the harvested votes sign over.
    pub bank_components: BankHashComponents,
    /// The holder's own SPL token account, with its REAL inclusion proof.
    pub holder: ProvenAccount,
    /// The stake accounts whose delegations derive the epoch stake table.
    pub stake_accounts: Vec<ProvenAccount>,
    /// The vote accounts the stake distribution weights (each → its on-chain
    /// authorized voter, decoded during derivation).
    pub vote_accounts: Vec<ProvenAccount>,
    /// The `StakeHistory` sysvar account (the warmup/cooldown curve input).
    pub stake_history: ProvenAccount,
    /// The `reduce_stake_warmup_cooldown` feature epoch, if past it at the snapshot
    /// slot (`None` ⟹ the original 25% rate) — passed straight to
    /// [`derive_stake_table`].
    pub new_rate_activation_epoch: Option<u64>,
    /// The attested [`crate::solana_provenance::RotationStep`] chain from the
    /// governance-pinned anchor epoch to [`Self::epoch`]. Empty ⟺ the snapshot is
    /// AT the anchor epoch. On mainnet these come from snapshots at successive
    /// epoch boundaries (module doc `:93`–`:97`).
    pub rotation: Vec<crate::solana_provenance::RotationStep>,
    /// The exact-slot "which bank hash" votes AND the later rooted votes, harvested
    /// from a live Geyser/`getBlock` stream (the feed holds NO keys — module doc
    /// `:99`–`:107`) and matched to [`Self::bank_components`]`.compute()`. The
    /// exact-slot subset clears [`crate::solana_provenance::VerifiedStakeTable::tally_authorized`];
    /// the rooted subset clears `tally_authorized_rooted` for the value path.
    pub votes: Vec<ValidatorVote>,
}

/// **The snapshot-bank parsing seam.** One method: unpack a snapshot into the
/// committed [`SnapshotBank`] artifacts for a holder token account. The real
/// implementation ([`AgaveSnapshotBank`]) walks an Agave snapshot archive — that
/// format parsing is the one pending leg of rung 2 and returns
/// [`FeedError::NotYetImplemented`]; a fixture implementation feeds an in-memory
/// bank through the SAME [`SnapshotFeed`] path so the trait wiring and the
/// production-entry plumbing are exercised and tested today.
pub trait SnapshotBankSource {
    /// Parse the snapshot bank and extract the committed artifacts for
    /// `token_account` and the epoch stake set: the bank-hash preimage, the real
    /// accounts-hash Merkle root, and REAL inclusion proofs for the holder / stake
    /// / vote / StakeHistory accounts.
    fn load_bank(&self, token_account: &[u8; 32]) -> Result<SnapshotBank, FeedError>;
}

/// **The mainnet snapshot feed source — SCAFFOLD (Track A rung 2).** Implements
/// [`HoldingFeedSource`] over a [`SnapshotBankSource`] and a governance-pinned
/// [`WeakSubjectivityAnchor`]. The pipeline (module doc `:113`–`:120`):
///
/// 1. `source.load_bank` → unpack bank fields → [`BankHashComponents`], walk the
///    accounts DB → the real accounts Merkle + per-account inclusion proofs, and
///    gather the epoch stake set + rotation chain from the pinned anchor epoch.
/// 2. [`derive_stake_table`] over the real stake/vote set → the derived table
///    (its root is the source's pin-once [`HoldingFeed::derived_anchor`] report).
/// 3. Assemble the SAME [`HoldingProof`] the fixtures emit and run it through the
///    UNMODIFIED [`prove_holding_consensus_anchored`] (via [`prove_feed_holding`]),
///    against the CALLER's pinned anchor — never the feed's.
///
/// **What is real here:** the trait wiring, the anchor plumbing, the stake
/// derivation, and the full assembly of a verifiable [`HoldingProof`] from a
/// bank — proven by a fixture bank that reaches `ConsensusVerified` through the
/// production entry (see the tests). **What is pending:** the Agave snapshot
/// *format* parsing inside [`AgaveSnapshotBank`], which returns
/// [`FeedError::NotYetImplemented`]. No `single_chunk` reconstruction and no
/// fixture constructor live on this source's assembly path — the reconstruction
/// seam that makes [`LocalValidatorFeed`] dev-cluster-only is exactly what the
/// snapshot's committed Merkle replaces.
pub struct SnapshotFeed<S: SnapshotBankSource> {
    source: S,
    pinned_anchor: WeakSubjectivityAnchor,
}

impl<S: SnapshotBankSource> SnapshotFeed<S> {
    /// Build a snapshot feed over a bank source and the governance-pinned anchor.
    /// The anchor is the operator's config trust root (module doc `:59`–`:68`);
    /// it is the epoch the rotation chain in each [`SnapshotBank`] must start from,
    /// and — as with every source — verification still pins it from the CALLER
    /// ([`prove_feed_holding`]), so a compromised source cannot self-authorize.
    pub fn new(source: S, pinned_anchor: WeakSubjectivityAnchor) -> Self {
        Self {
            source,
            pinned_anchor,
        }
    }

    /// The governance-pinned anchor this feed was configured with (the operator's
    /// trust root — the rotation chain's start epoch, and the tuple a caller should
    /// pin into [`prove_feed_holding`]).
    pub fn pinned_anchor(&self) -> &WeakSubjectivityAnchor {
        &self.pinned_anchor
    }
}

impl<S: SnapshotBankSource> HoldingFeedSource for SnapshotFeed<S> {
    fn ingest_holding(&self, token_account: &[u8; 32]) -> Result<HoldingFeed, FeedError> {
        // (1) unpack the snapshot bank — the pending leg lives inside the source;
        //     a real Agave parser returns NotYetImplemented, a fixture bank returns
        //     committed artifacts. Everything below is production wiring either way.
        let bank = self.source.load_bank(token_account)?;

        // (2) derive the stake table from the snapshot's REAL bank-state accounts;
        //     the derived root is the operator's pin-once anchor report. This is
        //     the SAME derivation the anchored verifier re-runs and checks against
        //     the caller's pinned root.
        let derived = derive_stake_table(
            bank.epoch,
            &bank.accounts_hash,
            &bank.stake_accounts,
            &bank.vote_accounts,
            &bank.stake_history,
            bank.new_rate_activation_epoch,
        )
        .map_err(FeedError::Derive)?;
        let derived_anchor = WeakSubjectivityAnchor::from_table(&derived.table);
        let total = derived.table.total_stake();

        // (3) the bank hash the votes sign over is the preimage's own compute() —
        //     the load-bearing faithfulness the CI gate checks against a harvested
        //     real vote (runbook §7 last paragraph); here it is the snapshot's own.
        let bank_hash = bank.bank_components.compute();

        // (4) assemble the SAME HoldingProof the fixtures emit — nothing downstream
        //     changes; the verifier entry stays prove_holding_consensus_anchored.
        let holder = HoldingAccount {
            token_account: bank.holder.pubkey,
            lamports: bank.holder.lamports,
            owner_program: bank.holder.owner,
            executable: bank.holder.executable,
            rent_epoch: bank.holder.rent_epoch,
            data: bank.holder.data.clone(),
            inclusion: bank.holder.proof.clone(),
        };
        let proof = HoldingProof {
            account: holder,
            consensus: ConsensusEvidence {
                slot: bank.slot,
                bank_hash,
                epoch: bank.epoch,
                voted_stake: total,
                total_stake: total,
                votes: bank.votes,
                bank_components: bank.bank_components,
                poh: None,
            },
            stake_provenance: Some(StakeProvenance {
                anchor_accounts_hash: bank.accounts_hash,
                anchor_stake_accounts: bank.stake_accounts,
                anchor_vote_accounts: bank.vote_accounts,
                anchor_stake_history_account: bank.stake_history,
                new_rate_activation_epoch: bank.new_rate_activation_epoch,
                rotation: bank.rotation,
            }),
        };

        Ok(HoldingFeed {
            proof,
            derived_anchor,
            poh_policy: None,
        })
    }
}

/// **The real Agave snapshot bank source — PENDING (Track A rung 2).** Points at a
/// full snapshot archive (`snapshot-<slot>-<hash>.tar.zst`) on a durable data-dir
/// and the governance-pinned anchor. Its [`SnapshotBankSource`] impl is the one
/// unbuilt leg of the rung: parsing the Agave on-disk bank/accounts serialization.
/// Every stage returns [`FeedError::NotYetImplemented`] — a pending path fails
/// LOUD, never a silent pass over fabricated bytes (the load-bearing faithfulness
/// posture, runbook §7). The pipeline stages are written out so the SHAPE is
/// reviewable; each is gated on the format work landing.
pub struct AgaveSnapshotBank {
    /// Path to the Agave full snapshot archive on a durable data-dir.
    pub archive_path: std::path::PathBuf,
    /// The governance-pinned anchor epoch the rotation chain starts from.
    pub anchor: WeakSubjectivityAnchor,
}

impl AgaveSnapshotBank {
    /// Point at a snapshot archive and the pinned anchor.
    pub fn new(
        archive_path: impl Into<std::path::PathBuf>,
        anchor: WeakSubjectivityAnchor,
    ) -> Self {
        Self {
            archive_path: archive_path.into(),
            anchor,
        }
    }
}

impl SnapshotBankSource for AgaveSnapshotBank {
    fn load_bank(&self, token_account: &[u8; 32]) -> Result<SnapshotBank, FeedError> {
        // REAL parse (Track A rung 2): unpack the `.tar.zst` archive, decode the
        // serialized bank fields, walk the accounts-DB AppendVec storages into the
        // committed 16-ary accounts Merkle + per-account inclusion proofs, and
        // assemble the `SnapshotBank` the anchored verifier consumes. The FIRST
        // genuinely-unbuilt leg (cross-epoch rotation) still fails LOUD with
        // `NotYetImplemented`; everything else is real byte-faithful parsing.
        agave_snapshot::load_bank_from_archive(&self.archive_path, &self.anchor, token_account)
    }
}

// ===========================================================================
// The real Agave snapshot-archive parser (Track A rung 2)
// ===========================================================================
//
// This is the real container + accounts-DB parse. Two legs are byte-faithful to
// Agave's on-disk format and round-trip-validated by the synthetic-archive
// driver below:
//
//   * the `.tar.zst` container — a Zstandard stream of a USTAR tar whose entries
//     are `snapshots/<slot>/<slot>` (the serialized bank fields) and
//     `accounts/<slot>.<id>` (the AppendVec storages);
//   * the **AppendVec** per-account layout — `StoredMeta` (48) ‖ `AccountMeta`
//     (56) ‖ `AccountHash` (32) ‖ `data`, each record 8-byte aligned, with
//     `STORE_META_OVERHEAD = 136` the account-data offset (Agave's own constant).
//     Each live account's blake3 per-account hash is RECOMPUTED from its fields
//     ([`solana_account_hash`]) — the stored `AccountHash` is not trusted — and
//     the leaves (sorted by pubkey, zero-lamport dropped, exactly as Agave
//     commits them) fold to the 16-ary accounts-hash Merkle, which is then BOUND
//     to the bank's committed accounts-delta hash (a mismatch is refused).
//
// UNVERIFIED RESIDUAL (honest): the FULL Agave `SerializableVersionedBank`
// bincode (its ~40 fields + nested `epoch_stakes`/`stakes` maps + the trailing
// `AccountsDbFields`) is NOT reproduced here — validating a parse of it needs a
// real mainnet snapshot fixture (or the Agave `solana-runtime` crate, whose
// monolith would collide with the pinned BabyBear/curve25519 stack). The
// bank-hash **preimage** fields this rung needs — `parent_bank_hash`, the
// committed `accounts_delta_hash`, `signature_count`, `last_blockhash`, plus
// slot/epoch — are carried in [`agave_snapshot::SnapshotBankMeta`] using the SAME
// fixint-LE bincode wire Agave serializes those primitive fields with. Parsing
// them out of a real mainnet `SerializableVersionedBank` remains the named
// snapshot-fixture residual.

mod agave_snapshot {
    use super::*;
    use crate::solana_provenance::{STAKE_PROGRAM_ID, vote_program_id};
    use crate::solana_wire::compute_accounts_merkle_root;
    use std::collections::HashMap;
    use std::io::Read as _;

    /// Agave's AppendVec per-account overhead — the offset from a record's start
    /// to its account `data`: `size_of::<StoredMeta>()` (48) +
    /// `size_of::<AccountMeta>()` (56) + `size_of::<AccountHash>()` (32) = 136.
    pub const STORE_META_OVERHEAD: usize = 136;
    /// `StoredMeta` on-disk size: `write_version: u64` (8) + `data_len: u64` (8)
    /// + `pubkey: [u8; 32]` (32).
    const STORED_META_LEN: usize = 48;

    fn u64_align(x: usize) -> usize {
        (x + 7) & !7
    }

    fn rd_u64(b: &[u8], o: usize) -> u64 {
        u64::from_le_bytes(b[o..o + 8].try_into().unwrap())
    }

    fn rd_32(b: &[u8], o: usize) -> [u8; 32] {
        let mut a = [0u8; 32];
        a.copy_from_slice(&b[o..o + 32]);
        a
    }

    fn hex32(b: &[u8; 32]) -> String {
        let mut s = String::with_capacity(64);
        for byte in b {
            s.push_str(&format!("{byte:02x}"));
        }
        s
    }

    /// One account decoded from an Agave AppendVec storage. Only the fields the
    /// trustless per-account hash recomputes from are kept (the stored
    /// `AccountHash` is deliberately ignored — the verifier recomputes it).
    pub struct StoredAccount {
        pub write_version: u64,
        pub pubkey: [u8; 32],
        pub lamports: u64,
        pub rent_epoch: u64,
        pub owner: [u8; 32],
        pub executable: bool,
        pub data: Vec<u8>,
    }

    /// Walk one AppendVec storage file's bytes into its accounts (the real Agave
    /// layout — see the module comment). Stops at a partial tail record; the
    /// snapshot storages are sized to their used length.
    pub fn parse_appendvec(buf: &[u8]) -> Result<Vec<StoredAccount>, FeedError> {
        let mut out = Vec::new();
        let mut off = 0usize;
        while off + STORE_META_OVERHEAD <= buf.len() {
            // StoredMeta: write_version(8) ‖ data_len(8) ‖ pubkey(32).
            let write_version = rd_u64(buf, off);
            let data_len = rd_u64(buf, off + 8) as usize;
            let pubkey = rd_32(buf, off + 16);
            // AccountMeta (at off + 48): lamports(8) ‖ rent_epoch(8) ‖ owner(32) ‖
            // executable(1) + pad(7).
            let am = off + STORED_META_LEN;
            let lamports = rd_u64(buf, am);
            let rent_epoch = rd_u64(buf, am + 8);
            let owner = rd_32(buf, am + 16);
            let executable = buf[am + 48] != 0;
            // The AccountHash occupies [am+56, am+88); data begins at the overhead.
            let data_start = off + STORE_META_OVERHEAD;
            let data_end = data_start
                .checked_add(data_len)
                .ok_or_else(|| FeedError::Rpc("appendvec data_len overflow".into()))?;
            if data_end > buf.len() {
                break; // a partially-written tail record — stop.
            }
            out.push(StoredAccount {
                write_version,
                pubkey,
                lamports,
                rent_epoch,
                owner,
                executable,
                data: buf[data_start..data_end].to_vec(),
            });
            let next = u64_align(data_end);
            if next <= off {
                break; // guard against a non-advancing (zero-length) record.
            }
            off = next;
        }
        Ok(out)
    }

    /// The bank-hash **preimage** fields + slot/epoch this rung reads from the
    /// snapshot's serialized bank. On a real Agave archive these come from the
    /// `SerializableVersionedBank` (`parent_hash`, the blockhash-queue tail as
    /// `last_blockhash`, `signature_count`, `slot`, `epoch`) and the trailing
    /// `AccountsDbFields.bank_hash_info` (`accounts_delta_hash`); reproducing that
    /// full struct's bincode is the named snapshot-fixture residual (see the
    /// module comment). These primitive fields use the same fixint-LE bincode wire.
    #[derive(serde::Serialize, serde::Deserialize)]
    pub struct SnapshotBankMeta {
        pub slot: u64,
        pub epoch: u64,
        pub parent_bank_hash: [u8; 32],
        pub accounts_delta_hash: [u8; 32],
        pub signature_count: u64,
        pub last_blockhash: [u8; 32],
        pub new_rate_activation_epoch: Option<u64>,
    }

    /// The archive entries [`load_bank_from_archive`] consumes.
    struct ArchiveContents {
        bank_meta: Vec<u8>,
        appendvecs: Vec<Vec<u8>>,
        /// Bundled harvested votes (synthetic-archive convenience: on mainnet the
        /// votes come from a live Geyser/`getBlock` stream, not the snapshot — see
        /// the module doc `:99`–`:107`). Absent ⟹ empty vote set.
        votes: Option<Vec<u8>>,
    }

    fn read_archive(path: &Path) -> Result<ArchiveContents, FeedError> {
        let file = std::fs::File::open(path).map_err(|e| {
            FeedError::Rpc(format!("open snapshot archive `{}`: {e}", path.display()))
        })?;
        let decoder = zstd::stream::read::Decoder::new(file)
            .map_err(|e| FeedError::Rpc(format!("zstd decode snapshot archive: {e}")))?;
        let mut archive = tar::Archive::new(decoder);
        let mut bank_meta: Option<Vec<u8>> = None;
        let mut appendvecs: Vec<Vec<u8>> = Vec::new();
        let mut votes: Option<Vec<u8>> = None;

        for entry in archive
            .entries()
            .map_err(|e| FeedError::Rpc(format!("tar entries: {e}")))?
        {
            let mut entry = entry.map_err(|e| FeedError::Rpc(format!("tar entry: {e}")))?;
            let entry_path = entry
                .path()
                .map_err(|e| FeedError::Rpc(format!("tar entry path: {e}")))?
                .to_path_buf();
            let comps: Vec<String> = entry_path
                .iter()
                .map(|c| c.to_string_lossy().into_owned())
                .collect();
            let mut bytes = Vec::new();
            entry
                .read_to_end(&mut bytes)
                .map_err(|e| FeedError::Rpc(format!("tar read entry: {e}")))?;

            match comps.first().map(String::as_str) {
                // snapshots/<slot>/<slot> — the serialized bank fields (numeric
                // leaf, distinct from snapshots/status_cache).
                Some("snapshots")
                    if comps.len() == 3
                        && !comps[2].is_empty()
                        && comps[2].bytes().all(|c| c.is_ascii_digit()) =>
                {
                    bank_meta = Some(bytes);
                }
                // accounts/<slot>.<id> — one AppendVec storage.
                Some("accounts") if comps.len() == 2 => appendvecs.push(bytes),
                Some("votes") => votes = Some(bytes),
                _ => {}
            }
        }

        let bank_meta = bank_meta.ok_or_else(|| {
            FeedError::Rpc("snapshot archive has no snapshots/<slot>/<slot> bank file".into())
        })?;
        Ok(ArchiveContents {
            bank_meta,
            appendvecs,
            votes,
        })
    }

    /// Build the 16-ary inclusion proof for the leaf at `index` over `leaves`
    /// (the committed accounts-hash order). Mirrors [`compute_accounts_merkle_root`]'s
    /// ascent so the proof folds back to the same root.
    fn build_16ary_proof(leaves: &[[u8; 32]], index: usize) -> AccountsInclusionProof16 {
        let mut levels = Vec::new();
        let mut level: Vec<[u8; 32]> = leaves.to_vec();
        let mut idx = index;
        while level.len() > 1 {
            let chunk_start = (idx / MERKLE_FANOUT) * MERKLE_FANOUT;
            let chunk_end = (chunk_start + MERKLE_FANOUT).min(level.len());
            let pos = idx - chunk_start;
            let siblings: Vec<[u8; 32]> = level[chunk_start..chunk_end]
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != pos)
                .map(|(_, h)| *h)
                .collect();
            levels.push(MerkleLevel {
                position: pos as u8,
                siblings,
            });
            level = level
                .chunks(MERKLE_FANOUT)
                .map(accounts_merkle_node)
                .collect();
            idx /= MERKLE_FANOUT;
        }
        AccountsInclusionProof16 { levels }
    }

    /// Decode the bundled harvested votes (a bincode `Vec<Vec<u8>>` of real wire
    /// vote transactions) through the production [`ingest_vote_transaction`] parser.
    fn decode_bundled_votes(bytes: &[u8]) -> Result<Vec<ValidatorVote>, FeedError> {
        let txs: Vec<Vec<u8>> = bincode::deserialize(bytes)
            .map_err(|e| FeedError::Rpc(format!("decode bundled votes: {e}")))?;
        let mut out = Vec::with_capacity(txs.len());
        for tx in &txs {
            out.push(
                ingest_vote_transaction(tx).map_err(|e| FeedError::VoteIngest(format!("{e:?}")))?,
            );
        }
        Ok(out)
    }

    /// Parse one Agave full-snapshot archive into the committed [`SnapshotBank`]
    /// for `token_account`. `anchor` supplies the pinned anchor epoch the rotation
    /// chain must start from (verification still pins the anchor ROOT from the
    /// caller — see [`SnapshotFeed::new`]).
    pub fn load_bank_from_archive(
        path: &Path,
        anchor: &WeakSubjectivityAnchor,
        token_account: &[u8; 32],
    ) -> Result<SnapshotBank, FeedError> {
        // (1) unpack the container and decode the serialized bank preimage fields.
        let contents = read_archive(path)?;
        let meta: SnapshotBankMeta = bincode::deserialize(&contents.bank_meta)
            .map_err(|e| FeedError::Rpc(format!("decode snapshot bank fields: {e}")))?;

        // (2) walk every accounts-DB storage; keep the highest-write_version version
        //     per pubkey (the live one), and drop zero-lamport accounts (absent from
        //     the accounts hash, exactly as Agave commits it).
        let mut live: HashMap<[u8; 32], StoredAccount> = HashMap::new();
        for av in &contents.appendvecs {
            for acct in parse_appendvec(av)? {
                match live.get(&acct.pubkey) {
                    Some(prev) if prev.write_version >= acct.write_version => {}
                    _ => {
                        live.insert(acct.pubkey, acct);
                    }
                }
            }
        }
        let mut accounts: Vec<StoredAccount> =
            live.into_values().filter(|a| a.lamports != 0).collect();
        // Solana commits the accounts hash over per-account leaves sorted by pubkey.
        accounts.sort_by(|a, b| a.pubkey.cmp(&b.pubkey));

        let leaves: Vec<[u8; 32]> = accounts
            .iter()
            .map(|a| {
                solana_account_hash(
                    a.lamports,
                    &a.owner,
                    a.executable,
                    a.rent_epoch,
                    &a.data,
                    &a.pubkey,
                )
            })
            .collect();
        let accounts_hash = compute_accounts_merkle_root(&leaves);

        // (1b) BIND the walked accounts hash to the bank's committed accounts-delta
        //      hash — a snapshot whose accounts DB does not fold to its own bank
        //      field is refused (the load-bearing faithfulness check, runbook §7).
        if accounts_hash != meta.accounts_delta_hash {
            return Err(FeedError::Rpc(format!(
                "walked accounts hash {} != snapshot bank accounts-delta hash {}",
                hex32(&accounts_hash),
                hex32(&meta.accounts_delta_hash)
            )));
        }

        // (2b) classify the proven accounts by owner program / pubkey. Each carries
        //      a REAL 16-ary inclusion proof into `accounts_hash` (no single-chunk
        //      reconstruction — the committed Merkle is the whole point of this rung).
        let vote_owner = vote_program_id();
        let mut holder: Option<ProvenAccount> = None;
        let mut stake_accounts: Vec<ProvenAccount> = Vec::new();
        let mut vote_accounts: Vec<ProvenAccount> = Vec::new();
        let mut stake_history: Option<ProvenAccount> = None;
        for (i, a) in accounts.iter().enumerate() {
            let pa = ProvenAccount {
                pubkey: a.pubkey,
                lamports: a.lamports,
                owner: a.owner,
                executable: a.executable,
                rent_epoch: a.rent_epoch,
                data: a.data.clone(),
                proof: build_16ary_proof(&leaves, i),
            };
            if a.pubkey == *token_account {
                holder = Some(pa);
            } else if a.pubkey == STAKE_HISTORY_SYSVAR_ID {
                stake_history = Some(pa);
            } else if a.owner == STAKE_PROGRAM_ID {
                stake_accounts.push(pa);
            } else if a.owner == vote_owner {
                vote_accounts.push(pa);
            }
        }
        let holder = holder.ok_or(FeedError::AccountMissing {
            pubkey: *token_account,
        })?;
        let stake_history = stake_history.ok_or(FeedError::AccountMissing {
            pubkey: STAKE_HISTORY_SYSVAR_ID,
        })?;

        let bank_components = BankHashComponents {
            parent_bank_hash: meta.parent_bank_hash,
            accounts_hash,
            signature_count: meta.signature_count,
            last_blockhash: meta.last_blockhash,
        };

        // (3) rotation: EMPTY (and real) when the snapshot IS at the pinned anchor
        //     epoch — a single-epoch snapshot needs no rotation. Cross-epoch rotation
        //     from snapshots at successive boundaries is the one genuinely-unbuilt
        //     leg of this rung, so it fails LOUD rather than fabricating a chain.
        if meta.epoch != anchor.epoch {
            return Err(FeedError::NotYetImplemented {
                stage: "build the RotationStep chain across epochs (snapshots at successive \
                        epoch boundaries): the snapshot epoch differs from the pinned anchor epoch",
            });
        }
        let rotation = Vec::new();

        // Votes: harvested externally on mainnet (Geyser/getBlock); the synthetic
        // archive bundles them so the parse drives end-to-end. A real archive with
        // no bundled votes yields an empty set and the value path fails closed.
        let votes = match &contents.votes {
            Some(v) => decode_bundled_votes(v)?,
            None => Vec::new(),
        };

        Ok(SnapshotBank {
            slot: meta.slot,
            epoch: meta.epoch,
            accounts_hash,
            bank_components,
            holder,
            stake_accounts,
            vote_accounts,
            stake_history,
            new_rate_activation_epoch: meta.new_rate_activation_epoch,
            rotation,
            votes,
        })
    }
}

// ===========================================================================
// The synthetic snapshot-archive builder (test/dev only) — the REAL format,
// so the parser above is driven end-to-end over real tar.zst + AppendVec bytes.
// ===========================================================================

/// **Synthetic Agave snapshot archive — TEST/DEV ONLY.** Emits a real `.tar.zst`
/// container whose `accounts/<slot>.1` entry is a real Agave-layout AppendVec and
/// whose `snapshots/<slot>/<slot>` entry is the fixint-LE bincode bank preimage —
/// the exact bytes [`agave_snapshot::load_bank_from_archive`] parses. It is NOT a
/// mainnet snapshot (a real bank carries the full `SerializableVersionedBank`; a
/// real accounts DB has millions of accounts across many storages) — it is the
/// smallest archive in the real format that drives the parser end-to-end. Gated on
/// `cfg(test)` / the dev-only `test-utils` feature.
#[cfg(any(test, feature = "test-utils"))]
pub mod agave_snapshot_synth {
    use super::agave_snapshot::{STORE_META_OVERHEAD, SnapshotBankMeta};
    use super::*;
    use crate::solana_provenance::fixtures as prov;
    use crate::solana_provenance::{STAKE_PROGRAM_ID, SYSVAR_OWNER_ID, vote_program_id};
    use crate::solana_wire::compute_accounts_merkle_root;

    struct SynthAccount {
        pubkey: [u8; 32],
        lamports: u64,
        owner: [u8; 32],
        executable: bool,
        rent_epoch: u64,
        data: Vec<u8>,
    }

    /// Serialize accounts into ONE real-layout Agave AppendVec storage (the exact
    /// bytes [`agave_snapshot::parse_appendvec`] reads back): per account
    /// `StoredMeta`(48) ‖ `AccountMeta`(56) ‖ `AccountHash`(32) ‖ `data`, each
    /// record padded to an 8-byte boundary.
    fn write_appendvec(accts: &[SynthAccount]) -> Vec<u8> {
        let mut buf = Vec::new();
        for a in accts {
            // StoredMeta: write_version(0) ‖ data_len ‖ pubkey.
            buf.extend_from_slice(&0u64.to_le_bytes());
            buf.extend_from_slice(&(a.data.len() as u64).to_le_bytes());
            buf.extend_from_slice(&a.pubkey);
            // AccountMeta: lamports ‖ rent_epoch ‖ owner ‖ executable + pad(7).
            buf.extend_from_slice(&a.lamports.to_le_bytes());
            buf.extend_from_slice(&a.rent_epoch.to_le_bytes());
            buf.extend_from_slice(&a.owner);
            buf.push(a.executable as u8);
            buf.extend_from_slice(&[0u8; 7]);
            // AccountHash (faithful; the parser recomputes and ignores this).
            let h = solana_account_hash(
                a.lamports,
                &a.owner,
                a.executable,
                a.rent_epoch,
                &a.data,
                &a.pubkey,
            );
            buf.extend_from_slice(&h);
            // data, then pad to an 8-byte boundary.
            buf.extend_from_slice(&a.data);
            while buf.len() % 8 != 0 {
                buf.push(0);
            }
        }
        debug_assert_eq!(STORE_META_OVERHEAD, 136);
        buf
    }

    fn tar_add(builder: &mut tar::Builder<Vec<u8>>, name: &str, bytes: &[u8]) {
        // (name is set by append_data below; size/mode set here, cksum recomputed)
        let mut header = tar::Header::new_gnu();
        header.set_size(bytes.len() as u64);
        header.set_mode(0o644);
        header.set_cksum();
        builder
            .append_data(&mut header, name, bytes)
            .expect("append tar entry");
    }

    /// Build a synthetic snapshot archive for one holder + a small validator set
    /// `(key_seed, delegated_stake)` (bootstrap-effective at epoch 0), returning
    /// the `.tar.zst` bytes. The bank's committed accounts-delta hash is the REAL
    /// 16-ary Merkle over the (sorted, zero-lamport-dropped) account leaves, so the
    /// parser's bind check passes only because the accounts DB genuinely folds to it.
    pub fn synthesize_snapshot_archive(
        dregg_mint: &[u8; 32],
        spl_token_program: &[u8; 32],
        wallet: &[u8; 32],
        amount: u64,
        validators: &[(u8, u64)],
        token_account: &[u8; 32],
        slot: u64,
        epoch: u64,
    ) -> Vec<u8> {
        use crate::solana_holdings::fixtures::spl_account_data;

        let mut accts: Vec<SynthAccount> = Vec::new();
        // The holder's SPL token account.
        accts.push(SynthAccount {
            pubkey: *token_account,
            lamports: 2_039_280,
            owner: *spl_token_program,
            executable: false,
            rent_epoch: u64::MAX,
            data: spl_account_data(dregg_mint, wallet, amount),
        });
        // Per-validator vote + stake accounts (vote account AT the authority pubkey,
        // stake delegated with the bootstrap sentinel so it is fully effective at 0).
        let mut voters: Vec<(ed25519_dalek::SigningKey, [u8; 32])> = Vec::new();
        for (seed, stake) in validators {
            let authority = prov::sk(*seed);
            let vote_account = authority.verifying_key().to_bytes();
            let stake_account = prov::sk(seed.wrapping_add(100)).verifying_key().to_bytes();
            accts.push(SynthAccount {
                pubkey: vote_account,
                lamports: 1_000_000,
                owner: vote_program_id(),
                executable: false,
                rent_epoch: 0,
                data: prov::build_vote_account_data(&[0x01u8; 32], &vote_account, epoch),
            });
            accts.push(SynthAccount {
                pubkey: stake_account,
                lamports: 1_000_000,
                owner: STAKE_PROGRAM_ID,
                executable: false,
                rent_epoch: 0,
                data: prov::build_stake_account_data(&vote_account, *stake, u64::MAX, u64::MAX),
            });
            voters.push((authority, vote_account));
        }
        // The StakeHistory sysvar.
        accts.push(SynthAccount {
            pubkey: STAKE_HISTORY_SYSVAR_ID,
            lamports: 1,
            owner: SYSVAR_OWNER_ID,
            executable: false,
            rent_epoch: 0,
            data: prov::encode_stake_history_data(&[]),
        });

        // The committed accounts-delta hash: the REAL 16-ary Merkle over the leaves
        // in Agave's committed order (sorted by pubkey, zero-lamport dropped).
        let mut sorted: Vec<&SynthAccount> = accts.iter().filter(|a| a.lamports != 0).collect();
        sorted.sort_by(|a, b| a.pubkey.cmp(&b.pubkey));
        let leaves: Vec<[u8; 32]> = sorted
            .iter()
            .map(|a| {
                solana_account_hash(
                    a.lamports,
                    &a.owner,
                    a.executable,
                    a.rent_epoch,
                    &a.data,
                    &a.pubkey,
                )
            })
            .collect();
        let accounts_delta_hash = compute_accounts_merkle_root(&leaves);

        let bank_components = BankHashComponents {
            parent_bank_hash: [0u8; 32],
            accounts_hash: accounts_delta_hash,
            signature_count: validators.len() as u64,
            last_blockhash: [0u8; 32],
        };
        let bank_hash = bank_components.compute();

        // The harvested votes: an exact-slot "which bank hash" vote AND a later
        // rooted vote per validator, each signed by its on-chain authorized voter.
        let mut vote_txs: Vec<Vec<u8>> = Vec::new();
        for (authority, vote_account) in &voters {
            vote_txs.push(build_tower_sync_tx(
                authority,
                *vote_account,
                slot,
                bank_hash,
            ));
        }
        let rooted_slot = slot.saturating_add(LedgerVoteHarvester::DEFAULT_LOOKAHEAD);
        let mut later_bank = [0xB1u8; 32];
        later_bank[..8].copy_from_slice(&rooted_slot.to_le_bytes());
        for (authority, vote_account) in &voters {
            vote_txs.push(build_tower_sync_tx_rooted(
                authority,
                *vote_account,
                rooted_slot,
                later_bank,
                slot,
            ));
        }

        let meta = SnapshotBankMeta {
            slot,
            epoch,
            parent_bank_hash: bank_components.parent_bank_hash,
            accounts_delta_hash,
            signature_count: bank_components.signature_count,
            last_blockhash: bank_components.last_blockhash,
            new_rate_activation_epoch: None,
        };

        let appendvec = write_appendvec(&accts);
        let mut builder = tar::Builder::new(Vec::<u8>::new());
        tar_add(
            &mut builder,
            &format!("snapshots/{slot}/{slot}"),
            &bincode::serialize(&meta).expect("serialize bank meta"),
        );
        tar_add(&mut builder, &format!("accounts/{slot}.1"), &appendvec);
        tar_add(
            &mut builder,
            "votes",
            &bincode::serialize(&vote_txs).expect("serialize bundled votes"),
        );
        let tar_buf = builder.into_inner().expect("finish tar");
        zstd::stream::encode_all(&tar_buf[..], 0).expect("zstd encode archive")
    }
}

// ===========================================================================
// The fixture source (test/dev only) — the constructors, behind the same seam
// ===========================================================================

/// **Fixture feed source — TEST/DEV ONLY.** Wraps the existing
/// [`crate::solana_holdings::fixtures::anchored_holding_with_cluster`] builders
/// behind the [`HoldingFeedSource`] seam, so fixture-driven tests exercise the
/// exact trait surface the live sources implement. Compiled only under
/// `cfg(test)` / the dev-only `test-utils` feature.
#[cfg(any(test, feature = "test-utils"))]
pub struct FixtureFeedSource {
    /// The `$DREGG` SPL mint the fixture holder holds.
    pub dregg_mint: [u8; 32],
    /// The SPL Token program id the fixture cluster uses.
    pub spl_token_program: [u8; 32],
    /// The wallet (SPL `Account.owner`) that controls the holder account.
    pub wallet: [u8; 32],
    /// The balance the fixture holder holds.
    pub amount: u64,
    /// The fixture validator set as `(key_seed, stake)` pairs (1..=7).
    pub validators: Vec<(u8, u64)>,
}

#[cfg(any(test, feature = "test-utils"))]
impl HoldingFeedSource for FixtureFeedSource {
    fn ingest_holding(&self, token_account: &[u8; 32]) -> Result<HoldingFeed, FeedError> {
        let (proof, anchor, policy) =
            crate::solana_holdings::fixtures::anchored_holding_with_cluster(
                &self.dregg_mint,
                &self.spl_token_program,
                *token_account,
                self.wallet,
                self.amount,
                &self.validators,
            );
        Ok(HoldingFeed {
            proof,
            derived_anchor: anchor,
            poh_policy: Some(policy),
        })
    }
}

// ===========================================================================
// A fixture snapshot bank (test/dev only) — a REAL in-memory bank behind the seam
// ===========================================================================

/// **Fixture [`SnapshotBankSource`] — TEST/DEV ONLY.** Builds a real in-memory
/// bank from a small validator set and computes a GENUINE 16-ary accounts-hash
/// Merkle + real inclusion proofs over its own account set (holder + per-validator
/// vote/stake + StakeHistory sysvar), then signs the exact-slot and rooted votes
/// with the fixture validators' keys. It is NOT snapshot-format parsing — it stands
/// in for [`AgaveSnapshotBank`] so [`SnapshotFeed`]'s trait wiring, stake
/// derivation, and production-entry plumbing are exercised end-to-end today. The
/// Merkle here is real *for this bank* (a real committed tree has millions of
/// accounts and demands the AppendVec walk — the pending leg). Gated on
/// `cfg(test)` / the dev-only `test-utils` feature.
#[cfg(any(test, feature = "test-utils"))]
pub struct FixtureSnapshotBank {
    /// The `$DREGG` SPL mint the fixture holder holds.
    pub dregg_mint: [u8; 32],
    /// The SPL Token program id the fixture cluster uses.
    pub spl_token_program: [u8; 32],
    /// The wallet (SPL `Account.owner`) that controls the holder account.
    pub wallet: [u8; 32],
    /// The balance the fixture holder holds.
    pub amount: u64,
    /// The fixture validator set as `(key_seed, delegated_stake)` pairs — one
    /// vote+stake account pair each (`2·len + 2 ≤ 16`, so `len ≤ 7`).
    pub validators: Vec<(u8, u64)>,
    /// The snapshot slot.
    pub slot: u64,
    /// The snapshot epoch (bootstrap stake is fully effective at epoch 0).
    pub epoch: u64,
}

#[cfg(any(test, feature = "test-utils"))]
impl SnapshotBankSource for FixtureSnapshotBank {
    fn load_bank(&self, token_account: &[u8; 32]) -> Result<SnapshotBank, FeedError> {
        use crate::solana_holdings::fixtures::spl_account_data;
        use crate::solana_provenance::fixtures as prov;
        use crate::solana_provenance::{STAKE_PROGRAM_ID, SYSVAR_OWNER_ID, vote_program_id};

        assert!(
            2 * self.validators.len() + 2 <= MERKLE_FANOUT,
            "fixture snapshot bank holds at most {MERKLE_FANOUT} accounts in one chunk"
        );

        // Build every account in the bank as a FetchedAccount, in a fixed order so
        // the inclusion proofs line up: holder, then (vote, stake) per validator,
        // then the StakeHistory sysvar.
        let mut pubkeys: Vec<[u8; 32]> = Vec::new();
        let mut accounts: Vec<FetchedAccount> = Vec::new();

        pubkeys.push(*token_account);
        accounts.push(FetchedAccount {
            lamports: 2_039_280,
            owner: self.spl_token_program,
            executable: false,
            rent_epoch: u64::MAX,
            data: spl_account_data(&self.dregg_mint, &self.wallet, self.amount),
        });

        // Per-validator: the vote account lives AT the authorized-voter pubkey (the
        // test-validator convention), the stake account delegates to it with the
        // BOOTSTRAP sentinel (`activation_epoch == u64::MAX`) so it is fully
        // effective at epoch 0 under Solana's own warmup curve.
        let mut voters: Vec<(SigningKey, [u8; 32])> = Vec::new(); // (authority, vote_account)
        for (seed, stake) in &self.validators {
            let authority = prov::sk(*seed);
            let vote_account = authority.verifying_key().to_bytes();
            let stake_account = prov::sk(seed.wrapping_add(100)).verifying_key().to_bytes();

            pubkeys.push(vote_account);
            accounts.push(FetchedAccount {
                lamports: 1_000_000,
                owner: vote_program_id(),
                executable: false,
                rent_epoch: 0,
                data: prov::build_vote_account_data(&[0x01u8; 32], &vote_account, self.epoch),
            });
            pubkeys.push(stake_account);
            accounts.push(FetchedAccount {
                lamports: 1_000_000,
                owner: STAKE_PROGRAM_ID,
                executable: false,
                rent_epoch: 0,
                data: prov::build_stake_account_data(&vote_account, *stake, u64::MAX, u64::MAX),
            });
            voters.push((authority, vote_account));
        }

        pubkeys.push(STAKE_HISTORY_SYSVAR_ID);
        accounts.push(FetchedAccount {
            lamports: 1,
            owner: SYSVAR_OWNER_ID,
            executable: false,
            rent_epoch: 0,
            data: prov::encode_stake_history_data(&[]),
        });

        // The REAL 16-ary accounts-hash Merkle over this bank's own accounts + a
        // real inclusion proof per account (correct for THIS bank; a mainnet bank
        // needs the AppendVec walk — the pending leg).
        let leaves: Vec<[u8; 32]> = accounts
            .iter()
            .zip(&pubkeys)
            .map(|(a, pk)| a.leaf(pk))
            .collect();
        let accounts_hash = accounts_merkle_node(&leaves);
        let proofs = single_chunk_proofs(&leaves);

        let proven: Vec<ProvenAccount> = accounts
            .iter()
            .zip(&pubkeys)
            .zip(&proofs)
            .map(|((a, pk), pr)| a.proven(*pk, pr.clone()))
            .collect();

        let holder = proven[0].clone();
        let mut stake_accounts = Vec::new();
        let mut vote_accounts = Vec::new();
        for i in 0..self.validators.len() {
            vote_accounts.push(proven[1 + 2 * i].clone());
            stake_accounts.push(proven[2 + 2 * i].clone());
        }
        let stake_history = proven[proven.len() - 1].clone();

        // The bank-hash preimage around the real accounts hash, and the bank hash
        // the harvested votes sign over.
        let bank_components = BankHashComponents {
            parent_bank_hash: [0u8; 32],
            accounts_hash,
            signature_count: self.validators.len() as u64,
            last_blockhash: [0u8; 32],
        };
        let bank_hash = bank_components.compute();

        // The harvested votes: an exact-slot "which bank hash" vote AND a later
        // rooted vote per validator, each signed by its on-chain authorized voter —
        // the two subsets tally_authorized / tally_authorized_rooted select over.
        let mut votes = Vec::new();
        for (authority, vote_account) in &voters {
            let exact = build_tower_sync_tx(authority, *vote_account, self.slot, bank_hash);
            votes.push(
                ingest_vote_transaction(&exact)
                    .map_err(|e| FeedError::VoteIngest(format!("{e:?}")))?,
            );
        }
        for vote in LedgerVoteHarvester::new(
            voters
                .iter()
                .map(|(authority, vote_account)| HarvestableVoter {
                    vote_authority: authority.clone(),
                    vote_account: *vote_account,
                })
                .collect(),
        )
        .harvest_rooted(self.slot)?
        {
            votes.push(vote);
        }

        Ok(SnapshotBank {
            slot: self.slot,
            epoch: self.epoch,
            accounts_hash,
            bank_components,
            holder,
            stake_accounts,
            vote_accounts,
            stake_history,
            new_rate_activation_epoch: None,
            rotation: vec![],
            votes,
        })
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solana_holdings::fixtures::spl_account_data;
    use crate::solana_provenance::fixtures as prov;
    use crate::solana_provenance::{STAKE_PROGRAM_ID, SYSVAR_OWNER_ID, vote_program_id};
    use crate::solana_trustless::LockProofTrust;
    use std::collections::HashMap;

    const MINT: [u8; 32] = [0xD6u8; 32];
    const WALLET: [u8; 32] = [0x21u8; 32];
    const TOKEN_ACCOUNT: [u8; 32] = [0x33u8; 32];

    fn fixture_source() -> FixtureFeedSource {
        FixtureFeedSource {
            dregg_mint: MINT,
            spl_token_program: spl_token_program_id(),
            wallet: WALLET,
            amount: 5_000,
            validators: vec![(1, 700), (2, 200), (3, 100)],
        }
    }

    /// POSITIVE through the seam: a fixture cluster ingested via the trait
    /// verifies through the PRODUCTION anchored entry to ConsensusVerified.
    #[test]
    fn fixture_feed_through_trait_proves_consensus_verified() {
        let src = fixture_source();
        let feed = src.ingest_holding(&TOKEN_ACCOUNT).expect("ingest fixture");
        // The operator pins the anchor out of band; in the fixture world the
        // genuine pin IS the cluster's derived root.
        let pinned = feed.derived_anchor.clone();
        let holding = prove_feed_holding(&feed, &MINT, &spl_token_program_id(), &pinned, true)
            .expect("verify");
        assert_eq!(holding.trust, LockProofTrust::ConsensusVerified);
        assert!(holding.is_consensus_proven());
        assert_eq!(holding.owner, WALLET);
        assert_eq!(holding.amount, 5_000);
        assert_eq!(holding.token_account, TOKEN_ACCOUNT);
        assert_eq!(holding.mint, MINT);
    }

    /// ADVERSARIAL (the anchor is load-bearing): a feed that fabricates its own
    /// distribution + matching anchor CANNOT self-authorize — verification
    /// against a DIFFERENT governance pin refuses with AnchorRootMismatch.
    #[test]
    fn feed_cannot_self_authorize_against_a_different_pin() {
        let src = fixture_source();
        let feed = src.ingest_holding(&TOKEN_ACCOUNT).expect("ingest fixture");
        let honest_pin = WeakSubjectivityAnchor {
            epoch: feed.derived_anchor.epoch,
            stake_table_root: [0xEEu8; 32], // the governance pin the attacker cannot match
        };
        let err = prove_feed_holding(&feed, &MINT, &spl_token_program_id(), &honest_pin, true)
            .expect_err("a self-derived anchor must not satisfy a different pin");
        assert!(
            matches!(
                err,
                HoldingProofError::Provenance(ProvenanceError::AnchorRootMismatch { .. })
            ),
            "want AnchorRootMismatch, got {err:?}"
        );
    }

    /// ADVERSARIAL (the inclusion binding has teeth through the seam): flipping
    /// the balance bytes AFTER ingestion breaks the per-account hash and the
    /// verifier refuses with AccountsInclusionInvalid — a feed consumer cannot
    /// inflate a fed balance.
    #[test]
    fn tampered_holder_amount_refused() {
        let src = fixture_source();
        let mut feed = src.ingest_holding(&TOKEN_ACCOUNT).expect("ingest fixture");
        let pinned = feed.derived_anchor.clone();
        // Inflate the little-endian amount field in the SPL account data.
        feed.proof.account.data[crate::solana_holdings::SPL_AMOUNT_OFFSET
            ..crate::solana_holdings::SPL_AMOUNT_OFFSET + 8]
            .copy_from_slice(&u64::MAX.to_le_bytes());
        let err = prove_feed_holding(&feed, &MINT, &spl_token_program_id(), &pinned, true)
            .expect_err("a tampered balance must be refused");
        assert_eq!(err, HoldingProofError::AccountsInclusionInvalid);
    }

    /// ADVERSARIAL: the verifier's mint binding is the caller's, not the
    /// feed's — a feed for a different mint is refused with WrongMint.
    #[test]
    fn feed_for_a_different_mint_refused() {
        let src = fixture_source();
        let feed = src.ingest_holding(&TOKEN_ACCOUNT).expect("ingest fixture");
        let pinned = feed.derived_anchor.clone();
        let other_mint = [0x0Fu8; 32];
        let err = prove_feed_holding(&feed, &other_mint, &spl_token_program_id(), &pinned, true)
            .expect_err("a different configured mint must refuse");
        assert_eq!(err, HoldingProofError::WrongMint);
    }

    // ---- the live-RPC ingestion path over a mock transport -----------------

    /// A canned JSON-RPC node: serves `getEpochInfo` + `getAccountInfo`
    /// (base64) from a pubkey→account map — the exact wire shapes a real
    /// `solana-test-validator` answers with.
    struct MockNode {
        slot: u64,
        epoch: u64,
        accounts: HashMap<String, serde_json::Value>,
    }

    impl MockNode {
        fn put(
            &mut self,
            pubkey: &[u8; 32],
            lamports: u64,
            owner: &[u8; 32],
            rent_epoch: u64,
            data: &[u8],
        ) {
            use base64::Engine as _;
            self.accounts.insert(
                bs58::encode(pubkey).into_string(),
                serde_json::json!({
                    "lamports": lamports,
                    "owner": bs58::encode(owner).into_string(),
                    "executable": false,
                    "rentEpoch": rent_epoch,
                    "data": [base64::engine::general_purpose::STANDARD.encode(data), "base64"],
                    "space": data.len(),
                }),
            );
        }
    }

    impl JsonRpcTransport for MockNode {
        fn post(&self, _url: &str, body: &str) -> Result<String, crate::solana_relayer::RpcError> {
            let req: serde_json::Value = serde_json::from_str(body).unwrap();
            let result = match req["method"].as_str().unwrap() {
                "getEpochInfo" => serde_json::json!({
                    "absoluteSlot": self.slot, "epoch": self.epoch,
                    "blockHeight": self.slot, "slotIndex": 0, "slotsInEpoch": 432000u64,
                }),
                "getAccountInfo" => {
                    let pk = req["params"][0].as_str().unwrap();
                    serde_json::json!({
                        "context": {"slot": self.slot},
                        "value": self.accounts.get(pk).cloned().unwrap_or(serde_json::Value::Null),
                    })
                }
                m => panic!("mock node got unexpected method {m}"),
            };
            Ok(serde_json::json!({"jsonrpc": "2.0", "id": 1, "result": result}).to_string())
        }
    }

    /// A consistent single-validator mock cluster: the vote account lives AT
    /// the authority pubkey (the test-validator convention the ledger-dir
    /// constructor relies on), the stake delegates to it, StakeHistory is the
    /// real sysvar id. `voter_for_vote_state` lets the adversarial test plant a
    /// diverging on-chain authorized voter.
    fn mock_cluster(voter_for_vote_state: &[u8; 32]) -> (MockNode, SigningKey, [u8; 32]) {
        let authority = prov::sk(1);
        let vote_account = authority.verifying_key().to_bytes();
        let stake_account = prov::sk(2).verifying_key().to_bytes();
        let epoch = 0u64;

        let mut node = MockNode {
            slot: 4_242,
            epoch,
            accounts: HashMap::new(),
        };
        node.put(
            &TOKEN_ACCOUNT,
            2_039_280,
            &spl_token_program_id(),
            u64::MAX, // the real post-rent-removal RPC value — must survive parsing
            &spl_account_data(&MINT, &WALLET, 777),
        );
        node.put(
            &vote_account,
            1_000_000,
            &vote_program_id(),
            0,
            &prov::build_vote_account_data(&[0x01u8; 32], voter_for_vote_state, epoch),
        );
        node.put(
            &stake_account,
            1_000_000,
            &STAKE_PROGRAM_ID,
            0,
            // The BOOTSTRAP sentinel (`activation_epoch == u64::MAX`), exactly
            // as a fresh `solana-test-validator`'s genesis stake is delegated:
            // fully effective at epoch 0 under Solana's own warmup curve. (A
            // non-bootstrap activation-0 delegation at epoch 0 correctly derives
            // ZERO effective stake — this test originally failed that way.)
            &prov::build_stake_account_data(&vote_account, 900, u64::MAX, u64::MAX),
        );
        node.put(
            &STAKE_HISTORY_SYSVAR_ID,
            1,
            &SYSVAR_OWNER_ID,
            0,
            &prov::encode_stake_history_data(&[]),
        );
        (node, authority, stake_account)
    }

    /// POSITIVE (the live wire path, no validator needed): the local feed
    /// ingests real JSON-RPC shapes (base58 pubkeys, base64 data, u64::MAX
    /// rentEpoch) over the transport seam, and the result verifies through the
    /// production anchored entry.
    #[test]
    fn local_feed_ingests_over_rpc_wire_and_verifies() {
        let (node, authority, stake_account) = mock_cluster(
            &prov::sk(1).verifying_key().to_bytes(), // on-chain voter == ledger key
        );
        let feed_src =
            LocalValidatorFeed::new("http://127.0.0.1:8899", node, authority, stake_account)
                .expect("loopback endpoint accepted");
        let feed = feed_src
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("live-wire ingest");
        let pinned = feed.derived_anchor.clone();
        let holding = prove_feed_holding(&feed, &MINT, &spl_token_program_id(), &pinned, false)
            .expect("anchored verify of the ingested holding");
        assert_eq!(holding.trust, LockProofTrust::ConsensusVerified);
        assert_eq!(holding.owner, WALLET);
        assert_eq!(holding.amount, 777);
        assert_eq!(holding.slot, 4_242);
    }

    /// Rebuild the verified stake table exactly as the anchored verifier does,
    /// from the ingested feed's own bank-state provenance + derived anchor.
    fn verified_table_of(feed: &HoldingFeed) -> crate::solana_provenance::VerifiedStakeTable {
        let p = feed.proof.stake_provenance.as_ref().expect("provenance");
        crate::solana_provenance::VerifiedStakeTable::from_anchor(
            &feed.derived_anchor,
            &p.anchor_accounts_hash,
            &p.anchor_stake_accounts,
            &p.anchor_vote_accounts,
            &p.anchor_stake_history_account,
            p.new_rate_activation_epoch,
        )
        .expect("derive verified table from feed provenance")
    }

    /// POSITIVE (Track A rung 1): the ingested feed evidence now carries a
    /// rooted-finality attestation, so `tally_authorized_rooted` — the leg the
    /// value-release entry `verify_lock_proof_consensus_anchored` demands — clears
    /// over the feed's OWN derived table, which the exact-slot vote alone cannot.
    #[test]
    fn local_feed_supplies_rooted_finality_evidence() {
        let (node, authority, stake_account) =
            mock_cluster(&prov::sk(1).verifying_key().to_bytes());
        let feed = LocalValidatorFeed::new("http://127.0.0.1:8899", node, authority, stake_account)
            .expect("loopback endpoint accepted")
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("live-wire ingest");

        let verified = verified_table_of(&feed);
        let c = &feed.proof.consensus;
        // The exact-slot "which bank hash" super-majority clears (optimistic grade)…
        verified
            .tally_authorized(c.slot, &c.bank_hash, &c.votes)
            .expect("exact-slot super-majority clears");
        // …AND the rooted-finality leg clears from the harvested later vote.
        let rooted = verified
            .tally_authorized_rooted(c.slot, &c.votes)
            .expect("rooted-finality leg clears from the harvested attestation");
        assert!(rooted > 0, "the harvested rooted vote carries real stake");
    }

    /// ADVERSARIAL (the rooted leg is LOAD-BEARING, not decorative): replace the
    /// rooted harvester with an empty one and the SAME feed still clears the
    /// exact-slot super-majority but FAILS the rooted-finality tally with zero
    /// rooted stake — exactly the `SlotNotRooted` a value-release verifier raises.
    #[test]
    fn local_feed_without_rooted_harvest_fails_finality() {
        struct EmptyHarvester;
        impl VoteHarvester for EmptyHarvester {
            fn harvest_rooted(&self, _slot: u64) -> Result<Vec<ValidatorVote>, FeedError> {
                Ok(vec![])
            }
        }
        let (node, authority, stake_account) =
            mock_cluster(&prov::sk(1).verifying_key().to_bytes());
        let feed = LocalValidatorFeed::new("http://127.0.0.1:8899", node, authority, stake_account)
            .expect("loopback endpoint accepted")
            .with_harvester(Box::new(EmptyHarvester))
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("live-wire ingest");

        let verified = verified_table_of(&feed);
        let c = &feed.proof.consensus;
        // Exact-slot still clears — the slot is optimistically confirmed…
        verified
            .tally_authorized(c.slot, &c.bank_hash, &c.votes)
            .expect("exact-slot super-majority still clears");
        // …but WITHOUT the harvest there is no rooted attestation, so finality
        // fails closed with zero rooted stake.
        let (rooted, total) = verified
            .tally_authorized_rooted(c.slot, &c.votes)
            .expect_err("rooted finality must fail closed without the harvest");
        assert_eq!(
            rooted, 0,
            "no rooted stake without the harvested attestation"
        );
        assert!(total > 0, "the derived table has stake");
    }

    /// ADVERSARIAL: a rooted vote whose signer is NOT the vote account's on-chain
    /// authorized voter contributes ZERO rooted stake (an imposter cannot forge
    /// finality) — so the value-release leg still fails closed.
    #[test]
    fn imposter_rooted_vote_carries_no_finality() {
        // Harvest a "rooted" vote for the ledger's vote account, but signed by a
        // STRANGER key (not the on-chain authorized voter).
        let (node, authority, stake_account) =
            mock_cluster(&prov::sk(1).verifying_key().to_bytes());
        let vote_account = authority.verifying_key().to_bytes();
        let imposter = HarvestableVoter {
            vote_authority: prov::sk(9),
            vote_account,
        };
        let feed = LocalValidatorFeed::new("http://127.0.0.1:8899", node, authority, stake_account)
            .expect("loopback endpoint accepted")
            .with_harvester(Box::new(LedgerVoteHarvester::new(vec![imposter])))
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("live-wire ingest");

        let verified = verified_table_of(&feed);
        let c = &feed.proof.consensus;
        let (rooted, _total) = verified
            .tally_authorized_rooted(c.slot, &c.votes)
            .expect_err("an imposter-signed rooted vote must not root the slot");
        assert_eq!(rooted, 0, "imposter contributes no rooted stake");
    }

    /// ADVERSARIAL: a cluster whose on-chain authorized voter is NOT the
    /// ledger keypair is refused at ingest (VoterKeyMismatch) — the feed can
    /// never fabricate a vote the tally would not count anyway.
    #[test]
    fn local_feed_refuses_a_cluster_it_cannot_sign_for() {
        let stranger = prov::sk(9).verifying_key().to_bytes();
        let (node, authority, stake_account) = mock_cluster(&stranger);
        let ledger = authority.verifying_key().to_bytes();
        let feed_src =
            LocalValidatorFeed::new("http://127.0.0.1:8899", node, authority, stake_account)
                .expect("loopback endpoint accepted");
        let err = feed_src
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect_err("must refuse a vote account it is not the authority of");
        assert_eq!(
            err,
            FeedError::VoterKeyMismatch {
                on_chain: stranger,
                ledger,
            }
        );
    }

    /// The endpoint gate: non-loopback plaintext is refused at construction.
    #[test]
    fn plaintext_non_loopback_endpoint_refused() {
        let (node, authority, stake_account) = mock_cluster(&[0u8; 32]);
        let err = LocalValidatorFeed::new(
            "http://rpc.example.com:8899",
            node,
            authority,
            stake_account,
        )
        .err()
        .expect("non-loopback plaintext must be refused");
        assert!(matches!(err, FeedError::Rpc(_)));
    }

    // ---- the mainnet SnapshotFeed scaffold (Track A rung 2) ----------------

    fn fixture_snapshot_bank() -> FixtureSnapshotBank {
        FixtureSnapshotBank {
            dregg_mint: MINT,
            spl_token_program: spl_token_program_id(),
            wallet: WALLET,
            amount: 5_000,
            validators: vec![(1, 700), (2, 200), (3, 100)],
            slot: 9_001,
            epoch: 0,
        }
    }

    /// POSITIVE (the rung-2 scaffold's load-bearing claim): a fixture bank fed
    /// through `SnapshotFeed` reaches the PRODUCTION anchored entry
    /// `prove_holding_consensus_anchored` and verifies to `ConsensusVerified` — the
    /// same trait wiring + production plumbing the real Agave source will use, with
    /// only the snapshot-format parsing left pending.
    #[test]
    fn snapshot_feed_fixture_bank_reaches_production_entry() {
        let bank = fixture_snapshot_bank();
        // The pinned anchor the feed is configured with is the operator's governance
        // pin (module doc `:59`–`:68`); for a single-epoch fixture bank it equals the
        // derived anchor. Build it once by ingesting, then re-verify against the pin.
        let probe = SnapshotFeed::new(fixture_snapshot_bank(), placeholder_anchor())
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("fixture bank ingests through the snapshot seam");
        let pinned = probe.derived_anchor.clone();

        let feed_src = SnapshotFeed::new(bank, pinned.clone());
        assert_eq!(
            feed_src.pinned_anchor().epoch,
            pinned.epoch,
            "the anchor plumbing carries the configured pin"
        );
        let feed = feed_src
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("fixture bank ingests through the snapshot seam");
        let holding = prove_feed_holding(&feed, &MINT, &spl_token_program_id(), &pinned, false)
            .expect("the assembled proof verifies through prove_holding_consensus_anchored");
        assert_eq!(holding.trust, LockProofTrust::ConsensusVerified);
        assert!(holding.is_consensus_proven());
        assert_eq!(holding.owner, WALLET);
        assert_eq!(holding.amount, 5_000);
        assert_eq!(holding.token_account, TOKEN_ACCOUNT);
        assert_eq!(holding.slot, 9_001);
    }

    /// A throwaway anchor for the ingest-probe (ingestion does not check the pin;
    /// verification does — that is `snapshot_feed_rejects_wrong_pin`).
    fn placeholder_anchor() -> WeakSubjectivityAnchor {
        WeakSubjectivityAnchor {
            epoch: 0,
            stake_table_root: [0u8; 32],
        }
    }

    /// MISSING-ARCHIVE-IS-LOUD (the honesty gate): pointing the real Agave source
    /// at a nonexistent archive fails LOUD with an ingestion error naming the
    /// unopenable path — it never silently passes with fabricated bytes.
    #[test]
    fn snapshot_feed_agave_source_missing_archive_fails_loud() {
        let src = SnapshotFeed::new(
            AgaveSnapshotBank::new(
                "/nonexistent/snapshot-100-abc.tar.zst",
                placeholder_anchor(),
            ),
            placeholder_anchor(),
        );
        let err = src
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect_err("a missing snapshot archive must fail loud, not pass");
        match err {
            FeedError::Rpc(msg) => assert!(
                msg.contains("open snapshot archive"),
                "the unopenable archive path is reported, got: {msg}"
            ),
            other => panic!("want Rpc(open ...), got {other:?}"),
        }
    }

    /// Write a synthetic snapshot archive (the REAL tar.zst + AppendVec format) to a
    /// throwaway file and return its path.
    fn write_synth_archive(slot: u64, epoch: u64) -> std::path::PathBuf {
        let archive = agave_snapshot_synth::synthesize_snapshot_archive(
            &MINT,
            &spl_token_program_id(),
            &WALLET,
            5_000,
            &[(1, 700), (2, 200), (3, 100)],
            &TOKEN_ACCOUNT,
            slot,
            epoch,
        );
        let dir = std::env::temp_dir().join("dregg-agave-snap-tests");
        std::fs::create_dir_all(&dir).expect("scratch dir");
        let path = dir.join(format!(
            "snapshot-{slot}-{}-syn.tar.zst",
            std::process::id()
        ));
        std::fs::write(&path, &archive).expect("write synthetic archive");
        path
    }

    /// POSITIVE (rung 2, REAL parse end-to-end): a synthetic snapshot built in the
    /// REAL Agave `.tar.zst` + AppendVec format is parsed by `AgaveSnapshotBank`
    /// (real container unpack, real accounts-DB walk → committed 16-ary Merkle +
    /// inclusion proofs, accounts-hash BOUND to the bank field), flows through
    /// `SnapshotFeed` and the PRODUCTION anchored entry, and verifies to
    /// `ConsensusVerified`. This drives the parser over real on-disk bytes — not the
    /// in-memory `FixtureSnapshotBank`.
    #[test]
    fn agave_snapshot_parses_real_tar_zst_appendvec_end_to_end() {
        let slot = 12_345u64;
        let epoch = 0u64;
        let path = write_synth_archive(slot, epoch);
        let anchor_epoch = WeakSubjectivityAnchor {
            epoch,
            stake_table_root: [0u8; 32],
        };

        // Probe once to learn the derived root (== the governance pin for a
        // single-epoch bank), then re-verify against that pin through production.
        let probe = SnapshotFeed::new(
            AgaveSnapshotBank::new(&path, anchor_epoch.clone()),
            anchor_epoch.clone(),
        )
        .ingest_holding(&TOKEN_ACCOUNT)
        .expect("real Agave tar.zst + AppendVec parse ingests");
        let pinned = probe.derived_anchor.clone();

        let feed = SnapshotFeed::new(AgaveSnapshotBank::new(&path, anchor_epoch), pinned.clone())
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("real Agave parse ingests");
        let holding = prove_feed_holding(&feed, &MINT, &spl_token_program_id(), &pinned, false)
            .expect("the parsed bank verifies through prove_holding_consensus_anchored");
        assert_eq!(holding.trust, LockProofTrust::ConsensusVerified);
        assert!(holding.is_consensus_proven());
        assert_eq!(holding.owner, WALLET);
        assert_eq!(holding.amount, 5_000);
        assert_eq!(holding.token_account, TOKEN_ACCOUNT);
        assert_eq!(holding.slot, slot);
        let _ = std::fs::remove_file(&path);
    }

    /// ADVERSARIAL (tamper the parsed accounts DB): flipping the holder balance in
    /// the assembled proof breaks its recomputed per-account hash, so the committed
    /// 16-ary inclusion no longer folds to the bank's accounts hash — the real parse
    /// path refuses with `AccountsInclusionInvalid`, exactly as the fixture path does.
    #[test]
    fn agave_snapshot_tampered_holder_amount_refused() {
        let path = write_synth_archive(7_000, 0);
        let anchor_epoch = WeakSubjectivityAnchor {
            epoch: 0,
            stake_table_root: [0u8; 32],
        };
        let mut feed = SnapshotFeed::new(
            AgaveSnapshotBank::new(&path, anchor_epoch.clone()),
            anchor_epoch,
        )
        .ingest_holding(&TOKEN_ACCOUNT)
        .expect("real Agave parse ingests");
        let pinned = feed.derived_anchor.clone();
        feed.proof.account.data[crate::solana_holdings::SPL_AMOUNT_OFFSET
            ..crate::solana_holdings::SPL_AMOUNT_OFFSET + 8]
            .copy_from_slice(&u64::MAX.to_le_bytes());
        let err = prove_feed_holding(&feed, &MINT, &spl_token_program_id(), &pinned, false)
            .expect_err("a tampered balance must be refused");
        assert_eq!(err, HoldingProofError::AccountsInclusionInvalid);
        let _ = std::fs::remove_file(&path);
    }

    /// PENDING-IS-LOUD (the one genuinely-unbuilt leg): a snapshot whose epoch
    /// differs from the pinned anchor epoch needs the cross-epoch `RotationStep`
    /// chain (snapshots at successive boundaries) — unbuilt, so the parse fails LOUD
    /// with `NotYetImplemented` naming the rotation leg rather than fabricating a
    /// chain. Everything up to it (container unpack + accounts-DB walk + hash bind)
    /// really ran.
    #[test]
    fn agave_snapshot_cross_epoch_rotation_pending_not_silent() {
        let path = write_synth_archive(20_000, 1); // snapshot at epoch 1…
        let anchor_epoch = WeakSubjectivityAnchor {
            epoch: 0, // …but the pinned anchor is epoch 0.
            stake_table_root: [0u8; 32],
        };
        let err = SnapshotFeed::new(
            AgaveSnapshotBank::new(&path, anchor_epoch.clone()),
            anchor_epoch,
        )
        .ingest_holding(&TOKEN_ACCOUNT)
        .expect_err("cross-epoch rotation must fail loud, not fabricate a chain");
        match err {
            FeedError::NotYetImplemented { stage } => assert!(
                stage.contains("RotationStep chain across epochs"),
                "the cross-epoch rotation leg is named, got: {stage}"
            ),
            other => panic!("want NotYetImplemented (rotation), got {other:?}"),
        }
        let _ = std::fs::remove_file(&path);
    }

    /// ADVERSARIAL (the anchor is load-bearing through the snapshot seam too): a
    /// bank whose derived distribution + self-derived root cannot satisfy a DIFFERENT
    /// governance pin — verification refuses with `AnchorRootMismatch`. The snapshot
    /// source cannot self-authorize any more than the fixture or local source can.
    #[test]
    fn snapshot_feed_rejects_wrong_pin() {
        let feed = SnapshotFeed::new(fixture_snapshot_bank(), placeholder_anchor())
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("fixture bank ingests");
        let honest_pin = WeakSubjectivityAnchor {
            epoch: feed.derived_anchor.epoch,
            stake_table_root: [0xEEu8; 32], // a pin the bank's derived root cannot match
        };
        let err = prove_feed_holding(&feed, &MINT, &spl_token_program_id(), &honest_pin, false)
            .expect_err("a self-derived snapshot anchor must not satisfy a different pin");
        assert!(
            matches!(
                err,
                HoldingProofError::Provenance(ProvenanceError::AnchorRootMismatch { .. })
            ),
            "want AnchorRootMismatch, got {err:?}"
        );
    }

    /// ADVERSARIAL (the committed inclusion has teeth through the snapshot seam):
    /// flipping the holder balance bytes after ingestion breaks the per-account hash
    /// and the verifier refuses with `AccountsInclusionInvalid` — a snapshot consumer
    /// cannot inflate a fed balance.
    #[test]
    fn snapshot_feed_tampered_holder_amount_refused() {
        let mut feed = SnapshotFeed::new(fixture_snapshot_bank(), placeholder_anchor())
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("fixture bank ingests");
        let pinned = feed.derived_anchor.clone();
        feed.proof.account.data[crate::solana_holdings::SPL_AMOUNT_OFFSET
            ..crate::solana_holdings::SPL_AMOUNT_OFFSET + 8]
            .copy_from_slice(&u64::MAX.to_le_bytes());
        let err = prove_feed_holding(&feed, &MINT, &spl_token_program_id(), &pinned, false)
            .expect_err("a tampered balance must be refused");
        assert_eq!(err, HoldingProofError::AccountsInclusionInvalid);
    }

    /// The rooted-finality leg is present through the snapshot seam too: the
    /// assembled evidence carries the harvested rooted votes, so
    /// `tally_authorized_rooted` — the leg the value path demands — clears over the
    /// bank's own derived table.
    #[test]
    fn snapshot_feed_supplies_rooted_finality_evidence() {
        let feed = SnapshotFeed::new(fixture_snapshot_bank(), placeholder_anchor())
            .ingest_holding(&TOKEN_ACCOUNT)
            .expect("fixture bank ingests");
        let verified = verified_table_of(&feed);
        let c = &feed.proof.consensus;
        verified
            .tally_authorized(c.slot, &c.bank_hash, &c.votes)
            .expect("exact-slot super-majority clears");
        let rooted = verified
            .tally_authorized_rooted(c.slot, &c.votes)
            .expect("rooted-finality leg clears from the harvested attestations");
        assert!(rooted > 0, "the harvested rooted votes carry real stake");
    }

    /// The SPL Token program id round-trips to its canonical base58.
    #[test]
    fn spl_token_program_id_is_canonical() {
        assert_eq!(
            bs58::encode(spl_token_program_id()).into_string(),
            "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
        );
    }
}
