//! `solana_relayer`: the **live off-chain relayer** for the Solana mirror.
//!
//! This is the runtime that turns the library-only Solana bridge into a watching
//! service. It replaces the in-memory feed stand-in (the dev-only channel of
//! pre-cooked locks) with a real Solana JSON-RPC client that:
//!
//! 1. **watches** the bridge vault account (or scans the lock program's accounts)
//!    over the real Solana JSON-RPC (`getAccountInfo` / `getProgramAccounts` /
//!    `getSlot`),
//! 2. **verifies** that the observed lock is genuinely *finalized* on Solana and
//!    escrows into the bridge's OWN vault (the BR-2-B escrow-to-vault binding),
//!    then runs the structure/binding [`verify_lock_proof`] over the **real**
//!    on-chain account bytes,
//! 3. **mints** the conserving mirror credit — by handing the verified lock to
//!    the committed, multi-relayer-safe `bridge_mint_against_lock` (the
//!    consume-once nullifier is the global double-mint authority, not this
//!    relayer's RAM).
//!
//! # The trust boundary (named precisely)
//!
//! A plain JSON-RPC endpoint exposes the account state at a commitment level but
//! NOT the bank-hash components, the stake-weighted vote set, or the 16-ary
//! accounts-Merkle proof a light client would need. So the relayer's off-chain
//! verify reaches [`LockProofTrust::StructureOnly`] over the real finalized
//! bytes: a *re-executing validator that trusts the RPC's finalized commitment*
//! accepts it. The fully-trustless consensus path
//! ([`verify_lock_proof_consensus_anchored`]) needs a snapshot/geyser pipeline
//! and is the mainnet route.
//!
//! Crucially, the relayer is **not** the soundness root, and the committed mint
//! does **not** trust a plain RPC. The trust gate (red-team BR-1/BR-2):
//! - the `StructureOnly` verify a plain/forged/MITM RPC can produce CANNOT mint:
//!   [`ObservedLock::to_bridge_mint_request`] sets `consensus_verified = false`
//!   for it, and `bridge_mint_against_lock` refuses that with `TrustTooLow`. Only
//!   [`SolanaRelayer::observe_vault_lock_consensus`] (the stake-weighted
//!   super-majority verify) reaches `ConsensusVerified` and can mint;
//! - the escrow account MUST be the configured vault, owned by the configured
//!   lock program (BR-2-B — [`SolanaLockProof::binds_bridge_vault`]);
//! - conservation is non-vacuous: the committed `currently_locked` is raised by a
//!   SEPARATE consensus-verified escrow leg (`TurnExecutor::bridge_record_escrow`),
//!   and the mint DRAWS against it (refusing `live + amount > currently_locked`),
//!   on top of the consume-once nullifier (the global double-mint authority).
//!
//! ## The in-circuit seam (the parallel circuit swarm's, NOT this module's)
//!
//! For a **dregg light client** (not a re-executing validator) to witness that a
//! mint is backed by a real finalized Solana lock, the Solana consensus + vault
//! binding must be folded into the EffectVM as `dregg_circuit::bridge_action_air`
//! (the G1 VK-epoch). That weld is owned by the circuit swarm; this module does
//! the off-chain relayer verify a re-executing validator runs, and binds the same
//! BR-fix gates into the live path. See `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.

use base64::Engine as _;

use crate::solana_consensus::{BankHashComponents, EpochStakeTable, ValidatorVote};
use crate::solana_mirror::{MirrorConfig, lock_nullifier};
use crate::solana_trustless::{
    AccountInclusionProof, ConsensusEvidence, LockProofError, LockProofTrust,
    MainnetAccountInclusion, SolanaLockProof, verify_lock_proof, verify_lock_proof_consensus,
};
use crate::solana_wire::{
    AccountsInclusionProof16, MerkleLevel, accounts_merkle_node, decode_lock_record,
    encode_lock_record, solana_account_hash,
};
use dregg_cell::Nullifier;
use dregg_types::CellId;

// ===========================================================================
// The chain view the relayer needs (the `SolanaRpc` seam)
// ===========================================================================

/// Solana RPC commitment level (the finality dial). `Finalized` is the only level
/// the relayer mints against; the lower levels exist so the relayer can DETECT an
/// un-finalized lock and refuse it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Commitment {
    /// The most recent block — may be skipped/rolled back. Never minted against.
    Processed,
    /// Voted on by a supermajority but not yet rooted. Never minted against.
    Confirmed,
    /// Rooted by a supermajority — irreversible. The ONLY level a mint draws on.
    Finalized,
}

impl Commitment {
    /// The string Solana's JSON-RPC `commitment` field expects.
    pub fn as_rpc_str(self) -> &'static str {
        match self {
            Self::Processed => "processed",
            Self::Confirmed => "confirmed",
            Self::Finalized => "finalized",
        }
    }
}

/// A Solana account as the relayer sees it over RPC: exactly the fields that feed
/// the per-account hash ([`solana_account_hash`]) plus the lock-record `data`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RpcAccount {
    /// Lamports balance (a finalized lock account is rent-funded, so `> 0`).
    pub lamports: u64,
    /// The owning program (must be the bridge lock program for the escrow gate).
    pub owner: [u8; 32],
    /// Whether the account is executable.
    pub executable: bool,
    /// The account's rent epoch.
    pub rent_epoch: u64,
    /// The raw account data, carrying the adapter lock record
    /// (`lock_id ‖ recipient ‖ amount_le`, see [`encode_lock_record`]).
    pub data: Vec<u8>,
}

/// The result of a `getAccountInfo` query: the account (absent at this commitment
/// ⟹ `None`) plus the slot the query was served at (`context.slot`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccountResponse {
    /// The account at the requested commitment, or `None` if absent there.
    pub account: Option<RpcAccount>,
    /// The slot the RPC served this query at (`context.slot`).
    pub context_slot: u64,
}

/// Why an RPC call failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RpcError {
    /// The byte-pipe (the [`JsonRpcTransport`]) failed.
    Transport(String),
    /// The response was not the JSON-RPC shape we expected.
    Decode(String),
    /// The node returned a JSON-RPC error object.
    Rpc { code: i64, message: String },
}

impl std::fmt::Display for RpcError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Transport(e) => write!(f, "rpc transport error: {e}"),
            Self::Decode(e) => write!(f, "rpc decode error: {e}"),
            Self::Rpc { code, message } => write!(f, "rpc error {code}: {message}"),
        }
    }
}

impl std::error::Error for RpcError {}

/// The relayer's view of the Solana chain. A real JSON-RPC client
/// ([`SolanaJsonRpc`]) and the in-memory test double ([`MockSolanaRpc`]) both
/// implement it; the relayer is generic over it so the watch→verify→mint loop is
/// tested without a network.
pub trait SolanaRpc {
    /// `getAccountInfo(pubkey, {encoding: base64, commitment})`.
    fn get_account_info(
        &self,
        pubkey: &[u8; 32],
        commitment: Commitment,
    ) -> Result<AccountResponse, RpcError>;

    /// `getSlot({commitment})` — the highest slot at this commitment level.
    fn get_slot(&self, commitment: Commitment) -> Result<u64, RpcError>;

    /// `getProgramAccounts(program, {encoding: base64, commitment})` — every
    /// account owned by `program` at this commitment (the lock-account scan).
    fn get_program_accounts(
        &self,
        program: &[u8; 32],
        commitment: Commitment,
    ) -> Result<Vec<([u8; 32], RpcAccount)>, RpcError>;
}

// ===========================================================================
// The real JSON-RPC client (real Solana wire over an injected byte-pipe)
// ===========================================================================

/// The byte-pipe under [`SolanaJsonRpc`]: a single blocking `POST body → string`.
/// This is the one seam where the network lives, so TLS is a deploy concern, not
/// a verified-core dependency. [`StdHttpTransport`] ships for `http://` endpoints
/// (the local `solana-test-validator`); an https/TLS transport is injected by the
/// deploy harness (REVIEWED-GO — the live mainnet relayer).
pub trait JsonRpcTransport {
    /// POST `body` (a JSON-RPC request) to `url` and return the response body.
    fn post(&self, url: &str, body: &str) -> Result<String, RpcError>;
}

/// A real Solana JSON-RPC client: it builds the genuine request envelopes and
/// parses the genuine response shapes (base58 pubkeys, base64 account data),
/// delegating the actual bytes to an injected [`JsonRpcTransport`].
pub struct SolanaJsonRpc<T: JsonRpcTransport> {
    /// The RPC endpoint, e.g. `http://127.0.0.1:8899` or
    /// `https://api.devnet.solana.com`.
    pub url: String,
    transport: T,
}

/// The host authority (`host[:port]`) of a `scheme://` URL, lowercased, with any
/// `userinfo@`, path, query, or fragment stripped.
fn url_authority_host(url: &str) -> String {
    let after_scheme = url.splitn(2, "://").nth(1).unwrap_or(url);
    let authority = after_scheme
        .split(['/', '?', '#'])
        .next()
        .unwrap_or(after_scheme);
    let authority = authority.rsplit('@').next().unwrap_or(authority);
    // Strip the port. `[::1]:8899` → `[::1]`; `127.0.0.1:8899` → `127.0.0.1`.
    let host = if let Some(rest) = authority.strip_prefix('[') {
        rest.split(']').next().unwrap_or(rest)
    } else {
        authority.rsplit_once(':').map_or(authority, |(h, _)| h)
    };
    host.to_ascii_lowercase()
}

/// Is `host` an unambiguous loopback address? (`127.0.0.1` / `localhost` / `::1`).
fn is_loopback_host(host: &str) -> bool {
    host == "127.0.0.1" || host == "localhost" || host == "::1" || host == "[::1]"
}

/// TLS-default endpoint gate (red-team BR-3): accept `https://`, refuse any
/// plaintext `http://`. The explicit local-dev opt-in is
/// [`SolanaJsonRpc::new_plaintext_local_dev`].
fn require_tls_endpoint(url: &str) -> Result<(), RpcError> {
    if url.starts_with("https://") {
        return Ok(());
    }
    Err(RpcError::Transport(format!(
        "plaintext RPC endpoint `{url}` refused: the default transport is TLS (BR-3 — a \
         plaintext RPC lets an on-path MITM forge the lock response and mint). Use https://, \
         or SolanaJsonRpc::new_plaintext_local_dev for an explicit loopback dev endpoint"
    )))
}

/// Loopback-only plaintext gate: accept `http://` ONLY for a loopback host.
fn require_loopback_plaintext(url: &str) -> Result<(), RpcError> {
    let rest = url.strip_prefix("http://").ok_or_else(|| {
        RpcError::Transport(format!("expected an http:// dev endpoint, got `{url}`"))
    })?;
    let host = url_authority_host(&format!("http://{rest}"));
    if is_loopback_host(&host) {
        Ok(())
    } else {
        Err(RpcError::Transport(format!(
            "plaintext endpoint `{url}` is not loopback ({host}): plaintext is permitted only \
             for 127.0.0.1 / localhost / [::1] (BR-3)"
        )))
    }
}

impl<T: JsonRpcTransport> SolanaJsonRpc<T> {
    /// Build a TLS-default client for `url` over `transport` (red-team BR-3).
    ///
    /// The default transport posture is TLS: a plaintext `http://` endpoint is
    /// REFUSED, because any on-path network attacker (not just the RPC operator)
    /// can forge a plaintext `getAccountInfo` response and — combined with a
    /// missing consensus gate — mint unbacked. For a local
    /// `solana-test-validator` over plaintext loopback, use the explicit
    /// localhost-only opt-in [`Self::new_plaintext_local_dev`].
    pub fn new(url: impl Into<String>, transport: T) -> Result<Self, RpcError> {
        let url = url.into();
        require_tls_endpoint(&url)?;
        Ok(Self { url, transport })
    }

    /// EXPLICIT local-dev opt-in: permit a plaintext `http://` endpoint ONLY when
    /// it is loopback (`127.0.0.1` / `localhost` / `[::1]`). A non-loopback
    /// plaintext URL — or a typo'd public host — is refused, so plaintext can
    /// never silently reach a remote RPC. `https://` is always accepted here too.
    pub fn new_plaintext_local_dev(url: impl Into<String>, transport: T) -> Result<Self, RpcError> {
        let url = url.into();
        if url.starts_with("https://") {
            return Ok(Self { url, transport });
        }
        require_loopback_plaintext(&url)?;
        Ok(Self { url, transport })
    }

    fn call(&self, method: &str, params: serde_json::Value) -> Result<serde_json::Value, RpcError> {
        let req = serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": method,
            "params": params,
        });
        let body = serde_json::to_string(&req).map_err(|e| RpcError::Decode(e.to_string()))?;
        let resp = self.transport.post(&self.url, &body)?;
        let v: serde_json::Value =
            serde_json::from_str(&resp).map_err(|e| RpcError::Decode(e.to_string()))?;
        if let Some(err) = v.get("error") {
            let code = err.get("code").and_then(|c| c.as_i64()).unwrap_or(0);
            let message = err
                .get("message")
                .and_then(|m| m.as_str())
                .unwrap_or("")
                .to_string();
            return Err(RpcError::Rpc { code, message });
        }
        v.get("result")
            .cloned()
            .ok_or_else(|| RpcError::Decode("missing `result`".into()))
    }
}

/// Decode a base58 pubkey string into 32 bytes.
fn b58_pubkey(s: &str) -> Result<[u8; 32], RpcError> {
    let v = bs58::decode(s)
        .into_vec()
        .map_err(|e| RpcError::Decode(format!("base58 pubkey: {e}")))?;
    if v.len() != 32 {
        return Err(RpcError::Decode(format!(
            "pubkey is {} bytes, expected 32",
            v.len()
        )));
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&v);
    Ok(out)
}

/// Parse the `value`/`account` JSON object Solana returns for one account.
fn parse_account(v: &serde_json::Value) -> Result<RpcAccount, RpcError> {
    let lamports = v
        .get("lamports")
        .and_then(|x| x.as_u64())
        .ok_or_else(|| RpcError::Decode("account.lamports".into()))?;
    let owner = b58_pubkey(
        v.get("owner")
            .and_then(|x| x.as_str())
            .ok_or_else(|| RpcError::Decode("account.owner".into()))?,
    )?;
    let executable = v
        .get("executable")
        .and_then(|x| x.as_bool())
        .unwrap_or(false);
    let rent_epoch = v.get("rentEpoch").and_then(|x| x.as_u64()).unwrap_or(0);
    // data is `["<base64>", "base64"]`.
    let data = match v.get("data") {
        Some(serde_json::Value::Array(a)) => {
            let b64 = a
                .first()
                .and_then(|x| x.as_str())
                .ok_or_else(|| RpcError::Decode("account.data[0]".into()))?;
            base64::engine::general_purpose::STANDARD
                .decode(b64)
                .map_err(|e| RpcError::Decode(format!("account.data base64: {e}")))?
        }
        // A program account with empty data may come back as `""`.
        Some(serde_json::Value::String(s)) if s.is_empty() => Vec::new(),
        _ => return Err(RpcError::Decode("account.data shape".into())),
    };
    Ok(RpcAccount {
        lamports,
        owner,
        executable,
        rent_epoch,
        data,
    })
}

impl<T: JsonRpcTransport> SolanaRpc for SolanaJsonRpc<T> {
    fn get_account_info(
        &self,
        pubkey: &[u8; 32],
        commitment: Commitment,
    ) -> Result<AccountResponse, RpcError> {
        let pk = bs58::encode(pubkey).into_string();
        let result = self.call(
            "getAccountInfo",
            serde_json::json!([
                pk,
                {"encoding": "base64", "commitment": commitment.as_rpc_str()}
            ]),
        )?;
        let context_slot = result
            .get("context")
            .and_then(|c| c.get("slot"))
            .and_then(|s| s.as_u64())
            .ok_or_else(|| RpcError::Decode("context.slot".into()))?;
        let account = match result.get("value") {
            Some(serde_json::Value::Null) | None => None,
            Some(v) => Some(parse_account(v)?),
        };
        Ok(AccountResponse {
            account,
            context_slot,
        })
    }

    fn get_slot(&self, commitment: Commitment) -> Result<u64, RpcError> {
        let result = self.call(
            "getSlot",
            serde_json::json!([{"commitment": commitment.as_rpc_str()}]),
        )?;
        result
            .as_u64()
            .ok_or_else(|| RpcError::Decode("getSlot result".into()))
    }

    fn get_program_accounts(
        &self,
        program: &[u8; 32],
        commitment: Commitment,
    ) -> Result<Vec<([u8; 32], RpcAccount)>, RpcError> {
        let pk = bs58::encode(program).into_string();
        let result = self.call(
            "getProgramAccounts",
            serde_json::json!([
                pk,
                {"encoding": "base64", "commitment": commitment.as_rpc_str()}
            ]),
        )?;
        let arr = result
            .as_array()
            .ok_or_else(|| RpcError::Decode("getProgramAccounts result".into()))?;
        let mut out = Vec::with_capacity(arr.len());
        for entry in arr {
            let pubkey = b58_pubkey(
                entry
                    .get("pubkey")
                    .and_then(|x| x.as_str())
                    .ok_or_else(|| RpcError::Decode("programAccount.pubkey".into()))?,
            )?;
            let account = parse_account(
                entry
                    .get("account")
                    .ok_or_else(|| RpcError::Decode("programAccount.account".into()))?,
            )?;
            out.push((pubkey, account));
        }
        Ok(out)
    }
}

/// A dependency-free blocking HTTP/1.1 transport over `std::net::TcpStream`, for
/// **`http://`** endpoints (the local `solana-test-validator` on
/// `http://127.0.0.1:8899`). It speaks `Connection: close` and reads to EOF, then
/// de-chunks a `Transfer-Encoding: chunked` body. `https://` endpoints return a
/// clear [`RpcError::Transport`] asking for an injected TLS transport — TLS is a
/// deploy concern (REVIEWED-GO), not a verified-core dependency.
pub struct StdHttpTransport {
    /// Connect/read timeout.
    pub timeout: std::time::Duration,
}

impl Default for StdHttpTransport {
    fn default() -> Self {
        Self {
            timeout: std::time::Duration::from_secs(20),
        }
    }
}

impl JsonRpcTransport for StdHttpTransport {
    fn post(&self, url: &str, body: &str) -> Result<String, RpcError> {
        use std::io::{Read, Write};
        use std::net::TcpStream;

        let rest = url.strip_prefix("http://").ok_or_else(|| {
            RpcError::Transport(format!(
                "StdHttpTransport only handles http:// (got `{url}`); inject a TLS \
                 transport for https endpoints"
            ))
        })?;
        let (authority, path) = match rest.find('/') {
            Some(i) => (&rest[..i], &rest[i..]),
            None => (rest, "/"),
        };
        let (host, port) = match authority.rsplit_once(':') {
            Some((h, p)) => (
                h,
                p.parse::<u16>()
                    .map_err(|e| RpcError::Transport(format!("bad port: {e}")))?,
            ),
            None => (authority, 80u16),
        };

        let mut stream = TcpStream::connect((host, port))
            .map_err(|e| RpcError::Transport(format!("connect {host}:{port}: {e}")))?;
        stream
            .set_read_timeout(Some(self.timeout))
            .map_err(|e| RpcError::Transport(e.to_string()))?;
        stream
            .set_write_timeout(Some(self.timeout))
            .map_err(|e| RpcError::Transport(e.to_string()))?;

        let req = format!(
            "POST {path} HTTP/1.1\r\nHost: {host}\r\nContent-Type: application/json\r\n\
             Accept: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
            body.len()
        );
        stream
            .write_all(req.as_bytes())
            .map_err(|e| RpcError::Transport(format!("write: {e}")))?;

        let mut raw = Vec::new();
        stream
            .read_to_end(&mut raw)
            .map_err(|e| RpcError::Transport(format!("read: {e}")))?;

        let split = raw
            .windows(4)
            .position(|w| w == b"\r\n\r\n")
            .ok_or_else(|| RpcError::Transport("no header/body boundary".into()))?;
        let headers = String::from_utf8_lossy(&raw[..split]).to_ascii_lowercase();
        let body_bytes = &raw[split + 4..];

        let body = if headers.contains("transfer-encoding: chunked") {
            dechunk(body_bytes)?
        } else {
            body_bytes.to_vec()
        };
        String::from_utf8(body).map_err(|e| RpcError::Transport(format!("utf8 body: {e}")))
    }
}

/// De-chunk an HTTP/1.1 `Transfer-Encoding: chunked` body.
fn dechunk(mut b: &[u8]) -> Result<Vec<u8>, RpcError> {
    let mut out = Vec::new();
    loop {
        let nl = b
            .windows(2)
            .position(|w| w == b"\r\n")
            .ok_or_else(|| RpcError::Transport("chunk size line".into()))?;
        let size_str = std::str::from_utf8(&b[..nl])
            .map_err(|_| RpcError::Transport("chunk size utf8".into()))?
            .trim();
        // Ignore any chunk extension after `;`.
        let size_hex = size_str.split(';').next().unwrap_or("");
        let size = usize::from_str_radix(size_hex, 16)
            .map_err(|_| RpcError::Transport(format!("chunk size hex `{size_hex}`")))?;
        b = &b[nl + 2..];
        if size == 0 {
            break;
        }
        if b.len() < size {
            return Err(RpcError::Transport("truncated chunk".into()));
        }
        out.extend_from_slice(&b[..size]);
        b = &b[size..];
        // Skip the trailing CRLF after the chunk data.
        if b.len() >= 2 && &b[..2] == b"\r\n" {
            b = &b[2..];
        }
    }
    Ok(out)
}

// ===========================================================================
// The relayer: watch → verify (finality + escrow) → produce the mint input
// ===========================================================================

/// A finalized, structurally-verified lock observed on Solana — the relayer's
/// output. It carries the consume-once [`Self::nullifier`] and the verified
/// [`SolanaLockProof`] over the REAL on-chain bytes, ready to feed the committed
/// `bridge_mint_against_lock` (the sound, multi-relayer-safe mint).
#[derive(Clone, Debug)]
pub struct ObservedLock {
    /// The lock event id (replay nonce) decoded from the vault record.
    pub lock_id: [u8; 32],
    /// The SPL mint this mirror tracks.
    pub spl_mint: [u8; 32],
    /// The dregg cell the mint credits.
    pub recipient: CellId,
    /// The locked amount (atomic units).
    pub amount: u64,
    /// The consume-once nullifier (the GLOBAL double-mint authority once consumed
    /// against the committed `note_nullifiers` set).
    pub nullifier: Nullifier,
    /// The structure/binding-verified lock proof over the real finalized bytes.
    pub proof: SolanaLockProof,
    /// The slot the finalized `getAccountInfo` was served at.
    pub observed_slot: u64,
    /// The finalized slot reported by `getSlot(finalized)` when observed.
    pub finalized_slot: u64,
    /// The trust the off-chain verify achieved (StructureOnly over a plain RPC).
    pub trust: LockProofTrust,
}

/// Why the relayer refused to surface an observed account as a mintable lock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelayerError {
    /// An RPC call failed.
    Rpc(RpcError),
    /// The vault account is not present at the **finalized** commitment — the
    /// lock is not yet (or never) finalized, so it is NOT minted.
    NotFinalized,
    /// The RPC served a `getAccountInfo` whose `context.slot` is ahead of the
    /// reported finalized slot — an inconsistent/forging node. Refused.
    SlotAheadOfFinalized { context: u64, finalized: u64 },
    /// The vault account holds no decodable lock record.
    NoLockRecord,
    /// The observed lock does not escrow into THIS bridge's configured vault,
    /// owned by its lock program (BR-2-B). It exists on Solana but is not the
    /// bridge's escrow — minting it would credit against nothing.
    NotBridgeVault,
    /// Structure/binding verification of the assembled lock proof failed.
    Proof(LockProofError),
}

impl std::fmt::Display for RelayerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Rpc(e) => write!(f, "{e}"),
            Self::NotFinalized => {
                write!(f, "vault account is not finalized on Solana (not minted)")
            }
            Self::SlotAheadOfFinalized { context, finalized } => write!(
                f,
                "rpc context slot {context} is ahead of finalized {finalized} (inconsistent node)"
            ),
            Self::NoLockRecord => write!(f, "vault account holds no decodable lock record"),
            Self::NotBridgeVault => write!(
                f,
                "observed lock does not escrow into the bridge vault owned by the lock program"
            ),
            Self::Proof(e) => write!(f, "lock proof rejected: {e}"),
        }
    }
}

impl std::error::Error for RelayerError {}

impl From<RpcError> for RelayerError {
    fn from(e: RpcError) -> Self {
        Self::Rpc(e)
    }
}

/// The live off-chain Solana relayer over a [`SolanaRpc`] connection.
pub struct SolanaRelayer<R: SolanaRpc> {
    /// The mirror configuration (vault, lock program, mint, bounds).
    pub config: MirrorConfig,
    /// The chain connection.
    pub rpc: R,
}

impl<R: SolanaRpc> SolanaRelayer<R> {
    /// Build a relayer for `config` over `rpc`.
    pub fn new(config: MirrorConfig, rpc: R) -> Self {
        Self { config, rpc }
    }

    /// **Watch the configured bridge vault and surface a finalized lock.**
    ///
    /// One poll of the watch loop: read the vault at finalized commitment, gate
    /// finality, decode the lock record, build the lock proof over the REAL
    /// finalized account bytes, enforce the escrow-to-bridge-vault binding
    /// (BR-2-B), and run [`verify_lock_proof`]. Returns the [`ObservedLock`] the
    /// caller feeds to the committed mint, or the precise refusal.
    pub fn observe_vault_lock(&self) -> Result<ObservedLock, RelayerError> {
        let vault = self.config.vault_account;
        self.observe_lock_at(&vault)
    }

    /// **Scan the lock program for all finalized lock accounts.**
    ///
    /// `getProgramAccounts` over the configured lock program, then run the same
    /// finalized verify on each owned account. Accounts that are not the
    /// configured vault, hold no lock record, or fail verification are skipped
    /// (returned as `Err` per account so the caller can log them).
    pub fn scan_program_locks(&self) -> Result<Vec<Result<ObservedLock, RelayerError>>, RpcError> {
        let accounts = self
            .rpc
            .get_program_accounts(&self.config.lock_program, Commitment::Finalized)?;
        let finalized = self.rpc.get_slot(Commitment::Finalized)?;
        Ok(accounts
            .into_iter()
            .map(|(pubkey, account)| {
                self.verify_finalized_account(&pubkey, &account, finalized, finalized)
            })
            .collect())
    }

    /// Observe a specific vault `pubkey` (used by [`Self::observe_vault_lock`]).
    pub fn observe_lock_at(&self, pubkey: &[u8; 32]) -> Result<ObservedLock, RelayerError> {
        // (1) finality: the lock MUST be visible at finalized commitment. An
        //     un-finalized lock (present only at confirmed/processed) returns
        //     `None` here and is refused — never minted against.
        let finalized = self.rpc.get_slot(Commitment::Finalized)?;
        let resp = self.rpc.get_account_info(pubkey, Commitment::Finalized)?;
        let account = resp.account.ok_or(RelayerError::NotFinalized)?;
        if resp.context_slot > finalized {
            return Err(RelayerError::SlotAheadOfFinalized {
                context: resp.context_slot,
                finalized,
            });
        }
        self.verify_finalized_account(pubkey, &account, resp.context_slot, finalized)
    }

    /// The shared verify over a finalized account: decode → assemble proof over
    /// the REAL bytes → escrow-to-vault binding (BR-2-B) → structure/binding
    /// verify. Slot args are recorded into the returned [`ObservedLock`].
    fn verify_finalized_account(
        &self,
        pubkey: &[u8; 32],
        account: &RpcAccount,
        observed_slot: u64,
        finalized_slot: u64,
    ) -> Result<ObservedLock, RelayerError> {
        // (2) decode the adapter lock record from the real on-chain data.
        let (lock_id, recipient, amount) =
            decode_lock_record(&account.data).ok_or(RelayerError::NoLockRecord)?;

        // (3) assemble a StructureOnly lock proof over the REAL finalized bytes:
        //     a single-leaf accounts hash + the genuine owner/lamports, so the
        //     escrow binding's mainnet `owner == lock_program` check is real.
        let proof =
            build_structure_proof(pubkey, account, lock_id, recipient, amount, &self.config);

        // (4) BR-2-B: the lock MUST escrow into THIS bridge's configured vault,
        //     owned by the configured lock program. An account that merely exists
        //     on Solana (different pubkey or owner) is refused — minting it would
        //     credit against nothing.
        if !proof.binds_bridge_vault(&self.config.vault_account, &self.config.lock_program) {
            return Err(RelayerError::NotBridgeVault);
        }

        // (5) structure + binding verify (mint match, amount bounds, the included
        //     record matches the bound claim). StructureOnly over a plain RPC;
        //     the consensus leg is the geyser/mainnet route (G1 in-circuit seam).
        let trust = verify_lock_proof(
            &proof,
            &self.config.spl_mint,
            self.config.min_amount,
            self.config.max_amount,
        )
        .map_err(RelayerError::Proof)?;

        Ok(ObservedLock {
            lock_id,
            spl_mint: self.config.spl_mint,
            recipient,
            amount,
            nullifier: lock_nullifier(&self.config.spl_mint, &lock_id),
            proof,
            observed_slot,
            finalized_slot,
            trust,
        })
    }

    /// **Observe the vault lock and verify it to [`LockProofTrust::ConsensusVerified`]**
    /// against a tracked epoch `stake_table` — the trust level the committed mint
    /// now REQUIRES (red-team BR-1). This wires the previously-dead consensus
    /// machinery ([`verify_lock_proof_consensus`] → the stake-weighted Ed25519
    /// super-majority tally) onto the live mint path: only an `ObservedLock` from
    /// THIS path carries `trust == ConsensusVerified`, so only it produces a
    /// mintable request (the `StructureOnly` [`Self::observe_vault_lock`] cannot).
    ///
    /// A plain JSON-RPC endpoint does not expose the bank-hash components / vote
    /// set, so the `consensus` evidence + `stake_table` are supplied by the
    /// operator's snapshot/geyser feed; the relayer cross-checks that evidence
    /// against the REAL finalized account it reads itself (same lock_id /
    /// recipient / amount, escrow-to-bridge-vault binding), then runs the real
    /// consensus verify. The fully-trustless in-circuit witness (so a dregg LIGHT
    /// client, not this re-executing relayer, sees the backing) remains the
    /// circuit swarm's G1 VK-epoch.
    pub fn observe_vault_lock_consensus(
        &self,
        consensus: ConsensusEvidence,
        stake_table: &EpochStakeTable,
        require_poh: bool,
    ) -> Result<ObservedLock, RelayerError> {
        let vault = self.config.vault_account;
        self.observe_lock_at_consensus(&vault, consensus, stake_table, require_poh)
    }

    /// Consensus-verifying observe of a specific `pubkey` (see
    /// [`Self::observe_vault_lock_consensus`]).
    pub fn observe_lock_at_consensus(
        &self,
        pubkey: &[u8; 32],
        consensus: ConsensusEvidence,
        stake_table: &EpochStakeTable,
        require_poh: bool,
    ) -> Result<ObservedLock, RelayerError> {
        // (1) finality gate over the REAL account, exactly as the structure path.
        let finalized = self.rpc.get_slot(Commitment::Finalized)?;
        let resp = self.rpc.get_account_info(pubkey, Commitment::Finalized)?;
        let account = resp.account.ok_or(RelayerError::NotFinalized)?;
        if resp.context_slot > finalized {
            return Err(RelayerError::SlotAheadOfFinalized {
                context: resp.context_slot,
                finalized,
            });
        }

        // (2) decode the lock record from the REAL on-chain bytes.
        let (lock_id, recipient, amount) =
            decode_lock_record(&account.data).ok_or(RelayerError::NoLockRecord)?;

        // (3) assemble the proof binding the real finalized account to the
        //     operator-supplied consensus evidence (the vote set + bank hash the
        //     relayer cannot get from plain RPC). The inclusion is built over the
        //     real bytes; the consensus leg is the supplied evidence.
        let proof = build_consensus_proof(
            pubkey,
            &account,
            lock_id,
            recipient,
            amount,
            consensus,
            &self.config,
        );

        // (4) BR-2-B: escrow-to-bridge-vault binding over the real account.
        if !proof.binds_bridge_vault(&self.config.vault_account, &self.config.lock_program) {
            return Err(RelayerError::NotBridgeVault);
        }

        // (5) the REAL consensus verify: ≥2/3 stake-weighted Ed25519 super-majority
        //     over the supplied stake table, bank-hash binding, inclusion. Reaches
        //     ConsensusVerified — or refuses (e.g. StakeBelowThreshold).
        let trust = verify_lock_proof_consensus(
            &proof,
            &self.config.spl_mint,
            self.config.min_amount,
            self.config.max_amount,
            stake_table,
            require_poh,
        )
        .map_err(RelayerError::Proof)?;

        Ok(ObservedLock {
            lock_id,
            spl_mint: self.config.spl_mint,
            recipient,
            amount,
            nullifier: lock_nullifier(&self.config.spl_mint, &lock_id),
            proof,
            observed_slot: resp.context_slot,
            finalized_slot: finalized,
            trust,
        })
    }
}

/// Assemble a [`SolanaLockProof`] over the REAL finalized vault bytes with a
/// single-leaf accounts hash (the StructureOnly inclusion the relayer can build
/// from plain RPC; the 16-ary multi-account proof + the stake-weighted vote set
/// are the geyser/mainnet trustless route). The owner/lamports are the genuine
/// on-chain values so the escrow `owner == lock_program` binding is real.
fn build_structure_proof(
    pubkey: &[u8; 32],
    account: &RpcAccount,
    lock_id: [u8; 32],
    recipient: CellId,
    amount: u64,
    config: &MirrorConfig,
) -> SolanaLockProof {
    // Canonicalize the lock record so the leaf binds exactly the decoded claim.
    let vault_data = encode_lock_record(&lock_id, &recipient, amount);
    let vault_leaf = solana_account_hash(
        account.lamports,
        &account.owner,
        account.executable,
        account.rent_epoch,
        &vault_data,
        pubkey,
    );
    let accounts_hash = accounts_merkle_node(&[vault_leaf]);
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
    SolanaLockProof {
        lock_id,
        spl_mint: config.spl_mint,
        amount,
        dregg_recipient: recipient,
        consensus: ConsensusEvidence {
            slot: 0,
            bank_hash,
            epoch: 0,
            // Claimed-tally hint only (StructureOnly sanity, NOT counted consensus
            // — the relayer over a plain RPC cannot anchor the vote set; that is
            // the geyser/mainnet route + the G1 in-circuit weld).
            voted_stake: 3,
            total_stake: 3,
            votes: vec![ValidatorVote::sign(
                &ed25519_dalek::SigningKey::from_bytes(&[0x77u8; 32]),
                0,
                bank_hash,
            )],
            bank_components,
            poh: None,
        },
        inclusion: AccountInclusionProof {
            vault_account: *pubkey,
            recorded_amount: amount,
            recorded_recipient: recipient,
            recorded_lock_id: lock_id,
            accounts_hash,
            merkle_path: vec![],
            mainnet: Some(MainnetAccountInclusion {
                lamports: account.lamports,
                owner: account.owner,
                executable: account.executable,
                rent_epoch: account.rent_epoch,
                data: vault_data,
                proof: vault_proof,
            }),
        },
        stake_provenance: None,
    }
}

/// Assemble a [`SolanaLockProof`] binding the REAL finalized vault bytes (the
/// single-leaf accounts inclusion the relayer builds itself) to the
/// operator-supplied `consensus` evidence (the vote set + bank hash a snapshot/
/// geyser feed provides, which plain RPC does not). The consensus leg is NOT
/// re-derived; [`verify_lock_proof_consensus`] then cross-checks it against the
/// inclusion (`bank_components.accounts_hash == inclusion.accounts_hash`) and the
/// stake table — so a consensus bundle inconsistent with the real account, or one
/// short of the 2/3 super-majority, is refused.
fn build_consensus_proof(
    pubkey: &[u8; 32],
    account: &RpcAccount,
    lock_id: [u8; 32],
    recipient: CellId,
    amount: u64,
    consensus: ConsensusEvidence,
    config: &MirrorConfig,
) -> SolanaLockProof {
    let vault_data = encode_lock_record(&lock_id, &recipient, amount);
    let vault_leaf = solana_account_hash(
        account.lamports,
        &account.owner,
        account.executable,
        account.rent_epoch,
        &vault_data,
        pubkey,
    );
    let accounts_hash = accounts_merkle_node(&[vault_leaf]);
    let vault_proof = AccountsInclusionProof16 {
        levels: vec![MerkleLevel {
            position: 0,
            siblings: vec![],
        }],
    };
    SolanaLockProof {
        lock_id,
        spl_mint: config.spl_mint,
        amount,
        dregg_recipient: recipient,
        consensus,
        inclusion: AccountInclusionProof {
            vault_account: *pubkey,
            recorded_amount: amount,
            recorded_recipient: recipient,
            recorded_lock_id: lock_id,
            accounts_hash,
            merkle_path: vec![],
            mainnet: Some(MainnetAccountInclusion {
                lamports: account.lamports,
                owner: account.owner,
                executable: account.executable,
                rent_epoch: account.rent_epoch,
                data: vault_data,
                proof: vault_proof,
            }),
        },
        stake_provenance: None,
    }
}

impl ObservedLock {
    /// Build the committed-mint input (`dregg_turn::BridgeMintRequest`) for the
    /// SOUND, multi-relayer-safe path: `actor` holds the mirror's mint-cap and
    /// `ledger_cell` is the committed mirror-ledger cell. The consume-once
    /// nullifier carried here is the GLOBAL double-mint authority once consumed.
    ///
    /// The committed mint is GATED on `consensus_verified` (red-team BR-1): we set
    /// it ONLY when the off-chain verify reached
    /// [`LockProofTrust::ConsensusVerified`]. A `StructureOnly` observation (the
    /// plain-RPC route a forged/MITM RPC can fabricate) yields `false`, so
    /// `bridge_mint_against_lock` refuses it with `TrustTooLow` — it cannot mint.
    pub fn to_bridge_mint_request(
        &self,
        actor: CellId,
        ledger_cell: CellId,
    ) -> dregg_turn::BridgeMintRequest {
        dregg_turn::BridgeMintRequest {
            actor,
            ledger_cell,
            lock_nullifier: self.nullifier,
            recipient: self.recipient,
            amount: self.amount,
            consensus_verified: self.trust == LockProofTrust::ConsensusVerified,
        }
    }

    /// Build the INDEPENDENT escrow-record input
    /// (`dregg_turn::BridgeEscrowRecord`) that raises the committed
    /// `currently_locked` backing this lock will be minted against (red-team
    /// BR-2/BR-3). Gated on the same `ConsensusVerified` trust: a `StructureOnly`
    /// observation cannot raise the backing, so a later draw against it is refused
    /// by conservation. The escrow nullifier is domain-separated from the mint
    /// nullifier so the same lock records its escrow exactly once and mints once.
    pub fn to_escrow_record(&self, ledger_cell: CellId) -> dregg_turn::BridgeEscrowRecord {
        dregg_turn::BridgeEscrowRecord {
            ledger_cell,
            escrow_nullifier: dregg_turn::escrow_nullifier_for(&self.nullifier),
            escrowed: self.amount,
            consensus_verified: self.trust == LockProofTrust::ConsensusVerified,
        }
    }
}

// ===========================================================================
// In-memory test double (the replacement for the dev-only feed stand-in)
// ===========================================================================

/// An in-memory [`SolanaRpc`] for tests and for the dev relayer harness — the
/// honest replacement for the old in-memory feed: it models the SAME
/// finalized/confirmed commitment split a real node exposes, so the relayer's
/// finality gate (and an un-finalized refusal) is exercised without a network.
#[cfg(any(test, feature = "test-utils"))]
#[derive(Clone, Debug, Default)]
pub struct MockSolanaRpc {
    finalized_slot: u64,
    confirmed_slot: u64,
    processed_slot: u64,
    /// Accounts visible at finalized commitment (and therefore at all levels).
    finalized: std::collections::BTreeMap<[u8; 32], RpcAccount>,
    /// Accounts visible at confirmed/processed but NOT yet finalized.
    confirmed_only: std::collections::BTreeMap<[u8; 32], RpcAccount>,
}

#[cfg(any(test, feature = "test-utils"))]
impl MockSolanaRpc {
    /// A mock at the given slots (`finalized ≤ confirmed ≤ processed`).
    pub fn new(finalized_slot: u64, confirmed_slot: u64, processed_slot: u64) -> Self {
        Self {
            finalized_slot,
            confirmed_slot,
            processed_slot,
            finalized: std::collections::BTreeMap::new(),
            confirmed_only: std::collections::BTreeMap::new(),
        }
    }

    /// Build a raw account holding the adapter lock record.
    pub fn lock_account(
        owner: [u8; 32],
        lamports: u64,
        rent_epoch: u64,
        lock_id: [u8; 32],
        recipient: CellId,
        amount: u64,
    ) -> RpcAccount {
        RpcAccount {
            lamports,
            owner,
            executable: false,
            rent_epoch,
            data: encode_lock_record(&lock_id, &recipient, amount),
        }
    }

    /// Insert an account visible at **finalized** commitment.
    pub fn insert_finalized(&mut self, pubkey: [u8; 32], account: RpcAccount) -> &mut Self {
        self.finalized.insert(pubkey, account);
        self
    }

    /// Insert an account visible only at **confirmed** commitment (the
    /// un-finalized case the relayer must refuse).
    pub fn insert_confirmed_only(&mut self, pubkey: [u8; 32], account: RpcAccount) -> &mut Self {
        self.confirmed_only.insert(pubkey, account);
        self
    }
}

#[cfg(any(test, feature = "test-utils"))]
impl SolanaRpc for MockSolanaRpc {
    fn get_account_info(
        &self,
        pubkey: &[u8; 32],
        commitment: Commitment,
    ) -> Result<AccountResponse, RpcError> {
        let (account, context_slot) = match commitment {
            Commitment::Finalized => (self.finalized.get(pubkey).cloned(), self.finalized_slot),
            Commitment::Confirmed => (
                self.finalized
                    .get(pubkey)
                    .or_else(|| self.confirmed_only.get(pubkey))
                    .cloned(),
                self.confirmed_slot,
            ),
            Commitment::Processed => (
                self.finalized
                    .get(pubkey)
                    .or_else(|| self.confirmed_only.get(pubkey))
                    .cloned(),
                self.processed_slot,
            ),
        };
        Ok(AccountResponse {
            account,
            context_slot,
        })
    }

    fn get_slot(&self, commitment: Commitment) -> Result<u64, RpcError> {
        Ok(match commitment {
            Commitment::Finalized => self.finalized_slot,
            Commitment::Confirmed => self.confirmed_slot,
            Commitment::Processed => self.processed_slot,
        })
    }

    fn get_program_accounts(
        &self,
        program: &[u8; 32],
        commitment: Commitment,
    ) -> Result<Vec<([u8; 32], RpcAccount)>, RpcError> {
        let mut out = Vec::new();
        let mut push_owned = |map: &std::collections::BTreeMap<[u8; 32], RpcAccount>| {
            for (pk, acct) in map {
                if &acct.owner == program {
                    out.push((*pk, acct.clone()));
                }
            }
        };
        push_owned(&self.finalized);
        if commitment != Commitment::Finalized {
            push_owned(&self.confirmed_only);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SPL_MINT: [u8; 32] = [0xABu8; 32];
    const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32];
    const VAULT: [u8; 32] = [0x22u8; 32];
    const LOCK_PROGRAM: [u8; 32] = [0x07u8; 32];

    fn config() -> MirrorConfig {
        MirrorConfig {
            spl_mint: SPL_MINT,
            asset: MIRROR_ASSET,
            oracle_keys: vec![],
            min_amount: 1,
            max_amount: 1_000_000,
            vault_account: VAULT,
            lock_program: LOCK_PROGRAM,
            pinned_anchor_epoch: None,
            pinned_anchor_root: None,
        }
    }

    fn lock_id(n: u8) -> [u8; 32] {
        [n; 32]
    }

    // ---- the JSON-RPC wire codec (real Solana shapes) ----------------------

    /// A canned transport returning a fixed response — proves the REAL request is
    /// built and the REAL Solana response shape parses.
    struct CannedTransport {
        expect_method: &'static str,
        response: String,
        seen: std::cell::RefCell<Option<String>>,
    }

    impl JsonRpcTransport for CannedTransport {
        fn post(&self, _url: &str, body: &str) -> Result<String, RpcError> {
            *self.seen.borrow_mut() = Some(body.to_string());
            assert!(
                body.contains(self.expect_method),
                "request did not name {}: {body}",
                self.expect_method
            );
            Ok(self.response.clone())
        }
    }

    #[test]
    fn json_rpc_parses_real_get_account_info_shape() {
        // A genuine Solana getAccountInfo response: base58 owner, base64 data,
        // context.slot.
        let lid = lock_id(9);
        let recipient = CellId::from_bytes([0x11u8; 32]);
        let data = encode_lock_record(&lid, &recipient, 500);
        let data_b64 = base64::engine::general_purpose::STANDARD.encode(&data);
        let owner_b58 = bs58::encode(LOCK_PROGRAM).into_string();
        let resp = format!(
            r#"{{"jsonrpc":"2.0","result":{{"context":{{"slot":12345}},"value":{{"data":["{data_b64}","base64"],"executable":false,"lamports":1000000,"owner":"{owner_b58}","rentEpoch":18446744073709551615}}}},"id":1}}"#
        );
        let rpc = SolanaJsonRpc::new_plaintext_local_dev(
            "http://127.0.0.1",
            CannedTransport {
                expect_method: "getAccountInfo",
                response: resp,
                seen: std::cell::RefCell::new(None),
            },
        )
        .unwrap();
        let out = rpc
            .get_account_info(&VAULT, Commitment::Finalized)
            .expect("parse real getAccountInfo shape");
        assert_eq!(out.context_slot, 12345);
        let acct = out.account.expect("account present");
        assert_eq!(acct.lamports, 1_000_000);
        assert_eq!(acct.owner, LOCK_PROGRAM);
        assert_eq!(acct.data, data);
        // The request carried the finalized commitment + base64 encoding.
        let sent = rpc.transport.seen.borrow().clone().unwrap();
        assert!(sent.contains("\"finalized\""));
        assert!(sent.contains("\"base64\""));
    }

    #[test]
    fn json_rpc_null_value_is_absent_account() {
        let resp = r#"{"jsonrpc":"2.0","result":{"context":{"slot":7},"value":null},"id":1}"#;
        let rpc = SolanaJsonRpc::new_plaintext_local_dev(
            "http://127.0.0.1",
            CannedTransport {
                expect_method: "getAccountInfo",
                response: resp.to_string(),
                seen: std::cell::RefCell::new(None),
            },
        )
        .unwrap();
        let out = rpc.get_account_info(&VAULT, Commitment::Finalized).unwrap();
        assert!(out.account.is_none());
        assert_eq!(out.context_slot, 7);
    }

    #[test]
    fn json_rpc_surfaces_node_error() {
        let resp = r#"{"jsonrpc":"2.0","error":{"code":-32602,"message":"Invalid"},"id":1}"#;
        let rpc = SolanaJsonRpc::new_plaintext_local_dev(
            "http://127.0.0.1",
            CannedTransport {
                expect_method: "getSlot",
                response: resp.to_string(),
                seen: std::cell::RefCell::new(None),
            },
        )
        .unwrap();
        let err = rpc.get_slot(Commitment::Finalized).unwrap_err();
        assert!(matches!(err, RpcError::Rpc { code: -32602, .. }));
    }

    #[test]
    fn dechunk_reassembles_chunked_body() {
        // "Wiki" + "pedia" in two chunks (RFC 7230 example shape).
        let chunked = b"4\r\nWiki\r\n5\r\npedia\r\n0\r\n\r\n";
        assert_eq!(dechunk(chunked).unwrap(), b"Wikipedia");
    }

    // ---- the relayer watch→verify gates over the mock chain ----------------

    #[test]
    fn relayer_observes_finalized_lock() {
        let recipient = CellId::from_bytes([0x11u8; 32]);
        let mut rpc = MockSolanaRpc::new(100, 105, 110);
        rpc.insert_finalized(
            VAULT,
            MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id(1), recipient, 500),
        );
        let relayer = SolanaRelayer::new(config(), rpc);
        let observed = relayer
            .observe_vault_lock()
            .expect("finalized lock observed");
        assert_eq!(observed.amount, 500);
        assert_eq!(observed.recipient, recipient);
        assert_eq!(observed.lock_id, lock_id(1));
        assert_eq!(observed.trust, LockProofTrust::StructureOnly);
        assert_eq!(observed.finalized_slot, 100);
        // The nullifier matches the canonical derivation the committed mint keys on.
        assert_eq!(observed.nullifier, lock_nullifier(&SPL_MINT, &lock_id(1)));
    }

    #[test]
    fn relayer_refuses_unfinalized_lock() {
        let recipient = CellId::from_bytes([0x11u8; 32]);
        let mut rpc = MockSolanaRpc::new(100, 105, 110);
        // The lock is visible at confirmed but NOT finalized — must be refused.
        rpc.insert_confirmed_only(
            VAULT,
            MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id(2), recipient, 500),
        );
        let relayer = SolanaRelayer::new(config(), rpc);
        assert_eq!(
            relayer.observe_vault_lock().unwrap_err(),
            RelayerError::NotFinalized
        );
    }

    #[test]
    fn relayer_refuses_unescrowed_lock() {
        // A finalized account that exists on Solana but is owned by an ATTACKER
        // program (not the bridge lock program) — the self-asserted-blob attack.
        let recipient = CellId::from_bytes([0x11u8; 32]);
        let attacker_program = [0x99u8; 32];
        let mut rpc = MockSolanaRpc::new(100, 105, 110);
        rpc.insert_finalized(
            VAULT,
            MockSolanaRpc::lock_account(attacker_program, 1_000_000, 0, lock_id(3), recipient, 500),
        );
        let relayer = SolanaRelayer::new(config(), rpc);
        assert_eq!(
            relayer.observe_vault_lock().unwrap_err(),
            RelayerError::NotBridgeVault
        );
    }

    #[test]
    fn relayer_refuses_wrong_vault_pubkey() {
        // The lock record is finalized and program-owned, but at a DIFFERENT
        // account than the configured vault — refused (escrow-to-vault binding).
        let recipient = CellId::from_bytes([0x11u8; 32]);
        let other_account = [0x33u8; 32];
        let mut rpc = MockSolanaRpc::new(100, 105, 110);
        rpc.insert_finalized(
            other_account,
            MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id(4), recipient, 500),
        );
        let relayer = SolanaRelayer::new(config(), rpc);
        assert_eq!(
            relayer.observe_lock_at(&other_account).unwrap_err(),
            RelayerError::NotBridgeVault
        );
    }

    #[test]
    fn relayer_refuses_absent_vault() {
        let rpc = MockSolanaRpc::new(100, 105, 110);
        let relayer = SolanaRelayer::new(config(), rpc);
        assert_eq!(
            relayer.observe_vault_lock().unwrap_err(),
            RelayerError::NotFinalized
        );
    }

    #[test]
    fn relayer_refuses_above_max() {
        let recipient = CellId::from_bytes([0x11u8; 32]);
        let mut rpc = MockSolanaRpc::new(100, 105, 110);
        rpc.insert_finalized(
            VAULT,
            MockSolanaRpc::lock_account(
                LOCK_PROGRAM,
                1_000_000,
                0,
                lock_id(5),
                recipient,
                9_999_999,
            ),
        );
        let relayer = SolanaRelayer::new(config(), rpc);
        assert!(matches!(
            relayer.observe_vault_lock().unwrap_err(),
            RelayerError::Proof(LockProofError::AboveMax)
        ));
    }

    #[test]
    fn scan_program_finds_finalized_locks() {
        let recipient = CellId::from_bytes([0x11u8; 32]);
        let mut rpc = MockSolanaRpc::new(100, 105, 110);
        rpc.insert_finalized(
            VAULT,
            MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id(6), recipient, 500),
        );
        // An attacker-owned account is NOT returned by a scan keyed on the lock
        // program, and even if observed would fail the vault binding.
        rpc.insert_finalized(
            [0x44u8; 32],
            MockSolanaRpc::lock_account([0x99u8; 32], 1_000_000, 0, lock_id(7), recipient, 500),
        );
        let relayer = SolanaRelayer::new(config(), rpc);
        let results = relayer.scan_program_locks().expect("scan");
        // Only the program-owned vault account is scanned.
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].as_ref().unwrap().lock_id, lock_id(6));
    }
}
