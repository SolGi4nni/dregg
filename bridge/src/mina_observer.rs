//! `mina_observer`: the **live off-chain Mina observer** for the settlement loop.
//!
//! This is the Mina-direction twin of [`crate::midnight_observer`] /
//! [`crate::solana_relayer`]: it turns the library-only Mina settlement state
//! machine ([`crate::mina`]) into a watching service that confirms an outbound
//! dregg→Mina settlement landed on a genuinely *finalized* Mina block — instead of
//! trusting a relayer's ack. ("For old time's sake" — the dregg↔Mina bridge made
//! real off-chain.)
//!
//! It speaks the **real Mina GraphQL** over an injected byte-pipe (the same
//! [`crate::solana_relayer::JsonRpcTransport`] seam — Mina GraphQL is a JSON `POST
//! {query}`):
//!
//! 1. **watches** the canonical chain via `bestChain` (the tip + the confirmation
//!    depth) and reads the dregg federation zkApp's settled state via
//!    `account(publicKey){ zkappState }`,
//! 2. **verifies** finality — Mina's Ouroboros Samasika gives probabilistic
//!    finality with depth: a settlement is accepted only once the canonical tip is
//!    `confirmation_depth` blocks past the height the settlement was submitted at
//!    (`StateAdvance.submitted_at`); a settlement still within `confirmation_depth`
//!    of the tip is REFUSED (it could still be re-orged),
//! 3. **confirms** the settlement by checking the zkApp's on-chain `provenRoot`
//!    (decoded from the app-state Fields) equals the dregg root we settled — so a
//!    forged/wrong on-chain state is refused.
//!
//! # The trust boundary (named precisely)
//!
//! A plain GraphQL endpoint exposes the canonical chain + account state at a
//! confirmation depth but NOT the Ouroboros VRF/ledger proofs a light client would
//! need. So the observer's verify is `StructureOnly`-grade over the real
//! depth-finalized state: a *re-executing validator that trusts the node's
//! canonical chain* accepts it. The fully-trustless path (a Mina ledger/consensus
//! proof verified in-circuit) is the mainnet/in-circuit route — the circuit
//! swarm's VK-epoch, NOT this module.

use crate::solana_relayer::{JsonRpcTransport, RpcError};

// ===========================================================================
// The chain view the observer needs (the `MinaRpc` seam)
// ===========================================================================

/// One block on Mina's canonical chain, as `bestChain` returns it. Carries just
/// the fields the observer's finality gate needs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaBlock {
    /// The block's state hash (Base58Check), the chain identity.
    pub state_hash: String,
    /// The block height (`protocolState.consensusState.blockHeight`).
    pub block_height: u64,
    /// The parent block's state hash.
    pub parent_state_hash: String,
}

/// A dregg federation zkApp account's settled state, as `account(publicKey)`
/// returns it: the 8 app-state Fields (each a decimal-string field element).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaZkappAccount {
    /// The 8 zkApp app-state Fields (decimal strings over GraphQL). The dregg
    /// `provenRoot` is encoded across `app_state[0]` (low 128 bits) and
    /// `app_state[1]` (high 128 bits) — see [`decode_root_from_fields`].
    pub app_state: Vec<String>,
}

/// The observer's view of the Mina chain. A real GraphQL client
/// ([`MinaGraphQlRpc`]) and the in-memory test double ([`MockMinaRpc`]) both
/// implement it; the observer is generic over it so the watch→verify loop is
/// tested without a network.
pub trait MinaRpc {
    /// `bestChain(maxLength: n)` — the canonical chain tip-ward (the LAST element
    /// is the tip). Used for the finality-depth gate.
    fn best_chain(&self, max_length: u32) -> Result<Vec<MinaBlock>, RpcError>;

    /// `account(publicKey: pk){ zkappState }` — the zkApp's current app-state
    /// Fields (absent / not-a-zkApp ⟹ `None`).
    fn zkapp_account(&self, public_key: &str) -> Result<Option<MinaZkappAccount>, RpcError>;
}

// ===========================================================================
// proven-root <-> app-state Field encoding
// ===========================================================================

/// Encode a 32-byte dregg proven root into the two app-state Fields a dregg
/// federation zkApp stores it in: `field[0]` = the low 16 bytes (a 128-bit value,
/// well within Mina's ~254-bit Field), `field[1]` = the high 16 bytes. Returned as
/// decimal strings (the GraphQL wire form). The inverse is
/// [`decode_root_from_fields`].
pub fn encode_root_to_fields(root: &[u8; 32]) -> [String; 2] {
    let mut high = [0u8; 16];
    high.copy_from_slice(&root[0..16]);
    let mut low = [0u8; 16];
    low.copy_from_slice(&root[16..32]);
    [
        u128::from_be_bytes(low).to_string(),
        u128::from_be_bytes(high).to_string(),
    ]
}

/// Decode a 32-byte dregg proven root from the two app-state Field decimal
/// strings (`low`, `high`). Each must be a `u128` (a 128-bit Field half); a value
/// that does not parse as `u128` is rejected.
pub fn decode_root_from_fields(low: &str, high: &str) -> Result<[u8; 32], ObserveError> {
    let low_v: u128 = low.parse().map_err(|_| ObserveError::MalformedZkappState {
        reason: format!("app_state[0] (low half) is not a u128 Field: `{low}`"),
    })?;
    let high_v: u128 = high
        .parse()
        .map_err(|_| ObserveError::MalformedZkappState {
            reason: format!("app_state[1] (high half) is not a u128 Field: `{high}`"),
        })?;
    let mut root = [0u8; 32];
    root[0..16].copy_from_slice(&high_v.to_be_bytes());
    root[16..32].copy_from_slice(&low_v.to_be_bytes());
    Ok(root)
}

// ===========================================================================
// The real GraphQL client (real Mina GraphQL over an injected byte-pipe)
// ===========================================================================

/// A real Mina GraphQL client: it builds the genuine `bestChain` / `account`
/// queries and parses the genuine response shapes (decimal-string heights and
/// Fields), delegating the actual bytes to an injected [`JsonRpcTransport`] (the
/// same seam the Solana relayer ships — Mina GraphQL is a JSON `POST {query}`).
pub struct MinaGraphQlRpc<T: JsonRpcTransport> {
    /// The GraphQL endpoint, e.g. `http://127.0.0.1:3085/graphql` or a provider.
    pub url: String,
    transport: T,
}

impl<T: JsonRpcTransport> MinaGraphQlRpc<T> {
    /// Build a client for `url` over `transport`.
    pub fn new(url: impl Into<String>, transport: T) -> Self {
        Self {
            url: url.into(),
            transport,
        }
    }

    fn query(&self, query: &str) -> Result<serde_json::Value, RpcError> {
        let req = serde_json::json!({ "query": query });
        let body = serde_json::to_string(&req).map_err(|e| RpcError::Decode(e.to_string()))?;
        let resp = self.transport.post(&self.url, &body)?;
        let v: serde_json::Value =
            serde_json::from_str(&resp).map_err(|e| RpcError::Decode(e.to_string()))?;
        // GraphQL surfaces errors in a top-level `errors` array.
        if let Some(errs) = v.get("errors").and_then(|e| e.as_array()) {
            let message = errs
                .first()
                .and_then(|e| e.get("message"))
                .and_then(|m| m.as_str())
                .unwrap_or("graphql error")
                .to_string();
            return Err(RpcError::Rpc { code: 0, message });
        }
        v.get("data")
            .cloned()
            .ok_or_else(|| RpcError::Decode("missing `data`".into()))
    }
}

impl<T: JsonRpcTransport> MinaRpc for MinaGraphQlRpc<T> {
    fn best_chain(&self, max_length: u32) -> Result<Vec<MinaBlock>, RpcError> {
        let q = format!(
            "{{ bestChain(maxLength: {max_length}) {{ stateHash protocolState {{ \
             previousStateHash consensusState {{ blockHeight }} }} }} }}"
        );
        let data = self.query(&q)?;
        let arr = data
            .get("bestChain")
            .and_then(|x| x.as_array())
            .ok_or_else(|| RpcError::Decode("bestChain".into()))?;
        arr.iter()
            .map(|b| {
                let state_hash = b
                    .get("stateHash")
                    .and_then(|x| x.as_str())
                    .ok_or_else(|| RpcError::Decode("block.stateHash".into()))?
                    .to_string();
                let protocol = b
                    .get("protocolState")
                    .ok_or_else(|| RpcError::Decode("block.protocolState".into()))?;
                let parent_state_hash = protocol
                    .get("previousStateHash")
                    .and_then(|x| x.as_str())
                    .unwrap_or("")
                    .to_string();
                // blockHeight is a decimal STRING in Mina GraphQL.
                let height_str = protocol
                    .get("consensusState")
                    .and_then(|c| c.get("blockHeight"))
                    .and_then(|x| x.as_str())
                    .ok_or_else(|| RpcError::Decode("block.blockHeight".into()))?;
                let block_height = height_str
                    .parse::<u64>()
                    .map_err(|e| RpcError::Decode(format!("blockHeight `{height_str}`: {e}")))?;
                Ok(MinaBlock {
                    state_hash,
                    block_height,
                    parent_state_hash,
                })
            })
            .collect()
    }

    fn zkapp_account(&self, public_key: &str) -> Result<Option<MinaZkappAccount>, RpcError> {
        let q = format!("{{ account(publicKey: \"{public_key}\") {{ zkappState }} }}");
        let data = self.query(&q)?;
        let account = match data.get("account") {
            Some(serde_json::Value::Null) | None => return Ok(None),
            Some(a) => a,
        };
        let app_state = match account.get("zkappState") {
            Some(serde_json::Value::Null) | None => return Ok(None),
            Some(serde_json::Value::Array(a)) => a
                .iter()
                .map(|f| {
                    f.as_str()
                        .map(|s| s.to_string())
                        .ok_or_else(|| RpcError::Decode("zkappState[i] not a string".into()))
                })
                .collect::<Result<Vec<_>, _>>()?,
            _ => return Err(RpcError::Decode("zkappState shape".into())),
        };
        Ok(Some(MinaZkappAccount { app_state }))
    }
}

// ===========================================================================
// The observer: watch bestChain → verify (finality depth) → confirm settlement
// ===========================================================================

/// The observer configuration: which zkApp to watch and how deep finality is.
#[derive(Clone, Debug)]
pub struct MinaObserverConfig {
    /// The dregg federation zkApp address (Base58Check `B62...`).
    pub zkapp_address: String,
    /// The number of canonical blocks past a settlement's submitted height before
    /// it is treated as finalized (Ouroboros Samasika depth — e.g. `~290` for
    /// full finality on mainnet; smaller for fast devnets/tests).
    pub confirmation_depth: u64,
    /// How many blocks of `bestChain` to request (must be ≥ 1; only the tip
    /// height is consumed for the depth gate).
    pub best_chain_length: u32,
}

/// A confirmed, depth-finalized dregg settlement observed on Mina — the observer's
/// output. It witnesses that the dregg `proven_root` is the zkApp's on-chain state
/// at a genuinely finalized canonical tip.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedMinaSettlement {
    /// The dregg proven root read from the zkApp's app-state Fields.
    pub proven_root: [u8; 32],
    /// The canonical tip height when observed.
    pub tip_height: u64,
    /// The height the settlement was submitted at (`StateAdvance.submitted_at`).
    pub submitted_height: u64,
    /// The confirmation depth achieved (`tip_height - submitted_height`).
    pub depth: u64,
}

/// Why the observer refused to confirm a settlement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ObserveError {
    /// A GraphQL/RPC call failed.
    Rpc(RpcError),
    /// `bestChain` returned no blocks (cannot read a tip).
    EmptyChain,
    /// The settlement is not yet `confirmation_depth` blocks deep — still re-orgable.
    NotFinalized {
        /// The canonical tip height.
        tip_height: u64,
        /// The settlement's submitted height.
        submitted_height: u64,
        /// The required depth.
        required_depth: u64,
    },
    /// The zkApp account was absent or not a zkApp (no app state).
    ZkappNotFound,
    /// The zkApp app state was malformed (wrong arity or a non-Field value).
    MalformedZkappState {
        /// Why.
        reason: String,
    },
    /// The zkApp's on-chain root does not equal the dregg root we settled — a
    /// forged/wrong settlement state is refused.
    RootMismatch {
        /// The root read from Mina.
        on_chain: [u8; 32],
        /// The dregg root we expected.
        expected: [u8; 32],
    },
}

impl std::fmt::Display for ObserveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Rpc(e) => write!(f, "{e}"),
            Self::EmptyChain => write!(f, "bestChain returned no blocks"),
            Self::NotFinalized {
                tip_height,
                submitted_height,
                required_depth,
            } => write!(
                f,
                "settlement at height {submitted_height} not finalized: tip {tip_height} is only \
                 {} deep (need {required_depth})",
                tip_height.saturating_sub(*submitted_height)
            ),
            Self::ZkappNotFound => write!(f, "zkApp account not found / not a zkApp"),
            Self::MalformedZkappState { reason } => write!(f, "malformed zkApp state: {reason}"),
            Self::RootMismatch { .. } => {
                write!(
                    f,
                    "zkApp on-chain root does not match the settled dregg root"
                )
            }
        }
    }
}

impl std::error::Error for ObserveError {}

impl From<RpcError> for ObserveError {
    fn from(e: RpcError) -> Self {
        Self::Rpc(e)
    }
}

/// The live off-chain Mina observer over a [`MinaRpc`] connection.
pub struct MinaObserver<R: MinaRpc> {
    /// The observer configuration (zkApp, finality depth).
    pub config: MinaObserverConfig,
    /// The chain connection.
    pub rpc: R,
}

impl<R: MinaRpc> MinaObserver<R> {
    /// Build an observer for `config` over `rpc`.
    pub fn new(config: MinaObserverConfig, rpc: R) -> Self {
        Self { config, rpc }
    }

    /// **Confirm an outbound settlement landed on a finalized Mina block.**
    ///
    /// `expected_root` is the dregg root the settlement advanced to;
    /// `submitted_height` is the Mina height the settlement was submitted at
    /// (`StateAdvance.submitted_at`). Reads the canonical tip, gates finality on
    /// `tip - submitted ≥ confirmation_depth`, reads the zkApp's settled root, and
    /// checks it equals `expected_root`. Returns the [`ObservedMinaSettlement`] or
    /// the precise refusal (un-finalized / root mismatch / absent zkApp).
    pub fn observe_settlement(
        &self,
        expected_root: &[u8; 32],
        submitted_height: u64,
    ) -> Result<ObservedMinaSettlement, ObserveError> {
        // (1) read the canonical tip height.
        let chain = self.rpc.best_chain(self.config.best_chain_length.max(1))?;
        let tip_height = chain
            .iter()
            .map(|b| b.block_height)
            .max()
            .ok_or(ObserveError::EmptyChain)?;

        // (2) finality: the settlement must be confirmation_depth blocks deep. A
        //     settlement still within the depth window could be re-orged — refused.
        let depth = tip_height.saturating_sub(submitted_height);
        if depth < self.config.confirmation_depth {
            return Err(ObserveError::NotFinalized {
                tip_height,
                submitted_height,
                required_depth: self.config.confirmation_depth,
            });
        }

        // (3) read the zkApp's settled root from its app-state Fields.
        let account = self
            .rpc
            .zkapp_account(&self.config.zkapp_address)?
            .ok_or(ObserveError::ZkappNotFound)?;
        if account.app_state.len() < 2 {
            return Err(ObserveError::MalformedZkappState {
                reason: format!(
                    "expected ≥ 2 app-state Fields (root low/high), got {}",
                    account.app_state.len()
                ),
            });
        }
        let on_chain = decode_root_from_fields(&account.app_state[0], &account.app_state[1])?;

        // (4) confirm it equals the dregg root we settled — a forged/wrong state
        //     is refused.
        if &on_chain != expected_root {
            return Err(ObserveError::RootMismatch {
                on_chain,
                expected: *expected_root,
            });
        }

        Ok(ObservedMinaSettlement {
            proven_root: on_chain,
            tip_height,
            submitted_height,
            depth,
        })
    }
}

// ===========================================================================
// In-memory test double (the dev observer harness + tests)
// ===========================================================================

/// An in-memory [`MinaRpc`] for tests and the dev observer harness: it models a
/// canonical chain at a tip height plus a zkApp account, so the observer's
/// finality-depth gate (and an un-finalized refusal) is exercised without a node.
#[cfg(any(test, feature = "test-utils"))]
#[derive(Clone, Debug, Default)]
pub struct MockMinaRpc {
    chain: Vec<MinaBlock>,
    accounts: std::collections::BTreeMap<String, MinaZkappAccount>,
}

#[cfg(any(test, feature = "test-utils"))]
impl MockMinaRpc {
    /// A mock whose canonical chain runs `1..=tip_height` (the last block is the
    /// tip). Heights are what the depth gate consumes.
    pub fn at_tip(tip_height: u64) -> Self {
        let chain = (1..=tip_height)
            .map(|h| MinaBlock {
                state_hash: format!("B62hash{h}"),
                block_height: h,
                parent_state_hash: if h > 1 {
                    format!("B62hash{}", h - 1)
                } else {
                    String::new()
                },
            })
            .collect();
        Self {
            chain,
            accounts: std::collections::BTreeMap::new(),
        }
    }

    /// Set the zkApp's settled root (encoded across the two app-state Fields).
    pub fn set_zkapp_root(&mut self, public_key: &str, root: &[u8; 32]) -> &mut Self {
        let [low, high] = encode_root_to_fields(root);
        // Pad to 8 app-state Fields like a real zkApp account.
        let mut app_state = vec![low, high];
        app_state.resize(8, "0".to_string());
        self.accounts
            .insert(public_key.to_string(), MinaZkappAccount { app_state });
        self
    }

    /// Set a raw zkApp account (for malformed-state tests).
    pub fn set_zkapp_account(&mut self, public_key: &str, account: MinaZkappAccount) -> &mut Self {
        self.accounts.insert(public_key.to_string(), account);
        self
    }
}

#[cfg(any(test, feature = "test-utils"))]
impl MinaRpc for MockMinaRpc {
    fn best_chain(&self, max_length: u32) -> Result<Vec<MinaBlock>, RpcError> {
        let n = (max_length as usize).min(self.chain.len());
        Ok(self.chain[self.chain.len() - n..].to_vec())
    }

    fn zkapp_account(&self, public_key: &str) -> Result<Option<MinaZkappAccount>, RpcError> {
        Ok(self.accounts.get(public_key).cloned())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ZKAPP: &str = "B62qrPN5Y5yq8kGE3FbVKbGTdTAJNdtNtS5vH1e3jX5uFtkKXb7x3zX";

    fn config(depth: u64) -> MinaObserverConfig {
        MinaObserverConfig {
            zkapp_address: ZKAPP.to_string(),
            confirmation_depth: depth,
            best_chain_length: 16,
        }
    }

    fn root(n: u8) -> [u8; 32] {
        let mut r = [n; 32];
        // Make the two halves distinct so the high/low split is genuinely tested.
        r[0] = n.wrapping_add(1);
        r[31] = n.wrapping_add(2);
        r
    }

    #[test]
    fn root_field_encoding_round_trips() {
        let r = root(0x5A);
        let [low, high] = encode_root_to_fields(&r);
        let decoded = decode_root_from_fields(&low, &high).expect("decode");
        assert_eq!(decoded, r, "root survives the app-state Field split");
    }

    #[test]
    fn observer_confirms_finalized_settlement() {
        let settled = root(0x11);
        let mut rpc = MockMinaRpc::at_tip(1000);
        rpc.set_zkapp_root(ZKAPP, &settled);
        // Submitted at height 700, tip 1000 → depth 300 ≥ 290.
        let observer = MinaObserver::new(config(290), rpc);
        let observed = observer
            .observe_settlement(&settled, 700)
            .expect("finalized settlement confirmed");
        assert_eq!(observed.proven_root, settled);
        assert_eq!(observed.tip_height, 1000);
        assert_eq!(observed.depth, 300);
    }

    #[test]
    fn observer_refuses_unfinalized_settlement() {
        let settled = root(0x22);
        let mut rpc = MockMinaRpc::at_tip(1000);
        rpc.set_zkapp_root(ZKAPP, &settled);
        // Submitted at height 900, tip 1000 → depth 100 < 290.
        let observer = MinaObserver::new(config(290), rpc);
        assert!(matches!(
            observer.observe_settlement(&settled, 900).unwrap_err(),
            ObserveError::NotFinalized {
                tip_height: 1000,
                submitted_height: 900,
                required_depth: 290,
            }
        ));
    }

    #[test]
    fn observer_refuses_root_mismatch() {
        // The zkApp holds a DIFFERENT root than the one we settled — refused.
        let settled = root(0x33);
        let forged = root(0x44);
        let mut rpc = MockMinaRpc::at_tip(1000);
        rpc.set_zkapp_root(ZKAPP, &forged);
        let observer = MinaObserver::new(config(290), rpc);
        assert!(matches!(
            observer.observe_settlement(&settled, 700).unwrap_err(),
            ObserveError::RootMismatch { .. }
        ));
    }

    #[test]
    fn observer_refuses_absent_zkapp() {
        let settled = root(0x55);
        let rpc = MockMinaRpc::at_tip(1000); // no zkApp account set
        let observer = MinaObserver::new(config(290), rpc);
        assert_eq!(
            observer.observe_settlement(&settled, 700).unwrap_err(),
            ObserveError::ZkappNotFound
        );
    }

    // ---- the GraphQL wire codec (real Mina shapes) --------------------------

    struct CannedTransport {
        response: String,
        seen: std::cell::RefCell<Option<String>>,
    }

    impl JsonRpcTransport for CannedTransport {
        fn post(&self, _url: &str, body: &str) -> Result<String, RpcError> {
            *self.seen.borrow_mut() = Some(body.to_string());
            Ok(self.response.clone())
        }
    }

    #[test]
    fn graphql_parses_real_best_chain_shape() {
        // A genuine Mina bestChain response: stateHash + nested consensusState
        // blockHeight as a STRING.
        let resp = r#"{"data":{"bestChain":[
            {"stateHash":"B62hashA","protocolState":{"previousStateHash":"B62hashZ","consensusState":{"blockHeight":"999"}}},
            {"stateHash":"B62hashB","protocolState":{"previousStateHash":"B62hashA","consensusState":{"blockHeight":"1000"}}}
        ]}}"#;
        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            CannedTransport {
                response: resp.to_string(),
                seen: std::cell::RefCell::new(None),
            },
        );
        let chain = rpc.best_chain(2).expect("parse real bestChain shape");
        assert_eq!(chain.len(), 2);
        assert_eq!(chain[1].block_height, 1000);
        assert_eq!(chain[1].state_hash, "B62hashB");
        let sent = rpc.transport.seen.borrow().clone().unwrap();
        assert!(sent.contains("bestChain"));
        assert!(sent.contains("blockHeight"));
    }

    #[test]
    fn graphql_parses_real_zkapp_account_shape() {
        let settled = root(0x6E);
        let [low, high] = encode_root_to_fields(&settled);
        let resp = format!(
            r#"{{"data":{{"account":{{"zkappState":["{low}","{high}","0","0","0","0","0","0"]}}}}}}"#
        );
        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            CannedTransport {
                response: resp,
                seen: std::cell::RefCell::new(None),
            },
        );
        let acct = rpc
            .zkapp_account(ZKAPP)
            .expect("parse")
            .expect("account present");
        assert_eq!(acct.app_state.len(), 8);
        let decoded = decode_root_from_fields(&acct.app_state[0], &acct.app_state[1]).unwrap();
        assert_eq!(
            decoded, settled,
            "the zkApp root decodes from the real shape"
        );
    }

    #[test]
    fn graphql_null_account_is_none() {
        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            CannedTransport {
                response: r#"{"data":{"account":null}}"#.to_string(),
                seen: std::cell::RefCell::new(None),
            },
        );
        assert!(rpc.zkapp_account(ZKAPP).unwrap().is_none());
    }

    #[test]
    fn graphql_surfaces_errors() {
        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            CannedTransport {
                response: r#"{"errors":[{"message":"bad query"}]}"#.to_string(),
                seen: std::cell::RefCell::new(None),
            },
        );
        let err = rpc.best_chain(2).unwrap_err();
        assert!(matches!(err, RpcError::Rpc { .. }));
    }

    /// End-to-end over the GraphQL client: a real bestChain + zkApp account shape
    /// drives the observer to a confirmed, depth-finalized settlement.
    #[test]
    fn observer_round_trip_over_graphql_client() {
        let settled = root(0x7F);
        let [low, high] = encode_root_to_fields(&settled);

        struct Router {
            best_chain: String,
            account: String,
        }
        impl JsonRpcTransport for Router {
            fn post(&self, _url: &str, body: &str) -> Result<String, RpcError> {
                if body.contains("bestChain") {
                    Ok(self.best_chain.clone())
                } else {
                    Ok(self.account.clone())
                }
            }
        }

        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            Router {
                best_chain: r#"{"data":{"bestChain":[{"stateHash":"B62tip","protocolState":{"previousStateHash":"B62p","consensusState":{"blockHeight":"1000"}}}]}}"#.to_string(),
                account: format!(
                    r#"{{"data":{{"account":{{"zkappState":["{low}","{high}","0","0","0","0","0","0"]}}}}}}"#
                ),
            },
        );
        let observer = MinaObserver::new(config(290), rpc);
        let observed = observer
            .observe_settlement(&settled, 700)
            .expect("graphql-driven settlement confirmed");
        assert_eq!(observed.proven_root, settled);
        assert_eq!(observed.depth, 300);
    }
}
