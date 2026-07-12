//! # The federation / local-submit leg — a minted grain turn lands on a REAL node.
//!
//! The served path ([`crate::AgentPlatform::drive_serving`]) already mints every
//! admitted agent action as a genuine committed executor turn (the R2 weld). But
//! `grain-turn`'s [`grain_turn::ToolGatewayMinter`] commits those turns to its OWN
//! throwaway in-process `AgentRuntime` — a fresh ledger per drive that no third
//! party can see. So a renter still has to trust *this host* that the turn
//! happened.
//!
//! This module closes that residual: a [`LocalNode`] is a locally-runnable dregg
//! node's two ground-truth surfaces —
//!
//! * its **world-state ledger** (`Arc<Mutex<Ledger>>`, shared INTO the minter, so
//!   the grain turn is executed by a real [`dregg_turn::TurnExecutor`] straight onto
//!   the node's ledger), and
//! * its **finalized receipt log** (the node's committed, linked receipt chain a
//!   light client verifies — [`dregg_turn::verify_receipt_chain`]).
//!
//! [`NodeMinter`] is the platform's node-backed [`GrainTurnMinter`]: it mints
//! exactly the same witnessed kernel turn `grain-turn` does (reusing
//! [`grain_turn::action_commit`] + the `CONSUMED`/`HEAP_ROOT`/`ACTION` slot layout,
//! so the committed turn shape is byte-identical and [`crate::AgentPlatform::verify_r2`]
//! still passes) and then **lands** the committed receipt on the node's finalized
//! log through [`LocalNode::land`] — the node's submit-record + finalization gate.
//! `land` REJECTS any receipt that does not link/extend the log (a forged or
//! tampered turn), fail-closed.
//!
//! ## Honest scope — what is REAL vs. the deploy step
//!
//! REAL and exercised here: the minted turn is executed by the genuine kernel
//! executor onto a real node's ledger, recorded on the node's finalized receipt
//! chain, and confirmed landed + light-client-verifiable — cross-node-verifiable
//! (the chain + ledger are exportable ground truth), not "trust this process's
//! private runtime." The default node is IN-PROCESS: a locally-hosted node you can
//! actually use, driven by the same `TurnExecutor` + receipt-chain the node daemon's
//! `POST /turns/submit` handler runs at the library level.
//!
//! The DEPLOY step (operational, NOT done here): pointing the platform at an
//! *external* federation node URL (a homelab node) over HTTP and forwarding the
//! finalized turn to its ingress — see [`crate::AgentPlatform::node_url`]. That leg
//! also carries full multi-node blocklace consensus finalization; the in-process
//! node models the executor + receipt-log half a single node runs locally.

use std::collections::HashSet;
use std::sync::{Arc, Mutex, RwLock};

use dregg_agent::agent::GrainTurnMinter;
use dregg_cell::program::field_from_u64;
use dregg_cell::{Cell, Ledger};
use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, CALLS_MADE_SLOT, Effect, SdkError, ToolGateway, ToolGrant,
};
use dregg_turn::TurnReceipt;
use grain_turn::{ACTION_SLOT, ATTESTATION_SLOT, CONSUMED_SLOT, HEAP_ROOT_SLOT, action_commit};

// The grain mandate parameters — MIRROR `grain-turn`'s private constants exactly, so
// the node-backed minter presents the identical cap-gated worker + mandate the
// shipped R2 weld does (same tool id, same far-out deadline, same scoped verb).
const GRAIN_TOOL_ID: i64 = 1;
const GRAIN_DEADLINE: i64 = i64::MAX / 2;
const GRAIN_TOOL_METHOD: &str = "grain.turn";

/// Why the local node refused to land a submitted turn on its finalized log.
#[derive(Debug)]
pub enum NodeError {
    /// The executor refused to commit the turn (over-rate / insolvent / invalid) —
    /// nothing was minted, so nothing lands.
    Mint(String),
    /// The receipt does not link/extend the node's finalized log: a genesis receipt
    /// carrying a predecessor, a broken hash chain, an agent mismatch, or a
    /// state-continuity break. The node's fail-closed finalization gate — a forged
    /// or tampered turn is rejected here.
    Rejected(String),
}

impl std::fmt::Display for NodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NodeError::Mint(m) => write!(f, "mint refused: {m}"),
            NodeError::Rejected(m) => write!(f, "node rejected turn: {m}"),
        }
    }
}

impl std::error::Error for NodeError {}

/// A locally-runnable dregg node's ground truth: the world-state **ledger** the
/// grain turn is executed onto, and the **finalized receipt log** (the linked,
/// light-client-verifiable chain) it is recorded on.
///
/// Cheap to [`Clone`] — the ledger and log are shared `Arc` handles, so a clone the
/// minter holds and a clone the platform reads/verifies name the SAME node.
#[derive(Clone)]
pub struct LocalNode {
    domain: String,
    /// The node's world-state ledger — shared INTO the minter's runtime so the
    /// grain turn commits straight onto it (a real executor turn on the node ledger).
    ledger: Arc<Mutex<Ledger>>,
    /// The node's finalized receipt log — the committed, linked receipt chain a
    /// light client verifies. Grown by [`land`](Self::land), the finalization gate.
    log: Arc<Mutex<Vec<TurnReceipt>>>,
    /// An O(1)-membership index of the finalized log's `turn_hash`es, maintained in
    /// lockstep with [`land`](Self::land). It carries no ground truth the log does not
    /// (every entry mirrors a receipt on `log`); it only lets [`contains`](Self::contains)
    /// — the hot membership check three verify paths (`verify_landed`, `audit_fund`,
    /// `grain-verify`) loop over — answer in O(1) instead of scanning the whole log.
    hashes: Arc<Mutex<HashSet<[u8; 32]>>>,
}

impl LocalNode {
    /// A fresh local node with an empty ledger + empty finalized log.
    pub fn new(domain: &str) -> LocalNode {
        LocalNode {
            domain: domain.to_string(),
            ledger: Arc::new(Mutex::new(Ledger::new())),
            log: Arc::new(Mutex::new(Vec::new())),
            hashes: Arc::new(Mutex::new(HashSet::new())),
        }
    }

    /// The node's world-state ledger handle (shared into the minter's runtime).
    pub fn ledger(&self) -> Arc<Mutex<Ledger>> {
        self.ledger.clone()
    }

    /// The node's domain.
    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// **Submit-record + finalize** a committed turn's receipt onto the node's
    /// finalized log — the node's fail-closed finalization gate. The receipt must
    /// LINK the log: a genesis receipt (empty log) may carry no predecessor, and any
    /// later receipt must extend the current head (hash chain + same agent + state
    /// continuity — [`dregg_turn::verify_receipt_extends`]). A forged or tampered
    /// receipt that does not link is [`NodeError::Rejected`] and does NOT grow the
    /// chain.
    pub fn land(&self, receipt: TurnReceipt) -> Result<(), NodeError> {
        let mut log = self.log.lock().expect("node log poisoned");
        match log.last() {
            None => {
                if let Some(prev) = receipt.previous_receipt_hash {
                    return Err(NodeError::Rejected(format!(
                        "genesis receipt carries a predecessor {prev:?}"
                    )));
                }
            }
            Some(head) => {
                dregg_turn::verify_receipt_extends(head, &receipt)
                    .map_err(|e| NodeError::Rejected(format!("{e:?}")))?;
            }
        }
        let turn_hash = receipt.turn_hash;
        log.push(receipt);
        // Maintain the membership index under the log lock so `contains` never sees a
        // landed receipt the index is missing (or vice versa).
        self.hashes
            .lock()
            .expect("node hashes poisoned")
            .insert(turn_hash);
        Ok(())
    }

    /// Whether a turn with this `turn_hash` is on the node's finalized log — the
    /// membership check a light client runs to confirm a receipt's link names a turn
    /// the node actually committed.
    pub fn contains(&self, turn_hash: &[u8; 32]) -> bool {
        self.hashes
            .lock()
            .expect("node hashes poisoned")
            .contains(turn_hash)
    }

    /// The number of turns finalized on the node's log.
    pub fn finalized_len(&self) -> usize {
        self.log.lock().expect("node log poisoned").len()
    }

    /// **The light-client verify path**: the node's finalized receipt chain is a
    /// non-empty, unbroken, single-agent, state-continuous chain
    /// ([`dregg_turn::verify_receipt_chain`]). A third party holding this chain
    /// confirms the turns are the node's genuine committed sequence WITHOUT trusting
    /// the host. An empty log verifies vacuously (nothing to check).
    pub fn verify(&self) -> Result<(), NodeError> {
        let log = self.log.lock().expect("node log poisoned");
        if log.is_empty() {
            return Ok(());
        }
        dregg_turn::verify_receipt_chain(&log).map_err(|e| NodeError::Rejected(format!("{e:?}")))
    }

    /// A snapshot of the node's finalized receipt chain — the exportable ground truth
    /// a light client re-verifies offline.
    pub fn chain(&self) -> Vec<TurnReceipt> {
        self.log.lock().expect("node log poisoned").clone()
    }
}

/// **The platform's node-backed [`GrainTurnMinter`]** — mints each admitted action
/// as a genuine committed kernel turn onto a [`LocalNode`]'s ledger (via the same
/// cap-gated [`ToolGateway`] worker + mandate the shipped R2 weld uses) AND lands the
/// committed receipt on the node's finalized log. Unlike `grain-turn`'s per-drive
/// throwaway runtime, one `NodeMinter` persists across a grain's drives: a stable
/// worker cell + an accumulating node ledger + a single-agent finalized chain — a
/// real local node for the grain.
pub struct NodeMinter {
    /// The runtime whose SHARED ledger is the node's ledger (turns commit onto it).
    runtime: AgentRuntime,
    /// The cap-gated worker + its metered `calls_made` counter + the mandate cell —
    /// identical to `grain-turn`'s `ToolGatewayMinter`, on the node ledger.
    gateway: ToolGateway,
    /// The node this minter mints onto + lands receipts on.
    node: LocalNode,
    /// The presentation clock every grain turn is stamped at (the DEADLINE leg is far
    /// out; the RATE leg `calls_made <= budget` is the meter).
    now: i64,
    /// The zkOracle attestation commitment bound onto this minter's turns — a 32-byte
    /// hash of the confined brain's `ZkOracleAttestation`, witnessed at
    /// [`ATTESTATION_SLOT`]. `None` = unattested (the slot stays zero). Set with
    /// [`bind_attestation`](Self::bind_attestation).
    pending_attestation: Option<[u8; 32]>,
}

impl NodeMinter {
    /// Open a node-backed minter on `node`: seed the mandate root cell into the
    /// node's ledger, build a runtime SHARING that ledger, and admit a cap-gated
    /// worker under a rate-`budget` [`ToolGrant`] (the executor's own `calls_made`
    /// `FieldLte` caveat bounds the committed-turn count host-side). Every turn this
    /// mints commits onto `node`'s ledger and lands on `node`'s finalized log.
    pub fn open(node: LocalNode, budget: i64) -> Result<NodeMinter, SdkError> {
        Self::open_signed(node, budget, None, None)
    }

    /// **ROUTE (ii) — open a node-backed minter whose grain turns are HOST-SIGNED.**
    /// Exactly [`open`](Self::open), but when `executor_signing_seed` is `Some`, the
    /// runtime the grain worker mints through carries the host's executor signing key,
    /// so every committed grain-turn receipt is Ed25519-signed over
    /// `canonical_executor_signed_message` — forge-admissible against the host's
    /// executor pubkey. `None` reproduces the legacy UNSIGNED behavior byte-for-byte.
    pub fn open_signed(
        node: LocalNode,
        budget: i64,
        executor_signing_seed: Option<[u8; 32]>,
        owner_pubkey: Option<[u8; 32]>,
    ) -> Result<NodeMinter, SdkError> {
        let mut cclerk = AgentCipherclerk::new();
        let root = cclerk.mint_token(&[0x6au8; 32], node.domain());
        let public_key = cclerk.public_key();
        let ledger = node.ledger();
        // `AgentRuntime::with_ledger` does NOT fund the root cell (unlike `new`), so
        // seed it into the SHARED node ledger exactly as `new` would — the funded
        // source the worker is spawned + metered under.
        {
            let mut l = ledger.lock().expect("node ledger poisoned");
            let root_cell = Cell::with_balance(
                public_key.0,
                *blake3::hash(node.domain().as_bytes()).as_bytes(),
                1_000_000,
            );
            // A fresh node ledger has no such cell; a re-open would (idempotent seed).
            let _ = l.insert_cell(root_cell);
        }
        let mut runtime =
            AgentRuntime::with_ledger(Arc::new(RwLock::new(cclerk)), node.domain(), ledger);
        // ROUTE (ii): install the host executor signing seed BEFORE the worker is
        // spawned (via `ToolGateway::admit`), so the worker `SubAgent` inherits it and
        // its committed grain-turn receipts are signed.
        if let Some(seed) = executor_signing_seed {
            runtime.set_executor_signing_key(seed);
        }
        let grant = ToolGrant {
            tool_id: GRAIN_TOOL_ID,
            rate_limit: budget.max(0),
            deadline: GRAIN_DEADLINE,
            tool_method: GRAIN_TOOL_METHOD.to_string(),
        };
        // Upgrade-safety keystone: when the renter supplied an anchor, stamp the
        // owner-signed envelope onto the grain worker so the host cannot widen its
        // authority over the grain through the executor.
        let gateway = match owner_pubkey {
            // WAVE A / WELD — OWNER LIVENESS: admit the worker enveloped AND register
            // the owner-envelope verifier live on its executor path (the owner can
            // now authorize the Custom-gated Delegate/SetPermissions; the host still
            // cannot forge the owner signature).
            Some(pk) => ToolGateway::admit_enveloped_owned(&runtime, &root, grant, pk)?,
            None => ToolGateway::admit(&runtime, &root, grant)?,
        };
        Ok(NodeMinter {
            runtime,
            gateway,
            node,
            now: 0,
            pending_attestation: None,
        })
    }

    /// The node this minter mints onto (a cheap `Arc`-sharing handle for the platform
    /// to read/verify the finalized chain).
    pub fn node(&self) -> LocalNode {
        self.node.clone()
    }

    /// **Bind a zkOracle attestation commitment onto this minter's turns** — every turn
    /// minted after this call witnesses `commitment` at [`ATTESTATION_SLOT`], so the
    /// turn landed on the node's finalized log commits to "driven by an attested brain."
    /// `commitment` is the canonical hash of the confined brain's `ZkOracleAttestation`
    /// (`deos_hermes::attestation_commitment`); a light client re-verifies the
    /// attestation and confirms its recomputed commitment equals the landed slot.
    pub fn bind_attestation(&mut self, commitment: [u8; 32]) {
        self.pending_attestation = Some(commitment);
    }

    /// The attestation commitment currently bound (witnessed on the next turn), or
    /// `None` if this minter's turns are unattested.
    pub fn bound_attestation(&self) -> Option<[u8; 32]> {
        self.pending_attestation
    }

    /// The attestation commitment WITNESSED on the node's committed grain-turn-cell —
    /// read straight off the finalized ledger state at [`ATTESTATION_SLOT`]. `Some(c)`
    /// once at least one turn has been minted after [`bind_attestation`]; a turn minted
    /// unattested leaves it at the zero default (`Some([0;32])`). This is the
    /// ground-truth a light client checks against the recomputed attestation commitment.
    pub fn attestation_slot(&self) -> Option<[u8; 32]> {
        self.read_slot(ATTESTATION_SLOT)
    }

    /// The number of grain turns committed so far (the on-ledger `calls_made`).
    pub fn calls_made(&self) -> i64 {
        self.gateway.calls_made()
    }

    /// Read a witnessed slot straight off the COMMITTED grain-turn-cell state in the
    /// node's ledger — what the kernel actually committed onto the node.
    pub fn read_slot(&self, index: usize) -> Option<[u8; 32]> {
        let ledger = self.runtime.ledger().lock().ok()?;
        let cell = ledger.get(&self.gateway.worker_cell())?;
        cell.state.fields.get(index).copied()
    }
}

impl GrainTurnMinter for NodeMinter {
    fn mint_turn(
        &mut self,
        label: &str,
        cost: i64,
        consumed_after: i64,
        cell_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        let cell = self.gateway.worker_cell();
        // The SAME witnessed work `grain-turn`'s minter rides on the metered turn:
        // the session's post-draw consumed total, the agent's committed heap root,
        // AND the action commit — so the committed turn witnesses WHAT the action
        // was, byte-identically to the shipped R2 weld.
        let mut work = vec![
            Effect::SetField {
                cell,
                index: CONSUMED_SLOT,
                value: field_from_u64(consumed_after.max(0) as u64),
            },
            Effect::SetField {
                cell,
                index: HEAP_ROOT_SLOT,
                value: cell_root,
            },
            Effect::SetField {
                cell,
                index: ACTION_SLOT,
                value: action_commit(label, cost),
            },
        ];
        // THE FUSION: a bound attestation commitment rides the SAME metered turn — the
        // turn landed on the node's finalized log commits to the confined brain's
        // zkOracle attestation. An unattested turn omits it (slot stays zero).
        if let Some(commitment) = self.pending_attestation {
            work.push(Effect::SetField {
                cell,
                index: ATTESTATION_SLOT,
                value: commitment,
            });
        }
        // The genuine executor turn, committed onto the NODE's ledger. `Err` = the
        // executor refused host-side (over-rate / insolvent) — no draw, no receipt.
        let toolreceipt = self
            .gateway
            .invoke(GRAIN_TOOL_ID, self.now, work)
            .map_err(|e| NodeError::Mint(e.to_string()).to_string())?;
        let receipt = toolreceipt.receipt;
        let turn_hash = receipt.turn_hash;
        // SUBMIT the committed turn onto the node's finalized log — the leg that makes
        // it cross-node-verifiable. The node's finalization gate re-checks the link;
        // a receipt that does not extend the chain is refused (a forged/tampered turn).
        self.node.land(receipt).map_err(|e| e.to_string())?;
        Ok(turn_hash)
    }
}

// Keep the slot binding honest at compile time: `NodeMinter` witnesses on the SAME
// slot indices `grain-turn` reserves. If either side ever renumbers, this fails to
// compile rather than silently minting a differently-shaped (verify_r2-breaking) turn.
const _: () = {
    assert!(CONSUMED_SLOT == 5);
    assert!(HEAP_ROOT_SLOT == 6);
    assert!(ACTION_SLOT == 7);
    assert!(ATTESTATION_SLOT == 8);
    assert!(CALLS_MADE_SLOT == 4);
};
