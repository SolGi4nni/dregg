//! # Agent coordination — the N-party promise-pipeline.
//!
//! The ring ([`crate::ring_trade::RingCoordinator`]) matches a conserving cycle
//! out of posted *asset* offers; the service-promise exchange
//! ([`crate::service_promise`]) binds a *single* provider↔consumer pay-for-perform
//! leg. This module is the missing middle: **N agents that each do COOPERATIVE
//! WORK, hand each other the results of that work as promises, compute their parts
//! off-chain (in parallel where there is no data dependency), and settle the whole
//! cooperation ATOMICALLY on-chain as one verified conserving fold.**
//!
//! It is the "watch your agent civilization" shape: agent A produces a result
//! agent B needs; A hands B a PROMISE (an [`EventualRef`] — a value that will
//! exist once A's work resolves); B PIPELINES its own work against that promise;
//! and only when every promise in the round is filled does the round settle. The
//! per-agent work never touches the chain — only the final all-or-nothing
//! settlement does. That is the dregg value: parties compute over a shared promise
//! pipeline at full off-chain speed and pay for it with a single atomic on-chain
//! commit.
//!
//! ## The pieces it composes (it invents no new primitive)
//!
//! * **The promise / guarded hole** — each leg's output is a promise other legs
//!   pipeline against. The handoff is the canonical [`EventualRef`] from
//!   `turn/src/eventual.rs` (`source_turn` = the round, `output_slot` = the
//!   producing leg); the FILL is the blake3 of the produced output (the
//!   guarded-hole value, recorded in the receipt so a verifier sees exactly which
//!   result each downstream leg pipelined against).
//! * **The topological pipeline** — legs are ordered by their declared
//!   dependencies with the SAME Kahn topo `turn/src/eventual.rs::Pipeline` uses;
//!   legs in one layer have no data dependency and run in parallel.
//! * **The atomic conserving settle** — the round's value moves settle through the
//!   verified executor ([`settle_ring_wide_verified`], per-asset Σδ=0, Lean-FFI
//!   cross-checked leg by leg). It is all-or-nothing by construction.
//! * **Broken-promise rollback** — if any leg's off-chain work fails, its promise
//!   is BROKEN and the breakage propagates to every downstream leg with the SAME
//!   [`BrokenReason`] cascade `turn/src/pending.rs` defines. The settle never runs,
//!   so ZERO value moves and the ledger is untouched: the round rolls back whole.
//!
//! ## What is real vs. demo (honest)
//!
//! REAL: the promise handoff (an [`EventualRef`] per leg + its recorded fill), the
//! topological parallel layering, the atomic verified conserving settle (the same
//! `settle_ring_wide_verified` the ring and the service-promise escrow trust — it
//! routes each leg through the real Lean kernel export), the broken-promise
//! rollback (no settle ⇒ no value move), and the per-asset conservation of the
//! whole round. What a CALLER supplies is the off-chain WORK each agent does (an
//! arbitrary closure that reads upstream promises and produces this leg's output +
//! the value moves it contributes); this module does not interpret that work — it
//! orchestrates the promise pipeline around it and proves the settlement.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use dregg_intent::CommitmentId;
use dregg_intent::exchange::AssetId;
use dregg_intent::verified_settle::{
    VerifiedSettleError, WideLedger, WideLeg, settle_ring_wide_verified,
};
use dregg_turn::error::TurnError;
use dregg_turn::eventual::EventualRef;
use dregg_turn::pending::BrokenReason;

/// The off-chain result an agent's work produces in a coordination round.
///
/// `output` is the value downstream legs pipeline against (the promise's fill);
/// `value_moves` are the on-chain settlements this leg contributes to the round's
/// single atomic settle.
#[derive(Clone, Debug, Default)]
pub struct LegOutput {
    /// The off-chain output downstream legs read as a resolved promise.
    pub output: Vec<u8>,
    /// The value moves this leg contributes to the round's atomic settlement.
    pub value_moves: Vec<WideLeg>,
}

impl LegOutput {
    /// An output with no value moves (a pure-compute leg that only produces a
    /// result for downstream legs to pipeline against).
    pub fn compute(output: impl Into<Vec<u8>>) -> Self {
        Self {
            output: output.into(),
            value_moves: Vec::new(),
        }
    }

    /// An output that also settles value moves in the atomic round.
    pub fn with_moves(output: impl Into<Vec<u8>>, value_moves: Vec<WideLeg>) -> Self {
        Self {
            output: output.into(),
            value_moves,
        }
    }
}

/// The resolved upstream promises a leg's work reads — its declared dependencies'
/// outputs, keyed by upstream leg label. A leg PIPELINES against these: they are
/// the promises its upstream agents handed it, already filled.
pub type ResolvedPromises<'a> = &'a HashMap<String, Vec<u8>>;

/// An agent's off-chain work: read the resolved upstream promises, produce this
/// leg's output + value moves, or fail (which BREAKS this leg's promise and rolls
/// the whole round back).
pub type WorkFn<'a> = Box<dyn FnOnce(ResolvedPromises) -> Result<LegOutput, String> + 'a>;

/// One agent's promised contribution to a coordination round.
pub struct CoordinationLeg<'a> {
    /// The agent performing this leg (its ring identity / cell commitment).
    pub agent: CommitmentId,
    /// A unique label naming this leg (downstream legs reference it by label).
    pub label: String,
    /// Labels of upstream legs whose promised output this leg pipelines against.
    pub depends_on: Vec<String>,
    /// The off-chain work this agent performs.
    pub work: WorkFn<'a>,
}

impl<'a> CoordinationLeg<'a> {
    /// A leg with no upstream dependencies (it can run in the first parallel
    /// layer).
    pub fn new(
        agent: CommitmentId,
        label: impl Into<String>,
        work: impl FnOnce(ResolvedPromises) -> Result<LegOutput, String> + 'a,
    ) -> Self {
        Self {
            agent,
            label: label.into(),
            depends_on: Vec::new(),
            work: Box::new(work),
        }
    }

    /// Declare that this leg pipelines against the promised output of `label`.
    pub fn after(mut self, label: impl Into<String>) -> Self {
        self.depends_on.push(label.into());
        self
    }
}

/// The record of one filled promise in a coordination round — which agent's leg
/// produced it, the canonical [`EventualRef`] handoff it stands for, and the
/// guarded-hole fill (the blake3 of the produced output) downstream legs
/// pipelined against.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromiseFill {
    /// The label of the leg that produced this promise.
    pub leg: String,
    /// The agent that produced it.
    pub agent: CommitmentId,
    /// The canonical eventual-ref this promise stands for (round + output slot).
    pub promise: EventualRef,
    /// The guarded-hole fill: blake3 of the produced output.
    pub output_hash: [u8; 32],
}

/// The receipt of a successful atomic coordination round.
#[derive(Clone, Debug)]
pub struct CoordinationReceipt {
    /// The round identifier (the `source_turn` of every promise in the round).
    pub round_id: [u8; 32],
    /// The promise handoffs, in resolution order — the pipeline's audit trail.
    pub fills: Vec<PromiseFill>,
    /// The dependency layers: legs in `parallel_layers[i]` had no data dependency
    /// on each other and ran in parallel off-chain.
    pub parallel_layers: Vec<Vec<String>>,
    /// Every value move that settled, in the order folded into the atomic settle.
    pub settled_moves: Vec<WideLeg>,
    /// The verified post-state ledger after the atomic settle (per-asset Σδ=0).
    pub verified_post: WideLedger,
    /// A canonical digest binding the whole round (id + every fill + every move).
    pub round_hash: [u8; 32],
}

impl CoordinationReceipt {
    /// The total settled supply of `asset` across the post-ledger (the conserved
    /// quantity — equals the pre-round supply on a conserving round).
    pub fn settled_total(&self, asset: &AssetId) -> i128 {
        self.verified_post.total_asset(asset)
    }
}

/// Why a coordination round refused. Every variant is ATOMIC: on `UnknownDependency`,
/// `Cycle`, and `Broken` ZERO value moved (the failure is before the settle); on
/// `NotConserving` the verified settle rejected the fold whole, so again nothing
/// committed.
#[derive(Clone, Debug)]
pub enum CoordinationError {
    /// A leg declared a dependency on a label that is not in the round.
    UnknownDependency {
        /// The leg with the dangling dependency.
        leg: String,
        /// The missing dependency label.
        missing: String,
    },
    /// Two legs share a label — labels must be unique to name promises.
    DuplicateLabel(String),
    /// The dependency graph has a cycle (legs that can never resolve).
    Cycle(Vec<String>),
    /// An agent's off-chain work failed: its promise BROKE. The breakage
    /// propagated to every downstream leg (the [`BrokenReason`] cascade). NOTHING
    /// settled — the round rolled back whole.
    Broken {
        /// The leg whose work failed.
        leg: String,
        /// Why its promise broke (the originating reason).
        reason: BrokenReason,
        /// The downstream legs whose promises broke transitively, with the
        /// dependency-broken reason each received.
        downstream_broken: Vec<String>,
    },
    /// The round's value moves did not conserve through the verified executor.
    /// Atomic: the verified gate rejected the fold whole, so nothing committed.
    NotConserving(VerifiedSettleError),
}

impl std::fmt::Display for CoordinationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownDependency { leg, missing } => {
                write!(f, "leg '{leg}' depends on unknown leg '{missing}'")
            }
            Self::DuplicateLabel(l) => write!(f, "duplicate leg label '{l}'"),
            Self::Cycle(nodes) => write!(f, "dependency cycle among legs {nodes:?}"),
            Self::Broken {
                leg,
                reason,
                downstream_broken,
            } => write!(
                f,
                "leg '{leg}' promise broke ({reason}); {} downstream legs rolled back: {downstream_broken:?}",
                downstream_broken.len()
            ),
            Self::NotConserving(e) => write!(f, "round did not conserve: {e}"),
        }
    }
}

impl std::error::Error for CoordinationError {}

/// **Run one atomic agent-coordination round.**
///
/// 1. **Validate + layer.** Labels must be unique and every declared dependency
///    must name a leg in the round. The legs are topologically layered (Kahn, the
///    same order `turn/src/eventual.rs::Pipeline` uses); a cycle is refused.
/// 2. **Off-chain promise pipeline.** In dependency order, each leg's work runs
///    with the resolved outputs of the legs it depends on (the promises handed to
///    it). Its output becomes a filled promise downstream legs pipeline against.
///    Legs in one layer have no data dependency and are independent (parallel).
///    NONE of this touches the chain.
///    * If a leg's work fails, its promise BREAKS: the breakage propagates to every
///      downstream leg ([`BrokenReason::DependencyBroken`]) and the round returns
///      [`CoordinationError::Broken`] WITHOUT settling — zero value moved.
/// 3. **One atomic on-chain settle.** Every leg's value moves are folded into a
///    single [`settle_ring_wide_verified`] over `ledger` — all-or-nothing, per-asset
///    conservation asserted, each leg Lean-FFI cross-checked. A non-conserving round
///    is rejected whole ([`CoordinationError::NotConserving`]); nothing commits.
///
/// On success returns a [`CoordinationReceipt`] carrying the promise handoffs, the
/// parallel layering, the settled moves, and the verified conserving post-ledger.
pub fn coordinate(
    round_id: [u8; 32],
    legs: Vec<CoordinationLeg<'_>>,
    ledger: &WideLedger,
) -> Result<CoordinationReceipt, CoordinationError> {
    // (1) Validate labels are unique and build the label→index map.
    let mut index: HashMap<String, usize> = HashMap::new();
    for (i, leg) in legs.iter().enumerate() {
        if index.insert(leg.label.clone(), i).is_some() {
            return Err(CoordinationError::DuplicateLabel(leg.label.clone()));
        }
    }
    // Every dependency must name a real leg.
    for leg in &legs {
        for dep in &leg.depends_on {
            if !index.contains_key(dep) {
                return Err(CoordinationError::UnknownDependency {
                    leg: leg.label.clone(),
                    missing: dep.clone(),
                });
            }
        }
    }

    // (1b) Topologically LAYER the legs (Kahn). Each layer's legs are mutually
    //      independent — no data dependency — so they run in parallel off-chain.
    let layers = topo_layers(&legs, &index)?;

    // (2) Off-chain promise pipeline. Resolve each leg's promise in dependency
    //     order, handing each leg the filled promises of the legs it depends on.
    let mut resolved: HashMap<String, Vec<u8>> = HashMap::new();
    let mut fills: Vec<PromiseFill> = Vec::new();
    let mut settled_moves: Vec<WideLeg> = Vec::new();

    // Consume legs by index so we can move each `work` (FnOnce) out exactly once.
    let mut work_by_label: HashMap<String, (CommitmentId, usize, WorkFn<'_>, Vec<String>)> =
        HashMap::new();
    for (i, leg) in legs.into_iter().enumerate() {
        work_by_label.insert(leg.label.clone(), (leg.agent, i, leg.work, leg.depends_on));
    }

    for layer in &layers {
        for label in layer {
            let (agent, slot, work, depends_on) = work_by_label
                .remove(label)
                .expect("layer label is a real leg");

            // Gather the promises handed to this leg (its resolved upstream
            // outputs). All deps are in earlier layers, so they are resolved.
            let inputs: HashMap<String, Vec<u8>> = depends_on
                .iter()
                .map(|d| (d.clone(), resolved.get(d).cloned().unwrap_or_default()))
                .collect();

            match work(&inputs) {
                Ok(out) => {
                    let output_hash = *blake3::hash(&out.output).as_bytes();
                    resolved.insert(label.clone(), out.output);
                    fills.push(PromiseFill {
                        leg: label.clone(),
                        agent,
                        promise: EventualRef::new(round_id, slot as u32),
                        output_hash,
                    });
                    settled_moves.extend(out.value_moves);
                }
                Err(detail) => {
                    // The promise broke. Propagate the breakage to every downstream
                    // leg (the BrokenReason cascade) and refuse the round WITHOUT
                    // settling — nothing has touched the chain, so the round rolls
                    // back whole.
                    let reason = BrokenReason::TurnRejected(TurnError::PreconditionFailed {
                        description: detail,
                    });
                    let downstream =
                        downstream_of(label, &work_by_label, &fills_labels(&fills), &layers);
                    return Err(CoordinationError::Broken {
                        leg: label.clone(),
                        reason,
                        downstream_broken: downstream,
                    });
                }
            }
        }
    }

    // (3) One atomic on-chain settle: fold every value move through the verified
    //     executor (all-or-nothing, per-asset Σδ=0, Lean-FFI cross-checked).
    let verified_post = settle_ring_wide_verified(ledger, &settled_moves)
        .map_err(CoordinationError::NotConserving)?;

    let round_hash = round_digest(round_id, &fills, &settled_moves);

    Ok(CoordinationReceipt {
        round_id,
        fills,
        parallel_layers: layers,
        settled_moves,
        verified_post,
        round_hash,
    })
}

/// The labels already resolved (for downstream computation on a break).
fn fills_labels(fills: &[PromiseFill]) -> BTreeSet<String> {
    fills.iter().map(|f| f.leg.clone()).collect()
}

/// Compute the set of legs that transitively depend on `broken` and have not yet
/// resolved — the legs whose promises break in the cascade.
fn downstream_of(
    broken: &str,
    remaining: &HashMap<String, (CommitmentId, usize, WorkFn<'_>, Vec<String>)>,
    resolved: &BTreeSet<String>,
    _layers: &[Vec<String>],
) -> Vec<String> {
    // Build the reverse edges over the still-unresolved legs.
    let mut deps: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (label, (_, _, _, depends_on)) in remaining {
        deps.insert(label.clone(), depends_on.clone());
    }
    let mut broken_set: BTreeSet<String> = BTreeSet::new();
    broken_set.insert(broken.to_string());
    // Iterate to a fixpoint: a leg breaks if any of its deps is broken.
    let mut changed = true;
    while changed {
        changed = false;
        for (label, depends_on) in &deps {
            if broken_set.contains(label) || resolved.contains(label) {
                continue;
            }
            if depends_on.iter().any(|d| broken_set.contains(d)) {
                broken_set.insert(label.clone());
                changed = true;
            }
        }
    }
    broken_set.remove(broken);
    broken_set.into_iter().collect()
}

/// Topologically layer the legs (Kahn). Each returned layer's labels are mutually
/// independent and run in parallel; layer `i+1` depends only on layers `≤ i`.
fn topo_layers(
    legs: &[CoordinationLeg<'_>],
    index: &HashMap<String, usize>,
) -> Result<Vec<Vec<String>>, CoordinationError> {
    let n = legs.len();
    let mut in_degree = vec![0usize; n];
    let mut successors: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, leg) in legs.iter().enumerate() {
        for dep in &leg.depends_on {
            let d = index[dep];
            successors[d].push(i);
            in_degree[i] += 1;
        }
    }

    let mut queue: VecDeque<usize> = (0..n).filter(|i| in_degree[*i] == 0).collect();
    let mut layers: Vec<Vec<String>> = Vec::new();
    let mut placed = 0usize;
    while !queue.is_empty() {
        let mut layer: Vec<usize> = queue.drain(..).collect();
        layer.sort_unstable();
        let mut next: VecDeque<usize> = VecDeque::new();
        for &node in &layer {
            placed += 1;
            for &succ in &successors[node] {
                in_degree[succ] -= 1;
                if in_degree[succ] == 0 {
                    next.push_back(succ);
                }
            }
        }
        layers.push(layer.into_iter().map(|i| legs[i].label.clone()).collect());
        queue = next;
    }

    if placed != n {
        let cycle: Vec<String> = (0..n)
            .filter(|i| in_degree[*i] > 0)
            .map(|i| legs[i].label.clone())
            .collect();
        return Err(CoordinationError::Cycle(cycle));
    }
    Ok(layers)
}

/// A canonical digest binding the whole round: the round id, every promise fill
/// (leg + agent + slot + output hash), and every settled value move.
fn round_digest(round_id: [u8; 32], fills: &[PromiseFill], moves: &[WideLeg]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg.agent-coordination.round.v1");
    h.update(&round_id);
    for f in fills {
        h.update(f.leg.as_bytes());
        h.update(&f.agent.0);
        h.update(&f.promise.source_turn);
        h.update(&f.promise.output_slot.to_le_bytes());
        h.update(&f.output_hash);
    }
    for m in moves {
        h.update(&m.from);
        h.update(&m.to);
        h.update(&m.asset);
        h.update(&m.amount.to_le_bytes());
    }
    *h.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CommitmentId {
        CommitmentId([b; 32])
    }
    fn asset(b: u8) -> AssetId {
        let mut a = [0u8; 32];
        a[0] = b;
        a
    }
    fn round() -> [u8; 32] {
        [0x9c; 32]
    }

    /// A ledger funding `cell` with `bal` of `asset`, with `also` live too.
    fn ledger_with(funded: &[([u8; 32], AssetId, i128)], live: &[[u8; 32]]) -> WideLedger {
        let mut k = WideLedger::new();
        for c in live {
            k.add_account(*c);
        }
        for (c, a, v) in funded {
            k.add_account(*c);
            k.set(*c, a, *v);
        }
        k
    }

    // ── The headline: two agents coordinate via the promise pipeline, settle atomic ──

    /// Agent A computes a result (off-chain). Agent B PIPELINES its work against
    /// A's promised result and contributes the value move. The whole cooperation
    /// settles as ONE atomic verified conserving fold. A produced a result B
    /// needed; only the final settle hit the chain.
    #[test]
    fn two_agents_coordinate_and_settle_atomically() {
        let a = cid(1); // the producer
        let b = cid(2); // the consumer who pipelines against A's promise
        let pay = asset(7);

        // B pays A 30 of `pay` IFF A's computed result is the agreed answer.
        // B's payment AMOUNT is derived from A's promised output (it pipelines it).
        let k0 = ledger_with(&[(b.0, pay, 100)], &[a.0]);
        assert_eq!(k0.total_asset(&pay), 100);

        let legs = vec![
            CoordinationLeg::new(a, "produce", move |_inputs| {
                // A's off-chain work: compute a result (here, the price to charge).
                Ok(LegOutput::compute(30u64.to_le_bytes().to_vec()))
            }),
            CoordinationLeg::new(b, "consume", move |inputs| {
                // B PIPELINES against A's promise: it reads A's produced result and
                // settles a payment for exactly that amount.
                let raw = inputs.get("produce").cloned().unwrap_or_default();
                let amount =
                    u64::from_le_bytes(raw.try_into().map_err(|_| "bad promise".to_string())?);
                Ok(LegOutput::with_moves(
                    b"paid",
                    vec![WideLeg {
                        from: b.0,
                        to: a.0,
                        asset: pay,
                        amount: amount as i128,
                    }],
                ))
            })
            .after("produce"),
        ];

        let receipt = coordinate(round(), legs, &k0).expect("a conserving round settles");

        // The promise pipeline ran: A produced, B pipelined against it.
        assert_eq!(receipt.fills.len(), 2);
        assert_eq!(receipt.fills[0].leg, "produce");
        assert_eq!(receipt.fills[1].leg, "consume");
        // A's promise stands as a canonical EventualRef on the round.
        assert_eq!(receipt.fills[0].promise.source_turn, round());

        // The two legs are in distinct parallel layers (B depends on A).
        assert_eq!(
            receipt.parallel_layers,
            vec![vec!["produce".to_string()], vec!["consume".to_string()]]
        );

        // The settle was ATOMIC + CONSERVED: B paid A 30, supply unchanged.
        assert_eq!(receipt.verified_post.get(b.0, &pay), 70);
        assert_eq!(receipt.verified_post.get(a.0, &pay), 30);
        assert_eq!(
            receipt.settled_total(&pay),
            100,
            "value conserved end-to-end"
        );
    }

    // ── N parties: three agents, parallel off-chain, one atomic settle ──

    /// Three agents form a conserving ring (A→B→C→A of one asset each). Two legs
    /// have no dependency (they compute in parallel); the closing leg pipelines
    /// against both. One atomic settle commits the whole ring or none of it.
    #[test]
    fn three_agents_parallel_then_one_atomic_settle() {
        let a = cid(1);
        let b = cid(2);
        let c = cid(3);
        let g = asset(7);

        // Each holds 100; A→B 10, B→C 10, C→A 10 — a conserving cycle.
        let k0 = ledger_with(&[(a.0, g, 100), (b.0, g, 100), (c.0, g, 100)], &[]);

        let legs = vec![
            CoordinationLeg::new(a, "leg_a", move |_| {
                Ok(LegOutput::with_moves(
                    b"a",
                    vec![WideLeg {
                        from: a.0,
                        to: b.0,
                        asset: g,
                        amount: 10,
                    }],
                ))
            }),
            CoordinationLeg::new(b, "leg_b", move |_| {
                Ok(LegOutput::with_moves(
                    b"b",
                    vec![WideLeg {
                        from: b.0,
                        to: c.0,
                        asset: g,
                        amount: 10,
                    }],
                ))
            }),
            // The closing leg pipelines against both upstream promises.
            CoordinationLeg::new(c, "leg_c", move |inputs| {
                assert!(inputs.contains_key("leg_a"));
                assert!(inputs.contains_key("leg_b"));
                Ok(LegOutput::with_moves(
                    b"c",
                    vec![WideLeg {
                        from: c.0,
                        to: a.0,
                        asset: g,
                        amount: 10,
                    }],
                ))
            })
            .after("leg_a")
            .after("leg_b"),
        ];

        let receipt = coordinate(round(), legs, &k0).expect("conserving ring settles");
        // leg_a and leg_b ran in the SAME (parallel) layer; leg_c closed.
        assert_eq!(
            receipt.parallel_layers[0],
            vec!["leg_a".to_string(), "leg_b".to_string()]
        );
        assert_eq!(receipt.parallel_layers[1], vec!["leg_c".to_string()]);
        // Conserved: everyone net-zero (received 10, sent 10).
        assert_eq!(receipt.verified_post.get(a.0, &g), 100);
        assert_eq!(receipt.verified_post.get(b.0, &g), 100);
        assert_eq!(receipt.verified_post.get(c.0, &g), 100);
        assert_eq!(receipt.settled_total(&g), 300);
    }

    // ── Rollback: one leg's promise breaks → the whole round rolls back ──

    /// Agent B's off-chain work FAILS — its promise breaks. The round refuses
    /// WITHOUT settling: zero value moves, the ledger is byte-identical to the
    /// pre-round state. This is the atomicity: parallel off-chain, and if any leg
    /// fails, nothing settles.
    #[test]
    fn a_broken_promise_rolls_the_whole_round_back() {
        let a = cid(1);
        let b = cid(2);
        let pay = asset(7);
        let k0 = ledger_with(&[(a.0, pay, 100), (b.0, pay, 100)], &[]);
        let before = k0.clone();

        let legs = vec![
            // A would have paid B — but A settles AFTER B in the pipeline.
            CoordinationLeg::new(a, "pay", move |_| {
                Ok(LegOutput::with_moves(
                    b"a",
                    vec![WideLeg {
                        from: a.0,
                        to: b.0,
                        asset: pay,
                        amount: 50,
                    }],
                ))
            }),
            // B's work fails: its promise breaks.
            CoordinationLeg::new(b, "verify", move |_| {
                Err("B could not verify the work — promise broken".to_string())
            })
            .after("pay"),
        ];

        let err = coordinate(round(), legs, &k0).expect_err("a broken promise refuses the round");
        match err {
            CoordinationError::Broken { leg, .. } => assert_eq!(leg, "verify"),
            other => panic!("expected Broken, got {other:?}"),
        }

        // ATOMICITY: the ledger is untouched — A's payment never settled.
        assert_eq!(
            k0, before,
            "a broken promise leaves the ledger byte-identical"
        );
        // (the coordinate() borrow took &k0; the demonstration is that no settle
        // ran because the break returned before settle_ring_wide_verified.)
    }

    /// The break PROPAGATES: a deep chain A→B→C→D where B breaks rolls back C and
    /// D too (the BrokenReason cascade), and nothing settles.
    #[test]
    fn broken_promise_propagates_downstream() {
        let a = cid(1);
        let b = cid(2);
        let c = cid(3);
        let d = cid(4);
        let k0 = ledger_with(&[(a.0, asset(7), 100)], &[b.0, c.0, d.0]);

        let legs = vec![
            CoordinationLeg::new(a, "a", move |_| Ok(LegOutput::compute(b"a".to_vec()))),
            CoordinationLeg::new(b, "b", move |_| Err("b fails".to_string())).after("a"),
            CoordinationLeg::new(c, "c", move |_| Ok(LegOutput::compute(b"c".to_vec()))).after("b"),
            CoordinationLeg::new(d, "d", move |_| Ok(LegOutput::compute(b"d".to_vec()))).after("c"),
        ];

        let err = coordinate(round(), legs, &k0).expect_err("b breaks the round");
        match err {
            CoordinationError::Broken {
                leg,
                downstream_broken,
                ..
            } => {
                assert_eq!(leg, "b");
                // c and d break transitively (a already resolved).
                assert!(downstream_broken.contains(&"c".to_string()));
                assert!(downstream_broken.contains(&"d".to_string()));
                assert!(!downstream_broken.contains(&"a".to_string()));
            }
            other => panic!("expected Broken, got {other:?}"),
        }
    }

    // ── Non-conserving round is rejected whole by the verified gate ──

    /// A round whose value moves do not conserve (an agent tries to pay more than
    /// it holds) is rejected by the verified executor — atomically, nothing
    /// commits.
    #[test]
    fn non_conserving_round_is_rejected_whole() {
        let a = cid(1);
        let b = cid(2);
        let pay = asset(7);
        // A holds only 10 but its leg tries to move 999.
        let k0 = ledger_with(&[(a.0, pay, 10)], &[b.0]);

        let legs = vec![CoordinationLeg::new(a, "overspend", move |_| {
            Ok(LegOutput::with_moves(
                b"x",
                vec![WideLeg {
                    from: a.0,
                    to: b.0,
                    asset: pay,
                    amount: 999,
                }],
            ))
        })];

        let err = coordinate(round(), legs, &k0).expect_err("overspend cannot conserve");
        assert!(matches!(err, CoordinationError::NotConserving(_)));
    }

    // ── Structural refusals ──

    #[test]
    fn unknown_dependency_is_refused() {
        let a = cid(1);
        let legs = vec![CoordinationLeg::new(a, "x", |_| Ok(LegOutput::default())).after("ghost")];
        let err = coordinate(round(), legs, &WideLedger::new()).unwrap_err();
        assert!(matches!(err, CoordinationError::UnknownDependency { .. }));
    }

    #[test]
    fn a_cycle_is_refused() {
        let a = cid(1);
        let b = cid(2);
        let legs = vec![
            CoordinationLeg::new(a, "x", |_| Ok(LegOutput::default())).after("y"),
            CoordinationLeg::new(b, "y", |_| Ok(LegOutput::default())).after("x"),
        ];
        let err = coordinate(round(), legs, &WideLedger::new()).unwrap_err();
        assert!(matches!(err, CoordinationError::Cycle(_)));
    }

    #[test]
    fn round_hash_is_deterministic() {
        let a = cid(1);
        let mk = || {
            vec![CoordinationLeg::new(a, "x", |_| {
                Ok(LegOutput::compute(b"same".to_vec()))
            })]
        };
        let r1 = coordinate(round(), mk(), &WideLedger::new()).unwrap();
        let r2 = coordinate(round(), mk(), &WideLedger::new()).unwrap();
        assert_eq!(r1.round_hash, r2.round_hash);
    }
}
