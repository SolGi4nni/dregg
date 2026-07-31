//! consensus_fault_sim.rs — the RUN under failure, tested at last.
//!
//! The test-rigor audit's #1 gap: "prove the rule, skip the run." The blocklace
//! finality RULE (`ordering::tau`) is machine-checked in
//! `metatheory/Dregg2/Distributed/BlocklaceFinality.lean` and differential-tested
//! (`ordering::tests`), and `multi_node_convergence.rs` drives ONE scripted
//! partition→heal→equivocate lifecycle at n=3. What was missing is the *run under
//! adversity, parameterised by the fault budget*: an N-node federation that injects
//! node-kill / partition / lag / Byzantine equivocation and asserts the
//! safety+liveness contract the federation poster claims:
//!
//!   * SAFETY  — no two honest nodes finalize a conflicting history
//!               (`no_conflicting_finalized_history`): every pair of finalized
//!               orders is prefix-consistent, at ALL times, through every fault.
//!   * LIVENESS— the federation finalizes a non-trivial order while ≥ quorum
//!               producers are up (`quorum_threshold(n) = supermajority(n)`).
//!   * TOLERANCE— it survives f = ⌊(n−1)/3⌋ faults: kill f ⇒ still finalizes;
//!               kill f+1 ⇒ it correctly STALLS (no finalization) — never forks.
//!   * EXCLUSION— a Byzantine equivocator is detected, evicted, and anchors
//!               nothing; the honest quorum finalizes identically through it.
//!
//! ## Real-vs-engine honesty
//!
//! This is a **deterministic in-process engine sim**, NOT real node processes. It
//! drives the EXACT consensus types the live `dregg-node` runs — the A1-fixed
//! `finality::Blocklace` insert/merge/equivocation path and the `ordering::tau`
//! Cordial-Miners rule (via `finalized_order`, lifted verbatim from
//! `blocklace_sync::poll_finalized_blocks`) — with NO mock and NO shadow. The only
//! thing simulated is the *network*: "deliver block set X to node subset S" models
//! gossip, so a partition is "don't deliver across the cut" and a kill is "this
//! creator authors nothing." This is deliberate: the real-process harness
//! (`node/tests/consensus_under_failure.rs`) exercises the SAME rule over real QUIC
//! but cannot assert finality today (the gossip-dissemination leg / A1 binary is
//! the open work — see that file). The property assertions BITE HERE, now: each
//! scenario injects a fault and asserts a property that would FAIL if the rule
//! broke, and `harness_meta_*` proves the safety/liveness checks are non-vacuous
//! (they reject a planted fork / a planted stall).
//!
//! Fast by construction (pure CPU, no I/O, no sleeps) — runs in the default
//! `cargo test --workspace` CI lane. The heavier soak sweep (many n, deeper DAGs)
//! is `#[ignore]`d and runs under `cargo test -p dregg-blocklace -- --ignored`.

use std::collections::HashMap;

use dregg_blocklace::constitution::{Constitution, ConstitutionManager};
use dregg_blocklace::finality::{
    Block, BlockError, BlockId, Blocklace, CheckpointData, MergeError, Payload,
};
use dregg_blocklace::ordering::supermajority_threshold;
use ed25519_dalek::SigningKey;

// ─── Scaffolding (mirrors multi_node_convergence.rs; kept self-contained so the
//     two sims don't share a mutable module in the shared tree) ─────────────────

fn key(seed: u8) -> SigningKey {
    // Every block this sim signs carries an ML-DSA-65 half, and `dregg-pq` aborts the process
    // on an ML-DSA op with no verified core installed. `dregg-blocklace` is a light leaf that
    // cannot link the Lean archive, so this test binary installs the cores through the
    // dev-only `dregg-pq-testkit`. `key` is the one gateway every test here goes through, and
    // the install is `Once`-guarded, so this is the whole wiring.
    dregg_pq_testkit::install_or_panic();
    SigningKey::from_bytes(&[seed; 32])
}
fn pubkey(sk: &SigningKey) -> [u8; 32] {
    // The CONSENSUS identity label is the HYBRID id (== `Block::creator`), so tau
    // participants match the creators the finality blocks actually carry.
    Block::hybrid_id(sk)
}

/// The **ed25519 strand key** — the space `Constitution::participants` is keyed by,
/// and therefore the space `auto_evict` matches an equivocator in.
///
/// ⚑ This fixture used to hand `pubkey` (the hybrid id) to `Constitution::new`, so its
/// constitution was HYBRID-keyed and the eviction assertion below passed. The real
/// node's constitution is ED25519-keyed (`blocklace_sync` seeds it from
/// `signing_key.verifying_key()`), so the same `auto_evict` call matched nothing and
/// evicted no one on the live path. The node holds both spaces; so does this now.
fn strand_key(sk: &SigningKey) -> [u8; 32] {
    sk.verifying_key().to_bytes()
}

/// Byzantine fault budget for an n-member committee: f = ⌊(n−1)/3⌋ (the
/// `n ≥ 3f+1` robust-BFT bound; matches `dregg_federation::fault_tolerance`).
fn fault_budget(n: usize) -> usize {
    if n == 0 { 0 } else { (n - 1) / 3 }
}

/// One in-process node: the finality blocklace (the live consensus state) + the
/// constitution manager that reacts to membership events — the exact pair the real
/// node holds in `BlocklaceHandle { lace, constitution, .. }`.
struct Node {
    name: String,
    lace: Blocklace,
    constitution: ConstitutionManager,
}

impl Node {
    /// `committee` is the validator set as SIGNING KEYS, so this derives BOTH identity
    /// spaces the way the node does: hybrid ids for tau, ed25519 strand keys for the
    /// constitution.
    fn new(name: impl Into<String>, sk: SigningKey, committee: &[&SigningKey]) -> Self {
        let quorum = if committee.len() <= 1 {
            1
        } else {
            supermajority_threshold(committee.len())
        };
        let strands: Vec<[u8; 32]> = committee.iter().map(|k| strand_key(k)).collect();
        let constitution = Constitution::new(strands, 0);
        Node {
            name: name.into(),
            lace: Blocklace::new(sk, quorum),
            constitution: ConstitutionManager::new(constitution),
        }
    }

    /// Receive one block as the live node does (`handle_push`): on an
    /// `Equivocation` the block is RETAINED as evidence and the creator is
    /// auto-evicted. Returns `true` iff an equivocation was surfaced.
    fn receive(&mut self, block: Block) -> bool {
        match self.lace.receive_block(block) {
            Ok(()) => false,
            Err(BlockError::Equivocation { proof, .. }) => {
                self.constitution.auto_evict(&proof);
                true
            }
            Err(e) => panic!("[{}] unexpected receive error: {e:?}", self.name),
        }
    }

    /// Deliver a causally-closed delta the way the node's catch-up path does
    /// (`Blocklace::merge` topo-sorts + closure-checks). Models a gossip flush.
    fn merge(&mut self, delta: Vec<Block>) -> Result<(), MergeError> {
        self.lace.merge(delta)
    }

    /// The finalized total order as `(creator, seq)` pairs — the node's
    /// `poll_finalized_blocks` observable.
    fn finalized(&self, participants: &[[u8; 32]]) -> Vec<([u8; 32], u64)> {
        finalized_order(&self.lace, participants)
    }
}

/// A round-synchronous block authored by `sk` at `seq`, pointing at `preds`.
fn round_block(sk: &SigningKey, seq: u64, preds: &[BlockId], tag: &[u8]) -> Block {
    Block::new(sk, seq, Payload::Turn(tag.to_vec()), preds.to_vec())
}

/// Compute the finalized `(creator, seq)` order EXACTLY as the node's
/// `blocklace_sync::poll_finalized_blocks` does (build the unsigned ordering
/// projection, run `ordering::tau`, map ids back). Lifted verbatim from
/// `multi_node_convergence.rs::finalized_order`.
fn finalized_order(finality_lace: &Blocklace, participants: &[[u8; 32]]) -> Vec<([u8; 32], u64)> {
    let mut ordering_lace = dregg_blocklace::Blocklace::new();
    let mut finality_to_ordering: HashMap<BlockId, dregg_blocklace::BlockId> = HashMap::new();
    let mut ordering_to_cs: HashMap<dregg_blocklace::BlockId, ([u8; 32], u64)> = HashMap::new();

    let mut blocks: Vec<(&BlockId, &Block)> = finality_lace.iter().collect();
    blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));

    for (fid, block) in blocks {
        let predecessors: Vec<dregg_blocklace::BlockId> = block
            .predecessors
            .iter()
            .filter_map(|p| finality_to_ordering.get(p).copied())
            .collect();
        let payload = match &block.payload {
            Payload::Turn(d) => d.clone(),
            Payload::TurnBundle(b) => b.signed_turn.clone(),
            Payload::ConsensusTimedTurnV1(b) => b.signed_turn().to_vec(),
            Payload::Ack => vec![],
            Payload::Checkpoint { root, height } => {
                let mut buf = Vec::with_capacity(40);
                buf.extend_from_slice(root);
                buf.extend_from_slice(&height.to_le_bytes());
                buf
            }
            Payload::MembershipVote { .. } => vec![0x04],
            Payload::Data(d) => d.clone(),
        };
        let ob = dregg_blocklace::Block::new(block.creator, block.seq, predecessors, payload);
        let oid = ob.id();
        let _ = ordering_lace.insert_unverified(ob);
        finality_to_ordering.insert(*fid, oid);
        ordering_to_cs.insert(oid, (block.creator, block.seq));
    }

    dregg_blocklace::ordering::tau(&ordering_lace, participants)
        .into_iter()
        .filter_map(|oid| ordering_to_cs.get(&oid).copied())
        .collect()
}

/// The SAME projection loop as [`finalized_order`], exposed as `(creator, seq) -> ordering-lace
/// BlockId`. Used to MEASURE (not assume) why two views can still differ intra-cohort: the
/// projection re-hashes each block over only the acks that RESOLVED in this node's lace, so a
/// block that acks something the node does not hold gets a different ordering-lace id — and
/// `ordering::xsort` breaks its ties on exactly that id.
fn ordering_projection_ids(
    finality_lace: &Blocklace,
) -> HashMap<([u8; 32], u64), dregg_blocklace::BlockId> {
    let mut finality_to_ordering: HashMap<BlockId, dregg_blocklace::BlockId> = HashMap::new();
    let mut out: HashMap<([u8; 32], u64), dregg_blocklace::BlockId> = HashMap::new();

    let mut blocks: Vec<(&BlockId, &Block)> = finality_lace.iter().collect();
    blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));

    for (fid, block) in blocks {
        let predecessors: Vec<dregg_blocklace::BlockId> = block
            .predecessors
            .iter()
            .filter_map(|p| finality_to_ordering.get(p).copied())
            .collect();
        let payload = match &block.payload {
            Payload::Turn(d) => d.clone(),
            _ => vec![],
        };
        let ob = dregg_blocklace::Block::new(block.creator, block.seq, predecessors, payload);
        let oid = ob.id();
        finality_to_ordering.insert(*fid, oid);
        out.insert((block.creator, block.seq), oid);
    }
    out
}

/// Build a round-synchronous DAG for `keys` over `rounds` rounds, each creator's
/// blocks starting at `start_seq` and pointing at ALL of the previous round's
/// blocks (round 0 seeded from `seed_preds`). Only the given `keys` author, so a
/// killed / partitioned-away creator is modelled by its ABSENCE from `keys`.
fn build_rounds_seeded(
    keys: &[&SigningKey],
    start_seq: u64,
    rounds: u64,
    seed_preds: &[BlockId],
) -> Vec<Vec<Block>> {
    let mut by_round: Vec<Vec<Block>> = Vec::new();
    for r in 0..rounds {
        let seq = start_seq + r;
        let preds: Vec<BlockId> = if r == 0 {
            seed_preds.to_vec()
        } else {
            by_round[(r - 1) as usize].iter().map(|b| b.id()).collect()
        };
        let mut round = Vec::new();
        for (i, sk) in keys.iter().enumerate() {
            round.push(round_block(sk, seq, &preds, &[seq as u8, i as u8]));
        }
        by_round.push(round);
    }
    by_round
}

fn build_rounds(keys: &[&SigningKey], rounds: u64) -> Vec<Vec<Block>> {
    build_rounds_seeded(keys, 0, rounds, &[])
}

fn flatten(by_round: &[Vec<Block>]) -> Vec<Block> {
    by_round.iter().flatten().cloned().collect()
}

// ─── The safety/liveness property checkers (returned as bool so the meta-tests
//     can prove they BITE — a checker that always passes proves nothing) ────────

/// SAFETY: `a` and `b` never DISAGREE at a shared position — one finalized order
/// is a prefix of the other. A fork (they agree up to position k then finalize
/// different `(creator,seq)` at k) is the exact `no_conflicting_finalized_history`
/// violation. Returns `false` on a conflict.
fn prefix_consistent(a: &[([u8; 32], u64)], b: &[([u8; 32], u64)]) -> bool {
    a.iter().zip(b.iter()).all(|(x, y)| x == y)
}

/// SAFETY over a whole federation: every pair of finalized orders is
/// prefix-consistent. Returns the first conflicting pair, or `None` if safe.
fn find_fork(orders: &[Vec<([u8; 32], u64)>]) -> Option<(usize, usize)> {
    for i in 0..orders.len() {
        for j in (i + 1)..orders.len() {
            if !prefix_consistent(&orders[i], &orders[j]) {
                return Some((i, j));
            }
        }
    }
    None
}

/// Assert the federation is fork-free (SAFETY). Panics with the offending pair.
fn assert_safety(nodes: &[&Node], participants: &[[u8; 32]], ctx: &str) {
    let orders: Vec<_> = nodes.iter().map(|n| n.finalized(participants)).collect();
    if let Some((i, j)) = find_fork(&orders) {
        panic!(
            "SAFETY VIOLATION [{ctx}]: node {} and node {} finalized conflicting histories\n  {} = {:?}\n  {} = {:?}",
            nodes[i].name, nodes[j].name, nodes[i].name, orders[i], nodes[j].name, orders[j]
        );
    }
}

// ─── SCENARIO A — node-kill: survive f, stall at f+1 (TOLERANCE + LIVENESS) ────

fn kill_scenario(n: usize, killed: usize, rounds: u64) -> (Vec<Vec<([u8; 32], u64)>>, usize) {
    let keys: Vec<SigningKey> = (0..n).map(|i| key(10 + i as u8)).collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();

    // The last `killed` creators are down: they author nothing and receive nothing.
    let alive = n - killed;
    let alive_keys: Vec<&SigningKey> = keys.iter().take(alive).collect();
    let dag = flatten(&build_rounds(&alive_keys, rounds));

    let mut nodes: Vec<Node> = (0..alive)
        .map(|i| {
            Node::new(
                format!("N{i}"),
                keys[i].clone(),
                &keys.iter().collect::<Vec<_>>(),
            )
        })
        .collect();
    for node in &mut nodes {
        node.merge(dag.clone())
            .expect("alive nodes merge the produced DAG");
    }

    // SAFETY holds regardless of how many are up.
    let refs: Vec<&Node> = nodes.iter().collect();
    assert_safety(&refs, &participants, &format!("n={n} killed={killed}"));

    let orders: Vec<_> = nodes.iter().map(|nd| nd.finalized(&participants)).collect();
    (orders, alive)
}

#[test]
fn n4_survives_f_kills_and_stalls_at_f_plus_one() {
    let n = 4;
    let f = fault_budget(n); // = 1
    assert_eq!(f, 1);

    // Kill exactly f: the remaining quorum (n−f = supermajority(n)) FINALIZES.
    let (orders_f, alive_f) = kill_scenario(n, f, 12);
    assert_eq!(
        alive_f,
        supermajority_threshold(n),
        "n−f must equal the quorum"
    );
    for (i, o) in orders_f.iter().enumerate() {
        assert!(
            !o.is_empty(),
            "[LIVENESS] with f={f} killed the surviving quorum of {alive_f} must finalize; node {i} finalized nothing"
        );
    }
    // (SAFETY was asserted inside kill_scenario.)

    // Kill f+1: only supermajority−1 producers remain → the leader can never be
    // super-ratified → the federation correctly STALLS (finalizes NOTHING). A
    // fork here is impossible because nothing is finalized at all.
    let (orders_f1, alive_f1) = kill_scenario(n, f + 1, 12);
    assert_eq!(alive_f1, supermajority_threshold(n) - 1);
    for (i, o) in orders_f1.iter().enumerate() {
        assert!(
            o.is_empty(),
            "[TOLERANCE] with f+1={} killed only {alive_f1} < quorum producers remain — tau MUST NOT finalize (safe stall, no fork); node {i} finalized {o:?}",
            f + 1
        );
    }
}

#[test]
fn n7_survives_two_kills_and_stalls_at_three() {
    // n=7 ⇒ f=2, quorum=5. The same contract at a wider committee.
    let n = 7;
    let f = fault_budget(n);
    assert_eq!(f, 2);

    let (orders_f, alive_f) = kill_scenario(n, f, 12);
    assert_eq!(alive_f, supermajority_threshold(n));
    assert!(
        orders_f.iter().all(|o| !o.is_empty()),
        "[LIVENESS] n=7, kill f=2 ⇒ quorum of 5 finalizes"
    );

    let (orders_f1, _) = kill_scenario(n, f + 1, 12);
    assert!(
        orders_f1.iter().all(|o| o.is_empty()),
        "[TOLERANCE] n=7, kill f+1=3 ⇒ only 4 < 5 producers ⇒ safe stall"
    );
}

// ─── SCENARIO B — partition heals with no conflicting finalization (SAFETY) ────

#[test]
fn partition_heals_without_conflicting_finalization() {
    // n=4, quorum=3. Split 3 | 1: the majority side is a quorum (can finalize),
    // the singleton cannot. Neither side may finalize a history that conflicts
    // with the other, and after the heal all four converge.
    let n = 4;
    let keys: Vec<SigningKey> = (0..n).map(|i| key(30 + i as u8)).collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();
    let kref: Vec<&SigningKey> = keys.iter().collect();

    let mut nodes: Vec<Node> = (0..n)
        .map(|i| {
            Node::new(
                format!("P{i}"),
                keys[i].clone(),
                &keys.iter().collect::<Vec<_>>(),
            )
        })
        .collect();

    // Phase 1: shared prefix (4 rounds), everyone.
    let pre = build_rounds(&kref, 4);
    let pre_flat = flatten(&pre);
    for node in &mut nodes {
        node.merge(pre_flat.clone())
            .expect("all merge shared prefix");
    }
    let refs: Vec<&Node> = nodes.iter().collect();
    assert_safety(&refs, &participants, "post-prefix");

    // Phase 2: PARTITION. Majority {0,1,2} keeps producing; minority {3} is cut off.
    let last_shared: Vec<BlockId> = pre[3].iter().map(|b| b.id()).collect();
    let maj_keys: Vec<&SigningKey> = keys.iter().take(3).collect();
    let maj_ext = flatten(&build_rounds_seeded(&maj_keys, 4, 4, &last_shared));
    for i in 0..3 {
        nodes[i].merge(maj_ext.clone()).expect("majority extends");
    }
    // The minority node {3}, alone, tries to extend too — but it is only 1 creator,
    // far below quorum, so it finalizes nothing new (and could not fork the chain).
    let min_ext = flatten(&build_rounds_seeded(&[&keys[3]], 4, 4, &last_shared));
    nodes[3]
        .merge(min_ext.clone())
        .expect("minority extends locally");

    // SAFETY holds THROUGH the partition: the majority finalized a longer history,
    // the minority did not finalize anything conflicting — prefix-consistent.
    let refs: Vec<&Node> = nodes.iter().collect();
    assert_safety(&refs, &participants, "under-partition");
    // The majority (a quorum) DID make finality progress the singleton could not.
    let maj_fin = nodes[0].finalized(&participants);
    let min_fin = nodes[3].finalized(&participants);
    assert!(
        !maj_fin.is_empty(),
        "[LIVENESS] the majority quorum keeps finalizing"
    );
    assert!(
        maj_fin.len() > min_fin.len(),
        "the partitioned singleton must fall behind the quorum ({} vs {})",
        min_fin.len(),
        maj_fin.len()
    );

    // Phase 3: HEAL. The minority receives the majority's delta (its causal past is
    // the shared prefix, already present) AND the majority receives the minority's
    // stray blocks. Everyone converges.
    nodes[3]
        .merge(maj_ext.clone())
        .expect("minority catches up");
    for i in 0..3 {
        nodes[i]
            .merge(min_ext.clone())
            .expect("majority absorbs minority's stray blocks");
    }

    let refs: Vec<&Node> = nodes.iter().collect();
    assert_safety(&refs, &participants, "post-heal");
    let orders: Vec<_> = nodes.iter().map(|nd| nd.finalized(&participants)).collect();
    // Convergence: all four finalize the identical order (same keyset ⇒ same tau).
    for i in 1..n {
        assert_eq!(
            orders[0], orders[i],
            "[CONVERGENCE] node P{i} must finalize identically after heal"
        );
    }
    // Monotonicity: the majority's pre-heal finalized prefix survives the heal.
    for entry in &maj_fin {
        assert!(
            orders[0].contains(entry),
            "heal must not retract a finalized entry {entry:?}"
        );
    }
}

// ─── SCENARIO C — Byzantine equivocation: detected, excluded, safety held ──────

#[test]
fn byzantine_equivocation_excluded_safety_and_liveness_held() {
    // n=4, f=1. One creator (C = index 3) is Byzantine and double-signs a slot.
    // The 3 honest nodes (= quorum) must: detect it, evict it, finalize identically
    // (SAFETY), never finalize the forked slot (EXCLUSION), and STILL finalize a
    // non-trivial order through the fault (LIVENESS survives f Byzantine).
    let n = 4;
    let keys: Vec<SigningKey> = (0..n).map(|i| key(50 + i as u8)).collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();
    let pk_c = pubkey(&keys[3]);
    let kref: Vec<&SigningKey> = keys.iter().collect();

    let mut nodes: Vec<Node> = (0..3)
        .map(|i| {
            Node::new(
                format!("H{i}"),
                keys[i].clone(),
                &keys.iter().collect::<Vec<_>>(),
            )
        })
        .collect();

    // A round-synchronous DAG over all 4 (C participates honestly at first).
    let dag = build_rounds(&kref, 5);
    let dag_flat = flatten(&dag);
    for node in &mut nodes {
        node.merge(dag_flat.clone())
            .expect("honest nodes merge the DAG");
    }
    let refs: Vec<&Node> = nodes.iter().collect();
    assert_safety(&refs, &participants, "pre-fork");
    let fin_pre: Vec<_> = nodes.iter().map(|nd| nd.finalized(&participants)).collect();
    assert!(
        !fin_pre[0].is_empty(),
        "the DAG finalized a prefix before the fault"
    );

    // C forks: two distinct blocks at the SAME (creator, seq).
    let fork_seq = 5u64;
    let fork_preds: Vec<BlockId> = dag[4].iter().map(|b| b.id()).collect();
    let fork_left = round_block(&keys[3], fork_seq, &fork_preds, b"BYZ-LEFT");
    let fork_right = round_block(&keys[3], fork_seq, &fork_preds, b"BYZ-RIGHT");
    assert_ne!(fork_left.id(), fork_right.id());

    // Deliver the two forks in DIFFERENT orders to different honest nodes — the
    // classic split-brain attempt. Detection must be order-independent.
    assert!(
        !nodes[0].receive(fork_left.clone()),
        "first fork inserts clean at H0"
    );
    assert!(
        nodes[0].receive(fork_right.clone()),
        "[DETECT] H0 must catch C's equivocation"
    );
    assert!(
        !nodes[1].receive(fork_right.clone()),
        "first fork inserts clean at H1 (opposite order)"
    );
    assert!(
        nodes[1].receive(fork_left.clone()),
        "[DETECT] H1 must catch it regardless of order"
    );
    // H2 sees only the left fork (a Byzantine node need not deliver both to everyone).
    nodes[2].receive(fork_left.clone());

    // DETECTION + EXCLUSION (membership): C is an equivocator on the nodes that saw
    // both, and evicted from their constitution; honest creators remain.
    for i in 0..2 {
        assert!(
            nodes[i].lace.equivocators().contains(&pk_c),
            "H{i} records C as equivocator"
        );
        // ⚑ Queried in the ED25519 STRAND space the constitution is actually keyed
        // by. Asking with `pk_c` (the hybrid id) is trivially false whether or not
        // the eviction fired, which is how this assertion stayed green while
        // `auto_evict` matched nothing on the live path.
        assert!(
            !nodes[i]
                .constitution
                .current
                .is_participant(&strand_key(&keys[3])),
            "H{i} evicts C"
        );
        assert!(
            nodes[i]
                .constitution
                .current
                .is_participant(&strand_key(&keys[0])),
            "H{i}: honest creator 0 must STILL be a participant — the anti-vacuity half. \
             A wrong query space reports EVERY key absent, which would make the eviction \
             assertion above meaningless."
        );
    }

    // SAFETY: the honest nodes finalize identically AFTER the fault; no split-brain.
    let refs: Vec<&Node> = nodes.iter().collect();
    assert_safety(&refs, &participants, "post-fork");
    let fin_post: Vec<_> = nodes.iter().map(|nd| nd.finalized(&participants)).collect();

    // EXCLUSION (finalized order): neither fork from the equivocator anchors the
    // forked slot on any honest node.
    for (i, fin) in fin_post.iter().enumerate() {
        assert!(
            !fin.iter().any(|(c, s)| *c == pk_c && *s == fork_seq),
            "H{i} must not finalize the equivocator's forked slot"
        );
    }
    // LIVENESS survives the Byzantine fault: the honest quorum still has a
    // non-trivial finalized order, and it did not regress.
    assert!(
        !fin_post[0].is_empty(),
        "[LIVENESS] honest quorum keeps a finalized order through the fault"
    );
    for entry in &fin_pre[0] {
        assert!(
            fin_post[0].contains(entry),
            "the pre-fork finalized prefix must survive the fault"
        );
    }
}

// ─── SCENARIO D — a slow/laggy node does not hold up finality (LIVENESS) ───────

#[test]
fn finality_proceeds_without_a_laggy_node() {
    // n=4, quorum=3. Three prompt nodes finalize; the 4th is SLOW — its blocks are
    // withheld during the finalization window, then delivered late. Finality must
    // proceed on the prompt quorum, and the late delivery must not retract or fork.
    let n = 4;
    let keys: Vec<SigningKey> = (0..n).map(|i| key(70 + i as u8)).collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();

    let prompt_keys: Vec<&SigningKey> = keys.iter().take(3).collect();
    // The prompt quorum's own round-synchronous DAG (the slow node contributes none
    // of these rounds in time).
    let prompt_dag = build_rounds(&prompt_keys, 10);
    let prompt_flat = flatten(&prompt_dag);

    let mut nodes: Vec<Node> = (0..3)
        .map(|i| {
            Node::new(
                format!("F{i}"),
                keys[i].clone(),
                &keys.iter().collect::<Vec<_>>(),
            )
        })
        .collect();
    for node in &mut nodes {
        node.merge(prompt_flat.clone()).expect("prompt nodes merge");
    }
    let refs: Vec<&Node> = nodes.iter().collect();
    assert_safety(&refs, &participants, "laggy: pre-late-delivery");
    let fin_prompt = nodes[0].finalized(&participants);
    assert!(
        !fin_prompt.is_empty(),
        "[LIVENESS] the prompt quorum finalizes without waiting for the slow node"
    );

    // The slow node's blocks finally arrive (it caught up on the prompt history, then
    // authored a couple of late rounds pointing at it). Deliver to the prompt nodes.
    let last_prompt: Vec<BlockId> = prompt_dag[9].iter().map(|b| b.id()).collect();
    let slow_late = flatten(&build_rounds_seeded(&[&keys[3]], 10, 2, &last_prompt));
    for node in &mut nodes {
        // causal past (the prompt history) is present, so the delta is closed.
        node.merge(slow_late.clone())
            .expect("prompt nodes absorb the slow node's late blocks");
    }

    let refs: Vec<&Node> = nodes.iter().collect();
    assert_safety(&refs, &participants, "laggy: post-late-delivery");
    let fin_after = nodes[0].finalized(&participants);
    // Monotonicity: nothing finalized before the late delivery is retracted.
    for entry in &fin_prompt {
        assert!(
            fin_after.contains(entry),
            "late delivery must not retract finalized entry {entry:?}"
        );
    }
}

// ─── SCENARIO F — an UNENROLLED creator must not supply a missing quorum member
//                 (HORIZONLOG B6) ────────────────────────────────────────────────

/// Run an `n`-validator federation for one wave (wavelength 3) where EVERY member authors the
/// first two rounds — so `ratifies`' approver-side quorum is satisfied for everyone — and only
/// `wave_end_alive` of them author the WAVE-END round, modelling validators that crash or slow
/// between rounds. Throughout, a signer that is **NOT in the committee** authors a well-formed,
/// correctly hybrid-signed block in every round and gossips it to everyone.
///
/// That signer is not an exotic adversary: `finality.rs::enroll_pq` is INSERT-ONLY while
/// `constitution.current.participants` shrinks on a passed membership proposal, so a ROTATED-OUT
/// validator keeps producing exactly these blocks and they keep passing ingest — which is why this
/// sim uses the same `receive_block`/`merge` path the live node uses and defeats no check to get
/// the block in. Returns each node's finalized order plus the committee and the outsider's id.
fn wave_end_short_with_outsider(
    n: usize,
    wave_end_alive: usize,
) -> (Vec<Vec<([u8; 32], u64)>>, Vec<[u8; 32]>, [u8; 32]) {
    let keys: Vec<SigningKey> = (0..n).map(|i| key(10 + i as u8)).collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();
    let outsider = key(200);
    let outsider_id = pubkey(&outsider);
    assert!(
        !participants.contains(&outsider_id),
        "the outsider must NOT be enrolled — else this scenario has no adversary"
    );

    // Rounds 1-2: the whole committee plus the outsider, fully connected.
    let mut early: Vec<&SigningKey> = keys.iter().collect();
    early.push(&outsider);
    let head = build_rounds_seeded(&early, 0, 2, &[]);
    let preds: Vec<BlockId> = head[1].iter().map(|b| b.id()).collect();

    // Round 3 (the wave end): only `wave_end_alive` committee members, plus the outsider.
    let mut late: Vec<&SigningKey> = keys.iter().take(wave_end_alive).collect();
    late.push(&outsider);
    let tail = build_rounds_seeded(&late, 2, 1, &preds);

    let dag: Vec<Block> = flatten(&head).into_iter().chain(flatten(&tail)).collect();

    let committee: Vec<&SigningKey> = keys.iter().collect();
    let mut nodes: Vec<Node> = (0..n)
        .map(|i| Node::new(format!("N{i}"), keys[i].clone(), &committee))
        .collect();
    for node in &mut nodes {
        node.merge(dag.clone())
            .expect("honest nodes accept the outsider's well-formed, correctly signed blocks");
    }

    // ANTI-VACUITY — the outsider really is in every honest node's lace, at every round,
    // including the wave-end round. A refusal that came from the block being absent would say
    // nothing about the finality rule.
    for node in &nodes {
        let seqs: Vec<u64> = node
            .lace
            .iter()
            .filter(|(_, b)| b.creator == outsider_id)
            .map(|(_, b)| b.seq)
            .collect();
        assert_eq!(
            seqs.len(),
            3,
            "[{}] the outsider must be in the lace at all three rounds, got {seqs:?}",
            node.name
        );
        assert!(
            seqs.contains(&2),
            "[{}] the outsider must have a WAVE-END block — that is the ratifier under test",
            node.name
        );
    }

    let refs: Vec<&Node> = nodes.iter().collect();
    assert_safety(
        &refs,
        &participants,
        &format!("n={n} wave_end_alive={wave_end_alive} +outsider"),
    );

    let orders = nodes.iter().map(|nd| nd.finalized(&participants)).collect();
    (orders, participants, outsider_id)
}

/// **HORIZONLOG B6, on the RUN.** `is_super_ratified` counted the DISTINCT CREATORS of the
/// wave-end blocks that ratify the leader, with no check that those creators are participants —
/// so a non-member's wave-end block was a full member of the quorum whose own name is
/// "a supermajority of distinct participants".
///
/// The consequence is the TOLERANCE property this file already asserts, defeated from outside:
/// at n=4 the quorum is 3, so a wave end reached by only 2 committee members MUST NOT anchor
/// (that is the safe stall `n4_survives_f_kills_and_stalls_at_f_plus_one` demands). Add ONE
/// unenrolled creator's block at that wave end and, before the ratifier gate, the count is 3 and
/// the federation COMMITS — the honest committee's turns finalized on a wave the committee did not
/// ratify. Two honest nodes with different views of a non-member's blocks (and non-members are
/// exactly the creators dissemination does not guarantee) would then finalize different prefixes.
///
/// BOTH POLES, in the same harness:
///   * the outsider cannot restore the quorum — the federation stalls, as it must; and
///   * with the committee's own wave end intact and the SAME outsider still in every lace at
///     every round, the federation finalizes normally and orders NOT ONE of its blocks.
///
/// Verified twin: `BlocklaceFinality.traceSybilRatify` and the `#guard` red/green pair on
/// `isSuperRatifiedPreEnrollment` / `isSuperRatified`.
#[test]
fn unenrolled_creator_cannot_supply_a_missing_wave_end_ratifier() {
    let n = 4;
    let quorum = supermajority_threshold(n);
    assert_eq!(quorum, 3, "n=4, f=1: three of four");

    // ── THE REFUSAL. Two committee members at the wave end is one short of the quorum; the
    //    outsider's wave-end block must not make it up.
    let (orders, participants, outsider) = wave_end_short_with_outsider(n, quorum - 1);
    for (i, o) in orders.iter().enumerate() {
        assert!(
            o.is_empty(),
            "[B6] node {i} FINALIZED {} coordinates on a wave whose enrolled wave-end ratifiers \
             were {} of a quorum of {quorum} — an UNENROLLED creator supplied the missing \
             ratifier and turned a correct safe stall into a commit: {o:?}",
            o.len(),
            quorum - 1
        );
    }

    // ── THE LIVENESS POLE. Whole committee at the wave end, same outsider present throughout:
    //    the federation finalizes, and no outsider coordinate is in the order.
    let (orders_ok, participants_ok, outsider_ok) = wave_end_short_with_outsider(n, n);
    assert_eq!(participants_ok, participants);
    assert_eq!(outsider_ok, outsider);
    for (i, o) in orders_ok.iter().enumerate() {
        assert!(
            !o.is_empty(),
            "[LIVENESS] node {i} finalized NOTHING with the full committee at the wave end — the \
             ratifier gate must be a pure subtraction of non-members, never a liveness trade"
        );
        assert!(
            o.iter().all(|(c, _)| *c != outsider),
            "[B6] node {i} finalized an UNENROLLED creator's block: {o:?}"
        );
        assert!(
            o.iter().all(|(c, _)| participants.contains(c)),
            "[B6] node {i} finalized a creator outside the committee: {o:?}"
        );
    }
    // The two arms are genuinely different outcomes, so neither assertion is vacuous.
    assert_ne!(
        orders[0].is_empty(),
        orders_ok[0].is_empty(),
        "the scenario must DISTINGUISH the safe stall from the honest commit"
    );
}

// ─── SCENARIO E — an OUTSIDER RELAY must not move the wave clock (the rounds leak) ────

/// Build the relay run and hand back TWO honest nodes' views of it.
///
/// `n` committee members produce three fully-connected rounds. Alongside them, THREE signers that
/// are **not in the committee** produce one block each, chained `r1 <- r2 <- r3` — three blocks,
/// depth three — and ONE honest layer-2 block acks the tip `r3`.
///
/// Node A receives everything. Node B receives the committee's blocks and NOT the relay. Their
/// ENROLLED sub-laces are identical, block for block; the only difference is three blocks from
/// creators node B was never sent — which is exactly the difference dissemination does not rule
/// out, because a non-participant is precisely the creator no honest node is obliged to relay.
///
/// The relay is not an exotic adversary: `finality.rs::enroll_pq` is INSERT-ONLY while
/// `constitution.current.participants` shrinks on a passed membership proposal, so rotated-out
/// validators keep producing exactly these blocks, and this sim puts them in through the same
/// `merge` the live node uses, defeating no check.
fn outsider_relay_two_views(n: usize) -> (Node, Node, Vec<[u8; 32]>, Vec<[u8; 32]>) {
    let keys: Vec<SigningKey> = (0..n).map(|i| key(40 + i as u8)).collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();

    // The relay's three signers, sorted by HYBRID ID. `finalized_order` (lifted verbatim from
    // `poll_finalized_blocks`) builds the ordering projection in `(seq, creator)` order and keeps
    // an ack only if its target was inserted first — so a same-`seq` chain must run
    // creator-ascending or the projection silently drops the very edges under test.
    let mut relay_keys: Vec<SigningKey> = (0..3).map(|i| key(210 + i as u8)).collect();
    relay_keys.sort_by_key(pubkey);
    let relay_ids: Vec<[u8; 32]> = relay_keys.iter().map(pubkey).collect();
    for r in &relay_ids {
        assert!(
            !participants.contains(r),
            "a relay signer must NOT be enrolled — else this scenario has no outsider"
        );
    }

    // The relay chain: one block each, at seq 0, each acking the previous.
    let mut relay: Vec<Block> = Vec::new();
    for (i, sk) in relay_keys.iter().enumerate() {
        let preds: Vec<BlockId> = relay.last().map(|b| vec![b.id()]).unwrap_or_default();
        relay.push(round_block(sk, 0, &preds, &[0x70u8.wrapping_add(i as u8)]));
    }

    // Layer 1: the whole committee, genesis.
    let l1: Vec<Block> = keys
        .iter()
        .enumerate()
        .map(|(i, sk)| round_block(sk, 0, &[], &[0x10, i as u8]))
        .collect();
    let l1_ids: Vec<BlockId> = l1.iter().map(|b| b.id()).collect();

    // Layer 2: the whole committee — and member 0 additionally acks the relay TIP.
    let mut with_relay = l1_ids.clone();
    with_relay.push(relay.last().unwrap().id());
    let l2: Vec<Block> = keys
        .iter()
        .enumerate()
        .map(|(i, sk)| {
            let preds = if i == 0 { &with_relay } else { &l1_ids };
            round_block(sk, 1, preds, &[0x20, i as u8])
        })
        .collect();
    let l2_ids: Vec<BlockId> = l2.iter().map(|b| b.id()).collect();

    // Layer 3 (the wave end at wavelength 3): the whole committee.
    let l3: Vec<Block> = keys
        .iter()
        .enumerate()
        .map(|(i, sk)| round_block(sk, 2, &l2_ids, &[0x30, i as u8]))
        .collect();

    let committee: Vec<&SigningKey> = keys.iter().collect();
    let mut node_a = Node::new("A(+relay)", keys[0].clone(), &committee);

    // Node A: everything, relay first so the delta is causally closed.
    let full: Vec<Block> = relay
        .iter()
        .chain(l1.iter())
        .chain(l2.iter())
        .chain(l3.iter())
        .cloned()
        .collect();
    node_a
        .merge(full)
        .expect("honest nodes accept the outsiders' well-formed, correctly signed blocks");

    // ── Node B: the SAME committee blocks, WITHOUT the relay — member 0's layer-2 ack of `r3`
    //    simply dangles.
    //
    // ⚑ This view is NOT reachable through gossip, and the difference matters. `receive_block` /
    // `receive_block_pinned` both go through `insert_checked`, which refuses a block with an
    // unknown predecessor (`MissingPredecessor`), and `merge` refuses the whole delta
    // (`NotCausallyClosed`) — so a node that holds the acking block necessarily holds the relay,
    // and two GOSSIPING honest nodes cannot differ on it. The reachable route is the RESTART path:
    // `from_checkpoint_trusted` inserts every persisted block straight into the map with no
    // signature check, no roster check and NO CLOSURE CHECK, which is exactly what the enrollment
    // docs in `ordering.rs` and `finality_gate.rs` already say about it. So this is the real
    // function on the real path, not a hand-built lace.
    let enrolled_only: Vec<Block> = l1
        .iter()
        .chain(l2.iter())
        .chain(l3.iter())
        .cloned()
        .collect();
    let mut tips: HashMap<[u8; 32], BlockId> = HashMap::new();
    for b in &enrolled_only {
        tips.insert(b.creator, b.id());
    }
    let ckpt = CheckpointData {
        blocks: enrolled_only.iter().map(|b| b.to_bytes()).collect(),
        tips,
        equivocators: vec![],
        ordered_block_ids: vec![],
        attested_block_ids: vec![],
    };
    let quorum = supermajority_threshold(n);
    let restored = Blocklace::from_checkpoint_trusted(&ckpt, keys[1].clone(), quorum)
        .expect("the restart path reloads a persisted DAG with no closure check");
    let strands: Vec<[u8; 32]> = committee.iter().map(|k| strand_key(k)).collect();
    let node_b = Node {
        name: "B(restarted, no relay)".to_string(),
        lace: restored,
        constitution: ConstitutionManager::new(Constitution::new(strands, 0)),
    };

    (node_a, node_b, participants, relay_ids)
}

/// **THE ROUNDS LEAK, ON THE RUN.** `compute_rounds` maxed over every present predecessor, so a
/// non-participant chain that one honest block acked ADDED DEPTH — and depth is the wave clock:
/// `round_to_wave`, the leader slot, the wave-end round where ratification is counted, and
/// `xsort`'s ordering are all read off it. With a three-deep relay the wave-end round of wave 0
/// contained the relay tip and NOT ONE committee block, so node A finalized nothing while node B —
/// same committee, same blocks, same everything it was allowed to see — finalized the lot.
///
/// That is not wave TIMING. Two honest nodes whose enrolled sub-laces are identical must finalize
/// identically; this is the reduction `tauOrder_deterministic` rests on ("agreement reduces to
/// seeing the same lace"), and non-participants are exactly the creators that reduction cannot
/// quantify over.
///
/// BOTH POLES, in one harness:
///   * the relay changes NOTHING — the two views agree coordinate for coordinate; and
///   * the committee still finalizes all of its own blocks, with no relay coordinate ordered.
///
/// Verified twin: `BlocklaceFinality.traceRelayStall` / `traceOrderFork` and the `#guard` red/green
/// pairs on `tauOrderPreRounds` vs `tauOrder`. The RED half is executed in-tree by
/// `ordering::tests::compute_rounds_gives_a_nonparticipant_relay_no_depth`, which runs THIS
/// module's `compute_rounds` at the pre-repair parameter.
#[test]
fn outsider_relay_cannot_shift_the_wave_clock() {
    let n = 3;
    let (node_a, node_b, participants, relay_ids) = outsider_relay_two_views(n);

    // ANTI-VACUITY — the relay really is in A's lace, really is three blocks by three DISTINCT
    // unenrolled creators, and really is acked by an honest block. A refusal that came from the
    // blocks being absent would say nothing about the finality rule.
    let in_a: Vec<[u8; 32]> = node_a
        .lace
        .iter()
        .map(|(_, b)| b.creator)
        .filter(|c| relay_ids.contains(c))
        .collect();
    assert_eq!(in_a.len(), 3, "all three relay blocks must be in A's lace");
    assert!(
        node_b
            .lace
            .iter()
            .all(|(_, b)| !relay_ids.contains(&b.creator)),
        "B must not hold any relay block — that is the whole difference between the two views"
    );
    // The two nodes' ENROLLED sub-laces are identical, block id for block id.
    let enrolled_of = |nd: &Node| -> Vec<([u8; 32], u64)> {
        let mut v: Vec<([u8; 32], u64)> = nd
            .lace
            .iter()
            .filter(|(_, b)| participants.contains(&b.creator))
            .map(|(_, b)| (b.creator, b.seq))
            .collect();
        v.sort();
        v
    };
    assert_eq!(
        enrolled_of(&node_a),
        enrolled_of(&node_b),
        "the two views must differ ONLY by the outsider blocks"
    );
    // …and an honest block genuinely ACKS the relay tip, so the relay is load-bearing in the
    // honest leader's causal past and cannot be refused by ignoring an unreferenced subgraph.
    let relay_tip_acked = node_a.lace.iter().any(|(_, b)| {
        participants.contains(&b.creator)
            && b.predecessors.iter().any(|p| {
                node_a
                    .lace
                    .iter()
                    .any(|(id, rb)| id == p && relay_ids.contains(&rb.creator))
            })
    });
    assert!(
        relay_tip_acked,
        "an honest block must ack the relay — else the relay cannot reach the wave clock"
    );

    // ── THE REFUSAL: the outsider relay no longer moves the wave clock. Both views finalize the
    //    SAME coordinates, in the SAME round cohorts, and BOTH finalize (before the repair the
    //    view holding the relay finalized NOTHING — the wave-end round was occupied by the relay
    //    tip and by no committee block at all; see
    //    `ordering::tests::compute_rounds_gives_a_nonparticipant_relay_no_depth`).
    let order_a = node_a.finalized(&participants);
    let order_b = node_b.finalized(&participants);
    assert!(
        !order_a.is_empty() && !order_b.is_empty(),
        "[LIVENESS] a three-block outsider relay must not stall a healthy committee: A={} B={}",
        order_a.len(),
        order_b.len()
    );
    assert_eq!(
        order_a.len(),
        3 * n,
        "[LIVENESS] the committee must still finalize all {} of its blocks; got {order_a:?}",
        3 * n
    );
    assert!(
        order_a.iter().all(|(c, _)| participants.contains(c)),
        "no outsider coordinate may be finalized: {order_a:?}"
    );
    let set = |o: &[([u8; 32], u64)]| -> Vec<([u8; 32], u64)> {
        let mut v = o.to_vec();
        v.sort();
        v
    };
    assert_eq!(
        set(&order_a),
        set(&order_b),
        "[ROUNDS LEAK] the two views must finalize the SAME coordinates"
    );
    // The load-bearing level, and the one the Lean↔Rust differential is stated at: the sequence of
    // ROUND COHORTS and each cohort's creator set. This is what the wave clock decides, and it is
    // now identical on the two views.
    let cohorts = |o: &[([u8; 32], u64)]| -> Vec<(u64, Vec<[u8; 32]>)> {
        let mut out: Vec<(u64, Vec<[u8; 32]>)> = Vec::new();
        for (c, seq) in o {
            match out.last_mut() {
                Some((s, members)) if s == seq => members.push(*c),
                _ => out.push((*seq, vec![*c])),
            }
        }
        for (_, members) in out.iter_mut() {
            members.sort();
        }
        out
    };
    assert_eq!(
        cohorts(&order_a),
        cohorts(&order_b),
        "[ROUNDS LEAK] the round-cohort structure must be a function of the ENROLLED sub-lace"
    );

    // ── ⚠ MEASURED RESIDUAL — NOT this defect, and NOT closed here.
    //
    // The two orders are still not EQUAL: within a cohort they differ. The cause is not the wave
    // clock (the cohorts above are identical) and not `xsort`'s algorithm — it is the projection
    // `poll_finalized_blocks` builds. It re-hashes every block over only the predecessors that
    // RESOLVED in this node's lace, so the acking block gets a different ordering-lace id on a
    // node that does not hold the relay, that id is `xsort`'s tie-break, and the difference
    // cascades into every block that acks it. Measured, not inferred:
    let ids_a = ordering_projection_ids(&node_a.lace);
    let ids_b = ordering_projection_ids(&node_b.lace);
    let acker = participants[0];
    assert_ne!(
        ids_a.get(&(acker, 1)),
        ids_b.get(&(acker, 1)),
        "the mechanism under test: the acking block's ORDERING-LACE id must differ between the \
         two views (if this ever becomes equal the residual below is closed and this test should \
         assert order equality instead)"
    );
    assert_eq!(
        ids_a.get(&(participants[1], 0)),
        ids_b.get(&(participants[1], 0)),
        "anti-vacuity: a block with no dangling ack keeps the SAME projection id in both views"
    );
    // Two consequences, both out of scope for the wave-clock pass and both named:
    //   * `from_checkpoint_trusted` can produce a lace that is NOT causally closed at all — the
    //     gossip paths (`insert_checked`, `merge`) both refuse one — which is what puts the two
    //     views in different states in the first place;
    //   * the ordering projection's content address is therefore a function of the VIEW, not of
    //     the block, so `xsort`'s deterministic tie-break is deterministic per node and not across
    //     nodes. Fixing that means keying the projection by the FINALITY block id (a stable
    //     content address) instead of re-hashing — `node/src/blocklace_sync.rs`, a different pass.
}

// ─── META-tests: the property checkers are NON-VACUOUS (they reject the fault) ──

#[test]
fn harness_meta_safety_check_rejects_a_planted_fork() {
    // Two "nodes" that finalized conflicting histories (they agree at position 0
    // then diverge) MUST be flagged by the safety checker. If `find_fork` returned
    // `None` here, every SAFETY assertion above would be vacuous.
    let a = pubkey(&key(1));
    let b = pubkey(&key(2));
    let order_x = vec![(a, 0u64), (a, 1), (b, 2)];
    let order_y = vec![(a, 0u64), (a, 1), (a, 2)]; // diverges at position 2
    assert!(
        !prefix_consistent(&order_x, &order_y),
        "planted fork must be inconsistent"
    );
    assert_eq!(
        find_fork(&[order_x.clone(), order_y.clone()]),
        Some((0, 1)),
        "find_fork MUST catch the planted conflicting finalization"
    );
    // A behind-but-consistent node (a strict prefix) is NOT a fork.
    let order_behind = vec![(a, 0u64), (a, 1)];
    assert!(prefix_consistent(&order_x, &order_behind));
    assert_eq!(
        find_fork(&[order_x, order_behind]),
        None,
        "a lagging node is not a fork"
    );
}

#[test]
fn harness_meta_liveness_and_stall_are_distinguishable() {
    // The kill sim must produce a genuinely NON-EMPTY order when a quorum is up and
    // a genuinely EMPTY order below quorum — otherwise the LIVENESS / TOLERANCE
    // assertions could not tell "finalized" from "stalled" and would be vacuous.
    let n = 4;
    let f = fault_budget(n);
    let (up, _) = kill_scenario(n, f, 12);
    let (down, _) = kill_scenario(n, f + 1, 12);
    let up_nonempty = up.iter().all(|o| !o.is_empty());
    let down_empty = down.iter().all(|o| o.is_empty());
    assert!(
        up_nonempty && down_empty,
        "the sim must DISTINGUISH finalize (quorum up) from stall (below quorum)"
    );
    // And the two are not the same trivial output.
    assert_ne!(up[0].is_empty(), down[0].is_empty());
}

// ─── SOAK: a wider sweep over committee sizes (heavier; opt-in) ────────────────

#[test]
#[ignore = "soak: run with `cargo test -p dregg-blocklace -- --ignored`"]
fn soak_kill_tolerance_sweep_across_committee_sizes() {
    for n in [4usize, 5, 7, 10] {
        let f = fault_budget(n);
        // kill f ⇒ finalize
        let (up, alive_up) = kill_scenario(n, f, 15);
        assert_eq!(alive_up, supermajority_threshold(n));
        assert!(
            up.iter().all(|o| !o.is_empty()),
            "n={n}: kill f={f} must finalize (quorum {alive_up} up)"
        );
        // kill f+1 ⇒ stall
        let (down, _) = kill_scenario(n, f + 1, 15);
        assert!(
            down.iter().all(|o| o.is_empty()),
            "n={n}: kill f+1={} must stall (below quorum)",
            f + 1
        );
    }
}
