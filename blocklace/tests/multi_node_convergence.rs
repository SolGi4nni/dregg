//! Multi-node integration test: partition → heal → equivocate → converge.
//!
//! This drives the REAL consensus engine the live node runs in
//! `dregg-node::blocklace_sync` — no mocks, no shadows:
//!
//! * [`dregg_blocklace::finality::Blocklace`] — the A1-fixed insert/merge path
//!   (signature + per-creator sequence + equivocation detection, evidence
//!   retained not lost). This is the exact type `BlocklaceHandle.lace` holds.
//! * [`dregg_blocklace::ordering::tau`] — the Cordial-Miners total-order rule
//!   the node's `poll_finalized_blocks` runs (via `build_ordering_blocklace`,
//!   mirrored here by [`finalized_order`]). Its safety is machine-checked in
//!   `metatheory/Dregg2/Distributed/BlocklaceFinality.lean`
//!   (`finalLeaders_one_per_wave`, `tauOrder_deterministic`, equivocator
//!   exclusion `finalLeaderAt_needs_unique_candidate`).
//! * [`dregg_blocklace::constitution::ConstitutionManager::auto_evict`] — the
//!   membership reaction the node fires from `handle_push` when an
//!   `EquivocationProof` surfaces.
//!
//! # The properties asserted (the load-bearing guarantees)
//!
//! 1. **Catch-up convergence = LaceMerge.** A node that was partitioned and
//!    then receives the causally-closed delta reaches the SAME blocklace KEYSET
//!    as the never-partitioned nodes, hence (since `tau` is a deterministic
//!    function of `(keyset, participants)` —
//!    `BlocklaceFinality.tauOrder_deterministic`) the SAME finalized order, hence
//!    the same executed finalized state. This is
//!    `Distributed/LaceMerge.merge_convergence_to_state` applied to a real
//!    catch-up: "a caught-up node reaching the same finalized state IS LaceMerge
//!    convergence."
//!
//! 2. **Equivocator detection + exclusion = StrandIntegrity / BlocklaceFinality.**
//!    A creator that forks (two distinct blocks at one `(creator, seq)`) is
//!    detected on insert (`EquivocationProof` retained as evidence), auto-evicted
//!    from the constitution, and — crucially — contributes NO block to the
//!    finalized `tau` order on the honest nodes. The honest nodes still agree
//!    with each other. This is the node-level witness of
//!    `BlocklaceFinality.finalLeaderAt_needs_unique_candidate` ("an equivocating
//!    leader anchors nothing") and the Rust `ordering::tests::
//!    test_tau_differential_equivocator_excluded`.
//!
//! The DAG is produced ROUND-SYNCHRONOUSLY (each round, every honest creator
//! authors one block pointing at ALL of the previous round's blocks). This is the
//! exact shape `ordering::tests::build_full_blocklace` uses — the trace the
//! Rust↔Lean `tau` differential is proven against — so the federation reaches the
//! wave depth at which `tau` finalizes. The convergence/exclusion guarantees
//! themselves do not depend on this shape; it just guarantees a non-trivial
//! finalized prefix to assert against.

use std::collections::HashSet;

use dregg_blocklace::constitution::{Constitution, ConstitutionManager};
use dregg_blocklace::finality::{Block, BlockError, BlockId, Blocklace, MergeError, Payload};
use ed25519_dalek::SigningKey;

// ─── Test scaffolding ────────────────────────────────────────────────────────

fn key(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

fn pubkey(sk: &SigningKey) -> [u8; 32] {
    sk.verifying_key().to_bytes()
}

/// One in-process node: a finality blocklace (the live consensus state) plus the
/// constitution manager that reacts to membership events — exactly the pair the
/// real node holds in `BlocklaceHandle { lace, constitution, .. }`.
struct Node {
    name: &'static str,
    lace: Blocklace,
    constitution: ConstitutionManager,
}

impl Node {
    fn new(name: &'static str, sk: SigningKey, participants: Vec<[u8; 32]>) -> Self {
        let quorum = if participants.len() <= 1 {
            1
        } else {
            (participants.len() * 2 / 3) + 1
        };
        let constitution = Constitution::new(participants.clone(), 0);
        Node {
            name,
            lace: Blocklace::new(sk, quorum),
            constitution: ConstitutionManager::new(constitution),
        }
    }

    /// Receive one block as the live node does, mirroring `handle_push`'s
    /// equivocation reaction: on an `Equivocation` error the block is RETAINED as
    /// evidence (the lace keeps it) and the creator is auto-evicted from the
    /// constitution. Returns `true` if an equivocation was surfaced+evicted.
    fn receive(&mut self, block: Block) -> bool {
        match self.lace.receive_block(block) {
            Ok(()) => false,
            Err(BlockError::Equivocation { proof, .. }) => {
                // This is precisely `node/src/blocklace_sync.rs::handle_push`'s
                // `outcome.equivocations` loop calling `constitution.auto_evict`.
                self.constitution.auto_evict(&proof);
                true
            }
            Err(e) => panic!("[{}] unexpected receive error: {e:?}", self.name),
        }
    }

    /// Merge a causally-closed delta the way the node's catch-up path does
    /// (`Blocklace::merge` topologically sorts + closure-checks the batch — the
    /// engine the node calls under `apply_with_buffering`). Out-of-order / mixed
    /// batches are fine; `merge` orders them. Returns the merge result.
    fn merge(&mut self, delta: Vec<Block>) -> Result<(), MergeError> {
        self.lace.merge(delta)
    }

    /// The content-addressed keyset of this node's lace (the CRDT observable of
    /// `Distributed/LaceMerge.lean` — convergence is keyset equality).
    fn keyset(&self) -> HashSet<BlockId> {
        self.lace.iter().map(|(id, _)| *id).collect()
    }

    /// The finalized total order as `(creator, seq)` pairs — the node's
    /// `poll_finalized_blocks` observable.
    fn finalized(&self, participants: &[[u8; 32]]) -> Vec<([u8; 32], u64)> {
        finalized_order(&self.lace, participants)
    }
}

/// A round-synchronous block authored by `sk` at `seq`, pointing at every block
/// of the previous round (`preds`). Signed, so verified `receive_block`/`merge`
/// accept it — exactly the full-cross-link shape `tau` finalizes over.
fn round_block(sk: &SigningKey, seq: u64, preds: &[BlockId], tag: &[u8]) -> Block {
    Block::new(sk, seq, Payload::Turn(tag.to_vec()), preds.to_vec())
}

/// Compute the finalized `(creator, seq)` order from a finality blocklace, EXACTLY
/// as the node's `blocklace_sync::poll_finalized_blocks` does: build the unsigned
/// ordering projection (`ordering::Blocklace` via `insert_unverified`), run
/// `ordering::tau`, map ids back. Lifted here verbatim so the test exercises the
/// node's real finalization rule rather than a re-derivation.
fn finalized_order(finality_lace: &Blocklace, participants: &[[u8; 32]]) -> Vec<([u8; 32], u64)> {
    use std::collections::HashMap;

    let mut ordering_lace = dregg_blocklace::Blocklace::new();
    let mut finality_to_ordering: HashMap<BlockId, dregg_blocklace::BlockId> = HashMap::new();
    let mut ordering_to_cs: HashMap<dregg_blocklace::BlockId, ([u8; 32], u64)> = HashMap::new();

    // Topological insertion (by seq, then creator) — matches build_ordering_blocklace.
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

/// Build a round-synchronous DAG for `keys` over `rounds` rounds. Returns the
/// blocks grouped by round (round 0 first). Round 0 blocks are genesis (no
/// predecessors); round r blocks point at ALL round r-1 blocks. This is the
/// `build_full_blocklace` shape the Rust↔Lean `tau` differential is proven on.
fn build_rounds(keys: &[&SigningKey], rounds: u64) -> Vec<Vec<Block>> {
    let mut by_round: Vec<Vec<Block>> = Vec::new();
    for r in 0..rounds {
        let preds: Vec<BlockId> = if r == 0 {
            vec![]
        } else {
            by_round[(r - 1) as usize].iter().map(|b| b.id()).collect()
        };
        let mut round = Vec::new();
        for (i, sk) in keys.iter().enumerate() {
            let tag = [r as u8, i as u8];
            round.push(round_block(sk, r, &preds, &tag));
        }
        by_round.push(round);
    }
    by_round
}

/// Flatten round-grouped blocks into a single causally-ordered vec.
fn flatten(by_round: &[Vec<Block>]) -> Vec<Block> {
    by_round.iter().flatten().cloned().collect()
}

// ─── The integration test ────────────────────────────────────────────────────

/// Full lifecycle: 3 honest-start nodes, a partition that isolates one node, a
/// heal, then an equivocation injected by one creator. Asserts honest
/// convergence to identical finalized state AND equivocator detection/exclusion.
#[test]
fn three_nodes_partition_heal_equivocate_converge() {
    // ── Setup: 3 participants A, B, C ──────────────────────────────────────
    let sk_a = key(1);
    let sk_b = key(2);
    let sk_c = key(3);
    let pk_a = pubkey(&sk_a);
    let pk_b = pubkey(&sk_b);
    let pk_c = pubkey(&sk_c);
    let participants = vec![pk_a, pk_b, pk_c];

    let mut node_a = Node::new("A", sk_a.clone(), participants.clone());
    let mut node_b = Node::new("B", sk_b.clone(), participants.clone());
    let mut node_c = Node::new("C", sk_c.clone(), participants.clone());

    // ── Phase 1: pre-partition — 4 round-synchronous rounds, fully shared ──
    // Every node ends up with the identical pre-partition DAG.
    let pre = build_rounds(&[&sk_a, &sk_b, &sk_c], 4);
    let pre_flat = flatten(&pre);
    node_a
        .merge(pre_flat.clone())
        .expect("A merges pre-partition DAG");
    node_b
        .merge(pre_flat.clone())
        .expect("B merges pre-partition DAG");
    node_c
        .merge(pre_flat.clone())
        .expect("C merges pre-partition DAG");

    assert_eq!(node_a.keyset(), node_b.keyset(), "A,B agree pre-partition");
    assert_eq!(node_b.keyset(), node_c.keyset(), "B,C agree pre-partition");

    // The pre-partition prefix already finalizes a non-trivial order.
    let fin_pre = node_a.finalized(&participants);
    assert!(
        !fin_pre.is_empty(),
        "the round-synchronous DAG must finalize a non-trivial prefix"
    );

    // ── Phase 2: PARTITION — A and B continue; C is isolated ───────────────
    // A and B extend the chain together (their shared sub-federation keeps
    // producing rounds that point at the last shared round). C, isolated, does
    // not see these rounds. We build the A+B extension as a continuation whose
    // round-4 predecessors are the last fully-shared round (round 3).
    let last_shared: Vec<BlockId> = pre[3].iter().map(|b| b.id()).collect();
    // A+B produce 3 more synchronous rounds among themselves (seqs 4,5,6).
    let mut ab_ext: Vec<Vec<Block>> = Vec::new();
    for r in 4u64..7 {
        let preds: Vec<BlockId> = if r == 4 {
            last_shared.clone()
        } else {
            ab_ext[(r - 4 - 1) as usize]
                .iter()
                .map(|b| b.id())
                .collect()
        };
        ab_ext.push(vec![
            round_block(&sk_a, r, &preds, &[r as u8, 0]),
            round_block(&sk_b, r, &preds, &[r as u8, 1]),
        ]);
    }
    let ab_ext_flat = flatten(&ab_ext);
    node_a
        .merge(ab_ext_flat.clone())
        .expect("A merges A+B extension");
    node_b
        .merge(ab_ext_flat.clone())
        .expect("B merges A+B extension");

    // During the partition, C's keyset diverges from A/B.
    assert_ne!(
        node_c.keyset(),
        node_a.keyset(),
        "C must diverge while partitioned"
    );
    // A and B (the connected side) agree throughout the partition.
    assert_eq!(
        node_a.keyset(),
        node_b.keyset(),
        "A,B stay consistent under partition"
    );

    // ── Phase 3: HEAL — deliver the missed delta to C ─────────────────────
    // The partition heals. C receives the A+B extension (its causal past — the
    // pre-partition rounds — is already present, so the delta is closed). The
    // engine's `merge` orders it. This is the node's catch-up `handle_push`.
    node_c
        .merge(ab_ext_flat.clone())
        .expect("C catches up on the missed delta");

    // CONVERGENCE (LaceMerge): all three keysets are now identical.
    assert_eq!(node_a.keyset(), node_b.keyset(), "A,B converge after heal");
    assert_eq!(
        node_b.keyset(),
        node_c.keyset(),
        "C catches up to the merged keyset after heal (LaceMerge convergence)"
    );

    // FINALIZED-STATE AGREEMENT: same keyset ⇒ same tau order ⇒ same finalized
    // state. This is the node's `poll_finalized_blocks` observable.
    let fin_a = node_a.finalized(&participants);
    let fin_b = node_b.finalized(&participants);
    let fin_c = node_c.finalized(&participants);
    assert_eq!(fin_a, fin_b, "honest A,B finalize identically post-heal");
    assert_eq!(fin_b, fin_c, "caught-up C finalizes identically post-heal");
    assert!(!fin_a.is_empty(), "the federation finalized turns");
    // Catch-up cannot regress the finalized prefix (monotonicity): everything
    // finalized pre-partition stays finalized after the heal.
    for entry in &fin_pre {
        assert!(
            fin_a.contains(entry),
            "pre-partition finalized entry {entry:?} must survive the heal"
        );
    }

    // ── Phase 4: EQUIVOCATION — creator C forks ───────────────────────────
    // C authors TWO distinct blocks at the SAME (creator, seq): a fork. They
    // share predecessors + seq but differ in body, so they share (creator, seq)
    // and differ in id — the equivocation witness.
    let fork_seq = 7u64;
    let fork_preds: Vec<BlockId> = ab_ext[2].iter().map(|b| b.id()).collect(); // last round tips
    let fork_left = round_block(&sk_c, fork_seq, &fork_preds, b"FORK-LEFT");
    let fork_right = round_block(&sk_c, fork_seq, &fork_preds, b"FORK-RIGHT");
    assert_ne!(
        fork_left.id(),
        fork_right.id(),
        "the two forks are distinct blocks"
    );

    // A receives the left fork first (clean), then the right fork (DETECTED).
    assert!(
        !node_a.receive(fork_left.clone()),
        "first fork block inserts cleanly"
    );
    assert!(
        node_a.receive(fork_right.clone()),
        "A must DETECT C's equivocation on the conflicting block"
    );

    // B receives the forks in the OPPOSITE order — detection is order-independent.
    node_b.receive(fork_right.clone());
    assert!(
        node_b.receive(fork_left.clone()),
        "B must detect the same equivocation regardless of arrival order"
    );

    // DETECTION: both honest nodes recorded C as an equivocator (evidence kept).
    assert!(
        node_a.lace.equivocators().contains(&pk_c),
        "A records C as an equivocator"
    );
    assert!(
        node_b.lace.equivocators().contains(&pk_c),
        "B records C as an equivocator"
    );
    // Evidence is RETAINED, not lost: both forks live in the lace.
    assert!(node_a.lace.contains(&fork_left.id()) && node_a.lace.contains(&fork_right.id()));

    // EXCLUSION (membership): the equivocator is auto-evicted from the constitution.
    assert!(
        !node_a.constitution.current.is_participant(&pk_c),
        "A auto-evicts equivocator C from the constitution"
    );
    assert!(
        !node_b.constitution.current.is_participant(&pk_c),
        "B auto-evicts equivocator C from the constitution"
    );
    // Honest A and B remain participants.
    assert!(node_a.constitution.current.is_participant(&pk_a));
    assert!(node_a.constitution.current.is_participant(&pk_b));

    // EXCLUSION (finalized order): no forked block from C at the fork seq anchors
    // anything, and the two honest nodes STILL agree with each other (safety
    // survives the fault).
    let fin_a2 = node_a.finalized(&participants);
    let fin_b2 = node_b.finalized(&participants);
    assert_eq!(
        fin_a2, fin_b2,
        "honest nodes A,B still finalize identically AFTER the equivocation"
    );
    assert!(
        !fin_a2
            .iter()
            .any(|(creator, seq)| *creator == pk_c && *seq == fork_seq),
        "neither fork from the equivocator is finalized (an equivocating leader anchors nothing)"
    );
    // The pre-fork finalized prefix is preserved (tau's finalized prefix is monotone).
    for entry in &fin_a {
        assert!(
            fin_a2.contains(entry),
            "pre-fork finalized entry {entry:?} must remain finalized after the fault"
        );
    }
}

/// Focused convergence test (the `n>1` catch-up leg in isolation): a fresh node
/// that joins LATE receives the whole causally-closed history and lands on the
/// identical finalized state — the direct node-level witness of
/// `LaceMerge.merge_convergence_to_state`.
#[test]
fn late_joiner_catches_up_to_identical_finalized_state() {
    let sk_a = key(10);
    let sk_b = key(11);
    let sk_c = key(12);
    let pk_a = pubkey(&sk_a);
    let pk_b = pubkey(&sk_b);
    let pk_c = pubkey(&sk_c);
    let participants = vec![pk_a, pk_b, pk_c];

    // A and B (and C's slot) produce a round-synchronous DAG. C is offline and
    // produces nothing, but the DAG still finalizes on the A/B coverage.
    let dag = build_rounds(&[&sk_a, &sk_b, &sk_c], 4);
    let history = flatten(&dag);

    let mut node_a = Node::new("A", sk_a.clone(), participants.clone());
    let mut node_b = Node::new("B", sk_b.clone(), participants.clone());
    node_a.merge(history.clone()).unwrap();
    node_b.merge(history.clone()).unwrap();

    // The late joiner D (a fresh replica) starts empty and catches up by merging
    // the full history — delivered REVERSED to stress the engine's topological
    // ordering in `merge`.
    let sk_d = key(13);
    let mut node_d = Node::new("D", sk_d, participants.clone());
    let mut reversed = history.clone();
    reversed.reverse();
    node_d.merge(reversed).unwrap();

    // D's keyset equals A's and B's (it caught up).
    assert_eq!(node_d.keyset(), node_a.keyset());
    assert_eq!(node_d.keyset(), node_b.keyset());

    // And therefore D's finalized order equals the established nodes' — a caught-up
    // node reaching the same finalized state IS LaceMerge convergence.
    let fin_a = node_a.finalized(&participants);
    let fin_d = node_d.finalized(&participants);
    assert_eq!(
        fin_a, fin_d,
        "late joiner finalizes identically to the established node"
    );
    assert!(!fin_a.is_empty());
}

/// Redundant / reordered delivery is inert (CRDT idempotence + commutativity at
/// the node level): delivering the same closed set twice, in different orders,
/// does not change the keyset or the finalized order.
#[test]
fn redundant_reordered_delivery_is_inert() {
    let sk_a = key(20);
    let sk_b = key(21);
    let sk_c = key(22);
    let pk_a = pubkey(&sk_a);
    let pk_b = pubkey(&sk_b);
    let pk_c = pubkey(&sk_c);
    let participants = vec![pk_a, pk_b, pk_c];

    let dag = build_rounds(&[&sk_a, &sk_b, &sk_c], 4);
    let history = flatten(&dag);

    let sk_d = key(23);
    let mut node_d = Node::new("D", sk_d, participants.clone());
    node_d.merge(history.clone()).unwrap();
    let keyset_once = node_d.keyset();
    let fin_once = node_d.finalized(&participants);
    assert!(!fin_once.is_empty());

    // Deliver again, reversed; and again rotated. Each must be inert.
    let mut reversed = history.clone();
    reversed.reverse();
    node_d.merge(reversed).unwrap();
    let mut rotated = history.clone();
    rotated.rotate_left(3);
    node_d.merge(rotated).unwrap();

    assert_eq!(
        node_d.keyset(),
        keyset_once,
        "redundant delivery leaves keyset unchanged"
    );
    assert_eq!(
        node_d.finalized(&participants),
        fin_once,
        "redundant/reordered delivery leaves the finalized order unchanged"
    );
}
