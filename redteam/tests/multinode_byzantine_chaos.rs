//! # Multi-node Byzantine chaos — the operational test of the distributed invariants.
//!
//! Part A of the MULTI-NODE BYZANTINE CHAOS red-team. This builds an *in-process
//! cluster* of real `dregg_blocklace::finality::Lace` nodes (the SAME reception
//! path the running node drives: `node/src/blocklace_sync.rs::handle_push` →
//! `finality.rs::receive_block` / `merge`) and runs adversarial network chaos
//! against them. It then asserts — OPERATIONALLY, against the running Rust, not
//! just in Lean — the three distributed properties the metatheory proves:
//!
//!   * **CatchupConverges** (`Dregg2/Distributed/CatchupConverges.lean`): a node
//!     that receives the same causally-closed set of finalized blocks (in ANY
//!     arrival order, ANY delta grouping, ANY buffering) reaches the SAME
//!     finalized state as any peer. The operational witness of "same finalized
//!     state" is: identical content-addressed block-id keyset ⇒ identical tau
//!     ordering ⇒ identical executed state (the `catchup_converges_to_leader`
//!     chain). We check the keyset + the per-creator tip map + the equivocator
//!     set, which together pin the lace's finalized projection.
//!
//!   * **StrandIntegrity** (`Dregg2/Distributed/StrandIntegrity.lean`): the per-
//!     creator SSB feed is append-only, Ed25519-signed, monotone-sequence, and a
//!     second distinct block at one `(creator, seq)` is RETAINED as detectable
//!     `EquivocationProof` with the tip WITHDRAWN (never silently overwritten —
//!     the audit-A1 fix). We attack the write path (`Blocklace::insert` /
//!     `Lace::receive_block`) with forks and assert detection + tip withdrawal.
//!
//!   * **finality / Byzantine exclusion**: the equivocator is detected and
//!     excluded from honest tip state, while honest nodes still converge.
//!
//! ## What makes this a RED-TEAM and not a demo
//!
//! Every test genuinely tries to BREAK the property: it constructs the *worst*
//! arrival order, the equivocation that would slip past a naive single-tip
//! overwrite, the partition that would diverge two honest nodes, the replay that
//! would double-count, the flood that would OOM or desync, the eclipse that
//! would starve a node. A break that SUCCEEDS is asserted as a FINDING (panic
//! with a precise message); a break that FAILS is asserted as EVIDENCE the
//! property holds on the running Rust. The Lean proofs are about the abstract
//! model; these tests are the projection check onto the concrete code.

use std::collections::HashSet;

use dregg_blocklace::finality::{Block, BlockId, Blocklace as Lace, Payload};
use ed25519_dalek::SigningKey;

// ─────────────────────────────────────────────────────────────────────────────
// Cluster + chaos-network model
// ─────────────────────────────────────────────────────────────────────────────

/// A deterministic keypair for a node, seeded so tests are reproducible.
/// The seed is a `u16` so node ids (100..800) and participant ids (10..80) both
/// fit and stay distinct; it is splayed across the 32 seed bytes little-endian.
fn key(seed: u16) -> SigningKey {
    let [lo, hi] = seed.to_le_bytes();
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        *b = if i % 2 == 0 { lo } else { hi };
    }
    SigningKey::from_bytes(&bytes)
}

/// A node in the in-process cluster: a real `Lace` plus its identity. The `Lace`
/// IS the node's view of the distributed log — the exact type the running node
/// holds (`node/src/state.rs` wraps one per federation group).
struct Node {
    lace: Lace,
    #[allow(dead_code)]
    id: u16,
}

impl Node {
    fn new(id: u16) -> Self {
        // quorum_threshold 1: solo-finality semantics, matching the devnet's
        // `federation_mode: solo`. Convergence/equivocation logic is independent
        // of the threshold; the threshold only gates the Attested level.
        Node {
            lace: Lace::new_simple(key(id)),
            id,
        }
    }

    /// The content-addressed finalized keyset: the set of block ids this node has
    /// accepted. CatchupConverges proves this set (not the arrival history)
    /// determines the finalized executed state.
    fn keyset(&self) -> HashSet<BlockId> {
        self.lace.iter().map(|(id, _)| *id).collect()
    }

    /// The honest per-creator tip map (the SSB feed heads). Equivocators have NO
    /// tip (withdrawn on detection), so this is the honest finalized frontier.
    fn tips(&self) -> std::collections::HashMap<[u8; 32], BlockId> {
        self.lace.tips().clone()
    }

    fn equivocators(&self) -> HashSet<[u8; 32]> {
        self.lace.equivocators().iter().copied().collect()
    }
}

/// Deliver one block to a node via the REAL reception path with causal
/// buffering: if predecessors are missing, hold it and retry after later
/// deliveries land (exactly what `catchup.rs::OrphanBuffer` does). Returns
/// whether the block (eventually, after this and prior buffered deliveries) was
/// admitted or is still orphaned.
///
/// We model the orphan buffer inline (rather than importing `node::catchup`,
/// which the SWAP workflow owns) by retrying the whole pending set whenever a
/// new block lands — same fixpoint, same admitted SET.
struct Inbox {
    pending: Vec<Block>,
}

impl Inbox {
    fn new() -> Self {
        Inbox {
            pending: Vec::new(),
        }
    }

    /// Push a block into the node, draining any now-satisfiable orphans. Uses
    /// `receive_block` (the wire reception path that re-verifies sig/seq/equiv).
    fn deliver(&mut self, node: &mut Node, block: Block) {
        self.pending.push(block);
        // Fixpoint: keep trying pending blocks until no progress. Each accepted
        // block may unblock orphans whose predecessors just landed.
        loop {
            let mut progressed = false;
            let mut still_pending = Vec::new();
            for b in std::mem::take(&mut self.pending) {
                let preds_present = b.predecessors.iter().all(|p| node.lace.contains(p));
                if preds_present {
                    // Predecessors present: feed the real reception path. An
                    // equivocation/forged-sig is REJECTED here (Err) but the
                    // block may still be retained as evidence (the A1 path).
                    let _ = node.lace.receive_block(b);
                    progressed = true;
                } else {
                    still_pending.push(b);
                }
            }
            self.pending = still_pending;
            if !progressed {
                break;
            }
        }
    }
}

/// Build a signed honest strand of `n` blocks for `signer`, each `Turn(payload)`
/// extending the previous (a real SSB feed). Returns the blocks in causal order.
fn honest_strand(signer: &SigningKey, n: u64, seed: u8) -> Vec<Block> {
    let mut blocks = Vec::new();
    let mut preds: Vec<BlockId> = Vec::new();
    for seq in 0..n {
        let payload = Payload::Turn(vec![seed, seq as u8, 0xAB]);
        let b = Block::new(signer, seq, payload, preds.clone());
        preds = vec![b.id()];
        blocks.push(b);
    }
    blocks
}

// ─────────────────────────────────────────────────────────────────────────────
// ATTACK 1 — out-of-order + chunked delivery must converge (CatchupConverges)
// ─────────────────────────────────────────────────────────────────────────────

/// Two honest nodes receive the SAME block set in DIFFERENT, adversarially-bad
/// orders (one reversed, one shuffled, with buffering). If CatchupConverges held
/// only in Lean but the Rust reception path admitted/dropped blocks order-
/// dependently, the keysets would diverge — a real bug. We assert byte-identical
/// keyset + tip map.
#[test]
fn attack_out_of_order_delivery_converges() {
    let a = key(10);
    let b = key(11);
    let c = key(12);
    // Three interleaved honest strands → a non-trivial DAG.
    let mut all: Vec<Block> = Vec::new();
    all.extend(honest_strand(&a, 4, 1));
    all.extend(honest_strand(&b, 4, 2));
    all.extend(honest_strand(&c, 4, 3));

    let mut node_fwd = Node::new(100);
    let mut node_rev = Node::new(101);
    let mut inbox_fwd = Inbox::new();
    let mut inbox_rev = Inbox::new();

    // Node 1: forward order.
    for blk in all.iter().cloned() {
        inbox_fwd.deliver(&mut node_fwd, blk);
    }
    // Node 2: REVERSED order (worst case for causal closure — every block
    // arrives before its predecessor and must be buffered).
    for blk in all.iter().rev().cloned() {
        inbox_rev.deliver(&mut node_rev, blk);
    }

    // No orphans should remain stuck: the set is causally closed, so buffering
    // must fully drain. A stuck orphan = the buffering fixpoint diverged.
    assert!(
        inbox_fwd.pending.is_empty() && inbox_rev.pending.is_empty(),
        "FINDING: causal buffering did not drain a closed set (orphans stuck: fwd={}, rev={})",
        inbox_fwd.pending.len(),
        inbox_rev.pending.len()
    );

    assert_eq!(
        node_fwd.keyset(),
        node_rev.keyset(),
        "FINDING(CatchupConverges BROKEN): two honest nodes given the same closed block set in \
         different arrival orders reached DIFFERENT keysets — finalized state is order-dependent"
    );
    assert_eq!(
        node_fwd.tips(),
        node_rev.tips(),
        "FINDING(CatchupConverges BROKEN): honest tip frontiers diverged under reordering"
    );
    // 12 blocks total, all honest, all admitted.
    assert_eq!(
        node_fwd.keyset().len(),
        12,
        "expected all 12 honest blocks admitted"
    );
    assert!(
        node_fwd.equivocators().is_empty(),
        "no equivocation in the honest run"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ATTACK 2 — Byzantine EQUIVOCATION must be detected + the fork-victim excluded
// ─────────────────────────────────────────────────────────────────────────────

/// A Byzantine node creates TWO distinct blocks at the same `(creator, seq)` —
/// an equivocation / double-spend fork — and sends DIFFERENT forks to two honest
/// peers (the classic split-brain). We assert:
///   (1) the fork is DETECTED on both honest nodes (equivocators non-empty),
///   (2) the equivocator's honest TIP is WITHDRAWN (not silently overwritten —
///       the StrandIntegrity audit-A1 fix; the OLD `insert` left one fork live),
///   (3) the two honest nodes STILL converge once they exchange both forks
///       (both retain both fork blocks as evidence ⇒ same keyset).
#[test]
fn attack_byzantine_equivocation_detected_and_excluded() {
    let byz = key(20);
    let honest_a = key(21);

    // A shared honest base block so the forks have a common causal anchor.
    let base = Block::new(&honest_a, 0, Payload::Turn(vec![0x01]), vec![]);
    let base_id = base.id();

    // Two distinct blocks at (byz, seq=1): same creator, same seq, DIFFERENT
    // payload ⇒ different id ⇒ a detectable fork.
    let fork_x = Block::new(&byz, 1, Payload::Turn(vec![0xAA]), vec![base_id]);
    let fork_y = Block::new(&byz, 1, Payload::Turn(vec![0xBB]), vec![base_id]);
    assert_ne!(fork_x.id(), fork_y.id(), "forks must be distinct blocks");

    // Node P sees fork_x first; node Q sees fork_y first (split-brain).
    let mut p = Node::new(200);
    let mut q = Node::new(201);
    let mut ibp = Inbox::new();
    let mut ibq = Inbox::new();

    ibp.deliver(&mut p, base.clone());
    ibq.deliver(&mut q, base.clone());
    ibp.deliver(&mut p, fork_x.clone());
    ibq.deliver(&mut q, fork_y.clone());

    // At this point neither has seen the OTHER fork yet — no detection.
    // Now the gossip layer cross-delivers the conflicting fork to each.
    ibp.deliver(&mut p, fork_y.clone());
    ibq.deliver(&mut q, fork_x.clone());

    let byz_pk = byz.verifying_key().to_bytes();

    // (1) DETECTION on both honest nodes.
    assert!(
        p.equivocators().contains(&byz_pk),
        "FINDING(StrandIntegrity BROKEN): node P did NOT detect the equivocation — a same-(creator,seq) \
         fork slipped through `receive_block` undetected"
    );
    assert!(
        q.equivocators().contains(&byz_pk),
        "FINDING(StrandIntegrity BROKEN): node Q did NOT detect the equivocation"
    );

    // (2) TIP WITHDRAWAL — the equivocator has NO honest feed head. The OLD
    // overwriting `insert` would leave exactly one fork as the live tip.
    assert!(
        !p.tips().contains_key(&byz_pk),
        "FINDING(StrandIntegrity audit-A1 REGRESSED): equivocator still has a live tip on node P \
         — a fork was silently retained as the feed head instead of being withdrawn"
    );
    assert!(
        !q.tips().contains_key(&byz_pk),
        "FINDING(StrandIntegrity audit-A1 REGRESSED): equivocator still has a live tip on node Q"
    );

    // (3) CONVERGENCE despite the fork: both retain BOTH fork blocks as evidence,
    // so the content-addressed keysets match (the honest base + both forks).
    assert_eq!(
        p.keyset(),
        q.keyset(),
        "FINDING: honest nodes diverged after exchanging both forks — equivocation evidence \
         retention is order-dependent"
    );
    assert!(
        p.keyset().contains(&fork_x.id()) && p.keyset().contains(&fork_y.id()),
        "FINDING: a fork block was DROPPED rather than retained as detectable evidence \
         (an attacker could then hide the fork from a late-joining auditor)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ATTACK 3 — forged-signature blocks must be rejected at the wire
// ─────────────────────────────────────────────────────────────────────────────

/// The Byzantine node fabricates blocks it did not sign: (a) a zero-signature
/// block, (b) a block claiming a victim's creator pubkey but signed by the
/// attacker, (c) a block whose payload was tampered AFTER signing (sig no longer
/// covers `id()`). All must be rejected by `receive_block` — none may enter the
/// keyset. A single admitted forgery = StrandIntegrity's Ed25519 seam BROKEN.
#[test]
fn attack_forged_signatures_rejected() {
    let victim = key(30);
    let attacker = key(31);

    let mut node = Node::new(300);

    // (a) Zero-signature block (the unsigned sentinel).
    let mut unsigned = Block::new(&victim, 0, Payload::Turn(vec![1]), vec![]);
    unsigned.signature = [0u8; 64];
    let unsigned_id = unsigned.id();
    let r_unsigned = node.lace.receive_block(unsigned);
    assert!(
        r_unsigned.is_err() && !node.lace.contains(&unsigned_id),
        "FINDING: an UNSIGNED block was admitted to the lace (Ed25519 seam not enforced)"
    );

    // (b) Creator-spoof: claim the victim's pubkey but carry the ATTACKER's
    // signature. `verify_signature` checks the signature against `creator`, so
    // the attacker's sig cannot validate under the victim's key.
    let mut spoof = Block::new(&attacker, 0, Payload::Turn(vec![2]), vec![]);
    spoof.creator = victim.verifying_key().to_bytes(); // claim to be the victim
    let spoof_id = spoof.id();
    let r_spoof = node.lace.receive_block(spoof);
    assert!(
        r_spoof.is_err() && !node.lace.contains(&spoof_id),
        "FINDING: a CREATOR-SPOOFED block (victim pubkey, attacker signature) was admitted — \
         an attacker could forge feed entries for any identity"
    );

    // (c) Tamper-after-sign: sign a block, then mutate the payload. The id() and
    // therefore the signed message change, so the retained signature no longer
    // verifies.
    let mut tampered = Block::new(&attacker, 0, Payload::Turn(vec![3]), vec![]);
    // Mutate the payload AFTER the constructor signed the original content.
    tampered.payload = Payload::Turn(vec![3, 0xFF, 0xFF]);
    let tampered_id = tampered.id();
    let r_tampered = node.lace.receive_block(tampered);
    assert!(
        r_tampered.is_err() && !node.lace.contains(&tampered_id),
        "FINDING: a TAMPERED block (payload mutated after signing) was admitted — \
         block integrity not bound to the signature"
    );

    // The lace must be untouched by the entire forgery barrage.
    assert_eq!(
        node.keyset().len(),
        0,
        "FINDING: forged blocks left residue in the lace"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ATTACK 4 — message REPLAY must be idempotent (no double-count)
// ─────────────────────────────────────────────────────────────────────────────

/// A replay attacker re-delivers already-accepted blocks many times (and out of
/// order). Because blocks are content-addressed and `receive_block` is idempotent
/// (skip-if-present), the keyset, tips, and len must be invariant to replay. A
/// replay that grew the lace or shifted a tip = a double-count bug (the classic
/// double-spend-via-replay).
#[test]
fn attack_replay_is_idempotent() {
    let a = key(40);
    let strand = honest_strand(&a, 5, 7);

    let mut node = Node::new(400);
    let mut inbox = Inbox::new();
    for blk in strand.iter().cloned() {
        inbox.deliver(&mut node, blk);
    }
    let keyset_once = node.keyset();
    let tips_once = node.tips();
    let len_once = node.lace.len();

    // Replay the WHOLE strand 50 times, reversed and forward, interleaved.
    for round in 0..50 {
        let iter: Box<dyn Iterator<Item = Block>> = if round % 2 == 0 {
            Box::new(strand.iter().cloned())
        } else {
            Box::new(strand.iter().rev().cloned())
        };
        for blk in iter {
            inbox.deliver(&mut node, blk);
        }
    }

    assert_eq!(
        node.keyset(),
        keyset_once,
        "FINDING: replay changed the keyset (double-count)"
    );
    assert_eq!(node.tips(), tips_once, "FINDING: replay shifted a tip");
    assert_eq!(
        node.lace.len(),
        len_once,
        "FINDING: replay grew the lace by {} blocks (non-idempotent reception)",
        node.lace.len() as i64 - len_once as i64
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ATTACK 5 — network PARTITION + HEAL converges (CatchupConverges across a split)
// ─────────────────────────────────────────────────────────────────────────────

/// Two honest nodes are PARTITIONED: each accepts its own local progress while
/// cut off from the other. When the partition HEALS, they exchange deltas
/// (`Lace::delta_for` / `merge`, the real CRDT path). We assert that after heal
/// both reach the SAME keyset + tips — the partition left no permanent fork.
#[test]
fn attack_partition_then_heal_converges() {
    let a = key(50);
    let b = key(51);

    let mut left = Node::new(500);
    let mut right = Node::new(501);

    // Shared genesis both observe before the split.
    let genesis = Block::new(&a, 0, Payload::Turn(vec![0]), vec![]);
    let _ = left.lace.receive_block(genesis.clone());
    let _ = right.lace.receive_block(genesis.clone());
    let g_id = genesis.id();

    // PARTITION: left advances creator A; right advances creator B. Neither sees
    // the other's progress.
    let mut preds_a = vec![g_id];
    for seq in 1..4 {
        let blk = Block::new(
            &a,
            seq,
            Payload::Turn(vec![0xA, seq as u8]),
            preds_a.clone(),
        );
        preds_a = vec![blk.id()];
        let _ = left.lace.receive_block(blk);
    }
    let mut preds_b = vec![g_id];
    for seq in 1..4 {
        let blk = Block::new(
            &b,
            seq,
            Payload::Turn(vec![0xB, seq as u8]),
            preds_b.clone(),
        );
        preds_b = vec![blk.id()];
        let _ = right.lace.receive_block(blk);
    }

    // Pre-heal: the two views DIFFER (the partition is real).
    assert_ne!(
        left.keyset(),
        right.keyset(),
        "partition should produce divergent views"
    );

    // HEAL: exchange deltas via the real CRDT merge. Each sends the other every
    // block the other lacks.
    let right_known: HashSet<BlockId> = right.keyset();
    let to_right = left.lace.delta_for(&right_known);
    let left_known: HashSet<BlockId> = left.keyset();
    let to_left = right.lace.delta_for(&left_known);

    right
        .lace
        .merge(to_right)
        .expect("merge of left's delta must succeed (causally closed)");
    left.lace
        .merge(to_left)
        .expect("merge of right's delta must succeed (causally closed)");

    // Post-heal: identical finalized views.
    assert_eq!(
        left.keyset(),
        right.keyset(),
        "FINDING(CatchupConverges BROKEN): nodes did NOT reconverge after partition heal — \
         a permanent fork survived the merge"
    );
    assert_eq!(
        left.tips(),
        right.tips(),
        "FINDING: tip frontiers diverged after heal"
    );
    // 1 genesis + 3 A-extensions + 3 B-extensions = 7.
    assert_eq!(
        left.keyset().len(),
        7,
        "expected the union of both partitions"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ATTACK 6 — FLOOD: a Byzantine spammer cannot desync honest nodes
// ─────────────────────────────────────────────────────────────────────────────

/// A Byzantine node FLOODS the network with a huge volume of valid-but-useless
/// blocks (a resource-exhaustion / spam attack). Honest nodes that ingest the
/// same flood (in different orders) must still converge, and the flood must not
/// corrupt the honest creators' tips. This is the operational check that volume
/// alone is not a liveness/safety break.
#[test]
fn attack_flood_does_not_desync() {
    let honest = key(60);
    let spammer = key(61);

    // A small honest strand we care about preserving.
    let honest_blocks = honest_strand(&honest, 3, 9);

    // A large spam strand (valid signed blocks, just noise).
    let spam = honest_strand(&spammer, 200, 0x55);

    let mut n1 = Node::new(600);
    let mut n2 = Node::new(601);
    let mut ib1 = Inbox::new();
    let mut ib2 = Inbox::new();

    // n1: honest first, then spam. n2: spam first, then honest. Both interleave.
    for blk in honest_blocks.iter().cloned() {
        ib1.deliver(&mut n1, blk);
    }
    for blk in spam.iter().cloned() {
        ib1.deliver(&mut n1, blk);
    }
    for blk in spam.iter().rev().cloned() {
        ib2.deliver(&mut n2, blk);
    }
    for blk in honest_blocks.iter().rev().cloned() {
        ib2.deliver(&mut n2, blk);
    }

    assert_eq!(
        n1.keyset(),
        n2.keyset(),
        "FINDING: a flood desynced two honest nodes (volume broke convergence)"
    );
    // The honest creator's tip must be its real seq-2 head, unperturbed by spam.
    let honest_pk = honest.verifying_key().to_bytes();
    let honest_tip = n1.tips().get(&honest_pk).copied();
    assert_eq!(
        honest_tip,
        Some(honest_blocks.last().unwrap().id()),
        "FINDING: the flood corrupted the honest creator's tip"
    );
    assert!(
        n1.equivocators().is_empty(),
        "a flood of valid blocks is not equivocation"
    );
    assert_eq!(
        n1.keyset().len(),
        203,
        "all honest + spam blocks accounted for"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ATTACK 7 — double-spend RACE across nodes: same fork → both nodes agree to
// withdraw, no node finalizes a single fork as canonical.
// ─────────────────────────────────────────────────────────────────────────────

/// The double-spend race: the attacker spends the SAME logical resource twice by
/// authoring two conflicting blocks at one `(creator, seq)` and racing them to
/// two nodes simultaneously. The safety property is that NO honest node ends up
/// treating exactly one fork as the canonical, live, single-tip state (which
/// would let the double-spend "win" on that node). Both must withdraw the tip
/// and flag the equivocator; and once both forks propagate, both nodes hold the
/// SAME evidence set. This is the operational dual of the StrandIntegrity
/// `strand_single_tip` keystone: a fork-free strand has a unique tip, so a forked
/// strand must have NONE.
#[test]
fn attack_double_spend_race_no_node_finalizes_one_fork() {
    let spender = key(70);
    let mut n1 = Node::new(700);
    let mut n2 = Node::new(701);

    // Two conflicting "spends" at seq 0 (no shared predecessor needed — both are
    // roots at the same slot).
    let spend_to_alice = Block::new(&spender, 0, Payload::Turn(vec![b'A']), vec![]);
    let spend_to_bob = Block::new(&spender, 0, Payload::Turn(vec![b'B']), vec![]);

    // RACE: n1 gets the Alice-spend, n2 gets the Bob-spend (simultaneous).
    let _ = n1.lace.receive_block(spend_to_alice.clone());
    let _ = n2.lace.receive_block(spend_to_bob.clone());

    // Each node, in isolation, currently believes its single spend is the tip.
    let spender_pk = spender.verifying_key().to_bytes();
    assert_eq!(n1.tips().get(&spender_pk), Some(&spend_to_alice.id()));
    assert_eq!(n2.tips().get(&spender_pk), Some(&spend_to_bob.id()));

    // Now gossip cross-delivers the conflicting spend to each node.
    let _ = n1.lace.receive_block(spend_to_bob.clone());
    let _ = n2.lace.receive_block(spend_to_alice.clone());

    // SAFETY: neither node finalizes a single fork — the tip is withdrawn on both,
    // the double-spender is flagged, and both nodes agree the spend is INVALID
    // (no canonical winner). A node that kept ONE spend live would have let the
    // double-spend succeed there.
    assert!(
        !n1.tips().contains_key(&spender_pk) && !n2.tips().contains_key(&spender_pk),
        "FINDING(DOUBLE-SPEND WINS): a node kept one fork as the live tip — the double-spend \
         was finalized on at least one node"
    );
    assert!(
        n1.equivocators().contains(&spender_pk) && n2.equivocators().contains(&spender_pk),
        "FINDING: the double-spender was not flagged on both nodes"
    );
    assert_eq!(
        n1.keyset(),
        n2.keyset(),
        "FINDING: the two nodes hold different evidence after the race (no agreement on the fork)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ATTACK 8 — ECLIPSE: a node fed ONLY by a Byzantine peer still detects the fork
// the moment ANY honest block reveals it; and a withheld block does not let the
// equivocator masquerade as honest forever.
// ─────────────────────────────────────────────────────────────────────────────

/// Eclipse: an attacker controls a victim's entire inbound feed and tries to
/// present a CONSISTENT-looking but forked history (withholding the second fork
/// so the victim never sees the conflict). The defense is content-addressing +
/// detection on FIRST sight of the conflicting block. We assert: (1) while
/// eclipsed with a single consistent fork, no false equivocation is raised
/// (liveness — the node still makes progress), but (2) the INSTANT a single
/// honest peer delivers the conflicting fork (eclipse broken by one honest
/// connection), detection fires and the tip is withdrawn. This shows eclipse buys
/// the attacker only delay, not a permanent undetected fork.
#[test]
fn attack_eclipse_delay_not_permanent_fork() {
    let byz = key(80);
    let mut victim = Node::new(800);

    let fork_a = Block::new(&byz, 0, Payload::Turn(vec![0x0A]), vec![]);
    let fork_b = Block::new(&byz, 0, Payload::Turn(vec![0x0B]), vec![]);
    let byz_pk = byz.verifying_key().to_bytes();

    // Phase 1 — ECLIPSED: the attacker feeds only fork_a. The victim makes
    // progress and (correctly) does NOT flag an equivocation it cannot see.
    let _ = victim.lace.receive_block(fork_a.clone());
    assert!(
        !victim.equivocators().contains(&byz_pk),
        "a node cannot detect a fork whose second branch it has never received \
         (this is expected — no false positive)"
    );
    assert_eq!(
        victim.tips().get(&byz_pk),
        Some(&fork_a.id()),
        "single-fork tip during eclipse"
    );

    // Phase 2 — ECLIPSE BROKEN: one honest peer delivers the withheld fork_b.
    // Detection must fire immediately and the tip must be withdrawn.
    let _ = victim.lace.receive_block(fork_b.clone());
    assert!(
        victim.equivocators().contains(&byz_pk),
        "FINDING: eclipse defeat FAILED — the conflicting fork arrived but no equivocation was \
         detected, so the attacker's withholding bought a PERMANENT undetected fork"
    );
    assert!(
        !victim.tips().contains_key(&byz_pk),
        "FINDING: equivocator tip not withdrawn after eclipse broken"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ATTACK 9 — sequence-regression / rollback: a Byzantine node cannot rewrite its
// own past by re-submitting a LOWER sequence to roll back history.
// ─────────────────────────────────────────────────────────────────────────────

/// We use `dregg_blocklace::Blocklace` (the `lib.rs` strand-integrity write path,
/// which enforces sequence monotonicity explicitly via `SeqRegression`). A
/// Byzantine creator advances to seq 3, then tries to "rewrite history" by
/// inserting a fresh, validly-signed block at seq 1. Monotonicity must reject it
/// (it is neither a higher-seq extension nor a same-seq fork). A node that
/// accepted it could be tricked into rolling back the creator's feed.
#[test]
fn attack_sequence_rollback_rejected() {
    use dregg_blocklace::{Block as LibBlock, Blocklace, InsertError};

    let creator = key(90);
    let mut bl = Blocklace::new();

    // Build a signed seq 0..=3 chain via the lib path.
    let mut preds: Vec<[u8; 32]> = Vec::new();
    let mut last_seq3: Option<[u8; 32]> = None;
    for seq in 0..=3u64 {
        let blk = LibBlock::new_signed(&creator, seq, preds.clone(), vec![seq as u8]);
        let id = blk.id();
        bl.insert(blk)
            .expect("honest monotone extension must insert");
        preds = vec![id];
        if seq == 3 {
            last_seq3 = Some(id);
        }
    }
    let tip_before = bl.tip_for(&creator.verifying_key().to_bytes()).copied();
    assert_eq!(tip_before, last_seq3, "tip should be the seq-3 head");

    // ROLLBACK ATTEMPT: a freshly-signed block at seq 1 (lower than tip seq 3),
    // with NO predecessors (so it is not a same-(creator,seq) fork of any stored
    // block — seq 1 already exists but with different preds ⇒ this is *also* a
    // fork; to isolate the monotonicity gate we craft a brand-new seq that
    // regresses without colliding: seq 1 collides, so use the cleanest rollback:
    // re-sign the seq-3 content at the creator but claim seq 2 with empty preds).
    let rollback = LibBlock::new_signed(&creator, 2, vec![], vec![0xDE, 0xAD]);
    let rollback_id = rollback.id();
    let res = bl.insert(rollback);

    // It must be rejected — either as a SeqRegression (monotonicity) or as an
    // Equivocation (if it collides with the stored seq-2). EITHER rejection is
    // correct; what must NOT happen is the tip moving backward or the block
    // becoming the new honest tip.
    assert!(
        res.is_err(),
        "FINDING(StrandIntegrity monotonicity BROKEN): a lower-sequence rollback block was \
         accepted as a valid strand extension — history can be rewritten"
    );
    if let Err(InsertError::SeqRegression {
        attempted,
        tip_sequence,
        ..
    }) = &res
    {
        assert!(
            *attempted <= *tip_sequence,
            "SeqRegression must report attempted <= tip"
        );
    }
    // The honest tip must be UNCHANGED (still seq 3) unless the rollback was a
    // fork that withdrew it; in the fork case the creator is an equivocator and
    // has no tip. Either way the rollback block is NOT the live tip.
    let tip_after = bl.tip_for(&creator.verifying_key().to_bytes()).copied();
    assert_ne!(
        tip_after,
        Some(rollback_id),
        "FINDING: the rollback block became the live tip — the creator's history was rewritten"
    );
}
