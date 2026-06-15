//! Verified FINALITY GATE — gate the live commit on the Lean-exported finalization rule.
//!
//! # What this is
//!
//! `blocklace_sync::poll_finalized_blocks` computes the finalized total order with the Rust
//! `dregg_blocklace::ordering::tau` and serves the not-yet-executed blocks (tracked BY IDENTITY in
//! `crate::execution_cursor::ExecutionCursor`; see TauPrefixMonotone) to the executor. The
//! verified Lean model of that rule (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean`:
//! `computeRounds`/`findAllFinalLeaders`/`tauOrder`) was, until now, only AGREEMENT-CHECKED in a
//! unit test (`ordering::tests::test_tau_differential_against_lean_model`). It did NOT gate the live
//! commit.
//!
//! This module converts "agreement-checked" into "Lean-gated". At commit time it:
//!   1. wire-encodes the SAME `(wavelength, participants, lace)` the Rust `tau` consumes, using the
//!      grammar `Dregg2.Distributed.FinalityGate.encodeLaceWire` mirrors byte-for-byte;
//!   2. calls the verified Lean rule via the FFI export `dregg_blocklace_finalize`
//!      (`dregg_lean_ffi::shadow_blocklace_finalize`), which runs `BlocklaceFinality.tauOrder` and
//!      returns the verified finalized order projected to `(creator, seq)` (the differential
//!      coordinate — the `BlockId` hash differs Rust↔Lean, but `(creator, seq)` is content-identical);
//!   3. exposes [`VerifiedFinality::admits`] — "the verified rule finalizes this `(creator, seq)`" —
//!      so `poll_finalized_blocks` admits a block to the executor ONLY when the verified rule
//!      finalizes it.
//!
//! The Lean theorem `gate_admits_iff_verified_finalizes` proves `admits` is EXACTLY membership in the
//! verified `tauGolden` order, so gating on it IS gating on the verified `BlocklaceFinality.tauOrder`.
//!
//! # Flag + fail-safety
//!
//! Gated by [`finality_gate_enabled`] (`DREGG_FINALITY_GATE`, **default ON**). When the Lean archive
//! lacks the export (stale build) or the wire round-trips to `ERR`, the gate FAILS OPEN to the
//! un-gated Rust order **with a loud warning + a divergence record** — the live path is never broken
//! (a node missing the verified archive keeps running), but the operator is told the verified gate is
//! not active. When the archive HAS the export and the rule disagrees with the Rust `tau` on a
//! `(creator, seq)`, the gate REFUSES that block (it is not sliced to the executor) and records the
//! divergence — the verified rule wins.

use std::collections::HashMap;

use dregg_blocklace::finality::{Block, BlockId, Blocklace};

/// The Cordial-Miners wavelength `tau` uses (`ordering::OrderingConfig::default().wavelength`).
/// The Lean model is parameterized by wavelength and the node runs the default-3 ordering, so the
/// wire we hand the verified rule MUST carry 3 (the Lean `#guard`s also use wavelength 3).
const WAVELENGTH: u64 = 3;

/// Whether the live finality gate is enabled. **Default ON** (per the devnet-readiness directive: the
/// verified rule gates new state). `DREGG_FINALITY_GATE=0`/`false`/`off` opts OUT (keeps the legacy
/// un-gated path) for an operator who needs to bypass it.
pub fn finality_gate_enabled() -> bool {
    !matches!(
        std::env::var("DREGG_FINALITY_GATE").ok().as_deref(),
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF")
    )
}

/// The verified finalized order, as the set of `(creator_id, seq)` coordinates the verified Lean rule
/// finalizes, PLUS the creator-interning table used to encode the wire (so the caller can map a Rust
/// `Block` back to its `creator_id`). Construct via [`VerifiedFinality::compute`].
#[derive(Debug, Clone)]
pub struct VerifiedFinality {
    /// `(creator_id, seq)` pairs the verified rule finalized. `creator_id` is the participant index
    /// (the `AuthorId` the Lean wire used); a block whose `(creator_id, seq)` is in this set is
    /// admitted.
    finalized: std::collections::HashSet<(u64, u64)>,
    /// creator pubkey -> the small `AuthorId` (participant index) used on the wire.
    creator_ids: HashMap<[u8; 32], u64>,
}

/// The wire-encoded lace + the interning tables the finality gates share. Produced once by
/// [`VerifiedFinality::build_wire`] and consumed by both the `(creator, seq)`-projection gate
/// (`compute`) and the RAW total-order gate (`compute_order`), so the two read the EXACT same wire.
struct LaceWire {
    /// The `"w=<W>;P=<...>;B=<...>"` wire the Lean rule consumes (the grammar `encodeLaceWire` mirrors).
    wire: String,
    /// creator pubkey -> the small `AuthorId` (participant index) used on the wire.
    creator_ids: HashMap<[u8; 32], u64>,
    /// the interned Lean `BlockId` (a `u64` index) -> the node's real `BlockId`. The inverse of the
    /// interning the wire uses, so the RAW-order export's `u64` ids map back to node blocks.
    id_to_block: HashMap<u64, BlockId>,
}

impl VerifiedFinality {
    /// Build the wire + interning tables ONCE — shared by `compute` (projection) and `compute_order`
    /// (raw total order), so both gates hand the verified rule byte-identical input. Interns creators
    /// to the participant index (the round-robin `participants[w % n]` leader, matching BOTH `tau` and
    /// the Lean `waveLeader`) and block ids to first-seen order over the SAME `(seq, creator)` sort
    /// `tau` uses (so the wire's `BlockId`s are a faithful relabeling of the lace).
    fn build_wire(lace: &Blocklace, participants: &[[u8; 32]]) -> LaceWire {
        let mut creator_ids: HashMap<[u8; 32], u64> = HashMap::new();
        for (i, p) in participants.iter().enumerate() {
            creator_ids.entry(*p).or_insert(i as u64);
        }
        let mut next_extra = participants.len() as u64;

        let mut blocks: Vec<(&BlockId, &Block)> = lace.iter().collect();
        blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));

        let mut id_ids: HashMap<BlockId, u64> = HashMap::new();
        let mut id_to_block: HashMap<u64, BlockId> = HashMap::new();
        for (i, (id, _)) in blocks.iter().enumerate() {
            id_ids.insert(**id, i as u64);
            id_to_block.insert(i as u64, **id);
        }

        let participants_wire: Vec<String> =
            (0..participants.len()).map(|i| i.to_string()).collect();

        let mut block_wires: Vec<String> = Vec::with_capacity(blocks.len());
        for (id, b) in &blocks {
            let creator_id = *creator_ids.entry(b.creator).or_insert_with(|| {
                let v = next_extra;
                next_extra += 1;
                v
            });
            let id_id = *id_ids.get(*id).expect("interned above");
            // Only predecessors PRESENT in the lace are edges `tau`/`tauOrder` traverse.
            let preds: Vec<String> = b
                .predecessors
                .iter()
                .filter_map(|p| id_ids.get(p).map(|n| n.to_string()))
                .collect();
            block_wires.push(format!(
                "{id_id}:{creator_id}:{seq}:{preds}",
                seq = b.seq,
                preds = preds.join(".")
            ));
        }

        let wire = format!(
            "w={W};P={P};B={B}",
            W = WAVELENGTH,
            P = participants_wire.join(","),
            B = block_wires.join("|")
        );
        LaceWire {
            wire,
            creator_ids,
            id_to_block,
        }
    }

    /// Run the VERIFIED Lean RAW TOTAL-ORDER rule (`dregg_tau_order`, the export proved
    /// order-faithfully equal to `BlocklaceFinality.tauOrder` by `tau_order_export_eq`) over the lace
    /// and return the finalized total order as node `BlockId`s, in the verified order. `None` when the
    /// raw-order export is unavailable (stale archive) or the wire returns `ERR` (the caller falls back
    /// to the Rust `tau` order). Unlike [`Self::compute`] (the `(creator, seq)`-set projection used for
    /// per-block admission), this is the FULL ordered id list — the verified `tauOrder` itself.
    pub fn compute_order(lace: &Blocklace, participants: &[[u8; 32]]) -> Option<Vec<BlockId>> {
        let LaceWire {
            wire, id_to_block, ..
        } = Self::build_wire(lace, participants);
        // The raw-order export returns the verified `tauOrder` as the interned-`u64` id list. Map each
        // back to the node's `BlockId`; an id the wire never interned (impossible for a well-formed
        // `tauOrder`, which only emits present ids) is dropped fail-safe.
        let order = dregg_lean_ffi::verified_tau_order(&wire).ok()?;
        Some(
            order
                .into_iter()
                .filter_map(|u| id_to_block.get(&u).copied())
                .collect(),
        )
    }

    /// Run the VERIFIED Lean finalization rule over the lace and participants. Returns `Ok(Some(_))`
    /// with the verified finalized set when the Lean gate ran and produced a non-`ERR` order;
    /// `Ok(None)` when the gate is unavailable/`ERR` (the caller fails open); `Err` is never produced
    /// (errors collapse to `None` so the caller has one fail-open branch).
    pub fn compute(lace: &Blocklace, participants: &[[u8; 32]]) -> Option<VerifiedFinality> {
        let LaceWire {
            wire, creator_ids, ..
        } = Self::build_wire(lace, participants);

        // Call the verified Lean rule. On any error (archive missing the export, init failure) or the
        // `ERR` sentinel, return None so the caller fails open with a warning.
        let out = match dregg_lean_ffi::shadow_blocklace_finalize(&wire) {
            Ok(s) => s,
            Err(_) => return None,
        };
        let body = out.strip_prefix("F=")?; // `ERR` (or anything else) -> None -> fail open.

        let mut finalized = std::collections::HashSet::new();
        if !body.is_empty() {
            for pair in body.split(',') {
                let (c, s) = pair.split_once(':')?;
                let c: u64 = c.parse().ok()?;
                let s: u64 = s.parse().ok()?;
                finalized.insert((c, s));
            }
        }
        Some(VerifiedFinality {
            finalized,
            creator_ids,
        })
    }

    /// Whether the verified rule finalizes a block — by its `(creator pubkey, seq)`. The node calls
    /// this per Rust-finalized block before slicing it to the executor: `true` ⇒ admit, `false` ⇒
    /// REFUSE (the verified rule did not finalize it). Mirrors the Lean `gateAdmits` predicate.
    pub fn admits(&self, creator: &[u8; 32], seq: u64) -> bool {
        match self.creator_ids.get(creator) {
            Some(cid) => self.finalized.contains(&(*cid, seq)),
            // A creator the wire never interned cannot have been finalized.
            None => false,
        }
    }

    /// Number of `(creator, seq)` coordinates the verified rule finalized (for diagnostics).
    #[allow(dead_code)] // Diagnostic accessor retained on the verified-finality surface.
    pub fn len(&self) -> usize {
        self.finalized.len()
    }

    /// Whether the verified rule finalized nothing.
    #[allow(dead_code)] // Diagnostic accessor retained on the verified-finality surface.
    pub fn is_empty(&self) -> bool {
        self.finalized.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_blocklace::finality::{Block, Payload};
    use ed25519_dalek::SigningKey;

    /// Pure admission semantics — `admits` is membership in the finalized `(creator_id, seq)` set,
    /// keyed by the participant index. No Lean archive needed.
    #[test]
    fn admits_semantics() {
        let p0 = [1u8; 32];
        let p1 = [2u8; 32];
        let mut creator_ids: HashMap<[u8; 32], u64> = HashMap::new();
        creator_ids.insert(p0, 0);
        creator_ids.insert(p1, 1);
        let vf = VerifiedFinality {
            finalized: [(0u64, 0u64), (1u64, 0u64)].into_iter().collect(),
            creator_ids,
        };
        assert!(vf.admits(&p0, 0));
        assert!(vf.admits(&p1, 0));
        assert!(!vf.admits(&p0, 1)); // seq 1 not finalized
        assert!(!vf.admits(&[9u8; 32], 0)); // unknown creator
        assert_eq!(vf.len(), 2);
        assert!(!vf.is_empty());
    }

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// THE LIVE-GATE DIFFERENTIAL — `VerifiedFinality::compute` (the verified Lean rule
    /// `BlocklaceFinality.tauOrder` via the `dregg_blocklace_finalize` FFI export) AGREES with the
    /// Rust `dregg_blocklace::ordering::tau` on a real 3-node / 3-round lace, at the `(creator, seq)`
    /// coordinate. This is the runtime face of the consensus-pillar differential
    /// (`blocklace::ordering::tests::test_tau_differential_against_lean_model`): the SAME verified
    /// rule that gates `poll_finalized_blocks` reproduces the order the Rust `tau` finalizes — so
    /// gating the live commit on it is transparent for honest traces and only bites on divergence.
    ///
    /// Self-skips when the Lean archive lacks the finality-gate export (a marshal-only / stale build).
    #[test]
    fn verified_gate_agrees_with_rust_tau_three_node() {
        if !dregg_lean_ffi::finality_gate_available() {
            eprintln!(
                "SKIP: Lean finality-gate export not linked (finality_gate_available()==false)"
            );
            return;
        }

        // Three nodes, three fully-connected rounds (the shape of the Lean `trace3`). Each node's
        // round-(r+1) block references all of round r; payloads are Turns (actionable).
        let keys = [key(1), key(2), key(3)];
        let participants: Vec<[u8; 32]> =
            keys.iter().map(|k| k.verifying_key().to_bytes()).collect();

        let mut lace = Blocklace::new(keys[0].clone(), 3);

        let mut r1_ids = Vec::new();
        for (i, k) in keys.iter().enumerate() {
            let b = Block::new(k, 0, Payload::Turn(vec![i as u8]), vec![]);
            r1_ids.push(b.id());
            lace.receive_block(b).expect("genesis insert");
        }
        let mut round_prev: Vec<BlockId> = r1_ids;
        for round in 1u64..=2 {
            let mut this_round = Vec::new();
            for (i, k) in keys.iter().enumerate() {
                let b = Block::new(
                    k,
                    round,
                    Payload::Turn(vec![(round * 10) as u8 + i as u8]),
                    round_prev.clone(),
                );
                this_round.push(b.id());
                lace.receive_block(b).expect("round insert");
            }
            round_prev = this_round;
        }

        // RUST tau over the same lace, projected to (creator_id, seq).
        let mut ordering_lace = dregg_blocklace::Blocklace::new();
        let mut fin_to_ord: HashMap<BlockId, dregg_blocklace::BlockId> = HashMap::new();
        let mut blocks: Vec<_> = lace.iter().collect();
        blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));
        let mut ord_to_cs: HashMap<dregg_blocklace::BlockId, ([u8; 32], u64)> = HashMap::new();
        for (fin_id, b) in &blocks {
            let preds: Vec<dregg_blocklace::BlockId> = b
                .predecessors
                .iter()
                .filter_map(|p| fin_to_ord.get(p).copied())
                .collect();
            let ob = dregg_blocklace::Block::new(b.creator, b.seq, preds, vec![]);
            let oid = ob.id();
            ordering_lace.insert_unverified(ob).ok();
            fin_to_ord.insert(**fin_id, oid);
            ord_to_cs.insert(oid, (b.creator, b.seq));
        }
        let rust_order = dregg_blocklace::ordering::tau(&ordering_lace, &participants);
        let rust_finalized: std::collections::HashSet<(u64, u64)> = rust_order
            .iter()
            .filter_map(|oid| ord_to_cs.get(oid))
            .map(|(creator, seq)| {
                let cid = participants.iter().position(|p| p == creator).unwrap() as u64;
                (cid, *seq)
            })
            .collect();

        // VERIFIED gate over the same lace, via the real node gate type.
        let vf = VerifiedFinality::compute(&lace, &participants)
            .expect("verified gate ran (archive present + wire non-ERR)");
        let verified: std::collections::HashSet<(u64, u64)> = vf.finalized.clone();

        assert_eq!(
            verified, rust_finalized,
            "verified finality gate must agree with Rust tau on the (creator, seq) finalized set"
        );
        assert_eq!(
            verified.len(),
            9,
            "3-node lace finalizes all nine (creator, seq) blocks"
        );

        // The gate ADMITS each finalized block by its (pubkey, seq), exactly as
        // poll_finalized_blocks queries it.
        for (cid, seq) in &verified {
            let creator = participants[*cid as usize];
            assert!(
                vf.admits(&creator, *seq),
                "gate must admit a verified-finalized block"
            );
        }
    }

    /// THE RAW-ORDER GATE DIFFERENTIAL — `VerifiedFinality::compute_order` (the verified Lean
    /// `BlocklaceFinality.tauOrder` via the NEW `dregg_tau_order` export, proved order-faithfully
    /// equal to `tauOrder` by `tau_order_export_eq`) returns the FULL finalized TOTAL ORDER as node
    /// `BlockId`s. On the 3-node lace this is the nine-block order whose `(creator, seq)` projection
    /// is exactly the projection gate's finalized SET — so the raw-order export and the projection
    /// export agree, and the order is a permutation-free superset relationship: every block the
    /// projection finalizes appears in the raw order, IN the verified sequence.
    ///
    /// Self-skips when the archive lacks the raw-order export (a stale/marshal-only build).
    #[test]
    fn raw_order_export_agrees_with_projection_three_node() {
        if !dregg_lean_ffi::tau_order_available() {
            eprintln!("SKIP: Lean raw tau-order export not linked (tau_order_available()==false)");
            return;
        }

        let keys = [key(1), key(2), key(3)];
        let participants: Vec<[u8; 32]> =
            keys.iter().map(|k| k.verifying_key().to_bytes()).collect();
        let mut lace = Blocklace::new(keys[0].clone(), 3);

        let mut r1_ids = Vec::new();
        for (i, k) in keys.iter().enumerate() {
            let b = Block::new(k, 0, Payload::Turn(vec![i as u8]), vec![]);
            r1_ids.push(b.id());
            lace.receive_block(b).expect("genesis insert");
        }
        let mut round_prev: Vec<BlockId> = r1_ids;
        for round in 1u64..=2 {
            let mut this_round = Vec::new();
            for (i, k) in keys.iter().enumerate() {
                let b = Block::new(
                    k,
                    round,
                    Payload::Turn(vec![(round * 10) as u8 + i as u8]),
                    round_prev.clone(),
                );
                this_round.push(b.id());
                lace.receive_block(b).expect("round insert");
            }
            round_prev = this_round;
        }

        // The verified RAW total order (node BlockIds), via the new export.
        let order = VerifiedFinality::compute_order(&lace, &participants)
            .expect("raw-order gate ran (archive present + wire non-ERR)");
        assert_eq!(
            order.len(),
            9,
            "3-node lace finalizes a nine-block total order"
        );

        // Its (creator, seq) projection must EQUAL the projection gate's finalized set — the two
        // verified exports are consistent (one is the order, the other its set projection).
        let vf = VerifiedFinality::compute(&lace, &participants).expect("projection gate ran");
        let order_cs: std::collections::HashSet<(u64, u64)> = order
            .iter()
            .filter_map(|id| lace.get(id))
            .map(|b| {
                let cid = participants.iter().position(|p| p == &b.creator).unwrap() as u64;
                (cid, b.seq)
            })
            .collect();
        assert_eq!(
            order_cs, vf.finalized,
            "the raw tau-order export's (creator,seq) projection must equal the projection gate's set"
        );
        // Every block in the verified order is admitted by the projection gate (consistency both ways).
        for id in &order {
            let b = lace.get(id).expect("ordered id is present");
            assert!(
                vf.admits(&b.creator, b.seq),
                "ordered block must be projection-admitted"
            );
        }
    }
}
