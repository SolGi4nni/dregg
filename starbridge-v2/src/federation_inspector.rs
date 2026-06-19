//! L8 — THE FEDERATION & CONSENSUS INSPECTOR (the moldable-inspector spine).
//!
//! Census slice-9 is the protocol's distribution layer — federations, the
//! blocklace causal DAG, finality / common-knowledge, quorum / threshold-BLS /
//! DKG, the OCapN netlayer (sturdy refs / handoff certs), the n=3 devnet — and
//! it is the census's single largest `None` block ("ZERO inspector coverage").
//! This module closes it on the L1 [`crate::presentable`] spine.
//!
//! ## The honest split — what is wire-reachable vs. captp-only
//!
//! The headless `embedded-executor` build runs the verified executor IN-PROCESS
//! but deliberately does NOT link the network stack: `dregg-sdk` is taken
//! `default-features = false`, dropping tokio/quinn/`captp`, and the
//! `federation` / `blocklace` / `coord` consensus crates are not dependencies
//! at all (only `dregg-coord`'s wire-free budget primitive is). So the live
//! federation/consensus STATE is never in this process — it lives on a node.
//!
//! The split this module draws, exactly as [`crate::organs`] draws it for
//! channel/mailbox/court:
//!
//!   * **WIRE-BACKED** — a connected [`crate::client::NodeClient`] returns the
//!     node's published federation/consensus snapshots as the
//!     [`crate::model`] wire types ([`FederationInfo`], [`BlockInfo`],
//!     [`NodeStatus`]). These are REAL data the node computed off its live
//!     `federation`/`blocklace` machinery and serialized over `/api/federations`
//!     / `/api/blocklace/blocks` / `/status`. We wrap them in thin newtypes and
//!     project the SAME uniform presentation set the embedded objects emit — a
//!     federation's committee + finalized-roots, the blocklace as a height-
//!     ordered causal stream, the published finality / quorum ladder. A
//!     fixture-constructed wire value is fully `cargo test`-able with no network.
//!
//!   * **CAPTP-ONLY** — the operations whose full state needs the live OCapN
//!     netlayer / `captp` surface the headless build does not link: a
//!     `dregg_captp::HandoffCertificate` (the introducer-signed third-party
//!     handoff), a sturdy-ref dereference, the per-block predecessor lace + tau
//!     causal-DAG ordering (the starbridge wire `BlockInfo` carries only
//!     height/hash/creator/seq — the node drops the predecessor set + the
//!     `QuorumCertificate` vote bundle from the public list), the DKG ceremony
//!     transcript, the beacon randomness, the equivocation court docket. These
//!     are surfaced HONESTLY as [`RemoteFederationPath`] — kind · seam · route —
//!     NOT faked local state. They become live reflections when the
//!     remote-federation panel connects a node and reads the richer per-object
//!     routes named here.
//!
//! gpui-free + `cargo test`-able: every presentation is pure data projected from
//! a wire snapshot or a static descriptor, exactly as `reflect.rs` /
//! `live_node.rs` / `organs.rs` are.

use crate::model::{BlockInfo, FederationInfo, NodeStatus};
use crate::presentable::{
    GaugeView, LatticeView, Presentable, PresentCtx, Presentation, PresentationBody,
    PresentationKind, TimelineEvent, TimelineView,
};
use crate::reflect::{self, Field, Inspectable, ObjectKind};

// ===========================================================================
// §L8.1 — the finality ladder (the common-knowledge rungs)
// ===========================================================================

/// The four monotone finality rungs of the blocklace common-knowledge ladder,
/// mirrored from `blocklace::finality::FinalityLevel` (which is not linked in
/// this build). The ordering is the protocol's: once a block reaches a rung it
/// never regresses (`Local ⊑ Bilateral ⊑ Attested ⊑ Ordered`).
///
/// This is DATA (the rung vocabulary + its order), not a re-implementation of
/// the consensus rule — the node assigns a block's rung off its live
/// `blocklace`/`coord` machinery; this names the ladder the node's published
/// finality reports against so the inspector can draw it.
pub const FINALITY_RUNGS: [&str; 4] = [
    // Local — known to the creator only (just created / received).
    "Local",
    // Bilateral — acknowledged by at least one other participant.
    "Bilateral",
    // Attested — a quorum (2f+1) acknowledged it (common knowledge).
    "Attested",
    // Ordered — assigned a total order by tau super-ratification (consensus).
    "Ordered",
];

/// Build the finality ladder as a [`LatticeView`] — the monotone rung order with
/// an optional "current" highlight. The four rungs, weakest-first, with the
/// covering relations `Local ⊑ Bilateral ⊑ Attested ⊑ Ordered`.
fn finality_ladder(current_rung: Option<usize>) -> LatticeView {
    let nodes: Vec<String> = FINALITY_RUNGS.iter().map(|s| s.to_string()).collect();
    let edges = vec![(0, 1), (1, 2), (2, 3)];
    LatticeView { nodes, edges, current: current_rung }
}

// ===========================================================================
// §L8.2 — FederationView (a wire FederationInfo as a Presentable)
// ===========================================================================

/// A thin newtype wrapping a node's published [`FederationInfo`] wire snapshot as
/// a [`Presentable`] — the established "reflect a foreign struct into a
/// starbridge view" pattern (`organs.rs`'s `TrustlineReflection`,
/// `live_node.rs`'s `LiveReflection`). The federation lives on a remote node, so
/// we register via this wrapper over the wire type rather than `impl Presentable`
/// for the (unlinked) `dregg_federation::Federation`.
#[derive(Clone, Debug)]
pub struct FederationView {
    /// The published federation snapshot (a `/api/federations` entry).
    pub info: FederationInfo,
}

impl FederationView {
    /// Wrap a wire federation snapshot.
    pub fn new(info: FederationInfo) -> Self {
        FederationView { info }
    }

    /// A short operator-legible id (abbreviated federation id hex).
    pub fn short(&self) -> String {
        reflect::short_hex_hexstr(&self.info.id)
    }

    /// The committee as an [`Inspectable`] (the RawFields floor): identity, the
    /// committee epoch, the `t`-of-`n` threshold, the member roster, the local
    /// flag, and the finalized-root tally — every field the wire snapshot
    /// carries, re-housed as the uniform field tree.
    fn committee_fields(&self) -> Inspectable {
        let i = &self.info;
        let mut fields = vec![
            Field::text("federation_id", reflect::short_hex_hexstr(&i.federation_id)),
            Field::boolean("is_local", i.is_local),
            Field::count("committee_epoch", i.committee_epoch),
            Field::count("threshold", i.threshold as u64),
            Field::count("member_count", i.member_count as u64),
            Field::count("latest_height", i.latest_height),
            Field::count("num_finalized_roots", i.num_finalized_roots as u64),
        ];
        match &i.latest_root {
            Some(r) => fields.push(Field::text("latest_root", reflect::short_hex_hexstr(r))),
            None => fields.push(Field::text("latest_root", "none (no finalized root yet)")),
        }
        for (n, m) in i.members.iter().enumerate() {
            fields.push(Field::text(format!("member[{n}]"), reflect::short_hex_hexstr(m)));
        }
        Inspectable {
            kind: ObjectKind::Image,
            title: format!("Federation {}", self.short()),
            subtitle: format!(
                "{} · epoch {} · {}-of-{} · h{}",
                if i.is_local { "local" } else { "remote" },
                i.committee_epoch,
                i.threshold,
                i.member_count,
                i.latest_height,
            ),
            fields,
        }
    }
}

impl Presentable for FederationView {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Image
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let i = &self.info;
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the committee + roster + roots.
        let insp = self.committee_fields();
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Federation".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) DomainVisual — the quorum gauge: `threshold` of `member_count`
        //     (the `t`-of-`n` BFT safety margin, drawn as a bounded dial).
        let gauge = GaugeView {
            label: "quorum threshold (t of n members)".to_string(),
            value: i.threshold as i64,
            ceiling: Some(i.member_count as i64),
            rungs: i
                .members
                .iter()
                .enumerate()
                .map(|(n, _)| format!("member {n}"))
                .collect(),
        };
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Quorum".to_string(),
            search_text: format!(
                "quorum threshold {} of {} members 2f+1 bft safety",
                i.threshold, i.member_count
            ),
            body: PresentationBody::Gauge(gauge),
        });

        // (3) Invariant — the attested-root coverage readout: the finalized-root
        //     tally + the latest attested root (the federation's published
        //     state-commitment binding, the verification axis).
        let mut iv_fields = vec![
            Field::count("num_finalized_roots", i.num_finalized_roots as u64),
            Field::count("latest_height", i.latest_height),
        ];
        match &i.latest_root {
            Some(r) => iv_fields.push(Field::text("latest_attested_root", reflect::short_hex_hexstr(r))),
            None => iv_fields.push(Field::text("latest_attested_root", "none")),
        }
        let iv = Inspectable {
            kind: ObjectKind::Proof,
            title: format!("Attested Roots · {}", self.short()),
            subtitle: format!("{} finalized root(s) · up to h{}", i.num_finalized_roots, i.latest_height),
            fields: iv_fields,
        };
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Attested Roots".to_string(),
            search_text: format!(
                "attested roots finalized {} height {}",
                i.num_finalized_roots, i.latest_height
            ),
            body: PresentationBody::Fields(iv),
        });

        out
    }
}

// ===========================================================================
// §L8.3 — BlocklaceView (the published blocklace DAG as a causal stream)
// ===========================================================================

/// A thin newtype wrapping a node's published blocklace block list (the
/// `/api/blocklace/blocks` snapshot, each entry a [`BlockInfo`] wire value) as a
/// [`Presentable`]. The blocklace is the protocol's causal DAG; the node
/// publishes a height-ordered subset of each block's identity (height / hash /
/// creator / seq).
///
/// The full causal DAG — each block's predecessor lace, the per-block
/// `QuorumCertificate` vote bundle, and the tau finality round — is NOT in the
/// starbridge wire `BlockInfo` (the node drops the predecessor set + votes from
/// the public list); that richer Graph view is a [`RemoteFederationPath`] facet,
/// surfaced honestly below rather than faked from the thin list.
#[derive(Clone, Debug)]
pub struct BlocklaceView {
    /// The published blocks (newest-first or height-ordered as the node returned them).
    pub blocks: Vec<BlockInfo>,
}

impl BlocklaceView {
    /// Wrap a wire block list.
    pub fn new(blocks: Vec<BlockInfo>) -> Self {
        BlocklaceView { blocks }
    }

    /// The DAG height: the maximum block height in the published list (0 if empty).
    pub fn dag_height(&self) -> u64 {
        self.blocks.iter().map(|b| b.height).max().unwrap_or(0)
    }

    /// The distinct creators in the published list (the DAG's participant breadth).
    pub fn creator_count(&self) -> usize {
        let mut creators: Vec<&String> = self.blocks.iter().map(|b| &b.creator).collect();
        creators.sort();
        creators.dedup();
        creators.len()
    }

    /// Decode a wire block hash hex into a navigable 32-byte hash (tolerant —
    /// a malformed live hash renders as zeros rather than panicking the view).
    fn block_hash(b: &BlockInfo) -> [u8; 32] {
        let mut out = [0u8; 32];
        if let Ok(bytes) = hex::decode(&b.hash) {
            let n = bytes.len().min(32);
            out[..n].copy_from_slice(&bytes[..n]);
        }
        out
    }
}

impl Presentable for BlocklaceView {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Image
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the DAG summary stats.
        let insp = Inspectable {
            kind: ObjectKind::Image,
            title: "Blocklace DAG".to_string(),
            subtitle: format!(
                "{} block(s) · DAG height {} · {} creator(s)",
                self.blocks.len(),
                self.dag_height(),
                self.creator_count()
            ),
            fields: vec![
                Field::count("block_count", self.blocks.len() as u64),
                Field::count("dag_height", self.dag_height()),
                Field::count("creator_count", self.creator_count() as u64),
            ],
        };
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Blocklace".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Provenance — the blocklace as a height-ordered causal stream (the
        //     happened-before timeline). Each block is a navigable event keyed on
        //     its height, carrying its real hash. The full predecessor DAG is the
        //     remote-path facet (the wire list drops the lace); this is the
        //     honest projection of what the published list DOES carry.
        let mut sorted: Vec<&BlockInfo> = self.blocks.iter().collect();
        sorted.sort_by(|a, b| a.height.cmp(&b.height).then(a.seq.cmp(&b.seq)));
        let events: Vec<TimelineEvent> = sorted
            .iter()
            .map(|b| TimelineEvent {
                at: b.height,
                label: format!(
                    "block {} · creator {} · seq {}",
                    reflect::short_hex_hexstr(&b.hash),
                    reflect::short_hex_hexstr(&b.creator),
                    b.seq
                ),
                hash: Some(BlocklaceView::block_hash(b)),
            })
            .collect();
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Causal Stream".to_string(),
            search_text: format!("blocklace causal stream {} blocks happened-before", events.len()),
            body: PresentationBody::Timeline(TimelineView { events }),
        });

        // (3) DomainVisual — the finality ladder (the common-knowledge rungs the
        //     node reports a block's finality against). Published as data; the
        //     live per-block rung assignment is a node-side computation.
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Finality Ladder".to_string(),
            search_text: "finality ladder local bilateral attested ordered common knowledge".to_string(),
            body: PresentationBody::Lattice(finality_ladder(None)),
        });

        out
    }
}

// ===========================================================================
// §L8.4 — NodeConsensusView (the /status consensus surface as a Presentable)
// ===========================================================================

/// A thin newtype wrapping a node's published [`NodeStatus`] consensus surface as
/// a [`Presentable`] — the distribution axis read off `/status`: peer count, DAG
/// height, consensus liveness, the federation mode, and (surfaced honestly) the
/// state producer (`lean` vs `rust` — a node on the legacy producer is visibly
/// NOT running the verified semantics).
#[derive(Clone, Debug)]
pub struct NodeConsensusView {
    /// The node's base URL (the route this consensus surface was read from).
    pub base_url: String,
    /// The published `/status` snapshot.
    pub status: NodeStatus,
}

impl NodeConsensusView {
    /// Wrap a `/status` snapshot read from `base_url`.
    pub fn new(base_url: impl Into<String>, status: NodeStatus) -> Self {
        NodeConsensusView { base_url: base_url.into(), status }
    }
}

impl Presentable for NodeConsensusView {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Image
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let s = &self.status;
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the full consensus/peer surface.
        let insp = Inspectable {
            kind: ObjectKind::Image,
            title: format!("Node Consensus — {}", self.base_url),
            subtitle: format!(
                "{} · {} peers · h{} · dag h{} · producer {}",
                if s.healthy { "healthy" } else { "DOWN" },
                s.peer_count,
                s.latest_height,
                s.dag_height,
                s.state_producer,
            ),
            fields: vec![
                Field::boolean("healthy", s.healthy),
                Field::count("peer_count", s.peer_count as u64),
                Field::count("latest_height", s.latest_height),
                Field::count("dag_height", s.dag_height),
                Field::count("block_count", s.block_count as u64),
                Field::boolean("consensus_live", s.consensus_live),
                Field::text("federation_mode", s.federation_mode.clone()),
                Field::text("state_producer", s.state_producer.clone()),
                Field::boolean("lean_producer", s.lean_producer),
                Field::boolean("full_turn_proving", s.full_turn_proving),
                Field::count("producer_covered_effects", s.producer_covered_effects as u64),
            ],
        };
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Consensus".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Invariant — the verified-producer readout: a node on the `rust`
        //     producer is visibly NOT running the verified Lean semantics (the
        //     honest soundness surface `live_node.rs` already names).
        let verified = s.lean_producer && s.state_producer == "lean";
        let iv = Inspectable {
            kind: ObjectKind::Proof,
            title: "Producer Soundness".to_string(),
            subtitle: if verified {
                "verified (lean producer)".to_string()
            } else {
                format!("UNVERIFIED — producer is `{}`", s.state_producer)
            },
            fields: vec![
                Field::boolean("verified_producer", verified),
                Field::text("state_producer", s.state_producer.clone()),
                Field::boolean("lean_producer", s.lean_producer),
                Field::boolean("full_turn_proving", s.full_turn_proving),
                Field::count("producer_covered_effects", s.producer_covered_effects as u64),
            ],
        };
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Producer Soundness".to_string(),
            search_text: format!("producer soundness verified {} {}", verified, s.state_producer),
            body: PresentationBody::Fields(iv),
        });

        // (3) DomainVisual — the consensus-liveness finality ladder. The node's
        //     published DAG height sits at `Ordered` only when consensus is live;
        //     otherwise the published state has not been totally ordered yet.
        let current_rung = if s.consensus_live { Some(3) } else { Some(0) };
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Finality".to_string(),
            search_text: format!(
                "finality ladder consensus_live {} dag_height {}",
                s.consensus_live, s.dag_height
            ),
            body: PresentationBody::Lattice(finality_ladder(current_rung)),
        });

        out
    }
}

// ===========================================================================
// §L8.5 — the remote-path (captp-only) federation surface, surfaced honestly
// ===========================================================================

/// A federation/consensus object whose full state needs the live OCapN netlayer
/// / `captp` surface the headless build does not link — surfaced HONESTLY (kind +
/// seam + route), not faked, exactly as [`crate::organs::RemoteOrgan`] surfaces
/// channel/mailbox/court. Becomes a live reflection when the remote-federation
/// panel connects a node and reads the per-object route named here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RemoteFederationPath {
    /// The object kind (handoff cert / sturdy ref / causal DAG / quorum cert / …).
    pub kind: &'static str,
    /// The object's one-seam description (what it IS / enforces).
    pub seam: &'static str,
    /// The route by which the master interface would reach it (the honest
    /// "designed-pending" path — a node endpoint or the captp surface).
    pub route: &'static str,
}

/// The captp-only federation/consensus objects catalogued honestly: the OCapN
/// handoff certificate, the sturdy-ref dereference, the per-block causal lace +
/// quorum-certificate vote bundle (dropped from the public block list), the DKG
/// ceremony transcript, the beacon randomness, the equivocation-court docket.
/// Each needs the network surface the headless build does not link, so we name
/// its kind + seam + route, never fake its state.
pub fn remote_federation_paths() -> Vec<RemoteFederationPath> {
    vec![
        RemoteFederationPath {
            kind: "handoff cert",
            seam: "OCapN third-party handoff — an introducer-signed \
                   `dregg_captp::HandoffCertificate` + sender Ed25519 sig over the \
                   canonical delivery message authorizes a Turn via \
                   `Authorization::CapTpDelivered` (the cap crosses a vat boundary)",
            route: "behind captp (the netlayer / vat-to-vat handoff) — exercise via a \
                    connected node's `dregg_exercise_handoff_cert` route, then reflect \
                    the cert's nonce + recipient/sender binding live",
        },
        RemoteFederationPath {
            kind: "sturdy ref",
            seam: "OCapN sturdy reference — a persistable `uri` that re-grants a live \
                   capability on dereference (the relay delivers it as an \
                   `InboxMessage::SturdyRef { uri, sender }`)",
            route: "behind captp (the relay transport / netlayer) — reach via a connected \
                    node's relay service, then reflect the dereferenced live ref",
        },
        RemoteFederationPath {
            kind: "causal DAG",
            seam: "the blocklace predecessor lace + tau total-order — each block's full \
                   predecessor set and its assigned finality round (the happened-before \
                   Graph the public block list drops to a thin height/hash/creator/seq tuple)",
            route: "node-service — read per-block via `/api/block/{height}` (carries the \
                    real `prev_hash` + full `predecessors` set), then build the causal Graph live",
        },
        RemoteFederationPath {
            kind: "quorum certificate",
            seam: "a `QuorumCertificate` — the 2f+1 vote bundle (threshold-BLS aggregate) \
                   that lifts a block to the Attested rung (the votes the public list omits)",
            route: "node-service — read via the block detail / federation-roots routes, then \
                    verify the threshold-BLS aggregate against the committee live",
        },
        RemoteFederationPath {
            kind: "DKG ceremony",
            seam: "the distributed-key-generation transcript — the committee's per-epoch \
                   threshold-key dealing (the BLS group key the quorum signs under)",
            route: "behind captp (the DKG service) — reach via a connected node's \
                    `dkg_service`, then reflect the ceremony's round/share progress live",
        },
        RemoteFederationPath {
            kind: "beacon randomness",
            seam: "the beacon committee's VRF/KZG randomness output (the unbiasable \
                   committee-selection / shuffle source)",
            route: "node-service — read the published beacon output, then reflect its \
                    value + usage live",
        },
        RemoteFederationPath {
            kind: "equivocation court",
            seam: "the equivocation-evidence docket — a fork proof (two conflicting \
                   blocks from one creator at one seq) adjudicated against a bonded obligation",
            route: "node-service (evidence intake + adjudication) — reach via a connected \
                    node's equivocation-court service, then reflect the docket + verdicts live",
        },
    ]
}

/// Project the remote-path federation catalog into an [`Inspectable`] (the
/// RawFields floor for the honest remote surface): each captp-only object is a
/// field whose value names its seam + route, so the gpui layer renders it with
/// the existing field-tree widget — the honest "designed-pending" surface, never
/// a faked live state.
fn remote_paths_as_inspectable(paths: &[RemoteFederationPath]) -> Inspectable {
    let fields = paths
        .iter()
        .map(|p| Field::text(p.kind.to_string(), format!("{} · {}", p.seam, p.route)))
        .collect();
    Inspectable {
        kind: ObjectKind::Image,
        title: "Federation — remote-path objects".to_string(),
        subtitle: format!("{} captp-only object(s), surfaced honestly", paths.len()),
        fields,
    }
}

/// THE FEDERATION SURVEY — the slice-9 panel root. It carries the wire-backed
/// views a connected node supplies (federations, the blocklace, the consensus
/// surface) AND the honest catalog of the captp-only objects, exactly as
/// [`crate::organs::OrganSurvey`] carries embed-core organs + the remote catalog.
///
/// Built from a [`crate::client::NodeClient`] snapshot at the call site (the
/// cockpit fetches `federations()` / `blocks()` / `status()` and passes them
/// in); this module stays gpui-free and network-free — it projects the snapshots
/// it is handed.
#[derive(Clone, Debug)]
pub struct FederationSurvey {
    /// The published federations (wire-backed).
    pub federations: Vec<FederationView>,
    /// The published blocklace (wire-backed), if a snapshot was supplied.
    pub blocklace: Option<BlocklaceView>,
    /// The node consensus surface (wire-backed), if a `/status` was supplied.
    pub consensus: Option<NodeConsensusView>,
    /// The captp-only federation objects, surfaced honestly.
    pub remote: Vec<RemoteFederationPath>,
}

impl FederationSurvey {
    /// Build a survey from wire snapshots a connected node supplied (any of which
    /// may be absent — a node not running consensus returns empty lists; the
    /// remote-path catalog is always present).
    pub fn from_wire(
        federations: Vec<FederationInfo>,
        blocks: Option<Vec<BlockInfo>>,
        status: Option<(String, NodeStatus)>,
    ) -> Self {
        FederationSurvey {
            federations: federations.into_iter().map(FederationView::new).collect(),
            blocklace: blocks.map(BlocklaceView::new),
            consensus: status.map(|(url, s)| NodeConsensusView::new(url, s)),
            remote: remote_federation_paths(),
        }
    }

    /// An empty survey (no node connected): no wire-backed views, but the
    /// captp-only catalog is still surfaced honestly so the panel is never blank.
    pub fn disconnected() -> Self {
        FederationSurvey {
            federations: Vec::new(),
            blocklace: None,
            consensus: None,
            remote: remote_federation_paths(),
        }
    }

    /// The count of LIVE (wire-backed) federation objects reflected.
    pub fn live_count(&self) -> usize {
        self.federations.len()
            + usize::from(self.blocklace.is_some())
            + usize::from(self.consensus.is_some())
    }

    /// The remote-path catalog projected as a single RawFields presentation (the
    /// honest captp-only surface, rendered with the field-tree widget).
    pub fn remote_presentation(&self) -> Presentation {
        let insp = remote_paths_as_inspectable(&self.remote);
        Presentation {
            kind: PresentationKind::RawFields,
            label: "Remote-Path Objects".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::presentable::PresentableExt;
    use crate::reflect::FieldValue;
    use crate::world::World;
    use dregg_cell::CellId;

    // A PresentCtx the wire-backed views ignore (they project a snapshot, not the
    // live embedded world) — but the trait takes one, so we build a trivial one.
    fn dummy_ctx(world: &World) -> PresentCtx<'_> {
        let viewer = CellId::from_bytes([0u8; 32]);
        PresentCtx::new(world, viewer)
    }

    fn sample_federation() -> FederationInfo {
        FederationInfo {
            id: "ab".repeat(32),
            federation_id: "ab".repeat(32),
            committee_epoch: 7,
            threshold: 3,
            member_count: 5,
            members: (0..5u8).map(|i| format!("{i:02x}").repeat(32)).collect(),
            is_local: true,
            latest_height: 142,
            latest_root: Some("9a".repeat(32)),
            num_finalized_roots: 142,
        }
    }

    fn sample_blocks() -> Vec<BlockInfo> {
        (1880..1888u64)
            .rev()
            .map(|h| BlockInfo {
                height: h,
                hash: format!("{h:04x}").repeat(16),
                creator: if h % 2 == 0 { "11".repeat(32) } else { "22".repeat(32) },
                seq: h,
            })
            .collect()
    }

    fn sample_status() -> NodeStatus {
        NodeStatus {
            healthy: true,
            peer_count: 2,
            latest_height: 142,
            dag_height: 1887,
            block_count: 8,
            consensus_live: true,
            federation_mode: "federated".into(),
            public_key: "cc".repeat(32),
            state_producer: "lean".into(),
            lean_producer: true,
            full_turn_proving: true,
            producer_covered_effects: 28,
        }
    }

    // ── the universal-coverage floor: every wire-backed view has RawFields ──

    #[test]
    fn every_wire_backed_view_yields_the_raw_fields_floor() {
        let w = World::new();
        let ctx = dummy_ctx(&w);

        let fed = FederationView::new(sample_federation());
        assert!(fed.has_raw_fields_floor(&ctx), "FederationView has the RawFields floor");

        let bl = BlocklaceView::new(sample_blocks());
        assert!(bl.has_raw_fields_floor(&ctx), "BlocklaceView has the RawFields floor");

        let cons = NodeConsensusView::new("http://node", sample_status());
        assert!(cons.has_raw_fields_floor(&ctx), "NodeConsensusView has the RawFields floor");
    }

    // ── the FederationView offers ≥3 kinds with real wire data ──────────────

    #[test]
    fn federation_view_offers_committee_quorum_and_attested_roots() {
        let w = World::new();
        let ctx = dummy_ctx(&w);
        let fed = FederationView::new(sample_federation());

        let kinds = fed.presentation_kinds(&ctx);
        assert!(kinds.contains(&PresentationKind::RawFields));
        assert!(kinds.contains(&PresentationKind::DomainVisual));
        assert!(kinds.contains(&PresentationKind::Invariant));

        let set = fed.present(&ctx);
        // The RawFields floor carries the real committee roster.
        let rf = set.iter().find(|p| p.kind == PresentationKind::RawFields).unwrap();
        match &rf.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "member[0]"));
                assert!(i.fields.iter().any(|f| f.key == "committee_epoch"));
                assert!(i.fields.iter().any(|f| f.key == "threshold"));
            }
            other => panic!("RawFields must carry a Fields body, got {other:?}"),
        }

        // The Quorum gauge reads the real t-of-n threshold.
        let dv = set.iter().find(|p| p.kind == PresentationKind::DomainVisual).unwrap();
        match &dv.body {
            PresentationBody::Gauge(g) => {
                assert_eq!(g.value, 3, "threshold");
                assert_eq!(g.ceiling, Some(5), "member count");
            }
            other => panic!("Quorum must carry a Gauge body, got {other:?}"),
        }
    }

    // ── the blocklace projects as a height-ordered causal stream ────────────

    #[test]
    fn blocklace_view_projects_a_height_ordered_causal_stream() {
        let w = World::new();
        let ctx = dummy_ctx(&w);
        let bl = BlocklaceView::new(sample_blocks());

        assert_eq!(bl.dag_height(), 1887);
        assert_eq!(bl.creator_count(), 2, "two distinct creators in the fixture");

        let set = bl.present(&ctx);
        let pv = set.iter().find(|p| p.kind == PresentationKind::Provenance).unwrap();
        match &pv.body {
            PresentationBody::Timeline(t) => {
                assert_eq!(t.events.len(), 8);
                // Height-ordered ascending (the fixture was built descending).
                assert!(t.events.windows(2).all(|w| w[0].at <= w[1].at));
                // Each block is navigable by its real hash.
                assert!(t.events.iter().all(|e| e.hash.is_some()));
            }
            other => panic!("Causal Stream must carry a Timeline body, got {other:?}"),
        }

        // The finality ladder is the four monotone rungs.
        let dv = set.iter().find(|p| p.kind == PresentationKind::DomainVisual).unwrap();
        match &dv.body {
            PresentationBody::Lattice(l) => {
                assert_eq!(l.nodes, vec!["Local", "Bilateral", "Attested", "Ordered"]);
                assert_eq!(l.edges, vec![(0, 1), (1, 2), (2, 3)]);
            }
            other => panic!("Finality Ladder must carry a Lattice body, got {other:?}"),
        }
    }

    // ── the consensus surface honestly flags the producer ───────────────────

    #[test]
    fn node_consensus_view_flags_the_verified_producer_honestly() {
        let w = World::new();
        let ctx = dummy_ctx(&w);

        // A lean producer is verified.
        let cons = NodeConsensusView::new("http://node", sample_status());
        let set = cons.present(&ctx);
        let iv = set.iter().find(|p| p.kind == PresentationKind::Invariant).unwrap();
        match &iv.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(
                    |f| f.key == "verified_producer" && matches!(f.value, FieldValue::Bool(true))
                ));
            }
            other => panic!("Producer Soundness must carry a Fields body, got {other:?}"),
        }

        // A rust producer is visibly UNVERIFIED — never laundered green.
        let mut rusty = sample_status();
        rusty.state_producer = "rust".into();
        rusty.lean_producer = false;
        let cons2 = NodeConsensusView::new("http://node", rusty);
        let set2 = cons2.present(&ctx);
        let iv2 = set2.iter().find(|p| p.kind == PresentationKind::Invariant).unwrap();
        match &iv2.body {
            PresentationBody::Fields(i) => {
                assert!(i.subtitle.contains("UNVERIFIED"));
                assert!(i.fields.iter().any(
                    |f| f.key == "verified_producer" && matches!(f.value, FieldValue::Bool(false))
                ));
            }
            _ => unreachable!(),
        }

        // The consensus-live finality ladder sits at Ordered when live, Local when not.
        let dv = set.iter().find(|p| p.kind == PresentationKind::DomainVisual).unwrap();
        match &dv.body {
            PresentationBody::Lattice(l) => assert_eq!(l.current, Some(3), "consensus_live ⟹ Ordered"),
            _ => unreachable!(),
        }
    }

    // ── the captp-only surface is surfaced HONESTLY, never faked ────────────

    #[test]
    fn remote_federation_paths_are_honest_not_faked() {
        let paths = remote_federation_paths();
        assert!(paths.len() >= 5, "the captp-only catalog is non-trivial");
        // The load-bearing remote objects are named.
        assert!(paths.iter().any(|p| p.kind == "handoff cert"));
        assert!(paths.iter().any(|p| p.kind == "sturdy ref"));
        assert!(paths.iter().any(|p| p.kind == "causal DAG"));
        assert!(paths.iter().any(|p| p.kind == "quorum certificate"));
        // Each names its kind, seam, and a route through a node/captp — no faked state.
        for p in &paths {
            assert!(!p.kind.is_empty());
            assert!(!p.seam.is_empty());
            assert!(
                p.route.contains("node") || p.route.contains("captp"),
                "every remote-path object names its node/captp route: {}",
                p.kind
            );
        }
    }

    // ── the survey carries wire-backed views + the honest remote catalog ────

    #[test]
    fn federation_survey_carries_wire_views_and_the_remote_catalog() {
        let survey = FederationSurvey::from_wire(
            vec![sample_federation()],
            Some(sample_blocks()),
            Some(("http://node".to_string(), sample_status())),
        );
        assert_eq!(survey.federations.len(), 1);
        assert!(survey.blocklace.is_some());
        assert!(survey.consensus.is_some());
        assert_eq!(survey.live_count(), 3, "1 federation + blocklace + consensus");
        // The captp-only catalog is always present (honest, never faked).
        assert!(!survey.remote.is_empty());

        // The remote presentation is a real RawFields field tree naming each object.
        let rp = survey.remote_presentation();
        assert_eq!(rp.kind, PresentationKind::RawFields);
        match &rp.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "handoff cert"));
                assert!(i.fields.iter().any(|f| f.key == "sturdy ref"));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn a_disconnected_survey_still_surfaces_the_remote_catalog_honestly() {
        // No node connected: no wire-backed views, but the panel is never blank —
        // the captp-only surface is named honestly so the operator sees the route.
        let survey = FederationSurvey::disconnected();
        assert_eq!(survey.live_count(), 0, "nothing wire-backed without a node");
        assert!(survey.federations.is_empty());
        assert!(survey.blocklace.is_none());
        assert!(survey.consensus.is_none());
        assert!(!survey.remote.is_empty(), "the honest remote catalog is always present");
    }

    // ── an empty blocklace (consensus not yet running) is honest, not faked ──

    #[test]
    fn an_empty_blocklace_reflects_an_empty_dag_honestly() {
        let w = World::new();
        let ctx = dummy_ctx(&w);
        let bl = BlocklaceView::new(Vec::new());
        assert_eq!(bl.dag_height(), 0);
        assert_eq!(bl.creator_count(), 0);
        let set = bl.present(&ctx);
        let pv = set.iter().find(|p| p.kind == PresentationKind::Provenance).unwrap();
        match &pv.body {
            PresentationBody::Timeline(t) => assert!(t.events.is_empty(), "no blocks, no events"),
            _ => unreachable!(),
        }
        // The floor is still present (a non-faked empty DAG summary).
        assert!(bl.has_raw_fields_floor(&ctx));
    }
}
