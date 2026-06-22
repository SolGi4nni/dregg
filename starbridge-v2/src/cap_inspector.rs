//! L4 — CAPABILITIES, ATTENUATION & THE CAP-CROWN, on the moldable-inspector
//! spine (`presentable.rs`).
//!
//! `reflect.rs` reflects a cell; this module reflects the **capability family**
//! — the ocap authority a cell holds and the lattice it sits in — through the
//! exact same `Presentable`/`Gadget` shapes the L1 spine defines. Nothing here
//! is reinvented: the partial order is the REAL [`AuthRequired::is_narrower_or_equal`]
//! (`cell/src/permissions.rs`), the non-amplification judge is the REAL
//! [`dregg_cell::is_attenuation`] (`granted ⊆ held`, `cell/src/capability.rs`),
//! the firmament handle is the REAL [`dregg_firmament::Capability`] (its
//! `attenuate` rides that same gate), the delegation neighborhood is the REAL
//! [`OcapGraph`] (`graph.rs`), the cap-crown root is the REAL openable
//! sorted-Poseidon2 root [`dregg_cell::compute_canonical_capability_root_felt`]
//! (`cell/src/commitment.rs`, the `#103` `capability_root`), and the mint path is
//! the REAL [`Powerbox::grant`] (`powerbox.rs`) — a genuine `GrantCapability`
//! turn through the verified executor.
//!
//! Two faces:
//!
//!   * [`HeldCapability`] — a thin newtype over one `CapabilityRef` a cell holds,
//!     lifted into the firmament [`Capability`] and offered as a `Presentable`
//!     set: RawFields · Lattice (the AuthRequired order with the held cap's
//!     position marked) · Graph (the ocap delegation neighborhood) · MerkleTree
//!     (the cap-crown membership readout, the real root + leaf digest of THIS
//!     cap's c-list) · Invariant (the `granted ⊆ held` non-amplification readout).
//!
//!   * [`AttenuationDial`] — THE attenuation dial: a [`Gadget`] that takes a held
//!     capability, designates a narrower rights tier, validates the narrowing
//!     with the REAL `is_attenuation` (refusing a widening fail-closed, in-band),
//!     and builds the attenuated firmament `Capability`. Where it MINTS into a
//!     grantee, [`AttenuationDial::grant_through_powerbox`] rides the established
//!     `Powerbox::grant` ceremony — the same verified-executor turn the cockpit's
//!     powerbox panel already drives. No parallel grant path.
//!
//! gpui-free + `cargo test`-able exactly as `presentable.rs`/`reflect.rs` are.

use dregg_cell::{
    cap_ref_to_leaf, compute_canonical_capability_root_felt, felt_to_bytes32, is_attenuation,
    AuthRequired, CapabilityRef, CellId,
};
use dregg_firmament::{Capability, Rights, Target};

use crate::graph::OcapGraph;
use crate::powerbox::{Powerbox, PowerboxOutcome};
use crate::presentable::{
    Gadget, GadgetError, GadgetField, GadgetInput, GadgetValidation, GraphView, LatticeView,
    MerkleTreeView, PresentCtx, Presentable, Presentation, PresentationBody, PresentationKind,
};
use crate::reflect::{self, Field, Inspectable, ObjectKind};
use crate::world::World;

// ===========================================================================
// §L4.0 — the AuthRequired lattice as data (the REAL partial order)
// ===========================================================================

/// The built-in lattice tiers, weakest-first, that a [`LatticeView`] renders.
/// `Custom { vk_hash }` is incomparable with everything but itself
/// ([`AuthRequired::is_narrower_or_equal`]), so it is NOT one of these covering
/// nodes — it is surfaced as a separate marker when a held cap carries it.
///
/// This is NOT a parallel lattice: the covering edges are derived by ASKING the
/// real [`AuthRequired::is_narrower_or_equal`], so the diagram is exactly the
/// shape the executor's gate enforces.
const LATTICE_TIERS: [AuthRequired; 5] = [
    AuthRequired::Impossible,
    AuthRequired::Signature,
    AuthRequired::Proof,
    AuthRequired::Either,
    AuthRequired::None,
];

/// A short legible name for a built-in tier (the lattice node label / search text).
fn auth_label(a: &AuthRequired) -> String {
    match a {
        AuthRequired::None => "None (always allowed)".to_string(),
        AuthRequired::Signature => "Signature".to_string(),
        AuthRequired::Proof => "Proof".to_string(),
        AuthRequired::Either => "Either (sig OR proof)".to_string(),
        AuthRequired::Impossible => "Impossible (locked)".to_string(),
        AuthRequired::Custom { vk_hash } => {
            format!("Custom · vk {}", reflect::short_hex(vk_hash))
        }
    }
}

/// Build the [`LatticeView`] of the built-in AuthRequired order, marking the tier
/// `held` currently sits at (if it is a built-in tier). The covering relations are
/// the REAL `is_narrower_or_equal`: an edge `i ⊑ j` is drawn iff `tier[i]` is
/// narrower-or-equal to `tier[j]` AND no intermediate tier sits strictly between
/// them (the Hasse covers, not the full transitive order).
fn auth_lattice_view(held: &AuthRequired) -> LatticeView {
    let nodes: Vec<String> = LATTICE_TIERS.iter().map(auth_label).collect();

    // Covering relations: `a ⊑ b` with no `c` strictly between (a < c < b).
    let mut edges: Vec<(usize, usize)> = Vec::new();
    for (i, a) in LATTICE_TIERS.iter().enumerate() {
        for (j, b) in LATTICE_TIERS.iter().enumerate() {
            if i == j {
                continue;
            }
            // a strictly narrower than b (narrower-or-equal AND not equal).
            if !(a.is_narrower_or_equal(b) && a != b) {
                continue;
            }
            // Is there a c strictly between? a < c < b.
            let has_between = LATTICE_TIERS.iter().any(|c| {
                c != a && c != b && a.is_narrower_or_equal(c) && c.is_narrower_or_equal(b)
            });
            if !has_between {
                edges.push((i, j));
            }
        }
    }

    let current = LATTICE_TIERS.iter().position(|t| t == held);
    LatticeView { nodes, edges, current }
}

// ===========================================================================
// §L4.1 — HeldCapability: a Presentable over one held CapabilityRef
// ===========================================================================

/// A thin newtype wrapping ONE capability a cell holds (a c-list entry) as a
/// [`Presentable`] — the established "reflect a foreign struct into a starbridge
/// view" pattern (`presentable.rs`'s `ReflectedCell`). The cap lives in the
/// foreign `dregg_cell` crate; we register via this wrapper, and we lift it into
/// the REAL firmament [`Capability`] (`Target::Distributed`, since a held c-list
/// cap reaches a distributed cell) so attenuation/delegation read off the one
/// backing-agnostic handle.
#[derive(Clone, Debug)]
pub struct HeldCapability {
    /// The cell that HOLDS this capability (the c-list owner — the graph's tail).
    pub holder: CellId,
    /// The genuine c-list entry (target, slot, rights, breadstuff, expiry, facet).
    pub cap: CapabilityRef,
}

impl HeldCapability {
    /// Wrap the cap at `slot` in `holder`'s live c-list, if present. Reads the
    /// live ledger — never a parallel cap store.
    pub fn from_world(world: &World, holder: CellId, slot: u32) -> Option<Self> {
        let cell = world.ledger().get(&holder)?;
        let cap = cell.capabilities.iter().find(|c| c.slot == slot)?.clone();
        Some(HeldCapability { holder, cap })
    }

    /// Every capability `holder` holds, wrapped — the whole c-list as
    /// [`HeldCapability`]s (the caller can present each). Reads the live ledger.
    pub fn all_for(world: &World, holder: CellId) -> Vec<Self> {
        match world.ledger().get(&holder) {
            Some(cell) => cell
                .capabilities
                .iter()
                .map(|cap| HeldCapability { holder, cap: cap.clone() })
                .collect(),
            None => Vec::new(),
        }
    }

    /// Lift this held cap into the REAL firmament [`Capability`] — a
    /// `Target::Distributed` handle over the target cell carrying the held
    /// `AuthRequired`. This is the ONE handle attenuation rides
    /// ([`Capability::attenuate`]); no parallel cap model.
    pub fn firmament(&self) -> Capability {
        Capability::distributed(self.cap.target, self.cap.permissions.clone())
    }

    /// The rights this cap carries (the held ceiling — any conferral attenuates
    /// from it).
    pub fn rights(&self) -> &AuthRequired {
        &self.cap.permissions
    }
}

impl Presentable for HeldCapability {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Capability
    }

    fn present(&self, ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the cap's genuine fields as an
        //     Inspectable (the same CapEdge primitive reflect_cell emits, here
        //     unpacked into the full c-list-entry detail).
        let insp = cap_raw_fields(self);
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Capability".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Lattice — the REAL AuthRequired partial order, with the held cap's
        //     tier marked (the Hasse diagram derived from is_narrower_or_equal).
        let lattice = auth_lattice_view(self.rights());
        out.push(Presentation {
            kind: PresentationKind::Graph,
            label: "Rights Lattice".to_string(),
            search_text: format!(
                "rights lattice authority {}",
                lattice.nodes.join(" ")
            ),
            body: PresentationBody::Lattice(lattice),
        });

        // (3) Graph — the ocap delegation neighborhood: the genuine OcapGraph
        //     restricted to the edges touching THIS held cap's holder/target.
        let graph = cap_ocap_neighborhood(ctx.world, self);
        out.push(Presentation {
            kind: PresentationKind::Graph,
            label: "ocap Delegation".to_string(),
            search_text: format!(
                "ocap delegation {} edges {} nodes",
                graph.edges.len(),
                graph.nodes.len()
            ),
            body: PresentationBody::Graph(graph),
        });

        // (4) MerkleTree — the cap-crown: the REAL openable capability_root over
        //     the holder's c-list, with this cap's genuine leaf digest as the
        //     highlighted leaf. The root is the #103 sorted-Poseidon2 root.
        if let Some(tree) = cap_crown_view(ctx.world, self) {
            out.push(Presentation {
                kind: PresentationKind::Invariant,
                label: "Cap-Crown".to_string(),
                search_text: format!("cap-crown capability_root {}", tree.label),
                body: PresentationBody::MerkleTree(tree),
            });
        }

        // (5) Invariant — the non-amplification readout: held ⊇ granted, the
        //     genuine is_attenuation judge over the held rights vs the lattice.
        let invariant = nonamp_invariant(self);
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Non-Amplification".to_string(),
            search_text: PresentationBody::Fields(invariant.clone()).search_text(),
            body: PresentationBody::Fields(invariant),
        });

        out
    }
}

/// The cap's RawFields body — the full c-list-entry detail (the genuine fields of
/// the `CapabilityRef`, surfaced as a field tree the existing widget renders).
fn cap_raw_fields(held: &HeldCapability) -> Inspectable {
    let cap = &held.cap;
    let mut fields = vec![
        Field::id("holder", *held.holder.as_bytes()),
        Field::id("target", *cap.target.as_bytes()),
        Field::count("slot", cap.slot as u64),
        Field::text("rights", auth_label(&cap.permissions)),
        Field::boolean("faceted", cap.allowed_effects.is_some()),
        Field::boolean("delegated_snapshot", cap.stored_epoch.is_some()),
    ];
    if let Some(exp) = cap.expires_at {
        fields.push(Field::count("expires_at", exp));
    }
    if let Some(bs) = &cap.breadstuff {
        fields.push(Field::hash("breadstuff", *bs));
    }
    if let Some(epoch) = cap.stored_epoch {
        fields.push(Field::count("stored_epoch", epoch));
    }
    Inspectable {
        kind: ObjectKind::Capability,
        title: format!(
            "Cap · slot {} → {}",
            cap.slot,
            reflect::short_hex(cap.target.as_bytes())
        ),
        subtitle: format!("held by {}", reflect::short_hex(held.holder.as_bytes())),
        fields,
    }
}

/// The cap's ocap delegation neighborhood: the genuine [`OcapGraph`] restricted to
/// the edges touching this cap's holder or target. The real graph primitives, read
/// off the live ledger (never a parallel edge model).
fn cap_ocap_neighborhood(world: &World, held: &HeldCapability) -> GraphView {
    let g = OcapGraph::build(world);
    let holder = held.holder;
    let target = held.cap.target;
    let edges: Vec<crate::graph::GraphEdge> = g
        .edges()
        .iter()
        .filter(|e| {
            e.holder == holder || e.target == holder || e.holder == target || e.target == target
        })
        .cloned()
        .collect();
    let mut node_ids: std::collections::BTreeSet<CellId> = std::collections::BTreeSet::new();
    node_ids.insert(holder);
    node_ids.insert(target);
    for e in &edges {
        node_ids.insert(e.holder);
        node_ids.insert(e.target);
    }
    let nodes: Vec<crate::graph::GraphNode> = g
        .nodes()
        .iter()
        .filter(|n| node_ids.contains(&n.cell))
        .cloned()
        .collect();
    GraphView { nodes, edges, focus: Some(holder) }
}

/// The cap-crown [`MerkleTreeView`]: the REAL openable `capability_root` over the
/// holder's whole c-list (the #103 sorted-Poseidon2 root,
/// [`compute_canonical_capability_root_felt`]), with THIS cap's genuine leaf
/// digest ([`cap_ref_to_leaf`]) marked as the highlighted leaf.
///
/// MEMBERSHIP-PATH NOTE: the cell crate exposes the canonical ROOT and the leaf
/// ENCODING, but the leaf→root sibling/direction PATH lives in
/// `dregg_circuit::cap_root::CanonicalCapTree::membership_witness`, which is NOT
/// re-exported through `dregg_cell` and is not a direct dependency of this crate.
/// So this view carries the real root + the real leaves (and marks this cap's leaf
/// in `path`); the full opened sibling path is a REPORTED missing route, not a
/// faked path.
fn cap_crown_view(world: &World, held: &HeldCapability) -> Option<MerkleTreeView> {
    let cell = world.ledger().get(&held.holder)?;
    let caps = &cell.capabilities;

    // The genuine sorted-Poseidon2 root over the live c-list (with tombstones).
    let root_felt = compute_canonical_capability_root_felt(caps);
    let root = felt_to_bytes32(root_felt);

    // The genuine leaf digest of every held cap (the sorted-tree leaves), and the
    // highlighted leaf for THIS cap.
    let mut leaves: Vec<String> = Vec::new();
    let mut this_leaf: Option<String> = None;
    for c in caps.iter() {
        let leaf_digest = felt_to_bytes32(cap_ref_to_leaf(c).digest());
        let leaf_hex = reflect::short_hex(&leaf_digest);
        if c.slot == held.cap.slot && c.target == held.cap.target {
            this_leaf = Some(leaf_hex.clone());
        }
        leaves.push(leaf_hex);
    }

    Some(MerkleTreeView {
        label: format!(
            "capability_root over {} held cap(s)",
            caps.len()
        ),
        leaves,
        root,
        // The highlighted leaf (this cap's genuine digest). The full opened
        // sibling path is the reported missing route (see fn doc).
        path: this_leaf.into_iter().collect(),
    })
}

/// The non-amplification [`Inspectable`]: the `granted ⊆ held` readout for THIS
/// cap, computed by the REAL [`is_attenuation`]. For each built-in tier it reports
/// whether conferring that tier from this held cap WOULD be a legal attenuation —
/// the exact set the executor's grant gate permits. This makes the in-band
/// non-amplification property legible (the ARGUS linchpin).
fn nonamp_invariant(held: &HeldCapability) -> Inspectable {
    let h = held.rights();
    let mut fields: Vec<Field> = vec![Field::text("held_rights", auth_label(h))];
    for tier in LATTICE_TIERS.iter() {
        let legal = is_attenuation(h, tier);
        fields.push(Field::text(
            format!("confer {}", auth_label(tier)),
            if legal {
                "✓ attenuation (granted ⊆ held)".to_string()
            } else {
                "✗ would AMPLIFY — refused".to_string()
            },
        ));
    }
    Inspectable {
        kind: ObjectKind::Capability,
        title: "Non-Amplification (granted ⊆ held)".to_string(),
        subtitle: format!(
            "held {} — only ⊆ tiers are conferrable",
            auth_label(h)
        ),
        fields,
    }
}

// ===========================================================================
// §L4.2 — the Attenuation Dial (a Gadget building an attenuated Capability)
// ===========================================================================

/// **THE ATTENUATION DIAL** — a [`Gadget`] that narrows a held capability.
///
/// It takes a held firmament [`Capability`] (the ceiling), lets the operator
/// designate a narrower rights tier, and validates the narrowing with the REAL
/// [`is_attenuation`] (`granted ⊆ held`) — a widening is refused FAIL-CLOSED, in
/// band, exactly as [`Capability::attenuate`] returns `None`. [`Gadget::build`]
/// materializes the attenuated firmament `Capability` (riding `attenuate`, never a
/// hand-rolled narrowing).
///
/// Where the attenuation is to be MINTED into a grantee, [`Self::grant_through_powerbox`]
/// rides the established [`Powerbox::grant`] ceremony — the same verified-executor
/// `GrantCapability` turn the cockpit's powerbox panel drives.
#[derive(Clone, Debug)]
pub struct AttenuationDial {
    /// The HELD capability (the ceiling) — the real firmament handle. Its rights
    /// are the upper bound; the dial can only narrow.
    held: Capability,
    /// The designated narrower rights (the dial's current setting). `None` until
    /// the operator picks a tier (the form is incomplete until then).
    designated: Option<AuthRequired>,
}

impl AttenuationDial {
    /// A dial over a held firmament [`Capability`] (the ceiling). The designated
    /// rights start unset — the form is incomplete until a tier is chosen.
    pub fn new(held: Capability) -> Self {
        AttenuationDial { held, designated: None }
    }

    /// A dial over a [`HeldCapability`] (the c-list entry lifted into the
    /// firmament handle). The common entry from an inspector's `Attenuate` halo.
    pub fn over_held(held: &HeldCapability) -> Self {
        AttenuationDial::new(held.firmament())
    }

    /// The held ceiling rights — the upper bound any designation must be `⊆`.
    pub fn ceiling(&self) -> &Rights {
        &self.held.rights
    }

    /// The held cap's target cell, if it is a distributed/surface handle (the
    /// grant target). A purely-local kernel-slot handle has no dregg cell target.
    pub fn target_cell(&self) -> Option<CellId> {
        match &self.held.target {
            Target::Distributed { cell } | Target::Surface { cell } => Some(*cell),
            // A local kernel-slot handle and a confined HOST-PD handle (an OS-
            // sandboxed subprocess reached over the firmament Endpoint) are not
            // dregg cells, so they carry no cell target.
            Target::Local { .. } | Target::HostPd { .. } => None,
        }
    }

    /// The variant names the rights `Enum` field offers (the built-in tiers).
    fn tier_variants() -> Vec<String> {
        LATTICE_TIERS.iter().map(tier_slug).collect()
    }

    /// **MINT the attenuated cap into `app_cell` through the REAL powerbox.** The
    /// dial's designated rights are conferred from `principal` (who must HOLD the
    /// target) into the grantee via [`Powerbox::grant`] — a genuine
    /// `Effect::GrantCapability` turn through the verified executor. Both gates
    /// (`is_attenuation` pre-check + the executor's no-amplification backstop) are
    /// the powerbox's own; we reinvent neither. Returns the powerbox outcome (a
    /// `Granted` receipt or a `Denied` reason) — fail-closed surfaced, never faked.
    ///
    /// Fails closed (a `Denied`) if the dial is not yet valid, or the held handle
    /// is not a dregg-cell target (a local kernel slot has no powerbox path).
    pub fn grant_through_powerbox(
        &self,
        world: &mut World,
        principal: CellId,
        app_cell: CellId,
    ) -> PowerboxOutcome {
        let Some(rights) = self.designated.clone() else {
            return PowerboxOutcome::Denied {
                reason: "the attenuation dial has no designated rights yet (incomplete)".to_string(),
            };
        };
        if !is_attenuation(&self.held.rights, &rights) {
            return PowerboxOutcome::Denied {
                reason: format!(
                    "designated {:?} would AMPLIFY the held {:?} — the dial is attenuation-only",
                    rights, self.held.rights
                ),
            };
        }
        let Some(target) = self.target_cell() else {
            return PowerboxOutcome::Denied {
                reason: "the held cap is a local kernel slot — no powerbox/executor grant path"
                    .to_string(),
            };
        };
        // Ride the established ceremony: the powerbox re-checks the principal HOLDS
        // the target and the conferral attenuates, then mints the real turn.
        Powerbox::grant(world, principal, app_cell, target, rights)
    }
}

/// The dial's tier slug (the Enum variant key the gpui layer renders / set() takes).
/// `Custom` is keyed by a fixed slug here (the built-in tiers are the dial's pickable
/// set; a Custom-tier attenuation is conferred by passing the held Custom unchanged).
fn tier_slug(a: &AuthRequired) -> String {
    match a {
        AuthRequired::None => "None".to_string(),
        AuthRequired::Signature => "Signature".to_string(),
        AuthRequired::Proof => "Proof".to_string(),
        AuthRequired::Either => "Either".to_string(),
        AuthRequired::Impossible => "Impossible".to_string(),
        AuthRequired::Custom { .. } => "Custom".to_string(),
    }
}

/// Parse a tier slug back into the built-in [`AuthRequired`] (the inverse of
/// [`tier_slug`] over the built-in tiers). `None` for an unknown / Custom slug
/// (Custom carries a vk_hash the dial does not synthesize).
fn tier_from_slug(slug: &str) -> Option<AuthRequired> {
    match slug {
        "None" => Some(AuthRequired::None),
        "Signature" => Some(AuthRequired::Signature),
        "Proof" => Some(AuthRequired::Proof),
        "Either" => Some(AuthRequired::Either),
        "Impossible" => Some(AuthRequired::Impossible),
        _ => None,
    }
}

impl Gadget for AttenuationDial {
    /// The dial builds an attenuated firmament [`Capability`] — the same handle
    /// `Capability::attenuate` returns.
    type Output = Capability;

    fn fields(&self) -> Vec<GadgetField> {
        vec![GadgetField::Enum {
            key: "rights".to_string(),
            variants: Self::tier_variants(),
        }]
    }

    fn set(&mut self, field: &str, v: GadgetInput) {
        if field == "rights" {
            if let GadgetInput::Variant(slug) = v {
                self.designated = tier_from_slug(&slug);
            }
        }
    }

    fn validate(&self) -> GadgetValidation {
        match &self.designated {
            None => GadgetValidation::Invalid {
                reason: "pick a rights tier to attenuate to".to_string(),
            },
            Some(rights) => {
                // THE REAL non-amplification judge: a widening is fail-closed.
                if is_attenuation(&self.held.rights, rights) {
                    GadgetValidation::Ok
                } else {
                    GadgetValidation::Invalid {
                        reason: format!(
                            "{} would AMPLIFY the held {} — attenuation-only (granted ⊆ held)",
                            auth_label(rights),
                            auth_label(&self.held.rights)
                        ),
                    }
                }
            }
        }
    }

    fn build(&self) -> Result<Self::Output, GadgetError> {
        let rights = self.designated.clone().ok_or_else(|| GadgetError::Incomplete {
            reason: "no rights tier designated".to_string(),
        })?;
        // Ride the REAL Capability::attenuate — it gates on is_attenuation and
        // returns None on a widening (the same fail-closed the executor models).
        self.held.attenuate(rights).ok_or_else(|| GadgetError::Lowering {
            reason: "the designated rights are not an attenuation of the held cap".to_string(),
        })
    }
}

// ===========================================================================
// TESTS — proven gpui-free against the REAL machinery (as presentable.rs is).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// A world where `holder` holds a cap reaching `sink`. Returns
    /// `(world, holder, sink, slot)`. Reuses `genesis_cell_with_cap` (the same
    /// helper `presentable.rs`'s graph test uses), so the cap is a genuine
    /// c-list entry the executor seeded.
    fn cap_world() -> (World, CellId, CellId, u32) {
        let mut w = World::new();
        let sink = w.genesis_cell(0xB0, 0);
        let (holder, slot) = w.genesis_cell_with_cap(0xA0, 1_000, sink);
        (w, holder, sink, slot)
    }

    // ── the RawFields floor + a multi-presentation set ──────────────────────

    #[test]
    fn a_held_cap_yields_the_raw_fields_floor_and_a_rich_set() {
        let (w, holder, _sink, slot) = cap_world();
        let held = HeldCapability::from_world(&w, holder, slot).expect("the held cap exists");
        let ctx = PresentCtx::new(&w, holder);

        let set = held.present(&ctx);
        // The mandatory RawFields floor is present and non-empty.
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .expect("RawFields floor");
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "rights"));
                assert!(i.fields.iter().any(|f| f.key == "target"));
            }
            other => panic!("RawFields must be a Fields body, got {other:?}"),
        }
        // The cap family offers the L4 set: Lattice + Graph + cap-crown + non-amp.
        assert!(set
            .iter()
            .any(|p| matches!(p.body, PresentationBody::Lattice(_))));
        assert!(set
            .iter()
            .any(|p| matches!(p.body, PresentationBody::Graph(_))));
        assert!(set
            .iter()
            .any(|p| matches!(p.body, PresentationBody::MerkleTree(_))));
        assert!(set.iter().any(|p| p.label == "Non-Amplification"));
    }

    // ── the Lattice reflects the REAL rights order ──────────────────────────

    #[test]
    fn the_lattice_reflects_the_real_rights_order() {
        // The covering relations are the genuine is_narrower_or_equal Hasse cover:
        // Signature ⊑ Either, Proof ⊑ Either, Impossible ⊑ everything, _ ⊑ None.
        let view = auth_lattice_view(&AuthRequired::Either);

        // The nodes are the five built-in tiers, weakest-first ends at None.
        assert_eq!(view.nodes.len(), 5);
        assert!(view.nodes.last().unwrap().starts_with("None"));

        // The held tier (Either) is marked current.
        let either_idx = LATTICE_TIERS.iter().position(|t| t == &AuthRequired::Either).unwrap();
        assert_eq!(view.current, Some(either_idx));

        // A real covering edge: Signature ⊑ Either (Signature is narrower than Either).
        let sig_idx = LATTICE_TIERS.iter().position(|t| t == &AuthRequired::Signature).unwrap();
        let proof_idx = LATTICE_TIERS.iter().position(|t| t == &AuthRequired::Proof).unwrap();
        assert!(
            view.edges.contains(&(sig_idx, either_idx)),
            "Signature ⊑ Either is a covering edge"
        );
        assert!(
            view.edges.contains(&(proof_idx, either_idx)),
            "Proof ⊑ Either is a covering edge"
        );
        // The covers agree with the real predicate: every edge (i,j) really IS
        // is_narrower_or_equal in the live lattice.
        for &(i, j) in &view.edges {
            assert!(
                LATTICE_TIERS[i].is_narrower_or_equal(&LATTICE_TIERS[j]),
                "every lattice edge is a real is_narrower_or_equal relation"
            );
        }
    }

    // ── attenuation narrows; a widening is refused by the REAL is_attenuation ─

    #[test]
    fn the_dial_narrows_and_refuses_a_widening_via_real_is_attenuation() {
        // A held Either cap can be narrowed to Signature (a real attenuation).
        let held = Capability::distributed(
            CellId::derive_raw(&[0x11u8; 32], &[0u8; 32]),
            AuthRequired::Either,
        );
        let mut dial = AttenuationDial::new(held.clone());

        // Incomplete until a tier is picked (fail-closed).
        assert!(dial.validate().is_fail_closed());

        // Narrow Either → Signature: a real attenuation, validates Ok, builds.
        dial.set("rights", GadgetInput::Variant("Signature".to_string()));
        assert!(dial.validate().is_ok(), "Signature ⊆ Either is an attenuation");
        let narrowed = dial.build().expect("the attenuated cap builds");
        assert_eq!(narrowed.rights, AuthRequired::Signature);
        // The target is preserved (attenuation narrows rights, not the target).
        assert_eq!(narrowed.target, held.target);

        // Now hold a narrow Signature cap and try to WIDEN it to Either — the REAL
        // is_attenuation refuses it: validation is fail-closed and build() errs.
        let narrow_held =
            Capability::distributed(CellId::derive_raw(&[0x11u8; 32], &[0u8; 32]), AuthRequired::Signature);
        let mut widen = AttenuationDial::new(narrow_held);
        widen.set("rights", GadgetInput::Variant("Either".to_string()));
        assert!(
            widen.validate().is_fail_closed(),
            "Either ⊄ Signature — a widening is refused in-band"
        );
        assert!(widen.build().is_err(), "the widening cannot build (fail-closed)");
    }

    #[test]
    fn the_dial_build_agrees_with_capability_attenuate() {
        // The dial's build() IS Capability::attenuate — they agree exactly.
        let held = Capability::distributed(
            CellId::derive_raw(&[0x22u8; 32], &[0u8; 32]),
            AuthRequired::Either,
        );
        let mut dial = AttenuationDial::new(held.clone());
        dial.set("rights", GadgetInput::Variant("Proof".to_string()));
        let built = dial.build().unwrap();
        let direct = held.attenuate(AuthRequired::Proof).unwrap();
        assert_eq!(built, direct, "the dial rides the real Capability::attenuate");
    }

    // ── the Graph shows real delegation edges ───────────────────────────────

    #[test]
    fn the_graph_shows_real_delegation_edges() {
        let (w, holder, sink, slot) = cap_world();
        let held = HeldCapability::from_world(&w, holder, slot).unwrap();
        let ctx = PresentCtx::new(&w, holder);
        let set = held.present(&ctx);

        let graph = set
            .iter()
            .find(|p| p.label == "ocap Delegation")
            .expect("the delegation graph presentation");
        match &graph.body {
            PresentationBody::Graph(g) => {
                assert_eq!(g.focus, Some(holder));
                assert!(
                    g.edges.iter().any(|e| e.holder == holder && e.target == sink),
                    "the real ocap edge holder → sink is in the neighborhood"
                );
            }
            other => panic!("expected a Graph body, got {other:?}"),
        }
    }

    // ── the cap-crown MerkleTree carries the REAL capability_root ────────────

    #[test]
    fn the_cap_crown_carries_the_real_capability_root_and_this_caps_leaf() {
        let (w, holder, _sink, slot) = cap_world();
        let held = HeldCapability::from_world(&w, holder, slot).unwrap();
        let ctx = PresentCtx::new(&w, holder);
        let set = held.present(&ctx);

        let crown = set
            .iter()
            .find(|p| p.label == "Cap-Crown")
            .expect("the cap-crown presentation");
        match &crown.body {
            PresentationBody::MerkleTree(m) => {
                // The root is the genuine sorted-Poseidon2 capability_root — non-zero
                // (the sentinels hash into a real value), matching the cell crate.
                let cell = w.ledger().get(&holder).unwrap();
                let expect_root =
                    felt_to_bytes32(compute_canonical_capability_root_felt(&cell.capabilities));
                assert_eq!(m.root, expect_root, "the real openable capability_root");
                assert_ne!(m.root, [0u8; 32], "the cap-crown root is non-zero");
                // The held cap's genuine leaf digest is among the leaves and marked.
                assert!(!m.leaves.is_empty(), "the c-list leaves are surfaced");
                assert_eq!(m.path.len(), 1, "this cap's leaf is the highlighted leaf");
                assert!(m.leaves.contains(&m.path[0]));
            }
            other => panic!("expected a MerkleTree body, got {other:?}"),
        }
    }

    // ── the non-amplification readout is the real is_attenuation set ─────────

    #[test]
    fn the_nonamp_readout_is_the_real_is_attenuation_set() {
        // A held Signature cap: only Signature and Impossible are ⊆ it (None/Either
        // are wider, Proof is incomparable) — the genuine is_attenuation set.
        let held = HeldCapability {
            holder: CellId::derive_raw(&[0x33u8; 32], &[0u8; 32]),
            cap: CapabilityRef {
                target: CellId::derive_raw(&[0x44u8; 32], &[0u8; 32]),
                slot: 0,
                permissions: AuthRequired::Signature,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: None,
            },
        };
        let insp = nonamp_invariant(&held);
        let confer_sig = insp
            .fields
            .iter()
            .find(|f| f.key.contains("Signature"))
            .unwrap();
        match &confer_sig.value {
            reflect::FieldValue::Text(t) => assert!(t.contains("attenuation")),
            _ => unreachable!(),
        }
        let confer_none = insp.fields.iter().find(|f| f.key.contains("None")).unwrap();
        match &confer_none.value {
            // None is WIDER than Signature → conferring None amplifies → refused.
            reflect::FieldValue::Text(t) => assert!(t.contains("AMPLIFY")),
            _ => unreachable!(),
        }
    }

    // ── the dial mints through the REAL powerbox grant ceremony ──────────────

    #[test]
    fn the_dial_grants_through_the_real_powerbox() {
        // holder holds an Either cap reaching sink; an app launched with no
        // authority can be GRANTED a narrowed (Signature) cap to sink through the
        // dial → the real Powerbox::grant → a genuine executor turn.
        let (mut w, holder, sink, slot) = cap_world();
        let app = w.genesis_cell(0xC0, 0);

        let held = HeldCapability::from_world(&w, holder, slot).unwrap();
        let mut dial = AttenuationDial::over_held(&held);
        dial.set("rights", GadgetInput::Variant("Signature".to_string()));
        assert!(dial.validate().is_ok());
        assert_eq!(dial.target_cell(), Some(sink));

        let outcome = dial.grant_through_powerbox(&mut w, holder, app);
        assert!(outcome.is_granted(), "the powerbox minted the attenuated cap: {outcome:?}");
        let conferred = outcome.conferred().unwrap();
        assert_eq!(conferred.app_cell, app);
        assert_eq!(conferred.target, sink);
        assert_eq!(conferred.conferred_rights, AuthRequired::Signature);

        // The app's live c-list now genuinely holds the narrowed cap (a real turn
        // committed it — not a faked grant).
        let app_held = HeldCapability::all_for(&w, app);
        assert!(
            app_held.iter().any(|h| h.cap.target == sink
                && h.cap.permissions == AuthRequired::Signature),
            "the app holds the granted attenuated cap after the real turn"
        );
    }

    #[test]
    fn the_dial_refuses_to_grant_a_widening_through_the_powerbox() {
        // A held Signature cap cannot be granted as Either: the dial's own
        // is_attenuation pre-check denies it (before the powerbox is even asked).
        let mut w = World::new();
        let sink = w.genesis_cell(0xB0, 0);
        // Seed a holder with a NARROW (Signature) cap reaching sink by attenuating
        // a granted cap through the dial first would be circular; instead build the
        // dial directly over a Signature firmament handle to assert the refusal.
        let _ = sink;
        let narrow =
            Capability::distributed(CellId::derive_raw(&[0x55u8; 32], &[0u8; 32]), AuthRequired::Signature);
        let mut dial = AttenuationDial::new(narrow);
        dial.set("rights", GadgetInput::Variant("Either".to_string()));
        let app = w.genesis_cell(0xC0, 0);
        let holder = CellId::derive_raw(&[0x55u8; 32], &[0u8; 32]);
        let outcome = dial.grant_through_powerbox(&mut w, holder, app);
        assert!(!outcome.is_granted(), "a widening grant is denied in-band");
    }

    // ── the field-form is well-formed ───────────────────────────────────────

    #[test]
    fn the_dial_field_form_is_well_formed() {
        let held = Capability::distributed(
            CellId::derive_raw(&[0x66u8; 32], &[0u8; 32]),
            AuthRequired::Either,
        );
        let dial = AttenuationDial::new(held);
        let fields = dial.fields();
        assert_eq!(fields.len(), 1);
        match &fields[0] {
            GadgetField::Enum { key, variants } => {
                assert_eq!(key, "rights");
                assert!(variants.contains(&"Signature".to_string()));
                assert!(variants.contains(&"Either".to_string()));
            }
            other => panic!("expected an Enum field, got {other:?}"),
        }
    }
}
