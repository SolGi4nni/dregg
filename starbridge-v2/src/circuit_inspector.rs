//! L9 — CIRCUIT & COMMITMENT INTERNALS, on the moldable-inspector spine
//! (`presentable.rs`).
//!
//! `proofs.rs` already gives every committed turn its honest verification TIER
//! (`VerifiedByConstruction` / `ExecutorSigned` / `StarkAttached`) and its
//! attach point. This module lifts the proof / commitment / nullifier family of
//! slices 7 & 11 onto the `Presentable`/`Gadget` shapes the L1 spine defines,
//! reusing — never reinventing — the real machinery:
//!
//!   * the verification tier + attach posture is the REAL
//!     [`crate::proofs::ProofBoard`]/[`crate::proofs::ProofEntry`] (built off the
//!     live receipt log), surfaced as a `Provenance` (the pre→post commitment
//!     chain) + a tier `Lattice` (the three honest tiers) + an `Invariant` (what
//!     each tier binds);
//!   * the **8-felt state commitment** is the REAL
//!     [`dregg_cell::compute_canonical_state_commitment`] (`cell/src/commitment.rs`,
//!     the single source of truth for "what bytes commit to this cell"), surfaced
//!     as an `Invariant` that enumerates what it binds — identity · mode · state ·
//!     permissions · VK · cap_root · delegate · delegation · program · lifecycle —
//!     PLUS a verifier [`Gadget`] that recomputes it and compares (the anti-ghost
//!     tooth: a tampered cell recomputes to a different commitment, in-band);
//!   * the **nullifier set** is the REAL [`dregg_cell::NullifierSet`] with its
//!     real Merkle `root()` and its real `verify_non_membership`, surfaced as a
//!     `MerkleTree` + an `Invariant` (double-spend = non-membership) PLUS a
//!     non-membership verifier [`Gadget`] running the genuine adjacent-neighbor
//!     fold;
//!   * a **note commitment** is the REAL [`dregg_cell::Note`]/[`dregg_cell::NoteCommitment`]
//!     (the Poseidon2 commitment that IS the circuit-side felt), surfaced as a
//!     creation `Trace` PLUS a hasher verifier [`Gadget`] that recomputes the
//!     commitment from the note preimage and compares.
//!
//! ## The honest boundary (REPORTED, not faked)
//!
//! The IR-v2 descriptor types the census names for slice 11 —
//! `EffectVmDescriptor2` / `TableDef2` / `VmConstraint2` / `AirDescriptor` /
//! `BatchProof` — live in the `dregg-circuit` crate, which is NOT a direct
//! dependency of `starbridge-v2` and is NOT re-exported through the crates that
//! ARE (`dregg-cell` references `dregg_circuit::field::BabyBear` /
//! `dregg_circuit::cap_root` only in function *signatures*, never re-exporting the
//! types). So those descriptor objects are NOT reachable. Rather than fabricate a
//! parallel descriptor model, [`DescriptorBoundary`] surfaces the descriptor
//! IR-v2 SHAPE from its on-disk artifact contract (the `circuit/descriptors/*.json`
//! the prover/verifier already read) as a `Source` presentation, and names the
//! dep route to reach the live types honestly. This is the same discipline
//! `cap_inspector.rs` uses for the cap-membership sibling path (real root, marked
//! leaf, reported missing path).
//!
//! gpui-free + `cargo test`-able exactly as `presentable.rs`/`proofs.rs`/
//! `reflect.rs` are.

use dregg_cell::{
    compute_canonical_state_commitment, Cell, CellId, Note, NoteCommitment, Nullifier, NullifierSet,
};

use crate::presentable::{
    Gadget, GadgetError, GadgetField, GadgetInput, GadgetValidation, MerkleTreeView, PresentCtx,
    Presentable, Presentation, PresentationBody, PresentationKind, TimelineEvent, TimelineView,
    TraceStep, TraceView,
};
use crate::proofs::{ProofBoard, ProofEntry, VerificationTier};
use crate::reflect::{self, Field, Inspectable, ObjectKind};
use crate::world::World;

// ===========================================================================
// §L9.0 — a shared verifier result (the read-only gadget Output)
// ===========================================================================

/// The verdict a read-only verifier [`Gadget`] returns: did the REAL machinery
/// accept? Mirrors `receipts_inspector.rs`'s verifier-result shape (green/red +
/// a count + human-legible notes). A verifier gadget runs genuine cryptographic
/// machinery (`compute_canonical_state_commitment`, `verify_non_membership`,
/// `Note::commitment`) and reports its honest verdict — it never commits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerificationResult {
    /// `true` iff the real machinery accepted (the green state).
    pub ok: bool,
    /// How many checks were exercised.
    pub checked: usize,
    /// Human-legible per-check notes (the audit trail the panel shows).
    pub notes: Vec<String>,
}

impl VerificationResult {
    fn green(checked: usize, note: impl Into<String>) -> Self {
        VerificationResult {
            ok: true,
            checked,
            notes: vec![note.into()],
        }
    }
    fn red(checked: usize, note: impl Into<String>) -> Self {
        VerificationResult {
            ok: false,
            checked,
            notes: vec![note.into()],
        }
    }
}

// ===========================================================================
// §L9.1 — the PROOF family: VerificationTier + ProofEntry as a Presentable
// ===========================================================================

/// A thin newtype over one committed turn's REAL [`ProofEntry`] (built by
/// [`ProofBoard::build`] off the live receipt log), lifted into the moldable
/// inspector. The proof posture is the genuine `proofs.rs` tiering — never
/// re-inflated: a tier-1 turn presents as tier-1, and the binding chain is the
/// real pre→post state commitment the receipt carries.
#[derive(Clone, Debug)]
pub struct ProvenTurn {
    /// The real proof entry (verification tier + attach status + pre/post commit).
    pub entry: ProofEntry,
}

impl ProvenTurn {
    /// The proof entries for every committed turn in the live world (most-recent
    /// first), each wrapped as a [`ProvenTurn`]. Reuses [`ProofBoard::build`]
    /// verbatim — no parallel classification.
    pub fn all(world: &World) -> Vec<ProvenTurn> {
        ProofBoard::build(world, usize::MAX)
            .entries
            .into_iter()
            .map(|entry| ProvenTurn { entry })
            .collect()
    }
}

impl Presentable for ProvenTurn {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Proof
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let e = &self.entry;
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the genuine reflect_proof_status
        //     Inspectable the ProofEntry already carries (the receipt's full
        //     attestation surface). No parallel projection.
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Proof Status".to_string(),
            search_text: PresentationBody::Fields(e.inspectable.clone()).search_text(),
            body: PresentationBody::Fields(e.inspectable.clone()),
        });

        // (2) DomainVisual — the three honest verification tiers as a lattice, with
        //     THIS turn's tier marked. The order is the real tier strength.
        let tiers = [
            VerificationTier::VerifiedByConstruction,
            VerificationTier::ExecutorSigned,
            VerificationTier::StarkAttached,
        ];
        let current = tiers.iter().position(|t| *t == e.tier);
        let lattice = crate::presentable::LatticeView {
            nodes: tiers.iter().map(|t| t.label().to_string()).collect(),
            // The covering relations: by-construction ⊑ signed ⊑ STARK.
            edges: vec![(0, 1), (1, 2)],
            current,
        };
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Verification Tier".to_string(),
            search_text: format!("tier {} {}", e.tier.label(), e.attach.label()),
            body: PresentationBody::Lattice(lattice),
        });

        // (3) Provenance — the binding chain the STARK (tier 3) would bind: the
        //     turn carried pre_state_commit → post_state_commit. The real hashes
        //     the receipt carries (short-form here; navigable in the panel).
        let prov = TimelineView {
            events: vec![
                TimelineEvent {
                    at: e.height.saturating_sub(1),
                    label: format!("pre-state commitment {}", e.pre_state_short),
                    hash: None,
                },
                TimelineEvent {
                    at: e.height,
                    label: format!(
                        "post-state commitment {} (the commitment the proof binds)",
                        e.post_state_short
                    ),
                    hash: Some(e.receipt_hash),
                },
            ],
        };
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Commitment Binding Chain".to_string(),
            search_text: format!("binding {} {}", e.pre_state_short, e.post_state_short),
            body: PresentationBody::Timeline(prov),
        });

        // (4) Invariant — what THIS turn's tier binds, honestly (the pale-ghost
        //     answer from proofs.rs §5: can a light client be fooled about whether
        //     the turn was verified?). The readout names what each tier binds and
        //     the route to the next, never claiming a higher tier than the receipt
        //     carries.
        let mut fields = vec![
            Field::text("tier", e.tier.label()),
            Field::count("tier_strength", e.tier.strength() as u64),
            Field::text("attach", e.attach.label()),
            Field::text(
                "binds",
                match e.tier {
                    VerificationTier::VerifiedByConstruction => {
                        "the operator's own re-execution (the verified executor enforced every \
                         whole-turn guarantee inline; the receipt's existence is the proof)"
                    }
                    VerificationTier::ExecutorSigned => {
                        "a known producer's Ed25519 signature over the receipt hash (a verifier \
                         checks the signature, no re-execution)"
                    }
                    VerificationTier::StarkAttached => {
                        "nothing but the math (a light client verifies with NO trust in the \
                         producer — the strongest tier)"
                    }
                },
            ),
            Field::boolean("burn_disclosed", e.burn_disclosed),
            Field::boolean("encrypted", e.encrypted),
        ];
        if let Some(route) = e.upgrade_route() {
            fields.push(Field::text("upgrade_route", route));
        } else {
            fields.push(Field::text(
                "upgrade_route",
                "(top tier — no further route)",
            ));
        }
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "What This Tier Binds".to_string(),
            search_text: format!("invariant binds {}", e.tier.label()),
            body: PresentationBody::Fields(Inspectable {
                kind: ObjectKind::Proof,
                title: format!("Verification posture · h{}", e.height),
                subtitle: format!("{} · {}", e.tier.label(), e.attach.label()),
                fields,
            }),
        });

        out
    }
}

// ===========================================================================
// §L9.2 — the 8-FELT STATE COMMITMENT as an Invariant (what it binds)
// ===========================================================================

/// The authority-bearing components the canonical 8-felt state commitment binds
/// — the anti-omission list from `cell/src/commitment.rs`'s
/// [`compute_canonical_state_commitment`]. Each entry is a component an attacker
/// would have to drop to forge two distinct authority states with one commitment;
/// the commitment absorbs ALL of them, so it CANNOT be dropped.
const COMMITMENT_BINDS: &[(&str, &str)] = &[
    ("identity", "id · public_key · token_id"),
    ("mode", "Hosted vs Sovereign"),
    (
        "core_state",
        "nonce · signed balance (biased two-limb LE) · fields · roots · delegation_epoch",
    ),
    (
        "permissions",
        "all eight Permissions tiers (incl. Custom vk_hash)",
    ),
    ("verification_key", "the cell's VK hash (if any)"),
    (
        "capability_root",
        "the openable sorted-Poseidon2 cap-crown root (tombstone-deletion, #103)",
    ),
    ("delegate", "the delegate cell id (if any)"),
    ("delegation", "the delegation snapshot (if any)"),
    ("program", "the installed CellProgram"),
    (
        "lifecycle",
        "Live/Sealed/Migrated/Destroyed/Archived + payload (authority-bearing)",
    ),
];

/// A thin newtype over a live ledger cell, surfacing its **8-felt state
/// commitment** binding as the moldable inspector's `Invariant` face — what the
/// single canonical commitment binds, and a recompute-and-compare verifier. The
/// commitment is the REAL [`compute_canonical_state_commitment`] (the single
/// source of truth for "what bytes commit to this cell"); this view never invents
/// a parallel hash.
#[derive(Clone, Debug)]
pub struct StateCommitmentBinding {
    /// The cell whose commitment this binds.
    pub id: CellId,
    /// A snapshot of the cell (cloned off the live ledger at build time).
    pub cell: Cell,
}

impl StateCommitmentBinding {
    /// Wrap the live cell `id` if present in the world's ledger.
    pub fn from_world(world: &World, id: CellId) -> Option<Self> {
        world.ledger().get(&id).map(|c| StateCommitmentBinding {
            id,
            cell: c.clone(),
        })
    }

    /// The genuine 8-felt canonical commitment for this cell (the real bytes).
    pub fn commitment(&self) -> [u8; 32] {
        compute_canonical_state_commitment(&self.cell)
    }
}

impl Presentable for StateCommitmentBinding {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Cell
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let commit = self.commitment();
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the raw commitment + its short form
        //     + the cell it commits.
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "State Commitment".to_string(),
            search_text: format!(
                "state commitment {} cell {}",
                reflect::short_hex(&commit),
                reflect::short_hex(self.id.as_bytes())
            ),
            body: PresentationBody::Fields(Inspectable {
                kind: ObjectKind::Cell,
                title: format!("State Commitment · {}", reflect::short_hex(&commit)),
                subtitle: "the canonical 8-felt (~124-bit) commitment · the single source of \
                           truth for what bytes commit to this cell"
                    .to_string(),
                fields: vec![
                    Field::id("cell", *self.id.as_bytes()),
                    Field::hash("commitment", commit),
                    Field::text(
                        "scheme",
                        "compute_canonical_state_commitment (cell/src/commitment.rs)",
                    ),
                ],
            }),
        });

        // (2) Invariant — WHAT THE COMMITMENT BINDS: the anti-omission list. Each
        //     row is a component the commitment absorbs; dropping any one would let
        //     an attacker present two distinct authority states with one
        //     commitment. The commitment absorbs all of them, so none can be
        //     dropped — the pale-ghost-proof readout.
        let fields: Vec<Field> = COMMITMENT_BINDS
            .iter()
            .map(|(component, what)| Field::text(*component, *what))
            .collect();
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "What the Commitment Binds".to_string(),
            search_text: format!(
                "invariant binds {}",
                COMMITMENT_BINDS
                    .iter()
                    .map(|(c, _)| *c)
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            body: PresentationBody::Fields(Inspectable {
                kind: ObjectKind::Cell,
                title: "Commitment Binding (anti-omission)".to_string(),
                subtitle: format!(
                    "{} authority-bearing components absorbed — omitting any one is a soundness \
                     hole",
                    COMMITMENT_BINDS.len()
                ),
                fields,
            }),
        });

        // (3) Trace — the absorption ORDER the canonical hasher walks (the
        //     domain-separated derive-key fold). Step-by-step, matching the real
        //     `compute_canonical_state_commitment` body.
        let steps: Vec<TraceStep> = COMMITMENT_BINDS
            .iter()
            .enumerate()
            .map(|(i, (component, _))| TraceStep {
                index: i,
                label: format!("absorb {component}"),
            })
            .collect();
        out.push(Presentation {
            kind: PresentationKind::Source,
            label: "Absorption Order".to_string(),
            search_text: "trace absorb commitment".to_string(),
            body: PresentationBody::Trace(TraceView { steps }),
        });

        out
    }
}

/// THE COMMITMENT RECOMPUTE VERIFIER — a read-only [`Gadget`] that recomputes a
/// cell's canonical commitment with the REAL
/// [`compute_canonical_state_commitment`] and compares it to a pinned reference.
/// This is the anti-ghost tooth: a cell tampered in ANY authority-bearing
/// component recomputes to a DIFFERENT commitment, so the comparison fails
/// in-band. No commit; pure cryptographic re-check.
#[derive(Clone, Debug)]
pub struct CommitmentRecomputeVerifier {
    /// The cell whose commitment is recomputed.
    cell: Cell,
    /// The reference commitment to compare against (the published/pinned value).
    expected: [u8; 32],
}

impl CommitmentRecomputeVerifier {
    /// A verifier over a cell + the commitment it is CLAIMED to have. The verifier
    /// recomputes the genuine commitment and reports whether it matches.
    pub fn new(cell: Cell, expected: [u8; 32]) -> Self {
        CommitmentRecomputeVerifier { cell, expected }
    }

    /// A verifier pinned to the cell's OWN genuine commitment (the self-consistent
    /// case — always green unless the cell is mutated after pinning).
    pub fn self_consistent(cell: Cell) -> Self {
        let expected = compute_canonical_state_commitment(&cell);
        CommitmentRecomputeVerifier { cell, expected }
    }
}

impl Gadget for CommitmentRecomputeVerifier {
    type Output = VerificationResult;

    fn fields(&self) -> Vec<GadgetField> {
        vec![GadgetField::HexBytes {
            key: "expected_commitment".into(),
            len: 32,
        }]
    }

    fn set(&mut self, field: &str, v: GadgetInput) {
        if field == "expected_commitment" {
            if let GadgetInput::Bytes(b) = v {
                if b.len() == 32 {
                    let mut a = [0u8; 32];
                    a.copy_from_slice(&b);
                    self.expected = a;
                }
            }
        }
    }

    fn validate(&self) -> GadgetValidation {
        GadgetValidation::Ok
    }

    fn build(&self) -> Result<VerificationResult, GadgetError> {
        let recomputed = compute_canonical_state_commitment(&self.cell);
        if recomputed == self.expected {
            Ok(VerificationResult::green(
                1,
                format!(
                    "recomputed commitment {} matches the pinned reference",
                    reflect::short_hex(&recomputed)
                ),
            ))
        } else {
            Ok(VerificationResult::red(
                1,
                format!(
                    "recomputed {} ≠ pinned {} — the cell's authority-bearing state was tampered",
                    reflect::short_hex(&recomputed),
                    reflect::short_hex(&self.expected)
                ),
            ))
        }
    }
}

// ===========================================================================
// §L9.3 — the NULLIFIER SET as a MerkleTree + non-membership verifier
// ===========================================================================

/// A thin newtype over a REAL [`NullifierSet`] (the append-only set of spent
/// nullifiers), surfaced as the moldable inspector's `MerkleTree` face + a
/// double-spend `Invariant`. The root is the genuine [`NullifierSet::root`]; the
/// non-membership verifier runs the genuine adjacent-neighbor fold. No parallel
/// set model.
#[derive(Clone, Debug)]
pub struct NullifierSetView {
    /// The live nullifier set (snapshot).
    pub set: NullifierSet,
}

impl NullifierSetView {
    /// Wrap a nullifier set for presentation.
    pub fn of(set: NullifierSet) -> Self {
        NullifierSetView { set }
    }

    /// The set's genuine Merkle root (the published commitment).
    pub fn root(&self) -> [u8; 32] {
        self.set.root()
    }
}

impl Presentable for NullifierSetView {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Nullifier
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let root = self.set.root();
        let mut leaves: Vec<String> = self.set.iter().map(|n| reflect::short_hex(&n.0)).collect();
        leaves.sort();
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: cardinality + root.
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Nullifier Set".to_string(),
            search_text: format!(
                "nullifier set {} root {}",
                self.set.len(),
                reflect::short_hex(&root)
            ),
            body: PresentationBody::Fields(Inspectable {
                kind: ObjectKind::Nullifier,
                title: format!("Nullifier Set · {}", reflect::short_hex(&root)),
                subtitle: format!(
                    "{} spent nullifier(s) (one-time authority consumed)",
                    self.set.len()
                ),
                fields: vec![
                    Field::count("cardinality", self.set.len() as u64),
                    Field::hash("root", root),
                    Field::boolean("empty", self.set.is_empty()),
                ],
            }),
        });

        // (2) MerkleTree — the genuine sorted nullifier tree (leaves + real root).
        out.push(Presentation {
            kind: PresentationKind::Graph,
            label: "Nullifier Tree".to_string(),
            search_text: format!("merkle nullifier tree {} leaves", leaves.len()),
            body: PresentationBody::MerkleTree(MerkleTreeView {
                label: format!("nullifier set ({} spent)", leaves.len()),
                leaves,
                root,
                // No single highlighted path — the set is the whole roster.
                path: Vec::new(),
            }),
        });

        // (3) Invariant — double-spend = membership; a fresh spend is a
        //     NON-membership the circuit's grow-gate enforces. The readout names
        //     the property the set protects.
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Double-Spend Protection".to_string(),
            search_text: "invariant double spend non-membership".to_string(),
            body: PresentationBody::Fields(Inspectable {
                kind: ObjectKind::Nullifier,
                title: "Double-Spend Invariant".to_string(),
                subtitle: "a nullifier appears AT MOST ONCE; re-spending is a membership the \
                           grow-gate refuses"
                    .to_string(),
                fields: vec![
                    Field::text(
                        "property",
                        "spend ⟺ insert a fresh nullifier (non-membership before, membership after)",
                    ),
                    Field::text(
                        "enforced_by",
                        "NullifierSet::insert (refuses a duplicate) + prove_non_membership",
                    ),
                    Field::count("spent", self.set.len() as u64),
                ],
            }),
        });

        out
    }
}

/// THE NON-MEMBERSHIP VERIFIER — a read-only [`Gadget`] that proves a candidate
/// nullifier is NOT in the set, then verifies the proof against the set's root
/// with the REAL [`NullifierSet::verify_non_membership`] (the genuine
/// adjacent-neighbor fold). Green ⟹ the candidate is a fresh, spendable
/// nullifier; red ⟹ it is already spent (a double-spend). No commit.
#[derive(Clone, Debug)]
pub struct NonMembershipVerifier {
    set: NullifierSet,
    candidate: Nullifier,
}

impl NonMembershipVerifier {
    /// A verifier over a set + the candidate nullifier to prove absent.
    pub fn new(set: NullifierSet, candidate: Nullifier) -> Self {
        NonMembershipVerifier { set, candidate }
    }
}

impl Gadget for NonMembershipVerifier {
    type Output = VerificationResult;

    fn fields(&self) -> Vec<GadgetField> {
        vec![GadgetField::HexBytes {
            key: "candidate_nullifier".into(),
            len: 32,
        }]
    }

    fn set(&mut self, field: &str, v: GadgetInput) {
        if field == "candidate_nullifier" {
            if let GadgetInput::Bytes(b) = v {
                if b.len() == 32 {
                    let mut a = [0u8; 32];
                    a.copy_from_slice(&b);
                    self.candidate = Nullifier(a);
                }
            }
        }
    }

    fn validate(&self) -> GadgetValidation {
        GadgetValidation::Ok
    }

    fn build(&self) -> Result<VerificationResult, GadgetError> {
        let root = self.set.root();
        // Already in the set ⟹ NOT a fresh spend (a double-spend); no proof exists.
        if self.set.contains(&self.candidate) {
            return Ok(VerificationResult::red(
                1,
                format!(
                    "nullifier {} is ALREADY in the set — a double-spend (no non-membership proof)",
                    reflect::short_hex(&self.candidate.0)
                ),
            ));
        }
        // Build + verify the genuine non-membership proof against the real root.
        match self.set.prove_non_membership(&self.candidate) {
            Some(proof) => {
                let ok = NullifierSet::verify_non_membership(&proof, &root);
                if ok {
                    Ok(VerificationResult::green(
                        1,
                        format!(
                            "nullifier {} verified ABSENT against root {} (a fresh, spendable spend)",
                            reflect::short_hex(&self.candidate.0),
                            reflect::short_hex(&root)
                        ),
                    ))
                } else {
                    Ok(VerificationResult::red(
                        1,
                        "the non-membership proof failed to verify against the set root"
                            .to_string(),
                    ))
                }
            }
            None => Ok(VerificationResult::red(
                1,
                "no non-membership proof could be produced for the candidate".to_string(),
            )),
        }
    }
}

// ===========================================================================
// §L9.4 — a NOTE COMMITMENT: creation Trace + hasher verifier
// ===========================================================================

/// A thin newtype over a REAL [`Note`], surfacing its Poseidon2 **note
/// commitment** (the value that IS the circuit-side felt) as a creation `Trace` +
/// a `MerkleTree` membership face. The commitment is the genuine [`Note::commitment`];
/// this view never invents a parallel hash.
#[derive(Clone, Debug)]
pub struct NoteCommitmentView {
    /// The note (snapshot).
    pub note: Note,
}

impl NoteCommitmentView {
    /// Wrap a note for presentation.
    pub fn of(note: Note) -> Self {
        NoteCommitmentView { note }
    }

    /// The note's genuine Poseidon2 commitment (the circuit-side felt, as bytes).
    pub fn commitment(&self) -> NoteCommitment {
        self.note.commitment()
    }
}

impl Presentable for NoteCommitmentView {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Nullifier
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let commit = self.note.commitment();
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the note's public face (owner,
        //     value, asset type) + its commitment.
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Note Commitment".to_string(),
            search_text: format!(
                "note commitment {} owner {}",
                reflect::short_hex(&commit.0),
                reflect::short_hex(&self.note.owner)
            ),
            body: PresentationBody::Fields(Inspectable {
                kind: ObjectKind::Nullifier,
                title: format!("Note Commitment · {}", reflect::short_hex(&commit.0)),
                subtitle: "the Poseidon2 commitment that IS the circuit-side felt".to_string(),
                fields: vec![
                    Field::id("owner", self.note.owner),
                    Field::count("value", self.note.value()),
                    Field::count("asset_type", self.note.asset_type()),
                    Field::boolean("fungible", self.note.is_fungible()),
                    Field::hash("commitment", commit.0),
                ],
            }),
        });

        // (2) Trace — the creation absorption: owner ‖ value ‖ asset_type ‖
        //     creation_nonce ‖ randomness, the 28-limb preimage the Poseidon2
        //     commitment folds (matching Note::poseidon2_commitment).
        let steps = vec![
            TraceStep {
                index: 0,
                label: "absorb owner (spending authority)".to_string(),
            },
            TraceStep {
                index: 1,
                label: format!("absorb value = {}", self.note.value()),
            },
            TraceStep {
                index: 2,
                label: format!("absorb asset_type = {}", self.note.asset_type()),
            },
            TraceStep {
                index: 3,
                label: "absorb creation_nonce (domain separation)".to_string(),
            },
            TraceStep {
                index: 4,
                label: "absorb randomness (blinding factor)".to_string(),
            },
            TraceStep {
                index: 5,
                label: format!("Poseidon2 → commitment {}", reflect::short_hex(&commit.0)),
            },
        ];
        out.push(Presentation {
            kind: PresentationKind::Source,
            label: "Commitment Creation".to_string(),
            search_text: "trace note commitment creation poseidon2".to_string(),
            body: PresentationBody::Trace(TraceView { steps }),
        });

        out
    }
}

/// THE NOTE-COMMITMENT HASHER — a read-only [`Gadget`] that recomputes a note's
/// Poseidon2 commitment with the REAL [`Note::commitment`] and compares it to a
/// pinned reference. Green ⟹ the note opens to the claimed commitment; red ⟹ it
/// does not. No commit; pure recompute.
#[derive(Clone, Debug)]
pub struct NoteCommitmentHasher {
    note: Note,
    expected: NoteCommitment,
}

impl NoteCommitmentHasher {
    /// A hasher over a note + the commitment it is CLAIMED to open to.
    pub fn new(note: Note, expected: NoteCommitment) -> Self {
        NoteCommitmentHasher { note, expected }
    }

    /// A hasher pinned to the note's OWN genuine commitment (self-consistent).
    pub fn self_consistent(note: Note) -> Self {
        let expected = note.commitment();
        NoteCommitmentHasher { note, expected }
    }
}

impl Gadget for NoteCommitmentHasher {
    type Output = VerificationResult;

    fn fields(&self) -> Vec<GadgetField> {
        vec![GadgetField::HexBytes {
            key: "expected_commitment".into(),
            len: 32,
        }]
    }

    fn set(&mut self, field: &str, v: GadgetInput) {
        if field == "expected_commitment" {
            if let GadgetInput::Bytes(b) = v {
                if b.len() == 32 {
                    let mut a = [0u8; 32];
                    a.copy_from_slice(&b);
                    self.expected = NoteCommitment(a);
                }
            }
        }
    }

    fn validate(&self) -> GadgetValidation {
        GadgetValidation::Ok
    }

    fn build(&self) -> Result<VerificationResult, GadgetError> {
        let recomputed = self.note.commitment();
        if recomputed == self.expected {
            Ok(VerificationResult::green(
                1,
                format!(
                    "note recomputes to {} — opens to the pinned commitment",
                    reflect::short_hex(&recomputed.0)
                ),
            ))
        } else {
            Ok(VerificationResult::red(
                1,
                format!(
                    "note recomputes to {} ≠ pinned {} — the note does not open to it",
                    reflect::short_hex(&recomputed.0),
                    reflect::short_hex(&self.expected.0)
                ),
            ))
        }
    }
}

// ===========================================================================
// §L9.5 — the DESCRIPTOR BOUNDARY (the honest unreachable surface)
// ===========================================================================

/// THE HONEST CIRCUIT-DESCRIPTOR BOUNDARY. The IR-v2 descriptor types the census
/// names for slice 11 — `EffectVmDescriptor2` / `TableDef2` / `VmConstraint2` /
/// `AirDescriptor` / `BatchProof` — live in the `dregg-circuit` crate, which is
/// NOT a direct dependency of `starbridge-v2` and is NOT re-exported through
/// `dregg-cell`/`dregg-turn`/`dregg-sdk` (those reference `dregg_circuit::*` only
/// inside private function signatures). So those objects are NOT reachable here.
///
/// Rather than fabricate a parallel descriptor model, this presents the IR-v2
/// descriptor *contract* — the on-disk JSON shape the prover/verifier already
/// read (`circuit/descriptors/*.json`: `name` · `ir` · `trace_width` ·
/// `public_input_count` · `tables[]` · `constraints[]` · `hash_sites[]` ·
/// `ranges[]`) — as a `Source` face, and names the dep route to reach the live
/// types. This is the same honesty `cap_inspector.rs` uses for the unreachable
/// cap-membership sibling path.
#[derive(Clone, Debug)]
pub struct DescriptorBoundary;

impl DescriptorBoundary {
    /// The dep route to reach the live IR-v2 descriptor types (the REPORTED
    /// wiring): add `dregg-circuit` as a direct dependency of `starbridge-v2`
    /// (it is already in the transitive graph via `dregg-turn`/`dregg-sdk`, and
    /// the workspace already replicates the plonky3-recursion `[patch]` it needs),
    /// then `use dregg_circuit::{descriptor_ir2::*, air_descriptor::AirDescriptor}`.
    pub const DEP_ROUTE: &'static str =
        "add `dregg-circuit` (path = \"../circuit\") as a direct dependency, gated on \
         `embedded-executor`; then `dregg_circuit::descriptor_ir2::EffectVmDescriptor2` / \
         `TableDef2` / `VmConstraint2` and `dregg_circuit::air_descriptor::AirDescriptor` / \
         `BatchProof` become nameable. They are already in the transitive graph (via \
         dregg-turn/dregg-sdk) and the plonky3-recursion [patch] is already replicated.";

    /// The IR-v2 descriptor on-disk contract fields (the artifact the prover +
    /// verifier read), in canonical JSON order.
    pub const IR2_FIELDS: &[(&'static str, &'static str)] = &[
        (
            "name",
            "the descriptor's stable name (the VK/fingerprint anchor)",
        ),
        ("ir", "the IR version (2 = the multi-table batch-STARK IR)"),
        ("trace_width", "the number of trace columns (the AIR width)"),
        ("public_input_count", "the number of public-input slots"),
        (
            "tables",
            "the TableDef2 lookup/memory tables (empty for a pure-gate AIR)",
        ),
        (
            "constraints",
            "the VmConstraint2 set: gate · pi_binding · boundary · window_gate · …",
        ),
        ("hash_sites", "the Poseidon2 hash-absorb sites"),
        ("ranges", "the range-check column constraints"),
    ];
}

impl Presentable for DescriptorBoundary {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Proof
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the IR-v2 descriptor contract shape.
        let fields: Vec<Field> = DescriptorBoundary::IR2_FIELDS
            .iter()
            .map(|(k, v)| Field::text(*k, *v))
            .collect();
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "IR-v2 Descriptor Shape".to_string(),
            search_text: "descriptor ir2 effectvm table air batch proof shape".to_string(),
            body: PresentationBody::Fields(Inspectable {
                kind: ObjectKind::Proof,
                title: "Circuit Descriptor (IR-v2)".to_string(),
                subtitle: "the multi-table batch-STARK descriptor contract \
                           (circuit/descriptors/*.json)"
                    .to_string(),
                fields,
            }),
        });

        // (2) Source — the HONEST boundary: the live types are not reachable, and
        //     the dep route to reach them. Never a faked descriptor object.
        out.push(Presentation {
            kind: PresentationKind::Source,
            label: "Reachability Boundary".to_string(),
            search_text: "boundary dregg-circuit not reachable dep route".to_string(),
            body: PresentationBody::Prose(format!(
                "The live IR-v2 descriptor types (EffectVmDescriptor2 / TableDef2 / VmConstraint2 \
                 / AirDescriptor / BatchProof) live in `dregg-circuit`, which is NOT a direct \
                 dependency of starbridge-v2 and is NOT re-exported by dregg-cell/dregg-turn/\
                 dregg-sdk. This view surfaces the descriptor's on-disk CONTRACT shape, not the \
                 live objects.\n\nDEP ROUTE: {}",
                DescriptorBoundary::DEP_ROUTE
            )),
        });

        out
    }
}

// ===========================================================================
// TESTS — the model, proven gpui-free (exactly as proofs.rs's tests are).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{transfer, World};

    /// A world with one committed transfer (verified-by-construction).
    fn proven_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let a = w.genesis_cell(1, 10_000);
        let b = w.genesis_cell(2, 0);
        let t = w.turn(a, vec![transfer(a, b, 250)]);
        assert!(w.commit_turn(t).is_committed());
        (w, a, b)
    }

    // ── the PROOF family ────────────────────────────────────────────────────

    #[test]
    fn a_proven_turn_offers_the_tier_and_binding_presentations() {
        let (w, _a, _b) = proven_world();
        let turns = ProvenTurn::all(&w);
        assert_eq!(turns.len(), 1, "one committed turn");
        let ctx = PresentCtx::new(&w, _a);
        let set = turns[0].present(&ctx);

        // The RawFields floor is the genuine reflect_proof_status surface.
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));

        // The DomainVisual tier lattice marks THIS turn's real tier (tier 1 in the
        // embedded single-custody world).
        let dv = set
            .iter()
            .find(|p| p.kind == PresentationKind::DomainVisual)
            .unwrap();
        match &dv.body {
            PresentationBody::Lattice(l) => {
                assert_eq!(l.nodes.len(), 3, "the three honest tiers");
                assert_eq!(
                    l.current,
                    Some(0),
                    "embedded turn is verified-by-construction"
                );
            }
            other => panic!("tier should be a Lattice, got {other:?}"),
        }

        // The Invariant names what tier-1 binds (the operator's re-execution).
        let iv = set
            .iter()
            .find(|p| p.kind == PresentationKind::Invariant)
            .unwrap();
        match &iv.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "binds"));
                assert!(i.fields.iter().any(|f| f.key == "upgrade_route"));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn the_proof_provenance_carries_the_pre_post_commitment_chain() {
        let (w, _a, _b) = proven_world();
        let turns = ProvenTurn::all(&w);
        let ctx = PresentCtx::new(&w, _a);
        let set = turns[0].present(&ctx);
        let prov = set
            .iter()
            .find(|p| p.kind == PresentationKind::Provenance)
            .unwrap();
        match &prov.body {
            PresentationBody::Timeline(t) => {
                assert_eq!(t.events.len(), 2, "pre → post commitment");
                assert!(t.events[1].label.contains("post-state"));
            }
            _ => unreachable!(),
        }
    }

    // ── the 8-FELT STATE COMMITMENT ─────────────────────────────────────────

    #[test]
    fn the_state_commitment_binding_lists_what_the_commitment_binds() {
        let (w, a, _b) = proven_world();
        let binding = StateCommitmentBinding::from_world(&w, a).expect("the cell exists");
        let ctx = PresentCtx::new(&w, a);
        let set = binding.present(&ctx);

        // RawFields floor carries the genuine canonical commitment.
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .unwrap();
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "commitment"));
            }
            _ => unreachable!(),
        }

        // The Invariant enumerates the anti-omission components (≥10, incl.
        // permissions + VK + cap_root + lifecycle — the soundness-critical ones).
        let iv = set
            .iter()
            .find(|p| p.kind == PresentationKind::Invariant)
            .unwrap();
        match &iv.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.len() >= 10);
                assert!(i.fields.iter().any(|f| f.key == "permissions"));
                assert!(i.fields.iter().any(|f| f.key == "verification_key"));
                assert!(i.fields.iter().any(|f| f.key == "capability_root"));
                assert!(i.fields.iter().any(|f| f.key == "lifecycle"));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn the_commitment_recompute_verifier_is_the_anti_ghost_tooth() {
        let (w, a, _b) = proven_world();
        let cell = w.ledger().get(&a).unwrap().clone();

        // A self-consistent verifier is GREEN (the cell opens to its own commitment).
        let v = CommitmentRecomputeVerifier::self_consistent(cell.clone());
        let r = v.build().unwrap();
        assert!(
            r.ok,
            "a genuine cell recomputes to its own commitment: {:?}",
            r.notes
        );

        // TAMPER: pin a DIFFERENT expected commitment → the recompute diverges →
        // the verifier flags it (the anti-ghost tooth, in-band).
        let bad = CommitmentRecomputeVerifier::new(cell, [0xAB; 32]);
        let br = bad.build().unwrap();
        assert!(!br.ok, "a mismatched commitment is flagged red");
        assert!(br.notes[0].contains("tampered"));
    }

    #[test]
    fn a_mutated_cell_recomputes_to_a_different_commitment() {
        // The anti-omission property end-to-end: change an authority-bearing
        // component (the balance) and the canonical commitment changes.
        let (w, a, _b) = proven_world();
        let cell = w.ledger().get(&a).unwrap().clone();
        let c0 = compute_canonical_state_commitment(&cell);

        let mut mutated = cell.clone();
        mutated.state.set_balance(mutated.state.balance() + 1);
        let c1 = compute_canonical_state_commitment(&mutated);
        assert_ne!(c0, c1, "a balance change moves the commitment");

        // The verifier pinned to the ORIGINAL commitment flags the mutated cell.
        let v = CommitmentRecomputeVerifier::new(mutated, c0);
        assert!(!v.build().unwrap().ok);
    }

    // ── the NULLIFIER SET ───────────────────────────────────────────────────

    fn nset_with(nullifiers: &[[u8; 32]]) -> NullifierSet {
        let mut s = NullifierSet::new();
        for n in nullifiers {
            s.insert(Nullifier(*n)).unwrap();
        }
        s
    }

    #[test]
    fn the_nullifier_set_view_carries_the_real_root_and_leaves() {
        let set = nset_with(&[[1u8; 32], [2u8; 32], [3u8; 32]]);
        let view = NullifierSetView::of(set.clone());
        let ctx_world = World::new();
        let ctx = PresentCtx::new(&ctx_world, CellId::derive_raw(&[0u8; 32], &[0u8; 32]));
        let presented = view.present(&ctx);

        let mt = presented
            .iter()
            .find_map(|p| match &p.body {
                PresentationBody::MerkleTree(m) => Some(m),
                _ => None,
            })
            .expect("a MerkleTree face");
        assert_eq!(
            mt.root,
            set.root(),
            "the view carries the genuine NullifierSet root"
        );
        assert_eq!(mt.leaves.len(), 3);
    }

    #[test]
    fn the_non_membership_verifier_runs_the_real_fold() {
        let set = nset_with(&[[10u8; 32], [20u8; 32], [30u8; 32]]);

        // An ABSENT nullifier verifies GREEN against the real root (a fresh spend).
        let absent = Nullifier([15u8; 32]);
        let v = NonMembershipVerifier::new(set.clone(), absent);
        let r = v.build().unwrap();
        assert!(
            r.ok,
            "an absent nullifier proves non-membership: {:?}",
            r.notes
        );

        // A PRESENT nullifier is flagged RED (a double-spend — no proof exists).
        let present = Nullifier([20u8; 32]);
        let v2 = NonMembershipVerifier::new(set, present);
        let r2 = v2.build().unwrap();
        assert!(!r2.ok, "a present nullifier is a double-spend");
        assert!(r2.notes[0].contains("double-spend"));
    }

    // ── a NOTE COMMITMENT ───────────────────────────────────────────────────

    fn a_note() -> Note {
        Note::with_randomness([0x07u8; 32], [100, 0, 0, 0, 0, 0, 0, 0], [0x09u8; 32])
    }

    #[test]
    fn the_note_commitment_view_traces_the_real_creation() {
        let note = a_note();
        let view = NoteCommitmentView::of(note.clone());
        let ctx_world = World::new();
        let ctx = PresentCtx::new(&ctx_world, CellId::derive_raw(&[0u8; 32], &[0u8; 32]));
        let set = view.present(&ctx);

        // The RawFields floor carries the genuine note commitment.
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .unwrap();
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "commitment"));
                assert!(i.fields.iter().any(|f| f.key == "value"));
            }
            _ => unreachable!(),
        }
        // The Trace ends at the genuine Poseidon2 commitment.
        let trace = set
            .iter()
            .find_map(|p| match &p.body {
                PresentationBody::Trace(t) => Some(t),
                _ => None,
            })
            .unwrap();
        assert!(trace.steps.last().unwrap().label.contains("commitment"));
    }

    #[test]
    fn the_note_commitment_hasher_recomputes_and_compares() {
        let note = a_note();

        // Self-consistent ⟹ GREEN.
        let v = NoteCommitmentHasher::self_consistent(note.clone());
        assert!(v.build().unwrap().ok, "a note opens to its own commitment");

        // A wrong pinned commitment ⟹ RED.
        let bad = NoteCommitmentHasher::new(note, NoteCommitment([0u8; 32]));
        assert!(!bad.build().unwrap().ok);
    }

    // ── the DESCRIPTOR BOUNDARY (the honest unreachable surface) ─────────────

    #[test]
    fn the_descriptor_boundary_is_honest_about_reachability() {
        let w = World::new();
        let ctx = PresentCtx::new(&w, CellId::derive_raw(&[0u8; 32], &[0u8; 32]));
        let set = DescriptorBoundary.present(&ctx);

        // RawFields surfaces the IR-v2 contract shape.
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .unwrap();
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "constraints"));
                assert!(i.fields.iter().any(|f| f.key == "trace_width"));
            }
            _ => unreachable!(),
        }
        // The Source face names the dep route honestly (no faked descriptor).
        let src = set
            .iter()
            .find(|p| p.kind == PresentationKind::Source)
            .unwrap();
        match &src.body {
            PresentationBody::Prose(p) => {
                assert!(p.contains("NOT a direct dependency"));
                assert!(p.contains("dregg-circuit"));
            }
            _ => unreachable!(),
        }
    }

    // ── the universal-coverage floor holds for every L9 Presentable ──────────

    #[test]
    fn every_l9_presentable_has_the_raw_fields_floor() {
        use crate::presentable::PresentableExt;
        let (w, a, _b) = proven_world();
        let ctx = PresentCtx::new(&w, a);

        let turns = ProvenTurn::all(&w);
        assert!(turns[0].has_raw_fields_floor(&ctx));

        let binding = StateCommitmentBinding::from_world(&w, a).unwrap();
        assert!(binding.has_raw_fields_floor(&ctx));

        let nset = NullifierSetView::of(nset_with(&[[1u8; 32]]));
        assert!(nset.has_raw_fields_floor(&ctx));

        let note = NoteCommitmentView::of(a_note());
        assert!(note.has_raw_fields_floor(&ctx));

        assert!(DescriptorBoundary.has_raw_fields_floor(&ctx));
    }
}
