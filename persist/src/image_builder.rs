//! The EROS image-builder: build-time IMAGE GENESIS.
//!
//! "Here's my OS + a proof of what it can't do."
//!
//! This is the build-time half of the genesis reframe (the runtime half is
//! turns). It takes a declarative [`ImageManifest`] — a set of EROS object
//! factories ([`FactoryDescriptor`]s) plus the cells to create from them — and
//! assembles a verified initial cell-graph into a SEALED, ATTESTABLE image:
//! a [`Snapshot`] (the sealed-state carrier, with its root-binding fail-closed
//! tooth) wrapped in an [`ImageArtifact`] that carries an [`ImageAttestation`].
//!
//! # What the attestation attests (and what it does NOT)
//!
//! The attestation is HONEST about its reach. It attests, and a recipient can
//! verify WITHOUT trusting the builder:
//!
//! - **Factory provenance.** Every cell was built from one of a fixed set of
//!   content-addressed [`FactoryDescriptor`]s (BLAKE3 `descriptor_hash`). The
//!   descriptor IS the constructor transparency: it pins the child program-VK
//!   strategy, the cap templates, the field constraints, and the **perpetual
//!   `state_constraints` baked onto every child cell's `CellProgram` for life**.
//!   The attestation records the sorted set of factory hashes; the verifier
//!   recomputes them. "This OS was built from these verified constructors."
//!
//! - **Conservation.** `BALANCE_SUM == 0` across the image (issuer wells carry
//!   −supply). The verifier recomputes the sum from the reconstructed ledger.
//!   "This OS conserves value."
//!
//! - **Root binding.** The `claimed_root` is the canonical `Ledger::root()` of
//!   the reconstructed cell-graph (`Snapshot`'s anti-substitution tooth). The
//!   verifier rebuilds `checkpoint ⊕ overlay` and refuses any mismatch.
//!   "This OS has exactly this state."
//!
//! - **Program-for-life binding.** Each created cell carries
//!   `CellProgram::Predicate(factory.state_constraints)` — the lifetime
//!   invariants its factory bakes in. The verifier re-derives each cell's
//!   program from its claimed factory and refuses a cell whose program does not
//!   match its factory's declared constraints. THIS is "what it can't do",
//!   made checkable: the recipient reads the factory descriptors to see what
//!   caps/programs the cells can EVER exercise.
//!
//! It does NOT yet attest (named seams, not silent gaps):
//!
//! - **The full Hatchery single-step invariant proofs (`hpres`).** The image
//!   carries the factory descriptors (the *declared* invariants) but not yet
//!   the `livingCellA_carries` proof object that an invariant HOLDS for one
//!   step → holds forever. The seam is marked at [`ImageAttestation`]:
//!   `hatchery_invariant_proof` is the slot where the `hpres` proof attaches.
//!
//! - **A cryptographic seal/signature.** The artifact is content-addressed and
//!   self-verifying (re-derive everything, fail-closed) but is not yet SIGNED
//!   by a builder key. The `seal` slot is reserved for that.
//!
//! - **The seL4 boot-wire.** Generating the `deos-image` `image_data.rs` const
//!   from a manifest via this builder (replacing the hand-built 6-cell const in
//!   `cell/examples/gen_image_snapshot.rs`) is a follow-up: the viewer PD is
//!   `#![no_std]` and cannot link this crate, so the wire is a codegen step,
//!   not a link. See [`crate::image_builder::tests`] for a manifest that
//!   reproduces the conservation shape that const ships.

use serde::{Deserialize, Serialize};

use dregg_cell::Ledger;
use dregg_cell::cell::{Cell, CellConfig};
use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor, FactoryError};
use dregg_cell::id::CellId;
use dregg_cell::program::CellProgram;

use crate::snapshot::{Snapshot, SnapshotHead, snapshot_ledger_root};

/// One cell to create in an image, naming the factory that constructs it.
///
/// The factory is referenced by its content-addressed `descriptor_hash`, so the
/// manifest is bound to the EXACT constructor (a different descriptor produces a
/// different hash and the build refuses it). `params` are the
/// [`FactoryCreationParams`] the factory validates (program-VK strategy, initial
/// fields, caps, owner pubkey); `balance` is the cell's signed initial balance
/// (negative only for issuer wells — the conservation shadow).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellSpec {
    /// The content-addressed hash of the [`FactoryDescriptor`] that constructs
    /// this cell (must be present in [`ImageManifest::factories`]).
    pub factory_hash: [u8; 32],
    /// The creation parameters the factory validates.
    pub params: FactoryCreationParams,
    /// The signed initial balance of the created cell. Issuer wells carry a
    /// negative balance so the closed image conserves to `BALANCE_SUM == 0`.
    pub balance: i64,
}

/// A declarative spec of an initial image — "what's in my ISO".
///
/// The full constructor set (the EROS factories, each carrying its
/// program-for-life) plus the cells to create from them. Serializable
/// (postcard/serde), matching the snapshot machinery.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct ImageManifest {
    /// A human label for the image (free-form, part of the manifest hash).
    pub name: String,
    /// The EROS object factories this image's cells are born from. Each is
    /// content-addressed by [`FactoryDescriptor::hash`]; a [`CellSpec`] names
    /// one by that hash.
    pub factories: Vec<FactoryDescriptor>,
    /// The cells to create, in order.
    pub cells: Vec<CellSpec>,
}

impl ImageManifest {
    /// The content-addressed hash of this manifest (binds name + every factory
    /// descriptor + every cell spec). A recipient recomputes it from the
    /// artifact's manifest and checks it against the attestation's
    /// `manifest_hash`.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-image-manifest-v1");
        hasher.update(&(self.name.len() as u64).to_le_bytes());
        hasher.update(self.name.as_bytes());
        hasher.update(&(self.factories.len() as u64).to_le_bytes());
        for f in &self.factories {
            hasher.update(&f.hash());
        }
        // Cell specs: postcard is deterministic for these serde-derived types.
        let cells_encoded = postcard::to_allocvec(&self.cells).unwrap_or_default();
        hasher.update(&(cells_encoded.len() as u64).to_le_bytes());
        hasher.update(&cells_encoded);
        *hasher.finalize().as_bytes()
    }

    /// Find a factory by its content-addressed hash.
    pub fn factory_by_hash(&self, hash: &[u8; 32]) -> Option<&FactoryDescriptor> {
        self.factories.iter().find(|f| &f.hash() == hash)
    }
}

/// The provenance of one created cell, recorded in the attestation.
///
/// Lets a recipient verify, per cell, WHICH verified factory it came from and
/// WHICH program-for-life it therefore carries — without trusting the builder.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellProvenance {
    /// The created cell's content-addressed id.
    pub cell_id: [u8; 32],
    /// The factory descriptor hash this cell was born from.
    pub factory_hash: [u8; 32],
    /// The cell's signed balance (so the conservation tally is auditable
    /// per-cell, not only in aggregate).
    pub balance: i64,
}

/// The attestation an image carries: "this image was built from these verified
/// factories, conserves value, has this root."
///
/// Every field here is RE-DERIVABLE by [`verify_image`] from the artifact's
/// manifest + snapshot, so a recipient verifies without trusting the builder.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImageAttestation {
    /// The manifest hash ([`ImageManifest::hash`]) — binds the artifact to the
    /// exact declarative spec it was built from.
    pub manifest_hash: [u8; 32],
    /// The canonical ledger root of the built cell-graph (== the snapshot's
    /// `claimed_root`). The recipient rebuilds the graph and refuses a mismatch.
    pub claimed_root: [u8; 32],
    /// The SORTED set of factory descriptor hashes the image's cells were born
    /// from (constructor provenance). Sorted so it is order-independent.
    pub factory_hashes: Vec<[u8; 32]>,
    /// `Σ balance` across the image. The conservation invariant requires this
    /// to be `0` (issuer wells carry −supply).
    pub balance_sum: i64,
    /// Per-cell provenance: which factory each cell came from + its balance.
    pub cells: Vec<CellProvenance>,
    /// SEAM (Hatchery): the `hpres` single-step invariant proof object that
    /// would let the image attest its invariants HOLD (not merely are
    /// declared). `None` today; this is where `livingCellA_carries` attaches.
    #[serde(default)]
    pub hatchery_invariant_proof: Option<Vec<u8>>,
    /// SEAM (seal): a builder-key signature over `manifest_hash || claimed_root`.
    /// `None` today; the artifact is self-verifying but not yet builder-signed.
    #[serde(default)]
    pub seal: Option<Vec<u8>>,
}

/// A sealed, attestable image: the snapshot (sealed-state carrier), the manifest
/// it was built from, and the attestation.
///
/// This is the thing you hand someone: "here's my OS + a proof of what it can't
/// do." [`verify_image`] checks it fail-closed without trusting the builder.
///
/// (No `PartialEq`/`Eq`: the carried [`Snapshot`] does not derive them. Compare
/// images by their [`ImageAttestation`] — which IS `Eq` and binds the root,
/// manifest, and per-cell provenance — and re-verify the snapshot.)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ImageArtifact {
    /// The declarative spec the image was built from.
    pub manifest: ImageManifest,
    /// The sealed-state carrier: a genesis-based [`Snapshot`] whose overlay is
    /// the built cell-graph and whose `claimed_root` binds it.
    pub snapshot: Snapshot,
    /// The attestation (all fields re-derivable; the verify path re-derives).
    pub attestation: ImageAttestation,
}

impl ImageArtifact {
    /// Serialize the artifact to deterministic postcard bytes (the shippable
    /// ISO payload).
    pub fn to_bytes(&self) -> Result<Vec<u8>, BuildError> {
        postcard::to_allocvec(self).map_err(|e| BuildError::Serialize(e.to_string()))
    }

    /// Deserialize an artifact from its postcard bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, BuildError> {
        postcard::from_bytes(bytes).map_err(|e| BuildError::Serialize(e.to_string()))
    }
}

/// Errors from building an image.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BuildError {
    /// A cell spec names a factory hash not present in the manifest.
    UnknownFactory { factory_hash: [u8; 32] },
    /// A cell spec's creation params violate its factory's descriptor.
    Factory(FactoryError),
    /// Two cell specs derive the same `CellId` (a collision the ledger's strict
    /// insert would silently drop — refused build-side so the image's cell
    /// count is honest).
    DuplicateCell { cell_id: [u8; 32] },
    /// Postcard (de)serialization failure.
    Serialize(String),
}

impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BuildError::UnknownFactory { factory_hash } => write!(
                f,
                "cell spec names unknown factory {:02x}{:02x}...",
                factory_hash[0], factory_hash[1]
            ),
            BuildError::Factory(e) => write!(f, "factory validation failed: {e}"),
            BuildError::DuplicateCell { cell_id } => write!(
                f,
                "two cell specs derive the same CellId {:02x}{:02x}...",
                cell_id[0], cell_id[1]
            ),
            BuildError::Serialize(s) => write!(f, "serialization: {s}"),
        }
    }
}

impl std::error::Error for BuildError {}

impl From<FactoryError> for BuildError {
    fn from(e: FactoryError) -> Self {
        BuildError::Factory(e)
    }
}

/// The `CellId` a spec will produce: content-addressed from `(owner_pubkey,
/// token)`. The token here is the cell's "kind" — we derive it from the
/// factory hash so two cells from the same factory + owner are distinct only
/// by owner, and the id is reproducible by a verifier holding the same spec.
fn spec_cell_id(spec: &CellSpec) -> CellId {
    // token := factory_hash (the cell's constructor identity). owner := the
    // creation params' owner pubkey. Both are in the manifest, so a verifier
    // re-derives the same id.
    CellId::derive_raw(&spec.params.owner_pubkey, &spec.factory_hash)
}

/// Construct a genuine factory-born cell from a validated spec + its factory.
///
/// The cell carries `CellProgram::Predicate(factory.state_constraints)` — the
/// factory's program-for-life — and the caps the params request (already
/// validated against the factory's templates by [`FactoryDescriptor::validate_creation`]).
fn build_cell(spec: &CellSpec, factory: &FactoryDescriptor) -> Cell {
    let mode = factory.default_mode.clone();
    // The perpetual program: the factory's slot caveats, baked on for life.
    let program = if factory.state_constraints.is_empty() {
        CellProgram::None
    } else {
        CellProgram::Predicate(factory.state_constraints.clone())
    };
    let token = spec.factory_hash; // constructor identity as the cell's token
    let config = CellConfig {
        mode,
        balance: spec.balance,
        permissions: None,
        program: Some(program),
        verification_key: None,
    };

    let mut cell = Cell::from_config(spec.params.owner_pubkey, token, config);

    // Install the requested capabilities (validated within the factory's
    // templates). Targets: SelfCell → the cell's own id; Specific(id) → that id.
    // `Any` cannot be granted to a concrete target, so it is skipped (the
    // template permitted it; an image grants only concrete caps).
    for cap in &spec.params.initial_caps {
        use dregg_cell::factory::CapTarget;
        let target = match &cap.target {
            CapTarget::SelfCell => cell.id(),
            CapTarget::Specific(id) => *id,
            CapTarget::Any => continue,
        };
        let _ = cell.capabilities.grant(target, cap.max_permissions.clone());
    }

    // Install the initial fields the params declare (already constraint-checked).
    for (idx, val) in &spec.params.initial_fields {
        let mut fe = [0u8; 32];
        fe[24..32].copy_from_slice(&val.to_be_bytes());
        cell.state.set_field(*idx as usize, fe);
    }

    cell
}

/// Build a sealed, attestable [`ImageArtifact`] from a manifest.
///
/// Pipeline (each step reuses the real substrate):
/// 1. For each [`CellSpec`], resolve its factory by content-addressed hash,
///    then `factory.validate_creation(params)` — REAL EROS validation
///    (program-VK strategy, cap templates, field constraints).
/// 2. Construct the genuine factory-born cell (program-for-life installed) and
///    `insert_cell` into a real [`Ledger`]; refuse a duplicate id.
/// 3. Compute the canonical `Ledger::root()` (the `claimed_root` binding).
/// 4. Package a genesis-based [`Snapshot`] (no checkpoint, overlay = the graph)
///    — the sealed-state carrier with its anti-substitution tooth.
/// 5. Emit the [`ImageAttestation`]: manifest hash, sorted factory hashes,
///    `BALANCE_SUM`, per-cell provenance, the root.
///
/// This does NOT touch a `PersistentStore` — image GENESIS is an offline,
/// in-memory assembly. The artifact's snapshot installs into a store later via
/// the existing [`crate::PersistentStore::install_snapshot`] path if a node
/// wants to BOOT the image.
pub fn build_image(manifest: &ImageManifest) -> Result<ImageArtifact, BuildError> {
    let mut ledger = Ledger::new();
    let mut overlay: Vec<Cell> = Vec::with_capacity(manifest.cells.len());
    let mut provenance: Vec<CellProvenance> = Vec::with_capacity(manifest.cells.len());
    let mut seen_ids = std::collections::BTreeSet::new();

    for spec in &manifest.cells {
        let factory =
            manifest
                .factory_by_hash(&spec.factory_hash)
                .ok_or(BuildError::UnknownFactory {
                    factory_hash: spec.factory_hash,
                })?;

        // REAL EROS validation: the params must satisfy the factory descriptor.
        factory.validate_creation(&spec.params)?;

        let cell = build_cell(spec, factory);
        let id = cell.id();
        debug_assert_eq!(id, spec_cell_id(spec));
        if !seen_ids.insert(*id.as_bytes()) {
            return Err(BuildError::DuplicateCell {
                cell_id: *id.as_bytes(),
            });
        }

        provenance.push(CellProvenance {
            cell_id: *id.as_bytes(),
            factory_hash: spec.factory_hash,
            balance: spec.balance,
        });

        // Insert into the real ledger (strict insert; duplicate ids already
        // refused above) and keep a copy for the snapshot overlay.
        let _ = ledger.insert_cell(cell.clone());
        overlay.push(cell);
    }

    let claimed_root = snapshot_ledger_root(&mut ledger);

    // The sealed-state carrier: a genesis-based snapshot (no checkpoint; the
    // overlay IS the whole built graph). Reuses the same fail-closed root tooth
    // a node uses for crash-recovery bootstrap.
    let snapshot = Snapshot {
        checkpoint: None,
        overlay_base_height: 0,
        overlay,
        head: SnapshotHead {
            commit_cursor: 0,
            block_executed_up_to: 0,
        },
        claimed_root,
    };

    // Sorted factory provenance (order-independent).
    let mut factory_hashes: Vec<[u8; 32]> = manifest
        .cells
        .iter()
        .map(|s| s.factory_hash)
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    factory_hashes.sort_unstable();

    let balance_sum: i64 = provenance.iter().map(|p| p.balance).sum();

    let attestation = ImageAttestation {
        manifest_hash: manifest.hash(),
        claimed_root,
        factory_hashes,
        balance_sum,
        cells: provenance,
        hatchery_invariant_proof: None,
        seal: None,
    };

    Ok(ImageArtifact {
        manifest: manifest.clone(),
        snapshot,
        attestation,
    })
}

/// The verdict of verifying an image: what it IS + what it CAN'T DO.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImageFacts {
    /// The verified canonical root of the image's cell-graph.
    pub root: [u8; 32],
    /// The verified `Σ balance` (== 0 for a conserving image).
    pub balance_sum: i64,
    /// The verified set of factory descriptor hashes the cells were born from.
    pub factory_hashes: Vec<[u8; 32]>,
    /// The number of cells in the image.
    pub cell_count: usize,
}

/// Why an image failed verification (fail-closed; any mismatch is fatal).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The recomputed manifest hash disagrees with the attestation.
    ManifestHashMismatch {
        claimed: [u8; 32],
        computed: [u8; 32],
    },
    /// The snapshot's `claimed_root` disagrees with the attestation's.
    RootBindingMismatch {
        snapshot_root: [u8; 32],
        attested_root: [u8; 32],
    },
    /// Rebuilding the cell-graph yields a root that does not match the
    /// `claimed_root` (the snapshot anti-substitution tooth tripped).
    RootReconstructMismatch {
        rebuilt: [u8; 32],
        claimed: [u8; 32],
    },
    /// `Σ balance ≠ 0` — the image does not conserve value.
    ConservationViolated { balance_sum: i64 },
    /// The attestation's recomputed balance sum disagrees with its cells.
    BalanceSumMismatch { attested: i64, computed: i64 },
    /// The recomputed sorted factory-hash set disagrees with the attestation.
    FactoryHashesMismatch,
    /// A cell's claimed factory hash is not present in the manifest.
    UnknownFactory { factory_hash: [u8; 32] },
    /// A cell in the snapshot was not constructed by the factory it claims
    /// (its program-for-life does not match the factory's declared
    /// `state_constraints`, or its id does not match the spec).
    CellNotFromFactory { cell_id: [u8; 32] },
    /// The attestation's per-cell provenance disagrees with the manifest/graph.
    ProvenanceMismatch,
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for VerifyError {}

/// Verify an image artifact WITHOUT trusting the builder, fail-closed.
///
/// Re-derives every attested fact from the artifact's manifest + snapshot and
/// refuses any mismatch:
///
/// 1. **Manifest binding.** Recompute [`ImageManifest::hash`]; must equal the
///    attestation's `manifest_hash`.
/// 2. **Root binding.** The snapshot's `claimed_root` must equal the
///    attestation's `claimed_root`, AND rebuilding `checkpoint ⊕ overlay` must
///    reproduce that root (the snapshot anti-substitution tooth).
/// 3. **Conservation.** `Σ balance` (recomputed from the rebuilt ledger) must
///    be `0`, and must match the attestation's `balance_sum`.
/// 4. **Factory provenance.** The sorted factory-hash set is recomputed from
///    the per-cell provenance and must match the attestation; every cell's
///    claimed factory must be in the manifest.
/// 5. **Program-for-life binding.** Each cell in the rebuilt ledger must carry
///    EXACTLY the `CellProgram` its claimed factory bakes in
///    (`Predicate(state_constraints)` or `None`), and its id must match the
///    spec — so a cell cannot claim a factory it was not born from.
///
/// On success returns [`ImageFacts`]: the verified root, conservation sum,
/// factory set, and cell count — "what this OS is + can't do."
pub fn verify_image(artifact: &ImageArtifact) -> Result<ImageFacts, VerifyError> {
    let att = &artifact.attestation;
    let manifest = &artifact.manifest;

    // 1. Manifest binding.
    let computed_manifest_hash = manifest.hash();
    if computed_manifest_hash != att.manifest_hash {
        return Err(VerifyError::ManifestHashMismatch {
            claimed: att.manifest_hash,
            computed: computed_manifest_hash,
        });
    }

    // 2a. The snapshot's claimed_root must equal the attestation's.
    if artifact.snapshot.claimed_root != att.claimed_root {
        return Err(VerifyError::RootBindingMismatch {
            snapshot_root: artifact.snapshot.claimed_root,
            attested_root: att.claimed_root,
        });
    }

    // 2b. Rebuild the cell-graph from the snapshot and re-derive the root
    // (the snapshot anti-substitution tooth, done in-crate without a store).
    let mut ledger = match &artifact.snapshot.checkpoint {
        Some(cp) => crate::ledger_store::checkpoint_to_ledger_snapshot(cp),
        None => Ledger::new(),
    };
    for cell in &artifact.snapshot.overlay {
        let _ = ledger.remove(&cell.id());
        let _ = ledger.insert_cell(cell.clone());
    }
    let rebuilt_root = snapshot_ledger_root(&mut ledger);
    if rebuilt_root != att.claimed_root {
        return Err(VerifyError::RootReconstructMismatch {
            rebuilt: rebuilt_root,
            claimed: att.claimed_root,
        });
    }

    // 3. Conservation: Σ balance over the REBUILT ledger (the source of truth),
    // and it must agree with the attestation's tally.
    let computed_sum: i64 = ledger.iter().map(|(_, c)| c.state.balance()).sum();
    let attested_cells_sum: i64 = att.cells.iter().map(|p| p.balance).sum();
    if attested_cells_sum != att.balance_sum {
        return Err(VerifyError::BalanceSumMismatch {
            attested: att.balance_sum,
            computed: attested_cells_sum,
        });
    }
    if computed_sum != att.balance_sum {
        return Err(VerifyError::BalanceSumMismatch {
            attested: att.balance_sum,
            computed: computed_sum,
        });
    }
    if computed_sum != 0 {
        return Err(VerifyError::ConservationViolated {
            balance_sum: computed_sum,
        });
    }

    // 4. Factory provenance: the sorted hash set recomputed from per-cell
    // provenance must match the attestation, and every claimed factory must be
    // present in the manifest.
    let mut recomputed_set: Vec<[u8; 32]> = att
        .cells
        .iter()
        .map(|p| p.factory_hash)
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    recomputed_set.sort_unstable();
    if recomputed_set != att.factory_hashes {
        return Err(VerifyError::FactoryHashesMismatch);
    }
    for p in &att.cells {
        if manifest.factory_by_hash(&p.factory_hash).is_none() {
            return Err(VerifyError::UnknownFactory {
                factory_hash: p.factory_hash,
            });
        }
    }

    // 5. Program-for-life binding. The attestation's per-cell provenance must
    // cover exactly the rebuilt ledger, and each cell must carry the program
    // its claimed factory bakes in (and the id a spec for it would derive).
    if att.cells.len() != ledger.iter().count() {
        return Err(VerifyError::ProvenanceMismatch);
    }
    for p in &att.cells {
        let id = CellId::from_bytes(p.cell_id);
        let cell = match ledger.get(&id) {
            Some(c) => c,
            None => return Err(VerifyError::ProvenanceMismatch),
        };
        // The cell's balance must match its claimed provenance.
        if cell.state.balance() != p.balance {
            return Err(VerifyError::ProvenanceMismatch);
        }
        // Recompute the program the claimed factory bakes in, and require the
        // cell to carry EXACTLY it.
        let factory =
            manifest
                .factory_by_hash(&p.factory_hash)
                .ok_or(VerifyError::UnknownFactory {
                    factory_hash: p.factory_hash,
                })?;
        let expected_program = if factory.state_constraints.is_empty() {
            CellProgram::None
        } else {
            CellProgram::Predicate(factory.state_constraints.clone())
        };
        if cell.program != expected_program {
            return Err(VerifyError::CellNotFromFactory { cell_id: p.cell_id });
        }
        // The cell's content-addressed id must be the one a spec from this
        // factory + owner derives (token == factory_hash), so a cell cannot be
        // smuggled in under a factory it was not constructed by.
        let expected_id = CellId::derive_raw(cell.public_key(), &p.factory_hash);
        if expected_id != id {
            return Err(VerifyError::CellNotFromFactory { cell_id: p.cell_id });
        }
    }

    Ok(ImageFacts {
        root: att.claimed_root,
        balance_sum: computed_sum,
        factory_hashes: att.factory_hashes.clone(),
        cell_count: att.cells.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::cell::CellMode;
    use dregg_cell::factory::{CapTarget, CapTemplate, FieldConstraint};
    use dregg_cell::permissions::AuthRequired;
    use dregg_cell::program::StateConstraint;

    /// A factory whose children carry a perpetual WriteOnce-style slot caveat as
    /// their program-for-life. Sovereign so children are owner-governed.
    fn value_factory() -> FactoryDescriptor {
        FactoryDescriptor {
            factory_vk: *blake3::hash(b"image.value.factory").as_bytes(),
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::Any,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            }],
            field_constraints: vec![],
            // The program-for-life: slot 0 is write-once.
            state_constraints: vec![StateConstraint::WriteOnce { index: 0 }],
            default_mode: CellMode::Sovereign,
            creation_budget: None,
        }
    }

    /// A second, distinct factory (different constraints + templates) so the
    /// image spans more than one constructor.
    fn record_factory() -> FactoryDescriptor {
        FactoryDescriptor {
            factory_vk: *blake3::hash(b"image.record.factory").as_bytes(),
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates: vec![],
            field_constraints: vec![FieldConstraint::NonZero { field_index: 0 }],
            state_constraints: vec![StateConstraint::Monotonic { index: 1 }],
            default_mode: CellMode::Sovereign,
            creation_budget: None,
        }
    }

    fn cell_spec(factory: &FactoryDescriptor, owner: u8, balance: i64) -> CellSpec {
        // For the record factory, field 0 must be non-zero (its constraint).
        let initial_fields = if factory.field_constraints.is_empty() {
            vec![]
        } else {
            vec![(0u32, 7u64)]
        };
        CellSpec {
            factory_hash: factory.hash(),
            params: FactoryCreationParams {
                mode: factory.default_mode.clone(),
                program_vk: None,
                initial_fields,
                initial_caps: vec![],
                owner_pubkey: [owner; 32],
            },
            balance,
        }
    }

    /// A conserving manifest: a mint well (−1200) + two value cells (+1000,
    /// +200) + a record cell (0). Σ = 0, two distinct factories.
    fn conserving_manifest() -> ImageManifest {
        let vf = value_factory();
        let rf = record_factory();
        ImageManifest {
            name: "deos-genesis-test".to_string(),
            factories: vec![vf.clone(), rf.clone()],
            cells: vec![
                cell_spec(&vf, 0xF0, -1200), // the mint well: −supply
                cell_spec(&vf, 0x01, 1000),  // a wallet
                cell_spec(&vf, 0x42, 200),   // a peer
                cell_spec(&rf, 0xC0, 0),     // a record (record factory)
            ],
        }
    }

    #[test]
    fn build_then_verify_roundtrips() {
        let manifest = conserving_manifest();
        let artifact = build_image(&manifest).expect("build");
        let facts = verify_image(&artifact).expect("verify");

        assert_eq!(facts.balance_sum, 0, "the image conserves value");
        assert_eq!(facts.cell_count, 4);
        assert_eq!(facts.root, artifact.snapshot.claimed_root);
        // Two distinct factories.
        assert_eq!(facts.factory_hashes.len(), 2);
        // The artifact round-trips through its wire form, still verifying.
        let bytes = artifact.to_bytes().unwrap();
        let decoded = ImageArtifact::from_bytes(&bytes).unwrap();
        assert!(verify_image(&decoded).is_ok());
        // The attestation (Eq) round-trips exactly, and so does the manifest.
        assert_eq!(decoded.attestation, artifact.attestation);
        assert_eq!(decoded.manifest, artifact.manifest);
        assert_eq!(
            decoded.snapshot.claimed_root,
            artifact.snapshot.claimed_root
        );
    }

    #[test]
    fn built_cells_carry_their_factory_program_for_life() {
        let manifest = conserving_manifest();
        let artifact = build_image(&manifest).unwrap();
        let vf_hash = value_factory().hash();
        let rf_hash = record_factory().hash();
        for cell in &artifact.snapshot.overlay {
            // find the provenance for this cell
            let prov = artifact
                .attestation
                .cells
                .iter()
                .find(|p| p.cell_id == *cell.id().as_bytes())
                .unwrap();
            if prov.factory_hash == vf_hash {
                assert_eq!(
                    cell.program,
                    CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: 0 }]),
                    "value-factory child carries WriteOnce for life"
                );
            } else if prov.factory_hash == rf_hash {
                assert_eq!(
                    cell.program,
                    CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 1 }]),
                    "record-factory child carries Monotonic for life"
                );
            } else {
                panic!("unexpected factory hash in provenance");
            }
        }
    }

    #[test]
    fn tampered_root_is_rejected() {
        let manifest = conserving_manifest();
        let mut artifact = build_image(&manifest).unwrap();
        // Forge the attested root.
        artifact.attestation.claimed_root[0] ^= 0xff;
        let err = verify_image(&artifact).unwrap_err();
        assert!(matches!(err, VerifyError::RootBindingMismatch { .. }));
    }

    #[test]
    fn tampered_overlay_cell_is_rejected() {
        let manifest = conserving_manifest();
        let mut artifact = build_image(&manifest).unwrap();
        // Tamper a cell's balance in the overlay WITHOUT updating the root —
        // the reconstruct tooth must trip (the rebuilt root no longer matches).
        let forged = artifact.snapshot.overlay[1].state.balance() + 1;
        artifact.snapshot.overlay[1].state.set_balance(forged);
        let err = verify_image(&artifact).unwrap_err();
        assert!(
            matches!(err, VerifyError::RootReconstructMismatch { .. }),
            "got {err:?}"
        );
    }

    #[test]
    fn non_conserving_image_is_rejected() {
        let vf = value_factory();
        // A manifest whose balances do NOT sum to zero (no −supply well).
        let manifest = ImageManifest {
            name: "leaky".to_string(),
            factories: vec![vf.clone()],
            cells: vec![cell_spec(&vf, 0x01, 1000), cell_spec(&vf, 0x02, 200)],
        };
        let artifact = build_image(&manifest).unwrap();
        // The build succeeds (conservation is an attestation FACT, not a build
        // precondition — a builder may declare a non-conserving image), but
        // verification REFUSES it.
        assert_eq!(artifact.attestation.balance_sum, 1200);
        let err = verify_image(&artifact).unwrap_err();
        assert!(matches!(err, VerifyError::ConservationViolated { .. }));
    }

    #[test]
    fn wrong_factory_hash_in_spec_is_rejected_at_build() {
        let vf = value_factory();
        let mut manifest = conserving_manifest();
        // Point a cell at a factory hash not in the manifest.
        manifest.cells[0].factory_hash = *blake3::hash(b"ghost.factory").as_bytes();
        let err = build_image(&manifest).unwrap_err();
        assert!(matches!(err, BuildError::UnknownFactory { .. }));
        let _ = vf;
    }

    #[test]
    fn factory_validation_rejects_out_of_template_creation() {
        // The record factory requires field 0 non-zero; supply a zero.
        let rf = record_factory();
        let manifest = ImageManifest {
            name: "bad-fields".to_string(),
            factories: vec![rf.clone()],
            cells: vec![CellSpec {
                factory_hash: rf.hash(),
                params: FactoryCreationParams {
                    mode: CellMode::Sovereign,
                    program_vk: None,
                    initial_fields: vec![(0, 0)], // violates NonZero
                    initial_caps: vec![],
                    owner_pubkey: [0xC0; 32],
                },
                balance: 0,
            }],
        };
        let err = build_image(&manifest).unwrap_err();
        assert!(matches!(err, BuildError::Factory(_)), "got {err:?}");
    }

    #[test]
    fn smuggled_cell_under_wrong_factory_is_rejected() {
        // Build a good image, then rewrite one cell's provenance to claim a
        // DIFFERENT factory than the one whose program it carries.
        let manifest = conserving_manifest();
        let mut artifact = build_image(&manifest).unwrap();
        let vf_hash = value_factory().hash();
        let rf_hash = record_factory().hash();
        // Find a value-factory cell and relabel it as record-factory.
        for p in &mut artifact.attestation.cells {
            if p.factory_hash == vf_hash {
                p.factory_hash = rf_hash;
                break;
            }
        }
        // factory_hashes set still recomputes to {vf, rf}; but the relabeled
        // cell's program (WriteOnce) no longer matches record-factory (Monotonic)
        // AND its id (token == vf_hash) no longer matches rf_hash derivation.
        let err = verify_image(&artifact).unwrap_err();
        assert!(
            matches!(err, VerifyError::CellNotFromFactory { .. }),
            "got {err:?}"
        );
    }
}
