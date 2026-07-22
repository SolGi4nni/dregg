//! Authenticated, crash-recoverable local durability for [`WorldCell`].
//!
//! The image contains no signing secret. A deployment-owned
//! [`WorldCellSigningCustody`] supplies that authority transiently on every
//! provision/open, and the derived public key must authenticate every receipt
//! in the checkpoint. Each turn first persists its exact method/effects intent;
//! only after ordinary executor admission does one atomic image replace install
//! the new cells, signed receipt chain, and cleared intent. A crash at any point
//! therefore replays at most the pending intent from the last signed checkpoint.

#[cfg(not(unix))]
use std::fs::OpenOptions;
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

use dregg_app_framework::{CellId, Effect};
use fs2::FileExt;
use serde::{Deserialize, Serialize};
use zeroize::Zeroizing;

use crate::world::{WorldCellDurability, WorldCellDurableState};
use crate::{CompiledStory, WorldCell, WorldError};

const IMAGE_MAGIC: &[u8; 16] = b"SPW-WORLD-IMG-1\0";
const IMAGE_FILE: &str = "world-cell-v1.image";
const LEASE_FILE: &str = "world-cell-v1.lock";
const CHECKPOINT_MAGIC: &[u8; 16] = b"SPW-WORLD-CHK-1\0";
const MAX_IMAGE_BYTES: usize = 16 * 1024 * 1024;
const MAX_CELLS: usize = 32;
const MAX_RECEIPTS: usize = 65_536;
const MAX_EFFECTS: usize = 64;
const MAX_METHOD_BYTES: usize = 256;

/// External signing custody for a durable world. Implementations may use an
/// HSM, encrypted secret store, or locked local key file; the world image never
/// serializes the returned seed.
pub trait WorldCellSigningCustody: Send + Sync {
    fn acquire_signing_seed(&self) -> Result<Zeroizing<[u8; 32]>, String>;

    /// Return the deployment-owned monotonic checkpoint authority paired with
    /// this signer. The durable world retains only this public-state handle;
    /// it does not retain the signing-custody interface.
    fn checkpoint_anchor(&self) -> Arc<dyn WorldCellCheckpointAnchor>;
}

/// Exact authenticated coordinate observed by rollback protection.
///
/// `final_receipt_count` is the monotonic coordinate, while the receipt head,
/// authority root, and full state digest make an equal-coordinate retry
/// byte-identical. The static fields prevent an anchor from being reused by a
/// different program, cell, agent, signer, or federation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldCellCheckpoint {
    pub format: u16,
    pub scene_digest: [u8; 32],
    pub target_cell: CellId,
    pub agent_cell: CellId,
    pub executor_pubkey: [u8; 32],
    pub federation_id: [u8; 32],
    pub final_receipt_count: u64,
    pub final_receipt_head: Option<[u8; 32]>,
    pub authority_root: [u8; 32],
    pub state_digest: [u8; 32],
}

/// Deployment-owned monotonic storage for authenticated world checkpoints.
/// Implementations can be backed by a remote service, HSM counter, TPM, or the
/// hardened local-file implementation below.
pub trait WorldCellCheckpointAnchor: Send + Sync {
    /// Establish the first coordinate during explicit provisioning. Exact
    /// retries are idempotent; this is the only operation allowed to create
    /// previously absent anchor state.
    fn initialize_authenticated_checkpoint(
        &self,
        checkpoint: &WorldCellCheckpoint,
    ) -> Result<(), String>;

    /// Observe an already-established coordinate. Missing anchor state is an
    /// integrity failure, so deletion cannot turn a rollback into first use.
    fn observe_authenticated_checkpoint(
        &self,
        checkpoint: &WorldCellCheckpoint,
    ) -> Result<(), String>;
}

/// Local monotonic checkpoint store. Its directory is independent from every
/// replaceable world-image directory and is pinned for this handle's lifetime.
/// A deployment requiring protection from whole-volume rollback should
/// implement [`WorldCellCheckpointAnchor`] using remote/HSM monotonic storage.
pub struct FileWorldCellCheckpointAnchor {
    directory: PathBuf,
    directory_handle: File,
}

impl std::fmt::Debug for FileWorldCellCheckpointAnchor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FileWorldCellCheckpointAnchor")
            .finish_non_exhaustive()
    }
}

impl FileWorldCellCheckpointAnchor {
    pub fn open_or_create(directory: impl AsRef<Path>) -> Result<Self, WorldError> {
        let directory = directory.as_ref();
        ensure_private_directory(directory)?;
        let inspected = fs::symlink_metadata(directory)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        let directory_handle =
            File::open(directory).map_err(|error| WorldError::Durability(error.to_string()))?;
        validate_directory_handle(&directory_handle, &inspected)?;
        let directory = fs::canonicalize(directory)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        Ok(Self {
            directory,
            directory_handle,
        })
    }

    fn validate_directory_identity(&self) -> Result<(), WorldError> {
        let inspected = fs::symlink_metadata(&self.directory)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        if inspected.file_type().is_symlink() || !inspected.is_dir() {
            return Err(WorldError::Durability(
                "checkpoint anchor path no longer names its pinned directory".to_owned(),
            ));
        }
        validate_directory_handle(&self.directory_handle, &inspected)
    }
}

impl WorldCellCheckpointAnchor for FileWorldCellCheckpointAnchor {
    fn initialize_authenticated_checkpoint(
        &self,
        checkpoint: &WorldCellCheckpoint,
    ) -> Result<(), String> {
        self.validate_directory_identity()
            .map_err(|error| error.to_string())?;
        observe_file_checkpoint(&self.directory_handle, &self.directory, checkpoint, true)
            .map_err(|error| error.to_string())
    }

    fn observe_authenticated_checkpoint(
        &self,
        checkpoint: &WorldCellCheckpoint,
    ) -> Result<(), String> {
        self.validate_directory_identity()
            .map_err(|error| error.to_string())?;
        observe_file_checkpoint(&self.directory_handle, &self.directory, checkpoint, false)
            .map_err(|error| error.to_string())
    }
}

/// Resolve only the public identity of a custody handle. The transient seed is
/// zeroized before this returns and is never exposed to the caller.
pub fn world_cell_signing_custody_pubkey(
    custody: &dyn WorldCellSigningCustody,
) -> Result<[u8; 32], WorldError> {
    let signing_seed = custody
        .acquire_signing_seed()
        .map_err(WorldError::Durability)?;
    Ok(dregg_sdk::executor_pubkey_from_seed(&signing_seed))
}

/// Result of opening a durable world. The deterministic deployment seed is
/// public configuration and is returned for a registry to bind to its expected
/// cell id; signing material is never exposed.
pub struct OpenedDurableWorldCell {
    pub world: WorldCell,
    pub seed: u8,
}

/// Provision one new durable image. Existing images are never overwritten.
pub fn provision_durable_world_cell(
    directory: impl AsRef<Path>,
    story: Arc<CompiledStory>,
    seed: u8,
    custody: &dyn WorldCellSigningCustody,
) -> Result<WorldCell, WorldError> {
    let signing_seed = custody
        .acquire_signing_seed()
        .map_err(WorldError::Durability)?;
    let world = WorldCell::deploy_compiled(story.clone(), seed)?;
    world.set_executor_signing_key(*signing_seed);
    let intent_mac_key = Zeroizing::new(derive_intent_mac_key(&signing_seed));
    let store = FileWorldCellDurability::open(
        directory.as_ref(),
        OpenMode::Provision,
        Zeroizing::new(*intent_mac_key),
        custody.checkpoint_anchor(),
    )?;
    let state = world.durable_state();
    let image = DurableImage::new(&story, seed, &world, state)?;
    store.install_new(image)?;
    world.attach_durability(store)
}

/// Open, authenticate, and recover one existing durable image. If its image
/// carries a pending write-ahead intent, that exact turn is replayed through the
/// ordinary executor before this function returns.
pub fn open_durable_world_cell(
    directory: impl AsRef<Path>,
    story: Arc<CompiledStory>,
    custody: &dyn WorldCellSigningCustody,
) -> Result<OpenedDurableWorldCell, WorldError> {
    let signing_seed = custody
        .acquire_signing_seed()
        .map_err(WorldError::Durability)?;
    let intent_mac_key = Zeroizing::new(derive_intent_mac_key(&signing_seed));
    let store = FileWorldCellDurability::open(
        directory.as_ref(),
        OpenMode::Existing,
        Zeroizing::new(*intent_mac_key),
        custody.checkpoint_anchor(),
    )?;
    let image = store.image()?;
    image.validate_static(&story, *signing_seed)?;

    // Re-derive the unsigned genesis image independently. It authenticates a
    // receipt-empty provision; any later checkpoint is anchored by the signed
    // receipt head instead.
    let probe = WorldCell::deploy_compiled(story.clone(), image.seed)?;
    probe.set_executor_signing_key(*signing_seed);
    image.validate_probe(&probe)?;
    image.validate_committed(&intent_mac_key)?;
    store.observe_checkpoint(&image)?;

    let mut world =
        WorldCell::restore_compiled(story, image.seed, *signing_seed, image.committed.clone())?;
    if let Some(intent) = image.pending.as_ref() {
        intent.validate(&image.committed, &image.intent_authority(), &intent_mac_key)?;
        world.apply_raw(&intent.method, intent.effects.clone())?;
        store.commit_recovered(&world.durable_state())?;
    }
    world = world.attach_durability(store)?;
    Ok(OpenedDurableWorldCell {
        world,
        seed: image.seed,
    })
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct DurableTurnIntent {
    pre_state_digest: [u8; 32],
    method: String,
    effects: Vec<Effect>,
    intent_digest: [u8; 32],
    intent_authenticator: [u8; 32],
}

#[derive(Clone, Copy)]
struct DurableIntentAuthority {
    format: u16,
    scene_digest: [u8; 32],
    target_cell: CellId,
    agent_cell: CellId,
    executor_pubkey: [u8; 32],
    federation_id: [u8; 32],
}

impl DurableTurnIntent {
    fn new(
        state: &WorldCellDurableState,
        method: &str,
        effects: &[Effect],
        authority: &DurableIntentAuthority,
        intent_mac_key: &[u8; 32],
    ) -> Result<Self, WorldError> {
        if method.is_empty() || method.len() > MAX_METHOD_BYTES {
            return Err(WorldError::Durability(
                "durable turn method is empty or exceeds its bound".to_owned(),
            ));
        }
        if effects.is_empty() || effects.len() > MAX_EFFECTS {
            return Err(WorldError::Durability(
                "durable turn effect count is outside its bound".to_owned(),
            ));
        }
        let pre_state_digest = state_digest(state)?;
        let mut intent = Self {
            pre_state_digest,
            method: method.to_owned(),
            effects: effects.to_vec(),
            intent_digest: [0; 32],
            intent_authenticator: [0; 32],
        };
        intent.intent_digest = intent.compute_digest()?;
        intent.intent_authenticator = intent.compute_authenticator(authority, intent_mac_key)?;
        Ok(intent)
    }

    fn compute_digest(&self) -> Result<[u8; 32], WorldError> {
        let encoded = postcard::to_stdvec(&(
            self.pre_state_digest,
            self.method.as_str(),
            self.effects.as_slice(),
        ))
        .map_err(|error| WorldError::Durability(error.to_string()))?;
        Ok(*blake3::hash(&encoded).as_bytes())
    }

    fn compute_authenticator(
        &self,
        authority: &DurableIntentAuthority,
        intent_mac_key: &[u8; 32],
    ) -> Result<[u8; 32], WorldError> {
        let encoded = postcard::to_stdvec(&(
            authority.format,
            authority.scene_digest,
            authority.target_cell,
            authority.agent_cell,
            authority.executor_pubkey,
            authority.federation_id,
            self.pre_state_digest,
            self.method.as_str(),
            self.effects.as_slice(),
            self.intent_digest,
        ))
        .map_err(|error| WorldError::Durability(error.to_string()))?;
        let mut hasher = blake3::Hasher::new_keyed(intent_mac_key);
        hasher.update(b"spween-dregg/durable-turn-intent-authenticator/v1");
        hasher.update(&encoded);
        Ok(*hasher.finalize().as_bytes())
    }

    fn validate(
        &self,
        committed: &WorldCellDurableState,
        authority: &DurableIntentAuthority,
        intent_mac_key: &[u8; 32],
    ) -> Result<(), WorldError> {
        if self.method.is_empty()
            || self.method.len() > MAX_METHOD_BYTES
            || self.effects.is_empty()
            || self.effects.len() > MAX_EFFECTS
            || self.pre_state_digest != state_digest(committed)?
            || self.intent_digest != self.compute_digest()?
            || self.intent_authenticator != self.compute_authenticator(authority, intent_mac_key)?
        {
            return Err(WorldError::Durability(
                "durable pending turn intent failed its binding checks".to_owned(),
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct DurableImage {
    format: u16,
    seed: u8,
    scene_digest: [u8; 32],
    target_cell: CellId,
    agent_cell: CellId,
    executor_pubkey: [u8; 32],
    federation_id: [u8; 32],
    initial_state_digest: [u8; 32],
    committed: WorldCellDurableState,
    pending: Option<DurableTurnIntent>,
}

impl DurableImage {
    fn intent_authority(&self) -> DurableIntentAuthority {
        DurableIntentAuthority {
            format: self.format,
            scene_digest: self.scene_digest,
            target_cell: self.target_cell,
            agent_cell: self.agent_cell,
            executor_pubkey: self.executor_pubkey,
            federation_id: self.federation_id,
        }
    }

    fn new(
        story: &CompiledStory,
        seed: u8,
        world: &WorldCell,
        committed: WorldCellDurableState,
    ) -> Result<Self, WorldError> {
        let executor_pubkey = world.executor_pubkey().ok_or_else(|| {
            WorldError::Durability("durable world custody installed no executor key".to_owned())
        })?;
        let initial_state_digest = state_digest(&committed)?;
        Ok(Self {
            format: 1,
            seed,
            scene_digest: scene_digest(story)?,
            target_cell: world.cell_id(),
            agent_cell: committed
                .receipts
                .first()
                .map(|receipt| receipt.agent)
                .unwrap_or_else(|| world.executor_agent_cell()),
            executor_pubkey,
            federation_id: world.federation_id(),
            initial_state_digest,
            committed,
            pending: None,
        })
    }

    fn validate_static(
        &self,
        story: &CompiledStory,
        signing_seed: [u8; 32],
    ) -> Result<(), WorldError> {
        if self.format != 1
            || self.scene_digest != scene_digest(story)?
            || self.executor_pubkey != dregg_sdk::executor_pubkey_from_seed(&signing_seed)
        {
            return Err(WorldError::Durability(
                "durable world image differs from its story or signer custody".to_owned(),
            ));
        }
        Ok(())
    }

    fn validate_probe(&self, probe: &WorldCell) -> Result<(), WorldError> {
        if self.target_cell != probe.cell_id()
            || self.agent_cell != probe.executor_agent_cell()
            || self.executor_pubkey != probe.executor_pubkey().unwrap_or([0; 32])
            || self.federation_id != probe.federation_id()
            || self.initial_state_digest != state_digest(&probe.durable_state())?
        {
            return Err(WorldError::Durability(
                "durable world identity does not reproduce from its provision".to_owned(),
            ));
        }
        Ok(())
    }

    fn validate_committed(&self, intent_mac_key: &[u8; 32]) -> Result<(), WorldError> {
        validate_state(
            &self.committed,
            self.target_cell,
            self.agent_cell,
            self.executor_pubkey,
            self.federation_id,
            self.initial_state_digest,
        )?;
        if let Some(intent) = &self.pending {
            intent.validate(&self.committed, &self.intent_authority(), intent_mac_key)?;
        }
        Ok(())
    }

    fn checkpoint(&self) -> Result<WorldCellCheckpoint, WorldError> {
        let final_receipt_count = u64::try_from(self.committed.receipts.len()).map_err(|_| {
            WorldError::Durability("durable receipt coordinate exceeds u64".to_owned())
        })?;
        Ok(WorldCellCheckpoint {
            format: self.format,
            scene_digest: self.scene_digest,
            target_cell: self.target_cell,
            agent_cell: self.agent_cell,
            executor_pubkey: self.executor_pubkey,
            federation_id: self.federation_id,
            final_receipt_count,
            final_receipt_head: self
                .committed
                .receipts
                .last()
                .map(dregg_turn::TurnReceipt::receipt_hash),
            authority_root: self.committed.ledger_root,
            state_digest: state_digest(&self.committed)?,
        })
    }
}

struct FileWorldCellDurability {
    directory: PathBuf,
    directory_handle: File,
    image: Mutex<DurableImage>,
    intent_mac_key: Zeroizing<[u8; 32]>,
    checkpoint_anchor: Arc<dyn WorldCellCheckpointAnchor>,
    _lease: File,
}

#[derive(Clone, Copy)]
enum OpenMode {
    Provision,
    Existing,
}

impl FileWorldCellDurability {
    fn open(
        directory: &Path,
        mode: OpenMode,
        intent_mac_key: Zeroizing<[u8; 32]>,
        checkpoint_anchor: Arc<dyn WorldCellCheckpointAnchor>,
    ) -> Result<Arc<Self>, WorldError> {
        match mode {
            OpenMode::Provision => ensure_private_directory(directory)?,
            OpenMode::Existing => validate_existing_private_directory(directory)?,
        }
        let inspected = fs::symlink_metadata(directory)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        let directory_handle =
            File::open(directory).map_err(|error| WorldError::Durability(error.to_string()))?;
        validate_directory_handle(&directory_handle, &inspected)?;
        let directory = fs::canonicalize(directory)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        let lease = open_private_child(&directory_handle, &directory, LEASE_FILE, ChildOpen::Lease)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        validate_private_file(&lease, &directory_handle)?;
        lease.try_lock_exclusive().map_err(|error| {
            WorldError::Durability(format!("durable world image is already owned: {error}"))
        })?;
        let image = match mode {
            OpenMode::Provision => {
                if child_exists(&directory_handle, &directory, IMAGE_FILE)? {
                    return Err(WorldError::Durability(
                        "durable world image already exists".to_owned(),
                    ));
                }
                // Temporary placeholder; install_new replaces it while holding
                // the single-owner lease.
                DurableImage {
                    format: 0,
                    seed: 0,
                    scene_digest: [0; 32],
                    target_cell: CellId([0; 32]),
                    agent_cell: CellId([0; 32]),
                    executor_pubkey: [0; 32],
                    federation_id: [0; 32],
                    initial_state_digest: [0; 32],
                    committed: WorldCellDurableState {
                        cells: Vec::new(),
                        receipts: Vec::new(),
                        ledger_root: [0; 32],
                    },
                    pending: None,
                }
            }
            OpenMode::Existing => read_image(&directory_handle, &directory)?,
        };
        Ok(Arc::new(Self {
            directory,
            directory_handle,
            image: Mutex::new(image),
            intent_mac_key,
            checkpoint_anchor,
            _lease: lease,
        }))
    }

    fn install_new(&self, image: DurableImage) -> Result<(), WorldError> {
        self.validate_directory_identity()?;
        image.validate_committed(&self.intent_mac_key)?;
        self.initialize_checkpoint(&image)?;
        write_image(&self.directory_handle, &self.directory, &image, true)?;
        *self.image.lock().unwrap_or_else(|error| error.into_inner()) = image;
        Ok(())
    }

    fn image(&self) -> Result<DurableImage, WorldError> {
        self.validate_directory_identity()?;
        Ok(self
            .image
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .clone())
    }

    fn commit_recovered(&self, state: &WorldCellDurableState) -> Result<(), WorldError> {
        self.validate_directory_identity()?;
        let mut image = self.image.lock().unwrap_or_else(|error| error.into_inner());
        if image.pending.is_none() {
            return Err(WorldError::Durability(
                "recovery found no pending durable turn".to_owned(),
            ));
        }
        validate_state(
            state,
            image.target_cell,
            image.agent_cell,
            image.executor_pubkey,
            image.federation_id,
            image.initial_state_digest,
        )?;
        image.committed = state.clone();
        image.pending = None;
        write_image(&self.directory_handle, &self.directory, &image, false)?;
        self.observe_checkpoint(&image)
    }

    fn observe_checkpoint(&self, image: &DurableImage) -> Result<(), WorldError> {
        self.checkpoint_anchor
            .observe_authenticated_checkpoint(&image.checkpoint()?)
            .map_err(WorldError::Durability)
    }

    fn initialize_checkpoint(&self, image: &DurableImage) -> Result<(), WorldError> {
        self.checkpoint_anchor
            .initialize_authenticated_checkpoint(&image.checkpoint()?)
            .map_err(WorldError::Durability)
    }

    fn validate_directory_identity(&self) -> Result<(), WorldError> {
        let inspected = fs::symlink_metadata(&self.directory)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        if inspected.file_type().is_symlink() || !inspected.is_dir() {
            return Err(WorldError::Durability(
                "durable world directory path no longer names its pinned directory".to_owned(),
            ));
        }
        validate_directory_handle(&self.directory_handle, &inspected)
    }
}

impl WorldCellDurability for FileWorldCellDurability {
    fn bind(&self, state: &WorldCellDurableState) -> Result<(), String> {
        self.validate_directory_identity()
            .map_err(|error| error.to_string())?;
        let image = self.image.lock().unwrap_or_else(|error| error.into_inner());
        if image.pending.is_some()
            || state_digest(&image.committed).map_err(|error| error.to_string())?
                != state_digest(state).map_err(|error| error.to_string())?
        {
            return Err("live world differs from its committed durable image".to_owned());
        }
        self.observe_checkpoint(&image)
            .map_err(|error| error.to_string())?;
        Ok(())
    }

    fn prepare(
        &self,
        state: &WorldCellDurableState,
        method: &str,
        effects: &[Effect],
    ) -> Result<(), String> {
        self.validate_directory_identity()
            .map_err(|error| error.to_string())?;
        let mut image = self.image.lock().unwrap_or_else(|error| error.into_inner());
        if image.pending.is_some()
            || state_digest(&image.committed).map_err(|error| error.to_string())?
                != state_digest(state).map_err(|error| error.to_string())?
        {
            return Err("durable world prepare did not start at its committed image".to_owned());
        }
        let authority = image.intent_authority();
        image.pending = Some(
            DurableTurnIntent::new(state, method, effects, &authority, &self.intent_mac_key)
                .map_err(|error| error.to_string())?,
        );
        write_image(&self.directory_handle, &self.directory, &image, false)
            .map_err(|error| error.to_string())
    }

    fn commit(&self, state: &WorldCellDurableState) -> Result<(), String> {
        self.commit_recovered(state)
            .map_err(|error| error.to_string())
    }

    fn abort(&self, state: &WorldCellDurableState) -> Result<(), String> {
        self.validate_directory_identity()
            .map_err(|error| error.to_string())?;
        let mut image = self.image.lock().unwrap_or_else(|error| error.into_inner());
        if state_digest(&image.committed).map_err(|error| error.to_string())?
            != state_digest(state).map_err(|error| error.to_string())?
        {
            return Err(
                "refused turn changed durable state; pending intent retained for recovery"
                    .to_owned(),
            );
        }
        image.pending = None;
        write_image(&self.directory_handle, &self.directory, &image, false)
            .map_err(|error| error.to_string())
    }
}

fn validate_state(
    state: &WorldCellDurableState,
    target_cell: CellId,
    agent_cell: CellId,
    executor_pubkey: [u8; 32],
    federation_id: [u8; 32],
    initial_state_digest: [u8; 32],
) -> Result<(), WorldError> {
    if state.cells.is_empty()
        || state.cells.len() > MAX_CELLS
        || state.receipts.len() > MAX_RECEIPTS
        || !state.cells.iter().any(|cell| cell.id() == target_cell)
        || !state.cells.iter().any(|cell| cell.id() == agent_cell)
    {
        return Err(WorldError::Durability(
            "durable world state exceeds bounds or misses required cells".to_owned(),
        ));
    }
    if state.receipts.is_empty() {
        if state_digest(state)? != initial_state_digest {
            return Err(WorldError::Durability(
                "unsigned durable world state differs from deterministic genesis".to_owned(),
            ));
        }
        return Ok(());
    }
    let mut previous = None;
    for receipt in &state.receipts {
        if receipt.agent != agent_cell
            || receipt.federation_id != federation_id
            || receipt.finality != dregg_turn::Finality::Final
            || receipt.previous_receipt_hash != previous
            || dregg_turn::verify_receipt_signature_with_keys(receipt, &[executor_pubkey]).is_err()
        {
            return Err(WorldError::Durability(
                "durable world receipt chain failed authority verification".to_owned(),
            ));
        }
        previous = Some(receipt.receipt_hash());
    }
    if state
        .receipts
        .windows(2)
        .any(|pair| pair[0].post_state_hash != pair[1].pre_state_hash)
    {
        return Err(WorldError::Durability(
            "durable world receipt chain has a discontinuous authority root".to_owned(),
        ));
    }
    if state.receipts.last().expect("non-empty").post_state_hash != state.ledger_root {
        return Err(WorldError::Durability(
            "durable world receipt head does not bind its ledger root".to_owned(),
        ));
    }
    Ok(())
}

fn scene_digest(story: &CompiledStory) -> Result<[u8; 32], WorldError> {
    let encoded = postcard::to_stdvec(&(
        story.scene_id.as_str(),
        &story.var_slots,
        &story.has_slots,
        &story.passage_index,
        &story.program,
        &story.fully_gated,
    ))
    .map_err(|error| WorldError::Durability(error.to_string()))?;
    Ok(*blake3::hash(&encoded).as_bytes())
}

fn derive_intent_mac_key(signing_seed: &[u8; 32]) -> [u8; 32] {
    blake3::derive_key("spween-dregg/durable-turn-intent-mac-key/v1", signing_seed)
}

fn observe_file_checkpoint(
    directory_handle: &File,
    directory: &Path,
    checkpoint: &WorldCellCheckpoint,
    allow_initialize: bool,
) -> Result<(), WorldError> {
    let cell = cell_hex(checkpoint.target_cell);
    let lock_name = format!("world-cell-{cell}.checkpoint.lock");
    let image_name = format!("world-cell-{cell}.checkpoint");
    let lock = open_private_child(directory_handle, directory, &lock_name, ChildOpen::Lease)
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    validate_private_file(&lock, directory_handle)?;
    lock.lock_exclusive()
        .map_err(|error| WorldError::Durability(error.to_string()))?;

    let existing =
        match open_private_child(directory_handle, directory, &image_name, ChildOpen::Read) {
            Ok(mut file) => {
                validate_private_file(&file, directory_handle)?;
                let length = file
                    .metadata()
                    .map_err(|error| WorldError::Durability(error.to_string()))?
                    .len();
                if length > 4096 {
                    return Err(WorldError::Durability(
                        "checkpoint anchor exceeds its byte bound".to_owned(),
                    ));
                }
                let mut encoded = Vec::with_capacity(length as usize);
                file.read_to_end(&mut encoded)
                    .map_err(|error| WorldError::Durability(error.to_string()))?;
                Some(decode_checkpoint(&encoded)?)
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => None,
            Err(error) => return Err(WorldError::Durability(error.to_string())),
        };

    if let Some(existing) = existing {
        if checkpoint_static_identity(&existing) != checkpoint_static_identity(checkpoint) {
            return Err(WorldError::Durability(
                "checkpoint anchor static identity changed".to_owned(),
            ));
        }
        if checkpoint.final_receipt_count < existing.final_receipt_count {
            return Err(WorldError::Durability(
                "authenticated world checkpoint rolled back".to_owned(),
            ));
        }
        if checkpoint.final_receipt_count == existing.final_receipt_count {
            if checkpoint != &existing {
                return Err(WorldError::Durability(
                    "authenticated world checkpoint equivocated at one coordinate".to_owned(),
                ));
            }
            return Ok(());
        }
    } else if !allow_initialize {
        return Err(WorldError::Durability(
            "authenticated world checkpoint anchor is missing".to_owned(),
        ));
    }

    if (checkpoint.final_receipt_count == 0) != checkpoint.final_receipt_head.is_none() {
        return Err(WorldError::Durability(
            "checkpoint receipt coordinate and head disagree".to_owned(),
        ));
    }
    write_checkpoint(directory_handle, directory, &image_name, checkpoint)
}

fn checkpoint_static_identity(
    checkpoint: &WorldCellCheckpoint,
) -> (u16, [u8; 32], CellId, CellId, [u8; 32], [u8; 32]) {
    (
        checkpoint.format,
        checkpoint.scene_digest,
        checkpoint.target_cell,
        checkpoint.agent_cell,
        checkpoint.executor_pubkey,
        checkpoint.federation_id,
    )
}

fn write_checkpoint(
    directory_handle: &File,
    directory: &Path,
    image_name: &str,
    checkpoint: &WorldCellCheckpoint,
) -> Result<(), WorldError> {
    let encoded = encode_checkpoint(checkpoint)?;
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let temporary = format!(".checkpoint-{}-{nonce}.tmp", std::process::id());
    let mut file = open_private_child(
        directory_handle,
        directory,
        &temporary,
        ChildOpen::CreateNew,
    )
    .map_err(|error| WorldError::Durability(error.to_string()))?;
    validate_private_file(&file, directory_handle)?;
    file.write_all(&encoded)
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    file.sync_all()
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    rename_child(directory_handle, directory, &temporary, image_name)
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    directory_handle
        .sync_all()
        .map_err(|error| WorldError::Durability(error.to_string()))
}

fn encode_checkpoint(checkpoint: &WorldCellCheckpoint) -> Result<Vec<u8>, WorldError> {
    let payload = postcard::to_stdvec(checkpoint)
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    let mut encoded = Vec::with_capacity(CHECKPOINT_MAGIC.len() + 8 + payload.len() + 32);
    encoded.extend_from_slice(CHECKPOINT_MAGIC);
    encoded.extend_from_slice(&(payload.len() as u64).to_be_bytes());
    encoded.extend_from_slice(&payload);
    encoded.extend_from_slice(blake3::hash(&payload).as_bytes());
    Ok(encoded)
}

fn decode_checkpoint(encoded: &[u8]) -> Result<WorldCellCheckpoint, WorldError> {
    let header = CHECKPOINT_MAGIC.len() + 8;
    if encoded.len() < header + 32 || &encoded[..CHECKPOINT_MAGIC.len()] != CHECKPOINT_MAGIC {
        return Err(WorldError::Durability(
            "checkpoint anchor has invalid framing".to_owned(),
        ));
    }
    let length = u64::from_be_bytes(
        encoded[CHECKPOINT_MAGIC.len()..header]
            .try_into()
            .expect("fixed checkpoint length"),
    );
    let length = usize::try_from(length)
        .map_err(|_| WorldError::Durability("checkpoint anchor length overflow".to_owned()))?;
    if length > 2048 || encoded.len() != header + length + 32 {
        return Err(WorldError::Durability(
            "checkpoint anchor length is invalid".to_owned(),
        ));
    }
    let payload = &encoded[header..header + length];
    if blake3::hash(payload).as_bytes() != &encoded[header + length..] {
        return Err(WorldError::Durability(
            "checkpoint anchor checksum mismatch".to_owned(),
        ));
    }
    postcard::from_bytes(payload).map_err(|error| WorldError::Durability(error.to_string()))
}

fn cell_hex(cell: CellId) -> String {
    let mut encoded = String::with_capacity(64);
    for byte in cell.0 {
        use std::fmt::Write as _;
        write!(&mut encoded, "{byte:02x}").expect("writing to String cannot fail");
    }
    encoded
}

fn state_digest(state: &WorldCellDurableState) -> Result<[u8; 32], WorldError> {
    let encoded =
        postcard::to_stdvec(state).map_err(|error| WorldError::Durability(error.to_string()))?;
    Ok(*blake3::hash(&encoded).as_bytes())
}

fn encode_image(image: &DurableImage) -> Result<Vec<u8>, WorldError> {
    let payload =
        postcard::to_stdvec(image).map_err(|error| WorldError::Durability(error.to_string()))?;
    if payload.len() > MAX_IMAGE_BYTES {
        return Err(WorldError::Durability(
            "durable world image exceeds its byte bound".to_owned(),
        ));
    }
    let mut encoded = Vec::with_capacity(IMAGE_MAGIC.len() + 8 + payload.len() + 32);
    encoded.extend_from_slice(IMAGE_MAGIC);
    encoded.extend_from_slice(&(payload.len() as u64).to_be_bytes());
    encoded.extend_from_slice(&payload);
    encoded.extend_from_slice(blake3::hash(&payload).as_bytes());
    Ok(encoded)
}

fn decode_image(bytes: &[u8]) -> Result<DurableImage, WorldError> {
    let header = IMAGE_MAGIC.len() + 8;
    if bytes.len() < header + 32 || &bytes[..IMAGE_MAGIC.len()] != IMAGE_MAGIC {
        return Err(WorldError::Durability(
            "durable world image has invalid framing".to_owned(),
        ));
    }
    let length = u64::from_be_bytes(
        bytes[IMAGE_MAGIC.len()..header]
            .try_into()
            .expect("fixed image length"),
    );
    let length = usize::try_from(length)
        .map_err(|_| WorldError::Durability("durable world image length overflow".to_owned()))?;
    if length > MAX_IMAGE_BYTES || bytes.len() != header + length + 32 {
        return Err(WorldError::Durability(
            "durable world image length is invalid".to_owned(),
        ));
    }
    let payload = &bytes[header..header + length];
    if blake3::hash(payload).as_bytes() != &bytes[header + length..] {
        return Err(WorldError::Durability(
            "durable world image checksum mismatch".to_owned(),
        ));
    }
    postcard::from_bytes(payload).map_err(|error| WorldError::Durability(error.to_string()))
}

fn read_image(directory_handle: &File, directory: &Path) -> Result<DurableImage, WorldError> {
    let mut file = open_private_child(directory_handle, directory, IMAGE_FILE, ChildOpen::Read)
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    validate_private_file(&file, directory_handle)?;
    let length = file
        .metadata()
        .map_err(|error| WorldError::Durability(error.to_string()))?
        .len();
    if length > (MAX_IMAGE_BYTES + 64) as u64 {
        return Err(WorldError::Durability(
            "durable world image file exceeds its byte bound".to_owned(),
        ));
    }
    let mut bytes = Vec::with_capacity(length as usize);
    file.read_to_end(&mut bytes)
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    decode_image(&bytes)
}

fn write_image(
    directory_handle: &File,
    directory: &Path,
    image: &DurableImage,
    create_only: bool,
) -> Result<(), WorldError> {
    if create_only && child_exists(directory_handle, directory, IMAGE_FILE)? {
        return Err(WorldError::Durability(
            "durable world image already exists".to_owned(),
        ));
    }
    if !create_only {
        let file = open_private_child(directory_handle, directory, IMAGE_FILE, ChildOpen::Read)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        validate_private_file(&file, directory_handle)?;
    }
    let encoded = encode_image(image)?;
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let temporary = format!(".world-cell-v1-{}-{nonce}.tmp", std::process::id());
    let mut file = open_private_child(
        directory_handle,
        directory,
        &temporary,
        ChildOpen::CreateNew,
    )
    .map_err(|error| WorldError::Durability(error.to_string()))?;
    validate_private_file(&file, directory_handle)?;
    file.write_all(&encoded)
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    file.sync_all()
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    rename_child(directory_handle, directory, &temporary, IMAGE_FILE)
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    directory_handle
        .sync_all()
        .map_err(|error| WorldError::Durability(error.to_string()))
}

fn ensure_private_directory(path: &Path) -> Result<(), WorldError> {
    fs::create_dir_all(path).map_err(|error| WorldError::Durability(error.to_string()))?;
    let metadata =
        fs::symlink_metadata(path).map_err(|error| WorldError::Durability(error.to_string()))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(WorldError::Durability(
            "durable world directory is not a private directory".to_owned(),
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut permissions = metadata.permissions();
        permissions.set_mode(0o700);
        fs::set_permissions(path, permissions)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
    }
    Ok(())
}

fn validate_existing_private_directory(path: &Path) -> Result<(), WorldError> {
    let metadata =
        fs::symlink_metadata(path).map_err(|error| WorldError::Durability(error.to_string()))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(WorldError::Durability(
            "durable world directory is not an existing private directory".to_owned(),
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if metadata.permissions().mode() & 0o077 != 0 {
            return Err(WorldError::Durability(
                "durable world directory permissions are too broad".to_owned(),
            ));
        }
    }
    Ok(())
}

fn validate_private_file(file: &File, directory: &File) -> Result<(), WorldError> {
    let metadata = file
        .metadata()
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    if !metadata.is_file() {
        return Err(WorldError::Durability(
            "durable world file is not regular".to_owned(),
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        if metadata.nlink() != 1 {
            return Err(WorldError::Durability(
                "durable world file has multiple hard links".to_owned(),
            ));
        }
        if metadata.permissions().mode() & 0o077 != 0 {
            return Err(WorldError::Durability(
                "durable world file permissions are too broad".to_owned(),
            ));
        }
        let parent = directory
            .metadata()
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        if metadata.uid() != parent.uid() {
            return Err(WorldError::Durability(
                "durable world file owner differs from its directory".to_owned(),
            ));
        }
    }
    Ok(())
}

fn validate_directory_handle(file: &File, inspected: &fs::Metadata) -> Result<(), WorldError> {
    let opened = file
        .metadata()
        .map_err(|error| WorldError::Durability(error.to_string()))?;
    if !opened.is_dir() {
        return Err(WorldError::Durability(
            "durable world directory handle is not a directory".to_owned(),
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        if opened.dev() != inspected.dev()
            || opened.ino() != inspected.ino()
            || opened.permissions().mode() & 0o077 != 0
        {
            return Err(WorldError::Durability(
                "durable world directory changed identity while it was pinned".to_owned(),
            ));
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum ChildOpen {
    Read,
    Lease,
    CreateNew,
}

#[cfg(unix)]
fn open_private_child(
    directory: &File,
    _directory_path: &Path,
    name: &str,
    mode: ChildOpen,
) -> io::Result<File> {
    use std::ffi::CString;
    use std::os::fd::{AsRawFd, FromRawFd};

    let name = CString::new(name)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "NUL in child name"))?;
    let flags = match mode {
        ChildOpen::Read => libc::O_RDONLY,
        ChildOpen::Lease => libc::O_RDWR | libc::O_CREAT,
        ChildOpen::CreateNew => libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL,
    } | libc::O_CLOEXEC
        | libc::O_NOFOLLOW;
    // SAFETY: `directory` is a validated open directory FD, `name` is a
    // NUL-terminated single component, and a successful owned FD is converted
    // exactly once into `File`.
    let fd = unsafe { libc::openat(directory.as_raw_fd(), name.as_ptr(), flags, 0o600) };
    if fd < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(unsafe { File::from_raw_fd(fd) })
    }
}

#[cfg(not(unix))]
fn open_private_child(
    _directory: &File,
    directory_path: &Path,
    name: &str,
    mode: ChildOpen,
) -> io::Result<File> {
    let mut options = OpenOptions::new();
    match mode {
        ChildOpen::Read => {
            options.read(true);
        }
        ChildOpen::Lease => {
            options.read(true).write(true).create(true);
        }
        ChildOpen::CreateNew => {
            options.write(true).create_new(true);
        }
    }
    options.open(directory_path.join(name))
}

fn child_exists(directory: &File, directory_path: &Path, name: &str) -> Result<bool, WorldError> {
    match open_private_child(directory, directory_path, name, ChildOpen::Read) {
        Ok(file) => {
            validate_private_file(&file, directory)?;
            Ok(true)
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(WorldError::Durability(error.to_string())),
    }
}

#[cfg(unix)]
fn rename_child(directory: &File, _directory_path: &Path, from: &str, to: &str) -> io::Result<()> {
    use std::ffi::CString;
    use std::os::fd::AsRawFd;

    let from = CString::new(from)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "NUL in child name"))?;
    let to = CString::new(to)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "NUL in child name"))?;
    // SAFETY: both names are single-component C strings resolved relative to
    // the same pinned directory FD.
    let result = unsafe {
        libc::renameat(
            directory.as_raw_fd(),
            from.as_ptr(),
            directory.as_raw_fd(),
            to.as_ptr(),
        )
    };
    if result == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(not(unix))]
fn rename_child(_directory: &File, directory_path: &Path, from: &str, to: &str) -> io::Result<()> {
    fs::rename(directory_path.join(from), directory_path.join(to))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    use dregg_app_framework::{
        CellProgram, StateConstraint, TransitionCase, TransitionGuard, field_from_u64, symbol,
    };

    struct TestCustody {
        seed: [u8; 32],
        anchor: Arc<FileWorldCellCheckpointAnchor>,
    }

    impl TestCustody {
        fn new(seed: [u8; 32], anchor: &Path) -> Self {
            Self {
                seed,
                anchor: Arc::new(FileWorldCellCheckpointAnchor::open_or_create(anchor).unwrap()),
            }
        }
    }

    impl WorldCellSigningCustody for TestCustody {
        fn acquire_signing_seed(&self) -> Result<Zeroizing<[u8; 32]>, String> {
            Ok(Zeroizing::new(self.seed))
        }

        fn checkpoint_anchor(&self) -> Arc<dyn WorldCellCheckpointAnchor> {
            self.anchor.clone()
        }
    }

    fn counter_story() -> Arc<CompiledStory> {
        Arc::new(CompiledStory {
            scene_id: "durable-counter".to_owned(),
            var_slots: BTreeMap::from([("counter".to_owned(), 1)]),
            has_slots: BTreeMap::new(),
            passage_index: BTreeMap::new(),
            program: CellProgram::Cases(vec![TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol("counter/gain"),
                },
                constraints: vec![StateConstraint::StrictMonotonic { index: 1 }],
            }]),
            fully_gated: BTreeMap::new(),
        })
    }

    fn prepared_store(
        directory: &Path,
        story: &Arc<CompiledStory>,
        custody: &TestCustody,
    ) -> (WorldCell, Arc<FileWorldCellDurability>) {
        let world = WorldCell::deploy_compiled(story.clone(), 7).unwrap();
        world.set_executor_signing_key(custody.seed);
        let store = FileWorldCellDurability::open(
            directory,
            OpenMode::Provision,
            Zeroizing::new(derive_intent_mac_key(&custody.seed)),
            custody.checkpoint_anchor(),
        )
        .unwrap();
        store
            .install_new(DurableImage::new(story, 7, &world, world.durable_state()).unwrap())
            .unwrap();
        (world, store)
    }

    #[test]
    fn checkpoint_anchor_is_idempotent_and_refuses_rollback_or_equivocation() {
        let temp = tempfile::tempdir().unwrap();
        let anchor =
            FileWorldCellCheckpointAnchor::open_or_create(temp.path().join("anchor")).unwrap();
        let genesis = WorldCellCheckpoint {
            format: 1,
            scene_digest: [0x11; 32],
            target_cell: CellId([0x12; 32]),
            agent_cell: CellId([0x13; 32]),
            executor_pubkey: [0x14; 32],
            federation_id: [0x15; 32],
            final_receipt_count: 0,
            final_receipt_head: None,
            authority_root: [0x16; 32],
            state_digest: [0x17; 32],
        };
        assert!(anchor.observe_authenticated_checkpoint(&genesis).is_err());
        anchor
            .initialize_authenticated_checkpoint(&genesis)
            .unwrap();
        anchor.observe_authenticated_checkpoint(&genesis).unwrap();

        let mut next = genesis.clone();
        next.final_receipt_count = 1;
        next.final_receipt_head = Some([0x21; 32]);
        next.authority_root = [0x22; 32];
        next.state_digest = [0x23; 32];
        anchor.observe_authenticated_checkpoint(&next).unwrap();
        anchor.observe_authenticated_checkpoint(&next).unwrap();

        assert!(anchor.observe_authenticated_checkpoint(&genesis).is_err());
        let mut equivocation = next.clone();
        equivocation.state_digest[0] ^= 1;
        assert!(
            anchor
                .observe_authenticated_checkpoint(&equivocation)
                .is_err()
        );
        let mut wrong_program = next;
        wrong_program.scene_digest[0] ^= 1;
        wrong_program.final_receipt_count = 2;
        wrong_program.final_receipt_head = Some([0x24; 32]);
        assert!(
            anchor
                .observe_authenticated_checkpoint(&wrong_program)
                .is_err()
        );

        let checkpoint_file = temp.path().join("anchor").join(format!(
            "world-cell-{}.checkpoint",
            cell_hex(genesis.target_cell)
        ));
        fs::remove_file(checkpoint_file).unwrap();
        assert!(anchor.observe_authenticated_checkpoint(&next).is_err());
    }

    #[test]
    fn prepared_intent_replays_once_through_the_ordinary_executor_after_restart() {
        let temp = tempfile::tempdir().unwrap();
        let directory = temp.path().join("world");
        let story = counter_story();
        let custody = TestCustody::new([0x62; 32], &temp.path().join("anchor"));

        // Reproduce the precise crash boundary: a valid genesis checkpoint is
        // installed, the exact next intent is forced, and the process disappears
        // before submit_action can run.
        let (world, store) = prepared_store(&directory, &story, &custody);
        let effects = vec![Effect::SetField {
            cell: world.cell_id(),
            index: 1,
            value: field_from_u64(9),
        }];
        store
            .prepare(&world.durable_state(), "counter/gain", &effects)
            .unwrap();
        drop(store);
        drop(world);

        let recovered = open_durable_world_cell(&directory, story.clone(), &custody).unwrap();
        assert_eq!(recovered.world.read_var("counter"), 9);
        assert_eq!(recovered.world.receipt_chain_snapshot().len(), 1);
        let head = recovered.world.receipt_chain_snapshot()[0].receipt_hash();
        drop(recovered);

        // The successful recovery atomically cleared the intent: another open
        // restores the checkpoint and does not award the turn twice.
        let reopened = open_durable_world_cell(&directory, story, &custody).unwrap();
        assert_eq!(reopened.world.read_var("counter"), 9);
        assert_eq!(reopened.world.receipt_chain_snapshot().len(), 1);
        assert_eq!(
            reopened.world.receipt_chain_snapshot()[0].receipt_hash(),
            head
        );
    }

    #[test]
    fn forged_pending_intent_with_recomputed_public_hashes_is_refused() {
        let temp = tempfile::tempdir().unwrap();
        let directory = temp.path().join("world");
        let story = counter_story();
        let custody = TestCustody::new([0x72; 32], &temp.path().join("anchor"));
        let (world, store) = prepared_store(&directory, &story, &custody);
        let effects = vec![Effect::SetField {
            cell: world.cell_id(),
            index: 1,
            value: field_from_u64(9),
        }];
        store
            .prepare(&world.durable_state(), "counter/gain", &effects)
            .unwrap();
        drop(store);
        drop(world);

        let path = directory.join(IMAGE_FILE);
        let mut image = decode_image(&fs::read(&path).unwrap()).unwrap();
        let pending = image.pending.as_mut().unwrap();
        pending.method = "counter/forged".to_owned();
        pending.intent_digest = pending.compute_digest().unwrap();
        // The attacker can recompute the public framing checksum but not the
        // custody-derived authenticator over this new method.
        fs::write(&path, encode_image(&image).unwrap()).unwrap();
        assert!(matches!(
            open_durable_world_cell(&directory, story, &custody),
            Err(WorldError::Durability(_))
        ));
    }

    #[cfg(unix)]
    #[test]
    fn replaced_directory_and_symlinked_image_are_refused() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let temp = tempfile::tempdir().unwrap();
        let directory = temp.path().join("world");
        let moved = temp.path().join("moved-world");
        let story = counter_story();
        let custody = TestCustody::new([0x82; 32], &temp.path().join("anchor"));
        let (world, store) = prepared_store(&directory, &story, &custody);
        fs::rename(&directory, &moved).unwrap();
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let effects = vec![Effect::SetField {
            cell: world.cell_id(),
            index: 1,
            value: field_from_u64(9),
        }];
        assert!(
            store
                .prepare(&world.durable_state(), "counter/gain", &effects)
                .is_err()
        );
        assert!(!directory.join(IMAGE_FILE).exists());
        drop(store);
        drop(world);

        fs::remove_dir(&directory).unwrap();
        fs::rename(&moved, &directory).unwrap();
        let image = directory.join(IMAGE_FILE);
        let held = directory.join("held.image");
        fs::rename(&image, &held).unwrap();
        symlink("held.image", &image).unwrap();
        assert!(matches!(
            open_durable_world_cell(&directory, story, &custody),
            Err(WorldError::Durability(_))
        ));
    }
}
