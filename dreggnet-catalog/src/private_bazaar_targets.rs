//! Authenticated durable Dungeon target registry for the live private Bazaar.
//!
//! Ordinary startup only opens an exact, already-provisioned directory for
//! every deployment-pinned roster cell. It never invents a seed or target.
//! Each image independently authenticates its signed receipt chain and any
//! prepared turn before recovery, while executor signing material remains in a
//! separate deployment-owned custody handle.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom};
use std::path::Path;
use std::sync::{Arc, Mutex};

use dregg_types::CellId;
use dreggnet_offerings::character::{Character, CharacterSheet, CharacterStore};
use dreggnet_offerings::dungeon::{DungeonOffering, DungeonSession};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, OfferingHost, Outcome, RunCost, SessionConfig,
    Surface, VerifyReport,
};
use dungeon_on_dregg::meta::meta_hero_story;
use spween_dregg::{
    FileWorldCellCheckpointAnchor, WorldCell, WorldCellCheckpointAnchor, WorldCellSigningCustody,
    WorldError, open_durable_world_cell, provision_durable_world_cell,
    world_cell_signing_custody_pubkey,
};
use zeroize::Zeroizing;

use crate::{PrivateBazaarLiveDeployment, PrivateBazaarWorkerError, PrivateBazaarWorkerTargets};

/// External secret file used by the production loader. The file is custody,
/// not part of any world snapshot, and must contain exactly 32 raw bytes or 64
/// hexadecimal bytes.
pub use crate::private_bazaar_live::PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV;

#[derive(Debug)]
pub enum PrivateBazaarTargetRegistryError {
    Config(String),
    Io(String),
    World(WorldError),
    Worker(PrivateBazaarWorkerError),
}

impl std::fmt::Display for PrivateBazaarTargetRegistryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Config(message) => write!(f, "private Bazaar target registry refused: {message}"),
            Self::Io(message) => write!(f, "private Bazaar target storage refused: {message}"),
            Self::World(error) => write!(f, "private Bazaar target image refused: {error}"),
            Self::Worker(error) => write!(f, "private Bazaar target install refused: {error}"),
        }
    }
}

impl std::error::Error for PrivateBazaarTargetRegistryError {}

impl From<WorldError> for PrivateBazaarTargetRegistryError {
    fn from(error: WorldError) -> Self {
        Self::World(error)
    }
}

impl From<PrivateBazaarWorkerError> for PrivateBazaarTargetRegistryError {
    fn from(error: PrivateBazaarWorkerError) -> Self {
        Self::Worker(error)
    }
}

/// Locked local-file implementation of the external signing-custody seam.
/// Debug output never includes the path, file contents, or derived public key.
pub struct PrivateBazaarFileSigningCustody {
    file: Mutex<File>,
    checkpoint_anchor: Arc<FileWorldCellCheckpointAnchor>,
}

impl std::fmt::Debug for PrivateBazaarFileSigningCustody {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateBazaarFileSigningCustody")
            .finish_non_exhaustive()
    }
}

impl PrivateBazaarFileSigningCustody {
    pub fn open(
        path: impl AsRef<Path>,
        checkpoint_directory: impl AsRef<Path>,
    ) -> Result<Self, PrivateBazaarTargetRegistryError> {
        let path = path.as_ref();
        let link_metadata = fs::symlink_metadata(path)
            .map_err(|error| PrivateBazaarTargetRegistryError::Io(error.to_string()))?;
        if link_metadata.file_type().is_symlink() || !link_metadata.is_file() {
            return Err(PrivateBazaarTargetRegistryError::Config(
                "executor signing custody is not a regular file".to_owned(),
            ));
        }
        let file = OpenOptions::new()
            .read(true)
            .open(path)
            .map_err(|error| PrivateBazaarTargetRegistryError::Io(error.to_string()))?;
        validate_custody_file(&file, &link_metadata)?;
        let custody = Self {
            file: Mutex::new(file),
            checkpoint_anchor: Arc::new(FileWorldCellCheckpointAnchor::open_or_create(
                checkpoint_directory,
            )?),
        };
        // Parse once now so malformed custody refuses before target traversal.
        custody
            .acquire_signing_seed()
            .map_err(PrivateBazaarTargetRegistryError::Config)?;
        Ok(custody)
    }
}

impl WorldCellSigningCustody for PrivateBazaarFileSigningCustody {
    fn acquire_signing_seed(&self) -> Result<Zeroizing<[u8; 32]>, String> {
        let mut file = self
            .file
            .lock()
            .map_err(|_| "executor signing custody lock is poisoned".to_owned())?;
        file.seek(SeekFrom::Start(0))
            .map_err(|error| error.to_string())?;
        let mut encoded = Zeroizing::new(Vec::with_capacity(65));
        (&mut *file)
            .take(65)
            .read_to_end(&mut encoded)
            .map_err(|error| error.to_string())?;
        decode_signing_seed(&encoded)
    }

    fn checkpoint_anchor(&self) -> Arc<dyn WorldCellCheckpointAnchor> {
        self.checkpoint_anchor.clone()
    }
}

/// Opened exact roster coverage. Its worker registry retains every world and,
/// transitively, every exclusive durable-image lease for the runtime lifetime.
pub struct PrivateBazaarDurableTargetRegistry {
    targets: PrivateBazaarWorkerTargets,
    worlds: BTreeMap<CellId, Arc<WorldCell>>,
    characters: PrivateBazaarCharacterStore,
    policy_id: [u8; 32],
}

impl PrivateBazaarDurableTargetRegistry {
    /// Load the custody path from deployment configuration, verify its public
    /// identity against the global pin, then open every pre-provisioned target.
    pub fn load_from_env(
        deployment: &PrivateBazaarLiveDeployment,
    ) -> Result<Self, PrivateBazaarTargetRegistryError> {
        let path = std::env::var(PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV)
            .ok()
            .filter(|value| !value.trim().is_empty())
            .ok_or_else(|| {
                PrivateBazaarTargetRegistryError::Config(format!(
                    "{PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV} is required"
                ))
            })?;
        let custody = PrivateBazaarFileSigningCustody::open(
            path,
            deployment.private_target_checkpoint_root(),
        )?;
        Self::load(deployment, &custody)
    }

    /// Open only the exact target directories named by the pinned roster.
    /// Missing, extra, duplicate, mismatched, or unauthenticated targets refuse
    /// the whole registry before a worker is started.
    pub fn load(
        deployment: &PrivateBazaarLiveDeployment,
        custody: &dyn WorldCellSigningCustody,
    ) -> Result<Self, PrivateBazaarTargetRegistryError> {
        verify_custody_pin(deployment, custody)?;
        let expected = expected_cells(deployment)?;
        let root = deployment.private_target_root();
        validate_exact_target_root(&root, expected.keys().copied())?;

        let mut worlds = BTreeMap::new();
        let story = Arc::new(meta_hero_story());
        for (cell, directory_name) in &expected {
            let opened =
                open_durable_world_cell(root.join(directory_name), story.clone(), custody)?;
            validate_opened_target(deployment, *cell, &opened.world)?;
            let world = Arc::new(opened.world);
            worlds.insert(*cell, world);
        }
        let targets = PrivateBazaarWorkerTargets::from_worlds(worlds.values().cloned())?;
        let characters = character_store(deployment, &worlds)?;
        Ok(Self {
            targets,
            worlds,
            characters,
            policy_id: deployment.private_policy_id(),
        })
    }

    /// Explicit operator provisioning path. This first proves that the supplied
    /// deterministic seeds derive exactly the pinned roster, then creates new
    /// images. It refuses an existing target root and never overwrites a target.
    pub fn provision(
        deployment: &PrivateBazaarLiveDeployment,
        custody: &dyn WorldCellSigningCustody,
        seeds: &[u8],
    ) -> Result<Self, PrivateBazaarTargetRegistryError> {
        verify_custody_pin(deployment, custody)?;
        let expected = expected_cells(deployment)?;
        let story = Arc::new(meta_hero_story());
        let mut derived = BTreeMap::new();
        for seed in seeds {
            let probe = WorldCell::deploy_compiled(story.clone(), *seed)?;
            if derived.insert(probe.cell_id(), *seed).is_some() {
                return Err(PrivateBazaarTargetRegistryError::Config(
                    "target provisioning seeds derive duplicate character cells".to_owned(),
                ));
            }
        }
        if derived.keys().copied().collect::<BTreeSet<_>>()
            != expected.keys().copied().collect::<BTreeSet<_>>()
        {
            return Err(PrivateBazaarTargetRegistryError::Config(
                "target provisioning seeds do not derive exactly the pinned roster".to_owned(),
            ));
        }

        let root = deployment.private_target_root();
        create_private_target_root(&root)?;
        let mut worlds = BTreeMap::new();
        for (cell, directory_name) in &expected {
            let seed = derived[cell];
            let world = provision_durable_world_cell(
                root.join(directory_name),
                story.clone(),
                seed,
                custody,
            )?;
            validate_opened_target(deployment, *cell, &world)?;
            let world = Arc::new(world);
            worlds.insert(*cell, world);
        }
        let targets = PrivateBazaarWorkerTargets::from_worlds(worlds.values().cloned())?;
        let characters = character_store(deployment, &worlds)?;
        Ok(Self {
            targets,
            worlds,
            characters,
            policy_id: deployment.private_policy_id(),
        })
    }

    pub fn len(&self) -> usize {
        self.worlds.len()
    }

    pub fn is_empty(&self) -> bool {
        self.worlds.is_empty()
    }

    /// Read-only clone consumed by the frontend. It resolves a viewer only to
    /// that roster member's exact durable meta-hero world; it has no install or
    /// replacement capability.
    pub fn character_store(&self) -> PrivateBazaarCharacterStore {
        self.characters.clone()
    }

    pub(crate) fn into_worker_targets_for(
        self,
        deployment: &PrivateBazaarLiveDeployment,
    ) -> Result<PrivateBazaarWorkerTargets, PrivateBazaarTargetRegistryError> {
        let expected = deployment
            .private_target_cells()
            .into_iter()
            .collect::<BTreeSet<_>>();
        if self.policy_id != deployment.private_policy_id()
            || self.worlds.keys().copied().collect::<BTreeSet<_>>() != expected
            || self.targets.len() != expected.len()
        {
            return Err(PrivateBazaarTargetRegistryError::Config(
                "durable target registry is not sealed to this exact deployment policy".to_owned(),
            ));
        }
        Ok(self.targets)
    }
}

/// Read-only CharacterStore over the exact durable roster worlds. Sheet loads
/// and live Character opens observe the same Arc that the Bazaar worker mutates.
#[derive(Clone)]
pub struct PrivateBazaarCharacterStore {
    entries: Arc<Vec<(DreggIdentity, Arc<WorldCell>)>>,
}

impl std::fmt::Debug for PrivateBazaarCharacterStore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateBazaarCharacterStore")
            .field("characters", &self.entries.len())
            .finish()
    }
}

impl PrivateBazaarCharacterStore {
    fn world_for(&self, who: &DreggIdentity) -> Option<Arc<WorldCell>> {
        self.entries
            .iter()
            .find(|(actor, _)| actor == who)
            .map(|(_, world)| Arc::clone(world))
    }

    /// Replace the baseline dungeon card with a viewer-bound projection over
    /// these canonical characters. Dungeon play remains the ordinary offering;
    /// the character panel is read from the exact world the Bazaar consequence
    /// advances, so a restart cannot display a shadow sheet.
    pub fn register_dungeon(&self, host: &mut OfferingHost) {
        host.register(
            "dungeon",
            "The Warden's Keep — a verifiable dungeon with one durable character authority",
            PrivateBazaarCharacterDungeonOffering {
                dungeon: DungeonOffering::new(),
                characters: self.clone(),
            },
        );
    }
}

impl CharacterStore for PrivateBazaarCharacterStore {
    fn load(&self, who: &DreggIdentity) -> CharacterSheet {
        self.world_for(who)
            .map(|_| Character::open_from_store(who.clone(), self).sheet())
            .unwrap_or_default()
    }

    fn save(&mut self, _who: &DreggIdentity, _sheet: CharacterSheet) {
        // The canonical world writes through on every admitted turn. Accepting
        // a detached sheet here would reintroduce the shadow-state fork this
        // store exists to remove.
    }

    fn world(&self, who: &DreggIdentity) -> Option<Arc<WorldCell>> {
        self.world_for(who)
    }
}

struct PrivateBazaarCharacterDungeonOffering {
    dungeon: DungeonOffering,
    characters: PrivateBazaarCharacterStore,
}

impl Offering for PrivateBazaarCharacterDungeonOffering {
    type Session = DungeonSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        self.dungeon.open(cfg)
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        self.dungeon.actions(session)
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        self.dungeon.advance(session, input, actor)
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        self.dungeon.verify(session)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        self.dungeon.render(session)
    }

    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        let base = self.dungeon.render_for(session, viewer);
        self.characters
            .world_for(viewer)
            .map(|_| {
                Character::open_from_store(viewer.clone(), &self.characters)
                    .render_over(base.clone())
            })
            .unwrap_or(base)
    }

    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        self.dungeon.actions_for(session, viewer)
    }

    fn price(&self, input: &Action) -> RunCost {
        self.dungeon.price(input)
    }
}

fn character_store(
    deployment: &PrivateBazaarLiveDeployment,
    worlds: &BTreeMap<CellId, Arc<WorldCell>>,
) -> Result<PrivateBazaarCharacterStore, PrivateBazaarTargetRegistryError> {
    let mut entries = Vec::new();
    for (actor, cell) in deployment.private_target_members() {
        let world = worlds.get(&cell).ok_or_else(|| {
            PrivateBazaarTargetRegistryError::Config(
                "durable character store is missing a pinned roster world".to_owned(),
            )
        })?;
        entries.push((actor, Arc::clone(world)));
    }
    Ok(PrivateBazaarCharacterStore {
        entries: Arc::new(entries),
    })
}

fn verify_custody_pin(
    deployment: &PrivateBazaarLiveDeployment,
    custody: &dyn WorldCellSigningCustody,
) -> Result<(), PrivateBazaarTargetRegistryError> {
    if world_cell_signing_custody_pubkey(custody)? != deployment.private_executor_pubkey() {
        return Err(PrivateBazaarTargetRegistryError::Config(
            "executor signing custody does not match the deployment public-key pin".to_owned(),
        ));
    }
    Ok(())
}

fn expected_cells(
    deployment: &PrivateBazaarLiveDeployment,
) -> Result<BTreeMap<CellId, String>, PrivateBazaarTargetRegistryError> {
    let mut expected = BTreeMap::new();
    for cell in deployment.private_target_cells() {
        let directory = cell_directory_name(cell);
        if expected.insert(cell, directory).is_some() {
            return Err(PrivateBazaarTargetRegistryError::Config(
                "deployment roster contains a duplicate target cell".to_owned(),
            ));
        }
    }
    if expected.is_empty() {
        return Err(PrivateBazaarTargetRegistryError::Config(
            "deployment roster contains no target cells".to_owned(),
        ));
    }
    Ok(expected)
}

fn validate_opened_target(
    deployment: &PrivateBazaarLiveDeployment,
    expected_cell: CellId,
    world: &WorldCell,
) -> Result<(), PrivateBazaarTargetRegistryError> {
    if world.cell_id() != expected_cell
        || world.executor_pubkey() != Some(deployment.private_executor_pubkey())
        || world.federation_id() != deployment.private_executor_federation()
    {
        return Err(PrivateBazaarTargetRegistryError::Config(
            "durable target identity differs from the deployment roster or executor pin".to_owned(),
        ));
    }
    Ok(())
}

fn validate_exact_target_root(
    root: &Path,
    expected_cells: impl Iterator<Item = CellId>,
) -> Result<(), PrivateBazaarTargetRegistryError> {
    validate_private_directory(root)?;
    let expected = expected_cells
        .map(cell_directory_name)
        .collect::<BTreeSet<_>>();
    let mut found = BTreeSet::new();
    for entry in fs::read_dir(root)
        .map_err(|error| PrivateBazaarTargetRegistryError::Io(error.to_string()))?
    {
        let entry =
            entry.map_err(|error| PrivateBazaarTargetRegistryError::Io(error.to_string()))?;
        let kind = entry
            .file_type()
            .map_err(|error| PrivateBazaarTargetRegistryError::Io(error.to_string()))?;
        let name = entry.file_name().into_string().map_err(|_| {
            PrivateBazaarTargetRegistryError::Config(
                "target root contains a non-UTF-8 entry".to_owned(),
            )
        })?;
        if !kind.is_dir() || !found.insert(name) {
            return Err(PrivateBazaarTargetRegistryError::Config(
                "target root contains a non-directory or duplicate entry".to_owned(),
            ));
        }
    }
    if found != expected {
        return Err(PrivateBazaarTargetRegistryError::Config(
            "target root does not contain exactly the pinned roster".to_owned(),
        ));
    }
    Ok(())
}

fn create_private_target_root(root: &Path) -> Result<(), PrivateBazaarTargetRegistryError> {
    fs::create_dir(root).map_err(|error| {
        PrivateBazaarTargetRegistryError::Io(format!(
            "could not create a new private target root: {error}"
        ))
    })?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(root, fs::Permissions::from_mode(0o700))
            .map_err(|error| PrivateBazaarTargetRegistryError::Io(error.to_string()))?;
    }
    Ok(())
}

fn validate_private_directory(path: &Path) -> Result<(), PrivateBazaarTargetRegistryError> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| PrivateBazaarTargetRegistryError::Io(error.to_string()))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(PrivateBazaarTargetRegistryError::Config(
            "target root is not a regular directory".to_owned(),
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if metadata.permissions().mode() & 0o077 != 0 {
            return Err(PrivateBazaarTargetRegistryError::Config(
                "target root permissions are too broad".to_owned(),
            ));
        }
    }
    Ok(())
}

fn validate_custody_file(
    file: &File,
    link_metadata: &fs::Metadata,
) -> Result<(), PrivateBazaarTargetRegistryError> {
    let metadata = file
        .metadata()
        .map_err(|error| PrivateBazaarTargetRegistryError::Io(error.to_string()))?;
    if !metadata.is_file() || metadata.len() != link_metadata.len() {
        return Err(PrivateBazaarTargetRegistryError::Config(
            "executor signing custody changed while it was opened".to_owned(),
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        if metadata.dev() != link_metadata.dev()
            || metadata.ino() != link_metadata.ino()
            || metadata.nlink() != 1
            || metadata.permissions().mode() & 0o077 != 0
        {
            return Err(PrivateBazaarTargetRegistryError::Config(
                "executor signing custody identity or permissions are unsafe".to_owned(),
            ));
        }
    }
    if metadata.len() != 32 && metadata.len() != 64 {
        return Err(PrivateBazaarTargetRegistryError::Config(
            "executor signing custody must contain exactly 32 raw or 64 hex bytes".to_owned(),
        ));
    }
    Ok(())
}

fn decode_signing_seed(encoded: &[u8]) -> Result<Zeroizing<[u8; 32]>, String> {
    if encoded.len() == 32 {
        let mut seed = Zeroizing::new([0u8; 32]);
        seed.copy_from_slice(encoded);
        return Ok(seed);
    }
    if encoded.len() != 64 {
        return Err("executor signing custody has an invalid length".to_owned());
    }
    let mut seed = Zeroizing::new([0u8; 32]);
    for (index, pair) in encoded.chunks_exact(2).enumerate() {
        let high = hex_nibble(pair[0])
            .ok_or_else(|| "executor signing custody contains non-hex bytes".to_owned())?;
        let low = hex_nibble(pair[1])
            .ok_or_else(|| "executor signing custody contains non-hex bytes".to_owned())?;
        seed[index] = (high << 4) | low;
    }
    Ok(seed)
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn cell_directory_name(cell: CellId) -> String {
    let mut name = String::with_capacity(64);
    for byte in cell.0 {
        use std::fmt::Write as _;
        write!(&mut name, "{byte:02x}").expect("writing to String cannot fail");
    }
    name
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::symbol;
    use dreggnet_market::private_bazaar_journey::{
        PrivateBazaarDeploymentPin, PrivateBazaarRaidPolicy,
    };
    use dreggnet_market::private_clearing_guild_allocation::{
        GuildMember, GuildReward, GuildRoster,
    };
    use dreggnet_offerings::DreggIdentity;
    use dreggnet_offerings::SessionId;
    use dungeon_on_dregg::progression::{
        PRIVATE_BAZAAR_XP_EVENT, PRIVATE_BAZAAR_XP_METHOD, deploy_hero, gain_private_bazaar_xp,
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

    fn deployment(
        authority: &Path,
        seeds: &[u8],
        custody: &dyn WorldCellSigningCustody,
    ) -> PrivateBazaarLiveDeployment {
        let members = seeds
            .iter()
            .enumerate()
            .map(|(index, seed)| {
                GuildMember::new(
                    DreggIdentity(format!("durable-target-{index}")),
                    deploy_hero(*seed).cell_id(),
                )
            })
            .collect();
        let roster = GuildRoster::new(members).unwrap();
        let reward = GuildReward::new("raid-xp/durable-target-test/v1", 144).unwrap();
        let pin = PrivateBazaarDeploymentPin::new(
            [0x31; 32],
            roster.digest(),
            PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
            PRIVATE_BAZAAR_XP_METHOD,
            symbol(PRIVATE_BAZAAR_XP_EVENT),
            world_cell_signing_custody_pubkey(custody).unwrap(),
            deploy_hero(seeds[0]).federation_id(),
        )
        .unwrap();
        PrivateBazaarLiveDeployment::open(
            PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap(),
            1,
            authority,
        )
        .unwrap()
    }

    #[test]
    fn exact_roster_reopens_signed_state_and_continues_receipt_chain() {
        let temp = tempfile::tempdir().unwrap();
        let custody = TestCustody::new([0xA7; 32], &temp.path().join("anchor"));
        let seeds = [0x91, 0x92, 0x93];
        let deployment = deployment(&temp.path().join("authority"), &seeds, &custody);
        let registry =
            PrivateBazaarDurableTargetRegistry::provision(&deployment, &custody, &seeds).unwrap();
        assert_eq!(registry.len(), seeds.len());

        let winner = deploy_hero(seeds[2]).cell_id();
        let winner_image = deployment
            .private_target_root()
            .join(cell_directory_name(winner))
            .join("world-cell-v1.image");
        let genesis_image = fs::read(&winner_image).unwrap();
        let first = gain_private_bazaar_xp(&registry.worlds[&winner], [0x41; 32], 0, 144)
            .expect("the ordinary executor commits the first durable reward");
        drop(registry);

        let restarted = PrivateBazaarDurableTargetRegistry::load(&deployment, &custody).unwrap();
        assert_eq!(restarted.worlds[&winner].read_var("xp"), 144);
        let viewer = DreggIdentity("durable-target-2".to_owned());
        assert_eq!(restarted.character_store().load(&viewer).xp, 144);
        let mut host = OfferingHost::new();
        restarted.character_store().register_dungeon(&mut host);
        let session = SessionId::new("durable-character-canary");
        host.ensure_open("dungeon", &session).unwrap();
        let rendered = format!(
            "{:?}",
            host.render_for("dungeon", &session, &viewer)
                .expect("the canonical character dungeon renders")
                .view()
        );
        assert!(rendered.contains("XP 144"), "{rendered}");
        assert_eq!(
            restarted.worlds[&winner]
                .receipt_by_hash(first.receipt_hash())
                .unwrap()
                .receipt_hash(),
            first.receipt_hash()
        );
        let second = gain_private_bazaar_xp(&restarted.worlds[&winner], [0x42; 32], 144, 56)
            .expect("restored nonce and receipt head admit the next ordinary turn");
        assert_eq!(second.previous_receipt_hash, Some(first.receipt_hash()));
        drop(restarted);

        let restarted_again =
            PrivateBazaarDurableTargetRegistry::load(&deployment, &custody).unwrap();
        assert_eq!(restarted_again.worlds[&winner].read_var("xp"), 200);
        assert_eq!(
            restarted_again.worlds[&winner]
                .receipt_chain_snapshot()
                .len(),
            2
        );
        let runtime = deployment
            .start_private_runtime(restarted_again)
            .expect("the exact sealed durable roster starts the production runtime");
        assert_eq!(runtime.target_count(), seeds.len());
        assert_eq!(
            runtime.shutdown().unwrap().phase,
            crate::PrivateBazaarWorkerServicePhase::Stopped
        );

        // The old image remains correctly signed, framed, and deterministic,
        // but its final receipt coordinate is now below the independent
        // checkpoint anchor. Replacing only the target image cannot retcon XP.
        fs::write(&winner_image, genesis_image).unwrap();
        assert!(PrivateBazaarDurableTargetRegistry::load(&deployment, &custody).is_err());
    }

    #[test]
    fn wrong_custody_missing_target_and_tampered_image_all_refuse() {
        let temp = tempfile::tempdir().unwrap();
        let custody = TestCustody::new([0xB7; 32], &temp.path().join("anchor"));
        let seeds = [0x81, 0x82];
        let deployment = deployment(&temp.path().join("authority"), &seeds, &custody);
        let registry =
            PrivateBazaarDurableTargetRegistry::provision(&deployment, &custody, &seeds).unwrap();
        drop(registry);

        let wrong = TestCustody::new([0xB8; 32], &temp.path().join("wrong-anchor"));
        assert!(PrivateBazaarDurableTargetRegistry::load(&deployment, &wrong).is_err());

        let root = deployment.private_target_root();
        let missing_cell = deploy_hero(seeds[0]).cell_id();
        let missing_path = root.join(cell_directory_name(missing_cell));
        let held_aside = temp.path().join("held-aside-target");
        fs::rename(&missing_path, &held_aside).unwrap();
        assert!(PrivateBazaarDurableTargetRegistry::load(&deployment, &custody).is_err());
        fs::rename(&held_aside, &missing_path).unwrap();

        let image = missing_path.join("world-cell-v1.image");
        let mut bytes = fs::read(&image).unwrap();
        *bytes.last_mut().unwrap() ^= 0x01;
        fs::write(&image, bytes).unwrap();
        assert!(PrivateBazaarDurableTargetRegistry::load(&deployment, &custody).is_err());
    }

    #[test]
    fn file_custody_accepts_private_hex_and_rejects_broad_permissions() {
        use std::io::Write as _;
        #[cfg(unix)]
        use std::os::unix::fs::PermissionsExt;

        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("executor.seed");
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .unwrap();
        file.write_all(&[b'a'; 64]).unwrap();
        drop(file);
        #[cfg(unix)]
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();

        let custody =
            PrivateBazaarFileSigningCustody::open(&path, temp.path().join("anchor")).unwrap();
        assert_eq!(*custody.acquire_signing_seed().unwrap(), [0xAA; 32]);
        drop(custody);

        #[cfg(unix)]
        {
            fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
            assert!(
                PrivateBazaarFileSigningCustody::open(&path, temp.path().join("anchor-2")).is_err()
            );
        }
    }
}
