//! Boot-time seeding of starbridge factory cells from genesis configuration.
//!
//! After `materialize_genesis_cells` loads faucet + demo agent balances,
//! this module:
//! 1. Registers all six starbridge-app factory descriptors (via
//!    [`StarbridgeAppContext`] + [`EmbeddedExecutor`], matching the
//!    `teasting/tests/cross_app_mandate_storage_e2e.rs` pattern).
//! 2. Deploys those descriptors into a [`TurnExecutor`] bound to the node's
//!    live ledger.
//! 3. For each `genesis.starbridge_cells` entry, calls
//!    [`AppCipherclerk::create_from_factory`] as the configured owner agent
//!    (typically `alice`) when the target cell is not already present.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, StarbridgeAppContext,
};
use dregg_cell::factory::{ChildVkStrategy, FactoryCreationParams, FactoryDescriptor};
use dregg_cell::{CellId, Ledger};
use dregg_turn::{ComputronCosts, TurnExecutor, TurnResult};
use tracing::{info, warn};
use zeroize::Zeroizing;

use crate::genesis::StarbridgeGenesisCell;

const SEED_MARKER_FILE: &str = "starbridge-seed.json";
const TOKEN_DOMAIN_SALT: &str = "dregg-starbridge-genesis-token-v1";

/// Outcome counters for a seeding pass.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct StarbridgeSeedStats {
    pub registered_factories: usize,
    pub created: usize,
    pub existing: usize,
    pub skipped: usize,
    pub failed: usize,
}

impl StarbridgeSeedStats {
    pub fn total(&self) -> usize {
        self.created + self.existing + self.skipped + self.failed
    }
}

/// Seed starbridge factory cells declared in `genesis.json`.
///
/// No-op when `starbridge_cells` is absent or empty. Safe to call on every
/// boot: already-present cells (ledger or marker file) are skipped.
pub fn seed_starbridge_factory_cells(
    genesis: &serde_json::Value,
    data_dir: &Path,
    ledger: &mut Ledger,
    federation_id: [u8; 32],
) -> StarbridgeSeedStats {
    let entries = match parse_starbridge_cells(genesis) {
        Some(entries) if !entries.is_empty() => entries,
        _ => return StarbridgeSeedStats::default(),
    };

    let factory_descriptors = register_starbridge_factory_descriptors();
    let mut stats = StarbridgeSeedStats {
        registered_factories: factory_descriptors.len(),
        ..StarbridgeSeedStats::default()
    };

    let mut turn_executor = TurnExecutor::new(ComputronCosts::default());
    turn_executor.set_local_federation_id(federation_id);
    for descriptor in &factory_descriptors {
        turn_executor.deploy_factory(descriptor.clone());
    }

    let mut marker = load_seed_marker(data_dir);

    for entry in entries {
        match seed_one_cell(
            &entry,
            data_dir,
            ledger,
            federation_id,
            &factory_descriptors,
            &mut turn_executor,
            &mut marker,
        ) {
            SeedOutcome::Created { cell_id } => {
                stats.created += 1;
                marker.insert(entry.label.clone(), hex_encode(&cell_id.0));
                info!(
                    label = %entry.label,
                    cell_id = %hex_encode(&cell_id.0),
                    factory_vk = %entry.factory_vk_hex,
                    "seeded starbridge factory cell"
                );
            }
            SeedOutcome::Existing => {
                stats.existing += 1;
                info!(label = %entry.label, "starbridge factory cell already present");
            }
            SeedOutcome::Skipped(reason) => {
                stats.skipped += 1;
                warn!(label = %entry.label, reason = %reason, "skipped starbridge factory cell");
            }
            SeedOutcome::Failed(reason) => {
                stats.failed += 1;
                warn!(label = %entry.label, reason = %reason, "failed to seed starbridge factory cell");
            }
        }
    }

    if stats.created > 0 {
        if let Err(e) = save_seed_marker(data_dir, &marker) {
            warn!(error = %e, "failed to persist starbridge seed marker");
        }
    }

    if stats.total() > 0 {
        info!(
            registered = stats.registered_factories,
            created = stats.created,
            existing = stats.existing,
            skipped = stats.skipped,
            failed = stats.failed,
            "starbridge factory seeding complete"
        );
    }

    stats
}

enum SeedOutcome {
    Created { cell_id: CellId },
    Existing,
    Skipped(String),
    Failed(String),
}

fn seed_one_cell(
    entry: &StarbridgeGenesisCell,
    data_dir: &Path,
    ledger: &mut Ledger,
    federation_id: [u8; 32],
    descriptors: &[FactoryDescriptor],
    turn_executor: &mut TurnExecutor,
    marker: &mut BTreeMap<String, String>,
) -> SeedOutcome {
    let factory_vk = match hex_decode_32(&entry.factory_vk_hex) {
        Some(vk) => vk,
        None => {
            return SeedOutcome::Skipped(format!(
                "malformed factory_vk_hex: {}",
                entry.factory_vk_hex
            ));
        }
    };

    let descriptor = match descriptors.iter().find(|d| d.factory_vk == factory_vk) {
        Some(d) => d,
        None => {
            return SeedOutcome::Skipped(format!(
                "factory VK {} not registered",
                entry.factory_vk_hex
            ));
        }
    };

    let owner_pubkey = match load_agent_public_key(data_dir, &entry.owner_agent) {
        Some(pk) => pk,
        None => {
            return SeedOutcome::Skipped(format!(
                "missing agent-{}.key in {}",
                entry.owner_agent,
                data_dir.display()
            ));
        }
    };

    let token_id = token_id_from_uri_hint(&entry.uri_hint);
    let expected_cell_id = CellId::derive_raw(&owner_pubkey, &token_id);

    if ledger.get(&expected_cell_id).is_some() {
        marker.insert(entry.label.clone(), hex_encode(&expected_cell_id.0));
        return SeedOutcome::Existing;
    }

    if marker.get(&entry.label).is_some_and(|id| {
        hex_decode_32(id)
            .map(|bytes| CellId(bytes) == expected_cell_id)
            .unwrap_or(false)
    }) {
        return SeedOutcome::Existing;
    }

    let owner_key = match load_agent_secret_key(data_dir, &entry.owner_agent) {
        Some(key) => key,
        None => {
            return SeedOutcome::Skipped(format!(
                "cannot read agent-{}.key",
                entry.owner_agent
            ));
        }
    };

    let owner_cclerk = AgentCipherclerk::from_key_bytes(Zeroizing::new(owner_key));
    let app_cclerk = AppCipherclerk::new(owner_cclerk, federation_id);

    if ledger.get(&app_cclerk.cell_id()).is_none() {
        return SeedOutcome::Skipped(format!(
            "owner agent '{}' cell not present in ledger; run genesis initial_cells first",
            entry.owner_agent
        ));
    }

    let params = FactoryCreationParams {
        mode: descriptor.default_mode.clone(),
        program_vk: program_vk_for_descriptor(descriptor),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey,
    };

    let mut turn = app_cclerk.create_from_factory(factory_vk, owner_pubkey, token_id, params);
    turn.fee = 10_000;
    turn.nonce = 0;

    match turn_executor.execute(&turn, ledger) {
        TurnResult::Committed { .. } => SeedOutcome::Created {
            cell_id: expected_cell_id,
        },
        TurnResult::Rejected { reason, .. } => SeedOutcome::Failed(reason.to_string()),
        TurnResult::Expired => SeedOutcome::Failed("turn expired".into()),
        TurnResult::Pending => SeedOutcome::Failed("turn pending".into()),
    }
}

/// Register all six starbridge-apps on an ephemeral
/// [`StarbridgeAppContext`] and return the deployed descriptors.
fn register_starbridge_factory_descriptors() -> Vec<FactoryDescriptor> {
    let bootstrap = AgentCipherclerk::new();
    let app_cclerk = AppCipherclerk::new(bootstrap, [0u8; 32]);
    let embedded = EmbeddedExecutor::new(&app_cclerk, "default");
    let ctx = StarbridgeAppContext::new(app_cclerk, embedded);

    starbridge_nameservice::register(&ctx);
    starbridge_identity::register(&ctx);
    starbridge_subscription::register(&ctx);
    starbridge_governed_namespace::register(&ctx);
    starbridge_compartment_workflow_mandate::register(&ctx);
    starbridge_storage_gateway_mandate::register(&ctx);

    ctx.factory_registry().descriptors()
}

fn program_vk_for_descriptor(descriptor: &FactoryDescriptor) -> Option<[u8; 32]> {
    match &descriptor.child_vk_strategy {
        Some(ChildVkStrategy::Fixed(vk)) => *vk,
        _ => descriptor.child_program_vk,
    }
}

fn token_id_from_uri_hint(uri_hint: &str) -> [u8; 32] {
    blake3::derive_key(TOKEN_DOMAIN_SALT, uri_hint.as_bytes())
}

fn parse_starbridge_cells(genesis: &serde_json::Value) -> Option<Vec<StarbridgeGenesisCell>> {
    serde_json::from_value(genesis["starbridge_cells"].clone()).ok()
}

fn load_seed_marker(data_dir: &Path) -> BTreeMap<String, String> {
    let path = marker_path(data_dir);
    let Ok(text) = std::fs::read_to_string(&path) else {
        return BTreeMap::new();
    };
    serde_json::from_str(&text).unwrap_or_default()
}

fn save_seed_marker(data_dir: &Path, marker: &BTreeMap<String, String>) -> std::io::Result<()> {
    let path = marker_path(data_dir);
    let json = serde_json::to_string_pretty(marker)?;
    std::fs::write(path, json)
}

fn marker_path(data_dir: &Path) -> PathBuf {
    data_dir.join(SEED_MARKER_FILE)
}

fn load_agent_secret_key(data_dir: &Path, agent: &str) -> Option<[u8; 32]> {
    let bytes = std::fs::read(data_dir.join(format!("agent-{agent}.key"))).ok()?;
    if bytes.len() < 32 {
        return None;
    }
    let mut key = [0u8; 32];
    key.copy_from_slice(&bytes[..32]);
    Some(key)
}

fn load_agent_public_key(data_dir: &Path, agent: &str) -> Option<[u8; 32]> {
    let key = load_agent_secret_key(data_dir, agent)?;
    let signing = ed25519_dalek::SigningKey::from_bytes(&key);
    Some(signing.verifying_key().to_bytes())
}

fn hex_decode_32(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(bytes)
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::genesis::default_starbridge_genesis_cells;

    #[test]
    fn seed_marker_round_trip() {
        let dir = tempfile::tempdir().expect("tempdir");
        let mut marker = BTreeMap::new();
        marker.insert("nameservice-registry".into(), "aa".repeat(32));
        save_seed_marker(dir.path(), &marker).expect("write marker");
        let loaded = load_seed_marker(dir.path());
        assert_eq!(loaded.get("nameservice-registry").unwrap().len(), 64);
    }

    #[test]
    fn parse_starbridge_cells_from_genesis_json() {
        let cells = default_starbridge_genesis_cells();
        let genesis = serde_json::json!({ "starbridge_cells": cells });
        let parsed = parse_starbridge_cells(&genesis).expect("parse cells");
        assert_eq!(parsed.len(), 6);
        assert_eq!(parsed[0].label, "nameservice-registry");
    }

    #[test]
    fn register_starbridge_factory_descriptors_covers_six_apps() {
        let descriptors = register_starbridge_factory_descriptors();
        assert_eq!(descriptors.len(), 6);
    }
}