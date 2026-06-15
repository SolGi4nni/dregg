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
    seed_starbridge_factory_cells_with_operator(genesis, data_dir, ledger, federation_id, None)
}

/// Like [`seed_starbridge_factory_cells`], but additionally grants `operator`
/// (the node's own agent cell) an owner capability over every cell created in
/// this pass and opens that cell's `set_state` permission to `AuthRequired::None`.
///
/// This is what makes the factory-born cells *demoable from the live node's
/// `/turn/submit` ingress*, which acts as the operator. Without the cap +
/// permission, the operator could not author cross-cell `SetField` turns against
/// a cell owned by a different agent (`alice`), so the slot-caveat gating could
/// never be exercised over HTTP. The caveats (`WriteOnce` / `Monotonic` /
/// `StrictMonotonic`) still bite — opening `set_state` only authorizes *who may
/// attempt* a write; the cell program decides whether the write is *legal*.
pub fn seed_starbridge_factory_cells_with_operator(
    genesis: &serde_json::Value,
    data_dir: &Path,
    ledger: &mut Ledger,
    federation_id: [u8; 32],
    operator: Option<[u8; 32]>,
) -> StarbridgeSeedStats {
    let entries = match parse_starbridge_cells(genesis) {
        Some(entries) if !entries.is_empty() => entries,
        _ => return StarbridgeSeedStats::default(),
    };
    seed_starbridge_cells(
        &entries,
        data_dir,
        ledger,
        federation_id,
        operator,
        /* devnet_fallback */ false,
    )
}

/// Idempotent-on-boot DEVNET seeding from the built-in default starbridge cell
/// set ([`crate::genesis::default_starbridge_genesis_cells`]).
///
/// This is the backfill path for a devnet data dir that predates the
/// starbridge seed (no `genesis.json`, or one without `starbridge_cells`):
/// invoked on every boot when the node runs with `--enable-faucet` (the devnet
/// switch), it inserts the missing poll/bounty/nameservice/... cells exactly
/// like `materialize_genesis_cells` — insert-if-absent, never overwriting.
/// `devnet_fallback` additionally lets it synthesize what an old data dir
/// lacks: a missing `agent-<owner>.key` is derived deterministically (devnet
/// keys are declared non-production by `.devnet` semantics) and a missing
/// owner issuer cell is materialized with a devnet balance, both logged.
pub fn seed_default_starbridge_cells_devnet(
    data_dir: &Path,
    ledger: &mut Ledger,
    federation_id: [u8; 32],
    operator: Option<[u8; 32]>,
) -> StarbridgeSeedStats {
    let entries = crate::genesis::default_starbridge_genesis_cells();
    seed_starbridge_cells(
        &entries,
        data_dir,
        ledger,
        federation_id,
        operator,
        /* devnet_fallback */ true,
    )
}

fn seed_starbridge_cells(
    entries: &[StarbridgeGenesisCell],
    data_dir: &Path,
    ledger: &mut Ledger,
    federation_id: [u8; 32],
    operator: Option<[u8; 32]>,
    devnet_fallback: bool,
) -> StarbridgeSeedStats {
    // Derive the operator's agent cell id the same way `api.rs` (the
    // `/turn/submit` path) and `executor_setup::local_agent_cell` do, so the cap
    // we grant lands on the cell the live ingress actually acts as.
    let operator_cell =
        operator.map(|pk| CellId::derive_raw(&pk, blake3::hash(b"default").as_bytes()));

    let factory_descriptors = register_starbridge_factory_descriptors();
    let mut stats = StarbridgeSeedStats {
        registered_factories: factory_descriptors.len(),
        ..StarbridgeSeedStats::default()
    };

    let mut turn_executor = TurnExecutor::new(ComputronCosts::default());
    turn_executor.set_local_federation_id(federation_id);
    // Genesis seeding runs before the first finalized block; height 1 matches the
    // first submit path (`BlockHeightMode::Next` from attested 0).
    turn_executor.set_block_height(1);
    for descriptor in &factory_descriptors {
        turn_executor.deploy_factory(descriptor.clone());
    }

    let mut marker = load_seed_marker(data_dir);
    // Per-issuer receipt-chain head. Each issuer (owner agent) accumulates a
    // receipt chain across its seed turns; the next turn must link to the prior
    // one via `previous_receipt_hash`, or the executor rejects it with
    // `ReceiptChainMismatch`. We thread the last committed receipt hash here.
    let mut receipt_heads: BTreeMap<CellId, [u8; 32]> = BTreeMap::new();

    for entry in entries {
        match seed_one_cell(
            entry,
            data_dir,
            ledger,
            federation_id,
            &factory_descriptors,
            &mut turn_executor,
            &mut marker,
            &mut receipt_heads,
            devnet_fallback,
        ) {
            SeedOutcome::Created { cell_id } => {
                stats.created += 1;
                marker.insert(entry.label.clone(), hex_encode(&cell_id.0));
                // Grant the node operator owner-reach over the freshly-born cell
                // and open its `set_state` so the live `/turn/submit` ingress (which
                // acts as the operator) can drive caveat-gated turns against it.
                if let (Some(op_cell), Some(op_pk)) = (operator_cell, operator) {
                    grant_operator_reach(ledger, op_cell, op_pk, cell_id);
                }
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

#[allow(clippy::too_many_arguments)]
fn seed_one_cell(
    entry: &StarbridgeGenesisCell,
    data_dir: &Path,
    ledger: &mut Ledger,
    federation_id: [u8; 32],
    descriptors: &[FactoryDescriptor],
    turn_executor: &mut TurnExecutor,
    marker: &mut BTreeMap<String, String>,
    receipt_heads: &mut BTreeMap<CellId, [u8; 32]>,
    devnet_fallback: bool,
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
        None if devnet_fallback => {
            // Devnet backfill: the data dir predates the agent keys genesis
            // would have written. Derive a deterministic devnet key (same
            // pattern as the faucet's `dregg-devnet-faucet-key-v1`) and
            // persist it so the seeded cells are stable across restarts and
            // the operator can act as the owner agent later.
            match materialize_devnet_agent_key(data_dir, &entry.owner_agent) {
                Some(pk) => pk,
                None => {
                    return SeedOutcome::Skipped(format!(
                        "could not materialize devnet agent-{}.key in {}",
                        entry.owner_agent,
                        data_dir.display()
                    ));
                }
            }
        }
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
            return SeedOutcome::Skipped(format!("cannot read agent-{}.key", entry.owner_agent));
        }
    };

    let owner_cclerk = AgentCipherclerk::from_key_bytes(Zeroizing::new(owner_key));
    let app_cclerk = AppCipherclerk::new(owner_cclerk, federation_id);

    // The issuer is the owner agent's genesis-materialized cell. `materialize_
    // genesis_cells` inserts `Cell::with_balance(pubkey, [0u8;32], _)` (the
    // default `[0u8;32]` token domain), NOT the `blake3("default")` token the
    // `AppCipherclerk::cell_id()` accessor derives. Issuing from the wrong id
    // is why every starbridge cell historically seeded as "owner cell not
    // present" — derive the issuer the same way genesis does so the seed turn
    // actually finds (and is authorized by) the funded owner cell.
    let issuer_cell = CellId::derive_raw(&owner_pubkey, &[0u8; 32]);

    if ledger.get(&issuer_cell).is_none() {
        if devnet_fallback {
            // Devnet backfill: materialize the owner issuer cell the way
            // genesis `initial_cells` would have (insert-if-absent, funded
            // enough to pay the seed-turn fees).
            //
            // THE EPOCH §5: fund by ISSUER-MOVE from the deterministic
            // devnet well when it is live (the well goes further negative —
            // value stays conserved). Only a pre-epoch data dir without the
            // well falls back to the legacy ex-nihilo credit.
            const BACKFILL_FUNDING: u64 = 50_000;
            let issuer = dregg_cell::Cell::with_balance(owner_pubkey, [0u8; 32], 0);
            let _ = ledger.insert_cell(issuer);
            let well_id = crate::genesis::devnet_issuer_well_id();
            let well_debited = ledger
                .get_mut(&well_id)
                .map(|w| w.state.well_debit_balance(BACKFILL_FUNDING))
                .unwrap_or(false);
            if let Some(c) = ledger.get_mut(&issuer_cell) {
                let _ = c.state.credit_balance(BACKFILL_FUNDING);
            }
            if !well_debited {
                tracing::warn!(
                    owner = %entry.owner_agent,
                    "devnet backfill funded ex nihilo (issuer well not in ledger) — pre-epoch data dir"
                );
            }
            info!(
                owner = %entry.owner_agent,
                cell_id = %hex_encode(&issuer_cell.0),
                "devnet backfill: materialized owner issuer cell for starbridge seeding"
            );
        } else {
            return SeedOutcome::Skipped(format!(
                "owner agent '{}' cell not present in ledger; run genesis initial_cells first",
                entry.owner_agent
            ));
        }
    }

    // Synthesize the minimal `initial_fields` that satisfy the descriptor's
    // creation-time `field_constraints` (NonZero/Range/Equality). Without this
    // every descriptor that declares such a constraint fails birth with
    // "field N constraint violated" — the cell is born empty and the
    // constraint validates against `params.initial_fields`. Seeding a satisfying
    // placeholder (the app's first real turn then writes the true value, gated
    // by the perpetual `state_constraints`) is what lets the genesis cells
    // materialize at all.
    let initial_fields = synth_initial_fields(&descriptor.field_constraints);

    let params = FactoryCreationParams {
        mode: descriptor.default_mode.clone(),
        program_vk: program_vk_for_descriptor(descriptor),
        initial_fields,
        initial_caps: vec![],
        owner_pubkey,
    };

    let mut turn = app_cclerk
        .shared_cipherclerk()
        .read()
        .unwrap()
        .create_from_factory(
            issuer_cell,
            factory_vk,
            owner_pubkey,
            token_id,
            params,
            &federation_id,
        );
    turn.fee = 2_000;
    turn.nonce = ledger
        .get(&issuer_cell)
        .map(|c| c.state.nonce())
        .unwrap_or(0);
    // Link to the issuer's prior seed receipt (if any) so the executor's
    // per-agent receipt chain validates. The first turn from this issuer carries
    // `None` (genesis chain head); each subsequent one links to the last commit.
    turn.previous_receipt_hash = receipt_heads.get(&issuer_cell).copied();

    match turn_executor.execute(&turn, ledger) {
        TurnResult::Committed { receipt, .. } => {
            receipt_heads.insert(issuer_cell, receipt.receipt_hash());
            SeedOutcome::Created {
                cell_id: expected_cell_id,
            }
        }
        TurnResult::Rejected { reason, .. } => SeedOutcome::Failed(reason.to_string()),
        TurnResult::Expired => SeedOutcome::Failed("turn expired".into()),
        TurnResult::Pending => SeedOutcome::Failed("turn pending".into()),
    }
}

/// Synthesize the minimal `(field_index, value)` initial-field list that
/// satisfies a descriptor's creation-time `field_constraints`:
/// `NonZero` → 1, `Range { min, .. }` → max(min, 1), `Equality { value, .. }`
/// → the required value. The value chosen for `NonZero` is just a non-zero
/// placeholder; the app's first turn overwrites it with the real (hashed)
/// value under the cell program's perpetual caveats.
fn synth_initial_fields(constraints: &[dregg_cell::FieldConstraint]) -> Vec<(u32, u64)> {
    use dregg_cell::FieldConstraint;
    let mut fields: BTreeMap<u32, u64> = BTreeMap::new();
    for c in constraints {
        match c {
            FieldConstraint::NonZero { field_index } => {
                fields.entry(*field_index).or_insert(1);
            }
            FieldConstraint::Range {
                field_index, min, ..
            } => {
                fields.insert(*field_index, (*min).max(1));
            }
            FieldConstraint::Equality { field_index, value } => {
                fields.insert(*field_index, *value);
            }
        }
    }
    fields.into_iter().collect()
}

/// Grant `operator` an owner capability over `target` and open `target`'s
/// `set_state` permission so the operator may author cross-cell `SetField`
/// turns against it. The cell's `CellProgram` slot caveats still gate whether
/// each write is *legal*.
fn grant_operator_reach(
    ledger: &mut Ledger,
    operator: CellId,
    operator_pubkey: [u8; 32],
    target: CellId,
) {
    if let Some(cell) = ledger.get_mut(&target) {
        cell.permissions.set_state = dregg_cell::AuthRequired::None;
    }
    // The operator agent cell is materialized lazily (on its first faucet/turn),
    // so at boot it may not yet exist. Insert it (zero balance — the operator
    // funds it via the faucet before driving turns) so the cap grant lands.
    if ledger.get(&operator).is_none() {
        let default_token = *blake3::hash(b"default").as_bytes();
        let op_cell = dregg_cell::Cell::with_balance(operator_pubkey, default_token, 0);
        let _ = ledger.insert_cell(op_cell);
    }
    if let Some(op_cell) = ledger.get_mut(&operator) {
        op_cell
            .capabilities
            .grant(target, dregg_cell::AuthRequired::None);
    }
}

/// Register all starbridge-apps on an ephemeral [`StarbridgeAppContext`] and
/// return the deployed descriptors.
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
    starbridge_privacy_voting::register(&ctx);
    starbridge_bounty_board::register(&ctx);
    // The storage-template CapInbox factory (mailbox organ) registers through
    // the same StarbridgeAppContext mount as the apps above, so its descriptor
    // deploys and its genesis cell births via the identical machinery.
    dregg_storage_templates::cap_inbox::register(&ctx);

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

/// Derive + persist a deterministic devnet agent key (`agent-<name>.key`).
/// Returns the public key. Devnet-only (the `.devnet`/`--enable-faucet`
/// contract already declares these keys non-production-grade); deterministic
/// derivation keeps the seeded cell ids stable across data dirs and restarts.
fn materialize_devnet_agent_key(data_dir: &Path, agent: &str) -> Option<[u8; 32]> {
    let secret = blake3::derive_key("dregg-devnet-agent-key-v1", agent.as_bytes());
    let path = data_dir.join(format!("agent-{agent}.key"));
    if let Err(e) = std::fs::write(&path, secret) {
        warn!(error = %e, path = %path.display(), "failed to write devnet agent key");
        return None;
    }
    info!(
        agent = %agent,
        path = %path.display(),
        "devnet backfill: materialized deterministic agent key (NOT production-grade)"
    );
    let signing = ed25519_dalek::SigningKey::from_bytes(&secret);
    Some(signing.verifying_key().to_bytes())
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
        assert_eq!(parsed.len(), 10);
        assert_eq!(parsed[0].label, "nameservice-registry");
    }

    #[test]
    fn register_starbridge_factory_descriptors_covers_all_apps() {
        // Six single-factory apps + privacy-voting (poll + ballot = 2) +
        // bounty-board (1) + the storage-template cap-inbox factory (1)
        // = 10 factory descriptors.
        let descriptors = register_starbridge_factory_descriptors();
        assert_eq!(descriptors.len(), 10);
        assert!(
            descriptors
                .iter()
                .any(|d| d.factory_vk == dregg_storage_templates::cap_inbox::CAP_INBOX_FACTORY_VK),
            "cap-inbox factory descriptor must be registered for boot seeding"
        );
    }
}
