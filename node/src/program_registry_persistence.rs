//! Durable storage for caller-deployed custom cell programs.
//!
//! The program registry is node-owned verifier configuration, not turn-local
//! scratch.  Production executors are deliberately short-lived, so the node
//! keeps one canonical registry and snapshots it into each executor.  The DFA
//! route verifier does **not** use this registry; it has a separate, pinned
//! canonical-route registry in `executor_setup`.

use std::collections::HashSet;

use dregg_dsl_runtime::{CellProgram, ProgramRegistry};
use dregg_persist::PersistentStore;
use serde::{Deserialize, Serialize};

const CONFIG_KEY: &str = "deployed_cell_program_registry_v1";
const FORMAT_VERSION: u32 = 1;

#[derive(Debug, Serialize, Deserialize)]
struct DurableProgramRegistry {
    format_version: u32,
    /// Strictly ascending by `vk_hash`, making the stored bytes canonical.
    programs: Vec<CellProgram>,
}

fn canonical_programs(registry: &ProgramRegistry) -> Vec<CellProgram> {
    let mut programs: Vec<_> = registry
        .iter()
        .map(|(_, program)| program.clone())
        .collect();
    programs.sort_unstable_by_key(|program| program.vk_hash);
    programs
}

/// Persist the complete registry before publishing it to live node state.
///
/// `PersistentStore::set_config` is one redb write transaction.  Callers build
/// and validate a candidate registry, persist that candidate, and only then
/// replace `NodeStateInner::program_registry`; a failed disk write therefore
/// cannot create a live-only deployment that disappears at restart.
pub(crate) fn persist_program_registry(
    store: &PersistentStore,
    registry: &ProgramRegistry,
) -> Result<(), String> {
    let envelope = DurableProgramRegistry {
        format_version: FORMAT_VERSION,
        programs: canonical_programs(registry),
    };
    let bytes = postcard::to_allocvec(&envelope)
        .map_err(|error| format!("failed to encode deployed program registry: {error}"))?;
    store
        .set_config(CONFIG_KEY, &bytes)
        .map_err(|error| format!("failed to persist deployed program registry: {error}"))
}

/// Restore and revalidate every caller-deployed program before the node serves.
///
/// Corrupt bytes, an unknown format, a non-canonical/duplicate sequence, a
/// descriptor that no longer passes the runtime's safety validation, or a
/// descriptor/VK mismatch are store-integrity failures.  None may silently
/// degrade to an empty registry: doing so would make valid custom-program cells
/// unverifiable after restart.
pub(crate) fn load_program_registry(store: &PersistentStore) -> Result<ProgramRegistry, String> {
    let Some(bytes) = store
        .get_config(CONFIG_KEY)
        .map_err(|error| format!("failed to load deployed program registry: {error}"))?
    else {
        return Ok(ProgramRegistry::new());
    };

    let envelope: DurableProgramRegistry = postcard::from_bytes(&bytes)
        .map_err(|error| format!("deployed program registry is corrupt: {error}"))?;
    if envelope.format_version != FORMAT_VERSION {
        return Err(format!(
            "unsupported deployed program registry format {} (expected {FORMAT_VERSION})",
            envelope.format_version
        ));
    }

    let mut previous = None;
    let mut seen = HashSet::with_capacity(envelope.programs.len());
    let mut registry = ProgramRegistry::new();
    for program in envelope.programs {
        if previous.is_some_and(|prior| prior >= program.vk_hash) {
            return Err(
                "deployed program registry is not in strict canonical VK order".to_string(),
            );
        }
        if !seen.insert(program.vk_hash) {
            return Err("deployed program registry contains a duplicate VK".to_string());
        }
        previous = Some(program.vk_hash);
        registry.deploy(program).map_err(|error| {
            format!("deployed program registry contains an invalid program: {error}")
        })?;
    }
    Ok(registry)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_dsl_runtime::CellProgram;

    fn program_named(name: &str) -> CellProgram {
        let mut descriptor = crate::executor_setup::route_circuit_program()
            .descriptor
            .clone();
        descriptor.name = name.to_string();
        CellProgram::new(descriptor, 7)
    }

    #[test]
    fn durable_registry_round_trips_and_revalidates() {
        let dir = tempfile::tempdir().unwrap();
        let store = PersistentStore::open(&dir.path().join("registry.redb")).unwrap();
        let first = program_named("custom-a");
        let second = program_named("custom-b");
        let mut registry = ProgramRegistry::new();
        registry.deploy(second.clone()).unwrap();
        registry.deploy(first.clone()).unwrap();

        persist_program_registry(&store, &registry).unwrap();
        let restored = load_program_registry(&store).unwrap();

        assert_eq!(restored.len(), 2);
        assert_eq!(restored.get(&first.vk_hash).unwrap().version, 7);
        assert_eq!(restored.get(&second.vk_hash).unwrap().version, 7);
    }

    #[test]
    fn corrupt_registry_refuses_instead_of_falling_back_empty() {
        let dir = tempfile::tempdir().unwrap();
        let store = PersistentStore::open(&dir.path().join("registry.redb")).unwrap();
        store.set_config(CONFIG_KEY, b"not-postcard").unwrap();

        let error = load_program_registry(&store).unwrap_err();
        assert!(error.contains("corrupt"), "unexpected error: {error}");
    }

    #[test]
    fn persistence_bytes_are_independent_of_hashmap_iteration_order() {
        let first = program_named("custom-a");
        let second = program_named("custom-b");
        let mut left = ProgramRegistry::new();
        left.deploy(first.clone()).unwrap();
        left.deploy(second.clone()).unwrap();
        let mut right = ProgramRegistry::new();
        right.deploy(second).unwrap();
        right.deploy(first).unwrap();

        let left = postcard::to_allocvec(&DurableProgramRegistry {
            format_version: FORMAT_VERSION,
            programs: canonical_programs(&left),
        })
        .unwrap();
        let right = postcard::to_allocvec(&DurableProgramRegistry {
            format_version: FORMAT_VERSION,
            programs: canonical_programs(&right),
        })
        .unwrap();
        assert_eq!(left, right);
    }

    #[tokio::test]
    async fn node_restart_restores_deployed_programs() {
        let dir = tempfile::tempdir().unwrap();
        let program = program_named("restart-program");
        let vk = program.vk_hash;

        {
            let state = crate::state::NodeState::new(dir.path(), Vec::new()).unwrap();
            let mut node = state.write().await;
            let mut candidate = node.program_registry.clone();
            candidate.deploy(program).unwrap();
            persist_program_registry(&node.store, &candidate).unwrap();
            node.program_registry = candidate;
        }

        let restarted = crate::state::NodeState::new(dir.path(), Vec::new()).unwrap();
        assert!(restarted.read().await.program_registry.contains(&vk));
    }
}
