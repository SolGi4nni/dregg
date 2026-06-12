//! Blocklace-aware [`TurnExecutor`] configuration shared across node entry points.
//!
//! Keeps federation id, wall-clock timestamp, and attested block height aligned with
//! the same rules as [`crate::blocklace_sync::execute_finalized_turn`].

use dregg_turn::TurnExecutor;

use crate::state::NodeStateInner;

/// How to derive the executor's block height from node state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockHeightMode {
    /// Use the latest attested root height (read-only / verify paths).
    Current,
    /// Use `latest + 1` — the height assigned to the turn about to execute.
    Next,
}

/// Resolve the blocklace-attested height from persistent store + solo fallback.
pub fn attested_block_height(s: &NodeStateInner) -> u64 {
    let store_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let solo_height = s
        .solo_consensus
        .as_ref()
        .map(|solo| solo.height)
        .unwrap_or(0);
    store_height.max(solo_height)
}

/// Federation id for turn signing — matches blocklace finalized-turn path.
pub fn federation_id_for_executor(s: &NodeStateInner) -> [u8; 32] {
    if s.federation_configured {
        s.federation_id
    } else {
        *blake3::hash(s.cclerk.public_key().as_bytes()).as_bytes()
    }
}

fn wall_clock_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

/// Configure `executor` with federation id, timestamp, and blocklace height.
pub fn configure_turn_executor(
    executor: &mut TurnExecutor,
    s: &NodeStateInner,
    height_mode: BlockHeightMode,
) {
    executor.set_local_federation_id(federation_id_for_executor(s));
    executor.set_timestamp(wall_clock_secs());
    // Sign committed receipts with the node's key (same key the MCP entry
    // points use). Without this, every HTTP/blocklace-path receipt carried
    // `executor_signature: None` (`executor_signed:false` in /api/receipts) and
    // conditional-turn verification of our receipts was impossible.
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());

    // ORGANS §5 (adjudication): install the court's `validEquivocation`
    // predicate atom into the executor's witnessed-predicate registry, so
    // turn admission / cell programs can gate on a verified fork exhibit
    // (CONSENSUS-FLEX §7 item 2, live on every node executor).
    if let Some(registry) = executor.witnessed_registry.as_mut() {
        dregg_federation::court::register_equivocation_court(registry);
    }

    // THE EPOCH §5 (signed wells): wire the genesis-declared wells so fees
    // are MOVES to the fee well and Burn is a MOVE to the asset's issuer
    // well — every committed turn conserves exactly
    // (`reachable_total_zero`'s hypotheses hold on the deployed chain).
    if let Some(fee_well) = s.fee_well {
        executor.set_fee_well_cell(fee_well);
    }
    for (token_id, well) in &s.issuer_wells {
        executor.register_issuer_well(*token_id, *well);
    }

    let base = attested_block_height(s);
    let height = match height_mode {
        BlockHeightMode::Current => base,
        BlockHeightMode::Next => base.saturating_add(1),
    };
    executor.set_block_height(height);
}

/// The node's OWN agent cell — `derive_raw(cipherclerk pubkey, blake3("default"))`. This is the
/// agent whose receipt chain the cipherclerk maintains authoritatively (the source of the
/// host-fed `stored_head` for the boundary-P1 admission shadow). Mirrors the derivation in
/// `api.rs` (the submit path), centralised so the blocklace-finalized path agrees.
pub fn local_agent_cell(s: &NodeStateInner) -> dregg_cell::CellId {
    let default_token_id = *blake3::hash(b"default").as_bytes();
    dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &default_token_id)
}

/// Build a fresh executor configured for turn submission (height = attested + 1).
pub fn new_submit_executor(s: &NodeStateInner) -> TurnExecutor {
    let mut executor = TurnExecutor::new(dregg_turn::ComputronCosts::default());
    configure_turn_executor(&mut executor, s, BlockHeightMode::Next);
    executor
}

/// Build a fresh executor at the current attested height (verify / read paths).
pub fn new_verify_executor(s: &NodeStateInner) -> TurnExecutor {
    let mut executor = TurnExecutor::new(dregg_turn::ComputronCosts::default());
    configure_turn_executor(&mut executor, s, BlockHeightMode::Current);
    executor
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn height_mode_next_increments() {
        let base = 41u64;
        let next = match BlockHeightMode::Next {
            BlockHeightMode::Next => base.saturating_add(1),
            BlockHeightMode::Current => base,
        };
        assert_eq!(next, 42);
    }
}
