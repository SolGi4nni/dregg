//! # kvstore — the deos-native surface (the STORE as a composed [`DeosApp`]).
//!
//! The second axis of a modern starbridge-app: the same verified store
//! ([`crate::store_program`]) re-expressed as a composed [`DeosApp`] — per-viewer
//! projection, web-of-cells publish (the store cell IS a `dregg://` sturdyref), the
//! rehydratable frustum-snapshot, the generated `<dregg-affordance-surface>`
//! component, and the manifest. The framework wires the rest; this module owns the
//! composition.
//!
//! The store cell is the agent's OWN cell ([`AppCipherclerk::cell_id`]) so fires
//! execute against the seeded embedded ledger. The SAME [`crate::store_program`]
//! that backs the service-cell axis is installed here ([`seed_store`]) and
//! re-enforced by the executor on every touching turn — so the
//! [`StateConstraint::Monotonic`](dregg_app_framework::StateConstraint) on
//! [`crate::VERSION_SLOT`] (rollback-proof) bites in the deos fire path too.

use dregg_app_framework::{
    AppCipherclerk, AuthRequired, CellAffordance, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FieldElement, FireExecuteError, StarbridgeAppContext, TurnReceipt, field_from_u64,
    symbol,
};
use dregg_types::CellId;

// =============================================================================
// Rights tiers — the reader ⊂ writer attenuation ladder
// =============================================================================

/// The READER rights tier ([`AuthRequired::Signature`]) — the narrow read tier: a
/// reader can `view` the store (read the live version) and nothing else. The store
/// cell is published at this tier (an indexer on another federation reacquires the
/// store's version across the membrane).
pub const READER_RIGHTS: AuthRequired = AuthRequired::Signature;

/// The WRITER rights tier ([`AuthRequired::Either`] — sig-or-proof) — a writer can
/// `put`/`delete` (mutate a register + bump the version) AND read. So
/// `Signature ⊂ Either` IS the reader ⊂ writer ladder.
pub const WRITER_RIGHTS: AuthRequired = AuthRequired::Either;

// =============================================================================
// The deos-native surface — the STORE as a composed `DeosApp`
// =============================================================================

/// **The kvstore STORE as a composed [`DeosApp`]** — the register store on the deos
/// bones. The store cell is the agent's OWN cell ([`AppCipherclerk::cell_id`]) so
/// fires execute against the seeded embedded ledger.
///
/// Three cap-only affordances on the STORE cell, on the reader ⊂ writer ladder:
///
///   - `view` — a READER reads the live store (cap-only, `Signature`): an
///     `EmitEvent("kvstore-read")`;
///   - `put` — a WRITER writes a register (cap-only, `Either`): the decisive effect
///     is a `SetField` on [`crate::REG_MIN`]; the real fire ([`fire_put`]) submits
///     the FULL two-effect turn (bump `VERSION` + write the register), re-enforced
///     by the executor's installed [`crate::store_program`]
///     (`Monotonic(VERSION)` bites);
///   - `delete` — a WRITER clears a register (cap-only, `Either`): the decisive
///     effect is a `SetField` on [`crate::REG_MIN`]; the real fire
///     ([`fire_delete`]) submits the FULL two-effect turn (bump `VERSION` + zero the
///     register).
///
/// The store cell is published into the web-of-cells at the reader tier and is
/// discoverable under `kvstore` / `registers`. Seed the cell's program with
/// [`seed_store`] so the executor re-enforces the rollback-proof invariant.
pub fn kvstore_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let store = cipherclerk.cell_id();

    // `view` — a READER reads the live store version. Cap-only.
    let view = CellAffordance::new(
        "view",
        READER_RIGHTS,
        Effect::EmitEvent {
            cell: store,
            event: Event::new(symbol("kvstore-read"), vec![]),
        },
    );
    // `put` — a WRITER writes a register. The decisive effect (the surface
    // representative) is the register write; the real fire ([`fire_put`]) submits the
    // FULL two-effect turn (bump VERSION + write the register).
    let put = CellAffordance::new(
        "put",
        WRITER_RIGHTS,
        Effect::SetField {
            cell: store,
            index: crate::REG_MIN,
            value: field_from_u64(0),
        },
    );
    // `delete` — a WRITER clears a register. The decisive effect is the register
    // clear; the real fire ([`fire_delete`]) submits the FULL two-effect turn (bump
    // VERSION + zero the register).
    let delete = CellAffordance::new(
        "delete",
        WRITER_RIGHTS,
        Effect::SetField {
            cell: store,
            index: crate::REG_MIN,
            value: field_from_u64(0),
        },
    );

    DeosApp::builder("kvstore", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["kvstore".into(), "registers".into()])
        .cell(
            DeosCell::new(store, "store")
                .affordance(view)
                .affordance(put)
                .affordance(delete)
                .publish(READER_RIGHTS),
        )
        .build()
}

/// **Seed the STORE cell** so the deos fires have live state + the
/// rollback-proof invariant bites: install the [`crate::store_program`] on the
/// agent's own cell (so the executor re-enforces `Monotonic(VERSION)` on every
/// touching turn). A born cell's fields are already zero, so `VERSION` starts at 0
/// — the real `(old, new)` baseline against which the first `put` bumps to 1.
pub fn seed_store(executor: &EmbeddedExecutor) {
    executor.install_program(executor.cell_id(), crate::store_program());
}

/// Read a `u64` out of a [`FieldElement`] (the last 8 big-endian bytes) — the
/// inverse of [`field_from_u64`]. Used to read the live store version off the cell.
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(buf)
}

/// Read the `u64` at `slot` off `cell` (defaulting to 0 if the cell is absent or
/// the slot is unset). The shared reader behind [`live_version`] / [`live_count`].
fn live_field_u64(cell: CellId, slot: usize, executor: &EmbeddedExecutor) -> u64 {
    executor
        .cell_state(cell)
        .and_then(|s| s.get_field(slot).copied())
        .map(|f| field_to_u64(&f))
        .unwrap_or(0)
}

/// Read the live store version off `cell` (defaulting to 0 if the cell is absent or
/// the slot is unset).
fn live_version(cell: CellId, executor: &EmbeddedExecutor) -> u64 {
    live_field_u64(cell, crate::VERSION_SLOT, executor)
}

/// Read the live entry count off `cell` (the number of occupied registers).
fn live_count(cell: CellId, executor: &EmbeddedExecutor) -> u64 {
    live_field_u64(cell, crate::COUNT_SLOT, executor)
}

/// Is register `reg` currently occupied (non-zero) on `cell`? A `put` to a free
/// register raises the entry count; a `put` overwriting an occupied one leaves it
/// unchanged; a `delete` of an occupied one lowers it. The whole lifecycle's
/// entry-count truth turns on this read.
fn register_occupied(cell: CellId, reg: usize, executor: &EmbeddedExecutor) -> bool {
    executor
        .cell_state(cell)
        .and_then(|s| s.get_field(reg).copied())
        .map(|f| f != [0u8; 32])
        .unwrap_or(false)
}

/// **Fire `put`** — write `value` into register `reg`, bump the store version, and
/// maintain the live header (entry count + last key/value).
///
/// Reads the live state off the cell and builds the FULL turn:
///   - `SetField(VERSION = version + 1)` — the rollback-proof bump;
///   - `SetField(COUNT = count + 1)` IF `reg` was free, else `COUNT` holds
///     (overwriting an occupied register is not a new entry);
///   - `SetField(LAST_KEY = reg)` + `SetField(LAST_VALUE = value)` — the header;
///   - `SetField(reg = value)` — the register write itself.
///
/// Submitted via [`AppCipherclerk::make_action`] through the executor, which
/// re-enforces the installed [`crate::store_program`] (`Monotonic(VERSION)` — a
/// rollback is a real refusal — and the [`crate::COUNT_SLOT`] capacity tooth).
/// Seed with [`seed_store`] first.
pub fn fire_put(
    cell: CellId,
    reg: usize,
    value: FieldElement,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let new_version = live_version(cell, executor) + 1;
    // A fresh register is a new entry; an overwrite is not.
    let new_count = live_count(cell, executor) + u64::from(!register_occupied(cell, reg, executor));
    let effects = vec![
        Effect::SetField {
            cell,
            index: crate::VERSION_SLOT,
            value: field_from_u64(new_version),
        },
        Effect::SetField {
            cell,
            index: crate::COUNT_SLOT,
            value: field_from_u64(new_count),
        },
        Effect::SetField {
            cell,
            index: crate::LAST_KEY_SLOT,
            value: field_from_u64(reg as u64),
        },
        Effect::SetField {
            cell,
            index: crate::LAST_VALUE_SLOT,
            value,
        },
        Effect::SetField {
            cell,
            index: reg,
            value,
        },
    ];
    let action = cipherclerk.make_action(cell, "put", effects);
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// **Fire `delete`** — clear register `reg` (write zero), bump the store version,
/// and maintain the live header.
///
/// Same shape as [`fire_put`], with a zero value: `COUNT` drops by one IF `reg`
/// was occupied (deleting an absent key is a no-op on the count), `LAST_KEY = reg`,
/// `LAST_VALUE = 0`. Seed with [`seed_store`] first.
pub fn fire_delete(
    cell: CellId,
    reg: usize,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let new_version = live_version(cell, executor) + 1;
    // Clearing an occupied register removes an entry; clearing a free one does not.
    let new_count = live_count(cell, executor)
        .saturating_sub(u64::from(register_occupied(cell, reg, executor)));
    let effects = vec![
        Effect::SetField {
            cell,
            index: crate::VERSION_SLOT,
            value: field_from_u64(new_version),
        },
        Effect::SetField {
            cell,
            index: crate::COUNT_SLOT,
            value: field_from_u64(new_count),
        },
        Effect::SetField {
            cell,
            index: crate::LAST_KEY_SLOT,
            value: field_from_u64(reg as u64),
        },
        Effect::SetField {
            cell,
            index: crate::LAST_VALUE_SLOT,
            value: [0u8; 32],
        },
        Effect::SetField {
            cell,
            index: reg,
            value: [0u8; 32],
        },
    ];
    let action = cipherclerk.make_action(cell, "delete", effects);
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// **Mount the deos-native surface** ([`kvstore_app`]) on a shared context: build
/// the composed [`DeosApp`] from the context's cipherclerk + executor, seed the
/// store cell's program (so the deos fires bite), and fold the app into the
/// context's affordance registry ([`DeosApp::register`]). Returns the live
/// [`DeosApp`] (so a host can also `DeosApp::mount` its axum router /
/// `DeosApp::publish_all` into the web-of-cells).
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = kvstore_app(ctx.cipherclerk(), ctx.executor());
    seed_store(ctx.executor());
    app.register(ctx);
    app
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [9u8; 32])
    }

    #[test]
    fn the_store_cell_exposes_the_three_affordances() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        seed_store(&exec);
        let app = kvstore_app(&cclerk, &exec);

        assert_eq!(app.cells().len(), 1);
        let names: Vec<&str> = app.cells()[0]
            .surface()
            .affordances
            .iter()
            .map(|a| a.name.as_str())
            .collect();
        assert!(names.contains(&"view"), "view affordance present");
        assert!(names.contains(&"put"), "put affordance present");
        assert!(names.contains(&"delete"), "delete affordance present");
    }

    #[test]
    fn fire_put_commits_and_bumps_the_version_to_one() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        seed_store(&exec);
        let store = cclerk.cell_id();

        // Version starts at 0 on the born cell.
        assert_eq!(live_version(store, &exec), 0);

        fire_put(store, crate::REG_MIN, [7u8; 32], &cclerk, &exec).expect("put commits");

        // The committed turn bumped VERSION to 1.
        assert_eq!(live_version(store, &exec), 1);
        let val = exec
            .cell_state(store)
            .and_then(|s| s.get_field(crate::REG_MIN).copied())
            .expect("register written");
        assert_eq!(val, [7u8; 32]);
    }

    #[test]
    fn the_entry_count_tracks_puts_overwrites_and_deletes() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        seed_store(&exec);
        let store = cclerk.cell_id();

        // A born store has zero entries.
        assert_eq!(live_count(store, &exec), 0);

        // Two puts to DISTINCT keys → two entries.
        fire_put(store, crate::REG_MIN, [1u8; 32], &cclerk, &exec).expect("put k0");
        assert_eq!(live_count(store, &exec), 1);
        fire_put(store, crate::REG_MIN + 1, [2u8; 32], &cclerk, &exec).expect("put k1");
        assert_eq!(live_count(store, &exec), 2);

        // Overwriting an existing key does NOT raise the count, but DOES bump the
        // version + record the header.
        fire_put(store, crate::REG_MIN, [9u8; 32], &cclerk, &exec).expect("overwrite k0");
        assert_eq!(
            live_count(store, &exec),
            2,
            "an overwrite is not a new entry"
        );

        let st = exec.cell_state(store).unwrap();
        assert_eq!(
            st.get_field(crate::LAST_KEY_SLOT).copied(),
            Some(field_from_u64(crate::REG_MIN as u64))
        );
        assert_eq!(
            st.get_field(crate::LAST_VALUE_SLOT).copied(),
            Some([9u8; 32])
        );

        // Deleting a present key lowers the count; deleting an absent key is a no-op
        // on the count.
        fire_delete(store, crate::REG_MIN, &cclerk, &exec).expect("delete k0");
        assert_eq!(live_count(store, &exec), 1);
        fire_delete(store, crate::REG_MAX, &cclerk, &exec).expect("delete absent key");
        assert_eq!(
            live_count(store, &exec),
            1,
            "deleting an absent key is a no-op on the count"
        );

        // The delete recorded the cleared header value.
        let st = exec.cell_state(store).unwrap();
        assert_eq!(
            st.get_field(crate::LAST_VALUE_SLOT).copied(),
            Some([0u8; 32])
        );
    }

    #[test]
    fn register_deos_seeds_and_registers() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let ctx = StarbridgeAppContext::new(cclerk, exec);
        let app = register_deos(&ctx);
        assert_eq!(app.cells().len(), 1);
    }
}
