# starbridge-compartment-workflow-mandate

Scaffold starbridge-app for the **Compartment Workflow Mandate** verified in
`metatheory/Dregg2/Apps/CompartmentWorkflowMandate*.lean`. Composes dregg-native
primitives only — `FactoryDescriptor`, `CellProgram::Cases`, `Effect::SetField`,
`Effect::EmitEvent`, `AppCipherclerk::make_action`.

The mandate cell models a charter DAG (**review → redact → sign**) with:

| Slot | Constant | Purpose | Caveat |
|---:|---|---|---|
| `0` | `STEP_CURSOR_SLOT` | completed-step prefix length | `MonotonicSequence` on `advance_step` |
| `1` | `COMMITMENT_ANCHOR_SLOT` | compartment tag (`charterNul`) | `Immutable` |
| `2` | `CHARTER_TERMINAL_SLOT` | DAG terminal bound (`steps.length`) | `Immutable` |
| `3` | `CLEARANCE_GRAPH_ROOT_SLOT` | label-dominance graph root | `Immutable` |
| `4` | `SPEND_POLICY_SLOT` | Stingray per-step debit | `Immutable` |

---

## Lean theorem → Rust admission check mapping

| Lean (CompartmentWorkflowMandate) | Rust (this crate) | Layer |
|---|---|---|
| `stepAdmissible` — DAG prerequisites + not-already-done | [`step_admissible`] | Predicate (off-chain / turn-builder preflight) |
| `stepClearanceOK` / `needsAll` — compartment clearance | [`step_clearance_ok`] | Predicate (scaffold; full graph via `CLEARANCE_GRAPH_ROOT_SLOT`) |
| `cwmAdvanceM` — composed one-step admission | [`cwm_advance_admits`] | Predicate |
| `cwm_illegal_dag_rejected` | `step_admissible` returns false → builder must not emit action | Predicate fail-closed |
| `cwm_clearance_violation_rejected` | `step_clearance_ok` returns false → no action | Predicate fail-closed |
| `cwm_illegal_dag_rejected_exec` — illegal cursor jump | `StateConstraint::MonotonicSequence { STEP_CURSOR_SLOT }` | Executor slot caveat |
| `mandateCaveats` — immutable anchor + bounded cursor | `Immutable(COMMITMENT_ANCHOR_SLOT)` + `FieldLteField(STEP_CURSOR, CHARTER_TERMINAL)` | Executor |
| `cwm_step_legal_forever` / `cwmWF` | `FieldLteField` + `MonotonicSequence` on every admitted turn | Invariant |
| `cwm_pay_supply_forever` | Metadata-only `SetField`/`EmitEvent` (balance-neutral by construction) | Conservation |
| `charterMandate3.spendPolicy` (Stingray demo) | `SPEND_POLICY_SLOT` + `DEFAULT_STEP_SPEND_POLICY` | Policy pin (debit wiring follow-on) |
| `cwmInCompartment` / `cwmAnchorIs` | `COMMITMENT_ANCHOR_SLOT` immutability + init field constraint | Bucket invariant |

[`step_admissible`]: src/lib.rs
[`step_clearance_ok`]: src/lib.rs
[`cwm_advance_admits`]: src/lib.rs

### Gated production theorems (CompartmentWorkflowMandateGated)

| Lean | Rust follow-on |
|---|---|
| `cwm_safety_forever` = step-legal ∩ pay-conserved ∩ revoked-dead ∩ compartment | Wire `SenderAuthorized` + revocation root witness on `advance_step` case |
| `MonotonicSequence` DAG enforcement in `execFullForestG` | Already scaffolded; gated lane adds method-scoped witness blobs |

---

## Exports

```rust
cwm_factory_descriptor() -> FactoryDescriptor
cwm_cell_program() -> CellProgram
factory_descriptors() -> Vec<FactoryDescriptor>

build_advance_step_action(cclerk, mandate_cell, current_cursor, phase) -> Action
build_init_mandate_action(cclerk, mandate_cell, anchor, terminal, graph_root, spend) -> Action

register(ctx: &StarbridgeAppContext) -> [u8; 32]
```

Factory VK placeholder (32 bytes):

```
*b"starbridge-cwm-mandate-factory!!"
= 0x737461726272696467652d63776d2d6d616e646174652d666163746f72792121
```

---

## Standalone check

```sh
cargo check -p starbridge-compartment-workflow-mandate
cargo test  -p starbridge-compartment-workflow-mandate
```

---

## See also

- `metatheory/Dregg2/Apps/CompartmentWorkflowMandate.lean` — ungated crown theorems
- `metatheory/Dregg2/Apps/CompartmentWorkflowMandateGated.lean` — production `cwm_safety_forever`
- `metatheory/Dregg2/Authority/ClearanceGraph.lean` — clearance label dominance
- `starbridge-apps/nameservice/` — pattern anchor
- `app-framework/src/starbridge.rs` — `StarbridgeAppContext` mount point