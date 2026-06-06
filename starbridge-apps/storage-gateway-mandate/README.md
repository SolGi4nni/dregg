# starbridge-storage-gateway-mandate

Scaffold starbridge-app for the **Storage Gateway Mandate** verified in
`metatheory/Dregg2/Apps/StorageGatewayMandate*.lean`. Composes dregg-native
primitives only — operation-scoped `CellProgram::Cases`, `SetField` +
`EmitEvent` turn chains mirroring Lean `sgmStorageChain`.

The mandate cell models a content-addressed object store with:

| Slot | Constant | Purpose | Caveat |
|---:|---|---|---|
| `0` | `OBJECT_KEY_SLOT` | last object key hash | per `storage_op` turn |
| `1` | `LAST_OP_SLOT` | GET=0 / PUT=1 / LIST=2 | per `storage_op` turn |
| `2` | `VOLUME_SPENT_SLOT` | Stingray debit tracker | `Monotonic` + `FieldLteField` vs ceiling |
| `3` | `COMMITMENT_ANCHOR_SLOT` | bucket/compartment tag | `Immutable` |
| `4` | `VOLUME_CEILING_SLOT` | Stingray slice ceiling | `Immutable` |
| `5` | `KEY_PREFIX_HASH_SLOT` | authorized prefix | `Immutable` |
| `6` | `READ_COMPARTMENT_SLOT` | GET clearance label | `Immutable` |

---

## Lean theorem → Rust admission check mapping

| Lean (StorageGatewayMandate) | Rust (this crate) | Layer |
|---|---|---|
| `StorageOp` GET/PUT/LIST + `StorageOp.toInt` | [`StorageOp`] + `to_field_value` / `from_field_value` | Domain encoding |
| `opAllowed` | [`op_allowed`] | Predicate |
| `keyUnderPrefix` / `putPrefixOK` | [`key_under_prefix`] | Predicate (PUT gate) |
| `getClearanceOK` / `mayRead` | [`get_clearance_ok`] | Predicate (GET gate; scaffold) |
| `opCost` + `Slice.tryDebit` | [`volume_debit_ok`] + `StorageOp::demo_cost` | Stingray volume budget |
| `sgmAdmitM` — composed admission | [`sgm_admit`] | Predicate |
| `sgm_op_not_allowed_rejected` | `op_allowed` false → `sgm_admit` returns `None` | Fail-closed |
| `sgm_prefix_violation_rejected` | `key_under_prefix` false on PUT | Fail-closed |
| `sgm_clearance_fail_rejected` | `get_clearance_ok` false on GET | Fail-closed |
| `sgm_over_debit_rejected` | `volume_debit_ok` false | Fail-closed |
| `sgm_over_debit_rejected_exec` | `Monotonic(VOLUME_SPENT)` + `FieldLteField` vs `VOLUME_CEILING` | Executor caveat |
| `sgm_volume_legal_forever` / `sgmWF` | `FieldLteField(VOLUME_SPENT, VOLUME_CEILING)` invariant | Forever stream |
| `sgm_pay_supply_forever` | Metadata-only writes (balance-neutral) | Conservation |
| `sgmInBucket` / `sgmAnchorIs` | `COMMITMENT_ANCHOR_SLOT` immutability | Bucket invariant |
| `sgmStorageChain` (set key → set op → emit) | [`build_storage_op_action`] effect chain | Turn builder |

[`StorageOp`]: src/lib.rs
[`op_allowed`]: src/lib.rs
[`key_under_prefix`]: src/lib.rs
[`get_clearance_ok`]: src/lib.rs
[`volume_debit_ok`]: src/lib.rs
[`sgm_admit`]: src/lib.rs
[`build_storage_op_action`]: src/lib.rs

### Gated production theorems (StorageGatewayMandateGated)

| Lean | Rust follow-on |
|---|---|
| `sgm_safety_forever` = step-legal ∩ pay-conserved ∩ revoked-dead ∩ bucket | Revocation witness + bucket tag check on `storage_op` case |
| `execFullForestG` gated setField/emit | Method-scoped `storage_op` case already scaffolded |

---

## Exports

```rust
sgm_factory_descriptor() -> FactoryDescriptor
sgm_cell_program() -> CellProgram
factory_descriptors() -> Vec<FactoryDescriptor>

build_storage_get_action(cclerk, cell, key, new_spent) -> Action
build_storage_put_action(cclerk, cell, key, new_spent, blob_hash) -> Action
build_storage_list_action(cclerk, cell, prefix, new_spent) -> Action
build_init_gateway_action(cclerk, cell, anchor, ceiling, prefix, read_compartment) -> Action

register(ctx: &StarbridgeAppContext) -> [u8; 32]
```

Factory VK placeholder (32 bytes):

```
*b"starbridge-sgm-mandate-factory!!"
= 0x737461726272696467652d73676d2d6d616e646174652d666163746f72792121
```

Demo defaults (Lean `demoMandate`):

- prefix: `uploads/`
- volume ceiling: `10`
- costs: GET=1, PUT=5, LIST=2
- read compartment: `storage-read`

---

## Standalone check

```sh
cargo check -p starbridge-storage-gateway-mandate
cargo test  -p starbridge-storage-gateway-mandate
```

---

## See also

- `metatheory/Dregg2/Apps/StorageGatewayMandate.lean` — ungated crown theorems
- `metatheory/Dregg2/Apps/StorageGatewayMandateGated.lean` — production `sgm_safety_forever`
- `metatheory/Dregg2/Proof/Stingray.lean` — `Slice` volume budget
- `starbridge-apps/subscription/` — operation-scoped `CellProgram::Cases` pattern
- `app-framework/src/starbridge.rs` — `StarbridgeAppContext` mount point