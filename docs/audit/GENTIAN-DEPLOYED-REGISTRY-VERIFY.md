# GENTIAN deployed-registry VERIFY — is the capacity-floor refuse live on the deployed light-client path?

Audit date: 2026-07-06. Repo `/Users/ember/dev/breadstuffs` @ `main` (HEAD `2630964ae`, the gentian
liveness commit). Grounded at file:line at HEAD.

## The question

The flag-day welded a three-block **capacity-floor refuse** (escrow tag 17 / discharge 18 / vault 19)
onto the bare rotated cohort so a **declared-capacity dodge** (a cell that DECLARES an escrow/discharge/
vault obligation and settles via a plain BARE cohort leg instead of its satisfaction member) is UNSAT
under the bare descriptor. The soundness keystone is
`metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3Refused.lean` (`v3RegistryRefused`, widening
`traceWidth` 1581→1626 + 39 refuse gates) with `BareCohortFloorRefuseDeployed.declared_capacity_unsat_deployed`.

The meta-review flagged a **registry mismatch**: that refuse is emitted onto the **V3 1-felt** registry
(`rotation-v3-staged-registry.tsv`), but the DEPLOYED light-client verify path resolves the **WIDE /
WELDED** registries. If the descriptor the deployed LC actually verifies a capacity turn against does not
carry the refuse, the flip is not live on the deployed path.

## VERDICT: NOT LIVE on the deployed light-client path.

The capacity-floor refuse and the three satisfaction members live **only** on the V3 1-felt registry.
The deployed light-client verify (both the SDK wire verifier and the executor cohort verify) resolves the
**WIDE** registry first, then the **WELDED** registry, and falls back to V3 **only** for `CapOpen`
members that lack a wide twin. A bare-cohort leg for a declared-capacity cell therefore binds its **WIDE**
member — which carries **neither the refuse nor the satisfaction gate** — and is accepted. The gentian
soundness flip is real in Lean and on the V3 registry, but the deployed light client never verifies a
capacity turn against that registry.

## Ground truth (grep + file:line)

### 1. The refuse + the satisfaction members are V3-ONLY

- `circuit/descriptors/rotation-v3-staged-registry.tsv`: 36 members at `trace_width:1626` (the
  refuse-widened bare cohort); the string `gentian-deployed-bare-refuse` appears **only** in this file
  (grep across `circuit/descriptors/` returns this file alone); `floor`/`refuse` selector strings: **72**
  occurrences. The three satisfaction members `settleEscrowSatVmDescriptor2R24` /
  `dischargeSatVmDescriptor2R24` / `vaultSatVmDescriptor2R24` are present here (width 1581).
- `circuit/descriptors/rotation-wide-registry-staged.tsv` and
  `rotation-wide-umem-welded-registry-staged.tsv`: `floor`/`refuse` occurrences: **0** each; the three
  satisfaction members: **absent** (0 hits) from both. Their `trace_width` band is 2465–2965 — a
  different emit entirely from the 1626 refuse cohort.
- Per-effect widths (the bare-cohort `transfer` / `burn` member): V3 `transferVmDescriptor2R24` =
  `trace_width 1626` (refuse-welded); WIDE = `2495`; WELDED = `2502`. V3 `burnVmDescriptor2R24` = `1626`;
  WIDE = `2493`. The wide/welded twins carry **no** `floor` gate.

### 2. The deployed light-client verify resolves WIDE/WELDED, not V3

- SDK wire verifier `sdk/src/full_turn_proof.rs::verify_effect_vm_rotated_with_cutover` (:4249): iterates
  `WIDE_REGISTRY_STAGED_TSV` first (:4313), extends with `WIDE_UMEM_WELD_REGISTRY_TSV` (:4324), and only
  if `bound.is_empty()` falls back to `V3_STAGED_REGISTRY_TSV` (:4326) — filtered to
  `name.contains("CapOpen") && !cap_open_key_has_wide_twin(name)` (:4334). The satisfaction members are
  NOT `CapOpen` names, and the refuse-welded bare transfer/burn is not `CapOpen` either, so neither can
  ever be surfaced by the fallback; and the fallback never fires for a bare leg (a wide member accepts, so
  `bound` is non-empty).
- Executor cohort verify `turn/src/executor/proof_verify.rs::verify_one_cohort_run` (:614): resolves the
  cohort member `name` from the EFFECT-keyed `rotated_descriptor_name_for_effect(lead)` (:677), i.e. a
  settle-as-transfer resolves `name = "transferVmDescriptor2R24"` — the declaration-keyed
  `rotated_descriptor_name_for_declared_capacity` the gentian commit added is NEVER called here. It parses
  that `name` from `WIDE_REGISTRY_STAGED_TSV` (:684) and the welded twin from
  `WIDE_UMEM_WELD_REGISTRY_TSV` (:734); `require_welded` (:1219) DROPS the bare wide member in favour of
  the welded twin for a single-cohort sovereign turn. The caveat manifest it reconstructs is
  `transfer_caveat_manifest()` (:755), which declares NO capacity tag — so the declared capacity is not
  even reconstructed on this path. V3 is never read on this path. (The V3 registry is only referenced in
  this file inside a comment, :981.)
- Non-test reads of `V3_STAGED_REGISTRY_TSV` are producers / aggregation / the SDK fallback, not a
  primary capacity-turn verify (grep over `--include=*.rs`, excluding tests).

### 3. The gentian LIVENESS test does NOT exercise the deployed resolution

`circuit/tests/gentian_deployed_capacity_liveness.rs` proves + verifies each satisfaction member by
parsing it **directly** from `V3_STAGED_REGISTRY_TSV` (`deployed_member`, :135) and calling
`verify_vm_descriptor2` on that exact descriptor (`accepts`, :153). That is a unit-level check of the V3
member in isolation — it never routes through `verify_effect_vm_rotated_with_cutover` /
`verify_one_cohort_run`, i.e. never through the WIDE-first resolution the deployed light client uses. So
the liveness test proves the V3 satisfaction member *can* accept an honest turn; it does **not** show the
deployed LC ever *selects* that member. The routing helper
`rotated_descriptor_name_for_declared_capacity` (`circuit/src/effect_vm/trace_rotated.rs`, added by
`2630964ae`) names the V3 satisfaction member, but nothing on the deployed verify path consults it, and no
WIDE/WELDED satisfaction member exists for a producer to emit or the LC to bind.

## The forge (the decider)

`sdk/tests/gentian_deployed_registry_dodge_forge.rs` —
`declared_capacity_dodge_verifies_through_deployed_lightclient`. It:

1. Builds a cell whose caveat manifest **declares** the escrow capacity obligation (tag 17, folded into
   the committed `caveatCommit` PI) and settles it via a plain bare-cohort leg (a value-draining `Burn`;
   the Lean refuse theorem `declared_capacity_unsat_deployed` is stated for ANY bare member).
2. Produces the **WIDE** bare leg (`burnVmDescriptor2R24`, width 2493 — the deployed producer's default),
   a real batch STARK.
3. Drives the serialized proof through the ACTUAL deployed entry
   `dregg_sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover`.

RESULT (real `--release` STARK, `1 passed`, verify in 1.52s): <!-- FORGE_RESULT -->the deployed LC
**ACCEPTS** the leg. `verify_effect_vm_rotated_with_cutover` bound the WIDE `burnVmDescriptor2R24`
(width 2493, marker-free — no `gentian-deployed-bare-refuse`); the refuse-welded V3 member (width 1626,
`...-gentian-deployed-bare-refuse`) and the V3 satisfaction members are UNREACHABLE on the deployed path.
UNSAT would have meant the refuse reached the deployed path (flip live); the ACCEPT confirms the
declared-capacity bare-descriptor dodge is OPEN on the deployed light-client path. (Structural corroboration
asserted in the same test: the `gentian-deployed-bare-refuse` marker is present on the V3 bare member and
absent from both the WIDE and WELDED bare members; the three satisfaction members are committed V3 members,
absent from WIDE/WELDED, and not `CapOpen` names.)<!-- /FORGE_RESULT -->

## What is and isn't true

- TRUE: the gentian soundness flip is real **in Lean and on the V3 1-felt registry** — a declared-capacity
  turn is UNSAT under every `v3RegistryRefused` member, and the V3 satisfaction members prove honest turns.
- FALSE (the overclaim): that the flip is **live on the deployed light-client path**. The deployed LC
  (`verify_effect_vm_rotated_with_cutover`, `verify_one_cohort_run`) verifies a bare-cohort capacity turn
  against its WIDE/WELDED twin, which carries no refuse and no satisfaction gate. A light client is
  therefore still foolable by a declared-capacity bare-descriptor dodge.

## The real hole → the closure lane

The refuse + satisfaction weld must be carried on the **WIDE / WELDED** cohort (the registries the deployed
LC actually resolves), not only on the V3 1-felt registry — OR the deployed resolution must be repointed to
require the V3 refuse/satisfaction member for a declared-capacity turn. Concretely, either:
(a) emit `gentianDeployedBareRefuse` onto the WIDE bare cohort (a wide re-emit + VK epoch, so the wide
    transfer/burn members widen to carry the floor refuse), and add WIDE satisfaction twins the deployed
    producer emits and the LC binds; or
(b) add a declared-capacity discriminator to `verify_effect_vm_rotated_with_cutover` /
    `verify_one_cohort_run` that, when the committed caveat manifest declares a capacity tag, REQUIRES the
    (V3) satisfaction member and REJECTS the bare wide member — the verify-side analog of the routing
    helper that already exists on the producer side.

Until then the caveat-declaration is enforced only by the off-AIR host / the V3 face, not by the deployed
light client.
