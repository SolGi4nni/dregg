# NOTIFY Step 2 — the cutover-settle VK checklist

*The EXACT batch to fold into the cutover's ONE coordinated VK epoch (NOT a second bump). The Lean
side is DONE and staged-additive (the `notify` ctor + α-totalization + all ripple arms landed, VK
byte-identical); this file is the Rust/VK tail that lands the encoding cutover. Whoever owns the
cutover executes this; the notify lane WROTE it.*

## Why this is staged (read first)

`Auth.notify` is a new kernel-authority constructor (`metatheory/Dregg2/Authority/Positional.lean:38`).
Every felt-encoder gained a `| .notify => 7` arm and the FFI codec a `7 ⇄ notify` arm — but **no
cap-construction site emits `notify` yet**, so for every deployed/test input the encoders produce
byte-identical columns and the VK is unchanged. The VK only moves when a REAL notification cap is
emitted with its badge-mask leaf. That emission + the Rust marshaller agreement is THIS checklist. It
MUST ride the same single VK epoch as the rotation/C3 cutover (the cell-commitment ↔ circuit ↔ verifier
triangle honors one VK at a time; two simultaneous bumps break the verifier contract — see
`docs/NOTIFY-CASCADE.md` "The hard constraint").

## What is ALREADY DONE (Lean, staged-additive, VK byte-identical — do NOT redo)

- `Auth.notify` ctor + docstring — `Dregg2/Authority/Positional.lean:38`.
- 5 felt-encoder arms `| .notify => 7` — `Dregg2/Circuit/Witness/{Spawn,Delegate,RefreshDelegation,RevokeDelegation,attenuateA}Witness.lean` (`authCode`).
- FFI codec `7 ⇄ notify` + round-trip theorem `authOfTag_authTag` — `Dregg2/Exec/FFI.lean:429`.
- `Fintype Auth` elems + `allAuths` (Handlers/Authority.lean) + the two `capFacetMask`(A) "full facet"
  lists + `CellConfine.fullAuthCeiling` — all now include `.notify` (the "every Auth" lists stay complete).
- Display arms (`Widget/DreggForest.authStr`, `Widget/CapabilityGraph.authTag`).
- α-totalization — `Dregg2/Firmament/SeL4Abstract.lean`: `Notify ↦ some .notify`, `.notify ∈ usedAuth`,
  new theorems `alpha_total_on_ipc` / `alpha_Notify_is_notify`; the grounding `dregg_executor_cap_authority_grounded_in_seL4`
  now covers all 7 IPC authorities. (`alpha_total_iff_used` / `alpha_injective_on_used` re-closed automatically.)
- The kernel-Auth re-binding — `Dregg2/Firmament/NotifyAuthority.lean` §5.5 (`notifyCap_confers_notify`,
  `notifyCap_confers_no_edge`, `notify_attenuate_real_no_amplify`, `firmament_Notify_alpha_real_notify`,
  `notify_real_binding_no_amplify`): the badge-mask non-amp IS the real `facetAttenuation`, the rights
  non-amp IS the real `attenuate_subset`, over the kernel `Auth.notify`.

## THE CUTOVER-SETTLE TAIL (Rust + VK — executed by the cutover owner, ONE epoch)

Each item is keyed to the live site. The whole batch is ONE VK bump; gate each green before the next.

### 1. The Rust FFI authTag marshaller (`7 ⇄ notify`)

- **Site:** the Rust counterpart of `Dregg2/Exec/FFI.lean:429` `authTag`/`authOfTag` — the `0..6` → `0..7`
  wire codec. Find the Rust auth-tag enum/match that mirrors the Lean `Auth` order (grep the marshaller
  for the `read=0 … control=6` sequence; likely `turn/src/lean_shadow.rs` `auth_to_wire` / the SDK
  cap-rights serializer).
- **Edit:** add the `notify => 7` encode arm and the `7 => notify` decode arm. Mirror the Lean
  `authOfTag_authTag` round-trip (a Rust unit test: encode∘decode = id for all 8, INCLUDING notify).
- **VK impact:** none in isolation (no felt), but it MUST land in the batch so the wire and the circuit
  agree the instant a notify cap is emitted.

### 2. The cap-leaf badge-mask (`circuit/src/cap_root.rs:94` `CapLeaf`)

This is the felt-level encoding change — the heart of the VK bump.

- **Site:** `circuit/src/cap_root.rs:94` `CapLeaf` — it ALREADY carries `mask_lo`/`mask_hi` (`:102`), an
  `EffectMask` (u32) split low-16/high-16, folded into the 7-field Poseidon2 leaf digest (`:115`);
  `split_effect_mask` `:146`; the builder `:551`.
- **RECOMMENDED edit (smallest VK delta — path A + effect-mask reuse, per `NOTIFY-CASCADE.md` §1d/R1):**
  when the cap's `auth_tag` indicates a NOTIFICATION cap, interpret the existing `mask_lo`/`mask_hi`
  pair AS the badge-mask (no new leaf field; a semantic overload on the mask). The notify badge-mask is
  the SAME u32 shape as the effect-mask, so the leaf arity is unchanged — the digest change is purely
  that a notify-cap's mask bits now MEAN the badge-mask. This is the smallest leaf-digest delta.
- **ALTERNATIVE (cleaner, larger VK delta — a later wave if the overload proves cramped):** add a
  parallel `badge_mask_lo`/`badge_mask_hi` pair → an 8th/9th leaf field → a leaf-arity change → a bigger
  VK bump. Deferred unless the effect-mask overload is insufficient.
- **VK impact:** the leaf digest changes (the `auth_tag = notify` interpretation), so the cap-root
  commitment and every VK over it must re-pin. This is the felt-level reason the batch is a VK bump.

### 3. The cap-leaf builder + auth-tag fold (`cell/src/commitment.rs`)

- **Sites:** `cell/src/commitment.rs:520` `auth_required_to_tag` (the `AuthRequired` tier → tag fold);
  `cell/src/commitment.rs:742` `compute_authority_digest_felt` (the 8 `Permissions` fields); the
  cap-leaf builder `cap_root.rs:551`.
- **Edit:** if the badge-mask reuses the effect-mask field (RECOMMENDED), NO change here — `notify` does
  NOT add an `AuthRequired` tier (a notify cap's RIGHTS ride the existing `None/Signature/Proof/Either/
  Impossible/Custom` lattice unchanged; this is the Lean `NotifyCap.rights : AuthReq`). If the parallel
  badge-mask field is taken instead, build it here from the cap. **Confirm `notify` adds no
  `AuthRequired` variant** — it is an `Authority.Auth` cap-right, NOT an `AuthRequired` tier (the two
  Rust namespaces, `NOTIFY-CASCADE.md` §Layer-3).

### 4. The in-circuit signal-admissibility gate (`circuit/src/effect_vm_p3_full_air.rs`) — Phase-B

- **Sites:** `effect_vm_p3_full_air.rs:255` (the held-auth-tier tag column), `:1963` (the in-circuit
  encode fold); `circuit/src/effect_vm/effect.rs:40` (the leaf auth_tag read).
- **Edit (only if a first-class `signalA` effect or an in-circuit cap-gate is wanted in this epoch —
  otherwise DEFER):** a `signalGated` analogue — a signalled badge must be within the leaf's badge-mask
  (the in-circuit `badge &&& ¬mask == 0` gate). The Lean reference is `NotifyAuthority.signalGated` +
  `signalAdmissible_attenuate_no_amplify`. For the FIRST cut (path A, cap-only), the badge-mask is
  carried on the leaf and the admissibility is enforced at apply-time by the executor (the cap gate),
  not necessarily a new in-circuit column — so this item is OPTIONAL for the first VK bump and can be a
  named later wave.

### 5. The verifier VK re-pin (`verifier/src/`)

- **Site:** `verifier/src/` — the VK / public-input contract.
- **Edit:** re-pin the VK after items 2 (and 4, if taken) change the leaf digest. This is THE single
  coordinated VK bump — it MUST be the only VK change in flight (the rotation/C3 churn must have settled
  first; confirm `docs/ROTATION-CUTOVER.md` is at its post-cutover VK epoch before starting).
- **Re-pin the descriptor SHA registry** (the "VK" = the 26+ descriptor SHA fingerprints): the 5
  felt-encoders now emit a column value `7` for a notify right, so any golden descriptor/byte-pin that
  could contain a notify cap re-pins. (No deployed descriptor contains one yet, so in practice the
  re-pin is a no-op UNTIL a notify cap ships — but it MUST be regenerated in the same epoch so the
  registry and the encoders agree.)

### 6. The differential (Lean ↔ NEW Rust over the badge-mask cap) — before cutover

- **What:** the `STAGED-ADDITIVE-THEN-CUTOVER` validation that the Lean kernel and the NEW Rust agree
  byte-for-byte on the new leaf for a notification cap. Build a notify cap (target + rights + badge-mask)
  on both sides and assert the cap-leaf digest matches (the Lean `NotifyCap` ↔ the Rust `CapLeaf` with
  `auth_tag = notify`). This is the gate that the encoding cutover is sound, NOT a differential against a
  buggy oracle.

## Lands LATER (named follow-on waves — NOT this VK epoch)

- **A first-class `signalA` effect (path B):** `| signalA …` on `FullActionA`
  (`Dregg2/Exec/TurnExecutorFull.lean`) + `Effect::Signal` on the Rust `Effect` enums
  (`cell/src/effect_vm/effect.rs:73`, `turn/src/action.rs:800`) + a new `EffectVmEmitSignal`
  wide-descriptor + `descriptor_agrees_with_executor`. A SEPARATE second VK bump.
- **The Rust organ welds (`W-organ-*`):** gate `node/src/channels_service.rs:300` `push_message` / the
  SSE, `starbridge-v2/src/dynamics.rs:111` `emit`, the relay drain — on a held notify-watch cap. Each a
  wave; touches the VK only where it changes the on-chain cap encoding. (The Lean models already exist —
  `Dregg2/Firmament/NotifyOrgans.lean`.)
- **The parallel `badge_mask_lo`/`badge_mask_hi` leaf field** (item 2's alternative), if the effect-mask
  overload proves cramped — another leaf-arity VK bump.

## The one risk carried forward (NOT closed)

The badge-OR is a covert channel (`NOTIFY-CASCADE.md` §the-one-risk): a signaller modulates bits of the
badge, a waiter reads the OR; bandwidth = the badge width, and "may wake but not read" is exactly the
authority that creates a one-bit leak. The badge-mask is the info-flow scope (so attenuation is also a
bandwidth attenuation — the keystone `signalAdmissible_attenuate_no_amplify` read as a bandwidth
non-amplification), but a notify cap is NEVER information-free even stripped of `read`, and dregg has no
noninterference argument yet (out-of-scope, `SeL4Abstract.lean:40`). A notify cap must be PRICED in any
future noninterference work. Flagged here, in the same breath — not laundered.
