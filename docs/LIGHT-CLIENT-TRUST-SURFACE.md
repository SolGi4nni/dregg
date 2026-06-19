# Light-Client Trust Surface — the definition of done for "a light client can actually trust dregg"

> Goal (ember): a client running ONLY `verify_and_commit_proof_rotated`'s `verify_batch` + the published
> public inputs — with NO ledger, NO executor, NO producer trust — can conclude the published `(pre,post)`
> is a **genuine, authorized, non-replayed, conservation-respecting** kernel transition.

## How this doc stays honest (read before editing — this doc rotted once)

The original version of this doc rotted in two ways that this format is designed to prevent: it **missed the
deepest hole** (the per-cell commitment was 1 felt ≈ 31-bit — it saw the symptom, the off-circuit PI override,
but framed it as a *trust seam* and never *counted the bits*, i.e. it laundered a 31-bit floor as "the existing
scheme"), and it **over-claimed an open hole** (#4 replay, already closed by the nonce-in-commit it didn't
trace). Both came from **unsourced assertions**, not a bad code source.

So every status line below obeys three rules: **(1) cite the forcing mechanism** (file:line) — a closure you
can't cite isn't closed; **(2) measure the quantity** (bits, where a binding has a width) — a felt is ≈30.9
bits, a collision is ≈half that, the proof's own FRI soundness is ≈130-bit, so a commitment narrower than ~8
felts is the floor regardless of how sound the proof is; **(3) date it + verify against HEAD** — this table is
a point-in-time reading, NOT a standing truth; re-confirm a line against the code before relying on it. A claim
forced to show its mechanism and count its bits cannot launder, over-claim, or silently rot.

## The lens: proof-FORCED vs off-circuit-ANCHORED

The deployed `verify_and_commit_proof_rotated` (`turn/src/executor/proof_verify.rs`) is, for some facts, still a
**producer-replay verifier**: it reconstructs trusted state from the ledger and ANCHORS a published PI to it
(sound for a full node; invisible to a ledgerless light client). A light client trusts only what the circuit's
`pi_binding`/gates FORCE. Every smuggle is one fact still ANCHORED that must become FORCED. As of the 8-felt
flip (`9e5a83935`) the *commitment itself* is forced (the ~31-bit waist is gone); the residue is per-fact.

## ⚑ STATUS AT HEAD (2026-06-19, post 8-felt flip `9e5a83935`)

| # | fact | status | mechanism (verify vs HEAD) |
|---|------|--------|----------------------------|
| commit width | the per-cell commitment | ✅ **FORCED ~124-bit** | 8-felt chip-faithful chain; 1-felt waist retired (`9e5a83935`); LIVE collision tooth bites with NO executor (`effect_vm_rotation_flip::wide_transfer..._collision_tooth_bites`). |
| #1 authority residue | record_digest per mover class | **MIXED.** value-cohort (WAVE 0) · lifecycle disc (WAVE 1) · perms/VK (WAVE 2) · makeSovereign = **FORCED in-circuit**. **refusal + setFieldDyn = ANCHORED off-circuit** (NOT a cheap "restore" — see below). | WAVE0 `rotateV3FrozenAuthority` colEq welds (`EffectVmEmitRotationV3.lean:1724`, `9f415ca97`); refusal off-circuit `proof_verify.rs:360,389` (`Anchor::RecordDigest`). |

**⚠ Correction (R1 audit `a424f1134992f6262`, supersedes the earlier "refusal is a cheap regression to restore"):**
the proven gate `rotateV3WithFieldsRootGate` welds the committed AFTER `fields_root` to `prmCol 0`, and that
works for setPerms/setVK (where `prmCol 0` = the new perms/vk hash, which the **effects_hash chain anchors to a
light-client PI** — the client has the declared value from the effect it's verifying). It does NOT work for
**refusal**: the refusal producer fills `prmCol 0` with the **target**, not the post-`fields_root`
(`trace.rs:893`), and the post-`fields_root` is `insert(pre_fields_root_map, REFUSAL_AUDIT_KEY → audit)`
(`rotation_witness.rs:518`) — a **map-root that depends on the whole pre-cell map**, which a ledgerless client
does NOT have. So the only declared post-root is `fields_root_felt(post_cell)` from the trusted pre-cell —
re-pointing would either make honest refusals UNSAT (the parked WIP `ff8c4d768` did exactly this) or merely
RELOCATE the off-circuit anchor (PI 38 → `prmCol 0`), still needing the trusted post-cell. **A ledgerless refusal
close needs the OPENABLE-fields_root / map-op construction** (derive the post-root in-circuit from the in-circuit
pre-root + the public audit value — the cap-reshape #103 family), which is NEW soundness, not a re-point. Today
refusal is **full-node-safe** (the 8-felt commitment already binds limb 36, anchored via the record-pin) — but
NOT ledgerless-safe. **`setFieldDynForcedV3` is LIVE (`v3Registry:2889`) and shares this exact gate + the same
`prmCol 0`-vs-fields_root mismatch, with NO end-to-end prove+verify roundtrip test — its deployed integration is
genuinely incomplete; AUDIT whether the live setFieldDyn gate forces the wrong value or is simply inert.**
| #2 whole-turn | the verifier proves `effects.first()` only | ✅ **FORCED-LIVE** (`0eab40743`). the deployed `verify_and_commit_proof_rotated` now `split_into_cohort_runs` + verifies EVERY leg against its run's PI + chain-checks (`leg[0].before==OLD`, `leg[N-1].after==NEW`, `leg[i+1].before==leg[i].after`); interior boundaries cryptographically chained, NOT executor-trusted. Teeth bite: tail-omitted + tail-unchained REJECTED, honest multi-cohort accepts (`sovereign_rotated_c1` 22/0); single-effect byte-identical. SCOPE: the record-pin anchor projects from the before-cell (correct when earlier runs don't move the authority residue; a residue-mutating earlier run needs per-run before-cell threading — documented follow-up). | `proof_verify.rs` `verify_one_cohort_run`; `RotatedKernelForestCohortChain.lean` (`fa35d5aa5`). |
| #3 agent signature | "the rightful agent authorized THIS turn" | **OPEN (largest — disclosure ≠ being).** A proven curve-constrained Schnorr signature-forcing rung exists (`turn_auth_signature_air` + `TurnAuthSignature.lean`, teeth bite, curve eqn constrained not a free bit) — but it is SCHNORR/BabyBear^8; the deployed turn auth is **Ed25519, off-circuit**. The Schnorr rung is a STEPPING-STONE, not the close. | `turn_auth_signature_air.rs`/`TurnAuthSignature.lean` (`fa35d5aa5`, the scaffold); BEING needs an Ed25519 AIR (Edwards decompress + `[S]B=R+[k]A`, heaviest unbuilt) OR re-bind turn auth to the in-circuit key. |
| #4 replay | freshness | ✅ **FORCED (by analysis).** nonce folds into the commit + forced `+1` → strictly-monotone commit sequence → a chain-following client rejects a stale OLD_COMMIT; the 8-felt widening preserves it. Residual = chain-FORK resistance (consensus layer, not the per-proof circuit). | `cell/src/commitment.rs:896` (nonce in pre-limbs), `gNonce` `+1` gate; `fd7b79b89`. |
| #5 fee-in-proof | the fee debit | ✅ **FORCED-LIVE.** live sovereign transfer routes the wide fee descriptor (55-PI); fee PI-published, gate forces `after = before − transfer − fee`; underclaimed/forged fee UNSAT. Residue: fee on a NON-sovereign agent cell still executor-trusted; the OLD_COMMIT block uses a blind `pre=post+fee` reconstruction (sound — OLD_COMMIT independently binds — but a trusted input). | `proof_verify.rs:171,301`; `3aa5debe8`; survived the flip (col-89 pin + debit gate in the wide TSV). |
| #6 cross-cell Σδ=0 | turn-wide conservation | **BUILD-HALF PROVEN + DRIFT-GREEN; LIVE-ENFORCEMENT BLOCKED on a deeper gap.** the AIR (`cross_cell_conservation_air.rs`) + Lean (`CrossCellConservation.lean`) force per-asset Σ(signed NET_DELTA)=0, teeth bite, emitter registered (`2f42998b1`, drift PASS). BUT the deployed path proves PER-CELL-ISOLATED transitions — `convert_turn_effects_to_vm` (`effect_vm_bridge.rs:69`) filters a Transfer to ONE cell (debit OR credit), so the two legs are SEPARATE per-cell proofs and NO point holds ≥2 cells' deltas. Live-enforcement needs a NEW BATCH/BLOCK COLLECTOR first (collect every per-cell proof's `(NET_DELTA_MAG, NET_DELTA_SIGN, asset)` at `verifyBatch`/block-assembly + run `verify_cross_cell_conservation` per asset, reject unbalanced). NOT just wiring — a deeper architectural piece. | `fa35d5aa5`/`2f42998b1`; `execute.rs:446` (one proof/cell), `node turn_proving` `conservation:None`. BLOCKED on the batch collector. |
| #8 non-vacuity | completeness | **TYPE-INHABITED (Lean) + SATISFIABILITY-WITNESSED (Rust).** `CircuitCompletenessNonVacuity.lean` inhabits `Satisfied2 transferV3` with the EMPTY trace (type-level only — gates vacuous). The MEANINGFUL satisfiability (real transfer satisfies the gates) is the deployed Rust roundtrips (`wide_transfer_proves_verifies`, sovereign 19/19). A non-empty Lean inhabitant is the residual. Does NOT affect soundness. | `CircuitCompletenessNonVacuity.lean` (`fa35d5aa5`, empty-trace); the Rust roundtrips are the being. |

## Remaining definition-of-done (ranked — trust-priority: *foolable* > *can't-prove*; regressions first)

- [~] **#8 — non-vacuity** — type-inhabited (Lean empty trace, `fa35d5aa5`) + satisfiability-WITNESSED (Rust
  roundtrips build real satisfying traces). Residual: a non-empty Lean inhabitant (polish; the being is already
  in Rust). Not a foolable gap.
- [x] **#2 — whole forest** — ✅ FORCED-LIVE (`0eab40743`): deployed verifier checks every cohort + the chain;
  tail-omitted/unchained rejected. (Follow-up: per-run before-cell threading for residue-mutating earlier runs.)
- [x] **setFieldDyn gate audit** — DONE: **INERT, not a live bug.** SetField `field_idx` 0..7 routes to the
  frozen-face per-slot `setFieldVmDescriptor2-{0..7}R24` (no fields-root gate); `field_idx≥8` routes to
  `setFieldDynForcedV3` but PANICS in trace-gen pre-prove (`trace.rs:417` asserts `<8`) → the descriptor is in
  the registry/VK but UNREACHABLE; no honest proof exercises its gate, no forgery selects it. Dead weight + a
  latent landmine (its gate welds the committed fields_root to `prmCol 0`=`FIELD_INDEX`, the same mismatch as
  refusal — its doc-comment OVERCLAIMS "forces the declared post-fields_root"; moot while unreachable). If
  dynamic (≥8) setField is ever enabled it needs the openable-root fix. Optional cleanup: delete the dead
  descriptor + `_=>` arm (VK-affecting, low-value, deferred).
- [ ] **refusal + setFieldDyn ledgerless authority** (medium, was mis-scoped as "R1 restore"): the OPENABLE-
  fields_root / map-op construction (#103 cap-reshape family) — derive the post-root in-circuit from the
  in-circuit pre-root + the public audit value. NEW soundness, not a re-point. Full-node-safe today.
- [~] **#6 — cross-cell Σδ=0** — AIR proven + drift-green (`2f42998b1`), but live-enforcement BLOCKED: the
  deployed path proves per-cell-isolated transitions and no point collects ≥2 cells' deltas. **Prerequisite: a
  BATCH/BLOCK COLLECTOR** (gather every per-cell proof's `(NET_DELTA, asset)` at `verifyBatch`/block-assembly +
  run `verify_cross_cell_conservation` per asset). A new architectural piece, not wiring.
- [ ] **refusal + setFieldDyn ledgerless authority** (medium): the OPENABLE-fields_root / map-op construction
  (#103 cap-reshape family). Full-node-safe today.
- [ ] **#3 — agent signature** (large, ember-design IN FLIGHT): the dual-scheme — Ed25519 off-circuit receipt
  path + in-circuit curve key (the proven Schnorr rung) for proofs, cell-anchored scheme tag, Ed25519 never
  circuit-ified. Stack-wide scheme-dispatch (cell/SDK/executor/client). Curve-only vs both-keyed = pending
  ember decision.

REMAINING ARC: the commitment floor (deepest) is done; #2 forest + #4 replay + #5 fee are FORCED-LIVE; the
residue is (a) #6 cross-cell — needs the batch collector; (b) #3 signature — the dual-scheme build; (c) refusal
ledgerless authority — the openable-root; (d) #8 non-empty Lean inhabitant (polish). When (a)–(c) land, a
ledgerless `verify_batch` client concludes genuine/authorized/non-replayed/conserving with nothing off-circuit.

## Live-wire serialization plan (the seams; I serialize these one-at-a-time after the build-halves land)

All four converge on `proof_verify.rs` / the cell crate / `node` block-assembly → SEQUENTIAL, not parallel.
- **#3 dual-scheme** → `execute.rs:446` (the `execution_proof` branch is the PROVEN path; `SovereignCellWitness`
  at `:734` is the RECEIPT path — dual-dispatch slots HERE) + `proof_verify.rs` (proven turn: assert forced
  `cpk` == the cell's committed Curve authority) + the cell-authority scheme-tag (`cell/src/state.rs`/
  `commitment.rs`, folded into the 8-felt commit) + SDK signer-select. Both-keyed.
- **#6 batch collector** → the BLOCK level above `node/src/turn_proving.rs:843` (`conservation: None` becomes the
  collector result): gather every per-cell proof's `(NET_DELTA_MAG, NET_DELTA_SIGN, asset)`, run the proven
  `verify_cross_cell_conservation` per asset, reject an unbalanced block. (Per-cell isolation confirmed:
  `effect_vm_bridge.rs:69` splits a Transfer into one cell's leg.)
- **refusal openable-root** → re-point `refusalV3` (`EffectVmEmitRotationV3.lean`) to the openable-insertion gate
  + drop `Anchor::RecordDigest` for refusal in `proof_verify.rs:360,389` + the cell `fields_root` becomes the
  openable Merkle structure. VK-affecting (re-emit + re-pin).
- **#8** → no live-wire (Lean-internal; the non-empty inhabitant replaces the empty-trace lemma).

## The #2 follow-up — TRUE shape (a DELIBERATE fix, not a parallel rush; completeness, not soundness)

`proof_verify.rs:672` computes `dpis[38] = digest(apply LEAD effect to record_pin_cell)` — first match only,
`record_pin_cell` = the GLOBAL before-cell for every run. TWO completeness gaps (honest turns rejected; NOT a
soundness hole — the closed multi-cohort tooth holds for authority-invariant earlier runs):
1. **within-run multi-effect:** a `[SetPerms(A→B), SetPerms(B→C)]` run (same descriptor → ONE contiguous run)
   commits perms=C but anchors perms=B (lead only) → rejected.
2. **cross-run residue:** a later run's anchor projects from the global before-cell, missing an earlier run's
   residue move.
FIX needs the run→kernel-effect mapping — FIDDLY because `convert_turn_effects_to_vm` filters+projects (Transfer
→ debit-or-credit, not 1:1) AND same-class runs can be NON-CONTIGUOUS (`[SetPerms,Transfer,SetPerms]` → two
SetPerms runs), so "apply all matching by cell_id" over-applies. Getting it wrong regresses the live single-cohort
fleet (`sovereign_rotated_c1` 22/0). → do it TEST-FIRST (a producible multi-residue-move turn) + verify no
fleet regression. Deliberate, not rushed.
