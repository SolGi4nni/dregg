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
| #2 whole-turn | the verifier proves `effects.first()` only | **BUILD-HALF PROVEN, NOT LIVE.** `RotatedKernelForestCohortChain.lean` proves the cohort-proof chain forces every effect + rejects an unchained tail; the deployed `split_into_cohort_runs` + SDK `verify_full_turn_bound` already provide the per-cohort proofs + chain check. NOT BEING until the node executor leg enforces it. | `proof_verify.rs:160` (lead-only, the live gap); `chainForcesEveryCohort`/`cohort_chain_forces_tail` (`RotatedKernelForestCohortChain.lean`, `fa35d5aa5`). LIVE-WIRE PENDING. |
| #3 agent signature | "the rightful agent authorized THIS turn" | **OPEN (largest — disclosure ≠ being).** A proven curve-constrained Schnorr signature-forcing rung exists (`turn_auth_signature_air` + `TurnAuthSignature.lean`, teeth bite, curve eqn constrained not a free bit) — but it is SCHNORR/BabyBear^8; the deployed turn auth is **Ed25519, off-circuit**. The Schnorr rung is a STEPPING-STONE, not the close. | `turn_auth_signature_air.rs`/`TurnAuthSignature.lean` (`fa35d5aa5`, the scaffold); BEING needs an Ed25519 AIR (Edwards decompress + `[S]B=R+[k]A`, heaviest unbuilt) OR re-bind turn auth to the in-circuit key. |
| #4 replay | freshness | ✅ **FORCED (by analysis).** nonce folds into the commit + forced `+1` → strictly-monotone commit sequence → a chain-following client rejects a stale OLD_COMMIT; the 8-felt widening preserves it. Residual = chain-FORK resistance (consensus layer, not the per-proof circuit). | `cell/src/commitment.rs:896` (nonce in pre-limbs), `gNonce` `+1` gate; `fd7b79b89`. |
| #5 fee-in-proof | the fee debit | ✅ **FORCED-LIVE.** live sovereign transfer routes the wide fee descriptor (55-PI); fee PI-published, gate forces `after = before − transfer − fee`; underclaimed/forged fee UNSAT. Residue: fee on a NON-sovereign agent cell still executor-trusted; the OLD_COMMIT block uses a blind `pre=post+fee` reconstruction (sound — OLD_COMMIT independently binds — but a trusted input). | `proof_verify.rs:171,301`; `3aa5debe8`; survived the flip (col-89 pin + debit gate in the wide TSV). |
| #6 cross-cell Σδ=0 | turn-wide conservation | **BUILD-HALF PROVEN, NOT LIVE.** a real AIR (`cross_cell_conservation_air.rs`) + Lean (`CrossCellConservation.lean`) force per-asset Σ(signed NET_DELTA)=0; teeth bite (forged A−10/B+999 UNSAT, wrong-asset rejected). NOT BEING until `proof_verify.rs` sums the per-cell NET_DELTA PIs per asset + requires Σ=0. | `fa35d5aa5`; the per-cell proofs already publish NET_DELTA PIs (`pi 16/17`). LIVE-WIRE PENDING (the being-completion). |
| #8 non-vacuity | completeness | **TYPE-INHABITED (Lean) + SATISFIABILITY-WITNESSED (Rust).** `CircuitCompletenessNonVacuity.lean` inhabits `Satisfied2 transferV3` with the EMPTY trace (type-level only — gates vacuous). The MEANINGFUL satisfiability (real transfer satisfies the gates) is the deployed Rust roundtrips (`wide_transfer_proves_verifies`, sovereign 19/19). A non-empty Lean inhabitant is the residual. Does NOT affect soundness. | `CircuitCompletenessNonVacuity.lean` (`fa35d5aa5`, empty-trace); the Rust roundtrips are the being. |

## Remaining definition-of-done (ranked — trust-priority: *foolable* > *can't-prove*; regressions first)

- [ ] **#8 — non-vacuity** (small, NEXT): construct one concrete `: Satisfied2 := by` inhabitant (an honest
  transfer trace) so completeness is provably non-empty.
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
- [ ] **#6 — cross-cell Σδ=0** (medium): a turn-wide cross-cell conservation AIR over the per-cell NET_DELTA PIs
  (lift the existing aggregation AIRs onto the deployed path).
- [ ] **#2 — whole forest** (medium-large): prove every effect, not the lead — a multi-effect descriptor or
  per-effect sub-proof; retire `effects.first()`-only (the forest apex exists in Lean to lift).
- [ ] **#3 — agent signature** (large long-pole): wire `native_signature_air` (Ed25519 over the turn-hash)
  into the rotated descriptor, forced in-circuit.

When all are forced, a ledgerless `verify_batch` client concludes the genuine/authorized/non-replayed/conserving
transition with nothing trusted off-circuit. The commitment floor (the deepest piece) is already there; the
residue is per-fact forcing of authority (refusal), forest, signature, and cross-cell conservation.
