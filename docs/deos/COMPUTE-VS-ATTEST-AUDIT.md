# Compute-vs-Attest / Input-Wire-Binding Audit (the DEPLOYED circuit)

> **⚠ GEOMETRY STALE (post-regen) — the CONCLUSIONS still hold, the NUMBERS do not.**
> This audit traced the `transferVmDescriptor2R24` geometry as of 2026-06-28
> (`trace_width=817`, `public_input_count=62`). Later big-bang regens widened it: the committed
> row at HEAD shows **`trace_width=2664`, `public_input_count=68`**
> (`circuit/descriptors/rotation-wide-registry-staged.tsv`). So every CONCRETE column index below
> (the BEFORE block base 188, AFTER block base 239, commit carriers 705..712/809..816, and the
> `PI[46..53]`/`PI[54..61]` last-16-PI cites) is **pre-regen and must be re-traced** — with
> `pi_count=68` the "last 16 PIs" are indices 52..67. Body `file:line` cites are likewise
> as-of-date. The load-bearing verdict is UNCHANGED: the deployed core computes over root-bound
> wires. The three findings' STATUS is updated in place below: FINDING 1's enforcement gates are
> deployed (the satisfaction member's committed VK remains the named residual), FINDING 2 is
> superseded by the in-circuit custom-binding fold, and FINDING 3's producer routes wide (a
> narrow-acceptance residual remains). (The balance gate
> `var[76]−var[54]−var[68]+2·var[69]·var[68]` itself survived the regens intact.)

Date: 2026-06-28. Scope: read-only soundness audit answering one sharp question for the
**deployed** verify path (NOT the staged gentian/satisfaction welds):

> Does dregg actually COMPUTE relations in-circuit over wires BOUND to the committed
> root, or does any deployed gate ATTEST over free/forgeable witness wires it only
> checks combinatorially?

The pitfall hunted: a circuit can satisfy its constraints over witness wires the prover
chooses freely; if those wires are not pinned to a committed root the light client checks,
the proof attests "some inputs satisfy R" but the inputs are forgeable. SOUND = every
load-bearing input wire is pinned to a committed root; aux/hint wires are forced by
constraints.

Evidence is cited to file:line at HEAD. **No code was changed by this audit.** Each real
finding names a fix but does NOT apply it (concurrent lanes share the working tree).

---

## Verdict (one line)

**The deployed NORMAL CORE computes over bound wires — yes, modulo the standard crypto
carriers.** Every load-bearing input wire in the deployed wide effect-VM leg is welded
in-circuit to the v1 state columns the gates read, those columns absorb (via a co-proven
Poseidon2 chip AIR) into the published 8-felt ~124-bit commit, and the commit PIs are bound
to the light client's trusted pre/post commit. There is **no free-wire forgery hole in the
deployed normal-core arithmetic**. Three honestly-named seams remain, all tracked:
(1) house-capacity SATISFACTION: the bare-descriptor dodge is CLOSED in the deployed VK
bytes (the bare-floor refuse weld) and in the verifier (GATE B), but the satisfaction
member itself carries no committed VK/producer yet, so satisfaction is not
pure-light-client-witnessed end-to-end; (2) the custom-effect sub-proof's commitment is
enforced IN-CIRCUIT by the recursion fold at 8 felts, and the deployed per-turn executor
entry pins the sub-proof's state I/O to the host's committed pre/post state fail-closed
(`enforce_custom_proof_state_binding`, `turn/src/executor/proof_verify.rs:620`); the
residual is chain-fold wiring — the state-binding fold node exists and is tested, but
`prove_chain_core_rotated`'s custom arm folds through the commitment-only node
(`ivc_turn_chain.rs:2868`); (3) the cap-open producer routes every live key wide (~124-bit), and
the 1-felt (~31-bit) commit persists only as an ACCEPTANCE residual (the
no-rotation-witness fallback + the verifier's narrow-TB admission) — a width FLOOR, not a
free wire.

---

## The binding chain for the deployed normal core (followed wire-by-wire)

The deployed effect-VM leg is `"effect-vm-rotated"`, a multi-table `Ir2BatchProof` resolved
selector-bound and verified by the audited IR-v2 batch verifier
(`sdk/src/full_turn_proof.rs:4485` → `verify_effect_vm_rotated_with_cutover`,
`full_turn_proof.rs:3878`). The verifier iterates the WIDE registry FIRST and binds the
leg's LAST 16 PIs as the 8-felt before/after commit (`full_turn_proof.rs:3942`, `4619-4674`).
The v1 hand-AIR `"effect-vm"` arm is RETIRED (`full_turn_proof.rs:4476-4478`).

I traced the actual deployed `transferVmDescriptor2R24` from the committed registry TSV
(`circuit/descriptors/rotation-wide-registry-staged.tsv`: 57 descriptors;
`trace_width=817`, `public_input_count=62`; tables main / `poseidon2_chip` / `range`/30 /
`memory`; constraint census = 45 gates, 14 range, 25 PI-bindings, 68 lookups).

1. **The gates read the v1 state columns.** The transfer balance gate is
   `var[76] − var[54] − var[68] + 2·var[69]·var[68]` (after_balance_lo − before_balance_lo
   − amount + sign·amount), i.e. it computes over `STATE_AFTER_BASE+BALANCE_LO=76`,
   `STATE_BEFORE_BASE+BALANCE_LO=54`, and the param columns (`columns.rs:193-208`). The
   gates do NOT read free wires; they read the v1 state/param columns.

2. **The committed wires are welded in-circuit to those v1 columns.** `fill_block`
   (`circuit/src/effect_vm/trace_rotated.rs:1785-1821`) is the PRODUCER copy of the v1 state
   into the rotated block columns; the binding that makes it non-forgeable is a set of
   equality GATES in the deployed descriptor. Detected (every weld present, both blocks):

   - BEFORE block (base 188): `(189,54)` r0=balance_lo, `(190,56)` r1=nonce, `(191,55)`
     r2=balance_hi, `(192..199)=(57..64)` r3..r10=fields[0..8], `(213,65)` cap_root.
   - AFTER block (base 239): `(240,76)`, `(241,78)`, `(242,77)`, `(243..250)=(79..86)`
     fields, `(264,87)` cap_root.

   These are `t:"gate"` constraints of the form `add(var A, mul(const −1, var B))` ⇒ A==B,
   evaluated by the verifier (`descriptor_ir2.rs::eval_lean_expr`). So the rotated limb
   columns (which the commit absorbs) are FORCED equal to the v1 columns the gates compute
   over — they are NOT independent free wires.

3. **The committed wires absorb into the 8-felt commit via a co-proven Poseidon2 chip.**
   `fill_wide_block` (`trace_rotated.rs:2748-2799`) chains the rotated limbs through chip
   absorbs: arity-4 head over the BEFORE-block head limbs, arity-11 body folds, arity-11
   final folding the iroot. Confirmed in the deployed descriptor's lookups (table 1):
   - head carrier `out[609..616]` ← arity-4 chip lookup over inputs `[188,189,190,191]`
     (the welded rotated head limbs);
   - commit carrier `out[705..712]` (BEFORE) ← arity-11 chip lookup over `[697..704, 225]`
     (prev carrier ‖ iroot col `BEFORE_BASE+B_IROOT=225`);
   - commit carrier `out[809..816]` (AFTER) ← arity-11 over `[801..808, 276]`.
   Each lookup's table side is the chip AIR; the chip is **co-proven**, not a free table —
   see "Lookup buses" below.

4. **The 8-felt commit columns are pinned to the published PIs.** The descriptor's
   `pi_binding` constraints pin `PI[46..53] ← cols 705..712 (first row)` and
   `PI[54..61] ← cols 809..816 (last row)` — the LAST 16 PIs. `append_wide_carriers`
   (`trace_rotated.rs:2848-2889`) reads exactly those columns into the published dpis;
   the retired 1-felt rotated commit PIs are ZEROed (`trace_rotated.rs:2862-2875`).

5. **The light client binds those PIs to its trusted pre/post commit.**
   `verify_full_turn_bound` extracts the leg's last 16 PIs as `(before8, after8)`
   (`full_turn_proof.rs:4647-4674`) and rejects unless `proof_old_commit == expected_old_commit`
   / `proof_new_commit == expected_new_commit` (`full_turn_proof.rs:4682-4695`), with chain
   adjacency for heterogeneous turns (`4700-4710`). `expected_*` are supplied by the caller
   from trusted state, never from the proof.

**Net:** gate-read v1 cols ⟸(weld gate)⟹ rotated limb cols ⟸(co-proven chip lookup)⟹ 8-felt
commit carrier cols ⟸(pi_binding)⟹ published PIs ⟸(verifier eq)⟹ light-client trusted
commit. Every link is an in-circuit constraint or a verifier equality. The arithmetic is
**compute-over-bound-wires**, not attest-over-free-wires.

### The cross-proof bindings are over committed PIs, not free felts

- Auth→EffectVM cell binding: `auth.state_root == effect.OLD_COMMIT`
  (`full_turn_proof.rs:4761-4789`); auth derived_hash == effect-action binding
  reconstructed from `PI[EFFECTS_HASH]` (`4791-4829`). Both sides are in-circuit-pinned PIs.
- Freshness (a): `revoc.revocation_root == expected canonical root`
  (`full_turn_proof.rs:4851-4877`); (b): `revoc.queried_item == effect nullifier`
  (`4880-5000`). The queried item is pinned in-circuit to the bracketed control row
  (the circuit crate's `dsl/revocation.rs`, since DELETED with the rest of the 1-felt
  non-revocation rail — freshness now rides the limb-26 `.absent` map-op), not a free felt.
- Cap-membership: `pi[CAP_ROOT] == caller's canonical capability_root` and
  `pi[LEAF_DIGEST] == digest of receipt-disclosed leaf` (`full_turn_proof.rs:5023-5060`).
  Both pinned in-circuit (row-0 / last-row boundaries); the AUTHORITY FLOOR forces a cap
  effect onto its cap-open descriptor (the in-circuit depth-16 membership crown), rejecting
  the plain cap descriptor that carries no membership check (`full_turn_proof.rs:3976-3984`).

---

## The lookup buses — every deployed bus has BOTH sides constrained over a co-proven table

The batch verifier builds the AIR set ITSELF from the descriptor + its own code
(`verify_vm_descriptor2_with_config`, `circuit/src/descriptor_ir2.rs:4822`):
`instance_airs(desc, layout, presence)` (`4836`), then requires
`proof.degree_bits.len() == airs.len()` (`4837-4844`) — the prover supplies no AIR shapes,
and only PRESENT (referenced) tables are committed (`Presence::of`, `4835`). So an unused
declared table (e.g. `memory` in the transfer descriptor — declared but 0 lookups) is NOT a
free bus; it is simply not in the batch.

| Bus | Table side | Query side | Classification |
|---|---|---|---|
| Poseidon2 chip (table 1) | `Ir2Air::Chip` — every row pinned to the REAL Poseidon2 round constraints (`descriptor_ir2.rs:15`, `1795-1850`); params validated against deployed pins (`649-662`) | main-AIR `lookup` queries (66 in the transfer desc) | co-proven AIR = `ChipTableSound`, justified in-circuit, resting on `StarkSound`. **OK** |
| Range/byte (table 2, 30-bit) | byte-table AIR pins value=row index; HEIGHT pinned to `LIMB_BITS` (`descriptor_ir2.rs:4845-4860`) so a taller table cannot widen the range | 2 range lookups + 14 `range` constraints | co-proven, height-pinned. Prior audit confirmed the recomposition tooth. **OK** |
| memory / map_ops / umem* | co-proven AIRs when present (`instance_airs`); NOT present in the deployed transfer leg | n/a here | **OK / not on this leg** |

The LogUp argument soundness (a balanced bus ⟹ each query is a real table entry) is the
p3-lookup carrier, subsumed into `StarkSound` (no separate dregg theorem; consistent with
the AIR-composition audit). **No deployed bus has an unconstrained/free side.**

---

## Carried floors (classified — standard crypto carriers, OK, NOT free wires)

These are the named assumptions the deployed soundness rests on. Each is a standard crypto
primitive or a co-proven-AIR, NOT a prover-chosen free input wire:

1. **`StarkSound`** — FRI/p3 batch-STARK knowledge extraction (incl. the LogUp legs).
   `metatheory/.../CircuitSoundness.lean:382`. Standard.
2. **`Poseidon2SpongeCR`** — Poseidon2 collision resistance. `Poseidon2Binding.lean:169`.
   Standard. (The 8-felt commit is genuine independent squeezes ⇒ ~124-bit, matching the
   FRI floor — `effect_vm/pi.rs:15-23`.)
3. **`ChipTableSound`** — the Poseidon2 chip AIR computes the real permutation per row
   (the table side of every hash lookup). Co-proven in-circuit by the round constraints;
   reduces to `StarkSound`. Standard carrier.
4. **Range/byte bus** — co-proven, height-pinned to `LIMB_BITS`. Standard carrier.
5. **`DeployedFaithful`** — deployed-tree faithfulness for the cap-root / nullifier
   accumulator roots (`DeployedCapTree.lean:299`). Standard structure (the roots the light
   client trusts are the canonical ones).

None of these is an unbound input wire. This matches the AIR-composition audit's carrier
list; this audit extends it to the chip + memory buses and the full wide-commit chain.

---

## Real findings / honestly-named seams in the DEPLOYED path

### FINDING 1 (Medium→Low-Medium) — house-capacity SATISFACTION: dodge CLOSED, satisfaction VK still the residual

The capacity-gate SATISFACTION constraints (e.g. the sealed-escrow gate: both legs
Deposited before, Consumed after) are still NOT in any committed VK — the deployed
satisfaction check is the OFF-AIR re-evaluation `verify::verify_slot_caveat_manifest` (the
`SETTLE_ESCROW` arm), which reads **CALLER-supplied** `initial_fields`/`final_fields`
8-felt slot views a pure light client does NOT bind
(`circuit/src/effect_vm/satisfaction_weld.rs` header, its STAGED block). But the
**bare-descriptor dodge the original finding turned on is CLOSED, two ways, both
deployed:**

- **GATE A (in the committed VK bytes):** the bare-floor refuse weld
  (`circuit/src/effect_vm/bare_floor_refuse_weld.rs`, §FLIPPED) welds per-capacity-tag
  `floor == 0`-refuse gates onto every deployed bare cohort member — the committed cohort
  rows carry the `-gentian-deployed-bare-refuse` suffix — so a cell whose committed
  manifest DECLARES a capacity is UNSATISFIABLE under the bare descriptor.
- **GATE B (in the deployed verifier, geometry-free):** a declared-capacity turn that
  binds a bare cohort descriptor is rejected by name
  (`required_satisfaction_member`, `sdk/src/full_turn_proof.rs:4330,4484`), independent of
  the refuse weld. Inert for the pure-LC entry (no declaration in hand) and for
  non-declaring cells.

The welded satisfaction members exist as committed staged-registry descriptors
(`settleEscrowSat`/`dischargeSat`/`vaultSatVmDescriptor2R24`,
`circuit/src/effect_vm/trace_rotated.rs:2722,2758,2764`) with declaration-keyed routing
(`rotated_descriptor_name_for_declared_capacity`, `trace_rotated.rs:2809`).

- **Bound today:** the capacity COVERAGE carrier (`caveatCommit` → the wide commit), so
  the manifest cannot be OMITTED; and the dodge — a declared-capacity turn cannot verify
  under a bare cohort member.
- **NOT bound today (pure light client):** that the gate HELD over the committed state.
  The satisfaction members carry **no wide twin, no producer, no committed VK yet**
  (`trace_rotated.rs:2716-2722`, the §6 BLOCKER-1 note), so satisfaction is witnessed only
  by a verifier holding the committed-state opening.
- **Severity:** Low-Medium, scoped to capacity-gated cells (escrow/vault/obligation/...).
  The dodge is closed fail-closed; the residual is the missing satisfaction-member VK
  (a liveness + pure-LC-witnessing gap, not a forgery path).
- **Fix (named residual):** emit the satisfaction members' wide twins + producer, commit
  their VKs, flip the live path (`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6).

### FINDING 2 (Low) — custom-effect sub-proof: binding enforced IN-CIRCUIT; host-state weld live on the per-turn entry; residual = chain-fold wiring

The original finding's mechanics are superseded. The off-AIR `verify_proof_bind` engine is
DELETED (stark-kill `dd038c08e` — `circuit-prove/src/custom_proof_bind.rs:30-35`); nothing
in the tree verifies a proof-bind off-AIR. The binding lives IN-CIRCUIT: the chain prover's
custom fold arm (`prove_custom_binding_node_segmented`,
`circuit-prove/src/joint_turn_recursive.rs:595`, wired into `prove_chain_core_rotated` at
`ivc_turn_chain.rs:2868`) folds the effect-vm leg as a DUAL-EXPOSE leaf — the claimed
commitment published at IR2 PI slots 46..53 — with the custom sub-proof leaf, whose
commitment is computed in-circuit from the sub-proof's real PIs, and `connect`s them lane
by lane. A turn whose effect-vm row claims a commitment no verifying sub-proof backs is
UNSAT: no root proof exists, and a pure light client never receives a verifying artifact.
The commitment is the full **8-felt** `WideHash` class (~124-bit birthday;
`PROOF_BIND_COMMIT_WIDTH = 8`, `custom_proof_bind.rs:90`), with old 4-felt custom
artifacts REFUSED at the versioned admission boundary (`require_custom_commit_teeth_v2`).

The host-state semantic link, per entry point:

- **Per-turn (the deployed executor entry): BOUND.** The sole rotated proof-carrying
  verify path (`verify_and_commit_proof_rotated`, `turn/src/executor/proof_verify.rs:524`)
  enforces the custom-proof state-binding weld fail-closed BEFORE any leg verify —
  `enforce_custom_proof_state_binding(turn, stored_old8, claimed_new8)`
  (`proof_verify.rs:620`), plus the entry weld `enforce_custom_proof_entry_binding`
  (`proof_verify.rs:415`) — pinning the sub-proof's state I/O to the host's committed
  pre/post state.
- **Chain-fold (in-circuit): the mechanism exists; the deployed arm does not wire it.**
  `prove_custom_binding_node_state_segmented`
  (`circuit-prove/src/joint_turn_recursive.rs:653`) welds the custom leaf's exposed
  `[old8 ‖ new8]` prefix (`prove_custom_leaf_with_state_commitment`,
  `CUSTOM_STATE_CLAIM_LEN = 24`, fail-closed on an 8-lane commitment-only leaf) to the
  leg's real `SEG_FIRST_OLD`/`SEG_LAST_NEW` lanes, with in-lib both-polarity tests. The
  deployed custom arm of `prove_chain_core_rotated` folds through the commitment-only
  `prove_custom_binding_node_segmented` (`ivc_turn_chain.rs:2868`) — there the fold proves
  "program P verified over PIs committing to C, and C is the committed column" without
  the state weld.

- The residual is **load-bearing only on the chain-fold path**, and only if an application
  relies on the custom sub-proof to constrain host state (e.g. "this transfer is valid per
  program P over THIS cell's balance"). The host's own Custom-effect state mutation is
  EffectVM-constrained, so this is not a free-wire forgery of the core transition — it is
  the un-wired state weld for the foreign attestation on that one arm.
- Automation note: the deployed end-to-end fold poles (honest-accept + forged-reject
  through `prove_turn_chain_recursive`) are `#[ignore]`d tests not run in CI
  (`custom_proof_bind.rs:46-53`); the per-lane forgery tooth
  (`every_forged_commitment_lane_is_rejected_by_the_fold`) runs on plain `cargo test`.
- **Severity:** Low; flag so integrators know the deployed chain-fold custom arm binds
  the commitment only — the per-turn executor entry pins the sub-proof's state I/O to
  host state fail-closed.
- **Fix (named seam):** wire `prove_custom_binding_node_state_segmented` into
  `prove_chain_core_rotated`'s custom arm (the state-claim leaf and the fold node exist
  and are tested; the wiring is the residual).

### FINDING 3 (Low) — cap-open narrow residual: a 1-felt (~31-bit) ACCEPTANCE floor (not a free wire)

Every live cap-open key — the authority crown, the §10 WRITE tail, AND the turn-bound
`transferCapOpenTB` — has a proven wide twin in the wide registry, and the producer routes
them all wide (`sdk/src/full_turn_proof.rs:2999-3006`; `node/src/turn_proving.rs:1328-1341`),
so an honest cap-gated turn publishes the full 8-felt (~124-bit) commit. The 1-felt commit
persists on the ACCEPTANCE side: the verifier's wide-twin predicate excludes the TB family
(`cap_open_key_has_wide_twin`, `full_turn_proof.rs:2706-2718`), so a narrow
`transferCapOpenTB` V3 leg survives the fallback filter (`full_turn_proof.rs:4446-4455`)
and binds at its single `PI[OLD_COMMIT]`/`PI[NEW_COMMIT]` felt broadcast into slot 0 of the
8-felt anchor (the `leg_commit` narrow branch, `full_turn_proof.rs:5123+`); the
no-rotation-witness producer path likewise emits a 1-felt commit
(`turn_proving.rs:1350`). This is **not a free wire** — the 1-felt commit is pinned
in-circuit to those PIs; it is a COMMITMENT-WIDTH floor (~31-bit vs the ~124-bit wide
core). The wide-dodge reject tooth forces every NON-TB cap-open key onto the wide route,
confining the floor to the named residual.
- **Severity:** Low; cap-gated turns only; classification = bit-width calibration/floor.
- **Fix (named residual):** extend the verifier's wide-twin predicate (and so the reject
  tooth) over the TB family, and retire the no-rotation-witness 1-felt fallback.

### NOTE (deployment placement, not a wire bug) — where custom-proof verify lives per entry point

A per-turn verifier running only `verify_full_turn_bound` does NOT verify custom sub-proofs
in steps 1–9 (custom effects are absent from that flow); on that entry they are enforced by
the executor (`turn/src/executor/proof_verify.rs`, `enforce_custom_effect_proofs`). On the
chain-fold path the binding is in-circuit (FINDING 2): a light client folding the recursion
tree needs no extra check. An integrator on the per-turn entry runs the executor check too —
an architectural placement, not a free-wire hole.

---

## Bottom line on "compute vs attest" for the DEPLOYED path

The deployed normal-core circuit **computes** its state-transition arithmetic over wires
that are bound, link-by-link, to the published 8-felt ~124-bit commit and thence to the
light client's trusted pre/post state. The gate-read columns are welded in-circuit to the
commit-absorbed columns; the absorb is a co-proven Poseidon2 chip; the commit PIs are
pinned and verifier-bound; the cross-proof PIs (auth, freshness, cap-membership) are all
over in-circuit-pinned roots, not free felts; every deployed lookup bus has both sides
constrained over a co-proven table. There is **no attest-over-free-wires forgery hole in the
deployed core arithmetic**.

The honest residue is three named, tracked seams: the capacity-satisfaction member lacks a
committed VK/producer (the bare-descriptor dodge itself is closed in the deployed VK bytes
and the verifier), the custom sub-proof's state I/O is pinned to host state on the
deployed per-turn executor entry — its 8-felt commitment in-circuit via the recursion
fold — with the deployed chain-fold custom arm binding the commitment only (the
state-binding fold node exists and is tested; wiring it into that arm is the named
residual), and the cap-open narrow residual keeps a ~31-bit commit floor on the
acceptance side (narrow-TB admission + the no-rotation-witness fallback). None is a
forgeable free input wire in the core; the first is a
pure-light-client-vs-opening-verifier gap, the second a chain-fold wiring residual, the
third a width floor.
