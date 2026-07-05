# Compute-vs-Attest / Input-Wire-Binding Audit (the DEPLOYED circuit)

> **⚠ GEOMETRY STALE (post-v12/v13-geom regen) — the CONCLUSIONS still hold, the NUMBERS do not.**
> This audit traced the `transferVmDescriptor2R24` geometry as of 2026-06-28
> (`trace_width=817`, `public_input_count=62`). The v12-geom and v13-geom big-bang regens have
> since widened it: the committed row now shows **`trace_width=2495`, `public_input_count=68`**,
> and the AFTER-carrier base moved (≈151→227). So every CONCRETE column index below (the BEFORE
> block base 188, AFTER block base 239, commit carriers 705..712/809..816, and the `PI[46..53]`/
> `PI[54..61]` last-16-PI cites) is **pre-regen and must be re-traced** — with `pi_count=68` the
> "last 16 PIs" are indices 52..67. The load-bearing verdict is UNCHANGED: the deployed core
> computes over root-bound wires, and the three named seams (§Real findings) remain staged/tracked.
> Only the specific column/PI numbers are stale; treat them as "as of 2026-06-28". (The balance
> gate `var[76]−var[54]−var[68]+2·var[69]·var[68]` itself survived the regens intact.)

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
deployed normal-core arithmetic**. Three honestly-named seams remain, all already tracked:
(1) house-capacity SATISFACTION is STAGED, not deployed — the deployed gate re-evaluates
over CALLER-supplied slot views a pure light client does not bind; (2) the custom-effect
sub-proof's PUBLIC INPUTS are not cross-bound to the host cell's state (the commitment is
bound; its relation to host state is not); (3) the cap-open narrow residual carries a
1-felt (~31-bit) commit, a width FLOOR (not a free wire) for cap-gated turns lacking a wide
twin.

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
  (`circuit/src/dsl/revocation.rs`), not a free felt.
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

### FINDING 1 (Medium) — house-capacity SATISFACTION is STAGED, not deployed

The capacity-gate SATISFACTION constraints (e.g. the sealed-escrow gate: both legs
Deposited before, Consumed after) are NOT in any committed VK. The deployed gate is the
OFF-AIR re-evaluation `verify::verify_slot_caveat_manifest` (the `SETTLE_ESCROW` arm), which
reads **CALLER-supplied** `initial_fields`/`final_fields` 8-felt slot views — a pure light
client does NOT bind those (`circuit/src/effect_vm/satisfaction_weld.rs:12-30`). The in-AIR
fix (`settle_escrow_satisfaction_gates`, `satisfaction_weld.rs:85-111`) and its selector
forcing (the GENTIAN keystone, `circuit/src/effect_vm/authority_digest_weld.rs` header) are
explicitly **STAGED — built BESIDE the deployed, NOT flipped, NOT in a committed VK**
(`satisfaction_weld.rs:21-30`, `authority_digest_weld.rs:27-37`).

- **Bound today:** the capacity COVERAGE carrier IS deployed (`caveatCommit` → the wide
  commit), so the manifest cannot be OMITTED — a light client witnesses *presence*
  (`satisfaction_weld.rs:7-10`).
- **NOT bound today (pure light client):** that the gate HELD over the committed state. A
  verifier holding the committed-state opening witnesses it (the cap-membership posture);
  a commitments-only light client does not.
- **Severity:** Medium, scoped to capacity-gated cells (escrow/vault/obligation/...).
  This is attest-over-caller-supplied-inputs for capacity SATISFACTION specifically — not a
  forgeable free wire in the core arithmetic, but a real gap between "verifier with opening"
  and "pure light client."
- **Fix (named, in progress):** the gated VK epoch — emit `settleEscrowSatVmDescriptor2R24`
  with the four satisfaction gates + the GENTIAN selector forcing, commit its VK, flip the
  live path. (`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6 + flip plan.)

### FINDING 2 (Low-Medium) — custom-effect sub-proof PUBLIC INPUTS not cross-bound to host state

`verify_proof_bind` (`circuit-prove/src/custom_proof_bind.rs:237-282`) binds, for a Custom
effect: (1) the program resolves by the committed `vk_hash` column, (2) the program's
self-computed VK equals it, (3) the sub-proof VERIFIES under the program's AIR, (4) the
sub-proof's PI **commitment** equals the committed `custom_proof_commitment` column. That
column is a turn param ⇒ bound into the turn hash and the effects_hash (so it cannot be
swapped post-hoc, and it is reachable from the auth derived_hash binding).

What is NOT bound: the sub-proof's **public inputs themselves** to the host cell's pre/post
commit. The in-AIR `ProofBind` op is only a bounds check
(`custom_proof_bind.rs:6-16`; `descriptor_ir2.rs:469-481,572` — `ProofBindSpec` carries only
`guard`/`commit`/`vk`, no host-state wiring); the recursion + commitment-equality is an
OFF-batch check the executor/verifier runs (`enforce_custom_effect_proofs`, the AIR-comp
audit's FINDING 1 path), not part of the main batch STARK. So the sub-proof attests
"program P verified over PIs committing to C" — the relation between those PIs and the
ACTUAL host state transition is not enforced in-circuit.

- This is **load-bearing only if** an application relies on the custom sub-proof to
  constrain host state (e.g. "this transfer is valid per program P over THIS cell's
  balance"). The host's own Custom-effect state mutation is still EffectVM-constrained, so
  this is not a free-wire forgery of the core transition — it is a missing semantic link
  for the foreign attestation.
- Secondary: the `custom_proof_commitment` is **4 felts (~62-bit)** over adversary-chosen
  PIs (`custom_proof_bind.rs:61-70`) — a named bit-width floor, collision-relevant, to
  rotate to 8 felts in a dedicated effect-VM descriptor pass.
- **Severity:** Low-Medium / by-design boundary; flag so integrators know the custom
  sub-proof does not pin its I/O to host state.
- **Fix:** wire the sub-proof's state-I/O public inputs to the host `OLD_COMMIT`/`NEW_COMMIT`
  columns in the `ProofBind` op (a VK-affecting descriptor change) if the intended semantics
  require host-state binding; widen the commitment to 8 felts.

### FINDING 3 (Low) — cap-open narrow residual: a 1-felt (~31-bit) commit WIDTH FLOOR (not a free wire)

A cap-gated turn whose key lacks a proven wide twin (today `transferCapOpenTB`) verifies via
the V3 fallback (`full_turn_proof.rs:3951-3962`), and its commit is the 1-felt
`PI[OLD_COMMIT]`/`PI[NEW_COMMIT]` broadcast into slot 0 of the 8-felt anchor
(`full_turn_proof.rs:4664-4673`). This is **not a free wire** — the 1-felt commit is pinned
in-circuit to those PIs; it is a COMMITMENT-WIDTH floor (~31-bit vs the ~124-bit wide core)
for that narrow tail. The reject tooth (`full_turn_proof.rs:3953-3961`) forces any cap-open
key that HAS a wide twin onto the ~124-bit wide route, so the floor is confined to the named
residual.
- **Severity:** Low; cap-gated turns only; classification = bit-width calibration/floor.
- **Fix:** land the wide twin for the remaining cap-open keys (in progress per the wide
  registry weld).

### NOTE (deployment placement, not a wire bug) — custom-proof verify is off the main batch

A pure light client running only `verify_full_turn_bound` does NOT verify custom sub-proofs
in steps 1–9 (custom effects are absent from that flow); they are verified by the executor's
`verify_and_commit_proof` / `enforce_custom_effect_proofs`. This is an architectural
placement to be aware of for a light-client integrator (run the custom-proof check too), not
a free-wire hole.

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

The honest residue is three named, already-tracked seams: capacity SATISFACTION is staged
behind the gated VK epoch (deployed gate reads caller-supplied slot views), the custom
sub-proof's I/O is not pinned to host state (its commitment is), and the cap-open narrow
residual carries a ~31-bit commit floor. None is a forgeable free input wire in the core;
the first is a pure-light-client-vs-opening-verifier gap, the second a missing foreign-proof
semantic link, the third a width floor.
