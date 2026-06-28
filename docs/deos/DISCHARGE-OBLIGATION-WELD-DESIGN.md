# DischargeObligation weld — making per-period discharge light-client-witnessed

This is the design for the **second house-capacity in-circuit weld** (#5, the standing
obligation), built immediately after the SettleEscrow weld
(`docs/deos/SETTLE-ESCROW-WELD-DESIGN.md`) and following its exact shape. It binds the standing
obligation's per-period discharge invariant into what a **light client** verifies, not just what a
re-executing validator checks out of band. It is built **STAGED** — beside the deployed default,
with the AIR constraint polynomials (the VK bytes) **unchanged** — exactly the way the temporal-caveat
verifier arms and the sealed-escrow tag-17 arm were landed.

## 1. What is witnessed today, and the gap

The standing obligation (`cell/src/obligation_standing.rs`, Lean
`metatheory/Dregg2/Deos/StandingObligation.lean`) is a cell that OWES `amount` to a beneficiary every
`period` blocks, starting at `start`. A committed `next_due` cursor (`start + k·period`), a discharged
count, and a cumulative discharged total live in reserved heap slots (`OBLIGATION_COLL`) folded into
the cell's canonical state commitment by the proven sorted-Poseidon2 `Heap.root`. The capacity's
soundness — no early discharge, no double-discharge (one-shot per period), no over/under-pay, no
silent skip — is proven at the **executor** altitude (§3–§6 of the Lean rung): a verifier holding the
committed heap consults `ObligationState::check_discharge` / `audit` and rejects every forge.

The **gap** is light-client altitude. A light client verifies a *batch proof* against the VK and
public inputs; it does **not** re-run the discharge check. So today the heap-root TRANSITION is
proven (the commitment moved), but the *gate* — that the discharge was DUE, advanced the one-shot
cursor by exactly one period, and paid exactly the schedule amount — is enforced only by a
re-executing validator. The weld closes that: a satisfying batch witness must **force** the per-period
shape, so a light client sees the schedule honored as part of the proven kernel transition. This is
the slice the subscription migration (`a22b7ff`) flagged as the named next `Effect::DischargeObligation`
weld.

## 2. The in-circuit gate (the design)

The natural temptation is "add a `DischargeObligation` `Effect` variant with new AIR columns." That is
**VK-affecting and large** (a new effect, descriptor, trace columns, AIR polynomials). We do not do
that. Instead we reuse the **manifest-in-public-inputs + off-AIR re-evaluation** vehicle that already
stages slot caveats (`circuit/src/effect_vm/verify.rs::verify_slot_caveat_manifest`, tags 1–17): the
executor projects the declared gate into PUBLIC INPUTS, and any proof consumer (receipt verifier,
third-party validator, light client) re-runs the gate against the bound `state_before`/`state_after`
views. Tampering with the manifest, the state-before/after, or the cell-program declaration surfaces as
a verifier-side rejection. **The AIR constraint polynomials are unchanged**, so the VK bytes are
unchanged; only the verifier's manifest-evaluation code grows an arm.

### 2.1 Why a NEW tag (not existing entries)

Per-period discharge is a *joint* invariant: "the discharge is DUE **and** the cursor advanced by
exactly one period **and** the total advanced by exactly the amount." The existing per-slot caveats
(`StrictMonotonic`, `FieldDelta`, `TemporalGate`, …) each bind ONE aspect of ONE slot
*independently*: `StrictMonotonic{cursor}` would force the cursor to move but not by exactly one
period; `FieldDelta{total, amount}` would force the exact total advance but not the due condition; a
`TemporalGate` would force a height bound but not tie it to the committed cursor. A forge could satisfy
each independently while violating the joint shape — discharging early, or skipping a period, or
paying the wrong amount on a moved cursor. The gate must read **all three** slots across the
transition in **one** entry. Hence a new tag, `SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION = 18`, with params
naming the due and total slots and the schedule constants, asserting:

```
block_height >= before[due_slot]                       (DUE)
∧ after[cursor_slot] == before[cursor_slot] + period   (ADVANCED one period)
∧ after[total_slot]  == before[total_slot]  + amount   (EXACT amount)
```

This is the Lean `DischargeGate t before after clock cb tb` — a single conjunctive entry whose accept
**forces** the per-period shape (`discharge_gate_forces_due_exact`) and whose failure on any one leg
refuses the early / wrong-amount / non-advanced step
(`discharge_gate_early_rejected` / `wrong_amount_rejected` / `cursor_not_advanced_rejected`).

### 2.2 The plane: field-mirrored schedule slots

The slot-caveat manifest reads the cell's slot-0..7 4-byte field views
(`initial_fields`/`final_fields`). The obligation's cursor/total live in a heap *collection*, not those
eight field slots. As with SettleEscrow stage (a):

- **Field-projected (this stage).** The obligation cell program mirrors its `next_due` cursor, the
  current period's due block, and the cumulative discharged total into three of its 8 field-slots (in
  addition to the heap). The `DischargeObligation` entry names those slot indices and the existing
  `initial_fields`/`final_fields` plane carries them. Smallest change; the heap remains the source of
  truth and the field mirror is what the AIR-teeth view binds.
- **Heap-plane (the named second stage).** Carry the cursor/total heap openings (`(OBLIGATION_COLL,
  KEY_NEXT_DUE / KEY_DISCHARGED_TOTAL)` against the cell's `heap_root` before and after) directly as
  manifest witnesses. Higher fidelity, slightly more plumbing.

Either way the **soundness is the same Lean rung** (§6b): the gate over a (before, after) pair, its
due/exact/advanced teeth, and the root-transport tooth that ties the verdict to the committed roots a
light client already has bound in public inputs.

### 2.3 The binding that makes it light-client-witnessed

The light client holds the before/after **committed roots** (the ledger/heap roots in the batch
public inputs). The weld's load-bearing tooth, `discharge_gate_root_bound`, proves the gate verdict is
a **function of those roots**: equal-root before/after views yield the same verdict (via
`cursor_bound_in_root` / `total_bound_in_root`, direct `Heap.root_binds_get` instances). So a forger
who presents fake cursor/total slots to fake a gate-pass must publish a **different root** — where the
§6 binding bites. The light client therefore cannot be shown an accepting `DischargeObligation` entry
over the honest roots unless the discharge genuinely honored the schedule.

## 3. The Lean rung — BUILT, `#assert_axioms`-clean

Landed in `metatheory/Dregg2/Deos/StandingObligation.lean` §6b, beside the executor teeth, reusing the
file's proven heap lemmas (no new mathematics, the one named `Poseidon2SpongeCR` floor):

| Theorem | What it proves | Role |
|---|---|---|
| `DischargeGate` | the transition gate (due ∧ cursor advanced one period ∧ total advanced by amount) | the off-AIR re-evaluation, as a predicate over a (before, after) pair |
| `discharge_passes_gate` | an honest due discharge satisfies the gate | non-vacuity (accept polarity) — the rung is not true-by-no-witness |
| `discharge_gate_forces_due_exact` | gate accept ⟹ due ∧ cursor advanced ∧ total exact | **the schedule tooth** — no accepting witness skips, over/under-pays, or fails to advance |
| `discharge_gate_early_rejected` | clock below the due block ⟹ gate refuses | **the no-early tooth** — paying before due is inexpressible |
| `wrong_amount_rejected` | total not advanced by exactly the amount ⟹ gate refuses | **the no-over/under tooth** |
| `cursor_not_advanced_rejected` | cursor not advanced by one period ⟹ gate refuses | **the one-shot tooth** — a replay that does not move the cursor is refused |
| `discharge_gate_root_bound` | equal before/after roots ⟹ same gate verdict | **the light-client tooth** — a forger must move a root, where §6 bites |

Non-vacuity `#guard`s (both polarities) compute on the reference sponge: the honest opened→stepped
discharge passes; an early (clock 999 < due 1000) discharge fails; a wrong-amount (`wrongAmt`, total
9999) discharge fails; a non-advanced (`notAdvanced`, cursor reverted to 1000) discharge fails.
`#assert_all_clean` pins all of §6b kernel-clean alongside the §3–§6 executor teeth (23 keystones
total).

This is the soundness the verifier arm **inherits** — precisely as the temporal-caveat arms (verify.rs
tags 13–16) inherit `temporalStateStepGuarded` and the sealed-escrow arm (tag 17) inherits
`SettleGate`. The Lean rung is the proof; the Rust arm is its mechanical shadow.

## 4. VK impact — NONE (staged), and the named flip

- **AIR / VK bytes: unchanged.** The gate is carried in public inputs and enforced by an **off-AIR**
  verifier check (the manifest re-evaluation), so the constraint polynomials — hence the VK — are
  byte-identical. The same property the slot-caveat manifest (tags 1–17) already has. `pi_v3` drift
  guard (`BASE_COUNT`) and the descriptor fingerprints stay green: tag 18 is a tag VALUE, not a
  PI-layout offset.
- **What an old verifier does:** rejects `type_tag = 18` as `unknown type_tag` (the existing
  `other =>` arm in `verify_slot_caveat_manifest`). So a cell that *declares* a `DischargeObligation`
  caveat can only be verified by an upgraded verifier — a **lockstep epoch**, the
  **standing-obligation verifier epoch**.
- **Deployed default: unchanged.** No existing obligation cell declares the new caveat (the live
  capacity discharges via the executor check), so nothing flips by default. The epoch is the
  coordinate-with-future-rollout step, deliberately deferred — the same posture as the SettleEscrow
  (tag 17), the temporal-caveat, and the umem VK epochs.

**The named gated VK-flip (future coordinated epoch):** *standing-obligation verifier epoch.* Land the
projection + verifier arm (done, §5) behind the new tag, ship the upgraded verifier to all consumers,
then allow obligation cells to declare `DischargeObligation`. Because the VK bytes are unchanged, this
is a *verifier-code* rollout, not a proving-key rotation — the lighter of the two epoch shapes. It
coordinates with the SettleEscrow, temporal-caveat, and umem epochs: **one verifier-upgrade window can
carry all the off-AIR manifest tags (17, 18, 13–16) at once.**

## 5. The precise staged-build plan (VK-risk-free, in order) — landed

1. **(DONE)** the Lean rung — `StandingObligation.lean` §6b, `#assert_all_clean`, green.
2. **(DONE)** `pub const SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION: u32 = 18;` in
   `circuit/src/effect_vm/pi.rs` beside the existing tags. **No AIR change** — a tag VALUE.
3. **(DONE)** a verifier arm in `verify_slot_caveat_manifest` (`circuit/src/effect_vm/verify.rs`)
   reading the cursor from `slot_index` (old_v/new_v), the due-block from `initial_fields[p0]`, the
   total from `initial_fields[p1]`/`final_fields[p1]`, the period from `p2` and amount from `p3`, and
   asserting the `DischargeGate` conjunction (due via `block_height`, cursor advanced by `period`,
   total advanced by `amount`), value-for-value mirroring the Lean teeth, fail-closed on
   out-of-range due/total slots. The `other =>` unknown-tag arm gives the lockstep-epoch rejection
   for old verifiers. There is ALSO an executor-side scalar evaluator arm (`cell/src/program/eval.rs`,
   the `StateConstraint::DischargeObligation` case, using `ctx.block_height` as the clock) so the gate
   is enforced out-of-band as well as in the manifest.
4. **(DONE)** a projection arm in `turn/src/executor/mod.rs::project_slot_caveat_manifest` that, for a
   cell declaring `StateConstraint::DischargeObligation { cursor_slot, due_slot, amount_slot, period,
   amount }`, emits the tag-18 entry (`slot_index = cursor_slot`, `params = [due_slot, amount_slot,
   period, amount]`). Additive and gated by the new caveat being declared, dead-by-default.
5. **(DONE)** teeth tests: `circuit/tests/discharge_obligation_air_teeth.rs` (both polarities — honest
   due discharge passes; early / over / under / non-advanced / over-advanced refused; out-of-range
   due/total slot fail-closed) and `turn/tests/discharge_obligation_projection.rs` (projection
   round-trip end-to-end). The new `StateConstraint::DischargeObligation` variant also rides the
   existing coverage teeth (`cell/src/program/tests.rs` view/serde totality;
   `teasting/.../protocol_coverage_gate.rs` ratchet 21 → 22).
6. **(future epoch only)** the standing-obligation verifier epoch: ship the upgraded verifier, then
   allow cells to declare the caveat.

Steps 1–5 are landed and VK-risk-free (PI + off-AIR check + additive projection); only step 6 — **the
named gated verifier-epoch flip** — remains, and it is a verifier-code rollout, not a VK rotation.
Stage (b) (heap-plane witnesses) is a later fidelity upgrade with the **same** Lean rung.

## 6. Why obligation second (the house-capacity weld ladder)

The standing obligation is the second of the six House capacities to gain its circuit weld (after the
sealed escrow). Its Lean teeth already existed (`StandingObligation.lean` §3–§6, the executor rung),
so the circuit rung is a short reuse; and the staging vehicle (manifest-in-PI, off-AIR re-evaluation)
is proven by the temporal-caveat and sealed-escrow epochs, so the path is de-risked. The remaining
House capacities (membrane, derived, vault, hatchery) follow the same template
(`metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`), each binding its invariant into what a light client,
not just a re-executing validator, witnesses — all carried by the one coordinated verifier-epoch
window.
