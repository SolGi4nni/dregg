# starbridge-vat

**HAVE A DREGG COMPUTER — a vat is a persistent, durable, forkable World you rent and reach
from any starbridge, and cannot be lied to.** A vat lives in the cloud but belongs to **you**,
not the provider running it: it is a cell whose history is receipted, so a provider you rent
from cannot forge what it did.

A vat is an **execution-lease with a lifecycle**. This crate is a dregg-native rewrite of a
prior imperative fleet-controller: the lease's economic + durability halves were already native,
so the vat builds ON them and adds the two things that make a lease a *computer* — a lifecycle
state machine and a placement binding.

- **persist** — the durable World is the lease cell's committed umem execution image
  (`lease::EXEC_COLL`): a checkpoint cursor + state digest + working memory, folded into the
  cell's commitment.
- **meter** — uptime is a `StandingObligation` (the lease's `RENT_SLOT`/`PERIOD_SLOT`); the
  recurring forge-detectors bite.
- **pay** — rent is a `Payable` conserving `Transfer` (Σδ = 0).
- **fork** — a vat forks by cloning its execution-image cell (the branch/stitch pushout).

## The lifecycle — a two-axis state machine

```
Created ──launch──▶ Running ──sleep──▶ Sleeping ──wake──▶ Running
   │                   │                   │
   └───────────────────┴──── lapse ────────┴───▶ Lapsed
                       (reap) ─────────────────▶ Reaped   (terminal)
```

The machine is **not linear** — sleep/wake move a vat up and down *within* being alive — so it
is encoded on two slots:

| axis | slot | caveat | what it is |
|---|---|---|---|
| **phase** (terminality rank) | `VAT_PHASE_SLOT` = 8 | `Monotonic` | `Provisioned(0) < Live(1) < Lapsed(2) < Reaped(3)` — one-way; `Running` and `Sleeping` **share** `Live` |
| **up** (liveness) | `VAT_UP_SLOT` = 7 | none (not monotone) | `1` = a box holds the running World; sleep flips 1→0, wake flips 0→1 |
| `machine_tag` / `endpoint_tag` | 9 / 10 | none (re-bound each placement) | the fungible box + reachable address |
| `witness_stance` | `WITNESS_SLOT` = 11 | `WriteOnce` | the renter's sealed Symbolic/Full trust-cost pick — a provider cannot silently downgrade a Full vat to skip proofs |

Splitting liveness OUT of the terminality rank is load-bearing: it is what lets a **wake**
(`Sleeping → Running`) be a legal turn under the `Monotonic` phase tooth — the earlier single-rank
encoding made a wake illegally *lower* the rank, and the tooth would have refused a legal wake.
Sleep = checkpoint the World to its durable image root; wake = restore from it.

## The enforced property (not asserted)

`vat_cell_program()` (`src/lib.rs:345`) is a strict extension of the lease's own program: it
carries `lease::lease_invariants()` PLUS `Monotonic(VAT_PHASE_SLOT)` + `WriteOnce(WITNESS_SLOT)`
(`vat_invariants`, `src/lib.rs:328`). `seed_vat` installs it; **`fire_vat_transition`
(`src/lib.rs:388`) submits every lifecycle move as a signed turn the executor RE-ENFORCES** — so
a phase-rank regression (or a contradictory two-axis state) is REFUSED in the fire path, not
merely by the pure check. The unit test `fire_admits_a_legal_move_and_refuses_a_phase_regression`
(`src/lib.rs:411`) proves both polarities: a legal `Created → Running` is admitted; a
`Running → Created` phase regression is refused by the installed program.

The pure apply layer (`src/lifecycle.rs`, `open_vat` / `apply_transition` / `read_state`) mirrors
the machine for unit-testing and seeding, and refuses an illegal transition
(`VatTransition::is_legal_from`) up front so it agrees with the executor's tooth. `open_vat_prepaid`
is the drift-unrepresentable twin — the durable image + the fused prepaid meter+reserve
(`prepaid_lease`, where meter/pay drift is a type error) + the same lifecycle slots, in one cell.

## The honest boundary

The verifiable core is the lifecycle + economics + durable cursor — all cells. What is NOT in
the core (and never should be) is the operational provisioning glue: spinning an actual VM, the
mesh overlay, the backend placement decision. That stays an imperative adapter the vat *drives*
— it reads the cell's state and makes the box match. So a light client witnesses "the vat is
Running, metered through period N, its image at digest D" without trusting the provider's word;
the worst a malicious provider can do is fail to run the box (which the lapse/reaper reclaims) —
never lie about what the box *did*. (`MACHINE`/`ENDPOINT` are deliberately unsealed — a re-placed
vat gets a fresh box + address; the durable image is what follows.)

## What this crate exports

```rust
VatState (Created/Running/Sleeping/Lapsed/Reaped) · VatPhase · VatTransition
vat_cell_program() / vat_invariants()            // the installed teeth
vat_transition_effects(vat, target) -> Vec<Effect>
seed_vat(executor) -> CellId                     // create + install the program
fire_vat_transition(cclerk, executor, vat, target) -> TurnReceipt   // the verified-turn wire

lifecycle::{open_vat, open_vat_prepaid, read_state, apply_transition, WitnessStance, VatError}
```

## Test

```
cargo test -p starbridge-vat
```

| Test | What it pins |
|---|---|
| `src/lib.rs::fire_admits_a_legal_move_and_refuses_a_phase_regression` | the executor re-enforces the phase tooth in the fire path (both polarities) |
| `src/lib.rs::the_vat_is_a_strict_extension_of_a_lease` | `vat_invariants = lease invariants + Monotonic(PHASE) + WriteOnce(WITNESS)` |
| `src/lib.rs::a_legal_transition_never_lowers_the_phase_rank` | the two-axis split — a wake holds `Live`, so the tooth admits it |
| `src/lifecycle.rs::the_full_lifecycle_walk_is_legal_and_binds_the_box`, `an_illegal_transition_is_refused_before_it_writes`, `a_reaped_vat_admits_nothing` | the pure machine + terminality |
| `src/lifecycle.rs::a_prepaid_vat_opens_at_created_and_walks_the_lifecycle` | the fused prepaid-meter twin |
