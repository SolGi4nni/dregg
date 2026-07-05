# The House-Capacity Framework — one shape for every room an agent lives in

The dregg "house capacities" are the moves an autonomous agent *living inside
dregg* holds as first-class: lock value, trade atomically, carry a recurring
duty, hand a sub-agent bounded money, publish a verifiable view, compose two
authorities, mint a custom kind. Each began as a `cell/src/*.rs` prototype with a
both-polarity forge-detector. This document is the **coherent frame** that makes
them ONE system rather than seven scattered modules: the common shape every
capacity shares, the grounding-by-reuse template, and the clear path for the ones
not yet grounded.

The frame is not aspirational. All six capacities — **membrane**, **derived
cells**, **sealed escrow**, **standing obligation**, **share-vault**, and the
**hatchery** abstraction-mint — now sit fully on it, each with a Lean rung
proven *by reuse* of an already-proven commitment/skeleton, no VK bump, the Rust
wired to the rung. The house is COMPLETE.

---

## 1. The common shape

Every house capacity is the same five-part object:

| Part | What it is | Where it lives |
|---|---|---|
| **1. A heap-committed cell-program** | the capacity's state, written into the cell's committed heap (`set_heap` / `compute_heap_root`, sorted-Poseidon2, folded into the canonical state commitment) | `cell/src/<cap>.rs` |
| **2. An INVARIANT** | the one load-bearing predicate that makes the capacity sound (e.g. "exposed ⊑ a & b", "claimed == f(sources)", "claimable exactly once after the release rule") | the module's soundness story |
| **3. A Lean RUNG** | the invariant proven as a theorem, **by reuse** of an already-proven lattice/commitment — no new mathematics, no VK bump | `metatheory/Dregg2/Deos/<Cap>.lean` |
| **4. A forge-detector** | the executor check that rejects a cell violating the invariant (forged AND stale), with both-polarity tests | the module's `verify`/`seal`/`exercise` + `#[cfg(test)]` |
| **5. A wiring test** | a Rust test mirroring the Lean witnesses, so the executor check is tied to the proven statement, not an ad-hoc tampering | `tests::*_matches_lean_rung` |

The discipline that ties 3–5 together: **the Rust forge-detector is the
EXECUTOR image of the Lean rung.** The rung proves the invariant over the abstract
commitment; the Rust enforces it over the deployed `CellState`; the wiring test
checks they agree on the witnesses. A capacity is "formally real" when all five
are present — not when its smoke tests pass (a smoke test rejects one tampering;
the rung proves the model).

---

## 2. The grounding-by-reuse template

The key move — what makes a rung cheap and VK-free — is that **the invariant is
already a property of a proven object.** You do not build a new commitment or a
new lattice; you NAME the capacity as a use of an existing one, and the
soundness follows by reuse. Two reuse bases carry the whole house:

### The cap lattice (`Dregg2.Exec` / `Dregg2.Authority`)

For capacities whose invariant is an **authority bound** — a `⊆` over conferred
authority. The membrane is here.

- **Reuse base:** `attenuate_subset` (a projection confers a subset) and the
  `capAuthConferred ⊆` order the cap-reshape crown proves on.
- **Template:** define the capacity's authority operation as a use of `attenuate`
  / the meet `compose`; the non-amplification floor is `Subset.trans` over the
  existing order. No new lattice.

### The committed heap root (`Dregg2.Substrate.Heap`)

For capacities whose invariant is a **bound value/state** — a committed scalar
that must equal something, or a write-once / monotone cursor. Derived cells are
here; vault, allowance, escrow, and obligation all bind their state into this
same heap.

- **Reuse base:** `hget_hset_self` (read-after-write, crypto-free),
  `hget_hset_frame` (untouched slots survive, under the named `Poseidon2SpongeCR`
  floor), and **`root_binds_get`** (equal roots open to the same value — the
  claim is bound into the commitment; the anti-ghost).
- **Template:** write the capacity's state into reserved heap slots; the
  invariant is a predicate over `hget` of those slots; the *honest round-trip* is
  `hget_hset_self`/`frame`; the *forge tooth* is the predicate biting on a
  divergent slot; the *binding tooth* (a forge cannot hide under the honest root)
  is `root_binds_get`. No new commitment.

### The shared anatomy of a heap-backed rung

Both grounded rungs (`Membrane.lean`, `DerivedCell.lean`) have the same sections,
and a new one should too:

1. **§1 — the operation** (the fold / the meet / the release rule), a small
   deterministic function the binder and the verifier BOTH compute.
2. **§2 — the capacity as a use of the reuse base** (write into the heap / project
   the cap).
3. **§3 — the honest round-trip + the teeth** (`bind_verifies` + `forged_*` +
   `stale_*` + `wrong_*`).
4. **§4 — the reuse keystone** (the invariant is bound into the proven
   commitment: `root_binds_get` for heap-backed, `Subset.trans` for cap-backed).
5. **§5 — non-vacuity `#guard` witnesses**, both polarities, on the reference
   sponge / concrete caps.
6. **§6 — `#assert_all_clean`.**

---

## 3. The factory route for compositions

Some capacities are not new invariants but **compositions of the wired settlement
vocabulary.** The `blueprint` route (`cell/src/blueprint.rs`, alive-wired) mints a
per-deal `FactoryDescriptor` whose `state_constraints` ARE a verified state
machine, settled by the already-wired `CreateCellFromFactory` + `Transfer` +
`SetField` triple — no new `Effect`, no VK change, the locked value living in the
minted cell's own balance.

This is the route for **allowance** (`Apps/Allowance.lean`): every gate it needs
already exists in the `StateConstraint` vocabulary (`RateLimit`/`RateLimitBySum` +
a `Monotonic` epoch cursor). It welds as `*_state_constraints` +
`*_factory_descriptor` + a `Dregg2/Apps/<Cap>.lean` twin with an
`EscrowFactoryProbe`-style PASS probe — the factory analogue of the grounding
template above. See `metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md` for the
per-capability census.

**Vault landed via BOTH routes.** Rather than only the predicted factory twin
(`Apps/Vault.lean`, over `FieldGteHeight`/`PreimageGate`), the share-vault also
took the invariant route directly: a `Deos/Vault.lean` heap-root rung
(`root_binds_get`) proving `deposit_no_dilution` / `withdraw_no_dilution` — so
the vault is provably immune to the ERC-4626 inflation attack — wired by
`cell/src/vault.rs::tests::share_vault_matches_lean_rung`. The two groundings are
complementary: the `Deos` rung binds the no-dilution invariant into the committed
heap, the `Apps` twin binds the lock/gate constraints into the factory descriptor.

The distinction: **invariant capacities** get a `Deos/*.lean` rung over a reuse
base; **settlement capacities** get an `Apps/*.lean` factory twin over the
constraint vocabulary. As it landed, most of the house took the invariant route:
membrane, derived, escrow, obligation, and vault all have a `Deos/*.lean` rung
over the heap-root / cap-lattice reuse base, and escrow / obligation / vault
*also* carry an `Apps/*.lean` factory twin. Only allowance is factory-only. Both
are "by reuse, no VK bump"; they differ only in which proven object they reuse.

---

## 4. The grounded house — all six on the frame

| Capacity | Reuse base | Rung | Status |
|---|---|---|---|
| **membrane** | cap lattice (`attenuate_subset` / meet) | `Deos/Membrane.lean` | **GROUNDED** — `membrane_non_amplifies` + teeth, Rust `non_amp_floor_matches_lean_rung` |
| **derived** | heap root (`root_binds_get`) | `Deos/DerivedCell.lean` | **GROUNDED** — `bind_verifies` + forge/stale/wrong-spec teeth + `claim_bound_in_root`, Rust `invariant_matches_lean_rung` |
| **escrow** | heap root (`root_binds_get`) + one-shot Consumed | `Deos/SealedEscrow.lean` | **GROUNDED** — `deposit_both_ready` + `replay_rejected` (one-shot) + `nonconforming_claim_rejected` + `over_claim_rejected` + `leg_status_bound_in_root`, Rust `invariant_matches_lean_rung` |
| **obligation** (standing/recurring) | heap root (`root_binds_get`) + `StrictMonotonic` cursor | `Deos/StandingObligation.lean` | **GROUNDED** — `cursor_strict_mono` + `replay_rejected` (one-shot/period) + early/over/behind-schedule teeth + `cursor_bound_in_root`, Rust `invariant_matches_lean_rung` |
| **share-vault** | heap root (`root_binds_get`, no-dilution) | `Deos/Vault.lean` (+ `Apps/Vault.lean` twin) | **GROUNDED** — `deposit_no_dilution` + `deposit_price_non_decreasing` + `withdraw_no_dilution` + `forged_shares_rejected` teeth (provably immune to ERC-4626 inflation), Rust `share_vault_matches_lean_rung` |
| **hatchery** (abstraction-mint) | `CellProgram::evaluate_with_meta` + a proved `Verify.Contract.CellContract` | `Deos/Hatchery.lean` | **GROUNDED** — `evalStep_admits_iff_*` + `step_preserves` (the hpres) + `invariant_forever` (the `CellContract` carry skeleton reused) + `Attested`/`attested_enforces_forever` (`HpresProof::Attested` ⟺ a machine-checked contract) + `program_missing_invariant_rejected` + `violating_*_rejected`, Rust `invariant_matches_lean_rung` |

The escrow and obligation rungs are the **invariant-capacity** route (a `Deos/*.lean` rung over the
heap-root reuse base), not the factory route — the standalone `cell/src/{escrow_sealed,
obligation_standing}.rs` 2-leg-swap / recurring-cursor shapes ground directly on
`Substrate.Heap.root_binds_get` (escrow: + the one-shot `Consumed` discipline; obligation: + the
`StrictMonotonic` `next_due` cursor, the version/supply monotone-slot law). The deeper light-client
weld (the circuit witness) stays the named per-capacity VK-affecting follow-up (§5).

The path for each follower is the same three steps the grounded two
demonstrate:

1. **Name the invariant** as a property of a reuse base (heap root or cap
   lattice or factory constraint), not a new commitment.
2. **Write the rung** in the shared §1–§6 anatomy, proving the honest round-trip,
   the forge/stale teeth, and the reuse keystone (`root_binds_get` /
   `Subset.trans` / the factory probe), `#assert_all_clean`.
3. **Wire the Rust** with a `*_matches_lean_rung` test mirroring the witnesses.

---

## 5. The one honest seam, named once for the whole house

Every grounded rung above is the **executor** tooth: a verifier holding the
sources/caps rejects a forge. The DEEPER weld — binding the invariant into the
cap-root / state-commitment the *circuit* sees, so a **light client** (not just
the executor) witnesses the capacity's invariant as part of the proven kernel
transition — is **VK-affecting**, and is the named per-capacity follow-up
(`metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`), the same lane the cap-root
reshape crown drives. It is not forced by the executor rung: the executor tooth is
real and load-bearing today; the circuit tooth is its shadow, climbed
deliberately per capacity. Naming it is the discipline, not a deferral — each
capacity's circuit weld is a tracked rung, not a parking lot.

**One sentence:** a house capacity is a heap-committed cell-program + an invariant
+ a Lean rung proven by reuse (no VK bump) + a forge-detector + a wiring test; the
all six — membrane, derived cells, sealed escrow, standing obligation,
share-vault, and the hatchery abstraction-mint — now sit fully on that frame.
The house is COMPLETE.
