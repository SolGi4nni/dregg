# SettleEscrow weld — making settlement atomicity light-client-witnessed

This is the design for the first **house-capacity in-circuit weld**: binding the sealed
escrow's atomic-swap invariant into what a **light client** verifies, not just what a
re-executing validator checks out of band. It is written to be built **STAGED** — beside the
deployed default, with the AIR constraint polynomials (the VK bytes) **unchanged** — exactly
the way the temporal-caveat verifier arms were landed.

## 1. What is witnessed today, and the gap

The sealed escrow (`cell/src/escrow_sealed.rs`, Lean `metatheory/Dregg2/Deos/SealedEscrow.lean`)
escrows a two-party swap "A gives X iff B gives Y". Each leg's status
(`Empty`/`Deposited`/`Consumed`) and committed amount live in a reserved heap collection
(`ESCROW_COLL`) folded into the cell's canonical state commitment by the proven sorted-Poseidon2
`Heap.root`. The capacity's soundness — no half-open trade, no replay, no over-claim — is proven
at the **executor** altitude: a verifier holding the committed heap consults
`EscrowState::settlement` / `check_claim` and rejects every forge (§3–§5 of the Lean rung).

The **gap** is light-client altitude. A light client verifies a *batch proof* against the VK and
public inputs; it does **not** re-run the escrow check. So today the heap-root TRANSITION is
proven (the commitment moved), but the *gate* that the transition was atomic — both legs
`Deposited`+conforming before, **both** `Consumed` after, never one — is enforced only by a
re-executing validator. The weld closes that: a satisfying batch witness must **force** the
atomic both-legs-or-none shape, so a light client sees settlement atomicity as part of the
proven kernel transition.

## 2. The in-circuit gate (the design)

The natural temptation is "add a `SettleEscrow` `Effect` variant with new AIR columns." That is
**VK-affecting and large** (a new effect, descriptor, trace columns, AIR polynomials). We do not
do that. Instead we reuse the **manifest-in-public-inputs + off-AIR re-evaluation** vehicle that
already stages slot caveats (`circuit/src/effect_vm/verify.rs::verify_slot_caveat_manifest`,
tags 1–16): the executor projects the declared gate into PUBLIC INPUTS, and any proof consumer
(receipt verifier, third-party validator, light client) re-runs the gate against the bound
`state_before`/`state_after` views. Tampering with the manifest, the state-before/after, or the
cell-program declaration surfaces as a verifier-side rejection. **The AIR constraint polynomials
are unchanged**, so the VK bytes are unchanged; only the verifier's manifest-evaluation code
grows an arm.

### 2.1 Why a NEW tag (not two existing entries)

The escrow leg statuses are a *joint* invariant: atomicity is "both legs flipped, **or
neither**." The existing per-slot caveats (`AllowedTransitions`, `Monotonic`, …) bind ONE slot
per entry, *independently*. Two independent `Deposited→Consumed` entries do **not** capture
atomicity — a forged partial settle would simply present one entry and omit the other. The gate
must read **both** leg slots in **one** entry and require the joint transition. Hence a new tag,
`SLOT_CAVEAT_TAG_SETTLE_ESCROW = 17`, with params naming the two leg slots (or the heap
openings, §2.3) and asserting:

```
before[legA] == Deposited  ∧  before[legB] == Deposited
∧ after[legA] == Consumed  ∧  after[legB] == Consumed
```

This is the Lean `SettleGate hash before after` — a single conjunctive entry whose accept
**forces** the atomic shape (`settle_gate_forces_atomic`) and whose failure on any one leg
refuses the half-open trade (`partial_settle_rejected`).

### 2.2 The plane: heap, not the 8 field-slots

The slot-caveat manifest as it stands reads the cell's slot-0..7 4-byte field views
(`initial_fields`/`final_fields`). The escrow legs live in a heap *collection*, not those eight
field slots. Two staging shapes, in increasing fidelity:

- **(a) Field-projected.** The escrow cell program mirrors its two leg-status felts into two of
  its 8 field-slots (in addition to the heap). The `SettleEscrow` entry then names those two
  slot indices and the existing `initial_fields`/`final_fields` plane carries them. Smallest
  change; the heap remains the source of truth and the field mirror is what the AIR-teeth view
  binds. This is the recommended first stage.
- **(b) Heap-plane.** Carry the two leg-status heap openings (`(ESCROW_COLL, statusKey A/B)`
  against the cell's `heap_root` before and after) directly as manifest witnesses, the way
  `trace.rs` already notes the slot and heap planes share one tag space. Higher fidelity (binds
  the genuine heap slots, no field mirror), slightly more plumbing. The named second stage.

Either way the **soundness is the same Lean rung** (§3): the gate over a (before, after) pair,
its atomicity/no-partial/no-phantom teeth, and the root-transport tooth that ties the verdict to
the committed roots a light client already has bound in public inputs.

### 2.3 The binding that makes it light-client-witnessed

The light client holds the before/after **committed roots** (the ledger/heap roots in the batch
public inputs). The weld's load-bearing tooth, `settle_gate_root_bound`, proves the gate verdict
is a **function of those roots**: equal-root before/after views yield the same verdict. So a
forger who presents fake leg slots to fake a gate-pass must publish a **different root** — where
the §5 status binding (`leg_status_bound_in_root`, a direct `Heap.root_binds_get` instance)
bites. The light client therefore cannot be shown an accepting `SettleEscrow` entry over the
honest roots unless the legs genuinely transitioned atomically.

## 3. The Lean rung — BUILT, `#assert_axioms`-clean (this pass)

Landed in `metatheory/Dregg2/Deos/SealedEscrow.lean` §6, beside the executor teeth, reusing the
file's proven heap lemmas (no new mathematics, the one named `Poseidon2SpongeCR` floor):

| Theorem | What it proves | Role |
|---|---|---|
| `SettleGate` | the transition gate (both Deposited before, both Consumed after) | the off-AIR re-evaluation, as a predicate over a (before, after) pair |
| `settle_passes_gate` | honest `Ready`→`settle` satisfies the gate | non-vacuity (accept polarity) — the rung is not true-by-no-witness |
| `settle_gate_forces_atomic` | gate accept ⟹ both legs Deposited before ∧ both Consumed after | **the atomicity tooth** — no accepting witness has only one leg moving |
| `partial_settle_rejected` | leg B left `Deposited` ⟹ gate refuses | **the no-partial tooth** — the half-open trade is inexpressible |
| `phantom_settle_rejected` | a before-leg not `Deposited` ⟹ gate refuses | **the no-phantom tooth** — no consume from an unlocked/replayed leg |
| `settle_gate_root_bound` | equal before/after roots ⟹ same gate verdict (via `leg_status_bound_in_root`) | **the light-client tooth** — a forger must move a root, where §5 bites |

Non-vacuity `#guard`s (both polarities) compute on the reference sponge: the honest
`SettleGate both settled` passes; a partial settle (`partialA`: A consumed, B still deposited)
fails; a phantom settle (`onlyA`, B never locked) fails. `#assert_all_clean` pins all five new
keystones kernel-clean alongside the eleven executor teeth (16 total).

This is the soundness the eventual verifier arm **inherits** — precisely as the temporal-caveat
arms (verify.rs tags 13–16) inherit `temporalStateStepGuarded`. The Lean rung is the proof; the
Rust arm is its mechanical shadow.

## 4. VK impact — NONE (staged), and the named flip

- **AIR / VK bytes: unchanged.** The gate is carried in public inputs and enforced by an
  **off-AIR** verifier check (the manifest re-evaluation), so the constraint polynomials — hence
  the VK — are byte-identical. This is the same property the slot-caveat manifest (tags 1–16)
  already has.
- **What an old verifier does:** rejects `type_tag = 17` as `unknown type_tag` (the existing
  `other =>` arm in `verify_slot_caveat_manifest`). So a cell that *declares* a `SettleEscrow`
  caveat can only be verified by an upgraded verifier — a **lockstep epoch**, the
  **sealed-escrow verifier epoch**.
- **Deployed default: unchanged.** No existing escrow cell declares the new caveat (the
  flagship demo settles via the executor check), so nothing flips by default. The epoch is the
  coordinate-with-future-rollout step, deliberately deferred — the same posture as the
  temporal-caveat verifier epoch and the Custom-apex `Satisfied2Custom` staging.

**The named gated VK-flip (future coordinated epoch):** *sealed-escrow verifier epoch.* Land the
projection + verifier arm (build plan §5) behind the new tag, ship the upgraded verifier to all
consumers, then allow escrow cells to declare `SettleEscrow`. Because the VK bytes are unchanged,
this is a *verifier-code* rollout, not a proving-key rotation — the lighter of the two epoch
shapes. It coordinates with the umem VK epoch and the temporal-caveat epoch (one verifier-upgrade
window can carry all the off-AIR manifest tags at once).

## 5. The precise staged-build plan (VK-risk-free, in order)

1. **(DONE, this pass)** the Lean rung — `SealedEscrow.lean` §6, `#assert_all_clean`, green.
2. `pub const SLOT_CAVEAT_TAG_SETTLE_ESCROW: u32 = 17;` in `circuit/src/effect_vm/pi.rs` beside
   the existing tags. **No AIR change.**
3. A verifier arm in `verify_slot_caveat_manifest` (`circuit/src/effect_vm/verify.rs`) reading
   the two named leg slots from `initial_fields`/`final_fields` (stage (a)) and asserting the
   `SettleGate` conjunction, value-for-value mirroring the Lean teeth. The `other =>` unknown-tag
   arm already gives the lockstep-epoch rejection for old verifiers.
4. A projection arm in `turn/src/executor/mod.rs::project_slot_caveat_manifest` that, for an
   escrow cell declaring settlement, emits the tag-17 entry with the two leg-slot indices —
   beside the existing `TemporalGate`/`RateBound` cases. (This is the one step outside
   `circuit/`; it is additive and gated by the new caveat being declared, so it is dead-by-
   default until a cell opts in.)
5. Teeth tests in `circuit/tests/` (a `settle_escrow_air_teeth.rs` mirroring the Lean `#guard`
   non-vacuity, both polarities: honest passes, partial fails, phantom fails) and the executor
   projection round-trip in `turn/`.
6. **(future epoch only)** the sealed-escrow verifier epoch: ship the upgraded verifier, then
   allow cells to declare the caveat.

Steps 2–5 are VK-risk-free (PI + off-AIR check + additive projection); only step 6 is the
coordinated rollout, and it is a verifier-code rollout, not a VK rotation. Stage (b) (heap-plane
witnesses) is a later fidelity upgrade with the **same** Lean rung.

## 6. Why escrow first (leverage × tractability)

The escrow capacity is the **live flagship** (the most recent commit lands a REAL SealedEscrow
atomic-swap demo), so the weld has immediate product leverage; its Lean teeth already existed, so
the circuit rung is a short reuse (this pass); and the staging vehicle (manifest-in-PI, off-AIR
re-evaluation) is proven by the temporal-caveat epoch, so the path is de-risked. The temporal-
caveat AIR — the other candidate — is already staged-wired (verify.rs tags 13–16 inherit
`temporalStateStepGuarded`), so escrow is the genuinely-open, highest-leverage first weld.
