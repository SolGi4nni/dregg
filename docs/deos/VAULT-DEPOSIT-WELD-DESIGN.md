# VaultDeposit weld — making the share-vault no-dilution invariant light-client-witnessed

This is the design for the **third house-capacity in-circuit weld** (#5, the share
vault), built after the SettleEscrow weld (`docs/deos/SETTLE-ESCROW-WELD-DESIGN.md`)
and the DischargeObligation weld (`docs/deos/DISCHARGE-OBLIGATION-WELD-DESIGN.md`) and
following their exact shape. It binds the share vault's ERC-4626 no-dilution / share-price
invariant into what a **light client** verifies, not just what a re-executing validator
checks out of band. It is built **STAGED** — beside the deployed default, with the AIR
constraint polynomials (the VK bytes) **unchanged** — exactly the way the temporal-caveat
verifier arms, the sealed-escrow tag-17 arm, and the standing-obligation tag-18 arm were
landed.

## 1. What is witnessed today, and the gap

The share vault (`cell/src/vault.rs`'s share-vault section, Lean
`metatheory/Dregg2/Deos/Vault.lean`) is a cell that pools an asset and mints fungible
`shares`, exactly the ERC-4626 deposit/withdraw shape. A committed `total_assets` counter
and a committed `total_shares` counter live in reserved heap slots (`SHARE_VAULT_COLL`)
folded into the cell's canonical state commitment by the proven sorted-Poseidon2
`Heap.root`. The capacity's soundness — minted shares `== d·S/T`, existing holders never
diluted, the ERC-4626 first-depositor inflation attack rejected — is proven at the
**executor** altitude (§1–§6 of the Lean rung): a verifier holding the committed counters
consults `ShareVaultState::check_deposit` and rejects a forged share count, a zero-mint
(inflation) deposit, and a skewed ratio.

**Why the share vault is STRONGER than ERC-4626** (both closed at the executor altitude):

  1. `total_assets` is an **internal committed counter**, changed only by an accounted
     deposit/withdraw — a raw balance donation never touches the committed slot, so it
     cannot skew the ratio (donation immunity).
  2. a deposit that would mint **zero shares** under a skewed ratio is **rejected**, so a
     victim is never robbed of a positive deposit for nothing.

The **gap** is light-client altitude. A light client verifies a *batch proof* against the
VK and public inputs; it does **not** re-run the deposit check. So today the heap-root
TRANSITION is proven (the commitment moved), but the *gate* — that the mint honored the
share-price relation and diluted no existing holder — is enforced only by a re-executing
validator. The weld closes that: a satisfying batch witness must **force** the no-dilution
shape, so a light client sees the share price honored as part of the proven kernel
transition. This is the slice `cell/src/vault.rs` flagged as the named next
`DepositToVault` / VK-affecting weld.

## 2. The in-circuit gate (the design)

The natural temptation is "add a `DepositToVault` `Effect` variant with new AIR columns
binding `shares_out == d·S/T`." That is **VK-affecting and large** (a new effect,
descriptor, trace columns, AIR polynomials — and the division `d·S/T` is awkward in field
arithmetic). We do not do that. Instead we reuse the **manifest-in-public-inputs + off-AIR
re-evaluation** vehicle that already stages slot caveats
(`circuit/src/effect_vm/verify.rs::verify_slot_caveat_manifest`, tags 1–18): the executor
projects the declared gate into PUBLIC INPUTS, and any proof consumer (receipt verifier,
third-party validator, light client) re-runs the gate against the bound
`state_before`/`state_after` views. Tampering with the manifest, the state-before/after, or
the cell-program declaration surfaces as a verifier-side rejection. **The AIR constraint
polynomials are unchanged**, so the VK bytes are unchanged; only the verifier's
manifest-evaluation code grows an arm.

### 2.1 Why a NEW tag (not existing entries)

No-dilution is a *joint* invariant over a (before, after) transition: "the deposit is
genuine (`d>0`) **and** the mint is positive (`m>0`) **and** no existing holder is diluted
(`before_assets·m ≤ before_shares·d`)." The existing per-slot caveats (`Monotonic`,
`FieldDelta`, …) each bind ONE aspect of ONE slot *independently*: `Monotonic{shares}`
would force shares not to decrease but not the no-dilution floor; `FieldDelta{assets, d}`
would force a fixed asset advance but a deposit varies per turn. A forge could satisfy each
independently while violating the joint shape — minting zero shares on a real deposit, or
over-minting to dilute. The gate must read **both counter slots across the transition** in
**one** entry. Hence a new tag, `SLOT_CAVEAT_TAG_VAULT_DEPOSIT = 19`, with `slot_index` =
the `total_assets` counter slot and `p0` = the `total_shares` counter slot, asserting:

```
after[assets_slot] > before[assets_slot]                              (CONSERVING d>0)
∧ after[shares_slot] > before[shares_slot]                            (POSITIVE MINT m>0)
∧ before[assets_slot]·m ≤ before[shares_slot]·d                       (NO DILUTION)
   where d = after[assets_slot] − before[assets_slot],
         m = after[shares_slot] − before[shares_slot]
```

This is the Lean `VaultDepositGate before after Tb Sb d m` — a single conjunctive entry
whose accept **forces** the no-dilution shape (`vault_gate_forces_no_dilution`) and whose
failure on any one leg refuses the zero-mint / diluting / non-conserving step
(`inflation_attack_rejected` / `dilution_rejected` / `assets_not_conserved_rejected`).

Note: unlike the standing obligation (whose `period`/`amount` are static schedule
constants), the deposit `d` and minted `m` are read as the **across-transition deltas** of
the two slots — a deposit varies per turn, so there is no per-deposit constant in the
declared caveat.

### 2.2 The plane: field-mirrored counter slots

The slot-caveat manifest reads the cell's slot-0..7 4-byte field views
(`initial_fields`/`final_fields`). The vault's `total_assets`/`total_shares` live in a heap
*collection*, not those eight field slots. As with the prior welds' stage (a): the vault
cell program mirrors its two committed counters into two of its 8 field-slots (in addition
to the heap), the `VaultDeposit` entry names those slot indices, and the existing
`initial_fields`/`final_fields` plane carries them. Smallest change; the heap remains the
source of truth and the field mirror is what the AIR-teeth view binds. The **heap-plane**
(carrying the counter heap openings against the cell's `heap_root` directly) is the named
second-stage fidelity upgrade with the **same** Lean rung (§6b).

### 2.3 The binding that makes it light-client-witnessed

The light client holds the before/after **committed roots** (the ledger/heap roots in the
batch public inputs). The weld's load-bearing tooth, `vault_gate_root_bound`, proves the
gate verdict is a **function of those roots**: equal-root before/after views yield the same
verdict (via `assets_bound_in_root` / `shares_bound_in_root`, direct `Heap.root_binds_get`
instances). So a forger who presents fake counter slots to fake a gate-pass must publish a
**different root** — where the §6 binding bites. The light client therefore cannot be shown
an accepting `VaultDeposit` entry over the honest roots unless the deposit genuinely honored
the share price.

## 3. The Lean rung — BUILT, `#assert_axioms`-clean

Landed in `metatheory/Dregg2/Deos/Vault.lean` §6b, beside the executor teeth, reusing the
file's proven heap lemmas (no new mathematics, the one named `Poseidon2SpongeCR` floor):

| Theorem | What it proves | Role |
|---|---|---|
| `VaultDepositGate` | the transition gate (d>0 ∧ m>0 ∧ `Tb·m ≤ Sb·d`) | the off-AIR re-evaluation, as a predicate over a (before, after) pair |
| `vault_passes_gate` | an honest no-dilution deposit satisfies the gate | non-vacuity (accept polarity) — the rung is not true-by-no-witness |
| `vault_gate_forces_no_dilution` | gate accept ⟹ assets+shares conserve ∧ m>0 ∧ no dilution | **the no-dilution tooth** — no accepting witness dilutes or conjures shares |
| `inflation_attack_rejected` | a zero/negative mint ⟹ gate refuses | **the inflation-attack tooth** — the ERC-4626 first-depositor zero-mint is inexpressible |
| `dilution_rejected` | `Sb·d < Tb·m` ⟹ gate refuses | **the over-mint tooth** — diluting the existing holders is inexpressible |
| `assets_not_conserved_rejected` | assets not advancing by exactly `d` ⟹ gate refuses | **the non-conserving tooth** — pooled value cannot be conjured |
| `vault_gate_root_bound` | equal before/after roots ⟹ same gate verdict | **the light-client tooth** — a forger must move a root, where §6 bites |

Non-vacuity `#guard`s (both polarities) compute on the reference sponge: the honest
established (2,4)→(12,24) and bootstrap (0,0)→(100,100) deposits pass; a zero-mint
(`afterZeroMint`, shares unchanged) fails; an over-mint (`afterDilute`, m=21) fails; a
non-conserving (`afterForgedAssets`, assets forged to 99) fails. `#assert_all_clean` pins
all of §6b kernel-clean alongside the §1–§6 executor teeth (21 keystones total).

This is the soundness the verifier arm **inherits** — precisely as the temporal-caveat arms
(verify.rs tags 13–16) inherit `temporalStateStepGuarded`, the sealed-escrow arm (tag 17)
inherits `SettleGate`, and the standing-obligation arm (tag 18) inherits `DischargeGate`.
The Lean rung is the proof; the Rust arm is its mechanical shadow.

## 4. VK impact — NONE (staged), and the named flip

- **AIR / VK bytes: unchanged.** The gate is carried in public inputs and enforced by an
  **off-AIR** verifier check (the manifest re-evaluation), so the constraint polynomials —
  hence the VK — are byte-identical. The same property the slot-caveat manifest (tags 1–18)
  already has. `pi_v3` drift guard (`BASE_COUNT`) and the descriptor fingerprints stay
  green: tag 19 is a tag VALUE, not a PI-layout offset.
- **What an old verifier does:** rejects `type_tag = 19` as `unknown type_tag` (the existing
  `other =>` arm in `verify_slot_caveat_manifest`). So a cell that *declares* a `VaultDeposit`
  caveat can only be verified by an upgraded verifier — a **lockstep epoch**, the
  **share-vault verifier epoch**.
- **Deployed default: unchanged.** No existing vault cell declares the new caveat (the live
  capacity deposits via the executor check), so nothing flips by default.

**The named gated VK-flip (future coordinated epoch):** *share-vault verifier epoch.* Land
the projection + verifier arm (done, §5) behind the new tag, ship the upgraded verifier to
all consumers, then allow vault cells to declare `VaultDeposit`. Because the VK bytes are
unchanged, this is a *verifier-code* rollout, not a proving-key rotation. It coordinates with
the SettleEscrow, DischargeObligation, temporal-caveat, and umem epochs: **one
verifier-upgrade window can carry all the off-AIR manifest tags (17, 18, 19, 13–16) at once.**

## 5. The precise staged-build plan (VK-risk-free, in order) — landed

1. **(DONE)** the Lean rung — `Vault.lean` §6b, `#assert_all_clean`, green.
2. **(DONE)** `pub const SLOT_CAVEAT_TAG_VAULT_DEPOSIT: u32 = 19;` in
   `circuit/src/effect_vm/pi.rs` beside the existing tags. **No AIR change** — a tag VALUE.
3. **(DONE)** a verifier arm in `verify_slot_caveat_manifest` (`circuit/src/effect_vm/verify.rs`)
   reading the total_assets counter from `slot_index` (old_v/new_v), the total_shares counter
   from `p0` (`initial_fields`/`final_fields`), computing `d`/`m` as the across-transition
   deltas, and asserting the `VaultDepositGate` conjunction (`d>0`, `m>0`,
   `before_assets·m ≤ before_shares·d` in `u128`), value-for-value mirroring the Lean teeth,
   fail-closed on an out-of-range shares slot. The `other =>` unknown-tag arm gives the
   lockstep-epoch rejection for old verifiers. There is ALSO an executor-side scalar evaluator
   arm (`cell/src/program/eval.rs`, the `StateConstraint::VaultDeposit` case) so the gate is
   enforced out-of-band as well as in the manifest.
4. **(DONE)** a projection arm in `turn/src/executor/mod.rs::project_slot_caveat_manifest` that,
   for a cell declaring `StateConstraint::VaultDeposit { assets_slot, shares_slot }`, emits the
   tag-19 entry (`slot_index = assets_slot`, `params = [shares_slot, 0, 0, 0]`). Additive and
   gated by the new caveat being declared, dead-by-default.
5. **(DONE)** teeth tests: `circuit/tests/vault_deposit_air_teeth.rs` (both polarities — honest
   no-dilution deposit + bootstrap pass; zero-mint inflation / over-mint dilution /
   non-conserving / asset-decrease refused; out-of-range shares slot fail-closed) and
   `turn/tests/vault_deposit_projection.rs` (projection round-trip end-to-end). The new
   `StateConstraint::VaultDeposit` variant also rides the existing coverage teeth
   (`cell/src/program/tests.rs` view/serde totality;
   `teasting/.../protocol_coverage_gate.rs` ratchet 22 → 23).
6. **(future epoch only)** the share-vault verifier epoch: ship the upgraded verifier, then
   allow cells to declare the caveat.

Steps 1–5 are landed and VK-risk-free (PI + off-AIR check + additive projection); only step 6
— **the named gated verifier-epoch flip** — remains, and it is a verifier-code rollout, not a
VK rotation. Stage (b) (heap-plane witnesses) is a later fidelity upgrade with the **same**
Lean rung.

## 6. Why the vault third (the house-capacity weld ladder)

The share vault is the third of the six House capacities to gain its circuit weld (after the
sealed escrow and the standing obligation). Its Lean teeth already existed (`Vault.lean`
§1–§6, the executor rung), so the circuit rung is a short reuse; and the staging vehicle
(manifest-in-PI, off-AIR re-evaluation) is proven by the temporal-caveat, sealed-escrow, and
standing-obligation epochs, so the path is de-risked. The remaining House capacities
(membrane, derived, hatchery) follow the same template
(`metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`), each binding its invariant into what a
light client, not just a re-executing validator, witnesses — all carried by the one
coordinated verifier-epoch window.
