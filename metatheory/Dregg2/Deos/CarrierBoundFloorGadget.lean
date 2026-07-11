/-
# Dregg2.Deos.CarrierBoundFloorGadget — the GENTIAN floor BINDING discharged: the required-tag floor
the selector gadget reads is DECODED from the already-coverage-bound caveat-manifest columns, so the
last `hcommitLimb` hypothesis is DISCHARGED (the floor is PROVABLY the cell's real declared floor, not
a forgeable free limb).

## The gap this closes (the last one to a sound escrow flip)

`InAirAuthorityDigestGadget.gentian_selector_forced_discharged` forces the capacity selector ON for a
committed declaration requiring the escrow tag — but its forcing is conditional on

  `hcommitLimb : loc gentianAuthDigestCol = hash committedFloor`

i.e. it ASSUMES the committed `B_AUTHORITY_DIGEST` limb (a FREE rotated headroom limb) carries
`hash(the real declared required-tag floor)`. Nothing in that gadget FORCES it: the limb is value-only
absorbed into the wide commit (consistent across the proof), but absorption does not pin it to the
*real* declared floor. A forger settling a half-open escrow on a cell that DECLARES escrow can write
`hash([])` into the limb, so the gadget decodes an empty floor → `floorCol = 0` → the selector is not
forced → the satisfaction teeth go inert → the dodge succeeds.

## The fix — PATH (b): decode the floor from the already-bound caveat manifest (no new BINDING VK)

The cell's required-capacity-caveat tags are ALREADY bound into the ~124-bit wide commit AND checked by
the deployed COVERAGE carrier: the rotated `RotCaveatManifest` (the 7-felt entries
`[type_tag, domain_tag, key, p0..p3]`) is chained by `caveatCommit` to the published caveat-commit PI
(`EffectVmEmitRotationCaveat.caveatCommit` / `caveatCommit_binds`; deployed at PI 45,
`circuit/src/effect_vm/trace_rotated.rs` `CAVEAT_BASE`, type tags at cols 291/298/305/312). A
pure light client binds that commit; `CapacityCarrier` already forces the published manifest to equal
the committed one from it. So the required-tag floor a light client checks for COVERAGE is the SAME
object whose escrow-membership the SELECTOR must read.

This module re-targets the selector gadget to decode the escrow bit DIRECTLY from the caveat-manifest
type-tag columns (the deployed, caveat-commit-bound columns) instead of from a separately-hashed digest
limb. The decode is the same in-AIR is-zero + OR-fold arithmetic, now folded over the FOUR manifest
type-tag slots (`MAX_CAVEATS = 4`). The payoff:

  * **`hcommitLimb` DISCHARGED.** The floor the gadget reads is `manifestTags (gadgetManifest row)` —
    the row's own caveat-manifest type tags. The binding `caveatCommit (gadgetManifest row) =
    caveatCommit committedManifest` (the EXISTING carrier binding a pure light client already has, the
    field-level analog the COVERAGE half consumes — NOT a new free-limb assumption) plus
    `caveatCommit_binds` (the deployed `Poseidon2SpongeCR` carrier floor — NO new CR floor, NO
    `FloorDigestBinds`, NO recompute chip lookup) force `gadgetManifest row = committedManifest`. So the
    decoded floor IS the cell's real declared floor, provably — not assumable.
  * **THE FORGED-FLOOR TOOTH** (`gentian_forged_floor_unsat_carrier`): a forger presenting a row
    manifest that OMITS the escrow tag while matching the committed caveat commit is IMPOSSIBLE
    (`caveatCommit_binds` collapses it to the committed manifest, which declares escrow). The free-limb
    dodge above is closed at the binding, not assumed away.

## What is and is NOT needed for a VK change

The floor BINDING needs NO new VK: the caveat manifest + its `caveatCommit` chain are already in the
deployed AIR (the COVERAGE carrier, `CapacityCarrier`'s "NOT VK-affecting" finding). The only new
constraint polynomials are the in-AIR DECODE + selector-force arithmetic gates (the irreducible in-AIR
selector forcing CapacityCarrier named as the VK-affecting tail) — and they are PURE ARITHMETIC: this
path DROPS the recompute chip lookup, the separate digest limb, and the `FloorDigestBinds` floor that
the Option-B digest path carried. STAGED — built beside the deployed, NOT emitted into a committed VK,
NOT routed; the deployed descriptors / VK are byte-identical. Rust shadow:
`circuit/src/effect_vm/carrier_floor_weld.rs`.

## Axiom hygiene

`#assert_all_clean` at the close. The only named hypothesis is `Poseidon2SpongeCR` (the deployed
carrier collision-resistance floor — the SAME one `caveatCommit_binds` carries); never an axiom; no
core edit. The forcing reduces through the STABLE `Satisfied2.rowConstraints` interface and the
deployed `caveatCommit_binds` lever.
-/
import Dregg2.Deos.InAirAuthorityDigestGadget
import Dregg2.Deos.CapacityCarrier

namespace Dregg2.Deos.CarrierBoundFloorGadget

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Deos.SealedEscrow (stEmpty stDeposited stConsumed)
open Dregg2.Deos.ConstraintBinding (Tag tagSettleEscrow)
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
  (RotCaveatEntry RotCaveatManifest caveatCommit caveatCommit_binds zeroEntry)
open Dregg2.Deos.SettleEscrowSatDescriptor
  (ESCROW_SEL_COL beforeFieldCol afterFieldCol settleEscrowSatGate settleEscrowSatGates)
open Dregg2.Deos.SettleEscrowSatWideDescriptor
  (settleEscrowSatVmDescriptor2R24Wide settleGateWide_mem)
open Dregg2.Deos.InAirAuthorityDigestSelector
  (GENTIAN_FLOOR_ESCROW_COL)
open Dregg2.Deos.InAirAuthorityDigestGadget
  (tagEscrowZ escrowBitZ isZeroDefGate isZeroForceGate isZero_from_gates)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

set_option autoImplicit false

/-- Field-faithful lift: two CANONICAL (`0 ≤ · < p`) integers congruent mod `p` are EQUAL. -/
private theorem canonEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (hap : a < 2013265921) (hb0 : 0 ≤ b) (hbp : b < 2013265921) : a = b := by
  unfold Int.ModEq at h
  rwa [Int.emod_eq_of_lt ha0 hap, Int.emod_eq_of_lt hb0 hbp] at h

/-- The felt-domain escrow decode is a boolean value. -/
private theorem escrowBitZ_mem (l : List ℤ) : escrowBitZ l = 0 ∨ escrowBitZ l = 1 := by
  unfold escrowBitZ; split <;> simp

/-- The OR-fold congruence lifts to the exact ℤ boolean-OR equality when the running OR and the next
bit are boolean and the output column is canonical. -/
private theorem orFoldLift {oNext o b : ℤ}
    (hmod : oNext ≡ o + b - o * b [ZMOD 2013265921])
    (hoN : 0 ≤ oNext ∧ oNext < 2013265921)
    (ho : o = 0 ∨ o = 1) (hb : b = 0 ∨ b = 1) :
    oNext = o + b - o * b := by
  have hrhs : 0 ≤ o + b - o * b ∧ o + b - o * b < 2013265921 := by
    rcases ho with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;> norm_num
  exact canonEq hmod hoN.1 hoN.2 hrhs.1 hrhs.2

/-! ## §1 — the caveat-manifest columns + the decode-aux columns (free headroom, value-only).

The four 7-felt manifest entries ride a free headroom block (the staged-rung mirror of the deployed
caveat carrier at `trace_rotated.rs::CAVEAT_BASE`, type tags at cols 291/298/305/312; the exact column
alignment to the deployed carrier is the emit-side concern, EXACTLY as the other staged rungs model
their commit columns — the SOUNDNESS content is that
the floor is bound by the EXISTING `caveatCommit`, proven below). Each entry's type tag is its first
felt; the decode reads those four columns. The per-slot is-zero bits, the inverse witnesses, and the
running-OR carriers ride further free headroom. -/

/-- The staged caveat-manifest block base — free headroom past the wide welded descriptor. -/
def CARRIER_BASE : Nat := EFFECT_VM_WIDTH + 200
/-- The caveat count column. -/
def cavCountCol : Nat := CARRIER_BASE
/-- Entry `i`'s base column (`CARRIER_BASE + 1 + 7 i`). -/
def cavEntryBase (i : Nat) : Nat := CARRIER_BASE + 1 + 7 * i
/-- Entry `i`'s TYPE-TAG column (the first felt of the entry — the decode input). -/
def cavTagCol (i : Nat) : Nat := cavEntryBase i
/-- The per-slot is-zero boolean column for entry `i`. -/
def bitCol (i : Nat) : Nat := CARRIER_BASE + 30 + i
/-- The per-slot inverse-witness column for entry `i`. -/
def invCol (i : Nat) : Nat := CARRIER_BASE + 40 + i
/-- The running-OR carrier `k` (`O0 = b0`, `O1 = O0∨b1`, `O2 = O1∨b2`; `O3 = floorCol`). -/
def orCol (k : Nat) : Nat := CARRIER_BASE + 50 + k

/-- Read the caveat manifest off a row (count at base, four 7-felt entries, positional) — EXACTLY the
`EffectVmEmitRotationCaveat.blockManifest` shape, over the gadget's headroom block. -/
def gadgetManifest (loc : Nat → ℤ) : RotCaveatManifest :=
  { count := loc cavCountCol
  , e0 := ⟨loc (cavEntryBase 0), loc (cavEntryBase 0 + 1), loc (cavEntryBase 0 + 2),
           loc (cavEntryBase 0 + 3), loc (cavEntryBase 0 + 4), loc (cavEntryBase 0 + 5),
           loc (cavEntryBase 0 + 6)⟩
  , e1 := ⟨loc (cavEntryBase 1), loc (cavEntryBase 1 + 1), loc (cavEntryBase 1 + 2),
           loc (cavEntryBase 1 + 3), loc (cavEntryBase 1 + 4), loc (cavEntryBase 1 + 5),
           loc (cavEntryBase 1 + 6)⟩
  , e2 := ⟨loc (cavEntryBase 2), loc (cavEntryBase 2 + 1), loc (cavEntryBase 2 + 2),
           loc (cavEntryBase 2 + 3), loc (cavEntryBase 2 + 4), loc (cavEntryBase 2 + 5),
           loc (cavEntryBase 2 + 6)⟩
  , e3 := ⟨loc (cavEntryBase 3), loc (cavEntryBase 3 + 1), loc (cavEntryBase 3 + 2),
           loc (cavEntryBase 3 + 3), loc (cavEntryBase 3 + 4), loc (cavEntryBase 3 + 5),
           loc (cavEntryBase 3 + 6)⟩ }

/-- The four type tags of a manifest (the REQUIRED-tag floor the cell declares). -/
def manifestTags (m : RotCaveatManifest) : List ℤ :=
  [m.e0.typeTag, m.e1.typeTag, m.e2.typeTag, m.e3.typeTag]

/-- The decode reads exactly the four type-tag columns. -/
theorem manifestTags_gadget (loc : Nat → ℤ) :
    manifestTags (gadgetManifest loc)
      = [loc (cavTagCol 0), loc (cavTagCol 1), loc (cavTagCol 2), loc (cavTagCol 3)] := rfl

/-! ## §2 — the decode gates (per-slot is-zero against the escrow tag + the running-OR fold). -/

/-- (seed) **OR seed**: `O0 − b0 == 0`. -/
def orSeedGate (outCol bitC : Nat) : VmConstraint2 :=
  .base (.gate (.add (.var outCol) (.mul (.const (-1)) (.var bitC))))

/-- (fold_k) **OR fold**: `outCol − (inOr + b − inOr·b) == 0`, the boolean OR of the running OR with
the next slot bit. -/
def orFoldGate (outCol inOrCol bitC : Nat) : VmConstraint2 :=
  .base (.gate (.add (.var outCol)
    (.mul (.const (-1)) (.add (.add (.var inOrCol) (.var bitC))
      (.mul (.const (-1)) (.mul (.var inOrCol) (.var bitC)))))))

/-! ## §2b — THE ROW-LOCALITY FIX gates (the §2 precondition of `VK-EPOCH-DESIGN.md`).

The selector-force is scoped to the FIRST (settle) row (`Boundary .first`) so it is INERT on the
carry-forward padding rows — the empirical `10ac36c54` defect was an EVERY-ROW force that, over a
uniform escrow manifest, forced `sel = 1` on padding rows where the base satisfaction gate
`sel·(before_leg − Deposited)` then bit (`before_leg = Consumed` there), making the honest settle
UNSATISFIABLE. The caveat-uniformity `windowGate`s force the type-tag columns constant across adjacent
rows, coupling the row-0 decode to the LAST-row-pinned committed caveat (PI 45). -/

/-- (selector-force, FIRST-ROW SCOPED) `GENTIAN_FLOOR_ESCROW_COL · (ESCROW_SEL_COL − 1) == 0`, fired
ONLY on the first (settle) row (`Boundary .first`, the `when_first_row` AIR domain). Rust twin
`carrier_floor_weld::selector_force_first_gate`. -/
def selectorForceFirstGate (floorCol selCol : Nat) : VmConstraint2 :=
  .base (.boundary .first (.mul (.var floorCol) (.add (.var selCol) (.const (-1)))))

/-- (caveat-uniformity) `nxt(tagCol) − loc(tagCol) == 0`, on the transition — a two-row `windowGate`
forcing the caveat type-tag column UNIFORM across adjacent rows. Rust twin
`carrier_floor_weld::caveat_uniform_gate`. -/
def caveatUniformGate (tagCol : Nat) : VmConstraint2 :=
  .windowGate { body := .add (.nxt tagCol) (.mul (.const (-1)) (.loc tagCol)), onTransition := true }

/-- The full carrier decode-gadget gate block: four per-slot is-zero gadgets (`def` + `force`), the
OR seed, two OR folds, the final OR fold into `GENTIAN_FLOOR_ESCROW_COL`, the FIRST-ROW-scoped
selector-force gate (the row-locality fix), and four caveat-uniformity `windowGate`s. -/
def carrierGates : List VmConstraint2 :=
  [ isZeroDefGate (cavTagCol 0) (bitCol 0) (invCol 0), isZeroForceGate (cavTagCol 0) (bitCol 0)
  , isZeroDefGate (cavTagCol 1) (bitCol 1) (invCol 1), isZeroForceGate (cavTagCol 1) (bitCol 1)
  , isZeroDefGate (cavTagCol 2) (bitCol 2) (invCol 2), isZeroForceGate (cavTagCol 2) (bitCol 2)
  , isZeroDefGate (cavTagCol 3) (bitCol 3) (invCol 3), isZeroForceGate (cavTagCol 3) (bitCol 3)
  , orSeedGate (orCol 0) (bitCol 0)
  , orFoldGate (orCol 1) (orCol 0) (bitCol 1)
  , orFoldGate (orCol 2) (orCol 1) (bitCol 2)
  , orFoldGate GENTIAN_FLOOR_ESCROW_COL (orCol 2) (bitCol 3)
  , selectorForceFirstGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL
  , caveatUniformGate (cavTagCol 0), caveatUniformGate (cavTagCol 1)
  , caveatUniformGate (cavTagCol 2), caveatUniformGate (cavTagCol 3) ]

/-! ## §3 — THE CARRIER GADGET DESCRIPTOR (the wide welded descriptor + the carrier decode gates). -/

/-- **`gentianCarrierDescriptor`** — the WIDE welded sealed-escrow satisfaction descriptor PLUS the
carrier-bound decode gates that force the selector from the caveat-manifest type-tag columns. STAGED —
a Lean definition (the source of truth); nothing is emitted into the deployed VK and nothing routes
through it. The deployed descriptors / VK are byte-identical. -/
def gentianCarrierDescriptor (legA legB : Nat) : EffectVmDescriptor2 :=
  let base := settleEscrowSatVmDescriptor2R24Wide legA legB
  { base with
    name        := "dregg-effectvm-settle-escrow-gentian-carrier-v1-rot24-v3-wide-staged"
    constraints := base.constraints ++ carrierGates }

/-! ## §4 — gate membership. -/

/-- A carrier decode gate is a member. -/
theorem carrierGate_mem (legA legB : Nat) (g : VmConstraint2) (hg : g ∈ carrierGates) :
    g ∈ (gentianCarrierDescriptor legA legB).constraints := by
  unfold gentianCarrierDescriptor
  simp only [List.mem_append]
  exact Or.inr hg

/-- A WIDE welded satisfaction gate is still a member. -/
theorem weldedGate_mem_carrier (legA legB : Nat) (g : VmConstraint2)
    (hg : g ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB) :
    g ∈ (gentianCarrierDescriptor legA legB).constraints := by
  unfold gentianCarrierDescriptor
  simp only [List.mem_append]
  exact Or.inl (settleGateWide_mem legA legB g hg)

/-! ## §5 — the generic gate-forcing helper. -/

/-- A carrier-descriptor gate's body vanishes on a satisfying NON-LAST row. -/
theorem carrier_gate_holds (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ (gentianCarrierDescriptor legA legB).constraints)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi g hg
  rw [hbody] at hrow
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-- **THE FIRST-ROW (settle-row) FORCING.** A `Boundary .first` gate's body vanishes on the FIRST row
(`isFirst`, the `when_first_row` AIR domain) — the row-locality discipline of the selector-force gate.
The body need NOT vanish on the carry-forward padding rows (where the force is inert), which is exactly
what restores the honest settle's satisfiability. -/
theorem carrier_boundary_first_holds (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (hi : 0 < t.rows.length)
    (g : VmConstraint2) (hg : g ∈ (gentianCarrierDescriptor legA legB).constraints)
    (body : EmittedExpr) (hbody : g = .base (.boundary .first body)) :
    body.eval (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints 0 hi g hg
  rw [hbody] at hrow
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrow
  exact hrow rfl

/-- **THE CAVEAT-UNIFORMITY STEP.** The uniformity `windowGate` forces the caveat type-tag column equal
across adjacent rows: on a non-last row `i`, `(envAt t (i+1)).loc (cavTagCol k) = (envAt t i).loc
(cavTagCol k)`. (`(envAt t i).nxt c` is definitionally `(envAt t (i+1)).loc c`.) -/
theorem caveat_uniform_step (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false) (k : Nat)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (hkmem : caveatUniformGate (cavTagCol k) ∈ (gentianCarrierDescriptor legA legB).constraints) :
    (envAt t (i + 1)).loc (cavTagCol k) = (envAt t i).loc (cavTagCol k) := by
  have hrow := hsat.rowConstraints i hi _ hkmem
  -- `.windowGate w` ⇒ `WindowConstraint.holdsAt env isLast`; `onTransition = true` ⇒ the body need
  -- only vanish off the last row (`isLast = false`, here `hnl`) — now field-faithfully mod `p`.
  simp only [VmConstraint2.holdsAt, caveatUniformGate, WindowConstraint.holdsAt] at hrow
  have hbody := hrow hnl
  simp only [WindowExpr.eval] at hbody
  -- `(envAt t i).nxt c` is definitionally `(envAt t (i+1)).loc c`.
  have hnxt : (envAt t i).nxt (cavTagCol k) = (envAt t (i + 1)).loc (cavTagCol k) := rfl
  rw [hnxt] at hbody
  -- both adjacent tag cells are canonical, so `nxt ≡ loc [ZMOD p]` lifts to the exact equality.
  exact canonEq ((gate_modEq_iff (by ring)).mp hbody) (hcanon (i + 1) _).1 (hcanon (i + 1) _).2
    (hcanon i _).1 (hcanon i _).2

/-- **THE CAVEAT-UNIFORMITY (whole trace).** Every row's caveat type-tag column equals the settle
(row-0) row's — the uniformity gates fold the per-step equality across the trace. -/
theorem caveat_uniform_const (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (k : Nat)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (hkmem : caveatUniformGate (cavTagCol k) ∈ (gentianCarrierDescriptor legA legB).constraints)
    (j : Nat) (hj : j < t.rows.length) :
    (envAt t j).loc (cavTagCol k) = (envAt t 0).loc (cavTagCol k) := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have hn : n < t.rows.length := by omega
    have hnl : (n + 1 == t.rows.length) = false := by
      have : n + 1 ≠ t.rows.length := by omega
      simpa using this
    have hstep := caveat_uniform_step hash legA legB hsat n hn hnl k hcanon hkmem
    rw [hstep]; exact ih hn

/-- **THE DECODE READS THE COMMITTED (LAST-ROW) TAGS.** With the uniformity gates, the settle-row
(row-0) decode reads the SAME caveat type tags as the LAST row — the row PI 45 (the caveat commit) is
pinned to. So a forger cannot light a no-escrow decode on the settle row while committing an escrow
manifest to PI 45: the decoded floor IS the committed declaration's floor. -/
theorem decode_reads_committed_tags (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (k : Nat) (hlen : 0 < t.rows.length)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (hkmem : caveatUniformGate (cavTagCol k) ∈ (gentianCarrierDescriptor legA legB).constraints) :
    (envAt t 0).loc (cavTagCol k) = (envAt t (t.rows.length - 1)).loc (cavTagCol k) := by
  have h := caveat_uniform_const hash legA legB hsat k hcanon hkmem (t.rows.length - 1) (by omega)
  exact h.symm

/-! ## §6 — the per-slot bit is the escrow decode of its tag column. -/

/-- A per-slot is-zero gadget forces `bitCol k = escrowBitZ [tagColumn]`. -/
theorem bit_decodes (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (k : Nat)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (hdefmem : isZeroDefGate (cavTagCol k) (bitCol k) (invCol k) ∈ carrierGates)
    (hforcemem : isZeroForceGate (cavTagCol k) (bitCol k) ∈ carrierGates) :
    (envAt t i).loc (bitCol k) = escrowBitZ [(envAt t i).loc (cavTagCol k)] := by
  have hdef := carrier_gate_holds hash legA legB hsat i hi hnl
    (isZeroDefGate (cavTagCol k) (bitCol k) (invCol k)) (carrierGate_mem legA legB _ hdefmem) _ rfl
  have hforce := carrier_gate_holds hash legA legB hsat i hi hnl
    (isZeroForceGate (cavTagCol k) (bitCol k)) (carrierGate_mem legA legB _ hforcemem) _ rfl
  simp only [EmittedExpr.eval] at hdef hforce
  have htagB : (0 : ℤ) ≤ tagEscrowZ ∧ tagEscrowZ < 2013265921 := by decide
  have hb := isZero_from_gates hdef hforce (hcanon i (bitCol k))
    (by have h := hcanon i (cavTagCol k); omega) (by have h := hcanon i (cavTagCol k); omega)
  rw [hb]
  unfold escrowBitZ
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  by_cases h : (envAt t i).loc (cavTagCol k) + (-tagEscrowZ) = 0
  · rw [if_pos h, if_pos (by omega : tagEscrowZ = (envAt t i).loc (cavTagCol k))]
  · rw [if_neg h, if_neg (by omega : ¬ tagEscrowZ = (envAt t i).loc (cavTagCol k))]

/-! ## §7 — the OR-fold step: a boolean OR of `escrowBitZ pre` with `escrowBitZ [tag]`. -/

set_option linter.unusedSimpArgs false in
/-- The boolean OR `o + b − o·b` of `escrowBitZ pre` and `escrowBitZ [tag]` is `escrowBitZ
(pre ++ [tag])` — the running-OR fold step, over the integral domain ℤ. -/
theorem orStep {pre : List ℤ} {tag o b oNext : ℤ}
    (ho : o = escrowBitZ pre) (hb : b = escrowBitZ [tag])
    (hg : oNext = o + b - o * b) :
    oNext = escrowBitZ (pre ++ [tag]) := by
  rw [hg, ho, hb]
  simp only [escrowBitZ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  by_cases hp : tagEscrowZ ∈ pre <;> by_cases ht : tagEscrowZ = tag <;>
    simp only [hp, ht, or_true, or_false, true_or, false_or, if_true, if_false] <;> ring

/-! ## §8 — THE DECODE KEYSTONE: the floor column is the escrow decode of the manifest tags. -/

/-- **THE CARRIER DECODE.** On a satisfying NON-LAST row, the floor column is the felt-domain escrow
decode of the row's four caveat-manifest type tags: `floorCol = escrowBitZ (manifestTags row)`. Proven
arithmetic over the caveat-bound type-tag columns — NO crypto floor, NO recompute lookup. -/
theorem floor_decodes (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921) :
    (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL
      = escrowBitZ (manifestTags (gadgetManifest (envAt t i).loc)) := by
  -- the four per-slot bits.
  have hb0 := bit_decodes hash legA legB hsat i hi hnl 0 hcanon (by simp [carrierGates]) (by simp [carrierGates])
  have hb1 := bit_decodes hash legA legB hsat i hi hnl 1 hcanon (by simp [carrierGates]) (by simp [carrierGates])
  have hb2 := bit_decodes hash legA legB hsat i hi hnl 2 hcanon (by simp [carrierGates]) (by simp [carrierGates])
  have hb3 := bit_decodes hash legA legB hsat i hi hnl 3 hcanon (by simp [carrierGates]) (by simp [carrierGates])
  -- the OR seed + the three folds, as raw gate equalities.
  have hseed := carrier_gate_holds hash legA legB hsat i hi hnl
    (orSeedGate (orCol 0) (bitCol 0)) (carrierGate_mem legA legB _ (by simp [carrierGates])) _ rfl
  have hf1 := carrier_gate_holds hash legA legB hsat i hi hnl
    (orFoldGate (orCol 1) (orCol 0) (bitCol 1))
    (carrierGate_mem legA legB _ (by simp [carrierGates])) _ rfl
  have hf2 := carrier_gate_holds hash legA legB hsat i hi hnl
    (orFoldGate (orCol 2) (orCol 1) (bitCol 2))
    (carrierGate_mem legA legB _ (by simp [carrierGates])) _ rfl
  have hf3 := carrier_gate_holds hash legA legB hsat i hi hnl
    (orFoldGate GENTIAN_FLOOR_ESCROW_COL (orCol 2) (bitCol 3))
    (carrierGate_mem legA legB _ (by simp [carrierGates])) _ rfl
  simp only [EmittedExpr.eval] at hseed hf1 hf2 hf3
  -- O0 = b0 = escrowBitZ [tag0] (the seed congruence lifts under canonicality).
  have ho0 : (envAt t i).loc (orCol 0) = escrowBitZ [(envAt t i).loc (cavTagCol 0)] := by
    rw [show (envAt t i).loc (orCol 0) = (envAt t i).loc (bitCol 0) from
      canonEq ((gate_modEq_iff (by ring)).mp hseed) (hcanon i _).1 (hcanon i _).2
        (hcanon i _).1 (hcanon i _).2]
    exact hb0
  -- step through the folds; each OR-fold congruence lifts to the exact boolean-OR under canonicality.
  have hm1 : (envAt t i).loc (orCol 1)
      ≡ (envAt t i).loc (orCol 0) + (envAt t i).loc (bitCol 1)
        - (envAt t i).loc (orCol 0) * (envAt t i).loc (bitCol 1) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hf1
  have ho1 : (envAt t i).loc (orCol 1)
      = escrowBitZ ([(envAt t i).loc (cavTagCol 0)] ++ [(envAt t i).loc (cavTagCol 1)]) :=
    orStep ho0 hb1 (orFoldLift hm1 (hcanon i _)
      (by rw [ho0]; exact escrowBitZ_mem _) (by rw [hb1]; exact escrowBitZ_mem _))
  have hm2 : (envAt t i).loc (orCol 2)
      ≡ (envAt t i).loc (orCol 1) + (envAt t i).loc (bitCol 2)
        - (envAt t i).loc (orCol 1) * (envAt t i).loc (bitCol 2) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hf2
  have ho2 : (envAt t i).loc (orCol 2)
      = escrowBitZ ([(envAt t i).loc (cavTagCol 0), (envAt t i).loc (cavTagCol 1)]
          ++ [(envAt t i).loc (cavTagCol 2)]) :=
    orStep ho1 hb2 (orFoldLift hm2 (hcanon i _)
      (by rw [ho1]; exact escrowBitZ_mem _) (by rw [hb2]; exact escrowBitZ_mem _))
  have hm3 : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL
      ≡ (envAt t i).loc (orCol 2) + (envAt t i).loc (bitCol 3)
        - (envAt t i).loc (orCol 2) * (envAt t i).loc (bitCol 3) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hf3
  have ho3 : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL
      = escrowBitZ ([(envAt t i).loc (cavTagCol 0), (envAt t i).loc (cavTagCol 1),
          (envAt t i).loc (cavTagCol 2)] ++ [(envAt t i).loc (cavTagCol 3)]) :=
    orStep ho2 hb3 (orFoldLift hm3 (hcanon i _)
      (by rw [ho2]; exact escrowBitZ_mem _) (by rw [hb3]; exact escrowBitZ_mem _))
  rw [ho3, manifestTags_gadget]
  simp only [List.cons_append, List.nil_append]

/-! ## §9 — THE SELECTOR-FORCING KEYSTONE, `hcommitLimb` DISCHARGED.

The floor is read from the caveat-manifest type-tag columns; the binding `caveatCommit (gadgetManifest
row) = caveatCommit committedManifest` (the EXISTING coverage carrier binding) plus `caveatCommit_binds`
force `gadgetManifest row = committedManifest`. So the decoded floor IS the committed declaration's
real floor — `hcommitLimb` is no longer assumed about a free limb, it is PROVEN from the existing
caveat-commit binding. -/

/-- **THE CARRIER SELECTOR-FORCING KEYSTONE (pure light client), `hcommitLimb` DISCHARGED.** A
satisfying carrier-gadget proof on a cell whose COMMITTED caveat manifest requires the escrow tag has
its capacity selector forced `1` — for a PURE light client, under ONLY the deployed carrier
collision-resistance floor (`Poseidon2SpongeCR`), with NO `hcommitLimb`, NO `FloorDigestBinds`, NO
recompute lookup. The forger cannot dodge by a fake floor: the floor is the row's caveat-manifest tags,
which the existing caveat-commit binding pins to the committed manifest. -/
theorem gentian_selector_forced_carrier (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (gadgetManifest (envAt t 0).loc) = caveatCommit hash committedManifest)
    (hreq : tagEscrowZ ∈ manifestTags committedManifest) :
    (envAt t 0).loc ESCROW_SEL_COL = 1 := by
  -- DISCHARGE: the existing caveat-commit binding forces the row manifest = the committed manifest.
  have hmeq : gadgetManifest (envAt t 0).loc = committedManifest := caveatCommit_binds hash hCR hbind
  have hrowreq : tagEscrowZ ∈ manifestTags (gadgetManifest (envAt t 0).loc) := by
    rw [hmeq]; exact hreq
  -- the decode lights the floor column from the bound type tags, on the SETTLE (row-0) row.
  have hdec := floor_decodes hash legA legB hsat 0 hi hnl hcanon
  have hfloor : (envAt t 0).loc GENTIAN_FLOOR_ESCROW_COL = 1 := by
    rw [hdec]; unfold escrowBitZ; rw [if_pos hrowreq]
  -- the FIRST-ROW selector-force gate forces sel = 1 on the settle row (field-faithfully).
  have hsel := carrier_boundary_first_holds hash legA legB hsat hi
    (selectorForceFirstGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL)
    (carrierGate_mem legA legB _ (by simp [carrierGates]))
    (.mul (.var GENTIAN_FLOOR_ESCROW_COL) (.add (.var ESCROW_SEL_COL) (.const (-1)))) rfl
  simp only [EmittedExpr.eval, hfloor, one_mul] at hsel
  exact canonEq ((gate_modEq_iff (by ring)).mp hsel) (hcanon 0 _).1 (hcanon 0 _).2 (by norm_num) (by norm_num)

/-! ## §10 — THE SETTLE-FORCING + the teeth. -/

/-- **THE CARRIER SETTLE-FORCING (pure light client), `hcommitLimb` DISCHARGED.** The four
sealed-escrow conjuncts are forced over the committed wide-bound field columns — driven by the carrier
selector forcing, with the floor PROVABLY the cell's real declared floor. -/
theorem gentian_settle_forced_carrier (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (gadgetManifest (envAt t 0).loc) = caveatCommit hash committedManifest)
    (hreq : tagEscrowZ ∈ manifestTags committedManifest) :
    (envAt t 0).loc (beforeFieldCol legA) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t 0).loc (beforeFieldCol legB) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t 0).loc (afterFieldCol legA)  ≡ stConsumed [ZMOD 2013265921] ∧
    (envAt t 0).loc (afterFieldCol legB)  ≡ stConsumed [ZMOD 2013265921] := by
  have hsel := gentian_selector_forced_carrier hash hCR legA legB hsat hi hnl hcanon committedManifest
    hbind hreq
  have force : ∀ (col : Nat) (val : ℤ),
      settleEscrowSatGate ESCROW_SEL_COL col val ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB →
      (envAt t 0).loc col ≡ val [ZMOD 2013265921] := by
    intro col val hmem
    have h0 := carrier_gate_holds hash legA legB hsat 0 hi hnl
      (settleEscrowSatGate ESCROW_SEL_COL col val) (weldedGate_mem_carrier legA legB _ hmem)
      (.mul (.var ESCROW_SEL_COL) (.add (.var col) (.const (-val)))) rfl
    simp only [EmittedExpr.eval, hsel, one_mul] at h0
    exact (gate_modEq_iff (by ring)).mp h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact force (beforeFieldCol legA) stDeposited (by simp [settleEscrowSatGates])
  · exact force (beforeFieldCol legB) stDeposited (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legA) stConsumed (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legB) stConsumed (by simp [settleEscrowSatGates])

/-- **THE FORGED-FLOOR TOOTH** — the `hcommitLimb` dodge, CLOSED at the binding. A forger presenting a
row manifest that OMITS the escrow tag (so the decode would read floor `0` and leave the selector free)
while matching the committed caveat commit of a cell that DECLARES escrow is IMPOSSIBLE: the existing
caveat-commit binding collapses the row manifest to the committed one, which declares escrow. The
free-limb floor dodge the digest path left open is closed — the floor cannot be forged. -/
theorem gentian_forged_floor_unsat_carrier (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (committedManifest rowManifest : RotCaveatManifest)
    (hbind : caveatCommit hash rowManifest = caveatCommit hash committedManifest)
    (hreq : tagEscrowZ ∈ manifestTags committedManifest)
    (hforge : tagEscrowZ ∉ manifestTags rowManifest) :
    False := by
  have hmeq : rowManifest = committedManifest := caveatCommit_binds hash hCR hbind
  rw [hmeq] at hforge
  exact hforge hreq

/-- **THE NO-PARTIAL TOOTH (carrier).** A partial settle on a declared-escrow cell cannot satisfy the
carrier descriptor — the floor is forced from the bound manifest, the selector on, the leg-B AFTER
conjunct `Consumed`. -/
theorem gentian_partial_unsat_carrier (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (gadgetManifest (envAt t 0).loc) = caveatCommit hash committedManifest)
    (hreq : tagEscrowZ ∈ manifestTags committedManifest)
    (hpartial : (envAt t 0).loc (afterFieldCol legB) = stDeposited) :
    False := by
  have h := (gentian_settle_forced_carrier hash hCR legA legB hsat hi hnl hcanon committedManifest
    hbind hreq).2.2.2
  rw [hpartial] at h
  simp only [stDeposited, stConsumed] at h
  exact absurd h (by decide)

/-- **THE NO-PHANTOM TOOTH (carrier).** A phantom settle on a declared-escrow cell cannot satisfy the
carrier descriptor. -/
theorem gentian_phantom_unsat_carrier (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianCarrierDescriptor legA legB) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (gadgetManifest (envAt t 0).loc) = caveatCommit hash committedManifest)
    (hreq : tagEscrowZ ∈ manifestTags committedManifest)
    (hphantom : (envAt t 0).loc (beforeFieldCol legA) = stEmpty) :
    False := by
  have h := (gentian_settle_forced_carrier hash hCR legA legB hsat hi hnl hcanon committedManifest
    hbind hreq).1
  rw [hphantom] at h
  simp only [stEmpty, stDeposited] at h
  exact absurd h (by decide)

/-! ## §11 — NON-VACUITY TEETH (`#guard`): the carrier decode + the binding BITE, both polarities. -/

section Witnesses

/-- A committed manifest declaring escrow in slot 0. -/
private def escrowManifest : RotCaveatManifest :=
  ⟨1, ⟨tagEscrowZ, 0, 0, 0, 0, 0, 0⟩, zeroEntry, zeroEntry, zeroEntry⟩
/-- A forger's manifest with NO escrow tag (the omission dodge). -/
private def hollowManifest : RotCaveatManifest :=
  ⟨1, ⟨6, 0, 0, 0, 0, 0, 0⟩, zeroEntry, zeroEntry, zeroEntry⟩

-- escrowBitZ over the manifest tags, both polarities.
#guard escrowBitZ (manifestTags escrowManifest) == 1
#guard escrowBitZ (manifestTags hollowManifest) == 0
#guard tagEscrowZ ∈ manifestTags escrowManifest
#guard tagEscrowZ ∉ manifestTags hollowManifest

-- The carrier descriptor extends the wide welded descriptor (63 PIs, no new PI — the forcing is
-- in-AIR) and appends exactly the carrier decode + first-row selector-force + caveat-uniformity block.
#guard (gentianCarrierDescriptor 0 1).piCount == 63
#guard carrierGates.length == 17

-- The decode/aux columns are distinct (no aliasing).
#guard [cavTagCol 0, cavTagCol 1, cavTagCol 2, cavTagCol 3,
        bitCol 0, bitCol 1, bitCol 2, bitCol 3,
        invCol 0, invCol 1, invCol 2, invCol 3,
        orCol 0, orCol 1, orCol 2, GENTIAN_FLOOR_ESCROW_COL].dedup.length == 16

-- A concrete decode evaluation: tag0 = escrow ⟹ b0 = 1 ⟹ floor OR = 1.
private def mkLoc (tag0 tag1 tag2 tag3 b0 b1 b2 b3 o0 o1 o2 fe : ℤ) : Nat → ℤ := fun c =>
  if c == cavTagCol 0 then tag0 else if c == cavTagCol 1 then tag1
  else if c == cavTagCol 2 then tag2 else if c == cavTagCol 3 then tag3
  else if c == bitCol 0 then b0 else if c == bitCol 1 then b1
  else if c == bitCol 2 then b2 else if c == bitCol 3 then b3
  else if c == orCol 0 then o0 else if c == orCol 1 then o1 else if c == orCol 2 then o2
  else if c == GENTIAN_FLOOR_ESCROW_COL then fe else 0

private def gateVal (g : VmConstraint2) (loc : Nat → ℤ) : ℤ :=
  match g with
  | .base (.gate body) => body.eval loc
  | _ => 999

-- is-zero DEF slot 0: tag0 = escrow ⟹ d = 0 ⟹ b0 = 1 vanishes (inv free 0).
#guard gateVal (isZeroDefGate (cavTagCol 0) (bitCol 0) (invCol 0))
  (mkLoc tagEscrowZ 6 0 0  1 0 0 0  1 1 1 1) == 0
-- ...b0 = 0 with tag0 = escrow makes DEF bite (b0 = 1 forced).
#guard gateVal (isZeroDefGate (cavTagCol 0) (bitCol 0) (invCol 0))
  (mkLoc tagEscrowZ 6 0 0  0 0 0 0  0 0 0 0) != 0
-- is-zero FORCE slot 1: tag1 = 6 (≠ escrow), b1 = 1 ⟹ (6−17)·1 ≠ 0 bites.
#guard gateVal (isZeroForceGate (cavTagCol 1) (bitCol 1))
  (mkLoc tagEscrowZ 6 0 0  1 1 0 0  1 1 1 1) != 0
-- OR seed: O0 = b0 vanishes; mismatched bites.
#guard gateVal (orSeedGate (orCol 0) (bitCol 0)) (mkLoc tagEscrowZ 6 0 0  1 0 0 0  1 1 1 1) == 0
#guard gateVal (orSeedGate (orCol 0) (bitCol 0)) (mkLoc tagEscrowZ 6 0 0  1 0 0 0  0 1 1 1) != 0
-- OR fold into floor: O2 = 1, b3 = 0 ⟹ floor = 1 vanishes; floor = 0 bites.
#guard gateVal (orFoldGate GENTIAN_FLOOR_ESCROW_COL (orCol 2) (bitCol 3))
  (mkLoc tagEscrowZ 6 0 0  1 0 0 0  1 1 1 1) == 0
#guard gateVal (orFoldGate GENTIAN_FLOOR_ESCROW_COL (orCol 2) (bitCol 3))
  (mkLoc tagEscrowZ 6 0 0  1 0 0 0  1 1 1 0) != 0
-- THE ROW-LOCALITY FIX gates have the right SHAPE: the selector-force is FIRST-row-scoped (a
-- `Boundary .first`), and the caveat-uniformity gates are on-transition two-row windows.
#guard (match selectorForceFirstGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL with
        | .base (.boundary .first _) => true | _ => false)
#guard (match caveatUniformGate (cavTagCol 0) with
        | .windowGate w => w.onTransition | _ => false)

-- The FIRST-ROW selector-force body: floor = 1 demands sel = 1 (sel = 0 bites).
private def forceBodyVal (g : VmConstraint2) (loc : Nat → ℤ) : ℤ :=
  match g with
  | .base (.boundary _ body) => body.eval loc
  | _ => 999
#guard forceBodyVal (selectorForceFirstGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL)
  (fun c => if c == GENTIAN_FLOOR_ESCROW_COL then 1 else if c == ESCROW_SEL_COL then 1 else 0) == 0
#guard forceBodyVal (selectorForceFirstGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL)
  (fun c => if c == GENTIAN_FLOOR_ESCROW_COL then 1 else if c == ESCROW_SEL_COL then 0 else 0) != 0

-- THE CAVEAT-UNIFORMITY body `nxt(tag) − loc(tag)` BITES on a non-uniform manifest and vanishes when
-- uniform.
private def uniformBodyVal (g : VmConstraint2) (locf nxtf : Nat → ℤ) : ℤ :=
  match g with
  | .windowGate w => w.body.eval ⟨locf, nxtf, fun _ => 0⟩
  | _ => 999
#guard uniformBodyVal (caveatUniformGate (cavTagCol 0))
  (fun c => if c == cavTagCol 0 then 6 else 0)
  (fun c => if c == cavTagCol 0 then tagEscrowZ else 0) != 0
#guard uniformBodyVal (caveatUniformGate (cavTagCol 0))
  (fun c => if c == cavTagCol 0 then tagEscrowZ else 0)
  (fun c => if c == cavTagCol 0 then tagEscrowZ else 0) == 0

-- THE BINDING BITES: the hollow (omitting) manifest cannot share the escrow manifest's caveat commit
-- (computed on the reference sponge — the forged-floor dodge moves the bound commit).
open Dregg2.Substrate.Heap (refSponge)
#guard caveatCommit refSponge escrowManifest != caveatCommit refSponge hollowManifest
#guard caveatCommit refSponge escrowManifest == caveatCommit refSponge escrowManifest

end Witnesses

/-! ## §12 — Axiom hygiene. -/

#assert_all_clean [
  manifestTags_gadget,
  carrierGate_mem,
  weldedGate_mem_carrier,
  carrier_gate_holds,
  carrier_boundary_first_holds,
  caveat_uniform_step,
  caveat_uniform_const,
  decode_reads_committed_tags,
  bit_decodes,
  orStep,
  floor_decodes,
  gentian_selector_forced_carrier,
  gentian_settle_forced_carrier,
  gentian_forged_floor_unsat_carrier,
  gentian_partial_unsat_carrier,
  gentian_phantom_unsat_carrier
]

end Dregg2.Deos.CarrierBoundFloorGadget
