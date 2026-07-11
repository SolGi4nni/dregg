/-
# Dregg2.Deos.InAirAuthorityDigestSelector — the GENTIAN KEYSTONE: the capacity SELECTOR is forced
IN-AIR from the COMMITTED authority digest, so a PURE light client demands the satisfaction weld with
NO off-band verifier discipline.

`docs/deos/IN-AIR-AUTHORITY-DIGEST-GADGET.md` is the design. This module is the FIRST PROVEN RUNG of
the terminal blocker of the sealed-escrow VK flip (`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`
§6 item 2).

## The obligation this discharges

`SettleEscrowSelectorBinding.escrow_selector_bound_to_declaration` forces the sealed-escrow gate over
the committed state — but GIVEN an explicit verifier-discipline hypothesis:

  `hverifier : demandsEscrowSelector (requiredTags presented) → (envAt t 0).pub ESCROW_SEL_PI = 1`

i.e. it ASSUMES a verifier that re-derives the required-tag floor from the declaration and pins the
selector PI = 1 off-band. A PURE light client holds only the wide commit, NOT the declaration
preimage, so it CANNOT perform that re-derivation. The forcing must be moved IN-AIR.

This module does that. It adds three degree-≤2 in-AIR gates to the WIDE welded descriptor:

  (1) recompute-bind  `witDigestCol − authDigestCol == 0`   — the recompute output equals the
      committed `B_AUTHORITY_DIGEST` limb (col `EFFECT_VM_WIDTH + 24`, the r23 limb the wide commit
      binds, `gentian_auth_digest_absorbed`).
  (2) decode-boolean  `floorCol · (floorCol − 1) == 0`       — the decoded floor bit is a boolean.
  (3) selector-force  `floorCol · (ESCROW_SEL_COL − 1) == 0` — when the floor includes escrow, the
      selector is forced ON; inert otherwise.

and proves that, under the authority-digest collision-resistance floor (`DeclCommitBinds`, the SAME
floor `ConstraintBinding` carries — never an axiom), a committed declaration requiring the escrow tag
FORCES the selector ON (`gentian_selector_forced`) and hence the four sealed-escrow conjuncts
(`gentian_settle_forced`) over the committed wide-bound columns — with NO `hverifier`.

## What is and is NOT realized (no overclaim)

The gates (1)(2)(3) are REAL `VmConstraint2` constraints forced by `Satisfied2`. The two links to the
witnessed declaration —
  * `hrecompute : witDigestCol = authDigest witnessed`  (the in-AIR `hash_bytes` recompute output), and
  * `hdecode    : floorCol = escrowBit (requiredTags witnessed)`  (the in-AIR required-tag decode)
— are named-MODELED hypotheses standing for the recompute/decode GADGET FAITHFULNESS, exactly as
`CapacitySatisfaction` models `stateCommit = hash b`. Realizing them as literal constraint CHAINS —
the variable-length byte-sponge recompute of `compute_authority_digest_felt` and the
`required_capacity_caveat_tags` decode — is the named, genuinely-VK-affecting remaining work
(`IN-AIR-AUTHORITY-DIGEST-GADGET.md` §4, Option A byte-sponge / Option B felt-domain limb). This rung
proves the SELECTOR-FORCING SOUNDNESS the gadget would carry; it is STAGED, NOT emitted into a
committed VK, NOT flipped — the deployed descriptors / VK are byte-identical.

## Axiom hygiene

`#assert_all_clean` at the close. The only named hypothesis is `DeclCommitBinds` (the authority-digest
collision-resistance floor, the analog of `Poseidon2SpongeCR`); never an axiom; no core edit. The
gate-forcing reduces through the STABLE `Satisfied2.rowConstraints` interface, as in
`SettleEscrowSatWideDescriptor`.
-/
import Dregg2.Deos.SettleEscrowSatWideDescriptor
import Dregg2.Deos.ConstraintBinding

namespace Dregg2.Deos.InAirAuthorityDigestSelector

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Deos.SealedEscrow (stEmpty stDeposited stConsumed)
open Dregg2.Deos.ConstraintBinding (Tag tagSettleEscrow DeclCommitBinds)
open Dregg2.Deos.SettleEscrowSatDescriptor
  (ESCROW_SEL_COL beforeFieldCol afterFieldCol settleEscrowSatGate settleEscrowSatGates
   settleEscrowV1Base)
open Dregg2.Deos.SettleEscrowSatWideDescriptor
  (settleEscrowSatVmDescriptor2R24Wide settleGateWide_mem settleEscrowWide_forces_settle_gate)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

set_option autoImplicit false

/-! ## §1 — the GENTIAN columns + the decode predicate.

`ESCROW_SEL_COL = prmCol 2` (col 70, the existing satisfaction selector). The two new free PARAM
columns carry the gadget's recompute output and decoded floor bit; the committed authority-digest
limb is the rotated `B_AUTHORITY_DIGEST` register (r23 = pre-limb 24), based at `EFFECT_VM_WIDTH`. -/

/-- The recompute-output column: a free PARAM slot (`prmCol 3`, col 71) the producer fills with the
in-AIR `hash_bytes` recompute of the witnessed declaration's authority digest. Rust twin
`authority_digest_weld::WIT_DIGEST_COL`. -/
def GENTIAN_WIT_DIGEST_COL : Nat := prmCol 3

/-- The decoded-floor column: a free PARAM slot (`prmCol 4`, col 72) the producer fills with the
boolean "the witnessed declaration's required-tag floor includes the escrow tag". Rust twin
`authority_digest_weld::FLOOR_ESCROW_COL`. -/
def GENTIAN_FLOOR_ESCROW_COL : Nat := prmCol 4

/-- The committed authority-digest column: the rotated `B_AUTHORITY_DIGEST` limb (r23 = pre-limb 24)
of the wide BEFORE block, based at `EFFECT_VM_WIDTH`. The ~124-bit wide commit absorbs it
(`gentian_auth_digest_absorbed`). Rust twin `BEFORE_BASE + B_AUTHORITY_DIGEST`. -/
def gentianAuthDigestCol : Nat := EFFECT_VM_WIDTH + 24

/-- The decode of a required-tag floor into the boolean "includes the escrow tag" (`1`/`0`). The
in-AIR `floorCol` carries this for the witnessed declaration; the in-circuit realization is the
`required_capacity_caveat_tags` decode (§4 remaining). -/
def escrowBit (required : List Tag) : ℤ := if tagSettleEscrow ∈ required then 1 else 0

theorem escrowBit_eq_one_of_mem {required : List Tag} (h : tagSettleEscrow ∈ required) :
    escrowBit required = 1 := by
  unfold escrowBit; rw [if_pos h]

/-! ## §2 — the three GENTIAN gates (degree ≤ 2, the `VmConstraint::Gate` vocabulary). -/

/-- (1) **recompute-bind**: `witDigestCol − authDigestCol == 0`. Forces the recompute output equal to
the committed authority-digest limb. -/
def gentianRecomputeBindGate (witCol authCol : Nat) : VmConstraint2 :=
  .base (.gate (.add (.var witCol) (.mul (.const (-1)) (.var authCol))))

/-- (2) **decode-boolean**: `floorCol · (floorCol − 1) == 0`. Forces the decoded floor bit ∈ {0,1}. -/
def gentianBooleanGate (floorCol : Nat) : VmConstraint2 :=
  .base (.gate (.mul (.var floorCol) (.add (.var floorCol) (.const (-1)))))

/-- (3) **selector-force**: `floorCol · (selCol − 1) == 0`. When the floor bit is `1`, forces the
selector ON; inert when `0`. -/
def gentianSelectorForceGate (floorCol selCol : Nat) : VmConstraint2 :=
  .base (.gate (.mul (.var floorCol) (.add (.var selCol) (.const (-1)))))

/-- The three GENTIAN gates, appended to the WIDE welded descriptor. -/
def gentianGates : List VmConstraint2 :=
  [ gentianRecomputeBindGate GENTIAN_WIT_DIGEST_COL gentianAuthDigestCol,
    gentianBooleanGate GENTIAN_FLOOR_ESCROW_COL,
    gentianSelectorForceGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL ]

/-! ## §3 — THE GENTIAN DESCRIPTOR (the WIDE welded descriptor + the in-AIR selector-forcing gates). -/

/-- **`gentianSelectorDescriptor`** — the WIDE welded sealed-escrow satisfaction descriptor
(`settleEscrowSatVmDescriptor2R24Wide`, whose satisfaction-gate field columns ARE absorbed into the
~124-bit wide commit) PLUS the three GENTIAN in-AIR gates that force the selector from the committed
authority digest. STAGED — a Lean definition (the source of truth); NOTHING is emitted into the
deployed wide registry / VK and nothing routes through it. -/
def gentianSelectorDescriptor (legA legB : Nat) : EffectVmDescriptor2 :=
  let base := settleEscrowSatVmDescriptor2R24Wide legA legB
  { base with
    name        := "dregg-effectvm-settle-escrow-gentian-v1-rot24-v3-wide-staged"
    constraints := base.constraints ++ gentianGates }

/-- Each GENTIAN gate is a member of the descriptor's constraint list (it lands in the appended
`gentianGates` block, after the wide-welded host). -/
theorem gentianGate_mem (legA legB : Nat) (g : VmConstraint2) (hg : g ∈ gentianGates) :
    g ∈ (gentianSelectorDescriptor legA legB).constraints := by
  unfold gentianSelectorDescriptor
  simp only [List.mem_append]
  exact Or.inr hg

/-- Each WIDE-welded satisfaction gate is STILL a member of the gentian descriptor (it lives in the
wide base's constraints, which the gentian descriptor extends). -/
theorem weldedGate_mem_gentian (legA legB : Nat) (g : VmConstraint2)
    (hg : g ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB) :
    g ∈ (gentianSelectorDescriptor legA legB).constraints := by
  unfold gentianSelectorDescriptor
  simp only [List.mem_append]
  exact Or.inl (settleGateWide_mem legA legB g hg)

/-! ## §4 — THE WIDE-BINDING of the committed authority-digest limb.

The committed `B_AUTHORITY_DIGEST` limb (r23 = pre-limb 24) is one of the 37 pre-iroot BEFORE limbs
`{EFFECT_VM_WIDTH, …, EFFECT_VM_WIDTH+36}` the wide BEFORE carriers consume into the published 8-felt
commit (`EffectVmEmitRotationWide.rotV3WideSpecs`); `rotV3Wide_binds_published` (under
`Poseidon2WideCR`) then binds it. So a PURE light client binding the wide BEFORE commit binds the
committed authority digest — exactly the column the recompute-bind gate ties the recompute to. This is
the same absorption argument `SettleEscrowSatWideDescriptor.beforeFieldCol_absorbed` makes for the
satisfaction-gate field columns. -/

/-- **THE AUTHORITY-DIGEST ABSORPTION KEYSTONE.** The committed authority-digest column
`gentianAuthDigestCol = EFFECT_VM_WIDTH + 24` is a member of the 37 pre-iroot BEFORE limbs the wide
carriers absorb (`24 < 37`). So a pure light client binding the wide commit binds it. -/
theorem gentian_auth_digest_absorbed :
    gentianAuthDigestCol ∈ (List.range 37).map (EFFECT_VM_WIDTH + ·) := by
  rw [List.mem_map]
  refine ⟨24, ?_, ?_⟩
  · rw [List.mem_range]; omega
  · unfold gentianAuthDigestCol; omega

/-! ## §5 — the generic gate-forcing helper (the `Satisfied2.rowConstraints` reduction). -/

/-- Field-faithful lift: two CANONICAL (`0 ≤ · < p`, the deployed range-check invariant) integers
that are congruent mod `p` are EQUAL. -/
private theorem canonEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (hap : a < 2013265921) (hb0 : 0 ≤ b) (hbp : b < 2013265921) : a = b := by
  unfold Int.ModEq at h
  rwa [Int.emod_eq_of_lt ha0 hap, Int.emod_eq_of_lt hb0 hbp] at h

/-- A GENTIAN-descriptor gate's body vanishes mod `p` on a satisfying NON-LAST row. Generic over any
`.base (.gate body)` constraint of the descriptor; the SAME reduction
`SettleEscrowSatWideDescriptor.welded_gate_holds_wide` uses (now field-faithful). -/
theorem gentian_gate_holds (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianSelectorDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ (gentianSelectorDescriptor legA legB).constraints)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi g hg
  rw [hbody] at hrow
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-! ## §6 — HALF A (the in-AIR recompute-bind forces the digests equal). -/

/-- **The recompute-bind gate forces the recompute output equal to the committed limb.** On a
satisfying non-last row, `witDigestCol = authDigestCol`. -/
theorem recompute_binds (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianSelectorDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcWit : 0 ≤ (envAt t i).loc GENTIAN_WIT_DIGEST_COL
      ∧ (envAt t i).loc GENTIAN_WIT_DIGEST_COL < 2013265921)
    (hcAuth : 0 ≤ (envAt t i).loc gentianAuthDigestCol
      ∧ (envAt t i).loc gentianAuthDigestCol < 2013265921) :
    (envAt t i).loc GENTIAN_WIT_DIGEST_COL = (envAt t i).loc gentianAuthDigestCol := by
  have h := gentian_gate_holds hash legA legB hsat i hi hnl
    (gentianRecomputeBindGate GENTIAN_WIT_DIGEST_COL gentianAuthDigestCol)
    (gentianGate_mem legA legB _ (by simp [gentianGates]))
    (.add (.var GENTIAN_WIT_DIGEST_COL) (.mul (.const (-1)) (.var gentianAuthDigestCol))) rfl
  simp only [EmittedExpr.eval] at h
  -- the recompute-bind gate is `wit − auth ≡ 0 [ZMOD p]`; both limbs are canonical digest cells,
  -- so the congruence lifts to the exact ℤ equality the CR floor consumes.
  exact canonEq ((gate_modEq_iff (by ring)).mp h) hcWit.1 hcWit.2 hcAuth.1 hcAuth.2

/-! ## §7 — HALF B (the forced floor bit forces the selector ON). -/

/-- **The selector-force gate, with the floor bit `1`, forces the selector ON.** On a satisfying
non-last row, if `floorCol = 1` then `ESCROW_SEL_COL = 1`. -/
theorem floor_forces_selector (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianSelectorDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hfloor : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL = 1)
    (hcSel : 0 ≤ (envAt t i).loc ESCROW_SEL_COL ∧ (envAt t i).loc ESCROW_SEL_COL < 2013265921) :
    (envAt t i).loc ESCROW_SEL_COL = 1 := by
  have h := gentian_gate_holds hash legA legB hsat i hi hnl
    (gentianSelectorForceGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL)
    (gentianGate_mem legA legB _ (by simp [gentianGates]))
    (.mul (.var GENTIAN_FLOOR_ESCROW_COL) (.add (.var ESCROW_SEL_COL) (.const (-1)))) rfl
  simp only [EmittedExpr.eval, hfloor, one_mul] at h
  -- with the floor bit `1` the gate is `sel − 1 ≡ 0 [ZMOD p]`; `sel` is a canonical selector cell,
  -- so it is forced exactly to `1`.
  exact canonEq ((gate_modEq_iff (by ring)).mp h) hcSel.1 hcSel.2 (by norm_num) (by norm_num)

/-! ## §8 — THE GENTIAN SELECTOR-FORCING KEYSTONE.

Composed: under the authority-digest collision-resistance floor (`DeclCommitBinds`), a committed
declaration requiring the escrow tag FORCES the selector ON — with NO off-band verifier discipline.
The forger cannot dodge by an alternate declaration (the recompute-bind + CR floor force the same
required floor) nor by `sel = 0` (the selector-force gate). The named-modeled `hrecompute`/`hdecode`
stand for the recompute/decode gadget faithfulness (§4 of the design — the remaining VK work). -/

/-- **THE SELECTOR-FORCING KEYSTONE (pure light client).** Given:
  * the authority-digest binding floor (`DeclCommitBinds authDigest requiredTags`),
  * a committed declaration requiring the escrow tag, and ANY witnessed declaration whose RECOMPUTED
    digest equals the committed authority-digest limb (the recompute-bind gate + `hrecompute`),
  * the decode column reflecting the witnessed declaration's floor (`hdecode`),
  * the committed authority-digest limb carrying the committed declaration's digest (`hcommitLimb` —
    the wide-bound limb, `gentian_auth_digest_absorbed`),
  * a satisfying trace whose row `i` is non-last,
then the selector column is FORCED to `1`. The forger can dodge NEITHER by a hollow declaration NOR by
`sel = 0`. This is the in-AIR realization of `SettleEscrowSelectorBinding`'s `hverifier`. -/
theorem gentian_selector_forced {Decl : Type}
    (authDigest : Decl → ℤ) (requiredTags : Decl → List Tag)
    (hbinds : DeclCommitBinds authDigest requiredTags)
    (committed witnessed : Decl)
    (hreq : tagSettleEscrow ∈ requiredTags committed)
    (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianSelectorDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hcommitLimb : (envAt t i).loc gentianAuthDigestCol = authDigest committed)
    (hrecompute : (envAt t i).loc GENTIAN_WIT_DIGEST_COL = authDigest witnessed)
    (hdecode : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL = escrowBit (requiredTags witnessed)) :
    (envAt t i).loc ESCROW_SEL_COL = 1 := by
  -- HALF A: the recompute-bind gate ties the recompute output to the committed limb.
  have hbind := recompute_binds hash legA legB hsat i hi hnl (hcanon _) (hcanon _)
  -- ⟹ the witnessed digest equals the committed digest.
  have hdigeq : authDigest witnessed = authDigest committed := by
    rw [← hrecompute, hbind, hcommitLimb]
  -- The CR floor forces the SAME required-tag floor.
  have htags : requiredTags witnessed = requiredTags committed := hbinds witnessed committed hdigeq
  -- ⟹ the witnessed declaration ALSO requires the escrow tag ⟹ the decoded floor bit is 1.
  have hwitreq : tagSettleEscrow ∈ requiredTags witnessed := by rw [htags]; exact hreq
  have hfloor : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL = 1 := by
    rw [hdecode]; exact escrowBit_eq_one_of_mem hwitreq
  -- HALF B: the forced floor bit forces the selector ON.
  exact floor_forces_selector hash legA legB hsat i hi hnl hfloor (hcanon _)

/-! ## §9 — THE COMPOSED GATE-FORCING (the `hverifier`-free discharge).

With the selector forced ON, the WIDE-welded satisfaction gates (still members of the gentian
descriptor) force the four sealed-escrow conjuncts over the committed wide-bound field columns — the
SAME conclusion as `escrow_selector_bound_to_declaration`, WITHOUT its `hverifier` hypothesis. -/

/-- **THE GENTIAN DISCHARGE (pure light client).** A cell whose COMMITTED declaration requires the
escrow tag has its settle FORCED through the gate over the committed rotated BEFORE/AFTER field columns
the ~124-bit wide commit absorbs — driven by the IN-AIR selector forcing, with NO off-band verifier
discipline. This realizes the `hverifier` obligation of
`SettleEscrowSelectorBinding.escrow_selector_bound_to_declaration` in-AIR. -/
theorem gentian_settle_forced {Decl : Type}
    (authDigest : Decl → ℤ) (requiredTags : Decl → List Tag)
    (hbinds : DeclCommitBinds authDigest requiredTags)
    (committed witnessed : Decl)
    (hreq : tagSettleEscrow ∈ requiredTags committed)
    (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianSelectorDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hcommitLimb : (envAt t i).loc gentianAuthDigestCol = authDigest committed)
    (hrecompute : (envAt t i).loc GENTIAN_WIT_DIGEST_COL = authDigest witnessed)
    (hdecode : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL = escrowBit (requiredTags witnessed)) :
    (envAt t i).loc (beforeFieldCol legA) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t i).loc (beforeFieldCol legB) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t i).loc (afterFieldCol legA)  ≡ stConsumed [ZMOD 2013265921] ∧
    (envAt t i).loc (afterFieldCol legB)  ≡ stConsumed [ZMOD 2013265921] := by
  -- The selector is forced ON by the in-AIR gadget.
  have hsel := gentian_selector_forced authDigest requiredTags hbinds committed witnessed hreq
    hash legA legB hsat i hi hnl hcanon hcommitLimb hrecompute hdecode
  -- The WIDE-welded gates (members of the gentian descriptor) then force the four conjuncts
  -- (field-faithfully, as mod-`p` congruences over the committed field columns).
  have force : ∀ (col : Nat) (val : ℤ),
      settleEscrowSatGate ESCROW_SEL_COL col val ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB →
      (envAt t i).loc col ≡ val [ZMOD 2013265921] := by
    intro col val hmem
    have h0 := gentian_gate_holds hash legA legB hsat i hi hnl
      (settleEscrowSatGate ESCROW_SEL_COL col val) (weldedGate_mem_gentian legA legB _ hmem)
      (.mul (.var ESCROW_SEL_COL) (.add (.var col) (.const (-val)))) rfl
    simp only [EmittedExpr.eval, hsel, one_mul] at h0
    exact (gate_modEq_iff (by ring)).mp h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact force (beforeFieldCol legA) stDeposited (by simp [settleEscrowSatGates])
  · exact force (beforeFieldCol legB) stDeposited (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legA) stConsumed (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legB) stConsumed (by simp [settleEscrowSatGates])

/-! ## §10 — THE TEETH: a forged settle on a DECLARED-escrow cell is UNSAT.

The selector cannot be turned off (the gentian gadget forces it), so the satisfaction teeth bite even
against a forger who tries to publish `sel = 0`. -/

/-- **THE NO-PARTIAL TOOTH (gentian).** A partial settle (leg B left `Deposited` after) on a cell
whose committed declaration requires the escrow tag CANNOT satisfy the gentian descriptor — the
selector is forced on, then the leg-B AFTER conjunct forces `Consumed`. -/
theorem gentian_partial_unsat {Decl : Type}
    (authDigest : Decl → ℤ) (requiredTags : Decl → List Tag)
    (hbinds : DeclCommitBinds authDigest requiredTags)
    (committed witnessed : Decl)
    (hreq : tagSettleEscrow ∈ requiredTags committed)
    (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianSelectorDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hcommitLimb : (envAt t i).loc gentianAuthDigestCol = authDigest committed)
    (hrecompute : (envAt t i).loc GENTIAN_WIT_DIGEST_COL = authDigest witnessed)
    (hdecode : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL = escrowBit (requiredTags witnessed))
    (hpartial : (envAt t i).loc (afterFieldCol legB) = stDeposited) :
    False := by
  have h := (gentian_settle_forced authDigest requiredTags hbinds committed witnessed hreq
    hash legA legB hsat i hi hnl hcanon hcommitLimb hrecompute hdecode).2.2.2
  rw [hpartial] at h
  simp only [stDeposited, stConsumed] at h
  exact absurd h (by decide)

/-- **THE NO-PHANTOM TOOTH (gentian).** A phantom settle (leg A never `Deposited` before) on a
declared-escrow cell CANNOT satisfy the gentian descriptor. -/
theorem gentian_phantom_unsat {Decl : Type}
    (authDigest : Decl → ℤ) (requiredTags : Decl → List Tag)
    (hbinds : DeclCommitBinds authDigest requiredTags)
    (committed witnessed : Decl)
    (hreq : tagSettleEscrow ∈ requiredTags committed)
    (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianSelectorDescriptor legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hcommitLimb : (envAt t i).loc gentianAuthDigestCol = authDigest committed)
    (hrecompute : (envAt t i).loc GENTIAN_WIT_DIGEST_COL = authDigest witnessed)
    (hdecode : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL = escrowBit (requiredTags witnessed))
    (hphantom : (envAt t i).loc (beforeFieldCol legA) = stEmpty) :
    False := by
  have h := (gentian_settle_forced authDigest requiredTags hbinds committed witnessed hreq
    hash legA legB hsat i hi hnl hcanon hcommitLimb hrecompute hdecode).1
  rw [hphantom] at h
  simp only [stEmpty, stDeposited] at h
  exact absurd h (by decide)

/-! ## §11 — NON-VACUITY TEETH (`#guard`): the decode + the gates BITE, both polarities. -/

section Witnesses

-- DECODE: an escrow-requiring floor decodes to 1; a non-escrow floor decodes to 0.
#guard escrowBit [tagSettleEscrow] == 1
#guard escrowBit [] == 0
#guard escrowBit [6] == 0
#guard escrowBit [18, tagSettleEscrow, 19] == 1

-- The descriptor extends the WIDE welded descriptor's 63 PIs (no new PI; the selector forcing is
-- in-AIR, NOT a PI pin) and appends exactly the three gentian gates.
#guard (gentianSelectorDescriptor 0 1).piCount == 63
#guard gentianGates.length == 3

/-- A row assignment for the gate-body #guards: the three gentian columns set, else 0. -/
private def mkLoc (wit auth floor sel : ℤ) : Nat → ℤ := fun c =>
  if c == GENTIAN_WIT_DIGEST_COL then wit
  else if c == gentianAuthDigestCol then auth
  else if c == GENTIAN_FLOOR_ESCROW_COL then floor
  else if c == ESCROW_SEL_COL then sel
  else 0

private def gateVal (g : VmConstraint2) (loc : Nat → ℤ) : ℤ :=
  match g with
  | .base (.gate body) => body.eval loc
  | _ => 999

-- RECOMPUTE-BIND: equal wit/auth ⟹ gate (1) vanishes; unequal ⟹ it bites.
#guard gateVal (gentianRecomputeBindGate GENTIAN_WIT_DIGEST_COL gentianAuthDigestCol)
  (mkLoc 42 42 1 1) == 0
#guard gateVal (gentianRecomputeBindGate GENTIAN_WIT_DIGEST_COL gentianAuthDigestCol)
  (mkLoc 42 43 1 1) != 0

-- DECODE-BOOLEAN: floor ∈ {0,1} ⟹ gate (2) vanishes; floor = 2 ⟹ it bites.
#guard gateVal (gentianBooleanGate GENTIAN_FLOOR_ESCROW_COL) (mkLoc 0 0 1 1) == 0
#guard gateVal (gentianBooleanGate GENTIAN_FLOOR_ESCROW_COL) (mkLoc 0 0 0 1) == 0
#guard gateVal (gentianBooleanGate GENTIAN_FLOOR_ESCROW_COL) (mkLoc 0 0 2 1) != 0

-- SELECTOR-FORCE: floor = 1 demands sel = 1 (sel = 0 ⟹ gate bites); floor = 0 ⟹ inert.
#guard gateVal (gentianSelectorForceGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL) (mkLoc 0 0 1 1) == 0
#guard gateVal (gentianSelectorForceGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL) (mkLoc 0 0 1 0) != 0
#guard gateVal (gentianSelectorForceGate GENTIAN_FLOOR_ESCROW_COL ESCROW_SEL_COL) (mkLoc 0 0 0 0) == 0

end Witnesses

/-! ## §12 — Axiom hygiene. -/

#assert_all_clean [
  escrowBit_eq_one_of_mem,
  gentianGate_mem,
  weldedGate_mem_gentian,
  gentian_auth_digest_absorbed,
  gentian_gate_holds,
  recompute_binds,
  floor_forces_selector,
  gentian_selector_forced,
  gentian_settle_forced,
  gentian_partial_unsat,
  gentian_phantom_unsat
]

end Dregg2.Deos.InAirAuthorityDigestSelector
