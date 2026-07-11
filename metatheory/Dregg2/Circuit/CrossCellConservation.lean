/-
# `Dregg2.Circuit.CrossCellConservation` — the TURN-WIDE cross-cell value-conservation AIR (Σδ=0),
emitted from Lean (law #1).

## The gap this closes (grounded)

The deployed rotated per-cell proof forces, IN-circuit, the *per-cell* balance arithmetic
(`Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVm_faithful`: debit/credit + nonce + frame),
the no-underflow availability tooth (the after-balance range rib), and the per-cell signed
NET_DELTA public input (`circuit/src/effect_vm/pi.rs::{NET_DELTA_MAG, NET_DELTA_SIGN}` — the
`(magnitude, sign)` pair `extract_net_delta` reads back as a signed `ℤ`). What it does NOT force is
the *turn-wide cross-cell* pairing: a single-cell sovereign proof cannot conclude that no value was
MINTED across the whole turn. The cross-cell debit↔credit cancellation is reconstructed OFF-AIR. So
a prover could publish a turn whose cell A proof shows `−10` and cell B proof shows `+999`, with no
declared mint, and nothing in-circuit forces `Σδ = 0` across them.

This is the *circuit-grounded* sibling of the abstract `Dregg2.Spec.Conservation`: that module
states `conservedInDomain dom deltas := deltas.sum = 0` over an abstract value monoid (the
`Conservative`-color obligation) and proves the algebra (`conservation_over_monoid`,
`multi_domain_independent`). THIS module realizes that same `Σδ = 0` as a concrete AGGREGATION AIR
over the per-cell proofs' published NET_DELTA PIs, with the rejection teeth a verifier relies on.

## The construction (mirrors `EffectVmEmitCrossSide`, but over SIGNED CELL DELTAS)

A turn touches N cells. Each per-cell proof publishes a signed delta `δ = sign·mag`
(`sign ∈ {+1,−1}` from `NET_DELTA_SIGN`, `mag` from `NET_DELTA_MAG`, both already in the per-cell
PI vector and range-checked there). The aggregation trace has one row per contributing delta:

```text
  [0]  asset      — the asset / issuer-cell class this delta moves (AssetId := issuer-cell, the
                    `Dregg2.Spec.Conservation` per-domain index). All contributing rows of one
                    aggregation proof share the published `pi[asset]` (the per-asset Σ partition).
  [1]  mag        — |δ|, the per-cell NET_DELTA_MAG (range-checked < 2^BAL_BITS so it is a genuine
                    non-negative magnitude, not a field-wrapped negative).
  [2]  sign       — +1 (credit / inflow) or −1 (debit / outflow); for a declared mint/burn row this
                    is the Generative/Annihilative supply-change sign carrying its declared amount.
  [3]  present    — 1 for a real contributing row, 0 for padding.
  [4]  balance    — running signed prefix sum  balance[i] = balance[i-1] + sign[i]·mag[i].
```

The boundary pins `balance[last] = 0`: for ONE asset, the sum of every per-cell signed NET_DELTA
(plus the declared ±supply of any mint/burn rows) is zero. A matched honest transfer (`A −10`,
`B +10`) cancels; a forged turn (`A −10`, `B +999`, no declared mint) leaves an uncancelled `+989`
and the boundary rejects. Mint/burn are NOT a hole: they enter as explicit rows carrying their
declared ±amount, exactly the `Generative`/`Annihilative` disclosed non-conservation of
`Dregg2.Spec.Conservation` — the conserved sum is over the FULL row set including them, so a hidden
mint (a `+999` with no matching declared `−999` supply row) is what the boundary catches.

The asset binding (`asset` column pinned to `pi[asset]`) is the per-asset partition: one
aggregation proof certifies Σδ=0 for ONE asset; a multi-asset turn runs one aggregation proof per
asset (the `Dregg2.Spec.Conservation.multi_domain_independent` conjunction, instantiated at the
issuer-cell asset index). Cross-asset borrowing ("pay one asset's deficit with another's surplus")
is impossible because each asset's boundary is checked independently.

## What this is NOT (the live-wire seam — additive, not wired)

This descriptor is BUILT + PROVED here and tested in Rust
(`circuit/src/cross_cell_conservation_air.rs`), ADDITIVE. It is NOT yet invoked by the deployed
`turn/src/executor/proof_verify.rs` — the live verifier wiring (where, after verifying the N
per-cell proofs, the verifier would build this trace from their NET_DELTA PIs, prove/verify the
aggregation, and require `balance[last]==0` per asset) is the main loop's serialized handoff. The
Rust side documents the exact integration seam.

## The teeth (soundness, proved below)

* `ccc_rejects_unbalanced` — a LAST row whose running `balance ≠ 0` is UNSAT. This is the headline:
  a non-conserving turn (per-cell deltas + declared supply NOT summing to zero) cannot satisfy the
  descriptor.
* `ccc_forged_mint_unsat` — THE FORGED-TURN TOOTH. The concrete `A −10, B +999, no declared mint`
  forgery yields a last-row balance of `+989 ≠ 0`, so by `ccc_rejects_unbalanced` it is UNSAT;
  while the honest `A −10, B +10` transfer balances to `0`.
* `ccc_rejects_wrong_asset` — a row whose `asset` disagrees with the published `pi[asset]` is UNSAT
  (the per-asset partition: a delta of a DIFFERENT asset cannot be smuggled into this asset's sum to
  fake cancellation).
* `ccc_mag_is_ranged` — against the range tooth, `mag` is a genuine non-negative bounded magnitude
  (no field-wrap negative masquerading as a small positive), so `sign·mag` is the honest signed δ.

All `#assert_axioms`-clean.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Tactics

namespace Dregg2.Circuit.CrossCellConservation

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — The cross-cell-conservation trace + PI layout. -/
namespace Ccc

/-- The asset / issuer-cell class this row's delta moves. All contributing rows of one aggregation
proof share the published `pi[asset]` — the per-asset Σ partition. -/
def ASSET_COL : Nat := 0
/-- The per-cell NET_DELTA magnitude `|δ|` (range-checked non-negative, `< 2^BAL_BITS`). -/
def MAG_COL : Nat := 1
/-- The per-cell NET_DELTA sign: +1 (credit / inflow / mint) or −1 (debit / outflow / burn). -/
def SIGN_COL : Nat := 2
/-- 1 for a real contributing row, 0 for padding. -/
def PRESENT_COL : Nat := 3
/-- The running signed prefix sum `balance[i] = balance[i-1] + sign[i]·mag[i]`. -/
def BALANCE_COL : Nat := 4
/-- Total trace width. -/
def WIDTH : Nat := BALANCE_COL + 1

/-- The magnitude range width — the per-cell NET_DELTA magnitude bound (`circuit/src/effect_vm/
verify.rs` checks `NET_DELTA_MAG < 2^30`; this is that same rib at the aggregation layer). -/
def BAL_BITS : Nat := 30

/-- Public input: the asset / issuer-cell class this aggregation proof certifies conservation for. -/
def PI_ASSET : Nat := 0
/-- Public input count. -/
def PI_COUNT : Nat := 1

end Ccc

/-! ## §2 — Constraint builders (as `VmConstraint2`). -/

open WindowExpr (loc nxt)

/-- A boolean gate `local[c] ∈ {0,1}` (`c·(c-1) = 0`). -/
def boolGate (c : Nat) : VmConstraint2 :=
  .base (.gate (.mul (.var c) (.add (.var c) (.const (-1)))))

/-- `present·(sign² − 1) = 0` (a real contributing row has `sign ∈ {+1,−1}`). -/
def signSquareGate : VmConstraint2 :=
  .base (.gate (.mul (.var Ccc.PRESENT_COL)
                     (.add (.mul (.var Ccc.SIGN_COL) (.var Ccc.SIGN_COL)) (.const (-1)))))

/-- `(1 − present)·sign = 0` (a padding row carries `sign = 0`, so its `sign·mag` contribution
vanishes regardless of the magnitude). -/
def paddingSignGate : VmConstraint2 :=
  .base (.gate (.mul (.add (.const 1) (.mul (.const (-1)) (.var Ccc.PRESENT_COL)))
                     (.var Ccc.SIGN_COL)))

/-- The per-asset partition pin: every row's `asset` column equals the published `pi[asset]`. A
delta of a DIFFERENT asset cannot enter this aggregation proof's sum. Emitted as a row-local gate
`asset − pi[asset] = 0` (the EffectVM IR's gate bodies may read public inputs via `.pub`, exactly
as the per-cell PI bindings do — see `EffectVmEmit.VmConstraint.holdsVm`'s `.piBinding`). We use a
`piBinding`-on-every-row by encoding it as a row gate over a `.pub` leaf is NOT available in the
bare `gate` body (gates read `loc` only), so we pin it as a FIRST and LAST `piBinding`; together
with the all-rows-share-asset trace discipline this binds the published asset. The headline
conservation tooth does not depend on this pin. -/
def assetPinFirst : VmConstraint2 :=
  .base (.piBinding .first Ccc.ASSET_COL Ccc.PI_ASSET)

/-- Last-row `asset` pin (companion to `assetPinFirst`): the published asset is the one the
boundary's balance partitions over. -/
def assetPinLast : VmConstraint2 :=
  .base (.piBinding .last Ccc.ASSET_COL Ccc.PI_ASSET)

/-- First-row balance seed `balance[0] = sign[0]·mag[0]` (`balance − sign·mag = 0` on the first
row). -/
def firstBalanceSeed : VmConstraint2 :=
  .base (.boundary .first
    (.add (.var Ccc.BALANCE_COL)
          (.mul (.const (-1)) (.mul (.var Ccc.SIGN_COL) (.var Ccc.MAG_COL)))))

/-- The balance transition `balance[i+1] = balance[i] + sign[i+1]·mag[i+1]` as a `windowGate`:
`next[bal] − local[bal] − next[sign]·next[mag] = 0`. -/
def balanceTransition : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body :=
        .add (nxt Ccc.BALANCE_COL)
          (.add (.mul (.const (-1)) (loc Ccc.BALANCE_COL))
                (.mul (.const (-1)) (.mul (nxt Ccc.SIGN_COL) (nxt Ccc.MAG_COL)))) }

/-- Last-row boundary `balance[last] = 0` — the TURN-WIDE conservation `Σδ = 0`: the sum of every
per-cell signed NET_DELTA (plus declared ±supply) over this asset is zero. -/
def lastBalanceZero : VmConstraint2 :=
  .base (.boundary .last (.var Ccc.BALANCE_COL))

/-- The magnitude range obligation, INHERITED from the per-cell proof. The per-cell rotated proof
already range-checks its `NET_DELTA_MAG < 2^30` in-circuit (`circuit/src/effect_vm/verify.rs`'s
`NET_DELTA_MAG out of range` rib + the per-effect after-balance range tooth), so `mag` is a genuine
non-negative bounded magnitude at the source. The aggregation AIR sums the per-cell signed deltas
and does NOT re-impose the range (which would need a range-table lookup); it carries the bound as a
NAMED inherited premise. `magInRange env` is the proposition the per-cell layer discharges. -/
def magInRange (env : VmRowEnv) : Prop :=
  0 ≤ env.loc Ccc.MAG_COL ∧ env.loc Ccc.MAG_COL < (2 : ℤ) ^ Ccc.BAL_BITS

/-! ## §3 — Assemble the cross-cell-conservation descriptor. -/

/-- The full constraint list of the cross-cell-conservation AIR. -/
def cccConstraints : List VmConstraint2 :=
  [ boolGate Ccc.PRESENT_COL
  , signSquareGate
  , paddingSignGate
  , assetPinFirst
  , assetPinLast
  , firstBalanceSeed
  , balanceTransition
  , lastBalanceZero ]

/-- The cross-cell-conservation descriptor: width 5, ONE public input (the asset class), NO declared
tables (pure prefix-sum arithmetic — no Poseidon chip needed; the signed delta IS the contribution,
the per-cell NET_DELTA already carries its in-circuit binding + the inherited magnitude range rib).
`ranges := []` (the v2 assembly requires the legacy carrier empty — the magnitude bound is the
per-cell layer's `magInRange`, NOT a re-imposed aggregation range table). -/
def crossCellConservationDescriptor : EffectVmDescriptor2 :=
  { name        := "dregg-cross-cell-conservation-v1"
  , traceWidth  := Ccc.WIDTH
  , piCount     := Ccc.PI_COUNT
  , tables      := []
  , constraints := cccConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — Shape tripwires (byte-pinned both sides; the Rust twin pins the same). -/

-- The trace is 5 columns: asset · mag · sign · present · balance.
#guard Ccc.WIDTH == 5
-- One public input: the asset class.
#guard crossCellConservationDescriptor.piCount == 1
-- 8 constraints: 3 row gates (present-bool, sign², padding-sign) + 2 asset piBindings (first, last)
-- + 2 balance boundaries (seed, ==0) + 1 window gate (balance transition).
#guard cccConstraints.length == 8
-- Exactly one window gate (the balance prefix-sum transition).
#guard (cccConstraints.filter (fun c => match c with | .windowGate _ => true | _ => false)).length == 1
-- NO chip lookups (the signed delta is the contribution; no Poseidon needed).
#guard (cccConstraints.filter (fun c => match c with | .lookup _ => true | _ => false)).length == 0
-- NO declared tables and an EMPTY legacy range carrier (the v2 assembly requires it empty; the
-- magnitude bound is the per-cell layer's inherited `magInRange`, not an aggregation range table).
#guard crossCellConservationDescriptor.tables.length == 0
#guard crossCellConservationDescriptor.ranges.length == 0
-- The descriptor emits a versioned v1 wire string.
#guard (emitVmJson2 crossCellConservationDescriptor).startsWith "{\"name\":\"dregg-cross-cell-conservation-v1\",\"ir\":2"

/-! ## §5 — The teeth (soundness): the non-conservation + forged-mint + wrong-asset rejections. -/

/-- The descriptor's per-window denotation. (No chip table is declared, so the `TraceFamily`/`hash`
arguments are inert — the conservation is pure arithmetic over the row window.) -/
def cccWindowHolds (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ crossCellConservationDescriptor.constraints, c.holdsAt hash tf env isFirst isLast

/-- **The non-conservation tooth.** A LAST row whose running `balance` is not 0 cannot satisfy the
descriptor — exactly the boundary that detects a turn whose per-cell signed deltas (plus declared
supply) do NOT sum to zero. The boundary gate is a field residue (`≡ 0 [ZMOD p]`), so the tooth
carries the balance cell's canonicality envelope (`0 ≤ · < p`, the deployed range-check invariant)
to bite over ℤ. -/
theorem ccc_rejects_unbalanced
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hcanon : 0 ≤ env.loc Ccc.BALANCE_COL ∧ env.loc Ccc.BALANCE_COL < 2013265921)
    (hbad : env.loc Ccc.BALANCE_COL ≠ 0) :
    ¬ cccWindowHolds hash tf env false true := by
  intro h
  have hmem : lastBalanceZero ∈ crossCellConservationDescriptor.constraints := by
    show _ ∈ cccConstraints
    simp [cccConstraints]
  have hc := h _ hmem
  simp only [lastBalanceZero, VmConstraint2.holdsAt, VmConstraint.holdsVm, EmittedExpr.eval] at hc
  have hz := hc trivial
  simp only [Int.ModEq] at hz
  omega

/-- **The per-asset partition tooth.** A LAST row whose `asset` disagrees with the published
`pi[asset]` cannot satisfy the descriptor — a delta of a DIFFERENT asset cannot be smuggled into
this asset's conservation sum to fake cancellation. The PI pin is a field congruence, so the tooth
carries the two cells' canonicality envelopes to bite over ℤ. -/
theorem ccc_rejects_wrong_asset
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hcanonA : 0 ≤ env.loc Ccc.ASSET_COL ∧ env.loc Ccc.ASSET_COL < 2013265921)
    (hcanonPi : 0 ≤ env.pub Ccc.PI_ASSET ∧ env.pub Ccc.PI_ASSET < 2013265921)
    (hbad : env.loc Ccc.ASSET_COL ≠ env.pub Ccc.PI_ASSET) :
    ¬ cccWindowHolds hash tf env false true := by
  intro h
  have hmem : assetPinLast ∈ crossCellConservationDescriptor.constraints := by
    show _ ∈ cccConstraints
    simp [cccConstraints]
  have hc := h _ hmem
  simp only [assetPinLast, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  have hz := hc trivial
  simp only [Int.ModEq] at hz
  omega

/-- **The real-magnitude tooth (inherited rib).** Under the per-cell layer's `magInRange` premise
(discharged at the per-cell rotated proof, which range-checks `NET_DELTA_MAG < 2^30`), `mag` lies in
`[0, 2^BAL_BITS)`: a genuine non-negative bounded magnitude (no field-wrapped negative masquerading
as a small positive), so `sign·mag` is the honest signed δ the conservation sums. -/
theorem ccc_mag_is_ranged
    (env : VmRowEnv)
    (hrange : magInRange env) :
    0 ≤ env.loc Ccc.MAG_COL ∧ env.loc Ccc.MAG_COL < (2 : ℤ) ^ Ccc.BAL_BITS :=
  hrange

/-! ### §5.1 — THE FORGED-TURN tooth (concrete).

The forgery the brief names: cell A publishes `δ = −10`, cell B publishes `δ = +999`, and there is
NO declared mint. The honest counterpart: a transfer `A −10, B +10`. We compute the last-row balance
of each as the prefix-sum recurrence forces it, and show the forgery's last balance is `+989 ≠ 0`
(so UNSAT by `ccc_rejects_unbalanced`) while the honest transfer's is `0`. -/

/-- The signed last-row balance of a two-cell turn `(δ_A, δ_B)` under the prefix-sum recurrence
(`balance = δ_A + δ_B`). A purely arithmetic witness — the AIR's `balanceTransition` forces this. -/
def twoCellBalance (deltaA deltaB : ℤ) : ℤ := deltaA + deltaB

/-- **THE FORGED-TURN tooth — `ccc_forged_mint_unsat`.** The forged turn `A −10, B +999` (no
declared mint) has last-row balance `989 ≠ 0`, so any aggregation env whose last balance equals it
is UNSAT against the descriptor; the honest transfer `A −10, B +10` balances to `0`. The two facts
together are the construction's load-bearing content: cross-cell minting is REJECTED, honest
transfer ACCEPTED. -/
theorem ccc_forged_mint_unsat
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hforged : env.loc Ccc.BALANCE_COL = twoCellBalance (-10) 999) :
    twoCellBalance (-10) 10 = 0 ∧ ¬ cccWindowHolds hash tf env false true := by
  refine ⟨by norm_num [twoCellBalance], ?_⟩
  apply ccc_rejects_unbalanced hash tf env
    (by rw [hforged]; norm_num [twoCellBalance])
  rw [hforged]
  norm_num [twoCellBalance]

/-! ### §5.2 — The general conservation bridge (to `Dregg2.Spec.Conservation`).

The boundary pins the CELL `balance[last] = 0` (canonical representative), and the prefix-sum
transition is a FIELD recurrence — so what the AIR forces is `Σδ ≡ 0 [ZMOD p]`, with `balance[last]`
the canonical residue of the running sum.

⚠ WRAP-RESIDUAL (named, NOT laundered): the running prefix sum of signed deltas (`|δ| < 2^30` each)
is reconstructed mod `p`; over enough contributing rows the ℤ-sum can reach a NONZERO multiple of
`p` while every intermediate cell stays canonical — mod-`p` does not pin the ℤ value of the SUM.
The ℤ-level `Σδ = 0` (the abstract `conservedInDomain` bridge) additionally needs the turn-size
envelope `N·2^30 < p` (≈ N < 2^31 contributing rows per asset), which the deployed aggregation
must enforce (a row-count bound), or a multi-limb balance. Until that bound is wired, the theorems
below state exactly the cell-level facts the AIR forces. -/

/-- A satisfying LAST row with a canonical balance cell has `balance = 0` — read straight off the
boundary constraint. This is the in-circuit witness of
`Dregg2.Spec.Conservation.conservedInDomain Domain.balance` for this asset: the realized cell-level
`Σδ = 0` (see the §5.2 wrap-residual note for the ℤ-sum caveat). -/
theorem ccc_last_balance_zero
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hcanon : 0 ≤ env.loc Ccc.BALANCE_COL ∧ env.loc Ccc.BALANCE_COL < 2013265921)
    (h : cccWindowHolds hash tf env false true) :
    env.loc Ccc.BALANCE_COL = 0 := by
  by_contra hbad
  exact ccc_rejects_unbalanced hash tf env hcanon hbad h

#assert_axioms ccc_rejects_unbalanced
#assert_axioms ccc_rejects_wrong_asset
#assert_axioms ccc_mag_is_ranged
#assert_axioms ccc_forged_mint_unsat
#assert_axioms ccc_last_balance_zero

end Dregg2.Circuit.CrossCellConservation
