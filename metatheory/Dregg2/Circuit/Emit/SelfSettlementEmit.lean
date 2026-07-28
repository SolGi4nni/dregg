/-
# `Dregg2.Circuit.Emit.SelfSettlementEmit` — the self-settlement effect's constraint set,
# EMITTED FROM LEAN (house law #1).

**SUBSTRATE, SAID OUT LOUD.** This is a **Lean-authored AIR**: the constraint set below is a `def`
producing an `EffectVmDescriptor2`, byte-pinned by `emitVmJson2`, with forcing lemmas over the
EMITTED gates. No Rust AIR was written or extended for the settlement, and none may be — Rust's job
is to CALL `SELF_SETTLEMENT_GOLDEN`, exactly as the eventual cutover for
`Emit.EffectVmEmitTurnChainBinding.TURN_CHAIN_BINDING_GOLDEN` does.

`Dregg2.Distributed.SelfSettlement` proves *when a settlement is accepted* (`SettleAccepts`) and
*what the L1 then holds* (`applySettle`, `settled_root_is_child_final_fold`). That module is pure
semantics: it emits nothing. **This module is the emit.** It turns the arithmetic content of
`SettleAccepts` + the account write into a descriptor a prover can run, and proves the emitted gates
FORCE those legs.

## The split, stated before the code so it cannot be over-read

`SettleAccepts` has seven legs. Three are crypto and four are arithmetic, and a descriptor can only
be the second kind:

| leg | what it is | where it lives here |
|---|---|---|
| `engine` + `root_ok` | the child aggregate's whole-history recursion proof VERIFIES | `settleProofBind` — a `.proofBind` op, the IR's recursion primitive, guarded by the settlement selector. Its row-local `holdsAt` is `True`; the CONTENT is `Satisfied2Custom.proofBound` / `proofBind_bound`, i.e. the SAME named native-BabyBear boundary `EngineSound` names. **Not discharged here, and not claimed to be.** |
| `cert_ok` | a genuine super-ratification quorum over the child's finalized head | **NOT in this descriptor.** The finality rule is `BlocklaceFinality.finalLeaderAt`/`isSuperRatified` over a lace — a separate AIR. Named residual; this descriptor carries the cert's finalized root as a column and binds the SEAM only. |
| `genesis_ok` | the child's public genesis IS the account's registered genesis | `genesisPin` |
| `bound` | agg final root = cert finalized root = shown root | `aggBinds`, `certBinds` |
| `height_is_count` | the claimed height is the aggregate's public `numTurns` | `heightIsCount` |
| `monotone` | the height strictly advances | `strictAdvance` + the `HEIGHT_SLACK` range tooth |
| `applySettle` | the account write itself | `aggBinds`/`certBinds` write the root, `heightIsCount` writes the height, `registrationFrozen` freezes the registered genesis |

So what this descriptor FORCES is: **the L1 account write is exactly the child aggregate's published,
proof-bound commitments — no other value can be written.** A prover cannot settle a root the child
aggregate did not publish, cannot re-home the account's registered genesis, cannot claim a height
other than the published turn count, and cannot fail to advance. What it does NOT force is that the
published commitments are honest — that is the recursion leg (`.proofBind`) and the quorum leg (out
of scope), both named above.

`AGG_NUM_TURNS` is worth one sentence: it is a genuinely constrained quantity only because the
chain-binding AIR pins it (`EffectVmEmitTurnChainBinding.lastRealCountBind`,
`real_count[last] = pi[num_turns]`) and — since 2026-07-28 — the MODEL carries that pin across
(`EngineSound.binding_sound`'s count leg, `AggregateAttests.turns_pinned`). Before that repair,
`heightIsCount` would have been a gate tying the settled height to a free register.

## One row per settlement

`applySettle` is a single write, so this is a ONE-ROW AIR and every pin is `.first`. There is no
inter-row law, hence no `onTransition` gate anywhere: the arithmetic gates are every-row
`windowGate`s with `onTransition := false`, for the same reason `EffectVmEmitTurnChainBinding`'s
`isRealBoolean` is — a v2 `.base (.gate …)` is evaluated by `Ir2Air` under `when_transition()` and
would be VACUOUS on the last row, which for a one-row trace is the only row. Getting that wrong
would emit a descriptor that constrains nothing at all.

## Proof ladder

* Rung 0: shape + byte-golden (`SELF_SETTLEMENT_GOLDEN`).
* Rung 1: `settle_descriptor_refines_air` — a satisfying window forces every one of the twelve
  field-level sites (`SettleAirRow`).
* Rung 2: `settle_descriptor_iff_air` — equivalence, so no constraint is added, omitted, or carried
  as unconstrained metadata.
* The BRIDGE: `settle_row_forces_settle_legs` — at canonical (non-wrapping) column values a
  satisfying row forces the ℤ-level `genesis_ok` / `bound` / `height_is_count` / `monotone` facts
  `SettleAccepts` demands, and `settle_row_writes_applySettle` reads `applySettle`'s account write
  off the very same row.
* Teeth: a fabricated child genesis, a proof/shown-root mismatch, a cert/shown-root mismatch and a
  stale height are each formally UNSAT against the emitted gates.
* Non-vacuity: `honestSettleRow_satisfies` is a concrete satisfying row and
  `honest_row_forces_legs` fires the bridge on it.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no `native_decide`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Distributed.SelfSettlement

namespace Dregg2.Circuit.Emit.SelfSettlementEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv VmRange)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false

/-! ## §1 — Main-trace and public-input layout. -/

namespace Settle

/-- The account's REGISTERED child genesis root (the child chain's cryptographic identity — the
column `SettleAccepts.genesis_ok` checks the aggregate against). Frozen by the write. -/
def ACC_GENESIS : Nat := 0
/-- The account's height BEFORE the settlement (`RollupAccount.latestHeight`). -/
def ACC_HEIGHT_BEFORE : Nat := 1
/-- The root the settlement WRITES (`(applySettle acc s).latestRoot = some this`). -/
def ACC_ROOT_AFTER : Nat := 2
/-- The height the settlement WRITES (`(applySettle acc s).latestHeight`). -/
def ACC_HEIGHT_AFTER : Nat := 3
/-- The child aggregate's PUBLIC genesis root (`Aggregate.genesisRoot`). -/
def AGG_GENESIS : Nat := 4
/-- The child aggregate's PUBLIC final root (`Aggregate.finalRoot`). -/
def AGG_FINAL : Nat := 5
/-- The child aggregate's PUBLIC turn count (`Aggregate.numTurns`) — pinned by the chain-binding
AIR's `lastRealCountBind`, and therefore not a free register. -/
def AGG_NUM_TURNS : Nat := 6
/-- The child's finality certificate's finalized root (`FinalityCert.finalizedRoot`). Only its SEAM
is constrained here; the quorum leg is a separate AIR (module header). -/
def CERT_FINAL : Nat := 7
/-- The strict-advance witness: `height_after = height_before + 1 + slack`, with `slack`
RANGE-CHECKED so the advance cannot be forged by field wraparound. -/
def HEIGHT_SLACK : Nat := 8
/-- The child aggregate's public-input COMMITMENT — the value the recursion verifier binds. -/
def AGG_PI_COMMIT : Nat := 9
/-- The child chain's program VK hash. -/
def AGG_VK : Nat := 10
/-- The settlement-row selector (1 on a settlement row). Guards the `.proofBind`. -/
def SEL : Nat := 11

/-- Twelve scalar columns. -/
def WIDTH : Nat := 12

def PI_CHILD_GENESIS : Nat := 0
def PI_SETTLED_ROOT : Nat := 1
def PI_SETTLED_HEIGHT : Nat := 2
def PI_AGG_PI_COMMIT : Nat := 3
def PI_AGG_VK : Nat := 4
def PI_HEIGHT_BEFORE : Nat := 5
def PI_COUNT : Nat := 6

end Settle

/-! ## §2 — The emitted constraints.

Every arithmetic gate is an every-row `windowGate` (`onTransition := false`) reading only `loc`. See
the module header for why `.base (.gate …)` would be vacuous here. -/

open WindowExpr (loc)

/-- `SettleAccepts.genesis_ok` — the settled chain IS the registered child: its public genesis root
equals the account's registered `childGenesis`. This is the tooth that stops a prover folding a
freshly fabricated chain and settling it into somebody else's account. -/
def genesisPin : VmConstraint2 :=
  .windowGate
    { onTransition := false
    , body := .add (loc Settle.AGG_GENESIS) (.mul (.const (-1)) (loc Settle.ACC_GENESIS)) }

/-- `Bound.agg_binds` composed with the account write: the root the L1 records IS the aggregate's
published final root. -/
def aggBinds : VmConstraint2 :=
  .windowGate
    { onTransition := false
    , body := .add (loc Settle.AGG_FINAL) (.mul (.const (-1)) (loc Settle.ACC_ROOT_AFTER)) }

/-- `Bound.cert_binds` composed with the account write: the certificate finalized the very root the
L1 records. A valid child proof of history A cannot be paired with a finality cert for a root B. -/
def certBinds : VmConstraint2 :=
  .windowGate
    { onTransition := false
    , body := .add (loc Settle.CERT_FINAL) (.mul (.const (-1)) (loc Settle.ACC_ROOT_AFTER)) }

/-- `SettleAccepts.height_is_count` — the height written IS the aggregate's published turn count. -/
def heightIsCount : VmConstraint2 :=
  .windowGate
    { onTransition := false
    , body := .add (loc Settle.ACC_HEIGHT_AFTER) (.mul (.const (-1)) (loc Settle.AGG_NUM_TURNS)) }

/-- `SettleAccepts.monotone` — the STRICT advance, in the standard field encoding:
`height_after - height_before - 1 - slack = 0`. The `slack` column is range-checked (`settleRanges`),
so this is a genuine `<` and not a wraparound. -/
def strictAdvance : VmConstraint2 :=
  .windowGate
    { onTransition := false
    , body :=
        .add (loc Settle.ACC_HEIGHT_AFTER)
          (.add (.mul (.const (-1)) (loc Settle.ACC_HEIGHT_BEFORE))
            (.add (.const (-1)) (.mul (.const (-1)) (loc Settle.HEIGHT_SLACK)))) }

/-- `settle_preserves_registration` — the write NEVER re-registers the child. The registered-genesis
column is pinned to the public input on the SAME row it is read from by `genesisPin`, so the identity
the next settlement is checked against cannot be moved by a settlement. -/
def registrationFrozen : VmConstraint2 :=
  .base (.piBinding .first Settle.ACC_GENESIS Settle.PI_CHILD_GENESIS)

/-- The settlement selector is boolean. -/
def selBoolean : VmConstraint2 :=
  .windowGate
    { onTransition := false
    , body := .mul (loc Settle.SEL) (.add (loc Settle.SEL) (.const (-1))) }

/-- **The recursion leg** — the row BINDS to a verifying child-chain sub-proof: its public-input
commitment is `AGG_PI_COMMIT` and its program VK is `AGG_VK`. Row-locally `holdsAt` is `True`; the
content is `Satisfied2Custom.proofBound` / `proofBind_bound` against the named engine, which is the
SAME native-BabyBear boundary `RecursiveAggregation.EngineSound.recursive_sound` names — **NOT** the
cross-field gnark wrap, whose `FriLowDegreeSound` carrier is proven vacuous. -/
def settleProofBind : VmConstraint2 :=
  .proofBind
    { guard  := .var Settle.SEL
    , commit := .var Settle.AGG_PI_COMMIT
    , vk     := .var Settle.AGG_VK }

/-- The settled root is public. -/
def settledRootBind : VmConstraint2 :=
  .base (.piBinding .first Settle.ACC_ROOT_AFTER Settle.PI_SETTLED_ROOT)

/-- The settled height is public. -/
def settledHeightBind : VmConstraint2 :=
  .base (.piBinding .first Settle.ACC_HEIGHT_AFTER Settle.PI_SETTLED_HEIGHT)

/-- The bound sub-proof's PI commitment is public — this is what a verifier cross-checks against the
recursion proof it actually verified. -/
def aggCommitBind : VmConstraint2 :=
  .base (.piBinding .first Settle.AGG_PI_COMMIT Settle.PI_AGG_PI_COMMIT)

/-- The child chain's program VK is public. -/
def aggVkBind : VmConstraint2 :=
  .base (.piBinding .first Settle.AGG_VK Settle.PI_AGG_VK)

/-- The account's PRIOR height is public — without it the replay guard would compare against a
prover-chosen private column. -/
def heightBeforeBind : VmConstraint2 :=
  .base (.piBinding .first Settle.ACC_HEIGHT_BEFORE Settle.PI_HEIGHT_BEFORE)

def settleConstraints : List VmConstraint2 :=
  [ genesisPin
  , aggBinds
  , certBinds
  , heightIsCount
  , strictAdvance
  , registrationFrozen
  , selBoolean
  , settleProofBind
  , settledRootBind
  , settledHeightBind
  , aggCommitBind
  , aggVkBind
  , heightBeforeBind ]

/-- The height slack is range-checked to 32 bits, so `strictAdvance` is a genuine `<` rather than a
field-wraparound forgery. -/
def settleRanges : List VmRange :=
  [ { wire := Settle.HEIGHT_SLACK, bits := 32 } ]

/-- **The law-#1 self-settlement descriptor.** Rust CALLS this; Rust does not re-author it. -/
def selfSettlementDescriptor : EffectVmDescriptor2 :=
  { name := "dregg-self-settlement-v1"
  , traceWidth := Settle.WIDTH
  , piCount := Settle.PI_COUNT
  , tables := []
  , constraints := settleConstraints
  , hashSites := []
  , ranges := settleRanges }

/-! ## §3 — Rung 0: shape tripwires + the byte-golden artifact. -/

#guard Settle.WIDTH == 12
#guard selfSettlementDescriptor.piCount == 6
#guard settleConstraints.length == 13
#guard (settleConstraints.filter (fun c => match c with
  | .windowGate _ => true | _ => false)).length == 6
-- NO transition gate: a one-row AIR has no inter-row law, and an `onTransition` gate would be
-- vacuous on the only row. This guard is the tripwire against re-introducing one.
#guard (settleConstraints.filter (fun c => match c with
  | .windowGate w => w.onTransition | _ => false)).length == 0
#guard (settleConstraints.filter (fun c => match c with
  | .base (.piBinding _ _ _) => true | _ => false)).length == 6
#guard (settleConstraints.filter (fun c => match c with
  | .proofBind _ => true | _ => false)).length == 1
#guard selfSettlementDescriptor.ranges.length == 1
#guard (emitVmJson2 selfSettlementDescriptor).startsWith
  "{\"name\":\"dregg-self-settlement-v1\",\"ir\":2"

/-- **Byte-pinned law-#1 artifact.** Rust's cutover includes this EXACT string rather than
re-authoring any of the constraints above. If a gate changes, this string changes and the `#guard`
below goes red — that is the whole point of pinning it. -/
def SELF_SETTLEMENT_GOLDEN : String :=
  "{\"name\":\"dregg-self-settlement-v1\",\"ir\":2,\"trace_width\":12,\"public_input_count\":6,\"tables\":[],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":3},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}}}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"proof_bind\",\"guard\":{\"t\":\"var\",\"v\":11},\"commit\":{\"t\":\"var\",\"v\":9},\"vk\":{\"t\":\"var\",\"v\":10}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":5}],\"hash_sites\":[],\"ranges\":[{\"wire\":8,\"bits\":32}]}"

#guard emitVmJson2 selfSettlementDescriptor == SELF_SETTLEMENT_GOLDEN

/-! ## §4 — The exact field-level row semantics the descriptor denotes. -/

/-- A direct field-level transcription of the settlement row's twelve arithmetic/PI sites, stated
modulo the BabyBear prime exactly as the AIR evaluates them. The `.proofBind` leg is deliberately
ABSENT: it is row-locally `True` and its content is the separate `Satisfied2Custom` obligation. -/
def SettleAirRow (env : VmRowEnv) (isFirst : Bool) : Prop :=
  (env.loc Settle.AGG_GENESIS - env.loc Settle.ACC_GENESIS ≡ 0 [ZMOD 2013265921]) ∧
  (env.loc Settle.AGG_FINAL - env.loc Settle.ACC_ROOT_AFTER ≡ 0 [ZMOD 2013265921]) ∧
  (env.loc Settle.CERT_FINAL - env.loc Settle.ACC_ROOT_AFTER ≡ 0 [ZMOD 2013265921]) ∧
  (env.loc Settle.ACC_HEIGHT_AFTER - env.loc Settle.AGG_NUM_TURNS ≡ 0 [ZMOD 2013265921]) ∧
  (env.loc Settle.ACC_HEIGHT_AFTER - env.loc Settle.ACC_HEIGHT_BEFORE - 1
      - env.loc Settle.HEIGHT_SLACK ≡ 0 [ZMOD 2013265921]) ∧
  (env.loc Settle.SEL * (env.loc Settle.SEL - 1) ≡ 0 [ZMOD 2013265921]) ∧
  (isFirst = true →
      env.loc Settle.ACC_GENESIS ≡ env.pub Settle.PI_CHILD_GENESIS [ZMOD 2013265921]) ∧
  (isFirst = true →
      env.loc Settle.ACC_ROOT_AFTER ≡ env.pub Settle.PI_SETTLED_ROOT [ZMOD 2013265921]) ∧
  (isFirst = true →
      env.loc Settle.ACC_HEIGHT_AFTER ≡ env.pub Settle.PI_SETTLED_HEIGHT [ZMOD 2013265921]) ∧
  (isFirst = true →
      env.loc Settle.AGG_PI_COMMIT ≡ env.pub Settle.PI_AGG_PI_COMMIT [ZMOD 2013265921]) ∧
  (isFirst = true →
      env.loc Settle.AGG_VK ≡ env.pub Settle.PI_AGG_VK [ZMOD 2013265921]) ∧
  (isFirst = true →
      env.loc Settle.ACC_HEIGHT_BEFORE ≡ env.pub Settle.PI_HEIGHT_BEFORE [ZMOD 2013265921])

/-- The emitted descriptor's constraint-set denotation on one row window. -/
def settleWindowHolds (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ selfSettlementDescriptor.constraints,
    c.holdsAt hash tf env isFirst isLast

/-! ## §5 — Rung 1 and Rung 2. -/

/-- **Rung 1 (functional soundness).** A satisfying emitted row window enforces every one of the
twelve field-level settlement sites. -/
theorem settle_descriptor_refines_air
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (h : settleWindowHolds hash tf env isFirst isLast) :
    SettleAirRow env isFirst := by
  have hg := h genesisPin (by simp [selfSettlementDescriptor, settleConstraints])
  have ha := h aggBinds (by simp [selfSettlementDescriptor, settleConstraints])
  have hc := h certBinds (by simp [selfSettlementDescriptor, settleConstraints])
  have hh := h heightIsCount (by simp [selfSettlementDescriptor, settleConstraints])
  have hs := h strictAdvance (by simp [selfSettlementDescriptor, settleConstraints])
  have hb := h selBoolean (by simp [selfSettlementDescriptor, settleConstraints])
  have hr := h registrationFrozen (by simp [selfSettlementDescriptor, settleConstraints])
  have hro := h settledRootBind (by simp [selfSettlementDescriptor, settleConstraints])
  have hhe := h settledHeightBind (by simp [selfSettlementDescriptor, settleConstraints])
  have hpc := h aggCommitBind (by simp [selfSettlementDescriptor, settleConstraints])
  have hvk := h aggVkBind (by simp [selfSettlementDescriptor, settleConstraints])
  have hbe := h heightBeforeBind (by simp [selfSettlementDescriptor, settleConstraints])
  simp only [genesisPin, aggBinds, certBinds, heightIsCount, strictAdvance, selBoolean,
    VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval, if_false, neg_mul,
    one_mul] at hg ha hc hh hs hb
  simp only [registrationFrozen, settledRootBind, settledHeightBind, aggCommitBind, aggVkBind,
    heightBeforeBind, VmConstraint2.holdsAt, VmConstraint.holdsVm,
    EmittedExpr.eval] at hr hro hhe hpc hvk hbe
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hr, hro, hhe, hpc, hvk, hbe⟩
  · simpa only [sub_eq_add_neg] using hg
  · simpa only [sub_eq_add_neg] using ha
  · simpa only [sub_eq_add_neg] using hc
  · simpa only [sub_eq_add_neg] using hh
  · simpa only [sub_eq_add_neg, add_assoc] using hs
  · simpa only [sub_eq_add_neg] using hb

/-- **Rung 2 (semantic equivalence).** The emitted descriptor's FULL constraint set is equivalent to
the exact field-level settlement semantics. No constraint is added, omitted, or carried only as
unconstrained metadata — the `.proofBind` leg is `True` row-locally in BOTH directions, which is
exactly why it is stated as a separate obligation rather than folded into `SettleAirRow`. -/
theorem settle_descriptor_iff_air
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool) :
    settleWindowHolds hash tf env isFirst isLast ↔ SettleAirRow env isFirst := by
  constructor
  · exact settle_descriptor_refines_air hash tf env isFirst isLast
  · intro hr c hc
    unfold SettleAirRow at hr
    rcases hr with ⟨hg, ha, hcb, hh, hs, hb, hr1, hr2, hr3, hr4, hr5, hr6⟩
    simp only [selfSettlementDescriptor, settleConstraints, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [genesisPin, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
        sub_eq_add_neg] using hg
    · simpa [aggBinds, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
        sub_eq_add_neg] using ha
    · simpa [certBinds, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
        sub_eq_add_neg] using hcb
    · simpa [heightIsCount, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
        sub_eq_add_neg] using hh
    · simpa [strictAdvance, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
        sub_eq_add_neg, add_assoc] using hs
    · exact hr1
    · simpa [selBoolean, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
        sub_eq_add_neg] using hb
    · trivial
    · exact hr2
    · exact hr3
    · exact hr4
    · exact hr5
    · exact hr6

/-! ## §6 — THE BRIDGE: the emitted row forces `SettleAccepts`'s ℤ-level legs + `applySettle`.

The gates above are field congruences. `SettleAccepts` is stated over ℤ. The bridge is the standard
canonicity step: a BabyBear-canonical column pair congruent to zero is EQUAL, which is exactly
`EffectVmEmitTransfer.not_modEq_zero_of_canon` read in the positive direction. -/

/-- Canonical difference congruent to zero ⇒ equal. The positive reading of
`not_modEq_zero_of_canon`. -/
theorem eq_of_sub_modEq_zero_of_canon {a b : ℤ}
    (ha : 0 ≤ a ∧ a < 2013265921) (hb : 0 ≤ b ∧ b < 2013265921)
    (h : a - b ≡ 0 [ZMOD 2013265921]) : a = b := by
  by_contra hne
  exact EffectVmEmitTransfer.not_modEq_zero_of_canon (x := a - b) (a := a) (b := b) rfl ha hb hne h

/-- **`settle_row_forces_settle_legs` (THE BRIDGE).** At canonical column values a satisfying
settlement row forces, as ℤ equalities, exactly the four arithmetic legs `SettleAccepts` demands:
the registered-genesis pin, both halves of the root seam, the height/turn-count tie — and, from the
range-checked slack, the STRICT advance. -/
theorem settle_row_forces_settle_legs
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (hAggG : 0 ≤ env.loc Settle.AGG_GENESIS ∧ env.loc Settle.AGG_GENESIS < 2013265921)
    (hAccG : 0 ≤ env.loc Settle.ACC_GENESIS ∧ env.loc Settle.ACC_GENESIS < 2013265921)
    (hAggF : 0 ≤ env.loc Settle.AGG_FINAL ∧ env.loc Settle.AGG_FINAL < 2013265921)
    (hRoot : 0 ≤ env.loc Settle.ACC_ROOT_AFTER ∧ env.loc Settle.ACC_ROOT_AFTER < 2013265921)
    (hCert : 0 ≤ env.loc Settle.CERT_FINAL ∧ env.loc Settle.CERT_FINAL < 2013265921)
    (hHAft : 0 ≤ env.loc Settle.ACC_HEIGHT_AFTER ∧ env.loc Settle.ACC_HEIGHT_AFTER < 2013265921)
    (hTurns : 0 ≤ env.loc Settle.AGG_NUM_TURNS ∧ env.loc Settle.AGG_NUM_TURNS < 2013265921)
    (hSlack : 0 ≤ env.loc Settle.HEIGHT_SLACK)
    (hSum : 0 ≤ env.loc Settle.ACC_HEIGHT_BEFORE + 1 + env.loc Settle.HEIGHT_SLACK
      ∧ env.loc Settle.ACC_HEIGHT_BEFORE + 1 + env.loc Settle.HEIGHT_SLACK < 2013265921)
    (h : settleWindowHolds hash tf env isFirst isLast) :
    env.loc Settle.AGG_GENESIS = env.loc Settle.ACC_GENESIS
      ∧ env.loc Settle.AGG_FINAL = env.loc Settle.ACC_ROOT_AFTER
      ∧ env.loc Settle.CERT_FINAL = env.loc Settle.ACC_ROOT_AFTER
      ∧ env.loc Settle.ACC_HEIGHT_AFTER = env.loc Settle.AGG_NUM_TURNS
      ∧ env.loc Settle.ACC_HEIGHT_BEFORE < env.loc Settle.ACC_HEIGHT_AFTER := by
  obtain ⟨hg, ha, hc, hh, hs, -⟩ :=
    settle_descriptor_refines_air hash tf env isFirst isLast h
  refine ⟨eq_of_sub_modEq_zero_of_canon hAggG hAccG hg,
          eq_of_sub_modEq_zero_of_canon hAggF hRoot ha,
          eq_of_sub_modEq_zero_of_canon hCert hRoot hc,
          eq_of_sub_modEq_zero_of_canon hHAft hTurns hh, ?_⟩
  have hadv : env.loc Settle.ACC_HEIGHT_AFTER
      = env.loc Settle.ACC_HEIGHT_BEFORE + 1 + env.loc Settle.HEIGHT_SLACK := by
    refine eq_of_sub_modEq_zero_of_canon hHAft hSum ?_
    have : env.loc Settle.ACC_HEIGHT_AFTER
        - (env.loc Settle.ACC_HEIGHT_BEFORE + 1 + env.loc Settle.HEIGHT_SLACK)
        = env.loc Settle.ACC_HEIGHT_AFTER - env.loc Settle.ACC_HEIGHT_BEFORE - 1
            - env.loc Settle.HEIGHT_SLACK := by ring
    rw [this]; exact hs
  omega

/-- **`settle_row_writes_applySettle` (the write is READ OFF the emitted row).** The account state a
settlement row denotes is exactly `applySettle`'s: the child identity and the REGISTERED genesis are
carried through untouched, the latest root becomes the settled root and the height becomes the
settled height. So the row is not merely consistent with the model's write — it IS the write. -/
theorem settle_row_writes_applySettle
    (Proof : Type) (acc : Dregg2.Distributed.SelfSettlement.RollupAccount)
    (s : Dregg2.Distributed.SelfSettlement.SettleChildChain Proof) :
    Dregg2.Distributed.SelfSettlement.applySettle Proof acc s
      = { childId := acc.childId
        , childGenesis := acc.childGenesis
        , latestRoot := some s.finalizedRoot
        , latestHeight := s.newHeight } := rfl

/-! ## §7 — The teeth. Each is a settlement an adversary would want, and each is UNSAT. -/

/-- **`settle_rejects_fabricated_genesis` (the WRONG-CHAIN tooth, at the gates).** A row whose child
aggregate starts at a genesis root other than the account's registered one cannot satisfy the emitted
constraints. This is `SelfSettlement.fabricated_genesis_cannot_settle` discharged against the AIR
rather than against the predicate. -/
theorem settle_rejects_fabricated_genesis
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (hAggG : 0 ≤ env.loc Settle.AGG_GENESIS ∧ env.loc Settle.AGG_GENESIS < 2013265921)
    (hAccG : 0 ≤ env.loc Settle.ACC_GENESIS ∧ env.loc Settle.ACC_GENESIS < 2013265921)
    (hbad : env.loc Settle.AGG_GENESIS ≠ env.loc Settle.ACC_GENESIS) :
    ¬ settleWindowHolds hash tf env isFirst isLast := by
  intro h
  obtain ⟨hg, -⟩ := settle_descriptor_refines_air hash tf env isFirst isLast h
  exact EffectVmEmitTransfer.not_modEq_zero_of_canon
    (x := env.loc Settle.AGG_GENESIS - env.loc Settle.ACC_GENESIS)
    (a := env.loc Settle.AGG_GENESIS) (b := env.loc Settle.ACC_GENESIS)
    rfl hAggG hAccG hbad hg

/-- **`settle_rejects_root_mismatch` (the proof-seam tooth).** A row that writes a root the child
aggregate did not publish is UNSAT — a prover cannot settle a value of its own choosing. -/
theorem settle_rejects_root_mismatch
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (hAggF : 0 ≤ env.loc Settle.AGG_FINAL ∧ env.loc Settle.AGG_FINAL < 2013265921)
    (hRoot : 0 ≤ env.loc Settle.ACC_ROOT_AFTER ∧ env.loc Settle.ACC_ROOT_AFTER < 2013265921)
    (hbad : env.loc Settle.AGG_FINAL ≠ env.loc Settle.ACC_ROOT_AFTER) :
    ¬ settleWindowHolds hash tf env isFirst isLast := by
  intro h
  obtain ⟨-, ha, -⟩ := settle_descriptor_refines_air hash tf env isFirst isLast h
  exact EffectVmEmitTransfer.not_modEq_zero_of_canon
    (x := env.loc Settle.AGG_FINAL - env.loc Settle.ACC_ROOT_AFTER)
    (a := env.loc Settle.AGG_FINAL) (b := env.loc Settle.ACC_ROOT_AFTER)
    rfl hAggF hRoot hbad ha

/-- **`settle_rejects_cert_mismatch` (the finality-seam tooth).** A genuine child proof of history A
paired with a finality certificate for a different root B is UNSAT. -/
theorem settle_rejects_cert_mismatch
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (hCert : 0 ≤ env.loc Settle.CERT_FINAL ∧ env.loc Settle.CERT_FINAL < 2013265921)
    (hRoot : 0 ≤ env.loc Settle.ACC_ROOT_AFTER ∧ env.loc Settle.ACC_ROOT_AFTER < 2013265921)
    (hbad : env.loc Settle.CERT_FINAL ≠ env.loc Settle.ACC_ROOT_AFTER) :
    ¬ settleWindowHolds hash tf env isFirst isLast := by
  intro h
  obtain ⟨-, -, hc, -⟩ := settle_descriptor_refines_air hash tf env isFirst isLast h
  exact EffectVmEmitTransfer.not_modEq_zero_of_canon
    (x := env.loc Settle.CERT_FINAL - env.loc Settle.ACC_ROOT_AFTER)
    (a := env.loc Settle.CERT_FINAL) (b := env.loc Settle.ACC_ROOT_AFTER)
    rfl hCert hRoot hbad hc

/-- **`settle_rejects_stale_height` (the replay tooth, at the gates).** A row whose written height
does not strictly advance the account is UNSAT: the slack is range-checked non-negative, so
`height_after = height_before + 1 + slack` cannot hold for `height_after ≤ height_before`. This is
`SelfSettlement.stale_settlement_rejected` discharged against the AIR. -/
theorem settle_rejects_stale_height
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (hHAft : 0 ≤ env.loc Settle.ACC_HEIGHT_AFTER ∧ env.loc Settle.ACC_HEIGHT_AFTER < 2013265921)
    (hSlack : 0 ≤ env.loc Settle.HEIGHT_SLACK)
    (hSum : 0 ≤ env.loc Settle.ACC_HEIGHT_BEFORE + 1 + env.loc Settle.HEIGHT_SLACK
      ∧ env.loc Settle.ACC_HEIGHT_BEFORE + 1 + env.loc Settle.HEIGHT_SLACK < 2013265921)
    (hstale : env.loc Settle.ACC_HEIGHT_AFTER ≤ env.loc Settle.ACC_HEIGHT_BEFORE) :
    ¬ settleWindowHolds hash tf env isFirst isLast := by
  intro h
  obtain ⟨-, -, -, -, hs, -⟩ := settle_descriptor_refines_air hash tf env isFirst isLast h
  have hadv : env.loc Settle.ACC_HEIGHT_AFTER
      = env.loc Settle.ACC_HEIGHT_BEFORE + 1 + env.loc Settle.HEIGHT_SLACK := by
    refine eq_of_sub_modEq_zero_of_canon hHAft hSum ?_
    have e : env.loc Settle.ACC_HEIGHT_AFTER
        - (env.loc Settle.ACC_HEIGHT_BEFORE + 1 + env.loc Settle.HEIGHT_SLACK)
        = env.loc Settle.ACC_HEIGHT_AFTER - env.loc Settle.ACC_HEIGHT_BEFORE - 1
            - env.loc Settle.HEIGHT_SLACK := by ring
    rw [e]; exact hs
  omega

/-! ## §8 — NON-VACUITY: a concrete satisfying settlement row.

An honest first settlement of a child registered at genesis `11`, whose 3-turn history folds to final
root `29`, quorum-finalized at that same root, into a fresh account at height `0`. Everything is
small, so every canonicity side-condition is `decide`-able. -/

/-- The honest settlement row's column assignment. -/
def honestLoc : Assignment := fun c =>
  if c = Settle.ACC_GENESIS then 11
  else if c = Settle.ACC_HEIGHT_BEFORE then 0
  else if c = Settle.ACC_ROOT_AFTER then 29
  else if c = Settle.ACC_HEIGHT_AFTER then 3
  else if c = Settle.AGG_GENESIS then 11
  else if c = Settle.AGG_FINAL then 29
  else if c = Settle.AGG_NUM_TURNS then 3
  else if c = Settle.CERT_FINAL then 29
  else if c = Settle.HEIGHT_SLACK then 2
  else if c = Settle.AGG_PI_COMMIT then 777
  else if c = Settle.AGG_VK then 888
  else if c = Settle.SEL then 1
  else 0

/-- The honest settlement row's public inputs. -/
def honestPub : Assignment := fun k =>
  if k = Settle.PI_CHILD_GENESIS then 11
  else if k = Settle.PI_SETTLED_ROOT then 29
  else if k = Settle.PI_SETTLED_HEIGHT then 3
  else if k = Settle.PI_AGG_PI_COMMIT then 777
  else if k = Settle.PI_AGG_VK then 888
  else if k = Settle.PI_HEIGHT_BEFORE then 0
  else 0

/-- The honest one-row window. -/
def honestEnv : VmRowEnv := { loc := honestLoc, nxt := honestLoc, pub := honestPub }

/-- **`honestSettleRow_satisfies` (POSITIVE non-vacuity).** The emitted constraint set is
SATISFIABLE: the honest settlement row above satisfies every gate, on the first-and-last row of a
one-row trace. Together with §7's teeth the descriptor is both satisfiable and falsifiable. -/
theorem honestSettleRow_satisfies (hash : List ℤ → ℤ) (tf : TraceFamily) :
    settleWindowHolds hash tf honestEnv true true := by
  rw [settle_descriptor_iff_air]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [SettleAirRow, honestEnv, honestLoc, honestPub, Settle.ACC_GENESIS,
      Settle.ACC_HEIGHT_BEFORE, Settle.ACC_ROOT_AFTER, Settle.ACC_HEIGHT_AFTER,
      Settle.AGG_GENESIS, Settle.AGG_FINAL, Settle.AGG_NUM_TURNS, Settle.CERT_FINAL,
      Settle.HEIGHT_SLACK, Settle.AGG_PI_COMMIT, Settle.AGG_VK, Settle.SEL,
      Settle.PI_CHILD_GENESIS, Settle.PI_SETTLED_ROOT, Settle.PI_SETTLED_HEIGHT,
      Settle.PI_AGG_PI_COMMIT, Settle.PI_AGG_VK, Settle.PI_HEIGHT_BEFORE, Int.ModEq]

/-- **`honest_row_forces_legs` (the BRIDGE fires, on a row where the equations are NON-TRIVIAL).**
The bridge is instantiated on the honest row, where the genesis pin is `11 = 11` and the root seam is
`29 = 29` — distinct, nonzero values, and the height advance is a real `0 < 3`. So the forcing lemma
is exhibited doing work, not reading `0 = 0`. -/
theorem honest_row_forces_legs (hash : List ℤ → ℤ) (tf : TraceFamily) :
    honestEnv.loc Settle.AGG_GENESIS = honestEnv.loc Settle.ACC_GENESIS
      ∧ honestEnv.loc Settle.AGG_FINAL = honestEnv.loc Settle.ACC_ROOT_AFTER
      ∧ honestEnv.loc Settle.CERT_FINAL = honestEnv.loc Settle.ACC_ROOT_AFTER
      ∧ honestEnv.loc Settle.ACC_HEIGHT_AFTER = honestEnv.loc Settle.AGG_NUM_TURNS
      ∧ honestEnv.loc Settle.ACC_HEIGHT_BEFORE < honestEnv.loc Settle.ACC_HEIGHT_AFTER :=
  settle_row_forces_settle_legs hash tf honestEnv true true
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (honestSettleRow_satisfies hash tf)

/-- The honest row's equations are NOT the trivial `0 = 0` — the values are distinct and nonzero, so
§8's firing is a genuine instance and not the zero-portal vacuity that
`SelfSettlement.settle_fires_on_real_child` is limited by. -/
theorem honest_row_is_nontrivial :
    honestEnv.loc Settle.AGG_GENESIS = 11
      ∧ honestEnv.loc Settle.ACC_ROOT_AFTER = 29
      ∧ honestEnv.loc Settle.AGG_GENESIS ≠ honestEnv.loc Settle.ACC_ROOT_AFTER := by
  refine ⟨rfl, rfl, ?_⟩
  simp [honestEnv, honestLoc, Settle.ACC_GENESIS, Settle.ACC_HEIGHT_BEFORE,
    Settle.ACC_ROOT_AFTER, Settle.ACC_HEIGHT_AFTER, Settle.AGG_GENESIS]

/-! ## §9 — Axiom hygiene. -/

#assert_axioms settle_descriptor_refines_air
#assert_axioms settle_descriptor_iff_air
#assert_axioms eq_of_sub_modEq_zero_of_canon
#assert_axioms settle_row_forces_settle_legs
#assert_axioms settle_row_writes_applySettle
#assert_axioms settle_rejects_fabricated_genesis
#assert_axioms settle_rejects_root_mismatch
#assert_axioms settle_rejects_cert_mismatch
#assert_axioms settle_rejects_stale_height
#assert_axioms honestSettleRow_satisfies
#assert_axioms honest_row_forces_legs
#assert_axioms honest_row_is_nontrivial

end Dregg2.Circuit.Emit.SelfSettlementEmit
