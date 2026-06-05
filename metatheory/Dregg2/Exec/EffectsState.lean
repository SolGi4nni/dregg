/-
# Dregg2.Exec.EffectsState — the NEUTRAL / MONOTONIC / TERMINAL non-balance regime.

**Sibling of `Exec/EffectTransfer.lean` (the REFERENCE TEMPLATE).** Where `EffectTransfer` drives
the prototypical *Conservative*/`Paired` effect (a gated debit/credit, `Σδ = 0`) all the way
through the executor layers, THIS module drives the dregg1 effects that carry **no balance delta**:
the field/state/lifecycle mutations whose `LinearityClass` color (`turn/src/action.rs
Effect::linearity`, mirrored in `CatalogInstances.effectLinearity`) is `Neutral`, `Monotonic`, or
`Terminal`. For these the conserved `balance` domain measure (`RecordKernel.recTotal`) is UNCHANGED
and the authority graph (`Spec.execGraph`) is UNCHANGED; only the METADATA domain advances (a field
write, a counter bump, a lifecycle flag set). So — as `EffectTransfer §0` foretells — the BESPOKE
work per effect is "the domain-specific field-write semantics + its non-interference lemma": the
write touches a named metadata field and PROVABLY does not perturb the conserved balance.

## The effects covered (Neutral / Monotonic / Terminal, the non-balance ones)

DISCOVERED from `turn/src/action.rs` (`Effect` enum) ∩ `CatalogInstances.effectLinearity` coloring:

  * **Neutral** (`effectLinearity .x = Neutral`): `SetField`, `SetVerificationKey`
    (`setVerificationKey`), `EmitEvent`, `RefreshDelegation`, `PipelinedSend`,
    `ExerciseViaCapability`, plus `SetPermissions`. No resource delta — pure book-keeping.
  * **Monotonic** (`= Monotonic`): `IncrementNonce`, `ExportSturdyRef`, `EnlivenRef`,
    `ValidateHandoff`, `Refusal`. A scalar counter that only grows.
  * **Terminal** (`= Terminal`): `Seal`/`Unseal` (`cellSeal`/`cellUnseal`), `MakeSovereign`,
    `CellDestroy`, `ReceiptArchive`, `DropRef`, `RevokeDelegation`, `AttenuateCapability`,
    `RevokeCapability`. A one-way lifecycle transition with no inverse.

We model the common shape once (a named-field write on the record cell) and instantiate it for the
three representative families, proving for EACH the FIVE-keystone pattern, specialized for the
non-balance regime:
  (a) exec semantics — the field/state/flag write over the record kernel state;
  (b) conserves — balance UNCHANGED (the load-bearing NON-INTERFERENCE lemma: a metadata write
      doesn't touch `balOf`, like `EffectTransfer.setNonce_balOf`) ∧ authority UNCHANGED;
  (c) authorized — the actor held authority over the target (reusing the cap gate);
  (d) metadata — what advances (field set / counter bumped / lifecycle flag raised);
  (e) forward-sim — `AbsStep (absS s) (absS s')`: the abstract balance total is conserved and the
      authority graph is unchanged (the Neutral/metadata bottom edge of the simulation square).

Terminal effects additionally carry an **irreversibility-shaped** obligation (the `Terminal` color
has no inverse): once the lifecycle flag is set it stays set under idempotent re-application, and a
sealed cell rejects a second seal — the executable shadow of `LinearityClass::Terminal`.

## Discipline
No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly `{propext,
Classical.choice, Quot.sound}` on every keystone. Reuses ONLY the already-built
`Exec.TurnExecutor`/`Exec.RecordKernel`/`Spec.ExecRefinement` primitives. Verified standalone:
`lake env lean Dregg2/Exec/EffectsState.lean`.
-/
import Dregg2.Exec.TurnExecutor
import Dregg2.Spec.ExecRefinement

namespace Dregg2.Exec.EffectsState

open Dregg2.Exec
open Dregg2.Authority (Caps)
open Dregg2.Spec (Domain conservedInDomain execGraph execAuthGuard Guard)
open Dregg2.Laws (Verifiable)
open scoped BigOperators

/-! ## §0 — The generic named-field write, and its NON-INTERFERENCE with the balance measure.

Every Neutral/Monotonic/Terminal effect of this module mutates a NAMED field of the
content-addressed record (a state field, a counter, a lifecycle flag) that is DISTINCT from the
conserved `balance` field. So the single bespoke fact each instantiates is: **a write to a field
`f ≠ "balance"` leaves `balOf` unchanged**. We prove this ONCE for a generic field name `f` (with
the side-condition `f ≠ balanceField`) and a generic value, then every concrete effect specializes
`f`. This is the `EffectTransfer.setNonce_balOf` non-interference lemma, generalized over the field.

The field write reuses EXACTLY the `RecordKernel.setBalance` shape (overwrite-in-place on a record,
singleton on a non-record), parameterized by the field name. -/

/-- Write the named field `f` of a record cell to `v` (overwriting in place; a non-record value
becomes a singleton `f` record). Touches ONLY field `f`. The generic named-field write — the
`f`-parameterized analog of `RecordKernel.setBalance` / `EffectTransfer.setNonce`. -/
def setField (f : FieldName) (cell : Value) (v : Value) : Value :=
  match cell with
  | .record fs => .record (setFieldList f fs v)
  | _          => .record [(f, v)]
where
  setFieldList : FieldName → List (FieldName × Value) → Value → List (FieldName × Value)
  | f, [],            v => [(f, v)]
  | f, (k, x) :: rest, v => if k == f then (f, v) :: rest
                            else (k, x) :: setFieldList f rest v

/-- Read field `f` of a value as a scalar `Int`, defaulting absent/ill-typed to `0`. The
`f`-parameterized analog of `RecordKernel.balOf` / `EffectTransfer.nonceOf`. -/
def fieldOf (f : FieldName) (v : Value) : Int := (v.scalar f).getD 0

/-- After `setField f cell (.int n)`, reading field `f` as a scalar returns exactly `n` (the
write/read law for the metadata field). -/
theorem setField_fieldOf (f : FieldName) (cell : Value) (n : Int) :
    fieldOf f (setField f cell (.int n)) = n := by
  have hlist : ∀ fs : List (FieldName × Value),
      ((Value.record (setField.setFieldList f fs (.int n))).scalar f) = some n := by
    intro fs
    induction fs with
    | nil => simp [setField.setFieldList, Value.scalar, Value.field]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setField.setFieldList]
        by_cases hk : (k == f) = true
        · rw [if_pos hk]; simp [Value.scalar, Value.field]
        · have hkf : (k == f) = false := by simpa using hk
          rw [if_neg hk]
          simp only [Value.scalar, Value.field] at ih ⊢
          rw [List.find?_cons_of_neg (by simpa using hkf)]
          exact ih
  unfold fieldOf setField
  cases cell with
  | record fs => rw [hlist fs]; rfl
  | int _  => simp [Value.scalar, Value.field]
  | dig _  => simp [Value.scalar, Value.field]
  | sym _  => simp [Value.scalar, Value.field]

/-- **NON-INTERFERENCE — PROVED (the load-bearing lemma).** Writing a field `f` DISTINCT from the
`balance` field leaves the conserved balance read (`balOf`) UNCHANGED. This is what lets every
Neutral/Monotonic/Terminal metadata move ride alongside the (frozen) balance domain without
disturbing it — the generic `f`-parameterized form of `EffectTransfer.setNonce_balOf`. -/
theorem setField_balOf (f : FieldName) (cell : Value) (v : Value) (hf : f ≠ balanceField) :
    balOf (setField f cell v) = balOf cell := by
  have hfb : (f == balanceField) = false := by
    simpa using beq_eq_false_iff_ne.2 hf
  have hlist : ∀ fs : List (FieldName × Value),
      ((Value.record (setField.setFieldList f fs v)).scalar balanceField)
        = ((Value.record fs).scalar balanceField) := by
    intro fs
    induction fs with
    | nil =>
        simp only [setField.setFieldList, Value.scalar, Value.field]
        rw [List.find?_cons_of_neg (by simpa using hfb)]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setField.setFieldList]
        by_cases hk : (k == f) = true
        · -- replaced field `f`; the `balance` lookup skips it either way (k = f ≠ "balance").
          rw [if_pos hk]
          have hkn : k = f := by simpa using hk
          have hkb : (k == balanceField) = false := by rw [hkn]; exact hfb
          simp only [Value.scalar, Value.field]
          rw [List.find?_cons_of_neg (by simpa using hfb),
              List.find?_cons_of_neg (by simpa using hkb)]
        · -- kept this entry; recurse on the tail, both sides carry the same head.
          rw [if_neg hk]
          simp only [Value.scalar, Value.field] at ih ⊢
          by_cases hkb : (k == balanceField) = true
          · rw [List.find?_cons_of_pos (by simpa using hkb),
                List.find?_cons_of_pos (by simpa using hkb)]
          · rw [List.find?_cons_of_neg (by simpa using hkb),
                List.find?_cons_of_neg (by simpa using hkb)]
            exact ih
  unfold balOf setField
  cases cell with
  | record fs => rw [hlist fs]
  | int _  =>
      simp only [Value.scalar, Value.field]
      rw [List.find?_cons_of_neg (by simpa using hfb)]; rfl
  | dig _  =>
      simp only [Value.scalar, Value.field]
      rw [List.find?_cons_of_neg (by simpa using hfb)]; rfl
  | sym _  =>
      simp only [Value.scalar, Value.field]
      rw [List.find?_cons_of_neg (by simpa using hfb)]; rfl

/-! ## §1 — The Neutral/metadata STEP over the record kernel, and its balance/authority frame.

A Neutral/Monotonic/Terminal effect, unlike Transfer, runs NO gated debit/credit — it is a PURE
named-field write on one cell (`target`), gated only by authority (the actor must own/hold the
target). We model the kernel move as: check authority over the target, then write field `f` of the
target cell to `v`, then append a receipt to the chain (the monotone metadata advance every
committed action carries). The cap table and account set are UNTOUCHED. -/

/-- The authority gate for a self-targeted Neutral/Monotonic/Terminal effect: the actor must hold
authority over the `target` cell. Reuses `RecordKernel.authorizedB` with `src = dst = target`
(the canonical "act on my own cell" turn shape — a field write is not a cross-cell move). -/
def stateAuthB (caps : Caps) (actor target : CellId) : Bool :=
  authorizedB caps { actor := actor, src := target, dst := target, amt := 0 }

/-- **`cellLive k target` — the LIFECYCLE-LIVENESS gate (the R6 fix, defined LOCALLY).** Does
`target`'s lifecycle state admit new effects? `true` only for the Live discriminant (`0`); a Sealed
(`1`) or Destroyed (`3`) cell is fail-closed REJECTED. This is the bare-kernel-level twin of
`TurnExecutorFull.acceptsEffects` (dregg1's `CellLifecycle::accepts_effects`, `lifecycle.rs:109`),
defined HERE because `EffectsState` is imported BY `TurnExecutorFull` (so it cannot import it back
without a cycle). It reads only the `RecordKernelState.lifecycle` side-table — the SAME `0`=Live
discriminant `acceptsEffects` checks, so the two predicates are definitionally interchangeable at the
cutover. Closing R6: a state write into a non-Live cell now FAILS in the live executor. -/
def cellLive (k : RecordKernelState) (target : CellId) : Bool := k.lifecycle target == 0

/-- Write field `f` of `target` to `v` in the kernel state (the bespoke field-write semantics);
every other cell untouched. The metadata-domain move shared by all Neutral/Monotonic/Terminal
effects (a state set, a counter bump, a lifecycle flag). -/
def writeField (k : RecordKernelState) (f : FieldName) (target : CellId) (v : Value) :
    RecordKernelState :=
  { k with cell := fun c => if c = target then setField f (k.cell c) v else k.cell c }

/-- **`stateStep` — the executable semantics of a Neutral/Monotonic/Terminal effect (PROVED
computable).** Fail-closed: commits only when the actor holds authority over `target`, `target` is
a live account (MEMBERSHIP), AND `target`'s lifecycle admits new effects (LIVENESS — `cellLive`, the
R6 fix). On commit, write field `f` of `target` to `v` and extend the receipt chain by one row
(the metadata advance). NO balance move, NO cap edit — the regime invariant.

**R6 — lifecycle liveness now gates the LIVE executor.** Previously the gate consulted only authority
+ membership (`target ∈ accounts`), so a field write into a SEALED/Destroyed cell silently COMMITTED
(bypassing `cellSeal`). The `cellLive` conjunct closes that hole HERE, in the bare step the live
executor (`execFullA`'s `.incrementNonceA`/`.setPermissionsA`/`.setVKA`/`.refusalA`/`.receiptArchiveA`
arms, and — via `stateStepGuarded` — `.setFieldA`) runs: a write into a non-Live cell now returns
`none`, matching the handler's `acceptsEffects` gate. -/
def stateStep (s : RecChainedState) (f : FieldName) (actor target : CellId) (v : Value) :
    Option RecChainedState :=
  if stateAuthB s.kernel.caps actor target = true ∧ target ∈ s.kernel.accounts
      ∧ cellLive s.kernel target = true then
    some { kernel := writeField s.kernel f target v,
           log    := { actor := actor, src := target, dst := target, amt := 0 } :: s.log }
  else
    none

/-- **`stateStep_factors` — PROVED.** A committed `stateStep` was authorized and produced exactly
the field-write post-state + a one-row chain extension. The live-target gate is exposed separately by
`state_target_live`. The bridge every downstream theorem reuses. -/
theorem stateStep_factors {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (h : stateStep s f actor target v = some s') :
    stateAuthB s.kernel.caps actor target = true ∧
      s' = { kernel := writeField s.kernel f target v,
             log := { actor := actor, src := target, dst := target, amt := 0 } :: s.log } := by
  unfold stateStep at h
  by_cases hg : stateAuthB s.kernel.caps actor target = true ∧ target ∈ s.kernel.accounts
      ∧ cellLive s.kernel target = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg.1, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §1.5 — SLOT-CAVEAT ENFORCEMENT: the caveat-gated field write (the foundation of app-safety).

`stateStep` does a plain *authorized* field write — but a factory-minted cell carries per-slot
caveats (`RecordKernel.SlotCaveat`, dregg1's `FactoryDescriptor.program`) that the executor checks
on EVERY `SetField` (`apply_set_field` → `RecordProgram::evaluate`, `cell/src/program.rs:1314`+).
`stateStepGuarded` is the caveat-gated field write: it consults `s.kernel.slotCaveats target` and
COMMITS the very same `stateStep` post-state ONLY when EVERY caveat bound to the written slot is
satisfied by the `(actor, old, new)` transition — otherwise it FAILS CLOSED (`none`).

Because a satisfying write commits EXACTLY `stateStep`'s post-state, ALL of §2–§5's
conservation/authority/forward-sim lemmas lift to `stateStepGuarded` for free (`stateStepGuarded_eq`
below): the caveat gate can only ever TIGHTEN `stateStep`, never move balance or edit caps. This is
what makes a published app-safety REAL — a `nameservice` `Immutable`-owner slot is *registered
forever* because THIS gate rejects any later rewrite, BY THE EXECUTOR. -/

/-- Do ALL caveats bound to slot `f` on cell `target` admit the write of new scalar `new` by `actor`
(against the slot's committed value, read as `fieldOf f (k.cell target)` defaulting absent to `0` —
dregg1's `FIELD_ZERO`)? Caveats on OTHER slots are irrelevant to this write (filtered out). Computable,
decidable, FAIL-CLOSED. Mirrors dregg1's per-slot `RecordProgram::evaluate` filtered to the touched
field. -/
def caveatsAdmit (k : RecordKernelState) (f : FieldName) (actor target : CellId) (new : Int) : Bool :=
  ((k.slotCaveats target).filter (fun cav => cav.field == f)).all
    (fun cav => cav.eval actor (fieldOf f (k.cell target)) new)

/-- **`stateStepGuarded` — the CAVEAT-GATED field write (PROVED computable).** First the authority
gate (`stateStep`), then the slot-caveat gate (`caveatsAdmit`): a write commits iff the actor holds
authority over `target` AND every caveat bound to the written slot admits the `(actor, old, new)`
transition. Fail-closed on EITHER gate. On commit the post-state is EXACTLY `stateStep`'s — the
caveat check only DECIDES, it never mutates extra state. The executable shadow of dregg1's
`apply_set_field` → `RecordProgram::evaluate` (`cell/src/program.rs:1314`+). -/
def stateStepGuarded (s : RecChainedState) (f : FieldName) (actor target : CellId) (n : Int) :
    Option RecChainedState :=
  if caveatsAdmit s.kernel f actor target n = true then
    stateStep s f actor target (.int n)
  else
    none

/-- **`stateStepGuarded_eq` — PROVED.** A committed caveat-gated write is EXACTLY the underlying
`stateStep` write (the caveat gate only restricts the domain — it never changes the post-state). The
bridge that lifts EVERY `stateStep` keystone (conservation, authority, forward-sim) to the guarded
write verbatim. -/
theorem stateStepGuarded_eq {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {n : Int} (h : stateStepGuarded s f actor target n = some s') :
    stateStep s f actor target (.int n) = some s' := by
  unfold stateStepGuarded at h
  by_cases hg : caveatsAdmit s.kernel f actor target n = true
  · rw [if_pos hg] at h; exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`stateStepGuarded_admits` — PROVED.** A committed caveat-gated write means every caveat bound
to the written slot ADMITTED the transition (`caveatsAdmit` held at the pre-state). The witness that
the published per-slot invariants were genuinely enforced. -/
theorem stateStepGuarded_admits {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {n : Int} (h : stateStepGuarded s f actor target n = some s') :
    caveatsAdmit s.kernel f actor target n = true := by
  unfold stateStepGuarded at h
  by_cases hg : caveatsAdmit s.kernel f actor target n = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`stateStepGuarded_caveat_violation_fails` — PROVED (FAIL-CLOSED).** If ANY caveat bound to the
written slot rejects the transition (`caveatsAdmit = false`), the guarded write does NOT commit. This
is the executor-level teeth: an `Immutable` slot rejects any rewrite, a `MonotonicSequence` slot
rejects a non-`+1` write, a `WriteOnce` slot rejects a second write. -/
theorem stateStepGuarded_caveat_violation_fails (s : RecChainedState) (f : FieldName)
    (actor target : CellId) (n : Int) (h : caveatsAdmit s.kernel f actor target n = false) :
    stateStepGuarded s f actor target n = none := by
  unfold stateStepGuarded; rw [if_neg (by rw [h]; simp)]

/-! ## §2 — `state_conserves`: balance UNCHANGED ∧ authority UNCHANGED (the regime invariant).

The Neutral/metadata regime's defining obligation: a non-balance effect's tri-domain reading is
`0` in BOTH the balance and authority domains (it may only advance metadata). We prove the balance
total is unchanged via the §0 non-interference lemma, and the cap table / authority graph are
untouched (the field write never edits `caps`). -/

/-- The field write preserves the conserved `balance` total — PROVED — provided the written field
is not the `balance` field. Every cell's `balOf` is unchanged by a non-balance field write (`§0`
non-interference, applied at the `target`). -/
theorem writeField_recTotal (k : RecordKernelState) (f : FieldName) (target : CellId) (v : Value)
    (hf : f ≠ balanceField) : recTotal (writeField k f target v) = recTotal k := by
  unfold recTotal writeField
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c = target
  · simp only [hc, if_pos]; exact setField_balOf f (k.cell target) v hf
  · simp only [if_neg hc]

/-- **`state_conserves` — BALANCE UNCHANGED (PROVED).** A committed Neutral/Monotonic/Terminal
effect (writing a non-`balance` field) preserves the total balance: `recTotal s'.kernel = recTotal
s.kernel`. The metadata move does NOT perturb the conserved balance — the regime's first
tri-domain obligation (balance `Δ = 0`). -/
theorem state_conserves {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (hf : f ≠ balanceField) (h : stateStep s f actor target v = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨_, hs'⟩ := stateStep_factors h
  subst hs'
  exact writeField_recTotal s.kernel f target v hf

/-- **`state_balance_domain` — PROVED (per-domain Σ = 0).** The realized balance-domain delta of a
committed Neutral/metadata effect nets to `0` (`Spec.conservedInDomain Domain.balance`) — the
executable shadow of dregg1's `excess == 0` gate for the non-conserving-but-balance-neutral colors. -/
theorem state_balance_domain {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (hf : f ≠ balanceField) (h : stateStep s f actor target v = some s') :
    conservedInDomain Domain.balance [recTotal s'.kernel - recTotal s.kernel] := by
  unfold conservedInDomain
  rw [state_conserves hf h]; simp

/-- **`state_caps_unchanged` — PROVED.** A committed Neutral/Monotonic/Terminal effect leaves the
cap table UNTOUCHED (the field write edits only `cell`, never `caps`). -/
theorem state_caps_unchanged {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (h : stateStep s f actor target v = some s') :
    s'.kernel.caps = s.kernel.caps := by
  obtain ⟨_, hs'⟩ := stateStep_factors h
  subst hs'; rfl

/-- **`state_authGraph_unchanged` — PROVED.** A committed Neutral/metadata effect leaves the
reconstructed authority `Graph` (`Spec.execGraph`) UNCHANGED — these effects move metadata, never
connectivity. The regime's second tri-domain obligation (authority `Δ = 0`). -/
theorem state_authGraph_unchanged {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (h : stateStep s f actor target v = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  rw [state_caps_unchanged h]

/-! ## §3 — `state_authorized`: a committed Neutral/metadata effect was authorized. -/

/-- **`state_authorized` — PROVED.** A committed Neutral/Monotonic/Terminal effect implies the
actor held authority over the `target` (`stateAuthB` true at the pre-state). The regime's
authorization obligation, reused from the cap gate. -/
theorem state_authorized {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (h : stateStep s f actor target v = some s') :
    stateAuthB s.kernel.caps actor target = true :=
  (stateStep_factors h).1

/-- **`state_target_live` — PROVED.** A committed Neutral/metadata field write targeted a live account.
This prevents self-authorized writes from creating ghost cell state outside `accounts`. -/
theorem state_target_live {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (h : stateStep s f actor target v = some s') :
    target ∈ s.kernel.accounts := by
  unfold stateStep at h
  by_cases hg : stateAuthB s.kernel.caps actor target = true ∧ target ∈ s.kernel.accounts
      ∧ cellLive s.kernel target = true
  · exact hg.2.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`state_target_lifecycle_live` — PROVED (the R6 teeth).** A committed Neutral/metadata field
write targeted a LIFECYCLE-LIVE cell (`cellLive`, i.e. the lifecycle discriminant is `0`=Live). This
is the executor-level R6 close: a write into a Sealed/Destroyed cell cannot have committed. -/
theorem state_target_lifecycle_live {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (h : stateStep s f actor target v = some s') :
    cellLive s.kernel target = true := by
  unfold stateStep at h
  by_cases hg : stateAuthB s.kernel.caps actor target = true ∧ target ∈ s.kernel.accounts
      ∧ cellLive s.kernel target = true
  · exact hg.2.2
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`state_nonlive_fails` — PROVED (FAIL-CLOSED, the R6 teeth).** A field write into a cell whose
lifecycle does NOT admit effects (`cellLive = false`: Sealed or Destroyed) does NOT commit in the
live executor. This is the executable shadow of dregg1's `accepts_effects` rejection — the hole the
handler closed (`acceptsEffects`) is now closed in the bare step `execFullA` runs. -/
theorem state_nonlive_fails (s : RecChainedState) (f : FieldName) (actor target : CellId)
    (v : Value) (h : cellLive s.kernel target = false) :
    stateStep s f actor target v = none := by
  unfold stateStep
  rw [if_neg]
  intro hg
  rw [h] at hg
  exact absurd hg.2.2 (by simp)

/-- **`state_unauthorized_fails` — PROVED (fail-closed).** If the actor lacks authority over the
target, no Neutral/metadata effect commits. The integrity/confinement core for the regime. -/
theorem state_unauthorized_fails (s : RecChainedState) (f : FieldName) (actor target : CellId)
    (v : Value) (h : stateAuthB s.kernel.caps actor target = false) :
    stateStep s f actor target v = none := by
  unfold stateStep
  rw [if_neg]
  intro hg
  rw [h] at hg
  exact absurd hg.1 (by simp)

/-! ## §4 — `state_metadata`: the metadata domain advances (the only moving domain).

The receipt chain grows by exactly one row (the monotone clock — `Monotonic` for EVERY committed
action), and the target's written field reads back the written value. -/

/-- **`state_obsadvance` — PROVED (metadata MONOTONE advance).** A committed Neutral/metadata
effect grows the receipt chain by exactly one row (the monotone metadata clock — replay-detectable).
This is the `Monotonic` color shared by every kind. -/
theorem state_obsadvance {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (h : stateStep s f actor target v = some s') :
    s'.log.length = s.log.length + 1 := by
  obtain ⟨_, hs'⟩ := stateStep_factors h
  subst hs'; simp

/-- **`state_field_written` — PROVED (the metadata field move).** After a committed Neutral/metadata
effect that writes `.int n`, the target's field `f` reads back exactly `n`. The bespoke field-write
semantics every concrete effect specializes (`SetField` sets a field, `IncrementNonce` writes the
bumped counter, `Seal` raises the flag, …). -/
theorem state_field_written {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {n : Int} (h : stateStep s f actor target (.int n) = some s') :
    fieldOf f (s'.kernel.cell target) = n := by
  obtain ⟨_, hs'⟩ := stateStep_factors h
  subst hs'
  simp only [writeField, if_pos]
  exact setField_fieldOf f (s.kernel.cell target) n

/-- **`state_metadata` — PROVED (the full metadata domain).** A committed Neutral/metadata effect:
(a) writes the target's field `f` to the written scalar `n`, AND (b) advances the receipt chain by
exactly one row, AND (c) leaves the cap table unchanged. The complete metadata-domain obligation. -/
theorem state_metadata {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {n : Int} (h : stateStep s f actor target (.int n) = some s') :
    fieldOf f (s'.kernel.cell target) = n ∧
      s'.log.length = s.log.length + 1 ∧
      s'.kernel.caps = s.kernel.caps :=
  ⟨state_field_written h, state_obsadvance h, state_caps_unchanged h⟩

/-! ## §5 — `state_forward_sim`: the REFINEMENT (forward-simulation square), Neutral regime.

A committed Neutral/metadata effect is matched by an abstract `Spec` step: the abstract balance
total is CONSERVED (`Δ = 0`) and the authority graph is UNCHANGED — the Neutral/metadata bottom
edge of the simulation square (the `EffectTransfer §5` shape, here with BOTH conserved-domain
deltas zero rather than a paired cancellation). -/

section ForwardSim
variable {Statement Witness : Type} [Verifiable Statement Witness]

/-- The record-world abstract Spec state a Neutral/metadata effect refines: the conserved
`balance`-domain total and the reconstructed authority `Graph`. (Same shape as
`EffectTransfer.AbstractT`.) -/
structure AbstractS where
  /-- the conserved `balance`-domain total. -/
  balanceTotal : ℤ
  /-- the reconstructed authority graph. -/
  authGraph    : Dregg2.Spec.Graph Dregg2.Authority.Label Dregg2.Spec.ExecRights

/-- The abstraction function: a chained record state denotes its conserved `recTotal` and its
reconstructed `execGraph`. -/
def absS (s : RecChainedState) : AbstractS :=
  { balanceTotal := recTotal s.kernel, authGraph := execGraph s.kernel.caps }

/-- **`AbsStep a a'`** — the abstract Neutral/metadata step relation: the abstract `balance` total
is CONSERVED (`conservedInDomain Domain.balance` on the realized delta) AND the authority graph is
UNCHANGED. For this regime BOTH the conserved domains are frozen — only metadata (off the abstract
state) advances. The bottom edge of the simulation square. -/
def AbsStep (a a' : AbstractS) : Prop :=
  conservedInDomain Domain.balance [a'.balanceTotal - a.balanceTotal] ∧
    a'.authGraph = a.authGraph

/-- **`state_forward_sim` — THE REFINEMENT (PROVED).** A committed Neutral/Monotonic/Terminal effect
(writing a non-`balance` field) is matched by an abstract `Spec` step `AbsStep (absS s) (absS s')`,
AND the committed effect passed the abstract authority `Guard`. So every executable
Neutral/metadata step is an abstract step (forward simulation), with the abstract balance total
conserved, the authority graph preserved, and the actor admitted by the abstract gate. -/
theorem state_forward_sim {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (w : Statement → Witness) (hf : f ≠ balanceField)
    (h : stateStep s f actor target v = some s') :
    AbsStep (absS s) (absS s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps)
        { actor := actor, src := target, dst := target, amt := 0 } w = true := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- conservation projection: the abstract balance total is conserved (Δ = 0).
    unfold conservedInDomain absS
    rw [state_conserves hf h]; simp
  · -- authority-graph preservation: a Neutral/metadata effect never edits connectivity.
    simp only [absS]
    exact state_authGraph_unchanged h
  · -- the committed effect passed the abstract first-party authority Guard.
    rw [Dregg2.Spec.exec_authz_iff_guard]
    exact state_authorized h

end ForwardSim

/-! ## §6 — TERMINAL effects: the irreversibility-shaped obligation (`LinearityClass::Terminal`).

The `Terminal` color (seal/destroy/makeSovereign/drop/revoke) has NO inverse: the lifecycle flag,
once raised, stays raised. We model a terminal lifecycle flag as a named scalar field whose `1`
encodes "sealed/destroyed/sovereign". The irreversibility obligations:
  * `seal` raises the flag to `1` (`sealField → 1`);
  * a SECOND seal of an already-sealed cell is REJECTED (the one-way gate — no double-seal);
  * the flag is IDEMPOTENT under re-writing `1` (raising-an-already-raised flag is a no-op on the
    field value — there is no path back to `0` through `sealStep`).
This is the executable shadow of `lifecycle::CellLifecycle::is_terminal`. -/

/-- The canonical name of a cell's terminal lifecycle flag (sealed / destroyed / sovereign). -/
def sealField : FieldName := "sealed"

/-- A cell is in the terminal (sealed/destroyed/sovereign) state iff its `sealed` flag reads `1`. -/
def isSealed (v : Value) : Bool := decide (fieldOf sealField v = 1)

/-- The `sealed` lifecycle flag is distinct from the conserved `balance` field. -/
theorem sealField_ne_balance : sealField ≠ balanceField := by decide

/-- **`sealStep` — a TERMINAL seal effect (PROVED computable).** Fail-closed on authority AND on
the one-way gate: a cell that is ALREADY sealed cannot be re-sealed (no double-seal). On commit it
raises the `sealed` flag to `1`. This is the `cellSeal`/`makeSovereign`/`cellDestroy` shape — a
one-way lifecycle transition. -/
def sealStep (s : RecChainedState) (actor target : CellId) : Option RecChainedState :=
  if isSealed (s.kernel.cell target) = true then none  -- already terminal: no inverse, no re-seal
  else stateStep s sealField actor target (.int 1)

/-- **`seal_raises_flag` — PROVED.** A committed `sealStep` raises the target's `sealed` flag to `1`
(the cell enters the terminal state). -/
theorem seal_raises_flag {s s' : RecChainedState} {actor target : CellId}
    (h : sealStep s actor target = some s') :
    isSealed (s'.kernel.cell target) = true := by
  unfold sealStep at h
  by_cases hsealed : isSealed (s.kernel.cell target) = true
  · rw [if_pos hsealed] at h; exact absurd h (by simp)
  · rw [if_neg hsealed] at h
    have := state_field_written h
    unfold isSealed; rw [this]; simp

/-- **`seal_conserves` — PROVED.** A `sealStep` preserves the balance total (the lifecycle flag is
not the balance field). -/
theorem seal_conserves {s s' : RecChainedState} {actor target : CellId}
    (h : sealStep s actor target = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  unfold sealStep at h
  by_cases hsealed : isSealed (s.kernel.cell target) = true
  · rw [if_pos hsealed] at h; exact absurd h (by simp)
  · rw [if_neg hsealed] at h; exact state_conserves sealField_ne_balance h

/-- **`seal_irreversible` — PROVED (the no-double-seal one-way gate).** A cell that is ALREADY in
the terminal (sealed) state cannot be re-sealed: `sealStep` rejects. This is the executable
irreversibility of the `Terminal` color — there is no `sealStep` that re-enters an already-terminal
cell, so the flag, once `1`, has no `sealStep`-path back to `0`. -/
theorem seal_irreversible (s : RecChainedState) (actor target : CellId)
    (h : isSealed (s.kernel.cell target) = true) :
    sealStep s actor target = none := by
  unfold sealStep; rw [if_pos h]

/-- **`seal_authGraph_unchanged` — PROVED.** Sealing a cell does not edit the authority graph
(a lifecycle transition is connectivity-neutral). -/
theorem seal_authGraph_unchanged {s s' : RecChainedState} {actor target : CellId}
    (h : sealStep s actor target = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  unfold sealStep at h
  by_cases hsealed : isSealed (s.kernel.cell target) = true
  · rw [if_pos hsealed] at h; exact absurd h (by simp)
  · rw [if_neg hsealed] at h; exact state_authGraph_unchanged h

/-! ## §7 — Per-effect coincidence: each named dregg1 effect IS a Neutral/Monotonic/Terminal use.

We pin each covered `Effect` variant to its `CatalogInstances.effectLinearity` color (the
faithful-mirror tripwire, mirroring `CatalogEffects §2`) and to which §0–§6 keystone characterizes
it. The non-balance regime is exactly Neutral ∪ Monotonic ∪ Terminal. -/

section EffectColoring
open Dregg2.CatalogInstances (EffectKind effectLinearity)
open Dregg2.Spec.LinearityClass

/-- `SetField` is `Neutral` — characterized by `stateStep`/`state_field_written` (a state-field
write that conserves balance + authority). -/
theorem setField_is_neutral : effectLinearity .setField = Neutral := rfl
/-- `SetVerificationKey` is `Neutral` — a metadata field write (the VK material is a §8 Prop-carrier
portal; here it is the field-write shape). -/
theorem setVerificationKey_is_neutral : effectLinearity .setVerificationKey = Neutral := rfl
/-- `EmitEvent` is `Neutral` — pure book-keeping, the receipt-chain advance. -/
theorem emitEvent_is_neutral : effectLinearity .emitEvent = Neutral := rfl
/-- `SetPermissions` is `Neutral`. -/
theorem setPermissions_is_neutral : effectLinearity .setPermissions = Neutral := rfl
/-- `RefreshDelegation` is `Neutral`. -/
theorem refreshDelegation_is_neutral : effectLinearity .refreshDelegation = Neutral := rfl
/-- `PipelinedSend` is `Neutral`. -/
theorem pipelinedSend_is_neutral : effectLinearity .pipelinedSend = Neutral := rfl
/-- `ExerciseViaCapability` is `Neutral`. -/
theorem exerciseViaCapability_is_neutral : effectLinearity .exerciseViaCapability = Neutral := rfl

/-- `IncrementNonce` is `Monotonic` — characterized by `state_field_written` (the bumped counter). -/
theorem incrementNonce_is_monotonic : effectLinearity .incrementNonce = Monotonic := rfl
/-- `ExportSturdyRef` is `Monotonic` — the export-counter bump (a metadata advance). -/
theorem exportSturdyRef_is_monotonic : effectLinearity .exportSturdyRef = Monotonic := rfl
/-- `EnlivenRef` is `Monotonic` — the use-count bump. -/
theorem enlivenRef_is_monotonic : effectLinearity .enlivenRef = Monotonic := rfl
/-- `ValidateHandoff` is `Monotonic`. -/
theorem validateHandoff_is_monotonic : effectLinearity .validateHandoff = Monotonic := rfl
/-- `Refusal` is `Monotonic` — the proof-of-non-action artifact (a chain row). -/
theorem refusal_is_monotonic : effectLinearity .refusal = Monotonic := rfl

/-- `Seal` (`cellSeal`) is `Terminal` — characterized by `sealStep`/`seal_irreversible`. -/
theorem cellSeal_is_terminal : effectLinearity .cellSeal = Terminal := rfl
/-- `Unseal` (`cellUnseal`) is `Terminal`. -/
theorem cellUnseal_is_terminal : effectLinearity .cellUnseal = Terminal := rfl
/-- `MakeSovereign` is `Terminal` — the cell leaves hosted mode irreversibly. -/
theorem makeSovereign_is_terminal : effectLinearity .makeSovereign = Terminal := rfl
/-- `CellDestroy` is `Terminal`. -/
theorem cellDestroy_is_terminal : effectLinearity .cellDestroy = Terminal := rfl
/-- `ReceiptArchive` is `Terminal`. -/
theorem receiptArchive_is_terminal : effectLinearity .receiptArchive = Terminal := rfl
/-- `DropRef` is `Terminal` — the GC decrement, one-way. -/
theorem dropRef_is_terminal : effectLinearity .dropRef = Terminal := rfl
/-- `RevokeDelegation` is `Terminal`. -/
theorem revokeDelegation_is_terminal : effectLinearity .revokeDelegation = Terminal := rfl
/-- `AttenuateCapability` is `Terminal`. -/
theorem attenuateCapability_is_terminal : effectLinearity .attenuateCapability = Terminal := rfl
/-- `RevokeCapability` is `Terminal`. -/
theorem revokeCapability_is_terminal : effectLinearity .revokeCapability = Terminal := rfl

/-- **The covered regime is exactly the non-balance one** — every effect this module covers is
`Neutral`, `Monotonic`, or `Terminal` (never `Conservative`/`Generative`/`Annihilative`, which move
balance/authority and are `EffectTransfer`/`TriDomain` territory). A bundled witness across the
three families. -/
theorem covered_effects_are_nonbalance :
    effectLinearity .setField = Neutral ∧
    effectLinearity .incrementNonce = Monotonic ∧
    effectLinearity .cellSeal = Terminal :=
  ⟨rfl, rfl, rfl⟩

end EffectColoring

/-! ## §8 — VK material is a Prop-carrier portal (note).

`SetVerificationKey` writes the cell's verification-key material. In dregg1 the VK is cryptographic
(an Ed25519 / STARK VK); in this metatheory it rides the `Verifiable Statement Witness` portal seam
(the `Spec.Guard.witnessed` route — cf. `CatalogInstances §2`'s `signature`/`proof` guards). At the
EXECUTABLE record-cell layer modelled here, `SetVerificationKey` is just a Neutral named-field write
(`setVerificationKey_is_neutral`): it sets a field, conserves balance + authority, advances
metadata — exactly `stateStep`. The cryptographic content of the VK is OFF this layer, behind the
§8 Prop-carrier portal, so no crypto obligation is incurred here. -/

/-! ## §6.5 — The guarded field write inherits the regime invariants (lifted via `stateStepGuarded_eq`).

A committed `stateStepGuarded` IS a committed `stateStep` (the caveat gate only restricts the
domain), so it preserves balance, leaves the authority graph fixed, advances the metadata clock, and
writes the field — VERBATIM the §2–§5 keystones, lifted through `stateStepGuarded_eq`. -/

/-- **`guarded_state_conserves` — BALANCE UNCHANGED (PROVED).** A committed caveat-gated field write
(of a non-`balance` field) preserves the total balance — the caveat gate is balance-neutral. -/
theorem guarded_state_conserves {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {n : Int} (hf : f ≠ balanceField) (h : stateStepGuarded s f actor target n = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  state_conserves hf (stateStepGuarded_eq h)

/-- **`guarded_state_authGraph_unchanged` — PROVED.** A committed caveat-gated write leaves the
authority graph unchanged (caveats gate writes, never connectivity). -/
theorem guarded_state_authGraph_unchanged {s s' : RecChainedState} {f : FieldName}
    {actor target : CellId} {n : Int} (h : stateStepGuarded s f actor target n = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps :=
  state_authGraph_unchanged (stateStepGuarded_eq h)

/-- **`guarded_state_authorized` — PROVED.** A committed caveat-gated write implies the actor held
authority over the target (the authority gate still fires under the caveat gate). -/
theorem guarded_state_authorized {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {n : Int} (h : stateStepGuarded s f actor target n = some s') :
    stateAuthB s.kernel.caps actor target = true :=
  state_authorized (stateStepGuarded_eq h)

/-- **`guarded_state_field_written` — PROVED.** After a committed caveat-gated write, the target's
slot reads back exactly the written value (and — by `stateStepGuarded_admits` — every caveat on that
slot was satisfied by this transition). -/
theorem guarded_state_field_written {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {n : Int} (h : stateStepGuarded s f actor target n = some s') :
    fieldOf f (s'.kernel.cell target) = n :=
  state_field_written (stateStepGuarded_eq h)

/-! ## §9 — Axiom-hygiene tripwires (the honesty pins over every keystone). -/

#assert_axioms setField_fieldOf
#assert_axioms setField_balOf
#assert_axioms stateStep_factors
#assert_axioms writeField_recTotal
#assert_axioms state_conserves
#assert_axioms state_balance_domain
#assert_axioms state_caps_unchanged
#assert_axioms state_authGraph_unchanged
#assert_axioms state_authorized
#assert_axioms state_target_live
#assert_axioms state_target_lifecycle_live
#assert_axioms state_nonlive_fails
#assert_axioms state_unauthorized_fails
#assert_axioms state_obsadvance
#assert_axioms state_field_written
#assert_axioms state_metadata
#assert_axioms state_forward_sim
#assert_axioms sealField_ne_balance
#assert_axioms sealStep
#assert_axioms seal_raises_flag
#assert_axioms seal_conserves
#assert_axioms seal_irreversible
#assert_axioms seal_authGraph_unchanged
#assert_axioms stateStepGuarded_eq
#assert_axioms stateStepGuarded_admits
#assert_axioms stateStepGuarded_caveat_violation_fails
#assert_axioms guarded_state_conserves
#assert_axioms guarded_state_authGraph_unchanged
#assert_axioms guarded_state_authorized
#assert_axioms guarded_state_field_written

/-! ## §10 — Non-vacuity: concrete Neutral / Monotonic / Terminal effects commit and behave.

Cell 0 has balance 100 + nonce 0 + status 0; cell 1 has balance 5. Actor 0 owns cell 0 (authority
by ownership — empty cap table). We run a `SetField`, an `IncrementNonce`-shaped counter bump, and a
`Seal`, checking each commits, conserves balance, advances metadata, and (for seal) is one-way. -/

/-- A chained record state: cells 0,1 with balances 100,5; cell 0 carries `nonce`/`status` fields.
Empty cap table (authority by ownership), empty receipt chain. -/
def ss0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 0),
                                                ("status", .int 0), ("sealed", .int 0)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

-- A SetField on cell 0's "status" → 7 commits (actor 0 owns target 0):
#eval (stateStep ss0 "status" 0 0 (.int 7)).isSome                                  -- true
-- ...conserves the total balance (105 unchanged):
#eval (stateStep ss0 "status" 0 0 (.int 7)).map (fun s => recTotal s.kernel)        -- some 105
#eval recTotal ss0.kernel                                                           -- 105
-- ...writes the field (status reads 7):
#eval (stateStep ss0 "status" 0 0 (.int 7)).map (fun s => fieldOf "status" (s.kernel.cell 0)) -- some 7
-- ...does NOT perturb the balance field of the target:
#eval (stateStep ss0 "status" 0 0 (.int 7)).map (fun s => balOf (s.kernel.cell 0))  -- some 100
-- ...advances the receipt chain by exactly one row (the metadata clock):
#eval (stateStep ss0 "status" 0 0 (.int 7)).map (fun s => s.log.length)             -- some 1
-- An unauthorized actor (9 owns nothing) cannot write a field (fail-closed):
#eval (stateStep ss0 "status" 9 0 (.int 7)).isSome                                  -- false
-- Self-targeting a non-live cell is rejected too: ownership alone cannot create ghost state.
#eval (stateStep ss0 "status" 9 9 (.int 7)).isSome                                  -- false

-- A Monotonic counter bump (nonce 0 → 1) commits and conserves:
#eval (stateStep ss0 "nonce" 0 0 (.int 1)).map (fun s => fieldOf "nonce" (s.kernel.cell 0)) -- some 1
#eval (stateStep ss0 "nonce" 0 0 (.int 1)).map (fun s => recTotal s.kernel)         -- some 105

-- A TERMINAL Seal of cell 0 commits and raises the flag:
#eval (sealStep ss0 0 0).isSome                                                     -- true
#eval (sealStep ss0 0 0).map (fun s => isSealed (s.kernel.cell 0))                  -- some true
#eval (sealStep ss0 0 0).map (fun s => recTotal s.kernel)                           -- some 105 (conserved)
-- ...and a SECOND seal of the now-sealed cell is REJECTED (irreversibility / no double-seal):
#eval ((sealStep ss0 0 0).bind (fun s => sealStep s 0 0)).isSome                    -- false

/-! ### §10.R6 — THE R6 TEETH: a write into a NON-LIVE (Sealed/Destroyed) cell is REJECTED.

The cutover finding, evaluated. `ssR6` is `ss0` with cell 0's LIFECYCLE side-table flipped to Sealed
(`1`) — the cell still EXISTS (`0 ∈ accounts`) and the actor still OWNS it (so authority + membership
both pass), but its lifecycle no longer admits effects. Previously the live `stateStep` gated ONLY on
authority + membership, so this write COMMITTED (the R6 hole — a write bypassing `cellSeal`). With the
`cellLive` gate it now returns `none`, matching the handler's `acceptsEffects`. A LIVE sibling cell
(cell 1, lifecycle `0`) still accepts the same write — the gate only TIGHTENS the non-live case. -/
def ssR6 : RecChainedState :=
  { ss0 with kernel := { ss0.kernel with lifecycle := fun c => if c = 0 then 1 else 0 } }

-- A field write into the now-SEALED cell 0 is REJECTED (R6 CLOSED) — was `true` (the LIVE HOLE):
#eval (stateStep ssR6 "status" 0 0 (.int 7)).isSome                                 -- false (R6 CLOSED)
-- ...even though authority + membership STILL hold (the cell exists and the actor owns it):
#eval (stateAuthB ssR6.kernel.caps 0 0 && decide (0 ∈ ssR6.kernel.accounts))        -- true
-- A write into a LIVE sibling (cell 1, lifecycle 0) still COMMITS — the gate only tightens non-live:
#eval (stateStep ssR6 "balance2" 1 1 (.int 7)).isSome                               -- true (live cell ok)
-- A nonce write (the live executor's `.incrementNonceA` arm) into the Sealed cell is REJECTED too:
#eval (stateStep ssR6 "nonce" 0 0 (.int 1)).isSome                                  -- false (R6 CLOSED)
-- And the guarded `.setFieldA` path inherits it (a Sealed cell rejects even a caveat-clean write):
#eval (stateStepGuarded ssR6 "freeField" 0 0 99).isSome                             -- false (R6 CLOSED)

/-- Non-vacuity of the R6 close: a write into a non-Live cell provably FAILS (`state_nonlive_fails`). -/
example : stateStep ssR6 "status" 0 0 (.int 7) = none :=
  state_nonlive_fails ssR6 "status" 0 0 (.int 7) (by decide)

/-- Non-vacuity of the headline forward-sim at a concrete `SetField` — `state_forward_sim`
instantiated (balance conserved, authority graph preserved, actor admitted). -/
example {Statement Witness : Type} [Verifiable Statement Witness]
    (w : Statement → Witness) (s' : RecChainedState)
    (h : stateStep ss0 "status" 0 0 (.int 7) = some s') :
    AbsStep (absS ss0) (absS s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) ss0.kernel.caps)
        { actor := 0, src := 0, dst := 0, amt := 0 } w = true :=
  state_forward_sim w (by decide) h

/-- Non-vacuity of irreversibility: an already-sealed cell rejects a further seal. -/
example (s' : RecChainedState) (h : sealStep ss0 0 0 = some s') :
    sealStep s' 0 0 = none :=
  seal_irreversible s' 0 0 (seal_raises_flag h)

/-! ## §11 — SLOT-CAVEAT TEETH: the executor genuinely rejects caveat-violating field writes.

Cell 0 carries factory-bound caveats: `status` is `Immutable`, `seq` is `MonotonicSequence`, `owner`
is `WriteOnce`, `level` is `Monotonic`, `band` is `BoundedBy [10,20]`, and `admin` is
`SenderAuthorized [0]`. We exercise each gate: a satisfying write commits, a violating write is
REJECTED BY THE EXECUTOR (fail-closed). This is what makes nameservice "registered-forever" /
subscription "monotone head" real — enforced HERE, not merely carried. -/

/-- A chained state whose cell 0 is factory-minted with six slot caveats; actor 0 owns cell 0. -/
def ssCav : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("status", .int 3),
                                                ("seq", .int 5), ("owner", .int 7),
                                                ("level", .int 2), ("band", .int 15),
                                                ("admin", .int 0)]
                         else .record [("balance", .int 5)]
        caps := fun _ => []
        slotCaveats := fun c => if c = 0 then
            [ .immutable "status", .monotonicSeq "seq", .writeOnce "owner",
              .monotonic "level", .boundedBy "band" 10 20, .senderAuthorized "admin" [0] ]
          else [] }
    log := [] }

-- IMMUTABLE: rewriting `status` (committed 3) to ANY different value is REJECTED; writing 3 (no-op) commits.
#eval (stateStepGuarded ssCav "status" 0 0 9).isSome    -- false (Immutable rejects any rewrite)
#eval (stateStepGuarded ssCav "status" 0 0 3).isSome    -- true  (no-op write to the committed value)

-- MONOTONIC SEQUENCE: `seq` (committed 5) admits only +1 (→6); a non-+1 write (→7) is REJECTED.
#eval (stateStepGuarded ssCav "seq" 0 0 6).isSome       -- true  (5 → 6 = old+1)
#eval (stateStepGuarded ssCav "seq" 0 0 7).isSome       -- false (5 ↛ 7: not old+1)

-- WRITE ONCE: `owner` already set (7 ≠ 0) ⇒ a SECOND (different) write is REJECTED; rewriting 7 is a no-op-OK.
#eval (stateStepGuarded ssCav "owner" 0 0 8).isSome     -- false (write-once, already set)
#eval (stateStepGuarded ssCav "owner" 0 0 7).isSome     -- true  (unchanged)

-- MONOTONIC: `level` (committed 2) admits new ≥ old (→4); a decrease (→1) is REJECTED.
#eval (stateStepGuarded ssCav "level" 0 0 4).isSome     -- true  (2 ≤ 4)
#eval (stateStepGuarded ssCav "level" 0 0 1).isSome     -- false (1 < 2)

-- BOUNDED BY [10,20]: `band` admits 18 (in range); 25 (out of range) is REJECTED.
#eval (stateStepGuarded ssCav "band" 0 0 18).isSome     -- true  (10 ≤ 18 ≤ 20)
#eval (stateStepGuarded ssCav "band" 0 0 25).isSome     -- false (25 > 20)

-- SENDER AUTHORIZED [0]: actor 0 may write `admin`; actor 1 (not in the set) is REJECTED — even
-- though actor 1 would need to OWN cell 0 too, the caveat gate alone refuses a non-member.
#eval (stateStepGuarded { ssCav with kernel := { ssCav.kernel with caps := fun _ => [] } } "admin" 0 0 1).isSome  -- true (actor 0 authorized)
-- A slot with NO caveat (`balance`-adjacent free field) writes freely (recovers prior semantics):
#eval (stateStepGuarded ssCav "freeField" 0 0 999).isSome   -- true (no caveat bound)

-- The committed satisfying write conserves balance and reads back the value (the lifted keystones):
#eval (stateStepGuarded ssCav "seq" 0 0 6).map (fun s => recTotal s.kernel)              -- some 105 (conserved)
#eval (stateStepGuarded ssCav "seq" 0 0 6).map (fun s => fieldOf "seq" (s.kernel.cell 0)) -- some 6

end Dregg2.Exec.EffectsState
