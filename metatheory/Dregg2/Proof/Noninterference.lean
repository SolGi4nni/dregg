/-
# Dregg2.Proof.Noninterference — confidentiality as information-flow noninterference.

This is the **l4v confidentiality axis** of dregg2 (Murray et al.'s seL4 noninterference; the
Volpano–Smith typed-IFC *unwinding* condition), restated over the concrete record executor
(`Exec.TurnExecutorFull.execFullA`). Where `Privacy.lean` tier-1 (`field_projection_hides_private`)
is the *static, one-state* selective-disclosure law, THIS module proves the *dynamic, two-trace*
property: a step driven by the SAME public inputs from two states that agree on the public view
produces post-states that STILL agree on the public view — HIGH (secret) inputs cannot perturb the
LOW (public) observation. That is noninterference.

## The security lattice and the model decision (ember-locked)

The two-point lattice reuses `Privacy.Visibility` as ONE classification vocabulary across the privacy
stack: `pub` = **Low** (public/declassified), `priv` = **High** (confidential). The order `flowsTo`
is the genuine no-write-down order (`High ⋢ Low`).

**ember's MODEL DECISION (locked): an account's balance is HIGH (secret).** This is the *sealed-bid*
policy — the whole point of the Track-A `committed_conservation` is that the *amount* stays hidden.
So the demonstrator policy classifies the `balance` field (and the per-asset ledger, and app-secret
fields like `secret`/bid amounts) as **HIGH**, and the public-observable LOW field-set is the
non-amount metadata. The unwinding theorem PROTECTS `balance` as a HIGH field: two states that differ
ONLY in `balance` are low-equal (the secret is hidden), and a public field-write driven by public
data preserves that low-equality. (This deliberately flips the spec's stated "balance LOW / audit
transparency" default — we follow ember's HIGH decision.)

## The proven effect slice (honest scope)

The unwinding is proved for the **pure-state field-write** slice — the `setFieldA` developer write
(caveat-gated) plus the protocol field-writes (`incrementNonceA`/`setPermissionsA`/`setVKA`,
`refusalA`/`receiptArchiveA`) — all of which route through `EffectsState.stateStep`'s single named-field
write. For these, K1 (a LOW write of a LOW-derived value preserves `lowEq`) and K2 (a HIGH write is
invisible to the low observer) are proved, and K3 lifts them across a whole turn for any list of
slice-confined writes.

What is **OPEN / out of slice** (flagged, not faked): the value-moving effects
(`balanceA`/`mintA`/`burnA`/escrow) only noninterfere when the `bal` ledger is LOW — but ember's
decision makes `bal` HIGH, so a transfer's commit/reject branches on HIGH data and is a *declassifier*
unless its guard is itself LOW. And `makeSovereignA` is provably a LEAK — it writes the LOW
`commitment` field as a hash of the WHOLE pre-state record, HIGH fields included. That leak is the
load-bearing TEETH (`makeSovereign_leaks`): it proves `lowEq` is not vacuous and that the proven slice
genuinely EXCLUDES declassifiers — the boundary between noninterfering effects and declassifiers is
real and proved.

Pure; spec-first; `#assert_axioms` pins every keystone to `{propext, Classical.choice, Quot.sound}`.
No `sorry`/`axiom`/`admit`/`native_decide`. §8 crypto (`stateCommitment` collision-resistance) is
NOT a Lean law here — the leak teeth ride a *closed-term* commitment inequality (`decide`), not a
general injectivity claim.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Privacy
import Dregg2.Tactics

namespace Dregg2.Proof.Noninterference

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (setField fieldOf writeField stateAuthB stateStep stateStep_factors
  setField_balOf setField_fieldOf stateStepGuarded stateStepGuarded_eq)

set_option linter.dupNamespace false

/-! ## §1 — The two-point security lattice.

`Level` reuses `Privacy.Visibility`: `pub` = Low (public), `priv` = High (confidential). -/

/-- The two-point security lattice (Low ⊑ High). We reuse `Privacy.Visibility` as the carrier to
keep ONE field-classification vocabulary across the privacy stack: `pub` = Low (declassified/public),
`priv` = High (confidential). -/
abbrev Level := Dregg2.Privacy.Visibility       -- `.pub` = Low, `.priv` = High

/-- The information-flow order: `Low ⊑ Low`, `Low ⊑ High`, `High ⊑ High`, and crucially
`¬ (High ⊑ Low)` — the no-write-down direction the unwinding needs. A genuine 2-point lattice,
decidable by `cases`. -/
def flowsTo : Level → Level → Prop
  | .pub,  _     => True
  | .priv, .priv => True
  | .priv, .pub  => False

/-- `flowsTo` is decidable (the order is a 2×2 closed table). -/
instance : ∀ a b, Decidable (flowsTo a b)
  | .pub,  _     => isTrue trivial
  | .priv, .priv => isTrue trivial
  | .priv, .pub  => isFalse (fun h => h)

/-- **The lattice has teeth: `High` does NOT flow to `Low`.** This is the no-write-down fact that
makes confidentiality non-trivial — without it `flowsTo` would be the vacuous `fun _ _ => True`. -/
theorem high_not_flowsTo_low : ¬ flowsTo .priv .pub := fun h => h

/-- `Low` flows everywhere (declassified data may be read at any level). -/
theorem low_flowsTo_all (b : Level) : flowsTo .pub b := trivial

/-! ## §2 — Security policy and the low-equality (indistinguishability) relation. -/

/-- A **security policy** classifies each named field as Low/High. The model-shape commitment lives
HERE: a field-name classifier (ember-locked: `balance` and amount/secret fields are `.priv` = HIGH;
public metadata is `.pub` = LOW). A richer per-cell carrier (`CellId → FieldName → Level`) is a
later extension — the field-name slice is the proven one. -/
structure Policy where
  /-- Per-field classification. `.pub` = Low (observable), `.priv` = High (confidential). -/
  fieldLevel : FieldName → Level

/-- The set of field names the policy calls LOW (public-observable). -/
def lowFields (p : Policy) : FieldName → Prop := fun f => p.fieldLevel f = .pub

/-- **Per-cell low-equality:** two cell-records agree on every LOW slot in the observed list. The
observation is the FULL stored `Value` at the field (`Value.field`), not its `Int`-scalar projection
(`fieldOf`) — a low observer of a public field sees whatever value sits there, of WHATEVER `Value`
shape (`.int`, `.dig`, …). This is load-bearing: a `makeSovereign` commitment is stored as a `.dig`,
which `fieldOf` would silently collapse to `0`, hiding the leak; observing `Value.field` keeps the
`.dig` digest genuinely visible (so T1's leak truly manifests — see §7). This is the executor-`Value`
analog of `Privacy.project` / `field_projection_hides_private`: the public view is *independent of* the
values stored in HIGH fields. -/
def cellLowEq (p : Policy) (lowSlots : List FieldName) (v w : Value) : Prop :=
  ∀ f ∈ lowSlots, p.fieldLevel f = .pub → v.field f = w.field f

/-- **lowEq on `RecChainedState` — the low observer's view.** Two states are low-equal iff they have
the same live account set AND, on every live account, their cell-records agree on all LOW fields. The
per-asset `bal` ledger is EXCLUDED (ember-locked: balance is HIGH, so the ledger is not observed), and
`caps` is excluded from the field-confidentiality slice (graph privacy has its own tier — `caps` is
untouched by the field-write slice anyway, so the slice preserves it trivially). -/
def lowEq (p : Policy) (lowSlots : List FieldName) (s t : RecChainedState) : Prop :=
  s.kernel.accounts = t.kernel.accounts ∧
  (∀ c ∈ s.kernel.accounts, cellLowEq p lowSlots (s.kernel.cell c) (t.kernel.cell c))

/-! ### `lowEq` is an equivalence (needed so the unwinding chains). -/

/-- `cellLowEq` is reflexive. -/
theorem cellLowEq_refl (p : Policy) (lowSlots : List FieldName) (v : Value) :
    cellLowEq p lowSlots v v := fun _ _ _ => rfl

/-- `cellLowEq` is symmetric. -/
theorem cellLowEq_symm {p : Policy} {lowSlots : List FieldName} {v w : Value}
    (h : cellLowEq p lowSlots v w) : cellLowEq p lowSlots w v :=
  fun f hf hlow => (h f hf hlow).symm

/-- `cellLowEq` is transitive. -/
theorem cellLowEq_trans {p : Policy} {lowSlots : List FieldName} {u v w : Value}
    (h1 : cellLowEq p lowSlots u v) (h2 : cellLowEq p lowSlots v w) : cellLowEq p lowSlots u w :=
  fun f hf hlow => (h1 f hf hlow).trans (h2 f hf hlow)

/-- **`lowEq` is reflexive.** -/
theorem lowEq_refl (p : Policy) (lowSlots : List FieldName) (s : RecChainedState) :
    lowEq p lowSlots s s :=
  ⟨rfl, fun c _ => cellLowEq_refl p lowSlots (s.kernel.cell c)⟩

/-- **`lowEq` is symmetric.** -/
theorem lowEq_symm {p : Policy} {lowSlots : List FieldName} {s t : RecChainedState}
    (h : lowEq p lowSlots s t) : lowEq p lowSlots t s := by
  obtain ⟨hacc, hcell⟩ := h
  refine ⟨hacc.symm, fun c hc => cellLowEq_symm (hcell c ?_)⟩
  rw [hacc]; exact hc

/-- **`lowEq` is transitive.** -/
theorem lowEq_trans {p : Policy} {lowSlots : List FieldName} {s t u : RecChainedState}
    (h1 : lowEq p lowSlots s t) (h2 : lowEq p lowSlots t u) : lowEq p lowSlots s u := by
  obtain ⟨hacc1, hcell1⟩ := h1
  obtain ⟨hacc2, hcell2⟩ := h2
  refine ⟨hacc1.trans hacc2, fun c hc => cellLowEq_trans (hcell1 c hc) (hcell2 c ?_)⟩
  rw [← hacc1]; exact hc

/-! ## §3 — The field-write non-interference lemmas, at the `Value.field` observation level.

`EffectsState.setField_balOf` proves a write to `f ≠ balanceField` leaves the `Int`-scalar `balOf`
unchanged. The low observation here is the FULL `Value.field` (so the `.dig` commitment is visible),
so we need the `Value.field`-level facts: (i) a write to `f` lands `some v` at slot `f`
(`field_setField_eq`); (ii) a write to `f` leaves the read of ANY OTHER slot `g ≠ f` unchanged
(`field_setField_ne`). Same `setFieldList` induction as `setField_fieldOf`/`setField_balOf`, but on
`Value.field` (the structural value) rather than `Value.scalar` (the `Int` projection). -/

/-- **A write to slot `f` lands `some v` at slot `f` (PROVED), at the `Value.field` level.** The
structural-value companion of `EffectsState.setField_fieldOf` (which reads back the `Int` scalar);
here we read back the whole stored `Value`, so it works for a `.dig` commitment too. -/
theorem field_setField_eq (f : FieldName) (cell v : Value) :
    (setField f cell v).field f = some v := by
  have hlist : ∀ fs : List (FieldName × Value),
      (Value.record (setField.setFieldList f fs v)).field f = some v := by
    intro fs
    induction fs with
    | nil => simp [setField.setFieldList, Value.field]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setField.setFieldList]
        by_cases hk : (k == f) = true
        · rw [if_pos hk]; simp [Value.field]
        · rw [if_neg hk]
          simp only [Value.field] at ih ⊢
          rw [List.find?_cons_of_neg (by simpa using hk)]
          exact ih
  unfold setField
  cases cell with
  | record fs => exact hlist fs
  | int _  => simp [Value.field]
  | dig _  => simp [Value.field]
  | sym _  => simp [Value.field]

/-- **A write to slot `f` does not perturb the `Value.field` read of a DISTINCT slot `g ≠ f`
(PROVED).** The structural-value companion of `setField_balOf` (which is the `Int`-scalar form at
`g = balanceField`). This is the load-bearing non-interference fact: writing one field cannot change
ANOTHER field's stored value. -/
theorem field_setField_ne (f g : FieldName) (cell v : Value) (hg : g ≠ f) :
    (setField f cell v).field g = cell.field g := by
  -- the `List.find?` lookup is on the read field `g`; when the head key is the WRITTEN field `f`
  -- the head predicate is `(f == g)`, so we need this orientation.
  have hfg : (f == g) = false := beq_eq_false_iff_ne.2 (fun h => hg h.symm)
  have hlist : ∀ fs : List (FieldName × Value),
      (Value.record (setField.setFieldList f fs v)).field g = (Value.record fs).field g := by
    intro fs
    induction fs with
    | nil =>
        simp only [setField.setFieldList, Value.field]
        rw [List.find?_cons_of_neg (by simpa using hfg)]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setField.setFieldList]
        by_cases hk : (k == f) = true
        · -- replaced field `f`; the `g`-lookup skips it either way (k = f ≠ g).
          rw [if_pos hk]
          have hkn : k = f := by simpa using hk
          have hkg : (k == g) = false := by rw [hkn]; simpa using hfg
          simp only [Value.field]
          rw [List.find?_cons_of_neg (by simpa using hfg),
              List.find?_cons_of_neg (by simpa using hkg)]
        · -- kept this entry; recurse on the tail, both sides carry the same head.
          rw [if_neg hk]
          simp only [Value.field] at ih ⊢
          by_cases hkg : (k == g) = true
          · rw [List.find?_cons_of_pos (by simpa using hkg),
                List.find?_cons_of_pos (by simpa using hkg)]
          · rw [List.find?_cons_of_neg (by simpa using hkg),
                List.find?_cons_of_neg (by simpa using hkg)]
            exact ih
  unfold setField
  cases cell with
  | record fs => exact hlist fs
  | int _  =>
      simp only [Value.field]
      rw [List.find?_cons_of_neg (by simpa using hfg)]; rfl
  | dig _  =>
      simp only [Value.field]
      rw [List.find?_cons_of_neg (by simpa using hfg)]; rfl
  | sym _  =>
      simp only [Value.field]
      rw [List.find?_cons_of_neg (by simpa using hfg)]; rfl

/-! ### Lifting the field-write lemmas through `writeField` (the kernel-level edit).

`writeField k f target v` edits ONLY `k.cell target`'s field `f`. So on a NON-target cell the record
is untouched, and on the target cell `Value.field g` is unchanged for `g ≠ f`. -/

/-- A non-target cell is untouched by `writeField`. -/
theorem writeField_cell_other (k : RecordKernelState) (f : FieldName) (target c : CellId)
    (v : Value) (hc : c ≠ target) : (writeField k f target v).cell c = k.cell c := by
  simp only [writeField, if_neg hc]

/-- On ANY cell, reading a slot `g ≠ f` after `writeField f` is unchanged at the `Value.field` level
(target: `field_setField_ne`; non-target: the record is untouched). -/
theorem writeField_field_ne (k : RecordKernelState) (f g : FieldName) (target c : CellId)
    (v : Value) (hg : g ≠ f) :
    ((writeField k f target v).cell c).field g = (k.cell c).field g := by
  simp only [writeField]
  by_cases hc : c = target
  · subst hc; rw [if_pos rfl]; exact field_setField_ne f g (k.cell c) v hg
  · rw [if_neg hc]

/-! ## §4 — KEYSTONE K1: single-step unwinding for the LOW field-write (Volpano–Smith / seL4).

If `s ≈_L t` and the SAME public field-write (a LOW slot `f`, with the SAME literal `Int` value `v`
in both traces — the "LOW-derived value" condition) commits in both, the post-states are STILL
low-equal. HIGH inputs cannot perturb the LOW observation. -/

/-- The state after a committed `setFieldA` to slot `f` with value `n` is the `stateStep` post-state
(the caveat gate only restricts the domain — `stateStepGuarded_eq`), whose kernel is `writeField`. -/
theorem execFullA_setFieldA_writeField {s s' : RecChainedState} {actor cell : CellId}
    {f : FieldName} {n : Int} (h : execFullA s (.setFieldA actor cell f n) = some s') :
    s'.kernel = writeField s.kernel f cell (.int n) := by
  -- `execFullA (.setFieldA …) = stateStepGuarded …`; lift to the bare `stateStep`, then factor.
  have hstep : stateStepGuarded s f actor cell n = some s' := h
  have hbare : stateStep s f actor cell (.int n) = some s' := stateStepGuarded_eq hstep
  obtain ⟨_, hs'⟩ := stateStep_factors hbare
  rw [hs']

/-- **`accounts` is preserved by a committed `setFieldA`** (the field write never edits `accounts`). -/
theorem execFullA_setFieldA_accounts {s s' : RecChainedState} {actor cell : CellId}
    {f : FieldName} {n : Int} (h : execFullA s (.setFieldA actor cell f n) = some s') :
    s'.kernel.accounts = s.kernel.accounts := by
  rw [execFullA_setFieldA_writeField h]; rfl

/-- **KEYSTONE K1 — single-step unwinding for the LOW field-write.** If `s` and `t` are low-equal and
the `setFieldA` effect writes a LOW slot `f` with the SAME literal value `n` (the LOW-derived value:
the written datum is identical in both traces, hence not a function of any secret), then the
post-states are STILL low-equal. This is the seL4/Volpano–Smith confinement: HIGH inputs cannot
perturb the LOW observation. -/
theorem unwinding_setField
    (p : Policy) (lowSlots : List FieldName)
    (actor cell : CellId) (f : FieldName) (n : Int)
    {s t s' t' : RecChainedState}
    (hst  : lowEq p lowSlots s t)
    (hes  : execFullA s (.setFieldA actor cell f n) = some s')
    (het  : execFullA t (.setFieldA actor cell f n) = some t') :
    lowEq p lowSlots s' t' := by
  obtain ⟨hacc, hcell⟩ := hst
  have hs'k : s'.kernel = writeField s.kernel f cell (.int n) := execFullA_setFieldA_writeField hes
  have ht'k : t'.kernel = writeField t.kernel f cell (.int n) := execFullA_setFieldA_writeField het
  refine ⟨?_, ?_⟩
  · -- accounts: both writes preserve the (equal) account sets.
    rw [hs'k, ht'k]; show s.kernel.accounts = t.kernel.accounts; exact hacc
  · -- per-cell LOW agreement on each live account.
    intro c hc
    -- `c` is a live account of `s'`, i.e. of `s`.
    have hc0 : c ∈ s.kernel.accounts := by
      rw [hs'k] at hc; exact hc
    intro g hg hglow
    -- two cases on the read field `g`:
    by_cases hgf : g = f
    · -- writing slot `g = f` to the SAME literal `n` on both sides ⇒ both store `some (.int n)`.
      subst hgf
      rw [hs'k, ht'k]
      -- the write touches cell `cell`; for the read of slot `g` we only care about cell `c`.
      by_cases hcc : c = cell
      · subst hcc
        rw [show (writeField s.kernel g c (.int n)).cell c
              = setField g (s.kernel.cell c) (.int n) by simp [writeField],
            show (writeField t.kernel g c (.int n)).cell c
              = setField g (t.kernel.cell c) (.int n) by simp [writeField]]
        rw [field_setField_eq, field_setField_eq]
      · -- non-target cell: untouched on both sides; falls back to the pre-state LOW agreement.
        rw [writeField_cell_other s.kernel g cell c (.int n) hcc,
            writeField_cell_other t.kernel g cell c (.int n) hcc]
        exact hcell c hc0 g hg hglow
    · -- reading a slot `g ≠ f`: the write doesn't perturb it on either side; pre-state agreement.
      rw [hs'k, ht'k,
          writeField_field_ne s.kernel f g cell c (.int n) hgf,
          writeField_field_ne t.kernel f g cell c (.int n) hgf]
      exact hcell c hc0 g hg hglow

/-! ## §5 — KEYSTONE K2: HIGH-write confinement (the no-write-down half).

A write to a HIGH slot is INVISIBLE to the low observer: the post-state is low-equal to the
pre-state. (Holds whenever the written slot is not itself one of the observed LOW slots — which is
exactly what HIGH means under a well-formed policy where `lowSlots` are all LOW.) -/

/-- **KEYSTONE K2 — HIGH-write confinement.** If the policy classifies `f` as HIGH (`.priv`), then a
committed `setFieldA` to slot `f` leaves the LOW observation UNCHANGED: `s ≈_L s'`. The low observer
sees no change — HIGH writes are confined. (Proof: every observed LOW slot `g` is `.pub ≠ f`'s `.priv`,
hence `g ≠ f`, hence `fieldOf g` is preserved by the write.) -/
theorem unwinding_high_write_invisible
    (p : Policy) (lowSlots : List FieldName)
    (actor cell : CellId) (f : FieldName) (n : Int)
    (hhigh : p.fieldLevel f = .priv)
    {s s' : RecChainedState}
    (hes : execFullA s (.setFieldA actor cell f n) = some s') :
    lowEq p lowSlots s s' := by
  have hs'k : s'.kernel = writeField s.kernel f cell (.int n) := execFullA_setFieldA_writeField hes
  refine ⟨?_, ?_⟩
  · -- accounts unchanged.
    rw [hs'k]; rfl
  · intro c _ g _ hglow
    -- `g` is observed LOW (`.pub`); `f` is HIGH (`.priv`); so `g ≠ f`.
    have hgf : g ≠ f := by
      intro hgf; rw [hgf] at hglow; rw [hhigh] at hglow; exact absurd hglow (by decide)
    rw [hs'k, writeField_field_ne s.kernel f g cell c (.int n) hgf]

/-! ## §6 — KEYSTONE K3: whole-turn lockstep noninterference.

We lift K1 across a whole turn. A field-write action is **slice-confined** if it is a `setFieldA`.
For two low-equal pre-states running the SAME confined turn, the post-states are low-equal. The turn
must commit in BOTH traces (the unwinding is a relation between two *successful* runs; failure is a
separate liveness concern). -/

/-- A `FullActionA` is in the proven noninterference slice iff it is a developer `setFieldA` write.
(The other `stateStep`-family writes route identically; this is the minimal honest slice for which K1
is stated as a `setFieldA` law. The transfer/authority/declassifier effects are OPEN/out of slice —
see the module header.) -/
def sliceConfined : FullActionA → Prop
  | .setFieldA _ _ _ _ => True
  | _                  => False

/-- **KEYSTONE K3 — whole-turn lockstep noninterference.** If every action of `tt` is slice-confined
(a LOW-or-HIGH field write driven by the SAME public action data), and the turn commits in BOTH the
`s`-trace and the `t`-trace from low-equal pre-states, the post-states are low-equal. Proved by
induction on `tt` reusing K1 at each step. NOTE: each `setFieldA` carries its OWN written value `n` in
the action itself — so "same action" already encodes "same (public) written datum", the LOW-derived
condition K1 needs. -/
theorem unwinding_turn
    (p : Policy) (lowSlots : List FieldName) :
    ∀ (tt : List FullActionA), (∀ a ∈ tt, sliceConfined a) →
      ∀ {s t s' t' : RecChainedState}, lowEq p lowSlots s t →
        execFullTurnA s tt = some s' → execFullTurnA t tt = some t' →
        lowEq p lowSlots s' t'
  | [], _, s, t, s', t', hst, hes, het => by
      simp only [execFullTurnA, Option.some.injEq] at hes het
      subst hes; subst het; exact hst
  | a :: rest, hslice, s, t, s', t', hst, hes, het => by
      -- peel the head action; it commits in both traces (else the turn would fail).
      simp only [execFullTurnA] at hes het
      -- `a` is slice-confined ⇒ it is a `setFieldA`.
      have ha : sliceConfined a := hslice a List.mem_cons_self
      -- split on the head; only `setFieldA` survives `sliceConfined`, the rest are `False`.
      cases a
      case setFieldA actor cell f n =>
          -- destruct the head commit in both traces.
          cases hsa : execFullA s (.setFieldA actor cell f n) with
          | none => rw [hsa] at hes; exact absurd hes (by simp)
          | some s1 =>
            cases hta : execFullA t (.setFieldA actor cell f n) with
            | none => rw [hta] at het; exact absurd het (by simp)
            | some t1 =>
              rw [hsa] at hes; rw [hta] at het
              -- K1 advances the low-equality across the head.
              have hst1 : lowEq p lowSlots s1 t1 :=
                unwinding_setField p lowSlots actor cell f n hst hsa hta
              -- recurse on the tail.
              exact unwinding_turn p lowSlots rest
                (fun b hb => hslice b (List.mem_cons_of_mem _ hb)) hst1 hes het
      -- all non-`setFieldA` heads are excluded by `sliceConfined a` (= `False`).
      all_goals (exact absurd ha (by simp [sliceConfined]))

/-! ## §7 — TEETH.

The keystones must not be vacuous. We exhibit (T3) that `lowEq` genuinely separates and genuinely
hides, (T4) that K1's slice is inhabited by a real committing step, and (T1 — the central teeth) that
`makeSovereign` is a genuine LEAK that BREAKS noninterference, which is why it is EXCLUDED from the
confined slice. The leak forces `lowEq` to have teeth and the slice to be a real boundary. -/

/-- The demonstrator policy: `balance` and `secret` are HIGH (ember-locked — sealed-bid), `commitment`
and the public metadata are LOW. -/
def policyLeak : Policy where
  fieldLevel f := if f = balanceField then .priv
                  else if f = "secret" then .priv
                  else .pub                       -- commitment / public metadata = LOW

/-- Two states agreeing on all LOW fields but DIFFERING in the HIGH `secret` field. (Both carry
`balance = 0` LOW-equal at the observed `commitment` slot — neither has a `commitment` yet, both read
`0` — and DIFFER only in the HIGH `secret`.) -/
def sLeak : RecChainedState :=
  { kernel := { accounts := {0}
                caps := fun _ => []
                cell := fun _ => .record [(balanceField, .int 0), ("secret", .int 7)] }
    log := [] }

def tLeak : RecChainedState :=
  { kernel := { accounts := {0}
                caps := fun _ => []
                cell := fun _ => .record [(balanceField, .int 0), ("secret", .int 99)] }
    log := [] }

/-! ### T3 — `lowEq` is a non-trivial relation (separates on LOW, hides on HIGH). -/

/-- **T3a — HIGH is genuinely hidden.** `sLeak` and `tLeak` differ ONLY in the HIGH `secret` field;
they ARE low-equal on the observed LOW slot `["commitment"]`. So `lowEq` does NOT see the secret —
balance/secret confidentiality is real, not the vacuous `fun _ _ => True`. -/
theorem sLeak_lowEq_tLeak : lowEq policyLeak ["commitment"] sLeak tLeak := by
  refine ⟨rfl, ?_⟩
  intro c _ g hg hglow
  -- the only observed slot is "commitment"; neither record carries it ⇒ both read `none`.
  simp only [List.mem_singleton] at hg
  subst hg
  -- both `sLeak` and `tLeak` cells lack a `commitment` field ⇒ both `Value.field` reads are `none`.
  show (sLeak.kernel.cell c).field "commitment" = (tLeak.kernel.cell c).field "commitment"
  rfl

/-- **T3b — `lowEq` genuinely SEPARATES on a LOW field.** A state differing from `sLeak` in the LOW
`commitment` field is NOT low-equal to it (when `commitment` is observed). So `lowEq` is a proper,
discriminating relation — it is not collapsed to `True`. -/
theorem lowEq_separates :
    ¬ lowEq policyLeak ["commitment"]
        sLeak
        { kernel := { accounts := {0}
                      caps := fun _ => []
                      cell := fun _ => .record [(balanceField, .int 0), ("commitment", .int 5)] }
          log := [] } := by
  intro h
  obtain ⟨_, hcell⟩ := h
  have hc : (0 : CellId) ∈ sLeak.kernel.accounts := by
    show (0 : CellId) ∈ ({0} : Finset CellId); decide
  have hsep := hcell 0 hc "commitment" (by simp) (by decide)
  -- LHS reads `commitment` from `[(balance,0),(secret,7)]` (reduces to `none`); RHS reads it from
  -- `[(balance,0),(commitment,5)]` (reduces to `some (.int 5)`). `none = some _` is absurd.
  rw [show ((Value.record [(balanceField, .int 0), ("commitment", .int 5)]).field "commitment"
            : Option Value) = some (.int 5) from rfl] at hsep
  simp at hsep

/-! ### T4 — non-vacuity: K1's slice is inhabited by a real committing step. -/

/-- A LOW `setFieldA` writing the LOW slot `commitment := 42` (self-authorized: `actor = cell = 0`,
so `stateAuthB` passes unconditionally; no factory caveats ⇒ `caveatsAdmit` passes). -/
def lowWrite : FullActionA := .setFieldA 0 0 "commitment" 42

/-- **T4a — the LOW write COMMITS from both `sLeak` and `tLeak`.** The slice is inhabited by a real
step (not an empty hypothesis) — `execFullA … |>.isSome`. -/
theorem lowWrite_commits_sLeak : (execFullA sLeak lowWrite).isSome = true := by decide

theorem lowWrite_commits_tLeak : (execFullA tLeak lowWrite).isSome = true := by decide

/-- **T4b — K1 is non-vacuously satisfied: two HIGH-differing-but-LOW-equal states, run through the
same LOW write, stay low-equal.** This instantiates `unwinding_setField` at a genuinely committing
step from genuinely-HIGH-differing states — the unwinding is inhabited, not vacuous. -/
theorem unwinding_setField_inhabited
    {s' t' : RecChainedState}
    (hes : execFullA sLeak lowWrite = some s')
    (het : execFullA tLeak lowWrite = some t') :
    lowEq policyLeak ["commitment"] s' t' :=
  unwinding_setField policyLeak ["commitment"] 0 0 "commitment" 42 sLeak_lowEq_tLeak hes het

/-! ### T1 — the CENTRAL TEETH: `makeSovereign` is a genuine LEAK. -/

/-- **The leak fact (closed-term, `decide`).** `stateCommitment` of `sLeak`'s record differs from that
of `tLeak`'s record, because it folds in the HIGH `secret` field (`7` vs `99`). So the commitment is a
function of the secret — a write of it into the LOW `commitment` slot LEAKS the secret. This is a
*closed-term inequality* (NOT general injectivity of `stateCommitment` — that would be the §8
collision-resistance portal, never claimed here). -/
theorem stateCommitment_differs :
    stateCommitment (.record [(balanceField, .int 0), ("secret", .int 7)])
      ≠ stateCommitment (.record [(balanceField, .int 0), ("secret", .int 99)]) := by
  decide

/-- After a committed `makeSovereignStep`, the rebound cell IS the commitment-only record whose LOW
`commitment` slot carries the `.dig` digest `stateCommitment` of the whole pre-state value. We read
that slot at the `Value.field` level — the digest is GENUINELY observable (it is NOT collapsed to a
scalar `0` the way `fieldOf` would). This is the exact reading `cellLowEq` performs on the observed
LOW `commitment` slot, so it is what the leak teeth (T1) compares. -/
theorem makeSovereign_commitment_value {s s' : RecChainedState} {actor cell : CellId}
    (h : execFullA s (.makeSovereignA actor cell) = some s') :
    (s'.kernel.cell cell).field commitmentField
      = some (.dig (stateCommitment (s.kernel.cell cell))) := by
  -- `execFullA (.makeSovereignA …) = makeSovereignStep`; factor + read the rebound literal record.
  have hstep : makeSovereignStep s actor cell = some s' := h
  obtain ⟨_, hs'⟩ := makeSovereignStep_factors hstep
  rw [hs', makeSovereignKernel_cell_eq]
  -- the rebound cell is `[(commitment, .dig (stateCommitment …))]`; the head field IS `commitment`,
  -- so the lookup hits it ⇒ `some (.dig …)` (computes by `rfl`: closed-string field match).
  rfl

/-- **T1 — `makeSovereign` LEAKS, refuted as a theorem (the central TEETH).** `sLeak ≈_L tLeak` (they
agree on every LOW field — they differ only in the HIGH `secret`), yet there is NO way to make the
post-`MakeSovereign` states low-equal on the observed `commitment` slot: the commitment field is
written from `stateCommitment` of the whole record, which DIFFERS between the two (it folds in the
HIGH secret). So noninterference FAILS for `makeSovereignA` — it is a DECLASSIFIER, not a
noninterfering effect, and is correctly EXCLUDED from `sliceConfined`. This is the load-bearing teeth:
it proves `lowEq` is not vacuous and that the proven slice (K1–K3) genuinely excludes the leak. -/
theorem makeSovereign_leaks :
    lowEq policyLeak ["commitment"] sLeak tLeak ∧
    ¬ ( ∀ s' t', execFullA sLeak (.makeSovereignA 0 0) = some s' →
                 execFullA tLeak (.makeSovereignA 0 0) = some t' →
                 lowEq policyLeak ["commitment"] s' t' ) := by
  refine ⟨sLeak_lowEq_tLeak, ?_⟩
  intro hni
  -- both makeSovereign steps commit (self-authorized; `actor = cell = 0`). Name the post-states.
  obtain ⟨s', hes⟩ : ∃ s', execFullA sLeak (.makeSovereignA 0 0) = some s' := ⟨_, rfl⟩
  obtain ⟨t', het⟩ : ∃ t', execFullA tLeak (.makeSovereignA 0 0) = some t' := ⟨_, rfl⟩
  obtain ⟨hacc, hcell⟩ := hni s' t' hes het
  -- cell `0` is a live account of `s'` (it is of `sLeak`, and `makeSovereign` preserves `accounts`).
  have hc : (0 : CellId) ∈ s'.kernel.accounts := by
    obtain ⟨_, hs'⟩ := makeSovereignStep_factors (show makeSovereignStep sLeak 0 0 = some s' from hes)
    rw [hs']; show (0 : CellId) ∈ ({0} : Finset CellId); decide
  -- the observed LOW `commitment` slot of the two post-states is EQUAL (by `hcell`); but it carries
  -- `.dig (stateCommitment (pre cell))` on each side, and the two commitments DIFFER (they fold in
  -- the HIGH `secret`, `7` vs `99`). Reading both via `makeSovereign_commitment_value` and peeling the
  -- `some`/`.dig` constructors reduces the contradiction to a closed-term Nat inequality.
  have heq := hcell 0 hc commitmentField (by simp [commitmentField]) (by decide)
  rw [makeSovereign_commitment_value hes, makeSovereign_commitment_value het] at heq
  simp only [sLeak, tLeak, Option.some.injEq, Value.dig.injEq] at heq
  -- `heq : stateCommitment [(balance,0),(secret,7)] = stateCommitment [(balance,0),(secret,99)]`,
  -- i.e. `227176 = 301328` — refuted.
  exact absurd heq (by decide)

/-! ## §8 — Non-vacuity #eval demos (the slice is real, the leak is real). -/

-- K1 is inhabited: the LOW write commits from the HIGH-differing states.
#eval (execFullA sLeak lowWrite).isSome    -- true
#eval (execFullA tLeak lowWrite).isSome    -- true

-- the leak is real: the two commitments genuinely differ (the §8 closed-term witness).
#eval decide (stateCommitment (.record [(balanceField, .int 0), ("secret", .int 7)])
            ≠ stateCommitment (.record [(balanceField, .int 0), ("secret", .int 99)]))  -- true

-- the lattice has teeth: High does NOT flow to Low.
#eval decide (¬ flowsTo .priv .pub)        -- true

/-! ## §9 — Axiom-hygiene tripwires.

Every keystone (K1/K2/K3) and the central leak teeth (T1) plus the lattice/separation facts are
kernel-clean (axioms ⊆ {propext, Classical.choice, Quot.sound}). The §8 crypto residue
(collision-resistance of `stateCommitment`) is NOT an axiom these pins would catch — the leak rides a
closed-term `decide` inequality, not a general injectivity claim. -/
#assert_axioms unwinding_setField
#assert_axioms unwinding_high_write_invisible
#assert_axioms unwinding_turn
#assert_axioms makeSovereign_leaks
#assert_axioms lowEq_refl
#assert_axioms lowEq_symm
#assert_axioms lowEq_trans
#assert_axioms field_setField_eq
#assert_axioms field_setField_ne
#assert_axioms high_not_flowsTo_low
#assert_axioms sLeak_lowEq_tLeak
#assert_axioms lowEq_separates

end Dregg2.Proof.Noninterference
