/-
# EffectAlgebraSketch — the argument of `docs/reference/EFFECT-ALGEBRA-RECKONING-2026-07-26.md`,
  as a standalone Lean model.

⚑⚑ SUBSTRATE: this file is LEAN. The refactoring it sketches is for a LEAN-AUTHORED effect algebra
and a LEAN-AUTHORED AIR. Nothing here proposes, or licenses, a hand-written Rust AIR. The `Act`
factoring in §5 is a proposal for `Dregg2/Exec/EffectsState.lean` + the emit path, with Rust calling
in — never mirroring.

⚑⚑ STATUS: **UNELABORATED.** This file has NOT been run (`lake build` / `lake env lean` were
forbidden by the task that produced it). Every proof script below is a PROPOSAL, not a result. Treat
a green here as unverified until someone actually elaborates it. It is deliberately SELF-CONTAINED —
no `Dregg2` imports, no mathlib — so that `lake env lean EffectAlgebraSketch.lean` alone settles it.

⚑ IT CANNOT BREAK THE BUILD. `metatheory/lakefile.toml`'s default targets are
`Dregg2 / Metatheory / Polis / Market / Bfv`; `Metatheory` and `Polis` are GLOBBED on their own
subtrees, and the other three are root-module libs. This file is top-level, is not `Metatheory.*` or
`Polis.*`, and is imported by nothing — so `lake build` never reaches it. Same standing as
`metatheory/EmitRotationV3SetFieldValue8.lean`. If you later want it gated, give it a root module or
import it from `Dregg2.lean` — but only AFTER it elaborates.

⚑ SCOPE: this is a MODEL, not the deployed object. It abstracts `RecChainedState` to
`{rec, log}` and `SlotCaveat` to a `Bool`-valued relation. It proves things about THE MODEL. The
value of doing it here is that the model is small enough that the negative results are checkable in
one file; the value of P1.3 in the reckoning is promoting them to the real types
(`Dregg2/Exec/EffectsState.lean`, `Dregg2/Exec/TurnExecutorFull/PerAsset.lean`).

## What it establishes

§2  ABSORPTION FAILS, for two independent reasons — the receipt log, and the guard.
    (`absorption_fails_on_log`, `absorption_fails_on_guard`)

§3  THE TWO ADMISSION SEMANTICS ARE INCOMPARABLE. `caveatsAdmit` is evaluated PER WRITE
    (`Dregg2/Exec/EffectsState.lean:248`); the Rust cell program is evaluated ONCE PER ACTION over
    the whole `(old,new)` transition (`turn/src/executor/execute_tree.rs:175`, `:1175`, with the
    pre-action snapshot at `:827-831`). This file exhibits both directions of divergence.
    (`perStep_admits_whole_refuses`, `whole_admits_perStep_refuses`)

§4  TRANSITIVITY IS EXACTLY THE REPAIR for one direction — and the two `SlotCaveat` constructors
    that lack it are exactly the two the divergence lives in.
    (`perStep_implies_whole`, `monotonicSeq_not_transitive`)

§5  UNDER THE DELTA FACTORING both problems dissolve, and SAME-SLOT WRITES COMMUTE — which is the
    law the deployed permission-effect reordering (`execute_tree.rs:845-848`) silently needs and
    cannot currently state. (`drun_admits_iff_all`, `dstep_comm`, `setValue_not_comm`)

The contrast in §5 is the whole point: **deltas commute, values do not.**
-/

namespace EffectAlgebraSketch

/-! ## §1 — The model.

A cell record is a name-keyed association list (faithful to `Dregg2/Exec/Value.lean:61`'s
`Value.record : List (FieldName × Value)`, projected to scalars). The state carries a `log` counter
standing for the receipt chain, which `Dregg2/Exec/CellCarry.lean:95` (`execFullTurnA_logMono`) and
`PerAsset.lean:2652` (`execFullA_log_suffix`) establish grows by at least one row per committed step. -/

/-- A cell's scalar fields: name-keyed, unbounded, overwrite-in-place, append-if-absent. -/
abbrev Rec := List (String × Int)

/-- `get r f` — read field `f`, defaulting absent to `0` (dregg1's `FIELD_ZERO`;
`Dregg2/Exec/EffectsState.lean:85` `fieldOf`). -/
def get : Rec → String → Int
  | [],             _ => 0
  | (k, x) :: rest, f => if k = f then x else get rest f

/-- `set r f v` — write field `f` (`Dregg2/Exec/EffectsState.lean:73` `setField`). -/
def set : Rec → String → Int → Rec
  | [],             f, v => [(f, v)]
  | (k, x) :: rest, f, v => if k = f then (f, v) :: rest else (k, x) :: set rest f v

/-- The state a step acts on: the record, plus the receipt-chain length. -/
structure St where
  rec : Rec
  log : Nat
  deriving Repr

/-- **The write/read law** (`setField_fieldOf`, `EffectsState.lean:89`). -/
theorem get_set_self (r : Rec) (f : String) (v : Int) : get (set r f v) f = v := by
  induction r with
  | nil => simp [set, get]
  | cons hd tl ih =>
      obtain ⟨k, x⟩ := hd
      by_cases h : k = f
      · subst h; simp [set, get]
      · simp [set, get, h, ih]

/-! ## §1.1 — The caveat language, as a `Bool`-valued relation on `(old, new)`.

Faithful in shape to `Dregg2/Exec/RecordKernel.lean:87` `SlotCaveat` (six of its eight constructors;
`senderAuthorized`/`clearanceGe` are omitted because they gate on the ACTOR, not the value — see
§3.3 of the reckoning, which argues they are misfiled into the wrong substance). -/

inductive Caveat where
  /-- `new = old` — the slot is registered forever. -/
  | immutable
  /-- `old ≤ new` — append-only counter / expiry extension. -/
  | monotonic
  /-- `new = old + 1` — replay-safe sequencing. ⚑ NOT transitive. -/
  | monotonicSeq
  /-- `lo ≤ new ≤ hi` — a bounded/windowed slot. Depends on `new` alone. -/
  | boundedBy (lo hi : Int)
  /-- `old = 0 ∨ new = old` — frozen after the first non-zero write. -/
  | writeOnce
  /-- no constraint (an unbound slot). -/
  | free
  deriving Repr

/-- The caveat evaluator (`SlotCaveat.eval`, consulted by `caveatsAdmit`,
`Dregg2/Exec/EffectsState.lean:248-250`). -/
def Caveat.admits : Caveat → Int → Int → Bool
  | .immutable,     o, n => n == o
  | .monotonic,     o, n => decide (o ≤ n)
  | .monotonicSeq,  o, n => n == o + 1
  | .boundedBy l h, _, n => decide (l ≤ n) && decide (n ≤ h)
  | .writeOnce,     o, n => (o == 0) || (n == o)
  | .free,          _, _ => true

/-! ## §1.2 — The two admission semantics, side by side.

`runPerStep` is the LEAN kernel's shape: the guard runs on EVERY write, against the value CURRENTLY
in the cell (`stateStepGuarded`, `EffectsState.lean:258`, over `caveatsAdmit`, `:248`).

`runWhole` is the RUST executor's shape: the effects are applied, and the cell program is evaluated
ONCE over the pre-action `old_state` and the post-action `new_state`
(`evaluate_cell_program_for_executor`, `turn/src/executor/execute_tree.rs:175`, called at `:1175`
with the snapshot taken at `:827-831`).

They are stated over an ARBITRARY `Bool`-valued relation `R` so that §4 can isolate exactly which
property of `R` makes them agree. -/

/-- Per-write guarded run — fail-closed, all-or-nothing (`execFullTurnA`, `PerAsset.lean:2302`). -/
def runPerStep (R : Int → Int → Bool) (f : String) : List Int → St → Option St
  | [],      s => some s
  | v :: vs, s =>
      if R (get s.rec f) v then
        runPerStep R f vs { rec := set s.rec f v, log := s.log + 1 }
      else none

/-- The unguarded application of the same writes (what Rust's `apply_set_field` does — it consults
no caveat: `turn/src/executor/apply.rs:520-583`). -/
def runRaw (f : String) : List Int → St → St
  | [],      s => s
  | v :: vs, s => runRaw f vs { rec := set s.rec f v, log := s.log + 1 }

/-- Whole-transition guarded run: apply everything, then check the guard ONCE on `(pre, post)`. -/
def runWhole (R : Int → Int → Bool) (f : String) (vs : List Int) (s : St) : Option St :=
  let s' := runRaw f vs s
  if R (get s.rec f) (get s'.rec f) then some s' else none

/-- **The guard only restricts the DOMAIN — it never changes the post-state.** The model's analog of
`stateStepGuarded_eq` (`EffectsState.lean:~270`) and `stateStepDev_eq` (`:~335`). -/
theorem runPerStep_eq_runRaw (R : Int → Int → Bool) (f : String) :
    ∀ (vs : List Int) (s s' : St), runPerStep R f vs s = some s' → s' = runRaw f vs s := by
  intro vs
  induction vs with
  | nil => intro s s' h; simp [runPerStep] at h; simp [runRaw, h]
  | cons v vs ih =>
      intro s s' h
      simp only [runPerStep] at h
      by_cases hg : R (get s.rec f) v
      · rw [if_pos hg] at h
        simpa [runRaw] using ih _ _ h
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §2 — ABSORPTION FAILS.

`SetField x a ; SetField x b = SetField x b` is not a law in dregg, is not folklore, and is not
true. It fails for TWO INDEPENDENT reasons, exhibited separately below. This matters because
absorption is the ONE equation everyone assumes a write algebra has. -/

/-- A one-field starting state with the slot at `0`. -/
def st0 : St := { rec := [("x", 0)], log := 0 }

/-- **(i) ABSORPTION FAILS ON THE LOG.** Two writes leave a two-row receipt chain; one write leaves
one. The denotation is faithful on the LENGTH of the effect list, so no two effect lists of different
length are ever denotationally equal. This is what makes the tape a tape — and it is exactly why the
free monoid on the verbs does not collapse. (`execFullA_log_suffix`, `PerAsset.lean:2652`.) -/
theorem absorption_fails_on_log :
    (runPerStep Caveat.free.admits "x" [7, 9] st0).map St.log
      ≠ (runPerStep Caveat.free.admits "x" [9] st0).map St.log := by
  decide

/-- **(ii) ABSORPTION FAILS ON THE GUARD** — and in the direction that surprises people: the
COMPOSITE is strictly MORE PERMISSIVE than its last element. Under a `monotonicSeq` slot at `old = 0`,
`[1, 2]` commits and `[2]` alone refuses. So you cannot replace a run of writes by its last write
even up to the log. -/
theorem absorption_fails_on_guard :
    (runPerStep Caveat.monotonicSeq.admits "x" [1, 2] st0).isSome = true
  ∧ (runPerStep Caveat.monotonicSeq.admits "x" [2] st0).isSome = false := by
  constructor <;> decide

/-! ## §3 — ⚑ THE TWO ADMISSION SEMANTICS ARE INCOMPARABLE.

These are the model's form of the two witnesses in §2.3.D of the reckoning. In the deployed system
they would be one action carrying two `SetField`s on one slot of a caveated cell. -/

/-- **Lean admits, Rust refuses.** `monotonicSeq` at `old = 0`, writes `[1, 2]`: each STEP is a
legal `+1`, but the whole transition is `0 → 2`, which is not `old + 1`. -/
theorem perStep_admits_whole_refuses :
    (runPerStep Caveat.monotonicSeq.admits "x" [1, 2] st0).isSome = true
  ∧ (runWhole    Caveat.monotonicSeq.admits "x" [1, 2] st0).isSome = false := by
  constructor <;> decide

/-- **⚑ Rust admits, Lean refuses — the dangerous direction.** `monotonic` at `old = 0`, writes
`[5, 1]`: the second STEP goes DOWN (5 → 1) and the per-write guard refuses, but the whole
transition is `0 → 1`, which is monotone, so a once-per-action check commits it.

If the deployed executor really does admit this, it admits a turn the verified kernel refuses. That
is an authority inversion in the wrong direction for a system whose bar is "the verified artifact IS
the running artifact". ⚑ The reckoning marks this DERIVED-NOT-MEASURED; P0.3 is the differential
test that settles it. -/
theorem whole_admits_perStep_refuses :
    (runPerStep Caveat.monotonic.admits "x" [5, 1] st0).isSome = false
  ∧ (runWhole    Caveat.monotonic.admits "x" [5, 1] st0).isSome = true := by
  constructor <;> decide

/-! ## §4 — TRANSITIVITY IS EXACTLY THE REPAIR (for one direction).

And the two `SlotCaveat` constructors that lack it are exactly the two the divergence lives in:
`monotonicSeq`, and `admitTable` (the arbitrary-relation escape hatch, which is not transitive in
general and is not modelled here because "arbitrary" is the whole point). -/

/-- Transitivity of a `Bool`-valued relation. (Named `TransB` to avoid the core `Transitive`.) -/
def TransB (R : Int → Int → Bool) : Prop :=
  ∀ a b c, R a b = true → R b c = true → R a c = true

/-- The chaining lemma: a committed per-write run of a NON-EMPTY write list relates its endpoints,
provided `R` is transitive. -/
theorem runPerStep_chain (R : Int → Int → Bool) (hT : TransB R) (f : String) :
    ∀ (vs : List Int) (s s' : St), runPerStep R f vs s = some s' →
      vs = [] ∨ R (get s.rec f) (get s'.rec f) = true := by
  intro vs
  induction vs with
  | nil => intro s s' _; exact Or.inl rfl
  | cons v vs ih =>
      intro s s' h
      refine Or.inr ?_
      simp only [runPerStep] at h
      by_cases hg : R (get s.rec f) v
      · rw [if_pos hg] at h
        -- the intermediate state, whose slot reads back exactly `v`
        have hmid : get (set s.rec f v) f = v := get_set_self s.rec f v
        rcases ih { rec := set s.rec f v, log := s.log + 1 } s' h with hnil | hrel
        · -- the tail was empty, so `s'` IS the intermediate state
          subst hnil
          simp only [runPerStep, Option.some.injEq] at h
          subst h
          simpa [hmid] using hg
        · exact hT _ v _ hg (by simpa [hmid] using hrel)
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`perStep_implies_whole` — THE REPAIR.** If the slot's relation is TRANSITIVE, a run the
per-write semantics admits is also admitted by the whole-transition semantics, with the same
post-state. So for a transitive caveat the two layers cannot disagree in this direction. -/
theorem perStep_implies_whole (R : Int → Int → Bool) (hT : TransB R) (f : String)
    (vs : List Int) (s s' : St) (hne : vs ≠ []) (h : runPerStep R f vs s = some s') :
    runWhole R f vs s = some s' := by
  have hraw : s' = runRaw f vs s := runPerStep_eq_runRaw R f vs s s' h
  rcases runPerStep_chain R hT f vs s s' h with hnil | hrel
  · exact absurd hnil hne
  · subst hraw
    simp only [runWhole]
    rw [if_pos hrel]

/-- Six of the eight deployed `SlotCaveat` constructors ARE transitive. Three exhibited. -/
theorem immutable_transB   : TransB Caveat.immutable.admits := by
  intro a b c h₁ h₂; simp [Caveat.admits] at h₁ h₂ ⊢; omega
theorem monotonic_transB   : TransB Caveat.monotonic.admits := by
  intro a b c h₁ h₂; simp [Caveat.admits] at h₁ h₂ ⊢; omega
theorem boundedBy_transB (l h : Int) : TransB (Caveat.boundedBy l h).admits := by
  intro a b c _ h₂; exact h₂

/-- **⚑ `monotonicSeq_not_transitive` — the refutation.** `0 → 1` and `1 → 2` are each legal `+1`
steps; `0 → 2` is not. This single fact is the entire content of
`perStep_admits_whole_refuses`, and it is why the ONE non-transitive structured caveat is the one
where the layers come apart.

Per `feedback-prove-the-floor-false`: the transitivity side-condition in `perStep_implies_whole` is
SATISFIABLE (three witnesses above), REFUTABLE (here), and NOT PROVABLE in general. -/
theorem monotonicSeq_not_transitive : ¬ TransB Caveat.monotonicSeq.admits := by
  intro h
  have hbad := h 0 1 2 (by decide) (by decide)
  exact absurd hbad (by decide)

/-! ## §5 — ⚑ THE DELTA FACTORING, and why it is worth having.

The proposal (§3.2 of the reckoning): a write should carry an element of the slot's declared update
algebra, not a raw value. Read `SlotCaveat` as data about an algebra and five of eight constructors
are "the new value is reachable from the old by an element of a declared monoid of deltas":
`immutable` = `{0}`; `monotonicSeq` = ℕ generated by `+1`; `monotonic` = ℕ under `+`; `boundedBy` = an
interval; `writeOnce` = a two-element poset.

The delta form already EXISTS in the Lean model and is not in the vocabulary:
`Dregg2/Exec/RecordCell.lean:41` `RecOp.addScalar (field : FieldName) (delta : Int)`, applied at
`:65`. `IncrementNonce` is its single monomorphic instance. -/

/-- A slot's declared update algebra: a submonoid of `(ℤ, +)`. -/
structure DeltaMonoid where
  mem      : Int → Bool
  mem_zero : mem 0 = true
  mem_add  : ∀ a b, mem a = true → mem b = true → mem (a + b) = true

/-- One `Act`: apply a delta, if the slot's algebra admits it. -/
def dstep (M : DeltaMonoid) (f : String) (d : Int) (s : St) : Option St :=
  if M.mem d then
    some { rec := set s.rec f (get s.rec f + d), log := s.log + 1 }
  else none

/-- A run of `Act`s. -/
def drun (M : DeltaMonoid) (f : String) : List Int → St → Option St
  | [],      s => some s
  | d :: ds, s => match dstep M f d s with
                  | some s1 => drun M f ds s1
                  | none    => none

/-- **`drun_admits_iff_all` — the compositionality the value form lacks.** A run of `Act`s is
admitted IFF every individual delta is admitted. There is no per-step-vs-whole gap to open: the
admission condition is a property of the multiset of deltas, and by `mem_add` the composite delta of
an admitted run is itself admitted. §3's divergence class cannot be written down. -/
theorem drun_admits_iff_all (M : DeltaMonoid) (f : String) :
    ∀ (ds : List Int) (s : St),
      (drun M f ds s).isSome = true ↔ (∀ d ∈ ds, M.mem d = true) := by
  intro ds
  induction ds with
  | nil => intro s; simp [drun]
  | cons d ds ih =>
      intro s
      by_cases hd : M.mem d = true
      · simp only [drun, dstep, if_pos hd]
        simpa [hd] using ih { rec := set s.rec f (get s.rec f + d), log := s.log + 1 }
      · simp [drun, dstep, hd]

/-- **⚑ `dstep_comm` — SAME-SLOT WRITES COMMUTE under the delta factoring.**

This is the law the deployed executor's permission-effect reordering
(`turn/src/executor/execute_tree.rs:845-848`, `partition(|e| !e.is_permission_effect())`) silently
needs and cannot currently state. Today the reorder is justified by a comment (`:833-840`); under
deltas it would be justified by a theorem.

Note the honest scope: it commutes ON THE RECORD. The `log` is unchanged in length either way but
its CONTENTS would still record the order — the receipt chain is deliberately not commutative, which
is correct (an audit log that forgot the order would be worse). -/
theorem dstep_comm (M : DeltaMonoid) (f : String) (d₁ d₂ : Int) (s : St) :
    (drun M f [d₁, d₂] s).map (fun t => get t.rec f)
      = (drun M f [d₂, d₁] s).map (fun t => get t.rec f) := by
  by_cases h₁ : M.mem d₁ = true <;> by_cases h₂ : M.mem d₂ = true
  · simp only [drun, dstep, if_pos h₁, if_pos h₂, Option.map_some]
    rw [get_set_self, get_set_self, get_set_self, get_set_self]
    omega
  · simp [drun, dstep, h₁, h₂]
  · simp [drun, dstep, h₁, h₂]
  · simp [drun, dstep, h₁, h₂]

/-- **⚑ THE CONTRAST — value writes do NOT commute.** `[1, 2]` leaves `2`; `[2, 1]` leaves `1`.

Put beside `dstep_comm`, this is the whole argument in two theorems: *deltas commute, values do
not.* Every reordering the executor performs is sound for the first and unjustified for the second. -/
theorem setValue_not_comm :
    (runPerStep Caveat.free.admits "x" [1, 2] st0).map (fun t => get t.rec "x")
      ≠ (runPerStep Caveat.free.admits "x" [2, 1] st0).map (fun t => get t.rec "x") := by
  decide

/-! ## §6 — What this file does NOT establish, stated so nobody quotes it as more.

  * It is a MODEL. `St` is not `RecChainedState` (19 kernel fields + a `List Turn` log); `Caveat` is
    not `SlotCaveat` (8 constructors, two of which gate on the actor and one of which is an arbitrary
    finite relation); there is no authority, no membership, no liveness, no cross-cell, no AIR.
  * §3's two divergence theorems are theorems ABOUT THIS MODEL. That the deployed pair diverges the
    same way is a DERIVATION from two definitions (`caveatsAdmit`, `EffectsState.lean:248`;
    `evaluate_cell_program_for_executor`, `execute_tree.rs:175`), not a measurement. P0.3.
  * `perStep_implies_whole` gives ONE direction. The converse (whole ⟹ per-step) is FALSE for almost
    everything including `monotonic` — `whole_admits_perStep_refuses` IS that refutation — so the two
    semantics are genuinely incomparable, not merely differently strict. No amount of transitivity
    fixes that direction; only the delta factoring does.
  * Nothing here is a functor, an adjunction, or a pushout, and nothing here should be named one.
    `runPerStep`/`drun` are partial monoid ACTIONS of a free monoid, exactly as `execFullTurnA` is
    (`execFullTurnA_append`, `PerAsset.lean:2426`). See §3.3 of the reckoning for what is proved,
    what is assumed, and what is refused.
  * ⚑ AND IT HAS NOT BEEN RUN. See the header.
-/

end EffectAlgebraSketch
