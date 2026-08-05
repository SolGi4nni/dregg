/-
# Dregg2.Circuit.Emit.KimchiArena — a variable ALLOCATOR for the kimchi rail that REFUSES reuse

## ⚑ WHAT THIS REPLACES

Authoring a kimchi circuit in this tree means writing `PVar.internal 0`, `PVar.internal 1`,
`PVar.external 0` **by hand** into a `PGate.permVars` list. Nothing checks that two roles got
different ids. The tree has already paid for that: `KimchiStepMainCore`'s `exposedVars` once gave
two of Step's 67 public words the SAME variable, and it was invisible because the smoke shape's
`take 12` cut before the collision. §5 re-enacts that bug and shows this allocator refusing it.

`KimchiStepMainCore.lean:3317`'s `AOp`/`AM` is the closest thing the tree had — but it is a
`StateM` namespaced inside `step_main`, it allocates only `xv (base + i)` (one flat `external`
space, no `internal` side), and a slot index is still a bare `Nat` the author computes.

## ⚑ THE CIRCUIT IS STILL A VALUE — AND THE ALLOCATOR IS NOT A MONAD

`KimchiPreimageCircuit`'s whole advantage is that `preimagePlaced` is a closed `def` twelve
theorems read by `decide`, against a control `unboundPlaced` that is *another value*. A `StateM`
allocator would put the circuit behind a `run`, and `decide` does not reach through one usefully.

So allocation here is **a pure fold over a list of claims** (`allocFrom`), not a state monad. It
loses nothing: `Claim.ext`/`Claim.int` hand out the next free id exactly as a `StateM` `fresh`
would, and the result is an `Arena` — an ordinary value that `decide` computes through. §6 proves
the point at a real circuit: the arena-authored `KimchiPreimageCircuit` gate list is `rfl`-equal to
the hand-picked one.

## ⚑ NAMES ARE A TYPE, NOT A STRING

`Arena` is parameterised by the author's own slot type `σ`. Use a `deriving DecidableEq` enum and a
misspelled slot is an **elaboration error**, not a runtime miss; exhaustiveness over the slots is
`decide`-able because the enum is finite. `String` works too and is strictly weaker.

## ⚑ THE HARD PART: DETECTING AN *UNINTENTIONAL* ALIAS ONCE MERGING EXISTS

A merge primitive (`assertEqual`/`mergeRoots`, the zero-row union-find over `PVar` that composes
into `circuitPositions`) makes aliasing INTENTIONAL, so "two cells share a copy class" stops being
evidence of a bug. The answer is not a smarter detector; it is that the three ways two cells can
land in one class become **type-distinct**, and only one of them was ever silent:

1. **By NAME** — the author wrote the same slot in two cells. Visible in the source, intended.
2. **By MERGE** — an explicit `assertEqual a b` edge unions two distinct slots. Visible in the
   merge list, intended.
3. **By ID COLLISION** — two distinct slots resolve to the same `PVar`. *This is the silent one,
   and it is the `exposedVars` bug.*

`alloc_injective` (§3) kills (3) **generally, for every claim list** — not per-instance: a
successful `alloc` has `Nodup` variables, so distinct slots never share a `PVar`. What remains is
that a circuit might use a `PVar` the arena never handed out (a hand-picked id smuggled back in, or
a slot that failed to resolve). `Arena.closes` (§4) is the decidable check for that, over `place`'s
own input positions.

⚑ **AND THE COUNT ALONE IS NOT ENOUGH ONCE MERGING EXISTS**, which is the part worth saying
plainly. `KimchiAssertEqual` landed the zero-row `assertEqual` as a RENAME of `PVar`s composed into
`circuitPositions`, so a merge LOWERS the emitted distinct-variable count — exactly as an
unintentional alias does. The two are separated by **attribution**, not by the count:

> emitted distinct variables **+** arena variables the merge list absorbed **=** allocated variables

`circuitVarCount` (§4) is one side of that; `KimchiConditionalCircuit` §3b assembles the whole
equation and exhibits the pair that settles it — an intentional merge and an unintentional alias
with the SAME emitted variable count and opposite verdicts. **So the answer to "can an
unintentional alias still be detected once merging exists" is yes**, and it is a theorem over the
emitted object rather than a convention.

⚠ Two honest limits. First, `alloc_injective` is a theorem about the ARENA; it says nothing about a
gate list that ignores the arena and writes `.internal 0` inline — `Arena.closes` catches that, *but
only if someone states it.* This file makes the check one `decide` away; it cannot make a circuit
run it. Second, the ledger detects an alias the merge list does not explain; it **cannot** detect a
*wrong* merge — an `assertEqual` the author wrote and should not have. That is a claim about intent
and no allocator reaches it.
-/
import Dregg2.Tactics
import Dregg2.Circuit.Emit.KimchiPlacement

namespace Dregg2.Circuit.Emit.KimchiArena

open Dregg2.Circuit.Emit.KimchiPlacement

set_option autoImplicit false

/-! ## §1 — claims, refusals, the arena. -/

/-- One allocation request. `ext`/`int` take the next free id on their OWN side; `extAt`/`intAt`
pin a specific id — the migration path for an existing hand-picked layout, and the operation that
can REFUSE. -/
inductive Claim (σ : Type) where
  /-- A fresh `external` (witness / public-input) variable, bound to slot `n`. -/
  | ext   : σ → Claim σ
  /-- A fresh `internal` (auxiliary reduction) variable, bound to slot `n`. -/
  | int   : σ → Claim σ
  /-- `external i`, bound to slot `n`. **Refuses if `external i` is already bound.** -/
  | extAt : σ → Nat → Claim σ
  /-- `internal i`, bound to slot `n`. **Refuses if `internal i` is already bound.** -/
  | intAt : σ → Nat → Claim σ
  deriving Repr, DecidableEq

/-- Why an allocation was REFUSED. Both are refusals, not aliases. -/
inductive AllocErr (σ : Type) where
  /-- The slot already denotes a variable. -/
  | nameTaken : σ → AllocErr σ
  /-- ⚑ **The collision this file exists for**: a second slot asked for a variable already handed
  out. This is `exposedVars`' bug, as an error value. -/
  | varTaken  : σ → PVar → AllocErr σ
  deriving Repr, DecidableEq

/-- The allocation state. `nExt`/`nInt` are HIGH-WATER MARKS — strictly above every id handed out
on their side (`Wf.extLt`/`Wf.intLt`), which is why a `fresh` claim can never collide. -/
structure Arena (σ : Type) where
  /-- Slot → variable, most recent first. -/
  bind : List (σ × PVar) := []
  nExt : Nat := 0
  nInt : Nat := 0
  deriving Repr, DecidableEq

variable {σ : Type}

/-- The bound slots. -/
def Arena.names (a : Arena σ) : List σ := a.bind.map Prod.fst

/-- The variables handed out. -/
def Arena.vars (a : Arena σ) : List PVar := a.bind.map Prod.snd

/-- Is `v` already handed out? ⚠ Spelled with `decide (w = v)` rather than `v ∈ a.vars`:
`KimchiPlacement`'s `PVar` derives `BEq` alongside `DecidableEq` and carries no `LawfulBEq`, so
`∈` is not decidable on it. This routes through `DecidableEq` instead of adding an orphan instance
to a file that is not ours. -/
def Arena.hasVar (a : Arena σ) (v : PVar) : Bool := a.vars.any (fun w => decide (w = v))

theorem hasVar_iff (a : Arena σ) (v : PVar) : a.hasVar v = true ↔ v ∈ a.vars := by
  simp only [Arena.hasVar, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨_, hw, he⟩ => he ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩

/-- Is slot `n` already bound? -/
def Arena.hasName [DecidableEq σ] (a : Arena σ) (n : σ) : Bool :=
  a.names.any (fun m => decide (m = n))

theorem hasName_iff [DecidableEq σ] (a : Arena σ) (n : σ) : a.hasName n = true ↔ n ∈ a.names := by
  simp only [Arena.hasName, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨_, hw, he⟩ => he ▸ hw, fun hv => ⟨n, hv, rfl⟩⟩

/-- Bind slot `n` to variable `v` and set the counters, or REFUSE. Both checks are refusals: a
repeat slot and a repeat variable are errors, never a silent overwrite and never a silent alias. -/
def Arena.bindAt [DecidableEq σ] (a : Arena σ) (n : σ) (v : PVar) (ne ni : Nat) :
    Except (AllocErr σ) (Arena σ) :=
  if a.hasName n then .error (.nameTaken n)
  else if a.hasVar v then .error (.varTaken n v)
  else .ok { bind := (n, v) :: a.bind, nExt := ne, nInt := ni }

/-- One claim. ⚠ `external`/`internal` are SEPARATED: two counters, two id spaces, and a claim
names its side. `external 3` and `internal 3` are different variables and neither blocks the
other. -/
def step [DecidableEq σ] (a : Arena σ) : Claim σ → Except (AllocErr σ) (Arena σ)
  | .ext n     => a.bindAt n (.external a.nExt) (a.nExt + 1) a.nInt
  | .int n     => a.bindAt n (.internal a.nInt) a.nExt (a.nInt + 1)
  | .extAt n i => a.bindAt n (.external i) (max a.nExt (i + 1)) a.nInt
  | .intAt n i => a.bindAt n (.internal i) a.nExt (max a.nInt (i + 1))

/-- The fold. Pure, structural, total — no monad reaches the circuit. -/
def allocFrom [DecidableEq σ] (a : Arena σ) : List (Claim σ) → Except (AllocErr σ) (Arena σ)
  | []      => .ok a
  | c :: cs => (step a c).bind (fun a' => allocFrom a' cs)

/-- **THE ALLOCATOR.** A claim list in, an arena or a REFUSAL out. -/
def alloc [DecidableEq σ] (cs : List (Claim σ)) : Except (AllocErr σ) (Arena σ) :=
  allocFrom {} cs

/-! ## §2 — the well-formedness invariant. -/

/-- The arena invariant: slots distinct, variables distinct, and each counter strictly above every
id handed out on its side. -/
structure Wf (a : Arena σ) : Prop where
  names : a.names.Nodup
  vars  : a.vars.Nodup
  extLt : ∀ i, PVar.external i ∈ a.vars → i < a.nExt
  intLt : ∀ i, PVar.internal i ∈ a.vars → i < a.nInt

theorem wf_empty : Wf ({} : Arena σ) where
  names := by simp [Arena.names]
  vars  := by simp [Arena.vars]
  extLt := by simp [Arena.vars]
  intLt := by simp [Arena.vars]

theorem bindAt_ok [DecidableEq σ] {a b : Arena σ} {n : σ} {v : PVar} {ne ni : Nat}
    (h : a.bindAt n v ne ni = .ok b) :
    n ∉ a.names ∧ v ∉ a.vars ∧ b = { bind := (n, v) :: a.bind, nExt := ne, nInt := ni } := by
  unfold Arena.bindAt at h
  have h1 : a.hasName n = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc; rw [hc] at h; simp at h
  have h2 : a.hasVar v = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc; rw [h1, hc] at h; simp at h
  rw [h1, h2] at h
  simp only [Bool.false_eq_true, if_false] at h
  refine ⟨fun hc => ?_, fun hc => ?_, ?_⟩
  · rw [(hasName_iff a n).2 hc] at h1; exact Bool.noConfusion h1
  · rw [(hasVar_iff a v).2 hc] at h2; exact Bool.noConfusion h2
  · injection h with h; exact h.symm

/-- ⚑ **THE ONE INVARIANT STEP**, used by all four claim forms. The two `fresh` forms discharge
`hex`/`hin` from the high-water mark; the two pinned forms discharge them from the `max`. -/
theorem wf_bindAt [DecidableEq σ] {a b : Arena σ} {n : σ} {v : PVar} {ne ni : Nat}
    (h : Wf a) (hb : a.bindAt n v ne ni = .ok b) (hne : a.nExt ≤ ne) (hni : a.nInt ≤ ni)
    (hex : ∀ i, v = PVar.external i → i < ne)
    (hin : ∀ i, v = PVar.internal i → i < ni) : Wf b := by
  obtain ⟨hn, hv, rfl⟩ := bindAt_ok hb
  have hnm : ∀ x : σ, x ∈ ({ bind := (n, v) :: a.bind, nExt := ne, nInt := ni } : Arena σ).names
      ↔ (x = n ∨ x ∈ a.names) := by intro x; simp [Arena.names]
  have hvm : ∀ x : PVar, x ∈ ({ bind := (n, v) :: a.bind, nExt := ne, nInt := ni } : Arena σ).vars
      ↔ (x = v ∨ x ∈ a.vars) := by intro x; simp [Arena.vars]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Arena.names] using List.nodup_cons.2 ⟨by simpa [Arena.names] using hn, h.names⟩
  · simpa [Arena.vars] using List.nodup_cons.2 ⟨by simpa [Arena.vars] using hv, h.vars⟩
  · intro i hi
    show i < ne
    rcases (hvm _).1 hi with hi | hi
    · exact hex i hi.symm
    · have := h.extLt i hi; omega
  · intro i hi
    show i < ni
    rcases (hvm _).1 hi with hi | hi
    · exact hin i hi.symm
    · have := h.intLt i hi; omega

/-- Every successful step preserves the invariant. ⚑ The two `fresh` cases never trip the variable
check — the high-water mark is exactly what makes that true. -/
theorem step_wf [DecidableEq σ] {a b : Arena σ} {c : Claim σ} (h : Wf a) (hs : step a c = .ok b) :
    Wf b := by
  cases c with
  | ext n =>
    exact wf_bindAt h hs (by omega) (by omega)
      (fun i hi => by injection hi with hi; omega) (fun i hi => by simp at hi)
  | int n =>
    exact wf_bindAt h hs (by omega) (by omega)
      (fun i hi => by simp at hi) (fun i hi => by injection hi with hi; omega)
  | extAt n j =>
    exact wf_bindAt h hs (by omega) (by omega)
      (fun i hi => by injection hi with hi; omega) (fun i hi => by simp at hi)
  | intAt n j =>
    exact wf_bindAt h hs (by omega) (by omega)
      (fun i hi => by simp at hi) (fun i hi => by injection hi with hi; omega)

theorem allocFrom_wf [DecidableEq σ] {cs : List (Claim σ)} :
    ∀ {a b : Arena σ}, Wf a → allocFrom a cs = .ok b → Wf b := by
  induction cs with
  | nil => intro a b h hr; simp only [allocFrom, Except.ok.injEq] at hr; exact hr ▸ h
  | cons c cs ih =>
    intro a b h hr
    simp only [allocFrom] at hr
    cases hstep : step a c with
    | error e => rw [hstep] at hr; simp [Except.bind] at hr
    | ok a'   => rw [hstep] at hr; simp only [Except.bind] at hr; exact ih (step_wf h hstep) hr

/-! ## §3 — ⚑ THE PROPERTY: a successful allocation cannot alias.

General over every claim list, not `decide`d per instance. -/

theorem alloc_wf [DecidableEq σ] {cs : List (Claim σ)} {a : Arena σ} (h : alloc cs = .ok a) :
    Wf a := allocFrom_wf wf_empty h

/-- The variables handed out are pairwise distinct. -/
theorem alloc_vars_nodup [DecidableEq σ] {cs : List (Claim σ)} {a : Arena σ}
    (h : alloc cs = .ok a) : a.vars.Nodup := (alloc_wf h).vars

/-- The slots bound are pairwise distinct, so `find?` is unambiguous. -/
theorem alloc_names_nodup [DecidableEq σ] {cs : List (Claim σ)} {a : Arena σ}
    (h : alloc cs = .ok a) : a.names.Nodup := (alloc_wf h).names

/-- ⚑ **NO UNINTENTIONAL ALIAS.** Two slots that denote the same variable ARE the same slot — for
every claim list that `alloc` accepts. This is the general theorem `exposedVars` did not have, and
it is what leaves an explicit `assertEqual` merge as the ONLY other way two cells share a copy
class. -/
theorem alloc_injective [DecidableEq σ] {cs : List (Claim σ)} {a : Arena σ}
    (h : alloc cs = .ok a) {n₁ n₂ : σ} {v : PVar}
    (h₁ : (n₁, v) ∈ a.bind) (h₂ : (n₂, v) ∈ a.bind) : n₁ = n₂ := by
  have hnd : (a.bind.map Prod.snd).Nodup := alloc_vars_nodup h
  exact congrArg Prod.fst (List.inj_on_of_nodup_map hnd h₁ h₂ rfl)

/-- The dual: a slot denotes at most one variable. -/
theorem alloc_functional [DecidableEq σ] {cs : List (Claim σ)} {a : Arena σ}
    (h : alloc cs = .ok a) {n : σ} {v₁ v₂ : PVar}
    (h₁ : (n, v₁) ∈ a.bind) (h₂ : (n, v₂) ∈ a.bind) : v₁ = v₂ := by
  have hnd : (a.bind.map Prod.fst).Nodup := alloc_names_nodup h
  exact congrArg Prod.snd (List.inj_on_of_nodup_map hnd h₁ h₂ rfl)

/-! ## §4 — reading the arena, and the ledger the merge seam cannot blur. -/

/-- Slot → variable. Unambiguous by `alloc_functional`. -/
def Arena.find? [DecidableEq σ] (a : Arena σ) (n : σ) : Option PVar :=
  (a.bind.find? (fun p => p.1 == n)).map Prod.snd

/-- An id no `ext`/`int` claim reaches, so an UNBOUND slot resolves to something conspicuous rather
than onto a real variable. It is not a safety mechanism on its own — `closes` is. -/
def POISON : Nat := 0xD0D0DEAD

/-- The variable an unbound slot resolves to. -/
def poison : PVar := .external POISON

/-- Total lookup. ⚠ An unbound slot yields `poison`; `Arena.closes` is what turns that into a
refusal at the emitted object. -/
def Arena.v [DecidableEq σ] (a : Arena σ) (n : σ) : PVar := (a.find? n).getD poison

/-- Every slot in `ns` resolves. Over a finite `deriving DecidableEq` slot enum this is a
`decide` away and it is the exhaustiveness check a `String`-keyed allocator cannot offer. -/
def Arena.covers [DecidableEq σ] (a : Arena σ) (ns : List σ) : Bool :=
  ns.all (fun n => (a.find? n).isSome)

/-- ⚑ **THE CLOSURE CHECK.** Every variable the circuit's placement positions mention was handed
out by this arena. Goes false if a hand-picked `.internal 0` was written inline, and false if a
slot failed to resolve (`poison` is not in `a.vars`). -/
def Arena.closes [DecidableEq σ] (a : Arena σ) (poss : List (PVar × Cell)) : Bool :=
  (poss.map Prod.fst).all (fun v => a.vars.contains v)

/-- ⚑ **THE ALIAS LEDGER.** How many DISTINCT variables the emitted circuit actually contains —
which is, before any merge, exactly how many copy-permutation classes `place` will build. An
unintentional alias shows up here as a count that is one lower than the arena's, and it is read off
`circuitPositions`, not off the author's intent. -/
def circuitVarCount (pubSize : Nat) (gates : List PGate) : Nat :=
  ((circuitPositions pubSize gates).map Prod.fst).dedup.length

/-- The arena's own count, for the ledger's other side. -/
def Arena.size (a : Arena σ) : Nat := a.bind.length

/-! ## §5 — ⚑ THE REFUSAL BITES: `exposedVars`' bug, re-enacted.

A refusal that is only ever satisfied is decoration. These two are the same claim list up to one
index, and `alloc` splits them. -/

/-- A three-word public-input layout, as a slot enum. -/
inductive PubWord where
  | w0 | w1 | w2
  deriving Repr, DecidableEq

/-- The layout an author MEANT: three public words at externals 0, 1, 2. -/
def goodWords : List (Claim PubWord) := [.extAt .w0 0, .extAt .w1 1, .extAt .w2 2]

/-- ⚑ **THE BUG.** `exposedVars`' index arithmetic gave two public words the same variable. Here
`w2` asks for `external 1` again. Under hand-picked ids this is a silent alias — the two words
become ONE copy class and the circuit stops distinguishing them. -/
def collidingWords : List (Claim PubWord) := [.extAt .w0 0, .extAt .w1 1, .extAt .w2 1]

/-- The good layout allocates. -/
theorem goodWords_allocates :
    (alloc goodWords).isOk = true := by decide

/-- ⚑ **AND THE COLLISION IS REFUSED** — named, with the variable that was already taken. Not an
alias, not a silent overwrite: an error value. -/
theorem collidingWords_refused :
    alloc collidingWords = .error (.varTaken .w2 (.external 1)) := by decide

/-- A repeated SLOT is refused too — the other half of the same discipline. -/
theorem repeatedSlot_refused :
    alloc [Claim.extAt PubWord.w0 0, Claim.extAt PubWord.w0 1]
      = .error (.nameTaken .w0) := by decide

/-- ⚠ `external`/`internal` are SEPARATE spaces: id 0 on each side is fine, and neither claim
blocks the other. -/
theorem sides_are_separated :
    (alloc [Claim.extAt PubWord.w0 0, Claim.intAt PubWord.w1 0]).isOk = true := by decide

/-- A `fresh` claim after a pinned one cannot collide with it — the high-water mark, at an
instance. (`step_wf`'s `extLt` is the general fact.) -/
theorem fresh_skips_the_pinned_id :
    ((alloc [Claim.extAt PubWord.w0 5, Claim.ext PubWord.w1]).toOption.map
      (fun a => a.v .w1)) = some (.external 6) := by decide

#assert_axioms alloc_injective
#assert_axioms alloc_functional
#assert_axioms alloc_vars_nodup
#assert_axioms collidingWords_refused
#assert_axioms repeatedSlot_refused
#assert_axioms sides_are_separated

end Dregg2.Circuit.Emit.KimchiArena
