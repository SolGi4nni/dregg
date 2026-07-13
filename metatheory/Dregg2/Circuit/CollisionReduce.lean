import Dregg2.Circuit.CommitmentReduction

/-!
# Infrastructure for the collision-reduction campaign: the "sound-unless-broken" monad

The de-vacuation campaign replaces every injectivity use (`sponge xs = sponge ys → xs = ys`, false at
real params) with its reduction form: the conclusion holds UNLESS the adversary produced a concrete
hash collision. Every binding layer threads the same `Or`-plumbing, so we mechanize it once here.

`OrBreak Break P` := "`P`, unless a `Break` (a concrete collision) was found". It is a monad over the
good branch `P` with `Break` as the sticky error — exactly `Except Break` at the `Prop` level. The
combinators (`imp`, `bind`, `map₂`, `weaken`, `resolve`) let a proof mirror its injective-form original
step for step, swapping each injectivity appeal for a `*_orBreak` leaf and letting the collision branch
propagate untouched. `weaken` injects a per-hash break into a coarser apex break, so lanes over
different commitment hashes compose into one `LightClientBreak`. `resolve` recovers the original
injective statement (`¬Break ⇒ P`), so nothing downstream is lost.
-/

namespace Dregg2.Circuit.CollisionReduce

open Dregg2.Circuit.CommitmentReduction
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ)

/-- A concrete collision of a sponge hash `List ℤ → ℤ`. -/
def SpongeCollision (sponge : List ℤ → ℤ) : Prop :=
  ∃ xs ys : List ℤ, xs ≠ ys ∧ sponge xs = sponge ys

/-- A concrete collision of a 2-to-1 combiner `ℤ → ℤ → ℤ`. -/
def CompressCollision (h : ℤ → ℤ → ℤ) : Prop :=
  ∃ p q : ℤ × ℤ, p ≠ q ∧ h p.1 p.2 = h q.1 q.2

/-- **The reduction dichotomy**: the good conclusion `P` holds, unless a `Break` (a concrete hash
collision) was produced. The 'sound-unless-broken' monad. -/
abbrev OrBreak (Break P : Prop) : Prop := P ∨ Break

variable {Break Break' P Q R : Prop}

/-- Inject the good conclusion. -/
theorem OrBreak.ok (h : P) : OrBreak Break P := Or.inl h

/-- Inject a break. -/
theorem OrBreak.broke (h : Break) : OrBreak Break P := Or.inr h

/-- Map the good branch (the collision branch passes through untouched). -/
theorem OrBreak.imp (f : P → Q) (x : OrBreak Break P) : OrBreak Break Q := Or.imp_left f x

/-- Chain: feed the good result into the next dichotomy; a break anywhere is sticky. -/
theorem OrBreak.bind (x : OrBreak Break P) (f : P → OrBreak Break Q) : OrBreak Break Q :=
  Or.elim x f Or.inr

/-- Combine two dichotomies over the same break — both good branches feed a binary conclusion. -/
theorem OrBreak.map₂ (f : P → Q → R) (x : OrBreak Break P) (y : OrBreak Break Q) : OrBreak Break R :=
  OrBreak.bind x (fun p => OrBreak.imp (f p) y)

/-- Weaken the break event: a per-hash break injects into a coarser (apex) break. -/
theorem OrBreak.weaken (g : Break → Break') (x : OrBreak Break P) : OrBreak Break' P :=
  Or.imp_right g x

/-- Recover the injective statement: if no break is possible, the good branch holds. -/
theorem OrBreak.resolve (hNo : ¬ Break) (x : OrBreak Break P) : P :=
  Or.elim x id (fun b => absurd b hNo)

/-! ## Leaf producers — the binding bricks, repackaged as `OrBreak` -/

/-- **Merkle opening** as an `OrBreak` leaf: the opened value binds, unless a sponge collision. -/
theorem opening_orBreak (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    OrBreak (SpongeCollision sponge) (vOpened = vCommitted) :=
  commitmentOpening_binds_or_collision sponge hCommitted hOpened

/-- **2-to-1 combiner** as an `OrBreak` leaf: the arguments bind, unless a combiner collision. -/
theorem compress_orBreak (h : ℤ → ℤ → ℤ) {a b c d : ℤ} (heq : h a b = h c d) :
    OrBreak (CompressCollision h) (a = c ∧ b = d) :=
  compress_binds_or_collision h heq

/-- A concrete collision of a keyed leaf hash `CH : α → β → ℤ` — same index, distinct values. -/
def CellCollision {α β : Type} (CH : α → β → ℤ) : Prop :=
  ∃ (c : α) (v w : β), v ≠ w ∧ CH c v = CH c w

/-- **Leaf hash** as an `OrBreak` leaf: the value binds, unless a leaf collision (the `cellLeafInjective`
`CommitSurface` carrier, de-vacuated). -/
theorem cellLeaf_orBreak {α β : Type} (CH : α → β → ℤ) {c : α} {v w : β} (heq : CH c v = CH c w) :
    OrBreak (CellCollision CH) (v = w) := by
  by_cases h : v = w
  · exact Or.inl h
  · exact Or.inr ⟨c, v, w, h, heq⟩

/-- **Sponge over a list** (`compressN`) as an `OrBreak` leaf: the lists bind, unless a sponge collision
(the `compressNInjective` `CommitSurface` carrier, de-vacuated). -/
theorem spongeN_orBreak (hN : List ℤ → ℤ) {xs ys : List ℤ} (heq : hN xs = hN ys) :
    OrBreak (SpongeCollision hN) (xs = ys) := by
  by_cases h : xs = ys
  · exact Or.inl h
  · exact Or.inr ⟨xs, ys, h, heq⟩

/-! ## Non-vacuity: the infra is load-bearing, not just plumbing -/

/-- `resolve` inverts `ok`: with no break, the good branch is recovered verbatim. -/
theorem OrBreak.resolve_ok (hNo : ¬ Break) (h : P) :
    OrBreak.resolve hNo (OrBreak.ok (Break := Break) h) = h := rfl

/-- A break genuinely blocks `resolve` — `resolve` is not vacuously total. -/
theorem OrBreak.no_resolve_of_break (hb : Break) : ¬ ∃ _ : ¬ Break, True :=
  fun ⟨hNo, _⟩ => hNo hb

#assert_axioms OrBreak.imp
#assert_axioms OrBreak.bind
#assert_axioms OrBreak.map₂
#assert_axioms OrBreak.weaken
#assert_axioms OrBreak.resolve
#assert_axioms opening_orBreak
#assert_axioms compress_orBreak
#assert_axioms cellLeaf_orBreak
#assert_axioms spongeN_orBreak

end Dregg2.Circuit.CollisionReduce
