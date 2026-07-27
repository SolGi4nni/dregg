/-
  Pancake/Lower.lean — Seam L of the pivot (PANCAKE-IN-LEAN-DESIGN §"TWO SEAMS").

  `lower : Dsl.EmitPancake.PFun → Option Pancake.PancakeProg` maps the emitter's
  subset AST (the thing `ppFun` pretty-prints to `.pnk`) into the real panLang
  subset modelled in Pancake/Sem.lean. The obligation this seam owes is that
  `lower` agrees with `cake`'s own parse of `ppFun f` — i.e. `lower f = some
  (parse (ppFun f))` on the modelled fragment. That is checked structurally on
  hbox (see PANCAKE-IN-LEAN report §Lower): the concrete AST `#eval (lower
  (emitRegion regionC0))` is compared against the `panPtreeConversion` output of
  the emitted `region.pnk`.

  PARTIALITY (why `Option`). The emitter's `PExpr`/`PStmt` cover a WIDER surface
  than the modelled panLang fragment of Pancake/Sem.lean. The first-order
  arithmetic/relational ops the fused-serve stages added — `== <= -`
  (`POp.eq`/`le`/`sub`) — are now MODELLED (Sem.lean `Cmp Equal`/`NotLess`,
  `Op Sub`) and so lower to `some`; the byte store `st8` (`PStmt.storeb`) is now
  MODELLED too (Sem.lean `StoreByte`, `mem_store_byte`) and lowers to
  `some (.storeByte …)`. What remains outside the model is the intra-program call
  `var r = f(..)` (`PStmt.call`): Sem.lean deliberately models ONLY this
  first-order, sans-IO fragment (its header lists `Call`/… as NOT modelled — the
  honest emission surface). So `lower` is still a PARTIAL map: it lowers the
  modelled constructs and returns `none` on `call`, rather than fabricating a
  semantics for it. `emitRegion regionC0` uses only modelled constructs, so
  `lower (emitRegion regionC0) = some prog`.

  The two nestings this seam gets right (the substantive content):
   * a `.pnk` statement LIST folds to a RIGHT nest — `s1; s2; s3` parses to
     `Seq s1 (Seq s2 s3)`; a `var x = e;` before `rest` parses to `Dec x e rest`
     (the `Dec` SCOPES over the continuation, panLang `Dec v sh e prog`).
   * `lds 1 a` is `Load One a` (shape One = one word); `ld8 a` is `LoadByte a`.
-/
import Pancake.Sem
import Dsl.EmitPancake

namespace Pancake.Lower

open Dsl.EmitPancake (PExpr PStmt PFun POp emitRegion regionC0)
open Pancake

/-- Lower an emitter expression to a modelled panLang expression, partially.
`POp.mul` is `Panop Mul`; `POp.lt` is `Cmp Less` (SIGNED); `POp.add`/`and_` are
`Op Add`/`Op And`. `loadw` (only `shape = 1` in the region) is `Load One`. The
fused-serve operators lower faithfully to their parse: `POp.eq` (`==`) to
`Cmp Equal a b`; `POp.le` (`<=`) to `Cmp NotLess b a` — the parser SWAPS the
operands (`conv_cmp`: `LeqT ↦ (NotLess, swap)`), so `a <= b ≡ ¬(b < a)`;
`POp.sub` (`-`) to `Op Sub [a;b]`. -/
def lowerExp : PExpr → Option PancakeExp
  | .base        => some .base
  | .const n     => some (.const (BitVec.ofNat 64 n))
  | .var s       => some (.var s)
  | .binop op l r =>
    match lowerExp l, lowerExp r with
    | some a, some b =>
      match op with
      | .add  => some (.op .add a b)
      | .and_ => some (.op .and_ a b)
      | .mul  => some (.mul a b)
      | .lt   => some (.cmp .less a b)
      | .eq   => some (.cmp .equal a b)     -- `a == b` parses to `Cmp Equal a b`
      | .le   => some (.cmp .notLess b a)   -- `a <= b` parses to `Cmp NotLess b a` (parser SWAPS operands)
      | .sub  => some (.op .sub a b)        -- `a - b` parses to `Op Sub [a;b]`
    | _, _ => none
  | .loadw _ a   =>                             -- region uses shape = 1 = `One`
    match lowerExp a with
    | some a' => some (.loadWord a')
    | none    => none
  | .loadb a     =>
    match lowerExp a with
    | some a' => some (.loadByte a')
    | none    => none

mutual
/-- Lower a single non-`dec` statement (the `dec` scoping is handled by
`lowerStmtsFold`, which threads the continuation). Returns `none` on the
serve-only constructs `storeb`/`call`, which the Sem model does not cover. -/
def lowerStmt1 : PStmt → Option PancakeProg
  | .dec n v    =>                          -- `dec` as a trailing stmt (unused by region)
    match lowerExp v with
    | some v' => some (.dec n v' .skip)
    | none    => none
  | .assign n v =>
    match lowerExp v with
    | some v' => some (.assign n v')
    | none    => none
  | .store a v  =>
    match lowerExp a, lowerExp v with
    | some a', some v' => some (.store a' v')
    | _, _             => none
  | .storeb a v  =>                         -- `st8 addr, val;` lowers to `StoreByte addr val`
    match lowerExp a, lowerExp v with
    | some a', some v' => some (.storeByte a' v')
    | _, _             => none
  | .ffi name (c :: cl :: a :: al :: _) =>
    match lowerExp c, lowerExp cl, lowerExp a, lowerExp al with
    | some c', some cl', some a', some al' => some (.extCall name c' cl' a' al')
    | _, _, _, _                           => none
  | .ffi name _ => some (.extCall name .base .base .base .base)  -- region ffi always 4 args
  | .call _ _ _ => none                     -- `var r = f(..)`: outside the modelled subset
  | .ret v      =>
    match lowerExp v with
    | some v' => some (.ret v')
    | none    => none
  | .ite c t e  =>
    match lowerExp c, lowerStmtsFold t, lowerStmtsFold e with
    | some c', some t', some e' => some (.cond c' t' e')
    | _, _, _                   => none
  | .while c b  =>
    match lowerExp c, lowerStmtsFold b with
    | some c', some b' => some (.while_ c' b')
    | _, _             => none
/-- Fold a `.pnk` statement list into the right-nested `Dec`/`Seq` structure the
Pancake parser produces. -/
def lowerStmtsFold : List PStmt → Option PancakeProg
  | []            => some .skip
  | [s]           => lowerStmt1 s
  | (.dec n v) :: rest =>
    match lowerExp v, lowerStmtsFold rest with
    | some v', some r' => some (.dec n v' r')
    | _, _             => none
  | s :: rest     =>
    match lowerStmt1 s, lowerStmtsFold rest with
    | some s', some r' => some (.seq s' r')
    | _, _             => none
end

/-- Lower a whole emitter function (partial: `none` if any construct is outside
the modelled Pancake fragment). -/
def lower (f : PFun) : Option PancakeProg := lowerStmtsFold f.body

/-- The region program, lowered from the canonical C0 spec — the concrete
`PancakeProg` the emit-correctness theorem runs. The region uses only modelled
constructs, so this is `some prog`. -/
def regionProg : Option PancakeProg := lower (emitRegion regionC0)

/-! ### Totality of `lowerExp` on the fused-serve first-order ops.

`lowerExp` now returns `some` (no longer `none`) on `POp.eq`/`le`/`sub` whenever
both operands lower, mapping each to the Sem construct its parse produces. -/

theorem lowerExp_eq_some {l r : PExpr} {a b : PancakeExp}
    (hl : lowerExp l = some a) (hr : lowerExp r = some b) :
    lowerExp (.binop .eq l r) = some (.cmp .equal a b) := by
  simp only [lowerExp, hl, hr]

theorem lowerExp_le_some {l r : PExpr} {a b : PancakeExp}
    (hl : lowerExp l = some a) (hr : lowerExp r = some b) :
    lowerExp (.binop .le l r) = some (.cmp .notLess b a) := by
  simp only [lowerExp, hl, hr]

theorem lowerExp_sub_some {l r : PExpr} {a b : PancakeExp}
    (hl : lowerExp l = some a) (hr : lowerExp r = some b) :
    lowerExp (.binop .sub l r) = some (.op .sub a b) := by
  simp only [lowerExp, hl, hr]

/-- Totality of `lowerStmt1` on the byte store `st8`: whenever both the address
and value expressions lower, `storeb` lowers (no longer `none`) to the modelled
`StoreByte`. -/
theorem lowerStmt1_storeb_some {a v : PExpr} {a' v' : PancakeExp}
    (ha : lowerExp a = some a') (hv : lowerExp v = some v') :
    lowerStmt1 (.storeb a v) = some (.storeByte a' v') := by
  simp only [lowerStmt1, ha, hv]

end Pancake.Lower
