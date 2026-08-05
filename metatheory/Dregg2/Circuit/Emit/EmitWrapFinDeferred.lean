/-
# EmitWrapFinDeferred — print the three deferred words `KimchiWrapMainField` §15c‴ memoises.

⚑ **THIS IS THE MEMO'S BOOTSTRAP, NOT A SECOND SOURCE.** `FIN_DEFERRED_CIP` / `_B` / `_XI` are the
`combined_inner_product`, `b` and `xi` of the block that claims `should_finalize`, as §20's own
program and sponge compute them. The constants cannot be typed in from nothing, so this driver
prints what `finSpDerivedWords` returns; the OBLIGATION that the constants ARE that triple is
discharged by `fin_deferred_words_are_the_derivation` (kernel, `rfl`) and by `EmitWrapMainJson`'s
refusal, not by this file.

    cd metatheory
    lake env lean --run Dregg2/Circuit/Emit/EmitWrapFinDeferred.lean
-/
import Dregg2.Circuit.Emit.KimchiWrapMainCore

open Dregg2.Circuit.Emit.KimchiWrapMain

def show3 (name : String) (t : WrapData) : IO Unit := do
  let d := finSpDerivedWords t
  IO.println s!"{name}:"
  IO.println s!"  FIN_DEFERRED_CIP := {d.1}"
  IO.println s!"  FIN_DEFERRED_B   := {d.2.1}"
  IO.println s!"  FIN_DEFERRED_XI  := {d.2.2}"

def main : IO Unit := do
  show3 "shapeSmoke" (mkWrap shapeSmoke)
  show3 "shapeWrap " (mkWrap shapeWrap)
  IO.println "⚑ paste into KimchiWrapMainField §15c‴; the kernel pin re-derives them."
