import Reactor.Deploy

/-!
# Reactor.ObserveFast — a flat, linear-time runtime for the correlation-id
render on the deployed serve path (`@[csimp]`, spec untouched).

## The super-linear site

The deployed serve stamps an `x-corr` response header carrying the request's
correlation id (`Reactor.Deploy.corrVal`, run inside `deployProg` on every
served request — stage 8 of `deployStagesFull2`, hence on `servePipelineFull2`
and the exported `drorb_serve`). Under the deployed generator/trust
(`demoGen = id`, `demoTrust = false`) the assigned id is exactly the request's
seed — `Reactor.Observe.seedOf input = input.map UInt8.toNat` — so the id has
one entry **per request byte**. The id is rendered to bytes by

    corrBytes c = (String.intercalate "." (c.map toString)).toUTF8.toList

`seedOf` (`input.map UInt8.toNat`) and `c.map toString` are each a single `O(N)`
pass — linear, not the cliff. The cliff is `String.intercalate`: its accumulator
loop is `go (acc ++ sep ++ a)`, and each `String.append` copies the whole growing
`acc` (`lean_string_append` reallocates when the left string has no spare
capacity, which an exactly-sized intercalation accumulator never does). Over an
id of length `N` that is `O(N²)` in the request size — the measured
43→308→1076-byte serve-bench slope grows quadratically, on both the 200 and the
refused (404) arm (both run `deployProg`).

## The flat runtime

`corrStringFast` builds the identical dotted-decimal string in a single linear
construction: the digit char-lists of the parts, joined by `'.'` via one
right-associated `flatten` (each part's chars copied once ⇒ `O(N)`), packed to a
`String` once (`String.ofList`). `corrBytesFast` is its `toUTF8.toList` — the SAME
tail as the spec, so the proof reuses it verbatim and never reasons about the
UTF-8 encoder or `ByteArray.toList`.

`corrBytes_eq_fast` proves `corrStringFast` produces the same `String` (`String`
equality via `String.toList_injective`, established from the 4.30 library lemma
`String.toList_intercalate` and the pure-list bridge `interc_cons_flatten`) and
hence `corrBytesFast = corrBytes`; `@[csimp]` installs the linear pass as the
compiled implementation of `Reactor.Deploy.corrBytes`. Every theorem about
`corrBytes` / `corrVal` / `servePipelineFull2` keeps referring to the unchanged
spec — only the runtime changes, and the emitted `x-corr` bytes are
byte-identical (so the deterministic, observable corr-id value is preserved).

Axioms of the agreement theorem: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

namespace Reactor.ObserveFast

open Reactor.Deploy (corrBytes)

/-! ## List-level bridge for the flat render -/

/-- **The intercalate/flatten bridge.** `List.intercalate sep (p :: ps)` opens
with the head block `p` and then contributes one `sep`-prefixed block per
remaining part — the exact right-associated `flatten` shape `corrStringFast`
builds. Proved by induction on `ps`. This replaces the 4.17
`String.intercalate.go` accumulator invariant: 4.30 rewrote `String.intercalate`
so its `go` worker is a hygienic, non-referenceable constant, but the public
`String.toList_intercalate` lemma exposes exactly `List.intercalate` on the
underlying char lists, so the whole argument moves to the list level. -/
private theorem interc_cons_flatten {α : Type _} (sep : List α) :
    ∀ (p : List α) (ps : List (List α)),
      sep.intercalate (p :: ps) = p ++ (ps.map (fun q => sep ++ q)).flatten := by
  intro p ps
  induction ps generalizing p with
  | nil => simp
  | cons q qs ih =>
    rw [List.intercalate_cons_cons, ih q]
    simp [List.append_assoc]

/-! ## The flat correlation-id render -/

/-- **The linear dotted-decimal render, as a `String`.** The first part opens the
string; every subsequent part contributes a `'.'`-prefixed digit block, joined by
a single right-associated `flatten` (each block's chars copied once ⇒ `O(N)`),
then packed once by `String.ofList`. No `String.append` accumulator — so no
`O(N²)` copy of a growing buffer. -/
def corrStringFast : List Nat → String
  | [] => ""
  | x :: xs =>
      String.ofList ((toString x).toList
        ++ (xs.map (fun n => ".".toList ++ (toString n).toList)).flatten)

/-- `corrStringFast` builds the SAME `String` as the spec's `String.intercalate`.
`String` equality via `String.toList_injective`; the underlying char lists agree
by `String.toList_intercalate` (which unfolds `String.intercalate` to
`List.intercalate` on char lists) and the `interc_cons_flatten` bridge. -/
theorem interc_eq_fast (c : List Nat) :
    String.intercalate "." (c.map toString) = corrStringFast c := by
  cases c with
  | nil => rfl
  | cons x xs =>
    apply String.toList_injective
    simp only [corrStringFast, String.toList_intercalate, String.toList_ofList,
      List.map_cons, List.map_map, interc_cons_flatten, Function.comp_def]

/-- **The flat correlation-id render, as bytes.** The SAME `toUTF8.toList` tail as
`corrBytes`, over the linear `corrStringFast` — so the emitted `x-corr` bytes are
byte-identical while the runtime is `O(N)`. -/
def corrBytesFast (c : Trace.CorrId) : Proto.Bytes := (corrStringFast c).toUTF8.toList

/-- **The linear/spec agreement.** `corrBytesFast` computes exactly `corrBytes`,
in `O(N)` — installed as the compiled implementation of `Reactor.Deploy.corrBytes`
(`@[csimp]`). Every theorem about `corrBytes` / `corrVal` / the deployed serve
keeps referring to the unchanged spec; the `x-corr` header value on the wire is
unchanged. -/
@[csimp] theorem corrBytes_eq_fast : @corrBytes = @corrBytesFast := by
  funext c
  show Reactor.Deploy.corrBytes c = corrBytesFast c
  unfold Reactor.Deploy.corrBytes corrBytesFast
  rw [interc_eq_fast]

end Reactor.ObserveFast
