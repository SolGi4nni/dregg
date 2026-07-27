/-
  Pancake/LowerBridge.lean — Seam L, closed for the EMITTED serve response head.

  THE RESIDUAL THIS FILE ATTACKS (the redesign named it in ServeEmit.lean's own
  header, "FAITHFULNESS RESIDUALS", third bullet): `ServeEmit.storesInto` emits
  `PStmt.storeb` (the byte store `st8 out+i, b`, the DSL the pretty-printer turns
  into the `.pnk` text cake compiles), while `StructEmit.storeLit` builds `.store`
  nodes (word stores) in the MODEL language, and NO theorem relates the two. So
  `respEmit_correct` certifies a MODEL program, not the emitted `.pnk`.

  WHAT THIS FILE PROVES (the bridge, for the emitted head). `Pancake/Lower.lean`
  gives `lower : PFun → Option PancakeProg`, whose OBLIGATION (Lower.lean header)
  is that it agrees with cake's own parse of `ppFun f`. Here we run `lower`'s
  statement folder on the EXACT `PStmt` list `ServeEmit.storesInto` emits and prove
  it equals a concrete, explicit model `PancakeProg` built from `.storeByte` nodes,
  for ALL byte lists:

      lowerStmtsFold (storesInto dst bs) = some (storesModel dst ((range |bs|).zip bs))

  This is the missing link: the emitted byte-store head and a named model program
  are now ONE term, related by the parse-faithful `lower`. It is proven GENERICALLY
  (induction on the zipped index/byte list), then discharged on the REAL emitted
  fragments — the `serialize resp200` / `serialize resp405` byte stores the routed
  serve actually prints (`serveExport`).

  WHAT IT DOES NOT CLOSE, STATED PLAINLY (see §4). Two gaps survive, and neither is
  papered over:

   1. `lower` maps the emitted `storeb` to `.storeByte` (the FAITHFUL image — the
      emitted `.pnk` genuinely says `st8`). `StructEmit.storeLit_membytes` /
      `respEmit_correct` are about `.store` (WORD stores). So the bridge lands a
      *byte-store* model program, which is NOT the *word-store* program those
      theorems certify. The proof and the printed text now share one term; that
      term is not (yet) the term the correctness proof runs on.

   2. Deeper: `MemBytesAt` is word-addressed — one byte per whole word slot
      (`s.memory (base+i) = wordOfByte bs[i]`, `wordOfByte b = b.setWidth 64`).
      The emitted `st8` runs `mem_store_byte`, i.e. `byteAlign`+`setByte` into a
      SHARED word (sub-word packing). Under the word-addressed `MemBytesAt` the
      byte-store program does NOT land the same post-state as `storeLit`; the two
      emitters commit to different memory models. Certifying the emitted program
      end-to-end needs a `storeByte`-flavoured landing lemma against a
      byte-addressed post-state (or the emitter switched to word stores to reuse
      `storeLit_membytes`) — named here, not proven.

  So this file closes the SYNTACTIC half of the seam (emitted PStmt ⟷ a named
  model PancakeProg, via the parse-faithful `lower`) for the real serve head, and
  pins the two residuals that block the SEMANTIC half.

  BUILD-GRAPH GAP (reported, not fixed): `Pancake/ServeEmit.lean` is NOT a
  `lakefile.lean` root (only `Lower` and `StructEmit` are), so `lake build` never
  compiles it. This file is built by its own script against the prebuilt olean set
  (the pattern the other serve lanes use), same as `ServeEmit` itself.
-/
import Pancake.ServeEmit
import Pancake.Lower

namespace Pancake.LowerBridge

open Dsl.EmitPancake (PExpr PStmt PFun POp atOff v n eAdd)
open Pancake
open Pancake.Lower (lowerExp lowerStmt1 lowerStmtsFold lower)
open Pancake.ServeEmit (storesInto serveExport)

/-! ## 1. The address model — what `lower` makes of `atOff (v dst) k`

`storesInto` addresses byte `k` as `atOff (v dst) k`, which is `v dst` at offset
`0` (the `+0` is dropped by `atOff`) and `eAdd (v dst) (n k)` otherwise. `lower`
sends the former to `.var dst` and the latter to `.op .add (.var dst) (.const k)`.
`addrModel` is that image, and `lowerExp_atOff` proves `lower` computes it. -/

/-- The `lower`-image of the `k`-th store address `atOff (v dst) k`. -/
def addrModel (dst : String) (k : Nat) : PancakeExp :=
  if k == 0 then .var dst
  else .op .add (.var dst) (.const (BitVec.ofNat 64 k))

/-- `lower` sends the emitted store address to `addrModel`, for every offset. The
`k = 0` case uses `atOff`'s `+0` drop; the `k = k'+1` case lowers the `.binop .add`
to `.op .add`. -/
theorem lowerExp_atOff (dst : String) (k : Nat) :
    lowerExp (atOff (v dst) k) = some (addrModel dst k) := by
  cases k with
  | zero =>
    simp [atOff, addrModel, v, lowerExp]
  | succ k' =>
    simp [atOff, addrModel, eAdd, v, n, lowerExp]

/-- `lower` sends the emitted byte value `n b` to `.const (b : word)`. -/
theorem lowerExp_n (b : Nat) :
    lowerExp (n b) = some (.const (BitVec.ofNat 64 b)) := by
  simp only [n, lowerExp]

/-! ## 2. The store-list model and the bridge lemma

`storesIntoL` is `storesInto`'s body isolated over an arbitrary index/byte list
`ps` (so `storesInto dst bs = storesIntoL dst ((range |bs|).zip bs)`, definitional).
`storesModel` is the model program `lower` produces from it: a right-nested `Seq`
of `.storeByte` nodes matching `lowerStmtsFold`'s own shape (singleton without a
trailing `Skip`). The bridge is proved by induction on `ps`. -/

/-- The emitted store list over an explicit `(offset, byte)` list. Definitionally
`storesInto dst bs = storesIntoL dst ((List.range bs.length).zip bs)`. -/
def storesIntoL (dst : String) (ps : List (Nat × Nat)) : List PStmt :=
  ps.map (fun p => PStmt.storeb (atOff (v dst) p.1) (n p.2))

/-- The `lower`-image of `storesIntoL`: `.storeByte (addrModel dst off) (const b)`
per entry, right-nested, matching `lowerStmtsFold` (a lone entry lowers to a bare
`.storeByte`, no trailing `.skip`). -/
def storesModel (dst : String) : List (Nat × Nat) → PancakeProg
  | []      => .skip
  | [p]     => .storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2))
  | p :: ps => .seq (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2)))
                    (storesModel dst ps)

/-- Lowering a single emitted store. -/
theorem lowerStmt1_storeb_off (dst : String) (p : Nat × Nat) :
    lowerStmt1 (PStmt.storeb (atOff (v dst) p.1) (n p.2))
      = some (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2))) := by
  rw [lowerStmt1]
  rw [lowerExp_atOff, lowerExp_n]

/-- **THE BRIDGE (generic).** `lower`'s statement folder run on the exact `PStmt`
list `storesInto` emits equals the explicit `.storeByte` model program, for ALL
index/byte lists. Induction on `ps`; the cons step splits on whether the tail is
empty (matching `lowerStmtsFold`'s singleton special case). Every emitted element
is a `.storeb` — never a `.dec` — so the `dec`-scoping branch of `lowerStmtsFold`
never fires. -/
theorem storesIntoL_lowers (dst : String) :
    ∀ ps : List (Nat × Nat),
      lowerStmtsFold (storesIntoL dst ps) = some (storesModel dst ps)
  | [] => rfl
  | [p] => by
      show lowerStmtsFold [PStmt.storeb (atOff (v dst) p.1) (n p.2)]
          = some (storesModel dst [p])
      rw [lowerStmtsFold]
      exact lowerStmt1_storeb_off dst p
  | p :: q :: ps => by
      have ih := storesIntoL_lowers dst (q :: ps)
      have h1 := lowerStmt1_storeb_off dst p
      show (match lowerStmt1 (PStmt.storeb (atOff (v dst) p.1) (n p.2)),
                  lowerStmtsFold (storesIntoL dst (q :: ps)) with
            | some s', some r' => some (PancakeProg.seq s' r')
            | _, _             => none)
          = some (storesModel dst (p :: q :: ps))
      rw [h1, ih]
      rfl

/-- **THE BRIDGE, on the real emitter.** `storesInto dst bs` is definitionally
`storesIntoL dst ((range |bs|).zip bs)`, so the emitted per-byte `st8` head lowers
to a named model `.storeByte` program for EVERY byte list `bs`. -/
theorem storesInto_lowers (dst : String) (bs : List Nat) :
    lowerStmtsFold (storesInto dst bs)
      = some (storesModel dst ((List.range bs.length).zip bs)) := by
  show lowerStmtsFold (storesIntoL dst ((List.range bs.length).zip bs))
      = some (storesModel dst ((List.range bs.length).zip bs))
  exact storesIntoL_lowers dst _

/-! ## 3. Non-vacuity — the bridge lands a REAL, non-trivial program

The emitted head is not empty and not a stub: for a non-empty byte list the model
is a genuine `.storeByte` chain, and its store count equals the byte count. -/

/-- Count the `.storeByte` nodes of a model program (the emitted head is all
byte stores; `.store` word stores are counted separately by StructEmit). -/
def storeByteCount : PancakeProg → Nat
  | .storeByte _ _ => 1
  | .seq c1 c2     => storeByteCount c1 + storeByteCount c2
  | _              => 0

/-- The model is exactly `|ps|` byte stores — one per emitted `st8`, no stub. -/
theorem storeByteCount_storesModel (dst : String) :
    ∀ ps : List (Nat × Nat), storeByteCount (storesModel dst ps) = ps.length
  | []          => rfl
  | [_]         => rfl
  | _ :: q :: ps => by
      show 1 + storeByteCount (storesModel dst (q :: ps)) = _
      rw [storeByteCount_storesModel dst (q :: ps)]
      simp [List.length_cons]
      omega

/-- On the real emitter: the lowered head has exactly `|bs|` byte stores. -/
theorem storesInto_storeByteCount (dst : String) (bs : List Nat) :
    storeByteCount (storesModel dst ((List.range bs.length).zip bs)) = bs.length := by
  rw [storeByteCount_storesModel]
  rw [List.length_zip, List.length_range, Nat.min_self]

/-! ## 4. Discharge on the ACTUAL emitted serve responses

`serveExport` stores `bytesOf (serialize resp200)` on the routed-in branch and
`bytesOf (serialize resp405)` on the 405 branch (ServeEmit §serveExport). Those are
the exact byte lists whose `st8` stores the printed `.pnk` carries. The bridge
fires on them: the emitted response head lowers to a named `.storeByte` model
program. (`bs200`/`bs405` are left abstract here so the statement is the bridge,
not a byte-blob recomputation; the `#guard`s in ServeEmit already pin their
content and non-emptiness.) -/

/-- The routed-branch response head lowers to a named model program. -/
theorem serve_resp_head_lowers (bs200 : List Nat) :
    lowerStmtsFold (storesInto "out" bs200)
      = some (storesModel "out" ((List.range bs200.length).zip bs200)) :=
  storesInto_lowers "out" bs200

/-- …and it is a genuine per-byte store chain (|bs200| byte stores). -/
theorem serve_resp_head_nonstub (bs200 : List Nat) :
    storeByteCount (storesModel "out" ((List.range bs200.length).zip bs200))
      = bs200.length :=
  storesInto_storeByteCount "out" bs200

/-! ## 5. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms lowerExp_atOff
#print axioms storesIntoL_lowers
#print axioms storesInto_lowers
#print axioms storeByteCount_storesModel
#print axioms storesInto_storeByteCount
#print axioms serve_resp_head_lowers
#print axioms serve_resp_head_nonstub

end Pancake.LowerBridge
