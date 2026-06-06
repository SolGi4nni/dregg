import Dregg2.Exec.CodecRoundtrip.Leaves
import Dregg2.Exec.CodecRoundtrip.Auth
import Dregg2.Exec.CodecRoundtrip.SideTables

/-!
Submodule of `Dregg2.Exec.CodecRoundtrip` — split for parallel compilation.
-/

namespace Dregg2.Exec.CodecRoundtrip

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide
open Dregg2.Exec.TurnExecutorFull (QueueTxOpA)

/-! ## §7 — the `FullActionA` (WHAT) decoder roundtrip (FILL-J production (c): the 46-arm effect sum).

`parseActionW` is FLAT (no fuel recursion) and uses `do`-notation over the `cN`/`cI`/`cS`/`cA` field
combinators, dispatching on a 46-deep fail-closed tag cascade. The 41 `simple` arms (every arm whose
fields are all `Nat`/`Int` — which is EVERY conserved-measure effect: balances, mints/burns, escrows,
queues, notes, bridges, seals, sovereign) are closed UNIFORMLY by `parseActionW_roundtrip`: the
`skip_to_arm` macro auto-discharges the dispatch (no per-tag lines — `rw [lit_ne_pre]` infers the tags &
defers the `decide`s), then one `simp only` collapses the `do`-block. The 5 remaining arms (the JSON-
string `setFieldA` + the 4 AUTHS-bearing arms) are the documented follow-on (see `isSimpleArm`). -/

/-- **Auto-dispatch:** advance past every WRONG tag in the fail-closed cascade. `rw [lit_ne_pre]` infers
the two concrete tags by unification and DEFERS the `litGo … = none` obligations as side-goals, which
`decide` then closes (sidestepping the eager-`by decide`-with-metavars problem). `repeat` stops exactly
at the matching tag (where the `decide` side-goal is `… = some _`, false, so the step fails & rolls back). -/
local macro "skip_to_arm" : tactic =>
  `(tactic| repeat (rw [lit_ne_pre] <;> first | (simp only []) | decide))

/-- `cS` (read `,` then a quoted JSON string) on an escape-free field — via §0d's `parseStr_clean`. The
input is the SPLIT form (`","`/`"\""` as SEPARATE literals — `setFieldA` first splits its COMBINED
`,"`/`",` separators so every comma is a plain `","`, matching `cN_step`/`nd_litComma`); the bridge to
`parseStr_clean`'s `'"' :: …` is the `decide`-rewrite of `("\"").toList = ['"']`. -/
private theorem cS_step (s : String) (rest : PState) (hcl : ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\') :
    cS ((",":String).toList ++ (("\"":String).toList ++ ((jsonEscape s).toList
        ++ (("\"":String).toList ++ rest)))) = some (s, rest) := by
  unfold cS; rw [lit_append]; simp only []
  rw [show (("\"":String).toList ++ ((jsonEscape s).toList ++ (("\"":String).toList ++ rest)))
        = '"' :: ((jsonEscape s).toList ++ ('"' :: rest)) from by
        simp only [show ("\"":String).toList = ['"'] from by decide, List.cons_append, List.nil_append]]
  exact parseStr_clean s rest hcl

/-- The ONE arm needing more than the `N`/`I`/`A` field toolkit: `setFieldA`, whose `cS` JSON-string
field needs an escape-free `Wf` hypothesis (it cannot be a hypothesis-free `simp` lemma). Every other
arm — including the 4 AUTHS-bearing arms (`delegateAttenA`/`attenuateA`/`exportSturdyRefA`/`enlivenRefA`),
now that §8's `cA_step`/`parseAuths_encode` closes the `cA` field — is `simple`. -/
def isSimpleArm : TurnExecutorFull.FullActionA → Bool
  | .setFieldA .. => false
  | .exerciseA .. => false   -- RECURSES: carries a nested `;`-joined inner-effect array, not a flat arm.
  | .sealA ..     => false   -- carries a `Cap` PAYLOAD field (not a flat `N`/`I`/`A`); see `parseActionW_seal`.
  -- WAVE-4 non-simple arms: a `0`/`1` BOOL flag (parsed under an `if hp ≤ 1` gate), and the two
  -- LIST-bearing batch arms (a `QueueTxOpA` array / two `Nat` arrays) — closed separately below.
  | .createCommittedEscrowA .. => false  -- carries the `hidingProof` flag; see `parseActionW_committedescrow`.
  | .queueAtomicTxA ..         => false  -- carries the `OPS` `QueueTxOpA` array; see `parseActionW_qatomic`.
  | .queuePipelineStepA ..     => false  -- carries two `NATSW` arrays; see `parseActionW_qpipe`.
  | _             => true

/-- One `simple` arm, fully automatic: auto-dispatch to its tag, then collapse the `do`-block of `N`/`I`
fields (`simp` selects the matching `nd_*` closer per field). `done` makes it all-or-nothing, so the
bundle's `first | action_arm | …` cleanly falls through on the 5 non-simple arms. -/
local macro "action_arm" : tactic =>
  `(tactic| (
    unfold parseActionW parseActionWFuel
    simp only [encodeActionW, String.toList_append, List.append_assoc]
    skip_to_arm
    simp only [lit_append,
      parseNat_toString _ _ (nd_litComma _), parseNat_toString _ _ (nd_litClose _),
      cN_step _ _ (nd_litComma _), cN_step _ _ (nd_litClose _),
      cI_step _ _ (nd_litComma _), cI_step _ _ (nd_litClose _), cA_step _ _,
      Option.bind_eq_bind, Option.bind]
    done))

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **FILL J production (c): the `FullActionA` (WHAT) decoder roundtrip — 45 of 46 arms.** Every
`isSimpleArm` action (all but `setFieldA`) round-trips through `encodeActionW`/`parseActionW`, now
INCLUDING the 4 AUTHS-bearing arms (via §8's `cA_step`). This removes nearly all of the WHAT decoder —
EVERY conserved-measure arm (`bal`/`mint`/`burn`/escrow/queue/note/bridge/seal/sovereign…) the
executor's per-asset laws range over, AND the capability-delegation/export arms — from the codec TCB. A
symmetric bug in the WHAT layer (wrong effect tag/args agreed by encoder+decoder) is caught here. -/
theorem parseActionW_roundtrip (act : TurnExecutorFull.FullActionA) (rest : PState)
    (h : isSimpleArm act = true) :
    parseActionW ((encodeActionW act).toList ++ rest) = some (act, rest) := by
  cases act <;> first | action_arm | simp [isSimpleArm] at h

/-! ### NON-VACUITY witnesses for the WHAT decoder (distinct clusters round-trip via one theorem). -/

-- A BALANCE effect (the conserved-measure arm, `[N,N,N,I,N]` with a `Turn` record) round-trips:
example : parseActionW ((encodeActionW (.balanceA ⟨1, 2, 3, 5⟩ 0)).toList ++ ['x'])
            = some (.balanceA ⟨1, 2, 3, 5⟩ 0, ['x']) :=
  parseActionW_roundtrip (.balanceA ⟨1, 2, 3, 5⟩ 0) ['x'] (by decide)
-- ...and an UNSEAL effect (`[N,N,N]`, a different cluster + later in the dispatch cascade) round-trips
-- too (the DE-SHADOWED unseal carries pid/actor/recipient — all flat `N`s; the Cap-bearing `sealA` is the
-- one non-simple seal arm, closed separately by `parseActionW_seal`):
example : parseActionW ((encodeActionW (.unsealA 7 8 9)).toList ++ ['x']) = some (.unsealA 7 8 9, ['x']) :=
  parseActionW_roundtrip (.unsealA 7 8 9) ['x'] (by decide)

set_option maxHeartbeats 1000000 in
/-- **The last `FullActionA` arm: `setFieldA`** — proved SEPARATELY because (a) its `cS` JSON-string
field needs the escape-free `Wf` hypothesis `hcl`, and (b) its encoder uses COMBINED separators `,"`/`",`
which we first SPLIT into single `","` literals so the standard field combinators apply. With this +
`parseActionW_roundtrip`, ALL 46 WHAT-decoder arms carry a parse∘encode theorem — the entire effect
decoder is out of the Lean-side TCB. -/
theorem parseActionW_setfield (actor cell : CellId) (field : String) (v : Int) (rest : PState)
    (hcl : ∀ c ∈ field.toList, c ≠ '"' ∧ c ≠ '\\') :
    parseActionW ((encodeActionW (.setFieldA actor cell field v)).toList ++ rest)
      = some (.setFieldA actor cell field v, rest) := by
  unfold parseActionW parseActionWFuel
  simp only [encodeActionW]
  rw [show (",\"" : String) = "," ++ "\"" from by decide,
      show ("\"," : String) = "\"" ++ "," from by decide]
  simp only [String.toList_append, List.append_assoc]
  skip_to_arm
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    cS_step _ _ hcl, cI_step _ _ (nd_litClose _), Option.bind_eq_bind, Option.bind]

-- A setField effect with an escape-free field name round-trips (the WHAT decoder is now COMPLETE, 46/46):
example : parseActionW ((encodeActionW (.setFieldA 1 2 "balance" 99)).toList ++ ['x'])
            = some (.setFieldA 1 2 "balance" 99, ['x']) :=
  parseActionW_setfield 1 2 "balance" 99 ['x'] (by decide)

set_option maxHeartbeats 1000000 in
/-- **The Wave-3 `sealA` arm (the one Cap-bearing action arm) round-trips** — `{"seal":[pid,actor,CAP]}`.
The DE-SHADOWED seal carries a `Cap` PAYLOAD field (the sealed capability the box binds), so it is NOT a
flat `N`/`I`/`A` arm (`isSimpleArm .sealA = false`); it is closed SEPARATELY here, reusing §C's
`parseCap_encode` for the cap field. With this + `parseActionW_roundtrip` + `parseActionW_setfield`, EVERY
`FullActionA` arm (incl. the Wave-3 lifecycle/seal arms) carries a parse∘encode theorem. -/
theorem parseActionW_seal (pid : Nat) (actor : CellId) (payload : Authority.Cap) (rest : PState) :
    parseActionW ((encodeActionW (.sealA pid actor payload)).toList ++ rest)
      = some (.sealA pid actor payload, rest) := by
  unfold parseActionW parseActionWFuel
  simp only [encodeActionW, String.toList_append, List.append_assoc]
  skip_to_arm
  -- dispatched to the `seal` tag: parse `pid` (post-`,`), `actor` (post-`,`), then `,` + the CAP, then `]}`.
  rw [lit_append]
  simp only [parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    parseCap_encode payload (("]}":String).toList ++ rest), lit_append,
    Option.bind_eq_bind, Option.bind]

/-! ### §7-WAVE4 — the WAVE-4 non-simple arms: the `createCommittedEscrowA` HIDING-FLAG arm and the two
LIST-bearing batch arms (`queueAtomicTxA` / `queuePipelineStepA`). The flag arm carries a `0`/`1` `Bool`
parsed under an `if hp ≤ 1` gate; the batch arms carry a `QueueTxOpA`/`Nat` array. -/

set_option maxHeartbeats 1000000 in
/-- **The WAVE-4 `createCommittedEscrowA` arm** — proved SEPARATELY because its 7th field is the
`hidingProof` BOOL, encoded as a `0`/`1` flag and parsed under the `if hp ≤ 1` gate (which the generic
`action_arm` `simp` cannot reduce). We case-split on `hidingProof`: `true` encodes `1` (`1 ≤ 1`, `1 == 1`),
`false` encodes `0` (`0 ≤ 1`, `0 == 1 = false`), each recovering the flag exactly. -/
theorem parseActionW_committedescrow (id : Nat) (actor creator recipient : CellId) (a : AssetId)
    (amount : Int) (hidingProof : Bool) (rest : PState) :
    parseActionW ((encodeActionW (.createCommittedEscrowA id actor creator recipient a amount hidingProof)).toList ++ rest)
      = some (.createCommittedEscrowA id actor creator recipient a amount hidingProof, rest) := by
  unfold parseActionW parseActionWFuel
  -- the flag is encoded as `","` ++ ("1"/"0"); split it into a plain `","` literal so `cN_step` applies.
  cases hidingProof with
  | true =>
      -- `simp` reduces the encoder's `if (true:Bool) then "1" else "0"` flag literal to `"1"`; we rewrite
      -- it to `toString (1:Nat)` so the closing `cN_step` reads it (closer `]}`), then `simp` evaluates the
      -- parser's `if 1 ≤ 1`/`(1 == 1) = true` gate to recover `true`.
      simp only [encodeActionW, if_true]
      rw [show ("1":String) = toString (1:Nat) from by decide]
      simp only [String.toList_append, List.append_assoc]
      skip_to_arm
      simp only [lit_append, parseNat_toString _ _ (nd_litComma _),
        cN_step _ _ (nd_litComma _), cN_step _ _ (nd_litClose _),
        cI_step _ _ (nd_litComma _), Option.bind_eq_bind, Option.bind,
        show ((1:Nat) ≤ 1) = True from by simp, if_true, beq_self_eq_true]
  | false =>
      -- `simp` reduces `if (false:Bool) then "1" else "0"` to `"0"` (the `false = true` decidable prop is
      -- `False`); rewrite to `toString (0:Nat)`, then `simp` evaluates `0 ≤ 1`/`(0 == 1) = false`.
      simp only [encodeActionW, Bool.false_eq_true, if_false]
      rw [show ("0":String) = toString (0:Nat) from by decide]
      simp only [String.toList_append, List.append_assoc]
      skip_to_arm
      simp only [lit_append, parseNat_toString _ _ (nd_litComma _),
        cN_step _ _ (nd_litComma _), cN_step _ _ (nd_litClose _),
        cI_step _ _ (nd_litComma _), Option.bind_eq_bind, Option.bind,
        show ((0:Nat) ≤ 1) = True from by simp, if_true, show ((0:Nat) == 1) = false from by decide]

-- A committed-escrow effect (privacy escrow, the `hidingProof = true` portal-discharged variant) round-trips:
example : parseActionW ((encodeActionW (.createCommittedEscrowA 1 2 3 4 5 9 true)).toList ++ ['x'])
            = some (.createCommittedEscrowA 1 2 3 4 5 9 true, ['x']) :=
  parseActionW_committedescrow 1 2 3 4 5 9 true ['x']
-- ...and the `hidingProof = false` variant too (the flag is REAL, not erased):
example : parseActionW ((encodeActionW (.createCommittedEscrowA 1 2 3 4 5 9 false)).toList ++ ['x'])
            = some (.createCommittedEscrowA 1 2 3 4 5 9 false, ['x']) :=
  parseActionW_committedescrow 1 2 3 4 5 9 false ['x']

/-! ### §7-WAVE4-LIST — the `queuePipelineStepA` (two `NATSW` arrays) and `queueAtomicTxA` (a `QueueTxOpA`
array) arms. The list-roundtrip infrastructure mirrors §9's `parseNats`/§10's `parseBal` length-fuel loops
verbatim: a `*_cons_shape` exposing the head, a `*_loop_works` induction, and the array-`encode` theorem. -/

-- ===== the `NATSW` array (`parseNatsW ∘ encodeNatsW = id`) — STRUCTURALLY §9's `parseNats`. =====

private def encodeNatsWTail (ns : List Nat) : String :=
  ns.foldl (fun acc x => acc ++ "," ++ toString x) ""

private theorem foldl_natsWTail (ns : List Nat) : ∀ (acc : String),
    ns.foldl (fun s x => s ++ "," ++ toString x) acc
      = acc ++ ns.foldl (fun s x => s ++ "," ++ toString x) "" := by
  induction ns with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ toString b), ih ("" ++ "," ++ toString b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encNatsWTail_cons_shape (b : Nat) (bs : List Nat) (rest : PState) :
    (encodeNatsWTail (b :: bs)).toList ++ rest
      = ',' :: ((toString b).toList ++ ((encodeNatsWTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeNatsWTail (b :: bs) = ("" ++ "," ++ toString b) ++ encodeNatsWTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ toString x) "" = _
      rw [List.foldl_cons]; exact foldl_natsWTail bs ("" ++ "," ++ toString b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeNatsW_cons_shape (a : Nat) (as : List Nat) (rest : PState) :
    (encodeNatsW (a :: as)).toList ++ rest
      = '[' :: ((toString a).toList ++ ((encodeNatsWTail as).toList ++ (']' :: rest))) := by
  simp only [encodeNatsW]
  rw [show (as.foldl (fun acc x => acc ++ "," ++ toString x) "") = encodeNatsWTail as from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem parseNatsW_loop_works : ∀ (as : List Nat) (a : Nat) (rest : PState) (fuel : Nat),
    ((toString a).toList ++ ((encodeNatsWTail as).toList ++ (']' :: rest))).length < fuel →
    parseNatsW.loop fuel ((toString a).toList ++ ((encodeNatsWTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeNatsWTail ([] : List Nat)).toList = [] from rfl, List.nil_append]
      unfold parseNatsW.loop
      rw [parseNat_toString a (']' :: rest) (nd_brack rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encNatsWTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseNatsW.loop
      rw [parseNat_toString a _ (nd_comma _)]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((toString a2).toList ++ ((encodeNatsWTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **`parseNatsW ∘ encodeNatsW = id`** — the WAVE-4 `Nat`-list (sink arrays) roundtrip (§9's recipe). -/
theorem parseNatsW_encode (ns : List Nat) (rest : PState) :
    parseNatsW ((encodeNatsW ns).toList ++ rest) = some (ns, rest) := by
  cases ns with
  | nil =>
      unfold parseNatsW
      simp only [encodeNatsW]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseNatsW
      rw [encodeNatsW_cons_shape a as rest]
      obtain ⟨h0, t0, ht0, hh0dig, _, _⟩ := repr_cons a
      have hempty : lit "[]"
          ('[' :: ((toString a).toList ++ ((encodeNatsWTail as).toList ++ (']' :: rest)))) = none := by
        rw [ht0, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] h0 _ (by intro heq; subst heq; exact absurd hh0dig (by decide))]
      rw [hempty]; simp only []
      rw [show ('[' :: ((toString a).toList ++ ((encodeNatsWTail as).toList ++ (']' :: rest))))
            = ("[":String).toList ++ ((toString a).toList ++ ((encodeNatsWTail as).toList ++ (']' :: rest)))
            from rfl, lit_append]
      simp only []
      apply parseNatsW_loop_works as a rest
      simp only [List.length_append, List.length_cons]; omega

-- ===== the `OPS` array (`parseQueueTxOps ∘ encodeQueueTxOps = id`) — STRUCTURALLY §10's `parseBal`,
-- with the self-delimiting element `encodeQueueTxOp` (a flat `enq`/`deq` tag closing on `]}`). =====

/-- **One `QueueTxOpA` round-trips for ANY tail** (self-delimiting: it closes on `]}`, no post-byte
condition). Dispatch on the `enq`/`deq` tag; each is a flat `N`/`I` do-block (§7 field combinators). -/
theorem parseQueueTxOp_encode (op : QueueTxOpA) (rest : PState) :
    parseQueueTxOp ((encodeQueueTxOp op).toList ++ rest) = some (op, rest) := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      unfold parseQueueTxOp
      simp only [encodeQueueTxOp, String.toList_append, List.append_assoc]
      rw [lit_append]
      simp only [parseNat_toString _ _ (nd_litComma _),
        cN_step _ _ (nd_litComma _), cN_step _ _ (nd_litClose _),
        cI_step _ _ (nd_litClose _), lit_append, Option.bind_eq_bind, Option.bind]
  | dequeue id actor cell depId deposit =>
      unfold parseQueueTxOp
      simp only [encodeQueueTxOp, String.toList_append, List.append_assoc]
      -- the `enq` tag fails first (the `deq` shape is `{"deq":…`), then the `deq` arm fires.
      rw [show lit "{\"enq\":[" (("{\"deq\":[":String).toList ++ _) = none from
            lit_ne_pre "{\"enq\":[" "{\"deq\":[" _ (by decide) (by decide)]
      simp only []
      rw [lit_append]
      simp only [parseNat_toString _ _ (nd_litComma _),
        cN_step _ _ (nd_litComma _), cN_step _ _ (nd_litClose _),
        cI_step _ _ (nd_litClose _), lit_append, Option.bind_eq_bind, Option.bind]

private def encodeQueueTxOpsTail (ops : List QueueTxOpA) : String :=
  ops.foldl (fun acc x => acc ++ "," ++ encodeQueueTxOp x) ""

/-- Every `OP` opens with `'{'` (so the `OPS` body is `[{…`, making `lit "[]"` fail). -/
private theorem encodeQueueTxOp_head (op : QueueTxOpA) : ∃ t, (encodeQueueTxOp op).toList = '{' :: t := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      refine ⟨("\"enq\":[" ++ toString id ++ "," ++ toString m ++ "," ++ toString actor ++ ","
        ++ toString cell ++ "," ++ toString depId ++ "," ++ toString dAsset ++ ","
        ++ toString deposit ++ "]}" : String).toList, ?_⟩
      unfold encodeQueueTxOp
      simp only [String.toList_append, show ("{\"enq\":[":String).toList = '{' :: "\"enq\":[".toList from by decide,
        List.cons_append, List.nil_append, List.append_assoc]
  | dequeue id actor cell depId deposit =>
      refine ⟨("\"deq\":[" ++ toString id ++ "," ++ toString actor ++ "," ++ toString cell ++ ","
        ++ toString depId ++ "," ++ toString deposit ++ "]}" : String).toList, ?_⟩
      unfold encodeQueueTxOp
      simp only [String.toList_append, show ("{\"deq\":[":String).toList = '{' :: "\"deq\":[".toList from by decide,
        List.cons_append, List.nil_append, List.append_assoc]

private theorem foldl_opsTail (ops : List QueueTxOpA) : ∀ (acc : String),
    ops.foldl (fun s x => s ++ "," ++ encodeQueueTxOp x) acc
      = acc ++ ops.foldl (fun s x => s ++ "," ++ encodeQueueTxOp x) "" := by
  induction ops with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeQueueTxOp b), ih ("" ++ "," ++ encodeQueueTxOp b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encOpsTail_cons_shape (b : QueueTxOpA) (bs : List QueueTxOpA) (rest : PState) :
    (encodeQueueTxOpsTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeQueueTxOp b).toList ++ ((encodeQueueTxOpsTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeQueueTxOpsTail (b :: bs)
        = ("" ++ "," ++ encodeQueueTxOp b) ++ encodeQueueTxOpsTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeQueueTxOp x) "" = _
      rw [List.foldl_cons]; exact foldl_opsTail bs ("" ++ "," ++ encodeQueueTxOp b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeQueueTxOps_cons_shape (a : QueueTxOpA) (as : List QueueTxOpA) (rest : PState) :
    (encodeQueueTxOps (a :: as)).toList ++ rest
      = '[' :: ((encodeQueueTxOp a).toList ++ ((encodeQueueTxOpsTail as).toList ++ (']' :: rest))) := by
  rw [show encodeQueueTxOps (a :: as) = "[" ++ encodeQueueTxOp a ++ encodeQueueTxOpsTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem parseQueueTxOps_loop_works : ∀ (as : List QueueTxOpA) (a : QueueTxOpA) (rest : PState) (fuel : Nat),
    ((encodeQueueTxOp a).toList ++ ((encodeQueueTxOpsTail as).toList ++ (']' :: rest))).length < fuel →
    parseQueueTxOps.loop fuel ((encodeQueueTxOp a).toList ++ ((encodeQueueTxOpsTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeQueueTxOpsTail ([] : List QueueTxOpA)).toList = [] from rfl, List.nil_append]
      unfold parseQueueTxOps.loop
      rw [parseQueueTxOp_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encOpsTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseQueueTxOps.loop
      rw [parseQueueTxOp_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeQueueTxOp a2).toList ++ ((encodeQueueTxOpsTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **`parseQueueTxOps ∘ encodeQueueTxOps = id`** — the WAVE-4 atomic-batch `OPS` array roundtrip (§10's
self-delimiting-element recipe, the element being a `QueueTxOpA`). -/
theorem parseQueueTxOps_encode (ops : List QueueTxOpA) (rest : PState) :
    parseQueueTxOps ((encodeQueueTxOps ops).toList ++ rest) = some (ops, rest) := by
  cases ops with
  | nil =>
      unfold parseQueueTxOps
      rw [show (encodeQueueTxOps ([] : List QueueTxOpA)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseQueueTxOps
      rw [encodeQueueTxOps_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeQueueTxOp a).toList ++ ((encodeQueueTxOpsTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeQueueTxOp_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '{' _ (by decide)]
      rw [hempty]; simp only []
      rw [show ('[' :: ((encodeQueueTxOp a).toList ++ ((encodeQueueTxOpsTail as).toList ++ (']' :: rest))))
            = ("[":String).toList ++ ((encodeQueueTxOp a).toList ++ ((encodeQueueTxOpsTail as).toList ++ (']' :: rest)))
            from rfl, lit_append]
      simp only []
      apply parseQueueTxOps_loop_works as a rest
      simp only [List.length_append, List.length_cons]; omega

set_option maxHeartbeats 1000000 in
/-- **The WAVE-4 `queueAtomicTxA` arm** — `{"qatomic":[actor,OPS]}`: read `actor` (post-tag `Nat`), then
the `,` + the `OPS` `QueueTxOpA` array (via `parseQueueTxOps_encode`), then `]}`. -/
theorem parseActionW_qatomic (actor : CellId) (ops : List QueueTxOpA) (rest : PState) :
    parseActionW ((encodeActionW (.queueAtomicTxA actor ops)).toList ++ rest)
      = some (.queueAtomicTxA actor ops, rest) := by
  unfold parseActionW parseActionWFuel
  simp only [encodeActionW, String.toList_append, List.append_assoc]
  skip_to_arm
  rw [lit_append]
  -- read `actor` (closer `,`), then `lit ","` (via `lit_append`), then the `OPS` array, then `]}`. The
  -- `Option.bind` reductions expose each step's input for the next rewrite.
  simp only [parseNat_toString _ _ (nd_litComma _), Option.bind_eq_bind, Option.bind]
  rw [lit_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseQueueTxOps_encode ops (("]}":String).toList ++ rest)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]

-- An atomic batch (one enqueue + one dequeue sub-op) round-trips (the WHAT decoder covers the batch arm):
example : parseActionW ((encodeActionW (.queueAtomicTxA 1 [QueueTxOpA.enqueue 2 3 4 5 6 7 8,
            QueueTxOpA.dequeue 9 10 11 12 13])).toList ++ ['x'])
            = some (.queueAtomicTxA 1 [QueueTxOpA.enqueue 2 3 4 5 6 7 8,
                QueueTxOpA.dequeue 9 10 11 12 13], ['x']) :=
  parseActionW_qatomic 1 [QueueTxOpA.enqueue 2 3 4 5 6 7 8, QueueTxOpA.dequeue 9 10 11 12 13] ['x']

set_option maxHeartbeats 1000000 in
/-- **The WAVE-4 `queuePipelineStepA` arm** — `{"qpipe":[srcId,owner,SINKCELLS,SINKIDS]}`: read `srcId`
(post-tag `Nat`) + `owner` (`cN`), then `,` + the two `NATSW` arrays (via `parseNatsW_encode`), then `]}`. -/
theorem parseActionW_qpipe (srcId : Nat) (owner : CellId) (sinkCells sinkIds : List Nat) (rest : PState) :
    parseActionW ((encodeActionW (.queuePipelineStepA srcId owner sinkCells sinkIds)).toList ++ rest)
      = some (.queuePipelineStepA srcId owner sinkCells sinkIds, rest) := by
  unfold parseActionW parseActionWFuel
  simp only [encodeActionW, String.toList_append, List.append_assoc]
  skip_to_arm
  rw [lit_append]
  -- read `srcId` (closer `,`) + `owner` (`cN`, closer `,`), then `,` + SINKCELLS, then `,` + SINKIDS, then
  -- `]}`. Each `lit`/array step is followed by an `Option.bind` reduction exposing the next input.
  simp only [parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    Option.bind_eq_bind, Option.bind]
  rw [lit_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNatsW_encode sinkCells _]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNatsW_encode sinkIds (("]}":String).toList ++ rest)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]

-- A pipeline step with two distinct sinks round-trips (the fan-out routing arm decodes exactly):
example : parseActionW ((encodeActionW (.queuePipelineStepA 1 2 [3, 4] [5, 6])).toList ++ ['x'])
            = some (.queuePipelineStepA 1 2 [3, 4] [5, 6], ['x']) :=
  parseActionW_qpipe 1 2 [3, 4] [5, 6] ['x']

-- A Wave-3 SEAL effect (the Cap-bearing arm) round-trips (the WHAT decoder is COMPLETE, every arm):
example : parseActionW ((encodeActionW (.sealA 7 8 (Authority.Cap.endpoint 9 [.read]))).toList ++ ['x'])
            = some (.sealA 7 8 (Authority.Cap.endpoint 9 [.read]), ['x']) :=
  parseActionW_seal 7 8 (Authority.Cap.endpoint 9 [.read]) ['x']
def WfActionW : TurnExecutorFull.FullActionA → Prop
  | .setFieldA _ _ field _ => ∀ c ∈ field.toList, c ≠ '"' ∧ c ≠ '\\'
  | .exerciseA _ _ inner   => inner = []
  | _                      => True

/-- `parseActionsWFuel` on a leading `]` is the empty-array base case, for ANY successor fuel. -/
private theorem parseActionsWFuel_leadBracket (n : Nat) (X : PState) :
    parseActionsWFuel (n + 1) (']' :: X) = some ([], ']' :: X) := by
  simp only [parseActionsWFuel]

/-- **The empty-inner `exerciseA` arm round-trips** — `{"exercise":[actor,target,[]]}` parses back to
`.exerciseA actor target []`. The bare cap-exercise wire form (the inner array is the empty `[]`); the
fuel never recurses (the inner-array parser hits the `']' :: _` base case immediately). The non-empty
nested case is the FILL-J followup (`#136`). -/
theorem parseActionW_exercise_nil (actor target : CellId) (rest : PState) :
    parseActionW ((encodeActionW (.exerciseA actor target [])).toList ++ rest)
      = some (.exerciseA actor target [], rest) := by
  unfold parseActionW parseActionWFuel
  simp only [encodeActionW, encodeActionsW, String.toList_append, List.append_assoc]
  skip_to_arm
  -- read actor (`parseNat`, closer `,`) + target (`cN`, whose closer is the `,` of the `,[` separator —
  -- proved non-digit by the inline `hnd`). The post-target tail is `,[` ++ `]]}` ++ rest: `lit ",["`
  -- fires, then `parseActionsWFuel` sees the leading `]` of `]]}` (base case ⇒ `[]`), then `lit "]"` +
  -- `lit "]}"` close the two brackets.
  have hnd : ∀ rest' : PState, (",[":String).toList ++ rest' = []
      ∨ ∃ c rs, (",[":String).toList ++ rest' = c :: rs ∧ c.isDigit = false :=
    fun rest' => Or.inr ⟨',', ('[' :: rest'), by rfl, by decide⟩
  -- the inner-array parse on a leading `]` ⇒ `[]` (`parseActionsWFuel_leadBracket` over the successor
  -- seed fuel), then `lit "]"`/`lit "]}"` consume the closing brackets.
  have hb1 : ∀ X : PState, lit "]" (']' :: X) = some X := fun X => by
    rw [show (']' :: X) = ("]" : String).toList ++ X from by
          rw [show ("]" : String).toList = [']'] from by decide]; rfl]
    exact lit_append _ _
  -- read actor (`parseNat`) + target (`cN`) + `lit ",["`, exposing the inner-array parse. `List.cons_append`
  -- normalizes `(']' :: …) ++ …` (note `::` binds TIGHTER than `++`) to `']' :: (… ++ …)` so the leading
  -- `]` is exposed for the base case.
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (hnd _),
    show ("]]}" : String).toList = ']' :: "]}".toList from by decide,
    show ("" : String).toList = [] from by decide, List.nil_append, List.cons_append,
    parseActionsWFuel_leadBracket, hb1, Option.bind_eq_bind, Option.bind]

/-- **`parseActionW` inverts `encodeActionW` on EVERY arm** — the `simple` arms via §7's
`parseActionW_roundtrip`, the `setFieldA` arm via §7's `parseActionW_setfield` (under its escape-free
`WfActionW`), and the bare `exerciseA` (`inner = []`) via `parseActionW_exercise_nil`. The unified
WHAT-decoder leaf the node element calls. -/
theorem parseActionW_any (act : TurnExecutorFull.FullActionA) (rest : PState) (hwf : WfActionW act) :
    parseActionW ((encodeActionW act).toList ++ rest) = some (act, rest) := by
  cases act with
  | setFieldA actor cell field v => exact parseActionW_setfield actor cell field v rest hwf
  | sealA pid actor payload => exact parseActionW_seal pid actor payload rest   -- Wave-3 Cap-bearing arm
  | exerciseA actor target inner =>
      -- `WfActionW` pins `inner = []` (the codec boundary); the empty-inner arm round-trips.
      simp only [WfActionW] at hwf; subst hwf
      exact parseActionW_exercise_nil actor target rest
  -- WAVE-4 non-simple arms (the `hidingProof` flag + the two list-bearing batch arms):
  | createCommittedEscrowA id actor creator recipient a amount hp =>
      exact parseActionW_committedescrow id actor creator recipient a amount hp rest
  | queueAtomicTxA actor ops => exact parseActionW_qatomic actor ops rest
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      exact parseActionW_qpipe srcId owner sinkCells sinkIds rest
  | _ => exact parseActionW_roundtrip _ rest rfl

end Dregg2.Exec.CodecRoundtrip
