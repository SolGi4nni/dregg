/-
# Dregg2.Circuit.Emit.DyckStackReplay — SLICE 4 of *parse as derivation*: the CAPSTONE that
closes the SAT⇒Replay loop.

`docs/DESIGN-parse-as-derivation.md` §3/§5.1 names the hard part deferred through slices 1–3: the
whole-descriptor bridge

    parse_sat_imp_replay :
      Satisfied2 dyckDesc … t  →  ReplayAccepts dyck (rulesOf t) (inputOf t)

— "a satisfying trace IS an accepting leftmost pushdown replay of the Dyck grammar." §3 calls this a
"genuine transition-relation induction across all active rows, with the STACK as the inductive
invariant" and flags it as the multi-month-*risk* item.

## What slice 3 already landed (verified at HEAD, `DyckStackRefine.lean`)

Two proven halves stand there, joined by ONE honestly-named residual (its §7):

* **(§4.1) the per-row bridge** `dyck_sat_imp_row_valid` — a trace `Satisfied2 dyckDesc`, canonical
  (`DyckCanon`), witnesses the genuine per-row relation `DyckRowValid` on EVERY transition row.
* **(§6) the multi-row assembly** `mrun_imp_replay` — a FORWARD `MRun` of per-row-valid steps ending
  in an accepting `done` IS a backward `CfgCompact.Replay`, with the rule sequence RECONSTRUCTED by
  `rulesOf` and the stack threaded as the induction invariant. This is the design's named hard part,
  and it is proven, not assumed.
* **(§7) the seam between them** — the DECODE GLUE: a function `decode : VmTrace → List MRow` reading
  each row's `STACK[0..D−1]` + `STACK_DEPTH` back into a `List (Symbol Brk NTs)`, its `Act` from the
  selectors, its remaining input from `INPUT_POS`; plus the per-row lemma `DyckRowValid (envAt t i) →
  MStep (decode t)[i] (decode t)[i+1]`. Its general form needs the **depth↔occupancy invariant**
  `dyck_stack.rs` still owes ("nothing yet ties `STACK_DEPTH` to which cells are nonzero").

## What THIS file (slice 4) adds

1. **`replay_of_run_initial`** (§1) — the stack-invariant fold's payoff stated at the `ReplayAccepts`
   level: an `MRun` whose head stack is the grammar's initial nonterminal IS an accepting replay.
   This is `mrun_imp_replay` lifted to the acceptance predicate; it is the "assemble per-row validity
   into a whole pushdown replay" of the prompt, PROVEN.
2. **The decode (§2)** — `symOfId` / `decodeStack` / `decodeAct` / `decodeRow` / `decodeRun`: the §7
   decode function, written concretely. It reads the same `STACK[i]` / `STACK_DEPTH` / selector /
   `INPUT_POS` columns the per-row teeth constrain.
3. **`decode_witTrace`** (§3) — the §7 decode seam CLOSED for the shipped bracket-pair trace: the
   satisfying `witTrace` (proven `Satisfied2` in slice 3, `DyckStackRefine.witTrace_satisfies`)
   decodes to the accepting forward run `bRow0 :: bracketsRest`. For this concrete trace the
   depth↔occupancy invariant holds by COMPUTATION, so the seam needs no circuit tooth here.
4. **`witTrace_replays`** (§3) — the concrete `parse_sat_imp_replay`: the decoded run assembles,
   through `mrun_imp_replay`, into `ReplayAccepts dyck [rBracket, rEmpty] [op, cl]` — EXACTLY the
   statement of the hand proof `CfgCompact.Reference.brackets_replays`, reached here from the actual
   circuit trace via decode.
5. **`witTrace_steps_valid`** (§3) — the satisfaction is load-bearing: the circuit's acceptance of
   `witTrace` CERTIFIES (via the per-row bridge) that every decoded transition row is a genuine
   pushdown step. Acceptance ⇒ valid steps; decode ⇒ the run; the two compose into the replay.
6. **`witTrace_in_language`** (§3) — the consistency check the prompt asks for: `compact_sound` on the
   produced `ReplayAccepts` recovers `[op, cl] ∈ dyck.language`.
7. **`witTrace_satisfies_and_replays`** (§4) — the closed loop for the shipped word, stated as the
   honest conjunction: the concrete trace is BOTH accepted by the circuit AND decodes to an accepting
   grammar replay.
8. **`decode_step`** (§2.3) — ONE `MStep` of the abstract run from ONE valid transition row: the
   per-action cell equations (`bracketPush`/`emptyPop`/`termPop`), assembled by
   `decodeStack_push`/`decodeStack_pop` over the length-pinned (occupancy) decoded stack, ARE the
   `MStep` stack relation `b.stk = r.output ++ rest`. The structural core the residual named.
9. **`mrun_from` / `parse_sat_imp_replay`** (§4.5) — the forward `MRun` threaded across an ARBITRARY
   satisfying trace (padding truncated at the first `done`), folded through `replay_of_run_initial`
   into `ReplayAccepts`. THE GENERAL SOUNDNESS THEOREM. `witTrace_replays_via_general` (§5) recovers
   the shipped case as an instance.

## SCOPE (honest, per the iterative method)

**The general theorem is now PROVEN.** `parse_sat_imp_replay` holds for an ARBITRARY trace `t` and
word `word` — the satisfaction predicate is what forces every decoded row to be a genuine pushdown
step (`decode_step`), so soundness is load-bearing, not a `rfl` on a fixed constant. It rests on the
depth↔occupancy tooth (`DyckStackRefine.occupied_of_sat` + `decodeStack_length_of_sat`), read out of
the deployed accept-set, plus honest boundary/tape hypotheses (initial-symbol PI, the halt row, the
input columns spelling `word`). The concrete `witTrace_replays` is kept as a sanity instance and is
also re-derived through the general theorem (`witTrace_replays_via_general`).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only; not
reachable from `Dregg2.lean`. Verified with `lake env lean` on this file.
-/
import Dregg2.Circuit.Emit.DyckStackRefine
import Dregg2.Crypto.CfgCompact
import Dregg2.Tactics

namespace Dregg2.Circuit.Emit.DyckStackReplay

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt gate_modEq_iff)
open Dregg2.Circuit.Emit.DyckStackRefine
open Dregg2.Crypto.Cfg.Reference (Brk NTs dyck rBracket rEmpty)
open Dregg2.Crypto.Cfg.Reference.Brk (op cl)
open Dregg2.Crypto.CfgCompact (Replay ReplayAccepts)

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §1 — THE ASSEMBLY, at the acceptance predicate: an `MRun` from the initial stack IS an
accepting replay.

`mrun_imp_replay` (slice 3, §6) is the transition-relation induction with the stack as invariant:
it turns a forward `MRun a rest` into `Replay dyck (rulesOf (a :: rest)) a.inp a.stk`. Here we pin the
head stack to the grammar's initial nonterminal, which is exactly the initial stack `ReplayAccepts`
opens on — so the run becomes an ACCEPTING replay. This is the "fold per-row validity forward,
maintaining `Replay g rs_so_far input_remaining stack_of_row` as the invariant" step, delivered. It is
general in the run length: no concreteness is used. -/
theorem replay_of_run_initial {a : MRow} {rest : List MRow}
    (hrun : MRun a rest) (hinit : a.stk = [Symbol.nonterminal dyck.initial]) :
    ReplayAccepts dyck (rulesOf (a :: rest)) a.inp := by
  have h := mrun_imp_replay hrun
  rw [hinit] at h
  exact h

/-! ## §2 — THE DECODE (the §7 seam, written concretely).

`decode` reads a trace row back into the `MRow` the abstract machine carries: the stack cells
`STACK[0..STACK_DEPTH)` under the symbol-id map, the action from the selectors + `RULE_ID`, and the
remaining input as the suffix of the word from `INPUT_POS`. These are the SAME columns
`DyckRowValid`'s per-action teeth constrain (`ruleTopIsS`, `bracketPush`, `termTopIsToken`,
`termAdvances`, …). -/

/-- The symbol-id map (`dyck_stack.rs`'s `SYM_*`): `1 ↦ S`, `2 ↦ op`, `3 ↦ cl`, everything else
(the `0 = EMPTY` marker, out-of-range) is absent. -/
def symOfId (z : ℤ) : Option (Symbol Brk NTs) :=
  if z = SYM_S then some (Symbol.nonterminal NTs.S)
  else if z = SYM_OP then some (Symbol.terminal op)
  else if z = SYM_CL then some (Symbol.terminal cl)
  else none

/-- Read the working stack: the first `STACK_DEPTH` cells (top at index `0`), symbol-decoded. The
`EMPTY` marker maps to nothing, so a well-formed occupancy yields exactly the live prefix. -/
def decodeStack (a : Assignment) : List (Symbol Brk NTs) :=
  (List.range (a STACK_DEPTH).toNat).filterMap (fun i => symOfId (a (stk i)))

/-- Read the action from the selectors + `RULE_ID` + `INPUT_TOKEN` (`dyck_stack.rs::Action`). -/
def decodeAct (a : Assignment) : Act :=
  if a IS_RULE = 1 then
    (if a RULE_ID = RULE_BRACKET then Act.rule rBracket else Act.rule rEmpty)
  else if a IS_TERM = 1 then
    (if a INPUT_TOKEN = SYM_OP then Act.term op else Act.term cl)
  else Act.done

/-- Decode one row against the input `word`: the remaining input is `word` dropped by `INPUT_POS`. -/
def decodeRow (word : List Brk) (a : Assignment) : MRow :=
  ⟨decodeAct a, decodeStack a, word.drop (a INPUT_POS).toNat⟩

/-- Decode the first `n` rows of a trace into a forward run. (The general `decode` truncates at the
first `done`; the concrete run length is supplied here — the truncation lemma is part of the §5
residual, not needed for the shipped fixed-length witness.) -/
def decodeRun (word : List Brk) (t : VmTrace) (n : Nat) : List MRow :=
  (List.range n).map (fun i => decodeRow word (t.rows.getD i zeroAsg))

/-! ## §2.1 — THE OCCUPANCY PAYOFF: the new circuit tooth makes `decodeStack` DROP NOTHING.

This is the part of the §5 residual the depth↔occupancy tooth (`dyck_stack.rs::occupancy_tooth`,
derived from the accept-set by `DyckStackRefine.occupied_of_sat`) DISCHARGES. Before the tooth,
`decodeStack`'s `filterMap` could silently drop an `EMPTY` hole below the pointer, making the decoded
stack SHORTER than `STACK_DEPTH` and breaking the correspondence with the shift equations. With the
tooth, every cell `[0, STACK_DEPTH)` is a real symbol, so the `filterMap` keeps all of them and the
decoded stack has length EXACTLY `STACK_DEPTH` — the invariant the general `decode_step` threads. -/

/-- A stack cell holding one of the three symbol ids decodes to `some` — never dropped. -/
theorem symOfId_isSome_of_symbol {z : ℤ}
    (h : z = SYM_S ∨ z = SYM_OP ∨ z = SYM_CL) : (symOfId z).isSome := by
  rcases h with h | h | h <;> subst h <;>
    simp [symOfId, SYM_S, SYM_OP, SYM_CL]

/-- `filterMap` over a list all of whose images are `some` keeps every element. -/
theorem length_filterMap_all_some {α β : Type _} (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome) → (l.filterMap f).length = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.filterMap_cons]
    have ha := h a List.mem_cons_self
    cases hfa : f a with
    | none => rw [hfa, Option.isSome_none] at ha; exact absurd ha (by decide)
    | some b =>
      simp only [List.length_cons]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **`decodeStack_length` — THE TOOTH'S PAYOFF, abstractly.** If every cell strictly below the
pointer is a real symbol (the depth↔occupancy invariant), the decoded working stack has length
EXACTLY `STACK_DEPTH`: `filterMap` drops nothing. -/
theorem decodeStack_length (a : Assignment)
    (hocc : ∀ i : Nat, (i : ℤ) < a STACK_DEPTH →
      a (stk i) = SYM_S ∨ a (stk i) = SYM_OP ∨ a (stk i) = SYM_CL) :
    (decodeStack a).length = (a STACK_DEPTH).toNat := by
  unfold decodeStack
  rw [length_filterMap_all_some _ _ (fun i hi => by
        rw [List.mem_range] at hi
        exact symOfId_isSome_of_symbol (hocc i (by omega))),
      List.length_range]

/-- **`decodeStack_length_of_sat` — the payoff on a SATISFYING trace.** The circuit's acceptance
(`Satisfied2`) now CERTIFIES, via `occupied_of_sat`, that the decoded working stack of any transition
row has length exactly its `STACK_DEPTH`. The `EMPTY`-hole failure the general `decode_step` had to
rule out by hand is retired by the tooth. -/
theorem decodeStack_length_of_sat {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (hcanon : DyckCanon t)
    (i : Nat) (hi : i + 1 < t.rows.length) :
    (decodeStack (envAt t i).loc).length = ((envAt t i).loc STACK_DEPTH).toNat := by
  refine decodeStack_length _ (fun j hj => ?_)
  have hbound : 0 ≤ (envAt t i).loc STACK_DEPTH ∧ (envAt t i).loc STACK_DEPTH ≤ 5 :=
    depth_of_sat hsat hcanon i hi
  exact occupied_of_sat hsat hcanon i hi j (by simp only [STACK_D]; omega) hj

/-! ## §2.2 — `decodeStack` AS A MAP, and the DEPTH-POSITIVITY the top-cell tooth gives.

The occupancy tooth (`decodeStack_length`) says the `filterMap` drops nothing; here we go one step
further and give `decodeStack` its explicit `map` form — every live cell decodes to a definite
symbol (`symTot`). That map form is what the shift equations (`bracketPush`/`emptyPop`/`termPop`)
rewrite pointwise into the `MStep` stack relation `b.stk = r.output ++ rest`. The `empty-above`
family of the tooth also lets us read `STACK_DEPTH ≥ 1` off a row whose top cell is a real symbol —
the fact that keeps a `rule rBracket` step from firing on an empty stack. -/

/-- The symbol-id of a terminal (`op ↦ 2`, `cl ↦ 3`) — the inverse of `symOfId` on terminals. -/
def symId : Brk → ℤ
  | Brk.op => SYM_OP
  | Brk.cl => SYM_CL

/-- Total symbol decode: the junk-defaulted total version of `symOfId`. On a real cell
(`∈ {S, op, cl}`) it agrees with `symOfId`; the final branch is never reached under occupancy. -/
def symTot (z : ℤ) : Symbol Brk NTs :=
  if z = SYM_S then Symbol.nonterminal NTs.S
  else if z = SYM_OP then Symbol.terminal op
  else Symbol.terminal cl

/-- On a real cell, `symOfId` is exactly `some ∘ symTot`. -/
theorem symOfId_eq_some_symTot {z : ℤ}
    (h : z = SYM_S ∨ z = SYM_OP ∨ z = SYM_CL) : symOfId z = some (symTot z) := by
  rcases h with h | h | h <;> subst h <;> simp [symOfId, symTot, SYM_S, SYM_OP, SYM_CL]

/-- `symTot` of a terminal's id is that terminal. -/
theorem symTot_symId (x : Brk) : symTot (symId x) = Symbol.terminal x := by
  cases x <;> simp [symTot, symId, SYM_OP, SYM_CL, SYM_S]

/-- `filterMap` of an all-`some` function equals the corresponding `map`. -/
theorem filterMap_all_some_eq_map {α β : Type _} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.filterMap f = l.map g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.filterMap_cons, h a List.mem_cons_self, List.map_cons,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **`decodeStack` in `map` form.** Under the depth↔occupancy invariant, the decoded working stack
is the pointwise `symTot`-image of the live cells: `[symTot STACK[0], …, symTot STACK[D−1]]`. -/
theorem decodeStack_eq_map (a : Assignment)
    (hocc : ∀ i : Nat, (i : ℤ) < a STACK_DEPTH →
      a (stk i) = SYM_S ∨ a (stk i) = SYM_OP ∨ a (stk i) = SYM_CL) :
    decodeStack a = (List.range (a STACK_DEPTH).toNat).map (fun i => symTot (a (stk i))) := by
  unfold decodeStack
  refine filterMap_all_some_eq_map _ _ _ (fun x hx => ?_)
  rw [List.mem_range] at hx
  exact symOfId_eq_some_symTot (hocc x (by omega))

/-- **`decodeStack` in `map` form on a SATISFYING transition row** — the tooth's payoff wired to the
accept-set. Every live cell of a transition row decodes to a definite symbol. -/
theorem decodeStack_eq_map_of_sat {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (hcanon : DyckCanon t)
    (i : Nat) (hi : i + 1 < t.rows.length) :
    decodeStack (envAt t i).loc
      = (List.range ((envAt t i).loc STACK_DEPTH).toNat).map
          (fun k => symTot ((envAt t i).loc (stk k))) := by
  refine decodeStack_eq_map _ (fun j hj => ?_)
  have hbound := depth_of_sat hsat hcanon i hi
  exact occupied_of_sat hsat hcanon i hi j (by simp only [STACK_D]; omega) hj

/-- **`depth_pos_of_top_symbol` — the empty-above tooth read back out.** On a satisfying, canonical
transition row whose TOP cell is a real symbol (`∈ {S, op, cl}`), the depth is at least `1`: the
`empty-above-pointer` gate `STACK[0] · ∏_{v=1}^{5}(STACK_DEPTH − v)` vanishes mod `p`, `p` cannot
divide the (small, nonzero) top, so it must vanish a depth factor — pinning `STACK_DEPTH ∈ {1,…,5}`.
This is what forbids a `rule` step from claiming a nonterminal top off an EMPTY stack. -/
theorem depth_pos_of_top_symbol {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (hcanon : DyckCanon t)
    (i : Nat) (hi : i + 1 < t.rows.length)
    (htop : (envAt t i).loc (stk 0) = SYM_S ∨ (envAt t i).loc (stk 0) = SYM_OP
      ∨ (envAt t i).loc (stk 0) = SYM_CL) :
    1 ≤ (envAt t i).loc STACK_DEPTH := by
  have hgate := dyck_gate hsat i hi (g := emptyAboveBody 0) (by dyck_mem)
  obtain ⟨hc0, hc1⟩ := canon_loc hcanon i (stk 0)
  obtain ⟨DB0, DB1⟩ := depth_of_sat hsat hcanon i hi
  have hd := Int.modEq_zero_iff_dvd.mp hgate
  rw [emptyAboveBody, eval_foldl_mul] at hd
  simp only [STACK_D, EmittedExpr.eval] at hd
  rcases pPrimeInt.dvd_mul.mp hd with htopdvd | hprod
  · exfalso
    obtain ⟨k, hk⟩ := htopdvd
    rcases htop with h | h | h <;> rw [h] at hk <;>
      simp only [SYM_S, SYM_OP, SYM_CL] at hk <;> omega
  · rw [List.map_map] at hprod
    simp only [gSubK] at hprod
    obtain ⟨v, hvmem, hxv⟩ :=
      prime_dvd_map_prod ((envAt t i).loc STACK_DEPTH) DB0 DB1 (List.range' 1 5)
        (fun w hw => by rw [List.mem_range'] at hw; omega) hprod
    rw [List.mem_range'] at hvmem
    omega

/-- `symTot` at the three concrete ids — the leaf rewrites the stack assembly needs. -/
theorem symTot_S : symTot SYM_S = Symbol.nonterminal NTs.S := by simp [symTot, SYM_S]
theorem symTot_OP : symTot SYM_OP = Symbol.terminal op := by simp [symTot, SYM_OP, SYM_S]
theorem symTot_CL : symTot SYM_CL = Symbol.terminal cl := by simp [symTot, SYM_CL, SYM_S, SYM_OP]

/-- **`decodeStack_pop` — the SHIFT-DOWN stack relation** (`emptyPop` / `termPop`). When the next
row's cells are this row's cells shifted down one (`N.STACK[k] = STACK[k+1]` for `k ≤ 3`) and the
depth drops by one, the decoded next stack is exactly this stack with its TOP popped:
`decodeStack L = symTot STACK[0] :: decodeStack N`. Pure list bookkeeping over the length-pinned
(occupancy) decoded stacks — no circuit tooth beyond the ones already read out. -/
theorem decodeStack_pop (L N : Assignment)
    (hoccL : ∀ i : Nat, (i : ℤ) < L STACK_DEPTH →
      L (stk i) = SYM_S ∨ L (stk i) = SYM_OP ∨ L (stk i) = SYM_CL)
    (hoccN : ∀ i : Nat, (i : ℤ) < N STACK_DEPTH →
      N (stk i) = SYM_S ∨ N (stk i) = SYM_OP ∨ N (stk i) = SYM_CL)
    (hpos : 1 ≤ L STACK_DEPTH) (hbnd : L STACK_DEPTH ≤ 5)
    (hdepth : N STACK_DEPTH = L STACK_DEPTH - 1)
    (hshift : ∀ k : Nat, k ≤ 3 → N (stk k) = L (stk (k + 1))) :
    decodeStack L = symTot (L (stk 0)) :: decodeStack N := by
  rw [decodeStack_eq_map L hoccL, decodeStack_eq_map N hoccN]
  obtain ⟨m, hm⟩ : ∃ m : Nat, (L STACK_DEPTH).toNat = m + 1 :=
    ⟨(L STACK_DEPTH).toNat - 1, by omega⟩
  have hmle : m ≤ 4 := by omega
  have hNtn : (N STACK_DEPTH).toNat = m := by omega
  rw [hm, hNtn, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  simp only [Function.comp]
  rw [← hshift k (by omega)]

/-- **`decodeStack_push` — the PUSH-BY-2 stack relation** (`bracketPush`, `S → [ S ]`). The next
stack is the RHS `[ op, S, cl ]` laid over the surviving remainder (this stack minus its `S` top),
so `decodeStack N = op :: S :: cl :: rest` while `decodeStack L = S :: rest`. The depth is bounded
`1 ≤ L.STACK_DEPTH` and `N.STACK_DEPTH = L.STACK_DEPTH + 2 ≤ 5`, so the remainder is at most two
cells — the finite cases the shift equations `hsh3`/`hsh4` cover. -/
theorem decodeStack_push (L N : Assignment)
    (hoccL : ∀ i : Nat, (i : ℤ) < L STACK_DEPTH →
      L (stk i) = SYM_S ∨ L (stk i) = SYM_OP ∨ L (stk i) = SYM_CL)
    (hoccN : ∀ i : Nat, (i : ℤ) < N STACK_DEPTH →
      N (stk i) = SYM_S ∨ N (stk i) = SYM_OP ∨ N (stk i) = SYM_CL)
    (hpos : 1 ≤ L STACK_DEPTH) (hbnd : N STACK_DEPTH ≤ 5)
    (hdepth : N STACK_DEPTH = L STACK_DEPTH + 2)
    (h0 : N (stk 0) = SYM_OP) (h1 : N (stk 1) = SYM_S) (h2 : N (stk 2) = SYM_CL)
    (hsh3 : N (stk 3) = L (stk 1)) (hsh4 : N (stk 4) = L (stk 2))
    (htop : L (stk 0) = SYM_S) :
    ∃ rest, decodeStack L = Symbol.nonterminal NTs.S :: rest
      ∧ decodeStack N = Symbol.terminal op :: Symbol.nonterminal NTs.S
          :: Symbol.terminal cl :: rest := by
  rw [decodeStack_eq_map L hoccL, decodeStack_eq_map N hoccN]
  obtain ⟨m, hm⟩ : ∃ m : Nat, (L STACK_DEPTH).toNat = m + 1 :=
    ⟨(L STACK_DEPTH).toNat - 1, by omega⟩
  have hmle : m ≤ 2 := by omega
  have hNtn : (N STACK_DEPTH).toNat = m + 3 := by omega
  rw [hm, hNtn]
  refine ⟨(List.range m).map (fun k => symTot (L (stk (k + 1)))), ?_, ?_⟩
  · rw [List.range_succ_eq_map, List.map_cons, List.map_map, htop, symTot_S]
    rfl
  · interval_cases m <;>
      simp only [List.range_succ_eq_map, List.range_zero, List.map_cons,
        List.map_nil, h0, h1, h2, hsh3, hsh4, symTot_S, symTot_OP, symTot_CL]

/-! ## §2.3 — `decode_step`: ONE `MStep` of the abstract run, from ONE valid transition row.

This is the structural core the §5 residual named — now proven, not deferred. On a transition row
`i` that is NOT a `done` row, `dyck_sat_imp_row_valid` gives `DyckRowValid`, and the depth↔occupancy
tooth gives the length-pinned decoded stacks; the per-action cell equations
(`bracketPush`/`emptyPop`/`termPop`, assembled by `decodeStack_push`/`decodeStack_pop`) then compose
into the `MStep` stack relation `b.stk = r.output ++ rest`. The `hword` hypothesis pins the tape
columns to the parsed word — the honest "the input columns of `t` spell `word`" of the residual,
load-bearing exactly on the `term` rows (the field-only `INPUT_POS` congruence cannot fix a Nat
position on its own). The `done` self-loop rows are excluded (`hlive`): a halted machine has no
successor step (`MStep .done = False`). -/
theorem decode_step {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (word : List Brk)
    (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (hcanon : DyckCanon t)
    (i : Nat) (hi2 : i + 2 < t.rows.length)
    (hlive : (envAt t i).loc IS_DONE = 0)
    (hword : (envAt t i).loc IS_TERM = 1 → ∃ x : Brk,
      (envAt t i).loc (stk 0) = symId x ∧
      word.drop ((envAt t i).loc INPUT_POS).toNat
        = x :: word.drop ((envAt t (i + 1)).loc INPUT_POS).toNat) :
    MStep (decodeRow word (t.rows.getD i zeroAsg))
          (decodeRow word (t.rows.getD (i + 1) zeroAsg)) := by
  have hi : i + 1 < t.rows.length := by omega
  have hi' : (i + 1) + 1 < t.rows.length := by omega
  have henv : (envAt t i).nxt = (envAt t (i + 1)).loc := rfl
  have rv : DyckRowValid (envAt t i) := dyck_sat_imp_row_valid hsat hcanon i hi
  have hkp := rv.kindPartition
  have hdL := depth_of_sat hsat hcanon i hi
  have hdN : 0 ≤ (envAt t i).nxt STACK_DEPTH ∧ (envAt t i).nxt STACK_DEPTH ≤ 5 := by
    rw [henv]; exact depth_of_sat hsat hcanon (i + 1) hi'
  have hoccL : ∀ j : Nat, (j : ℤ) < (envAt t i).loc STACK_DEPTH →
      (envAt t i).loc (stk j) = SYM_S ∨ (envAt t i).loc (stk j) = SYM_OP
        ∨ (envAt t i).loc (stk j) = SYM_CL := fun j hj =>
    occupied_of_sat hsat hcanon i hi j (by have := hdL.2; simp only [STACK_D]; omega) hj
  have hoccN : ∀ j : Nat, (j : ℤ) < (envAt t i).nxt STACK_DEPTH →
      (envAt t i).nxt (stk j) = SYM_S ∨ (envAt t i).nxt (stk j) = SYM_OP
        ∨ (envAt t i).nxt (stk j) = SYM_CL := by
    intro j hj
    rw [henv] at hj ⊢
    exact occupied_of_sat hsat hcanon (i + 1) hi' j
      (by have := (depth_of_sat hsat hcanon (i + 1) hi').2; simp only [STACK_D]; omega) hj
  have hthread := rv.depthThreads
  show MStep (decodeRow word (envAt t i).loc) (decodeRow word (envAt t i).nxt)
  rcases rv.kindsBoolean.1 with hR | hR
  · -- IS_RULE = 0 ⇒ IS_TERM = 1: a `term` step.
    have hT : (envAt t i).loc IS_TERM = 1 := by omega
    obtain ⟨x, hxtop, hxword⟩ := hword hT
    have htt := rv.termTopIsToken hT
    have hINPUT : (envAt t i).loc INPUT_TOKEN = symId x := htt.symm.trans hxtop
    have hact : decodeAct (envAt t i).loc = Act.term x := by
      cases x <;> simp [decodeAct, hR, hT, hINPUT, symId, SYM_OP, SYM_CL]
    obtain ⟨tp0, tp1, tp2, tp3, _tp4, tpd, tpge⟩ := rv.termPop hT
    have hdepth : (envAt t i).nxt STACK_DEPTH = (envAt t i).loc STACK_DEPTH - 1 := by
      rw [hthread, tpd]
    have hpop := decodeStack_pop (envAt t i).loc (envAt t i).nxt hoccL hoccN tpge hdL.2 hdepth
      (fun k hk => by interval_cases k <;> assumption)
    rw [hxtop, symTot_symId] at hpop
    simp only [MStep, decodeRow, hact]
    refine ⟨?_, decodeStack (envAt t i).nxt, hpop, rfl⟩
    exact hxword
  · -- IS_RULE = 1: a `rule` step; IS_TERM = 0.
    have hTz : (envAt t i).loc IS_TERM = 0 := by omega
    have hnth := rv.nonTermHolds hTz
    have htop := rv.ruleTopIsS hR
    have hsp := rv.subPartition
    rcases rv.subBoolean.1 with hSB | hSB
    · -- SEL_BRACKET = 0 ⇒ SEL_EMPTY = 1: `rule rEmpty`.
      have hSE : (envAt t i).loc SEL_EMPTY = 1 := by rw [hR, hSB] at hsp; omega
      have hRID := rv.emptyPinned hSE
      have hact : decodeAct (envAt t i).loc = Act.rule rEmpty := by
        simp [decodeAct, hR, hRID, RULE_EMPTY, RULE_BRACKET]
      obtain ⟨ep0, ep1, ep2, ep3, _ep4, epd, epge⟩ := rv.emptyPop hSE
      have hdepth : (envAt t i).nxt STACK_DEPTH = (envAt t i).loc STACK_DEPTH - 1 := by
        rw [hthread, epd]
      have hpop := decodeStack_pop (envAt t i).loc (envAt t i).nxt hoccL hoccN epge hdL.2 hdepth
        (fun k hk => by interval_cases k <;> assumption)
      rw [htop, symTot_S] at hpop
      simp only [MStep, decodeRow, hact]
      refine ⟨?_, ?_, decodeStack (envAt t i).nxt, ?_, ?_⟩
      · simp only [dyck]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · rw [hnth]
      · exact hpop
      · simp only [rEmpty, List.nil_append]
    · -- SEL_BRACKET = 1: `rule rBracket`.
      have hRID := rv.bracketPinned hSB
      have hact : decodeAct (envAt t i).loc = Act.rule rBracket := by
        simp [decodeAct, hR, hRID, RULE_BRACKET]
      obtain ⟨bp0, bp1, bp2, bp3, bp4, _bpe3, _bpe4, bpd⟩ := rv.bracketPush hSB
      have hpos := depth_pos_of_top_symbol hsat hcanon i hi (Or.inl htop)
      have hdepth : (envAt t i).nxt STACK_DEPTH = (envAt t i).loc STACK_DEPTH + 2 := by
        rw [hthread, bpd]
      obtain ⟨rest, hL, hN⟩ := decodeStack_push (envAt t i).loc (envAt t i).nxt hoccL hoccN
        hpos hdN.2 hdepth bp0 bp1 bp2 bp3 bp4 htop
      simp only [MStep, decodeRow, hact]
      refine ⟨?_, ?_, rest, ?_, ?_⟩
      · simp only [dyck]; exact Finset.mem_insert_self _ _
      · rw [hnth]
      · simpa only [rBracket] using hL
      · simpa only [rBracket, List.cons_append, List.nil_append] using hN

/-! ## §3 — THE LOOP CLOSED FOR THE SHIPPED WORD.

`witTrace` (slice 3, §5) is the honest `"[]"` parse `build_brackets_witness` lays, PROVEN in the
deployed accept-set by `DyckStackRefine.witTrace_satisfies`. Its 8 rows are `rule rBracket · term
'[' · rule rEmpty · term ']' · done`, padded with `done` self-loops; the run is the first 5. -/

/-- **`decode_witTrace` — the §7 decode seam, CLOSED for the concrete trace.** The satisfying
`witTrace` decodes (STACK cells + depth + selectors + `INPUT_POS`, read directly) to the accepting
forward run `bRow0 :: bracketsRest` — the SAME abstract machine slice 3's `abs_brackets_accepts`
hand-built, now recovered FROM the circuit trace's columns. For this fixed trace the depth↔occupancy
invariant the general seam needs holds by computation, so no circuit tooth is required here. -/
theorem decode_witTrace : decodeRun [op, cl] witTrace 5 = bRow0 :: bracketsRest := by
  rfl

/-- **`witTrace_replays` — the concrete `parse_sat_imp_replay`.** The decoded run assembles, through
the stack-invariant fold `mrun_imp_replay` (via `replay_of_run_initial`), into an accepting Dyck
replay whose reconstructed certificate is `[rBracket, rEmpty]` and whose word is `[op, cl]` — EXACTLY
`CfgCompact.Reference.brackets_replays`'s statement, reached here from the actual circuit trace. -/
theorem witTrace_replays :
    ReplayAccepts dyck (rulesOf (decodeRun [op, cl] witTrace 5)) [op, cl] := by
  rw [decode_witTrace]
  exact replay_of_run_initial bracketsRows_run rfl

/-- **`witTrace_steps_valid` — the satisfaction is load-bearing.** The circuit's ACCEPTANCE of
`witTrace` certifies, through the slice-3 per-row bridge `dyck_sat_imp_row_valid`, that every one of
the four transition rows the run decodes is a genuine pushdown step (`DyckRowValid`). Acceptance ⇒
valid steps (this lemma) and acceptance's trace decodes to the run (`decode_witTrace`); the two
compose into `witTrace_replays`. Nothing here rests on a vacuous hypothesis: `witTrace_satisfies`
inhabits the `Satisfied2` antecedent. -/
theorem witTrace_steps_valid (i : Nat) (hi : i + 1 < 5) : DyckRowValid (envAt witTrace i) :=
  dyck_sat_imp_row_valid witTrace_satisfies witTrace_canon i (by
    have h : witTrace.rows.length = 8 := rfl
    omega)

/-- **`witTrace_in_language` — the consistency check.** `compact_sound` on the produced
`ReplayAccepts` recovers language membership: the parse certificate the circuit trace decodes to
proves `[op, cl] ∈ dyck.language`, the SAME fact slice 3 reaches by hand. -/
theorem witTrace_in_language : [op, cl] ∈ dyck.language :=
  Dregg2.Crypto.CfgCompact.compact_sound dyck
    (rulesOf (decodeRun [op, cl] witTrace 5)) [op, cl] witTrace_replays

/-! ## §4 — THE CLOSED LOOP, stated honestly.

The concrete capstone is the CONJUNCTION: the shipped trace is BOTH accepted by the deployed circuit
predicate AND decodes to an accepting grammar replay. This is "a satisfying trace IS an accepting
leftmost pushdown replay" — for the shipped word, with the satisfaction genuinely established
(`witTrace_satisfies`), not assumed. -/

/-- **THE CAPSTONE (concrete):** `witTrace` satisfies the deployed Dyck descriptor AND decodes to an
accepting Dyck replay. The SAT⇒Replay loop `docs/DESIGN-parse-as-derivation.md` §3 names, closed for
the bracket-pair witness. -/
theorem witTrace_satisfies_and_replays :
    Satisfied2 (fun _ => (0 : ℤ)) dyckDesc (fun _ => 0) (fun _ => (0, 0)) [] witTrace
      ∧ ReplayAccepts dyck (rulesOf (decodeRun [op, cl] witTrace 5)) [op, cl] :=
  ⟨witTrace_satisfies, witTrace_replays⟩

/-! ## §4.5 — THE GENERAL THEOREM: `parse_sat_imp_replay`.

The concrete capstone above rides on `decode_witTrace`'s `rfl`. Here the trace is ARBITRARY: the only
levers are the deployed acceptance predicate (`Satisfied2`), the range-check envelope (`DyckCanon`),
and honest boundary/tape hypotheses. The chain is
`dyck_sat_imp_row_valid` (per row) ⟹ `decode_step` (one `MStep`) ⟹ `mrun_from` (the whole `MRun`,
padding truncated at the first `done`) ⟹ `replay_of_run_initial` ⟹ `ReplayAccepts`. Satisfaction is
genuinely load-bearing: `decode_step`'s stack relation is the assembled per-row cell equations, not a
`rfl` on a fixed constant. -/

/-- A FIRST-ROW boundary gate of `dyckDesc` fires on row `0` (`when_first_row()`). -/
theorem first_boundary {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (hlen : 0 < t.rows.length)
    {b : EmittedExpr} (hmem : VmConstraint2.base (.boundary .first b) ∈ dyckDesc.constraints) :
    b.eval (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 hlen _ hmem
  simp only [VmConstraint2.holdsAt, Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at h
  exact h (by decide)

/-- A FIRST-ROW PI binding of `dyckDesc` fires on row `0`. -/
theorem first_pi {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (hlen : 0 < t.rows.length)
    {col k : Nat} (hmem : VmConstraint2.base (.piBinding .first col k) ∈ dyckDesc.constraints) :
    (envAt t 0).loc col ≡ (envAt t 0).pub k [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 hlen _ hmem
  simp only [VmConstraint2.holdsAt, Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at h
  exact h (by decide)

/-- **`mrun_from` — the forward `MRun` threaded across the trace, padding truncated.** By induction on
the distance `j` from row `k` to the accepting `done` row `n`: each transition row is a genuine
`MStep` (`decode_step`), and the `done` row is the base case (`MFinal`). The `done` self-loop rows
past `n` are simply not part of the run. -/
theorem mrun_from {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (word : List Brk)
    (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (hcanon : DyckCanon t)
    (n : Nat) (hn : n + 1 < t.rows.length)
    (hfin : MFinal (decodeRow word (t.rows.getD n zeroAsg)))
    (hlive : ∀ i, i < n → (envAt t i).loc IS_DONE = 0)
    (hword : ∀ i, i < n → (envAt t i).loc IS_TERM = 1 → ∃ x : Brk,
      (envAt t i).loc (stk 0) = symId x ∧
      word.drop ((envAt t i).loc INPUT_POS).toNat
        = x :: word.drop ((envAt t (i + 1)).loc INPUT_POS).toNat) :
    ∀ j k, k + j = n →
      MRun (decodeRow word (t.rows.getD k zeroAsg))
        ((List.range' (k + 1) j).map (fun i => decodeRow word (t.rows.getD i zeroAsg))) := by
  intro j
  induction j with
  | zero =>
    intro k hk
    have hkn : k = n := by omega
    subst hkn
    simpa using MRun.last hfin
  | succ j ih =>
    intro k hk
    have hkn : k < n := by omega
    have hstep := decode_step word hsat hcanon k (by omega) (hlive k hkn) (hword k hkn)
    have hih := ih (k + 1) (by omega)
    rw [List.range'_succ, List.map_cons]
    exact MRun.step hstep hih

/-- **`parse_sat_imp_replay` — THE GENERAL SOUNDNESS THEOREM.** For ANY trace `t` accepted by the
deployed Dyck descriptor (`Satisfied2 dyckDesc`), canonical (`DyckCanon`), whose public initial
symbol is `S`, whose input columns spell `word` (`hword` / `hfin_inp`), and whose run halts at an
accepting `done` row `n` (`hdone`) with no earlier halt (`hlive`) — there is a compact certificate
`rulesOf (decodeRun word t (n+1))` whose leftmost pushdown replay ACCEPTS `word`. A satisfying trace
IS an accepting Dyck replay. Unlike the concrete `witTrace_replays`, satisfaction is load-bearing
here: `t` is arbitrary, so the acceptance predicate is what forces every decoded row to be a genuine
pushdown step. -/
theorem parse_sat_imp_replay {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (word : List Brk)
    (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (hcanon : DyckCanon t)
    (n : Nat) (hn : n + 1 < t.rows.length)
    (hpi : t.pub PI_INITIAL = SYM_S)
    (hdone : (envAt t n).loc IS_DONE = 1)
    (hlive : ∀ i, i < n → (envAt t i).loc IS_DONE = 0)
    (hword : ∀ i, i < n → (envAt t i).loc IS_TERM = 1 → ∃ x : Brk,
      (envAt t i).loc (stk 0) = symId x ∧
      word.drop ((envAt t i).loc INPUT_POS).toNat
        = x :: word.drop ((envAt t (i + 1)).loc INPUT_POS).toNat)
    (hfin_inp : word.drop ((envAt t n).loc INPUT_POS).toNat = []) :
    ReplayAccepts dyck (rulesOf (decodeRun word t (n + 1))) word := by
  have hlen : 0 < t.rows.length := by omega
  -- head-row boundaries
  have hpos0 : (envAt t 0).loc INPUT_POS = 0 := by
    have hg := first_boundary hsat hlen (b := gSubK INPUT_POS 0) (by dyck_mem)
    simp only [gSubK, EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (canon_loc hcanon 0 INPUT_POS) canon_zero
      ((gate_modEq_iff (by ring)).mp hg)
  have hdepth0 : (envAt t 0).loc STACK_DEPTH = 1 := by
    have hg := first_boundary hsat hlen (b := gSubK STACK_DEPTH 1) (by dyck_mem)
    simp only [gSubK, EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (canon_loc hcanon 0 STACK_DEPTH) canon_one
      ((gate_modEq_iff (by ring)).mp hg)
  have hstk0 : (envAt t 0).loc (stk 0) = SYM_S := by
    have hg := first_pi hsat hlen (col := stk 0) (k := PI_INITIAL) (by dyck_mem)
    rw [show (envAt t 0).pub PI_INITIAL = SYM_S from hpi] at hg
    exact eq_of_modEq_canon (canon_loc hcanon 0 (stk 0)) canon_one hg
  -- head: the decoded initial row
  have hinit : decodeStack (envAt t 0).loc = [Symbol.nonterminal dyck.initial] := by
    rw [decodeStack_eq_map_of_sat hsat hcanon 0 (by omega), hdepth0]
    simp only [Int.toNat_one, List.range_one, List.map_cons, List.map_nil, hstk0, symTot_S]
    rfl
  have hinp : (decodeRow word (t.rows.getD 0 zeroAsg)).inp = word := by
    show word.drop ((envAt t 0).loc INPUT_POS).toNat = word
    rw [hpos0]; rfl
  -- accepting `done` row `n`
  have rvn : DyckRowValid (envAt t n) := dyck_sat_imp_row_valid hsat hcanon n (by omega)
  have hpn := rvn.kindPartition
  have hkbn := rvn.kindsBoolean
  have hRn : (envAt t n).loc IS_RULE = 0 := by
    rcases hkbn.1 with h | h
    · exact h
    · rcases hkbn.2.1 with h2 | h2 <;> omega
  have hTn : (envAt t n).loc IS_TERM = 0 := by
    rcases hkbn.2.1 with h | h
    · exact h
    · rcases hkbn.1 with h2 | h2 <;> omega
  obtain ⟨hdemp, hddepth⟩ := rvn.doneEmpty hdone
  have hactn : decodeAct (envAt t n).loc = Act.done := by
    simp [decodeAct, hRn, hTn]
  have hstkn : decodeStack (envAt t n).loc = [] := by
    rw [decodeStack_eq_map_of_sat hsat hcanon n (by omega), hddepth]
    simp
  have hfin : MFinal (decodeRow word (t.rows.getD n zeroAsg)) := ⟨hactn, hstkn, hfin_inp⟩
  -- the whole forward run
  have hrun := mrun_from word hsat hcanon n hn hfin hlive hword n 0 (by omega)
  simp only [Nat.zero_add] at hrun
  have hdrun : decodeRun word t (n + 1)
      = decodeRow word (t.rows.getD 0 zeroAsg)
        :: (List.range' 1 n).map (fun i => decodeRow word (t.rows.getD i zeroAsg)) := by
    unfold decodeRun
    rw [List.range_eq_range', List.range'_succ, List.map_cons]
  have hres := replay_of_run_initial hrun hinit
  rw [hinp] at hres
  rw [← hdrun] at hres
  exact hres

/-- **`parse_sat_imp_replay_emit` — THE GENERAL SOUNDNESS THEOREM, keyed on the BYTE-PINNED
descriptor.** Identical to `parse_sat_imp_replay` but its acceptance hypothesis is SAT of the
deployed, emit-authored `DyckStackEmit.dyckParseDesc` — the descriptor `DyckStackEmit`'s
`#guard emitVmJson2` byte-pins and `circuit/descriptors/by-name/dyck-parse.json` carries — rather than
the hand-transcribed projection `dyckDesc`. It is `parse_sat_imp_replay` composed with the projection
`DyckStackRefine.sat_emit_imp_sat_dyck` (SAT of the emitted descriptor ⇒ SAT of `dyckDesc`, sound
because `dyckDesc` merely DROPS the orthogonal hash-chain constraints). With this, the whole
parse-as-derivation chain — a satisfying trace IS an accepting Dyck replay — is a theorem about the
SAME object the byte-pin fixes. -/
theorem parse_sat_imp_replay_emit {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (word : List Brk)
    (hsat : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t) (hcanon : DyckCanon t)
    (n : Nat) (hn : n + 1 < t.rows.length)
    (hpi : t.pub PI_INITIAL = SYM_S)
    (hdone : (envAt t n).loc IS_DONE = 1)
    (hlive : ∀ i, i < n → (envAt t i).loc IS_DONE = 0)
    (hword : ∀ i, i < n → (envAt t i).loc IS_TERM = 1 → ∃ x : Brk,
      (envAt t i).loc (stk 0) = symId x ∧
      word.drop ((envAt t i).loc INPUT_POS).toNat
        = x :: word.drop ((envAt t (i + 1)).loc INPUT_POS).toNat)
    (hfin_inp : word.drop ((envAt t n).loc INPUT_POS).toNat = []) :
    ReplayAccepts dyck (rulesOf (decodeRun word t (n + 1))) word :=
  parse_sat_imp_replay word (sat_emit_imp_sat_dyck hsat) hcanon n hn hpi hdone hlive hword hfin_inp

/-! ## §5 — THE GENERAL THEOREM IS CLOSED; the concrete case is now an INSTANCE of it.

The §4.6 residual is discharged. `parse_sat_imp_replay` above is the fully-general bridge:

    Satisfied2 dyckDesc t → DyckCanon t → (boundary/tape hypotheses) →
      ReplayAccepts dyck (rulesOf (decodeRun word t (n+1))) word

for an ARBITRARY trace `t` and word `word`, not a fixed constant. The chain that closes it:

  * (slice 3 §4.1)  `dyck_sat_imp_row_valid` : Satisfied2 → ∀ transition row, DyckRowValid   — PROVEN.
  * (§2.3 here)     `decode_step`            : DyckRowValid + occupancy → one `MStep`         — PROVEN.
  * (§4.5 here)     `mrun_from`              : the whole forward `MRun`, padding truncated    — PROVEN.
  * (slice 3 §6)    `mrun_imp_replay`        : MRun → Replay (via `replay_of_run_initial`)    — PROVEN.

The ONE arrow the residual named — `decode_step`, assembling `bracketPush`/`emptyPop`/`termPop` into
the `MStep` stack relation `b.stk = r.output ++ rest` over the now-length-pinned (occupancy) decoded
stack — is proven purely structurally: `decodeStack_push` / `decodeStack_pop` (§2.2). The
depth↔occupancy tooth it stood on (`DyckStackRefine.occupied_of_sat` + `decodeStack_length_of_sat`)
is read out of the deployed accept-set, not assumed. The `done` self-loop padding is truncated at the
accepting row (`MStep .done = False`).

Below, the shipped `witTrace` is recovered as an INSTANCE of the general theorem — the concrete
capstone `witTrace_replays` (which rode a `decode_witTrace` `rfl`) now also follows from
`parse_sat_imp_replay` with all six antecedents discharged from the actual trace. -/

/-- **`witTrace_replays_via_general` — the concrete case THROUGH the general theorem.** Identical in
statement to `witTrace_replays`, but here the accepting replay is produced by `parse_sat_imp_replay`
with `n = 4` (the accepting `done` row), every hypothesis (initial-symbol PI, the halt row, no earlier
halt, the input-columns-spell-`[op,cl]` tape relation, the fully-consumed tape) discharged by
computation on the deployed witness. The general soundness theorem SUBSUMES the shipped case. -/
theorem witTrace_replays_via_general :
    ReplayAccepts dyck (rulesOf (decodeRun [op, cl] witTrace 5)) [op, cl] :=
  parse_sat_imp_replay [op, cl] witTrace_satisfies witTrace_canon 4 (by decide) (by decide)
    (by decide) (by decide)
    (by intro i hi ht
        interval_cases i <;>
          first
            | exact absurd ht (by decide)
            | exact ⟨op, by decide, by decide⟩
            | exact ⟨cl, by decide, by decide⟩)
    (by decide)

/-! ## §6 — Non-vacuity guards + axiom hygiene. -/

-- The decoded run has all five rows (nothing collapsed).
#guard (decodeRun [op, cl] witTrace 5).length = 5
-- The reconstructed compact certificate has exactly two rules (`rBracket`, `rEmpty`) — the
-- O(tokens) wire form, non-empty, recovered from the circuit trace.
#guard (rulesOf (decodeRun [op, cl] witTrace 5)).length = 2
-- The decoded word is the length-2 bracket pair — the replay is not over the empty input.
#guard (decodeRow [op, cl] witTrace.rows.head!).inp.length = 2

#assert_axioms replay_of_run_initial
#assert_axioms symOfId_isSome_of_symbol
#assert_axioms length_filterMap_all_some
#assert_axioms decodeStack_length
#assert_axioms decodeStack_length_of_sat
#assert_axioms decodeStack_eq_map
#assert_axioms decodeStack_pop
#assert_axioms decodeStack_push
#assert_axioms depth_pos_of_top_symbol
#assert_axioms decode_step
#assert_axioms mrun_from
#assert_axioms parse_sat_imp_replay
#assert_axioms parse_sat_imp_replay_emit
#assert_axioms witTrace_replays_via_general
#assert_axioms decode_witTrace
#assert_axioms witTrace_replays
#assert_axioms witTrace_steps_valid
#assert_axioms witTrace_in_language
#assert_axioms witTrace_satisfies_and_replays

end Dregg2.Circuit.Emit.DyckStackReplay
