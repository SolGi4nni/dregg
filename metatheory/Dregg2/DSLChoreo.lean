/-
# Dregg2.DSLChoreo — the `dregg_choreo { … }` choreography eDSL.

A term-level eDSL that elaborates a readable MPST block directly to a verified
`Coordination.GlobalType`. A `dregg_choreo { … }` term IS a `GlobalType` — so
`Coordination.project` / `Projectable` / `deadlock_freedom_by_design` /
`privacy_by_projection` apply to the exact elaborated term.

The eDSL is a parser onto already-proved constructors (`declare_syntax_cat` + `macro_rules`),
with no new metatheory.

Surface (textbook MPST → `GlobalType`):
  `a ~(label)~> b ; cont`               → `.comm a b label cont`
  `a ~(label)~> b { ℓ . k | ℓ . k }`    → `.choice a b [(ℓ,k), …]`
  `done` / `end`                        → `.done`
  `rec X . body` / `var X`              → `.mu X body` / `.var X`

Roles, labels, and recursion variables are `Nat`s resolved from identifiers (the caller
supplies the symbol table: `def seller : Nat := 0`). The surface uses `~(label)~>` because
`→` is the Lean function-arrow token.

A `dregg_choreo` in the `NoRec` fragment that is `Projectable` and well-scoped (`NoSelfComm`)
inherits the proved `deadlock_freedom_by_design` and `privacy_by_projection` for free.

OPEN: the `NoRec` restriction is required for both inherited theorems (the recursion fragment
is OPEN in `Coordination.lean`).
-/
import Dregg2.Coordination
import Dregg2.Tactics      -- for the `#assert_axioms` honesty pin

namespace Dregg2.DSLChoreo

open Dregg2.Coordination

/-! ## §1 — The syntax category.

One fresh category `dregg_choreo_stmt` isolates the MPST statement grammar from Lean's term
grammar inside the braces. Roles, labels, and recursion variables are written as plain
identifiers (`term`s resolving to `Nat`), mirroring DSL-A's `on m` method resolution. -/

declare_syntax_cat dregg_choreo_stmt

/-! ### The statement atoms.

NB on tokenization: each surface keyword/operator must be a single token. The send arrow is the
ASCII digraph `~(` … `)~>` (the textbook `→` is reserved). Branch alternatives inside a `choice`
are separated by `|`; each alternative is `label . continuation`. -/

-- `a ~(ℓ)~> b ; cont`  →  `.comm a b ℓ cont`  (sequencing communication)
syntax:max term:max " ~(" term ")~> " term:max " ; " dregg_choreo_stmt : dregg_choreo_stmt
-- `a ~(ℓ)~> b { branches }`  →  `.choice a b branches`  (labelled branching)
syntax:max term:max " ~(" term ")~> " term:max " { " sepBy(dregg_choreo_stmt, " | ") " }" : dregg_choreo_stmt
-- a single labelled branch alternative: `label . continuation`  (used inside `{ … | … }`)
syntax:max term:max " . " dregg_choreo_stmt : dregg_choreo_stmt
-- `done` / `end`  →  `.done`
syntax:max "done" : dregg_choreo_stmt
syntax:max "end"  : dregg_choreo_stmt
-- recursion: `rec X . body`  →  `.mu X body`;  `var X`  →  `.var X`
syntax:max "rec " term:max " . " dregg_choreo_stmt : dregg_choreo_stmt
syntax:max "var " term:max : dregg_choreo_stmt

/-! ## §2 — Elaboration (`macro_rules`) — the parser onto `GlobalType`.

Each rule translates one MPST atom to the EXACT `GlobalType` constructor. A `choice`'s branch
alternatives (`ℓ . k`) elaborate to `(ℓ, k)` pairs via the `dregg_branch%` helper. The whole
thing is a syntactic `macro` (no `elab` context needed — roles/labels/vars resolve as ordinary
`Nat` term references). -/

/-- Elaborate one `dregg_choreo_stmt` to a `GlobalType` term. -/
syntax (name := dreggChoreoElab) "dregg_choreo% " dregg_choreo_stmt : term
/-- Elaborate a single branch alternative `ℓ . k` to a `(Label × GlobalType)` pair term. -/
syntax (name := dreggBranchElab) "dregg_branch% " dregg_choreo_stmt : term

macro_rules
  | `(dregg_choreo% $a:term ~($ℓ:term)~> $b:term ; $cont) =>
      `(GlobalType.comm $a $b $ℓ (dregg_choreo% $cont))
  | `(dregg_choreo% $a:term ~($_ℓ:term)~> $b:term { $brs|* }) =>
      -- the surface offer-sort `$_ℓ` is decorative: `GlobalType.choice` carries no top-level
      -- label (the selector labels live per-branch), so it is intentionally not threaded.
      `(GlobalType.choice $a $b [ $[(dregg_branch% $brs)],* ])
  | `(dregg_choreo% done) => `(GlobalType.done)
  | `(dregg_choreo% end)  => `(GlobalType.done)
  | `(dregg_choreo% rec $X:term . $body) =>
      `(GlobalType.mu $X (dregg_choreo% $body))
  | `(dregg_choreo% var $X:term) => `(GlobalType.var $X)

macro_rules
  | `(dregg_branch% $ℓ:term . $k) => `(($ℓ, (dregg_choreo% $k)))

/-! ## §3 — The top-level `dregg_choreo { … }` block.

A `dregg_choreo { stmt }` wraps a single statement (the root of the choreography) and elaborates
to its `GlobalType`. (Sequencing is expressed *inside* the statement via `;`, exactly as MPST
global types nest — there is no statement *list* at the top level, just the one root `G`.) -/

/-- `dregg_choreo { stmt }` → a `Coordination.GlobalType`. -/
syntax (name := dreggChoreo) "dregg_choreo " "{ " dregg_choreo_stmt " }" : term

macro_rules
  | `(dregg_choreo { $s }) => `(dregg_choreo% $s)

/-! ## §4 — Worked example: a 2-party request/response.

`client` requests (label `req`) from `server`; `server` responds (label `resp`); `end`.
Roles/labels are plain `Nat` defs. Elaborates to exactly the hand-written `GlobalType`,
proved by `rfl`. -/

/-- Roles and labels for the request/response example (the symbol table). -/
def client : Role  := 0
def server : Role  := 1
def req    : Label := 10
def resp   : Label := 11

/-- The request/response choreography, written in the eDSL. -/
def reqResp : GlobalType := dregg_choreo {
  client ~(req)~> server ;
  server ~(resp)~> client ;
  done
}

/-- The eDSL request/response IS exactly the hand-written `GlobalType` — proved by `rfl`. -/
theorem reqResp_eq :
    reqResp = GlobalType.comm 0 1 10 (GlobalType.comm 1 0 11 GlobalType.done) := rfl

#assert_axioms reqResp_eq

/-! ## §5 — Worked example: the auction (`choice` branching).

`seller ~(item)~> bidder { accept . done | reject . done }`: seller offers an item; bidder
selects `accept` or `reject`. Elaborates to the `.choice` term by `rfl`. -/

/-- Roles/labels for the auction (the symbol table). -/
def seller : Role  := 0
def bidder : Role  := 1
def item   : Label := 20
def accept : Label := 1
def reject : Label := 2

/-- The auction choreography, written in the eDSL (`seller→bidder {accept.done | reject.done}`). -/
def auction : GlobalType := dregg_choreo {
  seller ~(item)~> bidder {
      accept . done
    | reject . done
  }
}

/-- **The auction elaborates to exactly its `.choice` `GlobalType` — by `rfl`.** -/
theorem auction_eq :
    auction = GlobalType.choice 0 1 [(1, GlobalType.done), (2, GlobalType.done)] := rfl

#assert_axioms auction_eq

/-! ## §6 — Inherited deadlock-freedom + projection-privacy.

The auction is `NoRec`, well-scoped (`NoSelfComm`), `Guarded`, and `Projectable` — the
hypotheses of the inherited theorems. It therefore inherits, as theorems about this elaborated
term:
  * `Coordination.deadlock_freedom_by_design` — every reachable non-`done` residual has a `Dual`
    head pair (progress by construction);
  * `Coordination.privacy_by_projection` — any uninvolved role projects to `done`. -/

/-! The four well-formedness side-conditions. `NoRec`/`NoSelfComm`/`Guarded`/`Projectable` are
`Prop`-valued mutual recursions with no `Decidable` instance; we discharge each by structural
`simp`-unfolding with `src ≠ dst` / `bs ≠ []` obligations by `decide`. -/

/-- The auction is recursion-free (`NoRec`): its only constructors are `choice`/`done`. -/
example : NoRec auction := by
  simp only [auction, seller, bidder, accept, reject, NoRec, NoRecBranches, and_self]
/-- The auction is well-scoped — no role talks to itself (`seller ≠ bidder`). -/
example : NoSelfComm auction := by
  refine ⟨by decide, ?_⟩
  simp only [NoSelfCommBranches, NoSelfComm, and_self]
/-- The auction is guarded — its choice has a nonempty branch list. -/
example : Guarded auction := by
  refine ⟨by simp, ?_⟩
  simp only [GuardedBranches, Guarded, and_self]

/-- **The auction is `Projectable`** — every role projects successfully (the merge in the only
`choice` reconciles). The branching is driven by `bidder`/`seller` as offerer/selector, so no
*passive* role's `MergesAt` can fail; we discharge it by `MergesAt`/`MergesAtMap` unfolding at
each occurring role. This is the projectability side-condition the inherited privacy and fidelity
theorems take as hypothesis. -/
theorem auction_projectable : Projectable auction := by
  intro p hp
  simp only [auction, seller, bidder, accept, reject, roles, rolesBranches, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    · show MergesAt auction _
      simp only [auction, seller, bidder, accept, reject, MergesAt, MergesAtMap]
      split <;> trivial

#assert_axioms auction_projectable

/-- **Inherited deadlock-freedom for the eDSL auction.** `Coordination.deadlock_freedom_by_design`
instantiated at `auction`: every reachable non-`done` residual has an enabled (`Dual`)
communication. -/
theorem auction_deadlock_free
    (G' : GlobalType) (hreach : GReach auction G') (hdone : G' ≠ GlobalType.done) :
    ∃ (a b : Role), a ≠ b ∧ Dual (project G' a) (project G' b) :=
  deadlock_freedom_by_design auction
    (by simp only [auction, seller, bidder, accept, reject, NoRec, NoRecBranches, and_self])
    (by refine ⟨by decide, ?_⟩; simp only [NoSelfCommBranches, NoSelfComm, and_self])
    G' hreach hdone

#assert_axioms auction_deadlock_free

/-- **Inherited projection-privacy for the eDSL auction.** `Coordination.privacy_by_projection`
instantiated at `auction`: role `7` (not in the protocol) projects to `done`. -/
theorem auction_privacy_uninvolved : project auction 7 = LocalType.done :=
  privacy_by_projection auction
    (by simp only [auction, seller, bidder, accept, reject, NoRec, NoRecBranches, and_self])
    7
    (by simp only [auction, seller, bidder, accept, reject, roles, rolesBranches, List.append_nil,
          List.mem_cons, List.not_mem_nil]; decide)

#assert_axioms auction_privacy_uninvolved

/-! ## §7 — Recursion surface smoke-tests (`rec X . body` / `var X`).

The recursion constructors elaborate — a recursive ping loop. OPEN: a choreography using
`rec`/`var` is not `NoRec` and does not inherit the §6 guarantees. These pin the surface→term
map by `rfl`. -/

def alice : Role := 0
def bob   : Role := 1
def ping  : Label := 30
def loop  : TyVar := 0

/-- A recursive ping loop: `rec loop . alice ~(ping)~> bob ; var loop`. -/
def pingLoop : GlobalType := dregg_choreo {
  rec loop .
    alice ~(ping)~> bob ;
    var loop
}

/-- **The recursive loop elaborates to exactly its `.mu`/`.var` `GlobalType` — by `rfl`.** -/
theorem pingLoop_eq :
    pingLoop = GlobalType.mu 0 (GlobalType.comm 0 1 30 (GlobalType.var 0)) := rfl

#assert_axioms pingLoop_eq

/-- A bare variable surface atom elaborates to `.var`. -/
example : (dregg_choreo { var loop } : GlobalType) = GlobalType.var 0 := rfl
/-- `end` is a synonym for `done`. -/
example : (dregg_choreo { end } : GlobalType) = GlobalType.done := rfl

/-! ## §8 — Elaboration-time projectability check.

`#check_projectable e` evaluates `Projectable`/`NoSelfComm`/`Guarded` on the elaborated
`GlobalType` `e` at elaboration time and fails with a readable message if the conditions do not
hold. Implemented via `decide`-style evaluation inside a `CommandElab`.

OPEN: checks only the `NoRec`-fragment hypotheses; a `rec`/`var` choreography elaborates but is
outside the guaranteed fragment. -/

/-- **`discharge_projectable`** — a structural tactic proving `NoSelfComm G ∧ Guarded G ∧ Projectable G`
for a ground `NoRec`-fragment `G`. Unfolds the three predicates; reduces `NoSelfComm`/`Guarded`
to `src ≠ dst` / `bs ≠ []` (`decide`); discharges `Projectable` by unfolding `project` /
`projectBranches` / `mergeLocal`. Fails on a non-projectable or ill-scoped `G`. -/
macro "discharge_projectable" : tactic =>
  `(tactic|
    (refine ⟨?_, ?_, ?_⟩
     all_goals
       first
       | -- the `Projectable` conjunct: ∀ role ∈ roles G, MergesAt G role
         (intro p hp
          simp only [roles, rolesBranches, List.append_nil, List.append_assoc, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
          repeat' (rcases hp with rfl | hp)
          all_goals
            (simp only [MergesAt, MergesAtMap, projectBranches, project, mergeLocal]
             repeat' (first | split | constructor | trivial)
             all_goals trivial))
       | -- the `NoSelfComm` / `Guarded` conjuncts: structural ≠/nonempty obligations
         (simp only [NoSelfComm, NoSelfCommBranches, Guarded, GuardedBranches, ne_eq,
            reduceCtorEq, not_false_eq_true, List.cons_ne_nil]
          repeat' (first | constructor | decide | trivial))))

open Lean Elab Command Meta in
/-- `#check_projectable e` — fail elaboration unless `e` is `NoSelfComm`, `Guarded`, and
`Projectable`. Reduces `e` to constructor form (`reduceAll`) and attempts `discharge_projectable`;
fails loudly if the conjunction cannot be proved. -/
elab "#check_projectable " e:term : command => do
  liftTermElabM do
    let g ← Term.elabTermAndSynthesize e (some (.const ``GlobalType []))
    let g ← reduceAll g
    let gs ← Term.exprToSyntax g
    let stx ← `(term| (by discharge_projectable :
      NoSelfComm $gs ∧ Guarded $gs ∧ Projectable $gs))
    try
      let prf ← Term.elabTermAndSynthesize stx (some (.sort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      let _ ← instantiateMVars prf
    catch ex =>
      throwError "dregg_choreo: choreography is NOT projectable / well-scoped \
        (NoSelfComm ∧ Guarded ∧ Projectable could not be discharged).\n{← ex.toMessageData.toString}"

-- The auction passes the elaboration-time check.
#check_projectable auction
-- The request/response also passes (no branching ⇒ trivially projectable; distinct roles).
#check_projectable reqResp

end Dregg2.DSLChoreo
