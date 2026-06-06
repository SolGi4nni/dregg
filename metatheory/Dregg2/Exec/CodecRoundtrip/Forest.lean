import Dregg2.Exec.CodecRoundtrip.Auth
import Dregg2.Exec.CodecRoundtrip.Action
import Dregg2.Exec.CodecRoundtrip.SideTables

/-!
Submodule of `Dregg2.Exec.CodecRoundtrip` — split for parallel compilation.
-/

namespace Dregg2.Exec.CodecRoundtrip

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide
open Dregg2.Exec.TurnExecutorFull (QueueTxOpA)

/-! ## §15 — the RECURSIVE action-TREE (`parseForestW`/`parseChildrenW`) roundtrip — FILL-J production
(the call-FOREST + delegation edges). THE hardest production: a four-way mutual recursion (`parseForestW`
/ `parseChildrenW` / `parseChildrenLoopW` / `parseChildW`), each fuel-bounded for structural termination.
A node `{"auth":AUTH,"caveats":WCAVEATS,"action":ACTIONW,"children":KIDS}` carries the per-node credential
(§6 `parseAuthW_roundtrip`, the WHO), the tiered caveats (§11d `parseCaveatsW_encode`, the discharge leg),
the 51-arm action (§7 `parseActionW_roundtrip`/`_setfield`, the WHAT), and the delegated children, each a
`{"holder":N,"keep":AUTHS,"cap":CAP,"sub":NODE}` edge carrying its attenuation `keep` (§8
`parseAuths_encode`), the delegated `parentCap` (§13 `parseCap_encode`), and the recursive sub-tree.

It mirrors §6's `authGoal_all` exactly: a bundled mutual goal (forest / children-list / children-loop),
strong-induction on fuel, the recursive `children` arm threading fuel through the edge list as §6's
`oneOf` threads it through the candidate list. The ONE structural delta from §6 is the EXTRA `parseChildW`
fuel layer between the children-loop and the recursive `parseForestW` call: the loop decrements once to
reach `parseChildW`, which decrements again to reach `parseForestW`. So `childrenSize` charges `+2` per
edge (vs §6's `+1`), guaranteeing two fuel units survive each descent. A symmetric codec bug anywhere in
the tree — a forged credential on a deep node, a dropped delegation edge, a mis-bracketed sub-tree —
passes the differential silently; this theorem, pinning `parseForestW` as the genuine left-inverse of
`encodeForestW`, catches it, removing the whole action-tree codec from the Lean-side TCB. -/

/-! ### §15a — well-formedness (the codec boundary, mutual over the tree). The node's `auth` carries the
§6 `WfAuth` boundary (digests `< 2^256`), its `caveats` the §11d `WfCaveats` (`tier ≤ 3`), and its
`action` an escape-free `setFieldA` field name (every other arm is unconstrained); children recurse. -/

mutual
/-- Well-formed `WForest`: a well-formed credential (§6), well-formed caveats (§11d), a well-formed action
(escape-free `setFieldA` name), and well-formed children (recursively). Constructor-pattern form (the
structural recursion the termination checker needs sees `sub`/`kids` as subterms). -/
def WfForest : WForest → Prop
  | ⟨na, cavs, a, kids⟩ => WfAuth na ∧ WfCaveats cavs ∧ WfActionW a ∧ WfChildren kids
/-- Well-formed child-edge list: each edge's sub-tree is well-formed (the `keep`/`parentCap` are narrow
total codecs — no boundary). -/
def WfChildren : List WChild → Prop
  | []                  => True
  | ⟨_, _, _, sub⟩ :: cs => WfForest sub ∧ WfChildren cs
end

/-! ### §15b — the structural fuel measure (mutual). Each EDGE charges `+2` (the children-loop +
`parseChildW` double fuel descent to the recursive sub-tree), plus the sub-tree's own size; the node
charges `+1` over its credential and children. The fuel-adequacy: this measure DOMINATES the parse depth,
so each `fuel=0`/decremented sub-call lands with fuel to spare. -/
mutual
/-- Structural size of a `WForest`: `1 + authSize auth + childrenSize children`. Constructor-pattern form. -/
def forestSize : WForest → Nat
  | ⟨na, _, _, kids⟩ => 1 + authSize na + childrenSize kids
/-- Structural size of a child-edge list: `Σ (2 + forestSize sub)` (the `+2` covers the two fuel layers
between the children-loop and the recursive `parseForestW`). -/
def childrenSize : List WChild → Nat
  | []                  => 0
  | ⟨_, _, _, sub⟩ :: cs => 2 + forestSize sub + childrenSize cs
end

/-! ### §15c — the EDGE-list (KIDS) tail encoder normalized into peelable cons form (mirroring §6d). -/

/-- The `KIDS` tail encoder (the `foldl` body in cons-recursive form). -/
def encodeChildrenTailW (cs : List WChild) : String :=
  cs.foldl (fun acc x => acc ++ "," ++ encodeChildW x) ""

/-- Every `encodeChildW` edge opens with `'{'` — the head making `lit "[]"` fail on a `[{`-led KIDS body.
Explicit witness ⇒ no metavar. -/
private theorem encodeChildW_head (c : WChild) : ∃ t, (encodeChildW c).toList = '{' :: t := by
  obtain ⟨h, k, pc, sub⟩ := c
  refine ⟨("\"holder\":" ++ toString h ++ ",\"keep\":" ++ encodeAuthsW k ++ ",\"cap\":" ++ encodeCap pc
    ++ ",\"sub\":" ++ encodeForestW sub ++ "}" : String).toList, ?_⟩
  show (encodeChildW ⟨h, k, pc, sub⟩).toList = _
  unfold encodeChildW
  simp only [String.toList_append, show ("{\"holder\":":String).toList = '{' :: "\"holder\":".toList from by decide,
    List.cons_append, List.nil_append, List.append_assoc]

/-- The accumulator pulls OUT of the tail fold (`List Char`-level, mirroring `foldl_authtail`). -/
private theorem foldl_childrenTailW (cs : List WChild) : ∀ (acc : String),
    cs.foldl (fun s x => s ++ "," ++ encodeChildW x) acc
      = acc ++ cs.foldl (fun s x => s ++ "," ++ encodeChildW x) "" := by
  induction cs with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeChildW b), ih ("" ++ "," ++ encodeChildW b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

/-- Rebracket a NON-EMPTY edge TAIL `,EDGE ++ TAIL` into comma-then-edge-then-tail (peelable). -/
theorem encChildrenTailW_cons_shape (b : WChild) (bs : List WChild) (rest : PState) :
    (encodeChildrenTailW (b :: bs)).toList ++ rest
      = ',' :: ((encodeChildW b).toList ++ ((encodeChildrenTailW bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeChildrenTailW (b :: bs)
      = ("" ++ "," ++ encodeChildW b) ++ encodeChildrenTailW bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeChildW x) "" = _
      rw [List.foldl_cons]; exact foldl_childrenTailW bs ("" ++ "," ++ encodeChildW b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

/-- Rebracket a NON-EMPTY edge LIST `[EDGE ++ TAIL ++ ]` into open-`[`-then-body form. -/
theorem encodeChildrenW_cons_shape (a : WChild) (as : List WChild) (rest : PState) :
    (encodeChildrenW (a :: as)).toList ++ rest
      = '[' :: ((encodeChildW a).toList ++ ((encodeChildrenTailW as).toList ++ (']' :: rest))) := by
  conv_lhs => rw [show encodeChildrenW (a :: as)
                = "[" ++ encodeChildW a ++ encodeChildrenTailW as ++ "]" from by
              unfold encodeChildrenW; rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-! ### §15d — the NODE/EDGE `do`-block element shapes (rebracket into the parser-step sequence).

`encodeForestW`/`encodeChildW` are `String ++` chains; we rebracket each into the right-associated
`tag ++ (field ++ (sep ++ …))` form the `lit`/sub-parse steps consume. Following §11's perf gotchas: a
single `String.toList_append`/`List.append_assoc` `simp only` (NOT full `simp`) right-associates the
whole chain, and the closing `}` is exposed as `'}' :: rest`. -/

/-- Rebracket the NODE encoding into the `{"auth":` ++ AUTH ++ ,"caveats": ++ … sequence. -/
theorem encForestW_node_shape (na : AuthW) (cavs : List WCaveat) (a : TurnExecutorFull.FullActionA)
    (kids : List WChild) (rest : PState) :
    (encodeForestW ⟨na, cavs, a, kids⟩).toList ++ rest
      = ("{\"auth\":":String).toList ++ ((encodeAuthW na).toList
          ++ ((",\"caveats\":":String).toList ++ ((encodeCaveatsW cavs).toList
          ++ ((",\"action\":":String).toList ++ ((encodeActionW a).toList
          ++ ((",\"children\":":String).toList ++ ((encodeChildrenW kids).toList
          ++ ('}' :: rest)))))))) := by
  show (encodeForestW ⟨na, cavs, a, kids⟩).toList ++ rest = _
  unfold encodeForestW
  simp only [String.toList_append, show ("}":String).toList = ['}'] from by decide,
    List.append_assoc, List.cons_append, List.nil_append]

/-- Rebracket one EDGE encoding into the `{"holder":` ++ N ++ ,"keep": ++ … sequence. -/
theorem encChildW_edge_shape (h : CellId) (k : List Authority.Auth) (pc : Authority.Cap)
    (sub : WForest) (rest : PState) :
    (encodeChildW ⟨h, k, pc, sub⟩).toList ++ rest
      = ("{\"holder\":":String).toList ++ ((toString h).toList
          ++ ((",\"keep\":":String).toList ++ ((encodeAuthsW k).toList
          ++ ((",\"cap\":":String).toList ++ ((encodeCap pc).toList
          ++ ((",\"sub\":":String).toList ++ ((encodeForestW sub).toList
          ++ ('}' :: rest)))))))) := by
  show (encodeChildW ⟨h, k, pc, sub⟩).toList ++ rest = _
  unfold encodeChildW
  simp only [String.toList_append, show ("}":String).toList = ['}'] from by decide,
    List.append_assoc, List.cons_append, List.nil_append]

/-! ### §15e — the bundled fuel-adequate roundtrip (forest / children-list / children-loop, by strong
induction on fuel). Mirrors §6e: establish the LOOP clause (depends on the IH at strictly-smaller fuel
through `parseChildW`'s sub-tree call), then the LIST clause re-uses it at the same fuel, then the FOREST
clause runs the node `do`-block (auth §6 → caveats §11d → action §7 → children via the LIST clause). -/

/-- The bundled mutual goal at a given fuel: the forest parser, the children-list parser, and the
children-loop body all recover their argument whenever the fuel meets the `forestSize`/`childrenSize`
bound. The loop clause is stated over the loop BODY (post opening-`[`): the first edge, the
comma-prefixed tail, then the closing `]`. -/
private def ForestGoal (fuel : Nat) : Prop :=
  (∀ (f : WForest) (rest : PState), WfForest f → forestSize f ≤ fuel →
      parseForestW fuel ((encodeForestW f).toList ++ rest) = some (f, rest))
  ∧ (∀ (cs : List WChild) (rest : PState), WfChildren cs → childrenSize cs ≤ fuel →
      parseChildrenW fuel ((encodeChildrenW cs).toList ++ rest) = some (cs, rest))
  ∧ (∀ (a : WChild) (as' : List WChild) (rest : PState), WfForest a.sub → WfChildren as' →
        childrenSize (a :: as') ≤ fuel →
      parseChildrenLoopW fuel ((encodeChildW a).toList ++ ((encodeChildrenTailW as').toList ++ (']' :: rest)))
        = some (a :: as', rest))

set_option maxHeartbeats 1000000 in
/-- **The combined action-TREE fuel-adequate roundtrip.** By STRONG induction on fuel; each recursive
sub-call lands at strictly-smaller fuel (the `+2` edge charge guarantees the `parseChildW`→`parseForestW`
double descent stays funded), so the IH applies. The engine; the public `parseForestW_roundtrip` /
`parseChildrenW_roundtrip` below unwrap it. -/
private theorem forestGoal_all : ∀ fuel, ForestGoal fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    -- LOOP clause first (depends only on IH at strictly-smaller fuel through `parseChildW`).
    have hloop : ∀ (a : WChild) (as' : List WChild) (rest : PState), WfForest a.sub → WfChildren as' →
        childrenSize (a :: as') ≤ fuel →
        parseChildrenLoopW fuel ((encodeChildW a).toList ++ ((encodeChildrenTailW as').toList ++ (']' :: rest)))
          = some (a :: as', rest) := by
      intro a as' rest hwfa hwfas hsz
      obtain ⟨h, k, pc, sub⟩ := a
      -- `childrenSize (⟨h,k,pc,sub⟩::as')` reduces DEFINITIONALLY (constructor match) to the RHS:
      have hsz' : 2 + forestSize sub + childrenSize as' ≤ fuel := hsz
      -- two fuel layers: loop (g+1) → childW (g) where g ≥ 1 + forestSize sub + ...
      obtain ⟨g, rfl⟩ : ∃ k', fuel = k' + 1 := ⟨fuel - 1, by omega⟩
      unfold parseChildrenLoopW
      -- the loop's `parseChildW g` step: rebracket the edge, walk holder/keep/cap, then the sub-tree.
      obtain ⟨g', rfl⟩ : ∃ k', g = k' + 1 := ⟨g - 1, by omega⟩
      have hsubfuel : forestSize sub ≤ g' := by omega
      have hparseChild : parseChildW (g' + 1) ((encodeChildW ⟨h, k, pc, sub⟩).toList
            ++ ((encodeChildrenTailW as').toList ++ (']' :: rest)))
          = some (⟨h, k, pc, sub⟩, ((encodeChildrenTailW as').toList ++ (']' :: rest))) := by
        unfold parseChildW
        rw [encChildW_edge_shape h k pc sub ((encodeChildrenTailW as').toList ++ (']' :: rest))]
        rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
        rw [parseNat_toString h _ (Or.inr ⟨',', _, by
              rw [show (",\"keep\":":String).toList = ',' :: ("\"keep\":":String).toList from by decide]; rfl,
            by decide⟩)]
        simp only [Option.bind_eq_bind, Option.bind]
        rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
        rw [show parseAuthsW = parseAuths from rfl, show encodeAuthsW k = encodeAuths k from rfl,
            parseAuths_encode k _]
        simp only [Option.bind_eq_bind, Option.bind]
        rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
        rw [parseCap_encode pc _]; simp only [Option.bind_eq_bind, Option.bind]
        rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
        -- the recursive sub-tree via the IH at g' < g'+1 = g < g+1 = fuel:
        rw [(IH g' (by omega)).1 sub _ hwfa hsubfuel]
        simp only [Option.bind_eq_bind, Option.bind]
        rw [lit_brace]
      rw [hparseChild]
      simp only []
      cases as' with
      | nil =>
          simp only [show (encodeChildrenTailW ([] : List WChild)).toList = [] from rfl, List.nil_append]
          rw [show lit "," (']' :: rest) = none from by
                rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
                exact lit_ne_pre "," "]" rest (by decide) (by decide)]
          simp only []
          rw [lit_brack]
      | cons a2 as2 =>
          obtain ⟨h2, k2, pc2, sub2⟩ := a2
          -- `WfChildren (⟨..⟩::as2)` / `childrenSize (⟨..⟩::as2)` now reduce (constructor match):
          obtain ⟨hwfa2, hwfas2⟩ : WfForest sub2 ∧ WfChildren as2 := hwfas
          rw [encChildrenTailW_cons_shape ⟨h2, k2, pc2, sub2⟩ as2 (']' :: rest), lit_commaC]
          simp only []
          -- the loop RECURSES at `g'+1` (`parseChildrenLoopW (g+1)` calls `parseChildrenLoopW g`, g=g'+1):
          have hszrec : childrenSize (⟨h2, k2, pc2, sub2⟩ :: as2) ≤ g' + 1 := by
            have hh : 2 + forestSize sub + (2 + forestSize sub2 + childrenSize as2) ≤ g' + 1 + 1 := hsz'
            show 2 + forestSize sub2 + childrenSize as2 ≤ g' + 1
            omega
          rw [(IH (g' + 1) (by omega)).2.2 ⟨h2, k2, pc2, sub2⟩ as2 rest hwfa2 hwfas2 hszrec]
    -- LIST clause (re-uses `hloop` at the SAME fuel).
    have hlistW : ∀ (cs : List WChild) (rest : PState), WfChildren cs → childrenSize cs ≤ fuel →
        parseChildrenW fuel ((encodeChildrenW cs).toList ++ rest) = some (cs, rest) := by
      intro cs rest hwf hsz
      match cs with
      | [] =>
          unfold parseChildrenW
          simp only [encodeChildrenW]
          rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
      | a :: as' =>
          obtain ⟨h, k, pc, sub⟩ := a
          obtain ⟨hwfa, hwfas⟩ : WfForest sub ∧ WfChildren as' := hwf
          unfold parseChildrenW
          rw [encodeChildrenW_cons_shape ⟨h, k, pc, sub⟩ as' rest]
          have hempty : lit "[]"
              ('[' :: ((encodeChildW ⟨h, k, pc, sub⟩).toList ++ ((encodeChildrenTailW as').toList ++ (']' :: rest)))) = none := by
            obtain ⟨t, ht⟩ := encodeChildW_head ⟨h, k, pc, sub⟩
            rw [ht, List.cons_append]; rfl
          rw [hempty]; simp only []
          rw [lit_lbrack]
          exact hloop ⟨h, k, pc, sub⟩ as' rest hwfa hwfas hsz
    refine ⟨?_, hlistW, hloop⟩
    -- FOREST clause: the node `do`-block (auth §6 → caveats §11d → action §7 → children via `hlistW`).
    intro f rest hwf hsz
    obtain ⟨na, cavs, a, kids⟩ := f
    -- `WfForest ⟨..⟩` / `forestSize ⟨..⟩` reduce DEFINITIONALLY (constructor match):
    obtain ⟨hwfna, hwfcavs, hwfa, hwfkids⟩ : WfAuth na ∧ WfCaveats cavs ∧ WfActionW a ∧ WfChildren kids := hwf
    have hsz' : 1 + authSize na + childrenSize kids ≤ fuel := hsz
    obtain ⟨f', rfl⟩ : ∃ k', fuel = k' + 1 := ⟨fuel - 1, by omega⟩
    have hnafuel : authSize na ≤ f' := by omega
    have hkidsfuel : childrenSize kids ≤ f' := by omega
    unfold parseForestW
    rw [encForestW_node_shape na cavs a kids rest]
    rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
    -- auth via §6 (parser calls `parseAuthW f'`; the IH-independent public roundtrip suffices):
    rw [parseAuthW_roundtrip na _ hwfna f' hnafuel]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
    -- caveats via §11d:
    rw [parseCaveatsW_encode cavs _ hwfcavs]; simp only [Option.bind_eq_bind, Option.bind]
    rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
    -- action via §7 (the unified leaf):
    rw [parseActionW_any a _ hwfa]; simp only [Option.bind_eq_bind, Option.bind]
    rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
    -- children: the parser calls `parseChildrenW f'` (DECREMENTED) — use the IH's LIST clause at `f'`:
    rw [(IH f' (by omega)).2.1 kids _ hwfkids hkidsfuel]; simp only [Option.bind_eq_bind, Option.bind]
    rw [lit_brace]

/-! ### §15f — the public FILL-J action-TREE roundtrip facts (the call-forest decoder leaves the TCB). -/

/-- **FILL J production (the action-TREE): the FULL `WForest` roundtrip.** Every well-formed action tree —
including the recursive delegated children — round-trips through `encodeForestW`/`parseForestW`, given
fuel `≥ forestSize f` (the structural tree-depth bound). The node's credential (§6), caveats (§11d),
action (§7), and each child's `keep`/`parentCap` (§8/§13) round-trip; the recursion is REAL (children call
back into the forest parser). This REMOVES the whole action-tree codec — the call-forest the wholesale
swap marshals — from the Lean-side TCB. -/
theorem parseForestW_roundtrip (f : WForest) (rest : PState) (hwf : WfForest f) (fuel : Nat)
    (hfuel : forestSize f ≤ fuel) :
    parseForestW fuel ((encodeForestW f).toList ++ rest) = some (f, rest) :=
  (forestGoal_all fuel).1 f rest hwf hfuel

/-- **The KIDS (children edge-list) roundtrip** (`parseChildrenW ∘ encodeChildrenW = id`) — the delegation
edges, empty or non-empty, given fuel `≥ childrenSize cs`. -/
theorem parseChildrenW_roundtrip (cs : List WChild) (rest : PState) (hwf : WfChildren cs) (fuel : Nat)
    (hfuel : childrenSize cs ≤ fuel) :
    parseChildrenW fuel ((encodeChildrenW cs).toList ++ rest) = some (cs, rest) :=
  (forestGoal_all fuel).2.1 cs rest hwf hfuel

/-! ### NON-VACUITY witnesses for the action-tree decoder (the recursion + every node field are real). -/

/-- A well-formedness proof for the §W5-eval `demoTree` (the 2-level tree with a credential + caveat on
each node): every digest `< 2^256`, every tier `≤ 3`, every action `simple`. -/
private theorem demoTree_wf : WfForest demoTree :=
  -- the nested `And` of `WfForest`/`WfChildren`/`WfCaveats` (anonymous-ctor notation whnf-reduces each
  -- mutual def against the expected type); the two `2^256` digest bounds are `signature 7`/`token 3`,
  -- the one caveat tier is `0 ≤ 3` (each leaf `show`n in its unfolded `WfAuth`/`WfCaveat` form).
  ⟨show (7:Nat) < 2^256 by norm_num, ⟨show (0:Nat) ≤ 3 by decide, trivial⟩, trivial,
    ⟨show (3:Nat) < 2^256 by norm_num, trivial, trivial,
      ⟨⟨trivial, trivial, trivial, trivial⟩, trivial⟩⟩, trivial⟩

-- The whole `demoTree` round-trips through the wire (the recursion is real — the root's child + grandchild
-- each call back into the forest parser; fuel `forestSize demoTree` is adequate):
example : parseForestW (forestSize demoTree) ((encodeForestW demoTree).toList ++ ['x'])
            = some (demoTree, ['x']) :=
  parseForestW_roundtrip demoTree ['x'] demoTree_wf (forestSize demoTree) (le_refl _)
/-! Each charge in `authSize`/`authListSize` is paid by ≥1 encoded byte. Mutual: the `oneOf` body's `+1`
by the `{"oneof":[` prefix, each candidate by its own encoding (recursively), each tail comma by `,`. -/
mutual
private theorem authSize_le_encode (a : AuthW) : authSize a ≤ (encodeAuthW a).toList.length := by
  -- every arm's encoding opens with `'{'` (length ≥ 1); `ht` specializes per case below.
  obtain ⟨t, ht⟩ := encodeAuthW_head a
  cases a with
  | oneOf cands i =>
      -- `authSize (.oneOf …) = 1 + authListSize cands`; the encoding holds the candidate list verbatim,
      -- prefixed by `{"oneof":[` (length 9) — slack covers the `+1`.
      have hl := authListSize_le_encode cands
      show 1 + authListSize cands ≤ (encodeAuthW (.oneOf cands i)).toList.length
      -- `encodeAuthW` is mutual ⇒ doesn't reduce by `rfl`; unfold its oneOf equation via `simp only`.
      simp only [encodeAuthW, String.toList_append, List.length_append,
        show ("{\"oneof\":[":String).toList.length = 10 from by decide]
      omega
  | _ =>
      -- every other arm has `authSize = 1`; its encoding (now `'{' :: t` via `ht`) has length ≥ 1.
      rw [ht]; simp only [authSize, List.length_cons]; omega
private theorem authListSize_le_encode (as : List AuthW) : authListSize as ≤ (encodeAuthListW as).toList.length := by
  cases as with
  | nil => simp [authListSize]
  | cons a as' =>
      -- `[` + first auth + tail + `]`; the first via `authSize_le_encode`, the tail via the tail bound.
      have ha := authSize_le_encode a
      have ht := authTailSize_le_encode as'
      have hshape := encAuthListW_cons_shape a as' []
      simp only [List.append_nil] at hshape
      show 1 + authSize a + authListSize as' ≤ (encodeAuthListW (a :: as')).toList.length
      rw [hshape]
      simp only [List.length_cons, List.length_append]
      omega
private theorem authTailSize_le_encode (as : List AuthW) : authListSize as ≤ (encodeAuthTailW as).toList.length := by
  cases as with
  | nil => simp [authListSize, encodeAuthTailW]
  | cons a as' =>
      -- `,` + auth + tail; the auth via `authSize_le_encode`, the tail by self-recursion.
      have ha := authSize_le_encode a
      have ht := authTailSize_le_encode as'
      have hshape := encAuthTailW_cons_shape a as' []
      simp only [List.append_nil] at hshape
      show 1 + authSize a + authListSize as' ≤ (encodeAuthTailW (a :: as')).toList.length
      rw [hshape]
      simp only [List.length_cons, List.length_append]
      omega
end

/-! Each charge in `forestSize`/`childrenSize` is paid by ≥1 encoded byte. Mutual: the node's `+1` by the
`{"auth":` prefix, the credential by `authSize_le_encode`, each edge's `+2` by its `{"holder":`-led body and
the `sub` recursion. The fuel-adequacy fact the envelope parser relies on. -/
mutual
private theorem forestSize_le_encode (f : WForest) : forestSize f ≤ (encodeForestW f).toList.length := by
  obtain ⟨na, cavs, a, kids⟩ := f
  have hna := authSize_le_encode na
  have hkids := childrenSize_le_encode kids
  -- the node opens with `{"auth":` (length 8) then the credential, …, then the children array.
  have hshape := encForestW_node_shape na cavs a kids []
  simp only [List.append_nil] at hshape
  show 1 + authSize na + childrenSize kids ≤ (encodeForestW ⟨na, cavs, a, kids⟩).toList.length
  rw [hshape]
  simp only [List.length_cons, List.length_append,
    show ("{\"auth\":":String).toList.length = 8 from by decide]
  omega
private theorem childrenSize_le_encode (cs : List WChild) : childrenSize cs ≤ (encodeChildrenW cs).toList.length := by
  cases cs with
  | nil => simp [childrenSize, encodeChildrenW]
  | cons c cs' =>
      obtain ⟨h, k, pc, sub⟩ := c
      have hsub := forestSize_le_encode sub
      have htail := childrenTailSize_le_encode cs'
      -- `[` + first edge + tail + `]`; the edge `+2` charge is covered by its `{"holder":` body (length 10),
      -- the sub-tree by `forestSize_le_encode`, the tail by the tail bound.
      have hshape := encodeChildrenW_cons_shape ⟨h, k, pc, sub⟩ cs' []
      simp only [List.append_nil] at hshape
      have hedge := encChildW_edge_shape h k pc sub []
      simp only [List.append_nil] at hedge
      show 2 + forestSize sub + childrenSize cs' ≤ (encodeChildrenW (⟨h, k, pc, sub⟩ :: cs')).toList.length
      rw [hshape, hedge]
      simp only [List.length_cons, List.length_append,
        show ("{\"holder\":":String).toList.length = 10 from by decide]
      omega
private theorem childrenTailSize_le_encode (cs : List WChild) : childrenSize cs ≤ (encodeChildrenTailW cs).toList.length := by
  cases cs with
  | nil => simp [childrenSize, encodeChildrenTailW]
  | cons c cs' =>
      obtain ⟨h, k, pc, sub⟩ := c
      have hsub := forestSize_le_encode sub
      have htail := childrenTailSize_le_encode cs'
      -- `,` + edge + tail; the edge `{"holder":` body (length 10) covers the `+2`, the sub via the forest bound.
      have hshape := encChildrenTailW_cons_shape ⟨h, k, pc, sub⟩ cs' []
      simp only [List.append_nil] at hshape
      have hedge := encChildW_edge_shape h k pc sub []
      simp only [List.append_nil] at hedge
      show 2 + forestSize sub + childrenSize cs' ≤ (encodeChildrenTailW (⟨h, k, pc, sub⟩ :: cs')).toList.length
      rw [hshape, hedge]
      simp only [List.length_cons, List.length_append,
        show ("{\"holder\":":String).toList.length = 10 from by decide]
      omega
end

end Dregg2.Exec.CodecRoundtrip
