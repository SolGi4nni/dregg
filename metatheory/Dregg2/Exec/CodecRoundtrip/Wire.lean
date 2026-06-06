import Dregg2.Exec.CodecRoundtrip.Leaves
import Dregg2.Exec.CodecRoundtrip.SideTables
import Dregg2.Exec.CodecRoundtrip.Forest

/-!
Submodule of `Dregg2.Exec.CodecRoundtrip` — split for parallel compilation.
-/

namespace Dregg2.Exec.CodecRoundtrip

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide
open Dregg2.Exec.TurnExecutorFull (QueueTxOpA)

/-! ## §14 — the WIDE STATE record (`parseWState`) roundtrip — THE STATE DECODER (the differential's
core). The 9-field `do`-block assembling every side-table proved above: cells (§12), caps (§13),
bal (§10), escrows (§11), nullifiers/commitments/revoked (§9), queues (§11b), swiss (§11c). Strict on
field ORDER + the closing `}`. Carries one `Wf` hypothesis (`WfCells w.cells`, the §1 value boundary on
the cell payloads); every other field is a total-codec side-table. Fuel-adequate whenever the outer fuel
exceeds the encoded width (the `parseWWire` caller passes the whole-input length). -/

set_option maxHeartbeats 2000000 in
/-- **FILL J production (the STATE DECODER): the WIDE STATE record roundtrip**
(`parseWState ∘ encodeWState = id`) — the post-state object the differential re-decodes. Composes the
nine side-table roundtrips through the `do`-block: each `lit ",\"field\":"` is a clean literal consume;
each field arm is its proved leaf; the cells loop's outer fuel is met by the width hypothesis. This
removes the STATE codec — the heart of the wholesale-swap differential — from the Lean-side TCB. -/
theorem parseWState_encode (w : WState) (rest : PState) (hwf : WfCells w.cells) (fuel : Nat)
    (hf : ((encodeWState w).toList ++ rest).length ≤ fuel) :
    parseWState fuel ((encodeWState w).toList ++ rest) = some (w, rest) := by
  obtain ⟨cells, caps, bal, escrows, nullifiers, commitments, queues, swiss, revoked⟩ := w
  unfold parseWState
  -- unfold `encodeWState` in BOTH `hf` and the goal (so the width hypothesis expands to the SAME
  -- field-length sum the per-field fuel obligations reference; `unfold` alone misses `hf`).
  simp only [encodeWState, String.toList_append, List.append_assoc] at hf ⊢
  -- open `{"cells":`, then the cells store (outer fuel ≥ width)
  rw [lit_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseCellsW_encode cells _ hwf fuel (by
    simp only [List.length_append] at hf ⊢; omega)]
  simp only [Option.bind_eq_bind, Option.bind]
  -- the remaining 8 fields: each a clean `lit ",\"field\":"` then its proved leaf
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseCapsEntries_encode caps _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseBal_encode bal _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseEscrows_encode escrows _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNats_encode nullifiers _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNats_encode commitments _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseQueues_encode queues _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseSwissTable_encode swiss _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNats_encode revoked _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]

/-! ## §16 — the complete-turn ENVELOPE (`parseWTurn`/`parseWWire`) roundtrip — the OUTER WIRE
(the last FILL-J leaf). The Turn envelope `{"agent":N,"nonce":N,"fee":Z,"valid_until":N,"prev":"H64",
"root":NODE}` carries the dregg1 outer fields (`parseNat`/`parseInt`/`parseHex32` leaves, §0) wrapping the
recursive action-tree root (§15 `parseForestW_roundtrip`); the wire `{"state":STATEW,"turn":TURNW}` then
composes the §14 wide-state decoder with this envelope, requiring the WHOLE input consumed (`lit "}"` must
yield `some []` — fail-closed on trailing bytes). This removes the OUTERMOST codec layer — the envelope the
wholesale swap actually hands the C entry point — from the Lean-side TCB.

### §16a — the structural-fuel ADEQUACY bridge: `forestSize f ≤ (encodeForestW f).length`. The envelope
parser funds the tree recursion with `cs.length + 1` (the whole-input length); since the encoded tree is a
SUBSTRING of the input, this bound dominates `forestSize`. The bound itself: every `+1`/`+2` charge in the
size measure is paid by ≥1 literal byte the encoder emits (the credential by its `{…}` body, each edge by
its `{"holder":…}` body). Mutual over auth / auth-list / auth-tail / forest / children. -/
/-! ### §16b — the Turn ENVELOPE roundtrip (a fixed-field `do`-block; the tree via §15). -/

/-- Well-formed Turn: the `prev` digest fits the `[u8;32]` width (`< 2^256`, else `parseHex32` wraps) and
the root tree is well-formed (§15a). The `agent`/`nonce`/`valid_until` are `Nat`, `fee` an `Int` — total. -/
def WfTurn (t : WTurn) : Prop := t.prevHash < 2 ^ 256 ∧ WfForest t.root

set_option maxHeartbeats 1000000 in
/-- **FILL J production (the ENVELOPE): the Turn-envelope roundtrip** (`parseWTurn ∘ encodeWTurn = id`).
The dregg1 outer fields (`agent`/`nonce`/`fee`/`valid_until`/`prev`) walk their `parseNat`/`parseInt`/
`parseHex32` leaves (§0), the `prev` digest losslessly under the `< 2^256` boundary, then the action-tree
root via §15's `parseForestW_roundtrip` (fuel `≥ forestSize root`). Strict on field ORDER + the closing
`}`. The wire-envelope decoder the wholesale swap hands the C entry point — out of the Lean TCB. -/
theorem parseWTurn_encode (t : WTurn) (rest : PState) (hwf : WfTurn t) (fuel : Nat)
    (hfuel : forestSize t.root ≤ fuel) (hblock : t.blockHeight = 0) :
    parseWTurn fuel ((encodeWTurn t).toList ++ rest) = some (t, rest) := by
  obtain ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩ := t
  have hblock' : blockHeight = 0 := hblock
  obtain ⟨hprev, hroot⟩ : prevHash < 2 ^ 256 ∧ WfForest root := hwf
  unfold parseWTurn
  -- rebracket the `++` chain into the right-associated field sequence the parser steps consume.
  rw [show (encodeWTurn ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩).toList ++ rest
        = ("{\"agent\":":String).toList ++ ((toString agent).toList
            ++ ((",\"nonce\":":String).toList ++ ((toString nonce).toList
            ++ ((",\"fee\":":String).toList ++ ((toString fee).toList
            ++ ((",\"valid_until\":":String).toList ++ ((toString validUntil).toList
            ++ ((",\"prev\":\"":String).toList ++ ((toHex32 prevHash).toList
            ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList
            ++ ('}' :: rest)))))))))))) from by
        show (encodeWTurn ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩).toList ++ rest = _
        unfold encodeWTurn encodeBlockHeightW
        simp only [hblock', if_false (by decide : 0 > 0 = false), String.append_nil, String.toList_append,
          show ("}":String).toList = ['}'] from by decide,
          show ("\",\"root\":":String).toList = ("\"":String).toList ++ (",\"root\":":String).toList from by decide,
          List.append_assoc, List.cons_append, List.nil_append]]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString agent _ (Or.inr ⟨',', _, by
        rw [show (",\"nonce\":":String).toList = ',' :: ("\"nonce\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString nonce _ (Or.inr ⟨',', _, by
        rw [show (",\"fee\":":String).toList = ',' :: ("\"fee\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseInt_toString fee _ (Or.inr ⟨',', _, by
        rw [show (",\"valid_until\":":String).toList = ',' :: ("\"valid_until\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString validUntil _ (Or.inr ⟨',', _, by
        rw [show (",\"prev\":\"":String).toList = ',' :: ("\"prev\":\"":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show parseBlockHeightW ((",\"prev\":\"":String).toList ++ ((toHex32 prevHash).toList
            ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList
            ++ ('}' :: rest))))) = some (0, (",\"prev\":\"":String).toList ++ ((toHex32 prevHash).toList
            ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList
            ++ ('}' :: rest))))) from by
        rw [show (",\"prev\":\"":String).toList = ',' :: ("\"prev\":\"":String).toList from by decide]
        simp [parseBlockHeightW, lit]]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseHex32_toHex32 prevHash _, Nat.mod_eq_of_lt hprev]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseForestW_roundtrip root _ hroot fuel hfuel]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show lit "}" ('}' :: rest) = some rest from by
        rw [show ('}' :: rest) = ("}":String).toList ++ rest from rfl, lit_append]]
  simp only [hblock']

/-! ### §16c — the complete-turn WIRE roundtrip (state §14 ∘ envelope §16b; the WHOLE input consumed). -/

/-- The complete-turn wire ENCODER (the inline `{"state":STATEW,"turn":TURNW}` the C entry point reads —
matching `wideDemoInput`/`execFullTurnWide`'s input shape). -/
def encodeWWire (w : WWire) : String :=
  "{\"state\":" ++ encodeWState w.state ++ ",\"turn\":" ++ encodeWTurn w.turn ++ "}"

set_option maxHeartbeats 1000000 in
/-- **FILL J production (the OUTERMOST WIRE): the complete-turn wire roundtrip**
(`parseWWire ∘ encodeWWire = id`). Composes the §14 wide-state decoder with the §16b envelope, then
requires the WHOLE input consumed (`lit "}"` yields `some []` — trailing bytes fail-closed). The fuel
(`input.length + 1`) dominates both the state width and `forestSize root` (each `≤` the encoded length, the
encoded objects being substrings of the input, §16a). This removes the OUTERMOST codec — the envelope the
wholesale swap hands `execFullTurnWide` — from the Lean-side TCB; with §14/§15 the wire codec is FULLY out. -/
theorem parseWWire_encode (w : WWire) (hcells : WfCells w.state.cells) (hturn : WfTurn w.turn)
    (hblock : w.turn.blockHeight = 0) :
    parseWWire (encodeWWire w) = some w := by
  obtain ⟨state, turn⟩ := w
  have hwire : (encodeWWire ⟨state, turn⟩).toList
      = ("{\"state\":":String).toList ++ ((encodeWState state).toList
          ++ ((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList))) := by
    show (encodeWWire ⟨state, turn⟩).toList = _
    unfold encodeWWire
    simp only [String.toList_append, List.append_assoc]
  unfold parseWWire
  simp only []
  set fuel := (encodeWWire ⟨state, turn⟩).toList.length + 1 with hfueldef
  rw [hwire]
  rw [show lit "{\"state\":" (("{\"state\":":String).toList ++ ((encodeWState state).toList
          ++ ((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList))))
        = some ((encodeWState state).toList ++ ((",\"turn\":":String).toList
            ++ ((encodeWTurn turn).toList ++ "}".toList))) from
        lit_append "{\"state\":" _]
  simp only []
  rw [parseWState_encode state (((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList)))
        hcells fuel (by
        rw [hfueldef, hwire]
        simp only [List.length_append]
        omega)]
  dsimp only
  rw [show lit ",\"turn\":" ((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList))
        = some ((encodeWTurn turn).toList ++ "}".toList) from lit_append ",\"turn\":" _]
  simp only []
  rw [parseWTurn_encode turn "}".toList hturn fuel (by
        have hbridge := forestSize_le_encode turn.root
        rw [hfueldef, hwire]
        have hsub : (encodeForestW turn.root).toList.length ≤ (encodeWTurn turn).toList.length := by
          obtain ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩ := turn
          show (encodeForestW root).toList.length ≤ (encodeWTurn ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩).toList.length
          rw [show (encodeWTurn ⟨agent, nonce, fee, validUntil, blockHeight, prevHash, root⟩)
                = "{\"agent\":" ++ toString agent ++ ",\"nonce\":" ++ toString nonce ++ ",\"fee\":" ++ toString fee
                    ++ ",\"valid_until\":" ++ toString validUntil ++ encodeBlockHeightW blockHeight
                    ++ ",\"prev\":\"" ++ toHex32 prevHash ++ "\""
                    ++ ",\"root\":" ++ encodeForestW root ++ "}" from rfl]
          simp only [String.toList_append, List.length_append]
          omega
        simp only [List.length_append]
        omega) hblock]
  dsimp only
  rw [show lit "}" "}".toList = some [] from by
        rw [show ("}":String).toList = ("}":String).toList ++ ([] : PState) from by simp, lit_append]]

/-! ### §16d — NON-VACUITY: a complete wire WITH a delegation edge round-trips (the recursion + the
envelope + every state field are real). -/

/-- A real multi-node turn: the root credential bears a delegation EDGE (`keep`/`cap`/`sub`), so the wire
exercises the §15 children recursion, not just a leaf root; wrapped in a populated wide state. -/
private def wireWitness : WWire :=
  { state := { cells := [(0, .record [("balance", .int 100)])], caps := [(9, [.node 0])], bal := [(0, 0, 100)],
               escrows := [], nullifiers := [], commitments := [], queues := [], swiss := [] }
    turn  := { agent := 0, nonce := 1, fee := 2, validUntil := 9, prevHash := 7
               root := ⟨ .signature 3 3, [{ tier := 0, cell := 0, asset := 0, min := 1 }],
                         .balanceA { actor := 0, src := 0, dst := 1, amt := 10 } 0,
                         [⟨1, [.read], .node 0, ⟨.unchecked, [], .revoke 0 0, []⟩⟩] ⟩ } }

/-- The witness state's cells are well-formed (the one digest-free `int` balance). -/
private theorem wireWitness_cells_wf : WfCells wireWitness.state.cells := by
  show WfCells [(0, .record [("balance", .int 100)])]
  exact ⟨⟨by decide, trivial, trivial⟩, trivial⟩

/-- The witness turn is well-formed: `prev = 7 < 2^256`, root credential `signature 3 < 2^256`, the one
caveat tier `0 ≤ 3`, every action `simple`/total, and the one delegation edge's sub-tree well-formed. -/
private theorem wireWitness_turn_wf : WfTurn wireWitness.turn := by
  refine ⟨by decide, ?_⟩
  show WfForest ⟨ .signature 3 3, [{ tier := 0, cell := 0, asset := 0, min := 1 }],
                  .balanceA { actor := 0, src := 0, dst := 1, amt := 10 } 0,
                  [⟨1, [.read], .node 0, ⟨.unchecked, [], .revoke 0 0, []⟩⟩] ⟩
  -- the sub-tree's credential is `.unchecked` (`WfAuth = True`), its caveats/action/children all trivial.
  exact ⟨show (3:Nat) < 2^256 by norm_num, ⟨by unfold WfCaveat; decide, trivial⟩, trivial,
    ⟨⟨trivial, trivial, trivial, trivial⟩, trivial⟩⟩

-- The WHOLE wire — populated state + a delegation-bearing tree — round-trips through `parseWWire`:
example : parseWWire (encodeWWire wireWitness) = some wireWitness :=
  parseWWire_encode wireWitness wireWitness_cells_wf wireWitness_turn_wf rfl

end Dregg2.Exec.CodecRoundtrip
