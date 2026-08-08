/-
# POAG1 JSON primitives, and the declaration every hidden-instance game carries

⚑ Why this module exists.  These five definitions lived as `private` defs inside
`Emit.lean`.  A second descriptor renderer cannot reach them, and the two honest
ways out of that are (a) copy them, which is two shapes that agree today and
disagree later, or (b) give them one home.  This is (b).

`Emit.lean` is owned by another lane this cycle, so it still carries its own
copies at the time of writing.  The convergence is a three-line splice — import
this module, `open` it, delete the private block — and it is named in the
descent lane's handover rather than performed behind that lane's back.

Nothing here decides anything about a game.  `instanceDeclarationJson` is the
one substantive definition: it states WHERE an instance comes from and what a
client must verify before a run is scored, and it states no value from which one
can be computed.  It is a constant, so it is the same bytes for every game — the
point being that the descriptor a player downloads distinguishes no two runs.
-/
import Lean.Data.Json
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.EmitJson

open Lean

/-! ## Canonical JSON helpers -/

def jsonString (s : String) : String :=
  String.quote s

def jsonArray (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

def jsonPrettyArray (xs : List String) : String :=
  match xs with
  | [] => "[]"
  | _ => "[\n" ++ String.intercalate ",\n" xs ++ "\n  ]"

def jsonBool (value : Bool) : String :=
  if value then "true" else "false"

/-- How a game turns the drawn SEED into its instance.

⚠ This is a SEPARATE declaration from `sponge`, and the separation is the point.
`sponge` says how the seed is produced and `commitment` says nobody chose it; neither
says anything about the LAST HOP, and that hop is where a bias lived undetected —
`SignalTriangulation` folded three seed bytes with `% 6` while every surrounding
declaration described a careful uniform construction.  A gate reading this artifact had
to ASSUME the last hop, and `scripts/poa-design-gate.py` assumed `% alphabet`; that is
why its `seed-modulo-bias` finding could not be cleared by repairing the code, and why
the hop is now DECLARED and MEASURED rather than assumed.

`method` is what the gate measures the fibres of:

* `"rejection"` — `SeedDraw.drawBelow?`: byte values at or above `256 - 256 % bound`
  are discarded rather than folded, so every symbol has exactly `256 / bound`
  preimages for ANY bound, and the draw may refuse when the stream runs out.
* `"modulo"` — a bare `byte % bound`, total and never refusing.  Exact only when
  `bound` divides 256; the gate computes the fibres and reports the spread when it
  does not.

`bounds` lists the successive draws in order, so a game drawing 5/4/3/2 states four
bounds and the gate measures the whole instance space rather than one symbol. -/
def symbolDrawJson (method : String) (bounds : List Nat) : String :=
  let rejection := method == "rejection"
  let ceiling := fun (b : Nat) => if rejection then 256 - 256 % b else 256
  -- A rejection draw can only run out of bytes if some bound leaves a high block.
  let refuses := rejection && bounds.any (fun b => 256 % b != 0)
  "{\"method\":" ++ jsonString method ++
  (if rejection then
      ",\"module\":\"Dregg2.Games.PathOfAngels.SeedDraw\",\"function\":\"drawBelow?\""
    else ",\"module\":null,\"function\":null") ++
  ",\"bounds\":[" ++ String.intercalate "," (bounds.map toString) ++ "]" ++
  ",\"byte_ceilings\":[" ++
    String.intercalate "," ((bounds.map ceiling).map toString) ++ "]" ++
  ",\"consumes_rejected_bytes\":" ++ jsonBool rejection ++
  ",\"on_exhausted\":" ++ jsonString (if refuses then "refuse" else "unreachable") ++
  ",\"refuses\":" ++ jsonBool refuses ++ "}"

/-- The declaration every hidden-instance descriptor carries in place of its
instance.  It states WHERE the instance comes from and what a client must verify
before a run is scored; it states no value from which one can be computed.

The per-slot commitment itself is NOT in this artifact and cannot be: the bundle
is signed once per content epoch and slots open afterwards.  It is published per
slot in the run opening, whose shape `Emit.schemaJson` pins, and a client refuses
a run whose opening does not carry a curator-signed commitment for the slot it
claims. -/
def instanceDeclarationJson (disclosure : String) (symbolDraw : String) : String :=
  "{\"kind\":\"per-run-hidden-draw\"" ++
  ",\"derivation_module\":\"Dregg2.Games.PathOfAngels.HiddenInstance\"" ++
  ",\"disclosure\":" ++ jsonString disclosure ++
  ",\"symbol_draw\":" ++ symbolDraw ++
  ",\"commitment\":{\"published_in\":\"slot-opening\",\"domain\":\"POAC\"," ++
    "\"preimage\":[\"domain\",\"slot\",\"slot_secret\"]," ++
    "\"binding_bits\":124,\"opened_after\":\"slot-close\"}" ++
  ",\"draw\":{\"domain\":\"POAD\"," ++
    "\"preimage\":[\"domain\",\"purpose\",\"slot\",\"mission_id\",\"epoch\"," ++
      "\"slot_secret\",\"federation_id\",\"content_session\",\"player_key\"]," ++
    "\"purposes\":{\"judged\":1,\"practice\":2}}" ++
  ",\"sponge\":{\"permutation\":\"poseidon2-babybear-w16\",\"width\":16,\"rate\":8," ++
    "\"capacity\":8,\"lane_bytes\":1,\"lane_reject_at_or_above\":2013265920," ++
    "\"squeeze_blocks\":6}" ++
  ",\"practice\":{\"seed\":\"client-chosen\",\"scored\":false," ++
    "\"purpose_tag\":2,\"transcript_field\":\"mode\"}" ++
  ",\"operator_knows_instance\":true}"

/-! ## The shared validators

A descriptor is checked by parsing the bytes back and pinning the key set
EXACTLY.  An extra key is a refusal, not a shrug: the pre-split bundle differed
from the current one by extra keys that named the instance, and a decoder that
ignores unknown fields would have loaded it happily. -/

def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  let present := object.toArray.map Prod.fst
  for key in present do
    if !allowed.contains key then
      throw s!"POAG1 unexpected key {key}"
  for key in allowed do
    if !present.contains key then
      throw s!"POAG1 missing key {key}"

/-- The instance block, key by key.  ⚠ `selected` and `seed_byte` are refused by
construction: they are not in the allowed set, so a descriptor that still names a
drawn board fails to load rather than being reinterpreted. -/
def validateInstanceDeclaration (block : Json) (disclosure : String) :
    Except String Unit := do
  exactKeys block ["kind", "derivation_module", "disclosure", "symbol_draw",
    "commitment", "draw", "sponge", "practice", "operator_knows_instance"]
  exactKeys (← block.getObjVal? "symbol_draw")
    ["method", "module", "function", "bounds", "byte_ceilings",
     "consumes_rejected_bytes", "on_exhausted", "refuses"]
  if (← block.getObjValAs? String "kind") != "per-run-hidden-draw" then
    throw "POAG1 instance declaration is not a per-run hidden draw"
  if (← block.getObjValAs? String "disclosure") != disclosure then
    throw s!"POAG1 instance disclosure is not {disclosure}"
  exactKeys (← block.getObjVal? "commitment")
    ["published_in", "domain", "preimage", "binding_bits", "opened_after"]
  exactKeys (← block.getObjVal? "draw") ["domain", "preimage", "purposes"]
  exactKeys (← block.getObjVal? "sponge")
    ["permutation", "width", "rate", "capacity", "lane_bytes",
     "lane_reject_at_or_above", "squeeze_blocks"]
  exactKeys (← block.getObjVal? "practice")
    ["seed", "scored", "purpose_tag", "transcript_field"]

def validateHiddenSecurity (j : Json) (visibility : String) :
    Except String Unit := do
  let security ← j.getObjVal? "security"
  exactKeys security ["classification", "instance_visibility", "competitive_rewards",
    "economic_rewards"]
  if (← security.getObjValAs? String "instance_visibility") != visibility then
    throw s!"POAG1 descriptor does not declare instance_visibility {visibility}"

/- ⚠ There is deliberately no theorem here.  "This block names no run" is a fact
about the TYPE — `instanceDeclarationJson : String → String` takes a disclosure
and nothing else — and a Lean theorem restating it would be `congrArg` wearing a
name.  The property that could go wrong is that some later edit threads a seed
or a player key through this signature, and the thing that catches THAT is the
signature, not a `rfl`.  This module therefore carries no pins; every claim about
the emitted bytes is pinned where the bytes are assembled. -/

end Dregg2.Games.PathOfAngels.EmitJson
