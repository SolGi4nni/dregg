/-
# EmitLayoutManifest — the EffectVM rotated LAYOUT, exported from Lean as Rust source.

Lean is the source of truth for the rotated column geometry: it defines the limb layout and it emits
the constraint descriptors that READ those columns. But the Rust side ALSO needs the layout — the
producer (`turn::rotation_witness`) WRITES witness values into those columns, and the audit gates
check them. Historically Rust re-declared the whole geometry by hand (~89 `pub const`s mirroring
these defs), and the two drifted:

* the REVOKED-ROOT flag day inserted `revoked_root` at base limb 37 and shifted every limb ≥ 37 by
  +1. The producer moved (`write_lanes([33, 38..=44])`); the Lean perms/VK completion welds did NOT
  (they still read limb 37 — which IS `revoked_root` lane-0). Every honest setPermissions /
  setVerificationKey turn was UNSAT in-circuit until that was found;
* `B_SPAN` grew 227 → 239 and a hand-pinned Rust audit column rotted 439 → 451 silently;
* the `vaultSat` satisfaction span grew 64 columns and its hand-pinned width rotted too.

Every one of those is a producer/constraint (or gate/artifact) disagreement about a number that has
exactly ONE true value. So this emitter prints the layout AS RUST, the emit pipeline installs it as
`circuit/src/effect_vm/layout_generated.rs`, and both sides read the same constants. A disagreement
becomes a compile-time impossibility rather than a soundness bug that proves fine on the members you
happened to test.

What stays hand-written: the SEMANTIC teeth (does a forged witness refuse, does the weld bite). Those
must remain independent — they test properties, not coordinates.

SCRATCH executable: `lake env lean --run EmitLayoutManifest.lean`
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.RotatedLayout
import Dregg2.Circuit.Emit.RotWideCompactS2

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmit (EFFECT_VM_WIDTH)
open Dregg2.Circuit.Emit

namespace EmitLayoutManifest

/-- One exported constant: Rust name, value, and the doc line that travels with it. -/
structure Item where
  name : String
  value : Nat
  doc : String

/-! ### The chain-carrier base, READ OFF THE EMITTED SITE LIST (never a second literal)

`rotV3SitesAt` IS the object the descriptors are built from: its first site's `digestCol` is the
column the head absorption writes, i.e. the base of the chain-carrier band. Taking the value from
there — rather than restating `B_STATE_COMMIT + 1` — makes the exported constant a projection of
the emitted geometry, so a site-list change moves it instead of silently disagreeing with it.

This exists because the Rust side carried `pub const B_CHAIN_BASE: usize = 180;` by hand across the
178 → 184 flag day. The producer then wrote its chain digests OVER pre-limbs 180..183 and over the
iroot/state-commit carriers, and the descriptor audit read the carriers six columns below where the
committed descriptors put them. Every rotated member was UNSAT and the registry looked wrong. -/
def bChainBase : Nat := ((rotV3SitesAt 0).head?.map (·.digestCol)).getD 0

/-- The chain-carrier count is what is left of a block once the limbs, the iroot and the
state-commit carrier are accounted for. -/
def bNumChain : Nat := B_SPAN - bChainBase

-- REALITY GATES: the carrier band starts immediately past `state_commit`, every emitted site's
-- digest lands inside `[bChainBase, B_SPAN)` except the final one (which IS `B_STATE_COMMIT`), and
-- the band exactly fills the block's tail.
#guard bChainBase == B_STATE_COMMIT + 1
#guard bChainBase + bNumChain == B_SPAN
#guard ((rotV3SitesAt 0).dropLast.all (fun s => bChainBase ≤ s.digestCol && s.digestCol < B_SPAN))
#guard ((rotV3SitesAt 0).getLast?.map (·.digestCol)).getD 0 == B_STATE_COMMIT
#guard (rotV3SitesAt 0).length == bNumChain + 1

/-! ### The S2 deletion geometry, read off `RotWideCompactS2`'s own spec objects.

`s2_compact_generated.rs` advertises itself as `@generated`, but three of its constants were
string literals inside `scripts/emit_descriptors.py` (`179` / `60` / `840`) while the per-member
table came from Lean. They did not move with the flag day. Derived here from the SPEC LISTS so
there is no second place to re-type them. -/
def s2CarrierOff : Nat := ((Dregg2.Circuit.Emit.RotWideCompactS2.s2CarrierCols 0).head?).getD 0
def s2CarrierSpan : Nat := (Dregg2.Circuit.Emit.RotWideCompactS2.s2CarrierCols 0).length
def s2LaneSpan : Nat :=
  (Dregg2.Circuit.Emit.RotWideCompactS2.s2DeadCols 0 0).length - 2 * s2CarrierSpan

-- REALITY GATES: the deleted carrier band IS the state-commit carrier plus the whole chain band,
-- and `isDeadCol` (the computable form the emit gates ran on) agrees at both lane-band edges.
#guard s2CarrierOff == B_STATE_COMMIT
#guard s2CarrierSpan == bNumChain + 1
#guard Dregg2.Circuit.Emit.RotWideCompactS2.isDeadCol 0 100000 (100000 + s2LaneSpan - 1) == true
#guard Dregg2.Circuit.Emit.RotWideCompactS2.isDeadCol 0 100000 (100000 + s2LaneSpan) == false

/-- The rotated-layout spine. Each entry is a number the Rust side previously re-declared by hand. -/
def items : List Item :=
  [ { name := "EFFECT_VM_WIDTH", value := EFFECT_VM_WIDTH,
      doc := "the v1 EffectVM face width — the base every rotated member graduates from" }
  , { name := "NUM_PRE_LIMBS", value := rotated184.numPreLimbs,
      doc := "pre-iroot limbs in one rotated block — projected from the verified RotatedLayout" }
  , { name := "B_SPAN", value := B_SPAN,
      doc := "one rotated state block's span (BEFORE and AFTER each occupy B_SPAN columns)" }
  , { name := "AFTER_BLOCK_OFF", value := AFTER_BLOCK_OFF,
      doc := "column offset from a member's face to its AFTER block (= B_SPAN)" }
  , { name := "C_SPAN", value := C_SPAN,
      doc := "the caveat region's span" }
  , { name := "C_COMMIT", value := C_COMMIT,
      doc := "the caveat commitment carrier, in-region" }
  , { name := "C_RC_OFF", value := C_RC_OFF,
      doc := "the DFA route-commitment (rc) carrier, in-region" }
  , { name := "APPENDIX_SPAN", value := APPENDIX_SPAN,
      doc := "2*B_SPAN + C_SPAN — the rotated appendix appended to the v1 face" }
    -- the committed base limbs (pre-iroot)
  , { name := "B_RECORD_DIGEST", value := B_RECORD_DIGEST,
      doc := "committed record/authority digest limb" }
  , { name := "B_CAP_ROOT", value := B_CAP_ROOT, doc := "committed capability-root limb" }
  , { name := "B_NULLIFIER_ROOT_OFF", value := B_NULLIFIER_ROOT_OFF,
      doc := "committed nullifier-root limb" }
  , { name := "B_COMMITMENTS_ROOT", value := B_COMMITMENTS_ROOT,
      doc := "committed commitments-root limb" }
  , { name := "B_HEAP_ROOT", value := B_HEAP_ROOT, doc := "committed heap-root limb" }
  , { name := "B_LIFECYCLE", value := B_LIFECYCLE, doc := "committed lifecycle limb" }
  , { name := "B_EPOCH", value := B_EPOCH, doc := "committed epoch limb" }
  , { name := "B_COMMITTED_HEIGHT", value := B_COMMITTED_HEIGHT,
      doc := "last SCALAR pre-iroot limb (disc/perms/vk/mode/fields-root ride past it)" }
  , { name := "B_DISC", value := B_DISC, doc := "WAVE-1 committed discriminant limb" }
  , { name := "B_PERMS", value := B_PERMS,
      doc := "WAVE-2 committed permissions-digest limb (lane 0 of the faithful 8-felt group)" }
  , { name := "B_VK", value := B_VK,
      doc := "WAVE-2 committed verification-key-digest limb (lane 0 of the 8-felt group)" }
  , { name := "B_MODE", value := B_MODE, doc := "WAVE-3 committed mode limb" }
  , { name := "B_FIELDS_ROOT", value := B_FIELDS_ROOT,
      doc := "WAVE-3 committed fields-root digest limb" }
  , { name := "B_REVOKED_ROOT", value := B_REVOKED_ROOT,
      doc := "REVOKED-ROOT flag-day limb — inserted at 37, shifting every limb >= 37 by +1" }
    -- THE WELD OFFSETS. These are the numbers the setPerms/setVK bug lived in.
  , { name := "B_PERMS_COMPLETION", value := B_PERMS_COMPLETION,
      doc := "FIRST perms-digest completion limb; permsHash[1..7] ride B_PERMS_COMPLETION..+6. \
              The producer writes these lanes and the in-circuit weld reads them: ONE source." }
  , { name := "B_VK_COMPLETION", value := B_VK_COMPLETION,
      doc := "FIRST vk-digest completion limb; vkHash[1..7] ride B_VK_COMPLETION..+6" }
  , { name := "B_IROOT", value := B_IROOT, doc := "the iroot limb (pre-iroot limbs end here)" }
  , { name := "B_STATE_COMMIT", value := B_STATE_COMMIT, doc := "the state-commitment limb" }
  , { name := "B_CHAIN_BASE", value := bChainBase,
      doc := "in-block base of the chained-absorption carriers — READ OFF `rotV3SitesAt`'s first \
              emitted site, so the producer writes the columns the descriptors bind. Rust carried \
              this by hand and it rotted across the 178 -> 184 flag day (180 vs 186): the producer \
              overwrote four pre-limbs plus iroot/state_commit and every rotated member was UNSAT." }
  , { name := "B_NUM_CHAIN", value := bNumChain,
      doc := "chain carriers per block: they fill `[B_CHAIN_BASE, B_SPAN)` exactly" }
    -- THE S2 DELETION BANDS (`RotWideCompactS2`) — the Rust trace producer must drop exactly the
    -- columns the Lean emit deleted from the committed wide descriptors.
  , { name := "S2_CARRIER_OFF", value := s2CarrierOff,
      doc := "in-block offset of the first S2-deleted column (the 1-felt state_commit digest)" }
  , { name := "S2_CARRIER_SPAN", value := s2CarrierSpan,
      doc := "one S2-deleted carrier band's width (state_commit digest + B_NUM_CHAIN chain carriers)" }
  , { name := "S2_LANE_SPAN", value := s2LaneSpan,
      doc := "the S2-deleted graduated chip-lane band's width (7 lanes per deleted block site)" }
    -- THE OCTET → REGISTER QUERY + APP-PI LAYOUT (the field_key class — Rust reads, never re-derives).
    -- `FIELD_BASE` is the state register index the AFTER-block field octet's index 0 maps to; a consumer
    -- derives an octet index from a register slot via `octet_index_of_register` (emitted below).
  , { name := "FIELD_BASE", value := Dregg2.Circuit.Emit.EffectVmEmit.state.FIELD_BASE,
      doc := "state register index of the first committed field (fields[0]); the AFTER-block field \
              octet holds register r(FIELD_BASE+i) at octet index i, so octet_index(r) = r - FIELD_BASE" }
  , { name := "CUSTOM_APP_FIELD_ROT_BASE", value := CUSTOM_APP_FIELD_ROT_BASE,
      doc := "in-block column base of the AFTER-block committed fields[0..8] lane-0 octet (the app-root \
              weld octet): weldsAt maps base+CUSTOM_APP_FIELD_ROT_BASE+i ↔ stateBase+FIELD_BASE+i" }
  , { name := "CUSTOM_APP_FIELD_OCTET_LEN", value := CUSTOM_APP_FIELD_OCTET_LEN,
      doc := "width of the app-root field octet (8 field lane-0 limbs)" }
  , { name := "B_CHILD_VK_OCTET", value := B_CHILD_VK_OCTET,
      doc := "in-block base of the child_vk carrier octet (app-PI octet base 0 of [89, 97, 105])" }
  , { name := "B_CONTRACT_HASH_OCTET", value := B_CONTRACT_HASH_OCTET,
      doc := "in-block base of the contract_hash carrier octet (app-PI octet base 1 of [89, 97, 105])" }
  , { name := "B_PUBKEY_OCTET", value := B_PUBKEY_OCTET,
      doc := "in-block base of the public_key carrier octet (app-PI octet base 2 of [89, 97, 105])" }
  ]

/-- Emit one Rust `pub const`. -/
def renderItem (i : Item) : String :=
  s!"/// {i.doc}\npub const {i.name}: usize = {i.value};\n"

/-- Stable Rust API names for the verified layout's named groups. The values are not repeated here:
each Rust constant below indexes the one emitted `ROTATED_GROUP_TABLE`. -/
def groupRustName : GroupName → String
  | .authority   => "AUTHORITY_DIGEST_GROUP"
  | .cap         => "CAP_ROOT_GROUP"
  | .nullifier  => "NULLIFIER_ROOT_GROUP"
  | .commitments => "COMMITMENTS_ROOT_GROUP"
  | .heap        => "HEAP_ROOT_GROUP"
  | .perms       => "PERMS_GROUP"
  | .vk          => "VK_GROUP"
  | .fields      => "FIELDS_ROOT_GROUP"
  | .revoked     => "REVOKED_ROOT_GROUP"
  | .cells       => "CELLS_ROOT_GROUP"

def renderNatArray (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

/-- Emit the verified table as the sole Rust data value, then expose semantic names as const
indices into it. Reordering groups in Lean cannot silently retarget a Rust consumer because the
name→index declarations are generated in the same pass. -/
def renderGroupTable : String :=
  let rows := String.intercalate ",\n" (rotated184.groupTable.map (fun row => "    " ++ renderNatArray row)) ++ ","
  let names := String.intercalate "\n" <| rotated184.groups.zipIdx.map (fun p =>
    s!"pub const {groupRustName p.1.1}: Felt8Group = ROTATED_GROUP_TABLE[{p.2}];")
  s!"/// One faithful-8 group: lane 0 followed by seven completion columns.\n\
pub type Felt8Group = [usize; 8];\n\n\
/// Every named group, emitted verbatim from `rotated184.groupTable`.\n\
pub const ROTATED_GROUP_TABLE: [Felt8Group; {rotated184.groupTable.length}] = [\n{rows}\n];\n\n\
{names}\n\n\
/// Compatibility/readability alias used by the Rust disjointness tooth.\n\
pub const ALL_FELT8_GROUPS: [Felt8Group; {rotated184.groupTable.length}] = ROTATED_GROUP_TABLE;\n"

/-- The NON-GROUP regions of the verified tiling, emitted as data. The Rust disjointness tooth used
to hand-list these beside the generated group table (`[176, 177]` pads, `113..168` field lanes) — so
it re-stated the 178 layout and went red on the flag day for the one region it was NOT reading from
Lean. It now assembles its occupancy from these, which keeps it an artifact-integrity check on the
EMITTED table (a dropped or duplicated region still fails) without carrying a coordinate copy. -/
def renderRegions : String :=
  let singles := renderNatArray rotated184.singles
  let octets := renderNatArray rotated184.octets
  let fields := renderNatArray rotated184.fieldsOctet
  let pads := renderNatArray rotated184.pads
  let cellsC := renderNatArray rotated184.cellsCompletion
  s!"/// The scalar limbs that carry no faithful-8 completion group.\n\
pub const ROTATED_SINGLES: [usize; {rotated184.singles.length}] = {singles};\n\n\
/// The carrier-material octet BASES (each occupies `base .. base + 8`).\n\
pub const ROTATED_OCTET_BASES: [usize; {rotated184.octets.length}] = {octets};\n\n\
/// Every `fields[0..8]` completion lane column, in layout order (lanes 1..8 of each of the 8 \
slots — deliberately NON-CONTIGUOUS: the ninth lane of slot `j` is `176 + j`).\n\
pub const ROTATED_FIELDS_LANE_COLS: [usize; {rotated184.fieldsOctet.length}] = {fields};\n\n\
/// The legacy cells-completion slot (empty since `cells` became a named group).\n\
pub const ROTATED_CELLS_COMPLETION: [usize; {rotated184.cellsCompletion.length}] = {cellsC};\n\n\
/// Unoccupied pad columns. EMPTY at the nine-lane geometry — the two former pads (176, 177) were \
consumed by the fields nonet.\n\
pub const ROTATED_PADS: [usize; {rotated184.pads.length}] = {pads};\n"

/-- **THE NONET PROJECTION, AS DATA.** `RotatedLayout.fieldLaneCol slot lane` for all 8 slots × 9
lanes. Its own docstring says "Consumers must read THIS, never `113 + 8·slot` — the nonet is
deliberately NON-CONTIGUOUS"; the Rust setField VALUE8 producer was computing exactly
`SETFIELD_VALUE8_LANE_BASE + LEN·slot + k`, which is that forbidden formula and which lands on the
neighbouring slot the moment `LEN` becomes 8. Emitting the table removes the formula. -/
def renderFieldLaneTable : String :=
  let rows := String.intercalate ",\n" <|
    (List.range 8).map (fun s =>
      "    " ++ renderNatArray ((List.range 9).map (fun l =>
        fieldLaneCol ⟨s % 8, by omega⟩ ⟨l % 9, by omega⟩)))
  s!"/// `ROTATED_FIELD_LANE_COL[slot][lane]` — the column carrying lane `lane` of `fields[slot]`.\n\
/// Lane 0 is the welded v1-face limb, lanes 1..7 the historical completion window, lane 8 the\n\
/// flag-day ninth lane. NON-CONTIGUOUS BY DESIGN: never reconstruct this with a stride.\n\
pub const ROTATED_FIELD_LANE_COL: [[usize; 9]; 8] = [\n{rows},\n];\n\n\
/// Completion lanes per committed field slot (lanes 1..=8 — the VALUE8/nonet weld width).\n\
pub const ROTATED_FIELD_COMPLETION_LANES: usize = 8;\n"

def header : String :=
  "// @generated by metatheory/EmitLayoutManifest.lean — DO NOT EDIT BY HAND.\n\
   //\n\
   // The rotated EffectVM column layout, exported from the Lean that DEFINES it and that emits the\n\
   // constraint descriptors READING it. The Rust producer (`turn::rotation_witness`) WRITES these\n\
   // same columns, and the audit gates check them — so all three now read one source instead of\n\
   // three hand-maintained mirrors.\n\
   //\n\
   // This module exists because the mirrors drifted, and drift here is not a lint failure — it is a\n\
   // soundness bug. The perms/VK completion weld once read limb 37 (`revoked_root` lane-0) while the\n\
   // producer wrote limb 38, and every honest setPermissions/setVerificationKey turn was UNSAT.\n\
   //\n\
   // Regenerate with the ack-gated emit pipeline (`scripts/emit_descriptors.py`); never hand-edit.\n\n"

/-- The octet→register QUERY, emitted as a `const fn` so the Rust consumer READS the mapping instead
of re-deriving the `- FIELD_BASE` offset by hand (the `field_key` mirror the fold guessed wrong). -/
def footerLines : List String :=
  [ ""
  , "/// Derive the app-root field OCTET INDEX from a state register slot: the AFTER-block"
  , "/// `fields[0..8]` octet holds field register `r(FIELD_BASE + i)` at octet index `i`, so"
  , "/// `octet_index_of_register(r) == r - FIELD_BASE` — the single Lean-authored query the fold's"
  , "/// app-root weld reads (killing the hand `reg(\"winner\") - 3`)."
  , "pub const fn octet_index_of_register(reg: usize) -> usize {"
  , "    reg - FIELD_BASE"
  , "}"
  ]

def footer : String := String.intercalate "\n" footerLines ++ "\n"

def main : IO Unit := do
  IO.print header
  for i in items do
    IO.print (renderItem i)
    IO.print "\n"
  IO.print renderGroupTable
  IO.print "\n"
  IO.print renderRegions
  IO.print "\n"
  IO.print renderFieldLaneTable
  IO.print footer

end EmitLayoutManifest

def main : IO Unit := EmitLayoutManifest.main
