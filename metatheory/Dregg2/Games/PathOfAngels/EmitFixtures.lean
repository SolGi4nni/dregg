/-
# Emit — the artifact-boundary EVALUATION, out of the crypto archive's build

`Emit.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and until
2026-08-08 it ran twenty-seven `native_decide` pins at elaboration: it rendered the whole
POAG1 bundle, parsed it back through its own strict validators, replayed the Black Box
kernel across all 3000 oracle cells and every refusal witness, and drew eight Poseidon2
demonstration seeds for each of six games.  A game-fixture regression was therefore a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured).

The STATEMENTS remain in `Emit.lean` as evaluation-free `check_* : Bool` definitions, and
so do every render function, validator and refinement driver they name — `Emit` still owns
the bytes.  THIS module is where the checks are RUN.  It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking.  A descriptor
    that stops matching its own schema, an oracle cell that stops matching the kernel, a
    schema path list that drifts from `canonicalArtifacts`, all still go red;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ One proof did NOT move.  `signalRulesTable_cells_decode_to_the_kernel_bit` is the PREMISE
of `signalRulesCell_decodes_to_the_kernel_bit` and of the marquee
`signalRulesCell_matches_step`; both are general theorems about the emitter and belong
beside it, so its evaluation stays in `Emit.lean` as the named residue.
-/
import Dregg2.Games.PathOfAngels.Emit

namespace Dregg2.Games.PathOfAngels.Emit

set_option autoImplicit false

/-! ## Wire spellings and the byte pin -/

theorem parseBytes32Hex_test_federation_vector :
    check_parseBytes32Hex_test_federation_vector = true := by native_decide

theorem parseBytes32Hex_refuses_display_label :
    check_parseBytes32Hex_refuses_display_label = true := by native_decide

theorem fnv1a64_empty_vector : check_fnv1a64_empty_vector = true := by native_decide

theorem fnv1a64_a_vector : check_fnv1a64_a_vector = true := by native_decide

theorem artifactRefJson_exact_four_key_vector :
    check_artifactRefJson_exact_four_key_vector = true := by native_decide

theorem artifactRefJson_parses_as_exact_four_key_projection :
    check_artifactRefJson_parses_as_exact_four_key_projection = true := by native_decide

/-! ## Signal Triangulation — the whole oracle -/

theorem signalAllCodes_length : check_signalAllCodes_length = true := by native_decide

theorem signalAllCodes_nodup : check_signalAllCodes_nodup = true := by native_decide

theorem signalClassPairs_length : check_signalClassPairs_length = true := by native_decide

theorem signalClassPairs_complete :
    check_signalClassPairs_complete = true := by native_decide

theorem signal_every_row_solves_at_exactly_its_own_index :
    check_signal_every_row_solves_at_exactly_its_own_index = true := by native_decide

/-! ## The rendered descriptors, against their own validators and kernels -/

theorem relayDescriptor_exact_schema :
    check_relayDescriptor_exact_schema = true := by native_decide

theorem salvageDescriptor_exact_schema :
    check_salvageDescriptor_exact_schema = true := by native_decide

theorem blackBoxDescriptor_exact_schema :
    check_blackBoxDescriptor_exact_schema = true := by native_decide

theorem blackBox_table_is_the_kernel :
    check_blackBox_table_is_the_kernel = true := by native_decide

theorem blackBox_witnesses_are_the_kernel :
    check_blackBox_witnesses_are_the_kernel = true := by native_decide

theorem signalDescriptor_exact_schema :
    check_signalDescriptor_exact_schema = true := by native_decide

/-! ## The artifact does not determine the instance — one per game -/

theorem signalDescriptor_does_not_determine_the_target :
    check_signalDescriptor_does_not_determine_the_target = true := by native_decide

theorem signalDescriptor_demo_seeds_both_draw :
    check_signalDescriptor_demo_seeds_both_draw = true := by native_decide

theorem relayDescriptor_does_not_determine_the_board :
    check_relayDescriptor_does_not_determine_the_board = true := by native_decide

theorem salvageDescriptor_does_not_determine_the_board :
    check_salvageDescriptor_does_not_determine_the_board = true := by native_decide

theorem blackBoxDescriptor_does_not_determine_the_order :
    check_blackBoxDescriptor_does_not_determine_the_order = true := by native_decide

theorem descentDescriptor_does_not_determine_the_board :
    check_descentDescriptor_does_not_determine_the_board = true := by native_decide

theorem artificerDescriptor_does_not_determine_the_rule :
    check_artificerDescriptor_does_not_determine_the_rule = true := by native_decide

theorem ventDescriptor_does_not_determine_the_vein :
    check_ventDescriptor_does_not_determine_the_vein = true := by native_decide

/-! ## The two path lists that must move together -/

theorem schemaJson_declares_exactly_the_canonical_game_paths :
    check_schemaJson_declares_exactly_the_canonical_game_paths = true := by native_decide

#assert_compiled parseBytes32Hex_test_federation_vector
#assert_compiled parseBytes32Hex_refuses_display_label
#assert_compiled fnv1a64_empty_vector
#assert_compiled fnv1a64_a_vector
#assert_compiled artifactRefJson_exact_four_key_vector
#assert_compiled artifactRefJson_parses_as_exact_four_key_projection
#assert_compiled signalAllCodes_length
#assert_compiled signalAllCodes_nodup
#assert_compiled signalClassPairs_length
#assert_compiled signalClassPairs_complete
#assert_compiled signal_every_row_solves_at_exactly_its_own_index
#assert_compiled relayDescriptor_exact_schema
#assert_compiled salvageDescriptor_exact_schema
#assert_compiled blackBoxDescriptor_exact_schema
#assert_compiled blackBox_table_is_the_kernel
#assert_compiled blackBox_witnesses_are_the_kernel
#assert_compiled signalDescriptor_exact_schema
#assert_compiled signalDescriptor_does_not_determine_the_target
#assert_compiled signalDescriptor_demo_seeds_both_draw
#assert_compiled relayDescriptor_does_not_determine_the_board
#assert_compiled salvageDescriptor_does_not_determine_the_board
#assert_compiled blackBoxDescriptor_does_not_determine_the_order
#assert_compiled descentDescriptor_does_not_determine_the_board
#assert_compiled artificerDescriptor_does_not_determine_the_rule
#assert_compiled ventDescriptor_does_not_determine_the_vein
#assert_compiled schemaJson_declares_exactly_the_canonical_game_paths

end Dregg2.Games.PathOfAngels.Emit
