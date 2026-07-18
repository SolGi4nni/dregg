/-
# EmitByName — the byte source for the WHOLE `circuit/descriptors/by-name/` surface.

Prints one `<filename>\t<emitVmJson2 descriptor>` line per checked-in by-name descriptor, so
`scripts/emit_descriptors.py` can regenerate every one of them FROM THE VERIFIED LEAN EMISSION —
the same snapshot→emit→diff treatment the main `circuit/descriptors/*.json` set already gets.

    lake env lean --run EmitByName.lean

## Why this file exists

`by-name/` is the set `circuit/src/descriptor_by_name.rs::descriptor_by_name()` — the production
predicate-dispatch registry — serves to `bridge/` and `wire/` at verify time. Until this emitter,
NOTHING regenerated it: `emit_descriptors.py`'s coverage check walked `DESC.iterdir()` filtered on
`p.is_file()`, and `by-name/` is a DIRECTORY, so the entire deployed dispatch surface was silently
exempt from the drift gate. The gate's snapshot→emit→diff therefore left `by-name/` byte-identical
on both sides — an unconditional PASS for any content whatsoever. The real chain had an UNGATED
hand-transcription hop in it:

    Lean descriptor ==(#guard)== Lean golden ==(HAND TRANSCRIPTION, ungated)== disk bytes

That hop is where `predicate-arith.json` drifted from its 24-wide welded Lean author down to a
5-wide re-authoring with the two Poseidon2 value↔fact weld legs missing — a CRITICAL, deployed,
demonstrated forgery (the compared value and the committed fact had disjoint constraint sets, so a
prover could satisfy `value ≥ threshold` on a value of its choosing while presenting the honest
verifier-expected `fact_commitment` for an unrelated value). This emitter deletes the hop.

Law #1: the constraints are AUTHORED in the `Dregg2/Circuit/Emit/*` modules (proved there, with
their `emitVmJson2` `#guard`s); this file only SERIALIZES them. Rust interprets; Rust authors
nothing. A descriptor reachable from here can never again disagree with its Lean author, because
the artifact IS the Lean author's output.
-/
import Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit
import Dregg2.Circuit.Emit.AdjacencyMembershipEmit
import Dregg2.Circuit.Emit.AttestedFactMembershipEmit
import Dregg2.Circuit.Emit.AutomataflStepEmit
import Dregg2.Circuit.Emit.BlindedMembershipEmit
import Dregg2.Circuit.Emit.BoundPresentationEmit
import Dregg2.Circuit.Emit.BridgeActionEmit
import Dregg2.Circuit.Emit.DerivationEmit
import Dregg2.Circuit.Emit.DfaRoutingEmit
import Dregg2.Circuit.Emit.DyckStackEmit
import Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding
import Dregg2.Circuit.Emit.FieldDeltaRangeEmit
import Dregg2.Circuit.Emit.MerkleMembership4aryEmit
import Dregg2.Circuit.Emit.MerkleMembershipEmit
import Dregg2.Circuit.Emit.NonRevocationAdjacencyEmit
import Dregg2.Circuit.Emit.NonRevocationEmit
import Dregg2.Circuit.Emit.NoteSpendingLeafEmit
import Dregg2.Circuit.Emit.Poseidon2HashEmit
import Dregg2.Circuit.Emit.PredicatesArithmeticEmit
import Dregg2.Circuit.Emit.PredicatesGtEmit
import Dregg2.Circuit.Emit.PredicatesInRangeEmit
import Dregg2.Circuit.Emit.PredicatesLeEmit
import Dregg2.Circuit.Emit.PredicatesLtEmit
import Dregg2.Circuit.Emit.PredicatesNeqEmit
import Dregg2.Circuit.Emit.PresentationEmit
import Dregg2.Circuit.Emit.QuantifiedAbsenceEmit
import Dregg2.Circuit.Emit.TemporalPredicateEmit

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 emitVmJson2)

/-- The by-name routing table: `(checked-in filename, the Lean descriptor that authors it)`.

Each entry is the SOLE authorship of its artifact. Adding a by-name descriptor without adding it
here is a routing gap `emit_descriptors.py` REFUSES (its coverage check recurses into `by-name/`
and fails on any checked-in file no emitter reproduces) — so this table cannot silently fall
behind the directory.

Three notes the mechanical reader needs:
* `blindedMembership4aryDesc` is depth-PARAMETERIZED in Lean; the two checked-in artifacts are its
  `depth := 2` and `depth := 8` instances. (The constraint block is depth-uniform — only the `name`
  field differs — but both are checked in, so both are emitted.)
* `NoteSpendingLeafEmit` carries a DECOY: `noteSpendLeafDescFixed` shares `noteSpendLeafDesc`'s
  exact `name` and `trace_width` (149) while emitting different bytes. The deployed artifact is
  `noteSpendLeafDesc`; matching on the header alone would pick the wrong one.
* `dyck-parse.json` is EMITTED but not yet DISPATCHED: `descriptor_by_name.rs` has no arm for it,
  because `circuit/src/dsl/dyck_stack.rs` still hand-builds the IR-v1 `CircuitDescriptor` the Dyck
  prover/tamper suite drives. It is registered here anyway — routing it through this table is what
  makes the byte-pin RE-DERIVABLE and puts the Dyck circuit under the drift gate (law #1's spine);
  the loader flip is the follow-up. The routing table is a superset of the dispatch table by
  design: the coverage check fails on a checked-in file NO emitter reproduces, never on an emitted
  descriptor Rust does not yet serve. -/
def byNameDescriptors : List (String × EffectVmDescriptor2) :=
  [ ("accumulator-nonrev.json",
      Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit.accumulatorNonRevDesc)
  , ("adjacency-membership.json",
      Dregg2.Circuit.Emit.AdjacencyMembershipEmit.adjacencyDesc)
  , ("attested-fact-membership.json",
      Dregg2.Circuit.Emit.AttestedFactMembershipEmit.attestedFactMembershipDesc)
  , ("automatafl-step.json",
      Dregg2.Circuit.Emit.AutomataflStepEmit.automataflStepDesc)
  , ("blinded-membership-4ary-depth2.json",
      Dregg2.Circuit.Emit.BlindedMembershipEmit.blindedMembership4aryDesc 2)
  , ("blinded-membership-4ary-depth8.json",
      Dregg2.Circuit.Emit.BlindedMembershipEmit.blindedMembership4aryDesc 8)
  , ("blinded-membership.json",
      Dregg2.Circuit.Emit.BlindedMembershipEmit.blindedMembershipDesc)
  , ("bound-presentation.json",
      Dregg2.Circuit.Emit.BoundPresentationEmit.boundPresentationDesc)
  , ("bridge-action.json",
      Dregg2.Circuit.Emit.BridgeActionEmit.bridgeActionDesc)
  , ("derivation.json",
      Dregg2.Circuit.Emit.DerivationEmit.derivationDesc)
  , ("dfa-routing.json",
      Dregg2.Circuit.Emit.DfaRoutingEmit.dfaRoutingDesc)
  , ("dyck-parse.json",
      Dregg2.Circuit.Emit.DyckStackEmit.dyckParseDesc)
  , ("field-delta-result-range.json",
      Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor)
  , ("merkle-membership-4ary-general.json",
      Dregg2.Circuit.Emit.MerkleMembership4aryEmit.membership4aryDesc)
  , ("merkle-membership-depth2.json",
      Dregg2.Circuit.Emit.MerkleMembershipEmit.merkleMembershipDesc)
  , ("non-revocation-adjacency.json",
      Dregg2.Circuit.Emit.NonRevocationAdjacencyEmit.nonRevocationAdjacencyDesc)
  , ("non-revocation.json",
      Dregg2.Circuit.Emit.NonRevocationEmit.nonRevocationDesc)
  , ("note-spend-leaf.json",
      Dregg2.Circuit.Emit.NoteSpendingLeafEmit.noteSpendLeafDesc)
  , ("poseidon2-hash-arity2.json",
      Dregg2.Circuit.Emit.Poseidon2HashEmit.poseidon2HashDesc)
  , ("predicate-arith-gt.json",
      Dregg2.Circuit.Emit.PredicatesGtEmit.predicateGtDesc)
  , ("predicate-arith-inrange.json",
      Dregg2.Circuit.Emit.PredicatesInRangeEmit.predicateInRangeDesc)
  , ("predicate-arith-le.json",
      Dregg2.Circuit.Emit.PredicatesLeEmit.predicateLeDesc)
  , ("predicate-arith-lt.json",
      Dregg2.Circuit.Emit.PredicatesLtEmit.predicateLtDesc)
  , ("predicate-arith-neq.json",
      Dregg2.Circuit.Emit.PredicatesNeqEmit.predicateNeqDesc)
  , ("predicate-arith.json",
      Dregg2.Circuit.Emit.PredicatesArithmeticEmit.predicateGeDesc)
  , ("presentation-freshness.json",
      Dregg2.Circuit.Emit.PresentationEmit.presentationFreshnessDesc)
  , ("quantified-absence.json",
      Dregg2.Circuit.Emit.QuantifiedAbsenceEmit.quantifiedAbsenceDesc)
  , ("temporal-predicate.json",
      Dregg2.Circuit.Emit.TemporalPredicateEmit.temporalPredicateDesc)
  , ("turn-chain-binding.json",
      Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding.turnChainBindingDescriptor)
  ]

/- The routing table covers the checked-in directory exactly (29 artifacts). A bare count is a
weak guard, but it is the one this file can state without IO: the STRONG guard is
`emit_descriptors.py`'s recursive coverage check, which fails on any by-name file this table does
not reproduce. -/
#guard byNameDescriptors.length == 29

def main : IO Unit := do
  for (file, d) in byNameDescriptors do
    IO.println s!"{file}\t{emitVmJson2 d}"
