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
import Dregg2.Circuit.Emit.AdjacencyMembershipWideEmit
import Dregg2.Circuit.Emit.AttestedFactMembershipEmit
import Dregg2.Circuit.Emit.AutomataflResolveEmit
import Dregg2.Circuit.Emit.AutomataflStepEmit
import Dregg2.Circuit.Emit.AutomataflNGenGolden
import Dregg2.Circuit.Emit.AutomataflLegCEmit
import Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone
import Dregg2.Circuit.Emit.AutomataflStepMarksGolden
import Dregg2.Circuit.Emit.BlindedMembershipEmit
import Dregg2.Circuit.Emit.BlindedMembershipWideEmit
import Dregg2.Circuit.Emit.BoundPresentationEmit
import Dregg2.Circuit.Emit.BridgeActionEmit
import Dregg2.Circuit.Emit.DerivationEmit
import Dregg2.Circuit.Emit.DfaRoutingEmit
import Dregg2.Circuit.Emit.DfaRoutingTableEmit
import Dregg2.Circuit.Emit.DyckStackEmit
import Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit
import Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding
import Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld
import Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan
import Dregg2.Circuit.Emit.FieldDeltaRangeEmit
import Dregg2.Circuit.Emit.MerkleMembership4aryEmit
import Dregg2.Circuit.Emit.MerkleMembership4aryWideEmit
import Dregg2.Circuit.Emit.MerkleMembershipEmit
import Dregg2.Circuit.Emit.MinaFixtureEmit
import Dregg2.Circuit.Emit.LightClientMinaAir
import Dregg2.Circuit.Emit.LightClientMinaLinkAir
import Dregg2.Circuit.Emit.LightClientSolStakeFoldAir
import Dregg2.Circuit.Emit.NoteSpendingLeafEmit
import Dregg2.Circuit.Emit.Poseidon2HashEmit
import Dregg2.Circuit.Emit.PastaMsmWindowed
import Dregg2.Circuit.Emit.PastaMsmSliced
import Dregg2.Circuit.Emit.PastaFieldSound
import Dregg2.Circuit.Emit.PastaAddSubSound
import Dregg2.Circuit.Emit.MinaWrapVerifierAir
import Dregg2.Circuit.Emit.MinaWrapVerifierProgram
import Dregg2.Circuit.Emit.MinaPhase2Chain
import Dregg2.Circuit.Emit.PredicatesArithmeticEmit
import Dregg2.Circuit.Emit.PredicatesGtEmit
import Dregg2.Circuit.Emit.PredicatesInRangeEmit
import Dregg2.Circuit.Emit.PredicatesLeEmit
import Dregg2.Circuit.Emit.PredicatesLtEmit
import Dregg2.Circuit.Emit.PredicatesNeqEmit
import Dregg2.Circuit.Emit.PresentationEmit
import Dregg2.Circuit.Emit.QuantifiedAbsenceEmit
import Dregg2.Circuit.Emit.TemporalPredicateEmit
-- The four STARK-ified peer-chain lightclient verification AIRs (bridge tree). Each emits its
-- consensus-verification as an `EffectVmDescriptor2` carrying the chain's no-forgery obligation
-- (`eth_no_forgery` / `tmNoForgery` / `sol_no_forgery` / `mid_no_forgery`); routing them here puts
-- their byte-pinned descriptors under the same Lean-authored drift gate as every other by-name
-- artifact, so a dregg node emits + proves them from the VERIFIED Lean emission (the prerequisite
-- for the gnark peer-wrap → on-chain DreggPeerRegistry flow).
import Dregg2.Circuit.Emit.LightClientEthAir
import Dregg2.Circuit.Emit.LightClientTendermintAir
import Dregg2.Circuit.Emit.LightClientSolanaAir
import Dregg2.Circuit.Emit.LightClientMidnightAir
import Dregg2.Crypto.PrivateGraphRewriteDescriptor
import Dregg2.Games.PrivateQuestGraphDescriptor
import Dregg2.Crypto.PrivateGraphRewriteCellDescriptor
import Dregg2.Games.PrivatePreferenceDescriptor
import Dregg2.Games.PrivatePreferenceCellDescriptor
import Dregg2.Games.DescentCensusDescriptor
import Dregg2.Circuit.Emit.ShieldedWholeNoteSwapSubstrateDescriptor
import Dregg2.Circuit.Emit.ShieldedSpendDescriptor
import Dregg2.Circuit.Emit.ShieldedWideValueLinkDescriptor
import Dregg2.Circuit.ShieldedValueRangeDischarge
import Dregg2.Games.PrivateRaidAssignmentDescriptor
import Dregg2.Games.PrivateShuffleDescriptor
import Dregg2.Games.PrivateShuffleFairDescriptor
import Market.DarkBazaarPrivateDescriptor
import Market.DarkBazaarPrivatePoaDescriptor
import Market.DarkBazaarPrivatePoaSettlementDescriptor
-- The fixed q0/N8 exact-public BFV NTT butterfly stage descriptors (`stage{0,1,2}Descriptor`, the
-- three four-row per-stage LogUp relations). Emitted here so `by-name/*bfv*butterfly*stage*-exact-
-- public.json` are drift-checked from their Lean author, not left as un-reproduced checked-in bytes.
import Market.PrivateBookBfvExactPublicConsumer
import Market.DarkAmmPrivateDescriptor
import Market.PrivateBookBfvSliceDescriptor
import Market.PrivateBookBfvButterflyAir

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
* `mina-fixture.json` is EMITTED but not DISPATCHED, and never will be: it is not a predicate
  descriptor. `circuit/src/bin/mina_stark_fixture.rs` `include_str!`s it directly to mint the
  fixture proof `bridge/mina-zkapp` verifies. It is routed here for the same reason everything
  else is — so the artifact is RE-DERIVED from `MinaFixtureEmit.lean` on every drift run rather
  than transcribed once. (It replaced a hand-written Rust AIR; see HORIZONLOG E4.)
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
  -- ⚑ node8 CUTOVER: `adjacency-membership.json` (`adjacencyDesc`) is RETIRED — its per-level
  -- node was `chipLookupTupleNarrow [left, right] par`, the arity-2 NARROW bus binding `out0`
  -- alone, so every interior node, both leaf PIs and the root PI committed at ~31 bits and were
  -- collidable at 2^15.45 (`circuit/tests/adjacency_forge_tooth.rs` exhibits the forge: a MEMBER
  -- of the committed set passes the sorted-set NON-membership gate). The narrow `def` survives in
  -- `AdjacencyMembershipEmit` ONLY as the object the wide module's anti-masquerade tooth
  -- quantifies over (`narrowNode2Lane0`, `interior_forge_narrow_admits_wide_refuses`) and as the
  -- subject of the `AdjacencyMembershipRefine`/`Rung2` refinement rungs — you cannot state "the
  -- old fold admits this" without the old fold. It is emitted nowhere.
  , ("adjacency-membership-wide.json",
      Dregg2.Circuit.Emit.AdjacencyMembershipWideEmit.adjacencyWideDesc)
  , ("attested-fact-membership.json",
      Dregg2.Circuit.Emit.AttestedFactMembershipEmit.attestedFactMembershipDesc)
  , ("automatafl-resolve.json",
      Dregg2.Circuit.Emit.AutomataflResolveEmit.automataflResolveDesc)
  , ("automatafl-step.json",
      Dregg2.Circuit.Emit.AutomataflStepEmit.automataflStepDesc)
  , ("automatafl-step-n11.json",
      Dregg2.Circuit.Emit.AutomataflNGenGolden.automataflStepDescN11)
  , ("automatafl-resolve-n11.json",
      Dregg2.Circuit.Emit.AutomataflNGenGolden.automataflResolveDescN11)
  , ("automatafl-legc-n5.json",
      Dregg2.Circuit.Emit.AutomataflLegCEmit.automataflLegCDescN 5)
  , ("automatafl-legc-n11.json",
      Dregg2.Circuit.Emit.AutomataflLegCEmit.automataflLegCDescN 11)
  , ("automatafl-resolve-marks-n2.json",
      Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone.automataflResolveMarksDescN 2)
  , ("automatafl-resolve-marks-n11.json",
      Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone.automataflResolveMarksDescN 11)
  , ("automatafl-step-marks-n2.json",
      Dregg2.Circuit.Emit.AutomataflStepMarksCapstone.automataflStepMarksDescN 2)
  , ("automatafl-step-marks-n11.json",
      Dregg2.Circuit.Emit.AutomataflStepMarksCapstone.automataflStepMarksDescN 11)
  -- ⚑ node8 CUTOVER: the depth-keyed ONE-FELT blinded 4-ary pair
  -- (`blinded-membership-4ary-depth{2,8}.json`, `blindedMembership4aryDesc`) is RETIRED. Its
  -- node fold chained lane 0 only, so every interior node, the root PI and the published
  -- blinded leaf were ~31-bit. The wide twin is depth-uniform (the depth rides the trace
  -- height), so one row replaces two.
  , ("blinded-membership-4ary-wide.json",
      Dregg2.Circuit.Emit.BlindedMembershipWideEmit.blindedMembershipWideDesc)
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
  -- The TABLE-AS-INPUT DFA-routing instance (`DfaRoutingTableEmit.lean`). Its refinement
  -- `tableRouting_refines_classify` is over the WHOLE emitted descriptor and GENERAL over the
  -- transition table `tbl`, the automaton `d` and the descriptor `name` — strictly
  -- better-conditioned than `dfa-routing.json`'s per-automaton refinement, which carries a
  -- terminal-step hypothesis (`hterm`: the transition-zerofier leaves the last row unasserted) and
  -- a mod-`p` canonicality envelope. Here the transition tooth is ONE `exactPublicRows` lookup
  -- (row-uniform: no last-row exemption) and table membership is an exact ℤ equality, so neither
  -- residual exists. Routed here so the served bytes are RE-DERIVED from that Lean author.
  , ("dfa-routing-table-exact-public-v1.json",
      Dregg2.Circuit.Emit.DfaRoutingTableEmit.demoRoutingDesc)
  , ("dyck-parse.json",
      Dregg2.Circuit.Emit.DyckStackEmit.dyckParseDesc)
  , ("field-delta-result-range.json",
      Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor)
  , ("faithful-note-spend-v2.json",
      Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan.faithfulNoteSpendDescriptor)
  , ("faithful-note-spend-exact-v3.json",
      Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld.exactNullifierAafiRotatedStateDescriptor)
  -- ⚑ node8 CUTOVER: `merkle-membership-4ary-general.json` (`membership4aryDesc`) is RETIRED —
  -- its per-level node was `chip_absorb_all_lanes(4, children)[0]`, ONE BabyBear felt, so the
  -- whole tree committed at ~31 bits and was collidable at 2^15.5
  -- (`circuit/tests/membership_forge_tooth.rs` exhibits the forge). The narrow `def` survives in
  -- `MerkleMembership4aryEmit` ONLY as the object the wide module's anti-masquerade tooth
  -- quantifies over (`narrowFold4Lane0`, `interior_forge_narrow_admits_wide_refuses`) — you
  -- cannot state "the old fold admits this" without the old fold. It is emitted nowhere.
  , ("merkle-membership-4ary-wide-general.json",
      Dregg2.Circuit.Emit.MerkleMembership4aryWideEmit.merkleMembership4aryWideDesc)
  , ("merkle-membership-depth2.json",
      Dregg2.Circuit.Emit.MerkleMembershipEmit.merkleMembershipDesc)
  , ("mina-fixture.json",
      Dregg2.Circuit.Emit.MinaFixtureEmit.minaFixtureDesc)
  , ("note-spend-leaf.json",
      Dregg2.Circuit.Emit.NoteSpendingLeafEmit.noteSpendLeafDesc)
  , ("poseidon2-hash-arity2.json",
      Dregg2.Circuit.Emit.Poseidon2HashEmit.poseidon2HashDesc)
  -- The two Pasta ALU descriptors are the shared fp/fq modular-arithmetic
  -- rows used by the Mina wrap verifier. They were checked in and served but
  -- omitted from this source-of-truth routing table, which made the canonical
  -- emitter refuse the whole by-name surface as a routing gap.
  , ("pasta-alu-sound.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierAir.fpAluDesc)
  , ("pasta-sbox-prog.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierProgram.sboxDesc)
  , ("pasta-sbox-prog-1k.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierProgram.longDesc)
  , ("pasta-alu-fq-sound.json",
      Dregg2.Circuit.Emit.MinaWrapVerifierAir.fqAluDesc)
  -- ⚑ 2026-08-05 — THE EIGHT-BLOCK PHASE-2 CHAIN LINK, routed so its bytes are re-derivable from
  -- Lean on a flag day. `MinaPhase2Chain.the_chain_air_extends_the_program_air`: this and
  -- `dregg-pasta-fq-wraplink::v1` are the SAME `programAir qLimb absorbProg` (2048-instruction
  -- `fq_kimchi` ROM); only the boundary pin blocks differ — `chainPins` pins EIGHT
  -- (`in(3) ++ out(3) ++ absorbed(2)`, 256 PIs) where `linkPins` pins SEVEN (224 PIs) and exposes
  -- only TWO of a Poseidon state's THREE outgoing lanes. That missing third lane is why a chain
  -- welded on the wraplink hands a third of its state on as a free prover scalar.
  , ("pasta-fq-chainlink.json",
      Dregg2.Circuit.Emit.MinaPhase2Chain.chainDesc)
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
  , ("dark-bazaar-private-n4k4.json",
      Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4Descriptor)
  , ("dark-bazaar-private-poa-n4k4-v2.json",
      Market.DarkBazaarPrivatePoaDescriptor.darkBazaarPrivatePoaN4K4Descriptor)
  , ("dark-bazaar-private-poa-settlement-n4k4-v3.json",
      Market.DarkBazaarPrivatePoaSettlementDescriptor.darkBazaarPrivatePoaSettlementN4K4Descriptor)
  , ("private-book-bfv-slice-o0-c0-q0-k0.json",
      Market.PrivateBookBfvSliceDescriptor.privateBookBfvSliceDescriptor)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n8.json",
      Market.PrivateBookBfvButterflyAir.butterflyDescriptor)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n4096.json",
      Market.PrivateBookBfvButterflyAir.productionQ0N4096Descriptor)
  , ("private-book-bfv-odd-intt-butterfly-q0-n4096.json",
      Market.PrivateBookBfvButterflyAir.productionQ0N4096InverseDescriptor)
  , ("private-book-bfv-threshold-terminal-q0-b80.json",
      Market.PrivateBookBfvButterflyAir.thresholdTerminalQ0Descriptor)
  , ("dark-amm-private-v1.json",
      Market.DarkAmmPrivateDescriptor.darkAmmPrivateDescriptor)
  , ("private-preference-n4k4.json",
      Dregg2.Games.PrivatePreferenceDescriptor.privatePreferenceN4K4Descriptor)
  , ("private-preference-cell-n4k4.json",
      Dregg2.Games.PrivatePreferenceCellDescriptor.privatePreferenceCellN4K4Descriptor)
  , ("private-shuffle-n8.json",
      Dregg2.Games.PrivateShuffleDescriptor.privateShuffleN8Descriptor)
  , ("private-shuffle-fair-n8.json",
      Dregg2.Games.PrivateShuffleFairDescriptor.privateShuffleFairN8Descriptor)
  , ("private-raid-assignment-n4.json",
      Dregg2.Games.PrivateRaidAssignmentDescriptor.privateRaidAssignmentN4Descriptor)
  , ("private-graph-rewrite-4x2.json",
      Dregg2.Crypto.PrivateGraphRewriteDescriptor.privateGraphRewriteDescriptor)
  , ("private-graph-rewrite-cell-4x2.json",
      Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.privateGraphRewriteCellDescriptor)
  , ("private-quest-graph-4x2.json",
      Dregg2.Games.PrivateQuestGraphDescriptor.privateQuestGraphDescriptor)
  , ("descent-custody-census-fixed8-v1.json",
      Dregg2.Games.DescentCensusDescriptor.descentCensusDescriptor)
  , ("shielded-whole-note-swap-substrate-v1.json",
      Dregg2.Circuit.Emit.ShieldedWholeNoteSwapSubstrateDescriptor.shieldedWholeNoteSwapSubstrateDescriptor)
  -- ⚑ L3 (shielded apex redesign): the three already-PROVEN, previously-unrouted shielded
  -- descriptors land as emitted authority. Each is byte-pinned by a machine-checked
  -- `#guard emitVmJson2 <desc> == <GOLDEN>` in its authoring module — this table makes those
  -- bytes the SOLE checked-in artifact (house-law #1 for the shielded family). #15 spend-root
  -- pin, #17 ranged value-link + wraparound-refusal, #17 wide 8-lane value binding. Soundness
  -- WHEN USED still rests on L0's committed accumulator + the L4 route (not yet live).
  , ("dregg-shielded-spend-pinned-root-v1.json",
      Dregg2.Circuit.Emit.ShieldedSpendDescriptor.shieldedSpendDesc)
  , ("dregg-shielded-value-link-conserve-ranged-v1.json",
      Dregg2.Circuit.ShieldedValueRangeDischarge.shieldedValueLinkRangedDesc)
  , ("dregg-shielded-wide-value-link-conserve-v1.json",
      Dregg2.Circuit.Emit.ShieldedWideValueLinkDescriptor.shieldedWideValueLinkDesc)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n8-stage0-exact-public.json",
      Market.PrivateBookBfvExactPublicConsumer.stage0Descriptor)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n8-stage1-exact-public.json",
      Market.PrivateBookBfvExactPublicConsumer.stage1Descriptor)
  , ("private-book-bfv-odd-ntt-butterfly-q0-n8-stage2-exact-public.json",
      Market.PrivateBookBfvExactPublicConsumer.stage2Descriptor)
  -- THE hidden-span commitment descriptor: the WIDE-BLIND (5-blinding-lane, |R| = p⁵ ≈ 2^154.5)
  -- form. The narrow single-blinding-felt `guardedHidingSpanDesc` (~31-bit blinding space) was
  -- DELETED in the felt-width cutover of 2026-07-23 — it must never re-enter this table.
  , ("guarded-hiding-span-m0-wide-blinded-commit-blind5-v1.json",
      Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit.guardedHidingSpanWideBlindDesc)
  -- ⚑ The four peer-chain lightclient verification AIRs. Each is byte-pinned in its authoring
  -- module (`LightClient*Air.lean`); this table makes those bytes the SOLE checked-in artifact and
  -- RE-DERIVABLE from the Lean author (house-law #1). The descriptors carry the chain's consensus
  -- no-forgery obligation, so a dregg node can now emit + prove the STARK from `descriptor_by_name`
  -- — the producibility prerequisite for the gnark peer-wrap → on-chain `DreggPeerRegistry`
  -- true-peers flow. Soundness WHEN USED still rests on the undischarged FRI/STARK floor and each
  -- chain's trusted-instance mirror.
  --
  -- ⚑ FLAG DAY 2026-08-03, ETH ONLY: `ethLcVerifyDesc` is now COMPILER OUTPUT
  -- (`EffectLower.lowerAir` of the `EffectAir` source `ethHeadAir`, no hand-written `VmConstraint2`
  -- in its module) AND carries a new `PC_SLACK` leg that forces `PC ≤ BL` — the unbounded
  -- participation count that PROVED at `PC = 1023` against a 512-key committee. Trace width 20 → 21,
  -- constraints 20 → 22, all eleven anchor columns shifted up by one; the PI surface is UNCHANGED
  -- (11 slots, same meanings). `dregg-eth-lightclient-verify-v1.json` RE-EMITS and its VK must be
  -- re-minted; no other descriptor moves, nothing re-genesises. Its module's byte-golden `#guard` is
  -- retired in favour of `rfl` pins on the compiler's own emission.
  , ("dregg-eth-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientEthAir.ethLcVerifyDesc)
  , ("dregg-tm-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientTendermintAir.tmLcVerifyDesc)
    -- ⚑⚑ FLAG DAY 2026-08-04, SOLANA: `solLcVerifyDesc` is now COMPILER OUTPUT
    -- (`EffectLower.lowerAir` of the `EffectAir` source `solLcVerifyAir`, no hand-written
    -- `VmConstraint2` in its module; `solLcVerifyAir_mainRailOk = true` by `rfl`) and it is
    -- **MULTI-ROW**: it ABSORBS `dregg-solana-stake-table-fold::v1`'s 44 columns from the SAME
    -- source leg list (`foldLegs`, `sol_fold_block_is_the_shared_source`), one row per stake-table
    -- entry. Trace width 49 → 79, PIs 23 → 22, constraints 63 → 103, declared tables 2 → 4.
    -- `ANCHOR_ROOT` moved from NINE `.first` radix-2^31 limbs that no constraint read to the fold's
    -- EIGHT `.last` output lanes, so the light client's trust anchor is the IMAGE of the rows
    -- (2^123.63 birthday, over 8 · 30.906891 = 247.26 bits — NOT the 2^247.3 second-preimage
    -- figure); the DENOMINATOR moved from four dedicated `.first` columns to the fold's accumulator
    -- on the last row; and `STAKE_TABLE_OK` was DELETED because the fold computes what it asserted
    -- (`LightClientSolStakeFoldAir.solLcAir_table_carrier_from_the_fold` discharges the bridge's
    -- `stakeTableOk` from the emitted pin). ⚠ `dregg-solana-lightclient-verify-v1.json` RE-EMITS and
    -- its VK ROTATES; both the width and the PI count move, so a stale row or PI vector REFUSES TO
    -- LOAD. ⚠ Callers must now supply a POSEIDON2 root in PI[0..7]: `EpochStakeTable::root` is a
    -- domain-separated SHA-256 and must be re-anchored to `dregg-solana-stake-table-root:v2` with
    -- every `WeakSubjectivityAnchor.stake_table_root` re-derived. Until then a caller passing the
    -- SHA root is refused at the pin. The FOLD rung's own bytes are UNCHANGED.
  , ("dregg-solana-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientSolanaAir.solLcVerifyDesc)
  , ("dregg-midnight-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientMidnightAir.midLcVerifyDesc)
    -- ⚑ THE FIFTH, AND THE ONE THAT LANDS. Mina was the one peer chain with a PROVEN, `@[export]`ed
    -- verify decision (`dregg_mina_lc_verify`) and NO emitted AIR, so a verified Mina block produced
    -- no dregg state transition at all. `minaLcVerifyDesc` is COMPILER OUTPUT — `EffectLower.lowerAir`
    -- of the `EffectAir` source `minaHeadAir`, no hand-written `VmConstraint2` anywhere in its module
    -- (`minaHeadAir_mainRailOk = true` by `rfl` records that the compiler's vocabulary was ADEQUATE).
    -- Unlike its four siblings this one is CONSUMED: `turn/src/executor/mina_head_verifier.rs`
    -- dispatches it from a `StateConstraint::Witnessed` and a turn is REFUSED
    -- (`TurnError::ProgramViolation`) unless the proof verifies against the CELL-PROGRAM-PINNED Mina
    -- weak-subjectivity anchor and the head the turn actually records.
  , ("dregg-mina-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientMinaAir.minaLcVerifyDesc)
    -- ⚑ The MULTI-ROW companion (2026-08-03): `dregg-mina-lightclient-link::v1`, one row per
    -- EXHIBITED Mina block. `minaLinkDesc` is COMPILER OUTPUT — `EffectLower.lowerAir` of the
    -- `EffectAir` source `minaLinkAir`, no hand-written `VmConstraint2` in its module. It is the
    -- first COMPILER-AUTHORED MULTI-ROW descriptor in the tree (twelve `.transition` window legs;
    -- `minaLinkAir_mainRailOk = true` by `rfl` records that the vocabulary was adequate). It
    -- derives the SHAPE half of `LINK_OK` — nine-lane parent linkage, height contiguity, and the
    -- segment length as a counted row total — and NOT the Poseidon-over-Pasta half, which stays
    -- witnessed (`LinkHashResidual`).
  , ("dregg-mina-lightclient-link-v1.json",
      Dregg2.Circuit.Emit.LightClientMinaLinkAir.minaLinkDesc)
    -- ⚑ THE SOLANA STAKE-TABLE FOLD (2026-08-04): `dregg-solana-stake-table-fold::v1`, ONE ROW PER
    -- STAKE-TABLE ENTRY. `solStakeFoldDesc` is COMPILER OUTPUT — `EffectLower.lowerAir` of the
    -- `EffectAir` source `solStakeFoldAir`, no hand-written `VmConstraint2` in its module
    -- (`solStakeFoldAir_mainRailOk = true` by `rfl`). It DERIVES both of the numbers the Solana
    -- light client's trust story hangs from, from the SAME exhibited rows: the eight-lane Poseidon2
    -- commitment to the stake table (LAST-row PI pins) and the u64 active-stake DENOMINATOR (the
    -- LAST-row value of a limb accumulator with boolean carries). That pair is the point — a swapped
    -- validator set with an IDENTICAL tally clears every denominator pin `solLcVerifyDesc` has and
    -- moves the root (`FoldScheme.same_tally_moves_the_root`, and the deployed-prover half in
    -- `circuit-prove/tests/solana_stake_table_fold.rs`). ⚑ THE HASH WAS CHOSEN BY MEASUREMENT: the
    -- SHA-256 shape of the same fact is 18,049,248 constraints / 12,831,336 columns at 703 live vote
    -- accounts (`LightClientSolanaAir` §6c) against a proved ceiling of 2,131 columns; this is 44
    -- columns and 58 constraints at ANY validator count, because the validators are ROWS and a
    -- Poseidon2 absorb here is ONE chip lookup. ⚠ FLAG DAY: emit
    -- `circuit/descriptors/by-name/dregg-solana-stake-table-fold-v1.json` and MINT a VK. The
    -- commitment is NOT `EpochStakeTable::root`'s SHA-256 — a consumer that wants them to agree must
    -- re-anchor that dregg-authored root onto this Poseidon2 frame and re-derive every
    -- `WeakSubjectivityAnchor.stake_table_root`. ⚑ SUPERSEDED SAME DAY: that sentence continued
    -- "`solLcVerifyDesc` is untouched, no VK rotates" — it is no longer true and was never a reason.
    -- The verify rung ABSORBED this fold's legs (see its routing note above); the two now share ONE
    -- source list and this rung's own emitted bytes did not move.
  , ("dregg-solana-stake-table-fold-v1.json",
      Dregg2.Circuit.Emit.LightClientSolStakeFoldAir.solStakeFoldDesc)
    -- ⚑ THE LEAN-AUTHORED PASTA AIRs. `pasta-rcb-windowed.json` was checked in UNROUTED — its
    -- bytes were not re-derivable from Lean, which is precisely the ungated hand-transcription hop
    -- this file exists to delete, on the descriptor the whole Mina opening-check arc rests on.
  , ("pasta-rcb-windowed.json",
      Dregg2.Circuit.Emit.PastaMsmWindowed.windowedRowDesc)
    -- The FOUR-WAY CUT, at the REAL parameters: 8,192 generators per slice. The offset is a
    -- LITERAL in each emitted gate, so these are four distinct objects and routing them
    -- separately is the point, not duplication.
  , ("pasta-rcb-sg-slice-0-of-4.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 0 8192)
  , ("pasta-rcb-sg-slice-1-of-4.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 1 8192)
  , ("pasta-rcb-sg-slice-2-of-4.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 2 8192)
  , ("pasta-rcb-sg-slice-3-of-4.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 3 8192)
    -- …and at the width that PROVES on a box (`circuit/tests/pasta_sliced_sg_prove.rs`). Same
    -- `def`, different width literal; `slices_compose` is width-independent, the measurement is not.
  , ("pasta-rcb-sg-slice-0-of-4-w8.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 0 8)
  , ("pasta-rcb-sg-slice-1-of-4-w8.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 1 8)
  , ("pasta-rcb-sg-slice-2-of-4-w8.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 2 8)
  , ("pasta-rcb-sg-slice-3-of-4-w8.json",
      Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 3 8)
    -- ⚑ THE FELT-SOUND REPLACEMENTS for the six Pasta field ops. The nine `pasta-rcb-*` entries
    -- above are read over ℤ and the deployed prover reads them mod BabyBear; both halves of that
    -- gap are now exhibited as PROVING falsifiers against the very first entry
    -- (`circuit/tests/pasta_{field,addsub}_felt_soundness.rs`). These six are the encodings whose
    -- every gate body FITS a felt, so the two readings coincide — `8×32` limbs, range-checked
    -- carries, and a forcing theorem whose HYPOTHESIS is the mod-`P` reading
    -- (`PastaFieldSound.felt_gates_force_congruence`, `PastaAddSubSound.addsub_gates_force_congruence`).
    --
    -- ⚑ They landed here UNROUTED on 2026-08-03 (`3dcefe00a`, the multiply pair) — checked into
    -- `by-name/` with no entry in this table, which is exactly the ungated hand-transcription hop
    -- the comment above records, and `--verify-by-name-routing` named both by hand. Routed now,
    -- with the add/sub four.
  , ("pasta-fpmul-sound.json",
      Dregg2.Circuit.Emit.PastaFieldSound.fpMulSoundDesc)
  , ("pasta-fqmul-sound.json",
      Dregg2.Circuit.Emit.PastaFieldSound.fqMulSoundDesc)
  , ("pasta-fpadd-sound.json",
      Dregg2.Circuit.Emit.PastaAddSubSound.fpAddSoundDesc)
  , ("pasta-fpsub-sound.json",
      Dregg2.Circuit.Emit.PastaAddSubSound.fpSubSoundDesc)
  , ("pasta-fqadd-sound.json",
      Dregg2.Circuit.Emit.PastaAddSubSound.fqAddSoundDesc)
  , ("pasta-fqsub-sound.json",
      Dregg2.Circuit.Emit.PastaAddSubSound.fqSubSoundDesc)
  ]

/- The routing table covers the checked-in directory exactly. A bare count is a
weak guard, but it is the one this file can state without IO — and note what it does NOT say:
a table entry whose artifact was never committed still COUNTS, so this guard passes on a ghost.

Both directions are gated outside Lean:
* file → table: `emit_descriptors.py`'s recursive coverage check fails on any by-name file this
  table does not reproduce. Needs a full emit to say anything.
* table → file: `scripts/emit_descriptors.py --verify-by-name-routing` (CI job
  `descriptor-by-name-routing`, and a preflight in `check-descriptor-drift.sh`) reconciles this
  table against the tracked `by-name/` set AND the PROVENANCE stamp. It parses the name literals
  STATICALLY, so it keeps reporting while the emit is blocked. Adding an entry here without
  committing its artifact reds that gate by name. -/
-- ⚠ 89, not 87. This pin was STALE at 86 against 88 entries when this lane arrived: two sibling
-- lanes (`pasta-alu-sound` / `pasta-alu-fq-sound` / `dark-bazaar-private-poa-settlement-n4k4-v3`)
-- added routing rows in the shared tree and left the pin behind, so the file was already red for
-- everyone. 89 = those + `dregg-solana-stake-table-fold-v1.json`. A single shared line cannot be
-- bumped by only one lane's worth; whoever reads the blame should read it as three lanes' rows.
-- ⚠ 91, not 89: this lane added `pasta-sbox-prog` + `pasta-sbox-prog-1k` (the register-file /
-- instruction-ROM machine and its 2^10 instance). Same shared-line hazard as the note above — if
-- the blame on this line is one lane's, the count is probably still short.
theorem byNameDescriptors_length : byNameDescriptors.length = 92 := rfl

def main : IO Unit := do
  for (file, d) in byNameDescriptors do
    IO.println s!"{file}\t{emitVmJson2 d}"
