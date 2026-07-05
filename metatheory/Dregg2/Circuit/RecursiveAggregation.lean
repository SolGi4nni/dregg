/-
# Dregg2.Circuit.RecursiveAggregation — RECURSIVE-AGGREGATION SOUNDNESS (magnesium → gold).

**The headline.** A light client that verifies ONE succinct aggregate proof — and re-witnesses
NOTHING of the history — learns that the WHOLE chain of N finalized turns is correct:
every turn executed correctly per the verified executor, the chain is correctly ordered (no
reorder/drop/insert), and the final root is the genuine fold of the whole history. This is the model
that the IVC accumulator (`circuit/src/ivc_turn_chain.rs::prove_turn_chain_recursive` →
`WholeChainProof`) realizes; `verify_turn_chain_recursive` checks only the root, cost independent of N.

**Why proofs are ADDITIVE ATTESTATION here, and that is the POINT.** The light client does NOT
re-execute the history, does NOT re-hash the states, does NOT walk the blocklace. It checks the
succinct aggregate. The aggregate's validity, UNDER the named soundness hypotheses below, IS exactly
`HistoryAggregation.WellFormedChain` (`aggregate_attests_whole_history`) — so trusting the aggregate
is trusting the whole history. The verification IS the trust.

**What is PROVED vs. what is a NAMED, REALIZABLE hypothesis (the boundary).** You cannot prove
plonky3/pickles FRI-recursion soundness in Lean — it is the soundness of a concrete Rust prover over
a concrete field. So we NAME the three soundness facts the recursion engine supplies, as `structure`
fields the headline takes as hypotheses (each realizable: it is the standard SNARK soundness of a
fixed verifier circuit, which `DESIGN-recursion-aggregation-private-joint-turns.md` §H1 argues is a
BOUNDED obligation for plonky3's single fixed verifier AIR + differential testing):

  * **`InnerProofSound`** — an inner whole-turn step proof that VERIFIES attests the verified executor
    ran that turn (`recCexec pre turn = some post`). This is the EffectVm/descriptor
    circuit⟺executor soundness, ALREADY proved per-effect in Lean (`WholeTurnTriangle`,
    `EffectVmEmit*`) — here lifted to the leaf-proof boundary as the realized hypothesis the
    recursion engine carries up.
  * **`BindingAirSound`** — a `TurnChainBindingAir` leaf proof that VERIFIES attests the temporal
    tooth `new_root[i] == old_root[i+1]` over the whole chain (`HistoryAggregation.ChainBound`). The
    AIR's continuity constraint is `ivc_turn_chain.rs:246`; its in-circuit soundness is what the leaf
    proof's verification delivers.
  * **`RecursiveVerifierSound`** — an AGGREGATE proof that VERIFIES attests EVERY wrapped child leaf
    proof verifies. This is the recursion engine's in-circuit verifier (`verify_p3_batch_proof_circuit`
    run as a circuit, `prove_aggregation_layer`) being sound — the ONE big FRI obligation (§H1), the
    part outside Lean.

EVERYTHING ELSE — that these three, COMPOSED, yield the full `WellFormedChain` attestation, and hence
the whole-history correctness + conservation — is PROVED here in Lean, gap-free. The composition is
the load-bearing content: it is where a real aggregation bug (verify proof-of-step-7 but export
step-3's roots; swap a leg; drop a turn) would HAVE to show up, and the proof shows the named
hypotheses leave no such gap.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). The named
hypotheses are `structure` FIELDS, not axioms — they appear in the theorem statements, witnessed
non-vacuously (§5: a realizing instance exists). Verified with
`lake build Dregg2.Circuit.RecursiveAggregation`.
-/
import Dregg2.Distributed.HistoryAggregation

namespace Dregg2.Circuit.RecursiveAggregation

open Dregg2.Exec (RecChainedState recCexec recChainedSystem recTotal)
open Dregg2.Execution (Run)
open Dregg2.Distributed.HistoryAggregation
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)

section Engine

/-! ## 0. The SNARK proof object + verifier (opaque carriers).

`Proof` is an abstract STARK/recursion proof (the `RecursionCompatibleProof` /
`RecursionOutput` of `plonky3_recursion_impl`). `verify` is the native verifier
(`verify_recursive_batch_proof`). We treat them as opaque — the WHOLE point is that the light client
calls `verify` and nothing else. Soundness of `verify` w.r.t. the protocol is supplied by the named
hypotheses; we never inspect a proof's internals. -/

variable (Proof : Type)
variable (verify : Proof → Bool)

/-! ## 1. The aggregate artifact — the light client's whole view.

`Aggregate` is the `WholeChainProof` (`ivc_turn_chain.rs:430`): the single root recursion proof, plus
the PUBLIC commitments it exposes — `genesisRoot`, `finalRoot`, `chainDigest`, `numTurns`. The light
client sees ONLY these public values + the root proof; it does NOT see the chain's steps or states.
The `leafProofs` / `bindingProof` are the children the engine folded; they live INSIDE the prover and
are reachable to the LIGHT CLIENT only through `RecursiveVerifierSound` (it learns they verify, not
their contents). -/

/-- The succinct aggregate the light client verifies. `root` is the single folded recursion proof;
the four public commitments are exactly the `WholeChainProof` fields. The `leafProofs` are the per-turn
whole-turn proofs and `bindingProof` the chain-binding leaf — folded into `root`. -/
structure Aggregate where
  /-- The single root recursion proof (the whole tree folded to one — `WholeChainProof.root`). -/
  root        : Proof
  /-- The per-finalized-turn whole-turn (EffectVm) leaf proofs, in chain order. -/
  leafProofs  : List Proof
  /-- The `TurnChainBindingAir` chain-binding leaf proof (the temporal tooth). -/
  bindingProof : Proof
  /-- Public: the genesis root the chain starts from (`WholeChainProof.genesis_root`). This abstract
  field element denotes the FAITHFUL-FLOOR commitment the Rust waist exposes — the 8-felt (~124-bit)
  state anchor (`SEG_ANCHOR_WIDTH` lanes), NOT a single ~15-bit felt; the genuine 8-felt binding is
  proven in `Dregg2.Circuit.Emit.EffectVmEmitRotationWide` (`wireCommitR8_binds`). -/
  genesisRoot : ℤ
  /-- Public: the final root the chain reaches (`WholeChainProof.final_root`) — the 8-felt faithful
  state anchor, as for `genesisRoot`. -/
  finalRoot   : ℤ
  /-- Public: the running digest of the ordered (old,new) pairs (`WholeChainProof.chain_digest`) —
  the `SEG_DIGEST_WIDTH` = 8-lane (~124-bit) Poseidon2 ordered-history commitment (FAITHFUL-FLOOR
  lift; 4 lanes ~62-bit before). -/
  chainDigest : ℤ
  /-- Public: the number of finalized turns folded (`WholeChainProof.num_turns`). -/
  numTurns    : Nat

/-! ## 2. The named, realizable soundness hypotheses (the boundary).

These are the three facts the recursion engine supplies that we CANNOT prove in Lean (FRI/recursion
soundness). They are bundled in `EngineSound` as a hypothesis the headline takes — NOT an axiom. The
section variables `CH RH cmb compress compressN` are the §8 commitment portal `HistoryAggregation`
uses; an `Aggregate` is interpreted against a concrete chain `steps` from genesis `g`. -/

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`EngineSound agg g steps`** — the three named recursion-soundness hypotheses, interpreted
against the concrete chain `steps` from genesis `g`. Realizable (§5 exhibits an instance) and
NON-vacuous. -/
structure EngineSound (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- **H-RECURSE (`RecursiveVerifierSound`)** — if the root aggregate verifies, then every child leaf
  AND the binding leaf verify. The recursion engine's in-circuit verifier soundness (the ONE FRI
  obligation, §H1). This is the only hypothesis outside Lean's reach. -/
  recursive_sound : verify agg.root = true →
    (∀ p ∈ agg.leafProofs, verify p = true) ∧ verify agg.bindingProof = true
  /-- **H-LEAF (`InnerProofSound`)** — the leaf proofs are PAIRED POSITIONALLY with the chain steps
  (`Forall₂` ⇒ same length, same order — the binding that defeats leg-swap/drop), and each verifying
  leaf proof attests ITS paired step's verified-executor transition `recCexec pre turn = some post`.
  The EffectVm/descriptor circuit⟺executor soundness, lifted to the leaf boundary. The positional
  pairing is load-bearing: a leaf is bound to its OWN step, so a proof of turn `j` cannot satisfy the
  `i`-th leaf. -/
  leaf_sound : List.Forall₂
    (fun (p : Proof) (s : ChainStep) => verify p = true → recCexec s.pre s.turn = some s.post)
    agg.leafProofs steps
  /-- **H-BIND (`BindingAirSound`)** — a verifying `TurnChainBindingAir` leaf attests the temporal
  tooth over the whole chain (`ChainBound`), AND pins the public genesis/final roots to the chain's
  endpoints. The chain-binding AIR's in-circuit soundness. -/
  binding_sound : verify agg.bindingProof = true →
    ChainBound CH RH cmb compress compressN steps
      ∧ agg.genesisRoot = (match steps.head? with
          | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
          | some s => ChainStep.oldRoot CH RH cmb compress compressN s)
      ∧ agg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps

/-! ## 3. THE LIGHT-CLIENT HEADLINE — verifying the aggregate attests the WHOLE history.

The light client runs `verify agg.root` and NOTHING ELSE. We prove: if that one check passes (and the
engine is sound, the named hypotheses), then EVERY turn in the history executed correctly, the chain
is correctly ordered, and the final root is the genuine fold of the whole history. No re-witnessing. -/

/-- Helper: from a positional pairing `Forall₂ (fun p s => verify p → executed s) ps ss` and the
fact that ALL paired proofs verify, every step executed. Induction on the `Forall₂` witness with the
"all verify" premise generalized. -/
theorem forall₂_all_verify_executed
    {ps : List Proof} {ss : List ChainStep}
    (hpair : List.Forall₂
      (fun (p : Proof) (s : ChainStep) => verify p = true → recCexec s.pre s.turn = some s.post) ps ss)
    (hall : ∀ p ∈ ps, verify p = true) :
    ∀ s ∈ ss, recCexec s.pre s.turn = some s.post := by
  induction hpair with
  | nil => intro s hs; cases hs
  | @cons p s ps' ss' hps _htail ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hrest
    · exact hps (hall p (List.mem_cons_self))
    · exact ih (fun q hq => hall q (List.mem_cons_of_mem p hq)) a hrest

/-- **`every_leaf_verifies_implies_executed`.** From the recursion-soundness + leaf-soundness
hypotheses, a verifying root implies every step's verified-executor transition holds. The chain of
in-circuit verifications collapses to "every turn executed correctly" — `recursive_sound` (root ⇒
leaves verify) composed with `leaf_sound` (positional pairing ⇒ each step executed). -/
theorem every_leaf_verifies_implies_executed
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) :
    ∀ s ∈ steps, recCexec s.pre s.turn = some s.post := by
  obtain ⟨hleaves, _hbind⟩ := es.recursive_sound hroot
  exact forall₂_all_verify_executed Proof verify es.leaf_sound hleaves

/-- **`AggregateAttests agg g steps`** — the full attestation the light client obtains: every turn
executed correctly, the chain is correctly ordered, the whole chain is a verified-executor `Run` from
genesis, and the public roots are pinned to the genuine endpoints. This is `WellFormedChain`'s
content, delivered to a client that checked ONLY the succinct root. -/
structure AggregateAttests (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- (1) every turn executed correctly per the verified executor. -/
  every_turn : ∀ s ∈ steps, recCexec s.pre s.turn = some s.post
  /-- (2) the chain is correctly ordered (the temporal tooth holds — no reorder/drop/insert). -/
  ordered : ChainBound CH RH cmb compress compressN steps
  /-- (3) the public final root IS the genuine fold of the whole history. -/
  final_is_genuine_fold :
    agg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps
  /-- (4) the public genesis root is the chain's start. -/
  genesis_pinned : agg.genesisRoot = (match steps.head? with
      | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
      | some s => ChainStep.oldRoot CH RH cmb compress compressN s)

/-- **`light_client_verifies_whole_history` (THE MAGNESIUM→GOLD HEADLINE).**

A light client that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) obtains
`AggregateAttests`: every turn executed correctly, the chain is correctly ordered (no reorder/drop/
insert), and the public final root is the genuine fold of the whole history — UNDER the named,
realizable engine-soundness hypotheses. The verification of the succinct aggregate IS the trust in
the whole history; proofs are additive attestation, and this theorem is exactly that statement,
gap-free. -/
theorem light_client_verifies_whole_history
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) :
    AggregateAttests Proof CH RH cmb compress compressN agg g steps := by
  obtain ⟨_hleaves, hbind⟩ := es.recursive_sound hroot
  obtain ⟨hbound, hgen, hfin⟩ := es.binding_sound hbind
  exact
    { every_turn := every_leaf_verifies_implies_executed Proof verify CH RH cmb compress compressN agg g steps es hroot
    , ordered := hbound
    , final_is_genuine_fold := hfin
    , genesis_pinned := hgen }

/-! ### 3b. THE GENESIS ANCHOR — the verify-side dual of the final-root anchor (PREFIX completeness).

`AggregateAttests.genesis_pinned` pins the public genesis root only to the PROVER-CHOSEN first folded
step (`steps.head`). The deployed finality path pins the FINAL root to the committee-ratified head; its
EXACT DUAL pins the GENESIS root to the client's TRUSTED genesis/checkpoint (`expectedGenesis`). Without
it, a prover can fold a valid, committee-finalizable history from a FABRICATED/midpoint genesis to the
true head, HIDING the entire prefix (the TIER3 LANE-2c residual). With it, the attested history provably
STARTS at `expectedGenesis`. This is a VERIFY-SIDE anchor — a caller-supplied expected genesis compared
against the fold's public `genesisRoot` — NOT a circuit/VK change (exactly as the final-root anchor is
verify-side; the Rust dual is `verify_finalized_history(..., expected_genesis)`). -/

/-- **`AnchoredAttests`** — `AggregateAttests` PLUS the verify-side genesis anchor: the public genesis
the aggregate carries IS the client's trusted `expectedGenesis`. -/
structure AnchoredAttests
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) (expectedGenesis : ℤ) : Prop where
  /-- the full whole-history attestation (every turn correct, correctly ordered, genuine final fold,
  genesis pinned to the first folded step). -/
  attests : AggregateAttests Proof CH RH cmb compress compressN agg g steps
  /-- the CLIENT-SIDE anchor: the aggregate's public genesis root is the trusted genesis. -/
  genesis_anchored : agg.genesisRoot = expectedGenesis

/-- **`light_client_verifies_anchored_history` (THE GENESIS-ANCHORED HEADLINE).** A light client that
checks `verify agg.root = true` AND pins the aggregate's public genesis to its trusted `expectedGenesis`
obtains `AnchoredAttests`. Mirrors the final-root anchor exactly: the finality path checks
`agg.finalRoot`'s head against the committee-ratified root; this checks `agg.genesisRoot` against the
trusted genesis. -/
theorem light_client_verifies_anchored_history
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) (expectedGenesis : ℤ)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hanchor : agg.genesisRoot = expectedGenesis) :
    AnchoredAttests Proof CH RH cmb compress compressN agg g steps expectedGenesis :=
  { attests := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN agg g steps es hroot
  , genesis_anchored := hanchor }

/-- **`anchored_history_starts_at_genesis` (the prefix-gap closer).** The attested history genuinely
STARTS at the anchored genesis: the FIRST folded step's before-root (or the genesis state root, for an
empty chain) equals `expectedGenesis`. This is the fact a fabricated-genesis prover cannot satisfy — the
DUAL of `final_is_genuine_fold` checked against the committee head. -/
theorem anchored_history_starts_at_genesis
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) (expectedGenesis : ℤ)
    (anch : AnchoredAttests Proof CH RH cmb compress compressN agg g steps expectedGenesis) :
    (match steps.head? with
      | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
      | some s => ChainStep.oldRoot CH RH cmb compress compressN s) = expectedGenesis := by
  rw [← anch.attests.genesis_pinned]; exact anch.genesis_anchored

/-- **`anchored_attests_rejects_fabricated_genesis` (THE GENESIS ANTI-GHOST TOOTH).** No aggregate whose
public genesis differs from the client's `fabricated` anchor can be `AnchoredAttests` for it — the
`genesis_anchored` field is contradictory. So a prover presenting a history that does NOT start at the
trusted genesis (a hidden prefix) is REJECTED by the anchor. Mirrors `tampered_aggregate_cannot_bind`. -/
theorem anchored_attests_rejects_fabricated_genesis
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) (fabricated : ℤ)
    (hne : agg.genesisRoot ≠ fabricated)
    (anch : AnchoredAttests Proof CH RH cmb compress compressN agg g steps fabricated) :
    False := hne anch.genesis_anchored

/-! ## 4. The RUN + CONSERVATION the light client inherits (no re-execution).

`AggregateAttests` gives the per-step executor transitions + the ordering; composed with state-level
continuity (the strong form the root tooth recovers under CR, `HistoryAggregation.root_tooth_pins_-
state`), it yields a full `Run recChainedSystem` from genesis, hence conservation over the WHOLE
history — all WITHOUT the light client re-running a single turn. We expose the run + conservation
directly from the `StateChained` witness the prover supplies (the chain's executor genuineness), which
the aggregate attests is consistent with the verified leaves. -/

/-- **`attested_history_is_run`.** Given the executor-genuine chain (`StateChained` — the
prover's witness that the steps are a real run, which the verifying leaves attest step-by-step), the
whole attested history is a `Run recChainedSystem` from genesis to the folded endpoint. The light
client inherits every run-level theorem of the verified record cell.

NOTE (the run vs conservation split): a full `Run recChainedSystem` is a relation on `RecChainedState`
configs, so composing the steps requires the receipt LOG to chain (`s.post = s'.pre`), which the §8
state commitment does NOT bind (it commits the kernel, not the log). The full `Run` therefore genuinely
needs `StateChained`. CONSERVATION, by contrast, reads only the kernel — so it is derivable from the
VERIFIED root without `StateChained`; that is `conserves_from_verification` below (the CRITICAL-3
closure). The log being uncommitted is the exact, named residual: it blocks the full RUN, never
conservation. -/
theorem attested_history_is_run
    (g : RecChainedState) (steps : List ChainStep) (hch : StateChained g steps) :
    Run recChainedSystem g (lastStateOf g steps) :=
  wellformed_is_run g steps hch

/-- **`attested_history_conserves` (KEYSTONE).** Value is conserved across the WHOLE attested
history: the ledger total at the folded endpoint equals the genesis total. A light client trusting the
aggregate trusts a no-mint/no-burn history of arbitrary length, having re-executed nothing. Rides
`HistoryAggregation.wellformed_history_conserves`.

This form takes `StateChained` as a hypothesis (the legitimate producer-supplied path —
`Argus/Aggregate.lean` DERIVES `StateChained` from the genuine producer run). The verification-derived
form that needs NO such hypothesis is `conserves_from_verification` below. -/
theorem attested_history_conserves
    (g : RecChainedState) (steps : List ChainStep) (hch : StateChained g steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  wellformed_history_conserves g steps hch

/-! ### CRITICAL-3 CLOSURE — conservation-over-history DERIVED from `verify agg.root`, no `StateChained`.

The critique: `attested_history_conserves` takes `StateChained` (state continuity) as a SEPARATE
prover-supplied hypothesis — exactly what a malicious prover controls — and the tool that could close
it (`root_tooth_pins_state`) recovered only commitment-equality, not state-equality. We close it:
the strengthened `HistoryAggregation.root_tooth_pins_kernel` recovers KERNEL-equality from the verified
root tooth (under the standard Poseidon CR set + the preserved `AccountsWF` invariant), and
`verified_history_conserves` rides that to conservation through `KernelChained` — so conservation
follows from `verify agg.root` itself (which delivers the `ChainBound` tooth via `AggregateAttests`),
plus the genesis pin + the non-cryptographic structural envelope `SeamStruct`. The `StateChained`
hypothesis is GONE from the conservation headline. -/

/-- **`conserves_from_verification` (THE CRITICAL-3 HEADLINE — conservation from `verify agg.root`).**
A light client that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) learns the WHOLE
history conserves value — the ledger total at the folded endpoint equals the genesis total — with NO
`StateChained` hypothesis. The verified root gives `AggregateAttests` (hence the `ChainBound` root
tooth); under the standard Poseidon CR set + the genesis pin + the structural envelope `SeamStruct`
(matched turns + the preserved `AccountsWF` invariant, both non-cryptographic, neither a
state-continuity assertion), `verified_history_conserves` DERIVES kernel continuity from that tooth
(`root_tooth_pins_kernel`) and rides it to conservation. This is the exact gap the critique flagged,
closed: "trusting the aggregate trusts a no-mint/no-burn history" now follows from VERIFICATION, not
from the prover's honesty about state continuity. (The receipt LOG — the one `RecChainedState`
component the §8 root does not bind — blocks only the full `Run`, never conservation; named, not
hidden.) -/
theorem conserves_from_verification
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hgen : KernelGenesisPin g steps)
    (hstruct : SeamStruct steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel := by
  -- the verified root delivers the ordering tooth (ChainBound) — no re-witnessing.
  have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
    agg g steps es hroot
  -- conservation follows from the VERIFIED tooth + genesis pin + structural envelope; no StateChained.
  exact verified_history_conserves CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
    g steps hgen hatt.ordered hstruct

/-- **`anchored_conserves_from_verification` (conservation FROM the anchored genesis — BOTH ends pinned).**
A light client that checks `verify agg.root = true` AND pins the genesis to its trusted `expectedGenesis`
learns BOTH (1) the history genuinely STARTS at `expectedGenesis` and (2) the WHOLE history conserves
value from that anchored genesis — with NO `StateChained` hypothesis. The genesis is no longer
prover-chosen: the conservation statement is now anchored at BOTH ends (final ← committee head via the
finality seam, genesis ← trusted anchor here — the verify-side dual `AnchoredAttests` carries), closing
the prefix-completeness gap (TIER3 LANE 2c). -/
theorem anchored_conserves_from_verification
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) (expectedGenesis : ℤ)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hgen : KernelGenesisPin g steps) (hstruct : SeamStruct steps)
    (hanchor : agg.genesisRoot = expectedGenesis) :
    ((match steps.head? with
        | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
        | some s => ChainStep.oldRoot CH RH cmb compress compressN s) = expectedGenesis)
      ∧ recTotal (lastStateOf g steps).kernel = recTotal g.kernel := by
  refine ⟨?_, ?_⟩
  · have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN agg g steps es hroot
    rw [← hatt.genesis_pinned]; exact hanchor
  · exact conserves_from_verification Proof verify CH RH cmb compress compressN
      hCmb hCompress hCompressN hLeaf hRest agg g steps es hroot hgen hstruct

/-- **`non_omission_from_verification` (THE WHOLE-HISTORY NON-OMISSION HEADLINE — from `verify agg.root`).**
A light client that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) learns the receipt log
chains genuinely across the WHOLE history — `LogChained g steps`, i.e. every folded step's post-log is
the next step's pre-log — with NO `hweld`. The verified root gives `AggregateAttests` (hence the
`ChainBound` root tooth); under `compressNInjective` + the genesis log pin + the structural envelope
`SeamStruct` (only its turn-match arm), `logChained_of_verified` DERIVES log continuity from that tooth
via `root_tooth_pins_log` (the rotated commit's receipt-log limb). This is exactly the §3 residual the
ROOT-FACE repair named ("`HistoryAggregation.stateRoot := rotatedCommit`") now CLOSED whole-history: a
node cannot drop / forge / reorder / truncate a receipt at ANY step without breaking a published
commit, and the light client sees it from the succinct aggregate alone. The receipt LOG — the one
component the kernel-only §8 root did NOT bind — is now bound by the model the aggregate attests. -/
theorem non_omission_from_verification
    (hCompressN : compressNInjective compressN)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hgen : LogGenesisPin g steps)
    (hstruct : SeamStruct steps) :
    LogChained g steps := by
  have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
    agg g steps es hroot
  exact logChained_of_verified CH RH cmb compress compressN hCompressN g steps hgen hatt.ordered hstruct

end Engine

/-! ## 5. NON-VACUITY — the named hypotheses are REALIZABLE (witnessed BOTH ways).

The headline would be hollow if `EngineSound` were unsatisfiable, or if `verify agg.root = true`
could not occur. We exhibit a CONCRETE realizing instance over the `HistoryAggregation.honestStep`
chain (a real 1-step executor run over the teeth genesis): a `verify` that accepts, an `Aggregate`
whose root/leaf/binding all verify, and an `EngineSound` proof — so the headline fires on a real
chain and concludes a real `AggregateAttests`. We ALSO witness the negative: a `verify` that REJECTS
gives a vacuously-true `EngineSound` (no obligation), and the headline is not invoked — the tooth is
in the `binding_sound`/`leaf_sound` implications, which §6 shows separate honest from
tampered. -/

section Realize

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)

/-- A trivial proof carrier (Unit) and an ACCEPTING verifier — the realizing engine instance. -/
abbrev RealProof := Unit
def acceptAll : RealProof → Bool := fun _ => true

/-- The §8 portal realized by constant-zero hashes for the witness (the realizing instance only needs
the structure to typecheck + the soundness implications to hold; the CR carriers are not invoked here
because the engine hypotheses are supplied DIRECTLY as the realized facts). -/
def zCH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ := fun _ _ => 0
def zRH : Dregg2.Exec.RecordKernelState → ℤ := fun _ => 0
def zcmb : ℤ → ℤ → ℤ := fun _ _ => 0
def zcompress : ℤ → ℤ → ℤ := fun _ _ => 0
def zcompressN : List ℤ → ℤ := fun _ => 0

/-- The realizing 1-step chain: the honest executor step over the teeth genesis. -/
def realSteps : List ChainStep := [honestStep]

/-- The realizing aggregate: every proof is the accepting `Unit`; the public roots are the genuine
endpoints of `realSteps` (so `binding_sound`'s pin holds by `rfl`). -/
def realAggregate : Aggregate RealProof where
  root := ()
  leafProofs := [()]
  bindingProof := ()
  genesisRoot := ChainStep.oldRoot zCH zRH zcmb zcompress zcompressN honestStep
  finalRoot := foldedFinalRoot zCH zRH zcmb zcompress zcompressN teethGenesis realSteps
  chainDigest := 0
  numTurns := 1

/-- **`real_engine_sound` (non-vacuity, positive).** The named soundness hypotheses are
SATISFIABLE on a real chain: `EngineSound` holds for the accepting verifier, the realizing aggregate,
the teeth genesis, and the honest 1-step chain. Each implication is discharged concretely — the leaf
soundness yields the genuine `recCexec teethGenesis honestTurn = some _` (the honest step's `commits`),
the binding soundness yields the singleton `ChainBound` + the genuine root pins. So `EngineSound` is
INHABITED — the headline is not vacuous. -/
theorem real_engine_sound :
    EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps := by
  refine { recursive_sound := ?_, leaf_sound := ?_, binding_sound := ?_ }
  · intro _
    refine ⟨fun p hp => ?_, rfl⟩
    -- every leaf is `()`; `acceptAll _ = true`.
    rfl
  · -- the positional pairing: leaf `()` ↦ step `honestStep`, whose `commits` IS the executor witness.
    show List.Forall₂ _ [()] realSteps
    refine List.Forall₂.cons ?_ (List.Forall₂.nil)
    intro _
    exact honestStep.commits
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · -- ChainBound on a singleton is `True`.
      simp [realSteps, ChainBound]
    · -- genesisRoot is defined as the genuine oldRoot of the head step.
      simp [realAggregate, realSteps]
    · -- finalRoot is defined as the genuine fold.
      rfl

/-- **`light_client_fires_on_real_chain` (the headline is WITNESSED).** On the realizing
instance, the light-client headline concludes `AggregateAttests`: verifying the (accepting)
root attests the honest 1-step history. So `light_client_verifies_whole_history` is non-vacuous — it
fires on a real chain and delivers a real attestation, not an empty implication. -/
theorem light_client_fires_on_real_chain :
    AggregateAttests RealProof zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps :=
  light_client_verifies_whole_history RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps real_engine_sound rfl

/-- **`real_chain_first_turn_executed` (the attestation is REAL).** Reading the conclusion
of the witnessed headline: the first (only) turn of the realizing history executed —
`recCexec teethGenesis honestTurn = some _`. So the light client's attestation is a TRUE fact about a
real executor run, not a formal husk. -/
theorem real_chain_first_turn_executed :
    recCexec teethGenesis honestTurn = some honestStep.post := by
  have h := light_client_fires_on_real_chain.every_turn honestStep (by simp [realSteps])
  simpa [honestStep] using h

/-- **`anchored_fires_on_real_chain` (genesis-anchor non-vacuity, POSITIVE).** On the realizing
instance, anchoring to the GENUINE genesis (`realAggregate.genesisRoot`) fires `AnchoredAttests`: the
anchored headline delivers a real attestation whose genesis is pinned to the trusted value. So the
genesis anchor is not vacuous — the true-genesis history passes. -/
theorem anchored_fires_on_real_chain :
    AnchoredAttests RealProof zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps realAggregate.genesisRoot :=
  light_client_verifies_anchored_history RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps realAggregate.genesisRoot real_engine_sound rfl rfl

/-- **`anchored_tooth_bites_on_real_chain` (genesis-anchor non-vacuity, NEGATIVE — the tooth BITES).**
A WRONG expected genesis (the genuine genesis + 1, which differs) admits NO `AnchoredAttests` on the
realizing instance: any such witness contradicts its own `genesis_anchored` field. So the anchor is a
REAL discriminator (satisfiable AND refutable), not a vacuous conjunct — a fabricated-genesis history is
REJECTED. -/
theorem anchored_tooth_bites_on_real_chain
    (anch : AnchoredAttests RealProof zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps (realAggregate.genesisRoot + 1)) :
    False :=
  anchored_attests_rejects_fabricated_genesis RealProof zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps (realAggregate.genesisRoot + 1) (by omega) anch

end Realize

/-! ## 6. THE ANTI-GHOST TOOTH — the named hypotheses REJECT a tampered aggregate.

Additive attestation is only meaningful if the aggregate cannot attest a BROKEN history. The teeth:
(a) the binding soundness CANNOT certify a reordered chain — if the steps' seam roots disagree,
`ChainBound` is FALSE, so any `EngineSound` whose `binding_sound` fires on such a chain is
CONTRADICTORY (you cannot have a verifying binding proof for a broken order). (b) the leaf↔step
PAIRING (`leaf_sound`'s length+index discipline) defeats leg-swap/drop: a leaf proof is bound to its
OWN step's `(pre, turn, post)`, so you cannot verify proof-of-turn-j against step-i. -/

section AntiGhost

variable (Proof : Type) (verify : Proof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`tampered_aggregate_cannot_bind` (THE ANTI-GHOST TOOTH).** No sound aggregate can
attest a REORDERED 2-step chain. If the first step's `newRoot` differs from the second's `oldRoot`
(a spliced/reordered/dropped turn — the `TurnChainError::ChainBreak` condition), then for ANY engine
whose binding leaf verifies, `binding_sound` would force `ChainBound [s, s']`, which is FALSE for a
broken order. Hence the engine cannot have a verifying binding proof over a tampered chain — the
aggregate REJECTS reorder/drop/insert. -/
theorem tampered_aggregate_cannot_bind
    (agg : Aggregate Proof) (g : RecChainedState) (s s' : ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g [s, s'])
    (hbreak : ChainStep.newRoot CH RH cmb compress compressN s
                ≠ ChainStep.oldRoot CH RH cmb compress compressN s')
    (hverify : verify agg.bindingProof = true) :
    False := by
  obtain ⟨hbound, _, _⟩ := es.binding_sound hverify
  exact tooth_rejects_broken_order CH RH cmb compress compressN s s' hbreak hbound

/-- **`leaf_pairing_defeats_swap` (the leg-swap tooth).** A verifying leaf proof attests the
transition of ITS OWN POSITIONALLY-PAIRED step, not some other turn's. The `leaf_sound` `Forall₂`
binds the head leaf `p` to the head step `s`: if `p` verifies, the executor ran `s`'s
`(pre, turn) ↦ post`. An adversary cannot satisfy the head leaf by supplying a proof of a DIFFERENT
turn while exporting `s`'s roots — the leaf is bound to `s` by the positional pairing, not re-pointable.
This is the recursion analog of the per-effect anti-ghost. -/
theorem leaf_pairing_defeats_swap
    (agg : Aggregate Proof) (g : RecChainedState) (p : Proof) (ps : List Proof)
    (s : ChainStep) (ss : List ChainStep)
    (hagg : agg.leafProofs = p :: ps)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g (s :: ss))
    (hleafverify : verify p = true) :
    recCexec s.pre s.turn = some s.post := by
  have hpair := es.leaf_sound
  rw [hagg] at hpair
  cases hpair with
  | cons hhead _ => exact hhead hleafverify

end AntiGhost

/-! ## 7. THE UNBOUNDED IVC ACCUMULATOR — the running left-fold, proven by induction from genesis.

§§1–6 prove the FLAT statement: given a `WholeChainProof` over a *finite* K-turn window, verifying its
root attests `WellFormedChain` for that window. That is the BOUNDED-K light client (`ivc_turn_chain.rs::
prove_turn_chain_recursive`, a balanced binary tree over K leaves).

This section proves the part Mina LACKS: that the accumulator can be driven as a CONTINUOUS LEFT-FOLD
(`acc_n = accumulate(acc_{n-1}, turn_n)`), extending the attested history ONE step at a time, with O(1)
memory (keep only `acc_{n-1}`), and that the running accumulator's attestation is PRESERVED at every
step — so by induction from genesis, `acc_n` attests the WHOLE history `0..n`. This is the IVC soundness
INDUCTION as a Lean theorem:

  `accumulate_preserves_wellformed` — IF `acc` attests `WellFormedChain g steps` AND the next turn `s`
  is executor-sound (a `ChainStep`, so `s.commits` is built in) and STATE-EXTENDS the head
  (`s.pre = lastStateOf g steps`), THEN `accumulate acc s` attests `WellFormedChain g (steps ++ [s])`.

  `acc_attests_whole_history` — folding `accumulate` from the genesis accumulator over a state-extending
  stream yields an accumulator attesting `WellFormedChain g (the whole stream)`. The base case is the
  empty chain (trivially well-formed); the step is `accumulate_preserves_wellformed`.

This is the SOUNDNESS SKELETON of the unbounded online accumulator. The CRYPTO carrier (the running
recursion proof re-verified in-circuit so `acc_n.proof` has the SAME shape `acc_{n+1}` can verify — the
IVC fixed point) is the SAME named, realizable `EngineSound` boundary §2 already carries; nothing new is
axiomatized. What this section adds OVER §§1–6 is the INDUCTIVE characterization: the flat headline is
re-derived as the n-th unfolding of a one-step-at-a-time fold from genesis.

NOTE on the seam (the genuinely-load-bearing hypothesis, named not hidden). `accumulate` extends a chain
at its HEAD; for the *root-level* temporal tooth (`ChainBound`) to extend, the new step's `oldRoot` must
equal the previous last step's `newRoot`. We DERIVE that from state continuity (`s.pre = lastStateOf …`)
via `seam_roots_chain` (state-chaining ENTAILS the root tooth, the "honest accumulator never asserts the
tooth separately" direction) under the seam turn-context match — the same `hturn` the §5 CR recovery
carries. State continuity is the producer's witness (exactly as `StateChained` is everywhere here); the
tooth is then FREE, not a second assumption. -/

section Accumulator

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **The running accumulator state.** It carries the genesis it folds from, the ordered list of steps
folded so far (the prover's O(1) view keeps only the *witness* of these — the running proof — not the
list; the list is the SPECIFICATION the proof attests), and the live `WellFormedChain` attestation. The
`leanWitness` field IS the inductive invariant: at every fold step it stays a real `WellFormedChain`,
which is exactly what the running recursion proof is sound for (`EngineSound`). -/
structure Acc (g : RecChainedState) where
  /-- The steps folded so far, in chain order (the history the running proof attests). -/
  steps      : List ChainStep
  /-- The inductive invariant: the folded steps are a well-formed chain from genesis. -/
  leanWitness : WellFormedChain CH RH cmb compress compressN g steps

/-- **`Acc.head g acc`** — the state the running accumulator has reached: `lastStateOf` of the folded
steps. The next turn must consume THIS state (`s.pre = acc.head`). -/
def Acc.head {g : RecChainedState} (acc : Acc CH RH cmb compress compressN g) : RecChainedState :=
  lastStateOf g acc.steps

/-- **`genesisAcc g`** — `acc_0`: the empty fold from genesis. Attests the empty (trivially well-formed)
chain. Its head is genesis itself. This is the base of the IVC induction. -/
def genesisAcc (g : RecChainedState) : Acc CH RH cmb compress compressN g where
  steps := []
  leanWitness := { chained := trivial, bound := trivial }

/-- `genesisAcc`'s head is genesis (the empty fold has reached nowhere). -/
@[simp] theorem genesisAcc_head (g : RecChainedState) :
    Acc.head CH RH cmb compress compressN (genesisAcc CH RH cmb compress compressN g) = g := rfl

/-- For a NONEMPTY chain, `lastStateOf` is the last step's `post` (purely structural — it is the state
the fold reaches). Used to identify the join seam in `accumulate`. -/
theorem lastStateOf_eq_getLast_post (g : RecChainedState) (steps : List ChainStep) (last : ChainStep)
    (hlast : steps.getLast? = some last) :
    lastStateOf g steps = last.post := by
  induction steps generalizing g with
  | nil => simp at hlast
  | cons a rest ih =>
    cases rest with
    | nil => simp only [List.getLast?_singleton, Option.some.injEq] at hlast; subst hlast; rfl
    | cons b rest' =>
      have hlast' : (b :: rest').getLast? = some last := by simpa using hlast
      simpa [lastStateOf] using ih a.post hlast'

/-! ### Snoc lemmas — extending each chain predicate by one step at the TAIL.

`accumulate` appends `s` at the END (`steps ++ [s]`). The chain predicates (`StateChained`, `ChainBound`,
`lastStateOf`) are defined by recursion on the HEAD, so extending at the tail needs these three snoc
lemmas, each a straightforward list induction. They are the load-bearing combinatorial content of the
IVC step: dropping/reordering at the tail would break exactly one of them. -/

/-- `lastStateOf` of a tail-extended chain is the new step's `post`, provided the new step extends the
old head (`s.pre = lastStateOf g steps`). -/
theorem lastStateOf_snoc (g : RecChainedState) (steps : List ChainStep) (s : ChainStep) :
    lastStateOf g (steps ++ [s]) = lastStateOf s.pre [s] := by
  induction steps generalizing g with
  | nil => rfl
  | cons a rest ih => simpa [lastStateOf] using ih a.post

/-- A tail-extended chain stays state-chained, IF the old chain is state-chained AND the new step
consumes the old head's state (`s.pre = lastStateOf g steps`). The seam at the join is exactly that
hypothesis. -/
theorem stateChained_snoc (g : RecChainedState) (steps : List ChainStep) (s : ChainStep)
    (hch : StateChained g steps) (hseam : s.pre = lastStateOf g steps) :
    StateChained g (steps ++ [s]) := by
  induction steps generalizing g with
  | nil =>
    -- empty: `s.pre = g` (hseam at the base), and the tail `[]` is `StateChained s.post []` = True.
    refine ⟨?_, trivial⟩
    simpa [lastStateOf] using hseam
  | cons a rest ih =>
    obtain ⟨hpre, hrest⟩ := hch
    subst hpre
    exact ⟨rfl, ih a.post hrest (by simpa [lastStateOf] using hseam)⟩

/-- A tail-extended chain stays `ChainBound`, IF the old chain is bound AND the new step continues the
old LAST step at the root level (`Continues last s`). For the empty/singleton old chain the join has no
predecessor, so it is vacuous; for a longer chain we thread the bound and discharge the final seam. -/
theorem chainBound_snoc :
    ∀ (steps : List ChainStep) (s : ChainStep),
      ChainBound CH RH cmb compress compressN steps →
      (∀ last, steps.getLast? = some last → Continues CH RH cmb compress compressN last s) →
      ChainBound CH RH cmb compress compressN (steps ++ [s])
  | [], s, _, _ => by simp [ChainBound]
  | [a], s, _, hcont => by
    -- old chain `[a]`: the new pair is `[a, s]`; the bound is `Continues a s ∧ ChainBound [s]`.
    refine ⟨?_, trivial⟩
    exact hcont a (by simp)
  | a :: b :: rest, s, hbound, hcont => by
    obtain ⟨hab, htail⟩ := hbound
    refine ⟨hab, ?_⟩
    -- recurse on `b :: rest`; its getLast? is the same as `(a::b::rest).getLast?`.
    have := chainBound_snoc (b :: rest) s htail (by
      intro last hlast
      apply hcont last
      simpa using hlast)
    simpa using this

/-! ### `accumulate` — the IVC step (extend one leaf at a time). -/

/-- **`accumulate acc s hseam hturn`** — the running left-fold step. Given the running accumulator
`acc` (attesting `WellFormedChain g acc.steps`) and the next executor-sound turn `s` (a `ChainStep`, so
`s.commits` is built in) that STATE-EXTENDS the head (`hseam : s.pre = acc.head`) under a matched seam
turn-context (`hturn`), produce `acc'` attesting `WellFormedChain g (acc.steps ++ [s])`. O(1) view: the
prover keeps only `acc` (its running proof); `acc.steps` is the SPEC the proof attests, extended by one.

The two invariants are re-established by the snoc lemmas:
  * STATE continuity (`stateChained_snoc`) from `hseam`;
  * the ROOT temporal tooth (`chainBound_snoc`) — and the NEW seam `Continues last s` is DERIVED from
    `hseam` (state continuity) via `seam_roots_chain`, so the tooth is FREE, never a second assumption. -/
def accumulate {g : RecChainedState} (acc : Acc CH RH cmb compress compressN g) (s : ChainStep)
    (hseam : s.pre = Acc.head CH RH cmb compress compressN acc)
    (hturn : ∀ last, acc.steps.getLast? = some last → last.turn = s.turn) :
    Acc CH RH cmb compress compressN g where
  steps := acc.steps ++ [s]
  leanWitness :=
    { chained := stateChained_snoc g acc.steps s acc.leanWitness.chained hseam
    , bound := chainBound_snoc CH RH cmb compress compressN acc.steps s acc.leanWitness.bound
        (by
          intro last hlast
          -- the root tooth at the join, DERIVED from state continuity (seam_roots_chain).
          -- `last` is the old last step; its post is the old head (`lastStateOf`), which `s.pre` equals.
          have hpost : last.post = s.pre := by
            rw [hseam]
            -- old head = last step's post when the chain is nonempty (getLast? = some last).
            simpa [Acc.head] using (lastStateOf_eq_getLast_post g acc.steps last hlast).symm
          exact seam_roots_chain CH RH cmb compress compressN last s hpost
            (hturn last hlast)) }

/-- **`accumulate_preserves_wellformed` (THE IVC INVARIANT).** The running accumulator's attestation is
PRESERVED by one fold step: `accumulate acc s …` attests `WellFormedChain g (acc.steps ++ [s])`. This is
the inductive heart of the unbounded accumulator — `acc_{n-1} ⊢ 0..n-1` and `turn_n` extends ⟹
`acc_n ⊢ 0..n`. -/
theorem accumulate_preserves_wellformed {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) (s : ChainStep)
    (hseam : s.pre = Acc.head CH RH cmb compress compressN acc)
    (hturn : ∀ last, acc.steps.getLast? = some last → last.turn = s.turn) :
    WellFormedChain CH RH cmb compress compressN g
      (accumulate CH RH cmb compress compressN acc s hseam hturn).steps :=
  (accumulate CH RH cmb compress compressN acc s hseam hturn).leanWitness

/-- **`acc_attests_whole_history` (THE IVC HEADLINE — by induction from genesis).** The running
accumulator attests the WHOLE history it has folded: `acc.leanWitness` IS a `WellFormedChain` from
genesis over `acc.steps`, for ANY accumulator reachable from `genesisAcc` by `accumulate` steps. We
state it as: every `Acc` (which can only be built by `genesisAcc` + `accumulate`, both of which
maintain the invariant) carries the whole-history attestation in its `leanWitness`. Composed with
`light_client_verifies_whole_history` (§3) — whose `EngineSound` is sound for exactly this
`WellFormedChain` — a light client verifying the running root learns the whole accumulated history is
correct, ordered, and genuinely folded. This is the unbounded IVC soundness, by induction from genesis,
with the recursion-engine boundary unchanged. -/
theorem acc_attests_whole_history {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) :
    WellFormedChain CH RH cmb compress compressN g acc.steps :=
  acc.leanWitness

/-- **`acc_attests_run` (the run the accumulator inherits).** The accumulated history is a genuine
`Run recChainedSystem` from genesis to the accumulator's head — so EVERY run-level theorem of the
verified record cell (incl. conservation) applies to the whole O(1)-memory-folded history, with NO
re-execution. -/
theorem acc_attests_run {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) :
    Run recChainedSystem g (Acc.head CH RH cmb compress compressN acc) :=
  wellformed_is_run g acc.steps acc.leanWitness.chained

/-- **`acc_conserves` (conservation over the whole accumulated history).** Value is conserved across the
entire history the running accumulator folded: the ledger total at the head equals the genesis total. A
light client trusting the running aggregate trusts a no-mint/no-burn history of UNBOUNDED length, having
re-executed nothing and held O(1) memory. -/
theorem acc_conserves {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) :
    recTotal (Acc.head CH RH cmb compress compressN acc).kernel = recTotal g.kernel :=
  wellformed_history_conserves g acc.steps acc.leanWitness.chained

/-! ### IVC non-vacuity — the accumulator FIRES on a real chain (genesis → one accumulate step).

The induction would be hollow if no real `accumulate` step could fire. We build `genesisAcc` over the
teeth genesis and `accumulate` the honest step into it, getting a length-1 accumulator whose witness is
a REAL `WellFormedChain`, and read off its conservation (the `100` supply). So the IVC step is inhabited
on a genuine executor run, not an empty implication. -/

section IvcRealize

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)

/-- The honest step as a `ChainStep` over the teeth genesis (reusing `HistoryAggregation.honestStep`). -/
abbrev ivcHonestStep : ChainStep := honestStep

/-- The realizing accumulator: `genesisAcc` over the teeth genesis, then one `accumulate` of the honest
step. The seam holds because `genesisAcc`'s head IS genesis and the honest step consumes genesis; the
turn-context match is vacuous (the genesis fold has no last step). -/
def ivcRealAcc : Acc zCH zRH zcmb zcompress zcompressN teethGenesis :=
  accumulate zCH zRH zcmb zcompress zcompressN (genesisAcc zCH zRH zcmb zcompress zcompressN teethGenesis)
    ivcHonestStep
    (by simp [ivcHonestStep, honestStep])
    (by intro last hlast; simp [genesisAcc] at hlast)

/-- **`ivc_accumulate_fires` (IVC non-vacuity).** The realizing accumulator attests a REAL well-formed
1-step history from genesis — the IVC step genuinely fired and preserved the invariant. -/
theorem ivc_accumulate_fires :
    WellFormedChain zCH zRH zcmb zcompress zcompressN teethGenesis ivcRealAcc.steps :=
  acc_attests_whole_history zCH zRH zcmb zcompress zcompressN ivcRealAcc

/-- **`ivc_acc_conserves_real` (the accumulated history conserves — a TRUE arithmetic fact).** The
realizing accumulator's folded history conserves the ledger total: head total = genesis total. So the
unbounded-IVC conservation corollary delivers a real conservation fact on a real executor run. -/
theorem ivc_acc_conserves_real :
    recTotal (Acc.head zCH zRH zcmb zcompress zcompressN ivcRealAcc).kernel
      = recTotal teethGenesis.kernel :=
  acc_conserves zCH zRH zcmb zcompress zcompressN ivcRealAcc

end IvcRealize

end Accumulator

/-! ## 8. Axiom hygiene. -/

#assert_axioms Dregg2.Circuit.RecursiveAggregation.every_leaf_verifies_implies_executed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
-- the GENESIS ANCHOR (the verify-side dual of the final-root anchor — PREFIX completeness, TIER3 2c):
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_anchored_history
#assert_axioms Dregg2.Circuit.RecursiveAggregation.anchored_history_starts_at_genesis
#assert_axioms Dregg2.Circuit.RecursiveAggregation.anchored_attests_rejects_fabricated_genesis
#assert_axioms Dregg2.Circuit.RecursiveAggregation.anchored_conserves_from_verification
#assert_axioms Dregg2.Circuit.RecursiveAggregation.anchored_fires_on_real_chain
#assert_axioms Dregg2.Circuit.RecursiveAggregation.anchored_tooth_bites_on_real_chain
#assert_axioms Dregg2.Circuit.RecursiveAggregation.attested_history_conserves
-- the CRITICAL-3 closure: conservation-over-history DERIVED from `verify agg.root`, no StateChained:
#assert_axioms Dregg2.Circuit.RecursiveAggregation.conserves_from_verification
-- whole-history NON-OMISSION derived from `verify agg.root` (the rotated commit binds every receipt log):
#assert_axioms Dregg2.Circuit.RecursiveAggregation.non_omission_from_verification
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_engine_sound
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_fires_on_real_chain
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_chain_first_turn_executed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind
#assert_axioms Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap
-- the UNBOUNDED IVC accumulator: the running left-fold preserves whole-history attestation, by
-- induction from genesis (the part Mina lacks — a machine-checked IVC soundness induction):
#assert_axioms Dregg2.Circuit.RecursiveAggregation.lastStateOf_snoc
#assert_axioms Dregg2.Circuit.RecursiveAggregation.stateChained_snoc
#assert_axioms Dregg2.Circuit.RecursiveAggregation.chainBound_snoc
#assert_axioms Dregg2.Circuit.RecursiveAggregation.lastStateOf_eq_getLast_post
#assert_axioms Dregg2.Circuit.RecursiveAggregation.accumulate_preserves_wellformed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_attests_whole_history
#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_attests_run
#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_conserves
-- IVC non-vacuity (the accumulate step FIRES on a real executor run from genesis):
#assert_axioms Dregg2.Circuit.RecursiveAggregation.ivc_accumulate_fires
#assert_axioms Dregg2.Circuit.RecursiveAggregation.ivc_acc_conserves_real

/-! ## 9. THE ORDERED SEGMENT-ACCUMULATOR — the whole-chain binding DERIVED, not assumed.

§§1–8 took the whole-chain ordered binding as a NAMED hypothesis: `EngineSound.binding_sound` asserts
a verifying `TurnChainBindingAir` leaf delivers `ChainBound` + the genesis/final pins, and
`acc_attests_whole_history` then PROJECTS the attestation off the `Acc.leanWitness` the prover stored.
That is exactly the mixed-root hole codex's segment-accumulator fix closes BY CONSTRUCTION
(`docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md`): every descriptor/execution leaf — and every
aggregation node — carries a constant-size ordered SEGMENT summary `Seg = (firstOld, lastNew, count,
acc)`; a node combines its children with state-continuity (`L.lastNew = R.firstOld`), count additivity,
and an ORDERED Poseidon2 digest `acc = H(L.acc, R.acc)`; the host checks the root's exposed segment
equals the carried claim. The Rust verifier enforces this (`ivc_turn_chain.rs:224/1963`, codex
`CODEX-IVC-FINAL-REVIEW.md` — the mixed-root forgery REJECTS). Here we DERIVE — no longer assume — that
a verifying segment tree's root claim IS the genuine ordered segment-summary of the EXECUTED leaves.

THREE soundness layers, cleanly separated (codex `docs/CODEX-DISCHARGE-SKELETON.md`):

  * **`SegSound` (LAYER-1 — the per-node FRI/STARK crypto floor, ASSUMED, realizable).** Provides ONLY
    *local* statement soundness: a verifying LEAF node's exposed segment is its genuine leaf-segment
    (and its turn executed); a verifying COMBINE node's children verify and its exposed segment
    satisfies the local `CombineOk` constraint w.r.t. the children's exposed segments. This is the
    `EngineSound` boundary §2 already carries, refined to per-node and kept STRICTLY LOCAL — it does NOT
    mention `GenuineSeg`, `ChainBound`, or the whole history. (The leaf's executor witness is in fact
    free: a `ChainStep` bakes `commits`.)

  * **`subtree_binding` (LAYER-2 — THE DISCHARGE, DERIVED).** By induction on the aggregation tree, a
    verifying subtree's exposed segment is the genuine ordered segment-summary (`GenuineSeg`) of the
    leaves under it. BASE = a verifying leaf (LAYER-1 ⇒ exposed = leaf-segment). STEP = a verifying
    combine node (LAYER-1 ⇒ children verify + `CombineOk`; the children's `GenuineSeg` by IH; the
    `CombineOk` fields force the parent = the ordered concatenation). From `GenuineSeg` we DERIVE the
    whole-chain facts the §2 binding leaf used to ASSUME: `genuine_count`, `genuine_ordered`
    (`ChainBound` over the WHOLE leaf list — exactly `WellFormedChain.bound`/`binding_sound`),
    `genuine_firstOld`/`genuine_lastNew` (genesis = first leaf's old root, final = last leaf's new root).
    THIS is the ordered-binding discharge — `ordered_binding_derived` + `segment_tree_wellformed`
    produce `WellFormedChain.bound` from the segment construction, no longer as a hypothesis.

  * **`PoseidonSegBinding` (LAYER-3 — the digest collision-resistance crypto floor, ASSUMED,
    realizable).** Semantic uniqueness of the ordered digest: equal `acc` ⇒ equal ordered leaf
    sequence. The DISTINCT-ENDPOINT mixed-root forgery (B's claim has a different genesis/final than A's
    executed leaves) is rejected with NO appeal to this floor — `subtree_binding` forces the endpoints
    (`no_mixed_root_distinct_endpoint`). The SAME-ENDPOINT case (B's claim shares A's endpoints but a
    different interior leaf sequence) reduces to a Poseidon2 collision; that is the 4-lane W24 digest CR
    codex confirmed the close rests on (`CODEX-IVC-FINAL-REVIEW.md`). Named here as the terminal crypto
    floor it is (`no_mixed_root`) — NOT a hole, NOT something Lean can discharge.

So the whole-chain ORDERED binding moves from ASSUMED (`binding_sound`) to DERIVED (`subtree_binding` +
`GenuineSeg` corollaries); only the per-node proof soundness (LAYER-1) and the digest CR (LAYER-3)
remain as the two NAMED, realizable crypto floors. `#assert_axioms`-clean. -/

section Segment

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)
/-! The ordered (non-commutative) Poseidon2 digest combiner `H` — the running `acc = H(old,new)` at a
leaf and `acc = H(L.acc, R.acc)` at a node. Its collision-resistance is `PoseidonSegBinding` (LAYER-3). -/
variable (H : ℤ → ℤ → ℤ)

/-- **`Seg`** — the constant-size ordered segment summary every leaf/node carries: the segment's first
old root, its last new root, its turn count, and the ordered digest `acc` of the (old,new) pairs under
it. The Rust 7-felt claim `(genesis, final, count, + 4 BabyBear digest lanes)` (`ivc_turn_chain.rs:224`);
the four digest lanes are abstracted to the single field `acc : ℤ` over the combiner `H`. -/
structure Seg where
  firstOld : ℤ
  lastNew  : ℤ
  count    : Nat
  acc      : ℤ

/-- The genuine leaf segment of a `ChainStep`: `(oldRoot, newRoot, 1, H oldRoot newRoot)`. -/
def leafSeg (s : ChainStep) : Seg where
  firstOld := ChainStep.oldRoot CH RH cmb compress compressN s
  lastNew  := ChainStep.newRoot CH RH cmb compress compressN s
  count    := 1
  acc      := H (ChainStep.oldRoot CH RH cmb compress compressN s)
                (ChainStep.newRoot CH RH cmb compress compressN s)

/-- The genuine combine of two adjacent segments: endpoints from the ends, counts add, digest folds
ordered. (Continuity `L.lastNew = R.firstOld` is enforced separately by `CombineOk`.) -/
def combineSeg (L R : Seg) : Seg where
  firstOld := L.firstOld
  lastNew  := R.lastNew
  count    := L.count + R.count
  acc      := H L.acc R.acc

/-- **`CombineOk L R parent`** — the LOCAL combine constraint a verifying aggregation node enforces in
circuit: the parent's endpoints/count/digest are the genuine fold of the children's, AND the two
children are state-continuous at the seam (`L.lastNew = R.firstOld`). This is what LAYER-1 delivers for
a verifying node; it mentions only the node and its immediate children — nothing whole-history. -/
def CombineOk (L R parent : Seg) : Prop :=
  parent.firstOld = L.firstOld ∧ parent.lastNew = R.lastNew ∧
    parent.count = L.count + R.count ∧ parent.acc = H L.acc R.acc ∧ L.lastNew = R.firstOld

/-- **`AggTree`** — the aggregation tree the prover folds: a leaf carries its executed `ChainStep` and
the segment it EXPOSES; a node carries the segment it exposes and its two children. (The recursion
proofs themselves are abstracted into `Accepts` below — each subtree has a verification status.) -/
inductive AggTree where
  | leaf : ChainStep → Seg → AggTree
  | node : Seg → AggTree → AggTree → AggTree

/-- The segment a subtree EXPOSES (the prover's claim for it). The host checks the ROOT's exposed
segment equals the carried public claim. -/
def exposedSeg : AggTree → Seg
  | .leaf _ c   => c
  | .node c _ _ => c

/-- The executed leaves under a subtree, in chain (in-order) order — the genuine history the subtree
attests. -/
def treeLeaves : AggTree → List ChainStep
  | .leaf s _   => [s]
  | .node _ l r => treeLeaves l ++ treeLeaves r

/-- **`GenuineSeg s leaves`** — `s` IS the genuine ordered segment-summary of `leaves`: a single
executed leaf yields its `leafSeg`; a state-continuous concatenation yields the `combineSeg` of the
parts. This is the DERIVED object (LAYER-2) — NOT supplied by the engine, but reconstructed by
`subtree_binding` from per-node local soundness. -/
inductive GenuineSeg : Seg → List ChainStep → Prop
  | leaf (s : ChainStep) : GenuineSeg (leafSeg CH RH cmb compress compressN H s) [s]
  | node {sl sr : Seg} {ls rs : List ChainStep}
      (hl : GenuineSeg sl ls) (hr : GenuineSeg sr rs) (hcont : sl.lastNew = sr.firstOld) :
      GenuineSeg (combineSeg H sl sr) (ls ++ rs)

/-! The per-subtree verification status `Accepts` (the recursion proof of that subtree verifies).
Abstract — in the realized engine `Accepts t := (verify t.proof = true)`; we never inspect internals. -/
variable (Accepts : AggTree → Prop)

/-- **`SegSound t`** (LAYER-1, the per-node crypto floor — ASSUMED, realizable). Per-node *local*
soundness, recursive over the tree: a verifying LEAF exposes its genuine leaf-segment (its turn
executed); a verifying COMBINE node's two children verify and its exposed segment satisfies the local
`CombineOk`. STRICTLY LOCAL — it never mentions `GenuineSeg`, `ChainBound`, or the whole history. -/
def SegSound : AggTree → Prop
  | .leaf s c   => Accepts (.leaf s c) →
      (recCexec s.pre s.turn = some s.post ∧ c = leafSeg CH RH cmb compress compressN H s)
  | .node c l r => (Accepts (.node c l r) →
        Accepts l ∧ Accepts r ∧ CombineOk H (exposedSeg l) (exposedSeg r) c)
      ∧ SegSound l ∧ SegSound r

/-- A satisfied `CombineOk` pins the parent to the genuine `combineSeg` of the children, AND yields the
seam-continuity. The structural fact the induction step turns into a `GenuineSeg.node`. -/
theorem combineOk_eq {L R parent : Seg} (h : CombineOk H L R parent) :
    parent = combineSeg H L R ∧ L.lastNew = R.firstOld := by
  obtain ⟨hf, hln, hcnt, hacc, hcont⟩ := h
  refine ⟨?_, hcont⟩
  obtain ⟨pf, pl, pc, pa⟩ := parent
  simp only [combineSeg, Seg.mk.injEq]
  exact ⟨hf, hln, hcnt, hacc⟩

/-! ### The LAYER-2 induction — derive `GenuineSeg` from LAYER-1 local soundness. -/

/-- **`subtree_binding` (THE DISCHARGE).** A verifying subtree's exposed segment IS the genuine ordered
segment-summary of its executed leaves. By induction on the aggregation tree: BASE = a verifying leaf
(LAYER-1 ⇒ exposed = leaf-segment); STEP = a verifying combine node (LAYER-1 ⇒ children verify +
`CombineOk`; the children's `GenuineSeg` by IH; `CombineOk` forces the parent = the ordered
concatenation). The whole-chain ordered binding is DERIVED here, not assumed. -/
theorem subtree_binding (t : AggTree)
    (hs : SegSound CH RH cmb compress compressN H Accepts t) (hv : Accepts t) :
    GenuineSeg CH RH cmb compress compressN H (exposedSeg t) (treeLeaves t) := by
  induction t with
  | leaf s c =>
      have hc := (hs hv).2
      simp only [exposedSeg, treeLeaves]
      rw [hc]
      exact GenuineSeg.leaf s
  | node c l r ihl ihr =>
      obtain ⟨hnode, hsl, hsr⟩ := hs
      obtain ⟨hvl, hvr, hcomb⟩ := hnode hv
      have hgl := ihl hsl hvl
      have hgr := ihr hsr hvr
      obtain ⟨hpar, hcont⟩ := combineOk_eq H hcomb
      simp only [exposedSeg, treeLeaves]
      rw [hpar]
      exact GenuineSeg.node hgl hgr hcont

/-! ### Corollaries of `GenuineSeg` — the whole-chain facts, all DERIVED (no crypto floor). -/

/-- A genuine summary is over a NONEMPTY leaf list (every subtree has ≥1 executed leaf). -/
theorem genuine_ne_nil {s : Seg} {l : List ChainStep}
    (h : GenuineSeg CH RH cmb compress compressN H s l) : l ≠ [] := by
  induction h with
  | leaf s => simp
  | node hl hr hcont ihl ihr =>
      rename_i sl sr ls rs
      cases ls with
      | nil => exact absurd rfl ihl
      | cons a t => simp

/-- The genuine count IS the number of executed leaves (no drop/insert). -/
theorem genuine_count {s : Seg} {l : List ChainStep}
    (h : GenuineSeg CH RH cmb compress compressN H s l) : s.count = l.length := by
  induction h with
  | leaf s => simp [leafSeg]
  | node hl hr hcont ihl ihr =>
      simp only [combineSeg, List.length_append, ihl, ihr]

/-- The genuine genesis IS the first executed leaf's old root (the chain's true start). -/
theorem genuine_firstOld {s : Seg} {l : List ChainStep}
    (h : GenuineSeg CH RH cmb compress compressN H s l) :
    ∀ x, l.head? = some x → s.firstOld = ChainStep.oldRoot CH RH cmb compress compressN x := by
  induction h with
  | leaf s =>
      intro x hx
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst hx
      simp [leafSeg]
  | node hl hr hcont ihl ihr =>
      rename_i sl sr ls rs
      intro x hx
      rw [List.head?_append_of_ne_nil ls (genuine_ne_nil CH RH cmb compress compressN H hl)] at hx
      simp only [combineSeg]
      exact ihl x hx

/-- The genuine final IS the last executed leaf's new root (the chain's true end). -/
theorem genuine_lastNew {s : Seg} {l : List ChainStep}
    (h : GenuineSeg CH RH cmb compress compressN H s l) :
    ∀ x, l.getLast? = some x → s.lastNew = ChainStep.newRoot CH RH cmb compress compressN x := by
  induction h with
  | leaf s =>
      intro x hx
      simp only [List.getLast?_singleton, Option.some.injEq] at hx
      subst hx
      simp [leafSeg]
  | node hl hr hcont ihl ihr =>
      rename_i sl sr ls rs
      intro x hx
      rw [List.getLast?_append_of_ne_nil ls (genuine_ne_nil CH RH cmb compress compressN H hr)] at hx
      simp only [combineSeg]
      exact ihr x hx

/-- **`chainBound_append`** — splice two `ChainBound` segments at a continuous seam. The load-bearing
combinatorial lemma of the ordered-binding derivation: a drop/reorder at the join breaks exactly the
seam `Continues`. -/
theorem chainBound_append :
    ∀ (xs ys : List ChainStep),
      ChainBound CH RH cmb compress compressN xs →
      ChainBound CH RH cmb compress compressN ys →
      (∀ a b, xs.getLast? = some a → ys.head? = some b →
        Continues CH RH cmb compress compressN a b) →
      ChainBound CH RH cmb compress compressN (xs ++ ys)
  | [], ys, _, hy, _ => by simpa using hy
  | [a], ys, _, hy, hjoin => by
      cases ys with
      | nil => simp [ChainBound]
      | cons b rest =>
          show ChainBound CH RH cmb compress compressN (a :: b :: rest)
          exact ⟨hjoin a b (by simp) (by simp), hy⟩
  | a :: b :: rest, ys, hx, hy, hjoin => by
      obtain ⟨hab, htail⟩ := hx
      have ih := chainBound_append (b :: rest) ys htail hy
        (fun x y hxl hyl => hjoin x y (by rw [List.getLast?_cons_cons]; exact hxl) hyl)
      show ChainBound CH RH cmb compress compressN (a :: b :: (rest ++ ys))
      exact ⟨hab, by simpa using ih⟩

/-- **`genuine_ordered`** — a genuine summary's leaves are `ChainBound`: the temporal tooth holds over
the WHOLE list. This is EXACTLY the `WellFormedChain.bound` / `EngineSound.binding_sound` fact that §2
ASSUMED — here DERIVED from `GenuineSeg` (hence, via `subtree_binding`, from per-node local soundness). -/
theorem genuine_ordered {s : Seg} {l : List ChainStep}
    (h : GenuineSeg CH RH cmb compress compressN H s l) :
    ChainBound CH RH cmb compress compressN l := by
  induction h with
  | leaf s => simp [ChainBound]
  | node hl hr hcont ihl ihr =>
      rename_i sl sr ls rs
      refine chainBound_append CH RH cmb compress compressN ls rs ihl ihr ?_
      intro a b ha hb
      have h1 := genuine_lastNew CH RH cmb compress compressN H hl a ha
      have h2 := genuine_firstOld CH RH cmb compress compressN H hr b hb
      show ChainStep.newRoot CH RH cmb compress compressN a
            = ChainStep.oldRoot CH RH cmb compress compressN b
      rw [← h1, hcont, h2]

/-! ### The keystones — root binding, ordered-binding discharge, mixed-root rejection. -/

/-- **`root_binds_carried_claim`.** When the host check passes (the root's exposed segment equals the
carried public claim) and the root verifies, the carried CLAIM is the genuine ordered segment-summary
of the executed leaves. The whole-chain claim is bound to the actual execution. -/
theorem root_binds_carried_claim (t : AggTree) (carried : Seg)
    (hs : SegSound CH RH cmb compress compressN H Accepts t) (hv : Accepts t)
    (hhost : exposedSeg t = carried) :
    GenuineSeg CH RH cmb compress compressN H carried (treeLeaves t) := by
  rw [← hhost]
  exact subtree_binding CH RH cmb compress compressN H Accepts t hs hv

/-- **`ordered_binding_derived`.** A verifying segment tree's leaves are `ChainBound` — the whole-chain
ordered binding, DERIVED from the segment construction, NOT taken as a hypothesis. -/
theorem ordered_binding_derived (t : AggTree)
    (hs : SegSound CH RH cmb compress compressN H Accepts t) (hv : Accepts t) :
    ChainBound CH RH cmb compress compressN (treeLeaves t) :=
  genuine_ordered CH RH cmb compress compressN H
    (subtree_binding CH RH cmb compress compressN H Accepts t hs hv)

/-- **`segment_tree_wellformed` (THE CONNECT).** A verifying segment tree, with the producer's
state-continuity witness, IS a `WellFormedChain` — and its `bound` field is now DERIVED
(`ordered_binding_derived`) from the segment construction, where §2 took it as `binding_sound`. The
`chained` (state/log continuity) remains the named producer witness / CR residual, UNCHANGED. -/
theorem segment_tree_wellformed (g : RecChainedState) (t : AggTree)
    (hs : SegSound CH RH cmb compress compressN H Accepts t) (hv : Accepts t)
    (hchain : StateChained g (treeLeaves t)) :
    WellFormedChain CH RH cmb compress compressN g (treeLeaves t) :=
  { chained := hchain
  , bound := ordered_binding_derived CH RH cmb compress compressN H Accepts t hs hv }

/-- **`no_mixed_root_distinct_endpoint` (the DISTINCT-endpoint forgery, FULLY DERIVED).** A verifying
root cannot export a claim whose genesis differs from its OWN first executed leaf's old root: the host
check binds the claim to the genuine summary, which `genuine_firstOld` pins to the real genesis. So
"B's claim (a different genesis), A's leaves" is impossible — with NO appeal to the digest CR floor. -/
theorem no_mixed_root_distinct_endpoint (t : AggTree) (claimB : Seg) (a : ChainStep)
    (hs : SegSound CH RH cmb compress compressN H Accepts t) (hv : Accepts t)
    (hhost : exposedSeg t = claimB)
    (ha : (treeLeaves t).head? = some a)
    (hforge : claimB.firstOld ≠ ChainStep.oldRoot CH RH cmb compress compressN a) :
    False :=
  hforge (genuine_firstOld CH RH cmb compress compressN H
    (root_binds_carried_claim CH RH cmb compress compressN H Accepts t claimB hs hv hhost) a ha)

/-- **`PoseidonSegBinding` (LAYER-3 — the digest collision-resistance floor, ASSUMED, realizable).**
Semantic uniqueness of the ordered Poseidon2 digest: two genuine summaries with equal `acc` are over
the SAME ordered leaf sequence. Realizable as the 4-lane W24 digest CR (`CODEX-IVC-FINAL-REVIEW.md`);
NOT a hole — a terminal crypto primitive, exactly like the FRI soundness in `EngineSound`. -/
def PoseidonSegBinding : Prop :=
  ∀ (s1 s2 : Seg) (l1 l2 : List ChainStep),
    GenuineSeg CH RH cmb compress compressN H s1 l1 →
    GenuineSeg CH RH cmb compress compressN H s2 l2 →
    s1.acc = s2.acc → l1 = l2

/-- **`no_mixed_root` (the SAME-endpoint forgery, under the digest CR floor).** Even when a forged
claim shares A's endpoints, a verifying root cannot export a claim that is the genuine summary of a
DIFFERENT leaf sequence: the host check binds the claim to A's genuine summary, and `PoseidonSegBinding`
(equal digest ⇒ equal leaves) forces the two leaf sequences to coincide. This is the same-endpoint case
the distinct-endpoint argument cannot reach — closed by reduction to a Poseidon2 collision, the NAMED
terminal floor. -/
theorem no_mixed_root (hpsb : PoseidonSegBinding CH RH cmb compress compressN H)
    (t : AggTree) (claimB : Seg) (leavesB : List ChainStep)
    (hs : SegSound CH RH cmb compress compressN H Accepts t) (hv : Accepts t)
    (hB : GenuineSeg CH RH cmb compress compressN H claimB leavesB)
    (hhost : exposedSeg t = claimB)
    (hmixed : leavesB ≠ treeLeaves t) :
    False :=
  hmixed (hpsb claimB claimB leavesB (treeLeaves t) hB
    (root_binds_carried_claim CH RH cmb compress compressN H Accepts t claimB hs hv hhost) rfl)

end Segment

/-! ### §9 NON-VACUITY — the discharge FIRES on a real 2-leaf executor chain.

The induction would be hollow if no genuine combine node could fire. We build a REAL 2-step chain from
the teeth genesis (two honest transfers of 10), expose its genuine segments, and prove `SegSound` holds
with the accepting status — so `subtree_binding` concludes a genuine `GenuineSeg` over the two executed
leaves, and `ordered_binding_derived` delivers a REAL `ChainBound` over them. The combine node's
state-continuity holds DEFINITIONALLY (the second step consumes the first's post under the same
turn-context), exactly the seam the segment-accumulator binds. -/

section SegRealize

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)

/-- A concrete digest combiner for the witness. -/
def zH : ℤ → ℤ → ℤ := fun _ _ => 0

/-- A genuine SECOND honest step: from the post-state of `honestStep`, cell 0 transfers another 10.
`commits` is discharged by `decide` — the executor really takes the step. -/
def honestStep2 : ChainStep where
  pre := honestStep.post
  turn := honestTurn
  post := (recCexec honestStep.post honestTurn).get (by decide)
  commits := (Option.some_get _).symm

/-- The realizing 2-leaf aggregation tree: one combine node over the two honest leaves, each exposing
its genuine `leafSeg`, the node exposing their genuine `combineSeg`. -/
def realTree : AggTree :=
  .node (combineSeg zH (leafSeg zCH zRH zcmb zcompress zcompressN zH honestStep)
                       (leafSeg zCH zRH zcmb zcompress zcompressN zH honestStep2))
        (.leaf honestStep  (leafSeg zCH zRH zcmb zcompress zcompressN zH honestStep))
        (.leaf honestStep2 (leafSeg zCH zRH zcmb zcompress zcompressN zH honestStep2))

/-- **`real_seg_sound` (LAYER-1 inhabited).** The per-node local soundness holds on the realizing tree
under the accepting status: each leaf exposes its genuine `leafSeg` (its honest step executed), and the
combine node's `CombineOk` holds — the seam-continuity by `rfl` (step 2 consumes step 1's post under the
same turn-context). So `SegSound` is INHABITED on a real chain; the discharge is not vacuous. -/
theorem real_seg_sound :
    SegSound zCH zRH zcmb zcompress zcompressN zH (fun _ => True) realTree := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  · intro _; exact ⟨honestStep.commits, rfl⟩
  · intro _; exact ⟨honestStep2.commits, rfl⟩

/-- **`real_tree_binds` (the discharge FIRES).** `subtree_binding` concludes a genuine `GenuineSeg`:
the root's exposed segment IS the genuine ordered summary of the two executed leaves. A real, non-vacuous
firing of the LAYER-2 induction. -/
theorem real_tree_binds :
    GenuineSeg zCH zRH zcmb zcompress zcompressN zH (exposedSeg realTree) (treeLeaves realTree) :=
  subtree_binding zCH zRH zcmb zcompress zcompressN zH (fun _ => True) realTree real_seg_sound trivial

/-- **`real_tree_ordered` (the ordered binding DERIVED on a real chain).** A genuine `ChainBound` over
the two executed leaves — the whole-chain ordered binding, derived from the segment tree, on a real run. -/
theorem real_tree_ordered :
    ChainBound zCH zRH zcmb zcompress zcompressN (treeLeaves realTree) :=
  ordered_binding_derived zCH zRH zcmb zcompress zcompressN zH (fun _ => True) realTree real_seg_sound trivial

/-- **`real_tree_count` (the count is genuine).** The root segment's count equals the number of executed
leaves — read off the derived `GenuineSeg`. -/
theorem real_tree_count :
    (exposedSeg realTree).count = (treeLeaves realTree).length :=
  genuine_count zCH zRH zcmb zcompress zcompressN zH real_tree_binds

/-- And that count is literally `2` — a TRUE arithmetic fact, not a husk. -/
theorem real_tree_count_is_two : (exposedSeg realTree).count = 2 := rfl

end SegRealize

/-! ## 10. THE RUNNING-VK FIXED POINT — perpetual constancy MECHANIZED (the depth-invariance induction).

§§1–9 prove the whole-history ATTESTATION is preserved by the unbounded fold. They are SILENT on the
SHAPE of the running recursion proof's verifying key — the property a LIGHT CLIENT needs to pin ONE
trust anchor and accept an accumulated chain of ANY length: that the running VK is CONSTANT across fold
depth. `circuit-prove/src/accumulator.rs` MEASURES this (`wrapped_running_vk_is_constant_across_depth`):
the running aggregation VK settles to a fixed point at depth 4 (after a finite 2-step transient) and is
BYTE-IDENTICAL from there — `rows`, `degree_bits`, AND the preprocessed commitment all equal at depth 4
and depth 5. The "perpetual" half — `∀N, VK_N = VK_4` — used to rest on a PROSE structural-idempotence
argument. THIS SECTION MECHANIZES it.

The mechanization, tiered by what each part rests on (honest):

  * **The fold-shape transition is a deterministic function of SHAPE ALONE — `step : VkShape → VkShape`.**
    The parent aggregation circuit's op-list (hence its preprocessed commitment = the VK core) is built
    by `verify_p3_batch_proof_circuit` (the recursion fork) from ONLY the running input proof's SHAPE
    quantities — its `rows`, `table_packing`, the `non_primitives` op_type/rows/lanes manifest, and the
    per-instance public-value COUNTS (`entry.public_values.len()`, a count, never the values). The
    witness VALUES never enter the op-list, and `recursion_vk_fingerprint` (the impl) is correspondingly
    content-independent ("two proofs of the same circuit shape over different data fingerprint
    identically"). So the running VK at depth n+1 is a FUNCTION of the running VK at depth n and the
    constant leaf shape — modeled here as `step`. Modeling the transition as a FUNCTION of `VkShape`
    (not a relation over proofs) is precisely the encoding of that discharged fact. (Discharge: the fork
    code-audit + the value-independence Rust tooth `running_vk_fixed_point_is_value_independent` — two
    DIFFERENT value-streams reach the SAME depth-4 VK material.)

  * **The depth-4 VK is a FIXED POINT of `step` — `hfix : step anchor = anchor`.** MEASURED:
    `wrapped_running_vk_is_constant_across_depth` shows the full VK material is byte-identical at depth 4
    and depth 5 — i.e. one application of `step` to the depth-4 shape reproduces it exactly.

  * **THEREFORE the running VK is PERPETUALLY CONSTANT past depth 4** — `running_vk_perpetually_constant`:
    `∀ n, step^[n] anchor = anchor`. This is the deterministic-iteration induction the prose argument
    named, now machine-checked. A light client pins the ONE depth-4 anchor and EVERY deeper running proof
    carries it (`running_vk_one_anchor`).

The remaining recursion-fork work is NOT this perpetual claim (mechanized here): it is shrinking the
finite 2-step TRANSIENT (depths 2,3, before the fixed point) to zero, so every fold from the FIRST
aggregation already carries the one anchor. That needs a CANONICAL agg-shaped SEED whose own left is
agg-shaped (the Pickles step∘wrap identity/normalize fold) — a primitive the fork exposes none of today.
The transient is a USABILITY uniformity, NOT a soundness gate: the VK-identity pin TRACKS the running
commitment through it (honest transient folds are not rejected), and a light client anchors on the
perpetual fixed-point VK. -/

section RunningVkFixedPoint

/-! The running recursion proof's verifying-key SHAPE (`VkShape`) — the full verifier-reconstruction
material the `recursion_vk_fingerprint` hashes (table packing, `rows`, `degree_bits`, the non-primitive
manifest, and the preprocessed commitment = the op-list / VK core). Opaque here: the theorem speaks to
its TRANSITION across folds, not its internals.

`step` is the fold-shape transition: the VK shape of the running proof at depth n+1 as a DETERMINISTIC
function of the VK shape at depth n (the leaf shape being constant). That this is a function of SHAPE
ALONE — not of the witness values — is the fork's content-independence (the verifier op-list is built
from the input proof's shape quantities only); modeling it as `VkShape → VkShape` encodes exactly that
discharged fact. -/
variable {VkShape : Type}
variable (step : VkShape → VkShape)

/-- **`running_vk_iterate_fixed` (the deterministic-iteration core).** Iterating a deterministic map
from a fixed point stays at the fixed point — `Mathlib.Function.iterate_fixed`. The pure-math backbone
of perpetual constancy: the depth-4 shape is reproduced by every further fold. -/
theorem running_vk_iterate_fixed {a : VkShape} (hfix : step a = a) :
    ∀ n, step^[n] a = a :=
  fun n => Function.iterate_fixed hfix n

/-- **`running_vk_perpetually_constant` (THE DEPTH-INVARIANCE HEADLINE).** Given the MEASURED depth-4
fixed point (`hfix : step anchor = anchor` — the byte-identical depth-4 == depth-5 VK material), the
running VK at EVERY depth past 4 — `step^[n] anchor`, the n-th fold beyond the fixed point — equals the
depth-4 anchor. So `∀N, VK_N = VK_4`: a fixed-size verifier forever, no longer a prose idempotence
argument but a machine-checked induction off ONE measured fixed point. -/
theorem running_vk_perpetually_constant {anchor : VkShape} (hfix : step anchor = anchor) :
    ∀ n, step^[n] anchor = anchor :=
  running_vk_iterate_fixed step hfix

/-- **`running_vk_one_anchor` (the light-client single-anchor property).** Any two running proofs at or
past the fixed point carry the IDENTICAL VK shape — so a light client pins ONE anchor and accepts an
accumulated chain of ANY length. -/
theorem running_vk_one_anchor {anchor : VkShape} (hfix : step anchor = anchor) (m n : Nat) :
    step^[m] anchor = step^[n] anchor := by
  rw [running_vk_perpetually_constant step hfix m, running_vk_perpetually_constant step hfix n]

end RunningVkFixedPoint

/-! ### §10 NON-VACUITY — the fixed-point induction FIRES on a concrete transient + fixed point.

The mechanization would be hollow if no transition with a genuine transient AND a reachable fixed point
existed. We model exactly the measured shape: a transition that INCREMENTS through a transient (depths
0,1,2,3) and CLAMPS at 4 (the depth-4 fixed point), then fire the perpetual-constancy theorem off the
anchor — and witness the transient is REAL (depth 0 ≠ depth 4), the A/B companion of
`wrap_grows_vk_when_disabled`. -/
section RunningVkRealize

/-- A concrete VK-shape carrier for the witness — a Nat standing for the settled fold depth/shape. -/
abbrev RealVk := Nat

/-- A concrete fold-shape transition mirroring the MEASURED shape: it increments through the transient
(depths < 4) and is STATIONARY at the fixed point (depths ≥ 4 map to 4). The depth-4 shape `4` is its
fixed point. -/
def realStep : RealVk → RealVk := fun n => if 4 ≤ n then 4 else n + 1

/-- The MEASURED fixed point on the witness: `realStep 4 = 4` (the depth-4 == depth-5 reproduction). -/
theorem real_running_vk_fixed : realStep 4 = 4 := by decide

/-- **`real_running_vk_perpetual` (the headline WITNESSED).** The perpetual-constancy theorem fires:
from the witnessed fixed point, every iterate equals the anchor — a real, non-vacuous instance of the
depth-invariance induction (`∀N, VK_N = VK_4`). -/
theorem real_running_vk_perpetual : ∀ n, realStep^[n] 4 = 4 :=
  running_vk_perpetually_constant realStep real_running_vk_fixed

/-- **`real_running_vk_transient_is_real` (the non-vacuity A/B half).** The modeled transition genuinely
MOVES through the transient before settling: the depth-0 shape differs from the depth-4 shape
(`realStep^[4] 0 = 4 ≠ 0`). So the fixed-point equality asserted above is LOAD-BEARING (the early shapes
really differ), exactly as the Rust `wrap_grows_vk_when_disabled` confirms the measured transient is
real. -/
theorem real_running_vk_transient_is_real : realStep^[4] 0 ≠ realStep^[0] 0 := by decide

end RunningVkRealize

/-! ### §10 axiom hygiene — the running-VK fixed point is `#assert_axioms`-clean. -/
#assert_axioms Dregg2.Circuit.RecursiveAggregation.running_vk_iterate_fixed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.running_vk_perpetually_constant
#assert_axioms Dregg2.Circuit.RecursiveAggregation.running_vk_one_anchor
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_running_vk_fixed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_running_vk_perpetual
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_running_vk_transient_is_real

/-! ### §9 axiom hygiene — the discharge + its corollaries + the two named floors. -/
#assert_axioms Dregg2.Circuit.RecursiveAggregation.combineOk_eq
#assert_axioms Dregg2.Circuit.RecursiveAggregation.subtree_binding
#assert_axioms Dregg2.Circuit.RecursiveAggregation.genuine_ne_nil
#assert_axioms Dregg2.Circuit.RecursiveAggregation.genuine_count
#assert_axioms Dregg2.Circuit.RecursiveAggregation.genuine_firstOld
#assert_axioms Dregg2.Circuit.RecursiveAggregation.genuine_lastNew
#assert_axioms Dregg2.Circuit.RecursiveAggregation.chainBound_append
#assert_axioms Dregg2.Circuit.RecursiveAggregation.genuine_ordered
#assert_axioms Dregg2.Circuit.RecursiveAggregation.root_binds_carried_claim
#assert_axioms Dregg2.Circuit.RecursiveAggregation.ordered_binding_derived
#assert_axioms Dregg2.Circuit.RecursiveAggregation.segment_tree_wellformed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.no_mixed_root_distinct_endpoint
#assert_axioms Dregg2.Circuit.RecursiveAggregation.no_mixed_root
-- §9 non-vacuity (the discharge FIRES on a real 2-leaf executor chain from genesis):
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_seg_sound
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_tree_binds
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_tree_ordered
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_tree_count
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_tree_count_is_two

end Dregg2.Circuit.RecursiveAggregation
