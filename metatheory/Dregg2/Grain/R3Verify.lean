/-
# `Dregg2.Grain.R3Verify` — GRAIN R3: the whole execution history is UNFOOLABLE, from a constant-size
aggregate, with NO host trust. The EXECUTABLE verifier, EXPORTED to run as native code.

**What R3 is.** A grain (`grain-verify`) attests a running acknowledged head/root at R1. R3 is the
guarantee that the WHOLE execution history BEHIND that head is unfoolable: every turn executed correctly
per the verified executor (execution INTEGRITY) and the chain is correctly ordered with nothing dropped,
inserted or reordered (COMPLETENESS — no host fabrication) — learned from ONE succinct aggregate, the
host re-witnessing nothing. **Honest scope (not an overclaim):** this REDUCES `grain-verify`'s
`WHOLE_HISTORY_GAP` to the STARK/apex soundness — it does NOT close it unconditionally. The load-bearing
`EngineSound` hypothesis is an ASSUMED boundary: `recursive_sound`/`binding_sound` are the FRI legs
proved *outside* Lean, and `leaf_sound` is only *dischargeable* by the single-turn apex
(`EngineSoundOfApex`) modulo its three still-open reconciliation mismatches. GIVEN that soundness, a
lying host cannot serve a fabricated or truncated history under an honest-looking head — but R3 here is a
genuine *reduction plus head-binding*, not an unconditional proof of unfoolability. The new delta over
the existing aggregation theorem is exactly the one head-equality rewrite that binds the sound history to
THIS grain's R1 anchor.

**Lean-first, the assurance IS the code (the `Fips204Verify` / storage-in-Lean pattern).** The R3 accept
DECISION lives here as a plain executable `def` (`r3VerifyCore`), `@[export]`ed as `r3VerifyFFI` for the
Rust `grain-verify` to call. Its SOUNDNESS is not re-derived: it COMPOSES the already-proved whole-history
aggregation headline `Circuit.RecursiveAggregation.light_client_verifies_whole_history` — the theorem that
a verified aggregate ⟹ the whole history is `AggregateAttests` (every turn correct + correctly ordered +
the public final root is the genuine fold). R3 adds exactly ONE thing over it: the HEAD BINDING — the
aggregate's committed head must equal the R1-anchored attestation head, so the sound history is about THIS
grain's THIS history, not a swapped one.

**The boundary is INHERITED, not introduced (named, not laundered).** `r3VerifyCore` takes the STARK
verifier's verified-status as an INPUT Bool: it is `verify agg.root`, the output of the heavy Rust
`verify_whole_chain_proof_bytes`, whose in-circuit soundness is the named, realizable
`RecursiveAggregation.EngineSound` boundary (the ONE FRI/recursion obligation — a `structure` field, not
an axiom). R3 carries `EngineSound` through UNCHANGED as the honest, already-existing hypothesis; it adds
NO new axiom and NO `def …Hard` on the load-bearing step. The head equality is a plain `ℤ` decision — no
crypto, fully proved.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); `EngineSound` enters as a hypothesis
FIELD exactly as it does in the composed headline. Verified with `lake build Dregg2.Grain.R3Verify`.
-/
import Dregg2.Circuit.RecursiveAggregation

namespace Dregg2.Grain.R3Verify

open Dregg2.Exec (RecChainedState recCexec)
open Dregg2.Distributed.HistoryAggregation (ChainStep ChainBound foldedFinalRoot)
open Dregg2.Circuit.RecursiveAggregation
  (Aggregate EngineSound AggregateAttests light_client_verifies_whole_history)

section Verify

variable (Proof : Type)
variable (verify : Proof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-! ## 1. The EXECUTABLE R3 verify core.

`r3VerifyCore` decides R3-accept from two inputs the Rust `grain-verify` supplies:
  * `aggregateVerified : Bool` — the verified-status of the whole-chain STARK aggregate, i.e. the output
    of the heavy `verify_whole_chain_proof_bytes` (`= verify agg.root` in the model). Its SOUNDNESS is
    the named `EngineSound` boundary; here it enters as the verified-status Bool.
  * `aggregateHead`, `anchoredHead : ℤ` — the aggregate's public committed head root and the R1-anchored
    attestation head. Equality binds the aggregate to THIS grain's THIS history.

A plain `def … : Bool`, fail-closed: any mismatch is `false`. This IS the object `@[export]` compiles to
native and `grain-verify` calls. -/
def r3VerifyCore (aggregateVerified : Bool) (aggregateHead anchoredHead : ℤ) : Bool :=
  aggregateVerified && aggregateHead == anchoredHead

/-- Decomposition of the accept decision: `r3VerifyCore` accepts IFF the aggregate verified AND the head
binds. Pure `Bool` algebra (`Int` is `LawfulBEq`, so `== ` reflects `=`). -/
theorem r3VerifyCore_true {v : Bool} {a b : ℤ} (h : r3VerifyCore v a b = true) :
    v = true ∧ a = b := by
  unfold r3VerifyCore at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, by simp only [beq_iff_eq] at h; exact h.2⟩

/-! ## 2. THE R3 VERDICT + THE SOUNDNESS HEADLINE — unfoolable = integrity + completeness, anchored.

`R3Attested` is the precise "unfoolable whole history anchored at `anchoredHead`", using the aggregation
theorem's own conclusion vocabulary:
  * `integrity` — every turn executed correctly per the verified executor (`AggregateAttests.every_turn`);
  * `complete`  — the chain is correctly ordered, nothing dropped/inserted/reordered
    (`AggregateAttests.ordered`, `ChainBound`); and
  * `anchored_is_genuine_fold` — the R1-anchored head IS the genuine fold of THIS whole history
    (`anchoredHead = foldedFinalRoot g steps`), the binding that pins the sound history to the grain. -/

/-- **`R3Attested`** — the unfoolable-whole-history verdict for a grain anchored at `anchoredHead`. -/
structure R3Attested (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (anchoredHead : ℤ) : Prop where
  /-- INTEGRITY: every turn in the history executed correctly per the verified executor. -/
  integrity : ∀ s ∈ steps, recCexec s.pre s.turn = some s.post
  /-- COMPLETENESS: the chain is correctly ordered — no host fabrication (no drop/insert/reorder). -/
  complete : ChainBound CH RH cmb compress compressN steps
  /-- ANCHORING: the R1-anchored head IS the genuine fold of THIS whole history — so the sound history
  is about THIS grain's THIS head, not a swapped one. -/
  anchored_is_genuine_fold :
    anchoredHead = foldedFinalRoot CH RH cmb compress compressN g steps

/-- **`r3_unfoolable` (THE R3 HEADLINE).** If `r3VerifyCore` accepts — the whole-chain aggregate verified
(`verify agg.root`, the STARK verifier's status) AND the aggregate's committed head equals the R1-anchored
head — then the whole history behind `anchoredHead` is `R3Attested`: execution-integrity-sound AND complete
(correctly ordered, no fabrication), with the anchored head pinned to its genuine fold. A lying host cannot
serve a fabricated/truncated history under this head.

COMPOSITION: `light_client_verifies_whole_history` (the whole-chain aggregation headline) delivers
`AggregateAttests` from `verify agg.root = true` — its `every_turn` is integrity, its `ordered` is
completeness, its `final_is_genuine_fold` pins `agg.finalRoot` to the genuine fold. The HEAD BINDING
`agg.finalRoot = anchoredHead` (the `== ` decision) then rewrites that pin onto `anchoredHead`. No step is
re-derived; the load-bearing recursion soundness is the SAME `es : EngineSound` hypothesis, carried through
unchanged — no new axiom, no `def …Hard`. -/
theorem r3_unfoolable
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) (anchoredHead : ℤ)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (h : r3VerifyCore (verify agg.root) agg.finalRoot anchoredHead = true) :
    R3Attested Proof CH RH cmb compress compressN agg g steps anchoredHead := by
  obtain ⟨hroot, hhead⟩ := r3VerifyCore_true h
  have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
    agg g steps es hroot
  exact
    { integrity := hatt.every_turn
    , complete := hatt.ordered
    , anchored_is_genuine_fold := by rw [← hhead]; exact hatt.final_is_genuine_fold }

/-! ## 3. THE HEAD-BINDING ANTI-GHOST TOOTH — a swapped/wrong head is REJECTED.

R3's addition over the aggregation headline is meaningful only if a valid aggregate for history A cannot
be accepted against a DIFFERENT grain's anchored head. The tooth: if the aggregate's committed head differs
from the R1-anchored head, `r3VerifyCore` is `false` regardless of the aggregate's verified-status. So a
lying host cannot re-point a genuinely-verified whole-history proof at a head it did not fold to. -/

/-- **`r3_head_mismatch_rejected` (THE ANTI-GHOST TOOTH).** When the aggregate's committed head differs
from the anchored head, R3 REJECTS — the head-binding `== ` fails, `&&` short-circuits to `false`, no
matter the verified-status `v`. This is the tooth that makes the anchoring load-bearing: a whole-history
proof cannot be swapped onto a foreign anchor. -/
theorem r3_head_mismatch_rejected (v : Bool) (aggHead anchHead : ℤ) (hne : aggHead ≠ anchHead) :
    r3VerifyCore v aggHead anchHead = false := by
  unfold r3VerifyCore
  have hb : (aggHead == anchHead) = false := by
    simp only [beq_eq_false_iff_ne]; exact hne
  rw [hb, Bool.and_false]

/-! ## 4. The `@[export]` FFI entry (Rust → Lean), running the verified executable core. -/

/-- **FFI entry** (Rust→`grain-verify`→Lean): space-separated ints `"aggregateVerified aggregateHead
anchoredHead"` — `aggregateVerified` nonzero = the STARK verifier accepted the whole-chain proof — → the
extracted `r3VerifyCore` as `"1"` (accept) / `"0"` (reject). Runs the VERIFIED Lean R3 decision as native
code, the "Lean is the runtime" shape shared with `dregg_fips204_verify` / `dregg_storage_content_root`.
Malformed input (not three ints) fails CLOSED (`"0"`). -/
@[export dregg_grain_r3_verify]
def r3VerifyFFI (input : String) : String :=
  match (input.splitOn " ").filterMap String.toInt? with
  | [av, aggHead, anchHead] => if r3VerifyCore (av != 0) aggHead anchHead then "1" else "0"
  | _ => "0"

end Verify

/-! ## 5. NON-VACUITY — R3 FIRES on a real chain, and the head tooth BITES.

The headline would be hollow if `r3VerifyCore` could not accept a real verified history, or if the head
binding were vacuous. We reuse `RecursiveAggregation`'s realizing instance (`realAggregate` over the honest
1-step `realSteps` from `teethGenesis`, whose `real_engine_sound` witnesses the aggregation legs) and
anchor at its GENUINE head `realAggregate.finalRoot`:
  * **positive** — `r3_fires_on_real_chain` concludes a real `R3Attested` (integrity + completeness +
    anchoring) on the honest history;
  * **negative** — `r3_wrong_head_rejected` shows a WRONG anchor (genuine head + 1) is REJECTED by
    `r3VerifyCore`, so the head binding is a REAL discriminator (satisfiable AND refutable), not a vacuous
    conjunct. -/

section Realize

open Dregg2.Circuit.RecursiveAggregation
  (RealProof acceptAll zCH zRH zcmb zcompress zcompressN realAggregate realSteps real_engine_sound)
open Dregg2.Exec.ConsensusExec (teethGenesis)

/-- **`r3_fires_on_real_chain` (non-vacuity, POSITIVE).** On the realizing instance, anchoring at the
GENUINE head (`realAggregate.finalRoot`) fires R3: `r3VerifyCore` accepts (the accepting verifier + the
head equal to itself), and `r3_unfoolable` delivers a real `R3Attested` over the honest 1-step history —
so the headline is not an empty implication. -/
theorem r3_fires_on_real_chain :
    R3Attested RealProof zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps realAggregate.finalRoot :=
  r3_unfoolable RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps realAggregate.finalRoot real_engine_sound
    (by simp [r3VerifyCore, acceptAll])

/-- **`r3_real_chain_turn_executed` (the attestation is REAL).** Reading R3's conclusion on the witnessed
instance: the (only) turn of the honest history executed — `recCexec teethGenesis honestTurn = some _`. So
R3's verdict is a TRUE fact about a real executor run, not a formal husk. -/
theorem r3_real_chain_turn_executed :
    recCexec teethGenesis Dregg2.Exec.ConsensusExec.honestTurn
      = some Dregg2.Distributed.HistoryAggregation.honestStep.post := by
  have h := r3_fires_on_real_chain.integrity
              Dregg2.Distributed.HistoryAggregation.honestStep (by simp [realSteps])
  simpa [Dregg2.Distributed.HistoryAggregation.honestStep] using h

/-- **`r3_wrong_head_rejected` (non-vacuity, NEGATIVE — the head tooth BITES).** A WRONG anchored head
(the genuine head + 1, which differs) makes `r3VerifyCore` REJECT on the realizing instance — the
head-binding tooth is a real discriminator, so a whole-history proof cannot be re-pointed at a foreign
anchor. -/
theorem r3_wrong_head_rejected :
    r3VerifyCore (acceptAll realAggregate.root) realAggregate.finalRoot
      (realAggregate.finalRoot + 1) = false :=
  r3_head_mismatch_rejected (acceptAll realAggregate.root) realAggregate.finalRoot
    (realAggregate.finalRoot + 1) (by omega)

/-! The FFI entry reflects the core on the wire: an accepting whole-chain status (`1`) with matching heads
ACCEPTS (`"1"`); a mismatched anchored head REJECTS (`"0"`); a non-accepting status (`0`) REJECTS; malformed
input fails closed (`"0"`). -/
#guard r3VerifyFFI "1 42 42" = "1"
#guard r3VerifyFFI "1 42 43" = "0"
#guard r3VerifyFFI "0 42 42" = "0"
#guard r3VerifyFFI "garbage" = "0"

end Realize

/-! ## 6. Axiom hygiene. -/

#assert_axioms Dregg2.Grain.R3Verify.r3VerifyCore_true
#assert_axioms Dregg2.Grain.R3Verify.r3_unfoolable
#assert_axioms Dregg2.Grain.R3Verify.r3_head_mismatch_rejected
#assert_axioms Dregg2.Grain.R3Verify.r3_fires_on_real_chain
#assert_axioms Dregg2.Grain.R3Verify.r3_real_chain_turn_executed
#assert_axioms Dregg2.Grain.R3Verify.r3_wrong_head_rejected

end Dregg2.Grain.R3Verify
