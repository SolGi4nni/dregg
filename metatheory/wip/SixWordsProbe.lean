/-
SixWordsProbe — the six words the published step statement does not carry, DERIVED.

    cd metatheory && LEAN_PATH=$(lake env printenv LEAN_PATH) lean --run wip/SixWordsProbe.lean

Prints, for each of packed statement words 27, 28, 37, 54, 55, 56:

  * what the published `STEP_PUBLIC_IN` carries there, and at which x_hat entries;
  * what the wrap circuit DERIVES for it;
  * and, for the three deferred words, whether that derivation agrees with the
    `FIN_DEFERRED_*` constants `KimchiWrapMainField` already commits to — the
    "a new derivation must agree with the thing it replaces" check.

This is a MEASUREMENT, not a gate. The named theorems are in `KimchiWrapMainField`.
-/
import Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiWrapMainField

set_option maxRecDepth 1000000

def show6 (w : Nat) (have_ derived : Nat) : IO Unit := do
  IO.println s!"  word {w} @ entry {xhatEntryOf w}"
  IO.println s!"      published : {have_}"
  IO.println s!"      derived   : {derived}"
  IO.println s!"      agree     : {have_ == derived}"

def main : IO Unit := do
  IO.println "== the six words, published vs derived =="
  -- Stratum 1 — the two wrap-hack digests. These read `whOldChals` (a `wrapFixtureQ`)
  -- and `STEP_PREVCOMM_XY` (a RECURSION-CHALLENGE commitment, an INPUT to the step
  -- prover, not an output), so they are stable under re-proving the step circuit.
  let d0 := whPrevDigest 0
  let d1 := whPrevDigest 1
  show6 (PREV_MSG_NEXT_STEP + 1) (prevWordVal (PREV_MSG_NEXT_STEP + 1)) d0
  show6 (PREV_MSG_NEXT_STEP + 2) (prevWordVal (PREV_MSG_NEXT_STEP + 2)) d1
  -- Stratum 2 — the three deferred words, at the constants the tree already commits to.
  show6 (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK)
    (prevWordVal (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK)) FIN_DEFERRED_CIP
  show6 (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 1)
    (prevWordVal (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 1)) FIN_DEFERRED_B
  show6 (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 10)
    (prevWordVal (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 10)) FIN_DEFERRED_XI
  -- Stratum 0 — word 54 is derived by NOTHING; the wrap reads it and exposes it at
  -- Mina slot 12. Printed so the asymmetry is visible rather than assumed.
  IO.println s!"  word {PREV_MSG_NEXT_STEP} @ entry {xhatEntryOf PREV_MSG_NEXT_STEP}"
  IO.println s!"      published : {prevWordVal PREV_MSG_NEXT_STEP}  (derived by nothing — \
the wrap reads it and exposes it at Mina slot 12)"
  IO.println ""
  IO.println "== the entries a repair must write =="
  let put : Nat → Nat → IO Unit := fun w v => do
    let i := xhatEntryOf w
    if xhatIsSplitHi i then
      IO.println s!"  entry {i} := {v / 2}   entry {i + 1} := {v % 2}   (word {w}, split `Field`)"
    else
      IO.println s!"  entry {i} := {v}   (word {w})"
  put (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK) FIN_DEFERRED_CIP
  put (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 1) FIN_DEFERRED_B
  put (PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 10) FIN_DEFERRED_XI
  put (PREV_MSG_NEXT_STEP + 1) d0
  put (PREV_MSG_NEXT_STEP + 2) d1
