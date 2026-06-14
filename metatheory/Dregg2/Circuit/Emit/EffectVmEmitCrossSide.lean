/-
# `EffectVmEmitCrossSide` — the CROSS-SIDE EXISTENCE AIR (CG-5), emitted from Lean (law #1).

The bilateral-bundle aggregation's CG-5 leg (`circuit/src/bilateral_aggregation_air.rs::
CrossSideExistenceAir`) is the algebraic "no missing peer" enforcement: every directed bilateral
edge the canonical Turn schedule predicts is materialised as TWO half-edge rows — an OUTGOING
half (claimed by `from`, sign +1) and an INCOMING half (claimed by `to`, sign −1) — each carrying
the SAME direction-independent fingerprint `edge_fp = Poseidon2(edge_id)`. A running signed
balance `balance[i] = balance[i-1] + sign[i]·fp[i]` is pinned to ZERO at the last row: a matched
pair cancels (`+fp` and `−fp`), so a surviving uncancelled term (a missing peer) breaks the
boundary unless two distinct edge ids COLLIDE under Poseidon2.

Until now that AIR was HAND-AUTHORED Rust (a `StarkAir` impl, AIR name
`dregg-cross-side-existence-v1`). It reads NO `effect_vm::pi`, so there is no v1-PI coupling to
unwind — only the move under law #1. THIS module is that emission.

## The trace↔proof binding (why this descriptor carries a PUBLIC INPUT the hand-AIR didn't).

The hand-`StarkAir` bound its (empty-PI) proof to the shipped trace EXPLICITLY, via
`recompute_trace_commitment(air, trace) == proof.trace_commitment`. The IR-v2 batch verifier
(`verify_vm_descriptor2`) takes only `(descriptor, proof, public_inputs)` — it does NOT re-bind a
caller-supplied trace, so an empty-PI descriptor would attest only "SOME balanced trace exists",
not "the CANONICAL edge multiset balances". To preserve the hand-AIR's guarantee without an
explicit-commitment API, this descriptor binds the canonical edge SEQUENCE into a PUBLIC INPUT: a
rolling Poseidon2 commitment `commit[i] = Poseidon2(commit[i-1], edge_fp[i])` over the (ordered)
per-row fingerprints, seeded at `pi[commit_seed]` and pinned at the last row to `pi[edge_commit]`.
The off-AIR verifier RE-DERIVES `pi[edge_commit]` from the canonical Turn edges (the same
`build_cross_side_trace` order) and passes it in; a proof over any other edge multiset has a
different `commit[last]` and is rejected (barring a Poseidon2 collision). This is the IR-v2 analog
of the main-aggregation pattern (the trace is pinned to a verifier-derived PI), at the same
soundness as the retired `recompute_trace_commitment` binding.

## The constraint families (mirrors the Rust AIR, now law-#1, and STRONGER)

* **The fingerprint is REAL** (a chip lookup): `edge_fp = Poseidon2(edge_id)` as an arity-4 chip
  lookup `(4, edge_id padded to CHIP_RATE, edge_fp)`. The deployed chip table realizes the
  permutation with the arity tag at state[4] — byte-identical to `circuit/src/poseidon2.rs::
  hash_4_to_1` (state[0..4] = inputs, state[4] = 4). STRICTLY STRONGER than the hand-AIR, which
  never constrained `edge_fp` in-circuit.
* **The commitment is REAL** (a chip lookup): `commit[i] = Poseidon2(commit_in[i], edge_fp[i])` as
  an arity-2 chip lookup, with `commit_in[i] = commit[i-1]` carried by a `windowGate` continuity
  (seeded `commit_in[0] = pi[commit_seed]` and pinned `commit[last] = pi[edge_commit]`). This is
  the edge-sequence binding above.
* **Booleans + padding**: `present ∈ {0,1}`; on padding rows (`present = 0`) the balance
  contribution vanishes via `present·(sign² − 1) = 0` ∧ `(1 − present)·sign = 0` (so `sign·fp` is
  `0·fp = 0` regardless of the fingerprint). → per-row `gate`s.
* **The balance prefix sum**: seed `balance[0] = sign[0]·fp[0]` (a first-row `boundary`); the
  transition `balance[i+1] = balance[i] + sign[i+1]·fp[i+1]` (a two-row `windowGate`).
* **The boundary**: `balance[last] = 0` (the whole bundle balances — the missing-peer detector).

## The teeth (soundness, proved below)

`cse_rejects_unbalanced` (a last row whose `balance ≠ 0` is UNSAT — the missing-peer rejection the
Rust `cross_side_missing_peer_does_not_balance` gauntlet drives), `cse_rejects_wrong_commit` (a
last row whose `commit ≠ pi[edge_commit]` is UNSAT — the edge-sequence binding), and
`cse_fingerprint_is_hashed` (against a sound chip table the fingerprint column IS the genuine
Poseidon2 of the edge id — the in-circuit strengthening the hand-AIR lacked), axiom-clean.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Tactics

namespace Dregg2.Circuit.Emit.EffectVmEmitCrossSide

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — The cross-side-existence trace + PI layout (mirrors the Rust `CSE_*` constants). -/
namespace Cse

/-- Canonical 4-felt edge id, base offset. -/
def EDGE_ID_BASE : Nat := 0
def EDGE_ID_LEN : Nat := 4
/-- Poseidon2 fingerprint of the edge id. -/
def EDGE_FP_COL : Nat := EDGE_ID_BASE + EDGE_ID_LEN
/-- Edge direction sign (+1 outgoing / −1 incoming). -/
def SIGN_COL : Nat := EDGE_FP_COL + 1
/-- 1 for a real half-edge row, 0 for padding. -/
def PRESENT_COL : Nat := SIGN_COL + 1
/-- Running balance prefix sum (this row inclusive). -/
def BALANCE_COL : Nat := PRESENT_COL + 1
/-- The rolling edge-sequence commitment BEFORE absorbing this row (= previous row's `commit`). -/
def COMMIT_IN_COL : Nat := BALANCE_COL + 1
/-- The rolling edge-sequence commitment AFTER absorbing this row's fingerprint. -/
def COMMIT_COL : Nat := COMMIT_IN_COL + 1
/-- Total trace width. -/
def WIDTH : Nat := COMMIT_COL + 1

/-- Public input: the commitment seed (`commit_in[0]`). -/
def PI_COMMIT_SEED : Nat := 0
/-- Public input: the final edge-sequence commitment (`commit[last]`). -/
def PI_EDGE_COMMIT : Nat := 1
/-- Public input count. -/
def PI_COUNT : Nat := 2

end Cse

/-! ## §2 — Constraint builders (as `VmConstraint2`).

`loc`/`nxt` are the two-row `WindowExpr` leaves; the single-row gates use `EmittedExpr`. -/

open WindowExpr (loc nxt)

/-- A boolean gate `local[c] ∈ {0,1}` (`c·(c-1) = 0`). -/
def boolGate (c : Nat) : VmConstraint2 :=
  .base (.gate (.mul (.var c) (.add (.var c) (.const (-1)))))

/-- The chip lookup pinning `edge_fp = Poseidon2(edge_id)` — an arity-4 absorb of the four
`edge_id` columns into the `EDGE_FP_COL` digest. (`chipLookupTuple` renders `(4, ins padded to
CHIP_RATE, digestCol)`; the deployed chip table is the REAL permutation with the arity tag at
state[4], byte-identical to `hash_4_to_1`.) -/
def fingerprintLookup : VmConstraint2 :=
  .lookup
    { table := .poseidon2
    , tuple := chipLookupTuple
        [.var (Cse.EDGE_ID_BASE + 0), .var (Cse.EDGE_ID_BASE + 1),
         .var (Cse.EDGE_ID_BASE + 2), .var (Cse.EDGE_ID_BASE + 3)]
        Cse.EDGE_FP_COL }

/-- The chip lookup pinning `commit = Poseidon2(commit_in, edge_fp)` — an arity-2 absorb folding
this row's fingerprint into the rolling edge-sequence commitment. -/
def commitLookup : VmConstraint2 :=
  .lookup
    { table := .poseidon2
    , tuple := chipLookupTuple [.var Cse.COMMIT_IN_COL, .var Cse.EDGE_FP_COL] Cse.COMMIT_COL }

/-- `present·(sign² − 1) = 0` (a real half-edge has `sign ∈ {+1,−1}`). -/
def signSquareGate : VmConstraint2 :=
  .base (.gate (.mul (.var Cse.PRESENT_COL)
                     (.add (.mul (.var Cse.SIGN_COL) (.var Cse.SIGN_COL)) (.const (-1)))))

/-- `(1 − present)·sign = 0` (a padding row carries `sign = 0`, so its `sign·fp` contribution is 0
regardless of the genuine-hash fingerprint the chip lookup forces on padding rows). -/
def paddingSignGate : VmConstraint2 :=
  .base (.gate (.mul (.add (.const 1) (.mul (.const (-1)) (.var Cse.PRESENT_COL)))
                     (.var Cse.SIGN_COL)))

/-- First-row balance seed `balance[0] = sign[0]·fp[0]` (`balance − sign·fp = 0` on the first row). -/
def firstBalanceSeed : VmConstraint2 :=
  .base (.boundary .first
    (.add (.var Cse.BALANCE_COL)
          (.mul (.const (-1)) (.mul (.var Cse.SIGN_COL) (.var Cse.EDGE_FP_COL)))))

/-- The balance transition `balance[i+1] = balance[i] + sign[i+1]·fp[i+1]` as a `windowGate`:
`next[bal] − local[bal] − next[sign]·next[fp] = 0`. -/
def balanceTransition : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body :=
        .add (nxt Cse.BALANCE_COL)
          (.add (.mul (.const (-1)) (loc Cse.BALANCE_COL))
                (.mul (.const (-1)) (.mul (nxt Cse.SIGN_COL) (nxt Cse.EDGE_FP_COL)))) }

/-- Last-row boundary `balance[last] = 0` (the whole bundle balances — the missing-peer detector). -/
def lastBalanceZero : VmConstraint2 :=
  .base (.boundary .last (.var Cse.BALANCE_COL))

/-- First-row commitment seed `commit_in[0] = pi[commit_seed]`. -/
def firstCommitSeed : VmConstraint2 :=
  .base (.piBinding .first Cse.COMMIT_IN_COL Cse.PI_COMMIT_SEED)

/-- The commitment continuity `commit_in[i+1] = commit[i]` as a `windowGate`:
`next[commit_in] − local[commit] = 0`. -/
def commitContinuity : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body := .add (nxt Cse.COMMIT_IN_COL) (.mul (.const (-1)) (loc Cse.COMMIT_COL)) }

/-- Last-row boundary `commit[last] = pi[edge_commit]` (the edge-sequence binding). -/
def lastCommitEqPi : VmConstraint2 :=
  .base (.piBinding .last Cse.COMMIT_COL Cse.PI_EDGE_COMMIT)

/-! ## §3 — Assemble the cross-side-existence descriptor. -/

/-- The full constraint list of the cross-side-existence AIR. -/
def cseConstraints : List VmConstraint2 :=
  [ boolGate Cse.PRESENT_COL
  , signSquareGate
  , paddingSignGate
  , fingerprintLookup
  , commitLookup
  , firstBalanceSeed
  , balanceTransition
  , lastBalanceZero
  , firstCommitSeed
  , commitContinuity
  , lastCommitEqPi ]

/-- The cross-side-existence descriptor: width 10, public inputs `(commit_seed, edge_commit)`
binding the canonical edge sequence, ONE declared table — the Poseidon2 chip the fingerprint +
commitment lookups ride. -/
def crossSideDescriptor : EffectVmDescriptor2 :=
  { name        := "dregg-cross-side-existence-v2"
  , traceWidth  := Cse.WIDTH
  , piCount     := Cse.PI_COUNT
  , tables      := [poseidon2ChipTableDef]
  , constraints := cseConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — Shape tripwires (byte-pinned both sides; the Rust twin pins the same). -/

-- The trace is 10 columns: edge_id 4 + fp 1 + sign 1 + present 1 + balance 1 + commit_in 1 + commit 1.
#guard Cse.WIDTH == 10
-- Two public inputs: the commitment seed + the final edge-sequence commitment.
#guard crossSideDescriptor.piCount == 2
-- 11 constraints: 3 row-local gates (present-bool, sign², padding-sign) + 2 chip lookups
-- (fingerprint, commitment) + 2 boundaries (balance seed, balance==0) + 2 piBindings (commit seed,
-- commit==pi) + 2 window gates (balance transition, commit continuity).
#guard cseConstraints.length == 11
-- Exactly two window gates (the balance prefix-sum + the commitment continuity).
#guard (cseConstraints.filter (fun c => match c with | .windowGate _ => true | _ => false)).length == 2
-- Exactly two chip lookups (the fingerprint arity-4 + the commitment arity-2).
#guard (cseConstraints.filter (fun c => match c with | .lookup _ => true | _ => false)).length == 2
-- The descriptor emits a versioned v2 wire string.
#guard (emitVmJson2 crossSideDescriptor).startsWith "{\"name\":\"dregg-cross-side-existence-v2\",\"ir\":2"

/-! ## §5 — The teeth (soundness): the missing-peer + edge-binding rejections + the real-fingerprint.

A row-window satisfies the descriptor iff every constraint holds on it (with the chip table as the
`TraceFamily`). -/

/-- The descriptor's per-window denotation against a chip `TraceFamily` and a hash. -/
def cseWindowHolds (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ crossSideDescriptor.constraints, c.holdsAt hash tf env isFirst isLast

/-- **The missing-peer tooth.** A LAST row whose running `balance` is not 0 cannot satisfy the
descriptor — exactly the boundary that detects an uncancelled (missing-peer) half-edge. -/
theorem cse_rejects_unbalanced
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hbad : env.loc Cse.BALANCE_COL ≠ 0) :
    ¬ cseWindowHolds hash tf env false true := by
  intro h
  have hmem : lastBalanceZero ∈ crossSideDescriptor.constraints := by
    show _ ∈ cseConstraints
    simp [cseConstraints]
  have hc := h _ hmem
  simp only [lastBalanceZero, VmConstraint2.holdsAt, VmConstraint.holdsVm, EmittedExpr.eval] at hc
  exact hbad (hc trivial)

/-- **The edge-binding tooth.** A LAST row whose rolling `commit` disagrees with the published
`pi[edge_commit]` cannot satisfy the descriptor — this is the binding that ties the proven trace
to the verifier-derived canonical edge sequence (replacing the hand-AIR's
`recompute_trace_commitment` binding). -/
theorem cse_rejects_wrong_commit
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hbad : env.loc Cse.COMMIT_COL ≠ env.pub Cse.PI_EDGE_COMMIT) :
    ¬ cseWindowHolds hash tf env false true := by
  intro h
  have hmem : lastCommitEqPi ∈ crossSideDescriptor.constraints := by
    show _ ∈ cseConstraints
    simp [cseConstraints]
  have hc := h _ hmem
  simp only [lastCommitEqPi, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  exact hbad (hc trivial)

/-- **The real-fingerprint tooth (in-circuit strengthening over the hand-AIR).** Against a SOUND
chip table, the descriptor's fingerprint lookup ENFORCES `edge_fp = Poseidon2(edge_id)`: the
fingerprint column is the genuine hash of the four edge-id columns, not a prover-chosen value. The
hand-`StarkAir` never constrained this in-circuit. -/
theorem cse_fingerprint_is_hashed
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (hSound : ChipTableSound hash (tf .poseidon2))
    (h : cseWindowHolds hash tf env isFirst isLast) :
    env.loc Cse.EDGE_FP_COL
      = hash [env.loc (Cse.EDGE_ID_BASE + 0), env.loc (Cse.EDGE_ID_BASE + 1),
              env.loc (Cse.EDGE_ID_BASE + 2), env.loc (Cse.EDGE_ID_BASE + 3)] := by
  have hmem : fingerprintLookup ∈ crossSideDescriptor.constraints := by
    show _ ∈ cseConstraints
    simp [cseConstraints]
  have hc := h _ hmem
  simp only [fingerprintLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
  have hkey := chip_lookup_sound hash (tf .poseidon2) hSound env.loc
    [.var (Cse.EDGE_ID_BASE + 0), .var (Cse.EDGE_ID_BASE + 1),
     .var (Cse.EDGE_ID_BASE + 2), .var (Cse.EDGE_ID_BASE + 3)]
    Cse.EDGE_FP_COL (by unfold CHIP_RATE; decide) hc
  simpa [EmittedExpr.eval] using hkey

#assert_axioms cse_rejects_unbalanced
#assert_axioms cse_rejects_wrong_commit
#assert_axioms cse_fingerprint_is_hashed

end Dregg2.Circuit.Emit.EffectVmEmitCrossSide
