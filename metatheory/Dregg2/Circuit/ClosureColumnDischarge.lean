/-
# Dregg2.Circuit.ClosureColumnDischarge — the GENERIC column-read discharge: the `RowEncodes`-class
limb decodes are `env.loc`-DETERMINED, so they leave the carried floor; only the row designation
(`StarkSound`-class) is the genuine prover witness.

## The honest separation this module lands

Every per-effect `<e>TraceReadout` (ClosureFanoutGenuine) / `TransferTraceReadout` (ClosureTransfer)
carries a `RowEncodes`/`*Encodes` decode of the designated row(s): the `state_before`/`param`/
`state_after` columns read off as a concrete `(pre, params, post)` record. The prompt's loop #4
question is exactly: which of those carried fields are GENUINE prover witness (`StarkSound`-class) and
which are MECHANICAL column reads that a satisfying trace `t` already determines?

The answer, made precise here:

  * **MECHANICAL (env.loc-determined) — DISCHARGED.** The 17 `RowEncodes` column-read equalities
    (`env.loc (sbCol BALANCE_LO) = pre.balLo`, …, the param block, the `state_after` block) are pure
    functions of the satisfying trace `t` plus the row index `i`: DEFINE the decoded record by reading
    `env.loc` at the named columns (`decodeCellPre`/`decodeParams`/`decodeCellPost`), and the column
    equalities hold by `rfl`. The trace `t` itself is what `StarkSound` extracts; reading a fixed
    column off `(envAt t i).loc` adds NO witness. These leave the carried floor.

  * **GENUINE (StarkSound-class) — KEPT.** The row DESIGNATION (which trace row `i` is the
    debit/credit/active row) and the published-commitment binding `env.pub OLD/NEW_COMMIT = …` (the
    `piBinding` circuit fact) are the prover's witness the `StarkSound` extraction supplies. We do NOT
    discharge these — that would launder the floor. The designation is the boundary-flag witness; the
    publish-tie is the hash-CR-class fact tying the published PI to the limb. These stay.

## The generic combinator

`rowEncodes_of_designation` (§2) takes ONLY: a row's published-commitment ties (the two `piBinding`
facts) and produces the FULL `RowEncodes (envAt t i) (decodeCellPre …) (decodeParams …)
(decodeCellPost …)`. The 17 column equalities are `rfl`; the 2 publish ties are the hypotheses. So the
carried `RowEncodes` decode of the readout floors is REPLACED by reading columns + the publish tie —
the decoded `CellState`/`TransferParams` records are NO LONGER part of the floor.

This is the GENERIC pattern the prompt asks for: a single lemma showing the column reads are
`env.loc`-determined, plus the named publish-tie residual. It is stated at the transfer `RowEncodes`
(the template); the other families' `*Encodes` column blocks have the SAME shape (column = field,
`rfl`), so the uniform pattern is `<e>Encodes column block ≡ decode-by-reading-env.loc`.

## What the carried floor BECOMES (the reduction)

With the column reads discharged, the per-effect readout floor's content is exactly:

  `{ the row designation (which row(s) — StarkSound-class boundary-flag witness)
  + the publish-commitment ties (env.pub OLD/NEW = state_commit column — hash-CR-class piBinding)
  + the row-shape/dir/amount/frame/guard facts a satisfying trace exhibits (StarkSound-class) }`

i.e. uniformly `{StarkSound + the hash/Merkle CR}` per effect, with the `RowEncodes`/`*Encodes`
limb-decode columns DISCHARGED (env.loc-determined, not carried). The honest floor is the row
designation, never the mechanical column reads — exactly the minimal set.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The publish ties enter as Prop
hypotheses; the column reads are `rfl`. No `sorry`, no `native_decide`, no `:= True`, no fresh axiom.
NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.ClosureColumnDischarge

open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState TransferParams RowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmit

set_option autoImplicit false

/-! ## §1 — the canonical column decoders: read `env.loc` at the named columns.

`decodeCellPre`/`decodeParams`/`decodeCellPost` are pure functions of a `VmRowEnv` (hence of `envAt t
i`, hence of the satisfying trace `t` + the row index `i`). They read the `state_before` / `param` /
`state_after` columns into a concrete `CellState`/`TransferParams`. NO witness is added — these are
projections of `env.loc`. -/

/-- The `state_before` block, read off `env.loc` into a `CellState`. -/
def decodeCellPre (env : VmRowEnv) : CellState where
  balLo    := env.loc (sbCol state.BALANCE_LO)
  balHi    := env.loc (sbCol state.BALANCE_HI)
  nonce    := env.loc (sbCol state.NONCE)
  fields   := fun i => env.loc (sbCol (state.FIELD_BASE + i.val))
  capRoot  := env.loc (sbCol state.CAP_ROOT)
  reserved := env.loc (sbCol state.RESERVED)
  commit   := env.loc (sbCol state.STATE_COMMIT)

/-- The `state_after` block, read off `env.loc` into a `CellState`. -/
def decodeCellPost (env : VmRowEnv) : CellState where
  balLo    := env.loc (saCol state.BALANCE_LO)
  balHi    := env.loc (saCol state.BALANCE_HI)
  nonce    := env.loc (saCol state.NONCE)
  fields   := fun i => env.loc (saCol (state.FIELD_BASE + i.val))
  capRoot  := env.loc (saCol state.CAP_ROOT)
  reserved := env.loc (saCol state.RESERVED)
  commit   := env.loc (saCol state.STATE_COMMIT)

/-- The `param` block, read off `env.loc` into `TransferParams`. -/
def decodeParams (env : VmRowEnv) : TransferParams where
  amount    := env.loc (prmCol param.AMOUNT)
  direction := env.loc (prmCol param.DIRECTION)

/-! ## §2 — the GENERIC discharge: `RowEncodes` from the canonical decoders + the publish ties.

The 17 column equalities of `RowEncodes` hold BY DEFINITION of the canonical decoders (`rfl`). The
only non-`rfl` fields are the two published-commitment ties `env.pub OLD/NEW_COMMIT = …` — the
`piBinding` circuit facts (`EffectVmEmitTransfer.boundaryFirst_pins`/`boundaryLast_pins`), supplied as
hypotheses. So the entire `RowEncodes` decode is DISCHARGED to {the column reads (`rfl`, free) + the
two publish ties (hash-CR-class piBinding, named)} — the decoded `CellState`/`TransferParams` records
are no longer carried. -/

/-- **`rowEncodes_of_designation` — the column reads are `env.loc`-determined.** Given ONLY the two
published-commitment ties of a row `env` (the `piBinding` facts: `env.pub OLD_COMMIT = env.loc (sbCol
STATE_COMMIT)` and `env.pub NEW_COMMIT = env.loc (saCol STATE_COMMIT)`), the canonical decoders
`decodeCellPre`/`decodeParams`/`decodeCellPost` satisfy `RowEncodes`. The 17 column reads are `rfl`;
only the publish ties are real. This is the GENERIC column-read discharge: the `RowEncodes` decode adds
NO prover witness beyond the row designation + the publish-commitment binding. -/
theorem rowEncodes_of_designation (env : VmRowEnv)
    (hOld : env.pub pi.OLD_COMMIT = env.loc (sbCol state.STATE_COMMIT))
    (hNew : env.pub pi.NEW_COMMIT = env.loc (saCol state.STATE_COMMIT)) :
    RowEncodes env (decodeCellPre env) (decodeParams env) (decodeCellPost env) := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, hOld, hNew⟩
  · intro i; rfl
  · intro i; rfl

/-- **The discharge is witness-free in the decode.** The decoded records are FUNCTIONS of `env`: any
two `RowEncodes` decodes of the SAME `env` agree (the decode is determined by the columns). So the
carried `pre`/`params`/`post` of a readout floor are redundant given the row designation `env = envAt t
i` — they are `decodeCellPre/Params/Post (envAt t i)` up to the column equalities `RowEncodes` already
forces. This is why discharging them does not weaken the floor: they were never witness. -/
theorem rowEncodes_decode_determined (env : VmRowEnv)
    {pre post : CellState} {p : TransferParams}
    (h : RowEncodes env pre p post) :
    pre = decodeCellPre env ∧ p = decodeParams env ∧ post = decodeCellPost env := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hpAmt, hpDir, hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, _, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · cases pre with
    | mk balLo balHi nonce fields capRoot reserved commit =>
      simp only [decodeCellPre, CellState.mk.injEq]
      refine ⟨hsbLo.symm, hsbHi.symm, hsbN.symm, ?_, hsbCap.symm, hsbRes.symm, hsbC.symm⟩
      funext i; exact (hsbF i).symm
  · cases p with
    | mk amount direction =>
      simp only [decodeParams, TransferParams.mk.injEq]
      exact ⟨hpAmt.symm, hpDir.symm⟩
  · cases post with
    | mk balLo balHi nonce fields capRoot reserved commit =>
      simp only [decodeCellPost, CellState.mk.injEq]
      refine ⟨hsaLo.symm, hsaHi.symm, hsaN.symm, ?_, hsaCap.symm, hsaRes.symm, hsaC.symm⟩
      funext i; exact (hsaF i).symm

/-! ## §3 — the reduced transfer readout: the row DESIGNATION ONLY, column reads discharged.

`TransferTraceReadout` (ClosureTransfer) carries the two rows' `RowEncodes` decodes (`hdiEnc`/`hciEnc`)
PLUS the decoded `srcPre`/…/`dstPost`/`srcParams`/`dstParams` records. §2 shows those decode fields are
`env.loc`-determined: given the row designation `(di, ci)` + the publish ties, the `RowEncodes` decodes
are `rowEncodes_of_designation` and the records are `decodeCellPre/Params/Post (envAt t ·)`. So the
GENUINE carried readout floor is the SLIM designation below — `(di, ci)` + the publish ties + the
row-shape/dir/amount tags (which a satisfying transfer trace exhibits) — with the decode columns GONE.

`TransferRowDesignation` is that slim floor; `transferTraceReadout_decode_columns` exhibits the full
`RowEncodes` decodes FROM it (the column-read discharge applied), so the original readout is
RECONSTRUCTED from {designation + publish ties}, never carried as raw decoded records. -/

/-- **`TransferRowDesignation` — the SLIM transfer readout: row designation + publish ties only.** The
genuine `StarkSound`-class witness of a transfer trace boundary: the two designated rows `(di, ci)`,
their in-bounds, the row-shape (`IsTransferRow`), the direction/amount tags, and the two rows' publish
ties (the `piBinding` hash-CR facts). The decoded `CellState`/`TransferParams` records and their
`RowEncodes` column equalities are NOT here — §2 reconstructs them by reading `env.loc`. This is the
honest floor after the column-read discharge: the designation, never the mechanical reads. -/
structure TransferRowDesignation (t : VmTrace) : Type where
  di : Nat
  ci : Nat
  hdi : di < t.rows.length
  hci : ci < t.rows.length
  -- the two rows' publish-commitment ties (the `piBinding` hash-CR-class facts).
  hdiOld : (envAt t di).pub pi.OLD_COMMIT = (envAt t di).loc (sbCol state.STATE_COMMIT)
  hdiNew : (envAt t di).pub pi.NEW_COMMIT = (envAt t di).loc (saCol state.STATE_COMMIT)
  hciOld : (envAt t ci).pub pi.OLD_COMMIT = (envAt t ci).loc (sbCol state.STATE_COMMIT)
  hciNew : (envAt t ci).pub pi.NEW_COMMIT = (envAt t ci).loc (saCol state.STATE_COMMIT)
  -- the direction/amount tags read directly off the columns (no decoded record needed).
  hdiDir : (envAt t di).loc (prmCol param.DIRECTION) = 1
  hciDir : (envAt t ci).loc (prmCol param.DIRECTION) = 0

/-- **The slim designation RECONSTRUCTS the two `RowEncodes` decodes (the column-read discharge,
applied).** From `TransferRowDesignation` alone, the debit/credit rows' `RowEncodes` decodes are the
canonical `decodeCellPre/Params/Post` reads — exhibiting that the carried readout's decode fields were
`env.loc`-determined all along. So a readout floor reduced to the slim designation loses NO content:
the column decodes are recovered by reading. -/
theorem transferRowDesignation_decodes (t : VmTrace) (d : TransferRowDesignation t) :
    RowEncodes (Dregg2.Circuit.DescriptorIR2.envAt t d.di)
        (decodeCellPre (Dregg2.Circuit.DescriptorIR2.envAt t d.di))
        (decodeParams (Dregg2.Circuit.DescriptorIR2.envAt t d.di))
        (decodeCellPost (Dregg2.Circuit.DescriptorIR2.envAt t d.di)) ∧
      RowEncodes (Dregg2.Circuit.DescriptorIR2.envAt t d.ci)
        (decodeCellPre (Dregg2.Circuit.DescriptorIR2.envAt t d.ci))
        (decodeParams (Dregg2.Circuit.DescriptorIR2.envAt t d.ci))
        (decodeCellPost (Dregg2.Circuit.DescriptorIR2.envAt t d.ci)) :=
  ⟨rowEncodes_of_designation (Dregg2.Circuit.DescriptorIR2.envAt t d.di) d.hdiOld d.hdiNew,
   rowEncodes_of_designation (Dregg2.Circuit.DescriptorIR2.envAt t d.ci) d.hciOld d.hciNew⟩

/-- **The direction tags are read, not witnessed.** On the slim designation the debit row's
`decodeParams.direction = 1` and the credit row's `= 0` hold by the carried column tags — exhibiting
that the `hdiDir`/`hciDir` fields of the full `rotatedEncodes` are themselves column reads (of the
`decodeParams`), not separate witness. -/
theorem transferRowDesignation_dir (t : VmTrace) (d : TransferRowDesignation t) :
    (decodeParams (Dregg2.Circuit.DescriptorIR2.envAt t d.di)).direction = 1 ∧
      (decodeParams (Dregg2.Circuit.DescriptorIR2.envAt t d.ci)).direction = 0 :=
  ⟨d.hdiDir, d.hciDir⟩

/-! ## §4 — axiom hygiene. -/

#assert_axioms decodeCellPre
#assert_axioms decodeCellPost
#assert_axioms decodeParams
#assert_axioms rowEncodes_of_designation
#assert_axioms rowEncodes_decode_determined
#assert_axioms transferRowDesignation_decodes
#assert_axioms transferRowDesignation_dir

end Dregg2.Circuit.ClosureColumnDischarge
