/-
`KimchiWrapMain` — ⚑⚑ **THE PROVER-CHOICE CENSUS, WRAP SIDE.**

Companion to `KimchiStepProverChoice`. Same question, same three instruments, different assembly:
**which cells does the prover supply, and does choosing one change what the circuit accepts?**

⚑ NAMED THEOREMS, NOT `#guard`. Its own namespace, so `KimchiWrapMain`'s
`#assert_namespace_axioms` keeps meaning what it means; every theorem here carries `#assert_compiled`.

## ⚑ WHY THE EXISTING COUNT IS THE WRONG UNIT

`WRAP_UNCONSUMED` has **8** entries and `key_closes_one_unconsumed_entry` states it. That list counts
ITEM CLASSES — "sg_old", "w_comm", "lr". A prover does not choose a class; he chooses a **field
element**. Measured here on the emitted schedule at the committed shape: the transcript absorbs
**120 field elements**, and at `w5_key` **119 of them own exactly one permutation cell** — the
sponge's own absorb row and nothing else. At `w6_xhat` the `x_hat` pair becomes the MSM's output, so
the number is **117 of 120**.

⚠ §13's "WHERE FIAT–SHAMIR STANDS" says "THE INPUT IS DERIVED IN ITS FIRST WORD AND NOWHERE ELSE …
⚠ The other nine are not", and then names eight. Eight is the class count and it is one stale (`x_hat`
IS derived since `w6_xhat`, which the §2c entry says at length and this bullet does not). **The
number a prover cares about is 117**, and this module is where it is stated.
-/
import Dregg2.Circuit.Emit.KimchiWrapMain

namespace Dregg2.Circuit.Emit.KimchiWrapProverChoice

open Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder (VarEnv envIxBound)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §W1 — the instruments (this file's own copies, per `§3`'s rule). -/

/-- How many permutation cells `v` owns across a row schedule. -/
def occCount (rows : List WRow) (v : PVar) : Nat :=
  rows.foldl (fun n r => n + (r.perm.take K_PERMUTS).countP (fun o => o == some v)) 0

/-- The wired-variable bitmap, `varIx`-indexed — one pass, so the census is linear in the rows. -/
def wiredIxs (bound : Nat) (rows : List WRow) : Array Bool :=
  rows.foldl (fun a r =>
    (r.perm.take K_PERMUTS).foldl (fun a o =>
      match o with
      | none => a
      | some v => if varIx v < bound then a.set! (varIx v) true else a) a)
    (Array.replicate bound false)

/-- Environment variables no row of the schedule wires. -/
def envVarsNoRowReads (env : VarEnv) (rows : List WRow) : List PVar :=
  let bound := envIxBound env + 1
  let w := wiredIxs bound rows
  ((env.map (·.1)).dedup).filter (fun v => !(w.getD (varIx v) false))

/-- Every absorbed item's own variable, in schedule order. -/
def absorbedWordVars (t : WrapData) : List PVar :=
  (t.sp.evs.filter (fun e => e.isAbs)).map (fun e => e.wordV)

/-- ⚑ The committed instance at `w5_key` — the top rung whose environment does not carry §15's
ladders. `circuitEnvAt` exists for exactly this reason (§7's docblock: folding `xhatEnv` into a
shape-wide env drove the module to a ~10 GB ceiling), so the committed-shape census is stated here
and the `w6_xhat` census at the smoke shape. -/
def tWrap : WrapData := mkWrap shapeWrap
def rowsWrapKey : List WRow := rungRows tWrap .key true
/-- The smoke instance at the TOP rung, where `x_hat` is the MSM's output. -/
def tSm : WrapData := mkWrap shapeSmoke
def rowsSmXhat : List WRow := rungRows tSm .xhat true

/-! ## §W2 — ⚑⚑ THE TRANSCRIPT'S INPUT IS 120 FIELD ELEMENTS AND 119 OF THEM ARE THE PROVER'S. -/

/-- ⚑⚑ **THE HEADLINE.** At the committed shape the schedule absorbs `nItems = 120` field elements;
`absorbedWordVars` has one variable each; and **119 of those variables own exactly one permutation
cell in the whole `w5_key` circuit** — the absorb row. The one that owns more is `index_digest`,
which W-KEY derives (`key_digest_is_the_index_digest`) and whose closing tie puts the squeeze and the
absorb in one σ class.

⚑ This is the number `WRAP_UNCONSUMED`'s 8 abbreviates. A prover choosing any one of the 119 steers
every challenge squeezed after it, and the first of them is item 1 — so **every** challenge in this
assembly is reachable. **(a) forgery surface**, the largest one in either assembly. -/
theorem the_wrap_transcript_absorbs_120_words_and_119_are_supplied :
    ((absorbedWordVars tWrap).length = 120
     ∧ nItems shapeWrap = 120
     ∧ ((absorbedWordVars tWrap).filter
          (fun v => occCount rowsWrapKey v == 1)).length = 119
     ∧ occCount rowsWrapKey ((absorbedWordVars tWrap).headD (.external 0)) = 2) := by
  native_decide
#assert_compiled the_wrap_transcript_absorbs_120_words_and_119_are_supplied

/-- …and at `w6_xhat` exactly two more leave: `wrap_verifier.ml:617`'s absorbed pair IS §15's ladder
output. Stated at the smoke shape, where the top rung is reducible: 34 items, 31 supplied.
⚠ §2c is right that this changes the SHAPE and not the SIZE of the prover's reach — the MSM's 67
scalars are W-PREV's free witnesses — and the entry stays on `WRAP_UNCONSUMED` because of it. -/
theorem the_xhat_rung_derives_two_of_the_absorbed_words :
    ((absorbedWordVars tSm).length = 34
     ∧ nItems shapeSmoke = 34
     ∧ ((absorbedWordVars tSm).filter (fun v => occCount rowsSmXhat v == 1)).length = 31
     ∧ ((absorbedWordVars tSm).filter (fun v => occCount rowsSmXhat v > 1)).length = 3) := by
  native_decide
#assert_compiled the_xhat_rung_derives_two_of_the_absorbed_words

/-- …and the three that are consumed are the ones the two landed rungs derive, by TAG rather than by
position: `T_DIGEST` (one item, W-KEY) and `T_XHAT` (two items, W-XHAT). Every other tag's items own
one cell each. -/
theorem the_consumed_words_are_exactly_the_digest_and_the_xhat_pair :
    ((tSm.sp.evs.filter (fun e => e.isAbs && e.tag == T_DIGEST)).all
        (fun e => occCount rowsSmXhat e.wordV > 1)
     ∧ (tSm.sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).all
        (fun e => occCount rowsSmXhat e.wordV > 1)
     ∧ (tSm.sp.evs.filter (fun e => e.isAbs && e.tag != T_DIGEST && e.tag != T_XHAT)).all
        (fun e => occCount rowsSmXhat e.wordV == 1)) = true := by
  native_decide
#assert_compiled the_consumed_words_are_exactly_the_digest_and_the_xhat_pair

/-! ## §W3 — THE CELLS THE GRID NEVER READS. -/

/-- ⚑ **ONE PER CHALLENGE, AND THEY ARE THE HIGH CHAINS' OWN `hi`.** `challengeRowsQ` runs a second
`to_field_checked` over each squeeze's high half with `split = false` (`…:1099`), so that chain's
`cv.hi` variable is allocated, given the value 0 by `chainEnv` (`…:1111`), and never wired — a
`split = false` chain emits a `cEq` tie instead of a `cSplit` row and therefore reads no `hi`.

**(c) benign** — nothing reads them, so nothing can be moved by choosing them. Named because the
step side has the same shape at `vDHi 0` and because a dead environment entry is exactly the
inverse of the `qPrime` regression, which was a wired variable with no entry. -/
theorem the_only_unread_wrap_cells_are_the_high_chains_dead_hi :
    ((envVarsNoRowReads (circuitEnvAt tWrap .key) rowsWrapKey).length = 21
     ∧ nChals shapeWrap = 21
     ∧ (List.range (nChals shapeWrap)).all (fun c =>
          occCount rowsWrapKey
            (chainVars shapeWrap (baseCh shapeWrap tWrap.sp + 1) (nChals shapeWrap + c)).hi == 0)
        = true) := by
  native_decide
#assert_compiled the_only_unread_wrap_cells_are_the_high_chains_dead_hi

/-! ## §W4 — ⚑ THE PUBLIC VECTOR: 22 OF 40, AND THE GAP AGAINST UPSTREAM IS TWO WORDS.

§10's census reads "22 of 40" and lists the 18 this rung does not expose. ⚠ That framing implies
eighteen missing derivations. **Upstream derives 24, not 40.** Read at source, `wrap_main`'s closing
block pins exactly: β/γ/α/ζ (`assert_eq_plonk`, `wrap_verifier.ml:486-499,717-731`),
`sponge_digest_before_evaluations` (`wrap_main.ml:430-432`), the sixteen bulletproof challenges
(`:433-439`), `messages_for_next_wrap_proof` (`:421-429`) and `branch_data` (`:189-199`). Words 0–4
and 9 — `combined_inner_product`, `b`, the two ζ powers, `perm`, ξ — are DEFERRED VALUES that
`wrap_main` passes through as `~advice`/`~plonk` and never checks; the next STEP proof's
`finalize_other_proof` checks them. Words 30–37 are `Spec.T.Constant` feature flags
(`spec.ml:312-324`) and 38–39 are the lookup `Opt`'s flag and dummy, with
`lookup_verification_enabled = false` (`step_verifier.ml:12`) and `use = Opt.Flag.No`
(`wrap_main.ml:83-86`).

**So the real gap is words 11 and 12 — W-WRAPHACK — and nothing else.** -/

/-- ⚑ The census, with the honest denominator. 22 exposed; upstream pins 24; the difference is two
words and both are `hash_messages_for_next_wrap_proof`'s. -/
theorem the_public_vector_gap_against_upstream_is_two_words :
    (shapeWrap.pubWords = 22
     ∧ WRAP_PRIMARY_LEN = 40
     ∧ (exposedVars tWrap).length = 22
     ∧ shapeWrap.pubWords + 2 = 24) := by
  native_decide
#assert_compiled the_public_vector_gap_against_upstream_is_two_words

/-! ## §W5 — ⚑ THE HEADLINE, as one theorem. -/

/-- ⚑⚑ **THE WRAP CENSUS.** 120 absorbed field elements of which 119 are supplied and unconsumed at
`w5_key` (117 at `w6_xhat`); 21 environment cells the grid never reads, all of them the high chains'
dead `hi`; 22 of 40 statement words exposed against upstream's 24; and `WRAP_UNCONSUMED`'s eight
classes unchanged. -/
theorem the_wrap_prover_choice_census :
    (nItems shapeWrap = 120
     ∧ ((absorbedWordVars tWrap).filter (fun v => occCount rowsWrapKey v == 1)).length = 119
     ∧ (envVarsNoRowReads (circuitEnvAt tWrap .key) rowsWrapKey).length = 21
     ∧ WRAP_UNCONSUMED.length = 8
     ∧ shapeWrap.pubWords = 22) := by
  native_decide
#assert_compiled the_wrap_prover_choice_census

end Dregg2.Circuit.Emit.KimchiWrapProverChoice
