/-
# Dregg2.Circuit.Emit.HomomorphicDigestEmitProd — the PRODUCTION-WIDTH SIS digest FOLD STEP (n = 9)

THIS IS LEAN-AUTHORED AIR. This module is the sole author of the algebra for the
`dregg-homomorphic-digest-step-n9` descriptor; Rust may only parse the emitted IR2 bytes and
supply witnesses. No Rust-side constraint exists for this family.

## What it is

The PRODUCTION-WIDTH clone of the n = 4 POC (`HomomorphicDigestEmit.lean` — kept intact as the
POC): the recursion prover's scan-state digest update (`docs/reference/SIS-DIGEST-PARAMS.md`,
`Dregg2/Crypto/HomomorphicDigest.lean` + `HomomorphicDigestPositioned.lean`) is a MONOID fold
`dig' = dig + A·encode(turn)` over `ℤ_q` with `q = BabyBear = 2013265921`. Because `q` IS the AIR's
field modulus, field arithmetic IS the digest's ring arithmetic — no non-native reduction, no
carries: one windowGate per digest coordinate is the whole fold step. This descriptor is the
FOLD-STEP ACCEPTOR (not evaluator — the producer supplies the witness): rows are turns; each
transition folds one turn's contribution into the running digest accumulator.

## Width: n = 9 — the birthday-tight figure, stated honestly

`SIS-DIGEST-PARAMS.md` §4: the position-indexed digest at 128-bit classical is **9 felts
(279 bits) on the birthday floor** — the optimistic-ℓ₂ SIS reading collapses onto it — and
**46–48 felts on the conservative ℓ∞ SIS floor**. `n = 9` here is the birthday-tight
(128-bit collision-safe) production width; if the deployment sizes to the conservative ℓ∞
convention the clone to 46–48 is mechanical (same three constraint blocks, wider). The encode
block width is `m = 9` (square `A`) for this production POC — the doc's `m_block` is "a handful
of felts" and square keeps the descriptor symmetric; a deployed block width is the encoder's
call, and changing `m` only lengthens `rowDotExpr`.

## Transparent `A` — auditable derivation, NO hardness claim

Unlike the POC's hand-picked placeholder (`A k j = 1 + 4k + j`), every entry here is derived from
a PUBLIC SEED by a fixed, documented, nothing-up-my-sleeve function:

* `SEED = 0x6472656767` — the five ASCII bytes of the string `"dregg"` read as a big-endian
  integer (`echo -n dregg | xxd` — auditable in one shell line).
* `mix64` — the splitmix64 output mixer (Steele–Lea–Vigna; Vigna's public-domain
  `splitmix64.c`), verbatim with its published constants: the golden-ratio increment
  `0x9E3779B97F4A7C15` and the finalizer multipliers `0xBF58476D1CE4E5B9`, `0x94D049BB133111EB`.
* `A k j = mix64 (SEED + 9·k + j) mod p` — the inputs `SEED + 9k + j` are pairwise distinct for
  `k, j < 9`, so each entry gets its own mixer call.

HONESTY: transparency here means AUDITABLE DERIVATION (no freedom to cook the matrix), not a
hardness claim. The SIS-hardness of THIS `A` at THESE dimensions (n = m = 9, q = BabyBear,
short-vector bound per the encode discipline) is the ESTIMATOR'S job — `SIS-DIGEST-PARAMS.md`
sizes the felt count from the Core-SVP model and says exactly what a `lattice-estimator` run
would tighten. Nothing cryptographic is PROVED about `A` in this file; what IS proved is that the
emitted constraints accept exactly the fold step against this fixed public matrix. A
position-indexed deployment (`Aᵢ = H(i)`, the doc's winning construction) derives block `i` by
absorbing the position into the same mixer input; THIS descriptor carries the single fixed block
(the fold-step shape is identical).

## Rows / columns / PIs (n = 9 digest coords, m = 9 encode coords, traceWidth 27, piCount 18)

* `dig[k] = col k` (k < 9) — the running digest accumulator.
* `enc[j] = col 9+j` (j < 9) — this row's encode witness (the turn's `encode(turn)` coordinates).
* `contrib[k] = col 18+k` (k < 9) — this row's claimed `A·enc` matrix-vector product.
* PI 0..8 — the INITIAL digest (bound to the first row's `dig`); PI 9..17 — the FINAL digest
  (bound to the last row's `dig`). PI-bound (not zero-pinned) so an IVC chunk can continue a
  previous chunk's digest; a genesis chunk passes the zero digest as PI 0..8.
* Row 0 is the SEED row: it carries the initial digest and its own `enc`/`contrib` lanes are NOT
  accumulated (the accumulate gate fires on transitions, folding the NEXT row's contribution).
  A trace of `1 + t` rows folds exactly `t` turns; a 1-row trace folds none (initial = final).

## Constraints

1. Per k < 9 a `.gate`: `contrib[k] − Σ_{j<9} A k j · enc[j] = 0` — the witness column IS the
   genuine matrix-vector product (A entries are emitted `.const`s).
2. Per k < 9 a `.windowGate` (on-transition): `nxt[dig k] − loc[dig k] − nxt[contrib k] = 0` —
   the accumulate step, verbatim the BilateralAggregation cumulative-sum shape.
3. Per k < 9 a `.boundary .last` twin of gate 1 (LAST-ROW REPAIR, MerkleMembership's
   `gLastRowBoundaries` pattern): `.gate`s are transition-guarded (`when_transition()`), so
   without the repair the LAST row's `contrib` — the one the final transition folds — would be
   unconstrained and the final digest forgeable.
4. `.piBinding first dig[k] ↦ PI k` and `.piBinding last dig[k] ↦ PI 9+k`.

## Soundness in this file

* `step_refines_prod` — FIELD-FAITHFUL per-step iff (the `cg3_body_modEq_zero_iff` shape): the
  fold-step bodies vanish mod `p` at a two-row window IFF the folded row's `contrib` is the
  genuine `A·enc` AND `dig' ≡ dig + A·enc` coordinate-wise mod `p` — i.e. the constraints accept
  EXACTLY the monoid fold step, over the deployed field.
* `step_rejects_wrong_accumulate` — the descriptor-level tooth: a transition window whose claimed
  `dig'` disagrees (mod `p`) with `dig + contrib` cannot satisfy the descriptor. At `q = BabyBear`
  the mod-`p` disagreement IS the spec-level disagreement (the digest lives in `ℤ_q`), so no
  canonicality side-conditions are needed or smuggled.
* `step_accepts_correct` — the completeness face: an honest window satisfies EVERY descriptor
  constraint on a mid-trace transition window.
* Concrete non-vacuity witnesses (`#guard`): an honest step's bodies all vanish; a tampered
  `dig'₀` is rejected in the FIELD.

## Deferred / follow-ups (the honest seams)

* Registry wiring (`EmitByName` + `scripts/emit_descriptors.py` golden) is the INTEGRATOR'S
  step — this module is not yet reachable by name.
* The conservative-ℓ∞ width (46–48 felts) and the position-indexed per-block `Aᵢ` are mechanical
  widenings of this file (§ Width / § Transparent `A` above).
* The multi-step refinement — whole-trace satisfaction ⟹ `HomomorphicDigest.digest` /
  `HomomorphicDigestPositioned` over the folded history — is a follow-up; THIS file proves the
  per-step acceptance is exactly the fold step.

## Axiom hygiene

`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}` on every keystone. NEW file; imports
read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.HomomorphicDigestEmitProd

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

set_option autoImplicit false

/-! ## §0 — Layout: production parameters, columns, and the transparently-sampled matrix. -/

/-- Production digest width (`n` in the SIS doc: the birthday-tight 128-bit figure; the
conservative ℓ∞ figure is 46–48 — see header). -/
def N_DIG : Nat := 9
/-- Encode-block width (`m_block` in the SIS doc; square `A` for this production POC). -/
def N_ENC : Nat := 9

/-- Column of running-digest coordinate `k` (k < 9). -/
def digCol (k : Nat) : Nat := k
/-- Column of this row's encode-witness coordinate `j` (j < 9). -/
def encCol (j : Nat) : Nat := 9 + j
/-- Column of this row's claimed `A·enc` coordinate `k` (k < 9). -/
def contribCol (k : Nat) : Nat := 18 + k

/-- The PUBLIC nothing-up-my-sleeve seed: the five ASCII bytes of `"dregg"` read big-endian
(`0x64 0x72 0x65 0x67 0x67` — `echo -n dregg | xxd`). -/
def SEED : Nat := 0x6472656767

/-- The splitmix64 output mixer (Steele–Lea–Vigna, Vigna's public-domain `splitmix64.c`) —
a FIXED, documented, auditable 64-bit mixing function with its published constants. Used ONLY
as a transparent sampler (nothing-up-my-sleeve derivation of `A`); no cryptographic property
of `mix64` is claimed or used in any proof. -/
def mix64 (x : Nat) : Nat :=
  let m : Nat := 2 ^ 64
  let z := (x + 0x9E3779B97F4A7C15) % m
  let z := ((z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9) % m
  let z := ((z ^^^ (z >>> 27)) * 0x94D049BB133111EB) % m
  z ^^^ (z >>> 31)

/-- The transparent per-entry sampler: entry `(k, j)` mixes the distinct input `SEED + 9k + j`
(pairwise distinct for `k, j < 9`). -/
def seedHash (seed k j : Nat) : Nat := mix64 (seed + 9 * k + j)

/-- The fixed PUBLIC matrix, transparently sampled: `A k j = mix64 (SEED + 9k + j) mod p`
(meaningful for `k, j < 9`). Transparency = auditable derivation. The SIS-hardness of this `A`
at these dimensions is the ESTIMATOR'S job (`docs/reference/SIS-DIGEST-PARAMS.md`) — NOT proved
here. -/
def A (k j : Nat) : ℤ := ((seedHash SEED k j) % 2013265921 : Nat)

-- Every sampled entry is a canonical field element (non-vacuity of the derivation).
#guard (List.range 9).all fun k => (List.range 9).all fun j =>
  decide (0 ≤ A k j ∧ A k j < 2013265921)

/-! ## §1 — The emitted bodies. -/

/-- `Σ_{j<9} A k j · enc[j]` as the emitted expression (left-nested `.add`s, `A` entries
`.const`). -/
def rowDotExpr (k : Nat) : EmittedExpr :=
  .add (.add (.add (.add (.add (.add (.add (.add
        (.mul (.const (A k 0)) (.var (encCol 0)))
        (.mul (.const (A k 1)) (.var (encCol 1))))
        (.mul (.const (A k 2)) (.var (encCol 2))))
        (.mul (.const (A k 3)) (.var (encCol 3))))
        (.mul (.const (A k 4)) (.var (encCol 4))))
        (.mul (.const (A k 5)) (.var (encCol 5))))
        (.mul (.const (A k 6)) (.var (encCol 6))))
        (.mul (.const (A k 7)) (.var (encCol 7))))
       (.mul (.const (A k 8)) (.var (encCol 8)))

/-- The `A·enc` witness-gate body: `contrib[k] − Σ_j A k j · enc[j]`. -/
def contribBody (k : Nat) : EmittedExpr :=
  .add (.var (contribCol k)) (.mul (.const (-1)) (rowDotExpr k))

/-- The SPEC-side dot product `Σ_{j<9} A k j · enc[j]` over an assignment. -/
def dotRow (k : Nat) (asg : Assignment) : ℤ :=
  A k 0 * asg (encCol 0) + A k 1 * asg (encCol 1) + A k 2 * asg (encCol 2) +
  A k 3 * asg (encCol 3) + A k 4 * asg (encCol 4) + A k 5 * asg (encCol 5) +
  A k 6 * asg (encCol 6) + A k 7 * asg (encCol 7) + A k 8 * asg (encCol 8)

/-- The accumulate windowGate body (BilateralAggregation's cumulative-sum shape):
`nxt[dig k] + (−1)·loc[dig k] + (−1)·nxt[contrib k]`. -/
def accumBody (k : Nat) : WindowExpr :=
  .add (.nxt (digCol k))
       (.add (.mul (.const (-1)) (.loc (digCol k)))
             (.mul (.const (-1)) (.nxt (contribCol k))))

/-! ## §2 — The constraints and the descriptor. -/

/-- The per-row `A·enc` witness gate for coordinate `k`. -/
def contribGate (k : Nat) : VmConstraint2 := .base (.gate (contribBody k))

/-- The on-transition accumulate gate for coordinate `k`: `dig' = dig + contrib'`. -/
def accumGate (k : Nat) : VmConstraint2 := .windowGate ⟨accumBody k, true⟩

/-- LAST-ROW REPAIR: the `A·enc` witness gate re-asserted on the last row (`.gate` is
transition-guarded, so without this twin the final fold's `contrib` would be unconstrained). -/
def lastRepair (k : Nat) : VmConstraint2 := .base (.boundary .last (contribBody k))

/-- Bind first-row `dig[k]` to PI `k` (the initial digest). -/
def initialPin (k : Nat) : VmConstraint2 := .base (.piBinding .first (digCol k) k)

/-- Bind last-row `dig[k]` to PI `9+k` (the final digest). -/
def finalPin (k : Nat) : VmConstraint2 := .base (.piBinding .last (digCol k) (9 + k))

/-- The nine `A·enc` witness gates. -/
def contribGates : List VmConstraint2 := (List.range 9).map contribGate
/-- The nine accumulate windowGates. -/
def accumGates : List VmConstraint2 := (List.range 9).map accumGate
/-- The nine last-row repairs. -/
def lastRepairs : List VmConstraint2 := (List.range 9).map lastRepair
/-- The nine initial-digest PI pins. -/
def initialPins : List VmConstraint2 := (List.range 9).map initialPin
/-- The nine final-digest PI pins. -/
def finalPins : List VmConstraint2 := (List.range 9).map finalPin

/-- The complete fold-step constraint block. -/
def homDigestStepProdConstraints : List VmConstraint2 :=
  contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins

/-- The SIS homomorphic-digest FOLD-STEP descriptor (production width n = 9, `q = BabyBear`,
transparent `A`). -/
def homDigestStepProdDesc : EffectVmDescriptor2 :=
  { name        := "dregg-homomorphic-digest-step-n9::v1"
  , traceWidth  := 27
  , piCount     := 18
  , tables      := []
  , constraints := homDigestStepProdConstraints
  , hashSites   := []
  , ranges      := [] }

-- Non-vacuous structural pins. The exact emitted-byte pin follows the literal golden below.
#guard homDigestStepProdDesc.traceWidth == 27
#guard homDigestStepProdDesc.piCount == 18
#guard homDigestStepProdDesc.constraints.length == 45
#guard homDigestStepProdDesc.tables.length == 0
#guard (homDigestStepProdDesc.constraints.filter
          (fun c => match c with | .windowGate _ => true | _ => false)).length == 9

/-- Exact emitted-wire golden. Generated once from `#eval repr (emitVmJson2
homDigestStepProdDesc)` and pasted verbatim; the Rust side will `include_str!` these bytes when
the registry wiring lands (the INTEGRATOR's step). -/
def HOM_DIGEST_STEP_PROD_GOLDEN : String :=
  "{\"name\":\"dregg-homomorphic-digest-step-n9::v1\",\"ir\":2,\"trace_width\":27,\"public_input_count\":18,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":409872186},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1222735035},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":413868908},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1787765287},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":826900094},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1879173358},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":958222690},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":915390512},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1446052916},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1252646447},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":856763228},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":171692136},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1847453919},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":859132705},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1549613388},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":483992596},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1340307705},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1394585798},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":328164133},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":92733714},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":366475903},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1562365},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":691976870},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1467115963},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":680620278},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1422423447},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":169895877},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1056669352},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":73903633},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1342938567},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1420081606},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1538607526},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":695083503},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":444331339},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":361332713},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":285746021},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":276079888},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1144511956},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":645278577},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":540972572},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1215016717},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":594848568},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":760948359},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1294941349},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1469896349},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":711525736},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1847627690},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1844659476},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":656359178},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":646618130},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1481518972},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1907946203},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1357795894},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":277862603},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":154763718},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":629334432},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1700697655},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1394391381},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":319199763},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":873291362},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1811502002},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":564579295},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":18601851},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1500623700},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1421532846},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1628049958},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1260508399},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":994192780},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1034018670},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":373003893},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1058252072},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":932461347},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":55598663},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1326769871},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":118128441},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1244680715},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1404806094},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":691155776},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":893668809},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":856391692},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":141499502},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":18}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":19}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":20}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":21}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":22}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":23}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":24}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":7}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":25}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":26}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":409872186},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1222735035},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":413868908},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1787765287},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":826900094},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1879173358},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":958222690},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":915390512},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1446052916},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1252646447},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":856763228},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":171692136},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1847453919},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":859132705},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1549613388},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":483992596},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1340307705},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1394585798},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":328164133},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":92733714},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":366475903},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1562365},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":691976870},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1467115963},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":680620278},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1422423447},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":169895877},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1056669352},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":73903633},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1342938567},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1420081606},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1538607526},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":695083503},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":444331339},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":361332713},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":285746021},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":276079888},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1144511956},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":645278577},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":540972572},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1215016717},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":594848568},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":760948359},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1294941349},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1469896349},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":711525736},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1847627690},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1844659476},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":656359178},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":646618130},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1481518972},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1907946203},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1357795894},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":277862603},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":154763718},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":629334432},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1700697655},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1394391381},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":319199763},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":873291362},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1811502002},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":564579295},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":18601851},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1500623700},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1421532846},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1628049958},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1260508399},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":994192780},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1034018670},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":373003893},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1058252072},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":932461347},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":55598663},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1326769871},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":118128441},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1244680715},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1404806094},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":691155776},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":893668809},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":856391692},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":141499502},\"r\":{\"t\":\"var\",\"v\":17}}}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":0,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":1,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":3,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":4,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":5,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":6,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":7,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":8,\"pi_index\":17}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 homDigestStepProdDesc == HOM_DIGEST_STEP_PROD_GOLDEN

-- Corner-entry pins of the transparent matrix (audit anchors: recompute
-- `mix64 (SEED + 9k + j) % 2013265921` by hand or with any splitmix64 reference).
#guard A 0 0 == 409872186
#guard A 0 8 == 1446052916
#guard A 8 0 == 55598663
#guard A 8 8 == 141499502

/-- The complete constraint-block shape, pinned. -/
theorem descriptor_has_complete_shape :
    homDigestStepProdDesc.constraints =
      contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins := rfl

/-! ## §3 — FIELD-FAITHFUL per-step refinement (`cg3_body_modEq_zero_iff` shape). -/

/-- The `A·enc` witness gate vanishes mod `p` EXACTLY when the `contrib` column carries the
genuine matrix-vector product mod `p`. -/
theorem contrib_body_modEq_zero_iff (asg : Assignment) (k : Nat) :
    ((contribBody k).eval asg ≡ 0 [ZMOD 2013265921]) ↔
      (asg (contribCol k) ≡ dotRow k asg [ZMOD 2013265921]) := by
  simp only [contribBody, rowDotExpr, EmittedExpr.eval]
  exact gate_modEq_iff (by simp only [dotRow]; ring)

/-- The accumulate gate vanishes mod `p` EXACTLY when the next digest coordinate is the current
one plus the next row's contribution mod `p` — the monoid fold step, in the field. -/
theorem accum_body_modEq_zero_iff (env : VmRowEnv) (k : Nat) :
    ((accumBody k).eval env ≡ 0 [ZMOD 2013265921]) ↔
      (env.nxt (digCol k) ≡ env.loc (digCol k) + env.nxt (contribCol k) [ZMOD 2013265921]) := by
  simp only [accumBody, WindowExpr.eval]
  exact gate_modEq_iff (by ring)

/-- The FOLD-STEP body bundle at a two-row window: the nine accumulate windowGate bodies (on the
window) + the nine `A·enc` gate bodies on the NEXT row — the row being folded (in the whole-trace
denotation that row's own window asserts them: as its `.gate` on a transition row, as the
`.boundary .last` repair on the last row). -/
def foldStepHolds (env : VmRowEnv) : Prop :=
  (∀ k, k < 9 → ((accumBody k).eval env ≡ 0 [ZMOD 2013265921])) ∧
  (∀ k, k < 9 → ((contribBody k).eval env.nxt ≡ 0 [ZMOD 2013265921]))

/-- **THE PER-STEP REFINEMENT (production width, field-faithful, both directions).** The
fold-step bodies vanish mod `p` IFF, coordinate-wise over all nine digest coordinates: the folded
row's `contrib` witness IS the genuine `A·enc` (mod `p`), and the digest update IS the monoid
fold `dig' ≡ dig + A·enc` (mod `p`). Because `q = BabyBear` is the digest's ring modulus, the
mod-`p` statement IS the spec statement — the acceptor accepts exactly the SIS fold step, with
the witness column pinned. -/
theorem step_refines_prod (env : VmRowEnv) :
    foldStepHolds env ↔
      ∀ k, k < 9 →
        (env.nxt (contribCol k) ≡ dotRow k env.nxt [ZMOD 2013265921]) ∧
        (env.nxt (digCol k) ≡ env.loc (digCol k) + dotRow k env.nxt [ZMOD 2013265921]) := by
  constructor
  · rintro ⟨hacc, hwit⟩ k hk
    have h1 := (contrib_body_modEq_zero_iff env.nxt k).mp (hwit k hk)
    have h2 := (accum_body_modEq_zero_iff env k).mp (hacc k hk)
    exact ⟨h1, h2.trans (Int.ModEq.add_left _ h1)⟩
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · exact (accum_body_modEq_zero_iff env k).mpr
        ((h k hk).2.trans (Int.ModEq.add_left _ (h k hk).1.symm))
    · exact (contrib_body_modEq_zero_iff env.nxt k).mpr (h k hk).1

/-! ## §4 — Descriptor-level teeth: the emitted object itself accepts/rejects. -/

/-- The descriptor's per-window denotation (no tables / hash sites / ranges): every constraint
holds on the window. -/
def stepWindowHolds (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ homDigestStepProdDesc.constraints,
    c.holdsAt (fun _ => 0) (fun _ => []) env isFirst isLast

/-- The accumulate gate for coordinate `k < 9` is IN the descriptor. -/
theorem accumGate_mem (k : Nat) (hk : k < 9) :
    accumGate k ∈ homDigestStepProdDesc.constraints := by
  show accumGate k ∈ contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins
  have hmem : accumGate k ∈ accumGates :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ hmem)))

/-- **NEGATIVE TOOTH (descriptor-level, field-faithful).** A transition window whose claimed next
digest coordinate disagrees mod `p` with `dig + contrib` CANNOT satisfy the descriptor: the
accumulate gate is real, not decorative. At `q = BabyBear` the mod-`p` disagreement IS the
spec-level disagreement (the digest lives in `ℤ_q`), so no canonicality hypotheses are needed. -/
theorem step_rejects_wrong_accumulate (env : VmRowEnv) (k : Nat) (hk : k < 9)
    (hbad : ¬ (env.nxt (digCol k)
      ≡ env.loc (digCol k) + env.nxt (contribCol k) [ZMOD 2013265921])) :
    ¬ stepWindowHolds env false false := by
  intro h
  have hc := h _ (accumGate_mem k hk)
  simp only [accumGate, VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hc
  exact hbad ((accum_body_modEq_zero_iff env k).mp (hc trivial))

/-- **POSITIVE TOOTH (descriptor-level completeness).** An honest mid-trace transition window —
current row's `contrib` genuine, next digest the genuine fold — satisfies EVERY constraint of the
descriptor (boundary/PI forms are off-row here; the folded row's own witness gate is asserted by
ITS window, per `foldStepHolds`). The acceptor does not over-constrain the honest prover. -/
theorem step_accepts_correct (env : VmRowEnv)
    (hloc : ∀ k, k < 9 → (env.loc (contribCol k) ≡ dotRow k env.loc [ZMOD 2013265921]))
    (hacc : ∀ k, k < 9 → (env.nxt (digCol k)
      ≡ env.loc (digCol k) + env.nxt (contribCol k) [ZMOD 2013265921])) :
    stepWindowHolds env false false := by
  intro c hc
  rw [descriptor_has_complete_shape] at hc
  simp only [contribGates, accumGates, lastRepairs, initialPins, finalPins,
    List.mem_append, List.mem_map, List.mem_range] at hc
  rcases hc with ((((⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩)
  · exact (contrib_body_modEq_zero_iff env.loc k).mpr (hloc k hk)
  · exact fun _ => (accum_body_modEq_zero_iff env k).mpr (hacc k hk)
  · exact fun (h : false = true) => nomatch h
  · exact fun (h : false = true) => nomatch h
  · exact fun (h : false = true) => nomatch h

/-! ## §5 — Concrete witness rows (non-vacuity, both directions).

Honest window: `loc.dig[k] = 100·(k+1)`; the folded row has `enc = 1⁹`, so the genuine
contribution for coordinate `k` is the `A` row sum `Σ_j A k j` and the honest next digest is
`dig[k] + Σ_j A k j`. Everything is DEFINED through the transparently-sampled `A`, so these
guards compute through the real matrix, not through hand-copied constants. -/

/-- The genuine row-`k` contribution for the all-ones encode: `Σ_j A k j`. -/
def rowSumA (k : Nat) : ℤ := dotRow k (fun _ => 1)

/-- Honest current row: digest `dig[k] = 100·(k+1)`, all witness lanes zero. -/
def okLoc : Assignment := fun i => if i < 9 then 100 * ((i : ℤ) + 1) else 0

/-- Honest next row: `dig'[k] = dig[k] + Σ_j A k j`, `enc = 1⁹`, `contrib[k] = Σ_j A k j`. -/
def okNxt : Assignment := fun i =>
  if i < 9 then okLoc i + rowSumA i
  else if i < 18 then 1
  else if i < 27 then rowSumA (i - 18)
  else 0

/-- The honest two-row window. -/
def okEnv : VmRowEnv := { loc := okLoc, nxt := okNxt, pub := fun _ => 0 }

/-- The tampered next row: `dig'₀` forged by `+1` (everything else honest). -/
def badNxt : Assignment := fun i => if i = 0 then okNxt 0 + 1 else okNxt i

/-- The tampered window. -/
def badEnv : VmRowEnv := { loc := okLoc, nxt := badNxt, pub := fun _ => 0 }

-- ACCEPTS: every fold-step body vanishes on the honest window (over ℤ, hence mod p).
#guard (List.range 9).all fun k => decide ((accumBody k).eval okEnv = 0)
#guard (List.range 9).all fun k => decide ((contribBody k).eval okNxt = 0)

-- REJECTS: the forged `dig'₀` breaks the accumulate gate IN THE FIELD (not merely over ℤ).
#guard decide (¬ ((accumBody 0).eval badEnv ≡ 0 [ZMOD 2013265921]))

/-! ## §6 — Axiom hygiene. -/

#assert_axioms descriptor_has_complete_shape
#assert_axioms contrib_body_modEq_zero_iff
#assert_axioms accum_body_modEq_zero_iff
#assert_axioms step_refines_prod
#assert_axioms accumGate_mem
#assert_axioms step_rejects_wrong_accumulate
#assert_axioms step_accepts_correct

end Dregg2.Circuit.Emit.HomomorphicDigestEmitProd
