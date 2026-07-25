/-
# Dregg2.Circuit.Emit.ParamComposeEmit — the Lean-authored PARAMETER-COMPOSITION AIR
(`param_compose`), the replacement route for the hand-written Rust AIR in
`param-compose/src/{air.rs,builder.rs}`.

## SAY THE SUBSTRATE OUT LOUD

This is **Lean-authored AIR**. The constraint list below IS the emitted object; Rust's only job is
to resolve it by name (`circuit/src/descriptor_by_name.rs`), decode it (`parse_vm_descriptor2`) and
prove it (`prove_vm_descriptor2`). Until this file existed there was NO Lean route at all for
`param-compose`: a grep of `metatheory/` for `paramCompose`/`ParamCompose` returned nothing, while
`param-compose/src/air.rs` (659 lines, 19 `assert_zero` sites) plus `param-compose/src/builder.rs`
(369 lines, 5 more sites, 6 `ConstraintExpr` literals, and an `air_accepts` predicate) hand-wrote a
complete AIR in Rust — the exact three things the law names. That AIR is LIVE:
`entity-compose/src/lib.rs:78` imports `dregg_param_compose::air::{ComposeAir, build}` in non-test
code, riding the deployed `Effect::Custom` door.

`param-compose/src/builder.rs:9-14` says of itself that it is "a sibling of `dregg-automatafl`'s
builder … duplicated rather than shared". That reading is CONFIRMED by the code: `Head`,
`assert_zero`, `assert_binary`, `range_nonneg`, `forced_ge0`, `cond_nonzero`, `alloc_prod`,
`alloc_head`, `air_accepts`, `tamper` are the same harness. When the automatafl Rust AIR was deleted
the clone survived, because it had already been copied out from under the gate's scan scope.

## What the Rust AIR actually constrains (the specification, extracted before authoring)

One composition, at a bounded `ComposeShape { max_subjects n, max_params p, max_linear l,
max_knots k, identity_bits ib }`, over a SINGLE trace row (the Rust builder co-emits one witness row
and repeats it across `num_rows`). The relation:

    outcome = Σ_{linear t} coeff_t · P[role_t].params[param_t]
            + Σ_{knot   t} coeff_t · P[roleA_t].params[paramA_t] · P[roleB_t].params[paramB_t]

where `P[r]` is the (unique) ACTIVE subject slot whose role tag is `r`. The teeth, verbatim from
`air.rs`, and where each is emitted below:

| tooth | Rust | here |
|---|---|---|
| absent tag / activity is a PREFIX | `prefix_flags` | §4 `prefixFlagGates` |
| identity in `[0, 2^ib)` | `range_nonneg` per subject | §5 `subjectGates` |
| canonical order + duplicate rejection | `forced_ge0(id[i+1] − id[i] − 1)` | §6 `orderGates` |
| a role is a KEY | pairwise `cond_nonzero(active_i·active_j, role_i − role_j)` | §7 `roleKeyGates` |
| inactive ⇒ all-zero (absence is COMMITTED) | `c − active·c == 0` | §5, §8, §9 |
| resolution BY ROLE, never by slot | the gated one-hots of `fetch` | §8 `fetchGates` |
| THE KNOT (the degree-3 nonlinearity) | `contrib − coeff·va·vb == 0` | §9 `knotGates` |
| THE LAW | `outcome − Σ contribs == 0` | §10 `lawGate` |
| the four committed roots | `wide_chain` (`cap_node8` Merkle–Damgård) | §11 `chainLookups` |
| the PI layout | `pi.rs` (53 PIs, 16 door + 37 app) | §12 `piGates` |

## Two deliberate deviations from the Rust build (improvements, stated not hidden)

1. **No `zero` column.** Rust allocates a witness column pinned to `0` and uses it as the absorb
   padding and the canonical absent value. Here the padding is the literal `.const 0` in the chip
   tuple, which is strictly stronger: a constant cannot be tampered, whereas a pinned column is one
   more gate that must hold.
2. **No `iv` columns.** Rust allocates 8 witness columns per chain pinned to the domain IV. Here the
   first block's accumulator half is 8 literal constants.

Both remove witness columns whose only content was a constant pin. Nothing else moved: the stream
ORDER, the domain tags, the absorb rate, and the PI layout are the Rust ones felt-for-felt.

## Honest scope of THIS file

This file emits the descriptor and pins its wire bytes. The SEMANTIC bridge (SAT ⟹ the composition
law) is the sibling `ParamComposeRefine.lean`, which also records exactly which of the constraints
below are covered by a proven theorem and which are emitted-but-not-yet-refined.

## Axiom hygiene

Definitional descriptor family + a byte-pinned `#guard` on the wire string of a concrete instance +
shape `#guard`s. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.AirBuilder

namespace Dregg2.Circuit.Emit.ParamComposeEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTupleN CHIP_RATE CHIP_OUT_LANES
   emitVmJson2)
open Dregg2.Circuit.Emit.AirBuilder

set_option autoImplicit false

/-! ## §1 — The SHAPE (`param-compose/src/shape.rs::ComposeShape`).

Maxima only — no role list, no rule table, no param names. A new game is a new `ruleset_root` under
the SAME descriptor; only crossing a bound mints a new one. -/

/-- The build-time bounds that define one `param_compose` descriptor (VK class). -/
structure ComposeShape where
  /-- Max subjects (`max_subjects`). -/
  n  : Nat
  /-- Max typed params per subject (`max_params`). -/
  p  : Nat
  /-- Max sparse LINEAR rule terms (`max_linear`). -/
  l  : Nat
  /-- Max sparse KNOTS — signed pairwise products (`max_knots`). -/
  k  : Nat
  /-- Width of the subject-identity namespace, in bits (`identity_bits`). -/
  ib : Nat
  deriving Repr, DecidableEq

/-- `PARAM_COMPOSE_ABI_VERSION` (`shape.rs`). -/
def ABI_VERSION : ℤ := 1

/-- The largest identity width the ordering comparison stays sound at (`MAX_SOUND_IDENTITY_BITS`).
Above this both `d` and `−d−1` reduce into range and `forced_ge0` goes VACUOUS. -/
def MAX_SOUND_IDENTITY_BITS : Nat := 28

/-- Whether the ordering comparison is NON-VACUOUS at this identity width
(`ComposeShape::identity_bits_sound`). A shape failing this must be REFUSED, not built. -/
def ComposeShape.identityBitsSound (S : ComposeShape) : Bool :=
  1 ≤ S.ib && S.ib ≤ MAX_SOUND_IDENTITY_BITS

/-- Range width of the identity ordering comparison (`identity_cmp_bits`). -/
def ComposeShape.cmpBits (S : ComposeShape) : Nat := S.ib + 1

/-! ## §2 — The column layout.

Lean is the source of truth for the layout: the Rust `Builder::alloc` call order is replaced by these
explicit offsets, so a decoder and a witness producer agree by construction. -/

/-- PI slot / column: the committed ABI version. -/
def C_ABI : Nat := 0
/-- Column: the active subject count. -/
def C_NSUBJ : Nat := 1
/-- Column: the active param width. -/
def C_NPARAM : Nat := 2
/-- Column: the active linear-term count. -/
def C_NLIN : Nat := 3
/-- Column: the active knot count. -/
def C_NKNOT : Nat := 4

namespace ComposeShape

/-- Base of the param-activity prefix flags. -/
def paBase (_S : ComposeShape) : Nat := 5
/-- The `q`-th param-activity flag. -/
def paCol (S : ComposeShape) (q : Nat) : Nat := S.paBase + q

/-- Per-subject stride: `active, id, role, params[p], id-range bits[ib], role-inverse`. -/
def subjW (S : ComposeShape) : Nat := 4 + S.p + S.ib
/-- Base of the subject block. -/
def subjBase (S : ComposeShape) : Nat := 5 + S.p
/-- Base of subject slot `i`. -/
def sBase (S : ComposeShape) (i : Nat) : Nat := S.subjBase + i * S.subjW
/-- Subject `i`'s activity flag. -/
def sActive (S : ComposeShape) (i : Nat) : Nat := S.sBase i
/-- Subject `i`'s identity. -/
def sId (S : ComposeShape) (i : Nat) : Nat := S.sBase i + 1
/-- Subject `i`'s role tag. -/
def sRole (S : ComposeShape) (i : Nat) : Nat := S.sBase i + 2
/-- Subject `i`'s param slot `q`. -/
def sParam (S : ComposeShape) (i q : Nat) : Nat := S.sBase i + 3 + q
/-- Subject `i`'s identity range bits. -/
def sIdBits (S : ComposeShape) (i : Nat) : List Nat := bitsFrom (S.sBase i + 3 + S.p) S.ib
/-- Subject `i`'s role-nonzero witnessed inverse. -/
def sRoleInv (S : ComposeShape) (i : Nat) : Nat := S.sBase i + 3 + S.p + S.ib

/-- Base of the ordering-comparison block. -/
def ordBase (S : ComposeShape) : Nat := S.subjBase + S.n * S.subjW
/-- Per-comparison stride: the `ge` bit plus `ib+1` range bits. -/
def ordW (S : ComposeShape) : Nat := 2 + S.ib
/-- The `i`-th comparison's `[d ≥ 0]` bit. -/
def oGe (S : ComposeShape) (i : Nat) : Nat := S.ordBase + i * S.ordW
/-- The `i`-th comparison's range bits. -/
def oBits (S : ComposeShape) (i : Nat) : List Nat :=
  bitsFrom (S.ordBase + i * S.ordW + 1) S.cmpBits

/-- The ordered list of distinct subject-slot pairs `(i, j)` with `i < j` — the role-key sweep. -/
def pairList (S : ComposeShape) : List (Nat × Nat) :=
  (List.range S.n).flatMap fun i =>
    (List.range S.n).filterMap fun j => if i < j then some (i, j) else none

/-- Base of the role-key pair block. -/
def ruBase (S : ComposeShape) : Nat := S.ordBase + (S.n - 1) * S.ordW
/-- The `t`-th pair's `active_i · active_j` product column. -/
def ruBoth (S : ComposeShape) (t : Nat) : Nat := S.ruBase + 3 * t
/-- The `t`-th pair's `role_i − role_j` difference column. -/
def ruDiff (S : ComposeShape) (t : Nat) : Nat := S.ruBase + 3 * t + 1
/-- The `t`-th pair's witnessed inverse (the conditional-nonzero witness). -/
def ruInv (S : ComposeShape) (t : Nat) : Nat := S.ruBase + 3 * t + 2

/-- Base of the ruleset block. -/
def rsBase (S : ComposeShape) : Nat := S.ruBase + 3 * S.pairList.length
/-- The ruleset catalog id. -/
def cRid (S : ComposeShape) : Nat := S.rsBase
/-- The ruleset version. -/
def cRver (S : ComposeShape) : Nat := S.rsBase + 1

/-- Base of the linear-term activity flags. -/
def laBase (S : ComposeShape) : Nat := S.rsBase + 2
/-- The `t`-th linear term's activity flag. -/
def laCol (S : ComposeShape) (t : Nat) : Nat := S.laBase + t

/-- A fetch block's width: `n` subject selectors, `p` param selectors, and the read value. -/
def fetW (S : ComposeShape) : Nat := S.n + S.p + 1
/-- Per-linear-term stride: `role, param, coeff`, a fetch block, and the contribution. -/
def linW (S : ComposeShape) : Nat := 4 + S.fetW
/-- Base of the linear-term block. -/
def linBase (S : ComposeShape) : Nat := S.laBase + S.l
/-- Base of linear term `t`. -/
def lBase (S : ComposeShape) (t : Nat) : Nat := S.linBase + t * S.linW
/-- Linear term `t`'s addressed role. -/
def lRole (S : ComposeShape) (t : Nat) : Nat := S.lBase t
/-- Linear term `t`'s addressed param slot. -/
def lParam (S : ComposeShape) (t : Nat) : Nat := S.lBase t + 1
/-- Linear term `t`'s coefficient. -/
def lCoeff (S : ComposeShape) (t : Nat) : Nat := S.lBase t + 2
/-- Base of linear term `t`'s fetch block. -/
def lFet (S : ComposeShape) (t : Nat) : Nat := S.lBase t + 3
/-- Linear term `t`'s contribution `coeff · value`. -/
def lContrib (S : ComposeShape) (t : Nat) : Nat := S.lBase t + 3 + S.fetW

/-- Base of the knot activity flags. -/
def kaBase (S : ComposeShape) : Nat := S.linBase + S.l * S.linW
/-- The `t`-th knot's activity flag. -/
def kaCol (S : ComposeShape) (t : Nat) : Nat := S.kaBase + t

/-- Per-knot stride: five addressing columns, TWO fetch blocks, and the contribution. -/
def knotW (S : ComposeShape) : Nat := 6 + 2 * S.fetW
/-- Base of the knot block. -/
def knotBase (S : ComposeShape) : Nat := S.kaBase + S.k
/-- Base of knot `t`. -/
def kBase (S : ComposeShape) (t : Nat) : Nat := S.knotBase + t * S.knotW
/-- Knot `t`'s left role. -/
def kRoleA (S : ComposeShape) (t : Nat) : Nat := S.kBase t
/-- Knot `t`'s left param slot. -/
def kParA (S : ComposeShape) (t : Nat) : Nat := S.kBase t + 1
/-- Knot `t`'s right role. -/
def kRoleB (S : ComposeShape) (t : Nat) : Nat := S.kBase t + 2
/-- Knot `t`'s right param slot. -/
def kParB (S : ComposeShape) (t : Nat) : Nat := S.kBase t + 3
/-- Knot `t`'s coefficient. -/
def kCoeff (S : ComposeShape) (t : Nat) : Nat := S.kBase t + 4
/-- Base of knot `t`'s LEFT fetch block. -/
def kFetA (S : ComposeShape) (t : Nat) : Nat := S.kBase t + 5
/-- Base of knot `t`'s RIGHT fetch block. -/
def kFetB (S : ComposeShape) (t : Nat) : Nat := S.kBase t + 5 + S.fetW
/-- Knot `t`'s contribution `coeff · va · vb` — THE NONLINEARITY. -/
def kContrib (S : ComposeShape) (t : Nat) : Nat := S.kBase t + 5 + 2 * S.fetW

/-- The outcome column. -/
def cOut (S : ComposeShape) : Nat := S.knotBase + S.k * S.knotW

/-- A fetch block's subject selector `j`. -/
def fSel (_S : ComposeShape) (fb j : Nat) : Nat := fb + j
/-- A fetch block's param selector `q`. -/
def fSelP (S : ComposeShape) (fb q : Nat) : Nat := fb + S.n + q
/-- A fetch block's read value. -/
def fVal (S : ComposeShape) (fb : Nat) : Nat := fb + S.n + S.p

end ComposeShape

/-! ## §3 — The wide digest (`param-compose/src/digest.rs`).

Domain-separated `cap_node8` Merkle–Damgård: seed an 8-felt accumulator with `IV8(domain)`, absorb
the canonical stream 8 felts at a time by `acc8 := node8(acc8 ‖ block8)` — ONE arity-16 Poseidon2
permutation per block, all 8 output lanes program-owned. In IR-v2 that is exactly ONE WIDE chip
lookup (`chipLookupTupleN`, 16 inputs / 8 digest columns), whose soundness lever is
`chip_lookup_sound_N`. -/

/-- Felts absorbed per `node8` site (`ABSORB_RATE`). -/
def ABSORB_RATE : Nat := 8
/-- Felts in a committed root (`DIGEST_FELTS`) — the native `cap_node8` output width. -/
def DIGEST_FELTS : Nat := 8
/-- Spacing between domain IV lanes (`LANE_STRIDE`). -/
def LANE_STRIDE : ℤ := 256

/-- Domain tag `0x9C01` — the canonical subjects stream. -/
def DOMAIN_SUBJECTS : ℤ := 39937
/-- Domain tag `0x9C02` — the canonical ruleset stream (THE COMPOSITION LAW). -/
def DOMAIN_RULESET : ℤ := 39938
/-- Domain tag `0x9C03` — the outcome. -/
def DOMAIN_OUTCOME : ℤ := 39939
/-- Domain tag `0x9C04` — the per-term explanation contributions. -/
def DOMAIN_EXPLANATION : ℤ := 39940

/-- The domain-separated 8-felt initial accumulator: lane `t` is `domain · 256 + t`. -/
def iv8 (domain : ℤ) : List ℤ :=
  (List.range DIGEST_FELTS).map fun t => domain * LANE_STRIDE + (t : ℤ)

/-- Number of `node8` blocks a stream of `len` felts costs (`⌈len/8⌉`, at least one). -/
def blocksOf (len : Nat) : Nat := max 1 ((len + ABSORB_RATE - 1) / ABSORB_RATE)

namespace ComposeShape

/-- Felts in the canonical subjects stream (`subjects_stream_len`). -/
def subjLen (S : ComposeShape) : Nat := 2 + S.n * (3 + S.p)
/-- Felts in the canonical ruleset stream (`ruleset_stream_len`). -/
def ruleLen (S : ComposeShape) : Nat := 4 + S.l * 4 + S.k * 6
/-- Felts in the outcome stream. -/
def outLen (_S : ComposeShape) : Nat := 1
/-- Felts in the explanation stream (`explanation_stream_len`). -/
def explLen (S : ComposeShape) : Nat := S.l + S.k

/-- `node8` block counts, per stream. -/
def blkSubj (S : ComposeShape) : Nat := blocksOf S.subjLen
/-- `node8` block count for the ruleset stream. -/
def blkRule (S : ComposeShape) : Nat := blocksOf S.ruleLen
/-- `node8` block count for the outcome stream. -/
def blkOut (S : ComposeShape) : Nat := blocksOf S.outLen
/-- `node8` block count for the explanation stream. -/
def blkExpl (S : ComposeShape) : Nat := blocksOf S.explLen

/-- **THE FUEL BOUND** — total Poseidon2 chip sites at this shape (`ComposeShape::hash_sites`). -/
def hashSites (S : ComposeShape) : Nat := S.blkSubj + S.blkRule + S.blkOut + S.blkExpl

/-- Base of the digest-chain output columns. -/
def digBase (S : ComposeShape) : Nat := S.cOut + 1

/-- Block-column base of chain `c ∈ {0,1,2,3}` (subjects, ruleset, outcome, explanation). -/
def chainOff (S : ComposeShape) : Nat → Nat
  | 0 => 0
  | 1 => S.blkSubj
  | 2 => S.blkSubj + S.blkRule
  | _ => S.blkSubj + S.blkRule + S.blkOut

/-- The 8 output columns of chain `c`'s block `b`. -/
def chainCols (S : ComposeShape) (c b : Nat) : List Nat :=
  bitsFrom (S.digBase + DIGEST_FELTS * (S.chainOff c + b)) DIGEST_FELTS

/-- The 8 ROOT columns of chain `c` (its last block's output). -/
def rootCols (S : ComposeShape) (c : Nat) : List Nat :=
  S.chainCols c ((match c with
    | 0 => S.blkSubj | 1 => S.blkRule | 2 => S.blkOut | _ => S.blkExpl) - 1)

/-- **The main-trace width.** -/
def width (S : ComposeShape) : Nat :=
  S.digBase + DIGEST_FELTS * (S.blkSubj + S.blkRule + S.blkOut + S.blkExpl)

end ComposeShape

/-! ## §4 — Prefix-flag gates (`air.rs::prefix_flags`).

A boolean indicator vector whose sum is pinned to a count column and which is PREFIX-MONOTONE, so
"active" is a prefix and the canonical padding is unambiguous. -/

/-- `binary(f_i)` for each slot, `f_{i+1}·(1 − f_i) = 0` for each adjacent pair, and `Σ f = count`. -/
def prefixFlagGates (base cnt countCol : Nat) : List VmConstraint2 :=
  ((List.range cnt).map fun i => binGate (base + i))
  ++ ((List.range (cnt - 1)).map fun i =>
        cgH ((Head.lin 1 (base + i + 1)).addProd (-1) [base + i + 1, base + i]))
  ++ [cgH ((List.range cnt).foldl (fun h i => h.addLin 1 (base + i)) (Head.lin (-1) countCol))]

/-! ## §5 — The subjects (`air.rs` "the subjects" block). -/

/-- Per-subject gates: the activity pin, the identity range check, the two inactive⇒zero pins, the
active⇒`role ≠ 0` conditional-nonzero, and the two zero pins on each param slot (out-of-`param_count`
and inactive-subject). -/
def subjectGates (S : ComposeShape) (i : Nat) : List VmConstraint2 :=
  [binGate (S.sActive i)]
  ++ rangeNonneg (Head.lin 1 (S.sId i)) (S.sIdBits i)
  ++ [ cgH ((Head.lin 1 (S.sId i)).addProd (-1) [S.sActive i, S.sId i])
     , cgH ((Head.lin 1 (S.sRole i)).addProd (-1) [S.sActive i, S.sRole i])
     , condNonzero (S.sActive i) (S.sRole i) (S.sRoleInv i) ]
  ++ ((List.range S.p).flatMap fun q =>
        [ cgH ((Head.lin 1 (S.sParam i q)).addProd (-1) [S.paCol q, S.sParam i q])
        , cgH ((Head.lin 1 (S.sParam i q)).addProd (-1) [S.sActive i, S.sParam i q]) ])

/-- Subject activity is a PREFIX and its weight is the committed `subject_count`. -/
def subjectPrefixGates (S : ComposeShape) : List VmConstraint2 :=
  ((List.range (S.n - 1)).map fun i =>
      cgH ((Head.lin 1 (S.sActive (i + 1))).addProd (-1) [S.sActive (i + 1), S.sActive i]))
  ++ [cgH ((List.range S.n).foldl (fun h i => h.addLin 1 (S.sActive i)) (Head.lin (-1) C_NSUBJ))]

/-! ## §6 — Canonical order + duplicate rejection (`air.rs` ordering block).

Identity STRICTLY increases across ACTIVE slots. Strictness is what rejects a duplicate;
monotonicity is what makes `subjects_root` a function of the SET rather than of the host's order. -/

/-- The comparison head `d = id[i+1] − id[i] − 1`. -/
def ordDiffHead (S : ComposeShape) (i : Nat) : Head :=
  ((Head.lin 1 (S.sId (i + 1))).addLin (-1) (S.sId i)).addConst (-1)

/-- The `i`-th ordering comparison: `forced_ge0(d)` plus `active[i+1] ⇒ ge`. -/
def orderGates (S : ComposeShape) (i : Nat) : List VmConstraint2 :=
  forcedGe0 (S.oGe i) (ordDiffHead S i) (S.oBits i)
  ++ [cgH ((Head.lin 1 (S.sActive (i + 1))).addProd (-1) [S.sActive (i + 1), S.oGe i])]

/-! ## §7 — A ROLE IS A KEY (`air.rs` uniqueness block).

Pairwise distinct among ACTIVE subjects, so `role ↦ subject` is a FUNCTION and the prover cannot
choose which subject a rule term reads. -/

/-- K1 — `−both + active_i·active_j`: the pair's joint-activity product column. -/
def ruBothHead (S : ComposeShape) (t i j : Nat) : Head :=
  (Head.lin (-1) (S.ruBoth t)).addProd 1 [S.sActive i, S.sActive j]

/-- K2 — `role_i − role_j − diff`: the pair's role-difference column. -/
def ruDiffHead (S : ComposeShape) (t i j : Nat) : Head :=
  ((Head.lin 1 (S.sRole i)).addLin (-1) (S.sRole j)).addLin (-1) (S.ruDiff t)

/-- The `t`-th pair's three gates: the activity product, the role difference, and the
conditional-nonzero that forbids two active subjects sharing a role. -/
def roleKeyGates (S : ComposeShape) (t : Nat) (i j : Nat) : List VmConstraint2 :=
  [ cgH (ruBothHead S t i j)
  , cgH (ruDiffHead S t i j)
  , condNonzero (S.ruBoth t) (S.ruDiff t) (S.ruInv t) ]

/-! ## §8 — `fetch`: resolve `(role, param)` to a value IN-CIRCUIT (`air.rs::fetch`).

Two gated one-hots — one over SUBJECT slots pinned by ROLE (never by slot index: slot order is an
identity-sort artifact a ruleset author cannot predict), one over PARAM slots pinned by index. The
read is `Σ_j Σ_q sel_j · selp_q · param[j][q]`, degree 3. Refusals that ride here: a role no ACTIVE
subject occupies, and a param slot at or past `param_count`. -/

/-- F1 — `Σ_j sel_j − term_active`: exactly one subject slot is selected when the term is active. -/
def fSumHead (S : ComposeShape) (fb ta : Nat) : Head :=
  (List.range S.n).foldl (fun h j => h.addLin 1 (S.fSel fb j)) (Head.lin (-1) ta)

/-- F2 — `Σ_j sel_j·role_j − term_active·role_col`: the selection is pinned BY ROLE. -/
def fRoleHead (S : ComposeShape) (fb ta rc : Nat) : Head :=
  (List.range S.n).foldl (fun h j => h.addProd 1 [S.fSel fb j, S.sRole j])
    (Head.zero.addProd (-1) [ta, rc])

/-- F3 — `Σ_j sel_j·active_j − term_active`: the selected subject must be ACTIVE (a role no active
subject occupies is UNRESOLVABLE, fail-closed). -/
def fActiveHead (S : ComposeShape) (fb ta : Nat) : Head :=
  (List.range S.n).foldl (fun h j => h.addProd 1 [S.fSel fb j, S.sActive j]) (Head.lin (-1) ta)

/-- F4 — `Σ_q selp_q − term_active`. -/
def fpSumHead (S : ComposeShape) (fb ta : Nat) : Head :=
  (List.range S.p).foldl (fun h q => h.addLin 1 (S.fSelP fb q)) (Head.lin (-1) ta)

/-- F5 — `Σ_q q·selp_q − term_active·param_col`: the param selection is pinned BY INDEX. -/
def fpIdxHead (S : ComposeShape) (fb ta pc : Nat) : Head :=
  (List.range S.p).foldl (fun h (q : Nat) => h.addLin (q : ℤ) (S.fSelP fb q))
    (Head.zero.addProd (-1) [ta, pc])

/-- F6 — `Σ_q selp_q·pactive_q − term_active`: the addressed param slot is within `param_count`. -/
def fpActiveHead (S : ComposeShape) (fb ta : Nat) : Head :=
  (List.range S.p).foldl (fun h q => h.addProd 1 [S.fSelP fb q, S.paCol q]) (Head.lin (-1) ta)

/-- F7 — THE READ: `Σ_j Σ_q sel_j·selp_q·param[j][q] − val` (degree 3). -/
def fReadHead (S : ComposeShape) (fb : Nat) : Head :=
  ((List.range S.n).foldl (fun h j =>
      (List.range S.p).foldl
        (fun h2 q => h2.addProd 1 [S.fSel fb j, S.fSelP fb q, S.sParam j q]) h)
    Head.zero).addLin (-1) (S.fVal fb)

/-- The nine gate families of one fetch block based at `fb`, gated by `termActive`. -/
def fetchGates (S : ComposeShape) (fb termActive roleCol paramCol : Nat) : List VmConstraint2 :=
  ((List.range S.n).map fun j => binGate (S.fSel fb j))
  ++ [ cgH (fSumHead S fb termActive)
     , cgH (fRoleHead S fb termActive roleCol)
     , cgH (fActiveHead S fb termActive) ]
  ++ ((List.range S.p).map fun q => binGate (S.fSelP fb q))
  ++ [ cgH (fpSumHead S fb termActive)
     , cgH (fpIdxHead S fb termActive paramCol)
     , cgH (fpActiveHead S fb termActive) ]
  ++ [ cgH (fReadHead S fb) ]

/-! ## §9 — The ruleset terms (`air.rs` linear + knot blocks). -/

/-- Linear term `t`: the three inactive⇒zero pins, its fetch, and `contrib = coeff · value`. -/
def linearGates (S : ComposeShape) (t : Nat) : List VmConstraint2 :=
  ([S.lRole t, S.lParam t, S.lCoeff t].map fun c =>
      cgH ((Head.lin 1 c).addProd (-1) [S.laCol t, c]))
  ++ fetchGates S (S.lFet t) (S.laCol t) (S.lRole t) (S.lParam t)
  ++ [cgH ((Head.lin (-1) (S.lContrib t)).addProd 1 [S.lCoeff t, S.fVal (S.lFet t)])]

/-- Knot `t`: five inactive⇒zero pins, TWO fetches, and **THE NONLINEARITY**
`contrib = coeff · va · vb` (degree 3) — the product of two subjects' state values, precisely what
the LINEAR `AffineLe`/`AffineEq` vocabulary cannot say. -/
def knotGates (S : ComposeShape) (t : Nat) : List VmConstraint2 :=
  ([S.kRoleA t, S.kParA t, S.kRoleB t, S.kParB t, S.kCoeff t].map fun c =>
      cgH ((Head.lin 1 c).addProd (-1) [S.kaCol t, c]))
  ++ fetchGates S (S.kFetA t) (S.kaCol t) (S.kRoleA t) (S.kParA t)
  ++ fetchGates S (S.kFetB t) (S.kaCol t) (S.kRoleB t) (S.kParB t)
  ++ [cgH ((Head.lin 1 (S.kContrib t)).addProd (-1)
        [S.kCoeff t, S.fVal (S.kFetA t), S.fVal (S.kFetB t)])]

/-! ## §10 — THE LAW. -/

/-- `outcome − Σ linear contributions − Σ knot contributions = 0`. -/
def lawHead (S : ComposeShape) : Head :=
  ((List.range S.k).foldl (fun h t => h.addLin (-1) (S.kContrib t))
    ((List.range S.l).foldl (fun h t => h.addLin (-1) (S.lContrib t))
      (Head.lin 1 S.cOut)))

/-- THE LAW as a gate. -/
def lawGate (S : ComposeShape) : VmConstraint2 := cgH (lawHead S)

/-! ## §11 — The four committed roots (`air.rs::wide_chain`). -/

/-- The canonical subjects stream, as column expressions (`reference.rs::subjects_stream`). -/
def subjStream (S : ComposeShape) : List EmittedExpr :=
  [.var C_NSUBJ, .var C_NPARAM]
  ++ (List.range S.n).flatMap fun i =>
       [.var (S.sActive i), .var (S.sId i), .var (S.sRole i)]
       ++ (List.range S.p).map fun q => EmittedExpr.var (S.sParam i q)

/-- The canonical ruleset stream (`reference.rs::ruleset_stream`). -/
def ruleStream (S : ComposeShape) : List EmittedExpr :=
  [.var S.cRid, .var S.cRver, .var C_NLIN, .var C_NKNOT]
  ++ ((List.range S.l).flatMap fun t =>
        [.var (S.laCol t), .var (S.lRole t), .var (S.lParam t), .var (S.lCoeff t)])
  ++ ((List.range S.k).flatMap fun t =>
        [.var (S.kaCol t), .var (S.kRoleA t), .var (S.kParA t), .var (S.kRoleB t),
         .var (S.kParB t), .var (S.kCoeff t)])

/-- The outcome stream. -/
def outStream (S : ComposeShape) : List EmittedExpr := [.var S.cOut]

/-- The explanation stream — the per-term contribution vector a "Why?" is checked against. -/
def explStream (S : ComposeShape) : List EmittedExpr :=
  ((List.range S.l).map fun t => EmittedExpr.var (S.lContrib t))
  ++ ((List.range S.k).map fun t => EmittedExpr.var (S.kContrib t))

/-- Block `b` of a stream, zero-padded to the absorb rate with LITERAL zeros. -/
def streamBlock (data : List EmittedExpr) (b : Nat) : List EmittedExpr :=
  (List.range ABSORB_RATE).map fun t =>
    (data[b * ABSORB_RATE + t]?).getD (.const 0)

/-- The 16 chip inputs of chain `c` block `b`: the accumulator half (the domain IV for block 0, the
previous block's 8 output columns otherwise) followed by the 8 data felts. -/
def chainInputs (S : ComposeShape) (c : Nat) (domain : ℤ) (data : List EmittedExpr) (b : Nat) :
    List EmittedExpr :=
  (if b = 0 then (iv8 domain).map EmittedExpr.const
   else (S.chainCols c (b - 1)).map EmittedExpr.var)
  ++ streamBlock data b

/-- Chain `c`'s WIDE chip lookups — one arity-16 `node8` site per 8-felt block, binding all 8 output
lanes (`chipLookupTupleN`; the soundness lever is `chip_lookup_sound_N`). -/
def chainLookups (S : ComposeShape) (c : Nat) (domain : ℤ) (data : List EmittedExpr) (blocks : Nat) :
    List VmConstraint2 :=
  (List.range blocks).map fun b =>
    .lookup ⟨TableId.poseidon2, chipLookupTupleN (chainInputs S c domain data b) (S.chainCols c b)⟩

/-! ## §12 — The public-input layout (`param-compose/src/pi.rs`).

`[0..16)` is the Custom-VK door's `[old_commit8 ‖ new_commit8]` state prefix — RAW public inputs the
EXECUTOR welds, bound by no constraint here (exactly the Rust `Builder::add_pi`). The 37 app PIs are
the ABI version, four counts, and the four 8-felt roots. -/

/-- The door's state-prefix width (`CUSTOM_PI_STATE_PREFIX_LEN`). -/
def APP_BASE : Nat := 16
/-- First root PI slot (`ROOTS_BASE`). -/
def ROOTS_BASE : Nat := APP_BASE + 5
/-- Total public inputs (`pi::public_input_count`). -/
def PI_COUNT : Nat := ROOTS_BASE + 4 * DIGEST_FELTS

/-- The five scalar PI bindings plus the four roots, in `pi.rs` order: `ruleset_root`,
`subjects_root`, `outcome_commitment`, `explanation_root`. -/
def piGates (S : ComposeShape) : List VmConstraint2 :=
  [ pinPi C_ABI APP_BASE
  , pinPi C_NSUBJ (APP_BASE + 1)
  , pinPi C_NPARAM (APP_BASE + 2)
  , pinPi C_NLIN (APP_BASE + 3)
  , pinPi C_NKNOT (APP_BASE + 4) ]
  ++ ([(1, 0), (0, 1), (2, 2), (3, 3)].flatMap fun (cd : Nat × Nat) =>
        (List.range DIGEST_FELTS).map fun t =>
          pinPi ((S.rootCols cd.1).getD t 0) (ROOTS_BASE + DIGEST_FELTS * cd.2 + t))

/-! ## §13 — THE DESCRIPTOR. -/

/-- The full constraint list, in emission order. -/
def paramComposeConstraints (S : ComposeShape) : List VmConstraint2 :=
  -- the committed shape/version scalars
  [cgH ((Head.lin 1 C_ABI).addConst (-ABI_VERSION))]
  ++ prefixFlagGates S.paBase S.p C_NPARAM
  ++ ((List.range S.n).flatMap fun i => subjectGates S i)
  ++ subjectPrefixGates S
  ++ ((List.range (S.n - 1)).flatMap fun i => orderGates S i)
  ++ (S.pairList.zipIdx.flatMap fun (e : (Nat × Nat) × Nat) => roleKeyGates S e.2 e.1.1 e.1.2)
  ++ prefixFlagGates S.laBase S.l C_NLIN
  ++ ((List.range S.l).flatMap fun t => linearGates S t)
  ++ prefixFlagGates S.kaBase S.k C_NKNOT
  ++ ((List.range S.k).flatMap fun t => knotGates S t)
  ++ [lawGate S]
  ++ chainLookups S 0 DOMAIN_SUBJECTS (subjStream S) S.blkSubj
  ++ chainLookups S 1 DOMAIN_RULESET (ruleStream S) S.blkRule
  ++ chainLookups S 2 DOMAIN_OUTCOME (outStream S) S.blkOut
  ++ chainLookups S 3 DOMAIN_EXPLANATION (explStream S) S.blkExpl
  ++ piGates S

/-- The descriptor's name — a function of the SHAPE alone, never of the ruleset or the content
(two unrelated rulesets share one VK; that is the whole point of the crate). -/
def paramComposeName (S : ComposeShape) : String :=
  "dregg-param-compose-v1-n" ++ toString S.n ++ "p" ++ toString S.p ++ "l" ++ toString S.l ++
  "k" ++ toString S.k ++ "i" ++ toString S.ib ++ "::poseidon2-node8"

/-- **`paramComposeDesc S`** — the Lean-authored parameter-composition AIR at shape `S`. The chip
table (`TID_P2`) is IMPLICITLY present (Presence-detected from the wide lookups), so `tables` is
empty; there are no v1 hash sites and no v1 range carriers (the identity range check is an explicit
bit-decomposition, exactly as the Rust `range_nonneg` is). -/
def paramComposeDesc (S : ComposeShape) : EffectVmDescriptor2 :=
  { name        := paramComposeName S
  , traceWidth  := S.width
  , piCount     := PI_COUNT
  , tables      := []
  , constraints := paramComposeConstraints S
  , hashSites   := []
  , ranges      := [] }

/-! ## §14 — The minimal pinned instance.

`pcMin` is the smallest shape that exercises EVERY family: two subjects (so the ordering comparison
and the role-key pair both fire), two params (so the param one-hot is not a singleton), one linear
term and one knot (so both contribution kinds and the degree-3 read are present), at a 2-bit
identity namespace (`identity_bits_sound` holds: `1 ≤ 2 ≤ 28`). -/

/-- The minimal exercised shape. -/
def pcMin : ComposeShape := ⟨2, 2, 1, 1, 2⟩

/-- The DEPLOYED realistic shape (`lib.rs`'s `n4 p8 l8 k6` at the default 28-bit identity
namespace) — the one `entity-compose` builds. -/
def pcRealistic : ComposeShape := ⟨4, 8, 8, 6, 28⟩

#guard pcMin.identityBitsSound
#guard pcRealistic.identityBitsSound

-- Shape pins for the minimal instance.
#guard (paramComposeDesc pcMin).piCount == 53
#guard (paramComposeDesc pcMin).traceWidth == pcMin.width
#guard (paramComposeDesc pcMin).tables == []
#guard (paramComposeDesc pcMin).hashSites.length == 0
#guard (paramComposeDesc pcMin).ranges.length == 0

-- The fuel meter is a function of the SHAPE alone (`ComposeShape::hash_sites`), and it equals the
-- number of wide chip lookups the descriptor actually emits.
#guard ((paramComposeDesc pcMin).constraints.filter
          (fun c => match c with | .lookup _ => true | _ => false)).length == pcMin.hashSites
#guard ((paramComposeDesc pcRealistic).constraints.filter
          (fun c => match c with | .lookup _ => true | _ => false)).length == pcRealistic.hashSites

-- Every PI binding is emitted: 5 scalars + 4 roots × 8 lanes = 37 app PIs.
#guard ((paramComposeDesc pcMin).constraints.filter
          (fun c => match c with | .base (.piBinding _ _ _) => true | _ => false)).length == 37

-- Every wide chip lookup is a genuine 25-wide `node8` tuple (arity tag + 16 padded inputs + 8
-- digest lanes) — the shape `chip_lookup_sound_N` consumes.
#guard ((paramComposeDesc pcMin).constraints.filterMap
          (fun c => match c with | .lookup l => some l.tuple.length | _ => none)).all
        (· == 1 + CHIP_RATE + CHIP_OUT_LANES)

/-! ## §15 — THE BYTE-PIN (the Rust decoder ingests THIS string).

`emitVmJson2 (paramComposeDesc pcMin)` is pinned verbatim. This is the drift gate on the WHOLE
authoring chain: a change to any layout offset, any gate head, any stream order, any domain tag, any
PI index, or the `Head` lowering itself moves these bytes and breaks the `#guard`. The deployed-size
(`pcRealistic`) pin lives in the leaf `ParamComposeGolden.lean` (314 KiB — kept out of this module so
the refinement surface does not pay for it on every build). -/

/-- **`PARAM_COMPOSE_MIN_GOLDEN`** — the byte-pinned wire string of `paramComposeDesc pcMin`.
Exposed as a named raw-string `def` (not an inline literal) so the Rust wire canary
`circuit/tests/param_compose_descriptor.rs` can `include_str!` THIS module and split the
golden straight out of it — the Lean emission is then the only copy that exists, and a
hand-transcription hop cannot open between author and consumer. -/
def PARAM_COMPOSE_MIN_GOLDEN : String := r#"{"name":"dregg-param-compose-v1-n2p2l1k1i2::poseidon2-node8","ir":2,"trace_width":108,"public_input_count":53,"tables":[],"constraints":[{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":0}},"r":{"t":"const","v":-1}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":6}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":5}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":5}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":6}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"var","v":12},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":8}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":12}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":13}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":8}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":8}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":9}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":7}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":9}},"r":{"t":"var","v":14}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":10}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":10}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":10}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":10}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":11}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":11}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":11}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":11}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"var","v":15},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":20},"r":{"t":"add","l":{"t":"var","v":20},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":21},"r":{"t":"add","l":{"t":"var","v":21},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":16}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":20}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":21}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":16}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"var","v":16}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":17}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"var","v":17}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":15}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"var","v":17}},"r":{"t":"var","v":22}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":18}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":18}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":18}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"var","v":18}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":19}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":19}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":19}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"var","v":19}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":15}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"var","v":7}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":1}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":7}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":15}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"add","l":{"t":"var","v":23},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"var","v":24},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"var","v":25},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":26},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2},"r":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"var","v":16}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"var","v":8}}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":23}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":23}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":8}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":24}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":25}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":26}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":15}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"var","v":23}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":27}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":15}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":17}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":28}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":27}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":27},"r":{"t":"var","v":28}},"r":{"t":"var","v":29}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"add","l":{"t":"var","v":32},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":3}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":32}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":33}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"var","v":33}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":34}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"var","v":34}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":35}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"var","v":35}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":36},"r":{"t":"add","l":{"t":"var","v":36},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"var","v":37},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":36}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":37}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"var","v":33}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":36},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"var","v":17}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":36},"r":{"t":"var","v":7}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"var","v":15}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":38},"r":{"t":"add","l":{"t":"var","v":38},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":39},"r":{"t":"add","l":{"t":"var","v":39},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":38}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":39}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"var","v":34}}},"r":{"t":"mul","l":{"t":"const","v":0},"r":{"t":"var","v":38}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":39}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":38},"r":{"t":"var","v":5}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":39},"r":{"t":"var","v":6}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":36},"r":{"t":"var","v":38}},"r":{"t":"var","v":10}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":36},"r":{"t":"var","v":39}},"r":{"t":"var","v":11}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"var","v":38}},"r":{"t":"var","v":18}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"var","v":39}},"r":{"t":"var","v":19}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":40}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":41}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":35},"r":{"t":"var","v":40}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"add","l":{"t":"var","v":42},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":42}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":43}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"var","v":43}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":44}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"var","v":44}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":45}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"var","v":45}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":46}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"var","v":46}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":47}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"var","v":47}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":48},"r":{"t":"add","l":{"t":"var","v":48},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"add","l":{"t":"var","v":49},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":42}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":48}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":49}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"var","v":43}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":48},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"var","v":17}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":42}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":48},"r":{"t":"var","v":7}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"var","v":15}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":50},"r":{"t":"add","l":{"t":"var","v":50},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":51},"r":{"t":"add","l":{"t":"var","v":51},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":42}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":50}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":51}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"var","v":44}}},"r":{"t":"mul","l":{"t":"const","v":0},"r":{"t":"var","v":50}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":51}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":42}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":50},"r":{"t":"var","v":5}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":51},"r":{"t":"var","v":6}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":48},"r":{"t":"var","v":50}},"r":{"t":"var","v":10}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":48},"r":{"t":"var","v":51}},"r":{"t":"var","v":11}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"var","v":50}},"r":{"t":"var","v":18}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"var","v":51}},"r":{"t":"var","v":19}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":52}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"add","l":{"t":"var","v":53},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":54},"r":{"t":"add","l":{"t":"var","v":54},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":42}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":53}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":54}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"var","v":45}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":54},"r":{"t":"var","v":17}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":42}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"var","v":7}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":54},"r":{"t":"var","v":15}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":55},"r":{"t":"add","l":{"t":"var","v":55},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":56},"r":{"t":"add","l":{"t":"var","v":56},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":42}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":55}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":56}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"var","v":46}}},"r":{"t":"mul","l":{"t":"const","v":0},"r":{"t":"var","v":55}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":56}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":42}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":55},"r":{"t":"var","v":5}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"var","v":56},"r":{"t":"var","v":6}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"var","v":55}},"r":{"t":"var","v":10}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"var","v":56}},"r":{"t":"var","v":11}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":54},"r":{"t":"var","v":55}},"r":{"t":"var","v":18}}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":54},"r":{"t":"var","v":56}},"r":{"t":"var","v":19}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":57}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":58}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":47},"r":{"t":"var","v":52}},"r":{"t":"var","v":57}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":59}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":41}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":58}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":10223872},{"t":"const","v":10223873},{"t":"const","v":10223874},{"t":"const","v":10223875},{"t":"const","v":10223876},{"t":"const","v":10223877},{"t":"const","v":10223878},{"t":"const","v":10223879},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":7},{"t":"var","v":8},{"t":"var","v":9},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":15},{"t":"var","v":60},{"t":"var","v":61},{"t":"var","v":62},{"t":"var","v":63},{"t":"var","v":64},{"t":"var","v":65},{"t":"var","v":66},{"t":"var","v":67}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"var","v":60},{"t":"var","v":61},{"t":"var","v":62},{"t":"var","v":63},{"t":"var","v":64},{"t":"var","v":65},{"t":"var","v":66},{"t":"var","v":67},{"t":"var","v":16},{"t":"var","v":17},{"t":"var","v":18},{"t":"var","v":19},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":68},{"t":"var","v":69},{"t":"var","v":70},{"t":"var","v":71},{"t":"var","v":72},{"t":"var","v":73},{"t":"var","v":74},{"t":"var","v":75}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":10224128},{"t":"const","v":10224129},{"t":"const","v":10224130},{"t":"const","v":10224131},{"t":"const","v":10224132},{"t":"const","v":10224133},{"t":"const","v":10224134},{"t":"const","v":10224135},{"t":"var","v":30},{"t":"var","v":31},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":32},{"t":"var","v":33},{"t":"var","v":34},{"t":"var","v":35},{"t":"var","v":76},{"t":"var","v":77},{"t":"var","v":78},{"t":"var","v":79},{"t":"var","v":80},{"t":"var","v":81},{"t":"var","v":82},{"t":"var","v":83}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"var","v":76},{"t":"var","v":77},{"t":"var","v":78},{"t":"var","v":79},{"t":"var","v":80},{"t":"var","v":81},{"t":"var","v":82},{"t":"var","v":83},{"t":"var","v":42},{"t":"var","v":43},{"t":"var","v":44},{"t":"var","v":45},{"t":"var","v":46},{"t":"var","v":47},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":84},{"t":"var","v":85},{"t":"var","v":86},{"t":"var","v":87},{"t":"var","v":88},{"t":"var","v":89},{"t":"var","v":90},{"t":"var","v":91}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":10224384},{"t":"const","v":10224385},{"t":"const","v":10224386},{"t":"const","v":10224387},{"t":"const","v":10224388},{"t":"const","v":10224389},{"t":"const","v":10224390},{"t":"const","v":10224391},{"t":"var","v":59},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":92},{"t":"var","v":93},{"t":"var","v":94},{"t":"var","v":95},{"t":"var","v":96},{"t":"var","v":97},{"t":"var","v":98},{"t":"var","v":99}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":10224640},{"t":"const","v":10224641},{"t":"const","v":10224642},{"t":"const","v":10224643},{"t":"const","v":10224644},{"t":"const","v":10224645},{"t":"const","v":10224646},{"t":"const","v":10224647},{"t":"var","v":41},{"t":"var","v":58},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":100},{"t":"var","v":101},{"t":"var","v":102},{"t":"var","v":103},{"t":"var","v":104},{"t":"var","v":105},{"t":"var","v":106},{"t":"var","v":107}]},{"t":"pi_binding","row":"first","col":0,"pi_index":16},{"t":"pi_binding","row":"first","col":1,"pi_index":17},{"t":"pi_binding","row":"first","col":2,"pi_index":18},{"t":"pi_binding","row":"first","col":3,"pi_index":19},{"t":"pi_binding","row":"first","col":4,"pi_index":20},{"t":"pi_binding","row":"first","col":84,"pi_index":21},{"t":"pi_binding","row":"first","col":85,"pi_index":22},{"t":"pi_binding","row":"first","col":86,"pi_index":23},{"t":"pi_binding","row":"first","col":87,"pi_index":24},{"t":"pi_binding","row":"first","col":88,"pi_index":25},{"t":"pi_binding","row":"first","col":89,"pi_index":26},{"t":"pi_binding","row":"first","col":90,"pi_index":27},{"t":"pi_binding","row":"first","col":91,"pi_index":28},{"t":"pi_binding","row":"first","col":68,"pi_index":29},{"t":"pi_binding","row":"first","col":69,"pi_index":30},{"t":"pi_binding","row":"first","col":70,"pi_index":31},{"t":"pi_binding","row":"first","col":71,"pi_index":32},{"t":"pi_binding","row":"first","col":72,"pi_index":33},{"t":"pi_binding","row":"first","col":73,"pi_index":34},{"t":"pi_binding","row":"first","col":74,"pi_index":35},{"t":"pi_binding","row":"first","col":75,"pi_index":36},{"t":"pi_binding","row":"first","col":92,"pi_index":37},{"t":"pi_binding","row":"first","col":93,"pi_index":38},{"t":"pi_binding","row":"first","col":94,"pi_index":39},{"t":"pi_binding","row":"first","col":95,"pi_index":40},{"t":"pi_binding","row":"first","col":96,"pi_index":41},{"t":"pi_binding","row":"first","col":97,"pi_index":42},{"t":"pi_binding","row":"first","col":98,"pi_index":43},{"t":"pi_binding","row":"first","col":99,"pi_index":44},{"t":"pi_binding","row":"first","col":100,"pi_index":45},{"t":"pi_binding","row":"first","col":101,"pi_index":46},{"t":"pi_binding","row":"first","col":102,"pi_index":47},{"t":"pi_binding","row":"first","col":103,"pi_index":48},{"t":"pi_binding","row":"first","col":104,"pi_index":49},{"t":"pi_binding","row":"first","col":105,"pi_index":50},{"t":"pi_binding","row":"first","col":106,"pi_index":51},{"t":"pi_binding","row":"first","col":107,"pi_index":52}],"hash_sites":[],"ranges":[]}"#

#guard emitVmJson2 (paramComposeDesc pcMin) == PARAM_COMPOSE_MIN_GOLDEN

#assert_axioms paramComposeDesc

end Dregg2.Circuit.Emit.ParamComposeEmit
