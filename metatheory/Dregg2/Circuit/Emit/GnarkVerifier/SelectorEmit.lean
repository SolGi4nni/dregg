/-
# Dregg2.Circuit.Emit.GnarkVerifier.SelectorEmit — the STARK Lagrange-selector derivation,
Lean-authored, emitted as genuine R1CS, refined to the deployed algebra by a ∀-theorem.

SUBSTRATE, said out loud: **this is Lean-authored AIR/R1CS.** The constraint template below
is EMITTED from the committed `BabyBearFr` extension gadgets (`inputExt`, `gExtMul`,
`gExtSub`, and the hinted-inverse `gExtInv` this module adds) over the `R1csFr` foundation;
no constraint here is hand-written in Go. The deployed `chain/gnark/stark_verify_native.go`
`computeStarkSelectorsNative` is the REFERENCE the emission is pinned against, not the source
of the constraints — and this leaf is exactly the Lean route the deployed
`emitted_verifier_full.go:bindBlockZeta` NAMES as its tractable replacement for the hand-Go
selector derivation ("a SelectorEmit leaf is the ζ-squaring chain those already build plus
two inverse pins, with a refinement theorem `gHolds (selectorsData db) asg ↔ sel =
selectorsAtPoint ζ db`").

THE DEPLOYED ALGEBRA (`computeStarkSelectorsNative`, stark_verify_native.go:379;
domain.rs:262-271 with unshifted = ζ over the trace domain, shift ONE, size `2^db`):

    E            = ζ^{2^db}                         -- ExtExpPow2(ζ, db), db squarings
    Z_H(ζ)       = E − 1
    isTransition = ζ − g^{-1}                       -- g = bbTwoAdicGenerator(db)
    isFirstRow   = Z_H · (ζ − 1)^{-1}
    isLastRow    = Z_H · isTransition^{-1}

The two field inverses are the deployed `ExtInv` gadget (stark_verify_native.go:147): a
host-hinted witness `inv` PINNED by the constraint `a·inv = 1` (`ExtMul(a, inv) == 1`),
fail-closed at the degenerate points (ζ = 1 or ζ = g^{-1}) where `a = 0` has no satisfying
witness. This leaf mirrors that exactly: the honest witness fills `inv` with the Fermat
inverse `extInvV a` (the Lean twin of the deployed `bbExtInvRef`), and the emitted circuit
CONSTRAINS `gExtMul(a, inv) == one` — so the refinement rides the constraint, not the hint.

Deliverables:

  * **`emitSelectors db` / `selectorsData db ζ c₀ c₁ c₂`** — the compact ReplayTemplate:
    inputs `[ζ]` (canonical), outputs `[isFirstRow, isLastRow, isTransition]` (the three
    claimed selector triples `c₀ c₁ c₂`), `db` selecting the template (the squaring count
    and the constant `g^{-1}`). The ζ-squaring chain + two `gExtInv` pins + three output
    pins, emitted from the committed `BabyBearFr` gadgets.
  * **`selectorsV ζ db`** — the ℕ/`ExtV` value mirror of `computeStarkSelectorsNative`,
    `#guard`-KAT'd BIT-EXACT against the deployed Go on the REAL fixture ζ for every `db`
    the shrink uses (`{0, 9, 15, 16}`).
  * **`selectorTemplate_refines`** — the ∀-theorem, both polarities: for ALL canonical
    ζ and claimed triples, under the honest witness and the honest-inverse pins (the
    non-degeneracy the deployed `ExtInv` enforces), the LOWERED genuine R1CS of the emitted
    template is satisfied IFF the claimed triple equals `selectorsV ζ db` — the deployed
    algebra at that ζ/db.
  * **`selectorTemplate_refines_emitted`** — the same iff at the serialized wire form, via
    the proven `emit_faithful` round trip.
  * **`selectorTemplate_reject`** — the reject polarity (non-vacuity): a claimed triple that
    DISAGREES with the derivation makes the emitted R1CS UNSATISFIABLE under the honest
    witness.
  * **`selectorsDbJson db`** committed at `chain/gnark/emitted/selectors_db{0,9,15,16}.json`,
    byte-pinned (length + FNV-1a).

Classified seam (named, not silent — the `BabyBearFr`/`FriFoldEmit` ledger): the ∀-theorem
quantifies over the HONEST hint fill (the builder's generated witness — the Lean twin of
gnark's hint solver / `test.IsSolved`), and takes the two honest-inverse pins as hypotheses
(the `ExtInv` non-degeneracy `a·inv = 1`, discharged by `decide` at the real ζ — see the
KAT). Range checks are realized as bit decomposition (deployed gnark: lookup argument), the
same semantic contract already named in `BabyBearFr`. The frontend→R1CS leg inherits
`R1csFr.lower_sound` regardless.
-/
import Dregg2.Circuit.Emit.GnarkVerifier.FriFoldEmit
import Dregg2.Circuit.Emit.GnarkVerifier.EmitJson

namespace Dregg2.Circuit.Emit.GnarkVerifier.Selector

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.BabyBearFr
open Dregg2.Circuit.Emit.GnarkVerifier.FriFold
  (ginvT ginvT_lt ExtCanon constBB extAssertEqM
   asgOf wLt wLt_mono eval_congr asg_prefix
   StepTo BBv GEv inputExt_spec gExtMul_spec gExtSub_spec)

/-! ## §1 Value layer — the deployed selector algebra, mirrored over `ExtV`.

Ground truth: `computeStarkSelectorsRef` (stark_verify_native_ref.go:66) /
`computeStarkSelectorsNative` (stark_verify_native.go:379). All `#guard` literals below are
output of RUNNING the deployed Go on the real fixture ζ (see §7 KAT). -/

/-- A base constant embedded as an `ExtV` (the Go `BBExt{c, 0, 0, 0}`). -/
def extConst (c : ℕ) : ExtV := ⟨c, 0, 0, 0⟩

/-- `bbExtExpPow2Ref` (stark_verify_native_ref.go:26): `ζ^{2^db}` by `db` squarings. -/
def extExpV : ℕ → ExtV → ExtV
  | 0, v => v
  | k + 1, v => extExpV k (extMulV v v)

/-- Square-and-multiply over the extension, LSB-first (fuel-structural, mirrors
`BabyBearFr`'s `modPowAux` at the extension). -/
def extInvAux : ℕ → ExtV → ℕ → ExtV → ExtV
  | 0, _, _, acc => acc
  | f + 1, base, e, acc =>
      extInvAux f (extMulV base base) (e / 2) (if e % 2 == 1 then extMulV acc base else acc)

/-- The Fermat exponent for the quartic extension inverse: `a^{p⁴ − 2} = a^{-1}`
(`bbExtInvRef`, stark_verify_native_ref.go:43; `p⁴ − 2` is a 124-bit number). -/
def extInvExp : ℕ := pBB ^ 4 - 2

/-- **The extension inverse** — `bbExtInvRef` by Fermat (124 fuel steps cover the 124-bit
exponent). The Lean twin of the deployed `ExtInv` gadget's host hint. -/
def extInvV (a : ExtV) : ExtV := extInvAux 124 a extInvExp (extConst 1)

/-- **The deployed selector triple** — `computeStarkSelectorsNative` at `(ζ, db)`:
`(isFirstRow, isLastRow, isTransition)`. -/
def selectorsV (zeta : ExtV) (db : ℕ) : ExtV × ExtV × ExtV :=
  let e := extExpV db zeta
  let zh := extSubV e (extConst 1)
  let trans := extSubV zeta (extConst (ginvT db))
  let zm1 := extSubV zeta (extConst 1)
  (extMulV zh (extInvV zm1), extMulV zh (extInvV trans), trans)

/-- The decidable spec check: the claimed triple IS the deployed derivation. -/
def selectorCheckV (zeta : ExtV) (db : ℕ) (c0 c1 c2 : ExtV) : Bool :=
  decide ((c0, c1, c2) = selectorsV zeta db)

/-! ### Value-layer canonicity (every derived coordinate is a genuine BabyBear residue). -/

/-- `extMulV` outputs canonical coordinates (each is `· % pBB`). -/
theorem extMulV_canon (a b : ExtV) : ExtCanon (extMulV a b) :=
  ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
   Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem extConst_canon_one : ExtCanon (extConst 1) := ⟨by decide, by decide, by decide, by decide⟩

/-- The extension inverse is canonical: the square-and-multiply invariant keeps `acc`
canonical (start `⟨1,0,0,0⟩`; each step either keeps `acc` or replaces it with an `extMulV`
output). -/
theorem extInvAux_canon : ∀ (f : ℕ) (base : ExtV) (e : ℕ) (acc : ExtV),
    ExtCanon acc → ExtCanon (extInvAux f base e acc)
  | 0, _, _, _, h => h
  | f + 1, base, e, acc, h => by
      unfold extInvAux
      exact extInvAux_canon f _ _ _ (by split <;> [exact extMulV_canon _ _; exact h])

theorem extInvV_canon (a : ExtV) : ExtCanon (extInvV a) :=
  extInvAux_canon 124 a extInvExp (extConst 1) extConst_canon_one

/-! ## §2 Circuit layer — the ζ-squaring chain, the `gExtInv` pin, the selector program,
built from the committed `BabyBearFr` gadgets in the deployed op order. -/

/-- A base constant as a tracked extension element (the Go `BBExt{c,0,0,0}` witness). -/
def extConstG (c : ℕ) : GExt := ⟨constBB c, constBB 0, constBB 0, constBB 0⟩

theorem extConstG_vals (c : ℕ) : (extConstG c).vals = extConst c := rfl

/-- A constant extension element is GOOD at any state (const wires are trivially bounded,
evaluate to their value, and the value is canonical for `c < pBB`). -/
theorem extConstG_gev (c : ℕ) (hc : c < pBB) (s : St) : GEv s (extConstG c) :=
  have h0 : (0 : ℕ) < pBB := by decide
  ⟨⟨trivial, rfl, hc⟩, ⟨trivial, rfl, h0⟩, ⟨trivial, rfl, h0⟩, ⟨trivial, rfl, h0⟩⟩

/-- `bb.ExtExpPow2(a, db)` (stark_verify_native.go:168): `db` in-circuit squarings via the
committed `gExtMul`. -/
def gExtExpPow2Aux : ℕ → GExt → M GExt
  | 0, acc => pure acc
  | k + 1, acc => gExtMul acc acc >>= fun acc' => gExtExpPow2Aux k acc'

def gExtExpPow2 (a : GExt) (db : ℕ) : M GExt := gExtExpPow2Aux db a

/-- **`gExtInv`** — the deployed `ExtInv` gadget (stark_verify_native.go:147): mint the
hinted inverse `inv` (canonical ingestion = `ExtAssertIsCanonical`), then CONSTRAIN
`gExtMul(a, inv) == one` (`ExtAssertIsEqual(ExtMul(a, inv), one)`). The honest witness fills
`inv` with the Fermat inverse of the tracked value `aval`. -/
def gExtInv (a : GExt) (aval : ExtV) : M GExt :=
  inputExt (extInvV aval) >>= fun inv =>
  gExtMul a inv >>= fun prod =>
  extAssertEqM prod (extConstG 1) >>= fun _ =>
  pure inv

/-- **The one-round selector-derivation program** — ingest ζ and the three claimed selector
triples (canonical), form `E = ζ^{2^db}`, `Z_H = E − 1`, `ζ − 1`, `isTransition = ζ − g^{-1}`,
the two hinted inverses (each pinned `a·inv = 1`), `isFirstRow = Z_H·(ζ−1)^{-1}`,
`isLastRow = Z_H·isTransition^{-1}`, and assert the three claimed triples equal the
derivation. Returns the four ingested triples (for emission metadata). -/
def selectorRoundM (db : ℕ) (zeta c0 c1 c2 : ExtV) : M (GExt × GExt × GExt × GExt) :=
  inputExt zeta >>= fun gz =>
  inputExt c0 >>= fun gc0 =>
  inputExt c1 >>= fun gc1 =>
  inputExt c2 >>= fun gc2 =>
  gExtExpPow2 gz db >>= fun ge =>
  gExtSub ge (extConstG 1) >>= fun zh =>
  gExtSub gz (extConstG 1) >>= fun zm1 =>
  gExtSub gz (extConstG (ginvT db)) >>= fun trans =>
  gExtInv zm1 (extSubV zeta (extConst 1)) >>= fun invZm1 =>
  gExtInv trans (extSubV zeta (extConst (ginvT db))) >>= fun invTrans =>
  gExtMul zh invZm1 >>= fun first =>
  gExtMul zh invTrans >>= fun lastRow =>
  extAssertEqM first gc0 >>= fun _ =>
  extAssertEqM lastRow gc1 >>= fun _ =>
  extAssertEqM trans gc2 >>= fun _ =>
  pure (gz, gc0, gc1, gc2)

/-- The built package run: circuit + generated honest witness + the input records. -/
def selectorsRun (db : ℕ) (zeta c0 c1 c2 : ExtV) : RunOut (GExt × GExt × GExt × GExt) :=
  runM (selectorRoundM db zeta c0 c1 c2)

def selectorsCircuit (db : ℕ) (zeta c0 c1 c2 : ExtV) : Circuit :=
  (selectorsRun db zeta c0 c1 c2).circ

/-- The generated honest witness (the Lean twin of gnark's hint solver fill). -/
def selectorsAsg (db : ℕ) (zeta c0 c1 c2 : ExtV) : Assignment :=
  (selectorsRun db zeta c0 c1 c2).asg

def idxOf (b : BB) : ℕ := match b.wire with | .var k => k | _ => 0

def extIdx (g : GExt) : List ℕ := [idxOf g.e0, idxOf g.e1, idxOf g.e2, idxOf g.e3]

/-- **The emission package** for the selector derivation at degree bits `db`. -/
def selectorsData (db : ℕ) (zeta c0 c1 c2 : ExtV) : GnarkCircuitData :=
  let ro := selectorsRun db zeta c0 c1 c2
  let (gz, gc0, gc1, gc2) := ro.out
  { name         := s!"stark_lagrange_selectors_db{db}_v1"
    publicInputs :=
      (extIdx gz).zipIdx.map (fun p => (s!"zeta_{p.2}", p.1))
        ++ (extIdx gc0).zipIdx.map (fun p => (s!"isFirstRow_{p.2}", p.1))
        ++ (extIdx gc1).zipIdx.map (fun p => (s!"isLastRow_{p.2}", p.1))
        ++ (extIdx gc2).zipIdx.map (fun p => (s!"isTransition_{p.2}", p.1))
    gadgets      :=
      [ ⟨s!"ComputeStarkSelectors_db{db}", extIdx gz⟩,
        ⟨"ExtAssertIsEqual_isFirstRow", extIdx gc0⟩,
        ⟨"ExtAssertIsEqual_isLastRow", extIdx gc1⟩,
        ⟨"ExtAssertIsEqual_isTransition", extIdx gc2⟩ ]
    circuit      := ro.circ }

/-- **`emitSelectors`** — the template selected by `db` alone (the emitted constraint
structure is value-independent; a canonical placeholder ζ + its true selectors give a
consistent, honestly-fillable instance). -/
def emitSelectors (db : ℕ) (zeta : ExtV) : GnarkCircuitData :=
  let s := selectorsV zeta db
  selectorsData db zeta s.1 s.2.1 s.2.2

/-! ## §3 Local run/framework helpers (small copies of `FriFoldEmit`'s private glue). -/

private theorem runBind {α β : Type} (m : M α) (f : α → M β) (s : St) :
    (m >>= f).run s = (f (m.run s).1).run (m.run s).2 := rfl

private theorem runAssertEq (l r : Wire) (s : St) :
    (assertEq l r).run s = ((), ⟨s.assigns, s.asserts ++ [(l, r)]⟩) := rfl

/-- One bind step, PROJECTION-FREE in the conclusion: given the head gadget's run equation,
`(m >>= f).run s` reduces to `(f a).run t`. Rewriting with this (then `beta_reduce`) keeps the
goal free of `Prod` projections, so the monadic run reduces in a single linear pass without
the whnf-defeq blowup the projection-laden `runBind`+`dsimp` chain incurs. -/
private theorem bindStep {α β : Type} (m : M α) (f : α → M β) {s t : St} {a : α}
    (h : m.run s = (a, t)) : (m >>= f).run s = (f a).run t := by
  rw [runBind, h]

private theorem runPure {α : Type} (a : α) (s : St) :
    (pure a : M α).run s = (a, s) := rfl

private theorem pBB_lt_r : pBB < rBN254 := by
  show (2013265921 : ℕ) < rBN254
  rw [rBN254]; norm_num

/-- ℕ-cast injectivity below the BN254 scalar modulus. -/
private theorem cast_inj_lt {x y : ℕ} (hx : x < rBN254) (hy : y < rBN254)
    (h : (x : Fr) = (y : Fr)) : x = y := by
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hx, ZMod.val_cast_of_lt hy] at h'

private theorem list_toArray_getD (l : List Fr) (v : ℕ) : l.toArray.getD v 0 = l.getD v 0 := by
  simp

/-- `extAssertEqM` adds NO mints and exactly the four per-lane equality asserts. -/
private theorem extAssertEqM_run (a b : GExt) (s : St) :
    (extAssertEqM a b).run s
      = ((), ⟨s.assigns, s.asserts ++
          [(a.e0.wire, b.e0.wire), (a.e1.wire, b.e1.wire),
           (a.e2.wire, b.e2.wire), (a.e3.wire, b.e3.wire)]⟩) := by
  simp only [extAssertEqM, runBind, runAssertEq, List.append_assoc, List.nil_append,
    List.cons_append]

/-- **`extAssertEqM` as an honest `StepTo`** when the two tracked triples carry equal
values: no mint, the four lane asserts hold under the honest witness. -/
private theorem extAssertEqM_stepto (x y : GExt) (s : St) (hx : GEv s x) (hy : GEv s y)
    (hv : x.vals = y.vals) : StepTo s ((extAssertEqM x y).run s).2 := by
  rw [extAssertEqM_run]
  have hval : x.e0.val = y.e0.val ∧ x.e1.val = y.e1.val ∧ x.e2.val = y.e2.val ∧ x.e3.val = y.e3.val := by
    simpa only [GExt.vals, ExtV.mk.injEq] using hv
  refine ⟨List.prefix_rfl, [(x.e0.wire, y.e0.wire), (x.e1.wire, y.e1.wire),
    (x.e2.wire, y.e2.wire), (x.e3.wire, y.e3.wire)], rfl, ?_⟩
  intro p hp
  have ev : ∀ (bx by' : BB), bx.wire.eval (asgOf s) = (bx.val : Fr) →
      by'.wire.eval (asgOf s) = (by'.val : Fr) → bx.val = by'.val →
      wLt bx.wire s.assigns.length → wLt by'.wire s.assigns.length →
      (wLt bx.wire s.assigns.length ∧ wLt by'.wire s.assigns.length)
        ∧ bx.wire.eval (asgOf s) = by'.wire.eval (asgOf s) := by
    intro bx by' ex ey exy wx wy
    exact ⟨⟨wx, wy⟩, by rw [ex, ey, exy]⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ev _ _ hx.b0.ev hy.b0.ev hval.1 hx.b0.wlt hy.b0.wlt
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ev _ _ hx.b1.ev hy.b1.ev hval.2.1 hx.b1.wlt hy.b1.wlt
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ev _ _ hx.b2.ev hy.b2.ev hval.2.2.1 hx.b2.wlt hy.b2.wlt
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ev _ _ hx.b3.ev hy.b3.ev hval.2.2.2 hx.b3.wlt hy.b3.wlt
  · exact absurd hp (List.not_mem_nil)

/-! ## §4 Gadget honest-run specs. -/

/-- **`gExtExpPow2` honest run**: `db` squarings thread honestly, the output tracks
`extExpV db a.vals` exactly. -/
theorem gExtExpPow2Aux_spec : ∀ (db : ℕ) (a : GExt) (s : St), GEv s a →
    ∃ out t, (gExtExpPow2Aux db a).run s = (out, t) ∧ StepTo s t ∧ GEv t out ∧
      out.vals = extExpV db a.vals
  | 0, a, s, ha => ⟨a, s, rfl, StepTo.refl s, ha, rfl⟩
  | db + 1, a, s, ha => by
      obtain ⟨sq, t1, hr1, hst1, hgesq, hvsq⟩ := gExtMul_spec a a s ha ha
      obtain ⟨out, t, hr, hst, hge, hval⟩ := gExtExpPow2Aux_spec db sq t1 hgesq
      refine ⟨out, t, ?_, hst1.trans hst, hge, ?_⟩
      · show (gExtMul a a >>= fun acc' => gExtExpPow2Aux db acc').run s = (out, t)
        rw [runBind, hr1]; exact hr
      · rw [hval, hvsq]; rfl

theorem gExtExpPow2_spec (a : GExt) (db : ℕ) (s : St) (ha : GEv s a) :
    ∃ out t, (gExtExpPow2 a db).run s = (out, t) ∧ StepTo s t ∧ GEv t out ∧
      out.vals = extExpV db a.vals :=
  gExtExpPow2Aux_spec db a s ha

/-- **`gExtInv` honest run**: given the honest-inverse pin `aval · extInvV aval = one`
(the `ExtInv` non-degeneracy the deployed gadget enforces), the whole gadget threads
honestly and the output tracks the Fermat inverse `extInvV aval`. -/
theorem gExtInv_spec (a : GExt) (aval : ExtV) (s : St) (ha : GEv s a) (haval : a.vals = aval)
    (hpin : extMulV aval (extInvV aval) = extConst 1) :
    ∃ out t, (gExtInv a aval).run s = (out, t) ∧ StepTo s t ∧ GEv t out ∧
      out.vals = extInvV aval := by
  obtain ⟨inv, t1, hr1, hst1, hgeinv, hvinv⟩ := inputExt_spec (extInvV aval) s (extInvV_canon aval)
  obtain ⟨prod, t2, hr2, hst2, hgeprod, hvprod⟩ := gExtMul_spec a inv t1 (ha.mono hst1) hgeinv
  have hprodone : prod.vals = (extConstG 1).vals := by
    rw [hvprod, haval, hvinv]; exact hpin
  have hpe : StepTo t2 ((extAssertEqM prod (extConstG 1)).run t2).2 :=
    extAssertEqM_stepto prod (extConstG 1) t2 hgeprod (extConstG_gev 1 (by decide) t2) hprodone
  refine ⟨inv, ((extAssertEqM prod (extConstG 1)).run t2).2, ?_,
    (hst1.trans hst2).trans hpe, ?_, hvinv⟩
  · show (inputExt (extInvV aval) >>= fun inv =>
        gExtMul a inv >>= fun prod =>
        extAssertEqM prod (extConstG 1) >>= fun _ => pure inv).run s = _
    rw [runBind, hr1, runBind, hr2, runBind]
    rfl
  · exact hgeinv.mono (hst2.trans hpe)

/-! ## §5 The one-round program's honest run — the composition of the gadget specs. -/

/-- The 12 output-pin lane asserts appended after the honest derivation. -/
def outPins (first lastRow trans gc0 gc1 gc2 : GExt) : List (Wire × Wire) :=
  [(first.e0.wire, gc0.e0.wire), (first.e1.wire, gc0.e1.wire),
   (first.e2.wire, gc0.e2.wire), (first.e3.wire, gc0.e3.wire)] ++
  [(lastRow.e0.wire, gc1.e0.wire), (lastRow.e1.wire, gc1.e1.wire),
   (lastRow.e2.wire, gc1.e2.wire), (lastRow.e3.wire, gc1.e3.wire)] ++
  [(trans.e0.wire, gc2.e0.wire), (trans.e1.wire, gc2.e1.wire),
   (trans.e2.wire, gc2.e2.wire), (trans.e3.wire, gc2.e3.wire)]

/-- **The honest run of the one-round selector program.** Composing the committed gadget
specs: everything up to the three output pins threads honestly (a `StepTo` from the empty
state `tpre`), the derived `first`/`lastRow`/`trans` are good at `tpre` and track EXACTLY
`selectorsV zeta db`, the claimed triples track `c0`/`c1`/`c2`, and the emitted circuit is
the honest prefix `tpre.asserts` followed by the 12 output-pin lane equalities. -/
theorem selectorRound_spec (db : ℕ) (zeta c0 c1 c2 : ExtV)
    (hz : ExtCanon zeta) (hc0 : ExtCanon c0) (hc1 : ExtCanon c1) (hc2 : ExtCanon c2)
    (hpin1 : extMulV (extSubV zeta (extConst 1)) (extInvV (extSubV zeta (extConst 1))) = extConst 1)
    (hpint : extMulV (extSubV zeta (extConst (ginvT db)))
      (extInvV (extSubV zeta (extConst (ginvT db)))) = extConst 1) :
    ∃ (gz gc0 gc1 gc2 first lastRow trans : GExt) (tpre : St),
      StepTo ⟨[], []⟩ tpre ∧
      GEv tpre first ∧ GEv tpre lastRow ∧ GEv tpre trans ∧
      GEv tpre gc0 ∧ GEv tpre gc1 ∧ GEv tpre gc2 ∧
      first.vals = (selectorsV zeta db).1 ∧
      lastRow.vals = (selectorsV zeta db).2.1 ∧
      trans.vals = (selectorsV zeta db).2.2 ∧
      gc0.vals = c0 ∧ gc1.vals = c1 ∧ gc2.vals = c2 ∧
      (selectorRoundM db zeta c0 c1 c2).run ⟨[], []⟩
        = ((gz, gc0, gc1, gc2),
           ⟨tpre.assigns, tpre.asserts ++ outPins first lastRow trans gc0 gc1 gc2⟩) := by
  obtain ⟨gz, t0, hr0, hst0, hgez, hvz⟩ := inputExt_spec zeta ⟨[], []⟩ hz
  obtain ⟨gc0, t1, hr1, hst1, hgec0, hvc0⟩ := inputExt_spec c0 t0 hc0
  obtain ⟨gc1, t2, hr2, hst2, hgec1, hvc1⟩ := inputExt_spec c1 t1 hc1
  obtain ⟨gc2, t3, hr3, hst3, hgec2, hvc2⟩ := inputExt_spec c2 t2 hc2
  have hgez3 : GEv t3 gz := hgez.mono (hst1.trans (hst2.trans hst3))
  obtain ⟨ge, t4, hr4, hst4, hgee, hve⟩ := gExtExpPow2_spec gz db t3 hgez3
  obtain ⟨zh, t5, hr5, hst5, hgezh, hvzh⟩ :=
    gExtSub_spec ge (extConstG 1) t4 hgee (extConstG_gev 1 (by decide) t4)
  have hgez5 : GEv t5 gz := hgez3.mono (hst4.trans hst5)
  obtain ⟨zm1, t6, hr6, hst6, hgezm1, hvzm1⟩ :=
    gExtSub_spec gz (extConstG 1) t5 hgez5 (extConstG_gev 1 (by decide) t5)
  have hgez6 : GEv t6 gz := hgez5.mono hst6
  obtain ⟨trans, t7, hr7, hst7, hgetr, hvtr⟩ :=
    gExtSub_spec gz (extConstG (ginvT db)) t6 hgez6 (extConstG_gev (ginvT db) (ginvT_lt db) t6)
  -- tracked values of the two inverse inputs
  have hvzm1' : zm1.vals = extSubV zeta (extConst 1) := by
    rw [hvzm1, hvz]; rfl
  have hvtr' : trans.vals = extSubV zeta (extConst (ginvT db)) := by
    rw [hvtr, hvz]; rfl
  obtain ⟨invZm1, t8, hr8, hst8, hgeiz, hviz⟩ :=
    gExtInv_spec zm1 (extSubV zeta (extConst 1)) t7 (hgezm1.mono hst7) hvzm1' hpin1
  obtain ⟨invTr, t9, hr9, hst9, hgeit, hvit⟩ :=
    gExtInv_spec trans (extSubV zeta (extConst (ginvT db))) t8 (hgetr.mono hst8) hvtr' hpint
  have hgezh9 : GEv t9 zh := hgezh.mono ((hst6.trans (hst7.trans hst8)).trans hst9)
  obtain ⟨first, t10, hr10, hst10, hgef, hvf⟩ :=
    gExtMul_spec zh invZm1 t9 hgezh9 (hgeiz.mono hst9)
  obtain ⟨lastRow, t11, hr11, hst11, hgel, hvl⟩ :=
    gExtMul_spec zh invTr t10 (hgezh9.mono hst10) (hgeit.mono hst10)
  -- carry the derived / claimed elements to the common state t11
  have hgef11 : GEv t11 first := hgef.mono hst11
  have hgel11 : GEv t11 lastRow := hgel
  have hgetr11 : GEv t11 trans :=
    hgetr.mono ((hst8.trans (hst9.trans hst10)).trans hst11)
  have hgec011 : GEv t11 gc0 :=
    hgec0.mono ((hst2.trans (hst3.trans (hst4.trans (hst5.trans (hst6.trans (hst7.trans
      (hst8.trans (hst9.trans hst10)))))))).trans hst11)
  have hgec111 : GEv t11 gc1 :=
    hgec1.mono ((hst3.trans (hst4.trans (hst5.trans (hst6.trans (hst7.trans (hst8.trans
      (hst9.trans hst10))))))).trans hst11)
  have hgec211 : GEv t11 gc2 :=
    hgec2.mono ((hst4.trans (hst5.trans (hst6.trans (hst7.trans (hst8.trans (hst9.trans
      hst10)))))).trans hst11)
  have hstAll : StepTo ⟨[], []⟩ t11 :=
    hst0.trans (hst1.trans (hst2.trans (hst3.trans (hst4.trans (hst5.trans (hst6.trans
      (hst7.trans (hst8.trans (hst9.trans (hst10.trans hst11))))))))))
  -- the derived tracked values equal the deployed selector triple
  have hfv : first.vals = (selectorsV zeta db).1 := by
    rw [hvf, hvzh, hve, hvz, hviz]; rfl
  have hlv : lastRow.vals = (selectorsV zeta db).2.1 := by
    rw [hvl, hvzh, hve, hvz, hvit]; rfl
  have htv : trans.vals = (selectorsV zeta db).2.2 := hvtr'
  refine ⟨gz, gc0, gc1, gc2, first, lastRow, trans, t11, hstAll,
    hgef11, hgel11, hgetr11, hgec011, hgec111, hgec211, hfv, hlv, htv, hvc0, hvc1, hvc2, ?_⟩
  -- reduce the run in a single linear pass via the projection-free `bindStep` (`rw` auto-betas
  -- the exposed continuation). The `runBind`+`dsimp` chain is superlinear (projection whnf-defeq)
  -- and a `congr`/`simp`-only close blows up; this is the cheap discipline.
  show (selectorRoundM db zeta c0 c1 c2).run ⟨[], []⟩ = _
  unfold selectorRoundM
  rw [bindStep _ _ hr0, bindStep _ _ hr1, bindStep _ _ hr2, bindStep _ _ hr3,
    bindStep _ _ hr4, bindStep _ _ hr5, bindStep _ _ hr6, bindStep _ _ hr7,
    bindStep _ _ hr8, bindStep _ _ hr9, bindStep _ _ hr10, bindStep _ _ hr11,
    bindStep _ _ (extAssertEqM_run first gc0 _), bindStep _ _ (extAssertEqM_run lastRow gc1 _),
    bindStep _ _ (extAssertEqM_run trans gc2 _), runPure]
  simp only [outPins, List.append_assoc]

/-! ## §6 THE REFINEMENT. -/

/-- **`selectorTemplate_refines`** — THE deliverable, at the R1CS level the gnark backend
consumes. For ALL canonical ζ and claimed selector triples, under the builder-generated
honest witness and the two honest-inverse pins (the `ExtInv` non-degeneracy the deployed
gadget enforces — ζ ≠ 1 and ζ ≠ g^{-1}, discharged by `decide` at the real ζ), the LOWERED
genuine R1CS of the emitted selector-derivation template is satisfied IFF the claimed triple
equals the deployed `computeStarkSelectorsNative` derivation `selectorsV ζ db`. A genuine
∀-theorem, riding `R1csFr.gHolds` (frontend ↔ R1CS) over the committed `BabyBearFr` gadgets —
no field arithmetic is re-authored here. -/
theorem selectorTemplate_refines (db : ℕ) (zeta c0 c1 c2 : ExtV)
    (hz : ExtCanon zeta) (hc0 : ExtCanon c0) (hc1 : ExtCanon c1) (hc2 : ExtCanon c2)
    (hpin1 : extMulV (extSubV zeta (extConst 1)) (extInvV (extSubV zeta (extConst 1))) = extConst 1)
    (hpint : extMulV (extSubV zeta (extConst (ginvT db)))
      (extInvV (extSubV zeta (extConst (ginvT db)))) = extConst 1) :
    gHolds (selectorsData db zeta c0 c1 c2) (selectorsAsg db zeta c0 c1 c2)
      ↔ selectorCheckV zeta db c0 c1 c2 = true := by
  obtain ⟨gz, gc0, gc1, gc2, first, lastRow, trans, tpre, hstep,
    hgef, hgel, hgetr, hgec0, hgec1, hgec2, hfv, hlv, htv, hvc0, hvc1, hvc2, hrun⟩ :=
    selectorRound_spec db zeta c0 c1 c2 hz hc0 hc1 hc2 hpin1 hpint
  have hcirc : (selectorsData db zeta c0 c1 c2).circuit
      = ⟨tpre.asserts ++ outPins first lastRow trans gc0 gc1 gc2⟩ := by
    simp only [selectorsData, selectorsRun, runM, hrun]
  have hasg : selectorsAsg db zeta c0 c1 c2 = asgOf tpre := by
    funext v
    simp only [selectorsAsg, selectorsRun, runM, hrun]
    exact list_toArray_getD tpre.assigns v
  -- coordinate identifications of derived / claimed values
  have hfC : ExtCanon first.vals := GEv.canon hgef
  have hlC : ExtCanon lastRow.vals := GEv.canon hgel
  have htC : ExtCanon trans.vals := GEv.canon hgetr
  -- unfold gHolds to frontend acceptance, split the assert list
  unfold gHolds
  rw [← R1csFr.gHolds, hcirc, hasg]
  show (∀ p ∈ tpre.asserts ++ outPins first lastRow trans gc0 gc1 gc2,
      p.1.eval (asgOf tpre) = p.2.eval (asgOf tpre)) ↔ _
  rw [List.forall_mem_append, and_iff_right (StepTo.sat_of_nil hstep)]
  -- per-GExt block: the four lane eval-equalities hold IFF the tracked values agree.
  have blk : ∀ (u w : GExt), GEv tpre u → GEv tpre w →
      (((u.e0.wire.eval (asgOf tpre) = w.e0.wire.eval (asgOf tpre)) ∧
        (u.e1.wire.eval (asgOf tpre) = w.e1.wire.eval (asgOf tpre)) ∧
        (u.e2.wire.eval (asgOf tpre) = w.e2.wire.eval (asgOf tpre)) ∧
        (u.e3.wire.eval (asgOf tpre) = w.e3.wire.eval (asgOf tpre)))
      ↔ u.vals = w.vals) := by
    intro u w hu hw
    rw [hu.b0.ev, hw.b0.ev, hu.b1.ev, hw.b1.ev, hu.b2.ev, hw.b2.ev, hu.b3.ev, hw.b3.ev]
    constructor
    · rintro ⟨e0, e1, e2, e3⟩
      have c0' := cast_inj_lt (lt_trans hu.b0.lt pBB_lt_r) (lt_trans hw.b0.lt pBB_lt_r) e0
      have c1' := cast_inj_lt (lt_trans hu.b1.lt pBB_lt_r) (lt_trans hw.b1.lt pBB_lt_r) e1
      have c2' := cast_inj_lt (lt_trans hu.b2.lt pBB_lt_r) (lt_trans hw.b2.lt pBB_lt_r) e2
      have c3' := cast_inj_lt (lt_trans hu.b3.lt pBB_lt_r) (lt_trans hw.b3.lt pBB_lt_r) e3
      show ExtV.mk u.e0.val u.e1.val u.e2.val u.e3.val = ExtV.mk w.e0.val w.e1.val w.e2.val w.e3.val
      rw [c0', c1', c2', c3']
    · intro huw
      obtain ⟨a0, a1, a2, a3⟩ :
          u.e0.val = w.e0.val ∧ u.e1.val = w.e1.val ∧ u.e2.val = w.e2.val ∧ u.e3.val = w.e3.val := by
        simpa only [GExt.vals, ExtV.mk.injEq] using huw
      exact ⟨by rw [a0], by rw [a1], by rw [a2], by rw [a3]⟩
  -- the 12 output pins reduce to three coordinate-wise equalities of tracked values
  have key : (∀ p ∈ outPins first lastRow trans gc0 gc1 gc2,
        p.1.eval (asgOf tpre) = p.2.eval (asgOf tpre))
      ↔ ((first.vals = gc0.vals) ∧ (lastRow.vals = gc1.vals) ∧ (trans.vals = gc2.vals)) := by
    constructor
    · intro h
      exact ⟨(blk first gc0 hgef hgec0).mp
          ⟨h (first.e0.wire, gc0.e0.wire) (by simp [outPins]),
           h (first.e1.wire, gc0.e1.wire) (by simp [outPins]),
           h (first.e2.wire, gc0.e2.wire) (by simp [outPins]),
           h (first.e3.wire, gc0.e3.wire) (by simp [outPins])⟩,
        (blk lastRow gc1 hgel hgec1).mp
          ⟨h (lastRow.e0.wire, gc1.e0.wire) (by simp [outPins]),
           h (lastRow.e1.wire, gc1.e1.wire) (by simp [outPins]),
           h (lastRow.e2.wire, gc1.e2.wire) (by simp [outPins]),
           h (lastRow.e3.wire, gc1.e3.wire) (by simp [outPins])⟩,
        (blk trans gc2 hgetr hgec2).mp
          ⟨h (trans.e0.wire, gc2.e0.wire) (by simp [outPins]),
           h (trans.e1.wire, gc2.e1.wire) (by simp [outPins]),
           h (trans.e2.wire, gc2.e2.wire) (by simp [outPins]),
           h (trans.e3.wire, gc2.e3.wire) (by simp [outPins])⟩⟩
    · rintro ⟨hf, hl, ht⟩
      obtain ⟨f0, f1, f2, f3⟩ := (blk first gc0 hgef hgec0).mpr hf
      obtain ⟨l0, l1, l2, l3⟩ := (blk lastRow gc1 hgel hgec1).mpr hl
      obtain ⟨u0, u1, u2, u3⟩ := (blk trans gc2 hgetr hgec2).mpr ht
      intro p hp
      simp only [outPins, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        or_assoc] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [f0, f1, f2, f3, l0, l1, l2, l3, u0, u1, u2, u3]
  rw [key]
  -- rewrite tracked values into the deployed selector triple / claimed triples
  rw [hfv, hlv, htv, hvc0, hvc1, hvc2]
  -- close the iff to the decidable spec check
  simp only [selectorCheckV, decide_eq_true_eq, Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- The same refinement at the EMITTED wire form (composing the foundation's proven
`emit_faithful`): the bytes the JSON grammar renders denote exactly the selector-derivation
spec. -/
theorem selectorTemplate_refines_emitted (db : ℕ) (zeta c0 c1 c2 : ExtV)
    (hz : ExtCanon zeta) (hc0 : ExtCanon c0) (hc1 : ExtCanon c1) (hc2 : ExtCanon c2)
    (hpin1 : extMulV (extSubV zeta (extConst 1)) (extInvV (extSubV zeta (extConst 1))) = extConst 1)
    (hpint : extMulV (extSubV zeta (extConst (ginvT db)))
      (extInvV (extSubV zeta (extConst (ginvT db)))) = extConst 1) :
    satisfiedEmitted (emit (selectorsData db zeta c0 c1 c2)) (selectorsAsg db zeta c0 c1 c2)
      ↔ selectorCheckV zeta db c0 c1 c2 = true :=
  (emit_faithful (selectorsData db zeta c0 c1 c2) (selectorsAsg db zeta c0 c1 c2)).symm.trans
    (selectorTemplate_refines db zeta c0 c1 c2 hz hc0 hc1 hc2 hpin1 hpint)

/-- **The reject polarity** (non-vacuity): a claimed selector triple that DISAGREES with the
deployed derivation makes the emitted circuit UNSATISFIABLE under the honest witness — a
wrong `isFirstRow`/`isLastRow`/`isTransition` at ζ cannot pass. -/
theorem selectorTemplate_reject (db : ℕ) (zeta c0 c1 c2 : ExtV)
    (hz : ExtCanon zeta) (hc0 : ExtCanon c0) (hc1 : ExtCanon c1) (hc2 : ExtCanon c2)
    (hpin1 : extMulV (extSubV zeta (extConst 1)) (extInvV (extSubV zeta (extConst 1))) = extConst 1)
    (hpint : extMulV (extSubV zeta (extConst (ginvT db)))
      (extInvV (extSubV zeta (extConst (ginvT db)))) = extConst 1)
    (hne : (c0, c1, c2) ≠ selectorsV zeta db) :
    ¬ gHolds (selectorsData db zeta c0 c1 c2) (selectorsAsg db zeta c0 c1 c2) := by
  rw [selectorTemplate_refines db zeta c0 c1 c2 hz hc0 hc1 hc2 hpin1 hpint]
  simp only [selectorCheckV, decide_eq_true_eq]
  exact hne

#assert_axioms gExtExpPow2_spec
#assert_axioms gExtInv_spec
#assert_axioms selectorRound_spec
#assert_axioms selectorTemplate_refines
#assert_axioms selectorTemplate_refines_emitted
#assert_axioms selectorTemplate_reject

/-! ## §7 KAT — the emitted value spec is BIT-EXACT with the deployed Go on the REAL fixture.

The real transcript ζ (`chain/gnark/fixtures/apex_shrink_fri_real.json`, extracted by the
harness `extractShrinkStark(...).ch.zeta`) and the `computeStarkSelectorsRef` output at every
degree bits the shrink uses (`{0, 9, 15, 16}` — `degree_bits = [9,9,16,15,15,0]`). All
literals are the deployed Go's own output (dumped 2026-08-08, at the re-minted apex-shrink
fixture: the apex-VK flag day moved both the degree bits and the transcript ζ). -/

/-- The real fixture transcript ζ. -/
def katZeta : ExtV := ⟨99790091, 1104783006, 255303953, 1593865295⟩

-- db 9 — the full triple, bit-exact vs `computeStarkSelectorsNative(bb, zeta, 9)`.
#guard selectorsV katZeta 9 ==
  (⟨125572954, 1029063903, 706937462, 1728905076⟩,
   ⟨1924382664, 401512721, 1434662666, 220747139⟩,
   ⟨251380813, 1104783006, 255303953, 1593865295⟩)
-- db 15
#guard selectorsV katZeta 15 ==
  (⟨1694686603, 684106744, 1116876170, 1147746015⟩,
   ⟨938325115, 775150034, 882591307, 475039212⟩,
   ⟨701749077, 1104783006, 255303953, 1593865295⟩)
-- db 16 — the tallest trace the re-minted shrink proof carries.
#guard selectorsV katZeta 16 ==
  (⟨1825836338, 1781978203, 678681319, 1035663521⟩,
   ⟨943523277, 774095624, 1129234042, 949366847⟩,
   ⟨572113979, 1104783006, 255303953, 1593865295⟩)
-- db 0 — the degenerate trace height: E = ζ, Z_H = ζ − 1, both denominators equal, selectors = 1.
#guard selectorsV katZeta 0 ==
  (extConst 1, extConst 1, ⟨99790090, 1104783006, 255303953, 1593865295⟩)

-- The `E = ζ^{2^db}` vanishing recompute (`sel.zetaPow2Db`), bit-exact per db.
#guard extExpV 9 katZeta == ⟨870772733, 920256621, 638406872, 1995050955⟩
#guard extExpV 15 katZeta == ⟨752083680, 676024996, 786371405, 277213116⟩
#guard extExpV 16 katZeta == ⟨1317425510, 1082945534, 249831723, 1192034363⟩

-- The generator inverses `g^{-1} = bbInvRef(bbTwoAdicGeneratorRef(db))` (the `isTransition`
-- shift), bit-exact vs the deployed table.
#guard ginvT 9 == 1861675199
#guard ginvT 15 == 1411306935
#guard ginvT 16 == 1540942033
#guard ginvT 0 == 1

-- Non-vacuity of the refinement hypotheses: the honest-inverse pins `a · extInvV a = 1`
-- HOLD at the real ζ for both denominators, for every db the shrink uses — so
-- `selectorTemplate_refines` fires on the real fixture (its hypotheses are discharged here).
#guard [0, 9, 15, 16].all fun db =>
  (extMulV (extSubV katZeta (extConst 1)) (extInvV (extSubV katZeta (extConst 1))) == extConst 1)
  && (extMulV (extSubV katZeta (extConst (ginvT db)))
      (extInvV (extSubV katZeta (extConst (ginvT db)))) == extConst 1)

-- The claimed triple IS accepted by the spec check at the real ζ, and a tampered
-- isFirstRow is rejected (both polarities, decidable).
#guard selectorCheckV katZeta 9 (selectorsV katZeta 9).1 (selectorsV katZeta 9).2.1 (selectorsV katZeta 9).2.2
#guard ¬ selectorCheckV katZeta 9 ⟨0, 0, 0, 0⟩ (selectorsV katZeta 9).2.1 (selectorsV katZeta 9).2.2

/-! ## §8 The emitted JSON artifacts.

One template per distinct degree bits the shrink uses (`{0, 9, 15, 16}`), committed at
`chain/gnark/emitted/selectors_db{N}.json`. The emitted constraint STRUCTURE depends only on
`db` (the squaring count + the constant `g^{-1}`) — ζ enters as an INPUT variable, so the
0/9/15 bytes survived the 2026-08-08 fixture re-mint that moved ζ unchanged, and only the
paired WITNESS fixtures (`scripts/gen_selectors_witness.lean`) had to be re-dumped. The
placeholder ζ is the real fixture ζ and the claimed triple its true derivation, so each
template is a consistent, honestly-fillable instance. Byte pins are length + FNV-1a of the
exact rendered string. -/

/-- FNV-1a over the UTF-8 bytes — the byte-pin digest. -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

/-- The emitted template bytes for degree bits `db` (committed at
`chain/gnark/emitted/selectors_db{db}.json`). -/
def selectorsDbJson (db : ℕ) : String :=
  Dregg2.Circuit.Emit.GnarkVerifier.emitGnarkJson (emitSelectors db katZeta)

-- **Byte pins** of the committed artifacts `chain/gnark/emitted/selectors_db{0,9,15,16}.json`:
-- exact length + FNV-1a digest of the rendered string. Any byte drift in an emitted template
-- (a changed squaring count, a wrong `g^{-1}` constant, a re-ordered gadget) flips the digest.
#guard (selectorsDbJson 0).length == 1406036
#guard fnv1a (selectorsDbJson 0) == 17056074594331056466
#guard (selectorsDbJson 9).length == 2749975
#guard fnv1a (selectorsDbJson 9) == 9381981038340892017
#guard (selectorsDbJson 15).length == 3646187
#guard fnv1a (selectorsDbJson 15) == 2043968993851460074
#guard (selectorsDbJson 16).length == 3797142
#guard fnv1a (selectorsDbJson 16) == 7875364795002385664

end Dregg2.Circuit.Emit.GnarkVerifier.Selector
