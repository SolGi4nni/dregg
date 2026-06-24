# INTENT-REFS — Monoidal Adjunctions, Projection Formulas & Drinfeld Centers

**Pillar:** the formalism behind making the **receipt ⊣ intent adjunction *monoidal*** — so that escrow/conservation
*composes across fulfillment* — and behind **standing offers / AMM liquidity as central objects**.
**Companion to:** [`INTENT-AS-CO-RECEIPT.md`](./INTENT-AS-CO-RECEIPT.md) (the spine), [`INTENT-REFS-resources.md`](./INTENT-REFS-resources.md)
(the resource SMC this sits over), [`PHASE-2-INTENT-SPEC.md`](./PHASE-2-INTENT-SPEC.md) (the Phase-2 build it extends).
**Status:** reference map for **Phase 3+** (the monoidal upgrade). Produced by the `study-monoidal-centers` workflow
(2026-06-03): deep-read + mathlib survey + Kagi paper-hunt + spine-mapping + synthesis + adversarial critique.
Where the synthesis and critique disagreed, **this doc records the critique's corrected verdict** — flagged ⚠.

**Anchor paper:** Flake–Laugwitz–Posur, *Projection Formulas and Induced Functors on Centers of Monoidal
Categories*, arXiv [2402.10094](https://arxiv.org/abs/2402.10094) `[in library: pdfs/2402.10094v1.pdf]`.

---

## 0. The one-sentence frame

> A strong monoidal `G : C → D` does **not** push centers forward (`Z(C) → Z(D)`), just as a ring map doesn't
> restrict to centers. The fix is the **right adjoint `R`**, which induces a **braided-lax** center functor
> `Z(R) : Z(D) → Z(C)` — but **only when the projection formula holds** (`lproj : A ⊗ RX ⥲ R(GA ⊗ X)` is iso).

Read onto the spine: `Predicate ⊣ Witness` is the adjunction *idea*; the **center** is the locus of objects that
**commute past every turn** (standing offers / conserved-central quantities); the **projection formula** is the exact
hypothesis under which **escrow + intent transport along fulfillment**, and the transport is **lax** (escrow composes
up to coherence, invertible exactly when the projection formula holds) and **braided** (the half-braiding is the
"commutes-past-every-turn" datum). Two dregg targets throughout:

- **(a) monoidal receipt⊣intent + escrow compositionality** — `lproj_{A,X} : A ⊗ RX → R(GA ⊗ X)` *is* "combine a
  resource `A` with an escrowed demand `RX`, then fulfill = fulfill the combined demand `R(A⊗X)`."
- **(b) standing-offer/AMM-as-central-object + the escrow monad** — a commutative central monoid `M` and its monad
  `T_M = (– ⊗ M)`.

---

## 1. The load-bearing theorems (from 2402.10094)

Notation: `G ⊣ R` monoidal adjunction, `G : C → D` strong, `R : D → C` lax, `T = RG`, `Z(–)` = Drinfeld center, `1`
the unit.

- **Projection morphisms (3.1/3.3/3.5).** `lproj_{A,X} : A ⊗ RX --(unit⊗id)--> RGA ⊗ RX --(lax)--> R(GA ⊗ X)`;
  `rproj` symmetric. *"The projection formula holds"* (Def 3.12) = `lproj`/`rproj` natural isos. In the braided case
  one side suffices (Lemma 3.13).
- **coHopf / Hopf (§1.1).** projection-formula-holds = the adjunction is **coHopf** [Bal17]; dually, for `L ⊣ G`, the
  projection morphisms are the **Hopf operators** [BLV11] and their invertibility ⟺ `T = GL` is a **Hopf monad**. (The
  categorical "antipode exists / Frobenius reciprocity holds".)
- **The cheap route to the projection formula (§3.3).** **Cor 3.20:** if `C` is **rigid**, the projection formula holds
  for *every* monoidal adjunction. **Cor 3.19:** object-wise, it holds for any object with a dual. → **rigidity =
  every offer has a counter-offer / every credit a debit; if the resource theory is rigid, escrow-compositionality is
  free.**
- **Projection = monad morphism (Cor 3.11).** `lproj_{–,1} : (– ⊗ R1) ⟹ RG` is **always** a morphism of monads
  (unconditionally); an **iso** exactly when the projection formula holds. → the *fulfillment monad* `RG` is, up to the
  projection iso, literally **"tensor with the standing escrow object `R1`"**.
- **Theorem B (4.10) — the headline (a).** projection-formula ⟹ a **braided lax** `Z(R) : Z(D) → Z(C)`,
  `(X,c) ↦ (RX, c^R)`, half-braiding `c^R_A = lproj⁻¹ ∘ R(c) ∘ rproj` (4.11), **lax structure inherited verbatim from
  `R`** (4.12). Theorem A (Cor 4.11) = the special case "C rigid". *Centrality (commutes-past) tags along for free.*
- **Commutative central monoid (Def 5.1) + Thm 5.6 — the core of (b).** A commutative central monoid `M` = a
  **commutative monoid object in the braided center `Z(C)`**: a monoid `(M, mul, unit)` + a half-braiding `swap` making
  `mul/unit` central, commutative w.r.t. `swap`. It induces the **monoidal monad `T_M = (– ⊗ M)`** (η = `A⊗unit`,
  μ = `A⊗mul`, lax via `swap`). **Prop 5.3:** if the projection formula holds, `R1` *is* such an `M`. **Lemma 5.11:**
  for the escrow monad `T_M`, the projection formula holds **automatically** (`lproj = id`, `rproj = X⊗swap`).
  **Lemma 5.13:** `(– ⊗ R1) ≅ RG` as monoidal monads. **Thm 5.15:** under (ess.surj. + proj.formula), `D ≃ Klei(T_M)` —
  every turn factors as "do something to the pool".
- **§6 — Eilenberg–Moore = modules over the pool (the deepest, most hypothesis-heavy).** Under Assumption 6.4
  (reflexive coequalizers preserved by `⊗`): `EM(T_M) ≃ Mod_C-M` (positions = right `M`-modules; `⊗_M` = net out shared
  exposure). **Thm F (6.22):** + `R` reflects isos ⟹ `D ≃ Mod_C-M`. **Local modules (Def 6.25):** a module is *local*
  iff invariant under the **double-braiding (monodromy)** with `M` — i.e. **commutes-past-and-back the pool without
  drift = no path-dependence / no sandwich-MEV leakage** — a crisp, formalizable settle-safety predicate.
  **Schauenburg (6.27):** `Z(Mod_C-M) ≃ Mod^loc_{Z(C)}-M` (braided). → `Z(D) ≃ local-modules-over-the-pool`.
- **§7–§8 (low reuse).** Hopf-algebra/quantum-group/YD instantiations. Keep only: the *finite-projective* hypothesis
  for coinduction's projection formula (§7.2 — the "demand object is dualizable/finite" analogue), and the mental model
  `Z(Rep G) ≃ QCoh(G /^ad G)` = "center = gauge-invariant observables = invariant-under-conjugation-by-every-turn".

---

## 2. What mathlib v4.30 ALREADY gives us (verified by reading the source)

The big correction from the study: **most of this layer is IMPORT/EXTEND, not BUILD.** Verified paths in
`~/src/mathlib4/Mathlib/CategoryTheory/`:

| Capability | mathlib path | Key names |
|---|---|---|
| **Monoidal adjunction bundle** ✅ | `Monoidal/Functor.lean` | `Adjunction.IsMonoidal` (:952), `rightAdjointLaxMonoidal` (:897), `leftAdjointOplaxMonoidal` (:1009), id/comp instances. **A `Prop` over `Adjunction` + `[G.LaxMonoidal]` — the bundle is IMPORT.** |
| **Drinfeld center + half-braiding** ✅ | `Monoidal/Center.lean` | `HalfBraiding X` (`β : ∀ U, X⊗U ≅ U⊗X` + `monoidal` (=paper 5.2) + `naturality`), `Center C` (:73), `forget` (:313), `braidedCategoryCenter` (:347). `Center` is **braided, never symmetric** (no `SymmetricCategory (Center …)`). |
| **Monoid / comm-monoid objects** ✅ | `Monoidal/Mon.lean`, `CommMon_.lean` | `MonObj`, `IsCommMonObj` (needs `[BraidedCategory]`, law `(β_ X X).hom ≫ μ = μ`), `CommMon_`. Since `Center R` is braided, **`CommMon_ (Center R)` typechecks** — that IS the commutative central monoid (Def 5.1). |
| **Closed / internal hom** ✅ | `Monoidal/Closed/Basic.lean` | `Closed`, `ihom`, `tensorLeft A ⊣ ihom A` (:81). **The genuinely-monoidal `(–⊗A) ⊣ (A ⟹ –)` — the honest home for a monoidal Predicate⊣Witness, NOT Laws.lean's poset.** |
| **Rigid / duals** ✅ | `Monoidal/Rigid/Basic.lean` | `ExactPairing`, `HasLeftDual`/`HasRightDual`, `RigidCategory` — the cheap projection-formula route (Cor 3.20). |
| **Monads / Kleisli / EM** ✅ (partial) | `Monad/{Basic,Kleisli,Algebra,Adjunction}.lean` | `Monad`, `Kleisli T` + `Kleisli.Adjunction` (a **plain** `Adjunction`), `Monad.Algebra`, `Adjunction.toMonad`. |
| **Modules over a monoid object** ✅ | `Monoidal/Mod.lean` | `Mod A` (`:224`). (`Mod_.lean` is a **deprecation shim** since 2026-04-27.) |
| **Day convolution** ✅ | `Monoidal/DayConvolution.lean` | `F ⊛ G`, braided + closed variants. **Deferred — unused** (the `Match` coend already lives in presheaf-land). |
| **Coend** ✅ | `Limits/Shapes/End.lean`, `Limits/Types/End.lean` | `coend F` — already used by `Intent/Match.lean`. |

**Genuine BUILD gaps (mathlib has none of these):**
- ⚠ **`MonoidalCategory (Kleisli T)` — DOES NOT EXIST** (tree-wide grep empty). The Kleisli category of a monoidal monad
  *is* monoidal, but it is **unbuilt**. This is a real **L**-effort prerequisite, **not** "free from `Adjunction.IsMonoidal`"
  (the bundle only applies *once you already have* the monoidal functors). It gates the projection-formula-on-escrow,
  Theorem B, and the `fulfill`-as-counit bridge.
- ⚠ **No `(– ⊗ M)`-as-`Monad` construction from a `MonObj M`.** The monad itself (η = `A◁unit`, μ = `A◁mul`) + its 3 laws
  must be hand-built (solid **L**, not M).
- **No "monoidal monad" typeclass** (combine `Monad` + `LaxMonoidal`); thread it manually.
- **No Tambara modules / optics** over the existing `Profunctor`.

---

## 3. The spine mapping — faithful vs. stretch (⚠ = critique's corrections)

| Target | Verdict | The honest boundary |
|---|---|---|
| **#1 monoidal adjunction** | Faithful **only** as the escrow-Kleisli `Free ⊣ Forg` over `ResourceTheory R` | ⚠ **NOT `Predicate ⊣ Witness` (Laws.lean).** `Laws.predicate_witness_galois` is `polarity_galois` — a Galois connection between *powerset lattices*; its "tensor" is lattice meet, its center is trivial, every half-braiding over it is a tautology. Using it for the monoidal layer is the **WRONG MODEL**. Laws.lean is the *base hyperdoctrine fibre*. The genuinely-monoidal demand⊣supply, if wanted, is `tensorLeft ⊣ ihom` (closed structure), not the poset. |
| **#2 projection formula = escrow compositionality** | Faithful; Lemma 5.11 gives it for free on `T_M` | ⚠ **Vacuity trap.** On the escrow-Kleisli instance `lproj = id`, so `IsIso lproj` reduces to `IsIso (𝟙)` — *trivially true regardless of R*. The **content lives in the refuted general sibling** (a generic lax `Forg` where `lproj` is NOT iso, A1 §3.3). To have teeth, state it for a *generic* monoidal adjunction with the central-monoid hypothesis, AND exhibit the false general sibling. (On discrete `DemoRes` everything is iso — doubly vacuous.) |
| **#3 standing offer as a central object** | ⚠ **RENAME.** Faithful as a *frictionless / no-arb* idealization ONLY | ⚠ **"AMM-as-central-object" is a PUN.** `HalfBraiding.β : ∀ U, X⊗U ≅ U⊗X` forces the offer to commute *invertibly* past **every** turn. A real AMM (slippage, fees, finite liquidity) has `X⊗U ≇ U⊗X` in value ⇒ **cannot be a center object at all**. Name it `FrictionlessStandingOffer` / `IdealNoArbPool`; the half-braiding models **no-arb order-independence**, full stop. The teeth ARE the content (a slippage curve admits no `HalfBraiding`), but don't claim it verifies constant-product economics. ⚠ The proposed `central_match_routes ↔ Match.twoHop` bridge is **speculative** — `twoHop` is `Quot.mk ⟨B,(f,g)⟩` with zero relation to a half-braiding; no such bridge is built. Don't assert it. |
| **#4 commutative central monoid = the escrow monad** | Faithful for **standing / accumulating** escrow; ⚠ **mismatch for one-shot** | Real fit: `M` is a center object (#3) *and* a monoid; `T_M = (–⊗M)` is the writer-monad-over-a-commutative-monoid. ⚠ **Semantic mismatch the synthesis missed:** Thm 5.6's `μ = A⊗mul^M` **coalesces** two escrows (`x·y`), but the spine's escrow is **one-shot consumed** (`no_double_fulfill`: released ≠ refundable). Coalescing ≠ consumption. So `T_M` models *standing/AMM liquidity*, not *one-shot escrow*. Resolve in prose before mechanizing: either re-understand escrow as accumulating, or model consumption as a *module action that zeroes* (not a plain comm monoid). Do **not** unify one-shot escrow and AMM liquidity under one `M`. |
| **#5 `fulfill` = the adjunction counit** | ⚠ **DEFER (two prerequisites deep)** | `Core.lean`'s `fulfill` is a *function*; there is **no `Adjunction` object** in the Intent stack yet — "receipt⊣intent counit" is currently prose, not `Adjunction.counit`. Pinning it needs (i) monoidal-Kleisli (§2 gap) and (ii) re-founding `EscrowWitness` (a `Bool`) as a `T_M`-algebra (the single largest piece). Settle the one-shot-vs-accumulating question (#4) first. |

---

## 4. The build plan (Phase 3+) — corrected order

**IMPORT day-one (all verified present):** `Adjunction.IsMonoidal`, `Center`/`HalfBraiding`, `CommMon_`/`IsCommMonObj`,
`Closed`/`ihom`, the rigid stack, `Mod`, `Monad`/`Kleisli`/`Algebra`. **Decide early: is `ResourceTheory R` rigid?**
(every offer has a counter-offer) — rigidity �(Cor 3.20)⟹ the projection formula is free.

**BUILD, in dependency order:**
1. **`CommCentralMonoid R := CommMon_ (Center R)` + the underlying `escrowMonad : Monad (– ⊗ M)`** (3 monad laws from
   `MonObj`). *The unifier* — #3/#4 read off it. Sits on confirmed imports; **no upstream BUILD dependency.**
   **Gate:** add a *non-discrete* witness `R` with a non-trivial `M` **before** claiming it (on `DemoRes` the only `M`
   is `𝟙_`, so the structure is never exercised — vacuous).
2. **`escrowMonad_isMonoidal` (Thm 5.6 lax structure).** The page-46 hexagon chase via `M.swap`. **Real teeth:** fails
   without `IsCommMonObj.mul_comm` (drop commutativity → the hexagon won't close). Land green on the non-discrete witness.
3. ⚠ **`monoidalKleisli` — `MonoidalCategory (Kleisli T_M)` + `(toKleisli).Monoidal` + `(fromKleisli).LaxMonoidal`.**
   *The prerequisite the synthesis omitted.* Solid **L**. Must exist before steps 4–5.
4. **`escrow_projection_formula` (Lemma 5.11), with REAL teeth** — `IsIso lproj` for a *generic* monoidal adjunction
   under the central-monoid hypothesis, **plus** the refuted general sibling (`¬ ∀ …`, or a documented counterexample).
   Not as `IsIso (𝟙)`.

**DEFER:**
5. **`Z(R) : Z(D) → Z(C)` (Theorem B, 4.10)** — after step 3; ⚠ state as a functor between **two** centers
   (`Z(Klei(T_M)) → Z(C)`), **not** an endofunctor `Center R ⥤ Center R`. **L+.**
6. **§6 modules / local-modules / monodromy-invariance settle-safety** — hypothesis-heavy (Assumption 6.4). The richest,
   most novel payoff (`Z(D) ≃ local-modules-over-the-pool`; local = no-sandwich-MEV), but gated on settlement
   coequalizers in `ResourceTheory`.

**DROP / RE-SCOPE:**
7. **`FrictionlessStandingOffer`** (was "AMM-as-central-object") — keep the rescoped artifact, drop the AMM name and the
   unbuilt `Match` bridge; document that slippage/fee AMMs are *provably not* center objects (that's the teeth).
8. **`fulfill_is_counit`** — off the near roadmap until #5's prerequisites land **and** the one-shot-vs-accumulating
   design question is settled in prose.
9. **Day convolution** — unused; defer.

**Highest-leverage first artifact:** step 1 (`CommCentralMonoid` + `escrowMonad`), then step 2 (`escrowMonad_isMonoidal`).
It is the unifier, sits on confirmed imports, has the only genuinely-surviving teeth, and avoids the Laws.lean trap.

---

## 5. PDFs pulled this session (validated `%PDF`, in `pdfs/`)

- `hopf-monads-on-monoidal-categories-bruguieres-1003.1920.pdf` — Bruguières–Lack–Virelizier, *Hopf monads* (the coHopf /
  Hopf-adjunction target for making receipt⊣intent monoidal; fusion-operator invertibility = "no resource leaks across
  fulfillment composition").
- `frobenius-monoidal-functors-ambiadjunctions-lifts-centers-2410.08702.pdf` — Flake–Laugwitz–Posur (same authors as the
  anchor) — Frobenius monoidal functors from ambiadjunctions, **stated via the projection-formula morphisms**, lifted to
  Drinfeld centers. The bridge between (a) and (b).
- `frobenius-monoidal-functors-induced-2412.15056.pdf` — Flake–Laugwitz–Posur — induction-along-a-Frobenius-extension; a
  *constructive* escrow-installing functor instance.
- `composing-networks-of-amms-2106.00083.pdf` — Engel–Herlihy — AMMs as composable objects (the economics anchor for the
  standing-offer compositionality; Herlihy provenance speaks dregg's concurrency dialect).
- `drinfeld-center-representation-theory-monoidal-1501.07390.pdf` — Neshveyev–Yamashita — center objects from a unitary
  half-braiding on an ind-object in a rigid C*-tensor category (concrete half-braiding machinery; a notion of
  *honest/positive* standing offer).

Cited, not pulled (already in library or lower priority): Bruguières–Virelizier *Hopf monads* origin (math/0604180);
Bartoletti–Chiang–Lluch-Lafuente *A theory of AMMs in DeFi* (2102.11350, single-AMM operational grounding); Day
convolution (covered by `coend-calculus-loregian-1501.02503`); rewriting for SMCs with commutative (co)monoid (2204.04274).
