# Intent-as-Co-Receipt — Optics / Coend / Open-Games References

*Research date: 2026-06-03. Companion to `INTENT-AS-CO-RECEIPT.md`. This is the formalism behind
"intent/fulfillment as get/put optics", the solver-match law*
`Match(A,C) = ∫^B Offer(A→B) × Match(B,C)`*, and the auction-as-open-game connection (§3, §7 of the
spine).*

Pillar: **profunctor optics, coend calculus, and compositional game theory** — the three are *one
calculus*. An optic is a coend over its residual; an open game is an optic carrying a best-response
relation. So the intent's dataflow (get resources / put outcome), the solver's existential routing
(`∫^B`), and the auction's mechanism-design content all live in the same place.

---

## QUICK VERDICT TABLE

| Need | Source | Mathlib status | Recommendation |
|---|---|---|---|
| Coend `∫^B` (the solver-match) | Loregian, *(Co)end Calculus* | **EXISTS** — `Limits.Types.coend` is a ready quotient; abstract `chosenCoend` API too | **REUSE mathlib** — define `Match` as a `coend` of an offer-bifunctor; do NOT hand-roll |
| Profunctor optics (get/put, intent boundary) | Riley; Clarke et al. | **PARTIAL** — `Profunctor` defined (Apr 2026); **no Tambara module, no `Optic` type yet** | BUILD-THIN on mathlib `Profunctor` + `coend`; or model intent directly as a `(get,put)` lens pair and connect to the coend later |
| Open games / compositional mechanism (the auction) | Ghani-Hedges-Winschel-Zahn; Capucci et al. | **NONE** | BUILD-OURSELVES (small), on top of the optic/lens layer; the auction needs only the *lens* fragment + a best-response predicate, not the full bicategory |

**Headline:** mathlib's coend support is *fresh and complete enough to reuse directly* (the
`Type`-valued coend is literally the existential-over-the-middle quotient our `∫^B` law needs). The
profunctor scaffold is new but thin (no Tambara/optic types). There is no Lean optics or open-games
library to adopt — but we don't need one: the spine's auction wants the **lens** fragment, which is a
one-screen definition.

---

## 1. COEND CALCULUS — the `∫^B` solver-match

### 1a. Loregian, *(Co)end Calculus* — **PRIMARY**

- **Author / year:** Fosco Loregian, 2021 (book); arXiv preprint *This is the (co)end* since 2015.
- **Venue:** Cambridge University Press, *London Mathematical Society Lecture Note Series* No. 468
  (publ. Sep 2021). ISBN 978-1-108-74612-0.
- **arXiv:** `1501.02503` (the perpetually-updated preprint *Coend calculus* / *This is the (co)end,
  my only friend*). **PULLED** → `pdfs/coend-calculus-loregian-1501.02503.pdf`.
- **What it gives us + map onto the spine:** The systematic calculus of ends `∫_B` and coends `∫^B`,
  the co/wedge universal property, the **co-Yoneda / density** identities (`∫^B C(B,A)×F(B) ≅ F(A)`),
  the Fubini rule, and Ch. 5 **profunctors** (composition of profunctors *is* a coend:
  `(Q∘P)(A,C) = ∫^B P(A,B)×Q(B,C)`). That last line **is** our solver-match law verbatim — with
  `Offer = P`, `Match = Q`, and the intermediate object `B` the existential the solver routes through.
  Appendix B's "table of notable integrals" is the cheat-sheet for every rewrite we'll want (AMM
  multi-hop = profunctor composition associativity; density = "a bilateral match is the degenerate
  one-hop coend"). Read Ch. 1 (dinaturality/(co)ends) and Ch. 5 (profunctors) first.

---

## 2. PROFUNCTOR OPTICS — intent = get my resources A, put back outcome C

### 2a. Riley, *Categories of Optics* — **PRIMARY (the construction)**

- **Author / year:** Mitchell Riley (Wesleyan), 2018.
- **Venue:** arXiv preprint (widely cited; not formally published — the canonical reference for the
  general optic).
- **arXiv:** `1809.00738`. **PULLED** → `pdfs/optics-categories-riley-1809.00738.pdf`.
- **What it gives us + map onto the spine:** *The* general definition — lenses, prisms, traversals are
  all one **optic**, defined as a coend over the residual:
  `Optic((A,A'),(B,B')) = ∫^M C(A, M⊗B) × C(M⊗B', A')`. This is precisely the spine's "typed hole":
  the residual `M` is the *context the fulfilment runs in*, `A` = resources offered, `A'` = outcome
  demanded, `B/B'` = the inner step plugged into the hole. The "lawfulness ≡ folklore profunctor
  laws" result and the universal property ("optics freely add counit/feedback morphisms to a monoidal
  category") give us a principled story for *why fulfilment discharges intent* (the counit = the
  receipt-from-intent annihilation in §1 of the spine). Note: the optic coend is the *same shape* as
  the `Limits.Types.coend` in mathlib (§4 below) — the residual `M` is the coend index.

### 2b. Clarke, Elkins, Gibbons, Loregian, Milewski, Pillmore, Roman, *Profunctor optics, a categorical update* — **PRIMARY (the profunctor encoding)**

- **Authors / year:** Bryce Clarke, Derek Elkins, Jeremy Gibbons, Fosco Loregian, Bartosz Milewski,
  Emily Pillmore, Mario Román, 2020.
- **Venue:** arXiv (extended abstract at NWPT 2019; the long version is the standard reference).
- **arXiv:** `2001.07488`. **PULLED** → `pdfs/optics-profunctor-categorical-update-2001.07488.pdf`.
- **What it gives us + map onto the spine:** The **Tambara-module / double-Yoneda** machinery that
  makes the coend-optic *computable*: an optic `(A,A')→(B,B')` is equivalently a polymorphic function
  `∀P. Tambara P ⇒ P(A,B) → P(A',B')`. This is the "van Laarhoven / profunctor-encoding" that turns
  the existential coend into a concrete, composable representation — i.e. it tells us *how to actually
  build the solver*, not just specify it. The key theorem (optic-coend ≅ Tambara-end) is the
  bridge: solver matching can be *specified* as the coend `∫^B` (§1) and *implemented* as Tambara
  profunctor composition. Has worked examples (lens/prism/traversal/grate) we can mirror for
  intent-kinds (Need/Offer/Query ≈ different optic families over the same residual).

---

## 3. OPEN GAMES / COMPOSITIONAL GAME THEORY — the gallery auction

### 3a. Ghani, Hedges, Winschel, Zahn, *Compositional Game Theory* — **PRIMARY (the bridge)**

- **Authors / year:** Neil Ghani, Jules Hedges, Viktor Winschel, Philipp Zahn, 2018.
- **Venue:** LICS 2018 — *Proc. 33rd ACM/IEEE Symp. on Logic in Computer Science*, pp. 472–481.
  DOI `10.1145/3209108.3209165`.
- **arXiv:** `1603.04641`. **PULLED** → `pdfs/open-games-compositional-game-theory-1603.04641.pdf`.
- **What it gives us + map onto the spine:** **Open games** are morphisms of a symmetric monoidal
  category, composed sequentially (`∘`) and in parallel (`⊗`) — and they are **optic-based** (an open
  game = an optic carrying a *best-response* relation; "coutility" is the optic's backward/put pass).
  This is the literal bridge demanded by spine §3/§7: the gallery sealed-bid auction is an open game
  whose forward pass routes bids (the optic's `get`) and whose backward pass is the
  winner/payment rule (the `put`/coutility) — *the same optic calculus as the intent's dataflow*. So
  "auction mechanism-design content" and "intent solver dataflow" are not analogous, they are the
  *same structure*: prove the auction's incentive/conservation property as a property of the optic,
  and it composes with the solver `∫^B` for free. Read §2 (the open-game category) + the Nash/closed-
  game equilibrium section.

### 3b. Capucci, Gavranović, Hedges, Rischel, *Towards Foundations of Categorical Cybernetics* — **SUPPORTING (the modern optic-as-agent view)**

- **Authors / year:** Matteo Capucci, Bruno Gavranović, Jules Hedges, Eigil Fjeldgren Rischel, 2021.
- **Venue:** Applied Category Theory (ACT) 2021; later in *Compositionality* (journal).
- **arXiv:** `2105.06332`. (Not pulled — supporting, not central; available OA if needed.)
- **What it gives us + map onto the spine:** Reframes open games / open learners uniformly as **optics
  with a controller** — a bidirectional process interacting with an environment (forward) and a
  controller (backward). This is the cleanest "an intent *is* an agent-shaped optic" framing: the
  controller is the solver/auctioneer choosing the filling. Cite this as the *current* foundational
  account if/when we generalise the auction beyond pure mechanism (e.g. an AMM as a standing open
  learner). Lower priority than 3a for the gallery auction specifically.

### 3c. Hedges, *Towards compositional game theory* (PhD thesis) — **SUPPORTING (the long-form derivation)**

- **Author / year:** Jules Hedges (QMUL), 2016.
- **Venue:** PhD thesis, Queen Mary University of London. OA via QMUL / Hedges' site.
- **What it gives us:** The full development behind 3a — string-diagram reasoning for games, the
  selection-function (`J`-/`K`-) monad view, and the lens/optic coherence (cf. *Coherence for lenses
  and open games*). Reference depth; not needed before building the auction.

---

## 4. WHAT MATHLIB ALREADY HAS (verified against `~/src/mathlib4` @ v4.30.0)

This is the load-bearing finding: **the coend we need is already in mathlib, and it is fresh.**

| Construct | File | What's there |
|---|---|---|
| **Coend `∫^B` (Type-valued)** | `Mathlib/CategoryTheory/Limits/Types/End.lean` | `Limits.Types.coend F := Quot (coendRel F)` — the coend of a bifunctor `F : Jᵒᵖ ⥤ J ⥤ Type` as an **explicit quotient**: `⟨j,x⟩ ∼ ⟨j',x'⟩` iff `∃ f:j⟶j', y. (F.map f.op).app y = x ∧ (F.obj _).map f y = x'`. Plus `coend.ι`, `cowedgeIsColimit` (it's the universal cowedge), and a `ChosenCoends Type` instance. **This is exactly the "existential over the intermediate object" the `∫^B` solver-match is.** |
| **Abstract coend + universal API** | `Mathlib/CategoryTheory/Limits/Chosen/End.lean` | `ChosenCoendsOfShape` / `ChosenCoends`, `chosenCoend F`, `chosenCoend.ι`, `chosenCoend.desc`/`.hom_ext`/`.map` — the universal-property toolkit (define a map out of the coend by giving a cowedge). Dualized from ends in May 2026 (`#38383`). |
| **End / wedge shapes** | `Mathlib/CategoryTheory/Limits/Shapes/End.lean` | `end_`/`coend` as multi(co)equalizers; `Wedge`/`Cowedge`. The general (any-`C`) construction. (author J. Riou, 2024) |
| **Profunctors** | `Mathlib/CategoryTheory/Profunctor/Basic.lean` | `Profunctor C D := C ⥤ Dᵒᵖ ⥤ Type w`, `ProfunctorCore` builder, identity profunctor (Yoneda), op/whisker/`Functor.toProfunctor`. **Added Apr 2026 (`#38085`).** *Stated future work: profunctor composition + the bicategory — i.e. the very coend-composition we'd contribute.* |
| **Dinatural transformations** | `Mathlib/CategoryTheory/DinatTrans.lean` | `DinatTrans` (difunctor diagonal + hexagon) — the morphisms (co)ends are universal among. |
| **Day convolution** | `Mathlib/CategoryTheory/Monoidal/DayConvolution.lean` (+ `/Closed.lean`) | Coend-style monoidal product on presheaves — relevant if/when AMM pricing is modelled as a convolution. |

**Gaps in mathlib (we'd build, not adopt):** no **Tambara module**, no **`Optic`** type, no **profunctor
composition** (explicitly listed as future work), no **open games / lenses-as-agents**. None block us;
all are small relative to the coend that's already done.

---

## 5. WHAT TO FORMALIZE FIRST — recommendation

**Decision: REUSE mathlib's coend; do NOT port an optics library; build the auction's lens fragment
ourselves.**

1. **Coend-match as a Lean `def`, reusing `Limits.Types.coend` (do this first — it's nearly free).**
   Model offers as a bifunctor `Offer : Cᵒᵖ ⥤ C ⥤ Type` over a category `C` of resource-types (objects =
   asset bundles, morphisms = admissible conversions). Then
   `Match(A,C) := Limits.Types.coend (offerComp A C)` where `offerComp` is the
   `Offer(A,–) × Match(–,C)` integrand. The quotient relation `coendRel` *is* "two routings through
   different middles `B,B'` are the same match when a conversion `B→B'` reconciles them" — i.e. the
   solver's path-independence is definitional, not a theorem we owe. The co-Yoneda/density lemma gives
   "bilateral match = degenerate one-hop coend" as a corollary. **This is the single highest-leverage
   first step**: it makes the `∫^B` solver-law a *reused mathlib def*, exactly what spine §7's open
   formalization question asks ("the `∫^B` solver-match as a coend … reuse the optics already implicit").
   Caveat to check on contact: mathlib's `coend` wants a *bifunctor on one category `J`* (`Jᵒᵖ ⥤ J ⥤
   Type`); the integrand `Offer(A,–)×Match(–,C)` must be packaged as such a difunctor in the middle
   variable — straightforward but the first real proof obligation.

2. **Intent boundary as a lens/optic pair (second; small, no library needed).** For the gallery auction
   the *full* profunctor-optic generality is overkill — model an intent's boundary directly as a
   `get : A → S` / `put : A × B' → A'` pair (the lens fragment of Riley's optic with trivial residual),
   and only later identify it with the coend-optic via 2a/2b once Tambara modules exist. This keeps the
   auction proof (escrow ≥ kernel-escrow, causal reveal-order, conservation — spine §7) **independent of
   the heavy coend machinery**, which de-risks the first app.

3. **Open-game auction as `lens + best-response predicate` (third).** Following Ghani-Hedges et al.
   (3a): an open game over the lens from (2) plus a `Prop` best-response/winner relation. The auction's
   guarantees (no-reveal-before-commit, conservation across settle) become properties of this small
   structure; sequential/parallel composition (`∘`/`⊗`) is where it later meets the solver `∫^B`.

4. **(Defer) Contribute Tambara + profunctor-composition upstream-style.** Mathlib explicitly lists
   profunctor composition as future work, and composition *is* the coend `(Q∘P)(A,C)=∫^B P(A,B)×Q(B,C)`
   — which, post-step-1, we'll already have as a def. A thin `Profunctor.comp` + a `Tambara` class
   would (a) finish the optic story and (b) be a clean mathlib-shaped artifact. Worth doing *after* the
   auction validates the spine, not before.

**Port-thin or avoid?** Avoid porting any external optics library (there is no maintained Lean 4 one;
the closest ecosystem work is Haskell/Idris). The mathlib coend + a ~one-screen lens def covers the
spine's needs with far less surface than a port. The only thing worth eventually *contributing* (not
porting) is profunctor composition + Tambara, since mathlib already wants them.

---

## 6. PDFs PULLED (validated `%PDF`)

| File | arXiv | Role |
|---|---|---|
| `pdfs/coend-calculus-loregian-1501.02503.pdf` | 1501.02503 | the `∫^B` calculus + profunctor composition (= solver-match law) |
| `pdfs/optics-categories-riley-1809.00738.pdf` | 1809.00738 | optic = coend over residual (= the typed hole) |
| `pdfs/optics-profunctor-categorical-update-2001.07488.pdf` | 2001.07488 | Tambara encoding (= how to build the solver) |
| `pdfs/open-games-compositional-game-theory-1603.04641.pdf` | 1603.04641 | open games are optic-based (= the auction bridge) |

Not pulled (supporting, OA available): Capucci et al. *Categorical Cybernetics* (`2105.06332`); Hedges
thesis (QMUL OA). Already in `pdfs/` and relevant to the lens fragment: `edit-lenses-hofmann-pierce-
wagner.pdf`, `cambria-schema-evolution-edit-lenses-papoc21.pdf` (bidirectional/edit lenses);
`credible-optimal-auctions-via-blockchains-2023-114.pdf`,
`winner-determination-combinatorial-auctions-sandholm.pdf` (the auction app's mechanism side).
