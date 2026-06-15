# Phase 2 — the `Intent` core (build spec)

The concrete next build. Design spine: `INTENT-AS-CO-RECEIPT.md`. Decision: **layered option (c)** —
abstract `Intent` parametric over a resource category + a concrete `KernelIntent` the auction proves on.
Opus only. Gate the full build yourself before committing. Bring category-shape details to ember as they
sharpen.

---

## The four faces (target structure)

```lean
-- Abstract layer — parametric over a resource theory R (the convertibility preorder = the match relation).
-- Reuse the Coecke–Fritz–Spekkens framing (INTENT-REFS-resources.md): a resource theory is a symmetric
-- monoidal category; `a ⪰ c := Nonempty (a ⟶ c)` is the convertibility preorder = "can A be turned into C".
variable {R : Type*} [ResourceTheory R]   -- R = the objects (resources/outcomes); see §"ResourceTheory" below

structure Intent (R) [ResourceTheory R] where
  offered   : R                       -- face 1a: the resources brought (the A wire in)
  wanted    : R                       -- face 1b: the outcome demanded (the C wire out) — the typed hole
  predicate : R → Prop                -- face 2: which fillings count as correct (the Predicate side of Laws)
  resource  : EscrowWitness offered   -- face 3: the escrow funding `offered` (abstract here; KernelIntent = a real cell-program)
  validity  : Deadline                -- face 4: causal_after | frame_within  (Dregg2/Time/Deadline.lean — DONE)
```

- **Face 1 (boundary / the hole):** `offered ⊗ wanted` is the string-diagram interface (resources-in,
  outcome-out). Fulfillment plugs a morphism `offered ⟶ wanted` (or a chain) into the hole.
- **Face 2 (predicate):** the demand for a witness; `Predicate ⊣ Witness` is `Dregg2.Laws`. Need =
  predicate/demand, Offer = witness/supply, Query = unit/probe (one adjunction, three hats).
- **Face 3 (resource = escrow):** abstract `EscrowWitness` here; the *concrete* `KernelIntent` binds it
  to a userspace-escrow cell-program (Phase 3). "Resources To Do It With" made first-class.
- **Face 4 (validity):** the `Deadline` from Phase 1 — already built and green. Anti-frontrunning =
  `causalAfter` on the reveal event.

---

## Fulfillment + the receipt⊣intent adjunction (prove incrementally)

```lean
-- A fulfillment plugs a morphism into the hole and produces the discharging receipt.
def fulfill (i : Intent R) (f : i.offered ⟶ i.wanted) (h : i.predicate i.wanted) : Receipt := ...

-- The duality to target (prove the laws incrementally, NOT all up front):
--   intent  = a demand on the admissible input (a predicate on which turns are wanted)
--   receipt = a witness that a turn happened (part of Obs / the attestation face)
--   fulfill = the counit: Intent ⊗ (matching morphism) ⟶ Receipt   (co-receipt ↦ receipt)
-- Keystone to aim for: `fulfill_discharges` — a fulfilled intent's receipt witnesses exactly the
-- demanded outcome (predicate-satisfied + conserved), and the intent is consumed (no double-fulfill).
```

Don't front-load the full adjunction. Define `Intent` + `fulfill`, get one concrete fulfillment
running (`#eval`/`example`), then prove the unit/counit laws as the auction needs them.

---

## Match = the coend (first-class multi-hop solver, reuse mathlib)

```lean
-- INTENT-REFS-optics.md: mathlib ALREADY has the coend. Match IS Match(A,C) = ∫^B Offer(A→B) × Match(B,C).
-- mathlib4 v4.30: CategoryTheory.Limits.Types.coend F := Quot (coendRel F)  (Limits/Types/End.lean)
def Match (A C : R) : Type _ := ...   -- defined via Limits.Types.coend over the Offer profunctor
-- The existential-over-the-middle-B IS the solver routing A→C through whatever offers exist.
-- For the FIRST app (auction), the optics study recommends modelling the bilateral fill as a simple
-- LENS (get/put) and keeping the heavy coend for the multi-hop exchange — so the auction proof does NOT
-- depend on the coend machinery. Build the coend `Match`, but let the auction use the lens fill.
```

---

## `ResourceTheory` — the abstract layer (what to build it on)

From `INTENT-REFS-resources.md` (verified against mathlib v4.30):
- **Phase 0 (pure mathlib reuse):** a resource SMC on the resource objects via `MonoidalCategory` +
  `SymmetricCategory`, **withholding the cartesian/copy structure** (no copying = linearity =
  conservation — INTENT-REFS-linear.md). The **match relation = the convertibility preorder**
  `a ⪰ c := Nonempty (a ⟶ c)`. Conservation = a **monotone** (a monoid-hom invariant, Phase 3).
- **The one genuinely new artifact (highest leverage, do it here or Phase 3):** a **decorated-cospan
  SMC** assembled from mathlib's `WalkingCospan`/`cospan` + `HasPushout`/`pushout`, proving the **cospan
  composition law** ("open turns compose"). This is where escrow + predicate + validity ride as the
  cospan decoration (Fong; INTENT-REFS-resources.md). Nothing upstream provides it.

---

## Concrete instantiation: `KernelIntent`

```lean
-- The model the auction proves on: R = the kernel's resources (assets/caps/cells).
abbrev DreggResources := ...                     -- the kernel's resource objects
abbrev KernelIntent := Intent DreggResources
-- The escrow witness (face 3) is a reference to a real userspace-escrow cell-program (Phase 3).
-- The abstract laws proved over `Intent R` transfer to `KernelIntent` by instantiation.
```

---

## Suggested module layout

- `Dregg2/Intent/Resource.lean` — `ResourceTheory` class + the convertibility preorder + (the
  decorated-cospan composition if done here).
- `Dregg2/Intent/Core.lean` — `Intent` structure (four faces), `fulfill`, the discharge keystone.
- `Dregg2/Intent/Match.lean` — `Match` via mathlib's coend + the lens fill for the bilateral case.
- `Dregg2/Intent/Kernel.lean` — `DreggResources` + `KernelIntent` (the concrete instance).

Keep them import-disjoint where possible. Wire into `Dregg2.lean` after the `Time.*` block, after the
full-build gate.

---

## Acceptance (the auction-readiness bar for Phase 2)

- All modules green; `#assert_axioms`-clean; non-vacuity `#eval`/`example` (a real `Intent` with a real
  fulfillment; the predicate genuinely constrains; an unmatched intent does NOT fulfill — teeth).
- `validity` is a real `Deadline` (Phase 1) — a `causalAfter` intent carries no frame dependency; a
  `frameWithin` one does.
- `Match`/the coend is non-vacuous (a concrete bilateral match exists; the multi-hop `∫^B` typechecks).
- The receipt⊣intent discharge keystone (`fulfill_discharges`) holds for at least the bilateral case.
- NO sorry/admit/native_decide; crypto/authority enters only as explicit §8 carriers; bring the
  `ResourceTheory` category-shape (what exactly are the resource objects) to ember before it sets.

Then **Phase 3** (conservation-as-monoid-hom + userspace escrow ≥ kernel-escrow) and **Phase 4** (the
gallery auction).
