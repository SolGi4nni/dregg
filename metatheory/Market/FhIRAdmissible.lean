/-
# Market.FhIRAdmissible — the `fhIR` admissibility direction: **compiles ⇒ admissible** (the honest ⟸).

**The type-safety / soundness direction of the `fhIR` admissibility theorem.**
`docs/deos/FHEGG-PRODUCT-ORDER-FRONTIER.md` (the headline) and `docs/deos/DREGGFI-PRIVACY-TIERS.md §3`
state the organizing claim of the typed order/product DSL: *"a product is admissible AT TIER T iff it
compiles at tier T."* The **full IFF is a named research target** (six parts; resource-relative
maximality). This module formalizes and PROVES the honest, tractable **⟸ direction**:

    a product's convex program passes the tier-T resource manifest  ⇒  it is tier-T-admissible (runnable),

and NAMES the ⟹ (admissible ⇒ compiles — completeness / no-false-reject, the resource-relative
maximality gap) as the open target — with a CONCRETE counterexample witnessing why it is open.

## The bridge is GENUINE, not a mirror

An earlier version of this file made `RunnableAt` a re-reading of the SAME manifest booleans that
`passes` inspects (`carrierTransports`/`verifyNotFind` were literal flag equalities), so
`passes ⇒ RunnableAt` was a tautological flag-drop and the "⟹ gap" was manufactured by ignoring one
field. That was a MIRROR. This version fixes it: `RunnableAt` is now a genuine *semantic* predicate
over a concrete runtime — a `Program` (the actual convex-solver instance the manifest abstracts) is
`SemRunnableAt` a tier iff the tier's crypto carrier OPERATIONALLY hosts and runs it on **every**
input (`carrierRun` returns a defined output — a real `∀`-input `Option` statement) AND a sound
trace-independent certificate accepts. The manifest bridges to this through a faithful-abstraction
relation `Reflects m p`; `RunnableAt T m := ∀ p, Reflects m p → SemRunnableAt T p`. This is NOT
def-eq to `passes` (it quantifies over programs and inputs, over the operational `carrierRun`/
`certifies`), and `passes_runnable` is a NON-TRIVIAL theorem: from the manifest flags + faithful
reflection it PROVES the carrier's evaluation is defined for all inputs. `SemRunnableAt` is
falsifiable, not `True` (a data-branching program does NOT run at the crypto tiers, a
non-fixed-point certificate is refused) — the teeth in §8 exhibit both.

## The model

  * **`Manifest`** — what the compiler emits about a compiled program: `publicOps` (`A, P` public+sparse —
    the FHE public-matvec line), `approvedCone` (`𝒦` on the declared v0 `ProxLib` — a **conservative**
    list: no PSD/exp-cone in v0), `boundedDims` (dims/sparsity/precision/iteration bounds), `noIntegrality`
    (no endogenous binary/disjunction), `traceIndepCert` (a small trace-independent `Cert-F`/gap check).
  * **`passes T` (SYNTACTIC)** — the tier-T `fhIR` typecheck: **Tier 0 DARK** needs everything (FHE:
    matrices public); **Tier 1 SHIELDED** drops `publicOps` (the solver sees plaintext); **Tier 2 OPEN**
    passes anything (the general matcher). Monotone: `passes dark ⇒ passes shielded ⇒ passes open`.
  * **`Program` (SEMANTIC RUNTIME)** — the concrete convex-solver instance the manifest abstracts: an
    actual `stepMap`/`iters` proximal iteration plus the structural facts a crypto carrier inspects
    (public operator? data-branching? within the FHE/STARK depth budget?) and a declared optimum a
    trace-independent certificate checks.
  * **`RunnableAt T m` (SEMANTIC)** — every program the manifest faithfully abstracts (`Reflects m p`)
    is `SemRunnableAt T` — the tier's crypto carrier `carrierRun` hosts it on every input and the
    certificate accepts. A genuine `∀`-program-`∀`-input operational Prop, distinct from `passes`.

## What is proved (honest scope)

  * **`passes_runnable` (the per-form ⟸ core).** `passes T m ⇒ RunnableAt T m`. A NON-TRIVIAL bridge:
    it destructures the manifest flags, uses the faithful-abstraction relation to recover the program's
    structural facts, and CONSTRUCTS the `∀`-input proof that the carrier runs — the semantic content
    the flags stand for. Not a flag-drop: `RunnableAt` unfolds to a statement about `carrierRun`, never
    to the manifest booleans.
  * **`compiles_admissible` (THE KEYSTONE, ⟸).** For a `Product` (a set of equivalent compiled forms),
    `compilesAt T P ⇒ AdmissibleAt T P`: if SOME form passes the tier-T manifest, the product runs at
    tier T. The verify-not-find direction of the admissibility theorem.
  * **Monotonicity** (`passes_mono`, `runnable_mono`, `admissible_mono`) — Tier-0-admissible ⇒
    Tier-1-admissible ⇒ Tier-2-admissible, from a real *carrier* monotonicity
    (`carrierRun_shielded_of_dark`: an FHE-hosted program is STARK-hosted; the crypto requirements only
    weaken with visibility).
  * **`mostPrivateTier` + soundness** — the compiler computes the most private tier a product runs at, and
    `mostPrivateTier_runnable` proves the offered tier is always genuinely runnable; `mostPrivate_dark_iff`
    proves the type system (not marketing) decides the DARK label.
  * **Manifest-level refutability (`runnable_flag_census`, §8b/§9).** `RunnableAt` itself — not merely
    the program-level `SemRunnableAt` — is REFUTED for one-flag mutants of a passing manifest: each of
    the four flags `Reflects` carries sinks `RunnableAt` when withdrawn (the mutation pinned by `rfl`
    before the verdict), and `approvedCone` — the one field `Reflects` omits — is proved the ONLY flip
    `RunnableAt` survives. Satisfiable, refutable, not trivially provable.

**The ⟹ direction is the NAMED OPEN target — with a concrete witness.** `runnable_not_compiles` exhibits
a manifest that is `RunnableAt shielded` yet does NOT `passes shielded` — its cone is off the *conservative*
declared v0 `ProxLib` (`approvedCone = false`) even though a bounded STARK circuit carries it. This is now
GENUINE, not manufactured: the semantic `carrierRun` truly does NOT inspect the cone (the STARK carrier
transports any bounded convex circuit), so `RunnableAt` really holds while `passes` really rejects. So
`AdmissibleAt ⇏ compilesAt` in general (`admissible_not_compiles`): the full IFF requires the
**resource-relative maximality** argument (`FHEGG-PRODUCT-ORDER-FRONTIER.md`: "equivalent convex functions
can have radically different prox costs; maximality is relative to a declared `ProxLib`") — the honest
open piece. Also open (not modelled here): semantic preservation, the cost bound, conditional
completeness, no-wrap, and leakage refinement (the other five parts of the six-part theorem).

Pure.
-/
import Mathlib.Tactic.Tauto
import Dregg2.Tactics

namespace Market

/-! ## 1. Tiers, the compiled manifest, and the syntactic judgement. -/

/-- **The three privacy tiers** (`DREGGFI-PRIVACY-TIERS.md`): `dark` (FHE, no-viewer), `shielded`
(STARK-ZK, solver-sees), `open` (public, general). -/
inductive Tier | dark | shielded | «open»
  deriving DecidableEq, Repr

/-- **A compiled product's resource manifest** — the facts the `fhIR` compiler emits about a program. -/
structure Manifest where
  /-- `A, P` public + sparse (the FHE public-matvec line — the *true* efficiency boundary). -/
  publicOps : Bool
  /-- `𝒦` on the declared v0 `ProxLib` (a CONSERVATIVE list: no PSD / exp-cone in v0). -/
  approvedCone : Bool
  /-- Dims / sparsity / precision / iteration bounds met (a bounded circuit). -/
  boundedDims : Bool
  /-- No endogenous binary / disjunction (stays in the convex regime). -/
  noIntegrality : Bool
  /-- A small trace-independent `Cert-F` / gap check exists (verify-not-find). -/
  traceIndepCert : Bool
  deriving DecidableEq, Repr

/-- **`passes T m` — the SYNTACTIC tier-T `fhIR` typecheck.** Tier 0 DARK requires everything (FHE:
matrices public + approved cone + bounded + convex + certificate); Tier 1 SHIELDED drops `publicOps` (the
solver sees plaintext, so private matrices are fine); Tier 2 OPEN passes anything (the general matcher). -/
def passes : Tier → Manifest → Bool
  | .dark,     m => m.publicOps && m.approvedCone && m.boundedDims && m.noIntegrality && m.traceIndepCert
  | .shielded, m => m.approvedCone && m.boundedDims && m.noIntegrality && m.traceIndepCert
  | .«open»,   _ => true

/-- **`passes_mono` — the syntactic typecheck is monotone in visibility.** `passes dark ⇒ passes shielded
⇒ passes open`: DARK's requirements strictly contain SHIELDED's (it adds `publicOps`), which contain
OPEN's (`true`). -/
theorem passes_mono (m : Manifest) :
    (passes .dark m = true → passes .shielded m = true) ∧
    (passes .shielded m = true → passes .«open» m = true) := by
  constructor
  · intro h; simp only [passes, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩
  · intro _; rfl

/-! ## 2. THE SEMANTIC MODEL — a concrete program the manifest ABSTRACTS, and its OPERATIONAL
runnability under a tier's crypto carrier. This is genuine runtime content, NOT a re-reading of the
manifest booleans (that was the earlier MIRROR — see the header). -/

/-- **`Program`** — a concrete compiled program the `fhIR` manifest abstracts: the actual convex-solver
instance a crypto carrier must host. `stepMap`/`iters` are the REAL proximal iteration (`stepMap`
applied `iters` times); the other fields are the structural facts a carrier inspects. -/
structure Program where
  /-- The actual per-iteration solver map (the prox / matvec step), run `iters` times. -/
  stepMap : Nat → Nat
  /-- Iterations actually executed (the real runtime depth). -/
  iters : Nat
  /-- The operator matrices are public (the FHE public-matvec line needs this). -/
  opPublic : Bool
  /-- The program branches on data (endogenous integrality — off the arithmetic-circuit regime). -/
  branches : Bool
  /-- The declared optimum the trace-independent certificate checks. -/
  optimum : Nat

/-- The fixed circuit-depth budget the crypto carriers (FHE / STARK) can host. -/
def depthBudget : Nat := 4096

/-- **`carrierRun T p x`** — the tier-T crypto carrier attempts to HOST and RUN program `p` on input
`x`, returning the computed output or `none` if the carrier cannot transport the program:

  * `dark` (FHE) — needs a PUBLIC operator, NO data branching, and depth within the FHE budget;
  * `shielded` (STARK) — needs NO data branching and depth within budget (operator may be private);
  * `open` (plaintext) — re-executes anything.

The output is the genuine `iters`-fold application of `stepMap` — a real evaluation, not a flag. -/
def carrierRun : Tier → Program → Nat → Option Nat
  | .dark,     p, x =>
      if p.opPublic = true ∧ p.branches = false ∧ p.iters ≤ depthBudget
      then some (Nat.iterate p.stepMap p.iters x) else none
  | .shielded, p, x =>
      if p.branches = false ∧ p.iters ≤ depthBudget
      then some (Nat.iterate p.stepMap p.iters x) else none
  | .«open»,   p, x => some (Nat.iterate p.stepMap p.iters x)

/-- **`certifies p`** — the trace-independent (verify-not-find) certificate ACCEPTS: the declared
optimum is a genuine fixed point of the solver step, so a verifier confirms optimality by CHECKING the
KKT / fixed-point condition (`stepMap optimum = optimum`) WITHOUT replaying the iteration trace. -/
def certifies (p : Program) : Prop := p.stepMap p.optimum = p.optimum

/-- **`SemRunnableAt T p` — the SEMANTIC runtime guarantee.** The tier-T carrier hosts and runs `p` on
EVERY input (a defined output), AND — for the private tiers, which emit no trace — a sound
trace-independent certificate confirms the result; the public tier re-executes (execution IS the check).
A genuine `∀`-input operational Prop over `carrierRun` / `certifies` — NOT a manifest boolean. -/
def SemRunnableAt (T : Tier) (p : Program) : Prop :=
  (∀ x, (carrierRun T p x).isSome = true) ∧ (T = .«open» ∨ certifies p)

/-- **Carrier monotonicity (dark ⇒ shielded):** any input the FHE carrier hosts, the STARK carrier
hosts — the STARK requirements (no branching, in-budget) are strictly weaker (no `opPublic`). -/
theorem carrierRun_shielded_of_dark {p : Program} {x : Nat}
    (h : (carrierRun .dark p x).isSome = true) : (carrierRun .shielded p x).isSome = true := by
  by_cases hd : p.opPublic = true ∧ p.branches = false ∧ p.iters ≤ depthBudget
  · have hs : p.branches = false ∧ p.iters ≤ depthBudget := ⟨hd.2.1, hd.2.2⟩
    simp [carrierRun, hs]
  · simp [carrierRun, hd] at h

/-- **The public carrier hosts anything.** -/
theorem carrierRun_open_isSome (p : Program) (x : Nat) :
    (carrierRun .«open» p x).isSome = true := by simp [carrierRun]

/-! ## 3. THE ABSTRACTION BRIDGE — the manifest FAITHFULLY reflects the program. -/

/-- **`Reflects m p`** — the compiler-emitted manifest `m` truthfully abstracts the concrete program
`p`. Each manifest boolean, when set, GUARANTEES the corresponding structural fact of the actual
program. `approvedCone` is deliberately ABSENT — the approved-cone list is a conservative syntactic
declaration with NO runtime meaning (the STARK carrier transports any bounded convex cone); this
absence is the honest source of the ⟹ gap (§9). -/
structure Reflects (m : Manifest) (p : Program) : Prop where
  /-- `publicOps` truthfully reports whether the operator is public. -/
  pub : m.publicOps = p.opPublic
  /-- `boundedDims` guarantees the real iteration depth is within the carrier budget. -/
  bounded : m.boundedDims = true → p.iters ≤ depthBudget
  /-- `noIntegrality` guarantees the program does not branch on data. -/
  noInt : m.noIntegrality = true → p.branches = false
  /-- `traceIndepCert` guarantees a sound trace-independent (fixed-point) certificate exists. -/
  cert : m.traceIndepCert = true → certifies p

/-- **`RunnableAt T m` — the SEMANTIC runtime guarantee at the manifest level:** EVERY concrete
program the manifest faithfully abstracts runs at tier T. A genuine semantic Prop (`∀` programs, `∀`
inputs, over the operational `carrierRun`) — distinct from, and NOT def-eq to, the syntactic `passes`
booleans. -/
def RunnableAt (T : Tier) (m : Manifest) : Prop := ∀ p : Program, Reflects m p → SemRunnableAt T p

/-! ## 4. THE ⟸ CORE — the manifest typecheck soundly delivers the SEMANTIC runtime guarantee. -/

/-- **`passes_runnable` — `passes T m ⇒ RunnableAt T m` (the per-form soundness core).** A NON-TRIVIAL
bridge: the syntactic tier-T manifest check implies the semantic runtime guarantee. The proof
destructures the manifest flags, uses `Reflects` to recover the program's structural facts, and
CONSTRUCTS the `∀`-input proof that `carrierRun` hosts the program plus the certificate. This is
type-system soundness — the `fhIR` typecheck never promises a tier the math cannot deliver — and it is
NOT a flag-drop: `RunnableAt` is a statement about `carrierRun`, not the manifest booleans. -/
theorem passes_runnable {T : Tier} {m : Manifest} (h : passes T m = true) : RunnableAt T m := by
  intro p hrefl
  cases T with
  | dark =>
    simp only [passes, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hpub, _hcone⟩, hbd⟩, hni⟩, hc⟩ := h
    have hop : p.opPublic = true := by rw [← hrefl.pub]; exact hpub
    have hbr : p.branches = false := hrefl.noInt hni
    have hit : p.iters ≤ depthBudget := hrefl.bounded hbd
    exact ⟨fun x => by simp [carrierRun, hop, hbr, hit], Or.inr (hrefl.cert hc)⟩
  | shielded =>
    simp only [passes, Bool.and_eq_true] at h
    obtain ⟨⟨⟨_hcone, hbd⟩, hni⟩, hc⟩ := h
    have hbr : p.branches = false := hrefl.noInt hni
    have hit : p.iters ≤ depthBudget := hrefl.bounded hbd
    exact ⟨fun x => by simp [carrierRun, hbr, hit], Or.inr (hrefl.cert hc)⟩
  | «open» =>
    exact ⟨fun x => carrierRun_open_isSome p x, Or.inl rfl⟩

/-- **`runnable_mono` — the semantic guarantee is monotone in visibility.** `RunnableAt dark ⇒ RunnableAt
shielded ⇒ RunnableAt open`, from the real *carrier* monotonicity (`carrierRun_shielded_of_dark`) — more
visibility only ever weakens the runtime demand. The `DREGGFI-PRIVACY-TIERS.md §3`
"Tier-0-admissible ⇒ Tier-1-admissible ⇒ Tier-2-admissible." -/
theorem runnable_mono (m : Manifest) :
    (RunnableAt .dark m → RunnableAt .shielded m) ∧
    (RunnableAt .shielded m → RunnableAt .«open» m) := by
  refine ⟨fun h p hr => ?_, fun _ p _ => ?_⟩
  · obtain ⟨hrun, hc⟩ := h p hr
    refine ⟨fun x => carrierRun_shielded_of_dark (hrun x), ?_⟩
    rcases hc with hc | hc
    · exact absurd hc (by decide)
    · exact Or.inr hc
  · exact ⟨fun x => carrierRun_open_isSome p x, Or.inl rfl⟩

/-! ## 5. Products (representation-relative) and the ⟸ KEYSTONE. -/

/-- **A product is a nonempty set of equivalent compiled FORMS** (reformulations under the declared
`ProxLib`) — the resource-relative view the admissibility theorem's honest maximality demands
(`FHEGG-PRODUCT-ORDER-FRONTIER.md`: equivalent convex functions can have radically different prox costs). -/
structure Product where
  /-- The equivalent compiled forms (reformulations). -/
  forms : List Manifest
  /-- At least one form (a real product compiles to something). -/
  nonempty : forms ≠ []

/-- **`compilesAt T P` — the compiler finds SOME form of `P` that passes the tier-T manifest.** -/
def compilesAt (T : Tier) (P : Product) : Prop := ∃ m ∈ P.forms, passes T m = true

/-- **`AdmissibleAt T P` — SOME form of `P` actually runs at tier T.** -/
def AdmissibleAt (T : Tier) (P : Product) : Prop := ∃ m ∈ P.forms, RunnableAt T m

/-- **`compiles_admissible` — THE KEYSTONE (⟸): a product that COMPILES at tier T is ADMISSIBLE at tier
T.** If some form passes the tier-T typecheck, that same form runs at tier T (`passes_runnable`, the
genuine semantic bridge), so the product is admissible. The verify-not-find direction of the `fhIR`
admissibility theorem, over the resource-relative product. **The honest, tractable half of "admissible
iff compiles."** -/
theorem compiles_admissible {T : Tier} {P : Product} (h : compilesAt T P) : AdmissibleAt T P := by
  obtain ⟨m, hmem, hpass⟩ := h
  exact ⟨m, hmem, passes_runnable hpass⟩

/-- **`admissible_mono` — admissibility is monotone in visibility (composed from `runnable_mono`).** -/
theorem admissible_mono (P : Product) :
    (AdmissibleAt .dark P → AdmissibleAt .shielded P) ∧
    (AdmissibleAt .shielded P → AdmissibleAt .«open» P) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨m, hm, hr⟩; exact ⟨m, hm, (runnable_mono m).1 hr⟩
  · rintro ⟨m, hm, hr⟩; exact ⟨m, hm, (runnable_mono m).2 hr⟩

/-! ## 6. The compiler offers the MOST PRIVATE honest tier (and refuses to promise more). -/

/-- **`mostPrivateTier m` — the most private tier the manifest honestly passes** (DARK if FHE-tractable,
else SHIELDED if STARK-tractable, else OPEN). The `DREGGFI-PRIVACY-TIERS.md §3` "the compiler reports the
most private tier a given product can honestly run at." -/
def mostPrivateTier (m : Manifest) : Tier :=
  if passes .dark m then .dark else if passes .shielded m then .shielded else .«open»

/-- **`mostPrivateTier_runnable` — the offered tier is ALWAYS genuinely runnable (sound offering).** The
compiler never promises a tier the math cannot deliver: whatever `mostPrivateTier` returns, the manifest
is `RunnableAt` it. (In the final `open` branch the public re-executor runs anything.) -/
theorem mostPrivateTier_runnable (m : Manifest) : RunnableAt (mostPrivateTier m) m := by
  unfold mostPrivateTier
  split_ifs with hd hs
  · exact passes_runnable hd
  · exact passes_runnable hs
  · intro p _; exact ⟨fun x => carrierRun_open_isSome p x, Or.inl rfl⟩

/-- **`mostPrivate_dark_iff` — the TYPE SYSTEM (not marketing) decides the DARK label.** The compiler
offers Tier 0 DARK for exactly the products that pass the DARK manifest — it cannot dark-wash a product
that fails the FHE typecheck. -/
theorem mostPrivate_dark_iff (m : Manifest) :
    mostPrivateTier m = .dark ↔ passes .dark m = true := by
  unfold mostPrivateTier
  constructor
  · intro h; by_contra hp
    simp only [Bool.not_eq_true] at hp
    rw [hp] at h; simp only [Bool.false_eq_true, if_false] at h
    split_ifs at h <;> simp_all
  · intro h; rw [h]; rfl

/-! ## 7. NON-VACUITY — positive polarity (a cheap product compiles + is admissible everywhere), plus
a GENUINE SEMANTIC WITNESS (a concrete program the manifest abstracts, and it really runs). -/

/-- A fully cheap product: public sparse operators, approved cone, bounded, convex, certificate — the
`fhEgg` base case (uniform-price auction / `Cert-F` circulation). -/
def cheapM : Manifest :=
  { publicOps := true, approvedCone := true, boundedDims := true,
    noIntegrality := true, traceIndepCert := true }

def cheapProduct : Product := ⟨[cheapM], by simp⟩

/-- **THE KEYSTONE, INSTANTIATED — the cheap product compiles at DARK, hence is admissible at every tier.**
It passes the DARK typecheck, so `compiles_admissible` gives `AdmissibleAt dark`, and `admissible_mono`
lifts it to SHIELDED and OPEN. A concrete, non-vacuous run through the ⟸ keystone + monotonicity. -/
theorem cheapProduct_admissible_everywhere :
    AdmissibleAt .dark cheapProduct ∧ AdmissibleAt .shielded cheapProduct ∧
      AdmissibleAt .«open» cheapProduct := by
  have hd : AdmissibleAt .dark cheapProduct := compiles_admissible ⟨cheapM, by simp [cheapProduct], rfl⟩
  have hs := (admissible_mono cheapProduct).1 hd
  exact ⟨hd, hs, (admissible_mono cheapProduct).2 hs⟩

/-- The most private tier of the cheap manifest is DARK (the compiler offers no-viewer). -/
theorem cheapM_mostPrivate : mostPrivateTier cheapM = .dark := by
  rw [mostPrivate_dark_iff]; rfl

/-- A concrete program the cheap manifest FAITHFULLY abstracts: a public, non-branching, in-budget
solver whose declared optimum is a genuine fixed point (every point is a fixed point of `id`). -/
def cheapProg : Program :=
  { stepMap := id, iters := 0, opPublic := true, branches := false, optimum := 0 }

/-- The cheap manifest genuinely reflects the cheap program (a real faithful-abstraction witness). -/
theorem cheapProg_reflects : Reflects cheapM cheapProg where
  pub := rfl
  bounded := fun _ => Nat.zero_le _
  noInt := fun _ => rfl
  cert := fun _ => rfl

/-- **GENUINE SEMANTIC WITNESS** — the cheap program actually RUNS at DARK (the strongest carrier): the
FHE carrier hosts it on every input and its fixed-point certificate accepts. This is `SemRunnableAt`
inhabited by a concrete operational run, so `RunnableAt` is NOT vacuously true. -/
theorem cheapProg_semRunnable_dark : SemRunnableAt .dark cheapProg :=
  ⟨fun x => by simp [carrierRun, cheapProg, depthBudget], Or.inr rfl⟩

/-! ## 8. NON-VACUITY — negative polarity (the reject-list bites at the SYNTACTIC level, and
`SemRunnableAt` is GENUINELY FALSIFIABLE at the SEMANTIC level). -/

/-- A private-matrix product (Markowitz QP: the covariance `Σ` is PRIVATE, so `publicOps = false`) — off
the FHE public-matvec line, but a bounded convex STARK circuit. -/
def markowitzM : Manifest :=
  { publicOps := false, approvedCone := true, boundedDims := true,
    noIntegrality := true, traceIndepCert := true }

def markowitzProduct : Product := ⟨[markowitzM], by simp⟩

/-- **TOOTH (private matrix ⇒ NOT DARK, offered SHIELDED).** The Markowitz QP fails the DARK typecheck
(`publicOps = false`), so it is NOT `compilesAt dark` — but it DOES compile (and is admissible) at
SHIELDED. Mirrors `DREGGFI-PRIVACY-TIERS.md`'s "Markowitz → Tier 1." -/
theorem markowitz_not_dark_but_shielded :
    ¬ compilesAt .dark markowitzProduct ∧ AdmissibleAt .shielded markowitzProduct := by
  refine ⟨?_, compiles_admissible ⟨markowitzM, by simp [markowitzProduct], rfl⟩⟩
  rintro ⟨m, hm, hp⟩
  simp only [markowitzProduct, List.mem_singleton] at hm
  subst hm; simp [passes, markowitzM] at hp

/-- An endogenous-integrality product (AON / FOK: the fill itself is a binary decision, so
`noIntegrality = false`) — off the convex regime entirely. -/
def aonM : Manifest :=
  { publicOps := true, approvedCone := true, boundedDims := true,
    noIntegrality := false, traceIndepCert := true }

def aonProduct : Product := ⟨[aonM], by simp⟩

/-- **TOOTH (endogenous integrality ⇒ NOT SHIELDED, offered OPEN).** AON/FOK falls off the convex cliff
(`noIntegrality = false`), so it fails BOTH the DARK and SHIELDED typechecks — but the OPEN general matcher
still expresses it. Mirrors `DREGGFI-PRIVACY-TIERS.md`'s "AON-FOK optimization → Tier 2." -/
theorem aon_not_shielded_but_open :
    ¬ compilesAt .shielded aonProduct ∧ AdmissibleAt .«open» aonProduct := by
  refine ⟨?_, compiles_admissible ⟨aonM, by simp [aonProduct], rfl⟩⟩
  rintro ⟨m, hm, hp⟩
  simp only [aonProduct, List.mem_singleton] at hm
  subst hm; simp [passes, aonM] at hp

/-- A data-branching program (an AON/FOK binary fill) — off the arithmetic-circuit regime. -/
def branchingProg : Program :=
  { stepMap := id, iters := 0, opPublic := true, branches := true, optimum := 0 }

/-- **TOOTH — `SemRunnableAt` is GENUINELY FALSIFIABLE (not vacuous `True`).** A data-branching program
does NOT run at SHIELDED (nor DARK): the crypto carrier returns `none` on every input, so the `∀`-input
`isSome` conjunct fails. The semantic predicate has real teeth. -/
theorem branchingProg_not_semRunnable_shielded : ¬ SemRunnableAt .shielded branchingProg := by
  rintro ⟨hrun, _⟩
  have := hrun 0
  simp [carrierRun, branchingProg] at this

/-- A program exceeding the FHE/STARK depth budget — `boundedDims` is OPERATIONALLY load-bearing. -/
def deepProg : Program :=
  { stepMap := id, iters := depthBudget + 1, opPublic := true, branches := false, optimum := 0 }

/-- **TOOTH — the depth budget BITES at the semantic level:** an over-deep program does not run at
SHIELDED (the STARK circuit cannot host unbounded depth). -/
theorem deepProg_not_semRunnable_shielded : ¬ SemRunnableAt .shielded deepProg := by
  rintro ⟨hrun, _⟩
  have := hrun 0
  simp [carrierRun, deepProg] at this

/-- A program whose declared optimum is NOT a fixed point (`stepMap = (· + 1)`, so `stepMap 0 = 1 ≠ 0`)
— its verify-not-find certificate is UNSOUND. -/
def uncertProg : Program :=
  { stepMap := (· + 1), iters := 0, opPublic := true, branches := false, optimum := 0 }

/-- **TOOTH — verify-not-find is load-bearing:** a program whose certificate does NOT check (the
declared optimum is not a fixed point) is NOT `SemRunnableAt` at the private tier DARK... -/
theorem uncertProg_not_semRunnable_dark : ¬ SemRunnableAt .dark uncertProg := by
  rintro ⟨_, hc⟩
  rcases hc with h | h
  · exact absurd h (by decide)
  · simp [certifies, uncertProg] at h

/-- ...yet it IS `SemRunnableAt` at OPEN — the public tier re-executes, so no separate certificate is
required (execution IS the check). The private-vs-public certificate split is genuine, not cosmetic. -/
theorem uncertProg_semRunnable_open : SemRunnableAt .«open» uncertProg :=
  ⟨fun x => carrierRun_open_isSome uncertProg x, Or.inl rfl⟩

/-! ## 8b. MANIFEST-LEVEL REFUTATION — `RunnableAt` ITSELF has teeth, not merely `SemRunnableAt`.

The §8 teeth falsify the program-level predicate. That alone leaves a hole: if `Reflects` were too
weak to ever deliver a falsifying program, `RunnableAt` could still hold of EVERY manifest — making
`passes_runnable` empty and re-manufacturing the very mirror this file was rebuilt to kill. So here
we refute `RunnableAt` at the MANIFEST level, one theorem per semantically-load-bearing flag: for
each flag, the manifest that withdraws it faithfully abstracts (`Reflects`) one of the §8 rogue
programs, and that program sinks it. Each mutant is pinned as EXACTLY `cheapM` with the ONE flag
flipped (asserted by `rfl` *before* the verdict is read), so the refutations are one-flag mutations
of a manifest `passes` accepts — `RunnableAt` is satisfiable, refutable, and decided by the flags'
SEMANTIC content, not their syntax. -/

/-- A private-operator program (the Markowitz covariance `Σ` stays private) the `markowitzM` manifest
faithfully abstracts — `publicOps = false` truthfully reports `opPublic = false`. -/
def privOpProg : Program :=
  { stepMap := id, iters := 0, opPublic := false, branches := false, optimum := 0 }

theorem privOpProg_reflects_markowitzM : Reflects markowitzM privOpProg where
  pub := rfl
  bounded := fun _ => Nat.zero_le _
  noInt := fun _ => rfl
  cert := fun _ => rfl

/-- **`publicOps` is semantically load-bearing at DARK:** the private-matrix manifest is NOT
`RunnableAt dark` — it faithfully abstracts a private-operator program the FHE carrier refuses. -/
theorem markowitzM_not_runnable_dark : ¬ RunnableAt .dark markowitzM := by
  intro h
  obtain ⟨hrun, _⟩ := h privOpProg privOpProg_reflects_markowitzM
  have := hrun 0
  simp [carrierRun, privOpProg] at this

/-- The bounds-withdrawn mutant: EXACTLY `cheapM` with `boundedDims` flipped off. -/
def unboundedM : Manifest := { cheapM with boundedDims := false }

/-- With `boundedDims` withdrawn, the manifest faithfully abstracts the over-deep `deepProg`
(the `bounded` guarantee is no longer made; every other guarantee is honoured). -/
theorem deepProg_reflects_unboundedM : Reflects unboundedM deepProg where
  pub := rfl
  bounded := fun h => nomatch h
  noInt := fun _ => rfl
  cert := fun _ => rfl

/-- **`boundedDims` is semantically load-bearing at SHIELDED:** withdraw it and `RunnableAt` falls
to the over-budget program (`deepProg_not_semRunnable_shielded`). -/
theorem unboundedM_not_runnable_shielded : ¬ RunnableAt .shielded unboundedM :=
  fun h => deepProg_not_semRunnable_shielded (h deepProg deepProg_reflects_unboundedM)

/-- With `noIntegrality` withdrawn (`aonM`), the manifest faithfully abstracts the data-branching
`branchingProg` (the `noInt` guarantee is no longer made). -/
theorem branchingProg_reflects_aonM : Reflects aonM branchingProg where
  pub := rfl
  bounded := fun _ => Nat.zero_le _
  noInt := fun h => nomatch h
  cert := fun _ => rfl

/-- **`noIntegrality` is semantically load-bearing at SHIELDED:** the AON manifest is NOT
`RunnableAt shielded` — it abstracts a branching program no arithmetic-circuit carrier hosts. -/
theorem aonM_not_runnable_shielded : ¬ RunnableAt .shielded aonM :=
  fun h => branchingProg_not_semRunnable_shielded (h branchingProg branchingProg_reflects_aonM)

/-- The certificate-withdrawn mutant: EXACTLY `cheapM` with `traceIndepCert` flipped off. -/
def uncertM : Manifest := { cheapM with traceIndepCert := false }

/-- With `traceIndepCert` withdrawn, the manifest faithfully abstracts `uncertProg`, whose declared
optimum is NOT a fixed point (the `cert` guarantee is no longer made). -/
theorem uncertProg_reflects_uncertM : Reflects uncertM uncertProg where
  pub := rfl
  bounded := fun _ => Nat.zero_le _
  noInt := fun _ => rfl
  cert := fun h => nomatch h

/-- **`traceIndepCert` is semantically load-bearing at the private tiers:** withdraw it and
`RunnableAt dark` falls to the unsound-certificate program (`uncertProg_not_semRunnable_dark`). -/
theorem uncertM_not_runnable_dark : ¬ RunnableAt .dark uncertM :=
  fun h => uncertProg_not_semRunnable_dark (h uncertProg uncertProg_reflects_uncertM)

/-! ## 9. THE OPEN ⟹ DIRECTION, made concrete — admissible does NOT imply compiles (GENUINELY).

The full IFF `admissible ⟺ compiles` is the named research target. The ⟹ (admissible ⇒ compiles) FAILS
in general because the manifest's `approvedCone` clause is a CONSERVATIVE declaration (the v0 `ProxLib`),
not a runtime necessity: the STARK carrier `carrierRun .shielded` provably does NOT inspect the cone
(`Reflects` does not even carry it), so a bounded convex certified circuit runs whether or not its cone
is on the blessed list. This gap is now GENUINE — `RunnableAt` really holds while `passes` really
rejects — not manufactured by a definitional coincidence. We exhibit the witness. -/

/-- A product whose cone is NOT on the conservative v0 `ProxLib` (`approvedCone = false`) but is public,
bounded, convex, certified — it WOULD run at SHIELDED (the STARK carrier does not need the cone blessed),
but the manifest conservatively rejects it. -/
def frontierConeM : Manifest :=
  { publicOps := true, approvedCone := false, boundedDims := true,
    noIntegrality := true, traceIndepCert := true }

/-- **`runnable_not_compiles` — the per-form ⟹ counterexample, GENUINE.** `frontierConeM` is
`RunnableAt shielded` (EVERY program it faithfully abstracts is a bounded convex certified circuit — the
STARK carrier hosts it; the cone is never inspected) yet does NOT `passes shielded` (its cone is off the
declared v0 `ProxLib`). So the syntactic typecheck is STRICTLY weaker than semantic runnability — the
source of the resource-relative maximality gap. -/
theorem runnable_not_compiles :
    RunnableAt .shielded frontierConeM ∧ passes .shielded frontierConeM = false := by
  refine ⟨fun p hr => ?_, by decide⟩
  have hbr : p.branches = false := hr.noInt rfl
  have hit : p.iters ≤ depthBudget := hr.bounded rfl
  exact ⟨fun x => by simp [carrierRun, hbr, hit], Or.inr (hr.cert rfl)⟩

def frontierProduct : Product := ⟨[frontierConeM], by simp⟩

/-- **`admissible_not_compiles` — the ⟹ direction is OPEN (product-level witness).** `frontierProduct` is
`AdmissibleAt shielded` (it runs) yet is NOT `compilesAt shielded` (no form passes the conservative
manifest). So `AdmissibleAt ⇏ compilesAt`: the full IFF requires the resource-relative maximality argument
(a declared `ProxLib` + cost budget) — the honest open piece of the six-part theorem. The ⟸ we proved
(`compiles_admissible`) is the sound, tractable half; this is precisely the gap that remains research. -/
theorem admissible_not_compiles :
    AdmissibleAt .shielded frontierProduct ∧ ¬ compilesAt .shielded frontierProduct := by
  refine ⟨⟨frontierConeM, by simp [frontierProduct], runnable_not_compiles.1⟩, ?_⟩
  rintro ⟨m, hm, hp⟩
  simp only [frontierProduct, List.mem_singleton] at hm
  subst hm
  rw [runnable_not_compiles.2] at hp
  exact absurd hp (by decide)

/-- **`runnable_flag_census` — THE COMPLETE FLAG CENSUS: the ⟹ gap is a property of the CARRIER,
not a definitional artifact.** Every one of `cheapM`'s five flags is flipped off in turn — each
mutation pinned by `rfl` as EXACTLY the one-field update, *then* the verdict — and the census is
asymmetric in precisely the honest place: the four flags `Reflects` carries
(`publicOps`/`boundedDims`/`noIntegrality`/`traceIndepCert`) each REFUTE `RunnableAt` at the tier
that needed them, while `approvedCone` — the conservative v0 `ProxLib` declaration `Reflects`
deliberately omits — is the ONLY flip `RunnableAt` survives. The earlier MIRROR manufactured its
gap by silently ignoring a field; this census PROVES which fields carry runtime semantics and that
exactly the ignored one does not. The base point makes it self-contained: `cheapM` passes DARK and
IS `RunnableAt dark` — satisfiable, and refuted by exactly the four one-flag mutations below. -/
theorem runnable_flag_census :
    (passes .dark cheapM = true ∧ RunnableAt .dark cheapM) ∧
    ({ cheapM with publicOps      := false } = markowitzM   ∧ ¬ RunnableAt .dark markowitzM) ∧
    ({ cheapM with boundedDims    := false } = unboundedM   ∧ ¬ RunnableAt .shielded unboundedM) ∧
    ({ cheapM with noIntegrality  := false } = aonM         ∧ ¬ RunnableAt .shielded aonM) ∧
    ({ cheapM with traceIndepCert := false } = uncertM      ∧ ¬ RunnableAt .dark uncertM) ∧
    ({ cheapM with approvedCone   := false } = frontierConeM ∧ RunnableAt .shielded frontierConeM) :=
  ⟨⟨rfl, passes_runnable rfl⟩,
   ⟨rfl, markowitzM_not_runnable_dark⟩, ⟨rfl, unboundedM_not_runnable_shielded⟩,
   ⟨rfl, aonM_not_runnable_shielded⟩, ⟨rfl, uncertM_not_runnable_dark⟩,
   ⟨rfl, runnable_not_compiles.1⟩⟩

/-! ### `#guard` smoke — the typechecks are COMPUTED, and the carrier genuinely RUNS / REFUSES. -/

-- the cheap product passes at every tier; its most-private tier is DARK:
#guard passes .dark cheapM == true
#guard passes .shielded cheapM == true
-- the private-matrix (Markowitz) product fails DARK, passes SHIELDED:
#guard passes .dark markowitzM == false
#guard passes .shielded markowitzM == true
-- the integrality (AON) product fails SHIELDED, passes OPEN:
#guard passes .shielded aonM == false
#guard passes .«open» aonM == true
-- the frontier-cone product is off the conservative manifest (the ⟹ gap):
#guard passes .shielded frontierConeM == false
-- the SEMANTIC carrier genuinely RUNS the cheap program and REFUSES the branching one:
#guard (carrierRun .dark cheapProg 7).isSome == true
#guard (carrierRun .shielded branchingProg 7).isSome == false
#guard (carrierRun .«open» branchingProg 7).isSome == true

/-! ### Axiom hygiene — the `fhIR` admissibility keystones pinned kernel-clean. -/

#assert_all_clean [Market.passes_mono, Market.carrierRun_shielded_of_dark,
  Market.carrierRun_open_isSome, Market.passes_runnable, Market.runnable_mono,
  Market.compiles_admissible, Market.admissible_mono, Market.mostPrivateTier_runnable,
  Market.mostPrivate_dark_iff, Market.cheapProduct_admissible_everywhere, Market.cheapM_mostPrivate,
  Market.cheapProg_reflects, Market.cheapProg_semRunnable_dark,
  Market.markowitz_not_dark_but_shielded, Market.aon_not_shielded_but_open,
  Market.branchingProg_not_semRunnable_shielded, Market.deepProg_not_semRunnable_shielded,
  Market.uncertProg_not_semRunnable_dark, Market.uncertProg_semRunnable_open,
  Market.privOpProg_reflects_markowitzM, Market.markowitzM_not_runnable_dark,
  Market.deepProg_reflects_unboundedM, Market.unboundedM_not_runnable_shielded,
  Market.branchingProg_reflects_aonM, Market.aonM_not_runnable_shielded,
  Market.uncertProg_reflects_uncertM, Market.uncertM_not_runnable_dark,
  Market.runnable_flag_census,
  Market.runnable_not_compiles, Market.admissible_not_compiles]

end Market
