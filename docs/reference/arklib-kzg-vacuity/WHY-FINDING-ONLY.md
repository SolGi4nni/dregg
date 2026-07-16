# Why the numeric fix is genuinely the EF's — send the finding alone

**Status:** local analysis. NOTHING filed, pushed, or PR'd. Mechanized against a scratch copy of
ArkLib @ `d72f8392` (both `/private/tmp/arklib-review` and the session scratch `ArkLib` are at that
rev, verified). This file answers ONE question: *can we hand the Ethereum Foundation a residual-free,
numeric, sorry-free repair of `KZG.binding`'s vacuity — or is the numeric fix theirs to own?*

## Verdict

**A residual-free NUMERIC fix is NOT reachable in bounded effort. It is paper-sized and requires
building a generic group model essentially from scratch.** This is the honest "the fix is theirs"
conclusion. What we *can* hand them with zero residual is the **finding** plus the **reduction-shaped
repair** (`binding_reduces_to_tSdh`, option B in `REPAIR.md`) — which is complete-as-a-theorem and
sorry-free, its only "residual" being precisely the missing number that a GGM would supply.

The four-part bar for "residual-free" and where each part stands:

| Bar | Requirement | Status |
|-----|-------------|--------|
| 1. Non-vacuous | survive the exact `Classical.choice` attack | **MET** — `RepairSurvives.lean`, `repair_survives_attack`, sorry-free |
| 2. **Numeric** | `binding … ε` for a concrete small `ε` (a real GGM number) | **NOT MET — and not reachable on existing scaffolding** |
| 3. Sorry-free / axiom-clean | `[propext, Classical.choice, Quot.sound]` only | MET for what exists (option B); the missing numeric proof would be a from-scratch development |
| 4. Honest | no new unproven hypothesis smuggled in | the numeric bound cannot be produced *without* either a smuggled `def …Hard` hypothesis (a residual) or the full GGM (the paper) |

Bar 2 is the whole game, and it is where the work is genuinely the EF's.

## Why the number is unreachable here (verify, don't inherit)

The task is *not* "prove a theorem" — option B already did that. The task is "produce the number `ε`."
A number can only come from a model in which the adversary **cannot read the trapdoor** `τ`. Three
independent facts, each verified against the source at `d72f8392`, close every shortcut:

1. **Query-bounding does nothing.** t-SDH is algebraic: the killing adversary
   (`KzgVacuity.lean:tauExtractingAdversary`) makes **zero** oracle queries — all work is under `pure`,
   which the free monad `ProbComp` does not charge for. An `IsQueryBoundP`-style bound constrains
   something this adversary never does. (Confirmed by codex.)

2. **Naive AGM does not even close the vacuity, let alone give a number.** If the adversary stays an
   arbitrary function that *also* returns a representation of its output, `Classical.choice` still
   wins: it extracts `τ`, returns `h = g₁^(1/τ)`, **and** returns the genuinely-valid representation
   (coefficient `1/τ` on the `g₁` SRS basis element). A dependent pair `(element, valid-representation)`
   is extra data choice supplies for free, not a restriction. *Validity is not independence.*
   (REPAIR.md §2; confirmed by codex.)

3. **A number requires the group elements be OPAQUE HANDLES** the adversary can only combine through an
   oracle (so `τ` is unreadable), plus a proven symbolic-execution → concrete-execution simulation
   theorem. That is a generic group model. Reducing t-SDH to q-DLOG does **not** help: ArkLib has no
   q-DLOG assumption, and stated the same unbounded-function way it would be equally vacuous — the
   reduction merely *moves* the residual onto q-DLOG, whose number also needs the GGM.

### The scaffolding census (this is what "from scratch" means, concretely)

- `ArkLib/AGM/Basic.lean` **exists but is a WIP stub, not a foundation.** It defines
  `GroupRepresentation`, the group oracles (Op/Exp/Eq/Encode/Decode) with `StateT`-`Option`
  implementations, and an AGM `Adversary` type — but:
  - `Adversary.run` is literally **`sorry`** (line 165); the file has **zero theorems**;
  - it is **orphaned** — nothing in the ArkLib tree references `AGM.Adversary` or
    `AGM.GroupRepresentation` (it is `import`ed by the `ArkLib.lean` root only so it compiles);
  - it carries the exact design questions still open, in the source comments: *"TODO: need to be sure
    this definition is correct"*, *"How to make the adversary truly independent of the group
    description? It could have had `G` hardwired"*, *"TODO: talk about AGM in the pairing setting"*;
  - and critically it is **not opaque**: the `Adversary` is a `ReaderT (GroupValTable ι G) …` that is
    handed the *actual* group table over the *concrete* group `G`, and its scalar/control-flow outputs
    can still depend on discrete logs. Restricting only the *group-valued* outputs to handles does not
    stop a scalar output from being `1/τ`. `Adversary.run` being `sorry` is merely the smallest
    visible hole; the model's *opacity + simulation invariant* is the real gap.
- `Mathlib.Algebra.MvPolynomial.SchwartzZippel` + ArkLib's `SchwartzZippelCounting.lean` (a probability
  form) **exist** — but Schwartz–Zippel is only the **terminal root-counting lemma** of a GGM proof,
  not the model, not the symbolic-execution simulation theorem, not the union bound over the transcript.
- VCVio models DLog for Schnorr with a concrete Pointcheval–Stern number
  `ε'·(ε'/(qH+1) − 1/|F|)`, but that is a **random-oracle rewinding** reduction, not a generic-group
  bound, and `dlogExp` is itself another unbounded-adversary experiment. Nothing reusable for a GGM.
- No q-DLOG / q-SDH generic-group hardness theorem, and no numeric group-hardness bound of any kind,
  exists anywhere in the ArkLib tree.

## The precise map a sound numeric fix requires (so ember can offer to build it)

This is the standard Boneh–Boyen "q-SDH is hard in the generic bilinear group model" argument,
mechanized. Decomposition (codex's, corrected and checked against the winning condition):

1. **Opaque symbolic model.** Three separate handle tables for `G₁`, `G₂`, `G_T`, initialized with
   the SRS as *ordinary polynomials* in one formal indeterminate `X` (the trapdoor): `G₁ : 1, X, …, Xᴰ`;
   `G₂ : 1, X`. Group ops add exponent polynomials; inversion negates. **These are ordinary polynomials,
   not Laurent** — group inversion never introduces `X⁻¹`. (This corrects the "Laurent" framing in the
   task prompt; the correction is load-bearing because it is exactly *why* a winning `1/(X+c)` output is
   impossible to represent and therefore forces a root event.)
2. **Symbolic execution of every oracle call**, including the pairing (`G₁ × G₂ → G_T` multiplies
   exponent polynomials, degree `≤ D+1`; `G_T` results cannot feed back into `G₁`).
3. **Collision bound.** Every accidental equality of two *distinct* symbolic expressions at a random
   `τ` is a root event, bounded by Schwartz–Zippel; union-bound over the whole transcript.
4. **Terminal win bound.** A G₁ output `g₁^{P(X)}` with `deg P ≤ D` wins only if
   `((X+c)·P(X) − 1)(τ) = 0`; that polynomial is **nonzero of degree `≤ D+1`**, so the win is itself a
   root event `≤ (D+1)/(p−1)` over the nonzero-`τ` sampler.
5. **Simulation theorem** proving the concrete-group experiment and the symbolic experiment agree
   except on the collision events (query-count preservation, adaptive-transcript conditioning,
   handle/encoding freshness).
6. **Re-type and transport.** Re-state `tSdhAssumption`/`tSdhExperiment` over the restricted
   (opaque, straight-line) adversary class, then **carry the entire KZG binding reduction chain**
   (`bindingReduction` + the four transition lemmas in `Binding.lean`) into that class — because the
   reduction *builds* a `tSdhAdversary` from a binding adversary, and that construction must itself
   become a straight-line/symbolic program.

**The number is not a clean `O(q²/p)`.** The classical Boneh–Boyen GGM bound is of the form
`(q_G + D + 3)²·(D + 1)/(p − 1)`, i.e. `O((q_G + D)²·D / p)` — it carries a degree-`D` factor from the
SRS and is only quadratic when `D` is fixed. (Boneh–Boyen, *Short Signatures Without Random Oracles*,
Thm 12. Cited via codex; the `(D+1)/(p−1)` terminal factor is independently derived above, the exact
constant is theirs to confirm.) Flagging this matters: the residual is not just "a number", it is a
`q`-type, degree-dependent bound whose formalization is a research artifact.

## Effort estimate

**Weeks-to-paper, essentially from scratch.** The dominant cost is the opaque symbolic model + the
simulation theorem (items 1–2, 5) and the reduction transport (item 6) — none of which exist. The AGM
stub does not shorten it materially (wrong shape: transparent, `G`-hardwired, `run` = `sorry`, no
opacity invariant). Schwartz–Zippel shortens exactly item 3's terminal lemma. This is the kind of
development that is normally its own paper/PR in a formal-crypto library, not a drive-by patch — and
ArkLib is itself an in-development library (the tree is heavily `sorry`-laden; the AGM module is one
of many WIP corners), so this is squarely *their* roadmap item, not a gap we should paper over.

## Recommendation

**Send the finding alone**, with confidence that no easy numeric win was left on the table:

1. The **vacuity** (`KzgVacuity.lean`, `not_tSdhAssumption` / `not_arsdhAssumption`, sorry-free): the
   assumptions are false below error 1 and trivial at ≥ 1 — no content at any parameter.
2. The **reduction-shaped repair** (`binding_reduces_to_tSdh`, `binding-repair.patch`, `+41/−14`, tree
   green, axiom-clean) as the safe, mergeable step that removes the vacuous premise while keeping every
   ounce of the reduction's content — explicitly labeled as *not yet numeric*.
3. The **numeric bound as future work that is theirs to own**, with this map and effort estimate, and
   an offer to build the GGM in whichever direction they prefer (their own AGM module completed to
   opacity, or a bespoke straight-line symbolic model).

This is the residual-free outcome ember asked for: we send a finding and an honest, mergeable partial
repair with **zero smuggled hypotheses and zero faked completeness**, and we correctly identify the
numeric bound as the EF's careful work rather than fabricating it.

## Codex design consult — accepted / rejected

Prompt + full transcript in the session scratch (`codex-numeric-prompt.txt`,
`tasks/bujsg7o3p.output`). Codex independently re-read the ArkLib source (the AGM `sorry`, the orphan
status, the verbatim t-SDH defs, the KZG reduction) before answering — its facts match ours.

- **ACCEPTED:** query-bounding useless; naive-AGM-with-representation broken ("validity is not
  independence"); soundness fundamentally requires opacity/parametricity, not achievable while the
  adversary is a function of concrete group elements; the AGM stub lacks opacity and is not just
  `run = sorry`; verdict **weeks-to-paper, from scratch**; Schwartz–Zippel is only a terminal lemma.
- **ACCEPTED CORRECTION (checked against source):** the symbolic exponents are **ordinary polynomials,
  not Laurent** — inversion negates, it does not introduce `X⁻¹`. This is why the winning `1/(X+c)`
  output forces the degree-`≤ D+1` root event, and it is load-bearing for the argument's shape.
- **ACCEPTED CORRECTION (cited, not independently re-derived):** the number is `O((q_G+D)²·D/p)`
  (Boneh–Boyen Thm 12), **not** a clean `O(q²/p)`; the `(D+1)/(p−1)` terminal factor we derived
  independently corroborates the degree dependence.
- **REJECTED:** nothing. Codex's answer is consistent with the source at every point we could check;
  we flag only that the exact Boneh–Boyen constant is their (BB05's) to confirm, not something we
  re-proved here.
