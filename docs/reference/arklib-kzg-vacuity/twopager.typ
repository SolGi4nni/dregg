// Two-panel research summary of PAPER.md (this directory).
// One A3-landscape page = two A4-sized panels side by side, screenshot-ready as a spread.
// Compile: typst compile twopager.typ twopager.pdf

#let accent = rgb("#1e5f74")
#let inkdim = luma(90)
#let sans = "Helvetica Neue"

#set page(paper: "a3", flipped: true, margin: (top: 12mm, bottom: 11mm, x: 14mm))
#set text(font: "Libertinus Serif", size: 9.3pt, fill: luma(25))
#set par(justify: true, leading: 0.56em, spacing: 0.95em)

#show raw: set text(font: "DejaVu Sans Mono")
#show raw.where(block: false): set text(size: 8.1pt, fill: accent.darken(35%))
#show raw.where(block: true): it => block(
  fill: luma(249),
  stroke: (left: 1.4pt + accent.lighten(45%), rest: 0.4pt + luma(228)),
  inset: (x: 3.0mm, y: 2.5mm),
  width: 100%,
  radius: 1.5pt,
  text(size: 7.7pt, it),
)

#show heading.where(level: 1): it => block(above: 0mm, below: 3.0mm, {
  text(font: sans, size: 14pt, weight: "bold", fill: accent, it.body)
  v(1.4mm)
  line(length: 100%, stroke: 0.9pt + accent.lighten(35%))
})
#show heading.where(level: 2): it => block(
  above: 3.8mm, below: 1.7mm,
  text(font: sans, size: 10.2pt, weight: "bold", fill: accent.darken(15%), it.body),
)

#set list(marker: text(fill: accent, "▸"), indent: 1.2mm, body-indent: 1.8mm, spacing: 0.68em)

// ── Title banner ────────────────────────────────────────────────────────────
#block(width: 100%)[
  #grid(columns: (1fr, auto), column-gutter: 8mm, align: (left + bottom, right + bottom),
    [
      #text(font: sans, size: 21pt, weight: "bold", fill: luma(15))[Vacuity and Repair]
      #h(3.5mm)
      #text(font: sans, size: 12.5pt, fill: inkdim)[the generic-group security of KZG evaluation binding, from a mechanized formalization-soundness finding]
    ],
    [
      #text(font: sans, size: 8pt, fill: inkdim, align(right)[
        ArkLib #raw("d72f8392") · Lean v4.31.0 \
        two independent checkers · summary of #raw("PAPER.md")
      ])
    ],
  )
  #v(1.8mm)
  #line(length: 100%, stroke: 1.4pt + accent)
  #v(1.6mm)
  #text(size: 9.9pt)[
    ArkLib's KZG evaluation-binding theorem is axiom-clean *and* carries no information at any parameter: its `t`-SDH assumption quantifies over an unrestricted adversary type, which a `Classical.choice` trapdoor extractor inhabits with success probability exactly 1. We mechanize the refutation, the extraction-shaped repair that provably survives the exact attack, and generic-group numeric bounds — with the mechanization boundary stated scrupulously.
  ]
  #v(1mm)
  #text(font: sans, size: 8pt, fill: inkdim)[
    Draft — internal working paper, not filed, not a security advisory: a *formalization-soundness* issue in a public, in-development library, not a vulnerability in any deployed system. KZG, `t`-SDH, and the reduction are sound as normally stated — the issue is a Lean quantifier; nothing here is embargoed or exploitable.
  ]
]
#v(3mm)

// ── Two panels ──────────────────────────────────────────────────────────────
#grid(columns: (1fr, 1fr), column-gutter: 10mm,

// ═══ LEFT PANEL — the finding ═══
[
= I · The finding: axiom-clean, and empty

== The mechanism
KZG evaluation binding is proved in ArkLib by a correct, constructive reduction to the `t`-SDH assumption — whose adversary is a *plain, unrestricted function type*:

```lean
abbrev tSdhAdversary (D : ℕ) :=
  Vector G₁ (D+1) × Vector G₂ 2 → StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

def tSdhAssumption (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D), tSdhExperiment D adversary ≤ error
```

`ProbComp` is a free monad over oracle queries: only `query` nodes cost anything; pure computation is free and no resource bound is imposed anywhere. The SRS includes the verifier leg $(g_2, g_2^tau)$, which determines $tau$ whenever $g_2 eq.not 1$, and ArkLib's own `exists_zmod_power_of_generator` (`Algebra.lean:105`) makes the discrete log `Classical.choice`-definable. The adversary reads $g_2^tau$, recovers $tau$, and returns the `t`-SDH solution #box($(c = 0, g_1^(1\/tau))$) — zero oracle queries, success probability exactly 1.

```lean
noncomputable def tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) : tSdhAdversary D :=
  fun srs => pure (some (0, g₁ ^ (1 / dlogOf hg₂ srs.2[1]).val))

theorem tSdhExperiment_tauExtractingAdversary : tSdhExperiment D (…) = 1
theorem not_tSdhAssumption      (herr : error < 1) : ¬ tSdhAssumption D error
theorem tSdhAssumption_trivial_of_one_le (1 ≤ error) : tSdhAssumption D error
```

== No content at any parameter
Below 1 the assumption is refuted; at $gt.eq 1$ its conclusion is the triviality "a probability is $lt.eq 1$." `binding` consumes the assumption in the last step of its `calc`, and its hypothesis `hpair : pairing g₁ g₂ ≠ 0` *forces* $g_2 eq.not 1$ (a bilinear map kills the identity) — exactly what the extractor needs. So `binding`'s hypotheses are jointly unsatisfiable for any error below 1 (`binding_hypotheses_unsatisfiable`), and its conclusion is free at $gt.eq 1$. The sibling ARSDH assumption falls identically, taking `function_binding` with it. A canary — the giving-up adversary scores exactly 0 — confirms the experiment discriminates. The reduction itself is fully constructive and algebraically correct; the vacuity lives entirely in the assumption's quantifier.

== The pattern, not a typo
Reducing to a *different* base assumption does not escape. The natural `q`-DLOG assumption, stated in ArkLib's own unrestricted-adversary idiom, is equally false below 1 (`not_qDlogAssumption`, same extraction, own canary). And ArkLib's algebraic-group-model scaffolding confirms the disease from the other side: `AGM/Basic.lean` is a stub (its adversary's `run` is literally `sorry`; zero theorems; orphaned) and is *unsound as written* — the adversary is a `ReaderT` over the concrete group table, so its outputs can still depend on discrete logs. Its author flags the open problem verbatim: #quote[TODO: need to be sure this definition is correct]; #quote[How to make the adversary truly independent of the group description? It could have had `G` hardwired.] Any concrete-group assumption of the shape $forall "unrestricted adversary", "Pr"["win"] lt.eq epsilon < 1$ is `Classical.choice`-false in this idiom.

== The methodological point: axiom checks are blind to vacuity
`binding`, the refutation, and the winning adversary all print the *same* clean axiom closure:

```lean
#print axioms not_tSdhAssumption   -- [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, nothing any `#print axioms` / `#assert_axioms` gate would flag. *Axiom-clean and vacuous coexist.* The blindness is structural: an axiom check reports a proof term's closure; it never asks whether the theorem's *hypotheses* are jointly satisfiable, and any `def FooHard : Prop` used as a hypothesis is an assumption no axiom check inspects. Query-based bounds (`IsQueryBoundP`) do not help either — the winning adversary makes zero queries. The only reliable test is adversarial: try to *inhabit the assumption's negation* — prove the floor false at its deployed parameters. We found the identical pattern in our own hardness floors first, in several places, before ever looking at ArkLib; we present this as a field lesson, not a dunk.
],

// ═══ RIGHT PANEL — the repair + status ═══
[
= II · The repair, the number, and the honest status

== The mergeable de-vacuation (mechanized)
ArkLib's reduction is already constructive, and the assumption is consumed at exactly one `calc` step — so split there. The unconditional prefix becomes the primary theorem; the original `binding` becomes a one-line corollary.

```lean
theorem binding_reduces_to_tSdh … (adversary : KzgBindingAdversary …) :
    bindingExperiment … adversary
      ≤ tSdhExperiment g₁ g₂ n (bindingReduction … adversary)
```

No assumption `Prop`: both sides are concrete probabilities, true at every parameter — nothing for `Classical.choice` to inhabit. The diff is +41/−14 in one file; the whole tree builds (2994 jobs); axiom-clean. And it *provably survives the exact attack* (`repair_survives_attack`): in one `sorry`-free closure, (1) the trapdoor adversary still refutes `tSdhAssumption` below 1, and (2) the repaired bound holds regardless. The cure removes the unsatisfiable premise while keeping every step of the reduction. It does not by itself supply a number — it isolates the one obligation a sound assumption class must discharge.

== The number: the generic bilinear group bound
Group elements become opaque handles carrying *ordinary* polynomials in $ZZ_p [X]$ — *not Laurent*: group inversion negates the exponent, it never introduces $X^(-1)$. A winning $1\/(X+c)$ is therefore unrepresentable, and a "win" forces the nonzero, degree-$lt.eq D+1$ polynomial $F_ell dot (X+c) - 1$ to vanish at the random $tau$. Simulation (identical-until-bad) plus Schwartz–Zippel yield Boneh–Boyen's Theorem 12, verified line by line against the source:
$ epsilon space lt.eq space (q_G + D + 3)^2 (D+1) / (p-1) space = space O((q_G + D)^2 dot D \/ p) $
*Not* a clean $q^2\/p$: the bound is cubic in the SRS degree $D$, and at production parameters the $D^3\/p$ term is the one to watch (Corollary 13's $q < O(p^(1\/3))$ side condition). Naive AGM is not a shortcut: an adversary that *also* returns a valid representation is still `Classical.choice`-inhabitable — validity is not independence — so the AGM route relocates the same content onto `q`-DLog's generic hardness.

== Sorry-free in Lean today #text(size: 8.4pt, fill: inkdim, font: sans)[(all axioms `[propext, Classical.choice, Quot.sound]`)]
- *Vacuity refutations* — `t`-SDH, ARSDH, `q`-DLOG, each with a discriminating canary; imports genuine ArkLib at `d72f8392`, redefines nothing.
- *The repair and its survival* — `binding_reduces_to_tSdh` and `repair_survives_attack`.
- *Static GGM bound* — `ggm_tSdh_sound`: $epsilon lt.eq (D+1)\/(p-1)$ over the *entire* committed-generic adversary type (offset + degree-$lt.eq D$ polynomial, no group input — the trapdoor extractor is untypable here). Tight; $approx 2^(-234)$ at $p approx 2^254$, $D approx 2^20$. As far as our census found, the first generic-group security theorem in Lean.
- *Adaptive bound, explicit-equality-oracle (Maurer) model* — `adaptive_ggm_sound`: $epsilon lt.eq ("fuel" dot Delta + (D+1))\/(p-1)$ under adaptive group-op / pairing / equality queries; identical-until-bad *proven by induction* (`runAux_congr_of_agree`), not assumed; `fuel = 0` recovers the static bound. Linear in equality queries — a tighter model than Shoup's, where comparison is free.
- *Quadratic Shoup (random-encoding) bound* — `rand_encoding_bound`: $epsilon lt.eq (binom(n,2) dot 2D + (D+1))\/(p-1)$, $n = "fuel"+D+4$; the all-pairs bad event and the table size are theorems, not assumptions.
- *Degree invariant, structural* — $2D$ under the two-sorted pairing discipline; the naive flat-table $2D$ claim *refuted* ($X^4$ at $D=1$). Proved for a peer model.
- *ArkLib condition transport* — `groupWinSet_eq_realWinSet`: the field-level win predicate *is* ArkLib's real `tSdhCondition`, by prime-order injectivity.

== The named frontier #text(size: 8.4pt, fill: inkdim, font: sans)[(open — stated exactly, not gating the above)]
- *Degree hypotheses undischarged.* The adaptive and random-encoding theorems still consume `hdeg_*` as hypotheses. The structural $2D$ proof lives in a peer model (`PairedOp`/`buildPaired`) that the oracle `runAux` does not import — and it is a *genuine restriction* the oracle must adopt, not bookkeeping: the flat oracle provably violates $2D$. Until wired in, those theorems are not hypothesis-free.
- *`ProbComp` plumbing.* Threading the condition-level transport into the literal `tSdhExperiment` inequality (the `Strat → tSdhAdversary` embedding, the sampler's $"Pr" = "card"\/(p-1)$ semantics), and re-typing `bindingReduction`'s constructed adversary as a straight-line `Strat` — so `binding` itself inherits the bound.
- *The interlock is architectural, not mechanized.* The chain _random-encoding bound $arrow.l$ degree $lt.eq 2D$ $arrow.l$ pairing discipline_ is designed, with each link proven in its own file; the bridge lemmas between them remain to be written.
],
)

// ── Footer ──────────────────────────────────────────────────────────────────
#v(1fr)
#line(length: 100%, stroke: 0.6pt + luma(200))
#v(1.2mm)
#text(size: 7.8pt, fill: inkdim, font: sans)[
  *Artifacts* (this directory, all `sorry`-free against ArkLib `d72f8392`): #raw("KzgVacuity.lean") · #raw("binding-repair.patch") · #raw("RepairSurvives.lean") · #raw("candidates/{GgmCandidate, GgmAdaptive, GgmRandomEncoding, GgmDegreeInvariant, GgmArkLibTransport, KzgQDlogVacuity}.lean").
  *Reproduce:* drop #raw("KzgVacuity.lean") into #raw("ArkLib/Scratch/"), #raw("lake build") (green, no #raw("sorry")); #raw("#print axioms not_tSdhAssumption") → #raw("[propext, Classical.choice, Quot.sound]").
  *References:* [KZG10] Kate–Zaverucha–Goldberg · [BB04/BB08] Boneh–Boyen (Thm 12, Cor 13) · [Sho97] Shoup · [Mau05] Maurer · [FKL18] Fuchsbauer–Kiltz–Loss · [CGKY25] Chiesa–Guan–Knabenhans–Yu.
  Full treatment: #raw("PAPER.md").
]
