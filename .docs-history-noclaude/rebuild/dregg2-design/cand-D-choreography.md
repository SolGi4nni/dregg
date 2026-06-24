# cand-D — Choreography as the syntactic spine

> **Current as of 2026-06-02.** This candidate is **no longer purely forward-design**: its
> "Metatheory delta" (§7) has been **BUILT**. The choreography front-end now lives in
> `Dregg2/Projection.lean` (NOT the proposed `Metatheory/Projection.lean`) plus a dedicated
> projection↔hyperedge bridge `Dregg2/Spec/Choreography.lean`, sitting atop
> `Dregg2/Coordination.lean` (the MPST `GlobalType`/`project`/`LocalType`/`projection_sound`
> machinery). See §7 for the as-built receipts. Several `[F]` (forward-design) claims below are
> now `[C]` (grounded-in-code). The architecture/vision content (§0–§6, §8, §9) remains live and
> accurate; status corrections are inlined with `file:line` receipts.

> **Status:** a *fourth* candidate, of a different kind than A/B/C. Where `cand-A`
> (vat-coalgebra), `cand-B` (witness-PCA), `cand-C` (cap-distributed) are three
> projections of the **turn** — the *semantic* generator (`00-synthesis §1`) — cand-D
> proposes **choreography as the *syntactic* spine**: the thing a programmer *writes*,
> and the thing the compiler reasons over. Its **target is the A⊕B⊕C substrate**, not a
> replacement for it. Reads forward from `dregg2.md`, `pdfs/STUDY-projection-split.md`,
> `pdfs/discoveries-2.md §6`. Tags: `[G]` grounded-in-paper · `[C]` grounded-in-code ·
> `[F]` forward-design · `[T]` theorizing.
>
> **One-line thesis:** *a choreography is a diagram in the turn-category; endpoint
> projection is the functor from that diagram to per-cell behaviours; the runtime
> monitor of a projected local type **is** the vat-boundary membrane.* Choreography-first
> is therefore not a rival spine — it is the **missing front-end** whose back-end is
> dregg2.

---

## 0. The altitude distinction (why this is not a rival to "turn is the generator")

The synthesis converged on *turn = generator, cell/cap/proof = three projections*. That
is a claim about **semantics** — the smallest morphism. cand-D makes a claim at a
**different altitude — syntax / the programming model**:

| | dregg2 (bottom-up) | cand-D (top-down) |
|---|---|---|
| what you write | a turn (one morphism), composed by the executor | a **global type / choreography `G`** (a multiparty protocol) |
| what the compiler reasons over | per-turn `StepInv` | `G`'s well-formedness + its **projection** to endpoints |
| the coordination module | **deferred** (ROADMAP Phase 7-adjacent; "composes JointTurns over time") | **the front door** |
| a JointTurn (`dregg2 §1.6`) | the equalizer of N per-cell steps over a shared turn-id | **one interaction step of a projected `G`** |

Categorically `[T]`: a choreography is a **diagram** in the turn-category `𝒯` (objects =
cell-states, morphisms = turns); endpoint projection `⟦·⟧ᵣ` is a **functor** `Choreo →
∏ᵣ Endpointᵣ` sending `G` to each role's local behaviour; the runtime executes the
projection by emitting turns/JointTurns. So "turn is the generator" (semantics) and
"choreography is the spine" (what you write) **coexist** — `G` *elaborates into* a
composite of turns; projection is the elaborator (Lean = the semantics, metaprogramming =
the elaborator, exactly `dregg2 §0`'s "many syntaxes, one semantics"). The choreographic
programming languages already realise this shape: `choral-choreographic-oop`,
`functional-choreographic-programming`, `haschor-functional-choreographies-icfp23`,
`montesi-choreographic-programming-book`. `[G]`

---

## 1. The object: the annotated global type `G`

The primary artifact is a global type extended with three orthogonal annotations — and
the headline of cand-D is that **the three judgements of `dregg2 §2` become one typed
artifact + one analysis**, instead of three dynamic per-turn side-conditions:

- **Conservation (Law 1)** = **linear payload typing in `G`** — resources flow through
  the protocol linearly (Move-style). This is exactly the linear-logic reading of session
  types: `coherence-generalises-duality-mpst`, `formulas-as-processes-deadlock-freedom-choreographies`,
  `move-resources-safe-abstraction-money`. Conservation lives *in the types*, checked once
  at type-checking, not re-proven per turn. `[G]`
- **Ordering (Law 2)** = **the causal/sequencing structure of `G` itself** — the protocol
  *is* the order. *Intra-protocol* canonicity is free (the global type fixes it);
  *cross-protocol / multi-writer* finality still needs the consensus tier (§5a). `[G]`
- **I-confluence** = a **static analysis on `G`** — the projection-time blue/red colouring
  (`STUDY-projection-split.md`): interactions whose write-sets are BEC-I-confluent are
  *blue* (partition-progressing, no commit); the rest are *red* (atomic JointTurn). The
  classifier is Whittaker's segmented invariant-confluence (`interactive-checks-coordination-avoidance-vldb19`),
  tightened by `byzantine-eventual-consistency` (the iff) and `cryptoconcurrency` (escalate
  only on the actual N-ary conflicting set). `[G/C]`
  - **As-built receipt + a sharpening (2026-06-02):** the colour classifier is now
    `Projection.BlueEligible := Confluence.IConfluent` (`Dregg2/Projection.lean:56`); blue ⟺
    "merges preserve the invariant" is PROVED as `blue_merge_safe` (`Projection.lean:74`), which
    genuinely *uses* the I-confluence and FAILS for non-blue invariants
    (`Confluence.cardLeOne_not_iconfluent`). **Correction to the §1 framing above:** Coordination
    records `study-choreography` claim #1 as **[REFUTED]** — the linearity⇒I-confluence
    conflation (`Dregg2/Coordination.lean:36,444`). The colour is the **third judgement
    (`Confluence.IConfluent`), NOT the session/linear type**. So "Conservation = linear typing"
    (first bullet) and "I-confluence = the colour" are *kept orthogonal* in code — the linear
    payload type does **not** decide blue/red. The doc's three-annotations picture survives, but
    the colour classifier is `Confluence`, not the linearity reading.

So `G` carries all three; **projection is the compiler that discharges them** into
per-cell obligations. This is a genuine collapse and a cathedral-shaped one: `dregg2`
carries three judgements per turn; cand-D carries one annotated `G` + one analysis.

---

## 2. The three unifications (the case *for*)

cand-D's value is that, viewed top-down, three things dregg2 keeps separate become one:

1. **Three judgements → one annotated `G`** (§1).
2. **Membrane = endpoint projection = runtime monitor.** Projecting `G` to role `r` gives
   `r`'s local view across the boundary — exactly what `r` may observe and must do. The
   inter-endpoint interaction is where conformance/duality is checked. And
   `monitorability-of-session-types-ecoop21` shows a projected local type can be **enforced
   by a runtime monitor** that checks each message and **assigns blame** on violation. That
   monitor *is* dregg2's vat-boundary: the monitor = the verifier, the per-message
   conformance check = the checkable witness (`cand-B`'s soundness-by-verification), and
   **blame = the de-jure/de-facto split** (`dregg2 §0`: the protocol said you may do X; you
   didn't; here is the proof). The vat-boundary law and the EPP-correspondence theorem
   (`deadlock-freedom-by-design-choreography-cm13`) are **intended to be the same theorem.**
   `[G/T]`
   - **As-built receipt (2026-06-02), with a naming correction:** there are now TWO proven
     vat-boundary laws (the doc's bare `Positional.lean` reference was imprecise):
     `Authority.Positional.boundary_law` (`Dregg2/Authority/Positional.lean:152`, the PAS-refined
     access-control law) and `Exec.VatBoundary.vat_boundary_law`
     (`Dregg2/Exec/VatBoundary.lean:88`, PROVED on the *executable* living cell). The EPP side is
     `Projection.epp_correspondence` (`Dregg2/Projection.lean:112`), which today is an **explicit
     alias** for `Coordination.projection_sound` (head-duality only). The "same theorem at two
     altitudes" identification is therefore **NOT yet a proof** — `Projection.lean`'s own docstring
     (lines 18–22, 101–111) flags it as the *intended* stronger statement, blocked on the
     operational LTS of `Coordination` (the parallel-composed-projection ⤳ `pc.coalg`
     bisimulation). Honest status: membrane-duality and the executable boundary law both hold
     *separately*; their unification is the open residue.
3. **The deferred coordination module → the front-end.** dregg2's ROADMAP defers
   multi-party/multi-turn choreography as "research-grade, build JointTurn first." cand-D
   makes it the thing you program in; the JointTurn becomes *one projected interaction*.
   The hard problem (`STUDY-projection-split`) stops being a deferred module and becomes the
   **compiler** — which is the cathedral move: confront the hard problem as the organizing
   principle. `[F]`

---

## 3. The open-world resolution (why this is not pyana-#1 reborn)

The fatal objection to choreography-first is that **choreographies classically assume a
closed world of known participants who pre-agreed on one global script — but the vision is
"concurrency among strangers,"** and strangers share no script. If `G` were *mandatory*,
cand-D would re-impose pyana-#1's closed world — a *worse* punt (punting openness). The
literature dissolves this, via four composing mechanisms (`pdfs/` grounding in brackets):

1. **No single global script — protocols compose.** Independently-authored choreographies
   connect at *typed interfaces*; the system is a **web of small composable choreographies**,
   not one cathedral-spanning `G` [`compositional-choreographies-montesi-yoshida`]. `[G]`
2. **Bottom-up compatibility replaces top-down agreement.** A set of independently-specified
   endpoints can be *checked* for safe interaction **without** a pre-agreed `G` — compatibility
   is synthesizable from the endpoints [`mpst-meet-communicating-automata`]. Strangers don't
   agree on `G`; they check their local behaviours are *compatible*. `[G]`
3. **The typed/untyped boundary is gradual.** A dynamic `?` type lets typed and untyped
   endpoints interoperate, with **blame** when an untyped party violates the protocol
   [`gradual-session-types`, `hybrid-multiparty-session-types`]. This is *exactly* "choreography
   is the typed overlay; ocap messaging is the untyped substrate," formalized. `[G]`
4. **Dynamic participation.** Participants **join/leave and are optional** at runtime
   [`explicit-connection-actions-mpst-hu-yoshida`]; roles have unbounded/indexed populations
   [`dynamic-multirole-session-types`, `parameterised-multiparty-session-types`,
   `role-parametric-session-types-in-go`]; any *compatible* endpoint substitutes safely
   [`precise-subtyping-async-multiparty-sessions`]. `[G]`

**The design law that keeps this honest:** *choreography is the typed, verified overlay you
opt into; open-ended ocap messaging (cand-C turns/caps) is the substrate it compiles to and
falls back to.* Two strangers interact via raw caps/turns with no shared `G`; when they agree
on a protocol, they pin a `G` and gain the static guarantees (deadlock-freedom, conservation,
the blue/red split) + a monitored boundary. **Make `G` mandatory and cand-D dies.** `[F]`

---

## 4. The runtime (how `G` becomes execution)

```
   write G  ──projection (the compiler = the projection-split)──►  per-role local types ℓᵣ
                                                                         │
                                       ┌─────────────────────────────────┴───────────────┐
                                       ▼ blue interactions                 red interactions ▼
                            CellProgram admissibility (cand-A)        JointTurn (dregg2 §1.6,
                            I-confluent, tier-1, no commit             CG-2 ⊗ CG-5, atomic, tier≥3)
                                       │                                            │
                                       └────────── monitored boundary ─────────────┘
                                          = the vat membrane (cand-B verifier);
                                            blame on non-conformance (de-jure/de-facto)
```

- A **blue** interaction projects to a `CellProgram` admissibility clause (`cand-A`,
  `cell/src/program.rs`) — runs cross-group, partition-tolerant, no commit. Eligible **iff**
  its write-set is I-confluent (`Confluence.lean:44` `IConfluent`, `STUDY-confluence-module.md`).
  `[C]`
- A **red** interaction projects to a **JointTurn** — the already-built γ.2 bilateral
  aggregation (`circuit::bilateral_aggregation_air` — confirmed live in
  `turn/src/aggregate_bilateral_prover.rs`, `circuit/src/ivc.rs`; CG-2 turn-id pullback ⊗ CG-5
  conservation equalizer), atomic, committed at the join of the written cells' tiers. `[C]`
- The **boundary** between two endpoints is a **monitor** enforcing each side's projected
  local type — a proof-carrying turn (`cand-B`) whose conformance check is the witness. `[F]`

> **As-built (2026-06-02):** this whole blue→CellProgram / red→JointTurn routing is now
> formalized in `Dregg2/Spec/Choreography.lean` as the **projection↔hyperedge bridge** — the
> red target is the N-ary `Hyperedge` (`Dregg2/Hyperedge.lean`, the wide pullback over `TurnId`,
> a *generalization* of the bilateral JointTurn). `Interaction.routeOf` (`Choreography.lean:124`)
> makes the routing target a function of the colour alone (`Projection.route`,
> `Projection.lean:89`). PROVED keystones (all `#assert_axioms`-pinned, `Choreography.lean:339–345`):
> `red_projects_to_hyperedge` (structural half — a red commit assembles a `Hyperedge`),
> `blue_needs_no_hyperedge` (a blue interaction commits independently per cell, no Σ=0 cut),
> `red_iff_coupled` (red ⟺ ¬I-confluent, with the forced-escalation clashing-pair witness
> `Confluence.nonpairwise_escalation`). The single OPEN residue is OPERATIONAL (the live red
> commit *operationally produces* exactly that hyperedge along the not-yet-formalized
> composed-projection bisimulation), `-- OPEN` at `Choreography.lean:184`.

So cand-D *reuses the entire dregg2 runtime*; it only adds the front-end (`G` + projection)
and reframes the JointTurn as a projection target.

---

## 5. The honest tensions (self-adversarial — where this strains or could fail)

**(a) THE central risk — the equivocation gap; cand-D is NOT self-sufficient.** Monitoring
gives *safety against protocol-violation as locally observed*, but a **Byzantine peer can
equivocate** — show different messages to different observers — which *local* monitoring
cannot catch. Choreography/MPST machinery (even the crash-stop and "Byzantine web services"
lines) does not by itself repel equivocation. The fix is **not** in the choreography layer:
it is the **blocklace / BEC substrate** (`byzantine-eventual-consistency`, `blocklace`),
which makes equivocation harm "only a finite prefix." So the clean split — *monitored
projection handles "does this peer follow the protocol as I observe it"; the blocklace
handles "does this peer show everyone the same thing."* **cand-D's Byzantine-safety bottoms
out on cand-C's substrate.** This is the load-bearing honesty of the candidate: it is a
**front-end**, and removing the blocklace breaks it. `[T]`

**(b) The closed-world purism trap (§3).** If discipline slips and `G` becomes mandatory,
cand-D regresses to pyana-#1 (closed committee), punting the openness the vision exists for.
The typed-overlay-over-ocap law (§3) must be enforced, not aspirational. Risk: *social/
engineering*, not technical — it's tempting to "just require the protocol everywhere." `[F]`

**(c) Byzantine endpoint projection is research-grade.** Classical EPP assumes endpoints
follow their projected types; a Byzantine endpoint deviates. `STUDY-projection-split.md`
flags **Byzantine-EPP-by-verification** as genuinely new (monitor + blame + blocklace, not
a typing theorem). The soundness theorem (projection ≈ `G` over Byzantine parties) is *not
proven* — it is the candidate's central open theorem, not a settled foundation. `[T]`

**(d) The boundary lemma is conditional.** Gluing a red-step output to a blue-step input is
provable when red→blue is **session-ordered**, but is *false / a well-formedness restriction*
when they are `G₁ | G₂`-concurrent over a shared cell (`STUDY-projection-split §4`). So cand-D
must *reject* some well-formed-looking `G`s — the projector is sound-but-incomplete (which
stacks acceptably with MPST's own sound-incomplete projection). `[T]`

**(e) Does it simplify, or just move complexity into the projector?** The projector becomes
large and load-bearing. Mitigant: it is **soundness-by-verification** (`cand-B`) — the
projected output (CellPrograms + JointTurns + monitors) is *independently checkable*, so the
projector is **untrusted**; a buggy projector produces a turn that fails the existing
`StepInv` check. The TCB does **not** grow to include the projector. `[F]`

**(f) Who writes `G`, and global-type inference.** Programmer burden: someone must author the
protocol. Partial mitigants: bottom-up *synthesis* of `G` from endpoints (`mpst-meet-
communicating-automata`), libraries of composable choreographies (§3.1), and the gradual path
(§3.3) so un-protocol'd interaction still works untyped. Open: ergonomics. `[F]`

---

## 6. What cand-D KEEPS (it composes with A/B/C, doesn't replace them)

- **cand-C (blocklace / CDT / caps)** — the substrate cand-D's Byzantine-safety *requires*
  (§5a). Untyped ocap messaging is the fallback mode (§3).
- **cand-B (proof-carrying / verifier-TCB)** — the monitor *is* a cand-B verifier; the
  projector is untrusted because its output is cand-B-checkable.
- **cand-A (cell coalgebra / coinductive runtime)** — blue interactions are CellProgram
  admissibility steps; a running choreography session is itself codata (`νC.µI`), and
  `explicit-connection-actions` join/leave are reachability events (the `cand-A`/`STUDY-cyclic-gc`
  `Live(c)` side-condition).
- **The three judgements, the JointTurn, the privacy tiers** — all preserved, now *expressed
  in `G`* rather than carried per-turn.

cand-D is therefore best read as **A ⊕ B ⊕ C, plus a syntactic spine on top** — the same
substrate, a new front door.

---

## 7. Metatheory delta — **BUILT** (as of 2026-06-02)

> This section was originally a *proposal* ("Add `Metatheory/Projection.lean` …"). It is now
> **realized in code** — but in `Dregg2/`, NOT `Metatheory/`. The actual modules are
> `Dregg2/Coordination.lean` (the MPST base: `GlobalType`/`project`/`LocalType`/`Projectable`/
> `projection_sound`/`ProtocolCell`/`Dual`) and **two cand-D-specific modules**:
> `Dregg2/Projection.lean` (the blue/red split + the keystone aliases) and
> `Dregg2/Spec/Choreography.lean` (the projection↔hyperedge bridge, §4 above). The original
> proposal is preserved below, annotated with as-built status + `file:line` receipts.

**ORIGINAL PROPOSAL (preserved): add `Metatheory/Projection.lean` (peer of `Boundary.lean`):**
- `Projectable G` — well-formedness (projectability + boundedness ∧ conservation typing ∧ a
  sound I-confluence segmentation exists).
- `project : Choreo → Role → LocalType`.
- **`epp_correspondence`** — the keystone: the parallel composition of the projections of `G`
  is behaviourally equivalent to `G` (a bisimulation), *extending* `deadlock-freedom-by-design`
  to carry conservation + the blue/red split. **And the realization to record:** this theorem
  and `Boundary.boundary_law` are the **same theorem at two altitudes** — `boundary_law` is the
  per-endpoint instance of `epp_correspondence`. The membrane = projection.
- **`byzantine_epp_by_monitoring`** `[open theorem]` — projection is sound over
  Byzantine parties *given* (i) per-endpoint monitoring with blame, and (ii) the blocklace
  equivocation-repelling assumption as a hypothesis (NOT derived — same status as the JointTurn
  binding in `Boundary.lean`). This names §5a/§5c as a premise, honestly.

Crypto-soundness stays out (the monitor's `Verify` is a decidable oracle; `dregg2 §8`).

**AS-BUILT STATUS (the code wins):**
- `Projectable G` — **BUILT** as `Coordination.Projectable` (`Dregg2/Coordination.lean:325`).
  Caveat: it is the MPST projectability predicate; the conservation-typing / I-confluence-
  segmentation conjuncts of the proposal are carried *separately* (conservation in the record
  kernel; the blue/red colour in `Projection.BlueEligible`), not folded into this one `Prop`.
- `project : … → Role → LocalType` — **BUILT** as `Coordination.project`
  (`Coordination.lean:241`); the carrier is the MPST `GlobalType` (`Coordination.lean:98`), not a
  bespoke `Choreo`. `Role := Nat`, `Payload := Nat` (`Coordination.lean:73,80`).
- **`epp_correspondence`** — **BUILT** (`Dregg2/Projection.lean:112`), but **scoped honestly to
  head-duality, NOT the full bisimulation**. It is an explicit alias
  `:= Coordination.projection_sound …` (`Coordination.lean:416`, itself PROVED for head-duality
  via `simp`, ending the docstring's "full bisimulation … open hole" residual as a *comment about
  what's still aspirational*, not an `axiom` in the proof). The proposal's "extends
  `deadlock-freedom-by-design` to carry conservation + the blue/red split" is **NOT yet** in this
  theorem. The "same theorem as `boundary_law` at two altitudes" claim is the **intended**
  stronger statement (`Projection.lean:18–22,101–111`), blocked on the operational LTS — see the
  §2 correction. The two-altitude *conjunction at current scope* IS proved:
  `Spec.epp_membrane_is_projection` (`Choreography.lean:323`, `#assert_axioms`-pinned) shows
  membrane-duality AND hyperedge incidence-agreement both hold for a red head interaction.
- **`byzantine_epp_by_monitoring`** — **deliberately NOT a Lean `theorem`** (the honest call,
  `Projection.lean:121–138`): a faithful statement needs the operational monitor LTS + a
  refinement relation `Coordination` does not yet provide, so it is recorded as a *named
  obligation* in a comment, not written as a vacuous-or-unprovable `theorem`. The PROVABLE part
  of the Byzantine story — the **blue (I-confluent) fragment** stays invariant-safe under *any*
  adversarially-permuted concurrent merge — IS proved (`blue_merge_safe`, `Projection.lean:74`;
  `blue_commits_independently`, `Choreography.lean:230`). The red/coupled fragment's
  Byzantine-EPP is the open theorem the blocklace owns — exactly §5a/§5c.
- **NEW, not in the original proposal:** the projection↔hyperedge bridge
  (`Dregg2/Spec/Choreography.lean`) — `red_projects_to_hyperedge`, `blue_needs_no_hyperedge`,
  `red_iff_coupled`, `red_legs_agree`, all PROVED + `#assert_axioms`-pinned (§4 receipt). This is
  the as-built realization of "blue → CellProgram, red → JointTurn" at the *N-ary* hyperedge
  generalization (`Dregg2/Hyperedge.lean`), strictly more than the bilateral JointTurn the
  proposal named.

---

## 8. Relationship to the ROADMAP

cand-D does not reorder Phase 0–2 (step-completeness, the soundness spine — still the critical
path). It **promotes the deferred coordination module**:
- Phase 3 (JointTurn) is *unchanged* — it becomes the **projection target of one red
  interaction**, which validates building it first.
- The deferred "coordination/choreography module" (`ROADMAP` deferred-strata) becomes a
  **named candidate front-end** with `Projection.lean` + the projection-split compiler, built
  *after* the JointTurn and `Confluence.lean` exist (it consumes both).
- Nothing in cand-D is soundness-critical: a bad `G`/projector yields turns the Phase-2
  `StepInv` rejects. So cand-D is **purely additive and deferrable**, which is the right place
  for a front-end.

---

## 9. Verdict

cand-D is **more cathedral, not more product**: it deepens the unification (three judgements →
one `G`; membrane = projection = monitor; coordination-module → front-end) and makes the
hardest problem the organizing principle. It is **viable for the open/stranger world** — via
compositional + bottom-up-compatible + gradual + dynamic mechanisms (§3) — *provided* the
typed-overlay-over-ocap discipline holds (§5b) and the **equivocation gap is owned by the
blocklace** (§5a). It is **not a replacement** for dregg2; it is the syntactic spine over
A⊕B⊕C, and its central open theorem (Byzantine-EPP-by-monitoring) is the same frontier
`STUDY-projection-split.md` already named.

**Recommendation:** adopt cand-D as the *intended front-end*, build it last (after the
soundness spine, `Confluence.lean`, and the JointTurn), and let the discipline of §3/§5b be a
hard design law. The single thing that would *kill* it is making `G` mandatory; the single
thing it *cannot do alone* is repel equivocation — and dregg2 already has the substrate for
that.

---

## Appendix — grounding

- Choreographic programming: `montesi-choreographic-programming-book`, `choral-choreographic-oop`,
  `functional-choreographic-programming`, `haschor-functional-choreographies-icfp23`.
- Projection / correspondence: `deadlock-freedom-by-design-choreography-cm13`,
  `mpst-honda-yoshida-carbone-jacm`, `mpst-generalising-projection`,
  `mpst-semantic-global-type-wellformedness`, `mpst-meet-communicating-automata`.
- Open world: `compositional-choreographies`, `gradual-session-types`,
  `hybrid-multiparty-session-types`, `explicit-connection-actions-mpst`,
  `dynamic-multirole-session-types`, `parameterised-multiparty-session-types`,
  `precise-subtyping-async-multiparty-sessions`, `role-parametric-session-types-in-go`,
  `monitorability-of-session-types`, `dynamic-choreographies-theory-implementation`.
- Conservation-in-types: `coherence-generalises-duality-mpst`,
  `formulas-as-processes-deadlock-freedom-choreographies`, `move-resources-safe-abstraction-money`.
- The split + substrate: `pdfs/STUDY-projection-split.md`, `byzantine-eventual-consistency`,
  `blocklace`, `cryptoconcurrency`, `sui-lutris-broadcast-and-consensus`,
  `interactive-checks-coordination-avoidance-vldb19`.
- Failure-aware: `mpst-crash-stop-async`, `mpst-crash-failure-typing-viering`,
  `bft-web-services-session-types`, `cryptographic-choreographies`.
