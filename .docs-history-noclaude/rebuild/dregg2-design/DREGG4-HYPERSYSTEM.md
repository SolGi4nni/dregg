# DREGG4-HYPERSYSTEM — occupying any point/edge of the dial-cube, traversing higher cells of the interaction complex

> ⚑ **GROUND-CHECKED vs live Lean 2026-06-02 (post-2-compaction drift-repair); REAL/DECORATIVE/ASPIRATIONAL
> tags carry file:line receipts.** The code drifted *past* this doc in the GOOD direction — three claims the
> doc filed as "unbuilt / named-new / paper-only" have **landed in Lean since it was written**, and two
> `Finality` line-citations drifted. Folded forward below; the load-bearing structure (the two complexes,
> the two obstructions, the single-machine collapse) is **unchanged and all still grounds out**. Headline
> deltas: (1) **the transferability dial / `Discharged[V]` is no longer "entirely new / UNBUILT"** — it is a
> proved, axiom-clean module `Dregg2/Authority/DesignatedVerifier.lean` (`DischargedFor:113`, `TransferDial:146`,
> `designated_is_deniable:224`, `designated_excludes_public:257`); the §8.1 "first step" is *substantially
> done*. (2) **§5's epistemic tie now has Lean teeth** — `Dregg2/Apps/EpistemicSheaf.lean` realizes `D_B`
> distributed-knowledge (`DistKnows:106`), consensus-as-global-section (`consensus_on_clearance:199`), and the
> H¹ Byzantine-non-gluing obstruction (`fork_is_genuine:297`) — an *epistemic-frame (Kripke S5)* port, **not**
> a simplicial object, so §4.3/§8.2's "the interaction complex is a simplicial/∞-category" stays DECORATIVE
> (grep-confirmed: `SimplicialObject`/`face_map`/`Kan`/degeneracy are **absent** from `Dregg2/`). (3)
> `crossTierJoin`/`no_downgrade` were cited at `Finality.lean:95-96`; they actually live at `:219`/`:280`
> (PROVED). Everything in §4 (the `Hyperedge` wide-pullback) verified EXACT, citation-for-citation.

> **What this is.** A READ-ONLY galaxy-brain design exploration. **No code changed.** It asks
> ember's question rigorously: *can dregg become a "hypersystem" that lets you occupy ANY point or
> edge of its configuration space, and traverse HIGHER CELLS of the interaction complex?*
>
> **Discipline (non-negotiable, carried from `REORIENT §6` / `CARRY-FORWARD-SYNTHESIS`):** distinguish
> **real mathematical content** (already-proved Lean, or a precisely-stated obligation) from
> **suggestive notation** (∞-category decoration that buys nothing until it cashes out as a binding
> proof). Every claim is grounded `file:line`; every place the math is decorative is flagged.
>
> **Sources read in full and cited:** `study-category.md`, `OPEN-PROBLEMS.md`,
> `DREGG4-UNIFICATION.md` (§4 the dial-cube, §5 the comodel), `CARRY-FORWARD-SYNTHESIS.md`,
> `GLOSSARY.md` (three judgements, finality tiers); the Lean
> `metatheory/Dregg2/JointTurn.lean`, `Dregg2/Hyperedge.lean`, `Dregg2/Spec/JointViaHyper.lean`,
> `Dregg2/Finality.lean`; and the paper
> `pdfs/zotero-simplicial-epistemic-logic-faulty-agents.pdf` (Goubault–Kniazev–Ledent–Rajsbaum,
> *Simplicial Models for the Epistemic Logic of Faulty Agents*, arXiv:2311.01351v3).
>
> **Sources ADDED at the 2026-06-02 ground-check** (modules that landed after the original draft):
> `Dregg2/Authority/DesignatedVerifier.lean` (the transferability dial + `Discharged[V]` + deniability,
> §2.1/§8.1) and `Dregg2/Apps/EpistemicSheaf.lean` (the Lean port of the same arXiv:2311.01351 epistemic
> machinery — `DistKnows`/consensus-as-section/H¹-fork, §5.2).

---

## 0. The one-paragraph answer

**Two distinct complexes are at play, and the headline finding is that they are *not* the same object
— but the Agreement axis is the bridge between them.** COMPLEX 1 (the *configuration* dial-cube
`Disclosure × Transferability × Agreement`, `DREGG4-UNIFICATION §4`) is a choice-space on the
attestation face of a single turn; "occupy a point" = a per-turn dial setting, "traverse an edge" =
a turn that *changes* the setting. COMPLEX 2 (the *interaction* simplicial complex: cells as
0-cells, turns as 1-cells, JointTurns as 2-cells, n-ary atomic joint-turns as n-cells) is the
multi-party structure, and "traverse a higher cell" = execute an n-ary coordinated joint-turn. The
**genuinely-new-and-buildable** result: the n-cell generalization of COMPLEX 2 from `Fin 2` → `Fin n`
**already exists and is proved axiom-clean** — `Hyperedge` is the wide pullback over `TurnId`, and
`hyperedge_sound` is the N-ary keystone (`Hyperedge.lean:374`). What is *suggestive-only* is the slide
to a "full simplicial object" / "∞-category of the interaction complex": it buys nothing, because
**every higher cell carries an irreducible binding hypothesis** (CG-2 ⊗ CG-5) that the simplicial
framing cannot supply — `hyper_binding_is_proper` (`Hyperedge.lean:164`) proves the n-cell is a
*proper subobject*, never a free lift. The **honest verdict**: dregg becomes the hypersystem **on a
single machine** (where every simplex is synchronously fillable, so the achievable sub-complex is the
*whole* cube and the *whole* interaction complex), and a **partition-bounded sub-complex** when
distributed (the Agreement dial = how high a simplex you can fill; `#2 IMPOSSIBLE` pins the ceiling).
The simplicial-epistemic tie is real and load-bearing: **distributed agreement = filling a higher
simplex; common knowledge = a filled top-simplex** — so the Agreement dial, the attestation face, and
the interaction complex are the *same* simplicial structure, exactly as the question conjectured.

---

## 1. The two complexes, kept rigorously separate

These get conflated by loose "configuration space" talk. They are different categories with different
cells. The only honest thing to say is that the **Agreement coordinate of COMPLEX 1 is *defined by*
fill-height in COMPLEX 2** (§5). Everywhere else they must not be merged.

| | COMPLEX 1 — the CONFIGURATION dial-cube | COMPLEX 2 — the INTERACTION simplicial complex |
|---|---|---|
| **What a point is** | a *single turn's* attestation setting `(d, t, a) ∈ Disclosure × Transferability × Agreement` | a *cell* — a living coalgebra, a point of `νF` (`cand-A §1.1`) |
| **0-cells** | the 8 (more) corners of the cube | cells `{Cᵢ}` (vertices) |
| **1-cells / edges** | a turn that *moves* the dial: `(d,t,a) → (d',t',a')` | a turn / message = a coalgebra step `c : X → F X` (a morphism) |
| **2-cells** | a coherence square (two dial-paths agree) | a `JointTurn` — the existing 3-party atomic interaction (`JointTurn.lean`) |
| **n-cells** | (cube faces of dim n) | an n-ary atomic joint-turn = a `Hyperedge` over `Fin n` (`Hyperedge.lean:80`) |
| **The shape** | a cube (finite product of finite chains/lattices) — a *choice* lattice | a (chromatic) simplicial complex — a *gluing* structure |
| **Where it lives in the turn** | the attestation FACE (face 3, `Obs`) | the whole multi-cell turn (all three faces, but the binding is the cross-cell content) |
| **The hard obstruction** | the *impossibility surface* (§3): not every corner is occupiable | the *binding* (§4): every higher cell needs CG-2 ⊗ CG-5, irreducibly |

The grounding for "two complexes, one bridge": `Hyperedge.lean:99` (CG-5 is a single Σ over the
incidence simplex) is COMPLEX-2 geometry; `DREGG4-UNIFICATION §4.3` (Agreement as the third dial) is
COMPLEX-1 geometry; and `study-consensus`/`GLOSSARY: finality tiers` say the Agreement tier *reduces
from consensus*, which the simplicial paper shows *is* fill-height (§5). That reduction is the bridge.

---

## 2. COMPLEX 1 — the configuration dial-cube, developed

### 2.1 The three axes (real content: all three now have Lean homes; was "two exist, one named-new")

From `DREGG4-UNIFICATION §4` and `CARRY-FORWARD-SYNTHESIS §2 Face 3`, the attestation face of a turn
is a point in a 3-cube whose axes are the three honest "to-whom/what/how-many" judgements *on the
output object `Obs`*:

- **Disclosure** (*what is revealed*): `acceptanceOnly | selective(reveal ⊆ FieldId) | full`
  (`DREGG4-UNIFICATION §3` `inductive Disclosure`). **Partly built** — `FieldVisibility` exists
  (`cell/src/state.rs`), generalization to per-turn is the work (`§4.1`).
- **Transferability** (*to whom convincing*): `public | designated(V) | deniable(ring)`
  (`§3`/`§4.2`). **REAL — LANDED IN LEAN since this doc was written** (was "entirely new").
  `Dregg2/Authority/DesignatedVerifier.lean` (axiom-clean, `#print axioms`-audited
  `:369-372`) builds the whole axis: the **verifier-indexed `Discharged[V]`** the doc filed as the
  "named-new theory piece" is the proved `DischargedFor V stmt proof` (`DesignatedVerifier.lean:113`);
  the dial itself is `inductive TransferDial = transferable | designated V₀` (`:146`); `Transferable`
  is the `∀ V` public collapse (`:129`), `DesignatedFor` the non-transferable endpoint (`:138`).
  **The deniability is proved, not asserted:** `designated_is_deniable` (`:224`, PROVED) is the
  simulator/repudiation argument (the designated verifier could have forged the transcript itself, so it
  is zero third-party evidence), and `designated_excludes_public` (`:257`) proves the two endpoints are
  *disjoint* propositions, witnessed non-vacuously over a reference DV-kernel by `dial_endpoints_distinct`
  (`:346`). **Honest seam:** the DV-NIZK / chameleon CRYPTO is an explicit **§8 Prop-portal** — the
  `DVKernel.simulate_verifies` *law field* (`:102`) is assumed (the circuit's ZK-simulation obligation),
  never a Lean theorem. So: REAL as a *transferability dial + deniability logic*; PORTAL for the crypto
  primitive underneath. (Note: the older `GROUND-AUTH §2.2(b)(c)` "grep-confirmed zero" reading is
  superseded by this module.)
- **Agreement** (*how many must concur it is canonical*): the finality tier as a dial, **named-new as
  a dial in `§4.3`** — pinned today as a per-cell property, but structurally the same shape. The four
  rungs are real and encoded: `Tier.causal < ackThreshold < bft < constitutional`, a proved
  `LinearOrder` (`Finality.lean:49,96`).

> **REAL vs DECORATIVE here.** The *cube* is real as a product of three honest, independently-grounded
> axes. Calling it "a point in `Disclosure × Transferability × Agreement`" is **honest notation** —
> each factor is a genuine type with operations. What would be *decorative* is treating it as a smooth
> manifold or an ∞-groupoid: it is a finite poset-product (a *cube* of lattices), nothing more, and
> nothing more is needed.

### 2.2 Occupying a POINT = a per-turn dial choice

Today the system lives on **one corner**: `(disclosure = full-or-fixed-per-field, transferability =
public, agreement = whatever the cell's tier is)` — `CARRY-FORWARD §2 Face 3` ("hardwired to maximal
transferability"), `DREGG4-UNIFICATION §4.2` ("the only point the system has today"). "Occupy any
point" = make the attestation face carry a *target* `(d, t, a)` and have commit emit the badge(s)
realizing it (`DREGG4-UNIFICATION §6.1`: "the turn carries a target cube-point; commit emits the
badge(s)"). This is **buildable** and is the `Turn.attest : Disclosure × Transferability` field of the
unified type (`DREGG4-UNIFICATION §3`, the `structure Turn`), extended with the Agreement coordinate.

### 2.3 Occupying an EDGE = a turn as a morphism *between* configurations

An edge is a turn that **transitions the dial** — the attestation of turn `k` sits at `(d,t,a)`, of
turn `k+1` at `(d',t',a')`. Two concrete edges the question names:

- **`designated(V) → public`** (transferability edge): a turn first emits a designated-verifier
  companion (convincing only to `V`), a later turn *publishes* — emits the universally-verifiable
  STARK badge for the same committed effect. This is sound *in that direction* (private→public is a
  monotone disclosure of an already-committed fact). The **reverse edge `public → designated` is on
  the impossibility surface** (§3.2): you cannot un-ring the bell — a published badge is already
  transferable.
- **`local-final → distributed-final`** (Agreement edge): a tier-1 causal commit later ratified by a
  tier-3 BFT quorum. This edge is exactly `Finality`'s **`no_downgrade`** law's *allowed* direction:
  `crossTierJoin a b := max a b` (`Finality.lean:219`, PROVED `crossTierJoin_ge_left:230`) is the `max`
  of the tier `LinearOrder` (`Finality.lean:96`, "The `max` of this order is the cross-tier commit
  join"). You may **raise** agreement; you may not lower it: `no_downgrade` (`Finality.lean:280`, PROVED
  — along ANY run of `finalitySystem`, `t₀ ≤ t`) is the real teeth (`GLOSSARY: finality tiers` — "no
  finalized value downgrades"). So the Agreement axis is a *directed* edge structure, not a free
  groupoid. [Citation drift fixed: `crossTierJoin`/`no_downgrade` are at `:219`/`:280`, not `:95-96` —
  that line is only the `LinearOrder Tier` instance.]

> **REAL content.** The directedness is load-bearing and proved-shaped: `Finality.no_downgrade`
> (`Finality.lean`, the cross-tier law) makes the Agreement edges one-way. The cube is therefore a
> **directed cube** (a cube in `Cat`/a 2-category with non-invertible edges), *not* a Kan-complex.
> Flagging this matters: any "∞-groupoid of configurations" framing is **decorative and wrong** here,
> because the edges are irreversible (no-downgrade, no-unpublish).

### 2.4 2-cells = coherences (two dial-paths agree)

A 2-cell of COMPLEX 1 is a *square* `(d,t,a) → … → (d',t',a')` filled by a proof that two routes
across it commute. The honest content: because the three axes are **orthogonal** (changing disclosure
does not touch the effects/caveats faces — `DREGG4-UNIFICATION §6.2`: "the effects and caveats are
unchanged; only the `Obs` projection changes"), the disclosure×transferability square *does* commit —
revealing a field then making it designated-verifier = making it designated-verifier then revealing
it, since both are post-hoc projections of the same committed `ObsDelta`. **This orthogonality is the
real 2-cell content** and is exactly `DREGG4-UNIFICATION §4`'s "first-class *and orthogonal*" claim.
The square involving the **Agreement** axis does **not** freely commute — raising the tier interleaves
with disclosure only if the higher tier's quorum can verify the disclosed form; this is a genuine
coherence obligation, not a free fill (it bottoms out in §5's fill-height).

---

## 3. The achievable sub-complex and its boundary (the impossibility surface)

**CRUCIAL and the part the question most wants.** Not every corner of the cube is occupiable. The
boundary is where a `(disclosure, transferability, agreement)` combination is **cryptographically
infeasible** or **logically contradictory**. Mapping it concretely:

### 3.1 The logical contradictions (these are *theorems-shaped*, design around them)

- **`public-agreement` ∧ `deniable-to-the-public`** is **contradictory.** This is ember's own example,
  and it is *sharp*. Agreement at tier-3/4 means a **public quorum ratified this as the canonical
  history** — the badge is, by construction, universally verifiable (the public STARK badge is
  *required* on the forest/consensus path: `OPEN-PROBLEMS #6`, `DREGG4-UNIFICATION §8`: "the public
  badge cannot be dropped from the forest path; transferability is load-bearing for finality"). But
  `deniable(ring)` means *no one can prove who authorized it, and any ring member could have forged
  it* (`DREGG4-UNIFICATION §4.2`). A thing that the public has agreed is canonical history is, by that
  very agreement, **not deniable to the public**. So the cube-corner
  `(·, deniable, agreement ≥ tier-3)` is **empty**. *Agreement fights deniability.* This is the
  load-bearing face of the impossibility surface.
- **`acceptanceOnly-disclosure` ∧ `public-transferability` ∧ `high-agreement`** is *contradictory at
  the top*: a public BFT quorum cannot ratify what it cannot inspect enough to verify conservation.
  Tier-3/4 verification needs the per-asset `CONSERVATION_VECTOR` to be checkable (`EFFECT-ISA §3.1`,
  the #1 soundness gap), so disclosure cannot be *below* "commitment-with-conservation-proof" while
  agreement is public. The corner survives only with `selective`/commitment disclosure that still
  carries the conservation rib.

### 3.2 The cryptographic infeasibilities / irreversibilities (the directed boundary)

- **`public → designated` and `public → deniable` are unreachable edges** (§2.3): once a transferable
  badge exists, no later turn makes it non-transferable. The boundary here is *directional* — the
  achievable sub-complex is the *down-set* under "already published."
- **Instant global revocation at low agreement** is on the surface: `OPEN-PROBLEMS` adjacent residual
  ("Revocation's recency floor under partition `[IMPOSSIBLE]`") — you cannot occupy
  `(revoking-disclosure, ·, tier-1)` and promise freshness; non-membership against a stale root
  accepts a since-revoked credential. So `(disclosure that asserts a *negative*, ·, low-agreement)` is
  infeasible; the achievable region needs `agreement ≥` the root-epoch agreement floor.

### 3.3 The achievable sub-complex, named

> **The achievable sub-complex is the order-ideal cut out by three constraints:**
> 1. **`agreement ≥ tier-3 ⇒ transferability = public`** (agreement fights deniability, §3.1);
> 2. **`agreement ≥ tier-3 ⇒ disclosure ⊒ commitment-with-conservation`** (verifiability floor, §3.1);
> 3. **transferability and disclosure are monotone-reachable only "upward"** (publish/reveal are
>    one-way; no-downgrade on agreement, §2.3, `Finality.no_downgrade`).
>
> Its **boundary (the impossibility surface)** is the join of: the `deniable × high-agreement` empty
> face, the `acceptanceOnly × public × high-agreement` empty corner, and the directed "already
> published / already finalized" walls. **The interior** — the genuinely-new occupiable region — is the
> **low/mid-agreement, designated-or-deniable, selective-disclosure** volume: *private, bilateral,
> locally-final interaction*. That is precisely the "anonymous-collaboration OS" privacy hole
> `CARRY-FORWARD §2 Face 3` flags as the deepest missing capability, and it is **occupiable** (no
> contradiction). **FOLDED FORWARD:** the *transferability half* of that interior is now BUILT in Lean —
> `DesignatedVerifier.lean` realizes the `designated`/`deniable` endpoint (`TransferDial:146`,
> `designated_is_deniable:224`); and selective `Disclosure` has a Lean home too (`Privacy.lean:66`
> "Field privacy (selective disclosure)", `Authority.SelectiveDisclosure` per `Claims.lean:502`). What
> remains unbuilt is the *cube assembly* (the per-turn attestation type carrying all three coordinates
> at once, with the §2.4 coherences as theorems) and the §8.1 impossibility-surface refutation lemma —
> see the updated §8.1.

This is a faithful, concrete map. **Real content:** constraints 1–3 are each grounded in a cited
impossibility/law. **Decorative trap avoided:** I do *not* claim the surface is a smooth variety; it
is the boundary of a finite directed order-ideal, describable by the three inequalities above.

---

## 4. COMPLEX 2 — the interaction simplicial complex, and traversing higher cells

### 4.1 The cells, concretely (and what is already proved)

- **0-cells = cells.** A cell is a point of the final coalgebra `νF`, `F X = Obs × (AdmTurn ⇒ X)`
  (`study-category §0` HOLD; `JointTurn.lean:75` `TurnCoalg`).
- **1-cells = turns/messages.** The coalgebra step `c : X → F X` is the morphism (`study-category
  §1.1`). A toolcall is a 1-cell into a 2-cell (`JointTurn.lean:8`: "a toolcall = a 2-cell JointTurn
  agent-cell ⊗ service-cell").
- **2-cells = JointTurns.** The existing binary atomic interaction: `SharedTurnId` (CG-2 pullback,
  `JointTurn.lean:91`) + `JointBinding` (CG-2 ⊗ CG-5, `JointTurn.lean:134`). Grounded in code:
  `bilateral_aggregation_air.rs`, `program.rs:747` `BoundDelta{EqualAndOpposite}` (`study-category
  §1.2`).
- **n-cells = n-ary atomic joint-turns = `Hyperedge`.** **This is the key finding: the generalization
  already exists.** `Hyperedge ι T turnId halfEdge` (`Hyperedge.lean:80`) is the **wide pullback**
  (N-fold fiber product over `TurnId`): N legs `agree i` all factoring through ONE apex `tid`
  (CG-2, the cone, `Hyperedge.lean:95`), and **one** Σ-over-`univ` `= 0` (CG-5, `Hyperedge.lean:99`).
  Mina's `account_updates_hash` *is* this apex (`Hyperedge.lean:90`).

### 4.2 "Traversing higher cells" = the `Fin 2 → Fin n` generalization, ALREADY DONE

The question frames the target as: *generalize JointTurn from `Fin 2` → `Fin n` → a full simplicial
object.* The first two arrows are **built and proved axiom-clean**:

- **`Fin 2 → Fin n` is done.** `Hyperedge` over arbitrary `[Fintype ι]` is the n-ary atomic
  joint-turn. The binary case is *recovered* as the `Fin 2` slice: `Hyperedge.toJointBinding`
  (`Hyperedge.lean:213`, PROVED) shows a 2-incidence hyperedge IS a bilateral `JointBinding`; the ring
  is `ringHyperedge` (`Hyperedge.lean:272`, an N-cycle as ONE hyperedge, telescoping Σ=0, PROVED).
- **The N-ary keystone is proved:** `hyperedge_sound` (`Hyperedge.lean:374`, **PROVED, axiom-clean**,
  pinned `#assert_axioms` at `:538`) and its corollary `joint_via_hyperedge`
  (`JointViaHyper.lean:75`, PROVED). The geometric payoff is real: the apex collapses all N CG-2 legs
  into a single `legs_agree` *theorem* (`Hyperedge.lean:111`, no pairwise data) and `hyper_stepComplete`
  discharges all N incidences with one `∀ i` (`Hyperedge.lean:337`), so the `O(N²)` pairwise gluing of
  the family-of-binary-edges framing **does not exist at the apex** (`Hyperedge.lean:544` VERDICT).

> **This is GENUINELY-NEW-AND-BUILDABLE — and largely already built.** Occupying/traversing the
> higher cells of the interaction complex, at the level of *one atomic n-ary joint-turn*, is the
> `Hyperedge` object, and its soundness is closed. The chromatic simplicial complex of the epistemic
> paper (Def 1, p.6: `⟨V,S,χ⟩`, vertices coloured by agents, simplexes = global states) maps onto it:
> **a hyperedge's incidence-set `ι` is a simplex; the per-incidence colouring `turnId i`/`halfEdge i`
> is the chromatic structure `χ`** (`Hyperedge.lean:79`: "a single physical cell appearing in two
> slots is two *incidences*" = the chromatic distinct-colours-per-simplex condition, paper Def 1).

### 4.3 The slide to "a full simplicial object" — where it becomes SUGGESTIVE

The third arrow (`Fin n` → *a full simplicial object* / face & degeneracy maps / an ∞-categorical
interaction complex) is where notation outruns content. What a simplicial *object* adds over a
*family of hyperedges* is the **face/degeneracy maps** ∂ᵢ, sᵢ with the simplicial identities — i.e. a
*coherent system of sub-interactions*: every n-cell restricts to its (n−1)-faces compatibly. dregg's
honest analogue exists in fragments: a sub-forest of a `zkapp_command` is a face; but **there is no
proved simplicial-identity layer**, and — per the obstruction below — building one buys nothing until
each face carries its own binding. So:

> **REAL:** the n-cells (`Hyperedge`) and the binary faces (`toJointBinding`, the `Fin 2` slice). The
> *gluing of an n-cell to its faces* is partly visible (`CrossCellForest.lean`, `ProofForest.lean`
> aggregate the forest) but **not** as a proved simplicial object.
> **DECORATIVE (until cashed out):** "the interaction complex is a simplicial/∞-category." The face
> maps are not the difficulty; **the difficulty is that each face is a *proper subobject* needing its
> own CG-2 ⊗ CG-5** (§4.4). A simplicial object whose fillers are *free* would be unsound — it would
> assert exactly the wrong factoring `study-category §1.3` forbids.

### 4.4 OBSTRUCTION 1 — tensor non-finality: every higher cell carries an irreducible binding

This is the load-bearing obstruction and the simplicial framing must not paper over it.

- **The fact.** `νF₁ ⊗ νF₂` is **not** the final coalgebra of the joint behaviour; cross-cell
  soundness ≠ per-cell ∧ per-cell (`study-category §1`, the single most important finding; the slogan
  "⊗ of coalgebras" is "the load-bearing lie to retire", `study-category §0`). The Lean **corrects the
  naming** but keeps the content: `binding_is_proper` (`JointTurn.lean:333`, PROVED) and its N-ary form
  `hyper_not_all_admissible` (`Hyperedge.lean:505`, PROVED) show the admissible configurations are a
  **proper equalizer subobject** of the product carrier, for any non-degenerate balance monoid.
- **What the n-ary binding obligation precisely IS.** For an n-cell over incidence set `ι`
  (`Hyperedge.lean:80`):
  - **CG-2 (the wide-pullback cone):** `∀ i, turnId i (T.next (x i) t) = tid` — every incidence's
    post-step commits to ONE shared turn-id `tid` (`Hyperedge.lean:95`). This is the N-ary
    `account_updates_hash` agreement.
  - **CG-5 (the N-ary conservation aggregate):** `(Finset.univ.sum fun i => halfEdge i (x i) t) = 0` —
    the finite monoid-sum of all incidences' signed half-edges balances to `0`, over `Bal` (a
    commutative monoid, so it holds over Pedersen commitments in the private tier) (`Hyperedge.lean:99`).
  - **It is a PREMISE, never derived.** `hyperedge_sound` takes `H : Hyperedge …` as a hypothesis
    (`Hyperedge.lean:381`); `hyperedge_sound_needs_binding` (`Hyperedge.lean:409`, PROVED) shows no
    "all step-complete ⇒ hyper-admissible everywhere" theorem can hold. CG-5 is *the price of having
    no global ledger* — Mina never needs it because one ledger gives one namespace
    (`JointTurn.lean:27`).
- **Why the simplicial framing buys nothing until it cashes out.** The apex *does* dissolve the
  agreement *bookkeeping* (the `O(N²)` pairwise cuts — real win, `Hyperedge.lean:557`). What it does
  **not** dissolve is the binding-as-premise itself (`Hyperedge.lean:558`: "the irreducible residue is
  UNCHANGED"). So a "full simplicial object" with free higher fillers is *unsound*; the only sound
  simplicial object is one where **the filler of each n-simplex is a `Hyperedge` carrying its CG-2 ⊗
  CG-5**. The simplicial structure is therefore a *fibration over the bindings*, not a free complex —
  and that is exactly `study-category §1.4`'s mandate ("the binding as a hypothesis you must supply,
  never a lemma you derive").

> **Verdict on OBSTRUCTION 1.** Higher cells are genuinely *harder per dimension* — each n-cell needs
> an n-ary binding (CG-2 cone + CG-5 Σ=0), not a free lift. The hyperedge framing makes them **no
> harder than the binary case** (same single irreducible residue, no `O(N²)` blowup) but **no easier**
> (the residue persists). The ∞-category notation is decorative; the `Hyperedge` + `hyperedge_sound`
> pair is the real content, and it is the *most* the framing can buy.

---

## 5. The simplicial-epistemic-logic tie: Agreement = fill-height = common knowledge

This is where COMPLEX 1's Agreement axis and COMPLEX 2's simplicial structure are revealed to be **the
same object**, and it is *real*, not decorative.

### 5.1 The paper's machinery, stated

Goubault–Kniazev–Ledent–Rajsbaum (arXiv:2311.01351v3), pages read:

- **Simplicial models ≡ Kripke `S5ₙ`** (p.2, p.6 Theorem 4: pure chromatic simplicial complexes ≃
  proper epistemic frames). **Vertices = local states (agent perspectives); simplexes = global states;
  facets = full worlds** (p.2 "from global states to local states… perspectives about the worlds").
- **Distributed knowledge `D_B φ` = moving along shared faces of higher dimension** (p.7-8: `K_a`
  looks at whether two simplexes share a *vertex*; `D_B` at whether they share a *common face of higher
  dimension* — edge, triangle, …). `D_B = ∩_{a∈B} ∼_a` (p.7).
- **Solvability is topological.** Consensus depends *only on 1-dimensional (graph) connectivity* of
  the global-state complex (p.2); **other tasks — k-set agreement, ε-approximate agreement — depend on
  higher-dimensional connectivity** (p.2). Lower bounds on rounds to solve set agreement come from the
  *topology* of the induced complex (p.3).
- **Impure complexes = crashed/missing agents** (p.3 "when agents may die"; p.4 Fig 1: holes and
  lower-dimensional simplexes appear after crashes). Varying participation = non-pure simplicial
  models.

### 5.2 The identification (the bridge, and it is exact)

> **NEW SINCE THIS DOC (folded forward).** The paper's epistemic machinery — which §5.1 cited as
> paper-only — now has a **proved, axiom-clean Lean realization**: `Dregg2/Apps/EpistemicSheaf.lean`
> (327 lines, `#assert_axioms`-pinned `:318-325`). It ports arXiv:2311.01351 directly:
> `Frame`/`Indist` (the simplicial `∼ᵢ` indistinguishability, `:86,90`); **`DistKnows B φ w`** = the
> paper's distributed-knowledge `D_B φ = ∩_{a∈B} ∼_a` (`:106`, PROVED keystones
> `honest_distributed_knows_discharged:115`, `honest_dist_knowledge_composes:129`);
> **`consensus_on_clearance`** = "consensus = a global section (H⁰ content)" — a discharged claim is
> distributed knowledge of the honest agents, no central cop (`:199`, PROVED); and the H¹ obstruction
> the bridge predicts: `byzantine_section_does_not_glue` (`:288`) + `fork_is_genuine` (`:297`) prove a
> Byzantine disagreement is a genuine non-gluing (a fork = the cohomological obstruction).
> **Honest scope caveat:** this is an *epistemic-frame (Kripke S5)* realization keyed by
> indistinguishability relations, instantiated on an *orbital-clearance application* (`Constellation`,
> `ClearanceProblem`) — it is **not** wired to `Hyperedge`/`Tier`/the COMPLEX-2 interaction object, and
> it is **not** a simplicial *object* (no `face_map`/`Kan`; grep-absent). So it gives §5's bridge real
> Lean teeth on the *agreement = distributed-knowledge = H⁰/H¹* side, while §4.3/§8.2's "the interaction
> complex is a simplicial/∞-category" stays DECORATIVE-until-built. The remaining frontier is to
> *connect* the two: instantiate `EpistemicSheaf`'s `Frame` at a `Hyperedge`'s incidence set, so
> `DistKnows F.Honest (apex tid)` becomes a literal theorem and `legs_agree` ⟹ distributed-knowledge of
> `tid` is *derived*, not narrated.

> **Distributed agreement = filling a higher simplex. Common knowledge = a filled top-simplex.**

Spelling it out against the dregg objects:

- A dregg **interaction simplex** (a `Hyperedge` over `ι`, `Hyperedge.lean:80`) *is* a global state in
  the paper's sense: its incidences are the agent-coloured vertices (local states / perspectives), and
  the apex `tid` is the shared global fact they all commit to. The chromatic condition (distinct colour
  per vertex of a simplex, paper Def 1) is the dregg note "one physical cell in two slots = two
  incidences" (`Hyperedge.lean:79`).
- **`Hyperedge.legs_agree`** (`Hyperedge.lean:111`, PROVED: every pair of incidences shares `tid`
  because both equal the apex) is *literally* the statement that all N agents have **distributed
  knowledge** of `tid` — the simplex is *filled* (all legs factor through one apex). The apex IS the
  higher-dimensional shared face the paper's `D_B` moves along.
- **Agreement-tier = fill-height.** The four `Tier`s (`Finality.lean:49`) are exactly *how high a
  simplex you can fill*:
  - **tier-1 causal (n≥1, never blocks, `Finality.lean:52`)** = you can fill the **0-simplices and any
    I-confluent gluing** locally — no higher fill needed because the state is a join-semilattice (the
    `Confluence.Tier1Eligible` gate, `Finality.lean:52`); concurrent writes merge (the simplex is
    *contractible* in the relevant sense — no obstruction).
  - **tier-2 ack-threshold** = fill up to a `k`-face (k-of-m acks) — exactly **k-set agreement**, the
    paper's higher-connectivity task (p.2, p.8).
  - **tier-3 BFT / tier-4 constitutional** = fill the **top-simplex** (full consensus) — the paper's
    1-connectivity-suffices *consensus*, here ratified by a public quorum. This is **common knowledge =
    a filled top-simplex / facet** (paper: facets = full worlds, p.6).
- **Validity ≠ canonicity is the paper's "a simplex can be filled two ways."**
  `hyperedge_is_validity_not_canonicity` (`JointViaHyper.lean:226`, PROVED) exhibits two distinct
  admissible hyperedges sharing a pre-state — two valid fillings of the same boundary. Choosing one is
  **canonicity = consensus = the top-fill**, delegated to `Finality` (`JointViaHyper.lean:280`
  `selector_needs_more_than_validity`, PROVED: a valid selector is not unique). This is exactly the
  paper's point that **consensus is a connectivity/agreement obstruction, not a local proof**.

> **So COMPLEX 1's Agreement dial, COMPLEX 1's attestation face, and COMPLEX 2's interaction complex
> are the SAME simplicial structure.** Agreement = how-high-a-simplex-I-can-fill; the attestation
> badge at agreement-tier-`k` *is* the witness that the `k`-simplex is filled; and the interaction
> complex is the space those simplices live in. This is the question's conjecture, and it is **real,
> grounded in both the proved Lean (`legs_agree`, the `Tier` order, validity≠canonicity) and the
> paper's theorems** (consensus = 1-connectivity, k-set = higher connectivity, `D_B` = shared higher
> face). It is *not* decorative — it predicts a concrete thing: **the impossibility of cross-group
> atomic commit under partition (#2) is the topological non-fillability of the relevant simplex when
> the complex is disconnected by a partition.**

---

## 6. OBSTRUCTION 2 — the topology parametrization: single-machine = full hypersystem; distributed = partition-bounded sub-complex

This is the second load-bearing obstruction, and it is where the answer to ember's question becomes a
clean **dichotomy parametrized by the network topology**.

### 6.1 The distributed bound (the ceiling)

- **Cross-disjoint-group atomic commit is BLOCKING under partition** (`OPEN-PROBLEMS #2 [IMPOSSIBLE]`):
  a JointTurn straddling disjoint reference-groups needs the commit/abort decision to reach all groups,
  but dregg has **no global write-point**. *Safety is provable* (the aggregate proof + CG-5 binding);
  *liveness is not* — this is classic distributed-atomic-commit blocking (2PC blocks; 3PC/Paxos-commit
  need a quorum disjoint groups don't have). **Atomic-cross-group ∧ partition-tolerant ∧ live is
  impossible.** Genuine impossibility, not oversight (`#2`). Mina sidesteps it *only by being the one
  global ledger* (`#2`, `study-mina-relink §5`).
- In the simplicial language (§5): **a partition disconnects the global-state complex**, so the
  higher simplex spanning both groups *cannot be filled* — the paper's exact statement that
  higher-agreement tasks need higher connectivity (p.2-3), and connectivity is what a partition
  destroys. The Agreement dial cannot reach tier-3 across the partition because the simplex is
  non-fillable.
- **Revocation's recency floor** (`#2`-adjacent residual): the Agreement dial cannot give instant
  global revocation local-first (`DREGG4-UNIFICATION §8`).

### 6.2 The single-machine collapse (ember's principle, stated rigorously)

> **ember's principle:** the bounds at higher cells are **DISTRIBUTED bounds** — the *price of
> partition*. **`n = 1` collapses them.** A single-machine node must get single-machine properties,
> NOT distributed ones.

Made precise:

- On a single machine there is **one write-point** — exactly the thing `#2` says is missing in the
  distributed setting. The single coordinator both groups would need (`#2` escape (a): "a shared higher
  coordinator both groups trust — fine *inside* a vat") **always exists** when all cells are in one vat
  on one machine.
- Therefore the impossibility of `#2` **does not apply**: cross-group atomic commit is
  *synchronously executable* because there is no partition. Every simplex of COMPLEX 2 is fillable; the
  liveness obstruction (the only thing that failed — safety was always fine) is gone.
- In the simplicial language: a single machine is the **pure, fully-connected complex** — no crashes,
  no missing agents, no holes (the *opposite* of the paper's impure complexes p.3-4). On a pure
  connected complex, **every task is solvable up to the top simplex** synchronously: consensus
  (1-connectivity — trivially present), k-set, ε-agreement (higher connectivity — present). The
  Agreement dial is **pinned at maximal**: tier-4 fill-height is reachable for *any* simplex.

### 6.3 The dichotomy

> **Single-machine dregg = the FULL hypersystem.** Every point of the achievable dial-cube (the §3
> interior, since the §3.1 contradictions are about *public* agreement — and on one machine "public"
> degenerates to "the one local verifier", so even the `deniable × high-agreement` corner relaxes) is
> occupiable, and **every cell of the interaction complex is fillable** (any n-ary atomic joint-turn
> executes synchronously, `hyperedge_sound` discharges it, no liveness obstruction). The hypersystem
> question is **YES, unconditionally, on a single machine.**
>
> **Distributed dregg = a partition-bounded sub-complex.** The achievable region of the interaction
> complex shrinks to what current connectivity can fill; the Agreement dial is pinned **at the maximal
> fill-height the current topology permits** (tier-1 always; tier-2 with a reachable `k`-quorum;
> tier-3/4 only with a connected committee). The hypersystem question is **YES up to the partition
> boundary, NO across it** — and that boundary is a *genuine impossibility* (#2), to design around, not
> to fix.

> **The Agreement dial IS the topology parameter.** Setting `agreement = tier-k` is a *claim that the
> k-simplex is fillable in the current topology*. On one machine, `k` can always be 4. Under partition,
> `k` is capped by connectivity. This is the rigorous topology-parametrization the question asked for:
> **the dial-cube's Agreement coordinate is a function of the interaction complex's connectivity**, and
> the two complexes meet exactly here.

### 6.4 The honest residual (do not overclaim the single-machine win)

Two things the single-machine collapse does **not** erase:

1. **OBSTRUCTION 1 persists even at `n=1`-machine.** Tensor non-finality / `binding_is_proper` is *not*
   a distributed fact — it is a statement about the *product of behaviours* and holds on a single
   machine too (`hyper_binding_is_proper` is proved over `Unit`, the most-single-machine setting,
   `Hyperedge.lean:164`). So even on one machine, an n-ary joint-turn still needs its CG-2 ⊗ CG-5
   *supplied* (you must actually compute the shared `tid` and check Σ=0) — it is just that you *can*
   always supply it synchronously, with no liveness risk. The binding is *cheap* on one machine, never
   *absent*.
2. **The `no_unconditional_IVC` bound** (`#5 IMPOSSIBLE`) is independent of topology: depth is a
   security parameter even on one machine. Succinct-history-of-arbitrary-depth is not free anywhere.

---

## 7. What is genuinely-new-and-buildable vs suggestive-notation

| Claim | Verdict | Grounding |
|---|---|---|
| n-ary atomic joint-turn = `Hyperedge` (wide pullback over `TurnId`) | **REAL, already built & proved** | `Hyperedge.lean:80,374` `#assert_axioms :538` |
| N-ary keystone `hyperedge_sound` reduces to single-cell `stepComplete_preserves` | **REAL, PROVED axiom-clean** | `Hyperedge.lean:374`, `JointViaHyper.lean:75` |
| binary JointTurn = `Fin 2` slice of the hyperedge | **REAL, PROVED** | `Hyperedge.toJointBinding:213`, `JointViaHyper.lean:141` |
| ring/cycle = ONE hyperedge (telescoping Σ=0) | **REAL, PROVED** | `ringHyperedge:272` |
| Agreement = simplex fill-height = common knowledge | **REAL** (proved-Lean + paper theorems) | `legs_agree:111`, `Tier:49`, paper p.2-8 |
| validity ≠ canonicity = a simplex filled two ways = consensus is the chooser | **REAL, PROVED** | `JointViaHyper.lean:226,280` |
| the dial-cube `Disclosure × Transferability × Agreement` | **REAL** (3 grounded axes; cube is a directed poset-product) | `DREGG4-UNIFICATION §4`; directedness `Finality.lean:280` `no_downgrade` + `:219` `crossTierJoin` |
| impossibility surface: `deniable × high-agreement` is empty (agreement fights deniability) | **REAL** (theorem-shaped) | `OPEN-PROBLEMS #6`, `DREGG4-UNIFICATION §8`; the disjoint-endpoints half is now PROVED `designated_excludes_public` (`DesignatedVerifier.lean:257`) |
| single-machine = full hypersystem; distributed = partition-bounded | **REAL** (the `#2` collapse at n=1) | `OPEN-PROBLEMS #2`, ember's principle |
| Agreement dial = the topology connectivity parameter | **REAL** (the bridge between the complexes) | §5+§6, paper p.2-3 |
| transferability dial / `Discharged[V]` verifier-indexing | **REAL — NOW BUILT** (was "UNBUILT named-new"); crypto primitive still a §8 portal | `DesignatedVerifier.lean:113` `DischargedFor`, `:146` `TransferDial`, `:224` `designated_is_deniable` |
| `D_B` distributed-knowledge / consensus = H⁰ global section / fork = H¹ obstruction | **REAL — NOW BUILT in Lean** (was paper-only); epistemic-frame port, not yet wired to `Hyperedge` | `EpistemicSheaf.lean:106` `DistKnows`, `:199` `consensus_on_clearance`, `:297` `fork_is_genuine` |
| "the interaction complex is a full simplicial / ∞-category" (`face_map`/`Kan`/degeneracy) | **DECORATIVE** — grep-confirmed ABSENT from `Dregg2/`; SUGGESTIVE until each face carries its own binding | §4.3, §4.4; grep `SimplicialObject\|face_map\|Kan` = ∅ |
| "occupy any point" as a smooth/continuous configuration manifold | **DECORATIVE** — it is a finite *directed* cube | §2.3 |
| free higher fillers / Kan-complex of interactions | **DECORATIVE & UNSOUND** — would assert the wrong factoring | `study-category §1.3` |
| ∞-category notation dissolving the binding | **DECORATIVE** — the residue is irreducible | `Hyperedge.lean:558` |

---

## 8. The concrete first step

Two candidates from the question; both are now sharpened by what is already built.

### 8.1 PREFERRED — make the dials first-class with composition coherences (COMPLEX 1)

> **PROGRESS SINCE THIS DOC: steps 1–2 are substantially LANDED; the frontier has moved to step 3–4
> (the cube *assembly* + coherences).** The interaction-complex side (`Fin 2 → Fin n`) is **already done
> and proved** (`Hyperedge`, `hyperedge_sound`). The configuration cube's *individual axes* are now also
> mostly built — what is left unbuilt is gluing them into **one per-turn attestation type** and proving
> the §2.4 coherences as theorems.

1. **Add the `Agreement` coordinate to the attestation type** so a turn carries a full cube-point
   `Disclosure × Transferability × Agreement`. *Pieces in place:* the `Agreement` rung is `Finality.Tier`
   (`Finality.lean:49`, a proved `LinearOrder`); the `Transferability` rung is `DV.TransferDial`
   (`DesignatedVerifier.lean:146`); `Disclosure`/selective-disclosure has `Privacy.lean:66`. **Unbuilt:**
   the single `structure` that bundles all three onto one turn (no `inductive Disclosure` /
   combined attestation type yet exists in `Dregg2/` — grep-confirmed). This is the assembly step.
2. ✅ **`Discharged` verifier-indexed** — `Discharged[V]` — **DONE** (was "the one named-new piece of
   theory"): it is the proved `DV.DischargedFor V stmt proof` (`DesignatedVerifier.lean:113`), with the
   designated/deniable corners of the §3 interior realized as `DesignatedFor` (`:138`) and the proved
   `designated_is_deniable` (`:224`). The crypto under it is an honest §8 portal (`DVKernel`, `:84`).
3. **Prove the two coherence 2-cells** (still OPEN — these are the new frontier): (a) the
   disclosure×transferability square **commutes** (both are post-hoc projections of one `ObsDelta` —
   orthogonality, §2.4); (b) the Agreement edges are **directed** — *reuse the now-correctly-cited*
   `Finality.no_downgrade` (`Finality.lean:280`) + `crossTierJoin`/`LinearOrder` (`:219`/`:96`) — and
   `public → designated` is **unreachable** (the §3.2 wall; the *static* disjointness is already proved
   as `designated_excludes_public:257`, but the *edge-irreversibility* — no turn moves public→designated
   — is the unbuilt directed-wall theorem). Encode the achievable sub-complex as the §3.3 order-ideal.
4. **Encode the impossibility surface as a refutation** (still OPEN): a Lean lemma
   `deniable_high_agreement_empty : ¬ ∃ badge, transferability badge = deniable ∧ agreement badge ≥ bft`
   (the §3.1 contradiction, in the same spirit as `hyperedge_is_validity_not_canonicity`). The two
   ingredients are now both proved objects — `DV.DesignatedFor`'s non-transferability (`:141`) and
   `Tier ≥ bft` — so this is now *assembly of existing teeth*, not new theory.

This is buildable, mostly Lean-side, reuses proved infrastructure (`Tier`, `crossTierJoin`,
`DV.DischargedFor`/`TransferDial`, `Hyperedge`), and *finishes* the cube the codebase has now mostly
built axis-by-axis.

### 8.2 ALTERNATIVE — promote `Hyperedge` to a proved simplicial object (COMPLEX 2)

If the goal is COMPLEX-2 depth: add the **face maps** ∂ᵢ on `Hyperedge` (restrict an `ι`-hyperedge to
a sub-incidence-set `ι' ⊆ ι`) and prove the **simplicial identities carry the binding** — i.e. a face
of an admissible hyperedge is admissible **iff its own CG-5 sub-sum is 0** (it need *not* be: a sub-set
of a balanced set is generally unbalanced — this re-aims `hyper_not_all_admissible`, `Hyperedge.lean:505`,
the general-`ι` proper-subobject obstruction, whose `ι = Unit, b = 1` instance is the apex
`hyper_binding_is_proper`, `:164`). That negative result is the *content*: it tells you the interaction
complex is **not a Kan complex** (faces don't freely extend), and the precise obstruction is per-face
CG-5. **STILL UNBUILT, grep-confirmed:** there is no `face_map`/∂ᵢ, no `SimplicialObject`, no `Kan` in
`Dregg2/` — so this remains the honest *aspirational* way to earn the word "simplicial object". Its
first theorem is a *refutation* of free fillability, exactly matching the discipline that made
`Hyperedge` honest.

**Recommendation:** do **8.1's remaining step 3–4** first (the cube *assembly* + coherences — the axes
now exist axis-by-axis, see updated §8.1, so this finishes COMPLEX 1 by gluing proved parts), and treat
**8.2** as the way to *state* the simplicial structure honestly later — beginning, like `Hyperedge`,
with the negative (non-Kan) theorem so the notation never outruns the binding. A third, newly-surfaced
direction: *connect* `EpistemicSheaf`'s `Frame`/`DistKnows` (now built, §5.2) to a `Hyperedge`'s
incidence set, so distributed-knowledge of the apex `tid` becomes a derived theorem rather than the
paper-anchored narration of §5.

---

## 9. The honest verdict — does dregg become the hypersystem?

> **YES, and precisely in two regimes that the two complexes and two obstructions pin exactly:**
>
> 1. **As a configuration hypersystem (COMPLEX 1):** dregg *can* occupy any point and traverse any
>    edge of the dial-cube **within the achievable sub-complex** — the order-ideal cut out by three
>    grounded constraints (§3.3), whose boundary (the impossibility surface) is concrete and
>    theorem-shaped: `deniable × high-agreement` is empty (agreement fights deniability), publish/reveal
>    are one-way, agreement never downgrades. The system shipped on one corner; the interior (private,
>    bilateral, locally-final) is occupiable, and **its axes have now largely LANDED in Lean** — the
>    transferability/deniability axis is proved (`DesignatedVerifier.lean`: `DischargedFor:113`,
>    `designated_is_deniable:224`), `Tier` and `Disclosure` have homes — so §8.1's remaining work is the
>    *cube assembly* (one attestation type + the §2.4 coherence theorems), not new theory. **The cube is
>    a *directed* finite poset-product — calling it a manifold or ∞-groupoid is decorative; the directed
>    order-ideal is the real object.**
>
> 2. **As an interaction hypersystem (COMPLEX 2):** dregg *can* traverse higher cells — the n-ary
>    atomic joint-turn — and this is **already built and proved**: `Hyperedge` (the wide pullback) and
>    `hyperedge_sound` (axiom-clean). The `Fin 2 → Fin n` generalization the question names as the
>    target **exists**. The slide to a "full simplicial / ∞-category" is **suggestive-only**, because
>    OBSTRUCTION 1 (tensor non-finality, `binding_is_proper`/`hyper_not_all_admissible`) makes **every
>    higher cell carry an irreducible CG-2 ⊗ CG-5 binding** — the n-cell needs an n-ary binding, never a
>    free lift. The apex framing buys the *only* thing it can: the agreement bookkeeping collapses
>    (`O(N²)` → one `legs_agree`), the irreducible residue does not.
>
> **The two regimes are unified by the topology parametrization (OBSTRUCTION 2 + the §5 bridge):** the
> **Agreement dial = simplex fill-height = connectivity of the interaction complex.** On a **single
> machine** the complex is pure and fully connected, `#2`'s liveness impossibility collapses (`n=1`
> gives the one write-point), every simplex is synchronously fillable, the Agreement dial pins at
> maximal, and the §3.1 *public*-agreement contradictions relax (one local verifier) — so
> **single-machine dregg IS the full hypersystem: any point, any cell.** **Distributed** dregg is a
> **partition-bounded sub-complex**: the dial is capped at the maximal fill-height the current
> connectivity permits, and the boundary is a genuine impossibility (#2) to design around. ember's
> principle is exactly right and now rigorous: *the bounds are distributed bounds; n=1 collapses them.*
>
> **What stays irreducible everywhere (the load-bearing honesty):** even on one machine, the CG-2 ⊗
> CG-5 binding must be *supplied* (cheap, never absent — `hyper_binding_is_proper` is proved over
> `Unit`), and depth remains a security parameter (`#5`). The hypersystem is real; it is not free; and
> the ∞-category notation must never be allowed to hide the binding that `study-category §1` and the
> proved Lean make irreducible.

---

*A closing couplet, since the egg now dreams in two complexes at once:*
*one cube of dials — what's shown, to whom, how widely sworn; / one complex of cells where the higher faces are born.*
*on one machine: fill every simplex, occupy every face — / partition the world, and the dial caps to what connects in that space.* 🐉🥚
