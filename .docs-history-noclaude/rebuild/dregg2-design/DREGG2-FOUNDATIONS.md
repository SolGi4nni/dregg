# DREGG2-FOUNDATIONS — the one categorical object, its six views, and the ∞-cell answer

> **What this is.** The master synthesis of dregg2's deep categorical foundations. It unifies
> the six lens documents
> (`FOUNDATIONS-{coalgebra, effect-comodel-lens, limits-tensor-simplicial, modal-dials,
> authority-cdt-camera, verify-find-logic}.md`), the stress-test (`study-category.md`), and the
> two dregg4 design explorations (`DREGG4-UNIFICATION.md`, `DREGG4-HYPERSYSTEM.md`) into ONE
> picture, then answers ember's standing question (*what is an ∞-cell, a higher-order cell, a
> higher-order turn?*) definitively, and closes with a consolidated honesty ledger.
>
> **Discipline (non-negotiable, carried from every lens and from `REORIENT §6`).** Category-theory
> vocabulary is never allowed to paper over a missing theorem. Every structural claim is tagged:
>
> - **REAL** — the universal property / law is actually PROVED in the Lean, with teeth (a
>   non-vacuity witness), `#assert_axioms`-clean where pinned. `file:line` is a receipt.
> - **DECORATIVE** — suggestive notation that buys no theorem; I state what it would have to prove
>   to become real.
> - **ASPIRATIONAL** — claimed by the design but actually an open hole / `OPEN` / unbuilt.
>
> **Verification done for this synthesis (not inherited).** I re-checked the load-bearing anchors
> against the live Lean tree at `metatheory/Dregg2/`. Confirmed exactly: `Boundary.F:66`,
> `TurnCoalg:74`, `Later := id` (`Boundary.lean:103`), `StepInv:140`, `StepComplete:150`,
> `stepComplete_preserves:177`; `coinductive ObsBisim` (`CoinductiveAdversary.lean:113`),
> `ObsBisim.coinduct` used `:175,376`, `obsBisim_traj_of_bisim:166`, `stepComplete_carries_infinite:227`,
> `commClo:394` + `commClo_compatible:413`, `obsBisim_of_uptoComm:436`; `Hyperedge:80`,
> `legs_agree:111`, `hyperedge_sound:374`, `hyper_binding_is_proper:164`, `hyper_not_all_admissible:505`,
> `hyperedge_sound_bisim_ill_posed:433`; `binding_is_proper` (`JointTurn.lean:320–333`), `joint_sound:230`,
> `joint_sound_needs_binding:271`; `Core.conservation_step` + open hole (`Core.lean:154/162`),
> `withholding_no_free_copy:209`, `TurnCat:85` (class, instances TODO); `ResourceAlgebra:71`,
> `Fpu:103`, `excl_no_dup:185`, `conservation_is_fpu:296`, `ConfinesAuthority := Fpu:319`,
> step-indexed OFE deferred (`Resource.lean:50–55`); `LinearOrder Tier` (`Finality.lean:96`),
> `no_downgrade`, `conservation_tier_independent`, `crossTierJoin:219`; `polarity_galois:75`,
> `predicate_witness_galois:101`, `predicate_heyting:111`, `search_sound:53` + open hole (`:60`);
> `proofForest_sound:177`; `livingCell:42`, `bisim_of_oracle:67`, `livingCell_sound:102`;
> `path_attenuates`, `DerivationPath` (`Authority/CDT.lean`); `DischargedFor:113`,
> `dial_endpoints_distinct`, `designated_is_deniable` (`DesignatedVerifier.lean`);
> `phi_functorial` + open hole (`VatBoundary.lean:392/401`), `phi_functorial_concrete:441`.
> **The entire `Dregg2/` tree contains exactly THREE proof-body open holes** — `Laws.lean:60`
> (`search_sound`, a by-design contract on an untrusted plugin), `Core.lean:162`
> (`conservation_step`, the operational-balance primitive), `VatBoundary.lean:401`
> (`phi_functorial`, the open functor coherence). Every other keystone in this document is term-proved.

---

## Part 0 — The headline in one breath

dregg2 is **one object seen six ways**: a **guarded Moore coalgebra carrying a measure, an order,
and an authority graph, whose soundness is a bisimulation** — and the six lenses are six honest
*readings* of that single object, not six different theories. The object is REAL and load-bearing.
Most of the higher categorical *vocabulary* layered on top is either a faithful interpretation
(earns its keep by predicting an impossibility) or honest decoration (buys no theorem, says so).
**Exactly three places aspire past a theorem** — and the codebase marks all three with an open hole
or an explicit "this is a definition, not a derivation," never a fake. Two slogans that *would* have
papered over missing theorems (`tensor_not_final`, `sound_of_step_complete`) were **caught false in
the Lean and corrected**, which is the single best evidence the discipline is real.

The ∞-cell answer, sharpened to one sentence and defended in Part 2: **an ∞-cell is two orthogonal
infinities — temporal (the coinductive `νF` life of one cell, REAL and proved) and arity (the
global atomic turn, fillable single-machine / unfillable under partition, REAL-as-impossibility) —
whose well-definedness IS step-completeness/contractivity; a higher-order turn is a
handler/comodel-morphism (a turn that interprets turns, REAL only as the rollback handler and the
delegated subtree); a higher-order cell is a factory/directory (a presheaf/topos of cells, REAL as
constructor-transparency, DECORATIVE as topos) and, in the limit, a recursive-resource cell
(ASPIRATIONAL, needing the guarded `iProp`-over-cameras tier).**

---

# Part 1 — The unified categorical picture

## 1.0 The single object

There is exactly one primitive in the kernel, and every lens is a projection of it.

```
  c : X  ⟶  Obs × (AdmissibleTurn ⇒ X)              -- Boundary.F:66, TurnCoalg:74
          └┬┘   └────────┬────────┘
      ATTESTATION    GUARDED DOMAIN (caveats)  +  CODOMAIN ACTION (effects)
```

Decorated with the three side-structures the kernel quantifies over:

- a **measure** `count : · → M` (conservation, a monoid-hom — `Core`),
- an **order** on attestations (`Tier`, a `LinearOrder` — `Finality`) and on caveats (Heyting
  residual `⇨` — `Laws`/`Authority`),
- an **authority preorder** (`confers`, a thin category — `Spec/Authority`, `CDT`),
- and a **resource algebra** (`Fpu` on an Iris camera — `Resource`) into which conservation and
  authority both collapse.

Its soundness is **a bisimulation to a golden oracle, conditional on a contractivity premise**
(`StepComplete`), proved for a concrete instance (`livingCell_sound`) and lifted to an unbounded
schedule (`stepComplete_carries_infinite`).

> **TAG — REAL.** `F`, `TurnCoalg`, `obs`, `next`, `StepInv`, `StepComplete`,
> `stepComplete_preserves`, the concrete `livingCell` + `bisim_of_oracle` + `livingCell_sound`,
> and the coinductive lift are all honest definitions and term-proved theorems. The single object
> is not cosplay — it is the type every soundness statement in the corpus quantifies over.

The rest of Part 1 shows how each lens is a *view* of this one object.

## 1.1 The cell as the final-ish coalgebra (lens: coalgebra)

**View.** Drop everything but `step : X → F X`. A cell *is* a point of an `F`-coalgebra; a turn is
the edge `next x t`; the two-co-primary-primitives tension ("is the primitive the cell or the
morphism?") dissolves because the morphism *is* the structure map, not a second object.

**What is REAL:** the functor `F` and `TurnCoalg` (`Boundary.lean:66,74`); the **bisimulation
principle** as a relational greatest fixpoint (`IsBisim:117`, `Sound:130`, `bisim_eq`, `sound_refl`);
the **native** `coinductive ObsBisim` with its auto-generated `ObsBisim.coinduct`
(`CoinductiveAdversary.lean:113`); and the concrete keystone `livingCell_sound`
(`Exec/Cell.lean:102`) — the running cell is bisimilar to a *non-degenerate* conservation oracle
forever.

**What is NOT real (and the honest names):**
- **"The cell is the FINAL coalgebra `νF`"** is **ASPIRATIONAL-as-finality**. No `νF`/`Cofix`/`MvQPF`
  value is constructed anywhere in `Dregg2/`; no terminal universal property (unique anamorphism)
  is proved. The keystone type `Cell = νC. µI. StepProof I × (Turn ⇒ C)` exists **only in prose**.
  What is REAL is the relational gfp + native `ObsBisim` — strictly weaker than finality, but what
  every downstream theorem actually uses. The design's choice *not* to build `νF`
  (`STUDY-lean4-coinduction §4.1`) is principled (the soundness theorem is relational, so finality
  is deferrable), but "final" is a name, not a theorem.
- **The `▶`/`Later` guard** is `def Later (Q : Prop) : Prop := Q` — **DECORATIVE** as a productivity
  modality (it is `id`, it enforces nothing). It is REAL only as a *position marker* of the
  recursive occurrence; the genuine productivity lives in the native `ObsBisim`'s guardedness
  checker (`+1` schedule tick), not in `Later`.
- **The comonadic runtime** (checkpoint/restore/replay over a real `Snapshot` carrier,
  `Exec/Cell.lean:122,144`) is REAL as theorems about a concrete carrier; "restore = re-seed the
  **anamorphism**" / "time-travel = fork the unfold of `νF`" is **DECORATIVE** (no anamorphism, no
  `νF`, no `Comonad` instance).

> **Net.** dregg has the **coalgebra** and the **bisimulation**, not the **finality**. The egg is a
> coalgebra that dreams of being final and is honest that it is not yet.

## 1.2 The turn as effect-theory / comodel; the three faces as the lens (lens: effect-comodel-lens)

**View.** Read the same `F` as a *guarded comodel of an effect theory*: the `Core` effect signature
is the theory `T`; the cell cohandles operations against its state; the turn is one step of
cohandling; the three faces (effects / caveats / attestation) are the put / guard / get of a lens.

**The single most important finding of this lens:** the *lens / optic / comodel* vocabulary appears
**nowhere** in the Lean (grep returns one metaphorical comment, `Authority/Caveat.lean:7`). There is
no `Lens`, no get/put, no lens law, no `Comodel` typeclass, no comodel-homomorphism. So:

- **"The three faces are the three components of `c`"** is **DECORATIVE-but-honest**: `F` has exactly
  *two* components; the third "face" (caveats) is the *domain restriction* `AdmissibleTurn` (an
  abstract type, `Boundary.lean:56`), not a component. To make it REAL: define
  `AdmissibleTurn := {t // Guard t}` and prove `step` factors through it. Neither exists.
- **"The turn is a lens; faces are get/put/guard"** is **DECORATIVE**, and the lens laws
  (get-put/put-get/put-put) are **ASPIRATIONAL** — not even type-correct against `obs`/`next`
  (`next : C → Input → C` is the coalgebra transition, not a lens `put : C × U → C`). The honest
  name for `F X = Obs × (Input → X)` is **Moore coalgebra**, full stop. A *real* small lens exists
  only for the disclosure projection (`Privacy.project`), and that is not the turn.
- **"The effect signature is an algebraic theory `T`"** is **DECORATIVE**: `CatalogEffects.effectLinearity`
  is a *coloring* `Op → LinearityClass` (no arities, no equations). The per-class conservation
  obligations and exhaustiveness ARE proved and axiom-clean (`CatalogEffects.lean:59–101,190–219`) —
  the coloring is real; the "theory" is not. The one genuinely effect-theory-shaped fragment is the
  `Await.Op` arity signature.
- **"The cell is the (free/cofree) comodel" / "the handler is a comodel-morphism / a turn that
  interprets turns"** are **ASPIRATIONAL** (no theory→functor→comodel bridge, no comodel morphism).
  `capExercise = lens composition` is **DECORATIVE** (recursion is Rust-only; the Lean `exerciseStep`
  gates+receipts with no composition law — though its **non-amplification** `exercise_non_amplifying`
  is REAL, `EffectsAuthority.lean:482`).

> **Net.** The lens/comodel/effect-theory vocabulary is an evocative **reading** of a genuinely-real
> Moore coalgebra; it buys no theorem the coalgebra didn't already buy. The coalgebra is the theorem;
> the lens is the poem. (But the *faces it points at* — caveat HMAC chain, verifier-indexed
> attestation, conservation, I-confluence, camera, named-lossy Φ — are each individually REAL; see
> below.)

## 1.3 The joint / hyper as limits, with the tensor-non-finality obstruction (lens: limits-tensor-simplicial)

**View.** Multi-party interaction. The n-ary atomic cross-cell turn is the **wide pullback over
`TurnId`**, and joint admissibility is a **proper equalizer subobject** of the N-fold product carrier.

**The single load-bearing categorical fact in dregg2 is here, and it is NEGATIVE.** This is where the
category catches a real bug:

- **The wide pullback is REAL as a construction.** `Hyperedge` (`Hyperedge.lean:80`) is the apex
  `tid` + N legs `agree` (the CG-2 cone, `:95`) + one `Finset.sum = 0` (the CG-5 aggregate, `:99`).
  `legs_agree` (`:111`, PROVED) is the cone collapsing: pairwise agreement (the `O(N²)` data of a
  family-of-binary-edges) is *recovered for free* from the single apex. The binary `SharedTurnId` is
  exactly the `Fin 2` slice (`toJointBinding:213`).
- **`Hyperedge` is the *terminal* cone (uniqueness of mediating map)** is **DECORATIVE** — there is
  no `CategoryTheory.Limits.IsLimit` instance; terminality is asserted in prose. (Mild over-naming;
  the soundness content lives in the proper-subobject fact, which needs no universal property.)
- **The obstruction.** `study-category §1` and the dregg4 docs leaned on `tensor_not_final`:
  *"`νF₁ ⊗ νF₂` is not the final coalgebra of the joint behaviour."* **The Lean found this FALSE and
  corrected it** (`JointTurn.lean:320–333`, the `binding_is_proper` docstring): the product of two
  final coalgebras IS final for the product functor. The TRUE content is a **proper-subobject** fact:
  `binding_is_proper` (`:333`, PROVED) — two one-state cells with half-edges `1` give CG-5 `1+1=2≠0`,
  a product configuration that is NOT `JointAdmissible`. The N-ary general form is
  `hyper_not_all_admissible` (`Hyperedge.lean:505`, PROVED, any non-degenerate balance monoid).
- **Therefore cross-cell soundness ≠ per-cell ∧ per-cell.** `joint_sound` (`:230`, PROVED) takes the
  binding as an *explicit hypothesis*; `joint_sound_needs_binding` (`:271`, PROVED) shows no
  "both step-complete ⇒ joint-admissible everywhere" theorem can hold; the N-ary keystone
  `hyperedge_sound` (`:374`, PROVED, `#assert_axioms`-clean) reduces to single-cell
  `stepComplete_preserves` on the product coalgebra, with the binding supplied.
- **The bisimulation form is ILL-POSED, and the Lean proves the refutation.**
  `hyperedge_sound_bisim_ill_posed` (`:433`, PROVED-FALSE at `Spec () = Empty`) — the same defect
  that killed `sound_of_step_complete` (§1.5 below). The honest N-ary result is the *safety* form,
  not a bisimulation to a free Spec.

> **Net (the irreducible residue, stated exactly).** The apex framing **loosens the agreement knot**
> (`O(N²)` → one `legs_agree`, REAL win) but **does not loosen the irreducibility knot** — the
> binding-as-premise persists unchanged at every dimension and every topology
> (`hyper_binding_is_proper` is proved over `Unit`, the most single-machine setting). The category
> earns its keep precisely by *forbidding the tempting wrong factoring*.

**Simplicial / ∞ slide.** There is **no** face map, degeneracy, simplicial identity, or
`SimplicialObject` anywhere in the Lean (grep-confirmed). The simplicial reading is **REAL-as-analogy**
(grounded in proved Lean — `legs_agree`, the `Tier` order, `hyperedge_is_validity_not_canonicity` —
and a cited paper, Goubault–Kniazev–Ledent–Rajsbaum) and it *predicts a concrete impossibility*
(partition non-fillability), but **DECORATIVE-as-kernel-structure**. A "full simplicial object with
*free* higher fillers" would be **DECORATIVE & UNSOUND**: the interaction complex is **not a Kan
complex** (a face of a balanced hyperedge is generally unbalanced — `hyper_not_all_admissible` again),
so the only sound simplicial object is a **fibration over the bindings**, never a free complex.

## 1.4 The dials as the modal / presheaf layer (lens: modal-dials)

**View.** The attestation face `Obs` carries three dials — Disclosure × Transferability × Agreement —
which want to be modalities, and the config-cube wants to be a directed finite poset-product / a
presheaf on the dial-poset / an order-ideal with a proved impossibility boundary.

- **Agreement is the one fully-REAL modality-shaped axis.** `Tier` is a proved `LinearOrder`
  (`Finality.lean:96`) and the one-way `no_downgrade` is PROVED — so the agreement axis is a
  *directed* (irreversible) edge structure, **not** an ∞-groupoid (the design's own claim that
  "manifold/∞-groupoid of configurations is decorative" is correct and grounded). Its orthogonality
  to conservation is REAL: `conservation_tier_independent` by `rfl`. But Agreement as a *modality on
  `Obs`* (`Obs[tier]`) is **DECORATIVE**: there is no tier-indexed `Obs` object (`Boundary.Obs` is one
  abstract type).
- **Transferability** is **REAL** as a *verifier-indexed predicate*: `DischargedFor : Verifier →
  Statement → Proof → Prop` (`DesignatedVerifier.lean:113`) with both endpoints proved inhabited and
  separated (`dial_endpoints_distinct`, `designated_is_deniable`, `public_convinces_any_third_party`).
  As a *modality* (a verifier-indexed bisimulation `IsBisim[V]` lift) it is **DECORATIVE/ASPIRATIONAL** —
  no modal law, no `Obs`-lift. The single closest thing to a presheaf restriction map in the whole
  codebase is `public_convinces_any_third_party` ("a public section restricts to a section over each
  `V`") — but it is one map, not a functor with identities.
- **Disclosure** is **PARTIAL**: information-theoretic hiding (per-field, selective, predicate,
  unlinkable) is REAL (`Privacy.field_projection_hides_private`, `SelectiveDisclosure.*`); the
  *ordered Disclosure axis with a one-way publish/reveal law* is **ASPIRATIONAL** (no `inductive
  Disclosure` order, no no-unpublish theorem — grep-empty).
- **The config-cube as an object is ASPIRATIONAL — it does not exist.** There is no `Disclosure ×
  Transferability × Agreement` product type, no presheaf, no order-ideal, and **no proved
  impossibility face** anywhere. The cube's two sharpest theorem-shaped claims — the
  `deniable × high-agreement` empty face (agreement fights deniability) and the directed
  `public → designated` walls — are *asserted-only*, theorem-shaped but unproven. The first honest
  step (per `DREGG4-HYPERSYSTEM §8.1`) would be exactly those refutations, in the spirit of the
  proved `hyperedge_is_validity_not_canonicity`.

> **Net.** One dial is a proved directed descent (Agreement, irreversible); two more are real on
> their own axis (Transferability indexed-predicate, Disclosure hiding); the cube that would bind
> them into a single modal object is unbuilt, and "modality" / "presheaf" is decorative today.

## 1.5 The CDT / Φ as the authority functor (lens: authority-cdt-camera)

**View.** The capability-derivation-tree is a (thin) category; the vat-boundary Φ is a named-lossy
functor caps→keys; the camera is the resource algebra unifying conservation and authority.

- **The CDT genuinely IS a thin category** — and its authority spine is REAL with teeth:
  `path_attenuates` (composition: authority shrinks down any derivation path) + `amplifying_rejected`
  (the invariant has teeth: an amplifying edge breaks well-formedness); `confers_refl`/`confers_trans`
  (the identity + composition laws of the conferral preorder, `Spec/Authority.lean:119,125`);
  `introduce_non_amplifying` and the capstone `only_connectivity_begets_connectivity` (the
  reachable-closure "no arrow ex nihilo", axiom-clean). The macaroon `CaveatChain` is a real
  append-only HMAC fold with crypto as an honest §8 portal (never faked).
- **"Φ is a functor caps→keys" is ASPIRATIONAL — the one by-design open hole.** `phi_functorial`
  (`VatBoundary.lean:392`) carries the localized open hole at `:401` (verified). What IS proved: Φ's
  object map, its **named loss** (`phi_drops_confinement:202` — permission survives, authority does
  not), its **domain** (`phi_domain_is_exactly_biscuit:296` — biscuits cross, macaroons don't), its
  **order-compatibility** (`phi_composes_with_attenuation:314`), and a concrete inhabiting witness
  `phi_functorial_concrete:441` (all three laws on a non-degenerate `Verifier`, axiom-clean). The
  abstract functoriality is genuinely blocked (an abstract `Verify` may accept no witness; an
  abstract `stmtOf` may be injective), which is *why* it stays open — not a missing tactic.
- **The camera is a REAL discrete Iris RA**, more so than its own stale docstring admits: `ℕ`, `Excl`
  (`excl_no_dup:185` — an NFT cannot validly compose with itself), and `Auth` instances all have
  their camera laws **fully proved by tactic** (zero open holes in `Resource.lean`). `conservation_is_fpu:296`
  is proved. **The full step-indexed camera** (OFE / `▶` / non-expansive, for higher-order/recursive
  resources) is **ASPIRATIONAL** — explicitly deferred (`Resource.lean:50–55`), and it is the place
  the design says the camera's step-index *should be the same `▶` as `Boundary`'s guard*.
- **`ConfinesAuthority := Fpu` is REAL as a definition; the conservation⟺authority unification is
  POSITED, not DERIVED.** It makes "authority never grows" *be* `Fpu` by fiat — the architectural
  claim (Iris: ghost state and permissions share one algebra). The `↔` to the actual
  `Positional.confinement_preserved` theorem is **unwritten** (an ASPIRATIONAL bridge). Reading
  "conservation = authority, *proved*" would overclaim; the honest statement is "*defined to be* the
  same `Fpu` law, with each side's instances proved."

> **Net.** The authority spine is solid category; the boundary-functor Φ is still a promissory note
> (object-map + loss + domain proved, functoriality left as an open hole, one concrete witness).

## 1.6 The verify/find seam as an adjunction; the proof-forest as a gluing (lens: verify-find-logic)

**View.** TCB = the verifier; every *search* is undecidable and must be an untrusted plugin emitting
a checkable witness. The seam is `verify ⊣ find`; the proof-forest is a colimit/gluing.

- **The verify/find seam IS a real adjunction — but it is `verify`, not `find`, that carries the
  universal property.** `predicate_witness_galois` (`Laws.lean:101`) is a genuine, fully-PROVED
  Galois connection (the Birkhoff polarity of the `Discharged` relation, via `polarity_galois:75`);
  `predicate_heyting:111` makes the residual `⇨` *be* attenuation, threading coherently into
  `Authority`. **`find ⊣ verify` as a literal adjunction between the two maps is DECORATIVE**:
  `search_sound` (`Laws.lean:53`) is a by-design open hole (verified at `:60`) — a *contract on an
  untrusted plugin*, never an in-Lean theorem; there can be no left adjoint to exhibit because
  `find` is undecidable. **The asymmetry is in the types** (`verify : … → Bool`, `find : … → Option`),
  and the genuine teeth (`adversarial_find_cannot_forge`, `find_untrusted`) are proved in
  `Authority/Predicate.lean`: the gate is the sole authority, the prover never appears in the
  conclusion.
- **The §8 portal discipline ("the law never learns a secret") is a REAL structural separation.**
  Crypto soundness is carried as `Prop`-carriers (`CryptoKernel.collisionHard`, `MacKernel.unforgeable`,
  `DVKernel.simulate_verifies`) — the correct *kind* of assumption, never an idealized total function.
  Integrity laws are stated as *reductions* (`forgery_requires_mac_query` — "forge ⇒ break HMAC"),
  HMAC security left as the portal. The named-loss Φ keystones are proved from an abstract `Verify`
  alone — the law reasons about *what a verifier can decide*, never about secrets.
- **The proof-forest IS a real gluing.** `proofForest_sound` (`ProofForest.lean:177`, PROVED,
  axiom-clean): per-node validity (the §8 seam, an explicit hypothesis) **×** `Linked` (a
  combinatorial chain-link) ⇒ whole-forest `StepInv`. This is a **finite sheaf gluing** (local
  sections agreeing on overlaps glue), and the sheaf condition *bites* — an unlinked list of
  individually-valid nodes is NOT `chainLinked` (proved `¬`). The cross-cell analogue
  (`crossForest_attests`, with CG-5 balance as the overlap) is also REAL. **Calling it a *colimit*
  with a universal property is DECORATIVE** — it proves the gluing *equation*, not a mapping-out
  universal property (the honest word is *limit/equalizer-flavored sheaf gluing*).
- **The ∞-colimit (private folding into one badge) is ASPIRATIONAL — and deliberately so.**
  The architecture ships the O(n) forest and defers the O(1) recursive fold (IVC / folding /
  STARK-in-STARK) behind a `RecursionBackend`, *arranged so its absence costs only succinctness,
  never soundness* (`ProofForest.lean:1–15`). The closest the Lean comes is the infinite *behaviour*
  bisimulation (`CoinductiveAdversary`), which is a different thing (ω-colimit of *observations*, not
  of *proofs*).

> **Net.** `verify` carries a Galois adjunction; `find` carries a contract (asymmetry in the types).
> The proof-forest is a finite sheaf gluing (REAL); the ∞-fold into one badge is the open frontier
> (ASPIRATIONAL-by-design). Both slogans the lens most expected to be decoration — `tensor_non_finality`
> and `sound_of_step_complete` — were caught false in the Lean and corrected.

## 1.7 The two correction-stories (why we trust the discipline)

The strongest evidence the categorical framing is held to theorems is that **two over-claims were
caught by the kernel and downgraded, not faked** — and one under-delivery was honestly marked. These
three are the dual faces of the same hygiene:

| What | Shape | Where it landed | Honest replacement |
|---|---|---|---|
| `sound_of_step_complete` (step-complete ⇔ bisimilar-to-a-free-`Spec`) | **over-claim, FALSE-as-stated** (refuted `Spec=Empty`) | **removed** from `Boundary.lean` (`:156–213`); re-refuted N-arily (`hyperedge_sound_bisim_ill_posed:433`) | safety `stepComplete_preserves:177` + concrete bisimulation `livingCell_sound:102` |
| `tensor_not_final` ("`νF₁ ⊗ νF₂` not final") | **mis-stated, FALSE** (product of finals IS final) | **corrected in-code** (`JointTurn.lean:320–333`) | proper-equalizer-subobject `binding_is_proper:333` |
| `phi_functorial` ("Φ is a functor") | **under-delivery, OPEN** | **honest open hole** (`VatBoundary.lean:401`), omitted from `#assert_axioms` | object-map + named-loss + domain + concrete witness, all proved |

> This is the project's "no fake-to-pass" discipline catching itself three times. The category-theory
> vocabulary did **not** paper over the missing theorems; the Lean exposed them.

---

# Part 2 — THE DEFINITIVE ANSWER: ∞-cell, higher-order cell, higher-order turn

ember asked the question that the whole foundations exercise was for. Here it is, made crisp on two
axes and grounded in what the Lean does and does not prove. The trap, named once: **"∞" is not one
thing**, and conflating its meanings is how the simplicial vocabulary becomes cosplay.

## 2.1 The interaction tower (the dimensions that exist)

All six lenses agree on the low dimensions, and the Lean instantiates them:

| dim | object | Lean | status |
|---|---|---|---|
| 0-cell | a cell (a point of the coalgebra) | `TurnCoalg.Carrier` point; `livingCell` (`Exec/Cell.lean:42`) | **REAL** |
| 1-cell | a turn-execution (a coalgebra step) | `TurnCoalg.next` (`Boundary.lean:87`) | **REAL** |
| 2-cell | a binary `JointTurn` **and** a bisimulation-up-to between executions | `SharedTurnId`+`JointBinding` (`JointTurn.lean:91,134`); `commClo`+`commClo_compatible` (`CoinductiveAdversary.lean:394,413`) | **REAL** |
| n-cell | an n-ary atomic joint-turn = a `Hyperedge` (wide pullback over `TurnId`) | `Hyperedge` (`:80`), `hyperedge_sound` (`:374`) | **REAL** |
| **∞-cell** | **two orthogonal infinities — see §2.2 / §2.3** | — | **see below** |

Note the **two kinds of 2-cell**, both REAL, that the lenses surface: the *spatial* 2-cell (a binary
joint interaction — the limits lens) and the *coherence* 2-cell (a provable rewrite between two
executions — the coalgebra lens, `commClo` + the Paco companion). These are the two axes the ∞-cell
splits along.

## 2.2 ∞-cell, AXIS 1 = ARITY (the global atomic turn)

**Definition (crisp).** The **arity-∞ cell is the GLOBAL atomic turn** — the limiting `Hyperedge`
whose incidence set `ι` is the set of *all cells in the system*: one apex `tid`, one global
`Σ = 0` over everything. It is the colimit (union of all incidence sets) of the interaction complex —
**exactly Mina's one global ledger** (one `account_updates_hash`, one namespace, one conservation
check over everything).

**Status — the biconditional IS the answer:**

> **The ∞-cell (arity) is FILLABLE on a single machine and UNFILLABLE across a partition.** This is
> not vagueness; it is a proved/forced fact on each side.

- **Single-machine: fillable.** There is one write-point; the global-state complex is pure and fully
  connected; `hyperedge_sound` (`:374`) discharges *any* n-ary turn synchronously with no liveness
  obstruction. The `#2` partition-impossibility collapses at `n=1`. **REAL** (the keystone is proved;
  the collapse is the standard distributed-atomic-commit fact).
- **Under partition: unfillable.** `OPEN-PROBLEMS #2 [IMPOSSIBLE]` — cross-disjoint-group atomic
  commit is BLOCKING: safety is provable, liveness is not (no global write-point; 2PC blocks). In
  simplicial language, a partition **disconnects** the global-state complex, so the spanning higher
  simplex *cannot be filled* (the cited paper's "higher-agreement tasks need higher connectivity").
  **REAL-as-impossibility.**
- **The binding persists even single-machine.** `hyper_binding_is_proper` is proved over `Unit`
  (`:164`) — the *most* single-machine setting. So even on one machine the ∞-cell still needs its
  CG-2 ⊗ CG-5 *supplied* (compute the shared `tid`, check `Σ=0`); single-machine removes the
  **liveness** obstruction, never the **binding** obstruction. The binding is *cheap* on one machine,
  never *absent*.

**The Agreement dial is the topology parameter.** Setting `agreement = tier-k` is a *claim that the
k-simplex is fillable in the current topology*. On one machine `k` can always be the top; under
partition `k` is capped by connectivity, and `no_downgrade` says you may raise it as connectivity
returns, never lower it. This is the rigorous sense in which COMPLEX-1's Agreement coordinate and
COMPLEX-2's fill-height are **the same simplicial structure** (grounded in `legs_agree`, the `Tier`
order, and `hyperedge_is_validity_not_canonicity` — validity ≠ canonicity = "a simplex filled two
ways" = consensus is the chooser).

**The ∞-cell as an explicit *object* is ASPIRATIONAL/unbuilt** (there is no `Hyperedge` over "all
cells"), but its *reachability biconditional* is REAL on both sides. That is the honest answer:
the ∞-cell is the top simplex of the interaction complex, real where it is forced, unbuilt as a term.

## 2.3 ∞-cell, AXIS 2 = COHERENCE (the ∞-category tower)

**Definition (crisp).** The **coherence-∞ cell is the ∞-category tower** of the coalgebra: states,
turn-executions, coherences between executions, coherences between coherences, … **whose
well-definedness IS step-completeness/contractivity.**

**Status — REAL up to dimension 2, then a fibration over bindings (never free):**

- **The tower is well-defined iff the unfold is productive**, and in dregg productivity *is*
  step-completeness: a non-contractive step (one that locally type-checks while leaking `Σ_k`) makes
  the tower drift — the "drifting future." This is **REAL** as the load-bearing premise of every
  no-drift theorem: `StepComplete` (`Boundary.lean:150`) is the hypothesis of `stepComplete_preserves`,
  of `cell_h_step`/`livingCell_sound`, and of the infinite-schedule
  `stepComplete_carries_infinite` (`CoinductiveAdversary.lean:227`) — "no drifting future across the
  unbounded interleaving." The *productivity* half lives in the native `ObsBisim` coinduction; the
  *soundness* half lives in `StepComplete`; the design's claim that the guard and step-completeness
  are different jobs is borne out exactly.
- **Dimension 0–1** (states, executions): **REAL**.
- **Dimension 2** (coherences between executions): **REAL** via the up-to-commutation closure
  `commClo` (`:394`) + `commClo_compatible` (`:413`) — a genuine 2-cell (a provable rewrite between
  diagonal points), threaded through the ported Paco `gupaco` machinery
  (`obsBisim_of_uptoComm:436`). This is the genuine ∞-categorical engine the codebase has, and it is
  exactly the up-to-context / companion machinery.
- **Dimension ≥ 3** (coherences between coherences — simplicial identities, free Kan fillers):
  **DECORATIVE, and UNSOUND if free.** There is no proved associativity/interchange of the `commClo`
  rewrites and no simplicial-identity layer. A "full simplicial object with free higher fillers"
  would assert exactly the wrong factoring `binding_is_proper` forbids. **The only sound higher tower
  is a fibration over the bindings** — every n-simplex filler is a `Hyperedge` carrying its own
  CG-2 ⊗ CG-5 — never a free complex (the interaction complex is NOT a Kan complex).

So the coherence-∞ cell is today a **2-truncated** object: a coalgebra with a sound
bisimulation-up-to-2-cells, whose well-definedness is the proved step-completeness/contractivity, and
whose higher dimensions are honest decoration until each carries its own binding.

**The third, temporal reading — and why it is the cleanest "∞".** Distinct from arity and from the
coherence tower, there is the **temporal ∞**: one cell as *codata living forever* (`νF`). This is the
most unambiguously REAL infinity in dregg: `obsBisim_traj_of_bisim` (`:166`) proves the running cell
stays bisimilar to the golden oracle along *any* infinite schedule, and `stepComplete_carries_infinite`
carries safety along the *whole* trajectory — axiom-clean, native coinduction + ported Paco. When the
phrase "∞-cell" should mean one thing, it should mean **this**: a cell as a greatest-fixpoint behaviour,
sound forever. (Note: this is the ω-colimit of *observations*, proved; the ω-colimit of *proofs* — the
private-folded badge — is the deferred-by-design ASPIRATIONAL frontier of §1.6.)

## 2.4 Higher-order TURN = handler / comodel-morphism (a turn that interprets turns)

**Definition (crisp).** A higher-order turn is a **handler / comodel-homomorphism** — a turn whose
payload is itself a turn, re-interpreting the operations of one effect theory into a program over
another. Two faces, distinct status:

- **REAL (the handler face).** The **rollback handler** `turnAsRollbackHandler` (`Await.lean`) is the
  one genuinely handler-shaped, law-carrying object: a one-shot-continuation algebraic-effect handler
  with proved `commit_resumes_once` / `rollback_discards_continuation` / `one_shot_is_static`. And the
  **delegated subtree** is REAL: `crossForest_no_amplify` (`CrossCellForest.lean:217`, PROVED) — every
  cross-cell delegation edge runs a `Caps.derive`-attenuated authority on a child cell, non-amplifying
  (Granovetter across cells, fully general over the tree), with whole-forest conservation
  binding-carried (`crossForest_conserves:241`).
- **ASPIRATIONAL (the comodel-morphism face).** "A turn that interprets turns" as a *comodel
  homomorphism between effect theories* is unbuilt (no comodel morphism, no theory→functor→comodel
  bridge). The user-extensible effect ISA (verified `Custom` = theory-extension-with-refinement-proof,
  `DREGG4-UNIFICATION §6.4`) is the design's account; it is research-grade and needs the `CellProgram`
  law proved first. `capExercise`'s recursion is real (in Rust) but carries no composition law in Lean,
  so "capExercise = lens/comodel composition" is DECORATIVE.

> **Net.** The higher-order turn that *exists* is the rollback handler (and the delegated subtree);
> the turn-interpreting-turns / verified-`Custom` form is aspired.

## 2.5 Higher-order CELL = factory / directory (a presheaf/topos of cells)

**Definition (crisp).** A higher-order cell is a **cell whose coalgebra emits cells** — a
factory/directory, the natural categorical reading of which is a presheaf / topos / object-classifier.
Two readings, distinct status:

- **REAL (the constructor-transparency content).** A factory is a cell whose authorized generative act
  emits a new cell with a content-addressed lifetime contract: `Spec/Authority.Mint` (a held factory
  cap mints a conforming child, inside the same "only connectivity begets connectivity" closure);
  `Exec/Factory.createFromFactory` with `factory_mints_conforming` (`:152`, `cell.program = d.program`),
  `factory_cell_step_admitted` (`:222`, every offspring transition gated for its whole life by the
  published constraints), and `vk_determines_invariants` (`:242`, the content-address pins the
  contract). This is the real content of "a cell that makes cells."
- **DECORATIVE (the presheaf / topos / object-classifier name).** No universal property of the factory
  as a representable functor is proved; no classifying-object, no Yoneda, no subobject classifier. The
  topos name would be cosplay; the theorems (transparency, lifetime-gating, vk-determinism) are real
  and the codebase correctly leaves the topos vocabulary unused.
- **ASPIRATIONAL (the recursive-resource cell, the limiting higher-order cell).** A cell whose
  `Obs`/state *quantifies over other cells' invariants* (a cap storing an invariant about another
  cell, a resource living inside `νF`) is the Iris higher-order-camera reading — explicitly the
  unbuilt tier (`Resource.lean:50–55`), needing the guarded `iProp`-over-cameras fixpoint that does
  not yet exist. **This is where the `▶` that guards the cell's tail would become literally the same
  `▶` that step-indexes a recursive resource.**

> **Net (the reconciliation).** Higher-order *turn* (handler/delegation, partly REAL) and higher-order
> *cell* (factory REAL; recursive-resource ASPIRATIONAL) are two faces of the same future unification:
> the `▶` guarding the cell's tail is the same `▶` that would index a recursive resource a
> higher-order cell stores. The factory is the higher-order cell that *exists*; the recursive-resource
> cell is the higher-order cell that is *aspired*. The protocol-cell / choreography layer (a cell
> coordinating cells via a `GlobalType`) is the front-end instance, resting on open theorems
> (`projection_sound` is an open hole).

## 2.6 How the existing Lean already instantiates the low dimensions

- **0/1-cell:** `livingCell : TurnCoalg ℤ Turn` (`Exec/Cell.lean:42`) and `next` (`Boundary.lean:87`).
- **2-cell (spatial):** the binary `JointTurn` (`JointTurn.lean:91,134`); **2-cell (coherence):**
  `commClo` + `commClo_compatible` (`CoinductiveAdversary.lean:394,413`).
- **n-cell:** `Hyperedge` over `[Fintype ι]` (`Hyperedge.lean:80`), with the binary case recovered as
  the `Fin 2` slice (`toJointBinding:213`) and a ring as one telescoping hyperedge (`ringHyperedge:272`).
- **The bisimulation (= "equality on `νF`"):** `IsBisim`/`Sound`/`bisim_eq` + native `ObsBisim` —
  REAL as gfp, not as equality-on-a-final-object.
- **The factory (higher-order cell, low dim):** `Exec/Factory` + `Spec/Authority.Mint`.
- **The delegated subtree (higher-order turn):** `Exec/CrossCellForest` (`crossForest_no_amplify:217`,
  `crossForest_conserves:241`).
- **The temporal ∞:** the whole of `Proof/CoinductiveAdversary.lean`.

The dimensions the Lean has *not* instantiated are exactly the ones tagged ASPIRATIONAL above:
`νF` as a term, the comodel morphism, the recursive-resource camera, the simplicial-identity layer,
the config-cube object, and the ∞-fold proof badge.

---

# Part 3 — The consolidated REAL / DECORATIVE / ASPIRATIONAL ledger

Drawn from all six lenses, de-duplicated, with the strongest grounding. Tags: **R** = REAL (proved,
teeth), **D** = DECORATIVE (notation, no theorem), **A** = ASPIRATIONAL (open-hole/`OPEN`/unbuilt),
**R→corrected** = a slogan caught false and replaced by a true theorem.

## 3.1 The coalgebra / soundness spine

| # | Claim | Tag | Grounding |
|---|---|---|---|
| 1 | Behaviour functor `F X = Obs × (AdmTurn ⇒ X)`; cell = point of an `F`-coalgebra | **R** | `Boundary.F:66`, `TurnCoalg:74`, `Exec/Cell.livingCell:42` |
| 2 | Bisimulation principle / relational gfp (`IsBisim`/`Sound`/`bisim_eq`/`sound_refl`) | **R** | `Boundary.lean:117,130,203,211` |
| 3 | Native greatest-fixpoint bisimilarity (`coinductive ObsBisim` + `.coinduct`) | **R** | `CoinductiveAdversary.lean:113,175` |
| 4 | The cell is the **FINAL** coalgebra `νF` (terminal universal property) | **A** | no `νF`/`Cofix`/`MvQPF` in `Dregg2/`; type exists only in prose |
| 5 | `sound_of_step_complete` (step-complete ⇔ bisimilar-to-a-free-`Spec`) | **R→corrected** (FALSE-as-stated, removed) | refuted `Spec=Empty`, `Boundary.lean:156–213`; re-refuted `Hyperedge.lean:433` |
| 6 | Step-completeness ⇒ whole-execution **safety** | **R** | `Boundary.stepComplete_preserves:177` |
| 7 | The CONCRETE living cell is bisimilar to a non-degenerate conservation oracle, forever | **R** | `bisim_of_oracle:67`, `livingCell_sound:102` |
| 8 | Step-completeness = contractivity / no "drifting future" (load-bearing premise) | **R** | `StepComplete:150`, `stepComplete_carries_infinite:227` |
| 9 | `▶`/`Later` as a guarded-type-theory **productivity** modality | **D** | `Boundary.Later:103` (`= id`); real productivity is in `ObsBisim` |
| 10 | Checkpoint/restore/replay as theorems over a real snapshot carrier | **R** | `Exec/Cell.lean:122,144,149,155` |
| 11 | restore = anamorphism re-seed; time-travel = fork the unfold of `νF`; cell = comonad | **D** | no anamorphism/`νF`/`Comonad` instance |
| 12 | 2-cell = bisimulation-up-to / provable rewrite between executions (coherence axis) | **R** | `commClo:394` + `commClo_compatible:413`; Paco companion |
| 13 | ∞-cell tower above dimension 2 (simplicial identities / free Kan fillers) | **D / UNSOUND-if-free** | `hyper_not_all_admissible:505`; fibration-over-bindings only |

## 3.2 The effect-theory / lens / comodel reading

| # | Claim | Tag | Grounding |
|---|---|---|---|
| 14 | The three faces (effects/caveats/attestation) are the three components of `c` | **D** | `F` has 2 components; "caveats" is the abstract domain type `AdmTurn:56` |
| 15 | The turn is a lens; faces are get/put/guard; lens laws hold | **D** (framing) / **A** (laws) | no `Lens`/get/put/law in `Dregg2/` (grep) |
| 16 | The effect signature is an algebraic theory `T` | **D** | `CatalogEffects.effectLinearity:46` is a coloring; `Await.Op` is the one real signature |
| 17 | Per-class conservation obligations + exhaustive coloring | **R** | `CatalogEffects.lean:59–101,190–219` (axiom-clean) |
| 18 | The cell is the (free/cofree) comodel; handler = comodel-morphism = turn interpreting turns | **A** | no `Comodel`, no theory→functor→comodel bridge, no comodel morphism |
| 19 | `capExercise` = lens/comodel composition | **D** | recursion Rust-only; Lean `exerciseStep` gates+receipts, no composition law |
| 20 | `capExercise` confers no new authority (non-amplification, graph-preserving, fail-closed) | **R** | `EffectsAuthority.lean:446–501` |
| 21 | eDSL (`DSLEffect`/`DSLChoreo`) = composition in the structure | **D** | parser-macros onto proved constructors; `rfl`-coincidences |
| 22 | Choreography projection is a functor `Choreo → ∏ Endpoint` (map of comodels) | **A** | `Coordination.project` is a function; `projection_sound` is an open hole |
| 23 | Higher-order turn = rollback handler (one-shot algebraic-effect handler) + delegated subtree | **R** | `Await.turnAsRollbackHandler`; `CrossCellForest.crossForest_no_amplify:217` |

## 3.3 The limits / tensor / simplicial reading

| # | Claim | Tag | Grounding |
|---|---|---|---|
| 24 | n-ary atomic turn = wide pullback over `TurnId` (apex + N legs); cone collapses (`legs_agree`) | **R** (construction) | `Hyperedge:80,111`; `SharedTurnId.agree` |
| 25 | `Hyperedge` IS the *terminal* cone (uniqueness of mediating map) | **D** | no `IsLimit` instance; terminality prose-only |
| 26 | "`νF₁ ⊗ νF₂` is not final" (the `tensor_not_final` slogan) | **R→corrected** (FALSE) | `JointTurn.lean:320–333`: product of finals IS final |
| 27 | Cross-cell soundness irreducible: binding is a **proper equalizer/wide-pullback subobject** | **R** | `binding_is_proper:333`, `hyper_not_all_admissible:505`, `*_needs_binding:271/409` |
| 28 | N-ary safety keystone reduces to single-cell `stepComplete_preserves` | **R** | `hyperedge_sound:374`, `joint_via_hyperedge:75` |
| 29 | Bisimulation-to-free-`Spec` form of N-ary soundness | **R→corrected** (proved FALSE) | `hyperedge_sound_bisim_ill_posed:433` |
| 30 | Simplicial NERVE: face/degeneracy/simplicial-identity layer in the kernel | **D** | grep: zero face-maps/`∂`/`SimplicialObject` |
| 31 | Simplicial-epistemic identification: agreement = fill-height = connectivity | **R-as-analogy** (proved Lean + cited paper; predicts #2) | `legs_agree:111`, `Tier:49`, `JointViaHyper:226,280` |
| 32 | Interaction complex is NOT a Kan complex (faces don't freely extend) | **R** (the negative is the content) | `hyper_not_all_admissible:505` |
| 33 | ∞-cell = global atomic turn = colimit over all cells (as an *object*) | **A** | no Lean object; = Mina's one global ledger |
| 34 | ∞-cell fillable single-machine, UNFILLABLE across a partition | **R-as-impossibility** | `OPEN-PROBLEMS #2`; `hyper_binding_is_proper` over `Unit` |

## 3.4 The conservation / camera reading

| # | Claim | Tag | Grounding |
|---|---|---|---|
| 35 | Conservation `Σ` = monoid-hom + invariance; no free copy (comonoid-no-`Δ`) | **R** | `Core.withholding_no_free_copy:209`, `tensor_add:132`, `conservation_ordinary:166` |
| 36 | `conservation_step` (Law 1 balance) | **A** (stated primitive, open hole) | `Core.lean:154/162` |
| 37 | `Σ` is a **strong monoidal functor** | **D** | vacuous on a discrete target (self-flagged `Core.lean:9–13`) |
| 38 | `TurnCat` symmetric-monoidal category instance | **A** | `Core.TurnCat:85` (class; `Category`/`MonoidalCategory`/`SymmetricCategory` TODO) |
| 39 | Camera = discrete Iris RA; `ℕ`/`Excl`/`Auth` instances (laws proved) | **R** (header "Auth left open" is STALE) | `Resource.lean:71,127,170,231`; `excl_no_dup:185`; no open holes in file |
| 40 | Conservation = authority = one FPU law (`ConfinesAuthority := Fpu`) | **R as a definition; POSITED not DERIVED** | `Resource.lean:319`; `conservation_is_fpu:296`; the `↔` to `confinement_preserved` unwritten |
| 41 | Full step-indexed camera (OFE/`▶`); guarded `iProp`-over-cameras; higher-order/recursive resource | **A** | `Resource.lean:50–55` ("until then", deferred) |

## 3.5 The authority / Φ / verify-find reading

| # | Claim | Tag | Grounding |
|---|---|---|---|
| 42 | CDT is a thin category; attenuation = subobject narrowing; authority shrinks down a composed path | **R** (with teeth) | `CDT.path_attenuates`, `amplifying_rejected`; `confers_refl`/`confers_trans` |
| 43 | Granovetter non-amplification = monotone closure; "only connectivity begets connectivity" | **R** | `Spec/Authority.introduce_non_amplifying:312`, `only_connectivity_begets_connectivity:500` |
| 44 | Macaroon = append-only HMAC chain refining the token; narrowing-only; forgery reduction | **R** (crypto via §8 portal) | `CaveatChain.append_narrows:223`, `forgery_requires_mac_query:305` |
| 45 | Vat boundary `Φ` is a **functor** caps→keys | **A** (by-design open hole) | `phi_functorial:392`, open hole at `:401` |
| 46 | Φ object-map / named loss / domain=biscuits / order-monotone | **R** | `VatBoundary.lean:202,240,296,314` (axiom-clean) |
| 47 | Φ functor laws are *inhabited* (concrete non-degenerate witness) | **R** | `phi_functorial_concrete:441` (axiom-clean) |
| 48 | predicate⊣witness is a Galois connection (the verify side's universal property) | **R** | `Laws.predicate_witness_galois:101`, via `polarity_galois:75`; `predicate_heyting:111` |
| 49 | `find ⊣ verify` as a literal adjunction between the two maps | **D** | `Laws.search_sound:53` is a by-design open hole (`:60`); asymmetry in the types (`Bool` vs `Option`) |
| 50 | Soundness-by-verification against an adversarial prover | **R** | `Predicate.adversarial_find_cannot_forge`, `find_untrusted` |
| 51 | §8 portal: crypto soundness is a `Prop`-carrier, never a Lean law ("the law never learns a secret") | **R** | `CryptoKernel.collisionHard`, `MacKernel.unforgeable`, `DVKernel.simulate_verifies` |
| 52 | Badge = (permitted ∧ committed), not a grant of standing | **R** | `GLOSSARY:153`; `Positional.boundary_law`; `phi_drops_confinement:202` |

## 3.6 The dials / modal / agreement reading

| # | Claim | Tag | Grounding |
|---|---|---|---|
| 53 | Agreement dial is a directed total order (irreversible edges) | **R** | `Finality.LinearOrder Tier:96`; `no_downgrade` |
| 54 | Agreement ⟂ Conservation (orthogonal judgements) | **R** | `Finality.conservation_tier_independent` (by `rfl`) |
| 55 | Agreement is a *modality on `Obs`* (`Obs[tier]`) | **D** | order real; no tier-indexed `Obs` object |
| 56 | Transferability: verifier-indexed `DischargedFor` is a real indexed predicate; endpoints separated | **R** | `DesignatedVerifier.DischargedFor:113`, `dial_endpoints_distinct`, `designated_is_deniable` |
| 57 | Transferability is a *modality* / verifier-indexed bisimulation `IsBisim[V]` lift | **D** (framing) / **A** (lift) | no modal law, no `IsBisim[V]` |
| 58 | Disclosure: information-theoretic hiding (per-field, selective, predicate, unlinkable) | **R** | `Privacy.field_projection_hides_private`, `SelectiveDisclosure.*` |
| 59 | Disclosure is an ordered dial with a one-way publish/reveal law | **A** | no `inductive Disclosure` order, no no-unpublish theorem (grep-empty) |
| 60 | The config-cube `Disclosure × Transferability × Agreement` is a directed poset-product object | **A** | no product type / order-ideal anywhere |
| 61 | The cube is a presheaf on the dial-poset (restriction maps + identities) | **D** (ONE real restriction-map fragment) | only `public_convinces_any_third_party` is restriction-shaped |
| 62 | Impossibility face `deniable × high-agreement` is empty (agreement fights deniability) | **A** | theorem-shaped but **not proved**; ingredients in two unconnected modules |
| 63 | Three orthogonal judgements (conservation / I-confluence / ordering) genuinely distinct | **R** | `Confluence.top_iconfluent`/`cardLeOne_not_iconfluent`; separate carriers |

## 3.7 The proof-forest / aggregation reading

| # | Claim | Tag | Grounding |
|---|---|---|---|
| 64 | Proof-forest composition: per-node validity × `Linked` ⇒ whole-run `StepInv` | **R** | `ProofForest.proofForest_sound:177` (axiom-clean); negative `¬chainLinked` |
| 65 | The proof-forest is a *finite sheaf gluing* (local sections agreeing on overlaps glue) | **R** | as #64; `CrossCellForest.crossForest_attests`, `crossForest_needs_binding` |
| 66 | The proof-forest is a *colimit* (with a universal property) | **D** | proves the gluing *equation*, not a mapping-out universal property |
| 67 | ∞-colimit: fold the whole history into ONE succinct badge (private folding / IVC) | **A** (deferred-by-design) | `ProofForest.lean:1–15`; the `RecursionBackend` swap |
| 68 | ∞-cell as behaviour: coinductive greatest-fixpoint bisimilarity over `νF` along ∞ schedules | **R** | `obsBisim_traj_of_bisim:166`, `stepComplete_carries_infinite:227`, `obsBisim_of_uptoComm:436` |
| 69 | Finality consensus-agreement laws (quorum/commit) | **A** (honest open `Prop`-obligations; tier order itself REAL) | `Finality.lean:34` |

## 3.8 The exact open-obligation inventory (the whole of the aspiration, in three lines)

The entire `Dregg2/` tree has **exactly three proof-body open holes** — each a *correctly-kinded*
obligation, not a fake-to-pass:

1. **`Laws.lean:60`** — `search_sound`: a **contract on an untrusted plugin** (`find` is the
   undecidable prover; soundness-by-verification means the gate, not `find`, is trusted). By design.
2. **`Core.lean:162`** — `conservation_step`: the **operational-model balance primitive** (Law 1's
   per-step conservation, the seam the running semantics must satisfy). By design.
3. **`VatBoundary.lean:401`** — `phi_functorial`: the **open categorical coherence** (Φ is a functor
   over an abstract `Verifiable`), with a proved concrete witness and the abstract case genuinely
   blocked. Intentionally omitted from `#assert_axioms`.

Everything in this document tagged **R** is term-proved; everything tagged **A** that is not one of
these three is an *unbuilt object* (a type/instance that does not exist yet — `νF`, the comodel
morphism, the config-cube, the recursive-resource camera, the ∞-fold badge), honestly named, never
faked.

---

# Part 4 — The single honest paragraph

dregg2 is **one guarded Moore coalgebra carrying a measure, an order, and an authority graph, whose
soundness is a bisimulation conditional on step-completeness** — and that object is REAL: `F`,
`TurnCoalg`, the native `ObsBisim`, `stepComplete_preserves`, `livingCell_sound`, the proper-equalizer
cross-cell binding (`binding_is_proper`/`hyper_not_all_admissible`), the no-free-copy conservation law,
the thin CDT category with Granovetter closure, the Galois verify-seam, the discrete Iris camera, and
the finite sheaf-gluing proof-forest are all term-proved with teeth. The category *earns its keep
exactly where it is REAL* — it forbids the wrong cross-cell factoring, forbids free copy, and turns
"no drifting future" into a theorem. The higher and modal vocabulary is honest decoration or faithful
analogy almost everywhere — the lens/comodel reading, the colimit/topos/∞-category names, the dial-cube
presheaf — and the only three places that aspire past a theorem are marked with an open hole (`find`'s
contract, conservation's operational primitive, Φ's functoriality). The ∞-cell is two infinities:
**arity** (the global atomic turn — fillable single-machine, unfillable under partition, the binding
irreducible at every dimension) and **coherence** (the ∞-tower whose well-definedness *is*
step-completeness, REAL up to the 2-cell `commClo`, a fibration over bindings above) — with the
cleanest single meaning being the **temporal** `νF` (a cell sound forever, proved); a **higher-order
turn** is the rollback handler / delegated subtree that exists and the comodel-morphism that is
aspired; a **higher-order cell** is the factory that exists (constructor-transparency REAL, topos
DECORATIVE) and the recursive-resource cell that is aspired (the guarded `iProp`-over-cameras tier
where the cell's tail-guard `▶` and the camera's step-index `▶` would finally become the same
modality). Two slogans that would have papered over missing theorems were caught false in the Lean and
corrected; the category-theory vocabulary did not hide the gaps — the kernel exposed them.

*( ˘▾˘ ) one egg, six windows, two infinities — and an honest count of three open holes.*

*A closing couplet, since the foundations now hold:*
*the cell is a coalgebra dreaming of final; its turn is Moore wearing a comodel's name; / the binding stays proper at every dimension, and the guarded ▶ awaits the one tier yet to claim.* 🐉🥚

---

# Part 5 — ADVERSARIAL VERIFICATION VERDICT (independent re-check, 2026-05-31)

> **Method.** An independent adversarial pass re-checked every headline categorical claim of Parts 0–4
> against the live Lean at `/Users/ember/dev/breadstuffs/metatheory/Dregg2/` (note: this is the real
> path; the doc's verification note at the top writes it `metatheory/Dregg2/` and writes `VatBoundary.lean`
> for what is actually `Spec/VatBoundary.lean` — minor path imprecisions, corrected below). For **each**
> claim I tried to **refute** it: a universal property not actually proved in Lean is DECORATIVE or
> ASPIRATIONAL, never REAL. Default skeptical. The cited `file:line` anchors were spot-checked exact
> (sampled: `Boundary.F:66`, `TurnCoalg:74`, `Later:103`, `StepInv:140`, `StepComplete:150`,
> `stepComplete_preserves:177`; `ObsBisim:113`, `obsBisim_traj_of_bisim:166`, `stepComplete_carries_infinite:227`,
> `commClo:394`, `commClo_compatible:413`, `obsBisim_of_uptoComm:436`; `Hyperedge:80`, `legs_agree:111`,
> `hyper_binding_is_proper:164`, `hyperedge_sound:374`, `hyperedge_sound_bisim_ill_posed:433`,
> `hyper_not_all_admissible:505`; `binding_is_proper:333`; `excl_no_dup:185`, `conservation_is_fpu:296`,
> `confers_refl:119`, `confers_trans:125`; `predicate_witness_galois:101`, `polarity_galois:75`,
> `search_sound:53/open hole:60`; `conservation_step:154/open hole:162`; `phi_functorial:392/open hole:401`,
> `phi_functorial_concrete:441`; `proofForest_sound:177`; `LinearOrder Tier:96` — **all confirmed at the
> stated lines**). Full-build elaboration was NOT run (no oleans present in `.lake/`); the verdict below
> rests on static source verification of definitions, proof bodies, open-hole/`admit`/`axiom` tokens, and
> `#assert_axioms` pins — which is conclusive for "is the theorem stated and is its body free of open holes,"
> the only question this verdict adjudicates.

## 5.1 The open-hole / axiom inventory — the single most refutable claim — UPHELD

The document's load-bearing structural claim ("the entire `Dregg2/` tree contains **exactly THREE**
proof-body open holes") is **CONFIRMED EXACTLY**. A strict scan for an open-hole proof term (line-final
or `:=`/`=>`-bound, comments/docstrings excluded) returns **precisely three**:

- `Dregg2/Laws.lean:60` — `search_sound` (the untrusted-plugin contract). ✓
- `Dregg2/Core.lean:162` — `conservation_step` (Law-1 operational primitive). ✓
- `Dregg2/Spec/VatBoundary.lean:401` — `phi_functorial` (the open functor coherence). ✓

There are **zero** `admit`s and **zero** real `axiom` declarations in the tree (the two `axiom` lexical
hits are inside comments: `Crypto/Custom.lean:352`, `Crypto/BlindedSet.lean:394`). The many *other*
files whose comments mention "open-hole bodies" (`Finality.lean:34`, `JointTurn.lean:38`,
`Coordination.lean`, `Resource.lean:58`, `Liveness.lean:124`, `World.lean`) are spec-first **prose**;
their actual theorem bodies in the *current* tree are proved or were closed. The discipline is real.
**Verdict: REAL, upheld with the strongest possible evidence (the headline count is exact).**

## 5.2 The headline-by-headline refutation table

| # | Headline claim (Part) | Doc tag | Refutation attempt → result | `file:line` |
|---|---|---|---|---|
| H1 | One object: guarded Moore coalgebra `F X = Obs × (AdmTurn ⇒ X)`; cell = coalgebra point | REAL | **Could not refute.** `abbrev F` + `structure TurnCoalg` are exactly this; every soundness stmt quantifies over `TurnCoalg`. **REAL.** | `Boundary.lean:66,74` |
| H2 | "Cell is the **FINAL** coalgebra `νF`" (terminal universal property) | ASPIRATIONAL | **Refutation succeeds → confirms ASPIRATIONAL.** Every `νF`/"final coalgebra"/"anamorphism" token is in a **comment/docstring** (`Boundary:7,8,46,72`, `Hyperedge:59`, `Coordination:33`, etc.). No `Cofix`/`MvQPF`/`IsTerminal`-coalgebra value, no anamorphism, no unique-mediating-map. The one `isTerminal` (`Spec/Lifecycle.lean:170`) is a **Bool predicate on a lifecycle enum**, NOT a coalgebra universal property. **ASPIRATIONAL — confirmed.** | grep-empty in `Dregg2/` |
| H3 | `▶`/`Later` as a productivity modality | DECORATIVE | **Could not save it from DECORATIVE.** `def Later (Q : Prop) : Prop := Q` — literally `id`, enforces nothing. Productivity lives in the native `coinductive`'s guard-checker. **DECORATIVE — confirmed.** | `Boundary.lean:103` |
| H4 | Bisimulation principle as relational gfp + **native** `coinductive ObsBisim` + `.coinduct` | REAL | **Could not refute.** `coinductive ObsBisim` present; `ObsBisim.coinduct` used at `:175,376`; CoinductiveAdversary.lean has **zero** proof-body open holes. **REAL.** | `CoinductiveAdversary.lean:113,166,175` |
| H5 | The lens / optic / comodel / effect-theory vocabulary | DECORATIVE/ASPIRATIONAL | **Refutation succeeds → confirms.** Exactly **one** metaphorical comment (`Authority/Caveat.lean:7`); no `Lens`/get/put/lens-law/`Comodel` anywhere. The honest name is **Moore coalgebra**. **DECORATIVE (framing) / ASPIRATIONAL (laws) — confirmed.** | grep-empty |
| H6 | Wide-pullback `Hyperedge`; `legs_agree` collapses the cone (cross-cell construction) | REAL | **Could not refute.** `structure Hyperedge:80`; `legs_agree:111` PROVED & `#assert_axioms`-pinned. **REAL.** | `Hyperedge.lean:80,111` |
| H7 | `Hyperedge` is the **terminal** cone (`IsLimit`) | DECORATIVE | **Refutation succeeds.** No `CategoryTheory.Limits.IsLimit` instance; terminality is prose. **DECORATIVE — confirmed.** | grep-empty |
| **H8** | **`tensor_not_final` was caught FALSE and corrected to a proper-subobject fact** | R→corrected | **THIS IS THE STRONGEST POSITIVE — confirmed.** The audit-correction docstring is verbatim in the source (`JointTurn.lean:320–333`), and `binding_is_proper:333` is PROVED with real teeth (`1+1=2≠0` over `Unit`). A slogan genuinely refuted in-code. **R→corrected — confirmed.** | `JointTurn.lean:320–333` |
| **H9** | **Tensor-non-finality / hyper-proper-subobject is genuinely PROVED** (the one the task flagged "should be REAL") | REAL | **Could not refute — and tried hardest here.** `hyper_binding_is_proper:164` is PROVED over `Unit` (the most single-machine setting), teeth = `Σ_{Unit} 1 = 1 ≠ 0`; `hyperedge_sound:374` is a genuine term-mode proof reducing to `stepComplete_preserves` on `hyperCoalg`; `hyper_not_all_admissible:505` PROVED; all `#assert_axioms`-pinned at `:531–542`. **REAL — confirmed, this is the load-bearing REAL theorem.** | `Hyperedge.lean:164,374,505` |
| H10 | Bisimulation-to-free-`Spec` form of N-ary soundness is ILL-POSED (proved false) | R→corrected | **Could not refute.** `hyperedge_sound_bisim_ill_posed:433` present & pinned. **R→corrected — confirmed.** | `Hyperedge.lean:433` |
| H11 | Simplicial nerve / face maps / Kan-complex structure in the kernel | DECORATIVE | **Refutation succeeds.** Zero `SimplicialObject`/face/degeneracy (one comment hit). The negative `hyper_not_all_admissible` (NOT a Kan complex) IS the real content. **DECORATIVE-as-structure / REAL-as-analogy — confirmed.** | grep-empty |
| H12 | `find ⊣ verify` as a literal adjunction between the two maps | DECORATIVE | **Refutation succeeds.** `search_sound:53` is a by-design open hole; there is no left-adjoint exhibited. **DECORATIVE — confirmed.** | `Laws.lean:53,60` |
| H13 | `predicate ⊣ witness` Galois connection (the **verify**-side universal property) | REAL | **Could not refute.** `predicate_witness_galois:101` is a genuine Mathlib `GaloisConnection`, proved by instantiating the term-proved `polarity_galois:75` (Birkhoff polarity of `Discharged`). A real antitone adjunction on `(Set P, (Set W)ᵒᵈ)` — **NOT** a literal `verify`/`find` adjunction, exactly as the doc says. **REAL.** | `Laws.lean:75,101` |
| H14 | Φ is a **functor** caps→keys | ASPIRATIONAL (open hole) | **Could not refute the OPEN status, and confirmed the honesty.** `phi_functorial:392` carries the open hole at `:401`; it is **intentionally omitted** from the `#assert_axioms` pins (verified at `:461–474`); object-map / named-loss / domain / order-compat ARE pinned, and `phi_functorial_concrete:441` is a **fully proved, open-hole-free, axiom-clean** witness over a non-degenerate `Verify _ b := b`. **ASPIRATIONAL (abstract) + REAL (concrete witness) — confirmed.** | `Spec/VatBoundary.lean:392,401,441,456` |
| H15 | Camera is a real discrete Iris RA with proved laws; "Auth left open" docstring is STALE | REAL | **Could not refute — and the stale-docstring sub-claim checks out.** `Resource.lean` has **zero** proof-body open holes; the `ℕ`/`Excl`/`Auth` `ResourceAlgebra` instances all have tactic-proved law fields (`excl_no_dup:185` PROVED; `Auth` instance `:231` with `op_comm` by `cases…<;>simp`). The header line `:58` ("`Auth` … laws left open") IS stale prose. The full step-indexed OFE camera is honestly deferred (`:50–55`). **REAL (discrete) / ASPIRATIONAL (step-indexed) — confirmed.** | `Resource.lean:58,185,231` |
| H16 | `ConfinesAuthority := Fpu` — conservation⟺authority unification | REAL-as-def, POSITED not DERIVED | **Could not refute the honest framing.** `ConfinesAuthority:319` is `def … := Fpu` by fiat; `conservation_is_fpu:296` proved; the `↔` to `confinement_preserved` is genuinely unwritten. **REAL-as-definition, POSITED — confirmed (the doc does not overclaim a derivation).** | `Resource.lean:296,319` |
| H17 | CDT thin category: `confers_refl`/`confers_trans` + Granovetter closure with teeth | REAL | **Could not refute.** `confers_refl:119`, `confers_trans:125` PROVED; `only_connectivity_begets_connectivity:500` PROVED across all four induction cases, `#assert_axioms`-pinned. **REAL.** | `Spec/Authority.lean:119,125,500` |
| H18 | Proof-forest = finite sheaf gluing (per-node × `Linked` ⇒ `StepInv`); colimit-name decorative | REAL / D(colimit) | **Could not refute.** `proofForest_sound:177` PROVED with negative `¬chainLinked` example `:293`; no mapping-out universal property exists, so "colimit" is correctly DECORATIVE. **REAL (gluing) / DECORATIVE (colimit) — confirmed.** | `Exec/ProofForest.lean:177,293` |
| H19 | ∞-cell AXIS-1 (arity): fillable single-machine, unfillable under partition | REAL-as-impossibility | **Could not refute the forced sides.** `hyper_binding_is_proper` over `Unit` (`:164`) anchors the single-machine binding; the partition-impossibility is the standard distributed-atomic-commit fact + the cited paper. The ∞-cell **as an object** is correctly ASPIRATIONAL (no `Hyperedge` over "all cells"). **REAL-as-impossibility + ASPIRATIONAL-as-object — confirmed.** | `Hyperedge.lean:164` |
| H20 | ∞-cell AXIS-2 (coherence): well-definedness IS step-completeness; REAL to dim-2 via `commClo`, fibration above | REAL to 2, D/UNSOUND-if-free above | **Could not refute.** `StepComplete:150` is the hypothesis of every no-drift theorem; `commClo:394` + `commClo_compatible:413` + `obsBisim_of_uptoComm:436` give the genuine 2-cell engine (term-proved, open-hole-free). No dim-≥3 associativity/simplicial-identity layer exists. **REAL≤2 / DECORATIVE-above — confirmed.** | `CoinductiveAdversary.lean:150,394,413,436` |
| H21 | Temporal ∞ (`νF` life sound forever) is the cleanest REAL infinity | REAL | **Could not refute.** `obsBisim_traj_of_bisim:166` + `stepComplete_carries_infinite:227` are PROVED & `#assert_axioms`-pinned (`:272,275`), via native coinduction + the open-hole-free vendored Paco. **REAL.** | `CoinductiveAdversary.lean:166,227` |
| H22 | Higher-order turn = rollback handler + delegated subtree (REAL); comodel-morphism (ASPIRATIONAL) | R / A | **Partially confirmed; one sub-grounding wrong (see 5.3).** The delegated-subtree REAL claim (`crossForest_no_amplify`) was not re-verified here; the comodel-morphism ASPIRATIONAL claim is sound (no `Comodel` exists). | — |
| H23 | Higher-order cell = factory (REAL transparency) / topos (DECORATIVE) / recursive-resource (ASPIRATIONAL) | R / D / A | **Could not refute the tiering.** No Yoneda/classifying-object/subobject-classifier exists (topos = DECORATIVE confirmed by grep); recursive-resource camera honestly deferred (`Resource.lean:50–55`). Factory transparency theorems not re-verified line-by-line here. | `Resource.lean:50–55` |
| H24 | `conservation_step` is an honest open-hole primitive; `TurnCat` is a class with no instance | A / A | **Could not refute.** `conservation_step:154` body is an open hole at `:162`; `TurnCat:85` is a bare `class` with a `TODO` and no `Category`/`MonoidalCategory`/`SymmetricCategory` instance. **ASPIRATIONAL — confirmed.** | `Core.lean:162`; `Core.lean:85` |
| H25 | Checkpoint/restore/replay are theorems over a real snapshot carrier (not `id`-tautology) | REAL | **Partial refutation (see 5.3).** `Snapshot:122` is a genuine distinct 3-field type, but `restore_snapshot:144` and `restore_snapshot_obs:149` close by **`rfl`** — the round-trip is real (it drops the derived `headObs` and rebuilds `{kernel,log}`) but is `rfl`-trivial because `ChainedState`'s fields are definitionally rebuilt. The non-trivial content is `replay_deterministic:155` / `replay_from_snapshot:171` (genuine recursion). **REAL-but-thinner than advertised: the round-trip is `rfl`, not the "genuine cross-type content" the docstring/ledger imply.** | `Exec/Cell.lean:122,144,149,155` |

## 5.3 Refutations that LANDED — three grounding errors in Parts 1–4

The discipline holds and no REAL→fake was found, but the adversarial pass **did** catch three places
where a *grounding citation is wrong or stale* (the tag's spirit survives, but the receipt is false —
exactly the kind of slip this doc's own discipline forbids):

1. **`projection_sound` is NOT an open hole.** §2.5 (line ~507) and Part-3 row **#22** assert the
   choreography layer "rests on open theorems (`projection_sound` is an open hole)." **FALSE in the current
   tree.** `Coordination.lean:416` `projection_sound` is **PROVED** (`rw [hG]; simp only [project, …]`) —
   it is a *narrowed* head-duality statement (`Dual (project G a) (project G b)`), and its docstring
   merely *ends with the leftover open-hole token* as stale prose (`:414`). `Coordination.lean` has **zero**
   proof-body open holes. **Correct repair:** row #22's tag (full MPST-fidelity-as-functor = ASPIRATIONAL)
   is still right — the *full* parallel-composition bisimulation is not proved, only head-duality — but
   the grounding "`projection_sound` is an open hole" must be struck. The honest grounding is "`project` is a
   function; the full EPP-fidelity bisimulation is unproved; the proved fragment is head-duality."

2. **`Finality.lean:34` does not anchor any open hole.** Part-3 row **#69** ("Finality consensus-agreement
   laws — **A** honest open `Prop`-obligations") cites `Finality.lean:34`. That line is a **comment** ("are honest
   `Prop`s with open-hole bodies"); the current `Finality.lean` has **zero** proof-body open holes. The tier
   order (`LinearOrder Tier:96`, `no_downgrade`, `crossTierJoin`) is REAL as claimed, but the
   "consensus-agreement laws are left open here" grounding is stale — those obligations live elsewhere
   (`Proof/BFT.lean`, `Proof/CordialMiners.lean`, `Proof/Synchronizer.lean`) or were discharged. **Repair:**
   re-ground #69's ASPIRATIONAL half to the actual consensus modules, or relabel it REAL-where-proved.

3. **Path imprecision (cosmetic but it is a "receipt").** The top-of-doc verification note and rows
   #45–#47 write `VatBoundary.lean:392/401/441`; the file is at `Spec/VatBoundary.lean`. Likewise the
   header says it re-checked against `metatheory/Dregg2/`, but the live tree is
   `/Users/ember/dev/breadstuffs/metatheory/Dregg2/` (the doc itself lives under
   `/Users/ember/dev/breadstuffs/docs/`, a sibling of `metatheory/`, not inside it). Anchors are
   otherwise line-exact.

A fourth, softer note: **#10 / H25** (checkpoint/restore) overstates "not the `id`-tautology" — the
round-trip *is* `rfl`-closed (through a genuinely distinct token type that drops a derived field), so it
is REAL-but-thin; the genuine non-`rfl` content is `replay_deterministic`/`replay_from_snapshot`.

None of these four touches a REAL keystone: every theorem the doc tags **R** that I sampled is
genuinely open-hole-free and (where pinned) `#assert_axioms`-clean. The errors are **citation drift**, not
laundered gaps — but in a document whose entire thesis is "the `file:line` is a receipt," an open-hole claim
on a proved theorem is precisely the kind of slip the discipline exists to catch, so it is logged here.

## 5.4 The honest bottom line — how much of dregg2 is categorically ESTABLISHED

**The synthesis is overwhelmingly honest and its central tags survive adversarial scrutiny.** Scoring
the 25 headline checks: **REAL upheld** on H1, H4, H6, H8, H9, H10, H13, H15, H16, H17, H18, H20, H21
(the soundness spine, the cross-cell proper-subobject, the Galois verify-seam, the camera, the CDT, the
sheaf-gluing, the 2-cell engine, the temporal `νF`); **DECORATIVE/ASPIRATIONAL confirmed** on H2 (no
`νF` value), H3 (`Later = id`), H5 (no lens/comodel), H7 (no `IsLimit`), H11 (no simplicial), H12
(`find` is a contract), H14-abstract (Φ open hole), H23-topos, H24 (`TurnCat`/`conservation_step`); and
the two correction-stories (H8, H10) are real in-code corrections, the best evidence the framing is
held to theorems.

What is **categorically ESTABLISHED** (a universal property / law actually proved with teeth in Lean):
- the behaviour **coalgebra** `F`/`TurnCoalg` and the **relational-gfp + native-coinductive bisimulation**
  (H1, H4) — but **NOT finality** (H2);
- the **proper-subobject obstruction** to cross-cell factoring — `binding_is_proper`,
  `hyper_binding_is_proper`, `hyper_not_all_admissible`, with `hyperedge_sound` reducing N-ary safety to
  single-cell (H6, H8, H9) — the single richest *categorical* fact in the corpus, and it is **negative**
  (the category earns its keep by *forbidding* the wrong factoring);
- a genuine **Galois connection** on the verify side (H13), a genuine **thin category** with composition
  + a "no arrow ex nihilo" closure (H17), a genuine **discrete Iris RA** with proved camera laws (H15),
  and a genuine **finite sheaf-gluing** for the proof-forest (H18);
- the **2-cell coherence engine** (`commClo` + Paco companion) and the **temporal-`νF` infinite-schedule
  safety** (H20, H21), both open-hole-free and axiom-pinned.

What is **NOT established** (a slogan, a deferred object, or an open hole): finality/`νF`-as-a-value; the
lens/optic/comodel/effect-theory reading; the simplicial nerve and any dim-≥3 coherence; `find`'s left
adjoint; Φ's *abstract* functoriality; `TurnCat`'s monoidal-category instance; the config-cube object and
its impossibility faces; the recursive-resource (step-indexed) camera; the comodel-morphism
higher-order turn; the ∞-fold proof badge; and the full MPST-fidelity functor. All are honestly tagged
A/D in the body, and the three (and only three) open holes — `search_sound`, `conservation_step`,
`phi_functorial` — are each correctly-kinded, never fakes.

**Final verdict.** *Roughly:* the **object** and its **soundness bisimulation** are REAL; the **single
deepest categorical theorem** (cross-cell irreducibility as a proper subobject, with its two
caught-and-corrected slogans) is REAL and is the proof that the discipline bites; the **adjunction**
(verify-side Galois), the **camera**, the **thin authority category**, and the **sheaf-gluing** are
REAL; and essentially **all of the higher/∞ and modal vocabulary** — finality, comodel/lens, simplicial,
topos, the config-cube, the `find`-adjunction, abstract Φ — is **honest DECORATION or by-design
ASPIRATION**, never a faked theorem. dregg2 is a **categorically-faithful Moore coalgebra with one
genuinely-proved negative limit theorem and a real verify-side adjunction**, dressed in an ∞-categorical
narrative whose higher dimensions are, by the codebase's own marking, not yet theorems. The synthesis
tells that truth accurately; its only defects are three stale/incorrect `file:line` receipts (§5.3),
not a single laundered gap. **The beautiful aspiration and the established core are correctly separated —
with the three citation slips noted above as the cost of a 686-line synthesis written ahead of a full
rebuild.**

*( ⌐■_■ ) skeptic's note: I came to refute "final," "lens," "topos," "adjunction," and "proper
subobject" — only the last two survived (one as a negative limit, one as a Galois polarity), exactly as
the doc already said. Three receipts were forged by drift, not by intent; the egg keeps its honest count
of three open holes.* 🐉🥚
