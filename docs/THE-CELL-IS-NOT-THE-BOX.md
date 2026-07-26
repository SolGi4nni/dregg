# The Cell Is Not the Box

*A companion to a community article that got the picture right, on what the picture is a
picture of.*

A recent community writeup on dregg said, of cells: **"The cell IS the box."** It drew the
house — kitchen, bedroom, garage, a safe inside the garage — and it explained turns and
receipts through the hundred-dollar bill you can no longer account for. This is a good
picture. It is the picture we would draw first too. This article is about what the picture
is a picture *of*, because the truth underneath it is stranger and, we think, better: **a
cell is not a datastructure. It is the fixed point of the demands placed on it.** The box
is not the thing; the box is the *shadow* the thing casts when you interrogate it.

dregg's metatheory makes this precise in two independent, machine-checked ways — one for a
cell's *dynamics* (what it does), one for its *statics* (what it admits). Both are
fixpoints. Neither is a datastructure. Every claim below names the actual Lean theorem it
stands on, in this repository, checked down to three standard axioms.

---

## 1. The box picture, and what it quietly assumes

"The cell is the box" suggests: somewhere there is a struct — fields, owner, history,
rules — and the system is what happens when code manipulates that struct. And indeed
there is a struct (`cell/src/cell.rs`: sixteen field slots, a signed balance, a
capability tree, a program, eight kernel-owned side-table roots). If you stopped reading
the repository there, you would conclude that dregg is a particularly careful database.

But the struct is version nine. The wire format of a turn is version three; each bump
closed a named attack (v2→v3 closed a proof-swap). The kernel's verb set is *eight* verbs
by one theorem and *three* by another — and both are true, because
`verb_minimality_is_ontology_relative` proves that which presentation is "minimal" depends
on the ontology you fix first. The datastructure keeps changing shape, and the system
keeps being the same system. So the datastructure cannot be what the system *is*. Something
else is conserved through the re-shapings. Two theorems say what.

## 2. First fixpoint: what a cell does (the final coalgebra)

Fix the two things an outsider actually has: the **experiments** you may run against a
cell (admissible turns, `Adm`) and the **observations** it yields (`Obs`). A cell, seen
from outside, is then a state of a *coalgebra* for the functor

```
F X = Obs × (Adm → X)
```

— "an observation now, and for each experiment, a next state." This is
`Metatheory.Fobj` (`metatheory/Metatheory/Categorical.lean:459`), definitionally identical to the
kernel's own `Dregg2.Boundary.F`. A coalgebra map `V → F V` is exactly a transition
structure; the repository calls the structure `Cell` (`Categorical.lean:475`), which is
not a pun.

Now the classical move, and dregg actually performs it rather than gesturing: there is a
**final** coalgebra `νF` — the greatest fixpoint of `F` — and its carrier is proven to be

```
νF.V  =  List Adm → Obs
```

(`metatheory/Metatheory/Open/FinalCoalgebra.lean:74`). Read that carrier. An element of the final
coalgebra is *literally a function from finite experiment-words to observations*. It has
no fields. It has no owner slot. It **is** "how you respond to every finite
interrogation," and nothing else. Finality — that every coalgebra admits a *unique*
behaviour-preserving map into `νF` — is proven constructively (`nuF_isFinal`,
`FinalCoalgebra.lean:162`; uniqueness by induction on the experiment word), and the real
kernel cell is welded in: `Boundary.anaInto` unfolds an actual `TurnCoalg` state into
`νF`, and `no_drift_into_nuF` (`FinalCoalgebra.lean:227`) proves **two observers who each
compute a cell's behaviour cannot disagree**. The unfold is canonical
(`unfold_is_canonical`).

Note the precise shape of the claim, because it is the philosophical crux. The theorem is
*not* "a cell is an element of `νF`." The cell — the struct, version nine — is a state of
some particular coalgebra, one implementation among many. The theorem is that it has
exactly one shadow in `νF`, and that shadow is its *identity*: any two states with the
same shadow are indistinguishable by every experiment you will ever be permitted to run.
The equality that matters is bisimilarity, and the repository takes this seriously enough
to run it against an adversary: `xcell_obsStream_eq`
(`metatheory/Metatheory/Open/CrossCellBisim.lean:261`) proves that two extensionally-equal ledgers
produce identical observation streams under *any* adversarial interleaving, along the
whole unbounded trajectory. The struct is replaceable. The unfold is not.

So when the community article says a cell has "a stable identity, proven rather than
assumed" — this is the mathematics of that sentence. Identity is not a field in the box.
Identity is the unique map into the greatest fixpoint of the observation functor. The box
can be re-versioned forever; the map is pinned by what tests can see.

## 3. Second fixpoint: what a cell admits (biorthogonality)

The dynamics half says a cell *is* its responses. The statics half is sharper: even the
**types** in dregg — the guard classes that decide which turns a cell admits — are not
written down as sets. They are *carved* as fixed points of a closure operator, in exactly
Girard's sense.

The construction (`Dregg2/Calculus/Biorthogonality.lean`): let turns be "programs" and
guard atoms be "tests" (refutations). For a set of turns `S`, let `S^⊥` be the tests all
of `S` survives, and for a set of tests `X`, let `X^⊥` be the turns surviving all of `X`.
A **behaviour** is a set that is its own double-orthogonal:

```
IsBehaviour S  :=  S^⊥⊥ = S
```

— i.e. a fixed point of the biorthogonal closure, equivalently (proven,
`isBehaviour_iff_coOrth`) *any* set of the form `X^⊥`: something whose entire content is
"what passes these tests." Then:

- **Every deployed guard class is a behaviour.** `guard_class_is_biorthogonally_closed`
  (`Biorthogonality.lean:360`): `Adm(g) = Adm(g)^⊥⊥`. The admission set of a guard is not
  assembled from a datastructure; it is the closure of its own refutation set.
- **The deployed gate is not *like* orthogonality — it is orthogonality.**
  `caveatsAdmit_is_orthogonality` (`:496`) is an `Iff.rfl`: the executor's fail-closed
  slot check and membership-in-the-orthogonal are *the same function*, definitionally. No
  translation, no simulation argument. The production gate is the Girard construction,
  running.
- **A turn cannot be individuated more finely than its tests can see.**
  `singleton_not_behaviour` (`:433`): the singleton of one turn is *not* a behaviour —
  its closure strictly grows, absorbing every turn the test family cannot tell apart. Use
  determines grain. There is no fact of the matter about a turn below the resolution of
  the experiments the system fields.
- **Attenuation is refutation-growth.** `attenuation_is_refutation_growth` (`:611`):
  adding caveats to a capability grows the test set and *shrinks* the behaviour — the
  capability-security "attenuate, never amplify" law is the antitonicity of `(-)^⊥`.

And the flagship, because one law refuses to be carved pointwise: **conservation**. No
per-turn ("rectangular") family of tests can carve out the conserving pairs of moves —
proven in full generality (`conservation_not_behaviour_rectangular`,
`BiorthTensor.lean:207`). Field the *composite* observable Σδ as a test, and conservation
becomes exactly the biorthogonal closure of matched-delta tensors
(`linearity_recovered_from_orthogonality`, `:397`). This is linear logic's ⊗ recovered
from use, not imposed: the resource law lives at the correlated observable or nowhere.
The same triad closes for write-once monotonicity (needs the step observable) and for
distributed knowledge (needs the pooled-reconstruction challenge — a federation can know
a secret no member knows, `d_without_k`), and `correlation_classifies_the_family`
(`BiorthRelational.lean:999`) packages the moral: **what a guard family can be is
classified by which correlations its tests may observe.** Even the logic's connectives
are use-shaped.

So a cell is pinned between two fixpoints. Its behaviour is the unique unfold into the
*greatest fixpoint of a functor*; its interface is a *fixed point of a closure operator*
over tests. Coinduction on one side, orthogonality on the other, and the struct in the
middle is just the current coordinate chart.

## 4. Is the turn necessary? No — and that is a theorem, not a confession

Here is the part we find genuinely philosophically honest to say out loud: **the turn, as
a datastructure, is a little arbitrary.** The formal system knows this about itself.

- The verb roster is minimal *relative to an ontology*
  (`verb_minimality_is_ontology_relative`): under the substance-discipline ontology, eight
  verbs, each earning its `(substance, polarity)` cell; under the universal-map ontology,
  three shapes (`create · gwrite · move`), with five verbs dissolving into a guarded write.
  Both presentations are theorems. Neither is *the* turn.
- The calculus presentation (`Dregg2/Calculus/DreggCalculus.lean`) is deliberately thin:
  its reduction relation is *definitionally* the executor's gated step
  (`reduces_iff_step` is an `Iff.rfl`). The calculus does not generate the semantics; it
  reads the semantics off. Syntax here is honest bookkeeping, not a source of truth.
- The wire and commitment formats are versioned contingencies (`dregg-turn-v3`,
  commitment context v9), each bump preserving the laws while re-shaping the bytes.

What is *not* arbitrary — what survives every re-presentation — is the constraint set:

1. **Σδ = 0, exactly, on every reachable state** (`reachable_total_zero`) — value moves,
   never duplicates or vanishes;
2. **granted ≤ held, with teeth** (`attenuation_is_scope_restriction`) — authority only
   narrows as it flows;
3. **one receipt row per committed step** (`reduces_is_attested`) — every reduction leaves
   evidence;
4. **fail-closed** (`reduces_fail_closed`) — no reduction past a refused guard, no escape
   hatch.

The turn is whatever object satisfies these under composition. The datastructure you
serialize is a *solution* to the constraints, one of several the repository itself has
shipped, and the theorems quantify over the constraints, not the bytes. In the sense a
mathematician means, the turn is not necessary; the *laws* are, and the turn is their
current witness. (The community article's `$100` story is clause 3 wearing street
clothes: the receipt is not a feature added to the turn — a turn is *defined* as the kind
of step that cannot occur without leaving one.)

## 5. Not owned by a chain

The box picture invites a final misreading: that the boxes sit *on* something — a chain
that owns them. The architecture is the reverse, and it is the reverse in the
authorization path, not just in marketing.

- **Authority is witness-production at the cell, at exercise time.** The gate on a turn is
  one fail-closed conjunction (`gateOK`, `Dregg2/Exec/FullForestAuth.lean:486`): the
  credential verifies, the granted authority is within the held (verified in Lean), the
  caveats discharge, the credential's nullifier is unrevoked. Nothing in that conjunction
  consults a global ledger. You hold a capability iff you can *produce* its witness.
- **Sovereign is the default mode.** For a sovereign cell the federation stores a 32-byte
  commitment and nothing else; a turn touching it carries the cell's own signed transition
  witness. The receipt chain rooted at each turn *is* the persistence layer — in the
  kernel's own words, "the database is the cache; the receipt chain is the truth."
- **A cell can live on no machine at all.** The private-offline-cells construction
  (`metatheory/docs/PRIVATE-OFFLINE-CELLS.md`; keystone
  `joint_turn_sound_with_private_legs`) has a party maintain a cell entirely offline,
  never published in cleartext — not to the counterparties, not to any chain — while still
  participating in atomic multi-cell turns by commitment and proof alone.
- **Whether a cell needs consensus is a theorem about the cell, not about a chain.**
  `modality_price_is_tier` (`DreggCalculus.lean:299`): a guard modality runs
  coordination-free *iff* its invariant is I-confluent — grow-only guards are
  partition-tolerant and need no ordering ever; a ceiling guard (`balance ≥ 0`) provably
  *forces* ordering, with a constructive clashing-pair witness telling the author why.
  Consensus is a *priced service the cell's own invariants may or may not require* —
  hired, not inherited.
- **Settlement witnesses; it does not author.** What an external verifier — an L1
  contract, a light client — is entitled to conclude from an accepted proof is: *there
  exists a genuine kernel transition, whose authority was live at the settlement tip*
  (`lightclient_unfoolable_circuit_sound` composed with `settlement_soundness`, under the
  named cryptographic floors). The chain checks a statement *about* the cell's history. It
  never gates an append. Ownership — the ability to extend the log — never leaves the
  capability holders.

The house drawing is right that the safe in the garage has its own owner, its own
history, its own rules, unaffected by the garage. The mechanism under the drawing is that
"the garage" was never a container in the first place. Containment is an *authority
relationship* — iterated attenuation, proven non-amplifying down arbitrarily long reshare
chains (`reshareN_attenuates`) — and authority relationships do not need the related
things to be anywhere in particular.

## 6. What the box really is

Put the two fixpoints back together.

A cell's *identity* is its unique unfold into the final coalgebra: a function from
experiments to observations, nothing else surviving. A cell's *interface* is a
biorthogonally closed set: exactly what its refutations fail to refute, nothing else
admitted. A *turn* is one act of surviving a refutation set, obligated by construction to
leave a receipt. A *receipt chain* is the only sense in which the past exists. And the
datastructure — the box — is the current, versioned, replaceable coordinate chart on all
of this: real, load-bearing, and not the point.

The community article said the cell is the box. We'd sharpen it to this: **the box is
where the tests ran out.** Every wall of it is the boundary of some refutation family;
move the tests and the walls move; and the theorems above are the guarantee that what's
*inside* — the behaviour, the conserved value, the narrowing authority, the attested
history — holds still while the walls are redrawn.

That's not a datastructure. That's a discipline. The struct is just where it currently
sleeps.

---

### Resolution ledger

At dregg we describe things at their current resolution, including here. Finality of
`νF` is proven constructively for the Moore-shaped functor over a hand-rolled coalgebra
category (the pinned mathlib slice lacks endofunctor algebras); the kernel weld is the
canonical-unfold theorem, not an identification of the struct's carrier with `νF`. The
calculus file's `Reduces` presents the `gwrite` shape definitionally and points
`create`/`move` at their existing executor steps. The guarded-step bisimulation's `Later`
is presently a Prop-level placeholder for the ▷ modality, labeled as such in-tree. The
contended (non-disjoint) cross-cell case is proven *impossible* to make
schedule-agnostically confluent — that boundary is where consensus genuinely begins, and
it is stated, not smoothed. The circuit-facing results stand on three named cryptographic
floors (`StarkSound`, `Poseidon2SpongeCR`, `ClosedWitness`). Everything else named above
is `#assert_axioms`-clean against `{propext, Classical.choice, Quot.sound}`.
