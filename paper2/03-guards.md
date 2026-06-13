# 3 · The guard algebra

## 3.1 One Pred, four polarities

Everything that constrains a turn is one algebra of decidable predicates over
the proposed step:

```
Pred = curated atoms ⊕ all/any/not ⊕ witnessed(vk) ⊕ thirdParty(discharge)
```

appearing at four polarities that are four separate mechanisms in most
systems:

* a **caveat** — imposed on *delegated* power;
* a **program constraint** — maintained on *owned* state;
* a **precondition** — required of a *turn*;
* an **intent demand** — wanted of the *world* (the typed hole a fulfillment
  discharges).

A predicate is either first-party (decidable now against the old/new state)
or witnessed (`witnessed(vk)`: a registered verifier discharges it — a
third-party discharge, a range proof, an arbitrary proof-carrying claim).
The same `Pred` the executor evaluates is compiled to circuit obligations:
an installable guard and a provable property are one mechanism.

## 3.2 The grammar and its closures

The curated atoms are small decidable shapes over a cell's slots (equality,
bounds, write-once, immutability, monotone and strictly-monotone updates,
deltas, sums, allowed-transition automata, membership, prefix, …; the
machine-readable roster is the generated predicate catalog). Two closures
keep the grammar from ossifying into axis-aligned special cases:

* **Relational closure** (`Authority/RelationalClosure.lean`): any affine
  relation over the post-state — `head ≤ tail + capacity`,
  `Σ slots = const` — is the same `Pred` object (`RelPred`, with
  `ofFieldLteOther_eq` recovering the single-slot atoms as instances). No
  new atom per shape; the guard language is the internal predicate logic of
  the state object, bounded by decidability and circuit-expressibility.
* **Quantified closure** (`Authority/QuantifiedPredicate.lean`): bounded
  ∀/∃ over slot ranges compile to the relational closure with a proven
  constraint budget (`compile_sound`, `andFold_budget`, `orFold_budget`) —
  quantifiers cost what they cost, and the cost is a theorem.

## 3.3 The coordination dial

Guards carry a coordination price, and the system computes it
(`Authority/ConfluenceClassifier.lean`). Two concurrent turns merge without
coordination exactly when their guards are confluence-stable — the invariant
survives merging independently-taken steps:

* `keeps_iff_coordinationFree` — a guard preserves confluence iff it runs
  coordination-free;
* `monotone_keeps` — monotone thresholds are free;
* `bounded_breaks` / `bounded_forces_ordering` — upper bounds force
  ordering.

This is the independence logic of §2.4 landing in the guard language: a
confluence-stable guard runs coordination-free; one that is not forces
ordering (consensus). The classifier does not forbid expensive guards — it
prices them honestly.

## 3.4 The disclosure dial

The second computed price is disclosure: how much a guard reveals while
being checked. The principle — *what the proof does not need, it does not
ask to see* — and the ladder, most to least disclosed:

1. **cleartext** — the predicate reads values directly;
2. **committed** — values behind Pedersen commitments; conservation checks
   homomorphically without opening
   (`PrivatePredicate.private_conservation_checks_homomorphically`;
   `Spec.committed_iff_cleartext` — the committed and cleartext judgments
   agree, so privacy does not change the law);
3. **range-proved** — only the bound is disclosed
   (`RangeProof.disclosure_only_the_bound`,
   `committed_inequality_via_range`);
4. **jointly garbled** — two parties evaluate a shared gate over private
   inputs and learn the verdict and nothing else
   (`GarbledJoint.garbled_input_private`, `joint_turn_private_gate`); the
   disclosure floor of a garbled gate is acceptance-only
   (`garbledDialFloor_is_bot`).

Selective disclosure of receipts (hide / reveal / predicate /
committed-threshold) is the same dial applied to Q (§4): a projection, not a
copy.
