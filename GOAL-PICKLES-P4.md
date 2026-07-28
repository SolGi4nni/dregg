# GOAL — PICKLES P4: the transcript-equality binding (recursion soundness)

## The mission
`PicklesFinalize.lean`'s P4 (the assert families that bind the sampled transcript to the exposed
deferred-values record) was FORMALIZED and MEASURED but not proved sound: §Z named three residuals
— (1) the sponge-digest equality pins a value, not a history (a ROM assumption with no object in
this tree); (2) `endo` injectivity on 128-bit prechallenges (a hypothesis, never proven); (3) the
IPA opening floor (P10, inherited). Task: settle (2) either way, reduce (1) to a priced residual,
state P4 honestly.

## Result — GATE MET, 2026-07-28
New module `metatheory/Dregg2/Circuit/Emit/PicklesTranscriptBinding.lean` (45 theorems,
`#assert_namespace_axioms`-clean, no sorry/native_decide). NOT added to `Dregg2.lean` (new-module
discipline) — import line to add when integrated: `import Dregg2.Circuit.Emit.PicklesTranscriptBinding`.

- **(2) SETTLED TRUE.** `endoMap` (the real `to_field_checked_prime` then `a·endo+b`, at the actual
  constant Pickles uses, `lambdaVesta`) is injective on 128-bit prechallenges (`endoMap_injective_mod`).
  Two independent obstructions, both closed:
  - Combinatorial: the bit-stream-to-`(a,b)` decode is injective (`foldAB_injective_of_len_eq`) —
    proved via a `c=a+b`/`d=a-b` decomposition reducing to "fixed-length signed-binary digit streams
    are injective" (`signedBinary_injective`), a clean disjoint-integer-ranges induction.
  - Field-level: `(a,b) ↦ a·lambdaVesta+b` is injective on the reachable range (`glv_no_small_relation`).
    The GLV lattice `{(x,y) : x ≡ y·lambdaVesta (mod pN)}` was Gauss/Lagrange-reduced OUTSIDE Lean on
    the real 255-bit constants: shortest vector norm ≈2^127 (`glvA`,`glvB`), cross-checked against
    the classical Eisenstein-integer identity `a²+ab+b² = pN` it satisfies exactly — ~57 bits above
    the `<2^70` range 128 bits can reach. Minimality proved by an elementary coprimality argument
    (no general lattice-reduction theory formalized).
- **(1) REDUCED to a priced residual.** `hashSepOn` (mirroring `Sha256MerkleFold.pairSepOn`'s
  three-legs discipline) over the REAL `PastaPoseidon.Ref.hash`: refuted at `⊤` by a clean, generic
  mod-`pN` collision (`hash_singleton_ignores_mod_pN`) plus a sharper zero-query structural one
  (`hash_empty_eq_hash_zero` — absorbing nothing and absorbing a bare `0` coincide); satisfiable at
  an exhibited 3-transcript class over the real deployed Poseidon. Priced via the tree's PROVED
  `RomQueryFloor.birthday_bound` at the real digest cardinality `pN ≈ 2^255`
  (`deployed_digest_noCollision`): a `Q`-query forger's collision odds are `≤(Q²+1)/pN`, i.e. zero
  for any real budget. The one remaining named assumption: `SpongeKeyedROFaithful` (a fresh,
  per-experiment ROM-heuristic predicate mirroring `Poseidon2RomInstantiation.KeyedRomFaithful`,
  collision face only).
- **What's still assumed, precisely:** `SpongeKeyedROFaithful` for the one experiment (irreducible —
  no hash is unconditionally a random oracle) and P10 (IPA/FRI opening soundness, `PicklesRecursion`
  §Z item 5, untouched). Nothing else — `endo` injectivity is now a theorem.

## Incident, corrected in the same commit
An automated tree-wide "sweep up" commit (`af12e0cc2`) picked up this file mid-edit (an early,
incomplete local draft carrying a `sorry` and a placeholder lemma reference) and landed it on
`main` while this work was in progress. The finishing commit (`5ecafe486`) replaces it with the
complete, kernel-checked version — the `sorry` never reached a state anyone could have cited.

## Done-log
- `5ecafe486` — P4 (1/1): `PicklesTranscriptBinding.lean` — endo injectivity settled (GLV lattice,
  computed); digest binding reduced to a priced ROM residual (`birthday_bound` at `pN≈2^255`).
  45 theorems, axiom-clean. Also corrects the accidental swept `sorry` draft.

## What's NOT done (follow-on, not required by this goal's gate)
- Wiring `endoMap_injective_mod` / `hashSepOn` directly into `PicklesFinalize.binding_and_accept_
  determine`'s own statement (currently a standalone, composable result at the concrete Fp
  instantiation — the composition is straightforward but not yet a single theorem).
- P5 (the Step-side mirror of P4) — untouched, per `PicklesFinalize`'s own §Z handoff note.
- P10 (the IPA opening floor) — genuinely inherited, not attempted.
