# GOAL — P10: the IPA/FRI opening-soundness floor (the last inherited floor under the bridge)

## The mission
Both directions of the Mina↔dregg bridge bottom out in P10 — "the check passes" (`MinaWrapOpeningGate.
opening_relation_holds`, proven on a real Mina block) is not "the opening is sound" (an extraction
argument, nowhere in this tree). Follows directly from `pickles-p4` (GATE MET 2026-07-28,
`PicklesTranscriptBinding.lean`), whose own closing line named P10 as the one untouched residual.
Task: decide what P10 actually requires, precisely; settle whatever is genuinely settleable; price
the rest with a real number over real parameters; connect to the deployed verifier as far as
possible. Not a theorem that reads well — the priced number, honestly computed, is the point.

## Result — GATE MET, 2026-07-28
New module `metatheory/Dregg2/Crypto/IpaOpeningExtractionFloor.lean` (10 theorems,
`#assert_namespace_axioms`-clean, no sorry/native_decide, zero warnings). NOT added to
`Dregg2.lean` (new-module discipline, matching pickles-p4) — import line:
`import Dregg2.Crypto.IpaOpeningExtractionFloor`.

**Grounded against the actual state of the art first.** `l-adic/snarky`'s `formal/` (public,
unlicensed — read on GitHub for grounding, never imported, never copied) is the most complete
existing treatment: `Bulletproof/Soundness.lean` proves batched IPA knowledge soundness via
Mathlib's Vandermonde API, given a `FiatShamirTreeB` hypothesis asserted WHOLESALE by four axioms
(`poseidon_fiat_shamir_{vesta,pallas}`, `kimchi_fiat_shamir_{vesta,pallas}`) and a `DLRelation`
binding hypothesis whose OWN docstring calls "information-theoretically false for a real
single-curve SRS" — confirming, verbatim, both halves of ember's brief.

**P10 decomposed into FOUR things** (module docstring §-by-§):
1. **The linear-algebra step of extraction** — SETTLED (`vandermonde_dual_basis`, independently
   derived via `Matrix.det_vandermonde_ne_zero_iff`, never copying l-adic's code), instantiated at
   Pasta's real `qN` (`vandermonde_dual_basis_pasta`, given a named, undischarged `Fact
   (Nat.Prime pastaQ)` — `KimchiVerify.lean`'s own reason there is no `Field (ZMod pN)` instance:
   255-bit primality by `decide` is infeasible).
2. **The binding/no-relation idealization** — SETTLED FALSE (`srsRelation_exists`: rank-nullity via
   `Module.finrank` — an SRS with ≥2 generators in a group whose cardinality matches the scalar
   field's always has a nontrivial relation; `commitment_not_binding`: the same fact cashed out as
   "two different witnesses open the same commitment"; `dlog_of_relation`: a 2-generator relation
   reduces cleanly to a discrete log). Connects to THIS TREE'S OWN `FloorGames.DLFamily`/`dlGame` —
   already known `⊤`-false (`dlHardQuant_top_false`), already lacking an `Eff`, same shape as
   `MSISHardQuant`/`HashCRHardQuant` before the ROM escape.
3. **Challenge-distinctness of `T` rewound transcripts** — PRICED (`manyFreshDistinct_bound_pasta`,
   via a new union-bound lemma over `RomCounting`'s `condProb`, reusing `RomQueryFloor`'s PROVED
   `condProb_two_fresh_eq` unchanged): at `T=64` and the real Pasta modulus, `≤ 4096/pastaQ ≈
   2⁻²⁴³`.
4. **Getting `T` accepting transcripts from one prover at all** (the rewinding/forking argument) —
   NAMED, NOT DISCHARGED. Needs an interactive-prover-with-cost-budget object this tree does not
   have (`RomOracle`/`FloorGames` model a single-shot oracle adversary only). Real, unbuilt,
   moderately-sized formalization work per `reference-grounding-efficient-adversaries`'s own survey
   — not open research, but not attempted here, and NOT smuggled in via an axiom.

**What's still assumed, precisely — two things, and only two:** (1) the rewinding/forking argument
(item 4 above); (2) the computational hardness of FINDING the relation §2 proves EXISTS — exactly
`FloorGames.DLHardQuant` at Pasta's own curve group, a floor this tree already names and already
knows is vacuous at `⊤`, with no `Eff` yet.

**Connected to the deployed verifier in prose** (not by import, to keep this floor's build
independent of the heavy AIR-emission chain): ties to `MinaWrapOpeningGate`'s real `CHAL`/`CHAL_INV`
objects on the IPA side, and to `FriLdtExtractV3`'s already-documented vacuity wound
(`project-fri-correlated-agreement-formalization`) on the FRI side. Both directions bottom out in
the SAME missing ingredient — a probabilistic rewinding-cost model for Fiat–Shamir extraction — not
two unrelated gaps. FRI's own mathematical crux (correlated agreement) is separately already
proven; this file's method (the distinctness price) transfers to it directly, its Vandermonde
extraction does not (a different, already-built mechanism there).

## Done-log
- `ae0a587f6` — P10 (1/1): `IpaOpeningExtractionFloor.lean` — 2 pieces settled (Vandermonde
  extraction; binding-idealization falsity + DL reduction), 1 priced (T-wise challenge distinctness
  at real Pasta params, ≈2⁻²⁴³), 2 named as genuinely irreducible (rewinding cost model; DL search
  hardness). 10 theorems, axiom-clean.

## What's NOT done (follow-on, not required by this goal's gate)
- Building the interactive-prover/rewinding-cost-budget object itself (P10 item 4) — the single
  largest remaining piece, and the one both bridge directions share.
- A query-bounded (or generic-group) escape for `FloorGames.DLHardQuant`, mirroring what
  `RomQueryFloor` did for the hash floor — genuinely harder (GGM, not ROM) and not attempted.
- Wiring `IpaOpeningExtractionFloor`'s abstract results against a CONCRETE `[Module (ZMod qN)
  PastaPoint]` instance for this tree's own executable curve-point type (currently Nat-triple
  arithmetic, no abstract group/module typeclass) — would let §B's relation-existence instantiate
  concretely rather than by cardinality hypothesis.
- Formalizing an explicit primality certificate for `pastaQ` (a Pratt certificate via `norm_num`,
  or an imported literature fact) to discharge `vandermonde_dual_basis_pasta`'s named `Fact`.
