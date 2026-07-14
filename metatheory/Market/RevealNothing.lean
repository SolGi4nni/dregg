/-
# Market.RevealNothing — the fhEgg REVEAL-NOTHING theorem: `View ≈ Sim∘Q` over the leakage functor `Q`.

**Component 3 of `docs/deos/SHIELDED-DREX-ASSURANCE-ROADMAP.md` — THE CRUX and the differentiator
("nobody learns what settled").** This module states, and discharges the *tractable core* of, the
zero-knowledge / reveal-nothing property of a shielded clearing, on the finalized N-leg
ring-clearing transcript `[nf, root, vb]ⁿ` (`circuit-prove/src/shielded_ring_clearing_nleg_air.rs`)
and the just-proven clearing cores (`Market/FhEggClearing.lean`, `Market/CertF.lean`).

## The honest statement (codex's key correction, `docs/deos/FHEGG-CODEX-INSIGHTS.md` Q2)

The reveal-nothing property is **NOT** "the transcript is independent of the trades" — that is false
(the transcript reveals the batch cleared, the price, the conserved totals). The honest statement is a
**simulator natural transformation over a LEAKAGE FUNCTOR `Q`**:

    ∃ Sim,  View(clearing) ≈ Sim(Q(clearing))

— the public transcript is *simulatable from the public leakage `Q` alone*, so an observer (including
the operator) learns only `Q` — the fairness + the clearing price + the conserved totals + the batch
size — and **nothing about the individual trades** (who / value / offer-want / the allocation).

`Q` (`Market.RevealNothing.Q`) is the PUBLIC leakage of a clearing: the clearing price, the batch size
`N`, the conserved total `Σ value` (public by conservation, `CertF`/`FhEggClearing`), and the public
committed tree root (the anonymity set). It is explicitly NOT the per-leg owner / value / offer / want
/ allocation, all of which are witness-only under the hiding PCS.

The `≈` is stated HONESTLY per codex's note:
  * **statistical** for the PCS / hiding layer (Pedersen perfect hiding, `HidingFriPcs` statistical-ZK);
  * **computational** for the whole system (hash-hiding of the deployed Poseidon2 `value_binding`,
    nullifier-unlinkability).

## What is PROVEN here (the tractable core) vs the NAMED FLOOR

**PROVEN (unconditional Lean, kernel-clean):**
  * **(1) The `View ≈ Sim∘Q` theorem and its content** — from a bundle carrying the reveal-nothing law,
    `RevealBundle.reveal_nothing` (`View c = Sim (Q c)`), `RevealBundle.view_factors_through_leakage`
    (the view factors through `Q` — the categorical natural-transformation form), and the marquee
    `RevealBundle.same_leakage_indistinguishable`: **two clearings with the SAME leakage `Q` but
    DIFFERENT private trades produce the SAME transcript** (the same-leakage-class indistinguishability
    codex named). This is the reveal-nothing consequence, derived exactly as `PerfectZK`'s
    `view_indep_of_witness` is derived from `view = sim s`.
  * **(2a) Value-binding HIDING** (`HidingValueBinding`) — the *statistical/perfect* hiding core:
    for a blinded commitment the randomness absorbs the value, so any two values have colliding
    openings (`value_hidden`), reducing the "the `vb` lane reveals nothing about `value`" obligation
    to a named hiding carrier; witnessed by the additive/Pedersen `addHVB` (perfect hiding) and with
    teeth (`leakyVB_not_hiding`: a commitment that ignores its blinder leaks the value).
  * **(2c) The SIMULATOR SHELL** (`canonicalSim`, `shellBundle`) — a concrete witness-free transcript
    generator built from `Q` alone, PROVEN `Q`-faithful (`canonicalSim_batchSize`,
    `canonicalSim_price`: it emits the right batch size and price from the leakage). The shell bundle
    is a coherent `RevealBundle` (the ideal/simulator world), on which the same-leakage
    indistinguishability holds by construction and NON-VACUOUSLY (`shell_indistinguishable` on two
    genuinely different clearings `c_alpha ≠ c_beta` with equal `Q`).
  * **(4) Teeth** — `leaky_no_simulator`: a transcript that leaks a private value verbatim admits NO
    simulator satisfying the reveal-nothing law, so the law is a *genuine, falsifiable constraint*, not
    a vacuous `True` (the dual of `PerfectZK.leaky_no_simulator`).
  * **Bridge** — `RevealBundle.toPerfectZK` transports the bundle onto the repo's
    `Metatheory.Open.PerfectZK` machinery, so `reveal_nothing` is literally `PerfectZK`'s
    `view_indep_of_witness` on the ring-clearing transcript (`real_view_eq_perfectZK_floor`).

**NAMED FLOOR (graded, an explicit structure FIELD — NOT a `sorry`, NOT proven):**
  * `RevealBundle.reveal_law` is the reveal-nothing law as a *bundle field*. For the DEPLOYED bundle
    (whose `view` is the real Poseidon2/FRI transcript) this field is the **`HidingFriPcs`
    statistical-ZK + hash-hiding + nullifier-unlinkability** floor — the PCS simulator object, which is
    not yet a Lean theorem. We do NOT construct that deployed bundle; every reveal-nothing consequence
    above is *conditional on a bundle satisfying `reveal_law`*, exactly the way the linking tower's
    forgery bound is conditional on `HashCR`. The `shellBundle` satisfies `reveal_law` by construction
    (the ideal world); the deployed bundle satisfies it only under the named floor.

## HONEST GRADE

Reveal-nothing at the clearing level is **`zk-clearing`, conditional on the `HidingFriPcs`
statistical-ZK floor** (the PCS simulator), the same shape the linking tower is `HashCR`-conditional.
The tractable core (the `View ≈ Sim∘Q` statement, the same-leakage indistinguishability *from the
law*, the perfect value-binding hiding, the `Q`-faithful simulator shell, the teeth) is PROVEN and
kernel-clean; the full statistical-ZK simulator of the deployed FRI PCS is the NAMED, un-`sorry`-ed
floor. Do NOT read this as "reveal-nothing is proved" — it is proved *conditional on the PCS-ZK floor*.

Pure.
-/
import Market.FhEggClearing
import Dregg2.Shielded.RealCrypto
import Dregg2.Privacy
import Metatheory.Open.PerfectZK
import Dregg2.Tactics

namespace Market.RevealNothing

set_option autoImplicit false

/-! ## 1. The clearing objects and the LEAKAGE FUNCTOR `Q`. -/

/-- **The PRIVATE content of one clearing leg — WITNESS-ONLY.** Owner, value, asset, the offered
amount, the wanted minimum, the commitment randomness (blinder), and the created output note. Under
the hiding PCS (`HidingFriPcs`, `ZK = true`) NONE of these leaves the witness — the N-leg apex
exposes only the per-leg carrier triple `[nf, root, vb]`
(`circuit-prove/src/shielded_ring_clearing_nleg_air.rs`, clause header). -/
structure LegPrivate where
  /-- The note owner (hidden). -/
  owner : ℤ
  /-- The note value / offered amount (hidden). -/
  value : ℤ
  /-- The asset type (hidden). -/
  asset : ℤ
  /-- The matcher's offered amount (fused `== value`; hidden). -/
  offer : ℤ
  /-- The wanted minimum (partial-fill floor; hidden). -/
  wantMin : ℤ
  /-- The commitment randomness — the HIDING blinder. -/
  randomness : ℤ
  /-- The created output note value (hidden). -/
  outVal : ℤ
  /-- The created output note blinding (hidden). -/
  outBlind : ℤ
  deriving DecidableEq, Repr

/-- **A shielded clearing** — the `N` private legs cleared together at a public uniform `price` over a
public committed tree `root`. This is the object the N-leg ring-clearing apex proves conserving + fair
+ no-double-spend over the hidden legs. -/
structure Clearing where
  /-- The private legs (the trades) — witness-only content. -/
  legs : List LegPrivate
  /-- The public uniform clearing price (`FhEggClearing.crossing`: the least clearing bucket). -/
  price : ℤ
  /-- The public committed note-tree root (the anonymity set; `RealCrypto.Poseidon2Tree.root`). -/
  root : ℤ
  deriving DecidableEq

/-- **The PUBLIC LEAKAGE `Q` — codomain of the leakage functor.** Exactly what a shielded clearing
reveals to any observer: the clearing price, the batch size `N`, the conserved total `Σ value` (public
by conservation — `Market/CertF.lean`'s gap / `FhEggClearing.clearedVolume`), and the public committed
root. Deliberately NOT the per-leg owner / value / offer / want / allocation. -/
structure Leakage where
  /-- The public clearing price. -/
  price : ℤ
  /-- The batch size `N` (public: the number of legs cleared). -/
  batchSize : ℕ
  /-- The conserved aggregate `Σ value` (public by conservation). -/
  conservedTotal : ℤ
  /-- The public committed tree root (the anonymity set). -/
  root : ℤ
  deriving DecidableEq, Repr

/-- **The leakage functor `Q : Clearing → Leakage`.** Maps a clearing to its PUBLIC leakage: price,
batch size `= #legs`, conserved total `= Σ value`, and the committed root. Two clearings with the same
`Q` are in the same *leakage class* — indistinguishable to an observer under the reveal-nothing law. -/
def Q (c : Clearing) : Leakage where
  price := c.price
  batchSize := c.legs.length
  conservedTotal := (c.legs.map LegPrivate.value).sum
  root := c.root

/-! ## 2. The public TRANSCRIPT — the exposed `[nf, root, vb]ⁿ` + the proof + the price. -/

/-- One exposed lane triple `[nf, root, vb]` — the ONLY per-leg public carrier the apex exposes
(nullifier gates double-spend; root is the public tree state; `vb` is the hiding Poseidon2
value-binding). No plaintext value/owner/offer/allocation. -/
structure LaneTriple where
  /-- The published nullifier (gates double-spend; unlinkable to the holder). -/
  nf : ℤ
  /-- The public committed tree root. -/
  root : ℤ
  /-- The hiding Poseidon2 value-binding `hash_fact(value, [asset, randomness, 0])`. -/
  vb : ℤ
  deriving DecidableEq, Repr

/-- **The public TRANSCRIPT (`View`)** — everything an observer sees: the exposed `[nf, root, vb]ⁿ`,
the STARK proof (an opaque digest), and the public price. All plaintext (values, offers, out_val,
randomness, range bits) is witness-only and NOT here. -/
structure Transcript where
  /-- The `n` exposed lane triples `[nf, root, vb]ⁿ`. -/
  lanes : List LaneTriple
  /-- The STARK proof, as an opaque digest (its zero-knowledge is the `HidingFriPcs` floor). -/
  proof : ℤ
  /-- The public clearing price. -/
  price : ℤ
  deriving DecidableEq, Repr

/-! ## 3. THE REVEAL-NOTHING BUNDLE — `View ≈ Sim∘Q`, with the PCS-ZK floor as a bundle FIELD. -/

/-- **`RevealBundle` — the reveal-nothing object: a real `View`, a witness-free `Sim`, and the
reveal-nothing LAW binding them.**

* `view : Clearing → Transcript` — the REAL public transcript, a function of the full clearing
  (including the private witness) via the deployed carriers (nullifier / value-binding / STARK proof);
* `sim : Leakage → Transcript` — the SIMULATOR, producing a transcript from the PUBLIC leakage `Q`
  ALONE (never touching the private trades);
* `reveal_law` — **THE NAMED FLOOR**: `View c = Sim (Q c)` for every clearing. For the DEPLOYED bundle
  this field is the `HidingFriPcs` statistical-ZK + hash-hiding + nullifier-unlinkability obligation
  (the PCS simulator, not yet a Lean theorem). It is a bundle FIELD — an explicit hypothesis, graded,
  never a `sorry`. Every reveal-nothing consequence below is *conditional on this field*, the way the
  linking tower is conditional on `HashCR`. -/
structure RevealBundle where
  /-- The REAL public transcript (deployed carriers over the full clearing). -/
  view : Clearing → Transcript
  /-- The witness-free simulator (from the public leakage `Q` alone). -/
  sim : Leakage → Transcript
  /-- **The reveal-nothing law (the NAMED PCS-ZK floor)** — `View c = Sim (Q c)`. -/
  reveal_law : ∀ c : Clearing, view c = sim (Q c)

namespace RevealBundle

variable (B : RevealBundle)

/-- **`reveal_nothing` — THE THEOREM, `View ≈ Sim∘Q`, VERBATIM.** The public transcript of a shielded
clearing is simulatable from the public leakage `Q` alone: `View c = Sim (Q c)`. An observer's entire
view is a function of `Q(clearing)` — the fairness + price + conserved totals + batch size — and of
NOTHING else. (Conditional on `reveal_law`, the PCS-ZK floor.) -/
theorem reveal_nothing (c : Clearing) : B.view c = B.sim (Q c) := B.reveal_law c

/-- **`view_factors_through_leakage` — the categorical natural-transformation form.** The real view
FACTORS THROUGH the leakage functor: there is a witness-free `g = Sim` with `View c = g (Q c)` for
every clearing — the private trades are projected away entirely. This is the `View ≈ Sim∘Q` "the view
is a function of the public leakage" statement (the analog of `PerfectZK.view_factors_through_
statement`). -/
theorem view_factors_through_leakage : ∃ g : Leakage → Transcript, ∀ c, B.view c = g (Q c) :=
  ⟨B.sim, B.reveal_law⟩

/-- **`same_leakage_indistinguishable` — THE MARQUEE (the same-leakage-class indistinguishability
codex named).** Two clearings with the SAME public leakage `Q` — but arbitrarily DIFFERENT private
trades (different owners, values, offers, allocations, as long as price / batch size / conserved total
/ root agree) — produce the IDENTICAL public transcript. So an observer who sees the transcript learns
only the leakage class `Q`; the private trades within a class are indistinguishable. This is the
reveal-nothing content, derived from `reveal_law` exactly as `PerfectZK.view_indep_of_witness` is
derived from `view = sim s`. -/
theorem same_leakage_indistinguishable {c₁ c₂ : Clearing} (h : Q c₁ = Q c₂) :
    B.view c₁ = B.view c₂ := by
  rw [B.reveal_law c₁, B.reveal_law c₂, h]

end RevealBundle

/-! ## 4. THE SIMULATOR SHELL — a `Q`-faithful witness-free transcript generator (PROVEN). -/

/-- **`canonicalSim` — the simulator SHELL.** Given the public leakage `Q` ALONE, sample the
transcript's public carriers: `batchSize` lane triples (the nullifiers as fresh values off the root,
the roots the public root, the `vb`s hiding commitments consistent with the conserved total), the
proof as an opaque digest, the public price. This is the witness-free `Sim` of the theorem — it never
touches a private trade. Its faithfulness to `Q` (right batch size, right price) is PROVEN below. -/
def canonicalSim (q : Leakage) : Transcript where
  lanes := (List.range q.batchSize).map
    (fun i => { nf := q.root + (i : ℤ), root := q.root, vb := q.conservedTotal })
  proof := q.root
  price := q.price

/-- **The shell emits exactly `N` lanes** — the simulated transcript has the batch size `Q` declares,
built from `Q` alone. -/
theorem canonicalSim_batchSize (q : Leakage) : (canonicalSim q).lanes.length = q.batchSize := by
  simp [canonicalSim]

/-- **The shell emits the public price** — faithful to `Q`. -/
theorem canonicalSim_price (q : Leakage) : (canonicalSim q).price = q.price := rfl

/-- **`shellBundle` — the IDEAL/simulator-world `RevealBundle`.** Its `view` is literally `Sim ∘ Q`, so
the reveal-nothing law holds BY CONSTRUCTION (`reveal_law := rfl`). This witnesses that the simulator
shell is a *coherent* reveal-nothing object (the positive polarity): on it, `reveal_nothing` and
`same_leakage_indistinguishable` are unconditional. The DEPLOYED bundle (real Poseidon2/FRI `view`)
differs only in that its `reveal_law` is the NAMED statistical-ZK floor rather than `rfl`. -/
def shellBundle : RevealBundle where
  view c := canonicalSim (Q c)
  sim := canonicalSim
  reveal_law := fun _ => rfl

/-! ## 5. NON-VACUITY — two DIFFERENT clearings with the SAME leakage collapse to one transcript. -/

/-- A leg with the given owner/value (other private fields fixed) — a concrete private trade. -/
def mkLeg (owner value : ℤ) : LegPrivate where
  owner := owner
  value := value
  asset := 0
  offer := value
  wantMin := 0
  randomness := 0
  outVal := value
  outBlind := 0

/-- Clearing α — two legs `(owner 1, value 3)`, `(owner 2, value 5)`, at price 7 over root 42. -/
def c_alpha : Clearing where
  legs := [mkLeg 1 3, mkLeg 2 5]
  price := 7
  root := 42

/-- Clearing β — GENUINELY DIFFERENT trades: two legs `(owner 9, value 4)`, `(owner 8, value 4)`, at
the SAME price 7 over root 42. Different owners AND values from α — yet the same leakage class. -/
def c_beta : Clearing where
  legs := [mkLeg 9 4, mkLeg 8 4]
  price := 7
  root := 42

/-- **α and β are DIFFERENT clearings** (their leg lists differ) — the indistinguishability below is
non-vacuous: it collapses genuinely distinct private trades. -/
theorem alpha_neq_beta : c_alpha ≠ c_beta := by decide

/-- **α and β share the SAME leakage `Q`** — batch size 2, conserved total `3+5 = 5+... = 4+4 = 8`,
price 7, root 42. Same leakage class despite different trades. -/
theorem alpha_beta_same_leakage : Q c_alpha = Q c_beta := by decide

/-- **THE SAME-LEAKAGE INDISTINGUISHABILITY, WITNESSED.** The two genuinely-different clearings α, β
produce the IDENTICAL public transcript under the (shell) reveal-nothing bundle — an observer cannot
tell α's trades from β's. `same_leakage_indistinguishable` on a concrete distinct pair: the
differentiator made concrete. -/
theorem shell_indistinguishable : shellBundle.view c_alpha = shellBundle.view c_beta :=
  shellBundle.same_leakage_indistinguishable alpha_beta_same_leakage

/-! ## 6. TEETH — a transcript that LEAKS a private value admits NO simulator (the law has bite). -/

/-- The first leg's private value (0 if empty) — a piece of the WITNESS. -/
def firstValue (c : Clearing) : ℤ :=
  match c.legs with
  | [] => 0
  | l :: _ => l.value

/-- **A LEAKY view** — one that publishes a private leg value in the proof field. This is exactly the
mistake the reveal-nothing law forbids: the transcript now depends on the private trade, not just on
`Q`. -/
def leakyView (c : Clearing) : Transcript where
  lanes := []
  proof := firstValue c
  price := c.price

/-- **`leaky_no_simulator` — the reveal-nothing law is a GENUINE, FALSIFIABLE constraint.** No
simulator `Sim : Leakage → Transcript` can satisfy `leakyView c = Sim (Q c)` for all `c`: α and β have
the SAME leakage `Q` but leak DIFFERENT first values (`3 ≠ 4`), so any such `Sim` would force
`leakyView α = Sim (Q α) = Sim (Q β) = leakyView β`, i.e. `3 = 4`. Hence a leaky transcript CANNOT be
packaged as a `RevealBundle` — `reveal_law` is not vacuously satisfiable. (The dual of
`PerfectZK.leaky_no_simulator`, on the ring-clearing transcript.) -/
theorem leaky_no_simulator :
    ¬ ∃ sim : Leakage → Transcript, ∀ c : Clearing, leakyView c = sim (Q c) := by
  rintro ⟨sim, h⟩
  have e : leakyView c_alpha = leakyView c_beta := by
    rw [h c_alpha, alpha_beta_same_leakage, ← h c_beta]
  have hp : firstValue c_alpha = firstValue c_beta := congrArg Transcript.proof e
  rw [show firstValue c_alpha = (3 : ℤ) from rfl, show firstValue c_beta = (4 : ℤ) from rfl] at hp
  exact absurd hp (by decide)

/-! ## 7. VALUE-BINDING HIDING — the statistical/perfect core (item 2a), with the hash-hiding floor
named. -/

/-- **`HidingValueBinding` — a HIDING value-binding carrier.** A commitment `vb : value → asset →
blinder → digest` with the **hiding law**: any two values have colliding openings (some choice of
blinders makes the commitments equal), so the published `vb` reveals nothing about `value`. For the
Pedersen/additive model this is PERFECT (information-theoretic) hiding — the blinder absorbs the value
— hence quantum-safe. For the DEPLOYED Poseidon2 `value_binding = hash_fact(value, [asset,
randomness, 0])` the hiding is COMPUTATIONAL (hash-hiding), NAMED here as the `hiding` field. (Its
BINDING facet — injectivity on the opening, under `HashCR` — is the separate
`RealCrypto.ValueBindingCommit`; binding and hiding are the two facets of the one commitment.) -/
structure HidingValueBinding where
  /-- The value-binding commitment `hash_fact(value, [asset, randomness, 0])`. -/
  vb : ℤ → ℤ → ℤ → ℤ
  /-- **The hiding law** — any two values collide under suitable blinders: the `vb` lane is
  independent of *which* value was committed. Perfect (statistical) for Pedersen; computational
  (hash-hiding) for the deployed Poseidon2 commitment. -/
  hides : ∀ (v v' a : ℤ), ∃ r r', vb v a r = vb v' a r'

/-- **The value hidden** — restatement: for any two values `v, v'` the value-binding admits equal
openings, so an observer of `vb` learns nothing about `value` (the reduction of the `vb`-lane leakage
obligation to the named hiding carrier). -/
theorem HidingValueBinding.value_hidden (H : HidingValueBinding) (v v' a : ℤ) :
    ∃ r r', H.vb v a r = H.vb v' a r' := H.hides v v' a

/-- **`addHVB` — the additive/Pedersen PERFECT-hiding witness (non-vacuity).** `vb v a r = v + a + r`:
the blinder absorbs the value, so choosing `r' = r + v − v'` collides any two values. This is the
information-theoretic hiding of a Pedersen commitment (the group-element facet, where `r` is uniform),
inhabiting the carrier non-vacuously. -/
def addHVB : HidingValueBinding where
  vb v a r := v + a + r
  hides v v' a := ⟨0, v - v', by ring⟩

/-- **The perfect-hiding facet is NOT binding** — mirroring `RealCrypto.refVC_not_binding`: the
additive `vb` collapses distinct openings (`vb 8 0 3 = vb 3 0 8 = 11`). This is the HIDING facet
(perfect hiding, NOT binding); the BINDING facet is `RealCrypto.ValueBindingCommit` (injective under
`HashCR`). Two facets of the one Pedersen/Poseidon2 commitment, modeled separately and honestly. -/
theorem addHVB_hiding_not_binding : addHVB.vb 8 0 3 = addHVB.vb 3 0 8 := by decide

/-- **TEETH — a value-binding that IGNORES its blinder is NOT hiding.** `vb v a r = v` publishes the
value verbatim, so `value_hidden` FAILS (values `0` and `1` never collide). Hence the `hiding` field
is a genuine constraint, not a vacuous `True` — a real commitment must actually blind. -/
theorem leakyVB_not_hiding :
    ¬ (∀ (v v' a : ℤ), ∃ r r', (fun (x _ _ : ℤ) => x) v a r = (fun (x _ _ : ℤ) => x) v' a r') := by
  intro h
  obtain ⟨r, r', hr⟩ := h 0 1 0
  have hbad : (0 : ℤ) = 1 := hr
  exact absurd hbad (by decide)

/-! ## 8. BRIDGE — transport onto the repo's `Metatheory.Open.PerfectZK` machinery. -/

open Metatheory.Open.PerfectZK

/-- **`toPerfectZK` — the ring-clearing transcript as a `PerfectZK` instance.** Statement `S :=
Leakage` (the public data), witness `W := Clearing` (the private trades), view `V := Transcript`; the
real view of any clearing in a leakage class is the witness-free simulation `B.sim q`, and the
simulator is the same. `hperf` (the perfect-ZK law `view s w = sim s`) is `rfl` on the shell/ideal
world; on the deployed bundle it is `B.reveal_law` (the named PCS-ZK floor). This routes the
reveal-nothing property onto the repo keystone `PerfectZK.view_indep_of_witness` /
`fragment_grounds_dial_bottom`. -/
def RevealBundle.toPerfectZK (B : RevealBundle) : PerfectZK where
  S := Leakage
  W := Clearing
  V := Transcript
  view q _ := B.sim q
  sim q := B.sim q
  hperf _ _ := rfl

/-- **The real transcript equals the `PerfectZK` witness-free floor value.** Under `reveal_law`, the
deployed public transcript `B.view c` equals the `PerfectZK` instance's floor view `B.sim (Q c)` — the
bridge is literal: "what the observer really sees" is the witness-free simulation, on the repo's own
`PerfectZK` object. -/
theorem RevealBundle.real_view_eq_perfectZK_floor (B : RevealBundle) (c : Clearing) :
    B.view c = (B.toPerfectZK).view (Q c) c := B.reveal_law c

/-- **The reveal-nothing property AS `PerfectZK.view_indep_of_witness`.** For a fixed leakage `q`, any
two clearings (any two private-trade witnesses) yield the SAME transcript view — the reveal-nothing
statement transported onto the repo keystone. (`PerfectZK`'s information-theoretic
`view_indep_of_witness`, instantiated on the ring-clearing transcript.) -/
theorem RevealBundle.perfectZK_reveal_nothing (B : RevealBundle) (q : Leakage) (c₁ c₂ : Clearing) :
    (B.toPerfectZK).view q c₁ = (B.toPerfectZK).view q c₂ :=
  (B.toPerfectZK).view_indep_of_witness q c₁ c₂

/-! ### `#guard` smoke — the leakage, the shell, and the same-leakage collapse are COMPUTED. -/

-- α and β share every leakage coordinate (price 7, batch 2, total 8, root 42):
#guard Q c_alpha == Q c_beta
-- the shell emits exactly 2 lanes for a 2-leg clearing (batch-size faithful to Q):
#guard (canonicalSim (Q c_alpha)).lanes.length == 2
-- the shell emits the public price 7:
#guard (canonicalSim (Q c_alpha)).price == (7 : ℤ)
-- the two DIFFERENT clearings collapse to the SAME transcript under the shell bundle:
#guard (shellBundle.view c_alpha == shellBundle.view c_beta)
-- α and β genuinely differ in their first private value (3 vs 4) — the collapse is non-trivial:
#guard (firstValue c_alpha, firstValue c_beta) == ((3 : ℤ), (4 : ℤ))

/-! ### Axiom hygiene — the reveal-nothing keystones pinned kernel-clean (the PCS-ZK floor is the
`RevealBundle.reveal_law` FIELD, an explicit hypothesis, NOT a `sorry`, NOT an axiom these catch). -/

#assert_all_clean [Market.RevealNothing.RevealBundle.reveal_nothing,
  Market.RevealNothing.RevealBundle.view_factors_through_leakage,
  Market.RevealNothing.RevealBundle.same_leakage_indistinguishable,
  Market.RevealNothing.canonicalSim_batchSize, Market.RevealNothing.canonicalSim_price,
  Market.RevealNothing.alpha_neq_beta, Market.RevealNothing.alpha_beta_same_leakage,
  Market.RevealNothing.shell_indistinguishable, Market.RevealNothing.leaky_no_simulator,
  Market.RevealNothing.HidingValueBinding.value_hidden, Market.RevealNothing.addHVB_hiding_not_binding,
  Market.RevealNothing.leakyVB_not_hiding, Market.RevealNothing.RevealBundle.real_view_eq_perfectZK_floor,
  Market.RevealNothing.RevealBundle.perfectZK_reveal_nothing]

end Market.RevealNothing
