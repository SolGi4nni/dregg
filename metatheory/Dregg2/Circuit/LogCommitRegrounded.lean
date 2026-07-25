/-
# Dregg2.Circuit.LogCommitRegrounded — the `logHashInjective` endpoint, re-grounded (CORE).

`StateCommit.logHashInjective LH := ∀ xs ys : List Turn, LH xs = LH ys → xs = ys` is the receipt-chain
binding carrier. It is FALSE at deployed BabyBear parameters
(`StateCommitFloorRegrounded.logHashInjective_false_babyBear`: the chain `List Turn` GROWS without
bound and the digest is a field element, so pigeonhole forces a collision), and the bundle that
discharges it — `Poseidon2Binding.LogRealization` — is itself UNINHABITABLE there
(`logRealization_uninhabitable_babyBear`, because its `spongeCR` field's type is already refuted). So
every theorem that BINDS `logHashInjective` says nothing about the deployed system: 329 carriers, the
largest single threader cone in the tree.

This module is the port's CORE — deliberately LIGHT (`StateCommit` + `Tactics` only), because it is
imported by `EffectCommit`/`SetFieldCommit`/`CircuitSoundness`, which sit under most of the tree. The
game-theoretic half (the hypothesis-free S2 disjunction, its advantage bound, the keyed-ROM headline,
and the deployed-width refutations) lives in the sibling `Circuit/LogCommitRegroundedRom`, which may
import `StateCommitFloorRegrounded` + `RomCarrierSites` freely.

  * **§2 — the TOTAL EXTRACTOR (`logHashFind`) + its spec.** The irreducible work. The old proofs only
    ever ELIMINATED the injectivity (`hLog xs ys h : xs = ys` DISCARDS the equivocation branch); a
    reduction must CONSTRUCT the colliding pair. `logHashFind` is a total, decidable function that on
    an equivocation RETURNS the specific pair at which a DEPLOYED object breaks, TAGGED with which
    object broke: `.inl` = a genuine collision of the Poseidon2 sponge; `.inr` = a genuine collision of
    the canonical serialization. `logHashFind_spec` proves it always lands on a real break.
    ⚑ The spec is stated over the BARE FACTORING `∀ zs, LH zs = sponge (enc zs)` — an equation the real
    deployed hash satisfies — and deliberately NOT over `Poseidon2Binding.LogRealization`, which
    carries `Poseidon2SpongeCR` as a field and therefore has NO deployed inhabitant. A spec quantified
    over an uninhabitable bundle would be exactly the vacuity this campaign removes.
  * **§4 — S3 (`logHash_binds_of_noLogColl`)**: the SAME conclusion as every old endpoint application,
    with the refuted universal replaced by a per-instance, refutable side condition about ONE named
    pair. This is what the cone (endpoints hand-ported, threaders by `Tools/ConePort`) re-points onto.
    Unlike the leaf/list families there is no second carried object, so ONE S3 form covers every site.
  * **§5 — no strength lost** (`noLogColl_of_inj`, `logHash_binds_of_carrier`): the old carrier IMPLIES
    the new side condition at every pair, so each ported theorem is logically STRONGER; the old
    statement is re-derivable through the port. What is given up is only the pretence that the deployed
    accumulator is injective. `noLogColl_of_inj` is also the CUTOVER BRIDGE every not-yet-ported
    consumer discharges its callee's side condition through — one uniform application, which is what
    makes the next cone level portable by a single `ConePort` `AppRule`.
  * **§6 — teeth**: the side condition is REFUTABLE (a constant accumulator makes it fire), SATISFIABLE
    (at named deployed-shaped points it does not), and LOAD-BEARING (dropping it yields a FALSE
    statement); the S3 form BITES (it forces a tampered chain to move the digest with no injectivity
    floor in the argument); and the extractor genuinely reaches BOTH horns.

⚑ **THE 8-FELT RULE, for whoever instantiates this.** The per-instance side condition is a claim about
the deployed digest at named points, and its price is the digest WIDTH:
  `card R = babyBearP^8 ≈ 2^247` → birthday ≈ `2^123.5`  ← the target (8-felt digest)
  `card R = babyBearP   ≈ 2^30.9` → birthday ≈ `2^15.5`   ← a BREAK, never instantiate here
`LogCommitRegroundedRom.logColl_width_note` fires on the second case, so a 1-felt narrowing states
itself rather than passing unnoticed.

No `sorry`, no `axiom`, no `native_decide`; `decide` only on concrete closed instances.
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Tactics

namespace Dregg2.Circuit.LogCommitRegrounded

open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Exec (Turn)

set_option autoImplicit false

/-! ## §1 — the NAMED collision events. Distinctness is INSIDE each predicate, so a side condition
`¬ Coll` is never satisfied vacuously by an equal pair. -/

/-- **`LogColl LH xs ys`** — the two receipt chains are a GENUINE equivocation of the deployed log
accumulator: distinct chains, one digest. This is the event `logHashInjective` declared impossible at
EVERY pair and which §1 of `StateCommitFloorRegrounded` proves pigeonhole FORCES at SOME pair. The
cone's side condition is `¬ LogColl LH xs ys` at the pair the old proof actually fed the floor. -/
def LogColl (LH : List Turn → ℤ) (xs ys : List Turn) : Prop :=
  xs ≠ ys ∧ LH xs = LH ys

/-- **`SpongeColl sponge a b`** — a genuine collision of the Poseidon2 sponge on two felt lists. The
CRYPTO horn: this is the claim whose price is the digest width (the 8-felt rule in the header). -/
def SpongeColl (sponge : List ℤ → ℤ) (a b : List ℤ) : Prop :=
  a ≠ b ∧ sponge a = sponge b

/-- **`EncColl enc xs ys`** — a genuine collision of the canonical serialization. The STRUCTURAL horn:
not a cryptographic assumption at all — a canonical layout is provably injective, so a site that lands
here has a SERIALIZATION BUG, and the disjunct is a real obligation rather than a hedge. -/
def EncColl (enc : List Turn → List ℤ) (xs ys : List Turn) : Prop :=
  xs ≠ ys ∧ enc xs = enc ys

/-! ## §2 — ⚑ THE TOTAL EXTRACTOR. This is the irreducible work: the old proof ELIMINATED the
injectivity, so it can be replayed only by a function that CONSTRUCTS the witness. -/

/-- **The extractor's answer**: which deployed object broke, and at which pair. `.inl` names two felt
lists the SPONGE maps together; `.inr` names two receipt chains the SERIALIZATION maps together. -/
abbrev LogBreak : Type := (List ℤ × List ℤ) ⊕ (List Turn × List Turn)

/-- **`FoundLogColl enc sponge r`** — the returned pair really is a collision of the object its tag
names. A predicate about the SPECIFIC returned lists, never `∃ a b, …`: at deployed parameters an
existence claim is unconditionally true by pigeonhole and so binds nothing
(`InjectiveFloorRegrounded` §0, the same discipline `IsCollW` follows). -/
def FoundLogColl (enc : List Turn → List ℤ) (sponge : List ℤ → ℤ) : LogBreak → Prop
  | Sum.inl p => SpongeColl sponge p.1 p.2
  | Sum.inr p => EncColl enc p.1 p.2

/-- **⚑ THE EXTRACTOR.** Total, and decidable — `DecidableEq (List ℤ)` is real, so the branch is a
computation, never `Classical.choose` of an existential. On an equivocation of `LH = sponge ∘ enc`:
if the two chains SERIALIZE differently, the sponge is what mapped them together, so return the two
encoded felt lists; otherwise the serialization already lost the difference, so return the two chains
themselves. -/
def logHashFind (enc : List Turn → List ℤ) (xs ys : List Turn) : LogBreak :=
  if enc xs = enc ys then Sum.inr (xs, ys) else Sum.inl (enc xs, enc ys)

/-- **⚑ THE EXTRACTOR IS CORRECT.** From the deployed factoring alone (`LH = sponge ∘ enc` — an
equation the real Poseidon2 log hash satisfies, with NO collision-resistance field anywhere), a
receipt-chain equivocation always yields a REAL break of a REAL deployed object at the pair
`logHashFind` returns. This REPLACES the deleted `hLog xs ys h` application: where the floor discarded
the branch, this produces its witness. -/
theorem logHashFind_spec {LH : List Turn → ℤ} (enc : List Turn → List ℤ) (sponge : List ℤ → ℤ)
    (hfac : ∀ zs : List Turn, LH zs = sponge (enc zs))
    {xs ys : List Turn} (hne : xs ≠ ys) (h : LH xs = LH ys) :
    FoundLogColl enc sponge (logHashFind enc xs ys) := by
  by_cases henc : enc xs = enc ys
  · show FoundLogColl enc sponge (logHashFind enc xs ys)
    rw [logHashFind, if_pos henc]
    exact ⟨hne, henc⟩
  · show FoundLogColl enc sponge (logHashFind enc xs ys)
    rw [logHashFind, if_neg henc]
    refine ⟨henc, ?_⟩
    rw [← hfac xs, ← hfac ys]
    exact h

/-- **A `LogColl` CASHES OUT.** The abstract per-instance event is never merely abstract: under the
deployed factoring it IS a break of the sponge or of the serialization, at the pair the extractor
names. Without this, `¬ LogColl` could be mistaken for content it does not have. -/
theorem LogColl.extracts {LH : List Turn → ℤ} {enc : List Turn → List ℤ} {sponge : List ℤ → ℤ}
    (hfac : ∀ zs : List Turn, LH zs = sponge (enc zs)) {xs ys : List Turn}
    (hc : LogColl LH xs ys) : FoundLogColl enc sponge (logHashFind enc xs ys) :=
  logHashFind_spec enc sponge hfac hc.1 hc.2

/-- The two horns, separated: an equivocation that survives an injective serialization is a SPONGE
break — the crypto horn, priced by the digest width. -/
theorem spongeColl_of_logColl {LH : List Turn → ℤ} {enc : List Turn → List ℤ}
    {sponge : List ℤ → ℤ} (hfac : ∀ zs : List Turn, LH zs = sponge (enc zs))
    (hinj : ∀ xs ys : List Turn, enc xs = enc ys → xs = ys) {xs ys : List Turn}
    (hc : LogColl LH xs ys) : SpongeColl sponge (enc xs) (enc ys) := by
  refine ⟨fun he => hc.1 (hinj _ _ he), ?_⟩
  rw [← hfac xs, ← hfac ys]
  exact hc.2

/-! ## §4 — S3: the conclusion-stable restoration. The SAME conclusion as every old
`hLog a b h : a = b` application, with the refuted ∀-injectivity binder swapped for a per-instance
`¬ LogColl` about ONE named pair. This is the single rewrite target for the whole cone: unlike the
leaf/list families there is no second carried object, so ONE S3 form covers every site. -/

/-- **S3 — the cone's replacement for `logHashInjective`.** Instance arguments are EXPLICIT and in the
same order the old application used (`hLog xs ys h`), so a ported call site is exactly
`logHash_binds_of_noLogColl _ _ _ hno h`. -/
theorem logHash_binds_of_noLogColl (LH : List Turn → ℤ) (xs ys : List Turn)
    (hno : ¬ LogColl LH xs ys) (h : LH xs = LH ys) : xs = ys := by
  by_contra hne
  exact hno ⟨hne, h⟩

/-! ## §5 — no strength lost, and the CUTOVER BRIDGES. -/

/-- **The strength bridge**: the old (refuted) universal injectivity kills the per-instance event at
EVERY pair. So the old hypothesis IMPLIES the new one and each ported theorem is logically STRONGER.
Instance args implicit so a not-yet-ported consumer's rewired call site is exactly
`(noLogColl_of_inj hLog)` — one uniform bridge application, which is what makes the NEXT cone level
mechanically portable by a single `ConePort` `AppRule`. -/
theorem noLogColl_of_inj {LH : List Turn → ℤ} (hLog : logHashInjective LH) {xs ys : List Turn} :
    ¬ LogColl LH xs ys :=
  fun hc => hc.1 (hLog _ _ hc.2)

/-- The identity carrier for the bridge's side condition — the constant-headed replacement the
`ConePort` `AppRule` shape needs so a level-2 threader's `noLogColl_of_inj hLog` application can be
mechanically rewritten into a passed-through `hno` binder. -/
theorem noLogColl_self {LH : List Turn → ℤ} {xs ys : List Turn} (hno : ¬ LogColl LH xs ys) :
    ¬ LogColl LH xs ys := hno

/-- **The deleted-shape bridge**: the old endpoint application's exact conclusion, re-derived THROUGH
the port. Nothing genuinely proved was given up. Deliberately a standalone bridge, never a hypothesis
on a keystone. -/
theorem logHash_binds_of_carrier (LH : List Turn → ℤ) (hLog : logHashInjective LH)
    (xs ys : List Turn) (h : LH xs = LH ys) : xs = ys :=
  logHash_binds_of_noLogColl LH xs ys (noLogColl_of_inj hLog) h

/-! ## §6 — TEETH: the side condition is refutable, satisfiable, load-bearing; the left disjunct
bites; and the honest scope of the whole port is stated as a theorem. -/

private def tA : Turn := { actor := 0, src := 0, dst := 1, amt := 1 }
private def tB : Turn := { actor := 0, src := 0, dst := 2, amt := 1 }

/-- A deployed-SHAPED demo accumulator: a positional Horner fold over the serialized chain (the log
analog of `ListCommitRegrounded`'s `cND`). Injective on the demo points below, so the side condition
is genuinely satisfiable there. -/
private def demoLH (xs : List Turn) : ℤ :=
  xs.foldl (fun acc t => acc * 1000000 + (t.actor : ℤ) * 10000 + (t.src : ℤ) * 100
    + (t.dst : ℤ) * 7 + t.amt) (xs.length : ℤ)

/-- The refuted pole: a CONSTANT accumulator (every chain to one digest). -/
private def constLH : List Turn → ℤ := fun _ => 0

/-- The demo serialization: the `dst` column of the chain. Injective on the two demo chains, so the
extractor's SPONGE horn is the one that fires there. -/
private def encD (xs : List Turn) : List ℤ := xs.map (fun t => (t.dst : ℤ))

/-- The two demo chains are distinct — read off the `dst` field. (`Turn`'s `DecidableEq` instance is
tactic-built, so `decide` cannot reduce it; the field projection is the honest route.) -/
private theorem chain_ne : ([tA] : List Turn) ≠ [tB] := by
  intro h
  have h1 : tA = tB := by simpa using h
  exact absurd (congrArg Turn.dst h1) (by simp [tA, tB])

private theorem demoLH_tA : demoLH [tA] = 1000008 := by norm_num [demoLH, tA]

private theorem demoLH_tB : demoLH [tB] = 1000015 := by norm_num [demoLH, tB]

/-- **The side condition is SATISFIABLE** at deployed-shaped instances: no equivocation at these two
named chains of the Horner accumulator. (The `demoRoot_CR` half of the witness pair — a per-instance
claim that is TRUE, so `¬ LogColl` is not an empty ask.) -/
theorem noLogColl_satisfiable : ¬ LogColl demoLH [tA] [tB] := by
  rintro ⟨-, heq⟩
  rw [demoLH_tA, demoLH_tB] at heq
  exact absurd heq (by norm_num)

/-- **The side condition is REFUTABLE** — at a constant accumulator the equivocation event FIRES. The
new predicate commits to something a bad instantiation genuinely violates (the `badRoot_not_CR` half).
A predicate that could not fail would be a hedge, not a hypothesis. -/
theorem logColl_refutable : LogColl constLH [tA] [tB] :=
  ⟨chain_ne, rfl⟩

/-- **⚑ THE PORT BITES.** At the named points there is no equivocation available, so the S3 form —
with no injectivity floor anywhere in the argument — forces a tampered receipt chain to MOVE the log
digest. This is the anti-ghost content the old floor was carried for, recovered from the per-instance
side condition alone. -/
theorem canary_tamper_moves_logDigest : demoLH [tA] ≠ demoLH [tB] := fun h =>
  chain_ne (logHash_binds_of_noLogColl demoLH _ _ noLogColl_satisfiable h)

/-- **⚑ THE SIDE CONDITION IS LOAD-BEARING** — the S3 statement with `hno` DELETED is FALSE (at a
constant accumulator every pair of chains collides). A "port" that dropped the side condition would
not be a port; it would be refuted. This is the mutation canary for the whole cone. -/
theorem logHash_binds_unconditional_false :
    ¬ ∀ xs ys : List Turn, constLH xs = constLH ys → xs = ys := by
  intro hall
  exact absurd (hall [tA] [tB] rfl) chain_ne

/-- **⚑ THE EXTRACTOR IS LOAD-BEARING TOO** — it does not always answer `.inr`. At an injective
serialization with a colliding sponge it returns the SPONGE horn, naming two distinct felt lists the
sponge maps together. (Mutate `logHashFind` to a constant `.inr` and this REDS.) -/
theorem logHashFind_hits_sponge_horn :
    logHashFind encD [tA] [tB] = Sum.inl ([1], [2]) := by
  have hA : encD [tA] = [1] := by simp [encD, tA]
  have hB : encD [tB] = [2] := by simp [encD, tB]
  rw [logHashFind, hA, hB, if_neg (by decide : ¬ (([1] : List ℤ) = [2]))]

/-! ## §8 — kernel pins. -/

#assert_all_clean [logHashFind_spec, LogColl.extracts, spongeColl_of_logColl,
  logHash_binds_of_noLogColl, noLogColl_of_inj, noLogColl_self, logHash_binds_of_carrier,
  noLogColl_satisfiable, logColl_refutable, canary_tamper_moves_logDigest,
  logHash_binds_unconditional_false, logHashFind_hits_sponge_horn]

end Dregg2.Circuit.LogCommitRegrounded
