/-
# Dregg2.Deos.Membrane — the rehydration membrane cannot amplify across hops (leg 2 of the crown).

`docs/deos/DEOS.md` §"the verified-deos program", target 2 (**Membrane non-amplification**):

  > The rehydration membrane composes `is_attenuation` across hops; prove `reshare A→B→C ⟹ C's
  > authority ⊆ B's held ⊆ A's` (the chained lattice law — lift the proven `is_attenuation` to
  > projection composition). The Rust `Membrane` in `starbridge-web-surface` is the realization; the
  > Lean is the proof it cannot amplify.

`docs/desktop-os-research/REHYDRATABLE-SURFACES.md` residual #1: "`Membrane::reshare` composes
attenuation across chained reacquisitions (A→B→C) by re-applying the REAL `is_attenuation` per hop,
refusing any hop where C would receive more than B held — the same `is_attenuation` lattice the cap
crown proves, lifted to projection composition."

This is NOT new mathematics. Each membrane hop is `Dregg2.Exec.attenuate` (the per-viewer projection),
and the chained-hop guarantee is `Dregg2.Exec.attenuate_subset` composed with `List.Subset.trans`. A
membrane reshare A→B→C is `attenuate (attenuate cap)`, and the keystone `reshare_chain_attenuates`
says C's conferred authority ⊆ B's held ⊆ A's — by transitivity of the EXISTING per-hop subset law.

## What is proven (all by REUSE — no membrane-local lattice)

  * `oneHop_attenuates` — a single membrane hop (one `attenuate`) confers a SUBSET of the held
    authority. This IS `Dregg2.Exec.attenuate_subset`, named as "one membrane projection".
  * `reshare` — the A→B→C reshare: `attenuate keepBC (attenuate keepAB cap)` — re-applying the REAL
    per-hop projection twice (the Rust `Membrane::reshare`). And `reshareN` — the n-hop chain,
    folding `attenuate` down a list of per-hop keep-sets.
  * **`reshare_chain_attenuates` (KEYSTONE)** — `reshare A→B→C ⟹ C ⊆ B ⊆ A`: the conferred authority
    after two hops is `⊆` after one hop is `⊆` the original held authority. The chained lattice law,
    `attenuate_subset` lifted to composition by `List.Subset.trans`. The proof the membrane cannot
    amplify across reacquisitions — by the existing kernel theorem, transitively.
  * `reshareN_attenuates` — the n-hop generalization: ANY chain of membrane reshares confers a subset
    of the original held authority (induction over the hop list). No matter how many times a surface
    is re-shared, the last holder's authority is bounded by the first holder's. Confinement survives
    arbitrarily-long delegation chains.
  * `reshare_refuses_amplification` — the negative tooth: if a hop's keep-set requests an authority
    the prior hop did not hold, that authority is NOT in the reshared cap's conferred set (a widening
    is darkened, not granted). A reshare cannot manufacture an authority a prior holder lacked.

Discipline: axiom-clean (`#assert_all_clean` at the close). `lake build
Dregg2` green (LOCAL). NO core-`Auth`/`Cap` edit — every hop is the REAL `Dregg2.Exec.attenuate` and
every subset is the REAL `capAuthConferred` ⊆; the membrane is a NAMING of iterated kernel attenuation.
-/
import Dregg2.Exec.AuthTurn
import Dregg2.Deos.Surface
import Dregg2.Tactics

namespace Dregg2.Deos.Membrane

open Dregg2.Authority (Cap Auth Label capAuthConferred)
open Dregg2.Exec (attenuate attenuate_subset)

/-! ## §1 — A membrane hop is a kernel attenuation (the per-viewer projection).

A membrane mediates a reacquisition: holder A hands holder B a view of a surface, attenuated to what B
may see. That hop is EXACTLY `Dregg2.Exec.attenuate` — the per-viewer projection. We name it and
restate its non-amplification. -/

/-- **`hop keep cap`** — one membrane reacquisition: project `cap` to keep only `keep` (the per-viewer
attenuation the membrane applies at the boundary). A NAMING of `Dregg2.Exec.attenuate` — no new
projection algebra. -/
def hop (keep : List Auth) (cap : Cap) : Cap := attenuate keep cap

/-- **A SINGLE MEMBRANE HOP ATTENUATES** — the authority conferred after one membrane projection is a
SUBSET of the held authority. This IS `Dregg2.Exec.attenuate_subset`, restated as "one membrane
reacquisition cannot amplify". The base case of the chain. -/
theorem oneHop_attenuates (keep : List Auth) (cap : Cap) :
    capAuthConferred (hop keep cap) ⊆ capAuthConferred cap :=
  attenuate_subset keep cap

/-! ## §2 — `reshare A→B→C`: re-applying the per-hop projection (the Rust `Membrane::reshare`).

The membrane reshare composes attenuation across chained reacquisitions: A→B keeps `keepAB`, then
B→C keeps `keepBC`. That is `hop keepBC (hop keepAB cap)` — re-applying the REAL `is_attenuation`
per hop, exactly as `starbridge-web-surface`'s `Membrane::reshare` does. -/

/-- **`reshare keepAB keepBC cap`** — the A→B→C two-hop reshare: A holds `cap`, projects to B keeping
`keepAB`, B re-shares to C keeping `keepBC`. `hop keepBC (hop keepAB cap)`. The Rust `Membrane::reshare`
(re-applying the REAL per-hop projection). -/
def reshare (keepAB keepBC : List Auth) (cap : Cap) : Cap := hop keepBC (hop keepAB cap)

/-- **`reshareN keeps cap`** — the n-hop reshare chain: fold `hop` down a list of per-hop keep-sets
(head = the FIRST hop A→B, applied first). Models a surface re-shared through an arbitrary delegation
chain A→B→C→…→Z, each hop the membrane's per-viewer projection. -/
def reshareN : List (List Auth) → Cap → Cap
  | [],            cap => cap
  | keep :: rest,  cap => reshareN rest (hop keep cap)

/-! ## §3 — THE KEYSTONE: the membrane cannot amplify across hops.

`reshare A→B→C ⟹ C ⊆ B ⊆ A`. The conferred authority after two membrane hops is `⊆` after one hop is
`⊆` the original held authority — the chained lattice law, `attenuate_subset` lifted to composition by
`List.Subset.trans`. The proof the membrane cannot amplify across reacquisitions. -/

/-- **THE TWO-HOP NON-AMPLIFICATION KEYSTONE.** `reshare A→B→C` confers a SUBSET of A's held
authority: C's conferred authority ⊆ B's conferred authority ⊆ A's held authority. The membrane
re-applies the REAL per-hop `is_attenuation` (`attenuate_subset`) at each hop, and the two subset
facts compose by `List.Subset.trans` — so a reshared surface, two hops out, grants no more than the
original holder held. The `docs/deos/DEOS.md` target-2 statement, as a theorem. -/
theorem reshare_chain_attenuates (keepAB keepBC : List Auth) (cap : Cap) :
    capAuthConferred (reshare keepAB keepBC cap) ⊆ capAuthConferred cap := by
  -- C ⊆ B (second hop) and B ⊆ A (first hop); compose by transitivity of ⊆ on the conferred lists.
  have hBC : capAuthConferred (hop keepBC (hop keepAB cap)) ⊆ capAuthConferred (hop keepAB cap) :=
    oneHop_attenuates keepBC (hop keepAB cap)
  have hAB : capAuthConferred (hop keepAB cap) ⊆ capAuthConferred cap :=
    oneHop_attenuates keepAB cap
  exact List.Subset.trans hBC hAB

/-- **THE MIDDLE-HOLDER BOUND** (the `C ⊆ B` half, stated explicitly for the doc's "⊆ B's held"
clause). The reshared cap C confers a subset of what the MIDDLE holder B held — so even ignoring A, C
never exceeds its immediate grantor B. The membrane bounds each hop locally, not just end-to-end. -/
theorem reshare_bounded_by_middle (keepAB keepBC : List Auth) (cap : Cap) :
    capAuthConferred (reshare keepAB keepBC cap) ⊆ capAuthConferred (hop keepAB cap) :=
  oneHop_attenuates keepBC (hop keepAB cap)

/-- **THE n-HOP GENERALIZATION.** ANY chain of membrane reshares confers a subset of the original held
authority: `reshareN keeps cap ⊆ cap` for every hop-list `keeps`. By induction over the chain — each
hop attenuates (`oneHop_attenuates`) and the inductive hypothesis bounds the tail; `List.Subset.trans`
composes. So no matter how many times a surface is re-shared down a delegation chain, the last holder's
authority is bounded by the first holder's. Confinement survives arbitrarily-long reacquisition
chains. -/
theorem reshareN_attenuates (keeps : List (List Auth)) (cap : Cap) :
    capAuthConferred (reshareN keeps cap) ⊆ capAuthConferred cap := by
  induction keeps generalizing cap with
  | nil => exact fun a ha => ha          -- no hops: identity, conferred set unchanged
  | cons keep rest ih =>
    -- reshareN (keep :: rest) cap = reshareN rest (hop keep cap); tail bound ∘ one-hop bound.
    have htail : capAuthConferred (reshareN rest (hop keep cap)) ⊆ capAuthConferred (hop keep cap) :=
      ih (hop keep cap)
    have hhead : capAuthConferred (hop keep cap) ⊆ capAuthConferred cap :=
      oneHop_attenuates keep cap
    exact List.Subset.trans htail hhead

/-! ## §4 — THE NEGATIVE TOOTH: a reshare cannot manufacture an unheld authority.

A widening is DARKENED, not granted: if a hop requests (via `keep`) an authority the prior hop did not
hold, that authority is simply absent from the reshared cap's conferred set — `attenuate` filters it
out. So a reshare cannot grant an authority a prior holder lacked, even if the keep-set names it. -/

/-- **A RESHARE CANNOT GRANT AN UNHELD AUTHORITY** (the anti-amplification tooth). If `a` is NOT in
A's held authority, then `a` is NOT in the conferred authority of ANY reshare of A's cap (one hop or a
whole chain) — because every hop is `⊆`-bounded by A (`reshareN_attenuates`). So naming `a` in a
downstream keep-set does not conjure it: the membrane refuses to amplify into an authority no prior
holder had. -/
theorem reshare_refuses_amplification (keeps : List (List Auth)) (cap : Cap) (a : Auth)
    (hunheld : a ∉ capAuthConferred cap) :
    a ∉ capAuthConferred (reshareN keeps cap) := by
  intro hmem
  exact hunheld (reshareN_attenuates keeps cap hmem)

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the chain attenuation BITES, both polarities. -/

section Witnesses

open Dregg2.Deos.Surface (Surface interactiveSurface)

/-- A full interactive surface on cell `7`: holder A may write, read, and grant. -/
def egA : Cap := Surface 7 [Auth.write, Auth.read, Auth.grant]

-- A→B keeps {write, read} (drop grant); B→C keeps {read} (drop write). C ends VIEW-only.
def egC : Cap := reshare [Auth.write, Auth.read] [Auth.read] egA

-- The two-hop reshare attenuated to exactly [read]: C holds a view-only surface (chain shrank A→C):
#guard capAuthConferred egC == [Auth.read]
-- A held grant; C does NOT (the chain darkened it — amplification refused across hops):
#guard (Auth.grant ∈ capAuthConferred egA : Bool)
#guard !(Auth.grant ∈ capAuthConferred egC : Bool)
-- A held write; C does NOT (the second hop dropped it):
#guard !(Auth.write ∈ capAuthConferred egC : Bool)
-- a 4-hop chain keeping ever-less ends at most read-only; never grows back grant/write:
#guard capAuthConferred (reshareN [[Auth.write, Auth.read], [Auth.read], [Auth.read], [Auth.read]] egA)
        == [Auth.read]
#guard !(Auth.grant ∈ capAuthConferred
          (reshareN [[Auth.write, Auth.read], [Auth.read], [Auth.read]] egA) : Bool)
-- AMPLIFICATION REFUSED: a downstream hop naming `grant` (which the prior hop dropped) does NOT regrant
-- it — the reshared cap still lacks grant (the filter darkens an unheld request):
#guard !(Auth.grant ∈ capAuthConferred (reshare [Auth.read] [Auth.read, Auth.grant] egA) : Bool)
-- and an authority A NEVER held (`call`) is absent from any reshare, even if a keep-set names it:
#guard !(Auth.call ∈ capAuthConferred (reshareN [[Auth.call], [Auth.call]] egA) : Bool)

/-- **`reshareN_attenuates` NON-VACUITY (fires + is PROPER).** The `#guard`s above check the chain
computes; this is the NAMED, axiom-clean companion the non-vacuity meta-gate registers
(`docs/audit/NON-VACUITY-MANIFEST.md`). It USES `reshareN_attenuates` on a concrete two-hop chain
(so its `⊆` conclusion is exercised, not vacuous) AND witnesses the attenuation is STRICT: `grant`
is held by A upstream but DARKENED downstream — the subset is proper, so the theorem constrains
something. -/
theorem reshareN_attenuates_satisfiable :
    capAuthConferred (reshareN [[Auth.write, Auth.read], [Auth.read]] egA)
        ⊆ capAuthConferred egA
      ∧ Auth.grant ∈ capAuthConferred egA
      ∧ Auth.grant ∉ capAuthConferred (reshareN [[Auth.write, Auth.read], [Auth.read]] egA) :=
  ⟨reshareN_attenuates _ egA, by decide, by decide⟩

#assert_axioms reshareN_attenuates_satisfiable

end Witnesses

/-! ## §6 — THE UPWARD LEG: the conjunction forwarder (`cell/src/membrane.rs`).

§1–§5 are the DOWNWARD membrane: a reshare chain, iterated `attenuate` (descent), realized by
`starbridge-web-surface/src/rehydrate.rs`'s `Membrane::reshare`. The Rust HOUSE-CAPACITY
`cell/src/membrane.rs` is the DUAL — a 2-of-2 **conjunction forwarder**: it holds caps A and B and
exposes a new cap C exercisable only by presenting BOTH, whose authority floor is the **meet** of the
two held authorities (`compose_both = a.mask & b.mask`). Authority composes UPWARD through it, and the
non-amplification floor is `exposed ⊑ a & b`.

This is STILL the same lattice — `a & b` (effect-mask AND) is the MEET over the very `List Auth` /
`capAuthConferred ⊆` order the cap crown proves on. Over `List Auth` the meet is list intersection,
and "the meet is a lower bound" gives the floor by REUSE (`List.mem_of_mem_filter` + `Subset.trans`) —
no new lattice. This is the EXECUTOR-level rung of `cell/src/membrane.rs::is_non_amplifying`/`seal`
(`exposed ⊑ a & b`); the in-circuit / light-client witness is the named VK-affecting follow-up
(`metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md` membrane row), exactly as the downward leg's circuit
tooth is `cell/src/membrane.rs`'s own named shadow. -/

/-- **`compose a b`** — the conjunction forwarder's exposed-authority floor: the MEET of the two held
caps' conferred authorities (an authority survives only if BOTH held caps confer it). This IS the Rust
`compose_both`/`CompositionPolicy::BothOf::authority_bound` (`a.mask & b.mask`), with effect-mask AND
read as `List Auth` intersection. -/
def compose (a b : Cap) : List Auth :=
  (capAuthConferred a).filter (fun x => decide (x ∈ capAuthConferred b))

/-- The meet is bounded by the LEFT held cap (`a & b ⊑ a`). -/
theorem compose_subset_left (a b : Cap) : compose a b ⊆ capAuthConferred a := by
  intro x hx
  exact List.mem_of_mem_filter hx

/-- The meet is bounded by the RIGHT held cap (`a & b ⊑ b`). -/
theorem compose_subset_right (a b : Cap) : compose a b ⊆ capAuthConferred b := by
  intro x hx
  rw [compose, List.mem_filter] at hx
  exact of_decide_eq_true hx.2

/-- **THE CONJUNCTION-FORWARDER NON-AMPLIFICATION KEYSTONE** — the Rust `cell/src/membrane.rs` seal
floor `exposed ⊑ a & b`, as a theorem. A membrane whose exposed authority `C` is `⊆` the meet confers
NO more than EITHER held cap held: `exposed ⊆ a` AND `exposed ⊆ b`. So presenting C can never exercise
an authority a held cap lacked — the upward composition cannot amplify, by `Subset.trans` over the
SAME conferred-authority order the cap crown proves. -/
theorem membrane_non_amplifies (exposed : List Auth) (a b : Cap)
    (hseal : exposed ⊆ compose a b) :
    exposed ⊆ capAuthConferred a ∧ exposed ⊆ capAuthConferred b :=
  ⟨List.Subset.trans hseal (compose_subset_left a b),
   List.Subset.trans hseal (compose_subset_right a b)⟩

/-- **THE NEGATIVE TOOTH** (the Rust `forged_over_grant_is_rejected_at_seal` / the `a & b` darkening):
an authority a held cap LACKS is absent from the meet, so a SEALED membrane (`exposed ⊆ compose a b`)
cannot expose it — even if its claimed `exposed` names it. If `x ∉ a` (or `x ∉ b`), then `x ∉ exposed`.
A forwarder cannot manufacture an authority neither/either held cap carries. -/
theorem sealed_refuses_unheld (exposed : List Auth) (a b : Cap) (x : Auth)
    (hseal : exposed ⊆ compose a b) (hunheld : x ∉ capAuthConferred a) :
    x ∉ exposed :=
  fun hx => hunheld ((membrane_non_amplifies exposed a b hseal).1 hx)

/-! ## §7 — UPWARD-LEG NON-VACUITY TEETH (`#guard`): the conjunction floor BITES, both polarities. -/

section ForwarderWitnesses

open Dregg2.Deos.Surface (Surface)

/-- Held cap A on cell `5`: write, read, grant. -/
def fA : Cap := Surface 5 [Auth.write, Auth.read, Auth.grant]
/-- Held cap B on cell `5`: read, grant, call. -/
def fB : Cap := Surface 5 [Auth.read, Auth.grant, Auth.call]

-- THE MEET: only what BOTH hold (read, grant) — write (A-only) and call (B-only) are darkened.
#guard compose fA fB == [Auth.read, Auth.grant]
-- write ∈ A but ∉ the meet (B lacks it): the forwarder cannot expose an A-only authority.
#guard !(Auth.write ∈ compose fA fB : Bool)
-- call ∈ B but ∉ the meet (A lacks it): nor a B-only authority.
#guard !(Auth.call ∈ compose fA fB : Bool)
-- the MAXIMAL lawful membrane (exposes exactly the meet) seals:
#guard decide (([Auth.read, Auth.grant] : List Auth) ⊆ compose fA fB)
-- a SUB-floor exposed (less than the meet) also seals (you may forward narrower):
#guard decide (([Auth.read] : List Auth) ⊆ compose fA fB)
-- AMPLIFICATION REFUSED: a forged exposed naming `write` (A-only) is NOT ⊆ the meet — does not seal:
#guard !decide (([Auth.read, Auth.write] : List Auth) ⊆ compose fA fB)
-- and an authority NEITHER held cap carries (`reply`) does not seal either:
#guard !decide (([Auth.reply] : List Auth) ⊆ compose fA fB)

end ForwarderWitnesses

/-! ## §8 — Axiom hygiene. -/

#assert_all_clean [
  oneHop_attenuates,
  reshare_chain_attenuates,
  reshare_bounded_by_middle,
  reshareN_attenuates,
  reshare_refuses_amplification,
  compose_subset_left,
  compose_subset_right,
  membrane_non_amplifies,
  sealed_refuses_unheld
]

end Dregg2.Deos.Membrane
