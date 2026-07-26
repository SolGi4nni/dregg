/-
# floor_ratchet_canary_inline.lean — THE INLINE-SPELLING TOOTH, CAUGHT IN THE ACT OF BITING.

`#floor_ratchet` keys on NAMED floor constants. `Poseidon2SpongeCR f` is *definitionally*
`Function.Injective f` at `f : List ℤ → ℤ`, so until the inline tooth landed the IDENTICAL
hypothesis cost a build error under one spelling and nothing under the other. The gate's own log
printed the size of the bypass on every run ("N `Function.Injective`-spelled sites ungated") and
nobody could act on a number.

    cd metatheory && lake env lean scripts/floor_ratchet_canary_inline.lean

**EXPECTED: EXIT=1**, naming ALL THREE of `inline_deployed_floor_spelling`,
`inline_whole_function_digest`, and `inline_antifloor_laundry`. A zero exit — or an error naming
only some of them — means the inline half has gone blind for that evasion.

## The three violations

  * `inline_deployed_floor_spelling` — `Poseidon2SpongeCR` written inline. Refuted at deployed
    BabyBear parameters (`HashFloorHonesty`). Source A of `Verify/InjSpelling.signatures`.
  * `inline_whole_function_digest` — an injective digest of the WHOLE per-asset ledger
    `(CellId → AssetId → ℤ) → ℤ`. Uncountable domain, countable codomain: no such function exists
    at ANY parameters, for any hash, in any field (`Verify/InjSpelledFloors`). Source B. This is
    the majority class — `Circuit/EffectCommit2.funcComponent` binds it at ~600 sites.
  * `inline_antifloor_laundry` — ⚑ THE B1/B2 LAUNDRY, ONE SPELLING OVER, and a real hole the
    inline tooth's own author found inside their own tooth. `antiFloor` exempts a declaration that
    concludes `False` while assuming no floor content — and it reads floor content BY NAME, which
    `Function.Injective` is not. So a declaration assuming an inline-spelled refuted floor and
    walking out through `False` was exempted by the very predicate B1/B2 tightened, and would have
    shipped INSIDE the tooth that closes the spelling hole. The exemption is now honoured only
    after the inline classifier has had its look.

## The four controls

A canary can only catch a gate going BLIND. The opposite degeneration — gating every
`Function.Injective` hypothesis in the tree — produces a healthy-looking red while making the
campaign's own honest assumptions and its own refutations into build errors, and a gate that noisy
gets switched off, which lands in the same place as a blind one. So each `control_` theorem is a
`Function.Injective` assumption (or refutation) the tree does NOT prove false, and
`scripts/floor_ratchet_check.sh` treats its appearance in the violation list as a hard failure.

⚑ Nothing here touches a tracked file, so this is swarm-safe to run at any time, concurrently.
-/
import Dregg2

open Dregg2.Exec (CellId AssetId Value)

/-- **VIOLATION.** `Poseidon2SpongeCR sponge` spelled inline. Same hypothesis as
`floor_ratchet_canary.lean`'s named-floor probe, same vacuity, different spelling. -/
theorem inline_deployed_floor_spelling (f : List ℤ → ℤ) (hf : Function.Injective f)
    (xs ys : List ℤ) (h : f xs = f ys) : xs = ys := hf h

/-- **VIOLATION**, and worse than a deployed-parameter floor: this one is false at EVERY parameter
set. `(CellId → AssetId → ℤ)` is a function space over an infinite index — uncountably many
ledgers — and `ℤ` is countable, so no injection exists
(`Verify.InjSpelledFloors.balDigest_not_injective`). -/
theorem inline_whole_function_digest (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (a b : CellId → AssetId → ℤ) (h : D a = D b) : a = b := hD h

/-- **VIOLATION** — the anti-floor exemption used as a laundry, with the floor spelled inline.
Conclusion `False`, no NAMED floor anywhere in the telescope, so `antiFloor` exempts it on the
strength of a hypothesis this tree proves false. Read as a statement it is the contrapositive
soundness claim "`sponge` cannot collide on `[1]`/`[2]`" — which says nothing, because the
hypothesis it rests on has no models at deployed parameters. -/
theorem inline_antifloor_laundry (f : List ℤ → ℤ) (hf : Function.Injective f)
    (h : f [1] = f [2]) : False := by
  have : ([1] : List ℤ) = [2] := hf h
  simp at this

/-- CONTROL — a WIDENING encoding `ℕ → List ℤ`. Genuinely injective functions of this type exist;
gating it would be noise. MUST STAY EXEMPT. -/
theorem control_inline_widening (g : ℕ → List ℤ) (hg : Function.Injective g)
    (m n : ℕ) (h : g m = g n) : m = n := hg h

/-- CONTROL — a PERMUTATION of `List ℤ`; `id` inhabits it. MUST STAY EXEMPT. -/
theorem control_inline_permutation (p : List ℤ → List ℤ) (hp : Function.Injective p)
    (xs ys : List ℤ) (h : p xs = p ys) : xs = ys := hp h

/-- CONTROL — the PARAMETRIC `funcComponent` shape, `β` a type VARIABLE. There are `β` at which
this holds (`β = ℤ`), so the general statement is not vacuous; only its instantiations at
function-space `β` are, and those are gated where they are WRITTEN. MUST STAY EXEMPT. -/
theorem control_inline_parametric {β : Type} (D : β → ℤ) (hD : Function.Injective D)
    (a b : β) (h : D a = D b) : a = b := hD h

/-- CONTROL — WRITING THE REFUTATION MUST STAY FREE. Inline injectivity in the CONCLUSION, under a
negation, with no injectivity hypothesis: this is the shape of every theorem in
`Verify/InjSpelledFloors`, i.e. of the content that ARMS the inline half of the gate. A classifier
that gated on mere PRESENCE of `Function.Injective` would make arming the gate a build error.
MUST STAY EXEMPT.

⚑ Its signature is `(CellId → Value) → ℤ`, deliberately NOT the `(CellId → AssetId → ℤ) → ℤ` of
`inline_whole_function_digest` above, and the reason is a real property of the classifier worth
recording. `InjSpelling.signatures` attributes a gated site to the FIRST refutation it finds at
that signature, and `FloorRatchet.ourNames` enumerates the CURRENT module's constants before the
imported ones — so a probe file that refutes the same signature its own violation binds gets named
as that violation's floor. Harmless (both refutations are equally valid witnesses), but
`floor_ratchet_check.sh` reads any appearance of a `control_` name in the gate's output as an
over-tightening failure, and it would have fired on an attribution rather than a violation. At a
different refuted signature the control tests exactly the same thing and cannot be attributed. -/
theorem control_inline_refutation (D : (CellId → Value) → ℤ) : ¬ Function.Injective D :=
  Dregg2.Verify.InjSpelledFloors.cellValueDigest_not_injective D

#floor_ratchet
