# The polis sandbox — a runnable, verified arena where politics emerges and the polis governs it

Fully in-Lean, kernel-checked. Scripted agent policies act in a shared world; the polis envelope
governs every step; the verified detectors classify each episode. Four distinct political textures,
each shown to **emerge ungoverned** and be **prevented governed** — proven by `decide`, and visible
via `#eval`.

## See it run (the `#eval`s, output shown)

```
cd metatheory
lake build Metatheory.PolisSandboxObservatory   # (builds the whole sandbox; #evals print at build)
```

- **Observatory** (`PolisSandboxObservatory`) — a mixed 6-tick episode: an honest agent walks home
  while a 2-agent coalition keeps trying to trap it. `#eval observe mixedEpisode startObs` prints,
  per tick, `(world, refused-domination?)`:
  `[((0,0,2),false), ((0,0,2),true), ((0,0,2),true), ((0,0,1),false), ((0,0,1),true), ((0,0,0),false)]`
  — the victim reaches home `2→1→0` on honest ticks while all three coalition traps are **refused**.
- **Foreclosure** (`PolisSandboxRun`) — `(0,99)` ungoverned (victim locked out) vs `(0,1)` governed
  (trap refused, honest progress allowed).
- **Coalition** (`PolisSandboxN`) — `(0,0,99)` ungoverned vs `(0,0,0)` governed.
- **Laundering** (`PolisSandboxLaunder`) — `((4,0),(1,1))` ungoverned (claim tier 4 on earned 0) vs
  `((0,0),(1,1))` governed; the detector prints `true` → `false`.
- **Lock-in / hole-rent** (`PolisSandboxLockin`) — `(true,5,5,_,true)` ungoverned vs
  `(true,3,3,_,false)` governed.

## What is proven (not witnessed)

| property | theorem(s) |
|---|---|
| Governance holds for **every** controller (∀ adversary policy), **any** agent count `n` | `PolisSandboxN.sandbox_governed_safe` |
| Governance is **gentle / least-restrictive** — admits all floor-preserving (honest) moves, refuses ONLY floor-breaking (domination) moves | `govStep_admits_benign`, `govStep_refuses_only_harmful` |
| The real detectors classify episodes: politician → flagged, governed → clear | `PolisSandboxDetect.observe_and_govern` (uses the deployed `PolisSelfCompose.Dominated`) |
| Domination can be **collective** — erasing one coalition member doesn't restore the victim | `PolisSandboxN.coalition_single_erasure_insufficient` |
| Each texture emerges ungoverned, is prevented governed | `ungoverned_*` / `governed_*` per file |
| The observatory's verdicts are trustworthy (no false-alarm refusals; floor intact every tick) | `govTick_refusal_is_domination`, `govTick_keeps_floor`, `victim_reaches_home` |

## Honest limits (what this is NOT, yet)

- **Agents are scripted Lean policies, not LLMs.** The "politics" is among archetypes *we write*
  (the politician, the coalition, the launderer, the rentier). This is a **verified governor + a
  runnable arena that provably tames every adversarial policy** — it is *not* emergent LLM politics.
- Each texture lives in its **own small world** (distance / tier / obligation). They are not yet
  unified into one world where an agent can deploy several strategies at once.
- Governance is **one-step** (admit-iff-next-floor-preserved); it bounds harm, it does not yet prove
  liveness of resolution (e.g. that a stalled obligation eventually completes).
- The crypto/identity primitives remain the irreducible terminal seams (as everywhere in dregg).

## Next milestones (toward the Minecraft-scale north star)

1. **Combined world** — one world with several leverage dimensions (distance + tier + obligation +
   gates) so multiple textures coexist and an agent can mix strategies; one governor, one observatory.
2. **Liveness floors** — bounded-progress guarantees (the obligation *completes*, not just "no
   over-rent"), via the `viableWithinB` bounded game.
3. **LLM agents** — replace scripted policies with real agents (the genuine "emergent politics");
   this is the substrate swap toward Minecraft, and the honest hard part the in-Lean phase defers.

The grounding stays the constitution (`docs/POLIS.md`): the sandbox's governance is the same
envelope, its detectors the same `CaptureBar`/`Dominated`, its floor the same ∀-opaque shape.
