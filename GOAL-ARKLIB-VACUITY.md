# GOAL — ARKLIB-VACUITY: complete the vacuity repair + a complete end-to-end SOUND cryptographic argument

> ⚑ One of MANY live `/goal` lanes — see [`GOALS-INDEX.md`](GOALS-INDEX.md). This is the
> **arklib-vacuity** lane. Edit only this file; never clobber another lane's trail.

**Goal:** ArkLib (Ethereum-Foundation Lean crypto lib) KZG evaluation-binding was VACUOUS
(`tSdhAssumption` is `Classical.choice`-false at every parameter). The repair landed; now wire the
generic-group security bounds into ONE sound end-to-end theorem over ArkLib's *real* `tSdhExperiment`.

## Current thrust
Build the single target theorem (`docs/reference/arklib-kzg-vacuity/END-TO-END-PLAN.md`):
`tSdh_ggm_sound : ∀ strat, tSdhExperiment D (embed strat) ≤ (C(fuel+D+4,2)·D + (D+1))/(p−1)`
— "generic" = the *image of the embedding* (a construction, not a predicate), which is why it
escapes the vacuity. Architect's δ=D correction: ArkLib's adversary has NO pairing ⇒ degree ≤ D
(seed-max induction); prob-threading has VCVio + ArkLib `Binding.lean` precedent. ~1 focused week;
task D (the embedding) is the one genuinely-hard piece.

## Next 3 moves
1. **A** (linear-oracle refactor, drop `Move.pair`) + **C** (prob threading) + **D** (the embedding,
   long pole) — running in parallel.
2. **B** (degree discharge, seed-max induction) — fires when A lands.
3. **E** (compose `tSdh_ggm_sound`; apply the sufficient test to the FINAL theorem — no peer-model
   laundering into the socket) — fires when A,B,C,D land. Then re-cut the two-pager.

## Done-log
- vacuity finding mechanized (`KzgVacuity`, sorry-free, 3-way confirmed vs real ArkLib @ d72f8392)
- de-vacuation repair (`binding_reduces_to_tSdh` + `repair_survives_attack`) — DONE
- systemic finding (q-DLOG idiom + AGM stub vacuous too) mechanized
- static GGM bound `(D+1)/(p−1)` + adaptive GGM bound (identical-until-bad by induction) — sorry-free
- 3 residual-closers: quadratic random-encoding bound · degree invariant (peer model) · ArkLib transport
- Lean quality review — corpus A-grade, sorry-free, axiom-clean, one broken dup removed
- end-to-end architecture plan (`END-TO-END-PLAN.md`); δ=D + prob-threading-tractable findings
- packaging: two-pager PDF; `emberian/ArkLib` branches `kzg-binding-devacuation` (clean fix, 1 file)
  + `kzg-vacuity-wip` (full corpus, 10 modules build in-tree, 18 docs); no PR
