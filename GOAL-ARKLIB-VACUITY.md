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

## ⚑ GOAL COMPLETE (end-to-end sound argument mechanized)

## Done-log
- ✅ **RED RESOLVED — capstone GREEN from my own fresh build** (raw output): all 11 modules exit 0 from FRESH oleans; #print axioms tSdh_ggm_sound/_lt_one/embed_noncollapsing = [propext,Classical.choice,Quot.sound], no sorryAx; statements non-vacuous. The RED was a STALE bare-import olean + a toolchain mismatch (v4.32 default vs v4.31 deps), NOT a source bug — codex's diagnosis confirmed. The comb's g₂-removal was FINE. REAL wound to fix before PR: the bare-import layout + unpinned lean-toolchain that let a stale artifact impersonate a broken proof.
- ⚠ **REGRESSION caught + fix in flight** (post-goal comb): the capstone was green + 3× verified at `e03adb630`, but the PR-polish comb `a8e55f8e7` dropped `g₂` from `embed` and reported GgmEndToEnd green WITHOUT rebuilding it — a phantom `g₂` binder left the capstone RED. The witness lane caught it (rebuilt downstream — the diligence the comb skipped). CODEX critical-review lane (RED-fix priority 1, guaranteed-green fallback to restore-g₂; codex empowered to change, lane verifies) in flight. LESSON: a polish commit that doesn't rebuild downstream can regress a verified capstone — the gold-standard verify must RE-RUN after each edit, not once.
- **PACKAGED + CLOSED** (`2e4b98329`): two-pager re-cut to the wired end-to-end theorem (side-conditions named, stale frontier text dropped), opened. Goal fully done + packaged: repair + tSdh_ggm_sound (3× independently verified) + both fork branches + the tweetable spread.
- **WIP refreshed + 3rd independent verify** (`emberian/ArkLib` kzg-vacuity-wip @ 347b9a93): all 14 modules build GREEN IN-TREE on the fork, tSdh_ggm_sound axioms=[propext,Classical.choice,Quot.sound] from the build log. Fix branch untouched; no PR. Third independent capstone build (lane overlay · gold-standard rebuild · fork in-tree).
- **gold-standard verify** (`8c54a2c65`): capstone REBUILDS GREEN from committed files in a fresh overlay — #print axioms tSdh_ggm_sound = [propext,Classical.choice,Quot.sound], full spine clean, no sorryAx/native_decide; ArkLib HardnessAssumptions unmodified @ d72f8392. PAPER.md §9 frontier→DONE. Finishing: re-cut two-pager + push WIP.
- ⚑⚑ **task E DONE — GOAL COMPLETE** (`e03adb630`): `tSdh_ggm_sound` — the CAPSTONE, over ArkLib's REAL `tSdhExperiment`, quantifying over `embed strat` (the construction, NOT all adversaries → escapes the vacuity), sorry-free/axiom-clean. Chain: C(experiment_eq_count)∘D(embed_det/correspondence)∘transport(winIndex)∘A(rand_encoding_bound_D)∘B(degree discharge on the REAL runTable). `tSdh_ggm_sound_lt_one` = genuine <1 (mutation-canaried). Sufficient-test PASSED: richly-inhabited, real target, no laundering. Side-conds: 1≤D, 2≤p, generator, ArkLib SampleableType, the <1 regime. **The vacuity repair + a complete end-to-end SOUND cryptographic argument: DONE.**
- **task D DONE** (`9c1aa7721`): the EMBEDDING — embed:Strat→real tSdhAdversary + embed_run_correspondence (mirrors real runAux; equality-query crux via real gpow_val_inj_iff), sorry-free/axiom-clean. Honest side cond 1≤D (D=0 genuinely false: no pairing). A+B+C+D ALL DONE → E now.
- **task B DONE** (`115099abe`): degree discharge on the REAL runTable (not the peer model) — hdeg_out/pairs/handles are now theorems; hypothesis-free _of_run corollaries for E; closes the peer-model gap. Only 1≤D/2≤p side conds.
- **task C DONE** (`eed762a00`): prob threading — game_collapse + experiment_eq_count (tSdhExperiment = winSet.card/(p−1)), sorry-free/axiom-clean vs real ArkLib; leaves the resultOf/hdet socket that D's embed fills.
- **task A DONE** (`f71c50f70`): linear-oracle refactor — Move.pair removed (never load-bearing), degree≤D structural, rand_encoding_bound_D added; 5 files green/sorry-free/axiom-clean. B now unblocked.
- vacuity finding mechanized (`KzgVacuity`, sorry-free, 3-way confirmed vs real ArkLib @ d72f8392)
- de-vacuation repair (`binding_reduces_to_tSdh` + `repair_survives_attack`) — DONE
- systemic finding (q-DLOG idiom + AGM stub vacuous too) mechanized
- static GGM bound `(D+1)/(p−1)` + adaptive GGM bound (identical-until-bad by induction) — sorry-free
- 3 residual-closers: quadratic random-encoding bound · degree invariant (peer model) · ArkLib transport
- Lean quality review — corpus A-grade, sorry-free, axiom-clean, one broken dup removed
- end-to-end architecture plan (`END-TO-END-PLAN.md`); δ=D + prob-threading-tractable findings
- packaging: two-pager PDF; `emberian/ArkLib` branches `kzg-binding-devacuation` (clean fix, 1 file)
  + `kzg-vacuity-wip` (full corpus, 10 modules build in-tree, 18 docs); no PR
