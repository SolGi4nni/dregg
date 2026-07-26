# Orphan triage + axiom-pin migration pilot — measured, 2026-07-24

Scope: `metatheory/` build-artifact reclaim, the `Dregg2/**` orphan census, and a **measured
pilot** of the `#assert_axioms` → `#assert_namespace_axioms` migration. Every number here was
measured on this tree; nothing is estimated. Where a prior claim was wrong, the correction says so.

Owned by this pass: `scripts/check-lean-orphans.sh`, `scripts/lean-orphans-allow.txt`,
`metatheory/Dregg2/Exec/TurnExecutorFull.lean`, `metatheory/Dregg2/Exec/Program.lean`, this doc.

---

## 0. Two premises in the brief were WRONG — corrected before acting

**(a) The host.** This work was briefed as "on hbox". It cannot be. `hbox:~/dev/breadstuffs` is a
**different, unrelated lineage** — disjoint root commit (`db466dcd92` vs this tree's `4f736aa709`),
no `scripts/check-lean-orphans.sh`, no `scripts/lean-orphans-allow.txt`, no
`metatheory/docs/AXIOM-HYGIENE.md`, and it does not contain commit `d3c4ac853c`. Its `Claims.lean`
is a different file (543 lines / 206 pins vs 626 / 229 here). hbox's bare repo
(`~/dev/breadstuffs.git`) does not have this lineage either. **All work and all builds below were
therefore done on the Mac checkout `/Users/ember/dev/breadstuffs` (branch `main`), which is the tree
the brief actually describes.** Building "on hbox" would have measured different files.

**(b) The 192 MB orphan olean.** The brief said `Dregg2/Crypto/AcvpKats.olean` is 192 MB and orphaned
because `AcvpKats.lean` "was deleted by commit d3c4ac853c, renamed to CrateGeneratedKats.lean".
Half right. `d3c4ac853c` (2026-07-16) did **not** delete the file — it converted 10 `native_decide`
test-vector theorems to `#guard`. The `.lean` is nonetheless genuinely gone from this worktree and
the `.olean` was genuinely a 183.6 MiB dead artifact. Confirmed and deleted. (On hbox the 192 MB
olean is `CrateGeneratedKats.olean`, whose source **exists** — it is live there, not an orphan.)

---

## 1. Space reclaimed — 517.6 MiB (measured, `du -sk`)

Detection: for every `.olean` under `metatheory/.lake/build/lib/lean`, map back to its `.lean`
source; if the source no longer exists the module is dead, and so is every sibling artifact
(`.c`, `.ilean`, `.trace`, `.o`, `.hash`, `.setup.json`).

| | |
|---|---|
| total oleans before | 2132 (1901 live, **231 orphaned**) |
| orphan `.olean` bytes | 259.9 MiB |
| orphan artifacts, all extensions | 1993 files |
| `metatheory/.lake/build` before | 3,962,948 KB |
| `metatheory/.lake/build` after | 3,432,960 KB |
| **reclaimed** | **529,988 KB = 517.6 MiB** |
| largest single orphan | `Dregg2/Crypto/AcvpKats.olean`, 192,506,896 B (183.6 MiB) |

**Safety check run before deleting** (this is the part that matters): a stale `.olean` whose source
is gone can still *satisfy an `import`*, making a build green that should be red. I scanned every
in-tree `.lean` for imports of the 231 dead modules — **0 hits**, so no build was resting on one.
After deletion: 1900 oleans, **0 orphaned**, and `lake build Dregg2.Exec.TurnExecutorFull` →
`Build completed successfully (3028 jobs)`.

Honest caveats: (i) 1 live olean beyond the 231 was also removed by the second (multi-dot) sweep —
it is a rebuildable cache artifact, no source was touched, and `lake` regenerates it; I could not
pin down which. (ii) `.lake` is 4.2 G total, but 993 M of that is `packages/` (a symlink to a warm
mathlib) — the reclaimable surface was only ever the project's own `build/`.

---

## 2. The "several CARRY sorry" claim is FALSE — corrected in both files

`scripts/check-lean-orphans.sh` justified not globbing the `Dregg2` lib by saying the orphans
"several CARRY `sorry`", and `lean-orphans-allow.txt` repeated it. **Measured false.**

A comment-stripped token scan (block `/- -/` and line `--` comments removed first, because the
corpus is full of prose *asserting* sorry-freeness) finds:

- **0** real `sorry` tokens in the 123 allowlisted orphans;
- **0** real `sorry` tokens across **all 1730** `metatheory/Dregg2/**.lean`.

All 16 files that a naive `grep sorry` flags match only inside doc comments that say "no `sorry`".

The **real** reason not to glob is different and is now recorded in the header: ci.yml documents 28
`Circuit.Emit.*{Refine,Rung2}` modules that are **red at HEAD** — a Type mismatch that induces
`sorryAx` at *elaboration*, which is not a source `sorry` token, which is exactly why the textual
scan reads clean. Globbing would red the default build on those.

### Allowlist staleness fixed
The gate was failing on **28 stale entries** (23 modules that had been registered but never
de-listed, 5 naming files that no longer exist). All 28 removed; staleness is now **0**.

The gate still fails on **41 unlisted orphans** — and I deliberately did **not** silence that.
Auto-allowlisting 41 modules would destroy the one signal the gate exists to raise. They are
triaged below; adding them is the owning lane's call, with a reason each.

---

## 3. ★ The gate says "deliberate", not "checked" — 79 of 137 orphans are compiled by NOTHING

This is the finding with teeth. "Allowlisted" only records that an exclusion was *intentional*. It
says nothing about whether the module is verified anywhere. Cross-referencing the 137 orphans
against ci.yml's `AXIOM_GUARD_TARGETS`:

| | modules | theorems |
|---|---:|---:|
| orphan **and** covered by the CI orphan gate | 58 | 908 |
| orphan **and covered by nothing at all** | **79** | **1197** |

(20 names in `AXIOM_GUARD_TARGETS` are themselves stale — they are no longer orphans.)


---

## 4. ★ The axiom-pin migration pilot — the claim is TRUE per-file and UNSAFE as a mass rule

The claim under test (`metatheory/docs/AXIOM-HYGIENE.md`): `Trustline.lean` went 75 `#assert_axioms`
lines → 1 `#assert_namespace_axioms` pinning 108 theorems, i.e. **fewer lines AND more coverage**.
Corpus-wide there are ~16.7k `#assert_axioms` against only 90 `#assert_namespace_axioms`, so the
implied prize is large. I converted the top offenders and measured before/after.

### What `#assert_namespace_axioms NS` actually does
It walks the **whole environment** for theorems whose name has prefix `NS`. Three consequences that
decide every case below, and none of which are visible from the syntax:
1. it pins theorems from **other modules**, as long as they share the namespace prefix;
2. it pins **nothing** that lives outside the prefix, however loudly the old line pinned it;
3. it only sees what is **already elaborated where the command sits**.

### Results

| file | pins before | lines before → after | coverage before → after | verdict |
|---|---:|---|---|---|
| `Exec/TurnExecutorFull.lean` | 128 | 838 → 735 | 128 → **295** (2.30×) | ✅ **converted, green** |
| `Exec/Program.lean` | 85 | 2567 → 2501 | 85 → **316** (3.72×) | ✅ **converted, green** |
| `Claims.lean` | 229 | — | 229 → **0** | ⛔ **REFUSED — would destroy all 229** |
| `AssuranceCase.lean` | 110 | — | 110 → 11 | ⛔ **REFUSED — would drop 99** |
| `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean` | 118 | — | — | ⏸ not attempted (another lane's area) |

Build evidence, my hand, this tree:
```
info: Dregg2/Exec/TurnExecutorFull.lean:736:0: #assert_namespace_axioms
      Dregg2.Exec.TurnExecutorFull: 293 theorems pinned kernel-clean
Build completed successfully (3028 jobs).

info: Dregg2/Exec/Program.lean:2498:0: #assert_namespace_axioms
      Dregg2.Exec: 316 theorems pinned kernel-clean
Build completed successfully (713 jobs).
```
`TurnExecutorFull` = 293 from the namespace pin **+ 2 explicit pins deliberately retained** = 295.

### ★ Three ways a mechanical migration silently LOSES coverage

**(1) Pins that resolved through `open` are not in the namespace.** In `TurnExecutorFull.lean`,
**2 of the 128** pins — `recTotalAsset_insert_fresh`, `createCellIntoAsset_grows_accounts` — are
`Dregg2.Exec.*`, not `Dregg2.Exec.TurnExecutorFull.*`. They only looked local because of an
`open Dregg2.Exec` at the top of the file. The namespace pin does **not** cover them. A
delete-all-pins-add-one-line script drops them, and **nothing goes red**. I kept them explicitly.

**(2) Placement silently truncates coverage.** `#assert_namespace_axioms` only sees what is already
elaborated. Measured directly: placed at the top of §11 it reported **292**; moved to the end of the
same unchanged file it reports **293** — it had been silently missing the file's own
`fullActionInvA_nonvacuous`. In a file where pins are interleaved with theorems (the normal shape),
a mid-file namespace pin under-covers by however much follows it, with no diagnostic.

**(3) Coverage is a property of the import graph, not of the file.** The same command
`#assert_namespace_axioms Dregg2.Exec` reported **316** when only `Exec/Program` was imported and
**958** when `Exec/TurnExecutorFull` was imported too. So a namespace pin's strength silently
changes when an unrelated import is added or removed. A per-theorem pin fails **loudly**
(`unknown constant`) when its subject disappears; a namespace pin just quietly covers one fewer.
**Coverage count goes up; tripwire sharpness goes down.** For `TurnExecutorFull` — where all 128
pins name theorems defined in *other* modules — that trade is real, and it is recorded in the file.

### ⛔ The two biggest offenders are structurally NON-migratable

This is the part that blocks a mass migration, and it is not a corner case — it is the **two largest
pin files in the corpus**.

- **`Claims.lean` — 229 pins, would become 0.** The file declares **zero** theorems. It is the
  deliberate *corpus-wide pin net*: it imports the `Dregg2` root and re-pins keystones from **40
  different namespaces** (`Dregg2.Spec.*`, `Dregg2.Proof.*`, `Dregg2.Crypto.*`, …). Its own
  namespace `Dregg2.Claims` is empty, so `#assert_namespace_axioms Dregg2.Claims` pins **nothing**.
  Migrating it would delete 229 kernel-clean certifications and still build green. The file's own
  header warns that ~190 of those pins are the *unique* location of those certifications.
- **`AssuranceCase.lean` — 110 pins, 99 of them cross-namespace.** Same shape: an apex file that
  pins keystones across 24 namespaces. A namespace pin would retain only its 11 local theorems.

`Trustline.lean` and `Biorthogonality.lean` — the two files the doc generalizes from — are
self-contained modules that pin their own theorems. The top corpus offenders are the **opposite**
kind of file, and the offender ranking is dominated by them precisely *because* aggregator files
accumulate pins. **The metric "most `#assert_axioms` lines" selects for exactly the files where the
migration is least safe.**

### Is a mass migration safe? **No.**

Not as a mechanical pass over 1260 files. It is safe **per-file, after checking** that: every
existing pin resolves under the target namespace (not via `open`); the namespace is the file's own
and not a broad shared one; the command goes last; and the file's pins are local rather than remote.
Two of the top five failed that check outright. In a shared repo it is also a merge-conflict bomb.

Worth doing as a **guarded, incremental** pass: a script that proposes a conversion only when it can
prove `explicit_pins ⊆ namespace_theorems`, refuses otherwise, and is reviewed per file. The
`Dregg2.Claims` net should be left exactly as it is — permanently.

---

## 5. The orphan triage — 137 modules, five buckets

Buckets are assigned from measured signals: CI coverage, ci.yml's documented red cluster, theorem count, and `native_decide` use. No module was deleted; this is the triage list only.

### A — CI-COVERED ORPHAN (keep allowlisted; genuinely deliberate)

**58 modules, 908 theorems.** Built by ci.yml `AXIOM_GUARD_TARGETS` "Orphan gate". Outside the default `lake build`, but the sorry/axiom net DOES run on them. **Verdict: genuinely-WIP, correctly excluded.**

| module | thms | allowlisted |
|---|---:|---|
| `Dregg2.Apps.ColonistJob` | 7 | yes |
| `Dregg2.Bridge.HoldingWeightedTally` | 21 | yes |
| `Dregg2.Bridge.LightClientEth` | 28 | yes |
| `Dregg2.Bridge.LightClientMpt` | 21 | yes |
| `Dregg2.Bridge.LightClientTendermint` | 22 | yes |
| `Dregg2.Bridge.VerifiedLightClient` | 17 | yes |
| `Dregg2.Circuit.AcceptanceDischarge` | 26 | yes |
| `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree` | 62 | yes |
| `Dregg2.Circuit.AlgoStarkSoundFanoutMemory` | 22 | yes |
| `Dregg2.Circuit.AlgoStarkSoundFanoutSetField` | 32 | yes |
| `Dregg2.Circuit.AlgoStarkSoundKernel` | 53 | yes |
| `Dregg2.Circuit.AlgoStarkSoundKernelAvail` | 6 | yes |
| `Dregg2.Circuit.BlindedMembershipBindingFromFold` | 10 | yes |
| `Dregg2.Circuit.CustomLeafEncoding` | 6 | yes |
| `Dregg2.Circuit.Emit.AdjacencyMembershipRefine` | 21 | yes |
| `Dregg2.Circuit.Emit.AdjacencyMembershipRefineAudit` | 0 | yes |
| `Dregg2.Circuit.Emit.AdjacencyMembershipRung2` | 28 | yes |
| `Dregg2.Circuit.Emit.AvailWideMembersNarrow` | 13 | yes |
| `Dregg2.Circuit.Emit.BlindedMembershipRung2` | 28 | yes |
| `Dregg2.Circuit.Emit.BoundPresentationRefine` | 14 | yes |
| `Dregg2.Circuit.Emit.BoundPresentationRung2` | 14 | yes |
| `Dregg2.Circuit.Emit.CommittedThresholdEmit` | 2 | yes |
| `Dregg2.Circuit.Emit.CommittedThresholdRefine` | 29 | yes |
| `Dregg2.Circuit.Emit.DerivationRefine` | 34 | yes |
| `Dregg2.Circuit.Emit.DfaRoutingGeneralEmit` | 3 | yes |
| `Dregg2.Circuit.Emit.DfaRoutingRefine` | 36 | yes |
| `Dregg2.Circuit.Emit.DfaRoutingRung2` | 23 | yes |
| `Dregg2.Circuit.Emit.EffectActionBindingEmit` | 5 | yes |
| `Dregg2.Circuit.Emit.EffectActionBindingRefine` | 38 | yes |
| `Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransition` | 3 | yes |
| `Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRefine` | 24 | yes |
| `Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRung2` | 21 | yes |
| `Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRung2Full` | 4 | yes |
| `Dregg2.Circuit.Emit.EmitGraduate` | 0 | yes |
| `Dregg2.Circuit.Emit.FoldEmit` | 7 | yes |
| `Dregg2.Circuit.Emit.FoldRefine` | 19 | yes |
| `Dregg2.Circuit.Emit.FoldRung2` | 16 | yes |
| `Dregg2.Circuit.Emit.MembershipAuthRootEdge` | 2 | yes |
| `Dregg2.Circuit.Emit.MembershipDepthGeneralRung2` | 13 | yes |
| `Dregg2.Circuit.Emit.MultiStepChainEmit` | 1 | yes |
| `Dregg2.Circuit.FinBindsKernel` | 9 | yes |
| `Dregg2.Circuit.FinInjectivityCollapse` | 6 | yes |
| `Dregg2.Circuit.FriCorrelatedAgreementSharp` | 29 | yes |
| `Dregg2.Circuit.FriLdtJohnsonList` | 8 | yes |
| `Dregg2.Circuit.FriProximityGapListDecoding` | 4 | yes |
| `Dregg2.Circuit.FriProximityGapWitness` | 24 | yes |
| `Dregg2.Circuit.FriVerifierOracle` | 17 | yes |
| `Dregg2.Circuit.KernelConfigSoundness` | 1 | yes |
| `Dregg2.Circuit.KernelConfigSoundnessAvail` | 1 | yes |
| `Dregg2.Circuit.RotatedKernelRefinementAvailWideNarrow` | 24 | yes |
| `Dregg2.Circuit.WrapSafetyStaticAnalyzer` | 9 | yes |
| `Dregg2.Exec.FFIDirect` | 0 | yes |
| `Dregg2.Games.AutomataflAir` | 12 | yes |
| `Dregg2.Games.MultiwayTug` | 20 | yes |
| `Dregg2.Games.MultiwayTugAir` | 13 | yes |
| `Dregg2.Verify.LoadBearingAuditBroad` | 0 | yes |
| `Dregg2.Verify.LoadBearingAuditKey` | 0 | yes |
| `Dregg2.Verify.LoadBearingLint` | 0 | yes |

### B — DARK + RED-AT-HEAD (genuinely WIP, blocked)

**14 modules, 226 theorems.** Compiled by NOTHING, and ci.yml documents this cluster as red at HEAD (a Type mismatch that induces `sorryAx` at elaboration). **Verdict: genuinely-WIP. Repair, then register. Do NOT add to the orphan gate while red.**

| module | thms | allowlisted |
|---|---:|---|
| `Dregg2.Circuit.DeltaProto` | 8 | yes |
| `Dregg2.Circuit.EffectsAsDataProto` | 6 | yes |
| `Dregg2.Circuit.Emit.BridgeActionRefine` | 19 | yes |
| `Dregg2.Circuit.Emit.DerivationRung2` | 23 | yes |
| `Dregg2.Circuit.Emit.EffectActionBindingRung2` | 5 | yes |
| `Dregg2.Circuit.Emit.MerkleMembershipRung2` | 13 | yes |
| `Dregg2.Circuit.Emit.MultiStepChainRefine` | 16 | yes |
| `Dregg2.Circuit.Emit.NoteSpendingLeafRefine` | 24 | yes |
| `Dregg2.Circuit.Emit.NoteSpendingLeafRung2` | 29 | yes |
| `Dregg2.Circuit.Emit.PredicatesNeqRefine` | 21 | yes |
| `Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2` | 10 | yes |
| `Dregg2.Circuit.Emit.PredicatesRelationalCompoundRung2Full` | 14 | yes |
| `Dregg2.Circuit.Emit.QuantifiedAbsenceRefine` | 17 | yes |
| `Dregg2.Circuit.Emit.TemporalPredicateRefine` | 21 | yes |

### C — DARK + GREEN ★ SHOULD BE REGISTERED

**39 modules, 724 theorems.** Real theorems, self-checked, no source `sorry`, no `native_decide`, not in the red cluster — and compiled by NO CI target at all. **Verdict: should-be-registered (or at minimum added to `AXIOM_GUARD_TARGETS`). This is the actionable bucket.**

| module | thms | allowlisted |
|---|---:|---|
| `Dregg2.Circuit.Emit.AttestedFactMembershipEmit` | 2 | yes |
| `Dregg2.Circuit.Emit.AttestedFactsRootModel` | 3 | **NO (gate is red on it)** |
| `Dregg2.Circuit.Emit.BridgeActionEmit` | 1 | yes |
| `Dregg2.Circuit.Emit.DerivationEmit` | 1 | yes |
| `Dregg2.Circuit.Emit.DfaRoutingEmit` | 3 | yes |
| `Dregg2.Circuit.Emit.DfaRoutingTableEmit` | 28 | **NO (gate is red on it)** |
| `Dregg2.Circuit.Emit.GuardedHidingSpanGuardWeld` | 27 | **NO (gate is red on it)** |
| `Dregg2.Circuit.Emit.GuardedHidingSpanRefine` | 7 | **NO (gate is red on it)** |
| `Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit` | 4 | **NO (gate is red on it)** |
| `Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine` | 22 | **NO (gate is red on it)** |
| `Dregg2.Circuit.Emit.NoteSpendingLeafEmit` | 3 | yes |
| `Dregg2.Circuit.Emit.PredicatesNeqEmit` | 3 | yes |
| `Dregg2.Circuit.Emit.QuantifiedAbsenceEmit` | 3 | yes |
| `Dregg2.Circuit.Emit.TemporalPredicateEmit` | 3 | yes |
| `Dregg2.Circuit.FriIncidenceDesign` | 7 | **NO (gate is red on it)** |
| `Dregg2.Circuit.MapAbsentImtGateWide` | 31 | **NO (gate is red on it)** |
| `Dregg2.Circuit.PeepholeBilinear` | 4 | **NO (gate is red on it)** |
| `Dregg2.Circuit.PeepholeDeployedShape` | 59 | **NO (gate is red on it)** |
| `Dregg2.Circuit.PeepholeParityMeasurement` | 21 | **NO (gate is red on it)** |
| `Dregg2.Circuit.PeepholeZeroTestElision` | 4 | **NO (gate is red on it)** |
| `Dregg2.Crypto.BindingSurvivesSimulation` | 8 | **NO (gate is red on it)** |
| `Dregg2.Crypto.Fips204ChallengeHash` | 5 | **NO (gate is red on it)** |
| `Dregg2.Crypto.Keccak.Fips202Lfsr` | 5 | **NO (gate is red on it)** |
| `Dregg2.Crypto.Keccak.Fips202Refine` | 8 | **NO (gate is red on it)** |
| `Dregg2.Crypto.Keccak.Fips202Round` | 24 | **NO (gate is red on it)** |
| `Dregg2.Crypto.Keccak.Fips202Sponge` | 13 | **NO (gate is red on it)** |
| `Dregg2.Crypto.Keccak.Fips202SpongeRefine` | 34 | **NO (gate is red on it)** |
| `Dregg2.Crypto.KemSoundnessQuant` | 9 | yes |
| `Dregg2.Crypto.MlKemKeygenRefine` | 34 | **NO (gate is red on it)** |
| `Dregg2.Crypto.NttFaithful` | 159 | yes |
| `Dregg2.Crypto.PolyTimeRomBridge` | 25 | **NO (gate is red on it)** |
| `Dregg2.Crypto.SpongeCarrierBridge` | 4 | **NO (gate is red on it)** |
| `Dregg2.Crypto.VerifyCoreEqSpec` | 42 | yes |
| `Dregg2.Crypto.VerifyCoreEqSpecW` | 20 | yes |
| `Dregg2.Crypto.VerifyCoreUseHint` | 9 | **NO (gate is red on it)** |
| `Dregg2.Games.MultiwayTugProgram` | 30 | yes |
| `Dregg2.Metatheory.TypedLinearPredicateOptimizedWiring` | 23 | **NO (gate is red on it)** |
| `Dregg2.Metatheory.TypedLinearPredicateOptimizerCost` | 16 | **NO (gate is red on it)** |
| `Dregg2.Verify.ExistsImageVacuity` | 20 | **NO (gate is red on it)** |

### D — DARK + zero-theorem (harness / data / aggregator)

**11 modules, 0 theorems.** Declares no theorem: KAT data, JSON emitters, `#guard` drivers, or pin-nets. Registering adds no proof coverage. **Verdict: keep out of the default build; delete only the ones whose driver role is dead (owner call).**

| module | thms | allowlisted |
|---|---:|---|
| `Dregg2.Circuit.Emit.AutomataflNGenGolden` | 0 | **NO (gate is red on it)** |
| `Dregg2.Circuit.Emit.EmitAllJson` | 0 | yes |
| `Dregg2.Circuit.Emit.GuardedHidingSpanEmit` | 0 | **NO (gate is red on it)** |
| `Dregg2.Claims` | 0 | yes |
| `Dregg2.Crypto.AcvpHex` | 0 | **NO (gate is red on it)** |
| `Dregg2.Crypto.CrateGeneratedKats` | 0 | **NO (gate is red on it)** |
| `Dregg2.Crypto.CryptoVerifyAll` | 0 | yes |
| `Dregg2.Crypto.Keccak.Fips202Spec` | 0 | **NO (gate is red on it)** |
| `Dregg2.Crypto.MlDsaKeygen` | 0 | **NO (gate is red on it)** |
| `Dregg2.Crypto.MlKemKeygen` | 0 | **NO (gate is red on it)** |
| `Dregg2.Games.AutomataflDifferential` | 0 | **NO (gate is red on it)** |

### E — DARK + `native_decide` (cannot be kernel-clean)

**15 modules, 247 theorems.** Uses `native_decide` → `Lean.ofReduceBool`, so it can never pass the kernel-clean net unqualified. **Verdict: genuinely-WIP/by-design-excluded; if registered it needs an `except` clause with justification.**

| module | thms | allowlisted |
|---|---:|---|
| `Dregg2.Crypto.CodecRoundTrip` | 22 | yes |
| `Dregg2.Crypto.EncapsCoreSpec` | 19 | yes |
| `Dregg2.Crypto.KeccakCavp` | 35 | **NO (gate is red on it)** |
| `Dregg2.Crypto.MlDsaHintCodec` | 41 | yes |
| `Dregg2.Crypto.MlDsaKeygenAcvp` | 4 | **NO (gate is red on it)** |
| `Dregg2.Crypto.MlDsaKeygenRefine` | 87 | **NO (gate is red on it)** |
| `Dregg2.Crypto.MlDsaSigCodecClosed` | 3 | yes |
| `Dregg2.Crypto.MlDsaSigGenAcvp` | 2 | **NO (gate is red on it)** |
| `Dregg2.Crypto.MlDsaSigVerAcvp` | 1 | **NO (gate is red on it)** |
| `Dregg2.Crypto.MlDsaSignReal` | 4 | yes |
| `Dregg2.Crypto.MlKemEncapsAcvp` | 2 | **NO (gate is red on it)** |
| `Dregg2.Crypto.MlKemKeygenAcvp` | 3 | **NO (gate is red on it)** |
| `Dregg2.Crypto.SignCoreSpec` | 7 | yes |
| `Dregg2.Crypto.VerifyCoreHashFrame` | 10 | **NO (gate is red on it)** |
| `Dregg2.Crypto.VerifyCoreSpec` | 7 | yes |
