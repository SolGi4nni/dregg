# Claims ledger — what we can honestly stand behind, per theorem

**Date:** 2026-07-26. **Subject:** the 121 assurance-shaped carriers in the laundered-claims sweep,
plus 2 that the sweep missed. **Measured on:** a clean `git archive` export of `e0160d116f68de95a48204f78e818a31eb8ee793`.

This is a **citation ledger**, not a proof audit. It answers one question per theorem: *if someone
quotes this as evidence that dregg is verified, are they saying something true about the deployed
system?* For most of them the answer is no, and the reason is uniform — the theorem is true, and
its hypothesis is false at the parameters we ship.

> A theorem that reads as a deployed safety guarantee but is vacuous is worse than no theorem,
> because it reads as assurance. Everything below is written so that a reader who quotes a row
> cannot accidentally overclaim.

---

## How to read a verdict

| Verdict | Meaning |
|---|---|
| **CITABLE** | Quote it, within the stated scope. Its content survives at deployed parameters. Several of these are *wound reports* — citable as "here is what is broken", never as assurance. |
| **RE-GROUND** | The claim is real; the floor under it is refuted; a specific repair is named. **Do not cite until the repair lands.** Where the replacement already exists in-tree, the row names it — that one *is* citable today. |
| **DO-NOT-CITE** | Vacuous. The one-line honest restatement is given. Nothing to salvage as stated; the row says delete, restate, or leave it as a record. |

⚑ **A false CITABLE is the worst defect this document can carry** — it licenses quoting a vacuous
guarantee. The check that catches it is mechanical, and §4 states it: **for each hypothesis, ask whether
it is refuted _at the instantiation the theorem actually uses_.** `Poseidon2SpongeCR hash` at a bound
variable is parametric and may be fine; `Poseidon2SpongeCR poseidon2Hash` at the deployed constant is a
closed proposition the tree refutes, and any theorem carrying it is vacuous. Run that check on every row
added here.

A note on what "vacuous" means here, because two different strengths appear:

* **∅-ALWAYS** — the hypothesis is false *for every choice of parameters*, by cardinality. No
  widening, no re-parameterisation, no future primitive makes it true. There is no world in which
  the theorem applies.
* **∅-DEPLOYED** — the hypothesis is satisfiable in principle (an idealised injective primitive)
  but provably false at BabyBear / at a compressing lattice map. The theorem is a true statement
  about an object we do not run.

∅-ALWAYS is strictly worse and is ranked first.

---

## Measurement provenance

⛑ **RE-VERIFIED 2026-07-26 against `00ca2a8a4`** (audit of the CITABLE tier + every coordinate in the
document). **All line numbers below are HEAD-`00ca2a8a4` coordinates**, mechanically checked
declaration-by-declaration; **14 were stale** and are corrected. Two verdicts changed (#42, #43) and one
row was added (#47) — each change is annotated in place. Every file this audit re-read was byte-identical
between HEAD and the working tree at the time. No Lean was modified.

* Clean export: `git archive e0160d116` → statements read from the export, never the working tree.
* All **50** distinct source files carrying these claims are **byte-identical** between HEAD and the
  working tree (md5, 50 compared / 0 differ), so this ledger is simultaneously true of both today.
* Ruler check: `metatheory/Dregg2/Verify/FloorRatchet.lean` md5 `090de9a7239cbfed260dd889338212a8`
  in both trees.
* No Lean was modified for this ledger. The root build and the `floor-ratchet` emission are untouched.
* Blast radius = in-tree modules that reference the name, **excluding** the ratchet's own bookkeeping
  (`FloorRatchetBaseline`, `FloorRatchetSpecimens`, `Dregg2.lean`, the canary scripts). Those
  references are the gate recording the carrier, not a consumer depending on it.

**Coverage reconciliation — every row is accounted for, none is dropped.**

| Section | Rows |
|---|---|
| §1 Tier 0 — ∅-ALWAYS | 17 |
| §2 Tier 1 — crypto assurance | 13 (11 from the sweep + the 2 exempt Hermine claims) |
| §3 Tier 2 — ∅-DEPLOYED CR family | 85 (§3.1 = 8, §3.2 = 14 + 28 + 20 + 13 + 2 = 77) |
| §4 audited-as-CITABLE | 9 (8 original + #47, added by the 2026-07-26 audit) |
| **Total** | **124 = 121 swept + 2 exempt + 1 added** |

The assurance-shaped set the brief asked to cover completely — consensus, fork, forgery, downgrade,
omission — is §2 in full (all 13) plus the omission rows (`Deos/CapacityCarrier` ×2,
`Lightclient/NonOmissionAttack`) and the market/replay/freshness rows in §1. Nothing in that set is
deferred.

---

## The four floors, and exactly how each is refuted

| Floor | Definition | Refuted by | Strength |
|---|---|---|---|
| `Circuit.RestFrameCardinalityFloor` → `RestHashIffFrame RH` | a rest-hash `RecordKernelState → ℤ` separating kernels that differ in `bal : CellId → AssetId → ℤ` | `restHashIffFrame_false_by_cardinality` — composing with the `Set ℕ`-indexed ledger family gives an injection `Set ℕ → ℕ`; `Function.cantor_injective` | **∅-ALWAYS.** Not a width problem: `restHashIffFrame_false_at_babyBear` discharges the range bound and *never uses it*. |
| `Poseidon2Binding.Poseidon2SpongeCR h` (≡ `StateCommit.compressNInjective`, ≡ `InAirAuthorityDigestGadget.FloorDigestBinds`) | `∀ xs ys, h xs = h ys → xs = ys` on the infinite `List ℤ` | `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` — a sponge landing in `[0, 2013265921)` has finite range, so it is non-injective | **∅-DEPLOYED.** Every real Poseidon2 `hash_many` is exactly such a sponge. |
| `Lattice.MSISHard A β` | `¬ ∃ z, IsMSISSolution A β z` | `CryptoFloorTeeth.not_msisHard_of_short_ball` — pigeonhole: if the β₀-short ball outnumbers the codomain, two elements collide and their difference is a short nonzero kernel vector | **∅-DEPLOYED at any compressing `A`.** ⚑ The *instantiated* refutation in-tree is `not_msisHard_augmented_id`, at `[id \| 1]` over `ZMod 5` — a toy, despite `deployed_boolean_floor_refuted`'s name. The counting fact at real ML-DSA parameters is **not discharged in-tree**. |
| `SchnorrEufCma.SchnorrDLHardF g` | `¬ ∃ dlog : G → S, ∀ P, (dlog P) • g = P` | in-tree only at the ℚ toy (`ex_dl_not_hard`) | **DEGENERATE, direction unresolved** — see §2.2. Its truth value is decided by *surjectivity of `s ↦ s • g`*, a modelling artifact, in both directions. It never tracks hardness. |

`Compress8CR` and `Compress1CR` are the same disease at a wider digest: their domain is still the
infinite `List ℤ`, so widening the codomain from 1 felt to 8 does not make them true. The repair for
that whole family is a *game* floor, not a wider digest.

---

## §0 — The three things to fix first

1. **`CommitSurface` has no inhabitant at all.** Its fifth field is `restFrame : RestHashIffFrame RH`,
   refuted unconditionally by Cantor. `metatheory/Dregg2/Circuit/TurnDecodeChainLogBundleCutoverCheck.lean:306`
   discharges the consequence as an `example (S : CommitSurface) : False`. **Every theorem in this
   tree quantified over a `CommitSurface` is vacuous today, for all parameters** — the gate's own
   note puts that at **409 declarations** (431 `S : CommitSurface` binder sites across 99 files).
   Seventeen of the rows below are in that set, including the market boundary tooth and the whole
   replay/freshness family. **This is the single highest-leverage repair in the ledger** and it is
   structural, not cryptographic: split `CommitSurface` into the five *primitives* and a separate CR
   record, and re-parameterise. Most of the theorems survive verbatim, because their proofs use
   `S.commit` and the chain fields, not the CR fields.

2. **Two blindness controls are themselves blind.** `LightClientFusion.dProduced_not_vacuous` and
   `dProduced_false_everywhere` exist to prove the fusion's premise is not identically `True`. Both
   take `(S : CommitSurface)`. A non-vacuity control that is vacuous certifies nothing, and its green
   is what stopped anyone looking. Same shape at `StateCommitReduce.surface_no_stateBreak`, which is
   described in its own doc-comment as the *one* place the layer's hypotheses were consumed — that
   one place is empty.

3. **`closedLogExtract_emptyTag_false` sheds the wrong floor.** Its 2026-07-25 doc-comment celebrates
   dropping `Poseidon2SpongeCR` because "a refutation resting on a false hypothesis would have proved
   nothing" — while the theorem still carries `RestHashIffFrame` through the `Slive` abbreviation, and
   that one is false *unconditionally*, which is strictly worse. The sentence was right; it was
   pointed at the smaller of the two problems.

---

## §1 — Tier 0: ∅-ALWAYS (17 rows). Vacuous at every parameter, forever.

Sorted by blast radius. `dep` = in-tree consumer modules (ratchet bookkeeping excluded).

| # | Claim | dep | Verdict | Honest restatement / repair |
|---|---|---|---|---|
| 1 | `metatheory/Dregg2/Circuit/CircuitSoundness.lean:1177` `turnDecodeChainLog_rejects_forged_log` | 2 | RE-GROUND | Reads as "the published turn-chain binds the intermediate receipt-log". Says: *if a commitment surface existed (none does), a forged seam would be unsat.* Repair: split `CommitSurface`; the seam argument is `logPubSeam` + `logDecode`, structural. |
| 2 | `metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:177` `replay_rejected_after_apply` | 2 | RE-GROUND | "A replayed proof is rejected after the anchor advances." The proof is commitment-advancement, not CR — it needs the five primitives, not the five injectivity fields. Survives the split verbatim. |
| 3 | `metatheory/Dregg2/Circuit/Freshness.lean:137` `replay_rejected_after_apply` | 2 | RE-GROUND | As #2 (the pre-cross-turn twin). |
| 4 | `metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1356` `witnessChain_replay_rejected` | 1 | RE-GROUND | As #2, at the witness-chain. |
| 5 | `metatheory/Dregg2/Circuit/Freshness.lean:296` `witnessChain_replay_rejected` | 1 | RE-GROUND | As #4. |
| 6 | `metatheory/Dregg2/Circuit/ClosureReadoutsRealizable.lean:176` `closureReadouts_uninstantiable` | 1 | DO-NOT-CITE | Advertised as "Survey finding #3: no `ClosureReadouts` bundle exists, because its `other 15` member is refuted". Actually says nothing: `hRest : RestHashIffFrame RH` is a *type index* of the bundle, so the theorem is never applicable. **The finding is independently true** for a stronger and simpler reason (`restHashIffFrame_false_by_cardinality`) — cite that instead. |
| 7 | `metatheory/Dregg2/Circuit/ClosureReadoutsRealizable.lean:198` `closureReadouts_uninstantiable_concrete` | 1 | DO-NOT-CITE | As #6. |
| 8 | `metatheory/Dregg2/Circuit/ClosureReadoutsRealizable.lean:134` `closedLogExtract_emptyTag_false` | 1 | DO-NOT-CITE | See §0.3. "The dead slot is FALSE" — under an unconditionally false hypothesis, so it establishes nothing. Repair is the same `CommitSurface`/`RestHashIffFrame` split; the `kstepAll_not_total` core is floor-free and is what should be cited. |
| 9 | `metatheory/Dregg2/Circuit/ClosureTransferAvail.lean:548` `closure_rejects_overdebit_avail` | 0 | RE-GROUND | Reads as "the closure refuses an over-debit". Says: *if a commitment surface existed, an over-debited ledger readout would be unsat.* The over-debit arithmetic is structural; the surface is only the readout's index. |
| 10 | `metatheory/Dregg2/Circuit/ClosureTransferAvail.lean:561` `closure_audit_forgery_unsat` | 0 | RE-GROUND | The concrete `bal = 0, amt = 10⁹` instance of #9. Same repair, same caveat. |
| 11 | `metatheory/Dregg2/Circuit/TransferDecodeBridge.lean:328` `decodeBridge_rejects_wrong_readout` | 0 | RE-GROUND | As #9. |
| 12 | `metatheory/Dregg2/Circuit/RotatedKernelForestCohortChain.lean:203` `chainBroken_rejects` | 0 | RE-GROUND | "The deployed anti-splice `this_old == prev_new` rejects a forged tail." The proof is the chain's `pubChain` field — pure equality threading, no CR. Survives the split unchanged. |
| 13 | `metatheory/Dregg2/Circuit/RotatedKernelForestCohortChain.lean:267` `unchained_tail_rejects` | 0 | RE-GROUND | As #12. |
| 14 | `metatheory/Market/ProtocolAssurance.lean:298` `marketBoundaryBinding_rejects_wrong_post` | 0 | RE-GROUND | "Both public endpoints of the market boundary are load-bearing." Currently: *for every inhabitant of an empty type.* This is the market's negative tooth and it is not biting. Same split. |
| 15 | `metatheory/Dregg2/Circuit/LightClientFusion.lean:184` `dProduced_not_vacuous` | 0 | DO-NOT-CITE | A non-vacuity control that is itself vacuous (§0.2). Restate over floor-free primitives *before* it is cited as evidence the fusion premise is inhabited. |
| 16 | `metatheory/Dregg2/Circuit/LightClientFusion.lean:192` `dProduced_false_everywhere` | 0 | DO-NOT-CITE | As #15. |
| 17 | `metatheory/Dregg2/Circuit/StateCommitReduce.lean:292` `surface_no_stateBreak` | 0 | DO-NOT-CITE | "The surface's bundled injectivity refutes its own break." True of no surface. Its doc-comment says this is where the whole layer's hypotheses were consumed — i.e. the layer's obligations were moved into an empty room. |

**Repair for the whole tier, stated once.** Split
`CircuitSoundness.CommitSurface` into

* `CommitPrimitives` — `CH`, `RH`, `cmb`, `compress`, `compressN` (no `Prop` fields), and
* a separate CR record carrying the four injectivity fields, whose *own* repair is §3's game floor,

then re-parameterise. `restFrame` must be **deleted, not migrated**: the structural fix it wants —
already named in `Verify/InjSpelledFloors` — is to digest the *finite support actually touched* (the
`accounts : Finset CellId` rows) rather than the whole function `CellId → AssetId → ℤ`. That kills
the Cantor obstruction at the source. Every row above whose verdict is RE-GROUND then re-elaborates
with no change to its statement.

---

## §2 — Tier 1: the crypto assurance headliners (13 rows)

These are the theorems someone would actually cite in a security claim.

### 2.1 The `MSISHard`-carrying five

All five are the same shape: a protocol safety property, discharged through
`HybridCombiner.hybrid_secure_if_either_floor`, resting on `SchnorrDLHard ∨ MSISHard`.

| # | Claim | dep | Verdict | Honest restatement / repair |
|---|---|---|---|---|
| 18 | `metatheory/Dregg2/Crypto/ConsensusSafety.lean:200` `consensus_safe_under_floor` | 4 | RE-GROUND | Reads as **"two conflicting blocks cannot both be finalized"** — the quantum-safe-finality headline. Says: *if no short nonzero kernel vector exists for the augmented lattice map (false at any compressing `A`), then …* Replacement exists: `Crypto/ProtocolSoundnessQuant.settlement_finality_quant` bounds the break advantage by `hybridBreakAdv ≤ H.hybridForgerAdv`, negligible under `DLHardQuantShape ∨ MSISHardQuantShape`. |
| 19 | `metatheory/Dregg2/Crypto/LightClientSoundness.lean:173` `accepting_forged_history_breaks_floor` | 2 | RE-GROUND | "A light client accepting a forged history breaks the floor." Vacuous the same way. Replacement: `ProtocolSoundnessQuant.lightclient_forge_negl_quant`. |
| 20 | `metatheory/Dregg2/Crypto/BlocklaceSafety.lean:248` `no_forged_block_under_floor` | 2 | RE-GROUND | "No forged block is accepted." Replacement: `ProtocolSoundnessQuant.no_forged_block_quant`. |
| 21 | `metatheory/Dregg2/Crypto/DowngradeResistance.lean:211` `downgrade_resistant_under_floor` | 2 | RE-GROUND | "A downgrade below the strongest common suite cannot be accepted." Replacement: `ProtocolSoundnessQuant.downgrade_resistance_quant`. |
| 22 | `metatheory/Dregg2/Crypto/LightClientSoundness.lean:227` `lightclient_no_fork` | 1 | RE-GROUND (cheapest) | "Two certificates at the same height cannot carry different blocks." ⚑ `ProtocolSoundnessQuant`'s own §"What is STRUCTURAL" lists this theorem as **needing no hardness floor at all** — it is quorum intersection under `≤ f` Byzantine, given unforgeable votes. Repair: restate taking `EufCma` as a hypothesis instead of the floor. It then becomes **floor-free and CITABLE**. This is a one-theorem job and it is the best value in the ledger. |

⚑ **Read the replacement's own floor before citing it.** `ProtocolSoundnessQuant`'s twins are the
right *shape* — a negligible advantage ensemble over an adversary class — but their floor is
`…HardQuantShape` over an abstract adversary family whose efficiency predicate is not instantiated at
deployed parameters. At the unrestricted class the quantified floor is **refuted**
(`FloorGames.msisHardQuant_top_false_of_compressing`, `¬ MSISHardQuant F (fun _ => True)`). So the
honest citation is: *"conditional on MSIS being hard for a bounded adversary class, which we state but
do not instantiate"* — not *"proved"*. The efficiency predicate is the load-bearing part and it is
still open.

### 2.2 The `_discharged` family — six rows, and the reason they are not simply vacuous

`Crypto/ForkingDischargeConsumers` restates the five above (plus revocation) with the forking
extractor retired. Their floor is a **disjunction**:

```lean
(hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented A t) ((β + β) + (β + β)))
```

A disjunction with one refuted disjunct is not refuted — it collapses to the other. So at deployed
parameters these six reduce to *"assuming `SchnorrDLHardF g`"*, and the question is what that floor
is worth.

`DLSolverF g := ∃ dlog : G → S, ∀ P : G, (dlog P) • g = P`. Under `Classical.choice` such a `dlog`
exists **iff `s ↦ s • g` is surjective**. So:

* if `g` generates the modelled group (the honest keygen case — the module's own doc says keygen
  ranges `x ↦ x·g` over the whole scalar field), the solver exists, `SchnorrDLHardF g` is **FALSE**,
  and all six are vacuous;
* if it does not, `SchnorrDLHardF g` is **TRIVIALLY TRUE** — satisfied by a completely broken curve,
  exactly the degeneracy `CryptoFloorTeeth.schnorrDLHard_of_smul_collision` proves for the ℕ-scalar
  twin `SchnorrDLHard`.

**Either way the floor carries zero cryptographic content**: its truth value tracks surjectivity of
`s ↦ s • g`, a modelling artifact, never the difficulty of finding a discrete log. The tree refutes
it only at the ℚ toy (`ex_dl_not_hard`), so *which* degeneracy applies at deployed parameters is
currently **undetermined in-tree**, and it does not matter for citation.

| # | Claim | dep | Verdict | Honest restatement |
|---|---|---|---|---|
| 23 | `metatheory/Dregg2/Crypto/ForkingDischargeConsumers.lean:240` `consensus_safe_under_floor_discharged` | 0 | DO-NOT-CITE | "Under `n > 3f` and `SchnorrDLHardF ∨ MSISHard`, no two conflicting blocks finalize." The right disjunct is refuted at any compressing map; the left is a surjectivity artifact. Nothing about deployed security follows. |
| 24 | `…:388` `lightclient_no_fork_under_floor_discharged` | 0 | DO-NOT-CITE | As #23. (Its floor-free restatement is #22's repair.) |
| 25 | `…:361` `accepting_forged_history_breaks_floor_discharged` | 0 | DO-NOT-CITE | As #23. |
| 26 | `…:271` `no_forged_block_under_floor_discharged` | 0 | DO-NOT-CITE | As #23. |
| 27 | `…:171` `downgrade_resistant_under_floor_discharged` | 0 | DO-NOT-CITE | As #23. |
| 28 | `…:207` `revocation_sound_under_floor_discharged` | 0 | DO-NOT-CITE | As #23, **and doubly** — it also still carries `hcr : HashCR`, refuted at every compressing root hash. The module's own comment says so. Honest discharge for its hash horn already exists: `RevocationSoundness.revocationRoot_binds_rom` (keyed-ROM floor, proved). |

**The exact next theorem for this section**, which settles all six at once:

```lean
theorem not_schnorrDLHardF_of_surjective {G S} [·] (g : G)
    (hs : Function.Surjective (fun s : S => s • g)) : ¬ SchnorrDLHardF (S := S) g :=
  fun hard => hard ⟨Function.surjInv hs, Function.surjInv_eq hs⟩
```

in `metatheory/Dregg2/Crypto/CryptoFloorTeeth.lean` §3, plus the instance discharging `hs` at the deployed
generator. If it lands, rows 23–28 move from DO-NOT-CITE-contentless to DO-NOT-CITE-vacuous and the
`_discharged` family should be deleted in favour of `ProtocolSoundnessQuant`.

### 2.3 The two the sweep missed — the deployed threshold signature

Both were **exempt**, filed alongside genuine refutations by the old binder-order rule, because they
conclude `False`. Both read, in plain English, *"the deployed threshold signature cannot be forged."*

| # | Claim | Verdict | Honest restatement / repair |
|---|---|---|---|
| 29 | `metatheory/Dregg2/Crypto/HermineMSIS.lean:60` `no_forgery_under_msis` | RE-GROUND | Says: *if no short nonzero kernel vector exists for `A` at bound `βz+βz+βcs` — false at any compressing `A` — then a forked forgery is impossible.* **The reduction itself is floor-free and fully citable:** `forked_forgery_yields_msis_solution` (same file, no `hard` hypothesis) proves unconditionally that two accepting transcripts on a shared commitment with `c ≠ c'` yield a genuine `IsMSISSolution`. Cite the reduction; do not cite the packaging. |
| 30 | `metatheory/Dregg2/Crypto/HermineSelfTargetMSIS.lean:145` `no_forgery_under_msis_selftarget` | RE-GROUND | As #29, on the augmented map. Floor-free cores: `selftarget_extract_nonzero`, `forked_forgery_yields_msis_solution_selftarget` — strictly cleaner (no MLWE, no invertibility; `c ≠ c'` supplies non-triviality). |

**Downstream.** `HermineHybrid.hermine_hybrid_survives_classical_break` and
`AdvCalculus.pq_euf_cma_grounded_in_msis` build on these two and inherit the vacuity.

**The repair, precisely.** Replace the Boolean `MSISHard A β` with `FloorGames.MSISHardQuant F Eff`
at a genuine adversary-indexed family. ⚑ The `Eff` argument is not decoration: `MSISHardQuant F
(fun _ => True)` is **refuted** (`FloorGames.msisHardQuant_top_false_of_compressing`), so instantiating
`Eff := ⊤` reproduces the same vacuity in probabilistic costume — which is exactly the bug
`CryptoFloorTeeth` §4 proves about `FloorBridge.msisSolverAdv`
(`msisHardQuant_solverAdv_iff_msisHard`: the solution-indexed quantitative floor *is* the Boolean
floor). The repair is only real once `Eff` is a bounded class.

---

## §3 — Tier 2: ∅-DEPLOYED, the collision-resistance family (85 rows)

Every row below carries `Poseidon2SpongeCR` / `compressNInjective` / `Compress8CR` /
`FloorDigestBinds` — all the same predicate, "this hash is injective on an infinite domain" — refuted
at BabyBear by `HashFloorHonesty.poseidon2SpongeCR_false_babyBear`.

**The uniform honest restatement** for every DO-NOT-CITE row in this section:

> *If the deployed Poseidon2 sponge were injective on all of `List ℤ` — which it provably is not, its
> outputs being BabyBear field elements — then this forgery/tamper/double-spend would be unsatisfiable.*

**The uniform repair**, and it is one repair, not eighty-five: migrate the floor from *injectivity* to
the **keyed, query-counted collision game**.

* Target floor: `FloorGames.HashCRHardQuant F Eff` (`CollisionResistant F ↔ HashCRHardQuant F ⊤`, and
  the `⊤` instance is what is refuted — so again, `Eff` is the load-bearing part).
* The floor that is actually **PROVED**, no assumption underneath: `Crypto/KeyedRomFloor.keyedRom_hard`
  (and `Crypto/RomQueryFloor.romCollision_hard`, the birthday bound). Both fix the counterexample that
  kills the `IsPolyTime` floor: the hash is an *oracle the adversary queries*, cost is query-counted,
  and the key is sampled *after* the adversary is fixed.
* The worked exemplar for the conclusion-shape change is `Storage/DeployedFloorRegrounded` +
  `Circuit/S5Closure`: the migrated theorem concludes a **dichotomy** (`binds ∨ collides`) *without any
  floor hypothesis*, and the collision disjunct is refutable, so the disjunction is not `True`.

### 3.1 Rows where the floor-free replacement **already exists** — cite the replacement today

| # | Claim | Verdict | Cite instead |
|---|---|---|---|
| 31 | `metatheory/Dregg2/Storage/BucketCommitment.lean:178` `objectLeaf_injective_of_binds_or_collides` | RE-GROUND ✅ | `metatheory/Dregg2/Storage/BucketCommitment.lean:77` `objectLeaf_binds_or_collides` — unconditional. |
| 32 | `metatheory/Dregg2/Storage/BucketCommitment.lean:186` `contentRoot_injective_of_binds_or_collides` | RE-GROUND ✅ | `metatheory/Dregg2/Storage/BucketCommitment.lean:139` `contentRoot_binds_or_collides`. |
| 33 | `metatheory/Dregg2/Storage/BucketCommitment.lean:194` `read_sound_of_binds_or_collides` | RE-GROUND ✅ | `metatheory/Dregg2/Storage/BucketCommitment.lean:154` `read_sound_or_collides`. |
| 34 | `metatheory/Dregg2/Storage/Deployed.lean:153` `contentRootDeployed_injective_of_binds_or_collides` | RE-GROUND ✅ | `metatheory/Dregg2/Storage/Deployed.lean:143` `contentRootDeployed_binds_or_collides` — unconditional, at the deployed hash. ⚑ This is the **one concrete** member of §3.1 (its `hCR` is `Poseidon2SpongeCR poseidon2Hash`, not a parameter), so it is the one whose port-certificate content is **nil** — see the note under the table, and #42. |
| 35 | `metatheory/Dregg2/Storage/Retrievability.lean:125` `por_sound_of_or_collides` | RE-GROUND ✅ | `metatheory/Dregg2/Storage/Retrievability.lean:67` `por_sound_or_collides`. |
| 36 | `metatheory/Dregg2/Storage/Retrievability.lean:133` `por_refuses_substitution_of_or_collides` | RE-GROUND ✅ | `metatheory/Dregg2/Storage/Retrievability.lean:83` `por_substitution_forces_collision` — note the honest conclusion is *"a substitution exhibits a collision"*, not *"a substitution is impossible"*. |
| 37 | `metatheory/Dregg2/Storage/Retrievability.lean:141` `por_holds_committed_of_or_collides` | RE-GROUND ✅ | `metatheory/Dregg2/Storage/Retrievability.lean:102` `por_holds_committed_or_collides`. |
| 38 | `metatheory/Dregg2/Lightclient/MMR.lean:210` `hashOf_injective_of_binds_or_collides` | RE-GROUND ✅ | `metatheory/Dregg2/Lightclient/MMR.lean:161` `hashOf_binds_or_collides` — unconditional. |

These eight are **port certificates**: their job is to prove the cutover surrendered nothing
("under the deleted theorem's own hypothesis, the migrated form delivers the deleted conclusion").
For the seven that are **parametric in the hash** that is a real fact *about the port*: it holds for
every hash, including the injective ones where the old hypothesis is satisfiable. They are not, and
must never be quoted as, evidence that storage reads or MMR peaks bind at deployment — the migrated
twins are what say that.

⚑ **#34 is the exception and it is the pattern to watch for.** Its hypothesis is
`Poseidon2SpongeCR poseidon2Hash` at the **concrete deployed constant**, and that closed proposition is
refuted in-tree (#47). A port certificate whose hypothesis cannot be met at its only instantiation has
**no port content either** — there is nothing to hand back. Its RE-GROUND verdict is right; the
"citable fact about the port" sentence is not true of it. The same theorem, restated at the deployed
hash, is #42, which is why #42 was mislabelled.

### 3.2 The rest of Tier 2 — DO-NOT-CITE, uniform restatement above

Grouped by subsystem. `dep` counts real consumers.

**Map / heap Merkle spine — double-spend and non-membership refusals (14)**

| Claim | dep |
|---|---|
| `metatheory/Dregg2/Circuit/MapOpWideKeyWeld.lean:349` `gates_aafiInsertW_absentW_jointly_unsat` | 3 |
| `metatheory/Dregg2/Circuit/MapMerkleRoot.lean:261` `opensToMerkle_some_excludes_none` | 2 |
| `metatheory/Dregg2/Circuit/MapOpWideKeyGate.lean:318` `opensToMerkleW_some_excludes_none` | 2 |
| `metatheory/Dregg2/Circuit/MapOpWideKeyWeld.lean:340` `gates_insertW_absentW_jointly_unsat` | 2 |
| `metatheory/Dregg2/Circuit/MapOpWideKeyWeld.lean:362` `gates_jointly_unsat_via_abstract` | 2 |
| `metatheory/Dregg2/Circuit/MapOpWideKeyWeld.lean:371` `gates_jointly_unsat_via_abstract'` | 2 |
| `metatheory/Dregg2/Circuit/MapOpWideKeyRowBoundary.lean:376` `gates_insertW_absentW_jointly_unsat_row` | 1 |
| `metatheory/Dregg2/Circuit/MapOpWideKeyRowBoundary.lean:387` `gates_aafiInsertW_absentW_jointly_unsat_row` | 1 |
| `metatheory/Dregg2/Circuit/MapOpWideKeyRowBoundary.lean:409` `gates_jointly_unsat_via_abstract_row` | 1 |
| `metatheory/Dregg2/Circuit/MapOpWideKeyRowBoundary.lean:399` `gates_jointly_unsat_via_abstract_row'` | 1 |
| `metatheory/Dregg2/Circuit/DescriptorIR2.lean:553` `opensTo_some_excludes_none` | 1 |
| `metatheory/Dregg2/Circuit/MapOpWideKeyWeld.lean:326` `writeW_then_absentW_unsat` | 0 |
| `metatheory/Dregg2/Circuit/MapAbsentImtGateWide.lean:590` `aafiInsertW_then_absentImtW_unsat` | 0 |
| `metatheory/Dregg2/Circuit/MapMerkleRoot.lean:673` `opensToMerkle8_some_excludes_none_of_injective` | 0 |

⚑ The last one carries `Compress8CR` — the 8-felt digest. Note for the felt-width campaign: **widening
did not fix this floor**, because the domain is still infinite. Only the game migration does.

**Rotated-kernel refinement / lifecycle — "the circuit rejects a wrong X" (28)**

`metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:503` `heapWrite_sat_rejects_forged_root` (dep 1) ·
`…LifecycleDisc.lean:276` `cellSeal_disc_rejects_frozen` (1) · `…:297` `cellUnseal_disc_rejects_unrevived` (1) ·
`…:307` `cellDestroy_disc_rejects_resurrection` (1) · `…:288` `cellSeal_disc_rejects_wrong_after` ·
`…:329` `receiptArchive_disc_rejects_wrong_after` · `…Birth.lean:269` `createCell_descriptorRefines_rejects_wrong_accounts` ·
`…:357` `createCellFromFactory_descriptorRefines_rejects_wrong_accounts` · `…:462` `spawn_descriptorRefines_rejects_wrong_accounts` ·
`…CellSeal.lean:326` `cellSeal_descriptorRefines_rejects_unsealed` · `…:339` `cellSeal_descriptorRefines_rejects_wrong_map` ·
`…Lifecycle.lean:202` `cellUnseal_descriptorRefines_rejects_unrevived` · `…:212` `cellUnseal_descriptorRefines_rejects_wrong_map` ·
`…:363` `cellDestroy_descriptorRefines_rejects_undestroyed` · `…:375` `cellDestroy_descriptorRefines_rejects_wrong_cert` ·
`…:533` `audit_descriptorRefines_rejects_unwritten` · `…:935` `cellDestroy_sat_rejects_wrong_cert` ·
`…:1090` `refusal_sat_rejects_unwritten` · `…Misc.lean:209` `makeSovereign_descriptorRefines_rejects_wrong_commitment` ·
`…:328` `setFieldDyn_descriptorRefines_rejects_wrong_value` · `…Notes.lean:270` `noteSpend_descriptorRefines_rejects_wrong_nullifiers` ·
`…:373` `noteCreate_descriptorRefines_rejects_wrong_commitments` · `…PermsVK.lean:178,188,260,269` (four
`setPermissions`/`setVK` rejects) · `…Program.lean:180` `setProgram_sat_rejects_unwritten` ·
`…SpawnHandoff.lean:181` `spawn_handoff_rejects_wrong_accounts`.

All `compressNInjective`, all dep ≤ 1. `heapWrite_sat_rejects_forged_root` is the one to watch: it is
advertised as "the Lean twin of the Rust mutation-confirm `heap_write_deployed_root_forced.rs`", so a
reader may take it as the formal backing for a runtime canary. It is not, at deployed parameters.

**Deos capacity / bare-cohort refusals — the anti-launder forge (20)**

`metatheory/Dregg2/Deos/BareCohortFloorRefuseDeployed.lean:229` `declared_tag_unsat_at` (dep 3, the parametric keystone) ·
`…:345` `declared_capacity_unsat_deployed` (3) · `…:376,391,406` (escrow/discharge/vault, 0) ·
`metatheory/Dregg2/Deos/BareCohortFloorRefuseWide.lean:116` `declared_capacity_unsat_wide` (1) · `…:146,161,176` (0) ·
`metatheory/Dregg2/Deos/BareCohortFloorRefuse.lean:264,516,541,553` (escrow/tag/discharge/vault under bare, 0) ·
`metatheory/Dregg2/Deos/CarrierBoundFloorGadget.lean:517` `gentian_forged_floor_unsat_carrier` (1) · `…:530` `gentian_partial_unsat_carrier` ·
`…:549` `gentian_phantom_unsat_carrier` · `metatheory/Dregg2/Deos/CapacityCarrier.lean:106` `carrier_omission_impossible` ·
`…:160` `escrow_carrier_omission_impossible` · `metatheory/Dregg2/Deos/InAirAuthorityDigestGadget.lean:455`
`gentian_partial_unsat_discharged` (1) · `…:473` `gentian_phantom_unsat_discharged` (1).

The last two carry `FloorDigestBinds`, which is `Poseidon2SpongeCR` under a different name — the same
`∀ l l', hash l = hash l' → l = l'`. Their module already names the repair
(`gentian_alternate_floor_advantage_bound`, a real alternate-floor game over the deployed `VmTrace`
column) and is explicit that it re-grounds **the CR leg only** — `ChipTableSound` and the wide-commit
limb binding are separate hypotheses with their own repair paths. One of three legs.

⚑ `carrier_omission_impossible` / `escrow_carrier_omission_impossible` are the theorems behind "a pure
light client binding PI 45 catches a dropped capacity entry." That is a *product* claim; it is
currently vacuous.

**Emit / availability wide-members (13)**

`metatheory/Dregg2/Circuit/Emit/AvailWireMembers.lean:301` `declared_capacity_unsat_availWire` (dep 1) · `…:337,352,367` ·
`metatheory/Dregg2/Circuit/Emit/AvailWideMembers.lean:381,428,444,460` (`availWideRefused` family) · `…:616,664,680,696`
(`burnAvailWideRefused` family) · `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRecordRoot.lean:297` `recordTamper_rejected`.

**Light-client omission + bundle cutover (2)**

`metatheory/Dregg2/Lightclient/NonOmissionAttack.lean:226` `grounded_mmr_rejects_omission` — reads as "a server dropping
a receipt from a range proof is caught"; vacuous at the deployed sponge, and unlike §3.1 it has **no
landed unconditional twin**. `metatheory/Dregg2/Circuit/BundleCutoverCheck.lean:127` `nonmember_refused_of_injective` —
a port certificate for the deleted `nonmember_refused`; citable as such only.

---

## §4 — the rows audited as CITABLE (9 rows; 7 survive, 2 were mislabelled)

⚑ **THE DISCRIMINATOR, EARNED HERE 2026-07-26 AND APPLICABLE TO EVERY FUTURE CITABLE ROW.** A floor
hypothesis at a **universally quantified** hash/deployment/surface is a legitimately parametric
statement: it is satisfiable (at an injective hash), so the theorem has content. The *same* floor at a
**concrete deployed constant** — `Poseidon2SpongeCR poseidon2Hash` rather than `Poseidon2SpongeCR hash`
— is a **closed proposition the tree refutes**, and the theorem carrying it is vacuous with nothing left
to salvage, not even a port certificate. **Read the binder, not the name.** This audit found exactly one
row on the wrong side of that line (#42); the other seven CITABLE rows were re-read statement by
statement and hold.

Of the seven that survive, two are **wound reports** and two are **teeth** — quote them as evidence of
what is broken, never as assurance.

| # | Claim | Verdict | Scope / honest restatement |
|---|---|---|---|
| 39 | `metatheory/Dregg2/Circuit/StateCommitFloorRegrounded.lean:193` `leafRealization_uninhabitable_babyBear` | **CITABLE** | **Wound.** A `LeafRealization` whose sponge is BabyBear-range-bounded cannot exist. So `cellLeafInjective` is discharged only at a sponge no deployment runs. Binders are `{CH}`, `R`, `hb` — all parametric, and the conclusion `False` *is* the refutation. dep 2. |
| 40 | `metatheory/Dregg2/Circuit/StateCommitFloorRegrounded.lean:202` `logRealization_uninhabitable_babyBear` | **CITABLE** | **Wound.** Same on the log side — and it names the live consumer: `Verify/KeystoneAuditArgusReceipt.LH₀_inj` stands on `refLogRealization`, whose sponge is `Encodable.encode` (unbounded range). The receipt's carrier is discharged, and at BabyBear it could not be. dep 3. |
| 41 | `metatheory/Dregg2/Circuit/S5Closure.lean:119` `deployed_collision_refutes_domainSepCR` | **CITABLE** | **Tooth.** A genuine collision at any tag gives a constructed fixed-pair finder positive advantage, refuting `DomainSeparatedCR`. Nothing re-assumed; the finder is a real term. ⚑ Scope: `D` and the collision witness `hcol` are both **supplied** — it does not itself exhibit a collision of the deployed sponge, it converts one. |
| 42 | `metatheory/Dregg2/Storage/DeployedFloorRegrounded.lean:466` `storage_migration_strictly_stronger` | **DO-NOT-CITE** ⚑ *was CITABLE — corrected 2026-07-26* | **Vacuous at its only instantiation.** Its hypothesis is `hCR : Poseidon2SpongeCR poseidon2Hash` — the **concrete deployed hash, not a parameter** — and that exact proposition is refuted **seven lines below**, at `:473` (#47). It says: *if the deployed Poseidon2 sponge were injective on all of `List ℤ`, which it provably is not, then two distinct object lists could not share a deployed content root.* Nothing about the deployed system follows. There is no port content to fall back on either: it is #34 applied at `poseidon2Hash`, and #34 is RE-GROUND. **Cite instead:** #47 for the strictness half, and `metatheory/Dregg2/Storage/Deployed.lean:143` `contentRootDeployed_binds_or_collides` — unconditional, at the deployed hash — for the binding. |
| 43 | `metatheory/Dregg2/Storage/DeployedFloorRegrounded.lean:479` `mmr_migration_strictly_stronger` | **RE-GROUND ✅** ⚑ *was CITABLE — corrected 2026-07-26* | **Not #42's defect — read the binder.** Here `hash` is **universally quantified** (`(hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)`), so nothing in the tree refutes this statement; it is `MMR.mroot_injective` in contradiction form and it is satisfiable at an injective hash. But at the only instantiation that would license a deployed claim (`hash := poseidon2Hash`) the hypothesis is false, so it is a **port certificate exactly like §3.1's parametric seven** and it takes their verdict, not a CITABLE one. Its previous scope note ("As #42") inherited #42's framing and was wrong on both counts. **Cite instead:** `metatheory/Dregg2/Lightclient/MMR.lean:477` `mroot_binds_or_collides` — unconditional. |
| 44 | `metatheory/Dregg2/Storage/DeployedFloorRegrounded.lean:158` `poseidon2SpongeCR_gives_game_floor` | **CITABLE** | **Port certificate, PARAMETRIC.** The old injectivity floor implies the new game floor — the no-strength-lost direction of the CR migration, read at the sentinel's name. ⚑ `D : SpongeDeployment` is universally quantified, so this is **not** #42's defect; but instantiating at `deployedSponge` makes `hCR` false (#47 at its single tag), so it licenses nothing about the deployed sponge — only the **ordering of the two floors**. |
| 45 | `metatheory/Dregg2/Storage/DeployedFloorRegrounded.lean:496` `storage_collision_disjunct_refutable` | **CITABLE** | **Non-vacuity control, with a scope caveat.** `hash` is parametric. It proves the collision disjunct is refutable *at an injective sponge*. ⚑ It therefore does **not** establish that the migrated keystones are non-trivial at the deployed sponge, where the disjunction may well be dischargeable by its collision branch. Cite the fact; do not cite the consequence. |
| 46 | `metatheory/Dregg2/Tools/ConePortListCommitRun.lean:62` `leakyExhibit` | **CITABLE** | **Tool control.** A deliberately leaky specimen the cutover tool must refuse — the ~22% leaky class reproduced in miniature. It carries `compressNInjective cN` at a parametric `cN`; that is the point, since what the tool must recognise is its *shape*. Citable as instrument documentation only. |
| 47 | `metatheory/Dregg2/Storage/DeployedFloorRegrounded.lean:473` `storage_old_hypothesis_unavailable` | **CITABLE** | **Tooth, at the deployed constant.** `¬ Poseidon2SpongeCR poseidon2Hash`, discharged by `DeployedFloorRefuted.deployed_floor_false` (an `rfl` collision of the deployed hash). Closed, unconditional, no parameters. This is the honest half of what #42 was being cited for, and it is the very theorem that makes #42 vacuous. ⚑ **Added by the 2026-07-26 audit; the original sweep could not flag it because it carries no floor** — which is exactly why the citable statement was missing while its vacuous neighbour was listed. |

---

## §5 — What this ledger does not cover

* **Everything upstream of the FRI floor.** Nothing here touches the STARK/FRI posture; see
  `project-fri-soundness-reality` and `RESEARCH-correlated-agreement-UD-prompt-2026-07-24.md`. A row
  marked CITABLE is citable *modulo* that floor, which is separate and undischarged.
* **The witness-generator perimeter.** A refinement theorem constrains the trace, not the generator
  that produced it. Orthogonal to this ledger and unaffected by any repair named here.
* **`Function.Injective`-spelled sites.** The gate reports **628** injectivity-shaped sites spelled
  with Mathlib's `Function.Injective` rather than one of our named floors; they are *ungated* and were
  not swept, so they are not in these 123. They are the most likely place for the next batch.
* **The ~2059 grandfathered carriers** the ratchet counts. This ledger triages the 121 the sweep
  flagged as *assurance-shaped* plus the 2 exempt Hermine claims. The remainder are largely
  intermediate lemmas whose vacuity is inherited from a row above; they matter for repair scheduling,
  not for citation.

---

## §6 — Priority order for the repairs

1. **`lightclient_no_fork` → `EufCma`-parameterised** (row 22). One theorem, no new floor, converts a
   headline claim from vacuous to citable. `ProtocolSoundnessQuant`'s own analysis already says the
   hardness is not needed.
2. **Split `CommitSurface`; delete `restFrame`** (§1). Unblocks 17 rows here and 409 declarations
   tree-wide; structural, not cryptographic.
3. **`not_schnorrDLHardF_of_surjective`** (§2.2). One lemma; settles whether the six `_discharged`
   consumers are vacuous or merely contentless, and either way justifies deleting them.
4. **Hermine pair onto `MSISHardQuant _ Eff` with a bounded `Eff`** (§2.3). The reduction cores are
   already floor-free; only the packaging needs rewriting.
5. **CR family → `HashCRHardQuant` / keyed-ROM** (§3). Eighty-five rows, one repair, one landed
   exemplar (`Storage/DeployedFloorRegrounded`), one proved floor (`KeyedRomFloor.keyedRom_hard`).
   Do the `Deos` capacity-carrier rows first — those are product claims.

---

## §7 — The standing rule this earns

`#floor_ratchet` stops *accrual*. It does not stop *citation*. A theorem can be correctly recorded as
a grandfathered carrier and still be quoted next week in a launch post as if it were assurance,
because the record lives in the gate and the claim lives in prose.

**Before any public security claim: find the theorem in this ledger. If it is not here, check its
binders for a floor before you write the sentence** — and if there is one, check whether it stands at a
**concrete deployed constant** rather than a bound variable, because that is the difference between a
parametric theorem and a vacuous one (§4). The three verdicts are written to be pasted into a review
comment as-is.

⛑ **And the ledger is not exempt from its own rule.** #42 sat here as CITABLE with a hypothesis refuted
seven lines below itself in the same file, and the row that *should* have been cited (#47) was absent
because the sweep only listed floor-*carriers* — so the vacuous statement was listed and the true one was
not. Every CITABLE row must be re-read at the statement level, not matched by name.
