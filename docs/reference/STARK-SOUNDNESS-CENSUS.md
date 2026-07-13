# STARK / Config-Evolution Soundness Census (2026-07-13)

The authoritative honest state of the STARK-soundness campaign. Orient from this before the topic files.
Through-line: **the STARK layer went from an opaque `verifyBatch` fake carrier to a real, reduced-to-the-crypto-floor
soundness for the whole kernel's *configuration evolution* — and every real defect it surfaced was found by refusing
to carry a fact and asking what forces it.**

## THE OBJECT — `kernelConfigSound` (`Dregg2/Circuit/KernelConfigSoundness.lean`)

`verifyBatch`-accept over the real registry `Rfix` ⟹ `∃ pre post fa, StateDecode … ∧ actionTag fa = pi.effect ∧
fullActionStep pre fa post ∧ <commit-frame>` — i.e. `kstepAll pi.effect` UNFOLDED. `fullActionStep` is the REAL
declarative kernel step (`⟺ execFullA` over `RecordKernelState`: accounts/per-asset balances/caps/nullifiers/
commitments/heaps+heap_root/fields/nonce), with per-effect frame proved (transfer moves `bal` only w/ conservation
Law 1; noteSpend inserts nullifiers only; heapWrite splices heaps only) and cross-step frame DERIVED
(`stateDecodeChain_frame_continuous`). **Not** trace-satisfaction — the machine evolves correctly. Composed
genuinely: `algoStarkSound_kernel` (STARK) → `StarkSound hash Rfix` + `closedLogExtract_all_genuine` (config bridge,
36 proven per-effect rungs), NOT a re-assumed `EffectDecodeBridge`.

## THE FLOOR — minimal, named, mostly proven

`kernelConfigSound` rests on exactly:
- **`Poseidon2SpongeCR`** — hash collision-resistance (Merkle/commitment binding).
- **`Poseidon2ChipArithSound`** — the Poseidon2 chip round-gate output-correctness. `arithSound_not_CR` proves it is
  DISTINCT from CR (the all-zero perm is arith-sound-as-a-table yet violates CR) — a sibling Poseidon2 primitive.
- **`FRI-LDT@deployed`** — the list-decoding soundness bound every STARK shares. The proved BBHR18 algebra
  (`FriSoundness.fold_close_of_two_alpha` / `friProximity_discharge`) is now INSTANTIATED at the deployed
  parameters, no toy `δ=0` stand-in: over `F := BabyBear` at the deployed WRAP rate `1/64` (`|L|=128` coset,
  `numQueries=19`, `BabyBearFriDeployedInstance.friSetupWrapRate` / `wrapRate_friProximity`), plus the `2^27`
  2-adicity-cap domain (`BabyBearFriDeployed.friSetupMaxDomain`) and the prover rate `1/8`
  (`friSetupDeployedRate`). The query-reject teeth are DISCHARGED (unconditional counting) at `numQueries=19`
  (`wrap_far_word_rarely_accepted` ≤ `(65/128)^19`, fired on the committed far word `fSq`). HONEST residual:
  at `19` queries the unique-decoding radius gives only `(65/128)^19 ≈ 2^-18.6` (`wrap_ud_error_not_lt_2e31` —
  NOT `< 2^-31`), so deployed wrap security rests on the JOHNSON list-decoding radius `δ_J=1-√ρ=7/8` (BCIKS20),
  named `FriLdtDeployedBound`. **That bound as-written is now DISCHARGED** (`FriLdtJohnson.lean`,
  `friLdtDeployedBound_discharge`, axiom-clean): at `δ_J=7/8` it is exactly the trivial counting else-branch
  (`accept_prob_le_of_farN`), so `ldt_bound_unconditional` delivers `(1/8)^19 = 2^-57` with NO hypothesis. Its
  genuine BCIKS20 content (words inside the `δ_J` ball, past unique decoding) is reduced to two precisely-named
  lemmas — `RSListBound` and `FriProximityGapChallenges` — each PROVED at `L=1` and instantiated on the deployed
  rate-`1/64` code (min-distance `127` → singleton at radius `63`); only their `L>1` generalization remains open.
  The prover config (rate `1/8`, `38` queries)
  is separately DISCHARGED in the unique-decoding regime (`DeployedProximitySoundness`, `< 2^-31`).
- **FS-SZ ε** — Fiat-Shamir non-exceptionality, `ε ≤ deg/|F|` (a game in `ProbCrypto.winProb`, not an axiom).
- structural range tables (PROVEN, not a floor: `rangeTable bits = [0,2^bits)` symbolically, never enumerated).

Everything else DISCHARGED or REDUCED (not carried): the mod-p→ℤ lifts (field-faithful denotation); `hood.a` RLC
de-batch → Schwartz-Zippel; `hood.b` commitment binding → `Poseidon2SpongeCR`; `hnonexc` → the FS game; the LogUp bus
membership → SZ (`busBalance_forces_membership` + the multiset `_perm` extension); `MapTableAssembly` = a projection of
`Satisfied2`; `BusModelFamily` → the FS-SZ floor; `ChipTableSoundN` → `{Poseidon2ChipArithSound + structural range}`.
**No opaque floor, no carried `def`-hypotheses.**

## THE FIVE DEPLOYED SOUNDNESS GAPS (all found by refusing to carry a fact)

| # | Gap | Exploit | Status |
|---|-----|---------|--------|
| 1 | Vault settlement carry-wrap (16-bit carries reach p) | forge share-inflating settlement | FIXED (`CARRY_BITS 16→15`), staged |
| 2 | Cap-open mask-recon (32-bit, 2p<2³²) | a cap granting nothing authorizes a transfer | FIXED (per-16-bit-limb recon, `reconExact` DERIVED), staged |
| 3 | Cross-cell conservation (≥2-cell sum wraps p) | forge value-conservation | FIXED (multi-limb accumulator), staged |
| 4 | Core-transfer over-debit (amount unranged) + credit overflow | mint from nothing / value destruction | FIXED (15-bit borrow + carry, BOTH directions, availability DERIVED), staged |
| 5 | Heap-sortedness double-spend (per-turn insert forces no sorted placement) | commit a non-sorted heap → forge a nullifier absence → re-spend | Lean closure PROVEN (IMT); deployed Stage A landed; **Stage F (atomic flip) = the coordinated VK-regen** |

Gaps 1–4: local-gate fixes (magnitude bound + sign/direction gate). Gap 5: NOT a local gate — the compacted-array
insert is an O(n) suffix-shift unbindable in a fixed-width AIR; the sound closure is an **Indexed-Merkle-Tree
(append-at-free-index) migration** (impact analysis: low-pain, sync is replay not snapshot, order-independence not
load-bearing; AAFI also kills the O(n) rebuild = a perf win).

## GAP #5 CUTOVER — where it stands

- **Lean closure PROVEN** (`IndexedMerkleTree.lean`): `imtInsert_preserves`, `canonicalHeapExtract_of_imt`,
  `imt_double_spend_unsat`, + the AAFI bridge composing `aafiInsert_forces_imtInsert` → `canonicalHeapExtract`. Gap #5
  reduces into `{Poseidon2SpongeCR, FRI-LDT}` the moment the flip routes op=4.
- **Deployed Stage A LANDED (additive, green)**: `MapKind::AafiInsert` op + the two-path AIR gates (`MAP_WIDTH` 421→897,
  op≤3 byte-identical) + the Lean mirror (reconciled to the actual columns) + the 90-site `HeapLeaf` migration + the
  store append-seq persistence. Nothing routes to op=4 yet.
- **Stage F (OWED — the atomic flip, ember-approved, coordinated)**: route the 3 append-only ops (NoteSpend→nullifier,
  NoteCreate→commitment, Revoke→revoked) to `AafiInsert`, regen VK + fixtures, **batch the 4 wrap-class fixes into the
  same VK epoch**. Then Stage P (rebuild + hbox gauntlet last). Plan: `GAP5-AAFI-CUTOVER-PLAN.md`.
- **Named residuals** (not holes): the chain↔vector representation seam (the Lean↔Rust layout correspondence — being
  closed/bounded); the P3 tail (`blocklace_sync` append-seq export, historical-nullifier seq schema); the mutable
  cell/heap map AAFI-vs-sparse decision (deferred — NOT the double-spend; snapshot-sync-driven).

## THE METHOD (why it worked)

Making each layer *real* surfaced the defect that layer was hiding:
- **Field layer** — field-faithful (mod-p) denotation ⟹ the 4 wrap forgeries (the ℤ model hid all four).
- **Trace layer** — the bus/map "modeling facts" ⟹ discharged to the floor (debt, paid — not a toy: `kstepAll` is a
  real config model).
- **Config layer** — real `fullActionStep` instead of `Satisfied2` ⟹ the 5th gap (heap-sortedness double-spend).

The discipline that made it honest: read what the check CHECKS; a `def FooHard` used as a hypothesis is an assumption
(`#assert_axioms` never sees hypotheses); reduce to the floor; ship the adversarial (both-truth) test; classify every
seam before pessimism OR optimism; and apply all of it to the INTEGRATOR, not just the lanes — the self-caught
launderings (`reconExact`, `hcanonMove`, the `{hood,hnonexc}` "floor", the debit-only fix, transferV3-as-kernel, the
BabyBear-computability heap-bomb, the phantom column offsets) are where it mattered most.
