# STARK-COMPLETION-AUTOMATION — what the transferV3 end-to-end wiring teaches about the 27-effect rollout

**Honest scope, first sentence.** Having driven ONE effect (`transferV3`) all the way to a real
`AlgoStarkSound` instance with `hood`/`hnonexc` DISCHARGED (not re-assumed) resting on only
`{Poseidon2SpongeCR, FRI-LDT@deployed}`
(`metatheory/Dregg2/Circuit/AlgoStarkSoundTransferV3.lean`), this doc reports PRECISELY which parts of
that wiring are mechanical/descriptor-driven (they recur identically for each of the ~27 effects), which
are genuinely effect-specific, and what proof automation collapses the rollout from a deathmarch into a
fan-out. The verdict is grounded in a demonstrated fact: the entire crypto-composition core is already
descriptor-POLYMORPHIC in-tree — `hood_of_reductions d` and `mainAirAcceptF_of_floor d` are proven `∀ d`,
and the transferV3 instance is their specialization at `d := transferV3`.

The reference numbers below are concrete: `transferV3` has **283 constraints, 147 arithmetic**, so
`arithList transferV3` is a real 147-element list and `batchResidual (Rfam transferV3 t ζ qp)` is a
genuine BabyBear polynomial of degree `< 147` (ε_RLC ≤ 146/2013265921).

---

## 1. What is MECHANICAL / descriptor-driven (recurs IDENTICALLY, only the descriptor name changes)

The whole path from "FRI-LDT bundle" to `MainAirAcceptF d t` is descriptor-agnostic. Concretely:

### 1a. The arith-constraint layout — a one-liner, descriptor name only
```lean
def arithList (d : EffectVmDescriptor2) : List VmConstraint2 := d.constraints.filter isArithB
```
`isArithB` / `isArithB_iff` are GLOBAL (written once). Per effect this is the identical expression with
`d` substituted. **Zero per-effect proof.**

### 1b. The per-constraint residual family feeding `batchResidual` — identical shape
```lean
noncomputable def Rfam (d) (t) (ζ) (qp) : Fin (arithList d).length → BabyBear :=
  fun j => (constraintPoly d t ((arithList d).get j)).eval ζ
             - (vanishingPoly t).eval ζ * (qp ((arithList d).get j)).eval ζ
```
The column-layout map `constraint-list → Fin n → residual` is generated from the descriptor's constraint
list by this single polymorphic definition. **The column-layout map generation is fully mechanical.**

### 1c. The `hood` derivation — 100% descriptor-agnostic proof term
`hood_of_reductions d …` is proven once, `∀ d`. Its body is the fixed five-step composition, character
-identical for every effect (only `d` varies):
```lean
have htable := verifyAlgo_accept_forces_table_identity …        -- batched OOD identity (THEOREM)
have hbind  := commitmentOpening_binds_of_poseidon2CR sponge hCR hCommitted hOpened  -- hood.b (Poseidon2CR)
have hvc    := hbind.symm.trans htable                          -- vCommitted = A.mul …
have heval  : (batchResidual (Rfam d t ζ qp)).eval Λ = 0 := by rw [hlayout, hvc]; exact sub_self _
have hRzero := rlc_debatch (Rfam d t ζ qp) Λ heval hLam         -- hood.a RLC de-batch (THEOREM)
intro c hc harith
have hcf := List.mem_filter.mpr ⟨hc, (isArithB_iff c).mpr harith⟩
obtain ⟨i, hlt, hget⟩ := List.mem_iff_getElem.mp hcf
… simp only [Rfam, List.get_eq_getElem, hget] …; exact sub_eq_zero.mp hj0
```
**The batchResidual-from-constraint-list, the RLC/commitment/table-identity composition, and the
per-constraint read-off are all mechanical.** This is the bulk of the crypto work and it is written once.

### 1d. The `MainAirAcceptF` landing — one application, identical
```lean
theorem mainAirAcceptF_of_floor (d) … : MainAirAcceptF d t :=
  ood_forces_mainAirAccept_field_of_residuals d t hcap ζ qp (hood_of_reductions d …) hnonexc
```
Proven `∀ d`. Per effect: nothing new — instantiate.

### 1e. The FS ε-bound teeth — identical
`hnonexc_is_bounded_fs_form` / `rlc_lambda_is_bounded_fs_form` quote
`ood_hnonexc_escape_prob_le d` / `batchResidual_exceptionalSet_card_lt` — both descriptor-parametric.
The per-effect soundness error is just `natDegree(residual)/|F|` and `(#arithList d − 1)/|F|`: a
different NUMBER per effect, but no different PROOF.

### 1f. The `FriLdtExtract` bundle shape — mechanical copy-swap
`FriLdtExtractV3`'s field list (trace/ζ/Λ/qp/topen + Merkle recompute data + column-layout eq + the two
FS-non-exceptionality facts + aux legs) is a fixed template; only `transferV3` and the mem-free aux legs
change. For any other mem-free effect it is a pure copy-swap.

**Summary:** the column-layout map, the `batchResidual`, the entire hood-discharge composition, the
`oodInterpF`/`MainAirAcceptF` wiring, and the ε-bound teeth are ALL mechanical. They already exist as ONE
`∀ d` theorem pair. Per effect they cost a single `@mainAirAcceptF_of_floor <descriptor>` instantiation.

---

## 2. What is genuinely EFFECT-SPECIFIC (needs real thought)

The mechanical core lands `MainAirAcceptF d t`. The remaining per-effect obligations are NOT in the OOD
chain — they are the `AlgoStarkSound` assembler's OTHER legs:

- **The final assembler (`algoStarkSound_of_bricks_<effect>`).** `transferV3` is mem-op-free AND
  map-op-free, so its six `Satisfied2` memory/map legs COLLAPSE to `t.tf .memory = [] ∧ t.tf .mapOps = []`
  and concrete `fun _ => 0` witnesses (see `AlgoStarkSoundInstance.algoStarkSound_of_bricks_transferV3`).
  A **memory-touching effect** (spend, note, umem, mapOp effects) must use the GENERAL
  `algoStarkSound_of_bricks`, whose eight legs include `maddrs.Nodup`, `memClosed`, `Disciplined`,
  `MemCheck`, `memTF`, `mapTF`. Those are the effect's real memory-checking content (LogUp-balance +
  table-assembly faithfulness) — genuinely per-effect, NOT mechanical.
- **The `airAccept_forces_satisfied2_<effect>` bridge** (`MainAirAccept ⟹ Satisfied2`). The
  `rowConstraints` arm is generic (`airAccept_forces_satisfied2`), but the `rowHashes`/`rowRanges` and the
  memory legs discharge is per-descriptor (transferV3's lives in `AirLegsDischarged`). Templated, but each
  effect's hash-site / range / memory-discipline facts are its own.
- **The LogUp `hbus` floor and the column-layout LAW's TRUTH.** In the current scope both are CARRIED
  (inside `FriLdtExtract` / the `hbus` leg) as part of the FRI-LDT+LogUp floor. If one wanted to
  *discharge* `hlayout` (prove the batched opening really is the RLC of that effect's columns) rather than
  assume it, that requires the effect's actual commitment column arrangement modeled — genuinely
  effect-specific and currently unmodeled for ALL effects.
- **Per-constraint residual degrees** — a real per-effect quantity (transferV3's gates are low-degree;
  a hash-round or range-decomposition effect has higher-degree residuals, hence a looser ε). But it is
  `natDegree` of the residual — a different number, not a different proof.

---

## 3. The automation that makes the 27-rollout a FAN-OUT

**The strongest result: no macro is strictly needed for the OOD core — it is already ONE `∀ d`
theorem.** The 27-rollout's OOD/hood/MainAirAccept work is `@mainAirAcceptF_of_floor <descriptor>`, 27
instantiations of a proven lemma. That is the fan-out: the crypto composition is written ONCE.

What a `derive_stark_sound_for <descriptor>` command (a `macro`/elaborator) would still usefully
generate is the thin per-effect SHELL around that core:

- **Takes in:** a descriptor `d` (name), its committed assembler
  (`algoStarkSound_of_bricks_<d>` for mem-free, or `algoStarkSound_of_bricks` + the effect's memory-leg
  proofs), and its `airAccept_forces_satisfied2_<d>` bridge.
- **Emits, by textual substitution of `d` into fixed templates:**
  1. `FriLdtExtract_d` (the bundle — copy-swap of §1f);
  2. `algoStarkSound_d : Poseidon2SpongeCR sponge → FriLdtExtract_d … → AlgoStarkSound hash (fun _ => d) …`
     — the `intro/obtain/exact ⟨t, mainAirAcceptF_of_floor d …, aux⟩` wrapper (fixed skeleton);
  3. the two ε-bound teeth (`hnonexc_is_bounded_fs_form_d`, `rlc_lambda_is_bounded_fs_form_d`).
- **Eliminates per effect:** the entire hood-discharge (§1c, the crypto bulk), the column-layout map
  (§1a/b), the MainAirAccept landing (§1d), and the ε-bound teeth (§1e) — i.e. essentially ALL the
  soundness-composition code. What it CANNOT eliminate is §2: the effect's assembler-leg discharge
  (memory-checking / hash-site / range faithfulness for memory-touching effects) and, if one chooses to
  discharge rather than assume it, the effect's column-layout truth.

**Buildable?** Yes, and cheaply — because the hard part (a descriptor-polymorphic core theorem) is
already built and green. The command is a `syntax`/`macro_rules` that expands `derive_stark_sound_for foo`
into (2)+(3) with `foo` spliced in; the semantic content is `mainAirAcceptF_of_floor foo`, which already
typechecks for any `foo : EffectVmDescriptor2`. A mem-free effect is a pure fan-out (the command emits a
complete instance). A memory-touching effect is a fan-out MINUS the §2 memory-leg proofs, which remain
irreducible manual work (the same manual work `AirLegsDischarged` already does per descriptor).

**Honest bottom line.** The OOD/FRI-soundness half of the STARK completion is NOT 27 deathmarches — it is
one proven `∀ d` theorem plus 27 one-line instantiations (a `derive_stark_sound_for` macro is convenience,
not necessity). The genuinely-per-effect residue is the memory-checking / table-faithfulness leg discharge
for the ~half of effects that touch memory, plus the (shared, currently-assumed) column-layout and LogUp
floors. Those are real, but they are bounded and templated, not a per-effect reinvention of the STARK
argument.

---

## 4. Cross-reference

- The completed instance + discharged reductions: `metatheory/Dregg2/Circuit/AlgoStarkSoundTransferV3.lean`
  (`algoStarkSound_transferV3`, `mainAirAcceptF_of_floor`, `hood_of_reductions`; kernel-clean,
  `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}).
- The proven reductions it wires: `OodQuotientConsistency.verifyAlgo_accept_forces_table_identity`,
  `OodCommitmentBinding.commitmentOpening_binds_of_poseidon2CR`, `OodSoundnessGame.rlc_debatch` /
  `ood_hnonexc_escape_prob_le`, `FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals`.
- The residual-floor map it completes: `docs/reference/STARK-FLOOR-REDUCTION.md`.
- The general (all-eight-leg) assembler for memory-touching effects:
  `AlgoStarkSoundInstance.algoStarkSound_of_bricks`.
