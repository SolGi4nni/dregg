# VaultSatDescriptor carry-wrap — soundness investigation

Origin: census commit `3af80047f` flagged a POSSIBLE deployed soundness gap after the ℤ→mod-p
field-faithfulness migration. This doc resolves it.

**VERDICT: (A) REAL SOUNDNESS GAP in the circuit as written — the 16-bit carry range check admits a
mod-p wrap that lets a DILUTING vault deposit satisfy the no-dilution gate.** The deployed Rust and
the Lean model AGREE (both `CARRY_BITS = 16`), so this is NOT model-only (B) and NOT
safe-by-reconstruction (C). Mitigating fact: the tag-19 vault gadget is **STAGED, not yet flipped
into the live VK** (both headers say so), so it is a latent gap that MUST be closed before the
big-bang regen deploys it — not a currently-live-routed production hole. Severity: HIGH (fix before
flip).

The clean fix is `CARRY_BITS: 16 → 15` in BOTH files. It is faithful (honest carries provably fit 15
bits) and it restores the `< p` invariant the design's own header claims.

---

## 1. The Lean gate + carry structure (quoted)

`metatheory/Dregg2/Deos/VaultSatDescriptor.lean`:

- `LIMB_BITS = 15` (line 74), `CARRY_BITS = 16` (line 76), `TWO15 = 32768` (line 78).
- The overflow-safe schoolbook product (`productGates`, lines 156-163), gate **B**:
  ```
  selGate ( (x1·y0 + ca) − t1 − 2^15·cb )      -- residual R_B = x1·y0 + ca − t1 − 2^15·cb
  ```
- `rangeSpecs` (lines 122-129) range-checks the four cross-term carries to `CARRY_BITS`:
  `(PCB, CARRY_BITS), (PCC, CARRY_BITS)` and `(QCB, CARRY_BITS), (QCC, CARRY_BITS)` = **16 bits**;
  every other limb/carry (`PCA`, `QCA`, all `Z`/`W`/operand limbs) is `LIMB_BITS = 15`.
- `vaultSatV3_forces` (lines 318-441) reconstructs the ℤ product via
  `linear_combination hPA + 32768*hPB + 32768*hPC + 1073741824*hPD` (line 407) — this needs each gate
  residual to be **exactly 0 over ℤ**, not merely `≡ 0 mod p`.

Post-migration, a `.base (.gate body)` is satisfied iff `body.eval env ≡ 0 [ZMOD 2013265921]`
(`DescriptorIR2.lean:374-376`; `DecideSatisfied2.lean:69-70`). So the `linear_combination` step is
no longer discharged — the migration correctly EXPOSED the gap the old exact-ℤ `Satisfied2` hid.

## 2. The deployed Rust carry width (file:line)

`circuit/src/effect_vm/vault_weld.rs`:
- `pub const CARRY_BITS: usize = 16;` — **line 76**.
- `range_specs()` (lines 140-173): `let c = CARRY_BITS;` and `(PCB, c), (PCC, c), (QCB, c), (QCC, c)`
  — lines **157-158, 165-166**. The cross-term carries are range-checked to **16 bits** in the
  deployed prover, byte-for-byte matching the Lean.
- `product_gates` (lines 268-300) is the identical gate B `x1·y0 + ca − t1 − 2^15·cb`.

The Lean is a FAITHFUL mirror of the deployed circuit. Case (B) is refuted: the deployed does not use
a tighter width.

## 3. Max single-gate residual vs p

`p = 2013265921 = 2^15·61440 + 1` (BabyBear). Limbs `< 2^15`; `PCA/QCA` (`ca`) `< 2^15`.

**With the deployed 16-bit cross carry (`cb < 2^16`):** gate B residual
`R_B = x1·y0 + ca − t1 − 2^15·cb`.
- max `= x1·y0 + ca ≤ (2^15−1)^2 + (2^15−1) = 2^30 − 2^15 = 1073709056 < p`.
- min `= −t1 − 2^15·cb ≥ −(2^15−1) − 2^15·(2^16−1) = −(2^31−1) = −2147483647 < −p`.

The window `[−(2^31−1), 2^30−2^15]` has width `> p`, and it CONTAINS a nonzero multiple of p, namely
`−p`. So `R_B ≡ 0 [ZMOD p]` does **not** force `R_B = 0` over ℤ: `R_B ∈ {0, −p}`. Concretely (finding's
witness, operands 0): `x1=y0=ca=0, t1=1, cb=61440` gives `R_B = −(1 + 2^15·61440) = −p ≡ 0 [ZMOD p]`,
with `t1=1 < 2^15` and `cb=61440 < 2^16` both passing their range checks (`61440 > 2^15` — it needs
the 16th bit the loose check grants).

**With a 15-bit carry (`cb < 2^15`):** min `R_B = −(2^15−1) − 2^15(2^15−1) = −(2^30−1) > −p`; max
`= 2^30 − 2^15 < p`. So `R_B ∈ (−p, p)` → the only multiple of p is 0 → `R_B = 0` over ℤ. SOUND. Gate
C (uses `PCC`/`QCC`, 16-bit) wraps identically; gate D and the borrow/operand gates already stay
`(−p, p)`.

## 4. Exploitability (why it is a real forgery, not just a broken proof)

The exploit targets the `Q = Sa·d` product of a **diluting** deposit (true `Ta·m > Sa·d`). Because
the schoolbook reconstruction telescopes to
`Z_limbs = X·Y − (R_A + 2^15 R_B + 2^15 R_C + 2^30 R_D)`, and the only reachable wrap is `R_B = −p`
(the positive side stays `< p`), the forged LIMB value comes out LARGER than the true product:
`Q_limbs = Sa·d + 2^15·p`. A malicious prover picks, relative to the
honest `Sa·d` witness: `QT1 += 1`, `QCB += 61440`, `Q1 += 1`, `Q2 += 28672`, `Q3 += 1`. Check:
`2^15 + 28672·2^30 + 2^45 = 65970697699328 = 2^15·p` exactly. All columns stay in range for small
`Sa,d` (honest `cb,z2 < 4096`), gates A/C/D hold over ℤ, gate B holds mod p (residual `−p`), and the
16-bit `QCB` check admits `61440`.

Now `Q_limbs = Sa·d + 2^15·p ≈ 2^46` is astronomically larger than `P_limbs = Ta·m`. The 4-limb
borrow comparison `P_limbs ≤ Q_limbs` is genuinely TRUE over ℤ (both from valid 15-bit limbs), so the
honest borrow subtraction yields `bb3 = 0` — the no-dilution gate PASSES on a diluting deposit. Every
AIR constraint is satisfied mod p, so the STARK verifier ACCEPTS a forged (share-inflating,
value-extracting) vault settlement. Nothing else pins `QCB`: the only consumers of `PCB/PCC/QCB/QCC`
are their 16-bit range check and product gates B/D — no global reconstruction invariant recovers
soundness. Case (C) is refuted.

(The off-AIR `verify.rs VAULT_DEPOSIT` arm uses `u128` and is unaffected — but it is not what the
STARK enforces; the AIR gates are.)

## 5. The fix

`CARRY_BITS: 16 → 15` in BOTH:
- `circuit/src/effect_vm/vault_weld.rs:76`
- `metatheory/Dregg2/Deos/VaultSatDescriptor.lean:76`

Faithfulness of the tightening: for operands in `[0, 2^30)`, every honest carry fits 15 bits —
`ca ≤ 2^15−2`, `cb ≤ 2^15−2`, `cc ≤ 2^15−1`, top limb `z3 ≤ 2^15−1`. So no honest proof is lost, and
the header's own claim ("every constraint polynomial stays `< p`", vault_weld.rs:28-29) becomes TRUE
— it is currently FALSE on the negative excursion `−2^15·cb` when `cb` is allowed 16 bits. The `16`
("one bit past the limb width") was an over-loose bound that is simultaneously unnecessary and the
exact soundness hole. After the fix, `vaultSatV3_forces`'s `linear_combination` reconstruction
discharges again under the mod-p `Satisfied2`, and the mod-p lift is sound.

**Do the Rust and Lean edits together** (they are byte-for-byte twins). Re-run the vault_weld tests
(honest / large-overflow / inflation / no-deposit / dilution) and the Lean `#guard`/`#assert_all_clean`
to confirm honest proofs survive and the teeth still bite.

## ✅ FIX APPLIED (2026-07-11, claude — ember said "we should do them"; I over-gated calling it a decision)
- SOURCE FIX (the load-bearing part): `CARRY_BITS 16 → 15` in BOTH twins (`circuit/src/effect_vm/vault_weld.rs:76`
  + `Dregg2/Deos/VaultSatDescriptor.lean:76`). I VERIFIED the honest-carry bound myself from the actual gates
  (operands are 15-bit limbs, LIMB_BITS=15): cA,cB ≤ 2^15−2, cC ≤ 2^15−1 — every honest carry fits 15 bits, so the
  tightening rejects ZERO honest proofs (no liveness cost) while rejecting the wrap witness (cb=61440 > 2^15). Max
  residual now 2^30−1 < p ⟹ the mod-p→ℤ lift is SOUND (was unsound at 16 bits — the gap).
- LEAN PROOF: VaultSatDescriptor's conservation is now PROVABLE (the 15-bit range checks DERIVE the residual bound;
  no assumed reconExact). Completion lane in flight — will go from RED to GREEN, the proof that the fix works.
- REMAINING (scoped, staged-epoch): the staged descriptor (`vaultSatVmDescriptor2R24`, the row of
  `circuit/descriptors/rotation-v3-staged-registry.tsv` that `gentian_discharge_vault_prove.rs` reads) is stale
  (range_specs emit 15 not 16) and needs re-emission. ⚑ 2026-07-31: this used to name the
  `circuit/tests/fixtures/vault-sat-v3-staged.json` COPY, which is now DELETED — it had drifted 112 columns and
  304 constraints behind the registry row. This belongs with the tag-19 VK epoch regeneration (the vault "rides the big-bang flip", not
  live). Not a blocker on the soundness fix — the gap is closed at the source.
