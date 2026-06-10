/-
# Dregg2.Circuit.Emit.EffectVmEmitRecordRoot — RECORD-LAYER STAGE 2: absorb the user-field-map
`fields_root` into the EffectVM state-commitment (the GROUP-4 hash chain), with the anti-ghost tooth.

## What this module discharges

`_RECORD-LAYER-UPGRADE.md` §B.5 / §E Stage 2: the EffectVM circuit must bind the committed
user-field-map root (`Exec.FieldsMap.fieldsRoot`, the unbounded `key ≥ 8` overflow accumulator) into
the per-row `state_commit`, so that a verifier binds the WHOLE record — not only the 8 fixed
`fields[0..7]` cells. STAGE 1 (`Dregg2.Exec.RecordCommit`) folded `fields_root` into the *cell-canonical*
commitment; STAGE 2 folds it into the *EffectVM circuit* `state_commit`.

The deliverable is **width-neutral** (the 186-col EffectVM layout is unchanged). It reuses the single
state-block column GROUP-4 currently leaves UNABSORBED — the `RESERVED` cell (the
`EffectVmEmitTransferSound.reserved_not_bound_by_commitment` finding named it the lone un-hashed cell)
— as the `fields_root` carrier (`state.FIELDS_ROOT`), and absorbs it into GROUP-4 **site 3's
previously-spare 4th input** (`_IR-EXTENSION-DESIGN.md:23,158-162`, the reserved overflow-root slot).
No new column, no new `VmConstraint` kind, no new `VmHashSite` mechanism — the SAME ordered-site walk
the transfer keystone proves.

## The three teeth (mirroring `EffectVmEmitTransferSound`)

  1. `recordHash_binds` — a satisfying record-GROUP-4 site set forces `state_commit` to the genuine
     `H4`-of-`H4` digest of the 13 absorbed columns INCLUDING `fields_root` (site 3's 4th input now
     reads `FIELDS_ROOT`, not the literal `0`).
  2. `recordDescriptor_commit_binds_fieldsRoot` — THE ANTI-GHOST TOOTH: under `Poseidon2SpongeCR`,
     two rows that satisfy the record sites and publish the SAME `state_commit` have the SAME
     `fields_root`. Contrapositive: tampering a committed map field (which moves `fields_root`, off
     `Exec.FieldsMap.fieldsRoot_binds_tail`) MOVES `state_commit` ⇒ the published `NEW_COMMIT` pin is
     UNSAT. The map is bound (a `fields_root := 0` stub would collapse this — forbidden).
  3. NON-VACUITY — a concrete honest row whose absorbed `fields_root` differs from a tampered row's,
     refuting any shared-`state_commit` satisfaction under CR (the anti-ghost end-to-end), AND the
     legacy NO-OP (`fields_root = 0` ⇒ the record sites coincide byte-for-byte with the transfer
     sites, so STAGE 2 is backward-compatible).

## The transfer-keystone LIFT (backward compatibility, re-proved)

`recordSites_eq_transferSites_on_legacy`: when the carrier `fields_root = 0` (every legacy /
non-map-write row), the record-GROUP-4 site set is DEFINITIONALLY the transfer site set, so the whole
transfer keystone (`transferVm_faithful`, `transferDescriptor_commit_binds_state`, …) holds verbatim
for the record descriptor on legacy rows. STAGE 2 strictly EXTENDS the binding (adds `fields_root`)
without weakening the transfer guarantee.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY
as the NAMED `Poseidon2Binding.Poseidon2SpongeCR hash` (task #13's discharged carrier). No `sorry`,
no `:= True`, no `native_decide`. Imports are read-only; the transfer descriptor / sites are reused,
never edited.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.Emit.EffectVmEmitRecordRoot

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option linter.unusedVariables false

/-! ## §1 — The RECORD-LAYER GROUP-4 sites: site 3 absorbs `fields_root`.

The first three sites (`site0`/`site1`/`site2`) are REUSED VERBATIM from `EffectVmEmitTransfer` — they
already absorb the balance limbs, nonce, all 8 fields, and cap_root. The ONLY change is site 3: its
4th input, the spare `.zero` slot, now reads `state_after.FIELDS_ROOT` (the committed map root carried
in the `RESERVED` column). This is the `_IR-EXTENSION-DESIGN.md:23` overflow-root slot, the
`_RECORD-LAYER-UPGRADE.md:210` spare GROUP-4 absorb position. -/

/-- Record-layer site 3: `state_commit = H4(inter1, inter2, inter3, fields_root)`. The 4th input
(previously `.zero` in `EffectVmEmitTransfer.site3`) now reads `state_after.FIELDS_ROOT`, binding the
user-field-map root into the published commitment. -/
def recordSite3 : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .col (saCol state.FIELDS_ROOT) ]
  , arity := 4 }

/-- The ordered record-layer GROUP-4 sites: the transfer sites 0/1/2 (verbatim) followed by the
`fields_root`-absorbing site 3. Site order is load-bearing (site 3 reads sites 0/1/2's digests). -/
def recordHashSites : List VmHashSite := [site0, site1, site2, recordSite3]

/-! ## §2 — `recordHash_binds`: the published commitment IS the genuine digest of the after-state
INCLUDING `fields_root`. -/

/-- A satisfying record-site set forces `state_commit` to the genuine `H4`-of-`H4` digest of the 13
absorbed columns — the SAME 12 as transfer PLUS the `fields_root` cell in the final slot. The site
ORDER is load-bearing: site 3 reads sites 0/1/2's digests, exactly as the running prover's
`digests[3] = H4(digests[0], digests[1], digests[2], fields_root)`. -/
theorem recordHash_binds (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env recordHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = hash [ hash [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI)
                    , env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
                    , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
                    , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ]
             , env.loc (saCol state.FIELDS_ROOT) ] := by
  unfold siteHoldsAll recordHashSites at h
  simp only [siteHoldsAll.go, site0, site1, site2, recordSite3, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil, List.getD] at h
  obtain ⟨h0, h1, h2, h3, _⟩ := h
  rw [h3]
  rfl

/-! ## §3 — The absorbed columns (now 13: the 12 transfer columns + `fields_root`). -/

/-- The 13 absorbed columns of an after-state under the record sites, in site order:
`[bal_lo, bal_hi, nonce, fld0..fld7, cap_root, fields_root]`. -/
def recordAbsorbedCols (env : VmRowEnv) : List ℤ :=
  [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI), env.loc (saCol state.NONCE)
  , env.loc (saCol (state.FIELD_BASE + 0))
  , env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
  , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4))
  , env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
  , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT)
  , env.loc (saCol state.FIELDS_ROOT) ]

/-- The commitment as a direct scalar function of the 13 absorbed columns (the RHS of
`recordHash_binds`, written without a list match so it computes by `rfl`). -/
def recordCommitOf (hash : List ℤ → ℤ)
    (bLo bHi n f0 f1 f2 f3 f4 f5 f6 f7 cap fr : ℤ) : ℤ :=
  hash [ hash [bLo, bHi, n, f0], hash [f1, f2, f3, f4], hash [f5, f6, f7, cap], fr ]

/-- The published commitment IS `recordCommitOf` of the 13 absorbed columns (a repackaging of
`recordHash_binds`). -/
theorem recordCommit_eq_commitOf (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env recordHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = recordCommitOf hash
          (env.loc (saCol state.BALANCE_LO)) (env.loc (saCol state.BALANCE_HI))
          (env.loc (saCol state.NONCE)) (env.loc (saCol (state.FIELD_BASE + 0)))
          (env.loc (saCol (state.FIELD_BASE + 1))) (env.loc (saCol (state.FIELD_BASE + 2)))
          (env.loc (saCol (state.FIELD_BASE + 3))) (env.loc (saCol (state.FIELD_BASE + 4)))
          (env.loc (saCol (state.FIELD_BASE + 5))) (env.loc (saCol (state.FIELD_BASE + 6)))
          (env.loc (saCol (state.FIELD_BASE + 7))) (env.loc (saCol state.CAP_ROOT))
          (env.loc (saCol state.FIELDS_ROOT)) := by
  have hb := recordHash_binds hash env h
  rw [hb]; rfl

/-! ## §4 — THE ANTI-GHOST TOOTH: the commitment binds `fields_root`. -/

/-- **`recordAbsorbed_determined_by_commit` — the injective-commitment core (with `fields_root`).**
Under `Poseidon2SpongeCR hash`, two after-states whose published `state_commit`s are EQUAL have
identical absorbed-column lists — INCLUDING `fields_root`. CR peels the outer `hash` (the 4-list,
whose 4th element is now `fields_root`), then peels each inner `hash`. -/
theorem recordAbsorbed_determined_by_commit (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ recordHashSites)
    (hs₂ : siteHoldsAll hash e₂ recordHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    recordAbsorbedCols e₁ = recordAbsorbedCols e₂ := by
  rw [recordCommit_eq_commitOf hash e₁ hs₁, recordCommit_eq_commitOf hash e₂ hs₂] at hcommit
  unfold recordCommitOf at hcommit
  -- CR on the outer hash gives the 4-element list equal (4th element is fields_root).
  have houter := hCR _ _ hcommit
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at houter
  obtain ⟨hA, hB, hC, hFR, _⟩ := houter
  -- CR on each inner hash gives the 4-element field tuples equal.
  have hA' := hCR _ _ hA
  have hB' := hCR _ _ hB
  have hC' := hCR _ _ hC
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hA' hB' hC'
  obtain ⟨e_bLo, e_bHi, e_n, e_f0, _⟩ := hA'
  obtain ⟨e_f1, e_f2, e_f3, e_f4, _⟩ := hB'
  obtain ⟨e_f5, e_f6, e_f7, e_cap, _⟩ := hC'
  -- reassemble the 13-element absorbed lists (the 13th is fields_root, from hFR)
  unfold recordAbsorbedCols
  rw [e_bLo, e_bHi, e_n, e_f0, e_f1, e_f2, e_f3, e_f4, e_f5, e_f6, e_f7, e_cap, hFR]

/-- **`recordDescriptor_commit_binds_fieldsRoot` — THE ANTI-GHOST KEYSTONE.** Two rows that satisfy
the record GROUP-4 sites and publish the SAME `state_commit` have the SAME `fields_root`. Hence a
prover CANNOT keep the published commitment while tampering a committed map field: moving `fields_root`
(which `Exec.FieldsMap.fieldsRoot_binds_tail` guarantees a tampered map does) MOVES `state_commit`. The
user-field map is bound into the EffectVM commitment. -/
theorem recordDescriptor_commit_binds_fieldsRoot (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ recordHashSites)
    (hs₂ : siteHoldsAll hash e₂ recordHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (saCol state.FIELDS_ROOT) = e₂.loc (saCol state.FIELDS_ROOT) := by
  have h := recordAbsorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit
  -- the 13th list element is fields_root; extract it.
  unfold recordAbsorbedCols at h
  simp only [List.cons.injEq] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! ## §5 — The TRANSFER-KEYSTONE LIFT (backward compatibility, re-proved).

On a legacy / non-map-write row the `fields_root` carrier is `0`. There, the record-layer site 3 is
DEFINITIONALLY the same hash input as the transfer site 3's `.zero` (both resolve the 4th input to
`0`), so the record sites and the transfer sites produce IDENTICAL digests — the whole transfer
keystone lifts verbatim. We prove the resolved-input lists coincide (the load-bearing equality that
the digests, and hence every downstream binding, agree). -/

/-- **`recordSite3_resolves_as_transfer_on_legacy`.** When the carrier `fields_root = 0`, record
site 3's resolved inputs equal transfer site 3's resolved inputs (under any earlier-digest accumulator
`digs`). So the two site sets compute the SAME `state_commit` on a legacy row. -/
theorem recordSite3_resolves_as_transfer_on_legacy (env : VmRowEnv) (digs : List ℤ)
    (hlegacy : env.loc (saCol state.FIELDS_ROOT) = 0) :
    recordSite3.resolvedInputs env digs = site3.resolvedInputs env digs := by
  simp only [recordSite3, site3, VmHashSite.resolvedInputs, HashInput.resolve,
    List.map_cons, List.map_nil, hlegacy]

/-- **`recordSites_digest_eq_transfer_on_legacy`.** On a legacy row (`fields_root = 0`) the record
GROUP-4 sites and the transfer GROUP-4 sites bind the SAME published `state_commit` value — so STAGE 2
is byte-identical on legacy rows and the transfer keystone's commitment binding lifts unchanged. -/
theorem recordSites_digest_eq_transfer_on_legacy (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hlegacy : env.loc (saCol state.FIELDS_ROOT) = 0)
    (hT : siteHoldsAll hash env transferHashSites) :
    siteHoldsAll hash env transferHashSites ↔ siteHoldsAll hash env recordHashSites := by
  constructor
  · intro hTr
    -- both site sets reduce to the same chained digests; the record site 3's 4th input is 0=ZERO.
    unfold siteHoldsAll recordHashSites
    unfold siteHoldsAll transferHashSites at hTr
    simp only [siteHoldsAll.go, site0, site1, site2, site3, recordSite3,
      VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil, List.getD,
      hlegacy] at hTr ⊢
    exact hTr
  · intro hRec
    unfold siteHoldsAll transferHashSites
    unfold siteHoldsAll recordHashSites at hRec
    simp only [siteHoldsAll.go, site0, site1, site2, site3, recordSite3,
      VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil, List.getD,
      hlegacy] at hRec ⊢
    exact hRec

/-! ## §6 — The RECORD descriptor: the transfer descriptor with the `fields_root`-binding GROUP-4.

`recordVmDescriptor` is `transferVmDescriptor` with the hash-site list swapped for `recordHashSites`
(everything else — gates, transitions, boundary pins, ranges — identical). It is the runnable form the
STAGE-2 prover executes once a record / map-write row absorbs `fields_root`. Width-neutral: same 186
`traceWidth`, same constraint list. -/

/-- The STAGE-2 record descriptor: transfer descriptor + `fields_root`-binding GROUP-4 sites. -/
def recordVmDescriptor : EffectVmDescriptor :=
  { transferVmDescriptor with
    name := "dregg-effectvm-record-v1"
    hashSites := recordHashSites }

/-- The record descriptor is width-neutral: same 186-col trace width as transfer. -/
theorem recordVmDescriptor_width : recordVmDescriptor.traceWidth = EFFECT_VM_WIDTH := rfl

/-- The record descriptor's constraint list is EXACTLY the transfer descriptor's (only the hash sites
changed) — so every per-row gate / transition / boundary faithfulness theorem of the transfer keystone
applies verbatim to the record descriptor. -/
theorem recordVmDescriptor_constraints_eq :
    recordVmDescriptor.constraints = transferVmDescriptor.constraints := rfl

/-! ## §7 — NON-VACUITY: a concrete honest row and a tampered row (anti-ghost end-to-end).

We exhibit `recordGoodRow` (a transfer row carrying a NON-ZERO `fields_root = 555` — a populated user
map) and `recordTamperedRow` (the same but `fields_root` forged to `777`). Their absorbed-column lists
DIFFER in the `fields_root` slot, so no CR sponge admits both with the same published `state_commit`:
the map tamper is rejected by the commitment binding. This is the load-bearing anti-vacuity tooth — a
`fields_root := 0` stub would make the two rows' absorbed lists EQUAL (both `0`) and collapse the
guard (forbidden, `_RECORD-LAYER-UPGRADE.md` §D.4). -/

/-- An honest record row: `goodRow` extended with a NON-ZERO committed map root in the `FIELDS_ROOT`
carrier (`= 555`, a populated overflow map). -/
def recordGoodRow : VmRowEnv where
  loc := fun v => if v = saCol state.FIELDS_ROOT then 555 else goodRow.loc v
  nxt := goodRow.nxt
  pub := goodRow.pub

/-- A tampered record row: same as `recordGoodRow` but the committed map root forged to `777` (a map
value was changed, so `fields_root` moves off `FieldsMap.fieldsRoot_binds_tail`). -/
def recordTamperedRow : VmRowEnv where
  loc := fun v => if v = saCol state.FIELDS_ROOT then 777 else goodRow.loc v
  nxt := goodRow.nxt
  pub := goodRow.pub

/-- The carrier column index `saCol state.FIELDS_ROOT` is `87` (state_after base 76 + 13). The two
rows read `555` vs `777` there. -/
theorem recordRows_fieldsRoot :
    recordGoodRow.loc (saCol state.FIELDS_ROOT) = 555
    ∧ recordTamperedRow.loc (saCol state.FIELDS_ROOT) = 777 := by
  refine ⟨?_, ?_⟩
  · show (if saCol state.FIELDS_ROOT = saCol state.FIELDS_ROOT
            then (555:ℤ) else goodRow.loc (saCol state.FIELDS_ROOT)) = 555
    rw [if_pos rfl]
  · show (if saCol state.FIELDS_ROOT = saCol state.FIELDS_ROOT
            then (777:ℤ) else goodRow.loc (saCol state.FIELDS_ROOT)) = 777
    rw [if_pos rfl]

/-- **NON-VACUITY (anti-ghost, witness FALSE).** The honest and tampered rows' absorbed columns
DIFFER (in the `fields_root` slot), so they cannot share a published `state_commit` under CR. Concretely:
IF both satisfied the record sites with equal `state_commit`, `recordDescriptor_commit_binds_fieldsRoot`
would force `555 = 777` — absurd. So the commitment binding REJECTS the map tamper. -/
theorem recordTamper_rejected (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (hs₁ : siteHoldsAll hash recordGoodRow recordHashSites)
    (hs₂ : siteHoldsAll hash recordTamperedRow recordHashSites)
    (hcommit : recordGoodRow.loc (saCol state.STATE_COMMIT)
             = recordTamperedRow.loc (saCol state.STATE_COMMIT)) : False := by
  have h := recordDescriptor_commit_binds_fieldsRoot hash hCR recordGoodRow recordTamperedRow
    hs₁ hs₂ hcommit
  rw [recordRows_fieldsRoot.1, recordRows_fieldsRoot.2] at h
  exact absurd h (by decide)

/-- **NON-VACUITY (legacy NO-OP, witness TRUE).** `goodRow` (the transfer reference, whose
`FIELDS_ROOT`/`RESERVED` carrier is the `else 0` default) has `fields_root = 0`, so its record GROUP-4
sites coincide with its transfer GROUP-4 sites: STAGE 2 is byte-identical on the legacy reference row.
The legacy fold is a no-op (a populated-map row, `recordGoodRow`, is NOT — proved above). -/
theorem goodRow_fieldsRoot_zero : goodRow.loc (saCol state.FIELDS_ROOT) = 0 := by
  show goodRow.loc (saCol state.FIELDS_ROOT) = 0
  unfold goodRow
  -- the carrier column index is 89; it equals none of goodRow's named columns, so `loc` is `else 0`.
  norm_num [saCol, state.FIELDS_ROOT, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, sel.TRANSFER, sbCol, prmCol,
    state.BALANCE_LO, state.NONCE, param.AMOUNT, param.DIRECTION]

/-! ## §8 — Axiom-hygiene pins (the honesty tripwire). -/

#guard recordHashSites.length == 4
#guard recordVmDescriptor.traceWidth == 186
#guard recordVmDescriptor.hashSites.length == 4
-- 14 per-row gates + 14 transitions + 4 boundary-first + 3 boundary-last + 1 selector-binding
-- `sel[S]=1` tooth (task #74, added to `transferVmDescriptor` after this guard was first written;
-- inherited verbatim by `recordVmDescriptor` per `recordVmDescriptor_constraints_eq`). = 36.
#guard recordVmDescriptor.constraints.length == 14 + 14 + 4 + 3 + 1
-- The record site 3 absorbs the FIELDS_ROOT cell (col 87), NOT the literal zero:
#guard recordSite3.inputs == [HashInput.digest 0, HashInput.digest 1, HashInput.digest 2,
                              HashInput.col (saCol state.FIELDS_ROOT)]
-- The transfer site 3 STILL absorbs zero (transfer descriptor untouched / backward-compatible):
#guard site3.inputs == [HashInput.digest 0, HashInput.digest 1, HashInput.digest 2, HashInput.zero]

#assert_axioms recordHash_binds
#assert_axioms recordCommit_eq_commitOf
#assert_axioms recordAbsorbed_determined_by_commit
#assert_axioms recordDescriptor_commit_binds_fieldsRoot
#assert_axioms recordSite3_resolves_as_transfer_on_legacy
#assert_axioms recordSites_digest_eq_transfer_on_legacy
#assert_axioms recordVmDescriptor_width
#assert_axioms recordVmDescriptor_constraints_eq
#assert_axioms recordTamper_rejected
#assert_axioms goodRow_fieldsRoot_zero

end Dregg2.Circuit.Emit.EffectVmEmitRecordRoot
