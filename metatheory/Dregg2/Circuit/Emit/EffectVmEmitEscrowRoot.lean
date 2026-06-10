/-
# Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot — the GENUINE in-row `escrows`-list-digest recompute
(the shared class-A side-table primitive for the whole escrow/bridge-escrow family).

## Why this module exists (the class-A deepening)

The earlier escrow descriptors (`EffectVmEmitCreateEscrow.gEscrowRootUpdate:502`) bound the side-table
root by an ADDITIVE OPAQUE STEP: `sys_digest_after = sys_digest_before + step_param`, where `step_param`
is a FREE param column the prover supplies. That is NOT class A — a hostile prover can pick ANY `step`,
so the escrow root is *asserted*, not *recomputed*. The coverage ledger flags this exactly:

  > "the root advance is `SYS_DIG_AFTER = SYS_DIG_BEFORE + step_param` (additive opaque step), not a
  >  recomputed escrow-list digest." (`_CIRCUIT-ASSURANCE-PER-EFFECT.md:128`)

The class-A bar (`_CIRCUIT-ASSURANCE-PER-EFFECT.md:201` Tier-2 step (iii), ember's directive) is:

  > "replace the additive opaque root-STEP with an in-row recomputation of the genuine escrow-list digest
  >  so the new root is FORCED, not asserted." — `new_root = update(old_root, element)`, NOT a witnessed
  >  parameter.

This module supplies that recompute as a SHARED primitive, so createEscrow / refund / release /
committed / bridge-lock/finalize/cancel all inherit ONE genuine root recompute. The escrow side-table is
a `List EscrowRecord` whose committed root is `ListCommit.listDigest LE compressN` (the Poseidon sponge
of the per-record leaves). The runtime's escrow side-table is an APPEND/PREPEND accumulator: the new root
is `hash_2_to_1(record_leaf, old_root)` — the canonical prepend-accumulator advance (the SAME shape the
queue once used for FIFO append (its emit module died in F2a), but here the leaf is the escrow record).

## What this module BINDS (genuinely, in-row)

  1. **`siteEscrowLeaf`** — a hash-site that RECOMPUTES the parked record's leaf in-row:
     `record_leaf = hash[ id, creator, recipient, amount, asset, resolved ]`, where `amount` reads the
     SAME `param.AMOUNT` column that drives the balance debit (so the parked record's amount is FORCED to
     equal the debited amount — no amount-skew ghost), and `id/creator/recipient/asset/resolved` read
     dedicated param columns. The prover cannot choose the leaf freely; it is `hash` of the bound content.
  2. **`siteEscrowRootAdvance`** — a hash-site that RECOMPUTES the new root in-row:
     `new_root = hash[ record_leaf, old_root ]` — the genuine prepend-accumulator advance, reading the
     recomputed leaf (site above) and the OLD root carrier. The new root is FORCED by the old root + the
     bound record, not asserted.
  3. The new-root carrier is absorbed into `state_commit` (the per-effect file's GROUP-4 extension), so
     under `Poseidon2SpongeCR` a tampered record content / old root / new root provably MOVES
     `state_commit` ⇒ UNSAT (the anti-ghost tooth, `escrowRoot_binds_record` below).

## The genuine-recompute soundness (`escrowRootAdvance_forced`)

Under the two hash-sites, the new root carrier is UNIQUELY `hash[ hash[recordTuple], old_root ]` — a
DETERMINISTIC FUNCTION of (the bound record fields, the old root). No free `step` parameter survives. So:

  * **forced**: two rows with the SAME record fields AND the same old root have the SAME new root
    (`escrowRootAdvance_forced`) — the recompute is a function, not a choice;
  * **anti-ghost on the record**: under CR, two rows publishing the same new root that recompute it
    honestly have the SAME record-leaf-tuple AND the same old root (`escrowRoot_binds_record`) — so
    tampering ANY parked-record field (amount/recipient/…) or the old root changes the new root.

This is what the opaque step could never give: the root is now a genuine recomputation of the escrow-list
digest advance, FORCED by the bound record content (whose amount IS the debited amount).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the param columns that carry the parked `EscrowRecord` content.

The runtime trace generator lays the escrow record's fields in the param block. `param.AMOUNT = 0` is
SHARED with the balance debit (the parked amount IS the debited amount — load-bearing). The remaining
record fields take dedicated param columns 2..6 (param 1 = `DIRECTION`, reserved). All in `[0, NUM_PARAMS)`. -/

namespace ep
/-- The escrow `id` param column. -/
def ID        : Nat := 2
/-- The escrow `creator` (cell id) param column. -/
def CREATOR   : Nat := 3
/-- The escrow `recipient` (cell id) param column. -/
def RECIPIENT : Nat := 4
/-- The escrow `asset` (asset id) param column. -/
def ASSET     : Nat := 5
/-- The escrow `resolved` flag param column (0 on create, 1 on resolve). -/
def RESOLVED  : Nat := 6
end ep

/-- The escrow `amount` param column — the SAME `param.AMOUNT` that drives the balance debit. The parked
record's amount is therefore FORCED equal to the moved amount (no amount-skew ghost). -/
def AMOUNT : Nat := param.AMOUNT

/-! ## §1 — the in-row carriers for the recomputed leaf + old/new roots.

These are aux columns (past the state/param blocks). `ESCROW_LEAF` carries the recomputed record leaf;
`SYS_DIG_BEFORE` the old escrow-list root; `SYS_DIG_AFTER` the recomputed new root (the carrier the
per-effect file absorbs into `state_commit`). They are DISTINCT from every claimed slot. -/

/-- The recomputed escrow-record-leaf carrier (`hash[id,creator,recipient,amount,asset,resolved]`). An aux
column PAST the state-inter block (`auxCol aux_off.STATE_INTER3 = AUX_BASE + 10 = 100`), so it never
aliases a state-inter, the balance-bit block, or the system-roots digest carriers; well within
`EFFECT_VM_WIDTH = 186`. -/
def ESCROW_LEAF : Nat := auxCol aux_off.STATE_INTER3 + 1

/-- The OLD escrow-list root carrier (the pre-image of the accumulator advance). -/
def SYS_DIG_BEFORE : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST + 1

/-- The recomputed NEW escrow-list root carrier (the carrier `state_commit` absorbs). This is the IR's
`aux_off_sys.SYSTEM_ROOTS_DIGEST` (= 96): on an escrow row it holds the genuine advanced root. -/
def SYS_DIG_AFTER : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST

/-! ## §2 — the two RECOMPUTE hash-sites (the genuine update — NOT an additive step). -/

/-- **`siteEscrowLeaf`** — recompute the parked record's leaf in-row:
`record_leaf = hash[ id, creator, recipient, amount, asset, resolved ]`. The `amount` input is
`prmCol AMOUNT` = `prmCol param.AMOUNT` (shared with the debit). Arity 6. -/
def siteEscrowLeaf : VmHashSite :=
  { digestCol := ESCROW_LEAF
  , inputs := [ .col (prmCol ep.ID), .col (prmCol ep.CREATOR), .col (prmCol ep.RECIPIENT)
              , .col (prmCol AMOUNT), .col (prmCol ep.ASSET), .col (prmCol ep.RESOLVED) ]
  , arity := 6 }

/-- **`siteEscrowRootAdvance`** — recompute the new root in-row:
`new_root = hash[ record_leaf, old_root ]` — the genuine prepend-accumulator advance, reading the
recomputed leaf carrier and the OLD root carrier. Arity 2 (a 2-to-1 compression). The new root is FORCED
by `(record_leaf, old_root)` — no free step parameter. -/
def siteEscrowRootAdvance : VmHashSite :=
  { digestCol := SYS_DIG_AFTER
  , inputs := [ .col ESCROW_LEAF, .col SYS_DIG_BEFORE ]
  , arity := 2 }

/-- The escrow-root recompute sites, in order (leaf first — the advance reads it). These are appended to
the per-effect descriptor's GROUP-4 commitment sites; the per-effect file's `state_commit` site then
absorbs `SYS_DIG_AFTER`. -/
def escrowRecomputeSites : List VmHashSite := [ siteEscrowLeaf, siteEscrowRootAdvance ]

/-! ## §3 — the recomputed values as pure functions (what the sites FORCE). -/

/-- The record-leaf as a function of the six bound fields (the unique `hash` image the leaf site forces). -/
def leafOf (hash : List ℤ → ℤ) (id creator recipient amount asset resolved : ℤ) : ℤ :=
  hash [ id, creator, recipient, amount, asset, resolved ]

/-- The advanced root as a function of (record-leaf, old-root): the unique `hash` image the advance site
forces. NO free step survives — the new root IS `hash[leaf, old]`. -/
def advanceOf (hash : List ℤ → ℤ) (leaf oldRoot : ℤ) : ℤ := hash [ leaf, oldRoot ]

/-! ## §4 — `escrowRootHolds`: the two recompute sites hold on `env`.

A standalone predicate so a per-effect file can state "the escrow recompute holds" without re-deriving
the site walk. It is exactly `siteHoldsAll` on `escrowRecomputeSites` started from an empty digest acc. -/

/-- The escrow recompute holds on `env`: both recompute sites carry their genuine digests. -/
def escrowRootHolds (hash : List ℤ → ℤ) (env : VmRowEnv) : Prop :=
  siteHoldsAll hash env escrowRecomputeSites

/-- **`escrowLeaf_forced`** — under the recompute, the leaf carrier IS `hash` of the six bound fields. -/
theorem escrowLeaf_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : escrowRootHolds hash env) :
    env.loc ESCROW_LEAF
      = leafOf hash (env.loc (prmCol ep.ID)) (env.loc (prmCol ep.CREATOR))
          (env.loc (prmCol ep.RECIPIENT)) (env.loc (prmCol AMOUNT))
          (env.loc (prmCol ep.ASSET)) (env.loc (prmCol ep.RESOLVED)) := by
  unfold escrowRootHolds escrowRecomputeSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteEscrowLeaf, siteEscrowRootAdvance, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨h0, _⟩ := h
  rw [h0]; rfl

/-- **`escrowRootAdvance_forced`** — under the recompute, the NEW root carrier IS `hash[ leaf, old ]` where
`leaf` is itself `hash` of the bound fields. So the new root is a DETERMINISTIC FUNCTION of the bound
record content + the old root — the genuine recompute. NO opaque step. -/
theorem escrowRootAdvance_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : escrowRootHolds hash env) :
    env.loc SYS_DIG_AFTER
      = advanceOf hash
          (leafOf hash (env.loc (prmCol ep.ID)) (env.loc (prmCol ep.CREATOR))
            (env.loc (prmCol ep.RECIPIENT)) (env.loc (prmCol AMOUNT))
            (env.loc (prmCol ep.ASSET)) (env.loc (prmCol ep.RESOLVED)))
          (env.loc SYS_DIG_BEFORE) := by
  have hleaf := escrowLeaf_forced hash env h
  unfold escrowRootHolds escrowRecomputeSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteEscrowLeaf, siteEscrowRootAdvance, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil, List.getD] at h
  obtain ⟨_, h1, _⟩ := h
  -- site1 reads the digest of site0 (`digest 0`) for ESCROW_LEAF? No — it reads `.col ESCROW_LEAF`.
  -- So h1 : env.loc SYS_DIG_AFTER = hash [env.loc ESCROW_LEAF, env.loc SYS_DIG_BEFORE].
  rw [h1, hleaf]; rfl

/-! ## §5 — THE ANTI-GHOST: the recomputed root BINDS the record content + old root.

Under `Poseidon2SpongeCR`, two rows whose recompute holds and whose NEW root carriers are EQUAL have:
(a) the same old root, and (b) the same six bound record fields. So a prover CANNOT keep the published new
root while tampering the parked amount / recipient / id / asset / resolved flag / old root. This is the
genuine class-A tooth the opaque step lacked. -/

/-- **`escrowRoot_binds_record` — THE genuine-recompute anti-ghost.** Two recompute-honest rows with EQUAL
new-root carriers share the old root AND every bound record field. Off `Poseidon2SpongeCR`: peel the outer
advance hash (`[leaf, old]` equal) then the inner leaf hash (`[id,creator,recipient,amount,asset,resolved]`
equal). Tampering ANY of them moves the new root. -/
theorem escrowRoot_binds_record (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (h₁ : escrowRootHolds hash e₁) (h₂ : escrowRootHolds hash e₂)
    (hroot : e₁.loc SYS_DIG_AFTER = e₂.loc SYS_DIG_AFTER) :
    e₁.loc SYS_DIG_BEFORE = e₂.loc SYS_DIG_BEFORE
    ∧ e₁.loc (prmCol ep.ID) = e₂.loc (prmCol ep.ID)
    ∧ e₁.loc (prmCol ep.CREATOR) = e₂.loc (prmCol ep.CREATOR)
    ∧ e₁.loc (prmCol ep.RECIPIENT) = e₂.loc (prmCol ep.RECIPIENT)
    ∧ e₁.loc (prmCol AMOUNT) = e₂.loc (prmCol AMOUNT)
    ∧ e₁.loc (prmCol ep.ASSET) = e₂.loc (prmCol ep.ASSET)
    ∧ e₁.loc (prmCol ep.RESOLVED) = e₂.loc (prmCol ep.RESOLVED) := by
  rw [escrowRootAdvance_forced hash e₁ h₁, escrowRootAdvance_forced hash e₂ h₂] at hroot
  unfold advanceOf leafOf at hroot
  -- outer advance: hash [leaf₁, old₁] = hash [leaf₂, old₂]
  have houter := hCR _ _ hroot
  rw [List.cons.injEq, List.cons.injEq] at houter
  obtain ⟨hleafEq, hold, _⟩ := houter
  -- inner leaf: hash [id₁,creator₁,recipient₁,amount₁,asset₁,resolved₁] = hash [id₂,…]
  have hinner := hCR _ _ hleafEq
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq,
    List.cons.injEq] at hinner
  obtain ⟨hid, hcre, hrec, hamt, hasset, hres, _⟩ := hinner
  exact ⟨hold, hid, hcre, hrec, hamt, hasset, hres⟩

/-- **`escrowRoot_amount_bound` — the load-bearing corollary.** Two recompute-honest rows with the same
new root have the SAME parked amount. Since the same `param.AMOUNT` column drives the balance debit, the
parked record's amount IS the debited amount — bound by the commitment, no skew. -/
theorem escrowRoot_amount_bound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (h₁ : escrowRootHolds hash e₁) (h₂ : escrowRootHolds hash e₂)
    (hroot : e₁.loc SYS_DIG_AFTER = e₂.loc SYS_DIG_AFTER) :
    e₁.loc (prmCol AMOUNT) = e₂.loc (prmCol AMOUNT) :=
  (escrowRoot_binds_record hash hCR e₁ e₂ h₁ h₂ hroot).2.2.2.2.1

/-! ## §6 — NON-VACUITY: a concrete recompute fires; a tampered amount moves the root.

We use a concrete injective toy sponge (Horner) so the recompute is genuinely computable and a tampered
record provably yields a DIFFERENT new root. (The soundness theorems above use the abstract CR sponge; the
vacuity guard exhibits a realizable witness — the recompute is not vacuously satisfiable.) -/

/-- A concrete injective-enough toy sponge for the vacuity guards (Horner with a length tag). Exported so
downstream class-A files can re-use the concrete witness `goodEscrowRow_recomputes`. -/
def cN : List Int → Int := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : Int)

/-- A concrete escrow row: id=7 (col 70), creator=11 (col 71), recipient=13 (col 72), amount=30 (col 68),
asset=2 (col 73), resolved=0 (col 74), old_root=1000 (col 97). The leaf carrier (col 101) and new-root
carrier (col 96) hold the GENUINE recomputed values, so the recompute holds. Columns are the literal
indices `prmCol`/`SYS_DIG_*`/`ESCROW_LEAF` reduce to (checked by `#guard`s in §7). -/
def goodEscrowRow : VmRowEnv where
  loc := fun v =>
    if v = 70 then 7
    else if v = 71 then 11
    else if v = 72 then 13
    else if v = 68 then 30
    else if v = 73 then 2
    else if v = 74 then 0
    else if v = 97 then 1000
    else if v = 101 then cN [7, 11, 13, 30, 2, 0]
    else if v = 96 then cN [cN [7, 11, 13, 30, 2, 0], 1000]
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

-- The witness row's literal columns ARE the symbolic carrier columns (anti-drift).
#guard prmCol ep.ID == 70
#guard prmCol ep.CREATOR == 71
#guard prmCol ep.RECIPIENT == 72
#guard prmCol AMOUNT == 68
#guard prmCol ep.ASSET == 73
#guard prmCol ep.RESOLVED == 74
#guard SYS_DIG_BEFORE == 97
#guard ESCROW_LEAF == 101
#guard SYS_DIG_AFTER == 96

/-- **NON-VACUITY (witness TRUE).** `goodEscrowRow` satisfies the recompute under the concrete sponge:
both sites carry their genuine digests. So the genuine-recompute predicate is INHABITED, not vacuous. -/
theorem goodEscrowRow_recomputes : escrowRootHolds cN goodEscrowRow := by
  have hID : prmCol ep.ID = 70 := by decide
  have hCRE : prmCol ep.CREATOR = 71 := by decide
  have hREC : prmCol ep.RECIPIENT = 72 := by decide
  have hAMT : prmCol AMOUNT = 68 := by decide
  have hASS : prmCol ep.ASSET = 73 := by decide
  have hRES : prmCol ep.RESOLVED = 74 := by decide
  have hBEF : SYS_DIG_BEFORE = 97 := by decide
  have hLEAF : ESCROW_LEAF = 101 := by decide
  have hAFT : SYS_DIG_AFTER = 96 := by decide
  unfold escrowRootHolds escrowRecomputeSites siteHoldsAll
  simp only [siteHoldsAll.go, siteEscrowLeaf, siteEscrowRootAdvance, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil, hID, hCRE, hREC, hAMT, hASS, hRES, hBEF,
    hLEAF, hAFT]
  refine ⟨?_, ?_, trivial⟩
  · show goodEscrowRow.loc 101 = cN [goodEscrowRow.loc 70, goodEscrowRow.loc 71, goodEscrowRow.loc 72,
        goodEscrowRow.loc 68, goodEscrowRow.loc 73, goodEscrowRow.loc 74]
    decide
  · show goodEscrowRow.loc 96 = cN [goodEscrowRow.loc 101, goodEscrowRow.loc 97]
    decide

/-- A FORGED escrow row: the parked AMOUNT in the leaf is recomputed as 999 (skewed from the bound
amount 30), but the OTHER carriers stay at the honest values. So this row's recompute does NOT hold
(`siteEscrowLeaf` is violated): the leaf carrier reads the honest leaf for amount 30, but the prover
wants the new root for amount 999. We exhibit that the GENUINE recomputed roots for amount-30 vs amount-999
DIFFER — the amount is bound. -/
theorem tampered_amount_moves_root :
    advanceOf cN (leafOf cN 7 11 13 30 2 0) 1000
      ≠ advanceOf cN (leafOf cN 7 11 13 999 2 0) 1000 := by
  unfold advanceOf leafOf cN
  norm_num

/-! ## §7 — Axiom-hygiene + layout pins. -/

-- The new-root carrier IS the IR's system-roots digest carrier (aux 96), absorbed into state_commit.
#guard SYS_DIG_AFTER == aux_off_sys.SYSTEM_ROOTS_DIGEST
#guard SYS_DIG_AFTER == 96
-- The leaf / before / after carriers are DISTINCT, and distinct from the state-inters.
#guard [auxCol aux_off.STATE_INTER1, auxCol aux_off.STATE_INTER2, auxCol aux_off.STATE_INTER3,
        SYS_DIG_AFTER, SYS_DIG_BEFORE, ESCROW_LEAF].dedup.length == 6
-- The escrow-record param columns are distinct + in-range.
#guard [AMOUNT, ep.ID, ep.CREATOR, ep.RECIPIENT, ep.ASSET, ep.RESOLVED].dedup.length == 6
#guard [AMOUNT, ep.ID, ep.CREATOR, ep.RECIPIENT, ep.ASSET, ep.RESOLVED].all (· < NUM_PARAMS)
-- AMOUNT is the SHARED debit column (the parked amount IS the debited amount).
#guard AMOUNT == param.AMOUNT
-- The recompute is two ordered sites (leaf, then advance).
#guard escrowRecomputeSites.length == 2

#assert_axioms escrowLeaf_forced
#assert_axioms escrowRootAdvance_forced
#assert_axioms escrowRoot_binds_record
#assert_axioms escrowRoot_amount_bound
#assert_axioms goodEscrowRow_recomputes
#assert_axioms tampered_amount_moves_root

end Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
