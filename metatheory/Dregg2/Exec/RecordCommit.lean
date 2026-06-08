/-
# Dregg2.Exec.RecordCommit — STAGE 1 of the record-layer upgrade: absorb `fields_root`
into the canonical CELL commitment, with a re-proved injectivity over the extended state and the
LEGACY no-op (an empty-map cell commits byte-identically).

`_RECORD-LAYER-UPGRADE.md` §D.2.1 + Stage 1. Stage 0 (`Dregg2.Exec.FieldsMap`) added the committed
user-field MAP: keys `≥ 8` live in a `fields_root = ListCommit.listDigest (userTail v)` accumulator
ALONGSIDE the 8 fixed cells, but `fields_root` was NOT yet folded into the cell's canonical state
commitment. Stage 1 FOLDS it in — so a verifier binds the WHOLE record, not just the 8 fixed slots —
and bumps the Rust domain-separation context `v2 → v3` (`cell/src/commitment.rs`).

This module is the LEAN keystone certifying that the Rust Stage-1 change is SOUND:

  * `cellCommit` — the canonical cell commitment modelled as the SAME injective sponge the Rust side
    uses: a `compressN` (list digest) over the ORDERED authority-bearing limbs of the cell, with the
    user-field-map root (`FieldsMap.fieldsRoot`) absorbed at a FIXED position as ONE extra limb. The
    `restLimbs` carrier abstracts the identity/permissions/vk/caps/lifecycle prefix the Rust hasher
    absorbs before it (none of which Stage 1 touches), so the proofs are about the absorption itself.

  * `cellCommit_binds_fieldsRoot` (PROVED) — INJECTIVITY OVER THE EXTENDED STATE: two cells whose
    canonical commitments agree have the SAME rest-limbs AND the SAME `fields_root`. Tampering the
    user map (which flips `fields_root`, off `FieldsMap.fieldsRoot_binds_tail`) therefore FLIPS the
    commitment — the anti-ghost tooth for the map. Discharged off a single carried `compressN`
    collision-resistance hypothesis (a REALIZABLE Poseidon/BLAKE3 sponge injectivity — never an
    axiom, never a `+`-fold).

  * `legacy_commit_absorbs_empty_root` (PROVED) — THE BACKWARD-COMPAT NO-OP: a LEGACY cell (no
    user-tail keys, i.e. an empty overflow map) commits BYTE-IDENTICALLY to the empty-root reference.
    Its `fields_root` is the FIXED `emptyTailRoot` constant (`FieldsMap.fieldsRoot_empty_legacy`),
    cell-INDEPENDENT, so the absorbed limb is the same constant for every legacy cell: folding it in
    is a uniform no-op. This is the Lean shadow of the Rust
    `legacy_cells_share_fields_root_contribution` test and the byte-identical guarantee the task
    requires.

  * the VACUITY GUARD (`_RECORD-LAYER-UPGRADE.md` §D.4): a POSITIVE `#guard` (a populated map's
    commitment DIFFERS from the legacy commitment) AND a NEGATIVE/no-op `#guard` (a legacy cell's
    commitment EQUALS the empty-root reference). A `fields_root := 0` stub would collapse the positive
    guard — forbidden.

Pure, computable, `#guard`-able (no `native_decide`). Imports `Exec.FieldsMap` (Stage 0) and reuses
`Circuit.ListCommit.compressNInjective` as the single realizable CR carrier.
-/
import Dregg2.Exec.FieldsMap

namespace Dregg2.Exec.RecordCommit

open Dregg2.Exec
open Dregg2.Exec.FieldsMap
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)

/-! ## §1 — the canonical cell commitment, with `fields_root` absorbed as one limb.

We model the Rust `compute_canonical_state_commitment` (`cell/src/commitment.rs`) at the soundness-
relevant granularity: it is a sponge `compressN` over the ORDERED authority-bearing limbs of the
cell. Stage 1 appends ONE limb — the user-field-map root `FieldsMap.fieldsRoot` — at a fixed
position (mirroring the Rust `hasher.update(&state.fields_root)` right after `refcount_table_root`).

`restLimbs` is the (abstract) ordered prefix of every OTHER absorbed limb (identity, mode, nonce,
balance, the 8 fixed `fields`, visibility, commitments, swiss/refcount roots, permissions, vk, caps,
delegate, delegation, program, lifecycle) — Stage 1 changes NONE of it, so its exact shape is
irrelevant to the absorption proof; we carry it as the data it is. -/

section Surface

-- `compressN xs` — the canonical commitment sponge (`CryptoPrimitives.compressN` at `ℤ`; the Rust
-- BLAKE3 `new_derive_key(... v3) || updates || finalize`). The SINGLE crypto primitive here.
variable (compressN : List ℤ → ℤ)

-- The injective `(key, value)` leaf encoder for the user-field-map tail (reused from Stage 0's
-- `FieldsMap.fieldsRoot`, where it is `tailLeaf compress2`).
variable (compress2 : Int → Int → Int)

/-- **`cellCommit compressN compress2 rest v`** — the canonical cell commitment: the sponge over the
ordered `rest` limbs FOLLOWED BY the user-field-map root limb `FieldsMap.fieldsRoot compress2 …`.
`rest : List ℤ` is the abstract prefix of all the other absorbed limbs (none of which Stage 1
touches). The `fields_root` limb is the Stage-1 addition — the ONE extra `compressN` input that
binds the unbounded `key ≥ 8` overflow map into the commitment. -/
def cellCommit (rest : List ℤ) (v : Value) : ℤ :=
  compressN (rest ++ [fieldsRoot compress2 compressN v])

/-- **`legacyReferenceCommit compressN compress2 rest`** — the canonical commitment of a LEGACY cell,
with the EMPTY-map root folded in by hand: the sponge over `rest ++ [emptyTailRoot compressN]`. This
is the Rust `legacy_reference_commitment` (it hashes the same state with `empty_fields_root()` pinned
at the fixed position). A cell-INDEPENDENT constant in the `fields_root` slot — the no-op fold. -/
def legacyReferenceCommit (rest : List ℤ) : ℤ :=
  compressN (rest ++ [emptyTailRoot compressN])

/-! ## §2 — INJECTIVITY OVER THE EXTENDED STATE (the anti-ghost tooth for the map). -/

/-- **`cellCommit_binds_state` (PROVED).** Equal canonical commitments (over the SAME `rest` prefix)
force the SAME user-field-map root. Off the single realizable `compressN`-injectivity carrier: the
sponge binds its input list, and `rest` is shared, so the absorbed `fields_root` limbs are equal.
Combined with `FieldsMap.fieldsRoot_binds_tail` (the map digest is injective on the tail), this is
the anti-ghost tooth: two cells with the SAME commitment have the SAME committed map — so tampering
the map (which moves `fields_root`) provably MOVES the commitment. The Stage-1 absorption is genuinely
LOAD-BEARING (a `fields_root := 0` stub would make this vacuous — forbidden). -/
theorem cellCommit_binds_fieldsRoot
    (hN : compressNInjective compressN) (rest : List ℤ) (v w : Value)
    (h : cellCommit compressN compress2 rest v = cellCommit compressN compress2 rest w) :
    fieldsRoot compress2 compressN v = fieldsRoot compress2 compressN w := by
  unfold cellCommit at h
  -- compressN injective ⇒ the two absorbed limb-lists are equal.
  have hlist : rest ++ [fieldsRoot compress2 compressN v]
      = rest ++ [fieldsRoot compress2 compressN w] := hN _ _ h
  -- a shared `rest` prefix cancels, leaving the singleton fields_root limbs equal.
  have := List.append_cancel_left hlist
  simpa using this

/-- **`cellCommit_binds_tail` (PROVED corollary).** Equal commitments force the SAME committed user
tail (the actual `(key, value)` overflow entries), given the map digest's injectivity carriers. The
full chain: equal commitment ⇒ equal `fields_root` (`cellCommit_binds_fieldsRoot`) ⇒ equal user tail
(`FieldsMap.fieldsRoot_binds_tail`). This is "the canonical commitment binds the whole record" for
the map tail — the soundness statement Stage 1 buys. -/
theorem cellCommit_binds_tail
    (hN : compressNInjective compressN)
    (hLE : listLeafInjective (tailLeaf compress2))
    (rest : List ℤ) (v w : Value)
    (h : cellCommit compressN compress2 rest v = cellCommit compressN compress2 rest w) :
    userTail v = userTail w :=
  fieldsRoot_binds_tail compress2 compressN hN hLE v w
    (cellCommit_binds_fieldsRoot compressN compress2 hN rest v w h)

/-! ## §3 — THE LEGACY NO-OP (byte-identical backward-compat keystone). -/

/-- **`legacy_commit_absorbs_empty_root` (PROVED).** THE backward-compat keystone the task requires:
a LEGACY cell — a record with NO user-tail keys (every key reserved/non-numeric, i.e. the 8-fixed-
field cell whose overflow map is empty) — has a canonical commitment BYTE-IDENTICAL to the
empty-root reference. Its `fields_root` is the FIXED `emptyTailRoot` constant
(`FieldsMap.fieldsRoot_empty_legacy`), independent of the cell, so the absorbed limb is the same
constant for every legacy cell: folding it in changes nothing. This certifies the Rust
`legacy_cells_share_fields_root_contribution` test (and the Stage-1 byte-identical guarantee): the
`v2→v3` bump aside, a legacy cell's commitment is exactly the reference that pins the empty constant
at the fixed position. -/
theorem legacy_commit_absorbs_empty_root
    (rest : List ℤ) (fs : List (FieldName × Value))
    (h : fs.filter (fun p => isUserTailKey p.1) = []) :
    cellCommit compressN compress2 rest (.record fs) = legacyReferenceCommit compressN rest := by
  unfold cellCommit legacyReferenceCommit
  rw [fieldsRoot_empty_legacy compress2 compressN fs h]

/-- **`legacy_commits_agree` (PROVED corollary).** ANY two legacy cells (both with empty user tails)
share the SAME `fields_root` contribution: their commitments differ ONLY in the `rest` prefix. With
the SAME `rest`, two legacy cells commit IDENTICALLY — the absorption does not distinguish legacy
cells (it is a uniform no-op). Mirrors the Rust assertion that a fresh cell and a populated-then-
drained cell produce the same commitment. -/
theorem legacy_commits_agree
    (rest : List ℤ) (fs gs : List (FieldName × Value))
    (hf : fs.filter (fun p => isUserTailKey p.1) = [])
    (hg : gs.filter (fun p => isUserTailKey p.1) = []) :
    cellCommit compressN compress2 rest (.record fs)
      = cellCommit compressN compress2 rest (.record gs) := by
  rw [legacy_commit_absorbs_empty_root compressN compress2 rest fs hf,
      legacy_commit_absorbs_empty_root compressN compress2 rest gs hg]

end Surface

/-! ## §4 — VACUITY GUARD (`_RECORD-LAYER-UPGRADE.md` §D.4): pos + neg, no `native_decide`.

Concrete computable commitment instances over the §FieldsMap example cells. A POSITIVE guard: a
populated overflow map's commitment DIFFERS from the legacy commitment (the absorption is
load-bearing). A NO-OP guard: a legacy cell's commitment EQUALS the empty-root reference. A
`fields_root := 0` stub would collapse the positive guard. -/

-- A concrete commitment sponge + leaf combiner (the same toy CR pair `FieldsMap` uses).
private def cNC : List Int → Int := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : Int)
private def c2C : Int → Int → Int := fun a b => a * 1000003 + b
-- A concrete `rest` prefix (the abstract identity/perms/… limbs; any fixed list works).
private def restC : List Int := [7, 11, 13]

private def legacyCellR : Value :=
  .record [("0", .int 11), ("7", .int 99), ("balance", .int 500)]
private def overflowCellR : Value :=
  .record [("0", .int 11), ("7", .int 99), ("8", .int 1234), ("9", .dig 42)]
private def overflowTamperedR : Value :=
  .record [("0", .int 11), ("7", .int 99), ("8", .int 9999), ("9", .dig 42)]

-- NO-OP: a legacy cell's commitment EQUALS the empty-root reference (byte-identical fold).
#guard decide (cellCommit cNC c2C restC legacyCellR = legacyReferenceCommit cNC restC)
#guard decide (cellCommit cNC c2C restC (.record [("balance", .int 7)])
             = legacyReferenceCommit cNC restC)

-- POSITIVE (load-bearing): a POPULATED overflow map's commitment DIFFERS from the legacy commitment
-- (the absorbed fields_root is non-constant — a `:= 0` stub would make these EQUAL: forbidden).
#guard decide (cellCommit cNC c2C restC overflowCellR = legacyReferenceCommit cNC restC) == false
#guard decide (cellCommit cNC c2C restC overflowCellR = cellCommit cNC c2C restC legacyCellR) == false

-- ANTI-GHOST: tampering a committed map value MOVES the commitment (distinct maps ⇒ distinct roots ⇒
-- distinct commitments).
#guard decide (cellCommit cNC c2C restC overflowCellR = cellCommit cNC c2C restC overflowTamperedR) == false

-- COMPLETENESS dual: two cells with the SAME user tail commit IDENTICALLY (same rest, same tail).
#guard decide (cellCommit cNC c2C restC overflowCellR
             = cellCommit cNC c2C restC (.record [("8", .int 1234), ("9", .dig 42)]))

#assert_axioms cellCommit_binds_fieldsRoot
#assert_axioms cellCommit_binds_tail
#assert_axioms legacy_commit_absorbs_empty_root
#assert_axioms legacy_commits_agree

end Dregg2.Exec.RecordCommit
