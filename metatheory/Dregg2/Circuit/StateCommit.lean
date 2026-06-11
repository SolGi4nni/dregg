/-
# Dregg2.Circuit.StateCommit — FULL-STATE circuit⟺spec keystone for `Transfer`.

`Dregg2.Circuit.Transfer` proved a SOUND bridge over the *two moved balances*: a satisfying
`transferCircuit` witness pins `admitGuard` + the debit/credit of the source/dest `balance` field.
But that is a PROJECTION — it says NOTHING about the other 15 fields of the moved cells, the
balance of any THIRD cell, or any of the 16 non-`cell` state components (`accounts caps bal escrows
nullifiers revoked commitments slotCaveats factories lifecycle deathCert delegate
delegations sealedBoxes`). A forged post-state that keeps the two moved balances honest but mints a
third cell, or silently rewrites `nullifiers`, satisfies `transferCircuit`. THAT is the "pale ghost".

This module upgrades the bridge to FULL-STATE soundness: a satisfying `stateCircuit` witness pins the
WHOLE post-state — it proves `TransferSpec k t k'` (Transfer.lean's INDEPENDENT 17-component
declarative reference), so tampering with ANY field or ANY third cell is REJECTED.

## How the frame is PROVED (not portaled — the honesty constraint)

The post-state's UNCHANGED-ness is derived from a GENUINE BINDING COMMITMENT (a Poseidon Merkle
node-hash `compress` + sponge `compressN` over the ORDERED cell leaves), never asserted, and never
from a fake `+`-fold (a sum is NOT injective: `a+b=c+d ⇏ a=c∧b=d`, so a sum-fold commitment cannot
satisfy the per-cell binding portals — that would make the soundness theorem VACUOUS). The state
commitment splits into three honestly-encoded digests over the witness:
  * `restHash`   — a hash of the 16 non-`cell` components.
  * `frameDigest`— `compressN (S.sort.map (fun c => CH c (cell c)))` over `S = accounts \ {src,dst}`:
                   the Poseidon sponge of the UNTOUCHED cells' leaves in CANONICAL (sorted) order,
                   shared pre/post (the load-bearing reuse: the SAME ordered sponge on the SAME carrier).
  * `movedDigest`— `compress (CH src (cell src)) (CH dst (cell dst))` — the 2-to-1 node hash of the
                   two cells the transfer moves.
Three EQ gates force pre/post agreement on the frame + rest, and force the moved post-leaves to equal
the SPEC's debit/credit of the pre-leaves (the whole-`Value` analog of `cTDebit`/`cTCredit`):
  * `cSRestFrame`  : `restDigPre = restDigPost`           (the 16 non-cell fields are frozen)
  * `cSFrameReuse` : `frameDigPre = frameDigPost`         (every third cell is frozen)
  * `cSMovedBind`  : `movedDigPost = movedDigExpected`    (moved leaves = spec debit/credit of pre)
The CONCLUSIONS (`k.cell c = k'.cell c` etc.) come from PROVED binding lemmas
(`FrameDigestBindsCells`/`MovedDigestBindsCells`) DERIVED from a SMALL standard Poseidon
collision-resistance set (`compressInjective`/`compressNInjective`/`cellLeafInjective`) — the ONLY
crypto assumptions, and each is the REALIZABLE injectivity of a genuine 2-to-1 / list / leaf hash
(NOT the unrealizable injectivity of a `+`-fold). A satisfying witness then REASSEMBLES the full
`TransferSpec` by `funext`: moved cells from `cSMovedBind`+`MovedDigestBindsCells`, third cells from
`cSFrameReuse`+`FrameDigestBindsCells`, dead cells from the PROVED `AccountsWF` invariant, and the 16
non-cell fields from `cSRestFrame`+`RestHashIffFrame`.

## The assumption ledger (enumerated — verify NOTHING else is assumed)

ASSUMED (carried Prop hypotheses — the STANDARD Poseidon collision-resistance set, all REALIZABLE
injectivity of a genuine hash, never `axiom`, never sum-injectivity):
  * `compressInjective cmb`      — the 2-to-1 root combiner is injective (a collision-resistant compress).
  * `compressInjective compress` — the 2-to-1 node hash is injective (Merkle node CR).
  * `compressNInjective compressN` — the sponge over a list of leaves is injective (list CR).
  * `cellLeafInjective CH`       — the per-cell leaf encoding is injective in the `Value` (leaf encoding).
  * `RestHashIffFrame RH`        — equal rest hashes ⟺ the 16 non-cell components agree (BIDIRECTIONAL).
  * `AccountsWF k` — NOT crypto: the structural invariant "cells outside `accounts` hold the default".
                     PROVED PRESERVED by `recKExec_preserves_AccountsWF` (a real theorem, not a portal).
The OLD `FrameDigestBindsCells`/`MovedDigestBindsCells`/`CombineInjective` portals are now PROVED
LEMMAS (derived from the CR set + `List.map_inj_left` on the sorted carrier), not carried.

PROVED (everything else — crucially THE FRAME): `recKExec_preserves_AccountsWF`, the binding lemmas,
`transfer_circuit_full_sound`, `transfer_circuit_full_complete`, the anti-ghost rejections
(`stateCircuit_rejects_field_tamper`, `stateCircuit_rejects_third_cell`) + concrete `#guard`s, and
the emission faithfulness. NO `postRoot = recStateCommit (applyTransfer …)` hypothesis appears —
that forbidden "ghost-in-disguise" would carry the whole answer; here the answer is RECONSTRUCTED.
-/
import Dregg2.Circuit.Transfer

namespace Dregg2.Circuit.StateCommit

open Dregg2.Circuit
open Dregg2.Circuit.Transfer
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Authority (Caps)

/-! ## §0 — decidability re-exports (so the concrete anti-ghost `#guard`s can `decide`).

`Constraint.holds` unfolds to a `ℤ`-equality (decidable); `satisfied` is a finite `∀ … ∈ list`. We
re-expose the SAME instances `Transfer.lean` uses, locally, so `decide (satisfied stateCircuit …)`
elaborates. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the `AccountsWF` invariant and its PROVED preservation.

`AccountsWF k` says every cell OUTSIDE the live account set holds the default `Value` (`.int 0`).
This is the structural fact that lets the soundness `funext` close the "dead cell" case (a cell
`c ∉ accounts` has `k.cell c = k'.cell c = default`, so it agrees with `recTransfer` which leaves it
untouched). It is NOT a crypto assumption — we PROVE `recKExec` preserves it. -/

/-- **`AccountsWF k`** — every cell outside the live account set holds the default `Value`. The
structural well-formedness the dead-cell frame case rests on. -/
def AccountsWF (k : RecordKernelState) : Prop := ∀ c, c ∉ k.accounts → k.cell c = default

/-- **THEOREM 1 — `recKExec_preserves_AccountsWF` (not portaled).** A committed `recKExec`
step preserves `AccountsWF`: the account set is unchanged (`recKExec_frame`), and `recTransfer`
touches only `src`/`dst` (both IN `accounts`), so any cell outside `accounts` keeps its default. -/
theorem recKExec_preserves_AccountsWF {k k' : RecordKernelState} {t : Turn}
    (hwf : AccountsWF k) (h : recKExec k t = some k') : AccountsWF k' := by
  have hspec : TransferSpec k t k' := (recKExec_iff_spec k t k').mp h
  obtain ⟨hg, hcell, hacc, _⟩ := hspec
  obtain ⟨_, _, _, hne, hsrc, hdst⟩ := hg
  intro c hc
  -- `c ∉ k'.accounts = k.accounts`, so `c ≠ src`, `c ≠ dst` (both ARE in accounts).
  rw [hacc] at hc
  have hcs : c ≠ t.src := fun he => hc (he ▸ hsrc)
  have hcd : c ≠ t.dst := fun he => hc (he ▸ hdst)
  -- `recTransfer` leaves `c` untouched; `AccountsWF k` makes it default.
  rw [hcell]
  simp only [recTransfer, if_neg hcs, if_neg hcd]
  exact hwf c hc

#assert_axioms recKExec_preserves_AccountsWF

/-! ## §1b — the new wires (extending Transfer's `vTDstLive = 10`).

The full-state circuit reuses Transfer's wires `0..10` verbatim (so every `t*_iff` gate lemma
transports) and adds the digest columns. -/

/-- `preRoot`  — `recStateCommit` of the pre-state. -/
def vPreRoot     : Var := 11
/-- `postRoot` — `recStateCommit` of the post-state. -/
def vPostRoot    : Var := 12
/-- `restDigPre`  — `RH` of the pre-state (16 non-cell components). -/
def vRestDigPre  : Var := 13
/-- `restDigPost` — `RH` of the post-state. -/
def vRestDigPost : Var := 14
/-- `frameDigPre`  — `frameDigest` of the pre-state over `accounts \ {src,dst}`. -/
def vFrameDigPre  : Var := 15
/-- `frameDigPost` — `frameDigest` of the post-state over `accounts \ {src,dst}`. -/
def vFrameDigPost : Var := 16
/-- `movedDigPre`      — `movedDigest` of the pre-state's two moved leaves. -/
def vMovedDigPre      : Var := 17
/-- `movedDigPost`     — `movedDigest` of the post-state's two moved leaves. -/
def vMovedDigPost     : Var := 18
/-- `movedDigExpected` — `movedDigest` of the SPEC's `recTransfer`-debited PRE leaves (a pure
function of the pre-state + turn; no executor). -/
def vMovedDigExpected : Var := 19

/-- The full-state trace width (Transfer's 11 wires + 9 digest columns). -/
def stateTraceWidth : Nat := 20

/-! ## §2 — the abstract commitment surface + the STANDARD Poseidon collision-resistance set.

The commitment primitives are SECTION PARAMETERS, never `axiom`s: a cell-leaf hash `CH`, a rest hash
`RH` of the 16 non-cell components, a root combiner `cmb`, a 2-to-1 Merkle node hash `compress`, and
a sponge `compressN` over a list of leaves (mirroring `Crypto/Primitives.CryptoPrimitives`'
`compress`/`compressN`, but at `ℤ` so the `Expr`/`#guard` decidability transports). The digests are
GENUINE BINDING commitments (a Poseidon node-hash of the moved pair; a Poseidon sponge of the
sorted-canonical untouched leaves) — NOT `+`-folds. The collision-resistance facts are carried Prop
HYPOTHESES on the keystones (the standard Poseidon CR set), each REALIZABLE by a real Poseidon; the
old per-digest binding portals are now PROVED from this set. -/

section Surface

-- `CH c v` — the leaf hash of cell `c`'s WHOLE `Value` `v` (NOT just its `balance`).
variable (CH : CellId → Value → ℤ)
-- `RH k` — the hash of the 16 non-`cell` components of `k`.
variable (RH : RecordKernelState → ℤ)
-- `cmb a b` — the root combiner (a 2-1 compress over the cell-digest and rest-hash children).
variable (cmb : ℤ → ℤ → ℤ)
-- `compress a b` — the Poseidon 2-to-1 Merkle node hash (`CryptoPrimitives.compress` at `ℤ`).
variable (compress : ℤ → ℤ → ℤ)
-- `compressN xs` — the Poseidon sponge over a list of leaves (`CryptoPrimitives.compressN` at `ℤ`).
variable (compressN : List ℤ → ℤ)

/-- **`frameDigest CH compressN k S`** — the Poseidon sponge of the cells in `S` (used with
`S = accounts \ {src,dst}`, the UNTOUCHED cells whose digest is REUSED pre/post). The leaves are
hashed in CANONICAL (sorted) order (`CellId = Nat` has `LinearOrder`, so `Finset.sort (· ≤ ·)` pins
the positions). The load-bearing reuse: the SAME ordered sponge on the SAME carrier. A GENUINE
binding commitment — NOT a `+`-fold. -/
def frameDigest (k : RecordKernelState) (S : Finset CellId) : ℤ :=
  compressN ((S.sort (· ≤ ·)).map (fun c => CH c (k.cell c)))

/-- **`movedDigest CH compress f src dst`** — the Poseidon 2-to-1 node hash of the two moved cells'
leaves, over a cell map `f`. Taking a raw `CellId → Value` (not a state) lets the moved gate compare
the post state's leaves to the SPEC's `recTransfer`-debited pre leaves without mentioning the
executor. A GENUINE 2-leaf binding commitment — NOT a `+` of the two leaves. -/
def movedDigest (f : CellId → Value) (src dst : CellId) : ℤ :=
  compress (CH src (f src)) (CH dst (f dst))

/-- **`cellDigest CH compress compressN k t`** — the live-cell digest as a Merkle INTERNAL NODE: the
2-to-1 hash combining the untouched-frame subtree digest with the moved-pair node hash. Binding the
full cell map (over the transfer's src/dst partition): `compress`-injectivity recovers
`(frameDigest, movedDigest)`, then the sub-digest binding lemmas recover every cell. The first child
of the root. -/
def cellDigest (k : RecordKernelState) (t : Turn) : ℤ :=
  compress (frameDigest CH compressN k (k.accounts \ {t.src, t.dst}))
           (movedDigest CH compress k.cell t.src t.dst)

/-- **`recStateCommit CH RH cmb compress compressN k t`** — the full-state root: combine the
live-cell digest (a binding commitment to the cell map) with the rest hash. Tampering with ANY cell
changes `cellDigest` (via the binding lemmas); tampering with ANY non-cell field changes `RH`;
injectivity of `cmb` separates them. -/
def recStateCommit (k : RecordKernelState) (t : Turn) : ℤ :=
  cmb (cellDigest CH compress compressN k t) (RH k)

/-! ### The collision-resistance carriers + the PROVED binding lemmas.

The carried set is the standard Poseidon CR (each REALIZABLE injectivity of a genuine hash). The
per-digest binding facts the soundness `funext` consumes are PROVED from it, not carried. -/

/-- **CR carrier `compressInjective h`** — the 2-to-1 hash `h` is injective: `h a b = h c d ⇒ a=c ∧
b=d`. The standard collision-resistance of a Poseidon 4-to-1/node compress (REALIZABLE — unlike the
injectivity of a `+`-fold, which is FALSE). Used at both `cmb` and `compress`. -/
def compressInjective (h : ℤ → ℤ → ℤ) : Prop := ∀ a b c d : ℤ, h a b = h c d → a = c ∧ b = d

/-- **CR carrier `compressNInjective h`** — the sponge `h` over a list of leaves is injective:
`h xs = h ys ⇒ xs = ys`. The standard collision-resistance of a Poseidon sponge (REALIZABLE). -/
def compressNInjective (h : List ℤ → ℤ) : Prop := ∀ xs ys : List ℤ, h xs = h ys → xs = ys

/-- **CR carrier `cellLeafInjective CH`** — the per-cell leaf encoding is injective in the `Value`:
`CH c v = CH c w ⇒ v = w` (a fixed cell's leaf binds its whole `Value`). REALIZABLE (a canonical
serialization + Poseidon leaf hash). -/
def cellLeafInjective : Prop := ∀ (c : CellId) (v w : Value), CH c v = CH c w → v = w

/-- **CR carrier `logHashInjective LH`** — the receipt-chain hash is injective:
`LH xs = LH ys ⇒ xs = ys`. The standard collision-resistance of a Poseidon log/Merkle accumulator
(REALIZABLE). The portal a log-GROWING effect (`setFieldA`, …) needs (unlike a frozen-log effect like
`Transfer`). RELOCATED here (beside the other CR carriers) so the generic `EffectCommit` framework can
import the log CR portal from `StateCommit` directly, not from a specific instance. (Takes `LH` as an
explicit binder — the `Surface` section variables `CH`/`RH`/… are irrelevant to it.) -/
def logHashInjective (LH : List Turn → ℤ) : Prop := ∀ xs ys : List Turn, LH xs = LH ys → xs = ys

/-- **PORTAL `RestHashIffFrame`** — the rest hash is injective on the non-`cell` components (incl. the spliced `heaps`)
(BIDIRECTIONAL: `→` binds them in soundness/anti-ghost, `←` rebuilds the hash in completeness). Pure
injectivity, stated as the iff. -/
def RestHashIffFrame : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps)

/-- **LEMMA `MovedDigestBindsCells` (from `compressInjective compress` + `cellLeafInjective`).**
Equal moved (2-leaf) node hashes force WHOLE-`Value` equality of BOTH `src` and `dst` leaves. The old
carried portal is now derived: `compress`-injectivity splits the node hash into its two leaf inputs,
then `cellLeafInjective` recovers each `Value`. -/
theorem MovedDigestBindsCells
    (hC : compressInjective compress) (hL : cellLeafInjective CH)
    (f g : CellId → Value) (src dst : CellId)
    (h : movedDigest CH compress f src dst = movedDigest CH compress g src dst) :
    f src = g src ∧ f dst = g dst := by
  unfold movedDigest at h
  obtain ⟨hs, hd⟩ := hC _ _ _ _ h
  exact ⟨hL src _ _ hs, hL dst _ _ hd⟩

/-- **LEMMA `FrameDigestBindsCells` (from `compressNInjective compressN` + `cellLeafInjective`).**
Equal frame digests over a carrier `S` force per-cell WHOLE-`Value` equality on `S`. The old carried
portal is now derived: `compressN`-injectivity makes the two sorted-leaf lists equal, `List.map_inj_left`
on the SAME sorted carrier `S.sort` makes the per-position leaf hashes equal, then `cellLeafInjective`
recovers each `Value`. (The sorted carrier is the key: a `+`-fold could never do this — sums lose
positions; the ORDERED sponge keeps them.) -/
theorem FrameDigestBindsCells
    (hN : compressNInjective compressN) (hL : cellLeafInjective CH)
    (k k' : RecordKernelState) (S : Finset CellId)
    (h : frameDigest CH compressN k S = frameDigest CH compressN k' S) :
    ∀ c ∈ S, k.cell c = k'.cell c := by
  unfold frameDigest at h
  -- compressN-injective ⇒ the two sorted-leaf lists are equal.
  have hmap : (S.sort (· ≤ ·)).map (fun c => CH c (k.cell c))
      = (S.sort (· ≤ ·)).map (fun c => CH c (k'.cell c)) := hN _ _ h
  -- map_inj_left on the same carrier ⇒ per-position leaf hashes equal.
  have hpt : ∀ c ∈ S.sort (· ≤ ·), CH c (k.cell c) = CH c (k'.cell c) :=
    List.map_inj_left.mp hmap
  intro c hc
  exact hL c _ _ (hpt c ((Finset.mem_sort (· ≤ ·)).mpr hc))

/-- **LEMMA `CombineInjective` (it IS `compressInjective cmb`).** Equal root combinations
force equal cell-digest AND equal rest-hash children. Kept as a named lemma so the root-binding
corollary reads cleanly. -/
theorem CombineInjective (hCmb : compressInjective cmb) (a b c d : ℤ) (h : cmb a b = cmb c d) :
    a = c ∧ b = d := hCmb a b c d h

/-! ## §3 — the encoder + transport.

`encodeS` lays out the full-state witness. On wires `0..10` it DELEGATES to `encodeT` (the `else
encodeT k t k' v` tail), so every `t*_iff` gate lemma transports unchanged. The digest columns are
filled from the HONEST `recStateCommit`/`RH`/`frameDigest`/`movedDigest` values. -/

/-- The carrier of the frame digest: the live accounts MINUS the two moved cells. -/
def frameCarrier (k : RecordKernelState) (t : Turn) : Finset CellId :=
  k.accounts \ {t.src, t.dst}

/-- **`encodeS`** — the full-state witness. Wires `0..10` delegate to `encodeT`; the eight digest
columns carry the honest commitment values. The moved-expected column commits the SPEC's debit/credit
of the PRE leaves (a pure function of `k`, `t` — no `k'`/executor). -/
def encodeS (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) : Assignment := fun v =>
  if      v = vPreRoot         then recStateCommit CH RH cmb compress compressN k t
  else if v = vPostRoot        then recStateCommit CH RH cmb compress compressN k' t
  else if v = vRestDigPre      then RH k
  else if v = vRestDigPost     then RH k'
  else if v = vFrameDigPre     then frameDigest CH compressN k  (frameCarrier k t)
  else if v = vFrameDigPost    then frameDigest CH compressN k' (frameCarrier k t)
  else if v = vMovedDigPre      then movedDigest CH compress k.cell  t.src t.dst
  else if v = vMovedDigPost     then movedDigest CH compress k'.cell t.src t.dst
  else if v = vMovedDigExpected then movedDigest CH compress (recTransfer k.cell t.src t.dst t.amt) t.src t.dst
  else encodeT k t k' v

/-- **Transport:** on every Transfer wire (`v < 11`) `encodeS` agrees with `encodeT`, so all nine
`t*_iff` gate lemmas apply to `encodeS` verbatim. -/
theorem encodeS_agrees_encodeT (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (v : Var) (hv : v < 11) : encodeS CH RH cmb compress compressN k t k' v = encodeT k t k' v := by
  unfold encodeS Var at *
  simp only [vPreRoot, vPostRoot, vRestDigPre, vRestDigPost, vFrameDigPre, vFrameDigPost,
    vMovedDigPre, vMovedDigPost, vMovedDigExpected]
  -- every new wire index is ≥ 11, so under `v < 11` all the `if`s take their `else`.
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ <;> first | rfl | (exfalso; omega)

#assert_axioms encodeS_agrees_encodeT

/-! ## §4 — the full-state circuit: the frame-forcing EQ gates ++ `transferCircuit`.

Three real `Expr` EQ gates extend `transferCircuit`:
  * `cSRestFrame`  : `restDigPre = restDigPost`        — the 16 non-cell components are frozen.
  * `cSFrameReuse` : `frameDigPre = frameDigPost`      — every third (untouched) cell is frozen.
  * `cSMovedBind`  : `movedDigPost = movedDigExpected` — the moved post-leaves equal the SPEC's
                     debit/credit of the pre-leaves (the whole-`Value` analog of `cTDebit`/`cTCredit`).
The root decomposition (`StateCommitSat`) is an opaque-hash Prop that holds by `rfl` from `encodeS`. -/

/-- **Rest-frame gate:** `restDigPre = restDigPost` (`RH k = RH k'`). -/
def cSRestFrame : Constraint := { lhs := .var vRestDigPre, rhs := .var vRestDigPost }

/-- **Frame-reuse gate:** `frameDigPre = frameDigPost` (untouched-cell digest reused). -/
def cSFrameReuse : Constraint := { lhs := .var vFrameDigPre, rhs := .var vFrameDigPost }

/-- **Moved-bind gate:** `movedDigPost = movedDigExpected` (the moved leaves match the spec debit/
credit of the pre leaves — whole `Value`, not just `balOf`). -/
def cSMovedBind : Constraint := { lhs := .var vMovedDigPost, rhs := .var vMovedDigExpected }

/-- **The full-state circuit** — the three frame-forcing EQ gates ++ the nine `transferCircuit`
gates. THIS is the constraint data that pins the WHOLE post-state. -/
def stateCircuit : ConstraintSystem :=
  transferCircuit ++ [cSRestFrame, cSFrameReuse, cSMovedBind]

/-- Sanity: twelve gates (9 transfer + 3 frame). -/
example : stateCircuit.length = 12 := rfl

/-- **`StateCommitSat cmb compress a`** — the root-decomposition equalities the opaque combiners pin:
the pre/post root wires equal `cmb` of the (frame⊕moved cell-digest internal node) child and the
rest-hash child. Holds by `rfl` from `encodeS` (the cell-digest child IS the Merkle node
`compress frameDig movedDig`). Carried in `satisfiedS` so the root-binding corollary can use
`compressInjective cmb`. (`a` is the witness; we read the digest children off the SAME witness.) -/
def StateCommitSat (a : Assignment) : Prop :=
  a vPreRoot  = cmb (compress (a vFrameDigPre)  (a vMovedDigPre))  (a vRestDigPre)
  ∧ a vPostRoot = cmb (compress (a vFrameDigPost) (a vMovedDigPost)) (a vRestDigPost)

/-- **`satisfiedS cmb compress a`** — the full-state satisfaction predicate: the `stateCircuit` gates
hold AND the root decomposition holds. (The latter is the opaque-hash Prop the combiners enforce.) -/
def satisfiedS (a : Assignment) : Prop :=
  satisfied stateCircuit a ∧ StateCommitSat cmb compress a

/-! ## §4b — digest wire lookups (the new columns under `encodeS`). -/

theorem encS_vPreRoot (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeS CH RH cmb compress compressN k t k' vPreRoot
      = recStateCommit CH RH cmb compress compressN k t := by
  simp [encodeS, vPreRoot]
theorem encS_vPostRoot (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeS CH RH cmb compress compressN k t k' vPostRoot
      = recStateCommit CH RH cmb compress compressN k' t := by
  simp [encodeS, vPostRoot, vPreRoot]
theorem encS_vRestDigPre (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeS CH RH cmb compress compressN k t k' vRestDigPre = RH k := by
  simp [encodeS, vRestDigPre, vPreRoot, vPostRoot]
theorem encS_vRestDigPost (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeS CH RH cmb compress compressN k t k' vRestDigPost = RH k' := by
  simp [encodeS, vRestDigPost, vRestDigPre, vPreRoot, vPostRoot]
theorem encS_vFrameDigPre (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeS CH RH cmb compress compressN k t k' vFrameDigPre
      = frameDigest CH compressN k (frameCarrier k t) := by
  simp [encodeS, vFrameDigPre, vRestDigPost, vRestDigPre, vPreRoot, vPostRoot]
theorem encS_vFrameDigPost (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeS CH RH cmb compress compressN k t k' vFrameDigPost
      = frameDigest CH compressN k' (frameCarrier k t) := by
  simp [encodeS, vFrameDigPost, vFrameDigPre, vRestDigPost, vRestDigPre, vPreRoot, vPostRoot]
theorem encS_vMovedDigPre (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeS CH RH cmb compress compressN k t k' vMovedDigPre
      = movedDigest CH compress k.cell t.src t.dst := by
  simp [encodeS, vMovedDigPre, vFrameDigPost, vFrameDigPre, vRestDigPost,
    vRestDigPre, vPreRoot, vPostRoot]
theorem encS_vMovedDigPost (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeS CH RH cmb compress compressN k t k' vMovedDigPost
      = movedDigest CH compress k'.cell t.src t.dst := by
  simp [encodeS, vMovedDigPost, vMovedDigPre, vFrameDigPost, vFrameDigPre, vRestDigPost,
    vRestDigPre, vPreRoot, vPostRoot]
theorem encS_vMovedDigExpected (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeS CH RH cmb compress compressN k t k' vMovedDigExpected
      = movedDigest CH compress (recTransfer k.cell t.src t.dst t.amt) t.src t.dst := by
  simp [encodeS, vMovedDigExpected, vMovedDigPost, vMovedDigPre, vFrameDigPost, vFrameDigPre,
    vRestDigPost, vRestDigPre, vPreRoot, vPostRoot]

/-! ## §4c — the frame-gate ↔ digest-equality lemmas (each EQ gate's protocol content). -/

/-- `cSRestFrame` holds under `encodeS` IFF the rest hashes agree. -/
theorem srestframe_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cSRestFrame.holds (encodeS CH RH cmb compress compressN k t k') ↔ RH k = RH k' := by
  unfold Constraint.holds cSRestFrame
  simp only [Expr.eval, encS_vRestDigPre, encS_vRestDigPost]

/-- `cSFrameReuse` holds under `encodeS` IFF the frame digests (over the untouched carrier) agree. -/
theorem sframereuse_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cSFrameReuse.holds (encodeS CH RH cmb compress compressN k t k')
      ↔ frameDigest CH compressN k (frameCarrier k t)
          = frameDigest CH compressN k' (frameCarrier k t) := by
  unfold Constraint.holds cSFrameReuse
  simp only [Expr.eval, encS_vFrameDigPre, encS_vFrameDigPost]

/-- `cSMovedBind` holds under `encodeS` IFF the post moved-leaves digest equals the spec's debit/
credit of the pre leaves. -/
theorem smovedbind_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cSMovedBind.holds (encodeS CH RH cmb compress compressN k t k')
      ↔ movedDigest CH compress k'.cell t.src t.dst
          = movedDigest CH compress (recTransfer k.cell t.src t.dst t.amt) t.src t.dst := by
  unfold Constraint.holds cSMovedBind
  simp only [Expr.eval, encS_vMovedDigPost, encS_vMovedDigExpected]

/-! ## §5 — FULL-STATE SOUNDNESS: a satisfying witness PROVES `TransferSpec` (whole post-state).

The keystone. From a satisfying `stateCircuit` witness, the nine transfer gates give `admitGuard` +
the moved-balance debit/credit; the three frame EQ gates + the PROVED binding lemmas give the WHOLE
post-state frame; the `AccountsWF` invariant closes the dead-cell case. The post `cell` map is
reconstructed by `funext` — NOT asserted. Result: `TransferSpec k t k'`. -/

/-- **THEOREM 2 — `transfer_circuit_full_sound` (frame RECONSTRUCTED not portaled).** A
satisfying full-state witness on the encoded pre/turn/post proves the complete declarative
`TransferSpec`: every one of the 17 components is pinned. Carries ONLY the standard Poseidon
collision-resistance set (`compressInjective compress`, `compressNInjective compressN`,
`cellLeafInjective CH`, `RestHashIffFrame RH`) + the `AccountsWF` invariant on both states. The frame
binding is PROVED (`MovedDigestBindsCells`/`FrameDigestBindsCells` are now lemmas off the CR set), so
the soundness theorem is NON-VACUOUS: every carried Prop is realizable by a real Poseidon (a `+`-fold
could satisfy NONE of them). -/
theorem transfer_circuit_full_sound
    (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (h : satisfiedS cmb compress (encodeS CH RH cmb compress compressN k t k')) :
    TransferSpec k t k' := by
  obtain ⟨hsat, _hcommit⟩ := h
  -- Transport: `encodeS` agrees with `encodeT` on each of the eleven Transfer wires (0..10), so
  -- the 9 transfer gates' truth values are preserved. We supply the agreements as simp rewrites.
  have e0  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vSrcPre    (by decide)
  have e1  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vDstPre    (by decide)
  have e2  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vSrcPost   (by decide)
  have e3  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vDstPost   (by decide)
  have e4  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vAmt       (by decide)
  have e5  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTAuth     (by decide)
  have e6  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTNonneg   (by decide)
  have e7  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTAvail    (by decide)
  have e8  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTDistinct (by decide)
  have e9  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTSrcLive  (by decide)
  have e10 := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTDstLive  (by decide)
  have htsat : satisfied transferCircuit (encodeT k t k') := by
    intro c hc
    have hc' : c ∈ stateCircuit := by unfold stateCircuit; exact List.mem_append_left _ hc
    have hcS := hsat c hc'
    unfold transferCircuit at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · unfold Constraint.holds at hcS ⊢
        simp only [cTAuth, cTNonneg, cTAvail, cTDistinct, cTSrcLive, cTDstLive, cTDebit, cTCredit,
          cTConserve, Expr.eval, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] at hcS ⊢
        exact hcS
  -- soundness on the projection: admitGuard + debit/credit.
  obtain ⟨hg, hdeb, hcre, _hcons⟩ := transfer_circuit_sound k t k' htsat
  obtain ⟨hauth, hnn, hav, hne, hsrc, hdst⟩ := hg
  -- the three frame gates.
  have hrestgate : cSRestFrame.holds (encodeS CH RH cmb compress compressN k t k') :=
    hsat cSRestFrame (by unfold stateCircuit; simp)
  have hframegate : cSFrameReuse.holds (encodeS CH RH cmb compress compressN k t k') :=
    hsat cSFrameReuse (by unfold stateCircuit; simp)
  have hmovedgate : cSMovedBind.holds (encodeS CH RH cmb compress compressN k t k') :=
    hsat cSMovedBind (by unfold stateCircuit; simp)
  -- rest hash equal ⇒ the non-cell fields (incl. heaps) equal (RestHashIffFrame.→).
  have hRHeq : RH k = RH k' := (srestframe_iff CH RH cmb compress compressN k t k').mp hrestgate
  have hframe16 := (hRest k k').mp hRHeq
  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs,
    hDE, hDEA, hHeaps⟩ := hframe16
  -- frame digests equal ⇒ untouched cells equal (FrameDigestBindsCells).
  have hfdeq : frameDigest CH compressN k (frameCarrier k t)
      = frameDigest CH compressN k' (frameCarrier k t) :=
    (sframereuse_iff CH RH cmb compress compressN k t k').mp hframegate
  have hcellframe : ∀ c ∈ frameCarrier k t, k.cell c = k'.cell c :=
    FrameDigestBindsCells CH compressN hCompressN hLeaf k k' (frameCarrier k t) hfdeq
  -- moved digests equal ⇒ both moved leaves equal the spec's debit/credit (MovedDigestBindsCells).
  have hmoveq : movedDigest CH compress k'.cell t.src t.dst
      = movedDigest CH compress (recTransfer k.cell t.src t.dst t.amt) t.src t.dst :=
    (smovedbind_iff CH RH cmb compress compressN k t k').mp hmovedgate
  obtain ⟨hmsrc, hmdst⟩ :=
    MovedDigestBindsCells CH compress hCompress hLeaf
      k'.cell (recTransfer k.cell t.src t.dst t.amt) t.src t.dst hmoveq
  -- reconstruct the post cell map by funext.
  have hcellmap : k'.cell = recTransfer k.cell t.src t.dst t.amt := by
    funext c
    by_cases hcsrc : c = t.src
    · subst hcsrc; exact hmsrc
    · by_cases hcdst : c = t.dst
      · subst hcdst; exact hmdst
      · by_cases hcacc : c ∈ k.accounts
        · -- c is an UNTOUCHED live cell: frame lemma + recTransfer leaves it.
          have hmem : c ∈ frameCarrier k t := by
            unfold frameCarrier
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hcacc, hcsrc, hcdst⟩
          rw [← hcellframe c hmem]
          simp only [recTransfer, if_neg hcsrc, if_neg hcdst]
        · -- c is a DEAD cell: AccountsWF on both states ⇒ both default; recTransfer leaves it.
          have hk'acc : c ∉ k'.accounts := by rw [hAcc]; exact hcacc
          rw [hwf' c hk'acc]
          simp only [recTransfer, if_neg hcsrc, if_neg hcdst]
          exact (hwf c hcacc).symm
  -- assemble TransferSpec (admitGuard ∧ cell map ∧ the frame clauses, `heaps` included).
  exact ⟨⟨hauth, hnn, hav, hne, hsrc, hdst⟩, hcellmap,
    hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA, hHeaps⟩

#assert_axioms transfer_circuit_full_sound

/-! ## §5b — ROOT-BINDING corollary (where `compressInjective cmb` earns its keep).

The frame proof above does NOT use the root combiner — the digest EQ gates suffice. But the root
combiner's injectivity gives the headline "the published root BINDS the whole state": two witnesses
(for the same turn) whose `recStateCommit` roots agree commit to the same cell digest and rest hash.
This is the §8-portal binding shape `Spike.EffectVmConstraints2.state_commitment_binds_state` mirrors
— and the reason `compressInjective cmb` is a required portal. -/

/-- **`recStateCommit_binds` (via `compressInjective cmb`).** Equal full-state roots (for the
same turn) force equal cell-digest AND equal rest-hash. With the binding lemmas + `RestHashIffFrame`
this propagates to the actual state — the published root is a binding commitment. -/
theorem recStateCommit_binds (hCmb : compressInjective cmb) (k k' : RecordKernelState) (t : Turn)
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    cellDigest CH compress compressN k t = cellDigest CH compress compressN k' t ∧ RH k = RH k' := by
  unfold recStateCommit at hroot
  exact CombineInjective cmb hCmb _ _ _ _ hroot

#assert_axioms recStateCommit_binds

/-! ## §6 — FULL-STATE COMPLETENESS: every committed step satisfies `stateCircuit`. -/

/-- **THEOREM 3 — `transfer_circuit_full_complete`.** A real committed `recKExec` step (=
`TransferSpec`) yields a satisfying full-state witness: ALL protocol-acceptable Transfer behaviours
are full-state-circuit-acceptable. The frame gates hold because `k'`'s frame is literally `k`'s
(`List.map_congr_left` on the untouched cells ⇒ equal ordered leaf lists ⇒ equal sponge, +
`RestHashIffFrame.←`); the root decomposes definitionally (`cellDigest` IS the Merkle node). -/
theorem transfer_circuit_full_complete
    (hRest : RestHashIffFrame RH)
    (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hspec : TransferSpec k t k') :
    satisfiedS cmb compress (encodeS CH RH cmb compress compressN k t k') := by
  have hexec : recKExec k t = some k' := (recKExec_iff_spec k t k').mpr hspec
  obtain ⟨hg, hcell, hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel,
    hDgs, hDE, hDEA, hHeaps⟩ := hspec
  obtain ⟨_, _, _, hne, hsrc, hdst⟩ := hg
  -- the 9 transfer gates hold under encodeT (Transfer's completeness), transport to encodeS.
  have htsat : satisfied transferCircuit (encodeT k t k') := transfer_circuit_complete hexec
  have e0  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vSrcPre    (by decide)
  have e1  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vDstPre    (by decide)
  have e2  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vSrcPost   (by decide)
  have e3  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vDstPost   (by decide)
  have e4  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vAmt       (by decide)
  have e5  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTAuth     (by decide)
  have e6  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTNonneg   (by decide)
  have e7  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTAvail    (by decide)
  have e8  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTDistinct (by decide)
  have e9  := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTSrcLive  (by decide)
  have e10 := encodeS_agrees_encodeT CH RH cmb compress compressN k t k' vTDstLive  (by decide)
  -- frame-gate facts.
  have hRHeq : RH k = RH k' := (hRest k k').mpr
    ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA, hHeaps⟩
  have hcellc : ∀ c ∈ frameCarrier k t, CH c (k.cell c) = CH c (k'.cell c) := by
    intro c hc
    unfold frameCarrier at hc
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨_, hcs, hcd⟩ := hc
    rw [hcell]; simp only [recTransfer, if_neg hcs, if_neg hcd]
  have hfdeq : frameDigest CH compressN k (frameCarrier k t)
      = frameDigest CH compressN k' (frameCarrier k t) := by
    unfold frameDigest
    refine congrArg compressN (List.map_congr_left ?_)
    intro c hc
    exact hcellc c ((Finset.mem_sort (· ≤ ·)).mp hc)
  have hmoveq : movedDigest CH compress k'.cell t.src t.dst
      = movedDigest CH compress (recTransfer k.cell t.src t.dst t.amt) t.src t.dst := by rw [hcell]
  refine ⟨?_, ?_⟩
  · -- satisfied stateCircuit: 9 transfer gates ++ 3 frame gates.
    intro c hc
    unfold stateCircuit at hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · -- transfer gate: transport from htsat.
      have hcT := htsat c hc
      unfold transferCircuit at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · unfold Constraint.holds at hcT ⊢
          simp only [cTAuth, cTNonneg, cTAvail, cTDistinct, cTSrcLive, cTDstLive, cTDebit, cTCredit,
            cTConserve, Expr.eval, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] at hcT ⊢
          exact hcT
    · -- frame gate.
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact (srestframe_iff CH RH cmb compress compressN k t k').mpr hRHeq
      · exact (sframereuse_iff CH RH cmb compress compressN k t k').mpr hfdeq
      · exact (smovedbind_iff CH RH cmb compress compressN k t k').mpr hmoveq
  · -- StateCommitSat: roots decompose definitionally (cellDigest = compress frame moved).
    refine ⟨?_, ?_⟩
    · -- pre root: cellDigest k t uses carrier `k.accounts \ {src,dst}` = `frameCarrier k t`.
      simp only [encS_vPreRoot, encS_vFrameDigPre, encS_vMovedDigPre, encS_vRestDigPre,
        recStateCommit, cellDigest, frameCarrier]
    · -- post root: cellDigest k' t uses `k'.accounts \ {src,dst}`; encodeS prints the children over
      -- `frameCarrier k t = k.accounts \ {src,dst}`. The carriers agree by `hAcc` (accounts frozen).
      simp only [encS_vPostRoot, encS_vFrameDigPost, encS_vMovedDigPost, encS_vRestDigPost,
        recStateCommit, cellDigest, frameCarrier, hAcc]

#assert_axioms transfer_circuit_full_complete

/-! ## §7 — THE ANTI-GHOST TEETH: `stateCircuit` REJECTS what the projection missed.

The whole point. A field-tamper (any non-cell component changed) and a third-cell-tamper (any
untouched cell changed) each make `satisfiedS` UNSATISFIABLE — exactly the forgeries the old
two-balance `transferCircuit` accepted. These bite because the frame EQ gates + the PROVED binding
lemmas force the WHOLE post-state, not a projection. -/

/-- **`stateCircuit_rejects_field_tamper` — ANTI-GHOST (non-cell component).** ANY witness whose
post-state changes a non-`cell` component (here: `nullifiers`) makes `satisfiedS` UNSATISFIABLE: the
rest-frame gate forces `RH k = RH k'`, and `RestHashIffFrame.→` then forces the nullifier sets equal
— contradiction. A silent nullifier rewrite (a double-spend laundering) is FORBIDDEN BY CONSTRUCTION. -/
theorem stateCircuit_rejects_field_tamper
    (hRest : RestHashIffFrame RH)
    (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hfield : k'.nullifiers ≠ k.nullifiers) :
    ¬ satisfiedS cmb compress (encodeS CH RH cmb compress compressN k t k') := by
  rintro ⟨hsat, _⟩
  have hrestgate : cSRestFrame.holds (encodeS CH RH cmb compress compressN k t k') :=
    hsat cSRestFrame (by unfold stateCircuit; simp)
  have hRHeq : RH k = RH k' := (srestframe_iff CH RH cmb compress compressN k t k').mp hrestgate
  have hframe16 := (hRest k k').mp hRHeq
  obtain ⟨_, _, _, hNul, _⟩ := hframe16
  exact hfield hNul

#assert_axioms stateCircuit_rejects_field_tamper

/-- **`stateCircuit_rejects_third_cell` — ANTI-GHOST (untouched cell).** ANY witness whose post-state
changes a THIRD live cell `c₀` (a live account, neither `src` nor `dst`) makes `satisfiedS`
UNSATISFIABLE: the frame-reuse gate forces the untouched-cell digest equal, and the PROVED
`FrameDigestBindsCells` then forces `k.cell c₀ = k'.cell c₀` — contradiction. Minting/draining a
bystander cell is FORBIDDEN BY CONSTRUCTION. (The old `transferCircuit` accepted this — see the
concrete `#guard` below.) -/
theorem stateCircuit_rejects_third_cell
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    {c₀ : CellId} (hc₀ : c₀ ∈ k.accounts) (hcs : c₀ ≠ t.src) (hcd : c₀ ≠ t.dst)
    (htamper : k'.cell c₀ ≠ k.cell c₀) :
    ¬ satisfiedS cmb compress (encodeS CH RH cmb compress compressN k t k') := by
  rintro ⟨hsat, _⟩
  have hframegate : cSFrameReuse.holds (encodeS CH RH cmb compress compressN k t k') :=
    hsat cSFrameReuse (by unfold stateCircuit; simp)
  have hfdeq : frameDigest CH compressN k (frameCarrier k t)
      = frameDigest CH compressN k' (frameCarrier k t) :=
    (sframereuse_iff CH RH cmb compress compressN k t k').mp hframegate
  have hmem : c₀ ∈ frameCarrier k t := by
    unfold frameCarrier
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hc₀, hcs, hcd⟩
  have := FrameDigestBindsCells CH compressN hCompressN hLeaf k k' (frameCarrier k t) hfdeq c₀ hmem
  exact htamper this.symm

#assert_axioms stateCircuit_rejects_third_cell

end Surface

/-! ## §8 — CONCRETE anti-ghost `#guard`: `stateCircuit` catches what `transferCircuit` missed.

We instantiate concrete COMPUTABLE commitments over a THREE-cell state and EXHIBIT a forgery that the
old two-balance `transferCircuit` ACCEPTS but the new full-state `stateCircuit` REJECTS: an honest
0→1 transfer that ALSO mints value into the bystander cell 2. `transferCircuit` never looks at cell 2
(so it passes); `stateCircuit`'s frame-reuse gate hashes cell 2's leaf into the untouched-cell sponge
(so it fails). This is the concrete death of the "pale ghost".

The concrete primitives must be COMPUTABLE and INJECTIVE (so the rejection #guard fires on
a binding commitment, not a lossy `+`-fold): `chConcrete = balOf` (the leaf), and INJECTIVE toy
node/sponge hashes (`compressConcrete` = a range-bounded `a*BIG + b` pairing; `compressNConcrete` = a
positional Horner fold) over the tiny `#guard` domain. -/

/-- Concrete cell-leaf hash: the cell's `balance` field (so a minted bystander balance is visible). -/
def chConcrete : CellId → Value → ℤ := fun _ v => balOf v
/-- Concrete rest hash: a field-count of the non-`cell` components (here: account cardinality +
nullifier length) — unchanged by a pure cell forgery, so the rest-frame gate is not the one that
bites; the FRAME-REUSE gate is. -/
def rhConcrete : RecordKernelState → ℤ := fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
/-- Concrete root combiner: an INJECTIVE pairing `a * BIG + b` (BIG larger than any toy child), so
the root binds its two children on the `#guard` domain (NOT the lossy `a + b`). -/
def cmbConcrete : ℤ → ℤ → ℤ := fun a b => a * 1000000 + b
/-- Concrete 2-to-1 node hash: an INJECTIVE pairing `a * BIG + b` on the toy domain (NOT `a + b`). -/
def compressConcrete : ℤ → ℤ → ℤ := fun a b => a * 1000000 + b
/-- Concrete sponge: an INJECTIVE positional Horner fold (each leaf shifted by a base larger than any
toy leaf), so the ORDERED leaf list is recoverable on the `#guard` domain (NOT the lossy `List.sum`).
The length is folded in too so distinct-length lists never collide. -/
def compressNConcrete : List ℤ → ℤ :=
  fun xs => xs.foldl (fun acc x => acc * 1000000 + x) (xs.length : ℤ)

/-- A concrete THREE-cell pre-state: cells {0,1,2} with balances 100 / 5 / 50, empty caps (actor 0
owns cell 0 by ownership). The bystander cell 2 holds 50. -/
def kS0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun _ => [] }

/-- The good turn: actor 0 transfers 30 from cell 0 to cell 1 (cell 2 must stay at 50). -/
def goodTurnS : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

/-- The honest post-state (src 100→70, dst 5→35, cell 2 untouched at 50). -/
def goodPostS : RecordKernelState := (recKExec kS0 goodTurnS).getD kS0

/-- **THE FORGERY:** cells 0,1 are the honest debit/credit (70 / 35), but the bystander cell 2 is
MINTED from 50 to 999 — value forged into a third cell. The two MOVED balances conserve, so the old
projection circuit sees nothing wrong. -/
def forgedThirdCell : RecordKernelState :=
  { kS0 with cell := fun c => if c = 0 then .record [("balance", .int 70)]
                              else if c = 1 then .record [("balance", .int 35)]
                              else if c = 2 then .record [("balance", .int 999)]  -- MINTED bystander
                              else default }

-- The honest post-state satisfies the FULL-state circuit (every gate decides true):
#guard decide (satisfied stateCircuit
  (encodeS chConcrete rhConcrete cmbConcrete compressConcrete compressNConcrete kS0 goodTurnS goodPostS))
-- The OLD two-balance circuit ACCEPTS the forgery (it never inspects cell 2):
#guard decide (satisfied transferCircuit (encodeT kS0 goodTurnS forgedThirdCell))
-- ...but the NEW full-state circuit REJECTS the SAME forgery (the frame-reuse gate fails on cell 2):
#guard decide (satisfied stateCircuit
  (encodeS chConcrete rhConcrete cmbConcrete compressConcrete compressNConcrete kS0 goodTurnS
    forgedThirdCell)) == false
-- ...and specifically the frame-reuse gate ALONE is the one that fails:
#guard decide (cSFrameReuse.holds
  (encodeS chConcrete rhConcrete cmbConcrete compressConcrete compressNConcrete kS0 goodTurnS
    forgedThirdCell)) == false

/-! ## §9 — EMISSION: the full-state circuit composes with `CircuitEmit.emit`/`emit_faithful`.

The full-state circuit serializes to the PART-I wire form losslessly: satisfying the emitted
descriptor is EXACTLY satisfying `stateCircuit`. (The digest gates are pure `Expr` EQ constraints, so
they serialize identically to the transfer gates — the §2/§8 commitment primitives live OUTSIDE the
emitted AIR, in the witness generator that fills the digest columns.) -/

/-- The AIR identity string the full-state wire form carries. -/
def stateAirName : String := "dregg-transfer-fullstate-v1"

/-- **The emitted full-state circuit** — `stateCircuit` serialized via the SAME `CircuitEmit.emit`. -/
def emittedState : EmittedDescriptor := emit stateAirName stateTraceWidth stateCircuit

/-- **`emitStateFaithful`** — satisfying the EMITTED descriptor is EXACTLY satisfying `stateCircuit`.
Direct instance of `CircuitEmit.emit_faithful`. -/
theorem emitStateFaithful (a : Assignment) :
    satisfied stateCircuit a ↔ satisfiedEmitted emittedState a :=
  emit_faithful stateAirName stateTraceWidth stateCircuit a

/-- The round trip recovers the source circuit. -/
theorem decodeE_emittedState : decodeE emittedState = stateCircuit :=
  decodeE_emit stateAirName stateTraceWidth stateCircuit

-- Sanity: the emitted descriptor has the twelve gates and twenty wires.
#guard emittedState.constraints.length == 12
#guard emittedState.traceWidth == stateTraceWidth
#guard emittedState.traceWidth == 20

/-- **`stateDescriptorJson`** — the canonical wire string for the REAL emitted full-state circuit,
via `CircuitEmit.emitDescriptorJson`. THIS is the byte string the Rust
`lean_descriptor_air::parse_descriptor` decoder ingests to drive the Plonky3 prover on the genuine
Lean-derived `stateCircuit` (the 9 transfer gates + 3 frame-forcing EQ gates). Copy this exact string
into the Rust `lean_emitted_state_roundtrip` golden. -/
def stateDescriptorJson : String := emitDescriptorJson emittedState

-- `#guard` golden pin: full-state wire bytes the Rust decoder parses (Rust `STATE_DESCRIPTOR_JSON`).
#guard (stateDescriptorJson == r#"{"name":"dregg-transfer-fullstate-v1","trace_width":20,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}},{"lhs":{"t":"var","v":13},"rhs":{"t":"var","v":14}},{"lhs":{"t":"var","v":15},"rhs":{"t":"var","v":16}},{"lhs":{"t":"var","v":18},"rhs":{"t":"var","v":19}}]}"#)

/-- The four balance wires range-checked into `[0, 2³⁰)` — same field-soundness teeth as
`Transfer.transferRanges`. -/
def stateRanges : List RangeSpec :=
  [ ⟨vSrcPre,  balanceRangeBits⟩
  , ⟨vDstPre,  balanceRangeBits⟩
  , ⟨vSrcPost, balanceRangeBits⟩
  , ⟨vDstPost, balanceRangeBits⟩ ]

/-- **The RANGE-CHECKED emitted full-state descriptor** — `emittedState` bundled with balance-wire
range checks (closing the `ℤ → BabyBear` wraparound hole on the conserved measure). -/
def emittedStateRanged : RangedDescriptor := ⟨emittedState, stateRanges⟩

/-- **`stateDescriptorRangedJson`** — the canonical wire string for the RANGE-CHECKED full-state
circuit: `stateDescriptorJson` extended with `"ranges":[{"wire":i,"bits":30},…]` on the four balance
wires. Copy into the Rust `lean_emitted_state_field_sound` golden. -/
def stateDescriptorRangedJson : String := emitRangedDescriptorJson emittedStateRanged

-- `#guard` golden pin: range-checked full-state wire bytes (Rust `STATE_DESCRIPTOR_RANGED_JSON`).
#guard (stateDescriptorRangedJson == r#"{"name":"dregg-transfer-fullstate-v1","trace_width":20,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}},{"lhs":{"t":"var","v":13},"rhs":{"t":"var","v":14}},{"lhs":{"t":"var","v":15},"rhs":{"t":"var","v":16}},{"lhs":{"t":"var","v":18},"rhs":{"t":"var","v":19}}],"ranges":[{"wire":0,"bits":30},{"wire":1,"bits":30},{"wire":2,"bits":30},{"wire":3,"bits":30}]}"#)

#guard emittedStateRanged.ranges.length == 4
#guard emittedStateRanged.ranges.all (fun r => r.bits == 30)
#guard emittedStateRanged.base == emittedState

/-! ## §10 — Axiom-hygiene tripwires + the assumption ledger.

ASSUMED (carried Prop hypotheses, the STANDARD Poseidon collision-resistance set, ALL realizable
injectivity of a genuine hash, NEVER `axiom`, NEVER sum-injectivity): `compressInjective compress`,
`compressNInjective compressN`, `cellLeafInjective CH`, `RestHashIffFrame RH` (the leaf/node/sponge/
rest CR set; `compressInjective cmb` only for the root-binding corollary); `AccountsWF` (a STRUCTURAL
invariant, PROVED preserved by `recKExec_preserves_AccountsWF`). The old per-digest binding portals
`FrameDigestBindsCells`/`MovedDigestBindsCells`/`CombineInjective` are now PROVED LEMMAS off the CR
set. PROVED (everything else, crucially THE FRAME): the keystones below. NO `postRoot = recStateCommit
(applyTransfer …)` ghost hypothesis appears anywhere. -/

#assert_axioms recKExec_preserves_AccountsWF
#assert_axioms encodeS_agrees_encodeT
#assert_axioms logHashInjective
#assert_axioms MovedDigestBindsCells
#assert_axioms FrameDigestBindsCells
#assert_axioms CombineInjective
#assert_axioms srestframe_iff
#assert_axioms sframereuse_iff
#assert_axioms smovedbind_iff
#assert_axioms transfer_circuit_full_sound
#assert_axioms recStateCommit_binds
#assert_axioms transfer_circuit_full_complete
#assert_axioms stateCircuit_rejects_field_tamper
#assert_axioms stateCircuit_rejects_third_cell
#assert_axioms emitStateFaithful
#assert_axioms decodeE_emittedState

end Dregg2.Circuit.StateCommit
