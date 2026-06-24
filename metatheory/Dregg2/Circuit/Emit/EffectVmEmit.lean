/-
# Dregg2.Circuit.Emit.EffectVmEmit — the EffectVM-shaped circuit-emission IR.

`Exec.CircuitEmit` (PARTs I–IV) emits the 6-wire TOY kernel, the abstract-`Digest` Merkle
gadget, and column-indexed algebraic `ConstraintExpr` forms over a single `RowEnv`. None of
those is the shape the RUNNING EffectVM prover (`circuit/src/effect_vm_p3_full_air.rs`'s
`EffectVmP3Air`, a faithful mirror of bespoke `effect_vm/air.rs`'s `EffectVmAir`) needs:

  * a FIXED 188-column layout (54 selectors · 14 state_before · 8 params · 14 state_after ·
    98 aux) read by *named* offsets (`sel`/`state`/`param`/`aux`);
  * per-row gates GATED by the selector column (`s_transfer · (…) = 0`), reading
    `state_before`/`state_after`/`param`;
  * TRANSITION gates over the row window (`next.state_before[i] == this.state_after[i]`);
  * BOUNDARY gates pinning the FIRST / LAST row (row-0 `state_before.nonce == PI[ACTOR_NONCE]`,
    last-row `state_after.state_commit == PI[NEW_COMMIT]`, …);
  * PUBLIC-INPUT bindings (`column == PI[k]`);
  * HASH-SITE forms: a Poseidon2 permutation over named aux columns with a DETERMINISTIC
    SITE ORDER (`hash_sites()` in the Rust is the single source of truth shared by the
    symbolic evaluator and the witness generator — site `i` ↔ aux block `i`).

This module supplies that IR (`VmGate` / `VmConstraint` / `VmHashSite` / `EffectVmDescriptor`)
with a self-contained denotation over an EffectVM `VmRowEnv` (the `local`/`next`/`pi` triple
the Rust `eval` reads), reusing PART-III's algebraic-`Int` field model. The `Transfer` effect's
full concrete descriptor is emitted through it (`transferVmDescriptor`), and its denotation is
proved EQUIVALENT to the transfer intent (debit/credit + nonce-increment + frame-passthrough +
the boundary pins) — the same intent `Spec.CircuitSpecTriangle.transfer_circuit_pins_intent`
pins abstractly. See `EffectVmEmitTransfer.lean` for the transfer emission + faithfulness.
-/
import Dregg2.Circuit
import Dregg2.Exec.CircuitEmit

namespace Dregg2.Circuit.Emit.EffectVmEmit

open Dregg2.Circuit
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §0 — The EffectVM column layout (the Lean mirror of `effect_vm/columns.rs`).

These are the SAME absolute column indices the running prover reads. We keep them as plain
`Nat` so the emitted descriptor's `Var` indices are literally the prover's column indices —
the wire form is the prover's layout, not a re-numbering. -/

/-- Number of effect-type selector columns (`columns.rs::NUM_EFFECTS`). -/
def NUM_EFFECTS : Nat := 54
/-- State-block width (`state::SIZE`). -/
def STATE_SIZE : Nat := 14
/-- Number of parameter columns (`NUM_PARAMS`). -/
def NUM_PARAMS : Nat := 8

/-- Absolute base of the `state_before` block (`STATE_BEFORE_BASE = NUM_EFFECTS`). -/
def STATE_BEFORE_BASE : Nat := NUM_EFFECTS
/-- Absolute base of the parameter block (`PARAM_BASE = STATE_BEFORE_BASE + STATE_SIZE`). -/
def PARAM_BASE : Nat := STATE_BEFORE_BASE + STATE_SIZE
/-- Absolute base of the `state_after` block (`STATE_AFTER_BASE = PARAM_BASE + NUM_PARAMS`). -/
def STATE_AFTER_BASE : Nat := PARAM_BASE + NUM_PARAMS
/-- Absolute base of the auxiliary block (`AUX_BASE = STATE_AFTER_BASE + STATE_SIZE`). -/
def AUX_BASE : Nat := STATE_AFTER_BASE + STATE_SIZE
/-- Total BASE trace width (`EFFECT_VM_WIDTH = 188`). The P0-2 record-digest aux column
(`aux_off.STATE_RECORD_DIGEST = 96`, absolute `auxCol 96 = 186`) is the 97th aux slot; the
light-client `aux_off.ASSET_CLASS = 97` column (absolute `auxCol 97 = 187`, row-0-pinned to
`PI[v3.ASSET_CLASS]`) is the 98th aux slot, growing the base width to
`AUX_BASE + 98 = 90 + 98 = 188`, matching the Rust `columns.rs::EFFECT_VM_WIDTH = AUX_BASE + NUM_AUX`. -/
def EFFECT_VM_WIDTH : Nat := 188

/-! State-column offsets within a state block (`state::*`). -/
namespace state
def BALANCE_LO : Nat := 0
def BALANCE_HI : Nat := 1
def NONCE      : Nat := 2
def FIELD_BASE : Nat := 3
def CAP_ROOT   : Nat := 11
def STATE_COMMIT : Nat := 12
def RESERVED   : Nat := 13

/-- **`FIELDS_ROOT` (record-layer STAGE 2).** The committed user-field-MAP root
(`_RECORD-LAYER-UPGRADE.md` §B.5, `Exec.FieldsMap.fieldsRoot`) carried in the EffectVM state block.
It is width-neutral: it reuses the single state column GROUP-4 currently leaves UNABSORBED — the
`RESERVED` cell (col 13) — as the carrier (the transfer-keystone `reserved_not_bound_by_commitment`
finding identified `RESERVED` as the lone un-hashed state cell, so binding it costs no new column).
On a record / map-write row the runtime writes the row's `fields_root` felt here; on every legacy
row the carrier is `0` (the empty-map circuit root), so the legacy `state_commit` is byte-identical
to the pre-STAGE-2 `H4(inter1, inter2, inter3, 0)`. STAGE 2 absorbs THIS cell into `state_commit`
via GROUP-4 site 3's previously-spare 4th input (`_IR-EXTENSION-DESIGN.md:23,158-162`). -/
def FIELDS_ROOT : Nat := 13

/-! ### **`system_roots` sub-block (record-layer STAGE 3).** The dedicated, kernel-owned home for the
8 side-table roots (`_RECORD-LAYER-UPGRADE.md` §C, Option C1; `Exec.SystemRoots`). The IR-extension
(`_IR-EXTENSION-DESIGN.md:138-143`) originally STOLE the user `fields[1..7]` cells for these roots,
colliding with app data; STAGE 0–2 FREED the user namespace onto `FIELDS_ROOT`, and STAGE 3 gives the
side-table roots their OWN namespace so they never collide with user fields again.

These are the column constants the per-effect side-table descriptors (`EffectVmEmitCreateEscrow`,
`…QueueEnqueue`, `…NoteSpend`, `…Seal`, `…RefreshDelegation`, …) REFERENCE for their root-update
gate: each writes `saCol (systemRoot.X)`, NEVER a user `fields[j]`. The reconciliation note
(`_RECORD-LAYER-UPGRADE.md:246-250`) re-targets each emit file's root from `FIELD_BASE+i` onto
`systemRoot.X` — these are those targets. The 8 roots are committed by `Exec.SystemRoots.systemRootsDigest`
(one carrier column `SYSTEM_ROOTS_DIGEST`), absorbed into `state_commit` by the same GROUP-4 hash-site
mechanism `FIELDS_ROOT` uses (anti-ghost tooth: `Exec.SystemRoots.cellCommitS_binds_systemRoots`). -/
namespace systemRoot
/-- `escrows` list digest (createEscrow / refund / release / bridge-park). -/
def ESCROW       : Nat := 0
/-- `queues` table digest (allocate / enqueue / dequeue / resize / pipeline; FIFO order intrinsic). -/
def QUEUE        : Nat := 1
/-- refcount table digest (dropRef GC); was the running prover's `fields[3]` mirror. -/
def REFCOUNT     : Nat := 2
/-- `swiss` sturdyref table digest (export / enliven / handoff / drop); was `fields[4]`. -/
def STURDYREF    : Nat := 3
/-- `delegations` keyed-map digest (refresh / revoke delegation epoch). -/
def DELEG        : Nat := 4
/-- `nullifiers` accumulator digest (noteSpend append; non-membership via spend-proof PI). -/
def NULLIFIER    : Nat := 5
/-- `commitments` accumulator digest (noteCreate append). -/
def COMMIT       : Nat := 6
/-- `sealedBoxes` store digest (seal / unseal / createSealPair); its OWN home, not folded
into `cap_root`. -/
def SEALED_BOXES : Nat := 7
end systemRoot

/-- Size of the dedicated `system_roots` sub-block (`Exec.SystemRoots.N_SYSTEM_ROOTS = 8`). -/
def N_SYSTEM_ROOTS : Nat := 8
end state

/-! Auxiliary column carrying the committed `system_roots` digest (record-layer STAGE 3).

`Exec.SystemRoots.systemRootsDigest` over the 8 side-table roots is carried HERE (one aux column,
absorbed into `state_commit` by a GROUP-4 extension site, mirroring how `FIELDS_ROOT` is absorbed via
site3's spare slot). Apps never address it; only the kernel side-table transitions mutate the roots it
digests. The per-effect descriptors write the individual roots conceptually at `state.systemRoot.X`;
the prover digests them into this carrier and binds the carrier into the commitment. -/
namespace aux_off_sys
/-- The committed `system_roots` digest carrier (`Exec.SystemRoots.systemRootsDigest`). The first aux
column past the W9-RANGECHECK balance-bit block (`NEW_BAL_HI_BIT_BASE + 30 = 96`); growing aux by one
is the single minimal width touch (`_IR-EXTENSION-DESIGN.md:158-162` overflow contingency), kept
DISTINCT from every claimed aux slot so it never aliases a balance bit or sealing witness. -/
def SYSTEM_ROOTS_DIGEST : Nat := 96
end aux_off_sys

/-! ## §0½ — THE WIDENED `system_roots` COLUMN (magnesium STAGE 4: the deployed gap closed).

The finding the per-effect files PROVE (`*_root_not_in_descriptor_commit`,
`docs/rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md:52-56`): the side-table `system_roots` digest is
`Exec.SystemRoots.systemRootsDigest`-bound at the RECORD layer (`cellCommitS`), but `auxCol
aux_off_sys.SYSTEM_ROOTS_DIGEST = AUX_BASE + 96 = 186` is **PAST the GROUP-4-bound state** — the
deployed EffectVM row's `state_commit` does NOT absorb it. THIS section closes that, ADDITIVELY
(the binding constraint: `EFFECT_VM_WIDTH = 188` is load-bearing in ~50 unowned
`#guard …traceWidth == 188` sites — it MUST stay; the widening is a NEW width + a NEW dedicated
column block PAST the base width, opted into by a v2 descriptor shape).

The two dedicated carriers are placed at the FIRST TWO absolute columns past the base width
(`EFFECT_VM_WIDTH` = `188`, `EFFECT_VM_WIDTH + 1` = `189`), so they are DISTINCT from every column
the base layout claims (every aux slot is `< AUX_BASE + 98 = 188`, and the `ASSET_CLASS` column sits
at the last base slot `187`). Unlike the early cohort's `SYS_DIG_AFTER := aux_off_sys.SYSTEM_ROOTS_DIGEST`
(= the raw `96`, which lands inside the aux block at abs col `96` = `auxCol 6`, aliasing a balance
bit — benign for those effects but not a CLEAN home), these are a dedicated, non-aliasing
sub-block. `sysRootsDigestSiteWidth_clean` proves the disjointness by `decide`. -/

/-- **`EFFECT_VM_WIDTH_SYSROOTS`** — the WIDENED trace width that carries the dedicated `system_roots`
digest sub-block: the base `EFFECT_VM_WIDTH = 188` PLUS two carrier columns (after-state digest +
before-state digest). Strictly additive: every base-width descriptor is unaffected (it simply does not
populate cols `188`/`189`); a v2 descriptor declares THIS width and absorbs col `188` into its
`state_commit`. -/
def EFFECT_VM_WIDTH_SYSROOTS : Nat := EFFECT_VM_WIDTH + 2

/-- **`sysRootsDigestCol`** — the dedicated absolute column carrying the AFTER-state committed
`system_roots` digest (`Exec.SystemRoots.systemRootsDigest` over the 8 side-table roots). The first
column past the old width — NEVER aliases a 186-layout column. THIS is the carrier a v2 descriptor's
GROUP-4 extension site absorbs into `state_commit`, making every side-table root descriptor-bound. -/
def sysRootsDigestCol : Nat := EFFECT_VM_WIDTH

/-- **`sysRootsDigestColBefore`** — the dedicated absolute column carrying the BEFORE-state
`system_roots` digest (the pre-image of the per-effect root-update accumulator step). One past the
after-carrier; the per-effect root-update gate reads `sysRootsDigestColBefore` and writes
`sysRootsDigestCol`. -/
def sysRootsDigestColBefore : Nat := EFFECT_VM_WIDTH + 1

/-! Selector-column indices (`sel::*`). -/
namespace sel
def NOOP     : Nat := 0
def TRANSFER : Nat := 1
-- The DEPLOYED runtime selector columns (`circuit/src/effect_vm/columns.rs::sel`, the column
-- `effect_vm/trace.rs::effect_selector` sets per effect row). These are the columns the
-- selector-binding tooth (`selectorGate`, §6½) reads to bind a rotated descriptor to its OWN
-- effect — distinct from the per-effect Lean faithfulness abstractions (e.g. `selA.ATTENUATE = 2`
-- is the faithfulness-internal name; the LIVE attenuate row sets column 48). Each MUST equal its
-- Rust `columns::sel` twin or the gate would reject the HONEST row.
def GRANT_CAP            : Nat := 3   -- columns::sel::GRANT_CAP
def REVOKE_CAPABILITY    : Nat := 24  -- columns::sel::REVOKE_CAPABILITY
def REFRESH_DELEGATION   : Nat := 29  -- columns::sel::REFRESH_DELEGATION
def REVOKE_DELEGATION    : Nat := 30  -- columns::sel::REVOKE_DELEGATION
def INTRODUCE            : Nat := 35  -- columns::sel::INTRODUCE
def ATTENUATE_CAPABILITY : Nat := 48  -- columns::sel::ATTENUATE_CAPABILITY
def EXERCISE             : Nat := 34  -- columns::sel::EXERCISE_VIA_CAPABILITY
-- The DEDICATED SUPPLY-MINT selector (`columns::sel::MINT`, SUPPLY-MODEL.md Stage 2b). A
-- repurposed retired slot (the dissolved `ExportSturdyRef` column 14, which the IR-2 live path
-- never pinned). The supply-creation effect `Effect::Mint` fires THIS column — distinct from
-- `BRIDGE_MINT = 40` (the SHIELD-verb portable-proof credit), so the two mints prove + self-verify
-- under SEPARATE selectors and a `[Mint, …]` trace cannot ride the bridgeMint descriptor.
def MINT                 : Nat := 14  -- columns::sel::MINT (repurposed retired ExportSturdyRef slot)
end sel

/-! Transfer parameter offsets (`param::AMOUNT` / `param::DIRECTION`). -/
namespace param
def AMOUNT    : Nat := 0
def DIRECTION : Nat := 1
end param

/-! Aux offsets used by the state-commitment chain (`aux_off::STATE_INTER*`). -/
namespace aux_off
def STATE_INTER1 : Nat := 8
def STATE_INTER2 : Nat := 9
def STATE_INTER3 : Nat := 10
/-- **`STATE_RECORD_DIGEST` (audit P0-2).** The single Poseidon2 felt folding ALL authority-bearing
cell state the welded `balance`/`nonce`/`fields`/`cap_root` limbs do NOT carry (permissions / VK /
lifecycle / deathCert / delegate / delegation / program / mode / sealed-field mask / visibility /
side-table roots / `fields[8..]`). It is the FOURTH input of the GROUP-4 state-commit root hash
(`state_commit = H4(inter1, inter2, inter3, record_digest)`), replacing the old literal `.zero`, so
`OLD_COMMIT`/`NEW_COMMIT` bind the FULL cell state. Absolute column `auxCol 96 = 186`; matches the
Rust `columns.rs::aux_off::STATE_RECORD_DIGEST = 96` (`AUX_BASE + 96 = 186`). A residue-free cell
witnesses `0` here, so the absorption is byte-identical to the legacy `…, 0)` form for such cells. -/
def STATE_RECORD_DIGEST : Nat := 96
end aux_off

/-! Public-input slot indices (`pi::*`).

Phase C (`docs/FAITHFUL-STATE-COMMITMENT.md`): the OLD/NEW state commitment
widened from 4 felts to 8 felts each (~62-bit → ~124-bit collision floor,
matching FRI), shifting the whole PI prefix by +8. The slot indices below are
the Rust twin (`effect_vm/pi.rs`); the commit-binding lemmas (`saCol STATE_COMMIT
→ NEW_COMMIT`, etc.) are width-agnostic — they pin slot 0 of each commitment to
the in-trace continuity column, and the off-AIR PI match over all 8 felts is
what raises the floor. -/
namespace pi
def OLD_COMMIT : Nat := 0
/-- New commitment base: OLD_COMMIT + 8 (Phase C 8-felt commitment). -/
def NEW_COMMIT : Nat := 8
def INIT_BAL_LO : Nat := 20
def INIT_BAL_HI : Nat := 21
def FINAL_BAL_LO : Nat := 22
def FINAL_BAL_HI : Nat := 23
/-- `pi.rs` `ACTOR_NONCE` (the full v3 layout offset): post-Phase-C the OLD/NEW
state commitments widened 4→8 each (+8 prefix), shifting `INIT_BAL_LO` 12→20 AND the
later blocks, so `APPROVED_HANDOFFS_BASE = 29`, `TURN_HASH_BASE = 33`,
`EFFECTS_HASH_GLOBAL_BASE = 37`, and `ACTOR_NONCE = 41`. The descriptor PI window
must therefore be wide enough to address index 41 (see `PI_COUNT = 42`). -/
def ACTOR_NONCE : Nat := 41
end pi

/-- Absolute column index of `state_before[off]`. -/
def sbCol (off : Nat) : Nat := STATE_BEFORE_BASE + off
/-- Absolute column index of `state_after[off]`. -/
def saCol (off : Nat) : Nat := STATE_AFTER_BASE + off
/-- Absolute column index of `param[i]`. -/
def prmCol (i : Nat) : Nat := PARAM_BASE + i
/-- Absolute column index of `aux[i]`. -/
def auxCol (i : Nat) : Nat := AUX_BASE + i

/-! ## §1 — The row environment (`local`/`next`/`pi`, the Rust `eval` triple).

The running `EffectVmP3Air::eval` reads three slices: `local` (current row), `next` (next row),
and `pi` (public values). We model each as a column→`ℤ` map (PART-III's `Int` field model), so
the EffectVM IR reuses the proven `EmittedExpr.eval` and the algebraic forms. -/

/-- A row environment: the current row `loc`, the next row `nxt`, and the public inputs `pub`. -/
structure VmRowEnv where
  loc : Assignment
  nxt : Assignment
  pub : Assignment

/-! ## §2 — `VmGate`: a per-row arithmetic gate over the EffectVM layout.

A `VmGate` is an `EmittedExpr` over the CURRENT row that the AIR asserts is ZERO — exactly the
shape of the `tb.assert_zero(...)` calls in `EffectVmP3Air::eval`. Because the gate is an
`EmittedExpr`, it composes with PART-I's proven `EmittedExpr.eval`, and "holds" means
`eval = 0` (the Rust `assert_zero` semantics). Reading `state_before`/`state_after`/`param` is
just reading the named absolute columns. -/

/-- A per-row gate: the polynomial `body` must vanish on the row (`body.eval loc = 0`). -/
structure VmGate where
  body : EmittedExpr
  deriving Repr

/-- A per-row gate holds iff its body evaluates to zero on the current row. -/
def VmGate.holds (g : VmGate) (env : VmRowEnv) : Prop :=
  g.body.eval env.loc = 0

/-! ## §3 — `VmConstraint`: the four EffectVM constraint FORMS.

Mirrors the four kinds of `assert` the prover emits:

* `gate`        — a per-row `tb.assert_zero(body)` (selector-gated semantics live in `body`).
* `transition`  — `tb.assert_zero(next[hi] - this.after[lo])`: continuity over the row window.
* `boundaryFirst nzero`/`boundaryLast nzero` — a `when_first_row`/`when_last_row` assert that
  the polynomial `nzero` (over `local`+`pi`) vanishes on that boundary row.
* `piBinding col k` — `local[col] == pi[k]` (a `when_first_row` PI pin or in-row binding). -/

/-- A boundary-row tag. -/
inductive VmRow where
  | first | last
  deriving Repr, DecidableEq

/-- The four EffectVM constraint forms. Each constructor records the SAME columns / PI indices
the Rust AIR carries, so a decoder reconstructs the exact gate. -/
inductive VmConstraint where
  /-- Per-row gate `body = 0` (term-for-term a `tb.assert_zero`). -/
  | gate (body : EmittedExpr)
  /-- Transition gate `next[STATE_BEFORE_BASE+hi] = this[STATE_AFTER_BASE+lo]` (continuity). -/
  | transition (hi lo : Nat)
  /-- Boundary gate on `row`: the polynomial `body` (over `local`/`pi`) vanishes on that row. -/
  | boundary (row : VmRow) (body : EmittedExpr)
  /-- PI binding on `row`: `local[col] = pi[piIndex]`. -/
  | piBinding (row : VmRow) (col piIndex : Nat)
  deriving Repr

/-! ## §4 — `VmHashSite`: a Poseidon2 hash site with a DETERMINISTIC ordering.

The running prover lays one Poseidon2 aux block per hash site, in the FIXED order `hash_sites()`
returns. Site `i`'s digest is bound to a named result column (or consumed by a later site). We
model a site by its result column (`digestCol`), an absorbed-input list (`inputs`, a list of
`HashInput`), and the `arity`. The denotation is parametric in an ABSTRACT permutation
`hash : List ℤ → ℤ` (the Layer-A carrier — NEVER an in-Lean algebraic hash), exactly as PART II
keeps `compress` abstract: a site HOLDS iff `loc digestCol = hash (resolved inputs)`. The ORDER
of the site list is load-bearing (a `Digest k` input reads an earlier site's resolved digest),
so the denotation walks the list left-to-right accumulating resolved digests — the Lean mirror
of the Rust `digests.push(d)` loop. -/

/-- A hash-site input: a trace column, an earlier site's digest (by 0-based index), or zero. -/
inductive HashInput where
  | col   (c : Nat)
  | digest (k : Nat)
  | zero
  deriving Repr, DecidableEq

/-- A Poseidon2 hash site: its result column, the absorbed inputs (in order), and the arity tag. -/
structure VmHashSite where
  digestCol : Nat
  inputs    : List HashInput
  arity     : Nat
  deriving Repr

/-- Resolve a single hash input under `(env, earlier-digests)`. A `digest k` reads the `k`-th
already-resolved digest (`default 0` if out of range — the emitter only ever references earlier
sites, so this never fires on a well-formed descriptor). -/
def HashInput.resolve (env : VmRowEnv) (digs : List ℤ) : HashInput → ℤ
  | .col c   => env.loc c
  | .digest k => digs.getD k 0
  | .zero    => 0

/-- Resolve a site's input list to the `ℤ` values absorbed (in order). -/
def VmHashSite.resolvedInputs (env : VmRowEnv) (digs : List ℤ) (s : VmHashSite) : List ℤ :=
  s.inputs.map (HashInput.resolve env digs)

/-! ### Walking the ordered site list (the Rust `digests` accumulator).

`siteDigestsAcc` produces the list of resolved digests for the sites, in order, each site
reading the digests of the sites BEFORE it. `siteHoldsAll` asserts every site's result column
equals its hash — the EffectVM hash layer's denotation, abstract in `hash`. -/

/-- **`siteDigestsAcc hash env acc sites`** — the head-first accumulator: `acc` holds the digests
of the sites ALREADY processed (sites that come BEFORE `sites` in the global order), so a
`digest k` input in `sites` reads `acc.getD k`. Returns the FULL digest list (acc ++ new). This
is the faithful Lean mirror of the Rust `digests.push(poseidon2(...))` loop, where site `i`
sees `digests[0..i]`. -/
def siteDigestsAcc (hash : List ℤ → ℤ) (env : VmRowEnv) :
    List ℤ → List VmHashSite → List ℤ
  | acc, []      => acc
  | acc, s :: ss =>
    let d := hash (s.resolvedInputs env acc)
    siteDigestsAcc hash env (acc ++ [d]) ss

/-- The resolved digests for the whole ordered site list (starting from an empty accumulator). -/
def VmHashSite.allDigests (hash : List ℤ → ℤ) (env : VmRowEnv) (sites : List VmHashSite) : List ℤ :=
  siteDigestsAcc hash env [] sites

/-- **`siteHoldsAll hash env sites`** — every site's result column carries its genuine digest:
for the `i`-th site `s`, `loc s.digestCol = hash (s.resolvedInputs env digests[0..i])`. This is
the EffectVM GROUP-4 (and per-effect) hash-binding denotation, abstract in `hash`. -/
def siteHoldsAll (hash : List ℤ → ℤ) (env : VmRowEnv) (sites : List VmHashSite) : Prop :=
  go [] sites
where
  go : List ℤ → List VmHashSite → Prop
  | _,   []      => True
  | acc, s :: ss =>
    let d := hash (s.resolvedInputs env acc)
    env.loc s.digestCol = d ∧ go (acc ++ [d]) ss

/-! ## §5 — `EffectVmDescriptor`: the whole emitted circuit.

The descriptor bundles the name, trace width, PI count, the constraint list, the ordered hash
sites, and the range-checked balance wires (the field-soundness teeth, mirroring `RangeSpec`). -/

/-- A range-check tooth: wire `wire` must lie in `[0, 2^bits)`. -/
structure VmRange where
  wire : Nat
  bits : Nat
  deriving Repr, DecidableEq

/-- **`VmRange.holds env r`** — the range tooth's denotation: the wire's value lies in `[0, 2^bits)`.
This is the field-soundness tooth `satisfiedVm` now EVALUATES (it was inert before): a verifying
witness pins the (after-state balance) limb into `[0, 2^bits)`, so it is non-negative and
bounded — no field-wraparound underflow can disguise an over-debit as a small positive balance.
Combined with the per-effect balance-update gate (`post = pre − amt`), the post-balance non-neg tooth
is exactly AVAILABILITY (`amt ≤ pre`) over ℤ. -/
def VmRange.holds (env : VmRowEnv) (r : VmRange) : Prop :=
  0 ≤ env.loc r.wire ∧ env.loc r.wire < (2 : ℤ) ^ r.bits

/-- The emitted EffectVM descriptor. -/
structure EffectVmDescriptor where
  name        : String
  traceWidth  : Nat
  piCount     : Nat
  constraints : List VmConstraint
  hashSites   : List VmHashSite
  ranges      : List VmRange

/-! ## §6 — The denotation: `satisfiedVm`.

A descriptor is satisfied by `(env, isFirst, isLast)` iff:
  * every `gate` body vanishes on `loc`;
  * every `transition` continuity holds (`nxt (sbCol hi) = loc (saCol lo)`);
  * every `boundary first/last` body vanishes WHEN the corresponding flag is set;
  * every `piBinding first/last col k` holds WHEN the corresponding flag is set;
  * every hash site carries its genuine digest (under the abstract `hash`);
  * **every range tooth holds (`VmRange.holds`): the wire lies in `[0, 2^bits)`** — the
    field-soundness / availability / non-neg layer, now LIVE (it was inert when `satisfiedVm`
    dropped `d.ranges`; the running AIR `EffectVmDescriptorAir::eval` already enforces it).

The boundary/PI clauses are GUARDED by `isFirst`/`isLast` — matching `when_first_row()` /
`when_last_row()`, which are vacuous off the boundary. This is the faithful denotation of the
running AIR's row-quantified constraint set on a single row window. -/

/-- Meaning of one constraint on a row window with first/last flags.

`.gate` and `.transition` fire under the deployed Rust `builder.when_transition()` — every row
EXCEPT the last (the IR-v2 emitter `descriptor_ir2.rs` and the v1 hand-AIR both gate the per-row
algebra and the continuity on the transition domain `0..n-2`, where `nxt` is a genuine next row).
So both are GUARDED by `isLast = false`, exactly as `.boundary .last` / `.piBinding .last` guard
`isLast`: on the wrap row (`isLast = true`, where `nxt = zeroAsg`) they are vacuous, matching the
running circuit. This is the FAITHFUL denotation: a Lean rung may rely only on what the deployed
AIR actually forces. -/
def VmConstraint.holdsVm (env : VmRowEnv) (isFirst isLast : Bool) : VmConstraint → Prop
  | .gate body          => match isLast with | true => True | false => body.eval env.loc = 0
  | .transition hi lo   =>
      match isLast with | true => True | false => env.nxt (sbCol hi) = env.loc (saCol lo)
  | .boundary .first b  => isFirst = true → b.eval env.loc = 0
  | .boundary .last  b  => isLast = true → b.eval env.loc = 0
  | .piBinding .first col k => isFirst = true → env.loc col = env.pub k
  | .piBinding .last  col k => isLast = true → env.loc col = env.pub k

/-! ### `holdsVm` reduction lemmas — the STABLE interface to the row-quantified denotation.

`holdsVm` is the denotation EVERY rung consumes; its body shape (the `when_transition()` guard on
`.gate`/`.transition`, the `when_first/last_row()` guard on the boundary forms) is an implementation
detail a rung should not have to unfold by hand. These lemmas + the `reduce_holdsVm` tactic give the
stable surface: a rung names the ROW IT IS ON (active = `isLast = false`, wrap = `isLast = true`,
first = `isFirst = true`) and the constraint reduces to its plain content — `body = 0` / the
continuity equation / the PI equality — or to `True` where the deployed AIR does not bind it. Adding
a new guard to `holdsVm` later means re-proving these lemmas ONCE, not re-editing every rung. -/

/-- A `.gate` on a TRANSITION row (`isLast = false`) IS its body equation — the deployed
`when_transition()` arm binds. -/
@[simp] theorem holdsVm_gate_false (env : VmRowEnv) (isFirst : Bool) (body : EmittedExpr) :
    VmConstraint.holdsVm env isFirst false (.gate body) = (body.eval env.loc = 0) := rfl

/-- A `.gate` on the WRAP row (`isLast = true`) is vacuous — `when_transition()` does not fire. -/
@[simp] theorem holdsVm_gate_true (env : VmRowEnv) (isFirst : Bool) (body : EmittedExpr) :
    VmConstraint.holdsVm env isFirst true (.gate body) = True := rfl

/-- A `.transition` on a TRANSITION row IS its continuity equation. -/
@[simp] theorem holdsVm_transition_false (env : VmRowEnv) (isFirst : Bool) (hi lo : Nat) :
    VmConstraint.holdsVm env isFirst false (.transition hi lo)
      = (env.nxt (sbCol hi) = env.loc (saCol lo)) := rfl

/-- A `.transition` on the WRAP row is vacuous. -/
@[simp] theorem holdsVm_transition_true (env : VmRowEnv) (isFirst : Bool) (hi lo : Nat) :
    VmConstraint.holdsVm env isFirst true (.transition hi lo) = True := rfl

/-- A `.boundary .first` on the FIRST row IS its body equation. -/
@[simp] theorem holdsVm_boundaryFirst_true (env : VmRowEnv) (isLast : Bool) (b : EmittedExpr) :
    VmConstraint.holdsVm env true isLast (.boundary .first b) ↔ b.eval env.loc = 0 := by
  simp [VmConstraint.holdsVm]

/-- A `.boundary .last` on the LAST row IS its body equation. -/
@[simp] theorem holdsVm_boundaryLast_true (env : VmRowEnv) (isFirst : Bool) (b : EmittedExpr) :
    VmConstraint.holdsVm env isFirst true (.boundary .last b) ↔ b.eval env.loc = 0 := by
  simp [VmConstraint.holdsVm]

/-- A `.piBinding .first` on the FIRST row IS its PI equality. -/
@[simp] theorem holdsVm_piFirst_true (env : VmRowEnv) (isLast : Bool) (col k : Nat) :
    VmConstraint.holdsVm env true isLast (.piBinding .first col k) ↔ env.loc col = env.pub k := by
  simp [VmConstraint.holdsVm]

/-- A `.piBinding .last` on the LAST row IS its PI equality. -/
@[simp] theorem holdsVm_piLast_true (env : VmRowEnv) (isFirst : Bool) (col k : Nat) :
    VmConstraint.holdsVm env isFirst true (.piBinding .last col k) ↔ env.loc col = env.pub k := by
  simp [VmConstraint.holdsVm]

/-- **`holdsVm` at a known `isLast = false`, abstract `isFirst`.** A `.gate`/`.transition` reduces to
its plain content from the FACT that the row is a transition row — the form rungs that thread
`hnotlast : i + 1 ≠ t.rows.length` (whence `(i+1 == len) = false`) use. -/
theorem holdsVm_gate_of_notLast (env : VmRowEnv) (isFirst isLast : Bool) (body : EmittedExpr)
    (h : isLast = false) :
    VmConstraint.holdsVm env isFirst isLast (.gate body) = (body.eval env.loc = 0) := by
  subst h; rfl

theorem holdsVm_transition_of_notLast (env : VmRowEnv) (isFirst isLast : Bool) (hi lo : Nat)
    (h : isLast = false) :
    VmConstraint.holdsVm env isFirst isLast (.transition hi lo)
      = (env.nxt (sbCol hi) = env.loc (saCol lo)) := by
  subst h; rfl

-- The `@[simp]`-tagged `holdsVm_*` reduction lemmas above ARE the stable surface: a future change to
-- `holdsVm`'s guards is absorbed by re-proving those lemmas, then `simp only [holdsVm_gate_false, …]`
-- at the call sites. (A `reduce_holdsVm` wrapper tactic lived here but was removed — unused, and its
-- `(location)?` parser scoping did not compile; re-add it as its own clean pass if wanted.)

/-- **`satisfiedVm hash d env isFirst isLast`** — the emitted descriptor's denotation: every
constraint holds on the row window AND every hash site carries its genuine digest. -/
def satisfiedVm (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  (∀ c ∈ d.constraints, c.holdsVm env isFirst isLast)
    ∧ siteHoldsAll hash env d.hashSites
    ∧ (∀ r ∈ d.ranges, r.holds env)

/-! ## §6¾ — THE `system_roots`-ABSORBING GROUP-4 EXTENSION SITE (magnesium STAGE 4).

The deployed transfer commitment (`EffectVmEmitTransfer.site3`) absorbs `[inter1, inter2, inter3, 0]`
— the FOURTH slot is the spare literal `.zero`. A v2 descriptor REPLACES that spare slot with the
dedicated `sysRootsDigestCol` carrier, so the published `state_commit` now absorbs the side-table
`system_roots` digest. `sysRootsAbsorbSite` is the generic builder (it reads sites 0/1/2's digests
exactly as `site3` does, then absorbs the after-state digest column); a v2 descriptor's `hashSites`
is `[site0, site1, site2, sysRootsAbsorbSite]`. The deterministic site order is preserved (site 3
reads digests `[0..2]`), so the running prover's `hash_sites()` ordering contract is honoured. -/

/-- **`sysRootsAbsorbSite`** — the GROUP-4 extension site: `state_commit = H4(inter1, inter2, inter3,
sysRootsDigestCol)`. Replaces transfer's spare `.zero` 4th input with the dedicated `system_roots`
digest carrier, so the published commitment absorbs every side-table root. The inner digests
`[0..2]` are read by INDEX (`.digest 0/1/2`) — the site is placed 4th in the ordered list, exactly
where transfer's `site3` sits, so those references resolve to sites 0/1/2's digests identically; only
the `state_commit` result column is a parameter. -/
def sysRootsAbsorbSite (stateCommitCol : Nat) : VmHashSite :=
  { digestCol := stateCommitCol
  , inputs := [ .digest 0, .digest 1, .digest 2, .col sysRootsDigestCol ]
  , arity := 4 }

/-- The two dedicated `system_roots` carriers are DISTINCT from each other, from the base width
boundary, and (being `≥ EFFECT_VM_WIDTH = 188`) from every column the base layout claims (each
of which is `< 188`). So the widening is a clean, non-aliasing sub-block — unlike the early cohort's
`SYS_DIG_AFTER = 96` (which lands at `auxCol 6`, inside the balance-bit block). -/
theorem sysRootsDigest_cols_clean :
    sysRootsDigestCol = 188
    ∧ sysRootsDigestColBefore = 189
    ∧ sysRootsDigestCol ≠ sysRootsDigestColBefore
    ∧ EFFECT_VM_WIDTH ≤ sysRootsDigestCol
    ∧ EFFECT_VM_WIDTH ≤ sysRootsDigestColBefore
    ∧ sysRootsDigestCol < EFFECT_VM_WIDTH_SYSROOTS
    ∧ sysRootsDigestColBefore < EFFECT_VM_WIDTH_SYSROOTS := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide⟩

/-! ## §6½ — The SELECTOR-BINDING tooth (`selectorGate`).

The cutover verify path (`sdk/full_turn_proof.rs`) verifies an effect-vm descriptor sub-proof
against the descriptor for the EFFECT's selector. Before this tooth, all cutover descriptors
shared the same extended-AIR width / FRI shape and carried NO constraint reading the selector
columns, so a proof produced under selector `S` could re-verify under a DIFFERENT selector `S'`'s
descriptor AIR (the `full_turn_proof.rs` SOUNDNESS NOTE: "a frozen-frame / economic proof can
verify under several of these AIRs"). The post-state commitment was still pinned, but the proof
was NOT bound to ITS effect selector.

`selectorGate s` closes that: the per-row body `(1 - sel[NOOP]) · (1 - sel[s])` is asserted ZERO
on the transition domain (rows `0..n-2`, the `tb.assert_zero` the Rust `Gate` form enforces). On a
NoOp PAD row `sel[NOOP] = 1`, so the first factor is `0` and the body vanishes (pads never carry an
effect selector). On the single ACTIVE effect row `sel[NOOP] = 0`, so the body forces
`(1 - sel[s]) = 0`, i.e. `sel[s] = 1` — the descriptor's OWN selector column must be set. A trace
generated for a DIFFERENT effect `s'` has `sel[s] = 0` on its active row (the runtime sets exactly
one selector per row), so `(1 - 0)·(1 - 0) = 1 ≠ 0` and the descriptor for `s` REJECTS it. So a
descriptor proof now BINDS to its effect selector: descriptor-`s` accepts only `s`-traces.

It is a strict ADD: on every honest `s`-trace (active row has `sel[s] = 1`, pads have
`sel[NOOP] = 1`) the gate already holds, so the existing per-effect faithfulness / anti-ghost
theorems are unaffected; the gate ONLY removes the cross-selector replay. -/

/-- The selector-binding gate body for selector `s`: `(1 - sel[NOOP]) · (1 - sel[s])`. -/
def selectorGateBody (s : Nat) : EmittedExpr :=
  .mul
    (.add (.const 1) (.mul (.const (-1)) (.var sel.NOOP)))
    (.add (.const 1) (.mul (.const (-1)) (.var s)))

/-- The selector-binding constraint for selector `s` (a per-row `Gate`). -/
def selectorGate (s : Nat) : VmConstraint := .gate (selectorGateBody s)

/-- The selector-binding gate, as a one-element constraint list (the descriptor segment). -/
def selectorGates (s : Nat) : List VmConstraint := [selectorGate s]

/-- **The selector-binding gate's denotation (on the transition domain).** This is a `.gate`, so
under the deployed `when_transition()` it binds only off the last row. GIVEN `isLast = false`,
`selectorGate s` holds iff the row is a NoOp pad (`sel[NOOP] = 1`) OR carries selector `s`
(`sel[s] = 1`). In particular, on a NON-pad transition row (`sel[NOOP] = 0`) it forces `sel[s] = 1`.
(On the last row the gate is vacuous — matching the running circuit; see `_holds_of_active`/`_of_pad`,
which prove the honest direction without the `isLast` hypothesis.) -/
theorem selectorGate_holds_iff (s : Nat) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false) :
    (selectorGate s).holdsVm env isFirst isLast
      ↔ env.loc sel.NOOP = 1 ∨ env.loc s = 1 := by
  subst hlast
  simp only [selectorGate, selectorGateBody, VmConstraint.holdsVm, EmittedExpr.eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h) <;> rw [h] <;> ring

/-- **Selector-binding rejection.** On a NON-pad row (`sel[NOOP] = 0`) whose own selector column is
NOT set (`sel[s] ≠ 1`), `selectorGate s` REJECTS — the cross-selector replay tooth. A trace for a
different effect `s'` (which sets `sel[s'] = 1`, `sel[s] = 0`) is rejected by descriptor `s`. -/
theorem selectorGate_rejects_wrong_selector (s : Nat) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false) (hpad : env.loc sel.NOOP = 0) (hwrong : env.loc s ≠ 1) :
    ¬ (selectorGate s).holdsVm env isFirst isLast := by
  intro h
  rcases (selectorGate_holds_iff s env isFirst isLast hlast).mp h with h1 | h2
  · rw [hpad] at h1; exact absurd h1 (by norm_num)
  · exact hwrong h2

/-- **Selector-binding acceptance (the honest leg).** On a row carrying selector `s`
(`sel[s] = 1`), `selectorGate s` holds — every honest `s`-trace passes the tooth. -/
theorem selectorGate_holds_of_active (s : Nat) (env : VmRowEnv) (isFirst isLast : Bool)
    (hactive : env.loc s = 1) :
    (selectorGate s).holdsVm env isFirst isLast := by
  cases isLast with
  | true  => exact trivial
  | false =>
    simp only [selectorGate, selectorGateBody, VmConstraint.holdsVm, EmittedExpr.eval]
    rw [hactive]; ring

/-- **Selector-binding acceptance (the pad leg).** On a NoOp pad row (`sel[NOOP] = 1`),
`selectorGate s` holds — pad rows pass the tooth for every `s`. -/
theorem selectorGate_holds_of_pad (s : Nat) (env : VmRowEnv) (isFirst isLast : Bool)
    (hpad : env.loc sel.NOOP = 1) :
    (selectorGate s).holdsVm env isFirst isLast := by
  cases isLast with
  | true  => exact trivial
  | false =>
    simp only [selectorGate, selectorGateBody, VmConstraint.holdsVm, EmittedExpr.eval]
    rw [hpad]; ring

/-! ## §7 — Wire rendering (the canonical JSON the Rust decoder ingests).

A deterministic renderer for the EffectVM forms, mirroring the `lean_descriptor_air` grammar
(reusing PART-I's `EmittedExpr.toJson` for gate bodies) extended with `transition` / `boundary`
/ `pi_binding` / `hash_site` tags. The hash-site rendering carries the site ORDER (array order),
the result column, the arity, and the resolved input descriptors. -/

open Dregg2.Exec.CircuitEmit (EmittedExpr.toJson)

/-- Render a hash input as JSON. -/
def HashInput.toJson : HashInput → String
  | .col c   => "{\"t\":\"col\",\"c\":" ++ toString c ++ "}"
  | .digest k => "{\"t\":\"digest\",\"k\":" ++ toString k ++ "}"
  | .zero    => "{\"t\":\"zero\"}"

/-- Render an input list as a JSON array. -/
def inputsToJson : List HashInput → String
  | []      => "[]"
  | [i]     => "[" ++ i.toJson ++ "]"
  | i :: is => "[" ++ i.toJson ++ (is.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- Render one constraint as JSON. -/
def VmConstraint.toJson : VmConstraint → String
  | .gate body          => "{\"t\":\"gate\",\"body\":" ++ body.toJson ++ "}"
  | .transition hi lo   =>
      "{\"t\":\"transition\",\"hi\":" ++ toString hi ++ ",\"lo\":" ++ toString lo ++ "}"
  | .boundary r b       =>
      let rs := match r with | .first => "first" | .last => "last"
      "{\"t\":\"boundary\",\"row\":\"" ++ rs ++ "\",\"body\":" ++ b.toJson ++ "}"
  | .piBinding r col k   =>
      let rs := match r with | .first => "first" | .last => "last"
      "{\"t\":\"pi_binding\",\"row\":\"" ++ rs ++ "\",\"col\":" ++ toString col ++
        ",\"pi_index\":" ++ toString k ++ "}"

/-- Render a list of constraints as a JSON array. -/
def constraintsToJson : List VmConstraint → String
  | []      => "[]"
  | [c]     => "[" ++ c.toJson ++ "]"
  | c :: cs => "[" ++ c.toJson ++ (cs.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- Render one hash site as JSON. -/
def VmHashSite.toJson (s : VmHashSite) : String :=
  "{\"digest_col\":" ++ toString s.digestCol ++ ",\"arity\":" ++ toString s.arity ++
    ",\"inputs\":" ++ inputsToJson s.inputs ++ "}"

/-- Render a list of hash sites as a JSON array. -/
def hashSitesToJson : List VmHashSite → String
  | []      => "[]"
  | [s]     => "[" ++ s.toJson ++ "]"
  | s :: ss => "[" ++ s.toJson ++ (ss.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- Render one range as JSON. -/
def VmRange.toJson (r : VmRange) : String :=
  "{\"wire\":" ++ toString r.wire ++ ",\"bits\":" ++ toString r.bits ++ "}"

/-- Render a list of ranges as a JSON array. -/
def rangesToJson : List VmRange → String
  | []      => "[]"
  | [r]     => "[" ++ r.toJson ++ "]"
  | r :: rs => "[" ++ r.toJson ++ (rs.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- **`emitVmJson`** — the canonical wire string for an EffectVM descriptor. -/
def emitVmJson (d : EffectVmDescriptor) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"public_input_count\":" ++ toString d.piCount ++
  ",\"constraints\":" ++ constraintsToJson d.constraints ++
  ",\"hash_sites\":" ++ hashSitesToJson d.hashSites ++
  ",\"ranges\":" ++ rangesToJson d.ranges ++ "}"

/-! ## §8 — IR-widening tripwires (the additive `system_roots` column, verified backward-compatible). -/

-- The base width is 188 (the 97th aux column `STATE_RECORD_DIGEST` absorbed into the GROUP-4
-- commitment, plus the 98th aux column `ASSET_CLASS` row-0-pinned to `PI[v3.ASSET_CLASS]` —
-- `#guard …traceWidth == 188` everywhere).
#guard EFFECT_VM_WIDTH == 188
-- The widened width is exactly two dedicated carriers past the new boundary.
#guard EFFECT_VM_WIDTH_SYSROOTS == 190
#guard sysRootsDigestCol == 188
#guard sysRootsDigestColBefore == 189
-- The dedicated carriers do NOT alias each other or any 187-layout column (every aux slot is < 187).
#guard [sysRootsDigestCol, sysRootsDigestColBefore].dedup.length == 2
#guard decide (EFFECT_VM_WIDTH ≤ sysRootsDigestCol ∧ sysRootsDigestColBefore < EFFECT_VM_WIDTH_SYSROOTS)
-- The absorbing site replaces transfer's spare `.zero` 4th input with the `system_roots` carrier,
-- keeping the inner-digest references `[0..2]` (the GROUP-4 ordering contract).
#guard (sysRootsAbsorbSite (saCol state.STATE_COMMIT)).inputs
        == [HashInput.digest 0, HashInput.digest 1, HashInput.digest 2, HashInput.col sysRootsDigestCol]
#guard (sysRootsAbsorbSite (saCol state.STATE_COMMIT)).arity == 4

#assert_axioms sysRootsDigest_cols_clean

end Dregg2.Circuit.Emit.EffectVmEmit
