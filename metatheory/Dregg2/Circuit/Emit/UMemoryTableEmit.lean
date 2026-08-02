/-
# `Dregg2.Circuit.Emit.UMemoryTableEmit` — the UNIVERSAL memory op table's AIR, AUTHORED IN LEAN.

## What this replaces

`Ir2Air::UMemory` (`circuit/src/descriptor_ir2.rs`) is the op log of the UNIVERSAL memory argument:
one row per `umem_op`, addressing a cell of `Domain × κ` whose contents are an `Option` — a
`(present, value)` PAIR rather than the flat memory's single felt. It publishes each op's own image
on the ONE `ir2_umem_check` Blum multiset, consumes the prior image it claims, receives the gathered
`ir2_umem_log`, and QUERIES `ir2_umem_addrs` — the table the two universal BOUNDARY forms serve — for
address closure. On top of the flat memory's shape it carries the NULLIFIER insert-only tooth. Its
algebra was hand-authored Rust, which architectural law #1 forbids: *"circuits are emitted from Lean;
Rust only INTERPRETS."*

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `TExpr` under an explicit `RowSel`. Nothing in this cutover
hand-writes a Rust constraint, and the `law1_no_new_rust_authored_constraints` baseline for
`descriptor_ir2.rs` goes DOWN.

## The comment-only claims this port turns into theorems — and the TWO it refutes

The deleted arm asserted, in prose:

> Real rows form a prefix.
> Positional serials.
> Read discipline on the Option cell: a read returns its claimed prior cell.
> Canonical `none`: an absent cell carries payload 0 (the (present, value) pair is then a
>   faithful encoding of `Option` — Lean `optOf`).
> `prev_serial < serial` (Disciplined), exactly the flat memory's gap shape.
> Domain is a nibble (new state components are new codes, never new tables).
> THE INSERT-ONLY TOOTH (nullifiers): is_null is FORCED to the domain indicator, and a
>   nullifier-domain write installing `none` is UNSAT — `UniversalMemory.InsertOnlyAt`,
>   in-circuit. This is what upgrades a `present = 0` read into the PROVED freshness fact.
> The table carries EXACTLY the gathered log (umemTableFaithful).

§4 proves the first four and the forcing, and REFUTES two of the sentences as stated:

  * `serial_is_positional` — from the emitted `.first` anchor and `.transition` increment, under
    `Coherent`, row `i` carries serial `i + 1`.
  * `read_returns_its_claimed_cell` — BOTH components of the `Option`, which is the half that makes
    this table's read discipline stronger than the flat memory's (two gates, not one).
  * `canonical_none_is_forced` — an absent cell carries payload 0 on BOTH images, which is exactly
    what makes `(present, value)` a faithful `optOf` rather than a pair that merely agrees.
  * `is_null_is_the_domain_indicator` — ⚑ the forcing the tooth stands on, in BOTH directions, and
    the shape is sharper than the prose: at the nullifier domain the inverse-witness gate reads
    `is_null = is_real` EXACTLY, not `is_null = 1`.
  * `a_nullifier_write_cannot_install_none` — the insert-only tooth, on a REAL row.
  * ⚠ `wrapped_prev_serial_satisfies_every_gate` — **REFUTATION ONE, and the sentence refutes
    itself.** "exactly the flat memory's gap shape" is TRUE, and that shape does not bound: ⚑ there
    is NO magnitude gate on `UM_PREV_SERIAL` (contrast the boundary tables' `is_real·addr ∈
    [0,2^30)`). The gap gate *defines* `prev_serial = serial − 1 − gap` in the FIELD, so a one-row
    window at serial 1 claiming a prior serial of `p − 5` satisfies EVERY emitted gate. Here the
    witness is sharper than the flat memory's: it is a NULLIFIER-domain freshness read.
  * ⚠ `a_pad_row_spells_the_forbidden_nullifier_write` — **REFUTATION TWO.** "a nullifier-domain
    write installing `none` is UNSAT" is stated flat and is true only of REAL rows. The tooth
    `is_null·kind·(1 − present)` carries no `is_real` factor of its own; the gating arrives through
    `is_null`, which the inverse-witness gate forces to ZERO on a pad. So a PAD row spelling exactly
    the forbidden op — domain 3, `kind = 1`, `present = 0`, `prev_present = 1` — satisfies every
    gate. A reader of the tooth alone cannot see that, because the factor that disarms it is two
    gates away.

## ⚠ The containments, which live in a DIFFERENT object

Both refutations are contained OUTSIDE this table, and neither containment is a gate:

  * the wrapped prior serial is refused by the `ir2_umem_check` multiset — nothing ever PUBLISHES a
    tuple at serial `p − 5`, so the permutation cannot balance;
  * the pad row's forbidden write is refused by the same multiset plus `ir2_umem_log`: every one of
    this table's four multiset/log legs rides at `is_real`, so a pad contributes NOTHING and declares
    NOTHING.

That is a property of the assembled instance family — precisely the half `TableAir.Holds` does not
speak about (`TableAirIR` §3) — and it is written down here because a reader of this table alone
would take the gap gate for a bound and the tooth for an unconditional refusal.

⚠ **A THIRD RESIDUAL, and it is not refuted anywhere in this file.** `UM_KEY` — the column that says
WHICH cell of `Domain × κ` an op touches — is read by NO gate on any row
(`key_is_read_by_no_gate`). What binds it is the `ir2_umem_addrs` closure lookup and the
`ir2_umem_check` multiset, both bus legs. So a mutation sweep over the gates is structurally blind to
the key, and that is a fact about the mechanism rather than a gap in the sweep.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Crypto enters nowhere: this file is the ALGEBRA of an
op log over `Option` cells and the integer-faithfulness of its discipline claims.
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.Emit.UMemoryTableEmit

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.TableAirIR
  (TExpr BusOp BusInteraction TableAir TableGate Coherent emitTableAirJson
   v n k eSub eOneMinus gBool gAll gFirst gTrans decompGates decompQueries limbGeom decompCols)

set_option autoImplicit false

/-! ## §1 — The deployed column layout.

Transcribed from `descriptor_ir2.rs`'s `UM_*` constants. The `#guard`s derive each offset from the
one before it, so a layout drift on either side cannot be silent.

⚑ The first EIGHT columns are the `ir2_umem_log` tuple in order — `build_traces` writes
`row.extend_from_slice(&tuple)` and then appends — which is why the log receive below reads
`v 0 … v 7` contiguously. -/

/-- `MEM_GAP_BITS`, shared with the flat memory (the universal op log reuses its gap shape
verbatim, hole included — see §4c). -/
def GAP_BITS : Nat := 30
/-- `2 ^ MEM_GAP_BITS` — the ceiling the serial-gap range check imposes. -/
def GAP_CEIL : ℤ := 1073741824
/-- Columns one 30-bit decomposition costs (`decomp_cols(30)`). -/
def DECOMP : Nat := decompCols GAP_BITS

def UM_DOMAIN : Nat := 0
def UM_KEY : Nat := 1
def UM_PRESENT : Nat := 2
def UM_VALUE : Nat := 3
def UM_PREV_PRESENT : Nat := 4
def UM_PREV_VALUE : Nat := 5
def UM_PREV_SERIAL : Nat := 6
def UM_KIND : Nat := 7
def UM_SERIAL : Nat := 8
def UM_IS_REAL : Nat := 9
def UM_GAP : Nat := 10
def UM_GAP_LIMB0 : Nat := 11
def UM_IS_NULL : Nat := UM_GAP_LIMB0 + DECOMP
def UM_NULL_INV : Nat := UM_IS_NULL + 1
/-- `UM_WIDTH`. -/
def UM_WIDTH : Nat := UM_NULL_INV + 1

-- The deployed numbers, pinned.
#guard DECOMP == 10
#guard limbGeom GAP_BITS == (8, 2)
#guard UM_IS_NULL == 21
#guard UM_NULL_INV == 22
#guard UM_WIDTH == 23
#guard GAP_CEIL == 2 ^ GAP_BITS
theorem gap_ceil_lt_p : GAP_CEIL < 2013265921 := by decide

/-- `NULLIFIER_DOMAIN`, verbatim from the Rust constant. The one domain code the insert-only tooth
is keyed to. -/
def NULLIFIER_DOMAIN : ℤ := 3

/-- The bus names, verbatim from the Rust `BUS_*` constants. -/
def BUS_BYTE : String := "ir2_byte"
def BUS_UMEM_LOG : String := "ir2_umem_log"
def BUS_UMEM_CHECK : String := "ir2_umem_check"
def BUS_UMEM_ADDRS : String := "ir2_umem_addrs"

/-! ## §2 — THE TABLE. -/

/-- `is_real`, the row guard. -/
def gReal : TExpr := v UM_IS_REAL
/-- `domain − 3`, the nullifier-domain indicator's argument (the Rust `dom_m3`). -/
def domM3 : TExpr := eSub (v UM_DOMAIN) (k NULLIFIER_DOMAIN)

/-- The gate list, in the deleted Rust arm's emission order.

  * (1)–(5) `.all` — the row guard, the op KIND (`kind = 1` is a write), BOTH presence bits and the
    nullifier indicator are boolean.
  * (6) `.transition` — real rows form a PREFIX, so the op log is a contiguous initial segment.
  * (7) `.first` / (8) `.transition` — the POSITIONAL serial chain. ⚑ `.first`+`.transition` and not
    `.all`: on the last row p3's `nxt` is the WRAP row, where the increment is false at every height
    above 1.
  * (9)(10) `.all` — READ DISCIPLINE on the `Option` cell: a real read returns its claimed prior
    cell in BOTH components. Two gates, where the flat memory has one, because the cell is a pair.
  * (11)(12) `.all` — CANONICAL `none`: an absent cell carries payload 0, on the op's own image and
    on the prior one it claims. This is what makes `(present, value)` a faithful `optOf`.
  * (13) `.all` — the SERIAL GAP definition, range-checked by (14)–(17). ⚠ This DEFINES
    `prev_serial`; it does not bound it (§4c).
  * (18)(19) `.all` — ⚑ THE NULLIFIER INDICATOR, FORCED: `(domain − 3)·is_null = 0` kills the
    indicator off-domain, and `(domain − 3)·null_inv = is_real − is_null` is the inverse witness that
    forces it ON at the domain. At `domain = 3` the second reads `is_null = is_real` exactly.
  * (20) `.all` — ⚑ THE INSERT-ONLY TOOTH: a nullifier-domain WRITE (`kind = 1`) installing an
    ABSENT cell (`present = 0`) is UNSAT. ⚠ It carries no `is_real` factor of its own; the gating
    arrives through `is_null`, which (19) forces to ZERO on a pad — see §4c. -/
def umemGates : List TableGate :=
  [ gAll (gBool UM_IS_REAL)
  , gAll (gBool UM_KIND)
  , gAll (gBool UM_PRESENT)
  , gAll (gBool UM_PREV_PRESENT)
  , gAll (gBool UM_IS_NULL)
  , gTrans (.mul (eOneMinus (v UM_IS_REAL)) (n UM_IS_REAL))
  , gFirst (eSub (v UM_SERIAL) (k 1))
  , gTrans (eSub (eSub (n UM_SERIAL) (v UM_SERIAL)) (k 1))
  , gAll (.mul (.mul gReal (eOneMinus (v UM_KIND)))
      (eSub (v UM_PRESENT) (v UM_PREV_PRESENT)))
  , gAll (.mul (.mul gReal (eOneMinus (v UM_KIND)))
      (eSub (v UM_VALUE) (v UM_PREV_VALUE)))
  , gAll (.mul (.mul gReal (eOneMinus (v UM_PRESENT))) (v UM_VALUE))
  , gAll (.mul (.mul gReal (eOneMinus (v UM_PREV_PRESENT))) (v UM_PREV_VALUE))
  , gAll (eSub (v UM_GAP)
      (.mul gReal (eSub (eSub (v UM_SERIAL) (k 1)) (v UM_PREV_SERIAL)))) ] ++
  (decompGates GAP_BITS (v UM_GAP) UM_GAP_LIMB0).map gAll ++
  [ gAll (.mul domM3 (v UM_IS_NULL))
  , gAll (eSub (.mul domM3 (v UM_NULL_INV)) (eSub gReal (v UM_IS_NULL)))
  , gAll (.mul (.mul (v UM_IS_NULL) (v UM_KIND)) (eOneMinus (v UM_PRESENT))) ]

/-- The bus interactions, in the deleted Rust arm's emission order.

  * the gap decomposition's limb queries (multiplicity 1, as deployed — `eval_decomp` is the
    UNCOUNTED variant, so a pad row still queries),
  * ⚑ the DOMAIN nibble query, also at multiplicity 1 and therefore on EVERY row including pads.
    That is the whole of "domain is a nibble": a BUS leg, invisible to `Holds`,
  * the gathered op log (`umemTableFaithful`) at `is_real` — the eight-felt tuple that is this
    table's first eight columns verbatim,
  * the two Blum legs of the ONE multiset over `Domain × κ`: this op PUBLISHES its own `Option` image
    at its own serial and CONSUMES the prior image it claims,
  * and the ADDRESS CLOSURE query against the table the universal BOUNDARY serves. ⚑ `.query`, not
    `.provide`: this table is the CLIENT of `ir2_umem_addrs`. -/
def umemInteractions : List BusInteraction :=
  decompQueries GAP_BITS BUS_BYTE UM_GAP_LIMB0 (k 1) ++
  [ ⟨BUS_BYTE, .query, k 1, [v UM_DOMAIN]⟩
  , ⟨BUS_UMEM_LOG, .receive, gReal,
      [v UM_DOMAIN, v UM_KEY, v UM_PRESENT, v UM_VALUE, v UM_PREV_PRESENT, v UM_PREV_VALUE,
       v UM_PREV_SERIAL, v UM_KIND]⟩
  , ⟨BUS_UMEM_CHECK, .send, gReal,
      [v UM_DOMAIN, v UM_KEY, v UM_PRESENT, v UM_VALUE, v UM_SERIAL]⟩
  , ⟨BUS_UMEM_CHECK, .receive, gReal,
      [v UM_DOMAIN, v UM_KEY, v UM_PREV_PRESENT, v UM_PREV_VALUE, v UM_PREV_SERIAL]⟩
  , ⟨BUS_UMEM_ADDRS, .query, gReal, [v UM_DOMAIN, v UM_KEY]⟩ ]

/-- **`umemoryTable`** — the universal memory op table's AIR, as a Lean object. -/
def umemoryTable : TableAir :=
  { name         := "dregg-ir2-umemory-v1"
  , width        := UM_WIDTH
  , defs         := []
  , gates        := umemGates
  , interactions := umemInteractions }

/-! ## §3 — Shape pins.

Counts derived from the layout, not transcribed: `5 + 1 + 2 + 2 + 2 + 1 + 4 + 2 + 1 = 20` gates and
`7 + 1 + 1 + 2 + 1 = 12` interactions. -/

#guard umemoryTable.width == 23
#guard umemoryTable.gates.length == 20
#guard umemoryTable.busCount == 12
#guard umemoryTable.busCountOn BUS_BYTE == 8
#guard umemoryTable.busCountOn BUS_UMEM_LOG == 1
#guard umemoryTable.busCountOn BUS_UMEM_CHECK == 2
#guard umemoryTable.busCountOn BUS_UMEM_ADDRS == 1

-- ⚑ SELECTOR pins. Exactly two gates are transition-scoped (the real prefix and the serial
-- increment) and exactly ONE is first-scoped (the serial anchor). By `TableGate.transition_weakens`
-- a drift toward `.transition` accepts STRICTLY MORE while leaving the algebra byte-identical, so
-- the scope is pinned rather than left to the body.
#guard umemoryTable.gateCountSel .all == 17
#guard umemoryTable.gateCountSel .transition == 2
#guard umemoryTable.gateCountSel .first == 1
#guard umemoryTable.gateCountSel .last == 0

-- ⚑ BUS-SIDE pins. This table QUERIES `ir2_umem_addrs` and `ir2_byte`; it SERVES nothing. The two
-- universal BOUNDARY forms are the server of `ir2_umem_addrs`, and a swap here would make the
-- address-closure argument unsatisfiable in one direction and vacuous in the other — with no gate
-- involved and therefore nothing a mutation sweep could see.
#guard umemoryTable.busCountOp BUS_UMEM_ADDRS .query == 1
#guard umemoryTable.busCountOp BUS_UMEM_ADDRS .provide == 0
#guard umemoryTable.busCountOp BUS_BYTE .query == 8
#guard umemoryTable.busCountOp BUS_BYTE .provide == 0
-- The Blum pair: this op PUBLISHES its own image and CONSUMES the prior one. A swap here reverses
-- the whole read-consistency argument.
#guard umemoryTable.busCountOp BUS_UMEM_CHECK .send == 1
#guard umemoryTable.busCountOp BUS_UMEM_CHECK .receive == 1
#guard umemoryTable.busCountOp BUS_UMEM_LOG .receive == 1
#guard umemoryTable.busCountOp BUS_UMEM_LOG .send == 0

-- The table is NOT row-local — the serial chain and the real prefix read `nxt` — which is why it
-- could not be ported against the first-pass IR.
#guard umemoryTable.isRowLocal == false

/-! ## §4 — THE COMMENT-ONLY CLAIMS, PROVED — and the two REFUTED.

§4a takes the positional-serial claim straight off the EMITTED gates under `Coherent`. §4b states the
remaining gate equations as ℤ facts and derives the read discipline, the canonical-`none`
faithfulness, the nullifier forcing and the insert-only tooth. §4c exhibits the two witnesses that
refute the sentences AS STATED, on the emitted object. -/

/-! ### §4a — The serial column IS the positional index (+1). -/

/-- The first-row gate, unpacked: row 0 carries serial 1. -/
theorem first_row_serial_is_one {rows : List VmRowEnv}
    (hh : umemoryTable.Holds rows) (h : 0 < rows.length) :
    rows[0].loc UM_SERIAL ≡ 1 [ZMOD 2013265921] := by
  have hg := hh 0 h ⟨.first, eSub (v UM_SERIAL) (k 1)⟩
    (by simp [umemoryTable, umemGates, gFirst])
  simp only [TableGate.holdsAt] at hg
  have hz := hg (by simp)
  simp only [eSub, v, k, TExpr.evalWith] at hz
  unfold Int.ModEq at hz ⊢
  omega

/-- The transition gate, unpacked: on any non-final row the NEXT window's serial is one more. -/
theorem serial_step {rows : List VmRowEnv}
    (hh : umemoryTable.Holds rows) (i : Nat) (hlt : i < rows.length) (h : i + 1 < rows.length) :
    rows[i].nxt UM_SERIAL ≡ rows[i].loc UM_SERIAL + 1 [ZMOD 2013265921] := by
  have hg := hh i hlt ⟨.transition, eSub (eSub (n UM_SERIAL) (v UM_SERIAL)) (k 1)⟩
    (by simp [umemoryTable, umemGates, gTrans])
  simp only [TableGate.holdsAt] at hg
  have hz := hg (by simp; omega)
  simp only [eSub, v, n, k, TExpr.evalWith] at hz
  unfold Int.ModEq at hz ⊢
  omega

/-- ⚑ **THE SERIAL CONVENTION, PROVED.** On a COHERENT accepting trace row `i` carries serial
`i + 1` — the sentence the deleted arm compressed to "Positional serials.", and the index the
universal-memory soundness argument counts against.

⚠ `Coherent` is not decoration: without it `rows[i].nxt` is an unconstrained function and the
increment chain says nothing about `rows[i+1]`, so the whole claim would be about a machine that does
not exist. -/
theorem serial_is_positional {rows : List VmRowEnv}
    (hc : Coherent rows) (hh : umemoryTable.Holds rows) :
    ∀ i, ∀ h : i < rows.length,
      rows[i].loc UM_SERIAL ≡ (i : ℤ) + 1 [ZMOD 2013265921] := by
  intro i
  induction i with
  | zero => intro h; simpa using first_row_serial_is_one hh h
  | succ m ih =>
    intro h
    have hm : m + 1 < rows.length := h
    have hlt : m < rows.length := by omega
    have hstep := serial_step hh m hlt hm
    have hcoh : rows[m].nxt = rows[m + 1].loc := hc m hm
    rw [hcoh] at hstep
    have hfin : rows[m + 1].loc UM_SERIAL ≡ ((m : ℤ) + 1) + 1 [ZMOD 2013265921] :=
      hstep.trans (Int.ModEq.add_right 1 (ih (by omega)))
    push_cast
    simpa [add_assoc] using hfin

/-! ### §4b — The discipline claims and the nullifier forcing, over ℤ. -/

/-- The gate equations of an `m`-row universal op-log trace, as integer facts. Each field names the
gate it comes from; `gapRange` is what the 30-bit decomposition (gates 14–17) delivers.

⚠ These are facts about the ℤ LIFT the honest prover writes, exactly as `MemoryTableEmit.MemoryFacts`
is. §4c shows where the FELT is not so constrained. -/
structure UMemFacts (m : Nat) where
  domain      : Nat → ℤ
  present     : Nat → ℤ
  value       : Nat → ℤ
  prevPresent : Nat → ℤ
  prevValue   : Nat → ℤ
  prevSerial  : Nat → ℤ
  kind        : Nat → ℤ
  serial      : Nat → ℤ
  real        : Nat → ℤ
  gap         : Nat → ℤ
  isNull      : Nat → ℤ
  nullInv     : Nat → ℤ
  /-- gate (1), `.all`. -/
  realBool    : ∀ i, i < m → real i = 0 ∨ real i = 1
  /-- gate (2), `.all`. -/
  kindBool    : ∀ i, i < m → kind i = 0 ∨ kind i = 1
  /-- gate (3), `.all`. -/
  presentBool : ∀ i, i < m → present i = 0 ∨ present i = 1
  /-- gate (4), `.all`. -/
  prevPresentBool : ∀ i, i < m → prevPresent i = 0 ∨ prevPresent i = 1
  /-- gate (6), `.transition`: real rows form a prefix. -/
  prefixReal  : ∀ i, i + 1 < m → (1 - real i) * real (i + 1) = 0
  /-- gate (7), `.first`. -/
  serialOne   : 0 < m → serial 0 = 1
  /-- gate (8), `.transition`. -/
  serialStep  : ∀ i, i + 1 < m → serial (i + 1) - serial i - 1 = 0
  /-- gate (9), `.all`: a real read returns its claimed prior PRESENCE. -/
  readPresent : ∀ i, i < m → real i * (1 - kind i) * (present i - prevPresent i) = 0
  /-- gate (10), `.all`: …and its claimed prior VALUE. -/
  readValue   : ∀ i, i < m → real i * (1 - kind i) * (value i - prevValue i) = 0
  /-- gate (11), `.all`: an absent cell carries payload 0. -/
  canonNone   : ∀ i, i < m → real i * (1 - present i) * value i = 0
  /-- gate (12), `.all`: …and so does the claimed prior cell. -/
  canonNonePrev : ∀ i, i < m → real i * (1 - prevPresent i) * prevValue i = 0
  /-- gate (13), `.all`: the serial-gap DEFINITION. -/
  gapDef      : ∀ i, i < m → gap i = real i * (serial i - 1 - prevSerial i)
  /-- gates (14)–(17): the gap is 30-bit. -/
  gapRange    : ∀ i, i < m → 0 ≤ gap i ∧ gap i < GAP_CEIL
  /-- gate (18), `.all`: off the nullifier domain the indicator is dead. -/
  nullOffDom  : ∀ i, i < m → (domain i - NULLIFIER_DOMAIN) * isNull i = 0
  /-- gate (19), `.all`: the INVERSE WITNESS that forces the indicator on-domain. -/
  nullInvGate : ∀ i, i < m →
    (domain i - NULLIFIER_DOMAIN) * nullInv i - (real i - isNull i) = 0
  /-- gate (20), `.all`: THE INSERT-ONLY TOOTH. -/
  insertOnly  : ∀ i, i < m → isNull i * kind i * (1 - present i) = 0

variable {m : Nat}

/-- The PREFIX property, unpacked: a real row's predecessor is real. -/
theorem real_of_succ (F : UMemFacts m) {i : Nat} (h : i + 1 < m)
    (hr : F.real (i + 1) = 1) : F.real i = 1 := by
  have hp := F.prefixReal i h
  rw [hr, mul_one] at hp
  linarith

/-- The serial chain over ℤ: row `i` carries serial `i + 1`. The lift of §4a. -/
theorem serial_eq_index (F : UMemFacts m) : ∀ i, i < m → F.serial i = (i : ℤ) + 1 := by
  intro i
  induction i with
  | zero => intro h; simpa using F.serialOne h
  | succ t ih =>
    intro h
    have hs := F.serialStep t h
    have := ih (by omega)
    push_cast
    linarith

/-- ⚑ **READ DISCIPLINE ON THE `Option` CELL.** A real READ row (`kind = 0`) returns exactly the cell
it claims was there — BOTH components. This is the half that makes the universal read discipline
stronger than the flat memory's: the cell is a pair, so it takes two gates, and a port that dropped
either one would leave a read free to invent a presence bit or a payload. -/
theorem read_returns_its_claimed_cell (F : UMemFacts m) {i : Nat} (h : i < m)
    (hr : F.real i = 1) (hk : F.kind i = 0) :
    F.present i = F.prevPresent i ∧ F.value i = F.prevValue i := by
  have hp := F.readPresent i h
  have hv := F.readValue i h
  rw [hr, hk] at hp hv
  simp only [one_mul, sub_zero] at hp hv
  constructor <;> linarith

/-- ⚑ **CANONICAL `none`, PROVED — the `optOf` faithfulness.** On a real row an ABSENT cell carries
payload ZERO, on the op's own image and on the prior one it claims. Without this the `(present,
value)` pair would not be a faithful encoding of `Option`: two rows could denote the same `none` while
committing different payloads, and the Blum multiset compares the PAIR. -/
theorem canonical_none_is_forced (F : UMemFacts m) {i : Nat} (h : i < m) (hr : F.real i = 1) :
    (F.present i = 0 → F.value i = 0) ∧ (F.prevPresent i = 0 → F.prevValue i = 0) := by
  have hc := F.canonNone i h
  have hcp := F.canonNonePrev i h
  rw [hr, one_mul] at hc hcp
  constructor
  · intro hp; rw [hp] at hc; simpa using hc
  · intro hp; rw [hp] at hcp; simpa using hcp

/-- ⚑ **THE NULLIFIER INDICATOR IS FORCED, DIRECTION ONE (off-domain).** A row whose domain is not
the nullifier code cannot claim the indicator. -/
theorem is_null_dead_off_domain (F : UMemFacts m) {i : Nat} (h : i < m)
    (hd : F.domain i ≠ NULLIFIER_DOMAIN) : F.isNull i = 0 := by
  have hg := F.nullOffDom i h
  have hne : F.domain i - NULLIFIER_DOMAIN ≠ 0 := sub_ne_zero_of_ne hd
  exact (mul_eq_zero.mp hg).resolve_left hne

/-- ⚑ **THE NULLIFIER INDICATOR IS FORCED, DIRECTION TWO (on-domain) — and the shape is SHARPER than
the prose.** The deleted comment says "is_null is FORCED to the domain indicator". At the nullifier
domain the inverse-witness gate degenerates to `is_null = is_real` EXACTLY: on a real row the
indicator is 1 and a prover cannot switch it off, and on a PAD row it is forced to ZERO. The second
half is what §4c turns into a refutation — the tooth's only `is_real` gating arrives through here. -/
theorem is_null_eq_real_on_domain (F : UMemFacts m) {i : Nat} (h : i < m)
    (hd : F.domain i = NULLIFIER_DOMAIN) : F.isNull i = F.real i := by
  have hg := F.nullInvGate i h
  rw [hd] at hg
  simp only [sub_self, zero_mul, zero_sub, neg_sub] at hg
  linarith

/-- …and therefore the indicator IS the domain indicator, on a real row: `is_null = 1` exactly when
the domain is the nullifier code. -/
theorem is_null_is_the_domain_indicator (F : UMemFacts m) {i : Nat} (h : i < m)
    (hr : F.real i = 1) : F.isNull i = 1 ↔ F.domain i = NULLIFIER_DOMAIN := by
  constructor
  · intro hn
    by_contra hd
    exact absurd (is_null_dead_off_domain F h hd) (by rw [hn]; decide)
  · intro hd; rw [is_null_eq_real_on_domain F h hd, hr]

/-- ⚑ **THE INSERT-ONLY TOOTH, PROVED.** A REAL nullifier-domain WRITE installing an ABSENT cell is
UNSAT — nobody un-spends, in-circuit. This is the `UniversalMemory.InsertOnlyAt` discipline the
deleted comment named, and it is what upgrades a `present = 0` read at the nullifier domain into a
freshness fact *given* the Blum chain.

⚠ Read the hypotheses. `real i = 1` is one of them, and it is NOT carried by the tooth's own
polynomial — §4c exhibits the pad row where every hypothesis but that one holds and the gates are
green. -/
theorem a_nullifier_write_cannot_install_none (F : UMemFacts m) {i : Nat} (h : i < m)
    (hr : F.real i = 1) (hd : F.domain i = NULLIFIER_DOMAIN) (hk : F.kind i = 1)
    (hp : F.present i = 0) : False := by
  have hn : F.isNull i = 1 := by rw [is_null_eq_real_on_domain F h hd, hr]
  have ht := F.insertOnly i h
  rw [hn, hk, hp] at ht
  norm_num at ht

/-- ⚑ **`Disciplined`, THE PRIOR-SERIAL CONJUNCT — OF THE LIFT.** Over ℤ the claimed prior serial is
at most the row index, i.e. strictly below the op's own serial `i + 1`.

⚠ Read the quantifier: this is a statement about the ℤ-valued `prevSerial` field, i.e. about the lift
the honest prover writes. §4c shows the FELT is not so constrained. -/
theorem prev_serial_le_index (F : UMemFacts m) {i : Nat} (h : i < m) (hr : F.real i = 1) :
    F.prevSerial i ≤ (i : ℤ) ∧ F.prevSerial i < F.serial i := by
  have hd := F.gapDef i h
  rw [hr, one_mul] at hd
  have hg := (F.gapRange i h).1
  rw [hd] at hg
  have hs := serial_eq_index F i h
  constructor <;> linarith

/-! ### §4c — ⚠ THE TWO REFUTATIONS, on the EMITTED object.

Both are `decide`d against `umemoryTable`'s own gate list via `TableGate.instDecidableHoldsAt`, not
against a transcription of it — which is the step a cutover exists to delete. -/

/-- `p − 5`: the wrapped prior serial. Above `2^30`, and therefore above every serial this table can
ever publish. -/
def WRAP_PREV : ℤ := 2013265916

/-- A ONE-ROW window (first AND last, so both `.transition` gates are vacuous and the wrap row never
enters) at the NULLIFIER domain, reading an absent cell — the freshness shape — while claiming a
prior serial of `p − 5` at its own serial 1, with the 5-gap honestly decomposed: limb 0 is 5, every
other limb and both top bits are 0. The indicator is 1, as gate (19) forces at `domain = 3` on a real
row, and the inverse witness is 0, as gate (19) then permits. -/
def wrapRow : VmRowEnv :=
  ⟨fun c =>
      if c = UM_DOMAIN then NULLIFIER_DOMAIN
      else if c = UM_PREV_SERIAL then WRAP_PREV
      else if c = UM_SERIAL then 1
      else if c = UM_IS_REAL then 1
      else if c = UM_GAP then 5
      else if c = UM_GAP_LIMB0 then 5
      else if c = UM_IS_NULL then 1
      else 0
  , fun _ => 0, fun _ => 0⟩

/-- ⚑ **REFUTATION ONE, ON THE EMITTED OBJECT.** Every gate of `umemoryTable` — the emitted list, not
a transcription — vanishes on `wrapRow`, and the claimed prior serial it carries is ABOVE `2^30`
while the op's own serial is 1. So "`prev_serial < serial` (Disciplined), exactly the flat memory's
gap shape" is a sentence that refutes itself: the shape IS the flat memory's, and ⚑ **there is no
magnitude gate on `UM_PREV_SERIAL`**, so the gap gate DEFINES the claimed serial in the field rather
than bounding it. `prev_serial < serial` is a property of the honest prover's LIFT (§4b's
`prev_serial_le_index`), not a verdict of the row algebra.

⚠ Direction, said plainly: this is not a defect in the deployed prover. What refuses the witness is
the `ir2_umem_check` multiset in the assembled batch — nothing ever PUBLISHES a tuple at serial
`p − 5`, so the permutation cannot balance — which is a containment about a DIFFERENT object and is
exactly the half `TableAir.Holds` is silent on (`TableAirIR` §3). ⓘ And the witness is a NULLIFIER
freshness read, which is where the consequence would land: a row claiming to have consumed a cell
from a serial that no op can occupy. -/
theorem wrapped_prev_serial_satisfies_every_gate :
    umemoryTable.RowHolds wrapRow true true ∧
    wrapRow.loc UM_SERIAL = 1 ∧
    wrapRow.loc UM_DOMAIN = NULLIFIER_DOMAIN ∧
    GAP_CEIL ≤ wrapRow.loc UM_PREV_SERIAL ∧
    ¬ (wrapRow.loc UM_PREV_SERIAL < wrapRow.loc UM_SERIAL) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- A PAD row (`is_real = 0`) spelling EXACTLY the op the insert-only tooth is supposed to refuse: the
nullifier domain, a WRITE (`kind = 1`), installing an ABSENT cell (`present = 0`) over a cell it
claims WAS present (`prev_present = 1`, payload 9). The indicator is 0 — which gate (19) does not
merely permit but FORCES at `is_real = 0` (`is_null_eq_real_on_domain`) — and that zero is what
disarms the tooth. -/
def padNullifierDelete : VmRowEnv :=
  ⟨fun c =>
      if c = UM_DOMAIN then NULLIFIER_DOMAIN
      else if c = UM_KIND then 1
      else if c = UM_PREV_PRESENT then 1
      else if c = UM_PREV_VALUE then 9
      else if c = UM_SERIAL then 1
      else 0
  , fun _ => 0, fun _ => 0⟩

/-- ⚑ **REFUTATION TWO, ON THE EMITTED OBJECT.** "A nullifier-domain write installing `none` is
UNSAT" is stated flat in the deleted comment and is true only of REAL rows. The tooth
`is_null·kind·(1 − present)` carries NO `is_real` factor; the gating arrives two gates away, through
the inverse-witness gate that forces `is_null = is_real` at the nullifier domain. So this pad row —
domain 3, `kind = 1`, `present = 0`, `prev_present = 1` — satisfies EVERY emitted gate while spelling
the forbidden op.

⚠ The containment, again outside this table: every one of this table's four `ir2_umem_log` /
`ir2_umem_check` / `ir2_umem_addrs` legs rides at `is_real`, so a pad row declares NOTHING to the log,
publishes NOTHING to the multiset and asks NOTHING of the closure table. What a reader must not
conclude is that the tooth alone refuses the write; what refuses it is the tooth **on the rows the bus
legs are alive on**, which is a fact about the multiplicity expressions and not about the gates. -/
theorem a_pad_row_spells_the_forbidden_nullifier_write :
    umemoryTable.RowHolds padNullifierDelete true true ∧
    padNullifierDelete.loc UM_IS_REAL = 0 ∧
    padNullifierDelete.loc UM_DOMAIN = NULLIFIER_DOMAIN ∧
    padNullifierDelete.loc UM_KIND = 1 ∧
    padNullifierDelete.loc UM_PRESENT = 0 ∧
    padNullifierDelete.loc UM_PREV_PRESENT = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- …and the CONTRAST that keeps both refutations from reading as "no gate bites here": the same op
on a REAL row is REFUSED, in BOTH spellings of the indicator. With `is_null = 1` the tooth fires;
with `is_null = 0` the inverse-witness gate fires instead. A prover has no third choice, which is
what makes `a_nullifier_write_cannot_install_none` a real tooth rather than a hypothesis. -/
def realNullifierDelete (isNull : ℤ) : VmRowEnv :=
  ⟨fun c =>
      if c = UM_DOMAIN then NULLIFIER_DOMAIN
      else if c = UM_KIND then 1
      else if c = UM_PREV_PRESENT then 1
      else if c = UM_PREV_VALUE then 9
      else if c = UM_SERIAL then 1
      else if c = UM_IS_REAL then 1
      else if c = UM_IS_NULL then isNull
      else 0
  , fun _ => 0, fun _ => 0⟩

theorem a_real_nullifier_delete_is_refused_either_way :
    ¬ umemoryTable.RowHolds (realNullifierDelete 1) true true ∧
    ¬ umemoryTable.RowHolds (realNullifierDelete 0) true true := by
  refine ⟨by decide, by decide⟩

/-- The honest pole: a real nullifier-domain FRESHNESS READ at serial 1 — absent cell, absent claimed
prior cell, prior serial 0 — is ACCEPTED. -/
def honestRow : VmRowEnv :=
  ⟨fun c =>
      if c = UM_DOMAIN then NULLIFIER_DOMAIN
      else if c = UM_SERIAL then 1
      else if c = UM_IS_REAL then 1
      else if c = UM_IS_NULL then 1
      else 0
  , fun _ => 0, fun _ => 0⟩

theorem honest_row_is_accepted : umemoryTable.RowHolds honestRow true true := by decide

/-- NON-VACUITY, the FALSE pole of the GATES: a gap column with no limb witness is refused by the
recomposition gate. -/
theorem an_unwitnessed_gap_is_refused :
    ¬ umemoryTable.RowHolds
        (⟨fun c => if c = UM_DOMAIN then NULLIFIER_DOMAIN
                   else if c = UM_SERIAL then 1
                   else if c = UM_IS_REAL then 1
                   else if c = UM_IS_NULL then 1
                   else if c = UM_GAP then 1 else 0, fun _ => 0, fun _ => 0⟩)
        true true := by decide

/-- NON-VACUITY, the FALSE pole of the READ DISCIPLINE on the `Option`'s PRESENCE component — the
gate the flat memory has no counterpart for. A real read claiming an absent prior cell while
returning a present one is refused. -/
theorem a_read_inventing_presence_is_refused :
    ¬ umemoryTable.RowHolds
        (⟨fun c => if c = UM_DOMAIN then NULLIFIER_DOMAIN
                   else if c = UM_SERIAL then 1
                   else if c = UM_IS_REAL then 1
                   else if c = UM_IS_NULL then 1
                   else if c = UM_PRESENT then 1 else 0, fun _ => 0, fun _ => 0⟩)
        true true := by decide

/-! ### §4d — The residuals, stated as emission facts rather than prose. -/

/-- ⚠ **NO GATE READS `UM_KEY`**, on any row. The column that says WHICH cell of `Domain × κ` an op
touches is bound entirely by the `ir2_umem_addrs` closure lookup and the `ir2_umem_check` multiset —
both BUS legs, which `TableAir.Holds` is silent about. A gate-level mutation sweep is therefore
structurally blind to the key, and that is a fact about the mechanism, not a gap in the sweep. -/
theorem key_is_read_by_no_gate :
    (umemoryTable.gates.filter (fun g => TExpr.readsColIn umemoryTable.defs g.body UM_KEY)).length = 0 := by decide

/-- …the non-vacuity contrast: the DOMAIN, its sibling column in every bus tuple, IS read — by the
TWO nullifier-forcing gates. So "no gate reads the key" is a statement about the key, not about the
table being gate-free on its address columns.

ⓘ Two and not three: the insert-only TOOTH reads `is_null`, not the domain. The domain reaches the
tooth only through the forcing gates, which is the same two-gates-away structure §4c's second
refutation turns on. -/
theorem domain_is_read_by_two_gates :
    (umemoryTable.gates.filter (fun g => TExpr.readsColIn umemoryTable.defs g.body UM_DOMAIN)).length = 2 := by decide

/-- ⚠ **NO GATE RANGE-CHECKS `UM_PREV_SERIAL`.** The column is read by exactly ONE gate body — the
gap definition, which does not bound it — and by NO byte-bus query. This is the emission fact behind
§4c's first refutation. -/
theorem prev_serial_is_read_by_one_gate :
    (umemoryTable.gates.filter (fun g => TExpr.readsColIn umemoryTable.defs g.body UM_PREV_SERIAL)).length = 1 := by decide

theorem no_byte_query_reads_prev_serial :
    (umemoryTable.interactions.filter
      (fun i => i.bus == BUS_BYTE && i.tuple.any (fun e => TExpr.readsColIn umemoryTable.defs e UM_PREV_SERIAL))).length
      = 0 := by decide

/-- …and the contrast: eight byte queries — the gap's seven full limbs plus the DOMAIN nibble, which
is the whole of "domain is a nibble". -/
theorem the_byte_queries_are_the_gap_limbs_and_the_domain :
    (umemoryTable.interactions.filter (fun i => i.bus == BUS_BYTE)).length = 8 ∧
    (umemoryTable.interactions.filter
      (fun i => i.bus == BUS_BYTE && i.tuple.any (fun e => TExpr.readsColIn umemoryTable.defs e UM_DOMAIN))).length = 1 := by
  refine ⟨by decide, by decide⟩

/-! ## §5 — The wire pin. -/

/-- The wire string the Rust interpreter ingests. -/
def UMEMORY_JSON : String := emitTableAirJson umemoryTable

-- THE WIRE PIN. Byte length plus the structural `#guard`s in §3 (20 gates, 12 interactions in a
-- fixed per-bus/per-side split, width 23): any edit to a gate body, a tuple, a multiplicity or an
-- offset moves the length, and any edit to the SHAPE moves §3. (The checked-in artifact is these
-- bytes plus ONE trailing newline, which is the `by-name/` convention and which `JsonCursor` skips
-- as whitespace.)
#guard UMEMORY_JSON.length == 5782

/-- The emission is not empty and not a stub. -/
theorem umemoryTable_is_not_empty : umemoryTable.gates ≠ [] := by
  simp [umemoryTable, umemGates]

end Dregg2.Circuit.Emit.UMemoryTableEmit
