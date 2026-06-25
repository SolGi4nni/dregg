/-
# Dregg2.Exec.UniversalBridge — THE EXECUTOR-STATE BRIDGE: the executor IS a memory program.

The universal-map rotation's long pole (`docs/UNIVERSAL-MAP-ROTATION.md` §2.3/§3/§6,
`Substrate/VerbCompression.lean:87-89` — "the executor-state bridge ... rides THE ONE ROTATION").
This module is that bridge's Lean keystone, in three movements:

  1. **THE PROJECTION** (`uproj`): every field and side-table entry of the executor's
     `RecordKernelState` (+ the receipt chain of `RecChainedState`) lands at a
     `(Domain, key) ↦ Option ℤ` cell of `Crypto/UniversalMemory.lean`'s unified address space.
     TOTAL: all 17 kernel fields + the log have a home (the table is `UKey`); the `registers`
     domain is deliberately EMPTY (registers are per-proof VM transients, never persistent
     executor state — the one named exception).

  2. **THE TRACE EMITTERS** (`gwriteTrace`/`moveTrace`/`createTrace`): for each of the three
     compressed verbs (`VerbCompression.compressed_kernel_three` — create · gwrite · move) the
     Blum op list a committed step emits, computed from the PRE-state and the action alone
     (the executor can produce the witness without peeking at its own post-state). All
     emitted traces are `Disciplined` (the per-op memcheck discipline) — proved below.

  3. **THE AGREEMENT THEOREMS** (`gwrite_is_memory_program` / `move_is_memory_program` /
     `create_is_memory_program`): the projection of the executor's post-state EQUALS the fold
     (`MemoryChecking.step`) of the emitted trace over the projection of the pre-state — the
     commuting square the rotation needs, proved for ALL THREE VERBS against the live
     executable steps (`stateStepGuarded` — the caveat-gated field write the executor runs on
     every SetField; `recCexec` — the chained conserving move; `createCellStep` — the gated
     bundle birth). No create residue: the multi-address bundle is exactly its three-write
     trace (existence + balance field + receipt) — the arity separation
     (`create_birth_not_single_write`) shows up as trace LENGTH, never as a gap.

Plus the two umem-lane adapters that arise here:

  (a) **the cap-leaf value codec** (`cap_leaf_value_codec`): today's live cap leaf
      `hash[holder, target, rights, op]` (`EffectVmEmitCapRoot.siteCapEdgeLeaf`) versus the
      generic map leaf `hash[addr, value]` (`Heap.leafOf`) — encoding the cap tuple as the
      cell VALUE (`capCellValue = hash[target, rights, op]`) loses nothing: the generic leaf
      is injective in the full `(holder, target, rights, op)` tuple under the same named
      `Poseidon2SpongeCR` floor. A value-codec lemma, no new combinatorics
      (`docs/UNIVERSAL-MEMORY.md:138-144`).

  (b) **the index-domain MMR boundary derivation** (`index_boundary_mroot_derived` /
      `index_boundary_mroot_from_memcheck`): the receipt-index domain's boundary commitment
      is the MMR root (`Lightclient/MMR.lean`), not a sorted-map root; the
      `boundary_root_derived`/`boundary_root_from_memcheck` analogues hold — the log
      reconstructed from the (pinned) final index cells IS the committed log, so the MMR
      root derived at the boundary equals today's root, by canonicity, NO crypto
      (`docs/UNIVERSAL-MEMORY.md:115-121`).

Axiom hygiene: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} everywhere; crypto
enters ONLY as the named `Poseidon2SpongeCR` hypothesis. Non-vacuity: a concrete three-verb
run is `#guard`-folded address-by-address.
-/
import Dregg2.Exec.EffectsState
import Dregg2.Exec.EffectsSupply
import Dregg2.Exec.Program
import Dregg2.Crypto.UniversalMemory
import Dregg2.Circuit.MapMerkleRoot
import Dregg2.Lightclient.MMR
import Dregg2.Tactics

namespace Dregg2.Exec.UniversalBridge

open Dregg2.Exec
open Dregg2.Exec.EffectsState (stateStep stateStepGuarded stateStepGuarded_eq writeField
  setField cellLive stateAuthB)
open Dregg2.Exec.EffectsSupply (createCellStep createCellInto createTurn)
open Dregg2.Crypto.MemoryChecking (Op Kind step step_write step_read step_other Disciplined
  DisciplinedFrom MemCheck Consistent)
open Dregg2.Crypto.UniversalMemory (Domain UAddr boundaryCells)
open Dregg2.Substrate
open Dregg2.Authority (Cap)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.MapMerkleRoot (opensToMerkle mapRoot)
open Dregg2.Lightclient

/-! ## §1 — THE PROJECTION TABLE: every executor-state cell gets a universal address.

`UKey` is the structured in-domain key — one constructor per kernel field / side-table plane.
The deployed realization is `addr = hash[domain_tag, collection_id, key]`; the constructor IS
the abstract `(collection_id, key)` content of that hash (injective under the same CR floor,
here literal by `DecidableEq`). The domain assignment (`UKey.domain`) is the projection table:

  | RecordKernelState field        | constructor      | domain     |
  |--------------------------------|------------------|------------|
  | `accounts` (existence)         | `.exist`         | heap       |
  | `cell` (named record fields)   | `.field`         | heap       |
  | `bal` (per-asset ledger)       | `.balA`          | heap       |
  | `heaps` (per-cell user map)    | `.hcell`         | heap       |
  | `lifecycle`                    | `.lifecycle`     | heap       |
  | `deathCert`                    | `.deathCert`     | heap       |
  | `caps` (slot table)            | `.cap`           | caps       |
  | `delegate` (parent pointer)    | `.delegate`      | caps       |
  | `delegations` (c-list snapshot)| `.delegSnap`     | caps       |
  | `delegationEpoch`              | `.delegEpoch`    | caps       |
  | `delegationEpochAt`            | `.delegStamp`    | caps       |
  | `slotCaveats`                  | `.caveat`        | caps       |
  | `factories`                    | `.factory`       | caps       |
  | `nullifiers` (note spends)     | `.nullifier`     | nullifiers |
  | `revoked` (cred nullifiers)    | `.revoked`       | nullifiers |
  | `commitments` (note creates)   | `.commitment`    | nullifiers |
  | `RecChainedState.log`          | `.receipt`       | index      |

  `registers`: EMPTY by design (per-proof VM transients, not persistent state). The three
  insert-only sets share the `nullifiers` domain (distinct collections = distinct
  constructors), matching that domain's insert-only discipline (`InsertOnlyAt`). -/
inductive UKey where
  /-- `accounts` membership: the cell-existence bit. -/
  | exist (c : CellId)
  /-- `cell c` named record field `f` (the content-addressed record plane). -/
  | field (c : CellId) (f : FieldName)
  /-- `bal c a`: the per-asset signed ledger cell. -/
  | balA (c : CellId) (a : AssetId)
  /-- `heaps c` key `k`: the per-cell openable user map. -/
  | hcell (c : CellId) (k : ℤ)
  /-- `lifecycle c`: the lifecycle discriminant. -/
  | lifecycle (c : CellId)
  /-- `deathCert c`: the death-certificate binding. -/
  | deathCert (c : CellId)
  /-- `caps holder` slot `i`: the capability slot table. -/
  | cap (holder : CellId) (i : Nat)
  /-- `delegate c`: the delegation parent pointer (`none` = no parent = absent cell). -/
  | delegate (c : CellId)
  /-- `delegations c` slot `i`: the delegation c-list snapshot. -/
  | delegSnap (c : CellId) (i : Nat)
  /-- `delegationEpoch c`: the parent-side revocation counter. -/
  | delegEpoch (c : CellId)
  /-- `delegationEpochAt c`: the child-side snapshot stamp. -/
  | delegStamp (c : CellId)
  /-- `slotCaveats c` slot `i`: the factory-installed caveat list. -/
  | caveat (c : CellId) (i : Nat)
  /-- `factories` entry at VK `vk`: the published factory registry. -/
  | factory (vk : Nat)
  /-- `nullifiers` membership: the spent-note set (insert-only). -/
  | nullifier (n : Nat)
  /-- `revoked` membership: the credential-revocation registry (insert-only). -/
  | revoked (n : Nat)
  /-- `commitments` membership: the note-commitment set (insert-only). -/
  | commitment (n : Nat)
  /-- `RecChainedState.log` chronological position `i` (the receipt index; append-only). -/
  | receipt (i : Nat)
  deriving DecidableEq, Repr

/-- The domain assignment — the projection table's right column. -/
def UKey.domain : UKey → Domain
  | .exist _ | .field _ _ | .balA _ _ | .hcell _ _ | .lifecycle _ | .deathCert _ => .heap
  | .cap _ _ | .delegate _ | .delegSnap _ _ | .delegEpoch _ | .delegStamp _
  | .caveat _ _ | .factory _ => .caps
  | .nullifier _ | .revoked _ | .commitment _ => .nullifiers
  | .receipt _ => .index

/-- A key's canonical universal address: its domain paired with itself. -/
def uaddr (k : UKey) : UAddr UKey := (k.domain, k)

/-- **The value codecs** — how each non-scalar plane's values land in `ℤ`. Plain functions
here (the agreement theorems are equalities of projections, codec-agnostic); INJECTIVITY is
the boundary/anti-ghost requirement and is discharged separately per plane (the cap plane:
`cap_leaf_value_codec` below — the sponge encoding loses nothing under the CR floor). -/
structure UCodec where
  /-- record-field values (`Value`). -/
  val : Value → ℤ
  /-- capability slots / delegation snapshots (`Cap`). -/
  cap : Cap → ℤ
  /-- slot caveats (`SlotCaveat`). -/
  caveat : SlotCaveat → ℤ
  /-- factory entries (`FactoryEntry`). -/
  factory : FactoryEntry → ℤ
  /-- receipt rows (`Turn`). -/
  receipt : Turn → ℤ

/-- **THE KERNEL PROJECTION** — every `RecordKernelState` field as universal-map cells.
`Option ℤ` cells: `none` = absent, exactly the circuit's `(present, value)` encoding
(`DescriptorIR2.UMemOp`). The record-field plane is gated on `accounts` membership (a
non-account cell's record is not state — this is what makes `create` a finite trace). -/
def projKernel (C : UCodec) (k : RecordKernelState) : UKey → Option ℤ
  | .exist c      => if c ∈ k.accounts then some 1 else none
  | .field c f    => if c ∈ k.accounts then ((k.cell c).field f).map C.val else none
  | .balA c a     => some (k.bal c a)
  | .hcell c key  => Heap.get (k.heaps c) key
  | .lifecycle c  => some (k.lifecycle c)
  | .deathCert c  => some (k.deathCert c)
  | .cap h i      => ((k.caps h)[i]?).map C.cap
  | .delegate c   => (k.delegate c).map (fun p => (p : ℤ))
  | .delegSnap c i => ((k.delegations c)[i]?).map C.cap
  | .delegEpoch c => some (k.delegationEpoch c)
  | .delegStamp c => some (k.delegationEpochAt c)
  | .caveat c i   => ((k.slotCaveats c)[i]?).map C.caveat
  | .factory vk   => (List.lookup vk k.factories).map C.factory
  | .nullifier n  => if n ∈ k.nullifiers then some 1 else none
  | .revoked n    => if n ∈ k.revoked then some 1 else none
  | .commitment n => if n ∈ k.commitments then some 1 else none
  | .receipt _    => none  -- the receipt log lives on the CHAINED state (`projKey`)

/-- The chained-state key projection: the kernel planes + the receipt log (chronological:
position `i` counts from the OLDEST row, so the executor's prepend is an APPEND here). -/
def projKey (C : UCodec) (s : RecChainedState) : UKey → Option ℤ
  | .receipt i => (s.log.reverse[i]?).map C.receipt
  | k          => projKernel C s.kernel k

/-- **THE PROJECTION** — `RecChainedState` as ONE universal memory: a total function on the
unified `Domain × UKey` address space. Off-domain addresses (a key paired with the wrong
domain tag) are `none` — the tag is part of the address, never aliased
(`UniversalMemory` non-vacuity polarity 2). -/
def uproj (C : UCodec) (s : RecChainedState) : UAddr UKey → Option ℤ :=
  fun a => if a.1 = a.2.domain then projKey C s a.2 else none

/-- The op alphabet of the bridge: universal-memory ops over the structured address space,
`Option ℤ`-valued cells. -/
abbrev UOp := Op (UAddr UKey) (Option ℤ)

/-- A write op at a key's canonical address. -/
def writeOp (k : UKey) (v prev : Option ℤ) : UOp :=
  ⟨.write, uaddr k, v, prev, 0⟩

/-! ## §2 — THE TRACE EMITTERS: the Blum op list of each committed verb.

Computed from the PRE-state and the action alone. `prevVal` carries the pre-state cell (the
boundary claim the memcheck read-set consumes); `prevSerial 0` = the init boundary (each
address is touched once per verb — multi-touch serials are the Rust emitter's positional
bookkeeping, semantically irrelevant to the fold). -/

/-- The trace of a committed `stateStepGuarded` (the caveat-gated field write — THE gwrite
verb): one record-field write + the receipt append. -/
def gwriteTrace (C : UCodec) (s : RecChainedState) (f : FieldName) (actor target : CellId)
    (n : Int) : List UOp :=
  [ writeOp (.field target f) (some (C.val (.int n)))
      (((s.kernel.cell target).field f).map C.val),
    writeOp (.receipt s.log.length)
      (some (C.receipt { actor := actor, src := target, dst := target, amt := 0 })) none ]

/-- The trace of a committed `recCexec` (the chained conserving transfer — THE move verb):
the paired debit/credit balance-field writes + the receipt append. The Σδ = 0 correlation
lives in the PAIR of values (both computed from the pre-state), exactly the in-row
paired-write constraint the rotation keeps OUT of the multiset
(`VerbCompression.gwrite_conservation_trivializes`). -/
def moveTrace (C : UCodec) (s : RecChainedState) (t : Turn) : List UOp :=
  [ writeOp (.field t.src balanceField)
      (some (C.val (.int (balOf (s.kernel.cell t.src) - t.amt))))
      (((s.kernel.cell t.src).field balanceField).map C.val),
    writeOp (.field t.dst balanceField)
      (some (C.val (.int (balOf (s.kernel.cell t.dst) + t.amt))))
      (((s.kernel.cell t.dst).field balanceField).map C.val),
    writeOp (.receipt s.log.length) (some (C.receipt t)) none ]

/-- The trace of a committed `recCexecAsset` (the chained conserving PER-ASSET move — THE move
verb on the `bal` ledger plane, which is the arm `execFullA` ACTUALLY routes `balanceA` to):
the paired debit/credit writes on the `.balA` plane of asset `a` + the receipt append. This is
the per-asset analogue of `moveTrace`: where `moveTrace` writes the named `balance` FIELD
(`recCexec` / `recKExec`), this writes the genuine multi-asset `bal c a` ledger cell
(`recCexecAsset` / `recKExecAsset` / `recTransferBal`), the column the deployed executor moves.
The `.balA` plane carries `prevVal = some (k.bal · a)` truthfully (the ledger is total — every
cell/asset has a value, never `none`), so both writes claim the pre-state ledger value. -/
def moveAssetTrace (C : UCodec) (s : RecChainedState) (t : Turn) (a : AssetId) : List UOp :=
  [ writeOp (.balA t.src a) (some (s.kernel.bal t.src a - t.amt)) (some (s.kernel.bal t.src a)),
    writeOp (.balA t.dst a) (some (s.kernel.bal t.dst a + t.amt)) (some (s.kernel.bal t.dst a)),
    writeOp (.receipt s.log.length) (some (C.receipt t)) none ]

/-- The trace of a committed `createCellStep` (THE create verb): the atomic multi-address
bundle birth — existence bit + initial balance field + receipt. The arity separation
(`VerbCompression.create_birth_not_single_write`) is the trace LENGTH (3 writes), not a gap.
Both state writes claim `prevVal = none`: the gate's freshness conjunct
(`newCell ∉ accounts`) IS the absence claim. -/
def createTrace (C : UCodec) (s : RecChainedState) (actor newCell : CellId) (bal : ℤ) :
    List UOp :=
  [ writeOp (.exist newCell) (some 1) none,
    writeOp (.field newCell balanceField) (some (C.val (.int bal))) none,
    writeOp (.receipt s.log.length) (some (C.receipt (createTurn actor newCell bal))) none ]

/-- Every emitted trace is per-op DISCIPLINED (all writes; `prevSerial 0 < own serial`). -/
theorem gwriteTrace_disciplined (C : UCodec) (s : RecChainedState) (f : FieldName)
    (actor target : CellId) (n : Int) : Disciplined (gwriteTrace C s f actor target n) :=
  ⟨⟨Nat.zero_lt_succ 0, fun h => nomatch h⟩, ⟨Nat.zero_lt_succ 1, fun h => nomatch h⟩, trivial⟩

theorem moveTrace_disciplined (C : UCodec) (s : RecChainedState) (t : Turn) :
    Disciplined (moveTrace C s t) :=
  ⟨⟨Nat.zero_lt_succ 0, fun h => nomatch h⟩, ⟨Nat.zero_lt_succ 1, fun h => nomatch h⟩,
   ⟨Nat.zero_lt_succ 2, fun h => nomatch h⟩, trivial⟩

theorem moveAssetTrace_disciplined (C : UCodec) (s : RecChainedState) (t : Turn) (a : AssetId) :
    Disciplined (moveAssetTrace C s t a) :=
  ⟨⟨Nat.zero_lt_succ 0, fun h => nomatch h⟩, ⟨Nat.zero_lt_succ 1, fun h => nomatch h⟩,
   ⟨Nat.zero_lt_succ 2, fun h => nomatch h⟩, trivial⟩

theorem createTrace_disciplined (C : UCodec) (s : RecChainedState) (actor newCell : CellId)
    (bal : ℤ) : Disciplined (createTrace C s actor newCell bal) :=
  ⟨⟨Nat.zero_lt_succ 0, fun h => nomatch h⟩, ⟨Nat.zero_lt_succ 1, fun h => nomatch h⟩,
   ⟨Nat.zero_lt_succ 2, fun h => nomatch h⟩, trivial⟩

/-! ## §3 — frame lemmas: the field planes touch ONLY their slot; small step calculators. -/

/-- `setField` write/read: the written slot reads back the written value. -/
theorem field_setField_same (f : FieldName) (cell : Value) (w : Value) :
    (setField f cell w).field f = some w := by
  have hlist : ∀ fs : List (FieldName × Value),
      (Value.record (setField.setFieldList f fs w)).field f = some w := by
    intro fs
    induction fs with
    | nil => simp [setField.setFieldList, Value.field]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setField.setFieldList]
        by_cases hk : (k == f) = true
        · rw [if_pos hk]; simp [Value.field]
        · rw [if_neg hk]
          simp only [Value.field] at ih ⊢
          rw [List.find?_cons_of_neg (by simpa using hk)]
          exact ih
  cases cell with
  | record fs => simpa [setField] using hlist fs
  | int _ => simp [setField, Value.field]
  | dig _ => simp [setField, Value.field]
  | sym _ => simp [setField, Value.field]

/-- `setField` frame: every OTHER slot is untouched. -/
theorem field_setField_other {f g : FieldName} (hg : g ≠ f) (cell : Value) (w : Value) :
    (setField f cell w).field g = cell.field g := by
  have hfg : (f == g) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun h => hg h.symm
  have hlist : ∀ fs : List (FieldName × Value),
      (Value.record (setField.setFieldList f fs w)).field g
        = (Value.record fs).field g := by
    intro fs
    induction fs with
    | nil => simp [setField.setFieldList, Value.field, List.find?, hfg]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setField.setFieldList]
        by_cases hk : (k == f) = true
        · rw [if_pos hk]
          have hkf : k = f := by simpa using hk
          subst hkf
          simp [Value.field, List.find?, hfg]
        · rw [if_neg hk]
          simp only [Value.field] at ih ⊢
          by_cases hkg : (k == g) = true
          · simp [List.find?, hkg]
          · rw [List.find?_cons_of_neg (by simpa using hkg),
                List.find?_cons_of_neg (by simpa using hkg)]
            exact ih
  cases cell with
  | record fs => simpa [setField] using hlist fs
  | int _ => simp [setField, Value.field, List.find?, hfg]
  | dig _ => simp [setField, Value.field, List.find?, hfg]
  | sym _ => simp [setField, Value.field, List.find?, hfg]

/-- `setBalance` IS `setField` at the `balance` slot (the two write shapes coincide). -/
theorem setBalance_eq_setField (cell : Value) (v : Int) :
    setBalance cell v = setField balanceField cell (.int v) := by
  have hlist : ∀ fs : List (FieldName × Value),
      setBalance.setBalanceList fs v = setField.setFieldList balanceField fs (.int v) := by
    intro fs
    induction fs with
    | nil => rfl
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setBalance.setBalanceList, setField.setFieldList]
        by_cases hk : (k == balanceField) = true
        · rw [if_pos hk, if_pos hk]
        · rw [if_neg hk, if_neg hk, ih]
  cases cell with
  | record fs => simp [setBalance, setField, hlist fs]
  | int _ => rfl
  | dig _ => rfl
  | sym _ => rfl

/-- The receipt-plane append lemma: prepending a row to the log appends one cell at
chronological position `log.length`, leaving every other position untouched. -/
theorem receipt_append (log : List Turn) (row : Turn) (i : Nat) :
    (row :: log).reverse[i]? =
      if i = log.length then some row else log.reverse[i]? := by
  rw [List.reverse_cons]
  by_cases hi : i = log.length
  · subst hi
    have hlen : log.reverse.length = log.length := List.length_reverse ..
    rw [if_pos rfl, ← hlen, List.getElem?_concat_length]
  · rw [if_neg hi]
    rcases Nat.lt_or_ge i log.length with hlt | hge
    · exact List.getElem?_append_left (by simpa using hlt)
    · have hgt : log.length < i := lt_of_le_of_ne hge (Ne.symm hi)
      rw [List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by simp; omega)]

/-- An address whose key differs misses a `writeOp` (the structured key IS the address). -/
theorem writeOp_addr_ne {d : Domain} {key k : UKey} {v p : Option ℤ} (h : key ≠ k) :
    (d, key) ≠ (writeOp k v p).addr :=
  fun hc => h (congrArg Prod.snd hc)

/-- An address with a mismatched domain tag misses every `writeOp` (canonical addresses
carry their key's own tag). -/
theorem writeOp_addr_ne_tag {d : Domain} {key k : UKey} {v p : Option ℤ}
    (hd : d ≠ key.domain) : (d, key) ≠ (writeOp k v p).addr := by
  intro hc
  have h2 : key = k := congrArg Prod.snd hc
  have h1 : d = UKey.domain k := congrArg Prod.fst hc
  exact hd (h2 ▸ h1)

section StepCalc
variable {Addr : Type} {Val : Type} [DecidableEq Addr]
  {m : Addr → Val} {op1 op2 op3 : Op Addr Val} {a : Addr}

/-- 2-op fold, address untouched. -/
theorem step2_frame (h1 : a ≠ op1.addr) (h2 : a ≠ op2.addr) :
    step (step m op1) op2 a = m a := by rw [step_other h2, step_other h1]

/-- 3-op fold, address untouched. -/
theorem step3_frame (h1 : a ≠ op1.addr) (h2 : a ≠ op2.addr) (h3 : a ≠ op3.addr) :
    step (step (step m op1) op2) op3 a = m a := by
  rw [step_other h3, step_other h2, step_other h1]

end StepCalc

section StepCalcW
variable {m : UAddr UKey → Option ℤ} {k1 k2 k3 : UKey} {v1 p1 v2 p2 v3 p3 : Option ℤ}

/-- 2-`writeOp` fold at op 1's canonical address (missed by op 2): the installed value. -/
theorem step2w_hit1 (hne : k1 ≠ k2) :
    step (step m (writeOp k1 v1 p1)) (writeOp k2 v2 p2) (k1.domain, k1) = v1 := by
  rw [step_other (writeOp_addr_ne hne)]
  exact step_write rfl m

/-- 2-`writeOp` fold at op 2's canonical address: the installed value (op 2 is last). -/
theorem step2w_hit2 :
    step (step m (writeOp k1 v1 p1)) (writeOp k2 v2 p2) (k2.domain, k2) = v2 :=
  step_write rfl _

/-- 3-`writeOp` fold at op 1's canonical address (missed by ops 2/3). -/
theorem step3w_hit1 (hne2 : k1 ≠ k2) (hne3 : k1 ≠ k3) :
    step (step (step m (writeOp k1 v1 p1)) (writeOp k2 v2 p2)) (writeOp k3 v3 p3)
      (k1.domain, k1) = v1 := by
  rw [step_other (writeOp_addr_ne hne3), step_other (writeOp_addr_ne hne2)]
  exact step_write rfl m

/-- 3-`writeOp` fold at op 2's canonical address (missed by op 3). -/
theorem step3w_hit2 (hne3 : k2 ≠ k3) :
    step (step (step m (writeOp k1 v1 p1)) (writeOp k2 v2 p2)) (writeOp k3 v3 p3)
      (k2.domain, k2) = v2 := by
  rw [step_other (writeOp_addr_ne hne3)]
  exact step_write rfl _

/-- 3-`writeOp` fold at op 3's canonical address. -/
theorem step3w_hit3 :
    step (step (step m (writeOp k1 v1 p1)) (writeOp k2 v2 p2)) (writeOp k3 v3 p3)
      (k3.domain, k3) = v3 :=
  step_write rfl _

end StepCalcW

/-! ## §4 — THE AGREEMENT THEOREMS: post-projection = trace-fold over pre-projection. -/

/-- `stateStep`'s full gate factoring (membership + liveness included — the published
`stateStep_factors` drops the membership conjunct this bridge needs). -/
theorem stateStep_factors_full {s s' : RecChainedState} {f : FieldName}
    {actor target : CellId} {v : Value}
    (h : stateStep s f actor target v = some s') :
    stateAuthB s.kernel.caps actor target = true ∧ target ∈ s.kernel.accounts ∧
      cellLive s.kernel target = true ∧
      s' = { kernel := writeField s.kernel f target v,
             log := { actor := actor, src := target, dst := target, amt := 0 } :: s.log } := by
  unfold stateStep at h
  by_cases hg : stateAuthB s.kernel.caps actor target = true ∧ target ∈ s.kernel.accounts
      ∧ cellLive s.kernel target = true
  · rw [if_pos hg, Option.some.injEq] at h
    exact ⟨hg.1, hg.2.1, hg.2.2, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- `recKExec`'s full gate factoring. -/
theorem recKExec_factors {k k' : RecordKernelState} {t : Turn}
    (h : recKExec k t = some k') :
    (authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ balOf (k.cell t.src)
        ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts) ∧
      k' = { k with cell := recTransfer k.cell t.src t.dst t.amt } := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ balOf (k.cell t.src)
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
  · rw [if_pos hg, Option.some.injEq] at h
    exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`gwrite_is_memory_program`** — THE BRIDGE KEYSTONE for the gwrite verb. A committed
caveat-gated field write (`stateStepGuarded`, the live executor's SetField arm) is EXACTLY
its emitted two-op memory program: the projection of the post-state is the fold of
`gwriteTrace` over the projection of the pre-state. -/
theorem gwrite_is_memory_program (C : UCodec) {s s' : RecChainedState} {f : FieldName}
    {actor target : CellId} {n : Int}
    (h : stateStepGuarded s f actor target n = some s') :
    uproj C s' = (gwriteTrace C s f actor target n).foldl step (uproj C s) := by
  obtain ⟨-, hmem, -, hpost⟩ := stateStep_factors_full (stateStepGuarded_eq h)
  subst hpost
  funext a
  obtain ⟨d, key⟩ := a
  simp only [gwriteTrace, List.foldl_cons, List.foldl_nil]
  by_cases hd : d = key.domain
  case neg =>
    rw [step2_frame (writeOp_addr_ne_tag hd) (writeOp_addr_ne_tag hd)]
    show uproj _ _ (d, key) = uproj _ _ (d, key)
    show (if d = key.domain then _ else none) = (if d = key.domain then _ else none)
    rw [if_neg hd, if_neg hd]
  case pos =>
  subst hd
  cases key with
  | field c g =>
    by_cases hcg : c = target ∧ g = f
    · obtain ⟨rfl, rfl⟩ := hcg
      rw [step2w_hit1 (by simp)]
      show projKey C _ (.field c g) = some (C.val (.int n))
      show (if c ∈ (writeField s.kernel g c (Value.int n)).accounts
        then (((writeField s.kernel g c (Value.int n)).cell c).field g).map C.val
        else none) = some (C.val (.int n))
      have hcell : (writeField s.kernel g c (Value.int n)).cell c
          = setField g (s.kernel.cell c) (.int n) := by
        show (if c = c then _ else _) = _
        rw [if_pos rfl]
      have haccs : (writeField s.kernel g c (Value.int n)).accounts = s.kernel.accounts := rfl
      rw [haccs, if_pos hmem, hcell, field_setField_same]
      rfl
    · have hne : UKey.field c g ≠ UKey.field target f := by
        intro hcon
        injection hcon with h1 h2
        exact hcg ⟨h1, h2⟩
      rw [step2_frame (writeOp_addr_ne hne) (writeOp_addr_ne (by simp))]
      show projKey C _ (.field c g) = projKey C s (.field c g)
      show (if c ∈ (writeField s.kernel f target (Value.int n)).accounts
          then (((writeField s.kernel f target (Value.int n)).cell c).field g).map C.val
          else none)
        = (if c ∈ s.kernel.accounts then ((s.kernel.cell c).field g).map C.val else none)
      have haccs : (writeField s.kernel f target (Value.int n)).accounts
          = s.kernel.accounts := rfl
      rw [haccs]
      by_cases hc : c = target
      · subst hc
        have hgf : g ≠ f := fun hgf => hcg ⟨rfl, hgf⟩
        have hcell : (writeField s.kernel f c (Value.int n)).cell c
            = setField f (s.kernel.cell c) (.int n) := by
          show (if c = c then _ else _) = _
          rw [if_pos rfl]
        rw [hcell, field_setField_other hgf]
      · have hcell : (writeField s.kernel f target (Value.int n)).cell c = s.kernel.cell c := by
          show (if c = target then _ else _) = _
          rw [if_neg hc]
        rw [hcell]
  | receipt i =>
    by_cases hi : i = s.log.length
    · subst hi
      rw [step2w_hit2]
      show ((({ actor := actor, src := target, dst := target, amt := 0 } : Turn)
          :: s.log).reverse[s.log.length]?).map C.receipt = _
      rw [receipt_append, if_pos rfl]
      rfl
    · have hne : UKey.receipt i ≠ UKey.receipt s.log.length := by
        intro hcon; injection hcon with h1; exact hi h1
      rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne hne)]
      show ((({ actor := actor, src := target, dst := target, amt := 0 } : Turn)
          :: s.log).reverse[i]?).map C.receipt = (s.log.reverse[i]?).map C.receipt
      rw [receipt_append, if_neg hi]
  | exist c =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | balA c aa =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | hcell c kk =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | lifecycle c =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | deathCert c =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | cap hh i =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | delegate c =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | delegSnap c i =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | delegEpoch c =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | delegStamp c =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | caveat c i =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | factory vk =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | nullifier nn =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | revoked nn =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl
  | commitment nn =>
    rw [step2_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))]; rfl

/-- **`move_is_memory_program`** — THE BRIDGE KEYSTONE for the move verb. A committed chained
transfer (`recCexec`, the conserving two-cell move) is EXACTLY its emitted three-op memory
program (debit write + credit write + receipt append). -/
theorem move_is_memory_program (C : UCodec) {s s' : RecChainedState} {t : Turn}
    (h : recCexec s t = some s') :
    uproj C s' = (moveTrace C s t).foldl step (uproj C s) := by
  -- factor the chained step
  have hfac : ∃ k', recKExec s.kernel t = some k' ∧ s' = { kernel := k', log := t :: s.log } := by
    unfold recCexec at h
    cases hk : recKExec s.kernel t with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h
        simp only [Option.some.injEq] at h
        exact ⟨k', rfl, h.symm⟩
  obtain ⟨k', hk, hpost⟩ := hfac
  obtain ⟨⟨-, -, -, hne, hsrc, hdst⟩, hk'⟩ := recKExec_factors hk
  subst hpost
  subst hk'
  funext a
  obtain ⟨d, key⟩ := a
  simp only [moveTrace, List.foldl_cons, List.foldl_nil]
  by_cases hd : d = key.domain
  case neg =>
    rw [step3_frame (writeOp_addr_ne_tag hd) (writeOp_addr_ne_tag hd)
      (writeOp_addr_ne_tag hd)]
    show (if d = key.domain then _ else none) = (if d = key.domain then _ else none)
    rw [if_neg hd, if_neg hd]
  case pos =>
  subst hd
  -- the post-state record plane at a single cell
  have hcell : ∀ c, recTransfer s.kernel.cell t.src t.dst t.amt c
      = if c = t.src then setBalance (s.kernel.cell c) (balOf (s.kernel.cell c) - t.amt)
        else if c = t.dst then setBalance (s.kernel.cell c) (balOf (s.kernel.cell c) + t.amt)
        else s.kernel.cell c := fun c => rfl
  cases key with
  | field c g =>
    by_cases hcsrc : c = t.src ∧ g = balanceField
    · obtain ⟨rfl, rfl⟩ := hcsrc
      -- (`c` is now `t.src`, `g` is now `balanceField`)
      have hne2 : UKey.field t.src balanceField ≠ UKey.field t.dst balanceField := by
        intro hcon; injection hcon with h1 _; exact hne h1
      rw [step3w_hit1 hne2 (by simp)]
      show (if t.src ∈ s.kernel.accounts
          then ((recTransfer s.kernel.cell t.src t.dst t.amt t.src).field balanceField).map
            C.val
          else none) = some (C.val (.int (balOf (s.kernel.cell t.src) - t.amt)))
      rw [if_pos hsrc, hcell t.src, if_pos rfl, setBalance_eq_setField, field_setField_same]
      rfl
    · by_cases hcdst : c = t.dst ∧ g = balanceField
      · obtain ⟨rfl, rfl⟩ := hcdst
        rw [step3w_hit2 (by simp)]
        show (if t.dst ∈ s.kernel.accounts
            then ((recTransfer s.kernel.cell t.src t.dst t.amt t.dst).field balanceField).map
              C.val
            else none) = some (C.val (.int (balOf (s.kernel.cell t.dst) + t.amt)))
        rw [if_pos hdst, hcell t.dst, if_neg (Ne.symm hne),
          if_pos rfl, setBalance_eq_setField, field_setField_same]
        rfl
      · have hne1 : UKey.field c g ≠ UKey.field t.src balanceField := by
          intro hcon; injection hcon with h1 h2; exact hcsrc ⟨h1, h2⟩
        have hne2 : UKey.field c g ≠ UKey.field t.dst balanceField := by
          intro hcon; injection hcon with h1 h2; exact hcdst ⟨h1, h2⟩
        rw [step3_frame (writeOp_addr_ne hne1) (writeOp_addr_ne hne2)
          (writeOp_addr_ne (by simp))]
        show (if c ∈ s.kernel.accounts
            then ((recTransfer s.kernel.cell t.src t.dst t.amt c).field g).map C.val
            else none)
          = (if c ∈ s.kernel.accounts then ((s.kernel.cell c).field g).map C.val else none)
        rw [hcell c]
        by_cases hc1 : c = t.src
        · subst hc1
          have hgb : g ≠ balanceField := fun hgb => hcsrc ⟨rfl, hgb⟩
          rw [if_pos rfl, setBalance_eq_setField, field_setField_other hgb]
        · rw [if_neg hc1]
          by_cases hc2 : c = t.dst
          · subst hc2
            have hgb : g ≠ balanceField := fun hgb => hcdst ⟨rfl, hgb⟩
            rw [if_pos rfl, setBalance_eq_setField, field_setField_other hgb]
          · rw [if_neg hc2]
  | receipt i =>
    by_cases hi : i = s.log.length
    · subst hi
      rw [step3w_hit3]
      show ((t :: s.log).reverse[s.log.length]?).map C.receipt = _
      rw [receipt_append, if_pos rfl]
      rfl
    · have hne3 : UKey.receipt i ≠ UKey.receipt s.log.length := by
        intro hcon; injection hcon with h1; exact hi h1
      rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
        (writeOp_addr_ne hne3)]
      show ((t :: s.log).reverse[i]?).map C.receipt = (s.log.reverse[i]?).map C.receipt
      rw [receipt_append, if_neg hi]
  | exist c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | balA c aa =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | hcell c kk =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | lifecycle c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | deathCert c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | cap hh i =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegate c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegSnap c i =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegEpoch c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegStamp c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | caveat c i =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | factory vk =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | nullifier nn =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | revoked nn =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | commitment nn =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl

/-- **`create_is_memory_program`** — THE BRIDGE KEYSTONE for the create verb. A committed
bundle birth (`createCellStep`) is EXACTLY its emitted three-op memory program (existence
bit + initial balance field + receipt append) — the freshness gate makes the pre-state cells
`none`, so the bundle is finite and the trace claims `prevVal = none` truthfully. -/
theorem create_is_memory_program (C : UCodec) {s s' : RecChainedState}
    {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    uproj C s' = (createTrace C s actor newCell bal).foldl step (uproj C s) := by
  obtain ⟨-, hfresh, -, hpost⟩ := EffectsSupply.createCellStep_factors h
  subst hpost
  funext a
  obtain ⟨d, key⟩ := a
  simp only [createTrace, List.foldl_cons, List.foldl_nil]
  by_cases hd : d = key.domain
  case neg =>
    rw [step3_frame (writeOp_addr_ne_tag hd) (writeOp_addr_ne_tag hd)
      (writeOp_addr_ne_tag hd)]
    show (if d = key.domain then _ else none) = (if d = key.domain then _ else none)
    rw [if_neg hd, if_neg hd]
  case pos =>
  subst hd
  have hcell : ∀ c, (createCellInto s.kernel newCell bal).cell c
      = if c = newCell then setBalance (.record []) bal else s.kernel.cell c := fun c => rfl
  have haccs : (createCellInto s.kernel newCell bal).accounts
      = insert newCell s.kernel.accounts := rfl
  cases key with
  | exist c =>
    by_cases hc : c = newCell
    · subst hc
      have hne2 : UKey.exist c ≠ UKey.field c balanceField := by simp
      rw [step3w_hit1 hne2 (by simp)]
      show (if c ∈ (createCellInto s.kernel c bal).accounts then some 1 else none)
        = some (1 : ℤ)
      rw [haccs, if_pos (Finset.mem_insert_self ..)]
    · have hne1 : UKey.exist c ≠ UKey.exist newCell := by
        intro hcon; injection hcon with h1; exact hc h1
      rw [step3_frame (writeOp_addr_ne hne1) (writeOp_addr_ne (by simp))
        (writeOp_addr_ne (by simp))]
      show (if c ∈ (createCellInto s.kernel newCell bal).accounts then some 1 else none)
        = (if c ∈ s.kernel.accounts then some (1 : ℤ) else none)
      rw [haccs]
      by_cases hmem : c ∈ s.kernel.accounts
      · rw [if_pos (Finset.mem_insert_of_mem hmem), if_pos hmem]
      · rw [if_neg (fun hcon => hmem ((Finset.mem_insert.mp hcon).resolve_left hc)),
          if_neg hmem]
  | field c g =>
    by_cases hcg : c = newCell ∧ g = balanceField
    · obtain ⟨rfl, rfl⟩ := hcg
      -- (`newCell` is now `c`, `g` is now `balanceField`)
      rw [step3w_hit2 (by simp)]
      show (if c ∈ (createCellInto s.kernel c bal).accounts
          then (((createCellInto s.kernel c bal).cell c).field balanceField).map C.val
          else none) = some (C.val (.int bal))
      rw [haccs, if_pos (Finset.mem_insert_self ..), hcell c, if_pos rfl,
        setBalance_eq_setField, field_setField_same]
      rfl
    · have hne2 : UKey.field c g ≠ UKey.field newCell balanceField := by
        intro hcon; injection hcon with h1 h2; exact hcg ⟨h1, h2⟩
      rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne hne2)
        (writeOp_addr_ne (by simp))]
      show (if c ∈ (createCellInto s.kernel newCell bal).accounts
          then (((createCellInto s.kernel newCell bal).cell c).field g).map C.val
          else none)
        = (if c ∈ s.kernel.accounts then ((s.kernel.cell c).field g).map C.val else none)
      rw [haccs, hcell c]
      by_cases hc : c = newCell
      · subst hc
        have hgb : g ≠ balanceField := fun hgb => hcg ⟨rfl, hgb⟩
        rw [if_pos (Finset.mem_insert_self ..), if_pos rfl, if_neg hfresh,
          setBalance_eq_setField, field_setField_other hgb]
        show ((Value.record []).field g).map C.val = none
        rfl
      · rw [if_neg hc]
        by_cases hmem : c ∈ s.kernel.accounts
        · rw [if_pos (Finset.mem_insert_of_mem hmem), if_pos hmem]
        · rw [if_neg (fun hcon => hmem ((Finset.mem_insert.mp hcon).resolve_left hc)),
            if_neg hmem]
  | receipt i =>
    by_cases hi : i = s.log.length
    · subst hi
      rw [step3w_hit3]
      show ((createTurn actor newCell bal :: s.log).reverse[s.log.length]?).map C.receipt = _
      rw [receipt_append, if_pos rfl]
      rfl
    · have hne3 : UKey.receipt i ≠ UKey.receipt s.log.length := by
        intro hcon; injection hcon with h1; exact hi h1
      rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
        (writeOp_addr_ne hne3)]
      show ((createTurn actor newCell bal :: s.log).reverse[i]?).map C.receipt
        = (s.log.reverse[i]?).map C.receipt
      rw [receipt_append, if_neg hi]
  | balA c aa =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | hcell c kk =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | lifecycle c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | deathCert c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | cap hh i =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegate c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegSnap c i =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegEpoch c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegStamp c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | caveat c i =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | factory vk =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | nullifier nn =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | revoked nn =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | commitment nn =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl

/-! ## §5 — ADAPTER (a): the cap-leaf value codec (`docs/UNIVERSAL-MEMORY.md:138-144`).

Today's live cap leaf is the FLAT 4-ary sponge `hash[holder, target, rights, op]`
(`EffectVmEmitCapRoot.siteCapEdgeLeaf`); the universal map's generic leaf is the 2-ary
`hash[addr, value]` (`Heap.leafOf`). The adapter: encode the cap tuple's value part as ONE
sponge value `capCellValue = hash[target, rights, op]` and key the cell by the holder. The
lemma: under the SAME named CR floor, the generic leaf over the encoded value is injective
in the FULL `(holder, target, rights, op)` tuple — nothing the flat leaf binds is lost. -/

/-- The cap-cell VALUE codec: the cap edge's non-key content as one sponge value. -/
def capCellValue (hash : List ℤ → ℤ) (target rights op : ℤ) : ℤ := hash [target, rights, op]

/-- **`cap_leaf_value_codec`** — the generic `Heap.leafOf` over `capCellValue` binds the full
cap tuple: two equal generic leaves force equal `(holder, target, rights, op)`. Two CR
applications (outer leaf, inner value), no new combinatorics. -/
theorem cap_leaf_value_codec (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ t₁ r₁ o₁ h₂ t₂ r₂ o₂ : ℤ}
    (heq : Heap.leafOf hash (h₁, capCellValue hash t₁ r₁ o₁)
         = Heap.leafOf hash (h₂, capCellValue hash t₂ r₂ o₂)) :
    h₁ = h₂ ∧ t₁ = t₂ ∧ r₁ = r₂ ∧ o₁ = o₂ := by
  have houter := hCR _ _ heq
  injection houter with hh hrest
  injection hrest with hv _
  have hinner := hCR _ _ hv
  injection hinner with ht hrest2
  injection hrest2 with hr hrest3
  injection hrest3 with ho _
  exact ⟨hh, ht, hr, ho⟩

/-- The FLAT live leaf (`siteCapEdgeLeaf`'s 4-ary shape) binds the same tuple under the same
floor — so the two leaf forms are interchangeable carriers of the cap edge: each is injective
in `(holder, target, rights, op)`. -/
theorem cap_leaf_flat_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ t₁ r₁ o₁ h₂ t₂ r₂ o₂ : ℤ}
    (heq : hash [h₁, t₁, r₁, o₁] = hash [h₂, t₂, r₂, o₂]) :
    h₁ = h₂ ∧ t₁ = t₂ ∧ r₁ = r₂ ∧ o₁ = o₂ := by
  have hl := hCR _ _ heq
  injection hl with hh hr1
  injection hr1 with ht hr2
  injection hr2 with hr hr3
  injection hr3 with ho _
  exact ⟨hh, ht, hr, ho⟩

/-! ## §6 — ADAPTER (b): the index-domain MMR boundary derivation
(`docs/UNIVERSAL-MEMORY.md:115-121`).

The receipt-index domain is keyed by POSITION (append-only), and its boundary commitment is
the MMR root (`MMR.mroot`), not a sorted-map root. The `boundary_root_derived` analogue:
reading the (pinned) final index cells back over the declared position range RECONSTRUCTS the
committed log, so the boundary-derived MMR root equals today's root — list canonicity, NO
crypto. Welded to the ONE balance via `memcheck_pins_final`, exactly as
`boundary_root_from_memcheck`. -/

/-- The declared index-domain address range `[off, off+n)` as ℤ keys. -/
def indexRange (off n : Nat) : List ℤ := (List.range' off n).map (Nat.cast)

/-- Reconstruction: if the final index cells carry exactly the log's rows at positions
`off..off+n`, the boundary view over the declared range IS the log (values in order). -/
theorem boundaryCells_indexRange_reconstructs {fin' : ℤ → Option ℤ} :
    ∀ (L : List ℤ) (off : Nat),
      (∀ i : Nat, (h : i < L.length) → fin' ((off + i : Nat) : ℤ) = some L[i]) →
      (boundaryCells fin' (indexRange off L.length)).map Prod.snd = L := by
  intro L
  induction L with
  | nil => intro off _; rfl
  | cons x L ih =>
      intro off hsem
      have h0 : fin' ((off : Nat) : ℤ) = some x := by
        have := hsem 0 (by simp)
        simpa using this
      have hrec : (boundaryCells fin' (indexRange (off + 1) L.length)).map Prod.snd = L := by
        apply ih
        intro i h
        have hx := hsem (i + 1) (by simpa using Nat.succ_lt_succ h)
        have harg : ((off + (i + 1) : Nat) : ℤ) = (((off + 1) + i : Nat) : ℤ) := by
          congr 1
          omega
        rw [harg] at hx
        simpa using hx
      show (boundaryCells fin' (indexRange off (L.length + 1))).map Prod.snd = x :: L
      rw [indexRange, List.range'_succ, List.map_cons]
      show (boundaryCells fin' (((off : Nat) : ℤ)
          :: (List.range' (off + 1) L.length).map Nat.cast)).map Prod.snd = x :: L
      rw [boundaryCells, h0]
      show ((((off : Nat) : ℤ), x)
          :: boundaryCells fin' ((List.range' (off + 1) L.length).map Nat.cast)).map
            Prod.snd = x :: L
      rw [List.map_cons]
      show x :: (boundaryCells fin' (indexRange (off + 1) L.length)).map Prod.snd = x :: L
      rw [hrec]

/-- **`index_boundary_mroot_derived`** — the MMR analogue of `boundary_root_derived`: the
index log reconstructed from the final index cells has TODAY'S MMR root. List canonicity,
NO crypto. -/
theorem index_boundary_mroot_derived (hash : List ℤ → ℤ) {L : List ℤ} {fin' : ℤ → Option ℤ}
    (hsem : ∀ i : Nat, (h : i < L.length) → fin' (i : ℤ) = some L[i]) :
    MMR.mroot hash L
      = MMR.mroot hash ((boundaryCells fin' (indexRange 0 L.length)).map Prod.snd) := by
  rw [boundaryCells_indexRange_reconstructs L 0 (by intro i h; simpa using hsem i h)]

/-- **`index_boundary_mroot_from_memcheck`** — the index-domain analogue of
`boundary_root_from_memcheck`: under the ONE balance, the MMR root derived from the prover's
claimed final index cells equals the root of the GENUINE log — `memcheck_pins_final` forces
the claims to the real fold, and reconstruction is canonicity. -/
theorem index_boundary_mroot_from_memcheck (hash : List ℤ → ℤ)
    {init : UAddr ℤ → Option ℤ} {fin : UAddr ℤ → Option ℤ × Nat}
    {addrs : List (UAddr ℤ)} {tr : List (Op (UAddr ℤ) (Option ℤ))} {L : List ℤ}
    (hnd : addrs.Nodup) (hcl : ∀ op ∈ tr, op.addr ∈ addrs)
    (hdisc : Disciplined tr) (hmc : MemCheck init fin addrs tr)
    (hda : ∀ i : Nat, i < L.length → (Domain.index, (i : ℤ)) ∈ addrs)
    (hsem : ∀ i : Nat, (h : i < L.length) →
      (tr.foldl step init) (Domain.index, (i : ℤ)) = some L[i]) :
    MMR.mroot hash L
      = MMR.mroot hash ((boundaryCells (fun a => (fin (Domain.index, a)).1)
          (indexRange 0 L.length)).map Prod.snd) := by
  refine index_boundary_mroot_derived hash (fun i h => ?_)
  rw [Dregg2.Crypto.UniversalMemory.memcheck_pins_final hnd hcl hdisc hmc _ (hda i h)]
  exact hsem i h

/-! ## §6.5 — THE CROSS-CELL-READ REFINEMENT: the circuit's MapOp::Read leg REFINES
`ObservedFieldEquals` (`turn/src/executor/mod.rs:387-393`,
`circuit/tests/effect_vm_umem_real_turn.rs` keystone `99a8dc94`).

Codex's cross-review (`docs/deos/UMEM-CROSS-REVIEW-CODEX.md`) named the precise gap: the cross-cell-
read primitive exists as a Rust circuit test — a turn reads cell B's committed state via a
`MapOp::Read` against B's published heap root (the root column pinned to a public input) — but the
circuit↔`ObservedFieldEquals` THEOREM did not exist in Lean. This section is that theorem.

The shape (faithful to `xcell_read_desc` in the test):

  * The circuit's MapOp::Read leg, when the row's guard fires, denotes
    `opensToMerkle hash d openedRoot readAddr (some readValue)` — the `.read` arm of
    `DescriptorIR2.MapOp.holdsAt` — and the `PiBinding` leg pins `openedRoot = publishedRoot`
    (the published peer commitment supplied as a public input).
  * The published root is AUTHENTICATED as peer B's committed field-plane root by the host root-
    authority (the executor's `IssuerRootAuthority` check; off-circuit, exactly the carrier
    `TurnCtx.observedFields`'s prose precondition). We model that authentication as: B's GENUINE
    committed field-plane heap `peerHeap` (sorted, depth-`d`, `2^d` leaves) has
    `mapRoot hash d peerHeap = publishedRoot`, and B's committed field at `readAddr` is
    `Heap.get peerHeap readAddr`.

Then `readValue` IS B's committed published field, by the deployed binary-Merkle anti-forge
(`opensToMerkle_functional` → `mapRoot_injective`): the genuine peerHeap is itself an opening at
`(publishedRoot, readAddr)`, and the circuit's accepted opening is at the SAME root+key, so the two
read values agree. No whole-image equality is needed — this is exactly the per-cell membership view
Codex confirmed sound on its own; the anchor is `boundary_init_root_derived`'s `hsem` realized at the
single declared address `readAddr`. The CR floor enters ONCE, at the injectivity tooth, never per
access.

`crossCellRead_refines_observedField` is the theorem; it is then welded to the program carrier
(`cross_cell_read_pins_observedValue` / `cross_cell_read_admits_observedFieldEquals`): the value the
circuit accepts is exactly what makes `TurnCtx.observedValue` SOUND, and an admitted
`observedFieldEquals` turn's `new[localField]` then equals B's committed field
(`Program.evalConstraintCtx_observedFieldEquals_iff`). The witnessed cross-cell read is now a
circuit fact, not a free-witnessed assertion. -/

section CrossCellRead

variable (hash : List ℤ → ℤ) (d : Nat)

/-- **`crossCellRead_refines_observedField` — THE OFE THEOREM.** If the circuit accepts a turn as
reading `(readAddr ↦ readValue)` — i.e. its MapOp::Read leg holds (`hopen`: an `opensToMerkle`
opening at the opened root) and the opened root equals the published, PI-pinned peer commitment
(`hpi`) — and that published commitment is authenticated as peer B's committed field-plane root
(`hcommit`: B's genuine sorted, depth-`d`, `2^d`-leaf field heap `peerHeap` has
`mapRoot hash d peerHeap = publishedRoot`), THEN the read value IS B's committed published field:
`some readValue = Heap.get peerHeap readAddr`. The circuit's cross-cell read REFINES the executor's
`ObservedFieldEquals` carrier — per-cell membership against the published root, anchored at
`boundary_init_root_derived`'s `hsem` for the single address `readAddr`. -/
theorem crossCellRead_refines_observedField (hCR : Poseidon2SpongeCR hash)
    {openedRoot publishedRoot readAddr readValue : ℤ} {peerHeap : Heap.FeltHeap}
    (hopen : opensToMerkle hash d openedRoot readAddr (some readValue))
    (hpi : openedRoot = publishedRoot)
    (hps : Heap.SortedKeys peerHeap) (hpl : peerHeap.length = 2 ^ d)
    (hcommit : mapRoot hash d peerHeap = publishedRoot) :
    some readValue = Heap.get peerHeap readAddr := by
  -- the genuine committed peer heap is ITSELF an opening at (publishedRoot, readAddr).
  have hgenuine : opensToMerkle hash d publishedRoot readAddr (Heap.get peerHeap readAddr) :=
    ⟨peerHeap, hps, hpl, hcommit, rfl⟩
  -- the circuit's accepted opening is at the same root (by the PI pin) and key.
  have hopen' : opensToMerkle hash d publishedRoot readAddr (some readValue) := hpi ▸ hopen
  -- anti-forge: root + key determine the read, so the two read values agree.
  exact (Dregg2.Circuit.MapMerkleRoot.opensToMerkle_functional hash hCR d hopen' hgenuine)

/-- **`cross_cell_read_pins_observedValue` — the carrier is SOUND.** When the §8 portal's
`observedFields` triple `(sourceCell, sourceField, readValue)` is the one the circuit's MapOp::Read
leg accepted against the authenticated published peer root, the carrier value IS peer B's committed
field. This discharges the prose precondition on `TurnCtx.observedFields` (`Program.lean:1097-1108`)
with a circuit fact: `observedValue` is not free-witnessed — it equals the committed value the read
opened against the published commitment. -/
theorem cross_cell_read_pins_observedValue (hCR : Poseidon2SpongeCR hash)
    (ctx : TurnCtx) (sourceCell : ℤ) (sourceField : FieldName)
    {openedRoot publishedRoot readAddr readValue committedValue : ℤ}
    {peerHeap : Heap.FeltHeap}
    -- the carrier holds exactly the read value the circuit accepted:
    (hcarrier : ctx.observedValue sourceCell sourceField = some readValue)
    -- B's committed field at readAddr is `committedValue` (a present cell):
    (hfield : Heap.get peerHeap readAddr = some committedValue)
    -- the circuit accepted the read against the authenticated published root:
    (hopen : opensToMerkle hash d openedRoot readAddr (some readValue))
    (hpi : openedRoot = publishedRoot)
    (hps : Heap.SortedKeys peerHeap) (hpl : peerHeap.length = 2 ^ d)
    (hcommit : mapRoot hash d peerHeap = publishedRoot) :
    ctx.observedValue sourceCell sourceField = some committedValue := by
  have h := crossCellRead_refines_observedField hash d hCR hopen hpi hps hpl hcommit
  rw [hfield] at h
  -- `h : some readValue = some committedValue`; close the rewritten carrier goal.
  rw [hcarrier]; exact h

/-- **`cross_cell_read_admits_observedFieldEquals` — END-TO-END: an admitted `observedFieldEquals`
turn copies B's COMMITTED field.** Combining the circuit refinement with the program keystone
(`Program.evalConstraintCtx_observedFieldEquals_iff`): if the turn's `observedFieldEquals` atom is
ADMITTED and the carrier triple was produced by the circuit's MapOp::Read leg against the
authenticated published peer root, then the admitted turn's `new[localField]` EQUALS peer B's
committed field value `committedValue`. The cross-cell read is verified, never asserted. -/
theorem cross_cell_read_admits_observedFieldEquals (hCR : Poseidon2SpongeCR hash)
    (ctx : TurnCtx) (localField : FieldName) (sourceCell : ℤ) (sourceField : FieldName)
    (o n : Value)
    {openedRoot publishedRoot readAddr readValue committedValue : ℤ}
    {peerHeap : Heap.FeltHeap}
    (hadmit : evalConstraintCtx ctx
        (.observedFieldEquals localField sourceCell sourceField) o n = true)
    (hfield : Heap.get peerHeap readAddr = some committedValue)
    (hopen : opensToMerkle hash d openedRoot readAddr (some readValue))
    (hpi : openedRoot = publishedRoot)
    (hps : Heap.SortedKeys peerHeap) (hpl : peerHeap.length = 2 ^ d)
    (hcommit : mapRoot hash d peerHeap = publishedRoot)
    -- the carrier triple the portal opened is the value the circuit accepted:
    (hcarrier : ctx.observedValue sourceCell sourceField = some readValue) :
    n.scalar localField = some committedValue := by
  obtain ⟨v, hv, hn⟩ :=
    (evalConstraintCtx_observedFieldEquals_iff ctx localField sourceCell sourceField o n).mp
      hadmit
  -- the carrier value `v` is forced to be the circuit-accepted `readValue`…
  rw [hcarrier] at hv
  have hvr : v = readValue := (Option.some_inj.mp hv).symm
  subst hvr
  -- …which the refinement pins to B's committed field.
  have hpin := crossCellRead_refines_observedField hash d hCR hopen hpi hps hpl hcommit
  rw [hfield] at hpin
  rw [hn, Option.some_inj.mp hpin]

/-! ### §6.5b — THE WHOLE-IMAGE (no-extra-cells) DIRECTION of the deployed cross-cell read.

`crossCellRead_refines_observedField` is the SUBSET view: each declared address opens to peer B's
committed value under the published root (`opensToMerkle_functional`). It is sound for "this peer
field IS the committed value", but on its own it does NOT forbid a committed peer heap that holds
the declared cells AND EXTRA cells the boundary never declared — exactly the named tail in
`circuit/src/descriptor_ir2.rs` (the no-extra-cells direction "rides the universal-map rotation").

This section closes that direction at the bridge level, against the DEPLOYED binary-Merkle root.
`UniversalMemory.boundary_whole_image_sem` carries the no-extra-cells punch over the FLAT-sponge
commitment (`Heap.root_injective`); the deployed cross-cell read commits the peer field plane by
the depth-`d` binary fold (`MapMerkleRoot.mapRoot`, the `CanonicalHeapTree::root`). So the
deployed whole-image direction is the BINARY analog: it rides `mapRoot_injective` (the binary
anti-ghost) exactly as `crossCellRead_refines_observedField` rides `opensToMerkle_functional`
rather than the flat per-cell `boundary_init_root_derived`. The single CR tooth enters once, on
the WHOLE-boundary fold instead of a per-cell opening — no new crypto, the precise binary mirror
of `boundary_image_eq_of_root`.

The hypothesis `hpin` — the published peer root EQUALS `mapRoot hash d boundaryHeap`, the binary
fold of the ENTIRE declared whole-boundary view (a sorted `2^d`-leaf heap realizing the declared
image) — is EXACTLY the in-circuit obligation that remains: an AIR that COMPUTES the whole-boundary
binary fold over the universal boundary table (the per-domain sorted-leaf fold chip, padded to the
`2^d`-leaf vector) and pins it to the published-root public input. That fold chip rides the
universal-map rotation; today's leg realizes only the per-cell `opensToMerkle` openings above. -/

section CrossCellReadWholeImage

variable (hash : List ℤ → ℤ) (d : Nat)

/-- **`crossCellRead_whole_image` — the committed peer heap IS the declared whole-boundary view
(no extra cells), deployed binary-Merkle leg.** If the published peer root is the binary fold of
peer B's committed `2^d`-leaf field heap (`hcommit`) AND equals the binary fold of the declared
whole-boundary view `boundaryHeap` (`hpin`, the in-circuit whole-boundary fold pin), then under the
named CR floor the committed peer heap EQUALS that boundary view: a single extra or altered leaf
moves the binary root, so the peer can hold NOTHING the boundary never declared. The binary-Merkle
companion of `UniversalMemory.boundary_image_eq_of_root` — `mapRoot_injective` where the flat
companion uses `Heap.root_injective`. -/
theorem crossCellRead_whole_image (hCR : Poseidon2SpongeCR hash)
    {publishedRoot : ℤ} {peerHeap boundaryHeap : Heap.FeltHeap}
    (hpl : peerHeap.length = 2 ^ d) (hbl : boundaryHeap.length = 2 ^ d)
    (hcommit : mapRoot hash d peerHeap = publishedRoot)
    (hpin : mapRoot hash d boundaryHeap = publishedRoot) :
    peerHeap = boundaryHeap :=
  Dregg2.Circuit.MapMerkleRoot.mapRoot_injective hash hCR d hpl hbl (hcommit.trans hpin.symm)

/-- **`crossCellRead_whole_image_sem` — the committed peer heap agrees with the declared image at
EVERY address (no extra cells, in lookup terms).** The lookup-world consequence: once the published
peer root is pinned to the whole-boundary fold (`hpin`) and the declared boundary view realizes the
image `if k ∈ as then init k else none` (`hbsem` — the obligation the in-circuit leaf assembly
discharges), the committed peer heap's `get` equals that image at EVERY address: declared cells
open to their declared value, and EVERY address OFF the declared list is ABSENT in the peer heap.
The deployed binary-Merkle realization of `UniversalMemory.boundary_whole_image_sem`. -/
theorem crossCellRead_whole_image_sem (hCR : Poseidon2SpongeCR hash)
    {publishedRoot : ℤ} {peerHeap boundaryHeap : Heap.FeltHeap}
    {init : ℤ → Option ℤ} {as : List ℤ}
    (hpl : peerHeap.length = 2 ^ d) (hbl : boundaryHeap.length = 2 ^ d)
    (hcommit : mapRoot hash d peerHeap = publishedRoot)
    (hpin : mapRoot hash d boundaryHeap = publishedRoot)
    (hbsem : ∀ k, Heap.get boundaryHeap k = if k ∈ as then init k else none) :
    ∀ k, Heap.get peerHeap k = if k ∈ as then init k else none := by
  intro k
  rw [crossCellRead_whole_image hash d hCR hpl hbl hcommit hpin]
  exact hbsem k

/-- **`cross_cell_read_no_extra_cell` — a peer cell OFF the declared boundary is ABSENT.** The
no-extra-cells punch the per-cell subset view could not reach: under the whole-boundary fold pin,
any address `k ∉ as` (never declared) is `none` in the committed peer heap — the peer cannot hide a
cell behind the published root. A cross-cell read returning `none` at an undeclared address is
therefore SOUND (the peer genuinely has no such cell). -/
theorem cross_cell_read_no_extra_cell (hCR : Poseidon2SpongeCR hash)
    {publishedRoot : ℤ} {peerHeap boundaryHeap : Heap.FeltHeap}
    {init : ℤ → Option ℤ} {as : List ℤ} {k : ℤ}
    (hpl : peerHeap.length = 2 ^ d) (hbl : boundaryHeap.length = 2 ^ d)
    (hcommit : mapRoot hash d peerHeap = publishedRoot)
    (hpin : mapRoot hash d boundaryHeap = publishedRoot)
    (hbsem : ∀ k, Heap.get boundaryHeap k = if k ∈ as then init k else none)
    (hk : k ∉ as) :
    Heap.get peerHeap k = none := by
  have h := crossCellRead_whole_image_sem hash d hCR hpl hbl hcommit hpin hbsem k
  rwa [if_neg hk] at h

/-- **`cross_cell_read_whole_image_teeth` — the no-extra-cells REFUSAL.** A committed peer heap that
DIFFERS from the declared whole-boundary view (e.g. holds an extra cell, or alters a declared one)
CANNOT share the whole-boundary fold root: the binary anti-ghost (`mapRoot_injective`) discriminates.
This is the two-valued tooth showing the whole-image pin is not vacuous — the contrapositive of
`crossCellRead_whole_image`. -/
theorem cross_cell_read_whole_image_teeth (hCR : Poseidon2SpongeCR hash)
    {peerHeap boundaryHeap : Heap.FeltHeap}
    (hpl : peerHeap.length = 2 ^ d) (hbl : boundaryHeap.length = 2 ^ d)
    (hne : peerHeap ≠ boundaryHeap) :
    mapRoot hash d peerHeap ≠ mapRoot hash d boundaryHeap :=
  fun heq => hne (Dregg2.Circuit.MapMerkleRoot.mapRoot_injective hash hCR d hpl hbl heq)

end CrossCellReadWholeImage

end CrossCellRead

/-! ## §6.6 — NON-VACUITY for the cross-cell-read refinement: a concrete honest read +
the anti-forge teeth (the Lean shadow of the four Rust circuit teeth). -/

section CrossCellReadNonVacuity

/-- A concrete depth-0 peer field heap: one present cell `(readAddr 4 ↦ 777)` — the test's
`peer.state.fields[3] = 777` published as a single leaf. Depth-0 (`2^0 = 1` leaf) keeps the
`#guard`/`example` witnesses computable while exercising the same `opensToMerkle` opening. -/
private def peerHeapEx : Heap.FeltHeap := [(4, 777)]

private theorem peerHeapEx_sorted : Heap.SortedKeys peerHeapEx := by
  simp [peerHeapEx, Heap.SortedKeys, Heap.keys]

private theorem peerHeapEx_len : peerHeapEx.length = 2 ^ 0 := rfl

/-- The honest read of `(4 ↦ 777)` against the peer's committed root opens to the committed value —
the positive witness (the Rust `cross_cell_read_proves_committed_peer_state` test). -/
example (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (hopen : opensToMerkle hash 0 (mapRoot hash 0 peerHeapEx) 4 (some 777)) :
    some (777 : ℤ) = Heap.get peerHeapEx 4 :=
  crossCellRead_refines_observedField hash 0 hCR hopen rfl
    peerHeapEx_sorted peerHeapEx_len rfl

/-- TOOTH (forged field value): a read claiming value `778` against the SAME committed root cannot
also open to the genuine `777` — the two openings would contradict `opensToMerkle_functional`. The
Lean shadow of `cross_cell_read_forged_field_value_refuses`. -/
example (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (hforged : opensToMerkle hash 0 (mapRoot hash 0 peerHeapEx) 4 (some 778)) : False := by
  have h := crossCellRead_refines_observedField hash 0 hCR hforged rfl
    peerHeapEx_sorted peerHeapEx_len rfl
  -- `some 778 = Heap.get peerHeapEx 4 = some 777`, a contradiction.
  rw [show Heap.get peerHeapEx 4 = some 777 from rfl] at h
  have : (778 : ℤ) = 777 := Option.some_inj.mp h
  omega

-- The lookup characterization is concrete: the committed cell is present at addr 4, absent at the
-- sentinel-adjacent addr 5 (the off-leaf address).
#guard Heap.get peerHeapEx 4 == some 777
#guard Heap.get peerHeapEx 5 == none

/-- WHOLE-IMAGE non-vacuity: the peer's one-cell heap agrees with the declared image at EVERY
address — the declared cell `(4 ↦ 777)` present, every off-list address absent. This `get`-shape is
exactly the proven flat companion's (`UniversalMemory.get_boundaryCells` /
`boundary_whole_image_sem`), here on the concrete `peerHeapEx`. -/
private theorem peerHeapEx_whole_image_sem :
    ∀ k, Heap.get peerHeapEx k
      = if k ∈ [(4 : ℤ)] then (if k = 4 then some (777 : ℤ) else none) else none := by
  intro k
  rw [show peerHeapEx = [((4 : ℤ), (777 : ℤ))] from rfl]
  by_cases hk : k = 4
  · subst hk; decide
  · rw [if_neg (fun h => hk (List.mem_singleton.mp h)),
        Heap.get_cons_ne _ _ hk, Heap.get_nil]

/-- The honest whole-image read: with the published peer root pinned to the binary fold of the
declared whole-boundary view (here the peer heap IS its own one-cell boundary view),
`crossCellRead_whole_image_sem` forces the committed peer to agree with the declared image
EVERYWHERE — the no-extra-cells direction the per-cell subset opening could not see. -/
example (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ k, Heap.get peerHeapEx k
      = if k ∈ [(4 : ℤ)] then (if k = 4 then some (777 : ℤ) else none) else none :=
  crossCellRead_whole_image_sem hash 0 hCR peerHeapEx_len peerHeapEx_len rfl rfl
    peerHeapEx_whole_image_sem

/-- TOOTH (no extra cell): a concrete off-list address (addr 5) is ABSENT in the committed peer
(`cross_cell_read_no_extra_cell`) — a hidden cell cannot survive the whole-boundary fold pin. -/
example (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    Heap.get peerHeapEx 5 = none :=
  cross_cell_read_no_extra_cell hash 0 hCR peerHeapEx_len peerHeapEx_len rfl rfl
    peerHeapEx_whole_image_sem (by decide)

end CrossCellReadNonVacuity

/-! ## §7 — NON-VACUITY: a concrete three-verb run, fold-checked address-by-address.

A real little kernel (two live accounts, a mint cap), all three verbs COMMIT, and the fold of
each emitted trace over the pre-projection equals the post-projection at touched, framed,
appended, and off-domain addresses — the executable shadow of the three keystones. -/

section NonVacuity

/-- A simple computable codec (agreement is codec-agnostic; injectivity is the boundary's
business, not the fold's). -/
private def C0 : UCodec :=
  { val := fun v => match v with | .int i => i | _ => 0
  , cap := fun _ => 0
  , caveat := fun _ => 0
  , factory := fun _ => 0
  , receipt := fun t => (t.actor : ℤ) + 2 * t.src + 3 * t.dst + 5 * t.amt }

private def k0 : RecordKernelState :=
  { accounts := {1, 2}
  , cell := fun _ => .record [(balanceField, .int 10)]
  , caps := fun l => if l = 1 then [Cap.node 3] else [] }

private def s0 : RecChainedState := { kernel := k0, log := [] }

-- THE GWRITE VERB commits and its fold agrees (write · slot-frame · cell-frame · receipt ·
-- existence-frame · off-domain).
private def s1 : RecChainedState := (stateStepGuarded s0 "color" 1 1 7).getD s0
private def gtr : List UOp := gwriteTrace C0 s0 "color" 1 1 7

#guard (stateStepGuarded s0 "color" 1 1 7).isSome
#guard decide (uproj C0 s1 (uaddr (.field 1 "color"))
  = (gtr.foldl step (uproj C0 s0)) (uaddr (.field 1 "color")))
#guard decide (uproj C0 s1 (uaddr (.field 1 balanceField))
  = (gtr.foldl step (uproj C0 s0)) (uaddr (.field 1 balanceField)))
#guard decide (uproj C0 s1 (uaddr (.field 2 "color"))
  = (gtr.foldl step (uproj C0 s0)) (uaddr (.field 2 "color")))
#guard decide (uproj C0 s1 (uaddr (.receipt 0))
  = (gtr.foldl step (uproj C0 s0)) (uaddr (.receipt 0)))
#guard decide (uproj C0 s1 (uaddr (.exist 1))
  = (gtr.foldl step (uproj C0 s0)) (uaddr (.exist 1)))
#guard decide (uproj C0 s1 ((Domain.caps, UKey.field 1 "color") : UAddr UKey)
  = (gtr.foldl step (uproj C0 s0)) ((Domain.caps, UKey.field 1 "color") : UAddr UKey))
-- the written cell really moved (none of this is vacuous frame agreement):
#guard decide (uproj C0 s1 (uaddr (.field 1 "color")) = some 7)
#guard decide (uproj C0 s0 (uaddr (.field 1 "color")) = none)

-- THE MOVE VERB commits and its fold agrees (debit · credit · frame · receipt).
private def tm : Turn := { actor := 1, src := 1, dst := 2, amt := 4 }
private def s2 : RecChainedState := (recCexec s0 tm).getD s0
private def mtr : List UOp := moveTrace C0 s0 tm

#guard (recCexec s0 tm).isSome
#guard decide (uproj C0 s2 (uaddr (.field 1 balanceField))
  = (mtr.foldl step (uproj C0 s0)) (uaddr (.field 1 balanceField)))
#guard decide (uproj C0 s2 (uaddr (.field 2 balanceField))
  = (mtr.foldl step (uproj C0 s0)) (uaddr (.field 2 balanceField)))
#guard decide (uproj C0 s2 (uaddr (.field 1 "color"))
  = (mtr.foldl step (uproj C0 s0)) (uaddr (.field 1 "color")))
#guard decide (uproj C0 s2 (uaddr (.receipt 0))
  = (mtr.foldl step (uproj C0 s0)) (uaddr (.receipt 0)))
#guard decide (uproj C0 s2 (uaddr (.field 1 balanceField)) = some 6)   -- 10 − 4
#guard decide (uproj C0 s2 (uaddr (.field 2 balanceField)) = some 14)  -- 10 + 4

-- THE CREATE VERB commits and its fold agrees (existence · balance · fresh-frame · receipt).
private def s3 : RecChainedState := (createCellStep s0 1 3 5).getD s0
private def ctr : List UOp := createTrace C0 s0 1 3 5

#guard (createCellStep s0 1 3 5).isSome
#guard decide (uproj C0 s3 (uaddr (.exist 3))
  = (ctr.foldl step (uproj C0 s0)) (uaddr (.exist 3)))
#guard decide (uproj C0 s3 (uaddr (.field 3 balanceField))
  = (ctr.foldl step (uproj C0 s0)) (uaddr (.field 3 balanceField)))
#guard decide (uproj C0 s3 (uaddr (.field 3 "color"))
  = (ctr.foldl step (uproj C0 s0)) (uaddr (.field 3 "color")))
#guard decide (uproj C0 s3 (uaddr (.exist 2))
  = (ctr.foldl step (uproj C0 s0)) (uaddr (.exist 2)))
#guard decide (uproj C0 s3 (uaddr (.receipt 0))
  = (ctr.foldl step (uproj C0 s0)) (uaddr (.receipt 0)))
#guard decide (uproj C0 s0 (uaddr (.exist 3)) = none)        -- fresh before…
#guard decide (uproj C0 s3 (uaddr (.exist 3)) = some 1)      -- …born after
#guard decide (uproj C0 s3 (uaddr (.field 3 balanceField)) = some 5)

-- ADAPTER (b)'s reconstruction, executably: two index cells rebuild the two-row log.
#guard (boundaryCells
  (fun a => if a = 0 then some 7 else if a = 1 then some 9 else none)
  (indexRange 0 2)).map Prod.snd == [7, 9]

/-! ### keystone-audit companions (named, CONCRETE `*_satisfiable` / `*_teeth`).

The keystone-audit looks companions up BY NAME. Each verb-bridge keystone FIRES on its concrete committed
run (the `s1`/`s2`/`s3` above): the keystone applied to the concrete `… = some sᵢ` proof yields the full
`uproj sᵢ = trace.foldl step (uproj s₀)` function equality — a non-vacuous satisfiable. The shared teeth
shows the emitted program is NON-TRIVIAL (it really MOVES state — the gwrite genuinely writes cell 1's
"color" from `none` to `some 7`), so the "verb = its memory program" relation is not `:= True`. -/

/-- **`gwrite_is_memory_program_satisfiable`** — the gwrite-bridge keystone FIRES on the concrete write
(`s0 →"color"@1 7→ s1`): the projected post-state EQUALS the two-op trace folded onto the pre-state. -/
theorem gwrite_is_memory_program_satisfiable :
    uproj C0 s1 = (gwriteTrace C0 s0 "color" 1 1 7).foldl step (uproj C0 s0) :=
  gwrite_is_memory_program C0 (by rw [s1]; rfl)

/-- **`move_is_memory_program_satisfiable`** — the move-bridge keystone FIRES on the concrete transfer
(`s0 →move 4: 1→2→ s2`): the projected post-state EQUALS the three-op trace folded onto the pre-state. -/
theorem move_is_memory_program_satisfiable :
    uproj C0 s2 = (moveTrace C0 s0 tm).foldl step (uproj C0 s0) :=
  move_is_memory_program C0 (by rw [s2]; rfl)

/-- **`create_is_memory_program_satisfiable`** — the create-bridge keystone FIRES on the concrete birth
(`s0 →create cell 3 bal 5→ s3`): the projected post-state EQUALS the three-op trace folded onto the
pre-state. -/
theorem create_is_memory_program_satisfiable :
    uproj C0 s3 = (createTrace C0 s0 1 3 5).foldl step (uproj C0 s0) :=
  create_is_memory_program C0 (by rw [s3]; rfl)

/-- **`bridge_program_teeth`** — the emitted memory program is NON-TRIVIAL (not the identity, not
`:= True`): the gwrite genuinely MOVES cell 1's "color" slot from `none` (pre) to `some 7` (post). So the
verb-bridge keystones constrain real state motion; the relation DISCRIMINATES. -/
theorem bridge_program_teeth :
    uproj C0 s1 (uaddr (.field 1 "color")) ≠ uproj C0 s0 (uaddr (.field 1 "color")) := by decide

#assert_axioms gwrite_is_memory_program_satisfiable
#assert_axioms move_is_memory_program_satisfiable
#assert_axioms create_is_memory_program_satisfiable
#assert_axioms bridge_program_teeth

end NonVacuity

/-! ## §8 — axiom-hygiene pins. -/

#assert_axioms uproj
#assert_axioms gwriteTrace_disciplined
#assert_axioms moveTrace_disciplined
#assert_axioms moveAssetTrace_disciplined
#assert_axioms createTrace_disciplined
#assert_axioms gwrite_is_memory_program
#assert_axioms move_is_memory_program
#assert_axioms create_is_memory_program
#assert_axioms crossCellRead_refines_observedField
#assert_axioms crossCellRead_whole_image
#assert_axioms crossCellRead_whole_image_sem
#assert_axioms cross_cell_read_no_extra_cell
#assert_axioms cross_cell_read_whole_image_teeth
#assert_axioms cross_cell_read_pins_observedValue
#assert_axioms cross_cell_read_admits_observedFieldEquals
#assert_axioms cap_leaf_value_codec
#assert_axioms cap_leaf_flat_injective
#assert_axioms boundaryCells_indexRange_reconstructs
#assert_axioms index_boundary_mroot_derived
#assert_axioms index_boundary_mroot_from_memcheck

end Dregg2.Exec.UniversalBridge
