/-
# Dregg2.Crypto.MemoryChecking — offline memory checking (Blum): multiset balance ⇒ consistency.

THE EPOCH's interior principle (docs/EPOCH-DESIGN.md): inside one proof's transcript, state
consistency needs NO authenticated structure — every read and write is a tuple in a multiset,
and the read-multiset = write-multiset check (with the serial discipline and the init/final
boundary sets) IS memory consistency. This module is the semantic contract for the IR v2
memory-op kind, sitting exactly where `sorted_gap_excludes` sits for the boundary maps.

The model (the standard offline-checking instrumentation, Blum et al.):

  * an `Entry` is `addr × value × serial`. Kind lives on the OP, not the entry: it routes the
    op's two instrumentation entries into the read- and write-multisets — the entries themselves
    are kind-free so a read's claimed tuple can EQUAL the write tuple it consumes.
  * the op at trace position `i` holds serial `i + 1` (the init boundary holds serial `0`).
    Every op contributes ONE read-set entry — the untrusted memory's CLAIMED latest prior
    tuple `(addr, prevVal, prevSerial)` — and ONE write-set entry `(addr, val, i + 1)`
    (a read writes BACK the value it returned; a write installs the new value).
  * boundary sets: `initSet` = one serial-0 entry per address; `finalSet` = the prover's
    claimed final tuple per address.
  * the LOCAL per-op discipline (`Disciplined`): `prevSerial < i + 1` (no claiming the
    future) and a read returns exactly its claimed value.
  * the GLOBAL check (`MemCheck`): `initSet + writeSet = readSet + finalSet` as multisets —
    in circuit terms one LogUp/grand-product argument, zero hashing.

THE THEOREM (`memcheck_sound`): discipline + multiset balance ⇒ `Consistent` — every read
returns the latest prior write to its address (against the real fold semantics `step`).
Converse (`memcheck_complete` / `memcheck_iff_chained`): the balance holds EXACTLY when every
per-address claim chain is the honest predecessor chain (`Chained`) — so the honest prover
always passes, and passing pins the prover to honesty.

The combinatorial heart is `chain_reconstruct`: in the per-address projection, the strictly
increasing write serials + the no-future discipline force the multiset matching to be the
UNIQUE predecessor chain (peel the largest serial; only the final claim can absorb it).

Non-vacuity, both polarities, #guard-witnessed on concrete `Nat`-traces: an honest trace
balances AND is consistent; a tampered read (returns 7 where 5 lives) breaks the balance;
a time-traveling read (claims its own writeback serial) BALANCES while inconsistent — and is
exactly what `Disciplined` rejects, so the discipline hypothesis is load-bearing, not décor.

No crypto residue: everything here is unconditional combinatorics. Hashing enters only where
these multisets meet a commitment — at the boundary, in the map/MMR modules, not here.
-/
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.List.Induction
import Dregg2.Tactics

namespace Dregg2.Crypto.MemoryChecking

universe u v w

/-- Operation kind — a memory `read` or `write`. Kind routes an op's instrumentation entries;
it is deliberately NOT part of `Entry` (a read's claimed tuple must EQUAL the write tuple it
consumes for the multisets to cancel). -/
inductive Kind : Type where
  | read
  | write
deriving DecidableEq, Repr

/-- A memory-table entry: `addr × value × serial`. The atoms of the four instrumentation
multisets. Serial `0` is reserved for the init boundary; the op at trace position `i`
writes serial `i + 1`. -/
structure Entry (Addr : Type u) (Val : Type v) where
  addr   : Addr
  val    : Val
  serial : Nat
deriving DecidableEq, Repr

/-- One trace operation, carrying the untrusted memory's CLAIMED previous tuple (the prover
witness columns of the memory table). For a `write`, `val` is the value installed and
`prevVal` the value claimed overwritten; for a `read`, `val` is the value returned —
`Disciplined` forces `val = prevVal` (a read returns exactly what it claims was there). -/
structure Op (Addr : Type u) (Val : Type v) where
  kind       : Kind
  addr       : Addr
  val        : Val
  prevVal    : Val
  prevSerial : Nat
deriving DecidableEq, Repr

variable {Addr : Type u} {Val : Type v}

/-! ## The instrumentation entries and the four multisets -/

/-- The read-set entry an op contributes: the claimed latest prior tuple at its address. -/
def readEntry (op : Op Addr Val) : Entry Addr Val :=
  ⟨op.addr, op.prevVal, op.prevSerial⟩

/-- The write-set entry an op at counter `n` contributes: its (write-back) value under the
fresh serial `n + 1`. Reads write back the value they returned — the standard discipline that
makes every op consume exactly one prior tuple and produce exactly one. -/
def writeEntry (op : Op Addr Val) (n : Nat) : Entry Addr Val :=
  ⟨op.addr, op.val, n + 1⟩

/-- The read multiset of a trace. -/
def readSet : List (Op Addr Val) → Multiset (Entry Addr Val)
  | [] => 0
  | op :: tr => readEntry op ::ₘ readSet tr

/-- The write multiset of a trace, serials counted from `n` (top level: `n = 0`). -/
def writeSetFrom (n : Nat) : List (Op Addr Val) → Multiset (Entry Addr Val)
  | [] => 0
  | op :: tr => writeEntry op n ::ₘ writeSetFrom (n + 1) tr

/-- A boundary multiset: one entry per declared address. -/
def boundarySet (g : Addr → Entry Addr Val) : List Addr → Multiset (Entry Addr Val)
  | [] => 0
  | a :: as => g a ::ₘ boundarySet g as

/-- The init boundary entry of an address: its initial value at serial `0`. -/
def initEntry (init : Addr → Val) (a : Addr) : Entry Addr Val := ⟨a, init a, 0⟩

/-- The final boundary entry of an address: the prover's claimed final `(value, serial)`. -/
def finEntry (fin : Addr → Val × Nat) (a : Addr) : Entry Addr Val := ⟨a, (fin a).1, (fin a).2⟩

/-- The init boundary multiset over the declared address list. -/
def initSet (init : Addr → Val) (addrs : List Addr) : Multiset (Entry Addr Val) :=
  boundarySet (initEntry init) addrs

/-- The final boundary multiset over the declared address list. -/
def finalSet (fin : Addr → Val × Nat) (addrs : List Addr) : Multiset (Entry Addr Val) :=
  boundarySet (finEntry fin) addrs

@[simp] theorem readSet_nil : readSet ([] : List (Op Addr Val)) = 0 := rfl
@[simp] theorem readSet_cons (op : Op Addr Val) (tr : List (Op Addr Val)) :
    readSet (op :: tr) = readEntry op ::ₘ readSet tr := rfl
@[simp] theorem writeSetFrom_nil (n : Nat) : writeSetFrom n ([] : List (Op Addr Val)) = 0 := rfl
@[simp] theorem writeSetFrom_cons (n : Nat) (op : Op Addr Val) (tr : List (Op Addr Val)) :
    writeSetFrom n (op :: tr) = writeEntry op n ::ₘ writeSetFrom (n + 1) tr := rfl
@[simp] theorem boundarySet_nil (g : Addr → Entry Addr Val) :
    boundarySet g ([] : List Addr) = 0 := rfl
@[simp] theorem boundarySet_cons (g : Addr → Entry Addr Val) (a : Addr) (as : List Addr) :
    boundarySet g (a :: as) = g a ::ₘ boundarySet g as := rfl

/-! ## The check, the discipline, and the semantics -/

/-- **`MemCheck` — THE multiset balance** (the LogUp/grand-product statement, satisfaction
level): `initSet + writeSet = readSet + finalSet`. This is the ONLY global condition the
circuit's memory argument enforces; everything else is per-op local. -/
abbrev MemCheck (init : Addr → Val) (fin : Addr → Val × Nat) (addrs : List Addr)
    (tr : List (Op Addr Val)) : Prop :=
  initSet init addrs + writeSetFrom 0 tr = readSet tr + finalSet fin addrs

/-- The LOCAL per-op discipline, serials counted from `n`: the claimed prior serial is
strictly below the op's own serial `n + 1` (no claiming the future — the one timestamp
comparison the circuit row checks), and a read returns exactly its claimed value. -/
def DisciplinedFrom (n : Nat) : List (Op Addr Val) → Prop
  | [] => True
  | op :: tr =>
    (op.prevSerial < n + 1 ∧ (op.kind = .read → op.val = op.prevVal)) ∧
      DisciplinedFrom (n + 1) tr

/-- The per-op discipline of a whole trace (serials from `0`). -/
abbrev Disciplined (tr : List (Op Addr Val)) : Prop := DisciplinedFrom 0 tr

theorem disciplinedFrom_cons {n : Nat} {op : Op Addr Val} {tr : List (Op Addr Val)} :
    DisciplinedFrom n (op :: tr) ↔
      (op.prevSerial < n + 1 ∧ (op.kind = .read → op.val = op.prevVal)) ∧
        DisciplinedFrom (n + 1) tr := Iff.rfl

instance instDecidableDisciplinedFrom [DecidableEq Val] :
    ∀ (n : Nat) (tr : List (Op Addr Val)), Decidable (DisciplinedFrom n tr)
  | _, [] => isTrue trivial
  | n, _ :: tr =>
    haveI := instDecidableDisciplinedFrom (n + 1) tr
    inferInstanceAs (Decidable (_ ∧ _))

section Semantics

variable [DecidableEq Addr]

/-- The REAL memory semantics: a write updates its address, a read changes nothing. -/
def step (m : Addr → Val) (op : Op Addr Val) : Addr → Val :=
  fun a => if op.kind = .write ∧ a = op.addr then op.val else m a

theorem step_write {op : Op Addr Val} (h : op.kind = .write) (m : Addr → Val) :
    step m op op.addr = op.val := by simp [step, h]

theorem step_read {op : Op Addr Val} (h : op.kind = .read) (m : Addr → Val) :
    step m op = m := by
  funext a; simp [step, h]

theorem step_other {op : Op Addr Val} {a : Addr} (h : a ≠ op.addr) (m : Addr → Val) :
    step m op a = m a := by simp [step, h]

/-- **The consistency predicate** — every read returns the latest prior write to its address,
stated against the fold semantics: the head read must return the CURRENT value, and the rest
must be consistent from the stepped memory. -/
def ConsistentFrom (m : Addr → Val) : List (Op Addr Val) → Prop
  | [] => True
  | op :: tr => (op.kind = .read → op.val = m op.addr) ∧ ConsistentFrom (step m op) tr

/-- Memory consistency of a trace from an initial memory. -/
abbrev Consistent (init : Addr → Val) (tr : List (Op Addr Val)) : Prop :=
  ConsistentFrom init tr

theorem consistentFrom_cons {m : Addr → Val} {op : Op Addr Val} {tr : List (Op Addr Val)} :
    ConsistentFrom m (op :: tr) ↔
      (op.kind = .read → op.val = m op.addr) ∧ ConsistentFrom (step m op) tr := Iff.rfl

instance instDecidableConsistentFrom [DecidableEq Val] (m : Addr → Val) :
    ∀ tr : List (Op Addr Val), Decidable (ConsistentFrom m tr)
  | [] => isTrue trivial
  | op :: tr =>
    haveI := instDecidableConsistentFrom (step m op) tr
    inferInstanceAs (Decidable (_ ∧ _))

end Semantics

/-! ## The predecessor chain — the per-address honest-claims relation.

`Chained prev os fin` says: threading through the per-address (readEntry, writeEntry) pairs,
each op's claimed prior tuple IS the previous op's write tuple (starting from `prev`, ending
with the final claim `fin` = the last write tuple). This is exactly what the honest memory
produces, and `chain_reconstruct` shows the multiset balance FORCES it. -/

/-- The predecessor-chain relation over (read-entry, write-entry) pairs. -/
def Chained {α : Type w} (prev : α) : List (α × α) → α → Prop
  | [], fin => fin = prev
  | rw₀ :: rest, fin => rw₀.1 = prev ∧ Chained rw₀.2 rest fin

@[simp] theorem chained_nil {α : Type w} (p f : α) : Chained p [] f ↔ f = p := Iff.rfl

@[simp] theorem chained_cons {α : Type w} (p f : α) (rw₀ : α × α) (rest : List (α × α)) :
    Chained p (rw₀ :: rest) f ↔ rw₀.1 = p ∧ Chained rw₀.2 rest f := Iff.rfl

theorem chained_append_singleton {α : Type w} (o : α × α) :
    ∀ (l : List (α × α)) (p f : α),
      Chained p (l ++ [o]) f ↔ Chained p l o.1 ∧ f = o.2
  | [], p, f => by simp [Chained]
  | rw₀ :: l, p, f => by
    simp only [List.cons_append, chained_cons, chained_append_singleton o l rw₀.2 f, and_assoc]

/-- A chain rebuilds the multiset balance (the easy direction, per address):
`prev ::ₘ writes = reads + {fin}`. -/
theorem chained_multiset {α : Type w} :
    ∀ (os : List (α × α)) (initE fin : α), Chained initE os fin →
      (initE ::ₘ ((os.map Prod.snd : List α) : Multiset α))
        = ((os.map Prod.fst : List α) : Multiset α) + {fin}
  | [], initE, fin, h => by
    obtain rfl : fin = initE := h
    simp
  | rw₀ :: rest, initE, fin, h => by
    obtain ⟨h1, h2⟩ := h
    subst h1
    have ih := chained_multiset rest rw₀.2 fin h2
    simp only [List.map_cons, ← Multiset.cons_coe]
    rw [Multiset.cons_add, ← ih]

/-- **`chain_reconstruct` — the combinatorial heart (FULLY PROVED, no crypto).** In one
address class, if every op claims a strictly EARLIER serial than its own (`hdisc`) and the
write serials are strictly increasing (`hinc` — they are trace positions), then the multiset
balance `initE ::ₘ writes = reads + {fin}` forces the claims to be the UNIQUE predecessor
chain. Proof peels the LAST op: its write tuple carries the strictly largest serial, no
read claim may equal it (all claims point strictly earlier), so the FINAL claim must absorb
it; cancel and recurse — the recursive final claim is the peeled op's read claim, which the
next round pins to the new last write. -/
theorem chain_reconstruct {α : Type w} (σ : α → Nat) (initE : α) (os : List (α × α)) :
    ∀ fin : α,
      (∀ o ∈ os, σ o.1 < σ o.2) →
      ((os.map fun o => σ o.2).Pairwise (· < ·)) →
      ((initE ::ₘ ((os.map Prod.snd : List α) : Multiset α))
        = ((os.map Prod.fst : List α) : Multiset α) + {fin}) →
      Chained initE os fin := by
  induction os using List.reverseRecOn with
  | nil =>
    intro fin _ _ heq
    simp only [List.map_nil, Multiset.coe_nil, Multiset.cons_zero, zero_add] at heq
    exact (Multiset.singleton_inj.mp heq).symm
  | append_singleton os' o ih =>
    intro fin hdisc hinc heq
    simp only [List.map_append, List.map_cons, List.map_nil] at hinc heq
    rw [← Multiset.coe_add, ← Multiset.coe_add, Multiset.coe_singleton,
      Multiset.coe_singleton] at heq
    obtain ⟨hp1, _, hcross⟩ := List.pairwise_append.mp hinc
    -- The last write tuple `o.2` sits in the left side; locate it on the right.
    have hmem : o.2 ∈ initE ::ₘ (((os'.map Prod.snd : List α) : Multiset α) + {o.2}) :=
      Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _)))
    rw [heq] at hmem
    -- No read claim can carry the largest serial — only the final claim can absorb it.
    have hfin : fin = o.2 := by
      rcases Multiset.mem_add.mp hmem with hmem' | hmem'
      · exfalso
        rcases Multiset.mem_add.mp hmem' with hmem'' | hmem''
        · obtain ⟨o', ho', heq'⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmem'')
          have h1 : σ o'.1 < σ o'.2 := hdisc o' (List.mem_append_left _ ho')
          have h2 : σ o'.2 < σ o.2 :=
            hcross _ (List.mem_map.mpr ⟨o', ho', rfl⟩) _ (by simp)
          rw [heq'] at h1
          exact lt_irrefl _ (h1.trans h2)
        · have h1 : σ o.1 < σ o.2 := hdisc o (List.mem_append_right _ (by simp))
          rw [Multiset.mem_singleton] at hmem''
          rw [hmem''] at h1
          exact lt_irrefl _ h1
      · exact (Multiset.mem_singleton.mp hmem').symm
    subst hfin
    -- Cancel the absorbed tuple and recurse with the peeled op's read claim as final.
    rw [← Multiset.cons_add] at heq
    have heq2 := add_right_cancel heq
    exact (chained_append_singleton o os' initE o.2).mpr
      ⟨ih o.1 (fun o' h => hdisc o' (List.mem_append_left _ h)) hp1 heq2, rfl⟩

/-! ## The per-address projection -/

section Projection

variable [DecidableEq Addr]

/-- The (read-entry, write-entry) pairs of the ops touching address `a`, serials from `n`,
in trace order. -/
def opsAt (a : Addr) : Nat → List (Op Addr Val) → List (Entry Addr Val × Entry Addr Val)
  | _, [] => []
  | n, op :: tr =>
    if op.addr = a then (readEntry op, writeEntry op n) :: opsAt a (n + 1) tr
    else opsAt a (n + 1) tr

@[simp] theorem opsAt_nil (a : Addr) (n : Nat) :
    opsAt a n ([] : List (Op Addr Val)) = [] := rfl

theorem opsAt_cons_pos {op : Op Addr Val} {a : Addr} (h : op.addr = a)
    {n : Nat} {tr : List (Op Addr Val)} :
    opsAt a n (op :: tr) = (readEntry op, writeEntry op n) :: opsAt a (n + 1) tr := by
  simp [opsAt, h]

theorem opsAt_cons_neg {op : Op Addr Val} {a : Addr} (h : ¬op.addr = a)
    {n : Nat} {tr : List (Op Addr Val)} :
    opsAt a n (op :: tr) = opsAt a (n + 1) tr := by
  simp [opsAt, h]

/-- The discipline restricts to every address class, pointwise. -/
theorem opsAt_disc {a : Addr} {tr : List (Op Addr Val)} :
    ∀ {n : Nat}, DisciplinedFrom n tr →
      ∀ p ∈ opsAt a n tr, p.1.serial < p.2.serial := by
  induction tr with
  | nil => intro n _ p hp; simp at hp
  | cons op tr ih =>
    intro n hd p hp
    obtain ⟨⟨hser, _⟩, hrest⟩ := hd
    by_cases h : op.addr = a
    · rw [opsAt_cons_pos h] at hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hser
      · exact ih hrest p hp'
    · rw [opsAt_cons_neg h] at hp
      exact ih hrest p hp

/-- Every write serial in an address class from counter `n` is strictly above `n`. -/
theorem opsAt_serial_lb {a : Addr} {tr : List (Op Addr Val)} :
    ∀ {n : Nat}, ∀ p ∈ opsAt a n tr, n < p.2.serial := by
  induction tr with
  | nil => intro n p hp; simp at hp
  | cons op tr ih =>
    intro n p hp
    by_cases h : op.addr = a
    · rw [opsAt_cons_pos h] at hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact Nat.lt_succ_self n
      · exact Nat.lt_of_succ_lt (ih p hp')
    · rw [opsAt_cons_neg h] at hp
      exact Nat.lt_of_succ_lt (ih p hp)

/-- Write serials in an address class are strictly increasing (they are trace positions). -/
theorem opsAt_pairwise {a : Addr} {tr : List (Op Addr Val)} :
    ∀ {n : Nat}, ((opsAt a n tr).map fun p => p.2.serial).Pairwise (· < ·) := by
  induction tr with
  | nil => intro n; simp
  | cons op tr ih =>
    intro n
    by_cases h : op.addr = a
    · rw [opsAt_cons_pos h, List.map_cons]
      refine List.Pairwise.cons ?_ ih
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact opsAt_serial_lb p hp
    · rw [opsAt_cons_neg h]
      exact ih

/-- An address outside the declared list is never touched (under address closure). -/
theorem opsAt_nil_of_closure {addrs : List Addr} {a : Addr} (ha : a ∉ addrs) :
    ∀ {tr : List (Op Addr Val)}, (∀ op ∈ tr, op.addr ∈ addrs) →
      ∀ {n : Nat}, opsAt a n tr = [] := by
  intro tr
  induction tr with
  | nil => intro _ n; rfl
  | cons op tr ih =>
    intro hcl n
    have h : op.addr ≠ a := fun h => ha (h ▸ hcl op (by simp))
    rw [opsAt_cons_neg h]
    exact ih (fun o ho => hcl o (List.mem_cons_of_mem _ ho))

/-- Filtering the read multiset to one address yields that class's read entries. -/
theorem filter_readSet (a : Addr) :
    ∀ (tr : List (Op Addr Val)) (n : Nat),
      (readSet tr).filter (fun e => e.addr = a)
        = (((opsAt a n tr).map Prod.fst : List (Entry Addr Val)) : Multiset (Entry Addr Val))
  | [], n => by simp
  | op :: tr, n => by
    by_cases h : op.addr = a
    · rw [readSet_cons,
        Multiset.filter_cons_of_pos (p := fun e : Entry Addr Val => e.addr = a) _ h,
        opsAt_cons_pos h, List.map_cons, ← Multiset.cons_coe, filter_readSet a tr (n + 1)]
    · rw [readSet_cons,
        Multiset.filter_cons_of_neg (p := fun e : Entry Addr Val => e.addr = a) _ h,
        opsAt_cons_neg h, filter_readSet a tr (n + 1)]

/-- Filtering the write multiset to one address yields that class's write entries. -/
theorem filter_writeSetFrom (a : Addr) :
    ∀ (tr : List (Op Addr Val)) (n : Nat),
      (writeSetFrom n tr).filter (fun e => e.addr = a)
        = (((opsAt a n tr).map Prod.snd : List (Entry Addr Val)) : Multiset (Entry Addr Val))
  | [], n => by simp
  | op :: tr, n => by
    by_cases h : op.addr = a
    · rw [writeSetFrom_cons,
        Multiset.filter_cons_of_pos (p := fun e : Entry Addr Val => e.addr = a) _ h,
        opsAt_cons_pos h, List.map_cons, ← Multiset.cons_coe, filter_writeSetFrom a tr (n + 1)]
    · rw [writeSetFrom_cons,
        Multiset.filter_cons_of_neg (p := fun e : Entry Addr Val => e.addr = a) _ h,
        opsAt_cons_neg h, filter_writeSetFrom a tr (n + 1)]

theorem filter_boundarySet_of_notMem (g : Addr → Entry Addr Val) (hg : ∀ x, (g x).addr = x) :
    ∀ {addrs : List Addr} {a : Addr}, a ∉ addrs →
      (boundarySet g addrs).filter (fun e => e.addr = a) = 0
  | [], _, _ => by simp
  | a' :: as, a, ha => by
    have h1 : a' ≠ a := fun h => ha (h ▸ List.mem_cons_self ..)
    rw [boundarySet_cons,
      Multiset.filter_cons_of_neg (p := fun e : Entry Addr Val => e.addr = a) _ (fun h => h1 ((hg a').symm.trans h)),
      filter_boundarySet_of_notMem g hg (fun h => ha (List.mem_cons_of_mem _ h))]

/-- Filtering a boundary multiset (nodup addresses) to one declared address yields exactly
its boundary entry. -/
theorem filter_boundarySet (g : Addr → Entry Addr Val) (hg : ∀ x, (g x).addr = x) :
    ∀ {addrs : List Addr}, addrs.Nodup → ∀ {a : Addr}, a ∈ addrs →
      (boundarySet g addrs).filter (fun e => e.addr = a) = {g a}
  | [], _, a, ha => absurd ha (by simp)
  | a' :: as, hnd, a, ha => by
    obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha with rfl | hmem
    · rw [boundarySet_cons,
        Multiset.filter_cons_of_pos (p := fun e : Entry Addr Val => e.addr = a) _ (hg a),
        filter_boundarySet_of_notMem g hg hnotin, Multiset.cons_zero]
    · have h1 : a' ≠ a := fun h => hnotin (h ▸ hmem)
      rw [boundarySet_cons,
        Multiset.filter_cons_of_neg (p := fun e : Entry Addr Val => e.addr = a) _ (fun h => h1 ((hg a').symm.trans h)),
        filter_boundarySet g hg hnd' hmem]

omit [DecidableEq Addr] in
theorem addr_mem_of_mem_boundarySet (g : Addr → Entry Addr Val) (hg : ∀ x, (g x).addr = x) :
    ∀ {addrs : List Addr} {e : Entry Addr Val}, e ∈ boundarySet g addrs → e.addr ∈ addrs
  | [], _, he => absurd he (by simp)
  | a :: as, e, he => by
    rw [boundarySet_cons, Multiset.mem_cons] at he
    rcases he with rfl | he
    · rw [hg]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (addr_mem_of_mem_boundarySet g hg he)

omit [DecidableEq Addr] in
theorem addr_mem_of_mem_writeSetFrom {addrs : List Addr} :
    ∀ {tr : List (Op Addr Val)}, (∀ op ∈ tr, op.addr ∈ addrs) →
      ∀ {n : Nat} {e : Entry Addr Val}, e ∈ writeSetFrom n tr → e.addr ∈ addrs := by
  intro tr
  induction tr with
  | nil => intro _ n e he; simp at he
  | cons op tr ih =>
    intro hcl n e he
    rw [writeSetFrom_cons, Multiset.mem_cons] at he
    rcases he with rfl | he
    · exact hcl op (by simp)
    · exact ih (fun o ho => hcl o (List.mem_cons_of_mem _ ho)) he

omit [DecidableEq Addr] in
theorem addr_mem_of_mem_readSet {addrs : List Addr} :
    ∀ {tr : List (Op Addr Val)}, (∀ op ∈ tr, op.addr ∈ addrs) →
      ∀ {e : Entry Addr Val}, e ∈ readSet tr → e.addr ∈ addrs := by
  intro tr
  induction tr with
  | nil => intro _ e he; simp at he
  | cons op tr ih =>
    intro hcl e he
    rw [readSet_cons, Multiset.mem_cons] at he
    rcases he with rfl | he
    · exact hcl op (by simp)
    · exact ih (fun o ho => hcl o (List.mem_cons_of_mem _ ho)) he

/-- The multiset balance, filtered to one declared address, forces the predecessor chain
there (`chain_reconstruct` applied to the projection). -/
theorem per_address_chain {init : Addr → Val} {fin : Addr → Val × Nat}
    {addrs : List Addr} {tr : List (Op Addr Val)}
    (hnd : addrs.Nodup) (hdisc : Disciplined tr)
    (hmc : MemCheck init fin addrs tr) {a : Addr} (ha : a ∈ addrs) :
    Chained (initEntry init a) (opsAt a 0 tr) (finEntry fin a) := by
  have h := congrArg (Multiset.filter (fun e : Entry Addr Val => e.addr = a)) hmc
  simp only [initSet, finalSet] at h
  rw [Multiset.filter_add, Multiset.filter_add,
    filter_boundarySet (initEntry init) (fun _ => rfl) hnd ha,
    filter_boundarySet (finEntry fin) (fun _ => rfl) hnd ha,
    filter_writeSetFrom a tr 0, filter_readSet a tr 0,
    Multiset.singleton_add] at h
  exact chain_reconstruct Entry.serial (initEntry init a) (opsAt a 0 tr) (finEntry fin a)
    (opsAt_disc hdisc) opsAt_pairwise h

end Projection

/-! ## Chains ⇒ consistency (the forward semantic induction) -/

section Soundness

variable [DecidableEq Addr]

omit [DecidableEq Addr] in
/-- The read-echo half of the discipline, extracted per op. -/
theorem disciplined_echo {tr : List (Op Addr Val)} :
    ∀ {n : Nat}, DisciplinedFrom n tr →
      ∀ op ∈ tr, op.kind = .read → op.val = op.prevVal := by
  induction tr with
  | nil => intro n _ op h; simp at h
  | cons op' tr ih =>
    intro n hd op hmem hk
    obtain ⟨⟨_, hecho⟩, hrest⟩ := hd
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact hecho hk
    · exact ih hrest op hmem' hk

/-- Per-address predecessor chains + the read echo ⇒ memory consistency. The invariant
threads, per address, the latest write tuple (`cur`); the head of that address's chain pins
the op's claim to `cur`, whose value the invariant ties to the REAL memory. -/
theorem consistentFrom_of_chains {tr : List (Op Addr Val)} :
    ∀ {n : Nat} {m : Addr → Val} {cur fin : Addr → Entry Addr Val},
      (∀ op ∈ tr, op.kind = .read → op.val = op.prevVal) →
      (∀ a, Chained (cur a) (opsAt a n tr) (fin a)) →
      (∀ a, (cur a).val = m a) →
      ConsistentFrom m tr := by
  induction tr with
  | nil => intro n m cur fin _ _ _; trivial
  | cons op tr ih =>
    intro n m cur fin hecho hchain hval
    have hopc := hchain op.addr
    rw [opsAt_cons_pos rfl] at hopc
    obtain ⟨hr, hrest⟩ := hopc
    have hprev : op.prevVal = m op.addr := by
      have hv := congrArg Entry.val hr
      simp only [readEntry] at hv
      rw [hv, hval op.addr]
    have hread : op.kind = .read → op.val = m op.addr := fun hk =>
      (hecho op (List.mem_cons_self ..) hk).trans hprev
    refine ⟨hread, ?_⟩
    apply ih (n := n + 1) (m := step m op)
      (cur := fun a => if a = op.addr then writeEntry op n else cur a) (fin := fin)
    · exact fun op' h hk => hecho op' (List.mem_cons_of_mem _ h) hk
    · intro a
      by_cases ha : a = op.addr
      · subst ha
        rw [if_pos rfl]
        exact hrest
      · rw [if_neg ha]
        have h := hchain a
        rwa [opsAt_cons_neg (fun h' => ha h'.symm)] at h
    · intro a
      by_cases ha : a = op.addr
      · subst ha
        rw [if_pos rfl]
        show op.val = step m op op.addr
        cases hk : op.kind with
        | read => rw [step_read hk]; exact hread hk
        | write => rw [step_write hk]
      · rw [if_neg ha, step_other ha]
        exact hval a

/-- **THE THEOREM (Blum, offline memory checking): multiset balance ⇒ memory consistency.**
A disciplined trace whose four instrumentation multisets balance
(`initSet + writeSet = readSet + finalSet`) is consistent: every read returns the latest
prior write to its address. This is the WHOLE soundness contract of the IR v2 memory-op
kind — registers, heap ops, cap checks, nullifier touches ride this multiset with ZERO
intra-proof hashing; the boundary commitments take over only at the edges. -/
theorem memcheck_sound {init : Addr → Val} {fin : Addr → Val × Nat}
    {addrs : List Addr} {tr : List (Op Addr Val)}
    (hnd : addrs.Nodup) (hcl : ∀ op ∈ tr, op.addr ∈ addrs)
    (hdisc : Disciplined tr) (hmc : MemCheck init fin addrs tr) :
    Consistent init tr := by
  apply consistentFrom_of_chains (n := 0) (cur := fun a => initEntry init a)
    (fin := fun a => if a ∈ addrs then finEntry fin a else initEntry init a)
    (disciplined_echo hdisc)
  · intro a
    by_cases ha : a ∈ addrs
    · rw [if_pos ha]
      exact per_address_chain hnd hdisc hmc ha
    · rw [if_neg ha, opsAt_nil_of_closure ha hcl]
      exact rfl
  · intro a
    rfl

/-- Chains alone (with the read echo) already give consistency — the semantic half of the
round trip, no multisets needed. The honest memory's claims are chained by construction. -/
theorem chained_consistent {init : Addr → Val} {fin : Addr → Val × Nat}
    {addrs : List Addr} {tr : List (Op Addr Val)}
    (hcl : ∀ op ∈ tr, op.addr ∈ addrs)
    (hecho : ∀ op ∈ tr, op.kind = .read → op.val = op.prevVal)
    (hch : ∀ a ∈ addrs, Chained (initEntry init a) (opsAt a 0 tr) (finEntry fin a)) :
    Consistent init tr := by
  apply consistentFrom_of_chains (n := 0) (cur := fun a => initEntry init a)
    (fin := fun a => if a ∈ addrs then finEntry fin a else initEntry init a) hecho
  · intro a
    by_cases ha : a ∈ addrs
    · rw [if_pos ha]
      exact hch a ha
    · rw [if_neg ha, opsAt_nil_of_closure ha hcl]
      exact rfl
  · intro a
    rfl

end Soundness

/-! ## Completeness — the honest prover always balances -/

section Completeness

variable [DecidableEq Addr] [DecidableEq Val]

/-- **Completeness**: honest (chained) claims make the multiset check PASS. Together with
`memcheck_sound` this closes both polarities: balance ⟺ honest predecessor chains. -/
theorem memcheck_complete {init : Addr → Val} {fin : Addr → Val × Nat}
    {addrs : List Addr} {tr : List (Op Addr Val)}
    (hnd : addrs.Nodup) (hcl : ∀ op ∈ tr, op.addr ∈ addrs)
    (hch : ∀ a ∈ addrs, Chained (initEntry init a) (opsAt a 0 tr) (finEntry fin a)) :
    MemCheck init fin addrs tr := by
  refine Multiset.ext' fun e => ?_
  by_cases he : e.addr ∈ addrs
  · have hL : Multiset.count e (initSet init addrs + writeSetFrom 0 tr)
        = Multiset.count e
            ((initSet init addrs + writeSetFrom 0 tr).filter (fun x => x.addr = e.addr)) :=
      (Multiset.count_filter_of_pos (p := fun x : Entry Addr Val => x.addr = e.addr) rfl).symm
    have hR : Multiset.count e (readSet tr + finalSet fin addrs)
        = Multiset.count e
            ((readSet tr + finalSet fin addrs).filter (fun x => x.addr = e.addr)) :=
      (Multiset.count_filter_of_pos (p := fun x : Entry Addr Val => x.addr = e.addr) rfl).symm
    rw [hL, hR]
    simp only [initSet, finalSet]
    rw [Multiset.filter_add, Multiset.filter_add,
      filter_boundarySet (initEntry init) (fun _ => rfl) hnd he,
      filter_boundarySet (finEntry fin) (fun _ => rfl) hnd he,
      filter_writeSetFrom e.addr tr 0, filter_readSet e.addr tr 0,
      Multiset.singleton_add, chained_multiset _ _ _ (hch e.addr he)]
  · have h1 : e ∉ initSet init addrs :=
      fun h => he (addr_mem_of_mem_boundarySet _ (fun _ => rfl) h)
    have h2 : e ∉ writeSetFrom 0 tr := fun h => he (addr_mem_of_mem_writeSetFrom hcl h)
    have h3 : e ∉ readSet tr := fun h => he (addr_mem_of_mem_readSet hcl h)
    have h4 : e ∉ finalSet fin addrs :=
      fun h => he (addr_mem_of_mem_boundarySet _ (fun _ => rfl) h)
    rw [Multiset.count_add, Multiset.count_add,
      Multiset.count_eq_zero_of_notMem h1, Multiset.count_eq_zero_of_notMem h2,
      Multiset.count_eq_zero_of_notMem h3, Multiset.count_eq_zero_of_notMem h4]

/-- The full structural round trip: under the discipline, the multiset balance holds EXACTLY
when every address's claims are the honest predecessor chain. -/
theorem memcheck_iff_chained {init : Addr → Val} {fin : Addr → Val × Nat}
    {addrs : List Addr} {tr : List (Op Addr Val)}
    (hnd : addrs.Nodup) (hcl : ∀ op ∈ tr, op.addr ∈ addrs) (hdisc : Disciplined tr) :
    MemCheck init fin addrs tr ↔
      ∀ a ∈ addrs, Chained (initEntry init a) (opsAt a 0 tr) (finEntry fin a) :=
  ⟨fun hmc _ ha => per_address_chain hnd hdisc hmc ha, memcheck_complete hnd hcl⟩

end Completeness

/-! ## Non-vacuity — both polarities, concrete `Nat`-traces, #guard-witnessed -/

section NonVacuity

/-- All-zero initial memory. -/
private def init0 : Nat → Nat := fun _ => 0

/-- Honest trace: write 5 to addr 0, write 9 to addr 1, read addr 0 (returns 5, claims the
serial-1 write). Serials run 1, 2, 3. -/
private def trGood : List (Op Nat Nat) :=
  [⟨.write, 0, 5, 0, 0⟩, ⟨.write, 1, 9, 0, 0⟩, ⟨.read, 0, 5, 5, 1⟩]

/-- Honest final claims: addr 0 last touched by the read-back at serial 3, addr 1 by the
write at serial 2. -/
private def finGood : Nat → Nat × Nat := fun a => if a = 0 then (5, 3) else (9, 2)

-- The honest trace balances, is disciplined, and is consistent (positive polarity).
#guard decide (MemCheck init0 finGood [0, 1] trGood)
#guard decide (Disciplined trGood)
#guard decide (Consistent init0 trGood)

-- THE THEOREM fires on the honest instance end-to-end (every hypothesis discharged by
-- `decide` — nothing vacuous in the pipeline).
example : Consistent init0 trGood :=
  memcheck_sound (init := init0) (fin := finGood) (addrs := [0, 1])
    (by decide) (by decide) (by decide) (by decide)

/-- Tampered read: memory holds 5 at addr 0, the read returns 7 (claiming a prior (7,1)). -/
private def trBad : List (Op Nat Nat) :=
  [⟨.write, 0, 5, 0, 0⟩, ⟨.read, 0, 7, 7, 1⟩]

private def finBad : Nat → Nat × Nat := fun _ => (7, 2)

-- The tampered read is disciplined-but-inconsistent, and its multisets do NOT balance
-- (negative polarity — the lie (0,7,1) ∈ readSet matches no write tuple).
#guard decide (Disciplined trBad)
#guard decide (¬ Consistent init0 trBad)
#guard decide (¬ MemCheck init0 finBad [0] trBad)

/-- The discipline is LOAD-BEARING: a time-traveling read that claims its OWN write-back
serial balances the multisets while being inconsistent — and is exactly what the per-op
serial check `prevSerial < serial` rejects. -/
private def trTimeTravel : List (Op Nat Nat) :=
  [⟨.read, 0, 7, 7, 1⟩, ⟨.write, 0, 7, 0, 0⟩]

private def finTT : Nat → Nat × Nat := fun _ => (7, 2)

#guard decide (MemCheck init0 finTT [0] trTimeTravel)   -- balances!
#guard decide (¬ Consistent init0 trTimeTravel)         -- …but lies (read 7 from a 0-cell)
#guard decide (¬ Disciplined trTimeTravel)              -- …and the serial check catches it

end NonVacuity

/-! ## Axiom-hygiene pins -/

#assert_axioms chain_reconstruct
#assert_axioms memcheck_sound
#assert_axioms memcheck_complete
#assert_axioms memcheck_iff_chained
#assert_axioms chained_consistent
#assert_namespace_axioms Dregg2.Crypto.MemoryChecking

end Dregg2.Crypto.MemoryChecking
