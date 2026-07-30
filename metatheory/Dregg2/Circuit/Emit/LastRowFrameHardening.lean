/-
# Dregg2.Circuit.Emit.LastRowFrameHardening — the LAST row gets algebra.

## The wound

`VmConstraint.gate` is asserted on the TRANSITION domain: `holdsVm env isFirst true (.gate b)` is
definitionally `True` (`EffectVmEmit.holdsVm_gate_true`), and the Rust AIR agrees term-for-term
(`descriptor_ir2.rs`: `(Some(builder.is_transition()), body.eval_expr(local))`). So on the LAST row
a descriptor whose only row-local algebra is `gate`/`transition` asserts NOTHING about that row's
cells — while every deployed wide member pins its published 8-felt AFTER anchor, the value the IVC
fold consumes as the turn's ENDPOINT, at `piBinding .last`.

That was MEASURED, not predicted (`circuit/tests/last_row_anchor_forge.rs`): an honest wide
transfer, mutated on the last row only — AFTER balance rewritten, the row's Poseidon2 chip chain
re-derived from its own declared inputs (honest hashing), the PI vector rebuilt — PROVES and
VERIFIES, publishing an anchor for a state the turn never produced. The byte-identical mutation one
row earlier is REFUSED.

`circuit/tests/last_row_gate_domain_probe.rs` measured WHY, which is what fixes the repair:

  * the honest trace violates ZERO gate bodies on ALL 64 rows, last row included, and the last row
    is BYTE-IDENTICAL to the one before it;
  * under the forge the gate residue on the last row is `{#0, #46, #47}` — the economic gate and the
    two availability-limb gates — and the residue on the transition-covered row is THE SAME THREE.

So every gate that would catch the forge is present and evaluates non-zero on the last row. It is
multiplied by `is_transition()`, which is zero there. The vacuity is the MULTIPLIER.

## The repair

`hardenLastRow` re-lowers every `.base (.gate b)` as `.windowGate ⟨WindowExpr.ofLocal b, false⟩` —
the WHOLE-domain two-row gate, whose body carries no selector at all (`descriptor_ir2.rs`:
`w.on_transition.then(|| builder.is_transition())` is `None`, so the emitted polynomial IS the
body). `WindowExpr` is a strict generalization of `EmittedExpr` (`.var c` is `.loc c`), so the
lifted body is the SAME polynomial over the SAME columns; only its domain changes.

Nothing else moves. `traceWidth`, `piCount`, `tables`, `hashSites`, `ranges`, the constraint ORDER
and COUNT, and every non-`gate` constraint are preserved definitionally, so a hardened member has
the same geometry, the same PI layout, the same memory/map/umem logs and the same lookup tables as
the member it hardens. `.transition` is deliberately LEFT on the transition domain: its body reads
`nxt`, and on the last row `nxt` is the WRAP row, so a whole-domain transition would assert
`row[0].before = row[n-1].after` — false on every honest trace.

## Why the last row is then forced

With the gates whole-domain the last row is exactly as constrained as any other row:

  * the last row's BEFORE block is forced by the INCOMING `.transition` from row `n-2` (that
    instance has `isLast = false`, so it binds today and is untouched here);
  * the last row's AFTER block is forced FROM its BEFORE block by the now-live frame/economic
    gates;
  * the rotated carrier limbs are forced from the AFTER block by the now-live copy gates, and the
    chip chain forces the published anchor from the limbs.

## What this file proves, and what it does not

`satisfied2_of_hardened` is the REFINEMENT: a witness satisfying the hardened descriptor satisfies
the original. That is the direction that matters for reconnecting the existing keystones — every
theorem proved about a member still describes the hardened member's accepted witnesses.

`hardened_gate_binds_on_last_row` is the CONTENT — the thing that was FALSE before this file: under
`Satisfied2` of the hardened descriptor, every original `gate` body vanishes on the LAST row. It is
stated over an arbitrary trace with a nonempty row list, so it is not vacuous; `holdsVm_gate_true`
witnesses that the same statement fails for the unhardened descriptor.

The converse (`Satisfied2 d → Satisfied2 (hardenLastRow d)`) is FALSE and is not claimed — that is
the whole point. Honest completeness is a fact about the PRODUCER (the measured "zero violated gate
bodies on all 64 rows"), not a theorem about arbitrary traces.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.LastRowFrameHardening

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Circuit.DescriptorIR2

/-! ## §1 — Lifting a one-row body onto the two-row window -/

/-- Read a one-row `EmittedExpr` as a `WindowExpr` over the row window: `var c ↦ loc c`, everything
else structural. The `WindowExpr` doc calls this out as the intended embedding ("a strict
generalization — `EmittedExpr.var c` is `WindowExpr.loc c`"); this is that map, named. -/
def WindowExpr.ofLocal : EmittedExpr → WindowExpr
  | .var c     => .loc c
  | .const k   => .const k
  | .add a b   => .add (ofLocal a) (ofLocal b)
  | .mul a b   => .mul (ofLocal a) (ofLocal b)

/-- **The lift is value-preserving.** The lifted body evaluates on a row window to exactly what the
original body evaluates on that window's LOCAL row — so hardening changes the DOMAIN a body is
asserted on and nothing about the polynomial. -/
@[simp] theorem ofLocal_eval (env : VmRowEnv) (e : EmittedExpr) :
    (WindowExpr.ofLocal e).eval env = e.eval env.loc := by
  induction e with
  | var c => rfl
  | const k => rfl
  | add a b ha hb => simp [WindowExpr.ofLocal, WindowExpr.eval, EmittedExpr.eval, ha, hb]
  | mul a b ha hb => simp [WindowExpr.ofLocal, WindowExpr.eval, EmittedExpr.eval, ha, hb]

/-! ## §2 — The constraint-level and descriptor-level transform -/

/-- Re-lower one constraint: a `.base (.gate b)` becomes the WHOLE-domain `windowGate` carrying the
same body; every other kind is returned untouched (identity on `.transition`, the boundary/PI forms,
lookups, and all four bus kinds). -/
def hardenConstraint : VmConstraint2 → VmConstraint2
  | .base (.gate b) => .windowGate { body := WindowExpr.ofLocal b, onTransition := false }
  | c => c

/-- **The repair.** Every row-local `gate` lifted off the transition domain; geometry, PI layout,
tables, hash sites, ranges and constraint ORDER untouched. -/
def hardenLastRow (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints.map hardenConstraint }

/-! ### §2.1 — The geometry is untouched (the flag-day's blast radius, stated) -/

@[simp] theorem hardenLastRow_name (d : EffectVmDescriptor2) :
    (hardenLastRow d).name = d.name := rfl
@[simp] theorem hardenLastRow_traceWidth (d : EffectVmDescriptor2) :
    (hardenLastRow d).traceWidth = d.traceWidth := rfl
@[simp] theorem hardenLastRow_piCount (d : EffectVmDescriptor2) :
    (hardenLastRow d).piCount = d.piCount := rfl
@[simp] theorem hardenLastRow_tables (d : EffectVmDescriptor2) :
    (hardenLastRow d).tables = d.tables := rfl
@[simp] theorem hardenLastRow_hashSites (d : EffectVmDescriptor2) :
    (hardenLastRow d).hashSites = d.hashSites := rfl
@[simp] theorem hardenLastRow_ranges (d : EffectVmDescriptor2) :
    (hardenLastRow d).ranges = d.ranges := rfl
@[simp] theorem hardenLastRow_constraints_length (d : EffectVmDescriptor2) :
    (hardenLastRow d).constraints.length = d.constraints.length := by
  simp [hardenLastRow]

/-- Hardening leaves every BUS constraint in place, so the gathered memory log is unchanged. -/
@[simp] theorem hardenLastRow_memOpsOf (d : EffectVmDescriptor2) :
    memOpsOf (hardenLastRow d) = memOpsOf d := by
  simp only [memOpsOf, hardenLastRow, List.filterMap_map]
  refine List.filterMap_congr ?_
  intro c _
  cases c with
  | base b => cases b <;> rfl
  | _ => rfl

@[simp] theorem hardenLastRow_mapOpsOf (d : EffectVmDescriptor2) :
    mapOpsOf (hardenLastRow d) = mapOpsOf d := by
  simp only [mapOpsOf, hardenLastRow, List.filterMap_map]
  refine List.filterMap_congr ?_
  intro c _
  cases c with
  | base b => cases b <;> rfl
  | _ => rfl

@[simp] theorem hardenLastRow_umemOpsOf (d : EffectVmDescriptor2) :
    umemOpsOf (hardenLastRow d) = umemOpsOf d := by
  simp only [umemOpsOf, hardenLastRow, List.filterMap_map]
  refine List.filterMap_congr ?_
  intro c _
  cases c with
  | base b => cases b <;> rfl
  | _ => rfl

@[simp] theorem hardenLastRow_memLog (d : EffectVmDescriptor2) (t : VmTrace) :
    memLog (hardenLastRow d) t = memLog d t := by
  simp [memLog]

@[simp] theorem hardenLastRow_mapLog (d : EffectVmDescriptor2) (t : VmTrace) :
    mapLog (hardenLastRow d) t = mapLog d t := by
  simp [mapLog]

/-! ## §3 — The refinement: hardening only ever REFUSES more -/

/-- One constraint's hardened denotation implies its original denotation, on EVERY row.

On an active row (`isLast = false`) the two are the same equation, carried by `ofLocal_eval`. On the
LAST row the original is `True`, so the implication is immediate — and it is the hardened side that
carries content there. -/
theorem holdsAt_of_hardenConstraint (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (c : VmConstraint2) :
    (hardenConstraint c).holdsAt hash tf env isFirst isLast →
      c.holdsAt hash tf env isFirst isLast := by
  cases c with
  | base b =>
      cases b with
      | gate body =>
          intro h
          cases isLast with
          | true => exact trivial
          | false =>
              simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using
                (by simpa [hardenConstraint, VmConstraint2.holdsAt, WindowConstraint.holdsAt]
                      using h)
      | transition hi lo => exact id
      | boundary r b => exact id
      | piBinding r c k => exact id
  | lookup l => exact id
  | memOp m => exact id
  | mapOp m => exact id
  | umemOp m => exact id
  | proofBind m => exact id
  | windowGate w => exact id

/-- **THE REFINEMENT.** A witness satisfying the HARDENED descriptor satisfies the original one, so
every theorem already proved about a member still describes the hardened member's accepted
witnesses — the existing keystone chain re-connects through this arrow.

The converse is FALSE, which is the entire point of the file. -/
theorem satisfied2_of_hardened {hash : List ℤ → ℤ} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (hardenLastRow d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t where
  rowConstraints := by
    intro i hi c hc
    refine holdsAt_of_hardenConstraint hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) c ?_
    exact h.rowConstraints i hi (hardenConstraint c) (by
      simpa [hardenLastRow] using List.mem_map_of_mem (f := hardenConstraint) hc)
  rowHashes := by simpa [hardenLastRow] using h.rowHashes
  rowRanges := by simpa [hardenLastRow] using h.rowRanges
  memAddrsNodup := h.memAddrsNodup
  memClosed := by simpa using h.memClosed
  memDisciplined := by simpa using h.memDisciplined
  memBalanced := by simpa using h.memBalanced
  memTableFaithful := by simpa using h.memTableFaithful
  mapTableFaithful := by simpa using h.mapTableFaithful

/-! ## §4 — The content: the last row now BINDS -/

/-- **THE THING THAT WAS FALSE BEFORE.** Under `Satisfied2` of the hardened descriptor, every
`gate` body the original descriptor declares VANISHES on the LAST row of the trace.

For the UNHARDENED descriptor the corresponding statement is not merely unproved, it is refuted by
`EffectVmEmit.holdsVm_gate_true` — `holdsVm env isFirst true (.gate body)` reduces to `True`, so
`Satisfied2 hash d` constrains that row's cells not at all. This is the last-row anchor forge, in
Lean. -/
theorem hardened_gate_binds_on_last_row {hash : List ℤ → ℤ} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (hardenLastRow d) minit mfin maddrs t)
    (hne : 0 < t.rows.length)
    {body : EmittedExpr} (hmem : VmConstraint2.base (.gate body) ∈ d.constraints) :
    body.eval (envAt t (t.rows.length - 1)).loc ≡ 0 [ZMOD 2013265921] := by
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hne (by decide)
  have hc : hardenConstraint (VmConstraint2.base (.gate body)) ∈ (hardenLastRow d).constraints := by
    simpa [hardenLastRow] using List.mem_map_of_mem (f := hardenConstraint) hmem
  have := h.rowConstraints (t.rows.length - 1) hlt _ hc
  simpa [hardenConstraint, VmConstraint2.holdsAt, WindowConstraint.holdsAt] using this

/-- The same fact, said without a trace: the hardened form of a `gate` is NOT vacuous on the last
row — its denotation there is the body equation, whereas the unhardened form's is `True`. -/
theorem hardened_gate_holdsAt_last (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst : Bool) (body : EmittedExpr) :
    (hardenConstraint (.base (.gate body))).holdsAt hash tf env isFirst true
      = (body.eval env.loc ≡ 0 [ZMOD 2013265921]) := by
  simp [hardenConstraint, VmConstraint2.holdsAt, WindowConstraint.holdsAt]

/-- …and the unhardened one IS vacuous there. Stated beside it so the delta is readable in one
place rather than inferred from two files. -/
theorem unhardened_gate_holdsAt_last (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst : Bool) (body : EmittedExpr) :
    (VmConstraint2.base (.gate body)).holdsAt hash tf env isFirst true = True := rfl

/-- On an ACTIVE row nothing changed: hardened and unhardened denote the same equation, so the
repair is invisible to every row the transition domain already covered. -/
theorem hardened_gate_holdsAt_active (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst : Bool) (body : EmittedExpr) :
    (hardenConstraint (.base (.gate body))).holdsAt hash tf env isFirst false
      = (VmConstraint2.base (.gate body)).holdsAt hash tf env isFirst false := by
  simp [hardenConstraint, VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt]

/-! ## §5 — The transform LANDED (decidable, on a real shape)

A `#guard` that hardening is not the identity and not a no-op: after it, NO `.base (.gate _)`
survives, and the count of whole-domain window gates equals the gate count that went in. Run on a
small synthetic descriptor here; the deployed members are checked by the emit itself (the probes
call `hardenLastRow` on every one of the 57, and the Rust-side census
`deployed_members_have_no_last_row_algebra` is the wire-level tooth). -/

private def sample : EffectVmDescriptor2 :=
  { name := "sample", traceWidth := 4, piCount := 1
    tables := [], hashSites := [], ranges := []
    constraints :=
      [ .base (.gate (.add (.var 0) (.mul (.const (-1)) (.var 1))))
      , .base (.transition 0 0)
      , .base (.piBinding .last 2 0)
      , .base (.gate (.var 3)) ] }

private def gateCount (d : EffectVmDescriptor2) : Nat :=
  (d.constraints.filter (fun c => match c with | .base (.gate _) => true | _ => false)).length

private def wholeDomainWindowCount (d : EffectVmDescriptor2) : Nat :=
  (d.constraints.filter
    (fun c => match c with | .windowGate w => !w.onTransition | _ => false)).length

#guard gateCount sample == 2
#guard gateCount (hardenLastRow sample) == 0
#guard wholeDomainWindowCount sample == 0
#guard wholeDomainWindowCount (hardenLastRow sample) == 2
#guard (hardenLastRow sample).constraints.length == sample.constraints.length
#guard (hardenLastRow sample).traceWidth == sample.traceWidth
#guard (hardenLastRow sample).piCount == sample.piCount

end Dregg2.Circuit.Emit.LastRowFrameHardening
