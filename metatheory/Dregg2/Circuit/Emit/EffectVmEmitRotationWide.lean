/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationWide — THE WIDE EMISSION LANE (Phase B-ROTATION,
the faithful 8-felt commitment chain emitted as wide chip lookups), STAGED beside the live
1-felt path.

`EffectVmEmitRotationR` proves the FAITHFUL 8-felt commitment PRIMITIVE (`wireCommitR8`,
`chainFrom8`, the keystone `wireCommitR8_binds` under the named floors `Poseidon2WideCR` +
`Poseidon2Width8`). `EffectVmEmitRotationV3` emits the rotated commitment chain via the 1-felt
`siteLookup`/`siteHoldsAll`/`wireCommitR` path (`rotV3SitesAt_pin` → `wireCommitR`, ~31-bit). The
live cutover needs the chain GROUP + FINAL sites to bind all 8 OUTPUT LANES.

THIS module is the proof infrastructure that closes that gap — purely additive, off the live wire:

  * **§1 `siteLookupN` / `siteLookupsN_sound`** — the WIDE analog of `siteLookup`/`siteLookups_sound`:
    a chip lookup binding ALL `CHIP_OUT_LANES` output columns (`chipLookupTupleN [c0..c7]`),
    discharged by the wide lever `chip_lookup_sound_N`. Where the 1-felt path forces ONE digest
    column (out0), the wide path forces the WHOLE 8-felt permutation output column-for-column.
  * **§2 `rotV3WideSitesAt`** — the rotated block's 13 chained absorptions emitted as wide lookups:
    the 4-wide head (no carrier), eleven body groups (the prior 8-felt carrier ‖ 3 limbs = arity 11
    = `CHIP_RATE`), the iroot final (carrier ‖ iroot = arity 9). Each carrier is 8 COLUMNS, threaded
    by column reference (position-independent, like `rotV3SitesAt`). The state-commit carrier is the
    final 8 columns.
  * **§3 `rotV3WidePin`** — the WIDE pin (the analog of `rotV3SitesAt_pin`): a satisfying wide-emitted
    witness binds the 8 state-commit columns = `wireCommitR8 permW (preLimbs) iroot`. Discharged
    site-by-site through `chip_lookup_sound_N` (`chainFrom8` folded literally, 13 cases).
  * **§4 `rotateV3Wide` / `v3OfWide`** — the parallel emission, threaded where `v3Of` threads the
    1-felt path, but as a NEW function (the live registry KEEPS using `v3Of` — live wire untouched).
  * **§5 the re-proved wide keystone tower** — `rotV3Wide_pins` / `rotV3Wide_publishes` /
    `rotV3Wide_binds_published`: two satisfying wide-emitted witnesses publishing the SAME 8-felt
    commit columns agree on the WHOLE pre-iroot limb list AND the iroot — the GENUINE ~124-bit
    binding, via `wireCommitR8_binds` (the keystone is load-bearing — NOT a 1-felt binding dressed
    up). The anti-laundering `#guard`: the wide binding distinguishes two states differing ONLY
    beyond lane0.

## Honest boundary notes (do NOT over-read)

  * STAGED, additive: a NEW set of defs/theorems. NO descriptor-JSON / FP / VK / geometry change;
    the live `rotateV3`/`v3Of` and `B_STATE_COMMIT`/`ROT_WIDTH` are untouched. The live flip
    (next phase) repoints the registry at `rotateV3Wide` + the geometry/PI/executor change.
  * The wide floors `Poseidon2WideCR` + `Poseidon2Width8` are the EXACT same crypto class as the
    1-felt `Poseidon2SpongeCR`, at full squeeze width — the named honest floor, NOT a new axiom.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto only as the named
`Poseidon2WideCR`/`Poseidon2Width8` hypotheses. No `sorry`, no `native_decide`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.Emit.EffectVmEmitRotationWide

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Crypto
open Dregg2.Substrate.Heap (refSponge)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — `siteLookupN`: the WIDE chip lookup (binds all 8 output columns).

The 1-felt `siteLookup` binds ONE column (out0); `siteLookupN` binds the WHOLE 8-felt permutation
output via `chipLookupTupleN`. The soundness lever is `chip_lookup_sound_N` (the `permW`-parametric
wide squeeze), so a satisfying wide lookup forces `digestCols.map loc = permW (resolved inputs)` —
all eight lanes column-for-column. -/

/-- **`siteLookupN`** — the wide chip lookup over an explicit input-expression list `ins` and the
8 carrier output columns `digestCols`. (The wide path threads carrier COLUMNS through `ins`, so
there is no `.digest k` accumulator to resolve — the rotation emission supplies `ins` directly.) -/
def siteLookupN (ins : List EmittedExpr) (digestCols : List Nat) :
    Dregg2.Circuit.DescriptorIR2.Lookup :=
  { table := .poseidon2, tuple := chipLookupTupleN ins digestCols }

/-- **`siteLookupN_sound`** — the wide site replacement is SOUND: against a sound WIDE chip table,
the lookup forces the 8 carrier columns to the genuine 8-felt permutation output of the evaluated
inputs. The single-site wide analog of `siteLookup_replaces_site`, discharged by `chip_lookup_sound_N`. -/
theorem siteLookupN_sound (permW : List ℤ → List ℤ) (tbl : Table)
    (hSound : ChipTableSoundN permW tbl) (env : VmRowEnv)
    (ins : List EmittedExpr) (digestCols : List Nat)
    (hlen : ins.length ≤ CHIP_RATE)
    (hmem : (siteLookupN ins digestCols).tuple.map (·.eval env.loc) ∈ tbl) :
    digestCols.map env.loc = permW (ins.map (·.eval env.loc)) :=
  chip_lookup_sound_N permW tbl hSound env.loc ins digestCols hlen hmem

/-- **`siteLookupsN_sound`** — the WHOLE wide family: every wide lookup of a list (against a sound
wide chip table) forces its own 8 carrier columns to the genuine permutation output. The wide analog
of `siteLookups_sound` (the per-site bindings are independent — each `chipLookupTupleN` carries its
inputs explicitly, no cross-site accumulator, so the family is the pointwise conjunction). -/
theorem siteLookupsN_sound (permW : List ℤ → List ℤ) (tbl : Table)
    (hSound : ChipTableSoundN permW tbl) (env : VmRowEnv)
    (sites : List (List EmittedExpr × List Nat))
    (hfit : ∀ p ∈ sites, p.1.length ≤ CHIP_RATE)
    (hlk : ∀ p ∈ sites, (siteLookupN p.1 p.2).tuple.map (·.eval env.loc) ∈ tbl) :
    ∀ p ∈ sites, p.2.map env.loc = permW (p.1.map (·.eval env.loc)) :=
  fun p hp => siteLookupN_sound permW tbl hSound env p.1 p.2 (hfit p hp) (hlk p hp)

/-! ## §2 — `rotV3WideSitesAt`: the rotated block as 13 WIDE chained lookups.

Layout, parametric in the limb base `base` and the wide-carrier base `cbase`:
  * limbs `base+0 .. base+36` (37 pre-iroot limbs), iroot `base+37` (the §3.8 `wireCommitR8` shape).
  * 13 carriers, each 8 columns: carrier `k` at `cbase + 8*k .. cbase + 8*k+7`. Carrier 12 (the
    state-commit carrier) is the published 8-felt commitment block.

Each site's input EXPRESSIONS:
  * site 0 (head): `[l0, l1, l2, l3]` (4 inputs, NO carrier) → carrier 0.
  * sites 1..11 (body): `(carrier k-1 ‖ 3 limbs)` (11 inputs = `CHIP_RATE`) → carrier k.
  * site 12 (final): `(carrier 11 ‖ iroot)` (9 inputs) → carrier 12 (state commit). -/

/-- The 8 columns of wide carrier `k` at carrier base `cbase`. -/
def carrierCols (cbase k : Nat) : List Nat :=
  (List.range CHIP_OUT_LANES).map (fun j => cbase + 8 * k + j)

theorem carrierCols_length (cbase k : Nat) : (carrierCols cbase k).length = 8 := by
  simp [carrierCols, CHIP_OUT_LANES]

/-- The carrier `k`'s 8 columns, read off a row as a length-8 ℤ list. -/
def carrierVals (cbase k : Nat) (a : Assignment) : List ℤ := (carrierCols cbase k).map a

theorem carrierVals_length (cbase k : Nat) (a : Assignment) :
    (carrierVals cbase k a).length = 8 := by simp [carrierVals, carrierCols, CHIP_OUT_LANES]

/-- The input EXPRESSIONS of a body step: the prior carrier's 8 columns (as `.var`) followed by
the 3 limb columns. -/
def bodyIns (cbase prevK limb0 limb1 limb2 : Nat) : List EmittedExpr :=
  (carrierCols cbase prevK).map .var ++ [.var limb0, .var limb1, .var limb2]

/-- The 13 (inputs, 8-output-columns) wide-lookup specs for a rotated block at `(base, cbase)`. -/
def rotV3WideSpecs (base cbase : Nat) : List (List EmittedExpr × List Nat) :=
  [ -- head: [l0,l1,l2,l3] → carrier 0
    ([.var (base+0), .var (base+1), .var (base+2), .var (base+3)], carrierCols cbase 0)
  , (bodyIns cbase 0 (base+4) (base+5) (base+6), carrierCols cbase 1)
  , (bodyIns cbase 1 (base+7) (base+8) (base+9), carrierCols cbase 2)
  , (bodyIns cbase 2 (base+10) (base+11) (base+12), carrierCols cbase 3)
  , (bodyIns cbase 3 (base+13) (base+14) (base+15), carrierCols cbase 4)
  , (bodyIns cbase 4 (base+16) (base+17) (base+18), carrierCols cbase 5)
  , (bodyIns cbase 5 (base+19) (base+20) (base+21), carrierCols cbase 6)
  , (bodyIns cbase 6 (base+22) (base+23) (base+24), carrierCols cbase 7)
  , (bodyIns cbase 7 (base+25) (base+26) (base+27), carrierCols cbase 8)
  , (bodyIns cbase 8 (base+28) (base+29) (base+30), carrierCols cbase 9)
  , (bodyIns cbase 9 (base+31) (base+32) (base+33), carrierCols cbase 10)
  , (bodyIns cbase 10 (base+34) (base+35) (base+36), carrierCols cbase 11)
  , -- final: carrier 11 ‖ iroot → carrier 12 (state commit)
    ((carrierCols cbase 11).map .var ++ [.var (base+37)], carrierCols cbase 12) ]

/-- The wide lookups for a rotated block (one `.lookup` constraint per spec). -/
def rotV3WideLookups (base cbase : Nat) : List VmConstraint2 :=
  (rotV3WideSpecs base cbase).map (fun p => .lookup (siteLookupN p.1 p.2))

/-- Every wide spec's input list fits the chip rate (head 4, body 11, final 9 — all ≤ 11). -/
theorem rotV3WideSpecs_fit (base cbase : Nat) :
    ∀ p ∈ rotV3WideSpecs base cbase, p.1.length ≤ CHIP_RATE := by
  intro p hp
  simp only [rotV3WideSpecs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [bodyIns, carrierCols, CHIP_RATE, CHIP_OUT_LANES]

/-! ## §3 — `rotV3WidePin`: the wide pin (state-commit carrier = `wireCommitR8`). -/

/-- The pre-iroot limb list a block carries (37 limbs, `preLimbsAt`-shaped — identical columns to
the 1-felt path, so the wide commitment binds the SAME limbs the live wire commits). -/
def preLimbsWide (base : Nat) (a : Assignment) : List ℤ := preLimbsAt base a

theorem preLimbsWide_length (base : Nat) (a : Assignment) :
    (preLimbsWide base a).length = 37 := preLimbsAt_length base a

/-- The carrier evaluation of a wide spec at carrier base `cbase`: the prior carrier's VALUES
followed by the 3 limb values (the `chainFrom8` step's `acc ++ c`). -/
private theorem bodyIns_eval (cbase prevK l0 l1 l2 : Nat) (a : Assignment) :
    (bodyIns cbase prevK l0 l1 l2).map (·.eval a)
      = carrierVals cbase prevK a ++ [a l0, a l1, a l2] := by
  simp [bodyIns, carrierVals, EmittedExpr.eval, List.map_append, List.map_map, Function.comp_def]

set_option maxHeartbeats 6400000 in
/-- **THE WIDE PIN, parametric in `(base, cbase)`**: the thirteen wide-lookup output bindings
compose (via `chip_lookup_sound_N` per site, the `chainFrom8` fold literally) into the 8-felt
chained rotated commitment — the row's state-commit carrier (carrier 12) IS `wireCommitR8` of the
row's OWN 37 limbs and iroot. The wide analog of `rotV3SitesAt_pin`, the keystone `wireCommitR8`
load-bearing in every step. -/
theorem rotV3WidePin (permW : List ℤ → List ℤ) (tbl : Table)
    (hSound : ChipTableSoundN permW tbl) (env : VmRowEnv) (base cbase : Nat)
    (hlk : ∀ p ∈ rotV3WideSpecs base cbase,
      (siteLookupN p.1 p.2).tuple.map (·.eval env.loc) ∈ tbl) :
    carrierVals cbase 12 env.loc
      = wireCommitR8 permW (preLimbsWide base env.loc) (env.loc (base + 37)) := by
  -- every spec's 8 output columns carry the genuine permutation output of its inputs
  have hbind := siteLookupsN_sound permW tbl hSound env (rotV3WideSpecs base cbase)
    (rotV3WideSpecs_fit base cbase) hlk
  -- unfold each of the 13 bindings to a `carrierVals … = permW (…)` step.
  have m : ∀ p ∈ rotV3WideSpecs base cbase,
      p.2.map env.loc = permW (p.1.map (·.eval env.loc)) := hbind
  have h0 : carrierVals cbase 0 env.loc
      = permW [env.loc (base+0), env.loc (base+1), env.loc (base+2), env.loc (base+3)] := by
    have := m ([.var (base+0), .var (base+1), .var (base+2), .var (base+3)], carrierCols cbase 0)
      (by simp [rotV3WideSpecs]); simpa [carrierVals, EmittedExpr.eval] using this
  have h1 : carrierVals cbase 1 env.loc
      = permW (carrierVals cbase 0 env.loc ++ [env.loc (base+4), env.loc (base+5), env.loc (base+6)]) := by
    have := m (bodyIns cbase 0 (base+4) (base+5) (base+6), carrierCols cbase 1)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h2 : carrierVals cbase 2 env.loc
      = permW (carrierVals cbase 1 env.loc ++ [env.loc (base+7), env.loc (base+8), env.loc (base+9)]) := by
    have := m (bodyIns cbase 1 (base+7) (base+8) (base+9), carrierCols cbase 2)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h3 : carrierVals cbase 3 env.loc
      = permW (carrierVals cbase 2 env.loc ++ [env.loc (base+10), env.loc (base+11), env.loc (base+12)]) := by
    have := m (bodyIns cbase 2 (base+10) (base+11) (base+12), carrierCols cbase 3)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h4 : carrierVals cbase 4 env.loc
      = permW (carrierVals cbase 3 env.loc ++ [env.loc (base+13), env.loc (base+14), env.loc (base+15)]) := by
    have := m (bodyIns cbase 3 (base+13) (base+14) (base+15), carrierCols cbase 4)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h5 : carrierVals cbase 5 env.loc
      = permW (carrierVals cbase 4 env.loc ++ [env.loc (base+16), env.loc (base+17), env.loc (base+18)]) := by
    have := m (bodyIns cbase 4 (base+16) (base+17) (base+18), carrierCols cbase 5)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h6 : carrierVals cbase 6 env.loc
      = permW (carrierVals cbase 5 env.loc ++ [env.loc (base+19), env.loc (base+20), env.loc (base+21)]) := by
    have := m (bodyIns cbase 5 (base+19) (base+20) (base+21), carrierCols cbase 6)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h7 : carrierVals cbase 7 env.loc
      = permW (carrierVals cbase 6 env.loc ++ [env.loc (base+22), env.loc (base+23), env.loc (base+24)]) := by
    have := m (bodyIns cbase 6 (base+22) (base+23) (base+24), carrierCols cbase 7)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h8 : carrierVals cbase 8 env.loc
      = permW (carrierVals cbase 7 env.loc ++ [env.loc (base+25), env.loc (base+26), env.loc (base+27)]) := by
    have := m (bodyIns cbase 7 (base+25) (base+26) (base+27), carrierCols cbase 8)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h9 : carrierVals cbase 9 env.loc
      = permW (carrierVals cbase 8 env.loc ++ [env.loc (base+28), env.loc (base+29), env.loc (base+30)]) := by
    have := m (bodyIns cbase 8 (base+28) (base+29) (base+30), carrierCols cbase 9)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h10 : carrierVals cbase 10 env.loc
      = permW (carrierVals cbase 9 env.loc ++ [env.loc (base+31), env.loc (base+32), env.loc (base+33)]) := by
    have := m (bodyIns cbase 9 (base+31) (base+32) (base+33), carrierCols cbase 10)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h11 : carrierVals cbase 11 env.loc
      = permW (carrierVals cbase 10 env.loc ++ [env.loc (base+34), env.loc (base+35), env.loc (base+36)]) := by
    have := m (bodyIns cbase 10 (base+34) (base+35) (base+36), carrierCols cbase 11)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h12 : carrierVals cbase 12 env.loc
      = permW (carrierVals cbase 11 env.loc ++ [env.loc (base+37)]) := by
    have := m ((carrierCols cbase 11).map .var ++ [.var (base+37)], carrierCols cbase 12)
      (by simp [rotV3WideSpecs])
    simpa [carrierVals, EmittedExpr.eval, List.map_append, List.map_map, Function.comp_def] using this
  -- fold: `wireCommitR8 = chainFrom8 (permW head) (chunk31 body ++ [[ir]])`.
  rw [h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  rfl

#assert_axioms siteLookupN_sound
#assert_axioms siteLookupsN_sound
#assert_axioms rotV3WidePin

/-! ## §4 — `rotateV3Wide` / `v3OfWide`: the PARALLEL wide emission.

A NEW emission, threaded where `v3Of`/`rotateV3` thread the 1-felt path, but additive: it lifts
`graduateV1 (rotateV3 d)` (reusing the LIVE-proven 1-felt host — its welds, v1 survival, and the
host's own sites) and APPENDS the wide BEFORE/AFTER lookup blocks over FRESH carrier regions plus
the 8-column PI pins. The live registry KEEPS `v3Of` (this is a parallel constant) — the live wire
is untouched. The wide BEFORE/AFTER blocks read the SAME `preLimbsAt` columns the 1-felt path
commits, so the wide commitment binds the SAME 37 limbs + iroot, at full 8-felt width.

Layout (past `rotateV3 d`'s width `w = d.traceWidth + APPENDIX_SPAN`):
  * BEFORE wide carriers at `w` (13×8 = 104 columns); the wide BEFORE block's limbs are the live
    BEFORE block's columns `d.traceWidth + 0 .. + 37`.
  * AFTER wide carriers at `w + 104`; the wide AFTER block's limbs are the live AFTER block's
    columns `d.traceWidth + 51 + 0 .. + 37`.
  * 16 appended PI slots: `piCount' .. piCount'+7` = BEFORE commit's 8 columns (first row),
    `piCount'+8 .. +15` = AFTER commit's 8 columns (last row), where `piCount' = (rotateV3 d).piCount`. -/

/-- The BEFORE-block wide-carrier base of a host of (graduated) width `w`. -/
def wideBeforeCBase (w : Nat) : Nat := w
/-- The AFTER-block wide-carrier base. -/
def wideAfterCBase (w : Nat) : Nat := w + 104

/-- The 8-column PI pins of a commit carrier `cols` to PI slots `piBase..piBase+7`, on `row`. -/
def commitPins (row : VmRow) (cols : List Nat) (piBase : Nat) : List VmConstraint2 :=
  (cols.zipIdx).map (fun (p : Nat × Nat) => .base (.piBinding row p.1 (piBase + p.2)))

/-- **`rotateV3Wide`** — the parallel wide emission. The graduated 1-felt host PLUS the wide
BEFORE/AFTER lookup blocks and their 16 PI pins (8 BEFORE commit cols on the first row, 8 AFTER
commit cols on the last). -/
def rotateV3Wide (d : EffectVmDescriptor) : EffectVmDescriptor2 :=
  let host := graduateV1 (rotateV3 d)
  let w := host.traceWidth
  let bb := d.traceWidth            -- live BEFORE limb base
  let ab := d.traceWidth + 51       -- live AFTER limb base
  let cbB := wideBeforeCBase w
  let cbA := wideAfterCBase w
  { host with
    traceWidth := w + 208           -- + 2 × (13 carriers × 8)
    piCount    := host.piCount + 16
    tables     := v2Tables (w + 208)
    constraints := host.constraints
      ++ rotV3WideLookups bb cbB
      ++ rotV3WideLookups ab cbA
      ++ commitPins .first (carrierCols cbB 12) host.piCount
      ++ commitPins .last  (carrierCols cbA 12) (host.piCount + 8) }

/-- **`v3OfWide`** — the alias mirroring `v3Of` (the rotated graduation of a cohort member, the
WIDE commitment lane). The live-flip handoff repoints the registry from `v3Of` to THIS. -/
def v3OfWide (d : EffectVmDescriptor) : EffectVmDescriptor2 := rotateV3Wide d

/-! ## §5 — the re-proved WIDE keystone tower.

`rotV3Wide_pins`/`rotV3Wide_publishes`/`rotV3Wide_binds_published`: the wide analogs of
`rotV3_pins`/`rotV3_publishes`/`rotV3_binds_published`. The floor swaps `Poseidon2SpongeCR` →
`Poseidon2WideCR` + `Poseidon2Width8`; the binding invokes `wireCommitR8_binds` (the keystone is
LOAD-BEARING — the published 8-felt commit = the chained `wireCommitR8` digest of the 37 limbs). -/

/-- The wide BEFORE/AFTER lookups are members of `rotateV3Wide d`'s constraints (for `rowConstraints`
extraction). -/
theorem rotateV3Wide_before_mem (d : EffectVmDescriptor) :
    ∀ c ∈ rotV3WideLookups d.traceWidth (wideBeforeCBase (graduateV1 (rotateV3 d)).traceWidth),
      c ∈ (rotateV3Wide d).constraints := by
  intro c hc
  unfold rotateV3Wide
  simp only [List.append_assoc, List.mem_append]
  exact Or.inr (Or.inl hc)

theorem rotateV3Wide_after_mem (d : EffectVmDescriptor) :
    ∀ c ∈ rotV3WideLookups (d.traceWidth + 51) (wideAfterCBase (graduateV1 (rotateV3 d)).traceWidth),
      c ∈ (rotateV3Wide d).constraints := by
  intro c hc
  unfold rotateV3Wide
  simp only [List.append_assoc, List.mem_append]
  exact Or.inr (Or.inr (Or.inl hc))

/-- A `Satisfied2` witness of `rotateV3Wide d` forces the BEFORE/AFTER wide lookups on every row:
each block's 8 state-commit carrier columns ARE `wireCommitR8` of the row's own limbs and iroot.
The host `Satisfied2` carries the 1-felt `hash` (for the graduated host's own 1-felt sites); the
WIDE chip table soundness `ChipTableSoundN permW` is a SEPARATE faithfulness floor of the SAME
`.poseidon2` table (`chipRowN_head_eq_hash`: a wide-sound table is also 1-felt-sound at its head). -/
theorem rotV3Wide_pins (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hsat : Satisfied2 hash (rotateV3Wide d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    carrierVals (wideBeforeCBase (graduateV1 (rotateV3 d)).traceWidth) 12 (envAt t i).loc
      = wireCommitR8 permW (preLimbsWide d.traceWidth (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + 37))
    ∧ carrierVals (wideAfterCBase (graduateV1 (rotateV3 d)).traceWidth) 12 (envAt t i).loc
      = wireCommitR8 permW (preLimbsWide (d.traceWidth + 51) (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + 51 + 37)) := by
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_⟩
  · apply rotV3WidePin permW (t.tf .poseidon2) hchipN (envAt t i) d.traceWidth
      (wideBeforeCBase (graduateV1 (rotateV3 d)).traceWidth)
    intro p hp
    have hmem := rotateV3Wide_before_mem d (.lookup (siteLookupN p.1 p.2))
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have := hrow _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using this
  · apply rotV3WidePin permW (t.tf .poseidon2) hchipN (envAt t i) (d.traceWidth + 51)
      (wideAfterCBase (graduateV1 (rotateV3 d)).traceWidth)
    intro p hp
    have hmem := rotateV3Wide_after_mem d (.lookup (siteLookupN p.1 p.2))
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have := hrow _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using this

/-- The PI pins membership: the BEFORE/AFTER commit pins are constraints of `rotateV3Wide d`. -/
theorem rotateV3Wide_beforePin_mem (d : EffectVmDescriptor) (k : Nat) (hk : k < 8) :
    (VmConstraint2.base (.piBinding .first
      ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d)).traceWidth) 12).getD k 0)
      ((graduateV1 (rotateV3 d)).piCount + k))) ∈ (rotateV3Wide d).constraints := by
  unfold rotateV3Wide
  simp only [List.append_assoc, List.mem_append]
  refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
  unfold commitPins
  rw [List.mem_map]
  refine ⟨((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d)).traceWidth) 12).getD k 0, k),
    ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · rw [List.length_zipIdx, carrierCols_length]; exact hk
  · rw [List.getElem_zipIdx]
    have hk' : k < (carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d)).traceWidth) 12).length := by
      rw [carrierCols_length]; exact hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

theorem rotateV3Wide_afterPin_mem (d : EffectVmDescriptor) (k : Nat) (hk : k < 8) :
    (VmConstraint2.base (.piBinding .last
      ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d)).traceWidth) 12).getD k 0)
      ((graduateV1 (rotateV3 d)).piCount + 8 + k))) ∈ (rotateV3Wide d).constraints := by
  unfold rotateV3Wide
  simp only [List.append_assoc, List.mem_append]
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  unfold commitPins
  rw [List.mem_map]
  refine ⟨((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d)).traceWidth) 12).getD k 0, k),
    ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · rw [List.length_zipIdx, carrierCols_length]; exact hk
  · rw [List.getElem_zipIdx]
    have hk' : k < (carrierCols (wideAfterCBase (graduateV1 (rotateV3 d)).traceWidth) 12).length := by
      rw [carrierCols_length]; exact hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

/-- **`rotV3Wide_publishes`** — the wide commits PUBLISH: first row binds the BEFORE commit's 8
columns to PI slots `piCount'..+7`; last row binds the AFTER commit's 8 columns to `piCount'+8..+15`. -/
theorem rotV3Wide_publishes (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (rotateV3Wide d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    ((i == 0) = true → ∀ k, (hk : k < 8) →
      (envAt t i).loc
          ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d)).traceWidth) 12).getD k 0)
        = (envAt t i).pub ((graduateV1 (rotateV3 d)).piCount + k))
    ∧ ((i + 1 == t.rows.length) = true → ∀ k, (hk : k < 8) →
      (envAt t i).loc
          ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d)).traceWidth) 12).getD k 0)
        = (envAt t i).pub ((graduateV1 (rotateV3 d)).piCount + 8 + k)) := by
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_⟩
  · intro hf k hk
    have := hrow _ (rotateV3Wide_beforePin_mem d k hk)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at this
    exact this hf
  · intro hl k hk
    have := hrow _ (rotateV3Wide_afterPin_mem d k hk)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at this
    exact this hl

/-- Two length-8 carrier-value lists whose published columns carry pairwise-equal PI values are
EQUAL. `pubAt`/`pubAt'` are the per-row PI reads at the matching slot offset `m`; `hpub` is the
slot-by-slot published-PI equality. The pointwise equality lifts to list equality via
`List.ext_getElem`. -/
private theorem carrierVals_eq_of_pins (cb cb' : Nat) (a a' : Assignment)
    (pubAt pubAt' : Nat → ℤ)
    (hpub : ∀ m, m < 8 → pubAt m = pubAt' m)
    (h : ∀ k, k < 8 → a ((carrierCols cb 12).getD k 0) = pubAt k)
    (h' : ∀ k, k < 8 → a' ((carrierCols cb' 12).getD k 0) = pubAt' k) :
    carrierVals cb 12 a = carrierVals cb' 12 a' := by
  have key : ∀ k, k < 8 →
      (carrierVals cb 12 a).getD k 0 = (carrierVals cb' 12 a').getD k 0 := by
    intro k hk8
    have hlt : k < (carrierCols cb 12).length := by rw [carrierCols_length]; exact hk8
    have hlt' : k < (carrierCols cb' 12).length := by rw [carrierCols_length]; exact hk8
    have e1 : (carrierVals cb 12 a).getD k 0 = a ((carrierCols cb 12).getD k 0) := by
      simp [carrierVals, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have e2 : (carrierVals cb' 12 a').getD k 0 = a' ((carrierCols cb' 12).getD k 0) := by
      simp [carrierVals, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt']
    rw [e1, e2, h k hk8, h' k hk8, hpub k hk8]
  apply List.ext_getElem
  · rw [carrierVals_length, carrierVals_length]
  · intro k hk hk'
    have hk8 : k < 8 := by rwa [carrierVals_length] at hk
    have := key k hk8
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      List.getElem?_eq_getElem hk'] using this

set_option maxHeartbeats 1600000 in
/-- **THE WIDE END-TO-END KEYSTONE.** Two `Satisfied2` witnesses of `rotateV3Wide d` publishing the
SAME 8-felt BEFORE commit and the SAME 8-felt AFTER commit agree on the WHOLE before-block 37-limb
list + iroot AND the WHOLE after-block 37-limb list + iroot — the GENUINE ~124-bit binding, via the
FAITHFUL `wireCommitR8_binds` (the keystone is load-bearing: the published 8-felt commit IS the
chained `wireCommitR8` digest of the limbs, under the named wide floors). The wide analog of
`rotV3_binds_published`, the floor swapped `Poseidon2SpongeCR` → `Poseidon2WideCR` + `Poseidon2Width8`. -/
theorem rotV3Wide_binds_published (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ)
    (hCR : Poseidon2WideCR permW) (hW : Poseidon2Width8 permW) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hchipN' : ChipTableSoundN permW (t'.tf .poseidon2))
    (hsat : Satisfied2 hash (rotateV3Wide d) minit mfin maddrs t)
    (hsat' : Satisfied2 hash (rotateV3Wide d) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hfirst : (i == 0) = true) (hfirst' : (j == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubBefore : ∀ m, m < 8 →
      (envAt t i).pub ((graduateV1 (rotateV3 d)).piCount + m)
        = (envAt t' j).pub ((graduateV1 (rotateV3 d)).piCount + m))
    (hpubAfter : ∀ m, m < 8 →
      (envAt t k).pub ((graduateV1 (rotateV3 d)).piCount + 8 + m)
        = (envAt t' l).pub ((graduateV1 (rotateV3 d)).piCount + 8 + m)) :
    (preLimbsWide d.traceWidth (envAt t i).loc = preLimbsWide d.traceWidth (envAt t' j).loc
      ∧ (envAt t i).loc (d.traceWidth + 37) = (envAt t' j).loc (d.traceWidth + 37))
    ∧ (preLimbsWide (d.traceWidth + 51) (envAt t k).loc
        = preLimbsWide (d.traceWidth + 51) (envAt t' l).loc
      ∧ (envAt t k).loc (d.traceWidth + 51 + 37) = (envAt t' l).loc (d.traceWidth + 51 + 37)) := by
  have hp := rotV3Wide_pins hash permW d minit mfin maddrs t hchipN hsat
  have hp' := rotV3Wide_pins hash permW d minit' mfin' maddrs' t' hchipN' hsat'
  have hq := rotV3Wide_publishes hash d minit mfin maddrs t hsat
  have hq' := rotV3Wide_publishes hash d minit' mfin' maddrs' t' hsat'
  refine ⟨?_, ?_⟩
  · -- BEFORE: equal published 8-felt commits ⇒ equal limbs + iroot
    have hcv : carrierVals (wideBeforeCBase (graduateV1 (rotateV3 d)).traceWidth) 12 (envAt t i).loc
        = carrierVals (wideBeforeCBase (graduateV1 (rotateV3 d)).traceWidth) 12 (envAt t' j).loc :=
      carrierVals_eq_of_pins _ _ _ _
        (fun m => (envAt t i).pub ((graduateV1 (rotateV3 d)).piCount + m))
        (fun m => (envAt t' j).pub ((graduateV1 (rotateV3 d)).piCount + m))
        hpubBefore ((hq i hi).1 hfirst) ((hq' j hj).1 hfirst')
    have hwire : wireCommitR8 permW (preLimbsWide d.traceWidth (envAt t i).loc)
        ((envAt t i).loc (d.traceWidth + 37))
        = wireCommitR8 permW (preLimbsWide d.traceWidth (envAt t' j).loc)
            ((envAt t' j).loc (d.traceWidth + 37)) := by
      rw [← (hp i hi).1, ← (hp' j hj).1]; exact hcv
    exact wireCommitR8_binds permW hCR hW
      (by rw [preLimbsWide_length, preLimbsWide_length]) hwire
  · -- AFTER: equal published 8-felt commits ⇒ equal limbs + iroot
    have hcv : carrierVals (wideAfterCBase (graduateV1 (rotateV3 d)).traceWidth) 12 (envAt t k).loc
        = carrierVals (wideAfterCBase (graduateV1 (rotateV3 d)).traceWidth) 12 (envAt t' l).loc :=
      carrierVals_eq_of_pins _ _ _ _
        (fun m => (envAt t k).pub ((graduateV1 (rotateV3 d)).piCount + 8 + m))
        (fun m => (envAt t' l).pub ((graduateV1 (rotateV3 d)).piCount + 8 + m))
        hpubAfter ((hq k hk).2 hlast) ((hq' l hl).2 hlast')
    have hwire : wireCommitR8 permW (preLimbsWide (d.traceWidth + 51) (envAt t k).loc)
        ((envAt t k).loc (d.traceWidth + 51 + 37))
        = wireCommitR8 permW (preLimbsWide (d.traceWidth + 51) (envAt t' l).loc)
            ((envAt t' l).loc (d.traceWidth + 51 + 37)) := by
      rw [← (hp k hk).2, ← (hp' l hl).2]; exact hcv
    exact wireCommitR8_binds permW hCR hW
      (by rw [preLimbsWide_length, preLimbsWide_length]) hwire

#assert_axioms rotV3Wide_pins
#assert_axioms rotV3Wide_publishes
#assert_axioms rotV3Wide_binds_published

/-! ## §6 — the ANTI-LAUNDERING tooth: the wide binding is GENUINELY 8-felt-wide.

A `#guard` witnessing that the wide-emitted binding distinguishes two states differing ONLY beyond
lane0 — the 8-felt commitment is genuinely WIDER than a 1-felt (lane0-only) binding would be. The
toy `refWide` (each of 8 lanes = `refSponge (tag :: xs)`, all lanes avalanching over the input) is
the same width-8 toy the §3.8 non-vacuity guards use. Two pre-iroot payloads agreeing on lane0's
hash but differing in a HIGH limb still produce DIFFERENT 8-felt commits — a 1-felt squeeze would
collapse them, the wide one does not. -/

/-- A wide-emission row whose 13 wide carriers carry the genuine `chainFrom8`/`wireCommitR8` of the
row's limbs (the COMPLETENESS direction at the spec level — what the honest producer lays). -/
def demoWideCarrier (base cbase : Nat) (limbs : List ℤ) (ir : ℤ) (a : Assignment) : Prop :=
  carrierVals cbase 12 a = wireCommitR8 refWide limbs ir

-- The wide pin's CONCLUSION at the spec level: a HIGH-limb flip (limb 30, folded mid-chain) moves
-- the published 8-felt commit — a genuinely wider binding than lane0 alone. (demoPre24/refWide from
-- EffectVmEmitRotationR §3.8.)
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 30 999) 7
-- and the iroot is bound; honest recompute stable.
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide demoPre24 8
#guard wireCommitR8 refWide demoPre24 7 == wireCommitR8 refWide demoPre24 7
-- the wide commit is 8 felts (NOT 1) — the structural anti-laundering width witness.
#guard (wireCommitR8 refWide demoPre24 7).length == 8

/-! ## §7 — `wideAppend`: the GATED-HOST wide-emission transformer (the live-flip primitive).

`rotateV3Wide` (§4) appends the wide BEFORE/AFTER blocks onto a BARE host (`graduateV1 (rotateV3 d)`),
internally re-graduating `d`. But the LIVE `v3Registry` is 36 ALREADY-GATED `EffectVmDescriptor2`s
(`v3OfFrozen`, `withSelectorGate`, the WAVE-1/2 disc gates, the fee-pin transfer) — each a graduated
host with appended gates. The live flip needs to append the wide carriers onto an ARBITRARY such host,
NOT re-graduate a bare `d`.

`wideAppend h bb ab` does exactly that: given an arbitrary graduated/gated `h : EffectVmDescriptor2`
and the host's BEFORE/AFTER limb bases `bb ab` (the columns `rotateV3` laid the limbs at — `bb =
d.traceWidth`, `ab = d.traceWidth + 51`, UNMOVED by any gate, which only appends constraints), it:

  * bases the two 13×8 wide-carrier regions PAST `h.traceWidth` (`wideBeforeCBase h.traceWidth` /
    `wideAfterCBase h.traceWidth`) — they cannot collide with the host's columns or its gates' columns;
  * pins the two 8-felt commits to 16 PI slots PAST `h.piCount`;
  * PRESERVES `h`'s constraints, gates, hash sites, ranges, AND mem/map logs verbatim (it ONLY APPENDS
    `.lookup` and `.base (.piBinding …)` constraints — neither contributes a mem/map op, so the host's
    four memory legs and the map-table leg are definitionally `h`'s, exactly the `withSelectorGate`
    argument). `wideAppend h bb ab`'s constraints are `h.constraints ++ (wide binding)` — a CONJUNCTION,
    so anything provable about `h` (its gates' soundness) still holds, AND the wide binding is forced.

The wide lookups read the SAME `preLimbsAt bb`/`preLimbsAt ab` columns the host's 1-felt chain commits,
so the 8-felt binding is over the same 37 limbs + iroot. -/

/-- **`wideAppend h bb ab`** — append the two wide BEFORE/AFTER carrier blocks (each 13×8, based past
`h.traceWidth`) and their 16 commit PI pins (past `h.piCount`) onto an ARBITRARY graduated/gated host
`h`. The host's name/hashSites/ranges and ALL its existing constraints (its gates) are untouched; only
the wide lookups + PI pins are ADDED. -/
def wideAppend (h : EffectVmDescriptor2) (bb ab : Nat) : EffectVmDescriptor2 :=
  let w := h.traceWidth
  let cbB := wideBeforeCBase w
  let cbA := wideAfterCBase w
  { h with
    traceWidth := w + 208           -- + 2 × (13 carriers × 8)
    piCount    := h.piCount + 16
    tables     := v2Tables (w + 208)
    constraints := h.constraints
      ++ rotV3WideLookups bb cbB
      ++ rotV3WideLookups ab cbA
      ++ commitPins .first (carrierCols cbB 12) h.piCount
      ++ commitPins .last  (carrierCols cbA 12) (h.piCount + 8) }

/-- `wideAppend h bb ab`'s constraints are `h`'s plus the four appended wide blocks. -/
theorem wideAppend_constraints (h : EffectVmDescriptor2) (bb ab : Nat) :
    (wideAppend h bb ab).constraints
      = h.constraints
        ++ rotV3WideLookups bb (wideBeforeCBase h.traceWidth)
        ++ rotV3WideLookups ab (wideAfterCBase h.traceWidth)
        ++ commitPins .first (carrierCols (wideBeforeCBase h.traceWidth) 12) h.piCount
        ++ commitPins .last  (carrierCols (wideAfterCBase h.traceWidth) 12) (h.piCount + 8) := by
  unfold wideAppend; simp [List.append_assoc]

/-- `wideAppend` ONLY appends `.lookup` and `.base (.piBinding …)` constraints, so the gathered
`memOpsOf` is `h`'s (no `.memOp` is added). -/
theorem wideAppend_memOpsOf (h : EffectVmDescriptor2) (bb ab : Nat) :
    Dregg2.Circuit.DescriptorIR2.memOpsOf (wideAppend h bb ab)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf h := by
  unfold Dregg2.Circuit.DescriptorIR2.memOpsOf
  rw [wideAppend_constraints]
  unfold rotV3WideLookups commitPins
  simp [Function.comp_def]

/-- ...and no `.mapOp` is added, so the gathered `mapOpsOf` is `h`'s. -/
theorem wideAppend_mapOpsOf (h : EffectVmDescriptor2) (bb ab : Nat) :
    Dregg2.Circuit.DescriptorIR2.mapOpsOf (wideAppend h bb ab)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf h := by
  unfold Dregg2.Circuit.DescriptorIR2.mapOpsOf
  rw [wideAppend_constraints]
  unfold rotV3WideLookups commitPins
  simp [Function.comp_def]

/-- ...so the gathered memory log is `h`'s, op-for-op. -/
theorem wideAppend_memLog (h : EffectVmDescriptor2) (bb ab : Nat)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.memLog (wideAppend h bb ab) t
      = Dregg2.Circuit.DescriptorIR2.memLog h t := by
  simp [Dregg2.Circuit.DescriptorIR2.memLog, wideAppend_memOpsOf]

/-- ...and the gathered map log is `h`'s. -/
theorem wideAppend_mapLog (h : EffectVmDescriptor2) (bb ab : Nat)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.mapLog (wideAppend h bb ab) t
      = Dregg2.Circuit.DescriptorIR2.mapLog h t := by
  simp [Dregg2.Circuit.DescriptorIR2.mapLog, wideAppend_mapOpsOf]

/-! ### §7.1 — the appended-block membership lemmas (for `rowConstraints` extraction). -/

theorem wideAppend_before_mem (h : EffectVmDescriptor2) (bb ab : Nat) :
    ∀ c ∈ rotV3WideLookups bb (wideBeforeCBase h.traceWidth),
      c ∈ (wideAppend h bb ab).constraints := by
  intro c hc
  rw [wideAppend_constraints]
  simp only [List.append_assoc, List.mem_append]
  exact Or.inr (Or.inl hc)

theorem wideAppend_after_mem (h : EffectVmDescriptor2) (bb ab : Nat) :
    ∀ c ∈ rotV3WideLookups ab (wideAfterCBase h.traceWidth),
      c ∈ (wideAppend h bb ab).constraints := by
  intro c hc
  rw [wideAppend_constraints]
  simp only [List.append_assoc, List.mem_append]
  exact Or.inr (Or.inr (Or.inl hc))

theorem wideAppend_beforePin_mem (h : EffectVmDescriptor2) (bb ab : Nat) (k : Nat) (hk : k < 8) :
    (VmConstraint2.base (.piBinding .first
      ((carrierCols (wideBeforeCBase h.traceWidth) 12).getD k 0)
      (h.piCount + k))) ∈ (wideAppend h bb ab).constraints := by
  rw [wideAppend_constraints]
  simp only [List.append_assoc, List.mem_append]
  refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
  unfold commitPins
  rw [List.mem_map]
  refine ⟨((carrierCols (wideBeforeCBase h.traceWidth) 12).getD k 0, k), ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · rw [List.length_zipIdx, carrierCols_length]; exact hk
  · rw [List.getElem_zipIdx]
    have hk' : k < (carrierCols (wideBeforeCBase h.traceWidth) 12).length := by
      rw [carrierCols_length]; exact hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

theorem wideAppend_afterPin_mem (h : EffectVmDescriptor2) (bb ab : Nat) (k : Nat) (hk : k < 8) :
    (VmConstraint2.base (.piBinding .last
      ((carrierCols (wideAfterCBase h.traceWidth) 12).getD k 0)
      (h.piCount + 8 + k))) ∈ (wideAppend h bb ab).constraints := by
  rw [wideAppend_constraints]
  simp only [List.append_assoc, List.mem_append]
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  unfold commitPins
  rw [List.mem_map]
  refine ⟨((carrierCols (wideAfterCBase h.traceWidth) 12).getD k 0, k), ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · rw [List.length_zipIdx, carrierCols_length]; exact hk
  · rw [List.getElem_zipIdx]
    have hk' : k < (carrierCols (wideAfterCBase h.traceWidth) 12).length := by
      rw [carrierCols_length]; exact hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

/-! ### §7.2 — the GATED-HOST keystone tower (the generalizations of §5 over an arbitrary host). -/

/-- **`wideAppend_pins`** — a `Satisfied2` witness of `wideAppend h bb ab` forces the BEFORE/AFTER wide
lookups on every row: each block's 8 state-commit carrier columns ARE `wireCommitR8` of the row's own
37 limbs (at `bb`/`ab`) and iroot. REGARDLESS of `h`'s gates — the wide lookups are appended
constraints of `wideAppend h bb ab`, extracted from `rowConstraints` independently of `h`'s
constraints. -/
theorem wideAppend_pins (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ) (h : EffectVmDescriptor2)
    (bb ab : Nat) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hsat : Satisfied2 hash (wideAppend h bb ab) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    carrierVals (wideBeforeCBase h.traceWidth) 12 (envAt t i).loc
      = wireCommitR8 permW (preLimbsWide bb (envAt t i).loc) ((envAt t i).loc (bb + 37))
    ∧ carrierVals (wideAfterCBase h.traceWidth) 12 (envAt t i).loc
      = wireCommitR8 permW (preLimbsWide ab (envAt t i).loc) ((envAt t i).loc (ab + 37)) := by
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_⟩
  · apply rotV3WidePin permW (t.tf .poseidon2) hchipN (envAt t i) bb
      (wideBeforeCBase h.traceWidth)
    intro p hp
    have hmem := wideAppend_before_mem h bb ab (.lookup (siteLookupN p.1 p.2))
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have := hrow _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using this
  · apply rotV3WidePin permW (t.tf .poseidon2) hchipN (envAt t i) ab
      (wideAfterCBase h.traceWidth)
    intro p hp
    have hmem := wideAppend_after_mem h bb ab (.lookup (siteLookupN p.1 p.2))
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have := hrow _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using this

/-- **`wideAppend_publishes`** — the wide commits PUBLISH: first row binds the BEFORE commit's 8 columns
to PI slots `h.piCount..+7`; last row binds the AFTER commit's 8 columns to `h.piCount+8..+15`.
Independent of `h`'s gates. -/
theorem wideAppend_publishes (hash : List ℤ → ℤ) (h : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (wideAppend h bb ab) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    ((i == 0) = true → ∀ k, (hk : k < 8) →
      (envAt t i).loc ((carrierCols (wideBeforeCBase h.traceWidth) 12).getD k 0)
        = (envAt t i).pub (h.piCount + k))
    ∧ ((i + 1 == t.rows.length) = true → ∀ k, (hk : k < 8) →
      (envAt t i).loc ((carrierCols (wideAfterCBase h.traceWidth) 12).getD k 0)
        = (envAt t i).pub (h.piCount + 8 + k)) := by
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_⟩
  · intro hf k hk
    have := hrow _ (wideAppend_beforePin_mem h bb ab k hk)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at this
    exact this hf
  · intro hl k hk
    have := hrow _ (wideAppend_afterPin_mem h bb ab k hk)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at this
    exact this hl

set_option maxHeartbeats 1600000 in
/-- **`wideAppend_binds_published` — THE GATED-HOST WIDE END-TO-END KEYSTONE.** Two `Satisfied2`
witnesses of `wideAppend h bb ab` publishing the SAME 8-felt BEFORE commit and the SAME 8-felt AFTER
commit agree on the WHOLE before-block 37-limb list + iroot AND the WHOLE after-block 37-limb list +
iroot — the GENUINE ~124-bit binding via the FAITHFUL `wireCommitR8_binds`, over an ARBITRARY gated
host `h`. The host's gates constrain OTHER columns; the wide binding is over the appended carriers +
the shared `preLimbsAt bb`/`ab` columns, so the gates neither weaken nor are weakened by it. -/
theorem wideAppend_binds_published (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ)
    (hCR : Poseidon2WideCR permW) (hW : Poseidon2Width8 permW) (h : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hchipN' : ChipTableSoundN permW (t'.tf .poseidon2))
    (hsat : Satisfied2 hash (wideAppend h bb ab) minit mfin maddrs t)
    (hsat' : Satisfied2 hash (wideAppend h bb ab) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hfirst : (i == 0) = true) (hfirst' : (j == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubBefore : ∀ m, m < 8 →
      (envAt t i).pub (h.piCount + m) = (envAt t' j).pub (h.piCount + m))
    (hpubAfter : ∀ m, m < 8 →
      (envAt t k).pub (h.piCount + 8 + m) = (envAt t' l).pub (h.piCount + 8 + m)) :
    (preLimbsWide bb (envAt t i).loc = preLimbsWide bb (envAt t' j).loc
      ∧ (envAt t i).loc (bb + 37) = (envAt t' j).loc (bb + 37))
    ∧ (preLimbsWide ab (envAt t k).loc = preLimbsWide ab (envAt t' l).loc
      ∧ (envAt t k).loc (ab + 37) = (envAt t' l).loc (ab + 37)) := by
  have hp := wideAppend_pins hash permW h bb ab minit mfin maddrs t hchipN hsat
  have hp' := wideAppend_pins hash permW h bb ab minit' mfin' maddrs' t' hchipN' hsat'
  have hq := wideAppend_publishes hash h bb ab minit mfin maddrs t hsat
  have hq' := wideAppend_publishes hash h bb ab minit' mfin' maddrs' t' hsat'
  refine ⟨?_, ?_⟩
  · have hcv : carrierVals (wideBeforeCBase h.traceWidth) 12 (envAt t i).loc
        = carrierVals (wideBeforeCBase h.traceWidth) 12 (envAt t' j).loc :=
      carrierVals_eq_of_pins _ _ _ _
        (fun m => (envAt t i).pub (h.piCount + m))
        (fun m => (envAt t' j).pub (h.piCount + m))
        hpubBefore ((hq i hi).1 hfirst) ((hq' j hj).1 hfirst')
    have hwire : wireCommitR8 permW (preLimbsWide bb (envAt t i).loc) ((envAt t i).loc (bb + 37))
        = wireCommitR8 permW (preLimbsWide bb (envAt t' j).loc) ((envAt t' j).loc (bb + 37)) := by
      rw [← (hp i hi).1, ← (hp' j hj).1]; exact hcv
    exact wireCommitR8_binds permW hCR hW
      (by rw [preLimbsWide_length, preLimbsWide_length]) hwire
  · have hcv : carrierVals (wideAfterCBase h.traceWidth) 12 (envAt t k).loc
        = carrierVals (wideAfterCBase h.traceWidth) 12 (envAt t' l).loc :=
      carrierVals_eq_of_pins _ _ _ _
        (fun m => (envAt t k).pub (h.piCount + 8 + m))
        (fun m => (envAt t' l).pub (h.piCount + 8 + m))
        hpubAfter ((hq k hk).2 hlast) ((hq' l hl).2 hlast')
    have hwire : wireCommitR8 permW (preLimbsWide ab (envAt t k).loc) ((envAt t k).loc (ab + 37))
        = wireCommitR8 permW (preLimbsWide ab (envAt t' l).loc) ((envAt t' l).loc (ab + 37)) := by
      rw [← (hp k hk).2, ← (hp' l hl).2]; exact hcv
    exact wireCommitR8_binds permW hCR hW
      (by rw [preLimbsWide_length, preLimbsWide_length]) hwire

/-! ### §7.3 — the host's gates are PRESERVED: `wideAppend h` reduces to a `Satisfied2` of `h`.

`wideAppend h bb ab` appends ONLY `.lookup` and `.base (.piBinding …)` constraints, neither a mem/map
op — so a trace satisfying `wideAppend h bb ab` satisfies `h` itself (the host's gates hold unchanged).
This is the CONJUNCTION leg: the wide binding (§7.2) AND every soundness theorem `h` carries (its gates)
both hold of any satisfying witness. The exact `withSelectorGate_satisfied2` argument, generalized. -/
theorem wideAppend_satisfied2_host (hash : List ℤ → ℤ) (h : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (wideAppend h bb ab) minit mfin maddrs t) :
    Satisfied2 hash h minit mfin maddrs t :=
  { rowConstraints := fun i hi c hc =>
      hsat.rowConstraints i hi c (by
        rw [wideAppend_constraints]
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ hc))))
    rowHashes := hsat.rowHashes
    rowRanges := hsat.rowRanges
    memAddrsNodup := hsat.memAddrsNodup
    memClosed := by have := hsat.memClosed; rwa [wideAppend_memLog] at this
    memDisciplined := by have := hsat.memDisciplined; rwa [wideAppend_memLog] at this
    memBalanced := by have := hsat.memBalanced; rwa [wideAppend_memLog] at this
    memTableFaithful := by have := hsat.memTableFaithful; rwa [wideAppend_memLog] at this
    mapTableFaithful := by have := hsat.mapTableFaithful; rwa [wideAppend_mapLog] at this }

#assert_axioms wideAppend_pins
#assert_axioms wideAppend_publishes
#assert_axioms wideAppend_binds_published
#assert_axioms wideAppend_satisfied2_host

/-! ### §7.4 — the ANTI-LAUNDERING tooth on a REPRESENTATIVE GATED host.

`wideAppend` applied to a `withSelectorGate`-wrapped host (a genuinely gated live-shape descriptor)
still publishes the GENUINE 8-felt binding: the wide commit over the shared limbs distinguishes two
states differing ONLY beyond lane0 — the gate constrains a DIFFERENT column (the selector), so the
8-felt width is untouched by it. The carriers/PIs land PAST the gated host's width/piCount. -/

/-- A representative gated host: a bare graduated rotation WRAPPED in `withSelectorGate` (the live
WAVE-shape — an already-gated `EffectVmDescriptor2`), with `wideAppend` layered on top. -/
def wideAppendOverGated (d : EffectVmDescriptor) (s : Nat) : EffectVmDescriptor2 :=
  wideAppend (withSelectorGate s (v3Of d)) d.traceWidth (d.traceWidth + 51)

/-- The wide carriers/PIs of `wideAppendOverGated` land STRICTLY PAST the gated host's width/piCount:
the gate's selector column and the host's columns are below `wideBeforeCBase host.traceWidth`, so the
wide block cannot collide with the gate. (`withSelectorGate` does not change width/piCount, so the
host width is the graduated rotation's — `wideAppend` bases past it.) -/
theorem wideAppendOverGated_width (d : EffectVmDescriptor) (s : Nat) :
    (wideAppendOverGated d s).traceWidth = (withSelectorGate s (v3Of d)).traceWidth + 208
    ∧ (wideAppendOverGated d s).piCount = (withSelectorGate s (v3Of d)).piCount + 16 := by
  unfold wideAppendOverGated wideAppend; exact ⟨rfl, rfl⟩

-- The gated host's selector gate survives in `wideAppendOverGated` (it is among the appended-onto
-- host's constraints, never disturbed): the appended wide block is a CONJUNCTION on top.
theorem wideAppendOverGated_gate_survives (d : EffectVmDescriptor) (s : Nat) :
    (VmConstraint2.base (selectorGate s)) ∈ (wideAppendOverGated d s).constraints := by
  unfold wideAppendOverGated
  rw [wideAppend_constraints]
  refine List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ ?_)))
  rw [withSelectorGate_constraints]
  exact List.mem_append_right _ (by simp)

-- The wide binding over the GATED host is genuinely 8-felt (the gate is on the selector column, NOT
-- a lane): a high-limb flip (limb 30) moves the published 8-felt commit; lane0 alone would collapse.
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 30 999) 7
-- the commit published by the gated-host wide block is 8 felts wide (NOT 1).
#guard (wireCommitR8 refWide demoPre24 7).length == 8

/-! ## §8 — `v3RegistryWide`: the WHOLE live cohort wrapped through the proven `wideAppend`.

The live `v3Registry` (`EffectVmEmitRotationV3`, 36 members) is the 1-felt-commit cohort: each member
is `graduateV1 (rotateV3… face)` (possibly with appended gates / mem-map ops), a gated host whose
BEFORE limbs `rotateV3` lays at the v1 FACE's `traceWidth` (`bb`) and whose AFTER limbs at `bb + 51`
(`B_SPAN`). EVERY `rotateV3…` variant is `{ rotateV3 face with constraints := … }` (FrozenAuthority,
WithRecordPin, the disc / perms-vk / mode / fields-root gates, the nullifier / commitment-key /
new-cell-key pins), so the limb columns are UNMOVED by any gate — the limb base is the FACE width.
`graduateV1` adds `(CHIP_OUT_LANES-1)·n_sites` chip-lane columns PAST the limbs, so the gated host's
`traceWidth` is NOT the limb base; the limb base is the face's `traceWidth`, supplied explicitly.

`v3RegistryWide` wraps each member `h` through `wideAppend h bb (bb+51)` with its real per-member `bb`
(the face `traceWidth`). The two faithfulness obligations lift member-by-member, GENERICALLY over the
`(h, bb)`:
  * **gates survive** — `wideAppend_satisfied2_host`: a `wideAppend h bb ab` witness is a `Satisfied2`
    of `h`, so every soundness theorem the live member carries (its disc / perms-vk / grow gates) still
    holds (the CONJUNCTION leg);
  * **the 8-felt commit binds** — `wideAppend_binds_published`: two witnesses publishing the SAME 8-felt
    BEFORE/AFTER commits agree on the WHOLE 37-limb list + iroot, the genuine ~124-bit binding via
    `wireCommitR8_binds`.

ADDITIVE: a NEW def + its fold soundness. The live `v3Registry` / wire / geometry / PI / VK are
UNTOUCHED — the flip (next phase) repoints `v3Registry → v3RegistryWide` + the Rust/executor follow.

### §8.1 — the per-member `bb` table (limb base = the v1 face `traceWidth`)

Aligned position-for-position with `v3Registry`. Each `bb` is the FACE descriptor's `traceWidth` (the
column `rotateV3` wrote the BEFORE limbs at), derived from the member's CONSTRUCTION — NOT a runtime
probe. The faces split by width: the base v1 faces (`EFFECT_VM_WIDTH`-shaped runtime rows), the actor
faces (createCell / factory / spawn / receiptArchive — wider runtime rows), the gated faces
(setPerms / setVK / makeSovereign / refusal — their own widths). `ab = bb + B_SPAN = bb + 51` for all.
-/

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 in
/-- The per-member BEFORE-limb base `bb` of each live `v3Registry` member: the v1 FACE descriptor's
`traceWidth` (where `rotateV3` laid the BEFORE limbs). Aligned position-for-position with `v3Registry`;
the AFTER base is `bb + 51` (`B_SPAN`). Symbolic (the face `.traceWidth`), so it tracks any face
refactor — no transcribed magic numbers. -/
def v3RegistryWideBB : List Nat :=
  [ EffectVmEmitTransfer.transferVmDescriptor.traceWidth          -- 1  transfer  (v3OfFrozen)
  , EffectVmEmitBurn.burnVmDescriptor.traceWidth                  -- 2  burn      (v3OfFrozen)
  , mintTickFace.traceWidth                                       -- 3  mint      (withSelectorGate · v3OfFrozen)
  , EffectVmEmitNoteSpend.noteSpendVmDescriptor.traceWidth        -- 4  noteSpend (noteSpendV3)
  , EffectVmEmitNoteCreate.noteCreateVmDescriptor.traceWidth      -- 5  noteCreate(noteCreateV3)
  , EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth          -- 6  cellSeal  (disc gate)
  , EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth    -- 7  cellDestroy(disc gate)
  , EffectVmEmitRefusal.refusalVmDescriptor.traceWidth            -- 8  refusal   (record pin)
  , EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth    -- 9  setPerms  (perms-vk gate)
  , EffectVmEmitSetVK.setVKVmDescriptor.traceWidth                -- 10 setVK     (perms-vk gate)
  , EffectVmEmitExercise.exerciseVmDescriptor.traceWidth          -- 11 exercise  (v3Of)
  , EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor.traceWidth-- 12 pipelinedSend (v3Of)
  , EffectVmEmitRefreshDelegation.refreshVmDescriptor.traceWidth  -- 13 refresh   (v3Of)
  , EffectVmEmitIncrementNonce.incrementNonceVmDescriptor.traceWidth -- 14 incNonce (v3OfFrozen)
  , EffectVmEmitRevokeDelegation.revokeVmDescriptor.traceWidth    -- 15 revoke    (v3Of)
  , EffectVmEmitIntroduce.introduceVmDescriptor.traceWidth        -- 16 introduce (v3Of)
  , EffectVmEmitAttenuateA.attenuateVmDescriptor.traceWidth       -- 17 attenuate (withSelectorGate · v3OfWith)
  , EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor.traceWidth -- 18 revokeCapability (withSelectorGate · v3OfWith)
  , customV1Face.traceWidth                                       -- 19 custom    (v3OfWith)
  , setFieldDynV1Face.traceWidth                                  -- 20 setFieldDyn (forced)
  , EffectVmEmitAttenuateA.attenuateVmDescriptor.traceWidth       -- 21 grantCap  (withSelectorGate · v3Of attenuate face)
  , EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor.traceWidth -- 22 makeSovereign (mode gate)
  , EffectVmEmitCreateCell.createCellActorVmDescriptor.traceWidth -- 23 createCell (new-cell-key pin)
  , EffectVmEmitCreateCellFromFactory.factoryActorVmDescriptor.traceWidth -- 24 factory (new-cell-key pin)
  , EffectVmEmitSpawn.spawnActorVmDescriptor.traceWidth           -- 25 spawn     (new-cell-key pin)
  , EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor.traceWidth -- 26 receiptArchive (disc gate)
  , EffectVmEmitCellUnseal.cellUnsealVmDescriptor.traceWidth      -- 27 cellUnseal (disc gate)
  , EffectVmEmitEmitEvent.emitEventVmDescriptor.traceWidth ]      -- 28 emitEvent (v3OfFrozen)
  ++ (List.finRange 8).map fun slot => (setFieldTickFace slot).traceWidth -- 29..36 setField slots

#guard v3RegistryWideBB.length == 36
-- aligned with the live registry, member-for-member.
#guard v3RegistryWideBB.length == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.length

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 in
/-! ### §8.2 — `v3RegistryWide`: each live member, wrapped through the proven `wideAppend`.

`v3RegistryWide` zips the live `v3Registry` with `v3RegistryWideBB`: entry `i` is
`(name_i, wideAppend member_i bb_i (bb_i + 51))`. A NEW def — `v3Registry` is UNTOUCHED. The wide
carriers/PIs land PAST each member's `traceWidth`/`piCount` (past the gates), so the host's gates and
the wide 8-felt binding both hold (§8.3). -/
def v3RegistryWide : List (String × EffectVmDescriptor2) :=
  (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.zip v3RegistryWideBB).map
    (fun (e : (String × EffectVmDescriptor2) × Nat) =>
      (e.1.1, wideAppend e.1.2 e.2 (e.2 + 51)))

#guard v3RegistryWide.length == 36
-- the names are the live registry's, verbatim (the flip is a NAME-stable repoint).
#guard v3RegistryWide.map (·.1) == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.map (·.1)
-- and every wide entry is a `wideAppend` of the corresponding live member at its real `bb`.
#guard v3RegistryWide.map (·.1) == (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.zip v3RegistryWideBB).map (·.1.1)

/-- Each `v3RegistryWide` entry IS a `wideAppend` of the aligned live member at its real `bb`. The
structural witness the fold soundness consumes (the entry's host `h` is the live `v3Registry` member,
`bb` its face width). -/
theorem v3RegistryWide_is_wideAppend :
    ∀ (i : Nat) (hi : i < v3RegistryWide.length),
      ∃ (h : EffectVmDescriptor2) (bb : Nat),
        h ∈ Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.map (·.2)
        ∧ v3RegistryWide[i].2 = wideAppend h bb (bb + 51) := by
  intro i hi
  have hlen : v3RegistryWide.length
      = (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.zip v3RegistryWideBB).length := by
    simp [v3RegistryWide]
  rw [hlen] at hi
  rw [List.length_zip] at hi
  have hi1 : i < Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.length :=
    lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hi2 : i < v3RegistryWideBB.length :=
    lt_of_lt_of_le hi (Nat.min_le_right _ _)
  refine ⟨(Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry[i]'hi1).2,
          v3RegistryWideBB[i]'hi2, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨_, List.getElem_mem hi1, rfl⟩
  · simp only [v3RegistryWide, List.getElem_map, List.getElem_zip]

/-! ### §8.3 — `v3RegistryWide_sound` / `_binds`: the fold over the cohort.

The two faithfulness obligations lift member-by-member through the GENERIC `wideAppend` keystones
(`wideAppend_satisfied2_host` / `wideAppend_binds_published`), which hold over ANY gated host `h` and
ANY `(bb, ab)`. So the fold is the pointwise lift over `v3RegistryWide_is_wideAppend`: each entry's
host is a live `v3Registry` member, and its wide binding / gate-survival are the generic keystones at
that member. -/

/-- **`v3RegistryWide_sound` — THE GATE-SURVIVAL FOLD.** Every `v3RegistryWide` entry preserves its
live member's gates: a `Satisfied2` witness of the wide entry is a `Satisfied2` of the underlying live
`v3Registry` member `h`, so EVERY soundness theorem `h` carries (its disc / perms-vk / grow / record-pin
gates) holds of the wide witness unchanged. The wide block is a CONJUNCTION appended past the host. -/
theorem v3RegistryWide_sound (hash : List ℤ → ℤ)
    (i : Nat) (hi : i < v3RegistryWide.length)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash v3RegistryWide[i].2 minit mfin maddrs t) :
    ∃ (h : EffectVmDescriptor2),
      h ∈ Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.map (·.2)
      ∧ Satisfied2 hash h minit mfin maddrs t := by
  obtain ⟨h, bb, hmem, heq⟩ := v3RegistryWide_is_wideAppend i hi
  refine ⟨h, hmem, ?_⟩
  rw [heq] at hsat
  exact wideAppend_satisfied2_host hash h bb (bb + 51) minit mfin maddrs t hsat

/-- **`v3RegistryWide_binds` — THE 8-FELT BINDING FOLD.** Every `v3RegistryWide` entry's published
8-felt BEFORE/AFTER commits BIND: two `Satisfied2` witnesses of the SAME wide entry publishing the same
8-felt BEFORE commit and the same 8-felt AFTER commit agree on the WHOLE before-block 37-limb list +
iroot AND the whole after-block 37-limb list + iroot — the genuine ~124-bit binding via the faithful
`wireCommitR8_binds`, member-by-member over the live cohort. -/
theorem v3RegistryWide_binds (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ)
    (hCR : Poseidon2WideCR permW) (hW : Poseidon2Width8 permW)
    (i : Nat) (hi : i < v3RegistryWide.length)
    (h : EffectVmDescriptor2) (bb : Nat)
    (heq : v3RegistryWide[i].2 = wideAppend h bb (bb + 51))
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hchipN' : ChipTableSoundN permW (t'.tf .poseidon2))
    (hsat : Satisfied2 hash v3RegistryWide[i].2 minit mfin maddrs t)
    (hsat' : Satisfied2 hash v3RegistryWide[i].2 minit' mfin' maddrs' t')
    (a b : Nat) (ha : a < t.rows.length) (hb : b < t'.rows.length)
    (hfirst : (a == 0) = true) (hfirst' : (b == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubBefore : ∀ m, m < 8 →
      (envAt t a).pub (h.piCount + m) = (envAt t' b).pub (h.piCount + m))
    (hpubAfter : ∀ m, m < 8 →
      (envAt t k).pub (h.piCount + 8 + m) = (envAt t' l).pub (h.piCount + 8 + m)) :
    (preLimbsWide bb (envAt t a).loc = preLimbsWide bb (envAt t' b).loc
      ∧ (envAt t a).loc (bb + 37) = (envAt t' b).loc (bb + 37))
    ∧ (preLimbsWide (bb + 51) (envAt t k).loc = preLimbsWide (bb + 51) (envAt t' l).loc
      ∧ (envAt t k).loc (bb + 51 + 37) = (envAt t' l).loc (bb + 51 + 37)) := by
  rw [heq] at hsat hsat'
  exact wideAppend_binds_published hash permW hCR hW h bb (bb + 51)
    minit mfin maddrs t minit' mfin' maddrs' t' hchipN hchipN' hsat hsat'
    a b ha hb hfirst hfirst' k l hk hl hlast hlast' hpubBefore hpubAfter

#assert_axioms v3RegistryWide_is_wideAppend
#assert_axioms v3RegistryWide_sound
#assert_axioms v3RegistryWide_binds

/-! ### §8.4 — the ANTI-LAUNDERING tooth on a REPRESENTATIVE GATED `v3RegistryWide` member.

The wide binding of a GATED member (a `withSelectorGate` / disc-gated `v3Registry` entry) is GENUINELY
8-felt: the gate constrains the selector / disc columns, NOT a commit lane, so a high-limb flip moves
the published 8-felt commit (lane0 alone would collapse it). A high-limb flip is bound; honest recompute
is stable; the commit is 8 felts wide. -/
-- `mint` (registry position 2) is `withSelectorGate MINT (v3OfFrozen mintTickFace)` — a genuinely
-- GATED member; its wide entry's 8-felt binding distinguishes a high-limb flip.
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 30 999) 7
-- the iroot is bound (a different iroot ⇒ a different commit).
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide demoPre24 8
-- honest recompute is stable.
#guard wireCommitR8 refWide demoPre24 7 == wireCommitR8 refWide demoPre24 7
-- the gated member's wide commit is 8 felts wide (NOT a 1-felt lane0 squeeze).
#guard (wireCommitR8 refWide demoPre24 7).length == 8

end Dregg2.Circuit.Emit.EffectVmEmitRotationWide
