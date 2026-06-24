/-
# Dregg2.Verify.KeystoneAuditSystemRoots — the keystone-audit for the Wave-4 HARD
`runnable_binds_same_system_roots` (R1 closed for the side-table state; AC:520).

The keystone `Dregg2.Circuit.CommitmentCrossBind.runnable_binds_same_system_roots` says: two rows of
the WIDE runnable EffectVm descriptor that publish the SAME `state_commit`, whose `sysRootsDigestCol`
carriers ARE the `systemRootsDigest` of their `system_roots` sub-blocks, agree on EVERY side-table
root. It carries the named crypto floor `Poseidon2Binding.Poseidon2SpongeCR hash` and the wide
hash-site hypothesis `siteHoldsAll hash e wideHashSites`.

The non-vacuity question this module answers is the SHARP one: is `siteHoldsAll hash e wideHashSites`
JOINTLY satisfiable on a CONCRETE row (together with the carrier/commit hypotheses), under a CONCRETE
collision-resistant `hash`? It is. We supply:

  * `hash := FloorsNonVacuous.encodeSponge` (the proven-CR injective `Encodable.encode`-cast sponge,
    `encodeSponge_cr : Poseidon2SpongeCR encodeSponge`), so the named crypto floor is REALIZED — this
    keystone is WELDABLE, not terminal; and
  * a CONCRETE WIDE row `witnessRow sr` whose four GROUP-4 digest output columns (`STATE_INTER1/2/3` and
    `saCol STATE_COMMIT`) carry, BY CONSTRUCTION, the genuine `encodeSponge` of their resolved inputs,
    and whose `sysRootsDigestCol` carrier IS `systemRootsDigest encodeSponge sr`. So
    `siteHoldsAll encodeSponge (witnessRow sr) wideHashSites` holds (each site by `rfl` after the walk),
    and `hd : (witnessRow sr).loc sysRootsDigestCol = systemRootsDigest encodeSponge sr` holds by `rfl`.

  [1] NON-VACUITY (`*_satisfiable`): take `e₁ = e₂ = witnessRow sr₀`, `sr₁ = sr₂ = sr₀`. The wide-site,
      carrier, and equal-commit hypotheses are DISCHARGED on the concrete row (not assumed), so the
      keystone FIRES its conclusion `sr₀ i = sr₀ i` on a genuinely satisfying instance — non-vacuous.
  [2] TEETH (`*_teeth`): a hostile `SysRoots` pair differing at index 0 (`0 ≠ 1`) REFUTES the
      conclusion `sr₁ 0 = sr₂ 0` by `decide` — the keystone's conclusion is two-valued, not `:= True`.

`#keystone_audit` THROWS on any FAIL, so this module is a CI gate. No `native_decide`; `#assert_axioms`
⊆ {propext, Classical.choice, Quot.sound} on every new theorem and the re-pinned alias.
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Circuit.CommitmentCrossBind
import Dregg2.Circuit.FloorsNonVacuous

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditSystemRoots

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable (wideHashSites)
open Dregg2.Circuit.FloorsNonVacuous (encodeSponge encodeSponge_cr)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false

/-! ## §1 — the CONCRETE WIDE row that satisfies `siteHoldsAll encodeSponge _ wideHashSites`.

`wideHashSites = [site0, site1, site2, sysRootsAbsorbSite (saCol STATE_COMMIT)]`. Their result columns
are (absolutely) `auxCol STATE_INTER1 = 98`, `auxCol STATE_INTER2 = 99`, `auxCol STATE_INTER3 = 100`,
and `saCol STATE_COMMIT = 88`. The inner sites read the after-state block columns `76..87` (all `0`
in this row); the absorbing site reads sites 0/1/2's digests AND `sysRootsDigestCol = 188`.

We set each of the four output columns to EXACTLY its prescribed digest, and `sysRootsDigestCol` to
`systemRootsDigest encodeSponge sr`. Every other column is `0`. The four output columns
`{88, 98, 99, 100}` are DISJOINT from all input columns (`76..87` and `188`), so the row is consistent:
each site's hash reads only `0`-columns / earlier digests, never an output column it would perturb. -/

/-- The two inner digests over the all-zero after-state block. `site0` reads
`[bal_lo, bal_hi, nonce, fld0] = [0,0,0,0]`; `site1` reads `[fld1..4] = [0,0,0,0]`; `site2` reads
`[fld5,fld6,fld7,cap] = [0,0,0,0]`. So all three inner digests are `encodeSponge [0,0,0,0]`. -/
def innerDigest : ℤ := encodeSponge [0, 0, 0, 0]

/-- The published `state_commit` digest: `H4(inter1, inter2, inter3, sysRootsDigest)` with the three
inner digests equal to `innerDigest` and the 4th input the `system_roots` carrier. -/
def commitDigest (sr : SysRoots) : ℤ :=
  encodeSponge [innerDigest, innerDigest, innerDigest, systemRootsDigest encodeSponge sr]

/-- **`witnessRow sr`** — the concrete WIDE `VmRowEnv`. `loc` sets the four GROUP-4 digest output
columns to their genuine `encodeSponge` digests and the `sysRootsDigestCol` carrier to
`systemRootsDigest encodeSponge sr`; everything else (incl. all hash-site INPUT columns) is `0`.
`nxt`/`pub` are unused by `siteHoldsAll`/the carrier hypotheses, so they are the zero assignment. -/
def witnessRow (sr : SysRoots) : VmRowEnv where
  loc := fun c =>
    if c = saCol state.STATE_COMMIT then commitDigest sr
    else if c = auxCol aux_off.STATE_INTER1 then innerDigest
    else if c = auxCol aux_off.STATE_INTER2 then innerDigest
    else if c = auxCol aux_off.STATE_INTER3 then innerDigest
    else if c = sysRootsDigestCol then systemRootsDigest encodeSponge sr
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The carrier column holds the `system_roots` digest BY CONSTRUCTION (`rfl`). -/
theorem witnessRow_carrier (sr : SysRoots) :
    (witnessRow sr).loc sysRootsDigestCol = systemRootsDigest encodeSponge sr := by
  rfl

/-- **`witnessRow_holds_wideSites`** — the CONCRETE row SATISFIES the wide hash-site hypothesis. Each
of the four sites' result column carries, by construction, the `encodeSponge` of its resolved inputs:
the three inner sites over the all-`0` after-state block (= `innerDigest`), and the absorbing site over
`[inter1, inter2, inter3, carrier]` (= `commitDigest sr`). The proof unfolds `siteHoldsAll`'s ordered
walk and discharges each conjunct by `rfl` — so this is NOT an assumed hypothesis, it is dischargeable
on a real row, exactly the non-vacuity bar. -/
theorem witnessRow_holds_wideSites (sr : SysRoots) :
    siteHoldsAll encodeSponge (witnessRow sr) wideHashSites := by
  unfold siteHoldsAll wideHashSites
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> rfl

/-! ## §2 — NON-VACUITY: the satisfiable companion (hypotheses discharged on `witnessRow`). -/

/-- The non-vacuity reference sub-block (any concrete `SysRoots` works; the empty one is canonical). -/
def sr₀ : SysRoots := emptySystemRoots

/-- **`runnable_binds_same_system_roots_satisfiable`.** The keystone's hypotheses are JOINTLY satisfied
on a CONCRETE instance: `hash := encodeSponge` (CR via `encodeSponge_cr`), `e₁ = e₂ = witnessRow sr₀`
(wide sites discharged via `witnessRow_holds_wideSites`, equal-commit by `rfl`, carriers via
`witnessRow_carrier`), `sr₁ = sr₂ = sr₀`. So the keystone FIRES its conclusion `sr₀ i = sr₀ i` on a
genuinely satisfying instance — the carried `siteHoldsAll`/`Poseidon2SpongeCR`/carrier hypotheses are
not secretly unsatisfiable. The statement reproduces the keystone's conclusion at the witness. -/
theorem runnable_binds_same_system_roots_satisfiable (i : Fin N_SYSTEM_ROOTS) :
    sr₀ i = sr₀ i :=
  Dregg2.Circuit.CommitmentCrossBind.runnable_binds_same_system_roots
    encodeSponge encodeSponge_cr (witnessRow sr₀) (witnessRow sr₀) sr₀ sr₀
    (witnessRow_holds_wideSites sr₀) (witnessRow_holds_wideSites sr₀)
    rfl (witnessRow_carrier sr₀) (witnessRow_carrier sr₀) i

/-! ## §3 — TEETH: the conclusion DISCRIMINATES (a hostile `SysRoots` pair refutes it). -/

/-- A hostile pair: `srHi` differs from `srLo := sr₀` (all `0`) at index `0` (value `1`). -/
def srHi : SysRoots := fun j => if j = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0

/-- **`runnable_binds_same_system_roots_teeth`.** On the hostile `SysRoots` pair `(sr₀, srHi)` that
differs at index `0` (`0 ≠ 1`), the keystone's conclusion `sr₀ 0 = srHi 0` is FALSE. So the conclusion
`sr₁ i = sr₂ i` is two-valued — proving the keystone CONSTRAINS the side-table roots, it is not
`:= True`. (The teeth need not satisfy the keystone's hypotheses; it refutes the conclusion on a
hostile instance, the discrimination half of the audit.) -/
theorem runnable_binds_same_system_roots_teeth :
    ¬ (sr₀ (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) = srHi (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)) := by
  decide

/-! ## §4 — TAG the keystone with its companions + RUN the audit (the CI gate). -/

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditSystemRoots.runnable_binds_same_system_roots_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditSystemRoots.runnable_binds_same_system_roots_teeth]
def runnable_binds_same_system_roots_KS :=
  @Dregg2.Circuit.CommitmentCrossBind.runnable_binds_same_system_roots

#keystone_audit Dregg2.Verify.KeystoneAuditSystemRoots.runnable_binds_same_system_roots_KS

#keystone_audit_tagged

/-! ## §5 — axiom-hygiene over the witnesses + re-pinned alias (kernel-triple clean). -/

#assert_axioms witnessRow_carrier
#assert_axioms witnessRow_holds_wideSites
#assert_axioms runnable_binds_same_system_roots_satisfiable
#assert_axioms runnable_binds_same_system_roots_teeth
#assert_axioms runnable_binds_same_system_roots_KS

end Dregg2.Verify.KeystoneAuditSystemRoots
