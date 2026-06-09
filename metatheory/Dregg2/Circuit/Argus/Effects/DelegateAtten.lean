/-
# Dregg2.Circuit.Argus.Effects.DelegateAtten — the GATED rights-carrying Granovetter delegation
`delegateAttenA` welded into the Argus IR, in its OWN disjoint module (the per-effect-farm vehicle,
off the Argus cornerstone). This is the ATTENUATING sibling of `Effects/Delegate.lean`: where the
unattenuated `delegate` copies the held cap VERBATIM, `delegateAttenA` NARROWS it to `keep` before
granting — the faithful `apply_introduce` / `is_attenuation(held, granted)`, real `granted.rights ⊆
held.rights` over `ExecAuth = Finset Auth` (NOT a `()≤()` collapse).

`Argus/Stmt.lean` laid the cornerstone (`interp (transferStmt …) = recKExec`): the executor IS the
meaning of the IR term, by construction. It also built `checkSubset (a b : RecordKernelState →
ExecAuth)`, the FINITE-LATTICE non-amplification gate — a pure domain-restrictor committing IFF
`a k ⊆ b k` over the genuine `Finset Auth` `⊆` order (the FULL in-band realization of
non-amplification, superseding the cardinality-only `checkLe`). This module welds `delegateAttenA`
onto an Argus term that INTERNALIZES the FULL `granted.rights ⊆ held.rights` in-band via `checkSubset`,
and binds it against the audited `delegateAttenA` circuit.

## The executor target — the kernel step, unfolded (read off the CODE, `AuthTurn.lean:97`)

`recKDelegateAtten k del rec t keep`:

    if (k.caps del).any (fun cap => confersEdgeTo t cap) = true then
      some { k with caps := grant k.caps rec (attenuate keep (heldCapTo k.caps del t)) }
    else none

So a committed `delegateAttenA`:

  * **GUARD** `(k.caps del).any (fun cap => confersEdgeTo t cap) = true` — the Granovetter connectivity
    premise: `del` ALREADY HOLDS a `t`-conferring cap ("only connectivity begets connectivity").
  * **TOUCHED `caps`** ← `grant k.caps rec (attenuate keep (heldCapTo k.caps del t))` — `rec`'s slot
    gains the delegator's held `t`-cap ATTENUATED to `keep` (genuine non-amplification, §NON-AMPLIFICATION).
  * **FRAME** every other `RecordKernelState` component literally unchanged (`caps` is the one touched
    field) — so the IR body is `seq (guard …) (… setCaps …)`, the §A cap-graph write primitive.

## §NON-AMPLIFICATION — the FULL `granted.rights ⊆ held.rights`, enforced IN-BAND via `checkSubset`.

Unlike the unattenuated `delegate` (where amplification is impossible because the held cap is COPIED,
so `granted.rights = held.rights` definitionally and a `checkSubset` would gate the vacuous `x ⊆ x`),
`delegateAttenA` genuinely NARROWS: `attenuate keep c` filters an `endpoint` cap's rights to `keep`, so
`confRights (attenuate keep (heldCapTo …)) ⊆ confRights (heldCapTo …)` over the genuine `Finset Auth`
order (`attenuate_confRights_le`). This is a REAL, non-trivial subset, and the hint's `checkSubset`
in-band leg has genuine content here (it is the same finite-lattice gate `Effects/Attenuate.lean`
uses). The term is therefore `seq (guard premise) (seq (checkSubset granted held) (setCaps install))`:

  1. **`guard premise`** — the Granovetter connectivity gate (`AuthTurn.lean:99`), the EXACT executor
     commit condition. On a `del` with no `t`-conferring cap, `false` ⇒ `none` (fail-closed).
  2. **`checkSubset (granted.rights) (held.rights)`** — the in-band FULL non-amplification gate over
     `ExecAuth = Finset Auth ⊆`. It ALWAYS admits a genuine attenuation (`grantedDelRightsSet_le_held`,
     i.e. `attenuate_confRights_le`), so it does NOT change the term's commit set (which stays exactly
     the §1 premise); but it is GENUINELY TWO-VALUED (`checkSubset_rejects_overbroad_grant` /
     `…_incomparable_grant`, §6) — it would reject a superset OR an incomparable pair, the FULL partial
     order the cardinality `checkLe` could never express. So the FULL subset is an in-band IR gate.
  3. **`setCaps install`** — the EXACT executor cap-table write
     `grant k.caps rec (attenuate keep (heldCapTo k.caps del t))`.

The cornerstone (§3) proves this whole term IS `recKDelegateAtten` — the executor IS its meaning,
INCLUDING that the in-band `checkSubset` non-amplification leg matches the executor's (always-admitting,
because `attenuate` STRUCTURALLY narrows) attenuation discipline.

## SURFACE — the STRONGER full-state Surface2 weld (the BalanceA pattern, NOT the per-cell cap_root one).

`delegateAttenA` carries a GENUINE standalone v2 `EffectCommit2`/`Surface2` descriptor whose soundness
concludes the WHOLE 17-field declarative post-state — `Inst/delegateAttenA.lean`:

    delegateAttenA_full_sound : satisfiedE2 S (delegateAttenE D hD) (encodeE2 …) ⟹
      DelegateAttenSpec s args.del args.recv args.t args.keep s'

where `DelegateAttenSpec` (`Spec/authorityattenuation.lean`) is the INDEPENDENT full-state spec: the
guard ∧ the EXACT post-`caps` (the FULL function equality `grant … (attenuate keep (heldCapTo …))`, so
a tamper with ANY holder's slot is rejected — not just `rec`'s) ∧ the receipt-log cons ∧ all SIXTEEN
non-`caps` kernel fields frozen. Because a Surface2 `*_full_sound` exists, this module welds the
STRONGER full-state surface (per the BalanceA reference) rather than the per-cell `cap_root`
projection that `Effects/Delegate.lean`/`Effects/Attenuate.lean` use. The executor side is routed
through the independent `delegateAtten_iff_spec` (`execFullA ⟺ DelegateAttenSpec`); the circuit side is
`delegateAttenA_full_sound`. Both name the SAME `DelegateAttenSpec`, so they PROVABLY agree on the
WHOLE post-state (the `caps` rewrite + the log + every frozen field) — strictly stronger than a
per-cell weld.

## DIVERGENCE — NONE (this weld is divergence-clean at the spec level).

`delegateAttenA` is `caps`-only: it freezes the 16 non-`caps` kernel fields, so there is NO nonce-tick
divergence (a cap-graph effect touches no per-cell `nonce`; the `DelegateAttenSpec` frame freezes
every per-cell limb). And the chained executor `execFullA s (.delegateAttenA …) = recCDelegateAtten s
…` (`TurnExecutorFull.lean:3802`) wraps `recKDelegateAtten` DIRECTLY (it adds ONLY the receipt-log
prepend `authReceipt del :: s.log`) — there is NO `acceptsEffects` dst-liveness side-condition (unlike
the balanceA chained layer, whose `recCexecAsset` gates on R1). So the §4 chained lift carries NO
side-condition hypothesis. The one honest boundary the FULL-FUNCTION digest surface still carries (the
SAME as BalanceA): the circuit's `caps` component is a whole-FUNCTION injective digest
(`Function.Injective D` — the realizable Poseidon-CR bar), entering ONLY inside the reused
`delegateAttenA_full_sound`, never in the welded conclusion's statement.

## Honesty

`#assert_axioms` on both keystones (`interp_delegateAttenStmt_eq_recKDelegateAtten`,
`delegateAtten_compile_sound`) ⊆ {propext, Classical.choice, Quot.sound}; the whole-function-digest
assumption enters ONLY via the reused `delegateAttenA_full_sound`'s `Function.Injective D` hypothesis,
not in the welded conclusion. No `sorry`, no `:= True`, no `native_decide`, no `rfl`-posing-as-bridge.
Non-vacuity teeth (§6): the IR term genuinely INSTALLS the attenuated cap (observable cap-graph write),
genuinely NARROWS the rights (`{read,write}` → `{read}`, a real subset), genuinely REJECTS an
unconnected delegator (fail-closed), the `checkSubset` gate REJECTS a superset AND an incomparable
pair, and the welded descriptor is the genuine standalone v2 one (its emitted descriptor names
`dregg-delegateAttenA-v2`), not the inert placeholder. This module OWNS only itself; every import is
read-only.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.delegateAttenA

namespace Dregg2.Circuit.Argus.Effects.DelegateAtten

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus
  (RecStmt interp interp_checkSubset checkSubset_admits_iff kC)
open Dregg2.Authority (Caps Cap Auth Label)
-- Broad opens mirroring `Inst/delegateAttenA.lean` so the standalone-descriptor names resolve:
-- `logHashInjective` lives in `StateCommit`; `Surface2`/`satisfiedE2`/`encodeE2` in `EffectCommit2`.
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.AuthorityAttenuation
  (DelegateAttenSpec DelegateAttenGuard delegateAtten_iff_spec delegateAtten_rejects_ungrounded)
open Dregg2.Circuit.Inst.DelegateAttenA
  (DelegateAttenArgs delegateAttenE delegateAttenA_full_sound RestIffNoCaps
   delegateAttenAEmitted delegateAttenAAirName)

set_option autoImplicit false

/-! ## §1 — the in-band rights-SET read-outs (the genuine `Finset Auth` non-amplification carrier).

The FULL non-amplification gate reads the genuine rights LATTICE element `confRights c : ExecAuth`
(`Exec/Caps.lean:66`), ordered by `⊆`. The two read-outs are the conferred-rights SETS of the held
(parent) cap — `heldCapTo k.caps del t`, the cap the Granovetter premise witnesses — and of its
`keep`-attenuation (the cap the move actually installs into `rec`'s slot). These are exactly the values
the FULL `granted.rights ⊆ held.rights` gate (`checkSubset`) compares. -/

/-- The HELD-rights SET read-out: the parent cap's (`heldCapTo k.caps del t`) conferred rights as a
`Finset Auth` lattice element — the authority the attenuated grant must not exceed. -/
def heldDelRightsSet (del t : Label) : RecordKernelState → ExecAuth :=
  fun k => confRights (heldCapTo k.caps del t)

/-- The GRANTED-rights SET read-out: the conferred rights of the cap the move installs into `rec`'s
slot — the held `t`-cap ATTENUATED to `keep`. Its rights SET must be `⊆` the parent's (the FULL
non-amplification, `attenuate_confRights_le`). -/
def grantedDelRightsSet (del t : Label) (keep : List Auth) : RecordKernelState → ExecAuth :=
  fun k => confRights (attenuate keep (heldCapTo k.caps del t))

/-- **`grantedDelRightsSet_le_held` — the FULL in-band gate ALWAYS admits a genuine attenuation (PROVED).**
The attenuated cap's conferred-rights SET is `⊆` (= `≤`) the parent's, over the genuine `ExecAuth =
Finset Auth` order — directly `attenuate_confRights_le` (the executor's `attenuate` STRUCTURALLY
narrows the rights set). So the `checkSubset` non-amplification gate (granted ⊆ held) commits on every
genuine `delegateAttenA`: fail-closed, never fail-stuck. This is the FULL subset, NOT a cardinality
shadow — the genuine `granted.rights ⊆ held.rights`. -/
theorem grantedDelRightsSet_le_held (del t : Label) (keep : List Auth) (k : RecordKernelState) :
    grantedDelRightsSet del t keep k ≤ heldDelRightsSet del t k :=
  attenuate_confRights_le keep (heldCapTo k.caps del t)

/-! ## §2 — THE IR TERM: the Granovetter guard, the in-band FULL-SUBSET `checkSubset` gate, then the
attenuated cap-graph install.

`delegateAttenStmt = seq (guard premise) (seq (checkSubset granted held) (setCaps install))`.

  * `guard premise` is the EXACT executor commit condition (`.any confersEdgeTo` — the delegator holds a
    `t`-conferring cap). It is the only thing that gates the commit.
  * `checkSubset (granted.rights) (held.rights)` is the in-band FULL non-amplification gate over the
    genuine `Finset Auth ⊆` order: the installed cap's conferred-rights SET ⊆ the parent's. It ALWAYS
    admits a genuine attenuation (§1), so it does NOT alter the commit set — but it is genuinely
    two-valued (§6), internalizing the FULL `granted.rights ⊆ held.rights` in the IR.
  * `setCaps install` is the EXACT executor cap-table write `grant k.caps rec (attenuate keep (heldCapTo
    k.caps del t))`. -/

/-- **The delegateAtten admissibility gate as a `Bool`** — exactly `recKDelegateAtten`'s `if`-condition
(`AuthTurn.lean:99`): the delegator already holds a cap conferring an edge to `t`. The in-band Boolean
form of the Granovetter connectivity premise ("only connectivity begets connectivity"). -/
def delAttenGuardB (del t : Label) (k : RecordKernelState) : Bool :=
  (k.caps del).any (fun cap => confersEdgeTo t cap)

/-- **The delegateAtten effect as an Argus IR term.** Gate on the Granovetter premise, then the FULL
in-band non-amplification subset check `granted.rights ⊆ held.rights` (via `checkSubset`), then install
`grant k.caps rec (attenuate keep (heldCapTo k.caps del t))` (the EXACT executor cap-table write).
Mirrors `Effects/Attenuate.lean`'s `checkSubset`-gated shape, but with the leading Granovetter `guard`
(the executor's real commit condition — attenuate has none) — and a GENUINELY non-trivial subset (the
attenuated grant strictly narrows, unlike the verbatim-copy unattenuated `delegate`). -/
def delegateAttenStmt (del rec t : Label) (keep : List Auth) : RecStmt :=
  RecStmt.seq (RecStmt.guard (delAttenGuardB del t))
    (RecStmt.seq
      (RecStmt.checkSubset (grantedDelRightsSet del t keep) (heldDelRightsSet del t))
      (RecStmt.setCaps (fun k =>
        grant k.caps rec (attenuate keep (heldCapTo k.caps del t)))))

/-! ## §3 — THE CORNERSTONE: `interp` of the delegateAtten term IS the kernel step `recKDelegateAtten`.

The SAME shape as the transfer/escrow/attenuate cornerstones. The leading `guard` is the EXACT executor
commit condition; the `checkSubset` ALWAYS admits (`grantedDelRightsSet_le_held` — the executor's
`attenuate` structurally produces a subset), so it never changes the commit set; the `setCaps` install
is exactly `recKDelegateAtten`'s `grant … (attenuate keep (heldCapTo …))`. The executor IS the meaning
of the term, INCLUDING that the in-band `checkSubset` non-amplification leg matches the executor's
(always-admitting) attenuation discipline. -/

/-- **The cornerstone (gated rights-carrying delegation).** `interp` of the delegateAtten term IS the
verified executor `recKDelegateAtten` — the same partial function, by construction, exactly as the
transfer/mint/burn/escrow/attenuate cornerstones. The leading Granovetter `guard` is the EXACT commit
condition; the in-band FULL `checkSubset` non-amplification gate admits on every genuine attenuation
(`grantedDelRightsSet_le_held`, via `attenuate_confRights_le`), so the term commits exactly when (and
only when) `recKDelegateAtten` does, installing the SAME attenuated grant. -/
theorem interp_delegateAttenStmt_eq_recKDelegateAtten (del rec t : Label) (keep : List Auth)
    (k : RecordKernelState) :
    interp (delegateAttenStmt del rec t keep) k = recKDelegateAtten k del rec t keep := by
  simp only [delegateAttenStmt, interp]
  unfold recKDelegateAtten
  by_cases hg : delAttenGuardB del t k = true
  · -- ADMIT: the Granovetter `guard` fires (`some k`); the `bind` runs the `checkSubset` leg, which
    -- ALWAYS admits (`grantedDelRightsSet_le_held`), so the final `setCaps` installs the attenuated
    -- grant — exactly `recKDelegateAtten`'s post-`caps`. The kernel `if` opens on the same premise.
    rw [if_pos hg]
    simp only [Option.bind_some]
    rw [if_pos (grantedDelRightsSet_le_held del t keep k)]
    simp only [Option.bind_some]
    unfold delAttenGuardB at hg
    rw [if_pos hg]
  · -- REJECT: the Granovetter `guard` fails (`none`); the outer `bind` short-circuits ⇒ `none`. The
    -- kernel `if` also rejects on the same (negated) premise.
    rw [if_neg hg]
    simp only [Option.bind_none]
    unfold delAttenGuardB at hg
    rw [if_neg hg]

#assert_axioms interp_delegateAttenStmt_eq_recKDelegateAtten

/-! ## §4 — Lifting the cornerstone to the CHAINED executor `recCDelegateAtten` / `execFullA`.

The standalone descriptor (§5) is keyed on the CHAINED executor `execFullA` over `RecChainedState`
(kernel + receipt log) — the arm `execFullA s (.delegateAttenA del rec t keep) = recCDelegateAtten s
del rec t keep` (`TurnExecutorFull.lean:3802`). The §3 cornerstone is over the RAW kernel step
`recKDelegateAtten`. The chained layer is exactly `recKDelegateAtten` PLUS the receipt-log prepend
`authReceipt del :: s.log` — and, crucially, NOTHING ELSE: `recCDelegateAtten` has NO `acceptsEffects`
dst-liveness pre-gate (unlike the balanceA chained layer). So this lift carries NO side-condition
hypothesis (the honest contrast with balanceA, where the R1 gate had to be carried). -/

/-- **`interp_delegateAttenStmt_chained` — the IR term's executor, lifted to the chained `execFullA`,
with NO side-condition.** When the §3 cornerstone commits on the kernel (`interp (delegateAttenStmt …)
s.kernel = some k'`), the unified action executor `execFullA s (.delegateAttenA del rec t keep)` commits
to the chained state `⟨k', authReceipt del :: s.log⟩`. So the Argus term's kernel meaning lifts to the
chained executor the standalone descriptor speaks about — and (unlike balanceA) needs NO dst-liveness
hypothesis, because `recCDelegateAtten` wraps `recKDelegateAtten` directly. -/
theorem interp_delegateAttenStmt_chained
    (s : RecChainedState) (del rec t : Label) (keep : List Auth) (k' : RecordKernelState)
    (hexec : interp (delegateAttenStmt del rec t keep) s.kernel = some k') :
    execFullA s (.delegateAttenA del rec t keep) = some { kernel := k', log := authReceipt del :: s.log } := by
  -- the §3 cornerstone turns the IR term into the raw kernel step `recKDelegateAtten`.
  rw [interp_delegateAttenStmt_eq_recKDelegateAtten] at hexec
  -- `execFullA s (.delegateAttenA …)` reduces to `recCDelegateAtten s …`, a `match recKDelegateAtten …`;
  -- `hexec` names that as `some k'`, so the receipt-prepended chained state is produced.
  show recCDelegateAtten s del rec t keep = some { kernel := k', log := authReceipt del :: s.log }
  unfold recCDelegateAtten
  rw [hexec]

#assert_axioms interp_delegateAttenStmt_chained

/-! ## §5 — THE COMPILE WELD: a satisfying witness of delegateAtten's OWN standalone Surface2 circuit
agrees with the FULL post-state the IR term's executor interpretation produces.

This welds against delegateAtten's GENUINE standalone descriptor `satisfiedE2 S (delegateAttenE D hD)
…` (the v2 full-state circuit whose soundness is `delegateAttenA_full_sound`), NOT the per-cell
cap_root descriptor — see the SURFACE note in this file's header. The executor side is routed through
§4 (`interp` ⟹ `execFullA`) and the independent `delegateAtten_iff_spec` (executor ⟺ `DelegateAttenSpec`);
the circuit side is the audited `delegateAttenA_full_sound` (circuit ⟹ `DelegateAttenSpec`). Both name
the SAME `DelegateAttenSpec`, so they PROVABLY agree on the WHOLE 17-field state + the receipt log —
strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `delegateAttenA` term: delegateAtten's OWN audited standalone
v2 `Surface2` circuit step — the full-state arithmetization `satisfiedE2 S (delegateAttenE D hD)
(encodeE2 …)` satisfied on the encoded `(s, args, s')` triple. Its soundness `delegateAttenA_full_sound`
pins the complete `DelegateAttenSpec`. The `delegateAttenA`-keyed analog of `balanceACircuit`, in the
descriptor universe where delegateAtten carries its OWN genuine full-state circuit. -/
def delegateAttenCircuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2 S (delegateAttenE D hD) (encodeE2 S (delegateAttenE D hD) s args s')

/-- **`delegateAttenSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH
satisfy `DelegateAttenSpec s del rec t keep ·` are equal. Rather than re-derive this field-by-field, we
route through the PROVEN executor⟺spec corner `delegateAtten_iff_spec`: each `DelegateAttenSpec`
reconstructs the SAME committed value `execFullA s (.delegateAttenA …) = some ·`, and `some` is
injective. This is exactly the sense in which `DelegateAttenSpec` is functional — it determines the
post-state — so the circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem delegateAttenSpec_unique {s s₁ s₂ : RecChainedState} {del rec t : Label} {keep : List Auth}
    (h₁ : DelegateAttenSpec s del rec t keep s₁) (h₂ : DelegateAttenSpec s del rec t keep s₂) :
    s₁ = s₂ := by
  have e₁ : execFullA s (.delegateAttenA del rec t keep) = some s₁ :=
    (delegateAtten_iff_spec s del rec t keep s₁).mpr h₁
  have e₂ : execFullA s (.delegateAttenA del rec t keep) = some s₂ :=
    (delegateAtten_iff_spec s del rec t keep s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`delegateAtten_compile_sound` — the welded soundness (delegateAtten slice), against its OWN
descriptor.**

Suppose, for the Argus delegateAtten term `delegateAttenStmt del rec t keep`:
  * the standalone delegateAtten circuit `delegateAttenCircuit S D hD s ⟨del,rec,t,keep⟩ s'` (=
    `delegateAttenE`'s full-state v2 arithmetization satisfied on the encoded triple) holds, under the
    realizable whole-function digest portals (`hRest : RestIffNoCaps S.RH`, `hLog : logHashInjective
    S.LH`, `hD : Function.Injective D`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel: `interp (delegateAttenStmt …) s.kernel =
    some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `s' = { kernel := k', log := authReceipt del :: s.log }`. I.e. delegateAtten's OWN circuit and
the IR term AGREE on the WHOLE 17-field RecordKernelState (`caps` rewritten to the attenuated grant `grant
… (attenuate keep (heldCapTo …))` — the FULL function, so a tamper with ANY holder's slot is rejected —
every other field frozen) AND the receipt log — the full `DelegateAttenSpec`, NOT a per-cell projection.
So the circuit the prover runs for delegateAtten pins the complete state the IR term's executor produces.
NO divergence conjunct is needed: `delegateAttenA` freezes the 16 non-`caps` fields (no nonce-tick) and
the chained wrapper adds only the receipt (no dst-liveness gate). -/
theorem delegateAtten_compile_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (del rec t : Label) (keep : List Auth) (k' : RecordKernelState)
    (hcirc : delegateAttenCircuit S D hD s ⟨del, rec, t, keep⟩ s')
    (hexec : interp (delegateAttenStmt del rec t keep) s.kernel = some k') :
    s' = { kernel := k', log := authReceipt del :: s.log } := by
  -- circuit side: delegateAtten's OWN audited soundness forces the FULL `DelegateAttenSpec` on
  -- `(s, ⟨del,rec,t,keep⟩, s')` — note the args projections `.del/.recv/.t/.keep`.
  have hspec : DelegateAttenSpec s del rec t keep s' :=
    delegateAttenA_full_sound S D hD hRest hLog s ⟨del, rec, t, keep⟩ s' hcirc
  -- executor side: the §4 chained lift gives `execFullA s (.delegateAttenA …) = some ⟨k', authReceipt
  -- del :: s.log⟩`, and the independent executor⟺spec corner turns THAT into `DelegateAttenSpec s … ⟨k',
  -- authReceipt del :: s.log⟩`.
  have hspec' : DelegateAttenSpec s del rec t keep { kernel := k', log := authReceipt del :: s.log } :=
    (delegateAtten_iff_spec s del rec t keep _).mp (interp_delegateAttenStmt_chained s del rec t keep k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact delegateAttenSpec_unique hspec hspec'

#assert_axioms delegateAtten_compile_sound

/-! ## §6 — NON-VACUITY: the IR term genuinely INSTALLS the ATTENUATED cap (observable + a REAL subset),
genuinely REJECTS an unconnected delegator (fail-closed), the in-band `checkSubset` REJECTS a non-subset
(superset AND incomparable), and the welded descriptor is the genuine standalone v2 one.

The cornerstone/weld would be hollow if delegateAtten never committed, if the install were a no-op, if
the attenuation didn't narrow, if the gate admitted everything, or if the descriptor were a placeholder.
A concrete three-account kernel exercises a real attenuating delegation; the rejection lemmas show the
guard and the `checkSubset` gate each fail closed. -/

/-- A concrete kernel where the delegator (cell `0`) HOLDS an `endpoint 9 [read, write]` cap (an edge to
`9`, conferring rights `{read,write}`), the recipient (cell `2`) holds none. So an attenuating delegate
of the edge to target `9`, narrowed to `[read]`, is admissible and OBSERVABLE. Built on the §C `kC` base
(cells `0`,`1` live; we add cell `2` to `accounts`). -/
def kDA : RecordKernelState :=
  { kC with
    accounts := {0, 1, 2}
    caps := fun l => if l = 0 then [Cap.endpoint 9 [Auth.read, Auth.write]] else [] }

/-- **NON-VACUITY (the cap-graph write is OBSERVABLE — the ATTENUATED edge INSTALLS).** Running the
delegateAtten term on `kDA` (delegator `0` holds `endpoint 9 [read,write]`, recipient `2` holds nothing)
commits, and recipient cell `2`'s slot GAINS the delegator's held cap ATTENUATED to `[read]` (i.e.
`endpoint 9 [read]`): `[]` → `[Cap.endpoint 9 [Auth.read]]`. The `setCaps` write is a real, observable
cap-graph mutation (the recipient becomes connected to `9` with NARROWED rights), not a no-op. -/
theorem delegateAttenStmt_installs_attenuated :
    (interp (delegateAttenStmt 0 2 9 [Auth.read]) kDA).map (fun k => k.caps 2)
      = some [Cap.endpoint 9 [Auth.read]] := by
  rw [interp_delegateAttenStmt_eq_recKDelegateAtten]
  decide

/-- **NON-VACUITY (recipient was empty before).** Cell `2` held NO caps before the delegate — so the
install above is a genuine state change, not a pre-existing edge. -/
theorem delegateAttenStmt_recipient_empty_before : kDA.caps 2 = [] := by decide

/-- **NON-AMPLIFICATION (the attenuation genuinely NARROWS — a REAL subset, not a copy).** On `kDA` the
GRANTED rights SET (`{read}`, from the `[read]`-attenuation) is a STRICT subset of the HELD rights SET
(`{read,write}`): the delegateAtten move drops the `write` right. This is the content the unattenuated
`delegate` lacks (it copies, so granted = held) — here `granted.rights ⊊ held.rights`, the genuine
`is_attenuation`, pinned over the real `ExecAuth = Finset Auth` order. -/
theorem delegateAttenStmt_genuinely_narrows :
    grantedDelRightsSet 0 9 [Auth.read] kDA = ({Auth.read} : Finset Auth)
    ∧ heldDelRightsSet 0 9 kDA = ({Auth.read, Auth.write} : Finset Auth)
    ∧ grantedDelRightsSet 0 9 [Auth.read] kDA < heldDelRightsSet 0 9 kDA := by
  refine ⟨by decide, by decide, by decide⟩

/-- **NON-VACUITY (fail-closed — Granovetter premise).** A delegateAtten whose DELEGATOR holds no
`t`-conferring cap does NOT commit: delegating from the empty recipient cell `2` (which holds nothing)
the edge to `9` returns `none` — the Granovetter connectivity premise fails, so the cap-graph write
never fires (only connectivity begets connectivity). -/
theorem delegateAttenStmt_rejects_unconnected :
    interp (delegateAttenStmt 2 1 9 [Auth.read]) kDA = none := by
  rw [interp_delegateAttenStmt_eq_recKDelegateAtten]
  decide

/-- **`delegateAttenStmt_admits_iff_guard` — the term's commit set is EXACTLY the Granovetter premise.**
The delegateAtten term COMMITS (is `some`) IFF the delegator holds a `t`-conferring cap
(`DelegateAttenGuard`). So the in-band `checkSubset` leg — which ALWAYS admits (§1) — does NOT shrink the
commit set; the executor's real gate is the Granovetter premise, faithfully captured. (Via the §3
cornerstone + `delegateAtten_rejects_ungrounded`/the kernel `if`.) -/
theorem delegateAttenStmt_admits_iff_guard (s : RecChainedState) (del rec t : Label) (keep : List Auth) :
    (interp (delegateAttenStmt del rec t keep) s.kernel).isSome = true ↔ DelegateAttenGuard s del t := by
  rw [interp_delegateAttenStmt_eq_recKDelegateAtten]
  unfold DelegateAttenGuard recKDelegateAtten
  by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg]; simp [hg]
  · rw [if_neg hg]; simp [hg]

/-- **NON-VACUITY (the in-band gate REJECTS a strict SUPERSET).** A synthetic move whose installed cap's
rights SET is a strict SUPERSET of the parent's (`{read,write} ⊄ {read}`) is REJECTED by the `checkSubset`
gate (`interp = none`) — the in-band FULL non-amplification check fails closed on amplification. Exhibited
directly on `checkSubset`, the term's non-amplification leg, with an explicit over-broad granted-vs-held
pair. -/
theorem checkSubset_rejects_overbroad_grant :
    interp (RecStmt.checkSubset (fun _ => ({Auth.read, Auth.write} : Finset Auth))
              (fun _ => ({Auth.read} : Finset Auth))) kC = none := by
  rw [interp_checkSubset]; decide

/-- **⚑ NON-VACUITY (the GAIN over `checkLe` — the in-band gate REJECTS an INCOMPARABLE pair).** The thing
a cardinality `checkLe` could NEVER do: a move granting `{write}` against a parent holding only `{read}`
(EQUAL cardinality `1`, but NEITHER a subset of the other) is REJECTED by `checkSubset` (`interp = none`).
This is the FULL `granted.rights ⊆ held.rights` partial order enforced in-band — demonstrated on the
actual non-amplification leg of the term. -/
theorem checkSubset_rejects_incomparable_grant :
    interp (RecStmt.checkSubset (fun _ => ({Auth.write} : Finset Auth))
              (fun _ => ({Auth.read} : Finset Auth))) kC = none := by
  rw [interp_checkSubset]; decide

/-- **NON-VACUITY (the descriptor is the genuine standalone v2 one, not the placeholder).** The welded
circuit is delegateAtten's OWN audited standalone descriptor (`delegateAttenE`), whose emitted form names
`dregg-delegateAttenA-v2` (the running prover's per-effect AIR), not the inert placeholder. So
`delegateAtten_compile_sound` is a statement about a REAL full-state circuit. -/
theorem delegateAttenAEmitted_nontrivial :
    delegateAttenAEmitted.name = "dregg-delegateAttenA-v2"
    ∧ delegateAttenAAirName = "dregg-delegateAttenA-v2" := by
  refine ⟨by decide, rfl⟩

#assert_axioms delegateAttenStmt_installs_attenuated
#assert_axioms delegateAttenStmt_recipient_empty_before
#assert_axioms delegateAttenStmt_genuinely_narrows
#assert_axioms delegateAttenStmt_rejects_unconnected
#assert_axioms delegateAttenStmt_admits_iff_guard
#assert_axioms checkSubset_rejects_overbroad_grant
#assert_axioms checkSubset_rejects_incomparable_grant
#assert_axioms delegateAttenAEmitted_nontrivial

end Dregg2.Circuit.Argus.Effects.DelegateAtten
