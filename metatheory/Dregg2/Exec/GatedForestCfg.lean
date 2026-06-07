/-
# Dregg2.Exec.GatedForestCfg — first-class gated-forest carrier bundle.

Packages the `execFullForestG` carrier parameters as a `GatedForestCarriers` record, with
`starbridgeCarriers` the canonical production instance. Downstream modules `open StarbridgeGated`
instead of a pinned `Demo`/`Production` namespace.

**Production routing for `.coordinated` caveats:** intra-cell `execFullForestG` fail-closes
(see `FullForestAuth.GatedCaveat.holds`); the positive bilateral path is
`CoordinatedForestGLift.execCoordinatedForestG` over a `BilateralForestPairG` of two
`RecChainedState` snapshots (honest — no cross-cell reads on one cell).
-/
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Exec

open FullForestAuth
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Spec (Guard)
open Dregg2.Exec.AuthModes (AuthMode AuthContext unchecked_unconstrained_admits)
open Dregg2.Crypto.Reference
open Dregg2.Exec (ExecAuth confRights attenuate)

/-- **Carrier record** for the credential-gated call-forest executor. -/
structure GatedForestCarriers where
  digest : Type
  proof : Type
  request : Type
  stmt : Type
  wit : Type
  cellId : Type
  rights : Type
  ctx : Type
  gateway : Type
  bytes : Type
  tag : Type

/-! ## Starbridge — canonical production carriers + witness forests. -/

namespace StarbridgeGated

open Dregg2.Crypto.Reference

instance starbridgeVerifiable : Dregg2.Laws.Verifiable Nat Nat where
  Verify _ _ := true

def starbridgeCarriers : GatedForestCarriers where
  digest := Crypto.Reference.D
  proof := Crypto.Reference.P
  request := Bool
  stmt := Nat
  wit := Nat
  cellId := Label
  rights := ExecAuth
  ctx := Nat
  gateway := Unit
  bytes := Nat
  tag := Nat

abbrev Dg := Crypto.Reference.D
abbrev Pf := Crypto.Reference.P
abbrev Rq := Bool
abbrev St := Nat
abbrev Wt := Nat
abbrev Cx := Nat
abbrev Gw := Unit
abbrev Bt := Nat
abbrev Tg := Nat
/-- The production rights lattice (the REAL `Finset Auth ⊆` order — `granted ≤ held` is now
non-vacuous, unlike the previous `Unit` collapse). -/
abbrev Rt := ExecAuth
abbrev DNodeAuth := NodeAuth Dg Pf Rq St Wt Label Rt Cx Gw Bt Tg
abbrev DForest :=
  FullForestG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Rt) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)
abbrev DChild :=
  FullChildG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Rt) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)

/-- Fully-applied production forest step (`execFullForestG` at the starbridge carriers). -/
noncomputable def execForestG (s : RecChainedState) (f : DForest) : Option RecChainedState :=
  execFullForestG s f

def eraseForestG (f : DForest) : FullForestA :=
  eraseG f

theorem execForestG_erases (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    execFullForestA s (eraseForestG f) = some s' :=
  execFullForestG_erases s s' f h

/-- Childless gated forest = single gated node step. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a <;> rfl

def baseCapCtx : AuthContext Rq St Wt Label Rt Cx Gw :=
  { req := true, customStmt := 0, wit := fun _ => 0
  , registry := fun _ => none, caveatCtx := 150, discharges := fun _ => false
  , graph := fun _ _ => False, consents := fun _ => True, facetOk := true, freshOk := true }

def mkAuth (cred : Authorization Dg Pf) (caveats : List GatedCaveat) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := .unchecked (Guard.all []), capCtx := baseCapCtx
  , caveats := caveats, chain := none, chainCtx := 150, chainDis := fun _ => false }

/-! ### A1 — the REAL-RIGHTS cap-authority leg (the WHAT, now load-bearing).

`mkAuth` pins `capMode := .unchecked (Guard.all [])`, which `authModeAdmits` admits for ALL inputs —
so the proved `granted ≤ held` attenuation theory was proved-but-never-exercised over the wire. Here
we route the delegation edge's `keep`/`parentCap` into a `.capTpDelivered` cap mode whose
`granted := keep.toFinset` and `held := confRights parentCap` over the REAL `ExecAuth = Finset Auth`
lattice. `authModeAdmits (.capTpDelivered ⟨_,_,held,granted⟩ _) = decide (granted.rights ≤ held.rights)
&& facetOk && freshOk`, so a delegation edge that AMPLIFIES (`keep ⊄ parentCap.rights`) makes the WHAT
leg FALSE ⇒ the gate fail-closes ⇒ whole-turn rollback. This makes the attenuation theory load-bearing
at the wire. -/

/-- The target label of a positional `Cap` (`null` targets the agent cell `0` by convention; only
the rights matter for the attenuation check). -/
def capTargetOf : Cap → Label
  | .null         => 0
  | .endpoint t _ => t
  | .node t       => t

/-- Build a `.capTpDelivered` cap mode that gates the delegated `keep` rights against the parent
cap's conferred rights over the real `ExecAuth` lattice. `held := confRights parentCap`,
`granted := keep.toFinset`; admits iff `keep.toFinset ≤ confRights parentCap` (the non-amplifying
discipline `is_attenuation(held, granted)`), with facet/freshness already `true` in `baseCapCtx`. -/
def capModeOfEdge (holder : Label) (keep : List Auth) (parentCap : Cap) :
    AuthMode Rq St Wt Label Rt Cx Gw :=
  .capTpDelivered
    { introducer := holder, recipient := holder
    , held := { target := capTargetOf parentCap, rights := confRights parentCap }
    , granted := { target := capTargetOf parentCap, rights := keep.toFinset } }
    True

/-- A node-auth whose WHAT leg gates on the delegation edge's real-rights attenuation. The WHO
(credential) and caveats are the same as `mkAuth`; only `capMode` is the load-bearing
`capModeOfEdge holder keep parentCap`. -/
def mkAuthCap (cred : Authorization Dg Pf) (caveats : List GatedCaveat)
    (holder : Label) (keep : List Auth) (parentCap : Cap) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := capModeOfEdge holder keep parentCap, capCtx := baseCapCtx
  , caveats := caveats, chain := none, chainCtx := 150, chainDis := fun _ => false }

def goodCred : Authorization Dg Pf := .signature 7 7
def forgedCred : Authorization Dg Pf := .signature 7 8

def trueCaveat : GatedCaveat :=
  { tier := .monotone, check := fun s => decide (0 ≤ s.kernel.bal 0 0) }

def falseCaveat : GatedCaveat :=
  { tier := .monotone, check := fun s => decide (10000 ≤ s.kernel.bal 0 0) }

def goodFullForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .mintA 9 0 1 50
  , [ ({ holder := 0, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
       , sub := ⟨ mkAuth goodCred [trueCaveat], .balanceA ⟨0, 0, 1, 30⟩ 0
                , [ ({ holder := 9, keep := [], parentCap := .endpoint 0 [Auth.read]
                     , sub := ⟨ mkAuth goodCred [trueCaveat], .burnA 9 0 1 50, [] ⟩ } : DChild) ] ⟩ } : DChild) ] ⟩

def forgedCredForestG : DForest :=
  ⟨ mkAuth forgedCred [trueCaveat], .mintA 9 0 1 50, [] ⟩

def falseCaveatForestG : DForest :=
  ⟨ mkAuth goodCred [falseCaveat], .mintA 9 0 1 50, [] ⟩

def launderFullForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .mintA 9 0 1 50
  , [ ({ holder := 9, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read, Auth.write]
       , sub := ⟨ mkAuth goodCred [trueCaveat], .burnA 9 0 0 50, [] ⟩ } : DChild) ] ⟩

/-- Gated forest erasing to the canonical `transferCF` (actor 0, cell 0→1, asset 0). -/
def transferForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .balanceA ⟨0, 0, 1, 30⟩ 0, [] ⟩

/-- Single-node gated forest for production `◇` witnesses: one `emitEvent`, balance-neutral. -/
def logBumpForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .emitEventA 0 0 0 0, [] ⟩

theorem transferForestG_turn_delta_zero (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG transferForestG).map Prod.snd) b = 0 := by
  simp only [turnLedgerDeltaAsset, lowerForestG, lowerChildrenG, transferForestG, ledgerDeltaAsset,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem logBumpForestG_turn_delta_zero (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG logBumpForestG).map Prod.snd) b = 0 := by
  simp only [turnLedgerDeltaAsset, lowerForestG, lowerChildrenG, logBumpForestG, ledgerDeltaAsset,
    List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]

/-- The log-bump forest shares the good-credential root auth with `goodFullForestG`. -/
theorem logBumpForestG_auth_eq : logBumpForestG.auth = goodFullForestG.auth := rfl

theorem logBumpForestG_credential_valid : credentialValidG logBumpForestG.auth = true := by
  unfold logBumpForestG credentialValidG mkAuth goodCred
  decide

theorem logBumpForestG_cap_authority : capAuthorityG logBumpForestG.auth = true := by
  unfold logBumpForestG capAuthorityG mkAuth
  exact unchecked_unconstrained_admits (Guard.all []) baseCapCtx (fun _ _ => by simp)

theorem logBumpForestG_caveats_fma0 : caveatsDischarged logBumpForestG.auth fma0 = true := by
  unfold logBumpForestG caveatsDischarged mkAuth trueCaveat baseCapCtx chainGateG fma0
  simp only [List.all_cons, List.all_nil, Bool.and_true, GatedCaveat.holds, decide_eq_true_eq]
  norm_num

theorem logBumpForestG_revocation_fma0 : revocationGate logBumpForestG.auth fma0 = true := by
  unfold logBumpForestG revocationGate mkAuth fma0
  simp

/-- Gate legs for the log-bump witness forest at `fma0`. -/
theorem logBumpForestG_gateOK : gateOK logBumpForestG.auth fma0 = true := by
  unfold gateOK
  simp only [Bool.and_eq_true, logBumpForestG_credential_valid, logBumpForestG_cap_authority,
             logBumpForestG_caveats_fma0, logBumpForestG_revocation_fma0]
  trivial

theorem transferForestG_auth_eq : transferForestG.auth = logBumpForestG.auth := rfl

theorem transferForestG_gateOK : gateOK transferForestG.auth fma0 = true := by
  rw [transferForestG_auth_eq]
  exact logBumpForestG_gateOK

theorem transferForestG_erase_eq :
    eraseForestG transferForestG = ⟨.balanceA ⟨0, 0, 1, 30⟩ 0, []⟩ := rfl

theorem transferForestG_kernel_commits :
    (execFullForestA fma0 (eraseForestG transferForestG)).isSome := by decide

theorem transferForestG_commits : (execFullForestG fma0 transferForestG).isSome := by
  rcases Option.isSome_iff_exists.mp transferForestG_kernel_commits with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, transferForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0)).mpr
    ⟨transferForestG_gateOK, hs'⟩
  simpa [hga]

/-- The erased log-bump action commits at `fma0` (authority-free emit on a live cell). -/
theorem logBump_erase_commits : (execFullForestA fma0 (eraseG logBumpForestG)).isSome := by decide

/-- The production log-bump forest COMMITS at `fma0` (gate + credential + caveat all pass). -/
theorem logBumpForestG_commits : (execFullForestG fma0 logBumpForestG).isSome := by
  rcases Option.isSome_iff_exists.mp logBump_erase_commits with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, logBumpForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuth goodCred [trueCaveat]) (.emitEventA 0 0 0 0)).mpr
    ⟨logBumpForestG_gateOK, hs'⟩
  simpa [hga]

/-- The committed post-state lands exactly one receipt. -/
theorem logBumpForestG_log_one {s' : RecChainedState}
    (h : execFullForestG fma0 logBumpForestG = some s') : s'.log.length = 1 := by
  have herase := execFullForestG_erases fma0 s' logBumpForestG h
  have hlen : (execFullForestA fma0 (eraseG logBumpForestG)).map (fun s => s.log.length) = some 1 := by
    decide
  rw [herase] at hlen
  simpa using hlen

#guard ((execFullForestG fma0 logBumpForestG).isSome)
#guard ((execFullForestG fma0 logBumpForestG).map (fun s => s.log.length) == some 1)

#guard ((execFullForestG fmaDeleg goodFullForestG).isSome)
#guard (turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 0) == 0
#guard (turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 1) == 0
#guard ((execFullForestG fmaDeleg goodFullForestG).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)
#guard ((execFullForestG fmaDeleg forgedCredForestG).isSome) == false
#guard (credentialValidG forgedCredForestG.auth) == false
#guard (credentialValidG goodFullForestG.auth)
#guard ((execFullForestG fmaDeleg falseCaveatForestG).isSome) == false
#guard (caveatsDischarged falseCaveatForestG.auth fmaDeleg) == false
#guard (caveatsDischarged goodFullForestG.auth fmaDeleg)
#guard ((execFullForestG fmaDeleg launderFullForestG).isSome)
#guard (turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 0) == -50
#guard (turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 1) == 50
#guard ((execFullForestG fmaDeleg launderFullForestG).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (55, 57)
#guard ((execFullForestA fmaDeleg (eraseG goodFullForestG)).isSome)
#guard (((execFullForestG fmaDeleg goodFullForestG).map (fun s => s.log.length)
        == (execFullForestA fmaDeleg (eraseG goodFullForestG)).map (fun s => s.log.length)))
#guard ((execFullForestG fmaDeleg goodFullForestG).map
        (fun s' => decide (fmaDeleg.log.length < s'.log.length)) == some true)

/-! ### A1 — the WHAT leg (`capAuthorityG`) now has REAL TEETH at the wire.

The two forests below share EVERYTHING — the same genuine credential, the same caveat, the same
`emitEvent` action — differing ONLY in the delegated edge's `keep`/`parentCap`. The non-amplifying
one (`keep = [read]` against a parent cap `.endpoint 0 [read,write]`) COMMITS; the amplifying one
(`keep = [read,write]` against a parent cap `.endpoint 0 [read]`) is REJECTED by `capAuthorityG`
(`granted ⊄ held` over `ExecAuth`) ⇒ the whole forest rolls back. The previous `.unchecked` cap mode
admitted BOTH. This is the same-wire contrast proving the proved `granted ≤ held` attenuation is now
load-bearing — no longer admit-by-construction. -/

/-- A non-amplifying delegated node: `keep = [read]` ⊆ parent rights `[read, write]`. Its WHAT leg
ADMITS (`[read].toFinset ≤ {read, write}`). Balance-neutral `emitEvent`. -/
def capOkForestG : DForest :=
  ⟨ mkAuthCap goodCred [trueCaveat] 0 [Auth.read] (.endpoint 0 [Auth.read, Auth.write])
  , .emitEventA 0 0 0 0, [] ⟩

/-- An AMPLIFYING delegated node: `keep = [read, write]` ⊄ parent rights `[read]`. Its WHAT leg
REJECTS (`{read, write} ⊄ {read}`). The ONLY difference from `capOkForestG` is the cap data. -/
def capAmplifyForestG : DForest :=
  ⟨ mkAuthCap goodCred [trueCaveat] 0 [Auth.read, Auth.write] (.endpoint 0 [Auth.read])
  , .emitEventA 0 0 0 0, [] ⟩

-- The WHAT leg ADMITS the non-amplifying edge but REJECTS the amplifying one:
#guard (capAuthorityG capOkForestG.auth)                  --  true  (keep ⊆ parent)
#guard (capAuthorityG capAmplifyForestG.auth) == false    --  false (keep ⊄ parent: AMPLIFY)
-- ...and the gate (hence the whole forest) follows the WHAT leg — the amplifying turn ROLLS BACK:
#guard ((execFullForestG fma0 capOkForestG).isSome)               --  true  (commits)
#guard ((execFullForestG fma0 capAmplifyForestG).isSome) == false --  false (gate rejects ⇒ rollback)
-- The two differ ONLY in cap data (same credential ⇒ same WHO leg passes for both):
#guard (credentialValidG capOkForestG.auth)
#guard (credentialValidG capAmplifyForestG.auth)
-- An EXACT-rights (equal, not strict subset) edge also admits (reflexivity of attenuation):
#guard (capAuthorityG (mkAuthCap goodCred [trueCaveat] 0 [Auth.read, Auth.write]
          (.endpoint 0 [Auth.read, Auth.write])))  --  true

theorem capOkForestG_what_admits : capAuthorityG capOkForestG.auth = true := by
  show capAuthorityG (mkAuthCap goodCred [trueCaveat] 0 [Auth.read]
        (.endpoint 0 [Auth.read, Auth.write])) = true
  unfold capAuthorityG mkAuthCap capModeOfEdge baseCapCtx confRights capTargetOf
  simp only [AuthModes.authModeAdmits]
  decide

theorem capAmplifyForestG_what_rejects : capAuthorityG capAmplifyForestG.auth = false := by
  show capAuthorityG (mkAuthCap goodCred [trueCaveat] 0 [Auth.read, Auth.write]
        (.endpoint 0 [Auth.read])) = false
  unfold capAuthorityG mkAuthCap capModeOfEdge baseCapCtx confRights capTargetOf
  simp only [AuthModes.authModeAdmits]
  decide

/-- The amplifying forest is REJECTED by the full gate (the WHAT leg fail-closes the conjunction). -/
theorem capAmplifyForestG_gate_rejects : gateOK capAmplifyForestG.auth fma0 = false := by
  unfold gateOK
  rw [capAmplifyForestG_what_rejects]
  simp

/-- Hence the amplifying forest does NOT commit (`execFullForestG = none`). -/
theorem capAmplifyForestG_rolls_back : execFullForestG fma0 capAmplifyForestG = none := by
  unfold capAmplifyForestG
  show (match execFullAGated fma0 _ (.emitEventA 0 0 0 0) with
        | some s' => execFullChildrenG _ s' ([] : List DChild)
        | none    => none) = none
  rw [execFullAGated]
  have : gateOK capAmplifyForestG.auth fma0 = false := capAmplifyForestG_gate_rejects
  unfold capAmplifyForestG at this
  simp only [this]
  rfl

#assert_axioms capAmplifyForestG_what_rejects
#assert_axioms capOkForestG_what_admits
#assert_axioms capAmplifyForestG_gate_rejects
#assert_axioms capAmplifyForestG_rolls_back

end StarbridgeGated

end Dregg2.Exec