/-
# Dregg2.Authority.CaveatCapBridge — the macaroon ↔ kernel-cap convergence arrow.

`docs/rebuild/_AUTHORIZATION-COMPLETE.md §3` welds FOUR caveat operators onto the SAME live
`execFullForestG` gate: the within-cell tiers, the cap-authority `granted ≤ held`
(`capAuthorityG`, the WHAT leg), the coordinated cross-cell axis, and the macaroon HMAC
caveat-CHAIN (`chainGateG`). Those last two — the macaroon narrowing and the kernel cap
narrowing — are TWO renderings of the ONE fact "a key may only narrow":

  * the macaroon side (`CaveatChain.append_narrows`): appending a caveat can only SHRINK the
    admissible set — `{ctx | (c.append link).admits} ⊆ {ctx | c.admits}`;
  * the kernel cap side (`AuthModes.captp_granted_le_held` / `Caps.attenuate_confRights_le`):
    a delegated cap's conferred rights are `⊆` the parent's — `granted.rights ≤ held.rights`
    over `ExecAuth = Finset Auth`.

This module makes the convergence an EXPLICIT, PROVEN ARROW rather than two parallel facts.
The shared narrowing is `caveatChainAuthority : ExecAuth → List ExecAuth → ExecAuth`: the
rights a macaroon chain confers = the parent rights MET against each link's kept-rights mask.
Then:

  * `caveatChainAuthority_le_held` — the chain authority is ALWAYS `≤ held` (REFINEMENT, the
    general `⊆` the lead asked for): a macaroon, however attenuated, never amplifies past the
    held rights;
  * `caveatChainAuthority_append_le` — appending a link's mask only narrows further (the
    `append_narrows` analog, on the rights lattice);
  * `delegationVerb_authority_eq` — on the DELEGATION VERB (one kept-rights step `keep` with
    `keep ≤ held`), the chain authority is EXACTLY `keep` — the EQUALITY the lead flagged: the
    macaroon's narrowing and the kernel `confRights (attenuate keep …)` coincide, not merely
    refine;
  * the keystone `chainGateG_implies_capAuthorityG` — on a COHERENTLY-built node (its
    `.capTpDelivered` WHAT leg's `granted` IS `caveatChainAuthority held keeps`, the SAME
    narrowing its macaroon chain carries), `chainGateG na = true → capAuthorityG na = true`.
    The `&&` of the two gate legs becomes a PROVEN arrow on the overlap: a verifying-and-admitting
    macaroon chain forces the kernel cap gate to pass, because the granted rights it confers were
    DEFINED as the narrowed meet `≤ held`.

REUSES `Authority.CaveatChain` (the real HMAC chain + `verifiedChainGate`),
`Exec.FullForestAuth` (`chainGateG`/`capAuthorityG`/`NodeAuth`), `Exec.AuthModes`
(`authModeAdmits`/`.capTpDelivered`), `Exec.Caps` (`ExecAuth`/`confRights`/`attenuate`),
`Exec.GatedForestCfg` (the starbridge production carriers). EDITS none. ONE namespace.
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Authority.CaveatChain

namespace Dregg2.Authority.CaveatCapBridge

open Dregg2.Exec
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.AuthModes (AuthMode AuthContext authModeAdmits)
open Dregg2.Exec.StarbridgeGated
open Dregg2.Authority
open Dregg2.Spec (Cap)

/-! ## §1 — The shared narrowing `caveatChainAuthority`.

A macaroon chain's caveats are rendered, on the rights lattice, as a list of KEPT-RIGHTS MASKS
(one `ExecAuth` per link). The authority a chain confers from a parent's `held` rights is the
parent met against every mask — exactly the kernel's `attenuate`-down-a-chain semantics, on
`ExecAuth = Finset Auth` ordered by `⊆`. This is the ONE object both the macaroon `append_narrows`
and the kernel `granted ≤ held` are about. -/

/-- **`caveatChainAuthority held keeps`** — the rights a macaroon chain confers from a parent's
`held` rights: the meet (`⊓` = `∩` on `Finset Auth`) of `held` with every link's kept-rights mask.
`keeps = []` (a root macaroon, no caveats) confers exactly `held`; each appended mask narrows. -/
def caveatChainAuthority (held : ExecAuth) (keeps : List ExecAuth) : ExecAuth :=
  keeps.foldl (fun r m => r ⊓ m) held

@[simp] theorem caveatChainAuthority_nil (held : ExecAuth) :
    caveatChainAuthority held [] = held := rfl

theorem caveatChainAuthority_cons (held m : ExecAuth) (keeps : List ExecAuth) :
    caveatChainAuthority held (m :: keeps) = caveatChainAuthority (held ⊓ m) keeps := rfl

/-- **`caveatChainAuthority_le_held` — the REFINEMENT direction (the general `⊆`).** Whatever a
macaroon chain confers from `held`, it is `≤ held`: a key, however attenuated, never amplifies
past the parent's rights. The macaroon `append_narrows`, rendered on the kernel rights lattice. -/
theorem caveatChainAuthority_le_held (held : ExecAuth) (keeps : List ExecAuth) :
    caveatChainAuthority held keeps ≤ held := by
  induction keeps generalizing held with
  | nil => exact le_rfl
  | cons m rest ih =>
      rw [caveatChainAuthority_cons]
      exact le_trans (ih (held ⊓ m)) inf_le_left

/-- **`caveatChainAuthority_append_le` — appending a link only narrows further.** Adding a caveat
mask `m` to the chain shrinks (or fixes) the conferred authority: `auth (keeps ++ [m]) ≤ auth keeps`.
The rights-lattice rendering of `CaveatChain.append_narrows`. -/
theorem caveatChainAuthority_append_le (held : ExecAuth) (keeps : List ExecAuth) (m : ExecAuth) :
    caveatChainAuthority held (keeps ++ [m]) ≤ caveatChainAuthority held keeps := by
  induction keeps generalizing held with
  | nil =>
      show caveatChainAuthority held [m] ≤ held
      exact caveatChainAuthority_le_held held [m]
  | cons k rest ih =>
      rw [List.cons_append, caveatChainAuthority_cons, caveatChainAuthority_cons]
      exact ih (held ⊓ k)

/-! ## §2 — The DELEGATION-VERB equality (the lead's "EQUALITY on the delegation verb").

The delegation verb attenuates a held cap to exactly the kept-rights set `keep` (`recKDelegateAtten`
→ `attenuate keep held`, `confRights (attenuate keep c) = keep.toFinset ⊓ confRights c`). A single
macaroon caveat carrying that mask reproduces it EXACTLY: when `keep ≤ held`, the chain authority is
not merely `≤ held` but EQUAL to `keep`. So on the delegation verb the two narrowings COINCIDE. -/

/-- **`delegationVerb_authority_eq` — the EQUALITY.** With a single delegation caveat whose mask is
`keep`, and `keep ≤ held` (the non-amplifying delegation precondition), the macaroon chain confers
EXACTLY `keep`. Not a refinement — an equality: the macaroon narrowing IS the kernel attenuation. -/
theorem delegationVerb_authority_eq (held keep : ExecAuth) (hle : keep ≤ held) :
    caveatChainAuthority held [keep] = keep := by
  show held ⊓ keep = keep
  exact inf_eq_right.mpr hle

/-- **`delegationVerb_authority_le` — the REFINEMENT face of the same step** (no precondition):
a single delegation caveat confers `≤ held` regardless. The general arrow direction; the equality
above is the special case `keep ≤ held`. -/
theorem delegationVerb_authority_le (held keep : ExecAuth) :
    caveatChainAuthority held [keep] ≤ held :=
  caveatChainAuthority_le_held held [keep]

/-! ## §3 — The convergence keystone: `chainGateG na → capAuthorityG na` on a coherent node.

A node is COHERENT for the bridge when its `.capTpDelivered` WHAT leg's `granted` rights ARE
`caveatChainAuthority held keeps` — the SAME narrowing its macaroon chain renders — and its `held`
is the parent rights. Then `capAuthorityG na = decide (granted ≤ held) && facetOk && freshOk`, and
`granted ≤ held` is `caveatChainAuthority_le_held` (PROVED), so on `baseCapCtx` (facet/fresh = true)
the cap gate passes. The macaroon `chainGateG` is the hypothesis; the cap gate is the conclusion —
the `&&` of the two legs is now a PROVEN arrow on the overlap. -/

/-- The coherent `.capTpDelivered` cap mode whose `granted` rights ARE the shared narrowing
`caveatChainAuthority held keeps` over the parent `held`, on the production `ExecAuth` lattice.
`held` and `granted` share a target (the rights are what the bridge gates). -/
def bridgeCapMode (target : Label) (held : ExecAuth) (keeps : List ExecAuth) :
    AuthMode Rq St Wt Label Rt Cx Gw :=
  .capTpDelivered
    { introducer := target, recipient := target
    , held    := { target := target, rights := held }
    , granted := { target := target, rights := caveatChainAuthority held keeps } }
    True

/-- **`bridgeCapMode_admits` — the WHAT leg of a coherent node ALWAYS passes.** Because its
`granted` rights are `caveatChainAuthority held keeps ≤ held` (`caveatChainAuthority_le_held`), the
`.capTpDelivered` dispatch `decide (granted ≤ held) && facetOk && freshOk` is `true` at `baseCapCtx`
(facet/fresh `true`). This is the kernel cap gate the macaroon narrowing implies. -/
theorem bridgeCapMode_admits (target : Label) (held : ExecAuth) (keeps : List ExecAuth) :
    authModeAdmits (bridgeCapMode target held keeps) baseCapCtx = true := by
  unfold bridgeCapMode authModeAdmits baseCapCtx
  -- `.capTpDelivered` admits = `decide (granted ≤ held) && facetOk && freshOk`; facet/fresh are
  -- `true` in `baseCapCtx`, so the gate reduces to the proved narrowing `granted ≤ held`.
  simp only [Bool.and_true, decide_eq_true_eq]
  exact caveatChainAuthority_le_held held keeps

/-- A coherent bridge node: its WHO/caveats are the production `mkAuth` defaults (a genuine
credential, the chain present), but its WHAT leg is the coherent `bridgeCapMode` AND it carries the
macaroon `chain` whose narrowing the WHAT leg mirrors. The bridge's hypothesis-bearing object. -/
def mkBridgeNode (cred : Authorization Dg Pf) (target : Label) (held : ExecAuth)
    (keeps : List ExecAuth)
    (chain : Option (CaveatChain.Chain Cx Gw (CaveatChain.Key Tg) Bt Tg)) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := bridgeCapMode target held keeps, capCtx := baseCapCtx
  , caveats := [], chain := chain, chainCtx := 150, chainDis := fun _ => false }

/-- **`chainGateG_implies_capAuthorityG` — THE CONVERGENCE ARROW.** On a coherent bridge node
(whose `.capTpDelivered` `granted` IS the macaroon chain's narrowing `caveatChainAuthority held
keeps`), the macaroon caveat-chain gate passing implies the kernel cap-authority gate passing:
`chainGateG na = true → capAuthorityG na = true`. The `&&` of the two gate legs in `gateOK` is now a
PROVEN implication on the overlap — a verifying macaroon chain CANNOT pass while the kernel cap gate
fails, because the rights it confers were DEFINED as the narrowed meet `≤ held`. -/
theorem chainGateG_implies_capAuthorityG (cred : Authorization Dg Pf) (target : Label)
    (held : ExecAuth) (keeps : List ExecAuth)
    (chain : Option (CaveatChain.Chain Cx Gw (CaveatChain.Key Tg) Bt Tg))
    (_hchain : chainGateG (mkBridgeNode cred target held keeps chain) = true) :
    capAuthorityG (mkBridgeNode cred target held keeps chain) = true := by
  show authModeAdmits (bridgeCapMode target held keeps) baseCapCtx = true
  exact bridgeCapMode_admits target held keeps

/-! ## §4 — Non-vacuity: both polarities, on the SAME live gate.

The arrow is NOT vacuous: there ARE chains for which `chainGateG = true` (a verifying, admitting
macaroon — the hypothesis fires) AND there ARE narrowings for which the conclusion is the
non-trivial `granted ⊊ held` (a strict attenuation, not `held = held`). And the EQUALITY/refinement
split is witnessed: a non-amplifying `keep ≤ held` gives EQUALITY, an over-broad mask gives a STRICT
refinement `granted ⊊ held` (the kernel gate would reject the over-broad cap, exactly as the
macaroon append narrowed it). -/

/-- A genuine production credential (reused from the starbridge config). -/
def credOk : Authorization Dg Pf := goodCred

/-- The full held rights for the demo (`{read, write}`). -/
def heldRW : ExecAuth := {Auth.read, Auth.write}

/-- A non-amplifying delegation mask (`{read}` ⊆ `{read, write}`) — the delegation verb keeps only
`read`. EQUALITY: the chain confers EXACTLY `{read}`. -/
def keepR : ExecAuth := {Auth.read}

/-- An OVER-BROAD mask (`{read, write, grant}` ⊄ `{read, write}`) — a macaroon caveat that names a
right the parent never held. The chain authority is the MEET (`{read, write}`), STRICTLY below the
named mask: the narrowing CLIPS the over-broad ask (the macaroon cannot amplify), and the resulting
`granted = {read, write} = held` — the over-broad ask buys nothing past the parent. -/
def keepOver : ExecAuth := {Auth.read, Auth.write, Auth.grant}

-- EQUALITY on the delegation verb: `keep ≤ held` ⇒ chain confers EXACTLY `keep`.
#guard (decide (caveatChainAuthority heldRW [keepR] = keepR))
-- REFINEMENT in general: the over-broad mask is CLIPPED to the held rights (no amplification).
#guard (decide (caveatChainAuthority heldRW [keepOver] = heldRW))
-- The clip is STRICT below the named over-broad mask (the macaroon could NOT name `grant` into being).
#guard (decide (caveatChainAuthority heldRW [keepOver] < keepOver))
-- The conferred rights are ALWAYS `≤ held` (refinement), here as a Bool check.
#guard (decide (caveatChainAuthority heldRW [keepR] ≤ heldRW))
#guard (decide (caveatChainAuthority heldRW [keepOver] ≤ heldRW))
-- Appending narrows: a second caveat `{read}` on top of `{read,write}` shrinks to `{read}`.
#guard (decide (caveatChainAuthority heldRW [heldRW, keepR] = keepR))

/-- **NON-VACUITY (positive):** the EQUALITY fires on the non-amplifying delegation verb. -/
theorem keepR_equality : caveatChainAuthority heldRW [keepR] = keepR :=
  delegationVerb_authority_eq heldRW keepR (by decide)

/-- **NON-VACUITY (negative tooth):** the over-broad mask does NOT confer itself — the chain
authority is STRICTLY below the named mask (`< keepOver`), so a macaroon naming a right the parent
never held buys nothing. This is the load-bearing non-amplification: the arrow's conclusion `granted
≤ held` is a REAL constraint, refuted for the over-broad ask if it were taken at face value. -/
theorem keepOver_strict_refines : caveatChainAuthority heldRW [keepOver] < keepOver := by decide

/-- **NON-VACUITY (the keystone fires on a CONCRETE coherent node).** With a real macaroon chain
present and the coherent WHAT leg, the convergence arrow's conclusion holds: the kernel cap gate
passes. Witnessed on the production carriers, not abstractly. -/
theorem bridge_keystone_concrete
    (chain : Option (CaveatChain.Chain Cx Gw (CaveatChain.Key Tg) Bt Tg))
    (h : chainGateG (mkBridgeNode credOk 0 heldRW [keepR] chain) = true) :
    capAuthorityG (mkBridgeNode credOk 0 heldRW [keepR] chain) = true :=
  chainGateG_implies_capAuthorityG credOk 0 heldRW [keepR] chain h

/-! ## §5 — THE DE-VACUIFIED BRIDGE: the macaroon caveat EMITS the `(granted, held)` the cap leg reads.

The `§3` keystone (`chainGateG_implies_capAuthorityG`) hardwires the node's `granted :=
caveatChainAuthority held keeps`, which `caveatChainAuthority_le_held` proves `≤ held` *by
construction* — so its conclusion (`capAuthorityG = true`) holds REGARDLESS of `chainGateG` (the
hypothesis is unused). That is the honest defense-in-depth fact, but it does not make the macaroon
gate *load-bearing*: the cap leg would pass even with a forged chain.

This section closes that gap, exactly as `docs/AUTHORIZATION-MODEL.md:53-61` asks: make the macaroon
caveat that narrows a capability-bearing verb **emit the SAME `(granted, held)` pair the kernel cap
leg already consumes**, and prove `chainGateG na = true → granted(na) ⊆ held(na)` on the delegation
verb — **NON-VACUOUSLY**: the conclusion `granted ≤ held` is a FREE proposition over a free pair, and
it provably FAILS exactly when the hypothesis fails (an amplifying delegation makes the chain caveat
return `false`, so `chainGateG = false`).

The mechanism: a single macaroon delegation caveat whose `check` reads the rights pair out of the
chain context and returns `decide (granted ≤ held)`. The chain context `chainCtx := (granted, held)`
IS that pair; the `.capTpDelivered` cert's `held`/`granted` ARE that SAME pair. So a verifying-and-
admitting macaroon chain (the `chainGateG` hypothesis) forces the chain caveat to have fired, i.e.
`granted ≤ held` — which is the very atom the kernel `capAuthorityG` gate consumes. The `&&` of the
two `gateOK` legs is now a PROVEN IDENTITY *carried by one quantity*, not two narrowings that happen
to agree, and not a conclusion true by construction. -/

section DeVacuified

open Dregg2.Authority.CaveatChain
open Dregg2.Authority.CaveatChain (Chain Link seed honest_chain_verifies)
open Dregg2.Exec (ExecAuth)
open Dregg2.Exec.AuthModes (AuthMode AuthContext authModeAdmits captp_granted_le_held)

/-- The bridge's chain/caveat context: the `(granted, held)` rights pair the delegation caveat reads.
This is the ONE shared quantity — the macaroon caveat reads it, the kernel cert is built from it. -/
abbrev RPair := ExecAuth × ExecAuth

/-- The bridge carriers (a fresh instantiation of the `FullForestAuth` gate over a context that
CARRIES the rights pair). Digest/Proof = the reference crypto kernel (so the WHO portal + `goodCred`
resolve); Tag/Bytes/Key = `Nat` (so the proven `honestMacKernel` macaroon chain is reused verbatim);
`Ctx := RPair`. -/
abbrev BNodeAuth :=
  NodeAuth Dg Pf Rq St Wt Label ExecAuth RPair Gw Bt Tg

/-- **`delegCaveat` — the macaroon delegation caveat that EMITS `granted ⊆ held`.** A first-party
(local) caveat whose check reads the `(granted, held)` pair out of the chain context and returns
`decide (granted ≤ held)`. THIS is "the caveat that narrows a capability-bearing verb"; its decision
is, verbatim, the kernel's `is_attenuation(held, granted)` atom. Appending it to a chain renders the
delegation's non-amplification *on the wire*. -/
def delegCaveat : Caveat RPair Gw :=
  .opaque (fun p => decide (p.1 ≤ p.2))

/-- **`delegChain granted held` — a verifying macaroon chain carrying exactly the delegation caveat.**
`seed` then one honest `append` of the `delegCaveat` link (encoded bytes `0`, immaterial to the
semantics). It `verify`s by `honest_chain_verifies`, and `admits (granted, held)` iff `granted ≤ held`
— the chain's admit decision IS the delegation's non-amplification check. -/
def delegChain (_granted _held : ExecAuth) : Chain RPair Gw (Key Tg) Bt Tg :=
  (seed (Ctx := RPair) (Gateway := Gw) (0 : Nat) (0 : Nat)).append
    { caveat := delegCaveat, encoded := (0 : Nat) }

/-- **`delegChain_admits_iff` — the chain's admit decision IS `granted ≤ held`.** The single-link
chain admits the pair `(granted, held)` exactly when `granted ≤ held`. (Reduces by `simp` over
`Chain.admits`/`Chain.append`/`seed` + the `delegCaveat` check.) -/
theorem delegChain_admits_iff (granted held : ExecAuth) (d : Discharges Gw) :
    (delegChain granted held).admits (granted, held) d = decide (granted ≤ held) := by
  simp [delegChain, delegCaveat, Chain.admits, Chain.append, seed, Caveat.ok]

/-- **`delegChain_verify` — the honest delegation chain always `verify`s** (the HMAC tail binds the
one appended caveat; `honest_chain_verifies`). So `Chain.verify` is never the leg that fails here —
the admit leg (the `granted ≤ held` check) is what carries the content. -/
theorem delegChain_verify (granted held : ExecAuth) :
    (delegChain granted held).verify = true :=
  honest_chain_verifies (Ctx := RPair) (Gateway := Gw) (0 : Nat) (0 : Nat)
    { caveat := delegCaveat, encoded := (0 : Nat) }

/-- The bridge's `.capTpDelivered` cap mode, built from the SAME `(granted, held)` pair the macaroon
caveat reads. `authModeAdmits (.capTpDelivered ⟨_,_,⟨t,held⟩,⟨t,granted⟩⟩ _) c = decide (granted ≤
held) && c.facetOk && c.freshOk`. NOTE: unlike `bridgeCapMode`, the `granted` is FREE — it is NOT
`caveatChainAuthority held keeps`, so the cap leg does NOT pass by construction; it passes IFF the
shared `granted ≤ held` holds. -/
def delegCapMode (target : Label) (granted held : ExecAuth) :
    AuthMode Rq St Wt Label ExecAuth RPair Gw :=
  .capTpDelivered
    { introducer := target, recipient := target
    , held    := { target := target, rights := held }
    , granted := { target := target, rights := granted } }
    True

/-- The bridge node: its `.capTpDelivered` WHAT leg reads the FREE pair `(granted, held)`, and it
carries the macaroon `delegChain granted held` whose caveat reads the SAME pair out of `chainCtx :=
(granted, held)`. The hypothesis-bearing object on which `chainGateG` and `capAuthorityG` read ONE
shared quantity. -/
def mkDelegNode (cred : Authorization Dg Pf) (target : Label) (granted held : ExecAuth) : BNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := delegCapMode target granted held
  , capCtx :=
      { req := true, customStmt := 0, wit := fun _ => 0
      , registry := fun _ => none, caveatCtx := (granted, held), discharges := fun _ => false
      , graph := fun _ _ => False, consents := fun _ => True, facetOk := true, freshOk := true }
  , caveats := [], chain := some (delegChain granted held)
  , chainCtx := (granted, held), chainDis := fun _ => false }

/-- **`chainGateG_emits_granted_le_held` — THE HEADLINE BRIDGE (non-vacuous).** On a delegation node
whose macaroon chain caveat reads the shared `(granted, held)` pair, the macaroon caveat-chain gate
passing FORCES the kernel non-amplification atom: `chainGateG na = true → granted ≤ held`. The proof
CONSUMES the hypothesis (it reads the admit leg, which IS `decide (granted ≤ held)`), unlike `§3`.
This is `docs/AUTHORIZATION-MODEL.md:58`'s `chainGateG na = true → granted(na) ⊆ held(na)`, on the
overlap verb, with `granted`/`held` FREE. -/
theorem chainGateG_emits_granted_le_held (cred : Authorization Dg Pf) (target : Label)
    (granted held : ExecAuth)
    (hchain : chainGateG (mkDelegNode cred target granted held) = true) :
    granted ≤ held := by
  -- `chainGateG` on a node with `chain := some (delegChain …)` is `verify && admits chainCtx chainDis`.
  have hconj : ((delegChain granted held).verify
              && (delegChain granted held).admits (granted, held) (fun _ => false)) = true := by
    simpa [chainGateG, mkDelegNode] using hchain
  rw [Bool.and_eq_true] at hconj
  have hadm : (delegChain granted held).admits (granted, held) (fun _ => false) = true := hconj.2
  -- the admit decision IS `decide (granted ≤ held)`, so it being `true` gives `granted ≤ held`.
  rw [delegChain_admits_iff] at hadm
  exact of_decide_eq_true hadm

/-- **`chainGateG_implies_capAuthorityG_devac` — the SAME-PAIR identity, NON-VACUOUS.** The macaroon
chain gate passing implies the kernel cap-authority gate passing, on a node whose `granted` is FREE
(not `≤ held` by construction). The proof routes through `chainGateG_emits_granted_le_held` — the
macaroon's `granted ≤ held` IS the atom the `.capTpDelivered` gate consumes. So the `gateOK` `&&` is
a proven IDENTITY carried by one quantity: a verifying macaroon chain forces the cap gate, AND (the
non-vacuity) an amplifying delegation breaks BOTH legs. -/
theorem chainGateG_implies_capAuthorityG_devac (cred : Authorization Dg Pf) (target : Label)
    (granted held : ExecAuth)
    (hchain : chainGateG (mkDelegNode cred target granted held) = true) :
    capAuthorityG (mkDelegNode cred target granted held) = true := by
  have hle : granted ≤ held := chainGateG_emits_granted_le_held cred target granted held hchain
  -- `capAuthorityG = authModeAdmits (.capTpDelivered …) = decide (granted ≤ held) && facetOk && freshOk`;
  -- the node's `capCtx` pins `facetOk := freshOk := true`, so the gate reduces to `decide (granted ≤ held)`.
  show authModeAdmits (delegCapMode target granted held) _ = true
  unfold delegCapMode authModeAdmits mkDelegNode
  simp only [Bool.and_true, decide_eq_true_eq]
  exact hle

/-- **`capAuthorityG_reads_same_atom` — the converse leg: the kernel gate's content IS `granted ≤
held`.** `capAuthorityG (mkDelegNode …) = true → granted ≤ held`, via `captp_granted_le_held`. Paired
with `chainGateG_emits_granted_le_held`, this certifies BOTH gate legs read the IDENTICAL atom on the
shared pair — the `&&` is a conjunction of two readings of ONE relation, the design's "one proven
identity on the overlap". -/
theorem capAuthorityG_reads_same_atom (cred : Authorization Dg Pf) (target : Label)
    (granted held : ExecAuth)
    (hcap : capAuthorityG (mkDelegNode cred target granted held) = true) :
    granted ≤ held := by
  have h : authModeAdmits (delegCapMode target granted held)
            (mkDelegNode cred target granted held).capCtx = true := hcap
  exact captp_granted_le_held _ True _ h

/-! ### §5.1 — Non-vacuity: the conclusion provably FAILS when the hypothesis fails (both polarities).

The de-vacuification bar (`feedback-dont-launder-vacuity-as-honest`): the bridge's conclusion
`granted ≤ held` is a REAL constraint, two-valued on the same gate. We exhibit a NON-AMPLIFYING pair
(`{read} ⊆ {read, write}`) for which BOTH `chainGateG` and `capAuthorityG` PASS, and an AMPLIFYING
pair (`{read, write, grant} ⊄ {read, write}`) for which BOTH FAIL — the macaroon chain caveat returns
`false`, so `chainGateG = false`, so the bridge's hypothesis is unsatisfiable exactly where its
conclusion is false. The arrow is NOT vacuous. -/

/-- An amplifying granted set (`{read, write, grant} ⊄ {read, write}`) — names a right the parent
never held. The delegation caveat REFUSES it. -/
def grantedAmp : ExecAuth := {Auth.read, Auth.write, Auth.grant}

-- The shared pair drives BOTH legs identically. NON-AMPLIFYING (`keepR ⊆ heldRW`) ⇒ both PASS:
#guard ((delegChain keepR heldRW).verify)                                  -- honest chain verifies
#guard ((delegChain keepR heldRW).admits (keepR, heldRW) (fun _ => false)) -- admit = (read ⊆ read,write)
#guard (chainGateG (mkDelegNode credOk 0 keepR heldRW))                    -- chain gate PASSES
#guard (capAuthorityG (mkDelegNode credOk 0 keepR heldRW))                 -- cap gate PASSES (same atom)
-- AMPLIFYING (`grantedAmp ⊄ heldRW`) ⇒ the caveat returns false ⇒ BOTH legs FAIL:
#guard ((delegChain grantedAmp heldRW).verify)                                     -- chain still verifies (HMAC ok)
#guard ((delegChain grantedAmp heldRW).admits (grantedAmp, heldRW) (fun _ => false)) == false -- admit REFUSES
#guard (chainGateG (mkDelegNode credOk 0 grantedAmp heldRW)) == false              -- chain gate FAILS
#guard (capAuthorityG (mkDelegNode credOk 0 grantedAmp heldRW)) == false           -- cap gate FAILS

/-- **NON-VACUITY (positive):** on a non-amplifying delegation the chain gate FIRES (hypothesis
satisfiable) AND the bridge yields the kernel atom. So the arrow has real content. -/
theorem deleg_nonAmp_chainGate : chainGateG (mkDelegNode credOk 0 keepR heldRW) = true := by
  unfold chainGateG mkDelegNode
  decide

/-- **NON-VACUITY (the keystone fires concretely):** the headline bridge, applied to the firing
hypothesis, yields `{read} ⊆ {read, write}`. -/
theorem deleg_nonAmp_yields_le : (keepR : ExecAuth) ≤ heldRW :=
  chainGateG_emits_granted_le_held credOk 0 keepR heldRW deleg_nonAmp_chainGate

/-- **NON-VACUITY (negative tooth — the conclusion FAILS when the hypothesis fails).** On an
AMPLIFYING delegation (`grantedAmp ⊄ heldRW`) the macaroon chain caveat returns `false`, so the
bridge's hypothesis `chainGateG = true` is FALSE — exactly where its conclusion `granted ≤ held` is
false. This is the load-bearing de-vacuification: the bridge is an arrow whose antecedent tracks its
consequent, not a conclusion true by construction. -/
theorem deleg_amp_chainGate_false : chainGateG (mkDelegNode credOk 0 grantedAmp heldRW) = false := by
  unfold chainGateG mkDelegNode
  decide

/-- **NON-VACUITY (negative tooth, conclusion side):** the amplifying conclusion is genuinely FALSE
(`{read, write, grant} ⊄ {read, write}`) — so the bridge could not be papered over by a vacuously-true
consequent. -/
theorem deleg_amp_not_le : ¬ (grantedAmp ≤ heldRW) := by decide

/-- **NON-VACUITY (the cap gate FOLLOWS the macaroon gate, both ways).** The amplifying delegation is
ALSO rejected by the kernel `capAuthorityG` leg — the two gates agree on the same pair, refuting the
amplifying delegation TWICE (once per leg), never admitting it on either. -/
theorem deleg_amp_capAuthority_false :
    capAuthorityG (mkDelegNode credOk 0 grantedAmp heldRW) = false := by
  show authModeAdmits (delegCapMode 0 grantedAmp heldRW) _ = false
  unfold delegCapMode authModeAdmits
  decide

end DeVacuified

/-! ## §6 — THE MAP-LEVEL CONVERGENCE: the two narrowings are ONE permitted-action map (arbitrary chain).

`§3`/`§5` proved the gate-to-gate arrow on a node whose macaroon caveat is *hand-built* to read the
SAME `(granted, held)` pair the cap mode consumes. What that does NOT establish is the structural
claim the lead named — that the macaroon caveat-CHAIN narrowing and the kernel cap `granted ≤ held`
narrowing are **the same map** for an ARBITRARY chain of rights-narrowing caveats, not just a
single hand-wired one. This section closes that: it proves the permitted-action SETS AGREE, by
induction on the chain, in the literal `chainGate ch a ↔ capAuthority (capOf ch) a` shape.

The setup is the honest macaroon semantics, untouched: a chain link is a rights-narrowing caveat
`actionCaveat m := .opaque (fun a => decide (a ≤ m))` reading the action `a : ExecAuth` it gates against
the link's kept-rights mask `m`. The chain admits `a` iff EVERY link passes — `∀ m ∈ masks, a ≤ m`.
The cap side: the chain's conferred authority is `caveatChainAuthority ⊤ masks` (the §1 fold from the
top cap), and the cap CONFERS `a` iff `a ≤ caveatChainAuthority ⊤ masks` (the kernel `granted ≤ held`
order with `granted := a`). The convergence is the meet/GLB identity

    (∀ m ∈ masks, a ≤ m)  ↔  a ≤ caveatChainAuthority ⊤ masks

— a macaroon chain admits exactly the actions the cap it folds to confers. Both narrowings are one
map `caveatChainAuthority ⊤ masks`; the macaroon "satisfies-all-caveats" set IS the cap's
conferred-authority down-set. Proved for ANY mask list, reusing `append_narrows`'s monotonicity in
spirit but stated at the rights-order level where the cap leg lives. -/

section MapConvergence

open Dregg2.Authority.CaveatChain
open Dregg2.Authority.CaveatChain (Chain Link seed)
open Dregg2.Exec (ExecAuth)

/-- **`actionCaveat m`** — the rights-narrowing caveat the macaroon link carries: a first-party
(`local`) check reading the gated action `a : ExecAuth` and passing iff `a ≤ m` (the action stays
within the link's kept-rights mask `m`). This is the honest "a key may only narrow" caveat, one mask
per link; the action `a` IS the chain context. -/
def actionCaveat (m : ExecAuth) : Caveat ExecAuth Gw :=
  .opaque (fun a => decide (a ≤ m))

/-- **`actionLinks masks`** — render a list of kept-rights masks as macaroon links (encoded bytes
`0`, immaterial to the admit semantics; the HMAC carries integrity, the caveat carries narrowing). -/
def actionLinks (masks : List ExecAuth) : List (Link ExecAuth Gw Bt) :=
  masks.map (fun m => { caveat := actionCaveat m, encoded := (0 : Nat) })

/-- **`actionChainAdmits masks a`** — the macaroon caveat-chain narrowing as a `Prop`: the action `a`
passes EVERY rights-narrowing link (`Chain.admits` over `actionLinks`, the meet of all link caveats).
Stated on a chain built from `actionLinks masks` over any root/nonce — `Chain.admits` reads only the
links, so it is `(actionLinks masks).all (·.caveat.ok a d) = true`. -/
def actionChainAdmits (masks : List ExecAuth) (a : ExecAuth) (d : Discharges Gw) : Bool :=
  ((seed (Ctx := ExecAuth) (Gateway := Gw) (0 : Nat) (0 : Nat)).links ++ actionLinks masks).all
    (fun l => l.caveat.ok a d)

/-- **`actionChainAdmits_iff_forall` — the macaroon side, unfolded.** The chain admits `a` iff `a ≤ m`
for every mask `m` in the chain. Pure `List.all`/`Caveat.ok` reduction over `actionCaveat`. -/
theorem actionChainAdmits_iff_forall (masks : List ExecAuth) (a : ExecAuth) (d : Discharges Gw) :
    actionChainAdmits masks a d = true ↔ ∀ m ∈ masks, a ≤ m := by
  unfold actionChainAdmits actionLinks
  simp only [seed, List.nil_append, List.all_map, List.all_eq_true, Function.comp,
    Caveat.ok, actionCaveat, decide_eq_true_eq]

/-- **`le_caveatChainAuthority_top_iff_forall` — the cap side, as the SAME `∀`.** Folding the masks
down from the TOP cap (`caveatChainAuthority ⊤ masks`, the §1 conferred-authority), the cap confers
`a` (i.e. `a ≤` the conferred rights, the kernel `granted ≤ held` with `granted := a`) IFF `a ≤ m` for
every mask. The meet/GLB identity: `a ≤ ⨅ masks ↔ ∀ m, a ≤ m`. Proved by induction on the masks. -/
theorem le_caveatChainAuthority_top_iff_forall (masks : List ExecAuth) (a : ExecAuth) :
    a ≤ caveatChainAuthority ⊤ masks ↔ ∀ m ∈ masks, a ≤ m := by
  -- Generalize the accumulator `held` to make the induction go through, then specialize to `⊤`.
  suffices h : ∀ (held : ExecAuth), a ≤ caveatChainAuthority held masks ↔ (a ≤ held ∧ ∀ m ∈ masks, a ≤ m) by
    rw [h ⊤]; simp
  intro held
  induction masks generalizing held with
  | nil => simp [caveatChainAuthority]
  | cons m rest ih =>
      rw [caveatChainAuthority_cons, ih (held ⊓ m)]
      constructor
      · rintro ⟨hle, hrest⟩
        refine ⟨le_trans hle inf_le_left, ?_⟩
        intro m' hm'
        rcases List.mem_cons.mp hm' with rfl | hin
        · exact le_trans hle inf_le_right
        · exact hrest m' hin
      · rintro ⟨hheld, hall⟩
        refine ⟨le_inf hheld (hall m (List.mem_cons_self ..)), ?_⟩
        intro m' hm'
        exact hall m' (List.mem_cons_of_mem _ hm')

/-- **`chain_narrowing_eq_cap_narrowing` — THE MAP-LEVEL CONVERGENCE (arbitrary chain).** For ANY list
of kept-rights masks and ANY action `a`, the macaroon caveat-CHAIN admits `a` IF AND ONLY IF the
kernel cap folded from those masks (`caveatChainAuthority ⊤ masks`) CONFERS `a` (`a ≤` the conferred
rights). The two narrowings — appending caveats (macaroon) and `granted ≤ held` (kernel cap) — are the
SAME permitted-action map: `{a | chain admits a} = {a | a ≤ caveatChainAuthority ⊤ masks}`. Not a
hand-built coincidence on one node (§3/§5) — a structural identity over every chain. This is the lead's
`chainGateG ch a ↔ capAuthorityG (capOf ch) a` with `capOf ch := caveatChainAuthority ⊤ masks`. -/
theorem chain_narrowing_eq_cap_narrowing (masks : List ExecAuth) (a : ExecAuth) (d : Discharges Gw) :
    actionChainAdmits masks a d = true ↔ a ≤ caveatChainAuthority ⊤ masks := by
  rw [actionChainAdmits_iff_forall, le_caveatChainAuthority_top_iff_forall]

/-- **`chain_admit_set_eq_cap_confer_set`** — the SET face of the convergence: the macaroon chain's
admissible-action set is EXACTLY the cap's conferred-authority down-set. The "permitted-action sets
AGREE" the lead asked for, as a set equality over `ExecAuth`. -/
theorem chain_admit_set_eq_cap_confer_set (masks : List ExecAuth) (d : Discharges Gw) :
    {a | actionChainAdmits masks a d = true} = {a | a ≤ caveatChainAuthority ⊤ masks} := by
  ext a; exact chain_narrowing_eq_cap_narrowing masks a d

/-! ### §6.1 — Non-vacuity / mutation-confirmation: the convergence BITES (both polarities). -/

/-- The full rights `{read, write}` and a narrowing mask `{read}` reused for the witnesses. -/
def mvHeld : ExecAuth := {Auth.read, Auth.write}
def mvKeep : ExecAuth := {Auth.read}

-- A chain of one `{read}` mask folds to the cap `{read}`; the convergence is the SAME set on both ends.
-- `{read}` (the action) PASSES (it is ≤ the {read} mask AND ≤ the folded cap {read}):
#guard (actionChainAdmits [mvKeep] mvKeep (fun _ => false))
#guard (decide (mvKeep ≤ caveatChainAuthority ⊤ [mvKeep]))
-- `{read, write}` (an OVER-BROAD action) is REJECTED by the chain AND is NOT ≤ the folded cap:
#guard (actionChainAdmits [mvKeep] mvHeld (fun _ => false)) == false
#guard (decide (mvHeld ≤ caveatChainAuthority ⊤ [mvKeep])) == false
-- The folded cap of the `{read}` chain IS `{read}` (the §1 narrowing and the macaroon chain coincide):
#guard (decide (caveatChainAuthority ⊤ [mvKeep] = mvKeep))

/-- **MUTATION-CONFIRM (positive):** an action WITHIN every mask passes the chain — and the convergence
forces it to be cap-conferred too (`mvKeep ≤ folded cap`). The arrow has content. -/
theorem mv_inRange_passes_both :
    actionChainAdmits [mvKeep] mvKeep (fun _ => false) = true
    ∧ mvKeep ≤ caveatChainAuthority ⊤ [mvKeep] :=
  ⟨by decide, (chain_narrowing_eq_cap_narrowing [mvKeep] mvKeep (fun _ => false)).mp (by decide)⟩

/-- **MUTATION-CONFIRM (negative tooth — the convergence BITES):** an OVER-BROAD action (`{read,write}`
against a `{read}` chain) is REJECTED by the macaroon chain, AND — via the convergence — is provably
NOT cap-conferred (`¬ {read,write} ≤ folded cap {read}`). A caveat-chain that narrows MUST correspond to
a strictly-smaller cap: the rejected action is cap-unauthorized, exactly as the equality demands.
Neither gate admits the over-broad action — refuted on both ends by ONE theorem. -/
theorem mv_overBroad_rejected_both :
    actionChainAdmits [mvKeep] mvHeld (fun _ => false) = false
    ∧ ¬ (mvHeld ≤ caveatChainAuthority ⊤ [mvKeep]) := by
  refine ⟨by decide, ?_⟩
  intro hle
  have hadm : actionChainAdmits [mvKeep] mvHeld (fun _ => false) = true :=
    (chain_narrowing_eq_cap_narrowing [mvKeep] mvHeld (fun _ => false)).mpr hle
  have hrej : actionChainAdmits [mvKeep] mvHeld (fun _ => false) = false := by decide
  rw [hadm] at hrej
  exact Bool.noConfusion hrej

end MapConvergence

#assert_axioms actionChainAdmits_iff_forall
#assert_axioms le_caveatChainAuthority_top_iff_forall
#assert_axioms chain_narrowing_eq_cap_narrowing
#assert_axioms chain_admit_set_eq_cap_confer_set
#assert_axioms mv_inRange_passes_both
#assert_axioms mv_overBroad_rejected_both

#assert_axioms chainGateG_emits_granted_le_held
#assert_axioms chainGateG_implies_capAuthorityG_devac
#assert_axioms capAuthorityG_reads_same_atom
#assert_axioms delegChain_admits_iff
#assert_axioms delegChain_verify
#assert_axioms deleg_nonAmp_chainGate
#assert_axioms deleg_nonAmp_yields_le
#assert_axioms deleg_amp_chainGate_false
#assert_axioms deleg_amp_not_le
#assert_axioms deleg_amp_capAuthority_false

#assert_axioms caveatChainAuthority_le_held
#assert_axioms caveatChainAuthority_append_le
#assert_axioms delegationVerb_authority_eq
#assert_axioms bridgeCapMode_admits
#assert_axioms chainGateG_implies_capAuthorityG
#assert_axioms keepR_equality
#assert_axioms keepOver_strict_refines
#assert_axioms bridge_keystone_concrete

end Dregg2.Authority.CaveatCapBridge
