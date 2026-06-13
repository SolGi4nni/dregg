/-
# Dregg2.Firmament.SeL4Abstract — the FAITHFUL TRANSCRIPTION of seL4/l4v's OWN cap-authority semantics.

This module grounds **ONE LEG** of dregg's capability discipline — cap *non-amplification* on
`derive` — in a line-for-line transcription of the seL4 abstract specification, as machine-checked
in the `l4v` proof base. It is **NOT** "dregg composes with seL4"; it replaces a black-box authority
assumption (SEL4-DERIVE-NONAMP-BRIDGE, stated explicitly in §5 with named embedding hypotheses) with
a *named, pinned, transcribed* one. A named assumption is a severe-problem-reduced, not a wall-removed.

## SEL4-PIN

  * l4v commit: `e2f32e54dab5786766094fba7ce5f93d3e59f8c6` (HEAD of `/Users/ember/dev/l4v`, 2026-06).
  * Source paths + line ranges transcribed below (diff each `def` against these line-for-line):
      - `auth` enum                         — `proof/access-control/Types.thy:51`
      - `cap` datatype (11 named + Arch)    — `spec/abstract/Structures_A.thy:102-117`
      - `rights` enum (`cap_rights`)        — `spec/abstract/CapRights_A.thy:19,29`
      - `cap_rights_to_auth`                — `proof/access-control/Access.thy:107-113`
      - `reply_cap_rights_to_auth`          — `proof/access-control/Access.thy:115-116`
      - `cap_auth_conferred`                — `proof/access-control/Access.thy:118-131`
      - `default_cap`                       — `spec/abstract/Retype_A.thy:30-39`
      - `derive_cap`                        — `spec/abstract/CSpace_A.thy:105-114`
      - `ensure_no_children`                — `spec/abstract/CSpace_A.thy:68-72`

  ⚠ NOTE — the verdict's `auth` list (7 ctors) was INCOMPLETE. The l4v `auth` at `Types.thy:51` has
  **12** constructors: `Control | Receive | SyncSend | Notify | Reset | Grant | Call | Reply | Write
  | Read | DeleteDerived | AAuth arch_auth`. The full enum is transcribed faithfully in `Auth` below.
  This matters for §5's relabelling-faithfulness finding (seL4's authority vocabulary is RICHER than
  dregg's): see `alpha` and `alpha_total_iff_used`. The one genuine IPC conflation that finding surfaced
  (`Notify ↦ none`) is now CLOSED — dregg gained `Auth.notify` (`Authority/Positional.lean:38`), so α
  is total on all 7 IPC authorities (`alpha_total_on_ipc`); the 4 remaining `none` arms are principled
  projections (memory model / revocation registry / above-arch).

## SCOPE — the PURE (non-monadic) fragment ONLY (feasibility verdict = GO, scoped here).

PORTED (pure, transcribed): `auth`, `cap` (ArchObjectCap as an OPAQUE `ArchCap` placeholder — its
interior is NOT ported), `rights`, `cap_rights_to_auth`, `reply_cap_rights_to_auth`,
`cap_auth_conferred`, `default_cap`, and `derive_cap` PURE-ISED (the `ensure_no_children` state-read
threaded in as a `Bool` argument — justified by the §2 sole-state-read finding).

OUT OF SCOPE (genuinely research-grade — NOT touched): the nondet/`se_monad`,
`cap_insert`/`send_ipc`/`receive_ipc`/`send_signal`/`retype_region`, `policy_wellformed`/
`integrity_subjects` (the full AC tower), `resolve_address_bits'` termination, the
embedding-faithfulness PROOF (stays a named hypothesis), noninterference. The Isabelle `export_code`
DIFFERENTIAL (the anti-drift cross-check vs the l4v code generator) is a SEPARATE follow-up needing an
l4v/Isabelle build; for this pass the transcription is human-diffable via the per-`def` line headers.

## DISTINCT from the sibling `SeL4Kernel.lean`.

`SeL4Kernel.lean` is a HAND-ROLLED model of the `sel4/dregg-firmament` *EmulatedKernel* (the n=1 Rust
emulator) — it invents its own cap/IPC state machine. THIS module is a TRANSCRIPTION of l4v's *own*
Isabelle text, so a reviewer can diff it against the cited `.thy` line ranges. The two meet only at
the `Dregg2.Authority` lattice they both ground in.

## THE PAYOFF — §5's composition statement.

`seL4_derive_cap_non_amplifying` (§4): the transcribed `derive_cap` never amplifies conferred
authority (`cap_auth_conferred c' ⊆ cap_auth_conferred c`), proved axiom-clean over the transcribed
`cap`. Then `dregg_executor_cap_authority_grounded_in_seL4` (§5) discharges the seL4-side leg of
dregg's cap-non-amplification (the `AssuranceCase.running_entry_sound` cap-authority conjunct,
`AssuranceCase.lean:641`) from it, under EXPLICIT named embedding/relabelling hypotheses — that bundle
of hypotheses IS the SEL4-DERIVE-NONAMP-BRIDGE assumption.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. Verified
standalone: `lake env lean Dregg2/Firmament/SeL4Abstract.lean`.
-/
import Dregg2.Authority.Positional
import Dregg2.Exec.EffectsAuthority
import Dregg2.Tactics

namespace Dregg2.Firmament.SeL4Abstract

/-! ## §1 — The seL4 authority + capability datatypes (transcribed). -/

/-- **`auth`** — seL4's authority labels (the edges of the agent authority graph).
-- l4v@e2f32e54 proof/access-control/Types.thy:51
```
datatype auth = Control | Receive | SyncSend | Notify | Reset | Grant | Call
                        | Reply | Write | Read | DeleteDerived | AAuth arch_auth
```
`AAuth arch_auth` is kept as an OPAQUE nullary placeholder `aauth` (the arch authority kind; its
interior — `arch_auth` — is NOT ported, mirroring the `ArchCap` opacity). The full 12-constructor
enum is transcribed faithfully (the verdict's 7-ctor list was incomplete). -/
inductive Auth where
  | Control | Receive | SyncSend | Notify | Reset | Grant | Call
  | Reply | Write | Read | DeleteDerived
  | AAuth   -- opaque placeholder for `AAuth arch_auth` (arch authority kind; interior not ported)
  deriving DecidableEq, Repr

/-- **`rights`** — seL4's access-control rights (`cap_rights = rights set`).
-- l4v@e2f32e54 spec/abstract/CapRights_A.thy:19
```
datatype rights = AllowRead | AllowWrite | AllowGrant | AllowGrantReply
```
-- l4v@e2f32e54 spec/abstract/CapRights_A.thy:29 : `type_synonym cap_rights = "rights set"` -/
inductive Rights where
  | AllowRead | AllowWrite | AllowGrant | AllowGrantReply
  deriving DecidableEq, Repr

/-- `cap_rights = rights set` — transcribed as a duplicate-free `List Rights` membership carrier
(we only ever test `∈`, never cardinality, so a `List` is a faithful stand-in for the Isabelle
`set`). -/
abbrev CapRights := List Rights

/-- An OPAQUE arch capability — the `ArchObjectCap (the_arch_cap: arch_cap)` payload. Its interior
(`arch_cap`) is deliberately NOT ported (per the verdict scope). Kept an opaque INHABITED `Type` so the
`cap` datatype is faithful in SHAPE without committing to arch internals; `cap_auth_conferred` reads
it only through the opaque `archCapAuthConferred` below. (Inhabited via the standard `NonemptyType`
idiom so total constructors like `default_cap`'s arch branch can produce one.) -/
opaque ArchCapPointed : NonemptyType
/-- The opaque arch capability type (interior not ported). -/
def ArchCap : Type := ArchCapPointed.type
instance : Nonempty ArchCap := ArchCapPointed.property
/-- `ArchCap` is uninterpreted, so its `Inhabited` witness is necessarily `Classical` (hence
`noncomputable`). It is used ONLY by the opaque/total arch placeholders (`archDefaultCap`), never by a
load-bearing theorem, and never executed. -/
noncomputable instance : Inhabited ArchCap := Classical.inhabited_of_nonempty inferInstance

/-- The seL4 object reference / cnode-slot pointer types, transcribed as opaque-enough `Nat`s.
-- l4v@e2f32e54 spec/abstract/Structures_A.thy (`obj_ref` = machine word; `badge = data`;
--   `cnode_index = bool list`; `cslot_ptr = obj_ref × cnode_index`).
We carry them at the granularity `cap_auth_conferred`/`derive_cap` actually inspect (NONE of these
fields is read by the authority semantics — only the cap *constructor* and its `cap_rights`/`bool`
matter), so `Nat`/`List Bool` placeholders are faithful for THIS fragment. -/
abbrev ObjRef   := Nat
abbrev Badge    := Nat
abbrev Irq      := Nat
abbrev CnodeIdx := List Bool
abbrev CSlotPtr := ObjRef × CnodeIdx

/-- **`cap`** — seL4's capability datatype.
-- l4v@e2f32e54 spec/abstract/Structures_A.thy:102-117
```
datatype cap
         = NullCap
         | UntypedCap bool obj_ref nat nat          -- device flag, ptr, size bits, freeIndex
         | EndpointCap obj_ref badge cap_rights
         | NotificationCap obj_ref badge cap_rights
         | ReplyCap obj_ref bool cap_rights
         | CNodeCap obj_ref nat "bool list"          -- CNode ptr, bits translated, guard
         | ThreadCap obj_ref
         | DomainCap
         | IRQControlCap
         | IRQHandlerCap irq
         | Zombie obj_ref "nat option" nat
         | ArchObjectCap (the_arch_cap: arch_cap)
```
All 11 named constructors + `ArchObjectCap` (opaque payload `ArchCap`) are transcribed. -/
inductive Cap where
  | NullCap
  | UntypedCap      (dev : Bool) (ptr : ObjRef) (sizeBits : Nat) (freeIndex : Nat)
  | EndpointCap     (oref : ObjRef) (badge : Badge) (r : CapRights)
  | NotificationCap (oref : ObjRef) (badge : Badge) (r : CapRights)
  | ReplyCap        (oref : ObjRef) (master : Bool) (r : CapRights)
  | CNodeCap        (oref : ObjRef) (bits : Nat) (guard : List Bool)
  | ThreadCap       (oref : ObjRef)
  | DomainCap
  | IRQControlCap
  | IRQHandlerCap   (irq : Irq)
  | Zombie          (ptr : ObjRef) (b : Option Nat) (n : Nat)
  | ArchObjectCap   (ac : ArchCap)
  deriving Inhabited

/-! ## §2 — The pure authority semantics (`cap_rights_to_auth`, `cap_auth_conferred`). -/

/-- **`cap_rights_to_auth`** — the authority a `cap_rights` set confers (sync = endpoint vs ntfn).
-- l4v@e2f32e54 proof/access-control/Access.thy:107-113
```
cap_rights_to_auth r sync ≡
     {Reset}
   ∪ (if AllowRead ∈ r then {Receive} else {})
   ∪ (if AllowWrite ∈ r then (if sync then {SyncSend} else {Notify}) else {})
   ∪ (if AllowGrant ∈ r then UNIV else {})
   ∪ (if AllowGrantReply ∈ r ∧ AllowWrite ∈ r then {Call} else {})
```
`UNIV` (the `AllowGrant ⇒ everything` clause) is transcribed as the explicit full enumeration
`allAuth` (the finite `Auth` universe), so the def stays computable and the `UNIV ⊆` step in §4 is
`List.Subset`-decidable. -/
def allAuth : List Auth :=
  [.Control, .Receive, .SyncSend, .Notify, .Reset, .Grant, .Call,
   .Reply, .Write, .Read, .DeleteDerived, .AAuth]

def capRightsToAuth (r : CapRights) (sync : Bool) : List Auth :=
  [.Reset]
  ++ (if r.contains .AllowRead then [.Receive] else [])
  ++ (if r.contains .AllowWrite then (if sync then [.SyncSend] else [.Notify]) else [])
  ++ (if r.contains .AllowGrant then allAuth else [])
  ++ (if r.contains .AllowGrantReply ∧ r.contains .AllowWrite then [.Call] else [])

/-- **`reply_cap_rights_to_auth`**.
-- l4v@e2f32e54 proof/access-control/Access.thy:115-116
```
reply_cap_rights_to_auth master r ≡ if AllowGrant ∈ r ∨ master then UNIV else {Reply}
```
-/
def replyCapRightsToAuth (master : Bool) (r : CapRights) : List Auth :=
  if r.contains .AllowGrant ∨ master then allAuth else [.Reply]

/-- **`arch_cap_auth_conferred`** — the authority an arch cap confers. OPAQUE (its interior is not
ported; `Access.thy:131` delegates to the arch-specific `arch_cap_auth_conferred`). Kept an opaque
function so `cap_auth_conferred`'s `ArchObjectCap` case is transcribed in SHAPE; §4's non-amplification
holds for it because `derive_cap`'s arch branch is itself opaque and supplied (see `deriveCap`). -/
opaque archCapAuthConferred : ArchCap → List Auth

/-- **`cap_auth_conferred`** — the authority a cap confers (the heart of the agent authority graph).
-- l4v@e2f32e54 proof/access-control/Access.thy:118-131
```
cap_auth_conferred cap ≡ case cap of
    NullCap ⇒ {}
  | UntypedCap isdev oref bits freeIndex ⇒ {Control}
  | EndpointCap oref badge r ⇒ cap_rights_to_auth r True
  | NotificationCap oref badge r ⇒ cap_rights_to_auth (r - {AllowGrant, AllowGrantReply}) False
  | ReplyCap oref m r ⇒ reply_cap_rights_to_auth m r
  | CNodeCap oref bits guard ⇒ {Control}
  | ThreadCap obj_ref ⇒ {Control}
  | DomainCap ⇒ {Control}
  | IRQControlCap ⇒ {Control}
  | IRQHandlerCap irq ⇒ {Control}
  | Zombie ptr b n ⇒ {Control}
  | ArchObjectCap arch_cap ⇒ arch_cap_auth_conferred arch_cap
```
The `r - {AllowGrant, AllowGrantReply}` set-difference (Notification case) is transcribed as a
`List.filter` removing exactly those two rights. -/
def capAuthConferred : Cap → List Auth
  | .NullCap                 => []
  | .UntypedCap _ _ _ _      => [.Control]
  | .EndpointCap _ _ r       => capRightsToAuth r true
  | .NotificationCap _ _ r   =>
      capRightsToAuth (r.filter (fun x => x ≠ .AllowGrant ∧ x ≠ .AllowGrantReply)) false
  | .ReplyCap _ m r          => replyCapRightsToAuth m r
  | .CNodeCap _ _ _          => [.Control]
  | .ThreadCap _             => [.Control]
  | .DomainCap               => [.Control]
  | .IRQControlCap           => [.Control]
  | .IRQHandlerCap _         => [.Control]
  | .Zombie _ _ _            => [.Control]
  | .ArchObjectCap ac        => archCapAuthConferred ac

/-! ## §3 — `default_cap` and the PURE-ISED `derive_cap`.

⚠ THE SOLE-STATE-READ FINDING (the faithfulness verification for the pure-isation).
`derive_cap` (`CSpace_A.thy:105-114`) reads kernel state ONLY through `ensure_no_children`
(`CSpace_A.thy:68-72`, `cdt ← gets cdt; whenE (∃c. cdt c = Some cslot_ptr) (throwError RevokeFirst)`),
which reads exactly the capability-derivation tree `cdt`. In the NON-ARCH fragment this is the SOLE
state-read: the `UntypedCap` branch is the only one calling `ensure_no_children`; `Zombie`/`ReplyCap`/
`IRQControlCap` return `returnOk NullCap` (pure) and the catch-all `_ ⇒ returnOk cap` is a pure
pass-through. The `ArchObjectCap ⇒ arch_derive_cap c` branch DOES read state, but that is precisely the
OPAQUE branch the scope excludes — so we keep it as a SUPPLIED opaque result (`archDeriveCap`), not a
ported state-reader. Therefore the pure-isation threads `ensure_no_children`'s Boolean verdict
(`noChildren : Bool`) in as an argument and is FAITHFUL on the ported (non-arch) fragment. PATH TAKEN:
the full `derive_cap` pure-isation (NOT the narrowed `default_cap`-only slice) — the sole-state-read
condition holds. -/

/-- Opaque arch object kind (the `default_cap (ArchObject aobj)` payload — interior not ported).
Inhabited via the same `NonemptyType` idiom as `ArchCap`. -/
opaque ArchObjectKindPointed : NonemptyType
/-- The opaque arch object kind type. -/
def ArchObjectKind : Type := ArchObjectKindPointed.type
instance : Nonempty ArchObjectKind := ArchObjectKindPointed.property

/-- The seL4 API object types `default_cap` dispatches on.
-- l4v@e2f32e54 spec/abstract/Retype_A.thy:30-39 (the `apiobject_type` argument).
`ArchObject` carries an opaque arch object kind (its `default_cap` produces an `ArchObjectCap`). -/
inductive ApiObjectType where
  | CapTableObject | Untyped | TCBObject | EndpointObject | NotificationObject
  | ArchObject (ao : ArchObjectKind)

/-- An OPAQUE arch default cap (the `arch_default_cap aobj oref s dev` result — not ported). A total
but UNINTERPRETED placeholder: it produces a fixed (opaque) arch cap, which for an uninterpreted
`ArchCap` is as content-free as a port can be. `noncomputable` because `ArchCap`'s inhabitant is
`Classical`; it is referenced only by `defaultCap` (itself non-load-bearing for §4/§5). -/
noncomputable def archDefaultCap : ArchObjectKind → ObjRef → Nat → Bool → ArchCap :=
  fun _ _ _ _ => default

/-- The full rights set `UNIV` (the `EndpointObject` default).
-- transcribes `default_cap EndpointObject … = EndpointCap oref 0 UNIV`. -/
def allRights : CapRights := [.AllowRead, .AllowWrite, .AllowGrant, .AllowGrantReply]

/-- **`default_cap`** — the original cap created for a fresh object of a given API type.
-- l4v@e2f32e54 spec/abstract/Retype_A.thy:30-39 (pure primrec)
```
default_cap CapTableObject oref s _   = CNodeCap oref s []
default_cap Untyped oref s dev        = UntypedCap dev oref s 0
default_cap TCBObject oref s _        = ThreadCap oref
default_cap EndpointObject oref s _   = EndpointCap oref 0 UNIV
default_cap NotificationObject oref s _ = NotificationCap oref 0 {AllowRead, AllowWrite}
default_cap (ArchObject aobj) oref s dev = ArchObjectCap (arch_default_cap aobj oref s dev)
```
-/
noncomputable def defaultCap : ApiObjectType → ObjRef → Nat → Bool → Cap
  | .CapTableObject,    oref, s, _   => .CNodeCap oref s []
  | .Untyped,           oref, s, dev => .UntypedCap dev oref s 0
  | .TCBObject,         oref, _, _   => .ThreadCap oref
  | .EndpointObject,    oref, _, _   => .EndpointCap oref 0 allRights
  | .NotificationObject,oref, _, _   => .NotificationCap oref 0 [.AllowRead, .AllowWrite]
  | .ArchObject ao,     oref, s, dev => .ArchObjectCap (archDefaultCap ao oref s dev)

/-- An OPAQUE arch derive result (the `arch_derive_cap c` value — the arch branch reads state, but
that is the excluded opaque branch; here the result is SUPPLIED as a parameter so the pure-isation
does not pretend to compute it). It is an `Option Cap` because `arch_derive_cap` can `throwError`. -/
opaque archDeriveCap : ArchCap → Option Cap

/-- **`derive_cap`** — PURE-ISED. The `ensure_no_children` state-read is threaded in as the Boolean
`noChildren` (`True` = "the slot has no children", i.e. `ensure_no_children` would `returnOk ()`).
-- l4v@e2f32e54 spec/abstract/CSpace_A.thy:105-114
```
derive_cap slot cap ≡ case cap of
    ArchObjectCap c ⇒ arch_derive_cap c
  | UntypedCap dev ptr sz f ⇒ doE ensure_no_children slot; returnOk cap odE
  | Zombie ptr n sz ⇒ returnOk NullCap
  | ReplyCap ptr m cr ⇒ returnOk NullCap
  | IRQControlCap ⇒ returnOk NullCap
  | _ ⇒ returnOk cap
```
The `se_monad` `returnOk x`/`throwError` map to `some x`/`none`. The `UntypedCap` branch: when
`noChildren` holds, `ensure_no_children` succeeds and the cap passes through (`some cap`); when it
fails it `throwError RevokeFirst` (`none`). The `ArchObjectCap` branch is the supplied opaque
`archDeriveCap c`. `Zombie`/`ReplyCap`/`IRQControlCap` collapse to `some NullCap`; all else passes
through. (`slot` is retained as an argument for header fidelity though the pure-ised body no longer
reads it — `ensure_no_children`'s effect on it is now the `noChildren` premise.) -/
noncomputable def deriveCap (_slot : CSlotPtr) (cap : Cap) (noChildren : Bool) : Option Cap :=
  match cap with
  | .ArchObjectCap c         => archDeriveCap c
  | .UntypedCap _ _ _ _      => if noChildren then some cap else none
  | .Zombie _ _ _            => some .NullCap
  | .ReplyCap _ _ _          => some .NullCap
  | .IRQControlCap           => some .NullCap
  | other                    => some other

/-! ## §4 — THE LEMMA: `derive_cap` is non-amplifying (axiom-clean). -/

/-- The `ArchObjectCap` non-amplification premise. `arch_derive_cap` produces only arch caps that
confer no MORE than the source arch cap — but its interior is NOT ported, so we carry this as a NAMED
hypothesis on the opaque `archDeriveCap`/`archCapAuthConferred` (the arch-fragment counterpart of the
SEL4-DERIVE-NONAMP-BRIDGE; it is what an l4v arch-derive proof, e.g. `arch_derive_cap_inv`, discharges
for each architecture). It is the ONLY non-`rfl` obligation in the non-amplification proof, and it is
about the EXCLUDED opaque branch. -/
def ArchDeriveNonAmplifying : Prop :=
  ∀ (ac : ArchCap) (c' : Cap), archDeriveCap ac = some c' →
    capAuthConferred c' ⊆ capAuthConferred (.ArchObjectCap ac)

/-- **`seL4_derive_cap_non_amplifying` — THE TRANSCRIBED-SEL4 NON-AMPLIFICATION.** The cap produced
by the (pure-ised) seL4 `derive_cap` confers a SUBSET of the source cap's authority:
`cap_auth_conferred c' ⊆ cap_auth_conferred c`. Case-by-case (verbatim the l4v `derive_cap`
case-split):

  * `NullCap`/`Zombie`/`ReplyCap`/`IRQControlCap` ⇒ the derived cap is `NullCap`/itself with
    `cap_auth_conferred = ∅` (Zombie/Reply/IRQControl derive to `NullCap`); ∅ ⊆ anything.
  * `UntypedCap` ⇒ passes `cap` through unchanged (when `noChildren`) ⇒ `⊆` is reflexive.
  * `EndpointCap`/`NotificationCap`/`CNodeCap`/`ThreadCap`/`DomainCap`/`IRQHandlerCap` ⇒ pass through
    unchanged ⇒ reflexive.
  * `ArchObjectCap` ⇒ the EXCLUDED opaque branch, discharged by the named `ArchDeriveNonAmplifying`
    hypothesis on `archDeriveCap`.

This is the seL4-side mirror of dregg's `attenuate_subset` / `EffectsAuthority.attenuate_non_amplifying`
(`EffectsAuthority.lean:345`) — the SAME `granted ⊆ held` law, now grounded in transcribed seL4 text. -/
theorem seL4_derive_cap_non_amplifying
    (harch : ArchDeriveNonAmplifying)
    (slot : CSlotPtr) (c : Cap) (b : Bool) (c' : Cap)
    (h : deriveCap slot c b = some c') :
    capAuthConferred c' ⊆ capAuthConferred c := by
  unfold deriveCap at h
  cases c with
  | ArchObjectCap ac =>
      -- the excluded opaque branch: discharged by the named arch hypothesis.
      exact harch ac c' h
  | UntypedCap dev ptr sz f =>
      -- `some cap` iff `noChildren`; either way the result (when `some`) is `c` itself.
      by_cases hb : b
      · rw [if_pos hb] at h; cases h; exact fun a ha => ha
      · rw [if_neg hb] at h; exact absurd h (by simp)
  | Zombie ptr n sz =>
      -- derives to NullCap ⇒ ∅ ⊆ _.
      cases h; intro a ha; simp [capAuthConferred] at ha
  | ReplyCap ptr m cr =>
      cases h; intro a ha; simp [capAuthConferred] at ha
  | IRQControlCap =>
      cases h; intro a ha; simp [capAuthConferred] at ha
  | NullCap            => cases h; exact fun a ha => ha
  | EndpointCap _ _ _  => cases h; exact fun a ha => ha
  | NotificationCap _ _ _ => cases h; exact fun a ha => ha
  | CNodeCap _ _ _     => cases h; exact fun a ha => ha
  | ThreadCap _        => cases h; exact fun a ha => ha
  | DomainCap          => cases h; exact fun a ha => ha
  | IRQHandlerCap _    => cases h; exact fun a ha => ha

/-! ### §4.1 — NON-VACUITY: a satisfiable `derive_cap … = some _` witness.

The hypothesis of §4 is not vacuous — `derive_cap` actually commits on concrete caps. We witness an
`EndpointCap` (passes through) and an `UntypedCap` with `noChildren = true` (passes through), and the
collapsing `ReplyCap ⇒ NullCap`. -/

-- (`deriveCap` is `noncomputable` — its `ArchObjectCap` branch reaches the opaque `archDeriveCap` —
-- so we witness satisfiability as `rfl`/`decide` lemmas that REDUCE through the NON-arch branches
-- definitionally, never `#eval`/`#guard` over the opaque arm.)

/-- A concrete endpoint cap with full rights. -/
def egEndpoint : Cap := .EndpointCap 9 0 allRights
/-- A concrete untyped cap. -/
def egUntyped : Cap := .UntypedCap false 7 12 0
/-- A concrete cnode slot pointer (`ObjRef × CnodeIdx`). -/
def egSlot : CSlotPtr := (0, [])

-- `derive_cap` of an endpoint passes it through (COMMITS — so the §4 hypothesis is satisfiable):
example : deriveCap egSlot egEndpoint true = some egEndpoint := rfl
-- `derive_cap` of an untyped with NO children COMMITS (passes through):
example : deriveCap egSlot egUntyped true = some egUntyped := rfl
-- ...but with CHILDREN present it is REVOKE-FIRST rejected (the `ensure_no_children` teeth):
example : deriveCap egSlot egUntyped false = none := rfl
-- a ReplyCap collapses to NullCap (conferred authority ∅):
example : deriveCap egSlot (.ReplyCap 3 false []) true = some .NullCap := rfl
example : capAuthConferred (.NullCap : Cap) = ([] : List Auth) := rfl
-- the conferred authority of the derived endpoint is a real, NON-EMPTY set (so the §4 `⊆` is a real
-- containment of inhabited sets, not ∅ ⊆ ∅): `Reset` is always conferred.
example : Auth.Reset ∈ capAuthConferred egEndpoint := by decide

/-- The §4 theorem FIRES on the concrete endpoint witness (no children) — `derive_cap` commits and the
conferred authority is `⊆` (here `=`) the source's. Non-vacuity of the headline, given the arch
hypothesis (here trivially unused — the endpoint branch needs no arch premise). -/
example (harch : ArchDeriveNonAmplifying) :
    capAuthConferred egEndpoint ⊆ capAuthConferred egEndpoint :=
  seL4_derive_cap_non_amplifying harch egSlot egEndpoint true egEndpoint rfl

/-! ## §5 — THE COMPOSITION TARGET: ground dregg's cap-non-amplification leg in transcribed seL4.

dregg's executor enforces cap non-amplification (`AssuranceCase.running_entry_sound`'s cap-authority
conjunct, `AssuranceCase.lean:641`: `∀ e ∈ forestEdgesG f, capAuthConferred (attenuate e.1 e.2) ⊆
capAuthConferred e.2`). We want that leg to be GROUNDED IN seL4's own authority semantics rather than
asserted. The bridge is two maps + their faithfulness, carried as EXPLICIT NAMED hypotheses (their
bundle IS the SEL4-DERIVE-NONAMP-BRIDGE assumption — a named/pinned replacement for the black box):

  * `embed   : DAuth.Cap → SeL4Abstract.Cap`        — a dregg held-cap as an seL4 cap;
  * `embedInv`                                       — `embed` reflects authority faithfully:
        `α`-image of the seL4 conferred-authority ⊆/⊇ the dregg conferred-authority (stated below);
  * `α       : SeL4Abstract.Auth → Option DAuth.Auth`— the authority relabelling (PARTIAL — see the
        faithfulness finding below).

⚠ THE α-FAITHFULNESS FINDING (the divergence, narrowed by `notify`). The relabelling
(`Receive↦read, SyncSend↦write, Notify↦notify, Grant↦grant, Call↦call, Reply↦reply, Reset↦reset,
Control↦control`) is FAITHFUL and INJECTIVE on the 8 seL4 auth constructors it names — now TOTAL on all
7 seL4 IPC authorities (`alpha_total_on_ipc`). The remaining 4 (`Write, Read, DeleteDerived, AAuth`)
have no dregg cap-lattice image, but these are PRINCIPLED projections, not conflations: dregg factors
memory access into the richer Blum-multiset `Crypto.MemoryChecking.Kind` model, revocation into the
registry / `CNode.revoke` op, and operates above the arch layer (`docs/rebuild/AUTHORITY-DIVERGENCE-FINDING.md`).
So `α` is total only on the USED subset; we encode this honestly: `alpha` returns `Option DAuth.Auth`
(`none` exactly on the 4 principled-projection ctors), and `alpha_total_iff_used` proves α is defined ⟺
the auth is one of the used 8. dregg's authority lattice is an 8-of-12 PROJECTION of seL4's, with the
4 `none` arms each imaged outside the cap lattice (not ignored). The ONE genuine IPC conflation the
transcription originally found — `Notify ↦ none` while the firmament models a distinct `Notification`
object — is now CLOSED by `Auth.notify` (`alpha_Notify_is_notify`). -/

/-- A dregg held-cap (`Dregg2.Authority.Cap` — `null`/`endpoint`/`node`), abbreviated to disambiguate
from the transcribed seL4 `Cap` in scope. -/
abbrev DCap := Dregg2.Authority.Cap

/-- **`alpha` — the authority relabelling (PARTIAL, now total on all 7 IPC authorities).** Maps the 8
used seL4 auth ctors onto dregg's `Auth`; `none` on the 4 remaining seL4-richer ctors
(`Write`/`Read`/`DeleteDerived`/`AAuth`) that are *principled* projections (memory access lives in
dregg's Blum-multiset `Crypto.MemoryChecking.Kind` model, not the cap lattice; `DeleteDerived` is the
revocation registry / `CNode.revoke` op; `AAuth` is above dregg's arch level — see
`docs/rebuild/AUTHORITY-DIVERGENCE-FINDING.md`). Per the verdict: `Receive↦read, SyncSend↦write,
Grant↦grant, Call↦call, Reply↦reply, Reset↦reset, Control↦control`, **and now `Notify↦notify`** — the
one genuine IPC conflation the transcription found, closed (`Auth.notify` is the new dregg async-signal
authority, `Authority/Positional.lean:38`; `Firmament/NotifyAuthority` proves its cap algebra). So α is
now TOTAL on all 7 seL4 IPC authorities (`Receive, SyncSend, Notify, Reset, Grant, Call, Reply`), and
the firmament's async `Notification` object is faithfully seL4-grounded rather than 6-of-7-projected. -/
def alpha : Auth → Option Dregg2.Authority.Auth
  | .Receive       => some .read
  | .SyncSend      => some .write
  | .Grant         => some .grant
  | .Call          => some .call
  | .Reply         => some .reply
  | .Reset         => some .reset
  | .Control       => some .control
  | .Notify        => some .notify   -- the closed conflation: dregg's async-signal authority (the 8th IPC auth)
  | .Write         => none   -- principled projection: dregg memory-Write is `Crypto.MemoryChecking.Kind`
  | .Read          => none   -- principled projection: dregg memory-Read is `Crypto.MemoryChecking.Kind`
  | .DeleteDerived => none   -- principled projection: dregg revocation = registry / `CNode.revoke`
  | .AAuth         => none   -- opaque arch authority — above dregg's arch level, no dregg image

/-- The 8 seL4 auth ctors α is defined on (the USED subset, exactly dregg's vocabulary preimage —
the 7 IPC authorities, now INCLUDING `Notify ↦ notify`). -/
def usedAuth : List Auth :=
  [.Receive, .SyncSend, .Grant, .Call, .Reply, .Reset, .Control, .Notify]

/-- **`alpha_total_iff_used` — the divergence, made precise.** `α` is defined (`isSome`) EXACTLY on
`usedAuth` — i.e. seL4's `auth` is an 8-of-12 superset of dregg's relabelled vocabulary, and the
remaining 4 (`Write`/`Read`/`DeleteDerived`/`AAuth`) are the principled projections. α is total/faithful
on the used subset (all 7 IPC authorities + `Control`); the 4 `none` arms are dregg's deliberate
factoring (memory model / revocation registry / above-arch), not unexplained gaps. -/
theorem alpha_total_iff_used (a : Auth) : (alpha a).isSome ↔ a ∈ usedAuth := by
  cases a <;> simp [alpha, usedAuth]

/-- **`alpha_total_on_ipc` — α is now TOTAL on ALL 7 seL4 IPC authorities** (the grounding payoff
`notify` delivers). Every IPC authority (`Receive, SyncSend, Notify, Reset, Grant, Call, Reply`) has a
dregg image — in particular `Notify ↦ notify`, the one IPC ctor that was previously `none`. So the
firmament's async `Notification` authority is faithfully grounded, not 6-of-7-projected. -/
theorem alpha_total_on_ipc :
    (alpha .Receive).isSome ∧ (alpha .SyncSend).isSome ∧ (alpha .Notify).isSome
      ∧ (alpha .Reset).isSome ∧ (alpha .Grant).isSome ∧ (alpha .Call).isSome
      ∧ (alpha .Reply).isSome := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- **`alpha_Notify_is_notify` — the closed conflation, witnessed.** `Notify` maps to dregg's
`notify` (NOT `none`, NOT `write`): the async-signal authority is a DISTINCT dregg image from the
synchronous `SyncSend ↦ write`. This is the one genuine IPC conflation the transcription found, now a
faithful relabelling. Non-vacuity: `Notify` and `SyncSend` have DISTINCT dregg images, so the split is
real. -/
theorem alpha_Notify_is_notify :
    alpha .Notify = some .notify ∧ alpha .SyncSend = some .write
      ∧ alpha .Notify ≠ alpha .SyncSend := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- **`alpha_injective_on_used` — α is INJECTIVE on the used subset.** Distinct used seL4 auths map to
distinct dregg auths (so the relabelling loses no distinctions WITHIN the used vocabulary — the
projection is clean, not collapsing). -/
theorem alpha_injective_on_used (a₁ a₂ : Auth)
    (h₁ : a₁ ∈ usedAuth) (h₂ : a₂ ∈ usedAuth) (heq : alpha a₁ = alpha a₂) : a₁ = a₂ := by
  fin_cases h₁ <;> fin_cases h₂ <;> simp_all [alpha]

/-- **`alphaList` — α-image of a seL4 auth list**, dropping the un-mapped (seL4-richer) entries
(`filterMap`). The dregg authorities a seL4 cap's conferred-authority projects to. -/
def alphaList (as : List Auth) : List Dregg2.Authority.Auth := as.filterMap alpha

/-- **`alphaList_mono` — the α-image is MONOTONE on the used vocabulary.** If `xs ⊆ ys` (as seL4 auth
lists), then `alphaList xs ⊆ alphaList ys`. This is the α-image-monotonicity helper §5's target needs:
relabelling preserves the `⊆` non-amplification ordering. Proved on the CONCRETE `filterMap alpha` (it
holds for ANY total or partial `alpha`, so a fortiori on the used subset — no faithfulness gap here). -/
theorem alphaList_mono {xs ys : List Auth} (hsub : xs ⊆ ys) :
    alphaList xs ⊆ alphaList ys := by
  intro d hd
  simp only [alphaList, List.mem_filterMap] at hd ⊢
  obtain ⟨a, hax, hαa⟩ := hd
  exact ⟨a, hsub hax, hαa⟩

/-- **`SeL4DeriveNonAmpBridge` — THE NAMED ASSUMPTION (SEL4-DERIVE-NONAMP-BRIDGE).** The interface
that lets a dregg cap-derivation be READ as an seL4 `derive_cap`, bundling:

  (1) `embed`     — dregg held-cap ↦ seL4 cap;
  (2) `embedNoChildren` — the slot-derivation-tree premise (`ensure_no_children`'s verdict) for the
        embedded cap (supplied — the executor's own no-children check witnesses it);
  (3) `commutes`  — embedding COMMUTES with derivation: deriving the embedded dregg cap (seL4 side)
        yields the embedding of the dregg-derived cap. (This is the embedding-faithfulness obligation
        the verdict keeps a NAMED HYPOTHESIS — NOT proved here; it is what an l4v↔dregg refinement
        would discharge.)
  (4) `reflectAuth` — `α`-image faithfulness: the dregg conferred-authority of a cap is the α-image of
        the seL4 conferred-authority of its embedding. (Authority is preserved across the embedding,
        modulo the α-projection.)

This bundle is EXACTLY the black box `running_entry_sound`'s cap-leg rested on, now NAMED and PINNED to
transcribed seL4. -/
structure SeL4DeriveNonAmpBridge where
  /-- dregg held-cap ↦ seL4 cap. -/
  embed : DCap → Cap
  /-- the slot's `ensure_no_children` verdict for a given embedded cap (supplied by the executor's own
  no-children check; load-bearing premise of the pure-ised `derive_cap`). -/
  embedNoChildren : DCap → Bool
  /-- the cnode-slot pointer the embedded cap sits at (header fidelity; unused by the pure body). -/
  embedSlot : DCap → CSlotPtr
  /-- embedding COMMUTES with derivation (the NAMED faithfulness hypothesis — not proved). -/
  commutes : ∀ (keep : List Dregg2.Authority.Auth) (c : DCap),
    deriveCap (embedSlot c) (embed c) (embedNoChildren c)
      = some (embed (Dregg2.Exec.attenuate keep c))
  /-- α-image faithfulness: dregg conferred-authority = α-image of seL4 conferred-authority of the
  embedding (the NAMED authority-preservation hypothesis — not proved). -/
  reflectAuth : ∀ (c : DCap),
    Dregg2.Authority.capAuthConferred c = alphaList (capAuthConferred (embed c))
  /-- the arch non-amplification premise (the opaque arch branch; discharged per-architecture in l4v). -/
  archNonAmp : ArchDeriveNonAmplifying

/-- **`dregg_executor_cap_authority_grounded_in_seL4` — THE PAYOFF.** Under the named
SEL4-DERIVE-NONAMP-BRIDGE (`B`), dregg's cap non-amplification (the `AssuranceCase.lean:641` leg shape
`capAuthConferred (attenuate keep c) ⊆ capAuthConferred c`) is DERIVED FROM the transcribed-seL4
`seL4_derive_cap_non_amplifying` (§4) composed with the α-image-monotonicity helper (`alphaList_mono`)
— NOT re-proved on the dregg side. The chain:

    dregg `attenuate keep c` ↦ (embed, commutes) ↦ an seL4 `derive_cap … = some (embed (attenuate …))`
    ⟹ (§4) `capAuthConferred (embed (attenuate …)) ⊆ capAuthConferred (embed c)` over seL4 auth
    ⟹ (alphaList_mono) the α-images are `⊆`
    ⟹ (reflectAuth) the dregg conferred-authorities are `⊆`.

So the dregg executor's cap-authority leg STANDS ON seL4's own `derive_cap` semantics, through the
named bridge. (NOT "dregg composes with seL4" — ONE leg, grounded; the bridge faithfulness is a named
hypothesis, the α-projection a reported divergence.) -/
theorem dregg_executor_cap_authority_grounded_in_seL4
    (B : SeL4DeriveNonAmpBridge)
    (keep : List Dregg2.Authority.Auth) (c : DCap) :
    Dregg2.Authority.capAuthConferred (Dregg2.Exec.attenuate keep c)
      ⊆ Dregg2.Authority.capAuthConferred c := by
  -- (1) the dregg derivation, read as an seL4 `derive_cap`, commits (named `commutes`):
  have hderive : deriveCap (B.embedSlot c) (B.embed c) (B.embedNoChildren c)
      = some (B.embed (Dregg2.Exec.attenuate keep c)) := B.commutes keep c
  -- (2) §4 over the embedding: the seL4 conferred-authority is a subset.
  have hseL4 : capAuthConferred (B.embed (Dregg2.Exec.attenuate keep c))
      ⊆ capAuthConferred (B.embed c) :=
    seL4_derive_cap_non_amplifying B.archNonAmp (B.embedSlot c) (B.embed c)
      (B.embedNoChildren c) _ hderive
  -- (3) α-image-monotonicity: the relabelled (dregg-vocabulary) authorities stay ⊆.
  have hmono : alphaList (capAuthConferred (B.embed (Dregg2.Exec.attenuate keep c)))
      ⊆ alphaList (capAuthConferred (B.embed c)) := alphaList_mono hseL4
  -- (4) reflectAuth rewrites both sides into the DREGG conferred-authorities.
  rw [B.reflectAuth (Dregg2.Exec.attenuate keep c), B.reflectAuth c]
  exact hmono

/-! ## §6 — Axiom hygiene. Every load-bearing transcription + lemma is kernel-clean (no `sorry`, no
extra `axiom` beyond the opaque-`Type`/`opaque`-decl carriers which are NOT `axiom`-keyword decls and
so don't trip the guard; only `propext`/`Classical.choice`/`Quot.sound`). -/

#assert_all_clean [
  seL4_derive_cap_non_amplifying,
  alpha_total_iff_used,
  alpha_total_on_ipc,
  alpha_Notify_is_notify,
  alpha_injective_on_used,
  alphaList_mono,
  dregg_executor_cap_authority_grounded_in_seL4
]

end Dregg2.Firmament.SeL4Abstract
