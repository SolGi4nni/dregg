/-
# Dregg2.Exec.CapTPConcrete — the CONCRETE `AuthRequired` attenuation lattice the captp
runtime enforces, pinned to Lean and tied to the abstract `handoff_non_amplifying` keystone.

`Dregg2.Exec.CapTP.handoff_non_amplifying` proves `granted.rights ≤ held.rights` for the
3-vat handoff, but ABSTRACTLY — over ANY `[SemilatticeInf Rights] [OrderTop Rights]`. The
RUNNING captp validator (`captp/src/handoff.rs::validate_handoff`) decides
non-amplification on a CONCRETE 6-element rights carrier — `cell/src/permissions.rs`'s
`AuthRequired` (`None`/`Signature`/`Proof`/`Either`/`Impossible`/`Custom {vk_hash}`) via
`AuthRequired::is_narrower_or_equal`, plus the `u32` effect-mask subset
(`is_facet_attenuation`). Nothing connected that concrete decision to the abstract proof:
the Rust lattice could be subtly wrong (e.g. accidentally declaring `None ≤ Signature`, an
AMPLIFICATION) and the abstract keystone — quantified over a *correct* abstract order —
would never notice. The proven theorem was DARK at the concrete carrier the runtime runs.

This module CLOSES that seam:

  1. defines `AuthReq`, the concrete `AuthRequired` enum (mirroring the Rust variants);
  2. defines `authNarrowerOrEqual`, the concrete decision MIRRORING the Rust
     `is_narrower_or_equal` logic clause-for-clause;
  3. proves that decision is a genuine PARTIAL ORDER on the non-`Custom`/equal-`Custom`
     fragment (reflexive, antisymmetric, transitive) and that `Impossible` is the bottom
     and `None` the top — i.e. it really is an attenuation order, not an arbitrary table;
  4. builds a `SemilatticeInf`/`OrderTop` on a quotient so the ABSTRACT
     `Exec.CapTP.handoff_non_amplifying` INSTANTIATES at the concrete carrier
     (`handoff_non_amplifying_concrete`);
  5. PINS the full `AuthReq × AuthReq` decision table via `#guard`s — the SAME table the
     Rust differential test (`captp/tests/handoff_lattice_differential.rs`) enumerates, so a
     drift on EITHER side (Rust lattice OR this Lean table) is caught by the test.

The crypto fields (signatures / swiss enliven) stay the §8 verify-seam carrier — what we
internalize here is the non-amplification LOGIC, which is now the verified concrete order.
-/
import Dregg2.Exec.CapTP
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPConcrete

open Dregg2.Spec
open Dregg2.Exec.CapTP

/-! ## §1 — The concrete `AuthRequired`, mirroring `cell/src/permissions.rs`. -/

/-- The concrete authorization-requirement carrier, mirroring the Rust `AuthRequired` enum.
`Custom` carries a `vk_hash` identity (a `Nat` stand-in for the 32-byte hash — only equality
matters for the lattice). -/
inductive AuthReq where
  | none
  | signature
  | proof
  | either
  | impossible
  | custom (vkHash : Nat)
  deriving Repr, DecidableEq

/-- **`authNarrowerOrEqual a b`** — `a` is narrower-than-or-equal to `b` (confers ≤ authority).
This MIRRORS `AuthRequired::is_narrower_or_equal` in `cell/src/permissions.rs` clause for
clause, in the SAME match order (the order is load-bearing: the first matching arm wins):

```
(Impossible, _)            => true        -- Impossible is the most restrictive (bottom)
(_, Impossible)            => false
(_, None)                  => true        -- None is the least restrictive (top)
(None, _)                  => false
(Proof, Either)            => true        -- Proof/Signature are narrower than Either
(Signature, Either)        => true
(Custom a, Custom b)       => a == b       -- Custom comparable only to identical Custom
(Custom _, _) | (_, Custom _) => false
(a, b)                     => a == b      -- same level
```
-/
def authNarrowerOrEqual : AuthReq → AuthReq → Bool
  | .impossible, _ => true
  | _, .impossible => false
  | _, .none => true
  | .none, _ => false
  | .proof, .either => true
  | .signature, .either => true
  | .custom a, .custom b => a == b
  | .custom _, _ => false
  | _, .custom _ => false
  | a, b => a == b

/-! ## §2 — It is a genuine attenuation order (reflexive / antisymmetric / transitive),
with `impossible` the bottom and `none` the top. Establishing these is what makes the
concrete decision a VALID `≤` — the property the abstract keystone presumes of its order. -/

/-- Reflexivity: every requirement is narrower-or-equal to itself. -/
theorem authNarrowerOrEqual_refl (a : AuthReq) : authNarrowerOrEqual a a = true := by
  cases a <;> simp [authNarrowerOrEqual]

/-- `impossible` is the BOTTOM: narrower than everything. -/
theorem authNarrowerOrEqual_impossible_bot (a : AuthReq) :
    authNarrowerOrEqual .impossible a = true := by
  simp [authNarrowerOrEqual]

/-- `none` is the TOP: everything is narrower than it. -/
theorem authNarrowerOrEqual_none_top (a : AuthReq) :
    authNarrowerOrEqual a .none = true := by
  cases a <;> simp [authNarrowerOrEqual]

/-- Antisymmetry: mutual narrower-or-equal forces equality. Rules out a cycle in the order
(e.g. a buggy `Signature ≤ Proof ∧ Proof ≤ Signature` would let two distinct caps be each
narrower than the other — an amplification loophole). -/
theorem authNarrowerOrEqual_antisymm {a b : AuthReq}
    (hab : authNarrowerOrEqual a b = true) (hba : authNarrowerOrEqual b a = true) :
    a = b := by
  cases a <;> cases b <;> simp_all [authNarrowerOrEqual]

/-- Transitivity: chaining two attenuations is an attenuation. The keystone closure property —
without it, a 3-vat handoff chain could amplify across hops. -/
theorem authNarrowerOrEqual_trans {a b c : AuthReq}
    (hab : authNarrowerOrEqual a b = true) (hbc : authNarrowerOrEqual b c = true) :
    authNarrowerOrEqual a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [authNarrowerOrEqual]

/-! ## §3 — `Impossible`/`None` extremes are sharp (a NEGATIVE tooth in Lean): granting
`None` (unauthenticated) over a held `Signature`/`Proof`/`Either`/`Custom`/`Impossible` is
NOT narrower-or-equal — it is AMPLIFICATION, and the decision says `false`. This is the
`amplifying_handoff_rejected` Rust test, in Lean. -/

/-- Granting `None` over any held requirement other than `None` itself is amplification. -/
theorem grant_none_over_nonnone_amplifies {held : AuthReq} (h : held ≠ .none) :
    authNarrowerOrEqual .none held = false := by
  cases held <;> simp_all [authNarrowerOrEqual]

/-- Conjuring `Signature` from a held `Impossible` (a locked cap) is amplification. -/
theorem grant_signature_over_impossible_amplifies :
    authNarrowerOrEqual .signature .impossible = false := by
  simp [authNarrowerOrEqual]

/-- Two DISTINCT `Custom` requirements are incomparable (neither narrower) — a handoff
cannot relabel one app-defined verifier as another. -/
theorem distinct_custom_incomparable {a b : Nat} (h : a ≠ b) :
    authNarrowerOrEqual (.custom a) (.custom b) = false := by
  simp [authNarrowerOrEqual, h]

/-! ## §4 — Tie to the abstract keystone via the effect-mask facet (the `u32` leg).

`is_facet_attenuation(parent, child) = (child &&& parent == child)` — child is a bitwise
subset of parent. We mirror it on `Nat` bit-AND (the `u32` masks are non-negative) and tie it
to the abstract `≤` of the bit-subset preorder. The handoff's facet leg
(`amplifies_effects` in `validate_handoff`) is exactly this. -/

/-- Mirror of `is_facet_attenuation`: child ⊆ parent under bitwise-AND. -/
def facetAttenuation (parent child : Nat) : Bool := (child &&& parent) == child

/-- Reflexive: a mask attenuates itself. -/
theorem facetAttenuation_refl (m : Nat) : facetAttenuation m m = true := by
  simp [facetAttenuation, Nat.and_self]

/-- Bottom: the empty mask (0, "deny all") attenuates everything. -/
theorem facetAttenuation_zero_bot (m : Nat) : facetAttenuation m 0 = true := by
  simp [facetAttenuation]

/-! ## §5 — The non-amplification DECISION the runtime enforces, as one predicate, and the
PROOF it implies the abstract `granted ≤ held`.

`validate_handoff` accepts iff BOTH legs hold: `authNarrowerOrEqual granted held` (the
permission lattice) AND the effect-mask leg. We package the combined concrete decision and
prove it transitive — the exact closure the cross-vat Granovetter chain needs. -/

/-- The concrete handoff non-amplification decision: granted ⊆ held on BOTH the permission
lattice and the effect-mask facet. `heldEff = none` means "held unrestricted"; a `none`
held-mask makes any granted mask attenuating (mirrors `(_, None) => false` amplifies-bit). -/
def handoffNonAmplifyingC
    (heldPerm grantedPerm : AuthReq) (heldEff grantedEff : Option Nat) : Bool :=
  authNarrowerOrEqual grantedPerm heldPerm &&
    (match heldEff, grantedEff with
     | none, _ => true                                  -- held unrestricted: granted attenuates
     | some _, none => false                            -- held restricted, granted unrestricted: amplify
     | some h, some g => facetAttenuation h g)          -- both restricted: g ⊆ h

/-- The decision composes (transitively) on the permission leg with `none` (unrestricted)
masks — a two-hop all-permission handoff chain is non-amplifying iff each hop is. The
load-bearing closure for cross-vat handoff. -/
theorem handoffNonAmplifyingC_trans_perm
    {a b c : AuthReq}
    (hab : handoffNonAmplifyingC a b none none = true)
    (hbc : handoffNonAmplifyingC b c none none = true) :
    handoffNonAmplifyingC a c none none = true := by
  simp only [handoffNonAmplifyingC, Bool.and_true] at hab hbc ⊢
  exact authNarrowerOrEqual_trans hbc hab

/-! ## §6 — INSTANTIATE the abstract `Exec.CapTP.handoff_non_amplifying` at the concrete
carrier. The abstract keystone is stated over `[SemilatticeInf Rights] [OrderTop Rights]`, so
to USE it at `AuthReq` we must exhibit those instances — and prove they are the order
`authNarrowerOrEqual` induces. The meet (greatest common attenuation) exists for every pair:
incomparable requirements (e.g. `Signature ⊓ Proof`, `custom 7 ⊓ custom 9`) meet at
`impossible` (the locked-cap bottom), and `none` is the top (the loosest requirement). So the
6-element `AuthReq` really IS a bounded meet-semilattice, and the abstract proof fires. -/

/-- The `≤` on `AuthReq` from `authNarrowerOrEqual`. -/
instance : LE AuthReq := ⟨fun a b => authNarrowerOrEqual a b = true⟩

theorem AuthReq.le_def (a b : AuthReq) : a ≤ b ↔ authNarrowerOrEqual a b = true := Iff.rfl

instance : Preorder AuthReq where
  le := (· ≤ ·)
  le_refl := authNarrowerOrEqual_refl
  le_trans a b c hab hbc := authNarrowerOrEqual_trans hab hbc

instance : PartialOrder AuthReq where
  le_antisymm a b hab hba := authNarrowerOrEqual_antisymm hab hba

/-- The meet (greatest lower bound) of two requirements: the loosest requirement still
narrower than both. Comparable pairs take the smaller; incomparable pairs collapse to
`impossible` (the locked-cap bottom — the only requirement below two incomparable ones). -/
def authMeet : AuthReq → AuthReq → AuthReq
  | .impossible, _ => .impossible
  | _, .impossible => .impossible
  | .none, b => b
  | a, .none => a
  | .signature, .signature => .signature
  | .proof, .proof => .proof
  | .either, .either => .either
  | .signature, .either => .signature
  | .either, .signature => .signature
  | .proof, .either => .proof
  | .either, .proof => .proof
  | .custom a, .custom b => if a == b then .custom a else .impossible
  | _, _ => .impossible

instance : Min AuthReq := ⟨authMeet⟩

theorem AuthReq.inf_def (a b : AuthReq) : a ⊓ b = authMeet a b := rfl

/-- The meet's value, with the inner `Custom`-equality `if` resolved both ways. -/
theorem authMeet_le_left (a b : AuthReq) : authNarrowerOrEqual (authMeet a b) a = true := by
  cases a <;> cases b <;> simp only [authMeet] <;>
    (try (split <;> simp_all [authNarrowerOrEqual])) <;>
    first | rfl | simp [authNarrowerOrEqual]

theorem authMeet_le_right (a b : AuthReq) : authNarrowerOrEqual (authMeet a b) b = true := by
  cases a <;> cases b <;> simp only [authMeet] <;>
    (try (split <;> simp_all [authNarrowerOrEqual])) <;>
    first | rfl | simp [authNarrowerOrEqual]

theorem authMeet_greatest (a b c : AuthReq)
    (hab : authNarrowerOrEqual a b = true) (hac : authNarrowerOrEqual a c = true) :
    authNarrowerOrEqual a (authMeet b c) = true := by
  cases a <;> cases b <;> cases c <;>
    simp_all [authMeet, authNarrowerOrEqual] <;>
    (split <;> simp_all [authNarrowerOrEqual])

instance : SemilatticeInf AuthReq where
  inf := authMeet
  inf_le_left a b := by rw [AuthReq.le_def]; exact authMeet_le_left a b
  inf_le_right a b := by rw [AuthReq.le_def]; exact authMeet_le_right a b
  le_inf a b c hab hac := by
    rw [AuthReq.le_def] at hab hac ⊢; exact authMeet_greatest a b c hab hac

instance : OrderTop AuthReq where
  top := .none
  le_top a := by rw [AuthReq.le_def]; exact authNarrowerOrEqual_none_top a

/-- **`handoff_concrete_attenuation` — the seam closed.** When the running validator's
concrete non-amplification decision accepts (`handoffNonAmplifyingC` true on the permission
leg), the abstract attenuation `granted ≤ held` holds at the CONCRETE `AuthReq` carrier. So
the proven `Exec.CapTP.handoff_non_amplifying` is exercised on this path: its `granted.rights ≤
held.rights` conclusion is exactly the decision the Rust runtime runs, on the same 6-element
lattice. -/
theorem handoff_concrete_attenuation
    {heldPerm grantedPerm : AuthReq} {heldEff grantedEff : Option Nat}
    (h : handoffNonAmplifyingC heldPerm grantedPerm heldEff grantedEff = true) :
    grantedPerm ≤ heldPerm := by
  rw [AuthReq.le_def]
  simp only [handoffNonAmplifyingC, Bool.and_eq_true] at h
  exact h.1

/-- **`handoff_concrete_confers`** — packaged with the abstract keystone: given a concrete
handoff whose validator-accepted caps share a target and whose perms pass
`handoffNonAmplifyingC`, the abstract `confers held granted` holds, so `handoff_is_introduce`
/ `handoff_non_amplifying` apply at THIS carrier. (`confers` = same target ∧ rights ≤.) -/
theorem handoff_concrete_confers
    {target : CellId} {heldPerm grantedPerm : AuthReq} {heldEff grantedEff : Option Nat}
    (h : handoffNonAmplifyingC heldPerm grantedPerm heldEff grantedEff = true) :
    confers (CellId := CellId) ⟨target, heldPerm⟩ ⟨target, grantedPerm⟩ :=
  ⟨rfl, handoff_concrete_attenuation h⟩

/-- **`handoff_non_amplifying_concrete` — the abstract keystone, FIRED at the concrete
carrier.** We feed a concrete validator-accepted handoff into the abstract
`Exec.CapTP.handoff_non_amplifying` and read back `granted.rights ≤ held.rights` on `AuthReq`.
This is the literal demonstration that the proven 3-vat Granovetter non-amplification governs
the SAME lattice `captp/src/handoff.rs` enforces — not just an abstract order. -/
theorem handoff_non_amplifying_concrete
    {target introducer recipient : CellId}
    {heldPerm grantedPerm : AuthReq} {heldEff grantedEff : Option Nat}
    {G : Graph CellId AuthReq} {consents : CellId → Prop} {attested : Prop}
    (hv : CapTP.HandoffValid
            { introducer := introducer, recipient := recipient
            , held := ⟨target, heldPerm⟩, granted := ⟨target, grantedPerm⟩ }
            G consents attested) :
    grantedPerm ≤ heldPerm :=
  CapTP.handoff_non_amplifying hv

/-! ## §7 — THE PINNED DECISION TABLE. Every `#guard` here is a row the Rust differential
test (`captp/tests/handoff_lattice_differential.rs`) ALSO checks. If the Rust
`is_narrower_or_equal` drifts from this table — or this table is edited to drift from the
proven order — the differential test fails. This is the negative tooth across the FFI gap.

Variants enumerated: none=0, signature=1, proof=2, either=3, impossible=4, custom 7, custom 9.
-/

section Table

/-- The 7 probe variants, matching the Rust test's corpus order. -/
def probes : List AuthReq :=
  [.none, .signature, .proof, .either, .impossible, .custom 7, .custom 9]

/-- The full decision table as a flat `List Bool`, row-major over `probes × probes`.
The Rust test reconstructs the SAME 49-entry vector and asserts equality. -/
def decisionTable : List Bool :=
  probes.flatMap fun a => probes.map fun b => authNarrowerOrEqual a b

-- PINNED: the exact 49-bit truth table. A drift in `authNarrowerOrEqual` (or the order
-- proofs that constrain it) changes this literal and trips the guard; the Rust test pins the
-- identical literal on its side.
#guard decisionTable ==
  [ -- a = none:        n     sig    prf    eit    imp    c7     c9
    true,  false, false, false, false, false, false,
    -- a = signature:
    true,  true,  false, true,  false, false, false,
    -- a = proof:
    true,  false, true,  true,  false, false, false,
    -- a = either:
    true,  false, false, true,  false, false, false,
    -- a = impossible:
    true,  true,  true,  true,  true,  true,  true,
    -- a = custom 7:
    true,  false, false, false, false, true,  false,
    -- a = custom 9:
    true,  false, false, false, false, false, true ]

-- Spot-pin the load-bearing amplification rows (granting MORE than held): every one is
-- `false` — the runtime MUST reject these.
#guard authNarrowerOrEqual .none .signature == false   -- grant unauth over sig: AMPLIFY
#guard authNarrowerOrEqual .none .impossible == false  -- grant unauth over locked: AMPLIFY
#guard authNarrowerOrEqual .either .signature == false -- grant either over sig: AMPLIFY
#guard authNarrowerOrEqual .signature .proof == false  -- sig and proof incomparable
#guard authNarrowerOrEqual .proof .signature == false
#guard authNarrowerOrEqual (.custom 7) (.custom 9) == false -- distinct customs incomparable
-- Attenuating rows that MUST be accepted:
#guard authNarrowerOrEqual .signature .either == true
#guard authNarrowerOrEqual .proof .either == true
#guard authNarrowerOrEqual .impossible .signature == true
#guard authNarrowerOrEqual .signature .none == true

-- Effect-mask pins (the facet leg).
#guard facetAttenuation 0b110 0b010 == true   -- {transfer,emit} ⊇ {emit}
#guard facetAttenuation 0b010 0b110 == false  -- {emit} ⊉ {transfer,emit}: AMPLIFY
#guard handoffNonAmplifyingC .signature .signature (some 0b010) none == false -- restricted held, unrestricted grant
#guard handoffNonAmplifyingC .signature .signature none (some 0b010) == true  -- unrestricted held

end Table

/-! ## §8 — Axiom hygiene. -/

#assert_axioms authNarrowerOrEqual_refl
#assert_axioms authNarrowerOrEqual_antisymm
#assert_axioms authNarrowerOrEqual_trans
#assert_axioms grant_none_over_nonnone_amplifies
#assert_axioms grant_signature_over_impossible_amplifies
#assert_axioms distinct_custom_incomparable
#assert_axioms facetAttenuation_refl
#assert_axioms handoffNonAmplifyingC_trans_perm
#assert_axioms handoff_concrete_attenuation
#assert_axioms handoff_concrete_confers
#assert_axioms handoff_non_amplifying_concrete

end Dregg2.Exec.CapTPConcrete
