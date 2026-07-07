import IpFilter

/-!
# CIDR IP filtering — correctness against an independent RFC specification

`IpFilter.lean` gives a *safety*-flavoured account of CIDR access filtering:
its theorems restate facts about its own `matchCidr` / `permits` definitions.
This module upgrades that to *correctness by refinement*.  We write a
specification of the mandated behaviour **from the RFCs, without reference to
the implementation**, and prove the deployed `IpFilter.permits` equals it on
every input.

## The specification (independent of the implementation)

**Prefix match (RFC 4632 §3.1 / RFC 3493 addressing).**  RFC 4632 defines a
CIDR block by a prefix `P` and a length `len`: an address `A` is *in the block*
iff the leading `len` bits of `A` equal the leading `len` bits of `P` — i.e.
`A AND mask(len) = P AND mask(len)`, where `mask(len)` keeps exactly the top
`len` bits.  Bit position `i` survives the mask iff `i < len`, so masked
equality is precisely *agreement at every position below `len`*.  We take that
as the spec, phrased purely by indexing (`getElem?`) and a quantifier over bit
positions — a definition that never mentions `List.take` or any implementation
construct:

  `PrefixAgree len A P  :=  ∀ i, i < len → A[i]? = P[i]?`

Two addresses of different families can never share a block (RFC 3493 keeps the
IPv4 and IPv6 address spaces disjoint), so a match also requires equal families.

**Access precedence (RFC-style ordered ACL, deny-first).**  A ruleset is an
ordered list of `(prefix, allow | deny)` entries with a default verdict.  The
mandated resolution is: if some deny entry matches the address, reject; else if
some allow entry matches, admit; else apply the default.  We phrase "some entry
of a given action matches" existentially (`∃ r ∈ rules, …`) — again with no
reference to the implementation's `List.any` fold.

## What is proved

* `matchCidr_iff_spec` — the deployed membership test agrees with `SpecMatch`
  on all inputs (bridges `List.take` prefix equality to the indexed spec).
* `permits_eq_specVerdict` — **the refinement.** The deployed decision
  `IpFilter.permits rs a` equals the RFC precedence verdict `SpecVerdict rs a`
  for every ruleset and every address.

## Non-vacuity

The spec is *not* the implementation renamed: membership is specified by
`∀ i < len, A[i]? = P[i]?` and matching by `List.take`, and the equivalence
(`take_eq_iff_prefixAgree`) is a real lemma proved from `ext_getElem?` /
`getElem?_take`.  Non-vacuity is witnessed concretely:

* a boundary address that differs from the network *inside* the prefix is
  rejected, while one that differs only *past* bit `len` is admitted
  (`spec_boundary_reject`, `spec_boundary_past_len_admit`);
* an off-by-one matcher that compares one bit too few **disagrees** with the
  spec on that boundary (`wrong_bit_count_fails`);
* an allow-first resolution **disagrees** with the deny-first spec when both a
  deny and an allow entry match (`wrong_precedence_fails`).

So an implementation comparing the wrong number of bits, or resolving the wrong
precedence, would fail `permits_eq_specVerdict`.
-/

namespace IpFilterCorrect

open IpFilter

/-! ## A bridge lemma: `List.take` prefix equality is indexed agreement

The implementation compares prefixes with `List.take`; the spec quantifies over
bit positions.  These coincide for all inputs. -/

/-- Comparing the length-`len` prefixes of two bit-strings by `List.take` is
equivalent to agreement at every position below `len`.  Proved from list
extensionality and the `getElem?` law for `take`, so the equivalence carries no
implementation content. -/
theorem take_eq_iff_prefixAgree (len : Nat) (a p : List Bool) :
    a.take len = p.take len ↔ ∀ i, i < len → a[i]? = p[i]? := by
  constructor
  · intro h i hi
    have hc := congrArg (fun l => l[i]?) h
    simp only [List.getElem?_take] at hc
    rwa [if_pos hi, if_pos hi] at hc
  · intro h
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_take, List.getElem?_take]
    by_cases hi : i < len
    · rw [if_pos hi, if_pos hi]; exact h i hi
    · rw [if_neg hi, if_neg hi]

/-! ## The independent specification -/

/-- **RFC 4632 prefix match**, specified by indexing: address `a` and network
`p` agree at every bit position strictly below the prefix length `len`
(equivalently `a AND mask(len) = p AND mask(len)`).  Defined without any
reference to `IpFilter`. -/
def PrefixAgree (len : Nat) (a p : List Bool) : Prop :=
  ∀ i, i < len → a[i]? = p[i]?

instance (len : Nat) (a p : List Bool) : Decidable (PrefixAgree len a p) :=
  Nat.decidableBallLT len (fun i _ => a[i]? = p[i]?)

/-- **Address is in a CIDR block** (RFC 4632 §3.1 + RFC 3493 family split): same
family, and the address agrees with the network on the top `len` bits. -/
def SpecMatch (c : Cidr) (a : Addr) : Prop :=
  c.family = a.family ∧ PrefixAgree c.len a.bits c.net

instance (c : Cidr) (a : Addr) : Decidable (SpecMatch c a) :=
  inferInstanceAs (Decidable (c.family = a.family ∧ PrefixAgree c.len a.bits c.net))

/-- **Some rule of the given action matches** the address — the existential
form of an ordered-ACL scan (independent of the implementation's `List.any`). -/
def SomeRuleMatches (rs : Ruleset) (act : Action) (a : Addr) : Prop :=
  ∃ r ∈ rs.rules, r.2 = act ∧ SpecMatch r.1 a

instance (rs : Ruleset) (act : Action) (a : Addr) :
    Decidable (SomeRuleMatches rs act a) :=
  inferInstanceAs (Decidable (∃ r ∈ rs.rules, r.2 = act ∧ SpecMatch r.1 a))

/-- **The mandated access verdict** (deny-first precedence): a matching deny
rejects; else a matching allow admits; else the default toggle decides. `true`
= permit.  Written over the independent `SomeRuleMatches`, not over `permits`. -/
def SpecVerdict (rs : Ruleset) (a : Addr) : Bool :=
  if SomeRuleMatches rs Action.deny a then false
  else if SomeRuleMatches rs Action.allow a then true
  else !rs.defaultDeny

/-! ## Bridge: deployed predicates agree with the spec -/

/-- The deployed membership test equals the RFC prefix-match spec on all inputs. -/
theorem matchCidr_iff_spec (c : Cidr) (a : Addr) :
    matchCidr c a = true ↔ SpecMatch c a := by
  simp only [matchCidr, decide_eq_true_iff, SpecMatch, PrefixAgree,
    take_eq_iff_prefixAgree]

/-- The deployed deny scan equals the existential deny-match spec. -/
theorem matchesDeny_iff (rs : Ruleset) (a : Addr) :
    matchesDeny rs a = true ↔ SomeRuleMatches rs Action.deny a := by
  unfold matchesDeny SomeRuleMatches
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hc⟩
    rw [Bool.and_eq_true, decide_eq_true_iff] at hc
    exact ⟨r, hr, hc.1, (matchCidr_iff_spec r.1 a).mp hc.2⟩
  · rintro ⟨r, hr, hact, hm⟩
    refine ⟨r, hr, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨hact, (matchCidr_iff_spec r.1 a).mpr hm⟩

/-- The deployed allow scan equals the existential allow-match spec. -/
theorem matchesAllow_iff (rs : Ruleset) (a : Addr) :
    matchesAllow rs a = true ↔ SomeRuleMatches rs Action.allow a := by
  unfold matchesAllow SomeRuleMatches
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hc⟩
    rw [Bool.and_eq_true, decide_eq_true_iff] at hc
    exact ⟨r, hr, hc.1, (matchCidr_iff_spec r.1 a).mp hc.2⟩
  · rintro ⟨r, hr, hact, hm⟩
    refine ⟨r, hr, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨hact, (matchCidr_iff_spec r.1 a).mpr hm⟩

/-! ## The refinement theorem

The DEPLOYED `IpFilter.permits` (the function `Ruleset` decisions run through)
equals the independent RFC verdict on every ruleset and address. -/

theorem permits_eq_specVerdict (rs : Ruleset) (a : Addr) :
    permits rs a = SpecVerdict rs a := by
  unfold permits SpecVerdict
  by_cases hd : SomeRuleMatches rs Action.deny a
  · simp [(matchesDeny_iff rs a).mpr hd, hd]
  · have hdb : matchesDeny rs a = false := by
      cases hb : matchesDeny rs a with
      | false => rfl
      | true => exact absurd ((matchesDeny_iff rs a).mp hb) hd
    by_cases ha : SomeRuleMatches rs Action.allow a
    · simp [hdb, (matchesAllow_iff rs a).mpr ha, hd, ha]
    · have hab : matchesAllow rs a = false := by
        cases hb : matchesAllow rs a with
        | false => rfl
        | true => exact absurd ((matchesAllow_iff rs a).mp hb) ha
      simp [hdb, hab, hd, ha]

/-! ## Non-vacuity witnesses

Concrete inputs proving the spec forbids a wrong implementation. -/

/-- Network `1 0 1 _`, prefix length 3: the block is exactly the addresses whose
top three bits are `1 0 1`. -/
def cEx : Cidr := { family := Family.v4, net := [true, false, true, false], len := 3 }

/-- Inside the block: top three bits `1 0 1` (the 4th bit is outside the prefix). -/
def aIn : Addr := { family := Family.v4, bits := [true, false, true, true] }

/-- Just OUTSIDE the block: differs from the network at bit index 2, which is
*inside* the prefix (`2 < 3`).  Must be rejected. -/
def aOut : Addr := { family := Family.v4, bits := [true, false, false, false] }

/-- Differs from the network only at bit index 3 = `len`, *past* the prefix.
Must still match — only the top `len` bits are compared. -/
def aPastLen : Addr := { family := Family.v4, bits := [true, false, true, true] }

/-- Boundary: an address inside the prefix matches. -/
theorem spec_in_admit : SpecMatch cEx aIn := by decide

/-- Boundary: an address that differs *inside* the prefix is rejected —
the match compares all `len` bits, not fewer. -/
theorem spec_boundary_reject : ¬ SpecMatch cEx aOut := by decide

/-- Boundary: an address that differs only *past* bit `len` still matches —
the match compares no more than `len` bits. -/
theorem spec_boundary_past_len_admit : SpecMatch cEx aPastLen := by decide

/-- A deliberately wrong membership test comparing one bit too FEW.  Exhibited
only to witness non-vacuity. -/
def matchCidrWrong (c : Cidr) (a : Addr) : Bool :=
  decide (c.family = a.family ∧ a.bits.take (c.len - 1) = c.net.take (c.len - 1))

/-- **Wrong bit count fails the spec.**  The off-by-one matcher admits `aOut`
(it only checks the first two bits, which agree), but the RFC spec rejects it —
so an implementation comparing the wrong number of bits violates
`matchCidr_iff_spec`. -/
theorem wrong_bit_count_fails :
    matchCidrWrong cEx aOut ≠ decide (SpecMatch cEx aOut) := by decide

/-- A ruleset where the SAME block is both allowed and denied: deny must win. -/
def rsBoth : Ruleset :=
  { rules := [(cEx, Action.allow), (cEx, Action.deny)], defaultDeny := false }

/-- Deny-precedence is real end-to-end: the deployed `permits` rejects an
address that matches both an allow and a deny rule. -/
theorem deny_wins_deployed : permits rsBoth aIn = false := by decide

/-- An allow-first resolution (WRONG precedence). -/
def specVerdictWrong (rs : Ruleset) (a : Addr) : Bool :=
  if SomeRuleMatches rs Action.allow a then true
  else if SomeRuleMatches rs Action.deny a then false
  else !rs.defaultDeny

/-- **Wrong precedence fails the spec.**  When both a deny and an allow entry
match, allow-first permits but the deny-first spec rejects — so an
implementation with the wrong precedence violates `permits_eq_specVerdict`. -/
theorem wrong_precedence_fails :
    specVerdictWrong rsBoth aIn ≠ SpecVerdict rsBoth aIn := by decide

end IpFilterCorrect
