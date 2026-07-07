import Trace.W3C

/-!
# Correctness of `traceparent` parsing (W3C Trace Context, §3.2)

`Trace/W3C.lean` establishes *safety* facts about the `traceparent` parser — it
is total (`parse_total`), and on success the unconsumed tail is a suffix of the
input (`parse_suffix`, `parse_consumed_monotone`). Those say the parser never
runs off the input. They do **not** say the parser splits the fields at the
right boundaries, nor that it accepts exactly the headers the spec calls valid.

This file upgrades that to a *correctness* claim: `Trace.parse` accepts a token
stream and returns the four fields **iff** that stream is a well-formed
`traceparent` under the W3C grammar, with the fields split at exactly the spec's
boundaries.

## The W3C grammar (§3.2.1, ABNF)

The `traceparent` header field value is

    traceparent    = version "-" version-format
    version        = 2HEXDIGLC            ; this document assumes version 00
    version-format = trace-id "-" parent-id "-" trace-flags
    trace-id       = 32HEXDIGLC           ; 16-byte array
    parent-id      = 16HEXDIGLC           ; 8-byte array
    trace-flags    = 2HEXDIGLC            ; 8-bit field

so the value is exactly

    version(2) "-" trace-id(32) "-" parent-id(16) "-" trace-flags(2)

over hex digits and `-` delimiters. §3.2.2.3 adds two validity constraints:

* trace-id — "All bytes as zero (`00000000000000000000000000000000`) is
  considered an **invalid** value."
* parent-id — "All bytes as zero (`0000000000000000`) is considered an
  **invalid** value."

A header that does not match the grammar, or that violates either all-zero
constraint, is rejected.

## The specification (independent of the parser)

`Traceparent ts tp` below is a predicate on a token stream `ts` and a candidate
field record `tp`, written straight from the ABNF above and the §3.2.2.3
constraints. It refers only to the wire datatypes (`Tok`, `Nibble`,
`TraceParent`) — never to `parse`, `takeNibs`, `expectDash`, or `allZero`. In
particular the all-zero constraint is phrased as the spec states it, "not all
bytes zero", i.e. `∃ x ∈ …, x ≠ 0`, with no reference to the implementation's
`allZero` helper.

## The refinement

`parse_correct` proves, for the **deployed** `Trace.parse`,

    parse ts = .ok (tp, []) ↔ Traceparent ts tp

— the parser accepts a stream to exactly its four fields (consuming all of it)
precisely when the stream is a grammar-valid `traceparent` with those fields.

This is non-vacuous in both directions:

* An implementation that **mis-split** the fields (e.g. took 16 hex digits for
  the trace-id instead of 32) would fail the `←` direction: a grammar-valid
  header would no longer parse to its declared fields with an empty tail.
* An implementation that **accepted an all-zero** trace-id or parent-id would
  fail the `→` direction (`parse_sound`): it would return `.ok` on a stream that
  the spec predicate rejects, since `Traceparent` demands a non-zero id.
  `zero_traceId_rejected` records that consequence directly against `parse`.
-/

namespace Trace

/-- Render a run of hex nibbles as its `traceparent` tokens: the ABNF
`nHEXDIGLC` production is a sequence of hex digits, one `nib` token each. This is
the only bridge between an abstract field (a `List Nibble`) and its on-the-wire
tokens; it does not mention the parser. -/
def hexToks (xs : List Nibble) : List Tok := xs.map Tok.nib

@[simp] theorem hexToks_nil : hexToks [] = [] := rfl

@[simp] theorem hexToks_cons (a : Nibble) (xs : List Nibble) :
    hexToks (a :: xs) = Tok.nib a :: hexToks xs := rfl

/-- **The specification.**  `Traceparent ts tp` says the token stream `ts` is a
well-formed W3C `traceparent` header whose four fields are those of `tp`, read
directly off the §3.2.1 grammar and the §3.2.2.3 all-zero constraints:

* each field is a hex run of the mandated width (2 / 32 / 16 / 2 nibbles);
* the trace-id is not all-zero, and the parent-id is not all-zero (§3.2.2.3);
* the whole stream is exactly the fields interleaved with the three `-`
  delimiters — nothing before, between (beyond the delimiters), or after.

Defined without any reference to `parse` or its helpers. -/
structure Traceparent (ts : List Tok) (tp : TraceParent) : Prop where
  /-- `version = 2HEXDIGLC`. -/
  versionLen : tp.version.length = 2
  /-- `trace-id = 32HEXDIGLC`. -/
  traceIdLen : tp.traceId.length = 32
  /-- `parent-id = 16HEXDIGLC`. -/
  parentIdLen : tp.parentId.length = 16
  /-- `trace-flags = 2HEXDIGLC`. -/
  flagsLen : tp.flags.length = 2
  /-- §3.2.2.3: an all-zero trace-id is invalid, so some nibble is non-zero. -/
  traceIdSet : ∃ x ∈ tp.traceId, x ≠ 0
  /-- §3.2.2.3: an all-zero parent-id is invalid, so some nibble is non-zero. -/
  parentIdSet : ∃ x ∈ tp.parentId, x ≠ 0
  /-- The exact `version "-" trace-id "-" parent-id "-" trace-flags` layout. -/
  layout : ts = hexToks tp.version ++ [Tok.dash] ++ hexToks tp.traceId ++ [Tok.dash]
                  ++ hexToks tp.parentId ++ [Tok.dash] ++ hexToks tp.flags

/-! ### Characterizing the parser's helpers against `hexToks` -/

/-- `takeNibs` reads a hex run: `takeNibs n ts = some (xs, r)` means `xs` is
exactly the first `n` nibbles rendered off the front and `r` is what remains. -/
theorem takeNibs_sound : ∀ (n : Nat) (ts : List Tok) (xs : List Nibble) (r : List Tok),
    takeNibs n ts = some (xs, r) → xs.length = n ∧ ts = hexToks xs ++ r := by
  intro n
  induction n with
  | zero =>
    intro ts xs r h
    simp only [takeNibs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp⟩
  | succ n ih =>
    intro ts xs r h
    cases ts with
    | nil => simp [takeNibs] at h
    | cons t ts' =>
      cases t with
      | dash => simp [takeNibs] at h
      | nib x =>
        simp only [takeNibs] at h
        cases hn : takeNibs n ts' with
        | none => rw [hn] at h; simp at h
        | some p =>
          obtain ⟨xs', r'⟩ := p
          rw [hn] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hlen, heq⟩ := ih ts' xs' r' hn
          exact ⟨by simp [hlen], by simp [heq]⟩

/-- The converse: a hex run of `xs` followed by any tail `r` is read back
exactly as `xs` with remainder `r`. -/
theorem takeNibs_complete : ∀ (xs : List Nibble) (r : List Tok),
    takeNibs xs.length (hexToks xs ++ r) = some (xs, r) := by
  intro xs
  induction xs with
  | nil => intro r; simp [takeNibs]
  | cons a xs ih =>
    intro r
    simp only [hexToks_cons, List.length_cons, List.cons_append, takeNibs, ih r]

/-- A hex run with no tail is read back exactly, leaving nothing. -/
theorem takeNibs_complete_nil (xs : List Nibble) :
    takeNibs xs.length (hexToks xs) = some (xs, []) := by
  have h := takeNibs_complete xs []
  simpa using h

/-- `expectDash` consumes exactly a leading `-` delimiter. -/
theorem expectDash_sound {ts r : List Tok} (h : expectDash ts = some r) :
    ts = Tok.dash :: r := by
  cases ts with
  | nil => simp [expectDash] at h
  | cons t ts' =>
    cases t with
    | dash => simp only [expectDash, Option.some.injEq] at h; rw [h]
    | nib x => simp [expectDash] at h

/-- `allZero xs = false` is exactly the spec's "not all bytes zero": some nibble
is non-zero.  This bridges the implementation helper to the §3.2.2.3 wording so
that neither the spec nor the refinement statement mentions `allZero`. -/
theorem allZero_false_iff {xs : List Nibble} : allZero xs = false ↔ ∃ x ∈ xs, x ≠ 0 := by
  induction xs with
  | nil => simp [allZero]
  | cons a xs ih =>
    have hc : allZero (a :: xs) = ((a == 0) && allZero xs) := by simp [allZero]
    rw [hc, Bool.and_eq_false_iff, ih]
    constructor
    · rintro (h | ⟨x, hx, hne⟩)
      · refine ⟨a, List.mem_cons_self a xs, ?_⟩
        intro hEq; subst hEq; simp at h
      · exact ⟨x, List.mem_cons_of_mem a hx, hne⟩
    · rintro ⟨x, hx, hne⟩
      rcases List.mem_cons.mp hx with rfl | hin
      · left
        cases hb : (x == (0 : Nibble)) with
        | true => exact absurd (by simpa using hb) hne
        | false => rfl
      · exact Or.inr ⟨x, hin, hne⟩

/-! ### The refinement -/

/-- **Soundness.**  If the deployed `parse` accepts the whole stream `ts` to the
fields `tp`, then `ts` is a grammar-valid `traceparent` with those fields. -/
theorem parse_sound {ts : List Tok} {tp : TraceParent}
    (h : parse ts = .ok (tp, [])) : Traceparent ts tp := by
  unfold parse at h
  cases h2 : takeNibs 2 ts with
  | none => simp [h2] at h
  | some p2 =>
    obtain ⟨ver, ts1⟩ := p2
    simp only [h2] at h
    cases h3 : expectDash ts1 with
    | none => simp [h3] at h
    | some ts2 =>
      simp only [h3] at h
      cases h4 : takeNibs 32 ts2 with
      | none => simp [h4] at h
      | some p4 =>
        obtain ⟨tid, ts3⟩ := p4
        simp only [h4] at h
        cases h5 : expectDash ts3 with
        | none => simp [h5] at h
        | some ts4 =>
          simp only [h5] at h
          cases h6 : takeNibs 16 ts4 with
          | none => simp [h6] at h
          | some p6 =>
            obtain ⟨pid, ts5⟩ := p6
            simp only [h6] at h
            cases h7 : expectDash ts5 with
            | none => simp [h7] at h
            | some ts6 =>
              simp only [h7] at h
              cases h8 : takeNibs 2 ts6 with
              | none => simp [h8] at h
              | some p8 =>
                obtain ⟨fl, ts7⟩ := p8
                simp only [h8] at h
                cases hz1 : allZero tid with
                | true => simp [hz1] at h
                | false =>
                  cases hz2 : allZero pid with
                  | true => simp [hz1, hz2] at h
                  | false =>
                    simp only [hz1, hz2, Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    obtain ⟨hlen2, he2⟩ := takeNibs_sound 2 ts ver ts1 h2
                    have he3 := expectDash_sound h3
                    obtain ⟨hlen4, he4⟩ := takeNibs_sound 32 ts2 tid ts3 h4
                    have he5 := expectDash_sound h5
                    obtain ⟨hlen6, he6⟩ := takeNibs_sound 16 ts4 pid ts5 h6
                    have he7 := expectDash_sound h7
                    obtain ⟨hlen8, he8⟩ := takeNibs_sound 2 ts6 fl [] h8
                    refine
                      { versionLen := hlen2
                        traceIdLen := hlen4
                        parentIdLen := hlen6
                        flagsLen := hlen8
                        traceIdSet := allZero_false_iff.mp hz1
                        parentIdSet := allZero_false_iff.mp hz2
                        layout := ?_ }
                    rw [he2, he3, he4, he5, he6, he7, he8]
                    simp [List.append_assoc]

/-- **Completeness.**  A grammar-valid `traceparent` is accepted by the deployed
`parse` to exactly its four fields, consuming the whole stream. -/
theorem parse_complete {ts : List Tok} {tp : TraceParent}
    (h : Traceparent ts tp) : parse ts = .ok (tp, []) := by
  obtain ⟨hv, htid, hpid, hfl, htidset, hpidset, hlayout⟩ := h
  have ha : allZero tp.traceId = false := allZero_false_iff.mpr htidset
  have hb : allZero tp.parentId = false := allZero_false_iff.mpr hpidset
  have e1 : takeNibs 2 (hexToks tp.version ++
        (Tok.dash :: (hexToks tp.traceId ++ (Tok.dash ::
          (hexToks tp.parentId ++ (Tok.dash :: hexToks tp.flags))))))
      = some (tp.version, (Tok.dash :: (hexToks tp.traceId ++ (Tok.dash ::
          (hexToks tp.parentId ++ (Tok.dash :: hexToks tp.flags)))))) := by
    rw [← hv]; exact takeNibs_complete _ _
  have e3 : takeNibs 32 (hexToks tp.traceId ++ (Tok.dash ::
          (hexToks tp.parentId ++ (Tok.dash :: hexToks tp.flags))))
      = some (tp.traceId, (Tok.dash :: (hexToks tp.parentId ++ (Tok.dash :: hexToks tp.flags)))) := by
    rw [← htid]; exact takeNibs_complete _ _
  have e5 : takeNibs 16 (hexToks tp.parentId ++ (Tok.dash :: hexToks tp.flags))
      = some (tp.parentId, (Tok.dash :: hexToks tp.flags)) := by
    rw [← hpid]; exact takeNibs_complete _ _
  have e7 : takeNibs 2 (hexToks tp.flags) = some (tp.flags, []) := by
    rw [← hfl]; exact takeNibs_complete_nil _
  have hL : ts = hexToks tp.version ++
        (Tok.dash :: (hexToks tp.traceId ++ (Tok.dash ::
          (hexToks tp.parentId ++ (Tok.dash :: hexToks tp.flags))))) := by
    rw [hlayout]; simp [List.append_assoc]
  rw [hL]
  unfold parse
  simp only [e1, expectDash, e3, e5, e7, ha, hb]

/-- **The refinement (theorem 5 for `traceparent`).**  For the deployed
`Trace.parse`, accepting a stream to its four fields with nothing left over is
exactly grammar-validity under the W3C `traceparent` ABNF and its all-zero
constraints. -/
theorem parse_correct {ts : List Tok} {tp : TraceParent} :
    parse ts = .ok (tp, []) ↔ Traceparent ts tp :=
  ⟨parse_sound, parse_complete⟩

/-! ### Non-vacuity witnesses -/

/-- The spec genuinely forbids an all-zero trace-id: no all-zero-trace-id stream
is a valid `traceparent`, and therefore the deployed `parse` never accepts one.
An implementation that accepted an all-zero trace-id would make this false. -/
theorem zero_traceId_rejected {ts : List Tok} {tp : TraceParent}
    (hz : ∀ x ∈ tp.traceId, x = 0) : parse ts ≠ .ok (tp, []) := by
  intro hok
  obtain ⟨-, -, -, -, ⟨x, hx, hne⟩, -, -⟩ := parse_sound hok
  exact hne (hz x hx)

/-- A concrete valid header: version `00`, a trace-id and a parent-id whose last
nibble is `1` (so neither is all-zero), and flags `00`.  It parses to exactly
those fields with nothing left over — exercising the `←` (completeness) edge and
pinning the 2/32/16/2 field split. -/
def demoTP : TraceParent :=
  ⟨List.replicate 2 0, List.replicate 31 0 ++ [1], List.replicate 15 0 ++ [1], List.replicate 2 0⟩

def demoValid : List Tok :=
  hexToks demoTP.version ++ [Tok.dash] ++ hexToks demoTP.traceId ++ [Tok.dash]
    ++ hexToks demoTP.parentId ++ [Tok.dash] ++ hexToks demoTP.flags

example : parse demoValid = .ok (demoTP, []) := by
  apply parse_complete
  refine { versionLen := rfl, traceIdLen := ?_, parentIdLen := ?_, flagsLen := rfl,
           traceIdSet := ?_, parentIdSet := ?_, layout := rfl }
  · simp [demoTP]
  · simp [demoTP]
  · exact ⟨1, by simp [demoTP], by decide⟩
  · exact ⟨1, by simp [demoTP], by decide⟩

end Trace
