import H2.Hpack
import Proto.Kernel.Shortcuts

/-!
# HTTP/2 pseudo-header validation (RFC 9113 §8.3)

The HPACK decoder (`H2/Hpack.lean`) turns a HEADERS/CONTINUATION block into an
*ordered* list of decoded `(name, value)` byte-string pairs. RFC 9113 §8.3 then
imposes structural rules on that ordered list before it becomes a request. A
field block that breaks any of them is a **malformed request** (treated by the
peer as a stream error of type `PROTOCOL_ERROR`). The four rules this module
makes into theorems:

* **Ordering (§8.3).** All pseudo-header fields (names beginning with `:`) MUST
  appear before any regular header field. A pseudo-header after a regular field
  is malformed — `pseudo_before_regular`.
* **No duplicates (§8.3).** The same request pseudo-header name MUST NOT appear
  more than once. A second `:method` / `:path` / `:scheme` / `:authority` is
  malformed — `pseudo_no_duplicate`.
* **Required set (§8.3.1).** A well-formed request necessarily carries the
  `:method`, `:scheme`, and `:path` pseudo-headers — `pseudo_required`.
* **Unknown pseudo (§8.3).** A field whose name begins with `:` but is not one
  of the defined request pseudo-headers (e.g. `:status`, a *response*
  pseudo-header) is malformed — `pseudo_unknown_rejected`.

The validator is a single left-to-right scan over the decoded list, tracking a
five-flag `Seen` accumulator, followed by the required-set check. The four
headline theorems are *general* statements over arbitrary surrounding context
lists, proven by structural induction on the scan (no fixed-input tautologies).
A worked well-formed request (`goodRequest_ok`) and four mutant
counter-examples anchor non-vacuity on real byte strings.

Note on the witnesses: `strBytes s = s.toUTF8.toList` bottoms out in
`ByteArray`'s well-founded `toList` loop, which the kernel does not reduce. That wall
is real, but it no longer forces compiler evaluation: `Proto.Kernel.Shortcuts`
(§1 `ba_toList_eq`, §2 `toUTF8_toList_ascii`) rewrites a `toUTF8`-derived byte list to
a structural `s.data.map` the kernel DOES reduce, so the concrete-byte witnesses are
discharged by `simp`+kernel `decide`. Nothing in this file uses `native_decide`; every
theorem here, headline and witness alike, stays within
`{propext, Quot.sound, Classical.choice}` — no `Lean.ofReduceBool`.

Ground truth: `H2/Hpack.lean` (`strBytes`, `classifyName`, `PseudoKind`, the
decoded header list) and RFC 9113 §8.3 / §8.3.1.
-/

namespace H2
namespace PseudoHeader

open Hpack (strBytes classifyName PseudoKind)

/-- One decoded header field: an ordered name/value byte-string pair, exactly
as it leaves the HPACK decoder. -/
abbrev Header := Bytes × Bytes

/-- ASCII colon `:` (0x3A). A pseudo-header field name is any name whose first
octet is a colon (RFC 9113 §8.3). -/
def colon : UInt8 := 0x3a

/-- `true` iff `n` is a pseudo-header name, i.e. begins with `:`. This is the
purely-syntactic membership test §8.3 uses to separate pseudo-headers from
regular fields — independent of whether the name is one we recognise. -/
def isPseudoName (n : Bytes) : Bool :=
  match n with
  | b :: _ => b == colon
  | []     => false

/-! ## The `Seen` accumulator -/

/-- Progress of the scan: which request pseudo-headers have already been seen,
and whether any regular (non-pseudo) header has been seen. Every flag is
monotone — once set it never clears (see `stepReq_le`). -/
structure Seen where
  method    : Bool := false
  path      : Bool := false
  scheme    : Bool := false
  authority : Bool := false
  regular   : Bool := false
deriving Repr, DecidableEq

/-- Is pseudo-header kind `k` already recorded? -/
def Seen.has : Seen → PseudoKind → Bool
  | s, .method    => s.method
  | s, .path      => s.path
  | s, .scheme    => s.scheme
  | s, .authority => s.authority

/-- Record that pseudo-header kind `k` has been seen. -/
def Seen.mark (s : Seen) : PseudoKind → Seen
  | .method    => { s with method := true }
  | .path      => { s with path := true }
  | .scheme    => { s with scheme := true }
  | .authority => { s with authority := true }

/-- Typed malformed-request reasons (RFC 9113 §8.3 / §8.3.1). -/
inductive Malformed where
  /-- A pseudo-header field appeared after a regular header field (§8.3). -/
  | regularBeforePseudo
  /-- A request pseudo-header name appeared more than once (§8.3). -/
  | duplicatePseudo
  /-- A `:`-prefixed name that is not a defined request pseudo-header (§8.3). -/
  | unknownPseudo
  /-- The request is missing `:method`, `:scheme`, or `:path` (§8.3.1). -/
  | missingRequired
deriving Repr, DecidableEq

/-! ## The scan and the validator -/

/-- Fold one header into the accumulator. A pseudo-header is accepted only
before any regular field (ordering), only if it is a recognised request pseudo
(unknown rejected), and only if it has not already been seen (no duplicates). A
regular field just latches `regular`. -/
def stepReq (s : Seen) (h : Header) : Except Malformed Seen :=
  if isPseudoName h.1 then
    if s.regular then
      .error .regularBeforePseudo
    else
      match classifyName h.1 with
      | some k => if s.has k then .error .duplicatePseudo else .ok (s.mark k)
      | none   => .error .unknownPseudo
  else
    .ok { s with regular := true }

/-- Left-to-right scan of the decoded header list from a starting accumulator.
The first failing field short-circuits. -/
def scan (s : Seen) : List Header → Except Malformed Seen
  | []      => .ok s
  | h :: t  =>
    match stepReq s h with
    | .ok s'  => scan s' t
    | .error e => .error e

/-- Validate a decoded HTTP/2 request header list against RFC 9113 §8.3 /
§8.3.1: run the ordering / duplicate / unknown scan, then require `:method`,
`:scheme`, and `:path`. Returns `ok ()` for a well-formed request. -/
def validateRequest (hs : List Header) : Except Malformed Unit :=
  match scan {} hs with
  | .error e => .error e
  | .ok s    => if s.method && s.scheme && s.path then .ok () else .error .missingRequired

/-! ## Marking lemmas -/

/-- Marking preserves flags that were already set. -/
theorem mark_has_mono (s : Seen) (j k : PseudoKind) (h : s.has j = true) :
    (s.mark k).has j = true := by
  cases k <;> cases j <;> simp_all [Seen.mark, Seen.has]

/-- Marking `k` records `k`. -/
theorem mark_has_self (s : Seen) (k : PseudoKind) : (s.mark k).has k = true := by
  cases k <;> rfl

/-- Marking never touches the regular-seen flag. -/
theorem mark_regular (s : Seen) (k : PseudoKind) : (s.mark k).regular = s.regular := by
  cases k <;> rfl

/-! ## Monotonicity of the scan -/

/-- The monotone order on accumulators: every set flag stays set. -/
def Seen.le (a b : Seen) : Prop :=
  (∀ k, a.has k = true → b.has k = true) ∧ (a.regular = true → b.regular = true)

theorem Seen.le_refl (s : Seen) : Seen.le s s := ⟨fun _ h => h, fun h => h⟩

theorem Seen.le_trans {a b c : Seen} (h1 : Seen.le a b) (h2 : Seen.le b c) :
    Seen.le a c :=
  ⟨fun k hk => h2.1 k (h1.1 k hk), fun hr => h2.2 (h1.2 hr)⟩

/-- One step is monotone: a successful `stepReq` only ever adds flags. -/
theorem stepReq_le {s s' : Seen} {h : Header} (he : stepReq s h = .ok s') :
    Seen.le s s' := by
  unfold stepReq at he
  split at he
  · -- pseudo-header
    split at he
    · exact absurd he (by simp)
    · split at he
      · rename_i k _
        split at he
        · exact absurd he (by simp)
        · cases he
          refine ⟨fun j hj => mark_has_mono s j k hj, fun hr => ?_⟩
          rw [mark_regular]; exact hr
      · exact absurd he (by simp)
  · -- regular header
    cases he
    exact ⟨fun j hj => by cases j <;> exact hj, fun _ => rfl⟩

/-- The scan is monotone: a successful scan only ever adds flags. -/
theorem scan_le {s s' : Seen} {l : List Header} (he : scan s l = .ok s') :
    Seen.le s s' := by
  induction l generalizing s with
  | nil => cases he; exact Seen.le_refl _
  | cons h t ih =>
    unfold scan at he
    split at he
    · rename_i s1 hstep
      exact Seen.le_trans (stepReq_le hstep) (ih he)
    · exact absurd he (by simp)

/-- Scanning a concatenation threads the accumulator through the prefix. -/
theorem scan_append (s : Seen) (a b : List Header) :
    scan s (a ++ b) = (match scan s a with
                        | .ok s' => scan s' b
                        | .error e => .error e) := by
  induction a generalizing s with
  | nil => rfl
  | cons h t ih =>
    simp only [List.cons_append, scan]
    cases stepReq s h with
    | ok s1 => exact ih s1
    | error e => rfl

/-! ## Single-step characterisations -/

/-- A pseudo-header field encountered once a regular field has been seen aborts
the step (the ordering core, §8.3). -/
theorem stepReq_pseudo_after_regular {s : Seen} {h : Header}
    (hp : isPseudoName h.1 = true) (hr : s.regular = true) :
    stepReq s h = .error .regularBeforePseudo := by
  unfold stepReq; simp only [hp, hr, if_true]

/-- A regular field always steps to a state with `regular` set. -/
theorem stepReq_regular_ok {s s' : Seen} {h : Header}
    (hp : isPseudoName h.1 = false) (he : stepReq s h = .ok s') :
    s'.regular = true := by
  unfold stepReq at he; simp only [hp, if_false] at he
  cases he; rfl

/-- A successful step on a recognised pseudo-header records its kind. -/
theorem stepReq_pseudo_ok_has {s s' : Seen} {h : Header} {k : PseudoKind}
    (hp : isPseudoName h.1 = true) (hc : classifyName h.1 = some k)
    (he : stepReq s h = .ok s') : s'.has k = true := by
  unfold stepReq at he
  simp only [hp, if_true, hc] at he
  split at he
  · exact absurd he (by simp)
  · split at he
    · exact absurd he (by simp)
    · cases he; exact mark_has_self s k

/-- A recognised request pseudo-header whose kind is already seen aborts the
step (the duplicate core, §8.3). -/
theorem stepReq_dup {s : Seen} {h : Header} {k : PseudoKind}
    (hp : isPseudoName h.1 = true) (hc : classifyName h.1 = some k)
    (hhas : s.has k = true) : ∃ e, stepReq s h = .error e := by
  cases hr : s.regular
  · exact ⟨.duplicatePseudo, by unfold stepReq; simp [hp, hr, hc, hhas]⟩
  · exact ⟨.regularBeforePseudo, stepReq_pseudo_after_regular hp hr⟩

/-- A `:`-prefixed name that is not a recognised request pseudo aborts the step
(the unknown core, §8.3). -/
theorem stepReq_unknown {s : Seen} {h : Header}
    (hp : isPseudoName h.1 = true) (hc : classifyName h.1 = none) :
    ∃ e, stepReq s h = .error e := by
  cases hr : s.regular
  · exact ⟨.unknownPseudo, by unfold stepReq; simp [hp, hr, hc]⟩
  · exact ⟨.regularBeforePseudo, stepReq_pseudo_after_regular hp hr⟩

/-- A step on a header whose name does not classify to `k` leaves the `k`-flag
unchanged. -/
theorem stepReq_other_preserves {s s' : Seen} {h : Header} {k : PseudoKind}
    (hk : classifyName h.1 ≠ some k) (he : stepReq s h = .ok s') :
    s'.has k = s.has k := by
  unfold stepReq at he
  split at he
  · split at he
    · exact absurd he (by simp)
    · split at he
      · rename_i k' _
        split at he
        · exact absurd he (by simp)
        · cases he
          have hne : k' ≠ k := by rintro rfl; exact hk ‹_›
          cases k <;> cases k' <;> first | rfl | (simp_all [Seen.mark, Seen.has])
      · exact absurd he (by simp)
  · cases he; cases k <;> rfl

/-! ## Scan-level witnesses -/

/-- If a well-formed scan processed a regular field, `regular` is set at the end. -/
theorem scan_regular_witness {l : List Header} {s s' : Seen}
    (he : scan s l = .ok s') (hw : ∃ h ∈ l, isPseudoName h.1 = false) :
    s'.regular = true := by
  induction l generalizing s with
  | nil => obtain ⟨_, hin, _⟩ := hw; exact absurd hin (by simp)
  | cons h t ih =>
    unfold scan at he
    split at he
    · rename_i s1 hstep
      obtain ⟨x, hx, hxr⟩ := hw
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact (scan_le he).2 (stepReq_regular_ok hxr hstep)
      · exact ih he ⟨x, hxt, hxr⟩
    · exact absurd he (by simp)

/-- If a well-formed scan processed a recognised pseudo-header of kind `k`, the
`k`-flag is set at the end. -/
theorem scan_has_witness {l : List Header} {s s' : Seen} {k : PseudoKind}
    (he : scan s l = .ok s')
    (hw : ∃ h ∈ l, isPseudoName h.1 = true ∧ classifyName h.1 = some k) :
    s'.has k = true := by
  induction l generalizing s with
  | nil => obtain ⟨_, hin, _⟩ := hw; exact absurd hin (by simp)
  | cons h t ih =>
    unfold scan at he
    split at he
    · rename_i s1 hstep
      obtain ⟨x, hx, hxp, hxc⟩ := hw
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact (scan_le he).1 k (stepReq_pseudo_ok_has hxp hxc hstep)
      · exact ih he ⟨x, hxt, hxp, hxc⟩
    · exact absurd he (by simp)

/-- A set flag at the end of a scan came either from the starting state or from
a classifying header in the list. -/
theorem scan_has_source {l : List Header} {s s' : Seen} {k : PseudoKind}
    (he : scan s l = .ok s') (hset : s'.has k = true) :
    s.has k = true ∨ ∃ h ∈ l, classifyName h.1 = some k := by
  induction l generalizing s with
  | nil => cases he; exact Or.inl hset
  | cons hd t ih =>
    unfold scan at he
    split at he
    · rename_i s1 hstep
      rcases ih (s := s1) he with hs1 | hwit
      · cases hdk : decide (classifyName hd.1 = some k) with
        | true => exact Or.inr ⟨hd, List.mem_cons_self .., of_decide_eq_true hdk⟩
        | false =>
          have hpres := stepReq_other_preserves (of_decide_eq_false hdk) hstep
          rw [hpres] at hs1; exact Or.inl hs1
      · obtain ⟨x, hx, hxc⟩ := hwit
        exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hxc⟩
    · exact absurd he (by simp)

/-- A set flag at the end of a scan from the empty accumulator is witnessed by a
classifying header. -/
theorem scan_flag_witness {l : List Header} {s' : Seen} {k : PseudoKind}
    (he : scan {} l = .ok s') (hset : s'.has k = true) :
    ∃ h ∈ l, classifyName h.1 = some k := by
  rcases scan_has_source he hset with hz | hw
  · cases k <;> simp [Seen.has] at hz
  · exact hw

/-! ## Headline theorem 1 — ordering (§8.3) -/

/-- **Ordering (RFC 9113 §8.3).** A request whose decoded header list places a
regular field before a pseudo-header field is malformed — for arbitrary
surrounding context. -/
theorem pseudo_before_regular
    (pre : List Header) (reg : Header) (mid : List Header)
    (ps : Header) (post : List Header)
    (hreg : isPseudoName reg.1 = false)
    (hps : isPseudoName ps.1 = true) :
    ∃ e, validateRequest (pre ++ reg :: mid ++ ps :: post) = .error e := by
  suffices hscan : ∃ e, scan {} (pre ++ reg :: mid ++ ps :: post) = .error e by
    obtain ⟨e, he⟩ := hscan
    exact ⟨e, by unfold validateRequest; rw [he]⟩
  rw [scan_append]
  cases hA : scan {} (pre ++ reg :: mid) with
  | error e => exact ⟨e, rfl⟩
  | ok sA =>
    have hr : sA.regular = true :=
      scan_regular_witness hA ⟨reg, by simp, hreg⟩
    refine ⟨.regularBeforePseudo, ?_⟩
    show scan sA (ps :: post) = .error .regularBeforePseudo
    unfold scan
    rw [stepReq_pseudo_after_regular hps hr]

/-! ## Headline theorem 2 — no duplicate pseudo-headers (§8.3) -/

/-- **No duplicates (RFC 9113 §8.3).** A recognised request pseudo-header name
appearing twice makes the request malformed, in arbitrary surrounding context.
Instantiate `name := strBytes ":method"`, `k := .method` (or `:path`, `:scheme`,
`:authority`) for the concrete rule; `mutantB_duplicate_method` witnesses it on
real bytes. -/
theorem pseudo_no_duplicate
    (name : Bytes) (k : PseudoKind)
    (hp : isPseudoName name = true) (hc : classifyName name = some k)
    (pre mid post : List Header) (v1 v2 : Bytes) :
    ∃ e, validateRequest
      (pre ++ (name, v1) :: mid ++ (name, v2) :: post) = .error e := by
  suffices hscan : ∃ e,
      scan {} (pre ++ (name, v1) :: mid ++ (name, v2) :: post) = .error e by
    obtain ⟨e, he⟩ := hscan
    exact ⟨e, by unfold validateRequest; rw [he]⟩
  rw [scan_append]
  cases hA : scan {} (pre ++ (name, v1) :: mid) with
  | error e => exact ⟨e, rfl⟩
  | ok sA =>
    have hk : sA.has k = true :=
      scan_has_witness hA ⟨(name, v1), by simp, hp, hc⟩
    obtain ⟨e, he⟩ := stepReq_dup (s := sA) (h := (name, v2)) hp hc hk
    refine ⟨e, ?_⟩
    show scan sA ((name, v2) :: post) = .error e
    unfold scan
    rw [he]

/-! ## Headline theorem 3 — required pseudo-headers (§8.3.1) -/

/-- **Required pseudo-headers (RFC 9113 §8.3.1).** A well-formed request
necessarily contains a `:method`, a `:scheme`, and a `:path` field. -/
theorem pseudo_required (hs : List Header) (h : validateRequest hs = .ok ()) :
    (∃ e ∈ hs, classifyName e.1 = some PseudoKind.method) ∧
    (∃ e ∈ hs, classifyName e.1 = some PseudoKind.scheme) ∧
    (∃ e ∈ hs, classifyName e.1 = some PseudoKind.path) := by
  unfold validateRequest at h
  split at h
  · exact absurd h (by simp)
  · next s hscan =>
    split at h
    · next hflags =>
      simp only [Bool.and_eq_true] at hflags
      obtain ⟨⟨hm, hsc⟩, hpt⟩ := hflags
      exact ⟨scan_flag_witness hscan hm, scan_flag_witness hscan hsc,
             scan_flag_witness hscan hpt⟩
    · exact absurd h (by simp)

/-! ## Headline theorem 4 — unknown pseudo-header rejected (§8.3) -/

/-- **Unknown pseudo-header (RFC 9113 §8.3).** A field whose name begins with
`:` but is not a defined request pseudo-header makes the request malformed, in
arbitrary surrounding context (e.g. `:status`, a response-only pseudo-header).
`mutantD_unknown_status` witnesses it on real bytes. -/
theorem pseudo_unknown_rejected
    (pre post : List Header) (name val : Bytes)
    (hp : isPseudoName name = true) (hunk : classifyName name = none) :
    ∃ e, validateRequest (pre ++ (name, val) :: post) = .error e := by
  suffices hscan : ∃ e, scan {} (pre ++ (name, val) :: post) = .error e by
    obtain ⟨e, he⟩ := hscan
    exact ⟨e, by unfold validateRequest; rw [he]⟩
  rw [scan_append]
  cases hA : scan {} pre with
  | error e => exact ⟨e, rfl⟩
  | ok s0 =>
    obtain ⟨e, he⟩ := stepReq_unknown (s := s0) (h := (name, val)) hp hunk
    refine ⟨e, ?_⟩
    show scan s0 ((name, val) :: post) = .error e
    unfold scan
    rw [he]

/-! ## Non-vacuity — a well-formed request and mutants (real bytes)

These witnesses evaluate `validateRequest` on real UTF-8 byte strings. They are
discharged in the pure kernel: the `Proto.Kernel.Shortcuts.toUTF8_toList_ascii` bridge
turns each `strBytes` literal into a structural `List.map` over the string's chars, and
the resulting closed computation is settled by `simp (decide := true)`. They stay
illustrative rather than part of the verified contract — the load-bearing content is the
four *general* headline theorems above, proven by induction over arbitrary context. -/

/-- Decidable equality on validator results, so the concrete witnesses below can
be settled by evaluation. -/
instance : DecidableEq (Except Malformed Unit)
  | .ok _, .ok _ => isTrue rfl
  | .error a, .error b =>
      match decEq a b with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro he; cases he; exact h rfl)
  | .ok _, .error _ => isFalse (by intro he; cases he)
  | .error _, .ok _ => isFalse (by intro he; cases he)

/-- A concrete well-formed HTTP/2 GET request: the three required pseudo-headers
in order, then a regular field. The validator accepts it — so the
malformed-verdict theorems above are not vacuously about an always-rejecting
function. -/
def goodRequest : List Header :=
  [ (strBytes ":method", strBytes "GET"),
    (strBytes ":scheme", strBytes "https"),
    (strBytes ":path", strBytes "/"),
    (strBytes "user-agent", strBytes "drorb") ]

theorem goodRequest_ok : validateRequest goodRequest = .ok () := by
  simp (config := { decide := true }) only
    [goodRequest, validateRequest, strBytes, scan, stepReq, H2.Hpack.classifyName,
     Proto.Kernel.Shortcuts.toUTF8_toList_ascii]

/-- Mutant A — a regular field before the pseudo-headers is rejected (ordering). -/
theorem mutantA_regular_first :
    validateRequest
      [ (strBytes "user-agent", strBytes "drorb"),
        (strBytes ":method", strBytes "GET"),
        (strBytes ":scheme", strBytes "https"),
        (strBytes ":path", strBytes "/") ]
      = .error .regularBeforePseudo := by
  simp (config := { decide := true }) only
    [goodRequest, validateRequest, strBytes, scan, stepReq, H2.Hpack.classifyName,
     Proto.Kernel.Shortcuts.toUTF8_toList_ascii]

/-- Mutant B — a duplicate `:method` is rejected (no duplicates). -/
theorem mutantB_duplicate_method :
    validateRequest
      [ (strBytes ":method", strBytes "GET"),
        (strBytes ":method", strBytes "POST"),
        (strBytes ":scheme", strBytes "https"),
        (strBytes ":path", strBytes "/") ]
      = .error .duplicatePseudo := by
  simp (config := { decide := true }) only
    [goodRequest, validateRequest, strBytes, scan, stepReq, H2.Hpack.classifyName,
     Proto.Kernel.Shortcuts.toUTF8_toList_ascii]

/-- Mutant C — dropping `:scheme` is rejected (required set). -/
theorem mutantC_missing_scheme :
    validateRequest
      [ (strBytes ":method", strBytes "GET"),
        (strBytes ":path", strBytes "/") ]
      = .error .missingRequired := by
  simp (config := { decide := true }) only
    [goodRequest, validateRequest, strBytes, scan, stepReq, H2.Hpack.classifyName,
     Proto.Kernel.Shortcuts.toUTF8_toList_ascii]

/-- Mutant D — a `:status` field (a response-only, hence unknown request
pseudo-header) is rejected. -/
theorem mutantD_unknown_status :
    validateRequest
      [ (strBytes ":status", strBytes "200"),
        (strBytes ":method", strBytes "GET"),
        (strBytes ":scheme", strBytes "https"),
        (strBytes ":path", strBytes "/") ]
      = .error .unknownPseudo := by
  simp (config := { decide := true }) only
    [goodRequest, validateRequest, strBytes, scan, stepReq, H2.Hpack.classifyName,
     Proto.Kernel.Shortcuts.toUTF8_toList_ascii]

end PseudoHeader
end H2
