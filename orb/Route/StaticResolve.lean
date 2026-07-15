/-
Route.StaticResolve — the DEPLOYED static-file path decision, in the core.

The host's static lane used to make the traversal decision itself (split the
target, percent-decode each segment once, walk dot-segments, gate on UTF-8),
while the core carried only a *model* of that decision (`Route.Path` /
`Safety.Traversal`). This module moves the decision across the boundary: the
exported `drorb_static_resolve` below IS the resolver the running host calls
per static request — relative-target bytes in, the resolved relative path (or
a reject verdict) out. What runs is what is proven.

The pipeline, over the raw target bytes (the path portion after the configured
serving prefix; the query was already dropped by the request-line split):

  1. split on `/`, dropping empty raw segments;
  2. percent-decode each segment EXACTLY once: `%XX` with two hex digits is the
     decoded byte; a malformed escape emits the `%` literally and RE-EXAMINES
     the next byte. NOTE this is the deployed byte semantics, and it differs
     from the older string model `Route.Path.decodeChars` on malformed escapes
     (the model skips all three bytes; the deployed resolver advances one).
     This file proves the deployed semantics — the drift between model and
     host is exactly what moving the decision into the core retires;
  3. reject unless every decoded segment is well-formed UTF-8 (RFC 3629:
     no overlongs, no surrogates, nothing above U+10FFFF — the same set the
     host's string validation accepted);
  4. dot-segment walk: `.` is dropped, `..` pops one output segment and is
     clamped at the (empty) relative root — you cannot climb above the root.

Theorems (all over arbitrary input bytes):
  * `resolveRel_no_dot`    — no resolved segment is `.` or `..`.
  * `resolveRel_no_empty`  — no resolved segment is empty.
  * `resolveRel_confined`  — joining the resolved segments under a clean root
                             and interpreting the result with a filesystem
                             walker that ACTUALLY POPS on `..` still keeps the
                             root as a prefix: no input escapes.
  * `decode_once_only`     — `%252e` decodes to the literal `%2e`, not `.`
                             (single-decode boundary; a double decode is the
                             classic traversal hole).
  * `staticResolveC_accept` / `staticResolveC_reject` — the exported seam
                             function returns exactly `0x01 ++ join(segs)` or
                             `0x00`, per `resolveRel`'s verdict.

Residual (host-side, named): the request-line split, the serving-prefix strip,
and the filesystem canonicalize + root-prefix re-check (symlinks, existence)
remain in the host. A decoded segment may contain a literal `/` (from `%2f`);
the walk treats it as one opaque segment — confinement for components it
re-introduces at the filesystem layer rests on the host's canonicalize
re-check, exactly as before this change.
-/

namespace Route.StaticResolve

/-- One path segment, as raw bytes. -/
abbrev Seg := List UInt8

/-- `"."` as bytes. -/
def dotSeg : Seg := [0x2e]

/-- `".."` as bytes. -/
def dotdotSeg : Seg := [0x2e, 0x2e]

/-- A dot-segment: `.` or `..`. -/
def IsDotSeg (s : Seg) : Prop := s = dotSeg ∨ s = dotdotSeg

instance : DecidablePred IsDotSeg := fun s => by
  unfold IsDotSeg; exact inferInstance

/-! ## Percent-decode, exactly once (the boundary transform) -/

/-- Hex-digit value of an ASCII byte (`0-9`, `a-f`, `A-F`), or `none`. -/
def hexVal (b : UInt8) : Option UInt8 :=
  if 0x30 ≤ b ∧ b ≤ 0x39 then some (b - 0x30)
  else if 0x61 ≤ b ∧ b ≤ 0x66 then some (b - 0x61 + 10)
  else if 0x41 ≤ b ∧ b ≤ 0x46 then some (b - 0x41 + 10)
  else none

/-- The decode step, fuel-indexed so the recursion is structural (on the fuel)
and the kernel can evaluate it. Each step consumes one fuel and AT LEAST one
input byte, so with `fuel = input.length` the fuel never runs out — see
`decodeAux_fuel_free`. A valid `%XX` consumes three bytes and emits the decoded
one; a malformed escape emits the `%` literally and continues with the NEXT
byte (the deployed semantics — the following byte may itself begin a valid
escape). -/
def decodeAux : Nat → List UInt8 → List UInt8
  | _, [] => []
  | 0, l => l
  | n + 1, b :: rest =>
    if b = 0x25 then
      match rest with
      | h :: l :: rest' =>
        match hexVal h, hexVal l with
        | some hi, some lo => (hi * 16 + lo) :: decodeAux n rest'
        | _, _ => b :: decodeAux n rest
      | _ => b :: decodeAux n rest
    else
      b :: decodeAux n rest

/-- Percent-decode a byte stream once. `%XX` with two hex digits becomes the
decoded byte; a malformed escape emits the `%` literally and continues with the
next byte. Single-pass by construction: the output is never re-scanned, so an
encoded `%252e` decodes to the literal `%2e`, not to `.`. -/
def decodeOnce (l : List UInt8) : List UInt8 := decodeAux l.length l

/-- The fuel is enough: with any fuel of at least the input length the decode
is fuel-independent (each step consumes at least one input byte), so
`decodeOnce`'s `fuel = length` seed never hits the fuel-exhaustion branch. -/
theorem decodeAux_fuel_free :
    ∀ (n m : Nat) (l : List UInt8), l.length ≤ n → l.length ≤ m →
      decodeAux n l = decodeAux m l
  | _, _, [], _, _ => by simp [decodeAux]
  | 0, _, b :: rest, hn, _ => by simp at hn
  | _, 0, b :: rest, _, hm => by simp at hm
  | n + 1, m + 1, b :: rest, hn, hm => by
    have hn' : rest.length ≤ n := Nat.le_of_succ_le_succ hn
    have hm' : rest.length ≤ m := Nat.le_of_succ_le_succ hm
    unfold decodeAux
    match rest, hn', hm' with
    | [], _, _ => simp [decodeAux]
    | [x], hn', hm' => simp only [decodeAux_fuel_free n m [x] hn' hm']
    | h :: l :: rest', hn', hm' =>
      have hr : rest'.length ≤ n := by
        have := hn'; simp only [List.length_cons] at this; omega
      have hr' : rest'.length ≤ m := by
        have := hm'; simp only [List.length_cons] at this; omega
      cases hexVal h <;> cases hexVal l <;>
        simp only [decodeAux_fuel_free n m rest' hr hr',
                   decodeAux_fuel_free n m (h :: l :: rest') hn' hm']

/-- Decoding a nonempty segment yields a nonempty segment (every branch of the
decode on a cons emits at least one byte). -/
theorem decodeOnce_ne_nil : ∀ {l : List UInt8}, l ≠ [] → decodeOnce l ≠ []
  | [], h => absurd rfl h
  | b :: rest, _ => by
    show decodeAux (rest.length + 1) (b :: rest) ≠ []
    unfold decodeAux
    repeat' split
    all_goals exact List.cons_ne_nil _ _

/-! ## UTF-8 well-formedness (RFC 3629) — the segment gate -/

/-- A UTF-8 continuation byte: `0x80–0xBF`. -/
def isCont (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xbf

/-- RFC 3629 well-formedness: rejects overlong encodings, surrogates
(`U+D800–U+DFFF`), and anything above `U+10FFFF` — the exact byte-sequence set
the host's string validation accepted. -/
def validUtf8 : List UInt8 → Bool
  | [] => true
  | b :: rest =>
    if b ≤ 0x7f then validUtf8 rest
    else if 0xc2 ≤ b && b ≤ 0xdf then
      match rest with
      | c1 :: rest' => isCont c1 && validUtf8 rest'
      | [] => false
    else if b = 0xe0 then
      match rest with
      | c1 :: c2 :: rest' => (0xa0 ≤ c1 && c1 ≤ 0xbf) && isCont c2 && validUtf8 rest'
      | _ => false
    else if (0xe1 ≤ b && b ≤ 0xec) || b = 0xee || b = 0xef then
      match rest with
      | c1 :: c2 :: rest' => isCont c1 && isCont c2 && validUtf8 rest'
      | _ => false
    else if b = 0xed then
      match rest with
      | c1 :: c2 :: rest' => (0x80 ≤ c1 && c1 ≤ 0x9f) && isCont c2 && validUtf8 rest'
      | _ => false
    else if b = 0xf0 then
      match rest with
      | c1 :: c2 :: c3 :: rest' =>
        (0x90 ≤ c1 && c1 ≤ 0xbf) && isCont c2 && isCont c3 && validUtf8 rest'
      | _ => false
    else if 0xf1 ≤ b && b ≤ 0xf3 then
      match rest with
      | c1 :: c2 :: c3 :: rest' => isCont c1 && isCont c2 && isCont c3 && validUtf8 rest'
      | _ => false
    else if b = 0xf4 then
      match rest with
      | c1 :: c2 :: c3 :: rest' =>
        (0x80 ≤ c1 && c1 ≤ 0x8f) && isCont c2 && isCont c3 && validUtf8 rest'
      | _ => false
    else false

/-! ## Split on `/` -/

/-- Split a byte list on `/` — the segments between separators, empties
included (they are filtered by the caller, matching the host's skip of empty
raw segments). -/
def splitSlash : List UInt8 → List Seg
  | [] => [[]]
  | b :: rest =>
    if b = 0x2f then [] :: splitSlash rest
    else
      match splitSlash rest with
      | s :: ss => (b :: s) :: ss
      | [] => [[b]]

/-! ## The dot-segment walk (clamped at the relative root) -/

/-- The output-stack walk over decoded segments. `acc` holds the output in
REVERSE order. `.` is dropped; `..` pops one output segment or is dropped at
the root (the clamp); anything else is pushed. -/
def walk : List Seg → List Seg → List Seg
  | acc, [] => acc.reverse
  | acc, s :: rest =>
    if s = dotSeg then walk acc rest
    else if s = dotdotSeg then
      (match acc with
       | [] => walk [] rest
       | _ :: acc' => walk acc' rest)
    else walk (s :: acc) rest

/-- Every segment `walk` outputs is a non-dot segment, provided the seed
accumulator holds only non-dot segments. -/
theorem walk_noDot {acc segs : List Seg}
    (hacc : ∀ s ∈ acc, ¬ IsDotSeg s) :
    ∀ s ∈ walk acc segs, ¬ IsDotSeg s := by
  induction segs generalizing acc with
  | nil =>
    intro s hs
    simp only [walk, List.mem_reverse] at hs
    exact hacc s hs
  | cons a rest ih =>
    intro s hs
    unfold walk at hs
    by_cases h1 : a = dotSeg
    · rw [if_pos h1] at hs; exact ih hacc s hs
    · rw [if_neg h1] at hs
      by_cases h2 : a = dotdotSeg
      · rw [if_pos h2] at hs
        cases acc with
        | nil => exact ih (by intro x hx; cases hx) s hs
        | cons b acc' =>
          apply ih _ s hs
          intro x hx
          exact hacc x (List.mem_cons_of_mem _ hx)
      · rw [if_neg h2] at hs
        apply ih _ s hs
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · subst hx; intro hdot; rcases hdot with hd | hd
          · exact h1 hd
          · exact h2 hd
        · exact hacc x hx

/-- Every segment `walk` outputs is nonempty, provided the seed accumulator and
the input segments are nonempty (`walk` only ever pushes input segments). -/
theorem walk_ne_nil {acc segs : List Seg}
    (hacc : ∀ s ∈ acc, s ≠ ([] : Seg)) (hsegs : ∀ s ∈ segs, s ≠ ([] : Seg)) :
    ∀ s ∈ walk acc segs, s ≠ ([] : Seg) := by
  induction segs generalizing acc with
  | nil =>
    intro s hs
    simp only [walk, List.mem_reverse] at hs
    exact hacc s hs
  | cons a rest ih =>
    intro s hs
    have hrest : ∀ s ∈ rest, s ≠ ([] : Seg) :=
      fun x hx => hsegs x (List.mem_cons_of_mem _ hx)
    unfold walk at hs
    by_cases h1 : a = dotSeg
    · rw [if_pos h1] at hs; exact ih hacc hrest s hs
    · rw [if_neg h1] at hs
      by_cases h2 : a = dotdotSeg
      · rw [if_pos h2] at hs
        cases acc with
        | nil => exact ih (by intro x hx; cases hx) hrest s hs
        | cons b acc' =>
          exact ih (fun x hx => hacc x (List.mem_cons_of_mem _ hx)) hrest s hs
      · rw [if_neg h2] at hs
        refine ih ?_ hrest s hs
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · subst hx; exact hsegs x (List.mem_cons_self x rest)
        · exact hacc x hx

/-! ## The resolver (the decision the host used to make) -/

/-- The decoded nonempty segments of a relative target: split on `/`, drop
empty raw segments, percent-decode each once. -/
def decodedSegs (rel : List UInt8) : List Seg :=
  ((splitSlash rel).filter (· ≠ ([] : Seg))).map decodeOnce

/-- **The static-path resolution decision.** `some segs` — serve the file at
`root/segs` (after the host's canonicalize re-check); `none` — reject (a
decoded segment was not well-formed UTF-8), the host answers `404`. -/
def resolveRel (rel : List UInt8) : Option (List Seg) :=
  if (decodedSegs rel).all (fun s => validUtf8 s) then
    some (walk [] (decodedSegs rel))
  else
    none

/-- Every decoded segment is nonempty (empty raw segments were filtered, and
`decodeOnce` preserves nonemptiness). -/
theorem decodedSegs_ne_nil (rel : List UInt8) :
    ∀ s ∈ decodedSegs rel, s ≠ ([] : Seg) := by
  intro s hs
  unfold decodedSegs at hs
  rcases List.mem_map.mp hs with ⟨raw, hraw, rfl⟩
  have hne : raw ≠ ([] : Seg) := by
    have := (List.mem_filter.mp hraw).2
    exact of_decide_eq_true this
  exact decodeOnce_ne_nil hne

/-- **No resolved segment is `..` or `.`** — the walk removed every
dot-segment, for every input. -/
theorem resolveRel_no_dot {rel : List UInt8} {segs : List Seg}
    (h : resolveRel rel = some segs) :
    ∀ s ∈ segs, s ≠ dotdotSeg ∧ s ≠ dotSeg := by
  unfold resolveRel at h
  split at h
  · injection h with h
    subst h
    intro s hs
    have hnd := walk_noDot (acc := []) (by intro x hx; cases hx) s hs
    exact ⟨fun hd => hnd (Or.inr hd), fun hd => hnd (Or.inl hd)⟩
  · cases h

/-- **No resolved segment is empty.** -/
theorem resolveRel_no_empty {rel : List UInt8} {segs : List Seg}
    (h : resolveRel rel = some segs) :
    ∀ s ∈ segs, s ≠ ([] : Seg) := by
  unfold resolveRel at h
  split at h
  · injection h with h
    subst h
    exact walk_ne_nil (by intro x hx; cases hx) (decodedSegs_ne_nil rel)
  · cases h

/-! ## Confinement under a popping filesystem walker -/

/-- Filesystem-style descent that ACTUALLY POPS on `..` (unclamped) — the
interpreter a traversal attack targets. -/
def descendPop : List Seg → List Seg → List Seg
  | base, [] => base
  | base, s :: rest =>
    if s = dotdotSeg then descendPop base.dropLast rest
    else if s = dotSeg then descendPop base rest
    else descendPop (base ++ [s]) rest

/-- On a dot-free list, `descendPop` never pops: it just appends. -/
theorem descendPop_noDot {base segs : List Seg}
    (h : ∀ s ∈ segs, ¬ IsDotSeg s) :
    descendPop base segs = base ++ segs := by
  induction segs generalizing base with
  | nil => simp [descendPop]
  | cons a rest ih =>
    have ha : ¬ IsDotSeg a := h a (List.mem_cons_self a rest)
    have h1 : a ≠ dotdotSeg := fun hd => ha (Or.inr hd)
    have h2 : a ≠ dotSeg := fun hd => ha (Or.inl hd)
    have hrest : ∀ s ∈ rest, ¬ IsDotSeg s := fun s hs => h s (List.mem_cons_of_mem _ hs)
    unfold descendPop
    rw [if_neg h1, if_neg h2, ih hrest]
    simp

/-- **Traversal confinement.** For every accepted input, joining the resolved
segments under a clean document root (a real directory path has no
dot-segments) and interpreting the result with the `..`-popping walker still
keeps the root as a prefix: no request escapes the root through this decision.
The attacker's literal or encoded `..` was consumed by the clamped walk; a
double-encoded one survives only as the harmless literal `%2e%2e`. -/
theorem resolveRel_confined {rel : List UInt8} {segs root : List Seg}
    (h : resolveRel rel = some segs) (hroot : ∀ s ∈ root, ¬ IsDotSeg s) :
    root <+: descendPop [] (root ++ segs) := by
  have hno : ∀ s ∈ root ++ segs, ¬ IsDotSeg s := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hroot s hs
    · intro hd
      rcases resolveRel_no_dot h s hs with ⟨h2, h1⟩
      rcases hd with hd | hd
      · exact h1 hd
      · exact h2 hd
  rw [descendPop_noDot hno, List.nil_append]
  exact List.prefix_append root segs

/-! ## Single-decode witnesses (why decode is a once-only boundary) -/

/-- `%2e%2e` decodes once to `..` — which the walk then consumes. -/
theorem decode_encoded_dotdot :
    decodeOnce [0x25, 0x32, 0x65, 0x25, 0x32, 0x65] = dotdotSeg := by decide

/-- **`%252e` decodes ONCE to the literal `%2e`** — NOT to `.`. A resolver that
decoded its own output a second time would collapse it to a dot-segment after
the walk; this one cannot. -/
theorem decode_once_only :
    decodeOnce [0x25, 0x32, 0x35, 0x32, 0x65] = [0x25, 0x32, 0x65] := by decide

/-- Deployed malformed-escape semantics: after a literal `%`, the NEXT byte is
re-examined and may begin a valid escape (`%%34 1` → `%`, then `%34` → `4`,
then `1`). The older string model skipped all three bytes here — that drift is
retired by this module being the deployed decision. -/
theorem decode_malformed_reexamines :
    decodeOnce [0x25, 0x25, 0x33, 0x34, 0x31] = [0x25, 0x34, 0x31] := by decide

/-! ## Concrete adversarial witnesses through the whole resolver -/

/-- `../../etc/passwd` is clamped: both pops fire at the empty root and vanish;
the resolution is `etc/passwd` UNDER the root, never `/etc/passwd`. -/
theorem resolve_dotdot_clamped :
    resolveRel [0x2e, 0x2e, 0x2f, 0x2e, 0x2e, 0x2f, 0x65, 0x74, 0x63, 0x2f,
                0x70, 0x61, 0x73, 0x73, 0x77, 0x64]
      = some [[0x65, 0x74, 0x63], [0x70, 0x61, 0x73, 0x73, 0x77, 0x64]] := by decide

/-- `%2e%2e/%2e%2e/etc/passwd` — encoded dot-dots decode once to `..` and are
clamped identically. -/
theorem resolve_encoded_dotdot_clamped :
    resolveRel [0x25, 0x32, 0x65, 0x25, 0x32, 0x65, 0x2f,
                0x25, 0x32, 0x65, 0x25, 0x32, 0x65, 0x2f,
                0x65, 0x74, 0x63, 0x2f, 0x70, 0x61, 0x73, 0x73, 0x77, 0x64]
      = some [[0x65, 0x74, 0x63], [0x70, 0x61, 0x73, 0x73, 0x77, 0x64]] := by decide

/-- `%252e%252e/etc/passwd` — the double-encoded dot-dot survives only as the
harmless literal `%2e%2e` (an ordinary filename component): it names a file
strictly under the root and never collapses to `..`. -/
theorem resolve_double_encoded_literal :
    resolveRel [0x25, 0x32, 0x35, 0x32, 0x65, 0x25, 0x32, 0x35, 0x32, 0x65,
                0x2f, 0x65, 0x74, 0x63]
      = some [[0x25, 0x32, 0x65, 0x25, 0x32, 0x65], [0x65, 0x74, 0x63]] := by decide

/-- An escape decoding to an invalid UTF-8 byte (`%ff`) rejects the whole
target — the host answers `404`, never touching the filesystem. -/
theorem resolve_invalid_utf8_rejected :
    resolveRel [0x61, 0x2f, 0x25, 0x66, 0x66] = none := by decide

/-- UTF-8 gate witnesses: a well-formed 2-byte sequence passes; an overlong
encoding, a surrogate, and a plane beyond U+10FFFF are rejected. -/
theorem utf8_gate_witnesses :
    validUtf8 [0xc3, 0xa9] = true          -- é
    ∧ validUtf8 [0xc0, 0xaf] = false        -- overlong '/'
    ∧ validUtf8 [0xed, 0xa0, 0x80] = false  -- surrogate U+D800
    ∧ validUtf8 [0xf4, 0x90, 0x80, 0x80] = false := by decide  -- > U+10FFFF

/-! ## The exported seam -/

/-- Join resolved segments with `/` — the host appends the result under its
document root in one step (equal, at the filesystem, to pushing the segments
one by one). -/
def joinSlash : List Seg → List UInt8
  | [] => []
  | [s] => s
  | s :: rest => s ++ 0x2f :: joinSlash rest

/-- **`drorb_static_resolve` — the static-path decision as `ByteArray →
ByteArray`.** Input: the relative target bytes (after the serving prefix).
Output: `0x01 ++ joinSlash segs` when the resolution accepts (`segs` may be
empty — the root itself), or the single byte `0x00` when it rejects (the host
then serves its `404`). -/
@[export drorb_static_resolve]
def staticResolveC (input : ByteArray) : ByteArray :=
  match resolveRel input.toList with
  | none => ⟨#[0x00]⟩
  | some segs => ⟨(0x01 :: joinSlash segs).toArray⟩

/-- The seam returns exactly the accept verdict wired to `resolveRel`. -/
theorem staticResolveC_accept {input : ByteArray} {segs : List Seg}
    (h : resolveRel input.toList = some segs) :
    staticResolveC input = ⟨(0x01 :: joinSlash segs).toArray⟩ := by
  unfold staticResolveC; rw [h]

/-- The seam returns exactly the reject verdict wired to `resolveRel`. -/
theorem staticResolveC_reject {input : ByteArray}
    (h : resolveRel input.toList = none) :
    staticResolveC input = ⟨#[0x00]⟩ := by
  unfold staticResolveC; rw [h]

end Route.StaticResolve

#print axioms Route.StaticResolve.resolveRel_no_dot
#print axioms Route.StaticResolve.resolveRel_no_empty
#print axioms Route.StaticResolve.resolveRel_confined
#print axioms Route.StaticResolve.decode_once_only
#print axioms Route.StaticResolve.resolve_double_encoded_literal
#print axioms Route.StaticResolve.resolve_invalid_utf8_rejected
#print axioms Route.StaticResolve.staticResolveC_accept
#print axioms Route.StaticResolve.staticResolveC_reject
