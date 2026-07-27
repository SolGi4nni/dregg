import Proto.ResponseParse

/-!
# Content-Length body framing — proven exact, and no over-read

The deployed HTTP/1.1 dataplane frames a response body with a `Content-Length: N`
header and exactly `N` body bytes; the host reads that length to know where one
message ends and the next begins (`crates/dataplane/src/http.rs`, `body_frame`
→ `Fixed(n)`, `total = head_end + n`). This module proves the format the
serializer emits and the decoder that reads it are exact and self-delimiting.

The serializer `Reactor.serialize` (see `Reactor.Serialize`) emits, by
construction, `Content-Length: body.length` (the value is derived from the body,
never a caller input). This module adds the *reading* half a length-framed host
needs: a Content-Length-driven body decoder `decode`, the faithful model of the
Rust `next_request` framing — parse the head, read the `Content-Length` value,
take **exactly** that many body bytes, and leave the remainder (a pipelined next
message) untouched.

## What is proven

* `content_length_frames_exact` — a body of `N` bytes serialized and then decoded
  recovers exactly that body: for every well-formed response with no caller
  `Content-Length` header, and *any* trailing bytes `rest`,

      decode (serialize resp ++ rest) = some (wireForm resp, rest)

  The recovered `body` equals `resp.body` (via `wireForm`), the header carries
  `Content-Length: resp.body.length`, and the trailing `rest` is returned
  verbatim — the decoder consumed exactly the head plus `N` body bytes.
  `content_length_frames_exact_ok200` discharges the hypotheses on a concrete
  `200 OK`, witnessing non-vacuity.

* `content_length_no_overread` — whenever `decode` succeeds it read exactly the
  declared `Content-Length` and no further: the recovered body has length equal
  to the `Content-Length` header value, and the post-head bytes decompose as
  `body ++ rest` with `rest` (the next message) preserved byte-for-byte. The
  decoder never reads past `Content-Length`.

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`.
-/

namespace Proto
namespace ContentLength

open Reactor (Response Wire build serialize serializeWire statusLine renderHeaders
  allHeaders crlf http11 clName natToDec ok200)
open Proto.ResponseParse (SP CR LF COLON stripPrefix takeUntil takeUntilCrlf
  parseHeaders parseHeadersFuel blockOf wireForm WF
  stripPrefix_append takeUntil_append takeUntilCrlf_append renderHeaders_blockOf
  parseHeadersFuel_blockOf SP_notMem_natToDec CR_notMem_clName COLON_notMem_clName
  CR_notMem_natToDec ok200_WF)

abbrev Bytes := List UInt8

/-! ## The exact-count body reader

`takeBody n bs` reads exactly `n` bytes off the front of `bs`, returning those
`n` bytes and the untouched remainder; `none` if fewer than `n` bytes are
available. This is the Content-Length body rule: read exactly the declared
count, never more. -/
def takeBody : Nat → Bytes → Option (Bytes × Bytes)
  | 0,     bs      => some ([], bs)
  | _ + 1, []      => none
  | n + 1, b :: bs => (takeBody n bs).map (fun p => (b :: p.1, p.2))

/-- Reading `body.length` bytes off `body ++ rest` returns exactly `(body, rest)`. -/
theorem takeBody_append (body rest : Bytes) :
    takeBody body.length (body ++ rest) = some (body, rest) := by
  induction body with
  | nil => rfl
  | cons b t ih =>
    show takeBody (t.length + 1) (b :: (t ++ rest)) = some (b :: t, rest)
    simp only [takeBody, ih, Option.map_some]

/-- **Exact count.** A successful `takeBody n` returns exactly `n` bytes. -/
theorem takeBody_length : ∀ (n : Nat) (bs body rest : Bytes),
    takeBody n bs = some (body, rest) → body.length = n
  | 0, bs, body, rest, h => by
    simp only [takeBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, _⟩ := h; subst hb; rfl
  | n + 1, [], _, _, h => by simp [takeBody] at h
  | n + 1, b :: bs, body, rest, h => by
    simp only [takeBody, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨p, hp, hbody, hrest⟩ := h
    subst hbody
    have := takeBody_length n bs p.1 p.2 (by rw [hp])
    simp only [List.length_cons, this]

/-- **No over-read.** A successful `takeBody n bs` consumes a prefix and leaves
the rest untouched: `bs = body ++ rest`. Nothing beyond the `n`-th byte is read. -/
theorem takeBody_recon : ∀ (n : Nat) (bs body rest : Bytes),
    takeBody n bs = some (body, rest) → bs = body ++ rest
  | 0, bs, body, rest, h => by
    simp only [takeBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hr⟩ := h; subst hb; subst hr; rfl
  | n + 1, [], _, _, h => by simp [takeBody] at h
  | n + 1, b :: bs, body, rest, h => by
    simp only [takeBody, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨p, hp, hbody, hrest⟩ := h
    subst hbody; subst hrest
    have := takeBody_recon n bs p.1 p.2 (by rw [hp])
    rw [List.cons_append, ← this]

/-! ## Reading the Content-Length header value -/

/-- The `Content-Length` value declared by a header block: the decimal value of
the first `Content-Length` header, or `none` if absent. -/
def clValue (headers : List (Bytes × Bytes)) : Option Nat :=
  (headers.find? (fun kv => kv.1 == clName)).map (fun kv => Dec.dval 0 kv.2)

/-- `find?` over `l ++ [x]` when no element of `l` matches and `x` does: it is
`some x`. -/
theorem find?_append_singleton {α} (p : α → Bool) (l : List α) (x : α)
    (hl : ∀ a ∈ l, p a = false) (hx : p x = true) :
    (l ++ [x]).find? p = some x := by
  induction l with
  | nil => simp [List.find?, hx]
  | cons a t ih =>
    have ha : p a = false := hl a (by simp)
    have ht : ∀ b ∈ t, p b = false := fun b hb => hl b (by simp [hb])
    simp only [List.cons_append, List.find?_cons, ha, Bool.false_eq_true, if_false]
    exact ih ht

/-- The serializer's derived `Content-Length` header reads back exactly
`body.length`, provided the caller supplied no `Content-Length` header of its
own (so the derived one is the first match). -/
theorem clValue_allHeaders (resp : Response)
    (hnc : clName ∉ resp.headers.map Prod.fst) :
    clValue (allHeaders (build resp)) = some resp.body.length := by
  have hl : ∀ kv ∈ resp.headers, (fun kv => kv.1 == clName) kv = false := by
    intro kv hkv
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro heq
    exact hnc (by rw [← heq]; exact List.mem_map_of_mem hkv)
  have hx : (fun kv => kv.1 == clName) (clName, natToDec resp.body.length) = true := by
    simp
  simp only [clValue, allHeaders, build,
    find?_append_singleton _ resp.headers (clName, natToDec resp.body.length) hl hx,
    Option.map_some]
  exact congrArg some (Dec.dval_natToDec _)

/-! ## The Content-Length-driven decoder

The reading dual of `serialize`: parse the head (status line, header block),
read the `Content-Length` value, take **exactly** that many body bytes, and
return the decoded response together with the untouched remainder — the faithful
model of the deployed `next_request` framing. -/
def decode (bs : Bytes) : Option (Response × Bytes) :=
  match stripPrefix (http11 ++ [SP]) bs with
  | none => none
  | some bs =>
    match takeUntil SP bs with
    | none => none
    | some (statusTok, bs) =>
      match takeUntilCrlf bs with
      | none => none
      | some (reason, bs) =>
        match parseHeaders bs with
        | none => none
        | some (headers, afterHead) =>
          match clValue headers with
          | none => none
          | some n =>
            match takeBody n afterHead with
            | none => none
            | some (body, rest) =>
              some ({ status := Dec.dval 0 statusTok, reason := reason,
                      headers := headers, body := body }, rest)

/-! ## Exactness -/

/-- **Content-Length frames exactly.** A response serialized and then decoded
recovers its body exactly, framed by `Content-Length: body.length`, with any
trailing bytes returned untouched. -/
theorem content_length_frames_exact (resp : Response) (rest : Bytes)
    (hwf : WF resp) (hnc : clName ∉ resp.headers.map Prod.fst) :
    decode (serialize resp ++ rest) = some (wireForm resp, rest) := by
  obtain ⟨hreason, hhdrs⟩ := hwf
  have hAHne : allHeaders (build resp) ≠ [] := by simp [allHeaders]
  have hAHwf : ∀ kv ∈ allHeaders (build resp), COLON ∉ kv.1 ∧ CR ∉ kv.1 ∧ CR ∉ kv.2 := by
    intro kv hkv
    rw [allHeaders] at hkv
    rcases List.mem_append.mp hkv with h1 | h1
    · exact hhdrs kv h1
    · simp only [List.mem_singleton] at h1
      subst h1
      exact ⟨COLON_notMem_clName, CR_notMem_clName, CR_notMem_natToDec _⟩
  have hser : serialize resp ++ rest
      = (http11 ++ [SP]) ++ (natToDec resp.status ++ SP ::
          (resp.reason ++ crlf ++
            (renderHeaders (allHeaders (build resp)) ++ crlf ++ crlf ++ (resp.body ++ rest)))) := by
    simp only [serialize, serializeWire, statusLine, build, SP, List.append_assoc,
      List.cons_append, List.singleton_append, List.nil_append]
  have hblock : renderHeaders (allHeaders (build resp)) ++ crlf ++ crlf ++ (resp.body ++ rest)
      = blockOf (allHeaders (build resp)) ++ crlf ++ (resp.body ++ rest) := by
    rw [renderHeaders_blockOf (allHeaders (build resp)) hAHne]
  rw [decode, hser]
  simp only [stripPrefix_append,
    takeUntil_append SP (natToDec resp.status) _ (SP_notMem_natToDec _),
    takeUntilCrlf_append resp.reason _ hreason]
  rw [hblock]
  simp only [parseHeaders,
    parseHeadersFuel_blockOf (allHeaders (build resp)) (resp.body ++ rest) _ hAHwf (Nat.le_refl _),
    clValue_allHeaders resp hnc, takeBody_append resp.body rest]
  rw [show Dec.dval 0 (natToDec resp.status) = resp.status from Dec.dval_natToDec resp.status]
  simp only [wireForm, allHeaders, build]

/-- Non-vacuity: the hypotheses hold for a concrete `200 OK` with any body and
any trailing bytes. -/
theorem content_length_frames_exact_ok200 (body rest : Bytes) :
    decode (serialize (ok200 body) ++ rest) = some (wireForm (ok200 body), rest) :=
  content_length_frames_exact (ok200 body) rest (ok200_WF body) (by simp [ok200])

/-! ## No over-read -/

/-- **The decoder never reads past `Content-Length`.** Whenever `decode` succeeds
returning `(r, rest)`, the recovered body has length equal to the declared
`Content-Length` value, and the bytes after the head decompose as `r.body ++ rest`
— so exactly `Content-Length` body bytes were consumed and `rest` (the next
message on the wire) is preserved byte-for-byte. -/
theorem content_length_no_overread (bs : Bytes) (r : Response) (rest : Bytes)
    (h : decode bs = some (r, rest)) :
    clValue r.headers = some r.body.length ∧
    ∃ afterHead, afterHead = r.body ++ rest ∧
      takeBody r.body.length afterHead = some (r.body, rest) := by
  unfold decode at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i headers afterHead _
  split at h
  · exact absurd h (by simp)
  rename_i n hcl
  split at h
  · exact absurd h (by simp)
  rename_i body rest' htb
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hr, hrest⟩ := h
  subst hrest
  -- read off the components of the recovered response
  have hbody : r.body = body := by rw [← hr]
  have hhdr : r.headers = headers := by rw [← hr]
  have hn : body.length = n := takeBody_length n afterHead body rest' htb
  refine ⟨?_, afterHead, ?_, ?_⟩
  · rw [hhdr, hcl, hbody, hn]
  · rw [hbody]; exact takeBody_recon n afterHead body rest' htb
  · rw [hbody, hn]; exact htb

end ContentLength
end Proto
