import Datapath.ServeConformantFast
import Datapath.ServeHeadIdx

/-!
# Datapath.ServeConformantFused — the single-copy post-processor PROVEN, on the deployed inner

The deployed non-metered serve is the conformance wrapper around the head-idx
inner (`conformantServe serveHeadIdx`). Its accepted-path post-processing
re-copies the whole response `ByteArray` ~4 times per request: `injectDateBA`
(tail `extract` + the appends behind it — 2 whole-body `memcpy`s) then
`scrubCorrBA` on the dated bytes (another tail `extract` + `append` — 2 more).
`Datapath.ServeConformantFast.scrubDateBA` fuses the two into ONE body attach
(a single native `copySlice`), but its byte-identity to the unfused composition
was pinned only by a `#guard` battery — the named missing rung was the
blank-scan shift lemma. This module CLOSES it:

* `blankLen_line_append` — the blank scan distributes over a `crlfFree` line +
  `CRLF`: a blank fires at the line end iff the tail begins with another `CRLF`,
  else the scan resumes in the tail;
* `blankLen_injectDate` — the shift: splicing `Date` right after the status
  line's `CRLF` moves the blank take by exactly `dateHdr.length + 2`;
* `scrubDateBA_eq` — **`scrubDateBA bs = scrubCorrBA (injectDateBA bs)` for
  EVERY input** (a head with no `CRLF` inside the blank scan takes the unfused
  composition verbatim, so that branch is definitional);
* `conformantServeFast_eq` — the fused wrapper serves the SAME bytes as the
  deployed wrapper `conformantServe`, for ANY inner serve and EVERY input;
* `serveConformantFastHeadIdx` (`@[export drorb_serve_conformant_fast_head_idx]`)
  — the fused wrapper around the DEPLOYED head-idx inner
  (`Datapath.ServeHeadIdx.serveHeadIdx`), proven byte-identical to
  `conformantServe serveHeadIdx` — which is definitionally the deployed
  non-metered `Seam::Http` default (`drorb_serve_conformant_head_idx`). Swapping
  the export changes NO served byte and removes ~3 whole-body `memcpy`s per
  accepted request.

As a corollary the measured fused probe `serveConformantFastIdx`
(`drorb_serve_conformant_fast`) is now PROVEN byte-identical to the proven
conformant-dense serve (`serveConformantFastIdx_eq_denseIdx`) — the `#guard`
battery in `ServeConformantFast` is superseded by theorems over all inputs.
-/

namespace Datapath.ServeConformantFused

open Proto (Bytes Request)
open Reactor (serialize crlf)
open Reactor.ServeConformant
open Datapath.ServeConformantFast
  (scrubDateBA acceptedFastBA conformantServeFast serveConformantFastIdx
   copySlice_tail_toList)
open Reactor.Stage.StrictValidation (strictStage)
open Reactor.Stage.FramingValidation (framingValidationStage)
open Reactor.Stage.RequestHeadLimit (headGate)

/-! ## 1. The injected header line, kernel-transparent

`deployNow` is built through `String.toUTF8`, which the kernel does not reduce;
pin it once to its explicit bytes (`with_unfolding_all` closes the defeq), so the
line-shape facts `decide`. -/

/-- The fixed `Date` value as explicit bytes. -/
theorem deployNow_bytes :
    deployNow = [77, 111, 110, 44, 32, 48, 49, 32, 74, 97, 110, 32, 50, 48, 50,
      52, 32, 48, 48, 58, 48, 48, 58, 48, 48, 32, 71, 77, 84] := by
  with_unfolding_all rfl

/-- `dateHdr` is nonempty with first byte `D` (68) — never begins a `CRLF`. -/
theorem dateHdr_cons : dateHdr = 68 :: ([97, 116, 101, 58, 32] ++ deployNow) := rfl

/-- The injected `Date` header line carries no `CR LF` pair. -/
theorem crlfFree_dateHdr : crlfFree dateHdr = true := by
  rw [dateHdr_cons, deployNow_bytes]; decide

/-! ## 2. The blank-scan distribution and shift lemmas -/

/-- A blank line needs its first two bytes to be `CR LF`. -/
theorem startsBlank_false_of_not_crlf (x y : UInt8) (t : Bytes)
    (h : ¬(x = 13 ∧ y = 10)) : startsBlank (x :: y :: t) = false := by
  match t with
  | [] => rfl
  | [_] => rfl
  | c :: d :: t' =>
    show (x == 13 && y == 10 && c == 13 && d == 10) = false
    by_cases hx : x = 13
    · have hy : y ≠ 10 := fun hy => h ⟨hx, hy⟩
      rw [beq_false_of_ne hy]
      simp
    · rw [beq_false_of_ne hx]
      simp

/-- **The blank scan distributes over a `crlfFree` line + `CRLF`.** A blank fires
exactly at the line end iff the tail begins with another `CRLF`; otherwise the
scan walks the line + `CRLF` (adding their length) and resumes in the tail. -/
theorem blankLen_line_append (A : Bytes) :
    ∀ M : Bytes, crlfFree A = true →
      blankLen (A ++ 13 :: 10 :: M)
        = if startsCRLF M then A.length + 4 else A.length + 2 + blankLen M := by
  induction A with
  | nil =>
    intro M _
    show blankLen (13 :: 10 :: M) = _
    match M with
    | [] => rfl
    | [m0] => rfl
    | m0 :: m1 :: M' =>
      have h1 : startsBlank (13 :: 10 :: m0 :: m1 :: M') = (m0 == 13 && m1 == 10) := by
        show ((13 : UInt8) == 13 && (10 : UInt8) == 10 && m0 == 13 && m1 == 10) = _
        rw [show ((13 : UInt8) == 13) = true from rfl,
            show ((10 : UInt8) == 10) = true from rfl]
        simp
      have h2 : startsCRLF (m0 :: m1 :: M') = (m0 == 13 && m1 == 10) := rfl
      have h3 : blankLen (10 :: m0 :: m1 :: M') = blankLen (m0 :: m1 :: M') + 1 := by
        show (if startsBlank (10 :: m0 :: m1 :: M') then 4
              else blankLen (m0 :: m1 :: M') + 1) = _
        rw [startsBlank_false_of_not_crlf 10 m0 _
              (by rintro ⟨h10, -⟩; exact absurd h10 (by decide)),
            if_neg (by simp)]
      rw [blankLen, h1, h2]
      by_cases hb : (m0 == 13 && m1 == 10) = true
      · rw [if_pos hb, if_pos hb]; rfl
      · rw [if_neg hb, if_neg hb, h3]
        simp only [List.length_nil]
        omega
  | cons a A' ih =>
    intro M h
    show blankLen (a :: (A' ++ 13 :: 10 :: M)) = _
    have hsb : startsBlank (a :: (A' ++ 13 :: 10 :: M)) = false := by
      cases A' with
      | nil =>
        exact startsBlank_false_of_not_crlf a 13 _
          (by rintro ⟨-, h10⟩; exact absurd h10 (by decide))
      | cons b A'' =>
        exact startsBlank_false_of_not_crlf a b _ (crlfFree_head a b A'' h)
    rw [blankLen, hsb, if_neg (by simp), ih M (crlfFree_rest a A' h)]
    by_cases hcr : startsCRLF M = true
    · rw [if_pos hcr, if_pos hcr, List.length_cons]
    · rw [if_neg hcr, if_neg hcr, List.length_cons]; omega

/-- The blank take never exceeds the byte count. -/
theorem blankLen_le (L : Bytes) : blankLen L ≤ L.length := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons b rest ih =>
    rw [blankLen]
    by_cases hsb : startsBlank (b :: rest) = true
    · rw [if_pos hsb]
      have h4 : ((b :: rest).take 4).length = 4 := by
        rw [take4_of_startsBlank _ hsb]; rfl
      rw [List.length_take] at h4
      omega
    · rw [if_neg hsb, List.length_cons]; omega

/-- `injectDate` in nested-cons shape (`++` is left-assoc; re-associate once). -/
theorem injectDate_shape (bs : Bytes) :
    injectDate bs
      = beforeCRLF bs ++ 13 :: 10 :: (dateHdr ++ 13 :: 10 :: afterCRLF bs) := by
  show beforeCRLF bs ++ crlf ++ dateHdr ++ crlf ++ afterCRLF bs = _
  simp only [List.append_assoc]
  rfl

/-- A head whose first `CRLF` sits strictly inside the bytes SPLITS at it. -/
theorem crlf_split (L : Bytes) :
    (beforeCRLF L).length + 2 ≤ L.length →
      L = beforeCRLF L ++ 13 :: 10 :: afterCRLF L := by
  induction L with
  | nil => intro h; rw [show beforeCRLF [] = [] from rfl] at h; simp at h
  | cons a t ih =>
    intro h
    cases t with
    | nil => rw [beforeCRLF_singleton] at h; simp at h
    | cons b rest =>
      by_cases hcr : a = 13 ∧ b = 10
      · obtain ⟨rfl, rfl⟩ := hcr
        rw [show beforeCRLF (13 :: 10 :: rest) = [] from by
              rw [beforeCRLF_cons2]; exact if_pos ⟨rfl, rfl⟩,
            show afterCRLF (13 :: 10 :: rest) = rest from by
              rw [afterCRLF_cons2]; exact if_pos ⟨rfl, rfl⟩]
        rfl
      · have hb : beforeCRLF (a :: b :: rest) = a :: beforeCRLF (b :: rest) := by
          rw [beforeCRLF_cons2, if_neg hcr]
        have ha : afterCRLF (a :: b :: rest) = afterCRLF (b :: rest) := by
          rw [afterCRLF_cons2, if_neg hcr]
        rw [hb, List.length_cons] at h
        rw [hb, ha]
        show a :: (b :: rest)
            = a :: (beforeCRLF (b :: rest) ++ 13 :: 10 :: afterCRLF (b :: rest))
        rw [← ih (by simp only [List.length_cons] at h ⊢; omega)]

/-- **The blank-scan SHIFT.** Splicing `CRLF ++ dateHdr` right after the status
line's `CRLF` moves the blank take by exactly `dateHdr.length + 2` — the `Date`
line can neither create nor mask a blank (it is nonempty, `crlfFree`, and does
not begin with `CR`). Needs only that the head HAS a first `CRLF` in bounds. -/
theorem blankLen_injectDate (L : Bytes)
    (h : (beforeCRLF L).length + 2 ≤ L.length) :
    blankLen (injectDate L) = blankLen L + (dateHdr.length + 2) := by
  have hB : crlfFree (beforeCRLF L) = true := crlfFree_beforeCRLF L
  have hsplit := crlf_split L h
  have hinj := injectDate_shape L
  have hsc : startsCRLF (dateHdr ++ 13 :: 10 :: afterCRLF L) = false := by
    rw [dateHdr_cons]
    exact startsCRLF_ne13 68 _ (by decide)
  have hbl : blankLen L = if startsCRLF (afterCRLF L) then (beforeCRLF L).length + 4
      else (beforeCRLF L).length + 2 + blankLen (afterCRLF L) := by
    conv => lhs; rw [hsplit]
    exact blankLen_line_append _ _ hB
  rw [hinj, blankLen_line_append _ _ hB, hsc, if_neg (by simp),
      blankLen_line_append dateHdr _ crlfFree_dateHdr, hbl]
  by_cases hct : startsCRLF (afterCRLF L) = true
  · rw [if_pos hct, if_pos hct]; omega
  · rw [if_neg hct, if_neg hct]; omega

/-! ## 3. The fusion, list level -/

/-- Take past a line + `CRLF`: the line and its `CRLF` survive, the count moves
into the tail. -/
theorem take_line (B R : Bytes) (j : Nat) :
    (B ++ 13 :: 10 :: R).take (B.length + 2 + j) = B ++ 13 :: 10 :: R.take j := by
  rw [List.take_append, List.take_of_length_le (by omega),
      show B.length + 2 + j - B.length = j + 2 from by omega,
      show (13 :: 10 :: R).take (j + 2) = 13 :: 10 :: R.take j from rfl]

/-- Drop past a line + `CRLF`. -/
theorem drop_line (B R : Bytes) (j : Nat) :
    (B ++ 13 :: 10 :: R).drop (B.length + 2 + j) = R.drop j := by
  rw [List.drop_append, List.drop_of_length_le (by omega),
      List.nil_append,
      show B.length + 2 + j - B.length = j + 2 from by omega,
      show (13 :: 10 :: R).drop (j + 2) = R.drop j from rfl]

/-- The fusion over an explicitly split head `B ++ CRLF ++ T`: scrubbing the
`Date`-injected bytes at the SHIFTED blank equals scrubbing the `Date`-injected
HEAD alone and re-attaching the untouched body. -/
theorem fuse_split (B T : Bytes) (m : Nat) (hB : crlfFree B = true)
    (hn : blankLen (B ++ 13 :: 10 :: T) = B.length + 2 + m) :
    scrubCorr (injectDate (B ++ 13 :: 10 :: T))
      = scrubLines (injectDate ((B ++ 13 :: 10 :: T).take (B.length + 2 + m)))
        ++ (B ++ 13 :: 10 :: T).drop (B.length + 2 + m) := by
  have hbc : beforeCRLF (B ++ 13 :: 10 :: T) = B := beforeCRLF_append B T hB
  have hac : afterCRLF (B ++ 13 :: 10 :: T) = T := afterCRLF_append B T hB
  have hinj : injectDate (B ++ 13 :: 10 :: T)
      = B ++ 13 :: 10 :: (dateHdr ++ 13 :: 10 :: T) := by
    rw [injectDate_shape, hbc, hac]
  have hlen : (beforeCRLF (B ++ 13 :: 10 :: T)).length + 2
      ≤ (B ++ 13 :: 10 :: T).length := by
    rw [hbc, List.length_append, List.length_cons, List.length_cons]; omega
  have hshift := blankLen_injectDate _ hlen
  rw [hn] at hshift
  -- LHS: scrub at the shifted blank
  unfold scrubCorr
  rw [hshift, hinj,
      show B.length + 2 + m + (dateHdr.length + 2)
          = B.length + 2 + (dateHdr.length + (m + 2)) from by omega,
      take_line, drop_line,
      List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      show dateHdr.length + (m + 2) - dateHdr.length = m + 2 from by omega,
      show (13 :: 10 :: T).take (m + 2) = 13 :: 10 :: T.take m from rfl,
      List.drop_append, List.drop_of_length_le (Nat.le_add_right _ _),
      List.nil_append,
      show dateHdr.length + (m + 2) - dateHdr.length = m + 2 from by omega,
      show (13 :: 10 :: T).drop (m + 2) = T.drop m from rfl]
  -- RHS: inject into the taken head, attach the dropped body
  rw [take_line, drop_line,
      show injectDate (B ++ 13 :: 10 :: T.take m)
          = B ++ 13 :: 10 :: (dateHdr ++ 13 :: 10 :: T.take m) from by
        rw [injectDate_shape, beforeCRLF_append B _ hB, afterCRLF_append B _ hB]]

/-- **The fusion (list spec).** When the head's first `CRLF` lies within the
blank scan, `scrubCorr ∘ injectDate` factors through the HEAD alone: scrub the
`Date`-injected head, append the body bytes verbatim. -/
theorem scrubCorr_injectDate_fused (L : Bytes)
    (h : (beforeCRLF L).length + 2 ≤ blankLen L) :
    scrubCorr (injectDate L)
      = scrubLines (injectDate (L.take (blankLen L))) ++ L.drop (blankLen L) := by
  have hlen : (beforeCRLF L).length + 2 ≤ L.length := Nat.le_trans h (blankLen_le L)
  have hsplit := crlf_split L hlen
  obtain ⟨m, hm⟩ : ∃ m, blankLen L = (beforeCRLF L).length + 2 + m :=
    ⟨blankLen L - ((beforeCRLF L).length + 2), by omega⟩
  have hn : blankLen (beforeCRLF L ++ 13 :: 10 :: afterCRLF L)
      = (beforeCRLF L).length + 2 + m := by rw [← hsplit]; exact hm
  have hfuse := fuse_split (beforeCRLF L) (afterCRLF L) m (crlfFree_beforeCRLF L) hn
  rw [← hsplit, ← hm] at hfuse
  exact hfuse

/-! ## 4. The fusion, `ByteArray` level — `scrubDateBA = scrubCorrBA ∘ injectDateBA` -/

/-- `ByteArray`s with equal list readings are equal. -/
theorem ba_eq_of_toList {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  rw [ba_toList_eq, ba_toList_eq] at h
  have hd : a.data = b.data := Array.toList_inj.mp h
  calc a = ⟨a.data⟩ := rfl
    _ = ⟨b.data⟩ := by rw [hd]
    _ = b := rfl

/-- **The fused post-processor IS the unfused composition — every input.** The
single-`copySlice` body attach produces byte-for-byte `scrubCorrBA ∘ injectDateBA`;
the degenerate branch (no `CRLF` within the blank scan) is that composition
verbatim. This discharges the `#guard`-pinned claim in `ServeConformantFast` as a
theorem over ALL inputs. -/
theorem scrubDateBA_eq (bs : ByteArray) :
    scrubDateBA bs = scrubCorrBA (injectDateBA bs) := by
  show (if crIdxFrom bs 0 + 2 ≤ blankTakeFrom bs 0 then
      bs.copySlice (blankTakeFrom bs 0)
        (ByteArray.mk (scrubLines (injectDate
          (bs.extract 0 (blankTakeFrom bs 0)).toList)).toArray)
        (ByteArray.mk (scrubLines (injectDate
          (bs.extract 0 (blankTakeFrom bs 0)).toList)).toArray).size
        (bs.size - blankTakeFrom bs 0) false
    else scrubCorrBA (injectDateBA bs)) = scrubCorrBA (injectDateBA bs)
  by_cases hg : crIdxFrom bs 0 + 2 ≤ blankTakeFrom bs 0
  · rw [if_pos hg]
    have hcr : crIdxFrom bs 0 = (beforeCRLF bs.toList).length := by
      have h := crIdxFrom_eq bs bs.size 0 (by omega) (by omega)
      simpa using h
    have hbl : blankTakeFrom bs 0 = blankLen bs.toList := by
      have h := blankTakeFrom_eq bs bs.size 0 (by omega) (by omega)
      simpa using h
    apply ba_eq_of_toList
    rw [copySlice_tail_toList, mk_toArray_toList, BA_extract_toList,
        scrubCorrBA_toList, injectDateBA_toList]
    simp only [List.drop_zero, Nat.sub_zero]
    rw [hbl]
    exact (scrubCorr_injectDate_fused bs.toList
      (by rw [hcr, hbl] at hg; exact hg)).symm
  · rw [if_neg hg]

/-! ## 5. The fused wrapper = the deployed wrapper, for ANY inner -/

/-- The fused accepted path is the scrub of the deployed accepted path. -/
theorem acceptedFastBA_eq (inner : ByteArray → ByteArray) (req : Request)
    (innerInput : ByteArray) :
    acceptedFastBA inner req innerInput
      = scrubCorrBA (acceptedRawBA inner req innerInput) := by
  unfold Datapath.ServeConformantFast.acceptedFastBA Reactor.ServeConformant.acceptedRawBA
  by_cases hc : hasConditional req = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]; exact scrubDateBA_eq _

/-- **The fused conformant wrapper serves the deployed conformant bytes** — for
ANY inner serve and EVERY input. Same gates, same branches; only the accepted
non-conditional post-processing is fused (by `scrubDateBA_eq`). -/
theorem conformantServeFast_eq (inner : ByteArray → ByteArray) (input : ByteArray) :
    conformantServeFast inner input = conformantServe inner input := by
  -- The raw trees agree: the fast tree is the deployed tree with `scrubCorrBA`
  -- pushed into every leaf. Each level is case-split with the discriminant OPEN
  -- (a `show` re-states the constructor-reduced goal so the next discriminant is
  -- abstractable), keeping every leaf a small syntactic `rfl` — no whnf descent
  -- into the symbolic gates.
  have hraw :
      (match Proto.RequestSerialize.parse (reqBytes input) with
        | none => scrubCorrBA (ByteArray.mk
            (serialize (addDate Reactor.Stage.RequestValidation.badRequestResp)).toArray)
        | some req =>
          match strictStage.onRequest (mkCtx input req) with
          | .respond r => scrubCorrBA (ByteArray.mk (serialize (addDate r)).toArray)
          | .continue c' =>
            match framingValidationStage.onRequest c' with
            | .respond r => scrubCorrBA (ByteArray.mk (serialize (addDate r)).toArray)
            | .continue c'' =>
              let innerInput :=
                if c''.req.target == req.target then input
                else ByteArray.mk (Proto.RequestSerialize.serialize c''.req).toArray
              acceptedFastBA inner req innerInput)
      = scrubCorrBA (respBytesRawBA inner input) := by
    unfold Reactor.ServeConformant.respBytesRawBA
    cases hp : Proto.RequestSerialize.parse (reqBytes input)
    case none => rfl
    case some req =>
      show (match strictStage.onRequest (mkCtx input req) with
          | .respond r => scrubCorrBA (ByteArray.mk (serialize (addDate r)).toArray)
          | .continue c' =>
            match framingValidationStage.onRequest c' with
            | .respond r => scrubCorrBA (ByteArray.mk (serialize (addDate r)).toArray)
            | .continue c'' =>
              let innerInput :=
                if c''.req.target == req.target then input
                else ByteArray.mk (Proto.RequestSerialize.serialize c''.req).toArray
              acceptedFastBA inner req innerInput)
        = scrubCorrBA (match strictStage.onRequest (mkCtx input req) with
          | .respond r => ByteArray.mk (serialize (addDate r)).toArray
          | .continue c' =>
            match framingValidationStage.onRequest c' with
            | .respond r => ByteArray.mk (serialize (addDate r)).toArray
            | .continue c'' =>
              let innerInput :=
                if c''.req.target == req.target then input
                else ByteArray.mk (Proto.RequestSerialize.serialize c''.req).toArray
              acceptedRawBA inner req innerInput)
      cases hs : strictStage.onRequest (mkCtx input req)
      next r => rfl
      next c1 =>
        show (match framingValidationStage.onRequest c1 with
            | .respond r => scrubCorrBA (ByteArray.mk (serialize (addDate r)).toArray)
            | .continue c'' =>
              let innerInput :=
                if c''.req.target == req.target then input
                else ByteArray.mk (Proto.RequestSerialize.serialize c''.req).toArray
              acceptedFastBA inner req innerInput)
          = scrubCorrBA (match framingValidationStage.onRequest c1 with
            | .respond r => ByteArray.mk (serialize (addDate r)).toArray
            | .continue c'' =>
              let innerInput :=
                if c''.req.target == req.target then input
                else ByteArray.mk (Proto.RequestSerialize.serialize c''.req).toArray
              acceptedRawBA inner req innerInput)
        cases hf : framingValidationStage.onRequest c1
        next r => rfl
        next c2 => exact acceptedFastBA_eq inner req _
  unfold Datapath.ServeConformantFast.conformantServeFast
    Reactor.ServeConformant.conformantServe
  cases hz : headGate input
  case some r => rfl
  case none =>
    -- The ACME HTTP-01 arm is served identically by both (it short-circuits
    -- ahead of the post-processor, so there is nothing to fuse).
    cases ha : acmeChallengeBytes input
    case some out => rfl
    case none =>
      exact congrArg
        (fun raw => if isHeadReq input then stripBodyBA raw else raw) hraw

/-! ## 6. The deployed instantiation — fused wrapper, head-idx inner -/

open Datapath.ServeHeadIdx (serveHeadIdx)

/-- **The fused conformant HEAD-IDX serve** (`drorb_serve_conformant_fast_head_idx`)
— the single-copy conformance wrapper around the index-native-head inner. Same
`ByteArray -> ByteArray` ABI as `drorb_serve_conformant_head_idx` (the deployed
non-metered `Seam::Http` default), byte-identical to it for EVERY input
(`serveConformantFastHeadIdx_eq_conformant` — the deployed export is
definitionally `conformantServe serveHeadIdx`). The accepted non-conditional
response is post-processed with ONE whole-body `copySlice` instead of ~4. -/
@[export drorb_serve_conformant_fast_head_idx]
def serveConformantFastHeadIdx (input : ByteArray) : ByteArray :=
  conformantServeFast serveHeadIdx input

/-- **Byte-identity to the deployed non-metered default.**
`conformantServe serveHeadIdx` IS `drorbServeConformantHeadIdx`
(`drorb_serve_conformant_head_idx`) by definition — so swapping the deployed
export for the fused serve changes NO served byte. -/
theorem serveConformantFastHeadIdx_eq_conformant (input : ByteArray) :
    serveConformantFastHeadIdx input = conformantServe serveHeadIdx input :=
  conformantServeFast_eq _ input

/-- The measured fused probe (`drorb_serve_conformant_fast`, `DRORB_SPAN=22`) is
now PROVEN byte-identical to the proven conformant-dense serve
(`drorb_serve_conformant_dense`, `=20`) — no longer `#guard`-pinned. -/
theorem serveConformantFastIdx_eq_denseIdx (input : ByteArray) :
    serveConformantFastIdx input
      = Datapath.ServeConformantDense.serveConformantDenseIdx input :=
  conformantServeFast_eq _ input

/-! ## Non-vacuity — the fused export fires the dense arm through the wrapper -/

open Datapath.ServeDenseReal (bulkDemoReqAnyHost)

-- The fused conformant head-idx serve on a real `/bulk` request carries the 1 MiB body.
#guard (serveConformantFastHeadIdx bulkDemoReqAnyHost).size > 1048576

/-! ## Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound} -/

#print axioms scrubDateBA_eq
#print axioms conformantServeFast_eq
#print axioms serveConformantFastHeadIdx_eq_conformant
#print axioms serveConformantFastIdx_eq_denseIdx

end Datapath.ServeConformantFused
