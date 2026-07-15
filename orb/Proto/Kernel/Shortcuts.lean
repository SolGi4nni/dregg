/-
# Proto.Kernel.Shortcuts — the pure-kernel shortcut-lemma library

The behaviour proofs over the deployed serve keep hitting the same two walls:

  1. **The `ByteArray.toList` wall.** `String.toUTF8` itself is structural
     (`data.flatMap utf8EncodeChar`), but `ByteArray.toList` is well-founded-recursive,
     so `toUTF8`-derived byte constants are opaque to `decide`/`rfl`. Until now every
     `Proto/*Proven.lean` carried its own private copy of the `ba_toList_eq` bridge.

  2. **The `String`-function wall.** The deployed header parser (`reqOfHeaders` →
     `findHeader`/`parseRangeSet`) routes through `String.toLower`/`splitOn`/`trim`/
     `toNat?`/`isPrefixOf`, all of which bottom out in well-founded-recursive worker
     loops (`mapAux`, `splitOnAux`, `foldlAux`, `anyAux`, `takeWhileAux`,
     `takeRightWhileAux`, `substrEq.loop`). None reduce in the kernel, so concrete
     parses could previously only be discharged by `native_decide` — dragging
     `Lean.ofReduceBool` (the compiler!) into the TCB (`Proto.RangeProven` was the one
     Proto file paying that tax).

This file evicts both walls WITHOUT `native_decide`:

  * §1 the shared `ba_toList_eq` bridge (one copy, public) + `toUTF8_toList`.
  * §2 an ASCII characterization of `toUTF8`: `toUTF8_toList_ascii` /`strBytes_ascii`
    rewrite `s.toUTF8.toList` to a structural `s.data.map`, and `bytesToStr_strBytes`
    is the Latin-1 round-trip the header parser depends on. Header/Date-style proofs
    can now REWRITE at the char level instead of whole-list `decide` over `toUTF8`.
  * §3 the WF **step kit**: for each well-founded String worker loop, `eq_def`-derived
    step/stop lemmas whose side conditions are closed structural facts. A concrete
    call evaluates by `simp (config := { decide := true }) only [<step lemmas>]` —
    each step's guard is discharged by kernel `decide`, no compiler anywhere. This is
    the String-lemma development `Proto.OptionsProven` records as "deliberately
    avoided"; it is now available.
  * §4 serialize characterizations: `natToDec_eq`/`natToDec_eq_map` (decimal status/
    length bytes as a structural map over `Nat.repr`, via `repr_ascii`),
    `statusLineOf_eq`, `serialize_statusLine` (append-normalized framing),
    `statusLine_isPrefix_serialize`, and the `renderHeaders` equations.
  * §5 the shared deployed-route factor: `deployed_staticFile_route`,
    `ok_header_names`, `notin_ok_of_ne`, `serve_plain_ok`, `serveDeployed_plain_eq`,
    `plain_get_status_200`, `plain_get_omits_of_ne` — the shape
    `Proto.{Vary,Age,ContentDisposition}Proven` each re-proved from scratch.

Everything here is pure kernel: `#print axioms` ⊆ {propext, Quot.sound}. No
`native_decide`, no `Lean.ofReduceBool`, no `sorryAx`.
-/

import StaticFile
import Reactor.App
import Reactor.Serialize

namespace Proto.Kernel.Shortcuts

/-! ## §1 The `ByteArray.toList` kernel bridge (shared, public) -/

/-- Kernel-reducibility bridge for `toUTF8`-derived byte lists. `ByteArray.toList`
(Lean core) is defined by well-founded recursion (`termination_by bs.size - i`), so it
does NOT reduce in the kernel; this rewrites it to the structural `bs.data.toList`,
which the kernel DOES reduce — letting concrete byte witnesses close by `decide` in the
pure kernel. Previously copy-pasted privately into a dozen `Proto/*Proven.lean` files;
this is the one shared copy. -/
theorem ba_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  have key : ∀ (n i : Nat) (r : List UInt8),
      bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro n
    induction n with
    | zero =>
      intro i r hi
      rw [ByteArray.toList.loop.eq_def]
      have hnlt : ¬ i < bs.size := by omega
      simp only [hnlt, if_false]
      have hdrop : bs.data.toList.drop i = [] := by
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]
        have : bs.data.size = bs.size := rfl
        omega
      rw [hdrop, List.append_nil]
    | succ n ih =>
      intro i r hi
      rw [ByteArray.toList.loop.eq_def]
      have hlt : i < bs.size := by omega
      simp only [hlt, if_true]
      rw [ih (i+1) (bs.get! i :: r) (by omega)]
      have hidx : i < bs.data.toList.length := by rw [Array.length_toList]; exact hlt
      have hsz : i < bs.data.size := by rw [← Array.length_toList]; exact hidx
      have hget : bs.get! i = bs.data.toList[i]'hidx := by
        rw [show bs.get! i = bs.data.get! i from rfl, Array.get!_eq_getElem!,
            getElem!_pos bs.data i hsz, ← Array.getElem_toList hsz]
      rw [List.drop_eq_getElem_cons hidx, List.reverse_cons, hget, List.append_assoc]
      rfl
  have h := key bs.size 0 [] (by omega)
  rw [ByteArray.toList]
  simpa using h

/-- `toUTF8` itself is structural: through the bridge, its bytes are a `flatMap` of the
per-char encodings over the (kernel-reducible) `String.data`. -/
theorem toUTF8_toList (s : String) :
    s.toUTF8.toList = s.data.flatMap String.utf8EncodeChar := by
  rw [ba_toList_eq]; rfl

/-- `StaticFile.strBytes` in structural form. -/
theorem strBytes_toList (s : String) :
    StaticFile.strBytes s = s.data.flatMap String.utf8EncodeChar :=
  toUTF8_toList s

/-! ## §2 ASCII characterization of `toUTF8` (rewrite, don't decide) -/

/-- An ASCII code point UTF-8-encodes to its single byte. -/
theorem utf8EncodeChar_ascii {c : Char} (h : c.val ≤ 0x7f) :
    String.utf8EncodeChar c = [c.val.toUInt8] := by
  simp [String.utf8EncodeChar, h]

/-- On an all-ASCII char list the UTF-8 `flatMap` is a plain `map`. -/
theorem flatMap_utf8_ascii :
    ∀ (l : List Char), (∀ c ∈ l, c.val ≤ 0x7f) →
      l.flatMap String.utf8EncodeChar = l.map (fun c => c.val.toUInt8)
  | [], _ => rfl
  | c :: t, h => by
    rw [List.flatMap_cons, List.map_cons,
        utf8EncodeChar_ascii (h c (List.mem_cons_self c t)),
        flatMap_utf8_ascii t (fun x hx => h x (List.mem_cons_of_mem c hx))]
    rfl

/-- **The `toUTF8` ASCII characterization.** For an all-ASCII string the wire bytes are
a structural one-byte-per-char `map` over `s.data` — header/Date-style byte proofs
rewrite through this instead of whole-list `decide` over `toUTF8`. -/
theorem toUTF8_toList_ascii (s : String) (h : ∀ c ∈ s.data, c.val ≤ 0x7f) :
    s.toUTF8.toList = s.data.map (fun c => c.val.toUInt8) := by
  rw [toUTF8_toList, flatMap_utf8_ascii s.data h]

/-- `strBytes` form of the ASCII characterization. -/
theorem strBytes_ascii (s : String) (h : ∀ c ∈ s.data, c.val ≤ 0x7f) :
    StaticFile.strBytes s = s.data.map (fun c => c.val.toUInt8) :=
  toUTF8_toList_ascii s h

/-- UInt32 `≤` transfers to `toNat` (the direction the ASCII lemmas need). -/
theorem u32_le_toNat {a b : UInt32} (h : a ≤ b) : a.toNat ≤ b.toNat :=
  UInt32.le_iff_toNat_le.mp h

/-- Round-trip of an ASCII char through its UTF-8 byte. -/
theorem char_ofNat_val_toUInt8 {c : Char} (h : c.val ≤ 0x7f) :
    Char.ofNat c.val.toUInt8.toNat = c := by
  have h127 : c.val.toNat ≤ 127 := u32_le_toNat h
  have h1 : c.val.toUInt8.toNat = c.toNat := by
    rw [UInt32.toNat_toUInt8]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h1, Char.ofNat_toNat]

/-- **The parser round-trip.** `bytesToStr` (the deployed header parser's Latin-1
decode) inverts `strBytes` on ASCII strings — the fact `findHeader` evaluation
hinges on. -/
theorem bytesToStr_strBytes {s : String} (h : ∀ c ∈ s.data, c.val ≤ 0x7f) :
    StaticFile.bytesToStr (StaticFile.strBytes s) = s := by
  rw [strBytes_ascii s h]
  show String.mk (((s.data.map (fun c => c.val.toUInt8))).map (fun x => Char.ofNat x.toNat)) = s
  rw [List.map_map]
  have key : ∀ (l : List Char), (∀ c ∈ l, c.val ≤ 0x7f) →
      l.map ((fun x : UInt8 => Char.ofNat x.toNat) ∘ (fun c : Char => c.val.toUInt8)) = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a t ih =>
      rw [List.map_cons]
      have ha : Char.ofNat a.val.toUInt8.toNat = a :=
        char_ofNat_val_toUInt8 (hl a (List.mem_cons_self a t))
      rw [show ((fun x : UInt8 => Char.ofNat x.toNat) ∘ (fun c : Char => c.val.toUInt8)) a
            = Char.ofNat a.val.toUInt8.toNat from rfl, ha,
          ih (fun x hx => hl x (List.mem_cons_of_mem a hx))]
  rw [key s.data h]

/-! ## §3 The WF step kit

Each Lean-core well-founded String worker loop gets `eq_def`-derived step/stop lemmas
whose hypotheses are closed structural facts on concrete inputs. A concrete call then
evaluates in the pure kernel by

    simp (config := { decide := true }) only [<the loop's step lemmas>]

(each guard is discharged by kernel `decide`), or by an explicit
`rw [step _ _ _ (by decide) …]` chain. -/

/-! ### `String.mapAux` (drives `String.map`, `toLower`, `toUpper`) -/

theorem mapAux_stop (f : Char → Char) (i : String.Pos) (s : String)
    (h : s.atEnd i = true) : String.mapAux f i s = s := by
  rw [String.mapAux.eq_def]; simp [h]

theorem mapAux_step (f : Char → Char) (i : String.Pos) (s : String)
    (h : s.atEnd i = false) :
    String.mapAux f i s
      = String.mapAux f ((s.set i (f (s.get i))).next i) (s.set i (f (s.get i))) := by
  rw [String.mapAux.eq_def]; simp [h]

/-! ### `String.splitOnAux` (drives `String.splitOn`) -/

theorem splitOnAux_stop (s sep : String) (b i j : String.Pos) (r : List String)
    (h : s.atEnd i = true) :
    String.splitOnAux s sep b i j r = ((s.extract b i) :: r).reverse := by
  rw [String.splitOnAux.eq_def]; simp [h]

theorem splitOnAux_matchend (s sep : String) (b i j : String.Pos) (r : List String)
    (h1 : s.atEnd i = false) (h2 : (s.get i == sep.get j) = true)
    (h3 : sep.atEnd (sep.next j) = true) :
    String.splitOnAux s sep b i j r
      = String.splitOnAux s sep (s.next i) (s.next i) 0
          (s.extract b (s.next i - sep.next j) :: r) := by
  rw [String.splitOnAux.eq_def]; simp [h1, h2, h3]

theorem splitOnAux_matchcont (s sep : String) (b i j : String.Pos) (r : List String)
    (h1 : s.atEnd i = false) (h2 : (s.get i == sep.get j) = true)
    (h3 : sep.atEnd (sep.next j) = false) :
    String.splitOnAux s sep b i j r
      = String.splitOnAux s sep b (s.next i) (sep.next j) r := by
  rw [String.splitOnAux.eq_def]; simp [h1, h2, h3]

theorem splitOnAux_miss (s sep : String) (b i j : String.Pos) (r : List String)
    (h1 : s.atEnd i = false) (h2 : (s.get i == sep.get j) = false) :
    String.splitOnAux s sep b i j r
      = String.splitOnAux s sep b (s.next (i - j)) 0 r := by
  rw [String.splitOnAux.eq_def]; simp [h1, h2]

/-! ### `String.foldlAux` (drives `String.foldl`, hence `toNat?`'s digit fold) -/

theorem foldlAux_step {α : Type _} (f : α → Char → α) (s : String) (stopPos i : String.Pos)
    (a : α) (h : i < stopPos) :
    String.foldlAux f s stopPos i a
      = String.foldlAux f s stopPos (s.next i) (f a (s.get i)) := by
  rw [String.foldlAux.eq_def]; simp [h]

theorem foldlAux_stop {α : Type _} (f : α → Char → α) (s : String) (stopPos i : String.Pos)
    (a : α) (h : ¬ i < stopPos) :
    String.foldlAux f s stopPos i a = a := by
  rw [String.foldlAux.eq_def]; simp [h]

/-! ### `String.anyAux` (drives `String.any`/`all`, hence `isNat`) -/

theorem anyAux_true (s : String) (stopPos : String.Pos) (p : Char → Bool) (i : String.Pos)
    (h : i < stopPos) (hp : p (s.get i) = true) :
    String.anyAux s stopPos p i = true := by
  rw [String.anyAux.eq_def]; simp [h, hp]

theorem anyAux_step (s : String) (stopPos : String.Pos) (p : Char → Bool) (i : String.Pos)
    (h : i < stopPos) (hp : p (s.get i) = false) :
    String.anyAux s stopPos p i = String.anyAux s stopPos p (s.next i) := by
  rw [String.anyAux.eq_def]; simp [h, hp]

theorem anyAux_stop (s : String) (stopPos : String.Pos) (p : Char → Bool) (i : String.Pos)
    (h : ¬ i < stopPos) :
    String.anyAux s stopPos p i = false := by
  rw [String.anyAux.eq_def]; simp [h]

/-! ### `Substring.takeWhileAux` / `takeRightWhileAux` (drive `String.trim`) -/

theorem takeWhileAux_step (s : String) (stopPos : String.Pos) (p : Char → Bool)
    (i : String.Pos) (h : i < stopPos) (hp : p (s.get i) = true) :
    Substring.takeWhileAux s stopPos p i = Substring.takeWhileAux s stopPos p (s.next i) := by
  rw [Substring.takeWhileAux.eq_def]; simp [h, hp]

theorem takeWhileAux_stop_false (s : String) (stopPos : String.Pos) (p : Char → Bool)
    (i : String.Pos) (h : i < stopPos) (hp : p (s.get i) = false) :
    Substring.takeWhileAux s stopPos p i = i := by
  rw [Substring.takeWhileAux.eq_def]; simp [h, hp]

theorem takeWhileAux_stop_end (s : String) (stopPos : String.Pos) (p : Char → Bool)
    (i : String.Pos) (h : ¬ i < stopPos) :
    Substring.takeWhileAux s stopPos p i = i := by
  rw [Substring.takeWhileAux.eq_def]; simp [h]

theorem takeRightWhileAux_step (s : String) (begPos : String.Pos) (p : Char → Bool)
    (i : String.Pos) (h : begPos < i) (hp : p (s.get (s.prev i)) = true) :
    Substring.takeRightWhileAux s begPos p i
      = Substring.takeRightWhileAux s begPos p (s.prev i) := by
  rw [Substring.takeRightWhileAux.eq_def]; simp [h, hp]

theorem takeRightWhileAux_stop_false (s : String) (begPos : String.Pos) (p : Char → Bool)
    (i : String.Pos) (h : begPos < i) (hp : p (s.get (s.prev i)) = false) :
    Substring.takeRightWhileAux s begPos p i = i := by
  rw [Substring.takeRightWhileAux.eq_def]; simp [h, hp]

theorem takeRightWhileAux_stop_end (s : String) (begPos : String.Pos) (p : Char → Bool)
    (i : String.Pos) (h : ¬ begPos < i) :
    Substring.takeRightWhileAux s begPos p i = i := by
  rw [Substring.takeRightWhileAux.eq_def]; simp [h]

/-! ### `String.substrEq.loop` (drives `isPrefixOf`/`startsWith`) -/

theorem substrEq_loop_step (s1 s2 : String) (off1 off2 stop1 : String.Pos)
    (h : off1.byteIdx < stop1.byteIdx) :
    String.substrEq.loop s1 s2 off1 off2 stop1
      = ((s1.get off1 == s2.get off2)
          && String.substrEq.loop s1 s2 (off1 + s1.get off1) (off2 + s2.get off2) stop1) := by
  rw [String.substrEq.loop.eq_def]; simp [h]

theorem substrEq_loop_stop (s1 s2 : String) (off1 off2 stop1 : String.Pos)
    (h : ¬ off1.byteIdx < stop1.byteIdx) :
    String.substrEq.loop s1 s2 off1 off2 stop1 = true := by
  rw [String.substrEq.loop.eq_def]; simp [h]

/-! ## §4 serialize characterizations -/

/-- Every `Nat.digitChar` output is ASCII. -/
theorem digitChar_ascii (n : Nat) : (Nat.digitChar n).val ≤ 0x7f := by
  by_cases h : n < 16
  · have hsmall : ∀ m, m < 16 → (Nat.digitChar m).val ≤ 0x7f := by decide
    exact hsmall n h
  · unfold Nat.digitChar
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    decide

/-- `Nat.toDigitsCore` preserves ASCII-ness of the accumulator and only adds ASCII
digit chars. -/
theorem toDigitsCore_ascii (b : Nat) :
    ∀ (fuel n : Nat) (ds : List Char), (∀ c ∈ ds, c.val ≤ 0x7f) →
      ∀ c ∈ Nat.toDigitsCore b fuel n ds, c.val ≤ 0x7f := by
  intro fuel
  induction fuel with
  | zero =>
    intro n ds hds c hc
    simp only [Nat.toDigitsCore] at hc
    exact hds c hc
  | succ f ih =>
    intro n ds hds c hc
    simp only [Nat.toDigitsCore] at hc
    have hcons : ∀ x ∈ Nat.digitChar (n % b) :: ds, x.val ≤ 0x7f := by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; exact digitChar_ascii (n % b)
      · exact hds x h
    by_cases hz : n / b = 0
    · rw [if_pos hz] at hc
      exact hcons c hc
    · rw [if_neg hz] at hc
      exact ih (n / b) (Nat.digitChar (n % b) :: ds) hcons c hc

/-- `Nat.repr` is all-ASCII (decimal digits). -/
theorem repr_ascii (n : Nat) : ∀ c ∈ (Nat.repr n).data, c.val ≤ 0x7f := by
  intro c hc
  have hd : (Nat.repr n).data = Nat.toDigitsCore 10 (n + 1) n [] := rfl
  rw [hd] at hc
  exact toDigitsCore_ascii 10 (n + 1) n [] (fun x hx => absurd hx (List.not_mem_nil x)) c hc

/-- The serializer's decimal rendering, in structural (`flatMap`) form. -/
theorem natToDec_eq (n : Nat) :
    Reactor.natToDec n = (Nat.repr n).data.flatMap String.utf8EncodeChar := by
  rw [show Reactor.natToDec n = (Nat.repr n).toUTF8.toList from rfl, toUTF8_toList]

/-- **The serializer's decimal rendering as a structural `map`** (status codes and
`Content-Length` values): concrete instances now close by rewrite + char-level
`decide`, never by whole-list `decide` over `toUTF8`. -/
theorem natToDec_eq_map (n : Nat) :
    Reactor.natToDec n = (Nat.repr n).data.map (fun c => c.val.toUInt8) := by
  rw [show Reactor.natToDec n = (Nat.repr n).toUTF8.toList from rfl,
      toUTF8_toList_ascii _ (repr_ascii n)]

/-- The status line, compositionally. -/
theorem statusLineOf_eq (resp : Reactor.Response) :
    Reactor.statusLineOf resp
      = Reactor.http11 ++ [32] ++ Reactor.natToDec resp.status ++ [32] ++ resp.reason := rfl

/-- `serialize` with the status line split off as the head of one append (the
prefix-extraction form of `Reactor.serialize_framing`). -/
theorem serialize_statusLine (resp : Reactor.Response) :
    Reactor.serialize resp
      = Reactor.statusLineOf resp
          ++ (Reactor.crlf ++ Reactor.headerBlockOf resp
              ++ Reactor.crlf ++ Reactor.crlf ++ resp.body) := by
  rw [Reactor.serialize_framing]
  simp [List.append_assoc]

/-- The status line is a prefix of the serialized response. -/
theorem statusLine_isPrefix_serialize (resp : Reactor.Response) :
    Reactor.statusLineOf resp <+: Reactor.serialize resp :=
  ⟨_, (serialize_statusLine resp).symm⟩

theorem renderHeaders_nil : Reactor.renderHeaders [] = [] := rfl

theorem renderHeaders_single (h : Proto.Bytes × Proto.Bytes) :
    Reactor.renderHeaders [h] = Reactor.headerLine h := rfl

theorem renderHeaders_cons (h : Proto.Bytes × Proto.Bytes)
    (t : List (Proto.Bytes × Proto.Bytes)) (ht : t ≠ []) :
    Reactor.renderHeaders (h :: t)
      = Reactor.headerLine h ++ Reactor.crlf ++ Reactor.renderHeaders t := by
  match t with
  | [] => exact absurd rfl ht
  | a :: t' => rfl

/-! ## §5 The shared deployed-route factor

`Proto.VaryProven` / `AgeProven` / `ContentDispositionProven` (and kin) each prove the
same five facts from scratch before instantiating their header name. This is the one
shared copy; a Proven file now supplies only its name bytes and three `≠` facts. -/

/-- The served path segments for the deployed asset `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-- The deployed default app's `staticFile` handler is definitionally
`StaticFile.serveDeployed` over the request's normalized target segments and raw
headers. -/
theorem deployed_staticFile_route (req : Proto.Request) :
    Reactor.App.responseOfReq req .staticFile
      = StaticFile.serveDeployed (Reactor.App.targetSegments req.target) req.headers := rfl

/-- The `200 (.ok)` arm's header NAMES are exactly
`[ETag, Accept-Ranges, Content-Type]` — a closed three-element set. -/
theorem ok_header_names (body : Proto.Bytes) (etag : StaticFile.ETag) :
    (StaticFile.toResponse (.ok body etag)).headers.map Prod.fst
      = [StaticFile.strBytes "ETag", StaticFile.strBytes "Accept-Ranges",
         StaticFile.strBytes "Content-Type"] := rfl

/-- Any header name distinct from the three `200` names is absent from the deployed
handler's `200` header list, for every value and independent of the file served. -/
theorem notin_ok_of_ne (name : Proto.Bytes)
    (h1 : name ≠ StaticFile.strBytes "ETag")
    (h2 : name ≠ StaticFile.strBytes "Accept-Ranges")
    (h3 : name ≠ StaticFile.strBytes "Content-Type")
    (body : Proto.Bytes) (etag : StaticFile.ETag) (v : Proto.Bytes) :
    (name, v) ∉ (StaticFile.toResponse (.ok body etag)).headers := by
  intro hmem
  have hname := List.mem_map_of_mem Prod.fst hmem
  rw [ok_header_names] at hname
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

/-- The plain-`GET` selection for `/static/app.js` is the full `200 (.ok)`. -/
theorem serve_plain_ok :
    StaticFile.serveConditional StaticFile.deployedConfig (StaticFile.reqOfHeaders [])
        assetSegs
      = .ok StaticFile.appJs (StaticFile.contentETag StaticFile.appJs) := rfl

/-- The concrete deployed `GET /static/app.js` response IS the rendered `200`. -/
theorem serveDeployed_plain_eq :
    StaticFile.serveDeployed assetSegs []
      = StaticFile.toResponse (.ok StaticFile.appJs (StaticFile.contentETag StaticFile.appJs)) := by
  rw [show StaticFile.serveDeployed assetSegs []
        = StaticFile.toResponse (StaticFile.serveConditional StaticFile.deployedConfig
            (StaticFile.reqOfHeaders []) assetSegs) from rfl, serve_plain_ok]

/-- The concrete deployed `GET /static/app.js` is answered `200 (OK)`. -/
theorem plain_get_status_200 : (StaticFile.serveDeployed assetSegs []).status = 200 := by
  rw [serveDeployed_plain_eq]; rfl

/-- The concrete deployed `GET /static/app.js` answer omits every header whose name
differs from the three `200` names — non-vacuously (this request really hits the `200`
branch). -/
theorem plain_get_omits_of_ne (name : Proto.Bytes)
    (h1 : name ≠ StaticFile.strBytes "ETag")
    (h2 : name ≠ StaticFile.strBytes "Accept-Ranges")
    (h3 : name ≠ StaticFile.strBytes "Content-Type")
    (v : Proto.Bytes) :
    (name, v) ∉ (StaticFile.serveDeployed assetSegs []).headers := by
  rw [serveDeployed_plain_eq]
  exact notin_ok_of_ne name h1 h2 h3 _ _ v

end Proto.Kernel.Shortcuts

#print axioms Proto.Kernel.Shortcuts.ba_toList_eq
#print axioms Proto.Kernel.Shortcuts.toUTF8_toList_ascii
#print axioms Proto.Kernel.Shortcuts.bytesToStr_strBytes
#print axioms Proto.Kernel.Shortcuts.splitOnAux_matchend
#print axioms Proto.Kernel.Shortcuts.natToDec_eq_map
#print axioms Proto.Kernel.Shortcuts.serialize_statusLine
#print axioms Proto.Kernel.Shortcuts.notin_ok_of_ne
#print axioms Proto.Kernel.Shortcuts.plain_get_omits_of_ne
