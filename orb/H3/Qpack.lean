import H3.Varint
import Arena.Basic
import Arena.Theorems

/-!
# QPACK field-section decoding into the arena store (RFC 9204)

Decodes an encoded field section (the payload of an HTTP/3 HEADERS frame)
*into* the two-arena `Arena.Store`: every decoded name/value byte string is
appended to the **sidecar** arena and registered as a view `Entry` whose
offset carries the sidecar discriminant (`Arena.sidecarBase`). The main
arena is never touched — the caller keeps the wire bytes there.

Scope (deliberate cuts, all decodable-prefix layers included):

* **Prefix integers** (§4.1.1) — full, including the continuation-byte cap
  at 62 bits of shift.
* **String literals** (§4.1.2) — full framing. The decoder is parameterized
  over an abstract `HuffmanDecoder` interface, so every theorem below holds
  uniformly for *every* decoder behavior; the concrete RFC 7541 Appendix B
  Huffman decoder (`rfc7541Huffman`, the code an off-the-shelf client emits)
  is implemented below and is the one wired into the deployed QUIC/H3 lane.
* **Static table** (Appendix A) — the full table, indices 0–98; higher indices
  fail with `Err.staticIndex`.
* **Dynamic table** (§3.2) — implemented: a FIFO `DynTable` of `(name, value)`
  pairs with size-bounded oldest-first eviction and absolute / relative /
  post-base index resolution (§3.2.4–§3.2.6). The section prefix reconstructs the
  Base (§4.5.1) and the four dynamic representations (indexed `T=0`, literal with
  name reference `T=0`, indexed post-base, literal with post-base name reference)
  resolve against the supplied table; a reference out of range for the table
  fails with `Err.dynamicUnsupported`. Insertions are supplied out of band (the
  encoder-stream instructions of §4.3 are a separate lane); the field-section
  decode READS the table. The correctness theory in `QpackDynCorrect.lean` binds
  insert/evict/resolve to this deployed decoder.

Headline theorem — the H3 analogue of the H1 parser's `Wf` discharge:
`decodeFieldSection_wf` / `decodeFieldSection_entries_inBounds`: decoding
into a well-formed store yields a well-formed store, i.e. **every view entry
the decode emits is in-bounds of the arena it addresses** — for every
Huffman-decoder behavior and every input. `decodeFieldSection_main` shows
the main arena is preserved byte-for-byte.
-/

namespace H3
namespace Qpack

open Arena

/-! ## Prefix integers (RFC 9204 §4.1.1) -/

/-- Continuation-byte loop of the prefix integer. `shift` is the current
7-bit shift, `acc` the value so far. A continuation reaching past a shift of
62 is rejected (the 62-bit overflow cap); `none` also covers running out of
bytes. Returns `(value, bytesConsumed)`. -/
def decIntCont : Bytes → Nat → Nat → Option (Nat × Nat)
  | [], _, _ => none
  | b :: rest, shift, acc =>
    let acc' := acc + b.toNat % 128 * 2 ^ shift
    if b.toNat < 128 then some (acc', 1)
    else if 62 < shift + 7 then none
    else
      match decIntCont rest (shift + 7) acc' with
      | some (v, n) => some (v, n + 1)
      | none => none

theorem decIntCont_consumed (bs : Bytes) (shift acc v n : Nat)
    (h : decIntCont bs shift acc = some (v, n)) : 1 ≤ n ∧ n ≤ bs.length := by
  induction bs generalizing shift acc v n with
  | nil => exact absurd h (by simp [decIntCont])
  | cons b rest ih =>
    unfold decIntCont at h
    simp only [] at h
    split at h
    · cases h
      simp
    · split at h
      · exact absurd h (by simp)
      · split at h
        · rename_i v' n' hrec
          cases h
          have := ih _ _ _ _ hrec
          simp only [List.length_cons]
          omega
        · exact absurd h (by simp)

/-- Decode a prefix integer whose low `prefixBits` bits live in `first` and
whose continuation bytes (if any) are at the head of `rest`. Returns
`(value, bytesConsumedFromRest)` — the first byte is the caller's. -/
def decPrefixInt (prefixBits : Nat) (first : UInt8) (rest : Bytes) :
    Option (Nat × Nat) :=
  let maxPrefix := 2 ^ prefixBits - 1
  let v := first.toNat % 2 ^ prefixBits
  if v < maxPrefix then some (v, 0)
  else decIntCont rest 0 maxPrefix

theorem decPrefixInt_consumed (p : Nat) (first : UInt8) (rest : Bytes)
    (v n : Nat) (h : decPrefixInt p first rest = some (v, n)) :
    n ≤ rest.length := by
  unfold decPrefixInt at h
  simp only [] at h
  split at h
  · cases h; omega
  · exact (decIntCont_consumed rest 0 _ v n h).2

/-! ## String literals (§4.1.2) and the Huffman interface -/

/-- **The Huffman decoder interface** (RFC 9204 §4.1.2; the code itself is the
HPACK table of RFC 7541 Appendix B). The field-section decoder is parameterized
over this interface so every theorem in this file holds uniformly over every
decoder behavior; the concrete RFC 7541 Appendix B decoder (`rfc7541Huffman`) is
defined below and is the one the deployed lane supplies. `none` means the coded
bit string is invalid (e.g. bad EOS padding). -/
structure HuffmanDecoder where
  decode : Bytes → Option Bytes

/-- Typed error classes of the field-section decode. -/
inductive Err where
  /-- Ran off the end of the field section (or a malformed prefix integer). -/
  | truncated
  /-- A dynamic-table reference: the dynamic table is the explicit
  out-of-scope stub — no table state exists to resolve it. -/
  | dynamicUnsupported
  /-- Static-table index outside the modeled subset. -/
  | staticIndex
  /-- The Huffman decoder rejected a coded string. -/
  | huffman
  /-- A decoded name or value is not valid UTF-8. -/
  | nonUtf8
  /-- The sidecar arena's `2^31` offset space would be exhausted. -/
  | tooLarge
  /-- The encoded field-section prefix is invalid (RFC 9204 §4.5.1.1/§4.5.1.2:
  an Encoded Required Insert Count outside its window, or a negative Base). -/
  | prefixInvalid
  /-- An encoder-stream instruction is invalid (RFC 9204 §4.3: an unresolvable
  name reference / duplicate, or an insertion larger than the capacity). -/
  | encoderStream
deriving Repr, DecidableEq

/-- Decode one string literal: a length prefix integer of `prefixBits` bits
in `first` (the Huffman flag is the bit just above the prefix), then the
string bytes at the head of `rest` after any continuation bytes. Returns the
(possibly Huffman-decoded) bytes and the count consumed from `rest`. -/
def decStr (hd : HuffmanDecoder) (prefixBits : Nat) (first : UInt8)
    (rest : Bytes) : Except Err (Bytes × Nat) :=
  match decPrefixInt prefixBits first rest with
  | none => .error .truncated
  | some (len, n) =>
    let body := (rest.drop n).take len
    if body.length < len then .error .truncated
    else if first.toNat / 2 ^ prefixBits % 2 = 1 then
      match hd.decode body with
      | some out => .ok (out, n + len)
      | none => .error .huffman
    else .ok (body, n + len)

theorem decStr_consumed (hd : HuffmanDecoder) (p : Nat) (first : UInt8)
    (rest : Bytes) (out : Bytes) (n : Nat)
    (h : decStr hd p first rest = .ok (out, n)) : n ≤ rest.length := by
  unfold decStr at h
  split at h
  · exact absurd h (by simp)
  · rename_i len m hlen
    have hm := decPrefixInt_consumed p first rest len m hlen
    simp only [] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hguard
      simp only [List.length_take, List.length_drop] at hguard
      split at h
      · split at h
        · cases h; omega
        · exact absurd h (by simp)
      · cases h; omega

/-- Executable UTF-8 validity check (the dynamic discharge of the model's
explicit UTF-8 hypothesis, as in the H1 parser). -/
def utf8Ok (bs : Bytes) : Bool := String.validateUTF8 (ByteArray.mk bs.toArray)

/-! ## The static table (RFC 9204 Appendix A, indices 0–98) -/

/-- RFC 9204 Appendix A, the full static table (0-based, as in the RFC): all 99
entries (indices 0–98). Indices ≥ 99 fail with `Err.staticIndex`. -/
def staticTable : List (String × String) := [
  (":authority", ""), (":path", "/"), ("age", "0"),
  ("content-disposition", ""), ("content-length", "0"), ("cookie", ""),
  ("date", ""), ("etag", ""), ("if-modified-since", ""),
  ("if-none-match", ""), ("last-modified", ""), ("link", ""),
  ("location", ""), ("referer", ""), ("set-cookie", ""),
  (":method", "CONNECT"), (":method", "DELETE"), (":method", "GET"),
  (":method", "HEAD"), (":method", "OPTIONS"), (":method", "POST"),
  (":method", "PUT"), (":scheme", "http"), (":scheme", "https"),
  (":status", "103"), (":status", "200"), (":status", "304"),
  (":status", "404"), (":status", "503"), ("accept", "*/*"),
  ("accept", "application/dns-message"), ("accept-encoding", "gzip, deflate, br"), ("accept-ranges", "bytes"),
  ("access-control-allow-headers", "cache-control"), ("access-control-allow-headers", "content-type"), ("access-control-allow-origin", "*"),
  ("cache-control", "max-age=0"), ("cache-control", "max-age=2592000"), ("cache-control", "max-age=604800"),
  ("cache-control", "no-cache"), ("cache-control", "no-store"), ("cache-control", "public, max-age=31536000"),
  ("content-encoding", "br"), ("content-encoding", "gzip"), ("content-type", "application/dns-message"),
  ("content-type", "application/javascript"), ("content-type", "application/json"), ("content-type", "application/x-www-form-urlencoded"),
  ("content-type", "image/gif"), ("content-type", "image/jpeg"), ("content-type", "image/png"),
  ("content-type", "text/css"), ("content-type", "text/html; charset=utf-8"), ("content-type", "text/plain"),
  ("content-type", "text/plain;charset=utf-8"), ("range", "bytes=0-"), ("strict-transport-security", "max-age=31536000"),
  ("strict-transport-security", "max-age=31536000; includesubdomains"), ("strict-transport-security", "max-age=31536000; includesubdomains; preload"), ("vary", "accept-encoding"),
  ("vary", "origin"), ("x-content-type-options", "nosniff"), ("x-xss-protection", "1; mode=block"),
  (":status", "100"), (":status", "204"), (":status", "206"),
  (":status", "302"), (":status", "400"), (":status", "403"),
  (":status", "421"), (":status", "425"), (":status", "500"),
  ("accept-language", ""), ("access-control-allow-credentials", "FALSE"), ("access-control-allow-credentials", "TRUE"),
  ("access-control-allow-headers", "*"), ("access-control-allow-methods", "get"), ("access-control-allow-methods", "get, post, options"),
  ("access-control-allow-methods", "options"), ("access-control-expose-headers", "content-length"), ("access-control-request-headers", "content-type"),
  ("access-control-request-method", "get"), ("access-control-request-method", "post"), ("alt-svc", "clear"),
  ("authorization", ""), ("content-security-policy", "script-src 'none'; object-src 'none'; base-uri 'none'"), ("early-data", "1"),
  ("expect-ct", ""), ("forwarded", ""), ("if-range", ""),
  ("origin", ""), ("purpose", "prefetch"), ("server", ""),
  ("timing-allow-origin", "*"), ("upgrade-insecure-requests", "1"), ("user-agent", ""),
  ("x-forwarded-for", ""), ("x-frame-options", "deny"), ("x-frame-options", "sameorigin")]

def staticEntry (i : Nat) : Option (String × String) := staticTable[i]?

/-- UTF-8 bytes of a string (static-table materialization). -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## Emitting into the store -/

/-- Append `bs` to the sidecar arena and register a view entry addressing
exactly the appended range (the offset carries the sidecar discriminant).
`none` iff the append would exhaust the sidecar's `2^31` offset space —
the check that keeps every emitted offset/length exact in `UInt32`. -/
def emitSidecar (st : Store) (tag : NameTag) (bs : Bytes) :
    Option (Store × Entry) :=
  if sidecarBaseNat ≤ st.sidecar.size + bs.length then none
  else
    let e : Entry :=
      { tag := tag
        off := UInt32.ofNat (sidecarBaseNat + st.sidecar.size)
        len := UInt32.ofNat bs.length }
    some ((st.appendSidecar bs.toArray).pushEntry e, e)

theorem emitSidecar_eq (st : Store) (tag : NameTag) (bs : Bytes)
    (st' : Store) (e : Entry) (h : emitSidecar st tag bs = some (st', e)) :
    st' = (st.appendSidecar bs.toArray).pushEntry e ∧
      st.sidecar.size + bs.length < sidecarBaseNat := by
  unfold emitSidecar at h
  split at h
  · exact absurd h (by simp)
  · rename_i hlt
    cases h
    exact ⟨rfl, by omega⟩

/-- The emitted entry is in-bounds **by construction**: the size guard keeps
the offset arithmetic exact, the offset lands in the sidecar address space,
and the referenced range is exactly the appended block. -/
theorem emitSidecar_inBounds (st : Store) (tag : NameTag) (bs : Bytes)
    (st' : Store) (e : Entry) (h : emitSidecar st tag bs = some (st', e)) :
    (st.appendSidecar bs.toArray).InBounds e := by
  unfold emitSidecar at h
  split at h
  · exact absurd h (by simp)
  · rename_i hlt
    injection h with h
    injection h with h₁ h₂
    subst h₂
    have hsz : st.sidecar.size + bs.length < sidecarBaseNat := by omega
    have hoff : (UInt32.ofNat (sidecarBaseNat + st.sidecar.size)).toNat
        = sidecarBaseNat + st.sidecar.size := by
      show (sidecarBaseNat + st.sidecar.size) % 2 ^ 32
          = sidecarBaseNat + st.sidecar.size
      unfold sidecarBaseNat at *
      omega
    have hlen : (UInt32.ofNat bs.length).toNat = bs.length := by
      show bs.length % 2 ^ 32 = bs.length
      unfold sidecarBaseNat at hsz
      omega
    have hside : Entry.inSidecar
        { tag := tag
          off := UInt32.ofNat (sidecarBaseNat + st.sidecar.size)
          len := UInt32.ofNat bs.length } = true := by
      unfold Entry.inSidecar
      simp only [hoff, decide_eq_true_eq]
      unfold isSidecarAddr
      omega
    unfold Store.InBounds Store.arenaOf Entry.physOff
    simp only [hside, if_true, hoff, hlen]
    unfold Store.appendSidecar
    simp only [Array.size_append]
    have hta : bs.toArray.size = bs.length := rfl
    omega

/-- **Wf preservation for one emit**: pushing the constructed entry after the
sidecar append preserves store well-formedness. -/
theorem emitSidecar_wf (st : Store) (tag : NameTag) (bs : Bytes)
    (st' : Store) (e : Entry) (hwf : st.Wf)
    (h : emitSidecar st tag bs = some (st', e)) : st'.Wf := by
  have heq := (emitSidecar_eq st tag bs st' e h).1
  have hib := emitSidecar_inBounds st tag bs st' e h
  rw [heq]
  exact Store.wf_pushEntry _ (Store.wf_appendSidecar st hwf _) hib

/-- Emitting never touches the main arena. -/
theorem emitSidecar_main (st : Store) (tag : NameTag) (bs : Bytes)
    (st' : Store) (e : Entry) (h : emitSidecar st tag bs = some (st', e)) :
    st'.main = st.main := by
  rw [(emitSidecar_eq st tag bs st' e h).1]
  rfl

/-! ## Field lines -/

/-- A decoded (non-pseudo) field: name and value view entries. -/
structure FieldLine where
  name : Entry
  value : Entry
deriving Repr

/-- The four request pseudo-headers the decode routes into dedicated fields;
other pseudo names (e.g. `:status`) fall through as regular fields — the RFC
leaves that routing to the consumer. -/
inductive PseudoKind where
  | method | path | scheme | authority
deriving Repr, DecidableEq

/-- Pseudo-header values: the name is implied by the field, so only the
value entry is registered. -/
structure Pseudo where
  method : Option Entry := none
  path : Option Entry := none
  scheme : Option Entry := none
  authority : Option Entry := none
deriving Repr

def Pseudo.set (p : Pseudo) (k : PseudoKind) (e : Entry) : Pseudo :=
  match k with
  | .method => { p with method := some e }
  | .path => { p with path := some e }
  | .scheme => { p with scheme := some e }
  | .authority => { p with authority := some e }

/-- What one decoded field line contributes. -/
inductive LineOut where
  | pseudo (k : PseudoKind) (value : Entry)
  | field (fl : FieldLine)

def classifyName (name : Bytes) : Option PseudoKind :=
  if name = strBytes ":method" then some .method
  else if name = strBytes ":path" then some .path
  else if name = strBytes ":scheme" then some .scheme
  else if name = strBytes ":authority" then some .authority
  else none

/-- Emit one decoded field into the store: pseudo-headers register only a
value entry; regular fields register a name entry then a value entry. -/
def emitField (st : Store) (name value : Bytes) :
    Except Err (Store × LineOut) :=
  match classifyName name with
  | some k =>
    match emitSidecar st .headerValue value with
    | some (st', ve) => .ok (st', .pseudo k ve)
    | none => .error .tooLarge
  | none =>
    match emitSidecar st .headerName name with
    | none => .error .tooLarge
    | some (st₁, ne) =>
      match emitSidecar st₁ .headerValue value with
      | none => .error .tooLarge
      | some (st₂, ve) => .ok (st₂, .field ⟨ne, ve⟩)

theorem emitField_wf (st : Store) (name value : Bytes) (st' : Store)
    (out : LineOut) (hwf : st.Wf)
    (h : emitField st name value = .ok (st', out)) : st'.Wf := by
  unfold emitField at h
  split at h
  · split at h
    · rename_i hemit
      cases h
      exact emitSidecar_wf _ _ _ _ _ hwf hemit
    · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i st₁ ne hemit₁
      split at h
      · exact absurd h (by simp)
      · rename_i st₂ ve hemit₂
        cases h
        exact emitSidecar_wf _ _ _ _ _
          (emitSidecar_wf _ _ _ _ _ hwf hemit₁) hemit₂

theorem emitField_main (st : Store) (name value : Bytes) (st' : Store)
    (out : LineOut) (h : emitField st name value = .ok (st', out)) :
    st'.main = st.main := by
  unfold emitField at h
  split at h
  · split at h
    · rename_i hemit
      cases h
      exact emitSidecar_main _ _ _ _ _ hemit
    · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i st₁ ne hemit₁
      split at h
      · exact absurd h (by simp)
      · rename_i st₂ ve hemit₂
        cases h
        rw [emitSidecar_main _ _ _ _ _ hemit₂,
          emitSidecar_main _ _ _ _ _ hemit₁]

/-! ## The QPACK dynamic table (RFC 9204 §3.2)

The deployed dynamic table state the field-section decode resolves references
against. Entries are held NEWEST-FIRST (head = most recently inserted). Insertion
prepends the new entry and evicts the OLDEST entries — a suffix of the list —
until the table fits its maximum size (§3.2.2). A field section's Base
(reconstructed from the section prefix, §4.5.1) drives the RELATIVE (§3.2.5) and
POST-BASE (§3.2.6) index resolutions.

Insertions are performed out of band (by encoder-stream instructions, §4.3); the
field-section decode only READS this table — it is supplied as decode input. The
`CORRECTNESS` theory (`QpackDynCorrect.lean`) proves insert/evict/resolve against
exactly these definitions and binds them to this deployed decoder. -/

/-- A dynamic-table entry: a (name, value) pair of octet strings. -/
abbrev Pair := Bytes × Bytes

/-- RFC 9204 §3.2.1: the size of an entry is its name length plus its value
length plus 32. -/
def entrySize (p : Pair) : Nat := p.1.length + p.2.length + 32

/-- RFC 9204 §3.2.1: the size of the dynamic table is the sum of its entry
sizes. -/
def tableSize : List Pair → Nat
  | [] => 0
  | p :: rest => entrySize p + tableSize rest

@[simp] theorem tableSize_nil : tableSize [] = 0 := rfl

theorem tableSize_cons (p : Pair) (es : List Pair) :
    tableSize (p :: es) = entrySize p + tableSize es := rfl

/-- The QPACK dynamic table: entries NEWEST-FIRST, the number of entries ever
inserted (`insertCount`, so the newest has absolute index `insertCount - 1`,
§3.2.4), the CURRENT capacity in octets (`maxSize`, §3.2.2 — changed by the
§4.3.1 Set Dynamic Table Capacity instruction, initially zero per §3.2.3), and
the ADVERTISED bound `maxCapacity` (the decoder's
`SETTINGS_QPACK_MAX_TABLE_CAPACITY`, §3.2.3). The two are distinct on the
wire: `MaxEntries` of the §4.5.1.1 Required-Insert-Count arithmetic is
`maxCapacity / 32` (the SETTINGS value), while insertion/eviction budgets use
the current `maxSize`; an instruction raising `maxSize` above `maxCapacity` is
an encoder-stream error (§4.3.1). -/
structure DynTable where
  entries : List Pair
  insertCount : Nat
  maxSize : Nat
  maxCapacity : Nat

/-- The empty dynamic table: no entries, no inserts, zero capacity, nothing
advertised. A connection that has processed no encoder instructions resolves
every dynamic reference to `none` against this table. -/
def DynTable.empty : DynTable := ⟨[], 0, 0, 0⟩

/-- The dynamic table of a decoder that advertised
`SETTINGS_QPACK_MAX_TABLE_CAPACITY = cap` and has processed no encoder
instructions yet: still zero CURRENT capacity (§3.2.3 — the encoder must send
Set Dynamic Table Capacity first), but §4.5.1.1 arithmetic runs at
`MaxEntries = cap / 32`. -/
def DynTable.advertised (cap : Nat) : DynTable := ⟨[], 0, 0, cap⟩

/-- RFC 9204 §3.2.4: resolve an ABSOLUTE index. The newest entry (list head) has
absolute index `insertCount - 1`, so absolute index `a` sits at list position
`insertCount - 1 - a`. An index never inserted (`a ≥ insertCount`) or already
evicted resolves to `none`. -/
def DynTable.byAbs (t : DynTable) (a : Nat) : Option Pair :=
  if a < t.insertCount then t.entries[t.insertCount - 1 - a]? else none

/-- RFC 9204 §3.2.5 / §4.5.2: resolve a RELATIVE index against a field section's
`base`. Relative index `r` (with `r < base`) names absolute index `base - 1 - r`. -/
def DynTable.byRelative (t : DynTable) (base r : Nat) : Option Pair :=
  if r < base then t.byAbs (base - 1 - r) else none

/-- RFC 9204 §3.2.6 / §4.5.3: resolve a POST-BASE index against a field section's
`base`. Post-base index `p` names absolute index `base + p`. -/
def DynTable.byPostBase (t : DynTable) (base p : Nat) : Option Pair :=
  t.byAbs (base + p)

/-- Keep the newest entries (a prefix, scanning from the head) whose cumulative
size fits `budget`, dropping the first entry that would overflow it and every
older entry after it. Realizes RFC 9204 §3.2.2 eviction. -/
def keepFit : List Pair → Nat → List Pair
  | [], _ => []
  | e :: rest, budget =>
    if entrySize e ≤ budget then e :: keepFit rest (budget - entrySize e) else []

/-- RFC 9204 §3.2.2, §3.2.4: insert `(n, v)` as the new newest entry. If it fits
the maximum, evict the oldest entries so the retained old entries plus the new
one stay within the maximum, prepend the new entry, and advance the insert count.
If it is larger than the maximum, nothing is stored. -/
def DynTable.add (t : DynTable) (n v : Bytes) : DynTable :=
  if entrySize (n, v) ≤ t.maxSize then
    { entries := (n, v) :: keepFit t.entries (t.maxSize - entrySize (n, v))
      insertCount := t.insertCount + 1
      maxSize := t.maxSize
      maxCapacity := t.maxCapacity }
  else
    { entries := []
      insertCount := t.insertCount
      maxSize := t.maxSize
      maxCapacity := t.maxCapacity }

/-- Eviction only removes entries from the OLD end: the retained entries are a
prefix of the original list. -/
theorem keepFit_prefix : ∀ (es : List Pair) (budget : Nat),
    ∃ suf, keepFit es budget ++ suf = es
  | [], _ => ⟨[], rfl⟩
  | e :: rest, budget => by
    simp only [keepFit]
    by_cases h : entrySize e ≤ budget
    · simp only [h, if_true]
      obtain ⟨suf, hsuf⟩ := keepFit_prefix rest (budget - entrySize e)
      exact ⟨suf, by rw [List.cons_append, hsuf]⟩
    · simp only [h, if_false]
      exact ⟨e :: rest, rfl⟩

/-- Eviction keeps the retained entries within the budget. -/
theorem keepFit_size : ∀ (es : List Pair) (budget : Nat),
    tableSize (keepFit es budget) ≤ budget
  | [], budget => by simp [keepFit]
  | e :: rest, budget => by
    simp only [keepFit]
    by_cases h : entrySize e ≤ budget
    · simp only [h, if_true, tableSize_cons]
      have ih := keepFit_size rest (budget - entrySize e)
      omega
    · simp only [h, if_false, tableSize_nil]
      exact Nat.zero_le _

/-! ## Decoding one field line (§4.5) -/

/-- Decode one field-line representation from the head of `bs`, resolving any
dynamic reference against `dyn` and the section `base`.

Taxonomy by the top bits of the first byte (RFC 9204 §4.5.2–§4.5.6):

* `1 T idx(6)` — indexed field line; `T=1` static, `T=0` dynamic (relative
  index against `base`, §3.2.5).
* `01 N T idx(4)` — literal with name reference; `T=1` static name, `T=0`
  dynamic name (relative index).
* `001 N H len(3)` — literal with literal name.
* `0001 idx(4)` — indexed, post-base (dynamic, §3.2.6).
* `0000 N idx(3)` — literal with post-base name reference (dynamic).

A dynamic reference that resolves to `none` (out of range for the supplied
table) fails with `Err.dynamicUnsupported`. Returns the grown store, the line's
contribution, and bytes consumed. -/
def decodeOneLine (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (dyn : DynTable := DynTable.empty) (base : Nat := 0) :
    Except Err (Store × LineOut × Nat) :=
  match bs with
  | [] => .error .truncated
  | b :: rest =>
    if 0x80 ≤ b.toNat then
      -- Indexed field line (§4.5.2)
      if 0x40 ≤ b.toNat % 0x80 then
        -- T=1 static
        match decPrefixInt 6 b rest with
        | none => .error .truncated
        | some (idx, n) =>
          match staticEntry idx with
          | none => .error .staticIndex
          | some (name, value) =>
            match emitField st (strBytes name) (strBytes value) with
            | .error e => .error e
            | .ok (st', out) => .ok (st', out, 1 + n)
      else
        -- T=0 dynamic, relative index (§3.2.5)
        match decPrefixInt 6 b rest with
        | none => .error .truncated
        | some (idx, n) =>
          match dyn.byRelative base idx with
          | none => .error .dynamicUnsupported
          | some (name, value) =>
            match emitField st name value with
            | .error e => .error e
            | .ok (st', out) => .ok (st', out, 1 + n)
    else if 0x40 ≤ b.toNat then
      -- Literal field line with name reference (§4.5.4)
      if 0x10 ≤ b.toNat % 0x20 then
        -- T=1 static name
        match decPrefixInt 4 b rest with
        | none => .error .truncated
        | some (idx, n) =>
          match staticEntry idx with
          | none => .error .staticIndex
          | some (name, _) =>
            match rest.drop n with
            | [] => .error .truncated
            | vb :: vrest =>
              match decStr hd 7 vb vrest with
              | .error e => .error e
              | .ok (value, m) =>
                if utf8Ok value then
                  match emitField st (strBytes name) value with
                  | .error e => .error e
                  | .ok (st', out) => .ok (st', out, 1 + n + 1 + m)
                else .error .nonUtf8
      else
        -- T=0 dynamic name, relative index (§3.2.5)
        match decPrefixInt 4 b rest with
        | none => .error .truncated
        | some (idx, n) =>
          match dyn.byRelative base idx with
          | none => .error .dynamicUnsupported
          | some (name, _) =>
            match rest.drop n with
            | [] => .error .truncated
            | vb :: vrest =>
              match decStr hd 7 vb vrest with
              | .error e => .error e
              | .ok (value, m) =>
                if utf8Ok value then
                  match emitField st name value with
                  | .error e => .error e
                  | .ok (st', out) => .ok (st', out, 1 + n + 1 + m)
                else .error .nonUtf8
    else if 0x20 ≤ b.toNat then
      -- Literal field line with literal name (§4.5.6)
      match decStr hd 3 b rest with
      | .error e => .error e
      | .ok (name, n) =>
        if utf8Ok name then
          match rest.drop n with
          | [] => .error .truncated
          | vb :: vrest =>
            match decStr hd 7 vb vrest with
            | .error e => .error e
            | .ok (value, m) =>
              if utf8Ok value then
                match emitField st name value with
                | .error e => .error e
                | .ok (st', out) => .ok (st', out, 1 + n + 1 + m)
              else .error .nonUtf8
        else .error .nonUtf8
    else if 0x10 ≤ b.toNat then
      -- Indexed field line, post-base (§4.5.3): 0001 idx(4)
      match decPrefixInt 4 b rest with
      | none => .error .truncated
      | some (idx, n) =>
        match dyn.byPostBase base idx with
        | none => .error .dynamicUnsupported
        | some (name, value) =>
          match emitField st name value with
          | .error e => .error e
          | .ok (st', out) => .ok (st', out, 1 + n)
    else
      -- Literal field line with post-base name reference (§4.5.5): 0000 N idx(3)
      match decPrefixInt 3 b rest with
      | none => .error .truncated
      | some (idx, n) =>
        match dyn.byPostBase base idx with
        | none => .error .dynamicUnsupported
        | some (name, _) =>
          match rest.drop n with
          | [] => .error .truncated
          | vb :: vrest =>
            match decStr hd 7 vb vrest with
            | .error e => .error e
            | .ok (value, m) =>
              if utf8Ok value then
                match emitField st name value with
                | .error e => .error e
                | .ok (st', out) => .ok (st', out, 1 + n + 1 + m)
              else .error .nonUtf8

/-- **Progress + boundedness** for one field line: at least one byte, never
more than the input. -/
theorem decodeOneLine_consumed (hd : HuffmanDecoder) (st : Store)
    (bs : Bytes) (dyn : DynTable) (base : Nat) (st' : Store) (out : LineOut) (n : Nat)
    (h : decodeOneLine hd st bs dyn base = .ok (st', out, n)) :
    1 ≤ n ∧ n ≤ bs.length := by
  unfold decodeOneLine at h
  split at h
  · exact absurd h (by simp)
  · rename_i b rest
    -- helper: `.ok` from an index-only representation consuming `1 + n₁`
    have idxCase : ∀ (p : Nat) (idx n₁ : Nat),
        decPrefixInt p b rest = some (idx, n₁) → n = 1 + n₁ →
        1 ≤ n ∧ n ≤ (b :: rest).length := by
      intro p idx n₁ hpi hn
      have hn₁ := decPrefixInt_consumed p b rest idx n₁ hpi
      subst hn; simp only [List.length_cons]; omega
    -- helper: `.ok` from a name-ref/literal representation consuming `1 + n₁ + 1 + m`
    have litCase : ∀ (p : Nat) (idx n₁ : Nat) (vb : UInt8) (vrest value : Bytes) (m : Nat),
        decPrefixInt p b rest = some (idx, n₁) → rest.drop n₁ = vb :: vrest →
        decStr hd 7 vb vrest = .ok (value, m) → n = 1 + n₁ + 1 + m →
        1 ≤ n ∧ n ≤ (b :: rest).length := by
      intro p idx n₁ vb vrest value m hpi hdrop hstr hn
      have hn₁ := decPrefixInt_consumed p b rest idx n₁ hpi
      have hlen : rest.length - n₁ = vrest.length + 1 := by
        have := congrArg List.length hdrop
        simp only [List.length_drop, List.length_cons] at this
        omega
      have hm := decStr_consumed hd 7 vb vrest value m hstr
      subst hn; simp only [List.length_cons]; omega
    split at h
    · -- indexed field line (§4.5.2)
      split at h
      · -- T=1 static
        split at h
        · exact absurd h (by simp)
        · rename_i idx n₁ hpi
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · cases h; exact idxCase 6 idx n₁ hpi rfl
      · -- T=0 dynamic (relative)
        split at h
        · exact absurd h (by simp)
        · rename_i idx n₁ hpi
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · cases h; exact idxCase 6 idx n₁ hpi rfl
    · split at h
      · -- literal with name reference (§4.5.4)
        split at h
        · -- T=1 static name
          split at h
          · exact absurd h (by simp)
          · rename_i idx n₁ hpi
            split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · rename_i vb vrest hdrop
                split at h
                · exact absurd h (by simp)
                · rename_i value m hstr
                  split at h
                  · split at h
                    · exact absurd h (by simp)
                    · cases h; exact litCase 4 idx n₁ vb vrest value m hpi hdrop hstr rfl
                  · exact absurd h (by simp)
        · -- T=0 dynamic name
          split at h
          · exact absurd h (by simp)
          · rename_i idx n₁ hpi
            split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · rename_i vb vrest hdrop
                split at h
                · exact absurd h (by simp)
                · rename_i value m hstr
                  split at h
                  · split at h
                    · exact absurd h (by simp)
                    · cases h; exact litCase 4 idx n₁ vb vrest value m hpi hdrop hstr rfl
                  · exact absurd h (by simp)
      · split at h
        · -- literal with literal name (§4.5.6)
          split at h
          · exact absurd h (by simp)
          · rename_i name n₁ hstr₁
            have hn₁ := decStr_consumed hd 3 b rest name n₁ hstr₁
            split at h
            · split at h
              · exact absurd h (by simp)
              · rename_i vb vrest hdrop
                have hlen : rest.length - n₁ = vrest.length + 1 := by
                  have := congrArg List.length hdrop
                  simp only [List.length_drop, List.length_cons] at this
                  omega
                split at h
                · exact absurd h (by simp)
                · rename_i value m hstr₂
                  have hm := decStr_consumed hd 7 vb vrest value m hstr₂
                  split at h
                  · split at h
                    · exact absurd h (by simp)
                    · cases h; simp only [List.length_cons]; omega
                  · exact absurd h (by simp)
            · exact absurd h (by simp)
        · split at h
          · -- indexed post-base (§4.5.3)
            split at h
            · exact absurd h (by simp)
            · rename_i idx n₁ hpi
              split at h
              · exact absurd h (by simp)
              · split at h
                · exact absurd h (by simp)
                · cases h; exact idxCase 4 idx n₁ hpi rfl
          · -- literal with post-base name reference (§4.5.5)
            split at h
            · exact absurd h (by simp)
            · rename_i idx n₁ hpi
              split at h
              · exact absurd h (by simp)
              · split at h
                · exact absurd h (by simp)
                · rename_i vb vrest hdrop
                  split at h
                  · exact absurd h (by simp)
                  · rename_i value m hstr
                    split at h
                    · split at h
                      · exact absurd h (by simp)
                      · cases h; exact litCase 3 idx n₁ vb vrest value m hpi hdrop hstr rfl
                    · exact absurd h (by simp)

/-- One field line preserves store well-formedness. -/
theorem decodeOneLine_wf (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (dyn : DynTable) (base : Nat) (st' : Store) (out : LineOut) (n : Nat) (hwf : st.Wf)
    (h : decodeOneLine hd st bs dyn base = .ok (st', out, n)) : st'.Wf := by
  unfold decodeOneLine at h
  repeat' split at h
  all_goals cases h
  all_goals exact emitField_wf _ _ _ _ _ hwf (by assumption)

/-- One field line never touches the main arena. -/
theorem decodeOneLine_main (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (dyn : DynTable) (base : Nat) (st' : Store) (out : LineOut) (n : Nat)
    (h : decodeOneLine hd st bs dyn base = .ok (st', out, n)) :
    st'.main = st.main := by
  unfold decodeOneLine at h
  repeat' split at h
  all_goals cases h
  all_goals exact emitField_main _ _ _ _ _ (by assumption)

/-! ## The field-line loop and the section prefix (§4.5.1) -/

set_option linter.unusedVariables false in
/-- Decode all field lines of a section, resolving dynamic references against
`dyn` and the section `base`. Termination is `decodeOneLine_consumed` (every line
eats at least one byte; the discriminant name `h` is used only by
`decreasing_by`). -/
def decodeLines (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (pseudo : Pseudo) (acc : List FieldLine)
    (dyn : DynTable := DynTable.empty) (base : Nat := 0) :
    Except Err (Store × Pseudo × List FieldLine) :=
  match bs with
  | [] => .ok (st, pseudo, acc.reverse)
  | b :: rest =>
    match h : decodeOneLine hd st (b :: rest) dyn base with
    | .error e => .error e
    | .ok (st', out, n) =>
      decodeLines hd st' ((b :: rest).drop n)
        (match out with
         | .pseudo k ve => pseudo.set k ve
         | .field _ => pseudo)
        (match out with
         | .pseudo _ _ => acc
         | .field fl => fl :: acc)
        dyn base
termination_by bs.length
decreasing_by
  all_goals
    have := decodeOneLine_consumed hd st (b :: rest) dyn base st' out n h
    simp only [List.length_drop, List.length_cons]
    omega

/-- The loop preserves well-formedness. -/
theorem decodeLines_wf (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (pseudo : Pseudo) (acc : List FieldLine) (dyn : DynTable) (base : Nat) :
    ∀ r : Store × Pseudo × List FieldLine, st.Wf →
      decodeLines hd st bs pseudo acc dyn base = .ok r → r.1.Wf := by
  induction st, bs, pseudo, acc, dyn, base using decodeLines.induct hd with
  | case1 st pseudo acc dyn base =>
    intro r hwf h
    simp only [decodeLines] at h
    cases h
    exact hwf
  | case2 st pseudo acc dyn base b rest e hline =>
    intro r hwf h
    simp only [decodeLines] at h
    split at h
    · cases h
    · rename_i st' out n heq
      rw [hline] at heq
      cases heq
  | case3 st pseudo acc dyn base b rest st' out n hline ih =>
    intro r hwf h
    simp only [decodeLines] at h
    split at h
    · rename_i e heq
      rw [hline] at heq
      cases heq
    · rename_i st'' out'' n'' heq
      rw [hline] at heq
      cases heq
      exact ih r (decodeOneLine_wf _ _ _ _ _ _ _ _ hwf hline) h

/-- The loop never touches the main arena. -/
theorem decodeLines_main (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (pseudo : Pseudo) (acc : List FieldLine) (dyn : DynTable) (base : Nat) :
    ∀ r : Store × Pseudo × List FieldLine,
      decodeLines hd st bs pseudo acc dyn base = .ok r → r.1.main = st.main := by
  induction st, bs, pseudo, acc, dyn, base using decodeLines.induct hd with
  | case1 st pseudo acc dyn base =>
    intro r h
    simp only [decodeLines] at h
    cases h
    rfl
  | case2 st pseudo acc dyn base b rest e hline =>
    intro r h
    simp only [decodeLines] at h
    split at h
    · cases h
    · rename_i st' out n heq
      rw [hline] at heq
      cases heq
  | case3 st pseudo acc dyn base b rest st' out n hline ih =>
    intro r h
    simp only [decodeLines] at h
    split at h
    · rename_i e heq
      rw [hline] at heq
      cases heq
    · rename_i st'' out'' n'' heq
      rw [hline] at heq
      cases heq
      rw [ih r h, decodeOneLine_main _ _ _ _ _ _ _ _ hline]

/-- A decoded field section: the grown store, the routed pseudo-headers,
and the regular fields in wire order. -/
structure Decoded where
  store : Store
  pseudo : Pseudo
  fields : List FieldLine

/-- **Required Insert Count reconstruction — the full RFC 9204 §4.5.1.1
algorithm**, wrap included. `maxEntries` is `MaxTableCapacity / 32`,
`totalInserts` the decoder's total number of inserts so far. An
`encRic = 0` means no dynamic references. A nonzero `encRic` outside the
`2 * maxEntries` window, or one that reconstructs to an impossible value,
is a decoding error (`prefixInvalid`) — the RFC's "MUST treat as error"
cases. -/
def reconstructRic (maxEntries totalInserts encRic : Nat) : Except Err Nat :=
  if encRic = 0 then .ok 0
  else if 2 * maxEntries < encRic then .error .prefixInvalid
  else if totalInserts + maxEntries <
      (totalInserts + maxEntries) / (2 * maxEntries) * (2 * maxEntries) + encRic - 1 then
    if (totalInserts + maxEntries) / (2 * maxEntries) * (2 * maxEntries) + encRic - 1
        ≤ 2 * maxEntries then .error .prefixInvalid
    else .ok ((totalInserts + maxEntries) / (2 * maxEntries) * (2 * maxEntries) + encRic - 1
              - 2 * maxEntries)
  else if (totalInserts + maxEntries) / (2 * maxEntries) * (2 * maxEntries) + encRic - 1 = 0 then
    .error .prefixInvalid
  else .ok ((totalInserts + maxEntries) / (2 * maxEntries) * (2 * maxEntries) + encRic - 1)

@[simp] theorem reconstructRic_zero (me ti : Nat) : reconstructRic me ti 0 = .ok 0 := by
  unfold reconstructRic; simp

/-- The section Base (RFC 9204 §4.5.1.2) from the reconstructed Required Insert
Count, the Delta Base first byte `signByte` (its top bit is the sign S), and the
Delta Base magnitude. `S = 0` gives `ric + deltaBase`; `S = 1` gives
`ric - deltaBase - 1`, and a Delta Base that would make the Base negative
(`deltaBase ≥ ric`, which includes every `S = 1` prefix with `ric = 0`) is a
decoding error — the §4.5.1.2 "MUST treat as error" case. -/
def reconstructBase (ric : Nat) (signByte : UInt8) (deltaBase : Nat) : Except Err Nat :=
  if signByte.toNat / 2 ^ 7 % 2 = 1 then
    if deltaBase < ric then .ok (ric - deltaBase - 1) else .error .prefixInvalid
  else .ok (ric + deltaBase)

@[simp] theorem reconstructBase_zeroByte (ric db : Nat) :
    reconstructBase ric 0x00 db = .ok (ric + db) := by
  unfold reconstructBase
  rw [if_neg (by decide)]

/-! ### §4.5.1.1 round-trip correctness

The encoder transmits `EncodedInsertCount = ReqInsertCount mod (2 * MaxEntries)
+ 1`; the receiver's reconstruction must recover the exact `ReqInsertCount`
whenever it lies in the valid window `(MaxValue - FullRange, MaxValue]` around
the decoder's insert total. `reconstructRic_correct` proves the deployed
reconstruction is that inverse — for every `maxEntries`, `totalInserts` and
in-window `ric`, not just the non-wrapping regime. -/

private theorem div_eq_of_between (n F q : Nat) (hF : 0 < F)
    (h1 : F * q ≤ n) (h2 : n < F * (q + 1)) : n / F = q := by
  have h1' : q * F ≤ n := by rw [Nat.mul_comm]; exact h1
  have h2' : n < (q + 1) * F := by rw [Nat.mul_comm] at h2; exact h2
  have h5 : q ≤ n / F := (Nat.le_div_iff_mul_le hF).mpr h1'
  have h6 : n / F < q + 1 := (Nat.div_lt_iff_lt_mul hF).mpr h2'
  omega

/-- **Encode/decode inverse for the Required Insert Count (RFC 9204 §4.5.1.1).**
For a positive `ric` within the valid window around the decoder state —
`ric ≤ totalInserts + maxEntries < ric + 2 * maxEntries` — reconstructing the
encoder's `ric % (2 * maxEntries) + 1` recovers exactly `ric`. -/
theorem reconstructRic_correct (me ti ric : Nat) (hme : 0 < me) (hric : 0 < ric)
    (hle : ric ≤ ti + me) (hwin : ti + me < ric + 2 * me) :
    reconstructRic me ti (ric % (2 * me) + 1) = .ok ric := by
  have hF : 0 < 2 * me := by omega
  have hmod : ric % (2 * me) < 2 * me := Nat.mod_lt _ hF
  have hdm := Nat.div_add_mod ric (2 * me)
  -- abbreviations: q = ric / F, r = ric % F, F = 2 * me
  by_cases hcase : ti + me < 2 * me * (ric / (2 * me) + 1)
  · -- no borrow: (ti + me) / F = ric / F, the reconstruction lands on ric directly
    have hq : (ti + me) / (2 * me) = ric / (2 * me) :=
      div_eq_of_between (ti + me) (2 * me) (ric / (2 * me)) hF (by omega) hcase
    unfold reconstructRic
    rw [if_neg (by omega), if_neg (by omega), hq]
    have hW : ric / (2 * me) * (2 * me) = 2 * me * (ric / (2 * me)) := Nat.mul_comm _ _
    rw [hW]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1
    all_goals omega
  · -- borrow: (ti + me) / F = ric / F + 1, the reconstruction overshoots by F and subtracts
    have hup : ti + me < 2 * me * (ric / (2 * me) + 1 + 1) := by
      have hexp : 2 * me * (ric / (2 * me) + 1 + 1)
          = 2 * me * (ric / (2 * me)) + 2 * me + 2 * me := by
        rw [Nat.mul_succ, Nat.mul_succ]
      omega
    have hq : (ti + me) / (2 * me) = ric / (2 * me) + 1 :=
      div_eq_of_between (ti + me) (2 * me) (ric / (2 * me) + 1) hF (by omega) hup
    unfold reconstructRic
    rw [if_neg (by omega), if_neg (by omega), hq]
    have hW : (ric / (2 * me) + 1) * (2 * me)
        = 2 * me * (ric / (2 * me)) + 2 * me := by
      rw [Nat.succ_mul, Nat.mul_comm (ric / (2 * me)) (2 * me)]
    rw [hW]
    rw [if_pos (by omega), if_neg (by omega)]
    congr 1
    all_goals omega

/-- **Base reconstruction is the §4.5.1.2 inverse**: for `base ≥ ric` the
sign-0 encoding recovers it; for `base < ric` the sign-1 encoding recovers it. -/
theorem reconstructBase_correct_pos (ric base : Nat) (sb : UInt8)
    (hsb : sb.toNat / 2 ^ 7 % 2 ≠ 1) (h : ric ≤ base) :
    reconstructBase ric sb (base - ric) = .ok base := by
  unfold reconstructBase
  rw [if_neg hsb]
  congr 1
  omega

theorem reconstructBase_correct_neg (ric base : Nat) (sb : UInt8)
    (hsb : sb.toNat / 2 ^ 7 % 2 = 1) (h : base < ric) :
    reconstructBase ric sb (ric - base - 1) = .ok base := by
  unfold reconstructBase
  rw [if_pos hsb, if_pos (by omega)]
  congr 1
  omega

/-- Decode an encoded field section (§4.5.1) into the store, resolving dynamic
references against `dyn`.

The section prefix is the encoded Required Insert Count (8-bit prefix) and the
Delta Base (7-bit prefix + sign S). `reconstructRic` runs the full §4.5.1.1
reconstruction (window check + wrap) against the supplied table's capacity and
insert total; `reconstructBase` rebuilds the Base (§4.5.1.2, negative-Base
check). A Required Insert Count beyond the table's insert total names entries
the decoder has not received — unresolvable in a synchronous decode
(`dynamicUnsupported`, the §2.1.2 blocked-stream condition). RELATIVE and
POST-BASE references then resolve against `dyn` and the Base. -/
def decodeFieldSection (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (dyn : DynTable := DynTable.empty) : Except Err Decoded :=
  match bs with
  | [] => .error .truncated
  | b0 :: r0 =>
    match decPrefixInt 8 b0 r0 with
    | none => .error .truncated
    | some (encRic, n0) =>
      match r0.drop n0 with
      | [] => .error .truncated
      | b1 :: r1 =>
        match decPrefixInt 7 b1 r1 with
        | none => .error .truncated
        | some (deltaBase, n1) =>
          match reconstructRic (dyn.maxCapacity / 32) dyn.insertCount encRic with
          | .error e => .error e
          | .ok ric =>
            match reconstructBase ric b1 deltaBase with
            | .error e => .error e
            | .ok base =>
              if dyn.insertCount < ric then .error .dynamicUnsupported
              else
                match decodeLines hd st (r1.drop n1) {} [] dyn base with
                | .error e => .error e
                | .ok (st', pseudo, fields) => .ok ⟨st', pseudo, fields⟩

/-- **The headline theorem — Wf preservation** (the H3 analogue of the H1
parser's `Wf` discharge): decoding a field section into a well-formed store
yields a well-formed store, for every Huffman-decoder behavior and every
input. -/
theorem decodeFieldSection_wf_dyn (hd : HuffmanDecoder) (st : Store)
    (bs : Bytes) (dyn : DynTable) (r : Decoded) (hwf : st.Wf)
    (h : decodeFieldSection hd st bs dyn = .ok r) : r.store.Wf := by
  unfold decodeFieldSection at h
  repeat' split at h
  all_goals cases h
  all_goals exact decodeLines_wf _ _ _ _ _ _ _ _ hwf (by assumption)

/-- The default-table (no dynamic state) instance of
`decodeFieldSection_wf_dyn`. -/
theorem decodeFieldSection_wf (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (r : Decoded) (hwf : st.Wf) (h : decodeFieldSection hd st bs = .ok r) :
    r.store.Wf :=
  decodeFieldSection_wf_dyn hd st bs DynTable.empty r hwf h

/-- Corollary, in emitted-entry form: **every view entry of the decoded
store — the emitted ones included — is in-bounds of the arena it
addresses.** For every dynamic-table state. -/
theorem decodeFieldSection_entries_inBounds (hd : HuffmanDecoder)
    (st : Store) (bs : Bytes) (dyn : DynTable) (r : Decoded) (hwf : st.Wf)
    (h : decodeFieldSection hd st bs dyn = .ok r) :
    ∀ e ∈ r.store.entries, r.store.InBounds e :=
  decodeFieldSection_wf_dyn hd st bs dyn r hwf h

/-- The decode only appends to the sidecar: the main arena — the wire
bytes — is preserved byte-for-byte. For every dynamic-table state. -/
theorem decodeFieldSection_main_dyn (hd : HuffmanDecoder) (st : Store)
    (bs : Bytes) (dyn : DynTable) (r : Decoded)
    (h : decodeFieldSection hd st bs dyn = .ok r) : r.store.main = st.main := by
  unfold decodeFieldSection at h
  repeat' split at h
  all_goals cases h
  all_goals exact decodeLines_main _ _ _ _ _ _ _ _ (by assumption)

/-- The default-table instance of `decodeFieldSection_main_dyn`. -/
theorem decodeFieldSection_main (hd : HuffmanDecoder) (st : Store)
    (bs : Bytes) (r : Decoded) (h : decodeFieldSection hd st bs = .ok r) :
    r.store.main = st.main :=
  decodeFieldSection_main_dyn hd st bs DynTable.empty r h

/-! ## Wire vectors, checker-verified at build time (through `#guard`:
well-founded definitions do not kernel-reduce). All with the empty store and
a Huffman decoder that rejects everything — none of these vectors sets the
Huffman bit, so the decoder is never consulted. -/

private def rejectAllHuffman : HuffmanDecoder := ⟨fun _ => none⟩

private def emptyStore : Store := { main := #[], sidecar := #[], entries := [] }

/-- Section prefix `00 00`, then `0xd1` = indexed static 17 (`:method: GET`):
routed to the pseudo record, value entry emitted, store well-formed. -/
private def vecIndexedStatic : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore [0x00, 0x00, 0xd1] with
  | .ok r => r.pseudo.method.isSome && r.fields.isEmpty && r.store.wfCheck
  | .error _ => false
#guard vecIndexedStatic

/-- `0x51` = literal with static name reference, index 1 (`:path`), then the
value literal `/idx` (raw, 7-bit length prefix). -/
private def vecPathLiteral : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore
      ([0x00, 0x00, 0x51, 0x04] ++ strBytes "/idx") with
  | .ok r => r.pseudo.path.isSome && r.fields.isEmpty && r.store.wfCheck
  | .error _ => false
#guard vecPathLiteral

/-- `0x27 0x00` = literal field line with literal name, name length 7 (the
full 3-bit prefix plus a zero continuation byte), name `x-seven`, then value
literal `ok`: one regular field, name + value entries, store well-formed. -/
private def vecLiteralLiteral : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore
      ([0x00, 0x00, 0x27, 0x00] ++ strBytes "x-seven" ++
        [0x02] ++ strBytes "ok") with
  | .ok r =>
    r.fields.length == 1 && r.store.entries.length == 2 && r.store.wfCheck
  | .error _ => false
#guard vecLiteralLiteral

/-- `0x80` = indexed field line, dynamic relative index 0 (§4.5.2, `T=0`)
against the DEFAULT empty dynamic table (Base 0): the reference is out of range,
so the decode fails with `dynamicUnsupported`. -/
private def vecDynamicEmpty : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore [0x00, 0x00, 0x80] with
  | .error .dynamicUnsupported => true
  | _ => false
#guard vecDynamicEmpty

/-- A nonzero encoded Required Insert Count against a zero-capacity table is a
§4.5.1.1 window violation: prefix `01 00` (encoded RIC 1) with `maxEntries = 0`
is rejected as `prefixInvalid` before any field line is read. -/
private def vecRicEmpty : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore [0x01, 0x00, 0x80] with
  | .error .prefixInvalid => true
  | _ => false
#guard vecRicEmpty

/-- The §4.5.1.2 negative-Base error: prefix `00 81` (encoded RIC 0, Sign 1,
ΔBase 1) reconstructs a negative Base and MUST be rejected. -/
private def vecNegativeBase : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore [0x00, 0x81] with
  | .error .prefixInvalid => true
  | _ => false
#guard vecNegativeBase

/-- A Required Insert Count beyond the table's insert total names entries the
decoder has not received (the §2.1.2 blocked condition): prefix `02 00` against
a table with capacity but no inserts. -/
private def vecBlockedRic : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore [0x02, 0x00, 0x80]
      (DynTable.advertised 4096) with
  | .error .dynamicUnsupported => true
  | _ => false
#guard vecBlockedRic

/-- A POPULATED dynamic table: one entry `("x-dyn", "vv")` inserted into a
4096-octet table. -/
private def dynTbl : DynTable := (⟨[], 0, 4096, 4096⟩ : DynTable).add (strBytes "x-dyn") (strBytes "vv")

/-- **The deployed dynamic decode.** Prefix `02 00` reconstructs Required Insert
Count 1 and (S=0, ΔBase 0) Base 1; the field line `0x80` = indexed dynamic
relative index 0 (§4.5.2, `T=0`) then resolves against `dynTbl` to the inserted
`("x-dyn", "vv")` — a decoded regular field, name + value entries, store
well-formed. This is the case the old stub rejected. -/
private def vecDynamicIndexed : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore [0x02, 0x00, 0x80] dynTbl with
  | .ok r => r.fields.length == 1 && r.store.entries.length == 2 && r.store.wfCheck
  | .error _ => false
#guard vecDynamicIndexed

/-! ## RFC 7541 Appendix B Huffman decoder — the concrete decoder wired into
the deployed field-section decode (replacing the old reject-all stub).

The HPACK/QPACK static Huffman code (RFC 7541 Appendix B, referenced by
RFC 9204 §4.1.2 for QPACK string literals). `huffTable` is the canonical
`(bit-length, code)` of each of the 257 symbols (0–255 plus EOS at index 256),
the exact table an off-the-shelf client (aioquic) Huffman-codes its request
header field lines with. Decoding is the standard prefix-code walk: accumulate
bits MSB-first; the first `(length, value)` that is a complete codeword emits its
symbol (the prefix-free property makes the greedy match unambiguous). The
trailing bits must be a valid EOS padding (≤ 7 bits, all ones); the EOS symbol
appearing in the body, or an over-long padding, is an error (RFC 7541 §5.2). -/

/-- RFC 7541 Appendix B: `(number of bits, code)` for symbols 0–255 and EOS
(index 256). -/
def huffTable : Array (Nat × Nat) := #[
    (13, 8184),
    (23, 8388568),
    (28, 268435426),
    (28, 268435427),
    (28, 268435428),
    (28, 268435429),
    (28, 268435430),
    (28, 268435431),
    (28, 268435432),
    (24, 16777194),
    (30, 1073741820),
    (28, 268435433),
    (28, 268435434),
    (30, 1073741821),
    (28, 268435435),
    (28, 268435436),
    (28, 268435437),
    (28, 268435438),
    (28, 268435439),
    (28, 268435440),
    (28, 268435441),
    (28, 268435442),
    (30, 1073741822),
    (28, 268435443),
    (28, 268435444),
    (28, 268435445),
    (28, 268435446),
    (28, 268435447),
    (28, 268435448),
    (28, 268435449),
    (28, 268435450),
    (28, 268435451),
    (6, 20),
    (10, 1016),
    (10, 1017),
    (12, 4090),
    (13, 8185),
    (6, 21),
    (8, 248),
    (11, 2042),
    (10, 1018),
    (10, 1019),
    (8, 249),
    (11, 2043),
    (8, 250),
    (6, 22),
    (6, 23),
    (6, 24),
    (5, 0),
    (5, 1),
    (5, 2),
    (6, 25),
    (6, 26),
    (6, 27),
    (6, 28),
    (6, 29),
    (6, 30),
    (6, 31),
    (7, 92),
    (8, 251),
    (15, 32764),
    (6, 32),
    (12, 4091),
    (10, 1020),
    (13, 8186),
    (6, 33),
    (7, 93),
    (7, 94),
    (7, 95),
    (7, 96),
    (7, 97),
    (7, 98),
    (7, 99),
    (7, 100),
    (7, 101),
    (7, 102),
    (7, 103),
    (7, 104),
    (7, 105),
    (7, 106),
    (7, 107),
    (7, 108),
    (7, 109),
    (7, 110),
    (7, 111),
    (7, 112),
    (7, 113),
    (7, 114),
    (8, 252),
    (7, 115),
    (8, 253),
    (13, 8187),
    (19, 524272),
    (13, 8188),
    (14, 16380),
    (6, 34),
    (15, 32765),
    (5, 3),
    (6, 35),
    (5, 4),
    (6, 36),
    (5, 5),
    (6, 37),
    (6, 38),
    (6, 39),
    (5, 6),
    (7, 116),
    (7, 117),
    (6, 40),
    (6, 41),
    (6, 42),
    (5, 7),
    (6, 43),
    (7, 118),
    (6, 44),
    (5, 8),
    (5, 9),
    (6, 45),
    (7, 119),
    (7, 120),
    (7, 121),
    (7, 122),
    (7, 123),
    (15, 32766),
    (11, 2044),
    (14, 16381),
    (13, 8189),
    (28, 268435452),
    (20, 1048550),
    (22, 4194258),
    (20, 1048551),
    (20, 1048552),
    (22, 4194259),
    (22, 4194260),
    (22, 4194261),
    (23, 8388569),
    (22, 4194262),
    (23, 8388570),
    (23, 8388571),
    (23, 8388572),
    (23, 8388573),
    (23, 8388574),
    (24, 16777195),
    (23, 8388575),
    (24, 16777196),
    (24, 16777197),
    (22, 4194263),
    (23, 8388576),
    (24, 16777198),
    (23, 8388577),
    (23, 8388578),
    (23, 8388579),
    (23, 8388580),
    (21, 2097116),
    (22, 4194264),
    (23, 8388581),
    (22, 4194265),
    (23, 8388582),
    (23, 8388583),
    (24, 16777199),
    (22, 4194266),
    (21, 2097117),
    (20, 1048553),
    (22, 4194267),
    (22, 4194268),
    (23, 8388584),
    (23, 8388585),
    (21, 2097118),
    (23, 8388586),
    (22, 4194269),
    (22, 4194270),
    (24, 16777200),
    (21, 2097119),
    (22, 4194271),
    (23, 8388587),
    (23, 8388588),
    (21, 2097120),
    (21, 2097121),
    (22, 4194272),
    (21, 2097122),
    (23, 8388589),
    (22, 4194273),
    (23, 8388590),
    (23, 8388591),
    (20, 1048554),
    (22, 4194274),
    (22, 4194275),
    (22, 4194276),
    (23, 8388592),
    (22, 4194277),
    (22, 4194278),
    (23, 8388593),
    (26, 67108832),
    (26, 67108833),
    (20, 1048555),
    (19, 524273),
    (22, 4194279),
    (23, 8388594),
    (22, 4194280),
    (25, 33554412),
    (26, 67108834),
    (26, 67108835),
    (26, 67108836),
    (27, 134217694),
    (27, 134217695),
    (26, 67108837),
    (24, 16777201),
    (25, 33554413),
    (19, 524274),
    (21, 2097123),
    (26, 67108838),
    (27, 134217696),
    (27, 134217697),
    (26, 67108839),
    (27, 134217698),
    (24, 16777202),
    (21, 2097124),
    (21, 2097125),
    (26, 67108840),
    (26, 67108841),
    (28, 268435453),
    (27, 134217699),
    (27, 134217700),
    (27, 134217701),
    (20, 1048556),
    (24, 16777203),
    (20, 1048557),
    (21, 2097126),
    (22, 4194281),
    (21, 2097127),
    (21, 2097128),
    (23, 8388595),
    (22, 4194282),
    (22, 4194283),
    (25, 33554414),
    (25, 33554415),
    (24, 16777204),
    (24, 16777205),
    (26, 67108842),
    (23, 8388596),
    (26, 67108843),
    (27, 134217702),
    (26, 67108844),
    (26, 67108845),
    (27, 134217703),
    (27, 134217704),
    (27, 134217705),
    (27, 134217706),
    (27, 134217707),
    (28, 268435454),
    (27, 134217708),
    (27, 134217709),
    (27, 134217710),
    (27, 134217711),
    (27, 134217712),
    (26, 67108846),
    (30, 1073741823)]

/-- Reverse lookup: the symbol whose canonical code is exactly `len` bits with
value `val` (MSB-first), or `none` if no symbol has that code. Unique by the
prefix-free property. -/
def huffLookup (len val : Nat) : Option Nat :=
  huffTable.findIdx? (fun p => p.1 == len && p.2 == val)

/-- Expand `bs` into its bits, most-significant bit of each byte first. -/
def bytesToBits : Bytes → List Bool
  | [] => []
  | b :: rest =>
    (List.range 8).map (fun i => (b.toNat >>> (7 - i)) &&& 1 == 1) ++ bytesToBits rest

/-- Decode a Huffman bit string (RFC 7541 §5.2). `curLen`/`curVal` accumulate the
partial code MSB-first; on a complete codeword the symbol is emitted and the
accumulator resets. Structural recursion on the bit list. The EOS symbol in the
body (`sym = 256`), a code that never completes within 30 bits, or a trailing
padding that is not the (≤ 7-bit) all-ones EOS prefix, are each rejected. -/
def huffDecodeBits : List Bool → Nat → Nat → Option Bytes
  | [], curLen, curVal =>
    if curLen ≤ 7 && curVal == 2 ^ curLen - 1 then some [] else none
  | b :: rest, curLen, curVal =>
    let len := curLen + 1
    let val := curVal * 2 + (if b then 1 else 0)
    match huffLookup len val with
    | some sym =>
      if sym == 256 then none
      else (huffDecodeBits rest 0 0).map (fun tl => UInt8.ofNat sym :: tl)
    | none =>
      if len ≥ 32 then none
      else huffDecodeBits rest len val

/-- Decode a Huffman-coded octet string (RFC 7541 Appendix B). -/
def huffmanDecode (bs : Bytes) : Option Bytes :=
  huffDecodeBits (bytesToBits bs) 0 0

/-- **The deployed Huffman decoder** — the RFC 7541 Appendix B code, packaged as
the `HuffmanDecoder` the field-section decode consults for a Huffman-coded field
line. This replaces the reject-all stub in the deployed QUIC/H3 config. -/
def rfc7541Huffman : HuffmanDecoder := ⟨huffmanDecode⟩

/-! Execution vectors (`#guard`, compiled evaluation — the concrete Huffman codes
an aioquic client emits): each decodes to exactly its bytes. `62728e84cf` is the
Huffman code of `/health`, `9d29ad1f` of `https`, `a0e41d139d09` of `localhost`,
`c5837f` of `GET`, `63` of `/`. -/
#guard huffmanDecode [0x62, 0x72, 0x8e, 0x84, 0xcf] == some (strBytes "/health")
#guard huffmanDecode [0x9d, 0x29, 0xad, 0x1f] == some (strBytes "https")
#guard huffmanDecode [0xa0, 0xe4, 0x1d, 0x13, 0x9d, 0x09] == some (strBytes "localhost")
#guard huffmanDecode [0xc5, 0x83, 0x7f] == some (strBytes "GET")
#guard huffmanDecode [0x63] == some (strBytes "/")
/-! A Huffman-coded literal-with-static-name field line decodes end to end: `0x51`
= literal, static name index 1 (`:path`), then `0x85` = Huffman value of length 5,
`62728e84cf` = `/health`. Through the real `decodeFieldSection` with the deployed
Huffman decoder, the `:path` pseudo resolves to `/health`. -/
private def vecHuffmanPath : Bool :=
  match decodeFieldSection rfc7541Huffman emptyStore
      [0x00, 0x00, 0x51, 0x85, 0x62, 0x72, 0x8e, 0x84, 0xcf] with
  | .ok r => r.pseudo.path.isSome && r.store.wfCheck
  | .error _ => false
#guard vecHuffmanPath

/-! ## Encoder-stream instructions (RFC 9204 §4.3)

The four instructions an encoder sends on its unidirectional stream to build
the decoder's dynamic table: Set Dynamic Table Capacity (§4.3.1), Insert with
Name Reference (§4.3.2), Insert with Literal Name (§4.3.3), and Duplicate
(§4.3.4). `decEncInstr` parses one instruction off the wire; `execInstr`
applies it to the `DynTable` the field-section decode resolves against;
`execEncoderStream` runs a whole encoder-stream chunk. An unresolvable name
reference or duplicate, and an insertion larger than the table capacity, are
encoder-stream errors (`Err.encoderStream`) — the RFC's connection-error
conditions, surfaced as a typed rejection. -/

/-- A decoded encoder-stream instruction (RFC 9204 §4.3). -/
inductive EncInstr where
  /-- §4.3.1 `001 cap(5+)`: set the dynamic table capacity. -/
  | setCapacity (cap : Nat)
  /-- §4.3.2 `1 T idx(6+) ‖ H len(7+) value`: insert, name taken from the
  static (`T=1`) or dynamic (`T=0`, relative) table. -/
  | insertNameRef (isStatic : Bool) (nameIdx : Nat) (value : Bytes)
  /-- §4.3.3 `01 H len(5+) name ‖ H len(7+) value`: insert with literal name. -/
  | insertLiteral (name value : Bytes)
  /-- §4.3.4 `000 idx(5+)`: re-insert the entry at the (relative) index. -/
  | duplicate (idx : Nat)
deriving Repr, DecidableEq

/-- Parse one encoder-stream instruction from the head of `bs` (RFC 9204 §4.3).
Returns the instruction and the bytes consumed. -/
def decEncInstr (hd : HuffmanDecoder) (bs : Bytes) : Except Err (EncInstr × Nat) :=
  match bs with
  | [] => .error .truncated
  | b :: rest =>
    if 0x80 ≤ b.toNat then
      -- Insert with Name Reference (§4.3.2): 1 T idx(6+), then value H len(7+)
      match decPrefixInt 6 b rest with
      | none => .error .truncated
      | some (idx, n) =>
        match rest.drop n with
        | [] => .error .truncated
        | vb :: vrest =>
          match decStr hd 7 vb vrest with
          | .error e => .error e
          | .ok (value, m) =>
            .ok (.insertNameRef (0x40 ≤ b.toNat % 0x80) idx value, 1 + n + 1 + m)
    else if 0x40 ≤ b.toNat then
      -- Insert with Literal Name (§4.3.3): 01 H len(5+) name, then H len(7+) value
      match decStr hd 5 b rest with
      | .error e => .error e
      | .ok (name, n) =>
        match rest.drop n with
        | [] => .error .truncated
        | vb :: vrest =>
          match decStr hd 7 vb vrest with
          | .error e => .error e
          | .ok (value, m) => .ok (.insertLiteral name value, 1 + n + 1 + m)
    else if 0x20 ≤ b.toNat then
      -- Set Dynamic Table Capacity (§4.3.1): 001 cap(5+)
      match decPrefixInt 5 b rest with
      | none => .error .truncated
      | some (cap, n) => .ok (.setCapacity cap, 1 + n)
    else
      -- Duplicate (§4.3.4): 000 idx(5+)
      match decPrefixInt 5 b rest with
      | none => .error .truncated
      | some (idx, n) => .ok (.duplicate idx, 1 + n)

/-- **Progress + boundedness** for one instruction parse: at least one byte,
never more than the input — the encoder-stream loop strictly advances. -/
theorem decEncInstr_consumed (hd : HuffmanDecoder) (bs : Bytes)
    (i : EncInstr) (n : Nat) (h : decEncInstr hd bs = .ok (i, n)) :
    1 ≤ n ∧ n ≤ bs.length := by
  unfold decEncInstr at h
  split at h
  · exact absurd h (by simp)
  · rename_i b rest
    have idxCase : ∀ (p : Nat) (v n₁ : Nat),
        decPrefixInt p b rest = some (v, n₁) → n = 1 + n₁ →
        1 ≤ n ∧ n ≤ (b :: rest).length := by
      intro p v n₁ hpi hn
      have hn₁ := decPrefixInt_consumed p b rest v n₁ hpi
      subst hn; simp only [List.length_cons]; omega
    have refCase : ∀ (p : Nat) (v n₁ : Nat) (vb : UInt8) (vrest value : Bytes) (m : Nat),
        decPrefixInt p b rest = some (v, n₁) → rest.drop n₁ = vb :: vrest →
        decStr hd 7 vb vrest = .ok (value, m) → n = 1 + n₁ + 1 + m →
        1 ≤ n ∧ n ≤ (b :: rest).length := by
      intro p v n₁ vb vrest value m hpi hdrop hstr hn
      have hn₁ := decPrefixInt_consumed p b rest v n₁ hpi
      have hlen : rest.length - n₁ = vrest.length + 1 := by
        have := congrArg List.length hdrop
        simp only [List.length_drop, List.length_cons] at this
        omega
      have hm := decStr_consumed hd 7 vb vrest value m hstr
      subst hn; simp only [List.length_cons]; omega
    split at h
    · -- Insert with Name Reference
      split at h
      · exact absurd h (by simp)
      · rename_i idx n₁ hpi
        split at h
        · exact absurd h (by simp)
        · rename_i vb vrest hdrop
          split at h
          · exact absurd h (by simp)
          · rename_i value m hstr
            cases h; exact refCase 6 idx n₁ vb vrest value m hpi hdrop hstr rfl
    · split at h
      · -- Insert with Literal Name
        split at h
        · exact absurd h (by simp)
        · rename_i name n₁ hstr₁
          have hn₁ := decStr_consumed hd 5 b rest name n₁ hstr₁
          split at h
          · exact absurd h (by simp)
          · rename_i vb vrest hdrop
            have hlen : rest.length - n₁ = vrest.length + 1 := by
              have := congrArg List.length hdrop
              simp only [List.length_drop, List.length_cons] at this
              omega
            split at h
            · exact absurd h (by simp)
            · rename_i value m hstr₂
              have hm := decStr_consumed hd 7 vb vrest value m hstr₂
              cases h; simp only [List.length_cons]; omega
      · split at h
        · -- Set Dynamic Table Capacity
          split at h
          · exact absurd h (by simp)
          · rename_i cap n₁ hpi
            cases h; exact idxCase 5 cap n₁ hpi rfl
        · -- Duplicate
          split at h
          · exact absurd h (by simp)
          · rename_i idx n₁ hpi
            cases h; exact idxCase 5 idx n₁ hpi rfl

/-- RFC 9204 §4.3.1: set the dynamic table capacity. Entries are evicted from
the OLD end until the table fits the new capacity (`keepFit` keeps the newest
prefix); the insert count and the advertised bound are untouched. -/
def DynTable.setCapacity (t : DynTable) (cap : Nat) : DynTable :=
  { entries := keepFit t.entries cap
    insertCount := t.insertCount
    maxSize := cap
    maxCapacity := t.maxCapacity }

/-- Apply one instruction to the dynamic table (RFC 9204 §4.3). An
unresolvable name reference or duplicate, an insertion whose entry is
larger than the capacity (§3.2.2's "MUST NOT insert" bound, checked), and a
capacity exceeding the advertised `SETTINGS_QPACK_MAX_TABLE_CAPACITY`
(§4.3.1's "MUST treat ... as a connection error"), are `encoderStream`
errors. -/
def execInstr (t : DynTable) : EncInstr → Except Err DynTable
  | .setCapacity cap =>
    if cap ≤ t.maxCapacity then .ok (t.setCapacity cap)
    else .error .encoderStream
  | .insertNameRef isStatic idx value =>
    match (if isStatic then (staticEntry idx).map (fun p => strBytes p.1)
           else (t.byRelative t.insertCount idx).map Prod.fst) with
    | none => .error .encoderStream
    | some name =>
      if entrySize (name, value) ≤ t.maxSize then .ok (t.add name value)
      else .error .encoderStream
  | .insertLiteral name value =>
    if entrySize (name, value) ≤ t.maxSize then .ok (t.add name value)
    else .error .encoderStream
  | .duplicate idx =>
    match t.byRelative t.insertCount idx with
    | none => .error .encoderStream
    | some (n, v) =>
      if entrySize (n, v) ≤ t.maxSize then .ok (t.add n v)
      else .error .encoderStream

set_option linter.unusedVariables false in
/-- Run a whole encoder-stream chunk: parse and apply instructions until the
bytes are exhausted. Termination is `decEncInstr_consumed` (every instruction
eats at least one byte). A trailing partial instruction is an error — the
caller feeds whole flushed chunks. -/
def execEncoderStream (hd : HuffmanDecoder) (t : DynTable) (bs : Bytes) :
    Except Err DynTable :=
  match bs with
  | [] => .ok t
  | b :: rest =>
    match h : decEncInstr hd (b :: rest) with
    | .error e => .error e
    | .ok (i, n) =>
      match execInstr t i with
      | .error e => .error e
      | .ok t' => execEncoderStream hd t' ((b :: rest).drop n)
termination_by bs.length
decreasing_by
  have := decEncInstr_consumed hd (b :: rest) i n h
  simp only [List.length_drop, List.length_cons]
  omega

/-! ### Correctness: the size invariant and the §4.3.4 duplicate semantics -/

/-- The §3.2.2 size bound: the table's contents fit its capacity. -/
def DynTable.Fits (t : DynTable) : Prop := tableSize t.entries ≤ t.maxSize

/-- Insertion re-establishes the size bound unconditionally (fit → evict-to-fit;
oversize → empty table). -/
theorem add_fits (t : DynTable) (n v : Bytes) : (t.add n v).Fits := by
  unfold DynTable.Fits DynTable.add
  by_cases hs : entrySize (n, v) ≤ t.maxSize
  · rw [if_pos hs]
    simp only [tableSize_cons]
    have := keepFit_size t.entries (t.maxSize - entrySize (n, v))
    omega
  · rw [if_neg hs]
    simp

/-- Capacity change re-establishes the size bound: eviction trims to the new
capacity (RFC 9204 §4.3.1). -/
theorem setCapacity_fits (t : DynTable) (cap : Nat) : (t.setCapacity cap).Fits :=
  keepFit_size t.entries cap

/-- Capacity change evicts only from the OLD end: the surviving entries are a
prefix (the newest) of the original list. -/
theorem setCapacity_prefix (t : DynTable) (cap : Nat) :
    ∃ suf, (t.setCapacity cap).entries ++ suf = t.entries :=
  keepFit_prefix t.entries cap

/-- **Every instruction preserves the §3.2.2 size invariant**: a table within
its capacity stays within its capacity under any accepted instruction. -/
theorem execInstr_fits (t : DynTable) (i : EncInstr) (t' : DynTable)
    (ht : t.Fits) (h : execInstr t i = .ok t') : t'.Fits := by
  unfold execInstr at h
  split at h
  · split at h
    · cases h; exact setCapacity_fits t _
    · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · cases h; exact add_fits t _ _
      · exact absurd h (by simp)
  · split at h
    · cases h; exact add_fits t _ _
    · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · cases h; exact add_fits t _ _
      · exact absurd h (by simp)

/-- The whole-stream fold preserves the size invariant. -/
theorem execEncoderStream_fits (hd : HuffmanDecoder) (t : DynTable) (bs : Bytes) :
    ∀ t' : DynTable, t.Fits → execEncoderStream hd t bs = .ok t' → t'.Fits := by
  induction t, bs using execEncoderStream.induct hd with
  | case1 t =>
    intro t' ht h
    simp only [execEncoderStream] at h
    cases h
    exact ht
  | case2 t b rest e hinstr =>
    intro t' ht h
    simp only [execEncoderStream] at h
    split at h
    · cases h
    · rename_i i n heq
      rw [hinstr] at heq
      cases heq
  | case3 t b rest i n hinstr e hexec =>
    intro t' ht h
    simp only [execEncoderStream] at h
    split at h
    · rename_i e' heq; rw [hinstr] at heq; cases heq
    · rename_i i' n' heq
      rw [hinstr] at heq
      cases heq
      rw [hexec] at h
      cases h
  | case4 t b rest i n hinstr t₁ hexec ih =>
    intro t' ht h
    simp only [execEncoderStream] at h
    split at h
    · rename_i e' heq; rw [hinstr] at heq; cases heq
    · rename_i i' n' heq
      rw [hinstr] at heq
      cases heq
      rw [hexec] at h
      exact ih t' (execInstr_fits t i t₁ ht hexec) h

/-- **§4.3.1 capacity-bound enforcement**: a Set Dynamic Table Capacity that
exceeds the advertised `SETTINGS_QPACK_MAX_TABLE_CAPACITY` is an
encoder-stream error; within the bound it sets exactly that capacity. -/
theorem execInstr_setCapacity_bound (t : DynTable) (cap : Nat) :
    execInstr t (.setCapacity cap)
      = if cap ≤ t.maxCapacity then .ok (t.setCapacity cap)
        else .error .encoderStream := rfl

/-- No instruction changes the advertised bound: `maxCapacity` is a
connection constant (fixed by SETTINGS, §3.2.3). -/
theorem add_maxCapacity (t : DynTable) (n v : Bytes) :
    (t.add n v).maxCapacity = t.maxCapacity := by
  unfold DynTable.add; split <;> rfl

theorem execInstr_maxCapacity (t : DynTable) (i : EncInstr) (t' : DynTable)
    (h : execInstr t i = .ok t') : t'.maxCapacity = t.maxCapacity := by
  unfold execInstr at h
  split at h
  · split at h
    · cases h; rfl
    · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · cases h; exact add_maxCapacity t _ _
      · exact absurd h (by simp)
  · split at h
    · cases h; exact add_maxCapacity t _ _
    · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · cases h; exact add_maxCapacity t _ _
      · exact absurd h (by simp)

/-- **§4.3.4 duplicate semantics**: `Duplicate idx` on a table that resolves
the reference re-inserts EXACTLY the referenced pair — the result is the same
table `add` produces for that pair. -/
theorem execInstr_duplicate_correct (t : DynTable) (idx : Nat) (n v : Bytes)
    (h : t.byRelative t.insertCount idx = some (n, v))
    (hfit : entrySize (n, v) ≤ t.maxSize) :
    execInstr t (.duplicate idx) = .ok (t.add n v) := by
  have heq : execInstr t (.duplicate idx)
      = match t.byRelative t.insertCount idx with
        | none => .error .encoderStream
        | some (n, v) =>
          if entrySize (n, v) ≤ t.maxSize then .ok (t.add n v)
          else .error .encoderStream := rfl
  rw [heq, h]
  simp only [hfit, if_true, reduceIte]

/-- **§4.3.2 static-name insert semantics**: an insert-with-name-reference to
static index `idx` inserts the static entry's name with the instruction's
value. -/
theorem execInstr_insertStatic_correct (t : DynTable) (idx : Nat)
    (sname svalue : String) (value : Bytes)
    (h : staticEntry idx = some (sname, svalue))
    (hfit : entrySize (strBytes sname, value) ≤ t.maxSize) :
    execInstr t (.insertNameRef true idx value) = .ok (t.add (strBytes sname) value) := by
  have heq : execInstr t (.insertNameRef true idx value)
      = match (staticEntry idx).map (fun p => strBytes p.1) with
        | none => .error .encoderStream
        | some name =>
          if entrySize (name, value) ≤ t.maxSize then .ok (t.add name value)
          else .error .encoderStream := rfl
  rw [heq, h]
  simp only [Option.map, hfit, if_true, reduceIte]

/-! ### Wire vectors (RFC 9204 Appendix B.2's encoder stream, and the
error conditions), kernel/compiler-checked -/

/-- RFC 9204 Appendix B.2, first encoder-stream flight: `3fbd01` sets the
capacity to 220; `c00f www.example.com` inserts (`:authority`,
`www.example.com`) by static name reference 0; `c10c /sample/path` inserts
(`:path`, `/sample/path`) by static name reference 1. Two entries, insert
count 2, size within capacity. -/
private def vecB2 : Bool :=
  match execEncoderStream rejectAllHuffman (DynTable.advertised 4096)
      ([0x3f, 0xbd, 0x01, 0xc0, 0x0f] ++ strBytes "www.example.com"
        ++ [0xc1, 0x0c] ++ strBytes "/sample/path") with
  | .ok t =>
    t.insertCount == 2 && t.maxSize == 220 && t.entries.length == 2
      && (t.byAbs 0 == some (strBytes ":authority", strBytes "www.example.com"))
      && (t.byAbs 1 == some (strBytes ":path", strBytes "/sample/path"))
      && decide (tableSize t.entries ≤ t.maxSize)
  | .error _ => false
#guard vecB2

/-- A Duplicate of a never-inserted entry is an encoder-stream error
(the qifs `err11` shape: `01` = Duplicate index 1 on an empty table). -/
private def vecDupEmpty : Bool :=
  match execEncoderStream rejectAllHuffman DynTable.empty [0x01] with
  | .error .encoderStream => true
  | _ => false
#guard vecDupEmpty

/-- An Insert with Name Reference whose static index is absurd is an error
(the qifs `err12` shape: `ff 80 ff ff ff ff 01`). -/
private def vecInsertBadStatic : Bool :=
  match execEncoderStream rejectAllHuffman DynTable.empty
      [0xff, 0x80, 0xff, 0xff, 0xff, 0xff, 0x01] with
  | .error _ => true
  | _ => false
#guard vecInsertBadStatic

/-- Capacity reduction evicts oldest-first: shrink the B.2 table to fit only
the newest entry. -/
private def vecShrink : Bool :=
  match execEncoderStream rejectAllHuffman (DynTable.advertised 4096)
      ([0x3f, 0xbd, 0x01, 0xc0, 0x0f] ++ strBytes "www.example.com"
        ++ [0xc1, 0x0c] ++ strBytes "/sample/path" ++ [0x3f, 0x19]) with
  | .ok t =>
    -- capacity 56 holds only (":path", "/sample/path") (size 5+12+32 = 49)
    t.maxSize == 56 && t.entries.length == 1 && t.insertCount == 2
      && (t.byAbs 1 == some (strBytes ":path", strBytes "/sample/path"))
      && (t.byAbs 0 == none)
  | .error _ => false
#guard vecShrink

/-! ## Decoder-stream instructions (RFC 9204 §4.4)

The three instructions the DECODER sends back on its unidirectional stream:
Section Acknowledgment (§4.4.1, `1` + stream id on a 7-bit prefix), Stream
Cancellation (§4.4.2, `01` + stream id on a 6-bit prefix), and Insert Count
Increment (§4.4.3, `00` + increment on a 6-bit prefix). A server that
advertises a nonzero `SETTINGS_QPACK_MAX_TABLE_CAPACITY` MUST emit a Section
Acknowledgment after processing a section whose Required Insert Count is
nonzero; these are the emitters (and, for the round-trip proofs and the peer
role, the parser). The prefix-integer ENCODER (§4.1.1) is introduced here and
proven inverse to the deployed `decPrefixInt`. -/

/-- Continuation bytes of a §4.1.1 prefix integer for the residue `v`
(the part above the filled prefix): little-endian 7-bit groups, high bit set
on all but the last. -/
def encIntCont (v : Nat) : Bytes :=
  if v < 128 then [UInt8.ofNat v]
  else UInt8.ofNat (v % 128 + 128) :: encIntCont (v / 128)
termination_by v
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Encode a §4.1.1 prefix integer: `pat` is the instruction's pattern in the
bits above the `p`-bit prefix. Values below the prefix maximum fill the first
byte; larger values saturate the prefix and continue in `encIntCont`. -/
def encPrefixInt (p pat v : Nat) : Bytes :=
  if v < 2 ^ p - 1 then [UInt8.ofNat (pat * 2 ^ p + v)]
  else UInt8.ofNat (pat * 2 ^ p + (2 ^ p - 1)) :: encIntCont (v - (2 ^ p - 1))

/-- **Continuation round-trip**: decoding the continuation encoding of `w`
started at `shift` (with `w` inside the 62-bit window the decoder enforces)
adds exactly `w * 2 ^ shift` to the accumulator and consumes exactly the
encoding. -/
theorem decIntCont_encIntCont (w : Nat) : ∀ (shift acc : Nat) (tail : Bytes),
    w < 2 ^ (56 - shift) → shift ≤ 56 →
    decIntCont (encIntCont w ++ tail) shift acc
      = some (acc + w * 2 ^ shift, (encIntCont w).length) := by
  induction w using encIntCont.induct with
  | case1 w h128 =>
    intro shift acc tail hw hs
    unfold encIntCont
    rw [if_pos h128]
    unfold decIntCont
    have hb : (UInt8.ofNat w).toNat = w := by
      show w % 256 = w; omega
    simp only [List.cons_append, List.nil_append, hb]
    rw [if_pos (by omega)]
    congr 2
    have : w % 128 = w := by omega
    rw [this]
  | case2 w h128 ih =>
    intro shift acc tail hw hs
    unfold encIntCont
    rw [if_neg h128]
    unfold decIntCont
    have hb : (UInt8.ofNat (w % 128 + 128)).toNat = w % 128 + 128 := by
      show (w % 128 + 128) % 256 = w % 128 + 128
      have := Nat.mod_lt w (show 0 < 128 by omega)
      omega
    -- the shift stays under the decoder's cap: w ≥ 2^7 inside the window
    -- forces shift < 49
    have hshift : shift < 49 := by
      cases Nat.lt_or_ge shift 49 with
      | inl h => exact h
      | inr h =>
        have h1 : 56 - shift ≤ 7 := by omega
        have h2 : (2 : Nat) ^ (56 - shift) ≤ 2 ^ 7 :=
          Nat.pow_le_pow_right (by omega) h1
        omega
    have hrec := ih (shift + 7) (acc + w % 128 * 2 ^ shift) tail
      (by
        have hlt : w / 128 < 2 ^ (49 - shift) := by
          rw [Nat.div_lt_iff_lt_mul (show 0 < 128 by omega)]
          have : (2 : Nat) ^ (49 - shift) * 128 = 2 ^ (56 - shift) := by
            rw [show (128 : Nat) = 2 ^ 7 from rfl, ← Nat.pow_add]
            congr 1
            omega
          omega
        have : 49 - shift = 56 - (shift + 7) := by omega
        rwa [this] at hlt)
      (by omega)
    simp only [List.cons_append, hb]
    rw [if_neg (by omega), if_neg (by omega)]
    have hmod : (w % 128 + 128) % 128 = w % 128 := by omega
    rw [hmod, hrec]
    simp only [List.length_cons]
    -- acc + w%128·2^shift + w/128·2^(shift+7) = acc + w·2^shift
    have hpow : (2 : Nat) ^ (shift + 7) = 2 ^ shift * 128 := by
      rw [Nat.pow_add]
    have hsw : w / 128 * (2 ^ shift * 128) = w / 128 * 128 * 2 ^ shift := by
      rw [Nat.mul_comm (2 ^ shift) 128, ← Nat.mul_assoc]
    have hdm : w % 128 + w / 128 * 128 = w := by
      have := Nat.div_add_mod w 128
      omega
    congr 2
    rw [hpow, hsw, Nat.add_assoc, ← Nat.add_mul, hdm]

/-- **Prefix-integer round-trip** (§4.1.1): for every prefix width `1 ≤ p ≤ 7`,
pattern `pat` fitting the byte, and value `v` in the decoder's window, the
deployed `decPrefixInt` decodes `encPrefixInt p pat v` back to exactly `v`,
consuming exactly the continuation bytes. -/
theorem decPrefixInt_encPrefixInt (p pat v : Nat) (tail : Bytes)
    (hp : 0 < p) (hp7 : p ≤ 7) (hpat : pat * 2 ^ p + (2 ^ p - 1) < 256)
    (hv : v < 2 ^ 49) :
    ∃ (b : UInt8) (rest : Bytes),
      encPrefixInt p pat v = b :: rest ∧
      decPrefixInt p b (rest ++ tail) = some (v, rest.length) := by
  have hpow : (0 : Nat) < 2 ^ p := Nat.pos_pow_of_pos p (by omega)
  unfold encPrefixInt
  by_cases hsmall : v < 2 ^ p - 1
  · rw [if_pos hsmall]
    refine ⟨UInt8.ofNat (pat * 2 ^ p + v), [], rfl, ?_⟩
    unfold decPrefixInt
    have hb : (UInt8.ofNat (pat * 2 ^ p + v)).toNat = pat * 2 ^ p + v := by
      show (pat * 2 ^ p + v) % 256 = pat * 2 ^ p + v
      omega
    have hmod : (pat * 2 ^ p + v) % 2 ^ p = v := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [hb, hmod]
    rw [if_pos hsmall]
    rfl
  · rw [if_neg hsmall]
    refine ⟨UInt8.ofNat (pat * 2 ^ p + (2 ^ p - 1)),
      encIntCont (v - (2 ^ p - 1)), rfl, ?_⟩
    unfold decPrefixInt
    have hb : (UInt8.ofNat (pat * 2 ^ p + (2 ^ p - 1))).toNat
        = pat * 2 ^ p + (2 ^ p - 1) := by
      show (pat * 2 ^ p + (2 ^ p - 1)) % 256 = pat * 2 ^ p + (2 ^ p - 1)
      omega
    have hmod : (pat * 2 ^ p + (2 ^ p - 1)) % 2 ^ p = 2 ^ p - 1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [hb, hmod]
    rw [if_neg (by omega)]
    have hwin : v - (2 ^ p - 1) < 2 ^ 56 := by
      have h1 : (2 : Nat) ^ 49 ≤ 2 ^ 56 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have := decIntCont_encIntCont (v - (2 ^ p - 1)) 0 (2 ^ p - 1) tail
      (by simpa using hwin) (by omega)
    rw [this]
    congr 2
    · have : (2 : Nat) ^ 0 = 1 := rfl
      omega

/-- A decoder-stream instruction (RFC 9204 §4.4) — what the server EMITS
back to the encoder once the dynamic table is in play. -/
inductive DecInstr where
  /-- §4.4.1 `1 sid(7+)`: the section on `streamId` was fully processed. -/
  | sectionAck (streamId : Nat)
  /-- §4.4.2 `01 sid(6+)`: the stream was reset; its references are released. -/
  | streamCancel (streamId : Nat)
  /-- §4.4.3 `00 inc(6+)`: `inc` more insertions have been processed. -/
  | insertCountInc (inc : Nat)
deriving Repr, DecidableEq

/-- Emit one decoder-stream instruction (§4.4). -/
def encDecInstr : DecInstr → Bytes
  | .sectionAck sid => encPrefixInt 7 1 sid
  | .streamCancel sid => encPrefixInt 6 1 sid
  | .insertCountInc inc => encPrefixInt 6 0 inc

/-- Parse one decoder-stream instruction (the peer role; also the round-trip
witness for the emitter). -/
def decDecInstr (bs : Bytes) : Except Err (DecInstr × Nat) :=
  match bs with
  | [] => .error .truncated
  | b :: rest =>
    if 0x80 ≤ b.toNat then
      match decPrefixInt 7 b rest with
      | none => .error .truncated
      | some (sid, n) => .ok (.sectionAck sid, 1 + n)
    else if 0x40 ≤ b.toNat then
      match decPrefixInt 6 b rest with
      | none => .error .truncated
      | some (sid, n) => .ok (.streamCancel sid, 1 + n)
    else
      match decPrefixInt 6 b rest with
      | none => .error .truncated
      | some (inc, n) => .ok (.insertCountInc inc, 1 + n)

/-- The §4.1.1 value carried by an instruction. -/
def DecInstr.value : DecInstr → Nat
  | .sectionAck sid => sid
  | .streamCancel sid => sid
  | .insertCountInc inc => inc

/-- **Decoder-stream round-trip (§4.4)**: every emitted instruction (with its
value inside the decoder's 62-bit window) parses back to exactly itself,
consuming exactly its encoding — for any following bytes. -/
theorem decDecInstr_encDecInstr (i : DecInstr) (tail : Bytes)
    (hv : i.value < 2 ^ 49) :
    decDecInstr (encDecInstr i ++ tail) = .ok (i, (encDecInstr i).length) := by
  cases i with
  | sectionAck sid =>
    obtain ⟨b, rest, henc, hdec⟩ :=
      decPrefixInt_encPrefixInt 7 1 sid tail (by omega) (by omega) (by omega) hv
    show decDecInstr (encPrefixInt 7 1 sid ++ tail)
      = .ok (.sectionAck sid, (encPrefixInt 7 1 sid).length)
    rw [henc]
    unfold decDecInstr
    have hb : 0x80 ≤ b.toNat := by
      unfold encPrefixInt at henc
      split at henc
      · injection henc with h1 _
        subst h1
        show 0x80 ≤ (1 * 2 ^ 7 + sid) % 256
        rename_i hlt
        omega
      · injection henc with h1 _
        subst h1
        show 0x80 ≤ (1 * 2 ^ 7 + (2 ^ 7 - 1)) % 256
        omega
    simp only [List.cons_append]
    rw [if_pos hb]
    simp only [hdec, List.length_cons, Nat.add_comm]
  | streamCancel sid =>
    obtain ⟨b, rest, henc, hdec⟩ :=
      decPrefixInt_encPrefixInt 6 1 sid tail (by omega) (by omega) (by omega) hv
    show decDecInstr (encPrefixInt 6 1 sid ++ tail)
      = .ok (.streamCancel sid, (encPrefixInt 6 1 sid).length)
    rw [henc]
    unfold decDecInstr
    have hb : 0x40 ≤ b.toNat ∧ b.toNat < 0x80 := by
      unfold encPrefixInt at henc
      split at henc
      · injection henc with h1 _
        subst h1
        constructor
        · show 0x40 ≤ (1 * 2 ^ 6 + sid) % 256
          rename_i hlt
          omega
        · show (1 * 2 ^ 6 + sid) % 256 < 0x80
          rename_i hlt
          omega
      · injection henc with h1 _
        subst h1
        constructor
        · show 0x40 ≤ (1 * 2 ^ 6 + (2 ^ 6 - 1)) % 256
          omega
        · show (1 * 2 ^ 6 + (2 ^ 6 - 1)) % 256 < 0x80
          omega
    simp only [List.cons_append]
    rw [if_neg (show ¬(0x80 ≤ b.toNat) by omega), if_pos hb.1]
    simp only [hdec, List.length_cons, Nat.add_comm]
  | insertCountInc inc =>
    obtain ⟨b, rest, henc, hdec⟩ :=
      decPrefixInt_encPrefixInt 6 0 inc tail (by omega) (by omega) (by omega) hv
    show decDecInstr (encPrefixInt 6 0 inc ++ tail)
      = .ok (.insertCountInc inc, (encPrefixInt 6 0 inc).length)
    rw [henc]
    unfold decDecInstr
    have hb : b.toNat < 0x40 := by
      unfold encPrefixInt at henc
      split at henc
      · injection henc with h1 _
        subst h1
        show (0 * 2 ^ 6 + inc) % 256 < 0x40
        rename_i hlt
        omega
      · injection henc with h1 _
        subst h1
        show (0 * 2 ^ 6 + (2 ^ 6 - 1)) % 256 < 0x40
        omega
    simp only [List.cons_append]
    rw [if_neg (show ¬(0x80 ≤ b.toNat) by omega),
        if_neg (show ¬(0x40 ≤ b.toNat) by omega)]
    simp only [hdec, List.length_cons, Nat.add_comm]

/-! Emitter vectors (`#guard`): the RFC 9204 §4.4 shapes on the wire. Section
Acknowledgment of stream 4 is `0x84`; Stream Cancellation of stream 4 is
`0x44`; Insert Count Increment 1 is `0x01`; a multi-byte stream id crosses
the prefix boundary exactly as §4.1.1 prescribes. -/
#guard encDecInstr (.sectionAck 4) == [0x84]
#guard encDecInstr (.streamCancel 4) == [0x44]
#guard encDecInstr (.insertCountInc 1) == [0x01]
#guard encDecInstr (.sectionAck 200) == [0xff, 0x49]
private def vecDecInstrRoundTrip : Bool :=
  (match decDecInstr (encDecInstr (.sectionAck 200)) with
   | .ok (.sectionAck 200, 2) => true
   | _ => false)
  && (match decDecInstr [0x84] with
      | .ok (.sectionAck 4, 1) => true
      | _ => false)
#guard vecDecInstrRoundTrip

end Qpack
end H3
