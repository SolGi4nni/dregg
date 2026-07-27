/-!
# Control.TailcfgBridge — the leaf-value bridges of the tailcfg wire codec

`Control/Tailcfg.lean` carries a node key, an address prefix and an endpoint as
the **marshaled JSON strings** the public `tailcfg` package emits
(`"nodekey:<64 hex>"`, `"100.64.0.1/32"`, `"192.168.1.5:41641"`). That is exact at
the JSON level but leaves the *value* of a key or an address unscoped: nothing
said what those strings mean as bytes.

This module closes that gap. For each leaf it gives

* a **total** renderer `… → List Char` (no `partial`, no `sorry`),
* a **total** parser `List Char → Option (… × List Char)`, and
* a machine-checked **inverse theorem** `parse (render x ++ rest) = some (x, rest)`
  (plus the `String`-level corollary `ofString (toString x) = some x`).

The parsers are *resumable* (they return the unconsumed tail), which is what lets
them compose: an octet parser stops at `'.'`, the address parser stops at `'/'`,
and the whole-string wrappers additionally demand that nothing is left over.

Formats, all from the public `github.com/tailscale/tailscale` source (BSD-3):
`key.NodePublic.MarshalText` → `"nodekey:" ++ hex`, `MachinePublic` → `"mkey:"`,
`DiscoPublic` → `"discokey:"` (`types/key/node.go`, `machine.go`, `disco.go`);
`netip.Prefix` → `"<addr>/<bits>"`; `netip.AddrPort` → `"<addr>:<port>"`.

## Scope (named, not hidden)

IPv4 addresses are proven end to end. IPv6 is **not** modeled here: Go's
`netip.Addr.String` emits the RFC 5952 *compressed* form (`"fd7a:115c::1"`),
whose renderer picks a longest zero-run — a genuinely different theorem, and a
named residual rather than a silent gap. Tailnet addresses in the modeled flow
are CGNAT IPv4 (`100.64.0.0/10`), which is what the ACL compiler consumes.
-/

namespace Control.Bridge

/-! ## §1  Decimal — `Nat` ↔ its digit string

The shared numeric bridge: every port, octet and prefix length below (and the
JSON number renderer in `Control/TailcfgWire.lean`) is built on this pair. -/

/-- The decimal digit characters, as a table (so the inverse below is `decide`able). -/
def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'
  | _ => '0'

/-- Read a decimal digit character. -/
def charDigit (c : Char) : Option Nat :=
  if c = '0' then some 0 else if c = '1' then some 1 else if c = '2' then some 2
  else if c = '3' then some 3 else if c = '4' then some 4 else if c = '5' then some 5
  else if c = '6' then some 6 else if c = '7' then some 7 else if c = '8' then some 8
  else if c = '9' then some 9 else none

theorem charDigit_digitChar : ∀ d, d < 10 → charDigit (digitChar d) = some d := by decide

/-- The decimal rendering of a `Nat` (most-significant digit first, no leading
zeros, `0 ↦ "0"`). Total: the recursion is on `n / 10`. -/
def natDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else natDigits (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by omega

/-- Consume a maximal run of digits, accumulating; returns the value and the tail. -/
def readNat : Nat → List Char → Nat × List Char
  | acc, [] => (acc, [])
  | acc, c :: rest =>
    match charDigit c with
    | some d => readNat (acc * 10 + d) rest
    | none => (acc, c :: rest)

/-- `NoDigit rest`: the tail cannot extend a number that precedes it. Every
call site below discharges it with a literal separator (`'.'`, `'/'`, `':'`,
`','`, `']'`, `'}'`) or the end of input. -/
def NoDigit : List Char → Prop
  | [] => True
  | c :: _ => charDigit c = none

theorem readNat_stop {acc : Nat} {rest : List Char} (h : NoDigit rest) :
    readNat acc rest = (acc, rest) := by
  cases rest with
  | nil => rfl
  | cons c t => simp only [readNat, NoDigit] at h ⊢; rw [h]

/-- **The decimal digit run reads back exactly.** Consuming `natDigits n` moves the
accumulator from `0` to `n` and leaves the tail untouched. -/
theorem readNat_natDigits : ∀ (n : Nat) (rest : List Char),
    readNat 0 (natDigits n ++ rest) = readNat n rest := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro rest
    rw [natDigits]
    split
    · next hlt =>
        simp only [List.cons_append, List.nil_append, readNat,
          charDigit_digitChar n hlt]
        simp
    · next hge =>
        have hd : n / 10 < n := by omega
        rw [List.append_assoc, ih (n / 10) hd]
        simp only [List.cons_append, List.nil_append, readNat,
          charDigit_digitChar (n % 10) (by omega)]
        congr 1
        omega

/-- Does the input start with a digit? -/
def hasDigit : List Char → Bool
  | [] => false
  | c :: _ => (charDigit c).isSome

/-- Parse a decimal number: at least one digit required. -/
def parseNat (cs : List Char) : Option (Nat × List Char) :=
  if hasDigit cs then some (readNat 0 cs) else none

theorem hasDigit_natDigits : ∀ (n : Nat) (rest : List Char),
    hasDigit (natDigits n ++ rest) = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro rest
    rw [natDigits]
    split
    · next hlt =>
        simp only [List.cons_append, List.nil_append, hasDigit,
          charDigit_digitChar n hlt, Option.isSome_some]
    · next hge =>
        have hd : n / 10 < n := by omega
        rw [List.append_assoc]
        exact ih (n / 10) hd _

/-- The first character of a decimal rendering is a decimal digit. Used by the
JSON text layer to show that a rendered number cannot be mistaken for `null`,
`true`, a string, an array or an object. -/
theorem natDigits_head : ∀ (n : Nat), ∃ d t, d < 10 ∧ natDigits n = digitChar d :: t := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits]
    split
    · next hlt => exact ⟨n, [], hlt, rfl⟩
    · next hge =>
        have hd : n / 10 < n := by omega
        obtain ⟨d, t, hdlt, ht⟩ := ih (n / 10) hd
        exact ⟨d, t ++ [digitChar (n % 10)], hdlt, by rw [ht]; rfl⟩

/-- **`parseNat` inverts `natDigits`.** -/
theorem parseNat_natDigits (n : Nat) {rest : List Char} (h : NoDigit rest) :
    parseNat (natDigits n ++ rest) = some (n, rest) := by
  simp only [parseNat, hasDigit_natDigits n rest, if_pos, readNat_natDigits n rest,
    readNat_stop h]

/-- Parse a decimal number and require it below a bound. -/
def parseNatLt (bound : Nat) (cs : List Char) : Option (Nat × List Char) :=
  match parseNat cs with
  | some (n, r) => if n < bound then some (n, r) else none
  | none => none

theorem parseNatLt_natDigits {n bound : Nat} (hb : n < bound) {rest : List Char}
    (h : NoDigit rest) : parseNatLt bound (natDigits n ++ rest) = some (n, rest) := by
  simp only [parseNatLt, parseNat_natDigits n h, hb, if_pos]

/-! ## §2  Hexadecimal — bytes ↔ lowercase hex

Go's `hex.EncodeToString` (what `key.NodePublic.MarshalText` uses) emits
lowercase; the reader accepts either case. -/

def hexDigit : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6'
  | 7 => '7' | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b' | 12 => 'c'
  | 13 => 'd' | 14 => 'e' | 15 => 'f' | _ => '0'

def hexVal (c : Char) : Option Nat :=
  if c = '0' then some 0 else if c = '1' then some 1 else if c = '2' then some 2
  else if c = '3' then some 3 else if c = '4' then some 4 else if c = '5' then some 5
  else if c = '6' then some 6 else if c = '7' then some 7 else if c = '8' then some 8
  else if c = '9' then some 9
  else if c = 'a' || c = 'A' then some 10 else if c = 'b' || c = 'B' then some 11
  else if c = 'c' || c = 'C' then some 12 else if c = 'd' || c = 'D' then some 13
  else if c = 'e' || c = 'E' then some 14 else if c = 'f' || c = 'F' then some 15
  else none

theorem hexVal_hexDigit : ∀ n, n < 16 → hexVal (hexDigit n) = some n := by decide

/-- One byte as two lowercase hex characters (high nibble first). -/
def byteHex (b : UInt8) : List Char :=
  [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- A byte string as hex. -/
def bytesHex : List UInt8 → List Char
  | [] => []
  | b :: t => byteHex b ++ bytesHex t

/-- Read a byte string from hex; the length must be even and every character a
hex digit, else `none`. -/
def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexVal a
    let y ← hexVal b
    let t ← hexBytes rest
    some (UInt8.ofNat (x * 16 + y) :: t)
  | _ => none

theorem toNat_lt_256 (b : UInt8) : b.toNat < 256 := b.toNat_lt

/-- **The hex codec is inverted exactly.** -/
theorem hexBytes_bytesHex : ∀ bs : List UInt8, hexBytes (bytesHex bs) = some bs := by
  intro bs
  induction bs with
  | nil => rfl
  | cons b t ih =>
    have hb := toNat_lt_256 b
    have h1 : b.toNat / 16 < 16 := by omega
    have h2 : b.toNat % 16 < 16 := by omega
    simp only [bytesHex, byteHex, List.cons_append, List.nil_append, hexBytes,
      hexVal_hexDigit _ h1, hexVal_hexDigit _ h2, ih, Option.bind_some, bind]
    have : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
    simp [this]

/-! ## §3  Key strings — `"nodekey:<hex>"`, `"mkey:<hex>"`, `"discokey:<hex>"` -/

/-- Strip a literal prefix, or fail. -/
def stripPrefix : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | p :: ps, c :: cs => if p = c then stripPrefix ps cs else none
  | _ :: _, [] => none

theorem stripPrefix_append : ∀ (p rest : List Char),
    stripPrefix p (p ++ rest) = some rest := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons c t ih => intro rest; simp only [List.cons_append, stripPrefix, if_pos]; exact ih rest

/-- Render a typed key as its marshaled text: `<tag> ++ ":" ++ hex(bytes)`. -/
def keyText (tag : List Char) (bs : List UInt8) : List Char :=
  tag ++ (':' :: bytesHex bs)

/-- Read a typed key: the tag, a colon, then an even hex run to the end. -/
def keyBytes (tag : List Char) (cs : List Char) : Option (List UInt8) :=
  match stripPrefix (tag ++ [':']) cs with
  | some hex => hexBytes hex
  | none => none

/-- **A key string decodes to exactly the bytes it was rendered from.** -/
theorem keyBytes_keyText (tag : List Char) (bs : List UInt8) :
    keyBytes tag (keyText tag bs) = some bs := by
  have h : keyText tag bs = (tag ++ [':']) ++ bytesHex bs := by
    simp [keyText]
  simp only [keyBytes, h, stripPrefix_append, hexBytes_bytesHex]

/-! ### The three concrete key types (32 bytes each) -/

def nodeKeyTag : List Char := ['n','o','d','e','k','e','y']
def machineKeyTag : List Char := ['m','k','e','y']
def discoKeyTag : List Char := ['d','i','s','c','o','k','e','y']

/-- A 32-byte public key, as the tailcfg JSON string. -/
def NodeKey.toText (bs : List UInt8) : String := String.ofList (keyText nodeKeyTag bs)
def MachineKey.toText (bs : List UInt8) : String := String.ofList (keyText machineKeyTag bs)
def DiscoKey.toText (bs : List UInt8) : String := String.ofList (keyText discoKeyTag bs)

/-- Decode a key string, additionally enforcing the 32-byte key length that
`key.NodePublic` (an X25519 public key) always has. -/
def keyOfText (tag : List Char) (s : String) : Option (List UInt8) :=
  match keyBytes tag s.toList with
  | some bs => if bs.length = 32 then some bs else none
  | none => none

def NodeKey.ofText (s : String) : Option (List UInt8) := keyOfText nodeKeyTag s
def MachineKey.ofText (s : String) : Option (List UInt8) := keyOfText machineKeyTag s
def DiscoKey.ofText (s : String) : Option (List UInt8) := keyOfText discoKeyTag s

theorem keyOfText_toText (tag : List Char) (bs : List UInt8) (h : bs.length = 32) :
    keyOfText tag (String.ofList (keyText tag bs)) = some bs := by
  simp only [keyOfText, String.toList_ofList, keyBytes_keyText, h, if_pos]

/-- **`"nodekey:<64 hex>"` ↔ 32 bytes, proven inverse.** -/
theorem NodeKey.ofText_toText (bs : List UInt8) (h : bs.length = 32) :
    NodeKey.ofText (NodeKey.toText bs) = some bs := keyOfText_toText _ bs h
theorem MachineKey.ofText_toText (bs : List UInt8) (h : bs.length = 32) :
    MachineKey.ofText (MachineKey.toText bs) = some bs := keyOfText_toText _ bs h
theorem DiscoKey.ofText_toText (bs : List UInt8) (h : bs.length = 32) :
    DiscoKey.ofText (DiscoKey.toText bs) = some bs := keyOfText_toText _ bs h

/-! ## §4  `netip` — IPv4 address, prefix and endpoint -/

/-- An IPv4 address as its four octets (`netip.Addr`, 4-byte case). -/
structure Ip4 where
  a : UInt8
  b : UInt8
  c : UInt8
  d : UInt8
deriving Repr, BEq, DecidableEq

/-- Expect a literal character. -/
def expectC (ch : Char) : List Char → Option (List Char)
  | [] => none
  | c :: rest => if c = ch then some rest else none

theorem expectC_cons (ch : Char) (rest : List Char) :
    expectC ch (ch :: rest) = some rest := by simp [expectC]

/-- Dotted-quad rendering (`netip.Addr.String`, 4-byte case). -/
def Ip4.render (x : Ip4) : List Char :=
  natDigits x.a.toNat ++ ('.' :: (natDigits x.b.toNat ++
    ('.' :: (natDigits x.c.toNat ++ ('.' :: natDigits x.d.toNat)))))

def parseOctet (cs : List Char) : Option (UInt8 × List Char) :=
  match parseNatLt 256 cs with
  | some (n, r) => some (UInt8.ofNat n, r)
  | none => none

theorem parseOctet_render (b : UInt8) {rest : List Char} (h : NoDigit rest) :
    parseOctet (natDigits b.toNat ++ rest) = some (b, rest) := by
  have hb := toNat_lt_256 b
  simp only [parseOctet, parseNatLt_natDigits hb h]
  simp

/-- Resumable IPv4 parser: stops at the first character that is not part of the
address (`'/'`, `':'`, `','`, `'"'`, end of input …). -/
def Ip4.parse (cs : List Char) : Option (Ip4 × List Char) := do
  let (a, r1) ← parseOctet cs
  let r1 ← expectC '.' r1
  let (b, r2) ← parseOctet r1
  let r2 ← expectC '.' r2
  let (c, r3) ← parseOctet r2
  let r3 ← expectC '.' r3
  let (d, r4) ← parseOctet r3
  some ({ a, b, c, d }, r4)

theorem noDigit_dot (rest : List Char) : NoDigit ('.' :: rest) := by
  simp [NoDigit, charDigit]

theorem Ip4.parse_render (x : Ip4) {rest : List Char} (h : NoDigit rest) :
    Ip4.parse (Ip4.render x ++ rest) = some (x, rest) := by
  obtain ⟨a, b, c, d⟩ := x
  have e : Ip4.render { a, b, c, d } ++ rest =
      natDigits a.toNat ++ ('.' :: (natDigits b.toNat ++ ('.' :: (natDigits c.toNat ++
        ('.' :: (natDigits d.toNat ++ rest)))))) := by
    simp [Ip4.render]
  rw [e]
  simp only [Ip4.parse]
  rw [parseOctet_render a (noDigit_dot _)]
  simp [expectC_cons]
  rw [parseOctet_render b (noDigit_dot _)]
  simp [expectC_cons]
  rw [parseOctet_render c (noDigit_dot _)]
  simp [expectC_cons]
  rw [parseOctet_render d h]
  rfl

/-! ### `netip.Prefix` — `"a.b.c.d/bits"` -/

/-- `netip.Prefix` over IPv4: an address and a mask length `≤ 32`. -/
structure Prefix4 where
  addr : Ip4
  bits : Nat
deriving Repr, BEq, DecidableEq

def Prefix4.render (p : Prefix4) : List Char :=
  p.addr.render ++ ('/' :: natDigits p.bits)

def Prefix4.parse (cs : List Char) : Option (Prefix4 × List Char) := do
  let (addr, r1) ← Ip4.parse cs
  let r1 ← expectC '/' r1
  let (bits, r2) ← parseNatLt 33 r1
  some ({ addr, bits }, r2)

theorem noDigit_slash (rest : List Char) : NoDigit ('/' :: rest) := by
  simp [NoDigit, charDigit]

theorem Prefix4.parse_render (p : Prefix4) (hb : p.bits ≤ 32) {rest : List Char}
    (h : NoDigit rest) : Prefix4.parse (Prefix4.render p ++ rest) = some (p, rest) := by
  obtain ⟨addr, bits⟩ := p
  have hb' : bits ≤ 32 := hb
  have e : Prefix4.render { addr, bits } ++ rest =
      addr.render ++ ('/' :: (natDigits bits ++ rest)) := by
    simp [Prefix4.render]
  rw [e]
  simp only [Prefix4.parse]
  rw [Ip4.parse_render addr (noDigit_slash _)]
  simp [expectC_cons]
  rw [parseNatLt_natDigits (by omega : bits < 33) h]
  rfl

/-- Whole-string form (`netip.Prefix.MarshalText`). -/
def Prefix4.toText (p : Prefix4) : String := String.ofList p.render
def Prefix4.ofText (s : String) : Option Prefix4 :=
  match Prefix4.parse s.toList with
  | some (p, []) => some p
  | _ => none

/-- **`"100.64.0.1/32"` ↔ (4 bytes, mask), proven inverse.** -/
theorem Prefix4.ofText_toText (p : Prefix4) (hb : p.bits ≤ 32) :
    Prefix4.ofText (Prefix4.toText p) = some p := by
  simp only [Prefix4.ofText, Prefix4.toText, String.toList_ofList]
  have := Prefix4.parse_render p hb (rest := []) (by simp [NoDigit])
  simp only [List.append_nil] at this
  rw [this]

/-! ### `netip.AddrPort` — `"a.b.c.d:port"` -/

/-- `netip.AddrPort` over IPv4 (a WireGuard endpoint as `MapRequest.Endpoints`
carries it). -/
structure AddrPort4 where
  addr : Ip4
  port : Nat
deriving Repr, BEq, DecidableEq

def AddrPort4.render (e : AddrPort4) : List Char :=
  e.addr.render ++ (':' :: natDigits e.port)

def AddrPort4.parse (cs : List Char) : Option (AddrPort4 × List Char) := do
  let (addr, r1) ← Ip4.parse cs
  let r1 ← expectC ':' r1
  let (port, r2) ← parseNatLt 65536 r1
  some ({ addr, port }, r2)

theorem noDigit_colon (rest : List Char) : NoDigit (':' :: rest) := by
  simp [NoDigit, charDigit]

theorem AddrPort4.parse_render (e : AddrPort4) (hp : e.port < 65536)
    {rest : List Char} (h : NoDigit rest) :
    AddrPort4.parse (AddrPort4.render e ++ rest) = some (e, rest) := by
  obtain ⟨addr, port⟩ := e
  have hp' : port < 65536 := hp
  have e2 : AddrPort4.render { addr, port } ++ rest =
      addr.render ++ (':' :: (natDigits port ++ rest)) := by
    simp [AddrPort4.render]
  rw [e2]
  simp only [AddrPort4.parse]
  rw [Ip4.parse_render addr (noDigit_colon _)]
  simp [expectC_cons]
  rw [parseNatLt_natDigits hp' h]
  rfl

def AddrPort4.toText (e : AddrPort4) : String := String.ofList e.render
def AddrPort4.ofText (s : String) : Option AddrPort4 :=
  match AddrPort4.parse s.toList with
  | some (e, []) => some e
  | _ => none

/-- **`"192.168.1.5:41641"` ↔ (4 bytes, port), proven inverse.** -/
theorem AddrPort4.ofText_toText (e : AddrPort4) (hp : e.port < 65536) :
    AddrPort4.ofText (AddrPort4.toText e) = some e := by
  simp only [AddrPort4.ofText, AddrPort4.toText, String.toList_ofList]
  have := AddrPort4.parse_render e hp (rest := []) (by simp [NoDigit])
  simp only [List.append_nil] at this
  rw [this]

/-! ## §5  Execution witnesses (the proofs above are the guarantee; these show
the concrete strings a real client exchanges). -/

/-- The 32-byte key `00 01 02 … 1f`. -/
def demoKey : List UInt8 := (List.range 32).map (fun i => UInt8.ofNat i)

#eval NodeKey.toText demoKey
#eval (NodeKey.ofText (NodeKey.toText demoKey)) == some demoKey
-- a real tailscale-shaped node key string (64 hex chars after the tag):
#eval NodeKey.ofText "nodekey:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
-- wrong tag must fail:
#eval (NodeKey.ofText "mkey:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20").isSome
-- short key must fail (length gate):
#eval (NodeKey.ofText "nodekey:0102").isSome

def demoPrefix : Prefix4 := { addr := { a := 100, b := 64, c := 0, d := 1 }, bits := 32 }
#eval Prefix4.toText demoPrefix
#eval Prefix4.ofText "100.64.0.1/32"
#eval (Prefix4.ofText (Prefix4.toText demoPrefix)) == some demoPrefix
#eval (Prefix4.ofText "100.64.0.1/33").isSome   -- mask out of range → none
#eval (Prefix4.ofText "100.64.0.256/32").isSome -- octet out of range → none

def demoEndpoint : AddrPort4 := { addr := { a := 192, b := 168, c := 1, d := 5 }, port := 41641 }
#eval AddrPort4.toText demoEndpoint
#eval AddrPort4.ofText "192.168.1.5:41641"
#eval (AddrPort4.ofText (AddrPort4.toText demoEndpoint)) == some demoEndpoint

/-! ## §6  Axiom audit -/

#print axioms readNat_natDigits
#print axioms parseNat_natDigits
#print axioms hexBytes_bytesHex
#print axioms keyBytes_keyText
#print axioms NodeKey.ofText_toText
#print axioms MachineKey.ofText_toText
#print axioms DiscoKey.ofText_toText
#print axioms Ip4.parse_render
#print axioms Prefix4.ofText_toText
#print axioms AddrPort4.ofText_toText

end Control.Bridge
