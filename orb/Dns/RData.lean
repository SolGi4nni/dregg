import Dns.Wire

/-!
# Typed RDATA (RFC 1035 §3.3/§3.4, RFC 3596, RFC 4034, RFC 6891, RFC 9460)

`typedRData` gives resource-record RDATA its type-specific meaning:

* RFC 1035 §3.4.1 `A` (type 1) — a 4-octet IPv4 address;
* RFC 3596 §2.2 `AAAA` (type 28) — a 16-octet IPv6 address;
* RFC 1035 §3.3.1/§3.3.11/§3.3.12 `CNAME`/`NS`/`PTR` — a single domain name;
* RFC 1035 §3.3.9 `MX` — a 16-bit preference and an exchange domain name;
* RFC 1035 §3.3.13 `SOA` — MNAME, RNAME and five 32-bit fields;
* RFC 1035 §3.3.14 `TXT` — one or more `<character-string>`s;
* RFC 4034 §2 `DNSKEY`, §3 `RRSIG`, §4 `NSEC`, §5 `DS` — field-level DNSSEC
  record parses;
* RFC 6891 §6.1 `OPT` (type 41) — EDNS(0): the CLASS field is the requestor's
  UDP payload size and the TTL field carries extended-RCODE / version / DO;
* RFC 9460 §2.2 `SVCB`/`HTTPS` (types 64/65) — priority, target name, and the
  SvcParams TLV list.

**Design constraint honored here:** domain names inside RDATA (CNAME, NS, PTR,
MX, SOA) may be compressed, and their pointers target octets of the *whole
message*, not of the RDATA slice. Every name-bearing reader therefore decodes
against the full message at the record's RDATA offset (`RRAt.rdOff`) — this is
why `typedRData` takes the message and an `RRAt`, not bare RDATA bytes.

All readers are total: the two variable-length walks (`charStrings` for TXT,
`tlvs` for SvcParams/EDNS options) recurse on strictly shrinking byte lists,
and names inherit `Dns.decodeName`'s anti-loop termination.
-/

namespace Dns

/-- Big-endian 16-bit field at index `i` of a byte string. -/
def be16At (l : Bytes) (i : Nat) : Nat := be16 (l.getD i 0) (l.getD (i + 1) 0)

/-- Big-endian 32-bit field at index `i` of a byte string. -/
def be32At (l : Bytes) (i : Nat) : Nat :=
  be32 (l.getD i 0) (l.getD (i + 1) 0) (l.getD (i + 2) 0) (l.getD (i + 3) 0)

/-- A whole byte string as one big-endian number. -/
def beNat (l : Bytes) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem be16At_lt (l : Bytes) (i : Nat) : be16At l i < 65536 := be16_lt _ _

theorem be32At_lt (l : Bytes) (i : Nat) : be32At l i < 4294967296 := by
  have h1 := u8_lt (l.getD i 0); have h2 := u8_lt (l.getD (i + 1) 0)
  have h3 := u8_lt (l.getD (i + 2) 0); have h4 := u8_lt (l.getD (i + 3) 0)
  unfold be32At be32; omega

/-- `beNat` is bounded by `256 ^ length`: an `n`-octet field is an `8n`-bit
number. Stated over an arbitrary accumulator to make the fold's invariant
explicit. -/
theorem beNat_foldl_lt (l : Bytes) :
    ∀ acc : Nat, l.foldl (fun acc b => acc * 256 + b.toNat) acc < (acc + 1) * 256 ^ l.length := by
  induction l with
  | nil => intro acc; simp
  | cons b t ih =>
    intro acc
    have hb := u8_lt b
    have := ih (acc * 256 + b.toNat)
    simp only [List.foldl_cons, List.length_cons]
    calc List.foldl (fun acc b => acc * 256 + b.toNat) (acc * 256 + b.toNat) t
        < (acc * 256 + b.toNat + 1) * 256 ^ t.length := this
      _ ≤ ((acc + 1) * 256) * 256 ^ t.length := by
          apply Nat.mul_le_mul_right; omega
      _ = (acc + 1) * 256 ^ (t.length + 1) := by
          rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ t.length)]

/-- An `n`-octet big-endian field is `< 256^n`; a 16-octet AAAA address is a
128-bit number. -/
theorem beNat_lt (l : Bytes) : beNat l < 256 ^ l.length := by
  have := beNat_foldl_lt l 0
  simpa [beNat] using this

/-! ## `<character-string>` walk (RFC 1035 §3.3.14 / §3.3)

A TXT RDATA is one or more `<character-string>`s: a length octet followed by
that many octets. The walk must consume the RDATA exactly. -/

/-- Fuel-driven `<character-string>` walk: structural on the fuel, so it
reduces in the kernel. Each step consumes at least the length octet, so fuel
seeded from the byte count always suffices. -/
def charStringsAux : Nat → Bytes → Option (List (List UInt8))
  | _, [] => some []
  | 0, _ :: _ => none
  | Nat.succ fuel, n :: rest =>
    if n.toNat ≤ rest.length then
      match charStringsAux fuel (rest.drop n.toNat) with
      | none => none
      | some ss => some (rest.take n.toNat :: ss)
    else none

/-- Split a byte string into its `<character-string>`s. `none` when a length
octet overruns the remaining bytes. Total (fuel is the byte count, which
bounds the number of strings). -/
def charStrings (l : Bytes) : Option (List (List UInt8)) :=
  charStringsAux l.length l

/-! ## TLV walk (RFC 9460 §2.2 SvcParams; RFC 6891 §6.1.2 EDNS options)

Both SvcParams and EDNS(0) options are a sequence of
`key(16) length(16) value(length)` entries that must consume their region
exactly. -/

/-- Fuel-driven TLV walk: structural on the fuel, so it reduces in the kernel.
Each entry consumes 4 fixed octets, so fuel seeded from the byte count always
suffices. -/
def tlvsAux : Nat → Bytes → Option (List (Nat × List UInt8))
  | _, [] => some []
  | 0, _ :: _ => none
  | Nat.succ fuel, k1 :: k2 :: l1 :: l2 :: rest =>
    if be16 l1 l2 ≤ rest.length then
      match tlvsAux fuel (rest.drop (be16 l1 l2)) with
      | none => none
      | some ps => some ((be16 k1 k2, rest.take (be16 l1 l2)) :: ps)
    else none
  | Nat.succ _, _ => none

/-- Split a byte string into `(key, value)` TLV entries. `none` when a length
field overruns. Total (fuel is the byte count, which bounds the number of
entries). -/
def tlvs (l : Bytes) : Option (List (Nat × List UInt8)) :=
  tlvsAux l.length l

/-! ## The typed RDATA values -/

/-- Type-specific RDATA meaning. Domain names are decoded label lists; numeric
fields are `Nat`s read big-endian. `other` carries the raw RDATA of any type
without a typed reader here. -/
inductive RData where
  /-- RFC 1035 §3.4.1: a 32-bit IPv4 address. -/
  | a (addr : Nat)
  /-- RFC 3596 §2.2: a 128-bit IPv6 address. -/
  | aaaa (addr : Nat)
  /-- RFC 1035 §3.3.1: the canonical name. -/
  | cname (name : List (List UInt8))
  /-- RFC 1035 §3.3.11: the authoritative server name. -/
  | ns (name : List (List UInt8))
  /-- RFC 1035 §3.3.12: the pointed-to name. -/
  | ptr (name : List (List UInt8))
  /-- RFC 1035 §3.3.9: preference and exchange. -/
  | mx (pref : Nat) (exchange : List (List UInt8))
  /-- RFC 1035 §3.3.13: MNAME, RNAME, serial, refresh, retry, expire, minimum. -/
  | soa (mname rname : List (List UInt8)) (serial refresh retry expire minimum : Nat)
  /-- RFC 1035 §3.3.14: the `<character-string>`s. -/
  | txt (strings : List (List UInt8))
  /-- RFC 4034 §2: flags, protocol, algorithm, public key. -/
  | dnskey (flags protocol algorithm : Nat) (publicKey : List UInt8)
  /-- RFC 4034 §3: type covered, algorithm, labels, original TTL, signature
  expiration/inception (seconds since epoch), key tag, signer name, signature. -/
  | rrsig (typeCovered algorithm labels origTtl expiration inception keyTag : Nat)
          (signer : List (List UInt8)) (signature : List UInt8)
  /-- RFC 4034 §5: key tag, algorithm, digest type, digest. -/
  | ds (keyTag algorithm digestType : Nat) (digest : List UInt8)
  /-- RFC 4034 §4: next domain name and the type bit maps. -/
  | nsec (next : List (List UInt8)) (typeBitmaps : List UInt8)
  /-- RFC 5155 §3: hash algorithm, flags, iterations, salt, next hashed owner
  name (binary), and the type bit maps. -/
  | nsec3 (hashAlg flags iterations : Nat) (salt nextHashed typeBitmaps : List UInt8)
  /-- RFC 5155 §4: hash algorithm, flags, iterations, salt. -/
  | nsec3param (hashAlg flags iterations : Nat) (salt : List UInt8)
  /-- RFC 9460 §2.2 (SVCB type 64, HTTPS type 65): priority, target, SvcParams. -/
  | svcb (priority : Nat) (target : List (List UInt8)) (params : List (Nat × List UInt8))
  /-- RFC 6891 §6.1: requestor's UDP payload size (the CLASS field),
  extended RCODE and version and DO bit (the TTL field), and the options. -/
  | opt (udpPayload extRcode version : Nat) (doBit : Bool) (options : List (Nat × List UInt8))
  /-- Any type without a typed reader here: the raw RDATA. -/
  | other (rdata : List UInt8)
  deriving Repr, DecidableEq, BEq

/-- Decode a single domain name that must occupy the RDATA exactly
(CNAME/NS/PTR shape): decoded against the whole message at the RDATA offset so
compression pointers resolve. -/
def rdataName (msg : Bytes) (r : RRAt) : Option (List (List UInt8)) :=
  match decodeName msg r.rdOff with
  | .error _ => none
  | .ok d => if d.consumed = r.rr.rdata.length then some d.labels else none

/-- **The typed RDATA reader.** Dispatch on the record type; name-bearing
RDATA decodes against the whole message at `r.rdOff` (compression pointers
inside RDATA target the message, not the slice). `none` exactly when the RDATA
is malformed for its type; types without a typed reader yield `other`. -/
def typedRData (msg : Bytes) (r : RRAt) : Option RData :=
  match r.rr.rrType with
  | 1 =>
    match r.rr.rdata with
    | [a, b, c, d] => some (.a (be32 a b c d))
    | _ => none
  | 28 => if r.rr.rdata.length = 16 then some (.aaaa (beNat r.rr.rdata)) else none
  | 5 =>
    match rdataName msg r with
    | none => none
    | some nm => some (.cname nm)
  | 2 =>
    match rdataName msg r with
    | none => none
    | some nm => some (.ns nm)
  | 12 =>
    match rdataName msg r with
    | none => none
    | some nm => some (.ptr nm)
  | 15 =>
    if 2 ≤ r.rr.rdata.length then
      match decodeName msg (r.rdOff + 2) with
      | .error _ => none
      | .ok d =>
        if 2 + d.consumed = r.rr.rdata.length then some (.mx (be16At r.rr.rdata 0) d.labels) else none
    else none
  | 6 =>
    match decodeName msg r.rdOff with
    | .error _ => none
    | .ok m =>
      match decodeName msg (r.rdOff + m.consumed) with
      | .error _ => none
      | .ok rn =>
        if m.consumed + rn.consumed + 20 = r.rr.rdata.length then
          some (.soa m.labels rn.labels
            (be32At r.rr.rdata (m.consumed + rn.consumed))
            (be32At r.rr.rdata (m.consumed + rn.consumed + 4))
            (be32At r.rr.rdata (m.consumed + rn.consumed + 8))
            (be32At r.rr.rdata (m.consumed + rn.consumed + 12))
            (be32At r.rr.rdata (m.consumed + rn.consumed + 16)))
        else none
  | 16 =>
    match charStrings r.rr.rdata with
    | none => none
    | some ss => some (.txt ss)
  | 48 =>
    if 4 ≤ r.rr.rdata.length then
      some (.dnskey (be16At r.rr.rdata 0) (r.rr.rdata.getD 2 0).toNat (r.rr.rdata.getD 3 0).toNat (r.rr.rdata.drop 4))
    else none
  | 46 =>
    if 18 ≤ r.rr.rdata.length then
      match decodeName msg (r.rdOff + 18) with
      | .error _ => none
      | .ok s =>
        if 18 + s.consumed ≤ r.rr.rdata.length then
          some (.rrsig (be16At r.rr.rdata 0) (r.rr.rdata.getD 2 0).toNat (r.rr.rdata.getD 3 0).toNat
            (be32At r.rr.rdata 4) (be32At r.rr.rdata 8) (be32At r.rr.rdata 12) (be16At r.rr.rdata 16)
            s.labels (r.rr.rdata.drop (18 + s.consumed)))
        else none
    else none
  | 43 =>
    if 4 ≤ r.rr.rdata.length then
      some (.ds (be16At r.rr.rdata 0) (r.rr.rdata.getD 2 0).toNat (r.rr.rdata.getD 3 0).toNat (r.rr.rdata.drop 4))
    else none
  | 47 =>
    match decodeName msg r.rdOff with
    | .error _ => none
    | .ok d =>
      if d.consumed ≤ r.rr.rdata.length then some (.nsec d.labels (r.rr.rdata.drop d.consumed)) else none
  | 50 =>
    if 5 ≤ r.rr.rdata.length then
      if 6 + (r.rr.rdata.getD 4 0).toNat ≤ r.rr.rdata.length then
        if 6 + (r.rr.rdata.getD 4 0).toNat
            + (r.rr.rdata.getD (5 + (r.rr.rdata.getD 4 0).toNat) 0).toNat
            ≤ r.rr.rdata.length then
          some (.nsec3 (r.rr.rdata.getD 0 0).toNat (r.rr.rdata.getD 1 0).toNat
            (be16At r.rr.rdata 2)
            ((r.rr.rdata.drop 5).take (r.rr.rdata.getD 4 0).toNat)
            ((r.rr.rdata.drop (6 + (r.rr.rdata.getD 4 0).toNat)).take
              (r.rr.rdata.getD (5 + (r.rr.rdata.getD 4 0).toNat) 0).toNat)
            (r.rr.rdata.drop (6 + (r.rr.rdata.getD 4 0).toNat
              + (r.rr.rdata.getD (5 + (r.rr.rdata.getD 4 0).toNat) 0).toNat)))
        else none
      else none
    else none
  | 51 =>
    if 5 + (r.rr.rdata.getD 4 0).toNat = r.rr.rdata.length then
      some (.nsec3param (r.rr.rdata.getD 0 0).toNat (r.rr.rdata.getD 1 0).toNat
        (be16At r.rr.rdata 2) (r.rr.rdata.drop 5))
    else none
  | 41 =>
    match tlvs r.rr.rdata with
    | none => none
    | some os =>
      some (.opt r.rr.rrClass (r.rr.ttl / 16777216) (r.rr.ttl / 65536 % 256)
        (r.rr.ttl / 32768 % 2 == 1) os)
  | 64 =>
    if 2 ≤ r.rr.rdata.length then
      match decodeName msg (r.rdOff + 2) with
      | .error _ => none
      | .ok t =>
        match tlvs (r.rr.rdata.drop (2 + t.consumed)) with
        | none => none
        | some ps => some (.svcb (be16At r.rr.rdata 0) t.labels ps)
    else none
  | 65 =>
    if 2 ≤ r.rr.rdata.length then
      match decodeName msg (r.rdOff + 2) with
      | .error _ => none
      | .ok t =>
        match tlvs (r.rr.rdata.drop (2 + t.consumed)) with
        | none => none
        | some ps => some (.svcb (be16At r.rr.rdata 0) t.labels ps)
    else none
  | _ => some (.other r.rr.rdata)

theorem typedRData_total (msg : Bytes) (r : RRAt) : ∃ v, typedRData msg r = v := ⟨_, rfl⟩

/-! ## Field bounds: the typed reads respect their RFC field widths -/

/-- Every 32-bit read is bounded. -/
theorem be32_lt_u32 (a b c d : UInt8) : be32 a b c d < 4294967296 := by
  have h1 := u8_lt a; have h2 := u8_lt b; have h3 := u8_lt c; have h4 := u8_lt d
  unfold be32; omega

/-- An `A` value is a 32-bit number (RFC 1035 §3.4.1) — and only the type-1
branch of `typedRData` can produce one. -/
theorem typedRData_a_lt (msg : Bytes) (r : RRAt) (n : Nat)
    (h : typedRData msg r = some (.a n)) : n < 4294967296 := by
  unfold typedRData at h
  repeat' split at h
  all_goals try exact Option.noConfusion h
  all_goals injection h with h
  all_goals try exact RData.noConfusion h
  injection h with h
  subst h
  exact be32_lt_u32 _ _ _ _

/-- An `AAAA` value is a 128-bit number (RFC 3596 §2.2): the 16-octet length
gate in `typedRData` is what bounds it. -/
theorem typedRData_aaaa_lt (msg : Bytes) (r : RRAt) (n : Nat)
    (h : typedRData msg r = some (.aaaa n)) : n < 2 ^ 128 := by
  unfold typedRData at h
  repeat' split at h
  all_goals try exact Option.noConfusion h
  all_goals injection h with h
  all_goals try exact RData.noConfusion h
  injection h with h
  subst h
  have hlen : r.rr.rdata.length = 16 := by assumption
  have hb := beNat_lt r.rr.rdata
  rw [hlen] at hb
  have hpow : (256 : Nat) ^ 16 = 2 ^ 128 := by decide
  rw [hpow] at hb
  exact hb

/-! ## The walks consume their region exactly

RFC 1035 §3.3.14 (TXT) and RFC 9460 §2.2 / RFC 6891 §6.1.2 (TLVs) require the
strings/entries to fill the RDATA exactly — a successful walk accounts for
every input octet. -/

/-- Shifting the accumulator out of a `foldl (· + ·)`. -/
theorem foldl_add_shift (l : List Nat) : ∀ a : Nat, l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l with
  | nil => intro a; simp
  | cons x t ih => intro a; simp only [List.foldl_cons]; rw [ih (a + x), ih (0 + x)]; omega

/-- A successful `<character-string>` walk accounts for every octet: each
string contributes its length octet plus its bytes, and the total is the input
length. -/
theorem charStringsAux_exact (fuel : Nat) :
    ∀ (l : Bytes) (ss : List (List UInt8)),
      charStringsAux fuel l = some ss →
      (ss.map (fun s => s.length + 1)).foldl (· + ·) 0 = l.length := by
  induction fuel with
  | zero =>
    intro l ss h
    match l with
    | [] => injection h with h; subst h; rfl
    | _ :: _ => exact absurd h (by simp [charStringsAux])
  | succ fuel ih =>
    intro l ss h
    match l with
    | [] => injection h with h; subst h; rfl
    | n :: rest =>
      unfold charStringsAux at h
      split at h
      · rename_i hle
        split at h
        · exact absurd h (by simp)
        · rename_i ss' htail
          injection h with h; subst h
          have htl := ih _ _ htail
          have hlen : (rest.take n.toNat).length = n.toNat := by
            rw [List.length_take]; omega
          have hdrop : (rest.drop n.toNat).length = rest.length - n.toNat :=
            List.length_drop _ _
          simp only [List.map_cons, List.foldl_cons, List.length_cons, hlen] at *
          -- foldl (·+·) with a shifted accumulator
          rw [foldl_add_shift] at *
          omega
      · exact absurd h (by simp)

theorem charStrings_exact (l : Bytes) (ss : List (List UInt8))
    (h : charStrings l = some ss) :
    (ss.map (fun s => s.length + 1)).foldl (· + ·) 0 = l.length :=
  charStringsAux_exact _ _ _ h

/-- A successful TLV walk accounts for every octet: each entry contributes its
4 fixed octets plus its value bytes. -/
theorem tlvsAux_exact (fuel : Nat) :
    ∀ (l : Bytes) (ps : List (Nat × List UInt8)),
      tlvsAux fuel l = some ps →
      (ps.map (fun p => p.2.length + 4)).foldl (· + ·) 0 = l.length := by
  induction fuel with
  | zero =>
    intro l ps h
    match l with
    | [] => injection h with h; subst h; rfl
    | _ :: _ => exact absurd h (by simp [tlvsAux])
  | succ fuel ih =>
    intro l ps h
    match l with
    | [] => injection h with h; subst h; rfl
    | [_] | [_, _] | [_, _, _] => exact absurd h (by simp [tlvsAux])
    | k1 :: k2 :: l1 :: l2 :: rest =>
      unfold tlvsAux at h
      split at h
      · rename_i hle
        split at h
        · exact absurd h (by simp)
        · rename_i ps' htail
          injection h with h; subst h
          have htl := ih _ _ htail
          have hlen : (rest.take (be16 l1 l2)).length = be16 l1 l2 := by
            rw [List.length_take]; omega
          have hdrop : (rest.drop (be16 l1 l2)).length = rest.length - be16 l1 l2 :=
            List.length_drop _ _
          simp only [List.map_cons, List.foldl_cons, List.length_cons, hlen] at *
          rw [foldl_add_shift] at *
          omega
      · exact absurd h (by simp)

theorem tlvs_exact (l : Bytes) (ps : List (Nat × List UInt8))
    (h : tlvs l = some ps) :
    (ps.map (fun p => p.2.length + 4)).foldl (· + ·) 0 = l.length :=
  tlvsAux_exact _ _ _ h

/-! ## Worked wire vectors (uncompressed names reduce in the kernel) -/

/-- MX RDATA `10 mail.up` at offset 12 of a message whose RDATA is uncompressed:
preference 10, exchange `mail.up`. -/
example :
    typedRData
      [0,0,0,0,0,0,0,0,0,0,0,0, 0, 10, 4, 109, 97, 105, 108, 2, 117, 112, 0]
      ⟨{ name := [], rrType := 15, rrClass := 1, ttl := 60,
         rdata := [0, 10, 4, 109, 97, 105, 108, 2, 117, 112, 0] }, 12⟩
      = some (.mx 10 [[109, 97, 105, 108], [117, 112]]) := by decide

/-- TXT RDATA with two character-strings `"ab"` and `"c"`. -/
example :
    typedRData [] ⟨{ name := [], rrType := 16, rrClass := 1, ttl := 0,
                     rdata := [2, 97, 98, 1, 99] }, 0⟩
      = some (.txt [[97, 98], [99]]) := by decide

/-- A TXT whose length octet overruns is rejected. -/
example :
    typedRData [] ⟨{ name := [], rrType := 16, rrClass := 1, ttl := 0,
                     rdata := [3, 97, 98] }, 0⟩ = none := by decide

/-- DNSKEY RDATA: flags 257 (KSK), protocol 3, algorithm 13, 2-octet key. -/
example :
    typedRData [] ⟨{ name := [], rrType := 48, rrClass := 1, ttl := 0,
                     rdata := [1, 1, 3, 13, 0xAB, 0xCD] }, 0⟩
      = some (.dnskey 257 3 13 [0xAB, 0xCD]) := by decide

/-- EDNS(0) OPT semantics (RFC 6891 §6.1): CLASS 4096 is the UDP payload size;
TTL `0x00008000` sets the DO bit with extended-RCODE 0, version 0. -/
example :
    typedRData [] ⟨{ name := [], rrType := 41, rrClass := 4096, ttl := 0x00008000,
                     rdata := [] }, 0⟩
      = some (.opt 4096 0 0 true []) := by decide

/-- An A record's 4-octet RDATA is the big-endian address. -/
example :
    typedRData [] ⟨{ name := [], rrType := 1, rrClass := 1, ttl := 0,
                     rdata := [93, 184, 216, 34] }, 0⟩
      = some (.a 1572395042) := by decide

/-- A 3-octet A RDATA is malformed. -/
example :
    typedRData [] ⟨{ name := [], rrType := 1, rrClass := 1, ttl := 0,
                     rdata := [93, 184, 216] }, 0⟩ = none := by decide

/-- NSEC3 RDATA (RFC 5155 §3.2): SHA-1 (alg 1), opt-out flag, 0 iterations,
2-octet salt `ABCD`, 3-octet next hashed owner, one bitmap block (window 0,
1 octet, bit 1 → type A). -/
example :
    typedRData [] ⟨{ name := [], rrType := 50, rrClass := 1, ttl := 0,
                     rdata := [1, 1, 0, 0, 2, 0xAB, 0xCD, 3, 0x11, 0x22, 0x33,
                               0, 1, 0x40] }, 0⟩
      = some (.nsec3 1 1 0 [0xAB, 0xCD] [0x11, 0x22, 0x33] [0, 1, 0x40]) := by decide

/-- An NSEC3 whose salt length overruns the RDATA is malformed. -/
example :
    typedRData [] ⟨{ name := [], rrType := 50, rrClass := 1, ttl := 0,
                     rdata := [1, 0, 0, 0, 9, 0xAB] }, 0⟩ = none := by decide

/-- NSEC3PARAM RDATA (RFC 5155 §4.2): must be exactly its declared salt
longer than the 5 fixed octets. -/
example :
    typedRData [] ⟨{ name := [], rrType := 51, rrClass := 1, ttl := 0,
                     rdata := [1, 0, 0, 0, 2, 0xAB, 0xCD] }, 0⟩
      = some (.nsec3param 1 0 0 [0xAB, 0xCD]) := by decide

/-- An NSEC3PARAM with trailing octets past its salt is malformed. -/
example :
    typedRData [] ⟨{ name := [], rrType := 51, rrClass := 1, ttl := 0,
                     rdata := [1, 0, 0, 0, 1, 0xAB, 0xCD] }, 0⟩ = none := by decide

end Dns
