import Dns.RData

/-!
# Typed SvcParams and EDNS options (RFC 9460 §7, RFC 7873)

`Dns.typedRData` keeps SVCB/HTTPS SvcParams and EDNS(0) options as raw
`(key, value)` TLV lists — the walk itself (exact-cover) is proven in
`Dns.RData`. This file gives the common keys their typed meaning:

* RFC 9460 §7.1 `alpn` (key 1) — a sequence of length-prefixed protocol ids
  (the same `<character-string>` shape as TXT, so the proven walk is reused);
* RFC 9460 §7.2 `port` (key 3) — exactly one 16-bit port;
* RFC 9460 §7.3 `ipv4hint` (key 4) / `ipv6hint` (key 6) — a non-empty list of
  fixed-size addresses that must tile the value exactly;
* RFC 7873 §4 `COOKIE` (EDNS option 10) — an 8-octet client cookie, optionally
  followed by an 8–32 octet server cookie (total length 8 or 16–40).
-/

namespace Dns

/-- The value of the first TLV entry with key `k`. -/
def tlvGet (ps : List (Nat × List UInt8)) (k : Nat) : Option (List UInt8) :=
  match ps.find? (fun p => p.1 == k) with
  | none => none
  | some p => some p.2

/-! ## Fixed-size chunking (address hints) -/

/-- Fuel-driven split into chunks of exactly `n` octets; `none` unless the
input tiles exactly. -/
def chunksAux (n : Nat) : Nat → Bytes → Option (List (List UInt8))
  | _, [] => some []
  | 0, _ :: _ => none
  | Nat.succ fuel, b :: rest =>
    if n ≤ (b :: rest).length then
      match chunksAux n fuel ((b :: rest).drop n) with
      | none => none
      | some cs => some ((b :: rest).take n :: cs)
    else none

/-- Split a byte string into exact `n`-octet chunks (`1 ≤ n`). -/
def chunks (n : Nat) (l : Bytes) : Option (List (List UInt8)) := chunksAux n l.length l

/-- Every chunk has exactly the requested size. -/
theorem chunksAux_length (n fuel : Nat) (_hn : 1 ≤ n) :
    ∀ (l : Bytes) (cs : List (List UInt8)), chunksAux n fuel l = some cs →
      ∀ c ∈ cs, c.length = n := by
  induction fuel with
  | zero =>
    intro l cs h c hc
    match l with
    | [] => injection h with h; subst h; simp at hc
    | _ :: _ => exact absurd h (by simp [chunksAux])
  | succ fuel ih =>
    intro l cs h c hc
    match l with
    | [] => injection h with h; subst h; simp at hc
    | b :: rest =>
      unfold chunksAux at h
      split at h
      · rename_i hle
        split at h
        · exact absurd h (by simp)
        · rename_i cs' htail
          injection h with h; subst h
          rcases List.mem_cons.mp hc with h1 | h1
          · subst h1; rw [List.length_take]; omega
          · exact ih _ _ htail c h1
      · exact absurd h (by simp)

theorem chunks_length (n : Nat) (hn : 1 ≤ n) (l : Bytes) (cs : List (List UInt8))
    (h : chunks n l = some cs) : ∀ c ∈ cs, c.length = n :=
  chunksAux_length n _ hn l cs h

/-! ## RFC 9460 §7 typed SvcParams -/

/-- §7.1 `alpn` (key 1): the protocol-id list, decoded with the proven
`<character-string>` walk. `none` when absent or malformed. -/
def svcAlpn (ps : List (Nat × List UInt8)) : Option (List (List UInt8)) :=
  match tlvGet ps 1 with
  | none => none
  | some v => charStrings v

/-- §7.2 `port` (key 3): the value must be exactly two octets. -/
def svcPort (ps : List (Nat × List UInt8)) : Option Nat :=
  match tlvGet ps 3 with
  | some [hi, lo] => some (be16 hi lo)
  | _ => none

/-- §7.3 `ipv4hint` (key 4): exact 4-octet tiling, each chunk an address. -/
def svcIpv4Hint (ps : List (Nat × List UInt8)) : Option (List Nat) :=
  match tlvGet ps 4 with
  | none => none
  | some v =>
    match chunks 4 v with
    | none => none
    | some cs => some (cs.map beNat)

/-- §7.3 `ipv6hint` (key 6): exact 16-octet tiling. -/
def svcIpv6Hint (ps : List (Nat × List UInt8)) : Option (List Nat) :=
  match tlvGet ps 6 with
  | none => none
  | some v =>
    match chunks 16 v with
    | none => none
    | some cs => some (cs.map beNat)

/-- A decoded port is a 16-bit number (RFC 9460 §7.2). -/
theorem svcPort_lt (ps : List (Nat × List UInt8)) (p : Nat)
    (h : svcPort ps = some p) : p < 65536 := by
  unfold svcPort at h
  split at h
  · injection h with h; subst h; exact be16_lt _ _
  · exact absurd h (by simp)

/-- Every ipv4hint is a 32-bit address (RFC 9460 §7.3): the 4-octet chunking
is what bounds it. -/
theorem svcIpv4Hint_lt (ps : List (Nat × List UInt8)) (as : List Nat)
    (h : svcIpv4Hint ps = some as) : ∀ a ∈ as, a < 4294967296 := by
  intro a ha
  unfold svcIpv4Hint at h
  split at h
  · exact absurd h (by simp)
  · rename_i v hv
    split at h
    · exact absurd h (by simp)
    · rename_i cs hcs
      injection h with h; subst h
      rcases List.mem_map.mp ha with ⟨c, hc, hbe⟩
      have hlen := chunks_length 4 (by omega) v cs hcs c hc
      have := beNat_lt c
      rw [hlen] at this
      omega

/-- Every ipv6hint is a 128-bit address. -/
theorem svcIpv6Hint_lt (ps : List (Nat × List UInt8)) (as : List Nat)
    (h : svcIpv6Hint ps = some as) : ∀ a ∈ as, a < 2 ^ 128 := by
  intro a ha
  unfold svcIpv6Hint at h
  split at h
  · exact absurd h (by simp)
  · rename_i v hv
    split at h
    · exact absurd h (by simp)
    · rename_i cs hcs
      injection h with h; subst h
      rcases List.mem_map.mp ha with ⟨c, hc, hbe⟩
      have hlen := chunks_length 16 (by omega) v cs hcs c hc
      have hb := beNat_lt c
      rw [hlen] at hb
      have hpow : (256 : Nat) ^ 16 = 2 ^ 128 := by decide
      omega

/-! ## RFC 7873 EDNS COOKIE (option 10) -/

/-- §4: a COOKIE option is the 8-octet client cookie alone, or the client
cookie followed by an 8–32 octet server cookie. Returns
`(client, server)` with `server = []` when only the client half is present;
`none` when absent or of illegal length (§5.2 FORMERR shape). -/
def ednsCookie (os : List (Nat × List UInt8)) : Option (List UInt8 × List UInt8) :=
  match tlvGet os 10 with
  | none => none
  | some v =>
    if v.length = 8 then some (v, [])
    else if 16 ≤ v.length ∧ v.length ≤ 40 then some (v.take 8, v.drop 8)
    else none

/-- **Cookie shape (RFC 7873 §4).** A decoded cookie has an exactly-8-octet
client half, and a server half that is empty or 8–32 octets. -/
theorem ednsCookie_shape (os : List (Nat × List UInt8)) (c s : List UInt8)
    (h : ednsCookie os = some (c, s)) :
    c.length = 8 ∧ (s.length = 0 ∨ (8 ≤ s.length ∧ s.length ≤ 32)) := by
  unfold ednsCookie at h
  split at h
  · exact absurd h (by simp)
  · rename_i v hv
    split at h
    · rename_i h8
      injection h with h
      injection h with hc hs
      subst hc; subst hs
      exact ⟨h8, Or.inl rfl⟩
    · split at h
      · rename_i hrange
        injection h with h
        injection h with hc hs
        subst hc; subst hs
        refine ⟨by rw [List.length_take]; omega, Or.inr ?_⟩
        rw [List.length_drop]
        omega
      · exact absurd h (by simp)

/-! ## Worked vectors -/

/-- RFC 9460 §7 params of a real HTTPS record shape: alpn `h3`,`h2`,
port 8443, one ipv4hint. -/
example :
    svcAlpn [(1, [2, 104, 51, 2, 104, 50]), (4, [104, 16, 132, 229])]
      = some [[104, 51], [104, 50]] := by decide

example : svcPort [(3, [0x20, 0xFB])] = some 8443 := by decide

example :
    svcIpv4Hint [(4, [104, 16, 132, 229, 104, 16, 133, 229])]
      = some [1745913061, 1745913317] := by decide

/-- An ipv4hint that does not tile into 4-octet addresses is malformed. -/
example : svcIpv4Hint [(4, [104, 16, 132])] = none := by decide

/-- A client-only cookie and a full client+server cookie. -/
example :
    ednsCookie [(10, [1, 2, 3, 4, 5, 6, 7, 8])]
      = some ([1, 2, 3, 4, 5, 6, 7, 8], []) := by decide

example :
    ednsCookie [(10, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16])]
      = some ([1, 2, 3, 4, 5, 6, 7, 8], [9, 10, 11, 12, 13, 14, 15, 16]) := by decide

/-- A 12-octet cookie is illegal (RFC 7873 §5.2). -/
example : ednsCookie [(10, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])] = none := by decide

end Dns
