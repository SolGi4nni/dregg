import Dns.Encode
import Dns.RData

/-!
# Typed RDATA composition and encode-then-parse roundtrips

`Dns.Encode` composes the message *frame* (header, question, record shells)
and proves it parses back. This file closes the remaining composition gap:
**typed RDATA**. `encodeRData` writes the wire RDATA of every typed value
`Dns.typedRData` can read, and the roundtrip theorems prove the two sides
agree — `typedRData` applied to an `encodeRData`-written RDATA returns exactly
the value that was written, under the RFC field-width side conditions
(16/32-bit fields in range, labels 1..63 octets, names ≤ 255 octets,
`<character-string>`s ≤ 255 octets). The composer cannot drift from the
deployed reader without breaking a theorem.

Name-bearing RDATA is position-dependent (`typedRData` decodes names against
the whole message at the record's RDATA offset), so those roundtrips are
stated *embedded*: the encoded RDATA may sit at any offset of any message.

This file also gives composition its RFC 1035 §4.1.4 pointer form:
`encodePtr` writes a compression pointer, and `decodeName_encodePtr` proves
the deployed decoder resolves it to exactly the name at the target offset —
the compressing encoder and the pointer-chasing parser meet in a theorem.
-/

namespace Dns

/-! ## Fixed-width big-endian writer -/

/-- `putBe w n` writes the low `8·w` bits of `n`, big-endian, in exactly `w`
octets. -/
def putBe : Nat → Nat → Bytes
  | 0, _ => []
  | Nat.succ w, n => putBe w (n / 256) ++ [UInt8.ofNat n]

theorem putBe_length (w : Nat) : ∀ n, (putBe w n).length = w := by
  induction w with
  | zero => intro n; rfl
  | succ w ih => intro n; simp [putBe, List.length_append, ih]

theorem beNat_append_byte (l : Bytes) (b : UInt8) :
    beNat (l ++ [b]) = beNat l * 256 + b.toNat := by
  unfold beNat
  rw [List.foldl_append]
  rfl

/-- **The numeric roundtrip.** An in-range value reads back from its
fixed-width write: `beNat ∘ putBe w = id` on `[0, 256^w)`. -/
theorem beNat_putBe (w : Nat) : ∀ n, n < 256 ^ w → beNat (putBe w n) = n := by
  induction w with
  | zero =>
    intro n h
    rw [Nat.pow_zero] at h
    have : n = 0 := by omega
    subst this
    rfl
  | succ w ih =>
    intro n h
    have hdiv : n / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h
      omega
    simp only [putBe]
    rw [beNat_append_byte, ih _ hdiv, UInt8.toNat_ofNat]
    omega

/-- The 2-octet writer agrees with `putU16`. -/
theorem putBe_two (n : Nat) : putBe 2 n = putU16 n := by
  simp [putBe, putU16]

/-! ## `<character-string>` and TLV composition (the reverse walks) -/

/-- Write a TXT-shaped `<character-string>` sequence (RFC 1035 §3.3.14). -/
def encodeCharStrings (ss : List (List UInt8)) : Bytes :=
  (ss.map (fun s => UInt8.ofNat s.length :: s)).flatten

/-- Write a `key(16) length(16) value` TLV sequence (RFC 9460 §2.2 SvcParams /
RFC 6891 §6.1.2 EDNS options). -/
def encodeTlvs (ps : List (Nat × List UInt8)) : Bytes :=
  (ps.map (fun p => putU16 p.1 ++ (putU16 p.2.length ++ p.2))).flatten

theorem charStringsAux_encode (ss : List (List UInt8)) :
    ∀ fuel, (∀ s ∈ ss, s.length ≤ 255) → (encodeCharStrings ss).length ≤ fuel →
      charStringsAux fuel (encodeCharStrings ss) = some ss := by
  induction ss with
  | nil =>
    intro fuel _ _
    cases fuel <;> rfl
  | cons s tail ih =>
    intro fuel hlen hfuel
    have hs : s.length ≤ 255 := hlen s (by simp)
    have hunfold : encodeCharStrings (s :: tail)
        = UInt8.ofNat s.length :: (s ++ encodeCharStrings tail) := by
      simp [encodeCharStrings]
    match fuel with
    | 0 =>
      rw [hunfold] at hfuel
      simp at hfuel
    | Nat.succ fuel =>
      rw [hunfold]
      unfold charStringsAux
      have htn : (UInt8.ofNat s.length).toNat = s.length := by
        rw [UInt8.toNat_ofNat]; omega
      rw [htn]
      have hle : s.length ≤ (s ++ encodeCharStrings tail).length := by
        simp [List.length_append]
      rw [if_pos hle, List.drop_left s _, List.take_left s _]
      have hfu : (encodeCharStrings tail).length ≤ fuel := by
        have := congrArg List.length hunfold
        simp only [List.length_cons, List.length_append] at this
        omega
      rw [ih fuel (fun x hx => hlen x (by simp [hx])) hfu]

/-- **The `<character-string>` roundtrip**: what `encodeCharStrings` writes,
the proven TXT walk reads back verbatim (strings ≤ 255 octets). -/
theorem charStrings_encode (ss : List (List UInt8)) (h : ∀ s ∈ ss, s.length ≤ 255) :
    charStrings (encodeCharStrings ss) = some ss :=
  charStringsAux_encode ss _ h (Nat.le_refl _)

theorem tlvsAux_encode (ps : List (Nat × List UInt8)) :
    ∀ fuel, (∀ p ∈ ps, p.1 < 65536 ∧ p.2.length < 65536) →
      (encodeTlvs ps).length ≤ fuel →
      tlvsAux fuel (encodeTlvs ps) = some ps := by
  induction ps with
  | nil =>
    intro fuel _ _
    cases fuel <;> rfl
  | cons p tail ih =>
    intro fuel hok hfuel
    have hp := hok p (by simp)
    have hunfold : encodeTlvs (p :: tail)
        = UInt8.ofNat (p.1 / 256) :: UInt8.ofNat p.1
            :: UInt8.ofNat (p.2.length / 256) :: UInt8.ofNat p.2.length
            :: (p.2 ++ encodeTlvs tail) := by
      simp [encodeTlvs, putU16]
    match fuel with
    | 0 =>
      rw [hunfold] at hfuel
      simp at hfuel
    | Nat.succ fuel =>
      rw [hunfold]
      unfold tlvsAux
      rw [be16_putU16 p.2.length hp.2, be16_putU16 p.1 hp.1]
      have hle : p.2.length ≤ (p.2 ++ encodeTlvs tail).length := by
        simp [List.length_append]
      rw [if_pos hle, List.drop_left p.2 _, List.take_left p.2 _]
      have hfu : (encodeTlvs tail).length ≤ fuel := by
        have := congrArg List.length hunfold
        simp only [List.length_cons, List.length_append] at this
        omega
      rw [ih fuel (fun x hx => hok x (by simp [hx])) hfu]

/-- **The TLV roundtrip**: what `encodeTlvs` writes, the proven TLV walk reads
back verbatim (keys and value lengths 16-bit). -/
theorem tlvs_encode (ps : List (Nat × List UInt8))
    (h : ∀ p ∈ ps, p.1 < 65536 ∧ p.2.length < 65536) :
    tlvs (encodeTlvs ps) = some ps :=
  tlvsAux_encode ps _ h (Nat.le_refl _)

/-! ## The typed RDATA writer -/

/-- Write the wire RDATA of a typed value. Names are written uncompressed
(§4.1.4 makes compression optional); numeric fields are truncated to their
RFC widths, exactly as the roundtrip side conditions require them to already
be. `opt` writes only its options (its other fields live in the record shell's
CLASS and TTL); `other` is the raw RDATA back. -/
def encodeRData : RData → Bytes
  | .a addr => putBe 4 addr
  | .aaaa addr => putBe 16 addr
  | .cname n => encodeName n
  | .ns n => encodeName n
  | .ptr n => encodeName n
  | .mx pref exch => putBe 2 pref ++ encodeName exch
  | .soa m r serial refresh retry expire minimum =>
    encodeName m ++ encodeName r ++ putBe 4 serial ++ putBe 4 refresh
      ++ putBe 4 retry ++ putBe 4 expire ++ putBe 4 minimum
  | .txt ss => encodeCharStrings ss
  | .dnskey flags protocol algorithm key =>
    putBe 2 flags ++ UInt8.ofNat protocol :: UInt8.ofNat algorithm :: key
  | .rrsig tc alg labels origTtl exp inc tag signer sig =>
    putBe 2 tc ++ UInt8.ofNat alg :: UInt8.ofNat labels
      :: (putBe 4 origTtl ++ putBe 4 exp ++ putBe 4 inc ++ putBe 2 tag
          ++ encodeName signer ++ sig)
  | .ds tag alg dt digest =>
    putBe 2 tag ++ UInt8.ofNat alg :: UInt8.ofNat dt :: digest
  | .nsec next bitmaps => encodeName next ++ bitmaps
  | .nsec3 alg flags iter salt next bitmaps =>
    UInt8.ofNat alg :: UInt8.ofNat flags :: (putBe 2 iter
      ++ UInt8.ofNat salt.length :: (salt
      ++ UInt8.ofNat next.length :: (next ++ bitmaps)))
  | .nsec3param alg flags iter salt =>
    UInt8.ofNat alg :: UInt8.ofNat flags :: (putBe 2 iter
      ++ UInt8.ofNat salt.length :: salt)
  | .svcb priority target params =>
    putBe 2 priority ++ (encodeName target ++ encodeTlvs params)
  | .opt _ _ _ _ options => encodeTlvs options
  | .other rdata => rdata

/-! ## Encode-then-parse roundtrips

Each theorem drives the *deployed* `typedRData` over an `encodeRData`-written
RDATA. Name-free RDATA roundtrips at any position in any message; name-bearing
RDATA is stated embedded at its true offset. -/

/-- A (RFC 1035 §3.4.1): a 32-bit address roundtrips anywhere. -/
theorem typedRData_encode_a (msg : Bytes) (nm : List (List UInt8)) (cls ttl off addr : Nat)
    (h : addr < 4294967296) :
    typedRData msg ⟨{ name := nm, rrType := 1, rrClass := cls, ttl := ttl,
                      rdata := encodeRData (.a addr) }, off⟩ = some (.a addr) := by
  have hlist : encodeRData (.a addr)
      = [UInt8.ofNat (addr / 16777216), UInt8.ofNat (addr / 65536),
         UInt8.ofNat (addr / 256), UInt8.ofNat addr] := by
    simp [encodeRData, putBe, Nat.div_div_eq_div_mul]
  have hbranch : ∀ a b c d : UInt8,
      typedRData msg ⟨{ name := nm, rrType := 1, rrClass := cls, ttl := ttl,
                        rdata := [a, b, c, d] }, off⟩ = some (.a (be32 a b c d)) :=
    fun _ _ _ _ => rfl
  rw [hlist, hbranch, be32_putU32 addr h]

/-- AAAA (RFC 3596 §2.2): a 128-bit address roundtrips anywhere. -/
theorem typedRData_encode_aaaa (msg : Bytes) (nm : List (List UInt8)) (cls ttl off addr : Nat)
    (h : addr < 2 ^ 128) :
    typedRData msg ⟨{ name := nm, rrType := 28, rrClass := cls, ttl := ttl,
                      rdata := encodeRData (.aaaa addr) }, off⟩ = some (.aaaa addr) := by
  have hbranch : typedRData msg
      ⟨{ name := nm, rrType := 28, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.aaaa addr) }, off⟩
      = if (encodeRData (.aaaa addr)).length = 16
        then some (.aaaa (beNat (encodeRData (.aaaa addr)))) else none := rfl
  have hlen : (encodeRData (.aaaa addr)).length = 16 := putBe_length 16 addr
  have hpow : (256 : Nat) ^ 16 = 2 ^ 128 := by decide
  rw [hbranch, if_pos hlen]
  show some (RData.aaaa (beNat (putBe 16 addr))) = some (RData.aaaa addr)
  rw [beNat_putBe 16 addr (by omega)]

/-- TXT (RFC 1035 §3.3.14): the string list roundtrips anywhere (strings
≤ 255 octets). -/
theorem typedRData_encode_txt (msg : Bytes) (nm : List (List UInt8)) (cls ttl off : Nat)
    (ss : List (List UInt8)) (hs : ∀ s ∈ ss, s.length ≤ 255) :
    typedRData msg ⟨{ name := nm, rrType := 16, rrClass := cls, ttl := ttl,
                      rdata := encodeRData (.txt ss) }, off⟩ = some (.txt ss) := by
  have hbranch : typedRData msg
      ⟨{ name := nm, rrType := 16, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.txt ss) }, off⟩
      = match charStrings (encodeRData (.txt ss)) with
        | none => none
        | some ss' => some (.txt ss') := rfl
  rw [hbranch]
  show (match charStrings (encodeCharStrings ss) with
        | none => none
        | some ss' => some (RData.txt ss')) = _
  rw [charStrings_encode ss hs]

/-- DNSKEY (RFC 4034 §2): flags/protocol/algorithm/key roundtrip anywhere
(fields in range). -/
theorem typedRData_encode_dnskey (msg : Bytes) (nm : List (List UInt8)) (cls ttl off : Nat)
    (f p a : Nat) (key : List UInt8)
    (hf : f < 65536) (hp : p < 256) (ha : a < 256) :
    typedRData msg ⟨{ name := nm, rrType := 48, rrClass := cls, ttl := ttl,
                      rdata := encodeRData (.dnskey f p a key) }, off⟩
      = some (.dnskey f p a key) := by
  have hlist : encodeRData (.dnskey f p a key)
      = UInt8.ofNat (f / 256) :: UInt8.ofNat f
          :: UInt8.ofNat p :: UInt8.ofNat a :: key := by
    simp [encodeRData, putBe]
  have hbranch : ∀ rd : Bytes,
      typedRData msg ⟨{ name := nm, rrType := 48, rrClass := cls, ttl := ttl,
                        rdata := rd }, off⟩
        = if 4 ≤ rd.length
          then some (.dnskey (be16At rd 0) (rd.getD 2 0).toNat (rd.getD 3 0).toNat
                       (rd.drop 4))
          else none := fun _ => rfl
  rw [hlist, hbranch, if_pos (by simp [List.length_cons])]
  have h16 : be16At (UInt8.ofNat (f / 256) :: UInt8.ofNat f
      :: UInt8.ofNat p :: UInt8.ofNat a :: key) 0 = f := by
    simp only [be16At, List.getD_cons_zero, List.getD_cons_succ]
    exact be16_putU16 f hf
  have hpp : (UInt8.ofNat p).toNat = p := by rw [UInt8.toNat_ofNat]; omega
  have haa : (UInt8.ofNat a).toNat = a := by rw [UInt8.toNat_ofNat]; omega
  simp only [h16, List.getD_cons_succ, List.getD_cons_zero, List.drop_succ_cons,
    List.drop_zero, hpp, haa]

/-- DS (RFC 4034 §5): key tag/algorithm/digest type/digest roundtrip anywhere
(fields in range). -/
theorem typedRData_encode_ds (msg : Bytes) (nm : List (List UInt8)) (cls ttl off : Nat)
    (tag a dt : Nat) (digest : List UInt8)
    (htag : tag < 65536) (ha : a < 256) (hdt : dt < 256) :
    typedRData msg ⟨{ name := nm, rrType := 43, rrClass := cls, ttl := ttl,
                      rdata := encodeRData (.ds tag a dt digest) }, off⟩
      = some (.ds tag a dt digest) := by
  have hlist : encodeRData (.ds tag a dt digest)
      = UInt8.ofNat (tag / 256) :: UInt8.ofNat tag
          :: UInt8.ofNat a :: UInt8.ofNat dt :: digest := by
    simp [encodeRData, putBe]
  have hbranch : ∀ rd : Bytes,
      typedRData msg ⟨{ name := nm, rrType := 43, rrClass := cls, ttl := ttl,
                        rdata := rd }, off⟩
        = if 4 ≤ rd.length
          then some (.ds (be16At rd 0) (rd.getD 2 0).toNat (rd.getD 3 0).toNat
                       (rd.drop 4))
          else none := fun _ => rfl
  rw [hlist, hbranch, if_pos (by simp [List.length_cons])]
  have h16 : be16At (UInt8.ofNat (tag / 256) :: UInt8.ofNat tag
      :: UInt8.ofNat a :: UInt8.ofNat dt :: digest) 0 = tag := by
    simp only [be16At, List.getD_cons_zero, List.getD_cons_succ]
    exact be16_putU16 tag htag
  have haa : (UInt8.ofNat a).toNat = a := by rw [UInt8.toNat_ofNat]; omega
  have hdd : (UInt8.ofNat dt).toNat = dt := by rw [UInt8.toNat_ofNat]; omega
  simp only [h16, List.getD_cons_succ, List.getD_cons_zero, List.drop_succ_cons,
    List.drop_zero, haa, hdd]

/-- NSEC3PARAM (RFC 5155 §4.2): the parameter tuple roundtrips anywhere
(fields in range, salt ≤ 255 octets). -/
theorem typedRData_encode_nsec3param (msg : Bytes) (nm : List (List UInt8)) (cls ttl off : Nat)
    (alg fl iter : Nat) (salt : List UInt8)
    (halg : alg < 256) (hfl : fl < 256) (hiter : iter < 65536)
    (hsalt : salt.length ≤ 255) :
    typedRData msg ⟨{ name := nm, rrType := 51, rrClass := cls, ttl := ttl,
                      rdata := encodeRData (.nsec3param alg fl iter salt) }, off⟩
      = some (.nsec3param alg fl iter salt) := by
  have hlist : encodeRData (.nsec3param alg fl iter salt)
      = UInt8.ofNat alg :: UInt8.ofNat fl :: UInt8.ofNat (iter / 256)
          :: UInt8.ofNat iter :: UInt8.ofNat salt.length :: salt := by
    simp [encodeRData, putBe]
  have hbranch : ∀ rd : Bytes,
      typedRData msg ⟨{ name := nm, rrType := 51, rrClass := cls, ttl := ttl,
                        rdata := rd }, off⟩
        = if 5 + (rd.getD 4 0).toNat = rd.length
          then some (.nsec3param (rd.getD 0 0).toNat (rd.getD 1 0).toNat
                       (be16At rd 2) (rd.drop 5))
          else none := fun _ => rfl
  have hsl : (UInt8.ofNat salt.length).toNat = salt.length := by
    rw [UInt8.toNat_ofNat]; omega
  rw [hlist, hbranch]
  rw [if_pos (by simp only [List.getD_cons_succ, List.getD_cons_zero,
    List.length_cons, hsl]; omega)]
  have halg' : (UInt8.ofNat alg).toNat = alg := by rw [UInt8.toNat_ofNat]; omega
  have hfl' : (UInt8.ofNat fl).toNat = fl := by rw [UInt8.toNat_ofNat]; omega
  have h16 : be16At (UInt8.ofNat alg :: UInt8.ofNat fl :: UInt8.ofNat (iter / 256)
      :: UInt8.ofNat iter :: UInt8.ofNat salt.length :: salt) 2 = iter := by
    simp only [be16At, List.getD_cons_zero, List.getD_cons_succ]
    exact be16_putU16 iter hiter
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons,
    List.drop_zero, halg', hfl', h16]

/-- CNAME (RFC 1035 §3.3.1): the target name roundtrips, embedded at its true
offset in any message. -/
theorem typedRData_encode_cname (pre rest : Bytes) (nm target : List (List UInt8)) (cls ttl : Nat)
    (hok : LabelsOk target) (hcap : wireLen target ≤ maxName) :
    typedRData (pre ++ (encodeName target ++ rest))
      ⟨{ name := nm, rrType := 5, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.cname target) }, pre.length⟩
      = some (.cname target) := by
  have hrd : rdataName (pre ++ (encodeName target ++ rest))
      ⟨{ name := nm, rrType := 5, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.cname target) }, pre.length⟩ = some target := by
    show (match decodeName (pre ++ (encodeName target ++ rest)) pre.length with
          | .error _ => none
          | .ok d => if d.consumed = (encodeRData (.cname target)).length
                     then some d.labels else none) = some target
    rw [decodeName_encodeName_at pre rest target hok hcap]
    show (if wireLen target = (encodeName target).length
          then some target else none) = some target
    rw [encodeName_length]
    simp
  have hbranch : typedRData (pre ++ (encodeName target ++ rest))
      ⟨{ name := nm, rrType := 5, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.cname target) }, pre.length⟩
      = match rdataName (pre ++ (encodeName target ++ rest))
          ⟨{ name := nm, rrType := 5, rrClass := cls, ttl := ttl,
             rdata := encodeRData (.cname target) }, pre.length⟩ with
        | none => none
        | some n => some (.cname n) := rfl
  rw [hbranch, hrd]

/-- NS (RFC 1035 §3.3.11): same shape as CNAME. -/
theorem typedRData_encode_ns (pre rest : Bytes) (nm target : List (List UInt8)) (cls ttl : Nat)
    (hok : LabelsOk target) (hcap : wireLen target ≤ maxName) :
    typedRData (pre ++ (encodeName target ++ rest))
      ⟨{ name := nm, rrType := 2, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.ns target) }, pre.length⟩
      = some (.ns target) := by
  have hrd : rdataName (pre ++ (encodeName target ++ rest))
      ⟨{ name := nm, rrType := 2, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.ns target) }, pre.length⟩ = some target := by
    show (match decodeName (pre ++ (encodeName target ++ rest)) pre.length with
          | .error _ => none
          | .ok d => if d.consumed = (encodeRData (.ns target)).length
                     then some d.labels else none) = some target
    rw [decodeName_encodeName_at pre rest target hok hcap]
    show (if wireLen target = (encodeName target).length
          then some target else none) = some target
    rw [encodeName_length]
    simp
  have hbranch : typedRData (pre ++ (encodeName target ++ rest))
      ⟨{ name := nm, rrType := 2, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.ns target) }, pre.length⟩
      = match rdataName (pre ++ (encodeName target ++ rest))
          ⟨{ name := nm, rrType := 2, rrClass := cls, ttl := ttl,
             rdata := encodeRData (.ns target) }, pre.length⟩ with
        | none => none
        | some n => some (.ns n) := rfl
  rw [hbranch, hrd]

/-- PTR (RFC 1035 §3.3.12): same shape as CNAME. -/
theorem typedRData_encode_ptr (pre rest : Bytes) (nm target : List (List UInt8)) (cls ttl : Nat)
    (hok : LabelsOk target) (hcap : wireLen target ≤ maxName) :
    typedRData (pre ++ (encodeName target ++ rest))
      ⟨{ name := nm, rrType := 12, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.ptr target) }, pre.length⟩
      = some (.ptr target) := by
  have hrd : rdataName (pre ++ (encodeName target ++ rest))
      ⟨{ name := nm, rrType := 12, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.ptr target) }, pre.length⟩ = some target := by
    show (match decodeName (pre ++ (encodeName target ++ rest)) pre.length with
          | .error _ => none
          | .ok d => if d.consumed = (encodeRData (.ptr target)).length
                     then some d.labels else none) = some target
    rw [decodeName_encodeName_at pre rest target hok hcap]
    show (if wireLen target = (encodeName target).length
          then some target else none) = some target
    rw [encodeName_length]
    simp
  have hbranch : typedRData (pre ++ (encodeName target ++ rest))
      ⟨{ name := nm, rrType := 12, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.ptr target) }, pre.length⟩
      = match rdataName (pre ++ (encodeName target ++ rest))
          ⟨{ name := nm, rrType := 12, rrClass := cls, ttl := ttl,
             rdata := encodeRData (.ptr target) }, pre.length⟩ with
        | none => none
        | some n => some (.ptr n) := rfl
  rw [hbranch, hrd]

/-- MX (RFC 1035 §3.3.9): preference and exchange roundtrip, embedded at the
RDATA's true offset (preference 16-bit, exchange a legal name). -/
theorem typedRData_encode_mx (pre rest : Bytes) (nm exch : List (List UInt8)) (cls ttl pref : Nat)
    (hpref : pref < 65536) (hok : LabelsOk exch) (hcap : wireLen exch ≤ maxName) :
    typedRData (pre ++ (encodeRData (.mx pref exch) ++ rest))
      ⟨{ name := nm, rrType := 15, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.mx pref exch) }, pre.length⟩
      = some (.mx pref exch) := by
  have hshape : encodeRData (.mx pref exch)
      = UInt8.ofNat (pref / 256) :: UInt8.ofNat pref :: encodeName exch := by
    simp [encodeRData, putBe]
  have hbranch : typedRData (pre ++ (encodeRData (.mx pref exch) ++ rest))
      ⟨{ name := nm, rrType := 15, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.mx pref exch) }, pre.length⟩
      = if 2 ≤ (encodeRData (.mx pref exch)).length then
          match decodeName (pre ++ (encodeRData (.mx pref exch) ++ rest))
              (pre.length + 2) with
          | .error _ => none
          | .ok d =>
            if 2 + d.consumed = (encodeRData (.mx pref exch)).length
            then some (.mx (be16At (encodeRData (.mx pref exch)) 0) d.labels)
            else none
        else none := rfl
  have hlen2 : 2 ≤ (encodeRData (.mx pref exch)).length := by
    rw [hshape]; simp [List.length_cons]
  -- re-associate: the exchange name starts at offset pre.length + 2
  have hassoc : pre ++ (encodeRData (.mx pref exch) ++ rest)
      = (pre ++ [UInt8.ofNat (pref / 256), UInt8.ofNat pref])
          ++ (encodeName exch ++ rest) := by
    rw [hshape]; simp
  have hofflen : pre.length + 2
      = (pre ++ [UInt8.ofNat (pref / 256), UInt8.ofNat pref]).length := by
    simp [List.length_append]
  have hdec : decodeName (pre ++ (encodeRData (.mx pref exch) ++ rest))
      (pre.length + 2) = .ok ⟨exch, wireLen exch⟩ := by
    rw [hassoc, hofflen]
    exact decodeName_encodeName_at _ rest exch hok hcap
  rw [hbranch, if_pos hlen2, hdec]
  have hconsumed : 2 + wireLen exch = (encodeRData (.mx pref exch)).length := by
    rw [hshape]
    simp [List.length_cons, encodeName_length]
    omega
  show (if 2 + wireLen exch = (encodeRData (.mx pref exch)).length
        then some (RData.mx (be16At (encodeRData (.mx pref exch)) 0) exch)
        else none) = some (RData.mx pref exch)
  rw [if_pos hconsumed]
  have h16 : be16At (encodeRData (.mx pref exch)) 0 = pref := by
    rw [hshape]
    simp only [be16At, List.getD_cons_zero, List.getD_cons_succ]
    exact be16_putU16 pref hpref
  rw [h16]

/-! ## Compression-pointer composition (RFC 1035 §4.1.4) -/

/-- Write a compression pointer to message offset `off` (legal for
`off < 2^14`): the two-octet `11`-prefixed form of §4.1.4. -/
def encodePtr (off : Nat) : Bytes :=
  [UInt8.ofNat (192 + off / 256), UInt8.ofNat off]

/-- A pointer always occupies exactly 2 octets — pointing at a prior name is
never longer than any nonempty name it replaces. -/
theorem encodePtr_length (off : Nat) : (encodePtr off).length = 2 := rfl

/-- **The pointer roundtrip.** If the message carries an `encodeName`-written
name at offset `off < 2^14`, then an `encodePtr off` written at any position
`i` decodes — through the deployed pointer-chasing decoder — to exactly that
name, consuming exactly the 2 pointer octets. The compressing composer and
`Dns.decodeName` agree. -/
theorem decodeName_encodePtr (msg : Bytes) (i off : Nat) (ls : List (List UInt8))
    (rest rest2 : Bytes)
    (hptr : msg.drop i = encodePtr off ++ rest)
    (hoff : off < 16384)
    (hname : msg.drop off = encodeName ls ++ rest2)
    (hok : LabelsOk ls) (hcap : wireLen ls ≤ maxName) :
    decodeName msg i = .ok ⟨ls, 2⟩ := by
  -- the two pointer octets, read out of the message
  have h0 : msg[i]? = some (UInt8.ofNat (192 + off / 256)) := by
    have hg : (msg.drop i)[0]? = msg[i]? := by simp [List.getElem?_drop]
    rw [← hg, hptr]; rfl
  have h1 : msg[i + 1]? = some (UInt8.ofNat off) := by
    have hg : (msg.drop i)[1]? = msg[i + 1]? := by simp [List.getElem?_drop]
    rw [← hg, hptr]; simp [encodePtr]
  have ht0 : (UInt8.ofNat (192 + off / 256)).toNat = 192 + off / 256 := by
    rw [UInt8.toNat_ofNat]; omega
  -- the name run at the pointer target
  have hfuel : ls.length < msg.length + 1 := by
    have h2 := congrArg List.length hname
    rw [List.length_drop, List.length_append, encodeName_length] at h2
    have h3 := length_le_labelsLen ls
    have hw : wireLen ls = labelsLen ls + 1 := rfl
    omega
  have hrun := readRun_encodeName msg ls off (msg.length + 1) [] rest2 hname hok
    (by simpa using hcap) hfuel
  have hchain : followChain msg off [] = .okName ls := by
    have := followChain_complete msg off [] ([] ++ ls) (off + labelsLen ls + 1) hrun
    simpa using this
  -- the pointer read is a jump to `off`
  have hjump : readRun msg i [] (msg.length + 1) = .jump off [] (i + 2) := by
    show readRun msg i [] (Nat.succ msg.length) = .jump off [] (i + 2)
    unfold readRun
    rw [h0]
    dsimp only
    rw [ht0]
    rw [if_neg (by omega), if_pos (by omega), h1]
    dsimp only
    rw [UInt8.toNat_ofNat]
    have htarget : (192 + off / 256) % 64 * 256 + off % 256 = off := by omega
    rw [htarget]
  unfold decodeName
  rw [hjump]
  dsimp only
  rw [hchain]
  dsimp only
  have : i + 2 - i = 2 := by omega
  rw [this]

/-! ## Worked roundtrip vectors (the record shapes proven above by theorem are
joined by kernel-checked vectors for the multi-name/multi-field shapes) -/

/-- SOA roundtrip on concrete values, RDATA embedded at offset 2. -/
example :
    typedRData ([0xAA, 0xBB] ++ encodeRData (.soa [[110, 115]] [[104, 109]]
        305419896 7200 3600 1209600 300))
      ⟨{ name := [], rrType := 6, rrClass := 1, ttl := 60,
         rdata := encodeRData (.soa [[110, 115]] [[104, 109]]
           305419896 7200 3600 1209600 300) }, 2⟩
      = some (.soa [[110, 115]] [[104, 109]] 305419896 7200 3600 1209600 300) := by
  decide

/-- RRSIG roundtrip on concrete values (type covered A, algorithm 13, signer
`up`, 2-octet signature), RDATA at offset 0. -/
example :
    typedRData (encodeRData (.rrsig 1 13 2 3600 1720000000 1710000000 4711
        [[117, 112]] [0xAB, 0xCD]))
      ⟨{ name := [], rrType := 46, rrClass := 1, ttl := 60,
         rdata := encodeRData (.rrsig 1 13 2 3600 1720000000 1710000000 4711
           [[117, 112]] [0xAB, 0xCD]) }, 0⟩
      = some (.rrsig 1 13 2 3600 1720000000 1710000000 4711
          [[117, 112]] [0xAB, 0xCD]) := by decide

/-- NSEC roundtrip (next name `up`, one bitmap block). -/
example :
    typedRData (encodeRData (.nsec [[117, 112]] [0, 1, 0x40]))
      ⟨{ name := [], rrType := 47, rrClass := 1, ttl := 60,
         rdata := encodeRData (.nsec [[117, 112]] [0, 1, 0x40]) }, 0⟩
      = some (.nsec [[117, 112]] [0, 1, 0x40]) := by decide

/-- NSEC3 roundtrip (RFC 5155 §3.2 shape). -/
example :
    typedRData []
      ⟨{ name := [], rrType := 50, rrClass := 1, ttl := 60,
         rdata := encodeRData (.nsec3 1 1 0 [0xAB, 0xCD] [0x11, 0x22, 0x33]
           [0, 1, 0x40]) }, 0⟩
      = some (.nsec3 1 1 0 [0xAB, 0xCD] [0x11, 0x22, 0x33] [0, 1, 0x40]) := by decide

/-- SVCB/HTTPS roundtrip (priority 1, target `up`, alpn + port params),
RDATA at offset 0. -/
example :
    typedRData (encodeRData (.svcb 1 [[117, 112]]
        [(1, [2, 104, 51]), (3, [0x01, 0xBB])]))
      ⟨{ name := [], rrType := 65, rrClass := 1, ttl := 60,
         rdata := encodeRData (.svcb 1 [[117, 112]]
           [(1, [2, 104, 51]), (3, [0x01, 0xBB])]) }, 0⟩
      = some (.svcb 1 [[117, 112]] [(1, [2, 104, 51]), (3, [0x01, 0xBB])]) := by decide

/-- OPT options roundtrip: an encoded cookie option reads back through the
proven TLV walk. -/
example :
    typedRData []
      ⟨{ name := [], rrType := 41, rrClass := 1232, ttl := 0,
         rdata := encodeRData (.opt 1232 0 0 false
           [(10, [1, 2, 3, 4, 5, 6, 7, 8])]) }, 0⟩
      = some (.opt 1232 0 0 false [(10, [1, 2, 3, 4, 5, 6, 7, 8])]) := by decide

/-- A compressed name in a worked message: `encodePtr 0` at offset 13 resolves
to the name written at offset 0 — by the pointer-roundtrip theorem, not by
computation (the chase is well-founded recursion). -/
example :
    decodeName (encodeName [[117, 112]] ++ ([0xFF] ++ (encodePtr 0 ++ [0xEE]))) 5
      = .ok ⟨[[117, 112]], 2⟩ := by
  refine decodeName_encodePtr _ 5 0 [[117, 112]] [0xEE]
    (([0xFF] ++ (encodePtr 0 ++ [0xEE]))) ?_ (by omega) ?_ ?_ ?_
  · decide
  · decide
  · intro lab hl
    simp at hl
    subst hl
    decide
  · decide

end Dns
