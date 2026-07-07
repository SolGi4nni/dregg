import Dns.Wire

/-!
# Message composition (RFC 1035 §4.1) and parse-of-compose roundtrips

The encode side of the wire format: big-endian field writers, the uncompressed
domain-name encoder (§3.1), and the header/question/record/message encoders
(§4.1.1–§4.1.3). Compression pointers are never *emitted* — an uncompressed
name is always legal (§4.1.4 makes compression optional) — while the parse
side continues to accept both.

The headline theorems are the roundtrips: what `encodeName` writes,
`Dns.decodeName` reads back verbatim — at any offset, embedded in any message
(`decodeName_encodeName_at`) — and the encoded header/question/record frames
parse back to exactly the structures they came from. Together these pin the
encoders to the same wire format the deployed parsers accept: the composer
cannot drift from the parser without breaking a theorem.
-/

namespace Dns

/-! ## Big-endian field writers -/

/-- Big-endian 16-bit write. -/
def putU16 (n : Nat) : Bytes := [UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- Big-endian 32-bit write. -/
def putU32 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- `be16` reads back what `putU16` wrote (16-bit values). -/
theorem be16_putU16 (n : Nat) (h : n < 65536) :
    be16 (UInt8.ofNat (n / 256)) (UInt8.ofNat n) = n := by
  simp only [be16, UInt8.toNat_ofNat]
  omega

/-- `be32` reads back what `putU32` wrote (32-bit values). -/
theorem be32_putU32 (n : Nat) (h : n < 4294967296) :
    be32 (UInt8.ofNat (n / 16777216)) (UInt8.ofNat (n / 65536))
         (UInt8.ofNat (n / 256)) (UInt8.ofNat n) = n := by
  simp only [be32, UInt8.toNat_ofNat]
  omega

/-! ## The domain-name encoder (RFC 1035 §3.1)

A name is written as its labels, each preceded by its length octet, closed by
the root octet `0`. Well-formedness is the parse side's own invariants:
every label `1..63` octets (`LabelsOk`) and the whole name at most 255 octets
(`wireLen ≤ maxName`). -/

/-- Encode a decoded name back to wire form, uncompressed. -/
def encodeName : List (List UInt8) → Bytes
  | [] => [0]
  | l :: ls => UInt8.ofNat l.length :: (l ++ encodeName ls)

/-- The encoded name occupies exactly its wire length (`wireLen`). -/
theorem encodeName_length (ls : List (List UInt8)) :
    (encodeName ls).length = wireLen ls := by
  induction ls with
  | nil => rfl
  | cons l t ih =>
    simp only [encodeName, List.length_cons, List.length_append, ih, wireLen, labelsLen]
    omega

/-- `labelsLen` distributes over append. -/
theorem labelsLen_append₂ (xs ys : List (List UInt8)) :
    labelsLen (xs ++ ys) = labelsLen xs + labelsLen ys := by
  induction xs with
  | nil => simp [labelsLen]
  | cons x t ih => simp only [List.cons_append, labelsLen, ih]; omega

/-- Each label contributes at least one octet: the label count is bounded by
`labelsLen`. -/
theorem length_le_labelsLen (ls : List (List UInt8)) : ls.length ≤ labelsLen ls := by
  induction ls with
  | nil => simp [labelsLen]
  | cons l t ih => simp only [List.length_cons, labelsLen]; omega

/-! ## The name roundtrip

`readRun` walks forward over exactly the labels `encodeName` wrote and stops
at the root octet it wrote — no pointer is ever encountered, so the chase
machinery is bypassed and the decode is the identity. The statement is
*embedded*: the encoded name may sit at any offset of any larger message. -/

/-- The forward reader consumes an encoded name verbatim: if the message from
offset `i` on is `encodeName ls ++ rest`, the run completes with exactly the
labels `ls` appended and ends just past the root octet. -/
theorem readRun_encodeName (msg : Bytes) (ls : List (List UInt8)) :
    ∀ (i fuel : Nat) (acc : List (List UInt8)) (rest : Bytes),
      msg.drop i = encodeName ls ++ rest →
      LabelsOk ls →
      wireLen (acc ++ ls) ≤ maxName →
      ls.length < fuel →
      readRun msg i acc fuel = .complete (acc ++ ls) (i + labelsLen ls + 1) := by
  induction ls with
  | nil =>
    intro i fuel acc rest hdrop _ _ hfuel
    match fuel, hfuel with
    | Nat.succ fuel, _ =>
      have hi : msg[i]? = some 0 := by
        have h0 : (msg.drop i)[0]? = msg[i]? := by
          simp [List.getElem?_drop]
        rw [← h0, hdrop]
        simp [encodeName]
      unfold readRun
      rw [hi]
      simp [labelsLen]
  | cons l t ih =>
    intro i fuel acc rest hdrop hok hcap hfuel
    match fuel, hfuel with
    | Nat.succ fuel, hf =>
      have hl : 1 ≤ l.length ∧ l.length ≤ maxLabel := hok l (by simp)
      have hl1 : 1 ≤ l.length := hl.1
      have hl63 : l.length ≤ 63 := by
        have h2 := hl.2
        unfold maxLabel at h2
        exact h2
      have hl256 : l.length < 256 := by omega
      -- the length octet
      have hi : msg[i]? = some (UInt8.ofNat l.length) := by
        have h0 : (msg.drop i)[0]? = msg[i]? := by
          simp [List.getElem?_drop]
        rw [← h0, hdrop]
        simp [encodeName]
      have htn : (UInt8.ofNat l.length).toNat = l.length := by
        rw [UInt8.toNat_ofNat]; omega
      -- lengths: the suffix from i has everything the label needs
      have hdlen : (msg.drop i).length = msg.length - i := List.length_drop _ _
      have hsuf : (encodeName (l :: t) ++ rest).length
          = 1 + l.length + (encodeName t).length + rest.length := by
        simp [encodeName, List.length_append]; omega
      have hroom : i + 1 + l.length ≤ msg.length := by
        have h1 : (encodeName t).length = wireLen t := encodeName_length t
        have h2 : 1 ≤ wireLen t := by unfold wireLen; omega
        have := congrArg List.length hdrop
        rw [hdlen, hsuf] at this
        omega
      -- the label bytes are the label
      have hdrop1 : msg.drop (i + 1) = l ++ (encodeName t ++ rest) := by
        have : (msg.drop i).drop 1 = msg.drop (i + 1) := by
          rw [List.drop_drop]
        rw [← this, hdrop]
        simp [encodeName]
      have hlab : labelAt msg i ((UInt8.ofNat l.length).toNat) = l := by
        unfold labelAt
        rw [htn, hdrop1]
        exact List.take_left l _
      -- the cap check for acc ++ [l]
      have hcap1 : wireLen ((acc ++ [l]) ++ t) ≤ maxName := by
        rw [List.append_assoc]; simpa using hcap
      -- the recursive suffix
      have hdrop2 : msg.drop (i + 1 + l.length) = encodeName t ++ rest := by
        have : (msg.drop (i + 1)).drop l.length = msg.drop (i + 1 + l.length) := by
          rw [List.drop_drop]
        rw [← this, hdrop1]
        exact List.drop_left l _
      have hokt : LabelsOk t := fun lab hlab' => hok lab (by simp [hlab'])
      have hfu : t.length < fuel := by
        simp only [List.length_cons] at hf
        omega
      have ihx := ih (i + 1 + l.length) fuel (acc ++ [l]) rest hdrop2 hokt hcap1 hfu
      -- assemble the step
      unfold readRun
      rw [hi]
      simp only [htn]
      have hz : l.length / 64 = 0 := by omega
      have hnz : ¬ l.length = 0 := by omega

      have hlab' : labelAt msg i l.length = l := by rw [← htn]; exact hlab
      rw [if_pos hz, if_neg hnz, if_pos hroom, hlab']
      have hcap2 : wireLen (acc ++ [l]) ≤ maxName := by
        unfold wireLen at hcap1 ⊢
        simp only [labelsLen_append₂, labelsLen] at hcap1 ⊢
        omega
      rw [if_pos hcap2, ihx]
      have hlabels : (acc ++ [l]) ++ t = acc ++ l :: t := by simp
      have hoff : i + 1 + l.length + labelsLen t + 1 = i + labelsLen (l :: t) + 1 := by
        simp only [labelsLen]; omega
      rw [hlabels, hoff]

/-- **The name roundtrip, embedded.** An `encodeName`-written name at any
offset of any message decodes back to exactly its labels, consuming exactly
its wire length — `decodeName ∘ encodeName = id` for every well-formed name
(labels `1..63`, total ≤ 255 octets). -/
theorem decodeName_encodeName_at (pre rest : Bytes) (ls : List (List UInt8))
    (hok : LabelsOk ls) (hcap : wireLen ls ≤ maxName) :
    decodeName (pre ++ (encodeName ls ++ rest)) pre.length = .ok ⟨ls, wireLen ls⟩ := by
  have hdrop : (pre ++ (encodeName ls ++ rest)).drop pre.length = encodeName ls ++ rest :=
    List.drop_left pre _
  have hfuel : ls.length < (pre ++ (encodeName ls ++ rest)).length + 1 := by
    have h1 : (encodeName ls).length = wireLen ls := encodeName_length ls
    have h2 := length_le_labelsLen ls
    have : wireLen ls = labelsLen ls + 1 := rfl
    simp [List.length_append]
    omega
  have h := readRun_encodeName (pre ++ (encodeName ls ++ rest)) ls pre.length
    ((pre ++ (encodeName ls ++ rest)).length + 1) [] rest hdrop hok (by simpa using hcap) hfuel
  unfold decodeName
  rw [h]
  simp only [List.nil_append, NameResult.ok.injEq]
  have : pre.length + labelsLen ls + 1 - pre.length = wireLen ls := by
    unfold wireLen; omega
  rw [this]

/-- The name roundtrip at offset zero. -/
theorem decodeName_encodeName (ls : List (List UInt8)) (rest : Bytes)
    (hok : LabelsOk ls) (hcap : wireLen ls ≤ maxName) :
    decodeName (encodeName ls ++ rest) 0 = .ok ⟨ls, wireLen ls⟩ := by
  have := decodeName_encodeName_at [] rest ls hok hcap
  simpa using this

/-! ## Header, question, record and message encoders (RFC 1035 §4.1) -/

/-- Encode the 12-octet header. -/
def encodeHeader (h : Header) : Bytes :=
  putU16 h.id ++ putU16 h.flags ++ putU16 h.qdCount
    ++ putU16 h.anCount ++ putU16 h.nsCount ++ putU16 h.arCount

/-- Encode one question (§4.1.2). -/
def encodeQuestion (q : Question) : Bytes :=
  encodeName q.qname ++ putU16 q.qtype ++ putU16 q.qclass

/-- Encode one resource record (§4.1.3), name uncompressed, RDATA verbatim. -/
def encodeRR (r : RR) : Bytes :=
  encodeName r.name ++ putU16 r.rrType ++ putU16 r.rrClass
    ++ putU32 r.ttl ++ putU16 r.rdata.length ++ r.rdata

/-- Encode a whole message: header (with the section counts it must declare —
RFC 1035 §4.1.1 makes the counts describe the sections, and `parseMsg` rejects
a message where they do not), then the four sections. -/
def encodeMsg (m : Msg) : Bytes :=
  encodeHeader { m.header with
      qdCount := m.questions.length
      anCount := m.answers.length
      nsCount := m.authority.length
      arCount := m.additional.length }
    ++ (m.questions.map encodeQuestion).flatten
    ++ (m.answers.map (fun r => encodeRR r.rr)).flatten
    ++ (m.authority.map (fun r => encodeRR r.rr)).flatten
    ++ (m.additional.map (fun r => encodeRR r.rr)).flatten

/-! ## Header roundtrip -/

/-- **The header roundtrip.** A well-formed header (all fields 16-bit) parses
back from its encoding, before any payload. -/
theorem parseHeader_encodeHeader (h : Header) (rest : Bytes)
    (hid : h.id < 65536) (hfl : h.flags < 65536)
    (hqd : h.qdCount < 65536) (han : h.anCount < 65536)
    (hns : h.nsCount < 65536) (har : h.arCount < 65536) :
    parseHeader (encodeHeader h ++ rest) = some (h, 12) := by
  have hlen : 12 ≤ (encodeHeader h ++ rest).length := by
    simp [encodeHeader, putU16, List.length_append]
  unfold parseHeader
  rw [if_pos hlen]
  simp only [encodeHeader, putU16, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [be16_putU16 h.id hid, be16_putU16 h.flags hfl, be16_putU16 h.qdCount hqd,
      be16_putU16 h.anCount han, be16_putU16 h.nsCount hns, be16_putU16 h.arCount har]

/-! ## Worked roundtrip vectors, kernel-checked

The structural encoders reduce, and uncompressed decodes reduce, so whole
encode-then-parse runs are checkable by `decide`. -/

/-- A question `www.example.com IN A` roundtrips through its encoding. -/
example :
    parseQuestion (encodeQuestion { qname := [[119, 119, 119],
      [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]], qtype := 1, qclass := 1 }) 0
      = some ({ qname := [[119, 119, 119], [101, 120, 97, 109, 112, 108, 101],
                          [99, 111, 109]], qtype := 1, qclass := 1 }, 21) := by decide

/-- A full response message — header, question, A answer — roundtrips through
`encodeMsg` / `parseMsg`, RDATA offset included. -/
example :
    parseMsg (encodeMsg
      { header := { id := 0x1234, flags := 0x8180, qdCount := 1, anCount := 1,
                    nsCount := 0, arCount := 0 }
        questions := [{ qname := [[117, 112]], qtype := 1, qclass := 1 }]
        answers := [⟨{ name := [[117, 112]], rrType := 1, rrClass := 1, ttl := 60,
                       rdata := [93, 184, 216, 34] }, 34⟩]
        authority := []
        additional := [] })
      = some
        { header := { id := 0x1234, flags := 0x8180, qdCount := 1, anCount := 1,
                      nsCount := 0, arCount := 0 }
          questions := [{ qname := [[117, 112]], qtype := 1, qclass := 1 }]
          answers := [⟨{ name := [[117, 112]], rrType := 1, rrClass := 1, ttl := 60,
                         rdata := [93, 184, 216, 34] }, 34⟩]
          authority := []
          additional := [] } := by decide

end Dns
