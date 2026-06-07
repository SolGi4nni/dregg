/-
# Dregg2.Exec.SigningMessage — byte-exact signing-message preimage builders (the signing-hole guard).

The §8 `AuthPortal` routes every credential to `CryptoKernel.verify stmt sig`, but `stmt` is opaque
there. If the preimage is reconstructed even one byte differently from what dregg1 actually signs, the
portal verifies the wrong message. This module provides the byte-exact preimage builders, ported
field-for-field from dregg1 (`turn/src/executor/authorize.rs:1713-1880`, `turn/src/action.rs:606-635`,
`captp/src/handoff.rs:193-...`), and proves three structural-correctness properties:

  * **Domain-separator present + distinct per kind** — each preimage is prefixed by its kind's
    domain separator (`sigMsg*_hasPrefix`), and no two kinds share a separator
    (`domainSep_injective`): cross-protocol preimage collision is impossible.
  * **Binding** — tampering any bound field changes the preimage: a different `target`,
    `mayDelegate`, `commitmentMode`, `federationId`, `nonce`, `actionHash`, `ephemeralPk`, or
    `expiresAt` yields a different preimage, so a signature over one `(action, resource)` cannot
    be replayed against another.

The digest `CryptoKernel.verify` checks is `BLAKE3(preimage)` (or, for `Custom`, the raw preimage
the predicate AIR absorbs). BLAKE3's collision/preimage resistance is assumed at the §8 portal
(`CryptoKernel`); what this module proves is that the preimage commits to the right fields.

OPEN: the Rust `bytes == bytes` differential is the ultimate byte-fidelity certification; the
`#eval`s here confirm each separator literal equals `ascii "dregg-…"` of the dregg1 domain string.

Reuses only byte primitives defined here.
-/
import Dregg2.Tactics

namespace Dregg2.Exec.SigningMessage

/-! ## §0 — Byte primitives: the little-endian encoders dregg1's preimage builders use.

The preimage is the concatenation of byte fields (`hasher.update(x)` appends `x`'s bytes). We model
bytes as `List UInt8` with the encoders dregg1 uses: `u64.to_le_bytes()`, `u32.to_le_bytes()`,
`i64.to_le_bytes()` (all little-endian). A `Digest`/`Pubkey`/`Sig` is a 32-byte `List UInt8`
carried verbatim. -/

/-- A byte string: the preimage type (`hasher.update`-concatenation). -/
abbrev ByteString := List UInt8

/-- `u64.to_le_bytes()` — 8 little-endian bytes of a `UInt64`. -/
def u64le (x : UInt64) : ByteString :=
  [ x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
    (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8 ]

/-- `u32.to_le_bytes()` — 4 little-endian bytes of a `UInt32` (dregg1 length-prefixes `Custom` blobs with this). -/
def u32le (x : UInt32) : ByteString :=
  [ x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8 ]

/-- `(n as u32).to_le_bytes()` from a `Nat` length. -/
def u32leOfNat (n : Nat) : ByteString := u32le (UInt32.ofNat n)

/-- `i64.to_le_bytes()` — 8 little-endian bytes of a signed `Int64` (two's complement, matching Rust's
`i64::to_le_bytes`). Used for `balance_change` deltas. -/
def i64le (x : Int) : ByteString :=
  u64le (UInt64.ofInt x)

/-- A 32-byte digest / public key / signature half, appended verbatim into the preimage (no length
prefix). The 32-byte shape is a dregg1 side condition; the binding theorems hold for any byte content. -/
abbrev Bytes32 := ByteString

/-- The ASCII bytes of a string literal — the fidelity oracle for separator literals (`#eval`s check
`domainSep k = ascii "dregg-…"`). Not used inside the `decide`-proved distinctness (the kernel cannot
reduce `String.toUTF8` under `decide`). -/
def ascii (s : String) : ByteString := s.toUTF8.toList

/-! ### Domain-separator literals (explicit `List UInt8` so `decide` can check pairwise distinctness).

The `#eval`s in §8 certify each literal equals `ascii "…"` of the matching dregg1 string. -/

/-- `b"dregg-action-sig-v2:"` — the Signature-path separator. -/
def sepFull : ByteString :=
  [100,114,101,103,103,45,97,99,116,105,111,110,45,115,105,103,45,118,50,58]
/-- `b"dregg-partial-sig-v2:"` — the partial-commitment separator. -/
def sepPartial : ByteString :=
  [100,114,101,103,103,45,112,97,114,116,105,97,108,45,115,105,103,45,118,50,58]
/-- `b"dregg-custom-sig-v1:"` — the custom-predicate separator. -/
def sepCustom : ByteString :=
  [100,114,101,103,103,45,99,117,115,116,111,109,45,115,105,103,45,118,49,58]
/-- `b"dregg-stealth-sig-v1:"` — the stealth one-time-key separator. -/
def sepStealth : ByteString :=
  [100,114,101,103,103,45,115,116,101,97,108,116,104,45,115,105,103,45,118,49,58]
/-- `b"dregg-bearer-delegation-v1:"` — the bearer-delegation separator. -/
def sepBearer : ByteString :=
  [100,114,101,103,103,45,98,101,97,114,101,114,45,100,101,108,101,103,97,116,105,111,110,45,118,49,58]
/-- `b"dregg-handoff-cert-v1"` — the CapTP handoff-cert separator (NO trailing `:` — dregg1 omits it). -/
def sepHandoff : ByteString :=
  [100,114,101,103,103,45,104,97,110,100,111,102,102,45,99,101,114,116,45,118,49]

/-! ## §1 — Turn-record fields the preimage binds (ported from dregg1).

`SigningAction` is the Lean projection of dregg1's `Action` (`turn/src/action.rs:68`), carrying exactly
the fields `compute_signing_message` absorbs, in order:
  target · method · args · effect.hash()* · may_delegate · commitment_mode ·
  balance_change · postcard(preconditions).

`mayDelegate`/`commitmentMode` are single discriminant bytes; `balanceChange` uses a
`0u8`/`1u8`+`i64le` discriminant; `precondBytes` is the opaque postcard serialization (the preimage
commits to it; its internal grammar is the codec's concern). -/

/-- The signed projection of a dregg1 `Action`: exactly the fields the preimage binds. -/
structure SigningAction where
  /-- `action.target.as_bytes()` (32-byte cell id). -/
  target        : Bytes32
  /-- `action.method` (32-byte hashed symbol). -/
  method        : Bytes32
  /-- `action.args` — each a 32-byte field element, in order. -/
  args          : List Bytes32
  /-- `action.effects[i].hash()` — each effect's 32-byte BLAKE3 digest, in order. -/
  effectHashes  : List Bytes32
  /-- `action.may_delegate as u8` — the `DelegationMode` discriminant byte. -/
  mayDelegate   : UInt8
  /-- `action.commitment_mode as u8` — the `CommitmentMode` discriminant byte (Full=0, Partial=1). -/
  commitmentMode : UInt8
  /-- `action.balance_change : Option<i64>`. -/
  balanceChange : Option Int
  /-- `postcard::to_allocvec(&action.preconditions)` — opaque serialized preconditions. -/
  precondBytes  : ByteString
  deriving DecidableEq, Repr

/-- `action.hash()` (`turn/src/action.rs:1472`) — the 32-byte action digest the partial/stealth
preimages absorb instead of re-listing the full body. Carried as an opaque 32-byte field; it suffices
that the preimage commits to it (a different action ⇒ a different `actionHash` ⇒ a different preimage). -/
abbrev ActionHash := Bytes32

/-- The `Option<i64> balance_change` byte encoding: `Some d ⇒ 0x01 :: d.to_le_bytes()`,
`None ⇒ [0x00]` — the discriminant-prefixed malleability guard. -/
def balByte : Option Int → ByteString
  | some d => (1 : UInt8) :: i64le d
  | none   => [(0 : UInt8)]

/-- The optional `vk_hash` tail: the `Custom` arm appends its 32-byte `vk_hash` inline; all other arms append nothing. -/
def vkTail : Option Bytes32 → ByteString
  | some vk => vk
  | none    => []

/-- `Option<u64>` field encoding (`captp/handoff.rs`): `Some n ⇒ 0x01 :: n.to_le_bytes()`, `None ⇒ [0x00]`. -/
def optU64 : Option UInt64 → ByteString
  | some n => (1 : UInt8) :: u64le n
  | none   => [(0 : UInt8)]

/-! ## §2 — Preimage builders (byte-exact, field-for-field with dregg1).

Each `def` mirrors one Rust `compute_*` function, appending bytes in the same order. The domain
separator is the prefix. These produce the preimage — the message fed to `BLAKE3` or the AIR — not
the hash. -/

/-- **(1) Signature path** (`compute_signing_message`, `authorize.rs:1750`):
`sepFull · federation_id · target · method · args · effect.hash()* · [may_delegate] ·
[commitment_mode] · balance_change · postcard(preconditions)`. -/
def sigMsgFull (a : SigningAction) (federationId : Bytes32) : ByteString :=
  sepFull
    ++ federationId
    ++ a.target
    ++ a.method
    ++ a.args.flatten
    ++ a.effectHashes.flatten
    ++ [a.mayDelegate]
    ++ [a.commitmentMode]
    ++ balByte a.balanceChange
    ++ a.precondBytes

/-- **(2) Partial commitment** (`compute_partial_signing_message`, `authorize.rs:1801`):
`sepPartial · federation_id · action.hash() · position · turn_nonce`. -/
def sigMsgPartial (ah : ActionHash) (federationId : Bytes32) (position : UInt64)
    (turnNonce : UInt64) : ByteString :=
  sepPartial ++ federationId ++ ah ++ u64le position ++ u64le turnNonce

/-- **(3) Custom predicate** (`compute_custom_signing_message`, `authorize.rs:1842`): returns the full
byte vector (not a hash) because the predicate AIR absorbs it. Variable-length blobs are `u32`-le
length-prefixed. `sepCustom · federation_id · turn_nonce · position · target · method · args ·
effect.hash()* · [may_delegate] · [commitment_mode] · balance_change · (len(preconds) as u32) ·
preconds · (len(predicate) as u32) · predicate`. -/
def sigMsgCustom (a : SigningAction) (predBytes : ByteString) (position : UInt64)
    (federationId : Bytes32) (turnNonce : UInt64) : ByteString :=
  sepCustom
    ++ federationId
    ++ u64le turnNonce
    ++ u64le position
    ++ a.target
    ++ a.method
    ++ a.args.flatten
    ++ a.effectHashes.flatten
    ++ [a.mayDelegate]
    ++ [a.commitmentMode]
    ++ balByte a.balanceChange
    ++ u32leOfNat a.precondBytes.length
    ++ a.precondBytes
    ++ u32leOfNat predBytes.length
    ++ predBytes

/-- **(4) Stealth** (`Authorization::stealth_signing_message`, `action.rs:618`):
`sepStealth · federation_id · action.hash() · ephemeral_pubkey · blinding_scalar · position · turn_nonce`. -/
def sigMsgStealth (ah : ActionHash) (federationId ephemeralPk blindingScalar : Bytes32)
    (position : UInt64) (turnNonce : UInt64) : ByteString :=
  sepStealth ++ federationId ++ ah ++ ephemeralPk ++ blindingScalar
    ++ u64le position ++ u64le turnNonce

/-- **(5) Bearer delegation** (`compute_bearer_delegation_message`, `authorize.rs:1713`):
`sepBearer · federation_id · target · [perm_byte] · (perm==Custom ⇒ vk_hash) · bearer_pk · expires_at`.
The permission-lattice byte is the discriminant (None=0,…,Custom=5); `Custom` appends its 32-byte `vk_hash`. -/
def sigMsgBearer (target : Bytes32) (permByte : UInt8) (customVkHash : Option Bytes32)
    (bearerPk : Bytes32) (expiresAt : UInt64) (federationId : Bytes32) : ByteString :=
  sepBearer ++ federationId ++ target ++ [permByte] ++ vkTail customVkHash
    ++ bearerPk ++ u64le expiresAt

/-- **(6) CapTP handoff certificate** (`HandoffCertificate::signing_message`, `captp/handoff.rs:193`),
the message the introducer signs.
`sepHandoff · introducer · target_federation · target_cell · recipient_pk · [perm_byte] ·
(perm==Custom ⇒ vk_hash) · allowed_effects-opt · expires_at-opt · max_uses-opt`.
The three trailing `Option` fields use a `0x00`/`0x01`+`u64le` discriminant. -/
def sigMsgHandoffCert (introducer targetFederation targetCell recipientPk : Bytes32)
    (permByte : UInt8) (customVkHash : Option Bytes32)
    (allowedEffects : Option UInt64) (expiresAt : Option UInt64) (maxUses : Option UInt64) :
    ByteString :=
  sepHandoff ++ introducer ++ targetFederation ++ targetCell ++ recipientPk
    ++ [permByte] ++ vkTail customVkHash
    ++ optU64 allowedEffects ++ optU64 expiresAt ++ optU64 maxUses

/-! ## §3 — Signing-message kind + per-kind domain separator.

The kind tag selects the preimage builder; its domain separator is the preimage's mandatory prefix.
Constructors are `k`-prefixed to avoid the reserved `partial`/`custom`/`full` tokens. -/

/-- The signing-message kind (one per dregg1 preimage builder). -/
inductive SigKind where
  | kFull       -- Signature path (`compute_signing_message`)
  | kPartial    -- Partial-commitment (`compute_partial_signing_message`)
  | kCustom     -- Custom predicate (`compute_custom_signing_message`)
  | kStealth    -- Stealth one-time-key (`stealth_signing_message`)
  | kBearer     -- Bearer delegation (`compute_bearer_delegation_message`)
  | kHandoff    -- CapTP handoff cert (`HandoffCertificate::signing_message`)
  deriving DecidableEq, Repr

/-- The per-kind domain separator (the preimage's mandatory prefix). -/
def domainSep : SigKind → ByteString
  | .kFull    => sepFull
  | .kPartial => sepPartial
  | .kCustom  => sepCustom
  | .kStealth => sepStealth
  | .kBearer  => sepBearer
  | .kHandoff => sepHandoff

/-! ## §4 — `u64le` injectivity.

Distinct `UInt64`s have distinct 8-byte little-endian encodings. Proved via a left inverse
`u64leDecode` (`Σ bᵢ · 256ⁱ` recovers `toNat`), giving injectivity via `toNat`-injectivity. -/

/-- Recover the value from its 8 little-endian bytes: `Σ bᵢ · 256ⁱ` (left inverse of `u64le`). -/
def u64leDecode (bs : ByteString) : Nat :=
  match bs with
  | [b0,b1,b2,b3,b4,b5,b6,b7] =>
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat
        + 256 * (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat))))))
  | _ => 0

/-- `u64leDecode` recovers `x.toNat` from `u64le x` (the left-inverse equation). -/
theorem u64leDecode_u64le (x : UInt64) : u64leDecode (u64le x) = x.toNat := by
  have hlt : x.toNat < 2 ^ 64 := x.toNat_lt
  simp only [u64le, u64leDecode, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow,
    show UInt64.toNat 8 = 8 from rfl, show UInt64.toNat 16 = 16 from rfl,
    show UInt64.toNat 24 = 24 from rfl, show UInt64.toNat 32 = 32 from rfl,
    show UInt64.toNat 40 = 40 from rfl, show UInt64.toNat 48 = 48 from rfl,
    show UInt64.toNat 56 = 56 from rfl,
    show (8 % 64) = 8 from rfl, show (16 % 64) = 16 from rfl, show (24 % 64) = 24 from rfl,
    show (32 % 64) = 32 from rfl, show (40 % 64) = 40 from rfl, show (48 % 64) = 48 from rfl,
    show (56 % 64) = 56 from rfl,
    show (2:Nat)^8 = 256 from rfl, show (2:Nat)^16 = 65536 from rfl,
    show (2:Nat)^24 = 16777216 from rfl, show (2:Nat)^32 = 4294967296 from rfl,
    show (2:Nat)^40 = 1099511627776 from rfl, show (2:Nat)^48 = 281474976710656 from rfl,
    show (2:Nat)^56 = 72057594037927936 from rfl]
  omega

/-- `u64le` is injective: equal little-endian encodings ⇒ equal values. -/
theorem u64le_inj {x y : UInt64} (h : u64le x = u64le y) : x = y := by
  have hx := u64leDecode_u64le x
  have hy := u64leDecode_u64le y
  rw [h] at hx
  exact UInt64.toNat_inj.mp (hx.symm.trans hy)

/-! ## §5 — Structural correctness §A: domain separator present as prefix, per kind. -/

/-- `sigMsgFull` begins with the `.kFull` domain separator. -/
theorem sigMsgFull_hasPrefix (a : SigningAction) (fid : Bytes32) :
    (domainSep .kFull) <+: (sigMsgFull a fid) := by
  refine ⟨fid ++ a.target ++ a.method ++ a.args.flatten ++ a.effectHashes.flatten
          ++ [a.mayDelegate] ++ [a.commitmentMode] ++ balByte a.balanceChange ++ a.precondBytes, ?_⟩
  simp only [domainSep, sigMsgFull, List.append_assoc]

/-- `sigMsgPartial` begins with the `.kPartial` domain separator. -/
theorem sigMsgPartial_hasPrefix (ah fid : Bytes32) (pos nonce : UInt64) :
    (domainSep .kPartial) <+: (sigMsgPartial ah fid pos nonce) := by
  refine ⟨fid ++ ah ++ u64le pos ++ u64le nonce, ?_⟩
  simp only [domainSep, sigMsgPartial, List.append_assoc]

/-- `sigMsgCustom` begins with the `.kCustom` domain separator. -/
theorem sigMsgCustom_hasPrefix (a : SigningAction) (pb : ByteString) (pos : UInt64) (fid : Bytes32)
    (n : UInt64) :
    (domainSep .kCustom) <+: (sigMsgCustom a pb pos fid n) := by
  refine ⟨fid ++ u64le n ++ u64le pos ++ a.target ++ a.method ++ a.args.flatten
          ++ a.effectHashes.flatten ++ [a.mayDelegate] ++ [a.commitmentMode] ++ balByte a.balanceChange
          ++ u32leOfNat a.precondBytes.length ++ a.precondBytes ++ u32leOfNat pb.length ++ pb, ?_⟩
  simp only [domainSep, sigMsgCustom, List.append_assoc]

/-- `sigMsgStealth` begins with the `.kStealth` domain separator. -/
theorem sigMsgStealth_hasPrefix (ah fid ep bs : Bytes32) (pos nonce : UInt64) :
    (domainSep .kStealth) <+: (sigMsgStealth ah fid ep bs pos nonce) := by
  refine ⟨fid ++ ah ++ ep ++ bs ++ u64le pos ++ u64le nonce, ?_⟩
  simp only [domainSep, sigMsgStealth, List.append_assoc]

/-- `sigMsgBearer` begins with the `.kBearer` domain separator. -/
theorem sigMsgBearer_hasPrefix (tgt : Bytes32) (pb : UInt8) (vk : Option Bytes32)
    (bpk fid : Bytes32) (exp : UInt64) :
    (domainSep .kBearer) <+: (sigMsgBearer tgt pb vk bpk exp fid) := by
  refine ⟨fid ++ tgt ++ [pb] ++ vkTail vk ++ bpk ++ u64le exp, ?_⟩
  simp only [domainSep, sigMsgBearer, List.append_assoc]

/-- `sigMsgHandoffCert` begins with the `.kHandoff` domain separator. -/
theorem sigMsgHandoffCert_hasPrefix (intr tf tc rpk : Bytes32) (pb : UInt8) (vk : Option Bytes32)
    (ae ex mu : Option UInt64) :
    (domainSep .kHandoff) <+: (sigMsgHandoffCert intr tf tc rpk pb vk ae ex mu) := by
  refine ⟨intr ++ tf ++ tc ++ rpk ++ [pb] ++ vkTail vk ++ optU64 ae ++ optU64 ex ++ optU64 mu, ?_⟩
  simp only [domainSep, sigMsgHandoffCert, List.append_assoc]

/-! ## §6 — Structural correctness §B: separators pairwise distinct (cross-protocol isolation).

No two kinds share a domain separator. Combined with §A this means a preimage for one kind can never
equal a preimage for another — a signature for one purpose cannot verify for another. Proved by
`decide` on the concrete byte-list literals. -/

/-- Distinct kinds have distinct domain separators (all 15 unordered pairs). -/
theorem domainSep_injective {k₁ k₂ : SigKind} (h : k₁ ≠ k₂) : domainSep k₁ ≠ domainSep k₂ := by
  cases k₁ <;> cases k₂ <;> first | (exact absurd rfl h) | (simp only [domainSep]; decide)

/-! ## §7 — Structural correctness §C: binding — a tampered bound field changes the preimage.

For each builder, perturbing a bound field (`target`, `mayDelegate`, `commitmentMode`,
`federationId`, `nonce`, `actionHash`, `ephemeralPk`, `expiresAt`) yields a different preimage.
Proved by cancelling the common prefix and reading off the field difference. -/

/-- Binding (Full · target): a different target ⇒ a different preimage (both targets equal-length 32-byte cell ids). -/
theorem sigMsgFull_binds_target
    (a a' : SigningAction) (fid : Bytes32)
    (hlen : a.target.length = a'.target.length)
    (h : a.target ≠ a'.target)
    (hrest : a.method = a'.method ∧ a.args = a'.args ∧ a.effectHashes = a'.effectHashes ∧
             a.mayDelegate = a'.mayDelegate ∧ a.commitmentMode = a'.commitmentMode ∧
             a.balanceChange = a'.balanceChange ∧ a.precondBytes = a'.precondBytes) :
    sigMsgFull a fid ≠ sigMsgFull a' fid := by
  obtain ⟨hm, harg, heff, hmd, hcm, hbc, hpc⟩ := hrest
  intro heq
  apply h
  simp only [sigMsgFull, hm, harg, heff, hmd, hcm, hbc, hpc, List.append_assoc] at heq
  -- cancel sepFull, fid (2), then target is the equal-length head of the rest.
  exact List.append_inj_left (List.append_cancel_left (List.append_cancel_left heq)) hlen

/-- Binding (Full · may_delegate): a different `mayDelegate` byte ⇒ a different preimage (relay cannot toggle `may_delegate`). -/
theorem sigMsgFull_binds_mayDelegate
    (a a' : SigningAction) (fid : Bytes32)
    (heq : a.target = a'.target ∧ a.method = a'.method ∧ a.args = a'.args ∧
           a.effectHashes = a'.effectHashes ∧ a.commitmentMode = a'.commitmentMode ∧
           a.balanceChange = a'.balanceChange ∧ a.precondBytes = a'.precondBytes)
    (h : a.mayDelegate ≠ a'.mayDelegate) :
    sigMsgFull a fid ≠ sigMsgFull a' fid := by
  obtain ⟨ht, hm, harg, heff, hcm, hbc, hpc⟩ := heq
  intro hcontra
  apply h
  simp only [sigMsgFull, ht, hm, harg, heff, hcm, hbc, hpc, List.append_assoc] at hcontra
  -- cancel sepFull, fid, target, method, args, effects (6), then [md] is the differing head.
  have hc := List.append_cancel_left (List.append_cancel_left (List.append_cancel_left
    (List.append_cancel_left (List.append_cancel_left (List.append_cancel_left hcontra)))))
  exact (List.cons.injEq .. |>.mp hc).1

/-- Binding (Full · commitment_mode): a different `commitmentMode` byte ⇒ a different preimage (prevents cross-context replay). -/
theorem sigMsgFull_binds_commitmentMode
    (a a' : SigningAction) (fid : Bytes32)
    (heq : a.target = a'.target ∧ a.method = a'.method ∧ a.args = a'.args ∧
           a.effectHashes = a'.effectHashes ∧ a.mayDelegate = a'.mayDelegate ∧
           a.balanceChange = a'.balanceChange ∧ a.precondBytes = a'.precondBytes)
    (h : a.commitmentMode ≠ a'.commitmentMode) :
    sigMsgFull a fid ≠ sigMsgFull a' fid := by
  obtain ⟨ht, hm, harg, heff, hmd, hbc, hpc⟩ := heq
  intro hcontra
  apply h
  simp only [sigMsgFull, ht, hm, harg, heff, hmd, hbc, hpc, List.append_assoc] at hcontra
  -- cancel sepFull, fid, target, method, args, effects, [md] (7), then [cm] is the differing head.
  have hc := List.append_cancel_left (List.append_cancel_left (List.append_cancel_left
    (List.append_cancel_left (List.append_cancel_left (List.append_cancel_left
    (List.append_cancel_left hcontra))))))
  exact (List.cons.injEq .. |>.mp hc).1

/-- Binding (Full · federation_id): a different federation id ⇒ a different preimage (prevents cross-federation replay; equal-length 32-byte ids). -/
theorem sigMsgFull_binds_federationId
    (a : SigningAction) (fid fid' : Bytes32)
    (hlen : fid.length = fid'.length) (h : fid ≠ fid') :
    sigMsgFull a fid ≠ sigMsgFull a fid' := by
  intro hcontra
  apply h
  simp only [sigMsgFull, List.append_assoc] at hcontra
  -- cancel sepFull (1), then fid is the equal-length head of the rest.
  exact List.append_inj_left (List.append_cancel_left hcontra) hlen

/-- Binding (Partial · nonce): a different turn nonce ⇒ a different preimage (cross-turn replay defense). -/
theorem sigMsgPartial_binds_nonce
    (ah fid : Bytes32) (pos n n' : UInt64) (h : n ≠ n') :
    sigMsgPartial ah fid pos n ≠ sigMsgPartial ah fid pos n' := by
  intro hcontra
  apply h
  apply u64le_inj
  simp only [sigMsgPartial, List.append_assoc] at hcontra
  -- cancel sepPartial, fid, ah, u64le pos (4), then the u64le tails are equal.
  exact List.append_cancel_left (List.append_cancel_left (List.append_cancel_left
    (List.append_cancel_left hcontra)))

/-- Binding (Partial · action.hash): a different action digest ⇒ a different preimage (equal-length 32-byte field). -/
theorem sigMsgPartial_binds_actionHash
    (ah ah' fid : Bytes32) (pos n : UInt64)
    (hlen : ah.length = ah'.length) (h : ah ≠ ah') :
    sigMsgPartial ah fid pos n ≠ sigMsgPartial ah' fid pos n := by
  intro hcontra
  apply h
  simp only [sigMsgPartial, List.append_assoc] at hcontra
  -- cancel sepPartial, fid (2), then ah is the equal-length head of `pos ++ nonce`.
  exact List.append_inj_left (List.append_cancel_left (List.append_cancel_left hcontra)) hlen

/-- Binding (Stealth · ephemeral_pubkey): a different ephemeral pubkey ⇒ a different preimage (relay cannot swap `R`). -/
theorem sigMsgStealth_binds_ephemeralPk
    (ah fid ep ep' bs : Bytes32) (pos n : UInt64)
    (hlen : ep.length = ep'.length) (h : ep ≠ ep') :
    sigMsgStealth ah fid ep bs pos n ≠ sigMsgStealth ah fid ep' bs pos n := by
  intro hcontra
  apply h
  simp only [sigMsgStealth, List.append_assoc] at hcontra
  -- cancel sepStealth, fid, ah (3), then ep is the equal-length head of `bs ++ pos ++ nonce`.
  exact List.append_inj_left
    (List.append_cancel_left (List.append_cancel_left (List.append_cancel_left hcontra))) hlen

/-- Binding (Bearer · expires_at): a different `expiresAt` ⇒ a different preimage (relay cannot extend a delegation's expiry). -/
theorem sigMsgBearer_binds_expiresAt
    (tgt : Bytes32) (pb : UInt8) (vk : Option Bytes32) (bpk fid : Bytes32) (e e' : UInt64)
    (h : e ≠ e') :
    sigMsgBearer tgt pb vk bpk e fid ≠ sigMsgBearer tgt pb vk bpk e' fid := by
  intro hcontra
  apply h
  apply u64le_inj
  simp only [sigMsgBearer, List.append_assoc] at hcontra
  -- cancel sepBearer, fid, target, [pb], vkTail, bpk (6), then the u64le tails are equal.
  exact List.append_cancel_left (List.append_cancel_left (List.append_cancel_left
    (List.append_cancel_left (List.append_cancel_left (List.append_cancel_left hcontra)))))

/-! ## §8 — Non-vacuity + fidelity witnesses (`#eval`).

Tamper witnesses print `false` (a real tamper changes the bytes); separator distinctness and encoder
round-trips; each separator literal equals `ascii "dregg-…"` of the dregg1 domain string. -/

/-- A concrete signed action (`balanceChange = some (-5)` exercises the signed-delta arm). -/
def demoA : SigningAction :=
  { target := [1,1,1], method := [2,2], args := [[3],[4]], effectHashes := [[9,9]],
    mayDelegate := 0, commitmentMode := 0, balanceChange := some (-5), precondBytes := [7,7] }

/-- The same action retargeted (the one byte an attacker would change). -/
def demoA' : SigningAction := { demoA with target := [1,1,2] }

-- Tamper witnesses (all `false`):
#guard (decide (sigMsgFull demoA [0] = sigMsgFull demoA' [0])) == false  --  false: retarget ⇒ different preimage
#guard (decide (sigMsgFull demoA [0] = sigMsgFull demoA [9])) == false  --  false: different federation ⇒ different preimage
#guard (decide (u64le 1 = u64le 2)) == false  --  false: encoder injective
-- Encoder round-trips:
#guard (u64leDecode (u64le 123456789)) == 123456789  --  123456789
#guard ((i64le (-5)).length) == 8  --  8
-- Separator distinctness:
#guard (decide (domainSep .kFull = domainSep .kPartial)) == false  --  false
#guard (decide (domainSep .kCustom = domainSep .kStealth)) == false  --  false
-- Byte-literal fidelity (all `true`):
#guard (decide (sepFull    = ascii "dregg-action-sig-v2:"))  --  true
#guard (decide (sepPartial = ascii "dregg-partial-sig-v2:"))  --  true
#guard (decide (sepCustom  = ascii "dregg-custom-sig-v1:"))  --  true
#guard (decide (sepStealth = ascii "dregg-stealth-sig-v1:"))  --  true
#guard (decide (sepBearer  = ascii "dregg-bearer-delegation-v1:"))  --  true
#guard (decide (sepHandoff = ascii "dregg-handoff-cert-v1"))  --  true

/-! ## §9 — Axiom-hygiene pins. -/

#assert_axioms u64leDecode_u64le
#assert_axioms u64le_inj
#assert_axioms domainSep_injective
#assert_axioms sigMsgFull_hasPrefix
#assert_axioms sigMsgPartial_hasPrefix
#assert_axioms sigMsgCustom_hasPrefix
#assert_axioms sigMsgStealth_hasPrefix
#assert_axioms sigMsgBearer_hasPrefix
#assert_axioms sigMsgHandoffCert_hasPrefix
#assert_axioms sigMsgFull_binds_target
#assert_axioms sigMsgFull_binds_mayDelegate
#assert_axioms sigMsgFull_binds_commitmentMode
#assert_axioms sigMsgFull_binds_federationId
#assert_axioms sigMsgPartial_binds_nonce
#assert_axioms sigMsgPartial_binds_actionHash
#assert_axioms sigMsgStealth_binds_ephemeralPk
#assert_axioms sigMsgBearer_binds_expiresAt

end Dregg2.Exec.SigningMessage
