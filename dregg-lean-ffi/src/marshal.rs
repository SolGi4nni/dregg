//! marshal.rs — THE SWAP (T8 encode / T9 decode): the `Turn`→wire marshaller +
//! result decoder bridging dregg1's Rust executor to the verified Lean FFI
//! `@[export] dregg_exec_full_forest_auth`.
//!
//! # The contract
//!
//! This module mirrors `metatheory/Dregg2/Exec/FFI.lean` §W1–§WG **byte-for-byte**.
//! The Lean side is the SOURCE OF TRUTH for the wire; the Lean parser is strict and
//! fail-closed: ANY deviation (a stray space, a reordered key, an uppercase hex
//! nibble, a missing quote) makes the parser return `none`, and the kernel then
//! emits the empty-state `ok:0` sentinel. That looks like a rollback but is actually
//! a marshalling bug — so FORMAT-EXACTNESS is everything.
//!
//! There is **no serde** here on purpose: `serde_json::to_string` matches the (zero)
//! whitespace but REORDERS object keys and cannot reproduce the Lean grammar's
//! array-positional encoding. We hand-roll every byte.
//!
//!     WIRE := {"state":STATEW,"turn":TURNW}                       (input)
//!     OUT  := {"state":STATEW,"loglen":N,"ok":B}                  (output, B in {0,1})
//!
//! # Scope (be blunt about what crosses)
//!
//! What is byte-exact + round-trip-tested here (see `tests`/the round-trip bin):
//!   * the Turn ENVELOPE (`agent,nonce,fee,valid_until,prev,root`);
//!   * the WIDE STATE (all NINE fields incl. the new `revoked`);
//!   * the recursive ACTION-TREE node (`auth,caveats,action,children`) + delegation EDGEs;
//!   * the 10-variant `Authorization` sum (`sig/pf/bread/bearer/unchecked/captp/custom/
//!     oneof/stealth/token`);
//!   * the ~38 representable `FullActionA` arms (the simple ones the task enumerates).
//!
//! What is DEFERRED (documented, NEVER silently mis-encoded — a dropped field is worse
//! than an error). See `MarshalError` and the `// GAP:` comments:
//!   * **P0 — the `state` half is UNSOURCED on the Rust `Turn`.** `STATEW` is the
//!     *executor's pre-state* (it lives in `TurnExecutor`'s tables, NOT on `Turn`).
//!     `marshal_turn` therefore takes a `&WireState` the caller must extract — there is
//!     no `TurnExecutor -> WireState` extractor yet. This is the biggest gap.
//!   * **P0 — `CallForest -> WForest` projection.** The Rust forest's per-node `caveats`
//!     and the delegation-edge `keep`/`parentCap` have NO direct `Turn`/`CallForest`
//!     field; they are synthesized. `from_call_forest` documents this precisely.
//!   * **P0 — `CellId ([u8;32]) -> Nat`** is not injective into the executor id-space;
//!     there must be one canonical agreed map shared with the kernel. `cell_id_to_nat`
//!     is the seam.
//!   * **P1 — 13 Rust `Effect` variants + 2 auth variants have NO wire arm.** They MUST
//!     return `UnrepresentableEffect`/`UnrepresentableAuth`.
//!
//! This module is intentionally self-contained (the crate is workspace-detached for
//! swarm safety): it defines the wire-level types directly, the same discipline the
//! existing `full_turn_differential.rs` uses (a faithful Rust mirror, never an import of
//! the buggy dregg1 `turn` crate). Wiring the real `turn::Turn` is the call-site change
//! the P0 gaps above describe; the encoders are keyed to the dregg1 variant names so that
//! shim is thin.

#![allow(dead_code)] // the full encoder surface is exercised by tests + downstream wiring.

// ===================================================================
// ERRORS — every "cannot represent on the wire" is a HARD error.
// ===================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MarshalError {
    /// A Rust `Effect` with no wire arm in the `dregg_exec_full_forest_auth` grammar
    /// (GrantCapability/RevokeCapability/RefreshDelegation/sealed-box Seal·Unseal/
    /// FulfillObligation/SlashObligation/PipelinedSend/CreateCellFromFactory/
    /// QueueAtomicTx/QueuePipelineStep/CellDestroy).
    UnrepresentableEffect(&'static str),
    /// An auth variant with no wire arm (BiscuitIssuer / CellScopedMacaroon).
    UnrepresentableAuth(&'static str),
    /// A wire-`Nat` field (agent/nonce/valid_until/id/...) was given a negative value.
    NonNatField { field: &'static str },
    /// An AUTHS tag exceeded 6 (the `Auth` enumeration is 0..6).
    AuthTagOutOfRange(u8),
    /// A `Turn` envelope field the wire grammar requires is absent (e.g. `valid_until: None`).
    MissingEnvelopeField { field: &'static str },
}

impl std::fmt::Display for MarshalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MarshalError::UnrepresentableEffect(s) => {
                write!(f, "effect has no wire arm in dregg_exec_full_forest_auth grammar: {s}")
            }
            MarshalError::UnrepresentableAuth(s) => write!(f, "auth variant has no wire arm: {s}"),
            MarshalError::NonNatField { field } => {
                write!(f, "wire-Nat field `{field}` was negative (grammar needs Nat)")
            }
            MarshalError::AuthTagOutOfRange(t) => write!(f, "AUTHS tag {t} > 6 (Auth is 0..6)"),
            MarshalError::MissingEnvelopeField { field } => {
                write!(f, "Turn envelope field `{field}` required by wire grammar is absent")
            }
        }
    }
}
impl std::error::Error for MarshalError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnmarshalError {
    /// The kernel returned the empty-8/9-field-state `ok:0` sentinel = the wire we SENT
    /// was malformed (a marshalling bug), NOT a legitimate turn rejection.
    MalformedWireSentinel,
    /// The output envelope did not parse (`at` = byte offset, `why` = expectation).
    OutputParse { at: usize, why: String },
}

impl std::fmt::Display for UnmarshalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnmarshalError::MalformedWireSentinel => write!(
                f,
                "kernel returned the malformed-wire sentinel (empty state, ok:0) — the wire we SENT was malformed"
            ),
            UnmarshalError::OutputParse { at, why } => {
                write!(f, "output envelope did not parse at byte {at}: {why}")
            }
        }
    }
}
impl std::error::Error for UnmarshalError {}

// ===================================================================
// AUTHORITY: Auth (0..6) and Cap — faithful mirrors of Dregg2.Authority.
// (Identical to the mirror in full_turn_differential.rs.)
// ===================================================================

/// The 7-constructor `Auth` enumeration, in `Auth` ctor order (FFI.lean:410).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Auth {
    Read = 0,
    Write = 1,
    Grant = 2,
    Call = 3,
    Reply = 4,
    Reset = 5,
    Control = 6,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cap {
    Null,
    Node(u64),
    Endpoint(u64, Vec<Auth>),
}

// ===================================================================
// VALUE — the wide `Value` codec (`dig` as the 64-hex ByteArray32 field).
// FFI.lean:1121 (encodeValueW). NOTE: `dig` is WIDE here (quoted 64-hex), unlike the
// narrow record-kernel codec where `dig` was a bare Nat.
// ===================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WireValue {
    Int(i128),
    /// A `[u8;32]` digest. Encoded as the low 256 bits, big-endian, 64 LOWERCASE hex.
    Dig(u64),
    Sym(u64),
    Record(Vec<(String, WireValue)>),
}

// ===================================================================
// STATE side-tables — faithful mirrors of the RecordKernelState records.
// ===================================================================

/// EscrowRecord (FFI.lean:2326): `[id,creator,recipient,amount,resolved,asset,bridge]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireEscrow {
    pub id: u64,
    pub creator: u64,
    pub recipient: u64,
    pub amount: i128,
    pub resolved: bool,
    pub asset: u64,
    pub bridge: bool,
}

/// QueueRecord (FFI.lean:2416): `[id,owner,capacity,[msg,...]]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireQueue {
    pub id: u64,
    pub owner: u64,
    pub capacity: u64,
    pub buffer: Vec<u64>,
}

/// SwissRecord (FFI.lean:2479): `[swiss,exporter,target,AUTHS,refcount,CERT]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireSwiss {
    pub swiss: u64,
    pub exporter: u64,
    pub target: u64,
    pub rights: Vec<Auth>,
    pub refcount: u64,
    /// `{"none":0}` / `{"some":N}`.
    pub cert: Option<u64>,
}

/// The WIDE STATE — all NINE fields (FFI.lean:2561 encodeWState), in fixed order:
/// cells, caps, bal, escrows, nullifiers, commitments, queues, swiss, revoked.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WireState {
    pub cells: Vec<(u64, WireValue)>,
    pub caps: Vec<(u64, Vec<Cap>)>,
    /// Per-asset ledger: `[cell,asset,amt]` triples (amt SIGNED).
    pub bal: Vec<(u64, u64, i128)>,
    pub escrows: Vec<WireEscrow>,
    pub nullifiers: Vec<u64>,
    pub commitments: Vec<u64>,
    pub queues: Vec<WireQueue>,
    pub swiss: Vec<WireSwiss>,
    /// The revocation registry (hole #3 / #139) — the committed revoked-credential
    /// nullifier set the gate reads. LAST on the wire (additive); defaults empty.
    pub revoked: Vec<u64>,
}

impl WireState {
    /// The empty-9-field state the kernel emits on a MALFORMED wire (the §WG `none`
    /// branch, FFI.lean:3019). Distinguishing this from a non-empty echoed rollback state
    /// is how T9 tells "I sent garbage" (a bug) from "the turn was rejected" (legitimate).
    pub fn is_empty_sentinel(&self) -> bool {
        self.cells.is_empty()
            && self.caps.is_empty()
            && self.bal.is_empty()
            && self.escrows.is_empty()
            && self.nullifiers.is_empty()
            && self.commitments.is_empty()
            && self.queues.is_empty()
            && self.swiss.is_empty()
            && self.revoked.is_empty()
    }
}

// ===================================================================
// AUTHORIZATION — the 10-variant credential sum (FFI.lean:1365 encodeAuthW).
// Digest = a [u8;32] (encoded as quoted 64-hex); Proof = a decimal Nat blob.
// Variant order matches the dregg1 `Authorization` enum + the two extras (Stealth/Token).
// ===================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WireAuth {
    /// {"sig":["H64",P]} — signature(pubkeyMsg, sig).
    Signature { pubkey: u64, sig: u64 },
    /// {"pf":["H64",P,N,N]} — proof(vk, proofBytes, boundAction, boundResource).
    /// NOTE: `bound_action`/`bound_resource` are Nat here; the dregg1 `Authorization::Proof`
    /// carries them as Strings — `String -> Nat` is LOSSY/irreversible (GAP, see module doc).
    Proof { vk: u64, proof: u64, bound_action: u64, bound_resource: u64 },
    /// {"bread":[N]} — breadstuff(token).
    Breadstuff { token: u64 },
    /// {"bearer":["H64",P,B]} — bearer(delegMsg, delegSig, starkDelegation).
    /// GAP: the full `BearerCapProof` collapses to (delegMsg, delegSig, starkBool); the
    /// SignedDelegation|StarkDelegation distinction is the ONLY bit that survives.
    Bearer { deleg_msg: u64, deleg_sig: u64, stark: bool },
    /// {"unchecked":0} — TAG-ONLY literal.
    Unchecked,
    /// {"captp":["H64","H64",P,P]} — capTpDelivered(introMsg, senderMsg, introSig, senderSig).
    CapTpDelivered { intro_msg: u64, sender_msg: u64, intro_sig: u64, sender_sig: u64 },
    /// {"custom":["H64",P]} — custom(kindStmt, proofBytes).
    Custom { kind_stmt: u64, proof: u64 },
    /// {"oneof":[[AUTH(,AUTH)*],N]} — oneOf(candidates, proofIndex). RECURSES.
    OneOf { candidates: Vec<WireAuth>, proof_index: u64 },
    /// {"stealth":["H64","H64",P]} — stealth(oneTimePk, ephemeralPk, sig).
    Stealth { one_time_pk: u64, ephemeral_pk: u64, sig: u64 },
    /// {"token":["H64",P]} — token(issuerKey, sig).
    /// GAP: the dregg1 `Token` `encoded`/`discharges`/full `key_ref` are DROPPED.
    Token { issuer_key: u64, sig: u64 },
}

// ===================================================================
// CAVEAT — the per-node within-cell threshold (FFI.lean:2091 encodeCaveatW).
//   WCAVEAT := [tier,cell,asset,min]   (tier in {0,1,2,3}; min SIGNED)
// ===================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireCaveat {
    /// DriftTier ordinal: 0=monotone 1=reservation 2=locked 3=coordinated.
    pub tier: u64,
    pub cell: u64,
    pub asset: u64,
    pub min: i128,
}

// ===================================================================
// ACTION — the 51-arm `FullActionA` (FFI.lean:1619 encodeActionW). We model the
// representable arms the task enumerates. Each `id/asset/idx/...` is a Nat; each
// `amt/value/amount/stake/deposit/v/perms/vk/topic/data` is SIGNED.
// ===================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WireAction {
    /// {"bal":[actor,src,dst,amt,asset]}  (amt SIGNED, asset LAST)
    Balance { actor: u64, src: u64, dst: u64, amt: i128, asset: u64 },
    /// {"del":[delegator,recipient,t]}
    Delegate { delegator: u64, recipient: u64, t: u64 },
    /// {"rev":[holder,t]}
    Revoke { holder: u64, t: u64 },
    /// {"mint":[actor,cell,asset,amt]}
    Mint { actor: u64, cell: u64, asset: u64, amt: i128 },
    /// {"burn":[actor,cell,asset,amt]}
    Burn { actor: u64, cell: u64, asset: u64, amt: i128 },
    /// {"setfield":[actor,cell,"FIELD",v]}  (v SIGNED)
    SetField { actor: u64, cell: u64, field: String, v: i128 },
    /// {"emit":[actor,cell,topic,data]}  (topic,data SIGNED)
    Emit { actor: u64, cell: u64, topic: i128, data: i128 },
    /// {"incnonce":[actor,cell,newNonce]}  (newNonce SIGNED)
    IncNonce { actor: u64, cell: u64, new_nonce: i128 },
    /// {"setperms":[actor,cell,perms]}  (perms SIGNED)
    SetPerms { actor: u64, cell: u64, perms: i128 },
    /// {"setvk":[actor,cell,vk]}  (vk SIGNED)
    SetVk { actor: u64, cell: u64, vk: i128 },
    /// {"introduce":[introducer,recipient,target]}
    Introduce { introducer: u64, recipient: u64, target: u64 },
    /// {"delatten":[delegator,recipient,target,AUTHS]}
    DelegateAtten { delegator: u64, recipient: u64, target: u64, keep: Vec<Auth> },
    /// {"atten":[actor,idx,AUTHS]}
    Attenuate { actor: u64, idx: u64, keep: Vec<Auth> },
    /// {"dropref":[holder,target]}
    DropRef { holder: u64, target: u64 },
    /// {"revdel":[holder,target]}
    RevokeDelegation { holder: u64, target: u64 },
    /// {"vhandoff":[introducer,recipient,target]}
    ValidateHandoff { introducer: u64, recipient: u64, target: u64 },
    /// {"exercise":[actor,target]}
    Exercise { actor: u64, target: u64 },
    /// {"createcell":[actor,newCell]}
    CreateCell { actor: u64, new_cell: u64 },
    /// {"spawn":[actor,child,target]}
    Spawn { actor: u64, child: u64, target: u64 },
    /// {"bmint":[actor,cell,asset,value]}  (value SIGNED)
    BridgeMint { actor: u64, cell: u64, asset: u64, value: i128 },
    /// {"cesc":[id,actor,creator,recipient,asset,amount]}  (amount SIGNED)
    CreateEscrow { id: u64, actor: u64, creator: u64, recipient: u64, asset: u64, amount: i128 },
    /// {"resc":[id,actor]}
    ReleaseEscrow { id: u64, actor: u64 },
    /// {"fesc":[id,actor]}
    RefundEscrow { id: u64, actor: u64 },
    /// {"cobl":[id,actor,obligor,beneficiary,asset,stake]}  (stake SIGNED)
    CreateObligation { id: u64, actor: u64, obligor: u64, beneficiary: u64, asset: u64, stake: i128 },
    /// {"nspend":[nf,actor]}
    NoteSpend { nf: u64, actor: u64 },
    /// {"ncreate":[cm,actor]}
    NoteCreate { cm: u64, actor: u64 },
    /// {"ccesc":[id,actor,creator,recipient,asset,amount]}  (amount SIGNED)
    CreateCommittedEscrow { id: u64, actor: u64, creator: u64, recipient: u64, asset: u64, amount: i128 },
    /// {"rccesc":[id,actor]}
    ReleaseCommittedEscrow { id: u64, actor: u64 },
    /// {"fccesc":[id,actor]}
    RefundCommittedEscrow { id: u64, actor: u64 },
    /// {"block":[id,actor,originator,destination,asset,amount]}  (amount SIGNED)
    BridgeLock { id: u64, actor: u64, originator: u64, destination: u64, asset: u64, amount: i128 },
    /// {"bfin":[id,actor,asset,amount]}  (amount SIGNED)
    BridgeFinalize { id: u64, actor: u64, asset: u64, amount: i128 },
    /// {"bcancel":[id,actor]}
    BridgeCancel { id: u64, actor: u64 },
    /// {"seal":[actor,cell]}
    Seal { actor: u64, cell: u64 },
    /// {"unseal":[actor,cell]}
    Unseal { actor: u64, cell: u64 },
    /// {"csp":[actor,sealerHolder,unsealerHolder]}
    CreateSealPair { actor: u64, sealer_holder: u64, unsealer_holder: u64 },
    /// {"sov":[actor,cell]}
    MakeSovereign { actor: u64, cell: u64 },
    /// {"refusal":[actor,cell]}
    Refusal { actor: u64, cell: u64 },
    /// {"rarchive":[actor,cell]}
    ReceiptArchive { actor: u64, cell: u64 },
    /// {"qalloc":[id,actor,cell,capacity]}
    QueueAllocate { id: u64, actor: u64, cell: u64, capacity: u64 },
    /// {"qenq":[id,m,actor,cell,depId,dAsset,deposit]}  (deposit SIGNED)
    QueueEnqueue { id: u64, m: u64, actor: u64, cell: u64, dep_id: u64, d_asset: u64, deposit: i128 },
    /// {"qdeq":[id,actor,cell,depId,deposit]}  (deposit SIGNED)
    QueueDequeue { id: u64, actor: u64, cell: u64, dep_id: u64, deposit: i128 },
    /// {"qresize":[id,newCap,actor,cell]}
    QueueResize { id: u64, new_cap: u64, actor: u64, cell: u64 },
    /// {"export":[sw,actor,exporter,target,AUTHS]}
    ExportSturdyRef { sw: u64, actor: u64, exporter: u64, target: u64, rights: Vec<Auth> },
    /// {"enliven":[sw,actor,exporter,AUTHS]}
    EnlivenRef { sw: u64, actor: u64, exporter: u64, claimed: Vec<Auth> },
    /// {"shandoff":[sw,certHash,introducer,exporter]}
    SwissHandoff { sw: u64, cert_hash: u64, introducer: u64, exporter: u64 },
    /// {"sdrop":[sw,actor,exporter]}
    SwissDrop { sw: u64, actor: u64, exporter: u64 },
}

// ===================================================================
// TREE — the recursive action-tree NODE + delegation EDGE (FFI.lean:2204).
//   NODE := {"auth":AUTH,"caveats":WCAVEATS,"action":ACTIONW,"children":KIDS}
//   EDGE := {"holder":N,"keep":AUTHS,"cap":CAP,"sub":NODE}
// ===================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WForest {
    pub auth: WireAuth,
    pub caveats: Vec<WireCaveat>,
    pub action: WireAction,
    pub children: Vec<WChild>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WChild {
    pub holder: u64,
    pub keep: Vec<Auth>,
    pub parent_cap: Cap,
    pub sub: WForest,
}

// ===================================================================
// TURN — the dregg1 envelope + the action-tree root (FFI.lean:2646 encodeWTurn).
//   TURNW := {"agent":N,"nonce":N,"fee":Z,"valid_until":N,"prev":"H64","root":NODE}
// ===================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireTurn {
    pub agent: u64,
    pub nonce: u64,
    /// fee is a SIGNED Int (i128) on the wire, even though a real fee is non-negative.
    pub fee: i128,
    pub valid_until: u64,
    /// The previous-receipt hash, a [u8;32] (encoded as 64-hex).
    pub prev_hash: u64,
    pub root: WForest,
}

// ===================================================================
// T8 ENCODE — marshal_turn(state, turn) -> the input wire String.
// ===================================================================

/// The full input wire `{"state":STATEW,"turn":TURNW}`.
///
/// `state` is the executor's PRE-state (the P0-unsourced left half — see module doc); the
/// caller must supply a `WireState` snapshot. `turn` is the wire-level envelope+tree.
pub fn marshal_turn(state: &WireState, turn: &WireTurn) -> Result<String, MarshalError> {
    let mut s = String::with_capacity(512);
    s.push_str("{\"state\":");
    encode_wstate(state, &mut s)?;
    s.push_str(",\"turn\":");
    encode_wturn(turn, &mut s)?;
    s.push('}');
    Ok(s)
}

// ---- scalar primitives (mirror FFI.lean parseInt/parseNat/toHex32) ----

fn push_nat(out: &mut String, n: u64) {
    out.push_str(itoa_u64(n).as_str());
}
fn push_int(out: &mut String, i: i128) {
    // decimal, leading '-' if negative — matches Lean `toString : Int -> String`.
    out.push_str(&i.to_string());
}
fn itoa_u64(n: u64) -> String {
    n.to_string()
}

/// 64 LOWERCASE hex, big-endian, low 256 bits (mirror FFI.lean toHex32:1066). A u64 source
/// occupies the low 16 nibbles; the high 48 nibbles are zero-padded so width is pinned to 64.
fn to_hex32(n: u64) -> String {
    let mut s = String::with_capacity(64);
    // 64 hex chars = 256 bits; we have a u64 (64 bits = 16 nibbles). Pad 48 zeros, then the u64.
    for _ in 0..48 {
        s.push('0');
    }
    s.push_str(&format!("{n:016x}")); // lowercase, zero-padded to 16 nibbles
    debug_assert_eq!(s.len(), 64);
    s
}

fn push_json_escaped(out: &mut String, name: &str) {
    // mirror jsonEscape (FFI.lean:106): escape only `"` and `\`.
    for c in name.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            _ => out.push(c),
        }
    }
}

// ---- AUTHS tag array (0..6) ----

fn encode_auths(tags: &[Auth], out: &mut String) {
    out.push('[');
    for (i, t) in tags.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(itoa_u64(*t as u64).as_str());
    }
    out.push(']');
}

// ---- Cap (FFI.lean:428 encodeCap) ----

fn encode_cap(c: &Cap, out: &mut String) {
    match c {
        Cap::Null => out.push_str("{\"null\":0}"),
        Cap::Node(t) => {
            out.push_str("{\"node\":");
            push_nat(out, *t);
            out.push('}');
        }
        Cap::Endpoint(t, r) => {
            out.push_str("{\"ep\":[");
            push_nat(out, *t);
            out.push(',');
            encode_auths(r, out);
            out.push_str("]}");
        }
    }
}

fn encode_cap_list(cl: &[Cap], out: &mut String) {
    out.push('[');
    for (i, c) in cl.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        encode_cap(c, out);
    }
    out.push(']');
}

// ---- WireValue (FFI.lean:1121 encodeValueW) ----

fn encode_value(v: &WireValue, out: &mut String) {
    match v {
        WireValue::Int(i) => {
            out.push_str("{\"int\":");
            push_int(out, *i);
            out.push('}');
        }
        WireValue::Dig(d) => {
            out.push_str("{\"dig\":\"");
            out.push_str(&to_hex32(*d));
            out.push_str("\"}");
        }
        WireValue::Sym(s) => {
            out.push_str("{\"sym\":");
            push_nat(out, *s);
            out.push('}');
        }
        WireValue::Record(fs) => {
            out.push_str("{\"rec\":");
            encode_fields(fs, out);
            out.push('}');
        }
    }
}

fn encode_fields(fs: &[(String, WireValue)], out: &mut String) {
    out.push('[');
    for (i, (n, v)) in fs.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str("[\"");
        push_json_escaped(out, n);
        out.push_str("\",");
        encode_value(v, out);
        out.push(']');
    }
    out.push(']');
}

// ---- WireAuth (FFI.lean:1365 encodeAuthW) ----

fn encode_auth(a: &WireAuth, out: &mut String) {
    // encDig (FFI.lean:1353) = the QUOTED 64-hex digest.
    let push_dig = |out: &mut String, d: u64| {
        out.push('"');
        out.push_str(&to_hex32(d));
        out.push('"');
    };
    match a {
        WireAuth::Signature { pubkey, sig } => {
            out.push_str("{\"sig\":[");
            push_dig(out, *pubkey);
            out.push(',');
            push_nat(out, *sig);
            out.push_str("]}");
        }
        WireAuth::Proof { vk, proof, bound_action, bound_resource } => {
            out.push_str("{\"pf\":[");
            push_dig(out, *vk);
            out.push(',');
            push_nat(out, *proof);
            out.push(',');
            push_nat(out, *bound_action);
            out.push(',');
            push_nat(out, *bound_resource);
            out.push_str("]}");
        }
        WireAuth::Breadstuff { token } => {
            out.push_str("{\"bread\":[");
            push_nat(out, *token);
            out.push_str("]}");
        }
        WireAuth::Bearer { deleg_msg, deleg_sig, stark } => {
            out.push_str("{\"bearer\":[");
            push_dig(out, *deleg_msg);
            out.push(',');
            push_nat(out, *deleg_sig);
            out.push(',');
            out.push(if *stark { '1' } else { '0' });
            out.push_str("]}");
        }
        WireAuth::Unchecked => out.push_str("{\"unchecked\":0}"),
        WireAuth::CapTpDelivered { intro_msg, sender_msg, intro_sig, sender_sig } => {
            out.push_str("{\"captp\":[");
            push_dig(out, *intro_msg);
            out.push(',');
            push_dig(out, *sender_msg);
            out.push(',');
            push_nat(out, *intro_sig);
            out.push(',');
            push_nat(out, *sender_sig);
            out.push_str("]}");
        }
        WireAuth::Custom { kind_stmt, proof } => {
            out.push_str("{\"custom\":[");
            push_dig(out, *kind_stmt);
            out.push(',');
            push_nat(out, *proof);
            out.push_str("]}");
        }
        WireAuth::OneOf { candidates, proof_index } => {
            out.push_str("{\"oneof\":[[");
            for (i, c) in candidates.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                encode_auth(c, out); // RECURSION
            }
            out.push_str("],");
            push_nat(out, *proof_index);
            out.push_str("]}");
        }
        WireAuth::Stealth { one_time_pk, ephemeral_pk, sig } => {
            out.push_str("{\"stealth\":[");
            push_dig(out, *one_time_pk);
            out.push(',');
            push_dig(out, *ephemeral_pk);
            out.push(',');
            push_nat(out, *sig);
            out.push_str("]}");
        }
        WireAuth::Token { issuer_key, sig } => {
            out.push_str("{\"token\":[");
            push_dig(out, *issuer_key);
            out.push(',');
            push_nat(out, *sig);
            out.push_str("]}");
        }
    }
}

// ---- WireCaveat (FFI.lean:2091) ----

fn encode_caveat(c: &WireCaveat, out: &mut String) {
    out.push('[');
    push_nat(out, c.tier);
    out.push(',');
    push_nat(out, c.cell);
    out.push(',');
    push_nat(out, c.asset);
    out.push(',');
    push_int(out, c.min);
    out.push(']');
}

fn encode_caveats(cs: &[WireCaveat], out: &mut String) {
    out.push('[');
    for (i, c) in cs.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        encode_caveat(c, out);
    }
    out.push(']');
}

// ---- WireAction (FFI.lean:1619 encodeActionW), all representable arms ----

fn encode_action(a: &WireAction, out: &mut String) {
    // Helper macros emit `{"tag":[ ... ]}` with mixed Nat/Int/AUTHS/String args, comma-joined.
    match a {
        WireAction::Balance { actor, src, dst, amt, asset } => {
            out.push_str("{\"bal\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *src);
            out.push(',');
            push_nat(out, *dst);
            out.push(',');
            push_int(out, *amt);
            out.push(',');
            push_nat(out, *asset);
            out.push_str("]}");
        }
        WireAction::Delegate { delegator, recipient, t } => {
            out.push_str("{\"del\":[");
            push_nat(out, *delegator);
            out.push(',');
            push_nat(out, *recipient);
            out.push(',');
            push_nat(out, *t);
            out.push_str("]}");
        }
        WireAction::Revoke { holder, t } => {
            out.push_str("{\"rev\":[");
            push_nat(out, *holder);
            out.push(',');
            push_nat(out, *t);
            out.push_str("]}");
        }
        WireAction::Mint { actor, cell, asset, amt } => {
            out.push_str("{\"mint\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push(',');
            push_nat(out, *asset);
            out.push(',');
            push_int(out, *amt);
            out.push_str("]}");
        }
        WireAction::Burn { actor, cell, asset, amt } => {
            out.push_str("{\"burn\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push(',');
            push_nat(out, *asset);
            out.push(',');
            push_int(out, *amt);
            out.push_str("]}");
        }
        WireAction::SetField { actor, cell, field, v } => {
            out.push_str("{\"setfield\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push_str(",\"");
            push_json_escaped(out, field);
            out.push_str("\",");
            push_int(out, *v);
            out.push_str("]}");
        }
        WireAction::Emit { actor, cell, topic, data } => {
            out.push_str("{\"emit\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push(',');
            push_int(out, *topic);
            out.push(',');
            push_int(out, *data);
            out.push_str("]}");
        }
        WireAction::IncNonce { actor, cell, new_nonce } => {
            out.push_str("{\"incnonce\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push(',');
            push_int(out, *new_nonce);
            out.push_str("]}");
        }
        WireAction::SetPerms { actor, cell, perms } => {
            out.push_str("{\"setperms\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push(',');
            push_int(out, *perms);
            out.push_str("]}");
        }
        WireAction::SetVk { actor, cell, vk } => {
            out.push_str("{\"setvk\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push(',');
            push_int(out, *vk);
            out.push_str("]}");
        }
        WireAction::Introduce { introducer, recipient, target } => {
            out.push_str("{\"introduce\":[");
            push_nat(out, *introducer);
            out.push(',');
            push_nat(out, *recipient);
            out.push(',');
            push_nat(out, *target);
            out.push_str("]}");
        }
        WireAction::DelegateAtten { delegator, recipient, target, keep } => {
            out.push_str("{\"delatten\":[");
            push_nat(out, *delegator);
            out.push(',');
            push_nat(out, *recipient);
            out.push(',');
            push_nat(out, *target);
            out.push(',');
            encode_auths(keep, out);
            out.push_str("]}");
        }
        WireAction::Attenuate { actor, idx, keep } => {
            out.push_str("{\"atten\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *idx);
            out.push(',');
            encode_auths(keep, out);
            out.push_str("]}");
        }
        WireAction::DropRef { holder, target } => {
            out.push_str("{\"dropref\":[");
            push_nat(out, *holder);
            out.push(',');
            push_nat(out, *target);
            out.push_str("]}");
        }
        WireAction::RevokeDelegation { holder, target } => {
            out.push_str("{\"revdel\":[");
            push_nat(out, *holder);
            out.push(',');
            push_nat(out, *target);
            out.push_str("]}");
        }
        WireAction::ValidateHandoff { introducer, recipient, target } => {
            out.push_str("{\"vhandoff\":[");
            push_nat(out, *introducer);
            out.push(',');
            push_nat(out, *recipient);
            out.push(',');
            push_nat(out, *target);
            out.push_str("]}");
        }
        WireAction::Exercise { actor, target } => {
            out.push_str("{\"exercise\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *target);
            out.push_str("]}");
        }
        WireAction::CreateCell { actor, new_cell } => {
            out.push_str("{\"createcell\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *new_cell);
            out.push_str("]}");
        }
        WireAction::Spawn { actor, child, target } => {
            out.push_str("{\"spawn\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *child);
            out.push(',');
            push_nat(out, *target);
            out.push_str("]}");
        }
        WireAction::BridgeMint { actor, cell, asset, value } => {
            out.push_str("{\"bmint\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push(',');
            push_nat(out, *asset);
            out.push(',');
            push_int(out, *value);
            out.push_str("]}");
        }
        WireAction::CreateEscrow { id, actor, creator, recipient, asset, amount } => {
            out.push_str("{\"cesc\":[");
            for (i, n) in [*id, *actor, *creator, *recipient, *asset].iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                push_nat(out, *n);
            }
            out.push(',');
            push_int(out, *amount);
            out.push_str("]}");
        }
        WireAction::ReleaseEscrow { id, actor } => emit_id_actor("resc", *id, *actor, out),
        WireAction::RefundEscrow { id, actor } => emit_id_actor("fesc", *id, *actor, out),
        WireAction::CreateObligation { id, actor, obligor, beneficiary, asset, stake } => {
            out.push_str("{\"cobl\":[");
            for (i, n) in [*id, *actor, *obligor, *beneficiary, *asset].iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                push_nat(out, *n);
            }
            out.push(',');
            push_int(out, *stake);
            out.push_str("]}");
        }
        WireAction::NoteSpend { nf, actor } => emit_id_actor("nspend", *nf, *actor, out),
        WireAction::NoteCreate { cm, actor } => emit_id_actor("ncreate", *cm, *actor, out),
        WireAction::CreateCommittedEscrow { id, actor, creator, recipient, asset, amount } => {
            out.push_str("{\"ccesc\":[");
            for (i, n) in [*id, *actor, *creator, *recipient, *asset].iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                push_nat(out, *n);
            }
            out.push(',');
            push_int(out, *amount);
            out.push_str("]}");
        }
        WireAction::ReleaseCommittedEscrow { id, actor } => emit_id_actor("rccesc", *id, *actor, out),
        WireAction::RefundCommittedEscrow { id, actor } => emit_id_actor("fccesc", *id, *actor, out),
        WireAction::BridgeLock { id, actor, originator, destination, asset, amount } => {
            out.push_str("{\"block\":[");
            for (i, n) in [*id, *actor, *originator, *destination, *asset].iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                push_nat(out, *n);
            }
            out.push(',');
            push_int(out, *amount);
            out.push_str("]}");
        }
        WireAction::BridgeFinalize { id, actor, asset, amount } => {
            out.push_str("{\"bfin\":[");
            push_nat(out, *id);
            out.push(',');
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *asset);
            out.push(',');
            push_int(out, *amount);
            out.push_str("]}");
        }
        WireAction::BridgeCancel { id, actor } => emit_id_actor("bcancel", *id, *actor, out),
        WireAction::Seal { actor, cell } => emit_id_actor("seal", *actor, *cell, out),
        WireAction::Unseal { actor, cell } => emit_id_actor("unseal", *actor, *cell, out),
        WireAction::CreateSealPair { actor, sealer_holder, unsealer_holder } => {
            out.push_str("{\"csp\":[");
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *sealer_holder);
            out.push(',');
            push_nat(out, *unsealer_holder);
            out.push_str("]}");
        }
        WireAction::MakeSovereign { actor, cell } => emit_id_actor("sov", *actor, *cell, out),
        WireAction::Refusal { actor, cell } => emit_id_actor("refusal", *actor, *cell, out),
        WireAction::ReceiptArchive { actor, cell } => emit_id_actor("rarchive", *actor, *cell, out),
        WireAction::QueueAllocate { id, actor, cell, capacity } => {
            out.push_str("{\"qalloc\":[");
            push_nat(out, *id);
            out.push(',');
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push(',');
            push_nat(out, *capacity);
            out.push_str("]}");
        }
        WireAction::QueueEnqueue { id, m, actor, cell, dep_id, d_asset, deposit } => {
            out.push_str("{\"qenq\":[");
            for (i, n) in [*id, *m, *actor, *cell, *dep_id, *d_asset].iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                push_nat(out, *n);
            }
            out.push(',');
            push_int(out, *deposit);
            out.push_str("]}");
        }
        WireAction::QueueDequeue { id, actor, cell, dep_id, deposit } => {
            out.push_str("{\"qdeq\":[");
            for (i, n) in [*id, *actor, *cell, *dep_id].iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                push_nat(out, *n);
            }
            out.push(',');
            push_int(out, *deposit);
            out.push_str("]}");
        }
        WireAction::QueueResize { id, new_cap, actor, cell } => {
            out.push_str("{\"qresize\":[");
            push_nat(out, *id);
            out.push(',');
            push_nat(out, *new_cap);
            out.push(',');
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *cell);
            out.push_str("]}");
        }
        WireAction::ExportSturdyRef { sw, actor, exporter, target, rights } => {
            out.push_str("{\"export\":[");
            push_nat(out, *sw);
            out.push(',');
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *exporter);
            out.push(',');
            push_nat(out, *target);
            out.push(',');
            encode_auths(rights, out);
            out.push_str("]}");
        }
        WireAction::EnlivenRef { sw, actor, exporter, claimed } => {
            out.push_str("{\"enliven\":[");
            push_nat(out, *sw);
            out.push(',');
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *exporter);
            out.push(',');
            encode_auths(claimed, out);
            out.push_str("]}");
        }
        WireAction::SwissHandoff { sw, cert_hash, introducer, exporter } => {
            out.push_str("{\"shandoff\":[");
            push_nat(out, *sw);
            out.push(',');
            push_nat(out, *cert_hash);
            out.push(',');
            push_nat(out, *introducer);
            out.push(',');
            push_nat(out, *exporter);
            out.push_str("]}");
        }
        WireAction::SwissDrop { sw, actor, exporter } => {
            out.push_str("{\"sdrop\":[");
            push_nat(out, *sw);
            out.push(',');
            push_nat(out, *actor);
            out.push(',');
            push_nat(out, *exporter);
            out.push_str("]}");
        }
    }
}

/// Emit a 2-Nat tagged action `{"tag":[a,b]}` (the many `[id,actor]`/`[actor,cell]` arms).
fn emit_id_actor(tag: &str, a: u64, b: u64, out: &mut String) {
    out.push_str("{\"");
    out.push_str(tag);
    out.push_str("\":[");
    push_nat(out, a);
    out.push(',');
    push_nat(out, b);
    out.push_str("]}");
}

// ---- tree: NODE + EDGE (FFI.lean:2204 encodeForestW) ----

fn encode_forest(f: &WForest, out: &mut String) {
    out.push_str("{\"auth\":");
    encode_auth(&f.auth, out);
    out.push_str(",\"caveats\":");
    encode_caveats(&f.caveats, out);
    out.push_str(",\"action\":");
    encode_action(&f.action, out);
    out.push_str(",\"children\":");
    encode_children(&f.children, out);
    out.push('}');
}

fn encode_children(kids: &[WChild], out: &mut String) {
    out.push('[');
    for (i, c) in kids.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        encode_child(c, out);
    }
    out.push(']');
}

fn encode_child(c: &WChild, out: &mut String) {
    out.push_str("{\"holder\":");
    push_nat(out, c.holder);
    out.push_str(",\"keep\":");
    encode_auths(&c.keep, out);
    out.push_str(",\"cap\":");
    encode_cap(&c.parent_cap, out);
    out.push_str(",\"sub\":");
    encode_forest(&c.sub, out);
    out.push('}');
}

// ---- WireTurn envelope (FFI.lean:2646 encodeWTurn) ----

fn encode_wturn(t: &WireTurn, out: &mut String) -> Result<(), MarshalError> {
    out.push_str("{\"agent\":");
    push_nat(out, t.agent);
    out.push_str(",\"nonce\":");
    push_nat(out, t.nonce);
    out.push_str(",\"fee\":");
    push_int(out, t.fee);
    out.push_str(",\"valid_until\":");
    push_nat(out, t.valid_until);
    out.push_str(",\"prev\":\"");
    out.push_str(&to_hex32(t.prev_hash));
    out.push_str("\",\"root\":");
    encode_forest(&t.root, out);
    out.push('}');
    Ok(())
}

// ---- WireState (FFI.lean:2561 encodeWState), all NINE fields ----

fn encode_wstate(w: &WireState, out: &mut String) -> Result<(), MarshalError> {
    // cells
    out.push_str("{\"cells\":[");
    for (i, (id, v)) in w.cells.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('[');
        push_nat(out, *id);
        out.push(',');
        encode_value(v, out);
        out.push(']');
    }
    out.push(']');
    // caps
    out.push_str(",\"caps\":[");
    for (i, (h, cl)) in w.caps.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('[');
        push_nat(out, *h);
        out.push(',');
        encode_cap_list(cl, out);
        out.push(']');
    }
    out.push(']');
    // bal: [cell,asset,amt]
    out.push_str(",\"bal\":[");
    for (i, (cell, asset, amt)) in w.bal.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('[');
        push_nat(out, *cell);
        out.push(',');
        push_nat(out, *asset);
        out.push(',');
        push_int(out, *amt);
        out.push(']');
    }
    out.push(']');
    // escrows: [id,creator,recipient,amount,resolved,asset,bridge]
    out.push_str(",\"escrows\":[");
    for (i, e) in w.escrows.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('[');
        push_nat(out, e.id);
        out.push(',');
        push_nat(out, e.creator);
        out.push(',');
        push_nat(out, e.recipient);
        out.push(',');
        push_int(out, e.amount);
        out.push(',');
        out.push(if e.resolved { '1' } else { '0' });
        out.push(',');
        push_nat(out, e.asset);
        out.push(',');
        out.push(if e.bridge { '1' } else { '0' });
        out.push(']');
    }
    out.push(']');
    // nullifiers
    out.push_str(",\"nullifiers\":");
    encode_nats(&w.nullifiers, out);
    // commitments
    out.push_str(",\"commitments\":");
    encode_nats(&w.commitments, out);
    // queues: [id,owner,capacity,[buffer]]
    out.push_str(",\"queues\":[");
    for (i, q) in w.queues.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('[');
        push_nat(out, q.id);
        out.push(',');
        push_nat(out, q.owner);
        out.push(',');
        push_nat(out, q.capacity);
        out.push(',');
        encode_nats(&q.buffer, out);
        out.push(']');
    }
    out.push(']');
    // swiss: [swiss,exporter,target,AUTHS,refcount,CERT]
    out.push_str(",\"swiss\":[");
    for (i, sw) in w.swiss.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('[');
        push_nat(out, sw.swiss);
        out.push(',');
        push_nat(out, sw.exporter);
        out.push(',');
        push_nat(out, sw.target);
        out.push(',');
        encode_auths(&sw.rights, out);
        out.push(',');
        push_nat(out, sw.refcount);
        out.push(',');
        match sw.cert {
            None => out.push_str("{\"none\":0}"),
            Some(n) => {
                out.push_str("{\"some\":");
                push_nat(out, n);
                out.push('}');
            }
        }
        out.push(']');
    }
    out.push(']');
    // revoked (the NEW 9th field; FFI.lean:2570)
    out.push_str(",\"revoked\":");
    encode_nats(&w.revoked, out);
    out.push('}');
    Ok(())
}

fn encode_nats(ns: &[u64], out: &mut String) {
    out.push('[');
    for (i, n) in ns.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        push_nat(out, *n);
    }
    out.push(']');
}

// ===================================================================
// T9 DECODE — unmarshal_result(&str) -> Result<TurnResult, UnmarshalError>.
// A STRICT recursive descent mirroring parseWWire/parseWState (fail-closed; the WHOLE
// string must be consumed). Maps the empty-state sentinel to MalformedWireSentinel.
// ===================================================================

/// The decoded turn result `{"state":STATEW,"loglen":N,"ok":B}`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TurnResult {
    /// `ok == 1`: the turn COMMITTED. `ok == 0` with a non-empty state: legitimate ROLLBACK
    /// (state echoed unchanged). `ok == 0` with the empty sentinel is reported as an Err.
    pub committed: bool,
    /// The post-state (commit) OR the echoed pre-state (rollback).
    pub state: WireState,
    /// Receipt-log length; 0 on rollback.
    pub loglen: u64,
}

pub fn unmarshal_result(s: &str) -> Result<TurnResult, UnmarshalError> {
    let mut p = Parser::new(s);
    p.lit("{\"state\":").map_err(|e| p.err(e))?;
    let state = parse_wstate(&mut p)?;
    p.lit(",\"loglen\":").map_err(|e| p.err(e))?;
    let loglen = p.nat().map_err(|e| p.err(e))?;
    p.lit(",\"ok\":").map_err(|e| p.err(e))?;
    let ok = p.flag().map_err(|e| p.err(e))?;
    p.lit("}").map_err(|e| p.err(e))?;
    p.expect_eof().map_err(|e| p.err(e))?;

    // ok:0 + the empty 9-field sentinel = the wire we SENT was malformed (a bug), not a
    // legitimate turn rejection. Surface it loudly so a marshalling bug is never mistaken
    // for a rollback.
    if !ok && state.is_empty_sentinel() {
        return Err(UnmarshalError::MalformedWireSentinel);
    }
    Ok(TurnResult { committed: ok, state, loglen })
}

// ---- the strict recursive-descent parser (mirrors FFI.lean lit/parseInt/parseNat) ----

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> Parser<'a> {
    fn new(s: &'a str) -> Self {
        Parser { s: s.as_bytes(), i: 0 }
    }
    fn err(&self, why: String) -> UnmarshalError {
        UnmarshalError::OutputParse { at: self.i, why }
    }
    fn lit(&mut self, lit: &str) -> Result<(), String> {
        let b = lit.as_bytes();
        if self.i + b.len() <= self.s.len() && &self.s[self.i..self.i + b.len()] == b {
            self.i += b.len();
            Ok(())
        } else {
            Err(format!("expected `{lit}`"))
        }
    }
    /// Try to consume a literal; return whether it matched (no error on miss). For dispatch.
    fn try_lit(&mut self, lit: &str) -> bool {
        self.lit(lit).is_ok()
    }
    fn peek(&self) -> Option<u8> {
        self.s.get(self.i).copied()
    }
    fn int(&mut self) -> Result<i128, String> {
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        let dstart = self.i;
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            self.i += 1;
        }
        if self.i == dstart {
            return Err("expected digits".into());
        }
        let txt = std::str::from_utf8(&self.s[start..self.i]).map_err(|e| e.to_string())?;
        txt.parse::<i128>().map_err(|e| format!("bad int `{txt}`: {e}"))
    }
    fn nat(&mut self) -> Result<u64, String> {
        let v = self.int()?;
        if v < 0 {
            return Err(format!("negative nat {v}"));
        }
        if v > u64::MAX as i128 {
            return Err(format!("nat overflow {v}"));
        }
        Ok(v as u64)
    }
    /// A flag: exactly `0` or `1`.
    fn flag(&mut self) -> Result<bool, String> {
        match self.peek() {
            Some(b'0') => {
                self.i += 1;
                Ok(false)
            }
            Some(b'1') => {
                self.i += 1;
                Ok(true)
            }
            other => Err(format!("expected 0/1 flag, got {other:?}")),
        }
    }
    /// Consume EXACTLY 64 hex chars; decode the big-endian value into the low u64 (the high
    /// 192 bits are ignored — a u64 round-trips losslessly, a wider digest is truncated, which
    /// is acceptable because the wire only carries our zero-padded u64-origin digests).
    fn hex32(&mut self) -> Result<u64, String> {
        if self.i + 64 > self.s.len() {
            return Err("expected 64 hex chars".into());
        }
        let mut acc: u64 = 0;
        for k in 0..64 {
            let c = self.s[self.i + k];
            let nib = match c {
                b'0'..=b'9' => (c - b'0') as u64,
                b'a'..=b'f' => (c - b'a' + 10) as u64,
                b'A'..=b'F' => (c - b'A' + 10) as u64,
                _ => return Err(format!("non-hex char at {}", self.i + k)),
            };
            // big-endian fold into the low 64 bits (wrapping; high nibbles overflow away).
            acc = acc.wrapping_mul(16).wrapping_add(nib);
        }
        self.i += 64;
        Ok(acc)
    }
    fn string(&mut self) -> Result<String, String> {
        self.lit("\"")?;
        let mut out = String::new();
        loop {
            match self.peek() {
                Some(b'"') => {
                    self.i += 1;
                    return Ok(out);
                }
                Some(b'\\') => {
                    self.i += 1;
                    match self.peek() {
                        Some(b'"') => out.push('"'),
                        Some(b'\\') => out.push('\\'),
                        other => return Err(format!("bad escape {other:?}")),
                    }
                    self.i += 1;
                }
                Some(c) => {
                    out.push(c as char);
                    self.i += 1;
                }
                None => return Err("unterminated string".into()),
            }
        }
    }
    fn expect_eof(&self) -> Result<(), String> {
        if self.i == self.s.len() {
            Ok(())
        } else {
            Err("trailing bytes".into())
        }
    }
}

// ---- value/cell/cap/side-table parsers (mirror parseValueW / parseCellsW / ...) ----

fn parse_value(p: &mut Parser) -> Result<WireValue, String> {
    if p.try_lit("{\"int\":") {
        let i = p.int()?;
        p.lit("}")?;
        Ok(WireValue::Int(i))
    } else if p.try_lit("{\"dig\":\"") {
        let d = p.hex32()?;
        p.lit("\"}")?;
        Ok(WireValue::Dig(d))
    } else if p.try_lit("{\"sym\":") {
        let s = p.nat()?;
        p.lit("}")?;
        Ok(WireValue::Sym(s))
    } else if p.try_lit("{\"rec\":") {
        let fs = parse_fields(p)?;
        p.lit("}")?;
        Ok(WireValue::Record(fs))
    } else {
        Err("unknown value".into())
    }
}

fn parse_fields(p: &mut Parser) -> Result<Vec<(String, WireValue)>, String> {
    if p.try_lit("[]") {
        return Ok(vec![]);
    }
    p.lit("[")?;
    let mut out = Vec::new();
    loop {
        p.lit("[")?;
        let name = p.string()?;
        p.lit(",")?;
        let v = parse_value(p)?;
        p.lit("]")?;
        out.push((name, v));
        match p.peek() {
            Some(b',') => p.i += 1,
            Some(b']') => {
                p.i += 1;
                break;
            }
            _ => return Err("expected , or ] in fields".into()),
        }
    }
    Ok(out)
}

fn parse_auths(p: &mut Parser) -> Result<Vec<Auth>, String> {
    if p.try_lit("[]") {
        return Ok(vec![]);
    }
    p.lit("[")?;
    let mut out = Vec::new();
    loop {
        let tag = p.nat()?;
        let a = match tag {
            0 => Auth::Read,
            1 => Auth::Write,
            2 => Auth::Grant,
            3 => Auth::Call,
            4 => Auth::Reply,
            5 => Auth::Reset,
            6 => Auth::Control,
            _ => return Err(format!("bad auth tag {tag}")),
        };
        out.push(a);
        match p.peek() {
            Some(b',') => p.i += 1,
            Some(b']') => {
                p.i += 1;
                break;
            }
            _ => return Err("expected , or ] in auths".into()),
        }
    }
    Ok(out)
}

fn parse_cap(p: &mut Parser) -> Result<Cap, String> {
    if p.try_lit("{\"null\":0}") {
        Ok(Cap::Null)
    } else if p.try_lit("{\"node\":") {
        let t = p.nat()?;
        p.lit("}")?;
        Ok(Cap::Node(t))
    } else if p.try_lit("{\"ep\":[") {
        let t = p.nat()?;
        p.lit(",")?;
        let r = parse_auths(p)?;
        p.lit("]")?;
        p.lit("}")?;
        Ok(Cap::Endpoint(t, r))
    } else {
        Err("unknown cap".into())
    }
}

fn parse_cap_list(p: &mut Parser) -> Result<Vec<Cap>, String> {
    if p.try_lit("[]") {
        return Ok(vec![]);
    }
    p.lit("[")?;
    let mut out = Vec::new();
    loop {
        out.push(parse_cap(p)?);
        match p.peek() {
            Some(b',') => p.i += 1,
            Some(b']') => {
                p.i += 1;
                break;
            }
            _ => return Err("expected , or ] in cap list".into()),
        }
    }
    Ok(out)
}

fn parse_nats(p: &mut Parser) -> Result<Vec<u64>, String> {
    if p.try_lit("[]") {
        return Ok(vec![]);
    }
    p.lit("[")?;
    let mut out = Vec::new();
    loop {
        out.push(p.nat()?);
        match p.peek() {
            Some(b',') => p.i += 1,
            Some(b']') => {
                p.i += 1;
                break;
            }
            _ => return Err("expected , or ] in nats".into()),
        }
    }
    Ok(out)
}

/// Parse the 9-field WIDE STATE (strict field order; the closing `}` is consumed).
fn parse_wstate(p: &mut Parser) -> Result<WireState, UnmarshalError> {
    let map = |e: String, p: &Parser| UnmarshalError::OutputParse { at: p.i, why: e };
    // cells
    p.lit("{\"cells\":").map_err(|e| p.err(e))?;
    let cells = parse_list(p, |p| {
        p.lit("[")?;
        let id = p.nat()?;
        p.lit(",")?;
        let v = parse_value(p)?;
        p.lit("]")?;
        Ok((id, v))
    })
    .map_err(|e| map(e, p))?;
    // caps
    p.lit(",\"caps\":").map_err(|e| p.err(e))?;
    let caps = parse_list(p, |p| {
        p.lit("[")?;
        let h = p.nat()?;
        p.lit(",")?;
        let cl = parse_cap_list(p)?;
        p.lit("]")?;
        Ok((h, cl))
    })
    .map_err(|e| map(e, p))?;
    // bal
    p.lit(",\"bal\":").map_err(|e| p.err(e))?;
    let bal = parse_list(p, |p| {
        p.lit("[")?;
        let cell = p.nat()?;
        p.lit(",")?;
        let asset = p.nat()?;
        p.lit(",")?;
        let amt = p.int()?;
        p.lit("]")?;
        Ok((cell, asset, amt))
    })
    .map_err(|e| map(e, p))?;
    // escrows
    p.lit(",\"escrows\":").map_err(|e| p.err(e))?;
    let escrows = parse_list(p, |p| {
        p.lit("[")?;
        let id = p.nat()?;
        p.lit(",")?;
        let creator = p.nat()?;
        p.lit(",")?;
        let recipient = p.nat()?;
        p.lit(",")?;
        let amount = p.int()?;
        p.lit(",")?;
        let resolved = p.flag()?;
        p.lit(",")?;
        let asset = p.nat()?;
        p.lit(",")?;
        let bridge = p.flag()?;
        p.lit("]")?;
        Ok(WireEscrow { id, creator, recipient, amount, resolved, asset, bridge })
    })
    .map_err(|e| map(e, p))?;
    // nullifiers
    p.lit(",\"nullifiers\":").map_err(|e| p.err(e))?;
    let nullifiers = parse_nats(p).map_err(|e| map(e, p))?;
    // commitments
    p.lit(",\"commitments\":").map_err(|e| p.err(e))?;
    let commitments = parse_nats(p).map_err(|e| map(e, p))?;
    // queues
    p.lit(",\"queues\":").map_err(|e| p.err(e))?;
    let queues = parse_list(p, |p| {
        p.lit("[")?;
        let id = p.nat()?;
        p.lit(",")?;
        let owner = p.nat()?;
        p.lit(",")?;
        let capacity = p.nat()?;
        p.lit(",")?;
        let buffer = parse_nats(p)?;
        p.lit("]")?;
        Ok(WireQueue { id, owner, capacity, buffer })
    })
    .map_err(|e| map(e, p))?;
    // swiss
    p.lit(",\"swiss\":").map_err(|e| p.err(e))?;
    let swiss = parse_list(p, |p| {
        p.lit("[")?;
        let swiss = p.nat()?;
        p.lit(",")?;
        let exporter = p.nat()?;
        p.lit(",")?;
        let target = p.nat()?;
        p.lit(",")?;
        let rights = parse_auths(p)?;
        p.lit(",")?;
        let refcount = p.nat()?;
        p.lit(",")?;
        let cert = if p.try_lit("{\"none\":0}") {
            None
        } else if p.try_lit("{\"some\":") {
            let n = p.nat()?;
            p.lit("}")?;
            Some(n)
        } else {
            return Err("expected {\"none\":0} or {\"some\":N}".into());
        };
        p.lit("]")?;
        Ok(WireSwiss { swiss, exporter, target, rights, refcount, cert })
    })
    .map_err(|e| map(e, p))?;
    // revoked (the NEW 9th field)
    p.lit(",\"revoked\":").map_err(|e| p.err(e))?;
    let revoked = parse_nats(p).map_err(|e| map(e, p))?;
    // close
    p.lit("}").map_err(|e| p.err(e))?;
    Ok(WireState {
        cells,
        caps,
        bal,
        escrows,
        nullifiers,
        commitments,
        queues,
        swiss,
        revoked,
    })
}

/// Parse a JSON array `[]` | `[X(,X)*]` of items parsed by `item`.
fn parse_list<T>(
    p: &mut Parser,
    mut item: impl FnMut(&mut Parser) -> Result<T, String>,
) -> Result<Vec<T>, String> {
    if p.try_lit("[]") {
        return Ok(vec![]);
    }
    p.lit("[")?;
    let mut out = Vec::new();
    loop {
        out.push(item(p)?);
        match p.peek() {
            Some(b',') => p.i += 1,
            Some(b']') => {
                p.i += 1;
                break;
            }
            _ => return Err("expected , or ] in array".into()),
        }
    }
    Ok(out)
}
