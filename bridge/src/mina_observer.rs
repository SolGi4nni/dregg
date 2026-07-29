//! `mina_observer`: the **live off-chain Mina observer** for the settlement loop.
//!
//! This is the Mina-direction twin of [`crate::midnight_observer`] /
//! [`crate::solana_relayer`]: it turns the library-only Mina settlement state
//! machine ([`crate::mina`]) into a watching service that confirms an outbound
//! dregg→Mina settlement landed on a genuinely *finalized* Mina block.
//!
//! It speaks the **real Mina GraphQL** over an injected byte-pipe (the same
//! [`crate::solana_relayer::JsonRpcTransport`] seam — Mina GraphQL is a JSON `POST
//! {query}`): `bestChain` for the canonical segment and
//! `account(publicKey){ zkappState }` for the dregg federation zkApp's settled root.
//!
//! # ⚑ WHAT THIS MODULE USED TO DO, AND WHY IT WAS NOT A FINALITY CHECK
//!
//! Until 2026-07-29 `observe_settlement` read `bestChain`, took the **maximum**
//! `blockHeight` out of whatever came back, subtracted the settlement's submitted
//! height, and accepted when the difference cleared `confirmation_depth`. Its
//! docstring called that "verifies finality". It was not a check:
//!
//!   * the returned blocks were **never checked to form a chain** — no
//!     `previousStateHash` linkage, no height contiguity, so an arbitrary bag of
//!     blocks passed;
//!   * the settlement's own block was **never checked to be among them**, and with
//!     the shipped `best_chain_length: 16` against a mainnet `confirmation_depth:
//!     290` it *could not be* — the window was 274 blocks too short to contain the
//!     evidence the depth claim was about;
//!   * so **one fabricated block** with a large `blockHeight` finalized every
//!     settlement instantly. Both numbers came from the same untrusted endpoint,
//!     and the "verification" was a subtraction between them.
//!
//! # WHAT IT DOES NOW, PER STEP — VERIFIED, CHECKED, OR TRUSTED
//!
//! | step | status |
//! |---|---|
//! | the accept/reject DECISION | **VERIFIED** — rendered by the Lean gate `dregg_mina_lc_verify` (`Dregg2.Bridge.LightClientMinaGate`), proven by `minaVerifyDecision_refines` (axiom-free `rfl`) to BE `minaVerify`, over which `mina_no_forgery` is proven. No Rust twin decides it. |
//! | the confirmation depth | **VERIFIED, and now WITNESSED** — `minaVerifyDecision_depth_witnessed` turns an accept into "the depth is backed by that many exhibited, parent-linked blocks". The `anchor_height <= submitted_height` conjunct is what makes it provable; without it a ONE-block segment witnesses a depth of 1001 (`witnessedDepth_unbounded_without_anchor_bound`). |
//! | each state hash's encoding | **CHECKED in Rust** — genuine Base58Check: version byte `0x10`, bin_prot version `0x01`, a 4-byte double-SHA-256 checksum that must match, and a 32-byte little-endian `Fp` element. Garbage no longer passes as a state hash. |
//! | each state hash's canonicality | **CHECKED in Rust** (`< 2^254 < p`), the RESULT crossing into the gate as `cn`. This is not decoration: Poseidon's `absorbAt` enters every input through `(state + x) % p`, so a non-canonical element is invisible at the digest and an anchor `A + p` reaches the same tip as `A` (`LightClientMinaHashFold.stateChain_anchor_shift_collides`). |
//! | the parent linkage | **CHECKED in Rust**, RESULT crossing as `lk` — the named carrier. Compared over DECODED field elements, not Base58 strings. ⚑ TRUSTED here: that a block's `stateHash` really is the Poseidon hash of its protocol state. The Lean side MODELS the linkage as that Poseidon chain (`stateChain`, whose terminal value is the tip state hash) and can DERIVE the carrier from it, but the in-circuit composition is that file's RESIDUAL #1 and nothing deploys it. |
//! | each block's Pickles proof — DECODE | **CHECKED in Rust** (since 2026-07-29). `bestChain` now fetches `protocolStateProof` and [`crate::mina_pickles`] decodes the base64url binprot `Mina_base.Proof.Stable.V2` byte-exactly: every `PaddedSeq` terminator, every `Option` tag, every bounded array, every binprot integer in its CANONICAL width, every field element canonical for its Pasta modulus, and **every byte consumed**. On the real devnet block that is 294 field elements checked and 11138 bytes landed on exactly. A truncated, extended, re-widened or out-of-field proof is a REFUSAL. |
//! | each block's Pickles proof — PREAMBLE | **VERIFIED** — the decoded counts cross into the Lean gate `dregg_mina_wrap_shape_ok` (`Dregg2.Bridge.PicklesWrapShapeGate`), whose decision `picklesWrapShapeOk_is_shapeOkRec` proves IS `KimchiVerify.shapeOkRec` — the `verifier.rs:810-830` preamble — plus the accumulator-count and IPA-round agreements. `real_block_wrap_shape_accepts` pins the accept on block 539508; `real_block_wrap_shape_refused_by_freeze` pins that the retired `prevLen = 0` form REFUSES a real Mina block. The result IS the gate's `pk` bit. ⚑ TRUSTED here, and it is a lot: the verifier-index parameters themselves ([`crate::mina_pickles::MinaWrapIndexParams`]) — modelling the Wrap VK is P8/P9 and is NOT STARTED. |
//! | each block's Pickles proof — ARITHMETIC | **NOT CHECKED, and not reachable from here.** C3 (the Fiat–Shamir transcript), C5/C8, the group assembly, `public_comm` and the IPA opening relation all exist and all run on a real Mina block — as `by decide` over the LITERAL constants of one extracted block (`MinaRealBlockGate`, `MinaRealBlockTranscript`, `MinaWrap*`). They are not functions of a proof. Two independent walls, both measured: the values they need (verifier index, SRS, `endo_r`, the 40-element public input) are **not on the wire** — the proof's `messages_for_next_step_proof.app_state` is literally `()` — and they come from a dependency graph deliberately outside this workspace; and their cost is kernel-`decide` cost: 82 s for C5/C8, 153 s + 75 s for the opening rung, **~3.5 h of serial kernel and ~28 GB** for the terminal `⟨s, srs.g⟩` MSM, per block. |
//! | the proof↔block BINDING | **NOT CHECKED.** ⚑ A Wrap proof is not self-binding to its block. `app_state` is `()` on the wire and the verifier reconstructs the public input from the BLOCK plus the VK's `dlog_plonk_index`, so nothing in the proof's bytes says which block it proves. An endpoint may therefore serve block A's proof under block B's header and every check above still passes. Closing this needs the public-input assembly (a Poseidon over `Fp` against the VK) — the same object P8/P9 needs, and the honest next rung. |
//! | the zkApp's settled root | **CHECKED in Rust** — the on-chain `provenRoot` must equal the dregg root we settled. |
//! | FORK CHOICE | **NOT CHECKED, ANYWHERE.** Ouroboros Samasika's chain selection (VRF-weighted density, long-range) is formalized nowhere in this tree. An accept says "this exhibited segment is anchored, linked, canonical and `k` deep"; it does not say "and it is the chain the network selected". Two `k`-deep segments under different anchors are indistinguishable here. |
//!
//! So the rung moved from *trusting a node's arithmetic* to *checking an anchored,
//! parent-linked, canonical segment whose depth is evidence-backed and each of whose
//! blocks carries a well-formed Pickles proof of the shape the pinned verifier index
//! demands*, with every decision rendered by the archive. **It is not a Mina light
//! client**, and verifying each block's proof would not make it one: fork choice is
//! what turns an anchored-segment verifier into a chain follower, and it is being
//! built by sibling lanes.
//!
//! # ⚑ FAIL-CLOSED — AND THE TWO WRONG DIAGNOSES THAT KEPT IT REFUSING
//!
//! `dregg_mina_lc_verify` and `dregg_mina_wrap_shape_ok` were absent from every
//! archive until 2026-07-29, and this file carried two successive explanations that
//! were both wrong. First: "`LightClientMinaGate` is not rooted in `Dregg2.lean`" —
//! it was rooted (`Dregg2.lean:1536-1537`). Then: "what is stale is the committed Lean
//! SEED" — the seed is not committed (`dregg-lean-ffi/.gitignore:7`; it has never been
//! a tracked file), and it never carries these symbols anyway: they are SPLICE-ONLY,
//! written into the per-`OUT_DIR` working archive by `dregg-lean-ffi/build.rs` on
//! every build.
//!
//! The actual cause was one import. `build.rs` builds exactly one Lake target,
//! `Dregg2.FFI`, and splices exactly `metatheory/Dregg2/FFI.lean`'s import closure —
//! so a gate rooted only in `Dregg2.lean` ELABORATES but emits no `:c` facet and its
//! `@[export]` never enters the archive. That is layer 1 of `Dregg2/FFI.lean` §4, the
//! failure that made `dregg_{eth,mpt,tm}_lc_verify` dark, re-entered. CLOSED by adding
//! both modules to `Dregg2/FFI.lean`; both symbols are now on `build.rs`'s
//! `REQUIRED_DECISION_EXPORTS`, so a strict build cannot re-enter the dark state
//! quietly. When the gate IS absent, [`MinaObserver::observe_settlement`] returns
//! [`ObserveError::VerifiedGateUnavailable`] for every settlement. That is deliberate
//! and it is the whole posture: this repo has a
//! named, recurring defect class where an absent verified gate logs and PROCEEDS, and a
//! light client that silently falls back when its verifier is missing looks gated and
//! is not. There is no fallback, no `allow_unverified` flag, and no environment
//! variable that opens it — and in particular the retired `NEUTRAL_PICKLES_OK` constant
//! was **deleted**, not left behind as a fallback, because a constant that silently
//! means "fine" is that defect class with a comment on it.
//!
//! ⚑ **What the retirement costs, said plainly.** `bestChain` now carries ~11 KB of
//! proof per block, so a mainnet-depth (~290) window is ~3.2 MB and the
//! [`MAX_SEGMENT_BLOCKS`] bound is ~45 MB in one response. That is the price of the
//! evidence; it was not being paid before because the evidence was not being asked for.
//!
//! # WHAT `NEUTRAL_PICKLES_OK`'s RETIREMENT ACTUALLY BOUGHT
//!
//! Not "the observer verifies Mina blocks". Four specific things, and the fourth is the
//! one that matters most:
//!
//! 1. **An endpoint must now EXHIBIT each block's blockchain SNARK.** Before, a node
//!    could serve a segment of bare headers and every check passed. A block whose proof
//!    is withheld no longer counts toward a confirmation depth. That is a real
//!    availability obligation on the counterparty, and it is the kind of thing a depth
//!    claim was always pretending to have.
//! 2. **The exhibited bytes must be a real Mina proof.** Byte-exact, canonical, exact-
//!    fit — 294 field elements checked and 11138 bytes landed on, on the real object.
//!    Fabricating one is no longer free: it costs a well-formed
//!    `Mina_base.Proof.Stable.V2` at the right shape, not an arbitrary blob.
//! 3. **The shape decision is VERIFIED, and it is the one that was getting Mina wrong.**
//!    `shapeOkRec` at `prev_challenges = 2` is exactly where the retired `prevLen = 0`
//!    freeze REJECTED real Mina blocks. Wiring the observer to it means the deployed
//!    path and the proved path are the same predicate, checked on the same real block.
//! 4. ⚑ **A fail-open constant became a fail-closed dependency.** `NEUTRAL_PICKLES_OK`
//!    was a `true` that could never go red — the exact class this repo keeps
//!    rediscovering. The Pickles conjunct is now a value that CAN be false and a gate
//!    that can be absent, and both outcomes are refusals. The observer got *less* able
//!    to confirm settlements, which is the direction that counts.
//!
//! And what it did **not** buy: the arithmetic of a Wrap verify (fixture-bound, see the
//! table), the binding of a proof to its block (nothing checks it), the verifier index
//! (trusted config), and fork choice (formalized nowhere). Verifying each block's proof
//! is necessary for a Mina light client and nowhere near sufficient; Samasika chain
//! selection is what turns an anchored-segment verifier into a chain follower, and it
//! is not here.

use crate::mina_pickles::{MinaWrapIndexParams, WrapProofError, decode_protocol_state_proof};
use crate::solana_relayer::{JsonRpcTransport, RpcError};

// ===========================================================================
// The chain view the observer needs (the `MinaRpc` seam)
// ===========================================================================

/// One block on Mina's canonical chain, as `bestChain` returns it. Carries just
/// the fields the observer's segment check needs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaBlock {
    /// The block's state hash (Base58Check), the chain identity.
    pub state_hash: String,
    /// The block height (`protocolState.consensusState.blockHeight`).
    pub block_height: u64,
    /// The parent block's state hash.
    pub parent_state_hash: String,
    /// **The block's Pickles/Kimchi Wrap proof** (`protocolStateProof`), base64url
    /// binprot `Mina_base.Proof.Stable.V2` — the blockchain SNARK. Fetched since
    /// 2026-07-29; before that the observer did not ask for it and passed a constant
    /// for the gate's Pickles conjunct. An empty string is what the endpoint returning
    /// nothing looks like, and it is a REFUSAL, not a skip
    /// ([`ObserveError::WrapProofAbsent`]).
    pub protocol_state_proof: String,
}

/// A dregg federation zkApp account's settled state, as `account(publicKey)`
/// returns it: the 8 app-state Fields (each a decimal-string field element).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaZkappAccount {
    /// The 8 zkApp app-state Fields (decimal strings over GraphQL). The dregg
    /// `provenRoot` is encoded across `app_state[0]` (low 128 bits) and
    /// `app_state[1]` (high 128 bits) — see [`decode_root_from_fields`].
    pub app_state: Vec<String>,
}

/// The observer's view of the Mina chain. A real GraphQL client
/// ([`MinaGraphQlRpc`]) and the in-memory test double ([`MockMinaRpc`]) both
/// implement it; the observer is generic over it so the watch→verify loop is
/// tested without a network.
pub trait MinaRpc {
    /// `bestChain(maxLength: n)` — the canonical chain OLDEST-FIRST (the LAST
    /// element is the tip), which is the order real Mina GraphQL returns.
    fn best_chain(&self, max_length: u32) -> Result<Vec<MinaBlock>, RpcError>;

    /// `account(publicKey: pk){ zkappState }` — the zkApp's current app-state
    /// Fields (absent / not-a-zkApp ⟹ `None`).
    fn zkapp_account(&self, public_key: &str) -> Result<Option<MinaZkappAccount>, RpcError>;
}

// ===========================================================================
// Mina state hashes: Base58Check → a canonical Pasta `Fp` element
// ===========================================================================

/// The Base58 alphabet Mina uses (Bitcoin's).
const B58: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

/// Mina's Base58Check version byte for a `State_hash`.
const STATE_HASH_VERSION_BYTE: u8 = 0x10;

/// The bin_prot version byte that prefixes the serialized field element.
const BINPROT_VERSION_BYTE: u8 = 0x01;

/// A Mina protocol-state hash as the `Fp` element it is: 32 bytes, LITTLE-ENDIAN,
/// canonical.
///
/// Constructed only by [`decode_state_hash`], which verifies the Base58Check
/// checksum, the two version bytes and canonicality — so holding one of these is
/// evidence those checks ran. The bytes are private for that reason: the ETH
/// lane's `ProvenErc20Holding` makes its trust rung a `pub` field and is
/// consequently forgeable by struct literal, which is exactly the mistake not to
/// repeat.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MinaStateHash([u8; 32]);

impl MinaStateHash {
    /// The 32 little-endian bytes of the field element.
    pub fn to_le_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// The field element as a decimal string — the form
    /// `Dregg2.Circuit.Emit.LightClientMinaHashFold` pins its two real devnet
    /// state hashes in. Rendering it here is what makes the Rust decoder and the
    /// Lean constants cross-checkable on real chain data (see the tests).
    pub fn to_decimal(&self) -> String {
        // Schoolbook repeated division by 10 over 32-bit limbs (little-endian).
        let mut limbs = [0u32; 8];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut b = [0u8; 4];
            b.copy_from_slice(&self.0[i * 4..i * 4 + 4]);
            *limb = u32::from_le_bytes(b);
        }
        let mut digits: Vec<u8> = Vec::new();
        loop {
            if limbs.iter().all(|&l| l == 0) {
                break;
            }
            let mut rem: u64 = 0;
            for limb in limbs.iter_mut().rev() {
                let cur = (rem << 32) | u64::from(*limb);
                *limb = (cur / 10) as u32;
                rem = cur % 10;
            }
            digits.push(b'0' + rem as u8);
        }
        if digits.is_empty() {
            return "0".to_string();
        }
        digits.reverse();
        String::from_utf8(digits).expect("ASCII digits")
    }

    /// Whether the element is CANONICAL in the sense the Lean width gate forces:
    /// `< 2^254`, and `2^254 < p` (`LightClientMinaHashFold.pow254_lt_pN`), so an
    /// admitted element is a canonical `Fp` element.
    ///
    /// The test is exactly "the top two bits of the most significant byte are
    /// zero" — `2^254` is one bit below the 32-byte ceiling.
    pub fn is_canonical(&self) -> bool {
        self.0[31] < 0x40
    }
}

/// Decode a Base58 string to bytes (no checksum handling).
fn base58_decode(s: &str) -> Option<Vec<u8>> {
    let mut out: Vec<u8> = vec![0];
    for ch in s.bytes() {
        let val = B58.iter().position(|&c| c == ch)? as u32;
        let mut carry = val;
        for byte in out.iter_mut().rev() {
            let cur = u32::from(*byte) * 58 + carry;
            *byte = (cur & 0xff) as u8;
            carry = cur >> 8;
        }
        while carry > 0 {
            out.insert(0, (carry & 0xff) as u8);
            carry >>= 8;
        }
    }
    // Leading '1's are leading zero bytes.
    let leading_zeros = s.bytes().take_while(|&c| c == b'1').count();
    // Drop the single synthetic leading zero we seeded with, then re-add the real ones.
    let first_nonzero = out.iter().position(|&b| b != 0).unwrap_or(out.len());
    let mut res = vec![0u8; leading_zeros];
    res.extend_from_slice(&out[first_nonzero..]);
    Some(res)
}

/// **Decode a Mina Base58Check state hash into the `Fp` element it encodes**, the
/// way Mina encodes it: `version(0x10) || binprot(0x01) || field[32] LE ||
/// checksum[4]`, where the checksum is the first 4 bytes of
/// `SHA256(SHA256(version || payload))`.
///
/// Every failure is a REFUSAL, not a warning: a bad checksum, a wrong version
/// byte, a wrong length or a NON-CANONICAL field element (`>= 2^254`) all return
/// an error. Before this existed, `state_hash` was an opaque `String` the observer
/// never looked inside.
pub fn decode_state_hash(s: &str) -> Result<MinaStateHash, ObserveError> {
    use sha2::{Digest, Sha256};

    let bad = |why: &str| ObserveError::MalformedStateHash {
        state_hash: s.to_string(),
        reason: why.to_string(),
    };

    let raw = base58_decode(s).ok_or_else(|| bad("not valid Base58"))?;
    if raw.len() != 1 + 1 + 32 + 4 {
        return Err(bad(&format!(
            "expected 38 Base58Check bytes (version+binprot+32+checksum), got {}",
            raw.len()
        )));
    }
    let (body, checksum) = raw.split_at(raw.len() - 4);
    let calc = Sha256::digest(Sha256::digest(body));
    if calc[..4] != *checksum {
        return Err(bad("Base58Check checksum mismatch"));
    }
    if body[0] != STATE_HASH_VERSION_BYTE {
        return Err(bad(&format!(
            "version byte is 0x{:02x}, expected 0x{STATE_HASH_VERSION_BYTE:02x} (State_hash)",
            body[0]
        )));
    }
    if body[1] != BINPROT_VERSION_BYTE {
        return Err(bad(&format!(
            "bin_prot version byte is 0x{:02x}, expected 0x{BINPROT_VERSION_BYTE:02x}",
            body[1]
        )));
    }
    let mut fe = [0u8; 32];
    fe.copy_from_slice(&body[2..]);
    let h = MinaStateHash(fe);
    if !h.is_canonical() {
        return Err(bad(
            "field element is NON-CANONICAL (>= 2^254): Poseidon absorbs inputs mod p, so a \
             non-canonical element aliases a canonical one at the digest",
        ));
    }
    Ok(h)
}

// ===========================================================================
// proven-root <-> app-state Field encoding
// ===========================================================================

/// Encode a 32-byte dregg proven root into the two app-state Fields a dregg
/// federation zkApp stores it in: `field[0]` = the low 16 bytes (a 128-bit value,
/// well within Mina's ~254-bit Field), `field[1]` = the high 16 bytes. Returned as
/// decimal strings (the GraphQL wire form). The inverse is
/// [`decode_root_from_fields`].
pub fn encode_root_to_fields(root: &[u8; 32]) -> [String; 2] {
    let mut high = [0u8; 16];
    high.copy_from_slice(&root[0..16]);
    let mut low = [0u8; 16];
    low.copy_from_slice(&root[16..32]);
    [
        u128::from_be_bytes(low).to_string(),
        u128::from_be_bytes(high).to_string(),
    ]
}

/// Decode a 32-byte dregg proven root from the two app-state Field decimal
/// strings (`low`, `high`). Each must be a `u128` (a 128-bit Field half); a value
/// that does not parse as `u128` is rejected.
pub fn decode_root_from_fields(low: &str, high: &str) -> Result<[u8; 32], ObserveError> {
    let low_v: u128 = low.parse().map_err(|_| ObserveError::MalformedZkappState {
        reason: format!("app_state[0] (low half) is not a u128 Field: `{low}`"),
    })?;
    let high_v: u128 = high
        .parse()
        .map_err(|_| ObserveError::MalformedZkappState {
            reason: format!("app_state[1] (high half) is not a u128 Field: `{high}`"),
        })?;
    let mut root = [0u8; 32];
    root[0..16].copy_from_slice(&high_v.to_be_bytes());
    root[16..32].copy_from_slice(&low_v.to_be_bytes());
    Ok(root)
}

// ===========================================================================
// The real GraphQL client (real Mina GraphQL over an injected byte-pipe)
// ===========================================================================

/// A real Mina GraphQL client: it builds the genuine `bestChain` / `account`
/// queries and parses the genuine response shapes (decimal-string heights and
/// Fields), delegating the actual bytes to an injected [`JsonRpcTransport`] (the
/// same seam the Solana relayer ships — Mina GraphQL is a JSON `POST {query}`).
pub struct MinaGraphQlRpc<T: JsonRpcTransport> {
    /// The GraphQL endpoint, e.g. `http://127.0.0.1:3085/graphql` or a provider.
    pub url: String,
    transport: T,
}

impl<T: JsonRpcTransport> MinaGraphQlRpc<T> {
    /// Build a client for `url` over `transport`.
    pub fn new(url: impl Into<String>, transport: T) -> Self {
        Self {
            url: url.into(),
            transport,
        }
    }

    fn query(&self, query: &str) -> Result<serde_json::Value, RpcError> {
        let req = serde_json::json!({ "query": query });
        let body = serde_json::to_string(&req).map_err(|e| RpcError::Decode(e.to_string()))?;
        let resp = self.transport.post(&self.url, &body)?;
        let v: serde_json::Value =
            serde_json::from_str(&resp).map_err(|e| RpcError::Decode(e.to_string()))?;
        // GraphQL surfaces errors in a top-level `errors` array.
        if let Some(errs) = v.get("errors").and_then(|e| e.as_array()) {
            let message = errs
                .first()
                .and_then(|e| e.get("message"))
                .and_then(|m| m.as_str())
                .unwrap_or("graphql error")
                .to_string();
            return Err(RpcError::Rpc { code: 0, message });
        }
        v.get("data")
            .cloned()
            .ok_or_else(|| RpcError::Decode("missing `data`".into()))
    }
}

impl<T: JsonRpcTransport> MinaRpc for MinaGraphQlRpc<T> {
    fn best_chain(&self, max_length: u32) -> Result<Vec<MinaBlock>, RpcError> {
        // ⚑ `protocolStateProof` is the blockchain SNARK — the base64url binprot
        // `Mina_base.Proof.Stable.V2`. Asking for it is the whole of what retired
        // `NEUTRAL_PICKLES_OK`; before 2026-07-29 this query simply did not.
        let q = format!(
            "{{ bestChain(maxLength: {max_length}) {{ stateHash protocolStateProof protocolState \
             {{ previousStateHash consensusState {{ blockHeight }} }} }} }}"
        );
        let data = self.query(&q)?;
        let arr = data
            .get("bestChain")
            .and_then(|x| x.as_array())
            .ok_or_else(|| RpcError::Decode("bestChain".into()))?;
        arr.iter()
            .map(|b| {
                let state_hash = b
                    .get("stateHash")
                    .and_then(|x| x.as_str())
                    .ok_or_else(|| RpcError::Decode("block.stateHash".into()))?
                    .to_string();
                let protocol = b
                    .get("protocolState")
                    .ok_or_else(|| RpcError::Decode("block.protocolState".into()))?;
                let parent_state_hash = protocol
                    .get("previousStateHash")
                    .and_then(|x| x.as_str())
                    .unwrap_or("")
                    .to_string();
                // blockHeight is a decimal STRING in Mina GraphQL.
                let height_str = protocol
                    .get("consensusState")
                    .and_then(|c| c.get("blockHeight"))
                    .and_then(|x| x.as_str())
                    .ok_or_else(|| RpcError::Decode("block.blockHeight".into()))?;
                let block_height = height_str
                    .parse::<u64>()
                    .map_err(|e| RpcError::Decode(format!("blockHeight `{height_str}`: {e}")))?;
                // Absent / null is the EMPTY string, which `check_block_proofs`
                // refuses. Defaulting to empty rather than erroring here keeps the
                // refusal in one place, with the block's height in the message.
                let protocol_state_proof = b
                    .get("protocolStateProof")
                    .and_then(|x| x.as_str())
                    .unwrap_or("")
                    .to_string();
                Ok(MinaBlock {
                    state_hash,
                    block_height,
                    parent_state_hash,
                    protocol_state_proof,
                })
            })
            .collect()
    }

    fn zkapp_account(&self, public_key: &str) -> Result<Option<MinaZkappAccount>, RpcError> {
        let q = format!("{{ account(publicKey: \"{public_key}\") {{ zkappState }} }}");
        let data = self.query(&q)?;
        let account = match data.get("account") {
            Some(serde_json::Value::Null) | None => return Ok(None),
            Some(a) => a,
        };
        let app_state = match account.get("zkappState") {
            Some(serde_json::Value::Null) | None => return Ok(None),
            Some(serde_json::Value::Array(a)) => a
                .iter()
                .map(|f| {
                    f.as_str()
                        .map(|s| s.to_string())
                        .ok_or_else(|| RpcError::Decode("zkappState[i] not a string".into()))
                })
                .collect::<Result<Vec<_>, _>>()?,
            _ => return Err(RpcError::Decode("zkappState shape".into())),
        };
        Ok(Some(MinaZkappAccount { app_state }))
    }
}

// ===========================================================================
// The observer: watch bestChain → CHECK the segment → VERIFY via the Lean gate
// ===========================================================================

// ⚑ `NEUTRAL_PICKLES_OK` LIVED HERE AND IS GONE (2026-07-29). It was a
// `pub const … : bool = true` passed as the gate's Pickles conjunct because the
// observer never fetched `protocolStateProof`. It is DELETED rather than deprecated:
// a named constant that silently means "fine" is precisely the fail-open shape this
// repo keeps rediscovering, and leaving it as a fallback would mean an absent archive
// could still confirm a settlement. The conjunct is now computed by
// [`MinaObserver::check_block_proofs`] from every block's real proof bytes, and an
// unavailable gate is [`ObserveError::VerifiedGateUnavailable`]. Anything that used to
// import this constant should fail to compile, loudly, and be pointed at the real bit.

/// The observer configuration: which zkApp to watch, the pinned weak-subjectivity
/// anchor the segment must descend from, how deep finality is, and the pinned Wrap
/// verifier-index parameters each block's proof is shaped against.
#[derive(Clone, Debug)]
pub struct MinaObserverConfig {
    /// The dregg federation zkApp address (Base58Check `B62...`).
    pub zkapp_address: String,
    /// **The governance-pinned weak-subjectivity anchor's state hash**
    /// (Base58Check). The exhibited segment must descend from exactly this block.
    /// Without an anchor the "depth" is measured from wherever the endpoint says,
    /// which is what made the old code's subtraction meaningless.
    pub anchor_state_hash: String,
    /// The pinned anchor's blockchain length.
    pub anchor_height: u64,
    /// The number of canonical blocks past a settlement's submitted height before
    /// it is treated as finalized (Ouroboros Samasika depth — e.g. `~290` for
    /// full finality on mainnet; smaller for fast devnets/tests).
    pub confirmation_depth: u64,
    /// **The pinned Wrap verifier-index parameters** every exhibited block's Pickles
    /// proof must be shaped against. ⚑ TRUSTED CONFIG, and the largest trusted thing
    /// the Pickles check rests on — nothing here derives it from the chain. Use
    /// [`MinaWrapIndexParams::DEVNET_BLOCKCHAIN`]; there is deliberately no mainnet
    /// constant, because openmina at HEAD cannot load the mainnet verifier index at all
    /// (`BlockVerifier::make()` panics on a stale serde format), so no mainnet
    /// parameter set has been measured and inventing one would be a guess wearing a
    /// constant's clothes.
    pub wrap_index: MinaWrapIndexParams,
}

/// The largest segment the observer will pull and check in one call.
///
/// A bound is needed because the window size is derived from a height the ENDPOINT
/// claims; without it a hostile endpoint could make the observer request an
/// unbounded number of blocks. When the pinned anchor is further behind the claimed
/// tip than this, the observer refuses ([`ObserveError::AnchorTooFarBehind`]) and
/// the operator advances the pin — which is what a weak-subjectivity anchor is
/// for. `4096` blocks is comfortably past a mainnet `confirmation_depth` of ~290.
pub const MAX_SEGMENT_BLOCKS: u64 = 4096;

impl MinaObserverConfig {
    /// The smallest `bestChain` window that spans the pinned anchor through
    /// `claimed_tip`, or `None` when the anchor is further behind than
    /// [`MAX_SEGMENT_BLOCKS`].
    ///
    /// ⚑ DERIVED, not configured. The old `best_chain_length` field defaulted to
    /// 16 while `confirmation_depth` was 290, so the window could not contain the
    /// evidence the depth claim was about — and nothing noticed, because nothing
    /// looked at the blocks. There is now no way to set it too small: it is
    /// computed from the anchor, and a window that does not reach the anchor
    /// produces a REFUSAL rather than a shorter check.
    ///
    /// `claimed_tip` comes from the untrusted endpoint and is used ONLY to size the
    /// request. Over-claiming just asks for more blocks; under-claiming yields a
    /// window that does not reach the anchor, which is refused.
    pub fn window_for(&self, claimed_tip: u64) -> Option<u32> {
        let span = claimed_tip
            .checked_sub(self.anchor_height)?
            .saturating_add(1);
        if span > MAX_SEGMENT_BLOCKS {
            return None;
        }
        Some(span.min(u64::from(u32::MAX)) as u32)
    }
}

/// A confirmed, depth-finalized dregg settlement observed on Mina — the observer's
/// output. It witnesses that the dregg `proven_root` is the zkApp's on-chain state
/// at a tip reached by an anchored, parent-linked, canonical segment whose length
/// backs the claimed depth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedMinaSettlement {
    /// The dregg proven root read from the zkApp's app-state Fields.
    pub proven_root: [u8; 32],
    /// The canonical tip's state hash, as the `Fp` element it encodes.
    pub tip_state_hash: MinaStateHash,
    /// The tip height, WITNESSED by the exhibited segment
    /// (`anchor_height + segment_len`), not read off a claim.
    pub tip_height: u64,
    /// The height the settlement was submitted at (`StateAdvance.submitted_at`).
    pub submitted_height: u64,
    /// The number of exhibited, parent-linked, canonical blocks above the anchor.
    pub segment_len: u64,
    /// The confirmation depth achieved, witnessed by that segment.
    pub depth: u64,
}

/// Why the observer refused to confirm a settlement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ObserveError {
    /// A GraphQL/RPC call failed.
    Rpc(RpcError),
    /// `bestChain` returned no blocks (cannot read a segment).
    EmptyChain,
    /// A state hash did not decode as a genuine Mina Base58Check state hash, or
    /// decoded to a NON-CANONICAL field element.
    MalformedStateHash {
        /// The offending Base58Check string.
        state_hash: String,
        /// Why it was refused.
        reason: String,
    },
    /// The exhibited blocks do not descend from the pinned weak-subjectivity
    /// anchor.
    NotAnchored {
        /// The pinned anchor's state hash.
        anchor: String,
        /// What the oldest exhibited block claims as its parent.
        oldest_parent: String,
    },
    /// The pinned weak-subjectivity anchor is further behind the claimed tip than
    /// [`MAX_SEGMENT_BLOCKS`], so the observer will not pull a window that spans it.
    /// Advance the pin.
    AnchorTooFarBehind {
        /// The pinned anchor's height.
        anchor_height: u64,
        /// The tip height the endpoint claims.
        claimed_tip: u64,
        /// The largest span the observer will check.
        max_span: u64,
    },
    /// The exhibited blocks are not a parent-linked, height-contiguous chain.
    ChainNotLinked {
        /// The index (into the exhibited segment) where the linkage broke.
        at_index: usize,
        /// Why.
        reason: String,
    },
    /// The verified gate refused: the settlement's depth is not witnessed by the
    /// exhibited segment (too shallow, or submitted below the anchor).
    NotFinalized {
        /// The witnessed tip height.
        tip_height: u64,
        /// The settlement's submitted height.
        submitted_height: u64,
        /// The required depth.
        required_depth: u64,
        /// The number of exhibited, linked blocks backing the claim.
        segment_len: u64,
    },
    /// ⚑ **The verified gate could not run** — the linked archive does not export
    /// `dregg_mina_lc_verify` or `dregg_mina_wrap_shape_ok`. This is a REFUSAL, never
    /// a skipped check: there is no Rust twin to fall back to, and the pre-gate Rust
    /// path was not a check.
    VerifiedGateUnavailable {
        /// What the FFI reported.
        why: String,
    },
    /// A block in the exhibited segment carried **no** `protocolStateProof`. An
    /// endpoint that will not show a block's blockchain SNARK does not get to have that
    /// block counted toward a confirmation depth.
    WrapProofAbsent {
        /// The height of the block that had no proof.
        block_height: u64,
    },
    /// A block's `protocolStateProof` did not decode as a `Mina_base.Proof.Stable.V2`
    /// — bad base64url, a structural deviation, a non-canonical binprot integer, a
    /// field element outside its Pasta field, or trailing bytes.
    MalformedWrapProof {
        /// The height of the offending block.
        block_height: u64,
        /// Where and why, from the decoder.
        reason: String,
    },
    /// The VERIFIED per-block preamble gate REFUSED a block's Wrap proof: its decoded
    /// shape is not the shape the pinned verifier index demands.
    WrapProofShapeRefused {
        /// The height of the offending block.
        block_height: u64,
        /// The proof's recursion count, for the common case (`prev_challenges`
        /// disagreeing with the index) — the exact mismatch the retired `prevLen = 0`
        /// freeze got backwards.
        prev_challenges: usize,
        /// The IPA round count the proof exhibited.
        ipa_rounds: usize,
    },
    /// The zkApp account was absent or not a zkApp (no app state).
    ZkappNotFound,
    /// The zkApp app state was malformed (wrong arity or a non-Field value).
    MalformedZkappState {
        /// Why.
        reason: String,
    },
    /// The zkApp's on-chain root does not equal the dregg root we settled — a
    /// forged/wrong settlement state is refused.
    RootMismatch {
        /// The root read from Mina.
        on_chain: [u8; 32],
        /// The dregg root we expected.
        expected: [u8; 32],
    },
}

impl std::fmt::Display for ObserveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Rpc(e) => write!(f, "{e}"),
            Self::EmptyChain => write!(f, "bestChain returned no blocks"),
            Self::MalformedStateHash { state_hash, reason } => {
                write!(f, "state hash `{state_hash}` refused: {reason}")
            }
            Self::NotAnchored {
                anchor,
                oldest_parent,
            } => write!(
                f,
                "exhibited segment does not descend from the pinned anchor {anchor}: its oldest \
                 block's parent is {oldest_parent}"
            ),
            Self::AnchorTooFarBehind {
                anchor_height,
                claimed_tip,
                max_span,
            } => write!(
                f,
                "pinned anchor at height {anchor_height} is more than {max_span} blocks behind the \
                 claimed tip {claimed_tip}; advance the weak-subjectivity pin"
            ),
            Self::ChainNotLinked { at_index, reason } => {
                write!(
                    f,
                    "exhibited blocks are not a chain at index {at_index}: {reason}"
                )
            }
            Self::NotFinalized {
                tip_height,
                submitted_height,
                required_depth,
                segment_len,
            } => write!(
                f,
                "settlement at height {submitted_height} not finalized: witnessed tip {tip_height} \
                 over {segment_len} linked block(s) is only {} deep (need {required_depth})",
                tip_height.saturating_sub(*submitted_height)
            ),
            Self::VerifiedGateUnavailable { why } => write!(
                f,
                "REFUSED: a verified Mina gate could not run — {why}. There is no unverified \
                 fallback."
            ),
            Self::WrapProofAbsent { block_height } => write!(
                f,
                "block {block_height} carried no protocolStateProof: a block whose blockchain \
                 SNARK is not shown does not count toward a confirmation depth"
            ),
            Self::MalformedWrapProof {
                block_height,
                reason,
            } => write!(
                f,
                "block {block_height}'s protocolStateProof is not a Mina_base.Proof.Stable.V2: \
                 {reason}"
            ),
            Self::WrapProofShapeRefused {
                block_height,
                prev_challenges,
                ipa_rounds,
            } => write!(
                f,
                "the verified preamble gate REFUSED block {block_height}'s Wrap proof \
                 (prev_challenges={prev_challenges}, ipa_rounds={ipa_rounds}): its shape is not \
                 the shape the pinned verifier index demands"
            ),
            Self::ZkappNotFound => write!(f, "zkApp account not found / not a zkApp"),
            Self::MalformedZkappState { reason } => write!(f, "malformed zkApp state: {reason}"),
            Self::RootMismatch { .. } => {
                write!(
                    f,
                    "zkApp on-chain root does not match the settled dregg root"
                )
            }
        }
    }
}

impl std::error::Error for ObserveError {}

impl From<RpcError> for ObserveError {
    fn from(e: RpcError) -> Self {
        Self::Rpc(e)
    }
}

impl ObserveError {
    fn malformed_proof(block_height: u64, e: &WrapProofError) -> Self {
        Self::MalformedWrapProof {
            block_height,
            reason: e.to_string(),
        }
    }
}

/// **The `pk` bit, with its reason** — the outcome of checking every exhibited block's
/// Pickles Wrap proof.
///
/// ⚑ This is a two-valued type ON PURPOSE, and the reason is the thing it replaced.
/// `NEUTRAL_PICKLES_OK` was a `const … = true`: the gate's Pickles conjunct could not
/// go false, so the conjunct did no work and a Lean theorem about it
/// (`mina_decision_discriminates`, which pins `pk = false ⇒ reject`) described a
/// branch the deployed path could not reach. [`Self::bit`] can now genuinely be
/// `false`, the finality gate sees that `false` and does the rejecting, and Rust only
/// names which block afterwards.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PicklesOutcome {
    /// Every exhibited block's proof decoded and the VERIFIED preamble gate accepted
    /// its shape. `pk = true`.
    AllAccepted,
    /// The VERIFIED preamble gate REFUSED a block's shape. `pk = false` — which is
    /// what gets handed to the finality gate, so the refusal is rendered there.
    Refused {
        /// The height of the refused block.
        block_height: u64,
        /// Its exhibited recursion count.
        prev_challenges: usize,
        /// Its exhibited IPA round count.
        ipa_rounds: usize,
    },
}

impl PicklesOutcome {
    /// The `pk` projection the Lean gate's Pickles conjunct is fed.
    pub fn bit(&self) -> bool {
        matches!(self, Self::AllAccepted)
    }
}

/// The exhibited segment, after the Rust-side checks have run. Holding one is
/// evidence that every state hash decoded and is canonical, that the blocks are
/// parent-linked and height-contiguous, and that the oldest descends from the
/// pinned anchor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedSegment {
    /// The tip's state hash.
    pub tip_state_hash: MinaStateHash,
    /// The number of exhibited blocks above the anchor.
    pub len: u64,
    /// The tip height, witnessed as `anchor_height + len`.
    pub tip_height: u64,
}

/// The live off-chain Mina observer over a [`MinaRpc`] connection.
pub struct MinaObserver<R: MinaRpc> {
    /// The observer configuration (zkApp, pinned anchor, finality depth).
    pub config: MinaObserverConfig,
    /// The chain connection.
    pub rpc: R,
}

impl<R: MinaRpc> MinaObserver<R> {
    /// Build an observer for `config` over `rpc`.
    pub fn new(config: MinaObserverConfig, rpc: R) -> Self {
        Self { config, rpc }
    }

    /// **Check the exhibited `bestChain` segment**: every state hash decodes and is
    /// canonical, the oldest block descends from the pinned anchor, and the blocks
    /// are parent-linked with contiguous heights.
    ///
    /// This is the Rust half of the boundary — codec + comparison, no decision. Its
    /// RESULTS (`lk`, `cn`) cross into the Lean gate; the accept/reject is rendered
    /// there.
    ///
    /// ⚑ TRUSTED, named: that a block's `stateHash` is genuinely the Poseidon hash
    /// of its protocol state. That is what makes comparing decoded state hashes a
    /// linkage check at all, and it is not verified here — the Lean side models it
    /// as `LightClientMinaHashFold.stateChain`, whose in-circuit composition is that
    /// file's RESIDUAL #1.
    pub fn check_segment(&self, chain: &[MinaBlock]) -> Result<CheckedSegment, ObserveError> {
        if chain.is_empty() {
            return Err(ObserveError::EmptyChain);
        }
        let anchor = decode_state_hash(&self.config.anchor_state_hash)?;

        // The segment is everything strictly above the anchor. `bestChain` returns
        // oldest-first; drop any block at or below the anchor height (including the
        // anchor block itself, which a window spanning it will contain).
        let segment: Vec<&MinaBlock> = chain
            .iter()
            .filter(|b| b.block_height > self.config.anchor_height)
            .collect();
        if segment.is_empty() {
            return Err(ObserveError::EmptyChain);
        }

        let mut prev_hash = anchor;
        let mut prev_height = self.config.anchor_height;
        let mut tip = anchor;
        for (i, b) in segment.iter().enumerate() {
            let parent = decode_state_hash(&b.parent_state_hash)?;
            let own = decode_state_hash(&b.state_hash)?;
            if parent != prev_hash {
                if i == 0 {
                    return Err(ObserveError::NotAnchored {
                        anchor: self.config.anchor_state_hash.clone(),
                        oldest_parent: b.parent_state_hash.clone(),
                    });
                }
                return Err(ObserveError::ChainNotLinked {
                    at_index: i,
                    reason: format!(
                        "previousStateHash {} is not the preceding block's state hash",
                        b.parent_state_hash
                    ),
                });
            }
            if b.block_height != prev_height + 1 {
                return Err(ObserveError::ChainNotLinked {
                    at_index: i,
                    reason: format!(
                        "blockHeight {} is not one past {prev_height}",
                        b.block_height
                    ),
                });
            }
            prev_hash = own;
            prev_height = b.block_height;
            tip = own;
        }

        let len = segment.len() as u64;
        Ok(CheckedSegment {
            tip_state_hash: tip,
            len,
            tip_height: self.config.anchor_height + len,
        })
    }

    /// **Check every exhibited block's Pickles Wrap proof**, and return the `pk` bit
    /// the verified light-client gate's Pickles conjunct is fed.
    ///
    /// Two stages, and the split is the substrate boundary:
    ///
    /// 1. **Rust decodes** (`crate::mina_pickles`) — a CODEC. Base64url, then a total,
    ///    exact-fit binprot walk of `Mina_base.Proof.Stable.V2` with canonical integer
    ///    widths and canonical field elements. No field arithmetic and no group
    ///    arithmetic: `y² = x³ + 5`, the sponge and the IPA relation are Lean-authored
    ///    and stay there. Any deviation is a REFUSAL and it happens BEFORE the gate, so
    ///    it has teeth even with no archive.
    /// 2. **Lean decides** (`dregg_mina_wrap_shape_ok`) — the decoded counts against the
    ///    pinned verifier index, which `picklesWrapShapeOk_is_shapeOkRec` proves is
    ///    `KimchiVerify.shapeOkRec`, the check `verifier.rs:810-830` runs. An absent
    ///    export is [`ObserveError::VerifiedGateUnavailable`], never a `true`.
    ///
    /// A gate REJECT is **not** an `Err` here: it is [`PicklesOutcome::Refused`], whose
    /// `false` bit goes to the finality gate so the Pickles conjunct does the
    /// rejecting. An `Err` means the check could not be performed at all — no proof,
    /// undecodable bytes, or no archive.
    ///
    /// ⚑ What this does NOT do is verify the proofs. See the module table: the
    /// arithmetic is fixture-bound, and a Wrap proof does not bind to its own block.
    pub fn check_block_proofs(&self, chain: &[MinaBlock]) -> Result<PicklesOutcome, ObserveError> {
        let idx = self.config.wrap_index;
        for b in chain
            .iter()
            .filter(|b| b.block_height > self.config.anchor_height)
        {
            if b.protocol_state_proof.is_empty() {
                return Err(ObserveError::WrapProofAbsent {
                    block_height: b.block_height,
                });
            }
            let shape = decode_protocol_state_proof(&b.protocol_state_proof)
                .map_err(|e| ObserveError::malformed_proof(b.block_height, &e))?;
            let verdict = dregg_lean_ffi::verified_mina_wrap_shape_ok(
                idx.prev_challenges,
                shape.prev_challenges,
                shape.prev_challenge_vectors,
                idx.public_len,
                shape.w_comm,
                shape.s_evals,
                shape.coefficients,
                shape.t_comm,
                idx.chunk_size,
                idx.ipa_rounds,
                shape.ipa_rounds,
            )
            .map_err(|why| ObserveError::VerifiedGateUnavailable { why })?;
            if verdict != dregg_lean_ffi::MinaWrapShapeVerdict::Accept {
                return Ok(PicklesOutcome::Refused {
                    block_height: b.block_height,
                    prev_challenges: shape.prev_challenges,
                    ipa_rounds: shape.ipa_rounds,
                });
            }
        }
        Ok(PicklesOutcome::AllAccepted)
    }

    /// **Confirm an outbound settlement landed on a finalized Mina block.**
    ///
    /// `expected_root` is the dregg root the settlement advanced to;
    /// `submitted_height` is the Mina height the settlement was submitted at
    /// (`StateAdvance.submitted_at`).
    ///
    /// The pipeline: pull a `bestChain` window that SPANS the confirmation depth,
    /// CHECK the segment ([`Self::check_segment`]), hand the projections to the
    /// VERIFIED Lean gate, and only then read and compare the zkApp's settled root.
    ///
    /// ⚑ FAIL-CLOSED. If the archive does not export `dregg_mina_lc_verify` this
    /// returns [`ObserveError::VerifiedGateUnavailable`] and confirms nothing. There
    /// is no fallback path.
    pub fn observe_settlement(
        &self,
        expected_root: &[u8; 32],
        submitted_height: u64,
    ) -> Result<ObservedMinaSettlement, ObserveError> {
        // (1a) learn the claimed tip height — used ONLY to size the window, never
        //      as evidence. The old code used exactly this number AS the finality
        //      verdict.
        let tip_probe = self.rpc.best_chain(1)?;
        let claimed_tip = tip_probe
            .last()
            .map(|b| b.block_height)
            .ok_or(ObserveError::EmptyChain)?;

        // (1b) pull a window that SPANS the pinned anchor through that tip, and
        //      CHECK it. A window that cannot reach the anchor is a refusal, not a
        //      shorter check.
        let window =
            self.config
                .window_for(claimed_tip)
                .ok_or(ObserveError::AnchorTooFarBehind {
                    anchor_height: self.config.anchor_height,
                    claimed_tip,
                    max_span: MAX_SEGMENT_BLOCKS,
                })?;
        let chain = self.rpc.best_chain(window)?;
        let seg = self.check_segment(&chain)?;

        // (1c) CHECK every exhibited block's Pickles Wrap proof. This is what the
        //      retired `NEUTRAL_PICKLES_OK` constant used to stand in for. A block
        //      without a proof, with an undecodable one, or with a shape the pinned
        //      verifier index does not admit is refused here — before the finality
        //      gate, so the refusal is precise and does not need the archive.
        let pickles = self.check_block_proofs(&chain)?;

        // (2) hand the projections to the VERIFIED gate. `lk`, `pk` and `cn` are all
        //     RESULTS of the checks above — `lk` and `cn` are `true` because
        //     `check_segment` refused otherwise, and `pk` is the two-valued bit
        //     `check_block_proofs` computed from real proof bytes through a verified
        //     decision. A refused proof reaches the gate as `pk = false` and the
        //     gate's Pickles conjunct does the rejecting (Lean:
        //     `mina_decision_discriminates`); Rust only names which block afterwards.
        let witnessed_depth = seg.tip_height.saturating_sub(submitted_height);
        let verdict = dregg_lean_ffi::verified_mina_lc_verify(
            seg.len,
            self.config.anchor_height,
            submitted_height,
            witnessed_depth,
            self.config.confirmation_depth,
            true,
            pickles.bit(),
            true,
        )
        .map_err(|why| ObserveError::VerifiedGateUnavailable { why })?;

        if verdict != dregg_lean_ffi::MinaLcVerdict::Accept {
            if let PicklesOutcome::Refused {
                block_height,
                prev_challenges,
                ipa_rounds,
            } = pickles
            {
                return Err(ObserveError::WrapProofShapeRefused {
                    block_height,
                    prev_challenges,
                    ipa_rounds,
                });
            }
            return Err(ObserveError::NotFinalized {
                tip_height: seg.tip_height,
                submitted_height,
                required_depth: self.config.confirmation_depth,
                segment_len: seg.len,
            });
        }

        // (3) read the zkApp's settled root from its app-state Fields.
        let account = self
            .rpc
            .zkapp_account(&self.config.zkapp_address)?
            .ok_or(ObserveError::ZkappNotFound)?;
        if account.app_state.len() < 2 {
            return Err(ObserveError::MalformedZkappState {
                reason: format!(
                    "expected ≥ 2 app-state Fields (root low/high), got {}",
                    account.app_state.len()
                ),
            });
        }
        let on_chain = decode_root_from_fields(&account.app_state[0], &account.app_state[1])?;

        // (4) confirm it equals the dregg root we settled — a forged/wrong state
        //     is refused.
        if &on_chain != expected_root {
            return Err(ObserveError::RootMismatch {
                on_chain,
                expected: *expected_root,
            });
        }

        Ok(ObservedMinaSettlement {
            proven_root: on_chain,
            tip_state_hash: seg.tip_state_hash,
            tip_height: seg.tip_height,
            submitted_height,
            segment_len: seg.len,
            depth: witnessed_depth,
        })
    }
}

// ===========================================================================
// In-memory test double (the dev observer harness + tests)
// ===========================================================================

/// An in-memory [`MinaRpc`] for tests and the dev observer harness. It models a
/// GENUINE canonical chain — real Base58Check state hashes, parent-linked, with
/// contiguous heights — so the observer's segment checks are exercised rather than
/// bypassed, plus a zkApp account.
///
/// ⚑ AND IT SERVES A REAL PICKLES PROOF. Every block it hands out carries the actual
/// `protocolStateProof` of Mina devnet block 539508 (the object o1-labs' own
/// `kimchi::verifier::verify` accepts, pinned in
/// `metatheory/fixtures/pickles-extractors/mina_devnet_block.json`). A placeholder
/// string would make [`MinaObserver::check_block_proofs`] refuse everything and the
/// tests would then be asserting the wrong thing — the same mistake the pre-2026-07-29
/// mock made with `"B62hash7"` state hashes, which made every hash check vacuous.
#[cfg(any(test, feature = "test-utils"))]
#[derive(Clone, Debug, Default)]
pub struct MockMinaRpc {
    chain: Vec<MinaBlock>,
    /// Served for any block whose own `protocol_state_proof` is empty. Stored once,
    /// not per block: a 4096-block window would otherwise materialise ~45 MB of
    /// identical strings.
    proof: String,
    accounts: std::collections::BTreeMap<String, MinaZkappAccount>,
}

/// The REAL devnet block 539508 `protocolStateProof`, from the tracked extractor
/// fixture. Shared by the mock and by the observer tests, so a drift in what a Mina
/// proof IS shows up as a red test rather than as two decoders quietly disagreeing.
#[cfg(any(test, feature = "test-utils"))]
pub fn real_devnet_protocol_state_proof() -> String {
    const FIXTURE: &str =
        include_str!("../../metatheory/fixtures/pickles-extractors/mina_devnet_block.json");
    let v: serde_json::Value = serde_json::from_str(FIXTURE).expect("devnet block fixture JSON");
    v.get("protocol_state_proof_base64_urlsafe")
        .and_then(|x| x.as_str())
        .expect("the fixture carries the base64url protocolStateProof")
        .to_string()
}

/// Encode a 32-byte little-endian field element as a Mina Base58Check state hash.
/// The inverse of [`decode_state_hash`]; used by the test double to mint a chain
/// of GENUINE state hashes (a mock that emitted `"B62hash7"` would make every
/// check below vacuous).
#[cfg(any(test, feature = "test-utils"))]
pub fn encode_state_hash(fe_le: &[u8; 32]) -> String {
    use sha2::{Digest, Sha256};
    let mut body = Vec::with_capacity(34);
    body.push(STATE_HASH_VERSION_BYTE);
    body.push(BINPROT_VERSION_BYTE);
    body.extend_from_slice(fe_le);
    let calc = Sha256::digest(Sha256::digest(&body));
    let mut raw = body;
    raw.extend_from_slice(&calc[..4]);

    // Base58 encode.
    let leading_zeros = raw.iter().take_while(|&&b| b == 0).count();
    let mut digits: Vec<u8> = vec![0];
    for &byte in &raw {
        let mut carry = u32::from(byte);
        for d in digits.iter_mut() {
            let cur = u32::from(*d) * 256 + carry;
            *d = (cur % 58) as u8;
            carry = cur / 58;
        }
        while carry > 0 {
            digits.push((carry % 58) as u8);
            carry /= 58;
        }
    }
    let mut out = String::new();
    for _ in 0..leading_zeros {
        out.push('1');
    }
    for &d in digits.iter().rev() {
        out.push(B58[d as usize] as char);
    }
    // Strip the synthetic leading zero digit if the value did not need it.
    if out.len() > 1 && raw[0] != 0 {
        if let Some(stripped) = out.strip_prefix('1') {
            if !stripped.is_empty() {
                out = stripped.to_string();
            }
        }
    }
    out
}

/// A deterministic CANONICAL field element for block `n` (top two bits clear, so
/// `decode_state_hash`'s canonicality check admits it).
#[cfg(any(test, feature = "test-utils"))]
pub fn mock_fe(n: u64) -> [u8; 32] {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&n.to_le_bytes());
    fe[31] = 0x01; // well under 0x40 ⇒ < 2^254
    fe
}

#[cfg(any(test, feature = "test-utils"))]
impl MockMinaRpc {
    /// A mock whose canonical chain runs `anchor_height ..= tip_height`, genuinely
    /// parent-linked with real Base58Check state hashes. The block at
    /// `anchor_height` is the anchor.
    pub fn linked_chain(anchor_height: u64, tip_height: u64) -> Self {
        let chain = (anchor_height..=tip_height)
            .map(|h| MinaBlock {
                state_hash: encode_state_hash(&mock_fe(h)),
                block_height: h,
                parent_state_hash: encode_state_hash(&mock_fe(h.saturating_sub(1))),
                // Filled from `self.proof` on the way out — see the struct docs.
                protocol_state_proof: String::new(),
            })
            .collect();
        Self {
            chain,
            proof: real_devnet_protocol_state_proof(),
            accounts: std::collections::BTreeMap::new(),
        }
    }

    /// Replace the proof every block is served with — the falsifier hook. A tampered
    /// or empty string here is what an endpoint serving a bad proof looks like.
    pub fn set_served_proof(&mut self, proof: impl Into<String>) -> &mut Self {
        self.proof = proof.into();
        self
    }

    /// The anchor state hash for a chain minted by [`Self::linked_chain`].
    pub fn anchor_hash(anchor_height: u64) -> String {
        encode_state_hash(&mock_fe(anchor_height))
    }

    /// Replace the chain wholesale (for the not-a-chain / not-anchored tests).
    pub fn set_chain(&mut self, chain: Vec<MinaBlock>) -> &mut Self {
        self.chain = chain;
        self
    }

    /// Set the zkApp's settled root (encoded across the two app-state Fields).
    pub fn set_zkapp_root(&mut self, public_key: &str, root: &[u8; 32]) -> &mut Self {
        let [low, high] = encode_root_to_fields(root);
        // Pad to 8 app-state Fields like a real zkApp account.
        let mut app_state = vec![low, high];
        app_state.resize(8, "0".to_string());
        self.accounts
            .insert(public_key.to_string(), MinaZkappAccount { app_state });
        self
    }

    /// Set a raw zkApp account (for malformed-state tests).
    pub fn set_zkapp_account(&mut self, public_key: &str, account: MinaZkappAccount) -> &mut Self {
        self.accounts.insert(public_key.to_string(), account);
        self
    }
}

#[cfg(any(test, feature = "test-utils"))]
impl MinaRpc for MockMinaRpc {
    fn best_chain(&self, max_length: u32) -> Result<Vec<MinaBlock>, RpcError> {
        let n = (max_length as usize).min(self.chain.len());
        Ok(self.chain[self.chain.len() - n..]
            .iter()
            .map(|b| {
                if b.protocol_state_proof.is_empty() {
                    MinaBlock {
                        protocol_state_proof: self.proof.clone(),
                        ..b.clone()
                    }
                } else {
                    b.clone()
                }
            })
            .collect())
    }

    fn zkapp_account(&self, public_key: &str) -> Result<Option<MinaZkappAccount>, RpcError> {
        Ok(self.accounts.get(public_key).cloned())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ZKAPP: &str = "B62qrPN5Y5yq8kGE3FbVKbGTdTAJNdtNtS5vH1e3jX5uFtkKXb7x3zX";

    /// The two REAL Mina devnet state hashes `MinaRealBlockGate` names, and the
    /// `Fp` decimals `LightClientMinaHashFold` pins for them.
    const DEVNET_539508_B58: &str = "3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk";
    const DEVNET_539508_FE: &str =
        "26183698926150821166089117776323498226609958862529648923082869093695686732004";
    const DEVNET_GENESIS_B58: &str = "3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx";
    const DEVNET_GENESIS_FE: &str =
        "9114416221768123787477325283664893678899335531281108607736543138013422200977";

    fn config(anchor_height: u64, depth: u64) -> MinaObserverConfig {
        MinaObserverConfig {
            zkapp_address: ZKAPP.to_string(),
            anchor_state_hash: MockMinaRpc::anchor_hash(anchor_height),
            anchor_height,
            confirmation_depth: depth,
            wrap_index: MinaWrapIndexParams::DEVNET_BLOCKCHAIN,
        }
    }

    fn root(n: u8) -> [u8; 32] {
        let mut r = [n; 32];
        // Make the two halves distinct so the high/low split is genuinely tested.
        r[0] = n.wrapping_add(1);
        r[31] = n.wrapping_add(2);
        r
    }

    // ---- the state-hash codec, against REAL chain data ----------------------

    /// ⚑ THE CROSS-CHECK. The Rust decoder must reproduce, on two REAL devnet
    /// state hashes, exactly the `Fp` decimals
    /// `Dregg2.Circuit.Emit.LightClientMinaHashFold` pins
    /// (`DEVNET_539508_STATE_HASH`, `DEVNET_GENESIS_STATE_HASH`). Neither side
    /// derives the other, so a drift in either is a red test rather than a silent
    /// disagreement about what a Mina state hash IS.
    #[test]
    fn real_devnet_state_hashes_decode_to_the_lean_pinned_field_elements() {
        let b = decode_state_hash(DEVNET_539508_B58).expect("real devnet block decodes");
        assert_eq!(
            b.to_decimal(),
            DEVNET_539508_FE,
            "block 539508's state hash must decode to the Fp element Lean pins"
        );
        let g = decode_state_hash(DEVNET_GENESIS_B58).expect("real devnet genesis decodes");
        assert_eq!(g.to_decimal(), DEVNET_GENESIS_FE);
        // And both are canonical — the Lean side proves the same
        // (`devnet_state_hashes_in_range`), so the width gate is LIVE on real data.
        assert!(b.is_canonical() && g.is_canonical());
    }

    #[test]
    fn state_hash_decoder_refuses_garbage() {
        // A tampered Base58Check (one character changed) fails the checksum.
        let mut bad: Vec<char> = DEVNET_539508_B58.chars().collect();
        bad[10] = if bad[10] == 'a' { 'b' } else { 'a' };
        let bad: String = bad.into_iter().collect();
        assert!(matches!(
            decode_state_hash(&bad),
            Err(ObserveError::MalformedStateHash { .. })
        ));
        // The old mock's placeholder is not a state hash at all.
        assert!(matches!(
            decode_state_hash("B62hash7"),
            Err(ObserveError::MalformedStateHash { .. })
        ));
        // Neither is an empty string.
        assert!(matches!(
            decode_state_hash(""),
            Err(ObserveError::MalformedStateHash { .. })
        ));
    }

    #[test]
    fn state_hash_decoder_refuses_non_canonical_field_element() {
        // Top two bits set ⇒ >= 2^254 ⇒ refused. This is the `+p` alias family the
        // Lean width gate (`minaRowWidthGates`) refuses, at the codec boundary.
        let mut fe = [0u8; 32];
        fe[31] = 0xff;
        let encoded = encode_state_hash(&fe);
        let err = decode_state_hash(&encoded).unwrap_err();
        match err {
            ObserveError::MalformedStateHash { reason, .. } => {
                assert!(reason.contains("NON-CANONICAL"), "got: {reason}");
            }
            other => panic!("expected a canonicality refusal, got {other:?}"),
        }
    }

    #[test]
    fn state_hash_codec_round_trips() {
        for n in [0u64, 1, 42, 539_508, u64::MAX] {
            let fe = mock_fe(n);
            let s = encode_state_hash(&fe);
            let d = decode_state_hash(&s).expect("round trip");
            assert_eq!(d.to_le_bytes(), fe, "n={n}");
        }
    }

    #[test]
    fn root_field_encoding_round_trips() {
        let r = root(0x5A);
        let [low, high] = encode_root_to_fields(&r);
        let decoded = decode_root_from_fields(&low, &high).expect("decode");
        assert_eq!(decoded, r, "root survives the app-state Field split");
    }

    // ---- the segment check (Rust half of the boundary) ----------------------

    #[test]
    fn segment_check_accepts_a_genuine_linked_chain() {
        let rpc = MockMinaRpc::linked_chain(700, 1000);
        let observer = MinaObserver::new(config(700, 290), rpc);
        let chain = observer.rpc.best_chain(400).unwrap();
        let seg = observer
            .check_segment(&chain)
            .expect("genuine chain checks");
        assert_eq!(seg.len, 300, "300 blocks above the anchor at 700");
        assert_eq!(seg.tip_height, 1000);
        assert_eq!(seg.tip_state_hash.to_le_bytes(), mock_fe(1000));
    }

    /// ⚑ THE DEFECT THAT WAS SHIPPED. One fabricated block claiming a huge height
    /// used to finalize every settlement, because the code took `max(block_height)`
    /// and subtracted. It is now refused at the segment check: the block does not
    /// descend from the pinned anchor.
    #[test]
    fn segment_check_refuses_one_fabricated_high_block() {
        let mut rpc = MockMinaRpc::linked_chain(700, 1000);
        rpc.set_chain(vec![MinaBlock {
            state_hash: encode_state_hash(&mock_fe(999_999_999)),
            block_height: 999_999_999,
            parent_state_hash: encode_state_hash(&mock_fe(999_999_998)),
            protocol_state_proof: String::new(),
        }]);
        let observer = MinaObserver::new(config(700, 290), rpc);
        let chain = observer.rpc.best_chain(400).unwrap();
        assert!(matches!(
            observer.check_segment(&chain).unwrap_err(),
            ObserveError::NotAnchored { .. }
        ));
    }

    #[test]
    fn segment_check_refuses_a_broken_parent_link() {
        let mut rpc = MockMinaRpc::linked_chain(700, 705);
        let mut chain = rpc.best_chain(64).unwrap();
        // Re-point block 703's parent at an unrelated (but well-formed) hash.
        chain[3].parent_state_hash = encode_state_hash(&mock_fe(9_999));
        rpc.set_chain(chain.clone());
        let observer = MinaObserver::new(config(700, 1), rpc);
        assert!(matches!(
            observer.check_segment(&chain).unwrap_err(),
            ObserveError::ChainNotLinked { .. }
        ));
    }

    #[test]
    fn segment_check_refuses_a_height_gap() {
        let rpc = MockMinaRpc::linked_chain(700, 705);
        let mut chain = rpc.best_chain(64).unwrap();
        // Keep the linkage but skip a height.
        chain[3].block_height = 777;
        let observer = MinaObserver::new(config(700, 1), rpc);
        assert!(matches!(
            observer.check_segment(&chain).unwrap_err(),
            ObserveError::ChainNotLinked { .. }
        ));
    }

    #[test]
    fn segment_check_refuses_a_malformed_state_hash() {
        let rpc = MockMinaRpc::linked_chain(700, 705);
        let mut chain = rpc.best_chain(64).unwrap();
        chain[2].state_hash = "B62hash702".to_string();
        let observer = MinaObserver::new(config(700, 1), rpc);
        assert!(matches!(
            observer.check_segment(&chain).unwrap_err(),
            ObserveError::MalformedStateHash { .. }
        ));
    }

    /// The window is DERIVED from the pinned anchor and the claimed tip, so it
    /// always spans the evidence. The shipped code had a fixed
    /// `best_chain_length: 16` against a depth of 290 — 274 blocks too short to
    /// contain what the depth claim was about.
    #[test]
    fn best_chain_window_spans_the_anchor() {
        assert_eq!(config(700, 290).window_for(1000), Some(301));
        assert_eq!(config(700, 290).window_for(700), Some(1));
        // A tip BELOW the anchor is not a window at all.
        assert_eq!(config(700, 290).window_for(699), None);
        // And an anchor too far behind is refused rather than silently truncated.
        assert_eq!(config(0, 290).window_for(MAX_SEGMENT_BLOCKS + 1), None);
    }

    /// An anchor further behind than [`MAX_SEGMENT_BLOCKS`] is a REFUSAL naming the
    /// remedy (advance the pin), not a shorter check.
    #[test]
    fn observer_refuses_when_the_anchor_is_too_far_behind() {
        let settled = root(0x77);
        let mut rpc = MockMinaRpc::linked_chain(0, MAX_SEGMENT_BLOCKS + 10);
        rpc.set_zkapp_root(ZKAPP, &settled);
        let observer = MinaObserver::new(config(0, 5), rpc);
        assert!(matches!(
            observer.observe_settlement(&settled, 10).unwrap_err(),
            ObserveError::AnchorTooFarBehind { .. }
        ));
    }

    // ---- the verified gate: fail-closed --------------------------------------

    /// ⚑ THE FAIL-CLOSED PIN. With the gate absent from the linked archive, a genuine,
    /// fully-checked, deep-enough settlement is REFUSED with
    /// `VerifiedGateUnavailable`. When the export lands this flips to an accept and
    /// the other half of the assertion runs. Either way there is no third outcome:
    /// the observer never confirms without the gate.
    #[test]
    fn observer_fails_closed_without_the_verified_gate() {
        let settled = root(0x11);
        let mut rpc = MockMinaRpc::linked_chain(700, 1000);
        rpc.set_zkapp_root(ZKAPP, &settled);
        let observer = MinaObserver::new(config(700, 290), rpc);
        let outcome = observer.observe_settlement(&settled, 700);

        // ⚑ THE BRANCH IS ARMED, not merely chosen. Both arms below are green on their own
        // terms, which means a passing run proves nothing about WHICH ran — the shape a
        // "documented but not detected" wound wears. `demand_lean` PANICS under
        // `DREGG_TEST_REQUIRE_LEAN=1`, so under that env a green run is a green ACCEPT.
        if dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::mina_lc_verify_available(),
            "dregg_mina_lc_verify Mina anchored-segment gate (this test's ACCEPT half)",
        ) {
            let observed = outcome.expect("gate present ⇒ genuine settlement confirmed");
            assert_eq!(observed.proven_root, settled);
            assert_eq!(observed.tip_height, 1000);
            assert_eq!(observed.segment_len, 300);
            assert_eq!(observed.depth, 300);
        } else {
            assert!(
                matches!(outcome, Err(ObserveError::VerifiedGateUnavailable { .. })),
                "an absent verified gate MUST refuse, never skip the check; got {outcome:?}"
            );
        }
    }

    /// Un-finalized settlements are refused whether or not the gate is present:
    /// without it, by the gate-unavailable refusal; with it, by the gate.
    #[test]
    fn observer_refuses_unfinalized_settlement() {
        let settled = root(0x22);
        let mut rpc = MockMinaRpc::linked_chain(700, 1000);
        rpc.set_zkapp_root(ZKAPP, &settled);
        let observer = MinaObserver::new(config(700, 290), rpc);
        // Submitted at 900, witnessed tip 1000 ⇒ depth 100 < 290.
        let err = observer.observe_settlement(&settled, 900).unwrap_err();
        assert!(matches!(
            err,
            ObserveError::NotFinalized { .. } | ObserveError::VerifiedGateUnavailable { .. }
        ));
    }

    /// ⚑ The shipped observer's unbounded-depth shape: a settlement claimed BELOW
    /// the pinned anchor. `tip - submitted` is large, but the depth is not backed
    /// by exhibited evidence. Refused (by the gate's `ah <= sh` conjunct, or by the
    /// gate being unavailable).
    #[test]
    fn observer_refuses_settlement_claimed_below_the_anchor() {
        let settled = root(0x66);
        let mut rpc = MockMinaRpc::linked_chain(700, 701);
        rpc.set_zkapp_root(ZKAPP, &settled);
        let observer = MinaObserver::new(config(700, 290), rpc);
        let err = observer.observe_settlement(&settled, 0).unwrap_err();
        assert!(matches!(
            err,
            ObserveError::NotFinalized { .. } | ObserveError::VerifiedGateUnavailable { .. }
        ));
    }

    /// The segment checks run BEFORE the gate, so a not-a-chain answer is refused
    /// with its own precise error even when the archive is absent — this test is
    /// meaningful today.
    /// ⚑ THE SHIPPED DEFECT, end-to-end: a single well-formed block whose height
    /// clears the depth used to finalize every settlement. It is now refused BEFORE
    /// the gate, with a precise reason — so this test is meaningful today, with no
    /// archive.
    #[test]
    fn observer_refuses_an_unlinked_chain_before_reaching_the_gate() {
        let settled = root(0x33);
        let mut rpc = MockMinaRpc::linked_chain(700, 1000);
        rpc.set_zkapp_root(ZKAPP, &settled);
        // One block at a plausible tip height, not descending from the anchor.
        rpc.set_chain(vec![MinaBlock {
            state_hash: encode_state_hash(&mock_fe(1000)),
            block_height: 1000,
            parent_state_hash: encode_state_hash(&mock_fe(999)),
            protocol_state_proof: String::new(),
        }]);
        let observer = MinaObserver::new(config(700, 290), rpc);
        assert!(matches!(
            observer.observe_settlement(&settled, 700).unwrap_err(),
            ObserveError::NotAnchored { .. }
        ));
    }

    /// And the wilder version — a block claiming height 999,999,999 — is refused
    /// even earlier, at the window sizing: the pinned anchor cannot be spanned.
    #[test]
    fn observer_refuses_a_wildly_fabricated_tip_height() {
        let settled = root(0x88);
        let mut rpc = MockMinaRpc::linked_chain(700, 1000);
        rpc.set_zkapp_root(ZKAPP, &settled);
        rpc.set_chain(vec![MinaBlock {
            state_hash: encode_state_hash(&mock_fe(999_999_999)),
            block_height: 999_999_999,
            parent_state_hash: encode_state_hash(&mock_fe(999_999_998)),
            protocol_state_proof: String::new(),
        }]);
        let observer = MinaObserver::new(config(700, 290), rpc);
        assert!(matches!(
            observer.observe_settlement(&settled, 700).unwrap_err(),
            ObserveError::AnchorTooFarBehind { .. }
        ));
    }

    // ---- the per-block Pickles proof (what retired NEUTRAL_PICKLES_OK) -------
    //
    // ⚑ These four are the FALSIFIER, and they are meaningful TODAY, with no archive:
    // the decode runs BEFORE the verified gate, exactly as `check_segment` does, so a
    // bad proof is refused with its own precise error while a good proof gets as far
    // as the gate. That contrast is the whole point — a check that refuses everything
    // discriminates nothing.

    /// ⚑ A block whose `protocolStateProof` is absent is REFUSED. This is the shape a
    /// neutral filler hides: before 2026-07-29 the observer never asked for the proof,
    /// so "no proof" and "a good proof" were the same input.
    #[test]
    fn observer_refuses_a_block_with_no_pickles_proof() {
        let settled = root(0x91);
        let mut rpc = MockMinaRpc::linked_chain(700, 1000);
        rpc.set_zkapp_root(ZKAPP, &settled);
        rpc.set_served_proof("");
        let observer = MinaObserver::new(config(700, 290), rpc);
        match observer.observe_settlement(&settled, 700).unwrap_err() {
            ObserveError::WrapProofAbsent { block_height } => {
                assert_eq!(block_height, 701, "the first block above the anchor");
            }
            other => panic!("an absent Pickles proof must be refused, got {other:?}"),
        }
    }

    /// ⚑ A TAMPERED proof is refused, on real bytes: the real devnet proof with its
    /// last byte removed no longer decodes as a `Mina_base.Proof.Stable.V2`.
    #[test]
    fn observer_refuses_a_truncated_pickles_proof() {
        use base64::Engine as _;
        let real = real_devnet_protocol_state_proof();
        let mut raw = base64::engine::general_purpose::URL_SAFE_NO_PAD
            .decode(real.trim_end_matches('='))
            .unwrap();
        raw.pop();
        let truncated = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(&raw);

        let settled = root(0x92);
        let mut rpc = MockMinaRpc::linked_chain(700, 1000);
        rpc.set_zkapp_root(ZKAPP, &settled);
        rpc.set_served_proof(truncated);
        let observer = MinaObserver::new(config(700, 290), rpc);
        match observer.observe_settlement(&settled, 700).unwrap_err() {
            ObserveError::MalformedWrapProof { block_height, .. } => {
                assert_eq!(block_height, 701);
            }
            other => panic!("a truncated Pickles proof must be refused, got {other:?}"),
        }
    }

    /// And a proof whose bytes are fine but whose SHAPE is not: a coordinate pushed
    /// out of its Pasta field is the `x + p` alias family at a group element, and the
    /// decoder refuses it rather than admitting two encodings of one proof.
    #[test]
    fn observer_refuses_a_non_canonical_coordinate() {
        use base64::Engine as _;
        let real = real_devnet_protocol_state_proof();
        let mut raw = base64::engine::general_purpose::URL_SAFE_NO_PAD
            .decode(real.trim_end_matches('='))
            .unwrap();
        raw[460] = 0xff; // the top byte of the statement's first group coordinate
        let bad = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(&raw);

        let settled = root(0x93);
        let mut rpc = MockMinaRpc::linked_chain(700, 1000);
        rpc.set_zkapp_root(ZKAPP, &settled);
        rpc.set_served_proof(bad);
        let observer = MinaObserver::new(config(700, 290), rpc);
        let err = observer.observe_settlement(&settled, 700).unwrap_err();
        match err {
            ObserveError::MalformedWrapProof { ref reason, .. } => {
                assert!(reason.contains("NON-CANONICAL"), "got {err}");
            }
            other => panic!("a non-canonical coordinate must be refused, got {other:?}"),
        }
    }

    /// ⚑ THE DISCRIMINATION, and the half that makes the three above mean something: a
    /// REAL Mina devnet block's Pickles proof — the object o1-labs' own
    /// `kimchi::verifier::verify` accepts — passes the Rust decode and reaches the
    /// verified gate. With the archive absent that shows up as
    /// `VerifiedGateUnavailable` (the gate was ASKED); with it present, as an accept.
    /// Either way it is NOT one of the proof refusals above, which is exactly the
    /// property "refuses everything" would fail.
    #[test]
    fn real_devnet_pickles_proof_reaches_the_verified_gate() {
        // Same arming as the fail-closed pin: under `DREGG_TEST_REQUIRE_LEAN=1` an absent gate
        // PANICS here rather than letting the `VerifiedGateUnavailable` arm below carry the test
        // to green without any verdict having been rendered.
        let _ = dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::mina_wrap_shape_ok_available(),
            "dregg_mina_wrap_shape_ok Pickles Wrap-preamble gate (the observer's per-block accept)",
        );
        let rpc = MockMinaRpc::linked_chain(700, 703);
        let observer = MinaObserver::new(config(700, 1), rpc);
        let chain = observer.rpc.best_chain(16).unwrap();
        assert!(
            chain.iter().all(|b| !b.protocol_state_proof.is_empty()),
            "the mock must serve a real proof or this test is vacuous"
        );
        // The Rust decode half is unconditional and passes on the real object.
        let shape =
            crate::mina_pickles::decode_protocol_state_proof(&chain[0].protocol_state_proof)
                .expect("the real devnet proof decodes inside the observer path");
        assert_eq!(shape.prev_challenges, 2);
        assert_eq!(shape.ipa_rounds, 15);

        match observer.check_block_proofs(&chain) {
            Ok(PicklesOutcome::AllAccepted) => assert!(
                dregg_lean_ffi::mina_wrap_shape_ok_available(),
                "an accept without the gate would mean the check was skipped"
            ),
            Ok(PicklesOutcome::Refused { .. }) => panic!(
                "the verified gate must ACCEPT a real Mina block's Wrap shape — the same object \
                 `real_block_wrap_shape_accepts` proves it accepts"
            ),
            Err(ObserveError::VerifiedGateUnavailable { .. }) => assert!(
                !dregg_lean_ffi::mina_wrap_shape_ok_available(),
                "the gate is present, so it must have rendered a verdict"
            ),
            other => panic!(
                "a REAL Mina proof must reach the gate, not be refused by the decode: {other:?}"
            ),
        }
    }

    /// The `pk` projection is genuinely TWO-VALUED — the property `NEUTRAL_PICKLES_OK`
    /// could not have. Without it the Lean gate's Pickles conjunct, and the theorem
    /// pinning `pk = false ⇒ reject` (`mina_decision_discriminates`), describe a branch
    /// the deployed path cannot reach.
    #[test]
    fn the_pickles_bit_can_be_false() {
        assert!(PicklesOutcome::AllAccepted.bit());
        assert!(
            !PicklesOutcome::Refused {
                block_height: 701,
                prev_challenges: 1,
                ipa_rounds: 15,
            }
            .bit()
        );
    }

    #[test]
    fn observer_refuses_empty_chain() {
        let settled = root(0x44);
        let mut rpc = MockMinaRpc::linked_chain(700, 1000);
        rpc.set_chain(vec![]);
        let observer = MinaObserver::new(config(700, 290), rpc);
        assert_eq!(
            observer.observe_settlement(&settled, 700).unwrap_err(),
            ObserveError::EmptyChain
        );
    }

    // ---- the GraphQL wire codec (real Mina shapes) --------------------------

    struct CannedTransport {
        response: String,
        seen: std::cell::RefCell<Option<String>>,
    }

    impl JsonRpcTransport for CannedTransport {
        fn post(&self, _url: &str, body: &str) -> Result<String, RpcError> {
            *self.seen.borrow_mut() = Some(body.to_string());
            Ok(self.response.clone())
        }
    }

    #[test]
    fn graphql_parses_real_best_chain_shape() {
        // A genuine Mina bestChain response: stateHash + protocolStateProof (base64url
        // binprot) + nested consensusState blockHeight as a STRING. The proof carried
        // here is the REAL devnet block 539508 one, so the parse is checked against the
        // form a node actually serves rather than a placeholder.
        let proof = real_devnet_protocol_state_proof();
        let resp = format!(
            r#"{{"data":{{"bestChain":[
            {{"stateHash":"{a}","protocolStateProof":"{p}","protocolState":{{"previousStateHash":"{z}","consensusState":{{"blockHeight":"999"}}}}}},
            {{"stateHash":"{b}","protocolStateProof":"{p}","protocolState":{{"previousStateHash":"{a}","consensusState":{{"blockHeight":"1000"}}}}}}
        ]}}}}"#,
            z = encode_state_hash(&mock_fe(998)),
            a = encode_state_hash(&mock_fe(999)),
            b = encode_state_hash(&mock_fe(1000)),
            p = proof,
        );
        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            CannedTransport {
                response: resp,
                seen: std::cell::RefCell::new(None),
            },
        );
        let chain = rpc.best_chain(2).expect("parse real bestChain shape");
        assert_eq!(chain.len(), 2);
        assert_eq!(chain[1].block_height, 1000);
        assert_eq!(chain[1].state_hash, encode_state_hash(&mock_fe(1000)));
        // ⚑ The proof survives the wire and decodes — the parse is not just a string
        // copy, it is the input the per-block check runs on.
        assert_eq!(chain[1].protocol_state_proof, proof);
        assert_eq!(
            crate::mina_pickles::decode_protocol_state_proof(&chain[1].protocol_state_proof)
                .expect("parsed proof decodes")
                .prev_challenges,
            2
        );
        let sent = rpc.transport.seen.borrow().clone().unwrap();
        assert!(sent.contains("bestChain"));
        assert!(sent.contains("blockHeight"));
        // ⚑ THE QUERY ASKS FOR THE PROOF. Retiring `NEUTRAL_PICKLES_OK` starts here:
        // no field in the query, no evidence to check.
        assert!(
            sent.contains("protocolStateProof"),
            "the bestChain query must fetch the blockchain SNARK: {sent}"
        );
    }

    /// A `bestChain` response that omits `protocolStateProof` parses to an EMPTY proof,
    /// which the observer refuses. It does not parse to "fine".
    #[test]
    fn graphql_block_without_a_proof_yields_an_empty_proof_and_is_refused() {
        let resp = format!(
            r#"{{"data":{{"bestChain":[
            {{"stateHash":"{a}","protocolState":{{"previousStateHash":"{z}","consensusState":{{"blockHeight":"999"}}}}}}
        ]}}}}"#,
            z = encode_state_hash(&mock_fe(998)),
            a = encode_state_hash(&mock_fe(999)),
        );
        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            CannedTransport {
                response: resp,
                seen: std::cell::RefCell::new(None),
            },
        );
        let chain = rpc.best_chain(1).unwrap();
        assert_eq!(chain[0].protocol_state_proof, "");
        let observer = MinaObserver::new(config(998, 1), MockMinaRpc::linked_chain(998, 999));
        assert!(matches!(
            observer.check_block_proofs(&chain).unwrap_err(),
            ObserveError::WrapProofAbsent { .. }
        ));
    }

    #[test]
    fn graphql_parses_real_zkapp_account_shape() {
        let settled = root(0x6E);
        let [low, high] = encode_root_to_fields(&settled);
        let resp = format!(
            r#"{{"data":{{"account":{{"zkappState":["{low}","{high}","0","0","0","0","0","0"]}}}}}}"#
        );
        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            CannedTransport {
                response: resp,
                seen: std::cell::RefCell::new(None),
            },
        );
        let acct = rpc
            .zkapp_account(ZKAPP)
            .expect("parse")
            .expect("account present");
        assert_eq!(acct.app_state.len(), 8);
        let decoded = decode_root_from_fields(&acct.app_state[0], &acct.app_state[1]).unwrap();
        assert_eq!(
            decoded, settled,
            "the zkApp root decodes from the real shape"
        );
    }

    #[test]
    fn graphql_null_account_is_none() {
        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            CannedTransport {
                response: r#"{"data":{"account":null}}"#.to_string(),
                seen: std::cell::RefCell::new(None),
            },
        );
        assert!(rpc.zkapp_account(ZKAPP).unwrap().is_none());
    }

    #[test]
    fn graphql_surfaces_errors() {
        let rpc = MinaGraphQlRpc::new(
            "http://unused",
            CannedTransport {
                response: r#"{"errors":[{"message":"bad query"}]}"#.to_string(),
                seen: std::cell::RefCell::new(None),
            },
        );
        let err = rpc.best_chain(2).unwrap_err();
        assert!(matches!(err, RpcError::Rpc { .. }));
    }
}
