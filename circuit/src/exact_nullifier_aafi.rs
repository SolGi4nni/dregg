//! Additive Rust semantic/runtime twin of the Lean exact-nullifier AAFI plan.
//!
//! This module is deliberately **not** a live FNSP-v3 verifier.  It pins the runtime ABI and gives
//! the future Lean-emitted descriptor a hostile-input differential oracle:
//!
//! - a tagged `BOT < REAL(raw256) < TOP` key space, with no reserved raw value;
//! - the exact `FNI2`/`FNN2`/`FNE2`/`FNS3` `hash_many_8` geometry;
//! - a permanent `BOT -> TOP` leaf in physical slot zero;
//! - an authenticated predecessor rewrite followed by an append at the committed free cursor; and
//! - two depth-16, arity-4 paths whose shared middle root makes the update atomic.
//!
//! The remaining production seam is explicit: FNSP-v3 must carry the prior/successor `FNS3`
//! commitments in the rotated state and prove these constraints in the Lean-authored state16 AIR.
//! Accepting [`ValidatedExactAafiTransition`] here is not a substitute for accepting that proof.

use crate::field::BabyBear;
use crate::poseidon2::hash_many_8;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

/// ASCII `FNI2`: exact tagged linked-leaf sponge domain.
pub const EXACT_LINKED_LEAF_DOMAIN: u32 = 0x464e_4932;
/// ASCII `FNN2`: exact arity-4 node sponge domain.
pub const EXACT_NODE_DOMAIN: u32 = 0x464e_4e32;
/// ASCII `FNE2`: exact empty-leaf sponge domain.
pub const EXACT_EMPTY_DOMAIN: u32 = 0x464e_4532;
/// ASCII `FNS3`: exact `(root8, count64)` accumulator-state sponge domain.
pub const EXACT_STATE_DOMAIN: u32 = 0x464e_5333;

pub const KEY_LIMBS: usize = 16;
pub const VALUE_LIMBS: usize = 4;
pub const ROOT_LANES: usize = 8;
pub const TREE_ARITY: usize = 4;
pub const TREE_DEPTH: usize = 16;
pub const TREE_CAPACITY: u64 = 1u64 << 32;

/// The full eight-lane Poseidon2 sponge result used by the Lean plan.
pub type Digest8 = [BabyBear; ROOT_LANES];

/// Exact untrusted tagged-key wire.
///
/// Tag `0` is `BOT`, tag `1` is `REAL`, and tag `2` is `TOP`.  Endpoint payloads must be zero.
/// A `REAL` payload contains all 256 input bits as sixteen little-endian-u16 chunks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TaggedKeyWire {
    pub tag: u8,
    pub raw_u16_le: [u16; KEY_LIMBS],
}

impl TaggedKeyWire {
    pub const fn bot() -> Self {
        Self {
            tag: 0,
            raw_u16_le: [0; KEY_LIMBS],
        }
    }

    pub const fn top() -> Self {
        Self {
            tag: 2,
            raw_u16_le: [0; KEY_LIMBS],
        }
    }

    pub fn real(raw: [u8; 32]) -> Self {
        Self {
            tag: 1,
            raw_u16_le: raw_to_u16_le(raw),
        }
    }

    pub fn decode(self) -> Result<ExactTaggedKey, ExactAafiError> {
        match self.tag {
            0 if self.raw_u16_le == [0; KEY_LIMBS] => Ok(ExactTaggedKey::Bot),
            0 => Err(ExactAafiError::NonCanonicalEndpointPayload { tag: 0 }),
            1 => Ok(ExactTaggedKey::Real(self.raw_u16_le)),
            2 if self.raw_u16_le == [0; KEY_LIMBS] => Ok(ExactTaggedKey::Top),
            2 => Err(ExactAafiError::NonCanonicalEndpointPayload { tag: 2 }),
            tag => Err(ExactAafiError::InvalidTag(tag)),
        }
    }
}

/// Canonical exact key.  The enum makes forged endpoint payloads unrepresentable after validation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExactTaggedKey {
    Bot,
    Real([u16; KEY_LIMBS]),
    Top,
}

impl ExactTaggedKey {
    pub fn from_raw(raw: [u8; 32]) -> Self {
        Self::Real(raw_to_u16_le(raw))
    }

    pub fn wire(self) -> TaggedKeyWire {
        match self {
            Self::Bot => TaggedKeyWire::bot(),
            Self::Real(raw_u16_le) => TaggedKeyWire { tag: 1, raw_u16_le },
            Self::Top => TaggedKeyWire::top(),
        }
    }

    pub fn real_raw_bytes(self) -> Option<[u8; 32]> {
        match self {
            Self::Real(limbs) => Some(u16_le_to_raw(limbs)),
            Self::Bot | Self::Top => None,
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Bot => 0,
            Self::Real(_) => 1,
            Self::Top => 2,
        }
    }

    fn payload(self) -> [u16; KEY_LIMBS] {
        match self {
            Self::Real(raw) => raw,
            Self::Bot | Self::Top => [0; KEY_LIMBS],
        }
    }
}

impl Ord for ExactTaggedKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.tag()
            .cmp(&other.tag())
            .then_with(|| self.payload().cmp(&other.payload()))
    }
}

impl PartialOrd for ExactTaggedKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// An untrusted exact linked-leaf wire.  All four `value_u16_le` limbs are committed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LinkedLeafWire {
    pub addr: TaggedKeyWire,
    pub value_u16_le: [u16; VALUE_LIMBS],
    pub next_addr: TaggedKeyWire,
}

/// Canonical exact linked leaf.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactLinkedLeaf {
    addr: ExactTaggedKey,
    value_u16_le: [u16; VALUE_LIMBS],
    next_addr: ExactTaggedKey,
}

impl ExactLinkedLeaf {
    fn genesis() -> Self {
        Self {
            addr: ExactTaggedKey::Bot,
            value_u16_le: [0; VALUE_LIMBS],
            next_addr: ExactTaggedKey::Top,
        }
    }

    pub fn addr(&self) -> ExactTaggedKey {
        self.addr
    }

    pub fn value(&self) -> u64 {
        u16_le_to_u64(self.value_u16_le)
    }

    pub fn next_addr(&self) -> ExactTaggedKey {
        self.next_addr
    }

    pub fn wire(self) -> LinkedLeafWire {
        LinkedLeafWire {
            addr: self.addr.wire(),
            value_u16_le: self.value_u16_le,
            next_addr: self.next_addr.wire(),
        }
    }

    fn decode(wire: LinkedLeafWire) -> Result<Self, ExactAafiError> {
        let addr = wire.addr.decode()?;
        let next_addr = wire.next_addr.decode()?;
        if matches!(addr, ExactTaggedKey::Top) {
            return Err(ExactAafiError::InvalidPredecessorAddress);
        }
        if matches!(next_addr, ExactTaggedKey::Bot) {
            return Err(ExactAafiError::InvalidPredecessorSuccessor);
        }
        Ok(Self {
            addr,
            value_u16_le: wire.value_u16_le,
            next_addr,
        })
    }

    fn with_next(self, next_addr: ExactTaggedKey) -> Self {
        Self { next_addr, ..self }
    }
}

/// One least-significant-digit-first depth-16 arity-4 authentication path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactPath4 {
    /// Child position at every level.  Every entry must be in `0..4`.
    pub positions: [u8; TREE_DEPTH],
    /// The other three children at each level, in increasing child-slot order.
    pub siblings: [[Digest8; TREE_ARITY - 1]; TREE_DEPTH],
}

/// Complete hostile-input witness for one exact append-at-free-index transition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactAafiWitness {
    pub inserted_key: TaggedKeyWire,
    pub inserted_value_u16_le: [u16; VALUE_LIMBS],
    pub predecessor: LinkedLeafWire,
    pub predecessor_position: u64,
    pub cursor: u64,
    pub prior_count: u64,
    pub successor_count: u64,
    pub predecessor_path: ExactPath4,
    pub append_path: ExactPath4,
    pub prior_root: Digest8,
    pub middle_root: Digest8,
    pub successor_root: Digest8,
    pub prior_state_commit: Digest8,
    pub successor_state_commit: Digest8,
}

/// A transition that passed every semantic, path, root, cursor, and count check in this module.
/// It is intentionally not constructible by callers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedExactAafiTransition {
    inserted_key: ExactTaggedKey,
    inserted_value: u64,
    predecessor_position: u32,
    prior_root: Digest8,
    successor_root: Digest8,
    prior_count: u64,
    successor_count: u64,
}

/// Durable zero-based append record.  Record `seq = s` reconstructs physical slot `s + 1` because
/// slot zero is permanently occupied by the `BOT` sentinel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactAppendRecord {
    pub seq: u64,
    pub raw: [u8; 32],
    pub value: u64,
}

impl ValidatedExactAafiTransition {
    pub fn inserted_raw(&self) -> [u8; 32] {
        self.inserted_key
            .real_raw_bytes()
            .expect("validated inserted key is always REAL")
    }

    pub fn inserted_value(&self) -> u64 {
        self.inserted_value
    }

    pub fn predecessor_position(&self) -> u32 {
        self.predecessor_position
    }

    pub fn prior_root(&self) -> Digest8 {
        self.prior_root
    }

    pub fn successor_root(&self) -> Digest8 {
        self.successor_root
    }

    pub fn prior_count(&self) -> u64 {
        self.prior_count
    }

    pub fn successor_count(&self) -> u64 {
        self.successor_count
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactAafiError {
    InvalidTag(u8),
    NonCanonicalEndpointPayload {
        tag: u8,
    },
    InsertedKeyMustBeReal,
    InvalidPredecessorAddress,
    InvalidPredecessorSuccessor,
    InvalidBracket,
    Duplicate,
    EmptyGenesisCount,
    TreeFull,
    CountIncrement,
    CursorDoesNotEqualPriorCount,
    PredecessorOutsideOccupiedPrefix,
    PathDigit {
        path: &'static str,
        level: usize,
        digit: u8,
    },
    PathIndex {
        path: &'static str,
        expected: u64,
        actual: u64,
    },
    RootMismatch(&'static str),
    StateCommitMismatch(&'static str),
    RuntimePriorStateMismatch,
    RuntimePredecessorMismatch,
    RuntimeSuccessorStateMismatch,
    RuntimeChainInvariant,
    ReplayDuplicateSeq(u64),
    ReplaySeqGap {
        expected: u64,
        found: u64,
    },
    ReplaySeqOutOfRange(u64),
}

impl fmt::Display for ExactAafiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTag(tag) => write!(f, "invalid exact-key tag {tag}"),
            Self::NonCanonicalEndpointPayload { tag } => {
                write!(f, "endpoint tag {tag} carries a nonzero payload")
            }
            Self::InsertedKeyMustBeReal => write!(f, "inserted key must have the REAL tag"),
            Self::InvalidPredecessorAddress => write!(f, "predecessor address cannot be TOP"),
            Self::InvalidPredecessorSuccessor => {
                write!(f, "predecessor successor cannot be BOT")
            }
            Self::InvalidBracket => write!(f, "predecessor does not strictly bracket inserted key"),
            Self::Duplicate => write!(f, "exact nullifier already exists"),
            Self::EmptyGenesisCount => {
                write!(f, "count zero is not the canonical BOT-only genesis")
            }
            Self::TreeFull => write!(f, "exact nullifier tree is terminal-full"),
            Self::CountIncrement => write!(f, "successor count is not prior count plus one"),
            Self::CursorDoesNotEqualPriorCount => {
                write!(f, "append cursor is not the authenticated prior count")
            }
            Self::PredecessorOutsideOccupiedPrefix => {
                write!(f, "predecessor position is outside the occupied prefix")
            }
            Self::PathDigit { path, level, digit } => {
                write!(
                    f,
                    "{path} path digit {digit} at level {level} is not radix-4"
                )
            }
            Self::PathIndex {
                path,
                expected,
                actual,
            } => write!(
                f,
                "{path} path decodes to {actual}, expected authenticated index {expected}"
            ),
            Self::RootMismatch(which) => write!(f, "{which} root does not recompose"),
            Self::StateCommitMismatch(which) => {
                write!(f, "{which} accumulator-state commitment does not open")
            }
            Self::RuntimePriorStateMismatch => {
                write!(f, "witness prior state is not the runtime's current state")
            }
            Self::RuntimePredecessorMismatch => {
                write!(
                    f,
                    "witness predecessor is not the runtime's exact predecessor"
                )
            }
            Self::RuntimeSuccessorStateMismatch => {
                write!(f, "witness successor is not the runtime-computed successor")
            }
            Self::RuntimeChainInvariant => write!(f, "runtime indexed-chain invariant is broken"),
            Self::ReplayDuplicateSeq(seq) => write!(f, "duplicate durable append sequence {seq}"),
            Self::ReplaySeqGap { expected, found } => write!(
                f,
                "durable append sequence is not dense: expected {expected}, found {found}"
            ),
            Self::ReplaySeqOutOfRange(seq) => {
                write!(f, "durable append sequence {seq} exceeds tree capacity")
            }
        }
    }
}

impl Error for ExactAafiError {}

/// Decode a 32-byte value exactly as sixteen little-endian `u16` chunks.
pub fn raw_to_u16_le(raw: [u8; 32]) -> [u16; KEY_LIMBS] {
    let mut out = [0u16; KEY_LIMBS];
    for (dst, bytes) in out.iter_mut().zip(raw.chunks_exact(2)) {
        *dst = u16::from_le_bytes([bytes[0], bytes[1]]);
    }
    out
}

pub fn u16_le_to_raw(limbs: [u16; KEY_LIMBS]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (limb, bytes) in limbs.iter().zip(out.chunks_exact_mut(2)) {
        bytes.copy_from_slice(&limb.to_le_bytes());
    }
    out
}

pub fn u64_to_u16_le(value: u64) -> [u16; VALUE_LIMBS] {
    [
        value as u16,
        (value >> 16) as u16,
        (value >> 32) as u16,
        (value >> 48) as u16,
    ]
}

pub fn u16_le_to_u64(limbs: [u16; VALUE_LIMBS]) -> u64 {
    u64::from(limbs[0])
        | (u64::from(limbs[1]) << 16)
        | (u64::from(limbs[2]) << 32)
        | (u64::from(limbs[3]) << 48)
}

fn tagged_key_felts(key: ExactTaggedKey) -> impl Iterator<Item = BabyBear> {
    std::iter::once(BabyBear::new(u32::from(key.tag()))).chain(
        key.payload()
            .into_iter()
            .map(|x| BabyBear::new(u32::from(x))),
    )
}

/// The exact 39-felt `FNI2 || addr17 || value4 || next17` preimage.
pub fn exact_leaf_preimage(leaf: ExactLinkedLeaf) -> Vec<BabyBear> {
    let mut input = Vec::with_capacity(39);
    input.push(BabyBear::new(EXACT_LINKED_LEAF_DOMAIN));
    input.extend(tagged_key_felts(leaf.addr));
    input.extend(
        leaf.value_u16_le
            .into_iter()
            .map(|x| BabyBear::new(u32::from(x))),
    );
    input.extend(tagged_key_felts(leaf.next_addr));
    debug_assert_eq!(input.len(), 39);
    input
}

pub fn exact_leaf_digest(leaf: ExactLinkedLeaf) -> Digest8 {
    hash_many_8(&exact_leaf_preimage(leaf))
}

/// The exact 33-felt `FNN2 || child0[8] || ... || child3[8]` preimage.
pub fn exact_node_preimage(children: [Digest8; TREE_ARITY]) -> Vec<BabyBear> {
    let mut input = Vec::with_capacity(33);
    input.push(BabyBear::new(EXACT_NODE_DOMAIN));
    for child in children {
        input.extend(child);
    }
    debug_assert_eq!(input.len(), 33);
    input
}

pub fn exact_node_digest(children: [Digest8; TREE_ARITY]) -> Digest8 {
    hash_many_8(&exact_node_preimage(children))
}

pub fn exact_empty_leaf_digest() -> Digest8 {
    hash_many_8(&[BabyBear::new(EXACT_EMPTY_DOMAIN)])
}

/// The exact 13-felt `FNS3 || root8 || count_u16_le[4]` preimage.
pub fn exact_state_preimage(root: Digest8, count: u64) -> Vec<BabyBear> {
    let mut input = Vec::with_capacity(13);
    input.push(BabyBear::new(EXACT_STATE_DOMAIN));
    input.extend(root);
    input.extend(
        u64_to_u16_le(count)
            .into_iter()
            .map(|x| BabyBear::new(u32::from(x))),
    );
    debug_assert_eq!(input.len(), 13);
    input
}

pub fn exact_state_commit(root: Digest8, count: u64) -> Digest8 {
    hash_many_8(&exact_state_preimage(root, count))
}

fn path_index(path: &ExactPath4, name: &'static str) -> Result<u64, ExactAafiError> {
    let mut index = 0u64;
    let mut radix = 1u64;
    for (level, digit) in path.positions.iter().copied().enumerate() {
        if digit >= TREE_ARITY as u8 {
            return Err(ExactAafiError::PathDigit {
                path: name,
                level,
                digit,
            });
        }
        index += u64::from(digit) * radix;
        radix *= TREE_ARITY as u64;
    }
    Ok(index)
}

fn recompose(mut current: Digest8, path: &ExactPath4) -> Result<Digest8, ExactAafiError> {
    for (level, (&position, siblings)) in
        path.positions.iter().zip(path.siblings.iter()).enumerate()
    {
        if position >= TREE_ARITY as u8 {
            return Err(ExactAafiError::PathDigit {
                path: "authentication",
                level,
                digit: position,
            });
        }
        let mut children = [[BabyBear::ZERO; ROOT_LANES]; TREE_ARITY];
        let mut sibling = 0usize;
        for (slot, child) in children.iter_mut().enumerate() {
            if slot == usize::from(position) {
                *child = current;
            } else {
                *child = siblings[sibling];
                sibling += 1;
            }
        }
        current = exact_node_digest(children);
    }
    Ok(current)
}

/// Validate a complete exact-nullifier transition independently of runtime state.
pub fn validate_exact_aafi_witness(
    witness: &ExactAafiWitness,
) -> Result<ValidatedExactAafiTransition, ExactAafiError> {
    if witness.prior_count == 0 {
        return Err(ExactAafiError::EmptyGenesisCount);
    }
    if witness.prior_count >= TREE_CAPACITY {
        return Err(ExactAafiError::TreeFull);
    }
    if witness.successor_count != witness.prior_count + 1 {
        return Err(ExactAafiError::CountIncrement);
    }
    if witness.cursor != witness.prior_count {
        return Err(ExactAafiError::CursorDoesNotEqualPriorCount);
    }
    if witness.predecessor_position >= witness.prior_count {
        return Err(ExactAafiError::PredecessorOutsideOccupiedPrefix);
    }

    let inserted_key = witness.inserted_key.decode()?;
    if !matches!(inserted_key, ExactTaggedKey::Real(_)) {
        return Err(ExactAafiError::InsertedKeyMustBeReal);
    }
    let predecessor = ExactLinkedLeaf::decode(witness.predecessor)?;
    if !(predecessor.addr < inserted_key && inserted_key < predecessor.next_addr) {
        return Err(ExactAafiError::InvalidBracket);
    }

    let predecessor_index = path_index(&witness.predecessor_path, "predecessor")?;
    if predecessor_index != witness.predecessor_position {
        return Err(ExactAafiError::PathIndex {
            path: "predecessor",
            expected: witness.predecessor_position,
            actual: predecessor_index,
        });
    }
    let append_index = path_index(&witness.append_path, "append")?;
    if append_index != witness.cursor {
        return Err(ExactAafiError::PathIndex {
            path: "append",
            expected: witness.cursor,
            actual: append_index,
        });
    }

    let predecessor_after = predecessor.with_next(inserted_key);
    let appended = ExactLinkedLeaf {
        addr: inserted_key,
        value_u16_le: witness.inserted_value_u16_le,
        next_addr: predecessor.next_addr,
    };

    if recompose(exact_leaf_digest(predecessor), &witness.predecessor_path)? != witness.prior_root {
        return Err(ExactAafiError::RootMismatch("prior predecessor"));
    }
    if recompose(
        exact_leaf_digest(predecessor_after),
        &witness.predecessor_path,
    )? != witness.middle_root
    {
        return Err(ExactAafiError::RootMismatch("middle predecessor"));
    }
    if recompose(exact_empty_leaf_digest(), &witness.append_path)? != witness.middle_root {
        return Err(ExactAafiError::RootMismatch("middle append-empty"));
    }
    if recompose(exact_leaf_digest(appended), &witness.append_path)? != witness.successor_root {
        return Err(ExactAafiError::RootMismatch("successor append"));
    }

    if exact_state_commit(witness.prior_root, witness.prior_count) != witness.prior_state_commit {
        return Err(ExactAafiError::StateCommitMismatch("prior"));
    }
    if exact_state_commit(witness.successor_root, witness.successor_count)
        != witness.successor_state_commit
    {
        return Err(ExactAafiError::StateCommitMismatch("successor"));
    }

    Ok(ValidatedExactAafiTransition {
        inserted_key,
        inserted_value: u16_le_to_u64(witness.inserted_value_u16_le),
        predecessor_position: witness.predecessor_position as u32,
        prior_root: witness.prior_root,
        successor_root: witness.successor_root,
        prior_count: witness.prior_count,
        successor_count: witness.successor_count,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SparseArity4Tree {
    /// `(level, index)`, where level zero is a leaf and level sixteen is the root.
    nodes: BTreeMap<(u8, u32), Digest8>,
    empty: [Digest8; TREE_DEPTH + 1],
}

impl SparseArity4Tree {
    fn new() -> Self {
        let mut empty = [[BabyBear::ZERO; ROOT_LANES]; TREE_DEPTH + 1];
        empty[0] = exact_empty_leaf_digest();
        for level in 1..=TREE_DEPTH {
            empty[level] = exact_node_digest([empty[level - 1]; TREE_ARITY]);
        }
        Self {
            nodes: BTreeMap::new(),
            empty,
        }
    }

    fn node(&self, level: usize, index: u32) -> Digest8 {
        self.nodes
            .get(&(level as u8, index))
            .copied()
            .unwrap_or(self.empty[level])
    }

    fn node_with_overlay(
        &self,
        level: usize,
        index: u32,
        overlay: &BTreeMap<(u8, u32), Digest8>,
    ) -> Digest8 {
        overlay
            .get(&(level as u8, index))
            .copied()
            .unwrap_or_else(|| self.node(level, index))
    }

    fn root(&self) -> Digest8 {
        self.node(TREE_DEPTH, 0)
    }

    fn replacement_overlay(
        &self,
        index: u32,
        replacement: Digest8,
        base_overlay: &BTreeMap<(u8, u32), Digest8>,
    ) -> BTreeMap<(u8, u32), Digest8> {
        let mut out = BTreeMap::new();
        let mut current_index = index;
        out.insert((0, current_index), replacement);
        for level in 1..=TREE_DEPTH {
            let parent_index = current_index / TREE_ARITY as u32;
            let first_child = parent_index * TREE_ARITY as u32;
            let mut children = [[BabyBear::ZERO; ROOT_LANES]; TREE_ARITY];
            for (slot, child) in children.iter_mut().enumerate() {
                let child_index = first_child + slot as u32;
                *child = out
                    .get(&((level - 1) as u8, child_index))
                    .copied()
                    .unwrap_or_else(|| {
                        self.node_with_overlay(level - 1, child_index, base_overlay)
                    });
            }
            out.insert((level as u8, parent_index), exact_node_digest(children));
            current_index = parent_index;
        }
        out
    }

    fn path_with_overlay(
        &self,
        mut index: u32,
        overlay: &BTreeMap<(u8, u32), Digest8>,
    ) -> ExactPath4 {
        let mut positions = [0u8; TREE_DEPTH];
        let mut siblings = [[[BabyBear::ZERO; ROOT_LANES]; TREE_ARITY - 1]; TREE_DEPTH];
        for level in 0..TREE_DEPTH {
            let position = (index % TREE_ARITY as u32) as u8;
            let parent = index / TREE_ARITY as u32;
            positions[level] = position;
            let mut sibling = 0usize;
            for slot in 0..TREE_ARITY {
                if slot != usize::from(position) {
                    siblings[level][sibling] = self.node_with_overlay(
                        level,
                        parent * TREE_ARITY as u32 + slot as u32,
                        overlay,
                    );
                    sibling += 1;
                }
            }
            index = parent;
        }
        ExactPath4 {
            positions,
            siblings,
        }
    }

    fn apply_overlay(&mut self, overlay: BTreeMap<(u8, u32), Digest8>) {
        for ((level, index), digest) in overlay {
            if digest == self.empty[usize::from(level)] {
                self.nodes.remove(&(level, index));
            } else {
                self.nodes.insert((level, index), digest);
            }
        }
    }
}

/// Sparse O(depth)-update runtime for the exact append-order accumulator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactNullifierAafi {
    tree: SparseArity4Tree,
    leaves: BTreeMap<u32, ExactLinkedLeaf>,
    ordered_positions: BTreeMap<ExactTaggedKey, u32>,
    count: u64,
}

impl Default for ExactNullifierAafi {
    fn default() -> Self {
        Self::new()
    }
}

impl ExactNullifierAafi {
    /// Canonical logical-empty state: slot zero contains `BOT(value=0,next=TOP)`, count is one.
    pub fn new() -> Self {
        let genesis = ExactLinkedLeaf::genesis();
        let mut tree = SparseArity4Tree::new();
        let overlay = tree.replacement_overlay(0, exact_leaf_digest(genesis), &BTreeMap::new());
        tree.apply_overlay(overlay);
        let mut leaves = BTreeMap::new();
        leaves.insert(0, genesis);
        let mut ordered_positions = BTreeMap::new();
        ordered_positions.insert(ExactTaggedKey::Bot, 0);
        Self {
            tree,
            leaves,
            ordered_positions,
            count: 1,
        }
    }

    pub fn count(&self) -> u64 {
        self.count
    }

    pub fn root(&self) -> Digest8 {
        self.tree.root()
    }

    pub fn state_commit(&self) -> Digest8 {
        exact_state_commit(self.root(), self.count)
    }

    pub fn contains(&self, raw: [u8; 32]) -> bool {
        self.ordered_positions
            .contains_key(&ExactTaggedKey::from_raw(raw))
    }

    pub fn value(&self, raw: [u8; 32]) -> Option<u64> {
        let position = self.ordered_positions.get(&ExactTaggedKey::from_raw(raw))?;
        self.leaves.get(position).map(ExactLinkedLeaf::value)
    }

    /// Reconstruct append-order state from durable records in arbitrary storage iteration order.
    ///
    /// The durable sequence is an ABI, not a hint: it must be exactly `0..n`, with no duplicate,
    /// gap, or out-of-capacity value.  Replaying only sorted nullifier keys would recreate the old
    /// dense tree, not this AAFI root.
    pub fn from_append_records(
        records: impl IntoIterator<Item = ExactAppendRecord>,
    ) -> Result<Self, ExactAafiError> {
        let mut ordered = BTreeMap::new();
        for record in records {
            if record.seq >= TREE_CAPACITY - 1 {
                return Err(ExactAafiError::ReplaySeqOutOfRange(record.seq));
            }
            if ordered.insert(record.seq, record).is_some() {
                return Err(ExactAafiError::ReplayDuplicateSeq(record.seq));
            }
        }

        let mut state = Self::new();
        for (expected, (seq, record)) in (0u64..).zip(ordered) {
            if seq != expected {
                return Err(ExactAafiError::ReplaySeqGap {
                    expected,
                    found: seq,
                });
            }
            debug_assert_eq!(state.count(), seq + 1);
            state.insert(record.raw, record.value)?;
        }
        Ok(state)
    }

    /// Construct, but do not apply, the complete two-path witness.
    pub fn prepare_insert(
        &self,
        raw: [u8; 32],
        value: u64,
    ) -> Result<ExactAafiWitness, ExactAafiError> {
        if self.count >= TREE_CAPACITY {
            return Err(ExactAafiError::TreeFull);
        }
        let inserted_key = ExactTaggedKey::from_raw(raw);
        if self.ordered_positions.contains_key(&inserted_key) {
            return Err(ExactAafiError::Duplicate);
        }
        let (&predecessor_key, &predecessor_position) = self
            .ordered_positions
            .range(..inserted_key)
            .next_back()
            .ok_or(ExactAafiError::RuntimeChainInvariant)?;
        let predecessor = *self
            .leaves
            .get(&predecessor_position)
            .ok_or(ExactAafiError::RuntimeChainInvariant)?;
        if predecessor.addr != predecessor_key
            || !(predecessor.addr < inserted_key && inserted_key < predecessor.next_addr)
        {
            return Err(ExactAafiError::RuntimeChainInvariant);
        }

        let predecessor_path = self
            .tree
            .path_with_overlay(predecessor_position, &BTreeMap::new());
        let predecessor_after = predecessor.with_next(inserted_key);
        let predecessor_overlay = self.tree.replacement_overlay(
            predecessor_position,
            exact_leaf_digest(predecessor_after),
            &BTreeMap::new(),
        );
        let middle_root = predecessor_overlay
            .get(&(TREE_DEPTH as u8, 0))
            .copied()
            .ok_or(ExactAafiError::RuntimeChainInvariant)?;

        let cursor = self.count;
        let cursor_u32 = cursor as u32;
        let append_path = self
            .tree
            .path_with_overlay(cursor_u32, &predecessor_overlay);
        let appended = ExactLinkedLeaf {
            addr: inserted_key,
            value_u16_le: u64_to_u16_le(value),
            next_addr: predecessor.next_addr,
        };
        let append_overlay = self.tree.replacement_overlay(
            cursor_u32,
            exact_leaf_digest(appended),
            &predecessor_overlay,
        );
        let successor_root = append_overlay
            .get(&(TREE_DEPTH as u8, 0))
            .copied()
            .ok_or(ExactAafiError::RuntimeChainInvariant)?;
        let prior_root = self.root();
        let successor_count = self.count + 1;

        Ok(ExactAafiWitness {
            inserted_key: inserted_key.wire(),
            inserted_value_u16_le: u64_to_u16_le(value),
            predecessor: predecessor.wire(),
            predecessor_position: u64::from(predecessor_position),
            cursor,
            prior_count: self.count,
            successor_count,
            predecessor_path,
            append_path,
            prior_root,
            middle_root,
            successor_root,
            prior_state_commit: exact_state_commit(prior_root, self.count),
            successor_state_commit: exact_state_commit(successor_root, successor_count),
        })
    }

    /// Validate against the current runtime state and apply transactionally.
    pub fn apply_witness(
        &mut self,
        witness: &ExactAafiWitness,
    ) -> Result<ValidatedExactAafiTransition, ExactAafiError> {
        let validated = validate_exact_aafi_witness(witness)?;
        if witness.prior_count != self.count
            || witness.prior_root != self.root()
            || witness.prior_state_commit != self.state_commit()
        {
            return Err(ExactAafiError::RuntimePriorStateMismatch);
        }
        if self.ordered_positions.contains_key(&validated.inserted_key) {
            return Err(ExactAafiError::Duplicate);
        }
        let predecessor = ExactLinkedLeaf::decode(witness.predecessor)?;
        let predecessor_position = validated.predecessor_position;
        let actual_position = self
            .ordered_positions
            .range(..validated.inserted_key)
            .next_back()
            .map(|(_, position)| *position)
            .ok_or(ExactAafiError::RuntimeChainInvariant)?;
        if actual_position != predecessor_position
            || self.leaves.get(&predecessor_position) != Some(&predecessor)
        {
            return Err(ExactAafiError::RuntimePredecessorMismatch);
        }

        // Recompute the runtime candidate independently of the caller's paths.  All checks happen
        // before mutation, including in release builds; `debug_assert` is never a security gate.
        let predecessor_after = predecessor.with_next(validated.inserted_key);
        let predecessor_overlay = self.tree.replacement_overlay(
            predecessor_position,
            exact_leaf_digest(predecessor_after),
            &BTreeMap::new(),
        );
        let candidate_middle = predecessor_overlay
            .get(&(TREE_DEPTH as u8, 0))
            .copied()
            .ok_or(ExactAafiError::RuntimeChainInvariant)?;

        let cursor = self.count as u32;
        if self.tree.node(0, cursor) != exact_empty_leaf_digest() {
            return Err(ExactAafiError::RuntimeChainInvariant);
        }
        let appended = ExactLinkedLeaf {
            addr: validated.inserted_key,
            value_u16_le: witness.inserted_value_u16_le,
            next_addr: predecessor.next_addr,
        };
        let append_overlay = self.tree.replacement_overlay(
            cursor,
            exact_leaf_digest(appended),
            &predecessor_overlay,
        );
        let candidate_successor = append_overlay
            .get(&(TREE_DEPTH as u8, 0))
            .copied()
            .ok_or(ExactAafiError::RuntimeChainInvariant)?;
        if candidate_middle != witness.middle_root
            || candidate_successor != witness.successor_root
            || exact_state_commit(candidate_successor, self.count + 1)
                != witness.successor_state_commit
        {
            return Err(ExactAafiError::RuntimeSuccessorStateMismatch);
        }

        // Candidate is now fully checked.  Applying these two O(depth) overlays cannot refuse.
        self.tree.apply_overlay(predecessor_overlay);
        self.tree.apply_overlay(append_overlay);
        self.leaves.insert(predecessor_position, predecessor_after);
        self.leaves.insert(cursor, appended);
        self.ordered_positions
            .insert(validated.inserted_key, cursor);
        self.count += 1;

        assert_eq!(self.root(), witness.successor_root);
        assert_eq!(self.state_commit(), witness.successor_state_commit);
        Ok(validated)
    }

    pub fn insert(
        &mut self,
        raw: [u8; 32],
        value: u64,
    ) -> Result<ValidatedExactAafiTransition, ExactAafiError> {
        let witness = self.prepare_insert(raw, value)?;
        self.apply_witness(&witness)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw_with_first_u16(value: u16) -> [u8; 32] {
        let mut raw = [0u8; 32];
        raw[..2].copy_from_slice(&value.to_le_bytes());
        raw
    }

    fn digest(values: [u32; ROOT_LANES]) -> Digest8 {
        values.map(BabyBear::new)
    }

    fn assert_refuses_without_mutation(
        state: &mut ExactNullifierAafi,
        witness: &ExactAafiWitness,
        expected: impl FnOnce(&ExactAafiError) -> bool,
    ) {
        let before = state.clone();
        let error = state
            .apply_witness(witness)
            .expect_err("hostile witness must refuse");
        assert!(expected(&error), "unexpected refusal: {error:?}");
        assert_eq!(*state, before, "refusal must be transactional");
    }

    #[test]
    fn exact_geometry_and_order_abi_are_pinned() {
        let state = ExactNullifierAafi::new();
        assert_eq!(state.count(), 1);
        assert_ne!(state.root(), state.tree.empty[TREE_DEPTH]);
        assert_eq!(exact_leaf_preimage(ExactLinkedLeaf::genesis()).len(), 39);
        assert_eq!(
            exact_node_preimage([[BabyBear::ZERO; ROOT_LANES]; TREE_ARITY]).len(),
            33
        );
        assert_eq!(exact_state_preimage(state.root(), state.count()).len(), 13);

        // Cross-language KATs evaluated directly from the Lean definitions in
        // `ExactNullifierAafiDescriptorPlan`: `exactLeafDigestReal exactGenesisLeaf`,
        // `exactEmptyLeafReal`, one `exactNodeDigestList [genesis, empty, empty, empty]`, its
        // `accumulatorStateCommitReal _ countOne`, and the all-ff appended leaf respectively.
        let genesis_leaf = exact_leaf_digest(ExactLinkedLeaf::genesis());
        assert_eq!(
            genesis_leaf,
            digest([
                553_521_783,
                739_395_667,
                1_064_497_434,
                1_669_175_865,
                23_127_124,
                831_993_428,
                200_020_645,
                56_289_367,
            ])
        );
        let empty_leaf = exact_empty_leaf_digest();
        assert_eq!(
            empty_leaf,
            digest([
                1_802_464_954,
                1_721_499_353,
                1_979_478_910,
                447_874_828,
                920_245_230,
                1_244_183_099,
                10_235_817,
                1_896_623_126,
            ])
        );
        let first_node = exact_node_digest([genesis_leaf, empty_leaf, empty_leaf, empty_leaf]);
        assert_eq!(
            first_node,
            digest([
                870_482_489,
                1_298_961_555,
                236_370_950,
                95_853_994,
                1_219_982_061,
                1_067_502_163,
                410_684_317,
                1_338_509_777,
            ])
        );
        assert_eq!(
            exact_state_commit(first_node, 1),
            digest([
                1_055_458_131,
                1_530_696_711,
                544_796_148,
                1_572_792_285,
                31_301_791,
                543_157_439,
                1_679_264_059,
                111_754_335,
            ])
        );
        let ff_leaf = ExactLinkedLeaf {
            addr: ExactTaggedKey::from_raw([0xff; 32]),
            value_u16_le: [u16::MAX; VALUE_LIMBS],
            next_addr: ExactTaggedKey::Top,
        };
        assert_eq!(
            exact_leaf_digest(ff_leaf),
            digest([
                1_185_380_084,
                1_823_907_752,
                1_007_180_392,
                50_876_821,
                1_992_744_839,
                1_080_965_717,
                561_288_532,
                1_816_524_695,
            ])
        );

        // Lean KAT: numeric LE-u16 lane lex says 255 < 256, while byte lex says 00 < ff.
        let a = [
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        let b = [
            255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
        ];
        assert!(a < b, "Rust byte lex KAT premise");
        assert!(ExactTaggedKey::from_raw(b) < ExactTaggedKey::from_raw(a));
    }

    #[test]
    fn full_raw_domain_including_zero_and_ff_is_spendable() {
        let mut state = ExactNullifierAafi::new();
        let zero = state.insert([0u8; 32], 0).expect("REAL(00..00)");
        assert_eq!(zero.inserted_raw(), [0u8; 32]);
        let ff = state.insert([0xffu8; 32], u64::MAX).expect("REAL(ff..ff)");
        assert_eq!(ff.inserted_raw(), [0xffu8; 32]);
        assert_eq!(ff.inserted_value(), u64::MAX);
        assert_eq!(state.value([0xffu8; 32]), Some(u64::MAX));
        assert_eq!(state.count(), 3);
    }

    #[test]
    fn duplicate_and_wrong_bracket_refuse() {
        let raw = raw_with_first_u16(7);
        let mut state = ExactNullifierAafi::new();
        state.insert(raw, 1).expect("first insert");
        assert_eq!(state.prepare_insert(raw, 2), Err(ExactAafiError::Duplicate));

        let mut witness = state
            .prepare_insert(raw_with_first_u16(9), 2)
            .expect("honest witness");
        witness.inserted_key = TaggedKeyWire::real(raw_with_first_u16(7));
        assert_refuses_without_mutation(&mut state, &witness, |error| {
            matches!(error, ExactAafiError::InvalidBracket)
        });
    }

    #[test]
    fn wrong_path_cursor_count_and_roots_refuse_transactionally() {
        let mut state = ExactNullifierAafi::new();
        state.insert(raw_with_first_u16(10), 10).unwrap();
        let honest = state.prepare_insert(raw_with_first_u16(5), 5).unwrap();

        let mut wrong_path = honest.clone();
        wrong_path.predecessor_path.positions[0] ^= 1;
        assert_refuses_without_mutation(&mut state, &wrong_path, |error| {
            matches!(
                error,
                ExactAafiError::PathIndex {
                    path: "predecessor",
                    ..
                }
            )
        });

        let mut wrong_sibling = honest.clone();
        wrong_sibling.append_path.siblings[0][0][0] += BabyBear::ONE;
        assert_refuses_without_mutation(&mut state, &wrong_sibling, |error| {
            matches!(error, ExactAafiError::RootMismatch("middle append-empty"))
        });

        let mut wrong_cursor = honest.clone();
        wrong_cursor.cursor += 1;
        assert_refuses_without_mutation(&mut state, &wrong_cursor, |error| {
            matches!(error, ExactAafiError::CursorDoesNotEqualPriorCount)
        });

        let mut wrong_count = honest.clone();
        wrong_count.successor_count += 1;
        assert_refuses_without_mutation(&mut state, &wrong_count, |error| {
            matches!(error, ExactAafiError::CountIncrement)
        });

        let mut wrong_prior_root = honest.clone();
        wrong_prior_root.prior_root[0] += BabyBear::ONE;
        assert_refuses_without_mutation(&mut state, &wrong_prior_root, |error| {
            matches!(error, ExactAafiError::RootMismatch("prior predecessor"))
        });

        let mut wrong_middle_root = honest.clone();
        wrong_middle_root.middle_root[7] += BabyBear::ONE;
        assert_refuses_without_mutation(&mut state, &wrong_middle_root, |error| {
            matches!(error, ExactAafiError::RootMismatch("middle predecessor"))
        });

        let mut wrong_successor_root = honest.clone();
        wrong_successor_root.successor_root[3] += BabyBear::ONE;
        assert_refuses_without_mutation(&mut state, &wrong_successor_root, |error| {
            matches!(error, ExactAafiError::RootMismatch("successor append"))
        });

        let mut wrong_commit = honest.clone();
        wrong_commit.successor_state_commit[2] += BabyBear::ONE;
        assert_refuses_without_mutation(&mut state, &wrong_commit, |error| {
            matches!(error, ExactAafiError::StateCommitMismatch("successor"))
        });
    }

    #[test]
    fn malformed_tag_and_endpoint_payload_refuse() {
        let mut state = ExactNullifierAafi::new();
        let honest = state.prepare_insert(raw_with_first_u16(3), 4).unwrap();

        let mut invalid_tag = honest.clone();
        invalid_tag.inserted_key.tag = 9;
        assert_refuses_without_mutation(&mut state, &invalid_tag, |error| {
            matches!(error, ExactAafiError::InvalidTag(9))
        });

        let mut endpoint_as_insert = honest.clone();
        endpoint_as_insert.inserted_key = TaggedKeyWire::top();
        assert_refuses_without_mutation(&mut state, &endpoint_as_insert, |error| {
            matches!(error, ExactAafiError::InsertedKeyMustBeReal)
        });

        let mut endpoint_payload = honest.clone();
        endpoint_payload.predecessor.addr.raw_u16_le[15] = 1;
        assert_refuses_without_mutation(&mut state, &endpoint_payload, |error| {
            matches!(
                error,
                ExactAafiError::NonCanonicalEndpointPayload { tag: 0 }
            )
        });
    }

    #[test]
    fn two_paths_chain_and_nontrivial_predecessor_update_apply() {
        let mut state = ExactNullifierAafi::new();
        state.insert(raw_with_first_u16(20), 20).unwrap();
        state.insert(raw_with_first_u16(5), 5).unwrap();
        let witness = state.prepare_insert(raw_with_first_u16(10), 10).unwrap();
        assert_eq!(witness.predecessor_position, 2);
        let checked = validate_exact_aafi_witness(&witness).expect("static validation");
        assert_eq!(checked.predecessor_position(), 2);
        state.apply_witness(&witness).expect("runtime apply");
        assert!(state.contains(raw_with_first_u16(10)));
        assert_eq!(state.root(), witness.successor_root);
        assert_eq!(state.state_commit(), witness.successor_state_commit);
    }

    #[test]
    fn durable_append_replay_is_order_independent_and_strictly_dense() {
        let records = vec![
            ExactAppendRecord {
                seq: 0,
                raw: raw_with_first_u16(20),
                value: 20,
            },
            ExactAppendRecord {
                seq: 1,
                raw: raw_with_first_u16(5),
                value: 5,
            },
            ExactAppendRecord {
                seq: 2,
                raw: [0xff; 32],
                value: u64::MAX,
            },
        ];
        let expected = ExactNullifierAafi::from_append_records(records.clone()).unwrap();
        let shuffled =
            ExactNullifierAafi::from_append_records([records[2], records[0], records[1]]).unwrap();
        assert_eq!(shuffled, expected);
        assert_eq!(shuffled.count(), 4);

        // Same logical key/value set, different append sequence: deliberately a different root.
        // This is why the old sorted CanonicalHeapTree8 rebuild cannot recover AAFI state.
        let reordered = ExactNullifierAafi::from_append_records([
            ExactAppendRecord {
                seq: 0,
                ..records[1]
            },
            ExactAppendRecord {
                seq: 1,
                ..records[0]
            },
            records[2],
        ])
        .unwrap();
        assert_ne!(reordered.root(), expected.root());
        assert_ne!(reordered.state_commit(), expected.state_commit());

        assert_eq!(
            ExactNullifierAafi::from_append_records([records[0], records[0]]),
            Err(ExactAafiError::ReplayDuplicateSeq(0))
        );
        assert_eq!(
            ExactNullifierAafi::from_append_records([records[0], records[2]]),
            Err(ExactAafiError::ReplaySeqGap {
                expected: 1,
                found: 2
            })
        );
        assert_eq!(
            ExactNullifierAafi::from_append_records([ExactAppendRecord {
                seq: u64::MAX,
                raw: [1; 32],
                value: 1,
            }]),
            Err(ExactAafiError::ReplaySeqOutOfRange(u64::MAX))
        );
    }

    #[test]
    fn runtime_index_corruption_refuses_before_tree_mutation() {
        let mut state = ExactNullifierAafi::new();
        state.insert(raw_with_first_u16(20), 20).unwrap();
        state.insert(raw_with_first_u16(5), 5).unwrap();
        let witness = state.prepare_insert(raw_with_first_u16(10), 10).unwrap();

        // Model a collision-shaped/hostile runtime lookup result while leaving the authenticated
        // tree untouched.  The runtime must not begin either root rewrite.
        state
            .ordered_positions
            .insert(ExactTaggedKey::from_raw(raw_with_first_u16(5)), 1);
        let before_tree = state.tree.clone();
        assert_eq!(
            state.apply_witness(&witness),
            Err(ExactAafiError::RuntimePredecessorMismatch)
        );
        assert_eq!(state.tree, before_tree);
        assert_eq!(state.root(), witness.prior_root);
    }

    #[test]
    fn many_nonmonotone_appends_cross_radix_boundaries_and_replay() {
        let mut live = ExactNullifierAafi::new();
        let mut records = Vec::new();
        for seq in 0u64..65 {
            let key = ((seq * 37) % 65) as u16;
            let raw = raw_with_first_u16(key);
            let value = seq.wrapping_mul(0x1_0001_0001);
            let transition = live.insert(raw, value).expect("fresh permuted key");
            assert_eq!(transition.prior_count(), seq + 1);
            assert_eq!(transition.successor_count(), seq + 2);
            records.push(ExactAppendRecord { seq, raw, value });
        }
        records.reverse();
        let replay = ExactNullifierAafi::from_append_records(records).unwrap();
        assert_eq!(replay, live);
        assert_eq!(replay.count(), 66);
    }
}
