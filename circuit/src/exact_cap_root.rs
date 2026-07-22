//! Lossless typed capability leaves and their canonical openable root.
//!
//! All authoritative source values enter Poseidon2 through canonical `u16`
//! limbs. Leaf, node, padding, sentinel, and final-root domains are distinct.

use crate::faithful8::Faithful8;
use crate::field::BabyBear;
use crate::poseidon2::hash_many_8;
use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

pub const EXACT_CAP_TREE_DEPTH: usize = 16;
pub const EXACT_CAP_DIGEST_W: usize = 8;
pub const EXACT_CAP_BYTES32_LIMBS: usize = 16;
pub const EXACT_CAP_U32_LIMBS: usize = 2;
pub const EXACT_CAP_U64_LIMBS: usize = 4;

/// ASCII `CPL2` / `CPN2` / `CPR2` / `CPE2` / `CPM2` / `CPX2`.
pub const EXACT_CAP_LEAF_DOMAIN: u32 = 0x4350_4c32;
pub const EXACT_CAP_NODE_DOMAIN: u32 = 0x4350_4e32;
pub const EXACT_CAP_ROOT_DOMAIN: u32 = 0x4350_5232;
pub const EXACT_CAP_EMPTY_DOMAIN: u32 = 0x4350_4532;
pub const EXACT_CAP_MIN_DOMAIN: u32 = 0x4350_4d32;
pub const EXACT_CAP_MAX_DOMAIN: u32 = 0x4350_5832;

/// `domain || slot[2] || target[16] || auth_tag || custom_vk[16] ||
/// mask[2] || expiry_present || expiry[4] || breadstuff_present || breadstuff[16]`.
pub const EXACT_CAP_LEAF_PREIMAGE_LEN: usize = 60;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExactCapAuth {
    None,
    Signature,
    Proof,
    Either,
    Impossible,
    Custom([u8; 32]),
}

impl ExactCapAuth {
    pub const fn tag(self) -> u8 {
        match self {
            Self::None => 0,
            Self::Signature => 1,
            Self::Proof => 2,
            Self::Either => 3,
            Self::Impossible => 4,
            Self::Custom(_) => 5,
        }
    }

    pub const fn custom_vk(self) -> [u8; 32] {
        match self {
            Self::Custom(vk) => vk,
            _ => [0; 32],
        }
    }
}

pub fn bytes32_to_u16_le(bytes: [u8; 32]) -> [u16; EXACT_CAP_BYTES32_LIMBS] {
    core::array::from_fn(|i| u16::from_le_bytes([bytes[2 * i], bytes[2 * i + 1]]))
}

pub fn u32_to_u16_le(value: u32) -> [u16; EXACT_CAP_U32_LIMBS] {
    [value as u16, (value >> 16) as u16]
}

pub fn u64_to_u16_le(value: u64) -> [u16; EXACT_CAP_U64_LIMBS] {
    core::array::from_fn(|i| (value >> (16 * i)) as u16)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactCapLeaf {
    slot: u32,
    target: [u8; 32],
    auth: ExactCapAuth,
    mask: u32,
    expiry: Option<u64>,
    breadstuff: Option<[u8; 32]>,
}

impl ExactCapLeaf {
    pub const fn new(
        slot: u32,
        target: [u8; 32],
        auth: ExactCapAuth,
        mask: u32,
        expiry: Option<u64>,
        breadstuff: Option<[u8; 32]>,
    ) -> Self {
        Self {
            slot,
            target,
            auth,
            mask,
            expiry,
            breadstuff,
        }
    }

    pub const fn slot(self) -> u32 {
        self.slot
    }
    pub const fn target(self) -> [u8; 32] {
        self.target
    }
    pub const fn auth(self) -> ExactCapAuth {
        self.auth
    }
    pub const fn mask(self) -> u32 {
        self.mask
    }
    pub const fn expiry(self) -> Option<u64> {
        self.expiry
    }
    pub const fn breadstuff(self) -> Option<[u8; 32]> {
        self.breadstuff
    }

    pub fn preimage(self) -> [BabyBear; EXACT_CAP_LEAF_PREIMAGE_LEN] {
        let mut out = [BabyBear::ZERO; EXACT_CAP_LEAF_PREIMAGE_LEN];
        let mut at = 0usize;
        macro_rules! push {
            ($value:expr) => {{
                out[at] = $value;
                at += 1;
            }};
        }
        push!(BabyBear::new(EXACT_CAP_LEAF_DOMAIN));
        for x in u32_to_u16_le(self.slot) {
            push!(BabyBear::new(x.into()));
        }
        for x in bytes32_to_u16_le(self.target) {
            push!(BabyBear::new(x.into()));
        }
        push!(BabyBear::new(self.auth.tag().into()));
        for x in bytes32_to_u16_le(self.auth.custom_vk()) {
            push!(BabyBear::new(x.into()));
        }
        for x in u32_to_u16_le(self.mask) {
            push!(BabyBear::new(x.into()));
        }
        push!(BabyBear::new(u32::from(self.expiry.is_some())));
        for x in u64_to_u16_le(self.expiry.unwrap_or(0)) {
            push!(BabyBear::new(x.into()));
        }
        push!(BabyBear::new(u32::from(self.breadstuff.is_some())));
        for x in bytes32_to_u16_le(self.breadstuff.unwrap_or([0; 32])) {
            push!(BabyBear::new(x.into()));
        }
        debug_assert_eq!(at, EXACT_CAP_LEAF_PREIMAGE_LEN);
        out
    }

    pub fn digest8(self) -> [BabyBear; EXACT_CAP_DIGEST_W] {
        hash_many_8(&self.preimage())
    }
}

pub fn exact_cap_node8(
    left: [BabyBear; EXACT_CAP_DIGEST_W],
    right: [BabyBear; EXACT_CAP_DIGEST_W],
) -> [BabyBear; EXACT_CAP_DIGEST_W] {
    let mut input = [BabyBear::ZERO; 1 + 2 * EXACT_CAP_DIGEST_W];
    input[0] = BabyBear::new(EXACT_CAP_NODE_DOMAIN);
    input[1..9].copy_from_slice(&left);
    input[9..].copy_from_slice(&right);
    hash_many_8(&input)
}

pub fn exact_cap_root8(top: [BabyBear; 8]) -> [BabyBear; 8] {
    let mut input = [BabyBear::ZERO; 9];
    input[0] = BabyBear::new(EXACT_CAP_ROOT_DOMAIN);
    input[1..].copy_from_slice(&top);
    hash_many_8(&input)
}

pub fn exact_cap_empty_leaf8() -> [BabyBear; 8] {
    hash_many_8(&[BabyBear::new(EXACT_CAP_EMPTY_DOMAIN)])
}

fn exact_cap_min_leaf8() -> [BabyBear; 8] {
    hash_many_8(&[BabyBear::new(EXACT_CAP_MIN_DOMAIN)])
}

fn exact_cap_max_leaf8() -> [BabyBear; 8] {
    hash_many_8(&[BabyBear::new(EXACT_CAP_MAX_DOMAIN)])
}

fn exact_cap_empty_roots(depth: usize) -> Vec<[BabyBear; 8]> {
    let mut roots = Vec::with_capacity(depth + 1);
    roots.push(exact_cap_empty_leaf8());
    for level in 0..depth {
        roots.push(exact_cap_node8(roots[level], roots[level]));
    }
    roots
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StoredCapLeaf {
    Min,
    Live(ExactCapLeaf),
    Tombstone(u32),
    Max,
}

impl StoredCapLeaf {
    fn key(self) -> u64 {
        match self {
            Self::Min => 0,
            Self::Live(x) => u64::from(x.slot) + 1,
            Self::Tombstone(x) => u64::from(x) + 1,
            Self::Max => u64::from(u32::MAX) + 2,
        }
    }

    fn digest(self) -> [BabyBear; 8] {
        match self {
            Self::Min => exact_cap_min_leaf8(),
            Self::Live(x) => x.digest8(),
            Self::Tombstone(_) => exact_cap_empty_leaf8(),
            Self::Max => exact_cap_max_leaf8(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactCapTreeError {
    DuplicateSlot(u32),
    DuplicateTombstone(u32),
    CapacityExceeded { entries: usize, capacity: usize },
}

impl fmt::Display for ExactCapTreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateSlot(x) => write!(f, "duplicate capability slot {x}"),
            Self::DuplicateTombstone(x) => write!(f, "duplicate capability tombstone {x}"),
            Self::CapacityExceeded { entries, capacity } => write!(
                f,
                "capability tree ({entries} entries) exceeds capacity {capacity}"
            ),
        }
    }
}
impl Error for ExactCapTreeError {}

#[derive(Clone, Debug)]
pub struct CanonicalExactCapTree8 {
    levels: Vec<Vec<[BabyBear; 8]>>,
    entries: Vec<StoredCapLeaf>,
    empty_roots: Vec<[BabyBear; 8]>,
    depth: usize,
}

impl CanonicalExactCapTree8 {
    pub fn try_new(xs: Vec<ExactCapLeaf>, depth: usize) -> Result<Self, ExactCapTreeError> {
        Self::try_new_with_tombstones(xs, &[], depth)
    }
    pub fn new(xs: Vec<ExactCapLeaf>, depth: usize) -> Self {
        Self::try_new(xs, depth).expect("invalid exact capability tree")
    }
    pub fn new_with_tombstones(xs: Vec<ExactCapLeaf>, tombs: &[u32], depth: usize) -> Self {
        Self::try_new_with_tombstones(xs, tombs, depth).expect("invalid exact capability tree")
    }

    pub fn try_new_with_tombstones(
        mut leaves: Vec<ExactCapLeaf>,
        tombs: &[u32],
        depth: usize,
    ) -> Result<Self, ExactCapTreeError> {
        leaves.sort_by_key(|x| x.slot);
        if let Some(w) = leaves.windows(2).find(|w| w[0].slot == w[1].slot) {
            return Err(ExactCapTreeError::DuplicateSlot(w[0].slot));
        }
        let live: BTreeSet<u32> = leaves.iter().map(|x| x.slot).collect();
        let mut seen = BTreeSet::new();
        for &slot in tombs {
            if !seen.insert(slot) {
                return Err(ExactCapTreeError::DuplicateTombstone(slot));
            }
        }
        let mut entries = vec![StoredCapLeaf::Min];
        entries.extend(leaves.into_iter().map(StoredCapLeaf::Live));
        entries.extend(
            tombs
                .iter()
                .copied()
                .filter(|x| !live.contains(x))
                .map(StoredCapLeaf::Tombstone),
        );
        entries.push(StoredCapLeaf::Max);
        entries.sort_by_key(|x| x.key());
        let capacity = 1usize.checked_shl(depth as u32).unwrap_or(0);
        if capacity == 0 || entries.len() > capacity {
            return Err(ExactCapTreeError::CapacityExceeded {
                entries: entries.len(),
                capacity,
            });
        }
        let empty_roots = exact_cap_empty_roots(depth);
        let mut levels: Vec<Vec<[BabyBear; 8]>> =
            vec![entries.iter().copied().map(StoredCapLeaf::digest).collect()];
        for level in 0..depth {
            let prev = levels.last().expect("cap level");
            let mut next = Vec::with_capacity(prev.len().div_ceil(2));
            for i in 0..prev.len().div_ceil(2) {
                let left = prev[2 * i];
                let right = prev.get(2 * i + 1).copied().unwrap_or(empty_roots[level]);
                next.push(exact_cap_node8(left, right));
            }
            levels.push(next);
        }
        Ok(Self {
            levels,
            entries,
            empty_roots,
            depth,
        })
    }

    fn node(&self, level: usize, i: usize) -> [BabyBear; 8] {
        self.levels[level]
            .get(i)
            .copied()
            .unwrap_or(self.empty_roots[level])
    }
    pub fn root8(&self) -> Faithful8 {
        Faithful8::from_root8(exact_cap_root8(self.node(self.depth, 0)))
    }
    pub const fn depth(&self) -> usize {
        self.depth
    }
    pub fn position_of(&self, slot: u32) -> Option<usize> {
        let key = u64::from(slot) + 1;
        let i = self.entries.partition_point(|x| x.key() < key);
        (i < self.entries.len() && self.entries[i].key() == key).then_some(i)
    }
    pub fn live_position_of(&self, slot: u32) -> Option<usize> {
        let i = self.position_of(slot)?;
        matches!(self.entries[i], StoredCapLeaf::Live(_)).then_some(i)
    }
    pub fn live_leaves(&self) -> Vec<ExactCapLeaf> {
        self.entries
            .iter()
            .filter_map(|x| match x {
                StoredCapLeaf::Live(v) => Some(*v),
                _ => None,
            })
            .collect()
    }
    pub fn prove_membership(&self, position: usize) -> Option<(Vec<[BabyBear; 8]>, Vec<u8>)> {
        if position >= self.entries.len() {
            return None;
        }
        let mut siblings = Vec::with_capacity(self.depth);
        let mut directions = Vec::with_capacity(self.depth);
        let mut i = position;
        for level in 0..self.depth {
            siblings.push(self.node(level, i ^ 1));
            directions.push((i & 1) as u8);
            i >>= 1;
        }
        Some((siblings, directions))
    }
    pub fn membership_witness(&self, slot: u32) -> Option<ExactCapMembershipWitness> {
        let i = self.live_position_of(slot)?;
        let StoredCapLeaf::Live(leaf) = self.entries[i] else {
            return None;
        };
        let (siblings, directions) = self.prove_membership(i)?;
        Some(ExactCapMembershipWitness {
            leaf,
            siblings,
            directions,
            root: self.root8().limbs(),
        })
    }
    pub fn remove_witness(&self, slot: u32) -> Option<ExactCapRemoveWitness> {
        let w = self.membership_witness(slot)?;
        let new_root = recompose_exact_cap8(exact_cap_empty_leaf8(), &w.siblings, &w.directions);
        Some(ExactCapRemoveWitness {
            removed: w.leaf,
            siblings: w.siblings,
            directions: w.directions,
            old_root: w.root,
            new_root,
        })
    }
    pub fn insert_witness(&self, new_leaf: ExactCapLeaf) -> Option<ExactCapInsertWitness> {
        if self.position_of(new_leaf.slot).is_some() {
            return None;
        }
        let key = u64::from(new_leaf.slot) + 1;
        let succ = self.entries.partition_point(|x| x.key() <= key);
        if succ == 0 || succ >= self.entries.len() {
            return None;
        }
        let mut leaves = self.live_leaves();
        leaves.push(new_leaf);
        let tombs: Vec<u32> = self
            .entries
            .iter()
            .filter_map(|x| match x {
                StoredCapLeaf::Tombstone(v) => Some(*v),
                _ => None,
            })
            .collect();
        let after = Self::new_with_tombstones(leaves, &tombs, self.depth);
        let w = after.membership_witness(new_leaf.slot)?;
        Some(ExactCapInsertWitness {
            new_leaf,
            predecessor_key: self.entries[succ - 1].key(),
            successor_key: self.entries[succ].key(),
            siblings: w.siblings,
            directions: w.directions,
            old_root: self.root8().limbs(),
            new_root: w.root,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactCapMembershipWitness {
    pub leaf: ExactCapLeaf,
    pub siblings: Vec<[BabyBear; 8]>,
    pub directions: Vec<u8>,
    pub root: [BabyBear; 8],
}
impl ExactCapMembershipWitness {
    pub fn recomposes(&self) -> bool {
        recompose_exact_cap8(self.leaf.digest8(), &self.siblings, &self.directions) == self.root
    }
    pub fn target_is(&self, target: &[u8; 32]) -> bool {
        &self.leaf.target == target
    }
    pub fn breadstuff_is(&self, token: Option<&[u8; 32]>) -> bool {
        self.leaf.breadstuff.as_ref() == token
    }
    pub fn permits(&self, bit: u32) -> bool {
        self.leaf.mask & bit == bit
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactCapInsertWitness {
    pub new_leaf: ExactCapLeaf,
    pub predecessor_key: u64,
    pub successor_key: u64,
    pub siblings: Vec<[BabyBear; 8]>,
    pub directions: Vec<u8>,
    pub old_root: [BabyBear; 8],
    pub new_root: [BabyBear; 8],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactCapRemoveWitness {
    pub removed: ExactCapLeaf,
    pub siblings: Vec<[BabyBear; 8]>,
    pub directions: Vec<u8>,
    pub old_root: [BabyBear; 8],
    pub new_root: [BabyBear; 8],
}

pub fn recompose_exact_cap8(
    mut current: [BabyBear; 8],
    siblings: &[[BabyBear; 8]],
    directions: &[u8],
) -> [BabyBear; 8] {
    assert_eq!(siblings.len(), directions.len());
    for (sibling, direction) in siblings.iter().zip(directions) {
        current = match direction {
            0 => exact_cap_node8(current, *sibling),
            1 => exact_cap_node8(*sibling, current),
            x => panic!("exact capability direction {x} is not binary"),
        };
    }
    exact_cap_root8(current)
}

pub fn empty_exact_capability_root() -> Faithful8 {
    CanonicalExactCapTree8::new(Vec::new(), EXACT_CAP_TREE_DEPTH).root8()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cap_root::{fold_bytes32, slot_hash};
    const P: u32 = 2_013_265_921;
    const DEPTH: usize = 5;

    fn alias() -> ([u8; 32], [u8; 32]) {
        let a = [0; 32];
        let mut b = [0; 32];
        b[..4].copy_from_slice(&P.to_le_bytes());
        (a, b)
    }
    fn leaf(slot: u32, target: [u8; 32], bread: Option<[u8; 32]>) -> ExactCapLeaf {
        ExactCapLeaf::new(slot, target, ExactCapAuth::Signature, u32::MAX, None, bread)
    }
    #[test]
    fn old_target_and_token_aliases_are_separated() {
        let (a, b) = alias();
        assert_eq!(fold_bytes32(&a), fold_bytes32(&b));
        assert_ne!(leaf(7, a, None).digest8(), leaf(7, b, None).digest8());
        assert_ne!(
            leaf(7, [9; 32], Some(a)).digest8(),
            leaf(7, [9; 32], Some(b)).digest8()
        );
        assert_ne!(
            leaf(7, [9; 32], None).digest8(),
            leaf(7, [9; 32], Some([0; 32])).digest8()
        );
    }
    #[test]
    fn old_slot_alias_is_separated_and_duplicates_refuse() {
        assert_eq!(slot_hash(0), slot_hash(P));
        let a = CanonicalExactCapTree8::new(vec![leaf(0, [3; 32], None)], DEPTH).root8();
        let b = CanonicalExactCapTree8::new(vec![leaf(P, [3; 32], None)], DEPTH).root8();
        assert_ne!(a, b);
        assert_eq!(
            CanonicalExactCapTree8::try_new(
                vec![leaf(7, [3; 32], None), leaf(7, [3; 32], None)],
                DEPTH
            ),
            Err(ExactCapTreeError::DuplicateSlot(7))
        );
    }
    #[test]
    fn membership_and_tombstone_remove_recompose() {
        let a = leaf(3, [1; 32], None);
        let b = leaf(7, [2; 32], Some([4; 32]));
        let tree = CanonicalExactCapTree8::new(vec![a, b], DEPTH);
        let w = tree.membership_witness(7).unwrap();
        assert!(w.recomposes());
        assert!(w.target_is(&[2; 32]));
        let rm = tree.remove_witness(7).unwrap();
        let rebuilt = CanonicalExactCapTree8::new_with_tombstones(vec![a], &[7], DEPTH);
        assert_eq!(rm.new_root, rebuilt.root8().limbs());
        assert!(rebuilt.membership_witness(7).is_none());
    }
    #[test]
    fn custom_vk_expiry_and_domains_bind() {
        let (a, b) = alias();
        let x = ExactCapLeaf::new(1, [8; 32], ExactCapAuth::Custom(a), 1, None, None);
        let y = ExactCapLeaf::new(1, [8; 32], ExactCapAuth::Custom(b), 1, None, None);
        let z = ExactCapLeaf::new(1, [8; 32], ExactCapAuth::Custom(a), 1, Some(0), None);
        assert_ne!(x.digest8(), y.digest8());
        assert_ne!(x.digest8(), z.digest8());
        let zero = [BabyBear::ZERO; 8];
        assert_ne!(exact_cap_node8(zero, zero), exact_cap_root8(zero));
    }
}
