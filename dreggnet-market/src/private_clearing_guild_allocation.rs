//! Guild/raid allocation policy driven by a verified private Bazaar clearing.
//!
//! The private clearing selects one market identity. This module joins that
//! winner to an exact, deployment-pinned ordered guild roster mapping identities
//! to real game character cells, and derives a consequence tag committing the
//! full roster, reward, private statement/root, selected member, and settlement
//! turn. The resulting [`PrivateClearingConsequenceGate`] can drive any one-turn
//! quest/raid reward; the integration test uses the real executor-backed hero XP
//! transition.
//!
//! Roster order is intentionally significant. A relying deployment retains the
//! expected roster digest independently; reordering members, substituting a
//! character cell, or changing an identity fails before a game closure can run.

use std::collections::BTreeSet;

use dregg_app_framework::CellId;
use dreggnet_offerings::DreggIdentity;

use crate::private_clearing_consequence::{
    PrivateClearingConsequenceGate, PrivateClearingConsequenceSource, PrivateClearingConsequenceTag,
};

const ROSTER_DOMAIN: &str = "dreggnet-market/private-clearing-guild-roster/v1";
const ALLOCATION_DOMAIN: &str = "dreggnet-market/private-clearing-guild-allocation/v1";
pub const MAX_GUILD_MEMBERS: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GuildMember {
    pub actor: DreggIdentity,
    pub character_cell: CellId,
}

impl GuildMember {
    pub fn new(actor: DreggIdentity, character_cell: CellId) -> Self {
        Self {
            actor,
            character_cell,
        }
    }
}

/// Validated ordered roster and its faithful digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GuildRoster {
    ordered_members: Vec<GuildMember>,
    digest: [u8; 32],
}

impl GuildRoster {
    pub fn new(
        ordered_members: Vec<GuildMember>,
    ) -> Result<Self, PrivateClearingGuildAllocationError> {
        if ordered_members.is_empty() {
            return Err(PrivateClearingGuildAllocationError::EmptyRoster);
        }
        if ordered_members.len() > MAX_GUILD_MEMBERS {
            return Err(PrivateClearingGuildAllocationError::RosterTooLarge(
                ordered_members.len(),
            ));
        }
        let mut actors = BTreeSet::new();
        let mut cells = BTreeSet::new();
        for (index, member) in ordered_members.iter().enumerate() {
            if member.actor.0.is_empty() {
                return Err(PrivateClearingGuildAllocationError::EmptyActor { index });
            }
            if !actors.insert(member.actor.0.clone()) {
                return Err(PrivateClearingGuildAllocationError::DuplicateActor { index });
            }
            if !cells.insert(member.character_cell) {
                return Err(PrivateClearingGuildAllocationError::DuplicateCharacterCell { index });
            }
        }
        let digest = roster_digest(&ordered_members);
        Ok(Self {
            ordered_members,
            digest,
        })
    }

    pub fn ordered_members(&self) -> &[GuildMember] {
        &self.ordered_members
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub fn member_for(&self, actor: &DreggIdentity) -> Option<&GuildMember> {
        self.ordered_members
            .iter()
            .find(|member| &member.actor == actor)
    }
}

/// Product-owned reward name plus exact amount. The game consumer interprets
/// `kind`; both fields bind into the allocation tag before execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GuildReward {
    pub kind: String,
    pub amount: u64,
}

impl GuildReward {
    pub fn new(
        kind: impl Into<String>,
        amount: u64,
    ) -> Result<Self, PrivateClearingGuildAllocationError> {
        let kind = kind.into();
        if kind.is_empty() {
            return Err(PrivateClearingGuildAllocationError::EmptyRewardKind);
        }
        if amount == 0 {
            return Err(PrivateClearingGuildAllocationError::ZeroReward);
        }
        Ok(Self { kind, amount })
    }
}

/// Fully bound allocation plan. It is pure policy; game mutation remains in the
/// generic consequence gate's one-turn callback.
#[derive(Clone, Debug)]
pub struct PrivateClearingGuildAllocation {
    source: PrivateClearingConsequenceSource,
    roster: GuildRoster,
    selected_index: usize,
    reward: GuildReward,
    allocation_digest: [u8; 32],
    consequence_tag: PrivateClearingConsequenceTag,
}

impl PrivateClearingGuildAllocation {
    /// Build only against the independently pinned roster digest. The verified
    /// private winner must occur exactly once (roster validation already forbids
    /// duplicates), and selects that member's exact character cell.
    pub fn new(
        source: PrivateClearingConsequenceSource,
        roster: GuildRoster,
        expected_roster_digest: [u8; 32],
        reward: GuildReward,
    ) -> Result<Self, PrivateClearingGuildAllocationError> {
        if roster.digest != expected_roster_digest {
            return Err(PrivateClearingGuildAllocationError::RosterDigestMismatch);
        }
        let selected_index = roster
            .ordered_members
            .iter()
            .position(|member| &member.actor == source.winner())
            .ok_or(PrivateClearingGuildAllocationError::WinnerNotInRoster)?;
        let allocation_digest = allocation_digest(&source, &roster, selected_index, &reward);
        Ok(Self {
            source,
            roster,
            selected_index,
            reward,
            allocation_digest,
            consequence_tag: PrivateClearingConsequenceTag(allocation_digest),
        })
    }

    pub fn roster(&self) -> &GuildRoster {
        &self.roster
    }

    pub fn selected_member(&self) -> &GuildMember {
        &self.roster.ordered_members[self.selected_index]
    }

    pub fn reward(&self) -> &GuildReward {
        &self.reward
    }

    pub const fn allocation_digest(&self) -> [u8; 32] {
        self.allocation_digest
    }

    pub const fn consequence_tag(&self) -> PrivateClearingConsequenceTag {
        self.consequence_tag
    }

    /// A fresh one-shot/recoverable gate for this exact allocation. Durable
    /// callers restore consumed ids or use target-engine recovery before apply.
    pub fn consequence_gate(&self) -> PrivateClearingConsequenceGate {
        PrivateClearingConsequenceGate::new(
            self.selected_member().character_cell,
            self.source.clone(),
            self.consequence_tag,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateClearingGuildAllocationError {
    EmptyRoster,
    RosterTooLarge(usize),
    EmptyActor { index: usize },
    DuplicateActor { index: usize },
    DuplicateCharacterCell { index: usize },
    RosterDigestMismatch,
    WinnerNotInRoster,
    EmptyRewardKind,
    ZeroReward,
}

impl std::fmt::Display for PrivateClearingGuildAllocationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private clearing guild allocation refused: {self:?}")
    }
}

impl std::error::Error for PrivateClearingGuildAllocationError {}

fn roster_digest(ordered_members: &[GuildMember]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(ROSTER_DOMAIN);
    hasher.update(&(ordered_members.len() as u64).to_be_bytes());
    for member in ordered_members {
        hasher.update(&(member.actor.0.len() as u64).to_be_bytes());
        hasher.update(member.actor.0.as_bytes());
        hasher.update(&member.character_cell.0);
    }
    *hasher.finalize().as_bytes()
}

fn allocation_digest(
    source: &PrivateClearingConsequenceSource,
    roster: &GuildRoster,
    selected_index: usize,
    reward: &GuildReward,
) -> [u8; 32] {
    let statement = source.statement();
    let selected = &roster.ordered_members[selected_index];
    let mut hasher = blake3::Hasher::new_derive_key(ALLOCATION_DOMAIN);
    hasher.update(&roster.digest);
    hasher.update(&(selected_index as u64).to_be_bytes());
    hasher.update(&(reward.kind.len() as u64).to_be_bytes());
    hasher.update(reward.kind.as_bytes());
    hasher.update(&reward.amount.to_be_bytes());
    hasher.update(&statement.session.to_be_bytes());
    hasher.update(&statement.rule.to_be_bytes());
    for lane in statement.order_root {
        hasher.update(&lane.to_be_bytes());
    }
    hasher.update(&statement.p_star.to_be_bytes());
    hasher.update(&statement.v_star.to_be_bytes());
    hasher.update(&(source.winner().0.len() as u64).to_be_bytes());
    hasher.update(source.winner().0.as_bytes());
    hasher.update(&selected.character_cell.0);
    hasher.update(&source.settlement_turn_hash());
    *hasher.finalize().as_bytes()
}
