//! Robigalia-inspired designs mapped to dregg's distributed capability runtime.
//!
//! This crate provides three clusters of userspace primitives carried over
//! from the Robigalia capability-secure OS design and adapted to dregg's
//! distributed runtime:
//!
//! * [`directory`] — [`DirectoryCell`] (capability-secure versioned directory
//!   cells), [`ScopedIntentPool`] (intents bounded by directory membership),
//!   [`MetaDirectory`] (registry-of-registries / yellow pages),
//!   [`DirectoryFactory`] (constrained directory creation) and
//!   [`TopicSubscriptionManager`] (gossip-topic audience bounding).
//! * [`vfs`] — `Volume` / `Blob` / `Directory` triple modeling Robigalia's
//!   VFS as a userspace library that decomposes into existing Effect VM
//!   effects (`NoteCreate`, `NoteSpend`, `SetField`, balance accounting).
//! * [`factory`] — [`directory_factory_descriptor`] returning a
//!   `dregg_cell::factory::FactoryDescriptor` shape for the directory-cell
//!   pattern, so apps can `createFromFactory` a directory and have the
//!   executor enforce the slot caveats on every turn.
//!
//! The earlier DFA routing module that used to live here has been promoted
//! to the canonical [`dregg_dfa`] crate (see `DFA-RATIONALIZATION-DESIGN.md`).
//! This crate now reuses real workspace types (`dregg_types::FederationId`,
//! `dregg_types::CellId`) rather than the stub identifiers it once carried.
//!
//! [`directory`]: crate::directory
//! [`vfs`]: crate::vfs
//! [`factory`]: crate::factory
//! [`dregg_dfa`]: https://docs.rs/dregg-dfa
//! [`DirectoryCell`]: crate::directory::DirectoryCell
//! [`ScopedIntentPool`]: crate::directory::ScopedIntentPool
//! [`MetaDirectory`]: crate::directory::MetaDirectory
//! [`DirectoryFactory`]: crate::directory::DirectoryFactory
//! [`TopicSubscriptionManager`]: crate::directory::TopicSubscriptionManager

pub mod directory;
pub mod factory;
pub mod vfs;

pub use directory::{
    AudienceBoundClaim, DirectoryCell, DirectoryEntry, DirectoryError, DirectoryFactory,
    DirectoryFactoryError, EntryKind, GossipTopic, Listing, MatchPattern, MemberId, MetaDirectory,
    ScopedIntent, ScopedIntentKind, ScopedIntentPool, ScopedPoolError, SturdyRef,
    TopicSubscriptionManager,
};
pub use factory::{DirectoryFactoryConfig, DirectorySlots, directory_factory_descriptor};
