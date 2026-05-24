//! Robigalia-inspired designs mapped to pyana's distributed capability runtime.
//!
//! This crate provides three clusters of userspace primitives carried over
//! from the Robigalia capability-secure OS design and adapted to pyana's
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
//!   `pyana_cell::factory::FactoryDescriptor` shape for the directory-cell
//!   pattern, so apps can `createFromFactory` a directory and have the
//!   executor enforce the slot caveats on every turn.
//!
//! The earlier DFA routing module that used to live here has been promoted
//! to the canonical [`pyana_dfa`] crate (see `DFA-RATIONALIZATION-DESIGN.md`).
//! This crate now reuses real workspace types (`pyana_types::FederationId`,
//! `pyana_types::CellId`) rather than the stub identifiers it once carried.
//!
//! [`directory`]: crate::directory
//! [`vfs`]: crate::vfs
//! [`factory`]: crate::factory
//! [`pyana_dfa`]: https://docs.rs/pyana-dfa
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
