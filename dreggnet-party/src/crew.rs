//! # `crew` — THE AWAY TEAM: one identity, three seats, braided.
//!
//! Three real organs in this workspace each had their own idea of "a seat", and nothing
//! joined them:
//!
//! | organ | its "seat" | what it knew |
//! |-------|-----------|--------------|
//! | [`crate::Party`] | [`crate::Seat`] — a real player-cell + custody keypair, indexed by [`Role`] | caps, ledger identity |
//! | [`collective_choice`] (via [`dungeon_on_dregg::collective`]) | an electorate entry — a custody PUBLIC KEY | who may ballot |
//! | [`dungeon_on_dregg::private_raid`] | a bare `usize` 0..4 in `roles[4]` | **nothing at all** |
//!
//! The first two were already welded ([`crate::Seat::electorate_seat`]). The third was
//! free-floating: the private-raid statement publishes `(session, rule, input_root,
//! roles[4])` and **no identity appears anywhere in it**. A proof is a proof that *some*
//! four anonymous score-rows were optimally matched to four roles; nothing in the public
//! statement says whose rows they were, or that this crew ever agreed to them. Every
//! consumer to date closed that with HOST bookkeeping (an operation id it rechecks on
//! restart) or a host-seeded session — real, but only as good as the host's records.
//!
//! This module closes it **inside the statement**. A [`CrewCharter`] fixes the crew's
//! identities in a canonical seat order; each member publishes a hiding
//! [`PreferenceCommitment`] over their own private row; and the raid proof's `session` —
//! a public input the AIR binds — is *derived* from exactly that charter and those
//! commitments ([`CrewRoll::proof_session`]). Anyone holding the public roll recomputes
//! the expected session from public data alone and refuses a receipt that does not carry
//! it ([`CrewError::SessionNotThisCrew`]). Seat `i` of `roles[4]` therefore denotes
//! `charter.members()[i]` and no one else, with no host state in the loop.
//!
//! ## The braid
//!
//! ```text
//!   PartyLobby / Party ──► CrewCharter ──► CrewRoll ──(hiding proof)──► CrewRoles ──► AwayTeam
//!        who is here        canonical      per-member                    identity      caps + ballots
//!                           seat order     commitments                   ↦ Role        + loot
//! ```
//!
//! * **A crew forms.** [`CrewCharter::from_lobby`] / [`CrewCharter::from_party`] — the
//!   braid is reachable FROM a party, not a standalone demo.
//! * **Roles assign from hidden preferences.** [`CrewRoll::assign_roles`] proves the
//!   globally suitability-maximal admissible permutation over the crew's private rows.
//!   Nobody reveals what they wanted; the result is provably the best admissible
//!   assignment; and it is bound to THIS crew.
//! * **The crew acts by capability where the seat owns it.** [`AwayTeam::act`] fires at
//!   the real executor and, when the executor refuses, names the refusal:
//!   [`OutOfRole`] carries who tried it, the role the proof gave them, the role that
//!   actually owns the move, and the executor's own reason. The host never pre-checks.
//! * **The crew acts by collective decision where it matters.** [`AwayTeam::open_steer`]
//!   / [`AwayTeam::steer_vote`] / [`AwayTeam::steer`] — a signed quorum ballot on the real
//!   [`collective_choice`] engine, resolving into ONE real party-world turn. Sub-quorum
//!   moves nothing.
//! * **Loot splits on the ledger.** [`AwayTeam::split_loot`] — a `WriteOnce` ledger fact.
//!
//! ## Two role vocabularies, one bijection
//!
//! The party names roles Tank/Scout/Mage/Healer; the fixed Lean raid relation names them
//! Bulwark/Striker/Mender/Pathfinder. They are the same four jobs, so
//! [`Role::raid_role_index`] / [`Role::from_raid_role_index`] pin one total bijection
//! (front line, damage, mend, path) and every matrix column / published role index passes
//! through it. Preferences are authored in the PARTY vocabulary; the crew translates.
//!
//! ## Honest scope (named, not hidden)
//!
//! * The assignment producer is still **Tier-1**: whoever calls [`CrewRoll::assign_roles`]
//!   holds every member's plaintext row. The commitments bind each row to its author at
//!   submission time and bind the whole set into the proof's session, so a producer cannot
//!   swap in a row for a member whose commitment is already public *without that member
//!   being able to open theirs and show the mismatch* — but nothing here proves the
//!   producer used the committed rows. Distributed private-input assembly is the frontier.
//! * The relation is optimal **for the submitted matrix**, and the matrix is SELF-REPORTED
//!   here, so this is a preference-revelation mechanism and **not strategyproof**: a member
//!   who scores one role `3` and the rest `0` bids harder for it than one who reports
//!   honestly. (Uniform lying is self-defeating — an all-`3` crew makes every assignment
//!   tie and the lexicographic tie-break decides.) The fix is not in this module: a
//!   deployment sources scores from VERIFIED history (completion records, gear, achievement
//!   receipts) instead of a self-report, and the commitment binds whichever source is used.
//! * The session binding is a **public-statement** binding, not an executor
//!   `ObservedFieldEquals` between the raid receipt and the party's cells. The proof and
//!   the party world remain separately verified records; no cross-world atomicity is
//!   claimed.
//! * The underlying relation inherits its verifier's assurance level (the descriptor's
//!   documented modular-to-integer `OptimalLex` bridge is a named proof gate); this module
//!   consumes it and does not promote it.

use crate::lobby::PartyLobby;
use crate::{Party, PartyFormationError, PartyMove, Role, UnseatedIdentity};

#[cfg(feature = "private-role-assignment")]
use crate::{ActOutcome, PartyFork};
#[cfg(feature = "private-role-assignment")]
use dungeon_on_dregg::private_raid::{
    RAID_ROLES, RAID_SEATS, RaidAssignmentError, RaidAssignmentReceipt, RaidAssignmentSession,
    RaidRole, prove_private_assignment,
};

/// The crew size the fixed Lean raid relation is authored for.
pub const CREW_SEATS: usize = 4;

/// The BabyBear prime the raid statement's `session` public input lives in.
const BABYBEAR_P: u64 = 2_013_265_921;

/// `blake3::derive_key` context for the charter's canonical root.
const CHARTER_CONTEXT: &str = "dregg.party.crew.charter.v1";
/// `blake3::derive_key` context for the crew-bound raid proof session.
const SESSION_CONTEXT: &str = "dregg.party.crew.private-role-assignment.session.v1";
/// `blake3::derive_key` context for one member's hidden-preference commitment.
const PREFERENCE_CONTEXT: &str = "dregg.party.crew.hidden-preference.commitment.v1";

/// Maximum byte length of a crew member identity (matches the lobby's bound, so a
/// lobby roster always lowers into a charter).
pub const MAX_CREW_IDENTITY_BYTES: usize = crate::lobby::MAX_LOBBY_IDENTITY_BYTES;
/// Maximum byte length of a mission label.
pub const MAX_CREW_MISSION_BYTES: usize = crate::lobby::MAX_LOBBY_SESSION_BYTES;

// ── The two role vocabularies ────────────────────────────────────────────────────

impl Role {
    /// This role's column in the fixed Lean raid relation's role roster
    /// (`Bulwark=0, Striker=1, Mender=2, Pathfinder=3`). The bijection is by JOB:
    /// Tank↔Bulwark (front line), Mage↔Striker (damage), Healer↔Mender (mend),
    /// Scout↔Pathfinder (path).
    pub const fn raid_role_index(self) -> u8 {
        match self {
            Role::Tank => 0,
            Role::Mage => 1,
            Role::Healer => 2,
            Role::Scout => 3,
        }
    }

    /// The inverse of [`Role::raid_role_index`] — the party role a published raid role
    /// index denotes. `None` outside the fixed four-role roster.
    pub const fn from_raid_role_index(index: u8) -> Option<Role> {
        match index {
            0 => Some(Role::Tank),
            1 => Some(Role::Mage),
            2 => Some(Role::Healer),
            3 => Some(Role::Scout),
            _ => None,
        }
    }
}

#[cfg(feature = "private-role-assignment")]
impl From<RaidRole> for Role {
    fn from(role: RaidRole) -> Role {
        match role {
            RaidRole::Bulwark => Role::Tank,
            RaidRole::Striker => Role::Mage,
            RaidRole::Mender => Role::Healer,
            RaidRole::Pathfinder => Role::Scout,
        }
    }
}

#[cfg(feature = "private-role-assignment")]
impl From<Role> for RaidRole {
    fn from(role: Role) -> RaidRole {
        match role {
            Role::Tank => RaidRole::Bulwark,
            Role::Mage => RaidRole::Striker,
            Role::Healer => RaidRole::Mender,
            Role::Scout => RaidRole::Pathfinder,
        }
    }
}

impl PartyMove {
    /// The ONE role that holds the capabilities this move touches — the inverse of
    /// [`Role::move_of`]. Used to NAME an out-of-role refusal; the executor, not this
    /// function, decides whether a move lands.
    pub const fn sanctioned_role(self) -> Role {
        match self {
            PartyMove::GuardFront => Role::Tank,
            PartyMove::DisarmLock => Role::Scout,
            PartyMove::CastWard => Role::Mage,
            PartyMove::Rally => Role::Healer,
        }
    }
}

// ── The charter — the crew's canonical seat order ────────────────────────────────

/// **A crew charter** — the four authenticated identities on this away mission, in a
/// CANONICAL seat order.
///
/// Seat order is the members' identities in ascending byte order, so any observer holding
/// the identity SET recomputes the same seat numbering with no journal to replay and no
/// host to trust. Seat `i` of a private-raid statement's `roles[4]` is
/// [`members`](CrewCharter::members)`[i]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrewCharter {
    mission: String,
    members: [String; CREW_SEATS],
}

impl CrewCharter {
    /// Form a charter over four distinct identities. Input order is irrelevant — the
    /// members are canonicalized into ascending byte order.
    pub fn form(
        mission: impl Into<String>,
        members: [String; CREW_SEATS],
    ) -> Result<CrewCharter, CrewError> {
        let mission = mission.into();
        if mission.is_empty() || mission.len() > MAX_CREW_MISSION_BYTES {
            return Err(CrewError::InvalidMission);
        }
        for identity in &members {
            if identity.is_empty() || identity.len() > MAX_CREW_IDENTITY_BYTES {
                return Err(CrewError::InvalidIdentity(identity.clone()));
            }
        }
        let mut members = members;
        members.sort();
        for pair in members.windows(2) {
            if pair[0] == pair[1] {
                return Err(CrewError::DuplicateIdentity(pair[0].clone()));
            }
        }
        Ok(CrewCharter { mission, members })
    }

    /// Form a charter from a live [`PartyLobby`]'s occupied roster.
    ///
    /// The lobby's role CLAIMS are the seating protocol only — a crew's actual roles come
    /// from the proof ([`CrewRoll::assign_roles`]) and routinely differ from what a player
    /// clicked. The mission label is the lobby's session id.
    pub fn from_lobby(lobby: &PartyLobby) -> Result<CrewCharter, CrewError> {
        let mut members: Vec<String> = Vec::with_capacity(CREW_SEATS);
        for role in Role::ALL {
            let seat = lobby.seat(role).ok_or(CrewError::IncompleteRoster {
                occupied: lobby.occupied_count(),
            })?;
            members.push(seat.identity().to_string());
        }
        let members: [String; CREW_SEATS] =
            members
                .try_into()
                .map_err(|_| CrewError::IncompleteRoster {
                    occupied: lobby.occupied_count(),
                })?;
        CrewCharter::form(lobby.session_id().to_string(), members)
    }

    /// Form a charter from an already-seated [`Party`] — the braid reached from live play
    /// (the same four identities re-deciding who does what).
    pub fn from_party(mission: impl Into<String>, party: &Party) -> Result<CrewCharter, CrewError> {
        let members: Vec<String> = party
            .seats()
            .iter()
            .map(|seat| seat.name().to_string())
            .collect();
        let occupied = members.len();
        let members: [String; CREW_SEATS] = members
            .try_into()
            .map_err(|_| CrewError::IncompleteRoster { occupied })?;
        CrewCharter::form(mission, members)
    }

    /// The mission label.
    pub fn mission(&self) -> &str {
        &self.mission
    }

    /// The crew in canonical seat order.
    pub fn members(&self) -> &[String; CREW_SEATS] {
        &self.members
    }

    /// This identity's crew seat, if it is on the crew.
    pub fn seat_of(&self, identity: &str) -> Option<usize> {
        self.members.iter().position(|m| m == identity)
    }

    /// The charter's domain-separated root over the mission and the canonical roster.
    pub fn root(&self) -> [u8; 32] {
        let mut material = Vec::new();
        push_bounded(&mut material, self.mission.as_bytes());
        for identity in &self.members {
            push_bounded(&mut material, identity.as_bytes());
        }
        blake3::derive_key(CHARTER_CONTEXT, &material)
    }
}

// ── Hidden preferences ───────────────────────────────────────────────────────────

/// **One crew member's PRIVATE role preference** — how well they rate themselves in each
/// party [`Role`] (`0..=3`, the bound the fixed relation checks) and which roles they are
/// willing to take at all. Never published; only its [`commitment`](Self::commitment) is.
///
/// The `nonce` is LOAD-BEARING. The preference space is `4^4 · 2^4` — small enough to
/// brute-force a commitment over — so an unblinded row is not hidden at all. A zero nonce
/// is refused. The member's client generates it; this crate does not, so no crate here has
/// to be trusted with a player's entropy.
#[derive(Clone, PartialEq, Eq)]
pub struct HiddenPreference {
    /// Indexed by [`Role::index`].
    scores: [u8; CREW_SEATS],
    /// Indexed by [`Role::index`].
    willing: [bool; CREW_SEATS],
    nonce: [u8; 32],
}

impl std::fmt::Debug for HiddenPreference {
    /// Redacted: a preference that showed up in a log would not be private.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("HiddenPreference(<sealed>)")
    }
}

impl HiddenPreference {
    /// A member's private row. `scores` and `willing` are indexed by [`Role::index`]
    /// (Tank, Scout, Mage, Healer).
    pub fn new(
        scores: [u8; CREW_SEATS],
        willing: [bool; CREW_SEATS],
        nonce: [u8; 32],
    ) -> Result<HiddenPreference, CrewError> {
        for (index, &score) in scores.iter().enumerate() {
            if score > 3 {
                return Err(CrewError::ScoreOutOfRange {
                    role: Role::ALL[index],
                    score,
                });
            }
        }
        if !willing.iter().any(|&w| w) {
            return Err(CrewError::NoWillingRole);
        }
        if nonce == [0u8; 32] {
            return Err(CrewError::UnblindedPreference);
        }
        Ok(HiddenPreference {
            scores,
            willing,
            nonce,
        })
    }

    /// This member's private score for `role`.
    pub fn score_for(&self, role: Role) -> u8 {
        self.scores[role.index()]
    }

    /// Whether this member will take `role` at all.
    pub fn willing_to(&self, role: Role) -> bool {
        self.willing[role.index()]
    }

    /// The hiding commitment this member publishes: `H(context ‖ identity ‖ scores ‖
    /// willing ‖ nonce)`. Binding the identity stops a row being re-attributed to another
    /// member.
    pub fn commitment(&self, identity: &str) -> PreferenceCommitment {
        let mut material = Vec::new();
        push_bounded(&mut material, identity.as_bytes());
        material.extend_from_slice(&self.scores);
        material.extend(self.willing.iter().map(|&w| u8::from(w)));
        material.extend_from_slice(&self.nonce);
        PreferenceCommitment(blake3::derive_key(PREFERENCE_CONTEXT, &material))
    }
}

/// One member's published hiding commitment to their [`HiddenPreference`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PreferenceCommitment([u8; 32]);

impl PreferenceCommitment {
    /// The raw commitment bytes (a public value).
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Rebuild a commitment received over the wire.
    pub const fn from_bytes(bytes: [u8; 32]) -> PreferenceCommitment {
        PreferenceCommitment(bytes)
    }
}

// ── The roll — charter + commitments, and THE session binding ────────────────────

/// **The crew roll** — the charter plus each member's published preference commitment, in
/// charter seat order. This is the entire PUBLIC input to role assignment, and the thing
/// the raid proof's `session` is derived from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrewRoll {
    charter: CrewCharter,
    commitments: [PreferenceCommitment; CREW_SEATS],
}

impl CrewRoll {
    /// A roll from a charter and the members' published commitments (charter seat order).
    pub fn new(charter: CrewCharter, commitments: [PreferenceCommitment; CREW_SEATS]) -> CrewRoll {
        CrewRoll {
            charter,
            commitments,
        }
    }

    /// Compute the roll a producer holding every member's row would publish: each
    /// member's commitment under their own charter identity. `preferences` is indexed by
    /// CHARTER SEAT.
    pub fn from_preferences(
        charter: CrewCharter,
        preferences: &[HiddenPreference; CREW_SEATS],
    ) -> CrewRoll {
        let commitments =
            std::array::from_fn(|seat| preferences[seat].commitment(&charter.members()[seat]));
        CrewRoll {
            charter,
            commitments,
        }
    }

    /// The crew this roll is for.
    pub fn charter(&self) -> &CrewCharter {
        &self.charter
    }

    /// The published commitments, in charter seat order.
    pub fn commitments(&self) -> &[PreferenceCommitment; CREW_SEATS] {
        &self.commitments
    }

    /// **THE BINDING.** The private-raid statement's `session` public input for this exact
    /// crew: a canonical nonzero BabyBear element derived from the charter root and the
    /// ordered commitments.
    ///
    /// This is what makes an anonymous `roles[4]` mean something. A receipt whose statement
    /// carries a different `session` is not about this crew, and
    /// [`CrewRoll::accept`] refuses it ([`CrewError::SessionNotThisCrew`]) — recomputable by
    /// anyone from public data, with no host records in the loop.
    pub fn proof_session(&self) -> u32 {
        let mut material = Vec::new();
        material.extend_from_slice(&self.charter.root());
        for commitment in &self.commitments {
            material.extend_from_slice(commitment.as_bytes());
        }
        let digest = blake3::derive_key(SESSION_CONTEXT, &material);
        let mut low = [0u8; 8];
        low.copy_from_slice(&digest[..8]);
        // Nonzero and canonical: `0` stays available as an unmistakable "no session".
        ((u64::from_le_bytes(low) % (BABYBEAR_P - 1)) + 1) as u32
    }
}

#[cfg(feature = "private-role-assignment")]
impl CrewRoll {
    /// **Assign the crew's roles from their hidden preferences.** Produces the real
    /// Lean-emitted HidingFri receipt over the crew's private suitability/admissibility
    /// matrix, verifies it, checks it is bound to THIS crew, and mints [`CrewRoles`].
    ///
    /// `preferences` is indexed by CHARTER SEAT and each row must match the commitment
    /// this roll published for that member ([`CrewError::PreferenceNotCommitted`]) — a
    /// producer cannot quietly substitute a row for a member whose commitment is public.
    ///
    /// The published roles are a permutation, admissible for every member's stated
    /// willingness, globally suitability-maximizing over all 24 assignments, and
    /// lexicographic on ties. Nobody's scores are revealed.
    pub fn assign_roles(
        &self,
        preferences: &[HiddenPreference; CREW_SEATS],
    ) -> Result<CrewRoles, CrewError> {
        let receipt = self.prove_roles(preferences)?;
        self.accept(&receipt)
    }

    /// The PRODUCER half of [`CrewRoll::assign_roles`] — mint the transportable receipt
    /// without landing it, so the proof can travel to the consumers who verify it.
    pub fn prove_roles(
        &self,
        preferences: &[HiddenPreference; CREW_SEATS],
    ) -> Result<RaidAssignmentReceipt, CrewError> {
        const _: () = assert!(CREW_SEATS == RAID_SEATS && CREW_SEATS == RAID_ROLES);

        let mut scores = [[0u8; RAID_ROLES]; RAID_SEATS];
        let mut admissible = [[false; RAID_ROLES]; RAID_SEATS];
        for seat in 0..CREW_SEATS {
            let preference = &preferences[seat];
            let identity = &self.charter.members()[seat];
            if preference.commitment(identity) != self.commitments[seat] {
                return Err(CrewError::PreferenceNotCommitted {
                    seat,
                    identity: identity.clone(),
                });
            }
            for column in 0..RAID_ROLES {
                let role = Role::from_raid_role_index(column as u8)
                    .expect("the raid role roster is exactly the party role roster");
                scores[seat][column] = preference.score_for(role);
                admissible[seat][column] = preference.willing_to(role);
            }
        }

        // `HiddenPreference::new` already bounded every score, so the only private-input
        // refusal a well-formed crew can hit is "nobody will take that job"; anything else
        // (a blinding-entropy failure) stays a proof refusal rather than being mislabelled.
        prove_private_assignment(self.proof_session(), scores, admissible).map_err(|error| {
            match error {
                RaidAssignmentError::InvalidPrivateInput(reason)
                    if reason.contains("admissible") =>
                {
                    CrewError::NoAdmissibleAssignment(reason)
                }
                other => CrewError::Proof(other.to_string()),
            }
        })
    }

    /// **The CONSUMER half** — land a transported receipt against this exact crew.
    ///
    /// Holds no private data. Refuses any receipt whose statement session is not
    /// [`CrewRoll::proof_session`] ([`CrewError::SessionNotThisCrew`]) BEFORE any proof
    /// work, then verifies the hiding proof through the pinned canonical verifier via the
    /// existing one-shot [`RaidAssignmentSession`].
    pub fn accept(&self, receipt: &RaidAssignmentReceipt) -> Result<CrewRoles, CrewError> {
        let expected = self.proof_session();
        let claimed = receipt.statement().session;
        if claimed != expected {
            return Err(CrewError::SessionNotThisCrew { expected, claimed });
        }
        let mut slot =
            RaidAssignmentSession::new(expected).map_err(|e| CrewError::Proof(e.to_string()))?;
        let assignment = slot.accept(receipt).map_err(|error| match error {
            RaidAssignmentError::SessionMismatch { expected, claimed } => {
                CrewError::SessionNotThisCrew { expected, claimed }
            }
            other => CrewError::Proof(other.to_string()),
        })?;
        let roles = assignment.roles().map(Role::from);
        Ok(CrewRoles {
            roll: self.clone(),
            session: assignment.session(),
            input_root: assignment.input_root(),
            roles,
        })
    }
}

// ── The verified assignment ──────────────────────────────────────────────────────

/// **A crew's verified role assignment** — minted only from a hiding proof that is bound
/// to this crew's roll. `roles[i]` is the role the relation gave charter seat `i`.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg(feature = "private-role-assignment")]
pub struct CrewRoles {
    roll: CrewRoll,
    session: u32,
    input_root: [u32; 8],
    roles: [Role; CREW_SEATS],
}

#[cfg(feature = "private-role-assignment")]
impl CrewRoles {
    /// The roll (charter + commitments) this assignment is bound to.
    pub fn roll(&self) -> &CrewRoll {
        &self.roll
    }

    /// The crew.
    pub fn charter(&self) -> &CrewCharter {
        self.roll.charter()
    }

    /// The verified statement session — equal to [`CrewRoll::proof_session`] by
    /// construction (that is the binding).
    pub const fn session(&self) -> u32 {
        self.session
    }

    /// The verified hiding root over the private matrix (public, reveals nothing).
    pub const fn input_root(&self) -> [u32; 8] {
        self.input_root
    }

    /// The assigned roles, in charter seat order.
    pub const fn roles(&self) -> [Role; CREW_SEATS] {
        self.roles
    }

    /// **The join.** The role the proof gave this identity — the single lookup the three
    /// former seat notions collapse into.
    pub fn role_of(&self, identity: &str) -> Option<Role> {
        self.roll.charter().seat_of(identity).map(|s| self.roles[s])
    }

    /// The member the proof put in `role`.
    pub fn identity_in(&self, role: Role) -> &str {
        let seat = self
            .roles
            .iter()
            .position(|&r| r == role)
            .expect("a verified assignment is a permutation of the four roles");
        &self.roll.charter().members()[seat]
    }

    /// The roster [`Party::muster_with_roster`] wants.
    pub fn roster(&self) -> [(Role, String); CREW_SEATS] {
        Role::ALL.map(|role| (role, self.identity_in(role).to_string()))
    }

    /// **Depart on the away mission** — muster the real cap-seated party from the
    /// proof-assigned roster. Each member's capabilities are now the role the hidden
    /// preferences earned them, and the executor referees every move against exactly that.
    pub fn depart(&self) -> Result<AwayTeam, CrewError> {
        let party = Party::muster_with_roster(self.roster()).map_err(CrewError::Formation)?;
        Ok(AwayTeam {
            roles: self.clone(),
            party,
            steering: None,
        })
    }

    /// Depart with the crew's OWN custody public keys held by the party, so a member's
    /// ballot key is not derivable from their public identity
    /// ([`Party::muster_with_custody`]). `keys` is looked up by identity; every crew
    /// member must appear.
    pub fn depart_with_custody(
        &self,
        keys: &[(String, dregg_types::PublicKey)],
    ) -> Result<AwayTeam, CrewError> {
        let mut roster: Vec<(Role, String, dregg_types::PublicKey)> =
            Vec::with_capacity(CREW_SEATS);
        for role in Role::ALL {
            let identity = self.identity_in(role).to_string();
            let key = keys
                .iter()
                .find(|(name, _)| name == &identity)
                .map(|(_, pk)| *pk)
                .ok_or_else(|| CrewError::NoCustodyKey(identity.clone()))?;
            roster.push((role, identity, key));
        }
        let roster: [(Role, String, dregg_types::PublicKey); CREW_SEATS] =
            roster.try_into().expect("length checked");
        let party = Party::muster_with_custody(roster).map_err(CrewError::Formation)?;
        Ok(AwayTeam {
            roles: self.clone(),
            party,
            steering: None,
        })
    }
}

// ── The away team ────────────────────────────────────────────────────────────────

/// **The away team** — the crew, its proof-assigned roles, and the real cap-seated party
/// world they act in. One object where an IDENTITY is simultaneously a raid seat, a
/// capability-bearing player-cell, and an elector.
#[cfg(feature = "private-role-assignment")]
pub struct AwayTeam {
    roles: CrewRoles,
    party: Party,
    steering: Option<PartyFork>,
}

#[cfg(feature = "private-role-assignment")]
impl AwayTeam {
    /// The verified role assignment this team departed under.
    pub fn roles(&self) -> &CrewRoles {
        &self.roles
    }

    /// The live party world (read-only).
    pub fn party(&self) -> &Party {
        &self.party
    }

    /// The live party world, for the party APIs this braid does not re-wrap.
    pub fn party_mut(&mut self) -> &mut Party {
        &mut self.party
    }

    /// The role the proof gave this identity.
    pub fn role_of(&self, identity: &str) -> Option<Role> {
        self.roles.role_of(identity)
    }

    /// **Act as an individual — your job is yours.** Fires `mv` as `identity` at the REAL
    /// executor and reports what the executor did. No host role-check runs first: a move
    /// outside the mover's proof-assigned role reaches the kernel, is refused for want of
    /// the capability, and comes back as [`CrewActError::OutOfRole`] carrying the
    /// executor's own reason alongside the names.
    pub fn act(&mut self, identity: &str, mv: PartyMove) -> Result<[u8; 32], CrewActError> {
        let Some(assigned) = self.roles.role_of(identity) else {
            return Err(CrewActError::NotOnTheCrew(UnseatedIdentity(
                identity.to_string(),
            )));
        };
        let outcome = self.party.act_as(identity, mv);
        match outcome {
            ActOutcome::Committed { receipt } => Ok(receipt),
            ActOutcome::Refused { reason } => {
                let sanctioned = mv.sanctioned_role();
                if sanctioned == assigned {
                    Err(CrewActError::Refused {
                        identity: identity.to_string(),
                        assigned,
                        attempted: mv,
                        executor_reason: reason,
                    })
                } else {
                    Err(CrewActError::OutOfRole(OutOfRole {
                        identity: identity.to_string(),
                        assigned,
                        attempted: mv,
                        sanctioned,
                        sanctioned_holder: self.roles.identity_in(sanctioned).to_string(),
                        executor_reason: reason,
                    }))
                }
            }
        }
    }

    /// Act in the mover's OWN proof-assigned role (the sanctioned path).
    pub fn act_in_role(&mut self, identity: &str) -> Result<[u8; 32], CrewActError> {
        let Some(assigned) = self.roles.role_of(identity) else {
            return Err(CrewActError::NotOnTheCrew(UnseatedIdentity(
                identity.to_string(),
            )));
        };
        self.act(identity, assigned.move_of())
    }

    /// **Steer collectively** — open the crew's fork ballot. Each `(label, path)` is a
    /// candidate shared move; the certified winner writes `path` into the party's fork
    /// gate as ONE real turn.
    ///
    /// ONE steer per away mission: the party's fork gate is a single `WriteOnce` slot, so
    /// a certified path is final and a second certified path could not be written even if
    /// a second steer were opened. A campaign that forks repeatedly wants a gate cell per
    /// fork; that is a party-layout change, not a braid change.
    pub fn open_steer(
        &mut self,
        question: impl Into<String>,
        options: Vec<(String, u64)>,
    ) -> Result<(), CrewError> {
        if self.steering.is_some() {
            return Err(CrewError::SteeringAlreadyOpen);
        }
        let fork = self
            .party
            .open_fork(question, options)
            .map_err(|e| CrewError::Steering(e.to_string()))?;
        self.steering = Some(fork);
        Ok(())
    }

    /// Cast `identity`'s own custody-signed ballot in the open steer.
    pub fn steer_vote(&mut self, identity: &str, option: usize) -> Result<(), CrewError> {
        let Self {
            party, steering, ..
        } = self;
        let fork = steering.as_mut().ok_or(CrewError::NoOpenSteering)?;
        let ballot = party
            .try_sign_ballot_as(fork, identity, option)
            .map_err(|e| CrewError::Steering(e.to_string()))?;
        fork.cast(&ballot)
            .map_err(|e| CrewError::Steering(e.to_string()))
    }

    /// Cast an externally produced ballot (the deployment shape: the member's secret never
    /// leaves their device, so the signature arrives already made).
    pub fn steer_cast(
        &mut self,
        ballot: &dungeon_on_dregg::collective::SignedBallot,
    ) -> Result<(), CrewError> {
        let fork = self.steering.as_mut().ok_or(CrewError::NoOpenSteering)?;
        fork.cast(ballot)
            .map_err(|e| CrewError::Steering(e.to_string()))
    }

    /// The open steer's poll id — what a member needs to sign a ballot off-box.
    pub fn steer_poll(&self) -> Option<collective_choice::PollId> {
        self.steering.as_ref().map(|fork| fork.poll())
    }

    /// The open steer's monotone tally.
    pub fn steer_tally(&self) -> Result<collective_choice::Tally, CrewError> {
        let fork = self.steering.as_ref().ok_or(CrewError::NoOpenSteering)?;
        fork.tally().map_err(|e| CrewError::Steering(e.to_string()))
    }

    /// **Resolve the steer into the world.** Quorum-certifies the winner and fires its
    /// shared move as ONE real party turn. Below quorum the `AffineLe` gate refuses the
    /// decision-turn, NOTHING fires, and the steer stays open for more ballots.
    pub fn steer(&mut self) -> Result<crate::ForkResolution, SteerError> {
        let Self {
            party, steering, ..
        } = self;
        let fork = steering.as_mut().ok_or(SteerError::NoOpenSteering)?;
        fork.resolve_into(party).map_err(|error| match error {
            crate::ForkError::BelowQuorum => SteerError::BelowQuorum,
            other => SteerError::Fork(other.to_string()),
        })
    }

    /// Commit the away mission's on-ledger loot split, in CHARTER seat order (so a share
    /// is attributed to a member, not to whichever role they happened to draw). Each share
    /// lands in a `WriteOnce` slot: a ledger fact, not a leader's promise.
    pub fn split_loot(&mut self, shares: [u64; CREW_SEATS]) -> ActOutcome {
        // The party's loot slots are indexed by ROLE; the crew's shares are indexed by
        // CHARTER SEAT. Translate through the assignment so a member's share follows the
        // member.
        let mut by_role = [0u64; CREW_SEATS];
        for (seat, share) in shares.into_iter().enumerate() {
            by_role[self.roles.roles()[seat].index()] = share;
        }
        self.party.split_loot(&by_role)
    }

    /// A member's committed loot share, read back off the shared ledger.
    pub fn loot_share(&self, identity: &str) -> Option<u64> {
        let role = self.roles.role_of(identity)?;
        Some(self.party.loot_share(role.index()))
    }
}

// ── Refusals ─────────────────────────────────────────────────────────────────────

/// **An out-of-role move, refused by name.** The executor refused it for want of a
/// capability; this records who tried what, the role the proof gave them, and whose job it
/// actually was.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutOfRole {
    /// The member who fired the move.
    pub identity: String,
    /// The role the verified assignment gave them.
    pub assigned: Role,
    /// The move they attempted.
    pub attempted: PartyMove,
    /// The role that holds the capabilities that move touches.
    pub sanctioned: Role,
    /// The crew member the assignment put in that role.
    pub sanctioned_holder: String,
    /// The REAL executor refusal — this type never invents one.
    pub executor_reason: String,
}

impl std::fmt::Display for OutOfRole {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} holds the {} seat and attempted the {} move {:?}, which is {}'s job; the executor refused it: {}",
            self.identity,
            self.assigned.name(),
            self.sanctioned.name(),
            self.attempted,
            self.sanctioned_holder,
            self.executor_reason
        )
    }
}

impl std::error::Error for OutOfRole {}

/// Why an away-team action did not commit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CrewActError {
    /// The caller holds no seat on this crew.
    NotOnTheCrew(UnseatedIdentity),
    /// The mover acted outside the role the proof gave them — a real capability refusal.
    OutOfRole(OutOfRole),
    /// The mover acted IN role and the executor still refused (an exhausted shared focus
    /// pool, a once-per-encounter contribution already spent).
    Refused {
        /// The member who fired the move.
        identity: String,
        /// The role the verified assignment gave them.
        assigned: Role,
        /// The move they attempted.
        attempted: PartyMove,
        /// The REAL executor refusal.
        executor_reason: String,
    },
}

impl std::fmt::Display for CrewActError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CrewActError::NotOnTheCrew(who) => write!(f, "{who}"),
            CrewActError::OutOfRole(out) => write!(f, "{out}"),
            CrewActError::Refused {
                identity,
                assigned,
                attempted,
                executor_reason,
            } => write!(
                f,
                "{identity}'s own {} move {attempted:?} was refused by the executor: {executor_reason}",
                assigned.name()
            ),
        }
    }
}

impl std::error::Error for CrewActError {}

/// Why a collective steer did not resolve into the world.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SteerError {
    /// No steer is open.
    NoOpenSteering,
    /// The quorum `AffineLe` gate refused the decision-turn: no winner is certified and
    /// NOTHING fired. The world is byte-for-byte unchanged and the steer stays open.
    BelowQuorum,
    /// The vote engine or the party world refused the resolution.
    Fork(String),
}

impl std::fmt::Display for SteerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SteerError::NoOpenSteering => write!(f, "no steer is open"),
            SteerError::BelowQuorum => write!(
                f,
                "below quorum — no winner certified, the away team does not move"
            ),
            SteerError::Fork(reason) => write!(f, "the steer was refused: {reason}"),
        }
    }
}

impl std::error::Error for SteerError {}

/// Why a crew could not form, assign, or depart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CrewError {
    /// The mission label is empty or overlong.
    InvalidMission,
    /// An identity is empty or overlong.
    InvalidIdentity(String),
    /// One identity appeared twice on the charter.
    DuplicateIdentity(String),
    /// Fewer than [`CREW_SEATS`] roles were occupied.
    IncompleteRoster {
        /// How many were occupied.
        occupied: usize,
    },
    /// A suitability score is outside the fixed relation's `0..=3` range.
    ScoreOutOfRange {
        /// The role the score was for.
        role: Role,
        /// The out-of-range score.
        score: u8,
    },
    /// A member declared themselves unwilling to take ANY role.
    NoWillingRole,
    /// The preference carried a zero nonce — the tiny preference space makes an unblinded
    /// commitment brute-forceable, so it is not a commitment.
    UnblindedPreference,
    /// A submitted row does not hash to the commitment this crew published for that member.
    PreferenceNotCommitted {
        /// The charter seat.
        seat: usize,
        /// The member whose row did not match.
        identity: String,
    },
    /// No assignment satisfies every member's declared willingness — nobody will heal.
    NoAdmissibleAssignment(String),
    /// The receipt is not bound to THIS crew: its statement session is not the one this
    /// roll's charter and commitments derive.
    SessionNotThisCrew {
        /// The session this crew's roll derives.
        expected: u32,
        /// The session the receipt claims.
        claimed: u32,
    },
    /// The hiding proof / statement was refused.
    Proof(String),
    /// No custody public key was supplied for a crew member.
    NoCustodyKey(String),
    /// The proof-assigned roster could not be lowered into a cap-seated party.
    Formation(PartyFormationError),
    /// A steer is already open.
    SteeringAlreadyOpen,
    /// No steer is open.
    NoOpenSteering,
    /// The vote engine or party world refused a steering step.
    Steering(String),
}

impl std::fmt::Display for CrewError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CrewError::InvalidMission => {
                write!(
                    f,
                    "the mission label is empty or exceeds {MAX_CREW_MISSION_BYTES} bytes"
                )
            }
            CrewError::InvalidIdentity(identity) => write!(
                f,
                "identity {identity:?} is empty or exceeds {MAX_CREW_IDENTITY_BYTES} bytes"
            ),
            CrewError::DuplicateIdentity(identity) => {
                write!(f, "identity {identity:?} appears twice on the crew charter")
            }
            CrewError::IncompleteRoster { occupied } => write!(
                f,
                "a crew needs {CREW_SEATS} members; {occupied} seats are occupied"
            ),
            CrewError::ScoreOutOfRange { role, score } => write!(
                f,
                "the {} suitability score {score} is outside the relation's 0..=3 range",
                role.name()
            ),
            CrewError::NoWillingRole => {
                write!(f, "a crew member must be willing to take at least one role")
            }
            CrewError::UnblindedPreference => write!(
                f,
                "a hidden preference needs a nonzero nonce: the preference space is small enough to brute-force an unblinded commitment"
            ),
            CrewError::PreferenceNotCommitted { seat, identity } => write!(
                f,
                "the row submitted for crew seat {seat} ({identity}) does not match that member's published commitment"
            ),
            CrewError::NoAdmissibleAssignment(reason) => write!(
                f,
                "no role assignment satisfies every member's declared willingness: {reason}"
            ),
            CrewError::SessionNotThisCrew { expected, claimed } => write!(
                f,
                "the role-assignment receipt is not bound to this crew: its session is {claimed}, this crew's roll derives {expected}"
            ),
            CrewError::Proof(reason) => {
                write!(f, "the role-assignment proof was refused: {reason}")
            }
            CrewError::NoCustodyKey(identity) => {
                write!(f, "no custody public key was supplied for {identity:?}")
            }
            CrewError::Formation(error) => write!(f, "the crew could not be seated: {error}"),
            CrewError::SteeringAlreadyOpen => write!(f, "a steer is already open"),
            CrewError::NoOpenSteering => write!(f, "no steer is open"),
            CrewError::Steering(reason) => write!(f, "the steer was refused: {reason}"),
        }
    }
}

impl std::error::Error for CrewError {}

// ── helpers ──────────────────────────────────────────────────────────────────────

/// Length-prefix a variable-length field so a concatenation is unambiguous (two adjacent
/// identities cannot be re-split to spell a different pair).
fn push_bounded(material: &mut Vec<u8>, bytes: &[u8]) {
    material.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    material.extend_from_slice(bytes);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn charter() -> CrewCharter {
        CrewCharter::form(
            "descent:the-drowned-marches",
            [
                "player:della".to_string(),
                "player:bramwen".to_string(),
                "player:ferro".to_string(),
                "player:corvin".to_string(),
            ],
        )
        .expect("a valid charter")
    }

    /// The two role vocabularies are ONE roster under a total bijection — no index can be
    /// silently dropped or doubled when a published `roles[4]` becomes party roles.
    #[test]
    fn the_party_and_raid_role_vocabularies_are_one_bijection() {
        let mut seen = [false; 4];
        for role in Role::ALL {
            let index = role.raid_role_index();
            assert!(!seen[index as usize], "two party roles share a raid column");
            seen[index as usize] = true;
            assert_eq!(
                Role::from_raid_role_index(index),
                Some(role),
                "the raid column round-trips to its party role"
            );
        }
        assert!(seen.iter().all(|&s| s), "every raid column is claimed");
        assert_eq!(Role::from_raid_role_index(4), None);
    }

    /// Every party move has exactly one owning role, and it is the role whose `move_of` it
    /// is — so naming an out-of-role refusal cannot name the wrong job.
    #[test]
    fn every_move_is_sanctioned_by_exactly_the_role_that_fires_it() {
        for role in Role::ALL {
            assert_eq!(role.move_of().sanctioned_role(), role);
        }
    }

    /// The charter's seat order is canonical: the same identity SET in any input order is
    /// the same charter, with the same root and the same proof session.
    #[test]
    fn a_charter_is_canonical_under_input_order() {
        let a = charter();
        let b = CrewCharter::form(
            "descent:the-drowned-marches",
            [
                "player:ferro".to_string(),
                "player:corvin".to_string(),
                "player:della".to_string(),
                "player:bramwen".to_string(),
            ],
        )
        .expect("a valid charter");
        assert_eq!(a, b, "input order does not change the crew");
        assert_eq!(a.root(), b.root());
        assert_eq!(
            a.members(),
            &[
                "player:bramwen".to_string(),
                "player:corvin".to_string(),
                "player:della".to_string(),
                "player:ferro".to_string(),
            ]
        );
        assert_eq!(a.seat_of("player:della"), Some(2));
        assert_eq!(a.seat_of("player:mallory"), None);
    }

    /// A charter refuses a repeated identity (one player cannot hold two crew seats) and a
    /// malformed label.
    #[test]
    fn a_charter_refuses_a_doubled_identity_and_a_malformed_label() {
        assert_eq!(
            CrewCharter::form(
                "m",
                [
                    "a".to_string(),
                    "b".to_string(),
                    "a".to_string(),
                    "c".to_string()
                ]
            ),
            Err(CrewError::DuplicateIdentity("a".to_string()))
        );
        assert_eq!(
            CrewCharter::form(
                "",
                [
                    "a".to_string(),
                    "b".to_string(),
                    "c".to_string(),
                    "d".to_string()
                ]
            ),
            Err(CrewError::InvalidMission)
        );
        assert_eq!(
            CrewCharter::form(
                "m",
                [
                    "".to_string(),
                    "b".to_string(),
                    "c".to_string(),
                    "d".to_string()
                ]
            ),
            Err(CrewError::InvalidIdentity(String::new()))
        );
    }

    /// A preference is refused unblinded (the space is 4^4·2^4 — a zero-nonce commitment
    /// is brute-forceable, so it hides nothing), out of range, and with no willing role.
    #[test]
    fn a_hidden_preference_refuses_an_unblinded_or_impossible_row() {
        assert_eq!(
            HiddenPreference::new([3, 1, 0, 0], [true; 4], [0u8; 32]),
            Err(CrewError::UnblindedPreference)
        );
        assert_eq!(
            HiddenPreference::new([4, 1, 0, 0], [true; 4], [7u8; 32]),
            Err(CrewError::ScoreOutOfRange {
                role: Role::Tank,
                score: 4
            })
        );
        assert_eq!(
            HiddenPreference::new([3, 1, 0, 0], [false; 4], [7u8; 32]),
            Err(CrewError::NoWillingRole)
        );
        assert!(HiddenPreference::new([3, 1, 0, 0], [true, false, true, true], [7u8; 32]).is_ok());
    }

    /// A commitment binds the row to its AUTHOR: the same row published by a different
    /// member is a different commitment, so a row cannot be re-attributed.
    #[test]
    fn a_preference_commitment_binds_the_row_to_its_author_and_its_nonce() {
        let row = HiddenPreference::new([3, 0, 1, 0], [true; 4], [9u8; 32]).unwrap();
        assert_ne!(
            row.commitment("player:della"),
            row.commitment("player:ferro"),
            "the same row by another member is another commitment"
        );
        let reblinded = HiddenPreference::new([3, 0, 1, 0], [true; 4], [10u8; 32]).unwrap();
        assert_ne!(
            row.commitment("player:della"),
            reblinded.commitment("player:della"),
            "the nonce is covered"
        );
        assert_eq!(
            row.commitment("player:della"),
            row.commitment("player:della")
        );
    }

    /// THE BINDING is a function of the crew and its commitments ONLY: it is stable for a
    /// crew, canonical for BabyBear, nonzero, and it MOVES when the crew or any member's
    /// commitment changes. That is what makes an anonymous `roles[4]` mean this crew.
    #[test]
    fn the_proof_session_is_derived_from_the_crew_and_moves_with_it() {
        let rows: [HiddenPreference; 4] = std::array::from_fn(|i| {
            HiddenPreference::new([3, 2, 1, 0], [true; 4], [i as u8 + 1; 32]).unwrap()
        });
        let roll = CrewRoll::from_preferences(charter(), &rows);
        let session = roll.proof_session();
        assert_eq!(
            session,
            CrewRoll::from_preferences(charter(), &rows).proof_session()
        );
        assert!(session != 0 && u64::from(session) < BABYBEAR_P);

        // A different crew: same commitments, one member swapped.
        let other_crew = CrewCharter::form(
            "descent:the-drowned-marches",
            [
                "player:bramwen".to_string(),
                "player:corvin".to_string(),
                "player:della".to_string(),
                "player:mallory".to_string(),
            ],
        )
        .unwrap();
        assert_ne!(
            CrewRoll::new(other_crew, *roll.commitments()).proof_session(),
            session,
            "another crew derives another session"
        );

        // A different mission with the same members.
        let other_mission =
            CrewCharter::form("descent:the-sunken-stair", charter().members().clone()).unwrap();
        assert_ne!(
            CrewRoll::new(other_mission, *roll.commitments()).proof_session(),
            session,
            "another mission derives another session"
        );

        // One member re-blinds: a new roll, a new session.
        let mut rerolled = rows;
        rerolled[1] = HiddenPreference::new([3, 2, 1, 0], [true; 4], [200u8; 32]).unwrap();
        assert_ne!(
            CrewRoll::from_preferences(charter(), &rerolled).proof_session(),
            session,
            "a changed commitment derives another session"
        );
    }

    /// A crew charter is reachable FROM a live party — the braid is not a standalone demo.
    #[test]
    fn a_charter_is_reachable_from_a_seated_party() {
        let party = Party::muster();
        let charter = CrewCharter::from_party("descent:reform", &party).expect("a charter");
        assert_eq!(
            charter.members(),
            &[
                "Bramwen".to_string(),
                "Corvin".to_string(),
                "Della".to_string(),
                "Ferro".to_string()
            ]
        );
        for seat in party.seats() {
            assert!(charter.seat_of(seat.name()).is_some());
        }
    }

    /// A crew charter is reachable FROM a lobby, and an incomplete lobby is refused.
    #[test]
    fn a_charter_is_reachable_from_a_lobby_and_refuses_an_incomplete_one() {
        let mut lobby = PartyLobby::new("table:7", "player:bramwen").expect("a lobby");
        lobby.claim("player:bramwen", Role::Tank).unwrap();
        assert_eq!(
            CrewCharter::from_lobby(&lobby),
            Err(CrewError::IncompleteRoster { occupied: 1 })
        );
        lobby.claim("player:corvin", Role::Scout).unwrap();
        lobby.claim("player:della", Role::Mage).unwrap();
        lobby.claim("player:ferro", Role::Healer).unwrap();
        let charter = CrewCharter::from_lobby(&lobby).expect("a full lobby forms a crew");
        assert_eq!(charter.mission(), "table:7");
        assert_eq!(charter.members().len(), CREW_SEATS);
    }
}
