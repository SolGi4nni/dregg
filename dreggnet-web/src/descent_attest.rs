//! # `descent_attest` — **a Descent run can carry a signature, and the board re-checks it.**
//!
//! ## The gap this closes, at its real size
//!
//! The Descent does not use `/act` at all. It plays in a tab and POSTs a WHOLE RUN to
//! `/descent/native/submit` (the Lean-native lane) or `/descent/submit` (the procgen choice-tape
//! lane), and neither route took a signature. So the board where *"it cannot be faked"* is sold
//! hardest was the one lane still entirely asserted: every row honestly read `attributed`, because
//! the name on it was a string the browser chose and nothing checked.
//!
//! `/act-signed` closed that for a per-TURN move. This module closes it for a per-RUN envelope, on
//! the same primitive and with the same custody vocabulary: the browser's non-extractable device key
//! ([`crate::device_key`]) signs one short canonical message about the finished run, and
//! [`dreggnet_offerings::verify_detached`] checks it.
//!
//! ## ⚑ TWO DIFFERENT CLAIMS, AND THE BOARD RE-CHECKS BOTH
//!
//! The Descent board already re-verifies **the moves** by replay on every single read: a forged tape
//! does not appear, and no stored "verified" bit is trusted. That is a claim about WHAT HAPPENED.
//! A signature is a claim about WHO FILED IT. They are orthogonal, and a page that shows one while
//! being silent about the other is making a claim by omission. So an attestation is re-verified on
//! every read too: nothing here is a flag written at submit time and believed later.
//!
//! ## THE CANONICAL MESSAGE
//!
//! Domain-separated, unambiguous, and built the way `dreggnet_offerings::signed::signing_message`
//! is built (plain byte concatenation with `0x00` separators and fixed-width little-endian
//! integers), for the same reason: it contains NO HASH, so a browser can build it with
//! `crypto.subtle` and nothing else.
//!
//! ```text
//! NATIVE  "dregg-descent-native-run-v1:"  ‖ day_seed_hex ‖ 0x00 ‖ ruleset_id ‖ 0x00
//!                                         ‖ actor ‖ 0x00 ‖ turns_le(8) ‖ 0x00 ‖ root_hex
//!
//! PROCGEN "dregg-descent-procgen-run-v1:" ‖ day_seed_hex ‖ 0x00 ‖ ruleset_id ‖ 0x00
//!                                         ‖ player ‖ 0x00 ‖ count_le(8) ‖ move_le(8)…
//! ```
//!
//! The two domains are DISJOINT byte strings, not one domain with a lane field, so a signature made
//! for one lane can never verify as the other regardless of what the trailing bytes happen to be
//! (the same discipline `TURN_SIGNING_EPOCH_DOMAIN` uses against its epoch-free twin).
//!
//! ### What each field is doing there
//!
//! * **`day_seed_hex` — the WORLD, not the day's label.** A day KEY is a label and two labels can
//!   name one world (the demo's `"today"` and the canonical `d{utc}-off` are the same board, and
//!   `resolve_submitted_day` deliberately lands a run on whichever is already open). Signing the
//!   label would make a signature depend on which alias the server happened to resolve; signing the
//!   committed seed binds the thing the label names. On the native lane the seed is also folded into
//!   the run's genesis journal root, so it is bound twice over.
//! * **`ruleset_id`** — the hash of the emitted program the run was played under
//!   ([`native_ruleset_id`] / [`procgen_ruleset_id`]). A rules overhaul is imminent; a run landing
//!   today says what it was played under even though nothing consumes it yet.
//! * **`actor` / `player`** — the name the run is filed under. Bound because a signature that did
//!   not cover the name would let a captured envelope be re-filed under a different one, which is
//!   the failure that would make signing worse than not signing at all.
//! * **`turns`** — the claimed turn count, which is what the boards rank on.
//! * **`root_hex` (native)** — the run's actor-bound hash-chained journal head. THIS is how the
//!   whole move tape is covered without putting eight megabytes of JSON through the signer: the
//!   root chains every event, the day-seed is in its genesis, and the server's own exact replay is
//!   what proves the submitted record produces exactly this root. A different tape is a different
//!   root, so a signature over the root is a signature over the tape the replay just re-derived.
//! * **`moves` (procgen)** — that lane has no chained root, so the tape rides in the message
//!   directly: a length prefix then one fixed-width 8-byte word per choice, which is
//!   self-delimiting and cannot be re-partitioned into a different tape of the same bytes.
//!
//! ### ⚑ WHAT IT DOES NOT COVER, AND WHY
//!
//! 1. **It does not say the moves were legal.** That is the replay's claim and it is checked
//!    separately, on every read. A signature on a losing or illegal run proves only who filed it;
//!    the run still does not rank.
//! 2. **It does not say who DISCOVERED the line.** Any player may replay a public tape under their
//!    own name and sign that honestly. The signature answers "who filed this", not "who thought of
//!    it". Nothing here changes that a deterministic game with public tapes can be copied, and
//!    pretending otherwise would be the overstatement this whole vocabulary exists to refuse.
//! 3. **It does not cover display metadata** (the procgen lane's `level` / `class`): decoration the
//!    executor never reads, exactly as `signed.rs` refuses to sign `label` / `enabled`. A cosmetic
//!    change must not invalidate an otherwise-identical run.
//! 4. **It does not cover the run id.** The id is a content address of `(day, record)` and the
//!    record is pinned by the root the message DOES cover, so an id cannot vary without breaking a
//!    binding that is covered. Signing a value the client cannot compute would have meant a
//!    server-chosen field inside a client signature, which is not a signature about anything.
//! 5. **It is NOT epoch-bound, and unlike the turn lane that costs nothing.** `act_signed.rs` binds
//!    a host incarnation for custodial signers because a same-`id` session reopened after a restart
//!    resets its replay-counter floor and would re-admit a captured `counter = 0` envelope. A run
//!    submission has no counter and no session: it is content-addressed and idempotent, so
//!    re-presenting a captured envelope lands the byte-identical row under the byte-identical name.
//!    Binding a per-incarnation epoch here would buy nothing and would cost a player their signature
//!    every time the server restarted between finishing a run and the tab auto-anchoring it. The
//!    user-held `/act-signed` lane's epoch debt is real and is NOT discharged here; this is a
//!    different envelope with a different replay story, said out loud so the two are not confused.
//!
//! ## WHO MAY SIGN FOR A NAME
//!
//! The signer is a KEY; the run is filed under a NAME. Requiring them to be the same string would
//! have broken the actual product: the browser files a run under the player's CLAIMED root key (the
//! 24-word identity), while the key that signs is the browser's own device key, which is deliberately
//! a different key the server has never seen. So the rule is the one the boards already use for
//! everything else — [`RootResolver`]: **the signing key and the filed name must resolve to the same
//! human.** An enrolled device resolves to its owner's account, so it may sign for them; an
//! unenrolled key resolves to itself, so it may sign only for itself. A stranger's key never
//! resolves to your account, so it can never file a run under your name.

use blake3::Hasher;
use dreggnet_offerings::{Custody, verify_detached};
use serde::Deserialize;
use webauth_core::identity_resolve::RootResolver;
use webauth_core::link_registry::{
    FileLinkStore, LinkStore, account_id_of_root, default_store_path,
};

use crate::device_key::platform_is_self_held;

// ─────────────────────────────────────────────────────────────────────────────
// THE DOMAINS + THE RULESET IDS
// ─────────────────────────────────────────────────────────────────────────────

/// The domain tag a **Lean-native** Descent run attestation is bound under.
pub const NATIVE_RUN_DOMAIN: &[u8] = b"dregg-descent-native-run-v1:";

/// The domain tag a **procgen choice-tape** Descent run attestation is bound under. A distinct byte
/// string, not a field, so the two lanes' signatures are cryptographically disjoint.
pub const PROCGEN_RUN_DOMAIN: &[u8] = b"dregg-descent-procgen-run-v1:";

/// How many hex characters a ruleset id carries after its lane tag.
///
/// ⚑ 24, not 32 or 64, and the reason is a gate rather than taste: the shared refusal-copy checker
/// ([`dreggnet_offerings::refusal::audit_player_text`]) treats a run of 32-or-more hex characters as
/// a raw key that no reader can act on. A ruleset id is meant to be printable on a run card and
/// quotable in a refusal, so it is sized to stay a readable token. 12 bytes of a blake3 digest is
/// ample for naming which of a handful of shipped rulesets a run was played under.
const RULESET_HEX_CHARS: usize = 24;

/// **The Lean-native lane's ruleset id** — the hash of the emitted program this build installs
/// (`dungeon_on_dregg::descent::PROGRAM_JSON`, the checked-in Lean emission the native Descent
/// actually deploys). One string, no versioning machinery, no replayer: a run landing today records
/// what it was played under, so when the rules are overhauled the archive can say which runs belong
/// to which rules instead of leaving a reader to infer it from a date.
pub fn native_ruleset_id() -> &'static str {
    static ID: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    ID.get_or_init(|| {
        format!(
            "lean-dungeon-{}",
            short_hash(
                b"dregg.descent.ruleset.native.v1",
                dungeon_on_dregg::descent::PROGRAM_JSON.as_bytes(),
            )
        )
    })
    .as_str()
}

/// **The procgen lane's ruleset id** — the hash of the day's own compiled scene source, which is
/// what `record_playthrough` actually executes. That lane has no build-level emitted artifact: its
/// program is generated per day from the committed seed, so the honest "what rules was this played
/// under" is the generated program itself. A change to the generator yields a different id for the
/// same seed, which is exactly the fact worth recording.
pub fn procgen_ruleset_id(scene_source: &str) -> String {
    format!(
        "procgen-scene-{}",
        short_hash(b"dregg.descent.ruleset.procgen.v1", scene_source.as_bytes())
    )
}

fn short_hash(domain: &[u8], body: &[u8]) -> String {
    let mut hasher = Hasher::new();
    hasher.update(domain);
    hasher.update(&[0]);
    hasher.update(body);
    hasher
        .finalize()
        .as_bytes()
        .iter()
        .take(RULESET_HEX_CHARS / 2)
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// THE CANONICAL MESSAGES
// ─────────────────────────────────────────────────────────────────────────────

/// A field that would make the message ambiguous. See [`push_field`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AmbiguousField(pub &'static str);

/// Append one variable-length field and its `0x00` terminator.
///
/// ⚑ NUL HARDENING, for the reason the extension's and the browser's message builders both state:
/// the layout separates variable-length fields with `0x00`, so a field that CONTAINED one would let
/// two different runs encode to the same bytes and one signature verify as the other. A day seed, a
/// ruleset id and a journal root are hex by construction; an ACTOR is an arbitrary string a browser
/// chose, so this is a real gate on a real input rather than a formality.
fn push_field(out: &mut Vec<u8>, name: &'static str, value: &str) -> Result<(), AmbiguousField> {
    if value.as_bytes().contains(&0) {
        return Err(AmbiguousField(name));
    }
    out.extend_from_slice(value.as_bytes());
    out.push(0);
    Ok(())
}

/// **The canonical signing message for a Lean-native run** (see the module doc for the layout and
/// for what it deliberately leaves out).
pub fn native_signing_message(
    day_seed_hex: &str,
    ruleset_id: &str,
    actor: &str,
    turns: u64,
    root_hex: &str,
) -> Result<Vec<u8>, AmbiguousField> {
    let mut message = Vec::with_capacity(
        NATIVE_RUN_DOMAIN.len()
            + day_seed_hex.len()
            + ruleset_id.len()
            + actor.len()
            + root_hex.len()
            + 13,
    );
    message.extend_from_slice(NATIVE_RUN_DOMAIN);
    push_field(&mut message, "the day", day_seed_hex)?;
    push_field(&mut message, "the rules", ruleset_id)?;
    push_field(&mut message, "the name", actor)?;
    message.extend_from_slice(&turns.to_le_bytes());
    message.push(0);
    // The journal root rides LAST and unterminated: it is the tail of the message, so there is
    // nothing after it that a shifted boundary could steal bytes from.
    if root_hex.as_bytes().contains(&0) {
        return Err(AmbiguousField("the run root"));
    }
    message.extend_from_slice(root_hex.as_bytes());
    Ok(message)
}

/// **The canonical signing message for a procgen choice-tape run.** The tape rides in the message
/// itself (that lane commits no chained root): a `u64` count, then one fixed-width little-endian
/// `u64` per choice. Length-prefixed and fixed-width, so no tape can be re-partitioned into another
/// tape with the same bytes.
pub fn procgen_signing_message(
    day_seed_hex: &str,
    ruleset_id: &str,
    player: &str,
    moves: &[u64],
) -> Result<Vec<u8>, AmbiguousField> {
    let mut message = Vec::with_capacity(
        PROCGEN_RUN_DOMAIN.len()
            + day_seed_hex.len()
            + ruleset_id.len()
            + player.len()
            + 8 * moves.len()
            + 12,
    );
    message.extend_from_slice(PROCGEN_RUN_DOMAIN);
    push_field(&mut message, "the day", day_seed_hex)?;
    push_field(&mut message, "the rules", ruleset_id)?;
    push_field(&mut message, "the name", player)?;
    let count = u64::try_from(moves.len()).map_err(|_| AmbiguousField("the move count"))?;
    message.extend_from_slice(&count.to_le_bytes());
    for choice in moves {
        message.extend_from_slice(&choice.to_le_bytes());
    }
    Ok(message)
}

// ─────────────────────────────────────────────────────────────────────────────
// THE WIRE
// ─────────────────────────────────────────────────────────────────────────────

/// **The optional attestation block on a submit body.** Absent is the ordinary case and stays
/// ordinary: a stranger who plays a run and posts it still gets on the board, and the row honestly
/// reads `attributed`. This is a STRONGER CLAIM AVAILABLE, never a new requirement.
#[derive(Debug, Clone, Deserialize)]
pub struct RunAttestationWire {
    /// The signer's Ed25519 public key, 64 hex characters. For a browser this is the device key the
    /// player enrolled; the server has never held its secret half.
    pub signer_pubkey_hex: String,
    /// The 64-byte signature over the lane's canonical message, 128 hex characters.
    pub signature_hex: String,
    /// The ruleset id the client signed under. Echoed rather than assumed so a mismatch is a named
    /// refusal a player can act on instead of an anonymous bad-signature.
    pub ruleset_id: String,
}

/// **A signature that VERIFIED**, and nothing more. Deliberately separate from [`RunAttestation`]:
/// this is the part re-derivable from the run itself on every read, while custody is a fact about
/// the world that has to be looked up. Keeping them apart is what lets a board render re-check every
/// row's signature without a link-store scan per row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedSignature {
    /// The verified signer's public key, lowercase hex.
    pub signer_pubkey_hex: String,
    /// The signature that verified.
    pub signature: [u8; 64],
    /// The ruleset the run was played under.
    pub ruleset_id: String,
}

impl VerifiedSignature {
    /// Grade WHERE the signing key lives, from the shared link store, and become a full
    /// [`RunAttestation`]. ONE store scan, so a caller that only needs "did this check out" (a board
    /// render re-checking a retained row) never pays for it.
    pub fn with_custody(self) -> RunAttestation {
        let custody = custody_of(&self.signer_pubkey_hex);
        RunAttestation {
            signer_pubkey_hex: self.signer_pubkey_hex,
            signature: self.signature,
            ruleset_id: self.ruleset_id,
            custody,
        }
    }
}

/// **A VERIFIED attestation**, as the board retains and re-checks it. Everything here was checked at
/// submit and is checked again on every read; nothing in it is believed because it was stored.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunAttestation {
    /// The verified signer's public key, lowercase hex.
    pub signer_pubkey_hex: String,
    /// The signature, retained so every read can check it again rather than trust this row.
    pub signature: [u8; 64],
    /// The ruleset the run was played under.
    pub ruleset_id: String,
    /// Where the signing key lived. Provenance, not crypto (a signature is a signature), so it rides
    /// beside the verified fact exactly as `dreggnet_offerings::Custody` does, and an unknown value
    /// reads as [`Custody::Custodial`]: understating custody is safe, overstating it is the wound the
    /// grade exists to close.
    pub custody: Custody,
}

impl RunAttestation {
    /// The single-character custody tag this row persists (`u` user-held, `c` custodial).
    pub fn custody_tag(&self) -> &'static str {
        match self.custody {
            Custody::UserHeld => "u",
            Custody::Custodial => "c",
        }
    }

    /// Decode a persisted custody tag. Anything else is [`Custody::Custodial`] — the honest floor,
    /// never the stronger claim.
    pub fn custody_from_tag(tag: &str) -> Custody {
        match tag {
            "u" => Custody::UserHeld,
            _ => Custody::Custodial,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE REFUSALS
// ─────────────────────────────────────────────────────────────────────────────

/// Why an attestation was refused. One variant per gate that ran and said no; in every one of them
/// NOTHING was ingested, because the whole check happens before the run reaches the board.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttestRefusal {
    /// The block was not in a shape that could name a signer at all (bad hex, wrong length).
    Malformed,
    /// The run was signed under a different set of rules than this board keeps score with.
    WrongRuleset,
    /// The message could not be built unambiguously, because a field carried a zero byte.
    UnnameableRun,
    /// The signature did not verify over the canonical message.
    DidNotCheckOut,
    /// The signing key does not belong to the person the run is filed under.
    NotThisPlayer,
}

impl AttestRefusal {
    /// The sentence a player reads. Every one names the failing check in plain words, says that
    /// nothing was recorded and that their run is still theirs, and gives one thing to do next.
    /// ⚑ Every one of them also offers the unsigned path, because losing a run to an unavailable
    /// stronger claim would be a worse outcome than never having offered the stronger claim.
    pub fn message(&self) -> String {
        match self {
            AttestRefusal::Malformed => "Refused: the signature sent with this run was not in a \
                 form we could read, so nothing was added to the board and the run is still on your \
                 machine. Reload the game page and publish it again; publishing without a signature \
                 works too and the run still counts."
                .to_string(),
            AttestRefusal::WrongRuleset => "Refused: this run was signed under a different set of \
                 rules than the board is keeping score with, so nothing was added and the run is \
                 still on your machine. Reload the game page to pick up the current rules, then \
                 play and publish again."
                .to_string(),
            AttestRefusal::UnnameableRun => "Refused: the name this run is filed under contains a \
                 character we cannot sign around, so nothing was added and the run is still on your \
                 machine. Open your identity page and claim a name, or publish without a signature; \
                 the run still counts either way."
                .to_string(),
            AttestRefusal::DidNotCheckOut => "Refused: the signature on this run did not check out \
                 against the run it came with, so nothing was added to the board and the run is \
                 still on your machine. Reload the game page and publish it again; publishing \
                 without a signature works too and the run still counts."
                .to_string(),
            AttestRefusal::NotThisPlayer => "Refused: the key that signed this run is not one the \
                 player it is filed under has enrolled, so nothing was added to the board and the \
                 run is still on your machine. Open your identity page and enrol this browser, or \
                 publish the run without a signature; the run still counts either way."
                .to_string(),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// CUSTODY + THE HUMAN JOIN
// ─────────────────────────────────────────────────────────────────────────────

/// **Where a signing key lives**, from the shared link store: a key enrolled under a SELF-HELD
/// platform (a browser device key, a web root key) is [`Custody::UserHeld`]; anything else — a chat
/// bot's derived key, or a key with no link row at all — is [`Custody::Custodial`], the fail-closed
/// floor.
///
/// ⚑ This reads [`platform_is_self_held`] rather than re-spelling `platform != "web"`, which is the
/// exact comparison that would have printed "an operator can derive this key" beside the one key in
/// the whole system nobody but the browser can produce.
pub fn custody_of(signer_pubkey_hex: &str) -> Custody {
    let store = FileLinkStore::new(default_store_path());
    let mut latest: Option<(u64, String)> = None;
    for record in store.all().unwrap_or_default() {
        if record
            .custodial_pubkey_hex
            .eq_ignore_ascii_case(signer_pubkey_hex)
        {
            match &latest {
                Some((at, _)) if *at > record.verified_at => {}
                _ => latest = Some((record.verified_at, record.platform)),
            }
        }
    }
    match latest {
        Some((_, platform)) if platform_is_self_held(&platform) => Custody::UserHeld,
        _ => Custody::Custodial,
    }
}

/// **May this key sign for this name?** Three ways to say yes, and each is a real case the product
/// actually produces:
///
/// 1. **The name IS the key.** A signer filing under its own public key vouches for itself and needs
///    no enrolment at all. This is the only route open to a browser with a device key and no claimed
///    identity, and it is honest: the name and the signature are the same fact.
/// 2. **The name is the ROOT this key is enrolled under.** The ordinary flow: the run is filed under
///    the player's 24-word identity key while the browser's own device key signs, and the enrolment
///    row is exactly the statement "this device may act as that root". ⚑ Checked directly against the
///    root rather than by comparing two [`RootResolver`] answers, because a claimed identity that has
///    never linked a chat platform has NO self-row, so the resolver answers the raw key for the root
///    and an account id for the device: two correct answers about one human that are not equal as
///    strings. Comparing them would have refused the single most common signed run on the board.
/// 3. **Both resolve to the same human.** The general join every board already uses, which also
///    covers a name that is itself some other custodial key of the same person.
///
/// A stranger's key satisfies none of them: it is not the name, its enrolment names a different
/// root, and it resolves to a different account. So a valid signature can never file a run under
/// somebody else's name, which is the property that makes signing worth doing at all.
pub fn may_sign_for(resolver: &RootResolver, signer_pubkey_hex: &str, filed_name: &str) -> bool {
    let signer = signer_pubkey_hex.trim().to_ascii_lowercase();
    let name = filed_name.trim().to_ascii_lowercase();
    if signer == name {
        return true;
    }
    if let (Some(signer_account), Some(name_account)) =
        (resolver.resolve_opt(&signer), account_id_of_root(&name))
    {
        if signer_account == name_account {
            return true;
        }
    }
    match (resolver.resolve_opt(&signer), resolver.resolve_opt(&name)) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE VERIFIER
// ─────────────────────────────────────────────────────────────────────────────

/// Decode exactly `N * 2` hex characters. `None` on any other shape.
fn decode_hex<const N: usize>(s: &str) -> Option<[u8; N]> {
    let bytes = s.as_bytes();
    if bytes.len() != N * 2 {
        return None;
    }
    let nibble = |byte: u8| match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    };
    let mut out = [0u8; N];
    for (index, pair) in bytes.chunks_exact(2).enumerate() {
        out[index] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
    }
    Some(out)
}

/// **Verify one attestation against a message the caller built from FACTS IT RE-DERIVED.**
///
/// The gate order is fail-closed and cheapest first: shape, then the ruleset the board keeps score
/// with, then the signature, then the human join. `resolver` is passed in rather than loaded here so
/// a board render can scan the link store once for a whole page instead of once per row.
///
/// The caller MUST build `message` from its own re-verified material (the replayed actor, the
/// replayed turn count, the replayed journal root), never from the submitted claim. That is what
/// makes this a check rather than a comparison of a client's story with itself.
pub fn verify_attestation(
    resolver: &RootResolver,
    expected_ruleset_id: &str,
    filed_name: &str,
    message: &[u8],
    wire: &RunAttestationWire,
) -> Result<VerifiedSignature, AttestRefusal> {
    let signer = wire.signer_pubkey_hex.trim().to_ascii_lowercase();
    if decode_hex::<32>(&signer).is_none() {
        return Err(AttestRefusal::Malformed);
    }
    let signature = decode_hex::<64>(wire.signature_hex.trim()).ok_or(AttestRefusal::Malformed)?;
    if wire.ruleset_id != expected_ruleset_id {
        return Err(AttestRefusal::WrongRuleset);
    }
    verify_detached(&signer, message, &signature).map_err(|_| AttestRefusal::DidNotCheckOut)?;
    // THE NAME GATE, last and non-negotiable: a signature that verified over a message naming
    // somebody else is a valid signature about a claim this key is not entitled to make.
    if !may_sign_for(resolver, &signer, filed_name) {
        return Err(AttestRefusal::NotThisPlayer);
    }
    Ok(VerifiedSignature {
        signer_pubkey_hex: signer,
        signature,
        ruleset_id: wire.ruleset_id.clone(),
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// WHAT THE SIGNATURE PROVES, IN PROSE
// ─────────────────────────────────────────────────────────────────────────────

/// **The paragraph a run card prints beside a signed run**, stating what the signature does and does
/// not prove. It lives here, beside the message it describes, so a change to the coverage and a
/// change to the sentence are the same edit.
pub fn signature_panel(custody: Custody, signer_pubkey_hex: &str, ruleset_id: &str) -> String {
    let custody = match custody {
        Custody::UserHeld => {
            "made on the player's own machine, with a key this server has never held"
        }
        Custody::Custodial => {
            "made with a key whose custody we could not establish as the player's own, so it is \
             recorded at the weaker grade"
        }
    };
    format!(
        "<section class=\"deos-section\"><p class=\"eyebrow\">Who filed this run</p>\
         <h2>Signed</h2>\
         <p class=\"prose\">This run arrived with a signature {custody}. The signature was checked \
         again just now, against this run: it covers the world this run was played in, the rules it \
         was played under, the name it is filed under, how many turns it took, and the run's own \
         journal root, which every landed move is chained into. Change any of those and the \
         signature stops checking out.</p>\
         <p class=\"prose\"><strong>What it does not say.</strong> It does not say the moves were \
         legal: that is the replay above, and it is a separate question this page answers \
         separately. It does not say this player invented the line either. Anyone may replay a run \
         they have seen and file it honestly under their own name, and a signature on such a run is \
         a true statement about who filed it, not a claim to have thought of it.</p>\
         <div class=\"kv\"><div><p class=\"k\">Signing key</p><p class=\"v mono\">{key}</p></div>\
         <div><p class=\"k\">Rules</p><p class=\"v mono\">{rules}</p></div></div></section>",
        custody = custody,
        key = crate::esc(signer_pubkey_hex),
        rules = crate::esc(ruleset_id),
    )
}

/// The paragraph a run card prints when the run carries NO signature. ⚑ It is printed, not omitted:
/// an absence cannot be read, and on a page selling verifiability a silence about the name reads as
/// a claim about it.
pub fn unsigned_panel(ruleset_id: &str) -> String {
    format!(
        "<section class=\"deos-section\"><p class=\"eyebrow\">Who filed this run</p>\
         <h2>Attributed</h2>\
         <p class=\"prose\">This run was filed under the name the player was signed in as, and no \
         signature came with it. That is the ordinary way a browser plays here and it is not a \
         lesser run: the replay above checked the moves either way. What it cannot do is prove that \
         the person who filed it is the person named on it. A browser that has \
         <a href=\"/identity/device\">enrolled a signing key</a> attaches one automatically from \
         then on.</p>\
         <div class=\"kv\"><div><p class=\"k\">Rules</p><p class=\"v mono\">{rules}</p></div></div>\
         </section>",
        rules = crate::esc(ruleset_id),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::TurnSigner;
    use dreggnet_offerings::refusal::audit_player_text;
    use webauth_core::link_registry::{InMemoryLinkStore, LinkRecord};

    /// ⚑ THE WIRE PIN — the native message for a fixed input, byte for byte, built here BY HAND so
    /// any drift in the layout (a reordered field, a dropped separator, an endianness flip) is a red
    /// test rather than a silent fork between this verifier and the browser's signer.
    #[test]
    fn the_native_signing_message_is_pinned_byte_for_byte() {
        let message = native_signing_message(
            "aa".repeat(32).as_str(),
            "lean-dungeon-abc",
            "web:x",
            7,
            "ff".repeat(32).as_str(),
        )
        .expect("the fields are nameable");

        let mut expected: Vec<u8> = Vec::new();
        expected.extend_from_slice(b"dregg-descent-native-run-v1:");
        expected.extend_from_slice("aa".repeat(32).as_bytes());
        expected.push(0);
        expected.extend_from_slice(b"lean-dungeon-abc");
        expected.push(0);
        expected.extend_from_slice(b"web:x");
        expected.push(0);
        expected.extend_from_slice(&[7, 0, 0, 0, 0, 0, 0, 0]);
        expected.push(0);
        expected.extend_from_slice("ff".repeat(32).as_bytes());
        assert_eq!(message, expected, "the native run message drifted");

        // Every covered field CHANGES the message. Non-vacuous in five directions.
        let base = message.clone();
        for other in [
            native_signing_message(
                "ab".repeat(32).as_str(),
                "lean-dungeon-abc",
                "web:x",
                7,
                "ff".repeat(32).as_str(),
            ),
            native_signing_message(
                "aa".repeat(32).as_str(),
                "lean-dungeon-abd",
                "web:x",
                7,
                "ff".repeat(32).as_str(),
            ),
            native_signing_message(
                "aa".repeat(32).as_str(),
                "lean-dungeon-abc",
                "web:y",
                7,
                "ff".repeat(32).as_str(),
            ),
            native_signing_message(
                "aa".repeat(32).as_str(),
                "lean-dungeon-abc",
                "web:x",
                8,
                "ff".repeat(32).as_str(),
            ),
            native_signing_message(
                "aa".repeat(32).as_str(),
                "lean-dungeon-abc",
                "web:x",
                7,
                "fe".repeat(32).as_str(),
            ),
        ] {
            assert_ne!(
                base,
                other.expect("nameable"),
                "a covered field did not change the message"
            );
        }
    }

    /// The two lanes are byte-DISJOINT: neither message can ever begin with the other's domain, so
    /// a procgen signature can never be presented as a native one or the reverse.
    #[test]
    fn the_two_lane_domains_are_disjoint() {
        let native = native_signing_message("aa", "r", "p", 1, "bb").expect("nameable");
        let procgen = procgen_signing_message("aa", "r", "p", &[1]).expect("nameable");
        assert!(!native.starts_with(PROCGEN_RUN_DOMAIN));
        assert!(!procgen.starts_with(NATIVE_RUN_DOMAIN));
        assert_ne!(native, procgen);
    }

    /// The procgen tape is length-prefixed and fixed-width, so two DIFFERENT tapes can never encode
    /// to the same bytes (the ambiguity a separator-delimited tape would have).
    #[test]
    fn the_procgen_tape_cannot_be_repartitioned() {
        let a = procgen_signing_message("aa", "r", "p", &[1, 2]).expect("nameable");
        let b = procgen_signing_message("aa", "r", "p", &[1, 2, 0]).expect("nameable");
        let c = procgen_signing_message("aa", "r", "p", &[2, 1]).expect("nameable");
        assert_ne!(a, b);
        assert_ne!(a, c);
        // A name that swallowed the tape's leading bytes is refused rather than encoded.
        assert_eq!(
            procgen_signing_message("aa", "r", "p\0q", &[1]),
            Err(AmbiguousField("the name"))
        );
    }

    /// A run signed by a key, verified by the real verifier, and REFUSED for each forgery class.
    /// The name gate is the load-bearing one: it is what stops a captured envelope being re-filed.
    #[test]
    fn a_signed_run_verifies_and_every_forgery_class_is_refused() {
        let signer = TurnSigner::from_seed([3u8; 32]);
        let imposter = TurnSigner::from_seed([4u8; 32]);
        let resolver = RootResolver::default(); // no links: every key is its own human
        let rules = "lean-dungeon-testing";
        let message = native_signing_message(
            "aa".repeat(32).as_str(),
            rules,
            signer.pubkey_hex(),
            5,
            "cc".repeat(32).as_str(),
        )
        .expect("nameable");
        let wire = RunAttestationWire {
            signer_pubkey_hex: signer.pubkey_hex().to_string(),
            signature_hex: hex64(&signer.sign_detached(&message)),
            ruleset_id: rules.to_string(),
        };

        let ok = verify_attestation(&resolver, rules, signer.pubkey_hex(), &message, &wire)
            .expect("the genuine attestation verifies");
        assert_eq!(ok.signer_pubkey_hex, signer.pubkey_hex());

        // A DIFFERENT ruleset id refuses before any crypto runs.
        let mut wrong_rules = wire.clone();
        wrong_rules.ruleset_id = "lean-dungeon-elsewhere".to_string();
        assert_eq!(
            verify_attestation(
                &resolver,
                rules,
                signer.pubkey_hex(),
                &message,
                &wrong_rules
            ),
            Err(AttestRefusal::WrongRuleset)
        );

        // A FORGED signature (the imposter signs, claiming the signer's key).
        let mut forged = wire.clone();
        forged.signature_hex = hex64(&imposter.sign_detached(&message));
        assert_eq!(
            verify_attestation(&resolver, rules, signer.pubkey_hex(), &message, &forged),
            Err(AttestRefusal::DidNotCheckOut)
        );

        // A TAMPERED run: the same envelope presented against a message with one more turn.
        let moved = native_signing_message(
            "aa".repeat(32).as_str(),
            rules,
            signer.pubkey_hex(),
            6,
            "cc".repeat(32).as_str(),
        )
        .expect("nameable");
        assert_eq!(
            verify_attestation(&resolver, rules, signer.pubkey_hex(), &moved, &wire),
            Err(AttestRefusal::DidNotCheckOut)
        );

        // ⚑ THE RE-FILING TOOTH: the imposter signs an envelope naming their OWN key, which
        // verifies as a signature, and is refused because it is filed under somebody else.
        let their_message = native_signing_message(
            "aa".repeat(32).as_str(),
            rules,
            signer.pubkey_hex(),
            5,
            "cc".repeat(32).as_str(),
        )
        .expect("nameable");
        let refiled = RunAttestationWire {
            signer_pubkey_hex: imposter.pubkey_hex().to_string(),
            signature_hex: hex64(&imposter.sign_detached(&their_message)),
            ruleset_id: rules.to_string(),
        };
        assert_eq!(
            verify_attestation(
                &resolver,
                rules,
                signer.pubkey_hex(),
                &their_message,
                &refiled
            ),
            Err(AttestRefusal::NotThisPlayer),
            "a valid signature over another player's name must not file the run"
        );

        // MALFORMED shapes never reach the verifier.
        for bad in ["", "abcd", &"z".repeat(64)] {
            let mut wire = wire.clone();
            wire.signer_pubkey_hex = bad.to_string();
            assert_eq!(
                verify_attestation(&resolver, rules, signer.pubkey_hex(), &message, &wire),
                Err(AttestRefusal::Malformed)
            );
        }
    }

    /// An ENROLLED device signs for its owner's claimed name; a stranger's enrolled device does not.
    /// This is the case the product actually runs: the filed name is the phrase's key and the signer
    /// is the browser's own key, which are deliberately different keys.
    #[test]
    fn an_enrolled_device_may_sign_for_the_name_it_was_enrolled_under() {
        let root = "ab".repeat(32);
        let stranger_root = "cd".repeat(32);
        let device = TurnSigner::from_seed([9u8; 32]);
        let stranger_device = TurnSigner::from_seed([10u8; 32]);
        let mut store = InMemoryLinkStore::default();
        store
            .record(&LinkRecord {
                root_pubkey_hex: root.clone(),
                platform: crate::device_key::DEVICE_PLATFORM.to_string(),
                platform_uid: "dev-1".to_string(),
                custodial_pubkey_hex: device.pubkey_hex().to_string(),
                verified_at: 1_790_000_000,
            })
            .expect("the row records");
        store
            .record(&LinkRecord {
                root_pubkey_hex: stranger_root.clone(),
                platform: crate::device_key::DEVICE_PLATFORM.to_string(),
                platform_uid: "dev-2".to_string(),
                custodial_pubkey_hex: stranger_device.pubkey_hex().to_string(),
                verified_at: 1_790_000_000,
            })
            .expect("the row records");
        // ⚑ NO `web` self-row is written here, on purpose: a player who claimed an identity but has
        // never linked a chat platform has none, and that is the most common signed run on the
        // board. A rule that compared two resolver answers would refuse exactly this case.
        let resolver = RootResolver::from_store(&store);

        assert!(
            may_sign_for(&resolver, device.pubkey_hex(), &root),
            "an enrolled device signs for the identity that enrolled it, self-row or not"
        );
        assert!(
            !may_sign_for(&resolver, stranger_device.pubkey_hex(), &root),
            "a stranger's device must never file a run under this name"
        );
        assert!(
            !may_sign_for(&resolver, device.pubkey_hex(), &stranger_root),
            "and it must not file one under a name it was never enrolled for"
        );
        // A key filing under ITS OWN public key vouches for itself with no enrolment at all.
        assert!(may_sign_for(
            &resolver,
            device.pubkey_hex(),
            device.pubkey_hex()
        ));
        let unenrolled = TurnSigner::from_seed([11u8; 32]);
        assert!(may_sign_for(
            &resolver,
            unenrolled.pubkey_hex(),
            unenrolled.pubkey_hex()
        ));
        assert!(!may_sign_for(&resolver, unenrolled.pubkey_hex(), &root));
    }

    /// ⚑ THE COPY GATE, on the strings this module ships. A refusal that reads as broken rather than
    /// refused is the failure this vocabulary exists to prevent.
    #[test]
    fn every_refusal_passes_the_shared_copy_gate() {
        for refusal in [
            AttestRefusal::Malformed,
            AttestRefusal::WrongRuleset,
            AttestRefusal::UnnameableRun,
            AttestRefusal::DidNotCheckOut,
            AttestRefusal::NotThisPlayer,
        ] {
            let text = refusal.message();
            assert_eq!(
                audit_player_text(&text, true, true),
                Vec::new(),
                "a refusal this module ships fails the shared copy gate: {text}"
            );
            assert!(text.starts_with("Refused:"), "{text}");
            assert!(
                text.contains("without a signature") || text.contains("play and publish again"),
                "every refusal must leave the player a way to land their run: {text}"
            );
        }
    }

    /// The ruleset id is a stable, readable token that names the emitted program. A 32-character hex
    /// run would trip the shared copy gate the moment it appeared in a refusal or on a card.
    #[test]
    fn the_ruleset_id_is_stable_and_short_enough_to_print() {
        let id = native_ruleset_id();
        assert_eq!(id, native_ruleset_id(), "the id must not vary per call");
        assert!(id.starts_with("lean-dungeon-"), "{id}");
        assert_eq!(id.len(), "lean-dungeon-".len() + RULESET_HEX_CHARS);
        assert_eq!(
            audit_player_text(id, false, false),
            Vec::new(),
            "the ruleset id must be printable in player copy: {id}"
        );
        // A DIFFERENT program is a DIFFERENT id (the property the archive will read).
        assert_ne!(procgen_ruleset_id("scene a"), procgen_ruleset_id("scene b"));
    }

    fn hex64(bytes: &[u8; 64]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }
}
