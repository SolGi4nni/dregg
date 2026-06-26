//! Tier B/C CORE — postgres-independent, `cargo test`-proven.
//!
//! This is the storage/query/verified-write substrate of `pg-dregg`, built to
//! the spine invariant of `docs/PG-DREGG.md` §8:
//!
//! > **Reads are free SQL; state mutates ONLY through verified turns.**
//!
//! Like [`crate::authz`] (the Tier A core), everything here is plain Rust with
//! no `pgrx` dependency, so it is provable with `cargo test` (no postgres, no
//! `cargo-pgrx`). The `#[pg_extern]` wrappers in [`crate`] marshal SQL types
//! into these functions.
//!
//! ## Why this crate does NOT depend on `dregg-cell`
//!
//! `dregg-cell` pulls `dregg-circuit` unconditionally (its
//! `compute_canonical_state_commitment` is circuit-backed). Linking it here
//! would forfeit the circuit-free, offline property that makes the embeddable
//! `pg-dregg` layer attractive (`cargo tree -i dregg-circuit -p dregg-auth` is
//! empty, and we keep it that way). So the mirror works over **plain owned row
//! types** — the SQL-row projection of dregg state — and the *projection* from a
//! live `dregg_cell::Cell` into these rows happens on the **node** side (which
//! already has `dregg-cell`), at the commit-log sink. This crate owns the SQL
//! shape, the universal-memory model, the DDL, and the root-chaining tooth; the
//! node owns the `Cell -> CellRow` decode. The two meet at the serde wire
//! (`MirrorBatch`).
//!
//! ## What is in here
//!
//! 1. [`Domain`] + [`MemCell`] — the universal-memory model
//!    (`docs/UNIVERSAL-MEMORY.md`): ONE multiset over `Domain × κ`, the honest
//!    single-relation form of all dregg state.
//! 2. [`CellRow`] / [`TurnRow`] / [`CapRow`] — the typed projections of the
//!    commit log's `CommitRecord` + `Cell` + `CapabilityRef` (the query sugar
//!    over the universal table).
//! 3. [`MirrorBatch`] — one verified turn's worth of mirror rows, the serde unit
//!    the node ships into postgres (Tier B1, the mirror).
//! 4. [`RootChain`] — the Tier C tooth: the post-state root of turn *N* is the
//!    pre-state root of turn *N+1*; a batch that does not chain is refused. This
//!    is `snapshot.rs`'s `claimed_root` anti-substitution discipline, in SQL's
//!    write path.
//! 5. [`ddl`] — the schema as emittable SQL (so the extension ships its own
//!    `CREATE TABLE`/`CREATE POLICY`, generated from the same Rust that defines
//!    the rows — no schema drift between code and DDL).

use serde::{Deserialize, Serialize};

// ============================================================================
// 1. The universal-memory model — ONE multiset over Domain × κ.
// ============================================================================
//
// docs/UNIVERSAL-MEMORY.md proves dregg's whole state is one Blum multiset over
// `Domain × κ`, with the map roots as derived boundary views. A future state
// component is a NEW DOMAIN VALUE, never a new table. So this enum is the whole
// address space of dregg memory, and `MemCell` is one cell of it.

/// The memory domain — the `Domain` half of the universal `(domain, key)`
/// address (`docs/UNIVERSAL-MEMORY.md`). A new state component is a new VARIANT
/// here, never a new table; that is the whole point of the collapse.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Domain {
    /// Cell registers / scalar state (balance, nonce, field slots).
    Registers,
    /// The openable sorted heap maps.
    Heap,
    /// Capability c-lists (the delegation graph lives here).
    Caps,
    /// Spent-note nullifiers (the no-double-spend domain).
    Nullifiers,
    /// Collection / index roots.
    Index,
}

impl Domain {
    /// The stable SQL/tag string. Load-bearing: the tag is what keeps the flat
    /// untagged address space from aliasing (`docs/UNIVERSAL-MEMORY.md`: a cap
    /// check at key 7 must NOT read the nullifier value at 7).
    pub fn tag(self) -> &'static str {
        match self {
            Domain::Registers => "registers",
            Domain::Heap => "heap",
            Domain::Caps => "caps",
            Domain::Nullifiers => "nullifiers",
            Domain::Index => "index",
        }
    }

    /// Parse a tag back to a domain (fail-closed: unknown tag ⇒ `None`).
    pub fn from_tag(s: &str) -> Option<Domain> {
        Some(match s {
            "registers" => Domain::Registers,
            "heap" => Domain::Heap,
            "caps" => Domain::Caps,
            "nullifiers" => Domain::Nullifiers,
            "index" => Domain::Index,
            _ => return None,
        })
    }

    /// Every domain, for exhaustive iteration (boundary-root derivation).
    pub const ALL: [Domain; 5] = [
        Domain::Registers,
        Domain::Heap,
        Domain::Caps,
        Domain::Nullifiers,
        Domain::Index,
    ];
}

/// One cell of the universal memory: a `(domain, collection, key) -> Option ν`
/// entry. `value == None` is the "absent" cell (`none` in the Lean model);
/// `Some` is a present cell. `last_ordinal` ties it to the turn that produced it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemCell {
    pub domain: Domain,
    /// The collection id (e.g. the cell, the map) — `collection_id` in the
    /// concrete `addr = hash[domain_tag, collection_id, key]`.
    pub collection: Vec<u8>,
    /// The key within the domain (`κ`).
    pub key: Vec<u8>,
    /// `Some(ν)` = present cell, `None` = absent.
    pub value: Option<Vec<u8>>,
    /// The turn ordinal that produced this cell's value.
    pub last_ordinal: u64,
}

// ============================================================================
// 2. Typed projections — the query sugar over the universal table.
// ============================================================================

/// A turn row — the SQL projection of `persist::CommitRecord`
/// (`persist/src/commit_log.rs`). The authority for "what verified turns
/// happened"; every state row is reconcilable to one of these by `last_ordinal`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TurnRow {
    pub ordinal: u64,
    pub height: u64,
    pub block_id: [u8; 32],
    pub block_executed_up_to: u64,
    pub turn_hash: [u8; 32],
    pub creator: [u8; 32],
    pub receipt_hash: [u8; 32],
    /// The canonical ledger root AFTER this turn (`CommitRecord::ledger_root`).
    /// This is the post-state commitment that the next turn must chain onto.
    pub ledger_root: [u8; 32],
    /// The ledger root BEFORE this turn (the prior turn's `ledger_root`, or the
    /// genesis root for ordinal 0). Carried so the chaining tooth ([`RootChain`])
    /// can verify the batch links to the head without a separate lookup.
    pub prev_root: [u8; 32],
}

/// A cell row — the latest post-image of one cell. The SQL projection of
/// `dregg_cell::Cell` (`cell/src/cell.rs`); the heavy decode (`Cell` ⟶ this)
/// happens node-side. `cell_root` is the cell's commitment, a leaf of
/// `ledger_root`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellRow {
    pub cell_id: [u8; 32],
    pub mode: String,
    pub balance: i64,
    pub nonce: u64,
    /// Canonical field bytes (`CellState` field slots), authoritative.
    pub fields: Vec<u8>,
    /// Decoded field slots as JSON (query convenience; `fields` is canonical).
    pub fields_json: Option<String>,
    pub heap: Option<Vec<u8>>,
    pub program: Option<Vec<u8>>,
    pub verification_key: Option<Vec<u8>>,
    /// Decoded permissions as JSON (`cell/src/cell.rs` `Permissions`).
    pub permissions_json: Option<String>,
    pub delegate: Option<[u8; 32]>,
    pub lifecycle: String,
    pub last_ordinal: u64,
    pub cell_root: [u8; 32],
}

/// A capability row — one `CapabilityRef` in a cell's `CapabilitySet`
/// (`cell/src/capability.rs`). `(holder, slot)` is the c-list address; the
/// `holder -> target` edges are the delegation graph.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapRow {
    pub holder: [u8; 32],
    pub slot: u32,
    pub target: [u8; 32],
    /// `AuthRequired` as JSON.
    pub permissions_json: String,
    pub breadstuff: Option<[u8; 32]>,
    pub expires_at: Option<u64>,
    /// `allowed_effects` (the attenuation) as JSON, if present.
    pub allowed_effects_json: Option<String>,
    pub stored_epoch: Option<u64>,
    pub last_ordinal: u64,
}

// ============================================================================
// 3. MirrorBatch — one verified turn's mirror rows (the Tier B1 wire unit).
// ============================================================================

/// Everything the mirror writes for ONE verified turn: the turn row plus the
/// post-images of every cell / capability / memory cell it touched. This is the
/// serde unit the node ships from its commit-log sink into postgres (Tier B1).
///
/// The node produces this AFTER the kernel verified the turn — so by the time a
/// `MirrorBatch` exists, the spine invariant already holds for it: these rows
/// ARE a verified-turn post-image. The mirror's job is only to (a) refuse a
/// batch that does not chain onto the current head ([`RootChain::extend`]), and
/// (b) write it read-only-to-apps. It never decides authorization or execution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MirrorBatch {
    pub turn: TurnRow,
    pub cells: Vec<CellRow>,
    pub caps: Vec<CapRow>,
    pub memory: Vec<MemCell>,
}

impl MirrorBatch {
    /// Assemble a batch from a [`TurnRow`] and the already-projected post-image
    /// rows of the turn, stamping every row with the turn's ordinal and running
    /// the structural [`Self::check_ordinals`] tooth before returning.
    ///
    /// This is the pg-side assembly point: the node owns the heavy
    /// `dregg_cell::Cell -> CellRow / CapRow / MemCell` decode (it has
    /// `dregg-cell`; this crate deliberately does not — see the module header),
    /// then hands the decoded rows here so the *ordinal-stamping discipline* and
    /// the *well-formedness gate* live in ONE place (this crate, the SQL-shape
    /// home) rather than being re-implemented at each node sink. The returned
    /// batch is guaranteed to satisfy `check_ordinals` (every row carries the
    /// turn's ordinal); a [`RootChain`] is what then admits or refuses it against
    /// the head.
    ///
    /// Stamping is authoritative: any `last_ordinal` the caller left on a row is
    /// OVERWRITTEN with `turn.ordinal`, so a node cannot accidentally ship a row
    /// stamped for a different turn — the only way `check_ordinals` can then fail
    /// is an internal bug, which surfaces as `Err`.
    pub fn from_parts(
        turn: TurnRow,
        mut cells: Vec<CellRow>,
        mut caps: Vec<CapRow>,
        mut memory: Vec<MemCell>,
    ) -> Result<Self, String> {
        let o = turn.ordinal;
        for c in &mut cells {
            c.last_ordinal = o;
        }
        for c in &mut caps {
            c.last_ordinal = o;
        }
        for m in &mut memory {
            m.last_ordinal = o;
        }
        let batch = MirrorBatch {
            turn,
            cells,
            caps,
            memory,
        };
        batch.check_ordinals()?;
        Ok(batch)
    }

    /// A structural well-formedness check the mirror runs before writing:
    /// every touched row must reference THIS turn's ordinal (no smuggling a row
    /// from a different turn into a batch). Returns the first offending row's
    /// description, or `Ok(())`.
    pub fn check_ordinals(&self) -> Result<(), String> {
        let o = self.turn.ordinal;
        for c in &self.cells {
            if c.last_ordinal != o {
                return Err(format!(
                    "cell {} carries ordinal {}, batch is {o}",
                    hex(&c.cell_id),
                    c.last_ordinal
                ));
            }
        }
        for c in &self.caps {
            if c.last_ordinal != o {
                return Err(format!(
                    "cap ({},{}) carries ordinal {}, batch is {o}",
                    hex(&c.holder),
                    c.slot,
                    c.last_ordinal
                ));
            }
        }
        for m in &self.memory {
            if m.last_ordinal != o {
                return Err(format!(
                    "mem cell ({},{}) carries ordinal {}, batch is {o}",
                    m.domain.tag(),
                    hex(&m.key),
                    m.last_ordinal
                ));
            }
        }
        Ok(())
    }

    /// The touched-cell post-images as the jsonb the Tier-C `dregg.commit_log`
    /// trigger consumes (`docs/PG-DREGG.md` §10; [`ddl::tier_c`]). Each element
    /// carries the fields `dregg.apply_verified_turn` reads to materialize the
    /// cell via `dregg.merge_cell`: `cell_id` / `cell_root` / `fields` as hex,
    /// `mode` / `lifecycle` as text, `balance` / `nonce` as numbers, and the
    /// `fields_json` object verbatim. This is the SQL-submission face of the
    /// SAME post-image the Tier-B mirror writes; both materialize identically, so
    /// the verified-store path and the mirror path agree by construction.
    pub fn cells_json(&self) -> String {
        let cells: Vec<serde_json::Value> = self
            .cells
            .iter()
            .map(|c| {
                serde_json::json!({
                    "cell_id": hex(&c.cell_id),
                    "mode": c.mode,
                    "balance": c.balance,
                    "nonce": c.nonce,
                    "fields": hex(&c.fields),
                    "fields_json": c
                        .fields_json
                        .as_deref()
                        .and_then(|s| serde_json::from_str::<serde_json::Value>(s).ok()),
                    "lifecycle": c.lifecycle,
                    "cell_root": hex(&c.cell_root),
                })
            })
            .collect();
        serde_json::Value::Array(cells).to_string()
    }
}

// ============================================================================
// 4. RootChain — the anti-substitution tooth (Tier C, applied read-only in B).
// ============================================================================
//
// snapshot.rs binds a reconstructed ledger to a `claimed_root` and fails closed
// on mismatch. CommitRecord's ledger_root "binds the record to a concrete
// post-state". The SAME discipline, in the mirror's write path: the post-state
// root of turn N MUST be the pre-state root of turn N+1, so the turns table is a
// hash chain a light client could itself walk. A `MirrorBatch` whose `prev_root`
// does not equal the current head root is REFUSED — that is how the mirror
// detects a tampered / reordered / forged batch WITHOUT re-running the verifier.
// (Tier C adds the verifier on top; the chain tooth is the cheap structural half
// that even the read-only mirror enforces.)

/// The running head of the mirror's root chain. `None` before any turn (the
/// next batch is genesis); `Some(root)` is the post-state root of the last
/// accepted turn.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RootChain {
    head: Option<[u8; 32]>,
    next_ordinal: u64,
}

/// Why a batch was refused by the chain tooth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChainRefusal {
    /// The batch's ordinal is not the next expected one (gap or replay).
    OrdinalGap { expected: u64, got: u64 },
    /// The batch's pre-state root does not equal the current head — a tampered
    /// or reordered batch.
    RootMismatch { head: [u8; 32], prev: [u8; 32] },
    /// The batch's own ordinals are inconsistent (a row from a different turn).
    Malformed(String),
}

impl core::fmt::Display for ChainRefusal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ChainRefusal::OrdinalGap { expected, got } => {
                write!(f, "ordinal gap: expected {expected}, got {got}")
            }
            ChainRefusal::RootMismatch { head, prev } => write!(
                f,
                "root does not chain: head {}, batch prev_root {}",
                hex(head),
                hex(prev)
            ),
            ChainRefusal::Malformed(m) => write!(f, "malformed batch: {m}"),
        }
    }
}

impl RootChain {
    /// A fresh chain expecting genesis (ordinal 0).
    pub fn new() -> Self {
        RootChain {
            head: None,
            next_ordinal: 0,
        }
    }

    /// Resume a chain from a known head root and the next ordinal to expect
    /// (e.g. after restart, read from the mirror's current max-ordinal row).
    pub fn resume(head: [u8; 32], next_ordinal: u64) -> Self {
        RootChain {
            head: Some(head),
            next_ordinal,
        }
    }

    /// The current head post-state root, if any turns have been accepted.
    pub fn head(&self) -> Option<[u8; 32]> {
        self.head
    }

    /// The ordinal the chain next expects.
    pub fn next_ordinal(&self) -> u64 {
        self.next_ordinal
    }

    /// Attempt to extend the chain with a batch. Fail-closed: the batch is
    /// accepted ONLY if its ordinal is the next expected AND its `prev_root`
    /// equals the current head (genesis batch must carry `prev_root` matching
    /// the configured genesis root, here the all-zero/embedded one — the caller
    /// pins genesis by `resume`). On success the head advances to the batch's
    /// post-state `ledger_root`. On refusal the chain is UNCHANGED (so a bad
    /// batch cannot corrupt the head).
    pub fn extend(&mut self, batch: &MirrorBatch) -> Result<(), ChainRefusal> {
        if let Err(m) = batch.check_ordinals() {
            return Err(ChainRefusal::Malformed(m));
        }
        if batch.turn.ordinal != self.next_ordinal {
            return Err(ChainRefusal::OrdinalGap {
                expected: self.next_ordinal,
                got: batch.turn.ordinal,
            });
        }
        // The pre-state root of this batch must equal the chain head. For
        // genesis (head == None) the chain accepts whatever genesis root the
        // batch declares as prev_root and pins it (a `resume(genesis,0)` caller
        // makes this exact). For non-genesis, the roots MUST match.
        if let Some(head) = self.head {
            if batch.turn.prev_root != head {
                return Err(ChainRefusal::RootMismatch {
                    head,
                    prev: batch.turn.prev_root,
                });
            }
        }
        // The pure step gate is the single source of truth for the chain
        // discipline (also lifted into SQL as the Tier-C `dregg_verify_turn`
        // extension function — see [`verify_chain_step`]). Run it, then advance.
        verify_chain_step(
            self.head,
            self.next_ordinal,
            batch.turn.prev_root,
            batch.turn.ordinal,
        )?;
        // Accept: advance.
        self.head = Some(batch.turn.ledger_root);
        self.next_ordinal += 1;
        Ok(())
    }
}

/// The pure root-chain step gate — the anti-substitution tooth as a standalone
/// function over scalars, so it can be lifted verbatim into SQL.
///
/// This is the load-bearing "pg re-validates, never trusts" check
/// (`docs/PG-DREGG.md` §10, Tier C): given the current chain `head`
/// (`None` ⇒ genesis, no turns yet) and the `next_ordinal` the chain expects, a
/// candidate turn with pre-state `prev_root` and `ordinal` is admitted ONLY if
///
///   * its `ordinal` is exactly the next expected one (else a gap or replay), AND
///   * (non-genesis) its `prev_root` equals the head — the post-state root of
///     turn *N* IS the pre-state root of turn *N+1*, so the turns table is a hash
///     chain a light client could itself walk. A substituted / reordered / forged
///     batch breaks this and is REFUSED.
///
/// It decides nothing about the *contents* of the turn — that is the proof
/// verifier's job (the whole-chain IVC recursion, `circuit::ivc_turn_chain`; a
/// per-row STARK check is not realizable because a `CommitRecord` carries no
/// per-turn proof, `docs/PG-DREGG.md` §10.2). What it DOES enforce, on every row,
/// is that the row claims to chain onto the exact head the database already
/// holds — the structural half of the spine invariant the read-only mirror can
/// (and the Tier-C trigger does) enforce on a live database without re-running a
/// prover. Fail-closed: any deviation is a refusal, and the caller never
/// advances the head on a refusal.
///
/// `RootChain::extend` calls this so the in-process chain and the SQL gate are
/// provably the same check.
pub fn verify_chain_step(
    head: Option<[u8; 32]>,
    next_ordinal: u64,
    prev_root: [u8; 32],
    ordinal: u64,
) -> Result<(), ChainRefusal> {
    if ordinal != next_ordinal {
        return Err(ChainRefusal::OrdinalGap {
            expected: next_ordinal,
            got: ordinal,
        });
    }
    if let Some(head) = head {
        if prev_root != head {
            return Err(ChainRefusal::RootMismatch {
                head,
                prev: prev_root,
            });
        }
    }
    Ok(())
}

// ============================================================================
// 4b. Federation: a SUBSCRIBER re-validates a replicated chain (does not trust).
// ============================================================================
//
// docs/PG-DREGG.md §15 — federation via PostgreSQL logical replication. A
// subscriber tails a publisher's `dregg.turns`/`cells`/`capabilities`/`memory`
// (CREATE PUBLICATION / CREATE SUBSCRIPTION). The load-bearing soundness claim is
// that the anti-substitution tooth SURVIVES replication: it is STRUCTURAL ON THE
// `turns` ROWS (turn N's `ledger_root` == turn N+1's `prev_root`, ordinals dense),
// and logical replication copies those rows verbatim — so a subscriber can re-run
// the SAME `verify_chain_step` over its replicated rows and get the identical
// accept/refuse verdict the publisher did. A subscriber re-validates; it does not
// trust the stream. A reordered / substituted / dropped turn in the replication
// stream is caught by the tooth ON THE SUBSCRIBER SIDE.
//
// This is the realizable, circuit-free half every replica enforces (the Tier-C
// proof verify is the expensive complete half a *verifying* replica adds on top —
// see `crate::attest`). The function below is what a subscriber-side apply hook /
// periodic sweep runs over the replicated `dregg.turns` (read as `(ordinal,
// prev_root, ledger_root)` tuples, ordered by ordinal).

/// A replicated turn-chain row, the minimal projection a subscriber re-validates:
/// `(ordinal, prev_root, ledger_root)` from a replicated `dregg.turns`. (The full
/// [`TurnRow`] is what the publisher writes; the chain tooth needs only these
/// three, so a subscriber sweep reads only these.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChainLink {
    pub ordinal: u64,
    pub prev_root: [u8; 32],
    pub ledger_root: [u8; 32],
}

/// Re-validate a replicated chain on the SUBSCRIBER SIDE (docs/PG-DREGG.md §15).
/// Walks the replicated links (which MUST be ordered by ordinal) through the SAME
/// [`verify_chain_step`] the publisher ran, from the pinned `genesis` root. Returns
/// `Ok(head)` (the post-state root of the last link) if the whole replicated chain
/// re-validates, or `Err(ChainRefusal)` naming the FIRST link that does not chain —
/// a tampered / reordered / substituted / gapped replication stream is caught here,
/// locally, with NO call back to the publisher. This is the property §15 turns on:
/// *the RootChain tooth survives replication and lets a subscriber re-validate
/// locally*, because the tooth is defined on the replicated rows themselves.
///
/// `expect_count`, if `Some(n)`, additionally requires exactly `n` links (so a
/// subscriber can assert it received the whole published prefix, not a truncation
/// the per-link chaining alone would not notice at the tail).
pub fn revalidate_replicated_chain(
    genesis: [u8; 32],
    links: &[ChainLink],
    expect_count: Option<u64>,
) -> Result<Option<[u8; 32]>, ChainRefusal> {
    if let Some(n) = expect_count {
        if links.len() as u64 != n {
            return Err(ChainRefusal::Malformed(format!(
                "replicated chain has {} links, expected {n} (truncated or over-long stream)",
                links.len()
            )));
        }
    }
    let mut head: Option<[u8; 32]> = None;
    let mut next_ordinal: u64 = 0;
    // If the genesis is non-trivial, the first link's prev_root must equal it; we
    // express that by seeding the chain with genesis as the head ONLY when there
    // is a genesis to pin (an all-zero genesis matches the "no head yet" case for
    // ordinal 0, exactly as `RootChain::resume(genesis, 0)` does).
    if genesis != [0u8; 32] {
        head = Some(genesis);
    }
    for link in links {
        // For the very first link under an all-zero genesis, head is None ⇒ the
        // step gate accepts whatever prev_root ordinal-0 declares (genesis pin);
        // otherwise prev_root must equal the running head. This mirrors
        // `RootChain::extend` exactly.
        let effective_head = if next_ordinal == 0 && genesis == [0u8; 32] {
            None
        } else {
            head
        };
        verify_chain_step(effective_head, next_ordinal, link.prev_root, link.ordinal)?;
        head = Some(link.ledger_root);
        next_ordinal += 1;
    }
    Ok(head)
}

// ============================================================================
// 4c. Federation: the pg18 conflict counters DRIVE re-validation (compose).
// ============================================================================
//
// docs/PG-DREGG.md §15 + docs/PG-DREGG-PG18.md §10. The `dregg.replication_conflicts`
// view sums pg18's seven per-subscription `confl_*` counters into a
// `conflicts_total` alarm. The dregg federation model is SINGLE-WRITER FAN-OUT:
// the publisher is the only writer, subscribers RE-VALIDATE the replicated turn
// chain rather than accept local writes — so an apply conflict (a row the
// subscriber already holds, a missing update/delete target, a divergent origin)
// is, BY CONSTRUCTION, an ANOMALY: it means the stream is not the clean
// verified-turn feed the model assumes.
//
// The two halves SIT ON DIFFERENT LAYERS, and pg detects each:
//   * the CHAIN TOOTH (`revalidate_replicated_chain`) catches a substituted ROOT
//     (turn N's `ledger_root` ≠ turn N+1's `prev_root`) — a *structural* divergence
//     on the replicated `turns` rows;
//   * the CONFLICT COUNTERS catch an *apply-level* divergence pg itself detected
//     while applying the stream (before the rows even reach a shape the tooth reads).
//
// They COMPOSE: a non-zero `conflicts_total` is the signal that pg saw the feed
// diverge at apply time, and that is exactly when a subscriber should NOT trust
// its `dregg.turns` and MUST re-run the anti-substitution tooth over them. So the
// conflict alarm is not just a number to watch — it is the TRIGGER for the chain
// re-validation. This module is the pure, `cargo test`-provable half of that
// composition: the conflict report, the alarm/trigger decision, and the combined
// verdict. `lib.rs`'s `dregg_federation_health()` extern reads the REAL pg18
// `dregg.replication_conflicts` counters into a [`ConflictReport`], and — when the
// alarm fires — reads `dregg.turns` and runs [`revalidate_replicated_chain`],
// returning the [`FederationHealth`] this module composes.

/// One subscription's pg18 apply-conflict counters — the per-subscription row of
/// `dregg.replication_conflicts` (`docs/PG-DREGG-PG18.md` §10), the SQL-crossable
/// projection of `pg_stat_subscription_stats`'s seven `confl_*` columns. The
/// `total` is their sum (the view's `conflicts_total`), carried so a consumer does
/// not re-sum. A non-zero `total` on ANY subscription is a federation anomaly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubscriptionConflicts {
    /// The subscription name (`pg_subscription.subname`).
    pub subname: String,
    /// `confl_insert_exists` — an INSERT hit a row the subscriber already holds.
    pub insert_exists: i64,
    /// `confl_update_origin_differs` — an UPDATE target was last written by a
    /// different origin (a divergent writer — impossible in single-writer fan-out).
    pub update_origin_differs: i64,
    /// `confl_update_exists` — an UPDATE would collide with an existing row.
    pub update_exists: i64,
    /// `confl_update_missing` — an UPDATE's target row is absent (a gap in apply).
    pub update_missing: i64,
    /// `confl_delete_origin_differs` — a DELETE target was last written elsewhere.
    pub delete_origin_differs: i64,
    /// `confl_delete_missing` — a DELETE's target row is absent.
    pub delete_missing: i64,
    /// `confl_multiple_unique_conflicts` — a row violated several unique keys.
    pub multiple_unique_conflicts: i64,
    /// The view's `conflicts_total` — the sum of the seven kinds above.
    pub total: i64,
}

impl SubscriptionConflicts {
    /// Re-derive the total from the seven kinds (a self-check that the carried
    /// `total` matches the view's sum — a defensive cross-check, fail-loud if the
    /// view ever drifted from the seven columns it claims to sum).
    pub fn recomputed_total(&self) -> i64 {
        self.insert_exists
            + self.update_origin_differs
            + self.update_exists
            + self.update_missing
            + self.delete_origin_differs
            + self.delete_missing
            + self.multiple_unique_conflicts
    }

    /// `true` iff this subscription has any apply conflict — the per-subscription
    /// alarm bit.
    pub fn conflicted(&self) -> bool {
        self.total > 0
    }
}

/// The whole subscriber's federation conflict report — every subscription's
/// `dregg.replication_conflicts` row. Empty on a publisher (no subscriptions) or a
/// single node; populated on a subscriber. The aggregate [`Self::conflicts_total`]
/// is the mirror-facing alarm: non-zero ⇒ pg detected an apply-level divergence in
/// the replicated feed, which (in single-writer fan-out) means the stream is not
/// the clean verified-turn feed — investigate, AND re-validate the chain.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ConflictReport {
    pub subscriptions: Vec<SubscriptionConflicts>,
}

impl ConflictReport {
    /// The aggregate alarm value — the sum of every subscription's
    /// `conflicts_total`. Zero when no subscription has seen an apply conflict.
    pub fn conflicts_total(&self) -> i64 {
        self.subscriptions.iter().map(|s| s.total).sum()
    }

    /// `true` iff ANY subscription has a non-zero conflict count — the headline
    /// alarm bit. This is the TRIGGER condition for chain re-validation: pg saw the
    /// feed diverge at apply time, so the subscriber must not trust its replicated
    /// `dregg.turns` and re-runs the anti-substitution tooth over them.
    pub fn alarm(&self) -> bool {
        self.conflicts_total() > 0
    }

    /// The subscriptions that are actually conflicted (the offenders), for the
    /// alarm message — so the report names *which* subscription diverged.
    pub fn conflicted(&self) -> impl Iterator<Item = &SubscriptionConflicts> {
        self.subscriptions.iter().filter(|s| s.conflicted())
    }

    /// A terse human-readable alarm line: `clear (N subscriptions)` when no conflict,
    /// or `ALARM: <total> apply conflicts across [sub=k, …]` naming the offenders.
    pub fn alarm_line(&self) -> String {
        if !self.alarm() {
            return format!(
                "clear: {} subscription(s), 0 apply conflicts",
                self.subscriptions.len()
            );
        }
        let mut offenders: Vec<String> = self
            .conflicted()
            .map(|s| format!("{}={}", s.subname, s.total))
            .collect();
        offenders.sort();
        format!(
            "ALARM: {} apply conflict(s) on the replicated feed [{}] — \
             the stream diverged at apply time; re-validating the chain",
            self.conflicts_total(),
            offenders.join(", ")
        )
    }
}

/// The composed subscriber-side federation health verdict (`docs/PG-DREGG.md`
/// §15): the pg18 apply-conflict alarm AND — when it fires — the chain
/// re-validation it TRIGGERS. This is the realization of "the conflict counters
/// COMPOSE with the chain-tooth re-validation": the counters catch an apply-level
/// divergence, and that divergence is exactly what makes the subscriber re-run the
/// anti-substitution tooth over its replicated `dregg.turns`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FederationHealth {
    /// No subscription reported an apply conflict. The feed is, at the apply layer,
    /// the clean single-writer fan-out the model assumes. (The chain tooth is NOT
    /// re-run here on the alarm path — it is the *triggered* check; a deployment may
    /// still run `revalidate_replicated_chain` on its own periodic schedule, which
    /// this verdict does not preclude.) Carries the subscription count for context.
    Clear { subscriptions: usize },
    /// pg detected apply conflicts (`conflicts_total > 0`) AND the triggered chain
    /// re-validation then PASSED: the replicated `dregg.turns` still chains from
    /// genesis to `head`. The apply divergence did not (yet) corrupt the turn chain
    /// the subscriber re-validates — but it IS an anomaly the operator must chase
    /// (a conflicting writer, a botched bootstrap), so the alarm still fires.
    ConflictsButChainIntact {
        conflicts_total: i64,
        alarm: String,
        head: Option<[u8; 32]>,
    },
    /// pg detected apply conflicts AND the triggered chain re-validation REFUSED:
    /// the replicated turn chain does not re-validate locally. This is the severe
    /// case — the apply-level divergence the counters saw coincides with a chain the
    /// tooth rejects (a substituted / reordered / gapped turn). The subscriber must
    /// NOT trust its mirror. Carries both the alarm and the refusal reason.
    ConflictsAndChainBroken {
        conflicts_total: i64,
        alarm: String,
        refusal: ChainRefusal,
    },
}

impl FederationHealth {
    /// `true` iff the operator must act — any non-clear verdict (the alarm fired,
    /// whether or not the chain itself still re-validated).
    pub fn needs_attention(&self) -> bool {
        !matches!(self, FederationHealth::Clear { .. })
    }

    /// `true` iff the replicated mirror is NOT safe to trust — apply conflicts AND a
    /// chain the tooth refuses. The hardest signal: stop serving from this replica.
    pub fn chain_broken(&self) -> bool {
        matches!(self, FederationHealth::ConflictsAndChainBroken { .. })
    }

    /// A one-line operator-facing summary of the composed verdict.
    pub fn summary(&self) -> String {
        match self {
            FederationHealth::Clear { subscriptions } => {
                format!(
                    "ok: federation healthy — {subscriptions} subscription(s), 0 apply conflicts"
                )
            }
            FederationHealth::ConflictsButChainIntact {
                conflicts_total,
                head,
                ..
            } => format!(
                "ALARM ({conflicts_total} apply conflict(s)) but chain re-validates: head={}",
                head.map(|h| hex(&h))
                    .unwrap_or_else(|| "<empty>".to_string())
            ),
            FederationHealth::ConflictsAndChainBroken {
                conflicts_total,
                refusal,
                ..
            } => format!(
                "CRITICAL ({conflicts_total} apply conflict(s)) AND chain REFUSED: {refusal}"
            ),
        }
    }
}

/// Compose the federation health verdict from a [`ConflictReport`] and a
/// re-validation closure (`docs/PG-DREGG.md` §15) — the PURE composition the
/// `dregg_federation_health()` extern realizes over live pg.
///
/// This is the load-bearing wiring: the pg18 apply-conflict counters DRIVE the
/// chain re-validation. If the report is clear (no apply conflict), the feed is —
/// at the apply layer — the clean single-writer fan-out the model assumes, and we
/// return [`FederationHealth::Clear`] WITHOUT running the (then-unnecessary) tooth.
/// If the alarm fires (`conflicts_total > 0`), pg saw the feed diverge at apply
/// time, so we TRIGGER `revalidate` (the subscriber's `revalidate_replicated_chain`
/// over its replicated `dregg.turns`) and fold its verdict into the result: the
/// chain either still re-validates (anomaly to chase, but the turn chain is intact)
/// or it does not (the severe, do-not-trust case).
///
/// `revalidate` is a closure so this stays postgres-free and `cargo test`-provable:
/// the extern passes a closure that reads `dregg.turns` and calls
/// `revalidate_replicated_chain`; a test passes a closure that returns a canned
/// chain verdict. The TRIGGER LOGIC — alarm ⇒ re-validate, clear ⇒ skip — lives
/// HERE, proven once, the same in the extern and the test.
pub fn federation_health(
    report: &ConflictReport,
    revalidate: impl FnOnce() -> Result<Option<[u8; 32]>, ChainRefusal>,
) -> FederationHealth {
    if !report.alarm() {
        // No apply conflict ⇒ the feed is clean at the apply layer; the chain tooth
        // is the *triggered* check, so it is not run on this path. (A deployment may
        // still sweep on its own schedule.)
        return FederationHealth::Clear {
            subscriptions: report.subscriptions.len(),
        };
    }
    // The alarm fired: pg detected an apply-level divergence. The subscriber must
    // not trust its replicated turns — re-run the anti-substitution tooth NOW.
    let conflicts_total = report.conflicts_total();
    let alarm = report.alarm_line();
    match revalidate() {
        Ok(head) => FederationHealth::ConflictsButChainIntact {
            conflicts_total,
            alarm,
            head,
        },
        Err(refusal) => FederationHealth::ConflictsAndChainBroken {
            conflicts_total,
            alarm,
            refusal,
        },
    }
}

// ============================================================================
// 5. DDL emission — the schema generated from the same Rust that defines rows.
// ============================================================================
//
// The extension ships its own CREATE TABLE / CREATE POLICY so there is no drift
// between the row types above and the SQL. This returns the Tier B schema as a
// single string; the #[pg_extern] `dregg_install_schema()` runs it via SPI, and
// `pg-dregg/sql/schema-tierB.sql` is the human-readable mirror of it.

pub mod ddl {
    /// The Tier B schema (tables + indices + RLS policies + the write-lockdown
    /// role model). Idempotent (`IF NOT EXISTS`), so it is safe to re-run.
    /// Mirrors `pg-dregg/sql/schema-tierB.sql`; kept here so the extension can
    /// install it without shipping a separate file.
    pub fn tier_b() -> String {
        // Generated from the row types in the parent module. Kept terse here;
        // the file `sql/schema-tierB.sql` carries the fully-commented form.
        let mut s = String::new();
        s.push_str("CREATE SCHEMA IF NOT EXISTS dregg;\n");
        s.push_str("DO $$ BEGIN CREATE ROLE dregg_reader NOLOGIN; EXCEPTION WHEN duplicate_object THEN NULL; END $$;\n");
        // The kernel is the VERIFIED writer (the SECURITY DEFINER target in Tier
        // C). The read-side RLS gates APPLICATIONS, not the writer that produced
        // the post-image; the kernel writes verified-turn rows wholesale, so it
        // is BYPASSRLS. In Tier C even the kernel's writes still pass the
        // dregg_verify_turn CHECK (schema-tierC.sql) — RLS is the wrong tool to
        // gate them; the verifier is. (If the role pre-exists without the
        // attribute, ALTER lifts it.)
        s.push_str("DO $$ BEGIN CREATE ROLE dregg_kernel NOLOGIN BYPASSRLS; EXCEPTION WHEN duplicate_object THEN ALTER ROLE dregg_kernel BYPASSRLS; END $$;\n");
        s.push_str(TURNS);
        s.push_str(CELLS);
        s.push_str(CAPS);
        s.push_str(MEMORY);
        s.push_str(MERGE_CELL);
        s.push_str(VIEWS);
        s.push_str(RLS);
        s
    }

    /// The dregg-developer query surface: views that make the "your node IS your
    /// postgres" story good. Each is a plain SELECT over the Tier-B tables, so it
    /// inherits the read-side RLS of the tables it draws from. Emitted as part of
    /// [`tier_b`]; mirrored in `sql/schema-tierB.sql` (anti-drift test below).
    pub const VIEWS_SQL: &str = VIEWS;

    /// The Tier C schema (`docs/PG-DREGG.md` §10) — the verified-store gate.
    /// Makes `dregg.commit_log` the ONE door to state: its `BEFORE INSERT`
    /// trigger runs the real chain re-validator (`dregg_verify_turn`, the
    /// extension function backed by [`super::verify_chain_step`]) and, on
    /// acceptance, records the turn row and materializes the post-image cells via
    /// the pg18 `dregg.merge_cell` upsert — all in the same transaction. A row
    /// reaches the state tables ONLY through this trigger; the privilege lockdown
    /// (Tier B) forbids every other write path.
    ///
    /// Builds on [`tier_b`] (the tables must exist first). Idempotent. Mirrors
    /// `pg-dregg/sql/schema-tierC.sql` (the human-readable, fully-commented form);
    /// the load-bearing pieces are pinned together by the anti-drift test.
    ///
    /// What `dregg_verify_turn` does and does NOT do is documented honestly on
    /// [`super::verify_chain_step`]: it enforces the structural anti-substitution
    /// chain on every row (the realizable, per-row half of the spine invariant),
    /// NOT a per-turn STARK re-proof (a `CommitRecord` carries no per-turn proof;
    /// proof soundness is the whole-chain IVC light client's job, §10.2). It is
    /// NOT stubbed to TRUE — the forbidden failure mode (§10.3) — it runs the same
    /// gate the in-process `RootChain` runs, so a tampered/reordered batch is
    /// refused by the database engine itself.
    pub fn tier_c() -> String {
        let mut s = String::new();
        s.push_str(COMMIT_LOG);
        s.push_str(APPLY_VERIFIED_TURN);
        s.push_str(TIER_C_TRIGGER);
        s.push_str(TIER_C_VIEWS);
        s.push_str(TIER_C_GRANTS);
        s
    }

    /// The Tier-C PROOF store (`docs/PG-DREGG.md` §10.2) — the `dregg.turn_proofs`
    /// table the node-side whole-chain PROOF producer
    /// ([`crate::turn_proofs::TurnProofProducer`], S2) writes and the range-attest
    /// SRF (`dregg_attest_range`) reads. ONE row per folded finalized WINDOW: a
    /// recursive proof (`proof bytea`) attesting that all turns in `[lo, hi]`
    /// executed correctly and the root chain advanced from `genesis_root` to
    /// `final_root`, with the `vk` anchor the SRF verifies it against.
    ///
    /// This is the ORTHOGONAL soundness half the per-row chain tooth
    /// (`dregg_verify_turn`) honestly does NOT do (§10.2): a `CommitRecord` carries
    /// no per-turn STARK, so the proof gate is whole-chain (one proof per window),
    /// not per-row. The table is the durable handoff from the producer to the SRF.
    /// Builds on [`tier_b`] (the role model). Idempotent. (The producer is node-side
    /// / a `tier-c` build; the table + its grants ship here so the SRF has somewhere
    /// to read from regardless of which build wrote the rows.)
    ///
    /// Write-locked to the kernel (the producer runs as `dregg_kernel`); readable by
    /// reader + kernel so the SRF can join it. A row is append-mostly (a producer
    /// extends the proven prefix); the windows are dense + non-overlapping by the
    /// producer's watermark discipline (`[lo,hi]` then `[hi+1,…]`).
    pub fn turn_proofs() -> String {
        TURN_PROOFS.to_string()
    }

    /// DECLARED-BUT-SPINE-ENFORCED invariants on the materialized state, using two
    /// pg18 constraint features (`docs/PG-DREGG-PG18.md` §13.1) — the lock-light,
    /// non-enforcing way to make the verified turn's guarantees LEGIBLE to schema
    /// tooling, `\d dregg.cells`, and an auditor, WITHOUT the database re-deciding
    /// (or worse, *fighting*) the verified writer.
    ///
    /// Two pg18-new constraint forms, each chosen for a stated reason:
    ///
    /// * **`CHECK (...) NOT ENFORCED`** (pg18; Amul Sul) — declares the
    ///   non-negativity / well-formedness invariants the spine ALREADY guarantees
    ///   (a materialized balance is never negative; a nonce is never negative; the
    ///   `fields_json.balance` projection agrees with the `balance` column). The
    ///   enforcer is the verified TURN (the executor's transition function +
    ///   conservation), NOT postgres — so the constraint is `NOT ENFORCED`: it is a
    ///   *documented, machine-readable* invariant the catalog now carries, but pg
    ///   does not pay a per-write CHECK and (crucially) cannot REFUSE a verified
    ///   post-image that some future legitimate turn shape produces. Enforcing it in
    ///   pg would be a SECOND, weaker authority fighting the spine — exactly the
    ///   double-enforcement anti-pattern (`docs/PG-DREGG.md` §8). Declaring it
    ///   `NOT ENFORCED` is the honest pg18 idiom: the invariant lives in the catalog
    ///   as documentation + a target a DBA can later `ALTER ... ENFORCED` to spot-audit.
    ///
    /// * **`ADD CONSTRAINT ... NOT NULL ... NOT VALID` + `VALIDATE CONSTRAINT`**
    ///   (pg18; Rushabh Lathia, Jian He) — the LOCK-LIGHT migration path for adding
    ///   a NOT NULL constraint to the ALREADY-POPULATED `dregg.cells` without an
    ///   `ACCESS EXCLUSIVE` full-table scan blocking the live read path. pg18 lets a
    ///   NOT NULL constraint be added `NOT VALID` (a brief lock to record it, no
    ///   scan), after which a separate `VALIDATE CONSTRAINT` checks existing rows
    ///   under a weaker `SHARE UPDATE EXCLUSIVE` lock that does not block reads or
    ///   the mirror's writes. Here it pins `cell_root` NOT NULL as a named table
    ///   constraint (the column is already NOT NULL at CREATE, but a named
    ///   constraint is what an auditor references and what a future column would be
    ///   added through) — demonstrating the exact pre-18-impossible two-step on a
    ///   live mirror.
    ///
    /// Builds on [`tier_b`] (the `dregg.cells` table must exist). Idempotent: each
    /// constraint is added only if absent (a `DO` block guarded on the catalog), so
    /// re-running is safe and a fresh install validates against an empty table
    /// instantly. Run by a DBA/migration role (it `ALTER`s a kernel-owned table).
    pub fn invariants() -> String {
        INVARIANTS.to_string()
    }

    /// The WRITE-path outbox (`docs/PG-DREGG.md` §11; the first-class
    /// bidirectional piece). A pg-user submits a SIGNED turn FROM postgres by
    /// enqueuing it here through `dregg.submit_turn`; the node tails the queue,
    /// executes it through the REAL verified executor, and the resulting
    /// post-image flows back via the mirror. The spine is preserved: postgres
    /// NEVER executes — it only enqueues an intent that the verifier must accept.
    ///
    /// RLS gates submission: a role may enqueue a turn ONLY for an `agent` cell
    /// its presented capability admits `submit` on (the `submit_gate` policy),
    /// so a pg role can submit exactly the turns its caps authorize and no more.
    /// Reads stay free SQL; writes stay verified-only.
    ///
    /// Builds on [`tier_b`] (the role model). Idempotent. The node-side drainer
    /// (queue → `execute_via_producer` → mirror) is the M3 follow-up
    /// (`docs/PG-DREGG.md` §11.x); this installs the enqueue half + its gate.
    pub fn write_outbox() -> String {
        let mut s = String::new();
        s.push_str(SUBMIT_QUEUE);
        s.push_str(SUBMIT_QUEUE_RLS);
        s
    }

    /// The pg17 LOGIN EVENT TRIGGER authz binding (`docs/PG-DREGG-PG18.md` §6):
    /// bind a connecting pg role to its dregg agent identity AT CONNECTION TIME.
    /// A `dregg.role_identity` table maps `pg_role -> (agent cell, default token)`;
    /// an `event_trigger ON login` reads the connecting `session_user`'s row and
    /// `SET`s the `dregg.token` / `dregg.agent` session GUCs from it, so every
    /// statement in the session is already gated by that role's capability without
    /// the application having to present the token itself. This is the pg-native
    /// front door: the database binds identity → capability the moment you connect.
    ///
    /// Fail-OPEN-to-DENY: a role with no `role_identity` row gets NO token set, so
    /// `dregg_admits` reads an absent `dregg.token` ⇒ deny (the RLS gate shows it
    /// zero rows). Binding a token never widens authority — the token still has to
    /// verify against the issuer key and survive the caveats/revocation. The login
    /// trigger only SAVES the application from presenting a token it would have
    /// presented anyway; it cannot mint authority.
    ///
    /// pg17 login event triggers are a server feature; the trigger function is
    /// SECURITY DEFINER (it reads the mapping table the connecting role may not
    /// see) and is written defensively so a fault never locks every role out
    /// (it wraps the body so an error in the hook does not abort the login —
    /// `docs/PG-DREGG-PG18.md` §6.1, the lockout-avoidance discipline). Requires
    /// [`tier_b`] (the role model). Idempotent.
    pub fn login_binding() -> String {
        let mut s = String::new();
        s.push_str(ROLE_IDENTITY);
        s.push_str(LOGIN_HOOK);
        s
    }

    /// The FEDERATION-via-logical-replication publication (`docs/PG-DREGG.md`
    /// §15) — the PUBLISHER side. Publishes the four state tables + `turns` so a
    /// subscriber postgres tails the verified-turn stream by PostgreSQL's own
    /// logical replication (federation-via-pg, no bespoke gossip): the publisher's
    /// `dregg.turns` hash chain IS the replicated feed, and a subscriber that tails
    /// it is a read replica of verified dregg state. Idempotent.
    ///
    /// The SUBSCRIBER side ([`federation_subscriber`]) is a runbook (it needs the
    /// publisher's connection string + `pg_createsubscriber`), NOT extension SQL,
    /// so it is emitted as a commented template. The load-bearing soundness claim —
    /// the `RootChain` anti-substitution tooth SURVIVES replication and lets a
    /// subscriber re-validate LOCALLY — is enforced by
    /// [`super::revalidate_replicated_chain`] (the subscriber-side sweep over the
    /// replicated `dregg.turns`), proven `cargo test`. A subscriber re-validates;
    /// it does not trust the stream.
    pub fn federation_publication() -> String {
        FED_PUBLICATION.to_string()
    }

    /// The FEDERATION SUBSCRIBER runbook (`docs/PG-DREGG.md` §15) — emitted as a
    /// commented template because standing up a subscriber needs the publisher's
    /// connection string and is a `pg_createsubscriber` operation, not in-database
    /// SQL the extension runs. It documents (a) the `pg_createsubscriber` bootstrap
    /// (convert a physical standby into a logical subscriber WITHOUT a fresh dump,
    /// pg17), (b) the `CREATE SUBSCRIPTION … WITH (failover = true)` that tails the
    /// publisher and survives its failover (pg17 failover slots), and (c) the
    /// subscriber-side re-validation sweep the extension function
    /// `dregg_revalidate_replicated_chain()` runs (over `super::revalidate_replicated_chain`).
    pub fn federation_subscriber(publisher_conninfo: &str) -> String {
        FED_SUBSCRIBER_TEMPLATE.replace("{PUBLISHER_CONNINFO}", publisher_conninfo)
    }

    /// The recommended pg18 `COPY … ON_ERROR ignore` bulk-load command for the
    /// OAuth→role bind map (`docs/PG-DREGG-PG18.md` §12), with the CSV path
    /// substituted. COPY needs a literal path + format, so — like the federation
    /// runbook — this is emitted as a ready-to-run template rather than executed by
    /// the extension. It loads `(pg_role, agent_hex, token)` rows into the
    /// `dregg.role_identity_load` staging table, SKIPPING malformed lines (pg18
    /// `ON_ERROR ignore` + `REJECT_LIMIT` + `LOG_VERBOSITY silent`) instead of
    /// aborting the whole load; the DBA then runs
    /// `SELECT * FROM dregg.promote_role_identity_load();` to validate + upsert each
    /// staged row through the audited `dregg.bind_role` seam. `reject_limit` caps
    /// how many bad rows are tolerated before the load DOES fail (0 ⇒ omit the cap,
    /// tolerate any number).
    pub fn load_role_identity_sql(csv_path: &str, reject_limit: u64) -> String {
        let limit = if reject_limit == 0 {
            String::new()
        } else {
            format!(", REJECT_LIMIT {reject_limit}")
        };
        LOAD_ROLE_IDENTITY_TEMPLATE
            .replace("{CSV_PATH}", csv_path)
            .replace("{REJECT_LIMIT}", &limit)
    }

    const LOAD_ROLE_IDENTITY_TEMPLATE: &str = r#"
-- BULK-LOAD the OAuth→role bind map via pg18 COPY ON_ERROR (docs/PG-DREGG-PG18.md
-- §12). Lands raw (pg_role, agent_hex, token) rows into the staging table,
-- SKIPPING malformed lines (a bad hex agent, a short row) instead of aborting:
TRUNCATE dregg.role_identity_load;
COPY dregg.role_identity_load (pg_role, agent_hex, token)
    FROM '{CSV_PATH}'
    WITH (FORMAT csv, HEADER true, ON_ERROR ignore, LOG_VERBOSITY silent{REJECT_LIMIT});
-- Then VALIDATE + promote each staged row through the audited bind seam (a row
-- whose agent_hex does not decode is skipped, never written unchecked):
SELECT * FROM dregg.promote_role_identity_load();   -- (promoted, skipped)
TRUNCATE dregg.role_identity_load;                  -- clear the staging table
"#;

    const FED_PUBLICATION: &str = r#"
-- FEDERATION via logical replication (docs/PG-DREGG.md §15) — the PUBLISHER.
-- The publisher's dregg.turns hash chain IS the replicated feed; a subscriber
-- that tails it is a read replica of VERIFIED dregg state. Publishing the four
-- state tables + turns is all the subscriber needs to re-validate locally.
DO $$ BEGIN
    CREATE PUBLICATION dregg_mirror
        FOR TABLE dregg.turns, dregg.cells, dregg.capabilities, dregg.memory;
EXCEPTION WHEN duplicate_object THEN
    -- Re-runnable: keep the existing publication (a DBA ALTERs it to add tables).
    NULL;
END $$;
-- pg18 logical-replication CONFLICT observability (docs/PG-DREGG-PG18.md §10).
-- The dregg federation model is single-writer fan-out: the publisher is the ONLY
-- writer, subscribers are read replicas that RE-VALIDATE the replicated turn
-- chain (`dregg_revalidate_replicated_chain`) rather than accept local writes —
-- so an apply CONFLICT (a row the subscriber already holds, a missing update
-- target, divergent origins) is, by construction, an ANOMALY: it means the
-- stream is not the clean verified-turn feed the model assumes. pg18 newly
-- COUNTS those conflicts per-subscription in `pg_stat_subscription_stats` (the
-- `confl_*` columns); this view surfaces them as a mirror-facing alarm, summing
-- the seven conflict kinds into `conflicts_total` so a non-zero value is an
-- immediate "the replicated feed diverged — investigate" signal that COMPOSES
-- with the chain-tooth re-validation (the tooth catches a substituted ROOT; the
-- conflict counters catch an apply-level divergence pg itself detected). Empty on
-- a publisher (no subscriptions); populated on a subscriber. A thin SELECT over
-- the stats view (no row data). (pg18-only: the confl_* columns are new in 18.)
CREATE OR REPLACE VIEW dregg.replication_conflicts AS
    SELECT s.subname,
           ss.confl_insert_exists,
           ss.confl_update_origin_differs,
           ss.confl_update_exists,
           ss.confl_update_missing,
           ss.confl_delete_origin_differs,
           ss.confl_delete_missing,
           ss.confl_multiple_unique_conflicts,
           ( coalesce(ss.confl_insert_exists,0)
           + coalesce(ss.confl_update_origin_differs,0)
           + coalesce(ss.confl_update_exists,0)
           + coalesce(ss.confl_update_missing,0)
           + coalesce(ss.confl_delete_origin_differs,0)
           + coalesce(ss.confl_delete_missing,0)
           + coalesce(ss.confl_multiple_unique_conflicts,0) )::bigint AS conflicts_total,
           ss.stats_reset
    FROM pg_stat_subscription_stats ss
    JOIN pg_subscription s ON s.oid = ss.subid;
-- The conflict alarm is an OPERATOR/KERNEL surface: the subscriber-side federation
-- health check (`dregg_federation_health`) reads it as the kernel role to compose
-- the apply-conflict alarm with the chain re-validation. The Tier-B GRANT-ALL ran
-- before this view existed (the publication installs separately), so grant it
-- explicitly here — exactly like the Tier-C views need TIER_C_GRANTS. It is a thin
-- stats view (no dregg row data; it reads pg_stat_subscription_stats), so the
-- kernel + reader may select it without an RLS concern.
GRANT SELECT ON dregg.replication_conflicts TO dregg_kernel, dregg_reader;
"#;

    const FED_SUBSCRIBER_TEMPLATE: &str = r#"
-- FEDERATION via logical replication (docs/PG-DREGG.md §15) — the SUBSCRIBER.
-- This is a RUNBOOK (it needs the publisher conninfo + pg_createsubscriber), not
-- extension SQL. Steps:
--
-- (1) Bootstrap from a consistent base with pg17 pg_createsubscriber (converts a
--     physical standby into a logical subscriber WITHOUT a fresh dump — the
--     subscriber starts already caught up to a consistent point of the WHOLE
--     mirror, which a real ledger needs):
--       pg_createsubscriber -d dregg -P "{PUBLISHER_CONNINFO}" \
--         --publication=dregg_mirror
--
-- (2) The subscription tails the publisher's verified-turn stream thereafter,
--     surviving publisher failover via pg17 FAILOVER SLOTS:
--       CREATE SUBSCRIPTION dregg_tail
--         CONNECTION '{PUBLISHER_CONNINFO}'
--         PUBLICATION dregg_mirror
--         WITH (failover = true);
--
-- (3) RE-VALIDATE, DO NOT TRUST. On apply (or a periodic sweep), the subscriber
--     walks its replicated dregg.turns through the SAME anti-substitution tooth
--     the publisher ran (super::revalidate_replicated_chain, surfaced as the
--     extension function dregg_revalidate_replicated_chain()), and alarms on a
--     head that does not chain. A corrupted / reordered / substituted replication
--     stream is caught HERE, locally, with no call back to the publisher —
--     replication is NOT a trust boundary the tooth assumes away.
--       SELECT * FROM dregg_revalidate_replicated_chain();  -- () | a refusal row
"#;

    const TURNS: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.turns (
    ordinal bigint PRIMARY KEY, height bigint NOT NULL, block_id bytea NOT NULL,
    block_executed_up_to bigint NOT NULL, turn_hash bytea NOT NULL UNIQUE,
    creator bytea NOT NULL, receipt_hash bytea NOT NULL,
    ledger_root bytea NOT NULL, prev_root bytea NOT NULL,
    committed_at timestamptz NOT NULL DEFAULT now());
CREATE INDEX IF NOT EXISTS turns_by_height  ON dregg.turns (height);
CREATE INDEX IF NOT EXISTS turns_by_creator ON dregg.turns (creator, ordinal);
"#;

    // DECLARED-BUT-SPINE-ENFORCED invariants (docs/PG-DREGG-PG18.md §13.1), using
    // two pg18-new constraint forms. These make the verified turn's guarantees
    // legible to the catalog / `\d` / an auditor WITHOUT pg re-deciding or fighting
    // the verified writer. See `ddl::invariants()` for the rationale of each.
    //
    // Each ALTER is wrapped in a DO block guarded on pg_constraint so the whole
    // thing is idempotent (re-running adds nothing) and a missing pg18 server
    // surfaces a clear error rather than a half-applied state.
    const INVARIANTS: &str = r#"
-- (1) NON-NEGATIVITY + PROJECTION-AGREEMENT as pg18 `CHECK ... NOT ENFORCED`.
-- The verified TURN already guarantees these (the executor's transition function
-- + conservation); we DECLARE them so the catalog documents the floor, but mark
-- them NOT ENFORCED so pg pays no per-write CHECK and never REFUSES a verified
-- post-image (the spine is the single enforcer — double-enforcement is the
-- anti-pattern, docs/PG-DREGG.md §8). A DBA may later `ALTER ... ENFORCED` to run
-- a one-off audit, or `VALIDATE` it, without changing the write path.
DO $$ BEGIN
    IF NOT EXISTS (SELECT 1 FROM pg_constraint WHERE conname = 'cells_balance_nonneg') THEN
        ALTER TABLE dregg.cells
            ADD CONSTRAINT cells_balance_nonneg CHECK (balance >= 0) NOT ENFORCED;
    END IF;
    IF NOT EXISTS (SELECT 1 FROM pg_constraint WHERE conname = 'cells_nonce_nonneg') THEN
        ALTER TABLE dregg.cells
            ADD CONSTRAINT cells_nonce_nonneg CHECK (nonce >= 0) NOT ENFORCED;
    END IF;
    -- The canonical/derived agreement: the read-side `fields_json.balance`
    -- projection must equal the authoritative `balance` column. A turn produces
    -- both consistently; declaring it NOT ENFORCED documents the projection
    -- contract the §4 generated-column `balance_field` rests on.
    IF NOT EXISTS (SELECT 1 FROM pg_constraint WHERE conname = 'cells_fields_balance_agree') THEN
        ALTER TABLE dregg.cells
            ADD CONSTRAINT cells_fields_balance_agree
            CHECK (fields_json IS NULL OR (fields_json->>'balance')::bigint = balance) NOT ENFORCED;
    END IF;
END $$;

-- (2) `cell_root` NOT NULL as a pg18 `NOT VALID` named constraint, then VALIDATE.
-- The column is already NOT NULL at CREATE, but a NAMED constraint is what an
-- auditor references and what a future added column would be onboarded through.
-- pg18 lets a NOT NULL constraint be added NOT VALID (a brief lock to RECORD it,
-- no full-table scan) and then VALIDATEd under a weaker lock that does not block
-- the live read path or the mirror's writes — the pre-18-impossible lock-light
-- two-step, demonstrated on the live, already-populated mirror.
DO $$ BEGIN
    IF NOT EXISTS (SELECT 1 FROM pg_constraint WHERE conname = 'cells_cell_root_present') THEN
        -- Step A: add NOT VALID — brief lock, no scan (pg18 NOT NULL NOT VALID).
        ALTER TABLE dregg.cells
            ADD CONSTRAINT cells_cell_root_present NOT NULL cell_root NOT VALID;
        -- Step B: VALIDATE existing rows under SHARE UPDATE EXCLUSIVE (reads + the
        -- mirror's writes proceed). On a fresh install the table is empty, so this
        -- is instant; on a large live mirror it does not block the read path.
        ALTER TABLE dregg.cells VALIDATE CONSTRAINT cells_cell_root_present;
    END IF;
END $$;
"#;

    // The cells table carries GENERATED COLUMNS for the canonical derived state
    // (docs/PG-DREGG-PG18.md §4) — pg-MAINTAINED projections that cannot drift
    // from the canonical bytea, since the database derives them from the pinned
    // expression. pg18 makes VIRTUAL (read-time, zero storage) the DEFAULT kind;
    // we pick STORED-vs-VIRTUAL per column by whether it must be indexed:
    //   * `cell_hex` — STORED, because it backs the canonical-order index
    //     `cells_by_canonical` (a virtual column cannot be indexed). Typed with
    //     the pg17 builtin C collation `pg_c_utf8` so its byte order matches the
    //     node's canonical lexicographic-on-bytes order — no ICU drift (§3).
    //   * `cell_root_hex` / `balance_field` — VIRTUAL (the pg18 default, named
    //     explicitly): they are read-side projections (the canonical view, the
    //     analytics face) that need no index, so paying write-time storage for
    //     them is waste. pg18 computes them on read, identically and drift-free.
    const CELLS: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.cells (
    cell_id bytea PRIMARY KEY, mode text NOT NULL, balance bigint NOT NULL,
    nonce bigint NOT NULL, fields bytea NOT NULL, fields_json jsonb,
    heap bytea, program bytea, verification_key bytea, permissions jsonb,
    delegate bytea, lifecycle text NOT NULL,
    last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    cell_root bytea NOT NULL,
    -- STORED: indexed by cells_by_canonical (a VIRTUAL column cannot be indexed).
    cell_hex text COLLATE pg_c_utf8
        GENERATED ALWAYS AS (encode(cell_id, 'hex')) STORED,
    -- VIRTUAL (pg18 default, explicit): read-side projections, no index needed.
    cell_root_hex text COLLATE pg_c_utf8
        GENERATED ALWAYS AS (encode(cell_root, 'hex')) VIRTUAL,
    balance_field bigint
        GENERATED ALWAYS AS ((fields_json->>'balance')::bigint) VIRTUAL);
-- One composite index serves BOTH "cells in this mode" AND "cells by balance,
-- any mode" — the latter via pg18's B-tree SKIP SCAN. `mode` (the leading column)
-- has tiny cardinality (Hosted | Sovereign), which is exactly skip scan's sweet
-- spot: a query that constrains only `balance` makes the planner skip through the
-- few distinct `mode` prefixes and range-scan `balance` within each, instead of
-- the pre-18 fallback (a full index scan or a seq scan). So the one index covers
-- the analytics surface's two hot access paths — `WHERE mode = …` and
-- `WHERE balance >= …` / `ORDER BY balance` — with no separate `balance` index to
-- maintain on the write path. (docs/PG-DREGG-PG18.md §8 — applied pg18 leverage.)
CREATE INDEX IF NOT EXISTS cells_by_mode_balance ON dregg.cells (mode, balance);
CREATE INDEX IF NOT EXISTS cells_fields_gin ON dregg.cells USING gin (fields_json);
-- The canonical-order index: byte-order on the hex id under the builtin C
-- provider, the ordering the node's canonical roots use (no ICU drift).
CREATE INDEX IF NOT EXISTS cells_by_canonical ON dregg.cells (cell_hex);
"#;

    const CAPS: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.capabilities (
    holder bytea NOT NULL, slot int NOT NULL, target bytea NOT NULL,
    permissions jsonb NOT NULL, breadstuff bytea, expires_at bigint,
    allowed_effects jsonb, stored_epoch bigint,
    last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    PRIMARY KEY (holder, slot));
CREATE INDEX IF NOT EXISTS caps_by_target ON dregg.capabilities (target);
"#;

    const MEMORY: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.memory (
    domain text NOT NULL, collection bytea NOT NULL, key bytea NOT NULL,
    value bytea, last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    PRIMARY KEY (domain, collection, key));
CREATE INDEX IF NOT EXISTS memory_by_domain ON dregg.memory (domain);
"#;

    // The PostgreSQL 18 MERGE-based cell upsert, shipped as a SECURITY DEFINER
    // function so the kernel writer materializes a post-image in ONE atomic
    // statement. The MERGE's `merge_action()` (pg17) reports which arm fired, and
    // pg18's `RETURNING WITH (OLD AS …, NEW AS …)` reads the PRE-image in the SAME
    // statement — so the function returns the action AND the exact balance delta
    // the materialization caused (`'INSERT +1000000'` / `'UPDATE -500'`), an
    // audit signal impossible pre-18 without a separate pre-read. Wrapping the
    // MERGE in a SQL function (rather than issuing it as a top-level statement) is
    // also what lets the mirror invoke it through a plain `SELECT
    // dregg.merge_cell(...)` — the MERGE status is consumed inside the function;
    // the caller sees a normal SELECT result. (docs/PG-DREGG-PG18.md §7.)
    //
    // pg18 form: `RETURNING WITH (OLD AS o, NEW AS n)` binds explicit aliases for
    // the pre/post image (the spec-standard pg18 syntax). It is strictly better
    // than the bare `old.`/`new.` pseudo-aliases — those only resolve because no
    // column is literally named `old`/`new`; the explicit alias is unambiguous and
    // future-proof. `dregg.merge_cell` (the human-readable string contract) is
    // unchanged; `dregg.merge_cell_delta` exposes the richer typed (action, balance
    // delta, nonce delta) tuple for the audit surface.
    const MERGE_CELL: &str = r#"
CREATE OR REPLACE FUNCTION dregg.merge_cell(
    p_cell_id bytea, p_mode text, p_balance bigint, p_nonce bigint,
    p_fields bytea, p_fields_json jsonb, p_lifecycle text,
    p_last_ordinal bigint, p_cell_root bytea) RETURNS text
LANGUAGE plpgsql AS $$
DECLARE v_action text; v_dbal bigint;
BEGIN
    MERGE INTO dregg.cells AS t
    USING (SELECT p_cell_id AS cell_id) AS s
      ON t.cell_id = s.cell_id
    WHEN MATCHED THEN UPDATE SET balance=p_balance, nonce=p_nonce,
        fields_json=p_fields_json, last_ordinal=p_last_ordinal, cell_root=p_cell_root
    WHEN NOT MATCHED THEN INSERT
        (cell_id,mode,balance,nonce,fields,fields_json,lifecycle,last_ordinal,cell_root)
        VALUES (p_cell_id,p_mode,p_balance,p_nonce,p_fields,p_fields_json,
                p_lifecycle,p_last_ordinal,p_cell_root)
    -- pg17 merge_action() = 'INSERT' | 'UPDATE'; pg18 RETURNING WITH binds the
    -- pre-image (o.balance is NULL on an insert), so n.balance - coalesce(o.balance,0)
    -- is the materialized delta — both read in the one atomic statement.
    RETURNING WITH (OLD AS o, NEW AS n)
        merge_action(), n.balance - coalesce(o.balance, 0)
        INTO v_action, v_dbal;
    RETURN v_action || ' ' || (CASE WHEN v_dbal >= 0 THEN '+' ELSE '' END) || v_dbal::text;
END $$;

-- The richer audit applicator: the SAME atomic MERGE, returning the typed delta
-- tuple (which arm fired, the signed balance delta, the signed nonce delta) the
-- pg18 RETURNING WITH (OLD/NEW) reads from the pre-image. The verified-store gate
-- and the streaming mirror both materialize through dregg.merge_cell (the string
-- form); this twin is the analytics face when a caller wants the numbers typed —
-- e.g. asserting conservation (the per-cell balance deltas of a transfer sum to
-- zero) directly off the applicator's report. (docs/PG-DREGG-PG18.md §7.)
CREATE OR REPLACE FUNCTION dregg.merge_cell_delta(
    p_cell_id bytea, p_mode text, p_balance bigint, p_nonce bigint,
    p_fields bytea, p_fields_json jsonb, p_lifecycle text,
    p_last_ordinal bigint, p_cell_root bytea,
    OUT action text, OUT balance_delta bigint, OUT nonce_delta bigint)
LANGUAGE plpgsql AS $$
BEGIN
    MERGE INTO dregg.cells AS t
    USING (SELECT p_cell_id AS cell_id) AS s
      ON t.cell_id = s.cell_id
    WHEN MATCHED THEN UPDATE SET balance=p_balance, nonce=p_nonce,
        fields_json=p_fields_json, last_ordinal=p_last_ordinal, cell_root=p_cell_root
    WHEN NOT MATCHED THEN INSERT
        (cell_id,mode,balance,nonce,fields,fields_json,lifecycle,last_ordinal,cell_root)
        VALUES (p_cell_id,p_mode,p_balance,p_nonce,p_fields,p_fields_json,
                p_lifecycle,p_last_ordinal,p_cell_root)
    RETURNING WITH (OLD AS o, NEW AS n)
        merge_action(),
        n.balance - coalesce(o.balance, 0),
        n.nonce   - coalesce(o.nonce, 0)
        INTO action, balance_delta, nonce_delta;
END $$;
"#;

    // The dregg-developer query surface (docs/QUICKSTART-dregg-dev.md). Plain
    // SELECTs over the Tier-B tables; each inherits the table's read-side RLS.
    //
    // The last two views use PostgreSQL 17's SQL/JSON `JSON_TABLE` to project the
    // jsonb columns (`capabilities.allowed_effects`, `cells.fields_json`) into a
    // flat relational surface — turning dregg's embedded JSON state into proper
    // rows a developer can JOIN/aggregate without hand-written jsonb operators.
    // (docs/PG-DREGG-PG18.md §5.) JSON_TABLE is a pg17 feature; the mirror's
    // PRIMARY target is pg18 (which includes it), so these ship by default.
    // Every dev-view is created `WITH (security_invoker = true)` (pg15). Without
    // it, a view runs with its OWNER's privileges, so the read-side RLS on the base
    // tables would bite a querying reader only INCIDENTALLY (because the views are
    // owned by the same role and RLS is FORCEd) — a future owner-privileged change
    // could silently widen what a view exposes past the reader's capability. With
    // `security_invoker`, RLS is evaluated as the INVOKING reader on every base
    // table the view reads, so the capability gate on `dregg.cells` / `turns` /
    // `capabilities` is enforced THROUGH the view, by declaration not by accident.
    // (docs/PG-DREGG.md §14.3 — the cheap hardening, now wired.)
    const VIEWS: &str = r#"
CREATE OR REPLACE VIEW dregg.cap_edges WITH (security_invoker = true) AS
    SELECT holder AS src, target AS dst, slot, permissions, expires_at
    FROM dregg.capabilities;
CREATE OR REPLACE VIEW dregg.cell_balances WITH (security_invoker = true) AS
    SELECT encode(cell_id, 'hex') AS cell, balance, nonce, lifecycle, last_ordinal
    FROM dregg.cells;
CREATE OR REPLACE VIEW dregg.receipt_chain WITH (security_invoker = true) AS
    SELECT ordinal, height, encode(creator, 'hex') AS creator,
           encode(prev_root, 'hex') AS prev_root,
           encode(ledger_root, 'hex') AS ledger_root, committed_at
    FROM dregg.turns ORDER BY ordinal;
CREATE OR REPLACE VIEW dregg.cap_attenuations WITH (security_invoker = true) AS
    SELECT encode(c.holder, 'hex') AS holder, c.slot,
           encode(c.target, 'hex') AS target, jt.effect, c.expires_at,
           c.last_ordinal
    FROM dregg.capabilities c,
         JSON_TABLE(c.allowed_effects, '$[*]'
             COLUMNS (effect text PATH '$')) AS jt;
CREATE OR REPLACE VIEW dregg.cell_fields WITH (security_invoker = true) AS
    SELECT encode(cell_id, 'hex') AS cell, jt.balance, jt.nonce, last_ordinal
    FROM dregg.cells,
         JSON_TABLE(fields_json, '$'
             COLUMNS (balance bigint PATH '$.balance',
                      nonce    bigint PATH '$.nonce')) AS jt;
-- The canonical ledger view: cells in the deterministic byte-order the node's
-- canonical roots use, via the pg17 builtin C collation (pg_c_utf8) on the
-- generated cell_hex column. ORDER BY here matches the kernel's sorted-leaf
-- ordering exactly (no ICU/locale drift), so a pg-side fold over this view sees
-- leaves in the same order the ledger root commits them. (docs/PG-DREGG-PG18.md §3.)
CREATE OR REPLACE VIEW dregg.canonical_cells WITH (security_invoker = true) AS
    SELECT cell_hex, balance, nonce, lifecycle, cell_root_hex, last_ordinal
    FROM dregg.cells
    ORDER BY cell_hex COLLATE pg_c_utf8;
-- pg18 AIO observability (docs/PG-DREGG-PG18.md §8, docs/PG-DREGG.md §14.2): the
-- mirror is read-heavy (the explorer/analytics scans + the recursive cap_edges
-- walk) and Tier C adds verify-on-write, so the read/write/verify I/O mix is the
-- thing worth making legible. pg18's asynchronous I/O subsystem feeds pg_stat_io;
-- this view projects the read-path-relevant contexts (normal heap/index reads,
-- vacuum, bulkread/bulkwrite) into a compact mirror-facing surface: per (backend
-- type, io object, context) the read/write/extend counts and — the AIO-specific
-- columns pg18 adds — `reads`/`read_bytes` and the `hits` that never touched the
-- OS. `cache_hit_ratio` is the headline the read-heavy mirror watches as the
-- ledger grows under AIO. It is a thin SELECT over the system view (no security
-- concern — pg_stat_io exposes no row data), so it ships as a plain view the
-- kernel/operator reads. NULLs (a context with no activity yet) are coalesced.
CREATE OR REPLACE VIEW dregg.mirror_io_stats AS
    SELECT backend_type, object, context,
           reads, read_bytes, writes, write_bytes, extends, hits, evictions,
           CASE WHEN coalesce(hits,0) + coalesce(reads,0) > 0
                THEN round(coalesce(hits,0)::numeric
                           / (coalesce(hits,0) + coalesce(reads,0)), 4)
                ELSE NULL END AS cache_hit_ratio
    FROM pg_stat_io
    WHERE object IN ('relation')
      AND context IN ('normal','vacuum','bulkread','bulkwrite');
-- pg18 AIO IN-FLIGHT surface (docs/PG-DREGG-PG18.md §8). pg_stat_io is the
-- CUMULATIVE counter view; pg18 ALSO ships `pg_aios` — the live view of the I/O
-- handles a backend currently has OUTSTANDING under the asynchronous I/O
-- subsystem. For a read-heavy mirror that now issues batched async reads, the
-- in-flight depth is the companion signal to the cumulative ratio: it shows
-- whether AIO is actually queueing reads (depth > 0 under a big scan) vs falling
-- back to synchronous. A thin `SELECT *` so it inherits pg_aios's columns
-- verbatim (no row data; a system view). The kernel/operator reads it to confirm
-- AIO is engaged as the ledger grows. (pg18-only: pg_aios does not exist pre-18.)
CREATE OR REPLACE VIEW dregg.mirror_aio_inflight AS
    SELECT * FROM pg_aios;
-- pg18 DATA-INTEGRITY status (docs/PG-DREGG-PG18.md §11). dregg's whole thesis is
-- integrity-down-to-the-bytes: the kernel commits a sorted-leaf root, the chain
-- tooth refuses a substituted batch, the IVC light client attests execution. The
-- STORAGE floor under all of that is page-level integrity — and pg18 makes
-- `initdb` enable data checksums BY DEFAULT (every heap/index page carries a
-- checksum the engine verifies on read, so silent on-disk corruption surfaces as
-- a loud error instead of a wrong byte fed to the mirror). This view makes that
-- floor LEGIBLE in-database: `data_checksums` is the read-only GUC pg sets from
-- the cluster's control file (`'on'` when checksums are active), and
-- `block_size` is the page size the checksum covers. So an operator (or a setup
-- assertion) can confirm the mirror sits on a checksummed cluster — the page
-- integrity the higher-tier roots ASSUME. A thin SELECT over GUCs (no row data).
CREATE OR REPLACE VIEW dregg.integrity_status AS
    SELECT current_setting('data_checksums')           AS data_checksums,
           (current_setting('data_checksums') = 'on')   AS checksums_enabled,
           current_setting('block_size')                AS block_size;
"#;

    const RLS: &str = r#"
ALTER TABLE dregg.cells        ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.turns        ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.capabilities ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.memory       ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.cells        FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.turns        FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.capabilities FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.memory       FORCE ROW LEVEL SECURITY;
DROP POLICY IF EXISTS cells_read ON dregg.cells;
CREATE POLICY cells_read ON dregg.cells FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(cell_id, 'hex')));
DROP POLICY IF EXISTS turns_read ON dregg.turns;
CREATE POLICY turns_read ON dregg.turns FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(creator, 'hex')));
DROP POLICY IF EXISTS caps_read ON dregg.capabilities;
CREATE POLICY caps_read ON dregg.capabilities FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(holder, 'hex')));
DROP POLICY IF EXISTS memory_read ON dregg.memory;
CREATE POLICY memory_read ON dregg.memory FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(collection, 'hex')));
GRANT USAGE ON SCHEMA dregg TO dregg_reader, dregg_kernel;
GRANT SELECT ON ALL TABLES IN SCHEMA dregg TO dregg_reader;
-- The kernel is the verified writer; it needs SELECT as well as the mutating
-- privileges. The pg17 dregg.merge_cell upsert PROBES the target (its
-- `WHEN MATCHED` arm reads the existing row), and the kernel is the trust
-- position that materializes + audits post-images (it is BYPASSRLS, so the
-- read-side RLS never hides a row from it — but BYPASSRLS is not a table
-- privilege; the SELECT grant is). Without it the MERGE's matched arm and any
-- kernel-side read (turn_effects, canonical_cells) is "permission denied".
GRANT SELECT, INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg TO dregg_kernel;
REVOKE INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg FROM PUBLIC;
"#;

    // ----------------------------------------------------------------------
    // Tier C (docs/PG-DREGG.md §10) — the verified-store gate. The commit_log
    // is the ONE door to state; its BEFORE INSERT trigger re-validates the
    // chain and materializes the post-image. Mirrors sql/schema-tierC.sql.
    // ----------------------------------------------------------------------

    // The commit_log: the ONLY door to state. A verified-turn post-image is
    // submitted here (the turn metadata + its touched-cell post-images as a jsonb
    // array — the realizable payload, since a CommitRecord carries no per-turn
    // proof; §10.2). The trigger gates it on the chain re-validator and only then
    // materializes. Apps NEVER write the state tables directly (the Tier-B
    // privilege lockdown forbids it); the only door is this INSERT, and this
    // INSERT runs `dregg_verify_turn`.
    const COMMIT_LOG: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.commit_log (
    ordinal      bigint PRIMARY KEY,
    height       bigint NOT NULL,
    block_id     bytea  NOT NULL,
    block_executed_up_to bigint NOT NULL,
    turn_hash    bytea  NOT NULL,
    creator      bytea  NOT NULL,
    receipt_hash bytea  NOT NULL,
    ledger_root  bytea  NOT NULL,   -- the verified post-state root of this turn
    prev_root    bytea  NOT NULL,   -- the pre-state root it claims to chain onto
    cells        jsonb  NOT NULL DEFAULT '[]'::jsonb,  -- touched-cell post-images
    submitted_at timestamptz NOT NULL DEFAULT now());
"#;

    // The gate: verify the chain (the real anti-substitution tooth, the SAME
    // check `mirror::RootChain` runs — `dregg_verify_turn` is the extension
    // function backed by `verify_chain_step`), then record the turn + materialize
    // its cells via the pg18 `dregg.merge_cell` upsert, all in one transaction.
    // SECURITY DEFINER so the trigger writes the locked-down state tables on
    // behalf of the (least-privileged) submitter, who holds only INSERT on
    // commit_log. Fail-closed: a refused chain RAISEs and nothing is written.
    const APPLY_VERIFIED_TURN: &str = r#"
CREATE OR REPLACE FUNCTION dregg.apply_verified_turn() RETURNS trigger
LANGUAGE plpgsql SECURITY DEFINER AS $$
DECLARE c jsonb;
BEGIN
    -- (1) The chain MUST re-validate. dregg_verify_turn reads the current head
    --     from dregg.turns and runs the real verify_chain_step gate (ordinal is
    --     next-expected AND prev_root == head). A tampered / reordered / forged
    --     row is REFUSED here by the database engine, not by trusting the writer.
    --     (This is the structural half of the spine invariant; per-turn proof
    --     soundness is the whole-chain IVC light client's job — §10.2. The
    --     function is NOT stubbed to TRUE — the forbidden failure mode, §10.3.)
    IF NOT dregg_verify_turn(NEW.prev_root, NEW.ledger_root, NEW.ordinal) THEN
        RAISE EXCEPTION 'dregg: turn % does not chain onto the head root — refused (anti-substitution)', NEW.ordinal;
    END IF;

    -- (2) Record the verified turn row.
    INSERT INTO dregg.turns(ordinal, height, block_id, block_executed_up_to,
                            turn_hash, creator, receipt_hash, ledger_root, prev_root)
        VALUES (NEW.ordinal, NEW.height, NEW.block_id, NEW.block_executed_up_to,
                NEW.turn_hash, NEW.creator, NEW.receipt_hash, NEW.ledger_root, NEW.prev_root);

    -- (3) Materialize the post-image cells, same transaction, via the pg17 MERGE
    --     upsert (a later turn's post-image overwrites in place).
    FOR c IN SELECT * FROM jsonb_array_elements(NEW.cells) LOOP
        PERFORM dregg.merge_cell(
            decode(c->>'cell_id', 'hex'),
            c->>'mode',
            (c->>'balance')::bigint,
            (c->>'nonce')::bigint,
            decode(coalesce(c->>'fields',''), 'hex'),
            (c->'fields_json'),
            c->>'lifecycle',
            NEW.ordinal,
            decode(c->>'cell_root', 'hex'));
    END LOOP;
    RETURN NEW;
END $$;
"#;

    const TIER_C_TRIGGER: &str = r#"
DROP TRIGGER IF EXISTS verify_before_apply ON dregg.commit_log;
CREATE TRIGGER verify_before_apply BEFORE INSERT ON dregg.commit_log
    FOR EACH ROW EXECUTE FUNCTION dregg.apply_verified_turn();
"#;

    // A turn's touched-cell post-images, exploded from the commit_log jsonb
    // payload into first-class rows with pg17 JSON_TABLE: one row per (ordinal,
    // cell), so a developer queries "what did turn N do?" as plain SQL over the
    // verified store. This is the realizable per-turn effect surface (a
    // CommitRecord's touched cells — the payload the gate verified; §10.2). Lives
    // in Tier C because it reads dregg.commit_log (the verified-store door).
    // (docs/PG-DREGG-PG18.md §5.)
    const TIER_C_VIEWS: &str = r#"
CREATE OR REPLACE VIEW dregg.turn_effects AS
    SELECT cl.ordinal, jt.cell_id, jt.balance, jt.nonce, jt.lifecycle,
           jt.cell_root, cl.submitted_at
    FROM dregg.commit_log cl,
         JSON_TABLE(cl.cells, '$[*]'
             COLUMNS (cell_id   text   PATH '$.cell_id',
                      balance   bigint PATH '$.balance',
                      nonce     bigint PATH '$.nonce',
                      lifecycle text   PATH '$.lifecycle',
                      cell_root text   PATH '$.cell_root')) AS jt;
"#;

    // The only grant an app needs to change state is INSERT on commit_log — and
    // even that runs the verifier. The state tables stay closed to it. The kernel
    // (the verified writer / auditor trust position) gets SELECT on the
    // verified-store door + the JSON_TABLE turn-effects view it explodes, so it can
    // audit "what did turn N do?" over the store it materialized. The Tier-B
    // GRANT-ALL ran before these Tier-C relations existed, so they are granted
    // explicitly here (a GRANT ON ALL only covers relations that exist at its time).
    const TIER_C_GRANTS: &str = r#"
GRANT INSERT, SELECT ON dregg.commit_log TO dregg_kernel;
GRANT SELECT ON dregg.turn_effects TO dregg_kernel;
REVOKE INSERT, UPDATE, DELETE ON dregg.commit_log FROM PUBLIC;
"#;

    // ----------------------------------------------------------------------
    // The WRITE-path outbox (docs/PG-DREGG.md §11) — submit a verified turn
    // FROM postgres. The node drains this queue through the real executor.
    // ----------------------------------------------------------------------

    // The submit queue: a pg-user enqueues a SIGNED turn (postcard SignedTurn
    // bytes) for the node to execute. `agent` is the turn's agent cell (carried
    // out so the RLS gate can check the submitter's capability admits it WITHOUT
    // decoding the envelope in SQL). `status` walks pending → executed | refused
    // as the node drains it; `receipt_hash` / `error` carry the outcome back.
    // pg18 `uuidv7()` mints a TEMPORALLY-SORTABLE id (its leading bits are a
    // millisecond timestamp), so the queue's primary key already orders by
    // submission time — the node drains in arrival order by `id` alone, and the
    // index is append-friendly (no random-uuid page churn). (docs/PG-DREGG-PG18.md §6.)
    const SUBMIT_QUEUE: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.submit_queue (
    id           uuid PRIMARY KEY DEFAULT uuidv7(),
    agent        bytea NOT NULL,               -- the turn's agent cell (RLS key)
    signed_turn  bytea NOT NULL,               -- postcard SignedTurn bytes
    submitter    text  NOT NULL DEFAULT current_user,
    submit_token text,                          -- the bearer token the enqueue ran
                                                -- under (the dregg.token GUC), so the
                                                -- DRAINER can RE-CHECK the submit gate
                                                -- at drain time (a revoked-since-enqueue
                                                -- capability is then refused before it
                                                -- executes). NULL ⇒ deny-by-default.
    status       text  NOT NULL DEFAULT 'pending'
                 CHECK (status IN ('pending','executed','refused')),
    receipt_hash bytea,                         -- set by the node on success
    error        text,                          -- set by the node on refusal
    submitted_at timestamptz NOT NULL DEFAULT now(),
    resolved_at  timestamptz);
-- A pre-existing queue (installed before submit_token landed) is migrated in place.
ALTER TABLE dregg.submit_queue ADD COLUMN IF NOT EXISTS submit_token text;
CREATE INDEX IF NOT EXISTS submit_queue_pending
    ON dregg.submit_queue (submitted_at) WHERE status = 'pending';
"#;

    // RLS: a role may ENQUEUE a turn only for an `agent` cell its presented
    // capability admits `submit` on — so a pg role submits exactly the turns its
    // caps authorize. A role may READ only its own submissions' outcomes (gated
    // on the same `submit` admission, so a submitter sees its turn's status). The
    // node drainer (dregg_kernel, BYPASSRLS) reads pending rows and writes the
    // outcome. Reads stay free SQL; writes stay verified-only (only the node, via
    // the real executor, turns a queued intent into state).
    const SUBMIT_QUEUE_RLS: &str = r#"
ALTER TABLE dregg.submit_queue ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.submit_queue FORCE ROW LEVEL SECURITY;
DROP POLICY IF EXISTS submit_gate ON dregg.submit_queue;
CREATE POLICY submit_gate ON dregg.submit_queue FOR INSERT TO dregg_reader
    WITH CHECK (dregg_admits('submit', encode(agent, 'hex')));
DROP POLICY IF EXISTS submit_read ON dregg.submit_queue;
CREATE POLICY submit_read ON dregg.submit_queue FOR SELECT TO dregg_reader
    USING (dregg_admits('submit', encode(agent, 'hex')));
GRANT INSERT, SELECT ON dregg.submit_queue TO dregg_reader;
GRANT SELECT, UPDATE ON dregg.submit_queue TO dregg_kernel;
REVOKE INSERT, UPDATE, DELETE ON dregg.submit_queue FROM PUBLIC;
-- The queue audit surface (docs/PG-DREGG-PG18.md §6): pg18's `uuidv7()` key is
-- not merely sortable — its leading bits ARE the submission timestamp, and pg18
-- ships `uuid_extract_timestamp()` / `uuid_extract_version()` to read them back.
-- So the key itself is an audit signal: `enqueued_at` is recovered FROM the id
-- (independent of the `submitted_at` clock column — a cross-check that the key
-- really is time-ordered), `id_version` proves it is a v7, and `queue_latency`
-- (resolved_at − the key's own timestamp) is the node's drain latency measured
-- against the key. `security_invoker` so the submit_read RLS still gates which
-- rows a submitter sees through the view. Ordered by id = arrival order.
CREATE OR REPLACE VIEW dregg.submit_queue_audit WITH (security_invoker = true) AS
    SELECT id,
           encode(agent, 'hex')              AS agent,
           submitter, status,
           uuid_extract_version(id)          AS id_version,
           uuid_extract_timestamp(id)        AS enqueued_at,
           submitted_at,
           resolved_at,
           (resolved_at - uuid_extract_timestamp(id)) AS queue_latency,
           encode(receipt_hash, 'hex')       AS receipt_hash,
           error
    FROM dregg.submit_queue
    ORDER BY id;
GRANT SELECT ON dregg.submit_queue_audit TO dregg_reader, dregg_kernel;
"#;

    // ----------------------------------------------------------------------
    // The Tier-C PROOF store (docs/PG-DREGG.md §10.2) — the dregg.turn_proofs
    // table: ONE row per folded finalized WINDOW, written by the node-side
    // whole-chain proof producer (crate::turn_proofs, S2) and read by the
    // range-attest SRF (dregg_attest_range). The proof half the per-row chain
    // tooth (dregg_verify_turn) does NOT do (a CommitRecord carries no per-turn
    // STARK — §10.2); the proof is whole-chain (one per window), not per-row.
    // ----------------------------------------------------------------------
    const TURN_PROOFS: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.turn_proofs (
    lo           bigint NOT NULL,             -- inclusive lower ordinal attested
    hi           bigint NOT NULL,             -- inclusive upper ordinal attested
    genesis_root bytea  NOT NULL,             -- pre-root of `lo`  (window start)
    final_root   bytea  NOT NULL,             -- post-root of `hi` (window end)
    proof        bytea  NOT NULL,             -- serialized whole-chain proof transport
                                              -- (attest::SerializedWholeChainProof bytes)
    vk           bytea  NOT NULL,             -- the 32-byte RecursionVk anchor the SRF
                                              -- verifies `proof` against (trust root)
    num_turns    bigint GENERATED ALWAYS AS (hi - lo + 1) STORED,  -- the window length
    created_at   timestamptz NOT NULL DEFAULT now(),
    PRIMARY KEY (lo, hi),
    CHECK (hi >= lo));                        -- a window is never inverted
-- Resume the producer watermark from the max-hi row (the durable proof head); the
-- SRF finds the proof covering an ordinal via the [lo, hi] range index.
CREATE INDEX IF NOT EXISTS turn_proofs_hi ON dregg.turn_proofs (hi);
-- Write-locked to the kernel (the producer runs as dregg_kernel); readable by
-- reader + kernel so the SRF can join it against dregg.turns. Reads stay free SQL;
-- the proof rows are produced by the node, never by an application.
REVOKE ALL ON dregg.turn_proofs FROM PUBLIC;
GRANT SELECT ON dregg.turn_proofs TO dregg_reader, dregg_kernel;
GRANT INSERT, SELECT, UPDATE, DELETE ON dregg.turn_proofs TO dregg_kernel;
"#;

    // ----------------------------------------------------------------------
    // The pg17 LOGIN EVENT TRIGGER authz binding (docs/PG-DREGG-PG18.md §6) —
    // bind a connecting pg role to its dregg agent identity at connection time.
    // ----------------------------------------------------------------------

    // The role → dregg-identity map. `pg_role` is the connecting database role
    // (session_user); `agent` is the dregg cell it acts as; `default_token` is the
    // dga1_… capability token the login hook installs into the dregg.token GUC for
    // that role (so the role's whole session is gated by that capability). Only a
    // DBA writes this table (it is the trust binding of pg-role → dregg-cap); it is
    // NOT app-writable.
    const ROLE_IDENTITY: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.role_identity (
    pg_role       text PRIMARY KEY,        -- the connecting database role (session_user)
    agent         bytea NOT NULL,          -- the dregg cell this role acts as
    default_token text,                    -- the dga1_… token the login hook installs
    bound_at      timestamptz NOT NULL DEFAULT now());
REVOKE ALL ON dregg.role_identity FROM PUBLIC;
GRANT SELECT ON dregg.role_identity TO dregg_kernel;
-- The bind point where pg18 OAuth meets dregg (docs/PG-DREGG-PG18.md §6). OAuth
-- itself is `pg_hba.conf` deployment config (the `oauth` auth method + an
-- `oauth_validator_libraries` validator — NOT extension SQL); what it produces is
-- a pg ROLE for the authenticated IdP subject. `dregg.bind_role` is the seam that
-- turns that role into a dregg capability: a DBA (or an IdP-provisioning hook)
-- calls it to upsert the role → (agent, token) row the `ON login` trigger then
-- installs. So the full chain — OAuth subject → pg role → `dregg.bind_role` →
-- `role_identity` → login hook → `dregg.token` GUC → RLS on every row — is one
-- tested code path, not prose. SECURITY DEFINER (it writes role_identity, which is
-- closed to PUBLIC); callable only by a role the DBA grants EXECUTE.
CREATE OR REPLACE FUNCTION dregg.bind_role(
    p_pg_role text, p_agent bytea, p_token text DEFAULT NULL) RETURNS void
LANGUAGE plpgsql SECURITY DEFINER AS $$
BEGIN
    INSERT INTO dregg.role_identity (pg_role, agent, default_token, bound_at)
        VALUES (p_pg_role, p_agent, p_token, now())
    ON CONFLICT (pg_role) DO UPDATE
        SET agent = EXCLUDED.agent,
            default_token = EXCLUDED.default_token,
            bound_at = now();
END $$;
REVOKE ALL ON FUNCTION dregg.bind_role(text, bytea, text) FROM PUBLIC;
-- BULK ONBOARDING of the OAuth→role bind map via pg18 COPY ON_ERROR
-- (docs/PG-DREGG-PG18.md §12). Provisioning many federated identities at once
-- (an IdP export of `pg_role,agent_hex,token` rows) is a real bootstrap path —
-- and a single malformed line (a bad hex agent, a truncated row) should NOT abort
-- the whole load. pg18 adds `ON_ERROR ignore` + `REJECT_LIMIT n` + the
-- `LOG_VERBOSITY silent` level to COPY FROM, so a bulk load skips the malformed
-- rows (up to the limit) and lands the good ones, instead of the pre-18
-- all-or-nothing abort. dregg uses it on a TEXT staging table (not directly on
-- role_identity): COPY lands raw rows in `role_identity_load`, then
-- `dregg.promote_role_identity_load()` validates each (decode the hex agent; a
-- bad one is skipped, not fatal) and upserts it through `dregg.bind_role` — so the
-- trust binding still flows through the ONE audited seam, and the bulk path never
-- writes role_identity unchecked. The COPY itself needs a literal path/format, so
-- the recommended command is emitted as a template (`dregg.load_role_identity_sql`,
-- like the federation runbook); the staging table + promote function are real DDL.
CREATE TABLE IF NOT EXISTS dregg.role_identity_load (
    pg_role   text,
    agent_hex text,
    token     text);
REVOKE ALL ON dregg.role_identity_load FROM PUBLIC;
-- Validate + promote every staged row through the audited bind seam. A row whose
-- agent_hex does not decode to bytea is SKIPPED (counted), never written — the
-- bulk path cannot smuggle a malformed binding past dregg.bind_role. Returns the
-- (promoted, skipped) counts. SECURITY DEFINER (it reads the staging table and
-- calls bind_role, both PUBLIC-closed); the DBA truncates the staging table after.
CREATE OR REPLACE FUNCTION dregg.promote_role_identity_load(
    OUT promoted bigint, OUT skipped bigint)
LANGUAGE plpgsql SECURITY DEFINER AS $$
DECLARE r record; v_agent bytea;
BEGIN
    promoted := 0; skipped := 0;
    FOR r IN SELECT pg_role, agent_hex, token FROM dregg.role_identity_load LOOP
        BEGIN
            IF r.pg_role IS NULL OR r.agent_hex IS NULL THEN
                skipped := skipped + 1; CONTINUE;
            END IF;
            v_agent := decode(r.agent_hex, 'hex');   -- a bad hex raises ⇒ skip
            PERFORM dregg.bind_role(r.pg_role, v_agent, r.token);
            promoted := promoted + 1;
        EXCEPTION WHEN OTHERS THEN
            skipped := skipped + 1;   -- a malformed staged row never aborts the load
        END;
    END LOOP;
END $$;
REVOKE ALL ON FUNCTION dregg.promote_role_identity_load() FROM PUBLIC;
-- The role→capability introspection view: which pg roles are bound to which dregg
-- agent, and whether a default token is installed (the token text itself is NOT
-- exposed — only its presence — so the binding map is auditable without leaking
-- credentials). `security_invoker`; readable by the kernel/operator.
CREATE OR REPLACE VIEW dregg.role_bindings WITH (security_invoker = true) AS
    SELECT pg_role,
           encode(agent, 'hex')               AS agent,
           (default_token IS NOT NULL)         AS has_token,
           bound_at
    FROM dregg.role_identity;
GRANT SELECT ON dregg.role_bindings TO dregg_kernel;
"#;

    // The login event trigger. On every connection, look up the connecting role's
    // identity row and, if present, SET the session dregg.token + dregg.agent GUCs
    // from it — so the session is bound to that role's dregg capability the moment
    // it connects, with no application-side token presentation. SECURITY DEFINER
    // (it reads role_identity, which the connecting role cannot). Defensive: the
    // whole body is wrapped so any fault (a missing table during bootstrap, a
    // malformed row) is swallowed and the login still proceeds — a buggy hook must
    // never lock every role out of the database (the documented pg17 login-trigger
    // hazard; recover via a single-user-mode `ALTER EVENT TRIGGER … DISABLE`).
    //
    // SET_CONFIG with is_local=false makes the GUC session-scoped (it persists for
    // the connection, not just the current transaction), which is what binds the
    // whole session. The token is set only if the role HAS an identity row with a
    // non-null token; otherwise nothing is set and the role is deny-by-default.
    const LOGIN_HOOK: &str = r#"
CREATE OR REPLACE FUNCTION dregg.on_login() RETURNS event_trigger
LANGUAGE plpgsql SECURITY DEFINER AS $$
DECLARE r record;
BEGIN
    BEGIN
        SELECT agent, default_token INTO r
        FROM dregg.role_identity WHERE pg_role = session_user;
        IF FOUND THEN
            IF r.default_token IS NOT NULL THEN
                PERFORM set_config('dregg.token', r.default_token, false);
            END IF;
            PERFORM set_config('dregg.agent', encode(r.agent, 'hex'), false);
        END IF;
    EXCEPTION WHEN OTHERS THEN
        -- A fault in the hook must NOT abort the login (anti-lockout). The role
        -- simply connects unbound (deny-by-default), which is fail-closed.
        RAISE WARNING 'dregg.on_login: identity binding skipped (%):', SQLERRM;
    END;
END $$;
DROP EVENT TRIGGER IF EXISTS dregg_login_bind;
CREATE EVENT TRIGGER dregg_login_bind ON login EXECUTE FUNCTION dregg.on_login();
"#;
}

// ============================================================================
// helpers
// ============================================================================

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ============================================================================
// Tests — the Tier B/C core, proven at the Rust level (no postgres needed).
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn root(n: u8) -> [u8; 32] {
        [n; 32]
    }

    fn turn(ordinal: u64, prev: [u8; 32], post: [u8; 32]) -> TurnRow {
        TurnRow {
            ordinal,
            height: ordinal,
            block_id: root(1),
            block_executed_up_to: ordinal,
            turn_hash: root(2),
            creator: root(3),
            receipt_hash: root(4),
            ledger_root: post,
            prev_root: prev,
        }
    }

    fn batch(ordinal: u64, prev: [u8; 32], post: [u8; 32]) -> MirrorBatch {
        MirrorBatch {
            turn: turn(ordinal, prev, post),
            cells: vec![CellRow {
                cell_id: root(9),
                mode: "Hosted".into(),
                balance: 100,
                nonce: ordinal,
                fields: vec![],
                fields_json: None,
                heap: None,
                program: None,
                verification_key: None,
                permissions_json: None,
                delegate: None,
                lifecycle: "Active".into(),
                last_ordinal: ordinal,
                cell_root: root(10),
            }],
            caps: vec![],
            memory: vec![MemCell {
                domain: Domain::Registers,
                collection: root(9).to_vec(),
                key: vec![0],
                value: Some(vec![100]),
                last_ordinal: ordinal,
            }],
        }
    }

    #[test]
    fn domain_tag_roundtrips_and_is_total() {
        for d in Domain::ALL {
            assert_eq!(Domain::from_tag(d.tag()), Some(d));
        }
        // The tag is load-bearing: unknown tags fail closed.
        assert_eq!(Domain::from_tag("ghost"), None);
        assert_eq!(Domain::from_tag(""), None);
    }

    #[test]
    fn chain_accepts_a_well_formed_sequence() {
        // genesis root g; turn 0: g -> r1; turn 1: r1 -> r2; turn 2: r2 -> r3
        let g = root(0);
        let mut chain = RootChain::resume(g, 0);
        assert!(chain.extend(&batch(0, g, root(1))).is_ok());
        assert_eq!(chain.head(), Some(root(1)));
        assert!(chain.extend(&batch(1, root(1), root(2))).is_ok());
        assert!(chain.extend(&batch(2, root(2), root(3))).is_ok());
        assert_eq!(chain.head(), Some(root(3)));
        assert_eq!(chain.next_ordinal(), 3);
    }

    #[test]
    fn chain_refuses_a_root_that_does_not_chain() {
        // The anti-substitution tooth: a batch whose prev_root != head is a
        // tampered / substituted batch and is REFUSED, leaving the chain intact.
        let g = root(0);
        let mut chain = RootChain::resume(g, 0);
        chain.extend(&batch(0, g, root(1))).unwrap();
        // turn 1 claims a pre-root of root(7), but the head is root(1).
        let bad = batch(1, root(7), root(2));
        let err = chain.extend(&bad).unwrap_err();
        assert!(matches!(err, ChainRefusal::RootMismatch { .. }));
        // The chain head did NOT move — a bad batch cannot corrupt it.
        assert_eq!(chain.head(), Some(root(1)));
        assert_eq!(chain.next_ordinal(), 1);
    }

    #[test]
    fn chain_refuses_a_gap_or_replay() {
        let g = root(0);
        let mut chain = RootChain::resume(g, 0);
        chain.extend(&batch(0, g, root(1))).unwrap();
        // Skipping to ordinal 2 (gap) is refused.
        let gap = chain.extend(&batch(2, root(1), root(3))).unwrap_err();
        assert!(matches!(
            gap,
            ChainRefusal::OrdinalGap {
                expected: 1,
                got: 2
            }
        ));
        // Replaying ordinal 0 is refused.
        let replay = chain.extend(&batch(0, g, root(1))).unwrap_err();
        assert!(matches!(
            replay,
            ChainRefusal::OrdinalGap {
                expected: 1,
                got: 0
            }
        ));
    }

    #[test]
    fn chain_refuses_a_batch_with_smuggled_rows() {
        // A batch carrying a row stamped with a different ordinal is malformed:
        // you cannot smuggle a row from turn 5 into turn 1's batch.
        let g = root(0);
        let mut chain = RootChain::resume(g, 0);
        let mut b = batch(0, g, root(1));
        b.cells[0].last_ordinal = 99; // smuggled
        let err = chain.extend(&b).unwrap_err();
        assert!(matches!(err, ChainRefusal::Malformed(_)));
        // The chain is UNCHANGED — a malformed batch never advances the head.
        assert_eq!(
            chain.head(),
            Some(g),
            "a malformed genesis batch is rejected"
        );
        assert_eq!(chain.next_ordinal(), 0);
    }

    #[test]
    fn batch_ordinal_check_catches_each_row_kind() {
        let g = root(0);
        let mut b = batch(3, g, root(1));
        assert!(b.check_ordinals().is_ok());
        b.caps.push(CapRow {
            holder: root(9),
            slot: 0,
            target: root(8),
            permissions_json: "{}".into(),
            breadstuff: None,
            expires_at: None,
            allowed_effects_json: None,
            stored_epoch: 7.into(),
            last_ordinal: 4, // wrong
        });
        assert!(b.check_ordinals().is_err());
    }

    #[test]
    fn from_parts_stamps_ordinals_and_passes_the_gate() {
        // from_parts is the pg-side assembly point: it OVERWRITES each row's
        // last_ordinal with the turn's, so a row a caller left stamped for a
        // different turn is corrected (not smuggled through).
        let t = turn(7, root(0), root(1));
        let mut cell = CellRow {
            cell_id: root(9),
            mode: "Hosted".into(),
            balance: 5,
            nonce: 7,
            fields: vec![],
            fields_json: None,
            heap: None,
            program: None,
            verification_key: None,
            permissions_json: None,
            delegate: None,
            lifecycle: "Live".into(),
            last_ordinal: 999, // wrong on purpose
            cell_root: root(10),
        };
        let b = MirrorBatch::from_parts(t, vec![cell.clone()], vec![], vec![]).unwrap();
        assert_eq!(
            b.cells[0].last_ordinal, 7,
            "from_parts stamps the turn ordinal"
        );
        assert!(b.check_ordinals().is_ok());

        // And the assembled batch chains exactly like a hand-built one.
        let mut chain = RootChain::resume(root(0), 7);
        assert!(chain.extend(&b).is_ok());
        assert_eq!(chain.head(), Some(root(1)));

        // Independent: a hand-built batch with a mismatched row still fails the
        // gate (the from_parts overwrite is what saves the normal path).
        cell.last_ordinal = 4;
        let bad = MirrorBatch {
            turn: turn(7, root(0), root(1)),
            cells: vec![cell],
            caps: vec![],
            memory: vec![],
        };
        assert!(bad.check_ordinals().is_err());
    }

    #[test]
    fn mirror_batch_serde_roundtrips() {
        // The wire unit the node ships must round-trip exactly.
        let b = batch(0, root(0), root(1));
        let bytes = serde_json::to_vec(&b).unwrap();
        let back: MirrorBatch = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(b, back);
    }

    #[test]
    fn verify_chain_step_is_the_chains_gate() {
        // The pure step gate (lifted into SQL as dregg_verify_turn) decides
        // exactly what RootChain::extend decides, over scalars.
        // Genesis (head None): any prev_root at ordinal 0 is accepted.
        assert!(verify_chain_step(None, 0, root(9), 0).is_ok());
        // Genesis at the wrong ordinal is a gap.
        assert!(matches!(
            verify_chain_step(None, 0, root(9), 1),
            Err(ChainRefusal::OrdinalGap {
                expected: 0,
                got: 1
            })
        ));
        // Non-genesis: prev_root must equal head.
        assert!(verify_chain_step(Some(root(1)), 1, root(1), 1).is_ok());
        assert!(matches!(
            verify_chain_step(Some(root(1)), 1, root(9), 1),
            Err(ChainRefusal::RootMismatch { .. })
        ));
        // Wrong ordinal even with the right root is a gap.
        assert!(matches!(
            verify_chain_step(Some(root(1)), 1, root(1), 2),
            Err(ChainRefusal::OrdinalGap {
                expected: 1,
                got: 2
            })
        ));

        // It agrees with RootChain::extend on the whole synthetic-style chain:
        // every accepted extend corresponds to an Ok step at the same head.
        let g = root(0);
        let mut chain = RootChain::resume(g, 0);
        for (ord, prev, post) in [
            (0, g, root(1)),
            (1, root(1), root(2)),
            (2, root(2), root(3)),
        ] {
            let head = chain.head();
            let next = chain.next_ordinal();
            // The standalone gate and extend must agree.
            let step = verify_chain_step(head, next, prev, ord);
            let res = chain.extend(&batch(ord, prev, post));
            assert_eq!(
                step.is_ok(),
                res.is_ok(),
                "the gate and extend must agree at ord {ord}"
            );
        }
    }

    // ----------------------------------------------------------------------
    // Federation: a SUBSCRIBER re-validates a replicated chain (docs §15).
    // ----------------------------------------------------------------------

    fn link(ordinal: u64, prev: [u8; 32], post: [u8; 32]) -> ChainLink {
        ChainLink {
            ordinal,
            prev_root: prev,
            ledger_root: post,
        }
    }

    #[test]
    fn subscriber_revalidates_a_faithfully_replicated_chain() {
        // The §15 soundness property: a subscriber re-runs the SAME tooth over the
        // replicated turns and gets the publisher's verdict — the chain survives
        // replication because it is structural on the rows.
        let g = root(0);
        let links = [
            link(0, g, root(1)),
            link(1, root(1), root(2)),
            link(2, root(2), root(3)),
        ];
        let head = revalidate_replicated_chain(g, &links, Some(3)).unwrap();
        assert_eq!(
            head,
            Some(root(3)),
            "the re-validated head is the last post-root"
        );

        // It agrees with what RootChain::extend would accept, batch for batch.
        let mut chain = RootChain::resume(g, 0);
        for l in &links {
            assert!(
                chain
                    .extend(&batch(l.ordinal, l.prev_root, l.ledger_root))
                    .is_ok()
            );
        }
        assert_eq!(
            chain.head(),
            head,
            "subscriber sweep == publisher chain head"
        );
    }

    #[test]
    fn subscriber_catches_a_substituted_replicated_turn() {
        // A tampered replication stream (turn 1's prev_root substituted) is caught
        // ON THE SUBSCRIBER SIDE — replication is not a trust boundary.
        let g = root(0);
        let links = [
            link(0, g, root(1)),
            link(1, root(7), root(2)), // prev_root should be root(1)
        ];
        let err = revalidate_replicated_chain(g, &links, None).unwrap_err();
        assert!(matches!(err, ChainRefusal::RootMismatch { .. }));
    }

    #[test]
    fn subscriber_catches_a_reordered_or_gapped_stream() {
        let g = root(0);
        // A gap (ordinals 0 then 2) is caught.
        let gapped = [link(0, g, root(1)), link(2, root(1), root(3))];
        assert!(matches!(
            revalidate_replicated_chain(g, &gapped, None).unwrap_err(),
            ChainRefusal::OrdinalGap {
                expected: 1,
                got: 2
            }
        ));
        // A truncation (count mismatch) is caught when the expected count is known.
        let truncated = [link(0, g, root(1))];
        assert!(matches!(
            revalidate_replicated_chain(g, &truncated, Some(3)).unwrap_err(),
            ChainRefusal::Malformed(_)
        ));
    }

    #[test]
    fn subscriber_revalidates_the_synthetic_story_after_replication() {
        // The whole synthetic story, projected to ChainLinks (as a replicated
        // dregg.turns would be read), re-validates from the pinned genesis — the
        // exact federation claim over real demo data.
        let story = crate::synth::ledger_story();
        let links: Vec<ChainLink> = story
            .iter()
            .map(|b| link(b.turn.ordinal, b.turn.prev_root, b.turn.ledger_root))
            .collect();
        let head =
            revalidate_replicated_chain(crate::synth::GENESIS_ROOT, &links, Some(4)).unwrap();
        assert_eq!(head, Some(story[3].turn.ledger_root));
    }

    #[test]
    fn federation_publication_ddl_publishes_the_state_tables() {
        let sql = ddl::federation_publication();
        assert!(sql.contains("CREATE PUBLICATION dregg_mirror"));
        // All four state relations are in the feed.
        assert!(sql.contains("dregg.turns"));
        assert!(sql.contains("dregg.cells"));
        assert!(sql.contains("dregg.capabilities"));
        assert!(sql.contains("dregg.memory"));
        // Idempotent (re-runnable).
        assert!(sql.contains("duplicate_object"));
        // The pg18 logical-replication conflict-observability view ships with the
        // publication: the confl_* counters summed into a conflicts_total alarm.
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.replication_conflicts"));
        assert!(sql.contains("pg_stat_subscription_stats"));
        assert!(sql.contains("confl_insert_exists"));
        assert!(sql.contains("conflicts_total"));
        // The conflict view MUST be granted to the kernel — `dregg_federation_health`
        // reads it as the kernel/operator role to compose the alarm with the chain
        // re-validation. The Tier-B GRANT-ALL ran before this view existed (the
        // publication installs separately), so the grant is explicit here.
        assert!(
            sql.contains("GRANT SELECT ON dregg.replication_conflicts TO dregg_kernel"),
            "the conflict alarm view must be readable by the kernel role that runs \
             dregg_federation_health"
        );
        // The subscriber runbook substitutes the publisher conninfo + names the
        // re-validation sweep (re-validate, do not trust).
        let sub = ddl::federation_subscriber("host=pub dbname=dregg");
        assert!(sub.contains("pg_createsubscriber"));
        assert!(sub.contains("failover = true"));
        assert!(sub.contains("host=pub dbname=dregg"));
        assert!(sub.contains("dregg_revalidate_replicated_chain"));

        // The pg18 COPY ON_ERROR bulk-load template for the bind map: it stages to
        // role_identity_load with ON_ERROR ignore (skip malformed) and the path +
        // reject limit substituted, then promotes through the audited seam.
        let load = ddl::load_role_identity_sql("/srv/idp/roles.csv", 25);
        assert!(load.contains("COPY dregg.role_identity_load"));
        assert!(load.contains("/srv/idp/roles.csv"));
        assert!(load.contains("ON_ERROR ignore"));
        assert!(load.contains("REJECT_LIMIT 25"));
        assert!(load.contains("dregg.promote_role_identity_load()"));
        // A reject_limit of 0 omits the cap (tolerate any number of bad rows).
        let load0 = ddl::load_role_identity_sql("/srv/idp/roles.csv", 0);
        assert!(
            !load0.contains("REJECT_LIMIT"),
            "reject_limit 0 omits the cap"
        );
    }

    // ----------------------------------------------------------------------
    // Generative property test for the anti-substitution tooth — no proptest
    // dep, a tiny deterministic xorshift PRNG drives random batch sequences.
    // ----------------------------------------------------------------------

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545F4914F6CDD1D)
        }
    }

    #[test]
    fn generative_chain_extends_iff_step_gate_accepts_and_head_is_stable() {
        // Over MANY random batch sequences (right/wrong ordinals, right/wrong
        // prev_roots, occasional smuggled rows), assert the three load-bearing
        // invariants of the anti-substitution tooth on EVERY step:
        //   (1) RootChain::extend accepts IFF the standalone verify_chain_step gate
        //       accepts at the SAME (head, next_ordinal) — the SQL gate and the
        //       in-process chain are provably the same check;
        //   (2) on a REFUSAL the head and next_ordinal are UNCHANGED (a bad batch
        //       can never corrupt the chain);
        //   (3) on ACCEPTANCE the head advances to the batch's ledger_root and
        //       next_ordinal increments by one.
        let mut rng = Rng(0xDEADBEEFCAFEF00D);
        for _ in 0..400 {
            let g = root((rng.next() % 251) as u8);
            let mut chain = RootChain::resume(g, 0);
            for _ in 0..12 {
                let head_before = chain.head();
                let next_before = chain.next_ordinal();

                // Build a batch whose ordinal is usually-right (next), sometimes a
                // gap/replay; whose prev_root is usually-right (the head),
                // sometimes substituted; occasionally with a smuggled row ordinal.
                let ord = match rng.next() % 4 {
                    0 => next_before.wrapping_add(rng.next() % 3),   // gap
                    1 => next_before.saturating_sub(rng.next() % 2), // replay-ish
                    _ => next_before,                                // correct
                };
                let prev = if rng.next() % 3 == 0 {
                    root((rng.next() % 251) as u8) // substituted
                } else {
                    head_before.unwrap_or(g) // correct (chains onto head)
                };
                let post = root((rng.next() % 251) as u8);
                let mut b = batch(ord, prev, post);
                if rng.next() % 9 == 0 {
                    b.cells[0].last_ordinal = ord.wrapping_add(1 + rng.next() % 5);
                    // smuggle
                }

                // (1) the standalone gate's verdict (it does NOT see the smuggle,
                // which check_ordinals catches first; so predict accordingly).
                let smuggled = b.check_ordinals().is_err();
                let gate_ok =
                    !smuggled && verify_chain_step(head_before, next_before, prev, ord).is_ok();

                let res = chain.extend(&b);
                assert_eq!(
                    res.is_ok(),
                    gate_ok,
                    "extend must accept iff the step gate accepts (head={head_before:?}, \
                     next={next_before}, ord={ord}, smuggled={smuggled})"
                );

                if res.is_ok() {
                    // (3) accepted ⇒ head advanced to post, next incremented.
                    assert_eq!(chain.head(), Some(post), "accepted batch advances the head");
                    assert_eq!(
                        chain.next_ordinal(),
                        next_before + 1,
                        "next ordinal increments"
                    );
                } else {
                    // (2) refused ⇒ chain UNCHANGED.
                    assert_eq!(
                        chain.head(),
                        head_before,
                        "a refused batch must not move the head"
                    );
                    assert_eq!(
                        chain.next_ordinal(),
                        next_before,
                        "a refused batch must not move next"
                    );
                }
            }
        }
    }

    #[test]
    fn cells_json_has_the_trigger_shape() {
        // The Tier-C commit_log trigger reads these exact keys from each element.
        let b = batch(0, root(0), root(1));
        let v: serde_json::Value = serde_json::from_str(&b.cells_json()).unwrap();
        let arr = v.as_array().expect("cells_json is an array");
        assert_eq!(arr.len(), 1);
        let c = &arr[0];
        for key in [
            "cell_id",
            "mode",
            "balance",
            "nonce",
            "fields",
            "lifecycle",
            "cell_root",
        ] {
            assert!(c.get(key).is_some(), "cells_json element missing `{key}`");
        }
        // cell_id / cell_root / fields are hex strings (the trigger `decode`s them).
        assert_eq!(c["cell_id"].as_str().unwrap().len(), 64);
        assert_eq!(c["cell_root"].as_str().unwrap().len(), 64);
        // balance / nonce are numbers (the trigger casts ::bigint).
        assert!(c["balance"].is_number());
        assert!(c["nonce"].is_number());
    }

    #[test]
    fn write_outbox_ddl_is_emittable_and_rls_gated() {
        let sql = ddl::write_outbox();
        // The outbox door + the index the node drains pending rows by.
        assert!(sql.contains("CREATE TABLE IF NOT EXISTS dregg.submit_queue"));
        assert!(sql.contains("submit_queue_pending"));
        // RLS gates submission on the dregg cap layer: a role submits only the
        // turns its capability admits `submit` on (WITH CHECK on INSERT).
        assert!(sql.contains("FORCE ROW LEVEL SECURITY"));
        assert!(sql.contains("CREATE POLICY submit_gate"));
        assert!(sql.contains("WITH CHECK (dregg_admits('submit', encode(agent, 'hex')))"));
        // The node (dregg_kernel) drains + writes outcomes; PUBLIC gets nothing.
        assert!(sql.contains("GRANT SELECT, UPDATE ON dregg.submit_queue TO dregg_kernel"));
        assert!(sql.contains("REVOKE INSERT, UPDATE, DELETE ON dregg.submit_queue FROM PUBLIC"));
        // pg18 uuidv7 key as an audit signal: the audit view recovers the enqueue
        // time + version FROM the key (uuid_extract_timestamp/version), proving the
        // temporal-sortability claim is load-bearing, not decorative.
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.submit_queue_audit"));
        assert!(sql.contains("uuid_extract_timestamp(id)"));
        assert!(sql.contains("uuid_extract_version(id)"));
        // The audit view is security_invoker so submit_read RLS still gates it.
        assert!(sql.contains("dregg.submit_queue_audit WITH (security_invoker = true)"));
    }

    #[test]
    fn tier_c_ddl_is_emittable_and_gates_writes() {
        let sql = ddl::tier_c();
        // The ONE door: the commit_log table + the BEFORE INSERT gate trigger.
        assert!(sql.contains("CREATE TABLE IF NOT EXISTS dregg.commit_log"));
        assert!(sql.contains("BEFORE INSERT ON dregg.commit_log"));
        assert!(sql.contains("dregg.apply_verified_turn"));
        // The gate calls the REAL chain re-validator (not stubbed to TRUE).
        assert!(sql.contains("dregg_verify_turn(NEW.prev_root, NEW.ledger_root, NEW.ordinal)"));
        assert!(sql.contains("RAISE EXCEPTION"));
        // It materializes via the pg17 MERGE upsert (same as the mirror path).
        assert!(sql.contains("dregg.merge_cell"));
        // SECURITY DEFINER so the least-privileged submitter never touches state.
        assert!(sql.contains("SECURITY DEFINER"));
        // The kernel writer gets INSERT + SELECT on commit_log (it submits AND
        // audits the verified-store door); PUBLIC gets nothing.
        assert!(sql.contains("GRANT INSERT, SELECT ON dregg.commit_log TO dregg_kernel"));
        assert!(sql.contains("REVOKE INSERT, UPDATE, DELETE ON dregg.commit_log FROM PUBLIC"));
    }

    #[test]
    fn turn_proofs_ddl_is_emittable_and_kernel_write_locked() {
        // The Tier-C PROOF store (§10.2): the dregg.turn_proofs table the S2 producer
        // writes and the range-attest SRF reads — ONE row per folded finalized window.
        let sql = ddl::turn_proofs();
        assert!(sql.contains("CREATE TABLE IF NOT EXISTS dregg.turn_proofs"));
        // The §10.2 columns: (lo, hi, genesis_root, final_root, proof bytea, vk).
        for col in ["lo", "hi", "genesis_root", "final_root", "proof", "vk"] {
            assert!(
                sql.contains(col),
                "turn_proofs is missing the `{col}` column"
            );
        }
        // A window is keyed + never inverted; the producer extends a dense prefix.
        assert!(sql.contains("PRIMARY KEY (lo, hi)"));
        assert!(sql.contains("CHECK (hi >= lo)"));
        // Write-locked to the kernel (the producer is node-side / dregg_kernel);
        // PUBLIC gets nothing; reader + kernel may SELECT so the SRF can join it.
        assert!(sql.contains("REVOKE ALL ON dregg.turn_proofs FROM PUBLIC"));
        assert!(sql.contains("GRANT SELECT ON dregg.turn_proofs TO dregg_reader, dregg_kernel"));
        assert!(
            sql.contains(
                "GRANT INSERT, SELECT, UPDATE, DELETE ON dregg.turn_proofs TO dregg_kernel"
            )
        );
    }

    #[test]
    fn ddl_is_emittable_and_mentions_the_lockdown() {
        let sql = ddl::tier_b();
        // The spine: apps read, only the kernel writes. The DDL must REVOKE
        // writes from PUBLIC and grant them only to dregg_kernel.
        assert!(
            sql.contains("REVOKE INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg FROM PUBLIC")
        );
        assert!(sql.contains("GRANT SELECT ON ALL TABLES IN SCHEMA dregg TO dregg_reader"));
        assert!(sql.contains("FORCE ROW LEVEL SECURITY"));
        // Every state table is RLS-gated by the Tier A cap layer.
        assert!(sql.contains("dregg_admits('read'"));
        // The universal-memory table exists.
        assert!(sql.contains("dregg.memory"));
        // The dregg-dev query-surface views are emitted.
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.cell_balances"));
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.cap_edges"));
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.receipt_chain"));
        // The pg17 SQL/JSON (JSON_TABLE) projection views are emitted.
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.cap_attenuations"));
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.cell_fields"));
        assert!(sql.contains("JSON_TABLE"));
        // The pg17 builtin C collation + stored generated columns (canonical state).
        assert!(
            sql.contains("pg_c_utf8"),
            "builtin C collation on the canonical hex column"
        );
        assert!(
            sql.contains("GENERATED ALWAYS AS"),
            "stored generated columns"
        );
        assert!(sql.contains("cell_hex"));
        assert!(sql.contains("balance_field"));
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.canonical_cells"));
        // The pg17 MERGE-based upsert function is emitted.
        assert!(sql.contains("dregg.merge_cell"));
        assert!(sql.contains("merge_action()"));
        // The pg18 leverage wired in this pass.
        // RETURNING WITH (OLD/NEW) explicit alias on the applicator (both forms).
        assert!(
            sql.contains("RETURNING WITH (OLD AS o, NEW AS n)"),
            "merge_cell uses the pg18 explicit old/new alias"
        );
        // The typed-delta twin applicator (action, balance_delta, nonce_delta).
        assert!(sql.contains("CREATE OR REPLACE FUNCTION dregg.merge_cell_delta"));
        assert!(sql.contains("OUT balance_delta bigint, OUT nonce_delta bigint"));
        // The B-tree skip-scan composite index (mode, balance).
        assert!(sql.contains("cells_by_mode_balance ON dregg.cells (mode, balance)"));
        // Every dev-view is security_invoker (pg15 RLS-through-views).
        assert!(sql.contains("security_invoker = true"));
        // The pg18 AIO observability view over pg_stat_io.
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.mirror_io_stats"));
        assert!(sql.contains("FROM pg_stat_io"));
        // The pg18 AIO IN-FLIGHT view over pg_aios (the live-handles companion).
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.mirror_aio_inflight"));
        assert!(sql.contains("FROM pg_aios"));
        // The pg18 data-checksum integrity-status view (the storage integrity floor).
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.integrity_status"));
        assert!(sql.contains("current_setting('data_checksums')"));
    }

    /// The pg17 login-binding DDL is emittable and shaped: the role→identity map
    /// + the `ON login` event trigger that binds a connecting role to its dregg
    /// capability (docs/PG-DREGG-PG18.md §6). Defensive (anti-lockout) and
    /// SECURITY DEFINER (it reads the mapping the connecting role cannot).
    #[test]
    fn login_binding_ddl_is_emittable_and_defensive() {
        let sql = ddl::login_binding();
        assert!(sql.contains("CREATE TABLE IF NOT EXISTS dregg.role_identity"));
        assert!(sql.contains("CREATE EVENT TRIGGER dregg_login_bind ON login"));
        assert!(sql.contains("dregg.on_login"));
        assert!(sql.contains("SECURITY DEFINER"));
        // Binds the session token + agent from the role's identity row.
        assert!(sql.contains("set_config('dregg.token'"));
        assert!(sql.contains("set_config('dregg.agent'"));
        // Anti-lockout: the hook swallows faults so a bug never locks logins out.
        assert!(sql.contains("EXCEPTION WHEN OTHERS THEN"));
        // The mapping table is not app-writable (it is the trust binding).
        assert!(sql.contains("REVOKE ALL ON dregg.role_identity FROM PUBLIC"));
        // The OAuth→role→cap bind seam: the bind_role SECURITY DEFINER upsert (the
        // tested code path that turns a pg role — e.g. an OAuth-authenticated one —
        // into a dregg capability) + its PUBLIC lockdown + the introspection view.
        assert!(sql.contains("CREATE OR REPLACE FUNCTION dregg.bind_role"));
        assert!(
            sql.contains("REVOKE ALL ON FUNCTION dregg.bind_role(text, bytea, text) FROM PUBLIC")
        );
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.role_bindings"));
        // The introspection view exposes token PRESENCE, never the token itself.
        assert!(sql.contains("(default_token IS NOT NULL)         AS has_token"));
        // The pg18 COPY ON_ERROR bulk-onboarding path: the TEXT staging table + the
        // validate-and-promote function that upserts each staged row through the
        // audited bind_role seam (a malformed row is skipped, never written raw).
        assert!(sql.contains("CREATE TABLE IF NOT EXISTS dregg.role_identity_load"));
        assert!(sql.contains("CREATE OR REPLACE FUNCTION dregg.promote_role_identity_load"));
        assert!(sql.contains("PERFORM dregg.bind_role(r.pg_role, v_agent, r.token)"));
        assert!(sql.contains("REVOKE ALL ON dregg.role_identity_load FROM PUBLIC"));
    }

    /// The pg17 turn-effects JSON_TABLE view ships in Tier C (it reads the
    /// commit_log verified-store door) — a turn's touched cells exploded into rows.
    #[test]
    fn tier_c_emits_the_turn_effects_json_table_view() {
        let sql = ddl::tier_c();
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.turn_effects"));
        assert!(sql.contains("JSON_TABLE(cl.cells, '$[*]'"));
    }

    /// The pg18 INVARIANTS DDL is emittable and uses BOTH pg18-new constraint
    /// forms (docs/PG-DREGG-PG18.md §13.1): `CHECK ... NOT ENFORCED` (declared,
    /// not double-enforced) for the non-negativity/projection floor the spine
    /// guarantees, and `ADD CONSTRAINT ... NOT NULL ... NOT VALID` + `VALIDATE
    /// CONSTRAINT` (the lock-light migration form) for a named cell_root NOT NULL.
    /// Idempotent (every ALTER is guarded on pg_constraint).
    #[test]
    fn invariants_ddl_uses_the_pg18_constraint_forms() {
        let sql = ddl::invariants();
        // (1) the pg18 CHECK ... NOT ENFORCED form — declared, NOT double-enforced.
        assert!(
            sql.contains("CHECK (balance >= 0) NOT ENFORCED"),
            "balance non-negativity declared as a pg18 NOT ENFORCED check"
        );
        assert!(
            sql.contains("CHECK (nonce >= 0) NOT ENFORCED"),
            "nonce non-negativity declared as a pg18 NOT ENFORCED check"
        );
        // The projection-agreement invariant (fields_json.balance == balance).
        assert!(sql.contains("cells_fields_balance_agree"));
        assert!(sql.contains("NOT ENFORCED"));
        // CRUCIAL: the spine is the enforcer, so NO constraint may be APPLIED as
        // ENFORCED. A `) ENFORCED` clause (without the NOT) would mean pg re-decides
        // the verified writer — the double-enforcement anti-pattern. The applied
        // form is always `) NOT ENFORCED`; assert the bare `) ENFORCED` never
        // appears. (The word "ENFORCED" does occur in an explanatory comment about
        // `ALTER ... ENFORCED` to spot-audit, which is documentation, not a clause —
        // so we check the constraint-clause shape, not the bare word.)
        assert!(
            !sql.contains(") ENFORCED"),
            "no constraint may be APPLIED as ENFORCED — the verified turn is the single enforcer"
        );
        // (2) the pg18 NOT NULL ... NOT VALID + VALIDATE lock-light migration form.
        assert!(
            sql.contains("ADD CONSTRAINT cells_cell_root_present NOT NULL cell_root NOT VALID"),
            "cell_root pinned via the pg18 NOT NULL NOT VALID form (brief lock, no scan)"
        );
        assert!(
            sql.contains("VALIDATE CONSTRAINT cells_cell_root_present"),
            "the NOT VALID constraint is then VALIDATEd (the lock-light second step)"
        );
        // Idempotence: each ALTER is guarded on the catalog so re-running is safe.
        assert!(sql.contains("FROM pg_constraint WHERE conname ="));
        assert_eq!(
            sql.matches("DO $$ BEGIN").count(),
            2,
            "two guarded DO blocks: the NOT ENFORCED checks, and the NOT VALID/VALIDATE step"
        );
    }

    /// ANTI-DRIFT: the committed `sql/schema-tierB.sql` and the Rust DDL emitter
    /// (`ddl::tier_b()`) must AGREE — they describe the same tables, views, and
    /// policies. The SQL file is the human-readable, fully-commented form; the
    /// emitter is what the extension ships. This test pins them together so they
    /// cannot silently diverge: every CREATE TABLE / CREATE VIEW / CREATE POLICY
    /// the emitter produces must appear (whitespace- and modifier-normalized) in
    /// the committed SQL file, and vice-versa for the load-bearing relations.
    #[test]
    fn emitted_ddl_agrees_with_committed_sql_file() {
        let emitted = ddl::tier_b();
        let file = include_str!("../sql/schema-tierB.sql");

        // The relation/policy names the two MUST share. (Names, not full bodies:
        // the file carries extra comments + the cell_history/blocks tables that
        // are documented-as-future and not yet in the emitter; the emitter is the
        // shippable subset. Names are the anti-drift contract.)
        let shared = [
            "CREATE TABLE", // turns
            "dregg.turns",
            "dregg.cells",
            "dregg.capabilities",
            "dregg.memory",
            "dregg.cap_edges",
            "dregg.cell_balances",
            "dregg.receipt_chain",
            "dregg.cap_attenuations",
            "dregg.cell_fields",
            "dregg.canonical_cells",
            "JSON_TABLE",
            // pg17 builtin C collation + stored generated columns (canonical state).
            "pg_c_utf8",
            "GENERATED ALWAYS AS",
            "cell_hex",
            "balance_field",
            "dregg.merge_cell",
            "merge_action()",
            // pg18 leverage wired in this pass — pinned so emitter ↔ file cannot drift.
            "dregg.merge_cell_delta", // the typed (action, Δbalance, Δnonce) applicator
            "RETURNING WITH (OLD AS o, NEW AS n)", // the explicit pg18 old/new alias form
            "cells_by_mode_balance",  // the B-tree skip-scan composite index
            "security_invoker = true", // pg15 RLS-through-views, declared
            "dregg.mirror_io_stats",  // the pg18 AIO (pg_stat_io) observability view
            "pg_stat_io",
            "dregg.mirror_aio_inflight", // the pg18 pg_aios in-flight view
            "pg_aios",
            "dregg.integrity_status", // the pg18 data-checksum integrity floor view
            "current_setting('data_checksums')",
            "CREATE POLICY cells_read",
            "CREATE POLICY turns_read",
            "CREATE POLICY caps_read",
            "CREATE POLICY memory_read",
            "dregg_admits('read'",
            "FORCE ROW LEVEL SECURITY",
            "REVOKE INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg FROM PUBLIC",
        ];
        for needle in shared {
            assert!(
                emitted.contains(needle),
                "emitter is missing `{needle}` (drift vs schema-tierB.sql)"
            );
            assert!(
                file.contains(needle),
                "schema-tierB.sql is missing `{needle}` (drift vs ddl::tier_b())"
            );
        }

        // Column-level agreement on the spine table the writer must fill: every
        // column the emitter declares for dregg.cells must be named in the file.
        for col in [
            "cell_id",
            "mode",
            "balance",
            "nonce",
            "fields",
            "fields_json",
            "heap",
            "program",
            "verification_key",
            "delegate",
            "lifecycle",
            "last_ordinal",
            "cell_root",
        ] {
            assert!(
                file.contains(col),
                "schema-tierB.sql missing cells column `{col}`"
            );
            assert!(
                emitted.contains(col),
                "emitter missing cells column `{col}`"
            );
        }
    }

    // ========================================================================
    // §15 federation: the pg18 conflict counters DRIVE re-validation (compose).
    // ========================================================================

    fn sub(name: &str, kinds: [i64; 7]) -> SubscriptionConflicts {
        SubscriptionConflicts {
            subname: name.into(),
            insert_exists: kinds[0],
            update_origin_differs: kinds[1],
            update_exists: kinds[2],
            update_missing: kinds[3],
            delete_origin_differs: kinds[4],
            delete_missing: kinds[5],
            multiple_unique_conflicts: kinds[6],
            total: kinds.iter().sum(),
        }
    }

    #[test]
    fn conflict_total_sums_the_seven_kinds_and_self_checks() {
        // The carried `total` must equal the sum of the seven confl_* columns —
        // the view's conflicts_total IS that sum, and the row self-checks it.
        let s = sub("dregg_tail", [1, 0, 2, 0, 0, 3, 1]);
        assert_eq!(s.total, 7);
        assert_eq!(
            s.recomputed_total(),
            7,
            "the total re-derives from the seven kinds"
        );
        assert!(s.conflicted());

        let clean = sub("clean_tail", [0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(clean.total, 0);
        assert!(!clean.conflicted());
    }

    #[test]
    fn empty_report_is_clear_and_skips_the_tooth() {
        // A publisher / single node has no subscriptions ⇒ no alarm, and the
        // triggered chain re-validation is NOT run (it is the *triggered* check).
        let report = ConflictReport::default();
        assert!(!report.alarm());
        assert_eq!(report.conflicts_total(), 0);

        // The closure MUST NOT be called on the clear path — assert it via a flag.
        let mut ran = false;
        let verdict = federation_health(&report, || {
            ran = true;
            Ok(Some(root(9)))
        });
        assert!(!ran, "no apply conflict ⇒ the chain tooth is NOT triggered");
        assert!(matches!(
            verdict,
            FederationHealth::Clear { subscriptions: 0 }
        ));
        assert!(!verdict.needs_attention());
        assert!(!verdict.chain_broken());
    }

    #[test]
    fn a_clean_subscription_is_clear() {
        // A subscriber WITH a subscription but ZERO conflicts is still clear — the
        // alarm is on conflicts, not on the mere existence of a subscription.
        let report = ConflictReport {
            subscriptions: vec![sub("dregg_tail", [0; 7])],
        };
        assert!(!report.alarm());
        let mut ran = false;
        let verdict = federation_health(&report, || {
            ran = true;
            Ok(None)
        });
        assert!(!ran, "a clean subscription does not trigger re-validation");
        assert!(matches!(
            verdict,
            FederationHealth::Clear { subscriptions: 1 }
        ));
        assert!(report.alarm_line().starts_with("clear:"));
    }

    #[test]
    fn a_conflict_triggers_revalidation_chain_intact() {
        // THE COMPOSITION (happy-anomaly path): a non-zero conflict count fires the
        // alarm AND triggers the chain re-validation; here the chain still
        // re-validates, so the verdict is ConflictsButChainIntact — an anomaly to
        // chase, but the turn chain the subscriber re-validates is intact.
        let report = ConflictReport {
            subscriptions: vec![sub("dregg_tail", [0, 0, 0, 1, 0, 0, 0])], // one update_missing
        };
        assert!(report.alarm());
        assert_eq!(report.conflicts_total(), 1);

        let mut ran = false;
        let verdict = federation_health(&report, || {
            ran = true;
            Ok(Some(root(42))) // the tooth re-validated to this head
        });
        assert!(ran, "the alarm MUST trigger the chain re-validation");
        match verdict {
            FederationHealth::ConflictsButChainIntact {
                conflicts_total,
                head,
                alarm,
            } => {
                assert_eq!(conflicts_total, 1);
                assert_eq!(head, Some(root(42)));
                assert!(
                    alarm.contains("dregg_tail=1"),
                    "the alarm names the offender: {alarm}"
                );
                assert!(
                    alarm.contains("re-validating"),
                    "the alarm states it triggers re-validation"
                );
            }
            other => panic!("expected ConflictsButChainIntact, got {other:?}"),
        }
        // needs_attention is true (an anomaly), but chain_broken is false.
        let verdict2 = federation_health(&report, || Ok(Some(root(42))));
        assert!(verdict2.needs_attention());
        assert!(!verdict2.chain_broken());
    }

    #[test]
    fn a_conflict_with_a_broken_chain_is_the_critical_case() {
        // THE COMPOSITION (severe path): the conflict alarm fires AND the triggered
        // chain re-validation REFUSES — the apply-level divergence coincides with a
        // turn chain the tooth rejects. The subscriber must NOT trust its mirror.
        let report = ConflictReport {
            subscriptions: vec![
                sub("dregg_tail", [0, 0, 0, 0, 0, 1, 0]), // a delete_missing
                sub("dregg_tail2", [2, 0, 0, 0, 0, 0, 0]), // and inserts on a 2nd sub
            ],
        };
        assert!(report.alarm());
        assert_eq!(
            report.conflicts_total(),
            3,
            "summed across both subscriptions"
        );

        let refusal = ChainRefusal::RootMismatch {
            head: root(1),
            prev: root(9),
        };
        let verdict = federation_health(&report, || Err(refusal.clone()));
        match verdict {
            FederationHealth::ConflictsAndChainBroken {
                conflicts_total,
                alarm,
                refusal: r,
            } => {
                assert_eq!(conflicts_total, 3);
                assert_eq!(r, refusal);
                // The alarm names BOTH offenders, sorted.
                assert!(alarm.contains("dregg_tail=1"), "names offender 1: {alarm}");
                assert!(alarm.contains("dregg_tail2=2"), "names offender 2: {alarm}");
            }
            other => panic!("expected ConflictsAndChainBroken, got {other:?}"),
        }
        let verdict2 = federation_health(&report, || Err(refusal.clone()));
        assert!(verdict2.needs_attention());
        assert!(verdict2.chain_broken(), "this is the do-not-trust signal");
        assert!(verdict2.summary().contains("CRITICAL"));
    }

    #[test]
    fn alarm_aggregates_across_subscriptions() {
        // The headline alarm is the SUM across subscriptions; a clean one and a
        // conflicted one together still alarm (on the conflicted one).
        let report = ConflictReport {
            subscriptions: vec![sub("clean", [0; 7]), sub("dirty", [5, 0, 0, 0, 0, 0, 0])],
        };
        assert!(report.alarm());
        assert_eq!(report.conflicts_total(), 5);
        // Only the dirty one is named as an offender.
        let line = report.alarm_line();
        assert!(line.contains("dirty=5"));
        assert!(
            !line.contains("clean="),
            "a clean subscription is not an offender: {line}"
        );
        // The conflicted() iterator yields exactly the dirty one.
        let offenders: Vec<&str> = report.conflicted().map(|s| s.subname.as_str()).collect();
        assert_eq!(offenders, vec!["dirty"]);
    }
}
