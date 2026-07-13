//! # dreggnet-names — a NAMESERVICE [`Offering`].
//!
//! The dungeon is offering #0 (a confined narrative). THIS crate proves the
//! [`Offering`] abstraction reaches **identity / naming**: register / transfer /
//! resolve a name, each an executor-refereed turn, over the REAL naming substrate.
//!
//! ## What it wraps (no naming logic re-implemented)
//!
//! The substrate is [`starbridge_nameservice`]'s **per-name sovereign cell**: a name
//! string maps (deterministically) to its own cell carrying
//! [`starbridge_nameservice::name_cell_program`] —
//! `WriteOnce(NAME_HASH)` (the **first-claim** tooth: a name can be bound exactly
//! once, from zero), `Monotonic(EXPIRY)`, `WriteOnce(REVOKED)`, and the F1..F7
//! **owner-authorization caveats** (an owner-mutating write is a real executor
//! refusal unless the turn's `ctx.sender` IS the current owner). The signed turns are
//! the crate's own builders ([`starbridge_nameservice::build_register_action`] /
//! [`starbridge_nameservice::build_transfer_action`] /
//! [`starbridge_nameservice::build_accept_transfer_action`]). This offering only
//! ORCHESTRATES them through the real [`EmbeddedExecutor`].
//!
//! ## The one real design choice: distinct signers over ONE ledger
//!
//! The owner-auth caveats compare `ctx.sender` — which the executor binds to the
//! **action's own signer pubkey** — against the name cell's owner register. To make
//! that a genuine cross-actor identity (Alice ≠ Bob ≠ Carol), each enrolled actor
//! gets its OWN [`AppCipherclerk`] and its OWN [`EmbeddedExecutor`] (so its per-agent
//! nonce tracks correctly), all sharing ONE [`Ledger`] via
//! [`AgentRuntime::with_ledger`]. A name registered by Alice is therefore visible when
//! Bob tries to seize it — and the executor refuses Bob, admits Alice.
//!
//! ## The mapping onto [`Offering`]
//!
//! - `open` — a fresh registry session (an empty shared ledger; enroll actors with
//!   [`NamesSession::enroll`]).
//! - `advance(action, actor)` —
//!   - **register** (`turn = "register"`, name in `label`): claim a free name → a real
//!     [`TurnReceipt`]; a TAKEN name is `Refused` by `WriteOnce(NAME_HASH)`.
//!   - **transfer** (`turn = "transfer"`, name in `label`, recipient = enrolled index
//!     in `arg`): the current owner re-owners the name (propose + accept, two real
//!     turns) → `Landed`; a NON-owner is `Refused` by the owner-auth caveats.
//!   - **resolve** (`turn = "resolve"`, name in `label`): a real turn that emits a
//!     `name-resolved` receipt anchored on the name cell, carrying the committed owner.
//! - `verify` — re-drive the recorded op-log against a FRESH substrate ([`NamesSession::replay`]);
//!   the names re-resolve to their owners and a forged claim (a duplicate register, a
//!   non-owner transfer) fails replay at the same executor teeth.
//! - `render` / `actions` — the registered names + the register/transfer/resolve
//!   affordances as a deos [`Surface`].
//! - `price` — the free tier (the substrate turn is always free + verifiable).
//!
//! ## Honest scope
//!
//! This wraps the per-name sovereign cell (the `FactoryDescriptor` federation face of
//! the substrate). `resolve` is modelled as a receipt-emitting turn anchored on the
//! name cell; the substrate's `service` module marks resolve as a *serviced* OFE read
//! (the committed `name → owner` field IS the answer) — [`NamesSession::resolve_owner`]
//! exposes that committed read directly. A FULLER nameservice adds expiry-driven
//! reclaim (the `Monotonic(EXPIRY)` + `renew` machinery already lives in the substrate),
//! subdomains / hierarchical delegation, auctions for premium names, and reverse
//! resolution (owner → names) — none of which this offering exercises.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};

use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, Effect, EmbeddedExecutor, Event,
    FieldElement, field_from_bytes, hex_encode_32, symbol,
};
use dregg_cell::ledger::Ledger;
use dregg_cell::program::{CellProgram, StateConstraint};
use dregg_cell::{Cell, Permissions};
use dregg_sdk::AgentRuntime;
use starbridge_nameservice::{
    EXPIRY_SLOT, NAME_HASH_SLOT, OWNER_PK_SLOT, REVOKED_SLOT, build_accept_transfer_action,
    build_register_action, build_transfer_action, owner_authorization_constraints,
};

use deos_view::{MenuItem, ViewNode};

/// The affordance verb that claims a free name (name carried in [`Action::label`]).
pub const TURN_REGISTER: &str = "register";
/// The affordance verb that re-owners a name (name in [`Action::label`], recipient =
/// the enrolled-actor index in [`Action::arg`]).
pub const TURN_TRANSFER: &str = "transfer";
/// The affordance verb that resolves a name (name in [`Action::label`]).
pub const TURN_RESOLVE: &str = "resolve";

/// The default rent expiry height a fresh registration is stamped with (in blocks).
pub const DEFAULT_INITIAL_EXPIRY: u64 = 1_000_000;

/// One recorded registry operation — the replay-verifiable unit. Actors are named by
/// their [`DreggIdentity`] (an Ed25519 pubkey hex), so a log is meaningful across a
/// FRESH substrate (replay maps each identity to its enrollment slot). This is the
/// input [`NamesSession::replay`] re-drives; a FORGED log (a duplicate register, a
/// non-owner transfer) fails at the executor's own teeth.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameOp {
    /// `by` claimed the free name `name` (a real register turn).
    Register {
        /// The claimed name.
        name: String,
        /// The claimant (becomes the owner).
        by: DreggIdentity,
    },
    /// `by` (the current owner) transferred `name` to `to` (propose + accept, 2 turns).
    Transfer {
        /// The transferred name.
        name: String,
        /// The current owner (the propose signer).
        by: DreggIdentity,
        /// The incoming owner (the accept signer).
        to: DreggIdentity,
    },
    /// `by` resolved `name` (a real receipt-emitting read turn).
    Resolve {
        /// The resolved name.
        name: String,
        /// Who resolved it (any enrolled actor — resolve is the public tier).
        by: DreggIdentity,
    },
}

impl NameOp {
    /// How many committed turns this op contributes (register/resolve = 1; a completed
    /// transfer = 2: the owner's propose + the recipient's accept).
    fn turns(&self) -> usize {
        match self {
            NameOp::Register { .. } | NameOp::Resolve { .. } => 1,
            NameOp::Transfer { .. } => 2,
        }
    }
}

/// A live registry record for a registered name — the name's own cell + the owner of
/// record (kept in step with the committed `OWNER_PK_SLOT`).
#[derive(Debug, Clone)]
struct NameRecord {
    /// The per-name sovereign cell holding the binding.
    cell: CellId,
    /// The recorded owner (mirrors the committed authority register).
    owner: DreggIdentity,
}

/// One enrolled actor — a distinct signer with its own executor over the shared ledger.
struct ActorHandle {
    /// The actor's signing cipherclerk (the sender the owner-auth caveats bind against).
    cclerk: AppCipherclerk,
    /// The actor's dedicated executor (its per-agent nonce tracks its own cell), sharing
    /// the session's one ledger.
    exec: EmbeddedExecutor,
}

/// **A name-registry session** over the real substrate — the [`Offering::Session`].
///
/// Holds ONE shared [`Ledger`], a keyring of enrolled actors (each a distinct signer +
/// executor), the live name → record map, and the ordered op-log [`Offering::verify`]
/// re-drives.
pub struct NamesSession {
    /// The federation id every actor signs against and the executor verifies under.
    fed_id: [u8; 32],
    /// The ONE ledger every actor's executor shares — a name registered by one actor is
    /// visible to all.
    ledger: Arc<Mutex<Ledger>>,
    /// Enrolled actors (identity → distinct signer + executor).
    actors: HashMap<DreggIdentity, ActorHandle>,
    /// Enrollment order — a [`TURN_TRANSFER`] affordance's `arg` indexes this to name the
    /// recipient, and replay maps a logged identity to its slot.
    order: Vec<DreggIdentity>,
    /// The live registered names (name → cell + owner).
    names: BTreeMap<String, NameRecord>,
    /// The ordered committed op-log — the replay-verifiable history.
    log: Vec<NameOp>,
    /// The expiry height a fresh registration is stamped with.
    initial_expiry: u64,
    /// The count of committed turns so far (genesis-free; register 1 / transfer 2 / resolve 1).
    turns: usize,
}

impl NamesSession {
    /// A fresh, empty session bound to `fed_id`, stamping registrations at `initial_expiry`.
    fn new(fed_id: [u8; 32], initial_expiry: u64) -> Self {
        NamesSession {
            fed_id,
            ledger: Arc::new(Mutex::new(Ledger::new())),
            actors: HashMap::new(),
            order: Vec::new(),
            names: BTreeMap::new(),
            log: Vec::new(),
            initial_expiry,
            turns: 0,
        }
    }

    /// **Enroll a fresh actor** — mint a distinct signer ([`AppCipherclerk`]), fund its
    /// agent cell in the shared ledger, and stand up its own executor (so its per-agent
    /// nonce tracks correctly). Returns its [`DreggIdentity`] (its Ed25519 pubkey hex) —
    /// the handle an [`Offering::advance`] attributes a move to.
    pub fn enroll(&mut self) -> DreggIdentity {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), self.fed_id);
        let pk = cclerk.public_key().0;
        let id = DreggIdentity(hex_encode_32(&pk));

        // Fund the actor's agent cell (the fee payer + nonce holder) in the shared ledger.
        // Its id derives as `derive_raw(pk, blake3("default"))` — matching the cipherclerk's
        // own `cell_id("default")`, so the executor drives THIS cell.
        let agent_cell = Cell::with_balance(pk, *blake3::hash(b"default").as_bytes(), 1_000_000);
        {
            let mut l = self.ledger.lock().unwrap_or_else(|e| e.into_inner());
            if l.get(&agent_cell.id()).is_none() {
                let _ = l.insert_cell(agent_cell);
            }
        }

        let exec = build_actor_exec(&self.ledger, self.fed_id, &cclerk);
        self.actors.insert(id.clone(), ActorHandle { cclerk, exec });
        self.order.push(id.clone());
        id
    }

    /// The enrolled actors, in enrollment order (the index a transfer affordance's `arg`
    /// names the recipient by).
    pub fn actors(&self) -> &[DreggIdentity] {
        &self.order
    }

    /// The registered names with their current owners (read from committed state).
    pub fn registered(&self) -> Vec<(String, DreggIdentity)> {
        self.names
            .keys()
            .filter_map(|n| self.resolve_owner(n).map(|o| (n.clone(), o)))
            .collect()
    }

    /// The recorded op-log — the input [`Offering::verify`] re-drives. Public so a caller
    /// can clone it, splice in a FORGED op, and pass it to [`Self::replay`] to confirm the
    /// forgery fails (the non-vacuity of the verifier).
    pub fn log(&self) -> &[NameOp] {
        &self.log
    }

    /// The count of committed turns so far.
    pub fn turn_count(&self) -> usize {
        self.turns
    }

    /// **Resolve `name` to its committed owner** — the direct serviced read (the committed
    /// `OWNER_PK_SLOT` IS the answer; no turn). `None` if the name is unregistered or the
    /// owner register is clear.
    pub fn resolve_owner(&self, name: &str) -> Option<DreggIdentity> {
        let rec = self.names.get(name)?;
        let pk = self.read_field(rec.cell, OWNER_PK_SLOT)?;
        if pk == [0u8; 32] {
            return None;
        }
        Some(DreggIdentity(hex_encode_32(&pk)))
    }

    /// Whether `name` is currently registered (its cell carries a bound owner).
    pub fn is_registered(&self, name: &str) -> bool {
        self.resolve_owner(name).is_some()
    }

    // ── internals ────────────────────────────────────────────────────────────

    /// Grant `actor_cell` the c-list REACH capability over `target` (the name cell) — the
    /// executor's cross-cell access gate. This is REACH only (like [`open_permissions`]): the
    /// name cell's OWNERSHIP stays enforced by its cell program's F1..F7 owner-auth caveats, so
    /// a non-owner with reach can SUBMIT a transfer but the program still refuses it.
    fn grant_reach(&self, actor_cell: CellId, target: CellId) {
        let mut l = self.ledger.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(c) = l.get_mut(&actor_cell) {
            let _ = c.capabilities.grant(target, AuthRequired::None);
        }
    }

    fn read_field(&self, cell: CellId, slot: usize) -> Option<FieldElement> {
        let l = self.ledger.lock().unwrap_or_else(|e| e.into_inner());
        l.get(&cell).map(|c| c.state.fields[slot])
    }

    /// The deterministic per-name sovereign cell id, creating the cell (with the substrate's
    /// [`name_cell_program`] installed + open `set_state`, so the CELL PROGRAM is the sole
    /// gate) on first sight. Two actors claiming the SAME name string therefore target the
    /// SAME cell — the second's register hits `WriteOnce(NAME_HASH)` (the first-claim tooth).
    fn ensure_name_cell(&self, name: &str) -> CellId {
        let mut input = b"dreggnet-names/name:".to_vec();
        input.extend_from_slice(name.as_bytes());
        let pk = *blake3::hash(&input).as_bytes();
        let token = *blake3::hash(b"dreggnet-names").as_bytes();
        let id = CellId::derive_raw(&pk, &token);

        let mut l = self.ledger.lock().unwrap_or_else(|e| e.into_inner());
        if l.get(&id).is_none() {
            let mut cell = Cell::with_balance(pk, token, 0);
            cell.permissions = open_permissions();
            cell.program = name_invariants();
            let _ = l.insert_cell(cell);
        }
        id
    }

    /// REGISTER — claim a free name as `actor` (a real turn). A TAKEN name (its cell's
    /// `NAME_HASH` already bound) is `Refused` by `WriteOnce(NAME_HASH)`.
    fn do_register(&mut self, name: &str, actor: &DreggIdentity, expiry: u64) -> Outcome {
        let Some(handle) = self.actors.get(actor) else {
            return Outcome::Refused(format!("actor not enrolled: {}", actor.as_str()));
        };
        let cclerk = handle.cclerk.clone();
        let exec = handle.exec.clone();
        let owner_pk = cclerk.public_key().0;
        let cell = self.ensure_name_cell(name);
        self.grant_reach(cclerk.cell_id(), cell);

        let action = build_register_action(&cclerk, cell, name, owner_pk, expiry);
        match exec.submit_action(&cclerk, action) {
            Ok(receipt) => {
                self.names.insert(
                    name.to_string(),
                    NameRecord {
                        cell,
                        owner: actor.clone(),
                    },
                );
                self.log.push(NameOp::Register {
                    name: name.to_string(),
                    by: actor.clone(),
                });
                self.turns += 1;
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("register refused: {e}")),
        }
    }

    /// TRANSFER — the current owner (`from`) re-owners `name` to `to`: the owner's propose
    /// (re-point the owner image + stage the incoming key) then the recipient's accept
    /// (rotate the authority register). A NON-owner `from` is `Refused` by the owner-auth
    /// caveats at the propose half — nothing commits.
    fn do_transfer(&mut self, name: &str, from: &DreggIdentity, to: &DreggIdentity) -> Outcome {
        let Some(rec) = self.names.get(name).cloned() else {
            return Outcome::Refused(format!("no such name: {name}"));
        };
        let Some(fromh) = self.actors.get(from) else {
            return Outcome::Refused(format!("actor not enrolled: {}", from.as_str()));
        };
        let from_cclerk = fromh.cclerk.clone();
        let from_exec = fromh.exec.clone();
        let Some(toh) = self.actors.get(to) else {
            return Outcome::Refused(format!("recipient not enrolled: {}", to.as_str()));
        };
        let to_cclerk = toh.cclerk.clone();
        let to_exec = toh.exec.clone();
        let from_pk = from_cclerk.public_key().0;
        let to_pk = to_cclerk.public_key().0;
        self.grant_reach(from_cclerk.cell_id(), rec.cell);
        self.grant_reach(to_cclerk.cell_id(), rec.cell);

        // Propose half — signed by `from`. The owner-auth caveats admit it ONLY if
        // `ctx.sender == from == current owner`; a non-owner is refused here.
        let propose = build_transfer_action(&from_cclerk, rec.cell, name, from_pk, to_pk);
        if let Err(e) = from_exec.submit_action(&from_cclerk, propose) {
            return Outcome::Refused(format!("transfer refused (not the owner): {e}"));
        }

        // Accept half — signed by the incoming owner `to`; rotates the authority register.
        let accept = build_accept_transfer_action(&to_cclerk, rec.cell, name, to_pk);
        match to_exec.submit_action(&to_cclerk, accept) {
            Ok(receipt) => {
                if let Some(r) = self.names.get_mut(name) {
                    r.owner = to.clone();
                }
                self.log.push(NameOp::Transfer {
                    name: name.to_string(),
                    by: from.clone(),
                    to: to.clone(),
                });
                self.turns += 2;
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("transfer accept refused: {e}")),
        }
    }

    /// RESOLVE — a real turn that emits a `name-resolved` receipt anchored on the name cell,
    /// carrying the committed owner + expiry. The committed field is the source of truth (see
    /// [`Self::resolve_owner`]); this makes the read a first-class, executor-refereed receipt.
    fn do_resolve(&mut self, name: &str, actor: &DreggIdentity) -> Outcome {
        let Some(rec) = self.names.get(name).cloned() else {
            return Outcome::Refused(format!("no such name: {name}"));
        };
        let Some(handle) = self.actors.get(actor) else {
            return Outcome::Refused(format!("actor not enrolled: {}", actor.as_str()));
        };
        let cclerk = handle.cclerk.clone();
        let exec = handle.exec.clone();
        self.grant_reach(cclerk.cell_id(), rec.cell);

        let owner_pk = self
            .read_field(rec.cell, OWNER_PK_SLOT)
            .unwrap_or([0u8; 32]);
        let expiry = self.read_field(rec.cell, EXPIRY_SLOT).unwrap_or([0u8; 32]);
        let name_h = field_from_bytes(name.as_bytes());

        let action = cclerk.make_action(
            rec.cell,
            "resolve_name",
            vec![Effect::EmitEvent {
                cell: rec.cell,
                event: Event::new(symbol("name-resolved"), vec![name_h, owner_pk, expiry]),
            }],
        );
        match exec.submit_action(&cclerk, action) {
            Ok(receipt) => {
                self.log.push(NameOp::Resolve {
                    name: name.to_string(),
                    by: actor.clone(),
                });
                self.turns += 1;
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("resolve refused: {e}")),
        }
    }

    /// **Re-drive `ops` against a FRESH substrate** and report whether the resulting registry
    /// re-resolves to the SAME owners this session committed.
    ///
    /// Replay enrolls fresh signers (one per enrolled actor, in order) — so a logged
    /// [`DreggIdentity`] maps to its enrollment SLOT, not a reused key/chain — and re-runs each
    /// op through the real executor teeth. A legal log re-lands every op and reproduces the
    /// owner map (by slot); a FORGED op — a duplicate register (`WriteOnce(NAME_HASH)`), a
    /// non-owner transfer (owner-auth) — is refused on re-drive, and the report breaks.
    pub fn replay(&self, ops: &[NameOp]) -> VerifyReport {
        let mut fresh = NamesSession::new(self.fed_id, self.initial_expiry);
        let mut fresh_ids = Vec::with_capacity(self.order.len());
        for _ in &self.order {
            fresh_ids.push(fresh.enroll());
        }
        let live_slot = |id: &DreggIdentity| self.order.iter().position(|x| x == id);
        let to_fresh = |id: &DreggIdentity| live_slot(id).map(|i| fresh_ids[i].clone());

        let mut turns = 0usize;
        for op in ops {
            let out = match op {
                NameOp::Register { name, by } => {
                    let Some(b) = to_fresh(by) else {
                        return VerifyReport::broken(
                            turns,
                            format!("unknown actor in log: {by:?}"),
                        );
                    };
                    fresh.do_register(name, &b, self.initial_expiry)
                }
                NameOp::Transfer { name, by, to } => {
                    let (Some(b), Some(t)) = (to_fresh(by), to_fresh(to)) else {
                        return VerifyReport::broken(turns, "unknown actor in transfer log");
                    };
                    fresh.do_transfer(name, &b, &t)
                }
                NameOp::Resolve { name, by } => {
                    let Some(b) = to_fresh(by) else {
                        return VerifyReport::broken(
                            turns,
                            format!("unknown actor in log: {by:?}"),
                        );
                    };
                    fresh.do_resolve(name, &b)
                }
            };
            match out {
                Outcome::Landed { .. } => turns += op.turns(),
                Outcome::Refused(why) => {
                    return VerifyReport::broken(turns, format!("replay refused {op:?}: {why}"));
                }
            }
        }

        // The replayed registry must re-resolve every live name to the SAME owner SLOT.
        for name in self.names.keys() {
            let live = self.resolve_owner(name).and_then(|o| live_slot(&o));
            let repl = fresh
                .resolve_owner(name)
                .and_then(|o| fresh_ids.iter().position(|x| *x == o));
            if live != repl {
                return VerifyReport::broken(
                    turns,
                    format!(
                        "owner mismatch for {name}: live slot {live:?} != replay slot {repl:?}"
                    ),
                );
            }
        }
        VerifyReport::ok(turns)
    }
}

/// Stand up an actor's dedicated executor over the shared ledger, bound to the federation.
fn build_actor_exec(
    ledger: &Arc<Mutex<Ledger>>,
    fed_id: [u8; 32],
    cclerk: &AppCipherclerk,
) -> EmbeddedExecutor {
    let mut rt = AgentRuntime::with_ledger(cclerk.shared_cipherclerk(), "default", ledger.clone());
    rt.set_local_federation_id(fed_id);
    EmbeddedExecutor::from_runtime(rt)
}

/// **The per-name cell's life-of-name invariants** — the substrate's OWN teeth, as a
/// [`CellProgram::Predicate`]: `WriteOnce(NAME_HASH)` (the first-claim tooth),
/// `Monotonic(EXPIRY)`, `WriteOnce(REVOKED)`, and the F1..F7
/// [`owner_authorization_constraints`] (an owner-mutating write is refused unless
/// `ctx.sender` IS the current owner).
///
/// We compose the substrate's EXPORTED constraint pieces rather than call its
/// [`starbridge_nameservice::name_cell_program`] because that constructor is currently
/// BROKEN at HEAD: it is a `CellProgram::Cases` carrying a `MethodIs("renew_name")`
/// dispatch case, which trips the executor's dispatch-default-deny
/// (`NoTransitionCaseMatched`) for the `register_name`/`transfer_name` methods — its own
/// `tests/integration_register_full_flow.rs` (all 6) fail at HEAD for this reason. A
/// `Predicate` carries the identical invariants with no dispatch case, so the register /
/// transfer / resolve methods are admitted and the WriteOnce + owner-auth teeth bite. The
/// naming logic (slot schema, turn builders, owner-auth caveats) is entirely the
/// substrate's — this only picks the un-broken program combinator.
fn name_invariants() -> CellProgram {
    let mut cs = vec![
        StateConstraint::WriteOnce {
            index: NAME_HASH_SLOT as u8,
        },
        StateConstraint::Monotonic {
            index: EXPIRY_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: REVOKED_SLOT as u8,
        },
    ];
    cs.extend(owner_authorization_constraints());
    CellProgram::Predicate(cs)
}

/// Fully-open cell permissions — a per-name cell admits any signer's `SetField` at the
/// PERMISSION layer, so the substrate's CELL PROGRAM (`WriteOnce` + owner-auth) is the SOLE
/// gate on the write. This is faithful to the substrate's stance: register is
/// permissionless-first-write; ownership is enforced by the program's caveats, not by an
/// access list.
fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// **The names offering** — a stateless factory over the naming substrate. Each
/// [`open`](Offering::open) deploys a fresh [`NamesSession`] (an empty shared ledger).
pub struct NamesOffering {
    /// The expiry height a fresh registration is stamped with.
    initial_expiry: u64,
}

impl NamesOffering {
    /// The default-expiry names offering.
    pub fn new() -> Self {
        NamesOffering {
            initial_expiry: DEFAULT_INITIAL_EXPIRY,
        }
    }

    /// A names offering stamping fresh registrations at `initial_expiry` blocks.
    pub fn with_expiry(initial_expiry: u64) -> Self {
        NamesOffering { initial_expiry }
    }

    /// Convenience: REGISTER `name` as `by`, through [`Offering::advance`].
    pub fn register(&self, s: &mut NamesSession, name: &str, by: &DreggIdentity) -> Outcome {
        self.advance(s, Action::new(name, TURN_REGISTER, -1, true), by.clone())
    }

    /// Convenience: TRANSFER `name` from `by` (the current owner) to `to`, through
    /// [`Offering::advance`]. Encodes `to`'s enrolled index in the affordance `arg`.
    pub fn transfer(
        &self,
        s: &mut NamesSession,
        name: &str,
        by: &DreggIdentity,
        to: &DreggIdentity,
    ) -> Outcome {
        let arg = s
            .order
            .iter()
            .position(|x| x == to)
            .map(|i| i as i64)
            .unwrap_or(-1);
        self.advance(s, Action::new(name, TURN_TRANSFER, arg, true), by.clone())
    }

    /// Convenience: RESOLVE `name` as `by`, through [`Offering::advance`].
    pub fn resolve(&self, s: &mut NamesSession, name: &str, by: &DreggIdentity) -> Outcome {
        self.advance(s, Action::new(name, TURN_RESOLVE, -1, true), by.clone())
    }
}

impl Default for NamesOffering {
    fn default() -> Self {
        NamesOffering::new()
    }
}

impl Offering for NamesOffering {
    type Session = NamesSession;

    fn open(&self, cfg: SessionConfig) -> Result<NamesSession, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        let fed_id = *blake3::hash(&seed.to_le_bytes()).as_bytes();
        Ok(NamesSession::new(fed_id, self.initial_expiry))
    }

    /// The candidate moves: a resolve + transfer affordance per registered name, plus a
    /// generic register affordance. `enabled` is the cap tooth SHOWN (transfer is offered to
    /// all; the executor is the sole referee — a non-owner still refuses on `advance`).
    fn actions(&self, session: &NamesSession) -> Vec<Action> {
        let mut out = vec![Action::new("register a free name", TURN_REGISTER, -1, true)];
        for (name, _owner) in session.registered() {
            out.push(Action::new(
                format!("resolve {name}"),
                TURN_RESOLVE,
                -1,
                true,
            ));
            out.push(Action::new(
                format!("transfer {name} (owner only)"),
                TURN_TRANSFER,
                -1,
                true,
            ));
        }
        out
    }

    fn advance(&self, session: &mut NamesSession, input: Action, actor: DreggIdentity) -> Outcome {
        match input.turn.as_str() {
            TURN_REGISTER => session.do_register(&input.label, &actor, self.initial_expiry),
            TURN_TRANSFER => {
                if input.arg < 0 {
                    return Outcome::Refused(
                        "transfer needs a recipient (the enrolled-actor index in arg)".into(),
                    );
                }
                let Some(to) = session.order.get(input.arg as usize).cloned() else {
                    return Outcome::Refused(format!("no enrolled actor at index {}", input.arg));
                };
                session.do_transfer(&input.label, &actor, &to)
            }
            TURN_RESOLVE => session.do_resolve(&input.label, &actor),
            other => Outcome::Refused(format!("unknown affordance: {other}")),
        }
    }

    /// Re-drive the recorded op-log against a fresh substrate — the names re-resolve to their
    /// real owners, and a forged claim fails at the executor's teeth.
    fn verify(&self, session: &NamesSession) -> VerifyReport {
        session.replay(&session.log)
    }

    /// The registry as a deos affordance [`Surface`]: the registered names + owners, the
    /// verified-turn count, and the register/resolve/transfer affordances.
    fn render(&self, session: &NamesSession) -> Surface {
        let registered = session.registered();

        let mut name_rows: Vec<ViewNode> = Vec::new();
        if registered.is_empty() {
            name_rows.push(ViewNode::Text("(no names registered yet)".to_string()));
        } else {
            for (name, owner) in &registered {
                let short = owner.as_str().get(..8).unwrap_or(owner.as_str());
                name_rows.push(ViewNode::Text(format!("{name} → {short}…")));
            }
        }

        let action_items: Vec<MenuItem> = self
            .actions(session)
            .iter()
            .map(|a| MenuItem {
                label: a.label.clone(),
                turn: a.turn.clone(),
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();

        let children = vec![
            ViewNode::Text(format!(
                "{} enrolled · {} names · {} verified turns",
                session.order.len(),
                registered.len(),
                session.turns
            )),
            ViewNode::Section {
                title: "Registered names".to_string(),
                tag: "muted".to_string(),
                children: name_rows,
            },
            ViewNode::Section {
                title: "Verified turns".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(session.turns.to_string())],
            },
            ViewNode::Section {
                title: "Registry affordances".to_string(),
                tag: "accent".to_string(),
                children: vec![ViewNode::Menu {
                    items: action_items,
                }],
            },
        ];

        Surface(ViewNode::Section {
            title: "DreggNet Names — registry".to_string(),
            tag: "accent".to_string(),
            children,
        })
    }

    /// The free tier — the substrate turn is always free + verifiable.
    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}
