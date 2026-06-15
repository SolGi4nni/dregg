//! The EXECUTOR-PD — the firmament's HEART, on the semihost [`EmulatedKernel`].
//!
//! `docs/FIRMAMENT.md §2` names the executor-PD as **L3, the heart**: "*every*
//! authority decision, *every* cap mint/revoke, *every* state transition flows
//! through it." Its seL4 cap partition is exact (`§2` table): `turn_in` (R, the
//! de-enveloped signature-checked turn), `commit_out` (RW, the commit-log/receipt
//! entry handed to persist), and a notification edge to/from each app-PD. It
//! holds **NO device cap, NO NIC cap** — it is pure compute over bytes, and the
//! verified semantics is the only authority over state transitions.
//!
//! `docs/DREGG-DESKTOP-OS.md §3` (the semihosted-seL4 KEYSTONE) states the
//! payoff plainly: **"the verified executor-PD hosts on the host's *ordinary*
//! macOS/Linux Lean runtime ... so the semihost has a REAL verified heart NOW"**
//! — the executor-PD blocker that gates real-seL4 (WALL step 4) does **not** gate
//! the emulator. The real-seL4 [`sel4/dregg-pd/executor-stub`] PD holds this
//! exact seat and maps these exact regions, but idles its verified-turn path
//! until the Lean ELF runtime links. This module is that seat **running its turn
//! path NOW**, over the same [`EmulatedKernel`] IPC the compositor-PD uses.
//!
//! ## The shape (the executor-PD's `turn_in → step → commit_out` contract)
//!
//! The executor-PD is the Endpoint SERVER. An app-PD (the master-interface
//! cockpit, the swarm member, any turn-issuing PD) is a CLIENT that:
//!
//!   1. **stages the turn** into the `turn_in` region ([`memory_region_symbol!`]
//!      → an [`EmulatedKernel`] shm region the executor reads) — the
//!      length-prefixed turn bytes (postcard, as the wire carries a `Turn`;
//!      `turn/src/turn.rs` "transmitted via postcard");
//!   2. **`pp_call`s the executor's PP channel** (the synchronous
//!      [`Channel::pp_call`] → kernel `Call`) to signal "a turn is staged",
//!      exactly the `ingress→executor` notify edge (channel id 1) the
//!      executor-stub awaits;
//!   3. the executor **`recv`s, reads `turn_in`, runs the turn through its
//!      [`TurnRunner`]** (on the semihost the cockpit's REAL
//!      `dregg_sdk::embed::DreggEngine` — the verified `TurnExecutor` over a
//!      `dregg_cell::Ledger`), **writes the receipt** (or the rejection reason)
//!      into `commit_out`, and **`reply`s** a 1-byte verdict tag;
//!   4. the app-PD reads the receipt back out of `commit_out`.
//!
//! **The app-PD never touches the ledger** — it hands BYTES to the heart and
//! reads BYTES back. The authority over state lives entirely behind the Endpoint,
//! in the runner. A turn the runner rejects writes NOTHING to `commit_out` past
//! the reason and advances no state (fail-closed — the Rust analogue of the Lean
//! executor returning `Rejected`).
//!
//! ## Reuse, not reinvention (the WELD method)
//!
//! The IPC + shm substrate is the existing [`EmulatedKernel`] (Endpoint
//! `recv`/`reply`, regions) — the SAME primitives the compositor-PD and the
//! 2-PD notify slice ride. The turn semantics is the runner's (on the semihost
//! the genuine `DreggEngine`); this module adds NO executor logic of its own —
//! it is the cap-partitioned **seat + wire**, nothing more. The wire framing is
//! hand-rolled + dependency-free (the firmament's minimal-dep discipline, the
//! same as the compositor-PD's `encode_present`).
//!
//! [`Channel`]: crate::microkit_facade::Channel
//! [`Channel::pp_call`]: crate::microkit_facade::Channel::pp_call
//! [`memory_region_symbol!`]: crate::memory_region_symbol

use std::string::String;
use std::vec::Vec;

use crate::emulated_kernel::{EmulatedKernel, IpcError, Message, ObjectId};

/// The Endpoint message label for a "turn is staged in `turn_in`" request — the
/// `MessageInfo` tag the executor-PD dispatches on (the semihost analogue of the
/// `ingress→executor` channel-1 signal the executor-stub awaits).
pub const LABEL_RUN_TURN: u64 = 1;

/// The reply label when a turn COMMITTED — the receipt is in `commit_out`. The
/// reply payload is the receipt's byte length (so the app-PD reads exactly that
/// many bytes back out of `commit_out`).
pub const LABEL_TURN_COMMITTED: u64 = 2;

/// The reply label when a turn was REJECTED by the runner (the verified executor
/// refused — unauthorized effect / non-conservation / broken receipt-chain). The
/// reply payload is the rejection-reason byte length (in `commit_out`). A
/// rejection is a FEATURE: it is the ocap/verification guarantees firing.
pub const LABEL_TURN_REJECTED: u64 = 3;

/// The runner the executor-PD drives a staged turn through — **the verified
/// semantics behind the Endpoint.**
///
/// On the semihost this is implemented by the cockpit's REAL
/// `dregg_sdk::embed::DreggEngine` (the verified `TurnExecutor` over a
/// `dregg_cell::Ledger`); the firmament keeps the trait here so the executor-PD
/// is decoupled from the `dregg-turn`/`dregg-sdk` turn types — the wire carries
/// BYTES, and only the runner gives them meaning. (The real seL4 executor-PD's
/// runner is `execFullForestG` via `dregg-lean-ffi`; the contract — "turn bytes
/// in, receipt-or-reason bytes out, fail-closed" — is identical.)
pub trait TurnRunner {
    /// Run the turn whose postcard bytes are `turn_bytes` through the verified
    /// executor, mutating the runner's owned ledger.
    ///
    /// Returns `Ok(receipt_bytes)` on a committed turn (the encoded
    /// `TurnReceipt` to write into `commit_out`), or `Err(reason)` if the
    /// executor REJECTED it (the human-legible reason — the ledger is unchanged,
    /// fail-closed). A malformed/undecodable `turn_bytes` is an `Err` too (a
    /// garbage stage never advances state).
    fn run_turn_bytes(&mut self, turn_bytes: &[u8]) -> Result<Vec<u8>, String>;
}

/// The outcome of one served turn through the executor-PD (what the server
/// recorded, for a single-threaded harness to assert; mirrors the
/// `commit_out` + reply the app-PD reads).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ServedTurn {
    /// The turn COMMITTED — the receipt bytes are in `commit_out` (and echoed
    /// here). The app-PD reads them back via [`ExecutorPd::commit_out_read`].
    Committed {
        /// The encoded `TurnReceipt` bytes the runner produced (the
        /// `commit_out` payload — the on-ledger receipt / commit-log entry).
        receipt: Vec<u8>,
    },
    /// The turn was REJECTED — the reason bytes are in `commit_out` (and echoed
    /// here). No state advanced (fail-closed).
    Rejected {
        /// The rejection reason (the verified executor's refusal — an
        /// unauthorized effect, an overspend, a broken receipt chain). This is
        /// the ocap/verification guarantee firing, not a bug.
        reason: String,
    },
}

impl ServedTurn {
    /// Did the served turn commit?
    pub fn is_committed(&self) -> bool {
        matches!(self, ServedTurn::Committed { .. })
    }

    /// The committed receipt bytes, if it committed.
    pub fn receipt(&self) -> Option<&[u8]> {
        match self {
            ServedTurn::Committed { receipt } => Some(receipt),
            ServedTurn::Rejected { .. } => None,
        }
    }
}

/// THE EXECUTOR-PD — the firmament heart, on the semihost [`EmulatedKernel`].
///
/// It is the Endpoint SERVER for staged turns. It SOLELY reads the `turn_in`
/// region and SOLELY writes the `commit_out` region (the executor's exact
/// `§2` cap partition: `turn_in` R, `commit_out` RW, no device cap), and runs
/// every turn through its [`TurnRunner`] `R` (on the semihost the cockpit's real
/// `DreggEngine`). NO executor logic of its own — the cap-partitioned seat + the
/// `turn_in → step → commit_out` wire, nothing more.
///
/// On a real PD the executor IS its thread, holding `turn_in`/`commit_out` caps
/// the Microkit loader patched in; here `R` (the runner) is owned in-process and
/// the regions are [`EmulatedKernel`] shm — the SAME wire shape, the launch
/// mechanism (a thread / in-process server vs. a real PD) the only difference.
pub struct ExecutorPd<R: TurnRunner> {
    /// The shared [`EmulatedKernel`] (the n=1 microkernel) — the executor holds
    /// it to own its `turn_in`/`commit_out` regions + serve its Endpoint.
    kernel: EmulatedKernel,
    /// The `turn_in` region — R in the executor's cap partition. An app-PD
    /// stages the length-prefixed turn bytes here; the executor reads them. On
    /// the semihost this is an [`EmulatedKernel`] shm region.
    turn_in: ObjectId,
    /// The `commit_out` region — RW in the executor's cap partition. The
    /// executor writes the length-prefixed receipt (or rejection reason) here;
    /// the app-PD reads it back. The commit-log entry persist would durably store.
    commit_out: ObjectId,
    /// The verified turn semantics behind the Endpoint (the cockpit's real
    /// `DreggEngine` on the semihost). The ONLY authority over state.
    runner: R,
    /// How many turns committed (the operator log / boot observable).
    committed: u64,
    /// How many turns the runner rejected (the ocap/verification guarantees
    /// firing — a count, not a failure).
    rejected: u64,
}

impl<R: TurnRunner> ExecutorPd<R> {
    /// A short, honest statement of WHAT this seat is and is NOT — it travels
    /// WITH the code (the don't-launder-vacuity discipline). The executor-PD here
    /// runs the GENUINE verified turn semantics (its runner is the cockpit's real
    /// `DreggEngine` — the `TurnExecutor` over a `Ledger`) over the GENUINE
    /// [`EmulatedKernel`] IPC; the `n = 1` bounds it rides ([`crate::Bounds::LOCAL`])
    /// are genuinely real on the host. What it is NOT: the bare-metal aarch64-sel4
    /// PD (that is WALL step 4 — the Lean ELF runtime port, blocked there, NOT
    /// here). The SAME `TurnRunner`-bytes contract holds on both.
    pub const FIDELITY: &'static str = "\
        The executor-PD seat runs the GENUINE verified turn semantics (its runner \
        is the cockpit's real dregg_sdk::embed::DreggEngine — the TurnExecutor \
        over a dregg_cell::Ledger) over the GENUINE EmulatedKernel IPC (Endpoint \
        recv/reply + turn_in/commit_out shm regions), the SAME primitives the \
        compositor-PD rides. The n=1 bounds (Bounds::LOCAL) are genuinely real on \
        the host (a host present is one map; revoke is synchronous). This is the \
        executor-PD's turn_in→step→commit_out cap partition (FIRMAMENT.md §2) \
        running NOW on the semihost — the verified heart the executor-stub seat \
        idles until the Lean ELF runtime links (WALL step 4, real-seL4 only; NOT \
        a blocker here, NOT laundered as the real-seL4 PD).";

    /// Boot the executor-PD on the [`EmulatedKernel`]: it allocates and SOLELY
    /// holds its `turn_in` (capacity `turn_in_bytes`) and `commit_out` (capacity
    /// `commit_out_bytes`) regions, and takes ownership of `runner` (the verified
    /// semantics). The region caps are never handed to an app-PD; the app-PD
    /// reaches them only by name through the wire it `pp_call`s.
    ///
    /// `turn_in_bytes`/`commit_out_bytes` mirror the executor-stub's region sizes
    /// (`turn_in` 0x100000, `commit_out` 0x400000) — generously sized for a real
    /// turn + receipt. (The boot harness can size them smaller for a unit slice.)
    pub fn boot(
        kernel: EmulatedKernel,
        runner: R,
        turn_in_bytes: usize,
        commit_out_bytes: usize,
    ) -> Self {
        let turn_in = kernel.create_region(turn_in_bytes);
        let commit_out = kernel.create_region(commit_out_bytes);
        ExecutorPd {
            kernel,
            turn_in,
            commit_out,
            runner,
            committed: 0,
            rejected: 0,
        }
    }

    /// The `turn_in` region id — the executor's R-held stage. Exposed so the boot
    /// harness (standing in for an app-PD) can WRITE the staged turn bytes into
    /// it via [`Self::stage_turn`]; it is NEVER an authority over state (the
    /// authority is the runner behind the Endpoint).
    pub fn turn_in(&self) -> ObjectId {
        self.turn_in
    }

    /// The `commit_out` region id — the executor's RW-held commit log. Exposed so
    /// the boot harness (standing in for an app-PD / persist) can READ the
    /// receipt the executor wrote.
    pub fn commit_out(&self) -> ObjectId {
        self.commit_out
    }

    /// Read access to the runner (the verified semantics) — for the harness to
    /// inspect post-state (e.g. the ledger the cockpit's engine holds).
    pub fn runner(&self) -> &R {
        &self.runner
    }

    /// Mutable access to the runner — for the firmament/boot path to seed the
    /// runner's state out-of-band BEFORE turns flow (e.g. install the genesis
    /// cells the cockpit's `World` holds, the way the firmament mints genesis caps
    /// at boot). This is NOT a turn — it does not go through the `turn_in` wire;
    /// it is the trusted root's prerogative over the heart it boots.
    pub fn runner_mut(&mut self) -> &mut R {
        &mut self.runner
    }

    /// How many turns have COMMITTED through this seat (the boot observable).
    pub fn committed_count(&self) -> u64 {
        self.committed
    }

    /// How many turns the runner REJECTED (the ocap/verification guarantees
    /// firing — a count of refusals, not failures).
    pub fn rejected_count(&self) -> u64 {
        self.rejected
    }

    // ── The app-PD's client side of the wire (staging + reading back) ─────────
    //
    // On a real PD these are the app-PD's `memory_region_symbol!` writes/reads on
    // its mapped `turn_in`/`commit_out` views; here the harness drives them
    // through the kernel (the regions are kernel-held shm). They are length-
    // prefixed (4-byte LE length ‖ payload) so the reader takes exactly the bytes
    // the writer staged.

    /// **STAGE a turn** — write the length-prefixed turn bytes into `turn_in`
    /// (the app-PD's `turn_in` write before it signals the executor). Returns the
    /// number of bytes written, or `None` if the turn does not fit the region
    /// (the executor's R-region is finite — an over-large turn is refused at the
    /// stage, fail-closed, never truncated).
    ///
    /// (This delegates to the free [`stage_turn_into`] — an app-PD on its OWN
    /// thread stages through that, with just the shared kernel + the
    /// [`Self::turn_in`] id, NEVER needing a handle to the locked executor while
    /// the executor's thread is parked in `recv`. This convenience is for the
    /// single-thread / harness path where the executor is reachable.)
    pub fn stage_turn(&self, turn_bytes: &[u8]) -> Option<usize> {
        stage_turn_into(&self.kernel, self.turn_in, turn_bytes)
    }

    /// **READ the staged turn** from `turn_in` (the executor's R read after it is
    /// signalled). Returns the length-prefixed payload, or `None` if the stage is
    /// malformed (a zero/over-long length ⇒ a garbage stage, treated as no turn).
    fn read_turn_in(&self) -> Option<Vec<u8>> {
        let region = self.kernel.region_read(self.turn_in)?;
        read_len_prefixed(&region)
    }

    /// **READ the receipt/reason** the executor wrote into `commit_out` (the
    /// app-PD's read after the reply). Returns the length-prefixed payload (the
    /// encoded `TurnReceipt` on commit, or the reason string bytes on reject).
    pub fn commit_out_read(&self) -> Option<Vec<u8>> {
        let region = self.kernel.region_read(self.commit_out)?;
        read_len_prefixed(&region)
    }

    /// Write the length-prefixed `payload` into `commit_out` (the executor's RW
    /// write of the receipt/reason). Internal — the executor's side of the wire.
    fn write_commit_out(&self, payload: &[u8]) {
        let cap = self.kernel.region_len(self.commit_out).unwrap_or(0);
        // The commit_out region is sized for a real receipt; if a pathologically
        // large payload exceeds it we write what fits past the length prefix (the
        // app-PD reads `min(declared, region)` — never out of bounds). In normal
        // operation a receipt fits with room to spare.
        let n = payload.len().min(cap.saturating_sub(4));
        self.kernel.region_with_mut(self.commit_out, |buf| {
            if buf.len() >= 4 {
                buf[0..4].copy_from_slice(&(n as u32).to_le_bytes());
                buf[4..4 + n].copy_from_slice(&payload[..n]);
            }
        });
    }

    // ── The executor-PD's server side (the protected-procedure body) ──────────

    /// **SERVE ONE staged turn — the cap-gated `turn_in → step → commit_out`.**
    ///
    /// The executor-PD's protected-procedure body: read the staged turn from
    /// `turn_in`, run it through the [`TurnRunner`] (the verified semantics), and
    /// write the receipt (on commit) or the reason (on reject) into `commit_out`.
    /// Returns what was served (so a single-threaded harness can assert it) — the
    /// SAME information the reply tag + `commit_out` carry to the app-PD.
    ///
    /// A malformed/missing stage is served as a rejection (fail-closed — a
    /// garbage `turn_in` never advances state).
    pub fn step_staged_turn(&mut self) -> ServedTurn {
        let staged = match self.read_turn_in() {
            Some(b) if !b.is_empty() => b,
            _ => {
                // No (or empty/garbage) turn staged — a rejection that advances
                // nothing. The app-PD reads the reason from commit_out.
                let reason = "no turn staged in turn_in (empty or malformed stage)".to_string();
                self.write_commit_out(reason.as_bytes());
                self.rejected += 1;
                return ServedTurn::Rejected { reason };
            }
        };
        match self.runner.run_turn_bytes(&staged) {
            Ok(receipt) => {
                // The verified executor COMMITTED — write the receipt to
                // commit_out (the commit-log entry persist would durably store).
                self.write_commit_out(&receipt);
                self.committed += 1;
                ServedTurn::Committed { receipt }
            }
            Err(reason) => {
                // The verified executor REJECTED — write the reason to
                // commit_out; no state advanced (fail-closed).
                self.write_commit_out(reason.as_bytes());
                self.rejected += 1;
                ServedTurn::Rejected { reason }
            }
        }
    }

    /// **SERVE ONE turn off the Endpoint** (the cross-PD form): `recv` a
    /// [`LABEL_RUN_TURN`] call (the app-PD's `pp_call` signalling "a turn is
    /// staged"), run [`Self::step_staged_turn`] (read `turn_in` + step +
    /// write `commit_out`), and `reply` a 1-byte verdict tag whose payload is the
    /// `commit_out` byte length. Blocks until an app-PD calls (faithful seL4
    /// Endpoint synchrony). Returns what it served.
    ///
    /// An unknown verb (not `LABEL_RUN_TURN`) is replied REJECTED — the executor
    /// serves only the run-turn protected procedure.
    pub fn serve_turn(&mut self, endpoint: ObjectId) -> Result<ServedTurn, IpcError> {
        let (msg, token) = self.kernel.recv(endpoint)?;
        let served = self.dispatch_turn_message(&msg);
        let reply = match &served {
            ServedTurn::Committed { receipt } => Message::new(
                LABEL_TURN_COMMITTED,
                (receipt.len() as u32).to_le_bytes().to_vec(),
            ),
            ServedTurn::Rejected { reason } => Message::new(
                LABEL_TURN_REJECTED,
                (reason.len() as u32).to_le_bytes().to_vec(),
            ),
        };
        self.kernel.reply(token, reply)?;
        Ok(served)
    }

    /// Serve one turn whose call was staged INLINE (the single-threaded
    /// [`EmulatedKernel::call_served_by`] convenience) — dispatch + the reply
    /// message, with no second thread. The boot harness uses this to run the
    /// executor's protected body on the SAME thread as the calling app-PD stub.
    /// Returns the reply message; the step's side effects (commit_out write +
    /// counts) land on `self`.
    pub fn serve_turn_inline(&mut self, call: Message) -> Message {
        let served = self.dispatch_turn_message(&call);
        match served {
            ServedTurn::Committed { receipt } => Message::new(
                LABEL_TURN_COMMITTED,
                (receipt.len() as u32).to_le_bytes().to_vec(),
            ),
            ServedTurn::Rejected { reason } => Message::new(
                LABEL_TURN_REJECTED,
                (reason.len() as u32).to_le_bytes().to_vec(),
            ),
        }
    }

    /// Dispatch a run-turn message (shared by the cross-thread + inline serve
    /// paths). An unknown verb is a rejection (the executor serves only the
    /// run-turn protected procedure).
    fn dispatch_turn_message(&mut self, msg: &Message) -> ServedTurn {
        if msg.label != LABEL_RUN_TURN {
            let reason = format!("unknown verb {} (executor serves only run-turn)", msg.label);
            self.write_commit_out(reason.as_bytes());
            self.rejected += 1;
            return ServedTurn::Rejected { reason };
        }
        self.step_staged_turn()
    }
}

/// **STAGE turn bytes into a `turn_in` region** — the free, lock-free staging an
/// app-PD does on its OWN thread, given just the shared [`EmulatedKernel`] + the
/// region id (the executor exposes its [`ExecutorPd::turn_in`] id at boot). It
/// writes the length-prefixed bytes (4-byte LE length ‖ payload) and returns the
/// bytes written, or `None` if the turn does not fit (refused at the stage,
/// fail-closed, never truncated).
///
/// This is SEPARATE from [`ExecutorPd::stage_turn`] precisely so a CROSS-PD
/// harness can stage WITHOUT a handle to the executor while the executor's thread
/// is parked in [`EmulatedKernel::recv`] (taking the executor's own lock there) —
/// the app-PD writes the shared region through the kernel directly, exactly as a
/// real app-PD writes its mapped `turn_in` view. (On real seL4 the app-PD's
/// `turn_in` write needs no handle to the executor at all; the kernel handle here
/// is the host's stand-in for the implicit shared mapping.)
pub fn stage_turn_into(
    kernel: &EmulatedKernel,
    turn_in: ObjectId,
    turn_bytes: &[u8],
) -> Option<usize> {
    let need = 4 + turn_bytes.len();
    if need > kernel.region_len(turn_in)? {
        return None;
    }
    kernel.region_with_mut(turn_in, |buf| {
        buf[0..4].copy_from_slice(&(turn_bytes.len() as u32).to_le_bytes());
        buf[4..4 + turn_bytes.len()].copy_from_slice(turn_bytes);
    })?;
    Some(need)
}

/// Read a length-prefixed payload (4-byte LE length ‖ payload) from a region
/// snapshot. Returns `None` if the declared length over-runs the region (a
/// malformed stage — treated as no payload, fail-closed).
fn read_len_prefixed(region: &[u8]) -> Option<Vec<u8>> {
    if region.len() < 4 {
        return None;
    }
    let len = u32::from_le_bytes(region[0..4].try_into().ok()?) as usize;
    if len == 0 || 4 + len > region.len() {
        return None;
    }
    Some(region[4..4 + len].to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::{is_attenuation, AuthRequired};

    /// A MINIMAL real runner for the unit tests: it decodes a 2-byte "attenuation
    /// request" `[held, granted]` over the GENUINE [`is_attenuation`] lattice and
    /// commits iff `granted ⊆ held` (a stand-in for the real `DreggEngine`'s
    /// `granted ⊆ held` gate — the SAME `is_attenuation`, not a parallel model).
    /// On commit the "receipt" is `[held, granted, 0xOK]`; on reject the reason
    /// names the widening. This keeps the firmament's unit tests free of the
    /// heavy `dregg-turn::Turn` codec while exercising the REAL gate over the REAL
    /// `turn_in → step → commit_out` wire. (starbridge-v2 plugs in the FULL
    /// `DreggEngine` runner — see `world.rs::SemihostCockpit`.)
    struct AttenuationRunner {
        committed: u64,
    }

    fn auth_of(b: u8) -> AuthRequired {
        match b {
            0 => AuthRequired::None,
            1 => AuthRequired::Signature,
            2 => AuthRequired::Either,
            _ => AuthRequired::Impossible,
        }
    }

    impl TurnRunner for AttenuationRunner {
        fn run_turn_bytes(&mut self, turn_bytes: &[u8]) -> Result<Vec<u8>, String> {
            if turn_bytes.len() != 2 {
                return Err(format!(
                    "malformed turn: expected 2 bytes, got {}",
                    turn_bytes.len()
                ));
            }
            let held = auth_of(turn_bytes[0]);
            let granted = auth_of(turn_bytes[1]);
            // THE GENUINE GATE: granted ⊆ held (the SAME is_attenuation the real
            // executor's GrantCapability path runs). A widening is REJECTED.
            if is_attenuation(&held, &granted) {
                self.committed += 1;
                Ok(vec![turn_bytes[0], turn_bytes[1], 0xCC]) // 0xCC = committed
            } else {
                Err(format!(
                    "non-attenuating: granted {:?} is wider than held {:?} (granted ⊄ held)",
                    granted, held
                ))
            }
        }
    }

    fn boot() -> ExecutorPd<AttenuationRunner> {
        ExecutorPd::boot(
            EmulatedKernel::new(),
            AttenuationRunner { committed: 0 },
            4096,
            4096,
        )
    }

    #[test]
    fn staged_attenuating_turn_commits_and_receipt_round_trips_through_commit_out() {
        let mut exec = boot();
        // Stage an ATTENUATING turn: held=Either(2), granted=Signature(1) — a
        // genuine narrowing. The app-PD writes turn_in, then signals the executor.
        assert!(exec.stage_turn(&[2, 1]).is_some(), "the turn fits turn_in");
        let served = exec.step_staged_turn();
        assert!(
            served.is_committed(),
            "an attenuating turn COMMITS through the heart"
        );
        // The receipt round-trips through commit_out (the app-PD reads it back).
        let receipt = exec
            .commit_out_read()
            .expect("commit_out holds the receipt");
        assert_eq!(
            receipt,
            vec![2, 1, 0xCC],
            "the committed receipt is in commit_out"
        );
        assert_eq!(exec.committed_count(), 1);
        assert_eq!(exec.rejected_count(), 0);
    }

    #[test]
    fn staged_amplifying_turn_is_rejected_fail_closed() {
        let mut exec = boot();
        // Stage an AMPLIFYING turn: held=Signature(1), granted=Either(2) — a
        // WIDENING. The verified gate must REJECT it; commit_out holds the reason,
        // not a receipt; no state advanced (fail-closed).
        assert!(exec.stage_turn(&[1, 2]).is_some());
        let served = exec.step_staged_turn();
        assert!(
            !served.is_committed(),
            "a widening turn is REJECTED (the gate fires)"
        );
        let reason = exec.commit_out_read().expect("commit_out holds the reason");
        let reason = String::from_utf8(reason).unwrap();
        assert!(
            reason.contains("non-attenuating"),
            "the reason names the widening: {reason}"
        );
        assert_eq!(exec.committed_count(), 0);
        assert_eq!(exec.rejected_count(), 1);
    }

    #[test]
    fn serve_turn_inline_replies_committed_with_receipt_length() {
        let mut exec = boot();
        exec.stage_turn(&[2, 1]).unwrap(); // attenuating
        let reply = exec.serve_turn_inline(Message::new(LABEL_RUN_TURN, vec![]));
        assert_eq!(
            reply.label, LABEL_TURN_COMMITTED,
            "the reply tag is COMMITTED"
        );
        // The reply payload is the receipt byte length; the app-PD reads exactly
        // that many bytes back out of commit_out.
        let declared = u32::from_le_bytes(reply.bytes[..4].try_into().unwrap()) as usize;
        let receipt = exec.commit_out_read().unwrap();
        assert_eq!(
            receipt.len(),
            declared,
            "the reply length matches the commit_out receipt"
        );
    }

    #[test]
    fn serve_turn_inline_replies_rejected_for_a_widening() {
        let mut exec = boot();
        exec.stage_turn(&[1, 2]).unwrap(); // amplifying
        let reply = exec.serve_turn_inline(Message::new(LABEL_RUN_TURN, vec![]));
        assert_eq!(
            reply.label, LABEL_TURN_REJECTED,
            "the reply tag is REJECTED (fail-closed)"
        );
    }

    #[test]
    fn empty_stage_is_a_rejection_not_a_panic() {
        // The executor is signalled with NOTHING staged — it must reject cleanly
        // (a garbage/empty turn_in never advances state), not panic.
        let mut exec = boot();
        let served = exec.step_staged_turn();
        assert!(!served.is_committed(), "an empty stage is rejected");
        assert_eq!(exec.rejected_count(), 1);
    }

    #[test]
    fn unknown_verb_is_rejected() {
        let mut exec = boot();
        exec.stage_turn(&[2, 1]).unwrap();
        // A call with the WRONG label (not LABEL_RUN_TURN) is refused — the
        // executor serves only the run-turn protected procedure.
        let reply = exec.serve_turn_inline(Message::new(0xDEAD, vec![]));
        assert_eq!(reply.label, LABEL_TURN_REJECTED);
        assert_eq!(
            exec.committed_count(),
            0,
            "the wrong verb committed nothing"
        );
    }

    #[test]
    fn over_large_turn_does_not_fit_the_stage() {
        // turn_in is finite; an over-large turn is refused AT THE STAGE (the
        // executor's R-region is bounded — never truncated/overrun).
        let exec = ExecutorPd::boot(
            EmulatedKernel::new(),
            AttenuationRunner { committed: 0 },
            16,
            64,
        );
        // 16-byte region holds 4 (len) + 12 payload; a 20-byte turn does not fit.
        assert!(
            exec.stage_turn(&[0u8; 20]).is_none(),
            "an over-large turn is refused at the stage"
        );
        assert!(
            exec.stage_turn(&[0u8; 12]).is_some(),
            "a turn that fits is staged"
        );
    }
}
