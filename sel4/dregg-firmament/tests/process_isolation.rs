//! THE PROCESS-BACKED BOOT TEST + THE ISOLATION TOOTH (v1, the closed gap).
//!
//! `docs/DREGG-DESKTOP-OS.md §3` (the v1 process-backed-PD upgrade): the SAME PD
//! source that boots on the v0 thread backing (`tests/boot_pds.rs`) boots here
//! on the v1 PROCESS backing — PDs are forked host PROCESSES, so the host MMU
//! enforces address-space separation. This file proves TWO things the v0 test
//! could not:
//!
//!   1. **The same-code boot on the process backing** — m0-hello + the 2-PD
//!      notify slice run with PDs as forked processes (not threads). The notify
//!      IPC still works (PD-A `Signal`s, PD-B `Wait`s, via the kernel-mediated
//!      control socket), proving the facade's same-code claim holds across BOTH
//!      backings.
//!   2. **THE ISOLATION TOOTH v0 lacked** — a PD CANNOT read another PD's
//!      private memory (the MMU faults / it sees only its own memory), AND a PD
//!      CANNOT forge a cap by writing raw bytes (the kernel's epoch-tagged
//!      validity table refuses the fabricated handle). Endpoint/Notification IPC
//!      still works; raw cross-PD memory access / cap forgery is REFUSED.
//!
//! Gated behind `--features process-pd` (Unix only). Run with:
//!   `cargo test --features process-pd --test process_isolation -- --nocapture`
//!
//! NOTE on fork-in-a-test: each test forks children that do simple, bounded
//! work and `_exit`. The kernel (the test's parent process) services each
//! child's control socket inline. We keep the work minimal and the children
//! short-lived — exactly the shape a real PD's `init()` has.

#![cfg(all(feature = "process-pd", unix))]

use std::io::Write;

use dregg_cell::AuthRequired;
use dregg_firmament::process_kernel::{
    CapHandle, KernelReply, ProcessKernel,
};

// ===========================================================================
// PD #1 — m0-hello, on the PROCESS backing. The SAME banner-printing body as
// `tests/boot_pds.rs`'s m0_hello_init / sel4/dregg-pd/m0-hello, but launched as
// a forked PROCESS instead of a thread. The PRINTED TEXT + control flow are
// identical — that is the same-code claim across the thread→process move.
// ===========================================================================

#[test]
fn boot_m0_hello_on_the_process_kernel() {
    let kernel = ProcessKernel::new();
    // m0 services no caps; spawn it with an empty grant set. Its body prints the
    // banner and returns exit code 0 — the literal m0 idle.
    let pd = kernel
        .spawn_pd(vec![], |_client, _granted| {
            println!();
            println!("    ┌─────────────────────────────────────────┐");
            println!("    │   dregg robigalia v1  (semihost/process) │");
            println!("    │   a Rust userspace, PROCESS-isolated PDs │");
            println!("    └─────────────────────────────────────────┘");
            println!();
            println!("[m0] protection domain booted as a forked PROCESS");
            println!("[m0] isolation is the host MMU's now ( ◕‿◕ )");
            let _ = std::io::stdout().flush();
            0 // idle / clean exit
        })
        .expect("fork m0-hello PD");

    let code = pd.join().expect("join m0-hello");
    assert_eq!(code, 0, "m0-hello PROCESS must boot, print, and exit cleanly");
}

// ===========================================================================
// PD set #2 — the 2-PD notify slice, on the PROCESS backing. PD-A Signals a
// Notification cap; PD-B Waits on it and wakes. Across PROCESSES the notify is
// kernel-mediated (each PD's `Channel::notify`/`wait` is a validated control-
// socket request the kernel services) — the §3 Notified event end-to-end, with
// the PDs in SEPARATE address spaces. This is the same logical slice as the v0
// `boot_two_pd_notify_slice`, only the backing is processes + a real kernel.
// ===========================================================================

#[test]
fn boot_two_pd_notify_slice_on_processes() {
    let kernel = ProcessKernel::new();

    // The firmament wires the slice (the `.system`-file equivalent): ONE
    // notification cap both PDs hold a handle to, and ONE shared region PD-B
    // records its wake into (so the parent/kernel can observe it across the
    // process boundary — shm is how cross-process PDs share a buffer).
    let notif = kernel.create_notification(AuthRequired::Either);
    let witness = kernel
        .create_region(2, AuthRequired::Either)
        .expect("create witness shm region");
    const NOTIFY_BADGE: u64 = 1 << 5; // "channel 5" badge bit, as in the v0 slice

    // ── PD-B: the WAITER process. It maps the witness region (granted), waits on
    //    the notification, then writes its wake sentinel into the SHARED region. ──
    let pd_b = kernel
        .spawn_pd(vec![notif, witness], |client, granted| {
            let notif = granted[0];
            let region_h = granted[1];
            println!("[pd-b] init (process) — mapping witness + arming notify wait");
            // Map the granted shared region (the `memory_region_symbol!` path on
            // the process backing — a validated grant lookup + an mmap).
            let region = match client.map_region(region_h) {
                Ok(r) => r,
                Err(e) => {
                    eprintln!("[pd-b] FAILED to map granted region: {e}");
                    return 2;
                }
            };
            // Block on the notification (the §3 Notified event, kernel-mediated).
            let badge = match client.wait(notif) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("[pd-b] wait failed: {e}");
                    return 3;
                }
            };
            println!("[pd-b] notified — badge {badge:#x} — the wake fired (across processes!)");
            // Record (a) a liveness sentinel and (b) the badge low byte, into the
            // SHARED shm region (visible to the kernel/parent).
            region.with_mut(|buf| {
                buf[0] = 0xB0; // 'B' woke
                buf[1] = (badge & 0xFF) as u8;
            });
            let _ = std::io::stdout().flush();
            0
        })
        .expect("fork PD-B waiter");

    // ── PD-A: the SIGNALLER process. After a beat (so B parks), it signals the
    //    notification cap by handle — the SAME logical `Channel::notify`. ──
    let pd_a = kernel
        .spawn_pd(vec![notif], |client, granted| {
            let notif = granted[0];
            println!("[pd-a] init (process) — signalling the notify cap");
            std::thread::sleep(std::time::Duration::from_millis(30));
            match client.signal(notif, NOTIFY_BADGE) {
                Ok(KernelReply::Ok) => println!("[pd-a] signalled — PD-B should wake"),
                other => {
                    eprintln!("[pd-a] signal failed: {other:?}");
                    return 4;
                }
            }
            let _ = std::io::stdout().flush();
            0
        })
        .expect("fork PD-A signaller");

    // ── The kernel (this parent process) services BOTH PDs' control sockets. ──
    // Each PD makes a few validated requests; we pump each socket until the PD
    // exits (EOF). We service them on two helper threads so PD-B's blocking
    // `wait` and PD-A's `signal` interleave correctly across processes.
    let k_a = kernel.clone();
    let k_b = kernel.clone();
    let mut a_sock = pd_a.kernel_sock.try_clone().expect("clone A sock");
    let mut b_sock = pd_b.kernel_sock.try_clone().expect("clone B sock");
    let serve_a = std::thread::spawn(move || {
        while k_a.serve_one(&mut a_sock).unwrap_or(false) {}
    });
    let serve_b = std::thread::spawn(move || {
        while k_b.serve_one(&mut b_sock).unwrap_or(false) {}
    });

    // Join the PD processes.
    let a_code = wait_pid(pd_a.pid);
    let b_code = wait_pid(pd_b.pid);
    // The kernel sockets see EOF once the children exit; the servers return.
    serve_a.join().unwrap();
    serve_b.join().unwrap();

    assert_eq!(a_code, 0, "PD-A signaller exited cleanly");
    assert_eq!(b_code, 0, "PD-B waiter woke + ran its body cleanly");

    // THE OBSERVABLE: PD-B's wake body ran (sentinel 0xB0) and saw the badge,
    // recorded into the SHARED shm region the kernel reads — proving the notify
    // crossed from PD-A's process to PD-B's process through the kernel, and that
    // the cross-process shm grant works.
    let w = kernel.region_read(witness).expect("read witness region");
    assert_eq!(w[0], 0xB0, "PD-B's notified body must have run (process backing)");
    assert_eq!(
        w[1],
        (NOTIFY_BADGE & 0xFF) as u8,
        "PD-B must have seen the signalled badge bit"
    );
    println!(
        "PROCESS NOTIFY SLICE: PD-A signal → PD-B woke across processes, saw \
         badge {:#04x} — init()+notified() ran on the ProcessKernel ( ˘▾˘ )",
        w[1]
    );
}

// ===========================================================================
// THE ISOLATION TOOTH — what v0 could NOT enforce, now MMU-enforced + table-
// refused. Two halves:
//
//   (A) a PD CANNOT read another PD's PRIVATE memory — the host MMU faults /
//       the read lands in the reader's own unrelated address space. (v0: a raw
//       pointer into a sibling thread's heap is readable in one address space.)
//
//   (B) a PD CANNOT forge a cap by writing raw bytes — a fabricated CapHandle
//       presented to the kernel is refused by the epoch-tagged validity table
//       (the cross-process CNode-unforgeability analogue). Endpoint/Notification
//       IPC over a GENUINE granted handle still works.
// ===========================================================================

/// (A) Cross-PD private-memory read is impossible — the MMU separates address
/// spaces. We prove it CONSTRUCTIVELY: PD-victim writes a secret into a PRIVATE
/// (non-shared) buffer and reports the buffer's address to the kernel via a
/// shared channel region; PD-attacker is handed that raw address and tries to
/// read it. Because PD-attacker is a SEPARATE process, that virtual address in
/// its OWN space does NOT hold the victim's secret — the attacker can never
/// observe the secret. (On v0's one address space, the same raw read WOULD see
/// the secret — that is precisely the gap this closes.)
#[test]
fn pd_cannot_read_another_pds_private_memory() {
    let kernel = ProcessKernel::new();

    // A small shared "mailbox" region the two PDs use to pass the victim's
    // private-buffer address + a result flag (this is the ONLY memory they
    // share; everything else is each PD's private, MMU-separated space).
    //   bytes [0..8)  : victim's private secret-buffer virtual address (LE u64)
    //   byte  [8]     : victim-ready flag (1 = address published)
    //   byte  [9]     : attacker result (0 = did not observe secret, 1 = DID)
    //   byte  [10]    : attacker-done flag
    let mbox = kernel
        .create_region(16, AuthRequired::Either)
        .expect("mailbox region");
    const SECRET: u8 = 0x5A;

    // PD-victim: holds a PRIVATE buffer (a heap box) with the secret, publishes
    // its address into the mailbox, then spins until the attacker is done (so
    // the buffer stays alive at that address for the duration of the attempt).
    let victim = kernel
        .spawn_pd(vec![mbox], |client, granted| {
            let mbox = client.map_region(granted[0]).expect("victim maps mailbox");
            // A PRIVATE secret buffer — NOT a shared region. In v1 this lives in
            // the victim's own address space the attacker process cannot touch.
            let secret_buf: Box<[u8; 64]> = Box::new([SECRET; 64]);
            let addr = secret_buf.as_ptr() as u64;
            // Publish the address + ready flag.
            mbox.with_mut(|b| {
                b[..8].copy_from_slice(&addr.to_le_bytes());
                b[8] = 1;
            });
            // Spin until the attacker signals done (keeping secret_buf alive).
            let mut spins = 0;
            loop {
                let done = mbox.read()[10];
                if done == 1 || spins > 2_000_000 {
                    break;
                }
                spins += 1;
                std::hint::spin_loop();
            }
            // Touch the buffer so the optimizer cannot drop it early.
            std::hint::black_box(&secret_buf);
            0
        })
        .expect("fork victim");

    // PD-attacker: waits for the victim's published address, then ATTEMPTS to
    // read it as a raw pointer in ITS OWN address space. In a separate process
    // that address is either unmapped (→ it cannot read SECRET) or maps to the
    // attacker's own unrelated memory (→ also not SECRET). We guard the read
    // with a SIGSEGV handler so a fault is caught and reported as "did not
    // observe" rather than crashing the test. The attacker records whether it
    // observed SECRET.
    let attacker = kernel
        .spawn_pd(vec![mbox], |client, granted| {
            let mbox = client.map_region(granted[0]).expect("attacker maps mailbox");
            // Wait for the victim to publish its private address.
            let mut spins = 0u64;
            let addr = loop {
                let m = mbox.read();
                if m[8] == 1 {
                    let mut a = [0u8; 8];
                    a.copy_from_slice(&m[..8]);
                    break u64::from_le_bytes(a);
                }
                spins += 1;
                if spins > 5_000_000 {
                    // Victim never published — fail loud.
                    mbox.with_mut(|b| {
                        b[9] = 0;
                        b[10] = 1;
                    });
                    return 7;
                }
                std::hint::spin_loop();
            };

            // THE FORBIDDEN READ: try to read the victim's PRIVATE address from
            // the attacker's own space. Guarded against SIGSEGV: if it faults
            // (the common case — the address is unmapped here), we treat it as
            // "did not observe the secret" (which is correct — no cross-PD read).
            let observed = unsafe { try_read_byte(addr as *const u8) };
            let saw_secret = matches!(observed, Some(b) if b == SECRET);

            mbox.with_mut(|b| {
                b[9] = if saw_secret { 1 } else { 0 };
                b[10] = 1; // done — release the victim
            });
            0
        })
        .expect("fork attacker");

    // The kernel services both PDs' sockets (they each map one region).
    let k1 = kernel.clone();
    let k2 = kernel.clone();
    let mut vs = victim.kernel_sock.try_clone().unwrap();
    let mut as_ = attacker.kernel_sock.try_clone().unwrap();
    let sv = std::thread::spawn(move || while k1.serve_one(&mut vs).unwrap_or(false) {});
    let sa = std::thread::spawn(move || while k2.serve_one(&mut as_).unwrap_or(false) {});

    let v_code = wait_pid(victim.pid);
    let a_code = wait_pid(attacker.pid);
    sv.join().unwrap();
    sa.join().unwrap();

    assert_eq!(v_code, 0, "victim PD ran cleanly");
    assert_eq!(a_code, 0, "attacker PD ran cleanly (its forbidden read was contained)");

    // THE TOOTH: the attacker did NOT observe the victim's secret. Cross-PD
    // private-memory read is impossible under the process backing's MMU
    // separation — the v0 gap is closed.
    let result = kernel.region_read(mbox).expect("read mailbox");
    assert_eq!(result[10], 1, "attacker must have completed its attempt");
    assert_eq!(
        result[9], 0,
        "ISOLATION TOOTH: a PD must NOT be able to read another PD's private \
         memory by raw pointer — the host MMU separates the address spaces \
         (this is exactly the v0 gap, now closed)"
    );
    println!(
        "ISOLATION TOOTH (memory): attacker PROCESS could NOT read the victim's \
         private secret at {:#x} — MMU-enforced separation holds ( ⌐■_■ )",
        u64::from_le_bytes(result[..8].try_into().unwrap())
    );
}

/// (B) Cap forgery by writing raw bytes is impossible — the kernel's
/// epoch-tagged validity table refuses a fabricated handle, while a GENUINE
/// granted handle still works (IPC is unbroken). We run ONE PD that:
///   - presents a hand-fabricated CapHandle (raw bytes it invented) → REFUSED;
///   - presents a stale handle (right slot, wrong epoch) → REFUSED;
///   - presents its GENUINE granted notification handle → ACCEPTED (signal Ok).
#[test]
fn pd_cannot_forge_a_cap_by_writing_raw_bytes() {
    let kernel = ProcessKernel::new();
    let genuine = kernel.create_notification(AuthRequired::Either);

    let pd = kernel
        .spawn_pd(vec![genuine], |client, granted| {
            let genuine = granted[0];

            // 1) A cap forged from RAW BYTES — a slot the PD never received. The
            //    PD can fabricate any (slot, epoch) it likes; the kernel's table
            //    is the sole arbiter and refuses it.
            let forged = CapHandle { slot: 0xFFFF_FFFF, epoch: 0 };
            match client.validate(forged) {
                Ok(KernelReply::Forged) => println!("[pd] forged handle REFUSED (good)"),
                other => {
                    eprintln!("[pd] forged handle NOT refused: {other:?}");
                    return 10;
                }
            }
            // Also try to SIGNAL with the forged handle — must be refused, so a
            // forged cap cannot even drive IPC.
            match client.signal(forged, 0x1) {
                Ok(KernelReply::Forged) => println!("[pd] forged signal REFUSED (good)"),
                other => {
                    eprintln!("[pd] forged signal NOT refused: {other:?}");
                    return 11;
                }
            }

            // 2) A STALE handle: the right slot but a fabricated wrong epoch.
            //    Refused as a stale/forged handle (use-after-reuse guard).
            let stale = CapHandle { slot: genuine.slot, epoch: genuine.epoch.wrapping_add(99) };
            match client.validate(stale) {
                Ok(KernelReply::Forged) => println!("[pd] stale-epoch handle REFUSED (good)"),
                other => {
                    eprintln!("[pd] stale handle NOT refused: {other:?}");
                    return 12;
                }
            }

            // 3) The GENUINE granted handle still works — IPC is unbroken; only
            //    forgery is refused. Signalling the real notification succeeds.
            match client.signal(genuine, 0x2) {
                Ok(KernelReply::Ok) => println!("[pd] genuine signal ACCEPTED (IPC works)"),
                other => {
                    eprintln!("[pd] genuine signal failed: {other:?}");
                    return 13;
                }
            }
            let _ = std::io::stdout().flush();
            0
        })
        .expect("fork forgery-probe PD");

    // Service the PD's socket until it exits.
    let k = kernel.clone();
    let mut sock = pd.kernel_sock.try_clone().unwrap();
    let server = std::thread::spawn(move || while k.serve_one(&mut sock).unwrap_or(false) {});
    let code = wait_pid(pd.pid);
    server.join().unwrap();

    assert_eq!(
        code, 0,
        "ISOLATION TOOTH: forged + stale cap-handles must be REFUSED by the \
         validity table, and the genuine granted handle must still drive IPC \
         (a non-zero exit means one of these failed)"
    );
    // And the kernel-side accumulator saw the GENUINE signal (the IPC that did
    // go through) — confirming "forgery refused, real IPC unbroken".
    let badge = kernel.poll_notification(genuine).expect("poll genuine");
    assert_eq!(
        badge, 0x2,
        "the genuine signal (0x2) must have reached the notification — IPC over \
         a real granted cap works while raw-bytes forgery is refused"
    );
    println!(
        "ISOLATION TOOTH (forgery): raw-bytes + stale cap-handles REFUSED by the \
         kernel validity table; the genuine granted handle drove a real signal \
         (badge {badge:#x}) — cross-process CNode-unforgeability holds ( ✜‿‿✜ )"
    );
}

// ─────────────────────────── test helpers ──────────────────────────────────

/// Wait for a child pid and return its exit code (0 = clean). Mirrors
/// `PdProcess::join`'s status decode without consuming the `PdProcess` (so we
/// can keep its `kernel_sock` for the serving thread).
fn wait_pid(pid: libc::pid_t) -> i32 {
    let mut status: libc::c_int = 0;
    let rc = unsafe { libc::waitpid(pid, &mut status, 0) };
    if rc < 0 {
        return -1;
    }
    if status & 0x7f == 0 {
        (status >> 8) & 0xff
    } else {
        -(status & 0x7f)
    }
}

/// Try to read one byte at `ptr`, returning `None` if the read faults (SIGSEGV/
/// SIGBUS). Installs a thread-local-ish `sigsetjmp` landing pad around the read.
///
/// # Safety
/// `ptr` is dereferenced (in a fork-isolated grandchild, so a fault kills only
/// the grandchild). `ptr` is attacker-controlled — that is the whole point: we
/// PROVE the read cannot reach another PD's memory.
///
/// We `fork` a grandchild that performs the (possibly faulting) read and writes
/// the byte it observed into a pipe; the attacker reads the pipe. If the read
/// faults (the common case — the victim's address is unmapped in this process's
/// space), the grandchild dies by SIGSEGV and writes nothing → we return `None`
/// ("did not observe"). This needs no `sigsetjmp` (which the Rust `libc` crate
/// does not export, being a C macro) and is MORE faithful: a forbidden read
/// literally faults the reader. The grandchild is in the SAME address space as
/// the attacker (a fork of it), so this is a fair test — it reads exactly what
/// the attacker process could read; it just cannot crash the bookkeeping.
unsafe fn try_read_byte(ptr: *const u8) -> Option<u8> {
    // A pipe: [0] read end (attacker), [1] write end (grandchild).
    let mut fds = [0 as libc::c_int; 2];
    if libc::pipe(fds.as_mut_ptr()) != 0 {
        return None;
    }
    let (rd, wr) = (fds[0], fds[1]);

    let pid = libc::fork();
    if pid < 0 {
        libc::close(rd);
        libc::close(wr);
        return None;
    }
    if pid == 0 {
        // ── grandchild: do the forbidden read; write the byte; _exit ──
        libc::close(rd);
        // A volatile read so the compiler cannot elide it. If `ptr` is unmapped
        // in this address space, THIS faults and the grandchild dies here.
        let v = std::ptr::read_volatile(ptr);
        let buf = [v];
        let _ = libc::write(wr, buf.as_ptr() as *const libc::c_void, 1);
        libc::close(wr);
        libc::_exit(0);
    }

    // ── attacker (parent of the grandchild): read the result ──
    libc::close(wr);
    let mut byte = [0u8; 1];
    let n = libc::read(rd, byte.as_mut_ptr() as *mut libc::c_void, 1);
    libc::close(rd);
    let mut status: libc::c_int = 0;
    libc::waitpid(pid, &mut status, 0);
    // The grandchild wrote a byte ONLY if the read succeeded (no fault).
    if n == 1 {
        Some(byte[0])
    } else {
        None
    }
}
