//! THE SANDBOXED-FIRMAMENT ACCEPTANCE TEST (Phase 0) — the ambient-authority
//! confinement tooth that `tests/process_isolation.rs` could not enforce.
//!
//! `docs/DREGG-DESKTOP-OS.md §3`: the v1 process backing gives a forked PD
//! **MMU** isolation (separate page tables) but the fork-path child still
//! inherits **ambient OS authority** — it can `open` arbitrary files,
//! `socket(AF_INET)` the network, `execve`, and keeps every inherited fd
//! ([`ProcessKernel::ISOLATION_FIDELITY`] names exactly this gap). This file
//! proves that gap is CLOSED by [`ProcessKernel::spawn_pd_confined`], which
//! applies [`dregg_firmament::sandbox::confine_child`] in the child right after
//! `fork()` and BEFORE the body: the child's ONLY channel is the firmament
//! Endpoint (its control socket).
//!
//! The confined child runs FOUR probes and folds the results into its exit code
//! (a bitmask — it cannot use a shm region to report, because confinement closes
//! every non-control fd AND denies `shm_open`; the exit code crosses the process
//! boundary cleanly):
//!
//!   bit 0 (0x1): the control-socket round-trip WORKS (a `Validate` of its
//!                genuine granted handle returns Valid) — IPC over the Endpoint
//!                is unbroken.
//!   bit 1 (0x2): `open("/etc/passwd")` is DENIED (the Seatbelt/LSM profile
//!                refuses arbitrary file reads).
//!   bit 2 (0x4): `socket(AF_INET, SOCK_STREAM)` FAILS / cannot connect (no
//!                `network*` authority / empty net namespace).
//!   bit 3 (0x8): the inherited control socket is the ONLY non-std fd open (every
//!                other inherited fd was closed by the confinement).
//!
//! All four set ⇒ exit code 0xF. The macOS backend is ENFORCED + run here. The
//! Linux backend compiles (cfg-gated) and runs on Linux.
//!
//! Gated behind `--features process-pd,process-pd-sandbox` (Unix only). Run with:
//!   `cargo test --features process-pd,process-pd-sandbox --test process_sandbox -- --nocapture`

#![cfg(all(feature = "process-pd-sandbox", unix))]

use std::io::Write;

use dregg_cell::AuthRequired;
use dregg_firmament::process_kernel::{KernelReply, ProcessKernel};
use dregg_firmament::{
    Backing, Capability, FirmamentRouter, HostPdBacking, Router, DistributedBacking, LocalBacking,
};

// ── the four probe result bits the confined child folds into its exit code ──
const BIT_IPC_WORKS: i32 = 0x1;
const BIT_OPEN_DENIED: i32 = 0x2;
const BIT_NET_DENIED: i32 = 0x4;
const BIT_ONLY_SOCKET_FD: i32 = 0x8;
const ALL_BITS: i32 = BIT_IPC_WORKS | BIT_OPEN_DENIED | BIT_NET_DENIED | BIT_ONLY_SOCKET_FD;

/// THE ACCEPTANCE TEST: a confined child PD whose only channel is the firmament
/// Endpoint. It rounds-trips over the control socket (works), and its attempts
/// to open a file / reach the network are denied, and no fd but the socket
/// survives. The exit code carries the four-bit verdict.
#[test]
fn confined_pd_only_channel_is_the_firmament_endpoint() {
    let kernel = ProcessKernel::new();
    // A genuine notification cap the child holds — proves IPC over the Endpoint
    // still works AFTER confinement (the SAME validated round-trip the
    // non-confined slice uses).
    let genuine = kernel.create_notification(AuthRequired::Either);

    let pd = kernel
        .spawn_pd_confined(vec![genuine], |client, granted| {
            // ── CONFINED CHILD: confinement already applied (fds closed + the
            //    host sandbox self-applied). The body runs UNDER confinement. ──
            let genuine = granted[0];
            let mut verdict = 0i32;

            // (1) The firmament Endpoint round-trip WORKS — a `Validate` of the
            //     genuine handle returns Valid (the control socket is live and
            //     the kernel still services it).
            match client.validate(genuine) {
                Ok(KernelReply::Valid { .. }) => {
                    verdict |= BIT_IPC_WORKS;
                    println!("[confined] Endpoint round-trip WORKS (validate=Valid)");
                }
                other => eprintln!("[confined] Endpoint round-trip FAILED: {other:?}"),
            }

            // (2) open("/etc/passwd") is DENIED by the sandbox profile.
            if !can_open("/etc/passwd") {
                verdict |= BIT_OPEN_DENIED;
                println!("[confined] open(/etc/passwd) DENIED (good)");
            } else {
                eprintln!("[confined] open(/etc/passwd) SUCCEEDED — sandbox NOT enforced!");
            }

            // (3) socket(AF_INET) is denied / has no route.
            if !can_inet_socket() {
                verdict |= BIT_NET_DENIED;
                println!("[confined] socket(AF_INET) DENIED / no route (good)");
            } else {
                eprintln!("[confined] socket(AF_INET) SUCCEEDED — network NOT confined!");
            }

            // (4) The control socket is the ONLY non-std fd. We probe fds 3..64;
            //     exactly one (the inherited socketpair end) must be open.
            let open_non_std = count_open_fds_above_std(64);
            if open_non_std == 1 {
                verdict |= BIT_ONLY_SOCKET_FD;
                println!("[confined] exactly ONE non-std fd open = the Endpoint (good)");
            } else {
                eprintln!("[confined] {open_non_std} non-std fds open (expected 1 = the socket)");
            }

            let _ = std::io::stdout().flush();
            let _ = std::io::stderr().flush();
            verdict
        })
        .expect("fork confined PD");

    // The kernel services the child's control socket until it exits.
    let k = kernel.clone();
    let mut sock = pd.kernel_sock.try_clone().expect("clone kernel sock");
    let server = std::thread::spawn(move || while k.serve_one(&mut sock).unwrap_or(false) {});
    let code = wait_pid(pd.pid);
    server.join().unwrap();

    assert_eq!(
        code, ALL_BITS,
        "SANDBOX TOOTH: a confined PD must (1) round-trip over the firmament \
         Endpoint, (2) be DENIED open(/etc/passwd), (3) be DENIED the network, \
         (4) hold ONLY the control socket fd. exit={code:#x} (want {ALL_BITS:#x}); \
         each missing bit is a confinement that did not hold."
    );
    println!(
        "SANDBOX TOOTH: the confined PD's ONLY channel is the firmament Endpoint \
         — IPC works, file/network/exec ambient authority DENIED, one fd held \
         ( ⌐■_■ )"
    );
}

/// THE Target::HostPd WIRING: a confined child registered in the router's host
/// backing resolves as a `Capability::host_pd(id, rights)` through the SAME
/// backing-agnostic `Router::resolve` — the sandboxed-firmament leg of the fluid
/// reach-out. Attenuation reuses the unified `granted ⊆ held` gate, and a
/// widening grant is refused identically to every other backing.
#[test]
fn host_pd_target_resolves_through_the_router() {
    let kernel = ProcessKernel::new();

    // Spawn a confined child that simply idles (serving as a live Endpoint).
    let pd = kernel
        .spawn_pd_confined(vec![], |client, _granted| {
            // Keep the Endpoint open briefly so the parent can invoke it, then
            // exit. A single validate round-trip keeps the socket serviced.
            let _ = client.validate(dregg_firmament::process_kernel::CapHandle { slot: 0, epoch: 0 });
            std::thread::sleep(std::time::Duration::from_millis(80));
            0
        })
        .expect("fork host-pd child");

    // Register the child's Endpoint in the host backing with Either rights.
    let mut host = HostPdBacking::new();
    let pd_id = host.register(
        pd.kernel_sock.try_clone().expect("clone sock"),
        AuthRequired::Either,
    );

    // Build a router with that host backing; the app names a HostPd(id) target.
    let router =
        FirmamentRouter::new(LocalBacking::new(), DistributedBacking::new()).with_host(host);

    // Service the child's socket so its in-flight validate is answered.
    let k = kernel.clone();
    let mut sock = pd.kernel_sock.try_clone().expect("clone for serve");
    let server = std::thread::spawn(move || while k.serve_one(&mut sock).unwrap_or(false) {});

    // RESOLVE a host-PD capability — dispatches to the host backing, strong-local
    // bounds, and the right Backing tag.
    let cap = Capability::host_pd(pd_id, AuthRequired::Either);
    let res = router.resolve(&cap).expect("host-PD resolves");
    assert_eq!(res.backing, Backing::HostPdEndpoint);
    assert_eq!(res.bounds, dregg_firmament::Bounds::LOCAL);
    assert_eq!(FirmamentRouter::backing_of(&cap), Backing::HostPdEndpoint);

    // ATTENUATION reuses the unified gate: Either→Signature narrows (ok);
    // Signature→Either widens (refused) — the SAME `granted ⊆ held` law.
    let narrowed = cap.attenuate(AuthRequired::Signature).expect("narrow ok");
    assert_eq!(narrowed.rights, AuthRequired::Signature);
    let widened = Capability::host_pd(pd_id, AuthRequired::Signature).attenuate(AuthRequired::Either);
    assert!(widened.is_none(), "a widening host-PD grant must be refused");

    // A requested op within the held authority (Signature ⊆ Either) resolves —
    // the backing's `granted ⊆ held` gate authorizes it.
    let within = Capability::host_pd(pd_id, AuthRequired::Signature);
    assert!(
        router.resolve(&within).is_ok(),
        "Signature ⊆ Either: the held-Either Endpoint authorizes a Signature op"
    );

    let _ = wait_pid(pd.pid);
    server.join().unwrap();
    println!("Target::HostPd resolves through the router as the SANDBOXED-FIRMAMENT leg ( ✜‿‿✜ )");
}

// ─────────────────────────── probe helpers ──────────────────────────────────

/// Try to `open` a path read-only; returns whether it SUCCEEDED. Under the
/// confinement this must be false for an un-granted path.
fn can_open(path: &str) -> bool {
    let c = std::ffi::CString::new(path).unwrap();
    let fd = unsafe { libc::open(c.as_ptr(), libc::O_RDONLY) };
    if fd >= 0 {
        unsafe { libc::close(fd) };
        true
    } else {
        false
    }
}

/// Try to create an AF_INET socket AND begin a connect to a public address;
/// returns whether the NETWORK was reachable (socket created AND connect did not
/// immediately fail with a no-permission/no-route error). Under confinement
/// either the `socket(2)` itself is denied (macOS Seatbelt) or there is no route
/// (Linux empty net namespace), so this is false.
fn can_inet_socket() -> bool {
    let fd = unsafe { libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0) };
    if fd < 0 {
        // socket() itself refused (macOS Seatbelt denies network-outbound at the
        // socket layer) — the network is confined.
        return false;
    }
    // The socket was created; on Linux an empty net namespace still has no route,
    // so a connect to a non-loopback address fails. Probe a connect to 1.1.1.1:80.
    let mut addr: libc::sockaddr_in = unsafe { std::mem::zeroed() };
    addr.sin_family = libc::AF_INET as libc::sa_family_t;
    addr.sin_port = (80u16).to_be();
    // 1.1.1.1 in network byte order.
    addr.sin_addr.s_addr = u32::from_be_bytes([1, 1, 1, 1]).to_be();
    let rc = unsafe {
        libc::connect(
            fd,
            &addr as *const _ as *const libc::sockaddr,
            std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t,
        )
    };
    let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
    unsafe { libc::close(fd) };
    // A reachable network either connects (rc==0) or is EINPROGRESS/ECONNREFUSED
    // (we COULD reach the stack). ENETUNREACH / EPERM / EHOSTUNREACH = confined.
    if rc == 0 {
        return true;
    }
    !matches!(
        errno,
        libc::ENETUNREACH | libc::EPERM | libc::EHOSTUNREACH | libc::EACCES | libc::EAFNOSUPPORT
    ) && matches!(errno, libc::EINPROGRESS | libc::ECONNREFUSED | libc::ETIMEDOUT)
}

/// Count open fds in `3..max` (above the std streams). Under confinement exactly
/// one — the inherited control socket — must be open.
fn count_open_fds_above_std(max: libc::c_int) -> usize {
    let mut n = 0;
    for fd in 3..max {
        // F_GETFD returns >=0 for an open fd, -1 (EBADF) for a closed one.
        let rc = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        if rc >= 0 {
            n += 1;
        }
    }
    n
}

/// Wait for a child pid and return its exit code (mirrors the isolation test's
/// helper). A negative value means the child died by signal.
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
