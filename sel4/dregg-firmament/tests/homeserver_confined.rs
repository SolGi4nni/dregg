//! THE HEAVY-BODY CONFINED-GRAIN ACCEPTANCE TEST — firmament hosts the confined
//! homeserver grain (`docs/deos/GRAIN-HOMESERVER.md`, "Firmament confined-spawn
//! architecture").
//!
//! `tests/process_sandbox.rs` proves the LIGHT jail (a Rust-closure PD whose only
//! channel is the firmament Endpoint, all ambient authority denied). THIS file
//! proves the HEAVY tier: firmament's own `fork` + `sandbox_init` + `execve` hosts
//! a REAL prebuilt binary — the rocksdb+tokio Matrix homeserver — under the SAME
//! deny-default Seatbelt profile that `deos-homeserver/sandbox/homeserver.sb`
//! de-risked, and the grain BOOTS + SERVES `GET /_matrix/client/versions → 200`
//! confined, through firmament (not `sandbox-exec`).
//!
//! Three poles, each a distinct guarantee:
//!
//!   POSITIVE (`confined_homeserver_serves_200_through_firmament`, `#[ignore]`):
//!     the whole thing — [`ProcessKernel::spawn_pd_confined_exec`] execs the
//!     prebuilt `deos-homeserver` under a heavy-body [`Confinement`]
//!     {write=db_dir, listen=127.0.0.1:*, mach=the 10, system-reads, exec-image},
//!     reads its `READY <url>`, and curls `→ 200`. Ignored by default (it needs
//!     the prebuilt heavy bin — a ~20-min continuwuity build); run with
//!     `--ignored` once the bin exists (path via `$DEOS_HOMESERVER_BIN` or the
//!     default `deos-homeserver/target/debug/deos-homeserver`).
//!
//!   NEGATIVE × 3 (the "named door" proofs, runnable in the normal suite): a
//!     confined body's write to a SIBLING (ungranted) path is DENIED; a bind to
//!     an UNLISTED port is DENIED; a lookup of an UNLISTED mach service is DENIED
//!     — each a distinct refusal, proving the heavy doors are NAMED, not broad.
//!
//! Gated behind `--features process-pd,process-pd-sandbox` (macOS-enforced). Run:
//!   `cargo test --features process-pd-sandbox --test homeserver_confined -- --nocapture`
//!   `… --test homeserver_confined -- --ignored --nocapture`   (the heavy positive)

#![cfg(all(feature = "process-pd-sandbox", target_os = "macos"))]

use std::io::{BufRead, BufReader};
use std::time::Duration;

use dregg_firmament::process_kernel::ProcessKernel;
use dregg_firmament::sandbox::Confinement;

// ─────────────────────────── the POSITIVE pole ──────────────────────────────

/// THE HEAVY-BODY ACCEPTANCE: firmament execs the prebuilt `deos-homeserver`
/// under a deny-default heavy-body confinement, and the grain serves the CS API
/// 200 — confined, through firmament's fork+sandbox_init+execve.
#[test]
#[ignore = "needs the prebuilt heavy deos-homeserver bin; run with --ignored"]
fn confined_homeserver_serves_200_through_firmament() {
    let bin = homeserver_bin_path();
    assert!(
        std::path::Path::new(&bin).exists(),
        "prebuilt homeserver bin not found at {bin}\n\
         build it: (cd deos-homeserver && ROCKSDB_LIB_DIR=\"$(brew --prefix rocksdb)/lib\" \
         ROCKSDB_INCLUDE_DIR=\"$(brew --prefix rocksdb)/include\" cargo build --bin deos-homeserver)\n\
         or pass $DEOS_HOMESERVER_BIN"
    );

    // A fresh, CANONICAL run root (the one write subpath / the db-dir door). The
    // grain's std::env::temp_dir() honours $TMPDIR, so pinning TMPDIR here puts
    // the grain's RocksDB dir under a dir we granted write on.
    let run_root = fresh_canonical_dir("firmament-hs-confined");

    // The brew prefix (rocksdb + its compression dylibs live under it).
    let brew_prefix =
        std::env::var("HOMEBREW_PREFIX").unwrap_or_else(|_| "/opt/homebrew".to_string());

    // THE HEAVY-BODY CONFINEMENT — the SAME allow-set homeserver.sb de-risked.
    let confinement = Confinement::default()
        .with_system_reads() // dyld/libSystem/framework reads + process machinery
        .with_homebrew_prefix(&brew_prefix)
        .with_write_path(&run_root) // the db-dir door (read+write on the run root)
        .with_listen("127.0.0.1:*") // loopback bind+inbound (the grain self-selects a port)
        .with_net_out("127.0.0.1:*") // the grain's loopback readiness self-probe
        .with_homeserver_mach_defaults() // the NAMED 10 mach services
        .with_exec_image(&bin); // the grain-image execve door

    // argv: the grain reads server_name from argv[1]. env: inherit the parent's
    // (so PATH/HOME/dyld env survive) + pin TMPDIR to the run root + the rocksdb
    // link env (build-time; harmless at runtime) + a bounded readiness timeout.
    let argv = vec![bin.clone(), "localhost".to_string()];
    let mut env: Vec<(String, String)> = std::env::vars().collect();
    upsert(&mut env, "TMPDIR", &run_root);
    upsert(&mut env, "DEOS_HS_READY_TIMEOUT_SECS", "60");
    upsert(
        &mut env,
        "ROCKSDB_LIB_DIR",
        &format!("{brew_prefix}/opt/rocksdb/lib"),
    );
    upsert(
        &mut env,
        "ROCKSDB_INCLUDE_DIR",
        &format!("{brew_prefix}/opt/rocksdb/include"),
    );

    let kernel = ProcessKernel::new();
    let grain = kernel
        .spawn_pd_confined_exec(confinement, &argv, &env)
        .expect("firmament confined-exec of the grain image");

    // Read the grain's stdout for its single `READY <base_url>` line, on a reader
    // thread with an overall deadline (the grain then stays up).
    let (tx, rx) = std::sync::mpsc::channel::<String>();
    let stdout = grain.stdout.try_clone().expect("clone grain stdout");
    let reader = std::thread::spawn(move || {
        let mut lines = BufReader::new(stdout).lines();
        while let Some(Ok(line)) = lines.next() {
            eprintln!("[grain] {line}");
            if let Some(url) = line.strip_prefix("READY ") {
                let _ = tx.send(url.trim().to_string());
                break;
            }
        }
    });

    let base_url = match rx.recv_timeout(Duration::from_secs(75)) {
        Ok(u) => u,
        Err(_) => {
            grain.terminate();
            let _ = grain.reap();
            let _ = reader.join();
            panic!("the confined grain never printed READY within 75s");
        }
    };
    eprintln!("[test] grain READY at {base_url} (confined, through firmament)");

    // CURL the CS API from the (unconfined) parent — it connects to the grain's
    // loopback listener (network-inbound the confinement granted).
    let code = http_status(&format!("{base_url}/_matrix/client/versions"));
    // Tear the grain down before asserting so a failure never leaks a server.
    grain.terminate();
    let _ = grain.reap();
    let _ = reader.join();
    let _ = std::fs::remove_dir_all(&run_root);

    assert_eq!(
        code, "200",
        "HEAVY-BODY TOOTH: a firmament-confined deos-homeserver grain must serve \
         GET /_matrix/client/versions → 200 (got {code}). The grain booted its \
         rocksdb+tokio stack + bound loopback under the deny-default Seatbelt \
         profile firmament emitted + self-applied + execve'd through."
    );
    println!(
        "HEAVY-BODY TOOTH: the confined homeserver grain serves 200 — booted by \
         firmament's OWN fork+sandbox_init+execve, no sandbox-exec ( ⌐■_■ )"
    );
}

// ─────────────────────────── the NEGATIVE poles ─────────────────────────────

// The confined closure body folds two probes into its exit code: bit 0 = the
// GRANTED op succeeded, bit 1 = the UNGRANTED op was DENIED. Exit 0b11 = the door
// is NAMED (grant works, everything else refused). Any other code = a door leak.
const GRANT_WORKS: i32 = 0b01;
const OTHER_DENIED: i32 = 0b10;
const NAMED_DOOR: i32 = GRANT_WORKS | OTHER_DENIED;

/// NEGATIVE 1 — a write to a SIBLING (ungranted) path is DENIED; the write to the
/// granted subpath succeeds. The write door is NAMED to exactly the db subpath.
#[test]
fn write_to_a_sibling_path_is_denied() {
    let root = fresh_canonical_dir("firmament-hs-write-neg");
    let granted = format!("{root}/granted");
    let sibling = format!("{root}/sibling");
    std::fs::create_dir_all(&granted).unwrap();
    std::fs::create_dir_all(&sibling).unwrap();

    let confinement = Confinement::default()
        .with_system_reads()
        .with_write_path(&granted); // ONLY the granted subpath is writable.

    let granted_c = granted.clone();
    let sibling_c = sibling.clone();
    let kernel = ProcessKernel::new();
    let pd = kernel
        .spawn_pd_confined_with(vec![], confinement, move |_client, _granted| {
            let mut verdict = 0;
            // (a) write INSIDE the granted subpath → must SUCCEED.
            if std::fs::write(format!("{granted_c}/ok.txt"), b"hi").is_ok() {
                verdict |= GRANT_WORKS;
            }
            // (b) write to a SIBLING (ungranted) subpath → must be DENIED.
            if std::fs::write(format!("{sibling_c}/nope.txt"), b"hi").is_err() {
                verdict |= OTHER_DENIED;
            }
            verdict
        })
        .expect("spawn confined write-probe");

    let code = drive_to_exit(&kernel, pd);
    let _ = std::fs::remove_dir_all(&root);
    assert_eq!(
        code, NAMED_DOOR,
        "WRITE DOOR: the granted subpath must be writable (bit0) AND a sibling \
         path must be DENIED (bit1). exit={code:#b} (want {NAMED_DOOR:#b})."
    );
    println!("WRITE DOOR is NAMED: granted subpath writable, sibling DENIED (•̀ᴗ•́)و");
}

/// NEGATIVE 2 — a bind to an UNLISTED loopback port is DENIED; the bind to the
/// granted port succeeds. The listen door is NAMED to exactly one port.
#[test]
fn a_bind_to_an_unlisted_port_is_denied() {
    // Two DISTINCT free loopback ports: A is granted, B is not. Hold both probe
    // listeners simultaneously so the OS hands back two different ports.
    let (port_a, port_b) = two_free_loopback_ports();

    let confinement = Confinement::default()
        .with_system_reads()
        .with_listen(format!("127.0.0.1:{port_a}")); // ONLY port A may bind.

    let kernel = ProcessKernel::new();
    let pd = kernel
        .spawn_pd_confined_with(vec![], confinement, move |_client, _granted| {
            use std::net::{Ipv4Addr, TcpListener};
            let mut verdict = 0;
            // (a) bind the GRANTED port → must SUCCEED.
            if TcpListener::bind((Ipv4Addr::LOCALHOST, port_a)).is_ok() {
                verdict |= GRANT_WORKS;
            }
            // (b) bind an UNLISTED port → must be DENIED by the sandbox.
            if TcpListener::bind((Ipv4Addr::LOCALHOST, port_b)).is_err() {
                verdict |= OTHER_DENIED;
            }
            verdict
        })
        .expect("spawn confined bind-probe");

    let code = drive_to_exit(&kernel, pd);
    assert_eq!(
        code, NAMED_DOOR,
        "LISTEN DOOR: the granted port {port_a} must bind (bit0) AND an unlisted \
         port {port_b} must be DENIED (bit1). exit={code:#b} (want {NAMED_DOOR:#b})."
    );
    println!("LISTEN DOOR is NAMED: granted port binds, unlisted port DENIED (◕‿◕)");
}

/// NEGATIVE 3 — a lookup of an UNLISTED mach service is DENIED; the lookup of the
/// granted service is not refused. The mach allow-list is NAMED, never a blanket.
#[test]
fn an_unlisted_mach_service_is_denied() {
    // Grant exactly ONE mach service; probe it + an UNLISTED one.
    let granted_svc = "com.apple.system.notification_center";
    let unlisted_svc = "com.apple.SecurityServer"; // a real service, NOT granted here.

    let confinement = Confinement::default()
        .with_system_reads()
        .with_mach_service(granted_svc);

    let kernel = ProcessKernel::new();
    let pd = kernel
        .spawn_pd_confined_with(vec![], confinement, move |_client, _granted| {
            // Look up each service through launchd's bootstrap. A sandbox-denied
            // lookup returns a NON-success kern_return (never SIGKILL under a
            // plain (deny default)), so the granted vs unlisted outcomes differ.
            let granted_rc = mach_look_up(granted_svc);
            let unlisted_rc = mach_look_up(unlisted_svc);
            eprintln!("[mach-probe] granted rc={granted_rc} unlisted rc={unlisted_rc}");
            let mut verdict = 0;
            // (a) the GRANTED lookup is NOT the sandbox refusal (it resolves).
            if granted_rc == 0 {
                verdict |= GRANT_WORKS;
            }
            // (b) the UNLISTED lookup is DENIED (non-zero) AND differs from the
            //     granted outcome — the door is named, not blanket.
            if unlisted_rc != 0 && unlisted_rc != granted_rc {
                verdict |= OTHER_DENIED;
            }
            verdict
        })
        .expect("spawn confined mach-probe");

    let code = drive_to_exit(&kernel, pd);
    assert_eq!(
        code, NAMED_DOOR,
        "MACH DOOR: the granted service must resolve (bit0) AND an unlisted \
         service must be DENIED with a distinct refusal (bit1). exit={code:#b} \
         (want {NAMED_DOOR:#b}). A blanket (allow mach-lookup) would let the \
         unlisted lookup through — this proves the allow-list is NAMED."
    );
    println!("MACH DOOR is NAMED: granted service resolves, unlisted service DENIED ( ✜‿‿✜ )");
}

// ─────────────────────────────── helpers ────────────────────────────────────

/// Resolve the prebuilt homeserver bin: `$DEOS_HOMESERVER_BIN` else the default
/// `deos-homeserver/target/debug/deos-homeserver` (relative to this crate).
fn homeserver_bin_path() -> String {
    if let Ok(p) = std::env::var("DEOS_HOMESERVER_BIN") {
        return p;
    }
    let manifest = env!("CARGO_MANIFEST_DIR"); // …/sel4/dregg-firmament
    let default = format!("{manifest}/../../deos-homeserver/target/debug/deos-homeserver");
    std::fs::canonicalize(&default)
        .map(|p| p.to_string_lossy().into_owned())
        .unwrap_or(default)
}

/// A fresh, CANONICAL temp dir (symlinks resolved: /var → /private/var on macOS,
/// so the sandbox rule matches the path the kernel checks against).
fn fresh_canonical_dir(tag: &str) -> String {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let base = std::env::temp_dir().join(format!("{tag}-{}-{}", std::process::id(), nanos));
    std::fs::create_dir_all(&base).expect("create run root");
    std::fs::canonicalize(&base)
        .expect("canonicalize run root")
        .to_string_lossy()
        .into_owned()
}

/// Insert-or-replace an env var in the pair list.
fn upsert(env: &mut Vec<(String, String)>, key: &str, val: &str) {
    env.retain(|(k, _)| k != key);
    env.push((key.to_string(), val.to_string()));
}

/// Two DISTINCT free loopback ports (hold both listeners while reading, so the OS
/// never hands back the same port twice), then drop both.
fn two_free_loopback_ports() -> (u16, u16) {
    use std::net::{Ipv4Addr, TcpListener};
    let a = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).expect("probe port a");
    let b = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).expect("probe port b");
    let (pa, pb) = (
        a.local_addr().unwrap().port(),
        b.local_addr().unwrap().port(),
    );
    assert_ne!(pa, pb);
    (pa, pb)
}

/// `curl` the URL and return the HTTP status code string (curl runs UNCONFINED
/// in the parent — the de-risk harness uses the same shape).
fn http_status(url: &str) -> String {
    let out = std::process::Command::new("curl")
        .args(["-s", "-o", "/dev/null", "-w", "%{http_code}", url])
        .output()
        .expect("run curl");
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

/// Service a confined closure PD's control socket to exit, returning its exit
/// code (mirrors `tests/process_sandbox.rs`'s drive+wait).
fn drive_to_exit(kernel: &ProcessKernel, pd: dregg_firmament::process_kernel::PdProcess) -> i32 {
    let k = kernel.clone();
    let mut sock = pd.kernel_sock.try_clone().expect("clone kernel sock");
    let server = std::thread::spawn(move || while k.serve_one(&mut sock).unwrap_or(false) {});
    let code = wait_pid(pd.pid);
    server.join().unwrap();
    code
}

/// Wait for `pid`, returning its exit code (negative = died by signal).
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

// launchd bootstrap FFI (libSystem) — look up a service by name and return the
// kern_return. Used only by the mach-door negative to observe the sandbox
// refusal of an UNLISTED service. `bootstrap_port` is the process's inherited
// bootstrap port (a mach port, unaffected by fd-closing confinement).
extern "C" {
    static bootstrap_port: libc::mach_port_t;
    fn bootstrap_look_up(
        bp: libc::mach_port_t,
        service_name: *const libc::c_char,
        sp: *mut libc::mach_port_t,
    ) -> libc::kern_return_t;
}

/// Look up a mach service by name; returns the kern_return (0 = success). A
/// sandbox-denied lookup returns a non-zero refusal.
fn mach_look_up(name: &str) -> i32 {
    let cname = std::ffi::CString::new(name).unwrap();
    let mut port: libc::mach_port_t = 0;
    unsafe { bootstrap_look_up(bootstrap_port, cname.as_ptr(), &mut port) as i32 }
}
