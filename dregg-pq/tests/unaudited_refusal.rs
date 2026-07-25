//! The refusal gate, exercised on the SHIPPING code path.
//!
//! `dregg-pq`'s unit tests run with a `#[cfg(test)]` override that permits the
//! unaudited fallback (a unit-test binary cannot link the Lean archive, so every
//! one of them is on the crate path by construction). That override does NOT
//! exist here: an integration test links `dregg-pq` as an ordinary downstream
//! crate, exactly as a deployed binary does. So these tests drive the real gate.
//!
//! The refusal is `process::abort()`, which cannot be caught in-process — so the
//! only way to observe it is to BE a subprocess. This test re-executes its own
//! binary with a marker variable set; the child performs one PQ operation with no
//! verified core installed, and the parent asserts on how the child died.

use std::process::Command;

/// Marker telling a re-executed child which operation to attempt.
const ROLE: &str = "DREGG_PQ_REFUSAL_TEST_ROLE";

/// Lowercase-hex, the encoding every `dregg-pq` verified-core wire uses.
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Install a STAND-IN ML-DSA keygen core so the KEYGEN gate is satisfied and the gate under test
/// (sign) is the only one left armed. See the `"sign"` role for why this is needed and why it does
/// not weaken what that test asserts.
fn install_stand_in_keygen_core() {
    use fips204::ml_dsa_65;
    use fips204::traits::{KeyGen as _, SerDes as _};
    dregg_pq::install_lean_keygen_core_real(|wire| {
        let bytes: Vec<u8> = (0..wire.len() / 2)
            .map(|i| u8::from_str_radix(&wire[2 * i..2 * i + 2], 16).ok())
            .collect::<Option<Vec<u8>>>()?;
        let seed: [u8; 32] = bytes.try_into().ok()?;
        let (pk, sk) = ml_dsa_65::KG::keygen_from_seed(&seed);
        Some(format!(
            "{} {}",
            hex(&pk.into_bytes()),
            hex(&sk.into_bytes())
        ))
    });
}

/// The child half: perform one PQ operation with NO verified core installed and
/// NO opt-in, then report if it somehow survived.
fn child_body(role: &str) -> ! {
    match role {
        "verify" => {
            // Well-formed lengths so the fail-closed length check does not
            // short-circuit before the gate: the gate must be what stops this.
            let pk = vec![0u8; 1952];
            let sig = vec![0u8; 3309];
            let accepted = dregg_pq::ml_dsa_verify(&pk, b"ctx", b"msg", &sig);
            eprintln!("CHILD SURVIVED THE GATE: ml_dsa_verify returned {accepted}");
        }
        "encaps" => {
            let ek = vec![0u8; 1184];
            let out = dregg_pq::ml_kem768_encaps(&ek);
            eprintln!(
                "CHILD SURVIVED THE GATE: ml_kem768_encaps -> {:?}",
                out.is_some()
            );
        }
        "sign" => {
            // The SHIPPING sign path. ⚑ KEYGEN IS NOW GATED TOO (commit `c4f4b9cc3a`), so
            // `ml_dsa_sign_from_seed` used to abort at KEYGEN and this test asserted the SIGN
            // needles against a KEYGEN message — it had been red, unobserved, because no
            // `dregg-pq` row existed in `falsifiers.tsv` to run it. To reach the SIGN gate we
            // install a STAND-IN keygen core so the keygen half is "answered" and the only gate
            // left armed is sign's. The stand-in is the crate expansion behind a `fn` pointer:
            // it is a TEST DOUBLE for the verified core, declared as such, and it is not what
            // this test is about — the subject is that SIGN refuses.
            install_stand_in_keygen_core();
            let seed = [7u8; 32];
            let sig = dregg_pq::ml_dsa_sign_from_seed(&seed, b"ctx", b"msg");
            eprintln!(
                "CHILD SURVIVED THE GATE: ml_dsa_sign_from_seed -> {:?} bytes",
                sig.as_ref().map(|s| s.len())
            );
        }
        "decaps" => {
            // Well-formed FIPS-203 lengths so the fail-closed length gate does
            // not short-circuit ahead of the audit gate: dk = 2400, ct = 1088.
            let dk = vec![0u8; 2400];
            let ct = vec![0u8; 1088];
            let out = dregg_pq::ml_kem768_decaps(&dk, &ct);
            eprintln!(
                "CHILD SURVIVED THE GATE: ml_kem768_decaps -> {:?}",
                out.is_some()
            );
        }
        "verify_genuine" => {
            // ⚑ THE STRONGEST FORM OF THE VERIFY POLE: a GENUINE ML-DSA-65 keypair + signature,
            // minted with the `fips204` crate DIRECTLY (not through `dregg_pq`, whose keygen/sign
            // guards would abort first and prove nothing about the VERIFY gate). If the verify gate
            // falls through to the crate, the crate ACCEPTS — so a fall-open here is an observable
            // ACCEPT, not merely "the process survived".
            use fips204::ml_dsa_65;
            use fips204::traits::{KeyGen as _, SerDes as _, Signer as _};
            let (pk, sk) = ml_dsa_65::KG::try_keygen().expect("fips204 keygen");
            let msg = b"a genuine signature the unaudited crate WOULD accept";
            let sig = sk.try_sign(msg, b"ctx").expect("fips204 sign");
            let accepted = dregg_pq::ml_dsa_verify(&pk.into_bytes(), b"ctx", msg, &sig);
            eprintln!("CHILD SURVIVED THE GATE: ml_dsa_verify returned {accepted}");
            if accepted {
                eprintln!("CHILD OBSERVED ACCEPT");
            }
        }
        other => {
            eprintln!("CHILD: unknown role {other}");
            std::process::exit(3);
        }
    }
    // Reaching here means the unaudited primitive answered without refusal.
    std::process::exit(0);
}

/// Re-exec this test binary as a child in `role`, and return its output.
fn run_child(role: &str, allow_unaudited: bool) -> std::process::Output {
    run_child_env(role, allow_unaudited, false)
}

/// [`run_child`] with the `DREGG_REQUIRE_LEAN` pole under control too, so the REVOCATION can be
/// driven: both variables set at once is the only configuration in which the operator has opted in
/// AND the gate still refuses.
fn run_child_env(role: &str, allow_unaudited: bool, require_lean: bool) -> std::process::Output {
    let exe = std::env::current_exe().expect("current_exe");
    let mut cmd = Command::new(exe);
    // Run only the dispatcher test in the child, single-threaded.
    cmd.arg("child_dispatcher")
        .arg("--exact")
        .arg("--nocapture")
        .arg("--test-threads=1")
        .env(ROLE, role);
    if allow_unaudited {
        cmd.env("DREGG_ALLOW_UNAUDITED_PQ", "1");
    } else {
        cmd.env_remove("DREGG_ALLOW_UNAUDITED_PQ");
    }
    if require_lean {
        cmd.env("DREGG_REQUIRE_LEAN", "1");
    } else {
        cmd.env_remove("DREGG_REQUIRE_LEAN");
    }
    cmd.output().expect("spawn child")
}

/// The re-exec landing pad. In a normal (parent) run the marker is unset and this
/// is a no-op; in a child run it performs the operation and never returns.
#[test]
fn child_dispatcher() {
    if let Ok(role) = std::env::var(ROLE) {
        child_body(&role);
    }
}

/// ★ THE GATE: with no verified core installed and no opt-in, an ML-DSA verify
/// must ABORT the process rather than quietly answer from the `fips204` crate.
#[test]
fn verify_without_core_aborts_loudly() {
    let out = run_child("verify", false);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        !out.status.success(),
        "ml_dsa_verify SURVIVED with no verified core installed — the unaudited \
         fips204 fallback answered silently. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("CHILD SURVIVED THE GATE"),
        "the gate did not stop the call:\n{stderr}"
    );

    // SIGABRT (6), not a catchable panic: a panic would be swallowed by a task
    // boundary in a deployed server, restoring the silent substitution.
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(
            out.status.signal(),
            Some(6),
            "expected SIGABRT (process::abort), got {:?}. stderr:\n{stderr}",
            out.status
        );
    }

    // The message must NAME the unaudited crate that would otherwise have run.
    for needle in [
        "refused to run UNAUDITED post-quantum crypto",
        "ML-DSA-65 verify",
        "fips204 0.4",
        "install_verified_mldsa_verify_core",
        "DREGG_ALLOW_UNAUDITED_PQ=1",
    ] {
        assert!(
            stderr.contains(needle),
            "refusal message is missing {needle:?} — it must name the unaudited \
             crate and the install that fixes it. stderr:\n{stderr}"
        );
    }
}

/// The same for the KEM half, naming `ml-kem` instead.
#[test]
fn encaps_without_core_aborts_loudly() {
    let out = run_child("encaps", false);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        !out.status.success(),
        "ml_kem768_encaps SURVIVED with no verified core installed. stderr:\n{stderr}"
    );
    for needle in [
        "refused to run UNAUDITED post-quantum crypto",
        "ML-KEM-768 encaps",
        "ml-kem 0.2.3",
        "install_verified_mlkem_encaps_core",
    ] {
        assert!(
            stderr.contains(needle),
            "refusal message is missing {needle:?}. stderr:\n{stderr}"
        );
    }
}

/// ★ THE SIGN ARM of the gate. A signature is the half an operator most easily
/// mistakes for verified output -- it is bytes that go on the wire under a
/// pinned identity -- so producing one from the unaudited `fips204` primitive
/// must abort, not warn.
#[test]
fn sign_without_core_aborts_loudly() {
    let out = run_child("sign", false);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        !out.status.success(),
        "ml_dsa_sign_from_seed SURVIVED with no verified core installed -- the \
         unaudited fips204 fallback SIGNED silently. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("CHILD SURVIVED THE GATE"),
        "the gate did not stop the sign:\n{stderr}"
    );

    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(
            out.status.signal(),
            Some(6),
            "expected SIGABRT (process::abort), got {:?}. stderr:\n{stderr}",
            out.status
        );
    }

    for needle in [
        "refused to run UNAUDITED post-quantum crypto",
        "ML-DSA-65 sign",
        "fips204 0.4",
        "install_verified_mldsa_sign_core_real",
        "DREGG_ALLOW_UNAUDITED_PQ=1",
    ] {
        assert!(
            stderr.contains(needle),
            "refusal message is missing {needle:?} -- it must name the unaudited \
             crate and the install that fixes it. stderr:\n{stderr}"
        );
    }
}

/// The decaps twin of `encaps_without_core_aborts_loudly`. Gate 2 guards four
/// arms (verify / sign / encaps / decaps); each one gets a test that proves the
/// abort actually fires, so no arm can rot into a silent fallback unobserved.
#[test]
fn decaps_without_core_aborts_loudly() {
    let out = run_child("decaps", false);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        !out.status.success(),
        "ml_kem768_decaps SURVIVED with no verified core installed. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("CHILD SURVIVED THE GATE"),
        "the gate did not stop the decaps:\n{stderr}"
    );

    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(
            out.status.signal(),
            Some(6),
            "expected SIGABRT (process::abort), got {:?}. stderr:\n{stderr}",
            out.status
        );
    }

    for needle in [
        "refused to run UNAUDITED post-quantum crypto",
        "ML-KEM-768 decaps (bare)",
        "ml-kem 0.2.3",
        "install_verified_mlkem_decaps_core",
    ] {
        assert!(
            stderr.contains(needle),
            "refusal message is missing {needle:?}. stderr:\n{stderr}"
        );
    }
}

/// ⚑ **THE REVOCATION POLE (twin#12): `DREGG_REQUIRE_LEAN=1` REVOKES the
/// `DREGG_ALLOW_UNAUDITED_PQ=1` bypass, and the ACCEPT/REJECT gate REFUSES.**
///
/// This is the hole the declared-bypass wiring closed. `DREGG_REQUIRE_LEAN` is the tree-wide "I
/// demand the verified artifact" switch — `turn::require_verified_conservation_gate`,
/// `node::finality_gate` and `node::coord_gate` all honour it by revoking their declared bypasses —
/// and it had **NO EFFECT ON ANY PQ PATH AT ALL**. An operator could demand the verified artifact
/// and still have the unaudited `fips204` crate deciding accept/reject, because the permissive
/// variable silently won.
///
/// The material is a GENUINE keypair + signature minted by `fips204` directly, so the crate WOULD
/// accept it: this test therefore fails on an observed ACCEPT, not merely on a surviving process.
/// The negative is asserted three ways — the child must not exit 0, must not print `CHILD SURVIVED
/// THE GATE`, and must not print `CHILD OBSERVED ACCEPT`.
///
/// The companion below (`explicit_opt_in_permits_and_announces`, and
/// `genuine_signature_is_accepted_under_the_declared_bypass`) is the NON-OVER-FIRE half: without the
/// revocation the same genuine signature still verifies, so "refuses under require-lean" is not
/// satisfied by a gate that refuses everything.
#[test]
fn require_lean_revokes_the_unaudited_opt_in_and_verify_refuses() {
    let out = run_child_env("verify_genuine", true, true);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        !out.status.success(),
        "DREGG_REQUIRE_LEAN=1 must REVOKE DREGG_ALLOW_UNAUDITED_PQ=1: with no verified core \
         installed, ml_dsa_verify SURVIVED and the unaudited fips204 crate answered a SECURITY \
         accept/reject while the operator was demanding the verified artifact. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("CHILD OBSERVED ACCEPT"),
        "FAIL-OPEN: the child observed an ACCEPT on a genuine signature with DREGG_REQUIRE_LEAN=1 \
         and no verified core — the unaudited `fips204` crate decided a security accept/reject that \
         the operator had explicitly demanded the verified core decide. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("CHILD SURVIVED THE GATE"),
        "the revocation did not stop the call:\n{stderr}"
    );

    // SIGABRT (6), not a catchable panic — a task boundary would swallow a panic and restore the
    // quiet substitution.
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(
            out.status.signal(),
            Some(6),
            "expected SIGABRT (process::abort), got {:?}. stderr:\n{stderr}",
            out.status
        );
    }

    // And the message must say WHICH refusal this is. An operator who has already set
    // DREGG_ALLOW_UNAUDITED_PQ=1 must not be told to set DREGG_ALLOW_UNAUDITED_PQ=1.
    for needle in [
        "REVOKED the DREGG_ALLOW_UNAUDITED_PQ=1 bypass",
        "The DEMAND WINS",
        "ML-DSA-65 verify",
        "install_verified_mldsa_verify_core",
    ] {
        assert!(
            stderr.contains(needle),
            "the revocation message is missing {needle:?} — it must name the contradiction rather \
             than repeat the opt-in advice the operator already took. stderr:\n{stderr}"
        );
    }
}

/// THE NON-OVER-FIRE HALF of the pole above, on the SAME genuine material: with the declared bypass
/// intact (`DREGG_ALLOW_UNAUDITED_PQ=1`, no `DREGG_REQUIRE_LEAN`) an honest signature STILL VERIFIES
/// and a FORGED one is STILL REJECTED. Without this, "refuses when require-lean revokes" would be
/// satisfied by a gate that refuses every verification, and every archive-less build (wasm, the zkVM
/// guest, a dev box) would be bricked — which is exactly what this class must not do.
#[test]
fn genuine_signature_verifies_and_forgery_rejects_under_the_declared_bypass() {
    let out = run_child_env("verify_genuine", true, false);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "the DECLARED bypass must keep archive-less builds working. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("CHILD OBSERVED ACCEPT"),
        "an HONEST signature must still ACCEPT under the declared bypass — otherwise the refusal \
         pole is asserting nothing. stderr:\n{stderr}"
    );

    // THE NEGATIVE, in-process (this test binary has no verified core, so the declared bypass is
    // what answers — the same backend the child above used). A forged signature and a tampered one
    // must both REJECT: a bypass that accepts everything is not a fallback, it is a hole.
    unsafe { std::env::set_var("DREGG_ALLOW_UNAUDITED_PQ", "1") };
    use fips204::ml_dsa_65;
    use fips204::traits::{KeyGen as _, SerDes as _, Signer as _};
    let (pk, sk) = ml_dsa_65::KG::try_keygen().expect("fips204 keygen");
    let (attacker_pk, attacker_sk) = ml_dsa_65::KG::try_keygen().expect("fips204 keygen");
    let msg = b"the message the honest holder actually signed";
    let sig = sk.try_sign(msg, b"ctx").expect("sign");
    let pk_bytes = pk.into_bytes();

    assert!(
        dregg_pq::ml_dsa_verify(&pk_bytes, b"ctx", msg, &sig),
        "sanity: the honest signature accepts"
    );
    let forged = attacker_sk.try_sign(msg, b"ctx").expect("sign");
    assert!(
        !dregg_pq::ml_dsa_verify(&pk_bytes, b"ctx", msg, &forged),
        "FORGERY ACCEPTED: a signature by the attacker's OWN key over the same message must be \
         REJECTED against the honest holder's enrolled public key"
    );
    assert!(
        dregg_pq::ml_dsa_verify(&attacker_pk.into_bytes(), b"ctx", msg, &forged),
        "sanity: the forged signature IS valid under the attacker's own key — so the rejection \
         above is the KEY BINDING, not a broken signature"
    );
    let mut tampered = sig;
    tampered[100] ^= 0xff;
    assert!(
        !dregg_pq::ml_dsa_verify(&pk_bytes, b"ctx", msg, &tampered),
        "a one-byte-tampered signature must be REJECTED"
    );
    assert!(
        !dregg_pq::ml_dsa_verify(&pk_bytes, b"ctx", b"a different message", &sig),
        "a valid signature over a DIFFERENT message must be REJECTED"
    );

    // And the PROVENANCE says who answered: every one of those verdicts came from the unaudited
    // crate, and `pq_provenance()` reports it PER SITE rather than as one boot line.
    let verify_row = dregg_pq::pq_provenance()
        .into_iter()
        .find(|(site, _, _, _)| *site == dregg_pq::PqSite::MlDsaVerify)
        .expect("the ml_dsa_verify row");
    assert!(
        verify_row.2 >= 5,
        "the per-site provenance must count the unaudited answers (got {}) — the legibility half of \
         twin#12 is that an operator can tell WHICH implementation answered a verification",
        verify_row.2
    );
    assert_eq!(
        verify_row.1, 0,
        "and it must NOT claim the verified core answered anything in a binary with no core installed"
    );
}

/// The opt-out must work — otherwise the gate would break every legitimate
/// non-verified build — and it must ANNOUNCE itself, so an operator who set the
/// variable (or inherited it from a script) still learns this process is running
/// unaudited crypto.
#[test]
fn explicit_opt_in_permits_and_announces() {
    let out = run_child("verify", true);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        out.status.success(),
        "DREGG_ALLOW_UNAUDITED_PQ=1 must permit the fallback. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("UNAUDITED crate primitives"),
        "the opt-in must still WARN that this process runs unaudited crypto. \
         stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("CHILD SURVIVED THE GATE"),
        "with the opt-in set the operation should have completed. stderr:\n{stderr}"
    );
}
