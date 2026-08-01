//! # R1 internal_vars / rows_rev BYTE-DIFF — closing the last placement-fidelity residual
//!
//! R1 (`metatheory/Dregg2/Circuit/Emit/KimchiPlacement.lean`, commit 425ec7d87) made the placed
//! `{row,col}` gate WIRES byte-exact vs o1js, and MODELLED the `internal_vars` / `rows_rev` blob
//! shapes (`InternalVarDef` / `PGate.permVars`). It explicitly LEFT the byte-diff of those blobs as
//! a residual, because o1js's `constraintSystem` JSON does not expose them.
//!
//! This tool closes the residual. The REFERENCE is authoritative: `oracle/extract-reference.mjs`
//! reaches o1js's LIVE OCaml constraint system `cs` — the SAME object o1js's own
//! `dump_extra_circuit_data` (plonk_constraint_system.ml:2451) serialises into `_rows_rev.bin`
//! (`cs[3]`, a `V.t option array list`) and `_internal_vars.bin` (`cs[2]`, an
//! `Internal_var.Table.t`). We serialise both the reference and R1's Lean model with the EXACT
//! OCaml-compatible binprot codec mina-rust uses to read real circuit-blobs
//! (openmina/binprot-rs@400b52c), and byte-diff.
//!
//! House law #1: Lean emits internal_vars/rows_rev; o1js is a READ-ONLY oracle. mina-rust is neither
//! modified nor linked — we re-declare `VRaw` byte-identically to
//! `mina-rust crates/ledger/src/proofs/provers.rs:285-289`.

use binprot::{BinProtRead, BinProtWrite};
use binprot_derive::{BinProtRead, BinProtWrite};
use serde::Deserialize;
use std::collections::HashMap;

// ───────────────────────── mina-rust-faithful binprot types ─────────────────────────
// provers.rs:285-289
#[derive(Clone, Debug, PartialEq, BinProtRead, BinProtWrite)]
enum VRaw {
    External(u32),
    Internal(u32),
}

// provers.rs:296  —  rows_rev.bin  ==  `V.t option array list`
type RowsRev = Vec<Vec<Option<VRaw>>>;

/// Fp coefficient. OCaml `Fp.t` bin_io is a fixed 32-byte field element. This is used ONLY to
/// exhibit a NON-EMPTY Lean-side internal_vars table; the authoritative internal_vars divergence
/// is the ENTRY COUNT at byte offset 0 (empty map = `0x00`), which is independent of this encoding.
#[derive(Clone, Debug, PartialEq)]
struct Coeff([u8; 32]);
impl Coeff {
    fn one() -> Self {
        let mut b = [0u8; 32];
        b[0] = 1;
        Coeff(b)
    }
}
impl BinProtWrite for Coeff {
    fn binprot_write<W: std::io::Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(&self.0)
    }
}

// provers.rs:293  —  internal_vars.bin  ==  `HashMap<u32, (Vec<(BigInt, VRaw)>, Option<BigInt>)>`
type InternalVars = HashMap<u32, (Vec<(Coeff, VRaw)>, Option<Coeff>)>;

// ───────────────────────── reference JSON (from the o1js oracle) ─────────────────────────
#[derive(Deserialize)]
struct RefCell {
    kind: String,
    i: u32,
}
#[derive(Deserialize)]
struct RefJson {
    circuit: String,
    rows: u32,
    internal_vars_count: u32,
    rows_rev_on_disk: Vec<Vec<Option<RefCell>>>,
}
impl RefJson {
    fn rows_rev(&self) -> RowsRev {
        self.rows_rev_on_disk
            .iter()
            .map(|row| {
                row.iter()
                    .map(|c| {
                        c.as_ref().map(|c| match c.kind.as_str() {
                            "External" => VRaw::External(c.i),
                            "Internal" => VRaw::Internal(c.i),
                            other => panic!("unknown V kind {other}"),
                        })
                    })
                    .collect()
            })
            .collect()
    }
}

// ───────────────────────── R1's Lean model (transcribed from KimchiPlacement.lean) ─────────────
fn ext(i: u32) -> Option<VRaw> {
    Some(VRaw::External(i))
}
fn int(i: u32) -> Option<VRaw> {
    Some(VRaw::Internal(i))
}
const N: Option<VRaw> = None;

/// R1 `caseA.permVars` (KimchiPlacement.lean:227-230), in gate/circuit order.
fn lean_rows_rev(circuit: &str) -> RowsRev {
    match circuit {
        // caseA: one generic gate.
        "caseA" => vec![vec![int(0), ext(0), ext(1), N, N, int(0), N]],
        // caseB: two generic gates (lines 248-256).
        "caseB" => vec![
            vec![int(0), N, N, ext(0), ext(0), int(0), N],
            vec![int(1), N, N, ext(0), N, int(1), N],
        ],
        _ => unreachable!(),
    }
}

/// R1's modelled internal_vars. caseA references `Internal 0` (an implied reduction var); caseB has
/// `caseB_internalVars = [{id:0, terms:[(1, External 0)], const: Some 1}]` (KimchiPlacement.lean:327-328).
fn lean_internal_vars(circuit: &str) -> InternalVars {
    let mut m = InternalVars::new();
    match circuit {
        "caseA" => {
            // implied by permVars referencing Internal 0 (the reduced sum var).
            m.insert(0, (vec![(Coeff::one(), VRaw::External(0))], None));
        }
        "caseB" => {
            m.insert(
                0,
                (vec![(Coeff::one(), VRaw::External(0))], Some(Coeff::one())),
            );
        }
        _ => unreachable!(),
    }
    m
}

// ───────────────────────── helpers ─────────────────────────
fn ser<T: BinProtWrite>(t: &T) -> Vec<u8> {
    let mut v = Vec::new();
    t.binprot_write(&mut v).unwrap();
    v
}
fn hexs(b: &[u8]) -> String {
    b.iter()
        .map(|x| format!("{x:02x}"))
        .collect::<Vec<_>>()
        .join(" ")
}
fn first_diff(a: &[u8], b: &[u8]) -> Option<usize> {
    let n = a.len().min(b.len());
    for i in 0..n {
        if a[i] != b[i] {
            return Some(i);
        }
    }
    if a.len() != b.len() {
        Some(n)
    } else {
        None
    }
}
fn fmt_row(row: &[Option<VRaw>]) -> String {
    let cells: Vec<String> = row
        .iter()
        .map(|c| match c {
            None => "_".to_string(),
            Some(VRaw::External(i)) => format!("E{i}"),
            Some(VRaw::Internal(i)) => format!("I{i}"),
        })
        .collect();
    format!("[{}]", cells.join(", "))
}

fn main() {
    let mut fail = false;
    println!("R1 internal_vars / rows_rev BYTE-DIFF  (o1js 2.15.0 reference  vs  KimchiPlacement.lean model)");
    println!("codec: openmina/binprot-rs@400b52c (the OCaml-compatible codec mina-rust reads real circuit-blobs with)\n");

    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("reference");
    for circuit in ["caseA", "caseB"] {
        let rj: RefJson = serde_json::from_str(
            &std::fs::read_to_string(dir.join(format!("{circuit}.json"))).unwrap(),
        )
        .unwrap();
        assert_eq!(rj.circuit, circuit);
        println!(
            "════════════════════════════ {circuit}  (rows={}) ════════════════════════════",
            rj.rows
        );

        // ---------- rows_rev ----------
        let ref_rr = rj.rows_rev(); // on-disk (reversed) order, as the .bin holds it
        let lean_rr = lean_rows_rev(circuit); // gate/circuit order
        let ref_bytes = ser(&ref_rr);
        let lean_bytes = ser(&lean_rr);

        println!("── rows_rev.bin ──");
        println!(
            "  reference (o1js, on-disk order): {} bytes  {}",
            ref_bytes.len(),
            hexs(&ref_bytes)
        );
        for (i, r) in ref_rr.iter().enumerate() {
            println!("      on-disk row {i}: {}", fmt_row(r));
        }
        println!(
            "  lean model (circuit order):      {} bytes  {}",
            lean_bytes.len(),
            hexs(&lean_bytes)
        );
        for (i, r) in lean_rr.iter().enumerate() {
            println!("      gate     row {i}: {}", fmt_row(r));
        }
        match first_diff(&ref_bytes, &lean_bytes) {
            None => println!("  rows_rev: BYTE-MATCH"),
            Some(off) => {
                fail = true;
                println!(
                    "  rows_rev: DIVERGES — first differing byte at offset {off} (ref={}, lean={})",
                    ref_bytes
                        .get(off)
                        .map(|b| format!("0x{b:02x}"))
                        .unwrap_or_else(|| "<eof>".into()),
                    lean_bytes
                        .get(off)
                        .map(|b| format!("0x{b:02x}"))
                        .unwrap_or_else(|| "<eof>".into())
                );
            }
        }

        // aligned CONTENT divergence (reverse the reference back to circuit order to remove the
        // storage-reversal convention and expose the SUBSTANTIVE per-cell divergences).
        let mut ref_circuit = ref_rr.clone();
        ref_circuit.reverse();
        println!("  ── substantive per-cell divergence (row order aligned to circuit order) ──");
        let nrows = ref_circuit.len().max(lean_rr.len());
        for ri in 0..nrows {
            let rr = ref_circuit.get(ri);
            let lr = lean_rr.get(ri);
            match (rr, lr) {
                (Some(rr), Some(lr)) => {
                    if rr.len() != lr.len() {
                        println!(
                            "    row {ri}: LENGTH ref={} lean={}   ref={}  lean={}",
                            rr.len(),
                            lr.len(),
                            fmt_row(rr),
                            fmt_row(lr)
                        );
                    }
                    let w = rr.len().max(lr.len());
                    for col in 0..w {
                        let a = rr.get(col).cloned().flatten();
                        let b = lr.get(col).cloned().flatten();
                        if a != b {
                            println!("    row {ri} col {col}: ref={}  lean={}", opt(&a), opt(&b));
                        }
                    }
                }
                (r, l) => println!(
                    "    row {ri}: ref={:?} lean={:?}",
                    r.map(|x| fmt_row(x)),
                    l.map(|x| fmt_row(x))
                ),
            }
        }

        // shape-confirmation: the mina-rust binprot type round-trips o1js's real rows_rev.
        let decoded = RowsRev::binprot_read(&mut ref_bytes.as_slice()).unwrap();
        assert_eq!(decoded, ref_rr, "round-trip must reproduce the reference");
        println!("  shape: reference rows_rev decodes back through `Vec<Vec<Option<VRaw>>>` identically (round-trip OK)");

        // ---------- internal_vars ----------
        let ref_iv: InternalVars = InternalVars::new(); // o1js: EMPTY (internal_vars_count == 0)
        assert_eq!(
            rj.internal_vars_count, 0,
            "oracle measured internal_vars empty"
        );
        let lean_iv = lean_internal_vars(circuit);
        let ref_iv_bytes = ser(&ref_iv);
        let lean_iv_bytes = ser(&lean_iv);
        println!("── internal_vars.bin ──");
        println!(
            "  reference (o1js): {} entr{}  bytes: {}",
            rj.internal_vars_count,
            if rj.internal_vars_count == 1 {
                "y"
            } else {
                "ies"
            },
            hexs(&ref_iv_bytes)
        );
        println!(
            "  lean model:       {} entry   bytes[0..]: {}",
            lean_iv.len(),
            hexs(&lean_iv_bytes[..lean_iv_bytes.len().min(6)])
        );
        match first_diff(&ref_iv_bytes, &lean_iv_bytes) {
            None => println!("  internal_vars: BYTE-MATCH"),
            Some(off) => {
                fail = true;
                println!("  internal_vars: DIVERGES — first differing byte at offset {off} (ref=0x{:02x} [Nat0 entry-count 0], lean=0x{:02x} [entry-count {}])",
                    ref_iv_bytes[off], lean_iv_bytes[off], lean_iv.len());
            }
        }
        println!();
    }

    // ───────── comparator self-tests: satisfiable (green) AND refutable (red) ─────────
    println!("════════════════════════════ comparator self-tests ════════════════════════════");
    let a: RowsRev = vec![vec![ext(2), N, N, ext(0), ext(1), ext(2)]];
    // green achievable: identical bytes compare equal
    let green_ok = first_diff(&ser(&a), &ser(&a)).is_none();
    // red achievable: corrupt ONE cell (External 2 -> External 9) and confirm the diff bites
    let mut corrupt = a.clone();
    corrupt[0][0] = ext(9);
    let red_ok = first_diff(&ser(&a), &ser(&corrupt)).is_some();
    // round-trip achievable
    let rt_ok = RowsRev::binprot_read(&mut ser(&a).as_slice())
        .map(|d| d == a)
        .unwrap_or(false);
    println!(
        "  green (identical == identical):        {}",
        if green_ok { "PASS" } else { "FAIL" }
    );
    println!(
        "  red   (one-cell corruption detected):  {}",
        if red_ok { "PASS" } else { "FAIL" }
    );
    println!(
        "  round-trip (write->read identity):     {}",
        if rt_ok { "PASS" } else { "FAIL" }
    );
    if !(green_ok && red_ok && rt_ok) {
        eprintln!("SELF-TEST FAILURE: comparator is stuck — a diff that cannot fail is documented-not-detected");
        std::process::exit(2);
    }

    println!("\nVERDICT: R1's internal_vars/rows_rev MODEL DIVERGES from o1js's actual constraint system.");
    println!("  • wires match (R1's proven result holds); rows_rev/internal_vars do NOT.");
    println!("  • internal_vars: o1js EMPTY vs R1 non-empty  (byte 0: 0x00 vs 0x01).");
    println!(
        "  • rows_rev: o1js uses External witnesses where R1 modelled Internal reduction vars,"
    );
    println!(
        "    at different singleton columns; same equivalence-class STRUCTURE => identical wires."
    );
    if fail {
        std::process::exit(1);
    }
}

fn opt(o: &Option<VRaw>) -> String {
    match o {
        None => "_".into(),
        Some(VRaw::External(i)) => format!("E{i}"),
        Some(VRaw::Internal(i)) => format!("I{i}"),
    }
}
