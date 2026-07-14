//! fhegg-rtl / hardware / cosim / cosim_harness.rs  —  SCAFFOLD (honest TODOs)
//!
//! The differential co-simulation harness: read golden vectors dumped from the Lean golden model
//! (`../../lean/Fhegg/Rtl/Golden/`), drive the contributor's RTL simulator on the same inputs, and
//! assert equality — the RTL analogue of dregg's Rust `*_layout_matches_lean` byte-pin twin
//! (`circuit/src/effect_vm_descriptors.rs`).
//!
//! STATUS: this is a COMMENTED SCAFFOLD, deliberately NOT a member of the Cargo workspace (so it
//! cannot break other lanes' builds). A contributor turns it into a real crate — `cargo new`, add
//! it under `fhegg-rtl/hardware/cosim/`, wire a Verilator FFI or shell out to `verilator`/SpinalSim.
//! See `README.md` in this directory for the three-step contract.

// ------------------------------------------------------------------------------------------------
// A golden test vector for the NTT butterfly: (a, b, w) -> (hi, lo) mod q.
// Parsed from the CSV the Lean dumper prints (README §1): "a,b,w,hi,lo".
#[derive(Debug, Clone, PartialEq)]
pub struct ButterflyVector {
    pub a: i128,
    pub b: i128,
    pub w: i128,
    pub hi_expected: i128,
    pub lo_expected: i128,
}

impl ButterflyVector {
    /// Parse one CSV row `a,b,w,hi,lo`. TODO(contributor): robust error handling.
    pub fn parse(_line: &str) -> Option<ButterflyVector> {
        // let mut it = line.split(',').map(|s| s.trim().parse::<i128>().ok());
        // Some(ButterflyVector { a: it.next()??, b: it.next()??, w: it.next()??,
        //                        hi_expected: it.next()??, lo_expected: it.next()?? })
        todo!("parse CSV row from the Lean golden-vector dump")
    }
}

/// The interface a contributor's RTL simulator must implement: given (a, b, w) produce the
/// module's (hi, lo). Back this with a Verilator FFI, a subprocess to `verilator`, or SpinalSim.
pub trait ButterflySim {
    fn eval(&mut self, a: i128, b: i128, w: i128) -> (i128, i128);
}

/// Drive every golden vector through the RTL sim and assert equality. Returns the first mismatch,
/// or Ok(count) on full agreement — the co-sim PASS. This is the whole tie: the Lean golden model
/// PROVED `eval = spec` (`Fhegg.Rtl.Golden.butterfly` + `butterfly_add`/`butterfly_sub`), and this
/// checks the RTL realizes the same function on the vectors. The residual seam — "the simulator
/// faithfully executes the emitted RTL" — is NAMED, not proven (no formal Verilog semantics).
pub fn run_cosim<S: ButterflySim>(
    _sim: &mut S,
    _vectors: &[ButterflyVector],
) -> Result<usize, String> {
    // for (i, v) in vectors.iter().enumerate() {
    //     let (hi, lo) = sim.eval(v.a, v.b, v.w);
    //     if hi != v.hi_expected || lo != v.lo_expected {
    //         return Err(format!(
    //             "cosim mismatch at vector {i}: a={} b={} w={} :: RTL ({hi},{lo}) != golden ({},{})",
    //             v.a, v.b, v.w, v.hi_expected, v.lo_expected
    //         ));
    //     }
    // }
    // Ok(vectors.len())
    todo!("drive the RTL simulator over the golden vectors and assert equality")
}

// ------------------------------------------------------------------------------------------------
// TODO(contributor) — the full loop:
//   1. `lake env lean --run DumpButterflyVectors.lean > butterfly_golden.csv`  (README §1)
//   2. elaborate `../spinalhdl/Butterfly.scala` -> Verilog (`SpinalVerilog(...)`)
//   3. build a Verilator model (or SpinalSim), implement `ButterflySim` over it
//   4. `run_cosim(&mut sim, &vectors)` in a `#[test]` — CI gate on PASS
//   5. for the wide/sequential datapaths (NTT, PBS): move to sequential equivalence checking
//      against the staged golden model rather than vector diffing (README "Scaling up").
