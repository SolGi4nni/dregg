//! ⚑ **THE SECOND SOURCE FOR A `vkPin` LITERAL.**
//!
//! A `proofBind` leg's `vkPin` is a list of nine `Faithful9` key lanes of the bound program's
//! SEMANTIC FINGERPRINT, written as literals into a Lean descriptor
//! (`LightClientMinaAir.{CHAINLINK_VK_LANES, LINK_VK_LANES, CONJ_VK_LANES}`). Those literals cannot
//! be computed in Lean — the fingerprint is blake3 over the emitted bytes — so an author has to get
//! them from somewhere, and "somewhere" has already been wrong once: `75df624cf` re-emitted
//! `pasta-fq-wraplink.json` and the pinned lanes did not follow, so a deployed bind named **a
//! program no descriptor in this tree had**.
//!
//! This prints them from the served artifact. It is a WRITER'S tool, not a gate — the gate is
//! `circuit/tests/mina_transcript_carrier_binding.rs`, which recomputes the same lanes and asserts
//! them against the Lean literals, and `mina_head_verifier::check_subproof_program_pin`, which
//! recomputes them again at VERIFY time.
//!
//! ```text
//! cargo run -p dregg-circuit --release --example conj_fingerprint -- \
//!     circuit/descriptors/by-name/mina-wrap-conjunction.json
//! ```

use dregg_circuit::descriptor_ir2::parse_vm_descriptor2;
use dregg_circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;

/// `Faithful9::from_key_lanes9` — the 32 bytes as one little-endian 256-bit number in its NINE
/// base-`2^29` digits. Lanes 0..=7 below `2^29`, lane 8 below `2^24`; `8·29 + 24 = 256` exactly, so
/// the encoding loses nothing (`fieldToLanes9_injective`).
fn key_lanes9(bytes: &[u8; 32]) -> [u64; 9] {
    let mut acc = [0u64; 9];
    let mut cur: u128 = 0;
    let mut bits = 0u32;
    let mut out = 0usize;
    for b in bytes.iter() {
        cur |= (*b as u128) << bits;
        bits += 8;
        while bits >= 29 && out < 8 {
            acc[out] = (cur & ((1u128 << 29) - 1)) as u64;
            cur >>= 29;
            bits -= 29;
            out += 1;
        }
    }
    acc[8] = cur as u64;
    acc
}

fn main() {
    let mut any = false;
    for path in std::env::args().skip(1) {
        any = true;
        let json =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));
        let d = parse_vm_descriptor2(&json).unwrap_or_else(|e| panic!("cannot parse {path}: {e}"));
        let fp = effect_vm_descriptor2_semantic_fingerprint(&d)
            .unwrap_or_else(|e| panic!("{path} is not fingerprint-representable: {e}"));
        let lanes = key_lanes9(&fp);
        println!(
            "{path}\t{}\tw={}\tpi={}\tcons={}\tfp={}\tlanes={:?}",
            d.name,
            d.trace_width,
            d.public_input_count,
            d.constraints.len(),
            fp.iter().map(|b| format!("{b:02x}")).collect::<String>(),
            lanes
        );
    }
    if !any {
        eprintln!("usage: conj_fingerprint <by-name descriptor json> ...");
        std::process::exit(2);
    }
}
