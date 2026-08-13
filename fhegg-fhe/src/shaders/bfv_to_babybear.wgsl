// THE FUSION SEAM: reinterpret a device-resident BFV RNS ciphertext buffer as a BabyBear MLE
// evaluation table, WITHOUT a host round trip.
//
// The BFV fold's resident output holds one canonical RNS residue per coefficient lane, carried as a
// (lo, hi) u32 pair. Every deployed `FOLD_MODULI` entry is < 2^37, so a residue does not fit one
// BabyBear element (p = 2013265921 < 2^31). It is split into TWO base-2^30 limbs, which IS
// injective on [0, 2^37): limb0 = x mod 2^30 (< 2^30 < p), limb1 = x >> 30 (< 2^7 < p).
//
// ⚑ Injective, not canonical. This is a faithful 2-limb ENCODING of the residue, which is what a
// commitment to the ciphertext needs (a non-injective `x mod p` would let two distinct residues
// share a committed lane — exactly the pigeonhole wound this repo already carries elsewhere). It is
// NOT the base-field decomposition a specific vFHE relation would fix; the relation picks the limb
// base. What is fixed here is the SHAPE: 2 BabyBear elements per RNS lane, i.e. the table is the
// same byte count as the ciphertext it came from.
//
// The output table is padded to a power of two with zeros (zero-padding a multilinear's evaluation
// table extends f by 0 on the new corner, which is the standard embedding).

struct BridgeMeta {
    // Source RNS coefficient lanes (each lane is one u64 = two u32 words).
    n_lanes   : u32,
    // Padded power-of-two output table length, in BabyBear elements.
    table_len : u32,
    _pad0     : u32,
    _pad1     : u32,
};

@group(0) @binding(0) var<uniform>              params : BridgeMeta;
@group(0) @binding(1) var<storage, read>        rns    : array<u32>;
@group(0) @binding(2) var<storage, read_write>  table  : array<u32>;

@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let j = gid.x;
    if (j >= params.table_len) { return; }
    let lane = j >> 1u;
    if (lane >= params.n_lanes) {
        table[j] = 0u;
        return;
    }
    let lo = rns[lane * 2u];
    let hi = rns[lane * 2u + 1u];
    if ((j & 1u) == 0u) {
        table[j] = lo & 0x3fffffffu;
    } else {
        // hi < 2^5 for q < 2^37, so (hi << 2) occupies bits 2..6 and never collides with
        // (lo >> 30), which occupies bits 0..1. The limb is < 2^7.
        table[j] = (lo >> 30u) | (hi << 2u);
    }
}
