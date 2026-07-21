struct Metadata {
    scalar_count: u32,
    _pad0: u32,
    _pad1: u32,
    _pad2: u32,
};

@group(0) @binding(0) var<uniform> params: Metadata;
@group(0) @binding(1) var<storage, read> scalar_words: array<u32>;
@group(0) @binding(2) var<storage, read_write> windows: array<u32>;

// Each canonical scalar is eight little-endian u32 words.  Radix 256 is byte
// aligned, so the exact Pippenger digit extraction needs no cross-word shifts.
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let scalar_index = gid.x;
    if (scalar_index >= params.scalar_count) {
        return;
    }
    let input_base = scalar_index * 8u;
    let output_base = scalar_index * 32u;
    for (var word_index = 0u; word_index < 8u; word_index = word_index + 1u) {
        let word = scalar_words[input_base + word_index];
        windows[output_base + word_index * 4u] = word & 255u;
        windows[output_base + word_index * 4u + 1u] = (word >> 8u) & 255u;
        windows[output_base + word_index * 4u + 2u] = (word >> 16u) & 255u;
        windows[output_base + word_index * 4u + 3u] = (word >> 24u) & 255u;
    }
}
