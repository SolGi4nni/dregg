// Exact batched signed dots for the private-book BFV/R1CS message table.
//
// One workgroup computes one
//   sum_i sign[sign_row][i] * message[option][modulus][i]
// over u64 message coefficients. WGSL has no u64, so positive and negative
// terms are accumulated independently as exact (lo, hi) u32 pairs. The host
// performs the final signed subtraction in i128. No field reduction or float
// arithmetic occurs in this kernel.

struct Meta {
    sign_rows: u32,
    options: u32,
    degree: u32,
    sign_words: u32,
    sign_rows_per_modulus: u32,
    moduli: u32,
    _pad0: u32,
    _pad1: u32,
};

@group(0) @binding(0) var<uniform> params: Meta;
@group(0) @binding(1) var<storage, read> signs: array<u32>;
// [option][modulus][coefficient][lo, hi]
@group(0) @binding(2) var<storage, read> messages: array<u32>;
// [sign_row][option][positive_lo, positive_hi, negative_lo, negative_hi]
@group(0) @binding(3) var<storage, read_write> dots: array<u32>;

var<workgroup> positive_lo: array<u32, 256>;
var<workgroup> positive_hi: array<u32, 256>;
var<workgroup> negative_lo: array<u32, 256>;
var<workgroup> negative_hi: array<u32, 256>;

fn add64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let lo = a.x + b.x;
    let carry = select(0u, 1u, lo < a.x);
    return vec2<u32>(lo, a.y + b.y + carry);
}

@compute @workgroup_size(256)
fn main(
    @builtin(workgroup_id) group: vec3<u32>,
    @builtin(local_invocation_id) local: vec3<u32>,
) {
    let option = group.x;
    let sign_row = group.y;
    if (option >= params.options || sign_row >= params.sign_rows) {
        return;
    }

    let modulus = sign_row / params.sign_rows_per_modulus;
    var positive = vec2<u32>(0u, 0u);
    var negative = vec2<u32>(0u, 0u);
    var coefficient = local.x;
    loop {
        if (coefficient >= params.degree) {
            break;
        }
        let sign_word = signs[sign_row * params.sign_words + coefficient / 32u];
        let is_positive = ((sign_word >> (coefficient & 31u)) & 1u) != 0u;
        let message_index = ((option * params.moduli + modulus) * params.degree + coefficient) * 2u;
        let value = vec2<u32>(messages[message_index], messages[message_index + 1u]);
        if (is_positive) {
            positive = add64(positive, value);
        } else {
            negative = add64(negative, value);
        }
        coefficient += 256u;
    }

    positive_lo[local.x] = positive.x;
    positive_hi[local.x] = positive.y;
    negative_lo[local.x] = negative.x;
    negative_hi[local.x] = negative.y;
    workgroupBarrier();

    var stride = 128u;
    loop {
        if (local.x < stride) {
            let positive_sum = add64(
                vec2<u32>(positive_lo[local.x], positive_hi[local.x]),
                vec2<u32>(positive_lo[local.x + stride], positive_hi[local.x + stride]),
            );
            let negative_sum = add64(
                vec2<u32>(negative_lo[local.x], negative_hi[local.x]),
                vec2<u32>(negative_lo[local.x + stride], negative_hi[local.x + stride]),
            );
            positive_lo[local.x] = positive_sum.x;
            positive_hi[local.x] = positive_sum.y;
            negative_lo[local.x] = negative_sum.x;
            negative_hi[local.x] = negative_sum.y;
        }
        workgroupBarrier();
        if (stride == 1u) {
            break;
        }
        stride >>= 1u;
    }

    if (local.x == 0u) {
        let output = (sign_row * params.options + option) * 4u;
        dots[output] = positive_lo[0];
        dots[output + 1u] = positive_hi[0];
        dots[output + 2u] = negative_lo[0];
        dots[output + 3u] = negative_hi[0];
    }
}
