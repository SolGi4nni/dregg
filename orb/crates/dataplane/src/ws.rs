//! The RFC 6455 WebSocket **handshake** — the one piece of the WebSocket lane the
//! host owns, for the same reason the C shells do (`ffi/mac_io.c`): the proven
//! core ships no SHA-1, and the `Sec-WebSocket-Accept` token is a handshake
//! framing value, not part of the WebSocket data path.
//!
//! The split is the same discipline as HTTP/1.1 framing in [`crate::http`]: the
//! host reads only what it needs to *select* the WebSocket lane (the Upgrade
//! discriminator) and complete the opening handshake (the accept token). Every
//! WebSocket **data** frame after the 101 is handed unchanged to the proven
//! `drorb_serve_ws_frame` (`Seam::WsFrame`) — decode, unmask, reassemble, and
//! re-encode are the proven core's job. This module never touches a data frame.

/// SHA-1 (RFC 3174), one-shot. Used ONLY for the handshake accept token; never on
/// the WebSocket data path.
fn sha1(msg: &[u8]) -> [u8; 20] {
    let (mut h0, mut h1, mut h2, mut h3, mut h4): (u32, u32, u32, u32, u32) =
        (0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0);
    let mut m = msg.to_vec();
    let bits = (msg.len() as u64) * 8;
    m.push(0x80);
    while m.len() % 64 != 56 {
        m.push(0);
    }
    m.extend_from_slice(&bits.to_be_bytes());
    for chunk in m.chunks_exact(64) {
        let mut w = [0u32; 80];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
            ]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }
        let (mut a, mut b, mut c, mut d, mut e) = (h0, h1, h2, h3, h4);
        for (i, wi) in w.iter().enumerate() {
            let (f, k): (u32, u32) = match i {
                0..=19 => ((b & c) | ((!b) & d), 0x5A827999),
                20..=39 => (b ^ c ^ d, 0x6ED9EBA1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1BBCDC),
                _ => (b ^ c ^ d, 0xCA62C1D6),
            };
            let t = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(*wi);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = t;
        }
        h0 = h0.wrapping_add(a);
        h1 = h1.wrapping_add(b);
        h2 = h2.wrapping_add(c);
        h3 = h3.wrapping_add(d);
        h4 = h4.wrapping_add(e);
    }
    let mut out = [0u8; 20];
    for (i, h) in [h0, h1, h2, h3, h4].into_iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&h.to_be_bytes());
    }
    out
}

/// Base64 (RFC 4648) encode.
fn base64(input: &[u8]) -> String {
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity((input.len() + 2) / 3 * 4);
    for chunk in input.chunks(3) {
        let b = [
            chunk[0],
            *chunk.get(1).unwrap_or(&0),
            *chunk.get(2).unwrap_or(&0),
        ];
        let v = ((b[0] as u32) << 16) | ((b[1] as u32) << 8) | (b[2] as u32);
        out.push(T[((v >> 18) & 63) as usize] as char);
        out.push(T[((v >> 12) & 63) as usize] as char);
        out.push(if chunk.len() > 1 {
            T[((v >> 6) & 63) as usize] as char
        } else {
            '='
        });
        out.push(if chunk.len() > 2 {
            T[(v & 63) as usize] as char
        } else {
            '='
        });
    }
    out
}

/// Case-insensitive substring search over a byte buffer.
fn ci_find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || needle.len() > hay.len() {
        return None;
    }
    (0..=hay.len() - needle.len()).find(|&i| {
        hay[i..i + needle.len()]
            .iter()
            .zip(needle)
            .all(|(a, b)| a.to_ascii_lowercase() == b.to_ascii_lowercase())
    })
}

/// Is this request an RFC 6455 WebSocket upgrade? The lane discriminator — the
/// TCP analogue of the proven Ingress fork on the h2c preface.
pub fn is_ws_upgrade(head: &[u8]) -> bool {
    ci_find(head, b"sec-websocket-key:").is_some() && ci_find(head, b"websocket").is_some()
}

/// The RFC 6455 magic GUID appended to the client key before hashing.
const GUID: &[u8] = b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11";

/// Build the 101 Switching Protocols response for a WebSocket upgrade request,
/// or `None` if it carries no `Sec-WebSocket-Key`. The accept token is
/// `base64(sha1(key ++ GUID))` (RFC 6455 §4.2.2).
pub fn upgrade_response(head: &[u8]) -> Option<Vec<u8>> {
    let ki = ci_find(head, b"sec-websocket-key:")?;
    let mut p = ki + b"sec-websocket-key:".len();
    while p < head.len() && (head[p] == b' ' || head[p] == b'\t') {
        p += 1;
    }
    let start = p;
    while p < head.len() && head[p] != b'\r' && head[p] != b'\n' {
        p += 1;
    }
    let key = &head[start..p];
    let mut cat = Vec::with_capacity(key.len() + GUID.len());
    cat.extend_from_slice(key);
    cat.extend_from_slice(GUID);
    let accept = base64(&sha1(&cat));
    Some(
        format!(
            "HTTP/1.1 101 Switching Protocols\r\n\
             Upgrade: websocket\r\n\
             Connection: Upgrade\r\n\
             Sec-WebSocket-Accept: {accept}\r\n\r\n"
        )
        .into_bytes(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rfc6455_accept_vector() {
        // RFC 6455 §1.3: key "dGhlIHNhbXBsZSBub25jZQ==" → accept
        // "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=".
        let head = b"GET /chat HTTP/1.1\r\nUpgrade: websocket\r\n\
                     Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\r\n";
        let resp = String::from_utf8(upgrade_response(head).unwrap()).unwrap();
        assert!(resp.contains("Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo="));
    }
}
