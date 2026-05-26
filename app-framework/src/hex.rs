//! Hex encoding/decoding utilities for 32-byte identifiers.
//!
//! These are the common conversions duplicated across dregg apps.

/// Error type for hex decoding failures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HexError {
    /// Input has the wrong length (expected 64 hex chars for 32 bytes).
    InvalidLength { expected: usize, got: usize },
    /// Input contains a non-hex character.
    InvalidChar { ch: char, position: usize },
}

impl std::fmt::Display for HexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidLength { expected, got } => {
                write!(f, "expected {expected} hex chars, got {got}")
            }
            Self::InvalidChar { ch, position } => {
                write!(f, "invalid hex char '{ch}' at position {position}")
            }
        }
    }
}

impl std::error::Error for HexError {}

/// Decode a hex string into a 32-byte array.
///
/// Accepts exactly 64 hex characters (lowercase or uppercase).
/// Optionally strips a leading "0x" prefix.
pub fn hex_to_bytes32(s: &str) -> Result<[u8; 32], HexError> {
    let s = s.strip_prefix("0x").unwrap_or(s);

    if s.len() != 64 {
        return Err(HexError::InvalidLength {
            expected: 64,
            got: s.len(),
        });
    }

    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let hi = hex_nibble(chunk[0], i * 2)?;
        let lo = hex_nibble(chunk[1], i * 2 + 1)?;
        out[i] = (hi << 4) | lo;
    }
    Ok(out)
}

/// Encode a 32-byte array as a lowercase hex string (64 chars).
pub fn bytes32_to_hex(b: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in b {
        out.push(HEX_CHARS[(byte >> 4) as usize]);
        out.push(HEX_CHARS[(byte & 0x0f) as usize]);
    }
    out
}

const HEX_CHARS: [char; 16] = [
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
];

fn hex_nibble(byte: u8, position: usize) -> Result<u8, HexError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        b'A'..=b'F' => Ok(byte - b'A' + 10),
        _ => Err(HexError::InvalidChar {
            ch: byte as char,
            position,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let input = [0xab; 32];
        let hex = bytes32_to_hex(&input);
        assert_eq!(hex.len(), 64);
        let decoded = hex_to_bytes32(&hex).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn with_0x_prefix() {
        let input = [0x01; 32];
        let hex = format!("0x{}", bytes32_to_hex(&input));
        let decoded = hex_to_bytes32(&hex).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn invalid_length() {
        let result = hex_to_bytes32("abcd");
        assert!(matches!(result, Err(HexError::InvalidLength { .. })));
    }

    #[test]
    fn invalid_char() {
        let bad = "zz".to_string() + &"00".repeat(31);
        let result = hex_to_bytes32(&bad);
        assert!(matches!(result, Err(HexError::InvalidChar { .. })));
    }
}
