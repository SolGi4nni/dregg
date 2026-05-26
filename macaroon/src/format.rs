//! Macaroon encoding format.
//!
//! Wire format: MsgPack binary, base64url-encoded, with `em2_` prefix.
//!
//! - `em2_` = "Dregg Macaroon v2"
//! - Base64 uses URL-safe alphabet, no padding
//! - Authorization header: `DreggV1 em2_<token>,em2_<discharge>,...`

use base64::Engine;
use base64::engine::general_purpose::URL_SAFE_NO_PAD;

use crate::error::MacaroonError;

/// Prefix for Dregg Macaroon v2 tokens.
pub const TOKEN_PREFIX: &str = "em2_";

/// Authorization header scheme.
pub const AUTH_SCHEME: &str = "DreggV1";

/// Encode a binary macaroon to the wire format: `em2_<base64url>`.
pub fn encode_token(binary: &[u8]) -> String {
    let mut result = String::with_capacity(TOKEN_PREFIX.len() + binary.len() * 4 / 3 + 4);
    result.push_str(TOKEN_PREFIX);
    URL_SAFE_NO_PAD.encode_string(binary, &mut result);
    result
}

/// Decode a wire-format token back to binary.
///
/// Strips the `em2_` prefix and base64url-decodes.
pub fn decode_token(token: &str) -> Result<Vec<u8>, MacaroonError> {
    let b64 = token
        .strip_prefix(TOKEN_PREFIX)
        .ok_or_else(|| MacaroonError::Malformed(format!("missing '{TOKEN_PREFIX}' prefix")))?;
    URL_SAFE_NO_PAD
        .decode(b64)
        .map_err(|e| MacaroonError::Encoding(e.to_string()))
}

/// Format an Authorization header value from permission + discharge tokens.
///
/// Result: `DreggV1 em2_<permission>,em2_<discharge1>,em2_<discharge2>,...`
pub fn format_auth_header(permission: &[u8], discharges: &[Vec<u8>]) -> String {
    let mut parts = Vec::with_capacity(1 + discharges.len());
    parts.push(encode_token(permission));
    for d in discharges {
        parts.push(encode_token(d));
    }
    format!("{AUTH_SCHEME} {}", parts.join(","))
}

/// Parse an Authorization header value into permission + discharge tokens.
///
/// Expected format: `DreggV1 em2_<token>,em2_<token>,...`
///
/// Returns `(permission_binary, vec_of_discharge_binaries)`.
pub fn parse_auth_header(header: &str) -> Result<(Vec<u8>, Vec<Vec<u8>>), MacaroonError> {
    let rest = header
        .strip_prefix(AUTH_SCHEME)
        .ok_or_else(|| MacaroonError::Malformed(format!("expected '{AUTH_SCHEME}' scheme")))?
        .trim_start();

    let tokens: Vec<&str> = rest.split(',').map(|t| t.trim()).collect();
    if tokens.is_empty() {
        return Err(MacaroonError::Malformed("no tokens in header".into()));
    }

    let permission = decode_token(tokens[0])?;
    let discharges = tokens[1..]
        .iter()
        .map(|t| decode_token(t))
        .collect::<Result<Vec<_>, _>>()?;

    Ok((permission, discharges))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_decode_roundtrip() {
        let data = vec![0x01, 0x02, 0x03, 0xff, 0xfe];
        let encoded = encode_token(&data);
        assert!(encoded.starts_with("em2_"));
        let decoded = decode_token(&encoded).unwrap();
        assert_eq!(data, decoded);
    }

    #[test]
    fn test_decode_missing_prefix() {
        assert!(decode_token("invalid_base64").is_err());
    }

    #[test]
    fn test_auth_header_roundtrip() {
        let perm = vec![0x01, 0x02];
        let d1 = vec![0x03, 0x04];
        let d2 = vec![0x05, 0x06];

        let header = format_auth_header(&perm, &[d1.clone(), d2.clone()]);
        assert!(header.starts_with("DreggV1 em2_"));

        let (parsed_perm, parsed_discharges) = parse_auth_header(&header).unwrap();
        assert_eq!(perm, parsed_perm);
        assert_eq!(parsed_discharges.len(), 2);
        assert_eq!(d1, parsed_discharges[0]);
        assert_eq!(d2, parsed_discharges[1]);
    }
}
