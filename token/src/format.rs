//! Token format detection and wire encoding.

use crate::error::TokenError;

/// Supported token formats.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum TokenFormat {
    /// HMAC-SHA256 chained macaroon (symmetric, ~0.5μs verify).
    Macaroon,
    /// Ed25519/P-256 Biscuit with Datalog authorization (asymmetric, ~50-80μs verify).
    Biscuit,
}

impl TokenFormat {
    /// Wire prefix for encoded tokens.
    pub fn prefix(&self) -> &'static str {
        match self {
            TokenFormat::Macaroon => "em2_",
            TokenFormat::Biscuit => "eb2_",
        }
    }

    /// Detect format from an encoded token string.
    pub fn detect(encoded: &str) -> Result<TokenFormat, TokenError> {
        if encoded.starts_with("em2_") {
            Ok(TokenFormat::Macaroon)
        } else if encoded.starts_with("eb2_") || encoded.starts_with("biscuit:") {
            Ok(TokenFormat::Biscuit)
        } else {
            Err(TokenError::Malformed(
                "unrecognized token prefix (expected em2_ or eb2_)".into(),
            ))
        }
    }

    /// Detect format from raw bytes (for binary-encoded tokens).
    ///
    /// Macaroon tokens start with MsgPack array marker.
    /// Biscuit tokens start with Protobuf varint patterns.
    ///
    /// Returns `UnrecognizedFormat` if the data does not match either format's
    /// expected byte patterns, rather than defaulting to any format.
    pub fn detect_bytes(data: &[u8]) -> Result<TokenFormat, TokenError> {
        if data.is_empty() {
            return Err(TokenError::Malformed("empty token".into()));
        }
        // MsgPack fixarray or array16/array32 markers (macaroon)
        if (data[0] & 0xf0) == 0x90 || data[0] == 0xdc || data[0] == 0xdd {
            return Ok(TokenFormat::Macaroon);
        }
        // Biscuit uses protobuf encoding. Valid protobuf messages start with a
        // field tag (varint). Field 1 with wire type 2 (length-delimited) = 0x0a.
        // Field 1 with wire type 0 (varint) = 0x08. Field 2 with wire type 2 = 0x12.
        // These cover the known Biscuit serialization patterns.
        if data[0] == 0x0a || data[0] == 0x08 || data[0] == 0x12 {
            return Ok(TokenFormat::Biscuit);
        }
        // Also accept the Biscuit v2 format which may start with version byte 2
        if data.len() >= 2 && data[0] == 0x02 {
            return Ok(TokenFormat::Biscuit);
        }
        Err(TokenError::UnrecognizedFormat)
    }
}

impl std::fmt::Display for TokenFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenFormat::Macaroon => write!(f, "macaroon"),
            TokenFormat::Biscuit => write!(f, "biscuit"),
        }
    }
}

impl std::str::FromStr for TokenFormat {
    type Err = TokenError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "macaroon" | "mac" => Ok(TokenFormat::Macaroon),
            "biscuit" | "bisc" => Ok(TokenFormat::Biscuit),
            _ => Err(TokenError::UnsupportedFormat(s.to_string())),
        }
    }
}

/// Authorization header scheme.
pub const AUTH_HEADER_SCHEME: &str = "DreggV1";

/// Format tokens for an Authorization header.
///
/// `DreggV1 <token>[,<discharge>...]`
pub fn format_auth_header(tokens: &[&str]) -> String {
    format!("{} {}", AUTH_HEADER_SCHEME, tokens.join(","))
}

/// Parse tokens from an Authorization header.
pub fn parse_auth_header(header: &str) -> Result<Vec<String>, TokenError> {
    let stripped = header
        .strip_prefix(AUTH_HEADER_SCHEME)
        .ok_or_else(|| TokenError::Malformed("missing DreggV1 scheme".into()))?
        .trim_start();
    Ok(stripped
        .split(',')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_macaroon() {
        assert_eq!(
            TokenFormat::detect("em2_abc123").unwrap(),
            TokenFormat::Macaroon
        );
    }

    #[test]
    fn test_detect_biscuit() {
        assert_eq!(
            TokenFormat::detect("eb2_abc123").unwrap(),
            TokenFormat::Biscuit
        );
        assert_eq!(
            TokenFormat::detect("biscuit:abc123").unwrap(),
            TokenFormat::Biscuit
        );
    }

    #[test]
    fn test_detect_unknown() {
        assert!(TokenFormat::detect("xyz_abc").is_err());
    }

    #[test]
    fn test_parse_str() {
        assert_eq!(
            "macaroon".parse::<TokenFormat>().unwrap(),
            TokenFormat::Macaroon
        );
        assert_eq!(
            "biscuit".parse::<TokenFormat>().unwrap(),
            TokenFormat::Biscuit
        );
    }

    #[test]
    fn test_auth_header_roundtrip() {
        let header = format_auth_header(&["em2_token1", "em2_discharge1"]);
        let parsed = parse_auth_header(&header).unwrap();
        assert_eq!(parsed, vec!["em2_token1", "em2_discharge1"]);
    }

    // Security tests

    #[test]
    fn test_detect_bytes_rejects_unrecognized_data() {
        // Random garbage data should NOT default to Biscuit.
        // Previously any unrecognized data was assumed to be Biscuit format.
        let garbage = &[0xFF, 0xFE, 0xFD, 0xFC, 0x00];
        let result = TokenFormat::detect_bytes(garbage);
        assert!(
            result.is_err(),
            "random garbage must not be accepted as any token format"
        );

        // More garbage patterns that are not valid MsgPack or Protobuf
        let not_msgpack_not_proto = &[0x50, 0x4E, 0x47]; // "PNG" header bytes
        let result = TokenFormat::detect_bytes(not_msgpack_not_proto);
        assert!(
            result.is_err(),
            "PNG-like data must not be accepted as a token format"
        );

        // Null-filled data
        let nulls = &[0x00, 0x00, 0x00, 0x00];
        let result = TokenFormat::detect_bytes(nulls);
        assert!(
            result.is_err(),
            "null data must not be accepted as a token format"
        );
    }

    #[test]
    fn test_detect_bytes_accepts_valid_macaroon_patterns() {
        // MsgPack fixarray (0x90-0x9f)
        let msgpack_fixarray = &[0x93, 0x01, 0x02];
        assert_eq!(
            TokenFormat::detect_bytes(msgpack_fixarray).unwrap(),
            TokenFormat::Macaroon
        );

        // MsgPack array16
        let msgpack_array16 = &[0xdc, 0x00, 0x10];
        assert_eq!(
            TokenFormat::detect_bytes(msgpack_array16).unwrap(),
            TokenFormat::Macaroon
        );
    }

    #[test]
    fn test_detect_bytes_accepts_valid_biscuit_patterns() {
        // Protobuf field 1, wire type 2 (length-delimited)
        let proto_field1_len = &[0x0a, 0x05, 0x01, 0x02, 0x03];
        assert_eq!(
            TokenFormat::detect_bytes(proto_field1_len).unwrap(),
            TokenFormat::Biscuit
        );

        // Protobuf field 1, wire type 0 (varint)
        let proto_field1_varint = &[0x08, 0x01];
        assert_eq!(
            TokenFormat::detect_bytes(proto_field1_varint).unwrap(),
            TokenFormat::Biscuit
        );
    }
}
