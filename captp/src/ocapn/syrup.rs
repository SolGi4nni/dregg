//! # Syrup — OCapN's canonical serialization format.
//!
//! [Syrup](https://github.com/ocapn/syrup) is the wire serialization used by
//! OCapN (Spritely Goblins' object-capability network). Where dregg's silo
//! framing uses postcard, an OCapN peer speaks Syrup: every `op:start-session`
//! / `op:deliver` / `desc:export` is a Syrup **record**. This module is the
//! self-contained codec — the first concrete artifact of the Goblins-interop
//! adapter sketched in [`crate::netlayer`] (module docs, §"Goblins-interop
//! adapter").
//!
//! ## The grammar
//!
//! Syrup is a binary format with ASCII-ish type tags. A value is one of:
//!
//! | Type          | Wire form                                   |
//! |---------------|---------------------------------------------|
//! | Boolean       | `t` (true) / `f` (false)                    |
//! | Integer       | `<decimal>+` (≥ 0) or `<decimal>-` (< 0)    |
//! | Float64       | `D` followed by 8 bytes IEEE-754 big-endian |
//! | Bytestring    | `<len>:` followed by `len` raw bytes        |
//! | String (UTF-8)| `<len>"` followed by `len` UTF-8 bytes      |
//! | Symbol        | `<len>'` followed by `len` UTF-8 bytes      |
//! | List          | `[` items… `]`                              |
//! | Dictionary    | `{` (key value)… `}` (keys sorted)          |
//! | Set           | `#` items… `$` (items sorted)               |
//! | Record        | `<` label field… `>`                        |
//!
//! The integer `<decimal>` is the magnitude written in base-10 ASCII with no
//! leading zeros (except `0` itself, encoded `0+`). Lengths are likewise
//! base-10 ASCII.
//!
//! ## Canonical form
//!
//! Syrup is a *canonical* encoding: a given value has exactly one byte
//! representation, so two peers that encode equal values produce equal bytes
//! (this is what lets OCapN hash/sign Syrup directly). This codec enforces
//! canonicality on the **decode** side too, which is where it matters for an
//! adversarial peer:
//!
//! - **Dictionary keys are emitted in ascending order** of their *encoded
//!   bytes*, and decoding **rejects** keys that are out of order or duplicated
//!   ([`SyrupError::NonCanonicalDict`]). A peer cannot smuggle ambiguity past
//!   a canonical decoder.
//! - **Set members** are likewise emitted sorted and decoding rejects
//!   out-of-order / duplicate members ([`SyrupError::NonCanonicalSet`]).
//! - **Integers reject leading zeros** (`00+`, `01+` are malformed); `0` is
//!   `0+` and negative zero (`0-`) is rejected.
//! - **Strings/symbols reject invalid UTF-8**; lengths that run past the end
//!   of the input are rejected rather than read out of bounds.
//!
//! ## Integer range
//!
//! Syrup integers are arbitrary-precision bignums. This codec carries them in
//! [`i128`], which covers every integer OCapN actually places on the wire
//! (positions, versions, refcounts, sequence numbers). An on-wire integer
//! whose magnitude exceeds [`i128`] is **rejected** ([`SyrupError::IntOverflow`])
//! rather than silently truncated — an honest boundary, not a wrong answer.
//! (Lifting to true bignums is a localized change to the [`Value::Int`] payload
//! and the two integer codec sites; it does not touch the grammar.)

use std::collections::BTreeMap;
use std::fmt;

// =============================================================================
// The value model
// =============================================================================

/// A decoded Syrup value. Construct with the helpers ([`Value::int`],
/// [`Value::string`], [`Value::record`], …) or the variants directly, then
/// [`encode`](Value::encode) to bytes; [`decode`](Value::decode) parses bytes
/// back.
///
/// Dictionary keys and set members are themselves arbitrary [`Value`]s; the
/// canonical sort orders them by their encoded bytes. `Dict` and `Set` use a
/// [`BTreeMap`]/sorted vector keyed by the *encoding* so equal-valued keys
/// collapse and ordering is intrinsic.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    /// `t` / `f`.
    Bool(bool),
    /// A signed integer (see the module docs on range).
    Int(i128),
    /// A 64-bit IEEE-754 float (`D` + 8 BE bytes).
    Float(f64),
    /// A bytestring (`<len>:` + bytes) — opaque binary.
    Bytes(Vec<u8>),
    /// A UTF-8 string (`<len>"` + bytes).
    Str(String),
    /// A symbol (`<len>'` + bytes) — an interned identifier (method names,
    /// record labels-as-values, …).
    Symbol(String),
    /// A list (`[` … `]`), heterogeneous and ordered.
    List(Vec<Value>),
    /// A dictionary (`{` … `}`): canonical key→value, keys sorted by encoding.
    Dict(Dict),
    /// A set (`#` … `$`): canonical, members sorted by encoding.
    Set(Set),
    /// A record (`<` label field… `>`): a tagged tuple. OCapN messages
    /// (`op:deliver`, `desc:export`, …) are records whose label is a symbol.
    Record {
        /// The record label (typically a [`Value::Symbol`]).
        label: Box<Value>,
        /// The positional fields.
        fields: Vec<Value>,
    },
}

/// A canonical Syrup dictionary: keys ordered by their encoded bytes.
///
/// Keyed internally by the encoded key bytes so insertion is idempotent on
/// equal keys and iteration is always in canonical order — the same order the
/// encoder emits and the decoder requires.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Dict {
    /// encoded-key-bytes → (key value, value)
    entries: BTreeMap<Vec<u8>, (Value, Value)>,
}

impl Dict {
    /// An empty dictionary.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert/replace `key → value`. Returns the previous value, if any.
    pub fn insert(&mut self, key: Value, value: Value) -> Option<Value> {
        let k = key.encode();
        self.entries.insert(k, (key, value)).map(|(_, v)| v)
    }

    /// Look up by key value.
    pub fn get(&self, key: &Value) -> Option<&Value> {
        self.entries.get(&key.encode()).map(|(_, v)| v)
    }

    /// Number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the dictionary is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate `(key, value)` in canonical (encoded-bytes-ascending) order.
    pub fn iter(&self) -> impl Iterator<Item = (&Value, &Value)> {
        self.entries.values().map(|(k, v)| (k, v))
    }
}

impl FromIterator<(Value, Value)> for Dict {
    fn from_iter<T: IntoIterator<Item = (Value, Value)>>(iter: T) -> Self {
        let mut d = Dict::new();
        for (k, v) in iter {
            d.insert(k, v);
        }
        d
    }
}

/// A canonical Syrup set: members ordered by their encoded bytes.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Set {
    /// encoded-member-bytes → member value
    members: BTreeMap<Vec<u8>, Value>,
}

impl Set {
    /// An empty set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a member. Returns `true` if newly added.
    pub fn insert(&mut self, value: Value) -> bool {
        self.members.insert(value.encode(), value).is_none()
    }

    /// Whether `value` is a member.
    pub fn contains(&self, value: &Value) -> bool {
        self.members.contains_key(&value.encode())
    }

    /// Number of members.
    pub fn len(&self) -> usize {
        self.members.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    /// Iterate members in canonical (encoded-bytes-ascending) order.
    pub fn iter(&self) -> impl Iterator<Item = &Value> {
        self.members.values()
    }
}

impl FromIterator<Value> for Set {
    fn from_iter<T: IntoIterator<Item = Value>>(iter: T) -> Self {
        let mut s = Set::new();
        for v in iter {
            s.insert(v);
        }
        s
    }
}

// =============================================================================
// Constructors (ergonomic builders for the OCapN message layer)
// =============================================================================

impl Value {
    /// A boolean.
    pub fn bool(b: bool) -> Value {
        Value::Bool(b)
    }

    /// An integer.
    pub fn int(n: impl Into<i128>) -> Value {
        Value::Int(n.into())
    }

    /// A float.
    pub fn float(x: f64) -> Value {
        Value::Float(x)
    }

    /// A bytestring.
    pub fn bytes(b: impl Into<Vec<u8>>) -> Value {
        Value::Bytes(b.into())
    }

    /// A UTF-8 string.
    pub fn string(s: impl Into<String>) -> Value {
        Value::Str(s.into())
    }

    /// A symbol.
    pub fn symbol(s: impl Into<String>) -> Value {
        Value::Symbol(s.into())
    }

    /// A list from an iterator of values.
    pub fn list(items: impl IntoIterator<Item = Value>) -> Value {
        Value::List(items.into_iter().collect())
    }

    /// A dictionary from `(key, value)` pairs (canonicalized on build).
    pub fn dict(pairs: impl IntoIterator<Item = (Value, Value)>) -> Value {
        Value::Dict(pairs.into_iter().collect())
    }

    /// A set from members (canonicalized on build).
    pub fn set(items: impl IntoIterator<Item = Value>) -> Value {
        Value::Set(items.into_iter().collect())
    }

    /// A record with a **symbol** label (the OCapN message shape:
    /// `<op:deliver …>`) and the given positional fields.
    pub fn record(label: impl Into<String>, fields: impl IntoIterator<Item = Value>) -> Value {
        Value::Record {
            label: Box::new(Value::Symbol(label.into())),
            fields: fields.into_iter().collect(),
        }
    }

    /// A record with an arbitrary-value label.
    pub fn record_with_label(label: Value, fields: impl IntoIterator<Item = Value>) -> Value {
        Value::Record {
            label: Box::new(label),
            fields: fields.into_iter().collect(),
        }
    }
}

// =============================================================================
// Errors
// =============================================================================

/// Errors raised while decoding Syrup. Encoding is total (cannot fail).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SyrupError {
    /// The input ended before a complete value was read.
    UnexpectedEof {
        /// What the decoder was trying to read when input ran out.
        wanted: &'static str,
    },
    /// A type tag byte was not a recognized Syrup tag.
    UnknownTag {
        /// The offending byte.
        tag: u8,
        /// Byte offset in the input.
        at: usize,
    },
    /// An integer or length had no digits, a `+`/`-` sign was missing, or it
    /// carried a forbidden leading zero / negative-zero form.
    MalformedInteger {
        /// Byte offset where the number started.
        at: usize,
    },
    /// An on-wire integer magnitude does not fit in [`i128`] (see module docs).
    IntOverflow {
        /// Byte offset where the number started.
        at: usize,
    },
    /// A declared length would run past the end of the input.
    LengthOverflow {
        /// The declared length.
        len: usize,
        /// Bytes actually remaining.
        remaining: usize,
        /// Byte offset where the length was declared.
        at: usize,
    },
    /// A string or symbol's bytes were not valid UTF-8.
    InvalidUtf8 {
        /// Byte offset where the string body started.
        at: usize,
    },
    /// A float tag `D` was not followed by 8 bytes.
    MalformedFloat {
        /// Byte offset of the `D`.
        at: usize,
    },
    /// Dictionary keys were not strictly ascending by encoded bytes (out of
    /// order or duplicated) — a non-canonical encoding.
    NonCanonicalDict {
        /// Byte offset of the offending key.
        at: usize,
    },
    /// Set members were not strictly ascending by encoded bytes — a
    /// non-canonical encoding.
    NonCanonicalSet {
        /// Byte offset of the offending member.
        at: usize,
    },
    /// A value was nested more deeply than the decoder's supported limit.
    NestingTooDeep {
        /// Maximum supported nesting depth.
        max: usize,
        /// Byte offset of the value that exceeded the limit.
        at: usize,
    },
    /// Decoding consumed a complete value but left trailing bytes (only
    /// raised by [`Value::decode`], which requires the whole input).
    TrailingBytes {
        /// Number of unconsumed bytes.
        remaining: usize,
    },
}

impl fmt::Display for SyrupError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SyrupError::UnexpectedEof { wanted } => {
                write!(f, "unexpected end of input while reading {wanted}")
            }
            SyrupError::UnknownTag { tag, at } => {
                write!(f, "unknown Syrup tag byte {tag:#04x} at offset {at}")
            }
            SyrupError::MalformedInteger { at } => {
                write!(f, "malformed integer/length at offset {at}")
            }
            SyrupError::IntOverflow { at } => {
                write!(f, "integer at offset {at} exceeds i128 range")
            }
            SyrupError::LengthOverflow { len, remaining, at } => write!(
                f,
                "declared length {len} at offset {at} exceeds {remaining} remaining bytes"
            ),
            SyrupError::InvalidUtf8 { at } => {
                write!(f, "invalid UTF-8 in string/symbol at offset {at}")
            }
            SyrupError::MalformedFloat { at } => {
                write!(f, "float tag 'D' at offset {at} not followed by 8 bytes")
            }
            SyrupError::NonCanonicalDict { at } => {
                write!(
                    f,
                    "non-canonical dictionary (key out of order / duplicate) at offset {at}"
                )
            }
            SyrupError::NonCanonicalSet { at } => {
                write!(
                    f,
                    "non-canonical set (member out of order / duplicate) at offset {at}"
                )
            }
            SyrupError::NestingTooDeep { max, at } => {
                write!(
                    f,
                    "Syrup nesting exceeds maximum depth {max} at offset {at}"
                )
            }
            SyrupError::TrailingBytes { remaining } => {
                write!(f, "{remaining} trailing bytes after a complete value")
            }
        }
    }
}

impl std::error::Error for SyrupError {}

// =============================================================================
// Encoding (total)
// =============================================================================

impl Value {
    /// Encode this value to canonical Syrup bytes.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        self.encode_into(&mut out);
        out
    }

    /// Append the canonical Syrup encoding of this value to `out`.
    pub fn encode_into(&self, out: &mut Vec<u8>) {
        match self {
            Value::Bool(true) => out.push(b't'),
            Value::Bool(false) => out.push(b'f'),
            Value::Int(n) => encode_int(*n, out),
            Value::Float(x) => {
                out.push(b'D');
                out.extend_from_slice(&x.to_be_bytes());
            }
            Value::Bytes(b) => encode_len_prefixed(b, b':', out),
            Value::Str(s) => encode_len_prefixed(s.as_bytes(), b'"', out),
            Value::Symbol(s) => encode_len_prefixed(s.as_bytes(), b'\'', out),
            Value::List(items) => {
                out.push(b'[');
                for item in items {
                    item.encode_into(out);
                }
                out.push(b']');
            }
            Value::Dict(d) => {
                out.push(b'{');
                // BTreeMap iteration is already encoded-bytes-ascending: that
                // is exactly Syrup's canonical key order.
                for (k, v) in d.iter() {
                    k.encode_into(out);
                    v.encode_into(out);
                }
                out.push(b'}');
            }
            Value::Set(s) => {
                out.push(b'#');
                for m in s.iter() {
                    m.encode_into(out);
                }
                out.push(b'$');
            }
            Value::Record { label, fields } => {
                out.push(b'<');
                label.encode_into(out);
                for fld in fields {
                    fld.encode_into(out);
                }
                out.push(b'>');
            }
        }
    }
}

/// Encode an integer: magnitude in base-10 ASCII, then `+` (≥0) or `-` (<0).
fn encode_int(n: i128, out: &mut Vec<u8>) {
    // Use the unsigned magnitude so i128::MIN is representable (its negation
    // overflows i128, but `unsigned_abs` gives the correct u128 magnitude).
    let sign = if n < 0 { b'-' } else { b'+' };
    let mag = n.unsigned_abs();
    push_decimal_u128(mag, out);
    out.push(sign);
}

/// Encode a length-prefixed body: `<len>` in base-10 ASCII, the `tag`, body.
fn encode_len_prefixed(body: &[u8], tag: u8, out: &mut Vec<u8>) {
    push_decimal_usize(body.len(), out);
    out.push(tag);
    out.extend_from_slice(body);
}

/// Push the base-10 ASCII of a `usize` (no leading zeros; `0` → `"0"`).
fn push_decimal_usize(mut n: usize, out: &mut Vec<u8>) {
    if n == 0 {
        out.push(b'0');
        return;
    }
    let start = out.len();
    while n > 0 {
        out.push(b'0' + (n % 10) as u8);
        n /= 10;
    }
    out[start..].reverse();
}

/// Push the base-10 ASCII of a `u128` (no leading zeros; `0` → `"0"`).
fn push_decimal_u128(mut n: u128, out: &mut Vec<u8>) {
    if n == 0 {
        out.push(b'0');
        return;
    }
    let start = out.len();
    while n > 0 {
        out.push(b'0' + (n % 10) as u8);
        n /= 10;
    }
    out[start..].reverse();
}

// =============================================================================
// Decoding
// =============================================================================

impl Value {
    /// Decode exactly one Syrup value from `input`, requiring that it consumes
    /// the **entire** slice ([`SyrupError::TrailingBytes`] otherwise).
    pub fn decode(input: &[u8]) -> Result<Value, SyrupError> {
        let mut d = Decoder::new(input);
        let v = d.value()?;
        if d.pos != input.len() {
            return Err(SyrupError::TrailingBytes {
                remaining: input.len() - d.pos,
            });
        }
        Ok(v)
    }

    /// Decode one Syrup value from the front of `input`, returning the value
    /// and the number of bytes consumed. Trailing bytes are *allowed* (use
    /// this for streaming / framed decode); [`decode`](Value::decode) wraps
    /// this and forbids them.
    pub fn decode_prefix(input: &[u8]) -> Result<(Value, usize), SyrupError> {
        let mut d = Decoder::new(input);
        let v = d.value()?;
        Ok((v, d.pos))
    }
}

/// A single-pass Syrup decoder over a byte slice.
struct Decoder<'a> {
    buf: &'a [u8],
    pos: usize,
}

/// Maximum number of nested Syrup container levels accepted by the decoder.
pub const MAX_DECODE_DEPTH: usize = 256;

impl<'a> Decoder<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Decoder { buf, pos: 0 }
    }

    /// Peek the next byte without consuming.
    fn peek(&self) -> Option<u8> {
        self.buf.get(self.pos).copied()
    }

    /// Consume and return the next byte.
    fn next_byte(&mut self, wanted: &'static str) -> Result<u8, SyrupError> {
        let b = self
            .buf
            .get(self.pos)
            .copied()
            .ok_or(SyrupError::UnexpectedEof { wanted })?;
        self.pos += 1;
        Ok(b)
    }

    /// Take `n` bytes, bounds-checked.
    fn take(&mut self, n: usize, at: usize) -> Result<&'a [u8], SyrupError> {
        let remaining = self.buf.len() - self.pos;
        if n > remaining {
            return Err(SyrupError::LengthOverflow {
                len: n,
                remaining,
                at,
            });
        }
        let slice = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(slice)
    }

    /// Decode one value, dispatching on the leading tag.
    fn value(&mut self) -> Result<Value, SyrupError> {
        self.value_at_depth(0)
    }

    fn value_at_depth(&mut self, depth: usize) -> Result<Value, SyrupError> {
        if depth > MAX_DECODE_DEPTH {
            return Err(SyrupError::NestingTooDeep {
                max: MAX_DECODE_DEPTH,
                at: self.pos,
            });
        }
        let tag = self
            .peek()
            .ok_or(SyrupError::UnexpectedEof { wanted: "value" })?;
        match tag {
            b't' => {
                self.pos += 1;
                Ok(Value::Bool(true))
            }
            b'f' => {
                self.pos += 1;
                Ok(Value::Bool(false))
            }
            b'D' => self.float(),
            b'[' => self.list(depth),
            b'{' => self.dict(depth),
            b'#' => self.set(depth),
            b'<' => self.record(depth),
            // A leading ASCII digit begins an integer OR a length-prefixed
            // bytestring/string/symbol; the terminator byte disambiguates.
            b'0'..=b'9' => self.number_led(),
            other => Err(SyrupError::UnknownTag {
                tag: other,
                at: self.pos,
            }),
        }
    }

    /// Decode a `D`-tagged float (8 big-endian bytes).
    fn float(&mut self) -> Result<Value, SyrupError> {
        let at = self.pos;
        self.pos += 1; // consume 'D'
        let remaining = self.buf.len() - self.pos;
        if remaining < 8 {
            return Err(SyrupError::MalformedFloat { at });
        }
        let bytes: [u8; 8] = self.buf[self.pos..self.pos + 8].try_into().unwrap();
        self.pos += 8;
        Ok(Value::Float(f64::from_be_bytes(bytes)))
    }

    /// Decode a digit-led token: read the base-10 run, then the terminator
    /// selects integer (`+`/`-`) vs length-prefixed body (`:`/`"`/`'`).
    fn number_led(&mut self) -> Result<Value, SyrupError> {
        let at = self.pos;
        // Scan the digit run.
        let digit_start = self.pos;
        while let Some(b) = self.peek() {
            if b.is_ascii_digit() {
                self.pos += 1;
            } else {
                break;
            }
        }
        let digits = &self.buf[digit_start..self.pos];
        // There must be a terminator byte.
        let term = self.next_byte("integer/length terminator")?;
        match term {
            b'+' | b'-' => {
                // Parse the unsigned magnitude, then place the sign. Doing the
                // range check against the *signed* target per-sign is what lets
                // i128::MIN decode: its magnitude is 2^127 = i128::MAX + 1, in
                // range for `-` but not for `+`.
                let mag = parse_decimal_magnitude(digits, at)?;
                let signed = if term == b'-' {
                    // Reject negative zero (`0-`): non-canonical.
                    if mag == 0 {
                        return Err(SyrupError::MalformedInteger { at });
                    }
                    // i128::MIN == -(2^127); represent it via wrapping_neg on the
                    // i128 bit pattern of 2^127 (which is i128::MIN itself). For
                    // every other in-range magnitude this is the ordinary
                    // negation; magnitudes above 2^127 are rejected.
                    if mag > (i128::MAX as u128) + 1 {
                        return Err(SyrupError::IntOverflow { at });
                    }
                    (mag as i128).wrapping_neg()
                } else {
                    if mag > i128::MAX as u128 {
                        return Err(SyrupError::IntOverflow { at });
                    }
                    mag as i128
                };
                Ok(Value::Int(signed))
            }
            b':' | b'"' | b'\'' => {
                let len = parse_decimal_usize(digits, at)?;
                let body = self.take(len, at)?;
                match term {
                    b':' => Ok(Value::Bytes(body.to_vec())),
                    b'"' => {
                        let s = std::str::from_utf8(body)
                            .map_err(|_| SyrupError::InvalidUtf8 { at })?;
                        Ok(Value::Str(s.to_string()))
                    }
                    _ => {
                        let s = std::str::from_utf8(body)
                            .map_err(|_| SyrupError::InvalidUtf8 { at })?;
                        Ok(Value::Symbol(s.to_string()))
                    }
                }
            }
            _ => Err(SyrupError::MalformedInteger { at }),
        }
    }

    /// Decode a `[` … `]` list.
    fn list(&mut self, depth: usize) -> Result<Value, SyrupError> {
        self.pos += 1; // consume '['
        let mut items = Vec::new();
        loop {
            match self.peek() {
                Some(b']') => {
                    self.pos += 1;
                    return Ok(Value::List(items));
                }
                Some(_) => items.push(self.value_at_depth(depth + 1)?),
                None => {
                    return Err(SyrupError::UnexpectedEof {
                        wanted: "list item or ']'",
                    });
                }
            }
        }
    }

    /// Decode a `{` … `}` dictionary, enforcing strictly-ascending keys.
    fn dict(&mut self, depth: usize) -> Result<Value, SyrupError> {
        self.pos += 1; // consume '{'
        let mut entries: BTreeMap<Vec<u8>, (Value, Value)> = BTreeMap::new();
        let mut prev_key: Option<Vec<u8>> = None;
        loop {
            match self.peek() {
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(Value::Dict(Dict { entries }));
                }
                Some(_) => {
                    let key_at = self.pos;
                    let key = self.value_at_depth(depth + 1)?;
                    let key_enc = key.encode();
                    // Canonical: keys strictly ascending by encoded bytes.
                    if let Some(prev) = &prev_key
                        && key_enc <= *prev
                    {
                        return Err(SyrupError::NonCanonicalDict { at: key_at });
                    }
                    let value = self.value_at_depth(depth + 1)?;
                    prev_key = Some(key_enc.clone());
                    entries.insert(key_enc, (key, value));
                }
                None => {
                    return Err(SyrupError::UnexpectedEof {
                        wanted: "dict key or '}'",
                    });
                }
            }
        }
    }

    /// Decode a `#` … `$` set, enforcing strictly-ascending members.
    fn set(&mut self, depth: usize) -> Result<Value, SyrupError> {
        self.pos += 1; // consume '#'
        let mut members: BTreeMap<Vec<u8>, Value> = BTreeMap::new();
        let mut prev: Option<Vec<u8>> = None;
        loop {
            match self.peek() {
                Some(b'$') => {
                    self.pos += 1;
                    return Ok(Value::Set(Set { members }));
                }
                Some(_) => {
                    let at = self.pos;
                    let m = self.value_at_depth(depth + 1)?;
                    let enc = m.encode();
                    if let Some(p) = &prev
                        && enc <= *p
                    {
                        return Err(SyrupError::NonCanonicalSet { at });
                    }
                    prev = Some(enc.clone());
                    members.insert(enc, m);
                }
                None => {
                    return Err(SyrupError::UnexpectedEof {
                        wanted: "set member or '$'",
                    });
                }
            }
        }
    }

    /// Decode a `<` label field… `>` record.
    fn record(&mut self, depth: usize) -> Result<Value, SyrupError> {
        self.pos += 1; // consume '<'
        // A record must have at least a label.
        if self.peek() == Some(b'>') {
            return Err(SyrupError::UnexpectedEof {
                wanted: "record label",
            });
        }
        let label = Box::new(self.value_at_depth(depth + 1)?);
        let mut fields = Vec::new();
        loop {
            match self.peek() {
                Some(b'>') => {
                    self.pos += 1;
                    return Ok(Value::Record { label, fields });
                }
                Some(_) => fields.push(self.value_at_depth(depth + 1)?),
                None => {
                    return Err(SyrupError::UnexpectedEof {
                        wanted: "record field or '>'",
                    });
                }
            }
        }
    }
}

/// Parse a base-10 digit slice into an unsigned magnitude (`u128`), rejecting
/// empty input, leading zeros, and `u128` overflow. The caller applies the sign
/// and the signed-range check — splitting magnitude from sign is what lets
/// `i128::MIN` (magnitude `2^127`, one past `i128::MAX`) decode losslessly.
fn parse_decimal_magnitude(digits: &[u8], at: usize) -> Result<u128, SyrupError> {
    if digits.is_empty() {
        return Err(SyrupError::MalformedInteger { at });
    }
    // Reject leading zeros: "0" is the only representation starting with '0'.
    if digits.len() > 1 && digits[0] == b'0' {
        return Err(SyrupError::MalformedInteger { at });
    }
    let mut acc: u128 = 0;
    for &b in digits {
        // (digit-run was already validated as ASCII digits by the scanner, but
        // re-check defensively so this helper is correct in isolation.)
        if !b.is_ascii_digit() {
            return Err(SyrupError::MalformedInteger { at });
        }
        let d = (b - b'0') as u128;
        acc = acc
            .checked_mul(10)
            .and_then(|a| a.checked_add(d))
            .ok_or(SyrupError::IntOverflow { at })?;
    }
    Ok(acc)
}

/// Parse a base-10 digit slice into a `usize` length, rejecting empty input,
/// leading zeros, and overflow.
fn parse_decimal_usize(digits: &[u8], at: usize) -> Result<usize, SyrupError> {
    if digits.is_empty() {
        return Err(SyrupError::MalformedInteger { at });
    }
    if digits.len() > 1 && digits[0] == b'0' {
        return Err(SyrupError::MalformedInteger { at });
    }
    let mut acc: usize = 0;
    for &b in digits {
        if !b.is_ascii_digit() {
            return Err(SyrupError::MalformedInteger { at });
        }
        let d = (b - b'0') as usize;
        acc = acc
            .checked_mul(10)
            .and_then(|a| a.checked_add(d))
            .ok_or(SyrupError::IntOverflow { at })?;
    }
    Ok(acc)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Encode → decode is the identity for every value family.
    fn assert_roundtrip(v: Value) {
        let bytes = v.encode();
        let back = Value::decode(&bytes)
            .unwrap_or_else(|e| panic!("decode failed for {v:?}: {e} (bytes: {bytes:?})"));
        assert_eq!(back, v, "roundtrip mismatch (bytes: {bytes:?})");
    }

    // -------------------------------------------------------------------
    // Exact wire bytes (pins the format against the spec, not just self-
    // consistency).
    // -------------------------------------------------------------------

    #[test]
    fn wire_bytes_booleans() {
        assert_eq!(Value::Bool(true).encode(), b"t");
        assert_eq!(Value::Bool(false).encode(), b"f");
    }

    #[test]
    fn wire_bytes_integers() {
        assert_eq!(Value::int(0).encode(), b"0+");
        assert_eq!(Value::int(42).encode(), b"42+");
        assert_eq!(Value::int(-7).encode(), b"7-");
        assert_eq!(Value::int(1000000).encode(), b"1000000+");
    }

    #[test]
    fn wire_bytes_bytestring() {
        assert_eq!(Value::bytes(b"abc".to_vec()).encode(), b"3:abc");
        assert_eq!(Value::bytes(Vec::new()).encode(), b"0:");
    }

    #[test]
    fn wire_bytes_string_and_symbol() {
        assert_eq!(Value::string("hello").encode(), b"5\"hello");
        assert_eq!(Value::symbol("op:deliver").encode(), b"10'op:deliver");
        // empty
        assert_eq!(Value::string("").encode(), b"0\"");
    }

    #[test]
    fn wire_bytes_float() {
        let mut expected = vec![b'D'];
        expected.extend_from_slice(&1.5f64.to_be_bytes());
        assert_eq!(Value::float(1.5).encode(), expected);
    }

    #[test]
    fn wire_bytes_list() {
        // [t f 1+]  ==  "[" "t" "f" "1+" "]"
        let v = Value::list([Value::Bool(true), Value::Bool(false), Value::int(1)]);
        assert_eq!(v.encode(), b"[tf1+]");
    }

    #[test]
    fn wire_bytes_record() {
        // <op:deliver 3+>  (symbol label + one int field)
        let v = Value::record("op:deliver", [Value::int(3)]);
        assert_eq!(v.encode(), b"<10'op:deliver3+>");
    }

    #[test]
    fn wire_bytes_dict_is_key_sorted() {
        // Insert out of order; the canonical encoding sorts by encoded key.
        // Keys "a" (1'a -> ...) vs "b": symbol encodings compare by their
        // bytes. We use string keys here.
        let mut d = Dict::new();
        d.insert(Value::string("b"), Value::int(2));
        d.insert(Value::string("a"), Value::int(1));
        let v = Value::Dict(d);
        // "a" encodes 1"a , "b" encodes 1"b ; "1\"a" < "1\"b".
        assert_eq!(v.encode(), b"{1\"a1+1\"b2+}");
    }

    #[test]
    fn wire_bytes_set_is_sorted() {
        let s = Value::set([Value::int(3), Value::int(1), Value::int(2)]);
        // ints encode "1+","2+","3+" ; ascending.
        assert_eq!(s.encode(), b"#1+2+3+$");
    }

    // -------------------------------------------------------------------
    // Round trips across the whole value space.
    // -------------------------------------------------------------------

    #[test]
    fn roundtrip_scalars() {
        assert_roundtrip(Value::Bool(true));
        assert_roundtrip(Value::Bool(false));
        assert_roundtrip(Value::int(0));
        assert_roundtrip(Value::int(1));
        assert_roundtrip(Value::int(-1));
        assert_roundtrip(Value::int(i64::MAX as i128));
        assert_roundtrip(Value::int(i64::MIN as i128));
        assert_roundtrip(Value::int(i128::MAX));
        assert_roundtrip(Value::int(i128::MIN));
        assert_roundtrip(Value::float(0.0));
        assert_roundtrip(Value::float(-0.0));
        assert_roundtrip(Value::float(std::f64::consts::PI));
        assert_roundtrip(Value::float(f64::INFINITY));
        assert_roundtrip(Value::float(f64::NEG_INFINITY));
    }

    #[test]
    fn roundtrip_nan_float() {
        // NaN != NaN, so assert_roundtrip's equality check can't be used;
        // check the bit pattern survives instead.
        let bytes = Value::float(f64::NAN).encode();
        match Value::decode(&bytes).unwrap() {
            Value::Float(x) => assert!(x.is_nan()),
            other => panic!("expected float, got {other:?}"),
        }
    }

    #[test]
    fn roundtrip_strings_bytes_symbols() {
        assert_roundtrip(Value::string(""));
        assert_roundtrip(Value::string("hello world"));
        assert_roundtrip(Value::string("unicode: 日本語 ✨ café"));
        assert_roundtrip(Value::bytes(Vec::new()));
        assert_roundtrip(Value::bytes(vec![0u8, 1, 2, 255, 128]));
        // bytestrings can contain Syrup metacharacters without confusing the
        // decoder (length-prefixed, not delimited).
        assert_roundtrip(Value::bytes(b"]}>$ t f 1+".to_vec()));
        assert_roundtrip(Value::symbol("op:start-session"));
        assert_roundtrip(Value::symbol(""));
    }

    #[test]
    fn roundtrip_collections() {
        assert_roundtrip(Value::list([]));
        assert_roundtrip(Value::list([
            Value::int(1),
            Value::string("two"),
            Value::Bool(false),
        ]));
        // Nested.
        assert_roundtrip(Value::list([
            Value::list([Value::int(1), Value::int(2)]),
            Value::dict([(Value::symbol("k"), Value::list([Value::Bool(true)]))]),
        ]));
        assert_roundtrip(Value::dict([]));
        assert_roundtrip(Value::dict([
            (Value::symbol("alpha"), Value::int(1)),
            (Value::symbol("beta"), Value::int(2)),
            (Value::string("gamma"), Value::bytes(vec![9, 9, 9])),
        ]));
        assert_roundtrip(Value::set([]));
        assert_roundtrip(Value::set([
            Value::int(1),
            Value::int(2),
            Value::string("x"),
        ]));
    }

    #[test]
    fn roundtrip_records() {
        // The shape OCapN messages take.
        assert_roundtrip(Value::record("op:deliver", []));
        assert_roundtrip(Value::record(
            "op:deliver",
            [
                Value::int(0),
                Value::list([Value::symbol("greet"), Value::string("hi")]),
                Value::int(1),
            ],
        ));
        // record-in-record
        assert_roundtrip(Value::record(
            "desc:export",
            [Value::record("desc:import-object", [Value::int(5)])],
        ));
    }

    #[test]
    fn roundtrip_deeply_nested() {
        let mut v = Value::int(0);
        for i in 0..50 {
            v = Value::record("wrap", [Value::int(i), v]);
        }
        assert_roundtrip(v);
    }

    // -------------------------------------------------------------------
    // Canonical-form: equal values encode identically; dict/set order is
    // intrinsic regardless of insertion order.
    // -------------------------------------------------------------------

    #[test]
    fn canonical_dict_insertion_order_irrelevant() {
        let a = Value::dict([
            (Value::symbol("z"), Value::int(1)),
            (Value::symbol("a"), Value::int(2)),
            (Value::symbol("m"), Value::int(3)),
        ]);
        let b = Value::dict([
            (Value::symbol("a"), Value::int(2)),
            (Value::symbol("m"), Value::int(3)),
            (Value::symbol("z"), Value::int(1)),
        ]);
        assert_eq!(a.encode(), b.encode());
        assert_eq!(a, b);
    }

    #[test]
    fn canonical_dict_duplicate_key_collapses() {
        // Inserting the same key twice keeps the last value (map semantics).
        let mut d = Dict::new();
        d.insert(Value::symbol("k"), Value::int(1));
        d.insert(Value::symbol("k"), Value::int(2));
        assert_eq!(d.len(), 1);
        assert_eq!(d.get(&Value::symbol("k")), Some(&Value::int(2)));
    }

    #[test]
    fn canonical_set_insertion_order_irrelevant() {
        let a = Value::set([Value::int(5), Value::int(1), Value::int(3)]);
        let b = Value::set([Value::int(1), Value::int(3), Value::int(5)]);
        assert_eq!(a.encode(), b.encode());
        assert_eq!(a, b);
    }

    // -------------------------------------------------------------------
    // Adversarial: malformed inputs must be REJECTED, never panic, never
    // silently mis-decode.
    // -------------------------------------------------------------------

    #[test]
    fn reject_empty_input() {
        assert_eq!(
            Value::decode(b"").unwrap_err(),
            SyrupError::UnexpectedEof { wanted: "value" }
        );
    }

    #[test]
    fn reject_unknown_tag() {
        assert!(matches!(
            Value::decode(b"Z").unwrap_err(),
            SyrupError::UnknownTag { tag: b'Z', at: 0 }
        ));
        // 'D' float tag handled, but a stray '%' is not.
        assert!(matches!(
            Value::decode(b"%").unwrap_err(),
            SyrupError::UnknownTag { tag: b'%', .. }
        ));
    }

    #[test]
    fn reject_integer_leading_zero() {
        // "00+" and "01+" are non-canonical.
        assert!(matches!(
            Value::decode(b"00+").unwrap_err(),
            SyrupError::MalformedInteger { at: 0 }
        ));
        assert!(matches!(
            Value::decode(b"007+").unwrap_err(),
            SyrupError::MalformedInteger { at: 0 }
        ));
    }

    #[test]
    fn reject_negative_zero() {
        assert!(matches!(
            Value::decode(b"0-").unwrap_err(),
            SyrupError::MalformedInteger { at: 0 }
        ));
    }

    #[test]
    fn reject_integer_no_sign() {
        // A bare digit run with no terminator runs to EOF.
        assert!(matches!(
            Value::decode(b"42").unwrap_err(),
            SyrupError::UnexpectedEof { .. }
        ));
    }

    #[test]
    fn reject_integer_overflow() {
        // i128::MAX is 170141183460469231731687303715884105727; one more digit
        // (or +1) overflows the positive range.
        let too_big = b"1701411834604692317316873037158841057280+"; // MAX*10 area
        assert!(matches!(
            Value::decode(too_big).unwrap_err(),
            SyrupError::IntOverflow { at: 0 }
        ));
    }

    #[test]
    fn reject_length_overflow_bytestring() {
        // Declares 10 bytes, provides 3.
        assert!(matches!(
            Value::decode(b"10:abc").unwrap_err(),
            SyrupError::LengthOverflow {
                len: 10,
                remaining: 3,
                at: 0
            }
        ));
    }

    #[test]
    fn reject_length_overflow_string() {
        assert!(matches!(
            Value::decode(b"99\"short").unwrap_err(),
            SyrupError::LengthOverflow { len: 99, .. }
        ));
    }

    #[test]
    fn reject_invalid_utf8_string() {
        // Length 2, body is invalid UTF-8 (0xff 0xfe).
        let bad = [b'2', b'"', 0xff, 0xfe];
        assert!(matches!(
            Value::decode(&bad).unwrap_err(),
            SyrupError::InvalidUtf8 { .. }
        ));
    }

    #[test]
    fn reject_invalid_utf8_symbol() {
        let bad = [b'1', b'\'', 0xff];
        assert!(matches!(
            Value::decode(&bad).unwrap_err(),
            SyrupError::InvalidUtf8 { .. }
        ));
    }

    #[test]
    fn bytestring_allows_arbitrary_bytes() {
        // The SAME 0xff 0xfe bytes are fine in a *bytestring* (no UTF-8 rule).
        let ok = [b'2', b':', 0xff, 0xfe];
        assert_eq!(Value::decode(&ok).unwrap(), Value::bytes(vec![0xff, 0xfe]));
    }

    #[test]
    fn reject_truncated_float() {
        // 'D' then only 4 bytes.
        let bad = [b'D', 0, 0, 0, 0];
        assert!(matches!(
            Value::decode(&bad).unwrap_err(),
            SyrupError::MalformedFloat { at: 0 }
        ));
        // 'D' alone.
        assert!(matches!(
            Value::decode(b"D").unwrap_err(),
            SyrupError::MalformedFloat { at: 0 }
        ));
    }

    #[test]
    fn reject_unterminated_list() {
        assert!(matches!(
            Value::decode(b"[tf").unwrap_err(),
            SyrupError::UnexpectedEof { .. }
        ));
    }

    #[test]
    fn reject_unterminated_record() {
        assert!(matches!(
            Value::decode(b"<10'op:deliver").unwrap_err(),
            SyrupError::UnexpectedEof { .. }
        ));
    }

    #[test]
    fn reject_empty_record() {
        // '<>' has no label.
        assert!(matches!(
            Value::decode(b"<>").unwrap_err(),
            SyrupError::UnexpectedEof {
                wanted: "record label"
            }
        ));
    }

    #[test]
    fn reject_non_canonical_dict_out_of_order() {
        // Hand-craft a dict with keys "b" then "a" (descending) — a canonical
        // encoder would never emit this; the decoder must reject it.
        // {1"b 1+ 1"a 2+}
        let bad = b"{1\"b1+1\"a2+}";
        assert!(matches!(
            Value::decode(bad).unwrap_err(),
            SyrupError::NonCanonicalDict { .. }
        ));
    }

    #[test]
    fn reject_non_canonical_dict_duplicate_key() {
        // {1"a 1+ 1"a 2+} — duplicate key is not strictly ascending.
        let bad = b"{1\"a1+1\"a2+}";
        assert!(matches!(
            Value::decode(bad).unwrap_err(),
            SyrupError::NonCanonicalDict { .. }
        ));
    }

    #[test]
    fn reject_non_canonical_set_out_of_order() {
        // #2+1+$  (descending)
        assert!(matches!(
            Value::decode(b"#2+1+$").unwrap_err(),
            SyrupError::NonCanonicalSet { .. }
        ));
    }

    #[test]
    fn reject_non_canonical_set_duplicate() {
        // #1+1+$
        assert!(matches!(
            Value::decode(b"#1+1+$").unwrap_err(),
            SyrupError::NonCanonicalSet { .. }
        ));
    }

    #[test]
    fn reject_trailing_bytes() {
        // A complete "t" followed by garbage.
        assert!(matches!(
            Value::decode(b"tXXX").unwrap_err(),
            SyrupError::TrailingBytes { remaining: 3 }
        ));
    }

    #[test]
    fn decoder_enforces_nesting_limit() {
        let mut wire = vec![b'['; MAX_DECODE_DEPTH + 1];
        wire.push(b't');
        wire.extend(std::iter::repeat_n(b']', MAX_DECODE_DEPTH + 1));

        assert!(matches!(
            Value::decode(&wire),
            Err(SyrupError::NestingTooDeep {
                max: MAX_DECODE_DEPTH,
                ..
            })
        ));

        let mut at_limit = vec![b'['; MAX_DECODE_DEPTH];
        at_limit.push(b't');
        at_limit.extend(std::iter::repeat_n(b']', MAX_DECODE_DEPTH));
        assert!(Value::decode(&at_limit).is_ok());
    }

    #[test]
    fn decode_prefix_allows_trailing() {
        // decode_prefix is the framed/streaming entry point: trailing bytes OK.
        let (v, n) = Value::decode_prefix(b"t<rest>").unwrap();
        assert_eq!(v, Value::Bool(true));
        assert_eq!(n, 1);
    }

    #[test]
    fn decode_prefix_chains() {
        // Decode three values back-to-back from one buffer.
        let buf = b"t42+3:abc";
        let (v0, n0) = Value::decode_prefix(buf).unwrap();
        assert_eq!(v0, Value::Bool(true));
        let (v1, n1) = Value::decode_prefix(&buf[n0..]).unwrap();
        assert_eq!(v1, Value::int(42));
        let (v2, _) = Value::decode_prefix(&buf[n0 + n1..]).unwrap();
        assert_eq!(v2, Value::bytes(b"abc".to_vec()));
    }

    // -------------------------------------------------------------------
    // Fuzz-ish: a corpus of random-ish bytes must never panic the decoder.
    // -------------------------------------------------------------------

    #[test]
    fn decoder_never_panics_on_garbage() {
        // Deterministic pseudo-random byte sequences (xorshift) — the decoder
        // must return Ok or Err, never panic / overrun.
        let mut state: u64 = 0x9e3779b97f4a7c15;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..20_000 {
            let len = (next() % 64) as usize;
            let mut buf = Vec::with_capacity(len);
            for _ in 0..len {
                buf.push((next() & 0xff) as u8);
            }
            // Must not panic. (Mostly Err; occasionally Ok for valid prefixes,
            // which decode() then rejects as TrailingBytes — also fine.)
            let _ = Value::decode(&buf);
            let _ = Value::decode_prefix(&buf);
        }
    }

    #[test]
    fn fuzz_roundtrip_structured() {
        // Build random *valid* values and assert they round-trip. This catches
        // encoder/decoder asymmetries the fixed cases might miss.
        let mut state: u64 = 0x2545f4914f6cdd1d;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        fn build(next: &mut dyn FnMut() -> u64, depth: u32) -> Value {
            let choice = if depth == 0 { next() % 6 } else { next() % 9 };
            match choice {
                0 => Value::Bool(next() & 1 == 0),
                1 => Value::Int(next() as i64 as i128),
                2 => Value::Float(f64::from_bits(next())),
                3 => {
                    let n = (next() % 8) as usize;
                    Value::Bytes((0..n).map(|_| (next() & 0xff) as u8).collect())
                }
                4 => {
                    let n = (next() % 8) as usize;
                    Value::Str(
                        (0..n)
                            .map(|_| char::from(b'a' + (next() % 26) as u8))
                            .collect(),
                    )
                }
                5 => {
                    let n = (next() % 8) as usize;
                    Value::Symbol(
                        (0..n)
                            .map(|_| char::from(b'a' + (next() % 26) as u8))
                            .collect(),
                    )
                }
                6 => {
                    let n = (next() % 4) as usize;
                    Value::List((0..n).map(|_| build(next, depth - 1)).collect())
                }
                7 => {
                    let n = (next() % 4) as usize;
                    let mut d = Dict::new();
                    for _ in 0..n {
                        d.insert(build(next, depth - 1), build(next, depth - 1));
                    }
                    Value::Dict(d)
                }
                _ => {
                    let n = (next() % 4) as usize;
                    Value::record(
                        format!("rec{}", next() % 100),
                        (0..n).map(|_| build(next, depth - 1)).collect::<Vec<_>>(),
                    )
                }
            }
        }
        for _ in 0..5_000 {
            let v = build(&mut next, 4);
            // Floats may be NaN; compare via re-encode to dodge NaN != NaN.
            let bytes = v.encode();
            let back = Value::decode(&bytes).expect("valid value must decode");
            assert_eq!(
                back.encode(),
                bytes,
                "re-encode must be byte-identical (canonical) for {v:?}"
            );
        }
    }
}
