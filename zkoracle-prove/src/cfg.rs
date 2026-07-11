//! **The well-formed leg** — a JSON CFG parse certificate (`producesChain`-shaped).
//!
//! This is the Rust realization of `metatheory/Dregg2/Crypto/Cfg.lean`. The prover emits
//! a **derivation form-chain** — the sentential forms `[initial] ⟶ … ⟶ input`, each
//! consecutive pair a single-rule `Produces` — and the verifier checks each step locally.
//! This is the context-free analogue of a DFA run: nested/balanced structure (arbitrary
//! object/array depth) the regular DFA cascade provably cannot express.
//!
//! The types mirror `Cfg.lean` one-for-one:
//!
//! | this module                    | `Cfg.lean`                                   |
//! |--------------------------------|----------------------------------------------|
//! | [`Symbol`]                     | `Symbol T g.NT` (terminal / nonterminal)     |
//! | [`Rule`]                       | `ContextFreeRule T NT`                       |
//! | [`json_grammar`]               | a `ContextFreeGrammar`                        |
//! | [`ParseCertificate`] (`Vec<Vec<Symbol>>`) | the derivation `chain`             |
//! | [`produces_chain`]             | `producesChain g chain`                       |
//! | [`cfg_accepts`]                | `CfgAccepts g input chain` (head/getLast/producesChain) |
//! | [`verify_cfg_cert`]            | the `CfgVerifierKernel.verify` accepting bit  |
//!
//! Unlike `Cfg.lean`'s hand-written 5-token demo grammar, this is a **real JSON grammar**
//! (objects with members, arrays with elements, strings/numbers/booleans/null) plus a
//! recursive-descent parser that emits the leftmost derivation certificate over any
//! standard JSON body — e.g. an actual Anthropic `POST /v1/messages` response. A
//! well-formed body yields a valid certificate; a malformed body yields NONE.

/// A JSON terminal token class (the grammar's terminal alphabet — `T` in `Cfg.lean`).
/// String/number/boolean/null LEAVES are single terminals; structural punctuation are
/// terminals too. The concrete lexeme bytes are abstracted away (the CFG certifies
/// STRUCTURE — that the token stream nests correctly).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JTok {
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `[`
    LBrack,
    /// `]`
    RBrack,
    /// `:`
    Colon,
    /// `,`
    Comma,
    /// a string literal `"…"`
    Str,
    /// a number literal
    Num,
    /// `true`
    True,
    /// `false`
    False,
    /// `null`
    Null,
}

/// A JSON nonterminal (`g.NT` in `Cfg.lean`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JNt {
    /// a JSON value (the grammar's initial nonterminal)
    Value,
    /// an object `{ … }`
    Object,
    /// a non-empty comma-separated member list
    Members,
    /// one `"key": value` member
    Member,
    /// an array `[ … ]`
    Array,
    /// a non-empty comma-separated element list
    Elements,
}

/// A grammar symbol — terminal or nonterminal (`Symbol T g.NT`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Symbol {
    /// A terminal token.
    T(JTok),
    /// A nonterminal.
    N(JNt),
}

/// A context-free production `lhs → rhs` (`ContextFreeRule`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    /// The nonterminal being rewritten.
    pub lhs: JNt,
    /// The replacement sentential form.
    pub rhs: Vec<Symbol>,
}

/// The initial nonterminal (`g.initial`).
pub const INITIAL: JNt = JNt::Value;

/// **The JSON grammar** — the production set (`ContextFreeGrammar.rules`):
///
/// ```text
/// Value    → Str | Num | True | False | Null | Object | Array
/// Object   → { } | { Members }
/// Members  → Member | Member , Members
/// Member   → Str : Value
/// Array    → [ ] | [ Elements ]
/// Elements → Value | Value , Elements
/// ```
///
/// Objects and arrays nest through `Value`, so this recognizes arbitrary-depth balanced
/// JSON — the canonical NON-regular property the DFA cascade cannot certify.
pub fn json_grammar() -> Vec<Rule> {
    use JNt::*;
    use JTok::*;
    let t = Symbol::T;
    let n = Symbol::N;
    vec![
        Rule {
            lhs: Value,
            rhs: vec![t(Str)],
        },
        Rule {
            lhs: Value,
            rhs: vec![t(Num)],
        },
        Rule {
            lhs: Value,
            rhs: vec![t(True)],
        },
        Rule {
            lhs: Value,
            rhs: vec![t(False)],
        },
        Rule {
            lhs: Value,
            rhs: vec![t(Null)],
        },
        Rule {
            lhs: Value,
            rhs: vec![n(Object)],
        },
        Rule {
            lhs: Value,
            rhs: vec![n(Array)],
        },
        Rule {
            lhs: Object,
            rhs: vec![t(LBrace), t(RBrace)],
        },
        Rule {
            lhs: Object,
            rhs: vec![t(LBrace), n(Members), t(RBrace)],
        },
        Rule {
            lhs: Members,
            rhs: vec![n(Member)],
        },
        Rule {
            lhs: Members,
            rhs: vec![n(Member), t(Comma), n(Members)],
        },
        Rule {
            lhs: Member,
            rhs: vec![t(Str), t(Colon), n(Value)],
        },
        Rule {
            lhs: Array,
            rhs: vec![t(LBrack), t(RBrack)],
        },
        Rule {
            lhs: Array,
            rhs: vec![t(LBrack), n(Elements), t(RBrack)],
        },
        Rule {
            lhs: Elements,
            rhs: vec![n(Value)],
        },
        Rule {
            lhs: Elements,
            rhs: vec![n(Value), t(Comma), n(Elements)],
        },
    ]
}

/// **The parse certificate** — the derivation form-chain (`chain` in `Cfg.lean`): the
/// list of sentential forms threaded from `[N(initial)]` to the token word. Each
/// consecutive pair is one single-rule `Produces` step, checked locally by
/// [`verify_cfg_cert`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseCertificate {
    /// The sentential forms `[initial] ⟶ … ⟶ input`.
    pub chain: Vec<Vec<Symbol>>,
}

/// Why a JSON body failed to tokenize / parse (so the prover cannot emit a certificate),
/// or why a presented certificate does not certify its body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgError {
    /// The body does not lex as JSON at byte offset `at`.
    LexError { at: usize },
    /// The token stream does not parse as a JSON value (unbalanced / trailing tokens).
    ParseError { reason: &'static str },
    /// The certificate chain is empty.
    EmptyChain,
    /// The chain does not start at `[N(initial)]`.
    BadHead,
    /// The chain does not end at the body's token word (`input.map(terminal)`).
    BadTail,
    /// Step `at` of the chain is not a valid single-rule `Produces` rewrite.
    BadStep { at: usize },
}

// ─────────────────────────────────────────────────────────────────────────────
// Tokenizer — bytes → JTok stream (standard JSON lexing).
// ─────────────────────────────────────────────────────────────────────────────

/// Lex a JSON body into its terminal token stream. Fail-closed on any non-JSON byte —
/// a malformed body cannot even be tokenized, so no certificate is emitted for it.
pub fn tokenize(body: &[u8]) -> Result<Vec<JTok>, CfgError> {
    let mut toks = Vec::new();
    let mut i = 0usize;
    let n = body.len();
    while i < n {
        let c = body[i];
        match c {
            b' ' | b'\t' | b'\n' | b'\r' => {
                i += 1;
            }
            b'{' => {
                toks.push(JTok::LBrace);
                i += 1;
            }
            b'}' => {
                toks.push(JTok::RBrace);
                i += 1;
            }
            b'[' => {
                toks.push(JTok::LBrack);
                i += 1;
            }
            b']' => {
                toks.push(JTok::RBrack);
                i += 1;
            }
            b':' => {
                toks.push(JTok::Colon);
                i += 1;
            }
            b',' => {
                toks.push(JTok::Comma);
                i += 1;
            }
            b'"' => {
                i = lex_string(body, i)?;
                toks.push(JTok::Str);
            }
            b't' => {
                i = lex_keyword(body, i, b"true")?;
                toks.push(JTok::True);
            }
            b'f' => {
                i = lex_keyword(body, i, b"false")?;
                toks.push(JTok::False);
            }
            b'n' => {
                i = lex_keyword(body, i, b"null")?;
                toks.push(JTok::Null);
            }
            b'-' | b'0'..=b'9' => {
                i = lex_number(body, i)?;
                toks.push(JTok::Num);
            }
            _ => return Err(CfgError::LexError { at: i }),
        }
    }
    Ok(toks)
}

/// Consume a string starting at the opening quote `body[i] == '"'`; return the index just
/// past the closing quote. Handles the standard JSON escapes.
fn lex_string(body: &[u8], start: usize) -> Result<usize, CfgError> {
    let n = body.len();
    let mut i = start + 1; // past opening quote
    while i < n {
        match body[i] {
            b'"' => return Ok(i + 1),
            b'\\' => {
                let e = *body.get(i + 1).ok_or(CfgError::LexError { at: i })?;
                match e {
                    b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => i += 2,
                    b'u' => {
                        // \uXXXX — four hex digits
                        if i + 6 > n {
                            return Err(CfgError::LexError { at: i });
                        }
                        for h in &body[i + 2..i + 6] {
                            if !h.is_ascii_hexdigit() {
                                return Err(CfgError::LexError { at: i });
                            }
                        }
                        i += 6;
                    }
                    _ => return Err(CfgError::LexError { at: i }),
                }
            }
            // control chars must be escaped in strict JSON
            0x00..=0x1F => return Err(CfgError::LexError { at: i }),
            _ => i += 1,
        }
    }
    Err(CfgError::LexError { at: start }) // unterminated string
}

/// Consume the literal `kw` at `body[start..]`; return the index just past it.
fn lex_keyword(body: &[u8], start: usize, kw: &[u8]) -> Result<usize, CfgError> {
    if body.len() >= start + kw.len() && &body[start..start + kw.len()] == kw {
        Ok(start + kw.len())
    } else {
        Err(CfgError::LexError { at: start })
    }
}

/// Consume a JSON number at `body[start..]`; return the index just past it. Grammar:
/// `-? (0 | [1-9][0-9]*) (. [0-9]+)? ([eE] [+-]? [0-9]+)?`.
fn lex_number(body: &[u8], start: usize) -> Result<usize, CfgError> {
    let n = body.len();
    let mut i = start;
    if i < n && body[i] == b'-' {
        i += 1;
    }
    // integer part
    match body.get(i) {
        Some(b'0') => i += 1,
        Some(b'1'..=b'9') => {
            while i < n && body[i].is_ascii_digit() {
                i += 1;
            }
        }
        _ => return Err(CfgError::LexError { at: start }),
    }
    // fraction
    if i < n && body[i] == b'.' {
        i += 1;
        let f0 = i;
        while i < n && body[i].is_ascii_digit() {
            i += 1;
        }
        if i == f0 {
            return Err(CfgError::LexError { at: start });
        }
    }
    // exponent
    if i < n && (body[i] == b'e' || body[i] == b'E') {
        i += 1;
        if i < n && (body[i] == b'+' || body[i] == b'-') {
            i += 1;
        }
        let e0 = i;
        while i < n && body[i].is_ascii_digit() {
            i += 1;
        }
        if i == e0 {
            return Err(CfgError::LexError { at: start });
        }
    }
    Ok(i)
}

// ─────────────────────────────────────────────────────────────────────────────
// Parser — JTok stream → parse tree → leftmost derivation certificate.
// ─────────────────────────────────────────────────────────────────────────────

/// A concrete parse tree. Each [`Tree::Node`] records a nonterminal and its children; the
/// rule it applied is recovered from the children (leaves → terminals, sub-nodes →
/// nonterminals), so the tree witnesses a specific derivation.
#[derive(Clone, Debug)]
enum Tree {
    Leaf(JTok),
    Node(JNt, Vec<Tree>),
}

impl Tree {
    /// The grammar symbol this subtree occupies in its parent's rhs.
    fn symbol(&self) -> Symbol {
        match self {
            Tree::Leaf(t) => Symbol::T(*t),
            Tree::Node(nt, _) => Symbol::N(*nt),
        }
    }
}

/// A recursive-descent parser cursor over the token stream.
struct Parser<'a> {
    toks: &'a [JTok],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<JTok> {
        self.toks.get(self.pos).copied()
    }

    fn bump(&mut self, expected: JTok) -> Result<(), CfgError> {
        if self.peek() == Some(expected) {
            self.pos += 1;
            Ok(())
        } else {
            Err(CfgError::ParseError {
                reason: "unexpected token",
            })
        }
    }

    fn value(&mut self) -> Result<Tree, CfgError> {
        match self.peek() {
            Some(JTok::Str) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::Str)]))
            }
            Some(JTok::Num) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::Num)]))
            }
            Some(JTok::True) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::True)]))
            }
            Some(JTok::False) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::False)]))
            }
            Some(JTok::Null) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::Null)]))
            }
            Some(JTok::LBrace) => {
                let obj = self.object()?;
                Ok(Tree::Node(JNt::Value, vec![obj]))
            }
            Some(JTok::LBrack) => {
                let arr = self.array()?;
                Ok(Tree::Node(JNt::Value, vec![arr]))
            }
            _ => Err(CfgError::ParseError {
                reason: "expected a value",
            }),
        }
    }

    fn object(&mut self) -> Result<Tree, CfgError> {
        self.bump(JTok::LBrace)?;
        if self.peek() == Some(JTok::RBrace) {
            self.pos += 1;
            return Ok(Tree::Node(
                JNt::Object,
                vec![Tree::Leaf(JTok::LBrace), Tree::Leaf(JTok::RBrace)],
            ));
        }
        let members = self.members()?;
        self.bump(JTok::RBrace)?;
        Ok(Tree::Node(
            JNt::Object,
            vec![Tree::Leaf(JTok::LBrace), members, Tree::Leaf(JTok::RBrace)],
        ))
    }

    fn members(&mut self) -> Result<Tree, CfgError> {
        let member = self.member()?;
        if self.peek() == Some(JTok::Comma) {
            self.pos += 1;
            let rest = self.members()?;
            Ok(Tree::Node(
                JNt::Members,
                vec![member, Tree::Leaf(JTok::Comma), rest],
            ))
        } else {
            Ok(Tree::Node(JNt::Members, vec![member]))
        }
    }

    fn member(&mut self) -> Result<Tree, CfgError> {
        self.bump(JTok::Str)?;
        self.bump(JTok::Colon)?;
        let value = self.value()?;
        Ok(Tree::Node(
            JNt::Member,
            vec![Tree::Leaf(JTok::Str), Tree::Leaf(JTok::Colon), value],
        ))
    }

    fn array(&mut self) -> Result<Tree, CfgError> {
        self.bump(JTok::LBrack)?;
        if self.peek() == Some(JTok::RBrack) {
            self.pos += 1;
            return Ok(Tree::Node(
                JNt::Array,
                vec![Tree::Leaf(JTok::LBrack), Tree::Leaf(JTok::RBrack)],
            ));
        }
        let elements = self.elements()?;
        self.bump(JTok::RBrack)?;
        Ok(Tree::Node(
            JNt::Array,
            vec![Tree::Leaf(JTok::LBrack), elements, Tree::Leaf(JTok::RBrack)],
        ))
    }

    fn elements(&mut self) -> Result<Tree, CfgError> {
        let value = self.value()?;
        if self.peek() == Some(JTok::Comma) {
            self.pos += 1;
            let rest = self.elements()?;
            Ok(Tree::Node(
                JNt::Elements,
                vec![value, Tree::Leaf(JTok::Comma), rest],
            ))
        } else {
            Ok(Tree::Node(JNt::Elements, vec![value]))
        }
    }
}

/// Produce the LEFTMOST derivation chain from a parse tree: repeatedly rewrite the
/// leftmost nonterminal using the rule its subtree records. This is the certificate the
/// prover threads — a valid `producesChain` from `[N(initial)]` to the token word.
fn leftmost_chain(root: &Tree) -> Vec<Vec<Symbol>> {
    use std::collections::VecDeque;
    let root_nt = match root {
        Tree::Node(nt, _) => *nt,
        Tree::Leaf(_) => unreachable!("root of a JSON parse is always a Value nonterminal"),
    };
    let mut form: Vec<Symbol> = vec![Symbol::N(root_nt)];
    // The pending subtrees for the nonterminals of `form`, in left-to-right order.
    let mut queue: VecDeque<&Tree> = VecDeque::new();
    queue.push_back(root);
    let mut chain: Vec<Vec<Symbol>> = vec![form.clone()];

    while let Some(i) = form.iter().position(|s| matches!(s, Symbol::N(_))) {
        // Everything before i is terminal, so the front of the queue is the subtree for
        // the nonterminal at i.
        let node = queue
            .pop_front()
            .expect("a pending subtree per nonterminal");
        let Tree::Node(_nt, children) = node else {
            unreachable!("a nonterminal position always maps to a Node")
        };
        let rhs: Vec<Symbol> = children.iter().map(Tree::symbol).collect();
        // Splice rhs in at position i.
        let mut next = form[..i].to_vec();
        next.extend_from_slice(&rhs);
        next.extend_from_slice(&form[i + 1..]);
        // The rhs's nonterminal children become the new leftmost pending subtrees.
        for child in children.iter().rev() {
            if let Tree::Node(..) = child {
                queue.push_front(child);
            }
        }
        form = next;
        chain.push(form.clone());
    }
    chain
}

/// **PRODUCE a parse certificate** over a JSON body — the well-formed-leg prover.
///
/// Lexes + parses the body as a JSON value and emits the leftmost derivation certificate.
/// A well-formed body yields `Ok(cert)`; a malformed body (lex/parse failure, trailing
/// tokens) yields `Err` — **no certificate exists for a malformed body**.
pub fn prove_cfg_cert(body: &[u8]) -> Result<ParseCertificate, CfgError> {
    let tree = parse_tree(body)?;
    Ok(ParseCertificate {
        chain: leftmost_chain(&tree),
    })
}

/// Lex + parse `body` as a single JSON value (no trailing tokens) — the shared front
/// half of both certificate provers.
fn parse_tree(body: &[u8]) -> Result<Tree, CfgError> {
    let toks = tokenize(body)?;
    let mut parser = Parser {
        toks: &toks,
        pos: 0,
    };
    let tree = parser.value()?;
    if parser.pos != toks.len() {
        return Err(CfgError::ParseError {
            reason: "trailing tokens after the JSON value",
        });
    }
    Ok(tree)
}

// ─────────────────────────────────────────────────────────────────────────────
// The COMPACT certificate — the leftmost RULE SEQUENCE (O(tokens), not O(tokens²)).
// ─────────────────────────────────────────────────────────────────────────────

/// **The compact parse certificate** — the leftmost derivation's rule sequence (indices
/// into [`json_grammar`]), one byte per production step.
///
/// The full form-chain ([`ParseCertificate`]) stores every sentential form and is
/// O(tokens²) symbols; the forms are recomputable, so storing them is pure redundancy.
/// A leftmost derivation is determined by its RULE SEQUENCE alone, and
/// [`verify_cfg_compact`] replays it as a pushdown run in O(tokens) time and space.
///
/// This is `CfgCompact.lean`'s `Replay` certificate: `compact_sound` there proves an
/// accepted replay implies `input ∈ g.language`, and `compact_to_chain` rebuilds the
/// existing `CfgAccepts` chain object — [`expand_compact`] is that theorem's Rust twin.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CompactCert {
    /// The leftmost derivation's rule indices into [`json_grammar`] (16 rules → u8).
    pub rules: Vec<u8>,
}

/// The rule indices of [`json_grammar`], named (pinned by `rule_ids_match_the_grammar`).
mod rule_id {
    pub const VALUE_STR: u8 = 0;
    pub const VALUE_NUM: u8 = 1;
    pub const VALUE_TRUE: u8 = 2;
    pub const VALUE_FALSE: u8 = 3;
    pub const VALUE_NULL: u8 = 4;
    pub const VALUE_OBJECT: u8 = 5;
    pub const VALUE_ARRAY: u8 = 6;
    pub const OBJECT_EMPTY: u8 = 7;
    pub const OBJECT_MEMBERS: u8 = 8;
    pub const MEMBERS_ONE: u8 = 9;
    pub const MEMBERS_CONS: u8 = 10;
    pub const MEMBER: u8 = 11;
    pub const ARRAY_EMPTY: u8 = 12;
    pub const ARRAY_ELEMENTS: u8 = 13;
    pub const ELEMENTS_ONE: u8 = 14;
    pub const ELEMENTS_CONS: u8 = 15;
}

/// An unfilled rule slot ([`prove_cfg_compact`]'s placeholder — always patched before
/// return; no grammar rule has this index).
const RULE_PENDING: u8 = 0xFF;

/// A work item of the iterative compact prover: a grammar symbol to satisfy, or a
/// deferred CHOICE for a list nonterminal (`Members`/`Elements` pick `one` vs `cons`
/// only after their first item is consumed — the slot at `at` holds the choice's
/// preorder position, patched when the continuation resolves).
enum Work {
    Sym(Symbol),
    MembersCont { at: usize },
    ElementsCont { at: usize },
}

/// **PRODUCE a compact certificate** over a JSON body — the O(tokens) wire form of
/// [`prove_cfg_cert`], fully ITERATIVE (explicit work stack, no recursion): certificate
/// production is heap-bounded, so 10M-token and 100k-deep bodies prove without touching
/// the thread stack. The leftmost preorder position of every rule is known when its
/// nonterminal is expanded, even where the CHOICE (one vs cons) resolves later — those
/// slots are reserved and patched ([`Work::MembersCont`]/[`Work::ElementsCont`]).
///
/// A well-formed body yields `Ok`; a malformed body yields `Err`.
pub fn prove_cfg_compact(body: &[u8]) -> Result<CompactCert, CfgError> {
    use rule_id::*;
    let toks = tokenize(body)?;
    let err = |reason: &'static str| CfgError::ParseError { reason };
    let mut out: Vec<u8> = Vec::new();
    let mut stack: Vec<Work> = vec![Work::Sym(Symbol::N(INITIAL))];
    let mut pos = 0usize;
    while let Some(w) = stack.pop() {
        match w {
            Work::Sym(Symbol::T(t)) => {
                if toks.get(pos) != Some(&t) {
                    return Err(err("unexpected token"));
                }
                pos += 1;
            }
            Work::Sym(Symbol::N(nt)) => match nt {
                JNt::Value => {
                    let (rule, next) = match toks.get(pos) {
                        Some(JTok::Str) => (VALUE_STR, Symbol::T(JTok::Str)),
                        Some(JTok::Num) => (VALUE_NUM, Symbol::T(JTok::Num)),
                        Some(JTok::True) => (VALUE_TRUE, Symbol::T(JTok::True)),
                        Some(JTok::False) => (VALUE_FALSE, Symbol::T(JTok::False)),
                        Some(JTok::Null) => (VALUE_NULL, Symbol::T(JTok::Null)),
                        Some(JTok::LBrace) => (VALUE_OBJECT, Symbol::N(JNt::Object)),
                        Some(JTok::LBrack) => (VALUE_ARRAY, Symbol::N(JNt::Array)),
                        _ => return Err(err("expected a value")),
                    };
                    out.push(rule);
                    stack.push(Work::Sym(next));
                }
                JNt::Object => {
                    if toks.get(pos) != Some(&JTok::LBrace) {
                        return Err(err("expected an object"));
                    }
                    if toks.get(pos + 1) == Some(&JTok::RBrace) {
                        out.push(OBJECT_EMPTY);
                        stack.push(Work::Sym(Symbol::T(JTok::RBrace)));
                        stack.push(Work::Sym(Symbol::T(JTok::LBrace)));
                    } else {
                        out.push(OBJECT_MEMBERS);
                        stack.push(Work::Sym(Symbol::T(JTok::RBrace)));
                        stack.push(Work::Sym(Symbol::N(JNt::Members)));
                        stack.push(Work::Sym(Symbol::T(JTok::LBrace)));
                    }
                }
                JNt::Array => {
                    if toks.get(pos) != Some(&JTok::LBrack) {
                        return Err(err("expected an array"));
                    }
                    if toks.get(pos + 1) == Some(&JTok::RBrack) {
                        out.push(ARRAY_EMPTY);
                        stack.push(Work::Sym(Symbol::T(JTok::RBrack)));
                        stack.push(Work::Sym(Symbol::T(JTok::LBrack)));
                    } else {
                        out.push(ARRAY_ELEMENTS);
                        stack.push(Work::Sym(Symbol::T(JTok::RBrack)));
                        stack.push(Work::Sym(Symbol::N(JNt::Elements)));
                        stack.push(Work::Sym(Symbol::T(JTok::LBrack)));
                    }
                }
                JNt::Members => {
                    let at = out.len();
                    out.push(RULE_PENDING);
                    stack.push(Work::MembersCont { at });
                    stack.push(Work::Sym(Symbol::N(JNt::Member)));
                }
                JNt::Member => {
                    out.push(MEMBER);
                    stack.push(Work::Sym(Symbol::N(JNt::Value)));
                    stack.push(Work::Sym(Symbol::T(JTok::Colon)));
                    stack.push(Work::Sym(Symbol::T(JTok::Str)));
                }
                JNt::Elements => {
                    let at = out.len();
                    out.push(RULE_PENDING);
                    stack.push(Work::ElementsCont { at });
                    stack.push(Work::Sym(Symbol::N(JNt::Value)));
                }
            },
            Work::MembersCont { at } => {
                if toks.get(pos) == Some(&JTok::Comma) {
                    out[at] = MEMBERS_CONS;
                    pos += 1;
                    stack.push(Work::Sym(Symbol::N(JNt::Members)));
                } else {
                    out[at] = MEMBERS_ONE;
                }
            }
            Work::ElementsCont { at } => {
                if toks.get(pos) == Some(&JTok::Comma) {
                    out[at] = ELEMENTS_CONS;
                    pos += 1;
                    stack.push(Work::Sym(Symbol::N(JNt::Elements)));
                } else {
                    out[at] = ELEMENTS_ONE;
                }
            }
        }
    }
    if pos != toks.len() {
        return Err(err("trailing tokens after the JSON value"));
    }
    debug_assert!(!out.contains(&RULE_PENDING));
    Ok(CompactCert { rules: out })
}

/// **VERIFY a compact certificate binds a JSON body** — the pushdown replay
/// (`CfgCompact.lean::Replay`), O(tokens) time and space.
///
/// The verifier re-tokenizes `body` ITSELF, then replays: a stack starts at
/// `[N(initial)]`; a terminal on top must match the next input token; a nonterminal on
/// top consumes the next certificate rule, whose `lhs` must equal it, and pushes its
/// `rhs`. ACCEPT ⟺ the rules and the input are both exactly consumed as the stack
/// empties — a genuine leftmost derivation of the body's token word.
pub fn verify_cfg_compact(cert: &CompactCert, body: &[u8]) -> Result<(), CfgError> {
    let toks = tokenize(body)?;
    let grammar = json_grammar();
    let mut stack: Vec<Symbol> = vec![Symbol::N(INITIAL)];
    let mut pos = 0usize; // input cursor
    let mut at = 0usize; // rule cursor
    while let Some(top) = stack.pop() {
        match top {
            Symbol::T(t) => {
                if toks.get(pos) != Some(&t) {
                    return Err(CfgError::BadTail);
                }
                pos += 1;
            }
            Symbol::N(nt) => {
                let Some(&id) = cert.rules.get(at) else {
                    return Err(CfgError::BadStep { at });
                };
                let rule = grammar
                    .get(id as usize)
                    .filter(|r| r.lhs == nt)
                    .ok_or(CfgError::BadStep { at })?;
                at += 1;
                for sym in rule.rhs.iter().rev() {
                    stack.push(*sym);
                }
            }
        }
    }
    if at != cert.rules.len() {
        return Err(CfgError::BadStep { at });
    }
    if pos != toks.len() {
        return Err(CfgError::BadTail);
    }
    Ok(())
}

/// **EXPAND a compact certificate to the full form-chain** — the Rust twin of
/// `CfgCompact.lean::compact_to_chain`: a valid rule sequence rebuilds exactly the
/// `CfgAccepts`-shaped [`ParseCertificate`]. O(tokens²) — a spec-bridge for tests and
/// interop, NOT the verification path ([`verify_cfg_compact`] is O(tokens)).
pub fn expand_compact(cert: &CompactCert) -> Result<ParseCertificate, CfgError> {
    let grammar = json_grammar();
    let mut form: Vec<Symbol> = vec![Symbol::N(INITIAL)];
    let mut chain: Vec<Vec<Symbol>> = vec![form.clone()];
    for (at, &id) in cert.rules.iter().enumerate() {
        let i = form
            .iter()
            .position(|s| matches!(s, Symbol::N(_)))
            .ok_or(CfgError::BadStep { at })?;
        let Symbol::N(nt) = form[i] else {
            unreachable!()
        };
        let rule = grammar
            .get(id as usize)
            .filter(|r| r.lhs == nt)
            .ok_or(CfgError::BadStep { at })?;
        let mut next = form[..i].to_vec();
        next.extend_from_slice(&rule.rhs);
        next.extend_from_slice(&form[i + 1..]);
        form = next;
        chain.push(form.clone());
    }
    Ok(ParseCertificate { chain })
}

// ─────────────────────────────────────────────────────────────────────────────
// Verifier — the `CfgAccepts` accepting bit (locally-checkable).
// ─────────────────────────────────────────────────────────────────────────────

/// Whether `b` is one single-rule `Produces` rewrite of `a` under `grammar`: there is a
/// rule `lhs → rhs` and a position `i` with `a[i] = N(lhs)` and
/// `b == a[..i] ++ rhs ++ a[i+1..]`. This is `g.Produces a b` — a real production applied
/// at one nonterminal, in any context (matching `Cfg.lean`).
fn produces(grammar: &[Rule], a: &[Symbol], b: &[Symbol]) -> bool {
    for (i, sym) in a.iter().enumerate() {
        let Symbol::N(nt) = sym else { continue };
        for rule in grammar {
            if rule.lhs != *nt {
                continue;
            }
            // b == a[..i] ++ rhs ++ a[i+1..] ?
            let mut rebuilt = Vec::with_capacity(a.len() - 1 + rule.rhs.len());
            rebuilt.extend_from_slice(&a[..i]);
            rebuilt.extend_from_slice(&rule.rhs);
            rebuilt.extend_from_slice(&a[i + 1..]);
            if rebuilt == b {
                return true;
            }
        }
    }
    false
}

/// **`produces_chain`** — every consecutive pair of sentential forms is one valid
/// production step (`producesChain g chain` in `Cfg.lean`). The step at which validity
/// fails is returned as `Err(index)`.
fn produces_chain(grammar: &[Rule], chain: &[Vec<Symbol>]) -> Result<(), usize> {
    for (k, pair) in chain.windows(2).enumerate() {
        if !produces(grammar, &pair[0], &pair[1]) {
            return Err(k);
        }
    }
    Ok(())
}

/// **`cfg_accepts`** — the CFG acceptance predicate (`CfgAccepts g input chain`): the
/// chain is non-empty, STARTS at `[N(initial)]`, ENDS at the input word wrapped as
/// terminals, and every step is a valid production. Locally checkable — exactly what an
/// in-circuit CFG verifier's accepting bit certifies.
pub fn cfg_accepts(
    grammar: &[Rule],
    input: &[JTok],
    cert: &ParseCertificate,
) -> Result<(), CfgError> {
    let chain = &cert.chain;
    let head = chain.first().ok_or(CfgError::EmptyChain)?;
    if head.as_slice() != [Symbol::N(INITIAL)] {
        return Err(CfgError::BadHead);
    }
    let tail = chain.last().ok_or(CfgError::EmptyChain)?;
    let want_tail: Vec<Symbol> = input.iter().map(|t| Symbol::T(*t)).collect();
    if tail != &want_tail {
        return Err(CfgError::BadTail);
    }
    produces_chain(grammar, chain).map_err(|at| CfgError::BadStep { at })?;
    Ok(())
}

/// **VERIFY a parse certificate binds a JSON body** — the well-formed-leg verifier.
///
/// The verifier re-tokenizes `body` ITSELF (so the certificate is checked against the
/// authenticated bytes, not the prover's word), then checks `cfg_accepts` over the
/// [`json_grammar`]. `Ok(())` ⟺ the certificate is a genuine leftmost derivation of the
/// body's token word from the start symbol ⟹ the body lies in the JSON context-free
/// language.
pub fn verify_cfg_cert(cert: &ParseCertificate, body: &[u8]) -> Result<(), CfgError> {
    let toks = tokenize(body)?;
    cfg_accepts(&json_grammar(), &toks, cert)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A representative Anthropic `POST /v1/messages` response body — deeply nested
    /// (object → array of content blocks → object → …) — yields a valid certificate that
    /// the verifier accepts against the re-tokenized body.
    const ANTHROPIC_BODY: &[u8] = br#"{"id":"msg_01ABC","type":"message","role":"assistant","model":"claude-opus-4-8","content":[{"type":"text","text":"hello"}],"stop_reason":"end_turn","stop_sequence":null,"usage":{"input_tokens":12,"output_tokens":3}}"#;

    #[test]
    fn wellformed_anthropic_body_certificate_verifies() {
        let cert = prove_cfg_cert(ANTHROPIC_BODY).expect("well-formed body → certificate");
        verify_cfg_cert(&cert, ANTHROPIC_BODY).expect("the certificate verifies against the body");
        // The chain starts at the start symbol and ends at the token word (non-vacuous).
        assert_eq!(cert.chain.first().unwrap().as_slice(), [Symbol::N(INITIAL)]);
        assert!(cert.chain.len() > 1);
    }

    #[test]
    fn deeply_nested_json_certifies() {
        // Arbitrary-depth nesting — the canonical non-regular property.
        let body = br#"[[[[["deep"]]]]]"#;
        let cert = prove_cfg_cert(body).expect("nested arrays are well-formed");
        verify_cfg_cert(&cert, body).unwrap();
    }

    #[test]
    fn malformed_body_yields_no_certificate() {
        // Unbalanced brace / truncated object — the prover cannot emit a certificate.
        assert!(matches!(
            prove_cfg_cert(br#"{"id":"msg","content":"#),
            Err(_)
        ));
        assert!(matches!(prove_cfg_cert(br#"{"a":1,}"#), Err(_))); // trailing comma
        assert!(matches!(prove_cfg_cert(br#"[1,2"#), Err(_))); // unbalanced array
        assert!(matches!(prove_cfg_cert(br#"nul"#), Err(_))); // bad keyword
        assert!(matches!(prove_cfg_cert(br#"{"k" 1}"#), Err(_))); // missing colon
    }

    #[test]
    fn certificate_for_a_different_body_is_refused() {
        // A certificate proven over one body does NOT certify a different body — the
        // verifier re-tokenizes and the tail mismatches.
        let cert = prove_cfg_cert(br#"{"a":1}"#).unwrap();
        assert!(matches!(
            verify_cfg_cert(&cert, br#"{"a":2,"b":3}"#),
            Err(CfgError::BadTail)
        ));
    }

    #[test]
    fn tampered_step_is_refused() {
        // Corrupt an interior form so a step is no longer a valid single-rule Produces.
        let mut cert = prove_cfg_cert(br#"[null]"#).unwrap();
        let mid = cert.chain.len() / 2;
        cert.chain[mid].insert(0, Symbol::T(JTok::Comma));
        assert!(matches!(
            verify_cfg_cert(&cert, br#"[null]"#),
            Err(CfgError::BadStep { .. }) | Err(CfgError::BadTail)
        ));
    }

    #[test]
    fn empty_chain_and_bad_head_refused() {
        assert_eq!(
            verify_cfg_cert(&ParseCertificate { chain: vec![] }, br#"1"#),
            Err(CfgError::EmptyChain)
        );
        let bad = ParseCertificate {
            chain: vec![vec![Symbol::N(JNt::Object)], vec![Symbol::T(JTok::Num)]],
        };
        assert_eq!(verify_cfg_cert(&bad, br#"1"#), Err(CfgError::BadHead));
    }

    // ── the COMPACT certificate ──

    /// THE BRIDGE (Rust twin of `compact_to_chain`): the compact cert expands to EXACTLY
    /// the chain the full prover emits, and that expansion passes the chain verifier —
    /// so the compact form certifies the same `CfgAccepts` object.
    #[test]
    fn compact_expands_to_the_exact_chain() {
        for body in [
            ANTHROPIC_BODY,
            br#"[[[[["deep"]]]]]"# as &[u8],
            br#"{"a":{"b":[1,2,{"c":null}]},"d":true}"#,
            br#"42"#,
            br#"{}"#,
            br#"[]"#,
        ] {
            let compact = prove_cfg_compact(body).expect("well-formed body → compact cert");
            let chain = prove_cfg_cert(body).expect("well-formed body → chain cert");
            assert_eq!(expand_compact(&compact).unwrap(), chain);
            verify_cfg_cert(&expand_compact(&compact).unwrap(), body).unwrap();
            verify_cfg_compact(&compact, body).unwrap();
        }
    }

    #[test]
    fn compact_is_linear_not_quadratic() {
        // A dense body: the compact cert stays ~2 bytes/token while the chain's symbol
        // count is quadratic.
        let elems: Vec<String> = (0..512).map(|i| (i % 10).to_string()).collect();
        let body = format!(r#"{{"data":[{}]}}"#, elems.join(","));
        let toks = tokenize(body.as_bytes()).unwrap().len();
        let compact = prove_cfg_compact(body.as_bytes()).unwrap();
        assert!(compact.rules.len() < 3 * toks, "compact cert is O(tokens)");
        let chain = prove_cfg_cert(body.as_bytes()).unwrap();
        let symbols: usize = chain.chain.iter().map(|f| f.len()).sum();
        assert!(
            symbols > 100 * compact.rules.len(),
            "the chain is the fat one"
        );
        verify_cfg_compact(&compact, body.as_bytes()).unwrap();
    }

    #[test]
    fn compact_hostiles_are_refused() {
        let body = br#"{"a":[1,{"b":null}],"c":"x"}"#;
        let good = prove_cfg_compact(body).unwrap();
        verify_cfg_compact(&good, body).unwrap();

        // Flip a rule id → lhs mismatch or wrong shape.
        for at in 0..good.rules.len() {
            let mut bad = good.clone();
            bad.rules[at] = (bad.rules[at] + 1) % 16;
            assert!(
                verify_cfg_compact(&bad, body).is_err(),
                "flipping rule {at} must refuse"
            );
        }
        // Truncated sequence → a nonterminal starves.
        let mut short = good.clone();
        short.rules.pop();
        assert!(verify_cfg_compact(&short, body).is_err());
        // Extended sequence → leftover rules.
        let mut long = good.clone();
        long.rules.push(0);
        assert!(verify_cfg_compact(&long, body).is_err());
        // Out-of-range rule id.
        let mut oob = good.clone();
        oob.rules[0] = 200;
        assert!(matches!(
            verify_cfg_compact(&oob, body),
            Err(CfgError::BadStep { at: 0 })
        ));
        // A cert for a DIFFERENT body.
        let other = prove_cfg_compact(br#"{"z":9}"#).unwrap();
        assert!(verify_cfg_compact(&other, body).is_err());
        // Empty cert on non-trivial input.
        assert!(matches!(
            verify_cfg_compact(&CompactCert { rules: vec![] }, body),
            Err(CfgError::BadStep { at: 0 })
        ));
        // Malformed body refuses at tokenize, before any replay.
        assert!(verify_cfg_compact(&good, br#"{"a":"#).is_err());
    }

    /// The named rule indices are pinned to [`json_grammar`]'s order (the iterative
    /// prover's choices stay honest against the grammar the verifier replays).
    #[test]
    fn rule_ids_match_the_grammar() {
        use JNt::*;
        use JTok::*;
        let g = json_grammar();
        let expect: &[(u8, JNt, &[Symbol])] = &[
            (rule_id::VALUE_STR, Value, &[Symbol::T(Str)]),
            (rule_id::VALUE_NUM, Value, &[Symbol::T(Num)]),
            (rule_id::VALUE_TRUE, Value, &[Symbol::T(True)]),
            (rule_id::VALUE_FALSE, Value, &[Symbol::T(False)]),
            (rule_id::VALUE_NULL, Value, &[Symbol::T(Null)]),
            (rule_id::VALUE_OBJECT, Value, &[Symbol::N(Object)]),
            (rule_id::VALUE_ARRAY, Value, &[Symbol::N(Array)]),
            (
                rule_id::OBJECT_EMPTY,
                Object,
                &[Symbol::T(LBrace), Symbol::T(RBrace)],
            ),
            (
                rule_id::OBJECT_MEMBERS,
                Object,
                &[Symbol::T(LBrace), Symbol::N(Members), Symbol::T(RBrace)],
            ),
            (rule_id::MEMBERS_ONE, Members, &[Symbol::N(Member)]),
            (
                rule_id::MEMBERS_CONS,
                Members,
                &[Symbol::N(Member), Symbol::T(Comma), Symbol::N(Members)],
            ),
            (
                rule_id::MEMBER,
                Member,
                &[Symbol::T(Str), Symbol::T(Colon), Symbol::N(Value)],
            ),
            (
                rule_id::ARRAY_EMPTY,
                Array,
                &[Symbol::T(LBrack), Symbol::T(RBrack)],
            ),
            (
                rule_id::ARRAY_ELEMENTS,
                Array,
                &[Symbol::T(LBrack), Symbol::N(Elements), Symbol::T(RBrack)],
            ),
            (rule_id::ELEMENTS_ONE, Elements, &[Symbol::N(Value)]),
            (
                rule_id::ELEMENTS_CONS,
                Elements,
                &[Symbol::N(Value), Symbol::T(Comma), Symbol::N(Elements)],
            ),
        ];
        assert_eq!(g.len(), expect.len());
        for (id, lhs, rhs) in expect {
            assert_eq!(g[*id as usize].lhs, *lhs, "rule {id} lhs");
            assert_eq!(g[*id as usize].rhs.as_slice(), *rhs, "rule {id} rhs");
        }
    }

    /// STACK SAFETY — the compact prover and verifier are iterative: a 100k-DEEP body
    /// and a 200k-WIDE body both certify without touching the thread stack. (The chain
    /// prover stays recursive + O(n²) — it is the small-input spec bridge, not the
    /// scale path.)
    #[test]
    fn compact_scales_deep_and_wide() {
        // 100k-deep nesting.
        let depth = 100_000;
        let mut deep = String::with_capacity(2 * depth + 1);
        for _ in 0..depth {
            deep.push('[');
        }
        deep.push('1');
        for _ in 0..depth {
            deep.push(']');
        }
        let cert = prove_cfg_compact(deep.as_bytes()).expect("deep body certifies");
        verify_cfg_compact(&cert, deep.as_bytes()).expect("deep cert verifies");

        // 200k-wide array.
        let elems: Vec<&str> = (0..200_000).map(|_| "7").collect();
        let wide = format!("[{}]", elems.join(","));
        let cert = prove_cfg_compact(wide.as_bytes()).expect("wide body certifies");
        assert!(
            cert.rules.len() < 3 * 200_000 + 8,
            "compact cert stays O(tokens)"
        );
        verify_cfg_compact(&cert, wide.as_bytes()).expect("wide cert verifies");
    }
}
