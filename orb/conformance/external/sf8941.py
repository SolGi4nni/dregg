#!/usr/bin/env python3
"""Clean-room RFC 8941 Structured Fields parser (subset sufficient to validate the
target's emitted structured-field response headers).

This is the HARNESS ORACLE, not the target. It is validated against the imported
reference corpus (see corpus_runner.py --oracle-self-check) so its verdicts on the
target's produced fields can be trusted. It covers the grammar reachable from the
fields the target actually emits (List, Dictionary, Item, Inner List, Parameters,
and the bare-item types) per RFC 8941 §4.2.

Parse entrypoints raise SFParseError on any input the RFC requires to fail.
"""


class SFParseError(Exception):
    pass


class _P:
    def __init__(self, s: str):
        # RFC 8941 §4.2: input is ASCII. Reject anything outside 0x00..0x7f.
        for ch in s:
            if ord(ch) > 0x7F:
                raise SFParseError("non-ASCII octet in field value")
        self.s = s
        self.i = 0

    def eof(self):
        return self.i >= len(self.s)

    def peek(self):
        return self.s[self.i] if self.i < len(self.s) else ""

    def take(self):
        c = self.s[self.i]
        self.i += 1
        return c

    def skip_sp(self):
        # SP only (0x20)
        while self.i < len(self.s) and self.s[self.i] == " ":
            self.i += 1

    def skip_ows(self):
        while self.i < len(self.s) and self.s[self.i] in " \t":
            self.i += 1


# ---- top-level parse (§4.2) ----------------------------------------------------

def parse_list(value: str):
    p = _P(value)
    p.skip_sp()
    out = []
    if p.eof():
        return out
    while True:
        out.append(_parse_item_or_inner_list(p))
        p.skip_ows()
        if p.eof():
            return out
        if p.take() != ",":
            raise SFParseError("expected comma in list")
        p.skip_ows()
        if p.eof():
            raise SFParseError("trailing comma in list")


def parse_dictionary(value: str):
    p = _P(value)
    p.skip_sp()
    # RFC 8941 §4.2.2: duplicate keys — last value wins, first position retained.
    od = {}
    if p.eof():
        return []
    while True:
        key = _parse_key(p)
        if p.peek() == "=":
            p.take()
            member = _parse_item_or_inner_list(p)
        else:
            member = (True, _parse_params(p))
        od[key] = member
        p.skip_ows()
        if p.eof():
            return list(od.items())
        if p.take() != ",":
            raise SFParseError("expected comma in dictionary")
        p.skip_ows()
        if p.eof():
            raise SFParseError("trailing comma in dictionary")


def parse_item(value: str):
    p = _P(value)
    p.skip_sp()
    it = _parse_item(p)
    p.skip_sp()
    if not p.eof():
        raise SFParseError("trailing chars after item")
    return it


# ---- members -------------------------------------------------------------------

def _parse_item_or_inner_list(p: _P):
    if p.peek() == "(":
        return _parse_inner_list(p)
    return _parse_item(p)


def _parse_inner_list(p: _P):
    if p.take() != "(":
        raise SFParseError("inner list must start with (")
    items = []
    while True:
        p.skip_sp()
        if p.peek() == ")":
            p.take()
            params = _parse_params(p)
            return (items, params)
        items.append(_parse_item(p))
        nxt = p.peek()
        if nxt not in (" ", ")"):
            raise SFParseError("inner list items must be SP-separated")
    # unreachable


def _parse_item(p: _P):
    val = _parse_bare_item(p)
    params = _parse_params(p)
    return (val, params)


def _parse_params(p: _P):
    # RFC 8941 §3.1.2: duplicate parameter keys — last value wins, first position kept.
    od = {}
    while p.peek() == ";":
        p.take()
        p.skip_sp()
        key = _parse_key(p)
        if p.peek() == "=":
            p.take()
            val = _parse_bare_item(p)
        else:
            val = True
        od[key] = val
    return list(od.items())


def _parse_key(p: _P):
    c = p.peek()
    if not (c == "*" or c.islower() and c.isalpha()):
        raise SFParseError("key must start with lcalpha or *")
    out = []
    while not p.eof():
        c = p.peek()
        if c.islower() and c.isalpha() or c.isdigit() or c in "_-.*":
            out.append(p.take())
        else:
            break
    return "".join(out)


def _parse_bare_item(p: _P):
    c = p.peek()
    if c == "" :
        raise SFParseError("empty bare item")
    if c == "-" or c.isdigit():
        return _parse_number(p)
    if c == '"':
        return _parse_string(p)
    if c == ":":
        return _parse_byteseq(p)
    if c == "?":
        return _parse_boolean(p)
    if c == "@":
        return _parse_date(p)
    if c == "%":
        return _parse_display_string(p)
    if c.isalpha() or c == "*":
        return _parse_token(p)
    raise SFParseError("unrecognized bare item start %r" % c)


def _parse_number(p: _P):
    sign = 1
    if p.peek() == "-":
        p.take()
        sign = -1
    if not p.peek().isdigit():
        raise SFParseError("number needs a digit")
    digits = []
    is_decimal = False
    while not p.eof():
        c = p.peek()
        if c.isdigit():
            digits.append(p.take())
        elif c == "." and not is_decimal:
            if len(digits) > 12:
                raise SFParseError("too many integer digits before decimal")
            digits.append(p.take())
            is_decimal = True
        else:
            break
    tok = "".join(digits)
    if is_decimal:
        if tok.endswith("."):
            raise SFParseError("decimal ends with dot")
        frac = tok.split(".", 1)[1]
        if len(frac) > 3:
            raise SFParseError("too many fractional digits")
        if len(tok) > 16:
            raise SFParseError("decimal too long")
        return sign * float(tok)
    else:
        if len(tok) > 15:
            raise SFParseError("integer too long")
        return sign * int(tok)


def _parse_string(p: _P):
    if p.take() != '"':
        raise SFParseError("string must start with quote")
    out = []
    while not p.eof():
        c = p.take()
        if c == "\\":
            if p.eof():
                raise SFParseError("dangling escape")
            nxt = p.take()
            if nxt not in ('"', "\\"):
                raise SFParseError("bad escape")
            out.append(nxt)
        elif c == '"':
            return "".join(out)
        elif ord(c) < 0x20 or ord(c) >= 0x7F:
            raise SFParseError("bad char in string")
        else:
            out.append(c)
    raise SFParseError("unterminated string")


def _parse_token(p: _P):
    c = p.peek()
    if not (c.isalpha() or c == "*"):
        raise SFParseError("token start")
    out = [p.take()]
    tchar = set("!#$%&'*+-.^_`|~:/") | set(
        "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")
    while not p.eof():
        c = p.peek()
        if c in tchar:
            out.append(p.take())
        else:
            break
    return {"__type": "token", "value": "".join(out)}


def _parse_byteseq(p: _P):
    if p.take() != ":":
        raise SFParseError("byteseq start :")
    out = []
    while not p.eof():
        c = p.take()
        if c == ":":
            import base64
            try:
                decoded = base64.b64decode("".join(out), validate=True)
            except Exception:
                raise SFParseError("bad base64")
            # Corpus represents byte sequences as base32 of the decoded octets.
            return {"__type": "binary",
                    "value": base64.b32encode(decoded).decode("ascii")}
        out.append(c)
    raise SFParseError("unterminated byte sequence")


def _parse_boolean(p: _P):
    if p.take() != "?":
        raise SFParseError("boolean start")
    c = p.take()
    if c == "1":
        return True
    if c == "0":
        return False
    raise SFParseError("bad boolean")


def _parse_date(p: _P):
    if p.take() != "@":
        raise SFParseError("date start")
    v = _parse_number(p)
    if not isinstance(v, int):
        raise SFParseError("date must be integer")
    return {"__type": "date", "value": v}


def _parse_display_string(p: _P):
    if p.take() != "%":
        raise SFParseError("display string start")
    if p.take() != '"':
        raise SFParseError("display string needs quote")
    out = bytearray()
    while not p.eof():
        c = p.take()
        if c == "%":
            h = p.take() + p.take()
            if any(x not in "0123456789abcdef" for x in h):
                raise SFParseError("pct escape must be lowercase hex")
            out.append(int(h, 16))
        elif c == '"':
            try:
                return {"__type": "displaystring", "value": out.decode("utf-8")}
            except Exception:
                raise SFParseError("bad utf8 in display string")
        elif ord(c) < 0x20 or ord(c) >= 0x7F:
            raise SFParseError("bad char in display string")
        else:
            out.extend(c.encode("ascii"))
    raise SFParseError("unterminated display string")
