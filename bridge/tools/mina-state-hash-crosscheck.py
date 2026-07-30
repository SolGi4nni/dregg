#!/usr/bin/env python3
"""
`mina-state-hash-crosscheck` -- a SECOND rendering of `state_hash`, in python.

WHAT THIS IS NOT. It is not an independent check of the ORDER. It is the same
author reading the same daemon (~/dev/mina) and the same openmina
(~/dev/mina-rust) a second time, so if that reading is wrong both renderings are
wrong together -- which is exactly how a previous lane's python "confirmed" a bug
it shared. Nothing here validates that `Body.to_input` absorbs what we think it
absorbs.

WHAT IT IS. A typo tripwire over ~38 field elements and ~819 packed chunks: one
transposed, dropped or mis-widthed item between this and
`Dregg2/Bridge/MinaStateHashDerive.lean` shows up as a different digest. Its
outputs are pinned in `Dregg2/Bridge/MinaBinprotRealBlock.lean`
(`the_two_transcriptions_agree_on_the_real_block`), so the agreement is a gate
rather than a one-time observation.

THE ORDER'S ACTUAL GATE is `Dregg2/Bridge/MinaStateHashRealBlock.lean`, built by
`bridge/tools/mina-consecutive-pair.py`, where the comparand is a field of the
wire (`block_{N+1}.previous_state_hash`) rather than anything either
transcription produced.

Reads the 540186 fixture out of the Lean source and the Poseidon constants out of
`Dregg2/Circuit/Emit/PastaPoseidon.lean` -- those constants are themselves
`#guard`-anchored to six o1js gold vectors, so they are not a third rendering.

    bridge/tools/mina-state-hash-crosscheck.py
"""
import re, hashlib
P = 28948022309329048855892746252171976963363056481941560715954676764349967630337
src = open('/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/Emit/PastaPoseidon.lean').read()
def grab(name, n):
    i = src.index('def %s : List (List Nat) :=' % name); j = src.index(']]', i)
    rows = re.findall(r'\[([0-9,\s]+)\]', src[i:j+2])
    return [[int(x) for x in r.replace('\n',' ').split(',') if x.strip()] for r in rows][:n]
MDS = grab('mdsN',3); RC = grab('rcsN',55)
def perm(st):
    for r in range(55):
        s=[pow(x,7,P) for x in st]
        st=[(sum(MDS[j][i]*s[i] for i in range(3))+RC[r][j])%P for j in range(3)]
    return st
def absorb_all(st,xs):
    st=list(st); n=0
    for x in xs:
        if n==2: st=perm(st); st[0]=(st[0]+x)%P; n=1
        else: st[n]=(st[n]+x)%P; n+=1
    return perm(st)
def salt(s):
    b=(s.encode()+b'*'*20)[:20]
    return absorb_all([0,0,0],[int.from_bytes(b,'little')])
SALT_PS, SALT_BODY = salt("MinaProtoState"), salt("MinaProtoStateBody")

# ---------------- binprot reader ----------------
class R:
    def __init__(s,b): s.b=b; s.i=0
    def u8(s):
        v=s.b[s.i]; s.i+=1; return v
    def take(s,n):
        v=s.b[s.i:s.i+n]; assert len(v)==n; s.i+=n; return v
    def nat0(s):
        c=s.u8()
        if c<0x80: return c
        if c==0xfe: n=int.from_bytes(s.take(2),'little'); assert n>=0x80; return n
        if c==0xfd: n=int.from_bytes(s.take(4),'little'); assert n>=0x10000; return n
        if c==0xfc: n=int.from_bytes(s.take(8),'little'); assert n>=0x100000000; return n
        raise ValueError(hex(c))
    def sint(s):
        c=s.u8()
        if c<0x80: return c
        if c==0xff: n=int.from_bytes(s.take(1),'little'); return n-256
        if c==0xfe: n=int.from_bytes(s.take(2),'little'); return n-65536 if n>=0x8000 else n
        if c==0xfd: n=int.from_bytes(s.take(4),'little'); return n-(1<<32) if n>=0x80000000 else n
        if c==0xfc: n=int.from_bytes(s.take(8),'little'); return n-(1<<64) if n>=(1<<63) else n
        raise ValueError(hex(c))
    def u32(s):
        v=s.sint(); assert 0<=v<(1<<32); return v
    def u64(s):
        v=s.sint(); return v if v>=0 else v+(1<<64)
    def fp(s):
        v=int.from_bytes(s.take(32),'little'); assert v<P; return v
    def bs(s,cap):
        n=s.nat0(); assert n<=cap; return s.take(n)
    def unit(s): assert s.u8()==0
    def bool(s):
        v=s.u8(); assert v in (0,1); return v==1
    def var1(s): assert s.u8()==0

def signed(r): return (r.u64(), r.u8()==0)          # (magnitude, isPos)  Sgn: 0=Pos
def local(r):
    d={}
    for k in ('sf','cs','tc','ftc'): d[k]=r.fp()
    d['excess']=signed(r); d['si']=signed(r); d['ledger']=r.fp()
    d['success']=r.bool(); d['idx']=r.u32()
    o=r.nat0()
    for _ in range(o):
        inn=r.nat0()
        for _ in range(inn): r.u8()
    d['will']=r.bool(); return d
def regs(r):
    d={'fp':r.fp(),'sp':r.fp(),'cbd':r.fp(),'cbi':r.fp(),'cbc':r.fp()}
    d['ls']=local(r); return d
def epoch(r):
    return {'lh':r.fp(),'ltc':r.u64(),'seed':r.fp(),'start':r.fp(),'lock':r.fp(),'len':r.u32()}

def decode(b):
    r=R(b); ps={}
    ps['prev']=r.fp(); ps['genesis']=r.fp()
    bc={'slh':r.fp(),'aux':r.bs(4096),'pca':r.bs(4096),'pch':r.fp(),'glh':r.fp()}
    bc['src']=regs(r); bc['tgt']=regs(r)
    bc['cl']=r.fp(); bc['cr']=r.fp(); bc['si']=signed(r)
    bc['fee']={'tl':r.fp(),'fl':signed(r),'tr':r.fp(),'fr':signed(r)}
    r.unit(); bc['ts']=r.u64(); bc['bref']=r.bs(64)
    ps['bc']=bc
    c={'bl':r.u32(),'ec':r.u32(),'mwd':r.u32()}
    n=r.nat0(); assert n==11
    c['dens']=[r.u32() for _ in range(11)]
    c['vrf']=r.bs(64); assert len(c['vrf'])==32
    c['tc']=r.u64(); r.var1(); c['slot']=r.u32(); c['spe']=r.u32()
    r.var1(); c['gsg']=r.u32()
    c['stk']=epoch(r); c['nxt']=epoch(r); c['anc']=r.bool()
    c['w']=(r.fp(),r.bool()); c['cr']=(r.fp(),r.bool()); c['rc']=(r.fp(),r.bool())
    c['sc']=r.bool(); ps['cs']=c
    k={'k':r.u32(),'spe':r.u32(),'spsw':r.u32(),'gps':r.u32(),'delta':r.u32(),'ts':r.u64()}
    ps['k']=k
    return ps, r.i

# ---------------- to_input ----------------
class I:
    def __init__(s): s.f=[]; s.p=[]
    def field(s,x): s.f.append(x); return s
    def pk(s,x,n): s.p.append((x,n)); return s
    def b(s,v): return s.pk(1 if v else 0,1)
    def bytes_(s,bb):
        for by in bb:
            for i in range(8): s.pk((by>>i)&1,1)
        return s
    def fields(s):
        out=[]; acc=0; an=0
        for (x,n) in s.p:
            if n+an < 255: acc = acc*(1<<n) + x; an += n
            else: out.append(acc); acc=x; an=n
        if an>0: out.append(acc)
        return s.f + out

def sgnI(inp,sa): inp.pk(sa[0],64).b(sa[1])
def localI(inp,l):
    inp.field(l['sf']).field(l['cs']).field(l['tc']).field(l['ftc'])
    sgnI(inp,l['excess']); sgnI(inp,l['si'])
    inp.field(l['ledger']).pk(l['idx'],32).b(l['success']).b(l['will'])
def regsI(inp,rg):
    inp.field(rg['fp']).field(rg['sp']).field(rg['cbd']).field(rg['cbi']).field(rg['cbc'])
    localI(inp,rg['ls'])
def epochI(inp,e):
    inp.field(e['seed']).field(e['start']).pk(e['len'],32).field(e['lh']).pk(e['ltc'],64).field(e['lock'])

def body_input(ps):
    inp=I(); k=ps['k']; bc=ps['bc']; c=ps['cs']
    inp.pk(k['k'],32).pk(k['delta'],32).pk(k['spe'],32).pk(k['spsw'],32).pk(k['gps'],32).pk(k['ts'],64)
    inp.field(ps['genesis'])
    dg=hashlib.sha256(bc['slh'].to_bytes(32,'big')+bc['aux']+bc['pca']).digest()
    inp.bytes_(dg).field(bc['pch']).field(bc['glh'])
    regsI(inp,bc['src']); regsI(inp,bc['tgt'])
    inp.field(bc['cl']).field(bc['cr']); sgnI(inp,bc['si'])
    fe=bc['fee']; inp.field(fe['tl']); sgnI(inp,fe['fl']); inp.field(fe['tr']); sgnI(inp,fe['fr'])
    inp.pk(bc['ts'],64); inp.bytes_(bc['bref'])
    inp.pk(c['bl'],32).pk(c['ec'],32).pk(c['mwd'],32)
    for d in c['dens']: inp.pk(d,32)
    inp.bytes_(c['vrf'][:31])
    for i in range(5): inp.pk((c['vrf'][31]>>i)&1,1)
    inp.pk(c['tc'],64).pk(c['slot'],32).pk(c['spe'],32).pk(c['gsg'],32).b(c['anc']).b(c['sc'])
    epochI(inp,c['stk']); epochI(inp,c['nxt'])
    for pkk in (c['w'],c['cr'],c['rc']): inp.field(pkk[0]).b(pkk[1])
    return inp

def state_hash(ps):
    bh = absorb_all(SALT_BODY, body_input(ps).fields())[0]
    return absorb_all(SALT_PS, [ps['prev'], bh])[0]

# ⚑ Guarded so the module can be IMPORTED (by `mina-consecutive-pair.py`, which reuses this
# binprot reader rather than carrying a second one) without running the report.
def main():
    lean = open("/Users/ember/dev/breadstuffs/metatheory/Dregg2/Bridge/MinaBinprotRealBlock.lean").read()
    i = lean.index("def devnetBlock540186 : List Nat := [")
    j = lean.index("]", i)
    nums=[int(x) for x in re.findall(r"\d+", lean[i+len("def devnetBlock540186 : List Nat := ["):j])]
    buf=bytes(nums); print("bytes", len(buf))
    ps, used = decode(buf); print("consumed", used, "of", len(buf))
    print("blockchain_length", ps['cs']['bl'], "densities", ps['cs']['dens'], "total_currency", ps['cs']['tc'])
    inp = body_input(ps)
    print("field elements:", len(inp.f), " packed items:", len(inp.p), " packed bits:", sum(n for _,n in inp.p))
    fs = inp.fields(); print("poseidon input length:", len(fs))
    print("max packed chunk < p:", all(x < P for x in fs))
    print()
    print("state_body_hash(540186) =", absorb_all(SALT_BODY, fs)[0])
    print("state_hash(540186)      =", state_hash(ps))
    b2 = bytearray(buf); b2[1068]=27
    ps2,_ = decode(bytes(b2))
    print("state_hash(540187 mut)  =", state_hash(ps2))


if __name__ == "__main__":
    main()
