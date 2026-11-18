import json, os, random, sys, urllib.error, urllib.request

U = os.environ.get("MAKEFUN_ENV_URL") or sys.exit("MAKEFUN_ENV_URL missing")
BG = 100000
MT = 100000
INF = 10 ** 9
OP = 7800
V = [0, 100, 320, 330, 500, 900, 0]
_c = lambda f, r: min(f, 7 - f) + min(r, 7 - r)
_AD = [0, 0, 5, 10, 18, 30, 50, 0]
_CE = [0, 0, 0, 8, 14, 8, 0, 0]
PS = [[0] * 64 for _ in range(7)]
KM = [0] * 64
KE = [0] * 64
for _r in range(8):
    for _f in range(8):
        _i = _r * 8 + _f
        _cc = _c(_f, _r)
        PS[1][_i] = _AD[_r] + (_CE[_r] if _f in (3, 4) else 0)
        PS[2][_i] = 5 * _cc - 18
        PS[3][_i] = 4 * _cc - 6
        PS[4][_i] = (12 if _r == 6 else 0) + (4 if _r == 0 and _f in (3, 4) else 0)
        PS[5][_i] = 2 * _cc - 4
        KM[_i] = [15, 20, 8, 0, 0, 8, 20, 15][_f] if _r == 0 else max(-40, -12 * _r)
        KE[_i] = 6 * _cc - 18
KN = [33, 31, 18, 14, -14, -18, -31, -33]
KI = [1, -1, 16, -16, 15, 17, -15, -17]
BI = [15, 17, -15, -17]
RO = [1, -1, 16, -16]
CK = [15] * 128
CK[0] = 13; CK[7] = 14; CK[4] = 12; CK[112] = 7; CK[119] = 11; CK[116] = 3
_rg = random.Random(20261118)
Z = [[_rg.getrandbits(64) for _ in range(128)] for _ in range(12)]
ZS = _rg.getrandbits(64)
B = [0] * 128
sd = 0
cs = 0
ep = -1
kg = [4, 116]
S = 0
np = OP
bp = [2, 2]
H = 0
ud = []
nd = 0
TT = {}
KL = [[0, 0] for _ in range(512)]

class Ab(Exception):
    pass

def rl(sq, w):
    return (sq >> 4) * 8 + (sq & 7) if w else (7 - (sq >> 4)) * 8 + (sq & 7)

def zi(p):
    return (abs(p) - 1) + (0 if p > 0 else 6)

def st(fen):
    global sd, cs, ep, S, np, H
    p = fen.split()
    for i in range(128):
        B[i] = 0
    S = 0; np = 0; H = 0
    bp[0] = bp[1] = 0
    for r, row in enumerate(p[0].split("/")):
        f = 0
        for ch in row:
            if ch.isdigit():
                f += int(ch)
            else:
                t = "pnbrqk".index(ch.lower()) + 1
                pc = t if ch.isupper() else -t
                sq = (7 - r) * 16 + f
                B[sq] = pc
                H ^= Z[zi(pc)][sq]
                if t == 6:
                    kg[0 if pc > 0 else 1] = sq
                else:
                    w = 1 if pc > 0 else 0
                    v = V[t] + PS[t][rl(sq, w)]
                    S += v if w else -v
                    if t != 1:
                        np += V[t]
                    if t == 3:
                        bp[w] += 1
                f += 1
    sd = 0 if p[1] == "w" else 1
    if sd:
        H ^= ZS
    cs = 0
    if len(p) > 2:
        for ch in p[2]:
            cs |= {"K": 1, "Q": 2, "k": 4, "q": 8}.get(ch, 0)
    ep = -1
    if len(p) > 3 and p[3] != "-":
        ep = (ord(p[3][1]) - 49) * 16 + (ord(p[3][0]) - 97)

def atk(sq, byw):
    for d in (-15, -17) if byw else (15, 17):
        s = sq + d
        if not s & 0x88 and B[s] == (1 if byw else -1):
            return 1
    for d in KN:
        s = sq + d
        if not s & 0x88 and B[s] == (2 if byw else -2):
            return 1
    for d in KI:
        s = sq + d
        if not s & 0x88 and B[s] == (6 if byw else -6):
            return 1
    for d in BI:
        s = sq + d
        while not s & 0x88:
            pc = B[s]
            if pc:
                if pc == (3 if byw else -3) or pc == (5 if byw else -5):
                    return 1
                break
            s += d
    for d in RO:
        s = sq + d
        while not s & 0x88:
            pc = B[s]
            if pc:
                if pc == (4 if byw else -4) or pc == (5 if byw else -5):
                    return 1
                break
            s += d
    return 0

def gn(caps):
    ms = []
    w = sd == 0
    d = 16 if w else -16
    sr = 1 if w else 6
    pr = 6 if w else 1
    for sq in range(128):
        if sq & 0x88:
            continue
        pc = B[sq]
        if not pc or (pc > 0) != w:
            continue
        t = abs(pc)
        if t == 1:
            fw = sq + d
            if not caps and B[fw] == 0:
                if (sq >> 4) == pr:
                    for q in (5, 2, 4, 3):
                        ms.append(sq | fw << 7 | q << 14)
                else:
                    ms.append(sq | fw << 7)
                    if (sq >> 4) == sr and B[fw + d] == 0:
                        ms.append(sq | (fw + d) << 7)
            for dd in (d - 1, d + 1):
                to = sq + dd
                if to & 0x88:
                    continue
                q = B[to]
                if q and (q > 0) != w or to == ep:
                    if (sq >> 4) == pr:
                        for qq in (5, 2, 4, 3):
                            ms.append(sq | to << 7 | qq << 14)
                    else:
                        ms.append(sq | to << 7)
        elif t == 2 or t == 6:
            for dd in KN if t == 2 else KI:
                to = sq + dd
                if to & 0x88:
                    continue
                q = B[to]
                if not q or (q > 0) != w:
                    if not caps or q:
                        ms.append(sq | to << 7)
        else:
            dirs = BI if t == 3 else RO if t == 4 else BI + RO
            for dd in dirs:
                to = sq + dd
                while not to & 0x88:
                    q = B[to]
                    if not q:
                        if not caps:
                            ms.append(sq | to << 7)
                    else:
                        if (q > 0) != w:
                            ms.append(sq | to << 7)
                        break
                    to += dd
    if not caps:
        if w:
            if cs & 1 and not B[5] and not B[6] and B[7] == 4 and not atk(4, 0) and not atk(5, 0) and not atk(6, 0):
                ms.append(4 | 6 << 7)
            if cs & 2 and not B[3] and not B[2] and not B[1] and B[0] == 4 and not atk(4, 0) and not atk(3, 0) and not atk(2, 0):
                ms.append(4 | 2 << 7)
        else:
            if cs & 4 and not B[117] and not B[118] and B[119] == -4 and not atk(116, 1) and not atk(117, 1) and not atk(118, 1):
                ms.append(116 | 118 << 7)
            if cs & 8 and not B[115] and not B[114] and not B[113] and B[112] == -4 and not atk(116, 1) and not atk(115, 1) and not atk(114, 1):
                ms.append(116 | 114 << 7)
    return ms

def mk(m):
    global sd, cs, ep, S, np, H
    f = m & 127
    t = (m >> 7) & 127
    pr = (m >> 14) & 7
    pc = B[f]
    w = pc > 0
    t0 = abs(pc)
    sg = 1 if w else -1
    cap = B[t]
    csq = -1
    if t0 == 1 and not cap and t == ep:
        csq = t - 16 if w else t + 16
        cap = B[csq]
    ud.append((m, cap, csq, cs, ep, H, S, np, kg[0], kg[1], bp[0], bp[1]))
    H ^= Z[zi(pc)][f] ^ ZS
    B[f] = 0
    if t0 != 6:
        S -= (V[t0] + PS[t0][rl(f, w)]) * sg
    if cap:
        ct = abs(cap)
        cw = cap > 0
        cq = csq if csq >= 0 else t
        H ^= Z[zi(cap)][cq]
        if ct != 6:
            S -= (V[ct] + PS[ct][rl(cq, cw)]) * (1 if cw else -1)
            if ct != 1:
                np -= V[ct]
            if ct == 3:
                bp[0 if cw else 1] -= 1
        if csq >= 0:
            B[csq] = 0
    nt = pr if pr else t0
    if pr:
        np += V[pr]
        if pr == 3:
            bp[0 if w else 1] += 1
    npc = nt if w else -nt
    H ^= Z[zi(npc)][t]
    B[t] = npc
    if t0 != 6:
        S += (V[nt] + PS[nt][rl(t, w)]) * sg
    if t0 == 6:
        kg[0 if w else 1] = t
        if abs(t - f) == 2:
            rf = 7 if t > f else 0
            rt = 5 if t > f else 3
            if not w:
                rf += 112
                rt += 112
            rp = B[rf]
            H ^= Z[zi(rp)][rf] ^ Z[zi(rp)][rt]
            B[rf] = 0
            B[rt] = rp
            S += (PS[4][rl(rt, w)] - PS[4][rl(rf, w)]) * sg
    cs &= CK[f] & CK[t]
    ep = (t - 16 if w else t + 16) if t0 == 1 and abs(t - f) == 32 else -1
    sd = 1 - sd

def um():
    global sd, cs, ep, S, np, H
    m, cap, csq, cs, ep, H, S, np, k0, k1, b0, b1 = ud.pop()
    f = m & 127
    t = (m >> 7) & 127
    pr = (m >> 14) & 7
    pc = B[t]
    if pr:
        B[f] = 1 if pc > 0 else -1
    else:
        B[f] = pc
    B[t] = 0
    if cap:
        B[csq if csq >= 0 else t] = cap
    if abs(pc) == 6 and abs(t - f) == 2:
        rt = 5 if t > f else 3
        rf = 7 if t > f else 0
        if pc < 0:
            rf += 112
            rt += 112
        B[rf] = B[rt]
        B[rt] = 0
    kg[0] = k0
    kg[1] = k1
    bp[0] = b0
    bp[1] = b1
    sd = 1 - sd

def ev():
    ph = np if np < OP else OP
    kw = (KM[rl(kg[0], 1)] * ph + KE[rl(kg[0], 1)] * (OP - ph)) // OP
    kb = (KM[rl(kg[1], 0)] * ph + KE[rl(kg[1], 0)] * (OP - ph)) // OP
    s = S + kw - kb + (30 if bp[0] >= 2 else 0) - (30 if bp[1] >= 2 else 0)
    return s if sd == 0 else -s

def od(ms, tt, ply):
    k = KL[ply & 511]

    def key(m):
        f = m & 127
        t = (m >> 7) & 127
        if m == tt:
            return 1 << 24
        if B[t]:
            return 100000 + 10 * V[abs(B[t])] - V[abs(B[f])]
        if (m >> 14) & 7:
            return 90000 + V[(m >> 14) & 7]
        if m == k[0]:
            return 80000
        if m == k[1]:
            return 70000
        return 0
    ms.sort(key=key, reverse=True)
    return ms

def qs(a, b, ply):
    global nd
    nd += 1
    if nd > BG:
        raise Ab
    chk = atk(kg[sd], sd)
    if not chk:
        st = ev()
        if st >= b:
            return b
        if st > a:
            a = st
    else:
        st = -INF
    ms = od(gn(0 if chk else 1), 0, ply)
    lg = 0
    for m in ms:
        if not chk:
            t = (m >> 7) & 127
            pr = (m >> 14) & 7
            if st + V[abs(B[t])] + (V[pr] - 100 if pr else 0) + 100 < a:
                continue
        mk(m)
        if atk(kg[1 - sd], 1 - sd):
            um()
            continue
        lg += 1
        s = -qs(-b, -a, ply + 1)
        um()
        if s >= b:
            return b
        if s > a:
            a = s
    if chk and not lg:
        return -MT + ply
    return a

def ab(d, a, b, ply):
    global nd, sd, ep, H
    nd += 1
    if nd > BG:
        raise Ab
    if d <= 0:
        return qs(a, b, ply)
    e = TT.get(H)
    tt = 0
    if e and e[0] >= d:
        sc, fl, tt = e[1], e[2], e[3]
        if sc > MT - 1000:
            sc -= ply
        elif sc < -MT + 1000:
            sc += ply
        if fl == 0:
            return sc
        if fl == 1 and sc >= b:
            return sc
        if fl == 2 and sc <= a:
            return sc
    chk = atk(kg[sd], sd)
    if not chk and d >= 3 and np > 900 and ev() >= b:
        e0, h0 = ep, H
        ep = -1
        H ^= ZS
        sd = 1 - sd
        s = -ab(d - 3, -b, -b + 1, ply + 1)
        sd = 1 - sd
        ep, H = e0, h0
        if s >= b:
            return s
    ms = od(gn(0), tt, ply)
    best = -INF
    bm = 0
    lg = 0
    al = a
    for i, m in enumerate(ms):
        t = (m >> 7) & 127
        cap = B[t] != 0 or ((m >> 14) & 7) != 0
        mk(m)
        if atk(kg[1 - sd], 1 - sd):
            um()
            continue
        lg += 1
        if i == 0:
            s = -ab(d - 1, -b, -al, ply + 1)
        elif i > 3 and d >= 3 and not cap and not chk:
            s = -ab(d - 2, -al - 1, -al, ply + 1)
            if s > al:
                s = -ab(d - 1, -b, -al, ply + 1)
        else:
            s = -ab(d - 1, -al - 1, -al, ply + 1)
            if s > al:
                s = -ab(d - 1, -b, -al, ply + 1)
        um()
        if s > best:
            best = s
            bm = m
        if s > al:
            al = s
        if al >= b:
            if not cap:
                k = KL[ply & 511]
                if k[0] != m:
                    k[1] = k[0]
                    k[0] = m
            break
    if not lg:
        return -MT + ply if chk else 0
    fl = 2 if best <= a else 1 if best >= b else 0
    sc = best + ply if best > MT - 1000 else best - ply if best < -MT + 1000 else best
    TT[H] = (d, sc, fl, bm)
    return best

def uc(m):
    f = m & 127
    t = (m >> 7) & 127
    s = "abcdefgh"[f & 7] + str((f >> 4) + 1) + "abcdefgh"[t & 7] + str((t >> 4) + 1)
    pr = (m >> 14) & 7
    return s + ("pnbrqk"[pr - 1] if pr else "")

def ch(fen, lu):
    global nd
    st(fen)
    nd = 0
    TT.clear()
    for i in range(512):
        KL[i][0] = KL[i][1] = 0
    ms = []
    for m in gn(0):
        mk(m)
        if atk(kg[1 - sd], 1 - sd):
            um()
            continue
        um()
        ms.append(m)
    if not ms:
        return lu[0]
    if len(ms) == 1:
        return uc(ms[0])
    bu = {uc(m): m for m in ms}
    if set(bu) != set(lu):
        best = None
        for u in lu:
            to = (ord(u[2]) - 97) + (int(u[3]) - 1) * 16
            v = V[abs(B[to])] if B[to] else 0
            key = (-v, -(V["pnbrqk".index(u[4]) + 1] if len(u) == 5 else 0), u)
            if best is None or key < best[0]:
                best = (key, u)
        return best[1]
    bm = ms[0]
    try:
        for d in range(1, 10):
            e = TT.get(H)
            od(ms, e[3] if e else 0, 0)
            bs = -INF
            dm = bm
            for i, m in enumerate(ms):
                mk(m)
                if i == 0:
                    s = -ab(d - 1, -INF, INF, 1)
                else:
                    s = -ab(d - 1, -bs - 1, -bs, 1)
                    if s > bs:
                        s = -ab(d - 1, -INF, INF, 1)
                um()
                if s > bs:
                    bs = s
                    dm = m
            bm = dm
    except Ab:
        pass
    return uc(bm)

def pt(path, body):
    req = urllib.request.Request(
        U + path, data=json.dumps(body).encode(),
        headers={"content-type": "application/json"})
    try:
        with urllib.request.urlopen(req) as res:
            return json.load(res)
    except urllib.error.HTTPError as e:
        sys.exit(f"{path}: HTTP {e.code} {e.read().decode(errors='replace')}")

def mn():
    while True:
        g = pt("/game", {})
        if g["status"] == "done":
            break
        while g["status"] == "your_move":
            g = pt("/move", {"game": g["game"], "move": ch(g["fen"], g["legal_moves"])})
        print(g["game"], g["outcome"], g["reason"], file=sys.stderr)
    print(g.get("wins"), g.get("draws"), g.get("losses"), file=sys.stderr)

if __name__ == "__main__":
    mn()
