"""Generate `QVCheckImpl/DataStr.lean` (repository root): the auxiliary certificate data for the precompiled checker (all integers).

    python3 gen_qvcheck_data.py KCERT_DIR [OUT.lean]

KCERT_DIR holds `cert.json` (the QV certificate, identical to Paper E's `qv_all_state_certificate.json`) and `aux.json`
(3.2 MB, not committed): the auxiliary data of the search that found the Route D certificate.  Everything emitted is
untrusted data that the checker `QVCheckImpl` re-verifies, so the proof does not depend on how it was found; the committed
`QVCheckImpl/DataStr.lean` is the data actually checked.  Its module header (`HEADER` below) says how each piece of
`aux.json` can be recomputed.  Spins are indexed by `j/2 in {0,1,2,3}`.
"""
import json, sys, itertools
from math import comb, lcm, gcd
from fractions import Fraction
import numpy as np
from flint import fmpz_mat

cdir = sys.argv[1]
out = sys.argv[2] if len(sys.argv) > 2 else "QVCheckImpl/DataStr.lean"  # run from the repository root
CERT = json.load(open(cdir + '/cert.json')); AUX = json.load(open(cdir + '/aux.json'))
SP = (0, 2, 4, 6); MULT = {0: 5, 2: 9, 4: 5, 6: 1}
I64 = object
def dims(p): return tuple(MULT[j] for j in p)
def sdim(p): return int(np.prod(dims(p)))
# --- C
raising = np.zeros((64, 64), dtype=I64)
for b in range(64):
    for k in range(6):
        if (b >> k) & 1: raising[b ^ (1 << k), b] = 1
raising = np.array(raising, dtype=object)
rows = []
for j in SP:
    sup = CERT['highest_weight_supports'][str(j)]
    H = np.zeros((len(sup), 64), dtype=object)
    for row, (neg, pos) in zip(H, sup):
        row[:] = 0; row[neg] = -1; row[pos] = 1
    rows.append(H)
    for k in range(1, j + 1):
        H = H @ raising; assert not (H % k).any(); H = H // k; rows.append(H)
C = np.concatenate(rows); assert C.shape == (64, 64)
Cm = fmpz_mat(64, 64, [int(x) for x in C.ravel()])
Ci = Cm.inv()   # fmpq_mat
dens = 1
for i in range(64):
    for j in range(64): dens = lcm(dens, int(Ci[i, j].q))
Cinv = [[int(Ci[i, j] * dens) for j in range(64)] for i in range(64)]
for i in range(64):
    for j in range(64): assert Cinv[i][j] == int(Ci[i, j].p * (dens // int(Ci[i, j].q)))
# --- sectors
SEC = {tuple(int(x) // 2 for x in k.split(',')): v for k, v in AUX['sectors'].items()}
def code(p): return ((p[0] * 4 + p[1]) * 4 + p[2]) * 4 + p[3]
secs = sorted(SEC, key=code)
LAB = list(AUX['N'].keys())
NL = {l: [int(x) for x in v] for l, v in AUX['N'].items()}
LC = 1
for v in NL.values():
    for x in v: LC = lcm(LC, x)
WC = {l: [NL[l][x] * (LC // NL[l][0]) for x in range(len(NL[l]))] for l in LAB}
VC = {l: [NL[l][0] * (LC // NL[l][x]) for x in range(len(NL[l]))] for l in LAB}
PAIR = {}
for key, d in AUX['pairs'].items():
    j0, j1 = (int(x) // 2 for x in key.split(','))
    off = {}; o = 0; lay = []
    for l, dd, g in d['layout']:
        off[l] = (o, dd, g); o += dd * g; lay.append((LAB.index(l), dd, g))
    PAIR[(j0, j1)] = dict(T=np.array(d['T'], dtype=object), Ti=np.array(d['Tinv'], dtype=object), delta=int(d['delta']), off=off, lay=lay,
                          D=MULT[SP[j0]] * MULT[SP[j1]])
def rat_cert(A):
    """A: n x n integer matrix (list of lists). returns (U, c) with U A = c I, c>0"""
    n = len(A)
    M = [[Fraction(int(A[i][j])) for j in range(n)] + [Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        pr = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[pr] = M[pr], M[c]
        iv = 1 / M[c][c]; M[c] = [x * iv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    inv = [row[n:] for row in M]; cc = 1
    for row in inv:
        for x in row: cc = lcm(cc, x.denominator)
    return [[int(x * cc) for x in row] for row in inv], cc
def pivots(Mx):
    n, D = len(Mx), len(Mx[0]); P = 2147483647
    A = [[int(x) % P for x in row] for row in Mx]; piv = []; r = 0
    for c in range(D):
        if r == n: break
        pr = next((i for i in range(r, n) if A[i][c]), None)
        if pr is None: continue
        A[r], A[pr] = A[pr], A[r]; iv = pow(A[r][c], -1, P); A[r] = [x * iv % P for x in A[r]]
        for i in range(n):
            if i != r and A[i][c]:
                f = A[i][c]; A[i] = [(x - f * y) % P for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    assert r == n; return piv
V_all = []; W_all = []; PIVV = []; PIVW = []; UV = []; UW = []; CV = []; CW = []; OM = []; XI = []
for p in secs:
    V = SEC[p]['V']; W = SEC[p]['W']; n = len(V)
    V_all += [x for r in V for x in r]; W_all += [x for r in W for x in r]
    for (M, PV, UL, CL) in ((V, PIVV, UV, CV), (W, PIVW, UW, CW)):
        pv = pivots(M); PV += pv
        sub = [[M[b][c] for b in range(n)] for c in pv]      # rows = pivots, cols = b
        U, c = rat_cert(sub); UL += [x for r in U for x in r]; CL.append(c)
    # structure: Omega, Xi
    tpA, tpB = (p[0], p[1]), (p[2], p[3]); PA, PB = PAIR[tpA], PAIR[tpB]
    common = [l for l in PA['off'] if l in PB['off']]
    for b in range(n):
        Vp = PA['T'] @ np.array(V[b], dtype=object).reshape(PA['D'], PB['D']) @ PB['T'].T
        Wp = PA['Ti'].T @ np.array(W[b], dtype=object).reshape(PA['D'], PB['D']) @ PB['Ti']
        om = []; xi = []
        for l in common:
            oa, d, gA = PA['off'][l]; ob, _, gB = PB['off'][l]
            bv = Vp[oa:oa + gA, ob:ob + gB]; bw = Wp[oa:oa + gA, ob:ob + gB]
            xi += [int(x) for x in bv.ravel()]; om += [int(x) for x in bw.ravel()]
        OM += om; XI += xi
PL = []
perms4 = list(itertools.permutations(range(4)))
for p in secs:
    pp = tuple(2 * x for x in p)
    for pi in perms4:
        d = AUX['placements'][','.join(map(str, pp)) + '|' + ','.join(map(str, pi))]
        PL += [int(d['den'])] + [x for r in d['SW'] for x in r] + [x for r in d['SV'] for x in r]
def S(xs):
    s = ','.join(str(int(x)) for x in xs)
    return '"' + '\\\n'.join(s[i:i + 4000] for i in range(0, len(s), 4000)) + '"'
HEADER = """module

/-!
# Auxiliary data of the QV checker

Integer data for `QVCheckImpl.checkAll`, generated by a script from the QV certificate (`QVCert`, the all-state
certificate of the paper) and auxiliary data from the search that produced it.  It is untrusted: `checkAll` re-verifies
every property below, so any data passing the checks gives the same theorem, and the data can be recomputed from these
descriptions (choices of bases and normalisations are free, up to the checks).

* `cS`, `cinvS`, `cDen`: the six-copy intertwiner `C` (`QVCert.rowC`): rows `(j, k, mu)`, `j in {0,2,4,6}` twice the
  spin, multiplicities `m = (5, 9, 5, 1)`; row `(j, 0, mu)` is the highest-weight vector given by the certificate's
  supports, row `(j, k, mu)` is that row times `R^k / k!` (`R` the raising operator); `C * Cinv = cDen * 1`.
* `rhoS`: integer matrices `rho_j(s_i)` of the five adjacent transpositions of `S_6` on the multiplicity spaces, defined
  by `C Pi_{s_i} = (⊕_j rho_j(s_i) ⊗ 1) C`.
* `psiS`: the frame tables `Psi^(a)`, `a in {3, 4}`, defined by `C tau_a(E^j_{mu mu'}) = (⊕ Psi ⊗ 1) C`, with `tau_a` the
  partial transpose-with-`J` of the copies `t >= a` and `E^j_{mu mu'} = Σ_k omega_{jk} C_{(j,k,mu)}ᵀ C_{(j,k,mu')}`.
* `vS`, `wS`: for each spin tuple `p` (one spin per qubit) with `n_p > 0` invariants (code order), integer bases of the
  `S_6`-invariants of `⊗_q rho_{p_q}` (`V`) and of `⊗_q rho_{p_q}ᵀ` (`W`); `n_p` is the character inner product.
* `pivVS`, `pivWS`, `uVS`, `uWS`, `cVS`, `cWS`: for each basis, `n` independent columns and an integer `U` with
  `U · (those columns) = c · 1`, by exact elimination.
* `tS`, `tinvS`, `deltaS`, `layoutS`, `wcS`, `vcS`, `labelDims`, `lc`: for each pair of spins `(j0, j1)`, an integer change
  of basis `T` (with `T Tinv = delta 1`) splitting `rho_{j0} ⊗ rho_{j1}` into `S_6` irreducibles (labels = partitions of
  6, dimensions `labelDims`), each irreducible with multiplicity `g` (layout `(label, d, g)`), normalised so that the
  invariant pairing of two copies of an irreducible is `diag(N[label])` with positive integer weights `N`; stored as
  `wc = Lc N_x / N_0`, `vc = Lc N_0 / N_x` with `Lc = lc` their common multiple.
* `omS`, `xiS`: for each sector, with qubit pairs `A = (0,1)`, `B = (2,3)`, the reshaped invariants become
  `T_A V T_Bᵀ = ⊕_lam diag(N)^{-1} ⊗ Xi_lam` and `Tinv_Aᵀ W Tinv_B = ⊕_lam diag(N) ⊗ Omega_lam` (labels `lam` common to
  both layouts, up to the normalisation `N_0`); `Xi`, `Omega` are the `g^A x g^B` blocks.
* `placeS`: for each sector `p` and permutation `pi` of the four qubits, integer matrices `SW`, `SV` and `den` with
  `den · pi(W(p)) = SW · W(pi p)` and the same for `V`.
* `certDen`: the certificate denominator `D`.
-/

@[expose] public section

namespace QVCheck.DataStr

"""
w = open(out, 'w')
w.write(HEADER)
def put(name, doc, xs): w.write('/-- %s -/\ndef %s : String := %s\n\n' % (doc, name, S(xs)))
put('cS', 'The six-copy intertwiner `C`, row-major `64 x 64`.', [int(x) for x in C.ravel()])
put('cinvS', '`Cinv` with `C * Cinv = cDen * 1`.', [x for r in Cinv for x in r])
w.write('/-- Denominator of `Cinv`. -/\ndef cDen : Int := %d\n\n' % dens)
RHO = []
for j in SP:
    for i in range(5): RHO += [x for r in AUX['rho'][str(j)][i] for x in r]
put('rhoS', 'The generators `rho_j(s_i)`, order `(j, i)`, row-major.', RHO)
PSI = []
for a in (3, 4):
    for j in SP:
        for jp in SP:
            PSI += list(np.array(AUX['psi'][str(a)]['%d,%d' % (j, jp)], dtype=object).ravel())
put('psiS', 'The frame tables `Psi`, order (a in {3,4}, j, jp) then [mu][mup][nu][nup].', PSI)
put('vS', 'Right invariant bases of all sectors (code order), `n x D` each.', V_all)
put('wS', 'Left invariant bases of all sectors (code order), `n x D` each.', W_all)
put('pivVS', 'Pivot columns of `V` (`n` per sector).', PIVV); put('pivWS', 'Pivot columns of `W`.', PIVW)
put('uVS', 'Left-inverse certificates for `V` (`n x n` per sector).', UV); put('uWS', 'Left-inverse certificates for `W`.', UW)
put('cVS', 'Scalars `c` with `U Vpiv = c I`.', CV); put('cWS', 'Scalars `c` for `W`.', CW)
put('omS', 'Coordinates `Omega` (`n x n` per sector) of the coupled `W`.', OM); put('xiS', 'Coordinates `Xi` of the coupled `V`.', XI)
TT = []; TI = []; LY = []; DL = []
for j0 in range(4):
    for j1 in range(4):
        P = PAIR[(j0, j1)]; TT += [int(x) for x in P['T'].ravel()]; TI += [int(x) for x in P['Ti'].ravel()]; DL.append(P['delta'])
        LY += [len(P['lay'])] + [x for t in P['lay'] for x in t]
put('tS', 'The pair transforms `T` (pairs `(j0, j1)`, row-major).', TT); put('tinvS', 'The pair transforms `Tinv`.', TI)
put('deltaS', 'The scalars `delta` with `T Tinv = delta I`.', DL)
put('layoutS', 'Pair layouts: count then `(label, d, g)` triples.', LY)
put('wcS', 'Weights `wc[label][x]` (labels in `aux` order, lengths `d`).', [x for l in LAB for x in WC[l]])
put('vcS', 'Weights `vc[label][x]`.', [x for l in LAB for x in VC[l]])
w.write('/-- `d` of each label. -/\ndef labelDims : List Nat := %s\n\n/-- The common multiple `Lc`. -/\ndef lc : Int := %d\n\n' % ([len(NL[l]) for l in LAB], LC))
put('placeS', 'Placements per `(sector, pi)`: `den`, `SW`, `SV`.', PL)
w.write('/-- The constant `D`. -/\ndef certDen : Int := %d\n\n' % int(CERT['denominator']))
w.write('end QVCheck.DataStr\n'); w.close()
print('wrote', out)
