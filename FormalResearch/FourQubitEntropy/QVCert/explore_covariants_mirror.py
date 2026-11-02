"""Numerical evidence only: a naive floating-point mirror of the Lean definitions of `Covariants.lean`.

It follows the Lean transcription literally (`rowC`, `ztilde`, `sixCopy` with copy `k` at bit `5 - k`,
`sectorW` with row `(p_k, m_k, mu_k)` in slot `sigma k`, `muDigit`, `wp`, `Block.Phi`, `Block.normSqPhi`) and checks
the certificate identity `2 D 𝔇(z) = Σ_{k,i} q_ki ‖Φ_ki(z)‖²_w` at random complex vectors `z` (relative error ~1e-15).
This confirms that the Lean definitions reproduce the verifier `verify_qv_all_state_certificate.py`; it proves nothing.
Needs numpy; about 10 s.

    python3 explore_covariants_mirror.py [path/to/qv_all_state_certificate.json]
"""
import os
import itertools
import json
import sys
from math import comb, factorial, lcm, prod
from pathlib import Path

import numpy as np

DEFAULT = Path(os.environ.get('QIPROJECTS', '../QIprojects')) / 'ResearchNotes/QI/four_qubit_entropy/code/qv_all_state_certificate.json'  # format qv-positive-norms-v1
DATA = json.loads((Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT).read_text())
mult = {j: len(DATA['highest_weight_supports'][str(j)]) for j in (0, 2, 4, 6)}


def lower_op(v):                                   # lowerOp
    return np.array([sum(v[b ^ (1 << k)] for k in range(6) if (b >> k) & 1) for b in range(64)])


def hw_vec(j, mu):                                 # hwVec
    neg, pos = DATA['highest_weight_supports'][str(j)][mu]
    v = np.zeros(64, dtype=np.int64)
    v[neg], v[pos] = -1, 1
    return v


def row_c(j, m, mu):                               # rowC j m mu (all b)
    v = hw_vec(j, mu)
    for _ in range(m):
        v = lower_op(v)
    return v // factorial(m)


ROWC = {(j, m, mu): row_c(j, m, mu) for j in (0, 2, 4, 6) for m in range(j + 1) for mu in range(mult[j])}


def ztilde(z):                                     # z : (2,2,2,2); ztilde = (-1)^(a+b+c+d) conj z(rev)
    sign = np.fromfunction(lambda a, b, c, d: (-1.0) ** (a + b + c + d), (2, 2, 2, 2))
    return sign * np.conj(z[::-1, ::-1, ::-1, ::-1])


def six_copy(a, z):                                # sixCopy a z, as a (64,64,64,64) array
    zt = ztilde(z)
    L = 'abcdefghijklmnopqrstuvwx'
    idx = [[L[4 * k + q] for q in range(4)] for k in range(6)]
    out = ''.join(idx[k][q] for q in range(4) for k in range(5, -1, -1))   # einsum label k = bit k
    ops = [z if 5 - k < a else zt for k in range(6)]                       # Lean copy 5-k sits at bit k
    return np.einsum(','.join(''.join(i) for i in idx) + '->' + out, *ops, optimize=True).reshape(64, 64, 64, 64)


def apply_c6(Z):                                   # contraction with C6 (rows ordered j, m, mu) in every slot
    C6 = np.array([ROWC[(j, m, mu)] for j in (0, 2, 4, 6) for m in range(j + 1) for mu in range(mult[j])],
                  dtype=complex)
    for ax in range(4):
        Z = np.moveaxis(np.tensordot(C6, Z, axes=(1, ax)), 0, ax)
    return Z


OFFSET = {}
o = 0
for j in (0, 2, 4, 6):
    OFFSET[j] = o
    o += (j + 1) * mult[j]


def block_norms(W, blk):                           # Block.normSqPhi for every covariant i of the block
    p = blk['spins']
    mults = [mult[j] for j in p]
    wt = {(j, m): lcm(*(comb(j, r) for r in range(j + 1))) // comb(j, m) for j in p for m in range(j + 1)}
    out = np.zeros(len(blk['weights']))
    for sigma in itertools.permutations(range(4)):
        for ms in itertools.product(*[range(j + 1) for j in p]):
            w = prod(wt[(p[k], ms[k])] for k in range(4))
            cache = {}

            def col(c):                            # sectorW at flat multiplicity index c (muDigit)
                if c not in cache:
                    mus = [(c // prod(mults[k + 1:])) % mults[k] for k in range(4)]
                    rows = [0] * 4
                    for k in range(4):
                        rows[sigma[k]] = OFFSET[p[k]] + ms[k] * mults[k] + mus[k]
                    cache[c] = W[tuple(rows)]
                return cache[c]
            for i, v in enumerate(blk['vectors']):
                phi = sum(v[t + 1] * col(v[t]) for t in range(0, len(v), 2))
                out[i] += w * abs(phi) ** 2
    return out


def defect_d(z):                                   # defectD (homogeneous, any norm)
    t = z.reshape(2, 2, 2, 2)
    n = np.sum(abs(z) ** 2)
    ps, ts = [], []
    for j in (1, 2, 3):
        X = t.transpose([0, j] + [k for k in (1, 2, 3) if k != j]).reshape(4, 4)
        R = X @ X.conj().T
        ps.append(np.trace(R @ R).real)
        ts.append(np.trace(R @ R @ R).real)
    P, T, U = sum(ps), sum(ts), sum(p * p for p in ps)
    F = 17 * n * P - 12 * T - 12 * n ** 3
    return F * F + 5 * n * n * P * P - 3 * n ** 4 * P - 6 * n * n * U


if __name__ == '__main__':
    rng = np.random.default_rng(7)
    D = float(DATA['denominator'])
    for trial in range(2):
        z = (rng.normal(size=16) + 1j * rng.normal(size=16)).reshape(2, 2, 2, 2)
        W = {a: apply_c6(six_copy(a, z)) for a in (3, 4)}
        total = 0.0
        for blk in DATA['blocks']:
            total += float(np.dot([float(q) for q in blk['weights']], block_norms(W[blk['a']], blk)))
        lhs = 2 * D * defect_d(z.reshape(16))
        print(f'trial {trial}: 2 D defect = {lhs:.12e}, sum q ||Phi||^2 = {total:.12e}, rel err {abs(total - lhs) / abs(lhs):.2e}')
        assert abs(total - lhs) <= 1e-9 * abs(lhs)
    print('mirror OK')
