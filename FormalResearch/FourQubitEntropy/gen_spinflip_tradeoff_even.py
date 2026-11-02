"""Generate the data modules of the even-n purity--spin-flip tradeoff (`thm:purity-spinflip-tradeoff`, ST-2..ST-6):
  SpinFlipTradeoffEvenCert.lean     the dual certificates `tradeoffBound<n>` (n = 8, 10, 14, 16, 20)
  SpinFlipTradeoffEvenGraphA.lean   sharp graph states, n = 8, 10, 14
  SpinFlipTradeoffEvenGraph16.lean, SpinFlipTradeoffEvenGraph20.lean   sharp graph states, n = 16, 20
Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex` and `code/verify_spinflip_tradeoff.py`
(the `CASES` table: L_n, c_n, multipliers e_s (listed by s = 0, 1, ...), y_i, and the sharpness witnesses).

Certificates: a_{n/2} - L A_0 - c 2^{-n} sum_j (-1)^j A_j = sum_{s<n/2} e_s (a_s - a_{n-s}) + sum_i y_i S_i + sum_j w_j A_j
with y_i >= 0, w_j >= 0.  This script re-checks every certificate in exact `Fraction` arithmetic (independent
re-implementation of a_s and the shadow coefficients) before writing the Lean file; the Lean `lpCheckT` re-checks it
in the kernel.

Graphs (all vertices of odd degree, hence tau_n = 1): n = 8, 10, 14: the spin-flip extension of an (n-1)-vertex graph
(the cycle C_7, C_9, and the 13-vertex graph of `SHARP_WITNESS[14]`), i.e. a new last vertex joined to the vertices of
even degree; n = 16, 20: the circulants C_16(2,3,4,8), C_20(3,4,5,10).  For every graph this script recomputes the rank
histogram of all k-cuts in exact integer arithmetic and asserts mean purity == L_n + c_n.  The Lean modules re-check the
rank sums sum_{|S|=k} 2^{k - rk_2 Gamma[S,S^c]} by `decide +kernel` (bitmask recursion `maskSum`, halved by complement
symmetry for n >= 14).

Run from anywhere: python3 gen_spinflip_tradeoff_even.py   (writes the modules next to this file)."""
import os
from fractions import Fraction as F
from itertools import combinations
from math import comb
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))

# n: (L, c, {s: e_s}, {i: y_i})   -- verify_spinflip_tradeoff.py CASES (zero e_s omitted)
CASES = {
    8: ("3/35", "1/70", {0: "-1/14"}, {1: "1/224", 5: "1/1120"}),
    10: ("1/21", "1/168", {0: "-3/56", 4: "-5/24"},
         {1: "11/2688", 2: "1/504", 3: "47/64512", 7: "11/64512"}),
    14: ("331/27456", "5/6864", {0: "-10/429", 1: "175/3432", 5: "-7/24"},
         {1: "5/13728", 2: "1/6864", 3: "5/109824", 7: "1/219648"}),
    16: ("1/156", "1/1716", {0: "-133/5070", 1: "992/27885", 5: "-448/2145"},
         {1: "18263/57108480", 2: "17/102960", 3: "139/1784640", 4: "1/34320",
          5: "1489/171325440", 9: "21/19036160", 13: "7/11421696"}),
    20: ("1193/739024", "103/1478048",
         {0: "54/4199", 1: "-700/4199", 2: "4725/4862", 3: "-8100/2431", 4: "1050/143",
          5: "-1512/143", 6: "1350/143", 7: "-600/143"},
         {2: "23/1478048", 4: "3/1478048"}),
}
HEX13 = '1850 15ac d62 1412 1e69 c96 915 1e22 1a46 590 2be 11f5 99b'


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def aq(n, s, j):
    return F(choose(n - j, s - j), 2 ** s * comb(n, s))


def shq(n, i, j):
    return F(sum(choose(n - j, r) * 3 ** r * choose(j, i - r) * (-1) ** (j - i + r)
                 for r in range(max(0, i - j), min(i, n - j) + 1)), 2 ** n)


def residual(n, L, c, es, ys):
    k = n // 2
    return [aq(n, k, j) - c * F((-1) ** j, 2 ** n) - (L if j == 0 else 0)
            - sum(e * (aq(n, s, j) - aq(n, n - s, j)) for s, e in es.items())
            - sum(y * shq(n, i, j) for i, y in ys.items()) for j in range(n + 1)]


def parsed(n):
    L, c, es, ys = CASES[n]
    return F(L), F(c), {s: F(v) for s, v in es.items()}, {i: F(v) for i, v in ys.items()}


def rank2(rows):
    piv = {}
    for r in rows:
        while r:
            i = r.bit_length() - 1
            if i not in piv:
                piv[i] = r
                break
            r ^= piv[i]
    return len(piv)


def circ(n, D):
    adj = [0] * n
    for i in range(n):
        for d in D:
            for j in ((i + d) % n, (i - d) % n):
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    return adj


def extension(base):
    """New last vertex joined to the vertices of even degree of `base` (so that every degree is odd)."""
    m = len(base)
    adj = list(base) + [0]
    for i in range(m):
        if bin(base[i]).count("1") % 2 == 0:
            adj[i] |= 1 << m
            adj[m] |= 1 << i
    return adj


def graph(n):
    if n in (8, 10):
        m = n - 1
        return extension([1 << ((i - 1) % m) | 1 << ((i + 1) % m) for i in range(m)]), \
            f"the spin-flip extension of the cycle `C_{m}` (the wheel `W_{m}`)"
    if n == 14:
        return extension([int(x, 16) for x in HEX13.split()]), \
            "the spin-flip extension of the 13-vertex graph of `verify_spinflip_tradeoff.py` (hexadecimal rows)"
    D = {16: [2, 3, 4, 8], 20: [3, 4, 5, 10]}[n]
    return circ(n, D), f"the circulant `C_{n}({', '.join(map(str, D))})`"


LEAF = 2000
MIN_SPLIT_N = 14


def plan(n):
    if n < MIN_SPLIT_N:
        return None, 0
    cuts_ = comb(n, n // 2) // 2
    d = 0
    while cuts_ / 2 ** d > LEAF:
        d += 1
    return "halve", d


def tree(n, k, depth):
    root = (n - 1, k - 1, f"2 ^ {n - 1}")
    leaves, steps = [], []

    def rec(i, kk, m, d, bits):
        if d == 0:
            leaves.append((i, kk, m, bits))
            return
        steps.append((i - 1, kk, kk - 1, m))
        rec(i - 1, kk, m, d - 1, bits + ((i - 1, False),))
        rec(i - 1, kk - 1, f"{m} + 2 ^ {i - 1}", d - 1, bits + ((i - 1, True),))

    rec(*root, depth, ())
    return root, leaves, steps


def check_graph(n, adj, target):
    k = n // 2
    full = (1 << n) - 1
    assert len(adj) == n
    assert all(not (adj[i] >> i) & 1 for i in range(n))
    assert all(((adj[i] >> j) & 1) == ((adj[j] >> i) & 1) for i in range(n) for j in range(n))
    assert all(bin(adj[i]).count("1") % 2 == 1 for i in range(n)), "all degrees must be odd"
    mode, depth = plan(n)
    leaves = tree(n, k, depth)[1] if mode else []
    leafval = {lf[3]: 0 for lf in leaves}
    hist = Counter()
    for S in combinations(range(n), k):
        mask = sum(1 << i for i in S)
        r = rank2([adj[i] & (full ^ mask) for i in S])
        hist[r] += 1
        if mode and (n - 1) in S:
            key = tuple((v, v in S) for v, _ in leaves[0][3])
            leafval[key] += 2 ** (k - r)
    N = sum(cnt * 2 ** (k - r) for r, cnt in hist.items())
    assert F(N, 2 ** k * comb(n, k)) == target, (n, F(N, 2 ** k * comb(n, k)), target)
    if mode:
        assert 2 * sum(leafval.values()) == N
    return N, leafval, dict(sorted(hist.items()))


HEADER = """import FormalResearch.FourQubitEntropy.SpinFlipTradeoffEvenGraphCore

/-!
# Sharpness witnesses of the even-`n` purity--spin-flip tradeoff: %s

GENERATED by `gen_spinflip_tradeoff_even.py`; do not edit.  Source: `spinflip_tradeoff.tex`,
`thm:purity-spinflip-tradeoff` (sharpness clause), `code/verify_spinflip_tradeoff.py` (ST-2--ST-6).

The graph is given by its neighbourhood bitmasks `adjT<n>` (bit `j` of `adjT<n> i` is set iff `i ~ j`);
`adjT<n>_symm`, `adjT<n>_irrefl`, `adjT<n>_odd` check by `decide +kernel` that it is simple and that **every vertex has
odd degree**, so that `tau (gsn Γ) = 1` (`tau_gsn_eq_one`).  `rankSumT<n>` is the kernel-checked sum
`Σ_{|S| = k} 2^{k - rk_2 Γ[S,S^c]}` (bitmask recursion `maskSum`; for `n >= 14` over the cuts containing the last vertex
only, by complement symmetry, `sum_cuts_half`), and `piMean_graphT<n>` the resulting `π_k = L_n + c_n`.
Claim class: exact finite certificate (`decide +kernel`).
-/

open scoped BigOperators
open FormalResearch.FrameFree.NQubit

-- one kernel evaluation at a time: the kernel's cache grows with the number of cuts evaluated
set_option Elab.async false

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip
"""
FOOT = "\nend FormalResearch.FourQubitEntropy.PurityLP\n"


def emit_graph(n, out):
    L, c, _, _ = parsed(n)
    target = L + c
    k = n // 2
    adj, name = graph(n)
    N, leafval, hist = check_graph(n, adj, target)
    out.append(f"/-- Neighbourhood bitmasks of {name} on {n} vertices (all degrees odd). -/")
    out.append(f"def adjT{n}L : List ℕ := {adj}\n")
    out.append(f"/-- The adjacency function of {name} on {n} vertices. -/")
    out.append(f"def adjT{n} : Fin {n} → ℕ := fun i => adjT{n}L.getD i.1 0\n")
    out.append(f"theorem adjT{n}_symm : ∀ i j : Fin {n}, (adjT{n} i).testBit j = (adjT{n} j).testBit i := by\n"
               f"  decide +kernel\n")
    out.append(f"theorem adjT{n}_irrefl : ∀ i : Fin {n}, (adjT{n} i).testBit i = false := by\n  decide +kernel\n")
    out.append(f"/-- Every vertex has odd degree. -/\n"
               f"theorem adjT{n}_odd : ∀ i : Fin {n}, Odd (Finset.univ.filter fun j => adjGraph adjT{n} i j = true).card := by\n"
               f"  decide +kernel\n")
    P = f"((Finset.univ : Finset (Fin {n})).powersetCard {k})"
    full = f"(2 ^ {n} - 1)"
    g = f"(gK {k})"
    mode, depth = plan(n)
    ms = lambda i, kk, m: f"maskSum {g} {n} adjT{n}L {full} {i} {kk} ({m})"
    head = f"theorem rankSumT{n} : ∑ S ∈ {P}, gK {k} (cutRankN adjT{n} S) = {N} := by\n"
    if mode:
        root, leaves, steps = tree(n, k, depth)
        names = []
        for idx, (i, kk, m, bits) in enumerate(leaves):
            out.append(f"theorem leafT{n}_{idx} : {ms(i, kk, m)} = {leafval[bits]} := by\n  decide +kernel\n")
            names.append(f"leafT{n}_{idx}")
        splits = ", ".join([f"maskSum_split {g} {n} adjT{n}L {full} {i} {i + 1} {kk} {kk1} ({m}) rfl rfl"
                            for i, kk, kk1, m in steps] + names)
        p, j = n - 1, k - 1
        out.append(head +
                   f"  refine (sum_cuts_half {g} {n} {k} {p} {j} rfl rfl rfl adjT{n}L adjT{n} (fun i => rfl) "
                   f"adjT{n}_symm {full} rfl).trans ?_\n"
                   f"  rw [{splits}]\n")
    else:
        out.append(head +
                   f"  rw [sum_cuts_eq_maskSum {g} {n} adjT{n}L adjT{n} (fun i => rfl) {full} rfl {k}]\n"
                   f"  decide +kernel\n")
    out.append(f"/-- The graph state of {name} has `π_{k} = L_{n} + c_{n} = {target}` (rank histogram of the cuts, checked by the "
               f"generator: {', '.join(f'rank {r} on {cnt} cuts' for r, cnt in hist.items())}). -/\n"
               f"theorem piMean_graphT{n} : piMean (gsn (adjGraph adjT{n})) {k} = {target.numerator} / {target.denominator} := by\n"
               f"  rw [piMean_gsn adjT{n} adjT{n}_symm {k} {N} (by norm_num) rankSumT{n}]\n"
               f"  norm_num [Nat.choose]\n")


def write(fname, title, ns):
    out = [HEADER % title]
    for n in ns:
        emit_graph(n, out)
    out.append(FOOT)
    with open(os.path.join(HERE, fname), "w") as f:
        f.write("\n".join(out))


def lean_list(d):
    return "[" + ", ".join(f"({s}, ({v.numerator}{'' if v.denominator == 1 else f' / {v.denominator}'} : ℚ))"
                           for s, v in sorted(d.items())) + "]"


def write_certs():
    out = ["""import FormalResearch.FourQubitEntropy.SpinFlipTradeoffEvenLP

/-!
# Dual certificates of the even-`n` purity--spin-flip tradeoff (ST-2--ST-6)

GENERATED by `gen_spinflip_tradeoff_even.py`; do not edit.  Source: `spinflip_tradeoff.tex`,
`thm:purity-spinflip-tradeoff`, certificates ST-2--ST-6 of `code/verify_spinflip_tradeoff.py`.  For
`n ∈ {8, 10, 14, 16, 20}` each `tradeoffBound<n>` states, for **every unit `n`-qubit vector `ψ`**,

  `L_n + c_n τ_n(ψ) ≤ π_{n/2}(ψ)`   (`τ_n = tau ψ`, `π_{n/2} = piMean ψ (n/2)`),

by the exact coefficientwise identity `eq:tradeoff-dual` with rational multipliers `e_s`, `y_i ≥ 0`, residual
`w_j ≥ 0`, checked by `decide +kernel` (`lpCheckT`); the rest is `lp_tradeoff`.  Claim class: proved
(exact-rational certificate).
-/

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FrameFree.NQubit
open FormalResearch.FourQubitEntropy.SpinFlip
"""]
    for n in CASES:
        L, c, es, ys = parsed(n)
        w = residual(n, L, c, es, ys)
        assert w[0] == 0 and all(v >= 0 for v in w) and all(y >= 0 for y in ys.values()), (n, w)
        k = n // 2
        # the generic statement `L + c * tau ≤ piMean ψ k`
        out.append(f"""/-- `thm:purity-spinflip-tradeoff` at `n = {n}` (certificate ST-{[4, 8, 10, 14, 16, 20].index(n) + 1}): `π_{k}(ψ) ≥ {L} + ({c}) τ_{n}(ψ)` for every unit vector.  Residual `w_j = {[str(v) for v in w]}`. -/
theorem tradeoffBound{n} (ψ : Ψ {n}) (hψ : nsq ψ = 1) :
    ({L.numerator} / {L.denominator} : ℝ) + ({c.numerator} / {c.denominator} : ℝ) * tau ψ ≤ piMean ψ {k} := by
  rw [piMean_eq_purMean]
  have h := lp_tradeoff {n} ({L.numerator} / {L.denominator}) ({c.numerator} / {c.denominator}) {lean_list(es)} {lean_list(ys)} (by decide +kernel) ψ hψ
  norm_num at h
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.tradeoffBound{n}' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tradeoffBound{n}
""")
    out.append(FOOT)
    with open(os.path.join(HERE, "SpinFlipTradeoffEvenCert.lean"), "w") as f:
        f.write("\n".join(out))


if __name__ == "__main__":
    import sys
    which = sys.argv[1:] or ["cert", "A", "16", "20"]
    if "cert" in which:
        write_certs()
    if "A" in which:
        write("SpinFlipTradeoffEvenGraphA.lean", "n = 8, 10, 14", [8, 10, 14])
    if "16" in which:
        write("SpinFlipTradeoffEvenGraph16.lean", "n = 16", [16])
    if "20" in which:
        write("SpinFlipTradeoffEvenGraph20.lean", "n = 20", [20])
    print("wrote", which, "; all certificates and rank sums verified in exact arithmetic")
