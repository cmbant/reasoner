"""Generate the graph-state data modules of the Paper E purity-minima formalisation:
  PurityLPGraphDataA.lean  (n = 4, 5, 6, 8, 9, 10, 11, 12)      PurityLPGraphDataB.lean (n = 14, 15)
  PurityLPGraphData16.lean, PurityLPGraphData17.lean, PurityLPGraphData18.lean
  PurityLPMain.lean        (the exact minima `minPurity<n>`)
Sources: even_qubit_purity_minima.tex (tab:graphs, thm:fourteenfifteen, thm:sixteenseventeen),
balanced_purity_18.tex (thm:eighteen).  The graphs are those of code/verify_balanced_purity_lp_graph_states.py,
verify_balanced_purity_13_15.py, verify_graph_purity_16_17.py, verify_balanced_purity_18.py.

For every graph this script recomputes, in exact integer arithmetic (an independent bitmask elimination),
the multiset of ranks of all k-subset cuts, asserts it equals the paper's rank histogram, and asserts that the mean
purity equals the Rains-LP value L.  The Lean modules re-check the rank sums by `decide +kernel`.
Run from anywhere: python3 gen_lp_graphs.py"""
import os
from fractions import Fraction as F
from itertools import combinations
from math import comb
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))


def circ(n, D, mod=None):
    mod = mod or n
    adj = [0] * n
    for i in range(n):
        for d in D:
            for j in ((i + d) % mod, (i - d) % mod):
                if j < n and j != i:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
    return adj


def from_edges(n, E):
    adj = [0] * n
    for i, j in E:
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj


def from_hex(s):
    return [int(x, 16) for x in s.split()]


E8 = [(2, 0), (2, 1), (3, 1), (3, 2), (4, 1), (4, 3), (5, 0), (5, 1), (5, 2), (5, 4), (6, 0), (6, 1), (6, 3),
      (6, 4), (7, 0), (7, 1), (7, 6)]
E11 = [(2, 0), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (5, 1), (5, 3), (5, 4), (6, 0), (6, 1), (6, 3), (6, 4),
       (7, 0), (7, 1), (7, 6), (8, 1), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (9, 2), (9, 3), (9, 6), (9, 8),
       (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 9)]
E4 = [(0, 1), (1, 2), (2, 3)]
HEX14 = '38e8 1bf0 0d68 3855 3a0a 0487 318f 2563 2ac6 1512 32a4 011f 265b 15d9'
HEX15 = '41d4 37bc 7dcb 6a96 580b 6742 4625 730f 16a7 49ea 3966 061c 0596 04ae 02fd'
HEX18 = '36e72 0fb7d 1b80a 0cad6 25e0b 30583 1c10b 2b228 1a262 3999b 27031 3221f 2a696 1dd87 2a45b 273ce 22b65 1deb1'

# n: (L, name, adjacency, spec, paper histogram {rank: count})
G = {
    4: (F(1, 3), "path `P_4` (linear cluster)", from_edges(4, E4), ("edges", E4), {1: 2, 2: 4}),
    5: (F(1, 4), "`C_5(1)`", circ(5, [1]), ("circ", [1], 5, 5), {2: 10}),
    6: (F(1, 8), "`C_6(2,3)`", circ(6, [2, 3]), ("circ", [2, 3], 6, 6), {3: 20}),
    8: (F(3, 35), "the 17-edge graph of `tab:graphs`", from_edges(8, E8), ("edges", E8), {2: 6, 3: 8, 4: 56}),
    9: (F(1, 14), "`C_9(3,4)`", circ(9, [3, 4]), ("circ", [3, 4], 9, 9), {3: 18, 4: 108}),
    10: (F(1, 21), "`C_10(1,2,4)`", circ(10, [1, 2, 4]), ("circ", [1, 2, 4], 10, 10), {4: 132, 5: 120}),
    11: (F(1, 28), "the 34-edge graph of `tab:graphs`", from_edges(11, E11), ("edges", E11), {4: 66, 5: 396}),
    12: (F(5, 224), "`C_12(3,5,6)`", circ(12, [3, 5, 6]), ("circ", [3, 5, 6], 12, 12), {4: 6, 5: 378, 6: 540}),
    14: (F(331, 27456), "the 47-edge graph of `thm:fourteenfifteen` (hexadecimal rows)", from_hex(HEX14), ("hex",),
         {5: 60, 6: 1684, 7: 1688}),
    15: (F(1, 104), "the 56-edge graph of `thm:fourteenfifteen` (hexadecimal rows)", from_hex(HEX15), ("hex",),
         {5: 35, 6: 1380, 7: 5020}),
    16: (F(1, 156), "`C_17(1,3,4,5)` induced on the vertices `0..15`", circ(16, [1, 3, 4, 5], 17),
         ("circ", [1, 3, 4, 5], 16, 17), {5: 10, 6: 500, 7: 6680, 8: 5680}),
    17: (F(1, 208), "`C_17(1,3,4,5)`", circ(17, [1, 3, 4, 5]), ("circ", [1, 3, 4, 5], 17, 17),
         {6: 510, 7: 4080, 8: 19720}),
    18: (F(7, 2288), "the graph of `thm:eighteen` (hexadecimal rows)", from_hex(HEX18), ("hex",),
         {7: 9180, 9: 39440}),
}
BLOCK_A = {16: 4, 17: 4, 18: 4}   # blockwise evaluation uses A = {0,..,|A|-1}


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


def cuts(n, k, adj):
    full = (1 << n) - 1
    for S in combinations(range(n), k):
        mask = sum(1 << i for i in S)
        yield S, rank2([adj[i] & (full ^ mask) for i in S])


def check_graph(n, L, adj, hist_paper):
    k = n // 2
    assert len(adj) == n
    assert all(not (adj[i] >> i) & 1 for i in range(n))
    assert all(((adj[i] >> j) & 1) == ((adj[j] >> i) & 1) for i in range(n) for j in range(n))
    hist = Counter()
    sums = {}
    nb = BLOCK_A.get(n, 0)
    for S, r in cuts(n, k, adj):
        hist[r] += 1
        T = tuple(i for i in S if i < nb)
        sums[T] = sums.get(T, 0) + 2 ** (k - r)
    assert dict(hist) == hist_paper, (n, dict(hist), hist_paper)
    N = sum(c * 2 ** (k - r) for r, c in hist.items())
    assert F(N, 2 ** k * comb(n, k)) == L, (n, F(N, 2 ** k * comb(n, k)), L)
    return N, sums


def lean_set(T, n):
    return "(∅ : Finset (Fin %d))" % n if not T else "({%s} : Finset (Fin %d))" % (", ".join(map(str, T)), n)


def spec_stmt(n, name, spec):
    if spec[0] == "circ":
        D, nn, mod = spec[1], spec[2], spec[3]
        return (f"theorem adj{n}_spec : ∀ i j : Fin {n}, (adj{n} i).testBit j = decide ((i : ℕ) ≠ j ∧ "
                f"(((j : ℕ) + {mod} - i) % {mod} ∈ ({D} : List ℕ) ∨ ((i : ℕ) + {mod} - j) % {mod} ∈ ({D} : List ℕ))) := by\n"
                f"  decide +kernel\n")
    if spec[0] == "edges":
        return (f"theorem adj{n}_spec : ∀ i j : Fin {n}, (adj{n} i).testBit j = decide "
                f"(((i : ℕ), (j : ℕ)) ∈ ({spec[1]} : List (ℕ × ℕ)) ∨ ((j : ℕ), (i : ℕ)) ∈ ({spec[1]} : List (ℕ × ℕ))) := by\n"
                f"  decide +kernel\n")
    return ""


HEADER = """import FormalResearch.FourQubitEntropy.PurityLPBlocks

/-!
# Graph-state witnesses of the purity minima: %s

GENERATED by `gen_lp_graphs.py`; do not edit.  Sources: `even_qubit_purity_minima.tex` (`thm:lptable`(2),
`tab:graphs`, `thm:fourteenfifteen`, `thm:sixteenseventeen`), `balanced_purity_18.tex` (`thm:eighteen`).

For each `n` the graph is given by its neighbourhood bitmasks `adj<n>` (bit `j` of `adj<n> i` set iff `i ~ j`);
`adj<n>_spec` checks that they are the stated circulant / edge list (where the paper gives one),
`adj<n>_symm`, `adj<n>_irrefl` that the graph is simple.  `rankSum<n>` is the kernel-checked sum
`Σ_{|S| = k} 2^{k - rk_2 Γ[S,S^c]}` and `piMean_graph<n>` the resulting value of `π_k` of the (normalised) graph
state `gsn`, which equals the Rains-LP value.  Claim class: exact finite certificate (`decide +kernel`).
-/

open scoped BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.PurityLP
"""
FOOT = "\nend FormalResearch.FourQubitEntropy.PurityLP\n"


parts = {}
base = {}


def emit_graph(n, rec, out):
    L, name, adj, spec, hist = rec
    k = n // 2
    N, sums = check_graph(n, L, adj, hist)
    out.append(f"/-- Neighbourhood bitmasks of {name} on {n} vertices. -/")
    out.append(f"def adj{n} : Fin {n} → ℕ := fun i => ({adj} : List ℕ).getD i.1 0\n")
    s = spec_stmt(n, name, spec)
    if s:
        out.append(s)
    out.append(f"theorem adj{n}_symm : ∀ i j : Fin {n}, (adj{n} i).testBit j = (adj{n} j).testBit i := by\n  decide +kernel\n")
    out.append(f"theorem adj{n}_irrefl : ∀ i : Fin {n}, (adj{n} i).testBit i = false := by\n  decide +kernel\n")
    P = f"((Finset.univ : Finset (Fin {n})).powersetCard {k})"
    if n in BLOCK_A:
        nb = BLOCK_A[n]
        A = f"A{n}"
        out.append(f"/-- The block-splitting set `A = {{0, …, {nb - 1}}}`. -/")
        out.append(f"def {A} : Finset (Fin {n}) := {{{', '.join(map(str, range(nb)))}}}\n")
        Ts = sorted(sums, key=lambda t: (len(t), t))
        assert len(Ts) == 2 ** nb
        for idx, T in enumerate(Ts):
            out.append(f"theorem blk{n}_{idx} : blk' adj{n} {k} {A} {lean_set(T, n)} = {sums[T]} := by\n  decide +kernel\n")
        tl = ", ".join(lean_set(T, n) for T in Ts)
        ns = ", ".join(str(sums[T]) for T in Ts)
        chain = "List.Forall₂.nil"
        for idx in reversed(range(len(Ts))):
            chain = f"(List.Forall₂.cons blk{n}_{idx} {chain})"
        out.append(f"theorem rankSum{n} : ∑ S ∈ {P}, 2 ^ ({k} - cutRankN adj{n} S) = {N} := by\n"
                   f"  have h := total_of_blocks' adj{n} {k} {A} (by decide) [{tl}]\n    [{ns}] (by decide) {chain}\n"
                   f"  rw [h]; norm_num\n")
    else:
        out.append(f"theorem rankSum{n} : ∑ S ∈ {P}, 2 ^ ({k} - cutRankN adj{n} S) = {N} := by\n  decide +kernel\n")
    if n <= 15:
        rs = sorted(hist)
        conj = " ∧\n    ".join(
            [f"({P}.filter fun S => cutRankN adj{n} S = {r}).card = {hist[r]}" for r in rs]
            + [f"({P}.filter fun S => {' ∨ '.join(f'cutRankN adj{n} S = {r}' for r in rs)}).card = {comb(n, k)}"])
        out.append(f"/-- The rank histogram of `tab:graphs` / the theorem: "
                   f"{', '.join(f'rank {r} on {hist[r]} cuts' for r in rs)} (and no other rank). -/\n"
                   f"theorem rankHist{n} :\n    {conj} := by\n  decide +kernel\n")
    num, den = L.numerator, L.denominator
    out.append(f"/-- The graph state of {name} has `π_{k} = {L}`. -/\n"
               f"theorem piMean_graph{n} : piMean (gsn (adjGraph adj{n})) {k} = {num} / {den} := by\n"
               f"  rw [piMean_gsn adj{n} adj{n}_symm {k} {N} (by norm_num) rankSum{n}]\n"
               f"  norm_num [Nat.choose]\n")


def write(fname, title, ns, extra_imports=""):
    out = [HEADER % title]
    for n in ns:
        emit_graph(n, G[n], out)
    out.append(FOOT)
    text = "\n".join(out)
    if extra_imports:
        text = text.replace("import FormalResearch.FourQubitEntropy.PurityLPBlocks\n",
                            "import FormalResearch.FourQubitEntropy.PurityLPBlocks\n" + extra_imports, 1)
    with open(os.path.join(HERE, fname), "w") as f:
        f.write(text)


write("PurityLPGraphDataA.lean", "n = 4, 5, 6, 8, 9, 10, 11, 12", [4, 5, 6, 8, 9, 10, 11, 12])
write("PurityLPGraphDataB.lean", "n = 14, 15", [14, 15])
for n in (16, 17, 18):
    write(f"PurityLPGraphData{n}.lean", f"n = {n}", [n])


# ---- main theorems
main = ["""import FormalResearch.FourQubitEntropy.PurityLPCertData
import FormalResearch.FourQubitEntropy.PurityLPGraphDataA
import FormalResearch.FourQubitEntropy.PurityLPGraphDataB
import FormalResearch.FourQubitEntropy.PurityLPGraphData16
import FormalResearch.FourQubitEntropy.PurityLPGraphData17
import FormalResearch.FourQubitEntropy.PurityLPGraphData18

/-!
# Exact minima of the mean balanced-cut purity of `n`-qubit pure states (Paper E, Rains LP tables)

GENERATED by `gen_lp_graphs.py`; do not edit.  For `n ∈ {4,5,6,8,9,10,11,12,14,15,16,17,18}` and
`k = ⌊n/2⌋`, `minPurity<n>` states, for **unit vectors `ψ` of `(ℂ²)^{⊗n}`** and the **actual marginal purities**
`piMean ψ k = C(n,k)^{-1} Σ_{|S|=k} tr (ρ_S²)` (`ρ_S = rdm ψ S` the explicit partial trace),

  `IsLeast {x | ∃ ψ, ‖ψ‖ = 1 ∧ π_k(ψ) = x} L`,

with `L` the entry of `tab:minima` (`thm:lptable`, `thm:fourteenfifteen`, `thm:sixteenseventeen`, `thm:eighteen`).
The lower bound is `lpBound<n>` (shadow inequalities `shadow_nonneg`, `a_s = a_{n-s}`, exact rational dual
certificate); the attaining state is the normalised graph state `gsn (adjGraph adj<n>)` (`piMean_graph<n>`, from
`purity_gsn : tr ρ_S² = 2^{-rk_2 Γ[S,S^c]}` and the kernel-checked cut ranks).  `n = 7, 13` are out of scope.
-/

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FrameFree.NQubit
"""]
for n, rec in G.items():
    L = rec[0]
    k = n // 2
    main.append(f"""/-- **Exact minimum of `π_{k}` for `n = {n}` qubits**: `min π_{k} = {L}`, attained by {rec[1]}. -/
theorem minPurity{n} :
    IsLeast {{x : ℝ | ∃ ψ : Ψ {n}, nsq ψ = 1 ∧ piMean ψ {k} = x}} ({L.numerator} / {L.denominator}) :=
  ⟨⟨gsn (adjGraph adj{n}), nsq_gsn _, piMean_graph{n}⟩, fun _ ⟨ψ, hψ, hx⟩ => hx ▸ lpBound{n} ψ hψ⟩

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.minPurity{n}' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms minPurity{n}
""")
main.append(FOOT)
with open(os.path.join(HERE, "PurityLPMain.lean"), "w") as f:
    f.write("\n".join(main))
print("wrote graph data modules and PurityLPMain.lean; all rank histograms and means verified in exact arithmetic")
