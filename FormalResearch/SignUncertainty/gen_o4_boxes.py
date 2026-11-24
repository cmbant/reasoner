#!/usr/bin/env python3
"""Exact integer re-check of the `O4QuotientBound` box certificate, and generator of `O4CertData.lean`.

Source of truth for the boxes: CFT/sign_uncertainty/code/certify_u1c_o4_contraction.py (python-flint arb; log ALL PASS, M_F <= 0.12560).
This script re-does check (B) of that script in EXACT integer fixed-point ball arithmetic that mirrors, operation by operation, the Lean kernel
evaluator `O4CertEval.lean` (balls `(m, r)` over `Int`/`Nat` at scale SC = 2^SCB, floor/ceil outward rounding, no Rat/real functions):

  F(theta) = ((L s - a) theta - (pi^2/36)(s^3 - 1) theta^3 + rho(s theta)) / (theta (theta^2 - theta0^2)^2),   theta0^2 = 12 a / pi^2,
  rho(tau) = (1/pi) * w x^2 P(x),  w = pi tau,  x = w^2,  P(x) = sum_{k=0}^{11} (-1)^k r_{k+2} x^k,
  r_n = (2^{2n} - 2) |B_{2n}| / ((2n)! 2n (2n+1)),     (so that rho(tau) = sum_{n=2}^{13} (-1)^n r_n pi^{2n} tau^{2n+1} = rho_13)
  tail bound: |rho - rho_13|(tau) <= (2/(14*29)) T^29 / (1 - T^2) for |tau| <= T < 1 (c_n (pi/2)^{2n} <= 2/n).

Boxes (quarter circle theta = (1/4)(1 - t^2 + 2 i t)/(1 + t^2), t in [0,1], F even and conj-symmetric): L in [LMAX i/NL, LMAX (i+1)/NL], t in [j/NT, (j+1)/NT],
  s in [1 - Lhi/8, 1 + 0.606 Lhi]   (paper (ii), `o4Sigma0_sharp`),   a in [Llo, Lhi (1 + Lhi/4)]   (paper (i), `edgeKappa0_bounds`),
  pi in [3.14159265358979323846, 3.14159265358979323847] (Real.pi_gt_d20 / pi_lt_d20), tail ball radius ceil(tail(Tmax)), Tmax = (1 + 0.606 LMAX)/4.
A box PASSES when  hi(10000 |num|^2) <= lo(169 |den|^2)  (balls multiplied by exact integers; division-free form of |F| <= 0.13).

Usage:  python3 gen_o4_boxes.py check      # exact re-check, prints the log (committed as gen_o4_boxes.txt)
        python3 gen_o4_boxes.py emit       # prints O4CertData.lean (only after the check passed)
        python3 gen_o4_boxes.py emit-run K # prints O4CertRunKK.lean, K = 1 .. NL/ROWS_PER_RUN
"""
import sys
from fractions import Fraction as Fr
from math import sqrt
from sympy import bernoulli, factorial, Rational

SCB = 96
SC = 2 ** SCB
NL, NT = 40, 320          # grid (quarter circle); the script's own grid is 40 x 640
NTERMS = 14               # r_2 .. r_13
LMAX = Fr(2, 1000)
CBOUND2 = Fr(169, 10000)  # 0.13^2


def hullQ(pl, ql, ph, qh):
    """Mirror of `Ball.hullQ pl ql ph qh` (ql, qh > 0): ball enclosing [pl/ql, ph/qh]."""
    l = (pl * SC) // ql
    h = -((-(ph * SC)) // qh)
    m = (l + h) // 2
    return (m, max(h - m, m - l) + 1)


def hull(lo, hi):
    lo, hi = Fr(lo), Fr(hi)
    return hullQ(lo.numerator, lo.denominator, hi.numerator, hi.denominator)


def ofrat(q):
    q = Fr(q)
    return hullQ(q.numerator, q.denominator, q.numerator, q.denominator)


def ofint(n): return (n * SC, 0)
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def neg(a): return (-a[0], a[1])
def sub(a, b): return add(a, neg(b))


def mul(a, b):
    """Mirror of `Ball.mul` (AH6Ball): midpoint floor, radius (cross terms)/SC + 2."""
    return ((a[0] * b[0]) // SC, (abs(a[0]) * b[1] + abs(b[0]) * a[1] + a[1] * b[1]) // SC + 2)


def inv(a):
    """Mirror of `Ball.invPos` (AH6Ball) for a ball with positive lower end."""
    lo, hi = a[0] - a[1], a[0] + a[1]
    assert lo > 0
    l = (SC * SC) // hi
    q = (SC * SC) // lo
    m = (l + (q + 1)) // 2
    return (m, q + 1 - m)


def cadd(a, b): return (add(a[0], b[0]), add(a[1], b[1]))
def csub(a, b): return (sub(a[0], b[0]), sub(a[1], b[1]))
def cmul(a, b): return (sub(mul(a[0], b[0]), mul(a[1], b[1])), add(mul(a[0], b[1]), mul(a[1], b[0])))
def rmulc(k, a): return (mul(k, a[0]), mul(k, a[1]))


ZERO = (0, 0)
PI = hullQ(314159265358979323846, 10 ** 20, 314159265358979323847, 10 ** 20)
PI2 = mul(PI, PI)
IPI = inv(PI)
IPI2 = inv(PI2)
ONE = ofint(1)
RB = ofrat(Fr(1, 4))


def r_exact(n):
    q = (Rational(2) ** (2 * n) - 2) * abs(Rational(bernoulli(2 * n))) / (factorial(2 * n) * 2 * n * (2 * n + 1))
    return Fr(int(q.p), int(q.q))


RN = {n: r_exact(n) for n in range(2, NTERMS)}
RBALL = {n: ofrat(RN[n]) for n in RN}
SUP_S = 1 + Fr(606, 1000) * LMAX
TMAX = SUP_S / 4
TAIL = Fr(2, NTERMS * (2 * NTERMS + 1)) * TMAX ** (2 * NTERMS + 1) / (1 - TMAX ** 2)
TAIL_R = -((-(TAIL.numerator * SC)) // TAIL.denominator) + 1       # radius (scaled) added to re and im of rho


def box(i, j):
    Llo, Lhi = LMAX * i / NL, LMAX * (i + 1) / NL
    Lb = hull(Llo, Lhi)
    sb = hull(1 - Lhi / 8, 1 + Fr(606, 1000) * Lhi)
    ab = hull(Llo, Lhi * (1 + Lhi / 4))
    th02 = mul(mul(ofint(12), ab), IPI2)
    tb = hull(Fr(j, NT), Fr(j + 1, NT))
    t2 = mul(tb, tb)
    u = inv(add(ONE, t2))
    th = (mul(mul(sub(ONE, t2), u), RB), mul(mul(mul(ofint(2), tb), u), RB))
    th2 = cmul(th, th)
    th3 = cmul(th2, th)
    k1 = sub(mul(Lb, sb), ab)
    s3 = mul(mul(sb, sb), sb)
    k2 = mul(mul(PI2, ofrat(Fr(1, 36))), sub(s3, ONE))
    w = rmulc(PI, rmulc(sb, th))
    x = cmul(w, w)
    acc = (ZERO, ZERO)
    for k in range(NTERMS - 3, -1, -1):
        c = ofrat(RN[k + 2] if k % 2 == 0 else -RN[k + 2])
        acc = cadd(cmul(acc, x), (c, ZERO))
    rho = rmulc(IPI, cmul(cmul(w, cmul(x, x)), acc))
    rho = cadd(rho, ((0, TAIL_R), (0, TAIL_R)))
    num = cadd(csub(rmulc(k1, th), rmulc(k2, th3)), rho)
    d1 = csub(th2, (th02, ZERO))
    den = cmul(th, cmul(d1, d1))
    nn = add(mul(num[0], num[0]), mul(num[1], num[1]))
    dd = add(mul(den[0], den[0]), mul(den[1], den[1]))
    nn = mul(nn, ofint(10000))
    dd = mul(dd, ofint(169))
    dlo, nhi = dd[0] - dd[1], nn[0] + nn[1]
    return dlo > 0 and nhi <= dlo, (Fr(nhi * 169, dlo * 10000) if dlo > 0 else None)


def check():
    worst, wb, bad = Fr(0), None, 0
    for i in range(NL):
        for j in range(NT):
            ok, ratio = box(i, j)
            if not ok:
                bad += 1
            if ratio is not None and ratio > worst:
                worst, wb = ratio, (i, j)
    print(f"scale 2^{SCB}, NL={NL}, NT={NT}, boxes={NL * NT}, tail radius (scaled) = {TAIL_R}")
    print(f"worst box (i,j)={wb}: certified |F|^2 <= {float(worst):.6f}, |F| <= {sqrt(float(worst)):.6f}")
    print(f"failing boxes: {bad}")
    print("ALL PASS" if bad == 0 else "SOME BOX FAILED")
    return bad == 0


def emit():
    assert check_quiet()
    print("-- Generated by gen_o4_boxes.py emit (exactly its output); do not edit.")
    print("module\n\n@[expose] public section\n\nnamespace FormalResearch.SignUncertainty.O4Cert\n")
    print(f"def NL : Nat := {NL}\ndef NT : Nat := {NT}\n")
    print("/-- Radius (scaled by `SC`) of the ball added to `ρ`: `⌈SC · 2/(14·29) T^29/(1 - T²)⌉ + 1`, `T = (1 + 0.606 · 0.002)/4`. -/")
    print(f"def tailR : Nat := {TAIL_R}\n")
    print("/-- The Horner coefficients `(-1)^k r_{k+2}` for `k = 11, …, 0` (`r_n = (2^{2n} - 2) |B_{2n}| / ((2n)! 2n (2n+1))`), as `(numerator, denominator)`. -/")
    print("def csData : List (Int × Nat) :=\n  [" + ", ".join(
        f"({(RN[k + 2] if k % 2 == 0 else -RN[k + 2]).numerator}, {RN[k + 2].denominator})" for k in range(NTERMS - 3, -1, -1)) + "]\n")
    print("end FormalResearch.SignUncertainty.O4Cert")


ROWS_PER_RUN = 4


def emit_run(k):
    """Module `O4CertRun{k:02d}`: rows `ROWS_PER_RUN*(k-1) <= i < ROWS_PER_RUN*k` checked by `decide +kernel` (about 45 s of kernel time)."""
    i0, i1 = ROWS_PER_RUN * (k - 1), ROWS_PER_RUN * k
    assert 0 <= i0 < i1 <= NL
    print(f"-- Generated by gen_o4_boxes.py emit-run {k} (exactly its output); do not edit.")
    print("module\n")
    print("public import FormalResearch.SignUncertainty.O4CertCheck\n")
    print(f"/-!\n# Kernel check of the boxes `{i0} ≤ i < {i1}`, `j < NT` of the `O4QuotientBound` certificate\n\n"
          "Status: proved by `decide +kernel` (no `native_decide`); see `gen_o4_boxes.py` for the exact re-check in integer arithmetic.\n-/\n")
    print("@[expose] public section\n\nnamespace FormalResearch.SignUncertainty.O4Cert\n")
    print(f"theorem run{k:02d} : checkRange {i0} {i1} = true := by decide +kernel\n")
    print(f"/-- info: 'FormalResearch.SignUncertainty.O4Cert.run{k:02d}' depends on axioms: [propext] -/")
    print(f"#guard_msgs (whitespace := lax) in #print axioms run{k:02d}\n")
    print("end FormalResearch.SignUncertainty.O4Cert")


def check_quiet():
    for i in range(NL):
        for j in range(NT):
            if not box(i, j)[0]:
                return False
    return True


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    if cmd == "check":
        sys.exit(0 if check() else 1)
    elif cmd == "emit":
        emit()
    elif cmd == "emit-run":
        emit_run(int(sys.argv[2]))
