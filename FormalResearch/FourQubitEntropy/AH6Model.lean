import FormalResearch.FourQubitEntropy.AH6Poly

/-!
# The AH-6 computation, written once for any arithmetic

Source: `ResearchNotes/QI/seven_qubit_entanglement/joint_entropy_analytic_proof.tex` and the verifier
`code/verify_seven_entropy_joint_majorant.py` (AH-6a/b/c).  Everything is in nats (`f = negMulLog`), so
the paper's `8 ln 2 · k₀` is `8 k₀` here and the coefficients `α₂, α₃, β₁` of the paper carry a factor `ln 2`.

The computation is a chain of four stages, each a function of the previous ones, and is generic in the
arithmetic (`ℝ` for the analytic proof, `Ball` for the kernel certificate):

* `stageA`: from `x`, `ln 2`, `ln 3`, `ln c`, `ln a`, `ln d` (`Par`): `u = (1-2x)/30`, the cut eigenvalues
  `c = 4u`, `a = 3u + x`, `d = u + x`, the Hermite nodes `8c, 8a, 8d` (in the variable `e = 4(λ+μ)`), the data
  `g(nᵢ), g'(nᵢ)` of `g(e) = negMulLog(e/8)` and the inverse node differences;
* `stageB`: the Newton form of the quintic Hermite interpolant `P` of `g` (divided-difference tableau on the nodes
  `n₁n₁n₂n₂n₃n₃`) and `q = (e-n₁)(e-n₂)(e-n₃)`;
* `stageC1`, `stageC2`: `e₀ = 48u`, `v₀ = e₀²/9`, the contact data at `(b,c)`, the coefficients `α₀..α₃, β₀, β₁` of `H`,
  `k₀`, `γ`, `η₂, η₃`;
* `stageD1`, `stageD2`, `stageD3`: the coefficient lists `AA, BB, CC, EL, L`, the degree-twenty polynomial `R`, its
  quotient `Π = R/(e-e₀)²` and the four certificate lists.
-/

namespace FormalResearch.FourQubitEntropy.AH6

section Model

variable {α : Type} [Add α] [Mul α] [Neg α] [Inv α] [IntCast α]

/-- The rational constant `p/q`. -/
def rat (p q : ℤ) : α := ic p * (ic q)⁻¹

/-- Parameters: `x`, `ln 2`, `ln 3`, `ln c`, `ln a`, `ln d` (`c = 4u`, `a = 3u+x`, `d = u+x`). -/
structure Par (α : Type) where
  x : α
  l2 : α
  l3 : α
  lc : α
  la : α
  ld : α

structure StA (α : Type) where
  u : α
  c : α
  a : α
  d : α
  n1 : α
  n2 : α
  n3 : α
  G1 : α
  G2 : α
  G3 : α
  W1 : α
  W2 : α
  W3 : α
  i21 : α
  i31 : α
  i32 : α

def stageA (p : Par α) : StA α :=
  let u : α := (ic 1 + -(ic 2 * p.x)) * (ic 30)⁻¹
  let c : α := ic 4 * u
  let a : α := ic 3 * u + p.x
  let d : α := u + p.x
  let n1 : α := ic 8 * c
  let n2 : α := ic 8 * a
  let n3 : α := ic 8 * d
  { u := u, c := c, a := a, d := d, n1 := n1, n2 := n2, n3 := n3,
    G1 := -(c * p.lc), G2 := -(a * p.la), G3 := -(d * p.ld),
    W1 := -(p.lc + ic 1) * rat 1 8, W2 := -(p.la + ic 1) * rat 1 8,
    W3 := -(p.ld + ic 1) * rat 1 8,
    i21 := (n2 + -n1)⁻¹, i31 := (n3 + -n1)⁻¹, i32 := (n3 + -n2)⁻¹ }

structure StB (α : Type) where
  P : List α
  q : List α

/-- Newton form of the Hermite interpolant on the nodes `n₁ n₁ n₂ n₂ n₃ n₃`. -/
def stageB (s : StA α) : StB α :=
  let d12 : α := (s.G2 + -s.G1) * s.i21
  let d34 : α := (s.G3 + -s.G2) * s.i32
  let d02 : α := (d12 + -s.W1) * s.i21
  let d13 : α := (s.W2 + -d12) * s.i21
  let d24 : α := (d34 + -s.W2) * s.i32
  let d35 : α := (s.W3 + -d34) * s.i32
  let d03 : α := (d13 + -d02) * s.i21
  let d14 : α := (d24 + -d13) * s.i31
  let d25 : α := (d35 + -d24) * s.i32
  let d04 : α := (d14 + -d03) * s.i31
  let d15 : α := (d25 + -d14) * s.i31
  let d05 : α := (d15 + -d04) * s.i31
  let l1 : List α := [-s.n1, ic 1]
  let l2 : List α := [-s.n2, ic 1]
  let l3 : List α := [-s.n3, ic 1]
  let p2 : List α := mulL l1 l1
  let p3 : List α := mulL p2 l2
  let p4 : List α := mulL p3 l2
  let p5 : List α := mulL p4 l3
  { P := addL (addL (addL (addL (addL [s.G1] (scaleL s.W1 l1)) (scaleL d02 p2)) (scaleL d03 p3))
          (scaleL d04 p4)) (scaleL d05 p5),
    q := mulL (mulL l1 l2) l3 }

structure StC1 (α : Type) where
  e0 : α
  v0 : α
  Pe0 : α
  Pd0 : α
  hh : α
  he : α
  hv : α
  a2 : α
  a3 : α
  b1 : α
  g0 : α
  g1 : α
  q0 : α
  q1 : α
  eta2 : α
  eta3 : α

/-- Contact data at `(b, c)`, the evaluation of `P` and `q` at `e₀`, and `η₂, η₃`. -/
def stageC1 (p : Par α) (s : StA α) (t : StB α) : StC1 α :=
  let e0 : α := ic 48 * s.u
  let b : α := ic 8 * s.u
  let lnb : α := p.lc + p.l2
  let ln6 : α := p.lc + p.l3 + -p.l2
  { e0 := e0, v0 := (e0 * e0) * rat 1 9,
    Pe0 := evalL t.P e0, Pd0 := evalL (derL t.P) e0,
    hh := (-(b * lnb) + -(s.c * p.lc)) * rat 1 2,
    he := (-(lnb + ic 1) + -(p.lc + ic 1)) * rat 1 16,
    hv := (-(lnb + ic 1) + (p.lc + ic 1)) * (ic 512 * s.u)⁻¹,
    a2 := p.l2 * rat (-115001089107) 1000000000000,
    a3 := p.l2 * rat 18166193766 1000000000000,
    b1 := p.l2 * rat 14438812336 1000000000000,
    g0 := -(ic 6 * (s.u * ln6)), g1 := -(ln6 + ic 1) * rat 1 8,
    q0 := evalL t.q e0, q1 := evalL (derL t.q) e0,
    eta2 := rat 1593 4 * p.l2 + -(ic 243 * p.l3) + ic (-9),
    eta3 := rat 81 2 + -(rat 9477 4 * p.l2) + ic 1458 * p.l3 }

structure StC2 (α : Type) where
  b0 : α
  a1 : α
  a0 : α
  k0 : α
  k1 : α
  gam : α

/-- The coefficients `β₀, α₁, α₀` of `H` fixed by the contact conditions, and `k₀, k₁, γ`. -/
def stageC2 (c : StC1 α) : StC2 α :=
  let b0 : α := (c.v0 * c.hv + -c.hh + c.Pe0) * (c.v0 * c.v0)⁻¹ + -(c.b1 * c.e0)
  let a1 : α := (c.he + -c.Pd0 + -(c.v0 * (c.v0 * c.b1))) * c.v0⁻¹ + -(ic 2 * (c.a2 * c.e0))
    + -(ic 3 * (c.a3 * (c.e0 * c.e0)))
  let k0 : α := (c.Pe0 + -c.g0) * (c.q0 * c.q0)⁻¹
  let k1 : α := (c.Pd0 + -c.g1) * (c.q0 * c.q0)⁻¹ + -(ic 2 * (k0 * (c.q1 * c.q0⁻¹)))
  { b0 := b0, a1 := a1,
    a0 := c.hv + -(ic 2 * (c.v0 * (b0 + c.b1 * c.e0))) + -(a1 * c.e0) + -(c.a2 * (c.e0 * c.e0))
      + -(c.a3 * (c.e0 * (c.e0 * c.e0))),
    k0 := k0, k1 := k1, gam := -(k1 * k0⁻¹) }

structure StD1 (α : Type) where
  L : List α
  AA : List α
  BB : List α
  CC : List α
  EL : List α

def stageD1 (t : StB α) (c : StC1 α) (d : StC2 α) : StD1 α :=
  let L : List α := [ic 1 + -(d.gam * c.e0), d.gam]
  { L := L, AA := scaleL (ic 8 * d.k0) (powL t.q 2),
    BB := addL [rat 1 2] (scaleL (ic 8) [ic 0, d.a0, d.a1, c.a2, c.a3]),
    CC := addL [c.eta2] (scaleL (ic 8) [ic 0, ic 0, ic 0, d.b0, c.b1]),
    EL := mulL [ic 0, ic 1] L }

/-- `R = 27η₃²U² + 4eLUW³ + 4η₃e²L²V³ - e²L²V²W² - 18η₃eLUVW` (`U = AA`, `V = BB`, `W = CC`, `eL = EL`). -/
def stageD2 (c : StC1 α) (d : StD1 α) : List α :=
  addL (addL (addL (addL
    (scaleL (ic (-1)) (mulL (powL d.EL 2) (mulL (powL d.BB 2) (powL d.CC 2))))
    (scaleL (ic 4) (mulL d.EL (mulL d.AA (powL d.CC 3)))))
    (scaleL (ic 4 * c.eta3) (mulL (powL d.EL 2) (powL d.BB 3))))
    (scaleL (ic 27 * (c.eta3 * c.eta3)) (powL d.AA 2)))
    (scaleL (ic (-18) * c.eta3) (mulL d.EL (mulL d.AA (mulL d.BB d.CC))))

structure StD3 (α : Type) where
  Pi : List α
  cA : List α
  cB : List α
  cC : List α
  tail : List α

/-- `Π = R/(e-e₀)²` and the four certificate lists. -/
def stageD3 (c : StC1 α) (R : List α) : StD3 α :=
  let Pi : List α := (dl (dl R c.e0).1 c.e0).1
  { Pi := Pi,
    cA := mob (scalePow (rat 3 4 + -(ic 0)) (taylorL Pi (ic 0))),
    cB := mob (scalePow (ic 1 + -(rat 3 4)) (taylorL Pi (rat 3 4))),
    cC := mob (scalePow (rat 5 4 + -(ic 1)) (taylorL Pi (ic 1))),
    tail := taylorL Pi (rat 5 4) }

end Model

end FormalResearch.FourQubitEntropy.AH6
