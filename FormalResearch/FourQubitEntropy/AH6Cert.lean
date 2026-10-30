import FormalResearch.FourQubitEntropy.AH6Logs

/-!
# The AH-6 kernel certificate and its soundness

`parB` is the ball version of the parameters: `x` in a bracket of width `10^-45` around the root of the stationarity
equation `2³²(1-2x)¹⁵ = 3⁸(1+8x)⁸(1+28x)⁷` and `ln 2, ln 3, ln c, ln a, ln d` by `atanh` series
(`AH6Logs`).  `finalCheck parB = true` (`cert_ok`, by `decide +kernel`) runs the whole computation of AH-6a/b/c in ball
arithmetic and checks the positivity of the constants and of the Bernstein/shifted-power coefficients of the degree-eighteen
polynomial `Π`.  `cert_sound` turns it into the real statements about `stageA .. stageD3` evaluated at `ℝ`.
-/

namespace FormalResearch.FourQubitEntropy.AH6

/-- The integer `10^45 x_*` rounded down; `x_* ∈ [XLO/10^45, (XLO+1)/10^45]`. -/
def XLO : ℤ := 69828797600943511849779644863793600206704143

/-- The ball of the bracket `[XLO/10^45, (XLO+1)/10^45]`. -/
def xB : Ball := ⟨((2 * XLO + 1) * (SC : ℤ)) / (2 * 10 ^ 45), SC / (2 * 10 ^ 45) + 2, true⟩

section Generic
variable {α : Type} [Add α] [Mul α] [Neg α] [Inv α] [IntCast α]

/-- `u = (1-2x)/30`. -/
def uOf (x : α) : α := (ic 1 + -(ic 2 * x)) * (ic 30)⁻¹

/-- `z = (r c - 1)/(r c + 1)`, so that `(1+z)/(1-z) = r c`. -/
def zFor (r c : α) : α := (r * c + -(ic 1)) * (r * c + ic 1)⁻¹

end Generic

attribute [irreducible] xB

def l2B : Ball := lnB (rat 1 3) 60
def l3B : Ball := l2B + lnB (rat 1 5) 40

/-- The parameter balls. -/
def parB : Par Ball :=
  { x := xB, l2 := l2B, l3 := l3B,
    lc := ic (-2) * l3B + lnB (zFor (rat 9 1) (ic 4 * uOf xB)) 24,
    la := -(l2B + l3B) + lnB (zFor (rat 6 1) (ic 3 * uOf xB + xB)) 24,
    ld := l3B + ic (-5) * l2B + lnB (zFor (rat 32 3) (uOf xB + xB)) 24 }

/-- All lists have length `19` and positive entries. -/
def allPos19 (l : List Ball) : Bool := allPos l && l.length == 19

/-- The final check. -/
def finalCheck (p : Par Ball) : Bool :=
  let A := stageA p
  let B := stageB A
  let C1 := stageC1 p A B
  let C2 := stageC2 C1
  let D1 := stageD1 B C1 C2
  let D3 := stageD3 C1 (stageD2 C1 D1)
  A.u.pos && A.c.pos && A.a.pos && A.d.pos && p.x.pos &&
  (A.n2 + -A.n1).nz && (A.n3 + -A.n1).nz && (A.n3 + -A.n2).nz && C1.q0.nz &&
  C2.k0.pos && C2.gam.pos && (ic 1 + -(C2.gam * C1.e0)).pos && C1.eta3.pos &&
  allPos19 D3.cA && allPos19 D3.cB && allPos19 D3.cC && allPos19 D3.tail

set_option maxRecDepth 100000 in
theorem cert_ok : finalCheck parB = true := by decide +kernel

end FormalResearch.FourQubitEntropy.AH6
