module

public import Mathlib
public import FormalResearch.EuclTet.Gram
public import FormalResearch.Racah.P3CayleyMenger

/-!
# Weyl-shifted discriminant polynomial

Source: Weyl/P5 `thm:finitehwall`, especially `sec:finitehwall`. The Weyl factors and the four
printed correction coefficients are defined explicitly below. The determinant is the existing
`FormalResearch.Racah.P3.cmDet` determinant of its explicit bordered `5 × 5` matrix, with edge
lengths `(X,B,C,D,E,F)`. This module formalises the exact polynomial coefficient expansion (with the constant coefficient
identified as `8 X⁴ cmDet`) and evenness in `h`; the derivation of the midpoint recurrence coefficients from the Schulten--Gordon
recurrence is not repeated.
-/

@[expose] public section

namespace FormalResearch.EuclTet

/-- The adjacent-face Weyl factor `Φ_BC`. -/
def p5a_phiBC (X B C : ℝ) : ℝ :=
  (X ^ 2 - (B - C) ^ 2) * ((B + C) ^ 2 - X ^ 2)

/-- The adjacent-face Weyl factor `Φ_EF`. -/
def p5a_phiEF (X E F : ℝ) : ℝ :=
  (X ^ 2 - (E - F) ^ 2) * ((E + F) ^ 2 - X ^ 2)

/-- The quadratic Weyl combination `G` in `sec:finitehwall`. -/
def p5a_G (B C D E F : ℝ) : ℝ := B ^ 2 + C ^ 2 - 2 * D ^ 2 + E ^ 2 + F ^ 2

/-- The principal diagonal polynomial `Q₀` in `sec:finitehwall`. -/
def p5a_Q0 (X B C D E F : ℝ) : ℝ :=
  -X ^ 4 + X ^ 2 * p5a_G B C D E F + (B ^ 2 - C ^ 2) * (E ^ 2 - F ^ 2)

/-- The paper's `h²` correction to the discriminant. -/
def p5a_D2 (X B C E F : ℝ) (Q G : ℝ) : ℝ :=
  -4 * p5a_phiBC X B C * p5a_phiEF X E F + 2 * X ^ 2 * Q * G

/-- The paper's `h⁴` correction to the discriminant. -/
noncomputable def p5a_D4 (X : ℝ) (Q G : ℝ) : ℝ := -X ^ 2 / 4 * (G ^ 2 + 2 * Q)

/-- The paper's `h⁶` correction to the discriminant. -/
noncomputable def p5a_D6 (X G : ℝ) : ℝ := X ^ 2 * G / 8

/-- The paper's `h⁸` correction to the discriminant. -/
noncomputable def p5a_D8 (X : ℝ) : ℝ := -X ^ 2 / 64

/-- The frozen Weyl discriminant `4 A_h² - B_h²`. -/
noncomputable def p5a_delta (h X B C D E F : ℝ) : ℝ :=
  4 * ((X ^ 2 - h ^ 2) * p5a_phiBC X B C * p5a_phiEF X E F) -
    (2 * X * (p5a_Q0 X B C D E F - h ^ 2 * p5a_G B C D E F / 4 + h ^ 4 / 16)) ^ 2

/-- Constant coefficient identity, expressed through the library's `P3.cmDet`. -/
theorem p5a_cm_constant (X B C D E F : ℝ) :
    4 * X ^ 2 * p5a_phiBC X B C * p5a_phiEF X E F -
        (2 * X * p5a_Q0 X B C D E F) ^ 2 =
      8 * X ^ 4 * FormalResearch.Racah.P3.cmDet X B C D E F := by
  rw [cmDet_eq_cmDet2,
    cmDet2_eq_eight_det_gramX]
  simp [p5a_phiBC, p5a_phiEF, p5a_Q0, p5a_G, gramX, Matrix.det_fin_three]
  ring

/-- info: 'FormalResearch.EuclTet.p5a_cm_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_cm_constant

/-- Both coefficients in the finite-`h` symbol, and therefore its discriminant, are even in `h`.
This is the polynomial evenness assertion; the recurrence itself is not formalised here. -/
theorem p5a_discriminant_even (h X B C D E F : ℝ) :
    p5a_delta (-h) X B C D E F = p5a_delta h X B C D E F := by
  unfold p5a_delta
  ring

/-- Exact coefficient expansion of the squared frozen symbol (`thm:finitehwall`). The four
correction terms are the paper's printed `𝒟₂`, `𝒟₄`, `𝒟₆`, and `𝒟₈`. -/
theorem p5a_discriminant_expansion (h X B C D E F : ℝ) :
    p5a_delta h X B C D E F =
      8 * X ^ 4 * FormalResearch.Racah.P3.cmDet X B C D E F +
        h ^ 2 * p5a_D2 X B C E F (p5a_Q0 X B C D E F) (p5a_G B C D E F) +
        h ^ 4 * p5a_D4 X (p5a_Q0 X B C D E F) (p5a_G B C D E F) +
        h ^ 6 * p5a_D6 X (p5a_G B C D E F) + h ^ 8 * p5a_D8 X := by
  unfold p5a_delta p5a_D2 p5a_D4 p5a_D6 p5a_D8
  rw [← p5a_cm_constant]
  unfold p5a_Q0 p5a_G
  ring

/-- info: 'FormalResearch.EuclTet.p5a_discriminant_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_discriminant_expansion

/-- info: 'FormalResearch.EuclTet.p5a_discriminant_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_discriminant_even

end FormalResearch.EuclTet
