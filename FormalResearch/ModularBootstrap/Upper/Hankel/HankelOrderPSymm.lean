module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelOrderP

/-!
# Reflection of the order-`p` Hankel function

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, proof of Lemma `FW-SD` (`fw:SDp`), step (2)
(iii): the reflection symmetry of the order-`p` integrand on `E₊` rests on
`H_p¹(-z̄) = (-1)^{p+1} conj (H_p¹(z))` for `Im z > 0` (DLMF 10.11.5 with `conj H_p¹(z) = H_p²(z̄)`).

`laplaceCosh_conj`: the Laplace integral `∫₀^∞ e^{-w cosh s} g(s) ds` of a real profile `g` commutes with
complex conjugation in `w`.  With `H_p¹(z) = (2/(π i)) e^{-iπp/2} K_p(-i z)` and `-i(-z̄) = conj(-i z)` this gives
`hankelOrd_reflection`, whose `p = 0` case is `hankel0_reflection`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

lemma laplaceCosh_conj (g : ℝ → ℝ) (w : ℂ) :
    laplaceCosh g ((starRingEnd ℂ) w) = (starRingEnd ℂ) (laplaceCosh g w) := by
  unfold laplaceCosh
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [map_neg, map_mul, ← Complex.exp_conj, neg_mul, Complex.conj_ofReal]

lemma besselKP_conj (ν : ℝ) (w : ℂ) :
    besselKP ν ((starRingEnd ℂ) w) = (starRingEnd ℂ) (besselKP ν w) :=
  laplaceCosh_conj _ w

/-- `H_p¹(-z̄) = (-1)^{p+1} conj (H_p¹(z))`. -/
theorem hankelOrd_reflection (p : ℕ) (z : ℂ) :
    hankelOrd p (-(starRingEnd ℂ) z) = (-1 : ℂ) ^ (p + 1) * (starRingEnd ℂ) (hankelOrd p z) := by
  unfold hankelOrd
  have h1 : -I * (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (-I * z) := by
    simp [Complex.conj_I]
  have hexp : (starRingEnd ℂ) (Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2))) =
      (-1 : ℂ) ^ p * Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) := by
    rw [← Complex.exp_conj]
    have e : (starRingEnd ℂ) (-(I * (π : ℂ) * (p : ℂ) / 2)) =
        -(I * (π : ℂ) * (p : ℂ) / 2) + (p : ℂ) * ((π : ℂ) * I) := by
      simp only [map_neg, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast,
        map_ofNat]
      ring
    rw [e, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    ring
  have hs : (-1 : ℂ) ^ p * (-1 : ℂ) ^ p = 1 := by rw [← mul_pow]; simp
  have hI : (starRingEnd ℂ) I = -I := Complex.conj_I
  rw [h1, besselKP_conj, map_mul, map_mul, map_div₀, map_mul, hI, Complex.conj_ofReal,
    map_ofNat, hexp, pow_succ]
  have hI0 : I ≠ 0 := Complex.I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  generalize (starRingEnd ℂ) (besselKP (p : ℝ) (-I * z)) = K
  generalize Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) = A
  field_simp
  linear_combination (-A * K) * hs

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hankelOrd_reflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelOrd_reflection

end FormalResearch.ModularBootstrap.Upper.Hankel
