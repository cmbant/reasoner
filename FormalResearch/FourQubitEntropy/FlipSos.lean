import FormalResearch.FourQubitEntropy.FlipGradientReal
import FormalResearch.FourQubitEntropy.MomentInequality
import FormalResearch.FourQubitEntropy.FlipPsi

/-!
# The two sums of squares behind the spin-flip calibration

For every `ψ` the identity (S) writes `24 (4F - 3 n W₁) / 4 = A + 144 C` with `A = Σᵢ ‖Rᵢ‖²`
(`Rᵢ = 6 (Vᵢ - 8Uᵢ)`) and `C = Σ_{i<j} ‖(Rᵢ^{(i)} - Rⱼ^{(j)}) z‖²` both nonnegative. Moreover, with the
pairing `Y = Σᵢ Σ_{idx} sgn(idx) Rᵢ(idx) Rᵢ(1 - idx)` of a site tensor with its spin flip,
`Re Y + A = (1/2) Σ ‖R + R̃‖² ≥ 0` (`flip_sos`); this is the positivity behind the exact transport law
`eq:fqe-spin-flip-calibration`.
-/

open scoped ComplexConjugate
open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

theorem pair_nonneg (a b : ℂ) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    0 ≤ Complex.normSq a + Complex.normSq b + 2 * σ * (a * b).re := by
  have : Complex.normSq a + Complex.normSq b + 2 * σ * (a * b).re
      = (a.re + σ * b.re) ^ 2 + (a.im - σ * b.im) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.mul_re]
    have h1 : σ * σ = 1 := by nlinarith
    linear_combination (-(b.re * b.re) - b.im * b.im) * h1
  rw [this]; positivity

theorem sos_core (R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ) :
    0 ≤ (∑ o1, ∑ o2, ∑ o3, ((sgn o1 * sgn o2 * sgn o3 : ℤ) : ℝ) *
          (2 * (R 0 0 0 o1 o2 o3 * R 1 1 1 (1 - o1) (1 - o2) (1 - o3)).re
           - 6 * (R 0 0 1 o1 o2 o3 * R 0 1 1 (1 - o1) (1 - o2) (1 - o3)).re))
      + ∑ o1, ∑ o2, ∑ o3, (Complex.normSq (R 0 0 0 o1 o2 o3) + 3 * Complex.normSq (R 0 0 1 o1 o2 o3)
          + 3 * Complex.normSq (R 0 1 1 o1 o2 o3) + Complex.normSq (R 1 1 1 o1 o2 o3)) := by
  have p0 := pair_nonneg (R 0 0 0 0 0 0) (R 1 1 1 1 1 1) (1) (by norm_num)
  have p1 := pair_nonneg (R 0 0 1 0 0 0) (R 0 1 1 1 1 1) (-1) (by norm_num)
  have p2 := pair_nonneg (R 0 0 0 0 0 1) (R 1 1 1 1 1 0) (-1) (by norm_num)
  have p3 := pair_nonneg (R 0 0 1 0 0 1) (R 0 1 1 1 1 0) (1) (by norm_num)
  have p4 := pair_nonneg (R 0 0 0 0 1 0) (R 1 1 1 1 0 1) (-1) (by norm_num)
  have p5 := pair_nonneg (R 0 0 1 0 1 0) (R 0 1 1 1 0 1) (1) (by norm_num)
  have p6 := pair_nonneg (R 0 0 0 0 1 1) (R 1 1 1 1 0 0) (1) (by norm_num)
  have p7 := pair_nonneg (R 0 0 1 0 1 1) (R 0 1 1 1 0 0) (-1) (by norm_num)
  have p8 := pair_nonneg (R 0 0 0 1 0 0) (R 1 1 1 0 1 1) (-1) (by norm_num)
  have p9 := pair_nonneg (R 0 0 1 1 0 0) (R 0 1 1 0 1 1) (1) (by norm_num)
  have p10 := pair_nonneg (R 0 0 0 1 0 1) (R 1 1 1 0 1 0) (1) (by norm_num)
  have p11 := pair_nonneg (R 0 0 1 1 0 1) (R 0 1 1 0 1 0) (-1) (by norm_num)
  have p12 := pair_nonneg (R 0 0 0 1 1 0) (R 1 1 1 0 0 1) (1) (by norm_num)
  have p13 := pair_nonneg (R 0 0 1 1 1 0) (R 0 1 1 0 0 1) (-1) (by norm_num)
  have p14 := pair_nonneg (R 0 0 0 1 1 1) (R 1 1 1 0 0 0) (-1) (by norm_num)
  have p15 := pair_nonneg (R 0 0 1 1 1 1) (R 0 1 1 0 0 0) (1) (by norm_num)
  simp only [Fin.sum_univ_two, sgn_zero, sgn_one] at *
  norm_num at *
  linarith


theorem ysite_resnorm (φ : Psi) :
    0 ≤ (Ysite0 φ φ.conj).re + (resNorm0 φ φ.conj).re := by
  have key := sos_core (fun x y t o1 o2 o3 => resTensor φ φ.conj x y t o1 o2 o3)
  simp only [Fin.sum_univ_two, sgn_zero, sgn_one] at key
  simp only [Ysite0, resNorm0, resSlot, sum2, resTensor_conj, toAdd_complex, toMul_complex,
    toSub_complex, lit_complex, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, sgn_zero, sgn_one]
  norm_num at key ⊢
  simp only [Complex.normSq_apply] at key ⊢
  linarith


/-- The two sums of squares: for every `ψ` there are `A, C` with `A + 144 C = 24 · Hval ψ` (the identity
(S) of `thm:fqe-moment`, `Hval = 4 F - 3 n W₁`), `C ≥ 0`, and `Re Y + A ≥ 0` for the spin-flip pairing
`Y = Ysum ψ ψ̄` of the site tensors. -/
theorem flip_sos (ψ : Psi) :
    ∃ A C : ℝ, 0 ≤ C ∧ 0 ≤ (Ysum ψ ψ.conj).re + A ∧ 24 * Hval ψ = A + 144 * C := by
  have hd := sexticDefect_zero ψ ψ.conj
  obtain ⟨r0, h0, e0⟩ := resNorm0_nonneg ψ
  obtain ⟨r1, h1, e1⟩ := resNorm0_nonneg (siteSwap 1 ψ)
  obtain ⟨r2, h2, e2⟩ := resNorm0_nonneg (siteSwap 2 ψ)
  obtain ⟨r3, h3, e3⟩ := resNorm0_nonneg (siteSwap 3 ψ)
  obtain ⟨s, hs, es⟩ := pairSum_nonneg ψ
  refine ⟨r0 + r1 + r2 + r3, s, hs, ?_, ?_⟩
  · have y0 := ysite_resnorm ψ
    have y1 := ysite_resnorm (siteSwap 1 ψ)
    have y2 := ysite_resnorm (siteSwap 2 ψ)
    have y3 := ysite_resnorm (siteSwap 3 ψ)
    rw [e0] at y0
    rw [e1] at y1
    rw [e2] at y2
    rw [e3] at y3
    simp only [Complex.ofReal_re] at y0 y1 y2 y3
    simp only [Ysum, siteSwap_conj, toAdd_complex, Complex.add_re]
    linarith
  · simp only [sexticDefect, defectG, siteSwap_conj, toAdd_complex, toMul_complex, toSub_complex,
      lit_complex] at hd
    rw [Fgen_eq, W1gen_eq, normG_eq, e0, e1, e2, e3, es] at hd
    have hr : (96 * sexticF ψ - 72 * (normSqPsi ψ * blochSq ψ) - (r0 + r1 + r2 + r3) - 144 * s : ℝ)
        = 0 := by exact_mod_cast hd
    unfold Hval
    linarith

end FormalResearch.FourQubitEntropy
