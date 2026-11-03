module

public import FormalResearch.FourQubitEntropy.PaperEGapNullBloch

/-!
# Null-critical states: the 32 overlaps in Bloch coordinates

For the vector `v = B†(a ⊗ b)` (`vOf`) with unit `a, b` and Bloch vectors `r = bl a`, `s = bl b`, the overlap
of `v` with the `a`-th representative `η_a` of `𝓗` is
`q_a = (1 + ε_a·r/√3)(1 + η'_a·s/√3)/4` (`qH_vOf`), where `(ε_a, η'_a)` are the cube vertices of opposite
parity `epsT a, etaT a`.  Exact polynomial identities, checked per representative.
-/

@[expose] public section


set_option linter.unusedSimpArgs false

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- The cube vertex `ε` (signs in `ℝ³`) attached to the `a`-th representative of `𝓗`. -/
def epsT : Fin 32 → Fin 3 → ℝ :=
![![-1, -1, -1],
  ![1, -1, -1],
  ![-1, 1, -1],
  ![1, 1, -1],
  ![-1, -1, 1],
  ![1, -1, 1],
  ![-1, 1, 1],
  ![1, 1, 1],
  ![1, -1, 1],
  ![-1, -1, 1],
  ![1, -1, -1],
  ![-1, -1, -1],
  ![1, 1, 1],
  ![-1, 1, 1],
  ![1, 1, -1],
  ![-1, 1, -1],
  ![1, 1, -1],
  ![1, -1, -1],
  ![1, 1, 1],
  ![1, -1, 1],
  ![-1, 1, -1],
  ![-1, -1, -1],
  ![-1, 1, 1],
  ![-1, -1, 1],
  ![-1, 1, 1],
  ![-1, 1, -1],
  ![-1, -1, 1],
  ![-1, -1, -1],
  ![1, 1, 1],
  ![1, 1, -1],
  ![1, -1, 1],
  ![1, -1, -1]]

/-- The cube vertex `η` attached to the `a`-th representative of `𝓗`. -/
def etaT : Fin 32 → Fin 3 → ℝ :=
![![-1, 1, -1],
  ![1, 1, -1],
  ![-1, -1, -1],
  ![1, -1, -1],
  ![-1, 1, 1],
  ![1, 1, 1],
  ![-1, -1, 1],
  ![1, -1, 1],
  ![1, -1, -1],
  ![-1, -1, -1],
  ![1, -1, 1],
  ![-1, -1, 1],
  ![1, 1, -1],
  ![-1, 1, -1],
  ![1, 1, 1],
  ![-1, 1, 1],
  ![-1, -1, 1],
  ![-1, 1, 1],
  ![-1, -1, -1],
  ![-1, 1, -1],
  ![1, -1, 1],
  ![1, 1, 1],
  ![1, -1, -1],
  ![1, 1, -1],
  ![1, 1, 1],
  ![1, 1, -1],
  ![1, -1, 1],
  ![1, -1, -1],
  ![-1, 1, 1],
  ![-1, 1, -1],
  ![-1, -1, 1],
  ![-1, -1, -1]]

theorem hc_vOf (a0 a1 b0 b1 : ℂ) (j : Fin 4) :
    coord (vOf a0 a1 b0 b1) j = rt * coord (uOf a0 a1 b0 b1) j := by
  fin_cases j <;> rfl

theorem sum_rt_re (a : Fin 32) (a0 a1 b0 b1 : ℂ) :
    ∑ j, epsOf a j * (coord (vOf a0 a1 b0 b1) j).re = rt.re * ∑ j, epsOf a j * (coord (uOf a0 a1 b0 b1) j).re ∧
    ∑ j, epsOf a j * (coord (vOf a0 a1 b0 b1) j).im = rt.re * ∑ j, epsOf a j * (coord (uOf a0 a1 b0 b1) j).im := by
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hc_vOf, Complex.mul_re, rt_im]; ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hc_vOf, Complex.mul_im, rt_im]; ring

theorem Aq_vOf (a : Fin 32) (a0 a1 b0 b1 : ℂ) :
    Aq a (vOf a0 a1 b0 b1) = 1 / 2 * Aq a (uOf a0 a1 b0 b1) := by
  have hs := rt_sq
  obtain ⟨h1, h2⟩ := sum_rt_re a a0 a1 b0 b1
  unfold Aq Sx Sy
  rw [h1, h2, hc_vOf, Complex.normSq_mul, normSq_rt]
  linear_combination ((∑ j, epsOf a j * (coord (uOf a0 a1 b0 b1) j).re) ^ 2 +
    (∑ j, epsOf a j * (coord (uOf a0 a1 b0 b1) j).im) ^ 2) * hs

theorem Cq_vOf (a : Fin 32) (a0 a1 b0 b1 : ℂ) :
    Cq a (vOf a0 a1 b0 b1) = 1 / 2 * Cq a (uOf a0 a1 b0 b1) := by
  have hs := rt_sq
  obtain ⟨h1, h2⟩ := sum_rt_re a a0 a1 b0 b1
  unfold Cq Sx Sy
  rw [h1, h2, hc_vOf]
  simp only [Complex.mul_re, Complex.mul_im, rt_im]
  linear_combination ((coord (uOf a0 a1 b0 b1) (idxI a)).re * ∑ j, epsOf a j * (coord (uOf a0 a1 b0 b1) j).im
    - (coord (uOf a0 a1 b0 b1) (idxI a)).im * ∑ j, epsOf a j * (coord (uOf a0 a1 b0 b1) j).re) * hs

/-- `Σ_α ε_α r_α`. -/
def dotv (e : Fin 3 → ℝ) (r : Fin 3 → ℝ) : ℝ := e 0 * r 0 + e 1 * r 1 + e 2 * r 2

set_option maxHeartbeats 8000000 in
theorem Aq_uOf (a : Fin 32) (a0 a1 b0 b1 : ℂ) :
    Aq a (uOf a0 a1 b0 b1) = 3 * (Complex.normSq a0 + Complex.normSq a1) * (Complex.normSq b0 + Complex.normSq b1)
      + dotv (epsT a) (bl a0 a1) * dotv (etaT a) (bl b0 b1) := by
  fin_cases a <;>
  simp [Aq, Sx, Sy, coord, epsOf, idxI, uOf, bl, dotv, epsT, etaT, Fin.sum_univ_four, Complex.normSq_apply] <;>
  ring

set_option maxHeartbeats 8000000 in
theorem Cq_uOf (a : Fin 32) (a0 a1 b0 b1 : ℂ) :
    2 * Cq a (uOf a0 a1 b0 b1) = (Complex.normSq a0 + Complex.normSq a1) * dotv (etaT a) (bl b0 b1)
      + (Complex.normSq b0 + Complex.normSq b1) * dotv (epsT a) (bl a0 a1) := by
  fin_cases a <;>
  simp [Cq, Sx, Sy, coord, epsOf, idxI, uOf, bl, dotv, epsT, etaT, Fin.sum_univ_four, Complex.normSq_apply] <;>
  ring

/-- **`q_η = (1 + ε·r/√3)(1 + η'·s/√3)/4`** for the `a`-th representative of `𝓗`, for the vector
`v = B†(a ⊗ b)` with unit `a, b` and Bloch vectors `r = bl a`, `s = bl b`. -/
theorem qH_vOf (a : Fin 32) (a0 a1 b0 b1 : ℂ) (ha : Complex.normSq a0 + Complex.normSq a1 = 1)
    (hb : Complex.normSq b0 + Complex.normSq b1 = 1) :
    qH a (vOf a0 a1 b0 b1) =
      (1 + dotv (epsT a) (bl a0 a1) / Real.sqrt 3) * (1 + dotv (etaT a) (bl b0 b1) / Real.sqrt 3) / 4 := by
  have hA := Aq_uOf a a0 a1 b0 b1
  have hC := Cq_uOf a a0 a1 b0 b1
  rw [ha, hb] at hA hC
  unfold qH
  rw [Aq_vOf, Cq_vOf]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have ht : (Real.sqrt 3)⁻¹ = Real.sqrt 3 / 3 := by
    have h0 : Real.sqrt 3 ≠ 0 := by positivity
    field_simp; linarith [h3]
  simp only [div_eq_mul_inv, ht]
  rw [hA]
  linear_combination (Real.sqrt 3 / 12) * hC
    - (dotv (epsT a) (bl a0 a1) * dotv (etaT a) (bl b0 b1) / 36) * h3

end FormalResearch.FourQubitEntropy.CO
