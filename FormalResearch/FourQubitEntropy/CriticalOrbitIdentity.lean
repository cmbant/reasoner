import FormalResearch.FourQubitEntropy.CriticalOrbitPr

/-!
# Critical-orbit stability: the three-term identity

`eq:fqe-critical-three-term` of `critical_orbit_stability.tex`.  The twelve cut probabilities are
quadratic in `p_i = |v_i|²` and `c_{ij} = Re (conj v_i v_j)` (`pr_pc`), and the identity holds modulo
the four `3 × 3` Gram minors (`gram3`), which vanish because the `v_i` are vectors of `ℝ²`.
-/

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- The determinant of a `3 × 3` real Gram matrix. -/
def gram3 (p q r a b c : ℝ) : ℝ := p * q * r + 2 * a * b * c - p * c ^ 2 - q * b ^ 2 - r * a ^ 2

/-- The twelve cut probabilities as functions of `p_i`, `c_{ij}`. -/
noncomputable def prPC (p0 p1 p2 p3 c01 c02 c03 c12 c13 c23 : ℝ) : Fin 12 → ℝ :=
  ![
    p0,
    p1,
    p2,
    p3,
    (p0 + p1 + p2 + p3 + 2 * (-c01 + c02 - c03 - c12 + c13 - c23)) / 4,
    (p0 + p1 + p2 + p3 + 2 * (-c01 - c02 + c03 + c12 - c13 - c23)) / 4,
    (p0 + p1 + p2 + p3 + 2 * (c01 + c02 + c03 + c12 + c13 + c23)) / 4,
    (p0 + p1 + p2 + p3 + 2 * (c01 - c02 - c03 - c12 - c13 + c23)) / 4,
    (p0 + p1 + p2 + p3 + 2 * (-c01 - c02 - c03 + c12 + c13 + c23)) / 4,
    (p0 + p1 + p2 + p3 + 2 * (-c01 + c02 + c03 - c12 - c13 + c23)) / 4,
    (p0 + p1 + p2 + p3 + 2 * (c01 - c02 + c03 - c12 + c13 - c23)) / 4,
    (p0 + p1 + p2 + p3 + 2 * (c01 + c02 - c03 + c12 - c13 - c23)) / 4]

theorem q_pc (p0 p1 p2 p3 c01 c02 c03 c12 c13 c23 : ℝ)
    (h012 : gram3 p0 p1 p2 c01 c02 c12 = 0) (h013 : gram3 p0 p1 p3 c01 c03 c13 = 0)
    (h023 : gram3 p0 p2 p3 c02 c03 c23 = 0) (h123 : gram3 p1 p2 p3 c12 c13 c23 = 0) :
    18 * (p0 + p1 + p2 + p3) * ∑ k, prPC p0 p1 p2 p3 c01 c02 c03 c12 c13 c23 k ^ 2
      - 12 * ∑ k, prPC p0 p1 p2 p3 c01 c02 c03 c12 c13 c23 k ^ 3 - 13 * (p0 + p1 + p2 + p3) ^ 3 =
    (p0 + p1 + p2 + p3) ^ 3 / 2 + 18 * ((p0 + p1 - p2 - p3) * (c01 ^ 2 - c23 ^ 2) +
      (p0 + p2 - p1 - p3) * (c02 ^ 2 - c13 ^ 2) + (p0 + p3 - p1 - p2) * (c03 ^ 2 - c12 ^ 2)) := by
  unfold gram3 at *
  rw [sum12 (fun k => prPC p0 p1 p2 p3 c01 c02 c03 c12 c13 c23 k ^ 2),
    sum12 (fun k => prPC p0 p1 p2 p3 c01 c02 c03 c12 c13 c23 k ^ 3)]
  simp only [prPC]
  simp
  linear_combination (-36) * (h012 + h013 + h023 + h123)

/-- `eq:fqe-critical-three-term`: the three-term identity (`p_i = |v_i|²`, `c_{ij} = Re (conj v_i v_j)`). -/
theorem Qv_three_term (v : V) :
    Qv v =
      Nv v ^ 3 / 2 + 18 * (
        (Complex.normSq (v (0, 0)) + Complex.normSq (v (0, 1)) - Complex.normSq (v (1, 0))
            - Complex.normSq (v (1, 1))) *
          (((v (0, 0)).re * (v (0, 1)).re + (v (0, 0)).im * (v (0, 1)).im) ^ 2
            - ((v (1, 0)).re * (v (1, 1)).re + (v (1, 0)).im * (v (1, 1)).im) ^ 2) +
        (Complex.normSq (v (0, 0)) + Complex.normSq (v (1, 0)) - Complex.normSq (v (0, 1))
            - Complex.normSq (v (1, 1))) *
          (((v (0, 0)).re * (v (1, 0)).re + (v (0, 0)).im * (v (1, 0)).im) ^ 2
            - ((v (0, 1)).re * (v (1, 1)).re + (v (0, 1)).im * (v (1, 1)).im) ^ 2) +
        (Complex.normSq (v (0, 0)) + Complex.normSq (v (1, 1)) - Complex.normSq (v (0, 1))
            - Complex.normSq (v (1, 0))) *
          (((v (0, 0)).re * (v (1, 1)).re + (v (0, 0)).im * (v (1, 1)).im) ^ 2
            - ((v (0, 1)).re * (v (1, 0)).re + (v (0, 1)).im * (v (1, 0)).im) ^ 2)) := by
  have hpr : pr v = prPC (Complex.normSq (v (0, 0))) (Complex.normSq (v (0, 1)))
      (Complex.normSq (v (1, 0))) (Complex.normSq (v (1, 1)))
      ((v (0, 0)).re * (v (0, 1)).re + (v (0, 0)).im * (v (0, 1)).im)
      ((v (0, 0)).re * (v (1, 0)).re + (v (0, 0)).im * (v (1, 0)).im)
      ((v (0, 0)).re * (v (1, 1)).re + (v (0, 0)).im * (v (1, 1)).im)
      ((v (0, 1)).re * (v (1, 0)).re + (v (0, 1)).im * (v (1, 0)).im)
      ((v (0, 1)).re * (v (1, 1)).re + (v (0, 1)).im * (v (1, 1)).im)
      ((v (1, 0)).re * (v (1, 1)).re + (v (1, 0)).im * (v (1, 1)).im) := by
    funext k
    fin_cases k <;> simp [pr, prPC, wp, wm, Complex.normSq_apply] <;> ring
  have hN : Nv v = Complex.normSq (v (0, 0)) + Complex.normSq (v (0, 1)) +
      Complex.normSq (v (1, 0)) + Complex.normSq (v (1, 1)) := by
    simp [Nv, Fintype.sum_prod_type, Fin.sum_univ_two]; ring
  have key := q_pc (Complex.normSq (v (0, 0))) (Complex.normSq (v (0, 1)))
      (Complex.normSq (v (1, 0))) (Complex.normSq (v (1, 1)))
      ((v (0, 0)).re * (v (0, 1)).re + (v (0, 0)).im * (v (0, 1)).im)
      ((v (0, 0)).re * (v (1, 0)).re + (v (0, 0)).im * (v (1, 0)).im)
      ((v (0, 0)).re * (v (1, 1)).re + (v (0, 0)).im * (v (1, 1)).im)
      ((v (0, 1)).re * (v (1, 0)).re + (v (0, 1)).im * (v (1, 0)).im)
      ((v (0, 1)).re * (v (1, 1)).re + (v (0, 1)).im * (v (1, 1)).im)
      ((v (1, 0)).re * (v (1, 1)).re + (v (1, 0)).im * (v (1, 1)).im)
      (by simp only [gram3, Complex.normSq_apply]; ring)
      (by simp only [gram3, Complex.normSq_apply]; ring)
      (by simp only [gram3, Complex.normSq_apply]; ring)
      (by simp only [gram3, Complex.normSq_apply]; ring)
  unfold Qv
  rw [hpr, hN]
  exact key

end FormalResearch.FourQubitEntropy.CO
