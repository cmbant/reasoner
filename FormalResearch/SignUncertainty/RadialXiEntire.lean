module

public import FormalResearch.SignUncertainty.RadialContour

/-!
# `XiL W` is entire (`lem:radial-compactness`, Step 4)

Differentiation under the integral sign for `Ξ(s) = ∫ (π/2) e^{π²w³/36 + π² s w} W(w) dv` on `Re w = 1`,
with the Gaussian domination `(1+|v|)‖limInt‖ ≤ B(v)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma limInt_gauss_dom {W : ℂ → ℂ} {M₀ : ℝ} (hW : ∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀) (R : ℝ) :
    ∃ B : ℝ → ℝ, Integrable B ∧
      ∀ s : ℂ, ‖s‖ ≤ R → ∀ v : ℝ, (1 + |v|) * ‖limInt W 1 v s‖ ≤ B v := by
  have hM : 0 ≤ M₀ := le_trans (norm_nonneg _) (hW 1 (by simp))
  have hc : 0 < Real.pi ^ 2 / 12 := by positivity
  obtain ⟨C, hC0, hC⟩ := gauss_poly_bound hc (d := Real.pi ^ 2 * R)
  refine ⟨fun v => 2 * M₀ * Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * R) * C *
    Real.exp (-(Real.pi ^ 2 / 12 / 2) * v ^ 2), ?_, ?_⟩
  · have := (integrable_exp_neg_mul_sq (b := Real.pi ^ 2 / 12 / 2) (by positivity)).const_mul
      (2 * M₀ * Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * R) * C)
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp [neg_mul]
  · intro s hs v
    have h1 := norm_limInt_le hW (u := 1) one_pos v s
    have hre : s.re ≤ R := le_trans (Complex.re_le_norm s) hs
    have him : -s.im * v ≤ R * |v| := by
      have : |s.im| ≤ R := le_trans (Complex.abs_im_le_norm s) hs
      calc -s.im * v ≤ |-s.im * v| := le_abs_self _
        _ = |s.im| * |v| := by rw [abs_mul, abs_neg]
        _ ≤ R * |v| := by gcongr
    have h2 : ‖limInt W 1 v s‖ ≤ M₀ * Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * R) *
        Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2 + Real.pi ^ 2 * R * |v|) := by
      refine h1.trans ?_
      rw [mul_assoc M₀, ← Real.exp_add]
      gcongr
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hre (sq_nonneg Real.pi),
        mul_le_mul_of_nonneg_left him (sq_nonneg Real.pi)]
    have h3 : (1 + |v|) ≤ 2 * (1 + v ^ 2) := by nlinarith [sq_nonneg (|v| - 1), sq_abs v]
    have h4 := hC v
    calc (1 + |v|) * ‖limInt W 1 v s‖
        ≤ (2 * (1 + v ^ 2)) * (M₀ * Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * R) *
          Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2 + Real.pi ^ 2 * R * |v|)) := by gcongr
      _ = 2 * M₀ * Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * R) *
          ((1 + v ^ 2) * Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2 + Real.pi ^ 2 * R * |v|)) := by ring
      _ ≤ 2 * M₀ * Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * R) *
          (C * Real.exp (-(Real.pi ^ 2 / 12 / 2) * v ^ 2)) := by gcongr
      _ = _ := by ring

lemma continuous_limInt_v {W : ℂ → ℂ} (hWd : DifferentiableOn ℂ W {w | 0 < w.re}) (s : ℂ) :
    Continuous fun v : ℝ => limInt W 1 v s := by
  unfold limInt
  have hl : Continuous fun v : ℝ => (((1 : ℝ) : ℂ) + (v : ℂ) * Complex.I) := by fun_prop
  refine Continuous.mul (by fun_prop) ?_
  exact hWd.continuousOn.comp_continuous hl (fun v => by simp)

lemma hasDerivAt_limInt_s (W : ℂ → ℂ) (v : ℝ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => limInt W 1 v s)
      ((Real.pi ^ 2 : ℂ) * (((1 : ℝ) : ℂ) + (v : ℂ) * Complex.I) * limInt W 1 v s) s := by
  set w : ℂ := ((1 : ℝ) : ℂ) + (v : ℂ) * Complex.I with hw
  have h1 : HasDerivAt (fun s : ℂ => (Real.pi ^ 2 / 36 : ℂ) * w ^ 3 + (Real.pi ^ 2 : ℂ) * s * w)
      ((Real.pi ^ 2 : ℂ) * w) s := by
    have := (((hasDerivAt_id s).const_mul (Real.pi ^ 2 : ℂ)).mul_const w).const_add
      ((Real.pi ^ 2 / 36 : ℂ) * w ^ 3)
    simpa using this
  have h2 := (h1.cexp).mul_const (W w)
  unfold limInt
  convert h2 using 1
  ring

theorem differentiable_XiL {W : ℂ → ℂ} {M₀ : ℝ} (hW : ∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀)
    (hWd : DifferentiableOn ℂ W {w | 0 < w.re}) : Differentiable ℂ (XiL W) := by
  intro s₀
  obtain ⟨B, hB, hBd⟩ := limInt_gauss_dom hW (‖s₀‖ + 1)
  have hint : ∀ s : ℂ, Integrable (fun v : ℝ => limInt W 1 v s) := by
    intro s
    obtain ⟨B', hB', hBd'⟩ := limInt_gauss_dom hW ‖s‖
    refine hB'.mono' (continuous_limInt_v hWd s).aestronglyMeasurable (ae_of_all _ fun v => ?_)
    have := hBd' s le_rfl v
    have h1 : ‖limInt W 1 v s‖ ≤ (1 + |v|) * ‖limInt W 1 v s‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg v])
    exact h1.trans this
  have hnorm : ∀ v : ℝ, ‖((1 : ℝ) : ℂ) + (v : ℂ) * Complex.I‖ ≤ 1 + |v| := by
    intro v
    refine (norm_add_le _ _).trans ?_
    simp
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := volume)
    (F := fun s v => ((Real.pi / 2 : ℝ) : ℂ) * limInt W 1 v s)
    (F' := fun s v => ((Real.pi / 2 : ℝ) : ℂ) *
      ((Real.pi ^ 2 : ℂ) * (((1 : ℝ) : ℂ) + (v : ℂ) * Complex.I) * limInt W 1 v s))
    (x₀ := s₀) (bound := fun v => Real.pi / 2 * Real.pi ^ 2 * B v) (s := Metric.ball s₀ 1)
    (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun s => ((continuous_limInt_v hWd s).const_mul _).aestronglyMeasurable)
    ((hint s₀).const_mul _)
    (by
      have : Continuous fun v : ℝ => ((Real.pi / 2 : ℝ) : ℂ) *
          ((Real.pi ^ 2 : ℂ) * (((1 : ℝ) : ℂ) + (v : ℂ) * Complex.I) * limInt W 1 v s₀) := by
        have := continuous_limInt_v hWd s₀
        fun_prop
      exact this.aestronglyMeasurable)
    (ae_of_all _ fun v s hs => by
      have hs' : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have := Metric.mem_ball.mp hs
        rw [dist_eq_norm] at this
        calc ‖s‖ = ‖(s - s₀) + s₀‖ := by ring_nf
          _ ≤ ‖s - s₀‖ + ‖s₀‖ := norm_add_le _ _
          _ ≤ ‖s₀‖ + 1 := by linarith
      have hb := hBd s hs' v
      rw [norm_mul, norm_mul, norm_mul]
      have e1 : ‖((Real.pi / 2 : ℝ) : ℂ)‖ = Real.pi / 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have e2 : ‖((Real.pi ^ 2 : ℂ))‖ = Real.pi ^ 2 := by
        rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [e1, e2]
      have : ‖((1 : ℝ) : ℂ) + (v : ℂ) * Complex.I‖ * ‖limInt W 1 v s‖ ≤ B v :=
        (mul_le_mul_of_nonneg_right (hnorm v) (norm_nonneg _)).trans hb
      calc Real.pi / 2 * (Real.pi ^ 2 * ‖((1 : ℝ) : ℂ) + (v : ℂ) * Complex.I‖ * ‖limInt W 1 v s‖)
          = Real.pi / 2 * Real.pi ^ 2 *
            (‖((1 : ℝ) : ℂ) + (v : ℂ) * Complex.I‖ * ‖limInt W 1 v s‖) := by ring
        _ ≤ Real.pi / 2 * Real.pi ^ 2 * B v := by gcongr)
    (hB.const_mul _)
    (ae_of_all _ fun v s _ => (hasDerivAt_limInt_s W v s).const_mul _)
  exact key.2.differentiableAt

/-- info: 'FormalResearch.SignUncertainty.differentiable_XiL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiable_XiL

end FormalResearch.SignUncertainty
