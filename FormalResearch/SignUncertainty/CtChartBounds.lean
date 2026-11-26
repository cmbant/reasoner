module

public import FormalResearch.SignUncertainty.CtChartHad

/-!
# Taylor bounds in the first variable for a smooth two-variable function (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2/3 (the expansion `Q_ε(s;a) = Q_0 + i h̃ s + R_ε`,
`R_ε = O(|a| + |s|²)`, `∂_s R_ε = O(|a| + |s|)`).  **Proved.**
For `F` smooth at `(0,0)`: `|F(s,β) - F(0,0) - ∂_sF(0,0) s| ≤ C(|β| + |s|²)` and `|∂_sF(s,β) - ∂_sF(0,0)| ≤ C(|s| + |β|)`
near `(0,0)`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma lipschitz_of_cd {F : ℂ × ℂ → ℂ} (hF : ContDiffAt ℂ ∞' F (0, 0)) :
    ∃ (K : NNReal) (r : ℝ), 0 < r ∧ LipschitzOnWith K F (Metric.ball ((0 : ℂ), (0 : ℂ)) r) := by
  have h1 : ContDiffAt ℝ 1 F (0, 0) := (hF.of_le (by simp)).restrict_scalars ℝ
  obtain ⟨K, t, ht, hL⟩ := h1.exists_lipschitzOnWith
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp ht
  exact ⟨K, r, hr, hL.mono hb⟩

lemma norm_prod_le (s β : ℂ) : ‖(s, β)‖ ≤ ‖s‖ + ‖β‖ := by
  rw [Prod.norm_def]; exact max_le (by linarith [norm_nonneg β]) (by linarith [norm_nonneg s])

lemma mem_ball_prod {s β : ℂ} {r : ℝ} (hs : ‖s‖ < r) (hβ : ‖β‖ < r) :
    (s, β) ∈ Metric.ball ((0 : ℂ), (0 : ℂ)) r := by
  rw [Metric.mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]; exact max_lt hs hβ

lemma taylor_s_bounds {F : ℂ × ℂ → ℂ} (hF : ContDiffAt ℂ ∞' F (0, 0)) :
    ∃ C ρ : ℝ, 0 < ρ ∧ ∀ s β : ℂ, ‖s‖ < ρ → ‖β‖ < ρ →
      ‖F (s, β) - F (0, 0) - dyF F (0, 0) * s‖ ≤ C * (‖β‖ + ‖s‖ ^ 2) ∧
      ‖dyF F (s, β) - dyF F (0, 0)‖ ≤ C * (‖s‖ + ‖β‖) := by
  obtain ⟨K1, r1, hr1, hL1⟩ := lipschitz_of_cd hF
  obtain ⟨K2, r2, hr2, hL2⟩ := lipschitz_of_cd (contDiffAt_dyF hF)
  obtain ⟨r3, hr3, hd⟩ := Metric.eventually_nhds_iff_ball.mp (ev_diff hF)
  set ρ := min (min r1 r2) r3 with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hr1 hr2) hr3
  have hρ1 : ρ ≤ r1 := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ r2 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3 : ρ ≤ r3 := min_le_right _ _
  have hK1 : (0 : ℝ) ≤ K1 := K1.coe_nonneg
  have hK2 : (0 : ℝ) ≤ K2 := K2.coe_nonneg
  have h00 : ((0 : ℂ), (0 : ℂ)) ∈ Metric.ball ((0 : ℂ), (0 : ℂ)) r2 := Metric.mem_ball_self hr2
  refine ⟨(K1 : ℝ) + K2, ρ, hρ0, fun s β hs hβ => ⟨?_, ?_⟩⟩
  · -- first bound
    have hts : ∀ t ∈ Icc (0 : ℝ) 1, ‖(t : ℂ) * s‖ ≤ ‖s‖ := by
      intro t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      nlinarith [norm_nonneg s, ht.2]
    have hmem2 : ∀ t ∈ Icc (0 : ℝ) 1, ((t : ℂ) * s, (0 : ℂ)) ∈ Metric.ball ((0 : ℂ), (0 : ℂ)) r2 := fun t ht =>
      mem_ball_prod (lt_of_le_of_lt (hts t ht) (hs.trans_le hρ2)) (by simpa using hr2)
    have hmem3 : ∀ t ∈ Icc (0 : ℝ) 1, ((t : ℂ) * s, (0 : ℂ)) ∈ Metric.ball ((0 : ℂ), (0 : ℂ)) r3 := fun t ht =>
      mem_ball_prod (lt_of_le_of_lt (hts t ht) (hs.trans_le hρ3)) (by simpa using hr3)
    -- slice Taylor identity
    have hT := taylor1_seg (p := fun y : ℂ => F (y, 0)) (p1 := fun y : ℂ => dyF F (y, 0)) (z := s) (β := 0)
      (fun t ht => by
        have := hasDerivAt_slice1 (q := ((t : ℂ) * s, (0 : ℂ))) (hd _ (hmem3 t ht))
        simpa [dyF] using this)
      (by
        have hc : ContinuousOn (dyF F) (Metric.ball ((0 : ℂ), (0 : ℂ)) r2) := hL2.continuousOn
        have hcc : ContinuousOn (fun t : ℝ => ((t : ℂ) * s, (0 : ℂ))) (Icc 0 1) := by fun_prop
        simp only [zero_add, sub_zero]
        exact hc.comp hcc (fun t ht => hmem2 t ht))
    simp only [zero_add, sub_zero] at hT
    have hint : ‖∫ t in (0 : ℝ)..1, (dyF F ((t : ℂ) * s, 0) - dyF F (0, 0))‖ ≤ K2 * ‖s‖ := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
        (f := fun t : ℝ => dyF F ((t : ℂ) * s, 0) - dyF F (0, 0)) (C := K2 * ‖s‖) (by
          intro t ht
          rw [uIoc_of_le zero_le_one] at ht
          have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
          have := hL2.dist_le_mul _ (hmem2 t ht') _ h00
          rw [dist_eq_norm, dist_eq_norm] at this
          have e : (((t : ℂ) * s, (0 : ℂ)) - ((0 : ℂ), (0 : ℂ))) = ((t : ℂ) * s, (0 : ℂ)) := by simp
          rw [e] at this
          refine this.trans ?_
          refine mul_le_mul_of_nonneg_left ?_ hK2
          rw [Prod.norm_def]
          simpa using hts t ht')
      simpa using this
    have hii : IntervalIntegrable (fun t : ℝ => dyF F ((t : ℂ) * s, 0)) MeasureTheory.volume 0 1 := by
      have hc : ContinuousOn (dyF F) (Metric.ball ((0 : ℂ), (0 : ℂ)) r2) := hL2.continuousOn
      have hcc : ContinuousOn (fun t : ℝ => ((t : ℂ) * s, (0 : ℂ))) (Icc 0 1) := by fun_prop
      exact (hc.comp hcc (fun t ht => hmem2 t ht)).intervalIntegrable_of_Icc zero_le_one
    have hT' : F (s, 0) - F (0, 0) = s * ∫ t in (0 : ℝ)..1, dyF F ((t : ℂ) * s, 0) := by simpa using hT
    have hB : ‖F (s, 0) - F (0, 0) - dyF F (0, 0) * s‖ ≤ K2 * ‖s‖ ^ 2 := by
      have e : F (s, 0) - F (0, 0) - dyF F (0, 0) * s =
          s * ∫ t in (0 : ℝ)..1, (dyF F ((t : ℂ) * s, 0) - dyF F (0, 0)) := by
        rw [intervalIntegral.integral_sub hii intervalIntegrable_const, intervalIntegral.integral_const]
        simp only [sub_zero, one_smul, smul_eq_mul]
        linear_combination hT'
      rw [e, norm_mul]
      calc ‖s‖ * ‖∫ t in (0 : ℝ)..1, (dyF F ((t : ℂ) * s, 0) - dyF F (0, 0))‖ ≤ ‖s‖ * (K2 * ‖s‖) :=
            mul_le_mul_of_nonneg_left hint (norm_nonneg s)
        _ = K2 * ‖s‖ ^ 2 := by ring
    have hA : ‖F (s, β) - F (s, 0)‖ ≤ K1 * ‖β‖ := by
      have := hL1.dist_le_mul _ (mem_ball_prod (hs.trans_le hρ1) (hβ.trans_le hρ1)) _ (mem_ball_prod (hs.trans_le hρ1) (by rw [norm_zero]; exact hr1))
      rw [dist_eq_norm] at this
      refine this.trans (le_of_eq ?_)
      rw [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg _)]
    have e2 : F (s, β) - F (0, 0) - dyF F (0, 0) * s =
        (F (s, β) - F (s, 0)) + (F (s, 0) - F (0, 0) - dyF F (0, 0) * s) := by ring
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    nlinarith only [hA, hB, hK1, hK2, norm_nonneg β, sq_nonneg ‖s‖, mul_nonneg hK1 (sq_nonneg ‖s‖),
      mul_nonneg hK2 (norm_nonneg β)]
  · have := hL2.dist_le_mul _ (mem_ball_prod (hs.trans_le hρ2) (hβ.trans_le hρ2)) _ h00
    rw [dist_eq_norm, dist_eq_norm] at this
    have e : ((s, β) - ((0 : ℂ), (0 : ℂ))) = (s, β) := by simp
    rw [e] at this
    have h2 := norm_prod_le s β
    nlinarith only [this, h2, hK1, hK2, norm_nonneg s, norm_nonneg β, mul_le_mul_of_nonneg_left h2 hK2,
      mul_nonneg hK1 (add_nonneg (norm_nonneg s) (norm_nonneg β))]

end FormalResearch.SignUncertainty.CtChart
