module

public import FormalResearch.CohnElkies.PreEdgeCriterion
public import FormalResearch.CohnElkies.LobeSaddleSecondOrder

/-!
# Tangency-Inclusive Pre-Edge Fourier Criterion (`ce_o1_pre_edge.tex`, `cepe:abs-saddle`, `cepe:general`)

Proves Lemma `cepe:abs-saddle` (second-order absolute saddle estimate on a fixed compact dual
interval `J = [a, b] ⊂ (0, ∞)` using `LobeSaddleSecondOrder.lobe_total_saddle_second_order`) and
Proposition `cepe:general` / `cepe:tangency` (tangency-inclusive pre-edge positivity combining
`pe3_compact_origin_pos_on`, `lobe_saddle_asymptotic` on `(0, c^{1/3}] \ J`, and `cepe:abs-saddle` on `J`).
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace FormalResearch.CohnElkies

/-! ### Lemma `cepe:abs-saddle`: second-order absolute saddle estimate on a compact interval `J = [a, b]` -/

/-- **Lemma `cepe:abs-saddle` (`ce_o1_pre_edge.tex`):**
Second-order uniform saddle-point asymptotic on a compact dual interval `J = [a, b] ⊂ (0, ∞)`
for real-symmetric holomorphic two-edge multipliers bounded uniformly on `{Re w > 0}`, without
assuming a pointwise lower bound at the saddle. -/
theorem cepe_abs_saddle {W_S W_D : ℝ → ℂ → ℂ} {a b C_S K_D c_min Δ₁ U : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hCS : 0 ≤ C_S) (hKD : 0 ≤ K_D) (_hc_min : 0 ≤ c_min)
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U)
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤ (3 / 1000 : ℝ))
    (hW_S_diff : ∀ {c : ℝ}, c_min ≤ c → DifferentiableOn ℂ (W_S c) {w : ℂ | 0 < w.re})
    (hW_D_diff : ∀ {c : ℝ}, c_min ≤ c → DifferentiableOn ℂ (W_D c) {w : ℂ | 0 < w.re})
    (hW_S_real : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → (W_S c (x : ℂ)).im = 0)
    (hW_D_real : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → (W_D c (x : ℂ)).im = 0)
    (hW_S_bd : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 < w.re → ‖W_S c w‖ ≤ C_S)
    (hW_D_bd : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 < w.re → ‖W_D c w‖ ≤ K_D) :
    let A : ℝ := C_S + K_D + 1
    let C_abs : ℝ := 1500000 * A * (8 / (3 * a))
    ∀ {c Δ ξ σ_star : ℝ}, max c_min (max (max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ))) ((2 * b + 1) ^ 3)) ≤ c →
      Δ₁ ≤ Δ → Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) →
      ξ = Δ / c → 0 < σ_star → σ_star < 1 → stripGReal σ_star = -Real.log (π ^ 2 * ξ) →
      c ^ (1 / 3 : ℝ) * (1 - σ_star) ∈ Icc a b →
      let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
      let τ_sd := (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))
      let I_val := lobeSaddleIntegral (W_S c) (W_D c) c ξ σ_star
      let x_pos := c ^ (1 / 3 : ℝ) * σ_star
      let x_neg := c ^ (1 / 3 : ℝ) * (1 - σ_star)
      (mellinK0 c (σ_star : ℂ) ξ).im = 0 ∧ 0 < K₀ ∧ I_val.im = 0 ∧
        (W_S c (x_pos : ℂ) + W_D c (x_neg : ℂ)).im = 0 ∧
        |(2 * π * ξ * I_val.re) / (K₀ * Real.sqrt (2 * π) * τ_sd) -
            (W_S c (x_pos : ℂ) + W_D c (x_neg : ℂ)).re| ≤
          C_abs * c ^ (-(2 / 3 : ℝ)) := by
  dsimp only
  intro c Δ ξ σ_star hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq hx_mem
  have hc_min : c_min ≤ c := (le_max_left _ _).trans hc
  have hc_sad : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hc_b : (2 * b + 1) ^ 3 ≤ c :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc_sad]
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  let ε : ℝ := c ^ (-(1 / 3 : ℝ))
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hc_pos _
  have hε_inv : ε⁻¹ = c ^ (1 / 3 : ℝ) := by
    dsimp [ε]; rw [← Real.rpow_neg_one, ← Real.rpow_mul hc_pos.le]; norm_num
  have hε_c : (ε : ℂ)⁻¹ = ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by rw [← Complex.ofReal_inv, hε_inv]
  have hc13_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  have hc13_gt : 2 * b + 1 ≤ c ^ (1 / 3 : ℝ) := by
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact (Real.pow_rpow_inv_natCast (by linarith) (by norm_num : 3 ≠ 0)).symm.le.trans
      (Real.rpow_le_rpow (pow_nonneg (by linarith) 3) hc_b (by norm_num))
  have h1s_lt_half : 1 - σ_star < 1 / 2 := by
    have hmul : c ^ (1 / 3 : ℝ) * (1 - σ_star) ≤ b := hx_mem.2
    rw [show 1 - σ_star = (c ^ (1 / 3 : ℝ) * (1 - σ_star)) / c ^ (1 / 3 : ℝ) by
      field_simp [hc13_pos.ne'], div_lt_iff₀ hc13_pos]
    linarith
  have hd_eq : min σ_star (1 - σ_star) = 1 - σ_star := min_eq_right (by linarith)
  let d := min σ_star (1 - σ_star)
  have hd_pos : 0 < d := lt_min hσ0 h1s_pos
  let x_pos := c ^ (1 / 3 : ℝ) * σ_star
  let x_neg := c ^ (1 / 3 : ℝ) * (1 - σ_star)
  let A : ℝ := C_S + K_D + 1
  have hA_pos : 0 < A := by linarith
  let V : ℂ → ℂ := fun ζ => W_S c (ζ / (ε : ℂ)) + W_D c ((1 - ζ) / (ε : ℂ))
  have hre_ge_pos : ∀ ζ ∈ Metric.ball (σ_star : ℂ) (3 / 4 * d),
      0 < (ζ / (ε : ℂ)).re ∧ 0 < ((1 - ζ) / (ε : ℂ)).re := fun ζ hζ => by
    have hdist : ‖ζ - (σ_star : ℂ)‖ < 3 / 4 * d := by
      simpa only [Metric.mem_ball, Complex.dist_eq] using hζ
    have hre : |ζ.re - σ_star| < 3 / 4 * d := by
      calc |ζ.re - σ_star| = |(ζ - (σ_star : ℂ)).re| := by simp
        _ ≤ ‖ζ - (σ_star : ℂ)‖ := Complex.abs_re_le_norm _
        _ < 3 / 4 * d := hdist
    have hlo : d / 4 < ζ.re := by linarith [(abs_lt.mp hre).1, min_le_left σ_star (1 - σ_star)]
    have hhi : d / 4 < (1 - ζ).re := by
      simp only [Complex.sub_re, Complex.one_re]; linarith [(abs_lt.mp hre).2, min_le_right σ_star (1 - σ_star)]
    rw [Complex.div_ofReal_re, Complex.div_ofReal_re]
    exact ⟨div_pos (lt_trans (by positivity) hlo) hε_pos, div_pos (lt_trans (by positivity) hhi) hε_pos⟩
  have hV_holo : DifferentiableOn ℂ V (Metric.ball (σ_star : ℂ) (3 / 4 * d)) := fun ζ hζ => by
    have hr := hre_ge_pos ζ hζ
    have hS : DifferentiableAt ℂ (fun w => W_S c (w / (ε : ℂ))) ζ :=
      ((hW_S_diff hc_min _ hr.1).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hr.1)).comp
        ζ (differentiableAt_id.div_const _)
    have hD : DifferentiableAt ℂ (fun w => W_D c ((1 - w) / (ε : ℂ))) ζ :=
      ((hW_D_diff hc_min _ hr.2).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hr.2)).comp
        ζ ((differentiableAt_const (1 : ℂ) |>.sub differentiableAt_id).div_const _)
    exact (hS.add hD).differentiableWithinAt
  have hV_bd : ∀ ζ, 0 < ζ.re → ζ.re < 1 → ‖V ζ‖ ≤ A := fun ζ h0 h1 => by
    have hS_re : 0 < (ζ / (ε : ℂ)).re := by rw [Complex.div_ofReal_re]; exact div_pos h0 hε_pos
    have hD_re : 0 < ((1 - ζ) / (ε : ℂ)).re := by
      rw [Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]; exact div_pos (sub_pos.mpr h1) hε_pos
    calc ‖V ζ‖ ≤ ‖W_S c (ζ / (ε : ℂ))‖ + ‖W_D c ((1 - ζ) / (ε : ℂ))‖ := norm_add_le _ _
      _ ≤ C_S + K_D := add_le_add (hW_S_bd hc_min hS_re) (hW_D_bd hc_min hD_re)
      _ ≤ A := by dsimp [A]; linarith
  have hV_disk : ∀ ζ ∈ Metric.closedBall (σ_star : ℂ) (d / 2), ‖V ζ‖ ≤ 1 * A := fun ζ hζ => by
    have hr := hre_ge_pos ζ (Metric.closedBall_subset_ball (by linarith) hζ)
    have h0 : 0 < ζ.re := by
      rw [Complex.div_ofReal_re] at hr; exact (div_pos_iff_of_pos_right hε_pos).mp hr.1
    have h1 : ζ.re < 1 := by
      have h2 := hr.2
      rw [Complex.div_ofReal_re, Complex.sub_re, Complex.one_re] at h2
      linarith [(div_pos_iff_of_pos_right hε_pos).mp h2]
    exact (hV_bd ζ h0 h1).trans_eq (one_mul A).symm
  have hV_var : ∀ τ : ℝ, |τ| ≤ d / 4 → ‖V ((σ_star : ℂ) + (τ : ℂ) * Complex.I) - V (σ_star : ℂ)‖ ≤
      4 * 1 * A * |τ| / d := fun τ hτ => by
    have hr_pos : 0 < d / 4 := by positivity
    have hsub2 : Metric.closedBall (σ_star : ℂ) (d / 2) ⊆ Metric.ball (σ_star : ℂ) (3 / 4 * d) :=
      Metric.closedBall_subset_ball (by linarith)
    have hderiv_bd : ∀ t ∈ uIcc (0 : ℝ) τ, ‖deriv V ((σ_star : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 * A / d := fun t ht => by
      have ht_d4 : |t| ≤ d / 4 := by
        rcases le_or_gt 0 τ with h0 | h0
        · rw [uIcc_of_le h0] at ht; rw [abs_of_nonneg ht.1]; exact ht.2.trans ((le_abs_self τ).trans hτ)
        · rw [uIcc_of_ge h0.le] at ht; rw [abs_of_nonpos ht.2]
          have := abs_of_neg h0; linarith [ht.1]
      let z : ℂ := (σ_star : ℂ) + (t : ℂ) * Complex.I
      have hsub_t : Metric.closedBall z (d / 4) ⊆ Metric.closedBall (σ_star : ℂ) (d / 2) := fun ω hω => by
        rw [Metric.mem_closedBall] at hω ⊢
        have hdist_z : dist z (σ_star : ℂ) ≤ d / 4 := by
          rw [Complex.dist_eq]; simpa [z, Complex.norm_real] using ht_d4
        linarith [dist_triangle ω z (σ_star : ℂ), hω, hdist_z]
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := 1) hr_pos
        ⟨hV_holo.mono (Metric.ball_subset_closedBall.trans (hsub_t.trans hsub2)),
          by simpa only [closure_ball _ hr_pos.ne'] using (hV_holo.continuousOn.mono (hsub_t.trans hsub2))⟩
        fun ω hω => (hV_disk ω (hsub_t (Metric.sphere_subset_closedBall hω))).trans_eq (one_mul A)
      rw [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at hcauchy
      exact hcauchy.trans_eq (by ring)
    have hmem_ball : ∀ t ∈ uIcc (0 : ℝ) τ, ((σ_star : ℂ) + (t : ℂ) * Complex.I) ∈ Metric.ball (σ_star : ℂ) (3 / 4 * d) := fun t ht => by
      have ht_d4 : |t| ≤ d / 4 := by
        rcases le_or_gt 0 τ with h0 | h0
        · rw [uIcc_of_le h0] at ht; rw [abs_of_nonneg ht.1]; exact ht.2.trans ((le_abs_self τ).trans hτ)
        · rw [uIcc_of_ge h0.le] at ht; rw [abs_of_nonpos ht.2]
          have := abs_of_neg h0; linarith [ht.1]
      rw [Metric.mem_ball, Complex.dist_eq]
      simpa [Complex.norm_real] using lt_of_le_of_lt ht_d4 (by linarith : d / 4 < 3 / 4 * d)
    have hd_path : ∀ t ∈ uIcc (0 : ℝ) τ, HasDerivAt (fun u : ℝ => V ((σ_star : ℂ) + (u : ℂ) * Complex.I))
        (Complex.I * deriv V ((σ_star : ℂ) + (t : ℂ) * Complex.I)) t := fun t ht => by
      have hlin : HasDerivAt (fun u : ℝ => (σ_star : ℂ) + (u : ℂ) * Complex.I) Complex.I t :=
        (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add (σ_star : ℂ)).congr_deriv (by simp)
      have hv := ((hV_holo _ (hmem_ball t ht)).differentiableAt (Metric.isOpen_ball.mem_nhds (hmem_ball t ht))).hasDerivAt
      exact (hv.scomp t hlin).congr_deriv (by rw [smul_eq_mul])
    have hcont_deriv : ContinuousOn (fun u : ℝ => Complex.I * deriv V ((σ_star : ℂ) + (u : ℂ) * Complex.I)) (uIcc 0 τ) := by
      have hcd := (hV_holo.analyticOnNhd Metric.isOpen_ball).deriv.continuousOn
      exact continuousOn_const.mul (hcd.comp (by fun_prop) hmem_ball)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd_path hcont_deriv.intervalIntegrable
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hftc
    rw [← hftc]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * A / d) fun t ht => ?_).trans_eq ?_
    · rw [norm_mul, Complex.norm_I, one_mul]; exact hderiv_bd t (uIoc_subset_uIcc ht)
    · rw [sub_zero]; ring
  have hargS : ∀ τ : ℝ, (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)) =
      (x_pos : ℂ) + ((τ / ε : ℝ) : ℂ) * Complex.I := fun τ => by
    rw [div_eq_mul_inv, hε_c]; apply Complex.ext
    · simp [x_pos]; ring
    · simp [div_eq_mul_inv, hε_inv]
  have hargD : ∀ τ : ℝ, ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)) =
      (x_neg : ℂ) + (((-τ / ε : ℝ) : ℂ)) * Complex.I := fun τ => by
    rw [div_eq_mul_inv, hε_c]; apply Complex.ext
    · simp [x_neg]; ring
    · simp [div_eq_mul_inv, hε_inv]
  have hS0 : (σ_star : ℂ) / (ε : ℂ) = (x_pos : ℂ) := by simpa using hargS 0
  have hD0 : (1 - (σ_star : ℂ)) / (ε : ℂ) = (x_neg : ℂ) := by simpa using hargD 0
  let amp : TotalSaddleSecondOrderAmp c σ_star :=
    { V, A, M := 1, Λ := 1, Λ_add := 0, D := 1
      hA := hA_pos, hM := le_rfl, hΛ := le_rfl, hΛ_add := le_rfl, hD := le_rfl
      hΛ_add_half := fun h => absurd h (lt_irrefl 0)
      hV_meas := by
        have hS : Continuous fun τ : ℝ => W_S c (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)) :=
          (hW_S_diff hc_min).continuousOn.comp_continuous (by fun_prop) fun τ => by
            change 0 < (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)).re
            rw [Complex.div_ofReal_re]; simpa using div_pos hσ0 hε_pos
        have hD : Continuous fun τ : ℝ => W_D c ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)) :=
          (hW_D_diff hc_min).continuousOn.comp_continuous (by fun_prop) fun τ => by
            change 0 < ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)).re
            rw [Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]; simpa using div_pos h1s_pos hε_pos
        exact (hS.add hD).aestronglyMeasurable
      hV_symm := fun τ => by
        dsimp [V]
        have hS : W_S c (((σ_star : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) / (ε : ℂ)) =
            starRingEnd ℂ (W_S c (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ))) := by
          rw [hargS (-τ), hargS τ, show (x_pos : ℂ) + (((-τ) / ε : ℝ) : ℂ) * Complex.I =
            starRingEnd ℂ ((x_pos : ℂ) + ((τ / ε : ℝ) : ℂ) * Complex.I) by apply Complex.ext <;> simp [neg_div]]
          exact schwarz_reflection_rhp (hW_S_diff hc_min) (fun x hx => hW_S_real hc_min hx) (by simp; exact mul_pos hc13_pos hσ0)
        have hD : W_D c ((1 - ((σ_star : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I)) / (ε : ℂ)) =
            starRingEnd ℂ (W_D c ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ))) := by
          rw [hargD (-τ), hargD τ, show (x_neg : ℂ) + (((- -τ) / ε : ℝ) : ℂ) * Complex.I =
            starRingEnd ℂ ((x_neg : ℂ) + (((-τ) / ε : ℝ) : ℂ) * Complex.I) by apply Complex.ext <;> simp [neg_div]]
          exact schwarz_reflection_rhp (hW_D_diff hc_min) (fun x hx => hW_D_real hc_min hx) (by simp; exact mul_pos hc13_pos h1s_pos)
        rw [hS, hD, ← map_add]
      hV0_le := hV_bd (σ_star : ℂ) (by simpa using hσ0) (by simpa using hσ1)
      hV_var := hV_var
      hV_vert := fun τ => by
        refine (hV_bd _ (by simpa using hσ0) (by simpa using hσ1)).trans ?_
        split_ifs <;> linarith
      hV_holo := hV_holo
      hV_disk := hV_disk }
  have h_eps0' : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤
      min (3 / 1000 : ℝ) ((4 * amp.M) ^ (-(4 / 3 : ℝ))) := by
    have h4 : (3 / 1000 : ℝ) ≤ ((4 * 1 : ℝ) ^ (-(4 / 3 : ℝ))) := by
      have h4_ge : (4 : ℝ) ^ (4 / 3 : ℝ) ≤ 1000 / 3 := by
        have h3 : ((4 : ℝ) ^ (4 / 3 : ℝ)) ^ 3 ≤ (1000 / 3 : ℝ) ^ 3 := by
          rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by norm_num),
            show (4 / 3 : ℝ) * (3 : ℕ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
          norm_num
        exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h3
      rw [mul_one, Real.rpow_neg (by norm_num), ← one_div]
      exact (div_le_div_of_nonneg_left zero_le_one (by positivity) h4_ge).trans_eq' (by norm_num)
    exact h_eps0.trans (le_min le_rfl h4)
  have h2 := lobe_total_saddle_second_order hΔ₁ hU hc_sad hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp h_eps0'
  dsimp only at h2
  have hI_eq : totalSaddleIntegral amp.V c ξ σ_star = lobeSaddleIntegral (W_S c) (W_D c) c ξ σ_star := rfl
  have hV_eq : amp.V (σ_star : ℂ) = W_S c (x_pos : ℂ) + W_D c (x_neg : ℂ) := by
    change V (σ_star : ℂ) = _; dsimp [V]; rw [hS0, hD0]
  have hεL_sq : saddleEpsL c σ_star ^ 2 ≤ (8 / (3 * a)) * c ^ (-(2 / 3 : ℝ)) := by
    have hg'_pos : 0 < stripGDerivReal σ_star := stripGDerivReal_pos hσ0 hσ1
    have hg'_lo : (3 / 8 : ℝ) / (1 - σ_star) < stripGDerivReal σ_star := by
      have h1 := (stripG_deriv_bounds hσ0 hσ1).1
      have h2 : (3 / 8 : ℝ) < (3 / 4 : ℝ) * σ_star := by linarith
      exact (div_lt_div_of_pos_right h2 h1s_pos).trans h1
    have hτsd_sq : ((c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))) ^ 2 = (c * stripGDerivReal σ_star)⁻¹ := by
      rw [Real.rpow_neg (by positivity), inv_pow, ← Real.rpow_natCast ((c * stripGDerivReal σ_star) ^ (1 / 2 : ℝ)) 2,
        ← Real.rpow_mul (by positivity), show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, Real.rpow_one]
    have hc_prod : c * (1 - σ_star) = c ^ (2 / 3 : ℝ) * x_neg := by
      dsimp [x_neg]; rw [← mul_assoc, ← Real.rpow_add hc_pos, show (2 / 3 : ℝ) + (1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
    have hcm23 : (c ^ (2 / 3 : ℝ))⁻¹ = c ^ (-(2 / 3 : ℝ)) := (Real.rpow_neg hc_pos.le _).symm
    calc saddleEpsL c σ_star ^ 2 = ((c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ)) / (1 - σ_star)) ^ 2 := by
          dsimp [saddleEpsL]; rw [hd_eq]
      _ = (c * stripGDerivReal σ_star * (1 - σ_star) ^ 2)⁻¹ := by
          rw [div_pow, hτsd_sq, div_eq_mul_inv, ← mul_inv]
      _ ≤ (c * ((3 / 8 : ℝ) / (1 - σ_star)) * (1 - σ_star) ^ 2)⁻¹ := by
          apply inv_anti₀ (by positivity); gcongr
      _ = ((3 / 8 : ℝ) * (c * (1 - σ_star)))⁻¹ := by field_simp [h1s_pos.ne']
      _ = (8 / 3 : ℝ) * (c ^ (2 / 3 : ℝ) * x_neg)⁻¹ := by rw [hc_prod, mul_inv]; ring
      _ ≤ (8 / 3 : ℝ) * (c ^ (2 / 3 : ℝ) * a)⁻¹ := by
          gcongr; exact hx_mem.1
      _ = (8 / (3 * a)) * c ^ (-(2 / 3 : ℝ)) := by rw [mul_inv, hcm23]; ring
  rw [hI_eq, hV_eq] at h2
  refine ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.trans ?_⟩
  simp only [amp, mul_one]
  have h150 : ((1000000 : ℝ) + 500000) * A * saddleEpsL c σ_star ^ 2 ≤
      1500000 * A * (8 / (3 * a)) * c ^ (-(2 / 3 : ℝ)) := by
    calc ((1000000 : ℝ) + 500000) * A * saddleEpsL c σ_star ^ 2
        = 1500000 * A * saddleEpsL c σ_star ^ 2 := by ring
      _ ≤ 1500000 * A * ((8 / (3 * a)) * c ^ (-(2 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hεL_sq (by positivity)
      _ = _ := by ring
  linarith [h150]

/-! ### Proposition `cepe:general` (`cepe:tangency`): tangency-inclusive pre-edge criterion -/

/-- Hypotheses of Proposition `cepe:general` / `cepe:tangency` (`ce_o1_pre_edge.tex`)
allowing a compact tangency interval `J = [a_tan, b_tan] ⊂ (0, ∞)` where `W_D` may vanish
and relative bounds are replaced by `‖W_S‖ ≤ C_S`, `‖W_D‖ ≤ K_D`, and `W_D ≥ c_J ε` on `J`. -/
structure PreEdgeTangencyData (fhat : ℝ → ℝ → ℝ) where
  (W_S W_D : ℝ → ℂ → ℂ) (c_min M Λ Λ_add_max x₀ b a_tan b_tan c_J C_S K_D : ℝ)
  (hc_min : 0 ≤ c_min) (hM : 1 ≤ M) (hΛ : 1 ≤ Λ) (hΛ_add : 0 ≤ Λ_add_max) (hx₀ : 0 < x₀) (hb : 0 < b)
  (ha_tan : 0 < a_tan) (hab_tan : a_tan ≤ b_tan) (hc_J : 0 < c_J) (hCS : 0 ≤ C_S) (hKD : 0 ≤ K_D)
  (hW_S_diff : ∀ {c : ℝ}, c_min ≤ c → DifferentiableOn ℂ (W_S c) {w : ℂ | 0 < w.re})
  (hW_D_diff : ∀ {c : ℝ}, c_min ≤ c → DifferentiableOn ℂ (W_D c) {w : ℂ | 0 < w.re})
  (hW_S_real : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → (W_S c (x : ℂ)).im = 0)
  (hW_D_real : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → (W_D c (x : ℂ)).im = 0)
  (hW_S_nonneg : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → 0 ≤ (W_S c (x : ℂ)).re)
  (hW_D_nonneg : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → 0 ≤ (W_D c (x : ℂ)).re)
  (hW0_pos : ∀ {c x_pos x_neg : ℝ}, c_min ≤ c → 0 < x_pos → x_pos ≤ c ^ (1 / 3 : ℝ) →
    0 < x_neg → x_neg ≤ c ^ (1 / 3 : ℝ) → x_neg ∉ Icc a_tan b_tan →
    0 < (W_S c (x_pos : ℂ)).re + (W_D c (x_neg : ℂ)).re)
  (hD_floor : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → x < x₀ → x ∉ Icc a_tan b_tan →
    b * c ^ (-(1 / 3 : ℝ)) ≤ (W_D c (x : ℂ)).re)
  (hA1_S : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → |y| ≤ x / 4 →
    ‖W_S c ((x : ℂ) + (y : ℂ) * Complex.I) - W_S c (x : ℂ)‖ ≤ 4 * M * (|y| / x) * (W_S c (x : ℂ)).re)
  (hA1_D : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → x ∉ Icc a_tan b_tan → |y| ≤ x / 4 →
    ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I) - W_D c (x : ℂ)‖ ≤ 4 * M * (|y| / x) * (W_D c (x : ℂ)).re)
  (hA2_S : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) →
    ‖W_S c ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ * (W_S c (x : ℂ)).re)
  (hA2_D : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → x ∉ Icc a_tan b_tan →
    ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ * (W_D c (x : ℂ)).re +
      (if x < x₀ ∧ x / 2 < |y| then Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 else 0))
  (hD_tan_floor : ∀ {c x : ℝ}, c_min ≤ c → x ∈ Icc a_tan b_tan → x ≤ c ^ (1 / 3 : ℝ) →
    c_J * c ^ (-(1 / 3 : ℝ)) ≤ (W_D c (x : ℂ)).re)
  (hW_S_bd : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 < w.re → ‖W_S c w‖ ≤ C_S)
  (hW_D_bd : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 < w.re → ‖W_D c w‖ ≤ K_D)
  (orig : PE3OriginData fhat (Ico 0 (preEdgeDelta1 M Λ Λ_add_max b)))
  (h_saddle : ∀ {c Δ ξ σ_star : ℝ}, c_min ≤ c → preEdgeDelta1 M Λ Λ_add_max b ≤ Δ →
    Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * preEdgeU M Λ * c ^ (-(2 / 3 : ℝ)))) →
    ξ = Δ / c → 0 < σ_star → σ_star < 1 → stripGReal σ_star = -Real.log (π ^ 2 * ξ) →
    fhat c Δ = (lobeSaddleIntegral (W_S c) (W_D c) c ξ σ_star).re)

/-- **Proposition `cepe:general` / `cepe:tangency` (`ce_o1_pre_edge.tex`):**
shared pre-edge Fourier positivity criterion allowing a compact tangency interval `J = [a_tan, b_tan]`. -/
theorem preEdge_tangency_pos {fhat : ℝ → ℝ → ℝ} (d : PreEdgeTangencyData fhat) :
    ∃ U ≥ 1, ∃ c₀ ≥ 2, ∀ c ≥ c₀, ∀ Δ ∈ Icc 0 ((c / π ^ 2) * Real.exp (-π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))),
      0 < fhat c Δ := by
  let U := preEdgeU d.M d.Λ
  let Δ₁ := preEdgeDelta1 d.M d.Λ d.Λ_add_max d.b
  have hU1 : 1 ≤ U := one_le_preEdgeU d.M d.Λ
  have hΔ₁ : 1 ≤ Δ₁ := one_le_preEdgeDelta1 d.M d.Λ d.Λ_add_max d.b
  obtain ⟨c_orig, _, hc_orig⟩ := pe3_compact_origin_pos_on d.orig
  let A : ℝ := d.C_S + d.K_D + 1
  let C_abs : ℝ := 1500000 * A * (8 / (3 * d.a_tan))
  let c_tan : ℝ := (2 * C_abs / d.c_J + 1) ^ 3
  let c₀ : ℝ := max (max d.c_min c_orig)
    (max (max 2 (max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ))))
      (max ((2 * d.x₀ + 1) ^ 3) (max ((2 * d.b_tan + 1) ^ 3) c_tan)))
  refine ⟨U, hU1, c₀, (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)), fun c hc Δ hΔ => ?_⟩
  have hc_min : d.c_min ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hcorig : c_orig ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc_sad : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
  have hc_x0 : (2 * d.x₀ + 1) ^ 3 ≤ c :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hc_btan : (2 * d.b_tan + 1) ^ 3 ≤ c :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hc_tan : c_tan ≤ c :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc_sad]
  by_cases hlt : Δ < Δ₁
  · exact hc_orig c hcorig Δ ⟨hΔ.1, hlt⟩
  have hΔ_lo : Δ₁ ≤ Δ := not_lt.mp hlt
  have hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) := by
    simpa [neg_mul] using hΔ.2
  let ξ : ℝ := Δ / c
  have hξ_pos : 0 < ξ := div_pos (by linarith) hc_pos
  have hpiξ : π ^ 2 * ξ < 1 := (calc π ^ 2 * ξ ≤ π ^ 2 * ((c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) / c) := by dsimp [ξ]; gcongr
    _ = Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) := by field_simp [Real.pi_ne_zero, hc_pos.ne']).trans_lt
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos (mul_pos (sq_pos_of_pos Real.pi_pos) (by linarith)) (Real.rpow_pos_of_pos hc_pos _))))
  obtain ⟨σ_star, ⟨⟨hσ0, hσ1⟩, hσ_eq⟩, _⟩ := exists_unique_saddleSigma hξ_pos hpiξ
  let x_pos := c ^ (1 / 3 : ℝ) * σ_star
  let x_neg := c ^ (1 / 3 : ℝ) * (1 - σ_star)
  have hc13_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  have hxpos : 0 < x_pos := mul_pos hc13_pos hσ0
  have hxpos_le : x_pos ≤ c ^ (1 / 3 : ℝ) := mul_le_of_le_one_right hc13_pos.le hσ1.le
  have hxneg : 0 < x_neg := mul_pos hc13_pos (sub_pos.mpr hσ1)
  have hxneg_le : x_neg ≤ c ^ (1 / 3 : ℝ) := mul_le_of_le_one_right hc13_pos.le (by linarith)
  have hU_bnd : (27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ)) ≤ min (3 / 1000 : ℝ) ((4 * d.M) ^ (-(4 / 3 : ℝ))) := by
    let ε₀ := min (3 / 1000 : ℝ) ((4 * d.M) ^ (-(4 / 3 : ℝ)))
    have hε₀_pos : 0 < ε₀ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by linarith [d.hM]) _)
    exact (mul_le_mul (by norm_num : (27 / 100 : ℝ) ≤ 1)
      ((Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε₀_pos _)
        (show ε₀ ^ (-(4 / 3 : ℝ)) ≤ U from (le_max_right _ _).trans (le_max_left _ _))
        (by norm_num : -(3 / 4 : ℝ) ≤ 0)).trans_eq
          (by rw [← Real.rpow_mul hε₀_pos.le, show (-(4 / 3 : ℝ)) * (-(3 / 4 : ℝ)) = 1 by norm_num, Real.rpow_one]))
      (by positivity) zero_le_one).trans_eq (one_mul _)
  have hΔ_bnd : Δ₁ ^ (-(1 / 2 : ℝ)) ≤ min (3 / 1000 : ℝ) ((4 * d.M) ^ (-(4 / 3 : ℝ))) := by
    let ε₀ := min (3 / 1000 : ℝ) ((4 * d.M) ^ (-(4 / 3 : ℝ)))
    have hε₀_pos : 0 < ε₀ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by linarith [d.hM]) _)
    exact (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε₀_pos _)
      (show ε₀ ^ (-2 : ℝ) ≤ Δ₁ from (le_max_right _ _).trans (le_max_left _ _))
      (by norm_num : -(1 / 2 : ℝ) ≤ 0)).trans_eq
        (by rw [← Real.rpow_mul hε₀_pos.le, show (-2 : ℝ) * (-(1 / 2 : ℝ)) = 1 by norm_num, Real.rpow_one])
  by_cases htan : x_neg ∈ Icc d.a_tan d.b_tan
  · have h_eps0_tan : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤ (3 / 1000 : ℝ) :=
      (max_le hU_bnd hΔ_bnd).trans (min_le_left _ _)
    have h_abs := cepe_abs_saddle d.ha_tan d.hab_tan d.hCS d.hKD d.hc_min hΔ₁ hU1 h_eps0_tan
      d.hW_S_diff d.hW_D_diff d.hW_S_real d.hW_D_real d.hW_S_bd d.hW_D_bd
      (max_le hc_min (max_le hc_sad hc_btan)) hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq htan
    dsimp only at h_abs
    have h_lead : d.c_J * c ^ (-(1 / 3 : ℝ)) ≤ (d.W_S c (x_pos : ℂ) + d.W_D c (x_neg : ℂ)).re := by
      have hSn := d.hW_S_nonneg hc_min hxpos hxpos_le
      have hDn := d.hD_tan_floor hc_min htan hxneg_le
      simp only [Complex.add_re]; linarith
    have h_err : C_abs * c ^ (-(2 / 3 : ℝ)) < d.c_J * c ^ (-(1 / 3 : ℝ)) := by
      have hC_pos : 0 < C_abs := by
        dsimp [C_abs, A]; have := d.hCS; have := d.hKD; have := d.ha_tan; positivity
      have hc13_ge : 2 * C_abs / d.c_J + 1 ≤ c ^ (1 / 3 : ℝ) := by
        rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact (Real.pow_rpow_inv_natCast (by have := d.hc_J; positivity) (by norm_num : 3 ≠ 0)).symm.le.trans
          (Real.rpow_le_rpow (pow_nonneg (by have := d.hc_J; positivity) 3) hc_tan (by norm_num))
      have hε_lt : c ^ (-(1 / 3 : ℝ)) < d.c_J / (2 * C_abs) := by
        rw [Real.rpow_neg hc_pos.le, ← one_div, div_lt_div_iff₀ hc13_pos (by have := d.hc_J; positivity)]
        have hlt : 2 * C_abs / d.c_J < c ^ (1 / 3 : ℝ) := by linarith
        calc 1 * (2 * C_abs) = d.c_J * (2 * C_abs / d.c_J) := by field_simp [d.hc_J.ne']
          _ < d.c_J * c ^ (1 / 3 : ℝ) := mul_lt_mul_of_pos_left hlt d.hc_J
      have hmul_c : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc_pos]; norm_num
      have hc_err1 : C_abs * c ^ (-(1 / 3 : ℝ)) < d.c_J / 2 := by
        have := mul_lt_mul_of_pos_left hε_lt hC_pos
        refine this.trans_eq ?_; field_simp [hC_pos.ne']
      have hε_pos : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc_pos _
      calc C_abs * c ^ (-(2 / 3 : ℝ)) = (C_abs * c ^ (-(1 / 3 : ℝ))) * c ^ (-(1 / 3 : ℝ)) := by rw [hmul_c]; ring
        _ < (d.c_J / 2) * c ^ (-(1 / 3 : ℝ)) := mul_lt_mul_of_pos_right hc_err1 hε_pos
        _ < d.c_J * c ^ (-(1 / 3 : ℝ)) := by linarith [mul_pos d.hc_J hε_pos]
    have hK₀_pos : 0 < (mellinK0 c (σ_star : ℂ) ξ).re := h_abs.2.1
    have hτsd_pos : 0 < (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (mul_pos hc_pos (stripGDerivReal_pos hσ0 hσ1)) _
    have hden_pos : 0 < (mellinK0 c (σ_star : ℂ) ξ).re * Real.sqrt (2 * π) *
        (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ)) := by positivity
    have h1 := (abs_le.mp h_abs.2.2.2.2).1
    have hq_pos : 0 < (2 * π * ξ * (lobeSaddleIntegral (d.W_S c) (d.W_D c) c ξ σ_star).re) /
        ((mellinK0 c (σ_star : ℂ) ξ).re * Real.sqrt (2 * π) *
          (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))) := by linarith
    have hprod_pos := (div_pos_iff_of_pos_right hden_pos).mp hq_pos
    have hI_pos : 0 < (lobeSaddleIntegral (d.W_S c) (d.W_D c) c ξ σ_star).re := by
      have : 0 < 2 * π * ξ := by positivity
      exact (mul_pos_iff_of_pos_left this).mp hprod_pos
    rw [d.h_saddle hc_min hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq]; exact hI_pos
  · let amp : LobeSaddleAmp σ_star x_pos x_neg :=
      { W_S := d.W_S c, W_D := d.W_D c, M := d.M, Λ := d.Λ
        Λ_add := if x_neg < d.x₀ then d.Λ_add_max else 0, hM := d.hM, hΛ := d.hΛ
        hΛ_add := by split_ifs <;> [exact d.hΛ_add; exact le_rfl]
        hW_S_diff := d.hW_S_diff hc_min, hW_D_diff := d.hW_D_diff hc_min
        hW_S_real := fun _ hx => d.hW_S_real hc_min hx, hW_D_real := fun _ hx => d.hW_D_real hc_min hx
        hW_S_nonneg := d.hW_S_nonneg hc_min hxpos hxpos_le, hW_D_nonneg := d.hW_D_nonneg hc_min hxneg hxneg_le
        hW0_pos := d.hW0_pos hc_min hxpos hxpos_le hxneg hxneg_le htan
        hA1_S := fun _ hy => d.hA1_S hc_min hxpos hxpos_le hy
        hA1_D := fun _ hy => d.hA1_D hc_min hxneg hxneg_le htan hy
        hA2_S := fun y => d.hA2_S hc_min hxpos hxpos_le (y := y)
        hA2_D := fun y => (d.hA2_D hc_min hxneg hxneg_le htan (y := y)).trans_eq
          (by dsimp only [x_neg]; congr 1; by_cases h1 : c ^ (3⁻¹ : ℝ) * (1 - σ_star) < d.x₀ <;> simp [h1])
        hΛ_add_half := fun h => by
          have hxn : x_neg < d.x₀ := by by_contra hn; simp [hn] at h
          have hcr : 2 * d.x₀ + 1 ≤ c ^ (1 / 3 : ℝ) := by
            rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
            exact (Real.pow_rpow_inv_natCast (by linarith [d.hx₀]) (by norm_num : 3 ≠ 0)).symm.le.trans
              (Real.rpow_le_rpow (pow_nonneg (by linarith [d.hx₀]) 3) hc_x0 (by norm_num))
          have h1s : 1 - σ_star < 1 / 2 := by
            rw [show 1 - σ_star = x_neg / c ^ (1 / 3 : ℝ) by dsimp [x_neg]; field_simp [hc13_pos.ne'],
              div_lt_iff₀ hc13_pos]; linarith
          linarith }
    have hasymp := lobe_saddle_asymptotic hΔ₁ hU1 hc_sad hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq amp (max_le hU_bnd hΔ_bnd)
    let C_L2 : ℝ := 8 * amp.M + 54 * amp.Λ + 109; have hC_L2 : 0 < C_L2 := by linarith [amp.hM, amp.hΛ]
    have hU_L2 : (27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ)) ≤ (4 * C_L2)⁻¹ := (mul_le_mul (by norm_num : (27 / 100 : ℝ) ≤ 1)
      ((Real.rpow_le_rpow_of_nonpos (by positivity) (show (4 * C_L2) ^ (4 / 3 : ℝ) ≤ U from le_max_right _ _) (by norm_num : -(3 / 4 : ℝ) ≤ 0)).trans_eq
        (by rw [← Real.rpow_mul (by positivity), show (4 / 3 : ℝ) * (-(3 / 4 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]))
      (by positivity) zero_le_one).trans_eq (one_mul _)
    have hΔ_L2 : Δ₁ ^ (-(1 / 2 : ℝ)) ≤ (4 * C_L2)⁻¹ := (Real.rpow_le_rpow_of_nonpos (by positivity)
      (show (4 * C_L2) ^ 2 ≤ Δ₁ from (le_max_left _ _).trans (le_max_right _ _)) (by norm_num : -(1 / 2 : ℝ) ≤ 0)).trans_eq
      (by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((2 : ℕ) : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one])
    have h_mul_err : C_L2 * saddleEpsL c σ_star ≤ 1 / 4 := (mul_le_mul_of_nonneg_left
      ((saddleEpsL_bounds hΔ₁ hU1 hc_sad hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq).2.2.trans_le (max_le hU_L2 hΔ_L2)).le hC_L2.le).trans_eq (by field_simp [hC_L2.ne'])
    have h_add_err : 150 * amp.Λ_add * (c ^ (-(1 / 3 : ℝ)) /
        ((amp.W_S (x_pos : ℂ)).re + (amp.W_D (x_neg : ℂ)).re)) *
        Real.exp (-(3 / 320 : ℝ) * (c * (1 - σ_star))) ≤ 1 / 4 := by
      by_cases hxn : x_neg < d.x₀
      · have hfl := d.hD_floor hc_min hxneg hxn htan
        have hsnn := d.hW_S_nonneg hc_min hxpos hxpos_le
        have hW0_ge : d.b * c ^ (-(1 / 3 : ℝ)) ≤ (amp.W_S (x_pos : ℂ)).re + (amp.W_D (x_neg : ℂ)).re := by
          dsimp [amp]; linarith
        have hrat : c ^ (-(1 / 3 : ℝ)) / ((amp.W_S (x_pos : ℂ)).re + (amp.W_D (x_neg : ℂ)).re) ≤ d.b⁻¹ := by
          rw [div_le_iff₀ amp.hW0_pos]; exact (mul_le_mul_of_nonneg_left hW0_ge (inv_nonneg.mpr d.hb.le)).trans_eq' (by field_simp [d.hb.ne'])
        have hz_gt := (saddle_endpoint_scales hΔ₁ hU1 hc_sad hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq).2.2
        have hexp_le : Real.exp (-(3 / 320 : ℝ) * (c * (1 - σ_star))) ≤ (3 * π / 320 * Δ₁)⁻¹ := by
          rw [← one_div, le_one_div (Real.exp_pos _) (by positivity), neg_mul, Real.exp_neg, div_inv_eq_mul, one_mul]
          linarith [Real.add_one_le_exp (3 * π / 320 * Δ₁), Real.exp_le_exp.mpr (by linarith [hz_gt] : 3 * π / 320 * Δ₁ ≤ (3 / 320 : ℝ) * (c * (1 - σ_star)))]
        calc 150 * amp.Λ_add * (c ^ (-(1 / 3 : ℝ)) / ((amp.W_S (x_pos : ℂ)).re + (amp.W_D (x_neg : ℂ)).re)) * Real.exp (-(3 / 320 : ℝ) * (c * (1 - σ_star)))
            ≤ 150 * d.Λ_add_max * d.b⁻¹ * (3 * π / 320 * Δ₁)⁻¹ := by
              dsimp [amp]; simp only [hxn, ↓reduceIte]
              exact mul_le_mul (mul_le_mul_of_nonneg_left hrat (by have := d.hΛ_add; positivity)) hexp_le (Real.exp_pos _).le (by have := d.hΛ_add; have := d.hb; positivity)
          _ ≤ 1 / 4 := by
              rw [mul_inv, show 150 * d.Λ_add_max * d.b⁻¹ * ((3 * π / 320)⁻¹ * Δ₁⁻¹) = ((150 * d.Λ_add_max / d.b) * (320 / (3 * π))) * Δ₁⁻¹ by ring, mul_inv_le_iff₀ (by positivity)]
              have hpi3 : (320 : ℝ) / (3 * π) ≤ 36 := by rw [div_le_iff₀ (by positivity)]; linarith [Real.pi_gt_three]
              calc (150 * d.Λ_add_max / d.b) * (320 / (3 * π)) ≤ (150 * d.Λ_add_max / d.b) * 36 := mul_le_mul_of_nonneg_left hpi3 (by have := d.hΛ_add; have := d.hb; positivity)
                _ = (1 / 4) * (144 * (150 * d.Λ_add_max / d.b)) := by ring
                _ ≤ (1 / 4) * Δ₁ := by gcongr; exact (le_max_right _ _).trans (le_max_right _ _)
      · dsimp [amp]; simp only [hxn, ↓reduceIte, mul_zero, zero_mul]; norm_num
    dsimp only at hasymp; dsimp [C_L2] at h_mul_err
    let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
    let W₀ := (amp.W_S (x_pos : ℂ)).re + (amp.W_D (x_neg : ℂ)).re
    let L_lead := (1 / (2 * π * ξ)) * K₀ * W₀ * Real.sqrt (2 * π / (c * stripGDerivReal σ_star))
    have hL_pos : 0 < L_lead := mul_pos (mul_pos (mul_pos (by positivity) hasymp.2.1) amp.hW0_pos) (Real.sqrt_pos.mpr (div_pos (by positivity) (mul_pos hc_pos (stripGDerivReal_pos hσ0 hσ1))))
    have h1 := (abs_le.mp (hasymp.2.2.2.trans ((add_le_add h_mul_err h_add_err).trans (by norm_num : (1 / 4 : ℝ) + 1 / 4 ≤ 1 / 2)))).1
    rw [le_div_iff₀ hL_pos] at h1
    have hI_pos : 0 < (lobeSaddleIntegral amp.W_S amp.W_D c ξ σ_star).re := by linarith [h1, hL_pos]
    rw [d.h_saddle hc_min hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq]; exact hI_pos

/-- **Non-vacuity witness for `PreEdgeTangencyData`.** -/
theorem preEdgeTangencyData_nonvacuous : ∃ fhat : ℝ → ℝ → ℝ, Nonempty (PreEdgeTangencyData fhat) := by
  let Δ_cut := preEdgeDelta1 1 1 0 (1 / 2); let W_S : ℝ → ℂ → ℂ := fun _ _ => 0
  let W_D : ℝ → ℂ → ℂ := fun c w => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * (1 + w)⁻¹
  let fhat : ℝ → ℝ → ℝ := fun c Δ => if Δ < Δ_cut then c ^ (-(1 / 3 : ℝ)) * Real.exp (-4 * Δ)
    else if hξ : 0 < Δ / c ∧ π ^ 2 * (Δ / c) < 1 then
      (lobeSaddleIntegral (W_S c) (W_D c) c (Δ / c) (Classical.choose (exists_unique_saddleSigma hξ.1 hξ.2).exists)).re else 0
  have hinv_re : ∀ x : ℝ, (1 + (x : ℂ))⁻¹ = (((1 + x)⁻¹ : ℝ) : ℂ) := fun x => by push_cast; rfl
  refine ⟨fhat, ⟨{
    W_S, W_D, c_min := 4, M := 1, Λ := 1, Λ_add_max := 0, x₀ := 1, b := 1 / 2
    a_tan := 1, b_tan := 2, c_J := 1 / 3, C_S := 0, K_D := 1
    hc_min := by norm_num, hM := le_rfl, hΛ := le_rfl, hΛ_add := le_rfl, hx₀ := one_pos, hb := by norm_num
    ha_tan := one_pos, hab_tan := by norm_num, hc_J := by norm_num, hCS := le_rfl, hKD := zero_le_one
    hW_S_diff := fun _ => differentiableOn_const 0
    hW_D_diff := fun _ w hw => (differentiableAt_const _ |>.mul ((differentiableAt_id.const_add 1).inv fun h => by
      have := congrArg Complex.re h; simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this; linarith [show 0 < w.re from hw])).differentiableWithinAt
    hW_S_real := fun _ _ => rfl, hW_D_real := fun {c x} _ _ => by dsimp [W_D]; rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_im]
    hW_S_nonneg := fun _ _ _ => by simp [W_S]
    hW_D_nonneg := fun {c x} hc hx _ => by dsimp [W_D]; rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re]; exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (inv_nonneg.mpr (by linarith))
    hW0_pos := fun {c _ x_neg} hc _ _ hxneg _ _ => by dsimp [W_S, W_D]; rw [zero_add, hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re]; exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (inv_pos.mpr (by linarith))
    hD_floor := fun {c x} hc hx0 hx1 _ => by dsimp [W_D]; rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm (1 / 2 : ℝ), ← one_div]; exact mul_le_mul_of_nonneg_left ((le_div_iff₀ (by linarith : 0 < 1 + x)).mpr (by linarith)) (Real.rpow_nonneg (by linarith) _)
    hA1_S := fun _ _ _ _ => by simp [W_S]
    hA1_D := fun {c x y} hc hx _ _ _ => by
      have hε : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      have hne1 : 1 + ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
      have hne2 : 1 + (x : ℂ) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
      dsimp [W_D]; rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε,
        show (1 + ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹ - (1 + (x : ℂ))⁻¹ = -((y : ℂ) * Complex.I) / ((1 + ((x : ℂ) + (y : ℂ) * Complex.I)) * (1 + (x : ℂ))) by field_simp [hne1, hne2]; ring,
        norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
        show ‖1 + (x : ℂ)‖ = 1 + x by rw [show 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg (by linarith)],
        show (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * (1 + (x : ℂ))⁻¹).re = c ^ (-(1 / 3 : ℝ)) * (1 + x)⁻¹ by rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re]]
      have h_re : 1 + x ≤ ‖1 + ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by simpa using Complex.re_le_norm (1 + ((x : ℂ) + (y : ℂ) * Complex.I))
      calc c ^ (-(1 / 3 : ℝ)) * (|y| / (‖1 + ((x : ℂ) + (y : ℂ) * Complex.I)‖ * (1 + x))) ≤ c ^ (-(1 / 3 : ℝ)) * (|y| / (x * (1 + x))) := by gcongr; linarith
        _ = (|y| / x) * (c ^ (-(1 / 3 : ℝ)) * (1 + x)⁻¹) := by field_simp [hx.ne', (by linarith : 1 + x ≠ 0)]
        _ ≤ 4 * 1 * (|y| / x) * (c ^ (-(1 / 3 : ℝ)) * (1 + x)⁻¹) := by nlinarith [div_nonneg (abs_nonneg y) hx.le, mul_nonneg hε (inv_nonneg.mpr (by linarith : 0 ≤ 1 + x))]
    hA2_S := fun _ _ _ => by simp [W_S]
    hA2_D := fun {c x y} hc hx _ _ => by
      have hε : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      dsimp [W_D]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε, norm_inv,
        show (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * (1 + (x : ℂ))⁻¹).re = c ^ (-(1 / 3 : ℝ)) * (1 + x)⁻¹ by rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re], one_mul]
      exact (mul_le_mul_of_nonneg_left (inv_anti₀ (by linarith : 0 < 1 + x) (by simpa using Complex.re_le_norm (1 + ((x : ℂ) + (y : ℂ) * Complex.I)))) hε).trans (by split_ifs <;> simp)
    hD_tan_floor := fun {c x} hc hx _ => by
      dsimp [W_D]; rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm (1 / 3 : ℝ), ← one_div]
      exact mul_le_mul_of_nonneg_left ((le_div_iff₀ (by linarith [hx.1] : 0 < 1 + x)).mpr (by linarith [hx.2])) (Real.rpow_nonneg (by linarith) _)
    hW_S_bd := fun _ _ => by simp [W_S]
    hW_D_bd := fun {c w} hc hw => by
      dsimp [W_D]
      have hε : c ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      have hre : 1 ≤ ‖1 + w‖ := by
        calc (1 : ℝ) ≤ (1 + w).re := by simp [hw.le]
          _ ≤ ‖1 + w‖ := Complex.re_le_norm _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), norm_inv]
      exact (mul_le_mul hε (inv_le_one_of_one_le₀ hre) (inv_nonneg.mpr (norm_nonneg _)) zero_le_one).trans_eq (one_mul _)
    orig :=
      { c_min := 4, b_J := 1, C_ν := 0, C_err := 0, C_J := 0, C_B := 0, Δ_cap := Δ_cut
        hc_min := le_rfl, hb_J := one_pos, hC_ν := le_rfl, hC_err := le_rfl, hC_J := le_rfl, hC_B := le_rfl
        hΔ_cap := fun _ hΔ => ⟨hΔ.1, hΔ.2.le⟩, J₀ := fun c => c ^ (-(1 / 3 : ℝ)), g := fun _ _ => 0, R_c := fun _ _ => 0
        hJ₀ := fun _ => by rw [one_mul],
        hat0 := fun _ h0 => by dsimp [fhat, Δ_cut]; simp only [h0.2, ↓reduceIte, mul_zero, Real.exp_zero, mul_one]
        hg_meas := fun _ => aemeasurable_const, hg_nn := fun _ _ _ => le_rfl, hg_le := fun _ _ _ => by simp
        hR_meas := fun _ => aestronglyMeasurable_const, hR_lo := fun _ _ _ => by simp, hR_hi := fun _ _ => by simp
        h_mellin := fun {c Δ} _ hΔ _ => by dsimp [fhat, Δ_cut]; simp only [hΔ.2, ↓reduceIte]; simp [sub_self] }
    h_saddle := fun {c Δ ξ σ_star} hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq => by
      subst hξ
      have hc_pos : 0 < c := by linarith
      have hU1 : 1 ≤ preEdgeU 1 1 := one_le_preEdgeU 1 1
      have hξ_pos : 0 < Δ / c := div_pos ((one_le_preEdgeDelta1 1 1 0 (1 / 2)).trans hΔ_lo |>.trans_lt' zero_lt_one) hc_pos
      have hpiξ : π ^ 2 * (Δ / c) < 1 :=
        (calc π ^ 2 * (Δ / c) ≤ π ^ 2 * ((c / π ^ 2) * Real.exp (-(π ^ 2 * preEdgeU 1 1 * c ^ (-(2 / 3 : ℝ)))) / c) := by gcongr
          _ = Real.exp (-(π ^ 2 * preEdgeU 1 1 * c ^ (-(2 / 3 : ℝ)))) := by field_simp [Real.pi_ne_zero, hc_pos.ne']).trans_lt
          (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos (mul_pos (sq_pos_of_pos Real.pi_pos) (by linarith [hU1])) (Real.rpow_pos_of_pos hc_pos _))))
      have hσ_uniq := (exists_unique_saddleSigma hξ_pos hpiξ).unique ⟨⟨hσ0, hσ1⟩, hσ_eq⟩
        (Classical.choose_spec (exists_unique_saddleSigma hξ_pos hpiξ).exists)
      dsimp [fhat, Δ_cut]; simp only [not_lt.mpr hΔ_lo, ↓reduceIte, hξ_pos, hpiξ, and_self, ↓reduceDIte, hσ_uniq] }⟩⟩

/-- info: 'FormalResearch.CohnElkies.cepe_abs_saddle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cepe_abs_saddle

/-- info: 'FormalResearch.CohnElkies.preEdge_tangency_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.preEdge_tangency_pos

/-- info: 'FormalResearch.CohnElkies.preEdgeTangencyData_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.preEdgeTangencyData_nonvacuous

end FormalResearch.CohnElkies
