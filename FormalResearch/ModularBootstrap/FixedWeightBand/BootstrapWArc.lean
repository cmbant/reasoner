module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWLine
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.ArcBounds

/-!
# Good-Circle Airy Quadrature at Every Fixed `(w, Q)` (`hP_le`, `hArc_cov`, `hArc_unc`)

Source: `CFT/common/two_edge_bootstrap.tex` (`teb:bootstrap`, hypotheses `hP_le`, `hArc_cov`, `hArc_unc`) and
`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Step 3.

For the shifted test `f_{k,ℓ}(u) = Ψ̃(u + ℓ)(1 + u/R)^{k+1}` on a good circle `|u| = R`
(`CftCircleData` for the Airy zeros), the finite node sum is bounded by the real-line integral plus a covered
arc `Arc_cov` (from `YVEnvBound`, i.e. the band-feedback hypothesis) and an uncovered wedge
`Arc_unc ≤ C_unc c'^{-3/8}` (from the type-(II) envelope of `Lemma Q (2)`):

* `pNodesW`: the finite good-circle node sum;
* `quad_cov_ptW`, `quad_unc_ptW`: pointwise bounds on the covered arc and on the uncovered wedge;
* `quad_arc_boundW`: `P_nodes ≤ I_line + Arc_cov + Arc_unc` (the Virasoro `virasoro_quad_arc_bound`); the
  weight-free covered-arc Gamma bound `virasoroArcCov_le` is reused.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip

variable {prob : FixedWeightProblem} [Q : LemmaQData prob]

/-- Finite good-circle node sum `P_nodes` for `shiftedFunW`. -/
noncomputable def pNodesW (prob : FixedWeightProblem) (c' R ℓ : ℝ) (g : ℝ → ℝ) (k N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (shiftedFunW prob c' R ℓ g k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2

private lemma circleMap_mem_slitPlane {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo (-π) π) :
    circleMap 0 R θ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hθ0 : θ = 0
  · left; subst hθ0; simpa [circleMap] using hR
  · right
    rw [show (circleMap 0 R θ).im = R * Real.sin θ by
      rw [circleMap, zero_add, Complex.exp_mul_I]
      simp [Complex.add_im, Complex.mul_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re] ]
    have hsin_ne : Real.sin θ ≠ 0 := by
      rcases lt_or_gt_of_ne hθ0 with hlt | hlt
      · rw [← neg_ne_zero, ← Real.sin_neg]
        exact (Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hlt) (by linarith [hθ.1])).ne'
      · exact (Real.sin_pos_of_pos_of_lt_pi hlt hθ.2).ne'
    exact mul_ne_zero hR.ne' hsin_ne

private lemma quad_cov_ptW {c' R T L' ℓ θ : ℝ}
    (hc' : Q.cQ ≤ c') (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hL'_nn : 0 ≤ L') (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (hYV : YVEnvBound (psiTilde prob c' g) c' R L')
    {k : ℕ} (hk5 : 5 ≤ k)
    (hθ : θ ∈ Icc (-π) π) (h_abs_lt : |θ| < π)
    (hcov : |θ| ≤ π - 3 * π * c' ^ (-(1 / 12 : ℝ))) :
    ‖shiftedFunW prob c' R ℓ g k (circleMap 0 R θ)‖ ≤
      (2 ^ (3 / 4 : ℝ) * L' * (√R) ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) *
        ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) *
        Real.exp (-(4 * ℓ * √R / π) * ((π - |θ|) / 2))) *
      airyEnv (circleMap 0 R θ) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hR_pos : 0 < R := by linarith
  set a : ℝ := √R
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  have ha_sq : a ^ 2 = R := Real.sq_sqrt hR_pos.le
  have hθ_Ioo : θ ∈ Ioo (-π) π := abs_lt.mp h_abs_lt
  have hnorm_w : ‖circleMap 0 R θ‖ = R := by simp [norm_circleMap_zero, abs_of_pos hR_pos]
  have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
    norm_one_add_circleMap_div hR_pos hθ
  have hcos_nn : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hw_slit : circleMap 0 R θ ∈ Complex.slitPlane :=
    circleMap_mem_slitPlane hR_pos hθ_Ioo
  have h_re_w : (circleMap 0 R θ ^ (1 / 2 : ℂ)).re = a * Real.cos (θ / 2) :=
    re_cpow_half_circleMap hR_pos hθ_Ioo
  have h_env_shift : airyEnv (circleMap 0 R θ + (ℓ : ℂ)) ≤
      airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) :=
    (airyEnv_add_real_le hw_slit hℓ_nn).trans_eq (by rw [h_re_w])
  have h_u_norm_lo_sub : R - ℓ ≤ ‖circleMap 0 R θ + (ℓ : ℂ)‖ := by
    have hsub := norm_sub_le (circleMap 0 R θ + (ℓ : ℂ)) (ℓ : ℂ)
    rw [add_sub_cancel_right, hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn] at hsub
    linarith
  have h_u_norm_lo : R / 2 ≤ ‖circleMap 0 R θ + (ℓ : ℂ)‖ := by linarith
  have h_u_norm_hi : ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ R + 1 := by
    calc ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ ‖circleMap 0 R θ‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
      _ ≤ R + ℓ := by rw [hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn]
      _ ≤ R + 1 := by linarith
  have h_u_mem_dom : circleMap 0 R θ + (ℓ : ℂ) ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2) := by
    rw [mem_closedBall_zero_iff]; exact h_u_norm_hi.trans hR_ub
  have h_cos_bounds : (π - |θ|) / π ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ (π - |θ|) / 2 := by
    have hcos_eq : Real.cos (θ / 2) = Real.sin ((π - |θ|) / 2) := by
      rw [← Real.cos_abs (θ / 2), abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
        ← Real.sin_pi_div_two_sub]
      congr 1; ring
    rw [hcos_eq]
    have hx0 : 0 ≤ (π - |θ|) / 2 := by linarith [h_abs_lt]
    have hxpi2 : (π - |θ|) / 2 ≤ π / 2 := by linarith [abs_nonneg θ]
    refine ⟨?_, Real.sin_le hx0⟩
    calc (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
      _ ≤ Real.sin ((π - |θ|) / 2) := Real.mul_le_sin hx0 hxpi2
  have hcos_lb : 3 * c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos (θ / 2) := by
    have hpi_ge : (3 * π * c' ^ (-(1 / 12 : ℝ))) / π ≤ (π - |θ|) / π :=
      div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
    have hdp : (3 * π * c' ^ (-(1 / 12 : ℝ))) / π = 3 * c' ^ (-(1 / 12 : ℝ)) := by
      field_simp [Real.pi_pos.ne']
    linarith [h_cos_bounds.1]
  let θ' : ℝ := |θ|
  let w₁ : ℂ := circleMap 0 R θ'
  let u₁ : ℂ := w₁ + (ℓ : ℂ)
  have hθ'_nn : 0 ≤ θ' := abs_nonneg θ
  have hθ'_Ioo : θ' ∈ Ioo (-π) π := ⟨by linarith [Real.pi_pos], h_abs_lt⟩
  have hw1_slit : w₁ ∈ Complex.slitPlane :=
    circleMap_mem_slitPlane hR_pos hθ'_Ioo
  have hu1_im : 0 ≤ u₁.im := by
    dsimp [u₁, w₁]
    rw [circleMap, zero_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add]
    exact mul_nonneg hR_pos.le (Real.sin_nonneg_of_mem_Icc ⟨hθ'_nn, h_abs_lt.le⟩)
  have hu1_conj : u₁ = (circleMap 0 R θ + (ℓ : ℂ)) ∨
      u₁ = star (circleMap 0 R θ + (ℓ : ℂ)) := by
    rcases le_total 0 θ with h0 | h0
    · left; dsimp [u₁, w₁, θ']; rw [abs_of_nonneg h0]
    · right
      dsimp [u₁, w₁, θ']
      rw [abs_of_nonpos h0]
      have hw_conj : (circleMap 0 R (-θ) : ℂ) = star (circleMap 0 R θ) := by
        calc (circleMap 0 R (-θ) : ℂ)
            = (R : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * I) := by simp [circleMap]
          _ = (starRingEnd ℂ) ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
              rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
                Complex.conj_I]
              congr 2; push_cast; ring
          _ = star (circleMap 0 R θ) := by simp [circleMap]
      calc (circleMap 0 R (-θ) : ℂ) + (ℓ : ℂ)
          = star (circleMap 0 R θ) + star (ℓ : ℂ) := by rw [hw_conj, Complex.star_def, Complex.conj_ofReal]
        _ = star (circleMap 0 R θ + (ℓ : ℂ)) := (star_add _ _).symm
  have hΨ_norm_eq : ‖psiTilde prob c' g (circleMap 0 R θ + (ℓ : ℂ))‖ =
      ‖psiTilde prob c' g u₁‖ := by
    rcases hu1_conj with h_eq | h_eq
    · rw [h_eq]
    · rw [h_eq, Q.psiTilde_conj hc' hg.1 hM_pos h_u_mem_dom, norm_star]
  have hnorm_u1 : ‖u₁‖ = ‖circleMap 0 R θ + (ℓ : ℂ)‖ := by
    rcases hu1_conj with h_eq | h_eq
    · rw [h_eq]
    · rw [h_eq, norm_star]
  have hu1_re_w : (w₁ ^ (1 / 2 : ℂ)).re = a * Real.cos (θ / 2) := by
    have h1 := re_cpow_half_circleMap hR_pos hθ'_Ioo
    dsimp [θ'] at h1
    rwa [show |θ| / 2 = |θ / 2| by rw [abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2)],
      Real.cos_abs] at h1
  have hu1_re_lb : a * Real.cos (θ / 2) ≤ (u₁ ^ (1 / 2 : ℂ)).re := by
    rw [← hu1_re_w]
    exact (re_cpow_half_add_real_bounds hw1_slit hℓ_nn).1
  have hu1_sin : 2 * c' ^ (-(1 / 12 : ℝ)) * √‖u₁‖ ≤ (u₁ ^ (1 / 2 : ℂ)).re := by
    have h_sqrt_le : √‖u₁‖ ≤ (3 / 2 : ℝ) * a := by
      rw [hnorm_u1]
      have h1 : ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ (9 / 4 : ℝ) * R := by linarith
      calc √‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ √((9 / 4 : ℝ) * R) := Real.sqrt_le_sqrt h1
        _ = √((3 / 2 : ℝ) ^ 2 * R) := by norm_num
        _ = (3 / 2 : ℝ) * a := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hc12_nn : 0 ≤ c' ^ (-(1 / 12 : ℝ)) := Real.rpow_nonneg hc'_pos.le _
    calc 2 * c' ^ (-(1 / 12 : ℝ)) * √‖u₁‖
        ≤ 2 * c' ^ (-(1 / 12 : ℝ)) * ((3 / 2 : ℝ) * a) := by gcongr
      _ = a * (3 * c' ^ (-(1 / 12 : ℝ))) := by ring
      _ ≤ a * Real.cos (θ / 2) := mul_le_mul_of_nonneg_left hcos_lb ha_pos.le
      _ ≤ (u₁ ^ (1 / 2 : ℂ)).re := hu1_re_lb
  have hYV_u1 := hYV u₁ hu1_im (by rw [hnorm_u1]; linarith [h_u_norm_lo_sub])
    (by rw [hnorm_u1]; exact h_u_norm_hi) hu1_sin
  have he_u1 : airyEnv u₁ = airyEnv (circleMap 0 R θ + (ℓ : ℂ)) := by
    rcases hu1_conj with h_eq | h_eq
    · rw [h_eq]
    · rw [h_eq]
      unfold airyEnv
      have hstar_slit : circleMap 0 R θ + (ℓ : ℂ) ∈ Complex.slitPlane :=
        not_nonpos_add_ofReal hw_slit hℓ_nn
      have harg_ne : (circleMap 0 R θ + (ℓ : ℂ)).arg ≠ π :=
        (Complex.mem_slitPlane_iff_arg.mp hstar_slit).1
      have hcp0 := Complex.cpow_conj (circleMap 0 R θ + (ℓ : ℂ)) (3 / 2 : ℂ) harg_ne
      have h32_star : (starRingEnd ℂ) (3 / 2 : ℂ) = (3 / 2 : ℂ) := by
        rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
      rw [h32_star] at hcp0
      have h1 := congrArg (starRingEnd ℂ) hcp0
      rw [Complex.conj_conj] at h1
      rw [Complex.star_def, ← h1, Complex.conj_re]
  have h_re_neg_pow : ((u₁ ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) ≤
      (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) := by
    have hcos_pos : 0 < a * Real.cos (θ / 2) := by
      have : 0 < 3 * c' ^ (-(1 / 12 : ℝ)) := by positivity
      exact mul_pos ha_pos (this.trans_le hcos_lb)
    exact Real.rpow_le_rpow_of_nonpos hcos_pos hu1_re_lb (by norm_num)
  have h_norm_neg_pow : ‖u₁‖ ^ (-(3 / 4 : ℝ)) ≤ (R / 2) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [hnorm_u1]; exact h_u_norm_lo) (by norm_num)
  have h_r2_pow : (R / 2) ^ (-(3 / 4 : ℝ)) = (2 : ℝ) ^ (3 / 4 : ℝ) * a ^ (-(3 / 2 : ℝ)) := by
    rw [← ha_sq, div_eq_mul_inv, Real.mul_rpow (sq_nonneg a) (by norm_num),
      ← Real.rpow_natCast a 2, ← Real.rpow_mul ha_pos.le, Real.inv_rpow (by positivity),
      Real.rpow_neg (by positivity), inv_inv]
    norm_num; ring
  have hcos_pos : 0 < Real.cos (θ / 2) := by
    have : 0 < 3 * c' ^ (-(1 / 12 : ℝ)) := by positivity
    exact this.trans_le hcos_lb
  have h_ac_pow : (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) =
      a ^ (-(3 / 2 : ℝ)) * (Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) :=
    Real.mul_rpow ha_pos.le hcos_nn
  have h_a_comb : a ^ (-(3 / 2 : ℝ)) * a ^ (-(3 / 2 : ℝ)) = a ^ (-(3 : ℤ)) := by
    rw [← Real.rpow_add ha_pos, show -(3 / 2 : ℝ) + -(3 / 2 : ℝ) = ((-(3 : ℤ) : ℤ) : ℝ) by norm_num,
      Real.rpow_intCast]
  have h_cos_comb : (Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) * (Real.cos (θ / 2)) ^ (k + 1) =
      (Real.cos (θ / 2)) ^ ((k : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast (Real.cos (θ / 2)) (k + 1), ← Real.rpow_add hcos_pos]
    congr 1; push_cast; ring
  have hk_half_nn : 0 ≤ (k : ℝ) - 1 / 2 := by
    have : (5 : ℝ) ≤ k := by exact_mod_cast hk5
    linarith
  have h_cos_le_t : (Real.cos (θ / 2)) ^ ((k : ℝ) - 1 / 2) ≤ ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) :=
    Real.rpow_le_rpow hcos_nn h_cos_bounds.2 hk_half_nn
  have h_exp_le_t : Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) ≤
      Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2)) := by
    apply Real.exp_le_exp.mpr
    have h1 : (π - |θ|) / π ≤ Real.cos (θ / 2) := h_cos_bounds.1
    have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * ℓ * a)
    nlinarith only [hmul, show (4 * ℓ * a / π) * ((π - |θ|) / 2) = 2 * ℓ * a * ((π - |θ|) / π) by
      field_simp [Real.pi_pos.ne']; ring]
  dsimp [shiftedFunW]
  rw [norm_mul, norm_pow, h1w, hΨ_norm_eq, mul_pow]
  have h_u1_exp : L' * airyEnv u₁ * ((u₁ ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u₁‖ ^ (-(3 / 4 : ℝ)) ≤
      L' * (airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2)))) *
        (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) * ((2 : ℝ) ^ (3 / 4 : ℝ) * a ^ (-(3 / 2 : ℝ))) := by
    have h_u1_pos : 0 < ‖u₁‖ := by rw [hnorm_u1]; linarith
    have hnn1 : 0 ≤ ((u₁ ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_nonneg (lt_of_lt_of_le (mul_pos (mul_pos two_pos (Real.rpow_pos_of_pos hc'_pos _))
        (Real.sqrt_pos.mpr h_u1_pos)) hu1_sin).le _
    have hnn2 : 0 ≤ (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_nonneg (mul_nonneg ha_pos.le hcos_nn) _
    have hnn3 : 0 ≤ ‖u₁‖ ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hnn4 : 0 ≤ (2 : ℝ) ^ (3 / 4 : ℝ) * a ^ (-(3 / 2 : ℝ)) := by positivity
    rw [he_u1]
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h_env_shift hL'_nn) h_re_neg_pow
      hnn1 (by have := airyEnv_pos (circleMap 0 R θ); positivity)) (h_norm_neg_pow.trans_eq h_r2_pow)
      hnn3 (mul_nonneg (by have := airyEnv_pos (circleMap 0 R θ); positivity) hnn2)
  calc ‖psiTilde prob c' g u₁‖ * ((2 : ℝ) ^ (k + 1) * Real.cos (θ / 2) ^ (k + 1))
      ≤ (L' * airyEnv u₁ * ((u₁ ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u₁‖ ^ (-(3 / 4 : ℝ))) *
          ((2 : ℝ) ^ (k + 1) * Real.cos (θ / 2) ^ (k + 1)) := by
        gcongr
    _ ≤ (L' * (airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2)))) *
          (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) * ((2 : ℝ) ^ (3 / 4 : ℝ) * a ^ (-(3 / 2 : ℝ)))) *
          ((2 : ℝ) ^ (k + 1) * Real.cos (θ / 2) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right h_u1_exp (by positivity)
    _ = ((2 ^ (3 / 4 : ℝ) * L' * (a ^ (-(3 / 2 : ℝ)) * a ^ (-(3 / 2 : ℝ))) * (2 : ℝ) ^ (k + 1)) *
          ((Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) * Real.cos (θ / 2) ^ (k + 1)) *
          Real.exp (-2 * ℓ * (a * Real.cos (θ / 2)))) * airyEnv (circleMap 0 R θ) := by
        rw [h_ac_pow]; ring
    _ = ((2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)) *
          (Real.cos (θ / 2)) ^ ((k : ℝ) - 1 / 2)) *
          Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) * airyEnv (circleMap 0 R θ) := by
        rw [h_a_comb, h_cos_comb]
    _ ≤ ((2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)) *
          ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2)) *
          Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2)) * airyEnv (circleMap 0 R θ) := by
        have h_mc_nn : 0 ≤ 2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) := by positivity
        have h_pow_nn : 0 ≤ ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) :=
          Real.rpow_nonneg (by linarith [h_abs_lt] : 0 ≤ (π - |θ|) / 2) _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left h_cos_le_t h_mc_nn) h_exp_le_t
            (Real.exp_pos _).le (mul_nonneg h_mc_nn h_pow_nn))
          (airyEnv_pos _).le
    _ = (2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) *
          ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) *
          Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2))) * airyEnv (circleMap 0 R θ) := by ring

private lemma quad_unc_ptW {c' R T ℓ θ : ℝ}
    (hc' : Q.cQ ≤ c')
    (hς_arc : Q.sigma c' * (3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1) ≤ 1)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (k : ℕ) (hθ : θ ∈ Icc (-π) π) (h_abs_lt : |θ| < π)
    (hunc : π - 3 * π * c' ^ (-(1 / 12 : ℝ)) < |θ|) :
    ‖shiftedFunW prob c' R ℓ g k (circleMap 0 R θ)‖ ≤
      ((2 * √2 * Q.C0 * Real.exp 1) * (√R) ^ (-(2 : ℤ)) *
        (3 * π * c' ^ (-(1 / 12 : ℝ))) ^ k) * airyEnv (circleMap 0 R θ) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hR_pos : 0 < R := by linarith
  set a : ℝ := √R
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  have ha_sq : a ^ 2 = R := Real.sq_sqrt hR_pos.le
  set δ₀ : ℝ := 3 * π * c' ^ (-(1 / 12 : ℝ))
  have hθ_Ioo : θ ∈ Ioo (-π) π := abs_lt.mp h_abs_lt
  have hnorm_w : ‖circleMap 0 R θ‖ = R := by simp [norm_circleMap_zero, abs_of_pos hR_pos]
  have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
    norm_one_add_circleMap_div hR_pos hθ
  have hcos_nn : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hw_slit : circleMap 0 R θ ∈ Complex.slitPlane :=
    circleMap_mem_slitPlane hR_pos hθ_Ioo
  have h_re_w : (circleMap 0 R θ ^ (1 / 2 : ℂ)).re = a * Real.cos (θ / 2) :=
    re_cpow_half_circleMap hR_pos hθ_Ioo
  have h_env_shift : airyEnv (circleMap 0 R θ + (ℓ : ℂ)) ≤
      airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) :=
    (airyEnv_add_real_le hw_slit hℓ_nn).trans_eq (by rw [h_re_w])
  have h_re_shift := re_cpow_half_add_real_bounds hw_slit hℓ_nn
  rw [h_re_w] at h_re_shift
  have h_u_norm_lo : R / 2 ≤ ‖circleMap 0 R θ + (ℓ : ℂ)‖ := by
    have hsub := norm_sub_le (circleMap 0 R θ + (ℓ : ℂ)) (ℓ : ℂ)
    rw [add_sub_cancel_right, hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn] at hsub
    linarith
  have h_u_norm_hi : ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ R + 1 := by
    calc ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ ‖circleMap 0 R θ‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
      _ ≤ R + ℓ := by rw [hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn]
      _ ≤ R + 1 := by linarith
  have h_u_mem_dom : circleMap 0 R θ + (ℓ : ℂ) ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2) := by
    rw [mem_closedBall_zero_iff]; exact h_u_norm_hi.trans hR_ub
  have h_cos_bounds : (π - |θ|) / π ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ (π - |θ|) / 2 := by
    have hcos_eq : Real.cos (θ / 2) = Real.sin ((π - |θ|) / 2) := by
      rw [← Real.cos_abs (θ / 2), abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
        ← Real.sin_pi_div_two_sub]
      congr 1; ring
    rw [hcos_eq]
    have hx0 : 0 ≤ (π - |θ|) / 2 := by linarith [h_abs_lt]
    have hxpi2 : (π - |θ|) / 2 ≤ π / 2 := by linarith [abs_nonneg θ]
    refine ⟨?_, Real.sin_le hx0⟩
    calc (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
      _ ≤ Real.sin ((π - |θ|) / 2) := Real.mul_le_sin hx0 hxpi2
  have hcos_ub : Real.cos (θ / 2) ≤ δ₀ / 2 := by
    have : (π - |θ|) / 2 ≤ δ₀ / 2 := by dsimp [δ₀]; linarith
    exact h_cos_bounds.2.trans this
  have hcos_pos : 0 < Real.cos (θ / 2) := by
    have : 0 < (π - |θ|) / π := div_pos (by linarith [h_abs_lt]) Real.pi_pos
    exact this.trans_le h_cos_bounds.1
  have h_u_slit : circleMap 0 R θ + (ℓ : ℂ) ∈ Complex.slitPlane :=
    not_nonpos_add_ofReal hw_slit hℓ_nn
  have h_u_cut : ¬ ((circleMap 0 R θ + (ℓ : ℂ)).im = 0 ∧ (circleMap 0 R θ + (ℓ : ℂ)).re ≤ 0) := by
    rw [Complex.mem_slitPlane_iff] at h_u_slit
    intro ⟨him, hre⟩
    rcases h_u_slit with h | h
    · linarith
    · exact absurd him h
  have h_Q2 := (Q.part2 hc' hg.1 hM_pos).2.2 _ h_u_mem_dom h_u_cut
  have h_exp_ς : Q.sigma c' * ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ≤ 1 := by
    have hre_le : ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ≤
        3 * π * a * c' ^ (-(1 / 12 : ℝ)) + 1 := by
      have h1 := h_re_shift.2
      have hℓ1 : √ℓ ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
      have ha_cos : a * Real.cos (θ / 2) ≤ a * (δ₀ / 2) :=
        mul_le_mul_of_nonneg_left hcos_ub ha_pos.le
      have ha_δ : a * (δ₀ / 2) = (3 * π / 2) * a * c' ^ (-(1 / 12 : ℝ)) := by
        dsimp [δ₀]; ring
      have hc_nn : 0 ≤ (3 * π / 2) * a * c' ^ (-(1 / 12 : ℝ)) := by positivity
      linarith
    have hς_nn : 0 ≤ Q.sigma c' := Q.sigma_nonneg (by have := Q.hcQ_10000; linarith)
    calc Q.sigma c' * ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re
        ≤ Q.sigma c' * (3 * π * a * c' ^ (-(1 / 12 : ℝ)) + 1) :=
          mul_le_mul_of_nonneg_left hre_le hς_nn
      _ ≤ 1 := hς_arc
  have h_u_norm_neg_half : ‖circleMap 0 R θ + (ℓ : ℂ)‖ ^ (-(1 / 2 : ℝ)) ≤ √2 * a⁻¹ := by
    have h1 : (R / 2) ^ (-(1 / 2 : ℝ)) = √2 * a⁻¹ := by
      rw [← ha_sq, div_eq_mul_inv, Real.mul_rpow (sq_nonneg a) (by norm_num),
        ← Real.rpow_natCast a 2, ← Real.rpow_mul ha_pos.le,
        show ((2 : ℕ) : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one,
        Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv, ← Real.sqrt_eq_rpow]
      ring
    calc ‖circleMap 0 R θ + (ℓ : ℂ)‖ ^ (-(1 / 2 : ℝ))
        ≤ (R / 2) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h_u_norm_lo (by norm_num)
      _ = √2 * a⁻¹ := h1
  have h_u_re_inv : (((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re)⁻¹ ≤
      (a * Real.cos (θ / 2))⁻¹ :=
    inv_anti₀ (mul_pos ha_pos hcos_pos) h_re_shift.1
  have h_env_le : airyEnv (circleMap 0 R θ + (ℓ : ℂ)) ≤ airyEnv (circleMap 0 R θ) := by
    have h1 : Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 2 * ℓ * (a * Real.cos (θ / 2)) := mul_nonneg (mul_nonneg two_pos.le hℓ_nn) (mul_nonneg ha_pos.le hcos_nn)
      linarith
    calc airyEnv (circleMap 0 R θ + (ℓ : ℂ))
        ≤ airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) := h_env_shift
      _ ≤ airyEnv (circleMap 0 R θ) * 1 := mul_le_mul_of_nonneg_left h1 (airyEnv_pos _).le
      _ = airyEnv (circleMap 0 R θ) := mul_one _
  dsimp [shiftedFunW]
  rw [norm_mul, norm_pow, h1w]
  have h_pow_split : (2 * Real.cos (θ / 2)) ^ (k + 1) =
      2 * Real.cos (θ / 2) * (2 * Real.cos (θ / 2)) ^ k := by rw [pow_succ']
  have h_2cos_le : (2 * Real.cos (θ / 2)) ^ k ≤ δ₀ ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  have h_a_sq_inv : a⁻¹ * a⁻¹ = a ^ (-(2 : ℤ)) := by
    rw [zpow_neg, show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast]; ring
  have hδ₀_nn : 0 ≤ δ₀ := by dsimp [δ₀]; positivity
  have h_re_pos : 0 < ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re :=
    lt_of_lt_of_le (mul_pos ha_pos hcos_pos) h_re_shift.1
  have h_left_le : Q.C0 * airyEnv (circleMap 0 R θ + (ℓ : ℂ)) *
        Real.exp (Q.sigma c' * ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re) *
        ‖circleMap 0 R θ + (ℓ : ℂ)‖ ^ (-(1 / 2 : ℝ)) *
        (((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re)⁻¹ ≤
      Q.C0 * airyEnv (circleMap 0 R θ) * Real.exp 1 *
        (√2 * a⁻¹) * (a * Real.cos (θ / 2))⁻¹ := by
    have hC0 := Q.hC0
    have hnn_nh : 0 ≤ ‖circleMap 0 R θ + (ℓ : ℂ)‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hnn_e := (airyEnv_pos (circleMap 0 R θ)).le
    have hnn_re_inv : 0 ≤ (((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re)⁻¹ := inv_nonneg.mpr h_re_pos.le
    exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h_env_le hC0.le)
      (Real.exp_le_exp.mpr h_exp_ς) (Real.exp_pos _).le (mul_nonneg hC0.le hnn_e))
      h_u_norm_neg_half hnn_nh (by positivity)) h_u_re_inv hnn_re_inv (by positivity)
  calc ‖psiTilde prob c' g (circleMap 0 R θ + (ℓ : ℂ))‖ * (2 * Real.cos (θ / 2)) ^ (k + 1)
      ≤ (Q.C0 * airyEnv (circleMap 0 R θ + (ℓ : ℂ)) *
          Real.exp (Q.sigma c' * ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re) *
          ‖circleMap 0 R θ + (ℓ : ℂ)‖ ^ (-(1 / 2 : ℝ)) *
          (((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re)⁻¹) *
          (2 * Real.cos (θ / 2) * δ₀ ^ k) := by
        refine mul_le_mul h_Q2 ?_ (pow_nonneg (by linarith) _)
          (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg Q.hC0.le (airyEnv_pos _).le)
            (Real.exp_pos _).le) (Real.rpow_nonneg (norm_nonneg _) _)) (inv_nonneg.mpr h_re_pos.le))
        rw [h_pow_split]; exact mul_le_mul_of_nonneg_left h_2cos_le (by linarith)
    _ ≤ (Q.C0 * airyEnv (circleMap 0 R θ) * Real.exp 1 *
          (√2 * a⁻¹) * (a * Real.cos (θ / 2))⁻¹) *
          (2 * Real.cos (θ / 2) * δ₀ ^ k) :=
        mul_le_mul_of_nonneg_right h_left_le (by positivity)
    _ = ((2 * √2 * Q.C0 * Real.exp 1) * (a⁻¹ * a⁻¹) * δ₀ ^ k) * airyEnv (circleMap 0 R θ) := by
        field_simp [ha_pos.ne', hcos_pos.ne']
    _ = ((2 * √2 * Q.C0 * Real.exp 1) * a ^ (-(2 : ℤ)) * δ₀ ^ k) * airyEnv (circleMap 0 R θ) := by
        rw [h_a_sq_inv]

/-- **Quadrature + Arc Estimate (`BootstrapCore.hP_le`, `hArc_cov`, `hArc_unc`)** from `YVEnvBound`
and Lemma Q(2): on any good circle `R` with `CftCircleData` and ratio bounds,
`P_nodes ≤ I_line + Arc_cov + Arc_unc` with `Arc_unc ≤ Q.arcUncConst * c' ^ (-(3 / 8 : ℝ))`. -/
theorem quad_arc_boundW {c' R T L' ℓ : ℝ} {N : ℕ}
    (hc' : Q.cQ ≤ c')
    (h_c12 : (3 * π) ^ (12 : ℕ) ≤ c')
    (hς_arc : Q.sigma c' * (3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1) ≤ 1)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hL'_nn : 0 ≤ L') (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hYV : YVEnvBound (psiTilde prob c' g) c' R L')
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R)
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    {k : ℕ} (hk5 : 5 ≤ k) :
    pNodesW prob c' R ℓ g k N ≤
      (∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k (x : ℂ)).re) +
        virasoroArcCov c' R T L' ℓ g k + Q.arcUncConst * c' ^ (-(3 / 8 : ℝ)) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((Q.hcQ_10000.trans hc'))
  have ha : prob.totalShift ≤ c' / 12 := by
    have := Q.hcQ_shift; have := Q.hcQ_10000; linarith
  have hM_pos : 0 < prob.cardyNorm (c' / 12) g :=
    Q.cardyNorm_pos hc' hg
  have hR_pos : 0 < R := by linarith
  set a : ℝ := √R
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  have ha_sq : a ^ 2 = R := Real.sq_sqrt hR_pos.le
  set f := shiftedFunW prob c' R ℓ g k
  have hf_diff : DifferentiableOn ℂ f (ball (0 : ℂ) (R + 1 / 3)) := by
    intro u hu
    have hu_shift : u + (ℓ : ℂ) ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2) := by
      rw [mem_closedBall_zero_iff]
      rw [mem_ball_zero_iff] at hu
      calc ‖u + (ℓ : ℂ)‖ ≤ ‖u‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
        _ ≤ (R + 1 / 3) + ℓ := by
            rw [Complex.norm_real, Real.norm_of_nonneg hℓ_nn]; linarith
        _ ≤ R + 1 := by linarith
        _ ≤ Q.AC c' ^ 2 := hR_ub
    have hPsi_at : AnalyticAt ℂ (psiTilde prob c' g) (u + (ℓ : ℂ)) :=
      Q.analytic hc' hg.1 _ (Q.closedBall_subset_psiDom hc'_pos hu_shift)
    have h1 : DifferentiableAt ℂ (fun z : ℂ => psiTilde prob c' g (z + (ℓ : ℂ))) u :=
      (hPsi_at.differentiableAt).comp u ((differentiableAt_id).add (differentiableAt_const _))
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (1 + z / (R : ℂ)) ^ (k + 1)) u :=
      ((differentiableAt_const _).add (differentiableAt_id.div_const _)).pow _
    exact (h1.mul h2).differentiableWithinAt
  set δ₀ : ℝ := 3 * π * c' ^ (-(1 / 12 : ℝ))
  have hδ₀_pos : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀_le_1 : δ₀ ≤ 1 := by
    have h1 : (3 * π) ^ (12 : ℕ) ≤ c' := h_c12
    have h_rpow : 3 * π ≤ c' ^ (1 / 12 : ℝ) := by
      have h3pi_nn : 0 ≤ 3 * π := by positivity
      calc 3 * π = ((3 * π) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) := by
            rw [← Real.rpow_natCast (3 * π) 12, ← Real.rpow_mul h3pi_nn]; norm_num
        _ ≤ c' ^ (1 / 12 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    calc δ₀ = 3 * π * (c' ^ (1 / 12 : ℝ))⁻¹ := by dsimp [δ₀]; rw [Real.rpow_neg hc'_pos.le, mul_assoc]
      _ = 3 * π / c' ^ (1 / 12 : ℝ) := (div_eq_mul_inv _ _).symm
      _ ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hc'_pos _)).mpr h_rpow
  have hδ₀_le_pi2 : δ₀ ≤ π / 2 := hδ₀_le_1.trans (by linarith [Real.pi_gt_three])
  set M_c : ℝ := 2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)
  have hM_c_nn : 0 ≤ M_c := by dsimp [M_c]; positivity
  let B_cov : ℝ → ℝ := fun θ =>
    M_c * ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) * Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2))
  set M_unc : ℝ := (2 * √2 * Q.C0 * Real.exp 1) * a ^ (-(2 : ℤ)) * δ₀ ^ k
  have hM_unc_nn : 0 ≤ M_unc := by dsimp [M_unc]; have := Q.hC0; positivity
  let W_unc : Set ℝ := {θ : ℝ | π - δ₀ < |θ|}
  have hW_meas : MeasurableSet W_unc := measurableSet_lt measurable_const continuous_abs.measurable
  let B_unc : ℝ → ℝ := W_unc.indicator (fun _ => M_unc)
  let B : ℝ → ℝ := fun θ => B_cov θ + B_unc θ
  have hk_half_pos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by
    have : (5 : ℝ) ≤ k := by exact_mod_cast hk5
    linarith
  have hB_cov_cont : ContinuousOn B_cov (Icc (-π) π) := fun θ _ =>
    Continuous.continuousWithinAt <|
      (continuous_const.mul ((Continuous.rpow_const ((continuous_const.sub continuous_abs).div_const 2)
        (fun _ => Or.inr hk_half_pos.le)))).mul
      (Real.continuous_exp.comp (continuous_const.mul ((continuous_const.sub continuous_abs).div_const 2)))
  have hB_cov_int : IntervalIntegrable B_cov volume (-π) π :=
    hB_cov_cont.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])
  have hB_unc_int : IntervalIntegrable B_unc volume (-π) π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    exact ((continuousOn_const (c := M_unc)).integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator hW_meas
  have hB_int : IntervalIntegrable B volume (-π) π := hB_cov_int.add hB_unc_int
  have hB_bd : ∀ θ ∈ Icc (-π) π, ‖f (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤ B θ := by
    intro θ hθ
    have hB_cov_nn : 0 ≤ B_cov θ := by
      dsimp [B_cov]
      exact mul_nonneg (mul_nonneg hM_c_nn (Real.rpow_nonneg (by linarith [abs_le.mpr hθ]) _))
        (Real.exp_pos _).le
    have hB_unc_nn : 0 ≤ B_unc θ := by
      dsimp [B_unc]; by_cases h : θ ∈ W_unc <;> simp [h, hM_unc_nn]
    have he_pos : 0 < airyEnv (circleMap 0 R θ) := airyEnv_pos _
    rw [div_le_iff₀ he_pos]
    have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
      norm_one_add_circleMap_div hR_pos hθ
    by_cases hpi : |θ| = π
    · have hcos0 : Real.cos (θ / 2) = 0 := by
        rcases abs_eq Real.pi_pos.le |>.mp hpi with rfl | rfl
        · simp [Real.cos_pi_div_two]
        · simp [neg_div, Real.cos_neg, Real.cos_pi_div_two]
      have hpow0 : ‖(1 + circleMap 0 R θ / (R : ℂ)) ^ (k + 1)‖ = 0 := by
        rw [norm_pow, h1w, hcos0, mul_zero, zero_pow (Nat.succ_ne_zero k)]
      have hf0 : ‖f (circleMap 0 R θ)‖ = 0 := by
        dsimp [f, shiftedFunW]; rw [norm_mul, hpow0, mul_zero]
      rw [hf0]
      exact mul_nonneg (add_nonneg hB_cov_nn hB_unc_nn) he_pos.le
    · have h_abs_lt : |θ| < π := lt_of_le_of_ne (abs_le.mpr hθ) hpi
      by_cases hcov : |θ| ≤ π - δ₀
      · have h_pt := quad_cov_ptW hc' hR_10 hR_ub hL'_nn hℓ_nn hℓ_half hg hM_pos hYV hk5
          hθ h_abs_lt hcov
        have h1 : B_cov θ * airyEnv (circleMap 0 R θ) ≤ B θ * airyEnv (circleMap 0 R θ) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB_unc_nn) he_pos.le
        exact h_pt.trans h1
      · push Not at hcov
        have hB_unc_eq : B_unc θ = M_unc := Set.indicator_of_mem (show θ ∈ W_unc from hcov) _
        have h_pt := quad_unc_ptW hc' hς_arc hR_10 hR_ub hℓ_nn hℓ_half hg hM_pos k
          hθ h_abs_lt hcov
        have h1 : M_unc * airyEnv (circleMap 0 R θ) ≤ B θ * airyEnv (circleMap 0 R θ) := by
          rw [← hB_unc_eq]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB_cov_nn) he_pos.le
        exact h_pt.trans h1
  -- Apply `airy_defect_ball_split`
  have h_def := airy_defect_ball_split hD (by linarith : R < R + 1 / 3) hf_diff hRp hRm hB_int hB_bd
  have h_sum_eq : (∑ n ∈ Finset.Icc 1 N, (f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2)).re =
      pNodesW prob c' R ℓ g k N := by
    unfold pNodesW
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [deriv_airyAiC_ofReal, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  have h_int_eq : (∫ x in (-R)..R, f (x : ℂ)).re = ∫ x in (-R)..R, (f (x : ℂ)).re := by
    have hf_cont_R : ContinuousOn (fun x : ℝ => f (x : ℂ)) (Icc (-R) R) := by
      refine hf_diff.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr hx).trans_lt (by linarith)
    exact (Complex.reCLM.intervalIntegral_comp_comm (hf_cont_R.intervalIntegrable_of_Icc (by linarith))).symm
  have h_quad_re : pNodesW prob c' R ℓ g k N - (∫ x in (-R)..R, (f (x : ℂ)).re) ≤
      (15 * √π * R) * ∫ θ in (-π)..π, B θ := by
    have hre := (Complex.abs_re_le_norm _).trans h_def
    rw [Complex.sub_re, h_sum_eq, h_int_eq] at hre
    exact (abs_le.mp hre).2
  -- Bound `∫_{-π}^π B_unc θ dθ ≤ 4 * δ₀ * M_unc`
  have h_unc_int : (15 * √π * R) * ∫ θ in (-π)..π, B_unc θ ≤
      Q.arcUncConst * c' ^ (-(3 / 8 : ℝ)) := by
    have h_meas_le : ∫ θ in (-π)..π, B_unc θ ≤ 4 * δ₀ * M_unc := by
      let J₁ := Icc (-π) (-(π - δ₀))
      let J₂ := Icc (π - δ₀) π
      have h_sub_W : W_unc ∩ Ioc (-π) π ⊆ J₁ ∪ J₂ := by
        intro θ ⟨hW, hIoc⟩
        rcases le_total θ 0 with h0 | h0
        · left; refine ⟨hIoc.1.le, ?_⟩
          have : |θ| = -θ := abs_of_nonpos h0
          rw [Set.mem_ofPred_eq, this] at hW; linarith
        · right; refine ⟨?_, hIoc.2⟩
          have : |θ| = θ := abs_of_nonneg h0
          rw [Set.mem_ofPred_eq, this] at hW; linarith
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
      have h_ind_eq : ∫ θ in Ioc (-π) π, B_unc θ = M_unc * (volume (W_unc ∩ Ioc (-π) π)).toReal := by
        dsimp [B_unc]
        rw [setIntegral_indicator hW_meas, setIntegral_const, smul_eq_mul, Measure.real_def,
          Set.inter_comm]
        ring
      have h_vol : (volume (W_unc ∩ Ioc (-π) π)).toReal ≤ 4 * δ₀ := by
        have hm1 : volume (W_unc ∩ Ioc (-π) π) ≤ volume (J₁ ∪ J₂) := measure_mono h_sub_W
        have hm2 : volume (J₁ ∪ J₂) ≤ volume J₁ + volume J₂ := measure_union_le J₁ J₂
        have hJ1 : volume J₁ = ENNReal.ofReal δ₀ := by
          dsimp [J₁]; rw [Real.volume_Icc]; congr 1; ring
        have hJ2 : volume J₂ = ENNReal.ofReal δ₀ := by
          dsimp [J₂]; rw [Real.volume_Icc]; congr 1; ring
        have hlt : volume (W_unc ∩ Ioc (-π) π) ≤ ENNReal.ofReal (4 * δ₀) := by
          calc volume (W_unc ∩ Ioc (-π) π) ≤ ENNReal.ofReal δ₀ + ENNReal.ofReal δ₀ := by
                exact hm1.trans (hm2.trans_eq (by rw [hJ1, hJ2]))
            _ = ENNReal.ofReal (2 * δ₀) := by
                rw [← ENNReal.ofReal_add hδ₀_pos.le hδ₀_pos.le, two_mul]
            _ ≤ ENNReal.ofReal (4 * δ₀) := ENNReal.ofReal_le_ofReal (by linarith)
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlt
      rw [h_ind_eq]
      nlinarith
    have hR_a2 : R * a ^ (-(2 : ℤ)) = 1 := by
      rw [← ha_sq, zpow_neg, show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast]
      field_simp [ha_pos.ne']
    have hδ_pow : δ₀ ^ (k + 1) ≤ (3 * π) ^ (6 : ℕ) * c' ^ (-(3 / 8 : ℝ)) := by
      have hk6 : 6 ≤ k + 1 := by omega
      have h1 : δ₀ ^ (k + 1) ≤ δ₀ ^ 6 := pow_le_pow_of_le_one hδ₀_pos.le hδ₀_le_1 hk6
      have h2 : δ₀ ^ 6 = (3 * π) ^ (6 : ℕ) * c' ^ (-(1 / 2 : ℝ)) := by
        dsimp [δ₀]
        rw [mul_pow, ← Real.rpow_natCast (c' ^ (-(1 / 12 : ℝ))) 6, ← Real.rpow_mul hc'_pos.le]
        norm_num
      have h3 : c' ^ (-(1 / 2 : ℝ)) ≤ c' ^ (-(3 / 8 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by have := Q.hcQ_10000; linarith) (by norm_num)
      calc δ₀ ^ (k + 1) ≤ δ₀ ^ 6 := h1
        _ = (3 * π) ^ (6 : ℕ) * c' ^ (-(1 / 2 : ℝ)) := h2
        _ ≤ (3 * π) ^ (6 : ℕ) * c' ^ (-(3 / 8 : ℝ)) := by gcongr
    calc (15 * √π * R) * ∫ θ in (-π)..π, B_unc θ
        ≤ (15 * √π * R) * (4 * δ₀ * M_unc) := by gcongr
      _ = 15 * √π * 8 * √2 * Q.C0 * Real.exp 1 * (R * a ^ (-(2 : ℤ))) * δ₀ ^ (k + 1) := by
          dsimp [M_unc]; rw [pow_succ]; ring
      _ = 15 * √π * 8 * √2 * Q.C0 * Real.exp 1 * δ₀ ^ (k + 1) := by
          rw [hR_a2, mul_one]
      _ ≤ 15 * √π * 8 * √2 * Q.C0 * Real.exp 1 * ((3 * π) ^ (6 : ℕ) * c' ^ (-(3 / 8 : ℝ))) := by
          have := Q.hC0; gcongr
      _ = Q.arcUncConst * c' ^ (-(3 / 8 : ℝ)) := by
          unfold LemmaQData.arcUncConst; ring
  have hB_split : ∫ θ in (-π)..π, B θ =
      (∫ θ in (-π)..π, B_cov θ) + ∫ θ in (-π)..π, B_unc θ :=
    intervalIntegral.integral_add hB_cov_int hB_unc_int
  have h_cov_eq : (15 * √π * R) * ∫ θ in (-π)..π, B_cov θ = virasoroArcCov c' R T L' ℓ g k := by
    unfold virasoroArcCov; rfl
  rw [hB_split, mul_add] at h_quad_re
  dsimp only [f] at h_quad_re
  linarith only [h_quad_re, h_cov_eq, h_unc_int]

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.quad_arc_boundW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quad_arc_boundW

end FormalResearch.ModularBootstrap.FixedWeightBand
