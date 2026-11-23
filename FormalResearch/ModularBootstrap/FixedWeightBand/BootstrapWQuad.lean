module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWSchwarz

/-!
# Shifted-Weight Quadrature Inputs at Every Fixed `(w, Q)`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Steps 1-3, and
`CFT/common/two_edge_bootstrap.tex` (`teb:bootstrap`).

* `pos_real_norm_tail_leW`: exponential tail bound for `‖psiTilde‖` on `[A, B] ⊆ [1, A_{c'}²]`;
* `LemmaQData.psiTilde_moment_integral_eq`: moment identity in `u`-coordinates;
* `shiftedFunW`, `bandB1kW`, `bandB1kW_nonneg`, `bandB1W_le_B1k`: the shifted quadrature test
  `f_{k,ℓ}(u) = Ψ̃(u + ℓ)(1 + u/R)^{k+1}` and the truncated first band moments.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing PoissonJensen TipFront ConcreteBootstrap FixedWeightTip FormalResearch.Special

variable {prob : FixedWeightProblem}

section Tail

variable [Q : LemmaQData prob]

/-- Exponential tail bound for `psiTilde prob` on `[A, B] ⊆ [1, A_{c'}^2]` (`ς ≤ 1/2`). -/
lemma pos_real_norm_tail_leW {c' A B : ℝ}
    (hc' : Q.cQ ≤ c') (hς_nn : 0 ≤ Q.sigma c') (hς_half : Q.sigma c' ≤ 1 / 2)
    (hA1 : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g) :
    ∫ x in A..B, ‖psiTilde prob c' g (x : ℂ)‖ ≤
      (6 / 5 : ℝ) * Q.C0 * Real.exp (-(5 / 6 : ℝ) * A) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((Q.hcQ_10000.trans hc'))
  have hΨ_cont : ContinuousOn (fun x : ℝ => psiTilde prob c' g (x : ℂ)) (Icc A B) := by
    refine (Q.analytic hc' hg).continuousOn.comp
      continuous_ofReal.continuousOn fun x hx => ?_
    exact Q.closedBall_subset_psiDom hc'_pos
      (by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hx.1])]; exact hx.2.trans hB)
  have hi_l : IntervalIntegrable (fun x : ℝ => ‖psiTilde prob c' g (x : ℂ)‖) volume A B :=
    (continuous_norm.comp_continuousOn hΨ_cont).intervalIntegrable_of_Icc hAB
  have hi_r : IntervalIntegrable (fun x : ℝ => Q.C0 * Real.exp (-(5 / 6 : ℝ) * x)) volume A B :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable A B
  have h_pt : ∀ x ∈ Icc A B,
      ‖psiTilde prob c' g (x : ℂ)‖ ≤ Q.C0 * Real.exp (-(5 / 6 : ℝ) * x) := by
    intro x hx
    have hx1 : 1 ≤ x := hA1.trans hx.1
    have hx_pos : 0 < x := by linarith
    have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
      exact hx.2.trans hB
    have hcut : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := fun h0 => by
      simp only [Complex.ofReal_re] at h0; linarith
    have h_env := (Q.part2 hc' hg hM_pos).2.2 (x : ℂ) hx_ball hcut
    have h_re_sqrt : ((x : ℂ) ^ (1 / 2 : ℂ)).re = √x := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx_pos.le,
        Complex.ofReal_re, Real.sqrt_eq_rpow]
    have h_env_val : airyEnv (x : ℂ) = Real.exp (-(4 / 3 : ℝ) * (x ^ (3 / 2 : ℝ))) := by
      unfold airyEnv
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx_pos.le,
        Complex.ofReal_re]
    have hx32 : x ≤ x ^ (3 / 2 : ℝ) := by
      conv_lhs => rw [← Real.rpow_one x]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hsqrt_le : √x ≤ x := by
      rw [Real.sqrt_eq_rpow]
      conv_rhs => rw [← Real.rpow_one x]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h_exp : -(4 / 3 : ℝ) * (x ^ (3 / 2 : ℝ)) + Q.sigma c' * √x ≤ -(5 / 6 : ℝ) * x := by
      nlinarith
    have h_inv_le1 : ‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos, h_re_sqrt,
        Real.rpow_neg hx_pos.le, ← Real.sqrt_eq_rpow, ← mul_inv, Real.mul_self_sqrt hx_pos.le]
      exact inv_le_one_of_one_le₀ hx1
    calc ‖psiTilde prob c' g (x : ℂ)‖
        ≤ Q.C0 * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
            Real.exp (Q.sigma c' * √x) * (‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹) := by
          simpa only [h_re_sqrt, h_env_val, mul_assoc] using h_env
      _ ≤ Q.C0 * (Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
            Real.exp (Q.sigma c' * √x)) * 1 := by
          have hnn : 0 ≤ Q.C0 * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
              Real.exp (Q.sigma c' * √x) := by
            have := Q.hC0; positivity
          exact (mul_le_mul_of_nonneg_left h_inv_le1 hnn).trans_eq (by ring)
      _ = Q.C0 * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) + Q.sigma c' * √x) := by
          rw [mul_one, ← Real.exp_add]
      _ ≤ Q.C0 * Real.exp (-(5 / 6 : ℝ) * x) := by
          gcongr; exact Q.hC0.le
  have hmono := intervalIntegral.integral_mono_on hAB hi_l hi_r h_pt
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => -((6 / 5 : ℝ) * Q.C0) * Real.exp (-(5 / 6 : ℝ) * t))
        (Q.C0 * Real.exp (-(5 / 6 : ℝ) * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -(5 / 6 : ℝ) * t) (-(5 / 6 : ℝ)) x := by
      simpa using (hasDerivAt_id x).const_mul (-(5 / 6 : ℝ))
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(5 / 6 : ℝ) * t))
        (Real.exp (-(5 / 6 : ℝ) * x) * (-(5 / 6 : ℝ))) x :=
      (Real.hasDerivAt_exp _).comp x h1
    exact (h2.const_mul (-((6 / 5 : ℝ) * Q.C0))).congr_deriv (by ring)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi_r
  have hexpB_nn : 0 ≤ (6 / 5 : ℝ) * Q.C0 * Real.exp (-(5 / 6 : ℝ) * B) := by
    have := Q.hC0; positivity
  linarith

end Tail

namespace LemmaQData

variable (Q : LemmaQData prob)


/-- Moment identity in `u`-coordinates on `[a, b] ⊆ [-A_{c'}^2, A_{c'}^2]`:
`∫ u in a..b, (-u) * (psiTilde prob c' g (u : ℂ)).re = M⁻¹ * ∫ t in Δ(b)..Δ(a), (-u_T(t)) * g(t) * V(t)`. -/
lemma psiTilde_moment_integral_eq {c' a b : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g)
    (ha_bd : -(Q.AC c' ^ 2) ≤ a) (hb_bd : b ≤ Q.AC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, (-u) * (psiTilde prob c' g (u : ℂ)).re =
      (prob.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          (-virasoroUT c' t) * (g t * prob.cardyV (c' / 12) t) := by
  have hc'_pos : 0 < c' := by linarith
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ Q.AC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1 : ∫ u in a..b, (-u) * (psiTilde prob c' g (u : ℂ)).re =
      -((prob.cardyNorm (c' / 12) g)⁻¹ *
        ∫ u in a..b, ((-u) * (g (virasoroDeltaChart c' u) *
          prob.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
          deriv (virasoroDeltaChart c') u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [Q.psiTilde_re_ofReal hc'_pos hg (hu_mem u hu)]
    ring
  have hsub : ∫ u in a..b, ((-u) * (g (virasoroDeltaChart c' u) *
        prob.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
        deriv (virasoroDeltaChart c') u =
      ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
        (-virasoroUT c' t) * (g t * prob.cardyV (c' / 12) t) := by
    have hcont_t : ContinuousOn
        (fun t : ℝ => (-virasoroUT c' t) * (g t * prob.cardyV (c' / 12) t))
        (virasoroDeltaChart c' '' Set.uIcc a b) := by
      have h_ut_cont : ContinuousOn (fun t : ℝ => -virasoroUT c' t)
          (virasoroDeltaChart c' '' Set.uIcc a b) := by
        intro t ht
        rcases ht with ⟨u, hu, rfl⟩
        rw [Set.uIcc_of_le hab] at hu
        have hdiv := Q.deltaChart_div_mem hc'_pos (hu_mem u hu)
        have hξ_open : ((virasoroDeltaChart c' u / c' : ℝ) : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
          rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have h1 : |virasoroDeltaChart c' u / c' - xiBar| ≤ virasoroChartR0 :=
            abs_le.mpr ⟨by linarith [hdiv.1], by linarith [hdiv.2]⟩
          exact h1.trans_lt (chartParams.hr_xi0_le.trans_lt (half_lt_self virasoroRXiInf_pos))
        have hcont_at : ContinuousAt (fun x : ℝ => virasoroUChart c' (x / c')) (virasoroDeltaChart c' u) := by
          unfold virasoroUChart
          have hcomp := (virasoroUInf_an _ hξ_open).continuousAt.comp_of_eq
            (Complex.continuous_ofReal.comp (continuous_id.div_const c')).continuousAt rfl
          exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hcomp))
        exact hcont_at.neg.continuousWithinAt
      refine h_ut_cont.mul ((hg.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono ?_)
      rintro t ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact (Q.deltaChart_pos hc'_pos (hu_mem u hu)).le
    have hderiv_at : ∀ u ∈ Set.uIcc a b,
        HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hd := Q.deltaChart_hasDerivAt hc'_pos (hu_mem u hu)
      exact hd.deriv ▸ hd
    -- Use `continuousOn_deriv_virasoroDeltaChart` logic directly via `Q.deltaChart_hasDerivAt`
    have hcont_der : ContinuousOn (deriv (virasoroDeltaChart c')) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      let G : ℝ → ℝ := fun u =>
        c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re
      have hG_cont : ContinuousOn G (Icc a b) := by
        intro u hu
        have hw : ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
          have h1 := Q.u_mem_open_ball hc'_pos (u := (u : ℂ))
            (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu_mem u hu)
          rwa [show (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
            ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) by push_cast; rfl] at h1
        have hd_an := (virasoroXiInf_an.deriv _ hw).continuousAt
        have hcomp := hd_an.comp_of_eq
          (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousAt rfl
        exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hcomp)).continuousWithinAt
      exact hG_cont.congr fun u hu => (Q.deltaChart_hasDerivAt hc'_pos (hu_mem u hu)).deriv
    have hcov := intervalIntegral.integral_comp_mul_deriv' hderiv_at hcont_der hcont_t
    calc ∫ u in a..b, ((-u) * (g (virasoroDeltaChart c' u) *
            prob.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
            deriv (virasoroDeltaChart c') u
        = ∫ u in a..b, ((-virasoroUT c' (virasoroDeltaChart c' u)) *
            (g (virasoroDeltaChart c' u) *
              prob.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
            deriv (virasoroDeltaChart c') u := by
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [Set.uIcc_of_le hab] at hu
          have huc : virasoroUT c' (virasoroDeltaChart c' u) = u := by
            unfold virasoroUT
            exact Q.uChart_deltaChart hc'_pos (hu_mem u hu)
          rw [huc]
      _ = ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
            (-virasoroUT c' t) * (g t * prob.cardyV (c' / 12) t) := hcov
  rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c' b) (virasoroDeltaChart c' a)]
  ring

end LemmaQData

section Shifted

variable [Q : LemmaQData prob]

/-! ### Section 4: Shifted Test Function, Line Estimate (`hI_line`), and Arc Estimate (`hArc_cov`, `hArc_unc`) -/

/-- Shifted quadrature test `f_{k, ℓ}(u) := \widetilde\Psi_V(u + ℓ) (1 + u / R)^{k + 1}`. -/
noncomputable def shiftedFunW (prob : FixedWeightProblem) (c' R ℓ : ℝ) (g : ℝ → ℝ) (k : ℕ) (u : ℂ) : ℂ :=
  psiTilde prob c' g (u + (ℓ : ℂ)) * (1 + u / (R : ℂ)) ^ (k + 1)

/-- Truncated first band moment `B_1^{(k)} := ∫_{-R}^{u_T} min(1, (k+1)(-u)/R) \widetilde\Psi_V(u) du`. -/
noncomputable def bandB1kW (prob : FixedWeightProblem) (c' R T : ℝ) (g : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ u in (-R)..(virasoroUT c' T),
    min 1 (((k : ℝ) + 1) * (-u) / R) * (psiTilde prob c' g (u : ℂ)).re

lemma bandB1kW_nonneg {c' R T : ℝ} (hc' : Q.cQ ≤ c')
    (hR_nn : 0 ≤ R) (hR_ub : R ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-R)) (huT_hi : virasoroUT c' T ≤ 0) (k : ℕ) :
    0 ≤ bandB1kW prob c' R T g k := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hu_mem := Q.UT_between hc'_pos (by linarith : -(Q.AC c' ^ 2) ≤ -R) le_rfl
    (by linarith [hR_nn, hR_ub] : -R ≤ Q.AC c' ^ 2) hT_lo hT_hi
  refine intervalIntegral.integral_nonneg hu_mem.1.1 fun u hu => ?_
  have hΨ_nn : 0 ≤ (psiTilde prob c' g (u : ℂ)).re := by
    refine (Q.part3 hc' hg).1 u (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩) ?_
    rw [← hu_mem.2]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩
      ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2, sq_nonneg (Q.AC c')]⟩ hu.2
  have hmin_nn : 0 ≤ min (1 : ℝ) (((k : ℝ) + 1) * (-u) / R) :=
    le_min zero_le_one (div_nonneg (mul_nonneg (by positivity) (by linarith [hu.2, huT_hi])) hR_nn)
  exact mul_nonneg hmin_nn hΨ_nn

lemma bandB1W_le_B1k {c' R T : ℝ} (hc' : Q.cQ ≤ c')
    (hR_pos : 0 < R) (hR_ub : R ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-R)) (k : ℕ) :
    bandB1W prob c' R T g ≤ bandB1kW prob c' R T g k := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hc'_24 : 24 ≤ c' := by have := Q.hcQ_10000; linarith
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((Q.hcQ_10000.trans hc'))
  have hΔ_lo : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ virasoroDeltaChart c' 0 :=
    (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [sq_nonneg (Q.AC c')], sq_nonneg _⟩
      ⟨by linarith [sq_nonneg (Q.AC c')], le_rfl⟩ (sq_nonneg _)
  have hu_mem := Q.UT_between hc'_pos (by linarith : -(Q.AC c' ^ 2) ≤ -R)
    (sq_nonneg _) (by linarith : -R ≤ 0) hT_lo hT_hi
  have hmom := Q.psiTilde_moment_integral_eq hc'_24 hg.1
    (by linarith : -(Q.AC c' ^ 2) ≤ -R) (by linarith [hu_mem.1.2, sq_nonneg (Q.AC c')])
    hu_mem.1.1
  rw [hu_mem.2] at hmom
  have hB1_eq : bandB1W prob c' R T g =
      ∫ u in (-R)..(virasoroUT c' T), ((-u) / R) * (psiTilde prob c' g (u : ℂ)).re := by
    unfold bandB1W
    rw [mul_assoc, ← hmom, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => by ring
  rw [hB1_eq]
  unfold bandB1kW
  have hΨ_cont : ContinuousOn (fun u : ℝ => (psiTilde prob c' g (u : ℂ)).re)
      (Icc (-R) (virasoroUT c' T)) := by
    refine Complex.continuous_re.comp_continuousOn
      ((Q.analytic hc' hg.1).continuousOn.comp
        continuous_ofReal.continuousOn fun u hu => ?_)
    exact Q.closedBall_subset_psiDom hc'_pos (by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩)
  have hi_l : IntervalIntegrable
      (fun u : ℝ => (-u / R) * (psiTilde prob c' g (u : ℂ)).re) volume (-R) (virasoroUT c' T) :=
    (((continuousOn_id.neg.div_const R).mul hΨ_cont)).intervalIntegrable_of_Icc hu_mem.1.1
  have hi_r : IntervalIntegrable
      (fun u : ℝ => min 1 (((k : ℝ) + 1) * (-u) / R) * (psiTilde prob c' g (u : ℂ)).re)
      volume (-R) (virasoroUT c' T) :=
    ((ContinuousOn.inf continuousOn_const ((continuousOn_const.mul continuousOn_id.neg).div_const R)).mul
      hΨ_cont).intervalIntegrable_of_Icc hu_mem.1.1
  refine intervalIntegral.integral_mono_on hu_mem.1.1 hi_l hi_r fun u hu => ?_
  have hΨ_nn : 0 ≤ (psiTilde prob c' g (u : ℂ)).re := by
    refine (Q.part3 hc' hg).1 u (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩) ?_
    rw [← hu_mem.2]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩
      ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2, sq_nonneg (Q.AC c')]⟩ hu.2
  have hu_le1 : (-u) / R ≤ 1 := (div_le_one hR_pos).mpr (by linarith [hu.1])
  have hu_le_k : (-u) / R ≤ ((k : ℝ) + 1) * (-u) / R := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (by linarith [hu.2, hu_mem.1.2]) hk1) hR_pos.le
  exact mul_le_mul_of_nonneg_right (le_min hu_le1 hu_le_k) hΨ_nn

end Shifted

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.pos_real_norm_tail_leW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pos_real_norm_tail_leW

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.psiTilde_moment_integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.psiTilde_moment_integral_eq

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.bandB1kW_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bandB1kW_nonneg

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.bandB1W_le_B1k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bandB1W_le_B1k

end FormalResearch.ModularBootstrap.FixedWeightBand
