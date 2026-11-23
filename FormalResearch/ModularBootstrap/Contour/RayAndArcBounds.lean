module

public import FormalResearch.ModularBootstrap.Contour.PathTools

/-!
# Ray, Short-Arc, and Radial Decay Estimates for Lemma Z'

Proves the local saddle-descent estimates used in `Contour.SaddleContour` (`vlo:Zp`, lines
582–612 of `lower_o1_two_edge.tex`):
* `ray_H_integral_eq` and `saddle_ray_H_le`: exact Taylor integral along `w(v) = w₀ + v e^{iγ}`
  via `lemma_S5_deriv` and `lemma_F`, and the explicit `cos(2γ + arg s)` / `cos(3γ)` upper bound
  from `s = ρ e^{i(π/2 - φ')}`;
* `upper_ray_trig_le`, `lower_ray_trig_ge_pi4_le`, `lower_ray_trig_le_pi4_le`: trigonometric
  margins on the three rays `γ = π/3`, `-5π/12`, `5π/4`;
* `arc_cos_three_le_start_upper`, `arc_cos_three_le_start_lower`, `arc_H_step_le`: nonincrease
  of `cos(3α)` along short arcs from `arg(s + A₀ ρ e^{iγ})` to `±π/3` and total `H`-increment;
* `radial_H_antitone`: negative radial derivative along `r e^{±iπ/3}` for `(A₀ - 1) ρ ≤ r ≤ δ`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Contour

open Chart ChartGeometry

private lemma exp_ofReal_mul_I_norm (α : ℝ) : ‖Complex.exp (Complex.I * (α : ℂ))‖ = 1 := by
  rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring, Complex.norm_exp_ofReal_mul_I]

private lemma exp_ofReal_mul_I_re' (α : ℝ) :
    (Complex.exp (Complex.I * (α : ℂ))).re = Real.cos α := by
  rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring, Complex.exp_ofReal_mul_I_re]

private lemma exp_ofReal_mul_I_im' (α : ℝ) :
    (Complex.exp (Complex.I * (α : ℂ))).im = Real.sin α := by
  rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring, Complex.exp_ofReal_mul_I_im]

/-- Exact integral representation along a straight ray `w(v) = w₀ + v e^{iγ}` inside
`ball 0 ρ_F ∩ {0 ≤ Re w ≤ 1/4}` using `lemma_S5_deriv` and `lemma_F`. -/
lemma ray_phi_diff_eq {η : ℂ → ℂ → ℂ} {ρ_F : ℝ}
    (hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    {s b w₀ : ℂ} (hb_re : 0 < b.re) (hb_eq : b = chartB s) (hs_F : s ∈ ball (0 : ℂ) ρ_F)
    {γ t_max : ℝ} (_ht_max : 0 ≤ t_max)
    (hw_mem : ∀ v ∈ Icc (0 : ℝ) t_max,
      let w := w₀ + (v : ℂ) * Complex.exp (Complex.I * (γ : ℂ))
      w ∈ ball (0 : ℂ) ρ_F ∧ 0 ≤ w.re ∧ w.re ≤ 1 / 4) :
    ∀ t ∈ Icc (0 : ℝ) t_max,
      let dir := Complex.exp (Complex.I * (γ : ℂ))
      let w : ℝ → ℂ := fun v => w₀ + (v : ℂ) * dir
      chartPhiV (w t) b - chartPhiV w₀ b =
        ∫ v in (0 : ℝ)..t, (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((w v) ^ 2 - s ^ 2) *
          (1 + η (w v) s)) * dir := by
  intro t ht dir w
  have ht_nn : 0 ≤ t := ht.1
  let g : ℝ → ℂ := fun v => chartPhiV (w v) b
  let g' : ℝ → ℂ := fun v => (2 * Complex.log (chartB (w v) / b) * deriv chartOmega (w v)) * dir
  have hw_strip : ∀ v ∈ Icc (0 : ℝ) t_max, 0 ≤ (w v).re ∧ (w v).re ≤ 1 / 2 ∧ w v ≠ 1 / 2 :=
    fun v hv => by
      have hm := hw_mem v hv
      refine ⟨hm.2.1, hm.2.2.trans (by norm_num), fun h0 => ?_⟩
      have := congrArg Complex.re h0; simp at this; linarith [hm.2.2]
  have hg_cont : ContinuousOn g (Icc 0 t) := fun v hv => by
    have hv_max : v ∈ Icc 0 t_max := ⟨hv.1, hv.2.trans ht.2⟩
    have ⟨h0, h1, hne⟩ := hw_strip v hv_max
    have hd := (lemma_S5_deriv hb_re).2.2 _ h0 h1 hne
    have hm : MapsTo w (Icc 0 t) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2} := fun x hx =>
      ⟨(hw_strip x ⟨hx.1, hx.2.trans ht.2⟩).1, (hw_strip x ⟨hx.1, hx.2.trans ht.2⟩).2.1⟩
    have hc_w : ContinuousWithinAt w (Icc 0 t) v :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousWithinAt
    exact hd.continuousWithinAt.comp_of_eq hc_w hm rfl
  have hg_deriv : ∀ v ∈ Ioo 0 t, HasDerivAt g (g' v) v := fun v hv => by
    have hv_max : v ∈ Icc 0 t_max := ⟨hv.1.le, hv.2.le.trans ht.2⟩
    have ⟨h0, h1, hne⟩ := hw_strip v hv_max
    have hd := (lemma_S5_deriv hb_re).2.2 _ h0 h1 hne
    have hlin : HasDerivWithinAt w dir (Ioo 0 t) v := by
      have h1' : HasDerivAt (fun x : ℝ => (x : ℂ) * dir) dir v := by
        simpa using Complex.ofRealCLM.hasDerivAt.mul_const dir
      exact (h1'.const_add w₀).hasDerivWithinAt
    have hm : MapsTo w (Ioo 0 t) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2} := fun x hx =>
      ⟨(hw_strip x ⟨hx.1.le, hx.2.le.trans ht.2⟩).1,
       (hw_strip x ⟨hx.1.le, hx.2.le.trans ht.2⟩).2.1⟩
    exact (hd.comp v hlin hm).hasDerivAt (isOpen_Ioo.mem_nhds hv)
  have hg'_eq : EqOn g' (fun v => (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((w v) ^ 2 - s ^ 2) *
      (1 + η (w v) s)) * dir) (Icc 0 t) := fun v hv => by
    have hv_max : v ∈ Icc 0 t_max := ⟨hv.1, hv.2.trans ht.2⟩
    dsimp [g']
    rw [hb_eq, hF_id (w v) (hw_mem v hv_max).1 s hs_F]
  have hg'_cont : ContinuousOn g' (Icc 0 t) := by
    refine ContinuousOn.congr ?_ hg'_eq
    have hw_cont : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hη_comp : ContinuousOn (fun v => η (w v) s) (Icc 0 t) := fun v hv => by
      have hv_max : v ∈ Icc 0 t_max := ⟨hv.1, hv.2.trans ht.2⟩
      have hpair : ((w v, s) : ℂ × ℂ) ∈ ball (0 : ℂ × ℂ) ρ_F := by
        rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
        exact ⟨mem_ball_zero_iff.mp (hw_mem v hv_max).1, mem_ball_zero_iff.mp hs_F⟩
      have hc_at : ContinuousAt (Function.uncurry η) (w v, s) := (hη_an _ hpair).continuousAt
      exact (hc_at.comp_of_eq (hw_cont.prodMk continuous_const).continuousAt rfl).continuousWithinAt
    exact ((continuousOn_const.mul ((hw_cont.pow 2).continuousOn.sub continuousOn_const)).mul
      (continuousOn_const.add hη_comp)).mul continuousOn_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht_nn hg_cont hg_deriv
    (hg'_cont.mono (by rw [Set.uIcc_of_le ht_nn])).intervalIntegrable
  have heq_int : ∫ v in (0 : ℝ)..t, g' v =
      ∫ v in (0 : ℝ)..t, (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((w v) ^ 2 - s ^ 2) *
        (1 + η (w v) s)) * dir := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le ht_nn] at hv
    exact hg'_eq hv
  have hw0 : w 0 = w₀ := by simp [w]
  rw [← hw0]
  exact hftc.symm.trans heq_int

/-- Saddle ray upper bound for `w(v) = s + v e^{iγ}` with `s = ρ e^{i(π/2 - φ')}`. -/
lemma saddle_ray_H_le {η : ℂ → ℂ → ℂ} {ρ_F C_F : ℝ}
    (hCF_nn : 0 ≤ C_F)
    (hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    (hη_bd : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      ‖η w s‖ ≤ C_F * (‖w‖ + ‖s‖))
    {ρ φ' γ t_max : ℝ} (hρ_nn : 0 ≤ ρ) (ht_max : 0 ≤ t_max)
    (s b : ℂ) (hs_def : s = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)))
    (hb_re : 0 < b.re) (hb_eq : b = chartB s) (hs_F : s ∈ ball (0 : ℂ) ρ_F)
    (hw_mem : ∀ v ∈ Icc (0 : ℝ) t_max,
      let w := s + (v : ℂ) * Complex.exp (Complex.I * (γ : ℂ))
      w ∈ ball (0 : ℂ) ρ_F ∧ 0 ≤ w.re ∧ w.re ≤ 1 / 4) :
    ∀ t ∈ Icc (0 : ℝ) t_max,
      let dir := Complex.exp (Complex.I * (γ : ℂ))
      (chartPhiV (s + (t : ℂ) * dir) b).re - (chartPhiV s b).re ≤
        (Real.pi ^ 2 / 6) * (ρ * t ^ 2 * Real.cos (2 * γ + Real.pi / 2 - φ') +
          (1 / 3 : ℝ) * t ^ 3 * Real.cos (3 * γ) + 2 * C_F * t ^ 2 * (ρ + t) ^ 2) := by
  intro t ht dir
  have hdiff := ray_phi_diff_eq hη_an hF_id hb_re hb_eq hs_F ht_max hw_mem t ht
  let w : ℝ → ℂ := fun v => s + (v : ℂ) * dir
  let main : ℝ → ℂ := fun v =>
    ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (2 * s * dir ^ 2 * (v : ℂ) + dir ^ 3 * (v : ℂ) ^ 2)
  let rem : ℝ → ℂ := fun v =>
    ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((w v) ^ 2 - s ^ 2) * η (w v) s * dir
  have hsplit : ∀ v : ℝ,
      (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((w v) ^ 2 - s ^ 2) * (1 + η (w v) s)) * dir =
        main v + rem v := fun v => by
    dsimp [main, rem, w]; ring
  have hmain_cont : Continuous main := by dsimp [main]; fun_prop
  have hrem_cont : ContinuousOn rem (Icc 0 t) := by
    dsimp [rem]
    have hw_cont : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hη_comp : ContinuousOn (fun v => η (w v) s) (Icc 0 t) := fun v hv => by
      have hv_max : v ∈ Icc 0 t_max := ⟨hv.1, hv.2.trans ht.2⟩
      have hpair : ((w v, s) : ℂ × ℂ) ∈ ball (0 : ℂ × ℂ) ρ_F := by
        rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
        exact ⟨mem_ball_zero_iff.mp (hw_mem v hv_max).1, mem_ball_zero_iff.mp hs_F⟩
      have hc_at : ContinuousAt (Function.uncurry η) (w v, s) := (hη_an _ hpair).continuousAt
      exact (hc_at.comp_of_eq (hw_cont.prodMk continuous_const).continuousAt rfl).continuousWithinAt
    exact ((continuousOn_const.mul ((hw_cont.pow 2).continuousOn.sub continuousOn_const)).mul
      hη_comp).mul continuousOn_const
  have hre_diff : (chartPhiV (w t) b).re - (chartPhiV s b).re =
      (∫ v in (0 : ℝ)..t, main v).re + (∫ v in (0 : ℝ)..t, rem v).re := by
    rw [← Complex.sub_re, hdiff]
    have hint_eq : ∫ v in (0 : ℝ)..t,
        (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((w v) ^ 2 - s ^ 2) * (1 + η (w v) s)) * dir =
        (∫ v in (0 : ℝ)..t, main v) + ∫ v in (0 : ℝ)..t, rem v := by
      rw [← intervalIntegral.integral_add (hmain_cont.intervalIntegrable 0 t)
        ((hrem_cont.mono (by rw [Set.uIcc_of_le ht.1])).intervalIntegrable)]
      exact intervalIntegral.integral_congr fun v _ => hsplit v
    rw [hint_eq, Complex.add_re]
  have hmain_val : (∫ v in (0 : ℝ)..t, main v).re =
      (Real.pi ^ 2 / 6) * (ρ * t ^ 2 * Real.cos (2 * γ + Real.pi / 2 - φ') +
        (1 / 3 : ℝ) * t ^ 3 * Real.cos (3 * γ)) := by
    let P : ℝ → ℂ := fun v =>
      ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (s * dir ^ 2 * (v : ℂ) ^ 2 + (1 / 3 : ℂ) * dir ^ 3 * (v : ℂ) ^ 3)
    have hP_der : ∀ v : ℝ, HasDerivAt P (main v) v := fun v => by
      dsimp [P, main]
      have hd0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 v := by
        simpa [Complex.real_smul] using (hasDerivAt_id v).smul_const (1 : ℂ)
      have hd1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * (v : ℂ)) v := by
        have hsq : (fun x : ℝ => (x : ℂ) ^ 2) = (fun x : ℝ => (x : ℂ)) * (fun x : ℝ => (x : ℂ)) := by
          ext x; simp [sq]
        rw [hsq]
        exact (hd0.mul hd0).congr_deriv (by simp; ring)
      have hd2 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 3) (3 * (v : ℂ) ^ 2) v := by
        have hcb : (fun x : ℝ => (x : ℂ) ^ 3) = (fun x : ℝ => (x : ℂ) ^ 2) * (fun x : ℝ => (x : ℂ)) := by
          ext x; simp [pow_succ]
        rw [hcb]
        exact (hd1.mul hd0).congr_deriv (by simp; ring)
      have hP_raw := (((hd1.const_mul (s * dir ^ 2)).add
        (hd2.const_mul ((1 / 3 : ℂ) * dir ^ 3))).const_mul ((Real.pi ^ 2 / 6 : ℝ) : ℂ))
      exact (hP_raw.congr_of_eventuallyEq (Eventually.of_forall fun x => by
        simp [Pi.add_apply])).congr_deriv (by ring)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun v _ => hP_der v) (hmain_cont.intervalIntegrable 0 t)
    have hP0 : P 0 = 0 := by simp [P]
    rw [hftc, hP0, sub_zero]
    have hdir2 : dir ^ 2 = Complex.exp (Complex.I * ((2 * γ : ℝ) : ℂ)) := by
      dsimp [dir]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hdir3 : dir ^ 3 = Complex.exp (Complex.I * ((3 * γ : ℝ) : ℂ)) := by
      dsimp [dir]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hs_dir2 : s * dir ^ 2 =
        (ρ : ℂ) * Complex.exp (Complex.I * ((2 * γ + Real.pi / 2 - φ' : ℝ) : ℂ)) := by
      rw [hs_def, hdir2, mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    have hre1 : (s * dir ^ 2).re = ρ * Real.cos (2 * γ + Real.pi / 2 - φ') := by
      rw [hs_dir2, Complex.re_ofReal_mul, exp_ofReal_mul_I_re']
    have hre2 : (dir ^ 3).re = Real.cos (3 * γ) := by
      rw [hdir3, exp_ofReal_mul_I_re']
    dsimp [P]
    rw [Complex.re_ofReal_mul, Complex.add_re]
    have ht2_c : ((t : ℂ) ^ 2) = ((t ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    have ht3_c : ((t : ℂ) ^ 3) = ((t ^ 3 : ℝ) : ℂ) := by push_cast; rfl
    have h13_c : (1 / 3 : ℂ) * dir ^ 3 * (t : ℂ) ^ 3 =
        (((1 / 3 : ℝ) * t ^ 3 : ℝ) : ℂ) * dir ^ 3 := by push_cast; ring
    rw [ht2_c, show s * dir ^ 2 * ((t ^ 2 : ℝ) : ℂ) = ((t ^ 2 : ℝ) : ℂ) * (s * dir ^ 2) by ring,
      Complex.re_ofReal_mul, hre1, h13_c, Complex.re_ofReal_mul, hre2]
    ring
  have hs_norm : ‖s‖ = ρ := by
    rw [hs_def, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_nn, exp_ofReal_mul_I_norm, mul_one]
  have hdir_norm : ‖dir‖ = 1 := exp_ofReal_mul_I_norm γ
  have hrem_bd : (∫ v in (0 : ℝ)..t, rem v).re ≤
      (Real.pi ^ 2 / 6) * (2 * C_F * t ^ 2 * (ρ + t) ^ 2) := by
    have hle_norm : (∫ v in (0 : ℝ)..t, rem v).re ≤ ‖∫ v in (0 : ℝ)..t, rem v‖ :=
      Complex.re_le_norm _
    have h_int_bd : ∀ v ∈ Icc (0 : ℝ) t,
        ‖rem v‖ ≤ (Real.pi ^ 2 / 6) * (4 * C_F * (ρ + t) ^ 2) * v := fun v hv => by
      have hv_max : v ∈ Icc 0 t_max := ⟨hv.1, hv.2.trans ht.2⟩
      have hvw_diff : ‖(w v) ^ 2 - s ^ 2‖ ≤ v * (2 * ρ + v) := by
        have hid : (w v) ^ 2 - s ^ 2 = (v : ℂ) * dir * (2 * s + (v : ℂ) * dir) := by
          dsimp [w]; ring
        rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.1, hdir_norm, mul_one]
        refine mul_le_mul_of_nonneg_left ?_ hv.1
        calc ‖2 * s + (v : ℂ) * dir‖ ≤ ‖2 * s‖ + ‖(v : ℂ) * dir‖ := norm_add_le _ _
          _ = 2 * ρ + v := by
              rw [norm_mul, Complex.norm_ofNat, hs_norm, norm_mul, Complex.norm_real,
                Real.norm_of_nonneg hv.1, hdir_norm, mul_one]
      have hη_b : ‖η (w v) s‖ ≤ C_F * (2 * ρ + v) := by
        have h1 := hη_bd (w v) (hw_mem v hv_max).1 s hs_F
        have hw_ub : ‖w v‖ ≤ ρ + v := by
          calc ‖s + (v : ℂ) * dir‖ ≤ ‖s‖ + ‖(v : ℂ) * dir‖ := norm_add_le _ _
            _ = ρ + v := by
                rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.1, hdir_norm, mul_one]
        exact h1.trans (mul_le_mul_of_nonneg_left (by linarith [hs_norm]) hCF_nn)
      have h2ρ : 2 * ρ + v ≤ 2 * (ρ + t) := by linarith [hv.1, hv.2]
      dsimp [rem]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity [Real.pi_pos]), hdir_norm, mul_one]
      have hsub_pos : 0 ≤ 2 * ρ + v := by linarith [hρ_nn, hv.1]
      have hv_nn : 0 ≤ v := hv.1
      calc (Real.pi ^ 2 / 6) * ‖(w v) ^ 2 - s ^ 2‖ * ‖η (w v) s‖
          ≤ (Real.pi ^ 2 / 6) * (v * (2 * ρ + v)) * (C_F * (2 * ρ + v)) := by
            gcongr
        _ = (Real.pi ^ 2 / 6) * C_F * (2 * ρ + v) ^ 2 * v := by ring
        _ ≤ (Real.pi ^ 2 / 6) * C_F * (2 * (ρ + t)) ^ 2 * v := by
            gcongr
        _ = (Real.pi ^ 2 / 6) * (4 * C_F * (ρ + t) ^ 2) * v := by ring
    have h_mono := intervalIntegral.integral_mono_on ht.1
      ((hrem_cont.norm.mono (by rw [Set.uIcc_of_le ht.1])).intervalIntegrable (μ := volume))
      ((by fun_prop : Continuous fun v : ℝ =>
        (Real.pi ^ 2 / 6) * (4 * C_F * (ρ + t) ^ 2) * v).intervalIntegrable (μ := volume) 0 t)
      h_int_bd
    have hv_int : ∫ v in (0 : ℝ)..t, ((Real.pi ^ 2 / 6) * (4 * C_F * (ρ + t) ^ 2) * v) =
        (Real.pi ^ 2 / 6) * (2 * C_F * t ^ 2 * (ρ + t) ^ 2) := by
      let C_int : ℝ := (Real.pi ^ 2 / 6) * (4 * C_F * (ρ + t) ^ 2)
      have hd : ∀ v : ℝ, HasDerivAt (fun x : ℝ => C_int * (x ^ 2 / 2)) (C_int * v) v := fun v =>
        (((hasDerivAt_pow 2 v).div_const 2).const_mul C_int).congr_deriv
          (g' := C_int * v) (by simp)
      have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
        (fun v _ => hd v) ((continuous_const.mul (continuous_id : Continuous fun v : ℝ => v)).intervalIntegrable (μ := volume) 0 t)
      calc ∫ v in (0 : ℝ)..t, ((Real.pi ^ 2 / 6) * (4 * C_F * (ρ + t) ^ 2) * v)
          = ∫ v in (0 : ℝ)..t, C_int * v := by simp [C_int, mul_assoc]
        _ = C_int * (t ^ 2 / 2) - C_int * (0 ^ 2 / 2) := heq
        _ = (Real.pi ^ 2 / 6) * (2 * C_F * t ^ 2 * (ρ + t) ^ 2) := by dsimp [C_int]; ring
    have hnorm_rem := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := rem) ht.1
    linarith [hle_norm, hnorm_rem, h_mono, hv_int]
  change (chartPhiV (w t) b).re - (chartPhiV s b).re ≤ _
  linarith [hre_diff, hmain_val, hrem_bd]

/-! ### Section 2: Trigonometric margins on the three saddle rays -/

lemma upper_ray_cos_le {φ' : ℝ} (hφ0 : 0 ≤ φ') (hφ1 : φ' ≤ Real.pi / 2) :
    Real.cos (2 * (Real.pi / 3) + Real.pi / 2 - φ') ≤ -(1 / 2 : ℝ) := by
  have heq : 2 * (Real.pi / 3) + Real.pi / 2 - φ' = 7 * Real.pi / 6 - φ' := by ring
  rw [heq]
  rcases le_total (7 * Real.pi / 6 - φ') Real.pi with hle | hge
  · have h_mem1 : (2 * Real.pi / 3 : ℝ) ∈ Icc 0 Real.pi := ⟨by positivity [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have h_mem2 : 7 * Real.pi / 6 - φ' ∈ Icc 0 Real.pi := ⟨by linarith [Real.pi_pos], hle⟩
    have hle' := Real.strictAntiOn_cos.antitoneOn h_mem1 h_mem2 (by linarith)
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at hle'
    exact hle'
  · have hcos : Real.cos (7 * Real.pi / 6 - φ') = -Real.cos (Real.pi / 6 - φ') := by
      rw [show 7 * Real.pi / 6 - φ' = (Real.pi / 6 - φ') + Real.pi by ring, Real.cos_add_pi]
    rw [hcos]
    have h_mem1 : Real.pi / 6 - φ' ∈ Icc 0 Real.pi := ⟨by linarith, by linarith [Real.pi_pos]⟩
    have h_mem2 : (Real.pi / 3 : ℝ) ∈ Icc 0 Real.pi := ⟨by positivity [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hge' := Real.strictAntiOn_cos.antitoneOn h_mem1 h_mem2 (by linarith)
    rw [Real.cos_pi_div_three] at hge'
    linarith

lemma lower_ray_ge_pi4_cos_le {φ' : ℝ} (hφ0 : Real.pi / 4 ≤ φ') (hφ1 : φ' ≤ Real.pi / 2) :
    Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') ≤ Real.cos (7 * Real.pi / 12) ∧
    Real.cos (7 * Real.pi / 12) < 0 := by
  have heq : 2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ' = -(Real.pi / 3 + φ') := by ring
  rw [heq, Real.cos_neg]
  have hmem1 : (7 * Real.pi / 12 : ℝ) ∈ Icc 0 Real.pi := ⟨by positivity [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmem2 : Real.pi / 3 + φ' ∈ Icc 0 Real.pi := ⟨by linarith [Real.pi_pos, hφ0], by linarith [Real.pi_pos]⟩
  have hmem0 : (Real.pi / 2 : ℝ) ∈ Icc 0 Real.pi := ⟨by positivity [Real.pi_pos], by linarith [Real.pi_pos]⟩
  refine ⟨Real.strictAntiOn_cos.antitoneOn hmem1 hmem2 (by linarith), ?_⟩
  have hlt := Real.strictAntiOn_cos hmem0 hmem1 (by linarith [Real.pi_pos])
  rwa [Real.cos_pi_div_two] at hlt

lemma lower_ray_le_pi4_cos_le {φ' : ℝ} (hφ0 : 0 ≤ φ') (hφ1 : φ' ≤ Real.pi / 4) :
    Real.cos (2 * (5 * Real.pi / 4) + Real.pi / 2 - φ') ≤ -(1 / √2) ∧
    Real.cos (3 * (5 * Real.pi / 4)) = 1 / √2 := by
  have heq1 : 2 * (5 * Real.pi / 4) + Real.pi / 2 - φ' = (-φ') + 3 * Real.pi := by ring
  have heq1' : Real.cos (2 * (5 * Real.pi / 4) + Real.pi / 2 - φ') = -Real.cos φ' := by
    rw [heq1, show (-φ') + 3 * Real.pi = (-φ' + Real.pi) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_add_pi, Real.cos_neg]
  have hinv_sq : 1 / √2 = √2 / 2 := by
    have hsq2 : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
    rw [div_eq_div_iff hsq2 two_ne_zero]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
  have hcos_ge : 1 / √2 ≤ Real.cos φ' := by
    have h1 : φ' ∈ Icc 0 Real.pi := ⟨hφ0, hφ1.trans (by linarith [Real.pi_pos])⟩
    have h2 : (Real.pi / 4 : ℝ) ∈ Icc 0 Real.pi := ⟨by positivity [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hle := Real.strictAntiOn_cos.antitoneOn h1 h2 hφ1
    rw [Real.cos_pi_div_four] at hle
    linarith
  have heq2 : 3 * (5 * Real.pi / 4) = -(Real.pi / 4) + 2 * (2 * Real.pi) := by ring
  have hcos2 : Real.cos (3 * (5 * Real.pi / 4)) = 1 / √2 := by
    rw [heq2, show -(Real.pi / 4) + 2 * (2 * Real.pi) = (-(Real.pi / 4) + 2 * Real.pi) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_four]
    exact hinv_sq.symm
  exact ⟨by linarith, hcos2⟩

/-! ### Section 3: Short circular arcs (`cos(3α) ≤ cos(3θ₀)`) and radial decay -/

lemma cos_three_le_of_upper_arc {θ₀ α : ℝ} (hθ0 : 0 ≤ θ₀) (hθ1 : θ₀ ≤ Real.pi / 2)
    (hα : α ∈ uIcc θ₀ (Real.pi / 3)) : Real.cos (3 * α) ≤ Real.cos (3 * θ₀) := by
  rcases le_total θ₀ (Real.pi / 3) with hle | hge
  · rw [Set.uIcc_of_le hle] at hα
    exact Real.strictAntiOn_cos.antitoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith [hα.1], by linarith [hα.2]⟩ (by linarith [hα.1])
  · rw [Set.uIcc_of_ge hge] at hα
    rw [show Real.cos (3 * α) = -Real.cos (3 * α - Real.pi) by rw [← Real.cos_add_pi]; ring_nf,
        show Real.cos (3 * θ₀) = -Real.cos (3 * θ₀ - Real.pi) by rw [← Real.cos_add_pi]; ring_nf]
    have ha_mem : 3 * α - Real.pi ∈ Icc 0 Real.pi := ⟨by linarith [hα.1], by linarith [hα.2, hθ1]⟩
    have hθ_mem : 3 * θ₀ - Real.pi ∈ Icc 0 Real.pi := ⟨by linarith [hge], by linarith [hθ1]⟩
    have hle' := Real.strictAntiOn_cos.antitoneOn ha_mem hθ_mem (by linarith [hα.2])
    linarith

lemma cos_three_le_of_lower_arc {θ₀ α : ℝ} (hθ0 : -(Real.pi / 2) ≤ θ₀) (hθ1 : θ₀ ≤ 0)
    (hα : α ∈ uIcc θ₀ (-(Real.pi / 3))) : Real.cos (3 * α) ≤ Real.cos (3 * θ₀) := by
  have heq : ∀ x : ℝ, Real.cos (3 * x) = Real.cos (3 * (-x)) := fun x => by
    rw [show 3 * (-x) = -(3 * x) by ring, Real.cos_neg]
  rw [heq α, heq θ₀]
  refine cos_three_le_of_upper_arc (by linarith) (by linarith) ?_
  rw [Set.mem_uIcc] at hα ⊢
  rcases hα with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; exact ⟨by linarith, by linarith⟩
  · left; exact ⟨by linarith, by linarith⟩

/-- Short-arc `H`-step bound along `α ↦ r * exp(i α)` from `θ₀` to `θ₁ = ±π/3`. -/
lemma arc_H_step_le {η : ℂ → ℂ → ℂ} {ρ_F C_F : ℝ}
    (hCF_nn : 0 ≤ C_F)
    (hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    (hη_bd : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      ‖η w s‖ ≤ C_F * (‖w‖ + ‖s‖))
    {s b : ℂ} (hb_re : 0 < b.re) (hb_eq : b = chartB s) (hs_F : s ∈ ball (0 : ℂ) ρ_F)
    {r θ₀ θ₁ : ℝ} (hr_pos : 0 < r) (hr_lt : r < ρ_F) (hs_le : ‖s‖ ≤ r)
    (hθ_diff : |θ₁ - θ₀| ≤ Real.pi / 2)
    (harc_mem : ∀ α ∈ uIcc θ₀ θ₁,
      let w := (r : ℂ) * Complex.exp (Complex.I * (α : ℂ))
      0 ≤ w.re ∧ w.re ≤ 1 / 4)
    (hcos : ∀ α ∈ uIcc θ₀ θ₁, Real.cos (3 * α) ≤ Real.cos (3 * θ₀)) :
    ∀ α ∈ uIcc θ₀ θ₁,
      let w := (r : ℂ) * Complex.exp (Complex.I * (α : ℂ))
      let w₀ := (r : ℂ) * Complex.exp (Complex.I * (θ₀ : ℂ))
      (chartPhiV w b).re - (chartPhiV w₀ b).re ≤
        (Real.pi ^ 2 / 6) * (Real.pi / 2) * r * (‖s‖ ^ 2 + 4 * C_F * r ^ 3) := by
  intro α hα w w₀
  let γ : ℝ → ℂ := fun t => (r : ℂ) * Complex.exp (Complex.I * (t : ℂ))
  have hγ_F : ∀ t : ℝ, γ t ∈ ball (0 : ℂ) ρ_F := fun t => by
    rw [mem_ball_zero_iff]
    simpa [γ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_pos.le, exp_ofReal_mul_I_norm]
      using hr_lt
  have hγ_norm : ∀ t : ℝ, ‖γ t‖ = r := fun t => by
    dsimp [γ]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_pos.le, exp_ofReal_mul_I_norm, mul_one]
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ (Complex.I * γ t) t := fun t => by
    dsimp [γ]
    have h1 : HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ)) Complex.I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
    exact (h1.cexp.const_mul (r : ℂ)).congr_deriv (by ring)
  let g : ℝ → ℂ := fun t => chartPhiV (γ t) b
  let g' : ℝ → ℂ := fun t =>
    (2 * Complex.log (chartB (γ t) / b) * deriv chartOmega (γ t)) * (Complex.I * γ t)
  have hu_sub : uIcc θ₀ α ⊆ uIcc θ₀ θ₁ := Set.uIcc_subset_uIcc Set.left_mem_uIcc hα
  have hw_strip : ∀ t ∈ uIcc θ₀ θ₁, 0 ≤ (γ t).re ∧ (γ t).re ≤ 1 / 2 ∧ γ t ≠ 1 / 2 :=
    fun t ht => by
      have hm := harc_mem t ht
      refine ⟨hm.1, hm.2.trans (by norm_num), fun h0 => ?_⟩
      have := congrArg Complex.re h0; simp at this; linarith [hm.2]
  have hg_cont : ContinuousOn g (uIcc θ₀ α) := fun t ht => by
    have ⟨h0, h1, hne⟩ := hw_strip t (hu_sub ht)
    have hd := (lemma_S5_deriv hb_re).2.2 _ h0 h1 hne
    have hm : MapsTo γ (uIcc θ₀ α) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2} := fun x hx =>
      ⟨(hw_strip x (hu_sub hx)).1, (hw_strip x (hu_sub hx)).2.1⟩
    have hc_γ : ContinuousWithinAt γ (uIcc θ₀ α) t := (hγ_deriv t).continuousAt.continuousWithinAt
    exact hd.continuousWithinAt.comp_of_eq hc_γ hm rfl
  have hg_deriv : ∀ t ∈ Ioo (min θ₀ α) (max θ₀ α), HasDerivAt g (g' t) t := fun t ht => by
    have ht_u : t ∈ uIcc θ₀ θ₁ := hu_sub (Ioo_subset_Icc_self ht)
    have ⟨h0, h1, hne⟩ := hw_strip t ht_u
    have hd := (lemma_S5_deriv hb_re).2.2 _ h0 h1 hne
    have hm : MapsTo γ (Ioo (min θ₀ α) (max θ₀ α)) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2} :=
      fun x hx => ⟨(hw_strip x (hu_sub (Ioo_subset_Icc_self hx))).1,
        (hw_strip x (hu_sub (Ioo_subset_Icc_self hx))).2.1⟩
    exact (hd.comp t (hγ_deriv t).hasDerivWithinAt hm).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hg'_eq : EqOn g' (fun t =>
      (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((γ t) ^ 2 - s ^ 2) * (1 + η (γ t) s)) * (Complex.I * γ t))
      (uIcc θ₀ θ₁) := fun t _ => by
    dsimp [g']; rw [hb_eq, hF_id (γ t) (hγ_F t) s hs_F]
  let main : ℝ → ℂ := fun t => ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (γ t) ^ 2 * (Complex.I * γ t)
  let rem : ℝ → ℂ := fun t =>
    ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (-s ^ 2 + ((γ t) ^ 2 - s ^ 2) * η (γ t) s) * (Complex.I * γ t)
  have hg'_split : EqOn g' (fun t => main t + rem t) (uIcc θ₀ θ₁) := fun t ht => by
    rw [hg'_eq ht]; dsimp [main, rem]; ring
  have hg'_cont : ContinuousOn g' (uIcc θ₀ θ₁) := by
    refine ContinuousOn.congr ?_ (fun t ht => hg'_eq ht)
    have hγ_c : Continuous γ := by dsimp [γ]; fun_prop
    have hη_c : ContinuousOn (fun t => η (γ t) s) (uIcc θ₀ θ₁) := fun t _ => by
      have hpair : ((γ t, s) : ℂ × ℂ) ∈ ball (0 : ℂ × ℂ) ρ_F := by
        rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
        exact ⟨mem_ball_zero_iff.mp (hγ_F t), mem_ball_zero_iff.mp hs_F⟩
      have hc_map : Continuous (fun x : ℝ => (γ x, s)) := hγ_c.prodMk continuous_const
      have hc_at : ContinuousAt (Function.uncurry η) (γ t, s) := (hη_an _ hpair).continuousAt
      exact (hc_at.comp_of_eq hc_map.continuousAt rfl).continuousWithinAt
    have hpoly : ContinuousOn (fun t : ℝ =>
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((γ t) ^ 2 - s ^ 2)) (uIcc θ₀ θ₁) := by fun_prop
    exact (hpoly.mul (continuousOn_const.add hη_c)).mul (by fun_prop)
  have hftc : chartPhiV w b - chartPhiV w₀ b = ∫ t in θ₀..α, g' t := by
    have hint : IntervalIntegrable g' volume θ₀ α := (hg'_cont.mono hu_sub).intervalIntegrable
    rcases le_total θ₀ α with hle | hge
    · have hc' : ContinuousOn g (Icc θ₀ α) := by rwa [← Set.uIcc_of_le hle]
      have hd' : ∀ t ∈ Ioo θ₀ α, HasDerivAt g (g' t) t := fun t ht =>
        hg_deriv t (by rwa [min_eq_left hle, max_eq_right hle])
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hc' hd' hint).symm
    · have hc' : ContinuousOn g (Icc α θ₀) := by rwa [← Set.uIcc_of_ge hge]
      have hd' : ∀ t ∈ Ioo α θ₀, HasDerivAt g (g' t) t := fun t ht =>
        hg_deriv t (by rwa [min_eq_right hge, max_eq_left hge])
      have hsymm := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hge hc' hd' hint.symm
      rw [intervalIntegral.integral_symm α θ₀, hsymm]
      ring
  have hmain_cont : Continuous main := by dsimp [main, γ]; fun_prop
  have hrem_cont : ContinuousOn rem (uIcc θ₀ θ₁) := by
    dsimp [rem]
    have hγ_c : Continuous γ := by dsimp [γ]; fun_prop
    have hη_c : ContinuousOn (fun t => η (γ t) s) (uIcc θ₀ θ₁) := fun t _ => by
      have hpair : ((γ t, s) : ℂ × ℂ) ∈ ball (0 : ℂ × ℂ) ρ_F := by
        rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
        exact ⟨mem_ball_zero_iff.mp (hγ_F t), mem_ball_zero_iff.mp hs_F⟩
      have hc_map : Continuous (fun x : ℝ => (γ x, s)) := hγ_c.prodMk continuous_const
      have hc_at : ContinuousAt (Function.uncurry η) (γ t, s) := (hη_an _ hpair).continuousAt
      exact (hc_at.comp_of_eq hc_map.continuousAt rfl).continuousWithinAt
    have hpoly : ContinuousOn (fun t : ℝ => ((γ t) ^ 2 - s ^ 2) * η (γ t) s) (uIcc θ₀ θ₁) :=
      ((hγ_c.pow 2).continuousOn.sub continuousOn_const).mul hη_c
    exact ((continuousOn_const.mul (continuousOn_const.add hpoly))).mul (by fun_prop)
  have hrem_int : IntervalIntegrable rem volume θ₀ α := (hrem_cont.mono hu_sub).intervalIntegrable
  have hmain_int : IntervalIntegrable main volume θ₀ α := hmain_cont.intervalIntegrable θ₀ α
  have hint_split : ∫ t in θ₀..α, g' t = (∫ t in θ₀..α, main t) + ∫ t in θ₀..α, rem t := by
    rw [← intervalIntegral.integral_add hmain_int hrem_int]
    exact intervalIntegral.integral_congr fun t ht => hg'_split (hu_sub ht)
  have hmain_val : (∫ t in θ₀..α, main t).re =
      (Real.pi ^ 2 / 18) * r ^ 3 * (Real.cos (3 * α) - Real.cos (3 * θ₀)) := by
    let P : ℝ → ℂ := fun t => ((Real.pi ^ 2 / 18 : ℝ) : ℂ) * (γ t) ^ 3
    have hP_der : ∀ t : ℝ, HasDerivAt P (main t) t := fun t => by
      dsimp [P, main]
      have h3 := (hγ_deriv t).pow 3
      exact (h3.const_mul ((Real.pi ^ 2 / 18 : ℝ) : ℂ)).congr_deriv (by
        simp only [Nat.cast_ofNat, Nat.reduceSub]; push_cast; ring)
    have h_int := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := θ₀) (b := α)
      (fun t _ => hP_der t) hmain_int
    have hγ3_re : ∀ x : ℝ, ((γ x) ^ 3).re = r ^ 3 * Real.cos (3 * x) := fun x => by
      have heq3 : (γ x) ^ 3 = ((r ^ 3 : ℝ) : ℂ) * Complex.exp (Complex.I * ((3 * x : ℝ) : ℂ)) := by
        dsimp [γ]
        rw [mul_pow, ← Complex.exp_nat_mul]
        congr 2 <;> push_cast <;> ring
      rw [heq3, Complex.re_ofReal_mul, exp_ofReal_mul_I_re']
    have h_re_eq : (∫ t in θ₀..α, main t).re = (P α).re - (P θ₀).re := by
      rw [h_int, Complex.sub_re]
    rw [h_re_eq]
    dsimp [P]
    rw [Complex.mul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, zero_mul, sub_zero, hγ3_re α, hγ3_re θ₀]
    ring
  have hmain_nonpos : (∫ t in θ₀..α, main t).re ≤ 0 := by
    rw [hmain_val]
    have hcos_le : Real.cos (3 * α) - Real.cos (3 * θ₀) ≤ 0 := sub_nonpos.mpr (hcos α hα)
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity [Real.pi_pos]) hcos_le
  have hrem_bd : ∀ t ∈ uIcc θ₀ α,
      ‖rem t‖ ≤ (Real.pi ^ 2 / 6) * r * (‖s‖ ^ 2 + 4 * C_F * r ^ 3) := fun t _ => by
    have hη_b : ‖η (γ t) s‖ ≤ C_F * (r + ‖s‖) := by
      simpa [hγ_norm t] using hη_bd (γ t) (hγ_F t) s hs_F
    have h2r : r + ‖s‖ ≤ 2 * r := by linarith
    have hsq_b : ‖(γ t) ^ 2 - s ^ 2‖ ≤ 2 * r ^ 2 := by
      calc ‖(γ t) ^ 2 - s ^ 2‖ ≤ ‖γ t‖ ^ 2 + ‖s‖ ^ 2 :=
            (norm_sub_le ((γ t) ^ 2) (s ^ 2)).trans_eq (by rw [norm_pow, norm_pow])
        _ = r ^ 2 + ‖s‖ ^ 2 := by rw [hγ_norm t]
        _ ≤ r ^ 2 + r ^ 2 := by gcongr
        _ = 2 * r ^ 2 := by ring
    have hinner : ‖-s ^ 2 + ((γ t) ^ 2 - s ^ 2) * η (γ t) s‖ ≤ ‖s‖ ^ 2 + 4 * C_F * r ^ 3 := by
      calc ‖-s ^ 2 + ((γ t) ^ 2 - s ^ 2) * η (γ t) s‖
          ≤ ‖s‖ ^ 2 + ‖(γ t) ^ 2 - s ^ 2‖ * ‖η (γ t) s‖ :=
            (norm_add_le (-s ^ 2) (((γ t) ^ 2 - s ^ 2) * η (γ t) s)).trans_eq
              (by rw [norm_neg, norm_pow, norm_mul])
        _ ≤ ‖s‖ ^ 2 + (2 * r ^ 2) * (C_F * (2 * r)) := by
            gcongr; exact hη_b.trans (mul_le_mul_of_nonneg_left h2r hCF_nn)
        _ = ‖s‖ ^ 2 + 4 * C_F * r ^ 3 := by ring
    dsimp [rem]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity [Real.pi_pos]),
      norm_mul, Complex.norm_I, one_mul, hγ_norm t]
    calc (Real.pi ^ 2 / 6) * ‖-s ^ 2 + ((γ t) ^ 2 - s ^ 2) * η (γ t) s‖ * r
        ≤ (Real.pi ^ 2 / 6) * (‖s‖ ^ 2 + 4 * C_F * r ^ 3) * r := by gcongr
      _ = (Real.pi ^ 2 / 6) * r * (‖s‖ ^ 2 + 4 * C_F * r ^ 3) := by ring
  have hlen_le : |α - θ₀| ≤ Real.pi / 2 := by
    rw [Set.mem_uIcc] at hα
    rcases hα with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hle : θ₁ - θ₀ ≥ 0 := by linarith
      rw [abs_of_nonneg (by linarith : α - θ₀ ≥ 0)]
      exact (by linarith : α - θ₀ ≤ θ₁ - θ₀).trans ((le_abs_self _).trans hθ_diff)
    · rw [abs_of_nonpos (by linarith : α - θ₀ ≤ 0), neg_sub]
      have hge : θ₁ - θ₀ ≤ 0 := by linarith
      exact (by linarith : θ₀ - α ≤ θ₀ - θ₁).trans
        (by rw [show θ₀ - θ₁ = -(θ₁ - θ₀) by ring, ← abs_of_nonpos hge]; exact hθ_diff)
  have hrem_int_bd : (∫ t in θ₀..α, rem t).re ≤
      (Real.pi ^ 2 / 6) * (Real.pi / 2) * r * (‖s‖ ^ 2 + 4 * C_F * r ^ 3) := by
    have h1 := Complex.re_le_norm (∫ t in θ₀..α, rem t)
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (C := (Real.pi ^ 2 / 6) * r * (‖s‖ ^ 2 + 4 * C_F * r ^ 3))
      fun t ht => hrem_bd t (by simpa [Set.mem_uIoc] using (Set.mem_uIoc.mp ht |> fun h =>
        h.elim (fun h' => Set.mem_uIcc.mpr (Or.inl ⟨h'.1.le, h'.2⟩))
          (fun h' => Set.mem_uIcc.mpr (Or.inr ⟨h'.1.le, h'.2⟩))))
    exact ((h1.trans h2).trans
      (mul_le_mul_of_nonneg_left hlen_le (by positivity [Real.pi_pos]))).trans_eq (by ring)
  change (chartPhiV w b).re - (chartPhiV w₀ b).re ≤ _
  have hsub_eq : (chartPhiV w b).re - (chartPhiV w₀ b).re =
      (∫ t in θ₀..α, main t).re + (∫ t in θ₀..α, rem t).re := by
    rw [← Complex.sub_re, hftc, hint_split, Complex.add_re]
  linarith [hsub_eq, hmain_nonpos, hrem_int_bd]

/-- Radial segment `H` monotonicity along `r ↦ r * exp(i σ π/3)` (`σ = ±1`) for
`(A₀ - 1) ρ ≤ r ≤ δ` when `A₀ ≥ 5` and `δ` is small. -/
lemma radial_H_antitone {η : ℂ → ℂ → ℂ} {ρ_F C_F : ℝ}
    (hCF_nn : 0 ≤ C_F)
    (_hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    (hη_bd : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      ‖η w s‖ ≤ C_F * (‖w‖ + ‖s‖))
    {s b : ℂ} (hb_re : 0 < b.re) (hb_eq : b = chartB s) (hs_F : s ∈ ball (0 : ℂ) ρ_F)
    {σ r₁ δ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hr₁_pos : 0 < r₁) (hr₁_le : r₁ ≤ δ)
    (hδ_lt : δ < min ρ_F (1 / 2))
    (h_rho_le : ‖s‖ ≤ r₁ / 4)
    (h_eta_small : C_F * (5 / 4 * δ) * (1 + 1 / 16) ≤ 1 / 4) :
    AntitoneOn (fun r : ℝ => (chartPhiV ((r : ℂ) * Complex.exp (Complex.I * ((σ * Real.pi / 3 : ℝ) : ℂ))) b).re)
      (Icc r₁ δ) := by
  let dir : ℂ := Complex.exp (Complex.I * ((σ * Real.pi / 3 : ℝ) : ℂ))
  have hdir_re : dir.re = 1 / 2 := by
    dsimp [dir]; rw [exp_ofReal_mul_I_re']
    rcases hσ with rfl | rfl
    · simp [Real.cos_pi_div_three]
    · rw [show (-1 * Real.pi / 3 : ℝ) = -(Real.pi / 3) by ring, Real.cos_neg, Real.cos_pi_div_three]
  have hdir_norm : ‖dir‖ = 1 := exp_ofReal_mul_I_norm _
  have hdir3 : dir ^ 3 = -1 := by
    dsimp [dir]; rw [← Complex.exp_nat_mul]
    rcases hσ with rfl | rfl
    · have : (3 : ℕ) * (Complex.I * ((1 * Real.pi / 3 : ℝ) : ℂ)) = (Real.pi : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.exp_pi_mul_I]
    · have : (3 : ℕ) * (Complex.I * ((-1 * Real.pi / 3 : ℝ) : ℂ)) = -((Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  let f : ℝ → ℂ := fun r => chartPhiV ((r : ℂ) * dir) b
  let f' : ℝ → ℂ := fun r =>
    ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (-(r ^ 2 : ℂ) - s ^ 2 * dir + (((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir)
  have hf_mem : ∀ r ∈ Icc r₁ δ, ((r : ℂ) * dir) ∈ ball (0 : ℂ) ρ_F ∧
      0 ≤ ((r : ℂ) * dir).re ∧ ((r : ℂ) * dir).re ≤ 1 / 4 := fun r hr => by
    have hr_nn : 0 ≤ r := hr₁_pos.le.trans hr.1
    have hnorm : ‖(r : ℂ) * dir‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_nn, hdir_norm, mul_one]
    have hre : ((r : ℂ) * dir).re = r / 2 := by
      rw [Complex.re_ofReal_mul, hdir_re]; ring
    refine ⟨mem_ball_zero_iff.mpr (hnorm.symm ▸ hr.2.trans_lt (hδ_lt.trans_le (min_le_left _ _))),
      by linarith, ?_⟩
    have hδ_12 : δ ≤ 1 / 2 := hδ_lt.le.trans (min_le_right _ _)
    linarith [hr.2]
  have hf_deriv : ∀ r ∈ Icc r₁ δ, HasDerivWithinAt f (f' r) (Icc r₁ δ) r := fun r hr => by
    have hm_r := hf_mem r hr
    have hne : (r : ℂ) * dir ≠ 1 / 2 := fun h0 => by
      have := congrArg Complex.re h0; simp only [Complex.one_re, Complex.div_ofNat_re] at this; linarith [hm_r.2.2]
    have hd := (lemma_S5_deriv hb_re).2.2 _ hm_r.2.1 (hm_r.2.2.trans (by norm_num)) hne
    have hlin : HasDerivWithinAt (fun x : ℝ => (x : ℂ) * dir) dir (Icc r₁ δ) r := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const dir).hasDerivWithinAt
    have hm : MapsTo (fun x : ℝ => (x : ℂ) * dir) (Icc r₁ δ) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2} :=
      fun x hx => ⟨(hf_mem x hx).2.1, (hf_mem x hx).2.2.trans (by norm_num)⟩
    refine (hd.comp r hlin hm).congr_deriv ?_
    rw [hb_eq, hF_id _ hm_r.1 s hs_F]
    dsimp [f']
    calc ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (((r : ℂ) * dir) ^ 2 - s ^ 2) * (1 + η ((r : ℂ) * dir) s) * dir
        = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((r : ℂ) ^ 2 * dir ^ 3 - s ^ 2 * dir +
            (((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir) := by ring
      _ = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (-(r ^ 2 : ℂ) - s ^ 2 * dir +
            (((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir) := by
          rw [hdir3]; ring_nf
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc r₁ δ)
    (fun r hr => (Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt r (hf_deriv r hr)).continuousWithinAt)
    (fun r hr => ((Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt r
      (hf_deriv r (interior_subset hr))).mono interior_subset))
    (fun r hr => ?_)
  have hr_icc : r ∈ Icc r₁ δ := interior_subset hr
  have hr_pos : 0 < r := lt_of_lt_of_le hr₁_pos hr_icc.1
  have hs_le_r : ‖s‖ ≤ r / 4 := h_rho_le.trans (by linarith [hr_icc.1])
  have hη_b : ‖η ((r : ℂ) * dir) s‖ ≤ C_F * (5 / 4 * δ) := by
    have h1 := hη_bd _ (hf_mem r hr_icc).1 s hs_F
    have hnr : ‖(r : ℂ) * dir‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_pos.le, hdir_norm, mul_one]
    exact h1.trans (mul_le_mul_of_nonneg_left (by linarith [hr_icc.2]) hCF_nn)
  have hre_bd : (f' r).re ≤ (Real.pi ^ 2 / 6) * (-(r ^ 2) + ‖s‖ ^ 2 + (r ^ 2 + ‖s‖ ^ 2) * ‖η ((r : ℂ) * dir) s‖) := by
    have hrem_norm : ‖-s ^ 2 * dir + (((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir‖ ≤
        ‖s‖ ^ 2 + (r ^ 2 + ‖s‖ ^ 2) * ‖η ((r : ℂ) * dir) s‖ := by
      calc ‖-s ^ 2 * dir + (((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir‖
          ≤ ‖-s ^ 2 * dir‖ + ‖(((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir‖ := norm_add_le _ _
        _ ≤ ‖s‖ ^ 2 + (r ^ 2 + ‖s‖ ^ 2) * ‖η ((r : ℂ) * dir) s‖ := by
            gcongr
            · rw [norm_mul, norm_neg, norm_pow, hdir_norm, mul_one]
            · rw [norm_mul, norm_mul, hdir_norm, mul_one]
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              calc ‖((r : ℂ) * dir) ^ 2 - s ^ 2‖
                  ≤ ‖((r : ℂ) * dir) ^ 2‖ + ‖s ^ 2‖ := norm_sub_le _ _
                _ = r ^ 2 + ‖s‖ ^ 2 := by
                    rw [norm_pow, norm_pow, norm_mul, Complex.norm_real,
                      Real.norm_of_nonneg hr_pos.le, hdir_norm, mul_one]
    dsimp [f']
    rw [Complex.re_ofReal_mul]
    have hrew : -((r : ℂ) ^ 2) - s ^ 2 * dir + (((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir =
        ((-(r ^ 2) : ℝ) : ℂ) + (-s ^ 2 * dir + (((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir) := by
      push_cast; ring
    have hsplit_re : (-((r : ℂ) ^ 2) - s ^ 2 * dir + (((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir).re =
        -(r ^ 2) + (-s ^ 2 * dir + (((r : ℂ) * dir) ^ 2 - s ^ 2) * η ((r : ℂ) * dir) s * dir).re := by
      rw [hrew, Complex.add_re, Complex.ofReal_re]
    rw [hsplit_re]
    have hre1 := (Complex.re_le_norm _).trans hrem_norm
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity [Real.pi_pos])
  have hs_sq_le : ‖s‖ ^ 2 ≤ r ^ 2 / 16 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hs_le_r 2
    linarith
  have hmain_neg : -(r ^ 2) + ‖s‖ ^ 2 + (r ^ 2 + ‖s‖ ^ 2) * ‖η ((r : ℂ) * dir) s‖ ≤ 0 := by
    have hprod : (r ^ 2 + ‖s‖ ^ 2) * ‖η ((r : ℂ) * dir) s‖ ≤ (1 + 1 / 16) * r ^ 2 * (C_F * (5 / 4 * δ)) := by
      have h1 : r ^ 2 + ‖s‖ ^ 2 ≤ (1 + 1 / 16) * r ^ 2 := by linarith
      exact mul_le_mul h1 hη_b (norm_nonneg _) (by positivity)
    nlinarith [sq_nonneg r, mul_le_mul_of_nonneg_left h_eta_small (sq_nonneg r)]
  have heq_apply : (Complex.reCLM (f' r)) = (f' r).re := rfl
  rw [heq_apply]
  exact hre_bd.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity [Real.pi_pos]) hmain_neg)

end FormalResearch.ModularBootstrap.Contour
