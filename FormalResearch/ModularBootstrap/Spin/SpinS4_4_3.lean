/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_3_Box
public import FormalResearch.ModularBootstrap.Spin.SpinS4_3_3
public import FormalResearch.ModularBootstrap.Blowup.PropositionT

/-!
# SPIN-S4 Theorem `s4:4.3` (Global Non-Vanishing and Restricted Observability)

Proves **`spinS4_4_3 : SpinS4_4_3`** (`spinning_s4.tex`, Theorem 4.3) by contradiction via the
adaptive selector `χ_k` on the box `[-R, R] × [-V, V]`, Lemma 4.2 (`spinS4_4_2`) + Montel exhaustion
(`montel_exhaustion_entire`), and the calibrated exterior lower bound on `J = [aJ, bJ]`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real

private lemma spinS4_4_3_norm_pt
    {c V x₁ h₀ : ℝ} (hc49 : 49 ≤ c) (hV_pos : 0 < V) (hh₀_pos : 0 < h₀)
    (hh₀_bd : ∀ b ∈ Icc (xiStar / 2) (2 * xiStar), ∀ d ∈ Icc (-(xiStar / 4)) (xiStar / 4),
      h₀ ≤ spinHbCalReal b d)
    (hV_eps : V * Real.sqrt ((c - 1) ^ (-(2 / 3 : ℝ))) ≤ xiStar / 4)
    {Φ : ℝ × ℝ → ℝ} (hS : SpinSlackHyp c x₁ Φ)
    (N : ℕ) {χ : ℝ → ℝ} (hχ_m : Measurable χ)
    (hχ_b : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1) (hχ_s : ∀ v, V < |v| → χ v = 0)
    {u : ℝ} (hb_ge_x1 : x₁ ≤ xiStar + (c - 1) ^ (-(2 / 3 : ℝ)) * u)
    (hb_mem : xiStar + (c - 1) ^ (-(2 / 3 : ℝ)) * u ∈ Icc (xiStar / 2) (2 * xiStar)) :
    let n := c - 1
    let a := n / 12
    let ε := n ^ (-(2 / 3 : ℝ))
    let W := V * Real.sqrt ε
    let b := xiStar + ε * u
    ‖spinHProfile c N Φ χ (u : ℂ)‖ ≤
      (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * spinFProfile c Φ u +
        (ε * a * Real.exp (n * (2 * π / 3) * b) *
          ∫ d in Icc (-W) W, |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)|) := by
  intro n a ε W b
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  have hGc : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG; exact hS.2.1.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))
  obtain ⟨htr_int, hH_im, hH_re⟩ := spinHProfile_ofReal_eq hc49 hV_pos N hS.2.1 hχ_m hχ_b hχ_s u
  have hre_norm : ‖spinHProfile c N Φ χ (u : ℂ)‖ = |(spinHProfile c N Φ χ (u : ℂ)).re| := by
    rw [← Complex.re_add_im (spinHProfile c N Φ χ (u : ℂ)), hH_im]
    simp
  rw [hre_norm, hH_re]
  have hG_ge0 : ∀ d : ℝ, 0 ≤ spinG a Φ (b + d) (b - d) := fun d =>
    hS.2.2.2.2 b d (by
      have : x₁ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hS.1 hb_ge_x1 2
      linarith [sq_nonneg d])
  have hpair_b : Continuous (fun d : ℝ => (b + d, b - d)) :=
    (continuous_const.add continuous_id).prodMk (continuous_const.sub continuous_id)
  have hG_m : Measurable (fun d : ℝ => spinG a Φ (b + d) (b - d)) :=
    (hGc.comp hpair_b).measurable
  have hχG_dom : IntegrableOn (fun d : ℝ => spinG a Φ (b + d) (b - d)) (Icc (-W) W) :=
    (hGc.comp hpair_b).continuousOn.integrableOn_Icc
  have hχG_int : Integrable (fun d : ℝ => χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d)) := by
    refine (hχG_dom.integrable_indicator measurableSet_Icc).mono
      ((hχ_m.comp (measurable_id.div_const _)).mul hG_m).aestronglyMeasurable
      (Eventually.of_forall fun d => ?_)
    by_cases hd : d ∈ Icc (-W) W
    · rw [Set.indicator_of_mem hd, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (abs_le.mpr ⟨by linarith [(hχ_b (d / Real.sqrt ε)).1], (hχ_b (d / Real.sqrt ε)).2⟩)
    · have hnotv := lt_div_sqrt_of_notMem_Icc hV_pos.le hε_pos hd
      rw [Set.indicator_of_notMem hd, hχ_s _ hnotv, zero_mul, norm_zero]
  have htr_abs : |∫ d : ℝ, χ (d / Real.sqrt ε) * spinTruncInv a N Φ (b + d) (b - d)| ≤
      (∫ d : ℝ, χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d)) +
      ∫ d in Icc (-W) W, |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)| := by
    have hdiff_abs : |∫ d : ℝ, χ (d / Real.sqrt ε) * spinTruncInv a N Φ (b + d) (b - d) -
        χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d)| ≤
        ∫ d in Icc (-W) W, |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)| := by
      refine (abs_integral_le_integral_abs).trans ?_
      have hint_w : IntegrableOn (fun d : ℝ => |spinG a Φ (b + d) (b - d) -
          spinTruncInv a N Φ (b + d) (b - d)|) (Icc (-W) W) := by
        have hsub_b : Continuous (fun d : ℝ => spinG a Φ (b + d) (b - d) -
            spinTruncInv a N Φ (b + d) (b - d)) := by
          change Continuous ((fun q : ℝ × ℝ => spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2) ∘
            fun d : ℝ => (b + d, b - d))
          exact (hGc.sub (continuous_spinTruncInv_s4_3 hS.2.1 N)).comp hpair_b
        exact hsub_b.abs.continuousOn.integrableOn_Icc
      rw [← integral_indicator measurableSet_Icc]
      refine integral_mono (htr_int.sub hχG_int).abs (hint_w.integrable_indicator measurableSet_Icc) fun d => ?_
      by_cases hd : d ∈ Icc (-W) W
      · rw [Set.indicator_of_mem hd, ← mul_sub, abs_mul,
          abs_of_nonneg (hχ_b _).1, abs_sub_comm]
        exact mul_le_of_le_one_left (abs_nonneg _) (hχ_b _).2
      · have hnotv := lt_div_sqrt_of_notMem_Icc hV_pos.le hε_pos hd
        rw [Set.indicator_of_notMem hd, hχ_s _ hnotv, zero_mul, zero_mul, sub_zero, abs_zero]
    have hG_nn_int : 0 ≤ ∫ d : ℝ, χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d) :=
      integral_nonneg fun d => mul_nonneg (hχ_b _).1 (hG_ge0 d)
    have hsub_id : ∫ d : ℝ, χ (d / Real.sqrt ε) * spinTruncInv a N Φ (b + d) (b - d) -
        χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d) =
        (∫ d : ℝ, χ (d / Real.sqrt ε) * spinTruncInv a N Φ (b + d) (b - d)) -
          ∫ d : ℝ, χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d) :=
      integral_sub htr_int hχG_int
    have htri := abs_le.mp hdiff_abs
    rw [hsub_id] at htri
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hG_comp : ∫ d : ℝ, χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d) ≤
      (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (spinGcal a Φ (b : ℂ)).re := by
    rw [spinGcal_re_ofReal ha0.le hS.2.1 b]
    have hG_abs_bd : ∀ xL xR : ℝ, |spinG a Φ xL xR| ≤ ∫ p : ℝ × ℝ, |Φ p| := fun xL xR => by
      have hcos := spinG_eq_cosine_integral ha0.le hS.2.1 xL xR
      have hnorm : ‖((spinG a Φ xL xR : ℝ) : ℂ)‖ = |spinG a Φ xL xR| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [← hnorm, hcos, norm_neg]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hcos_pt : ∀ p : ℝ × ℝ,
          ‖(Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
            Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ))‖ ≤ |Φ p| := fun p => by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          show 4 * ↑π * ↑(Real.sqrt a) * ↑p.1 * ↑xL =
            ((4 * π * Real.sqrt a * p.1 * xL : ℝ) : ℂ) by push_cast; rfl,
          show 4 * ↑π * ↑(Real.sqrt a) * ↑p.2 * ↑xR =
            ((4 * π * Real.sqrt a * p.2 * xR : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cos, ← Complex.ofReal_cos, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (mul_nonneg (abs_nonneg (Φ p)) (abs_nonneg _))
          (Real.abs_cos_le_one _)).trans
          (mul_le_of_le_one_right (abs_nonneg (Φ p)) (Real.abs_cos_le_one _))
      refine integral_mono ?_ hS.2.1.int.norm fun p => ?_
      · refine hS.2.1.int.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
        · have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) :=
            Complex.continuous_ofReal.comp hS.2.1.cont
          have hc1 : Continuous (fun p : ℝ × ℝ =>
              Complex.cos (4 * ↑π * ↑(Real.sqrt a) * ↑p.1 * ↑xL)) :=
            Complex.continuous_cos.comp (by fun_prop)
          have hc2 : Continuous (fun p : ℝ × ℝ =>
              Complex.cos (4 * ↑π * ↑(Real.sqrt a) * ↑p.2 * ↑xR)) :=
            Complex.continuous_cos.comp (by fun_prop)
          exact ((h1.mul hc1).mul hc2).norm.aestronglyMeasurable
        · rw [norm_norm]
          exact hcos_pt p
      · exact hcos_pt p
    let C_G : ℝ := ∫ p : ℝ × ℝ, |Φ p|
    have hCG_nn : 0 ≤ C_G := integral_nonneg fun _ => abs_nonneg _
    have hadj_d : Integrable (fun d : ℝ => spinHbCalReal b d * spinG a Φ (b + d) (b - d)) := by
      have hsig_pos : 0 < spinSigma0 := by unfold spinSigma0; positivity
      have hexp_int : Integrable (fun d : ℝ => Real.exp (-((spinSigma0 ^ 2)⁻¹ * d ^ 2))) := by
        simpa [neg_mul] using integrable_exp_neg_mul_sq (inv_pos.mpr (sq_pos_of_pos hsig_pos))
      let C_hb : ℝ := (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * spinCalFac b * C_G
      have hC_hb : 0 ≤ C_hb := by
        have hcf : 0 ≤ spinCalFac b := by unfold spinCalFac; exact (Real.exp_pos _).le
        have hxs : 0 < Real.tanh (xiStar / 2) := spinTanh_pos (half_pos xiStar_pos)
        dsimp [C_hb]
        exact mul_nonneg (mul_nonneg (div_nonneg (add_nonneg zero_le_one (sq_nonneg _))
          (pow_nonneg hxs.le 4)) hcf) hCG_nn
      refine (hexp_int.const_mul C_hb).mono' ?_ (Eventually.of_forall fun d => ?_)
      · have hhb : Continuous (spinHbCalReal b) := by
          unfold spinHbCalReal
          have hth : Continuous Real.tanh := by
            have heq : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
              funext Real.tanh_eq_sinh_div_cosh
            rw [heq]
            exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'
          have h2 : Continuous (fun d : ℝ => Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) :=
            ((hth.comp ((continuous_const.add continuous_id).div_const 2)).pow 2).mul
              ((hth.comp ((continuous_const.sub continuous_id).div_const 2)).pow 2)
          exact (((continuous_const.mul h2).div_const (Real.tanh (xiStar / 2) ^ 4)).mul
            (Real.continuous_exp.comp (((continuous_id.pow 2).div_const (spinSigma0 ^ 2)).neg))).mul
            continuous_const
        exact (hhb.mul (hGc.comp hpair_b)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (spinHbCalReal_nonneg b d)]
        have hhb_eq : spinHbCalReal b d =
            ((1 + xiStar ^ 2) / (1 + b ^ 2) *
              (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) /
              Real.tanh (xiStar / 2) ^ 4) *
              Real.exp (-((spinSigma0 ^ 2)⁻¹ * d ^ 2)) * spinCalFac b := by
          unfold spinHbCalReal
          rw [show -(d ^ 2 / spinSigma0 ^ 2) = -((spinSigma0 ^ 2)⁻¹ * d ^ 2) by ring]
        have hpre_le : (1 + xiStar ^ 2) / (1 + b ^ 2) *
            (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) /
            Real.tanh (xiStar / 2) ^ 4 ≤ (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 := by
          have h1 : (1 + xiStar ^ 2) / (1 + b ^ 2) ≤ 1 + xiStar ^ 2 :=
            div_le_self (by positivity) (by linarith [sq_nonneg b])
          have ht_sq : ∀ x : ℝ, Real.tanh x ^ 2 ≤ 1 := fun x => by
            rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_le_one (sq_pos_of_pos (Real.cosh_pos x))]
            nlinarith [Real.cosh_sq_sub_sinh_sq x]
          have ht_prod : Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2 ≤ 1 :=
            (mul_le_of_le_one_right (sq_nonneg _) (ht_sq _)).trans (ht_sq _)
          have hmul : (1 + xiStar ^ 2) / (1 + b ^ 2) *
              (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) ≤ 1 + xiStar ^ 2 :=
            (mul_le_of_le_one_right (by positivity) ht_prod).trans h1
          exact div_le_div_of_nonneg_right hmul (by positivity)
        have hcf : 0 ≤ spinCalFac b := by unfold spinCalFac; exact (Real.exp_pos _).le
        have hhb_bd : spinHbCalReal b d ≤ ((1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * spinCalFac b) *
            Real.exp (-((spinSigma0 ^ 2)⁻¹ * d ^ 2)) := by
          rw [hhb_eq]
          have hmul1 : ((1 + xiStar ^ 2) / (1 + b ^ 2) *
              (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) /
              Real.tanh (xiStar / 2) ^ 4) * Real.exp (-((spinSigma0 ^ 2)⁻¹ * d ^ 2)) ≤
              ((1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4) * Real.exp (-((spinSigma0 ^ 2)⁻¹ * d ^ 2)) :=
            mul_le_mul_of_nonneg_right hpre_le (Real.exp_pos _).le
          calc _ ≤ ((1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4) *
                  Real.exp (-((spinSigma0 ^ 2)⁻¹ * d ^ 2)) * spinCalFac b :=
                mul_le_mul_of_nonneg_right hmul1 hcf
            _ = _ := by ring
        have hg_bd := hG_abs_bd (b + d) (b - d)
        calc spinHbCalReal b d * |spinG a Φ (b + d) (b - d)|
            ≤ (((1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * spinCalFac b) *
                Real.exp (-((spinSigma0 ^ 2)⁻¹ * d ^ 2))) * C_G :=
              mul_le_mul hhb_bd hg_bd (abs_nonneg _) (mul_nonneg (by positivity) (Real.exp_pos _).le)
          _ = C_hb * Real.exp (-((spinSigma0 ^ 2)⁻¹ * d ^ 2)) := by dsimp [C_hb]; ring
    have hpt_d : ∀ d : ℝ, χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d) ≤
        h₀⁻¹ * (spinHbCalReal b d * spinG a Φ (b + d) (b - d)) := fun d => by
      by_cases hd : d ∈ Icc (-W) W
      · have hd_mem : d ∈ Icc (-(xiStar / 4)) (xiStar / 4) :=
          ⟨by linarith [hd.1, hV_eps], by linarith [hd.2, hV_eps]⟩
        have hlo_d := hh₀_bd b hb_mem d hd_mem
        have hχ1 : χ (d / Real.sqrt ε) ≤ 1 := (hχ_b _).2
        have hg0 := hG_ge0 d
        calc χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d)
            ≤ 1 * spinG a Φ (b + d) (b - d) := mul_le_mul_of_nonneg_right hχ1 hg0
          _ = h₀⁻¹ * (h₀ * spinG a Φ (b + d) (b - d)) := by
              rw [one_mul, ← mul_assoc, inv_mul_cancel₀ hh₀_pos.ne', one_mul]
          _ ≤ h₀⁻¹ * (spinHbCalReal b d * spinG a Φ (b + d) (b - d)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlo_d hg0) (inv_pos.mpr hh₀_pos).le
      · have hnotv := lt_div_sqrt_of_notMem_Icc hV_pos.le hε_pos hd
        rw [hχ_s _ hnotv, zero_mul]
        exact mul_nonneg (inv_pos.mpr hh₀_pos).le (mul_nonneg (spinHbCalReal_nonneg b d) (hG_ge0 d))
    have hint_le := integral_mono hχG_int (hadj_d.const_mul h₀⁻¹) hpt_d
    rw [integral_const_mul] at hint_le
    have hC_F : 0 < 4 * spinCalF xiStar ^ 2 := mul_pos (by norm_num) (pow_pos (spinCalF_pos' xiStar_pos) 2)
    have hmul_c : h₀⁻¹ * ∫ d : ℝ, spinHbCalReal b d * spinG a Φ (b + d) (b - d) =
        (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (4 * spinCalF xiStar ^ 2 *
          ∫ d : ℝ, spinHbCalReal b d * spinG a Φ (b + d) (b - d)) := by
      field_simp [hh₀_pos.ne', (spinCalF_pos' xiStar_pos).ne']
    exact hint_le.trans_eq hmul_c
  have hcoef_nn : 0 ≤ ε * a * Real.exp (n * (2 * π / 3) * b) := by positivity
  have hb_nn : 0 ≤ b := by linarith [hb_mem.1, xiStar_pos]
  have hL_eq : spinL b = (2 * π / 3) * b := by
    unfold spinL; rw [abs_of_nonneg hb_nn]; ring
  have hF_eq : spinFProfile c Φ u =
      ε * a * Real.exp (n * (2 * π / 3) * b) * (spinGcal a Φ (b : ℂ)).re := by
    unfold spinFProfile
    change a * ε * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re = _
    rw [hL_eq, ← mul_assoc]; ring
  calc |ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
          ∫ d : ℝ, χ (d / Real.sqrt ε) * spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)|
      = (ε * a * Real.exp (n * (2 * π / 3) * b)) *
          |∫ d : ℝ, χ (d / Real.sqrt ε) * spinTruncInv a N Φ (b + d) (b - d)| := by
          rw [abs_mul, abs_of_nonneg hcoef_nn]
    _ ≤ (ε * a * Real.exp (n * (2 * π / 3) * b)) *
          ((∫ d : ℝ, χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d)) +
            ∫ d in Icc (-W) W, |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)|) :=
        mul_le_mul_of_nonneg_left htr_abs hcoef_nn
    _ ≤ (ε * a * Real.exp (n * (2 * π / 3) * b)) *
          ((4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (spinGcal a Φ (b : ℂ)).re +
            ∫ d in Icc (-W) W, |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)|) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hG_comp _) hcoef_nn
    _ = _ := by
        rw [mul_add]
        congr 1
        rw [hF_eq]
        ring

private lemma spinS4_4_3_montel_contra
    {V R M aJ bJ cFc C_r h₀ : ℝ}
    (hV_pos : 0 < V) (hR_pos : 0 < R) (hM_pos : 0 < M)
    (hab : aJ < bJ) (haJ_M : -M ≤ aJ) (hbJ_M : bJ ≤ M)
    {cSeq : ℕ → ℝ} {ΦSeq : ℕ → ℝ × ℝ → ℝ} {uSeq : ℕ → ℝ} {χSeq : ℕ → ℝ → ℝ}
    (hcSeq_ge : ∀ k : ℕ, (k : ℝ) + 50 ≤ cSeq k)
    (hPhi_tc : ∀ k : ℕ, SpinTestClass ((cSeq k - 1) / 12) (ΦSeq k))
    (hPhi_m2 : ∀ k : ℕ, spinM2 ((cSeq k - 1) / 12) (ΦSeq k) = 1)
    (hk_u : ∀ k : ℕ, uSeq k ∈ Icc (-R) R)
    (hk_χ_m : ∀ k : ℕ, Measurable (χSeq k))
    (hk_χ_b : ∀ k : ℕ, ∀ v : ℝ, 0 ≤ χSeq k v ∧ χSeq k v ≤ 1)
    (hk_χ_s : ∀ k : ℕ, ∀ v : ℝ, V < |v| → χSeq k v = 0)
    (hk_neg : ∀ k : ℕ,
      (spinHProfile (cSeq k) (Nat.ceil (Real.log (cSeq k - 1))) (ΦSeq k) (χSeq k) (uSeq k : ℂ)).re ≤
        -(1 / (256 * R)))
    (hk_J : ∀ k : ℕ,
      ∫ u in Icc aJ bJ,
          ‖spinHProfile (cSeq k) (Nat.ceil (Real.log (cSeq k - 1))) (ΦSeq k) (χSeq k) (u : ℂ)‖ ≤
        (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (1 / ((k : ℝ) + 1)) +
          (2 * cFc)⁻¹ * C_r * ((Nat.ceil (Real.log (cSeq k - 1)) : ℝ) + 1) *
            Real.exp (-4 * π * (xiStar / 4) * (Nat.ceil (Real.log (cSeq k - 1)) : ℝ)))
    (h_err_lim : Tendsto (fun c : ℝ =>
      (2 * cFc)⁻¹ * C_r * ((Nat.ceil (Real.log (c - 1)) : ℝ) + 1) *
        Real.exp (-4 * π * (xiStar / 4) * (Nat.ceil (Real.log (c - 1)) : ℝ))) atTop (𝓝 0)) :
    False := by
  let HSeq : ℕ → ℂ → ℂ := fun k =>
    spinHProfile (cSeq k) (Nat.ceil (Real.log (cSeq k - 1))) (ΦSeq k) (χSeq k)
  have hMontel_hol : ∀ R' : ℝ, 0 ≤ R' → ∀ᶠ k in atTop, DifferentiableOn ℂ (HSeq k) (ball 0 R') := by
    intro R' _hR'
    let R'' : ℝ := max R' 1
    have hR''_pos : 0 < R'' := zero_lt_one.trans_le (le_max_right R' 1)
    obtain ⟨_C_RV, c₄₂, _, _, h42⟩ := spinS4_4_2 hV_pos hR''_pos
    refine eventually_atTop.mpr ⟨Nat.ceil c₄₂, fun k hk => ?_⟩
    have hc42 : c₄₂ ≤ cSeq k := by
      have h1 : c₄₂ ≤ (k : ℝ) := (Nat.le_ceil c₄₂).trans (by exact_mod_cast hk)
      linarith only [h1, hcSeq_ge k]
    have hd := (h42 hc42 (hPhi_tc k) (hPhi_m2 k) (hk_χ_m k) (hk_χ_b k) (hk_χ_s k)).1
    exact hd.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (le_max_left R' 1)))
  have hMontel_bdd : ∀ R' : ℝ, 0 ≤ R' → ∃ M' : ℝ, ∀ᶠ k in atTop, ∀ z ∈ ball 0 R', ‖HSeq k z‖ ≤ M' := by
    intro R' _hR'
    let R'' : ℝ := max R' 1
    have hR''_pos : 0 < R'' := zero_lt_one.trans_le (le_max_right R' 1)
    obtain ⟨C_RV, c₄₂, _, _, h42⟩ := spinS4_4_2 hV_pos hR''_pos
    refine ⟨C_RV, eventually_atTop.mpr ⟨Nat.ceil c₄₂, fun k hk z hz => ?_⟩⟩
    have hc42 : c₄₂ ≤ cSeq k := by
      have h1 : c₄₂ ≤ (k : ℝ) := (Nat.le_ceil c₄₂).trans (by exact_mod_cast hk)
      linarith only [h1, hcSeq_ge k]
    have hbd := (h42 hc42 (hPhi_tc k) (hPhi_m2 k) (hk_χ_m k) (hk_χ_b k) (hk_χ_s k)).2
    exact hbd z (closedBall_subset_closedBall (le_max_left R' 1) (ball_subset_closedBall hz))
  obtain ⟨φ, H_lim, hφ_mono, hH_diff, hH_lim⟩ := montel_exhaustion_entire HSeq hMontel_hol hMontel_bdd
  obtain ⟨u₀, _hu₀_mem, ψ, hψ_mono, hu_tend⟩ := isCompact_Icc.tendsto_subseq fun m => hk_u (φ m)
  let τ : ℕ → ℕ := φ ∘ ψ
  have hτ_mono : StrictMono τ := hφ_mono.comp hψ_mono
  have hH_sub_lim : TendstoLocallyUniformlyOn (fun m => HSeq (τ m)) H_lim atTop univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K hK_sub hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε' hε'
    have hu := (Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hH_lim K hK_sub hK)) ε' hε'
    exact hψ_mono.tendsto_atTop.eventually hu
  have hHu₀_val : (H_lim (u₀ : ℂ)).re ≤ -(1 / (256 * R)) := by
    have hK_R : IsCompact (Complex.ofReal '' Icc (-R) R) := isCompact_Icc.image Complex.continuous_ofReal
    have hunif_R := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hH_sub_lim)
      _ (subset_univ _) hK_R
    have h_at_um : Tendsto (fun m => HSeq (τ m) ((uSeq (τ m) : ℂ))) atTop (𝓝 (H_lim (u₀ : ℂ))) := by
      have h1 : Tendsto (fun m => HSeq (τ m) ((uSeq (τ m) : ℂ)) - H_lim ((uSeq (τ m) : ℂ))) atTop (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro ε' hε'
        rw [Metric.tendstoUniformlyOn_iff] at hunif_R
        filter_upwards [hunif_R ε' hε'] with m hm
        have hmem : (uSeq (τ m) : ℂ) ∈ Complex.ofReal '' Icc (-R) R :=
          ⟨uSeq (τ m), hk_u (τ m), rfl⟩
        simpa [dist_eq_norm, norm_sub_rev] using hm (uSeq (τ m) : ℂ) hmem
      have h2 : Tendsto (fun m => H_lim ((uSeq (τ m) : ℂ))) atTop (𝓝 (H_lim (u₀ : ℂ))) :=
        (hH_diff.continuous.comp Complex.continuous_ofReal).continuousAt.tendsto.comp hu_tend
      simpa using h1.add h2
    have hre_tend := Complex.continuous_re.continuousAt.tendsto.comp h_at_um
    exact le_of_tendsto hre_tend (Eventually.of_forall fun m => hk_neg (τ m))
  have hHu₀_ne0 : H_lim (u₀ : ℂ) ≠ 0 := fun h0 => by
    have : (0 : ℝ) ≤ -(1 / (256 * R)) := by simpa [h0] using hHu₀_val
    linarith [hR_pos]
  have hJ_int_zero : ∫ u in Icc aJ bJ, ‖H_lim (u : ℂ)‖ = 0 := by
    have hunif_J : TendstoUniformlyOn (fun m (u : ℝ) => ‖HSeq (τ m) (u : ℂ)‖)
        (fun u : ℝ => ‖H_lim (u : ℂ)‖) atTop (Icc aJ bJ) := by
      have hK_J : IsCompact (Complex.ofReal '' Icc aJ bJ) := isCompact_Icc.image Complex.continuous_ofReal
      have hu := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hH_sub_lim)
        _ (subset_univ _) hK_J
      rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
      intro ε' hε'
      filter_upwards [hu ε' hε'] with m hm u hu_mem
      have hd := hm (u : ℂ) (mem_image_of_mem _ hu_mem)
      rw [Real.dist_eq]
      rw [Complex.dist_eq] at hd
      exact (abs_norm_sub_norm_le (H_lim (u : ℂ)) (HSeq (τ m) (u : ℂ))).trans_lt hd
    have hcont_lim : ContinuousOn (fun u : ℝ => ‖H_lim (u : ℂ)‖) (Icc aJ bJ) :=
      (continuous_norm.comp (hH_diff.continuous.comp Complex.continuous_ofReal)).continuousOn
    have hint_ev : ∀ᶠ m in atTop,
        IntervalIntegrable (fun u : ℝ => ‖HSeq (τ m) (u : ℂ)‖) volume aJ bJ := by
      obtain ⟨_C_RV, c₄₂, _, _, h42⟩ := spinS4_4_2 hV_pos (by linarith only [hM_pos] : 0 < M + 1)
      refine eventually_atTop.mpr ⟨Nat.ceil c₄₂, fun m hm => ?_⟩
      have hτm : Nat.ceil c₄₂ ≤ τ m := hm.trans (hτ_mono.id_le m)
      have hc42 : c₄₂ ≤ cSeq (τ m) := by
        have h1 : c₄₂ ≤ (τ m : ℝ) := (Nat.le_ceil c₄₂).trans (by exact_mod_cast hτm)
        linarith only [h1, hcSeq_ge (τ m)]
      have hdiff := (h42 hc42 (hPhi_tc (τ m)) (hPhi_m2 (τ m))
        (hk_χ_m (τ m)) (hk_χ_b (τ m)) (hk_χ_s (τ m))).1
      have hcont_m : ContinuousOn (fun u : ℝ => ‖HSeq (τ m) (u : ℂ)‖) (Icc aJ bJ) :=
        (hdiff.continuousOn.comp Complex.continuous_ofReal.continuousOn fun u hu => by
          rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
          have huM := Icc_subset_Icc haJ_M hbJ_M hu
          linarith [abs_le.mpr huM]).norm
      exact hcont_m.intervalIntegrable_of_Icc hab.le
    have hlim_int : Tendsto (fun m => ∫ u in aJ..bJ, ‖HSeq (τ m) (u : ℂ)‖) atTop
        (𝓝 (∫ u in aJ..bJ, ‖H_lim (u : ℂ)‖)) :=
      intervalIntegral_tendsto_of_tendstoUniformlyOn hab.le hunif_J hint_ev hcont_lim
    have h_ub_tend : Tendsto (fun m =>
        (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (1 / ((τ m : ℝ) + 1)) +
          (2 * cFc)⁻¹ * C_r * ((Nat.ceil (Real.log (cSeq (τ m) - 1)) : ℝ) + 1) *
            Real.exp (-4 * π * (xiStar / 4) * (Nat.ceil (Real.log (cSeq (τ m) - 1)) : ℝ)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (1 / ((τ m : ℝ) + 1)))
          atTop (𝓝 0) := by
        have ht : Tendsto (fun m : ℕ => ((τ m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop.comp hτ_mono.tendsto_atTop).atTop_add tendsto_const_nhds)
        simpa using ht.const_mul (4 * spinCalF xiStar ^ 2 * h₀)⁻¹
      have h2 : Tendsto (fun m : ℕ => (2 * cFc)⁻¹ * C_r * ((Nat.ceil (Real.log (cSeq (τ m) - 1)) : ℝ) + 1) *
            Real.exp (-4 * π * (xiStar / 4) * (Nat.ceil (Real.log (cSeq (τ m) - 1)) : ℝ)))
          atTop (𝓝 0) := by
        have hc_tend : Tendsto (fun m => cSeq (τ m)) atTop atTop :=
          tendsto_atTop_mono (fun m => hcSeq_ge (τ m))
            ((tendsto_natCast_atTop_atTop.comp hτ_mono.tendsto_atTop).atTop_add tendsto_const_nhds)
        exact h_err_lim.comp hc_tend
      simpa using h1.add h2
    have hle_zero : ∫ u in aJ..bJ, ‖H_lim (u : ℂ)‖ ≤ 0 :=
      le_of_tendsto_of_tendsto hlim_int h_ub_tend (Eventually.of_forall fun m => by
        dsimp only
        rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.restrict_Ioc_eq_restrict_Icc]
        exact hk_J (τ m))
    have hge_zero : 0 ≤ ∫ u in aJ..bJ, ‖H_lim (u : ℂ)‖ := by
      rw [intervalIntegral.integral_of_le hab.le]
      exact setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _
    rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.restrict_Ioc_eq_restrict_Icc] at hle_zero hge_zero
    exact le_antisymm hle_zero hge_zero
  have hH_zero_J : ∀ u ∈ Ioo aJ bJ, H_lim (u : ℂ) = 0 := by
    have hcont_lim : ContinuousOn (fun u : ℝ => ‖H_lim (u : ℂ)‖) (Icc aJ bJ) :=
      (continuous_norm.comp (hH_diff.continuous.comp Complex.continuous_ofReal)).continuousOn
    have h_ae : (fun u : ℝ => ‖H_lim (u : ℂ)‖) =ᵐ[volume.restrict (Icc aJ bJ)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
        hcont_lim.integrableOn_Icc).mp hJ_int_zero
    intro u hu
    by_contra hne
    have hpos : 0 < ‖H_lim (u : ℂ)‖ := norm_pos_iff.mpr hne
    have hcont_at : ContinuousAt (fun t : ℝ => ‖H_lim (t : ℂ)‖) u :=
      (continuous_norm.comp (hH_diff.continuous.comp Complex.continuous_ofReal)).continuousAt
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hcont_at (‖H_lim (u : ℂ)‖ / 2) (half_pos hpos)
    let r : ℝ := min δ (min (u - aJ) (bJ - u))
    have hr_pos : 0 < r := lt_min hδ_pos (lt_min (sub_pos.mpr hu.1) (sub_pos.mpr hu.2))
    have hsub_ball : ball u r ⊆ Icc aJ bJ := fun t ht => by
      have ht' := abs_lt.mp (by simpa [Real.dist_eq] using mem_ball.mp ht)
      exact ⟨by linarith [min_le_right δ (min (u - aJ) (bJ - u)), min_le_left (u - aJ) (bJ - u)],
        by linarith [min_le_right δ (min (u - aJ) (bJ - u)), min_le_right (u - aJ) (bJ - u)]⟩
    have hpos_on : ∀ t ∈ ball u r, ‖H_lim (t : ℂ)‖ ≠ 0 := fun t ht => by
      have h1 : |‖H_lim (t : ℂ)‖ - ‖H_lim (u : ℂ)‖| < ‖H_lim (u : ℂ)‖ / 2 :=
        hδ ((Real.dist_eq t u).trans_lt ((mem_ball.mp ht).trans_le (min_le_left _ _)))
      have h2 := (abs_lt.mp h1).1
      linarith
    have hnull_ball : volume (ball u r) = 0 := by
      have h_ae_sub := ae_restrict_of_ae_restrict_of_subset hsub_ball h_ae
      rw [ae_iff] at h_ae_sub
      have heq : ball u r ⊆ {t : ℝ | ¬ ‖H_lim (t : ℂ)‖ = (0 : ℝ → ℝ) t} ∩ ball u r :=
        fun t ht => ⟨hpos_on t ht, ht⟩
      refine measure_mono_null heq ?_
      rw [← Measure.restrict_apply' measurableSet_ball]
      exact h_ae_sub
    rw [Real.ball_eq_Ioo, Real.volume_Ioo] at hnull_ball
    exact absurd hnull_ball (ENNReal.ofReal_pos.mpr (by linarith only [hr_pos])).ne'
  have hH_an : AnalyticOnNhd ℂ H_lim univ := hH_diff.differentiableOn.analyticOnNhd isOpen_univ
  let uMid : ℝ := (aJ + bJ) / 2
  have hfreq : ∃ᶠ z in 𝓝[≠] (uMid : ℂ), H_lim z = 0 := by
    have htend : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[≠] uMid) (𝓝[≠] (uMid : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun u hu h => hu (Complex.ofReal_inj.mp h))
    have hIoo : Ioo aJ bJ ∈ 𝓝[≠] uMid :=
      nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by dsimp only [uMid]; linarith only [hab],
        by dsimp only [uMid]; linarith only [hab]⟩)
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [hIoo] with u hu
    exact hH_zero_J u hu
  exact hHu₀_ne0
    (hH_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ (uMid : ℂ)) hfreq (mem_univ (u₀ : ℂ)))

private lemma spinS4_4_3_J_lower {C₀ aJ bJ : ℝ} (hC₀ : 0 < C₀) (hCa : C₀ < aJ) (hab : aJ < bJ) :
    ∃ (κ_J c₀ : ℝ), 0 < κ_J ∧ 40 ≤ c₀ ∧
      ∀ {c x₁ : ℝ}, c₀ ≤ c →
        let n := c - 1
        let ε := n ^ (-(2 / 3 : ℝ))
        |x₁ - xiStar| ≤ C₀ * ε →
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinSlackHyp c x₁ Φ →
          κ_J ≤ ∫ u in Icc aJ bJ, spinFProfile c Φ u := by
  by_contra hno
  obtain ⟨C₃₃, c_exp, R₀, hC33_pos, hcexp_pos, hR₀_pos, h33⟩ := spinS4_3_3 (C_x := C₀) hC₀
  have hexp_lim : Tendsto (fun R : ℝ => C₃₃ * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => c_exp * R ^ (3 / 2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul_atTop hcexp_pos
    have h2 : Tendsto (fun R : ℝ => Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
      have : (fun R : ℝ => Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) =
          fun R => Real.exp (-(c_exp * R ^ (3 / 2 : ℝ))) := by
        ext R; congr 1; ring
      rw [this]
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    simpa using h2.const_mul C₃₃
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp (hexp_lim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12)))
  let R : ℝ := max (max R₀ C₀) (max 1 R₁)
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_right _ _))
  have hCR : C₀ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR₀_R : R₀ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have h33_small : C₃₃ * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) ≤ 1 / 12 :=
    (hR₁ R ((le_max_right _ _).trans (le_max_right _ _))).le
  let V : ℝ := Real.sqrt (4 * xiStar * (C₀ + R))
  have hV_pos : 0 < V := Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) xiStar_pos) (by linarith))
  let M : ℝ := max R bJ
  have hM_pos : 0 < M := lt_of_lt_of_le hR_pos (le_max_left _ _)
  obtain ⟨_C_RV_M, c42_M, _, hc42_M_40, h42_M⟩ := spinS4_4_2 hV_pos (by linarith : 0 < M + 1)
  obtain ⟨C_r, _C_V, c₄₁, hCr_pos, _hCV_pos, hc41_40, h41⟩ :=
    spinS4_4_1 (r₀ := xiStar / 4) (V := V) (by positivity [xiStar_pos]) hV_pos
  obtain ⟨h₀, hh₀_pos, hh₀_bd⟩ := spinHbCalReal_pos_lower_near_tip
  obtain ⟨N₃₃, hN₃₃⟩ := eventually_atTop.mp (h33 hR₀_R)
  let cFc : ℝ := (1 - Real.exp (-π * xiStar)) ^ 4
  have hcFc_pos : 0 < cFc := by
    have h1 : Real.exp (-π * xiStar) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, xiStar_pos])
    exact pow_pos (by linarith) 4
  have h_eps_lim : Tendsto (fun c : ℝ => (c - 1) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      (Filter.Tendsto.atTop_add tendsto_id tendsto_const_nhds)
  have h_err_lim : Tendsto (fun c : ℝ =>
      (2 * cFc)⁻¹ * C_r * ((Nat.ceil (Real.log (c - 1)) : ℝ) + 1) *
        Real.exp (-4 * π * (xiStar / 4) * (Nat.ceil (Real.log (c - 1)) : ℝ))) atTop (𝓝 0) := by
    have hlim := exp_decay_ceil_log_tendsto (by nlinarith [Real.pi_gt_three, xiStar_pos] : 0 < π * xiStar)
    have hfun : (fun c : ℝ => (2 * cFc)⁻¹ * C_r * ((Nat.ceil (Real.log (c - 1)) : ℝ) + 1) *
          Real.exp (-4 * π * (xiStar / 4) * (Nat.ceil (Real.log (c - 1)) : ℝ))) =
        fun c : ℝ => ((2 * cFc)⁻¹ * C_r) * (((Nat.ceil (Real.log (c - 1)) : ℝ) + 1) *
          Real.exp (-(π * xiStar) * (Nat.ceil (Real.log (c - 1)) : ℝ))) := by
      ext c; ring_nf
    rw [hfun]
    simpa using hlim.const_mul ((2 * cFc)⁻¹ * C_r)
  obtain ⟨N_M, hNM⟩ := eventually_atTop.mp
    (h_eps_lim.eventually (gt_mem_nhds (div_pos (div_pos xiStar_pos (by norm_num : (0 : ℝ) < 4)) hM_pos)))
  obtain ⟨N_V, hNV⟩ := eventually_atTop.mp
    (h_eps_lim.eventually (gt_mem_nhds
      (div_pos (sq_pos_of_pos (div_pos xiStar_pos (by norm_num : (0 : ℝ) < 4))) (sq_pos_of_pos hV_pos))))
  obtain ⟨N_err, hNerr⟩ := eventually_atTop.mp
    (h_err_lim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64)))
  let c_thr : ℝ := max (max 49 (max c₄₁ c42_M)) (max (max (N₃₃ + 1) N_M) (max N_V N_err))
  have hseq : ∀ k : ℕ, ∃ c x₁ : ℝ, ∃ Φ : ℝ × ℝ → ℝ,
      max c_thr ((k : ℝ) + 50) ≤ c ∧
      |x₁ - xiStar| ≤ C₀ * (c - 1) ^ (-(2 / 3 : ℝ)) ∧
      SpinSlackHyp c x₁ Φ ∧
      ∫ u in Icc aJ bJ, spinFProfile c Φ u < 1 / ((k : ℝ) + 1) := by
    intro k
    by_contra hk
    apply hno
    refine ⟨1 / ((k : ℝ) + 1), max c_thr ((k : ℝ) + 50), by positivity,
      (le_trans (by norm_num : (40 : ℝ) ≤ 49) ((le_max_left _ _).trans (le_max_left _ _))).trans
        (le_max_left _ _), ?_⟩
    intro c x₁ hc n ε hx₁ Φ hS
    by_contra hlt
    exact hk ⟨c, x₁, Φ, hc, hx₁, hS, not_le.mp hlt⟩
  choose cSeq xSeq ΦSeq hSeq_prop using hseq
  -- Setup adaptive slices and Montel normal family
  let uSeq : ℕ → ℝ := fun k => by
    classical
    let c := cSeq k; let x₁ := xSeq k; let Φ := ΦSeq k
    let n := c - 1; let a := n / 12; let ε := n ^ (-(2 / 3 : ℝ)); let N := Nat.ceil (Real.log n)
    let f_m : ℝ → ℝ := fun u =>
      ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
        ∫ d in Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε),
          max (-spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) 0
    let f_e : ℝ → ℝ := fun u =>
      ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
        ∫ d in Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε),
          |spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d) -
            spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)|
    exact if h : ∃ u ∈ Icc (-R) R, 1 / (256 * R) ≤ f_m u - f_e u then h.choose else 0
  let χSeq : ℕ → ℝ → ℝ := fun k =>
    let c := cSeq k; let n := c - 1; let a := n / 12; let ε := n ^ (-(2 / 3 : ℝ))
    (Icc (-V) V).indicator fun v =>
      if spinG a (ΦSeq k) (xiStar + ε * uSeq k + Real.sqrt ε * v)
          (xiStar + ε * uSeq k - Real.sqrt ε * v) < 0 then 1 else 0
  have hk_all : ∀ k : ℕ,
      let c := cSeq k; let x₁ := xSeq k; let Φ := ΦSeq k
      let n := c - 1; let a := n / 12; let ε := n ^ (-(2 / 3 : ℝ)); let N := Nat.ceil (Real.log n)
      let χ := χSeq k
      49 ≤ c ∧ c₄₁ ≤ c ∧
      uSeq k ∈ Icc (-R) R ∧
      Measurable χ ∧ (∀ v, 0 ≤ χ v ∧ χ v ≤ 1) ∧ (∀ v, V < |v| → χ v = 0) ∧
      (spinHProfile c N Φ χ (uSeq k : ℂ)).re ≤ -(1 / (256 * R)) ∧
      ∫ u in Icc aJ bJ, ‖spinHProfile c N Φ χ (u : ℂ)‖ ≤
        (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (1 / ((k : ℝ) + 1)) +
          (2 * cFc)⁻¹ * C_r * ((N : ℝ) + 1) * Real.exp (-4 * π * (xiStar / 4) * (N : ℝ)) := by
    intro k c x₁ Φ n a ε N χ
    obtain ⟨hc_max, hx₁_bd, hS, hF_lt⟩ := hSeq_prop k
    have hc_thr : c_thr ≤ c := (le_max_left _ _).trans hc_max
    have hc49 : 49 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc_thr
    have hc41 : c₄₁ ≤ c :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc_thr
    have hc42_M : c42_M ≤ c :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc_thr
    have hn_ge33 : N₃₃ ≤ n := by
      have h1 : N₃₃ + 1 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans
        ((le_max_right _ _).trans hc_thr)
      dsimp [n]; linarith
    have hc_M : N_M ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans
      ((le_max_right _ _).trans hc_thr)
    have hc_V : N_V ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans
      ((le_max_right _ _).trans hc_thr)
    have hc_err : N_err ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans
      ((le_max_right _ _).trans hc_thr)
    have hn_pos : 0 < n := by dsimp [n]; linarith
    have ha2 : 2 < a := by dsimp [a, n]; linarith
    have ha0 : 0 < a := by linarith
    have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
    have hM_eps : ε * M ≤ xiStar / 4 := by
      have h1 : ε < xiStar / 4 / M := hNM c hc_M
      have h2 := (lt_div_iff₀ hM_pos).mp h1
      linarith
    have hR_eps : ε * R ≤ xiStar / 4 :=
      (mul_le_mul_of_nonneg_left (le_max_left R bJ) hε_pos.le).trans hM_eps
    have hC₀_eps : C₀ * ε ≤ xiStar / 4 :=
      (mul_le_mul_of_nonneg_right hCR hε_pos.le).trans (by linarith [hR_eps])
    have hbJ_eps : ε * bJ ≤ xiStar / 4 :=
      (mul_le_mul_of_nonneg_left (le_max_right R bJ) hε_pos.le).trans hM_eps
    have hV_eps : V * Real.sqrt ε ≤ xiStar / 4 := by
      have h1 : ε < (xiStar / 4) ^ 2 / V ^ 2 := hNV c hc_V
      have h2 : V ^ 2 * ε < (xiStar / 4) ^ 2 := by
        have h3 := (lt_div_iff₀ (sq_pos_of_pos hV_pos)).mp h1; linarith
      have hsq : (V * Real.sqrt ε) ^ 2 < (xiStar / 4) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hε_pos.le]; exact h2
      have hnn : 0 ≤ V * Real.sqrt ε := mul_nonneg hV_pos.le (Real.sqrt_nonneg _)
      nlinarith [xiStar_pos]
    have h33_inst_n := hN₃₃ n hn_ge33 (by simpa [n] using hx₁_bd) (by simpa [n] using hS)
    have hbox_lo := spin_neg_mass_box_lower hC₀ hCR rfl h33_small hc49 hC₀_eps hR_eps hx₁_bd hS
      (by simpa [n] using h33_inst_n)
    have herr_M := spinHProfile_err_integral_le hM_pos hV_pos hc49 N hS.2.1 hM_eps hV_eps
    have h41_err := (h41 hc41 hS.2.1 hS.2.2.1).1
    have herr_M_164 : ∫ u in Icc (-M) M,
        (ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
          ∫ d in Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε),
            |spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d) -
              spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)|) ≤ 1 / 64 := by
      have h1 := herr_M.trans (mul_le_mul_of_nonneg_left h41_err (by positivity))
      have h2 : (2 * cFc)⁻¹ * (C_r * ((N : ℝ) + 1) * Real.exp (-4 * π * (xiStar / 4) * (N : ℝ))) < 1 / 64 := by
        simpa [mul_assoc] using hNerr c hc_err
      linarith
    -- Pick witness `u_k ∈ Icc (-R) R`
    let f_m : ℝ → ℝ := fun u =>
      ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
        ∫ d in Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε),
          max (-spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) 0
    let f_e : ℝ → ℝ := fun u =>
      ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
        ∫ d in Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε),
          |spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d) -
            spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)|
    have hGc : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
      unfold spinG; exact hS.2.1.cont.comp ((continuous_const.mul continuous_fst).prodMk
        (continuous_const.mul continuous_snd))
    let W : ℝ := V * Real.sqrt ε
    have hW_le : -W ≤ W := by linarith [mul_nonneg hV_pos.le (Real.sqrt_nonneg ε)]
    have hfm_cont : Continuous f_m := by
      have hm_u : Continuous (Function.uncurry fun u d : ℝ =>
          max (-spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) 0) :=
        (hGc.comp (((continuous_const.add (continuous_const.mul continuous_fst)).add continuous_snd).prodMk
          ((continuous_const.add (continuous_const.mul continuous_fst)).sub continuous_snd))).neg.max continuous_const
      refine (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).mul ?_
      have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) hm_u (-W) W
      simpa only [intervalIntegral.integral_of_le hW_le, MeasureTheory.restrict_Ioc_eq_restrict_Icc] using hc
    have hfe_cont : Continuous f_e := by
      have hpair_ud : Continuous (fun p : ℝ × ℝ => ((xiStar + ε * p.1) + p.2, (xiStar + ε * p.1) - p.2)) :=
        ((continuous_const.add (continuous_const.mul continuous_fst)).add continuous_snd).prodMk
          ((continuous_const.add (continuous_const.mul continuous_fst)).sub continuous_snd)
      have hsub_tr : Continuous (fun p : ℝ × ℝ =>
          spinG a Φ ((xiStar + ε * p.1) + p.2) ((xiStar + ε * p.1) - p.2) -
            spinTruncInv a N Φ ((xiStar + ε * p.1) + p.2) ((xiStar + ε * p.1) - p.2)) := by
        change Continuous ((fun q : ℝ × ℝ => spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2) ∘
          fun p : ℝ × ℝ => ((xiStar + ε * p.1) + p.2, (xiStar + ε * p.1) - p.2))
        exact (hGc.sub (continuous_spinTruncInv_s4_3 hS.2.1 N)).comp hpair_ud
      have he_u : Continuous (Function.uncurry fun u d : ℝ =>
          |spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d) -
            spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)|) :=
        hsub_tr.abs
      refine (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).mul ?_
      have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) he_u (-W) W
      simpa only [intervalIntegral.integral_of_le hW_le, MeasureTheory.restrict_Ioc_eq_restrict_Icc] using hc
    have herr_R_164 : ∫ u in Icc (-R) R, f_e u ≤ 1 / 64 := by
      have hsub : Icc (-R) R ⊆ Icc (-M) M := Icc_subset_Icc (by linarith [le_max_left R bJ]) (le_max_left R bJ)
      have h1 : ∫ u in Icc (-R) R, f_e u ≤ ∫ u in Icc (-M) M, f_e u :=
        setIntegral_mono_set hfe_cont.continuousOn.integrableOn_Icc (Eventually.of_forall fun u => by
          dsimp [f_e]; exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Icc fun _ _ => abs_nonneg _))
          hsub.eventuallySubset
      exact h1.trans herr_M_164
    have hex_u : ∃ u ∈ Icc (-R) R, 1 / (256 * R) ≤ f_m u - f_e u := by
      by_contra hno_u
      push Not at hno_u
      have hle_int : ∫ u in Icc (-R) R, (f_m u - f_e u) ≤
          ∫ _ in Icc (-R) R, (1 / (256 * R) : ℝ) :=
        setIntegral_mono_on (hfm_cont.sub hfe_cont).continuousOn.integrableOn_Icc
          (integrableOn_const (hs := measure_Icc_lt_top.ne)) measurableSet_Icc fun u hu => (hno_u u hu).le
      have hconst_val : ∫ _ in Icc (-R) R, (1 / (256 * R) : ℝ) = 1 / 128 := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
          smul_eq_mul]
        field_simp [hR_pos.ne']; norm_num
      have hsub_int : ∫ u in Icc (-R) R, (f_m u - f_e u) =
          (∫ u in Icc (-R) R, f_m u) - ∫ u in Icc (-R) R, f_e u :=
        integral_sub hfm_cont.continuousOn.integrableOn_Icc hfe_cont.continuousOn.integrableOn_Icc
      linarith [hbox_lo, herr_R_164, hle_int, hconst_val, hsub_int]
    have hu_spec : uSeq k ∈ Icc (-R) R ∧ 1 / (256 * R) ≤ f_m (uSeq k) - f_e (uSeq k) := by
      dsimp only [uSeq]
      split_ifs with h_if
      · simpa [n, a, ε, N, f_m, f_e, W] using h_if.choose_spec
      · exact absurd (by simpa [n, a, ε, N, f_m, f_e, W] using hex_u) h_if
    have hu_mem : uSeq k ∈ Icc (-R) R := hu_spec.1
    have hu_val : 1 / (256 * R) ≤ f_m (uSeq k) - f_e (uSeq k) := hu_spec.2
    obtain ⟨hχ_m, hχ_b, hχ_s, hH_u⟩ := adaptive_chi_H_lower hc49 hV_pos N hS.2.1 (xiStar + ε * uSeq k)
    have hH_uk : (spinHProfile c N Φ χ (uSeq k : ℂ)).re ≤ -(1 / (256 * R)) := by
      have h1 := hH_u rfl
      change (spinHProfile c N Φ χ (uSeq k : ℂ)).re ≤ -f_m (uSeq k) + f_e (uSeq k) at h1
      linarith
    -- Now bound `∫ u in Icc aJ bJ, ‖spinHProfile c N Φ χ (u : ℂ)‖`
    have hJ_sub : Icc aJ bJ ⊆ Icc (-M) M := Icc_subset_Icc
      (by linarith [hCa, hC₀, le_max_left R bJ]) (le_max_right R bJ)
    have herr_J : ∫ u in Icc aJ bJ, f_e u ≤
        (2 * cFc)⁻¹ * C_r * ((N : ℝ) + 1) * Real.exp (-4 * π * (xiStar / 4) * (N : ℝ)) := by
      have h1 : ∫ u in Icc aJ bJ, f_e u ≤ ∫ u in Icc (-M) M, f_e u :=
        setIntegral_mono_set hfe_cont.continuousOn.integrableOn_Icc (Eventually.of_forall fun u => by
          dsimp [f_e]; exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Icc fun _ _ => abs_nonneg _))
          hJ_sub.eventuallySubset
      have h2 := herr_M.trans (mul_le_mul_of_nonneg_left h41_err (by positivity))
      linarith
    have hnorm_pt : ∀ u ∈ Icc aJ bJ, ‖spinHProfile c N Φ χ (u : ℂ)‖ ≤
        (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * spinFProfile c Φ u + f_e u := fun u hu => by
      have hb_ge_x1 : x₁ ≤ xiStar + ε * u := by
        have h1 : x₁ ≤ xiStar + C₀ * ε := by
          have h := (abs_le.mp hx₁_bd).2
          linarith only [h]
        have h3 : C₀ * ε ≤ ε * u := by nlinarith only [hCa.le.trans hu.1, hε_pos]
        linarith only [h1, h3]
      have hb_mem : xiStar + ε * u ∈ Icc (xiStar / 2) (2 * xiStar) := by
        have huM := hJ_sub hu
        have h3 : -(M * ε) ≤ ε * u := by nlinarith only [huM.1, hε_pos]
        have h4 : ε * u ≤ M * ε := by nlinarith only [huM.2, hε_pos]
        exact ⟨by linarith only [hM_eps, xiStar_pos, h3], by linarith only [hM_eps, xiStar_pos, h4]⟩
      exact spinS4_4_3_norm_pt hc49 hV_pos hh₀_pos hh₀_bd hV_eps hS N hχ_m hχ_b hχ_s
        hb_ge_x1 hb_mem
    have hH_diff_J : DifferentiableOn ℂ (spinHProfile c N Φ χ) (closedBall (0 : ℂ) (M + 1)) :=
      (h42_M hc42_M hS.2.1 hS.2.2.1 hχ_m hχ_b hχ_s).1
    have hH_cont_J : ContinuousOn (fun u : ℝ => ‖spinHProfile c N Φ χ (u : ℂ)‖) (Icc aJ bJ) := by
      have hc1 : ContinuousOn (fun u : ℝ => spinHProfile c N Φ χ (u : ℂ)) (Icc aJ bJ) :=
        hH_diff_J.continuousOn.comp Complex.continuous_ofReal.continuousOn fun u hu => by
          rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
          have huM := hJ_sub hu
          have habs : |u| ≤ M := abs_le.mpr huM
          linarith
      exact hc1.norm
    have hF_int_J : IntegrableOn (spinFProfile c Φ) (Icc aJ bJ) := by
      have hFb_int := integrable_spinCalInt_integrand (by linarith : 40 ≤ c) hS.2.1
      have hlin := (hFb_int.comp_add_left xiStar).comp_mul_left' hε_pos.ne'
      have hF_eq_all : spinFProfile c Φ = fun u =>
          ε * (a * Real.exp (n * spinL (xiStar + ε * u)) *
            (spinGcal a Φ ((xiStar + ε * u : ℝ) : ℂ)).re) := by
        ext u; unfold spinFProfile; dsimp only [n, a, ε]; ring
      rw [hF_eq_all]
      exact (hlin.const_mul ε).integrableOn
    have h_int_mono : ∫ u in Icc aJ bJ, ‖spinHProfile c N Φ χ (u : ℂ)‖ ≤
        (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (∫ u in Icc aJ bJ, spinFProfile c Φ u) +
          ∫ u in Icc aJ bJ, f_e u := by
      have hconstF : IntegrableOn (fun u => (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * spinFProfile c Φ u)
          (Icc aJ bJ) := hF_int_J.const_mul ((4 * spinCalF xiStar ^ 2 * h₀)⁻¹)
      have h1 := setIntegral_mono_on hH_cont_J.integrableOn_Icc
        (hconstF.add hfe_cont.continuousOn.integrableOn_Icc) measurableSet_Icc hnorm_pt
      dsimp only [Pi.add_apply] at h1
      rw [integral_add hconstF hfe_cont.continuousOn.integrableOn_Icc,
        integral_const_mul] at h1
      exact h1
    have hinv_nn : 0 ≤ (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ := by positivity
    have hF_le : (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (∫ u in Icc aJ bJ, spinFProfile c Φ u) +
        ∫ u in Icc aJ bJ, f_e u ≤
        (4 * spinCalF xiStar ^ 2 * h₀)⁻¹ * (1 / ((k : ℝ) + 1)) +
          (2 * cFc)⁻¹ * C_r * ((N : ℝ) + 1) * Real.exp (-4 * π * (xiStar / 4) * (N : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hF_lt.le hinv_nn) herr_J
    exact ⟨hc49, hc41, hu_mem, hχ_m, hχ_b, hχ_s, hH_uk, h_int_mono.trans hF_le⟩
  exact spinS4_4_3_montel_contra hV_pos hR_pos hM_pos hab
    (by linarith [hCa, hC₀, le_max_left R bJ] : -M ≤ aJ) (le_max_right R bJ : bJ ≤ M)
    (fun k => (le_max_right c_thr ((k : ℝ) + 50)).trans (hSeq_prop k).1)
    (fun k => (hSeq_prop k).2.2.1.2.1)
    (fun k => (hSeq_prop k).2.2.1.2.2.1)
    (fun k => (hk_all k).2.2.1)
    (fun k => (hk_all k).2.2.2.1)
    (fun k => (hk_all k).2.2.2.2.1)
    (fun k => (hk_all k).2.2.2.2.2.1)
    (fun k => (hk_all k).2.2.2.2.2.2.1)
    (fun k => (hk_all k).2.2.2.2.2.2.2)
    h_err_lim

/-- **`s4:4.3` (`spinning_s4.tex`, Theorem 4.3): global non-vanishing and restricted
observability on compact intervals `J ⊂ (C₀, ∞)`.** -/
theorem spinS4_4_3 : SpinS4_4_3 := by
  intro C₀ aJ bJ hC₀ hCa hab
  obtain ⟨κ_J, c₀', hκJ_pos, hc₀', h_int⟩ := spinS4_4_3_J_lower hC₀ hCa hab
  refine ⟨κ_J, κ_J, max 49 c₀', hκJ_pos, hκJ_pos, by linarith [le_max_left (49 : ℝ) c₀'], ?_⟩
  intro c x₁ hc n ε _hx₁ Φ hS
  have hJ := h_int ((le_max_right 49 c₀').trans hc) _hx₁ hS
  refine ⟨hJ, ?_⟩
  rw [hS.2.2.1, mul_one]
  exact hJ.trans (spinFProfile_le_spinCalNorm ((le_max_left 49 c₀').trans hc) hab hS.2.1)

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_4_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_4_3

end FormalResearch.ModularBootstrap.Spin
