module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeOuterBase

/-!
# Uniform Amplitude Bounds on `(0, ∞)` for the Outer Edge Kernel (`LowerKedgeOuterAmp`)

Provides the `ε`-uniform `C²` amplitude bounds on `(0, v_max]` and `[v₀, ∞)` used by
`LowerKedgeOuter` (`cts:Kedge-outer`), building on `LowerKedgeOuterBase`:

* `kedgeAmp0_D2_of_ge`: uniform `D2 (Ici v₀)` bounds (`v₀ > 0`) for `kedgeAmp0 ε` and
  `kedgeAmp0Aux ε` (feeds `CtOsc.stat_phase` via domain scaling).
* `kedgeAmp0_small_v_bounds`: uniform-in-`ε` singular bounds
  `‖B(v)‖ ≤ M₀ v^{1/2}`, `‖B'(v)‖ ≤ M₁ v^{-1/2}`, `‖B''(v)‖ ≤ M₂ v^{-3/2}` on `(0, v_max]`
  for `kedgeAmp0 ε` and `kedgeAmp0Aux ε`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
open FormalResearch.SignUncertainty.CtOsc

noncomputable section

private lemma mtSq_D2_small_v {v_max : ℝ} (hv_max : 0 < v_max) :
    ∃ K_mt : ℝ, 0 < K_mt ∧ ∀ {ε : ℝ}, ε ∈ Ioo (0 : ℝ) (1 / 2) →
      ∃ M1 M2 : ℝ → ℂ, D2 (Ioc (0 : ℝ) v_max)
        (fun v => lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2) M1 M2 K_mt := by
  let v_hi := v_max + 1
  have hv_hi : 0 < v_hi := by linarith
  let x_max := edgeF v_hi
  have hx_max : xiStar < x_max := by rw [← edgeF_zero]; exact edgeF_strictMonoOn le_rfl hv_hi.le hv_hi
  let m : ℝ := slitA x_max
  have hm_pos : 0 < m := slitA_pos x_max
  obtain ⟨hd_tau, hd_τ1, hc_τ2, hτ_bd⟩ := tauOfV_derivs
  have hpi := Real.pi_pos
  let a := fun v : ℝ => π * tauOfV v / 4
  let a1 := fun v : ℝ => (π / 4) * (2 * Real.cosh (π * v) / √(1 + Real.cosh (π * v) ^ 2))
  let a2 := fun v : ℝ => (π / 4) * (2 * π * Real.sinh (π * v) / (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ))
  let y := fun v : ℝ => Real.tanh (a v)
  have hd_y : ∀ v, HasDerivAt y ((1 - y v ^ 2) * a1 v) v := fun v => by
    have hda : HasDerivAt a (a1 v) v := (((hd_tau v).const_mul π).div_const 4).congr_deriv (by
      dsimp [a1]; ring)
    have hch_pos : 0 < Real.cosh (a v) := Real.cosh_pos _
    have htan : y = fun t => Real.sinh (a t) / Real.cosh (a t) :=
      funext fun t => Real.tanh_eq_sinh_div_cosh _
    have hdiv := ((Real.hasDerivAt_sinh (a v)).comp v hda).div
      ((Real.hasDerivAt_cosh (a v)).comp v hda) hch_pos.ne'
    have hch2 : Real.cosh (a v) ^ 2 ≠ 0 := pow_ne_zero 2 hch_pos.ne'
    have hsq := Real.cosh_sq_sub_sinh_sq (a v)
    have hid : 1 - (Real.sinh (a v) / Real.cosh (a v)) ^ 2 = (Real.cosh (a v) ^ 2)⁻¹ := by
      field_simp [hch2]; linarith
    rw [htan]
    refine hdiv.congr_deriv ?_
    change (Real.cosh (a v) * a1 v * Real.cosh (a v) - Real.sinh (a v) * (Real.sinh (a v) * a1 v)) /
        Real.cosh (a v) ^ 2 = (1 - (Real.sinh (a v) / Real.cosh (a v)) ^ 2) * a1 v
    rw [hid]
    field_simp [hch2]
    linear_combination (a1 v) * hsq
  let sA := fun v : ℝ => 1 - y v ^ 2
  let sA1 := fun v : ℝ => -2 * y v * sA v * a1 v
  let sA2 := fun v : ℝ => -2 * (sA v ^ 2 - 2 * y v ^ 2 * sA v) * a1 v ^ 2 - 2 * y v * sA v * a2 v
  have hd_sA : ∀ v, HasDerivAt sA (sA1 v) v := fun v =>
    ((hasDerivAt_const v (1 : ℝ)).sub ((hd_y v).pow 2)).congr_deriv (by dsimp [sA1, sA]; ring)
  have hd_sA1 : ∀ v, HasDerivAt sA1 (sA2 v) v := fun v => by
    have hda1 : HasDerivAt a1 (a2 v) v := ((hd_τ1 v).const_mul (π / 4)).congr_deriv (by ring)
    have hp : HasDerivAt (fun t => (-2 * y t) * sA t)
        ((-2 * (sA v * a1 v)) * sA v + (-2 * y v) * sA1 v) v :=
      (((hd_y v).const_mul (-2)).mul (hd_sA v)).congr_deriv (by ring)
    have hp2 : HasDerivAt (fun t => (-2 * y t * sA t) * a1 t)
        (((-2 * (sA v * a1 v)) * sA v + (-2 * y v) * sA1 v) * a1 v + (-2 * y v * sA v) * a2 v) v :=
      hp.mul hda1
    refine hp2.congr_deriv ?_
    dsimp [sA2, sA1, sA]; ring
  have hy_bd : ∀ v ∈ Ioo (0 : ℝ) v_hi, 0 ≤ y v ∧ y v < 1 ∧ m ≤ sA v ∧ sA v ≤ 1 := fun v hv => by
    have hv0 : 0 ≤ v := hv.1.le
    have hy_eq : y v = lowerY (edgeF v) := tanh_tauOfV_eq_lowerY_edgeF hv0
    have hle : edgeF v ≤ x_max := (edgeF_strictMonoOn hv0 hv_hi.le hv.2).le
    have hx_gt : xiStar < edgeF v := by rw [← edgeF_zero]; exact edgeF_strictMonoOn le_rfl hv0 hv.1
    have hs_ge : slitA x_max ≤ slitA (edgeF v) := by
      unfold slitA
      have hch : Real.cosh (π * edgeF v) ≤ Real.cosh (π * x_max) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hpi.le (xiStar_pos.le.trans hx_gt.le)),
          abs_of_nonneg (mul_nonneg hpi.le (xiStar_pos.le.trans hx_max.le))]
        exact mul_le_mul_of_nonneg_left hle hpi.le
      have hden : 0 < Real.cosh (π * edgeF v) + √2 := by have := Real.cosh_pos (π * edgeF v); positivity
      exact div_le_div_of_nonneg_left (by positivity) hden (by linarith)
    have h1y : 1 - y v ^ 2 = slitA (edgeF v) := by rw [hy_eq]; exact one_sub_lowerY_sq hx_gt
    have hy_mem := yOfX_mem hx_gt
    have hs1 : slitA (edgeF v) ≤ 1 := (slitA_lt_one hx_gt).le
    rw [hy_eq]
    refine ⟨hy_mem.1.le, hy_mem.2, ?_, ?_⟩ <;> linarith [h1y, hy_eq]
  have hc_y : Continuous y := continuous_iff_continuousAt.mpr fun v => (hd_y v).continuousAt
  have hc_a1 : Continuous a1 := (continuous_const.mul ((continuous_iff_continuousAt.mpr fun v =>
    (hd_τ1 v).continuousAt)))
  have hc_a2 : Continuous a2 := continuous_const.mul hc_τ2
  have hc_sA : Continuous sA := continuous_const.sub (hc_y.pow 2)
  have hc_sA1 : Continuous sA1 := (((continuous_const.mul hc_y).mul hc_sA).mul hc_a1)
  have hc_sA2 : Continuous sA2 := by
    unfold sA2
    fun_prop
  have ha1_bd : ∀ v, 0 ≤ v → |a1 v| ≤ π / 2 := fun v hv => by
    dsimp [a1]; rw [abs_mul, abs_of_pos (div_pos hpi (by norm_num))]
    exact (mul_le_mul_of_nonneg_left (hτ_bd v hv).1 (div_pos hpi (by norm_num)).le).trans_eq (by ring)
  have ha2_bd : ∀ v, 0 ≤ v → |a2 v| ≤ π ^ 2 / 2 := fun v hv => by
    dsimp [a2]; rw [abs_mul, abs_of_pos (div_pos hpi (by norm_num))]
    exact (mul_le_mul_of_nonneg_left (hτ_bd v hv).2 (div_pos hpi (by norm_num)).le).trans_eq (by ring)
  let Ky : ℝ := 1 + π + π ^ 2
  let KsA : ℝ := 1 + π + (4 * (π / 2) ^ 2 + π ^ 2)
  have hKsA_pos : 0 < KsA := by positivity
  have hD2_y : D2 (Ioo (0 : ℝ) v_hi) y (fun v => sA v * a1 v)
      (fun v => sA1 v * a1 v + sA v * a2 v) Ky := {
    d1 := fun v _ => hd_y v
    d2 := fun v _ => ((hd_sA v).mul ((hd_τ1 v).const_mul (π / 4))).congr_deriv (by dsimp [a1, a2])
    c2 := (hc_sA1.mul hc_a1 |>.add (hc_sA.mul hc_a2)).continuousOn
    K0 := by positivity
    b0 := fun v hv => by
      have := hy_bd v hv; rw [Real.norm_eq_abs, abs_of_nonneg this.1]
      exact this.2.1.le.trans (by dsimp [Ky]; nlinarith)
    b1 := fun v hv => by
      have hb := hy_bd v hv
      have hs0 : 0 ≤ sA v := hm_pos.le.trans hb.2.2.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0]
      calc sA v * |a1 v| ≤ 1 * (π / 2) := mul_le_mul hb.2.2.2 (ha1_bd v hv.1.le) (abs_nonneg _) zero_le_one
        _ ≤ Ky := by dsimp [Ky]; nlinarith [sq_nonneg π]
    b2 := fun v hv => by
      have hb := hy_bd v hv
      have hs0 : 0 ≤ sA v := hm_pos.le.trans hb.2.2.1
      have hsA1_bd : |sA1 v| ≤ π := by
        dsimp [sA1]; rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_two, abs_of_nonneg hb.1, abs_of_nonneg hs0]
        calc 2 * y v * sA v * |a1 v| ≤ 2 * 1 * 1 * (π / 2) := by
              gcongr; exact hb.2.1.le; exact hb.2.2.2; exact ha1_bd v hv.1.le
          _ = π := by ring
      rw [Real.norm_eq_abs]
      have h1 : |sA1 v * a1 v| ≤ π * (π / 2) := by
        rw [abs_mul]; exact mul_le_mul hsA1_bd (ha1_bd v hv.1.le) (abs_nonneg _) (by positivity)
      have h2 : |sA v * a2 v| ≤ 1 * (π ^ 2 / 2) := by
        rw [abs_mul, abs_of_nonneg hs0]
        exact mul_le_mul hb.2.2.2 (ha2_bd v hv.1.le) (abs_nonneg _) zero_le_one
      exact (abs_add_le _ _).trans (by dsimp [Ky]; nlinarith [hpi]) }
  have hD2_sA : D2 (Ioo (0 : ℝ) v_hi) sA sA1 sA2 KsA := {
    d1 := fun v _ => hd_sA v
    d2 := fun v _ => hd_sA1 v
    c2 := hc_sA2.continuousOn
    K0 := hKsA_pos.le
    b0 := fun v hv => by
      have hb := hy_bd v hv; rw [Real.norm_eq_abs, abs_of_nonneg (hm_pos.le.trans hb.2.2.1)]
      exact hb.2.2.2.trans (by dsimp [KsA]; nlinarith [sq_nonneg π])
    b1 := fun v hv => by
      have hb := hy_bd v hv; have hs0 : 0 ≤ sA v := hm_pos.le.trans hb.2.2.1
      rw [Real.norm_eq_abs]
      dsimp [sA1]; rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_two, abs_of_nonneg hb.1, abs_of_nonneg hs0]
      calc 2 * y v * sA v * |a1 v| ≤ 2 * 1 * 1 * (π / 2) := by
            gcongr; exact hb.2.1.le; exact hb.2.2.2; exact ha1_bd v hv.1.le
        _ = π := by ring
        _ ≤ KsA := by dsimp [KsA]; nlinarith [sq_nonneg π]
    b2 := fun v hv => by
      have hb := hy_bd v hv; have hs0 : 0 ≤ sA v := hm_pos.le.trans hb.2.2.1
      rw [Real.norm_eq_abs]; dsimp [sA2]
      refine (abs_sub _ _).trans ?_
      have h1 : |-2 * (sA v ^ 2 - 2 * y v ^ 2 * sA v) * a1 v ^ 2| ≤ 4 * (π / 2) ^ 2 := by
        rw [abs_mul, abs_mul, abs_neg, abs_two, abs_pow]
        have hbr : |sA v ^ 2 - 2 * y v ^ 2 * sA v| ≤ 2 := by
          have hs_sq_nn : 0 ≤ sA v ^ 2 := sq_nonneg _
          have hs_sq_le : sA v ^ 2 ≤ 1 := pow_le_one₀ hs0 hb.2.2.2
          have hy_sq_nn : 0 ≤ 2 * y v ^ 2 * sA v := by positivity
          have hy_sq_le : 2 * y v ^ 2 * sA v ≤ 2 := by
            have hy2 : y v ^ 2 ≤ 1 := pow_le_one₀ hb.1 hb.2.1.le
            nlinarith
          rw [abs_le]; constructor <;> linarith
        have ha1sq : |a1 v| ^ 2 ≤ (π / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (ha1_bd v hv.1.le) 2
        calc 2 * |sA v ^ 2 - 2 * y v ^ 2 * sA v| * |a1 v| ^ 2 ≤ 2 * 2 * (π / 2) ^ 2 := by gcongr
          _ = 4 * (π / 2) ^ 2 := by ring
      have h2 : |2 * y v * sA v * a2 v| ≤ π ^ 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg hb.1, abs_of_nonneg hs0]
        calc 2 * y v * sA v * |a2 v| ≤ 2 * 1 * 1 * (π ^ 2 / 2) := by
              gcongr; exact hb.2.1.le; exact hb.2.2.2; exact ha2_bd v hv.1.le
          _ = π ^ 2 := by ring
      dsimp [KsA]; linarith }
  let KD : ℝ := KsA + 1 + Ky
  let Kn2 : ℝ := 4 * KD * KD
  let Km : ℝ := (m ^ 2)⁻¹ + Kn2 * (m ^ 2)⁻¹ ^ 2 + 2 * (Kn2 ^ 2 * (m ^ 2)⁻¹ ^ 3)
  let KQ : ℝ := 4 * KsA * (4 * KD * Km)
  let K_mt : ℝ := 4 * (9 / 4) * (4 * KQ * KQ)
  refine ⟨K_mt, by positivity, fun {ε} hε => ?_⟩
  let D := fun v : ℝ => ((sA v + ε : ℝ) : ℂ) + Complex.I * ((ε * y v : ℝ) : ℂ)
  let D1 := fun v : ℝ => (sA1 v : ℂ) + Complex.I * ((ε * (sA v * a1 v) : ℝ) : ℂ)
  let D2v := fun v : ℝ => (sA2 v : ℂ) + Complex.I * ((ε * (sA1 v * a1 v + sA v * a2 v) : ℝ) : ℂ)
  have hD_D2 : D2 (Ioo (0 : ℝ) v_hi) D D1 D2v KD := {
    d1 := fun v hv => ((hD2_sA.d1 v hv).add_const ε).ofReal_comp.add
      (((hD2_y.d1 v hv).const_mul ε).ofReal_comp.const_mul Complex.I)
    d2 := fun v hv => (hD2_sA.d2 v hv).ofReal_comp.add
      (((hD2_y.d2 v hv).const_mul ε).ofReal_comp.const_mul Complex.I)
    c2 := (Complex.continuous_ofReal.comp hc_sA2).continuousOn.add
      ((Complex.continuous_ofReal.comp
        (((hc_sA1.mul hc_a1).add (hc_sA.mul hc_a2)).const_mul ε)).const_mul Complex.I).continuousOn
    K0 := by positivity
    b0 := fun v hv => by
      have hb := hy_bd v hv
      have h1 := norm_add_le ((sA v + ε : ℝ) : ℂ) (Complex.I * ((ε * y v : ℝ) : ℂ))
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs] at h1
      have h_se : |sA v + ε| ≤ 1 + 1 / 2 := by
        rw [abs_of_nonneg (by have := hm_pos.le.trans hb.2.2.1; linarith [hε.1])]
        linarith [hb.2.2.2, hε.2]
      have h_ey : |ε * y v| ≤ 1 / 2 := by
        rw [abs_of_nonneg (mul_nonneg hε.1.le hb.1)]
        nlinarith [hε.1, hε.2, hb.1, hb.2.1]
      have : 0 ≤ Ky := hD2_y.K0
      have : 1 + 1 / 2 + 1 / 2 ≤ KsA + 1 := by dsimp [KsA]; nlinarith [sq_nonneg π]
      dsimp [KD]; linarith
    b1 := fun v hv => by
      have hs1 := hD2_sA.b1 v hv; rw [Real.norm_eq_abs] at hs1
      have hy1 := hD2_y.b1 v hv; rw [Real.norm_eq_abs] at hy1
      have hre : ‖(sA1 v : ℂ)‖ ≤ KsA := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hs1
      have him : ‖Complex.I * ((ε * (sA v * a1 v) : ℝ) : ℂ)‖ ≤ Ky := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hε.1]
        nlinarith [hε.2, hy1, abs_nonneg (sA v * a1 v)]
      exact (norm_add_le _ _).trans (by dsimp [KD]; linarith)
    b2 := fun v hv => by
      have hs2 := hD2_sA.b2 v hv; rw [Real.norm_eq_abs] at hs2
      have hy2 := hD2_y.b2 v hv; rw [Real.norm_eq_abs] at hy2
      have hre : ‖(sA2 v : ℂ)‖ ≤ KsA := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hs2
      have him : ‖Complex.I * ((ε * (sA1 v * a1 v + sA v * a2 v) : ℝ) : ℂ)‖ ≤ Ky := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hε.1]
        nlinarith [hε.2, hy2, abs_nonneg (sA1 v * a1 v + sA v * a2 v)]
      exact (norm_add_le _ _).trans (by dsimp [KD]; linarith) }
  let Dconj := fun v : ℝ => ((sA v + ε : ℝ) : ℂ) - Complex.I * ((ε * y v : ℝ) : ℂ)
  let Dconj1 := fun v : ℝ => (sA1 v : ℂ) - Complex.I * ((ε * (sA v * a1 v) : ℝ) : ℂ)
  let Dconj2 := fun v : ℝ => (sA2 v : ℂ) - Complex.I * ((ε * (sA1 v * a1 v + sA v * a2 v) : ℝ) : ℂ)
  have hDc_D2 : D2 (Ioo (0 : ℝ) v_hi) Dconj Dconj1 Dconj2 KD := {
    d1 := fun v hv => ((hD2_sA.d1 v hv).add_const ε).ofReal_comp.sub
      (((hD2_y.d1 v hv).const_mul ε).ofReal_comp.const_mul Complex.I)
    d2 := fun v hv => (hD2_sA.d2 v hv).ofReal_comp.sub
      (((hD2_y.d2 v hv).const_mul ε).ofReal_comp.const_mul Complex.I)
    c2 := (Complex.continuous_ofReal.comp hc_sA2).continuousOn.sub
      ((Complex.continuous_ofReal.comp
        (((hc_sA1.mul hc_a1).add (hc_sA.mul hc_a2)).const_mul ε)).const_mul Complex.I).continuousOn
    K0 := hD_D2.K0
    b0 := fun v hv => by
      have hconj : Dconj v = starRingEnd ℂ (D v) := by dsimp [Dconj, D]; simp [Complex.conj_ofReal]; ring
      rw [hconj, Complex.norm_conj]; exact hD_D2.b0 v hv
    b1 := fun v hv => by
      have hconj : Dconj1 v = starRingEnd ℂ (D1 v) := by dsimp [Dconj1, D1]; simp [Complex.conj_ofReal]; ring
      rw [hconj, Complex.norm_conj]; exact hD_D2.b1 v hv
    b2 := fun v hv => by
      have hconj : Dconj2 v = starRingEnd ℂ (D2v v) := by dsimp [Dconj2, D2v]; simp [Complex.conj_ofReal]; ring
      rw [hconj, Complex.norm_conj]; exact hD_D2.b2 v hv }
  have hN_D2 := D2_re (D2_mulC hD_D2 hDc_D2)
  have hN_lo : ∀ v ∈ Ioo (0 : ℝ) v_hi, m ^ 2 ≤ (D v * Dconj v).re := fun v hv => by
    have hconj : Dconj v = starRingEnd ℂ (D v) := by dsimp [Dconj, D]; simp [Complex.conj_ofReal]; ring
    rw [hconj, Complex.mul_conj]
    simp only [Complex.ofReal_re, Complex.normSq_apply]
    dsimp [D]; simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, Complex.mul_im, one_mul, zero_add]
    have hs := (hy_bd v hv).2.2.1
    nlinarith [sq_nonneg (sA v + ε), hε.1]
  have hNinv_D2 := hN_D2.inv (pow_pos hm_pos 2) hN_lo
  have hNinvC : D2 (Ioo (0 : ℝ) v_hi) (fun v => (((D v * Dconj v).re⁻¹ : ℝ) : ℂ)) _ _ Km := {
    d1 := fun v hv => (hNinv_D2.d1 v hv).ofReal_comp
    d2 := fun v hv => (hNinv_D2.d2 v hv).ofReal_comp
    c2 := Complex.continuous_ofReal.comp_continuousOn hNinv_D2.c2
    K0 := hNinv_D2.K0
    b0 := fun v hv => by rw [Complex.norm_real]; exact hNinv_D2.b0 v hv
    b1 := fun v hv => by rw [Complex.norm_real]; exact hNinv_D2.b1 v hv
    b2 := fun v hv => by rw [Complex.norm_real]; exact hNinv_D2.b2 v hv }
  have hDinv_D2 := D2_mulC hDc_D2 hNinvC
  have hsAC_D2 : D2 (Ioo (0 : ℝ) v_hi) (fun v => (sA v : ℂ)) (fun v => (sA1 v : ℂ)) (fun v => (sA2 v : ℂ)) KsA := {
    d1 := fun v hv => (hD2_sA.d1 v hv).ofReal_comp
    d2 := fun v hv => (hD2_sA.d2 v hv).ofReal_comp
    c2 := Complex.continuous_ofReal.comp_continuousOn hD2_sA.c2
    K0 := hD2_sA.K0
    b0 := fun v hv => by rw [Complex.norm_real]; exact hD2_sA.b0 v hv
    b1 := fun v hv => by rw [Complex.norm_real]; exact hD2_sA.b1 v hv
    b2 := fun v hv => by rw [Complex.norm_real]; exact hD2_sA.b2 v hv }
  have hQ_D2 := D2_mulC hsAC_D2 hDinv_D2
  have hc1e : D2 (Ioo (0 : ℝ) v_hi) (fun _ => ((1 + ε : ℝ) : ℂ) ^ 2) (fun _ => 0) (fun _ => 0) (9 / 4) := {
    d1 := fun v _ => hasDerivAt_const v _
    d2 := fun v _ => hasDerivAt_const v 0
    c2 := continuousOn_const
    K0 := by norm_num
    b0 := fun _ _ => by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hε.1])]
      nlinarith [hε.1, hε.2]
    b1 := fun _ _ => by simp; norm_num
    b2 := fun _ _ => by simp; norm_num }
  have hM_D2 := D2_mulC hc1e (D2_mulC hQ_D2 hQ_D2)
  have hmt_eq : ∀ v ∈ Ioo (0 : ℝ) v_hi,
      lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 =
        ((1 + ε : ℝ) : ℂ) ^ 2 * ((sA v : ℂ) * (Dconj v * (((D v * Dconj v).re⁻¹ : ℝ) : ℂ)) *
          ((sA v : ℂ) * (Dconj v * (((D v * Dconj v).re⁻¹ : ℝ) : ℂ)))) := fun v hv => by
    have h1 : (1 : ℂ) + (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 = (sA v : ℂ) := by
      rw [← tanh_tauOfV_eq_lowerY_edgeF hv.1.le, mul_pow, Complex.I_sq]
      change (1 : ℂ) + -1 * (y v : ℂ) ^ 2 = ((1 - y v ^ 2 : ℝ) : ℂ)
      push_cast; ring
    have h2 : (1 : ℂ) + (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 +
        (ε : ℂ) * (1 + Complex.I * (lowerY (edgeF v) : ℂ)) = D v := by
      rw [h1, ← tanh_tauOfV_eq_lowerY_edgeF hv.1.le]
      change ((1 - y v ^ 2 : ℝ) : ℂ) + (ε : ℂ) * (1 + Complex.I * (y v : ℂ)) =
        ((sA v + ε : ℝ) : ℂ) + Complex.I * ((ε * y v : ℝ) : ℂ)
      dsimp [sA]; push_cast; ring
    have hDne : D v ≠ 0 := fun hz => by
      have := hN_lo v hv
      have hconj : Dconj v = starRingEnd ℂ (D v) := by dsimp [Dconj, D]; simp [Complex.conj_ofReal]; ring
      rw [hz, zero_mul, Complex.zero_re] at this
      linarith [pow_pos hm_pos 2]
    have hconj : Dconj v = starRingEnd ℂ (D v) := by dsimp [Dconj, D]; simp [Complex.conj_ofReal]; ring
    have hnormSq : (((D v * Dconj v).re : ℝ) : ℂ) = D v * Dconj v := by
      rw [hconj, Complex.mul_conj, Complex.ofReal_re]
    have hinv : Dconj v * (((D v * Dconj v).re⁻¹ : ℝ) : ℂ) = (D v)⁻¹ := by
      rw [Complex.ofReal_inv, hnormSq]
      have hDc_ne : Dconj v ≠ 0 := fun hz => hDne (by simpa [hconj] using congrArg (starRingEnd ℂ) hz)
      field_simp [hDne, hDc_ne]
    rw [hinv]
    unfold lowerMt
    rw [h2, h1]
    push_cast
    ring
  have hsub : Ioc (0 : ℝ) v_max ⊆ Ioo (0 : ℝ) v_hi := fun v hv => ⟨hv.1, lt_of_le_of_lt hv.2 (lt_add_one v_max)⟩
  refine ⟨_, _, {
    d1 := fun v hv => (hM_D2.d1 v (hsub hv)).congr_of_eventuallyEq
      (Eventually.mono (Ioo_mem_nhds (hsub hv).1 (hsub hv).2) fun t ht => hmt_eq t ht)
    d2 := fun v hv => hM_D2.d2 v (hsub hv)
    c2 := hM_D2.c2.mono hsub
    K0 := hM_D2.K0
    b0 := fun v hv => by rw [hmt_eq v (hsub hv)]; exact hM_D2.b0 v (hsub hv)
    b1 := fun v hv => hM_D2.b1 v (hsub hv)
    b2 := fun v hv => hM_D2.b2 v (hsub hv) }⟩

/-- `ε`-uniform `D2 (Ici v₀)` (`v₀ > 0`) for `kedgeAmp0 ε` and `kedgeAmp0Aux ε`. -/
theorem kedgeAmp0_D2_of_ge {v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∃ K0 K1 : ℝ, 0 < K0 ∧ 0 < K1 ∧ ∀ {ε : ℝ}, ε ∈ Ioo (0 : ℝ) (1 / 2) →
      (∃ B1 B2 : ℝ → ℂ, D2 (Ici v₀) (kedgeAmp0 ε) B1 B2 K0) ∧
      (∃ A1 A2 : ℝ → ℂ, D2 (Ici v₀) (kedgeAmp0Aux ε) A1 A2 K1) := by
  obtain ⟨K_th, hKth_pos, E1, E2, hE⟩ := expThetaOut_D2_global
  obtain ⟨K_e, hKe_pos, G1, G2, hG⟩ := oneSubExp_D2_global
  obtain ⟨I1, I2, hI⟩ := auxInv_D2_global
  obtain ⟨C0, C1, C2, CL1, CL2, hC0_nn, hC1_nn, hC2_nn, _, _, hmt⟩ := mtSq_oscAmpBound (half_pos hv₀)
  have hF_c : Continuous edgeF := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF v).continuousAt
  have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt
  have hF''_c : Continuous edgeF'' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF'' v).continuousAt
  let F0 := edgeF' v₀
  have hF0_pos : 0 < F0 := edgeF'_pos hv₀
  have hpi := Real.pi_pos
  let K_sq : ℝ := 1 + 4 * π / √F0 + (8 * π ^ 2 / √F0 + 16 * π ^ 2 / F0 ^ (3 / 2 : ℝ))
  have hKsq_pos : 0 < K_sq := by positivity
  let s1 := fun v : ℝ => edgeF'' v / (2 * √(edgeF' v))
  let s2 := fun v : ℝ => edgeF''' v / (2 * √(edgeF' v)) - edgeF'' v ^ 2 / (4 * √(edgeF' v) ^ 3)
  have hS_D2 : D2 (Ici v₀) (fun v => (√(edgeF' v) : ℂ)) (fun v => (s1 v : ℂ)) (fun v => (s2 v : ℂ)) K_sq := by
    have hD_real : D2 (Ici v₀) (fun v => √(edgeF' v)) s1 s2 K_sq := {
      d1 := fun v hv => (hasDerivAt_edgeF' v).sqrt (edgeF'_pos (hv₀.trans_le hv)).ne'
      d2 := fun v hv => by
        have hp : 0 < edgeF' v := edgeF'_pos (hv₀.trans_le hv)
        have hs_pos : 0 < √(edgeF' v) := Real.sqrt_pos.mpr hp
        have hs1 : HasDerivAt (fun t => √(edgeF' t)) (edgeF'' v / (2 * √(edgeF' v))) v :=
          (hasDerivAt_edgeF' v).sqrt hp.ne'
        have hd := (hasDerivAt_edgeF'' v).div (hs1.const_mul 2) (mul_ne_zero two_ne_zero hs_pos.ne')
        refine hd.congr_deriv ?_
        dsimp [s2]; field_simp [hs_pos.ne']; ring
      c2 := by
        have hcF''' : Continuous edgeF''' := by
          unfold edgeF'''
          have hpos : ∀ v : ℝ, (1 + Real.cosh (π * v) ^ 2) ^ (5 / 2 : ℝ) ≠ 0 :=
            fun v => (Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)) _).ne'
          exact ((continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
            (continuous_const.sub (continuous_const.mul ((Real.continuous_cosh.comp
              (continuous_const.mul continuous_id)).pow 2)))).div
            ((continuous_const.add ((Real.continuous_cosh.comp
              (continuous_const.mul continuous_id)).pow 2)).rpow_const
              fun _ => Or.inl (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)).ne') hpos
        have hs_c : Continuous fun v => √(edgeF' v) := Real.continuous_sqrt.comp hF'_c
        have hne : ∀ v ∈ Ici v₀, √(edgeF' v) ≠ 0 := fun v hv =>
          (Real.sqrt_pos.mpr (edgeF'_pos (hv₀.trans_le hv))).ne'
        exact (hcF'''.continuousOn.div (continuousOn_const.mul hs_c.continuousOn) fun v hv =>
            mul_ne_zero two_ne_zero (hne v hv)).sub
          ((hF''_c.pow 2).continuousOn.div (continuousOn_const.mul (hs_c.pow 3).continuousOn) fun v hv =>
            mul_ne_zero (by norm_num) (pow_ne_zero 3 (hne v hv)))
      K0 := hKsq_pos.le
      b0 := fun v hv => by
        have hbd := edgeF_deriv_bounds_of_ge hv₀ hv
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        have h1 : √(edgeF' v) ≤ 1 := Real.sqrt_le_one.mpr hbd.2.1
        have ha : 0 ≤ 4 * π / √F0 := by positivity
        have hb : 0 ≤ 8 * π ^ 2 / √F0 + 16 * π ^ 2 / F0 ^ (3 / 2 : ℝ) := by positivity
        dsimp [K_sq]; linarith
      b1 := fun v hv => by
        have hbd := edgeF_deriv_bounds_of_ge hv₀ hv
        have hs_ge : √F0 ≤ √(edgeF' v) := Real.sqrt_le_sqrt hbd.1
        have hs_pos : 0 < √F0 := Real.sqrt_pos.mpr hF0_pos
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hbd.2.2.1.le,
          abs_of_pos (mul_pos two_pos (Real.sqrt_pos.mpr (hF0_pos.trans_le hbd.1)))]
        have hdiv : edgeF'' v / (2 * √(edgeF' v)) ≤ 8 * π / (2 * √F0) :=
          div_le_div₀ (by positivity) hbd.2.2.2.1 (by positivity) (by gcongr)
        have h4 : 8 * π / (2 * √F0) = 4 * π / √F0 := by ring
        have hb : 0 ≤ 8 * π ^ 2 / √F0 + 16 * π ^ 2 / F0 ^ (3 / 2 : ℝ) := by positivity
        dsimp [K_sq]; linarith
      b2 := fun v hv => by
        have hbd := edgeF_deriv_bounds_of_ge hv₀ hv
        have hs_ge : √F0 ≤ √(edgeF' v) := Real.sqrt_le_sqrt hbd.1
        have hs_pos : 0 < √F0 := Real.sqrt_pos.mpr hF0_pos
        have hs_v : 0 < √(edgeF' v) := Real.sqrt_pos.mpr (hF0_pos.trans_le hbd.1)
        have h32_eq : √(edgeF' v) ^ 3 = edgeF' v ^ (3 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (hF0_pos.trans_le hbd.1).le]
          norm_num
        have h32_ge : F0 ^ (3 / 2 : ℝ) ≤ edgeF' v ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow hF0_pos.le hbd.1 (by norm_num)
        rw [Real.norm_eq_abs]
        refine (abs_sub _ _).trans ?_
        have t1 : |edgeF''' v / (2 * √(edgeF' v))| ≤ 8 * π ^ 2 / √F0 := by
          rw [abs_div, abs_of_pos (mul_pos two_pos hs_v)]
          calc |edgeF''' v| / (2 * √(edgeF' v)) ≤ (16 * π ^ 2) / (2 * √F0) :=
                div_le_div₀ (by positivity) hbd.2.2.2.2 (by positivity) (by gcongr)
            _ = 8 * π ^ 2 / √F0 := by ring
        have t2 : |edgeF'' v ^ 2 / (4 * √(edgeF' v) ^ 3)| ≤ 16 * π ^ 2 / F0 ^ (3 / 2 : ℝ) := by
          rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)), h32_eq]
          calc edgeF'' v ^ 2 / (4 * edgeF' v ^ (3 / 2 : ℝ))
              ≤ (8 * π) ^ 2 / (4 * F0 ^ (3 / 2 : ℝ)) :=
                div_le_div₀ (by positivity) (pow_le_pow_left₀ hbd.2.2.1.le hbd.2.2.2.1 2)
                  (by positivity) (by gcongr)
            _ = 16 * π ^ 2 / F0 ^ (3 / 2 : ℝ) := by ring
        have ha : 0 ≤ 4 * π / √F0 := by positivity
        dsimp [K_sq]; linarith }
    exact {
      d1 := fun v hv => (hD_real.d1 v hv).ofReal_comp
      d2 := fun v hv => (hD_real.d2 v hv).ofReal_comp
      c2 := Complex.continuous_ofReal.comp_continuousOn hD_real.c2
      K0 := hD_real.K0
      b0 := fun v hv => by rw [Complex.norm_real]; exact hD_real.b0 v hv
      b1 := fun v hv => by rw [Complex.norm_real]; exact hD_real.b1 v hv
      b2 := fun v hv => by rw [Complex.norm_real]; exact hD_real.b2 v hv }
  have hE_ge : D2 (Ici v₀) (fun v => Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ))) E1 E2 K_th :=
    { d1 := fun v hv => hE.d1 v (hv₀.trans_le hv)
      d2 := fun v hv => hE.d2 v (hv₀.trans_le hv)
      c2 := hE.c2.mono (fun v hv => hv₀.trans_le hv)
      K0 := hE.K0
      b0 := fun v hv => hE.b0 v (hv₀.trans_le hv)
      b1 := fun v hv => hE.b1 v (hv₀.trans_le hv)
      b2 := fun v hv => hE.b2 v (hv₀.trans_le hv) }
  have hG_ge : D2 (Ici v₀) _ G1 G2 K_e :=
    { d1 := fun v hv => hG.d1 v (hv₀.trans_le hv).le
      d2 := fun v hv => hG.d2 v (hv₀.trans_le hv).le
      c2 := hG.c2.mono (fun v hv => (hv₀.trans_le hv).le)
      K0 := hG.K0
      b0 := fun v hv => hG.b0 v (hv₀.trans_le hv).le
      b1 := fun v hv => hG.b1 v (hv₀.trans_le hv).le
      b2 := fun v hv => hG.b2 v (hv₀.trans_le hv).le }
  have hI_ge : D2 (Ici v₀) _ I1 I2 8 :=
    { d1 := fun v hv => hI.d1 v (hv₀.trans_le hv).le
      d2 := fun v hv => hI.d2 v (hv₀.trans_le hv).le
      c2 := hI.c2.mono (fun v hv => (hv₀.trans_le hv).le)
      K0 := hI.K0
      b0 := fun v hv => hI.b0 v (hv₀.trans_le hv).le
      b1 := fun v hv => hI.b1 v (hv₀.trans_le hv).le
      b2 := fun v hv => hI.b2 v (hv₀.trans_le hv).le }
  have hTES := D2_mulC hE_ge (D2_mulC hG_ge hS_D2)
  let K_mt : ℝ := max 1 (max C0 (max C1 C2))
  let K0 : ℝ := 4 * K_mt * (4 * K_th * (4 * K_e * K_sq))
  let K1 : ℝ := 4 * K0 * 8
  have hKmt_pos : 0 < K_mt := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK0_pos : 0 < K0 := by positivity
  have hK1_pos : 0 < K1 := by positivity
  refine ⟨K0, K1, hK0_pos, hK1_pos, fun {ε} hε => ?_⟩
  obtain ⟨F1, F2, hmt_e, hC0, hC1, hC2, _, _⟩ := hmt hε
  have hc_mt : ContinuousOn F2 (Ici v₀) := by
    let mtFun : ℝ → ℂ := fun v => lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2
    have hcd_tau : ContDiff ℝ 2 tauOfV := by
      unfold tauOfV
      refine contDiff_const.mul (Real.contDiff_arsinh.comp ?_)
      exact ContDiff.div_const (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)) √2
    have hcd_y : ContDiff ℝ 2 (fun v => Real.tanh (π * tauOfV v / 4)) := by
      have ha : ContDiff ℝ 2 (fun v => π * tauOfV v / 4) := ContDiff.div_const (contDiff_const.mul hcd_tau) 4
      have hch_ne : ∀ v : ℝ, Real.cosh (π * tauOfV v / 4) ≠ 0 := fun v => (Real.cosh_pos _).ne'
      have htan : (fun v => Real.tanh (π * tauOfV v / 4)) =
          fun v => Real.sinh (π * tauOfV v / 4) / Real.cosh (π * tauOfV v / 4) :=
        funext fun v => Real.tanh_eq_sinh_div_cosh _
      rw [htan]
      exact (Real.contDiff_sinh.comp ha).div (Real.contDiff_cosh.comp ha) hch_ne
    have hcd_yC : ContDiff ℝ 2 (fun v : ℝ => Complex.I * ((Real.tanh (π * tauOfV v / 4) : ℝ) : ℂ)) :=
      contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hcd_y)
    have hden_ne : ∀ v ∈ Ioi (v₀ / 2),
        (1 : ℂ) + (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 +
          (ε : ℂ) * (1 + Complex.I * (lowerY (edgeF v) : ℂ)) ≠ 0 := fun v hv => by
      have hv0 : 0 < v := (half_pos hv₀).trans hv
      have hx : xiStar < edgeF v := by rw [← edgeF_zero]; exact edgeF_strictMonoOn le_rfl hv0.le hv0
      intro hz
      have hre : ((1 : ℂ) + (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 +
          (ε : ℂ) * (1 + Complex.I * (lowerY (edgeF v) : ℂ))).re = slitA (edgeF v) + ε := by
        simp [mul_pow, Complex.I_sq, ← Complex.ofReal_pow]
        linarith [one_sub_lowerY_sq hx]
      rw [hz, Complex.zero_re] at hre
      linarith [slitA_pos (edgeF v), hε.1]
    let numFun : ℝ → ℂ := fun v => ((1 + ε : ℝ) : ℂ) *
      ((1 : ℂ) + (Complex.I * ((Real.tanh (π * tauOfV v / 4) : ℝ) : ℂ)) ^ 2)
    let denFun : ℝ → ℂ := fun v => (1 : ℂ) +
      (Complex.I * ((Real.tanh (π * tauOfV v / 4) : ℝ) : ℂ)) ^ 2 +
        (ε : ℂ) * (1 + Complex.I * ((Real.tanh (π * tauOfV v / 4) : ℝ) : ℂ))
    let rhsFun : ℝ → ℂ := fun v => (numFun v * (denFun v)⁻¹) ^ 2
    have heq_mt : EqOn mtFun rhsFun (Ioi (v₀ / 2)) :=
      fun v hv => by
        dsimp [mtFun, rhsFun, numFun, denFun, lowerMt]
        rw [tanh_tauOfV_eq_lowerY_edgeF ((half_pos hv₀).trans hv).le, div_eq_mul_inv]
        push_cast; ring
    have hcd_rhs : ContDiffOn ℝ 2 rhsFun (Ioi (v₀ / 2)) := by
      have hnum : ContDiffOn ℝ 2 numFun (Ioi (v₀ / 2)) :=
        (contDiff_const.mul (contDiff_const.add (hcd_yC.pow 2))).contDiffOn
      have hden : ContDiffOn ℝ 2 denFun (Ioi (v₀ / 2)) :=
        ((contDiff_const.add (hcd_yC.pow 2)).add (contDiff_const.mul (contDiff_const.add hcd_yC))).contDiffOn
      exact (hnum.mul (hden.inv fun v hv => by
        dsimp [denFun]
        simpa [← tanh_tauOfV_eq_lowerY_edgeF ((half_pos hv₀).trans hv).le] using hden_ne v hv)).pow 2
    have hcd_mt : ContDiffOn ℝ 2 mtFun (Ioi (v₀ / 2)) := hcd_rhs.congr heq_mt
    have hc_it2 : ContinuousOn (iteratedDerivWithin 2 mtFun (Ioi (v₀ / 2))) (Ioi (v₀ / 2)) :=
      hcd_mt.continuousOn_iteratedDerivWithin (m := 2) (le_refl _) (uniqueDiffOn_Ioi _)
    have heq_it2 : EqOn F2 (iteratedDerivWithin 2 mtFun (Ioi (v₀ / 2))) (Ioi (v₀ / 2)) := fun v hv => by
      have hF1_eq : EqOn F1 (derivWithin mtFun (Ioi (v₀ / 2))) (Ioi (v₀ / 2)) := fun t ht =>
        ((hmt_e.hd1 t ht.le).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ioi _ _ ht)).symm
      have hF2_eq : F2 v = derivWithin F1 (Ioi (v₀ / 2)) v :=
        ((hmt_e.hd2 v hv.le).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ioi _ _ hv)).symm
      rw [hF2_eq, derivWithin_congr hF1_eq (hF1_eq hv)]
      rw [iteratedDerivWithin_succ, iteratedDerivWithin_one]
    exact (hc_it2.congr heq_it2).mono fun v hv => lt_of_lt_of_le (half_lt_self hv₀) hv
  have hmt_D2 : D2 (Ici v₀) (fun v => lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2) F1 F2 K_mt := {
    d1 := fun v hv => hmt_e.hd1 v ((half_lt_self hv₀).le.trans hv)
    d2 := fun v hv => hmt_e.hd2 v ((half_lt_self hv₀).le.trans hv)
    c2 := hc_mt
    K0 := hKmt_pos.le
    b0 := fun v hv => (hmt_e.b0 v ((half_lt_self hv₀).le.trans hv)).trans
      (hC0.trans ((le_max_left _ _).trans (le_max_right 1 _)))
    b1 := fun v hv => (hmt_e.b1 v ((half_lt_self hv₀).le.trans hv)).trans
      (hC1.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right 1 _))))
    b2 := fun v hv => (hmt_e.b2 v ((half_lt_self hv₀).le.trans hv)).trans
      (hC2.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right 1 _)))) }
  have hB0_D2 := D2_mulC hmt_D2 hTES
  have hB1_D2 := D2_mulC hB0_D2 hI_ge
  have hB0_eq : ∀ t : ℝ,
      lowerMt ε (Complex.I * (lowerY (edgeF t) : ℂ)) ^ 2 *
        (Complex.exp (Complex.I * (thetaOut (lowerY (edgeF t)) : ℂ)) *
          ((((1 - Real.exp (-(4 * π * edgeF t))) ^ 2 : ℝ) : ℂ) * (√(edgeF' t) : ℂ))) =
      kedgeAmp0 ε t := fun t => by unfold kedgeAmp0; push_cast; ring
  have hB1_eq : ∀ t : ℝ,
      lowerMt ε (Complex.I * (lowerY (edgeF t) : ℂ)) ^ 2 *
        (Complex.exp (Complex.I * (thetaOut (lowerY (edgeF t)) : ℂ)) *
          ((((1 - Real.exp (-(4 * π * edgeF t))) ^ 2 : ℝ) : ℂ) * (√(edgeF' t) : ℂ))) *
        ((1 : ℂ) - 2 * Complex.I * (t : ℂ))⁻¹ =
      kedgeAmp0Aux ε t := fun t => by unfold kedgeAmp0Aux kedgeAmp0; push_cast; ring
  exact ⟨⟨_, _, {
      d1 := fun v hv => (hB0_D2.d1 v hv).congr_of_eventuallyEq (Eventually.of_forall fun t => (hB0_eq t).symm)
      d2 := hB0_D2.d2
      c2 := hB0_D2.c2
      K0 := hB0_D2.K0
      b0 := fun v hv => by rw [← hB0_eq v]; exact hB0_D2.b0 v hv
      b1 := hB0_D2.b1
      b2 := hB0_D2.b2 }⟩,
    ⟨_, _, {
      d1 := fun v hv => (hB1_D2.d1 v hv).congr_of_eventuallyEq (Eventually.of_forall fun t => (hB1_eq t).symm)
      d2 := hB1_D2.d2
      c2 := hB1_D2.c2
      K0 := hB1_D2.K0
      b0 := fun v hv => by rw [← hB1_eq v]; exact hB1_D2.b0 v hv
      b1 := hB1_D2.b1
      b2 := hB1_D2.b2 }⟩⟩

private lemma small_v_mul_sqrtEdgeF' {v_max K_s : ℝ} (hv_max : 0 < v_max) (hKs : 0 ≤ K_s)
    {S S1 S2 : ℝ → ℂ} (hS : D2 (Ioc (0 : ℝ) v_max) S S1 S2 K_s) :
    let cF : ℝ := 2 * π / (1 + Real.cosh (π * v_max) ^ 2) ^ (3 / 2 : ℝ)
    let C0 : ℝ := √(8 * π)
    let C1 : ℝ := 4 * π / √cF
    let C2 : ℝ := 8 * π ^ 2 * v_max / √cF + 16 * π ^ 2 / cF ^ (3 / 2 : ℝ)
    let M0 : ℝ := K_s * C0
    let M1 : ℝ := K_s * C0 * v_max + K_s * C1
    let M2 : ℝ := K_s * C0 * v_max ^ 2 + 2 * K_s * C1 * v_max + K_s * C2
    ∃ B1 B2 : ℝ → ℂ,
      (∀ v ∈ Ioc (0 : ℝ) v_max,
        HasDerivAt (fun t => S t * (√(edgeF' t) : ℂ)) (B1 v) v ∧ HasDerivAt B1 (B2 v) v) ∧
      ContinuousOn B2 (Ioc (0 : ℝ) v_max) ∧
      (∀ v ∈ Ioc (0 : ℝ) v_max,
        ‖S v * (√(edgeF' v) : ℂ)‖ ≤ M0 * v ^ (1 / 2 : ℝ) ∧
        ‖B1 v‖ ≤ M1 * v ^ (-(1 / 2 : ℝ)) ∧
        ‖B2 v‖ ≤ M2 * v ^ (-(3 / 2 : ℝ))) := by
  intro cF C0 C1 C2 M0 M1 M2
  have hpi := Real.pi_pos
  have hcF_pos : 0 < cF := by dsimp [cF]; positivity
  let s := fun v : ℝ => √(edgeF' v)
  let s1 := fun v : ℝ => edgeF'' v / (2 * √(edgeF' v))
  let s2 := fun v : ℝ => edgeF''' v / (2 * √(edgeF' v)) - edgeF'' v ^ 2 / (4 * √(edgeF' v) ^ 3)
  let B1 : ℝ → ℂ := fun v => S1 v * (s v : ℂ) + S v * (s1 v : ℂ)
  let B2 : ℝ → ℂ := fun v => S2 v * (s v : ℂ) + 2 * (S1 v * (s1 v : ℂ)) + S v * (s2 v : ℂ)
  have hF'_lb_ub : ∀ v ∈ Ioc (0 : ℝ) v_max, cF * v ≤ edgeF' v ∧ edgeF' v ≤ 8 * π * v := fun v hv => by
    have hv0 : 0 < v := hv.1
    have hlo : ∀ t ∈ Icc (0 : ℝ) v, cF ≤ edgeF'' t := fun t ht => by
      have ht_le : t ≤ v_max := ht.2.trans hv.2
      have hch_le : Real.cosh (π * t) ≤ Real.cosh (π * v_max) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hpi.le ht.1), abs_of_nonneg (mul_nonneg hpi.le hv_max.le)]
        exact mul_le_mul_of_nonneg_left ht_le hpi.le
      have hden_le : (1 + Real.cosh (π * t) ^ 2) ^ (3 / 2 : ℝ) ≤ (1 + Real.cosh (π * v_max) ^ 2) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by gcongr) (by norm_num)
      have hch_ge : 1 ≤ Real.cosh (π * t) := Real.one_le_cosh _
      have hnum : 2 * π * 1 ≤ 2 * π * Real.cosh (π * t) := mul_le_mul_of_nonneg_left hch_ge (by positivity)
      unfold edgeF''
      calc cF = 2 * π * 1 / (1 + Real.cosh (π * v_max) ^ 2) ^ (3 / 2 : ℝ) := by dsimp [cF]; ring
        _ ≤ 2 * π * Real.cosh (π * t) / (1 + Real.cosh (π * t) ^ 2) ^ (3 / 2 : ℝ) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden_le
    have hhi : ∀ t ∈ Icc (0 : ℝ) v, edgeF'' t ≤ 8 * π := fun t ht =>
      (edgeF''_bound ht.1).2.trans (by
        have : Real.exp (-(2 * π * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
        nlinarith)
    obtain ⟨c1, hc1, hce1⟩ := exists_hasDerivAt_eq_slope edgeF' edgeF'' hv0
      (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF' t).continuousAt).continuousOn
      fun t _ => hasDerivAt_edgeF' t
    rw [edgeF'_zero, sub_zero, sub_zero, eq_div_iff hv0.ne'] at hce1
    rw [← hce1]
    exact ⟨mul_le_mul_of_nonneg_right (hlo c1 ⟨hc1.1.le, hc1.2.le⟩) hv0.le,
      mul_le_mul_of_nonneg_right (hhi c1 ⟨hc1.1.le, hc1.2.le⟩) hv0.le⟩
  have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt
  have hF''_c : Continuous edgeF'' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF'' v).continuousAt
  have hcF''' : Continuous edgeF''' := by
    unfold edgeF'''
    have hpos : ∀ v : ℝ, (1 + Real.cosh (π * v) ^ 2) ^ (5 / 2 : ℝ) ≠ 0 :=
      fun v => (Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)) _).ne'
    exact ((continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
      (continuous_const.sub (continuous_const.mul ((Real.continuous_cosh.comp
        (continuous_const.mul continuous_id)).pow 2)))).div
      ((continuous_const.add ((Real.continuous_cosh.comp
        (continuous_const.mul continuous_id)).pow 2)).rpow_const
        fun _ => Or.inl (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)).ne') hpos
  have hs_d1 : ∀ v ∈ Ioc (0 : ℝ) v_max, HasDerivAt (fun t => (s t : ℂ)) (s1 v : ℂ) v := fun v hv => by
    have hp : 0 < edgeF' v := (mul_pos hcF_pos hv.1).trans_le (hF'_lb_ub v hv).1
    exact ((hasDerivAt_edgeF' v).sqrt hp.ne').ofReal_comp
  have hs_d2 : ∀ v ∈ Ioc (0 : ℝ) v_max, HasDerivAt (fun t => (s1 t : ℂ)) (s2 v : ℂ) v := fun v hv => by
    have hp : 0 < edgeF' v := (mul_pos hcF_pos hv.1).trans_le (hF'_lb_ub v hv).1
    have hsp : 0 < s v := Real.sqrt_pos.mpr hp
    have hs1 : HasDerivAt s (edgeF'' v / (2 * √(edgeF' v))) v := (hasDerivAt_edgeF' v).sqrt hp.ne'
    have hd := (hasDerivAt_edgeF'' v).div (hs1.const_mul 2) (mul_ne_zero two_ne_zero hsp.ne')
    exact (hd.congr_deriv (by dsimp [s2, s]; field_simp [hsp.ne']; ring)).ofReal_comp
  have hc_B2 : ContinuousOn B2 (Ioc (0 : ℝ) v_max) := by
    have hs_c : ContinuousOn (fun v => (s v : ℂ)) (Ioc (0 : ℝ) v_max) :=
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hF'_c)).continuousOn
    have hne : ∀ v ∈ Ioc (0 : ℝ) v_max, s v ≠ 0 := fun v hv =>
      (Real.sqrt_pos.mpr ((mul_pos hcF_pos hv.1).trans_le (hF'_lb_ub v hv).1)).ne'
    have hs1_c : ContinuousOn (fun v => (s1 v : ℂ)) (Ioc (0 : ℝ) v_max) :=
      Complex.continuous_ofReal.comp_continuousOn (hF''_c.continuousOn.div
        (continuousOn_const.mul (Real.continuous_sqrt.comp hF'_c).continuousOn)
        fun v hv => mul_ne_zero two_ne_zero (hne v hv))
    have hs2_c : ContinuousOn (fun v => (s2 v : ℂ)) (Ioc (0 : ℝ) v_max) :=
      Complex.continuous_ofReal.comp_continuousOn ((hcF'''.continuousOn.div
        (continuousOn_const.mul (Real.continuous_sqrt.comp hF'_c).continuousOn)
        fun v hv => mul_ne_zero two_ne_zero (hne v hv)).sub
        ((hF''_c.pow 2).continuousOn.div
          (continuousOn_const.mul ((Real.continuous_sqrt.comp hF'_c).pow 3).continuousOn)
          fun v hv => mul_ne_zero (by norm_num) (pow_ne_zero 3 (hne v hv))))
    exact ((hS.c2.mul hs_c).add (continuousOn_const.mul (hS.cont1.mul hs1_c))).add (hS.cont0.mul hs2_c)
  refine ⟨B1, B2, fun v hv => ⟨(hS.d1 v hv).mul (hs_d1 v hv), ?_⟩, hc_B2, fun v hv => ?_⟩
  · exact (((hS.d2 v hv).mul (hs_d1 v hv)).add ((hS.d1 v hv).mul (hs_d2 v hv))).congr_deriv (by dsimp [B2]; ring)
  · have hv0 : 0 < v := hv.1
    have hb_F := hF'_lb_ub v hv
    have hs_ub : s v ≤ C0 * v ^ (1 / 2 : ℝ) := by
      dsimp [s, C0]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hb_F.2
    have hs_lb : √cF * v ^ (1 / 2 : ℝ) ≤ s v := by
      dsimp [s]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul hcF_pos.le]
      exact Real.sqrt_le_sqrt hb_F.1
    have hsp : 0 < √cF * v ^ (1 / 2 : ℝ) := mul_pos (Real.sqrt_pos.mpr hcF_pos) (Real.rpow_pos_of_pos hv0 _)
    have hs_pos : 0 < s v := hsp.trans_le hs_lb
    have hF''_ub : 0 ≤ edgeF'' v ∧ edgeF'' v ≤ 8 * π :=
      ⟨(edgeF''_pos v).le, (edgeF''_bound hv0.le).2.trans (by
        have : Real.exp (-(2 * π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        nlinarith)⟩
    have hF'''_ub : |edgeF''' v| ≤ 16 * π ^ 2 :=
      (edgeF'''_bound hv0.le).trans (by
        have : Real.exp (-(2 * π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        nlinarith [sq_nonneg π])
    have hv12_inv : (v ^ (1 / 2 : ℝ))⁻¹ = v ^ (-(1 / 2 : ℝ)) := (Real.rpow_neg hv0.le (1 / 2 : ℝ)).symm
    have hs1_bd : |s1 v| ≤ C1 * v ^ (-(1 / 2 : ℝ)) := by
      dsimp [s1, C1]
      rw [abs_div, abs_of_nonneg hF''_ub.1, abs_of_pos (mul_pos two_pos hs_pos)]
      calc edgeF'' v / (2 * s v) ≤ (8 * π) / (2 * (√cF * v ^ (1 / 2 : ℝ))) :=
            div_le_div₀ (by positivity) hF''_ub.2 (by positivity) (by gcongr)
        _ = (4 * π / √cF) * (v ^ (1 / 2 : ℝ))⁻¹ := by ring
        _ = (4 * π / √cF) * v ^ (-(1 / 2 : ℝ)) := by rw [hv12_inv]
    have hv_pow12_32 : v * v ^ (-(3 / 2 : ℝ)) = v ^ (-(1 / 2 : ℝ)) := by
      conv_lhs => lhs; rw [← Real.rpow_one v]
      rw [← Real.rpow_add hv0]; norm_num
    have hv_pow2_32 : v ^ 2 * v ^ (-(3 / 2 : ℝ)) = v ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast v 2, ← Real.rpow_add hv0]; norm_num
    have hs_pow3 : s v ^ 3 ≥ cF ^ (3 / 2 : ℝ) * v ^ (3 / 2 : ℝ) := by
      have h1 : (√cF * v ^ (1 / 2 : ℝ)) ^ 3 ≤ s v ^ 3 := pow_le_pow_left₀ hsp.le hs_lb 3
      have h2 : (√cF) ^ 3 = cF ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hcF_pos.le]; norm_num
      have h3 : (v ^ (1 / 2 : ℝ)) ^ 3 = v ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hv0.le]; norm_num
      rw [mul_pow, h2, h3] at h1
      exact h1
    have hs2_bd : |s2 v| ≤ C2 * v ^ (-(3 / 2 : ℝ)) := by
      dsimp [s2, C2]
      refine (abs_sub _ _).trans ?_
      have t1 : |edgeF''' v / (2 * s v)| ≤ (8 * π ^ 2 * v_max / √cF) * v ^ (-(3 / 2 : ℝ)) := by
        rw [abs_div, abs_of_pos (mul_pos two_pos hs_pos)]
        have h1 : |edgeF''' v| / (2 * s v) ≤ (8 * π ^ 2 / √cF) * v ^ (-(1 / 2 : ℝ)) := by
          calc |edgeF''' v| / (2 * s v) ≤ (16 * π ^ 2) / (2 * (√cF * v ^ (1 / 2 : ℝ))) :=
                div_le_div₀ (by positivity) hF'''_ub (by positivity) (by gcongr)
            _ = (8 * π ^ 2 / √cF) * (v ^ (1 / 2 : ℝ))⁻¹ := by ring
            _ = (8 * π ^ 2 / √cF) * v ^ (-(1 / 2 : ℝ)) := by rw [hv12_inv]
        refine h1.trans ?_
        rw [← hv_pow12_32]
        have : (8 * π ^ 2 / √cF) * (v * v ^ (-(3 / 2 : ℝ))) = (8 * π ^ 2 * v / √cF) * v ^ (-(3 / 2 : ℝ)) := by ring
        rw [this]
        gcongr; exact hv.2
      have t2 : |edgeF'' v ^ 2 / (4 * s v ^ 3)| ≤ (16 * π ^ 2 / cF ^ (3 / 2 : ℝ)) * v ^ (-(3 / 2 : ℝ)) := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
        have hv32_pos : 0 < cF ^ (3 / 2 : ℝ) * v ^ (3 / 2 : ℝ) := by positivity
        calc edgeF'' v ^ 2 / (4 * s v ^ 3)
            ≤ (8 * π) ^ 2 / (4 * (cF ^ (3 / 2 : ℝ) * v ^ (3 / 2 : ℝ))) :=
              div_le_div₀ (by positivity) (pow_le_pow_left₀ hF''_ub.1 hF''_ub.2 2)
                (by positivity) (by gcongr)
          _ = (16 * π ^ 2 / cF ^ (3 / 2 : ℝ)) * (v ^ (3 / 2 : ℝ))⁻¹ := by ring
          _ = (16 * π ^ 2 / cF ^ (3 / 2 : ℝ)) * v ^ (-(3 / 2 : ℝ)) := by
              rw [Real.rpow_neg hv0.le (3 / 2 : ℝ)]
      exact (add_le_add t1 t2).trans_eq (by ring)
    have hB0 : ‖S v * (s v : ℂ)‖ ≤ M0 * v ^ (1 / 2 : ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs_pos.le]
      exact (mul_le_mul (hS.b0 v hv) hs_ub (by positivity) hKs).trans_eq (by dsimp [M0]; ring)
    have hB1 : ‖B1 v‖ ≤ M1 * v ^ (-(1 / 2 : ℝ)) := by
      dsimp [B1]
      have p1 : ‖S1 v * (s v : ℂ)‖ ≤ K_s * C0 * v_max * v ^ (-(1 / 2 : ℝ)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs_pos.le]
        have hle := mul_le_mul (hS.b1 v hv) hs_ub (by positivity) hKs
        have hv_rpow : v ^ (1 / 2 : ℝ) = v * v ^ (-(1 / 2 : ℝ)) := by
          conv_rhs => lhs; rw [← Real.rpow_one v]
          rw [← Real.rpow_add hv0]; norm_num
        rw [hv_rpow] at hle
        refine hle.trans ?_
        have : K_s * (C0 * (v * v ^ (-(1 / 2 : ℝ)))) = K_s * C0 * v * v ^ (-(1 / 2 : ℝ)) := by ring
        rw [this]
        gcongr; exact hv.2
      have p2 : ‖S v * (s1 v : ℂ)‖ ≤ K_s * C1 * v ^ (-(1 / 2 : ℝ)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (hS.b0 v hv) hs1_bd (abs_nonneg _) hKs).trans_eq (by ring)
      exact (norm_add_le _ _).trans ((add_le_add p1 p2).trans_eq (by dsimp [M1]; ring))
    have hB2 : ‖B2 v‖ ≤ M2 * v ^ (-(3 / 2 : ℝ)) := by
      dsimp [B2]
      have p1 : ‖S2 v * (s v : ℂ)‖ ≤ K_s * C0 * v_max ^ 2 * v ^ (-(3 / 2 : ℝ)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs_pos.le]
        have hle := mul_le_mul (hS.b2 v hv) hs_ub (by positivity) hKs
        rw [← hv_pow2_32] at hle
        refine hle.trans ?_
        have h1 : K_s * (C0 * (v ^ 2 * v ^ (-(3 / 2 : ℝ)))) = K_s * C0 * v ^ 2 * v ^ (-(3 / 2 : ℝ)) := by ring
        rw [h1]
        have hsqv : v ^ 2 ≤ v_max ^ 2 := pow_le_pow_left₀ hv0.le hv.2 2
        gcongr
      have p2 : ‖2 * (S1 v * (s1 v : ℂ))‖ ≤ 2 * K_s * C1 * v_max * v ^ (-(3 / 2 : ℝ)) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, show ‖(2 : ℂ)‖ = 2 by norm_num]
        have hle : 2 * (‖S1 v‖ * |s1 v|) ≤ 2 * (K_s * (C1 * v ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hS.b1 v hv) hs1_bd (abs_nonneg _) hKs) zero_le_two
        rw [← hv_pow12_32] at hle
        refine hle.trans ?_
        have h1 : 2 * (K_s * (C1 * (v * v ^ (-(3 / 2 : ℝ))))) = 2 * K_s * C1 * v * v ^ (-(3 / 2 : ℝ)) := by ring
        rw [h1]
        gcongr; exact hv.2
      have p3 : ‖S v * (s2 v : ℂ)‖ ≤ K_s * C2 * v ^ (-(3 / 2 : ℝ)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (hS.b0 v hv) hs2_bd (abs_nonneg _) hKs).trans_eq (by ring)
      exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add p1 p2)) p3).trans_eq
        (by dsimp [M2]; ring))
    exact ⟨hB0, hB1, hB2⟩

/-- Small-`v` (`(0, v_max]`) `v^{1/2 - k}` bounds for `kedgeAmp0 ε` and `kedgeAmp0Aux ε`. -/
theorem kedgeAmp0_small_v_bounds {v_max : ℝ} (hv_max : 0 < v_max) :
    ∃ M0 M1 M2 : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧ ∀ {ε : ℝ}, ε ∈ Ioo (0 : ℝ) (1 / 2) →
      (∃ B1 B2 : ℝ → ℂ,
        (∀ v ∈ Ioc (0 : ℝ) v_max, HasDerivAt (kedgeAmp0 ε) (B1 v) v ∧ HasDerivAt B1 (B2 v) v) ∧
        ContinuousOn B2 (Ioc (0 : ℝ) v_max) ∧
        (∀ v ∈ Ioc (0 : ℝ) v_max,
          ‖kedgeAmp0 ε v‖ ≤ M0 * v ^ (1 / 2 : ℝ) ∧
          ‖B1 v‖ ≤ M1 * v ^ (-(1 / 2 : ℝ)) ∧
          ‖B2 v‖ ≤ M2 * v ^ (-(3 / 2 : ℝ)))) ∧
      (∃ A1 A2 : ℝ → ℂ,
        (∀ v ∈ Ioc (0 : ℝ) v_max, HasDerivAt (kedgeAmp0Aux ε) (A1 v) v ∧ HasDerivAt A1 (A2 v) v) ∧
        ContinuousOn A2 (Ioc (0 : ℝ) v_max) ∧
        (∀ v ∈ Ioc (0 : ℝ) v_max,
          ‖kedgeAmp0Aux ε v‖ ≤ M0 * v ^ (1 / 2 : ℝ) ∧
          ‖A1 v‖ ≤ M1 * v ^ (-(1 / 2 : ℝ)) ∧
          ‖A2 v‖ ≤ M2 * v ^ (-(3 / 2 : ℝ)))) := by
  obtain ⟨K_mt, hKmt_pos, hmt⟩ := mtSq_D2_small_v hv_max
  obtain ⟨K_th, hKth_pos, E1, E2, hE⟩ := expThetaOut_D2_global
  obtain ⟨K_e, hKe_pos, G1, G2, hG⟩ := oneSubExp_D2_global
  obtain ⟨I1, I2, hI⟩ := auxInv_D2_global
  have hE_sm : D2 (Ioc (0 : ℝ) v_max) (fun v => Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ))) E1 E2 K_th :=
    { d1 := fun v hv => hE.d1 v hv.1, d2 := fun v hv => hE.d2 v hv.1,
      c2 := hE.c2.mono (fun v hv => hv.1), K0 := hE.K0,
      b0 := fun v hv => hE.b0 v hv.1, b1 := fun v hv => hE.b1 v hv.1, b2 := fun v hv => hE.b2 v hv.1 }
  have hG_sm : D2 (Ioc (0 : ℝ) v_max) _ G1 G2 K_e :=
    { d1 := fun v hv => hG.d1 v hv.1.le, d2 := fun v hv => hG.d2 v hv.1.le,
      c2 := hG.c2.mono (fun v hv => hv.1.le), K0 := hG.K0,
      b0 := fun v hv => hG.b0 v hv.1.le, b1 := fun v hv => hG.b1 v hv.1.le, b2 := fun v hv => hG.b2 v hv.1.le }
  have hI_sm : D2 (Ioc (0 : ℝ) v_max) _ I1 I2 8 :=
    { d1 := fun v hv => hI.d1 v hv.1.le, d2 := fun v hv => hI.d2 v hv.1.le,
      c2 := hI.c2.mono (fun v hv => hv.1.le), K0 := hI.K0,
      b0 := fun v hv => hI.b0 v hv.1.le, b1 := fun v hv => hI.b1 v hv.1.le, b2 := fun v hv => hI.b2 v hv.1.le }
  let K_s0 : ℝ := 4 * K_mt * (4 * K_th * K_e)
  let K_s1 : ℝ := 4 * K_s0 * 8
  let K_s : ℝ := max K_s0 K_s1
  have hKs0_pos : 0 < K_s0 := by positivity
  have hKs_nn : 0 ≤ K_s := le_max_of_le_left hKs0_pos.le
  let cF : ℝ := 2 * π / (1 + Real.cosh (π * v_max) ^ 2) ^ (3 / 2 : ℝ)
  have hcF_pos : 0 < cF := by have := Real.pi_pos; dsimp [cF]; positivity
  let C0 : ℝ := √(8 * π)
  let C1 : ℝ := 4 * π / √cF
  let C2 : ℝ := 8 * π ^ 2 * v_max / √cF + 16 * π ^ 2 / cF ^ (3 / 2 : ℝ)
  let M0 : ℝ := K_s * C0
  let M1 : ℝ := K_s * C0 * v_max + K_s * C1
  let M2 : ℝ := K_s * C0 * v_max ^ 2 + 2 * K_s * C1 * v_max + K_s * C2
  have hpi := Real.pi_pos
  refine ⟨M0, M1, M2, by positivity, by positivity, by positivity, fun {ε} hε => ?_⟩
  obtain ⟨Mt1, Mt2, hMt⟩ := hmt hε
  have hS0 := D2_mulC hMt (D2_mulC hE_sm hG_sm)
  have hS1 := D2_mulC hS0 hI_sm
  obtain ⟨B1, B2, hB_d, hB_c, hB_bd⟩ := small_v_mul_sqrtEdgeF' hv_max hKs_nn (hS0.mono (le_max_left K_s0 K_s1))
  obtain ⟨A1, A2, hA_d, hA_c, hA_bd⟩ := small_v_mul_sqrtEdgeF' hv_max hKs_nn (hS1.mono (le_max_right K_s0 K_s1))
  have hK0_eq : ∀ v, kedgeAmp0 ε v =
      (lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 *
        (Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) *
          (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 : ℝ) : ℂ))) * (√(edgeF' v) : ℂ) := fun v => by
    unfold kedgeAmp0; push_cast; ring
  have hK1_eq : ∀ v, kedgeAmp0Aux ε v =
      ((lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 *
        (Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) *
          (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 : ℝ) : ℂ))) *
        ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹) * (√(edgeF' v) : ℂ) := fun v => by
    unfold kedgeAmp0Aux kedgeAmp0; push_cast; ring
  refine ⟨⟨B1, B2, fun v hv => ?_, hB_c, fun v hv => ?_⟩,
          ⟨A1, A2, fun v hv => ?_, hA_c, fun v hv => ?_⟩⟩
  · have := hB_d v hv
    exact ⟨this.1.congr_of_eventuallyEq (Eventually.of_forall hK0_eq), this.2⟩
  · have := hB_bd v hv; rwa [← hK0_eq v] at this
  · have := hA_d v hv
    exact ⟨this.1.congr_of_eventuallyEq (Eventually.of_forall hK1_eq), this.2⟩
  · have := hA_bd v hv; rwa [← hK1_eq v] at this

end

end FormalResearch.ModularBootstrap.FiveTerm
