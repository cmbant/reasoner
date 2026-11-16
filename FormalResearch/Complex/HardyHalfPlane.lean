module

public import FormalResearch.Complex.HardyFejerRiesz

/-!
# Fejér–Riesz arc inequality for the upper half-plane

Generic complex analysis, no Airy content.  **Proved.**

`FormalResearch.Hardy.hardy_arc_le`: let `G` be holomorphic on the open upper half-plane `ℍ`, continuous on its closure,
with `‖G z‖ (1 + ‖z‖)³ ≤ C` on `Im z ≥ 0`.  Then for every `a > 0`

`a ∫_0^π ‖G(a e^{iφ})‖ dφ  =  ∫_{S_a} ‖G‖ |dz|  ≤  (1/2) ∫_ℝ ‖G(x)‖ dx`,

`S_a = {|z| = a, Im z > 0}` (the semicircle, a geodesic of `ℍ`).  This is Lemma FR of the Airy–Poisson note
(`CFT/modular_bootstrap/notes/AIRY_POISSON.md` §5, step (1)), via the Möbius map `φ(w) = (w + i)/(1 + iw)`
(`D → ℍ`, `(-1,1) → S_1`, `∂D → ℝ ∪ ∞`) and `fejerRiesz_disc` for `h = (G ∘ φ) φ'`, which is continuous on the closed
disc because of the decay (`hpTransport_diffContOnCl`; at the pole `w = i` it tends to `0`).  The two changes of variable
are `integral_diam_hpTransport` (`x = tan γ`) and `integral_circle_hpTransport` (`w = -i e^{2iβ}`, `t = tan β`).
The decay `(1+|z|)^{-3}` is only for continuity at `w = i`; a polynomially growing `G` with `L¹` boundary values is handled
in `HardyArcDecay` by the approximants `G (1 - iδz)^{-K}`.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace FormalResearch.Hardy


/-- The Möbius map `D → ℍ`, `φ(w) = (w + i)/(1 + i w)`. -/
noncomputable def hpPhi (w : ℂ) : ℂ := (w + I) / (1 + I * w)

/-- The transported function `h = (G ∘ φ) φ'` with `φ'(w) = 2/(1 + i w)²`. -/
noncomputable def hpTransport (G : ℂ → ℂ) (w : ℂ) : ℂ := G (hpPhi w) * (2 / (1 + I * w) ^ 2)

lemma one_add_I_mul_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1 + I * w ≠ 0 := by
  intro h
  have : I * w = -1 := by linear_combination h
  have h2 := congrArg norm this
  simp at h2
  linarith

lemma norm_one_add_I_mul (w : ℂ) : ‖1 + I * w‖ = ‖w - I‖ := by
  have : 1 + I * w = I * (w - I) := by ring_nf; simp [Complex.I_sq]; ring
  rw [this, norm_mul, Complex.norm_I, one_mul]

lemma hpPhi_im {w : ℂ} (hw : 1 + I * w ≠ 0) :
    (hpPhi w).im = (1 - ‖w‖ ^ 2) / ‖1 + I * w‖ ^ 2 := by
  unfold hpPhi
  have hn : ‖1 + I * w‖ ^ 2 ≠ 0 := by positivity
  rw [Complex.div_im]
  simp only [Complex.sq_norm, Complex.normSq_apply] at hn ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  field_simp
  ring

lemma hpPhi_im_nonneg {w : ℂ} (hw : 1 + I * w ≠ 0) (h1 : ‖w‖ ≤ 1) : 0 ≤ (hpPhi w).im := by
  rw [hpPhi_im hw]
  have : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  positivity

lemma hpPhi_im_pos {w : ℂ} (h1 : ‖w‖ < 1) : 0 < (hpPhi w).im := by
  rw [hpPhi_im (one_add_I_mul_ne_zero h1)]
  have : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have := norm_pos_iff.2 (one_add_I_mul_ne_zero h1)
  positivity

lemma hpTransport_I (G : ℂ → ℂ) : hpTransport G I = 0 := by
  simp [hpTransport, hpPhi]

lemma isOpen_im_pos : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im

lemma hpTransport_norm_le {G : ℂ → ℂ} {C : ℝ} (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ * (1 + ‖z‖) ^ 3 ≤ C)
    {w : ℂ} (hw : ‖w‖ ≤ 1) (hwI : w ≠ I) (hwI' : w ≠ -I) :
    ‖hpTransport G w‖ ≤ 2 * C * ‖w - I‖ / ‖w + I‖ ^ 3 := by
  have hd : 1 + I * w ≠ 0 := by
    intro h; apply hwI
    have : I * w = -1 := by linear_combination h
    have h2 : w = I := by
      have := congrArg (fun x => -I * x) this
      simp only [neg_mul, ← mul_assoc, Complex.I_mul_I] at this
      linear_combination this
    exact h2
  have hn1 : 0 < ‖w - I‖ := norm_pos_iff.2 (sub_ne_zero.2 hwI)
  have hn2 : 0 < ‖w + I‖ := norm_pos_iff.2 (by
    intro h; apply hwI'; linear_combination h)
  have him := hpPhi_im_nonneg hd hw
  have hG := hC _ him
  have hz : ‖hpPhi w‖ = ‖w + I‖ / ‖w - I‖ := by
    rw [hpPhi, norm_div, norm_one_add_I_mul]
  have hzpos : 0 < ‖hpPhi w‖ := by rw [hz]; positivity
  have h1 : ‖G (hpPhi w)‖ ≤ C / ‖hpPhi w‖ ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    refine le_trans ?_ hG
    have : ‖hpPhi w‖ ^ 3 ≤ (1 + ‖hpPhi w‖) ^ 3 := by
      apply pow_le_pow_left₀ hzpos.le; linarith
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  unfold hpTransport
  rw [norm_mul, norm_div, norm_pow, norm_one_add_I_mul]
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e2]
  calc ‖G (hpPhi w)‖ * (2 / ‖w - I‖ ^ 2) ≤ (C / ‖hpPhi w‖ ^ 3) * (2 / ‖w - I‖ ^ 2) := by
        gcongr
    _ = 2 * C * ‖w - I‖ / ‖w + I‖ ^ 3 := by
        rw [hz]; field_simp

lemma hpTransport_diffContOnCl {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im})
    {C : ℝ} (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ * (1 + ‖z‖) ^ 3 ≤ C) :
    DiffContOnCl ℂ (hpTransport G) (ball 0 1) := by
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hnu : ∀ w : ℂ, w ≠ I → 1 + I * w ≠ 0 := by
    intro w hw h; apply hw
    have : I * w = -1 := by linear_combination h
    have := congrArg (fun x => -I * x) this
    simp only [neg_mul, ← mul_assoc, Complex.I_mul_I] at this
    linear_combination this
  refine ⟨?_, ?_⟩
  · intro w hw
    have hw1 : ‖w‖ < 1 := by simpa using hw
    have hd := one_add_I_mul_ne_zero hw1
    have hphi : DifferentiableAt ℂ hpPhi w := by
      unfold hpPhi; exact (differentiableAt_id.add_const I).div (by fun_prop) hd
    have hGd : DifferentiableAt ℂ G (hpPhi w) :=
      hG.1.differentiableAt (isOpen_im_pos.mem_nhds (hpPhi_im_pos hw1))
    unfold hpTransport
    refine (hGd.comp w hphi).mul ?_ |>.differentiableWithinAt
    exact (differentiableAt_const _).div (by fun_prop) (pow_ne_zero 2 hd)
  · rw [hcl]
    intro w hw
    have hw1 : ‖w‖ ≤ 1 := by simpa using hw
    by_cases hwI : w = I
    · subst hwI
      rw [ContinuousWithinAt, hpTransport_I]
      have hC0 : 0 ≤ C := by
        have := hC 0 (by simp)
        simp at this
        exact le_trans (norm_nonneg _) this
      have hb : ∀ᶠ w in 𝓝[closedBall (0 : ℂ) 1] I, ‖hpTransport G w‖ ≤ 2 * C * ‖w - I‖ := by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds I one_pos)] with
          w hwcb hwb
        have hw1' : ‖w‖ ≤ 1 := by simpa using hwcb
        have hwb' : ‖w - I‖ < 1 := by rw [← dist_eq_norm]; exact hwb
        by_cases hwI : w = I
        · subst hwI; simp [hpTransport_I]
        · have hwI' : w ≠ -I := by
            intro h; rw [h] at hwb'
            have : ‖(-I : ℂ) - I‖ = 2 := by
              have : (-I : ℂ) - I = -(2 * I) := by ring
              rw [this, norm_neg, norm_mul]; simp
            linarith
          have h1 := hpTransport_norm_le hC hw1' hwI hwI'
          have h2 : 1 ≤ ‖w + I‖ := by
            have : ‖(2 * I : ℂ)‖ ≤ ‖w + I‖ + ‖w - I‖ := by
              have := norm_sub_le (w + I) (w - I)
              have e : (w + I) - (w - I) = 2 * I := by ring
              rw [e] at this
              have e2 : ‖w + I - (w - I)‖ = ‖(2 * I : ℂ)‖ := by rw [e]
              calc ‖(2 * I : ℂ)‖ = ‖w + I - (w - I)‖ := e2.symm
                _ ≤ ‖w + I‖ + ‖w - I‖ := norm_sub_le _ _
            have e3 : ‖(2 * I : ℂ)‖ = 2 := by simp
            linarith
          have h3 : 2 * C * ‖w - I‖ / ‖w + I‖ ^ 3 ≤ 2 * C * ‖w - I‖ := by
            rw [div_le_iff₀ (by positivity)]
            have : 1 ≤ ‖w + I‖ ^ 3 := one_le_pow₀ h2
            have h4 : 0 ≤ 2 * C * ‖w - I‖ := by positivity
            nlinarith
          exact h1.trans h3
      have ha : Tendsto (fun w : ℂ => 2 * C * ‖w - I‖) (𝓝[closedBall (0 : ℂ) 1] I) (𝓝 0) := by
        have : Tendsto (fun w : ℂ => 2 * C * ‖w - I‖) (𝓝 I) (𝓝 (2 * C * ‖I - I‖)) :=
          ((continuous_const.mul (continuous_norm.comp (continuous_id.sub continuous_const))).tendsto I)
        simp only [sub_self, norm_zero, mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact squeeze_zero_norm' hb ha
    · have hd := hnu w hwI
      have hphi : ContinuousAt hpPhi w := by
        unfold hpPhi; exact (continuousAt_id.add continuousAt_const).div (by fun_prop) hd
      have hGc : ContinuousWithinAt G {z : ℂ | 0 ≤ z.im} (hpPhi w) := by
        have := hG.2 (hpPhi w) (by rw [closure_setOfPred_lt_im]; exact hpPhi_im_nonneg hd hw1)
        rwa [closure_setOfPred_lt_im] at this
      unfold hpTransport
      refine ContinuousWithinAt.mul ?_ ?_
      · refine ContinuousWithinAt.comp (g := G) hGc hphi.continuousWithinAt ?_
        intro v hv
        have hv1 : ‖v‖ ≤ 1 := by simpa using hv
        by_cases hvI : v = I
        · subst hvI; simp [hpPhi]
        · exact hpPhi_im_nonneg (hnu v hvI) hv1
      · have hden : ContinuousAt (fun v : ℂ => (1 + I * v) ^ 2) w := by fun_prop
        exact ((continuousAt_const).div hden (pow_ne_zero 2 hd)).continuousWithinAt

lemma circleMap_one_two_sub (β : ℝ) :
    circleMap 0 1 (2 * β - π / 2) =
      ((Real.sin (2 * β) : ℝ) : ℂ) - I * ((Real.cos (2 * β) : ℝ) : ℂ) := by
  rw [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.exp_mul_I]
  have h1 : Complex.cos ((2 * β - π / 2 : ℝ) : ℂ) = ((Real.sin (2 * β) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos, show 2 * β - π / 2 = -(π / 2 - 2 * β) by ring, Real.cos_neg, Real.cos_pi_div_two_sub]
  have h2 : Complex.sin ((2 * β - π / 2 : ℝ) : ℂ) = -((Real.cos (2 * β) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, show 2 * β - π / 2 = -(π / 2 - 2 * β) by ring, Real.sin_neg, Real.sin_pi_div_two_sub]
    push_cast; ring
  push_cast at h1 h2 ⊢
  rw [h1, h2]; ring

lemma hpPhi_circle (β : ℝ) (hc : Real.cos β ≠ 0) :
    hpPhi (circleMap 0 1 (2 * β - π / 2)) = (Real.tan β : ℂ) := by
  rw [circleMap_one_two_sub, hpPhi]
  have hcC : (Real.cos β : ℂ) ≠ 0 := by exact_mod_cast hc
  have hs2 : (Real.sin (2 * β) : ℂ) = 2 * Real.sin β * Real.cos β := by
    rw [Real.sin_two_mul]; push_cast; ring
  have hc2 : (Real.cos (2 * β) : ℂ) = 2 * (Real.cos β) ^ 2 - 1 := by
    rw [Real.cos_two_mul]; push_cast; ring
  have hpy : (Real.sin β : ℂ) ^ 2 + (Real.cos β : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq β
  have hu : (Real.cos β : ℂ) + I * (Real.sin β : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hc this
  have hden : 1 + I * (((Real.sin (2 * β) : ℝ) : ℂ) - I * ((Real.cos (2 * β) : ℝ) : ℂ)) =
      2 * (Real.cos β : ℂ) * ((Real.cos β : ℂ) + I * (Real.sin β : ℂ)) := by
    rw [hs2, hc2]
    linear_combination (-(2 * (Real.cos β : ℂ) ^ 2 - 1)) * Complex.I_sq
  have hnum : (((Real.sin (2 * β) : ℝ) : ℂ) - I * ((Real.cos (2 * β) : ℝ) : ℂ)) + I =
      2 * (Real.sin β : ℂ) * ((Real.cos β : ℂ) + I * (Real.sin β : ℂ)) := by
    rw [hs2, hc2]
    linear_combination (-2 * I) * hpy
  rw [hden, hnum, Real.tan_eq_sin_div_cos, Complex.ofReal_div]
  have hu' : (Real.cos β : ℂ) + (Real.sin β : ℂ) * I ≠ 0 := by rwa [mul_comm] at hu
  field_simp

lemma norm_one_add_I_circle (β : ℝ) (hc : 0 < Real.cos β) :
    ‖1 + I * circleMap 0 1 (2 * β - π / 2)‖ = 2 * Real.cos β := by
  rw [circleMap_one_two_sub]
  have hs2 : (Real.sin (2 * β) : ℂ) = 2 * Real.sin β * Real.cos β := by
    rw [Real.sin_two_mul]; push_cast; ring
  have hc2 : (Real.cos (2 * β) : ℂ) = 2 * (Real.cos β) ^ 2 - 1 := by
    rw [Real.cos_two_mul]; push_cast; ring
  have hden : 1 + I * (((Real.sin (2 * β) : ℝ) : ℂ) - I * ((Real.cos (2 * β) : ℝ) : ℂ)) =
      2 * (Real.cos β : ℂ) * ((Real.cos β : ℂ) + I * (Real.sin β : ℂ)) := by
    rw [hs2, hc2]
    linear_combination (-(2 * (Real.cos β : ℂ) ^ 2 - 1)) * Complex.I_sq
  rw [hden, norm_mul, norm_mul]
  have h1 : ‖(Real.cos β : ℂ) + I * (Real.sin β : ℂ)‖ = 1 := by
    have : (Real.cos β : ℂ) + I * (Real.sin β : ℂ) = Complex.exp ((β : ℂ) * I) := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h1, Complex.norm_real, Real.norm_of_nonneg hc.le]
  simp

lemma hpTransport_circle_norm (G : ℂ → ℂ) {β : ℝ} (hβ : β ∈ Ioo (-(π / 2)) (π / 2)) :
    ‖hpTransport G (circleMap 0 1 (2 * β - π / 2))‖ = ‖G (Real.tan β : ℂ)‖ / (2 * Real.cos β ^ 2) := by
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo hβ
  unfold hpTransport
  rw [hpPhi_circle β hc.ne', norm_mul, norm_div, norm_pow, norm_one_add_I_circle β hc]
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e2]
  field_simp

/-- Change of variables on the circle: the boundary integral of the transported function is `∫_ℝ ‖G‖`. -/
theorem integral_circle_hpTransport (G : ℂ → ℂ) :
    ∫ θ in (-π)..π, ‖hpTransport G (circleMap 0 1 θ)‖ = ∫ t : ℝ, ‖G (t : ℂ)‖ := by
  set F : ℝ → ℝ := fun θ => ‖hpTransport G (circleMap 0 1 θ)‖ with hF
  have hper : Function.Periodic F (2 * π) := fun θ => by
    simp only [hF]; rw [periodic_circleMap]
  have h1 : ∫ θ in (-π)..π, F θ = ∫ θ in (-(3 * π / 2))..(π / 2), F θ := by
    have := hper.intervalIntegral_add_eq (-π) (-(3 * π / 2))
    convert this using 2 <;> ring
  have h2 : ∫ θ in (-(3 * π / 2))..(π / 2), F θ = 2 * ∫ β in (-(π / 2))..(π / 2), F (2 * β - π / 2) := by
    have := intervalIntegral.integral_comp_mul_sub (a := -(π / 2)) (b := π / 2) F (two_ne_zero) (π / 2)
    rw [smul_eq_mul] at this
    have e1 : (2 : ℝ) * -(π / 2) - π / 2 = -(3 * π / 2) := by ring
    have e2 : (2 : ℝ) * (π / 2) - π / 2 = π / 2 := by ring
    rw [e1, e2] at this
    rw [this]; field_simp
  have h3 : ∫ β in (-(π / 2))..(π / 2), F (2 * β - π / 2) =
      ∫ β in Ioo (-(π / 2)) (π / 2), ‖G (Real.tan β : ℂ)‖ / (2 * Real.cos β ^ 2) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun β hβ => ?_
    exact hpTransport_circle_norm G hβ
  have h4 : ∫ t : ℝ, ‖G (t : ℂ)‖ = ∫ β in Ioo (-(π / 2)) (π / 2), |1 / Real.cos β ^ 2| • ‖G (Real.tan β : ℂ)‖ := by
    have := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioo (-(π / 2)) (π / 2))
      (f := Real.tan) (f' := fun β => 1 / Real.cos β ^ 2) measurableSet_Ioo
      (fun β hβ => (Real.hasDerivAt_tan (Real.cos_pos_of_mem_Ioo hβ).ne').hasDerivWithinAt)
      Real.strictMonoOn_tan.injOn (fun t => ‖G (t : ℂ)‖)
    rw [Real.image_tan_Ioo, Measure.restrict_univ] at this
    exact this
  rw [h1, h2, h3, h4]
  have : ∀ β ∈ Ioo (-(π / 2)) (π / 2), 2 * (‖G (Real.tan β : ℂ)‖ / (2 * Real.cos β ^ 2)) =
      |1 / Real.cos β ^ 2| • ‖G (Real.tan β : ℂ)‖ := by
    intro β hβ
    have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo hβ
    rw [abs_of_pos (by positivity), smul_eq_mul]
    field_simp
  rw [← MeasureTheory.integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioo this

lemma circleMap_one_pi_div_two_sub (γ : ℝ) :
    circleMap 0 1 (π / 2 - 2 * γ) =
      ((Real.sin (2 * γ) : ℝ) : ℂ) + I * ((Real.cos (2 * γ) : ℝ) : ℂ) := by
  rw [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.exp_mul_I]
  have h1 : Complex.cos ((π / 2 - 2 * γ : ℝ) : ℂ) = ((Real.sin (2 * γ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos, Real.cos_pi_div_two_sub]
  have h2 : Complex.sin ((π / 2 - 2 * γ : ℝ) : ℂ) = ((Real.cos (2 * γ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, Real.sin_pi_div_two_sub]
  rw [h1, h2]; ring

lemma hpPhi_tan (γ : ℝ) (hc : Real.cos γ ≠ 0) :
    hpPhi (Real.tan γ : ℂ) = circleMap 0 1 (π / 2 - 2 * γ) := by
  rw [circleMap_one_pi_div_two_sub, hpPhi]
  have hcC : (Real.cos γ : ℂ) ≠ 0 := by exact_mod_cast hc
  have hs2 : (Real.sin (2 * γ) : ℂ) = 2 * Real.sin γ * Real.cos γ := by
    rw [Real.sin_two_mul]; push_cast; ring
  have hc2 : (Real.cos (2 * γ) : ℂ) = 2 * (Real.cos γ) ^ 2 - 1 := by
    rw [Real.cos_two_mul]; push_cast; ring
  have hpy : (Real.sin γ : ℂ) ^ 2 + (Real.cos γ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq γ
  have hu : (Real.cos γ : ℂ) + I * (Real.sin γ : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hc this
  have hden : 1 + I * (Real.tan γ : ℂ) = ((Real.cos γ : ℂ) + I * (Real.sin γ : ℂ)) / (Real.cos γ : ℂ) := by
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    field_simp
  rw [hden, hs2, hc2, Real.tan_eq_sin_div_cos, Complex.ofReal_div]
  rw [div_eq_iff (div_ne_zero hu hcC)]
  field_simp
  linear_combination (-2 * I * (Real.cos γ : ℂ)) * hpy + (-(Real.sin γ : ℂ) * (2 * (Real.cos γ : ℂ) ^ 2 - 1)) * Complex.I_sq

lemma norm_one_add_I_tan (γ : ℝ) (hc : 0 < Real.cos γ) : ‖1 + I * (Real.tan γ : ℂ)‖ = 1 / Real.cos γ := by
  have hcC : (Real.cos γ : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have : 1 + I * (Real.tan γ : ℂ) = ((Real.cos γ : ℂ) + I * (Real.sin γ : ℂ)) / (Real.cos γ : ℂ) := by
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    field_simp
  rw [this, norm_div]
  have h1 : ‖(Real.cos γ : ℂ) + I * (Real.sin γ : ℂ)‖ = 1 := by
    have : (Real.cos γ : ℂ) + I * (Real.sin γ : ℂ) = Complex.exp ((γ : ℂ) * I) := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h1, Complex.norm_real, Real.norm_of_nonneg hc.le]

lemma image_tan_Ioo_quarter : Real.tan '' Ioo (-(π / 4)) (π / 4) = Ioo (-1) 1 := by
  have hmono := Real.strictMonoOn_tan
  have hsub : Ioo (-(π / 4)) (π / 4) ⊆ Ioo (-(π / 2)) (π / 2) := fun x hx =>
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  ext x
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have h1 : Real.tan (-(π / 4)) < Real.tan γ :=
      hmono (⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ : -(π / 4) ∈ Ioo (-(π / 2)) (π / 2))
        (hsub hγ) hγ.1
    have h2 : Real.tan γ < Real.tan (π / 4) :=
      hmono (hsub hγ) (⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ : π / 4 ∈ Ioo (-(π / 2)) (π / 2))
        hγ.2
    rw [Real.tan_neg, Real.tan_pi_div_four] at h1
    rw [Real.tan_pi_div_four] at h2
    exact ⟨h1, h2⟩
  · intro hx
    refine ⟨Real.arctan x, ⟨?_, ?_⟩, Real.tan_arctan x⟩
    · have := Real.arctan_strictMono hx.1
      rw [Real.arctan_neg, Real.arctan_one] at this
      exact this
    · have := Real.arctan_strictMono hx.2
      rw [Real.arctan_one] at this
      exact this

/-- Change of variables on the diameter: the integral of the transported function over `(-1,1)` is the arc integral. -/
theorem integral_diam_hpTransport (G : ℂ → ℂ) :
    ∫ x in (-1 : ℝ)..1, ‖hpTransport G (x : ℂ)‖ = ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 1 φ)‖ := by
  have h1 : ∫ x in (-1 : ℝ)..1, ‖hpTransport G (x : ℂ)‖ = ∫ x in Ioo (-1 : ℝ) 1, ‖hpTransport G (x : ℂ)‖ := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  have hsub : Ioo (-(π / 4)) (π / 4) ⊆ Ioo (-(π / 2)) (π / 2) := fun x hx =>
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have h2 : ∫ x in Ioo (-1 : ℝ) 1, ‖hpTransport G (x : ℂ)‖ =
      ∫ γ in Ioo (-(π / 4)) (π / 4), |1 / Real.cos γ ^ 2| • ‖hpTransport G (Real.tan γ : ℂ)‖ := by
    rw [← image_tan_Ioo_quarter]
    exact MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioo (-(π / 4)) (π / 4))
      (f := Real.tan) (f' := fun γ => 1 / Real.cos γ ^ 2) measurableSet_Ioo
      (fun γ hγ => (Real.hasDerivAt_tan (Real.cos_pos_of_mem_Ioo (hsub hγ)).ne').hasDerivWithinAt)
      (Real.strictMonoOn_tan.injOn.mono hsub) (fun x => ‖hpTransport G (x : ℂ)‖)
  have h3 : ∀ γ ∈ Ioo (-(π / 4)) (π / 4), |1 / Real.cos γ ^ 2| • ‖hpTransport G (Real.tan γ : ℂ)‖ =
      2 * ‖G (circleMap 0 1 (π / 2 - 2 * γ))‖ := by
    intro γ hγ
    have hc : 0 < Real.cos γ := Real.cos_pos_of_mem_Ioo (hsub hγ)
    unfold hpTransport
    rw [hpPhi_tan γ hc.ne', norm_mul, norm_div, norm_pow, norm_one_add_I_tan γ hc, abs_of_pos (by positivity),
      smul_eq_mul]
    have e2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [e2]
    field_simp
  have h4 : ∫ γ in Ioo (-(π / 4)) (π / 4), |1 / Real.cos γ ^ 2| • ‖hpTransport G (Real.tan γ : ℂ)‖ =
      ∫ γ in (-(π / 4))..(π / 4), 2 * ‖G (circleMap 0 1 (π / 2 - 2 * γ))‖ := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo h3
  have h5 : ∫ γ in (-(π / 4))..(π / 4), ‖G (circleMap 0 1 (π / 2 - 2 * γ))‖ =
      (1 / 2) * ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 1 φ)‖ := by
    have := intervalIntegral.integral_comp_mul_sub (a := -(π / 4)) (b := π / 4)
      (fun φ => ‖G (circleMap 0 1 φ)‖) (c := -2) (by norm_num) (-(π / 2))
    have e0 : ∀ γ : ℝ, -2 * γ - -(π / 2) = π / 2 - 2 * γ := fun γ => by ring
    simp only [e0] at this
    have e1 : π / 2 - 2 * -(π / 4) = π := by ring
    have e2 : π / 2 - 2 * (π / 4) = 0 := by ring
    rw [e1, e2, smul_eq_mul, intervalIntegral.integral_symm (0 : ℝ) π] at this
    rw [this]; ring
  rw [h1, h2, h4, intervalIntegral.integral_const_mul, h5]
  ring


/-- **Fejér–Riesz arc inequality** for the unit semicircle. -/
theorem hardy_arc_one {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ * (1 + ‖z‖) ^ 3 ≤ C) :
    ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 1 φ)‖ ≤ (1 / 2) * ∫ t : ℝ, ‖G (t : ℂ)‖ := by
  have := fejerRiesz_disc (hpTransport_diffContOnCl hG hC)
  rwa [integral_diam_hpTransport, integral_circle_hpTransport] at this

/-- Dilation `z ↦ a G(a z)` preserves the hypotheses of `hardy_arc_one`. -/
lemma diffContOnCl_scale {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {a : ℝ} (ha : 0 < a) :
    DiffContOnCl ℂ (fun z => (a : ℂ) * G ((a : ℂ) * z)) {z : ℂ | 0 < z.im} := by
  have hmaps : ∀ z : ℂ, 0 < z.im → 0 < ((a : ℂ) * z).im := fun z hz => by
    simp [Complex.mul_im, hz, ha]
  have hmaps' : ∀ z : ℂ, 0 ≤ z.im → 0 ≤ ((a : ℂ) * z).im := fun z hz => by
    simp [Complex.mul_im]; positivity
  refine ⟨?_, ?_⟩
  · intro z hz
    have h1 : DifferentiableAt ℂ G ((a : ℂ) * z) :=
      hG.1.differentiableAt (isOpen_im_pos.mem_nhds (hmaps z hz))
    exact ((differentiableAt_const _).mul (h1.comp z (by fun_prop))).differentiableWithinAt
  · rw [closure_setOfPred_lt_im]
    intro z hz
    have hz' : 0 ≤ z.im := hz
    have h1 : ContinuousWithinAt G {z : ℂ | 0 ≤ z.im} ((a : ℂ) * z) := by
      have := hG.2 ((a : ℂ) * z) (by rw [closure_setOfPred_lt_im]; exact hmaps' z hz')
      rwa [closure_setOfPred_lt_im] at this
    refine continuousWithinAt_const.mul ?_
    exact h1.comp (f := fun z : ℂ => (a : ℂ) * z) (by fun_prop) (fun v hv => hmaps' v hv)

/-- **Fejér–Riesz arc inequality** for the semicircle `S_a = {|z| = a, Im z > 0}`:
`∫_{S_a} ‖G‖ |dz| = a ∫_0^π ‖G(a e^{iφ})‖ dφ ≤ (1/2) ∫_ℝ ‖G‖`. -/
theorem hardy_arc_le {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ * (1 + ‖z‖) ^ 3 ≤ C) {a : ℝ} (ha : 0 < a) :
    a * ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ)‖ ≤ (1 / 2) * ∫ t : ℝ, ‖G (t : ℂ)‖ := by
  have hC' : ∀ z : ℂ, 0 ≤ z.im →
      ‖(a : ℂ) * G ((a : ℂ) * z)‖ * (1 + ‖z‖) ^ 3 ≤ a * max 1 a⁻¹ ^ 3 * C := by
    intro z hz
    have him : 0 ≤ ((a : ℂ) * z).im := by simp [Complex.mul_im]; positivity
    have h1 := hC _ him
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
    have h2 : 1 + ‖z‖ ≤ max 1 a⁻¹ * (1 + ‖(a : ℂ) * z‖) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
      rcases le_total 1 a⁻¹ with h | h
      · rw [max_eq_right h]
        have : ‖z‖ = a⁻¹ * (a * ‖z‖) := by field_simp
        nlinarith [norm_nonneg z, mul_nonneg ha.le (norm_nonneg z)]
      · rw [max_eq_left h]
        have : a⁻¹ ≤ 1 := h
        have : 1 ≤ a := by
          by_contra hlt; push Not at hlt
          have := (one_lt_inv₀ ha).2 hlt
          linarith
        nlinarith [norm_nonneg z, mul_nonneg ha.le (norm_nonneg z)]
    have h3 : (1 + ‖z‖) ^ 3 ≤ (max 1 a⁻¹) ^ 3 * (1 + ‖(a : ℂ) * z‖) ^ 3 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 3
    calc a * ‖G ((a : ℂ) * z)‖ * (1 + ‖z‖) ^ 3
        ≤ a * ‖G ((a : ℂ) * z)‖ * ((max 1 a⁻¹) ^ 3 * (1 + ‖(a : ℂ) * z‖) ^ 3) := by gcongr
      _ = a * (max 1 a⁻¹) ^ 3 * (‖G ((a : ℂ) * z)‖ * (1 + ‖(a : ℂ) * z‖) ^ 3) := by ring
      _ ≤ a * (max 1 a⁻¹) ^ 3 * C := by gcongr
  have key := hardy_arc_one (diffContOnCl_scale hG ha) hC'
  have e1 : ∀ φ : ℝ, ‖(a : ℂ) * G ((a : ℂ) * circleMap 0 1 φ)‖ = a * ‖G (circleMap 0 a φ)‖ := by
    intro φ
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
    congr 2
    simp [circleMap]
  have e2 : ∫ t : ℝ, ‖(a : ℂ) * G ((a : ℂ) * (t : ℂ))‖ = ∫ t : ℝ, ‖G (t : ℂ)‖ := by
    have : ∀ t : ℝ, ‖(a : ℂ) * G ((a : ℂ) * (t : ℂ))‖ = a * ‖G (((a * t : ℝ)) : ℂ)‖ := by
      intro t
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]; push_cast; rfl
    simp_rw [this]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ => ‖G (t : ℂ)‖) a]
    rw [abs_of_pos (inv_pos.2 ha), smul_eq_mul]
    field_simp
  simp_rw [e1] at key
  rw [intervalIntegral.integral_const_mul, e2] at key
  exact key

/-- info: 'FormalResearch.Hardy.hardy_arc_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_arc_le

end FormalResearch.Hardy
