module

public import FormalResearch.SignUncertainty.CtOuterThird
public import FormalResearch.SignUncertainty.CtOuterU2Zero
public import FormalResearch.SignUncertainty.CtOuter

/-!
# `θ_3^-` as an integral, and the splitting `c_{3,h} = c_{3,mp} + c_{3,1t2}'`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (2), paragraph on `c_{3,h}`.  **Proved.**

`θ_-'''(0) = ∫_ℝ (u_r''(t) - u_r''(0)) π cosh(πt)/sinh²(πt) dt + 2`, and for `t > 0`
`u_r''(t) - u_r''(0) = ½ (L''(t) + 7π²/30) + (3t² + t⁴)/(1+t²)²` with `L = log(m'(t)/t)`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `L'' = 2 u_r'' + 2(1-t²)/(1+t²)²` for `L(t) = log(m'(t)/t)`, `t > 0`. -/
lemma deriv2_logM {t : ℝ} (ht : 0 < t) :
    deriv (deriv fun s : ℝ => Real.log (mPrime s / s)) t = 2 * uR2 t + 2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2 := by
  have hL : ∀ s : ℝ, 0 < s → Real.log (mPrime s / s) =
      2 * uR s - Real.log (6 / π ^ 2) + Real.log (1 + s ^ 2) := by
    intro s hs
    have hN := mPrime_pos hs
    rw [uR_eq_log hs, Real.log_div hN.ne' hs.ne']
    ring
  have hev : (fun s : ℝ => Real.log (mPrime s / s)) =ᶠ[𝓝 t]
      fun s : ℝ => 2 * uR s - Real.log (6 / π ^ 2) + Real.log (1 + s ^ 2) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using hL s hs
  have hd1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 2 * uR s - Real.log (6 / π ^ 2) + Real.log (1 + s ^ 2))
      (2 * uR1 s + 2 * s / (1 + s ^ 2)) s := fun s => by
    have h3 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * s) s := by
      simpa using ((hasDerivAt_pow 2 s).const_add 1)
    have h4 := h3.log (by positivity)
    exact ((((hasDerivAt_uR s).const_mul 2).sub_const _).add h4).congr_deriv (by ring)
  have e1 : deriv (fun s : ℝ => Real.log (mPrime s / s)) =ᶠ[𝓝 t] fun s : ℝ => 2 * uR1 s + 2 * s / (1 + s ^ 2) := by
    have := hev.deriv
    filter_upwards [this] with s hs
    rw [hs]; exact (hd1 s).deriv
  have hd2 : HasDerivAt (fun s : ℝ => 2 * uR1 s + 2 * s / (1 + s ^ 2)) (2 * uR2 t + 2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
    have h4 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1)
    have h5 : HasDerivAt (fun s : ℝ => 2 * s / (1 + s ^ 2)) (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2) t :=
      (((hasDerivAt_id t).const_mul 2).div h4 (by positivity)).congr_deriv (by
        simp only [id]; field_simp; ring)
    exact (((hasDerivAt_uR1 t).const_mul 2).add h5).congr_deriv (by ring)
  exact ((hd2.congr_of_eventuallyEq e1)).deriv


/-- `K̂(t) = cosh(πt)/sinh²(πt)`. -/
noncomputable def Khat (t : ℝ) : ℝ := Real.cosh (π * t) / Real.sinh (π * t) ^ 2

lemma thetaK_eq (t : ℝ) : thetaK t = π * Khat t := by
  unfold thetaK Khat; ring

lemma thetaK_neg (t : ℝ) : thetaK (-t) = thetaK t := by
  unfold thetaK; simp only [mul_neg, Real.cosh_neg, Real.sinh_neg, neg_sq]

lemma Khat_neg (t : ℝ) : Khat (-t) = Khat t := by
  unfold Khat; simp only [mul_neg, Real.cosh_neg, Real.sinh_neg, neg_sq]

/-- `g(t) = 1 - (1-t²)/(1+t²)² = (3t² + t⁴)/(1+t²)²`. -/
noncomputable def gC (t : ℝ) : ℝ := 1 - (1 - t ^ 2) / (1 + t ^ 2) ^ 2

lemma gC_eq (t : ℝ) : gC t = (3 * t ^ 2 + t ^ 4) / (1 + t ^ 2) ^ 2 := by
  unfold gC
  have : (1 + t ^ 2) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma continuous_gC : Continuous gC := by
  unfold gC
  exact continuous_const.sub (Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity))

lemma gC_nonneg (t : ℝ) : 0 ≤ gC t := by
  rw [gC_eq]; positivity

lemma gC_le (t : ℝ) : gC t ≤ 2 := by
  unfold gC
  have h0 : 0 < (1 + t ^ 2) ^ 2 := by positivity
  have : |1 - t ^ 2| ≤ (1 + t ^ 2) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith only [sq_nonneg t, sq_nonneg (t ^ 2)]
  have h2 : -1 ≤ (1 - t ^ 2) / (1 + t ^ 2) ^ 2 := by
    rw [le_div_iff₀ h0]; linarith only [(abs_le.mp this).1]
  linarith only [h2]

lemma gC_quad : ∀ t : ℝ, |t| ≤ 1 / 2 → |gC t| ≤ 4 * t ^ 2 := by
  intro t ht
  rw [abs_of_nonneg (gC_nonneg t), gC_eq, div_le_iff₀ (by positivity)]
  have h1 : t ^ 2 ≤ 1 := by nlinarith only [abs_le.mp ht, sq_abs t, abs_nonneg t]
  have h2 : t ^ 4 ≤ t ^ 2 := by nlinarith only [h1, sq_nonneg t]
  have h3 : 1 ≤ (1 + t ^ 2) ^ 2 := by nlinarith only [sq_nonneg t]
  nlinarith only [h2, h3, sq_nonneg t]

lemma expBdd_gC : ExpBdd gC := by
  refine ⟨2, fun t => ?_⟩
  have h4 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  rw [abs_of_nonneg (gC_nonneg t)]
  nlinarith only [gC_le t, h4]

/-- The pointwise splitting `u_r'' - u_r''(0) = ½ (L'' + 7π²/30) + g` for `t > 0`. -/
lemma uR2_sub_split {t : ℝ} (ht : 0 < t) :
    uR2 t - uR2 0 = (1 / 2) * (deriv (deriv fun s : ℝ => Real.log (mPrime s / s)) t + 7 * π ^ 2 / 30) + gC t := by
  rw [deriv2_logM ht, uR2_zero]
  unfold gC
  ring


lemma measurable_thetaK : Measurable thetaK := by
  unfold thetaK
  exact (by fun_prop : Measurable fun t : ℝ => π * Real.cosh (π * t)).div (by fun_prop)

lemma measurable_Khat : Measurable Khat := by
  unfold Khat
  exact (by fun_prop : Measurable fun t : ℝ => Real.cosh (π * t)).div (by fun_prop)

lemma integrable_amp_thetaK' {w : ℝ → ℝ} (hw : Continuous w) (hb : ExpBdd w)
    (hn : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 / 2 → |w t| ≤ C * t ^ 2) :
    Integrable fun t : ℝ => w t * thetaK t := by
  have h := integrable_amp_thetaK hw hb hn
  refine Integrable.mono' h ((hw.measurable.mul measurable_thetaK).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (thetaK_nonneg t)]

lemma integrableOn_amp_Khat {w : ℝ → ℝ} (hw : Continuous w) (hb : ExpBdd w)
    (hn : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 / 2 → |w t| ≤ C * t ^ 2) :
    IntegrableOn (fun t : ℝ => w t * Khat t) (Ioi 0) := by
  have h := (integrable_amp_thetaK' hw hb hn).const_mul (1 / π)
  refine (h.integrableOn (s := Ioi (0 : ℝ))).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [thetaK_eq]
  have := Real.pi_pos.ne'
  field_simp

lemma integral_even_thetaK {w : ℝ → ℝ} (hw : ∀ t, w (-t) = w t) :
    ∫ t : ℝ, w t * thetaK t = 2 * π * ∫ t in Ioi (0 : ℝ), w t * Khat t := by
  have h := integral_comp_abs (f := fun t : ℝ => w t * thetaK t)
  have e : (fun t : ℝ => w |t| * thetaK |t|) = fun t => w t * thetaK t := by
    funext t
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hw, thetaK_neg]
  simp only [e] at h
  rw [h]
  have : ∀ t : ℝ, w t * thetaK t = π * (w t * Khat t) := fun t => by rw [thetaK_eq]; ring
  simp_rw [this]
  rw [integral_const_mul]
  ring

/-- **`θ_ε'''(0)` as an integral.** -/
theorem iteratedDeriv_three_outerTheta_P (ε : ℝ) :
    iteratedDeriv 3 (outerTheta ε) 0 =
      2 * π * (∫ t in Ioi (0 : ℝ), (uR2 t - uR2 0) * Khat t) + 2 + (if ε = 1 then π ^ 3 else 0) := by
  rw [iteratedDeriv_three_outerTheta, deriv3_H0_zero_uR, Complex.neg_re, neg_neg,
    integral_complex_ofReal, Complex.ofReal_re]
  rw [integral_even_thetaK (w := fun t => uR2 t - uR2 0) (fun t => by simp [uR2_neg])]


lemma uR2_amp_hyp : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 / 2 → |uR2 t - uR2 0| ≤ C * t ^ 2 := by
  obtain ⟨C, hC⟩ := uR2_quad
  exact ⟨C, fun t ht => hC t (by linarith [ht])⟩

lemma integrableOn_P : IntegrableOn (fun t : ℝ => (uR2 t - uR2 0) * Khat t) (Ioi 0) :=
  integrableOn_amp_Khat (continuous_uR2.sub continuous_const) (expBdd_sub_const expBdd_uR2 _) uR2_amp_hyp

lemma integrableOn_G : IntegrableOn (fun t : ℝ => gC t * Khat t) (Ioi 0) :=
  integrableOn_amp_Khat continuous_gC expBdd_gC ⟨4, gC_quad⟩

/-- `c_{3,mp} = (π/3) (P - G)` with `P = ∫₀^∞ (u_r'' - u_r''(0)) K̂`, `G = ∫₀^∞ g K̂`. -/
theorem ctC3mp_eq :
    ctC3mp = π / 3 * ((∫ t in Ioi (0 : ℝ), (uR2 t - uR2 0) * Khat t) - ∫ t in Ioi (0 : ℝ), gC t * Khat t) := by
  unfold ctC3mp
  have h : ∫ t in Ioi (0 : ℝ), (deriv (deriv fun s : ℝ => Real.log (mPrime s / s)) t + 7 * π ^ 2 / 30) *
      (Real.cosh (π * t) / Real.sinh (π * t) ^ 2) =
      ∫ t in Ioi (0 : ℝ), (2 * ((uR2 t - uR2 0) * Khat t) - 2 * (gC t * Khat t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have h1 := uR2_sub_split (show 0 < t from ht)
    unfold Khat
    rw [show deriv (deriv fun s : ℝ => Real.log (mPrime s / s)) t + 7 * π ^ 2 / 30 =
      2 * (uR2 t - uR2 0 - gC t) by linarith only [h1]]
    ring
  rw [h, integral_sub (integrableOn_P.const_mul 2) (integrableOn_G.const_mul 2), integral_const_mul,
    integral_const_mul]
  ring

/-- info: 'FormalResearch.SignUncertainty.CtOuter.iteratedDeriv_three_outerTheta_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_three_outerTheta_P

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ctC3mp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctC3mp_eq

end FormalResearch.SignUncertainty.CtOuter
