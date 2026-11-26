module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroAmpDeriv

/-!
# The elementary integrals of `a'(τ)/sinh(πτ)` (FIVE-0, `ctu:jets`, step 3)

The five elementary integrals over `(0, ∞)` entering the evaluation of `∫₀^∞ a'(τ)/sinh(πτ) dτ`: by explicit
antiderivatives with `f' ≥ 0`.  Proved.

* `∫ π/cosh(πτ) = π/2`, `∫ π/(1+cosh πτ) = 1`, `∫ π/√(c(1+c)) = √2 arsinh 1`,
* `∫ g₄ = π/2 - 1`, `∫ g₅ = 1`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma tendsto_tanh_atTop' : Tendsto Real.tanh atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun x : ℝ => 1 - Real.exp (-x))
    (h := fun _ => (1 : ℝ)) ?_ tendsto_const_nhds (fun x => ?_) (fun x => (Real.tanh_lt_one x).le)
  · have : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  · have hc := Real.cosh_pos x
    rw [Real.tanh_eq_sinh_div_cosh, le_div_iff₀ hc]
    have h1 : Real.cosh x - Real.sinh x = Real.exp (-x) := by
      rw [Real.cosh_eq, Real.sinh_eq]; ring
    have h2 : 1 ≤ Real.cosh x := Real.one_le_cosh x
    have h3 := Real.exp_pos (-x)
    nlinarith

lemma tendsto_tanh_arg {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => Real.tanh (π * t / k)) atTop (𝓝 1) := by
  have hpi := Real.pi_pos
  have : Tendsto (fun t : ℝ => π * t / k) atTop atTop :=
    (tendsto_id.const_mul_atTop (show 0 < π / k by positivity)).congr (fun t => by simp; ring)
  exact tendsto_tanh_atTop'.comp this

lemma hasDerivAt_tanh_arg (k t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.tanh (π * t / k)) ((π / k) / Real.cosh (π * t / k) ^ 2) t := by
  have h := (hasDerivAt_sinh_arg k t).div (hasDerivAt_cosh_arg k t) (Real.cosh_pos _).ne'
  have e : (fun t : ℝ => Real.tanh (π * t / k)) = fun t => Real.sinh (π * t / k) / Real.cosh (π * t / k) := by
    funext t; exact Real.tanh_eq_sinh_div_cosh _
  rw [e]
  refine h.congr_deriv ?_
  have hc := Real.cosh_pos (π * t / k)
  have h1 : Real.cosh (π * t / k) ^ 2 - Real.sinh (π * t / k) ^ 2 = 1 := by
    linarith [Real.cosh_sq (π * t / k)]
  have h2 : Real.cosh (π * t / k) * (π / k) * Real.cosh (π * t / k) -
      Real.sinh (π * t / k) * (Real.sinh (π * t / k) * (π / k)) =
      (π / k) * (Real.cosh (π * t / k) ^ 2 - Real.sinh (π * t / k) ^ 2) := by ring
  rw [h2, h1]; ring

lemma tendsto_arctan_sinh : Tendsto (fun t : ℝ => Real.arctan (Real.sinh (π * t))) atTop (𝓝 (π / 2)) := by
  have hpi := Real.pi_pos
  exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    (tendsto_sinh_atTop'.comp (tendsto_id.const_mul_atTop hpi))

/-- `∫₀^∞ π/cosh(πτ) dτ = π/2`. -/
lemma int_sech :
    IntegrableOn (fun t : ℝ => π / Real.cosh (π * t)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), π / Real.cosh (π * t) = π / 2 := by
  have hpi := Real.pi_pos
  have hd : ∀ t : ℝ, HasDerivAt (fun t => Real.arctan (Real.sinh (π * t))) (π / Real.cosh (π * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.sinh (π * t)) (Real.cosh (π * t) * π) t := by
      simpa using hasDerivAt_sinh_arg 1 t
    have h2 := (Real.hasDerivAt_arctan (Real.sinh (π * t))).comp t h1
    refine h2.congr_deriv ?_
    have hc := Real.cosh_pos (π * t)
    have h3 : 1 + Real.sinh (π * t) ^ 2 = Real.cosh (π * t) ^ 2 := by linarith [Real.cosh_sq (π * t)]
    rw [h3]; field_simp
  have := integrableOn_Ioi_of_deriv hd (fun t _ => (div_pos hpi (Real.cosh_pos _)).le) tendsto_arctan_sinh
  refine ⟨this.1, ?_⟩
  rw [this.2]; simp

/-- `∫₀^∞ π/(1+cosh πτ) dτ = 1`. -/
lemma int_half :
    IntegrableOn (fun t : ℝ => π / (1 + Real.cosh (π * t))) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), π / (1 + Real.cosh (π * t)) = 1 := by
  have hpi := Real.pi_pos
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.tanh (π * t / 2)) (π / (1 + Real.cosh (π * t))) t := by
    intro t
    refine (hasDerivAt_tanh_arg 2 t).congr_deriv ?_
    have h := cosh_double t
    have hc := Real.cosh_pos (π * t / 2)
    rw [h]; field_simp; ring
  have := integrableOn_Ioi_of_deriv hd (fun t _ => (div_pos hpi (by have := Real.cosh_pos (π * t); linarith)).le)
    (tendsto_tanh_arg two_pos)
  refine ⟨this.1, ?_⟩
  rw [this.2]; simp

/-- `∫₀^∞ π/√(c(1+c)) dτ = √2 arsinh 1`. -/
lemma int_sqrt :
    IntegrableOn (fun t : ℝ => π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t)))) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t))) = √2 * Real.arsinh 1 := by
  have hpi := Real.pi_pos
  have h2 : 0 < √2 := by positivity
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => √2 * Real.arsinh (Real.tanh (π * t / 2)))
      (π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t)))) t := by
    intro t
    have h := ((hasDerivAt_tanh_arg 2 t).arsinh).const_mul (√2)
    refine h.congr_deriv ?_
    have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
    have hch : 0 < Real.cosh (π * t / 2) := Real.cosh_pos _
    have hq : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr hc
    have hqq : √(Real.cosh (π * t)) * √(Real.cosh (π * t)) = Real.cosh (π * t) := Real.mul_self_sqrt hc.le
    have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    -- cosh πt = cosh² + sinh² at half argument
    have hc2 : Real.cosh (π * t) = Real.cosh (π * t / 2) ^ 2 + Real.sinh (π * t / 2) ^ 2 := by
      have h' : Real.cosh (π * t) = Real.cosh (2 * (π * t / 2)) := by congr 1; ring
      rw [h', Real.cosh_two_mul]
    have hdd := cosh_double t
    have h1t : 1 + Real.tanh (π * t / 2) ^ 2 = Real.cosh (π * t) / Real.cosh (π * t / 2) ^ 2 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_pow, hc2]; field_simp
    have hs1 : √(1 + Real.tanh (π * t / 2) ^ 2) = √(Real.cosh (π * t)) / Real.cosh (π * t / 2) := by
      rw [h1t, Real.sqrt_div hc.le, Real.sqrt_sq hch.le]
    have hs2 : √(Real.cosh (π * t) * (1 + Real.cosh (π * t))) =
        √(Real.cosh (π * t)) * (√2 * Real.cosh (π * t / 2)) := by
      rw [Real.sqrt_mul hc.le]
      congr 1
      have : 1 + Real.cosh (π * t) = (√2 * Real.cosh (π * t / 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num), hdd]; ring
      rw [this, Real.sqrt_sq (by positivity)]
    rw [hs1, hs2, smul_eq_mul]
    have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    exact h22
  have hlim : Tendsto (fun t : ℝ => √2 * Real.arsinh (Real.tanh (π * t / 2))) atTop
      (𝓝 (√2 * Real.arsinh 1)) :=
    ((Real.continuous_arsinh.tendsto 1).comp (tendsto_tanh_arg two_pos)).const_mul (√2)
  have := integrableOn_Ioi_of_deriv hd (fun t _ => (div_pos hpi (Real.sqrt_pos.mpr
    (mul_pos (Real.cosh_pos _) (by have := Real.cosh_pos (π * t); linarith)))).le) hlim
  refine ⟨this.1, ?_⟩
  rw [this.2]; simp

/-- `∫₀^∞ g₅ = 1`. -/
lemma int_g5 : IntegrableOn g5 (Ioi 0) ∧ ∫ t in Ioi (0 : ℝ), g5 t = 1 := by
  have hpi := Real.pi_pos
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.tanh (π * t / 2)) (g5 t) t := fun t => hasDerivAt_tanh_arg 2 t
  have := integrableOn_Ioi_of_deriv hd (fun t _ => by unfold g5; positivity) (tendsto_tanh_arg two_pos)
  refine ⟨this.1, ?_⟩
  rw [this.2]; simp

/-- `∫₀^∞ g₄ = π/2 - 1`. -/
lemma int_g4 : IntegrableOn g4 (Ioi 0) ∧ ∫ t in Ioi (0 : ℝ), g4 t = π / 2 - 1 := by
  have hpi := Real.pi_pos
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 2 * Real.arctan (Real.tanh (π * t / 4)) - Real.tanh (π * t / 4))
      (g4 t) t := by
    intro t
    have hs := hasDerivAt_tanh_arg 4 t
    have h := ((Real.hasDerivAt_arctan (Real.tanh (π * t / 4))).comp t hs).const_mul 2 |>.sub hs
    refine h.congr_deriv ?_
    have hφ : 0 < Real.cosh (π * t / 4) := Real.cosh_pos _
    have hc2 : Real.cosh (π * t / 2) = Real.cosh (π * t / 4) ^ 2 + Real.sinh (π * t / 4) ^ 2 := by
      have h' : Real.cosh (π * t / 2) = Real.cosh (2 * (π * t / 4)) := by congr 1; ring
      rw [h', Real.cosh_two_mul]
    have h1 : Real.cosh (π * t / 4) ^ 2 - Real.sinh (π * t / 4) ^ 2 = 1 := by
      linarith [Real.cosh_sq (π * t / 4)]
    have hch2 : 0 < Real.cosh (π * t / 2) := Real.cosh_pos _
    unfold g4
    rw [Real.tanh_eq_sinh_div_cosh]
    have e1 : 1 + (Real.sinh (π * t / 4) / Real.cosh (π * t / 4)) ^ 2 =
        Real.cosh (π * t / 2) / Real.cosh (π * t / 4) ^ 2 := by
      rw [div_pow, hc2]; field_simp
    rw [e1]
    have hne : Real.cosh (π * t / 4) ^ 2 ≠ 0 := by positivity
    have e2 : (π / 4) / Real.cosh (π * t / 4) ^ 2 * (1 / (Real.cosh (π * t / 2) / Real.cosh (π * t / 4) ^ 2)) =
        (π / 4) / Real.cosh (π * t / 2) := by field_simp
    field_simp
    rw [hc2] at *
    nlinarith [h1]
  have hlim : Tendsto (fun t : ℝ => 2 * Real.arctan (Real.tanh (π * t / 4)) - Real.tanh (π * t / 4)) atTop
      (𝓝 (2 * Real.arctan 1 - 1)) :=
    (((Real.continuous_arctan.tendsto 1).comp (tendsto_tanh_arg (by norm_num : (0 : ℝ) < 4))).const_mul 2).sub
      (tendsto_tanh_arg (by norm_num : (0 : ℝ) < 4))
  have := integrableOn_Ioi_of_deriv hd (fun t _ => by
    unfold g4
    have h2 := Real.cosh_pos (π * t / 2)
    have h4 := Real.cosh_pos (π * t / 4)
    positivity) hlim
  refine ⟨this.1, ?_⟩
  rw [this.2, Real.arctan_one]; simp; ring

end FormalResearch.ModularBootstrap.FiveTerm
