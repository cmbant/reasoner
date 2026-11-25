module

public import FormalResearch.SignUncertainty.CtOuterTaylor

/-!
# `ct:outer` (2): the third derivative of `θ_ε` at `0` in terms of `H₀'''(0)`

**Proved.**  `θ_ε'''(0) = -Re H₀'''(0) + 2 + [ε = 1] π³`: the three terms `Im H₀(iτ)`, `-arctan τ` and
`-2 arctan(tanh(πτ/2))` (`ε = +1`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma hasDerivAt_im_comp_I {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball (0 : ℂ) (1 / 2))) (c : ℂ) {τ : ℝ}
    (hτ : |τ| < 1 / 2) :
    HasDerivAt (fun s : ℝ => (c * G (Complex.I * (s : ℂ))).im) ((c * Complex.I * deriv G (Complex.I * (τ : ℂ))).im) τ := by
  have hb : Complex.I * (τ : ℂ) ∈ ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball_zero_iff]; simpa [norm_mul] using hτ
  have hd : HasDerivAt G (deriv G (Complex.I * (τ : ℂ))) (Complex.I * (τ : ℂ)) :=
    (hG.differentiableAt (isOpen_ball.mem_nhds hb)).hasDerivAt
  have hl : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) Complex.I τ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul Complex.I)
  have h1 := (hd.scomp τ hl).const_mul c
  have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ h1
  refine h2.congr_deriv ?_
  simp [mul_assoc]


lemma ev_abs_lt : ∀ᶠ τ : ℝ in 𝓝 0, |τ| < 1 / 2 := by
  have := Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [this] with τ hτ using by simpa [Real.dist_eq] using hτ

lemma iteratedDeriv_three_im :
    iteratedDeriv 3 (fun s : ℝ => (H0 (Complex.I * (s : ℂ))).im) 0 = -(deriv (deriv (deriv H0)) 0).re := by
  have hD0 := differentiableOn_H0
  have hD1 := hD0.deriv isOpen_ball
  have hD2 := hD1.deriv isOpen_ball
  set A : ℝ → ℝ := fun s => (1 * H0 (Complex.I * (s : ℂ))).im with hA
  have hA' : (fun s : ℝ => (H0 (Complex.I * (s : ℂ))).im) = A := by funext s; simp [hA]
  rw [hA']
  have d1 : ∀ τ : ℝ, |τ| < 1 / 2 → HasDerivAt A ((1 * Complex.I * deriv H0 (Complex.I * (τ : ℂ))).im) τ :=
    fun τ hτ => hasDerivAt_im_comp_I hD0 1 hτ
  have d2 : ∀ τ : ℝ, |τ| < 1 / 2 → HasDerivAt (fun s : ℝ => (1 * Complex.I * deriv H0 (Complex.I * (s : ℂ))).im)
      ((1 * Complex.I * Complex.I * deriv (deriv H0) (Complex.I * (τ : ℂ))).im) τ :=
    fun τ hτ => hasDerivAt_im_comp_I hD1 (1 * Complex.I) hτ
  have d3 : ∀ τ : ℝ, |τ| < 1 / 2 → HasDerivAt
      (fun s : ℝ => (1 * Complex.I * Complex.I * deriv (deriv H0) (Complex.I * (s : ℂ))).im)
      ((1 * Complex.I * Complex.I * Complex.I * deriv (deriv (deriv H0)) (Complex.I * (τ : ℂ))).im) τ :=
    fun τ hτ => hasDerivAt_im_comp_I hD2 (1 * Complex.I * Complex.I) hτ
  have e1 : deriv A =ᶠ[𝓝 0] fun s : ℝ => (1 * Complex.I * deriv H0 (Complex.I * (s : ℂ))).im := by
    filter_upwards [ev_abs_lt] with τ hτ using (d1 τ hτ).deriv
  have e2 : deriv (deriv A) =ᶠ[𝓝 0] fun s : ℝ =>
      (1 * Complex.I * Complex.I * deriv (deriv H0) (Complex.I * (s : ℂ))).im := by
    have := e1.deriv
    filter_upwards [this, (ev_abs_lt : ∀ᶠ τ : ℝ in 𝓝 0, |τ| < 1 / 2)] with τ hτ hτ' 
    rw [hτ]
    exact (d2 τ hτ').deriv
  have h3 := ((d3 0 (by norm_num)).congr_of_eventuallyEq e2)
  have : iteratedDeriv 3 A 0 = deriv (deriv (deriv A)) 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [this, h3.deriv]
  simp [Complex.mul_im, Complex.I_mul_I]


lemma iteratedDeriv_three_arctan : iteratedDeriv 3 Real.arctan 0 = -2 := by
  have h1 : deriv Real.arctan = fun x : ℝ => (1 + x ^ 2)⁻¹ := by
    funext x; rw [Real.deriv_arctan]; simp
  have h2 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 + x ^ 2)⁻¹) (-(2 * x) / (1 + x ^ 2) ^ 2) x := fun x => by
    have hne : (1 + x ^ 2) ≠ 0 := by positivity
    have h := ((hasDerivAt_pow 2 x).const_add 1).inv hne
    refine h.congr_deriv ?_
    simp
  have h3 : deriv (fun x : ℝ => (1 + x ^ 2)⁻¹) = fun x : ℝ => -(2 * x) / (1 + x ^ 2) ^ 2 := by
    funext x; exact (h2 x).deriv
  have h4 : HasDerivAt (fun x : ℝ => -(2 * x) / (1 + x ^ 2) ^ 2) (-2) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul 2).neg).div
      (((hasDerivAt_pow 2 (0 : ℝ)).const_add 1).pow 2) (by simp)
    refine h.congr_deriv ?_
    simp
  rw [iteratedDeriv_succ' , iteratedDeriv_succ', iteratedDeriv_one, h1, h3, h4.deriv]

lemma hasDerivAt_psi (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => 2 * Real.arctan (Real.tanh (π * τ / 2))) (π / Real.cosh (π * τ)) τ := by
  have hc : 0 < Real.cosh (π * τ / 2) := Real.cosh_pos _
  have hl : HasDerivAt (fun τ : ℝ => π * τ / 2) (π / 2) τ := by
    simpa using ((hasDerivAt_id τ).const_mul π).div_const 2
  have hs : HasDerivAt (fun τ : ℝ => Real.sinh (π * τ / 2)) (Real.cosh (π * τ / 2) * (π / 2)) τ :=
    by have h := (Real.hasDerivAt_sinh (π * τ / 2)).comp τ hl; exact h
  have hch : HasDerivAt (fun τ : ℝ => Real.cosh (π * τ / 2)) (Real.sinh (π * τ / 2) * (π / 2)) τ :=
    by have h := (Real.hasDerivAt_cosh (π * τ / 2)).comp τ hl; exact h
  have ht0 := hs.div hch hc.ne'
  have ht : HasDerivAt (fun τ : ℝ => Real.tanh (π * τ / 2))
      ((Real.cosh (π * τ / 2) * (π / 2) * Real.cosh (π * τ / 2) -
        Real.sinh (π * τ / 2) * (Real.sinh (π * τ / 2) * (π / 2))) / Real.cosh (π * τ / 2) ^ 2) τ := by
    have e : (fun τ : ℝ => Real.tanh (π * τ / 2)) =
        (fun τ : ℝ => Real.sinh (π * τ / 2)) / fun τ : ℝ => Real.cosh (π * τ / 2) := by
      funext x; simp [Real.tanh_eq_sinh_div_cosh]
    rw [e]; exact ht0
  have ha := ((Real.hasDerivAt_arctan (Real.tanh (π * τ / 2))).comp τ ht).const_mul 2
  refine ha.congr_deriv ?_
  have e2 : Real.cosh (π * τ) = Real.cosh (π * τ / 2) ^ 2 + Real.sinh (π * τ / 2) ^ 2 := by
    have := Real.cosh_two_mul (π * τ / 2)
    rwa [show 2 * (π * τ / 2) = π * τ by ring] at this
  rw [e2, Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring_nf
  rw [Real.cosh_sq]
  ring

lemma iteratedDeriv_three_psi :
    iteratedDeriv 3 (fun τ : ℝ => 2 * Real.arctan (Real.tanh (π * τ / 2))) 0 = -π ^ 3 := by
  have h1 : deriv (fun τ : ℝ => 2 * Real.arctan (Real.tanh (π * τ / 2))) = fun τ => π / Real.cosh (π * τ) := by
    funext τ; exact (hasDerivAt_psi τ).deriv
  have h2 : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => π / Real.cosh (π * τ))
      (-π ^ 2 * Real.sinh (π * τ) / Real.cosh (π * τ) ^ 2) τ := fun τ => by
    have hc : HasDerivAt (fun τ : ℝ => Real.cosh (π * τ)) (Real.sinh (π * τ) * π) τ :=
      ((Real.hasDerivAt_cosh (π * τ)).comp τ ((hasDerivAt_id τ).const_mul π)).congr_deriv (by simp)
    exact ((hasDerivAt_const τ π).div hc (Real.cosh_pos _).ne').congr_deriv (by field_simp; simp)
  have h3 : deriv (fun τ : ℝ => π / Real.cosh (π * τ)) = fun τ => -π ^ 2 * Real.sinh (π * τ) / Real.cosh (π * τ) ^ 2 := by
    funext τ; exact (h2 τ).deriv
  have h4 : HasDerivAt (fun τ : ℝ => -π ^ 2 * Real.sinh (π * τ) / Real.cosh (π * τ) ^ 2) (-π ^ 3) 0 := by
    have hs : HasDerivAt (fun τ : ℝ => Real.sinh (π * τ)) (Real.cosh (π * 0) * π) 0 :=
      ((Real.hasDerivAt_sinh (π * 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul π)).congr_deriv (by simp)
    have hc : HasDerivAt (fun τ : ℝ => Real.cosh (π * τ)) (Real.sinh (π * 0) * π) 0 :=
      ((Real.hasDerivAt_cosh (π * 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul π)).congr_deriv (by simp)
    have h := (hs.const_mul (-π ^ 2)).div (hc.pow 2) (by simp)
    refine h.congr_deriv ?_
    simp
    ring
  rw [iteratedDeriv_succ' , iteratedDeriv_succ', iteratedDeriv_one, h1, h3, h4.deriv]


lemma outerTheta_eventually (ε : ℝ) :
    outerTheta ε =ᶠ[𝓝 (0 : ℝ)] fun τ : ℝ => (H0 (Complex.I * (τ : ℂ))).im - Real.arctan τ -
      (if ε = 1 then 2 * Real.arctan (Real.tanh (π * τ / 2)) else 0) := by
  filter_upwards [ev_abs_lt] with τ hτ
  have hn : ‖Complex.I * (τ : ℂ)‖ < 1 / 2 := by simpa [norm_mul] using hτ
  have hb : Complex.I * (τ : ℂ) ∈ ball (0 : ℂ) (1 / 2) := mem_ball_zero_iff.mpr hn
  have hcl : Complex.I * (τ : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  unfold outerTheta
  rw [outerHbar_eq_H0 hcl hb]

lemma contDiff_psi : ContDiff ℝ 3 (fun τ : ℝ => 2 * Real.arctan (Real.tanh (π * τ / 2))) := by
  have h1 : ContDiff ℝ 3 (fun τ : ℝ => π * τ / 2) := by fun_prop
  have h2 : ContDiff ℝ 3 Real.tanh := contDiff_tanh_real.of_le (by exact_mod_cast le_top)
  exact (contDiff_const.mul (Real.contDiff_arctan.comp (h2.comp h1)))

/-- **`θ_ε'''(0) = -Re H₀'''(0) + 2 + [ε = 1] π³`.** -/
theorem iteratedDeriv_three_outerTheta (ε : ℝ) :
    iteratedDeriv 3 (outerTheta ε) 0 = -(deriv (deriv (deriv H0)) 0).re + 2 + (if ε = 1 then π ^ 3 else 0) := by
  set c : ℝ := if ε = 1 then 1 else 0 with hc
  have hev : (fun s : ℝ => (H0 (Complex.I * (s : ℂ))).im) =ᶠ[𝓝 (0 : ℝ)]
      fun τ : ℝ => outerTheta ε τ + Real.arctan τ + c * (2 * Real.arctan (Real.tanh (π * τ / 2))) := by
    filter_upwards [outerTheta_eventually ε] with τ hτ
    rw [hτ]
    by_cases h : ε = 1
    · simp [hc, h]; ring
    · simp [hc, h]
  have hθ : ContDiffAt ℝ 3 (outerTheta ε) 0 := ((contDiff_outerTheta ε).of_le (by exact_mod_cast le_top)).contDiffAt
  have hat : ContDiffAt ℝ 3 Real.arctan 0 := Real.contDiff_arctan.contDiffAt
  have hps : ContDiffAt ℝ 3 (fun τ : ℝ => c * (2 * Real.arctan (Real.tanh (π * τ / 2)))) 0 :=
    (contDiff_const.mul contDiff_psi).contDiffAt
  have h1 := hev.iteratedDeriv_eq 3
  rw [iteratedDeriv_three_im] at h1
  have h2 : iteratedDeriv 3 (fun τ : ℝ => outerTheta ε τ + Real.arctan τ +
      c * (2 * Real.arctan (Real.tanh (π * τ / 2)))) 0 =
      iteratedDeriv 3 (outerTheta ε) 0 + iteratedDeriv 3 Real.arctan 0 +
        c * iteratedDeriv 3 (fun τ : ℝ => 2 * Real.arctan (Real.tanh (π * τ / 2))) 0 := by
    rw [iteratedDeriv_fun_add (hθ.add hat) hps, iteratedDeriv_fun_add hθ hat,
      iteratedDeriv_const_mul c (contDiff_psi.contDiffAt)]
  rw [h2, iteratedDeriv_three_arctan, iteratedDeriv_three_psi] at h1
  by_cases h : ε = 1
  · simp only [hc, h, ↓reduceIte] at h1 ⊢
    linarith only [h1]
  · simp only [hc, h, ↓reduceIte] at h1 ⊢
    linarith only [h1]

/-- info: 'FormalResearch.SignUncertainty.CtOuter.iteratedDeriv_three_outerTheta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_three_outerTheta

end FormalResearch.SignUncertainty.CtOuter
