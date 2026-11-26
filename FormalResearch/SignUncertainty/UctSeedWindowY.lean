module

public import FormalResearch.SignUncertainty.UctSeedEdgeKW
public import FormalResearch.SignUncertainty.UctSeedWHolder
public import FormalResearch.SignUncertainty.UctMcSmallA
public import FormalResearch.SignUncertainty.UctMcSmallPhi

/-!
# The holomorphic factor `Y_ε(ζ) = (1-ζ)^{-5/2} Z_ε(ζ) e^{-H_0(ζ)}` of `W^seed` (F2a, `uct:seed-asymp` (1))

On `D(0,1/2)`: `Y_ε` is holomorphic, `Y_ε(0) = 1`, and on the imaginary axis `Y_ε(iτ) = (1-iτ)^{1/2} e^{-iθ_ε(τ)} A_*(τ)`
(`seedYw_edge`, from `seedZ_edge_core_all`).  Hence `Y_ε'(0) = -(1/2 + θ_ε'(0))` (`seedYw_deriv_zero`, real) and
`|Y_ε(ζ) - e^{-λζ}| ≤ C|ζ|²` on `|ζ| ≤ 1/4` with `λ = θ_ε'(0) + 1/2` (`seedYw_taylor`).
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

noncomputable def seedYw (ε : ℝ) (ζ : ℂ) : ℂ :=
  (1 - ζ) ^ (-(5 / 2 : ℂ)) * (uctSeedZ ε ζ * Complex.exp (-H0 ζ))

lemma seedYw_differentiableOn (ε : ℝ) : DifferentiableOn ℂ (seedYw ε) (ball (0 : ℂ) (1 / 2)) := by
  have hZ : DifferentiableOn ℂ (uctSeedZ ε) (ball (0 : ℂ) (1 / 2)) :=
    (differentiableOn_uctSeedZ ε).mono fun ζ hζ => by
      have := Complex.abs_re_le_norm ζ
      have h2 : ‖ζ‖ < 1 / 2 := by simpa using hζ
      rw [abs_le] at this
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hP : DifferentiableOn ℂ (fun ζ : ℂ => (1 - ζ) ^ (-(5 / 2 : ℂ))) (ball (0 : ℂ) (1 / 2)) := by
    intro ζ hζ
    have h2 : ‖ζ‖ < 1 / 2 := by simpa using hζ
    have hre : 0 < (1 - ζ).re := by
      have := Complex.re_le_norm ζ
      simp only [Complex.sub_re, Complex.one_re]; linarith
    have : DifferentiableAt ℂ (fun ζ : ℂ => (1 - ζ) ^ (-(5 / 2 : ℂ))) ζ :=
      (differentiableAt_const _ |>.sub differentiableAt_id).cpow_const (Or.inl hre)
    exact this.differentiableWithinAt
  unfold seedYw
  exact hP.mul (hZ.mul differentiableOn_H0.neg.cexp)

lemma seedYw_zero (ε : ℝ) : seedYw ε 0 = 1 := by
  simp [seedYw, uctSeedZ_zero, H0_zero]

lemma seedZ_core_any {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (τ : ℝ) :
    (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
        (uctSeedZ ε (Complex.I * (τ : ℂ)) * Complex.exp (-outerHbar (Complex.I * (τ : ℂ)))) =
      Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * (uctAstar τ : ℂ) := by
  by_cases hτ : τ = 0
  · subst hτ; exact seedZ_edge_core_zero
  · exact seedZ_edge_core_all hε hτ

/-- On the imaginary axis (`|τ| < 1/2`): `Y_ε(iτ) = (1-iτ)^{1/2} e^{-iθ_ε(τ)} A_*(τ)`. -/
theorem seedYw_edge {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {τ : ℝ} (hτ : |τ| < 1 / 2) :
    seedYw ε (Complex.I * (τ : ℂ)) =
      (1 - Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * (uctAstar τ : ℂ) := by
  have hcl : Complex.I * (τ : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have hb : Complex.I * (τ : ℂ) ∈ ball (0 : ℂ) (1 / 2) := by
    have : ‖Complex.I * (τ : ℂ)‖ = |τ| := by simp
    rw [Metric.mem_ball, dist_zero_right, this]; exact hτ
  unfold seedYw
  rw [← outerHbar_eq_H0 hcl hb]
  have hcore := seedZ_core_any hε τ
  set w : ℂ := 1 - Complex.I * (τ : ℂ) with hw
  have hre : 0 < w.re := by simp [hw]
  have hw0 : w ≠ 0 := fun h => by rw [h] at hre; simp at hre
  set P : ℂ := w ^ (1 / 2 : ℂ) with hP
  have hP2 : P ^ 2 = w := FormalResearch.SignUncertainty.CtOuter.cpow_half_sq w
  have hP0 : P ≠ 0 := by intro h; apply hw0; rw [← hP2, h]; simp
  have e1 : w ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [Complex.cpow_neg]
  have e2 : w ^ (5 / 2 : ℂ) = w ^ 2 * P := by
    rw [show (5 / 2 : ℂ) = 2 + 1 / 2 by norm_num, Complex.cpow_add _ _ hw0]
    congr 1
    exact_mod_cast Complex.cpow_natCast w 2
  have e3 : w ^ (-(5 / 2 : ℂ)) = (w ^ 2 * P)⁻¹ := by rw [Complex.cpow_neg, e2]
  rw [e1, e2] at hcore
  rw [e3]
  set ZE := uctSeedZ ε (Complex.I * (τ : ℂ)) * Complex.exp (-outerHbar (Complex.I * (τ : ℂ))) with hZE
  have hZE' : ZE = Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * w ^ 3 * (uctAstar τ : ℂ) := by
    have : ZE = P * (P⁻¹ * ZE) := by field_simp
    rw [this, hcore]
    have h3 : w ^ 3 = w ^ 2 * P ^ 2 := by rw [hP2]; ring
    rw [h3]; ring
  rw [hZE']
  have hw2 : w ^ 2 * P ≠ 0 := mul_ne_zero (pow_ne_zero 2 hw0) hP0
  have hwP : w = P ^ 2 := hP2.symm
  field_simp
  rw [hwP]

/-- `λ_ε = θ_ε'(0) + 1/2`. -/
noncomputable def seedLam (ε : ℝ) : ℝ := deriv (outerTheta ε) 0 + 1 / 2

theorem seedYw_deriv_zero {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    deriv (seedYw ε) 0 = -((seedLam ε : ℝ) : ℂ) := by
  have hY : HasDerivAt (seedYw ε) (deriv (seedYw ε) 0) 0 :=
    ((seedYw_differentiableOn ε).differentiableAt (ball_mem_nhds (0 : ℂ) (by norm_num))).hasDerivAt
  have h1 : HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I (0 : ℂ) := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul Complex.I
  have hY' : HasDerivAt (seedYw ε) (deriv (seedYw ε) 0) (Complex.I * 0) := by simpa using hY
  have hc := hY'.comp (0 : ℂ) h1
  have hc' : HasDerivAt (fun z : ℂ => seedYw ε (Complex.I * z)) (deriv (seedYw ε) 0 * Complex.I) ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]; exact hc
  have hG := hc'.comp_ofReal
  -- the edge expression
  have hin : HasDerivAt (fun z : ℂ => 1 - Complex.I * z) (-Complex.I) (0 : ℂ) := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul Complex.I).const_sub 1
  have e1 := hin.cpow_const (c := (1 / 2 : ℂ)) (by simp)
  have e1' : HasDerivAt (fun z : ℂ => (1 - Complex.I * z) ^ (1 / 2 : ℂ)) (-(Complex.I / 2)) ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    refine e1.congr_deriv ?_
    simp; ring
  have hf1 := e1'.comp_ofReal
  have hθd : Differentiable ℝ (outerTheta ε) := (contDiff_outerTheta ε).differentiable (by simp)
  have hθ : HasDerivAt (fun τ : ℝ => ((outerTheta ε τ : ℝ) : ℂ)) ((deriv (outerTheta ε) 0 : ℝ) : ℂ) 0 :=
    (hθd 0).hasDerivAt.ofReal_comp
  have hf2 := ((hθ.const_mul Complex.I).neg).cexp
  have hAd : Differentiable ℝ uctAstar := contDiff_uctAstar.differentiable (by simp)
  have hA : HasDerivAt (fun τ : ℝ => ((uctAstar τ : ℝ) : ℂ)) 0 0 := by
    have := (hAd 0).hasDerivAt.ofReal_comp
    rwa [deriv_zero_of_even uctAstar_neg, Complex.ofReal_zero] at this
  have hR := (hf1.mul hf2).mul hA
  have heq : (fun τ : ℝ => seedYw ε (Complex.I * (τ : ℂ))) =ᶠ[nhds 0]
      (fun τ : ℝ => (1 - Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) *
        (uctAstar τ : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with τ hτ
    have : |τ| < 1 / 2 := by simpa [Real.dist_eq] using hτ
    exact seedYw_edge hε this
  have huniq := hG.unique (hR.congr_of_eventuallyEq heq)
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  simp only [Pi.neg_apply, Pi.mul_apply, outerTheta_zero, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, uctAstar_zero,
    Complex.ofReal_one, one_mul, mul_one, sub_zero, Complex.one_cpow, add_zero] at huniq
  unfold seedLam
  apply mul_right_cancel₀ hI
  rw [huniq]
  push_cast
  ring

lemma taylor2_of_holo {f : ℂ → ℂ} {r ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < r)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) r)) (h0 : f 0 = 0) (h1 : deriv f 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ ρ → ‖f z‖ ≤ C * ‖z‖ ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt hρ0 hρ
  have hmem : ball (0 : ℂ) r ∈ nhds (0 : ℂ) := ball_mem_nhds _ hr
  have hg : DifferentiableOn ℂ (dslope f 0) (ball (0 : ℂ) r) := (differentiableOn_dslope hmem).mpr hf
  have hg0 : dslope f 0 0 = 0 := by rw [dslope_same, h1]
  obtain ⟨L, M, hL, hM, hLM⟩ := holo_lip_zero hρ0 hρ hg
  refine ⟨L, hL, fun z hz => ?_⟩
  have hs := sub_smul_dslope f 0 z
  rw [sub_zero, smul_eq_mul, h0, sub_zero] at hs
  have := (hLM z hz).1
  rw [hg0, sub_zero] at this
  rw [← hs, norm_mul]
  nlinarith [norm_nonneg z, norm_nonneg (dslope f 0 z)]

theorem seedYw_taylor {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 4 →
      ‖seedYw ε ζ - Complex.exp (-((seedLam ε : ℝ) : ℂ) * ζ)‖ ≤ C * ‖ζ‖ ^ 2 := by
  have hD : DifferentiableOn ℂ (fun ζ => seedYw ε ζ - Complex.exp (-((seedLam ε : ℝ) : ℂ) * ζ)) (ball (0 : ℂ) (1 / 2)) :=
    (seedYw_differentiableOn ε).sub (by fun_prop)
  have hderiv : deriv (fun ζ => seedYw ε ζ - Complex.exp (-((seedLam ε : ℝ) : ℂ) * ζ)) 0 = 0 := by
    have h1 : HasDerivAt (seedYw ε) (deriv (seedYw ε) 0) 0 :=
      ((seedYw_differentiableOn ε).differentiableAt (ball_mem_nhds (0 : ℂ) (by norm_num))).hasDerivAt
    have h2 : HasDerivAt (fun ζ : ℂ => Complex.exp (-((seedLam ε : ℝ) : ℂ) * ζ))
        (Complex.exp (-((seedLam ε : ℝ) : ℂ) * 0) * (-((seedLam ε : ℝ) : ℂ))) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).const_mul (-((seedLam ε : ℝ) : ℂ))).cexp
      simpa using this
    have h4 : HasDerivAt (fun ζ : ℂ => seedYw ε ζ - Complex.exp (-((seedLam ε : ℝ) : ℂ) * ζ))
        (deriv (seedYw ε) 0 - Complex.exp (-((seedLam ε : ℝ) : ℂ) * 0) * (-((seedLam ε : ℝ) : ℂ))) 0 := h1.sub h2
    rw [h4.deriv, seedYw_deriv_zero hε]
    simp
  obtain ⟨C, hC, h⟩ := taylor2_of_holo (r := 1 / 2) (ρ := 1 / 4) (by norm_num) (by norm_num) hD
    (by simp [seedYw_zero]) hderiv
  exact ⟨C, hC, h⟩

/-- info: 'FormalResearch.SignUncertainty.seedYw_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedYw_edge

/-- info: 'FormalResearch.SignUncertainty.seedYw_deriv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedYw_deriv_zero

/-- info: 'FormalResearch.SignUncertainty.seedYw_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedYw_taylor

end FormalResearch.SignUncertainty
