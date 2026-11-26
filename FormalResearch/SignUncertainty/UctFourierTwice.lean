module

public import FormalResearch.SignUncertainty.UctEnv2
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Two integrations by parts on the whole line for a `C²` function with an integrable envelope (F2a helper)

`env2_fourier_decay`: if `f` has an `Env2` envelope `P` (`‖f‖, ‖f'‖, ‖f''‖ ≤ P`) with `P` integrable, then for `ω ≠ 0`
`‖∫ f(τ) e^{iωτ} dτ‖ ≤ (∫ P) / ω²`.  Used for the reflected-density bound of `uct:bump-symbol`.

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma ibp_line {g : ℝ → ℂ} (hg : Differentiable ℝ g) (hg1 : Continuous (deriv g)) (hi : Integrable g) (hi1 : Integrable (deriv g))
    {ω : ℝ} (hω : ω ≠ 0) :
    ∫ τ : ℝ, g τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) =
      -(1 / (Complex.I * (ω : ℂ))) * ∫ τ : ℝ, deriv g τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) := by
  set iω : ℂ := Complex.I * (ω : ℂ) with hiω
  have hiω0 : iω ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hω)
  set e : ℝ → ℂ := fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) with he
  have hen : ∀ τ, ‖e τ‖ = 1 := fun τ => Complex.norm_exp_I_mul_ofReal _
  have hecont : Continuous e := by simp only [he]; fun_prop
  have hv : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => e τ / iω) (e τ) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => Complex.I * ((ω * τ : ℝ) : ℂ)) (Complex.I * (ω : ℂ)) τ := by
      have := ((hasDerivAt_id τ).const_mul ω).ofReal_comp.const_mul Complex.I
      simpa using this
    have h2 := h1.cexp
    have h3 := h2.div_const iω
    refine h3.congr_deriv ?_
    simp only [he, hiω]
    have hI : (Complex.I * (ω : ℂ)) ≠ 0 := hiω0
    exact mul_div_cancel_right₀ _ hI
  have hu : ∀ τ : ℝ, HasDerivAt g (deriv g τ) τ := fun τ => (hg τ).hasDerivAt
  have hbdd : ∀ τ, ‖e τ‖ ≤ 1 := fun τ => (hen τ).le
  have hvb : ∀ τ, ‖e τ / iω‖ ≤ ‖iω‖⁻¹ := fun τ => by rw [norm_div, hen, one_div]
  have hvcont : Continuous (fun τ : ℝ => e τ / iω) := hecont.div_const _
  have hm1 : Integrable (g * e) := by
    have := hi.mul_bdd hecont.aestronglyMeasurable (c := 1) (ae_of_all _ hbdd)
    exact this
  have hm2 : Integrable (deriv g * fun τ : ℝ => e τ / iω) :=
    hi1.mul_bdd hvcont.aestronglyMeasurable (c := ‖iω‖⁻¹) (ae_of_all _ hvb)
  have hm3 : Integrable (g * fun τ : ℝ => e τ / iω) :=
    hi.mul_bdd hvcont.aestronglyMeasurable (c := ‖iω‖⁻¹) (ae_of_all _ hvb)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := g) (v := fun τ : ℝ => e τ / iω) (u' := deriv g) (v' := e)
    (fun x _ => hu x) (fun x _ => hv x) hm1 hm2 hm3
  have e1 : ∫ τ : ℝ, g τ * e τ = -∫ τ : ℝ, deriv g τ * (e τ / iω) := key
  rw [e1]
  have e2 : ∀ τ : ℝ, deriv g τ * (e τ / iω) = (1 / iω) * (deriv g τ * e τ) := fun τ => by ring
  simp_rw [e2]
  rw [integral_const_mul]
  ring

lemma Env2.continuous_deriv_deriv {f : ℝ → ℂ} {P : ℝ → ℝ} (h : Env2 f P) : Continuous (deriv (deriv f)) := by
  have := h.deriv_contDiff
  exact this.continuous_deriv (by norm_num)

theorem env2_fourier_decay {f : ℝ → ℂ} {P : ℝ → ℝ} (hf : Env2 f P) (hP : Integrable P) {ω : ℝ} (hω : ω ≠ 0) :
    ‖∫ τ : ℝ, f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ ≤ (∫ τ : ℝ, P τ) / ω ^ 2 := by
  have hf0 : Continuous f := hf.1.continuous
  have hf1c : Continuous (deriv f) := hf.deriv_contDiff.continuous
  have hf2c : Continuous (deriv (deriv f)) := hf.continuous_deriv_deriv
  have i0 : Integrable f := hP.mono' hf0.aestronglyMeasurable (ae_of_all _ fun τ => (hf.2 τ).1)
  have i1 : Integrable (deriv f) := hP.mono' hf1c.aestronglyMeasurable (ae_of_all _ fun τ => (hf.2 τ).2.1)
  have i2 : Integrable (deriv (deriv f)) := hP.mono' hf2c.aestronglyMeasurable (ae_of_all _ fun τ => (hf.2 τ).2.2)
  have s1 := ibp_line hf.differentiable hf1c i0 i1 hω
  have s2 := ibp_line hf.differentiable_deriv hf2c i1 i2 hω
  rw [s1, s2]
  have hn : ‖(1 / (Complex.I * (ω : ℂ)))‖ = 1 / |ω| := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [← mul_assoc, norm_mul, norm_mul, norm_neg, hn]
  have hint : ‖∫ τ : ℝ, deriv (deriv f) τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ ≤ ∫ τ : ℝ, P τ := by
    refine norm_integral_le_of_norm_le hP (ae_of_all _ fun τ => ?_)
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    exact (hf.2 τ).2.2
  have hω2 : 0 < |ω| := abs_pos.mpr hω
  calc 1 / |ω| * (1 / |ω|) * ‖∫ τ : ℝ, deriv (deriv f) τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖
      ≤ 1 / |ω| * (1 / |ω|) * ∫ τ : ℝ, P τ := by gcongr
    _ = (∫ τ : ℝ, P τ) / ω ^ 2 := by
        rw [← sq_abs ω]; field_simp

/-- info: 'FormalResearch.SignUncertainty.env2_fourier_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env2_fourier_decay

end FormalResearch.SignUncertainty
