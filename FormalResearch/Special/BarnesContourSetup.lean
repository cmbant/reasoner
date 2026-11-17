module

public import FormalResearch.Special.BarnesKernel

/-!
# Contour setup for `thm:BG`: the interpolated integrand `H = N/D`

Fix real `θ ≠ 0`, `|θ| < π`, and let `D = kerD θ`, `a₊ = kerPlus θ`, `a₋ = kerMinus θ`,
`Q₊ = Q(z(a₊)) = Q(1 - θ/2π)`, `Q₋ = Q(z(a₋)) = Q(1 + θ/2π)`.  Instead of subtracting the principal
parts at `a_±` (which would need the rectangle integral of `1/(ξ-a)`), the integrand `Q(z(ξ))/D(ξ)` is
replaced by `N(ξ)/D(ξ)` with
`N(ξ) = Q(z(ξ)) - α - β e^{πξ}`, `α + β e^{π a_±} = Q_±`.
Since `e^{πξ}` and `D` are `2i`-periodic and `D` has simple zeros at `a_±`, the quotient `N/D` has
removable singularities there (`tendsto_div_of_simple_zero`), is `2i`-periodic up to the shift
`N(ξ-2i) - N(ξ) = ψ(z(ξ))`, and tends to the constants `-2β` (right) and `0` (left) at `Re ξ → ±∞`.

This file proves the continuity/differentiability hypotheses of the Cauchy–Goursat theorem for the
rectangle `[-X,X] × [-2,0]` for `contourH`; `BarnesContour` applies it and takes `X → ∞`.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex
open scoped Real

lemma tendsto_div_of_simple_zero {N D : ℂ → ℂ} {a : ℂ} (hN : DifferentiableAt ℂ N a)
    (hD : DifferentiableAt ℂ D a) (hNa : N a = 0) (hDa : D a = 0) (hD' : deriv D a ≠ 0) :
    Tendsto (fun ξ => N ξ / D ξ) (𝓝[≠] a) (𝓝 (deriv N a / deriv D a)) := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp hN.hasDerivAt
  have h2 := hasDerivAt_iff_tendsto_slope.mp hD.hasDerivAt
  have h3 := h1.div h2 hD'
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ξ hξ
  have hξ' : ξ - a ≠ 0 := sub_ne_zero.mpr hξ
  rw [Pi.div_apply, slope_def_field, slope_def_field, hNa, hDa, sub_zero, sub_zero,
    div_div_div_cancel_right₀ hξ']


/-- `Q` at `z(a₊)`. -/
noncomputable def cQplus (θ : ℝ) : ℂ := barnesQ (zOf (kerPlus θ))

/-- `Q` at `z(a₋)`. -/
noncomputable def cQminus (θ : ℝ) : ℂ := barnesQ (zOf (kerMinus θ))

/-- The interpolation coefficient `β`. -/
noncomputable def cBeta (θ : ℝ) : ℂ :=
  (cQplus θ - cQminus θ) / (Complex.exp (π * kerPlus θ) - Complex.exp (π * kerMinus θ))

/-- The interpolation coefficient `α`. -/
noncomputable def cAlpha (θ : ℝ) : ℂ := cQplus θ - cBeta θ * Complex.exp (π * kerPlus θ)

/-- The numerator `N(ξ) = Q(z(ξ)) - α - β e^{πξ}`. -/
noncomputable def cN (θ : ℝ) (ξ : ℂ) : ℂ :=
  barnesQ (zOf ξ) - cAlpha θ - cBeta θ * Complex.exp (π * ξ)

/-- `N/D` with the removable singularities at `a_±` filled in. -/
noncomputable def cH (θ : ℝ) (ξ : ℂ) : ℂ :=
  if ξ = kerPlus θ then deriv (cN θ) (kerPlus θ) / deriv (kerD θ) (kerPlus θ)
  else if ξ = kerMinus θ then deriv (cN θ) (kerMinus θ) / deriv (kerD θ) (kerMinus θ)
  else cN θ ξ / kerD θ ξ

lemma exp_kerPlus_sub_exp_kerMinus (θ : ℝ) :
    Complex.exp (π * kerPlus θ) - Complex.exp (π * kerMinus θ) = -2 * (Real.sin θ : ℂ) * I := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (π : ℂ) * kerPlus θ = ((θ - π : ℝ) : ℂ) * I := by
    unfold kerPlus; push_cast; field_simp; ring
  have h2 : (π : ℂ) * kerMinus θ = ((-(π + θ) : ℝ) : ℂ) * I := by
    unfold kerMinus; push_cast; field_simp
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_sub_pi, Complex.sin_sub_pi, Complex.cos_neg, Complex.sin_neg, add_comm (π : ℂ) θ,
    Complex.cos_add_pi, Complex.sin_add_pi]
  ring


lemma exp_diff_ne_zero {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) :
    Complex.exp (π * kerPlus θ) - Complex.exp (π * kerMinus θ) ≠ 0 := by
  rw [exp_kerPlus_sub_exp_kerMinus]
  have h' : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast sin_ne_zero_of_abs_lt h0 hθ
  exact mul_ne_zero (mul_ne_zero (by norm_num) h') Complex.I_ne_zero

lemma cN_kerPlus (θ : ℝ) : cN θ (kerPlus θ) = 0 := by
  unfold cN cAlpha cQplus
  ring

lemma cN_kerMinus {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) : cN θ (kerMinus θ) = 0 := by
  have hne := exp_diff_ne_zero h0 hθ
  have hβ : cBeta θ * (Complex.exp (π * kerPlus θ) - Complex.exp (π * kerMinus θ)) =
      cQplus θ - cQminus θ := by
    unfold cBeta; field_simp
  unfold cN cAlpha
  have : cQminus θ = barnesQ (zOf (kerMinus θ)) := rfl
  rw [← this]
  linear_combination hβ

lemma re_zOf (ξ : ℂ) : (zOf ξ).re = 1 / 2 - ξ.im / 2 := by
  simp [zOf]; ring

lemma differentiableAt_barnesQ {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ barnesQ w := by
  have hd : DifferentiableAt ℂ digamma w :=
    differentiableOn_digamma_rhp.differentiableAt (isOpen_rhp.mem_nhds hw)
  unfold barnesQ
  fun_prop

lemma differentiableAt_cN (θ : ℝ) {ξ : ℂ} (hξ : ξ.im < 1) : DifferentiableAt ℂ (cN θ) ξ := by
  have h1 : DifferentiableAt ℂ (fun ξ => barnesQ (zOf ξ)) ξ := by
    have hz : 0 < (zOf ξ).re := by rw [re_zOf]; linarith
    refine DifferentiableAt.comp (g := barnesQ) ξ (differentiableAt_barnesQ hz) ?_
    unfold zOf; fun_prop
  unfold cN
  fun_prop

lemma differentiableAt_kerD (θ : ℝ) (ξ : ℂ) : DifferentiableAt ℂ (kerD θ) ξ :=
  (hasDerivAt_kerD θ ξ).differentiableAt

lemma cH_eq_of_ne {θ : ℝ} {ξ : ℂ} (h1 : ξ ≠ kerPlus θ) (h2 : ξ ≠ kerMinus θ) :
    cH θ ξ = cN θ ξ / kerD θ ξ := by
  simp only [cH, h1, h2, ite_false]

lemma continuousAt_cH_of_ne_zero {θ : ℝ} {ξ : ℂ} (hξ : ξ.im < 1) (hD : kerD θ ξ ≠ 0) :
    ContinuousAt (cH θ) ξ := by
  have hc : ContinuousAt (fun ξ => cN θ ξ / kerD θ ξ) ξ :=
    ((differentiableAt_cN θ hξ).continuousAt).div (differentiableAt_kerD θ ξ).continuousAt hD
  refine hc.congr ?_
  have hopen : ∀ᶠ ξ' in 𝓝 ξ, kerD θ ξ' ≠ 0 :=
    (differentiableAt_kerD θ ξ).continuousAt.eventually_ne hD
  filter_upwards [hopen] with ξ' h'
  have h1 : ξ' ≠ kerPlus θ := fun h => h' (h ▸ kerD_kerPlus θ)
  have h2 : ξ' ≠ kerMinus θ := fun h => h' (h ▸ kerD_kerMinus θ)
  exact (cH_eq_of_ne h1 h2).symm

lemma im_kerPlus {θ : ℝ} : (kerPlus θ).im = -(1 - θ / π) := by
  simp [kerPlus]

lemma im_kerMinus {θ : ℝ} : (kerMinus θ).im = -(1 + θ / π) := by
  simp [kerMinus]

lemma continuousAt_cH_zero_aux {θ : ℝ} {a b : ℂ} (ha : kerD θ a = 0) (hab : a ≠ b)
    (hpair : ∀ ξ, ξ ≠ a → ξ ≠ b → ξ ≠ kerPlus θ ∧ ξ ≠ kerMinus θ)
    (hval : cH θ a = deriv (cN θ) a / deriv (kerD θ) a) (him : a.im < 1)
    (hNa : cN θ a = 0) (hD' : deriv (kerD θ) a ≠ 0) : ContinuousAt (cH θ) a := by
  have rs := tendsto_div_of_simple_zero (differentiableAt_cN θ him) (differentiableAt_kerD θ a)
    hNa ha hD'
  rw [← hval] at rs
  have : ContinuousWithinAt (cH θ) {a}ᶜ a := by
    refine Tendsto.congr' ?_ rs
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds hab)] with ξ h1 h2
    have := hpair ξ h1 h2
    exact (cH_eq_of_ne this.1 this.2).symm
  exact continuousWithinAt_compl_self.mp this

lemma continuousAt_cH_kerPlus {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) :
    ContinuousAt (cH θ) (kerPlus θ) := by
  have hθ' := abs_lt.mp hθ
  have hpi := Real.pi_pos
  refine continuousAt_cH_zero_aux (b := kerMinus θ) (kerD_kerPlus θ) (kerPlus_ne_kerMinus h0)
    (fun ξ h1 h2 => ⟨h1, h2⟩) ?_ ?_ (cN_kerPlus θ) (deriv_kerD_kerPlus_ne h0 hθ)
  · simp only [cH, ite_true]
  · rw [im_kerPlus]
    have : θ / π < 1 := (div_lt_one hpi).mpr hθ'.2
    have : -1 < θ / π := by rw [lt_div_iff₀ hpi]; linarith
    linarith

lemma continuousAt_cH_kerMinus {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) :
    ContinuousAt (cH θ) (kerMinus θ) := by
  have hθ' := abs_lt.mp hθ
  have hpi := Real.pi_pos
  refine continuousAt_cH_zero_aux (b := kerPlus θ) (kerD_kerMinus θ) (kerPlus_ne_kerMinus h0).symm
    (fun ξ h1 h2 => ⟨h2, h1⟩) ?_ ?_ (cN_kerMinus h0 hθ) (deriv_kerD_kerMinus_ne h0 hθ)
  · simp only [cH, (kerPlus_ne_kerMinus h0).symm, ite_true, ite_false]
  · rw [im_kerMinus]
    have : θ / π < 1 := (div_lt_one hpi).mpr hθ'.2
    have : -1 < θ / π := by rw [lt_div_iff₀ hpi]; linarith
    linarith

/-- `cH` is continuous at every point of the strip `-2 ≤ Im ξ ≤ 0`. -/
theorem continuousAt_cH_of_mem_strip {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) {ξ : ℂ}
    (him1 : -2 ≤ ξ.im) (him2 : ξ.im ≤ 0) : ContinuousAt (cH θ) ξ := by
  by_cases hD : kerD θ ξ = 0
  · rcases kerD_zero_of_mem_strip hθ him1 him2 hD with h | h
    · rw [h]; exact continuousAt_cH_kerPlus h0 hθ
    · rw [h]; exact continuousAt_cH_kerMinus h0 hθ
  · exact continuousAt_cH_of_ne_zero (by linarith) hD

/-- `cH` is complex differentiable at every point of the strip other than `a_±`. -/
theorem differentiableAt_cH_of_mem_strip {θ : ℝ} (hθ : |θ| < π) {ξ : ℂ}
    (him1 : -2 ≤ ξ.im) (him2 : ξ.im ≤ 0) (h1 : ξ ≠ kerPlus θ) (h2 : ξ ≠ kerMinus θ) :
    DifferentiableAt ℂ (cH θ) ξ := by
  have hD : kerD θ ξ ≠ 0 := fun h => by
    rcases kerD_zero_of_mem_strip hθ him1 him2 h with h' | h' <;> contradiction
  have hd : DifferentiableAt ℂ (fun ξ => cN θ ξ / kerD θ ξ) ξ :=
    (differentiableAt_cN θ (by linarith)).div (differentiableAt_kerD θ ξ) hD
  refine hd.congr_of_eventuallyEq ?_
  have hopen : ∀ᶠ ξ' in 𝓝 ξ, kerD θ ξ' ≠ 0 :=
    (differentiableAt_kerD θ ξ).continuousAt.eventually_ne hD
  filter_upwards [hopen] with ξ' h'
  have e1 : ξ' ≠ kerPlus θ := fun h => h' (h ▸ kerD_kerPlus θ)
  have e2 : ξ' ≠ kerMinus θ := fun h => h' (h ▸ kerD_kerMinus θ)
  exact cH_eq_of_ne e1 e2

end FormalResearch.Special.Barnes
