module

public import FormalResearch.Special.BarnesBG

/-!
# `lem:VI`: the variance integral

For `w(ξ) = [4 cosh²(πξ/2)]⁻¹` (so `w = f(1-f)`, `f(ξ) = 1/(1+e^{πξ})`):

`∫_ℝ w dξ = 1/π`  and  `∫_ℝ w(ξ) Re ψ(1/2 + iξ/2) dξ = -(1+γ)/π`

(`lem:VI`, Weyl/free_fermion/paper/parts/constants.tex).  The first is the fundamental theorem of
calculus for `f`; the second is the paper's proof: divide the contour-shift identity
`∫ Re ψ(z(ξ))/(cosh πξ + cos θ) dξ = 2 b [Re ψ(1+b) + Re ψ(1-b) - 2]/sin θ`, `b = θ/2π`, by `θ → 0`
(the left side is continuous at `θ = 0` by dominated convergence, with `1/(cosh πξ + 1) = 2 w`).
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex MeasureTheory Metric
open scoped Real

local notation "γ" => Real.eulerMascheroniConstant

/-- The weight `w(ξ) = [4 cosh²(πξ/2)]⁻¹ = f(ξ)(1 - f(ξ))`. -/
noncomputable def wR (ξ : ℝ) : ℝ := 1 / (4 * Real.cosh (π * ξ / 2) ^ 2)

lemma kerR_zero_eq (x : ℝ) : kerR 0 x = 2 * Real.cosh (π * x / 2) ^ 2 := by
  have h := Real.cosh_two_mul (π * x / 2)
  have h2 := Real.cosh_sq (π * x / 2)
  rw [show 2 * (π * x / 2) = π * x by ring] at h
  rw [kerR_zero]
  nlinarith

lemma wR_eq (x : ℝ) : wR x = 1 / (2 * kerR 0 x) := by
  rw [wR, kerR_zero_eq]; congr 1; ring

lemma wR_eq_exp (x : ℝ) : wR x = Real.exp (π * x) / (1 + Real.exp (π * x)) ^ 2 := by
  unfold wR
  have ha : 0 < Real.exp (π * x / 2) := Real.exp_pos _
  have h1 : Real.exp (π * x) = Real.exp (π * x / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have h2 : Real.exp (-(π * x / 2)) = (Real.exp (π * x / 2))⁻¹ := Real.exp_neg _
  rw [Real.cosh_eq, h2, h1]
  field_simp
  ring

lemma wR_pos (x : ℝ) : 0 < wR x := by
  unfold wR; have := Real.cosh_pos (π * x / 2); positivity

lemma continuous_wR : Continuous wR := by
  unfold wR
  refine Continuous.div continuous_const (by fun_prop) fun x => ?_
  have := Real.cosh_pos (π * x / 2); positivity

lemma integrable_wR : Integrable wR := by
  refine ((integrable_exp_neg_mul_abs Real.pi_pos).const_mul 2).mono'
    continuous_wR.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (wR_pos x), wR_eq]
  have hk := kerR_pos (θ := 0) (by rw [abs_zero]; exact Real.pi_pos) x
  have hc := Real.cosh_pos (π * x)
  have h1 : Real.cosh (π * x) ≤ kerR 0 x := by unfold kerR; simp
  calc 1 / (2 * kerR 0 x) ≤ 1 / Real.cosh (π * x) :=
        one_div_le_one_div_of_le hc (by linarith)
    _ ≤ 2 * Real.exp (-π * |x|) := one_div_cosh_le x

/-- `∫ w = 1/π`. -/
theorem integral_wR : ∫ x : ℝ, wR x = 1 / π := by
  have hpi := Real.pi_pos
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 + Real.exp (π * x))⁻¹) (-π * wR x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => 1 + Real.exp (π * x)) (Real.exp (π * x) * π) x := by
      simpa using ((hasDerivAt_id x).const_mul π).exp.const_add 1
    have h2 := h1.inv (by positivity)
    refine h2.congr_deriv ?_
    rw [wR_eq_exp]
    field_simp
  have hint : Integrable (fun x : ℝ => -π * wR x) := integrable_wR.const_mul _
  have hbot : Tendsto (fun x : ℝ => (1 + Real.exp (π * x))⁻¹) atBot (𝓝 1) := by
    have : Tendsto (fun x : ℝ => Real.exp (π * x)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos hpi).mpr tendsto_id)
    have h2 := (tendsto_const_nhds (x := (1 : ℝ)) |>.add this).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simpa using h2
  have htop : Tendsto (fun x : ℝ => (1 + Real.exp (π * x))⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => Real.exp (π * x)) atTop atTop :=
      Real.tendsto_exp_atTop.comp ((tendsto_const_mul_atTop_of_pos hpi).mpr tendsto_id)
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 this)
  have := integral_of_hasDerivAt_of_tendsto hderiv hint hbot htop
  rw [integral_const_mul] at this
  field_simp at this ⊢
  linarith


/-- `K(θ) = ∫ ρ/K_θ`. -/
noncomputable def kInt (θ : ℝ) : ℝ := ∫ x : ℝ, rhoR x / kerR θ x

lemma continuousAt_kInt_zero : ContinuousAt kInt 0 := by
  set η : ℝ := π / 2 with hη
  have hηpos : 0 < η := by positivity
  have hηπ : η < π := by rw [hη]; linarith [Real.pi_pos]
  have hκ := kappa_pos hηpos hηπ
  set M : ℝ := (|γ| + 2 * invSqSum) * 3 with hM
  have hM0 : 0 ≤ M := by have := invSqSum_nonneg; rw [hM]; positivity
  have hs : ∀ θ ∈ ball (0 : ℝ) η, |θ| ≤ π - η := by
    intro θ hθ
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hθ
    rw [hη] at hθ ⊢; linarith
  have hmaj : Integrable (fun x : ℝ => (2 * M / kappa η) * ((1 + |x|) * Real.exp (-π * |x|))) :=
    integrable_one_add_abs_mul_exp.const_mul _
  have hsπ : ∀ θ ∈ ball (0 : ℝ) η, |θ| < π := fun θ hθ => by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hθ
    rw [hη] at hθ; linarith [Real.pi_pos]
  refine continuousAt_of_dominated (bound := fun x : ℝ =>
    (2 * M / kappa η) * ((1 + |x|) * Real.exp (-π * |x|))) ?_ ?_ hmaj ?_
  · filter_upwards [ball_mem_nhds (0 : ℝ) hηpos] with θ hθ
    exact (continuous_rhoR.div (continuous_kerR θ) fun x => (kerR_pos (hsπ θ hθ) x).ne').aestronglyMeasurable
  · filter_upwards [ball_mem_nhds (0 : ℝ) hηpos] with θ hθ
    refine Eventually.of_forall fun x => ?_
    have hpos := kerR_pos (hsπ θ hθ) x
    have hge := kerR_ge hηpos (hs θ hθ) x
    have hc := Real.cosh_pos (π * x)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    have h2 := abs_rhoR_le x
    have h3 : 1 / kerR θ x ≤ (2 / kappa η) * Real.exp (-π * |x|) := by
      calc 1 / kerR θ x ≤ 1 / (kappa η * Real.cosh (π * x)) :=
            one_div_le_one_div_of_le (by positivity) hge
        _ = (1 / kappa η) * (1 / Real.cosh (π * x)) := by field_simp
        _ ≤ (1 / kappa η) * (2 * Real.exp (-π * |x|)) :=
            mul_le_mul_of_nonneg_left (one_div_cosh_le x) (by positivity)
        _ = (2 / kappa η) * Real.exp (-π * |x|) := by ring
    calc |rhoR x| / kerR θ x = |rhoR x| * (1 / kerR θ x) := by ring
      _ ≤ (M * (1 + |x|)) * ((2 / kappa η) * Real.exp (-π * |x|)) :=
          mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = (2 * M / kappa η) * ((1 + |x|) * Real.exp (-π * |x|)) := by ring
  · refine Eventually.of_forall fun x => ?_
    have hk : kerR 0 x ≠ 0 := (kerR_pos (θ := 0) (by rw [abs_zero]; exact Real.pi_pos) x).ne'
    have : ContinuousAt (fun θ : ℝ => kerR θ x) 0 := by unfold kerR; fun_prop
    exact continuousAt_const.div this hk


/-- Closed form of `K(θ)` for `θ ≠ 0`, `|θ| < π`, `b = θ/(2π)`:
`K(θ) = 2 b [Re ψ(1+b) + Re ψ(1-b) - 2] / sin θ`. -/
lemma kInt_closed {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) :
    kInt θ = 2 * (θ / (2 * π)) *
      ((digamma ((1 + θ / (2 * π) : ℝ) : ℂ)).re + (digamma ((1 - θ / (2 * π) : ℝ) : ℂ)).re - 2) /
        Real.sin θ := by
  unfold kInt
  rw [integral_rho_div_kerR hθ]
  have hI : (∫ x : ℝ, psiKer θ x) =
      2 * (barnesQ (1 + (θ : ℂ) / (2 * π)) - barnesQ (1 - (θ : ℂ) / (2 * π))) /
        (Real.sin θ : ℂ) := integral_digamma_div_kerD h0 hθ
  rw [hI, Complex.div_ofReal_re]
  have hb : ((θ : ℂ) / (2 * π)) = ((θ / (2 * π) : ℝ) : ℂ) := by push_cast; rfl
  rw [hb]
  set b : ℝ := θ / (2 * π)
  have hQ : barnesQ (1 + (b : ℂ)) - barnesQ (1 - (b : ℂ)) =
      ((b : ℝ) : ℂ) * (digamma ((1 + b : ℝ) : ℂ) + digamma ((1 - b : ℝ) : ℂ) - 2) := by
    unfold barnesQ
    push_cast
    ring
  rw [hQ]
  have : (2 * (((b : ℝ) : ℂ) * (digamma ((1 + b : ℝ) : ℂ) + digamma ((1 - b : ℝ) : ℂ) - 2))).re =
      2 * (b * ((digamma ((1 + b : ℝ) : ℂ)).re + (digamma ((1 - b : ℝ) : ℂ)).re - 2)) := by
    rw [show (2 : ℂ) * (((b : ℝ) : ℂ) * (digamma ((1 + b : ℝ) : ℂ) + digamma ((1 - b : ℝ) : ℂ) - 2)) =
      ((2 * b : ℝ) : ℂ) * (digamma ((1 + b : ℝ) : ℂ) + digamma ((1 - b : ℝ) : ℂ) - 2) by push_cast; ring,
      Complex.re_ofReal_mul]
    simp; ring
  rw [this]; ring

lemma tendsto_div_sin : Tendsto (fun θ : ℝ => θ / Real.sin θ) (𝓝[≠] 0) (𝓝 1) := by
  have h := hasDerivAt_iff_tendsto_slope_zero.mp (Real.hasDerivAt_sin 0)
  simp only [zero_add, Real.sin_zero, sub_zero, smul_eq_mul, Real.cos_zero] at h
  have h2 := h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_one] at h2
  refine h2.congr fun θ => ?_
  simp [div_eq_mul_inv, mul_comm]

lemma continuousAt_digamma_one_add : ContinuousAt (fun θ : ℝ => digamma ((1 + θ / (2 * π) : ℝ) : ℂ)) 0 := by
  have hd : ContinuousAt digamma ((1 + (0 : ℝ) / (2 * π) : ℝ) : ℂ) := by
    have : ((1 + (0 : ℝ) / (2 * π) : ℝ) : ℂ) = 1 := by simp
    rw [this]
    exact (differentiableOn_digamma_rhp.differentiableAt (isOpen_rhp.mem_nhds (by simp [rhp]))).continuousAt
  have hc : Continuous fun θ : ℝ => (((1 + θ / (2 * π) : ℝ)) : ℂ) := by fun_prop
  exact hd.comp_of_eq hc.continuousAt rfl

lemma continuousAt_digamma_one_sub : ContinuousAt (fun θ : ℝ => digamma ((1 - θ / (2 * π) : ℝ) : ℂ)) 0 := by
  have hd : ContinuousAt digamma ((1 - (0 : ℝ) / (2 * π) : ℝ) : ℂ) := by
    have : ((1 - (0 : ℝ) / (2 * π) : ℝ) : ℂ) = 1 := by simp
    rw [this]
    exact (differentiableOn_digamma_rhp.differentiableAt (isOpen_rhp.mem_nhds (by simp [rhp]))).continuousAt
  have hc : Continuous fun θ : ℝ => (((1 - θ / (2 * π) : ℝ)) : ℂ) := by fun_prop
  exact hd.comp_of_eq hc.continuousAt rfl

/-- `∫ ρ/(cosh πx + 1) = -2(1+γ)/π`. -/
theorem kInt_zero : kInt 0 = -2 * (1 + γ) / π := by
  have hπ := Real.pi_pos
  have hc : Tendsto kInt (𝓝[≠] 0) (𝓝 (kInt 0)) :=
    continuousAt_kInt_zero.tendsto.mono_left nhdsWithin_le_nhds
  have hψ1 := (continuousAt_digamma_one_add.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ)))
  have hψ2 := (continuousAt_digamma_one_sub.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ)))
  have hre1 := (Complex.continuous_re.tendsto _).comp hψ1
  have hre2 := (Complex.continuous_re.tendsto _).comp hψ2
  have hlim0 := ((tendsto_const_nhds (x := 1 / π)).mul tendsto_div_sin).mul
    ((hre1.add hre2).sub_const 2)
  have hv : (digamma ((1 + (0 : ℝ) / (2 * π) : ℝ) : ℂ)).re = -γ := by
    have : ((1 + (0 : ℝ) / (2 * π) : ℝ) : ℂ) = 1 := by simp
    rw [this, digamma_one]; simp
  have hv2 : (digamma ((1 - (0 : ℝ) / (2 * π) : ℝ) : ℂ)).re = -γ := by
    have : ((1 - (0 : ℝ) / (2 * π) : ℝ) : ℂ) = 1 := by simp
    rw [this, digamma_one]; simp
  rw [hv, hv2] at hlim0
  have heq : (fun θ : ℝ => (1 / π * (θ / Real.sin θ)) *
      ((re ∘ fun θ : ℝ => digamma ((1 + θ / (2 * π) : ℝ) : ℂ)) θ +
        (re ∘ fun θ : ℝ => digamma ((1 - θ / (2 * π) : ℝ) : ℂ)) θ - 2)) =ᶠ[𝓝[≠] (0 : ℝ)] kInt := by
    have hball : ball (0 : ℝ) π ∈ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_le_nhds (ball_mem_nhds 0 hπ)
    filter_upwards [hball, self_mem_nhdsWithin] with θ hθ hne
    have hθ' : |θ| < π := by simpa [Real.dist_eq] using hθ
    have hne' : θ ≠ 0 := hne
    have hs := sin_ne_zero_of_abs_lt hne' hθ'
    rw [kInt_closed hne' hθ']
    simp only [Function.comp_apply]
    field_simp
  have := tendsto_nhds_unique hc (hlim0.congr' heq)
  rw [this]
  field_simp
  ring

/-- **`lem:VI`**, second half: `∫_ℝ w(ξ) Re ψ(1/2 + iξ/2) dξ = -(1+γ)/π`. -/
theorem integral_wR_mul_rhoR : ∫ x : ℝ, wR x * rhoR x = -(1 + γ) / π := by
  have hπ := Real.pi_pos
  have h := kInt_zero
  unfold kInt at h
  have : ∫ x : ℝ, rhoR x / kerR 0 x = 2 * ∫ x : ℝ, wR x * rhoR x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show rhoR x / kerR 0 x = 2 * (wR x * rhoR x)
    rw [wR_eq]
    have hk := (kerR_pos (θ := 0) (by rw [abs_zero]; exact Real.pi_pos) x).ne'
    field_simp
  rw [this] at h
  field_simp at h ⊢
  linarith

/-- info: 'FormalResearch.Special.Barnes.integral_wR_mul_rhoR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_wR_mul_rhoR

/-- info: 'FormalResearch.Special.Barnes.integral_wR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_wR

end FormalResearch.Special.Barnes
