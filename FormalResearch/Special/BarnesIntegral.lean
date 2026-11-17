module

public import FormalResearch.Special.BarnesContour

/-!
# The real integral `B(θ)` of `thm:BG` and its derivative

With `ρ(x) = Re ψ(1/2 + ix/2)` and `K_θ(x) = cosh πx + cos θ`, put

`bgInt θ = -(1/4π) ∫_ℝ log (K_θ(x)/K_0(x)) ρ(x) dx`

(the real form (BGreal) of `thm:BG`, Weyl/free_fermion/paper/parts/constants.tex: `K_0 = cosh πx + 1`).
For `|θ| < π`, `bgInt` is differentiable with
`bgInt' θ = (sin θ/4π) ∫_ℝ ρ(x)/K_θ(x) dx`  (`hasDerivAt_bgInt`, the formula (BGderiv)): the
integrand's `θ`-derivative is dominated by `C (1+|x|) e^{-π|x|}` uniformly for `|θ| ≤ π - η`, using
`K_θ ≥ κ cosh πx`, `κ = min 1 (1 - cos η)`, and the linear growth bound for `ψ`
(`norm_digamma_le`; the paper uses the sharper `O(log)`).
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex MeasureTheory Metric
open scoped Real

local notation "γ" => Real.eulerMascheroniConstant

/-- `ρ(x) = Re ψ(1/2 + ix/2)`. -/
noncomputable def rhoR (x : ℝ) : ℝ := (digamma (zOf (x : ℂ))).re

/-- Real kernel `cosh πx + cos θ`. -/
noncomputable def kerR (θ x : ℝ) : ℝ := Real.cosh (π * x) + Real.cos θ

lemma kerD_ofReal (θ x : ℝ) : kerD θ (x : ℂ) = ((kerR θ x : ℝ) : ℂ) := by
  unfold kerD kerR; push_cast; rfl

lemma continuous_digamma_zOf : Continuous fun x : ℝ => digamma (zOf (x : ℂ)) := by
  have h1 : Continuous fun x : ℝ => zOf (x : ℂ) := by unfold zOf; fun_prop
  have hz : ∀ x : ℝ, zOf (x : ℂ) ∈ rhp := fun x => by
    show 0 < (zOf (x : ℂ)).re
    rw [re_zOf]; simp
  exact (differentiableOn_digamma_rhp.continuousOn).comp_continuous h1 hz

lemma continuous_rhoR : Continuous rhoR :=
  Complex.continuous_re.comp continuous_digamma_zOf

/-- Linear growth of `ρ`. -/
lemma abs_rhoR_le (x : ℝ) : |rhoR x| ≤ (|γ| + 2 * invSqSum) * 3 * (1 + |x|) := by
  have hz : 1 / 2 ≤ (zOf (x : ℂ)).re := by rw [re_zOf]; simp
  have h1 := norm_digamma_le hz
  have h2 := norm_zOf_le (ξ := (x : ℂ)) (X := |x|) (by simp) (by simp) (by simp)
  have hCψ : 0 ≤ |γ| + 2 * invSqSum := by have := invSqSum_nonneg; positivity
  have : |rhoR x| ≤ ‖digamma (zOf (x : ℂ))‖ := Complex.abs_re_le_norm _
  refine this.trans (h1.trans ?_)
  have : 1 + ‖zOf (x : ℂ)‖ ≤ 3 * (1 + |x|) := by linarith [abs_nonneg x]
  calc (|γ| + 2 * invSqSum) * (1 + ‖zOf (x : ℂ)‖) ≤ (|γ| + 2 * invSqSum) * (3 * (1 + |x|)) :=
        mul_le_mul_of_nonneg_left this hCψ
    _ = _ := by ring

lemma re_psiKer (θ x : ℝ) : (psiKer θ x).re = rhoR x / kerR θ x := by
  unfold psiKer rhoR
  rw [kerD_ofReal, Complex.div_ofReal_re]

/-- Positive lower bound for the kernel in a compact sub-range of `|θ| < π`. -/
noncomputable def kappa (η : ℝ) : ℝ := min 1 (1 - Real.cos η)

lemma kappa_pos {η : ℝ} (h0 : 0 < η) (hπ : η < π) : 0 < kappa η := by
  have : Real.cos η < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0
  rw [Real.cos_zero] at this
  exact lt_min one_pos (by linarith)

lemma kappa_le_one (η : ℝ) : kappa η ≤ 1 := min_le_left _ _

lemma kerR_ge {η θ : ℝ} (hη : 0 < η) (hθ : |θ| ≤ π - η) (x : ℝ) :
    kappa η * Real.cosh (π * x) ≤ kerR θ x := by
  have hcos : -Real.cos η ≤ Real.cos θ := by
    have := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith : π - η ≤ π) hθ
    rw [Real.cos_abs, Real.cos_pi_sub] at this
    exact this
  have h1 : 1 ≤ Real.cosh (π * x) := Real.one_le_cosh _
  have hk1 := kappa_le_one η
  have hk2 : kappa η ≤ 1 - Real.cos η := min_le_right _ _
  unfold kerR
  nlinarith

lemma kerR_pos {θ : ℝ} (hθ : |θ| < π) (x : ℝ) : 0 < kerR θ x := by
  have := kerD_real_ge hθ x
  have h4 : 0 < min 1 (1 + Real.cos θ) * Real.cosh (π * x) :=
    mul_pos (min_one_cos_pos hθ) (Real.cosh_pos _)
  unfold kerR; linarith

lemma one_div_cosh_le (x : ℝ) : 1 / Real.cosh (π * x) ≤ 2 * Real.exp (-π * |x|) := by
  have h := exp_abs_le_two_cosh (π * x)
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  have hc := Real.cosh_pos (π * x)
  rw [div_le_iff₀ hc]
  have hE : Real.exp (-π * |x|) * Real.exp (π * |x|) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-π * |x|)]


/-- The integrand of (BGreal). -/
noncomputable def bgFun (θ x : ℝ) : ℝ := Real.log (kerR θ x / kerR 0 x) * rhoR x

/-- `B(θ)`, real form (BGreal) of `thm:BG`. -/
noncomputable def bgInt (θ : ℝ) : ℝ := -(1 / (4 * π)) * ∫ x : ℝ, bgFun θ x

lemma kerR_zero (x : ℝ) : kerR 0 x = Real.cosh (π * x) + 1 := by simp [kerR]

lemma abs_log_kerR_le {η θ : ℝ} (hη : 0 < η) (hηπ : η < π) (hθ : |θ| ≤ π - η) (x : ℝ) :
    |Real.log (kerR θ x / kerR 0 x)| ≤ (4 / kappa η) * Real.exp (-π * |x|) := by
  have hκ := kappa_pos hη hηπ
  have hθ' : |θ| < π := by linarith
  have ha := kerR_pos hθ' x
  have hb := kerR_pos (by rw [abs_zero]; exact Real.pi_pos) (x := x) (θ := 0)
  have hab : kerR θ x ≤ kerR 0 x := by
    unfold kerR; linarith [Real.cos_le_one θ, Real.cos_zero]
  have hlog : Real.log (kerR θ x / kerR 0 x) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one hb).mpr hab)
  rw [abs_of_nonpos hlog, ← Real.log_inv, inv_div]
  have h1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
  refine h1.trans ?_
  have hc := Real.cosh_pos (π * x)
  have h2 : kappa η * Real.cosh (π * x) ≤ kerR θ x := kerR_ge hη hθ x
  have h3 : kerR 0 x / kerR θ x - 1 = (kerR 0 x - kerR θ x) / kerR θ x := by field_simp
  rw [h3]
  have h4 : kerR 0 x - kerR θ x ≤ 2 := by
    unfold kerR; linarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, Real.cos_zero]
  have h5 : 0 ≤ kerR 0 x - kerR θ x := by linarith
  calc (kerR 0 x - kerR θ x) / kerR θ x ≤ 2 / (kappa η * Real.cosh (π * x)) :=
        div_le_div₀ (by norm_num) h4 (by positivity) h2
    _ = (2 / kappa η) * (1 / Real.cosh (π * x)) := by field_simp
    _ ≤ (2 / kappa η) * (2 * Real.exp (-π * |x|)) :=
        mul_le_mul_of_nonneg_left (one_div_cosh_le x) (by positivity)
    _ = (4 / kappa η) * Real.exp (-π * |x|) := by ring


lemma continuous_kerR (θ : ℝ) : Continuous (kerR θ) := by unfold kerR; fun_prop

lemma continuous_bgFun {θ : ℝ} (hθ : |θ| < π) : Continuous (bgFun θ) := by
  unfold bgFun
  refine Continuous.mul ?_ continuous_rhoR
  refine Continuous.log ((continuous_kerR θ).div (continuous_kerR 0) fun x => ?_) fun x => ?_
  · exact (kerR_pos (by rw [abs_zero]; exact Real.pi_pos) x).ne'
  · exact (div_pos (kerR_pos hθ x) (kerR_pos (by rw [abs_zero]; exact Real.pi_pos) x)).ne'

theorem hasDerivAt_bgInt {θ0 : ℝ} (hθ0 : |θ0| < π) :
    HasDerivAt bgInt (Real.sin θ0 / (4 * π) * ∫ x : ℝ, rhoR x / kerR θ0 x) θ0 := by
  set η : ℝ := (π - |θ0|) / 2 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hηπ : η < π := by rw [hη]; linarith [abs_nonneg θ0, Real.pi_pos]
  have hκ := kappa_pos hηpos hηπ
  set M : ℝ := (|γ| + 2 * invSqSum) * 3 with hM
  have hM0 : 0 ≤ M := by have := invSqSum_nonneg; rw [hM]; positivity
  have hs : ∀ θ ∈ ball θ0 η, |θ| ≤ π - η := by
    intro θ hθ
    rw [Metric.mem_ball, Real.dist_eq] at hθ
    have : |θ| ≤ |θ0| + |θ - θ0| := by
      calc |θ| = |θ0 + (θ - θ0)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [hη] at hθ ⊢
    linarith
  have hsπ : ∀ θ ∈ ball θ0 η, |θ| < π := fun θ hθ => by
    have := hs θ hθ; linarith
  have hθ0s : θ0 ∈ ball θ0 η := Metric.mem_ball_self hηpos
  -- majorant
  have hmaj : Integrable (fun x : ℝ => (2 * M / kappa η) * ((1 + |x|) * Real.exp (-π * |x|))) :=
    integrable_one_add_abs_mul_exp.const_mul _
  have hmaj2 : Integrable (fun x : ℝ => (4 * M / kappa η) * ((1 + |x|) * Real.exp (-π * |x|))) :=
    integrable_one_add_abs_mul_exp.const_mul _
  -- derivative integrand
  set F : ℝ → ℝ → ℝ := fun θ x => bgFun θ x with hF
  set F' : ℝ → ℝ → ℝ := fun θ x => (-Real.sin θ / kerR θ x) * rhoR x with hF'
  have hcontF' : ∀ θ, |θ| < π → Continuous (F' θ) := by
    intro θ hθ
    refine Continuous.mul (Continuous.div continuous_const (continuous_kerR θ) fun x => ?_)
      continuous_rhoR
    exact (kerR_pos hθ x).ne'
  have hFint : Integrable (F θ0) := by
    refine hmaj2.mono' (continuous_bgFun hθ0).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    show ‖bgFun θ0 x‖ ≤ _
    unfold bgFun
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_log_kerR_le hηpos hηπ (hs θ0 hθ0s) x
    have h2 := abs_rhoR_le x
    calc |Real.log (kerR θ0 x / kerR 0 x)| * |rhoR x|
        ≤ ((4 / kappa η) * Real.exp (-π * |x|)) * (M * (1 + |x|)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = (4 * M / kappa η) * ((1 + |x|) * Real.exp (-π * |x|)) := by ring
  have hbound : ∀ x : ℝ, ∀ θ ∈ ball θ0 η, ‖F' θ x‖ ≤
      (2 * M / kappa η) * ((1 + |x|) * Real.exp (-π * |x|)) := by
    intro x θ hθ
    have hpos := kerR_pos (hsπ θ hθ) x
    have hge := kerR_ge hηpos (hs θ hθ) x
    have hc := Real.cosh_pos (π * x)
    show ‖(-Real.sin θ / kerR θ x) * rhoR x‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos hpos]
    have h2 := abs_rhoR_le x
    have h3 : |Real.sin θ| / kerR θ x ≤ (2 / kappa η) * Real.exp (-π * |x|) := by
      calc |Real.sin θ| / kerR θ x ≤ 1 / (kappa η * Real.cosh (π * x)) :=
            div_le_div₀ (by norm_num) (Real.abs_sin_le_one θ) (by positivity) hge
        _ = (1 / kappa η) * (1 / Real.cosh (π * x)) := by field_simp
        _ ≤ (1 / kappa η) * (2 * Real.exp (-π * |x|)) :=
            mul_le_mul_of_nonneg_left (one_div_cosh_le x) (by positivity)
        _ = (2 / kappa η) * Real.exp (-π * |x|) := by ring
    calc |Real.sin θ| / kerR θ x * |rhoR x|
        ≤ ((2 / kappa η) * Real.exp (-π * |x|)) * (M * (1 + |x|)) :=
          mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
      _ = (2 * M / kappa η) * ((1 + |x|) * Real.exp (-π * |x|)) := by ring
  have hderiv : ∀ x : ℝ, ∀ θ ∈ ball θ0 η, HasDerivAt (fun θ => F θ x) (F' θ x) θ := by
    intro x θ hθ
    have hpos := kerR_pos (hsπ θ hθ) x
    have hb0 := kerR_pos (by rw [abs_zero]; exact Real.pi_pos : |(0 : ℝ)| < π) x
    have h1 : HasDerivAt (fun θ : ℝ => kerR θ x) (-Real.sin θ) θ := by
      unfold kerR
      exact (Real.hasDerivAt_cos θ).const_add _
    have h2 := (h1.div_const (kerR 0 x)).log (div_pos hpos hb0).ne'
    have h3 := h2.mul_const (rhoR x)
    refine h3.congr_deriv ?_
    simp only [hF']
    field_simp
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := F) (F' := F') (bound := fun x : ℝ => (2 * M / kappa η) * ((1 + |x|) * Real.exp (-π * |x|)))
    (ball_mem_nhds θ0 hηpos)
    (by filter_upwards [ball_mem_nhds θ0 hηpos] with θ hθ
        exact (continuous_bgFun (hsπ θ hθ)).aestronglyMeasurable)
    hFint (hcontF' θ0 hθ0).aestronglyMeasurable
    (Eventually.of_forall fun x θ hθ => hbound x θ hθ) hmaj
    (Eventually.of_forall fun x θ hθ => hderiv x θ hθ)
  have h2 := key.2.const_mul (-(1 / (4 * π)))
  have hfun : bgInt = fun θ => -(1 / (4 * π)) * ∫ x : ℝ, F θ x := rfl
  rw [hfun]
  refine h2.congr_deriv ?_
  simp only [hF']
  rw [← integral_const_mul]
  have : Real.sin θ0 / (4 * π) * ∫ x : ℝ, rhoR x / kerR θ0 x =
      ∫ x : ℝ, Real.sin θ0 / (4 * π) * (rhoR x / kerR θ0 x) := (integral_const_mul _ _).symm
  rw [this]
  congr 1
  ext x
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  ring

end FormalResearch.Special.Barnes
