module

public import FormalResearch.Special.BarnesContourSetup
public import FormalResearch.Special.BarnesDecay

/-!
# The contour shift of `thm:BG`

For real `θ ≠ 0`, `|θ| < π`, `b = θ/(2π)`:

`∫_ℝ ψ(1/2 + ix/2) / (cosh πx + cos θ) dx = 2 (Q(1+b) - Q(1-b)) / sin θ`   (`integral_digamma_div_kerD`),

with `Q = barnesQ` (the formula `∫ψ(z(ξ))(cosh πξ+cos θ)⁻¹ dξ = 2[Q(1+b)-Q(1-b)]/sin θ` of the proof of
`thm:BG` in Weyl/free_fermion/paper/parts/constants.tex).

Proof: Cauchy–Goursat on the rectangle `[-X,X] × [-2,0]` for `cH = N/D` of `BarnesContourSetup`,
using `N(ξ-2i) - N(ξ) = ψ(z(ξ))` and `D(ξ-2i) = D(ξ)` (the horizontal sides combine into the
integrand), then `X → ∞`: the right side tends to `-2β` and the left side to `0`, so the integral is `4 i β`
with `β = (Q₊ - Q₋)/(e^{πa₊} - e^{πa₋}) = (Q₊ - Q₋)/(-2 i sin θ)`.  Differs from the paper's wording only
in that the two simple poles are handled by interpolating `Q(z(ξ))` with `α + β e^{πξ}` (so the
integrand has removable singularities) rather than computing residues.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex MeasureTheory
open scoped Real

local notation "γ" => Real.eulerMascheroniConstant

lemma kerD_im_strip_ne {θ : ℝ} (hθ : |θ| < π) {y : ℝ} (hy : y = 0 ∨ y = -2) :
    ∀ x : ℝ, ((x : ℂ) + y * I) ≠ kerPlus θ ∧ ((x : ℂ) + y * I) ≠ kerMinus θ := by
  intro x
  have hθ' := abs_lt.mp hθ
  have hpi := Real.pi_pos
  have h1 : θ / π < 1 := (div_lt_one hpi).mpr hθ'.2
  have h2 : -1 < θ / π := by rw [lt_div_iff₀ hpi]; linarith
  constructor
  · intro h
    have := congrArg Complex.im h
    rw [im_kerPlus] at this
    simp at this
    rcases hy with rfl | rfl <;> linarith
  · intro h
    have := congrArg Complex.im h
    rw [im_kerMinus] at this
    simp at this
    rcases hy with rfl | rfl <;> linarith

/-- Cauchy–Goursat for `cH` on the rectangle `[-X,X] × [-2,0]`. -/
theorem cH_rect {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) (X : ℝ) :
    (∫ x : ℝ in (-X)..X, cH θ ((x : ℂ) + (-2 : ℝ) * I)) -
      (∫ x : ℝ in (-X)..X, cH θ ((x : ℂ) + (0 : ℝ) * I)) +
      I * (∫ y : ℝ in (-2 : ℝ)..0, cH θ ((X : ℂ) + y * I)) -
      I * (∫ y : ℝ in (-2 : ℝ)..0, cH θ (((-X : ℝ) : ℂ) + y * I)) = 0 := by
  have key := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (cH θ)
    (((-X : ℝ) : ℂ) + (-2 : ℝ) * I) ((X : ℂ) + (0 : ℝ) * I) {kerPlus θ, kerMinus θ}
    ((Set.toFinite _).countable) ?_ ?_
  · simpa using key
  · intro ξ hξ
    refine (continuousAt_cH_of_mem_strip h0 hθ ?_ ?_).continuousWithinAt
    all_goals
      rw [Complex.mem_reProdIm] at hξ
      have := hξ.2
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at this
      rw [Set.mem_uIcc] at this
    · rcases this with h | h <;> linarith [h.1]
    · rcases this with h | h <;> linarith [h.2]
  · intro ξ hξ
    have hξ1 := hξ.1
    rw [Complex.mem_reProdIm] at hξ1
    have := hξ1.2
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero, min_def, max_def] at this
    have hn : ξ ≠ kerPlus θ ∧ ξ ≠ kerMinus θ := by
      have := hξ.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
      exact this
    refine differentiableAt_cH_of_mem_strip hθ ?_ ?_ hn.1 hn.2
    all_goals
      rw [Set.mem_Ioo] at this
      split_ifs at this <;> linarith [this.1, this.2]


lemma cH_horizontal_diff {θ : ℝ} (hθ : |θ| < π) (x : ℝ) :
    cH θ ((x : ℂ) + (-2 : ℝ) * I) - cH θ ((x : ℂ) + (0 : ℝ) * I) =
      digamma (zOf x) / kerD θ x := by
  have hx0 : ((x : ℂ) + (0 : ℝ) * I) = x := by simp
  have hx2 : ((x : ℂ) + (-2 : ℝ) * I) = x - 2 * I := by push_cast; ring
  have n0 := kerD_im_strip_ne hθ (Or.inl rfl) x
  have n2 := kerD_im_strip_ne hθ (Or.inr rfl) x
  rw [hx0] at n0 ⊢
  rw [hx2] at n2 ⊢
  rw [cH_eq_of_ne n0.1 n0.2, cH_eq_of_ne n2.1 n2.2, kerD_sub_two_I, ← sub_div]
  congr 1
  unfold cN
  rw [zOf_sub_two_I, exp_pi_sub_two_I]
  have hre : 0 < (zOf x).re := by rw [re_zOf]; simp
  rw [barnesQ_add_one hre]
  ring


lemma re_kerPlus (θ : ℝ) : (kerPlus θ).re = 0 := by simp [kerPlus]
lemma re_kerMinus (θ : ℝ) : (kerMinus θ).re = 0 := by simp [kerMinus]

lemma norm_zOf_le {ξ : ℂ} {X : ℝ} (hX : |ξ.re| = X) (him1 : -2 ≤ ξ.im) (him2 : ξ.im ≤ 0) :
    1 + ‖zOf ξ‖ ≤ X + 3 := by
  have h1 : ‖zOf ξ‖ ≤ 1 / 2 + ‖ξ‖ / 2 := by
    unfold zOf
    calc ‖(1 / 2 : ℂ) + I * ξ / 2‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖I * ξ / 2‖ := norm_add_le _ _
      _ = 1 / 2 + ‖ξ‖ / 2 := by simp
  have h2 : ‖ξ‖ ≤ |ξ.re| + |ξ.im| := by
    have := Complex.norm_le_abs_re_add_abs_im ξ
    exact this
  have h3 : |ξ.im| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hX0 : 0 ≤ X := hX ▸ abs_nonneg _
  linarith

/-- Uniform bound on the vertical sides. -/
theorem cH_vertical_bound (θ : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ X : ℝ, 1 ≤ X → ∀ y : ℝ, -2 ≤ y → y ≤ 0 →
      ‖cH θ ((X : ℂ) + y * I) + 2 * cBeta θ‖ ≤ A * ((X + 3) ^ 2 * Real.exp (-π * X)) ∧
      ‖cH θ (((-X : ℝ) : ℂ) + y * I)‖ ≤ A * ((X + 3) ^ 2 * Real.exp (-π * X)) := by
  obtain ⟨C, hC, hQ⟩ := norm_barnesQ_le
  set K : ℝ := C + ‖cAlpha θ‖ + 3 * ‖cBeta θ‖ with hK
  have hK0 : 0 < K := by positivity
  refine ⟨8 * K, by positivity, fun X hX y hy1 hy2 => ?_⟩
  have hX0 : 0 < X := by linarith
  -- common facts
  have hQb : ∀ ξ : ℂ, |ξ.re| = X → ξ.im = y → ‖barnesQ (zOf ξ)‖ ≤ C * (X + 3) ^ 2 := by
    intro ξ hr hi
    have hre : 1 / 2 ≤ (zOf ξ).re := by rw [re_zOf]; linarith
    have h1 := hQ _ hre
    have h2 := norm_zOf_le hr (by linarith) (by linarith)
    refine h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 2) hC.le)
  have hsq : (1 : ℝ) ≤ (X + 3) ^ 2 := by nlinarith
  have hexp : 0 < Real.exp (-π * X) := Real.exp_pos _
  have hΔ : ∀ ξ : ℂ, |ξ.re| = X → Real.exp (π * X) / 8 ≤ ‖kerD θ ξ‖ := by
    intro ξ hr
    have := norm_kerD_ge θ (ξ := ξ) (by rw [hr]; exact hX)
    rwa [hr] at this
  have hE : Real.exp (-π * X) = (Real.exp (π * X))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hEpos : 0 < Real.exp (π * X) := Real.exp_pos _
  have div_bd : ∀ (n d : ℝ), 0 ≤ n → n ≤ K * (X + 3) ^ 2 → Real.exp (π * X) / 8 ≤ d →
      n / d ≤ 8 * K * ((X + 3) ^ 2 * Real.exp (-π * X)) := by
    intro n d hn0 hn hd
    have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd
    rw [div_le_iff₀ hdpos, hE]
    have : 8 * K * ((X + 3) ^ 2 * (Real.exp (π * X))⁻¹) * d ≥
        8 * K * ((X + 3) ^ 2 * (Real.exp (π * X))⁻¹) * (Real.exp (π * X) / 8) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    have h2 : 8 * K * ((X + 3) ^ 2 * (Real.exp (π * X))⁻¹) * (Real.exp (π * X) / 8) =
        K * (X + 3) ^ 2 := by field_simp
    linarith
  have hexp_le : ∀ w : ℂ, w.re ≤ 0 → ‖Complex.exp w‖ ≤ 1 := fun w hw => by
    rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hw
  have hK1 : ‖cAlpha θ‖ + 3 * ‖cBeta θ‖ ≤ (‖cAlpha θ‖ + 3 * ‖cBeta θ‖) * (X + 3) ^ 2 :=
    le_mul_of_one_le_right (by positivity) hsq
  constructor
  · -- right side
    set ξ : ℂ := (X : ℂ) + y * I with hξ
    have hre : ξ.re = X := by simp [hξ]
    have him : ξ.im = y := by simp [hξ]
    have hr : |ξ.re| = X := by rw [hre]; exact abs_of_pos hX0
    have hne1 : ξ ≠ kerPlus θ := fun h => by
      have := congrArg Complex.re h; rw [re_kerPlus, hre] at this; linarith
    have hne2 : ξ ≠ kerMinus θ := fun h => by
      have := congrArg Complex.re h; rw [re_kerMinus, hre] at this; linarith
    have hDne : kerD θ ξ ≠ 0 := by
      intro h
      have := hΔ ξ hr
      rw [h, norm_zero] at this
      linarith
    rw [cH_eq_of_ne hne1 hne2, ← mul_div_cancel_right₀ (2 * cBeta θ) hDne, ← add_div]
    rw [norm_div]
    have hnum : cN θ ξ + 2 * cBeta θ * kerD θ ξ =
        barnesQ (zOf ξ) - cAlpha θ + cBeta θ * (Complex.exp (-(π * ξ)) + 2 * (Real.cos θ : ℂ)) := by
      unfold cN kerD Complex.cosh
      ring
    rw [hnum]
    refine div_bd _ _ (norm_nonneg _) ?_ (hΔ ξ hr)
    have e1 : ‖Complex.exp (-(π * ξ))‖ ≤ 1 := hexp_le _ (by simp [hre]; positivity)
    have e2 : ‖((Real.cos θ : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one θ
    have e3 : ‖Complex.exp (-(π * ξ)) + 2 * (Real.cos θ : ℂ)‖ ≤ 3 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]; simp only [norm_ofNat] ; linarith
    calc ‖barnesQ (zOf ξ) - cAlpha θ + cBeta θ * (Complex.exp (-(π * ξ)) + 2 * (Real.cos θ : ℂ))‖
        ≤ ‖barnesQ (zOf ξ)‖ + ‖cAlpha θ‖ + ‖cBeta θ‖ * 3 := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _)) ?_)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left e3 (norm_nonneg _)
      _ ≤ C * (X + 3) ^ 2 + (‖cAlpha θ‖ + 3 * ‖cBeta θ‖) * (X + 3) ^ 2 := by
          have := hQb ξ hr him
          nlinarith
      _ = K * (X + 3) ^ 2 := by rw [hK]; ring
  · -- left side
    set ξ : ℂ := ((-X : ℝ) : ℂ) + y * I with hξ
    have hre : ξ.re = -X := by simp [hξ]
    have him : ξ.im = y := by simp [hξ]
    have hr : |ξ.re| = X := by rw [hre, abs_neg]; exact abs_of_pos hX0
    have hne1 : ξ ≠ kerPlus θ := fun h => by
      have := congrArg Complex.re h; rw [re_kerPlus, hre] at this; linarith
    have hne2 : ξ ≠ kerMinus θ := fun h => by
      have := congrArg Complex.re h; rw [re_kerMinus, hre] at this; linarith
    rw [cH_eq_of_ne hne1 hne2, norm_div]
    refine div_bd _ _ (norm_nonneg _) ?_ (hΔ ξ hr)
    have e1 : ‖Complex.exp (π * ξ)‖ ≤ 1 := hexp_le _ (by simp [hre]; positivity)
    calc ‖cN θ ξ‖ ≤ ‖barnesQ (zOf ξ)‖ + ‖cAlpha θ‖ + ‖cBeta θ‖ * 1 := by
          unfold cN
          refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left e1 (norm_nonneg _)
      _ ≤ C * (X + 3) ^ 2 + (‖cAlpha θ‖ + 3 * ‖cBeta θ‖) * (X + 3) ^ 2 := by
          have := hQb ξ hr him
          nlinarith [norm_nonneg (cBeta θ)]
      _ = K * (X + 3) ^ 2 := by rw [hK]; ring


lemma continuousOn_cH_vertical {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) (x : ℝ) :
    ContinuousOn (fun y : ℝ => cH θ ((x : ℂ) + y * I)) (uIcc (-2 : ℝ) 0) := by
  intro y hy
  rw [Set.mem_uIcc] at hy
  have hc : ContinuousAt (cH θ) ((x : ℂ) + y * I) := by
    refine continuousAt_cH_of_mem_strip h0 hθ ?_ ?_ <;> simp <;> rcases hy with h | h <;> linarith [h.1, h.2]
  have : Continuous fun y : ℝ => (x : ℂ) + y * I := by fun_prop
  exact (hc.comp_of_eq this.continuousAt rfl).continuousWithinAt

theorem tendsto_cH_right {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) :
    Tendsto (fun X : ℝ => ∫ y : ℝ in (-2 : ℝ)..0, cH θ ((X : ℂ) + y * I)) atTop
      (𝓝 (-4 * cBeta θ)) := by
  obtain ⟨A, hA, hb⟩ := cH_vertical_bound θ
  have hlim : Tendsto (fun X : ℝ => (∫ y : ℝ in (-2 : ℝ)..0, cH θ ((X : ℂ) + y * I)) +
      4 * cBeta θ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun X : ℝ => 2 * A * ((X + 3) ^ 2 * Real.exp (-π * X))) atTop (𝓝 0) := by
      simpa using tendsto_poly_exp.const_mul (2 * A)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hint : IntervalIntegrable (fun y : ℝ => cH θ ((X : ℂ) + y * I)) volume (-2) 0 :=
      (continuousOn_cH_vertical h0 hθ X).intervalIntegrable
    have hsplit : (∫ y : ℝ in (-2 : ℝ)..0, cH θ ((X : ℂ) + y * I)) + 4 * cBeta θ =
        ∫ y : ℝ in (-2 : ℝ)..0, (cH θ ((X : ℂ) + y * I) + 2 * cBeta θ) := by
      rw [intervalIntegral.integral_add hint intervalIntegrable_const, intervalIntegral.integral_const]
      simp; ring
    rw [hsplit]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -2) (b := 0)
      (f := fun y : ℝ => cH θ ((X : ℂ) + y * I) + 2 * cBeta θ)
      (C := A * ((X + 3) ^ 2 * Real.exp (-π * X)))
      (fun y hy => by
        rw [Set.uIoc_of_le (by norm_num)] at hy
        exact (hb X hX y hy.1.le hy.2).1)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have := hlim.sub_const (4 * cBeta θ)
  simpa using this

theorem tendsto_cH_left (θ : ℝ) :
    Tendsto (fun X : ℝ => ∫ y : ℝ in (-2 : ℝ)..0, cH θ (((-X : ℝ) : ℂ) + y * I)) atTop (𝓝 0) := by
  obtain ⟨A, hA, hb⟩ := cH_vertical_bound θ
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun X : ℝ => 2 * A * ((X + 3) ^ 2 * Real.exp (-π * X))) atTop (𝓝 0) := by
    simpa using tendsto_poly_exp.const_mul (2 * A)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [eventually_ge_atTop 1] with X hX
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -2) (b := 0)
    (f := fun y : ℝ => cH θ (((-X : ℝ) : ℂ) + y * I))
    (C := A * ((X + 3) ^ 2 * Real.exp (-π * X)))
    (fun y hy => by
      rw [Set.uIoc_of_le (by norm_num)] at hy
      exact (hb X hX y hy.1.le hy.2).2)
  simpa [mul_comm, mul_assoc, mul_left_comm] using this


lemma continuousOn_cH_horizontal {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) {c : ℝ} (hc1 : -2 ≤ c)
    (hc2 : c ≤ 0) : Continuous (fun x : ℝ => cH θ ((x : ℂ) + (c : ℝ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc : ContinuousAt (cH θ) ((x : ℂ) + (c : ℝ) * I) :=
    continuousAt_cH_of_mem_strip h0 hθ (by simpa using hc1) (by simpa using hc2)
  have : Continuous fun x : ℝ => (x : ℂ) + (c : ℝ) * I := by fun_prop
  exact hc.comp_of_eq this.continuousAt rfl

/-- The integrand `ψ(z(x)) / (cosh πx + cos θ)`. -/
noncomputable def psiKer (θ : ℝ) (x : ℝ) : ℂ := digamma (zOf x) / kerD θ x

lemma continuous_psiKer {θ : ℝ} (hθ : |θ| < π) : Continuous (psiKer θ) := by
  have h1 : Continuous fun x : ℝ => zOf (x : ℂ) := by unfold zOf; fun_prop
  have hz : ∀ x : ℝ, zOf (x : ℂ) ∈ rhp := fun x => by
    show 0 < (zOf (x : ℂ)).re
    rw [re_zOf]; simp
  have h2 : Continuous fun x : ℝ => digamma (zOf (x : ℂ)) :=
    (differentiableOn_digamma_rhp.continuousOn).comp_continuous h1 hz
  have h3 : Continuous fun x : ℝ => kerD θ (x : ℂ) := by unfold kerD; fun_prop
  refine h2.div h3 (fun x => ?_)
  have hc0 := min_one_cos_pos hθ
  have hk : kerD θ (x : ℂ) = (((Real.cosh (π * x) + Real.cos θ : ℝ)) : ℂ) := by
    unfold kerD; push_cast; rfl
  rw [hk]
  have := kerD_real_ge hθ x
  have h4 : 0 < min 1 (1 + Real.cos θ) * Real.cosh (π * x) :=
    mul_pos hc0 (Real.cosh_pos _)
  exact_mod_cast (lt_of_lt_of_le h4 this).ne'

lemma norm_psiKer_le {θ : ℝ} (hθ : |θ| < π) (x : ℝ) :
    ‖psiKer θ x‖ ≤ ((|γ| + 2 * invSqSum) * 3 * (2 / min 1 (1 + Real.cos θ))) *
      ((1 + |x|) * Real.exp (-π * |x|)) := by
  set Cψ := |γ| + 2 * invSqSum
  have hc0 := min_one_cos_pos hθ
  have hz : 1 / 2 ≤ (zOf (x : ℂ)).re := by rw [re_zOf]; simp
  have h1 := norm_digamma_le hz
  have h2 := norm_zOf_le (ξ := (x : ℂ)) (X := |x|) (by simp) (by simp) (by simp)
  have hCψ : 0 ≤ Cψ := by have := invSqSum_nonneg; positivity
  have hnum : ‖digamma (zOf (x : ℂ))‖ ≤ Cψ * 3 * (1 + |x|) := by
    refine h1.trans ?_
    have : 1 + ‖zOf (x : ℂ)‖ ≤ 3 * (1 + |x|) := by linarith [abs_nonneg x]
    calc Cψ * (1 + ‖zOf (x : ℂ)‖) ≤ Cψ * (3 * (1 + |x|)) := mul_le_mul_of_nonneg_left this hCψ
      _ = Cψ * 3 * (1 + |x|) := by ring
  have hk : kerD θ (x : ℂ) = (((Real.cosh (π * x) + Real.cos θ : ℝ)) : ℂ) := by
    unfold kerD; push_cast; rfl
  have hden : min 1 (1 + Real.cos θ) * (Real.exp (π * |x|) / 2) ≤ ‖kerD θ (x : ℂ)‖ := by
    rw [hk, Complex.norm_real, Real.norm_eq_abs]
    have h3 := kerD_real_ge hθ x
    have h4 : 0 < Real.cosh (π * x) + Real.cos θ :=
      lt_of_lt_of_le (mul_pos hc0 (Real.cosh_pos _)) h3
    rw [abs_of_pos h4]
    refine le_trans ?_ h3
    refine mul_le_mul_of_nonneg_left ?_ hc0.le
    have := exp_abs_le_two_cosh (π * x)
    rw [abs_mul, abs_of_pos Real.pi_pos] at this
    linarith
  unfold psiKer
  rw [norm_div]
  have hEpos : 0 < Real.exp (π * |x|) := Real.exp_pos _
  have hdpos : 0 < ‖kerD θ (x : ℂ)‖ := lt_of_lt_of_le (by positivity) hden
  rw [div_le_iff₀ hdpos]
  have hE : Real.exp (-π * |x|) * Real.exp (π * |x|) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖digamma (zOf (x : ℂ))‖ ≤ Cψ * 3 * (1 + |x|) := hnum
    _ = (Cψ * 3 * (2 / min 1 (1 + Real.cos θ))) * ((1 + |x|) * Real.exp (-π * |x|)) *
        (min 1 (1 + Real.cos θ) * (Real.exp (π * |x|) / 2)) := by
        have e : (Cψ * 3 * (2 / min 1 (1 + Real.cos θ))) * ((1 + |x|) * Real.exp (-π * |x|)) *
            (min 1 (1 + Real.cos θ) * (Real.exp (π * |x|) / 2)) =
            Cψ * 3 * (1 + |x|) * ((Real.exp (-π * |x|) * Real.exp (π * |x|)) *
              ((2 / min 1 (1 + Real.cos θ)) * (min 1 (1 + Real.cos θ) / 2))) := by ring
        have e2 : (2 / min 1 (1 + Real.cos θ)) * (min 1 (1 + Real.cos θ) / 2) = 1 := by
          field_simp
        rw [e, hE, e2]; ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left hden (by positivity)

theorem integrable_psiKer {θ : ℝ} (hθ : |θ| < π) : Integrable (psiKer θ) := by
  refine (integrable_one_add_abs_mul_exp.const_mul
    ((|γ| + 2 * invSqSum) * 3 * (2 / min 1 (1 + Real.cos θ)))).mono'
    (continuous_psiKer hθ).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  exact norm_psiKer_le hθ x


/-- `∫_ℝ ψ(z(x)) / (cosh πx + cos θ) dx = 4 i β`. -/
theorem integral_psiKer_eq {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) :
    ∫ x : ℝ, psiKer θ x = 4 * I * cBeta θ := by
  have hg := integrable_psiKer hθ
  have hlim1 : Tendsto (fun X : ℝ => ∫ x : ℝ in (-X)..X, psiKer θ x) atTop
      (𝓝 (∫ x : ℝ, psiKer θ x)) :=
    intervalIntegral_tendsto_integral hg tendsto_neg_atTop_atBot tendsto_id
  have hrel : ∀ X : ℝ, ∫ x : ℝ in (-X)..X, psiKer θ x =
      I * (∫ y : ℝ in (-2 : ℝ)..0, cH θ (((-X : ℝ) : ℂ) + y * I)) -
      I * (∫ y : ℝ in (-2 : ℝ)..0, cH θ ((X : ℂ) + y * I)) := by
    intro X
    have hR := cH_rect h0 hθ X
    have hc2 := continuousOn_cH_horizontal h0 hθ (c := -2) (by norm_num) (by norm_num)
    have hc0 := continuousOn_cH_horizontal h0 hθ (c := 0) (by norm_num) (by norm_num)
    have hsub : ∫ x : ℝ in (-X)..X, psiKer θ x =
        (∫ x : ℝ in (-X)..X, cH θ ((x : ℂ) + (-2 : ℝ) * I)) -
        (∫ x : ℝ in (-X)..X, cH θ ((x : ℂ) + (0 : ℝ) * I)) := by
      rw [← intervalIntegral.integral_sub (hc2.intervalIntegrable _ _) (hc0.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun x _ => ?_
      exact (cH_horizontal_diff hθ x).symm
    rw [hsub]
    linear_combination hR
  have hlim2 : Tendsto (fun X : ℝ => ∫ x : ℝ in (-X)..X, psiKer θ x) atTop
      (𝓝 (I * 0 - I * (-4 * cBeta θ))) := by
    simp_rw [hrel]
    exact (tendsto_cH_left θ).const_mul I |>.sub ((tendsto_cH_right h0 hθ).const_mul I)
  have := tendsto_nhds_unique hlim1 hlim2
  rw [this]; ring


/-- **Contour shift of `thm:BG`.**  For real `θ ≠ 0`, `|θ| < π`, `b = θ/(2π)`:
`∫_ℝ ψ(1/2 + ix/2) / (cosh πx + cos θ) dx = 2 (Q(1+b) - Q(1-b)) / sin θ`. -/
theorem integral_digamma_div_kerD {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) :
    ∫ x : ℝ, digamma (zOf x) / kerD θ x =
      2 * (barnesQ (1 + (θ : ℂ) / (2 * π)) - barnesQ (1 - (θ : ℂ) / (2 * π))) /
        (Real.sin θ : ℂ) := by
  have h := integral_psiKer_eq h0 hθ
  have hs : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast sin_ne_zero_of_abs_lt h0 hθ
  change ∫ x : ℝ, psiKer θ x = _
  rw [h]
  unfold cBeta cQplus cQminus
  rw [exp_kerPlus_sub_exp_kerMinus, zOf_kerPlus, zOf_kerMinus]
  field_simp
  ring

/-- info: 'FormalResearch.Special.Barnes.integral_digamma_div_kerD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_digamma_div_kerD

end FormalResearch.Special.Barnes
