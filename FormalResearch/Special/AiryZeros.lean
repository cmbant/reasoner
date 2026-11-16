module

public import FormalResearch.Special.AiryPositive

/-!
# All zeros of `Ai` are real and negative

`airyAiC_zero_real_neg`: if `Ai(z₀) = 0` for `z₀ ∈ ℂ` then `Im z₀ = 0` and `Re z₀ < 0`.

Proof (self-adjointness).  Put `y(x) = Ai(z₀ + x)` for real `x ≥ 0`; then `y(0) = 0`, `y'' = (z₀ + x) y`
and `y`, `y'` decay like `e^{-x}` (`airyMom_one_norm_le`, from the contour representation with
`c = 1`; for fixed `Im z` the Gaussian factor is uniform).  Integrating `(ȳ y')' = |y'|² + (z₀ + x)|y|²`
over `(0, ∞)` gives `z₀ ∫|y|² = -(∫|y'|² + ∫ x|y|²)`, with `∫|y|² > 0` (otherwise the entire function
`Ai` vanishes on a ray, hence identically, contradicting `Ai(1) > 0`).  So `z₀` is real and `≤ 0`;
`z₀ ≠ 0` since `Ai(0) > 0` (`airyAi_pos`).
-/

@[expose] public section

open Filter Topology MeasureTheory Set Complex
open scoped Real

namespace FormalResearch.Special

/-- Majorant on the line `c = 1`, uniform in `Re z`: for the moments `M_k(1, z)`. -/
lemma norm_airyPoly_one_le (k : ℕ) (z : ℂ) (s : ℝ) :
    ‖airyPoly k 1 z s‖ ≤ Real.exp (1 / 3 - z.re + z.im ^ 2 / 2) *
      ((|(1 : ℝ)| + |s|) ^ k * Real.exp (-(1 / 2) * s ^ 2)) := by
  have hLn : ‖airyLine 1 s‖ ≤ |(1 : ℝ)| + |s| := norm_airyLine_le 1 s
  have hpow : ‖airyLine 1 s‖ ^ k ≤ (|(1 : ℝ)| + |s|) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) hLn k
  have hexp : (1 : ℝ) ^ 3 / 3 - z.re * 1 + z.im * s - 1 * s ^ 2 ≤
      (1 / 3 - z.re + z.im ^ 2 / 2) + (-(1 / 2) * s ^ 2) := by
    nlinarith [sq_nonneg (z.im - s)]
  rw [norm_airyPoly]
  calc ‖airyLine 1 s‖ ^ k * Real.exp ((1 : ℝ) ^ 3 / 3 - z.re * 1 + z.im * s - 1 * s ^ 2)
      ≤ (|(1 : ℝ)| + |s|) ^ k * Real.exp ((1 / 3 - z.re + z.im ^ 2 / 2) + (-(1 / 2) * s ^ 2)) :=
        mul_le_mul hpow (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- `‖M_k(1, z)‖ ≤ J_k · exp(1/3 - Re z + (Im z)²/2)`, `J_k = (1/2π) ∫ (1+|s|)^k e^{-s²/2} ds`. -/
lemma airyMom_one_norm_le (k : ℕ) (z : ℂ) :
    ‖airyMom k 1 z‖ ≤ (1 / (2 * π) * ∫ s : ℝ, (|(1 : ℝ)| + |s|) ^ k * Real.exp (-(1 / 2) * s ^ 2)) *
      Real.exp (1 / 3 - z.re + z.im ^ 2 / 2) := by
  refine (norm_airyMom_le_integral k 1 z).trans ?_
  have hi : Integrable (fun s : ℝ => (|(1 : ℝ)| + |s|) ^ k * Real.exp (-(1 / 2) * s ^ 2)) :=
    integrable_absAdd_pow_gauss 1 (by norm_num) k
  have h1 : ∫ s, ‖airyPoly k 1 z s‖ ≤ ∫ s : ℝ, Real.exp (1 / 3 - z.re + z.im ^ 2 / 2) *
      ((|(1 : ℝ)| + |s|) ^ k * Real.exp (-(1 / 2) * s ^ 2)) :=
    integral_mono (integrable_airyPoly one_pos k z).norm (hi.const_mul _)
      fun s => norm_airyPoly_one_le k z s
  rw [integral_const_mul] at h1
  calc 1 / (2 * π) * ∫ s, ‖airyPoly k 1 z s‖
      ≤ 1 / (2 * π) * (Real.exp (1 / 3 - z.re + z.im ^ 2 / 2) *
          ∫ s : ℝ, (|(1 : ℝ)| + |s|) ^ k * Real.exp (-(1 / 2) * s ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- Exponential decay along a horizontal ray: for fixed `z₀` there is `C` with
`‖M_k(1, z₀ + x)‖ ≤ C e^{-x}` for all real `x`. -/
lemma airyMom_ray_decay (k : ℕ) (z₀ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖airyMom k 1 (z₀ + x)‖ ≤ C * Real.exp (-x) := by
  set J := 1 / (2 * π) * ∫ s : ℝ, (|(1 : ℝ)| + |s|) ^ k * Real.exp (-(1 / 2) * s ^ 2) with hJ
  have hJ0 : 0 ≤ J := by
    rw [hJ]
    exact mul_nonneg (by positivity) (integral_nonneg fun s => by positivity)
  refine ⟨J * Real.exp (1 / 3 - z₀.re + z₀.im ^ 2 / 2), by positivity, fun x => ?_⟩
  refine (airyMom_one_norm_le k (z₀ + x)).trans (le_of_eq ?_)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
  rw [show 1 / 3 - (z₀.re + x) + z₀.im ^ 2 / 2 = (1 / 3 - z₀.re + z₀.im ^ 2 / 2) + -x by ring,
    Real.exp_add]
  ring

/-- An entire function vanishing on a horizontal ray vanishes identically. -/
lemma entire_eq_zero_of_ray {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z₀ : ℂ)
    (h : ∀ x : ℝ, 0 < x → f (z₀ + x) = 0) (z : ℂ) : f z = 0 := by
  have han : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have ht : Tendsto (fun x : ℝ => z₀ + (x : ℂ)) (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun x : ℝ => z₀ + (x : ℂ)) (𝓝 0) (𝓝 (z₀ + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, Complex.ofReal_eq_zero]
      exact ne_of_gt hx
  have hfreq : Filter.Frequently (fun x : ℝ => f (z₀ + (x : ℂ)) = 0) (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) := by
    exact ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).mono fun x hx => h x hx).frequently
  have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ z₀)
    (ht.frequently hfreq) (mem_univ z)
  simpa using this


/-- The shifted solution `y(x) = Ai(z₀ + x)`, `x ∈ ℝ`. -/
noncomputable def airyRay (z₀ : ℂ) (x : ℝ) : ℂ := airyAiC (z₀ + x)

/-- Its derivative `y'(x) = Ai'(z₀ + x)`. -/
noncomputable def airyRay' (z₀ : ℂ) (x : ℝ) : ℂ := deriv airyAiC (z₀ + x)

lemma hasDerivAt_airyRay (z₀ : ℂ) (x : ℝ) : HasDerivAt (airyRay z₀) (airyRay' z₀ x) x := by
  have h : HasDerivAt airyAiC (deriv airyAiC (z₀ + x)) (z₀ + x) :=
    differentiable_airyAiC.differentiableAt.hasDerivAt
  exact (h.comp_const_add z₀ (x : ℂ)).comp_ofReal

lemma hasDerivAt_airyRay' (z₀ : ℂ) (x : ℝ) :
    HasDerivAt (airyRay' z₀) ((z₀ + x) * airyRay z₀ x) x := by
  have h := hasDerivAt_deriv_airyAiC (z₀ + x)
  exact (h.comp_const_add z₀ (x : ℂ)).comp_ofReal

lemma continuous_airyRay (z₀ : ℂ) : Continuous (airyRay z₀) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyRay z₀ x).continuousAt

lemma continuous_airyRay' (z₀ : ℂ) : Continuous (airyRay' z₀) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyRay' z₀ x).continuousAt

lemma airyRay_decay (z₀ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖airyRay z₀ x‖ ≤ C * Real.exp (-x) ∧
      ‖airyRay' z₀ x‖ ≤ C * Real.exp (-x) := by
  obtain ⟨C₀, hC₀, h₀⟩ := airyMom_ray_decay 0 z₀
  obtain ⟨C₁, hC₁, h₁⟩ := airyMom_ray_decay 1 z₀
  refine ⟨max C₀ C₁, le_max_of_le_left hC₀, fun x => ⟨?_, ?_⟩⟩
  · exact (h₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have : airyRay' z₀ x = airyMom 1 1 (z₀ + x) := deriv_airyAiC one_pos _
    rw [this]
    exact (h₁ x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

/-- **All zeros of `Ai` are real and negative.** -/
theorem airyAiC_zero_real_neg {z₀ : ℂ} (h0 : airyAiC z₀ = 0) : z₀.im = 0 ∧ z₀.re < 0 := by
  obtain ⟨C, hC, hdec⟩ := airyRay_decay z₀
  set y := airyRay z₀ with hy
  set y' := airyRay' z₀ with hy'
  set p : ℝ → ℝ := fun x => Complex.normSq (y x) with hp
  set q : ℝ → ℝ := fun x => Complex.normSq (y' x) with hq
  have hpc : Continuous p := Complex.continuous_normSq.comp (continuous_airyRay z₀)
  have hqc : Continuous q := Complex.continuous_normSq.comp (continuous_airyRay' z₀)
  have hexp : ∀ x : ℝ, Real.exp (-x) ^ 2 = Real.exp (-2 * x) := fun x => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hpb : ∀ x, p x ≤ C ^ 2 * Real.exp (-2 * x) := fun x => by
    rw [hp]; simp only []
    rw [Complex.normSq_eq_norm_sq, ← hexp, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdec x).1 2
  have hqb : ∀ x, q x ≤ C ^ 2 * Real.exp (-2 * x) := fun x => by
    rw [hq]; simp only []
    rw [Complex.normSq_eq_norm_sq, ← hexp, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdec x).2 2
  have e2 : IntegrableOn (fun x : ℝ => C ^ 2 * Real.exp (-2 * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (b := 2) two_pos).const_mul _
  have e1 : IntegrableOn (fun x : ℝ => C ^ 2 * Real.exp (-1 * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (b := 1) one_pos).const_mul _
  have hpi : IntegrableOn p (Ioi 0) :=
    Integrable.mono' e2 hpc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Complex.normSq_nonneg _)]; exact hpb x)
  have hqi : IntegrableOn q (Ioi 0) :=
    Integrable.mono' e2 hqc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Complex.normSq_nonneg _)]; exact hqb x)
  have hxpi : IntegrableOn (fun x => x * p x) (Ioi 0) := by
    refine Integrable.mono' e1 (continuous_id.mul hpc).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    rw [Real.norm_of_nonneg (mul_nonneg hx0.le (Complex.normSq_nonneg _))]
    have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have h2 : Real.exp (-2 * x) * Real.exp x = Real.exp (-1 * x) := by
      rw [← Real.exp_add]; congr 1; ring
    calc x * p x ≤ x * (C ^ 2 * Real.exp (-2 * x)) :=
          mul_le_mul_of_nonneg_left (hpb x) hx0.le
      _ ≤ Real.exp x * (C ^ 2 * Real.exp (-2 * x)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = C ^ 2 * Real.exp (-1 * x) := by rw [← h2]; ring
  -- the complex identity
  set F : ℝ → ℂ := fun x => star (y x) * y' x with hF
  set F' : ℝ → ℂ := fun x => (q x : ℂ) + z₀ * (p x : ℂ) + ((x * p x : ℝ) : ℂ) with hF'
  have hcm : ∀ w : ℂ, star w * w = (Complex.normSq w : ℂ) := fun w => by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  have hFd : ∀ x : ℝ, HasDerivAt F (F' x) x := fun x => by
    have h := ((hasDerivAt_airyRay z₀ x).star).mul (hasDerivAt_airyRay' z₀ x)
    refine h.congr_deriv ?_
    have e1 := hcm (y' x)
    have e2 := hcm (y x)
    simp only [hF', hq, hp]
    push_cast
    rw [← e1, ← e2]
    ring
  have hF'i : IntegrableOn F' (Ioi 0) := by
    have := ((hqi.ofReal (𝕜 := ℂ)).add ((hpi.ofReal (𝕜 := ℂ)).const_mul z₀)).add
      (hxpi.ofReal (𝕜 := ℂ))
    exact this
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have hl : Tendsto (fun x : ℝ => C * Real.exp (-x) * (C * Real.exp (-x))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C)
      simpa using this.mul this
    refine squeeze_zero_norm (fun x => ?_) hl
    rw [hF]; simp only [norm_mul, norm_star]
    exact mul_le_mul (hdec x).1 (hdec x).2 (norm_nonneg _) (by positivity)
  have hF0 : F 0 = 0 := by
    simp [hF, hy, airyRay, h0]
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun x _ => hFd x) hF'i hFlim
  rw [hF0, sub_zero] at hint
  have hsplit : ∫ x in Ioi (0 : ℝ), F' x =
      ((∫ x in Ioi (0 : ℝ), q x : ℝ) : ℂ) + z₀ * ((∫ x in Ioi (0 : ℝ), p x : ℝ) : ℂ) +
        ((∫ x in Ioi (0 : ℝ), x * p x : ℝ) : ℂ) := by
    have i1 : IntegrableOn (fun x : ℝ => ((q x : ℝ) : ℂ)) (Ioi 0) := hqi.ofReal
    have i2 : IntegrableOn (fun x : ℝ => z₀ * ((p x : ℝ) : ℂ)) (Ioi 0) := (hpi.ofReal).const_mul z₀
    have i3 : IntegrableOn (fun x : ℝ => ((x * p x : ℝ) : ℂ)) (Ioi 0) := hxpi.ofReal
    have i12 : IntegrableOn (fun x : ℝ => ((q x : ℝ) : ℂ) + z₀ * ((p x : ℝ) : ℂ)) (Ioi 0) :=
      i1.add i2
    simp only [hF']
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_complex_ofReal,
      integral_complex_ofReal, integral_complex_ofReal]
  rw [hsplit] at hint
  set Q := ∫ x in Ioi (0 : ℝ), q x with hQ
  set A := ∫ x in Ioi (0 : ℝ), p x with hA
  set X := ∫ x in Ioi (0 : ℝ), x * p x with hX
  have hQ0 : 0 ≤ Q := setIntegral_nonneg measurableSet_Ioi fun x _ => Complex.normSq_nonneg _
  have hX0 : 0 ≤ X := setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mul_nonneg (le_of_lt hx) (Complex.normSq_nonneg _)
  have hApos : 0 < A := by
    have hex : ∃ x0 : ℝ, 0 < x0 ∧ 0 < p x0 := by
      by_contra hno
      simp only [not_exists, not_and, not_lt] at hno
      have hz : ∀ x : ℝ, 0 < x → airyAiC (z₀ + x) = 0 := fun x hx => by
        have h1 := hno x hx
        have h2 : Complex.normSq (y x) = 0 := le_antisymm h1 (Complex.normSq_nonneg _)
        exact Complex.normSq_eq_zero.mp h2
      have h1 := entire_eq_zero_of_ray differentiable_airyAiC z₀ hz ((1 : ℝ) : ℂ)
      rw [airyAiC_ofReal] at h1
      exact (airyAi_pos zero_le_one).ne' (by exact_mod_cast h1)
    obtain ⟨x0, hx0, hpx0⟩ := hex
    obtain ⟨δ, hδ, hδp⟩ := Metric.continuousAt_iff.mp hpc.continuousAt (p x0 / 2) (by positivity)
    set r := min δ x0 with hr
    have hrpos : 0 < r := lt_min hδ hx0
    have hsub : Ioo (x0 - r) (x0 + r) ⊆ Ioi 0 := fun x hx => by
      have : r ≤ x0 := min_le_right _ _
      exact lt_of_le_of_lt (by linarith) hx.1
    have hlow : ∀ x ∈ Ioo (x0 - r) (x0 + r), p x0 / 2 ≤ p x := fun x hx => by
      have hd : dist x x0 < δ := by
        rw [Real.dist_eq, abs_lt]
        have : r ≤ δ := min_le_left _ _
        constructor <;> linarith [hx.1, hx.2]
      have := hδp hd
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have h1 : p x0 / 2 * (volume.real (Ioo (x0 - r) (x0 + r))) ≤ ∫ x in Ioo (x0 - r) (x0 + r), p x :=
      setIntegral_ge_of_const_le_real measurableSet_Ioo (by simp) hlow (hpi.mono_set hsub)
    have h2 : ∫ x in Ioo (x0 - r) (x0 + r), p x ≤ A :=
      setIntegral_mono_set hpi (Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hsub hx)
    have h3 : volume.real (Ioo (x0 - r) (x0 + r)) = 2 * r := by
      rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]; ring
    rw [h3] at h1
    have : 0 < p x0 / 2 * (2 * r) := by positivity
    linarith
  have hz : z₀ = ((-(Q + X) / A : ℝ) : ℂ) := by
    have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
    push_cast
    field_simp
    linear_combination hint
  have hre : z₀.re = -(Q + X) / A := by rw [hz]; simp
  have him : z₀.im = 0 := by rw [hz]; simp
  refine ⟨him, ?_⟩
  have hle : z₀.re ≤ 0 := by
    rw [hre]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hApos.le
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hz0 : z₀ = 0 := Complex.ext (by simpa using heq) (by simpa using him)
    have := airyAi_pos (le_refl (0 : ℝ))
    rw [hz0] at h0
    have h00 : airyAiC ((0 : ℝ) : ℂ) = (airyAi 0 : ℂ) := airyAiC_ofReal 0
    simp only [Complex.ofReal_zero] at h00
    rw [h0] at h00
    exact this.ne' (by exact_mod_cast h00.symm)

/-- info: 'FormalResearch.Special.airyAiC_zero_real_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_zero_real_neg

end FormalResearch.Special
