module

public import FormalResearch.ModularBootstrap.Mixtures.SourceAxioms

/-!
# `pmix:weight` (b), (c): the axioms `(W1)-(W4)` for the common source class

`positive_mixtures.tex`, Lemma PM.2 (b), (c).  For a `CommonSource` (atomic signed measure `λ`, floor
`V ≥ d_λ V_{w,Q_0}` for all large charge):

* `testClass_iff_trivial`: for `c' ≥ c₀` the test class `\overline{\mathcal A}_{w,src}` equals the class built with the
  weight `V = K_a^{(w)}` (the test class of `Q ≡ 1`), as sets; the norms compare as
  `d_λ M_{Q_0}[g] ≤ M[g] ≤ C_up M_K[g]` (`cardyNorm_comparison`).
* `pmix_weight_c`: `SourceUniformAxioms src` with `p_0 = m + w - 1`, `p_K = p_e = m`, `p_u = 0`, `Q_* = A` (the
  paper's `Q_*(b) = A(b)` on `|b - ξ_*| ≤ r_1`), where `m` is the number of factors of `Q_0`.  The disc radius
  `r_1 ∈ (0, min(1/10, ξ_*/2)]` is chosen by continuity with `A(ξ_*) > 0` so that `A` has no zero on the disc.
* `pmix_weight_b`: the real and holomorphic Cardy asymptotes `pmix:Vasym` and the two-sided bound
  `d_λ P(e^{-4π x}) ≤ A(x) ≤ C_up` on `x > 0` (`P` = the null polynomial of `Q_0`).

Proof route: everything is *derived from the already proved fixed-weight theorems for `Q_0`* by the comparison
`d_λ V_{Q_0} ≤ V ≤ ‖λ‖_TV K_a` (norms, the sup bound, the strip continuation `hankelContinuationW`, floors, kernel and
band comparisons) plus the shifted-kernel asymptotes of `ShiftAsymptotics`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.Bessel
  FormalResearch.ModularBootstrap.ComplexBessel FormalResearch.ModularBootstrap.FixedWeight

/-! ### Test class and norm comparisons -/

namespace FloorData.At

variable {src : ShiftSource} {F : FloorData src} {a : ℝ}

/-- A source test function is a test function for the comparison product `Q_0`. -/
lemma testClass_prob (h : F.At a) {g : ℝ → ℝ} (hg : TestClass src a g) : Crossing.TestClass F.prob a g := by
  refine ⟨hg.cont, hg.int_lift, hg.fourier_odd, ?_⟩
  have hc : ContinuousOn (fun t => |g t| * F.prob.cardyV a t) (Ioi 0) :=
    ((hg.cont.abs.mono Ioi_subset_Ici_self).mul
      (continuous_cardyV F.prob a).continuousOn)
  refine (hg.int_cardy.const_mul (F.d)⁻¹).mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := ht
  have hP : 0 ≤ F.prob.cardyV a t := F.prob.cardyV_nonneg h.prob_shift ht0.le
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hP)]
  have hl := h.lower ht0
  have hd := F.hd
  have : F.prob.cardyV a t ≤ (F.d)⁻¹ * src.cardyV a t := by
    rw [← div_eq_inv_mul, le_div_iff₀ hd]; linarith
  calc |g t| * F.prob.cardyV a t ≤ |g t| * ((F.d)⁻¹ * src.cardyV a t) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = (F.d)⁻¹ * (|g t| * src.cardyV a t) := by ring

/-- `d_λ M_{Q_0}[g] ≤ M[g]` for a source test function. -/
lemma cardyNorm_ge (h : F.At a) {g : ℝ → ℝ} (hg : TestClass src a g) :
    F.d * F.prob.cardyNorm a g ≤ src.cardyNorm a g := by
  have hgP := h.testClass_prob hg
  unfold FixedWeightProblem.cardyNorm ShiftSource.cardyNorm
  rw [← integral_const_mul]
  refine setIntegral_mono_on (hgP.int_cardy.const_mul _) hg.int_cardy measurableSet_Ioi fun t ht => ?_
  have hl := h.lower ht
  calc F.d * (|g t| * F.prob.cardyV a t) = |g t| * (F.d * F.prob.cardyV a t) := by ring
    _ ≤ |g t| * src.cardyV a t := mul_le_mul_of_nonneg_left hl (abs_nonneg _)

/-- `M[g] ≤ C_up M_K[g]` whenever `|g| K_a` is integrable (`C_up = ‖λ‖_TV`). -/
lemma cardyNorm_le (h : F.At a) {g : ℝ → ℝ} (hg : TestClass src a g)
    (hK : IntegrableOn (fun t => |g t| * kernelK src.w a t) (Ioi 0)) :
    src.cardyNorm a g ≤ src.tv * ∫ t in Ioi 0, |g t| * kernelK src.w a t := by
  unfold ShiftSource.cardyNorm
  rw [← integral_const_mul]
  refine setIntegral_mono_on hg.int_cardy (hK.const_mul _) measurableSet_Ioi fun t ht => ?_
  calc |g t| * src.cardyV a t ≤ |g t| * (src.tv * kernelK src.w a t) :=
        mul_le_mul_of_nonneg_left (h.upper (le_of_lt ht)) (abs_nonneg _)
    _ = src.tv * (|g t| * kernelK src.w a t) := by ring

/-- A comparison-product test function is a source test function as soon as `|g| K_a` is integrable. -/
lemma testClass_of_prob (h : F.At a) {g : ℝ → ℝ} (hg : Crossing.TestClass F.prob a g)
    (hK : IntegrableOn (fun t => |g t| * kernelK src.w a t) (Ioi 0)) : TestClass src a g := by
  refine ⟨hg.cont, hg.int_lift, hg.fourier_odd, ?_⟩
  have hc : ContinuousOn (fun t => |g t| * src.cardyV a t) (Ioi 0) :=
    ((hg.cont.abs.mono Ioi_subset_Ici_self).mul (src.continuous_cardyV a).continuousOn)
  refine (hK.const_mul src.tv).mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := ht
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (h.pos_V ht0).le)]
  calc |g t| * src.cardyV a t ≤ |g t| * (src.tv * kernelK src.w a t) :=
        mul_le_mul_of_nonneg_left (h.upper ht0.le) (abs_nonneg _)
    _ = src.tv * (|g t| * kernelK src.w a t) := by ring

end FloorData.At

/-- A comparison-product test function at large charge has `|g| K_a` integrable (`testClass_integral_kernelK_le`),
so it is a source test function. -/
theorem FloorData.exists_testClass_iff {src : ShiftSource} (F : FloorData src) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {c' : ℝ}, c₀ ≤ c' → F.At (c' / 12) → ∀ {g : ℝ → ℝ},
      (TestClass src (c' / 12) g ↔ Crossing.TestClass F.prob (c' / 12) g) ∧
      (TestClass src (c' / 12) g ↔ Crossing.TestClass (trivialProductProblem src.w src.hw) (c' / 12) g) := by
  obtain ⟨C_Kint, c₀, hCK, hc₀, hK⟩ := testClass_integral_kernelK_le F.prob
  refine ⟨c₀, lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_left _ _)) hc₀, fun {c'} hc' h {g} => ?_⟩
  have hK' : ∀ {g : ℝ → ℝ}, Crossing.TestClass F.prob (c' / 12) g →
      IntegrableOn (fun t => |g t| * kernelK src.w (c' / 12) t) (Ioi 0) :=
    fun {g} hg => (hK hc' hg).1
  have e1 : TestClass src (c' / 12) g ↔ Crossing.TestClass F.prob (c' / 12) g :=
    ⟨h.testClass_prob, fun hg => h.testClass_of_prob hg (hK' hg)⟩
  refine ⟨e1, e1.trans ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · refine ⟨hg.cont, hg.int_lift, hg.fourier_odd, ?_⟩
    have := hK' hg
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [trivial_cardyV]
  · have hgP : Crossing.TestClass F.prob (c' / 12) g := by
      have hsrc : TestClass src (c' / 12) g := by
        refine ⟨hg.cont, hg.int_lift, hg.fourier_odd, ?_⟩
        have hKint : IntegrableOn (fun t => |g t| * kernelK src.w (c' / 12) t) (Ioi 0) :=
          hg.int_cardy.congr_fun (fun t _ => by simp only [trivial_cardyV]) measurableSet_Ioi
        have hc : ContinuousOn (fun t => |g t| * src.cardyV (c' / 12) t) (Ioi 0) :=
          ((hg.cont.abs.mono Ioi_subset_Ici_self).mul (src.continuous_cardyV _).continuousOn)
        refine (hKint.const_mul src.tv).mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
        have ht0 : 0 < t := ht
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (h.pos_V ht0).le)]
        calc |g t| * src.cardyV (c' / 12) t ≤ |g t| * (src.tv * kernelK src.w (c' / 12) t) :=
              mul_le_mul_of_nonneg_left (h.upper ht0.le) (abs_nonneg _)
          _ = src.tv * (|g t| * kernelK src.w (c' / 12) t) := by ring
      exact h.testClass_prob hsrc
    exact hgP

/-! ### A limit lemma -/

private lemma le_of_forall_large_div {u v K c₀ : ℝ}
    (h : ∀ c' : ℝ, c₀ ≤ c' → 0 < c' → u ≤ v + K / c') : u ≤ v := by
  by_contra hcon
  push Not at hcon
  have hε : 0 < u - v := sub_pos.mpr hcon
  set c' : ℝ := max (max c₀ 1) (K / (u - v) + 1) with hc'
  have hc1 : 1 ≤ c' := (le_max_right c₀ 1).trans (le_max_left _ _)
  have hcpos : 0 < c' := lt_of_lt_of_le one_pos hc1
  have hc0 : c₀ ≤ c' := (le_max_left c₀ 1).trans (le_max_left _ _)
  have hbig : K / (u - v) + 1 ≤ c' := le_max_right _ _
  have h1 := h c' hc0 hcpos
  have h2 : K / c' < u - v := by
    rw [div_lt_iff₀ hcpos]
    have : K / (u - v) < c' := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  linarith

/-! ### `pmix:weight` (b), (c) -/


private lemma mul_le_div_mul_of_le {A d x y : ℝ} (hd : 0 < d) (hA : 0 ≤ A) (h : d * x ≤ y) :
    A * x ≤ (A / d) * y := by
  calc A * x = (A / d) * (d * x) := by field_simp
    _ ≤ (A / d) * y := mul_le_mul_of_nonneg_left h (div_nonneg hA hd.le)

/-- **`pmix:weight` (b), lower bound for the amplitude**: `A(x) ≥ d_λ P(e^{-4π x})` for every `x > 0`, where
`P` is the null polynomial of the comparison product `Q_0` (passing to the limit in the floor comparison). -/
theorem ampl_lower {src : ShiftSource} (F : FloorData src) {a₀ : ℝ}
    (at_ : ∀ {a : ℝ}, a₀ ≤ a → F.At a) {x : ℝ} (hx : 0 < x) :
    F.d * F.prob.nullPoly (Real.exp (-4 * π * x)) ≤ src.ampl x := by
  have hA0 := at_ (le_refl a₀)
  have ha₀ : 0 < a₀ := hA0.pos
  obtain ⟨C_r, hCr, hr⟩ := cardyV_asymptotic_real F.prob hx
  obtain ⟨C_s, hCs, hs⟩ := src.real_asymp (S := a₀) hA0.shift hx
  refine le_of_forall_large_div (K := F.d * C_r + C_s) (c₀ := max 1 (24 * a₀)) fun c' hc' hcpos => ?_
  have hcA : a₀ ≤ c' / 12 := by
    have := (le_max_right 1 (24 * a₀)).trans hc'
    linarith
  have hAt := at_ hcA
  have hP : max 1 (24 * F.prob.totalShift) ≤ c' := by
    refine max_le ((le_max_left _ _).trans hc') ?_
    have := (le_max_right 1 (24 * a₀)).trans hc'
    nlinarith [hA0.prob_shift]
  have ht : 0 < c' * x ^ 2 / 3 := by positivity
  have hpref : 0 < (2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3)) :=
    mul_pos (by positivity) (besselAs_pos (by positivity))
  have e1 := abs_le.mp (hr (c' := c') (x := x) hP le_rfl)
  have e2 := abs_le.mp (hs (c' := c') (x := x) hc' le_rfl)
  have hlow : F.d * (F.prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3)))) ≤
      src.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hAt.lower ht) hpref.le
  have hF : F.prob.w = src.w := rfl
  have e1' : F.prob.nullPoly (Real.exp (-4 * Real.pi * x)) ≤
      F.prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) + C_r / c' := by
    have := e1.1
    simp only [hF] at this
    linarith
  have hdC : F.d * (C_r / c') = F.d * C_r / c' := by ring
  have hsum : (F.d * C_r + C_s) / c' = F.d * C_r / c' + C_s / c' := by ring
  nlinarith only [mul_le_mul_of_nonneg_left e1' F.hd.le, hlow, e2.2, hdC, hsum]

/-- **`pmix:weight` (c)** (Lemma PM.2 (c)), proved from the data of a common source: the structural axioms
`(W1)-(W4)` hold for every `c' ≥ c₀` with constants independent of `c'`, with `p_0 = m + w - 1`,
`p_K = p_e = m`, `p_u = 0`, `Q_* = A`; here `m` is the number of factors of the comparison product `Q_0`. -/
theorem pmix_weight_c_aux (src : ShiftSource) (F : FloorData src) (a₀ : ℝ)
    (at_ : ∀ {a : ℝ}, a₀ ≤ a → F.At a) :
    ∃ U : SourceUniformAxioms src,
      U.p_e = (F.m : ℝ) ∧ U.p_0 = ((F.m + src.w - 1 : ℕ) : ℝ) ∧ U.p_K = (F.m : ℝ) ∧
        U.p_u = 0 ∧ U.Q_star = src.amplC := by
  have hd := F.hd
  have hξ := xiStar_pos
  have hw := src.hw
  have hA0 := at_ (le_refl a₀)
  have ha₀pos : 0 < a₀ := hA0.pos
  -- constants from the comparison product `Q_0`
  obtain ⟨C_int, C_1, hCint_pos, hC1_pos, hwin⟩ := testClass_window_bounds F.prob
  obtain ⟨C_e, c₁, hCe_pos, hc1_ge, hstrip⟩ := hankelContinuationW_strip_bound F.prob
  obtain ⟨c₂, hc2_ge, hcont⟩ := continuousOn_hankelContinuationW F.prob
  obtain ⟨c₃, hc3_ge, hdiff⟩ := differentiableOn_hankelContinuationW F.prob
  obtain ⟨c_low, hc_low_pos, hfloor⟩ := cardyV_small_t_floor F.prob
  obtain ⟨C_K, c₄, hCK_pos, hc4_ge, hker⟩ := kernelK_le_mul_cardyV_gen F.prob
  obtain ⟨c_band, c₅, hc_band_pos, hc5_ge, hband⟩ := cardyV_ge_band_mul_kernelK F.prob
  -- the source asymptotes
  obtain ⟨C_s, hCs_nn, hreal⟩ := src.real_asymp (S := a₀) hA0.shift (x₀ := xiStar / 2) (half_pos hξ)
  obtain ⟨C_c, c₇, hCc_nn, hc7_ge, hcmplx⟩ := src.complex_asymp a₀ (m₀ := xiStar / 2)
    (M₀ := (3 / 2 : ℝ) * xiStar) (half_pos hξ) (mul_nonneg (by positivity) hξ.le)
  have hc1 : (1 : ℝ) ≤ c₁ := (le_max_left _ _).trans hc1_ge
  have hc7_24 : 24 * a₀ ≤ c₇ := (le_max_right _ _).trans hc7_ge
  let c₀ : ℝ := max c₁ (max c₂ (max c₃ (max c₄ (max c₅ c₇))))
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le one_pos (hc1.trans (le_max_left _ _))
  -- the amplitude: bounds and the zero-free disc
  obtain ⟨hnp0, hnp⟩ := nullPoly_exp_bounds F.prob (half_pos hξ)
  have hlow := fun {x : ℝ} (hx : 0 < x) => ampl_lower F at_ hx
  have hA_ξ : 0 < src.ampl xiStar := by
    have h1 := hlow hξ
    have h2 := (nullPoly_exp_bounds F.prob hξ).1
    exact lt_of_lt_of_le (mul_pos hd h2) h1
  have hcontA : Continuous src.amplC := src.amplC_entire.continuous
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcontA.continuousAt (src.ampl xiStar) hA_ξ
  let r₁ : ℝ := min (1 / 10) (min (xiStar / 2) (δ / 2))
  have hr1_pos : 0 < r₁ := lt_min (by norm_num) (lt_min (half_pos hξ) (half_pos hδ))
  have hr1_le : r₁ ≤ xiStar / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr1_tenth : r₁ ≤ 1 / 10 := min_le_left _ _
  have hr1_delta : r₁ < δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (half_lt_self hδ)
  have hnz : ∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r₁ → src.amplC b ≠ 0 := by
    intro b hb h0
    have hdist : dist b (xiStar : ℂ) < δ := lt_of_le_of_lt (mem_closedBall.mp hb) hr1_delta
    have := hδ' hdist
    rw [h0, src.amplC_ofReal, Complex.dist_eq, zero_sub, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hA_ξ.le] at this
    exact lt_irrefl _ this
  have hbox : ∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r₁ →
      b ∈ Box (xiStar / 2) ((3 / 2 : ℝ) * xiStar) := by
    intro b hb
    have hdist : ‖b - (xiStar : ℂ)‖ ≤ 1 / 10 := by
      simpa [Complex.dist_eq] using (mem_closedBall.mp hb).trans hr1_tenth
    have hre_sub : |b.re - xiStar| ≤ ‖b - (xiStar : ℂ)‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (b - (xiStar : ℂ))
    have him_sub : |b.im| ≤ ‖b - (xiStar : ℂ)‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (b - (xiStar : ℂ))
    refine ⟨?_, ?_, ?_⟩
    · have := (abs_le.mp (hre_sub.trans hdist)).1
      linarith [one_fifth_le_xiStar]
    · have := him_sub.trans hdist
      have h2 := (abs_le.mp (hre_sub.trans hdist)).1
      linarith [one_fifth_le_xiStar]
    · have hxi : ‖(xiStar : ℂ)‖ = xiStar := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
      calc ‖b‖ = ‖(b - (xiStar : ℂ)) + (xiStar : ℂ)‖ := by ring_nf
        _ ≤ ‖b - (xiStar : ℂ)‖ + ‖(xiStar : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 / 10 + xiStar := add_le_add hdist hxi.le
        _ ≤ (3 / 2 : ℝ) * xiStar := by linarith [one_fifth_le_xiStar]
  let c_Q : ℝ := F.d * F.prob.nullPoly (Real.exp (-4 * Real.pi * (xiStar / 2)))
  have hcQ_pos : 0 < c_Q := mul_pos hd hnp0
  have hQreal : ∀ {x : ℝ}, xiStar / 2 ≤ x → c_Q ≤ src.ampl x ∧ src.ampl x ≤ src.tv := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (half_pos hξ) hx
    refine ⟨?_, (le_abs_self _).trans (src.abs_ampl_le hx0.le)⟩
    exact (mul_le_mul_of_nonneg_left (hnp hx).1 hd.le).trans (hlow hx0)
  have hcQ_le : c_Q ≤ src.tv := (hQreal le_rfl).1.trans (hQreal le_rfl).2
  let C_V : ℝ := max C_s C_c
  have hCV_nn : 0 ≤ C_V := hCs_nn.trans (le_max_left _ _)
  -- the axioms at each large `c'`
  have hat : ∀ {c' : ℝ}, c₀ ≤ c' → F.At (c' / 12) := fun {c'} hc' => at_ (by
    have : c₇ ≤ c' := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))))
    linarith)
  -- the axioms at a given `c' ≥ c₀`
  have hhc : ∀ {j : ℝ}, (j = c₁ ∨ j = c₂ ∨ j = c₃ ∨ j = c₄ ∨ j = c₅ ∨ j = c₇) → j ≤ c₀ := by
    rintro j (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))
  have hcc : ∀ {c' : ℝ}, c₀ ≤ c' → c₁ ≤ c' ∧ c₂ ≤ c' ∧ c₃ ≤ c' ∧ c₄ ≤ c' ∧ c₅ ≤ c' ∧ c₇ ≤ c' :=
    fun {c'} hc' => ⟨(hhc (Or.inl rfl)).trans hc', (hhc (Or.inr (Or.inl rfl))).trans hc',
      (hhc (Or.inr (Or.inr (Or.inl rfl)))).trans hc',
      (hhc (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans hc',
      (hhc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans hc',
      (hhc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).trans hc'⟩
  let key : ∀ {c' : ℝ}, c₀ ≤ c' → SourceAxioms src c' := fun {c'} hc' => by
    have hc'_pos : 0 < c' := lt_of_lt_of_le hc₀_pos hc'
    obtain ⟨hcc1, hcc2, hcc3, hcc4, hcc5, hcc7⟩ := hcc hc'
    have hAt := hat hc'
    have hmax : max 1 (24 * a₀) ≤ c' := max_le (hc1.trans hcc1) (hc7_24.trans hcc7)
    exact
      { hc'_pos := hc'_pos
        ha_shift := hAt.shift
        C_1 := C_1 / F.d
        hC1_pos := div_pos hC1_pos hd
        C_e := C_e / F.d
        hCe_pos := div_pos hCe_pos hd
        p_e := (F.m : ℝ)
        hp_e_nn := Nat.cast_nonneg _
        c_low := F.d * c_low
        hc_low_pos := mul_pos hd hc_low_pos
        p_0 := ((F.m + src.w - 1 : ℕ) : ℝ)
        hp_0_nn := Nat.cast_nonneg _
        C_K := C_K / F.d
        hCK_pos := div_pos hCK_pos hd
        p_K := (F.m : ℝ)
        hp_K_nn := Nat.cast_nonneg _
        c_band := F.d * c_band
        hc_band_pos := mul_pos hd hc_band_pos
        C_up := src.tv
        hCup_pos := hAt.tv_pos
        p_u := 0
        hp_u_nn := le_rfl
        r_1 := r₁
        hr1_pos := hr1_pos
        hr1_le := hr1_le
        Q_star := src.amplC
        c_Q := c_Q
        C_Q := src.tv
        hcQ_pos := hcQ_pos
        hcQ_le := hcQ_le
        C_V := C_V
        hCV_nn := hCV_nn
        w1_sup := fun {g} hg {t} ht => by
          have hgP := hAt.testClass_prob hg
          have h1 := (hwin hAt.prob_shift hgP).2 ht
          exact h1.trans (mul_le_div_mul_of_le hd hC1_pos.le (hAt.cardyNorm_ge hg))
        w1_strip := fun {g} hg => by
          have hgP := hAt.testClass_prob hg
          refine ⟨hankelContinuationW src.w c' g, hcont hcc2 hgP, hdiff hcc3 hgP,
            fun x => hankelContinuationW_ofReal src.hw hc'_pos hg.cont hg.int_lift hg.fourier_odd x,
            fun {b} hb => ?_⟩
          have h1 := (hstrip hcc1 hgP hb).1
          have h2 := mul_le_div_mul_of_le hd (mul_nonneg hCe_pos.le (Real.rpow_nonneg hc'_pos.le (F.m : ℝ)))
            (hAt.cardyNorm_ge hg)
          calc ‖hankelContinuationW src.w c' g b‖ ≤ C_e * c' ^ (F.m : ℝ) * F.prob.cardyNorm (c' / 12) g := h1
            _ ≤ C_e * c' ^ (F.m : ℝ) / F.d * src.cardyNorm (c' / 12) g := h2
            _ = C_e / F.d * c' ^ (F.m : ℝ) * src.cardyNorm (c' / 12) g := by ring
        w2_pos := fun {t} ht => hAt.pos_V ht
        w2_floor := fun {t} ht _ => by
          have h1 := hfloor hAt.prob_shift ht
          have h2 := hAt.lower ht
          have : F.d * (c_low * t ^ ((F.m + src.w - 1 : ℕ) : ℝ)) ≤ F.d * F.prob.cardyV (c' / 12) t :=
            mul_le_mul_of_nonneg_left h1 hd.le
          linarith
        w2_ker_le := fun {t} ht => by
          have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
          have h1 := hker hcc4 ht
          have h2 := mul_le_div_mul_of_le hd (mul_nonneg hCK_pos.le (Real.rpow_nonneg hc'_pos.le (F.m : ℝ)))
            (hAt.lower ht0)
          calc kernelK src.w (c' / 12) t ≤ C_K * c' ^ (F.m : ℝ) * F.prob.cardyV (c' / 12) t := h1
            _ ≤ C_K * c' ^ (F.m : ℝ) / F.d * src.cardyV (c' / 12) t := h2
            _ = C_K / F.d * c' ^ (F.m : ℝ) * src.cardyV (c' / 12) t := by ring
        w2_band := fun {t} ht => by
          have ht0 : 0 < t := lt_of_lt_of_le (mul_pos (by unfold xiBar; positivity) hc'_pos) ht
          have h1 := hband hcc5 ht
          have h2 := hAt.lower ht0
          have : F.d * (c_band * kernelK src.w (c' / 12) t) ≤ F.d * F.prob.cardyV (c' / 12) t :=
            mul_le_mul_of_nonneg_left h1 hd.le
          linarith
        w2_up := fun {t} ht _ => by
          have h1 := hAt.upper ht.le
          have hK : 0 ≤ kernelK src.w (c' / 12) t := kernelK_nonneg hAt.pos.le ht.le
          have htv := hAt.tv_pos
          calc src.cardyV (c' / 12) t ≤ src.tv * kernelK src.w (c' / 12) t := h1
            _ ≤ src.tv * (1 + c' ^ (0 : ℝ)) * kernelK src.w (c' / 12) t := by
              rw [Real.rpow_zero]; nlinarith only [mul_nonneg htv.le hK]
        w3_Q_holo := src.amplC_entire.differentiableOn
        w3_Q_ne_zero := fun {b} hb => hnz hb
        w3_Q_real_bounds := fun {x} hx => by
          rw [src.amplC_ofReal]
          exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact (hQreal hx).1,
            by rw [Complex.ofReal_re]; exact (hQreal hx).2⟩
        w3_real_asymp := fun {x} hx => by
          rw [src.amplC_ofReal, Complex.ofReal_re]
          exact (hreal hmax hx).trans (div_le_div_of_nonneg_right (le_max_left _ _) hc'_pos.le)
        w3_complex_holo :=
          ⟨(src.cardyVC_entire (c' / 12)).comp (by fun_prop), fun x => src.cardyVC_ofReal (c' / 12) x⟩
        w3_complex_asymp := fun {b} hb =>
          (hcmplx hcc7 (hbox hb)).trans (div_le_div_of_nonneg_right (le_max_right _ _) hc'_pos.le)
        w4_vac := fun {T g} hfeas => by
          have hvac : 0 ≤ -2 * Real.pi * ∫ t in Ioi (0 : ℝ), g t * src.cardyV (c' / 12) t :=
            hfeas.2.2.1
          nlinarith [Real.pi_pos] }
  refine ⟨
    { c₀ := c₀
      hc₀_pos := hc₀_pos
      C_1 := C_1 / F.d
      hC1_pos := div_pos hC1_pos hd
      C_e := C_e / F.d
      hCe_pos := div_pos hCe_pos hd
      p_e := (F.m : ℝ)
      hp_e_nn := Nat.cast_nonneg _
      c_low := F.d * c_low
      hc_low_pos := mul_pos hd hc_low_pos
      p_0 := ((F.m + src.w - 1 : ℕ) : ℝ)
      hp_0_nn := Nat.cast_nonneg _
      C_K := C_K / F.d
      hCK_pos := div_pos hCK_pos hd
      p_K := (F.m : ℝ)
      hp_K_nn := Nat.cast_nonneg _
      c_band := F.d * c_band
      hc_band_pos := mul_pos hd hc_band_pos
      C_up := src.tv
      hCup_pos := (hat (le_refl c₀)).tv_pos
      p_u := 0
      hp_u_nn := le_rfl
      r_1 := r₁
      hr1_pos := hr1_pos
      hr1_le := hr1_le
      Q_star := src.amplC
      c_Q := c_Q
      C_Q := src.tv
      hcQ_pos := hcQ_pos
      hcQ_le := hcQ_le
      C_V := C_V
      hCV_nn := hCV_nn
      axioms_at := key
      uniform_C_1 := fun _ => rfl
      uniform_C_e := fun _ => rfl
      uniform_p_e := fun _ => rfl
      uniform_c_low := fun _ => rfl
      uniform_p_0 := fun _ => rfl
      uniform_C_K := fun _ => rfl
      uniform_p_K := fun _ => rfl
      uniform_c_band := fun _ => rfl
      uniform_C_up := fun _ => rfl
      uniform_p_u := fun _ => rfl
      uniform_r_1 := fun _ => rfl
      uniform_Q_star := fun _ => rfl
      uniform_c_Q := fun _ => rfl
      uniform_C_Q := fun _ => rfl
      uniform_C_V := fun _ => rfl }, rfl, rfl, rfl, rfl, rfl⟩

/-- **`pmix:weight` (c)** for a `CommonSource`. -/
theorem pmix_weight_c (C : CommonSource) :
    ∃ U : SourceUniformAxioms C.src,
      U.p_e = (C.F.m : ℝ) ∧ U.p_0 = ((C.F.m + C.src.w - 1 : ℕ) : ℝ) ∧ U.p_K = (C.F.m : ℝ) ∧
        U.p_u = 0 ∧ U.Q_star = C.src.amplC :=
  pmix_weight_c_aux C.src C.F C.a₀ C.at_

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_weight_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_weight_c

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.ampl_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampl_lower

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.FloorData.exists_testClass_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FloorData.exists_testClass_iff


/-- **`pmix:weight` (b)** (Lemma PM.2 (b)) for a common source: the real Cardy asymptote `pmix:Vasym`
uniformly on `x ≥ x₀` for `n ≥ n₀` with error `C_{x₀}/n`; the amplitude bounds
`d_λ Q_0(e^{-4π x₀}) ≤ A(x) ≤ C_up` on `x ≥ x₀`; `A` entire with `A(ξ_*) > 0`, a zero-free disc
`|b - ξ_*| ≤ r₁` (`r₁ ≤ min(0.1, ξ_*/2)`, `|A| ≥ A(ξ_*)/2` there), and the holomorphic asymptote on it with error
`C/n`. -/
theorem pmix_weight_b (C : CommonSource) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    (∃ Cx n₀ : ℝ, 0 ≤ Cx ∧ ∀ {n x : ℝ}, n₀ ≤ n → x₀ ≤ x →
      |C.src.cardyV (n / 12) (n * x ^ 2 / 3) /
          ((2 * x) ^ (C.src.w - 1) * besselAs (n * (2 * Real.pi * x / 3))) - C.src.ampl x| ≤ Cx / n) ∧
    (∀ {x : ℝ}, x₀ ≤ x →
      C.F.d * C.F.prob.nullPoly (Real.exp (-4 * Real.pi * x₀)) ≤ C.src.ampl x ∧
        C.src.ampl x ≤ C.src.tv) ∧
    Differentiable ℂ C.src.amplC ∧ 0 < C.src.ampl xiStar ∧
    (∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ min (1 / 10) (xiStar / 2) ∧
      (∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r₁ → C.src.ampl xiStar / 2 ≤ ‖C.src.amplC b‖) ∧
      ∃ Cc n₁ : ℝ, 0 ≤ Cc ∧ ∀ {n : ℝ}, n₁ ≤ n → ∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r₁ →
        ‖C.src.cardyVC (n / 12) ((n : ℂ) * b ^ 2 / 3) /
            ((2 * b) ^ (C.src.w - 1) * asC ((n : ℂ) * tipL b)) - C.src.amplC b‖ ≤ Cc / n) := by
  have hξ := xiStar_pos
  have hA0 := C.at_ (le_refl C.a₀)
  obtain ⟨Cx, hCx, hreal⟩ := C.src.real_asymp (S := C.a₀) hA0.shift hx₀
  refine ⟨⟨Cx, max 1 (24 * C.a₀), hCx, fun {n x} hn hx => hreal hn hx⟩, ?_, C.src.amplC_entire, ?_, ?_⟩
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
    refine ⟨?_, (le_abs_self _).trans (C.src.abs_ampl_le hx0.le)⟩
    obtain ⟨_, hnp⟩ := nullPoly_exp_bounds C.F.prob hx₀
    exact (mul_le_mul_of_nonneg_left (hnp hx).1 C.F.hd.le).trans (ampl_lower C.F C.at_ hx0)
  · exact lt_of_lt_of_le (mul_pos C.F.hd (nullPoly_exp_bounds C.F.prob hξ).1)
      (ampl_lower C.F C.at_ hξ)
  · have hA_ξ : 0 < C.src.ampl xiStar := lt_of_lt_of_le
      (mul_pos C.F.hd (nullPoly_exp_bounds C.F.prob hξ).1) (ampl_lower C.F C.at_ hξ)
    have hcontA : Continuous C.src.amplC := C.src.amplC_entire.continuous
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcontA.continuousAt (C.src.ampl xiStar / 2)
      (half_pos hA_ξ)
    refine ⟨min (1 / 10) (min (xiStar / 2) (δ / 2)),
      lt_min (by norm_num) (lt_min (half_pos hξ) (half_pos hδ)),
      min_le_min_left _ ((min_le_left _ _)), ?_, ?_⟩
    · intro b hb
      have hdist : dist b (xiStar : ℂ) < δ := lt_of_le_of_lt (mem_closedBall.mp hb)
        (lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (half_lt_self hδ))
      have := hδ' hdist
      rw [C.src.amplC_ofReal, Complex.dist_eq] at this
      have h2 : ‖(C.src.ampl xiStar : ℂ)‖ ≤ ‖C.src.amplC b‖ + ‖C.src.amplC b - (C.src.ampl xiStar : ℂ)‖ := by
        calc ‖(C.src.ampl xiStar : ℂ)‖ = ‖C.src.amplC b - (C.src.amplC b - (C.src.ampl xiStar : ℂ))‖ := by
              ring_nf
          _ ≤ _ := norm_sub_le _ _
      rw [Complex.norm_real, Real.norm_of_nonneg hA_ξ.le] at h2
      linarith
    · obtain ⟨Cc, c₇, hCc, hc7, hcmplx⟩ := C.src.complex_asymp C.a₀ (m₀ := xiStar / 2)
        (M₀ := (3 / 2 : ℝ) * xiStar) (half_pos hξ) (mul_nonneg (by positivity) hξ.le)
      refine ⟨Cc, c₇, hCc, fun {n} hn {b} hb => hcmplx hn ?_⟩
      have hr1 : min (1 / 10) (min (xiStar / 2) (δ / 2)) ≤ 1 / 10 := min_le_left _ _
      have hdist : ‖b - (xiStar : ℂ)‖ ≤ 1 / 10 := by
        simpa [Complex.dist_eq] using (mem_closedBall.mp hb).trans hr1
      have hre_sub : |b.re - xiStar| ≤ ‖b - (xiStar : ℂ)‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (b - (xiStar : ℂ))
      have him_sub : |b.im| ≤ ‖b - (xiStar : ℂ)‖ := by
        simpa [Complex.sub_im] using Complex.abs_im_le_norm (b - (xiStar : ℂ))
      refine ⟨?_, ?_, ?_⟩
      · have := (abs_le.mp (hre_sub.trans hdist)).1
        linarith [one_fifth_le_xiStar]
      · have := him_sub.trans hdist
        have h2 := (abs_le.mp (hre_sub.trans hdist)).1
        linarith [one_fifth_le_xiStar]
      · have hxi : ‖(xiStar : ℂ)‖ = xiStar := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
        calc ‖b‖ = ‖(b - (xiStar : ℂ)) + (xiStar : ℂ)‖ := by ring_nf
          _ ≤ ‖b - (xiStar : ℂ)‖ + ‖(xiStar : ℂ)‖ := norm_add_le _ _
          _ ≤ 1 / 10 + xiStar := add_le_add hdist hxi.le
          _ ≤ (3 / 2 : ℝ) * xiStar := by linarith [one_fifth_le_xiStar]

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_weight_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_weight_b

end FormalResearch.ModularBootstrap.Mixtures
