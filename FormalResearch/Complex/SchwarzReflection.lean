module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Morera Across a Horizontal Line and Schwarz Reflection (Phase-Free)

Provides three reusable complex-analysis lemmas:
* (A) `differentiableOn_of_continuousOn_off_horizLine`: if `F : ℂ → ℂ` is continuous on an open
  set `U` and complex-differentiable on `U \ {z | z.im = a}`, then `F` is complex-differentiable
  on `U` (Morera's theorem via `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`
  and `Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`).
* (B) `schwarzReflection`: Schwarz reflection across `{z | z.im = a}` for `f` continuous on
  `U ∩ {z | a ≤ z.im}`, holomorphic on `U ∩ {z | a < z.im}`, and real on `U ∩ {z | z.im = a}`.
* (C) `schwarzReflection_prescribed_re`: reflection across `{z | z.im = a}` with a prescribed
  holomorphic function `u` on `U` that is real on `U ∩ {z | z.im = a}` and satisfies
  `(f z).re = (u z).re` on `U ∩ {z | z.im = a}`, extending `f` by
  `2 * u z - starRingEnd ℂ (f (reflHoriz a z))` on `{z | z.im < a}` (used in Paper II, Lemma C10).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric intervalIntegral
open scoped Interval

namespace FormalResearch.Complex

/-! ### (A) Morera across a horizontal line -/

private lemma rectBdry_eq_zero_of_not_mem_Ioo {F : ℂ → ℂ} {U : Set ℂ} {a : ℝ}
    (hF_cont : ContinuousOn F U)
    (hF_diff : DifferentiableOn ℂ F (U \ {z : ℂ | z.im = a}))
    {z w : ℂ} (hrect : Rectangle z w ⊆ U)
    (ha : a ∉ Ioo (min z.im w.im) (max z.im w.im)) :
    (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I)) = 0 := by
  refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F z w
    (hF_cont.mono hrect) (hF_diff.mono ?_)
  intro ζ hζ
  refine ⟨hrect ⟨Ioo_subset_Icc_self hζ.1, Ioo_subset_Icc_self hζ.2⟩, ?_⟩
  intro him
  exact ha (him ▸ hζ.2)

private lemma rectBdry_eq_zero_of_horizLine {F : ℂ → ℂ} {U : Set ℂ} {a : ℝ}
    (hF_cont : ContinuousOn F U)
    (hF_diff : DifferentiableOn ℂ F (U \ {z : ℂ | z.im = a}))
    {z w : ℂ} (hrect : Rectangle z w ⊆ U) :
    (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I)) = 0 := by
  by_cases ha : a ∈ Ioo (min z.im w.im) (max z.im w.im)
  · have ha_mem : a ∈ [[z.im, w.im]] := Ioo_subset_Icc_self ha
    let z₁ : ℂ := z.re + z.im * I
    let w₁ : ℂ := w.re + a * I
    let z₂ : ℂ := z.re + a * I
    let w₂ : ℂ := w.re + w.im * I
    have hrect₁ : Rectangle z₁ w₁ ⊆ Rectangle z w := by
      intro ζ hζ
      refine ⟨by simpa [z₁, w₁] using hζ.1, ?_⟩
      have hsub : [[z.im, a]] ⊆ [[z.im, w.im]] := uIcc_subset_uIcc_left ha_mem
      exact hsub (by simpa [z₁, w₁] using hζ.2)
    have hrect₂ : Rectangle z₂ w₂ ⊆ Rectangle z w := by
      intro ζ hζ
      refine ⟨by simpa [z₂, w₂] using hζ.1, ?_⟩
      have hsub : [[a, w.im]] ⊆ [[z.im, w.im]] := uIcc_subset_uIcc_right ha_mem
      exact hsub (by simpa [z₂, w₂] using hζ.2)
    have ha₁ : a ∉ Ioo (min z₁.im w₁.im) (max z₁.im w₁.im) := by
      simp only [z₁, w₁, add_im, ofReal_im, mul_im, I_re, I_im, mul_zero, mul_one, add_zero,
        zero_add, mem_Ioo, not_and, not_lt]
      intro hlt
      rcases le_total z.im a with hza | haz
      · simp [max_eq_right hza]
      · simp [min_eq_right haz] at hlt
    have ha₂ : a ∉ Ioo (min z₂.im w₂.im) (max z₂.im w₂.im) := by
      simp only [z₂, w₂, add_im, ofReal_im, mul_im, I_re, I_im, mul_zero, mul_one, add_zero,
        zero_add, mem_Ioo, not_and, not_lt]
      intro hlt
      rcases le_total a w.im with haw | hwa
      · simp [min_eq_left haw] at hlt
      · simp [max_eq_left hwa]
    have h₁ := rectBdry_eq_zero_of_not_mem_Ioo hF_cont hF_diff (hrect₁.trans hrect) ha₁
    have h₂ := rectBdry_eq_zero_of_not_mem_Ioo hF_cont hF_diff (hrect₂.trans hrect) ha₂
    have hcont_w : IntervalIntegrable (fun y : ℝ => F (w.re + y * I)) volume z.im a ∧
        IntervalIntegrable (fun y : ℝ => F (w.re + y * I)) volume a w.im := by
      have hw_mem : w.re ∈ [[z.re, w.re]] := right_mem_uIcc
      constructor
      · refine (hF_cont.comp (by fun_prop : Continuous fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I).continuousOn
          fun y hy => hrect ⟨by simp [hw_mem],
            by simpa using uIcc_subset_uIcc_left ha_mem hy⟩).intervalIntegrable
      · refine (hF_cont.comp (by fun_prop : Continuous fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I).continuousOn
          fun y hy => hrect ⟨by simp [hw_mem],
            by simpa using uIcc_subset_uIcc_right ha_mem hy⟩).intervalIntegrable
    have hcont_z : IntervalIntegrable (fun y : ℝ => F (z.re + y * I)) volume z.im a ∧
        IntervalIntegrable (fun y : ℝ => F (z.re + y * I)) volume a w.im := by
      have hz_mem : z.re ∈ [[z.re, w.re]] := left_mem_uIcc
      constructor
      · refine (hF_cont.comp (by fun_prop : Continuous fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I).continuousOn
          fun y hy => hrect ⟨by simp [hz_mem],
            by simpa using uIcc_subset_uIcc_left ha_mem hy⟩).intervalIntegrable
      · refine (hF_cont.comp (by fun_prop : Continuous fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I).continuousOn
          fun y hy => hrect ⟨by simp [hz_mem],
            by simpa using uIcc_subset_uIcc_right ha_mem hy⟩).intervalIntegrable
    have hw_add := intervalIntegral.integral_add_adjacent_intervals hcont_w.1 hcont_w.2
    have hz_add := intervalIntegral.integral_add_adjacent_intervals hcont_z.1 hcont_z.2
    simp only [z₁, w₁, z₂, w₂, add_re, ofReal_re, mul_re, I_re, I_im, mul_zero, sub_zero,
      add_zero, add_im, ofReal_im, mul_im, mul_one, zero_add] at h₁ h₂
    linear_combination h₁ + h₂ - I * hw_add + I * hz_add
  · exact rectBdry_eq_zero_of_not_mem_Ioo hF_cont hF_diff hrect ha

/-- **(A) Morera across a horizontal line.**
If `U ⊆ ℂ` is open, `a : ℝ`, `F : ℂ → ℂ` is continuous on `U`, and `F` is complex-differentiable
on `U \ {z | z.im = a}`, then `F` is complex-differentiable on `U`. -/
theorem differentiableOn_of_continuousOn_off_horizLine {U : Set ℂ} {a : ℝ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF_cont : ContinuousOn F U)
    (hF_diff : DifferentiableOn ℂ F (U \ {z : ℂ | z.im = a})) :
    DifferentiableOn ℂ F U := by
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp ⟨?_, hF_cont⟩
  intro z w hrect
  have h0 := rectBdry_eq_zero_of_horizLine hF_cont hF_diff hrect
  have h1 := wedgeIntegral_add_wedgeIntegral_eq z w F
  have h2 : wedgeIntegral z w F + wedgeIntegral w z F = 0 := by
    rw [h1]
    exact h0
  exact eq_neg_of_add_eq_zero_left h2

/-! ### (B) Schwarz reflection across `Im z = a` -/

/-- Reflection across the horizontal line `Im z = a`: `z ↦ conj (z - a * I) + a * I`. -/
def reflHoriz (a : ℝ) (z : ℂ) : ℂ := starRingEnd ℂ (z - (a : ℂ) * I) + (a : ℂ) * I

lemma reflHoriz_re (a : ℝ) (z : ℂ) : (reflHoriz a z).re = z.re := by
  unfold reflHoriz; simp

lemma reflHoriz_im (a : ℝ) (z : ℂ) : (reflHoriz a z).im = 2 * a - z.im := by
  unfold reflHoriz; simp; ring

lemma reflHoriz_involutive (a : ℝ) (z : ℂ) : reflHoriz a (reflHoriz a z) = z := by
  apply Complex.ext <;> simp [reflHoriz_re, reflHoriz_im]

lemma reflHoriz_continuous (a : ℝ) : Continuous (reflHoriz a) := by
  unfold reflHoriz
  exact (Complex.continuous_conj.comp (continuous_id.sub continuous_const)).add continuous_const

lemma reflHoriz_eq_self_of_im {a : ℝ} {z : ℂ} (hz : z.im = a) : reflHoriz a z = z := by
  apply Complex.ext
  · exact reflHoriz_re a z
  · rw [reflHoriz_im, hz]; ring

lemma reflHoriz_dist (a : ℝ) (z w : ℂ) : dist (reflHoriz a z) (reflHoriz a w) = dist z w := by
  rw [dist_eq_norm, dist_eq_norm]
  have hdiff : reflHoriz a z - reflHoriz a w = starRingEnd ℂ (z - w) := by
    apply Complex.ext
    · simp [reflHoriz_re]
    · simp [reflHoriz_im]; ring
  rw [hdiff, Complex.norm_conj]

/-- Schwarz reflection of `f` across `Im z = a`: `f z` on `{z | a ≤ z.im}` and
`conj (f (reflHoriz a z))` on `{z | z.im < a}`. -/
noncomputable def schwarzReflect (a : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if a ≤ z.im then f z else starRingEnd ℂ (f (reflHoriz a z))

private lemma hasDerivAt_schwarzReflect_lower {a : ℝ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hU_symm : ∀ z ∈ U, reflHoriz a z ∈ U)
    (hf_holo : DifferentiableOn ℂ f (U ∩ {z : ℂ | a < z.im}))
    {z : ℂ} (hzU : z ∈ U) (hz_lt : z.im < a) :
    DifferentiableAt ℂ (fun w => starRingEnd ℂ (f (reflHoriz a w))) z := by
  have hr_mem : reflHoriz a z ∈ U ∩ {w : ℂ | a < w.im} :=
    ⟨hU_symm z hzU, by change a < (reflHoriz a z).im; rw [reflHoriz_im]; linarith⟩
  have hopen : IsOpen (U ∩ {w : ℂ | a < w.im}) :=
    hU.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hdf : HasDerivAt f (deriv f (reflHoriz a z)) (reflHoriz a z) :=
    (hf_holo.differentiableAt (hopen.mem_nhds hr_mem)).hasDerivAt
  have hlim : HasDerivAt (fun w => starRingEnd ℂ (f (reflHoriz a w)))
      (starRingEnd ℂ (deriv f (reflHoriz a z))) z := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h_sl := hasDerivAt_iff_tendsto_slope_zero.mp hdf
    have h_conj : Tendsto (fun t : ℂ => starRingEnd ℂ (t⁻¹ • (f (reflHoriz a z + t) - f (reflHoriz a z))))
        (𝓝[≠] 0) (𝓝 (starRingEnd ℂ (deriv f (reflHoriz a z)))) :=
      Complex.continuous_conj.continuousAt.tendsto.comp h_sl
    have h_pre : Tendsto (starRingEnd ℂ : ℂ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(Complex.continuous_conj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).trans (by simp),
          eventually_nhdsWithin_of_forall fun t (ht : t ≠ 0) => by simpa using ht⟩
    refine (h_conj.comp h_pre).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    have hrefl_add : reflHoriz a (z + t) = reflHoriz a z + starRingEnd ℂ t := by
      apply Complex.ext
      · simp [reflHoriz_re]
      · simp [reflHoriz_im]; ring
    simp only [Function.comp_apply, smul_eq_mul, hrefl_add, map_mul, map_inv₀,
      map_sub, Complex.conj_conj]
  exact hlim.differentiableAt

/-- **(B) Schwarz reflection across `Im z = a`.**
Let `U ⊆ ℂ` be open and symmetric under `reflHoriz a` (`z ↦ conj (z - a * I) + a * I`).
If `f` is continuous on `U ∩ {z | a ≤ z.im}`, complex-differentiable on `U ∩ {z | a < z.im}`,
and real-valued on `U ∩ {z | z.im = a}`, then `schwarzReflect a f` is complex-differentiable on `U`. -/
theorem schwarzReflection {a : ℝ} {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hU_symm : ∀ z ∈ U, reflHoriz a z ∈ U)
    (hf_cont : ContinuousOn f (U ∩ {z : ℂ | a ≤ z.im}))
    (hf_holo : DifferentiableOn ℂ f (U ∩ {z : ℂ | a < z.im}))
    (hf_real : ∀ z ∈ U, z.im = a → (f z).im = 0) :
    DifferentiableOn ℂ (schwarzReflect a f) U := by
  refine differentiableOn_of_continuousOn_off_horizLine (a := a) hU ?_ ?_
  · have h_upper : ContinuousOn (schwarzReflect a f) (U ∩ {z : ℂ | a ≤ z.im}) :=
      hf_cont.congr fun z hz => by
        have hza : a ≤ z.im := hz.2
        simp [schwarzReflect, hza]
    have h_lower_eq : EqOn (schwarzReflect a f) (fun z => starRingEnd ℂ (f (reflHoriz a z)))
        (U ∩ {z : ℂ | z.im ≤ a}) := by
      intro z hz
      have hza : z.im ≤ a := hz.2
      rcases lt_or_eq_of_le hza with hlt | heq
      · simp [schwarzReflect, not_le.mpr hlt]
      · simp only [schwarzReflect, heq.ge, ↓reduceIte, reflHoriz_eq_self_of_im heq]
        exact (Complex.conj_eq_iff_im.mpr (hf_real z hz.1 heq)).symm
    have h_lower : ContinuousOn (schwarzReflect a f) (U ∩ {z : ℂ | z.im ≤ a}) := by
      refine ContinuousOn.congr ?_ h_lower_eq
      refine Complex.continuous_conj.comp_continuousOn ?_
      refine hf_cont.comp (reflHoriz_continuous a).continuousOn fun z hz => ?_
      have hza : z.im ≤ a := hz.2
      exact ⟨hU_symm z hz.1, show a ≤ (reflHoriz a z).im by rw [reflHoriz_im]; linarith⟩
    have h_union : U = (U ∩ {z : ℂ | a ≤ z.im}) ∪ (U ∩ {z : ℂ | z.im ≤ a}) := by
      ext z; simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro hz; rcases le_total a z.im with h | h <;> [exact Or.inl ⟨hz, h⟩; exact Or.inr ⟨hz, h⟩]
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    rw [h_union]
    intro z hz
    rcases hz with hz_up | hz_lo
    · have hza : a ≤ z.im := hz_up.2
      rcases lt_or_eq_of_le hza with hlt | heq
      · have hopen : IsOpen (U ∩ {w : ℂ | a < w.im}) :=
          hU.inter (isOpen_lt continuous_const Complex.continuous_im)
        have hnhds : U ∩ {w : ℂ | a < w.im} ∈ 𝓝 z := hopen.mem_nhds ⟨hz_up.1, hlt⟩
        have hc := (h_upper z hz_up).continuousAt
          (Filter.mem_of_superset hnhds fun w hw => ⟨hw.1, show a ≤ w.im from hw.2.le⟩)
        exact hc.continuousWithinAt
      · have hc1 := h_upper z hz_up
        have hc2 := h_lower z ⟨hz_up.1, heq.symm.le⟩
        exact hc1.union hc2
    · have hza : z.im ≤ a := hz_lo.2
      rcases lt_or_eq_of_le hza with hlt | heq
      · have hopen : IsOpen (U ∩ {w : ℂ | w.im < a}) :=
          hU.inter (isOpen_lt Complex.continuous_im continuous_const)
        have hnhds : U ∩ {w : ℂ | w.im < a} ∈ 𝓝 z := hopen.mem_nhds ⟨hz_lo.1, hlt⟩
        have hc := (h_lower z hz_lo).continuousAt
          (Filter.mem_of_superset hnhds fun w hw => ⟨hw.1, show w.im ≤ a from hw.2.le⟩)
        exact hc.continuousWithinAt
      · exact (h_upper z ⟨hz_lo.1, heq.ge⟩).union (h_lower z hz_lo)
  · intro z hz
    rcases lt_trichotomy z.im a with hlt | heq | hgt
    · have hd := hasDerivAt_schwarzReflect_lower hU hU_symm hf_holo hz.1 hlt
      have hopen : IsOpen (U ∩ {w : ℂ | w.im < a}) :=
        hU.inter (isOpen_lt Complex.continuous_im continuous_const)
      have hev : (fun w => starRingEnd ℂ (f (reflHoriz a w))) =ᶠ[𝓝 z] schwarzReflect a f := by
        filter_upwards [hopen.mem_nhds ⟨hz.1, hlt⟩] with w hw
        have hwim : w.im < a := hw.2
        simp [schwarzReflect, not_le.mpr hwim]
      exact (hd.congr_of_eventuallyEq hev.symm).differentiableWithinAt
    · exact absurd heq hz.2
    · have hopen : IsOpen (U ∩ {w : ℂ | a < w.im}) :=
        hU.inter (isOpen_lt continuous_const Complex.continuous_im)
      have hdf := hf_holo.differentiableAt (hopen.mem_nhds ⟨hz.1, hgt⟩)
      have hev : f =ᶠ[𝓝 z] schwarzReflect a f := by
        filter_upwards [hopen.mem_nhds ⟨hz.1, hgt⟩] with w hw
        have hwim : a < w.im := hw.2
        simp [schwarzReflect, hwim.le]
      exact (hdf.congr_of_eventuallyEq hev.symm).differentiableWithinAt

/-! ### (C) Reflection with a prescribed real part -/

/-- Schwarz reflection of `f` across `Im z = a` with prescribed holomorphic real-part reference `u`:
`f z` on `{z | a ≤ z.im}` and `2 * u z - conj (f (reflHoriz a z))` on `{z | z.im < a}`. -/
noncomputable def schwarzReflectPrescribedRe (a : ℝ) (f u : ℂ → ℂ) (z : ℂ) : ℂ :=
  if a ≤ z.im then f z else 2 * u z - starRingEnd ℂ (f (reflHoriz a z))

/-- **(C) Schwarz reflection with a prescribed real part (`Lemma C10`).**
Let `U ⊆ ℂ` be open and symmetric under `reflHoriz a`. Suppose `u` is holomorphic on `U`
and real-valued on `U ∩ {z | z.im = a}`, `f` is continuous on `U ∩ {z | a ≤ z.im}` and
holomorphic on `U ∩ {z | a < z.im}`, and `(f z).re = (u z).re` on `U ∩ {z | z.im = a}`.
Then `schwarzReflectPrescribedRe a f u` (equal to `f z` for `a ≤ z.im` and
`2 * u z - conj (f (reflHoriz a z))` for `z.im < a`) is complex-differentiable on `U`. -/
theorem schwarzReflection_prescribed_re {a : ℝ} {U : Set ℂ} {f u : ℂ → ℂ}
    (hU : IsOpen U) (hU_symm : ∀ z ∈ U, reflHoriz a z ∈ U)
    (hu_holo : DifferentiableOn ℂ u U)
    (hu_real : ∀ z ∈ U, z.im = a → (u z).im = 0)
    (hf_cont : ContinuousOn f (U ∩ {z : ℂ | a ≤ z.im}))
    (hf_holo : DifferentiableOn ℂ f (U ∩ {z : ℂ | a < z.im}))
    (hf_re : ∀ z ∈ U, z.im = a → (f z).re = (u z).re) :
    DifferentiableOn ℂ (schwarzReflectPrescribedRe a f u) U := by
  intro z₀ hz₀
  refine DifferentiableAt.differentiableWithinAt ?_
  rcases lt_trichotomy z₀.im a with hlt | heq | hgt
  · have hopen : IsOpen (U ∩ {z : ℂ | z.im < a}) :=
      hU.inter (isOpen_lt Complex.continuous_im continuous_const)
    have hdu : DifferentiableAt ℂ u z₀ := hu_holo.differentiableAt (hU.mem_nhds hz₀)
    have hdf : DifferentiableAt ℂ (fun z => starRingEnd ℂ (f (reflHoriz a z))) z₀ :=
      hasDerivAt_schwarzReflect_lower hU hU_symm hf_holo hz₀ hlt
    have hd : DifferentiableAt ℂ (fun z => 2 * u z - starRingEnd ℂ (f (reflHoriz a z))) z₀ :=
      ((differentiableAt_const _).mul hdu).sub hdf
    have hev : (fun z => 2 * u z - starRingEnd ℂ (f (reflHoriz a z))) =ᶠ[𝓝 z₀]
        schwarzReflectPrescribedRe a f u := by
      filter_upwards [hopen.mem_nhds ⟨hz₀, hlt⟩] with z hz
      have hzim : z.im < a := hz.2
      simp [schwarzReflectPrescribedRe, not_le.mpr hzim]
    exact hd.congr_of_eventuallyEq hev.symm
  · obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
    have hball_symm : ∀ z ∈ ball z₀ r, reflHoriz a z ∈ ball z₀ r := by
      intro z hz
      rw [mem_ball] at hz ⊢
      rwa [← reflHoriz_eq_self_of_im heq, reflHoriz_dist]
    have h_u_refl : DifferentiableOn ℂ (schwarzReflect a u) (ball z₀ r) :=
      schwarzReflection isOpen_ball hball_symm
        (hu_holo.continuousOn.mono (inter_subset_left.trans hball))
        (hu_holo.mono (inter_subset_left.trans hball))
        fun z hz hzim => hu_real z (hball hz) hzim
    have hu_an : AnalyticOnNhd ℂ u (ball z₀ r) :=
      (hu_holo.mono hball).analyticOnNhd isOpen_ball
    have h_u_refl_an : AnalyticOnNhd ℂ (schwarzReflect a u) (ball z₀ r) :=
      h_u_refl.analyticOnNhd isOpen_ball
    let z_up : ℂ := z₀ + ((r / 2 : ℝ) : ℂ) * I
    have hz_up_mem : z_up ∈ ball z₀ r := by
      rw [mem_ball, dist_eq_norm, show z_up - z₀ = ((r / 2 : ℝ) : ℂ) * I by ring,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_I, mul_one]
      linarith
    have hz_up_im : a < z_up.im := by
      dsimp [z_up]; simp [heq]; linarith
    have hopen_up : IsOpen (ball z₀ r ∩ {z : ℂ | a < z.im}) :=
      isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hev_up : schwarzReflect a u =ᶠ[𝓝 z_up] u := by
      filter_upwards [hopen_up.mem_nhds ⟨hz_up_mem, hz_up_im⟩] with z hz
      have hzim : a < z.im := hz.2
      simp [schwarzReflect, hzim.le]
    have heq_ball : EqOn (schwarzReflect a u) u (ball z₀ r) :=
      h_u_refl_an.eqOn_of_preconnected_of_eventuallyEq hu_an (convex_ball z₀ r).isPreconnected
        hz_up_mem hev_up
    have hf_u_refl : DifferentiableOn ℂ (schwarzReflect a (fun w => I * (f w - u w))) (ball z₀ r) := by
      refine schwarzReflection isOpen_ball hball_symm ?_ ?_ ?_
      · exact continuousOn_const.mul (hf_cont.mono (inter_subset_inter_left _ hball) |>.sub
          (hu_holo.continuousOn.mono (inter_subset_left.trans hball)))
      · exact (differentiableOn_const _).mul (hf_holo.mono (inter_subset_inter_left _ hball) |>.sub
          (hu_holo.mono (inter_subset_left.trans hball)))
      · intro z hz hzim
        simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
          Complex.sub_re]
        exact sub_eq_zero.mpr (hf_re z (hball hz) hzim)
    let G : ℂ → ℂ := fun w => u w - I * schwarzReflect a (fun w => I * (f w - u w)) w
    have hG_diff : DifferentiableAt ℂ G z₀ :=
      ((hu_holo.mono hball).sub ((differentiableOn_const _).mul hf_u_refl)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hr0))
    have hG_eq : EqOn G (schwarzReflectPrescribedRe a f u) (ball z₀ r) := by
      intro z hz
      by_cases hza : a ≤ z.im
      · simp only [G, schwarzReflect, schwarzReflectPrescribedRe, hza, ↓reduceIte]
        rw [← mul_assoc, Complex.I_mul_I]
        ring
      · have hza_lt : z.im < a := not_le.mp hza
        have hu_conj : starRingEnd ℂ (u (reflHoriz a z)) = u z := by
          have h1 := heq_ball hz
          simpa [schwarzReflect, hza] using h1
        simp only [G, schwarzReflect, schwarzReflectPrescribedRe, hza, ↓reduceIte, map_mul,
          Complex.conj_I, map_sub, hu_conj]
        calc u z - I * (-I * (starRingEnd ℂ (f (reflHoriz a z)) - u z))
            = u z + (I * I) * (starRingEnd ℂ (f (reflHoriz a z)) - u z) := by ring
          _ = u z + (-1) * (starRingEnd ℂ (f (reflHoriz a z)) - u z) := by rw [Complex.I_mul_I]
          _ = 2 * u z - starRingEnd ℂ (f (reflHoriz a z)) := by ring
    exact hG_diff.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr0)) hG_eq).symm
  · have hopen : IsOpen (U ∩ {z : ℂ | a < z.im}) :=
      hU.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hdf := hf_holo.differentiableAt (hopen.mem_nhds ⟨hz₀, hgt⟩)
    have hev : f =ᶠ[𝓝 z₀] schwarzReflectPrescribedRe a f u := by
      filter_upwards [hopen.mem_nhds ⟨hz₀, hgt⟩] with z hz
      have hzim : a < z.im := hz.2
      simp [schwarzReflectPrescribedRe, hzim.le]
    exact hdf.congr_of_eventuallyEq hev.symm

end FormalResearch.Complex

/-- info: 'FormalResearch.Complex.differentiableOn_of_continuousOn_off_horizLine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Complex.differentiableOn_of_continuousOn_off_horizLine

/-- info: 'FormalResearch.Complex.schwarzReflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Complex.schwarzReflection

/-- info: 'FormalResearch.Complex.schwarzReflection_prescribed_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Complex.schwarzReflection_prescribed_re
