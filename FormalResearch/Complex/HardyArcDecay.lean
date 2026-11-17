module

public import FormalResearch.Complex.HardyHalfPlane

/-!
# Fejér–Riesz arc bound for polynomially growing `G` with `L¹` boundary values, and decay of the arcs

Generic complex analysis, no Airy content.  **Proved.**  Let `G` be holomorphic on the open upper half-plane `ℍ`, continuous
on its closure, with `‖G z‖ ≤ C (1 + ‖z‖)^m` on `Im z ≥ 0` and `G|_ℝ ∈ L¹(ℝ)` (`Integrable (fun x : ℝ => G x)`).

* `hardy_arc_le_poly`: `a ∫_0^π ‖G(a e^{iφ})‖ dφ ≤ (1/2) ∫_ℝ ‖G‖` for every `a > 0` (the semicircle `S_a` carries at most
  half of the `L¹` norm of the boundary values);
* `hardy_arc_tendsto_zero`: `a ∫_0^π ‖G(a e^{iφ})‖ dφ → 0` as `a → ∞` (every sequence, not only a subsequence).

Proof (the notes' Lemma FR, step (2)): `HardyHalfPlane.hardy_arc_le` applies to `G_δ = G·(1 - iδz)^{-(m+3)}` (decay `(1+|z|)^{-3}`);
`|(1 - iδz)^{-K}| ≤ 1` on `Im z ≥ 0` and `→ 1` as `δ → 0`, so the bound passes to the limit (dominated convergence on the arc).
For the decay: `G = G_η + (G - G_η)`; the arc integral of `G_η` is `O(a^{-2})`, and that of `G - G_η` is at most
`(1/2)∫_ℝ ‖G‖ ‖1 - (1 - iηx)^{-K}‖`, which tends to `0` as `η → 0⁺` (dominated convergence).  Not formalised here:
`∫_ℝ G = 0` and the pointwise bound `‖G(z)‖ ≤ ‖g‖₁/(4π Im z)` are `HardyPoint` (not needed for the arc bound); the Poisson representation is not formalised.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace FormalResearch.Hardy

/-- The damping factor `(1 - iδz)^{-K}`. -/
noncomputable def hpDamp (δ : ℝ) (K : ℕ) (z : ℂ) : ℂ := 1 / (1 - I * δ * z) ^ K

lemma one_sub_I_mul_norm_sq (δ : ℝ) (z : ℂ) :
    ‖1 - I * (δ : ℂ) * z‖ ^ 2 = (1 + δ * z.im) ^ 2 + δ ^ 2 * z.re ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma one_le_norm_one_sub {δ : ℝ} (hδ : 0 ≤ δ) {z : ℂ} (hz : 0 ≤ z.im) : 1 ≤ ‖1 - I * (δ : ℂ) * z‖ := by
  have h := one_sub_I_mul_norm_sq δ z
  have h1 : 1 ≤ ‖1 - I * (δ : ℂ) * z‖ ^ 2 := by
    rw [h]; nlinarith [sq_nonneg (δ * z.re), mul_nonneg hδ hz]
  nlinarith [norm_nonneg (1 - I * (δ : ℂ) * z)]

lemma one_add_le_sqrt_two_mul {δ : ℝ} (hδ : 0 ≤ δ) {z : ℂ} (hz : 0 ≤ z.im) :
    1 + δ * ‖z‖ ≤ 2 * ‖1 - I * (δ : ℂ) * z‖ := by
  have h := one_sub_I_mul_norm_sq δ z
  have hz2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : (1 + δ * ‖z‖) ^ 2 ≤ 2 * ‖1 - I * (δ : ℂ) * z‖ ^ 2 := by
    rw [h]
    have : (1 + δ * ‖z‖) ^ 2 ≤ 2 * (1 + δ ^ 2 * ‖z‖ ^ 2) := by nlinarith [sq_nonneg (1 - δ * ‖z‖)]
    nlinarith [mul_nonneg hδ hz, sq_nonneg (δ * z.im), sq_nonneg (δ * z.re)]
  have h2 : (1 + δ * ‖z‖) ^ 2 ≤ (2 * ‖1 - I * (δ : ℂ) * z‖) ^ 2 := by nlinarith [norm_nonneg (1 - I * (δ : ℂ) * z)]
  exact (sq_le_sq₀ (by positivity) (by positivity)).1 h2

lemma one_sub_I_mul_ne_zero {δ : ℝ} (hδ : 0 ≤ δ) {z : ℂ} (hz : 0 ≤ z.im) : 1 - I * (δ : ℂ) * z ≠ 0 := by
  intro h
  have := one_le_norm_one_sub hδ hz
  rw [h, norm_zero] at this
  linarith

lemma norm_hpDamp_le_one {δ : ℝ} (hδ : 0 ≤ δ) (K : ℕ) {z : ℂ} (hz : 0 ≤ z.im) : ‖hpDamp δ K z‖ ≤ 1 := by
  unfold hpDamp
  rw [norm_div, norm_one, norm_pow, div_le_one (by have := one_le_norm_one_sub hδ hz; positivity)]
  exact one_le_pow₀ (one_le_norm_one_sub hδ hz)

lemma norm_hpDamp_le {δ : ℝ} (hδ : 0 ≤ δ) (K : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖hpDamp δ K z‖ ≤ (2 / (1 + δ * ‖z‖)) ^ K := by
  unfold hpDamp
  have h1 := one_le_norm_one_sub hδ hz
  have h2 := one_add_le_sqrt_two_mul hδ hz
  have hpos : 0 < 1 + δ * ‖z‖ := by positivity
  rw [norm_div, norm_one, norm_pow, ← one_div_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ K
  rw [div_le_div_iff₀ (by linarith) hpos]
  nlinarith

lemma diffContOnCl_damp {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {δ : ℝ} (hδ : 0 ≤ δ) (K : ℕ) :
    DiffContOnCl ℂ (fun z => G z * hpDamp δ K z) {z : ℂ | 0 < z.im} := by
  have hd : ∀ z : ℂ, 0 ≤ z.im → (1 - I * (δ : ℂ) * z) ^ K ≠ 0 := fun z hz =>
    pow_ne_zero _ (one_sub_I_mul_ne_zero hδ hz)
  refine ⟨?_, ?_⟩
  · intro z hz
    have hz' : 0 ≤ z.im := le_of_lt hz
    have h1 : DifferentiableAt ℂ G z := hG.1.differentiableAt (isOpen_im_pos.mem_nhds hz)
    refine (h1.mul ?_).differentiableWithinAt
    unfold hpDamp
    exact (differentiableAt_const _).div (by fun_prop) (hd z hz')
  · rw [closure_setOfPred_lt_im]
    intro z hz
    have hz' : 0 ≤ z.im := hz
    have h1 : ContinuousWithinAt G {z : ℂ | 0 ≤ z.im} z := by
      have := hG.2 z (by rw [closure_setOfPred_lt_im]; exact hz')
      rwa [closure_setOfPred_lt_im] at this
    refine h1.mul ?_
    unfold hpDamp
    have hden : ContinuousAt (fun v : ℂ => (1 - I * (δ : ℂ) * v) ^ K) z := by fun_prop
    exact ((continuousAt_const).div hden (hd z hz')).continuousWithinAt

lemma circleMap_im_nonneg {a : ℝ} (ha : 0 ≤ a) {φ : ℝ} (hφ : φ ∈ Icc (0 : ℝ) π) : 0 ≤ (circleMap 0 a φ).im := by
  simp only [circleMap, zero_add, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  exact mul_nonneg ha (Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 hφ.2)

lemma norm_damp_decay {G : ℂ → ℂ} {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖G z * hpDamp δ (m + 3) z‖ * (1 + ‖z‖) ^ 3 ≤ C * 2 ^ (m + 3) * max 1 δ⁻¹ ^ (m + 3) := by
  have hC0 : 0 ≤ C := by
    have := hC 0 (by simp)
    simp at this
    exact le_trans (norm_nonneg _) this
  rw [norm_mul]
  have h1 := hC z hz
  have h2 := norm_hpDamp_le hδ.le (m + 3) hz
  have h3 : 1 + ‖z‖ ≤ max 1 δ⁻¹ * (1 + δ * ‖z‖) := by
    rcases le_total 1 δ⁻¹ with h | h
    · rw [max_eq_right h]
      have : ‖z‖ = δ⁻¹ * (δ * ‖z‖) := by field_simp
      nlinarith [norm_nonneg z, mul_nonneg hδ.le (norm_nonneg z)]
    · rw [max_eq_left h]
      have : 1 ≤ δ := by
        by_contra hlt; push Not at hlt
        have := (one_lt_inv₀ hδ).2 hlt
        linarith
      nlinarith [norm_nonneg z, mul_nonneg hδ.le (norm_nonneg z)]
  have hpos : 0 < 1 + δ * ‖z‖ := by positivity
  calc ‖G z‖ * ‖hpDamp δ (m + 3) z‖ * (1 + ‖z‖) ^ 3
      ≤ (C * (1 + ‖z‖) ^ m) * (2 / (1 + δ * ‖z‖)) ^ (m + 3) * (1 + ‖z‖) ^ 3 := by gcongr
    _ = C * 2 ^ (m + 3) * ((1 + ‖z‖) / (1 + δ * ‖z‖)) ^ (m + 3) := by
        rw [div_pow, div_pow]; field_simp; ring
    _ ≤ C * 2 ^ (m + 3) * (max 1 δ⁻¹) ^ (m + 3) := by
        gcongr
        rw [div_le_iff₀ hpos]; exact h3

lemma tendsto_hpDamp_zero (K : ℕ) (z : ℂ) : Tendsto (fun δ : ℝ => hpDamp δ K z) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun δ : ℝ => hpDamp δ K z) 0 := by
    unfold hpDamp
    have : ContinuousAt (fun δ : ℝ => (1 - I * (δ : ℂ) * z) ^ K) 0 := by fun_prop
    refine (continuousAt_const).div this ?_
    simp
  have := hc.tendsto
  simp only [hpDamp] at this ⊢
  simpa using this.mono_left nhdsWithin_le_nhds

lemma continuousOn_norm_arc {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {a : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun φ : ℝ => ‖G (circleMap 0 a φ)‖) (Icc 0 π) := by
  have hGc : ContinuousOn G {z : ℂ | 0 ≤ z.im} := by
    have := hG.2; rwa [closure_setOfPred_lt_im] at this
  exact (hGc.comp (continuous_circleMap 0 a).continuousOn (fun φ hφ => circleMap_im_nonneg ha hφ)).norm

/-- **Fejér–Riesz arc inequality, polynomial growth.** -/
theorem hardy_arc_le_poly {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ)))
    {a : ℝ} (ha : 0 < a) :
    a * ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ)‖ ≤ (1 / 2) * ∫ t : ℝ, ‖G (t : ℂ)‖ := by
  have hGc : ContinuousOn G {z : ℂ | 0 ≤ z.im} := by
    have := hG.2; rwa [closure_setOfPred_lt_im] at this
  have hreal : ∀ x : ℝ, 0 ≤ (x : ℂ).im := fun x => by simp
  -- the bound for each damped function
  have hmain : ∀ δ : ℝ, 0 < δ →
      a * ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ) * hpDamp δ (m + 3) (circleMap 0 a φ)‖ ≤
        (1 / 2) * ∫ t : ℝ, ‖G (t : ℂ)‖ := by
    intro δ hδ
    have h1 := hardy_arc_le (diffContOnCl_damp hG hδ.le (m + 3)) (fun z hz => norm_damp_decay hC hδ hz) ha
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine integral_mono_of_nonneg (Eventually.of_forall fun x : ℝ => norm_nonneg (G (x : ℂ) * hpDamp δ (m + 3) (x : ℂ)))
      hint.norm (Eventually.of_forall fun x : ℝ => ?_)
    show ‖G (x : ℂ) * hpDamp δ (m + 3) (x : ℂ)‖ ≤ ‖G (x : ℂ)‖
    rw [norm_mul]
    have := norm_hpDamp_le_one hδ.le (m + 3) (hreal x)
    calc ‖G (x : ℂ)‖ * ‖hpDamp δ (m + 3) (x : ℂ)‖ ≤ ‖G (x : ℂ)‖ * 1 := by gcongr
      _ = ‖G (x : ℂ)‖ := mul_one _
  -- δ → 0
  have hlim : Tendsto (fun δ : ℝ => a * ∫ φ in (0 : ℝ)..π,
      ‖G (circleMap 0 a φ) * hpDamp δ (m + 3) (circleMap 0 a φ)‖) (𝓝[>] 0)
      (𝓝 (a * ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ)‖)) := by
    refine Tendsto.const_mul a ?_
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun φ => ‖G (circleMap 0 a φ)‖) ?_ ?_ ?_ ?_
    · refine eventually_of_mem self_mem_nhdsWithin fun δ hδ => ?_
      have hδ' : 0 < δ := hδ
      have hc' : ContinuousOn (fun φ : ℝ => ‖G (circleMap 0 a φ) * hpDamp δ (m + 3) (circleMap 0 a φ)‖)
          (Icc 0 π) := by
        have := (diffContOnCl_damp hG hδ'.le (m + 3)).2
        rw [closure_setOfPred_lt_im] at this
        exact (this.comp (continuous_circleMap 0 a).continuousOn
          (fun φ hφ => circleMap_im_nonneg ha.le hφ)).norm
      have hsub : Set.uIoc (0 : ℝ) π ⊆ Icc 0 π := by
        rw [Set.uIoc_of_le Real.pi_pos.le]; exact Ioc_subset_Icc_self
      have hc := hc'.mono hsub
      exact hc.aestronglyMeasurable measurableSet_uIoc
    · refine eventually_of_mem self_mem_nhdsWithin fun δ hδ => ?_
      have hδ' : 0 < δ := hδ
      refine Eventually.of_forall fun φ hφ => ?_
      rw [Set.uIoc_of_le Real.pi_pos.le] at hφ
      have hz := circleMap_im_nonneg ha.le (Ioc_subset_Icc_self hφ)
      rw [norm_norm, norm_mul]
      have := norm_hpDamp_le_one hδ'.le (m + 3) hz
      calc ‖G (circleMap 0 a φ)‖ * ‖hpDamp δ (m + 3) (circleMap 0 a φ)‖ ≤ ‖G (circleMap 0 a φ)‖ * 1 := by gcongr
        _ = _ := mul_one _
    · exact (continuousOn_norm_arc hG ha.le).intervalIntegrable_of_Icc Real.pi_pos.le
    · refine Eventually.of_forall fun φ hφ => ?_
      rw [Set.uIoc_of_le Real.pi_pos.le] at hφ
      have hz := circleMap_im_nonneg ha.le (Ioc_subset_Icc_self hφ)
      set z := circleMap 0 a φ
      have hdamp := tendsto_hpDamp_zero (m + 3) z
      have := ((tendsto_const_nhds (x := G z)).mul hdamp).norm
      simpa using this
  exact le_of_tendsto hlim (eventually_of_mem self_mem_nhdsWithin fun δ hδ => hmain δ hδ)

lemma integrable_damp {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {δ : ℝ} (hδ : 0 ≤ δ) (K : ℕ)
    (hint : Integrable (fun x : ℝ => G (x : ℂ))) :
    Integrable (fun x : ℝ => G (x : ℂ) * hpDamp δ K (x : ℂ)) := by
  have hc : ContinuousOn (fun z => G z * hpDamp δ K z) {z : ℂ | 0 ≤ z.im} := by
    have := (diffContOnCl_damp hG hδ K).2
    rwa [closure_setOfPred_lt_im] at this
  have hcont : Continuous (fun x : ℝ => G (x : ℂ) * hpDamp δ K (x : ℂ)) :=
    hc.comp_continuous Complex.continuous_ofReal (fun x => by simp)
  refine Integrable.mono' hint.norm hcont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  have := norm_hpDamp_le_one hδ K (show 0 ≤ (x : ℂ).im by simp)
  calc ‖G (x : ℂ)‖ * ‖hpDamp δ K (x : ℂ)‖ ≤ ‖G (x : ℂ)‖ * 1 := by gcongr
    _ = _ := mul_one _

lemma continuous_ofReal_comp {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) :
    Continuous (fun x : ℝ => G (x : ℂ)) := by
  have hGc : ContinuousOn G {z : ℂ | 0 ≤ z.im} := by
    have := hG.2; rwa [closure_setOfPred_lt_im] at this
  exact hGc.comp_continuous Complex.continuous_ofReal (fun x => by simp)

/-- The tail integral `∫ ‖G‖ ‖1 - (1 - iδx)^{-K}‖` tends to `0` as `δ → 0⁺`. -/
lemma tendsto_integral_damp {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im})
    (hint : Integrable (fun x : ℝ => G (x : ℂ))) (K : ℕ) :
    Tendsto (fun δ : ℝ => ∫ x : ℝ, ‖G (x : ℂ) - G (x : ℂ) * hpDamp δ K (x : ℂ)‖) (𝓝[>] 0) (𝓝 0) := by
  have := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℝ))
    (l := 𝓝[>] (0 : ℝ))
    (F := fun (δ : ℝ) (x : ℝ) => ‖G (x : ℂ) - G (x : ℂ) * hpDamp δ K (x : ℂ)‖) (f := fun _ : ℝ => (0 : ℝ))
    (fun x : ℝ => 2 * ‖G (x : ℂ)‖) ?_ ?_ (hint.norm.const_mul 2) ?_
  · simpa using this
  · refine eventually_of_mem self_mem_nhdsWithin fun δ hδ => ?_
    have hδ' : 0 < δ := hδ
    have hc : ContinuousOn (fun z => G z * hpDamp δ K z) {z : ℂ | 0 ≤ z.im} := by
      have := (diffContOnCl_damp hG hδ'.le K).2
      rwa [closure_setOfPred_lt_im] at this
    have hcont : Continuous (fun x : ℝ => G (x : ℂ) * hpDamp δ K (x : ℂ)) :=
      hc.comp_continuous Complex.continuous_ofReal (fun x => by simp)
    exact ((continuous_ofReal_comp hG).sub hcont).norm.aestronglyMeasurable
  · refine eventually_of_mem self_mem_nhdsWithin fun δ hδ => Eventually.of_forall fun x => ?_
    have hδ' : 0 < δ := hδ
    have h1 := norm_hpDamp_le_one hδ'.le K (show 0 ≤ (x : ℂ).im by simp)
    rw [norm_norm]
    calc ‖G (x : ℂ) - G (x : ℂ) * hpDamp δ K (x : ℂ)‖ ≤ ‖G (x : ℂ)‖ + ‖G (x : ℂ) * hpDamp δ K (x : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ ‖G (x : ℂ)‖ + ‖G (x : ℂ)‖ * 1 := by
          rw [norm_mul]; gcongr
      _ = 2 * ‖G (x : ℂ)‖ := by ring
  · refine Eventually.of_forall fun x => ?_
    have hdamp := tendsto_hpDamp_zero K (x : ℂ)
    have := ((tendsto_const_nhds (x := G (x : ℂ))).sub ((tendsto_const_nhds (x := G (x : ℂ))).mul hdamp)).norm
    simpa using this

/-- **The arc integrals tend to zero:** for `G` holomorphic on `ℍ`, continuous on the closure, of polynomial growth
with `L¹` boundary values, `∫_{S_a} ‖G‖ |dz| → 0` as `a → ∞` (along every sequence). -/
theorem hardy_arc_tendsto_zero {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ))) :
    Tendsto (fun a : ℝ => a * ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ)‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose the damping parameter
  have h1 := (tendsto_integral_damp hG hint (m + 3)).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨η, hηe, hηpos⟩ := (h1.and self_mem_nhdsWithin).exists
  have hη : 0 < η := hηpos
  set Cη : ℝ := C * 2 ^ (m + 3) * max 1 η⁻¹ ^ (m + 3) with hCη
  have hC0 : 0 ≤ C := by
    have := hC 0 (by simp)
    simp at this
    exact le_trans (norm_nonneg _) this
  have hCη0 : 0 ≤ Cη := by positivity
  -- eventually the decaying part is small
  have hev : ∀ᶠ a : ℝ in atTop, π * Cη / (1 + a) ^ 2 < ε / 2 := by
    have h2 : Tendsto (fun a : ℝ => π * Cη / (1 + a) ^ 2) atTop (𝓝 0) := by
      have : Tendsto (fun a : ℝ => (1 + a) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
      exact Tendsto.div_atTop tendsto_const_nhds this
    exact h2.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev, eventually_gt_atTop 0] with a hea ha
  -- the error function
  set E : ℂ → ℂ := fun z => G z - G z * hpDamp η (m + 3) z with hE
  have hEd : DiffContOnCl ℂ E {z : ℂ | 0 < z.im} := hG.sub (diffContOnCl_damp hG hη.le (m + 3))
  have hEC : ∀ z : ℂ, 0 ≤ z.im → ‖E z‖ ≤ (2 * C) * (1 + ‖z‖) ^ m := by
    intro z hz
    have h3 := norm_hpDamp_le_one hη.le (m + 3) hz
    have h4 := hC z hz
    calc ‖E z‖ ≤ ‖G z‖ + ‖G z * hpDamp η (m + 3) z‖ := norm_sub_le _ _
      _ ≤ ‖G z‖ + ‖G z‖ * 1 := by rw [norm_mul]; gcongr
      _ ≤ (2 * C) * (1 + ‖z‖) ^ m := by nlinarith
  have hEint : Integrable (fun x : ℝ => E (x : ℂ)) := hint.sub (integrable_damp hG hη.le (m + 3) hint)
  have hEarc := hardy_arc_le_poly hEd hEC hEint ha
  have hEreal : (1 / 2 : ℝ) * ∫ t : ℝ, ‖E (t : ℂ)‖ < ε / 2 := by
    have : ∫ t : ℝ, ‖E (t : ℂ)‖ < ε / 2 := hηe
    linarith
  -- the decaying part
  have hGηarc : ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ) * hpDamp η (m + 3) (circleMap 0 a φ)‖ ≤
      π * (Cη / (1 + a) ^ 3) := by
    have : ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ) * hpDamp η (m + 3) (circleMap 0 a φ)‖ ≤
        ∫ φ in (0 : ℝ)..π, Cη / (1 + a) ^ 3 := by
      refine intervalIntegral.integral_mono_on Real.pi_pos.le ?_ intervalIntegrable_const (fun φ hφ => ?_)
      · have := (diffContOnCl_damp hG hη.le (m + 3)).2
        rw [closure_setOfPred_lt_im] at this
        exact ((this.comp (continuous_circleMap 0 a).continuousOn
          (fun φ hφ => circleMap_im_nonneg ha.le hφ)).norm).intervalIntegrable_of_Icc Real.pi_pos.le
      · have hz := circleMap_im_nonneg ha.le hφ
        have h5 := norm_damp_decay hC hη hz
        have hn : ‖circleMap 0 a φ‖ = a := by rw [norm_circleMap_zero, abs_of_pos ha]
        rw [hn] at h5
        rw [le_div_iff₀ (by positivity)]
        exact h5
    refine this.trans ?_
    simp [mul_div_assoc]
  -- triangle inequality on the arc
  have hsplit : ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ)‖ ≤
      (∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ) * hpDamp η (m + 3) (circleMap 0 a φ)‖) +
        ∫ φ in (0 : ℝ)..π, ‖E (circleMap 0 a φ)‖ := by
    have hi1 : IntervalIntegrable (fun φ : ℝ => ‖G (circleMap 0 a φ) * hpDamp η (m + 3) (circleMap 0 a φ)‖)
        volume 0 π := by
      have := (diffContOnCl_damp hG hη.le (m + 3)).2
      rw [closure_setOfPred_lt_im] at this
      exact ((this.comp (continuous_circleMap 0 a).continuousOn
        (fun φ hφ => circleMap_im_nonneg ha.le hφ)).norm).intervalIntegrable_of_Icc Real.pi_pos.le
    have hi2 : IntervalIntegrable (fun φ : ℝ => ‖E (circleMap 0 a φ)‖) volume 0 π := by
      have := hEd.2
      rw [closure_setOfPred_lt_im] at this
      exact ((this.comp (continuous_circleMap 0 a).continuousOn
        (fun φ hφ => circleMap_im_nonneg ha.le hφ)).norm).intervalIntegrable_of_Icc Real.pi_pos.le
    rw [← intervalIntegral.integral_add hi1 hi2]
    refine intervalIntegral.integral_mono_on Real.pi_pos.le
      ((continuousOn_norm_arc hG ha.le).intervalIntegrable_of_Icc Real.pi_pos.le) (hi1.add hi2) (fun φ _ => ?_)
    simp only [hE]
    calc ‖G (circleMap 0 a φ)‖ = ‖G (circleMap 0 a φ) * hpDamp η (m + 3) (circleMap 0 a φ) +
          (G (circleMap 0 a φ) - G (circleMap 0 a φ) * hpDamp η (m + 3) (circleMap 0 a φ))‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have hnn : 0 ≤ a * ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ)‖ :=
    mul_nonneg ha.le (intervalIntegral.integral_nonneg Real.pi_pos.le (fun _ _ => norm_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hfin : a * (π * (Cη / (1 + a) ^ 3)) ≤ π * Cη / (1 + a) ^ 2 := by
    have h6 : a / (1 + a) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc a * (π * (Cη / (1 + a) ^ 3)) = (a / (1 + a)) * (π * Cη / (1 + a) ^ 2) := by field_simp
      _ ≤ 1 * (π * Cη / (1 + a) ^ 2) := by
          gcongr
      _ = _ := one_mul _
  calc a * ∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ)‖
      ≤ a * ((∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ) * hpDamp η (m + 3) (circleMap 0 a φ)‖) +
        ∫ φ in (0 : ℝ)..π, ‖E (circleMap 0 a φ)‖) := by gcongr
    _ = a * (∫ φ in (0 : ℝ)..π, ‖G (circleMap 0 a φ) * hpDamp η (m + 3) (circleMap 0 a φ)‖) +
        a * ∫ φ in (0 : ℝ)..π, ‖E (circleMap 0 a φ)‖ := by ring
    _ ≤ a * (π * (Cη / (1 + a) ^ 3)) + (1 / 2) * ∫ t : ℝ, ‖E (t : ℂ)‖ := by
        gcongr
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- info: 'FormalResearch.Hardy.hardy_arc_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_arc_tendsto_zero

/-- info: 'FormalResearch.Hardy.hardy_arc_le_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_arc_le_poly

end FormalResearch.Hardy
