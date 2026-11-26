module

public import FormalResearch.SignUncertainty.CtDualCut
public import FormalResearch.SignUncertainty.HankelEdgeRep
public import FormalResearch.SignUncertainty.HankelBandMeasure
public import FormalResearch.SignUncertainty.HankelWtConj
public import FormalResearch.SignUncertainty.CtOuterPhase
public import FormalResearch.SignUncertainty.CtOuterLogId
public import FormalResearch.SignUncertainty.CtCfuInv

/-!
# `ct:Wc-rep` and the exact Cauchy duality identity `ct:dual-id` (2)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, eq. `ct:Wc-rep` and Lemma `ct:dual-id` (2).  **Proved.**

* `ct_Wc_rep`: for `f ∈ 𝒜_c^ε` (`IsHankelEigenfn`), `c > 3/2`, `W̃_c(iτ) = (1-iτ)^{1/2} e^{-B_c(iτ)} ∫_0^∞ e^{-icΦ_Ph(τ;ξ)} dm(ξ)`
  with `dm = c (fρ₀)(cξ) dξ` (from `hankelWtS_edge_eq`, `hankelEdge_kernel_inv_eq`);
* `vertical_lines_eq_cts`: the Cauchy theorem on the strip for a function continuous on the closed strip and holomorphic inside;
* `strip_integral_zero`: antisymmetric `F(1-ζ) = -F(ζ)` with decay gives `∫ F(iy) dy = 0`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtDual

open CtOuter FormalResearch.Asymptotics FormalResearch.CohnElkies

/-- `∫_{iℝ} = ∫_{1+iℝ}` for `F` continuous on the closed strip, holomorphic inside, with an integrable decaying majorant. -/
theorem vertical_lines_eq_cts {f : ℂ → ℂ} (hc : ContinuousOn f closedStrip) (hd : DifferentiableOn ℂ f strip)
    {B : ℝ → ℝ} (hB : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B y)
    (hBint : Integrable B) (hB1 : Tendsto B atTop (𝓝 0)) (hB2 : Tendsto B atBot (𝓝 0)) :
    ∫ y : ℝ, f (1 + (y : ℂ) * Complex.I) = ∫ y : ℝ, f ((y : ℂ) * Complex.I) := by
  have hcont : ∀ x : ℝ, x ∈ Icc (0 : ℝ) 1 → Continuous fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x hx
    refine hc.comp_continuous (by fun_prop) (fun y => ?_)
    exact ⟨by simpa using hx.1, by simpa using hx.2⟩
  have hint : ∀ x : ℝ, x ∈ Icc (0 : ℝ) 1 → Integrable fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x hx
    exact Integrable.mono' hBint (hcont x hx).aestronglyMeasurable (Eventually.of_forall fun y => hB x hx y)
  have hrect : ∀ Y : ℝ, 0 < Y →
      (∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (-Y : ℝ) * Complex.I)) - (∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (Y : ℝ) * Complex.I)) +
        Complex.I * (∫ y : ℝ in (-Y)..Y, f ((1 : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ in (-Y)..Y, f ((0 : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro Y hY
    have hsub : [[((-Y : ℝ) * Complex.I : ℂ).re, ((1 : ℂ) + (Y : ℝ) * Complex.I).re]] ×ℂ
        [[((-Y : ℝ) * Complex.I : ℂ).im, ((1 : ℂ) + (Y : ℝ) * Complex.I).im]] ⊆ closedStrip := by
      intro z hz
      have h1 := hz.1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, Complex.add_re, Complex.one_re] at h1
      rw [Set.uIcc_of_le (by norm_num)] at h1
      exact ⟨h1.1, by simpa using h1.2⟩
    have hsub' : Ioo (min ((-Y : ℝ) * Complex.I : ℂ).re ((1 : ℂ) + (Y : ℝ) * Complex.I).re)
          (max ((-Y : ℝ) * Complex.I : ℂ).re ((1 : ℂ) + (Y : ℝ) * Complex.I).re) ×ℂ
        Ioo (min ((-Y : ℝ) * Complex.I : ℂ).im ((1 : ℂ) + (Y : ℝ) * Complex.I).im)
          (max ((-Y : ℝ) * Complex.I : ℂ).im ((1 : ℂ) + (Y : ℝ) * Complex.I).im) ⊆ strip := by
      intro z hz
      have h1 := hz.1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, Complex.add_re, Complex.one_re] at h1
      rw [min_eq_left (by norm_num), max_eq_right (by norm_num)] at h1
      exact ⟨h1.1, by simpa using h1.2⟩
    have := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f ((-Y : ℝ) * Complex.I)
      ((1 : ℂ) + (Y : ℝ) * Complex.I) (hc.mono hsub) (hd.mono hsub')
    simpa using this
  -- limits
  have hH1 : Tendsto (fun Y : ℝ => ∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (-Y : ℝ) * Complex.I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun Y => ?_) (hB2.comp tendsto_neg_atTop_atBot)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := B (-Y)) (f := fun x : ℝ => f ((x : ℂ) + (-Y : ℝ) * Complex.I)) (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num)] at hx
        exact hB x ⟨hx.1.le, hx.2⟩ (-Y))
    simpa using this
  have hH2 : Tendsto (fun Y : ℝ => ∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (Y : ℝ) * Complex.I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun Y => ?_) hB1
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := B Y) (f := fun x : ℝ => f ((x : ℂ) + (Y : ℝ) * Complex.I)) (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num)] at hx
        exact hB x ⟨hx.1.le, hx.2⟩ Y)
    simpa using this
  have hV1 : Tendsto (fun Y : ℝ => ∫ y : ℝ in (-Y)..Y, f ((1 : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f (1 + (y : ℂ) * Complex.I))) := by
    have h := hint 1 ⟨by norm_num, le_rfl⟩
    simp only [Complex.ofReal_one] at h
    exact intervalIntegral_tendsto_integral h tendsto_neg_atTop_atBot tendsto_id
  have hV0 : Tendsto (fun Y : ℝ => ∫ y : ℝ in (-Y)..Y, f ((0 : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f ((y : ℂ) * Complex.I))) := by
    have h := hint 0 ⟨le_rfl, by norm_num⟩
    simp only [Complex.ofReal_zero, zero_add] at h ⊢
    exact intervalIntegral_tendsto_integral h tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hH1.sub hH2).add (hV1.const_mul Complex.I)).sub (hV0.const_mul Complex.I)
  have hev : (fun Y : ℝ => (∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (-Y : ℝ) * Complex.I)) -
      (∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (Y : ℝ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (-Y)..Y, f ((1 : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ in (-Y)..Y, f ((0 : ℂ) + (y : ℂ) * Complex.I))) =ᶠ[atTop] fun _ => (0 : ℂ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY using hrect Y hY
  have h0 := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  simp only [zero_sub] at h0
  have : Complex.I * ((∫ y : ℝ, f (1 + (y : ℂ) * Complex.I)) - ∫ y : ℝ, f ((y : ℂ) * Complex.I)) = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h Complex.I_ne_zero
  · exact sub_eq_zero.mp h

/-- Antisymmetric functions: `F(1-ζ) = -F(ζ)` and decay give `∫ F(iy) dy = 0`. -/
theorem strip_integral_zero {F : ℂ → ℂ} (hc : ContinuousOn F closedStrip) (hd : DifferentiableOn ℂ F strip)
    (hsym : ∀ ζ ∈ closedStrip, F (1 - ζ) = -F ζ) {B : ℝ → ℝ}
    (hB : ∀ ζ ∈ closedStrip, ‖F ζ‖ ≤ B ζ.im) (hBint : Integrable B) (hB1 : Tendsto B atTop (𝓝 0))
    (hB2 : Tendsto B atBot (𝓝 0)) : ∫ y : ℝ, F ((y : ℂ) * Complex.I) = 0 := by
  have h1 := vertical_lines_eq_cts hc hd (B := B) (fun x hx y => by
    refine hB _ ⟨by simpa using hx.1, by simpa using hx.2⟩ |>.trans_eq ?_
    simp) hBint hB1 hB2
  have h2 : ∫ y : ℝ, F (1 + (y : ℂ) * Complex.I) = -∫ y : ℝ, F ((y : ℂ) * Complex.I) := by
    have : ∀ y : ℝ, F (1 + (y : ℂ) * Complex.I) = -F (((-y : ℝ) : ℂ) * Complex.I) := fun y => by
      have hmem : (((-y : ℝ) : ℂ) * Complex.I) ∈ closedStrip := ⟨by simp, by simp⟩
      have := hsym _ hmem
      rw [show (1 : ℂ) - ((-y : ℝ) : ℂ) * Complex.I = 1 + (y : ℂ) * Complex.I by push_cast; ring] at this
      rw [this]
    simp_rw [this]
    rw [integral_neg, integral_neg_eq_self (fun y : ℝ => F ((y : ℂ) * Complex.I)) volume]
  rw [h2] at h1
  have : (2 : ℂ) * ∫ y : ℝ, F ((y : ℂ) * Complex.I) = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp this with h | h
  · norm_num at h
  · exact h

/-- Conjugate-symmetric integrand: if `∫_ℝ f = 0` then `Re ∫_{(0,∞)} f = 0`. -/
theorem re_half_line_zero {f : ℝ → ℂ} (hint : Integrable f) (hconj : ∀ y : ℝ, f (-y) = starRingEnd ℂ (f y))
    (h0 : ∫ y : ℝ, f y = 0) : (∫ y in Ioi (0 : ℝ), f y).re = 0 := by
  have hsplit : ∫ y : ℝ, f y = (∫ y in Iic (0 : ℝ), f y) + ∫ y in Ioi (0 : ℝ), f y := by
    rw [← setIntegral_union (Set.disjoint_left.2 fun x hx hx' => absurd hx' (not_lt.2 hx))
      measurableSet_Ioi hint.integrableOn hint.integrableOn, Set.Iic_union_Ioi, Measure.restrict_univ]
  have hIic : ∫ y in Iic (0 : ℝ), f y = starRingEnd ℂ (∫ y in Ioi (0 : ℝ), f y) := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun y => f (-y))
    simp only [neg_neg, neg_zero] at h
    rw [h, ← integral_conj]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => hconj y
  rw [hsplit, hIic] at h0
  have := congrArg Complex.re h0
  simp at this
  linarith

/-- `ct:Wc-rep`: the boundary representation of `W̃_c` as an integral against `dm = c (fρ₀)(cξ) dξ`. -/
theorem ct_Wc_rep {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (τ : ℝ) :
    hankelWtS c ε f ((τ : ℂ) * Complex.I) =
      (1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ) * Complex.exp (-(binetDiff c ((τ : ℂ) * Complex.I))) *
        ∫ ξ in Ioi (0 : ℝ), Complex.exp (-(Complex.I * (c : ℂ) *
          (edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ))) * ((hankelDmDens c f ξ : ℝ) : ℂ) := by
  rw [hankelWtS_edge_eq hc hf τ, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  rw [hankelEdge_kernel_inv_eq c τ ξ hξ]
  unfold hankelDmDens
  ring

/-- The Gaussian regulariser `e^{-δ ζ(1-ζ)}` as a function of `ζ`. -/
noncomputable def gcutC (δ : ℝ) (ζ : ℂ) : ℂ := Complex.exp (-(δ : ℂ) * (ζ * (1 - ζ)))

lemma gcutC_I_mul (δ y : ℝ) : gcutC δ ((y : ℂ) * Complex.I) = CtOsc.gcut δ y := by
  unfold gcutC CtOsc.gcut
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

lemma gcutC_one_sub (δ : ℝ) (ζ : ℂ) : gcutC δ (1 - ζ) = gcutC δ ζ := by
  unfold gcutC; congr 1; ring

lemma gcutC_conj (δ : ℝ) (ζ : ℂ) : gcutC δ (starRingEnd ℂ ζ) = starRingEnd ℂ (gcutC δ ζ) := by
  unfold gcutC
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_neg, map_mul, map_sub, map_one, Complex.conj_ofReal]

lemma differentiable_gcutC (δ : ℝ) : Differentiable ℂ (gcutC δ) := by
  unfold gcutC; fun_prop

lemma norm_gcutC (δ : ℝ) (ζ : ℂ) :
    ‖gcutC δ ζ‖ = Real.exp (-(δ * (ζ.re * (1 - ζ.re) + ζ.im ^ 2))) := by
  unfold gcutC
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

lemma norm_gcutC_le {δ : ℝ} (hδ : 0 ≤ δ) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    ‖gcutC δ ζ‖ ≤ Real.exp (-(δ * ζ.im ^ 2)) := by
  rw [norm_gcutC]
  apply Real.exp_le_exp.2
  have : 0 ≤ ζ.re * (1 - ζ.re) := mul_nonneg hζ.1 (by linarith [hζ.2])
  nlinarith [mul_nonneg hδ this]

/-- Conjugation symmetry of `W̃_c` on the closed strip. -/
theorem hankelWtS_conj {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1)
    {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    hankelWtS c ε f (starRingEnd ℂ ζ) = starRingEnd ℂ (hankelWtS c ε f ζ) := by
  have hcl : ∀ z ∈ closedStrip, starRingEnd ℂ z ∈ closedStrip := fun z hz =>
    ⟨by rw [Complex.conj_re]; exact hz.1, by rw [Complex.conj_re]; exact hz.2⟩
  have hEq : EqOn (fun z => hankelWtS c ε f (starRingEnd ℂ z)) (fun z => starRingEnd ℂ (hankelWtS c ε f z)) strip := by
    intro z hz
    simp only
    have h1 : (starRingEnd ℂ z).re = z.re := by simp
    rw [hankelWtS_eq hc hf (by rw [h1]; exact hz.1.le) (by rw [h1]; exact hz.2),
      hankelWtS_eq hc hf hz.1.le hz.2, hankelWt_conj f hz.1 hz.2]
  have hc1 : ContinuousOn (fun z => hankelWtS c ε f (starRingEnd ℂ z)) closedStrip :=
    (hankelWtS_continuousOn hc hf).comp (Complex.continuous_conj.continuousOn) (fun z hz => hcl z hz)
  have hc2 : ContinuousOn (fun z => starRingEnd ℂ (hankelWtS c ε f z)) closedStrip :=
    Complex.continuous_conj.comp_continuousOn (hankelWtS_continuousOn hc hf)
  exact (hEq.of_subset_closure hc1 hc2 strip_subset_closedStrip (by rw [closure_strip_eq])) hζ

lemma gauss_tendsto_atTop (K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun y : ℝ => K * Real.exp (-(δ * y ^ 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => δ * y ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop hδ
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  simpa using (h2.const_mul K)

lemma gauss_tendsto_atBot (K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun y : ℝ => K * Real.exp (-(δ * y ^ 2))) atBot (𝓝 0) := by
  have := (gauss_tendsto_atTop K hδ).comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

/-- The regularised product `F_δ = G_ε · M_δ · W̃_c` on the closed strip. -/
noncomputable def Fd (c ε : ℝ) (f : ℝ → ℝ) (δ : ℝ) (ζ : ℂ) : ℂ :=
  outerGbar ε ζ * gcutC δ ζ * hankelWtS c ε f ζ

section Fprops

variable {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1)
include hc hf hε

theorem Fd_continuousOn (δ : ℝ) : ContinuousOn (Fd c ε f δ) closedStrip :=
  ((outerGbar_continuousOn ε).mul (differentiable_gcutC δ).continuous.continuousOn).mul
    (hankelWtS_continuousOn hc hf)

theorem Fd_differentiableOn (δ : ℝ) : DifferentiableOn ℂ (Fd c ε f δ) strip := by
  have h1 : DifferentiableOn ℂ (outerGbar ε) strip :=
    (outerG_differentiableOn ε).congr (fun z hz => outerGbar_eq_outerG ε hz)
  exact (h1.mul (differentiable_gcutC δ).differentiableOn).mul (hankelWtS_differentiableOn hc hf)

theorem Fd_one_sub (δ : ℝ) {ζ : ℂ} (hζ : ζ ∈ closedStrip) : Fd c ε f δ (1 - ζ) = -Fd c ε f δ ζ := by
  unfold Fd
  rw [outerGbar_oneSub hε hζ, gcutC_one_sub, hankelWtS_one_sub hc hf hε hζ.1 hζ.2]
  rcases hε with rfl | rfl <;> push_cast <;> ring

theorem Fd_conj (δ : ℝ) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    Fd c ε f δ (starRingEnd ℂ ζ) = starRingEnd ℂ (Fd c ε f δ ζ) := by
  unfold Fd
  rw [outerGbar_conj hε hζ, gcutC_conj, hankelWtS_conj hc hf hε hζ, map_mul, map_mul]

theorem Fd_bound (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ K : ℝ, ∀ ζ ∈ closedStrip, ‖Fd c ε f δ ζ‖ ≤ K * Real.exp (-(δ * ζ.im ^ 2)) := by
  obtain ⟨Cg, hCg⟩ := (outerGbar_bound (ε := ε))
  have hc0 : 0 < c := by linarith
  have hCg0 : 0 ≤ Cg := by
    have := hCg 0 ⟨le_rfl, zero_le_one⟩
    simp at this
    linarith [norm_nonneg (outerGbar ε 0)]
  set Cw : ℝ := hankelMass c f * Real.exp (1 / (6 * c)) with hCw
  have hCw0 : 0 ≤ Cw := mul_nonneg (hankelMass_nonneg hc0 f) (Real.exp_pos _).le
  refine ⟨Cg * Cw * Real.sqrt 2, fun ζ hζ => ?_⟩
  set y := ζ.im with hy
  set u : ℝ := 1 + |y| with hu
  have hu1 : 1 ≤ u := by rw [hu]; linarith [abs_nonneg y]
  have hu0 : 0 < u := by linarith
  have hE := (Real.exp_pos (-(δ * y ^ 2))).le
  have h1 : ‖outerGbar ε ζ‖ ≤ Cg / u := hCg ζ hζ
  have h2 : ‖gcutC δ ζ‖ ≤ Real.exp (-(δ * y ^ 2)) := norm_gcutC_le hδ hζ
  have h3 : ‖hankelWtS c ε f ζ‖ ≤ Cw * (Real.sqrt 2 * Real.sqrt u) := by
    refine (hankelWtS_norm_le hc hf hε hζ.1 hζ.2).trans ?_
    rw [← hCw]
    apply mul_le_mul_of_nonneg_left _ hCw0
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    have : ‖ζ‖ ≤ u := by
      refine (Complex.norm_le_abs_re_add_abs_im ζ).trans ?_
      have : |ζ.re| ≤ 1 := by rw [abs_of_nonneg hζ.1]; exact hζ.2
      rw [hu]; linarith
    linarith
  have hs : Real.sqrt u / u ≤ 1 := by
    rw [div_le_one hu0]
    have : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
    nlinarith [Real.sqrt_nonneg u, Real.one_le_sqrt.2 hu1]
  unfold Fd
  rw [norm_mul, norm_mul]
  calc ‖outerGbar ε ζ‖ * ‖gcutC δ ζ‖ * ‖hankelWtS c ε f ζ‖ ≤
        (Cg / u) * Real.exp (-(δ * y ^ 2)) * (Cw * (Real.sqrt 2 * Real.sqrt u)) := by
        refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)
    _ = (Cg * Cw * Real.sqrt 2) * Real.exp (-(δ * y ^ 2)) * (Real.sqrt u / u) := by
        field_simp
    _ ≤ (Cg * Cw * Real.sqrt 2) * Real.exp (-(δ * y ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := mul_one _

/-- **The Cauchy step**: for `δ > 0`, `Re ∫_0^∞ F_δ(iy) dy = 0`. -/
theorem Fd_re_zero {δ : ℝ} (hδ : 0 < δ) : (∫ y in Ioi (0 : ℝ), Fd c ε f δ ((y : ℂ) * Complex.I)).re = 0 := by
  obtain ⟨K, hK⟩ := Fd_bound hc hf hε δ hδ.le
  have hgauss : Integrable (fun y : ℝ => K * Real.exp (-(δ * y ^ 2))) := by
    have := integrable_exp_neg_mul_sq hδ
    simpa [mul_comm] using this.const_mul K
  have hmem : ∀ y : ℝ, ((y : ℂ) * Complex.I) ∈ closedStrip := fun y => ⟨by simp, by simp⟩
  have hint : Integrable (fun y : ℝ => Fd c ε f δ ((y : ℂ) * Complex.I)) := by
    refine Integrable.mono' hgauss ?_ (Eventually.of_forall fun y => ?_)
    · exact ((Fd_continuousOn hc hf hε δ).comp_continuous (by fun_prop) hmem).aestronglyMeasurable
    · have := hK _ (hmem y)
      simpa using this
  have hzero : ∫ y : ℝ, Fd c ε f δ ((y : ℂ) * Complex.I) = 0 := by
    refine strip_integral_zero (Fd_continuousOn hc hf hε δ) (Fd_differentiableOn hc hf hε δ)
      (fun ζ hζ => Fd_one_sub hc hf hε δ hζ) (B := fun y => K * Real.exp (-(δ * y ^ 2)))
      (fun ζ hζ => hK ζ hζ) hgauss ?_ ?_
    · exact gauss_tendsto_atTop K hδ
    · exact gauss_tendsto_atBot K hδ
  refine re_half_line_zero hint (fun y => ?_) hzero
  have := Fd_conj hc hf hε δ (hmem y)
  have hc' : starRingEnd ℂ ((y : ℂ) * Complex.I) = ((-y : ℝ) : ℂ) * Complex.I := by simp [map_mul]
  rw [hc'] at this
  exact this

end Fprops

/-- info: 'FormalResearch.SignUncertainty.CtDual.ct_Wc_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_Wc_rep

/-- info: 'FormalResearch.SignUncertainty.CtDual.strip_integral_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strip_integral_zero

/-- info: 'FormalResearch.SignUncertainty.CtDual.Fd_re_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fd_re_zero

end FormalResearch.SignUncertainty.CtDual
