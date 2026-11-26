module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Cauchy's theorem on the strip `0 < Re s < 1` for decaying functions (FIVE-0 tool)

Generic complex analysis (no Paper II content): the contour step behind the defect identity of
`ctu:common-functional` (Paper II, `constant_term_universality.tex`, Lemma ctu.2a) and hence `cts:main`.

`strip_edge_integral_eq`: let `Ψ` be holomorphic on the open strip `0 < Re s < 1`, continuous on the closed
strip minus the two points `0` and `1`, and `‖Ψ s‖ ≤ C e^{-ε |Im s|}` on the open strip.  Then the two edge
integrals agree,
`∫_ℝ Ψ(i τ) dτ = ∫_ℝ Ψ(1 + i τ) dτ`.
It is the rectangle theorem on `[δ, 1-δ] × [-T, T]` followed by `T → ∞` (the horizontal sides decay)
and `δ → 0` (dominated convergence; the two edge points `0`, `1` are a null set).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The open vertical strip `{0 < Re s < 1}`. -/
def unitStrip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The closed vertical strip `{0 ≤ Re s ≤ 1}`. -/
def unitStripCl : Set ℂ := {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1}

lemma isOpen_unitStrip : IsOpen unitStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma unitStrip_subset_cl : unitStrip ⊆ unitStripCl := fun _ h => ⟨h.1.le, h.2.le⟩

lemma add_mul_I_mem_unitStrip {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (τ : ℝ) :
    ((x : ℂ) + τ * Complex.I) ∈ unitStrip := by
  simp [unitStrip, h0, h1]

lemma integrable_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    Integrable fun τ : ℝ => Real.exp (-(ε * |τ|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have := integrableOn_exp_mul_Iic hε 0
    refine this.congr_fun (fun v hv => ?_) measurableSet_Iic
    simp only [mem_Iic] at hv
    rw [abs_of_nonpos hv]; ring_nf
  · have := integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0
    refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hv)]; ring_nf

lemma tendsto_exp_neg_mul_atTop {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℝ => Real.exp (-(ε * T))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hε)

section

variable {Ψ : ℂ → ℂ} {C ε : ℝ}

lemma continuousOn_unitStrip (hd : DifferentiableOn ℂ Ψ unitStrip) : ContinuousOn Ψ unitStrip :=
  hd.continuousOn

/-- On a vertical line inside the open strip, `Ψ` is integrable (it is continuous and decays). -/
lemma integrable_vertical (hd : DifferentiableOn ℂ Ψ unitStrip) (hε : 0 < ε)
    (hb : ∀ s ∈ unitStrip, ‖Ψ s‖ ≤ C * Real.exp (-(ε * |s.im|))) {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    Integrable fun τ : ℝ => Ψ ((x : ℂ) + τ * Complex.I) := by
  have hcont : Continuous fun τ : ℝ => Ψ ((x : ℂ) + τ * Complex.I) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hmem := add_mul_I_mem_unitStrip h0 h1 τ
    have hc : ContinuousAt Ψ ((x : ℂ) + τ * Complex.I) :=
      hd.continuousOn.continuousAt (isOpen_unitStrip.mem_nhds hmem)
    have hf : Continuous fun τ : ℝ => (x : ℂ) + τ * Complex.I := by fun_prop
    exact ContinuousAt.comp (f := fun τ : ℝ => (x : ℂ) + τ * Complex.I) hc hf.continuousAt
  refine Integrable.mono' ((integrable_exp_neg_mul_abs hε).const_mul C) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun τ => ?_
  have := hb _ (add_mul_I_mem_unitStrip h0 h1 τ)
  simpa using this

/-- For `0 < δ < 1/2` the two interior vertical lines `Re s = δ` and `Re s = 1 - δ` carry the same integral. -/
lemma vertical_integral_eq (hd : DifferentiableOn ℂ Ψ unitStrip) (hε : 0 < ε)
    (hb : ∀ s ∈ unitStrip, ‖Ψ s‖ ≤ C * Real.exp (-(ε * |s.im|))) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    ∫ τ : ℝ, Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I) = ∫ τ : ℝ, Ψ ((δ : ℂ) + τ * Complex.I) := by
  have hC : 0 ≤ C := by
    have h := hb _ (add_mul_I_mem_unitStrip hδ (by linarith) 0)
    have h2 : 0 ≤ ‖Ψ ((δ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ := norm_nonneg _
    have h3 : 0 < Real.exp (-(ε * |((δ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I).im|)) := Real.exp_pos _
    by_contra hneg
    push Not at hneg
    nlinarith only [h, h2, h3, hneg]
  -- the rectangle identity for each `T`
  have hrect : ∀ T : ℝ, 0 < T →
      (∫ x : ℝ in δ..(1 - δ), Ψ ((x : ℂ) + (-T : ℝ) * Complex.I))
        - (∫ x : ℝ in δ..(1 - δ), Ψ ((x : ℂ) + (T : ℝ) * Complex.I))
        + Complex.I • (∫ τ : ℝ in (-T)..T, Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I))
        - Complex.I • (∫ τ : ℝ in (-T)..T, Ψ ((δ : ℂ) + τ * Complex.I)) = 0 := by
    intro T hT
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn Ψ
      ((δ : ℂ) + (-T : ℝ) * Complex.I) (((1 - δ : ℝ) : ℂ) + (T : ℝ) * Complex.I) (by
        refine hd.mono ?_
        intro s hs
        simp only [Complex.reProdIm, Set.uIcc_of_le (show δ ≤ 1 - δ by linarith),
          Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at hs
        exact ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩)
    simpa using h
  -- limit `T → ∞`
  have hexp := (tendsto_exp_neg_mul_atTop hε).const_mul (C * |1 - δ - δ|)
  rw [mul_zero] at hexp
  have hbound : ∀ t : ℝ, ‖∫ x : ℝ in δ..(1 - δ), Ψ ((x : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      C * |1 - δ - δ| * Real.exp (-(ε * |t|)) := by
    intro t
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := δ) (b := 1 - δ)
      (C := C * Real.exp (-(ε * |t|))) (f := fun x : ℝ => Ψ ((x : ℂ) + (t : ℝ) * Complex.I)) (by
        intro x hx
        rw [Set.uIoc_of_le (by linarith : δ ≤ 1 - δ)] at hx
        have := hb _ (add_mul_I_mem_unitStrip (x := x) (by linarith [hx.1]) (by linarith [hx.2]) t)
        simpa using this)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hA : Tendsto (fun T : ℝ => ∫ x : ℝ in δ..(1 - δ), Ψ ((x : ℂ) + (-T : ℝ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hexp
    filter_upwards [eventually_gt_atTop 0] with T hT
    simpa [abs_neg, abs_of_pos hT] using hbound (-T)
  have hB : Tendsto (fun T : ℝ => ∫ x : ℝ in δ..(1 - δ), Ψ ((x : ℂ) + (T : ℝ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hexp
    filter_upwards [eventually_gt_atTop 0] with T hT
    simpa [abs_of_pos hT] using hbound T
  have hV1 := intervalIntegral_tendsto_integral (μ := volume) (l := atTop) (a := fun T : ℝ => -T)
    (b := fun T : ℝ => T)
    (integrable_vertical hd hε hb (x := 1 - δ) (by linarith) (by linarith)) tendsto_neg_atTop_atBot tendsto_id
  have hV0 := intervalIntegral_tendsto_integral (μ := volume) (l := atTop) (a := fun T : ℝ => -T)
    (b := fun T : ℝ => T)
    (integrable_vertical hd hε hb (x := δ) hδ (by linarith)) tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ =>
      (∫ x : ℝ in δ..(1 - δ), Ψ ((x : ℂ) + (-T : ℝ) * Complex.I))
        - (∫ x : ℝ in δ..(1 - δ), Ψ ((x : ℂ) + (T : ℝ) * Complex.I))
        + Complex.I • (∫ τ : ℝ in (-T)..T, Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I))
        - Complex.I • (∫ τ : ℝ in (-T)..T, Ψ ((δ : ℂ) + τ * Complex.I))) atTop
      (𝓝 (0 - 0 + Complex.I • (∫ τ : ℝ, Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I))
        - Complex.I • (∫ τ : ℝ, Ψ ((δ : ℂ) + τ * Complex.I)))) :=
    (((hA.sub hB).add (hV1.const_smul Complex.I)).sub (hV0.const_smul Complex.I))
  have hzero : Tendsto (fun T : ℝ =>
      (∫ x : ℝ in δ..(1 - δ), Ψ ((x : ℂ) + (-T : ℝ) * Complex.I))
        - (∫ x : ℝ in δ..(1 - δ), Ψ ((x : ℂ) + (T : ℝ) * Complex.I))
        + Complex.I • (∫ τ : ℝ in (-T)..T, Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I))
        - Complex.I • (∫ τ : ℝ in (-T)..T, Ψ ((δ : ℂ) + τ * Complex.I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop 0] with T hT using (hrect T hT).symm)
  have h3 := tendsto_nhds_unique hlim hzero
  have h2 : Complex.I • (∫ τ : ℝ, Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I))
      = Complex.I • (∫ τ : ℝ, Ψ ((δ : ℂ) + τ * Complex.I)) := by
    linear_combination h3
  exact smul_right_injective ℂ Complex.I_ne_zero h2

/-- **Cauchy's theorem on the strip for decaying functions** (edge form):
`∫_ℝ Ψ(i τ) dτ = ∫_ℝ Ψ(1 + i τ) dτ` for `Ψ` holomorphic on `0 < Re s < 1`, continuous on the closed strip
off the two points `0`, `1`, and `‖Ψ s‖ ≤ C e^{-ε |Im s|}`. -/
theorem strip_edge_integral_eq (hd : DifferentiableOn ℂ Ψ unitStrip) (hε : 0 < ε)
    (hc : ContinuousOn Ψ (unitStripCl \ {0, 1}))
    (hb : ∀ s ∈ unitStrip, ‖Ψ s‖ ≤ C * Real.exp (-(ε * |s.im|))) :
    ∫ τ : ℝ, Ψ ((τ : ℂ) * Complex.I) = ∫ τ : ℝ, Ψ (1 + (τ : ℂ) * Complex.I) := by
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  have hbd : ∀ᶠ δ : ℝ in l, ∀ τ : ℝ, ‖Ψ ((δ : ℂ) + τ * Complex.I)‖ ≤ C * Real.exp (-(ε * |τ|)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ τ
    have := hb _ (add_mul_I_mem_unitStrip hδ.1 (by linarith [hδ.2]) τ)
    simpa using this
  have hbd' : ∀ᶠ δ : ℝ in l, ∀ τ : ℝ, ‖Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I)‖ ≤ C * Real.exp (-(ε * |τ|)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ τ
    have := hb _ (add_mul_I_mem_unitStrip (x := 1 - δ) (by linarith [hδ.2]) (by linarith [hδ.1]) τ)
    simpa using this
  have hint : Integrable fun τ : ℝ => C * Real.exp (-(ε * |τ|)) :=
    (integrable_exp_neg_mul_abs hε).const_mul C
  have hmeas : ∀ᶠ δ : ℝ in l, AEStronglyMeasurable (fun τ : ℝ => Ψ ((δ : ℂ) + τ * Complex.I)) volume := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
    exact (integrable_vertical hd hε hb hδ.1 (by linarith [hδ.2])).aestronglyMeasurable
  have hmeas' : ∀ᶠ δ : ℝ in l,
      AEStronglyMeasurable (fun τ : ℝ => Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I)) volume := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
    exact (integrable_vertical hd hε hb (x := 1 - δ) (by linarith [hδ.2]) (by linarith [hδ.1])).aestronglyMeasurable
  have hlim0 : ∀ᵐ τ : ℝ, Tendsto (fun δ : ℝ => Ψ ((δ : ℂ) + τ * Complex.I)) l (𝓝 (Ψ ((τ : ℂ) * Complex.I))) := by
    have hne : ∀ᵐ τ : ℝ, τ ≠ 0 := by
      have : (volume : Measure ℝ) {0} = 0 := Real.volume_singleton
      filter_upwards [compl_mem_ae_iff.mpr this] with τ hτ using hτ
    filter_upwards [hne] with τ hτ
    have hmem : (τ : ℂ) * Complex.I ∈ unitStripCl \ {0, 1} := by
      refine ⟨by simp [unitStripCl], ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨?_, ?_⟩
      · intro h; apply hτ; simpa [Complex.ext_iff] using h
      · intro h; have := congrArg Complex.re h; simp at this
    have hcw := (hc _ hmem)
    have hmap : Tendsto (fun δ : ℝ => (δ : ℂ) + τ * Complex.I) l (𝓝[unitStripCl \ {0, 1}] ((τ : ℂ) * Complex.I)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun δ : ℝ => (δ : ℂ) + τ * Complex.I) (𝓝 (0 : ℝ)) (𝓝 ((τ : ℂ) * Complex.I)) := by
          have hc' : Continuous fun δ : ℝ => (δ : ℂ) + τ * Complex.I := by fun_prop
          simpa using hc'.tendsto 0
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
        refine ⟨⟨by simp [hδ.1.le], by simp; linarith [hδ.2]⟩, ?_⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        refine ⟨?_, ?_⟩
        · intro h; apply hτ; have := congrArg Complex.im h; simpa using this
        · intro h; apply hτ; have := congrArg Complex.im h; simpa using this
    exact hcw.tendsto.comp hmap
  have hlim1 : ∀ᵐ τ : ℝ, Tendsto (fun δ : ℝ => Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I)) l
      (𝓝 (Ψ (1 + (τ : ℂ) * Complex.I))) := by
    have hne : ∀ᵐ τ : ℝ, τ ≠ 0 := by
      have : (volume : Measure ℝ) {0} = 0 := Real.volume_singleton
      filter_upwards [compl_mem_ae_iff.mpr this] with τ hτ using hτ
    filter_upwards [hne] with τ hτ
    have hmem : 1 + (τ : ℂ) * Complex.I ∈ unitStripCl \ {0, 1} := by
      refine ⟨by simp [unitStripCl], ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.re h; simp at this
      · intro h; apply hτ; have := congrArg Complex.im h; simpa using this
    have hcw := (hc _ hmem)
    have hmap : Tendsto (fun δ : ℝ => ((1 - δ : ℝ) : ℂ) + τ * Complex.I) l
        (𝓝[unitStripCl \ {0, 1}] (1 + (τ : ℂ) * Complex.I)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun δ : ℝ => ((1 - δ : ℝ) : ℂ) + τ * Complex.I) (𝓝 (0 : ℝ))
            (𝓝 (1 + (τ : ℂ) * Complex.I)) := by
          have hc' : Continuous fun δ : ℝ => ((1 - δ : ℝ) : ℂ) + τ * Complex.I := by fun_prop
          simpa using hc'.tendsto 0
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
        refine ⟨⟨by simp; linarith [hδ.2], by simp; linarith [hδ.1]⟩, ?_⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        refine ⟨?_, ?_⟩
        · intro h; apply hτ; have := congrArg Complex.im h; simpa using this
        · intro h; have := congrArg Complex.re h; simp at this; linarith [hδ.1]
    exact hcw.tendsto.comp hmap
  have T0 := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (l := l)
    (F := fun (δ τ : ℝ) => Ψ ((δ : ℂ) + τ * Complex.I)) (f := fun τ : ℝ => Ψ ((τ : ℂ) * Complex.I))
    (fun τ : ℝ => C * Real.exp (-(ε * |τ|))) hmeas
    (by filter_upwards [hbd] with δ h; exact Filter.Eventually.of_forall fun τ => h τ) hint hlim0
  have T1 := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (l := l)
    (F := fun (δ τ : ℝ) => Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I)) (f := fun τ : ℝ => Ψ (1 + (τ : ℂ) * Complex.I))
    (fun τ : ℝ => C * Real.exp (-(ε * |τ|))) hmeas'
    (by filter_upwards [hbd'] with δ h; exact Filter.Eventually.of_forall fun τ => h τ) hint hlim1
  have heq : (fun δ : ℝ => ∫ τ : ℝ, Ψ (((1 - δ : ℝ) : ℂ) + τ * Complex.I)) =ᶠ[l]
      (fun δ : ℝ => ∫ τ : ℝ, Ψ ((δ : ℂ) + τ * Complex.I)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
    exact vertical_integral_eq hd hε hb hδ.1 hδ.2
  have hne : l.NeBot := inferInstance
  exact tendsto_nhds_unique T0 (T1.congr' heq)

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.strip_edge_integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.strip_edge_integral_eq
