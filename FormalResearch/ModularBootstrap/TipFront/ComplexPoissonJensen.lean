module

public import FormalResearch.ModularBootstrap.TipFront.ComplexMajorant
public import FormalResearch.ModularBootstrap.PoissonJensen.LemmaPJAssembly
public import FormalResearch.ModularBootstrap.Blowup.Majorant
public import FormalResearch.ModularBootstrap.Integration.StripTheoremA

/-!
# Complex-`b` Poisson–Jensen Estimate and Concrete `StripBootstrapInputs`

Proves Lemma PJ (`lower_o1_two_edge.tex`, Lemma `vlo:PJ`) for **complex** points `b = 𝓑(z)`
in the tip neighborhood (`0 < z.im`, `‖z - σ_*‖ ≤ 0.1`, `|b.im| < 1/2`), and constructs the
unconditional `virasoroStripBootstrapInputs : StripBootstrapInputs`:

* `slitBoundaryMapC_eq_confB`: `slitBoundaryMapC z = confB z` for `0 < z.im`.
* `hankelContinuation_bdy_ne_zero_ae_of_complex`: a.e. nonvanishing of
  `hankelContinuation c' g` along the slit boundary from nonvanishing at any strip point `b`.
* `stripPoissonJensen_complex`: the complex-`b` strip Poisson–Jensen inequality with potential
  `PoissonJensen.majorant2D`, matching `BlowupTest.hPJ_complex`.
* `virasoroStripBootstrapInputs`: canonical unconditional `StripBootstrapInputs` combining
  `lemmaGPotentialInput_virasoro`, `PoissonJensen.stripPoissonJensen`,
  `Crossing.virasoro_Ka_ub`, `Crossing.lemmaGapInput_of_lemmaPJInput`, and
  `stripPoissonJensen_complex`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology Metric
open scoped Interval

namespace FormalResearch.ModularBootstrap.TipFront

open PoissonJensen Crossing Integration Bessel

/-! ### 1. Tip geometry bounds for `confB` and `slitBoundaryMapC` -/

lemma slitBoundaryMapC_eq_confB {z : ℂ} (hz : 0 < z.im) :
    slitBoundaryMapC z = confB z := by
  unfold slitBoundaryMapC
  rw [confB_eq_log_confE hz]
  unfold confE
  push_cast
  rfl

private lemma sqrt_two_bounds : (1.41 : ℝ) < √2 ∧ √2 < 1.42 := by
  constructor
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.41)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.42)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma abs_confB_re_le_of_tip_ball {z : ℂ} (hz_im : 0 < z.im)
    (hz : ‖z - (sigmaStar : ℂ)‖ ≤ 0.1) :
    |(confB z).re| ≤ Real.log 12 / (2 * π) := by
  obtain ⟨hsq_lo, hsq_hi⟩ := sqrt_two_bounds
  have hσ_def : sigmaStar = 1 - √2 := rfl
  have hσ_lo : (-0.42 : ℝ) < sigmaStar := by linarith
  have hσ_hi : sigmaStar < -0.41 := by linarith
  -- Distance bounds from `σ_*` to `1`, `0`, `-1`
  have hz1_lo : 1.31 ≤ ‖z - 1‖ := by
    have h1 : ‖(sigmaStar - 1 : ℂ)‖ = 1 - sigmaStar := by
      rw [show (sigmaStar - 1 : ℂ) = ((sigmaStar - 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    have htri : ‖(sigmaStar - 1 : ℂ)‖ ≤ ‖z - (sigmaStar : ℂ)‖ + ‖z - 1‖ := by
      calc ‖(sigmaStar - 1 : ℂ)‖
          = ‖-(z - (sigmaStar : ℂ)) + (z - 1)‖ := by ring_nf
        _ ≤ ‖-(z - (sigmaStar : ℂ))‖ + ‖z - 1‖ := norm_add_le _ _
        _ = ‖z - (sigmaStar : ℂ)‖ + ‖z - 1‖ := by rw [norm_neg]
    linarith
  have hz1_hi : ‖z - 1‖ ≤ 1.52 := by
    have h1 : ‖(sigmaStar - 1 : ℂ)‖ = 1 - sigmaStar := by
      rw [show (sigmaStar - 1 : ℂ) = ((sigmaStar - 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    calc ‖z - 1‖
        = ‖(z - (sigmaStar : ℂ)) + (sigmaStar - 1 : ℂ)‖ := by ring_nf
      _ ≤ ‖z - (sigmaStar : ℂ)‖ + ‖(sigmaStar - 1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 0.1 + (1 - sigmaStar) := by linarith
      _ ≤ 1.52 := by linarith
  have hz0_lo : 0.31 ≤ ‖z‖ := by
    have h1 : ‖(sigmaStar : ℂ)‖ = -sigmaStar := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    have htri : ‖(sigmaStar : ℂ)‖ ≤ ‖z - (sigmaStar : ℂ)‖ + ‖z‖ := by
      calc ‖(sigmaStar : ℂ)‖
          = ‖-(z - (sigmaStar : ℂ)) + z‖ := by ring_nf
        _ ≤ ‖-(z - (sigmaStar : ℂ))‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z - (sigmaStar : ℂ)‖ + ‖z‖ := by rw [norm_neg]
    linarith
  have hz0_hi : ‖z‖ ≤ 0.52 := by
    have h1 : ‖(sigmaStar : ℂ)‖ = -sigmaStar := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    calc ‖z‖
        = ‖(z - (sigmaStar : ℂ)) + (sigmaStar : ℂ)‖ := by ring_nf
      _ ≤ ‖z - (sigmaStar : ℂ)‖ + ‖(sigmaStar : ℂ)‖ := norm_add_le _ _
      _ ≤ 0.1 + (-sigmaStar) := by linarith
      _ ≤ 0.52 := by linarith
  have hzp_lo : 0.48 ≤ ‖z + 1‖ := by
    have h1 : ‖(sigmaStar + 1 : ℂ)‖ = sigmaStar + 1 := by
      rw [show (sigmaStar + 1 : ℂ) = ((sigmaStar + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have htri : ‖(sigmaStar + 1 : ℂ)‖ ≤ ‖z - (sigmaStar : ℂ)‖ + ‖z + 1‖ := by
      calc ‖(sigmaStar + 1 : ℂ)‖
          = ‖-(z - (sigmaStar : ℂ)) + (z + 1)‖ := by ring_nf
        _ ≤ ‖-(z - (sigmaStar : ℂ))‖ + ‖z + 1‖ := norm_add_le _ _
        _ = ‖z - (sigmaStar : ℂ)‖ + ‖z + 1‖ := by rw [norm_neg]
    linarith
  have hzp_hi : ‖z + 1‖ ≤ 0.69 := by
    have h1 : ‖(sigmaStar + 1 : ℂ)‖ = sigmaStar + 1 := by
      rw [show (sigmaStar + 1 : ℂ) = ((sigmaStar + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    calc ‖z + 1‖
        = ‖(z - (sigmaStar : ℂ)) + (sigmaStar + 1 : ℂ)‖ := by ring_nf
      _ ≤ ‖z - (sigmaStar : ℂ)‖ + ‖(sigmaStar + 1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 0.1 + (sigmaStar + 1) := by linarith
      _ ≤ 0.69 := by linarith
  -- Bound `‖confE z‖ ∈ [1, 12]`
  have hnormE_eq : ‖confE z‖ = ‖z - 1‖ / (‖z‖ * ‖z + 1‖) := by
    unfold confE
    rw [norm_div, norm_mul]
  have hnormE_ge1 : 1 ≤ ‖confE z‖ := by
    rw [hnormE_eq, one_le_div (mul_pos (by linarith) (by linarith))]
    nlinarith
  have hnormE_le12 : ‖confE z‖ ≤ 12 := by
    rw [hnormE_eq, div_le_iff₀ (mul_pos (by linarith) (by linarith))]
    nlinarith
  have hlogE_nn : 0 ≤ Real.log ‖confE z‖ := Real.log_nonneg hnormE_ge1
  have hlogE_le : Real.log ‖confE z‖ ≤ Real.log 12 :=
    Real.log_le_log (by linarith) hnormE_le12
  rw [confB_eq_log_confE hz_im, show (2 * (π : ℂ))⁻¹ = (((2 * π)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.log_re, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹),
    abs_of_nonneg hlogE_nn, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hlogE_le (by positivity)

/-! ### 2. A.e. nonvanishing along the slit boundary from nonvanishing at a strip point -/

lemma hankelContinuation_bdy_ne_zero_ae_of_complex {c' : ℝ} (hc : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    {b : ℂ} (hb_mem : |b.im| < 1 / 2) (hb_ne : hankelContinuation c' g b ≠ 0) :
    ∀ᵐ σ ∂(volume.restrict slitPreimage),
      hankelContinuation c' g (slitBoundaryMap σ : ℂ) ≠ 0 := by
  have han : AnalyticOnNhd ℂ (hankelContinuation c' g) {w : ℂ | |w.im| < 1 / 2} :=
    analyticOnNhd_hankelContinuation hc hg
  have hpre : IsPreconnected {w : ℂ | |w.im| < 1 / 2} := by
    have hconv : Convex ℝ {w : ℂ | |w.im| < 1 / 2} := by
      intro x hx y hy u v hu hv huv
      change |(u • x + v • y).im| < 1 / 2
      have him : (u • x + v • y).im = u * x.im + v * y.im := by
        simp [Complex.add_im, Complex.real_smul]
      rw [him]
      have hx' : |x.im| < 1 / 2 := hx
      have hy' : |y.im| < 1 / 2 := hy
      have hbd : u * |x.im| + v * |y.im| < 1 / 2 := by
        rcases eq_or_lt_of_le hu with rfl | hu_pos
        · have hv1 : v = 1 := by linarith
          subst hv1
          simpa using hy'
        · have h1 : u * |x.im| < u * (1 / 2) := mul_lt_mul_of_pos_left hx' hu_pos
          have h2 : v * |y.im| ≤ v * (1 / 2) := mul_le_mul_of_nonneg_left hy'.le hv
          linarith
      calc |u * x.im + v * y.im|
          ≤ |u * x.im| + |v * y.im| := abs_add_le _ _
        _ = u * |x.im| + v * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hv]
        _ < 1 / 2 := hbd
    exact hconv.isPreconnected
  have hz_re_cnt : {r : ℝ | hankelContinuation c' g (r : ℂ) = 0}.Countable := by
    have heq : {r : ℝ | hankelContinuation c' g (r : ℂ) = 0} =
        ⋃ n : ℕ, {r : ℝ | r ∈ Icc (-(n : ℝ)) n ∧ hankelContinuation c' g (r : ℂ) = 0} := by
      ext r
      simp only [Set.mem_ofPred_eq, mem_iUnion, mem_Icc]
      refine ⟨fun hr => ?_, fun ⟨_, _, hr⟩ => hr⟩
      obtain ⟨n, hn⟩ := exists_nat_ge |r|
      exact ⟨n, ⟨by linarith [abs_le.mp hn], by linarith [abs_le.mp hn]⟩, hr⟩
    rw [heq]
    have hfin : ∀ n : ℕ,
        {r : ℝ | r ∈ Icc (-(n : ℝ)) n ∧ hankelContinuation c' g (r : ℂ) = 0}.Finite := by
      intro n
      by_contra hinf
      rw [Set.not_finite] at hinf
      obtain ⟨r₀, _, hacc⟩ :=
        hinf.exists_accPt_of_subset_isCompact isCompact_Icc (fun _ hr => hr.1)
      have hr₀_mem : (r₀ : ℂ) ∈ {w : ℂ | |w.im| < 1 / 2} := by simp
      have hfreq : ∃ᶠ z in 𝓝[≠] (r₀ : ℂ), hankelContinuation c' g z = 0 := by
        rw [Filter.frequently_iff]
        intro U hU
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
        obtain ⟨V, hV, hVU⟩ := hU
        obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp hV
        rw [accPt_iff_frequently] at hacc
        obtain ⟨r, ⟨hr_ne, hr_mem⟩, hr_ball⟩ :=
          (hacc.and_eventually (Metric.ball_mem_nhds r₀ hε_pos)).exists
        have hrC_ne : (r : ℂ) ≠ (r₀ : ℂ) := fun he => hr_ne (Complex.ofReal_injective he)
        have hrC_ball : (r : ℂ) ∈ Metric.ball (r₀ : ℂ) ε := by
          rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs]
          simpa [Metric.mem_ball, Real.dist_eq] using hr_ball
        exact ⟨(r : ℂ), hVU ⟨hball hrC_ball, hrC_ne⟩, hr_mem.2⟩
      have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre hr₀_mem hfreq
      have hb0 := hzero hb_mem
      simp only [Pi.zero_apply] at hb0
      exact hb_ne hb0
    exact Set.countable_iUnion fun n => (hfin n).countable
  have hσ_cnt :
      {σ : ℝ | σ ∈ slitPreimage ∧ hankelContinuation c' g (slitBoundaryMap σ : ℂ) = 0}.Countable := by
    have hsub : {σ : ℝ | σ ∈ slitPreimage ∧ hankelContinuation c' g (slitBoundaryMap σ : ℂ) = 0} ⊆
        ⋃ r ∈ {r : ℝ | hankelContinuation c' g (r : ℂ) = 0},
          {σ : ℝ | σ ∈ slitPreimage ∧ slitBoundaryMap σ = r} := fun σ ⟨hσ, h0⟩ =>
      mem_iUnion₂.mpr ⟨slitBoundaryMap σ, h0, hσ, rfl⟩
    exact (hz_re_cnt.biUnion fun r _ => (slitBoundaryMap_preimage_finite r).countable).mono hsub
  have hnull : volume {σ : ℝ | σ ∈ slitPreimage ∧ hankelContinuation c' g (slitBoundaryMap σ : ℂ) = 0} = 0 :=
    hσ_cnt.measure_zero volume
  change ∀ᵐ σ ∂(volume.restrict (Ioo (-1 : ℝ) 0 ∪ Ioi 1)),
      hankelContinuation c' g (slitBoundaryMap σ : ℂ) ≠ 0
  rw [ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hσ hmem h0
  exact hσ ⟨hmem, h0⟩

/-! ### 3. Local Poisson–Jensen helpers on `slitPreimage` for arbitrary `z₀ ∈ ℍ` -/

private lemma slitMass_pos' {x y : ℝ} (hy : 0 < y) : 0 < slitMass x y := by
  have hIoo_pos : 0 < ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel x y σ := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
      (integrable_poissonKernel x hy).integrableOn).mpr ?_
    have hsupp : Function.support (poissonKernel x y) ∩ Ioo (-1 : ℝ) 0 = Ioo (-1) 0 := by
      ext σ
      simp only [mem_inter_iff, Function.mem_support, ne_eq, and_iff_right_iff_imp]
      intro _
      exact (poissonKernel_pos (x := x) hy σ).ne'
    rw [hsupp, Real.volume_Ioo]
    norm_num
  have hle : ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel x y σ ≤ slitMass x y := by
    unfold slitMass slitPreimage
    exact setIntegral_mono_set (integrable_poissonKernel x hy).integrableOn
      (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
      (ae_of_all _ fun σ hσ => Set.subset_union_left hσ)
  linarith

private lemma slitMass_le_one'' {x y : ℝ} (hy : 0 < y) : slitMass x y ≤ 1 := by
  unfold slitMass
  calc ∫ σ in slitPreimage, poissonKernel x y σ
      ≤ ∫ σ : ℝ, poissonKernel x y σ :=
        setIntegral_le_integral (integrable_poissonKernel x hy)
          (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
    _ = 1 := integral_poissonKernel x hy

private lemma one_sub_slitMass_eq_edgeMass'' {x y : ℝ} (hy : 0 < y) :
    1 - slitMass x y = ∫ σ in edgePreimage, poissonKernel x y σ := by
  have hint := integrable_poissonKernel x hy
  have hdisj : Disjoint slitPreimage edgePreimage := by
    rw [Set.disjoint_left]
    intro σ h1 h2
    rcases h1 with h1 | (h1 : 1 < σ) <;> rcases h2 with (h2 : σ < -1) | h2
    · linarith [h1.1]
    · linarith [h1.2, h2.1]
    · linarith
    · linarith [h2.2]
  have hunion_ae : (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    change ∀ᵐ σ ∂volume, (σ ∈ slitPreimage ∪ edgePreimage) = (σ ∈ (univ : Set ℝ))
    rw [ae_iff]
    refine measure_mono_null (fun σ hσ => ?_) hnull
    by_contra hnot
    apply hσ; apply propext
    simp only [mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio, mem_univ, iff_true]
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_or_gt_of_ne hnot.1 with hm | hm
    · exact Or.inr (Or.inl hm)
    · rcases lt_or_gt_of_ne hnot.2.1 with h0 | h0
      · exact Or.inl (Or.inl ⟨hm, h0⟩)
      · rcases lt_or_gt_of_ne hnot.2.2 with h1 | h1
        · exact Or.inr (Or.inr ⟨h0, h1⟩)
        · exact Or.inl (Or.inr h1)
  have htot : slitMass x y + ∫ σ in edgePreimage, poissonKernel x y σ = 1 := by
    unfold slitMass
    rw [← setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
        hint.integrableOn hint.integrableOn,
      setIntegral_congr_set hunion_ae, setIntegral_univ]
    exact integral_poissonKernel x hy
  linarith

private lemma abs_slitBoundaryMap_ge_xiStar' {σ : ℝ} (hσ : σ ∈ slitPreimage) :
    xiStar ≤ |slitBoundaryMap σ| := by
  rcases hσ with hIoo | hIoi
  · exact (xiStar_le_slitBoundaryMap hIoo).trans (le_abs_self _)
  · have := slitBoundaryMap_le_neg_xiStar hIoi
    linarith [neg_abs_le (slitBoundaryMap σ)]

private lemma log_integral_jensen_slitPreimage' {x y : ℝ} (hy : 0 < y)
    {f : ℝ → ℝ} (hf_pos : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ)
    (hf_int : IntegrableOn (fun σ => f σ * poissonKernel x y σ) slitPreimage)
    (hlog_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x y σ) slitPreimage)
    {B : ℝ} (_hB_pos : 0 < B)
    (hI_le : ∫ σ in slitPreimage, f σ * poissonKernel x y σ ≤ B) :
    ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x y σ ≤
      slitMass x y * Real.log B + (1 - slitMass x y) := by
  have hm_pos : 0 < slitMass x y := slitMass_pos' hy
  set m := slitMass x y
  set I_f := ∫ σ in slitPreimage, f σ * poissonKernel x y σ
  have hIf_pos : 0 < I_f := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hf_int).mpr ?_
    · filter_upwards [hf_pos] with σ hσ
      exact mul_nonneg hσ.le (poissonKernel_nonneg hy.le σ)
    · have hIoo_sub : Ioo (-1 : ℝ) 0 ⊆ slitPreimage := Set.subset_union_left
      have hIoo_pos : 0 < volume (Ioo (-1 : ℝ) 0) := by rw [Real.volume_Ioo]; norm_num
      have hae_pos : ∀ᵐ σ ∂volume, σ ∈ Ioo (-1 : ℝ) 0 → 0 < f σ * poissonKernel x y σ := by
        have h1 : ∀ᵐ σ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), 0 < f σ :=
          hf_pos.filter_mono (ae_mono (Measure.restrict_mono hIoo_sub le_rfl))
        rw [ae_restrict_iff' measurableSet_Ioo] at h1
        filter_upwards [h1] with σ hσ hm
        exact mul_pos (hσ hm) (poissonKernel_pos (x := x) hy σ)
      by_contra h0
      have hzero : volume ((Function.support fun σ => f σ * poissonKernel x y σ) ∩ slitPreimage) = 0 :=
        nonpos_iff_eq_zero.mp (not_lt.mp h0)
      have hnull1 : ∀ᵐ σ ∂volume, ¬(σ ∈ Ioo (-1 : ℝ) 0 ∧ f σ * poissonKernel x y σ ≠ 0) := by
        rw [← compl_mem_ae_iff] at hzero
        filter_upwards [hzero] with σ hσ ⟨h1, h2⟩
        exact hσ ⟨h2, hIoo_sub h1⟩
      have hsub_empty : ∀ᵐ σ ∂volume, σ ∉ Ioo (-1 : ℝ) 0 := by
        filter_upwards [hae_pos, hnull1] with σ hp hn hm
        exact hn ⟨hm, (hp hm).ne'⟩
      have hv0 : volume (Ioo (-1 : ℝ) 0) = 0 := by
        rw [ae_iff] at hsub_empty
        convert hsub_empty using 2
        ext σ; simp
      exact hIoo_pos.ne' hv0
  set c_avg := I_f / m
  have hc_pos : 0 < c_avg := div_pos hIf_pos hm_pos
  have hlog_bd : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x y σ ≤
        (Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ) := by
    filter_upwards [hf_pos] with σ hσ
    have h1 : Real.log (f σ / c_avg) ≤ f σ / c_avg - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hσ hc_pos)
    rw [Real.log_div hσ.ne' hc_pos.ne'] at h1
    have h2 : Real.log (f σ) ≤ (Real.log c_avg - 1) + c_avg⁻¹ * f σ := by
      linarith [show f σ / c_avg = c_avg⁻¹ * f σ by ring]
    have hP0 := poissonKernel_nonneg (x := x) hy.le σ
    calc Real.log (f σ) * poissonKernel x y σ
        ≤ ((Real.log c_avg - 1) + c_avg⁻¹ * f σ) * poissonKernel x y σ := by gcongr
      _ = (Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ) := by
          ring
  have hpk_int : IntegrableOn (poissonKernel x y) slitPreimage :=
    (integrable_poissonKernel x hy).integrableOn
  have hrhs_int : IntegrableOn
      (fun σ => (Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ))
      slitPreimage :=
    (hpk_int.const_mul _).add (hf_int.const_mul _)
  have hint_mono : ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x y σ ≤
      ∫ σ in slitPreimage,
        ((Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ)) :=
    setIntegral_mono_ae_restrict hlog_int hrhs_int hlog_bd
  have heval : ∫ σ in slitPreimage,
        ((Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ)) =
      m * Real.log (I_f / m) := by
    rw [integral_add (hpk_int.const_mul _) (hf_int.const_mul _),
      integral_const_mul, integral_const_mul]
    change (Real.log c_avg - 1) * m + c_avg⁻¹ * I_f = m * Real.log (I_f / m)
    have hc_eq : c_avg⁻¹ * I_f = m := by
      dsimp [c_avg]; field_simp [hm_pos.ne', hIf_pos.ne']
    rw [hc_eq]
    dsimp [c_avg]
    ring
  have hdiv_le : m * Real.log (I_f / m) ≤ m * Real.log B + (1 - m) := by
    rw [div_eq_mul_inv, Real.log_mul hIf_pos.ne' (inv_ne_zero hm_pos.ne')]
    have hlogI : Real.log I_f ≤ Real.log B := Real.log_le_log hIf_pos hI_le
    have hlogm : Real.log m⁻¹ ≤ m⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hm_pos)
    have hm1 : m * Real.log m⁻¹ ≤ 1 - m := by
      calc m * Real.log m⁻¹ ≤ m * (m⁻¹ - 1) := mul_le_mul_of_nonneg_left hlogm hm_pos.le
        _ = 1 - m := by field_simp [hm_pos.ne']
    calc m * (Real.log I_f + Real.log m⁻¹)
        = m * Real.log I_f + m * Real.log m⁻¹ := by ring
      _ ≤ m * Real.log B + (1 - m) := add_le_add (mul_le_mul_of_nonneg_left hlogI hm_pos.le) hm1
  exact hint_mono.trans (heval.le.trans hdiv_le)

/-! ### 4. Complex-`b` Lemma PJ and `virasoroStripBootstrapInputs` -/

/-- Explicit complex-`b` Poisson–Jensen threshold constant (`10000 ≥ 39`). -/
noncomputable def c_PJ_complex : ℝ := 10000

/-- Explicit complex-`b` Poisson–Jensen additive constant on `‖z - σ_*‖ ≤ 0.1`, `0 < z.im`. -/
noncomputable def C_PJ_complex : ℝ :=
  Real.log (4 * π * Real.exp 92) +
    max 0 (Real.log (2 * (9 * Real.sqrt (2 * π) / xiStar))) + 1 +
    (1 / 2 : ℝ) * (|majorantU0| + (4 * π / 3) * (Real.log 12 / (2 * π) + 2) ^ 2) + 4

/-- **Complex-`b` Lemma PJ** (`lower_o1_two_edge.tex`, Lemma `vlo:PJ` at complex `b = 𝓑(z)` near
the tip): for `10000 ≤ c'`, `g ∈ TestClass virasoroProblem (c' / 12)` with `M[g] > 0`, and any
`z ∈ ℍ` with `‖z - σ_*‖ ≤ 0.1`, writing `b = slitBoundaryMapC z` (`G = hankelContinuation c' g`),
if `|b.im| < 1/2` and `G b ≠ 0` then
`log ‖G b‖ ≤ c' * majorant2D b + log M - (1/2) log c' + (5/2)(1 - slitMass z.re z.im) log c' + slitEntropy z.re z.im + C_PJ_complex`. -/
theorem stripPoissonJensen_complex {c' : ℝ} (hc' : c_PJ_complex ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    {z : ℂ} (hz_im : 0 < z.im) (hz_tip : ‖z - (sigmaStar : ℂ)‖ ≤ 0.1)
    (hb_im : |(slitBoundaryMapC z).im| < 1 / 2)
    (hb_ne : hankelContinuation c' g (slitBoundaryMapC z) ≠ 0) :
    let b := slitBoundaryMapC z
    let M := virasoroProblem.cardyNorm (c' / 12) g
    Real.log ‖hankelContinuation c' g b‖ ≤
      c' * majorant2D b + Real.log M - (1 / 2 : ℝ) * Real.log c' +
        (5 / 2 : ℝ) * (1 - slitMass z.re z.im) * Real.log c' + slitEntropy z.re z.im +
        C_PJ_complex := by
  have hc10000 : 10000 ≤ c' := hc'
  have hc1000 : 1000 ≤ c' := by linarith
  have hc8 : 8 ≤ c' := by linarith
  have hc0 : 0 < c' := by linarith
  let C_slit : ℝ := 9 * Real.sqrt (2 * π) / xiStar
  have hCslit_pos : 0 < C_slit := by dsimp [C_slit]; positivity [xiStar_pos]
  let C_U : ℝ := |majorantU0| + (4 * π / 3) * (Real.log 12 / (2 * π) + 2) ^ 2
  set M : ℝ := virasoroProblem.cardyNorm (c' / 12) g
  set x₀ : ℝ := z.re
  set y₀ : ℝ := z.im
  have hy₀_pos : 0 < y₀ := hz_im
  have hm_pos : 0 < slitMass x₀ y₀ := slitMass_pos' hy₀_pos
  have hm_le : slitMass x₀ y₀ ≤ 1 := slitMass_le_one'' hy₀_pos
  set m : ℝ := slitMass x₀ y₀
  let F : ℂ → ℂ := fun w => (M⁻¹ : ℂ) * hankelContinuation c' g (confB w)
  let F_bdy : ℝ → ℂ := fun σ => (M⁻¹ : ℂ) * hankelContinuation c' g (confB (σ : ℂ))
  let M_strip : ℝ := 4 * π * Real.exp 92 * c' ^ 2
  have hMstrip_ge1 : 1 ≤ M_strip := by
    dsimp [M_strip]
    have h1 : 1 ≤ Real.exp 92 := Real.one_le_exp (by norm_num)
    have h2 := Real.pi_gt_three
    have h3 : 1 ≤ 4 * π * Real.exp 92 := by nlinarith
    have h4 : 1 ≤ c' ^ 2 := by nlinarith
    nlinarith
  have hMstrip_pos : 0 < M_strip := by linarith
  have hF_diff : DifferentiableOn ℂ F {w : ℂ | 0 < w.im} := by
    intro w hw
    have hcb : confB w ∈ slitStrip := confB_mem_slitStrip hw
    have hc_diff : DifferentiableAt ℂ confB w := (hasDerivAt_confB hw).differentiableAt
    have hg_diff : DifferentiableAt ℂ (hankelContinuation c' g) (confB w) :=
      (differentiableOn_hankelContinuation hc1000 hg).differentiableAt
        ((isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds hcb.1)
    exact ((hg_diff.comp w hc_diff).const_mul (M⁻¹ : ℂ)).differentiableWithinAt
  have hF_bd : ∀ w : ℂ, 0 < w.im → ‖F w‖ ≤ M_strip := by
    intro w hw
    have hcb : |(confB w).im| ≤ 1 / 2 := (confB_mem_slitStrip hw).1.le
    have hsup := lemmaB_d_sup hc1000 hg hcb
    dsimp [F]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos]
    calc M⁻¹ * ‖hankelContinuation c' g (confB w)‖
        ≤ M⁻¹ * (M_strip * M) := by gcongr
      _ = M_strip := by field_simp [hM_pos.ne']
  have hconfB_im_real : ∀ σ : ℝ, σ ∉ ({-1, 0, 1} : Set ℝ) → |(confB (σ : ℂ)).im| ≤ 1 / 2 := by
    intro σ hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_trichotomy σ (-1) with hm | rfl | hm1
    · rw [confB_real_im_of_lt_neg_one hm]; norm_num
    · exact absurd rfl hnot.1
    · rcases lt_trichotomy σ 0 with h0 | rfl | h0
      · rw [confB_real_im_of_mem_Ioo_neg_one_zero ⟨hm1, h0⟩]; norm_num
      · exact absurd rfl hnot.2.1
      · rcases lt_trichotomy σ 1 with h1 | rfl | h1
        · rw [confB_real_im_of_mem_Ioo_zero_one ⟨h0, h1⟩]; norm_num
        · exact absurd rfl hnot.2.2
        · rw [confB_real_im_of_one_lt h1]; norm_num
  have hF_bdy : ∀ᵐ σ : ℝ ∂volume,
      Tendsto F (𝓝[{w : ℂ | 0 < w.im}] (σ : ℂ)) (𝓝 (F_bdy σ)) := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hnot
    have hnot' : σ ∉ ({-1, 0, 1} : Set ℝ) := hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot'
    have htend_B : Tendsto confB (𝓝[{w : ℂ | 0 < w.im}] (σ : ℂ))
        (𝓝[{b : ℂ | |b.im| ≤ 1 / 2}] (confB (σ : ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (confB_continuousWithinAt_real hnot'.2.1 hnot'.2.2 hnot'.1).tendsto.mono_left
          (nhdsWithin_mono _ fun w (hw : 0 < w.im) => hw.le)
      · filter_upwards [self_mem_nhdsWithin] with w hw
        exact (confB_mem_slitStrip hw).1.le
    have htend_G : Tendsto (fun w : ℂ => hankelContinuation c' g (confB w))
        (𝓝[{w : ℂ | 0 < w.im}] (σ : ℂ)) (𝓝 (hankelContinuation c' g (confB (σ : ℂ)))) :=
      ((continuousOn_hankelContinuation hc1000 hg).continuousWithinAt
        (hconfB_im_real σ hnot)).tendsto.comp htend_B
    exact tendsto_const_nhds.mul htend_G
  have hb_eq : slitBoundaryMapC z = confB z := slitBoundaryMapC_eq_confB hz_im
  have hFz_ne : F z ≠ 0 := by
    dsimp [F]
    rw [← hb_eq]
    exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hb_ne
  obtain ⟨hPJ_int, hPJ_le⟩ := halfPlane_poissonJensen hMstrip_pos hF_diff hF_bd hF_bdy hz_im hFz_ne
  change Real.log ‖F z‖ ≤ ∫ σ, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ at hPJ_le
  have hlhs_eq : Real.log ‖F z‖ = Real.log ‖hankelContinuation c' g (slitBoundaryMapC z)‖ - Real.log M := by
    dsimp [F]
    rw [← hb_eq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos,
      Real.log_mul (inv_ne_zero hM_pos.ne') (norm_ne_zero_iff.mpr hb_ne), Real.log_inv]
    ring
  rw [hlhs_eq] at hPJ_le
  have hdisj : Disjoint slitPreimage edgePreimage := by
    rw [Set.disjoint_left]
    intro σ h1 h2
    rcases h1 with h1 | (h1 : 1 < σ) <;> rcases h2 with (h2 : σ < -1) | h2
    · linarith [h1.1]
    · linarith [h1.2, h2.1]
    · linarith
    · linarith [h2.2]
  have hunion_ae : (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    change ∀ᵐ σ ∂volume, (σ ∈ slitPreimage ∪ edgePreimage) = (σ ∈ (univ : Set ℝ))
    rw [ae_iff]
    refine measure_mono_null (fun σ hσ => ?_) hnull
    by_contra hnot
    apply hσ; apply propext
    simp only [mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio, mem_univ, iff_true]
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_or_gt_of_ne hnot.1 with hm | hm
    · exact Or.inr (Or.inl hm)
    · rcases lt_or_gt_of_ne hnot.2.1 with h0 | h0
      · exact Or.inl (Or.inl ⟨hm, h0⟩)
      · rcases lt_or_gt_of_ne hnot.2.2 with h1 | h1
        · exact Or.inr (Or.inr ⟨h0, h1⟩)
        · exact Or.inl (Or.inr h1)
  have hsplit_eq : ∫ σ : ℝ, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) +
        (∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set hunion_ae]
    exact setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
      hPJ_int.integrableOn hPJ_int.integrableOn
  -- Edge bound
  have hedge_le : ∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤
      (1 - m) * Real.log (4 * π * Real.exp 92) + 2 * (1 - m) * Real.log c' := by
    have hint_edge := hPJ_int.integrableOn (s := edgePreimage)
    have hpk_edge : IntegrableOn (fun σ => Real.log M_strip * poissonKernel x₀ y₀ σ) edgePreimage :=
      (integrable_poissonKernel x₀ hy₀_pos).integrableOn.const_mul _
    have hpt_edge : ∀ σ ∈ edgePreimage,
        Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤ Real.log M_strip * poissonKernel x₀ y₀ σ := by
      intro σ hσ
      have hnot : σ ∉ ({-1, 0, 1} : Set ℝ) := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        rcases hσ with (hlt : σ < -1) | ⟨h0, h1⟩
        · exact ⟨by linarith, by linarith, by linarith⟩
        · exact ⟨by linarith, by linarith, by linarith⟩
      have hsup := lemmaB_d_sup hc1000 hg (hconfB_im_real σ hnot)
      have hbd_σ : ‖F_bdy σ‖ ≤ M_strip := by
        dsimp [F_bdy]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos]
        calc M⁻¹ * ‖hankelContinuation c' g (confB (σ : ℂ))‖
            ≤ M⁻¹ * (M_strip * M) := by gcongr
          _ = M_strip := by field_simp [hM_pos.ne']
      have hlog_le : Real.log ‖F_bdy σ‖ ≤ Real.log M_strip := by
        by_cases h0 : ‖F_bdy σ‖ = 0
        · rw [h0, Real.log_zero]; exact Real.log_nonneg hMstrip_ge1
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) hbd_σ
      exact mul_le_mul_of_nonneg_right hlog_le (poissonKernel_nonneg hy₀_pos.le σ)
    have hmono := setIntegral_mono_on hint_edge hpk_edge (measurableSet_Iio.union measurableSet_Ioo) hpt_edge
    rw [integral_const_mul, ← one_sub_slitMass_eq_edgeMass'' hy₀_pos] at hmono
    have hMstrip_log : Real.log M_strip = Real.log (4 * π * Real.exp 92) + 2 * Real.log c' := by
      dsimp [M_strip]
      rw [Real.log_mul (by positivity) (pow_ne_zero 2 hc0.ne'), Real.log_pow, Nat.cast_ofNat]
    rw [hMstrip_log] at hmono
    linarith [hmono]
  -- Slit bound
  have hslit_confB : ∀ σ ∈ slitPreimage, confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := by
    intro σ hσ
    rcases hσ with hIoo | hIoi
    · have h0 : σ ≠ 0 := hIoo.2.ne
      have h1 : σ ≠ 1 := by linarith [hIoo.2]
      have hm1 : σ ≠ -1 := hIoo.1.ne'
      exact Complex.ext (confB_real_re h0 h1 hm1) (confB_real_im_of_mem_Ioo_neg_one_zero hIoo)
    · have hgt : 1 < σ := hIoi
      exact Complex.ext (confB_real_re (by linarith) hgt.ne' (by linarith))
        (confB_real_im_of_one_lt hgt)
  let φ : ℝ → ℝ := fun t => (|g (c' * t ^ 2 / 3)| / M) * besselI0 (c' * besselL t)
  have hφ_cont : Continuous φ := by
    have hg_cont : Continuous (fun t : ℝ => g (c' * t ^ 2 / 3)) :=
      hg.cont.comp_continuous (by fun_prop) (fun t => by change 0 ≤ c' * t ^ 2 / 3; positivity)
    have hb_cont : Continuous (fun t : ℝ => besselI0 (c' * besselL t)) :=
      continuous_besselI0.comp (continuous_const.mul (by unfold besselL; fun_prop))
    exact (hg_cont.abs.div_const M).mul hb_cont
  have hφ_meas : Measurable φ := hφ_cont.measurable
  have hφ_nn : ∀ t ∈ Ioi xiStar, 0 ≤ φ t := fun t _ => by
    dsimp [φ]
    exact mul_nonneg (div_nonneg (abs_nonneg _) hM_pos.le) (zero_le_one.trans (one_le_besselI0 _))
  obtain ⟨heS_int, heS_le⟩ := eSlitMass hc10000 hg
  have hφ_eq_on : EqOn φ (fun t => (|g (c' * t ^ 2 / 3)| * besselK (c' / 12) (c' * t ^ 2 / 3)) / M)
      (Ioi xiStar) := fun t ht => by
    have hK := besselK_shift (c' := c') (x := t) (j := 0) hc0 (xiStar_pos.trans ht).le
    simp only [mul_zero, zero_div, sub_zero, Real.sqrt_one, mul_one] at hK
    dsimp [φ]; rw [← hK]; ring
  have hφ_int : IntegrableOn φ (Ioi xiStar) := by
    have hi : IntegrableOn (fun t => |g (c' * t ^ 2 / 3)| * besselK (c' / 12) (c' * t ^ 2 / 3) / M)
        (Ioi xiStar) := heS_int.div_const M
    exact hi.congr_fun hφ_eq_on.symm measurableSet_Ioi
  have hIφ_le : 2 * ∫ t in Ioi xiStar, φ t ≤ 2 * C_slit * c'⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioi hφ_eq_on, integral_div]
    calc 2 * ((∫ t in Ioi xiStar, |g (c' * t ^ 2 / 3)| * besselK (c' / 12) (c' * t ^ 2 / 3)) / M)
        ≤ 2 * ((C_slit * c'⁻¹ * M) / M) := by gcongr
      _ = 2 * C_slit * c'⁻¹ := by field_simp [hM_pos.ne']
  obtain ⟨hf_pull_int, hf_pull_eq⟩ :=
    setIntegral_slitPreimage_div_slitDensity (x := x₀) hy₀_pos hφ_meas hφ_nn hφ_int
  let K_val : ℝ → ℝ := fun σ => besselI0 (c' * besselL |slitBoundaryMap σ|)
  let f : ℝ → ℝ := fun σ => φ |slitBoundaryMap σ| / slitDensity x₀ y₀ σ
  have hK_eq : ∀ σ ∈ slitPreimage,
      K_val σ = besselK (c' / 12) (c' * |slitBoundaryMap σ| ^ 2 / 3) := fun σ hσ => by
    have hge := (xiStar_pos.trans_le (abs_slitBoundaryMap_ge_xiStar' hσ)).le
    have hK := besselK_shift (c' := c') (x := |slitBoundaryMap σ|) (j := 0) hc0 hge
    simpa [K_val] using hK.symm
  have hK_ge1 : ∀ σ : ℝ, 1 ≤ K_val σ := fun σ => one_le_besselI0 _
  have hK_pos : ∀ σ : ℝ, 0 < K_val σ := fun σ => lt_of_lt_of_le zero_lt_one (hK_ge1 σ)
  have hFbdy_eq : ∀ σ ∈ slitPreimage,
      ‖F_bdy σ‖ = |g (c' * (slitBoundaryMap σ) ^ 2 / 3)| / M := fun σ hσ => by
    dsimp [F_bdy]
    rw [hslit_confB σ hσ, hankelContinuation_ofReal hc0 hg (slitBoundaryMap σ),
      norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hM_pos, inv_mul_eq_div]
  have hf_eq_Fbdy : ∀ σ ∈ slitPreimage, f σ = ‖F_bdy σ‖ * K_val σ / slitDensity x₀ y₀ σ := by
    intro σ hσ
    dsimp [f, φ, K_val]
    rw [hFbdy_eq σ hσ, sq_abs]
  have hG_ne_ae := hankelContinuation_bdy_ne_zero_ae_of_complex hc1000 hg hb_im hb_ne
  have hf_pos_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ := by
    have hω_pos := slitDensity_pos_ae (x := x₀) hy₀_pos
    have hmem_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), σ ∈ slitPreimage :=
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)
    filter_upwards [hG_ne_ae, hω_pos, hmem_ae] with σ hG hω hσ
    rw [hf_eq_Fbdy σ hσ]
    have hF_pos : 0 < ‖F_bdy σ‖ := by
      dsimp [F_bdy]
      rw [hslit_confB σ hσ]
      exact norm_pos_iff.mpr (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hG)
    exact div_pos (mul_pos hF_pos (hK_pos σ)) hω
  have hlogK_int : IntegrableOn
      (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ) slitPreimage := by
    have hident := identification_integrand_integrable x₀ hy₀_pos
    have hpk_int : IntegrableOn (poissonKernel x₀ y₀) slitPreimage :=
      (integrable_poissonKernel x₀ hy₀_pos).integrableOn
    let u₀ : ℝ := 2 * π * xiStar / 3
    have hu₀_pos : 0 < u₀ := by dsimp [u₀]; positivity [xiStar_pos]
    let Ck : ℝ := 4 + (1 / 2 : ℝ) * (|Real.log c'| + |Real.log u₀|)
    let dom : ℝ → ℝ := fun σ =>
      (c' + 1 / 2) * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) + Ck * poissonKernel x₀ y₀ σ
    have hdom_int : IntegrableOn dom slitPreimage :=
      (hident.const_mul _).add (hpk_int.const_mul _)
    have hmeas_K : AEStronglyMeasurable
        (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ) (volume.restrict slitPreimage) := by
      have hm_L : Measurable (fun σ : ℝ => c' * besselL |slitBoundaryMap σ|) :=
        measurable_const.mul ((by unfold besselL; fun_prop : Continuous besselL).measurable.comp
          measurable_slitBoundaryMap.abs)
      exact ((Real.measurable_log.comp (continuous_besselI0.measurable.comp hm_L)).mul
        (continuous_poissonKernel x₀ hy₀_pos).measurable).aestronglyMeasurable
    refine hdom_int.mono' hmeas_K ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with σ hσ
    have hge := abs_slitBoundaryMap_ge_xiStar' hσ
    have hasy := log_besselK_asymptotic hc8 hge
    rw [← hK_eq σ hσ] at hasy
    have hbL_eq : besselL |slitBoundaryMap σ| = slitL (slitBoundaryMap σ) := by
      unfold besselL slitL; rfl
    rw [hbL_eq] at hasy
    have hslit_ge : u₀ ≤ slitL (slitBoundaryMap σ) := by
      dsimp [u₀]; unfold slitL; gcongr
    have hL_pos : 0 < slitL (slitBoundaryMap σ) := hu₀_pos.trans_le hslit_ge
    have hlogL_abs : |Real.log (slitL (slitBoundaryMap σ))| ≤
        |Real.log u₀| + slitL (slitBoundaryMap σ) := by
      have h1 : Real.log u₀ ≤ Real.log (slitL (slitBoundaryMap σ)) :=
        Real.log_le_log hu₀_pos hslit_ge
      have h2 : Real.log (slitL (slitBoundaryMap σ)) ≤ slitL (slitBoundaryMap σ) := by
        linarith [Real.log_le_sub_one_of_pos hL_pos]
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log u₀), (by unfold slitL; positivity : 0 ≤ slitL (slitBoundaryMap σ))]
      · linarith [abs_nonneg (Real.log u₀)]
    have hlogcL_abs : |Real.log (c' * slitL (slitBoundaryMap σ))| ≤
        |Real.log c'| + |Real.log u₀| + slitL (slitBoundaryMap σ) := by
      rw [Real.log_mul hc0.ne' hL_pos.ne']
      calc |Real.log c' + Real.log (slitL (slitBoundaryMap σ))|
          ≤ |Real.log c'| + |Real.log (slitBoundaryMap σ |> slitL)| := abs_add_le _ _
        _ ≤ |Real.log c'| + (|Real.log u₀| + slitL (slitBoundaryMap σ)) := by gcongr
        _ = _ := by ring
    have hlogK_bd : |Real.log (K_val σ)| ≤
        (c' + 1 / 2) * slitL (slitBoundaryMap σ) + Ck := by
      have h1 : |Real.log (K_val σ)| ≤
          |c' * slitL (slitBoundaryMap σ) - 1 / 2 * Real.log (c' * slitL (slitBoundaryMap σ))| + 4 := by
        linarith [abs_sub_abs_le_abs_sub (Real.log (K_val σ))
          (c' * slitL (slitBoundaryMap σ) - 1 / 2 * Real.log (c' * slitL (slitBoundaryMap σ)))]
      have h2 : |c' * slitL (slitBoundaryMap σ) - 1 / 2 * Real.log (c' * slitL (slitBoundaryMap σ))| ≤
          c' * slitL (slitBoundaryMap σ) + 1 / 2 * |Real.log (c' * slitL (slitBoundaryMap σ))| := by
        calc _ ≤ |c' * slitL (slitBoundaryMap σ)| + |1 / 2 * Real.log (c' * slitL (slitBoundaryMap σ))| :=
              abs_sub _ _
          _ = c' * slitL (slitBoundaryMap σ) + 1 / 2 * |Real.log (c' * slitL (slitBoundaryMap σ))| := by
              rw [abs_of_pos (mul_pos hc0 hL_pos), abs_mul, abs_of_pos (by norm_num)]
      dsimp [Ck]; linarith
    have hP0 := poissonKernel_nonneg (x := x₀) hy₀_pos.le σ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]
    calc |Real.log (K_val σ)| * poissonKernel x₀ y₀ σ
        ≤ ((c' + 1 / 2) * slitL (slitBoundaryMap σ) + Ck) * poissonKernel x₀ y₀ σ := by gcongr
      _ = dom σ := by dsimp [dom]; ring
  have hlogω_int : IntegrableOn
      (fun σ => Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) slitPreimage := by
    refine (integrableOn_poisson_mul_log_slitDensity x₀ hy₀_pos).congr_fun
      (fun σ _ => by dsimp only; ring) (measurableSet_Ioo.union measurableSet_Ioi)
  have hlogF_slit_int : IntegrableOn
      (fun σ => Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) slitPreimage :=
    hPJ_int.integrableOn
  have hlogf_eq_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x₀ y₀ σ =
        Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ -
          Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ +
          Real.log (K_val σ) * poissonKernel x₀ y₀ σ := by
    have hω_pos := slitDensity_pos_ae (x := x₀) hy₀_pos
    have hmem_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), σ ∈ slitPreimage :=
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)
    filter_upwards [hG_ne_ae, hω_pos, hmem_ae] with σ hG hω hσ
    rw [hf_eq_Fbdy σ hσ]
    have hF_pos : 0 < ‖F_bdy σ‖ := by
      dsimp [F_bdy]
      rw [hslit_confB σ hσ]
      exact norm_pos_iff.mpr (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hG)
    rw [Real.log_div (mul_pos hF_pos (hK_pos σ)).ne' hω.ne',
      Real.log_mul hF_pos.ne' (hK_pos σ).ne']
    ring
  have hlogf_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x₀ y₀ σ) slitPreimage := by
    refine ((hlogF_slit_int.sub hlogω_int).add hlogK_int).congr ?_
    filter_upwards [hlogf_eq_ae] with σ h
    exact h.symm
  have hjensen := log_integral_jensen_slitPreimage' hy₀_pos hf_pos_ae hf_pull_int hlogf_int
    (by positivity) (hf_pull_eq.le.trans hIφ_le)
  have hdecomp : ∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ) +
        (∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) -
        (∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ) := by
    have hFW_sub : IntegrableOn
        (fun σ => Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ -
          Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
      hlogF_slit_int.sub hlogω_int
    rw [integral_congr_ae hlogf_eq_ae, integral_add hFW_sub hlogK_int,
      integral_sub hlogF_slit_int hlogω_int]
    ring
  have hent_le : ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ ≤
      slitEntropy x₀ y₀ := by
    calc ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ
        = ∫ σ in slitPreimage, poissonKernel x₀ y₀ σ * Real.log (slitDensity x₀ y₀ σ) := by
          refine integral_congr_ae (Eventually.of_forall fun σ => by ring)
      _ ≤ slitEntropy x₀ y₀ := setIntegral_poisson_mul_log_slitDensity_le_entropy x₀ hy₀_pos
  have hlogK_lb : -(∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ) ≤
      c' * majorant2D (slitBoundaryMapC z) + (1 / 2 : ℝ) * m * Real.log c' +
        (1 / 2 : ℝ) * C_U + 4 := by
    have hident : IntegrableOn (fun σ => slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
      identification_integrand_integrable x₀ hy₀_pos
    have hpk_int : IntegrableOn (poissonKernel x₀ y₀) slitPreimage :=
      (integrable_poissonKernel x₀ hy₀_pos).integrableOn
    let rhs : ℝ → ℝ := fun σ =>
      c' * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) -
        (1 / 2 * Real.log c' + 4) * poissonKernel x₀ y₀ σ -
        (1 / 2 : ℝ) * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ)
    have hrhs_int : IntegrableOn rhs slitPreimage :=
      ((hident.const_mul c').sub (hpk_int.const_mul _)).sub (hident.const_mul _)
    have hpt : ∀ σ ∈ slitPreimage, rhs σ ≤ Real.log (K_val σ) * poissonKernel x₀ y₀ σ := by
      intro σ hσ
      have hge := abs_slitBoundaryMap_ge_xiStar' hσ
      have hasy := (abs_le.mp (log_besselK_asymptotic hc8 hge)).1
      rw [← hK_eq σ hσ] at hasy
      have hbL_eq : besselL |slitBoundaryMap σ| = slitL (slitBoundaryMap σ) := by
        unfold besselL slitL; rfl
      rw [hbL_eq] at hasy
      have hL_pos : 0 < slitL (slitBoundaryMap σ) := by
        unfold slitL; positivity [xiStar_pos.trans_le hge]
      have hlog_sub : Real.log (slitL (slitBoundaryMap σ)) ≤ slitL (slitBoundaryMap σ) := by
        linarith [Real.log_le_sub_one_of_pos hL_pos]
      have hlogcL : Real.log (c' * slitL (slitBoundaryMap σ)) ≤
          Real.log c' + slitL (slitBoundaryMap σ) := by
        rw [Real.log_mul hc0.ne' hL_pos.ne']; linarith
      have hK_low : c' * slitL (slitBoundaryMap σ) - (1 / 2 * Real.log c' + 4) -
          (1 / 2) * slitL (slitBoundaryMap σ) ≤ Real.log (K_val σ) := by
        linarith
      have hP0 := poissonKernel_nonneg (x := x₀) hy₀_pos.le σ
      calc rhs σ
          = (c' * slitL (slitBoundaryMap σ) - (1 / 2 * Real.log c' + 4) -
              (1 / 2) * slitL (slitBoundaryMap σ)) * poissonKernel x₀ y₀ σ := by
            dsimp [rhs]; ring
        _ ≤ Real.log (K_val σ) * poissonKernel x₀ y₀ σ := mul_le_mul_of_nonneg_right hK_low hP0
    have hmono := setIntegral_mono_on hrhs_int hlogK_int (measurableSet_Ioo.union measurableSet_Ioi) hpt
    have hrhs_eval : ∫ σ in slitPreimage, rhs σ =
        c' * (∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) -
          (1 / 2 * Real.log c' + 4) * m -
          (1 / 2 : ℝ) * (∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) := by
      dsimp [rhs]
      have h12 : IntegrableOn
          (fun σ => c' * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) -
            (1 / 2 * Real.log c' + 4) * poissonKernel x₀ y₀ σ) slitPreimage :=
        (hident.const_mul c').sub (hpk_int.const_mul _)
      rw [integral_sub h12 (hident.const_mul _),
        integral_sub (hident.const_mul c') (hpk_int.const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul]
      rfl
    rw [hrhs_eval] at hmono
    have hharm : -∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ =
        majorant2D (slitBoundaryMapC z) := by
      rw [hb_eq]
      exact (harmonicMajorantIdentification_complex hz_im).symm
    have hharm_eq : ∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ =
        -majorant2D (slitBoundaryMapC z) := by linarith
    rw [hharm_eq] at hmono
    have hU_abs : |majorant2D (slitBoundaryMapC z)| ≤ C_U := by
      rw [hb_eq]
      have hbd := majorant2D_abs_le (confB_mem_slitStrip hz_im)
      have hre := abs_confB_re_le_of_tip_ball hz_im hz_tip
      dsimp [C_U]
      calc |majorant2D (confB z)|
          ≤ |majorantU0| + (4 * π / 3) * (|(confB z).re| + 2) ^ 2 := hbd
        _ ≤ |majorantU0| + (4 * π / 3) * (Real.log 12 / (2 * π) + 2) ^ 2 := by gcongr
    have hneg_le : -majorant2D (slitBoundaryMapC z) ≤ C_U :=
      (neg_le_abs _).trans hU_abs
    have h4m : (4 : ℝ) * m ≤ 4 := by linarith [hm_le]
    linarith
  have hjensen_bd : ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ ≤
      max 0 (Real.log (2 * C_slit)) - m * Real.log c' + 1 := by
    have h1 : m * Real.log (2 * C_slit * c'⁻¹) =
        m * Real.log (2 * C_slit) - m * Real.log c' := by
      rw [Real.log_mul (by positivity) (inv_ne_zero hc0.ne'), Real.log_inv]
      ring
    have h2 : m * Real.log (2 * C_slit) ≤ max 0 (Real.log (2 * C_slit)) := by
      have := mul_le_mul_of_nonneg_left (le_max_right 0 (Real.log (2 * C_slit))) hm_pos.le
      calc m * Real.log (2 * C_slit)
          ≤ m * max 0 (Real.log (2 * C_slit)) := this
        _ ≤ 1 * max 0 (Real.log (2 * C_slit)) :=
            mul_le_mul_of_nonneg_right hm_le (le_max_left _ _)
        _ = max 0 (Real.log (2 * C_slit)) := one_mul _
    have h3 : 1 - m ≤ 1 := by linarith [hm_pos]
    linarith [hjensen, h1, h2, h3]
  have hedge_const : (1 - m) * Real.log (4 * π * Real.exp 92) ≤ Real.log (4 * π * Real.exp 92) := by
    have hge1 : 1 ≤ 4 * π * Real.exp 92 := by
      have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 92)
      have := Real.pi_gt_three
      nlinarith
    have hln_nn : 0 ≤ Real.log (4 * π * Real.exp 92) := Real.log_nonneg hge1
    calc (1 - m) * Real.log (4 * π * Real.exp 92)
        ≤ 1 * Real.log (4 * π * Real.exp 92) := mul_le_mul_of_nonneg_right (by linarith [hm_pos]) hln_nn
      _ = Real.log (4 * π * Real.exp 92) := one_mul _
  have hslit_le : ∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤
      c' * majorant2D (slitBoundaryMapC z) - (1 / 2 : ℝ) * m * Real.log c' + slitEntropy x₀ y₀ +
        (max 0 (Real.log (2 * C_slit)) + 1 + (1 / 2 : ℝ) * C_U + 4) := by
    linarith [hdecomp, hjensen_bd, hent_le, hlogK_lb]
  have hlogc_comb :
      2 * (1 - m) * Real.log c' - (1 / 2 : ℝ) * m * Real.log c' =
        -(1 / 2 : ℝ) * Real.log c' + (5 / 2 : ℝ) * (1 - m) * Real.log c' := by
    ring
  dsimp [C_PJ_complex, C_slit, C_U] at *
  linarith [hPJ_le, hsplit_eq, hedge_le, hedge_const, hslit_le, hlogc_comb]

/-- Canonical unconditional `StripBootstrapInputs` for the Virasoro modular bootstrap:
* `.pot = lemmaGPotentialInput_virasoro` (with `U = majorant2D`, `TipFront.ComplexMajorant`),
* `.pj`: real-`b` `PoissonJensenInput` (`PoissonJensen.stripPoissonJensen` + `Crossing.virasoro_Ka_ub`),
* `.fg`: `FixedGapInput` (`Crossing.lemmaGapInput_of_lemmaPJInput`),
* `.c_PJ_complex = 10000 ≥ 39`, `.C_PJ_complex = C_PJ_complex`. -/
noncomputable def virasoroStripBootstrapInputs : StripBootstrapInputs :=
  let hPJ_ex := PoissonJensen.stripPoissonJensen
  let c_PJ := hPJ_ex.choose
  let C_PJ := hPJ_ex.choose_spec.choose
  let hc_PJ : 1 ≤ c_PJ := hPJ_ex.choose_spec.choose_spec.1
  let hPJ : LemmaPJInput realSliceData c_PJ C_PJ majorantReal :=
    hPJ_ex.choose_spec.choose_spec.2
  let hfg := (Integration.lemmaGapInput_of_lemmaPJInput realSliceData majorantReal
    (c_PJ := c_PJ) (C_PJ := C_PJ) hc_PJ (fun _ hx => majorantReal_g_deficit hx) hPJ).choose
  { pot := lemmaGPotentialInput_virasoro
    pj :=
      { rs := realSliceData
        c_PJ := c_PJ
        C_PJ := C_PJ
        C_K := Real.sqrt (15 / 4)
        hc_PJ := hc_PJ
        hC_K := by positivity
        U := majorantReal
        g_deficit := fun _ hx => majorantReal_g_deficit hx }
    fg := hfg
    c_PJ_complex := c_PJ_complex
    hc_PJ_complex := by unfold c_PJ_complex; norm_num
    C_PJ_complex := C_PJ_complex }

/--
info: 'FormalResearch.ModularBootstrap.TipFront.stripPoissonJensen_complex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stripPoissonJensen_complex

/--
info: 'FormalResearch.ModularBootstrap.TipFront.virasoroStripBootstrapInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms virasoroStripBootstrapInputs

end FormalResearch.ModularBootstrap.TipFront
