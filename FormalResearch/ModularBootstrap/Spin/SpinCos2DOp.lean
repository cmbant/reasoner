module

public import FormalResearch.ModularBootstrap.Integrality.FourierConcentration
public import FormalResearch.ModularBootstrap.Integrality.HankelSonine

/-!
# Two-dimensional Fourier concentration and `A_R^{2D}` inverse (`int:cos2d-repair`)

`CFT/modular_bootstrap/paper/integrality_spin.tex`, Lemma INT-7C (`int:cos2d-repair`), operator part.

On `Q_R = [0, R]^2`, define the 2D tensor-cosine kernel
`K_{2D}(r, s) = 4 cos(2π r_L s_L) cos(2π r_R s_R)`
and the band operator `P_{Q_R} H_{2D} P_{Q_R}` on `L^2(Q_R, dr_L dr_R)`. Extending a continuous
1D profile evenly to `[-R, R]` and applying `Integrality.fourier_concentration_1d` in each
coordinate sequentially yields
`‖P_{Q_R} H_{2D} P_{Q_R}‖ ≤ 1 - cos2DGap R`,
so `A_R^{2D} := I + P_{Q_R} H_{2D} P_{Q_R}` is invertible on `L^2(Q_R)` with
`‖(A_R^{2D})⁻¹‖ ≤ max 2 (256 π^2 R^4 exp(8π R^2))` (`(int:AR2d-inv)`).
-/

@[expose] public section

open MeasureTheory Set Filter Real
open scoped FourierTransform Topology

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap.Integrality

/-! ### Section 1: 1D even cosine concentration from `fourier_concentration_1d` -/

/-- The 1D/2D Fourier concentration gap at radius `R > 0`:
`ε_R = min(1/2, (256 π^2 R^4 exp(8π R^2))⁻¹)`. -/
noncomputable def cos2DGap (R : ℝ) : ℝ :=
  min (1 / 2 : ℝ) (1 / (256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2)))

lemma cos2DGap_pos {R : ℝ} (hR : 0 < R) : 0 < cos2DGap R := by
  unfold cos2DGap
  exact lt_min (by norm_num) (by positivity)

lemma cos2DGap_le_half (R : ℝ) : cos2DGap R ≤ 1 / 2 :=
  min_le_left _ _

/-- Splitting a symmetric interval integral `∫ x in Icc (-R) R, f x` into `Icc 0 R`. -/
lemma setIntegral_Icc_neg_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) {f : ℝ → E} (hf : IntegrableOn f (Icc (-R) R) volume) :
    ∫ x in Icc (-R) R, f x = ∫ s in Icc (0 : ℝ) R, (f s + f (-s)) := by
  have h1 : ∫ x in Icc (-R) R, f x = ∫ x in Ioc (-R) R, f x := integral_Icc_eq_integral_Ioc
  have hunion : Ioc (-R) R = Ioc (-R) 0 ∪ Ioc 0 R :=
    (Ioc_union_Ioc_eq_Ioc (neg_nonpos.mpr hR) hR).symm
  have hdisj : Disjoint (Ioc (-R) 0) (Ioc 0 R) := Ioc_disjoint_Ioc_of_le le_rfl
  have hf_ioc : IntegrableOn f (Ioc (-R) R) volume := by
    rwa [IntegrableOn, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hf_left : IntegrableOn f (Ioc (-R) 0) volume :=
    hf_ioc.mono_set (by rw [hunion]; exact subset_union_left)
  have hf_right : IntegrableOn f (Ioc (0 : ℝ) R) volume :=
    hf_ioc.mono_set (by rw [hunion]; exact subset_union_right)
  rw [h1, hunion, setIntegral_union hdisj measurableSet_Ioc hf_left hf_right]
  have hpre : Neg.neg ⁻¹' (Ioc (-R) (0 : ℝ)) = Ico (0 : ℝ) R := by
    ext s; simp only [mem_preimage, mem_Ioc, mem_Ico]; constructor <;> intro ⟨h1, h2⟩ <;>
      exact ⟨by linarith, by linarith⟩
  have hneg_eq : ∫ x in Ioc (-R) (0 : ℝ), f x = ∫ s in Icc (0 : ℝ) R, f (-s) := by
    have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg volume
    have heq := hmp.setIntegral_preimage_emb (Homeomorph.neg ℝ).measurableEmbedding f (Ioc (-R) 0)
    rw [hpre] at heq
    have hae : volume.restrict (Ico (0 : ℝ) R) = volume.restrict (Icc (0 : ℝ) R) :=
      Measure.restrict_congr_set Ico_ae_eq_Icc
    rw [← heq, hae]
  have hf_neg_int : IntegrableOn (fun s => f (-s)) (Icc (0 : ℝ) R) volume := by
    have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg volume
    have h1 : IntegrableOn (f ∘ Neg.neg) (Ico (0 : ℝ) R) volume := by
      rw [← hpre]
      exact (hmp.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding).mpr hf_left
    change IntegrableOn (fun s => f (-s)) (Ico (0 : ℝ) R) volume at h1
    simpa [IntegrableOn, Measure.restrict_congr_set Ico_ae_eq_Icc] using h1
  have hf_right' : IntegrableOn f (Icc (0 : ℝ) R) volume := by
    simpa [IntegrableOn, Measure.restrict_congr_set Ioc_ae_eq_Icc] using hf_right
  rw [hneg_eq, ← integral_Icc_eq_integral_Ioc (f := f), add_comm,
    ← integral_add hf_right' hf_neg_int]

/-- Even extension of `u : ℝ → ℝ` on `[0, R]` to `ℝ → ℂ` vanishing outside `[-R, R]`. -/
noncomputable def evenExt1D (R : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℂ :=
  (Icc (-R) R).indicator (fun t => ((u |t| : ℝ) : ℂ)) x

lemma aestronglyMeasurable_evenExt1D {R : ℝ} {u : ℝ → ℝ} (hu : Continuous u) :
    AEStronglyMeasurable (evenExt1D R u) volume := by
  have hc : Continuous (fun t : ℝ => ((u |t| : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hu.comp continuous_abs)
  exact hc.aestronglyMeasurable.indicator measurableSet_Icc

lemma memLp_evenExt1D {R : ℝ} {u : ℝ → ℝ} (hu : Continuous u) :
    MemLp (evenExt1D R u) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_evenExt1D (R := R) hu)).mpr ?_
  have heq : (fun x : ℝ => ‖evenExt1D R u x‖ ^ 2) =
      (Icc (-R) R).indicator (fun t => (u |t|) ^ 2) := by
    ext x
    by_cases hx : x ∈ Icc (-R) R
    · simp [evenExt1D, hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · simp [evenExt1D, hx]
  rw [heq, integrable_indicator_iff measurableSet_Icc]
  have hc : Continuous (fun t : ℝ => (u |t|) ^ 2) := (hu.comp continuous_abs).pow 2
  exact hc.continuousOn.integrableOn_Icc

lemma fourier_evenExt1D {R : ℝ} (hR : 0 ≤ R) {u : ℝ → ℝ} (hu : Continuous u) (r : ℝ) :
    𝓕 (evenExt1D R u) r =
      ((2 * ∫ s in Icc (0 : ℝ) R, Real.cos (2 * π * r * s) * u s : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  have heq1 : (fun x : ℝ => Complex.exp (↑(-2 * π * inner ℝ x r) * Complex.I) • evenExt1D R u x) =
      (Icc (-R) R).indicator (fun x =>
        Complex.exp (-(2 * π * r * x : ℝ) * Complex.I) * ((u |x| : ℝ) : ℂ)) := by
    ext x
    by_cases hx : x ∈ Icc (-R) R
    · simp only [evenExt1D, Set.indicator_of_mem hx, smul_eq_mul, RCLike.inner_apply, conj_trivial]
      congr 2; push_cast; ring
    · simp only [evenExt1D, Set.indicator_of_notMem hx, smul_zero]
  rw [heq1, integral_indicator measurableSet_Icc]
  have hint : IntegrableOn (fun x : ℝ =>
      Complex.exp (-(2 * π * r * x : ℝ) * Complex.I) * ((u |x| : ℝ) : ℂ)) (Icc (-R) R) volume := by
    refine Continuous.continuousOn ?_ |>.integrableOn_Icc
    exact (Complex.continuous_exp.comp (by fun_prop)).mul
      (Complex.continuous_ofReal.comp (hu.comp continuous_abs))
  rw [setIntegral_Icc_neg_self hR hint]
  have hcos : ∫ s in Icc (0 : ℝ) R,
      (Complex.exp (-(2 * π * r * s : ℝ) * Complex.I) * ((u |s| : ℝ) : ℂ) +
        Complex.exp (-(2 * π * r * (-s) : ℝ) * Complex.I) * ((u |(-s)| : ℝ) : ℂ)) =
      ∫ s in Icc (0 : ℝ) R, ((2 * (Real.cos (2 * π * r * s) * u s) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    rw [abs_neg, abs_of_nonneg hs.1]
    have hsum : Complex.exp (-(2 * π * r * s : ℝ) * Complex.I) +
        Complex.exp (-(2 * π * r * (-s) : ℝ) * Complex.I) =
        ((2 * Real.cos (2 * π * r * s) : ℝ) : ℂ) := by
      have h1 : Complex.exp (-(2 * π * r * (-s) : ℝ) * Complex.I) =
          Complex.exp (((2 * π * r * s : ℝ) : ℂ) * Complex.I) := by
        congr 1; push_cast; ring
      have h2 : Complex.exp (-(2 * π * r * s : ℝ) * Complex.I) =
          Complex.exp (-(((2 * π * r * s : ℝ) : ℂ) * Complex.I)) := by
        congr 1; push_cast; ring
      rw [h1, h2, add_comm]
      calc Complex.exp (((2 * π * r * s : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((2 * π * r * s : ℝ) : ℂ) * Complex.I))
          = 2 * Complex.cos ((2 * π * r * s : ℝ) : ℂ) := by
            rw [Complex.cos]; ring
        _ = ((2 * Real.cos (2 * π * r * s) : ℝ) : ℂ) := by
            simp [Complex.ofReal_cos]
    calc Complex.exp (-(2 * π * r * s : ℝ) * Complex.I) * ((u s : ℝ) : ℂ) +
          Complex.exp (-(2 * π * r * (-s) : ℝ) * Complex.I) * ((u s : ℝ) : ℂ)
        = (Complex.exp (-(2 * π * r * s : ℝ) * Complex.I) +
            Complex.exp (-(2 * π * r * (-s) : ℝ) * Complex.I)) * ((u s : ℝ) : ℂ) := by ring
      _ = ((2 * Real.cos (2 * π * r * s) : ℝ) : ℂ) * ((u s : ℝ) : ℂ) := by rw [hsum]
      _ = ((2 * (Real.cos (2 * π * r * s) * u s) : ℝ) : ℂ) := by push_cast; ring
  calc ∫ s in Icc (0 : ℝ) R,
        (Complex.exp (-(2 * π * r * s : ℝ) * Complex.I) * ((u |s| : ℝ) : ℂ) +
          Complex.exp (-(2 * π * r * (-s) : ℝ) * Complex.I) * ((u |(-s)| : ℝ) : ℂ))
      = ∫ s in Icc (0 : ℝ) R, ((2 * (Real.cos (2 * π * r * s) * u s) : ℝ) : ℂ) := hcos
    _ = ((∫ s in Icc (0 : ℝ) R, 2 * (Real.cos (2 * π * r * s) * u s) : ℝ) : ℂ) :=
        integral_ofReal
    _ = ((2 * ∫ s in Icc (0 : ℝ) R, Real.cos (2 * π * r * s) * u s : ℝ) : ℂ) := by
        rw [integral_const_mul]

/-- 1D cosine-band energy inequality on `[0, R]`:
`∫_0^R (2 ∫_0^R cos(2π r s) u(s) ds)^2 dr ≤ (1 - cos2DGap R) ∫_0^R u(s)^2 ds`. -/
lemma cosTransform1D_band_sq_le {R : ℝ} (hR : 0 < R) {u : ℝ → ℝ} (hu : Continuous u) :
    ∫ r in Icc (0 : ℝ) R, (2 * ∫ s in Icc (0 : ℝ) R, Real.cos (2 * π * r * s) * u s) ^ 2 ≤
      (1 - cos2DGap R) * ∫ s in Icc (0 : ℝ) R, (u s) ^ 2 := by
  have hconc := fourier_concentration_1d hR (aestronglyMeasurable_evenExt1D (R := R) hu)
    (memLp_evenExt1D (R := R) hu)
    (fun x hx => by
      have hn : x ∉ Icc (-R) R := by
        intro hmem; exact absurd (abs_le.mpr hmem) (not_le.mpr hx)
      exact Set.indicator_of_notMem hn _)
  set C : ℝ → ℝ := fun r => 2 * ∫ s in Icc (0 : ℝ) R, Real.cos (2 * π * r * s) * u s
  have hC_cont : Continuous C := by
    refine Continuous.const_mul ?_ 2
    rw [continuous_iff_continuousAt]
    intro r₀
    have hint_u : IntegrableOn u (Icc 0 R) volume := hu.continuousOn.integrableOn_Icc
    refine tendsto_integral_filter_of_dominated_convergence (fun s => |u s|) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun r =>
        ((Real.continuous_cos.comp (by fun_prop)).mul hu).aestronglyMeasurable
    · refine Eventually.of_forall fun r => ae_restrict_mem measurableSet_Icc |>.mono fun s _ => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
    · exact hint_u.abs
    · exact Eventually.of_forall fun s =>
        ((Real.continuous_cos.comp (by fun_prop)).continuousAt.mul continuousAt_const)
  have hlhs_eq : ∫ r in Icc (-R) R, ‖𝓕 (evenExt1D R u) r‖ ^ 2 =
      2 * ∫ r in Icc (0 : ℝ) R, (C r) ^ 2 := by
    have heq_f : ∀ r : ℝ, ‖𝓕 (evenExt1D R u) r‖ ^ 2 = (C r) ^ 2 := fun r => by
      rw [fourier_evenExt1D hR.le hu r, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp_rw [heq_f]
    rw [setIntegral_Icc_neg_self hR.le (f := fun r => (C r) ^ 2) ((hC_cont.pow 2).continuousOn.integrableOn_Icc)]
    have heven : ∀ s : ℝ, (C (-s)) ^ 2 = (C s) ^ 2 := fun s => by
      have : C (-s) = C s := by
        dsimp [C]; congr 1
        refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
        rw [show 2 * π * -s * t = -(2 * π * s * t) by ring, Real.cos_neg]
      rw [this]
    simp_rw [heven, ← two_mul, integral_const_mul]
  have hrhs_eq : ∫ x : ℝ, ‖evenExt1D R u x‖ ^ 2 = 2 * ∫ s in Icc (0 : ℝ) R, (u s) ^ 2 := by
    have heq_x : (fun x : ℝ => ‖evenExt1D R u x‖ ^ 2) =
        (Icc (-R) R).indicator (fun t => (u |t|) ^ 2) := by
      ext x
      by_cases hx : x ∈ Icc (-R) R
      · simp [evenExt1D, hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      · simp [evenExt1D, hx]
    rw [heq_x, integral_indicator measurableSet_Icc,
      setIntegral_Icc_neg_self hR.le (f := fun t => (u |t|) ^ 2)
        (((hu.comp continuous_abs).pow 2).continuousOn.integrableOn_Icc)]
    have heq_pos : ∫ s in Icc (0 : ℝ) R, ((u |s|) ^ 2 + (u |(-s)|) ^ 2) =
        ∫ s in Icc (0 : ℝ) R, 2 * (u s) ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      rw [abs_neg, abs_of_nonneg hs.1]; ring
    rw [heq_pos, integral_const_mul]
  rw [hlhs_eq, hrhs_eq] at hconc
  change 2 * ∫ r in Icc (0 : ℝ) R, (C r) ^ 2 ≤
    (1 - cos2DGap R) * (2 * ∫ s in Icc (0 : ℝ) R, (u s) ^ 2) at hconc
  linarith

/-! ### Section 2: 2D cosine kernel, band measure, and operator norm `‖cos2DBandOp R‖ ≤ 1 - cos2DGap R` -/

/-- The 2D tensor-cosine kernel `4 cos(2π r_L s_L) cos(2π r_R s_R)`. -/
noncomputable def cos2DKernel (r s : ℝ × ℝ) : ℝ :=
  4 * Real.cos (2 * π * r.1 * s.1) * Real.cos (2 * π * r.2 * s.2)

lemma continuous_cos2DKernel : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) => cos2DKernel p.1 p.2) := by
  unfold cos2DKernel
  fun_prop

lemma cos2DKernel_symm (r s : ℝ × ℝ) : cos2DKernel r s = cos2DKernel s r := by
  unfold cos2DKernel
  rw [show 2 * π * r.1 * s.1 = 2 * π * s.1 * r.1 by ring,
    show 2 * π * r.2 * s.2 = 2 * π * s.2 * r.2 by ring]

lemma abs_cos2DKernel_le (r s : ℝ × ℝ) : |cos2DKernel r s| ≤ 4 := by
  unfold cos2DKernel
  calc |4 * Real.cos (2 * π * r.1 * s.1) * Real.cos (2 * π * r.2 * s.2)|
      = 4 * |Real.cos (2 * π * r.1 * s.1)| * |Real.cos (2 * π * r.2 * s.2)| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num)]
    _ ≤ 4 * 1 * 1 := by gcongr <;> exact Real.abs_cos_le_one _
    _ = 4 := by norm_num

/-- The square `Q_R = [0, R]^2 ⊂ ℝ × ℝ`. -/
def cos2DBandSet (R : ℝ) : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R

lemma measurableSet_cos2DBandSet (R : ℝ) : MeasurableSet (cos2DBandSet R) :=
  measurableSet_Icc.prod measurableSet_Icc

lemma isCompact_cos2DBandSet (R : ℝ) : IsCompact (cos2DBandSet R) :=
  isCompact_Icc.prod isCompact_Icc

/-- Lebesgue measure restricted to `Q_R = [0, R]^2`. -/
noncomputable def cos2DBandMeasure (R : ℝ) : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).restrict (cos2DBandSet R)

lemma volume_cos2DBandSet_lt_top (R : ℝ) : volume (cos2DBandSet R) < ⊤ := by
  rw [cos2DBandSet, Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (by simp [Real.volume_Icc]) (by simp [Real.volume_Icc])

instance isFiniteMeasure_cos2DBandMeasure (R : ℝ) : IsFiniteMeasure (cos2DBandMeasure R) :=
  isFiniteMeasure_restrict.mpr (volume_cos2DBandSet_lt_top R).ne

lemma volume_real_cos2DBandSet (R : ℝ) :
    volume.real (cos2DBandSet R) = (cos2DBandMeasure R).real univ := by
  rw [Measure.real, Measure.real, cos2DBandMeasure, Measure.restrict_apply MeasurableSet.univ, univ_inter]

lemma cos2DBandMeasure_real_univ {R : ℝ} (hR : 0 ≤ R) :
    (cos2DBandMeasure R).real univ = R ^ 2 := by
  rw [Measure.real, cos2DBandMeasure, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    cos2DBandSet, Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

lemma memLp_cos2DBandMeasure_of_continuous {R : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (cos2DBandMeasure R) := by
  refine (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr ?_
  exact (hf.pow 2).continuousOn.integrableOn_compact (isCompact_cos2DBandSet R)

lemma lp_norm_sq_cos2DBandMeasure {R : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 (cos2DBandMeasure R)) :
    ‖hf.toLp f‖ ^ 2 = ∫ p in cos2DBandSet R, (f p) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  have heq : (fun p => inner ℝ ((hf.toLp f : ℝ × ℝ → ℝ) p) ((hf.toLp f : ℝ × ℝ → ℝ) p)) =ᵐ[cos2DBandMeasure R]
      fun p => (f p) ^ 2 := by
    filter_upwards [hf.coeFn_toLp] with p hp
    rw [hp, RCLike.inner_apply, conj_trivial, sq]
  exact integral_congr_ae heq

/-- Raw 2D cosine integral operator on `Q_R`. -/
noncomputable def rawCos2DOp (R : ℝ) (f : ℝ × ℝ → ℝ) (r : ℝ × ℝ) : ℝ :=
  ∫ s, cos2DKernel r s * f s ∂(cos2DBandMeasure R)

lemma continuous_rawCos2DOp {R : ℝ} (f : Lp ℝ 2 (cos2DBandMeasure R)) :
    Continuous (rawCos2DOp R f) := by
  rw [continuous_iff_continuousAt]
  intro r₀
  have hf1 : Integrable (fun s => (f : ℝ × ℝ → ℝ) s) (cos2DBandMeasure R) :=
    (Lp.memLp f).integrable one_le_two
  refine tendsto_integral_filter_of_dominated_convergence (fun s => 4 * ‖(f : ℝ × ℝ → ℝ) s‖) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun r =>
      ((continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f))
  · refine Eventually.of_forall fun r => Eventually.of_forall fun s => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_cos2DKernel_le r s) (norm_nonneg _)
  · exact hf1.norm.const_mul 4
  · exact Eventually.of_forall fun s =>
      ((continuous_cos2DKernel.comp (continuous_id.prodMk continuous_const)).continuousAt.mul
        continuousAt_const)

lemma rawCos2DOp_sq_le {R : ℝ} (hR : 0 ≤ R) (f : Lp ℝ 2 (cos2DBandMeasure R)) (r : ℝ × ℝ) :
    (rawCos2DOp R f r) ^ 2 ≤ 16 * R ^ 2 * ‖f‖ ^ 2 := by
  have hg_mem : MemLp (fun s => cos2DKernel r s) 2 (cos2DBandMeasure R) :=
    memLp_cos2DBandMeasure_of_continuous (continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id))
  let g : Lp ℝ 2 (cos2DBandMeasure R) := hg_mem.toLp _
  have hinner : rawCos2DOp R f r = inner ℝ g f := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg_mem.coeFn_toLp] with s hs
    rw [hs, real_inner_comm]
    rfl
  have hg_sq : ‖g‖ ^ 2 ≤ 16 * R ^ 2 := by
    rw [lp_norm_sq_cos2DBandMeasure hg_mem]
    have hconst_int : IntegrableOn (fun _ : ℝ × ℝ => (16 : ℝ)) (cos2DBandSet R) volume :=
      integrableOn_const (hs := (volume_cos2DBandSet_lt_top R).ne)
    have hker_int : IntegrableOn (fun s => (cos2DKernel r s) ^ 2) (cos2DBandSet R) volume :=
      ((continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).pow 2).continuousOn.integrableOn_compact
        (isCompact_cos2DBandSet R)
    calc ∫ s in cos2DBandSet R, (cos2DKernel r s) ^ 2
        ≤ ∫ _s in cos2DBandSet R, (16 : ℝ) :=
          setIntegral_mono_on hker_int hconst_int (measurableSet_cos2DBandSet R) fun s _ => by
            calc (cos2DKernel r s) ^ 2 = |cos2DKernel r s| ^ 2 := (sq_abs _).symm
              _ ≤ 4 ^ 2 := by gcongr; exact abs_cos2DKernel_le r s
              _ = 16 := by norm_num
      _ = (cos2DBandMeasure R).real univ * 16 := by
          rw [setIntegral_const, smul_eq_mul, mul_comm, volume_real_cos2DBandSet]; ring
      _ = 16 * R ^ 2 := by rw [cos2DBandMeasure_real_univ hR]; ring
  have hcs := norm_inner_le_norm (𝕜 := ℝ) g f
  rw [hinner]
  calc (inner ℝ g f) ^ 2 = ‖inner ℝ g f‖ ^ 2 := (sq_abs _).symm
    _ ≤ (‖g‖ * ‖f‖) ^ 2 := by gcongr
    _ = ‖g‖ ^ 2 * ‖f‖ ^ 2 := by ring
    _ ≤ (16 * R ^ 2) * ‖f‖ ^ 2 := by gcongr

lemma rawCos2DOp_memLp {R : ℝ} (f : Lp ℝ 2 (cos2DBandMeasure R)) :
    MemLp (rawCos2DOp R f) 2 (cos2DBandMeasure R) :=
  memLp_cos2DBandMeasure_of_continuous (continuous_rawCos2DOp f)

/-- The bounded linear operator `P_{Q_R} H_{2D} P_{Q_R}` on `L^2(Q_R)`. -/
noncomputable def cos2DBandOp {R : ℝ} (hR : 0 ≤ R) :
    Lp ℝ 2 (cos2DBandMeasure R) →L[ℝ] Lp ℝ 2 (cos2DBandMeasure R) :=
  LinearMap.mkContinuous
    { toFun := fun f => (rawCos2DOp_memLp f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add (rawCos2DOp_memLp f) (rawCos2DOp_memLp g)]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun r => ?_)
        unfold rawCos2DOp
        have hf1 : Integrable (fun s => (f : ℝ × ℝ → ℝ) s) (cos2DBandMeasure R) :=
          (Lp.memLp f).integrable one_le_two
        have hg1 : Integrable (fun s => (g : ℝ × ℝ → ℝ) s) (cos2DBandMeasure R) :=
          (Lp.memLp g).integrable one_le_two
        have hint_f : Integrable (fun s => cos2DKernel r s * (f : ℝ × ℝ → ℝ) s) (cos2DBandMeasure R) :=
          (hf1.norm.const_mul 4).mono'
            ((continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
              (Lp.aestronglyMeasurable f))
            (Eventually.of_forall fun s => by
              rw [norm_mul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right (abs_cos2DKernel_le r s) (norm_nonneg _))
        have hint_g : Integrable (fun s => cos2DKernel r s * (g : ℝ × ℝ → ℝ) s) (cos2DBandMeasure R) :=
          (hg1.norm.const_mul 4).mono'
            ((continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
              (Lp.aestronglyMeasurable g))
            (Eventually.of_forall fun s => by
              rw [norm_mul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right (abs_cos2DKernel_le r s) (norm_nonneg _))
        have heq_f : (fun s => cos2DKernel r s * ((f + g : Lp ℝ 2 (cos2DBandMeasure R)) : ℝ × ℝ → ℝ) s) =ᵐ[cos2DBandMeasure R]
            fun s => cos2DKernel r s * (f : ℝ × ℝ → ℝ) s + cos2DKernel r s * (g : ℝ × ℝ → ℝ) s := by
          filter_upwards [Lp.coeFn_add f g] with s hs
          simp only [hs, Pi.add_apply, mul_add]
        rw [integral_congr_ae heq_f, integral_add hint_f hint_g]; rfl
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (rawCos2DOp_memLp f)]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun r => ?_)
        unfold rawCos2DOp
        have heq_c : (fun s => cos2DKernel r s * ((c • f : Lp ℝ 2 (cos2DBandMeasure R)) : ℝ × ℝ → ℝ) s) =ᵐ[cos2DBandMeasure R]
            fun s => c * (cos2DKernel r s * (f : ℝ × ℝ → ℝ) s) := by
          filter_upwards [Lp.coeFn_smul c f] with s hs
          simp only [hs, Pi.smul_apply, smul_eq_mul]; ring
        rw [integral_congr_ae heq_c, integral_const_mul]; rfl }
    (4 * R ^ 2)
    fun f => by
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity)]
      change ‖(rawCos2DOp_memLp f).toLp _‖ ^ 2 ≤ (4 * R ^ 2 * ‖f‖) ^ 2
      rw [lp_norm_sq_cos2DBandMeasure (rawCos2DOp_memLp f)]
      have hconst_int : IntegrableOn (fun _ : ℝ × ℝ => 16 * R ^ 2 * ‖f‖ ^ 2) (cos2DBandSet R) volume :=
        integrableOn_const (hs := (volume_cos2DBandSet_lt_top R).ne)
      have hlhs_int : IntegrableOn (fun r => (rawCos2DOp R f r) ^ 2) (cos2DBandSet R) volume :=
        ((continuous_rawCos2DOp f).pow 2).continuousOn.integrableOn_compact (isCompact_cos2DBandSet R)
      calc ∫ r in cos2DBandSet R, (rawCos2DOp R f r) ^ 2
          ≤ ∫ _r in cos2DBandSet R, 16 * R ^ 2 * ‖f‖ ^ 2 :=
            setIntegral_mono_on hlhs_int hconst_int (measurableSet_cos2DBandSet R)
              fun r _ => rawCos2DOp_sq_le hR f r
        _ = (cos2DBandMeasure R).real univ * (16 * R ^ 2 * ‖f‖ ^ 2) := by
            rw [setIntegral_const, smul_eq_mul, mul_comm, volume_real_cos2DBandSet]; ring
        _ = R ^ 2 * (16 * R ^ 2 * ‖f‖ ^ 2) := by rw [cos2DBandMeasure_real_univ hR]
        _ = (4 * R ^ 2 * ‖f‖) ^ 2 := by ring

lemma cos2DBandOp_apply_ae {R : ℝ} (hR : 0 ≤ R) (f : Lp ℝ 2 (cos2DBandMeasure R)) :
    ∀ᵐ r ∂(cos2DBandMeasure R),
      (cos2DBandOp hR f : ℝ × ℝ → ℝ) r =
        ∫ s, cos2DKernel r s * (f : ℝ × ℝ → ℝ) s ∂(cos2DBandMeasure R) :=
  (rawCos2DOp_memLp f).coeFn_toLp

/-- **Operator norm bound**: `‖P_{Q_R} H_{2D} P_{Q_R}‖ ≤ 1 - cos2DGap R` (`0 < R`),
proved by two sequential applications of 1D Fourier concentration `cosTransform1D_band_sq_le`. -/
lemma cos2DBandOp_norm_le {R : ℝ} (hR : 0 < R) :
    ‖cos2DBandOp hR.le‖ ≤ 1 - cos2DGap R := by
  have h1gap_nn : 0 ≤ 1 - cos2DGap R := by linarith [cos2DGap_le_half R]
  refine ContinuousLinearMap.opNorm_le_bound _ h1gap_nn fun f => ?_
  have h_bcf : ∀ g : BoundedContinuousFunction (ℝ × ℝ) ℝ,
      ∀ (hg_mem : MemLp (g : ℝ × ℝ → ℝ) 2 (cos2DBandMeasure R)),
      ‖cos2DBandOp hR.le (hg_mem.toLp _)‖ ≤ (1 - cos2DGap R) * ‖hg_mem.toLp _‖ := by
    intro g hg_mem
    let ψ : ℝ → ℝ → ℝ := fun sL rR =>
      2 * ∫ sR in Icc (0 : ℝ) R, Real.cos (2 * π * rR * sR) * g (sL, sR)
    have hψ_cont : Continuous (Function.uncurry ψ) := by
      refine Continuous.const_mul ?_ 2
      rw [continuous_iff_continuousAt]
      intro ⟨sL₀, rR₀⟩
      have hconst_int : IntegrableOn (fun _ : ℝ => ‖g‖) (Icc (0 : ℝ) R) volume :=
        integrableOn_const (hs := by simp [Real.volume_Icc])
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun p =>
          ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
            (g.continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
      · exact Eventually.of_forall fun p => ae_restrict_mem measurableSet_Icc |>.mono fun sR _ => by
          rw [Real.norm_eq_abs, abs_mul]
          exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans
            (g.norm_coe_le_norm (p.1, sR))
      · exact hconst_int
      · exact Eventually.of_forall fun sR =>
          ((Real.continuous_cos.comp
            ((continuous_const.mul continuous_snd).mul continuous_const)).continuousAt.mul
            (g.continuous.continuousAt.comp (continuousAt_fst.prodMk continuousAt_const)))
    have h_prod_int : ∀ {h : ℝ × ℝ → ℝ}, Continuous h →
        Integrable h ((volume.restrict (Icc (0 : ℝ) R)).prod (volume.restrict (Icc (0 : ℝ) R))) := by
      intro h hh
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hh.continuousOn.integrableOn_compact (isCompact_cos2DBandSet R)
    have hraw_eq : ∀ rL rR : ℝ, rawCos2DOp R (hg_mem.toLp g) (rL, rR) =
        2 * ∫ sL in Icc (0 : ℝ) R, Real.cos (2 * π * rL * sL) * ψ sL rR := by
      intro rL rR
      unfold rawCos2DOp
      have hae : (fun s => cos2DKernel (rL, rR) s * ((hg_mem.toLp g : ℝ × ℝ → ℝ) s)) =ᵐ[cos2DBandMeasure R]
          fun s => cos2DKernel (rL, rR) s * g s := by
        filter_upwards [hg_mem.coeFn_toLp] with s hs; rw [hs]
      rw [integral_congr_ae hae]
      change ∫ s in cos2DBandSet R, cos2DKernel (rL, rR) s * g s = _
      have hint2 : Integrable (fun s => cos2DKernel (rL, rR) s * g s)
          ((volume.restrict (Icc (0 : ℝ) R)).prod (volume.restrict (Icc (0 : ℝ) R))) :=
        h_prod_int ((continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).mul g.continuous)
      rw [cos2DBandSet, Measure.volume_eq_prod, ← Measure.prod_restrict]
      change ∫ s, cos2DKernel (rL, rR) s * g s ∂((volume.restrict (Icc 0 R)).prod (volume.restrict (Icc 0 R))) = _
      rw [integral_prod _ hint2]
      calc ∫ sL in Icc (0 : ℝ) R, ∫ sR in Icc (0 : ℝ) R, cos2DKernel (rL, rR) (sL, sR) * g (sL, sR)
          = ∫ sL in Icc (0 : ℝ) R,
              (Real.cos (2 * π * rL * sL) * 4) * ∫ sR in Icc (0 : ℝ) R, Real.cos (2 * π * rR * sR) * g (sL, sR) := by
            refine setIntegral_congr_fun measurableSet_Icc fun sL _ => ?_
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Icc fun sR _ => ?_
            unfold cos2DKernel; ring
        _ = 2 * ∫ sL in Icc (0 : ℝ) R, Real.cos (2 * π * rL * sL) * ψ sL rR := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Icc fun sL _ => by dsimp [ψ]; ring
    have hint_raw2 := h_prod_int ((continuous_rawCos2DOp (hg_mem.toLp g)).pow 2)
    have hint_ψ2 := h_prod_int (hψ_cont.pow 2)
    have hint_ψ2_swap : Integrable (Function.uncurry fun rR sL => (ψ sL rR) ^ 2)
        ((volume.restrict (Icc (0 : ℝ) R)).prod (volume.restrict (Icc (0 : ℝ) R))) :=
      h_prod_int ((hψ_cont.comp continuous_swap).pow 2)
    have hint_g2 := h_prod_int (g.continuous.pow 2)
    have hlhs : ‖cos2DBandOp hR.le (hg_mem.toLp g)‖ ^ 2 =
        ∫ rR in Icc (0 : ℝ) R, ∫ rL in Icc (0 : ℝ) R, (rawCos2DOp R (hg_mem.toLp g) (rL, rR)) ^ 2 := by
      change ‖(rawCos2DOp_memLp (hg_mem.toLp g)).toLp _‖ ^ 2 = _
      rw [lp_norm_sq_cos2DBandMeasure (rawCos2DOp_memLp (hg_mem.toLp g)), cos2DBandSet,
        Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact integral_prod_symm _ hint_raw2
    have hrhs : ‖hg_mem.toLp g‖ ^ 2 =
        ∫ sL in Icc (0 : ℝ) R, ∫ sR in Icc (0 : ℝ) R, (g (sL, sR)) ^ 2 := by
      rw [lp_norm_sq_cos2DBandMeasure hg_mem, cos2DBandSet, Measure.volume_eq_prod,
        ← Measure.prod_restrict]
      exact integral_prod _ hint_g2
    have hstep1 : ∀ rR : ℝ,
        ∫ rL in Icc (0 : ℝ) R, (rawCos2DOp R (hg_mem.toLp g) (rL, rR)) ^ 2 ≤
          (1 - cos2DGap R) * ∫ sL in Icc (0 : ℝ) R, (ψ sL rR) ^ 2 := fun rR => by
      simp_rw [hraw_eq _ rR]
      exact cosTransform1D_band_sq_le hR (hψ_cont.comp (continuous_id.prodMk continuous_const))
    have hstep2 : ∀ sL : ℝ,
        ∫ rR in Icc (0 : ℝ) R, (ψ sL rR) ^ 2 ≤
          (1 - cos2DGap R) * ∫ sR in Icc (0 : ℝ) R, (g (sL, sR)) ^ 2 := fun sL =>
      cosTransform1D_band_sq_le hR (g.continuous.comp (continuous_const.prodMk continuous_id))
    have hsq : ‖cos2DBandOp hR.le (hg_mem.toLp g)‖ ^ 2 ≤ ((1 - cos2DGap R) * ‖hg_mem.toLp g‖) ^ 2 := by
      calc ‖cos2DBandOp hR.le (hg_mem.toLp g)‖ ^ 2
          = ∫ rR in Icc (0 : ℝ) R, ∫ rL in Icc (0 : ℝ) R,
              (rawCos2DOp R (hg_mem.toLp g) (rL, rR)) ^ 2 := hlhs
        _ ≤ ∫ rR in Icc (0 : ℝ) R, (1 - cos2DGap R) * ∫ sL in Icc (0 : ℝ) R, (ψ sL rR) ^ 2 :=
            integral_mono hint_raw2.integral_prod_right (hint_ψ2.integral_prod_right.const_mul _) hstep1
        _ = (1 - cos2DGap R) * ∫ rR in Icc (0 : ℝ) R, ∫ sL in Icc (0 : ℝ) R, (ψ sL rR) ^ 2 :=
            integral_const_mul _ _
        _ = (1 - cos2DGap R) * ∫ sL in Icc (0 : ℝ) R, ∫ rR in Icc (0 : ℝ) R, (ψ sL rR) ^ 2 := by
            rw [integral_integral_swap hint_ψ2_swap]
        _ ≤ (1 - cos2DGap R) * ∫ sL in Icc (0 : ℝ) R,
              (1 - cos2DGap R) * ∫ sR in Icc (0 : ℝ) R, (g (sL, sR)) ^ 2 :=
            mul_le_mul_of_nonneg_left
              (integral_mono hint_ψ2.integral_prod_left (hint_g2.integral_prod_left.const_mul _) hstep2)
              h1gap_nn
        _ = (1 - cos2DGap R) ^ 2 * ∫ sL in Icc (0 : ℝ) R, ∫ sR in Icc (0 : ℝ) R, (g (sL, sR)) ^ 2 := by
            rw [integral_const_mul]; ring
        _ = ((1 - cos2DGap R) * ‖hg_mem.toLp g‖) ^ 2 := by rw [← hrhs]; ring
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg h1gap_nn (norm_nonneg _))).mp hsq
  have h_eps : ∀ {ε : ℝ}, 0 < ε →
      ‖cos2DBandOp hR.le f‖ ≤ (1 - cos2DGap R) * ‖f‖ +
        ((1 - cos2DGap R) + ‖cos2DBandOp hR.le‖) * ε := by
    intro ε hε
    have hf_mem : MemLp (f : ℝ × ℝ → ℝ) (ENNReal.ofReal 2) (cos2DBandMeasure R) := by
      simpa using Lp.memLp f
    obtain ⟨g, hg_int, g_mem⟩ := hf_mem.exists_boundedContinuous_integral_rpow_sub_le zero_lt_two
      (sq_pos_of_pos hε)
    have g_mem2 : MemLp (g : ℝ × ℝ → ℝ) 2 (cos2DBandMeasure R) := by simpa using g_mem
    have hdist : ‖f - g_mem2.toLp g‖ ≤ ε := by
      have hf2 : f = (Lp.memLp f).toLp f := (Lp.toLp_coeFn f (Lp.memLp f)).symm
      have hsub_eq : f - g_mem2.toLp g = ((Lp.memLp f).sub g_mem2).toLp ((f : ℝ × ℝ → ℝ) - ⇑g) := by
        nth_rw 1 [hf2]; rw [MemLp.toLp_sub]
      rw [hsub_eq, ← sq_le_sq₀ (norm_nonneg _) hε.le, ← real_inner_self_eq_norm_sq,
        MeasureTheory.L2.inner_def]
      have heq_in : (fun s => inner ℝ ((((Lp.memLp f).sub g_mem2).toLp ((f : ℝ × ℝ → ℝ) - ⇑g) : ℝ × ℝ → ℝ) s)
          ((((Lp.memLp f).sub g_mem2).toLp ((f : ℝ × ℝ → ℝ) - ⇑g) : ℝ × ℝ → ℝ) s)) =ᵐ[cos2DBandMeasure R]
          fun s => ‖(f : ℝ × ℝ → ℝ) s - g s‖ ^ (2 : ℝ) := by
        filter_upwards [((Lp.memLp f).sub g_mem2).coeFn_toLp] with s hs
        rw [hs, Pi.sub_apply, RCLike.inner_apply, conj_trivial, Real.rpow_two, Real.norm_eq_abs,
          sq_abs, sq]
      rw [integral_congr_ae heq_in]; exact hg_int
    have hdiff_op : ‖cos2DBandOp hR.le f - cos2DBandOp hR.le (g_mem2.toLp g)‖ ≤
        ‖cos2DBandOp hR.le‖ * ε := by
      rw [← map_sub]
      exact ((cos2DBandOp hR.le).le_opNorm _).trans (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
    have hg_norm : ‖g_mem2.toLp g‖ ≤ ‖f‖ + ε := by
      calc ‖g_mem2.toLp g‖ = ‖f - (f - g_mem2.toLp g)‖ := by congr 1; abel
        _ ≤ ‖f‖ + ‖f - g_mem2.toLp g‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ε := by linarith
    calc ‖cos2DBandOp hR.le f‖
        ≤ ‖cos2DBandOp hR.le (g_mem2.toLp g)‖ +
            ‖cos2DBandOp hR.le f - cos2DBandOp hR.le (g_mem2.toLp g)‖ := by
          simpa only [add_comm] using
            (norm_add_le (cos2DBandOp hR.le (g_mem2.toLp g))
              (cos2DBandOp hR.le f - cos2DBandOp hR.le (g_mem2.toLp g))) |>.trans_eq' (by
              congr 1; abel)
      _ ≤ (1 - cos2DGap R) * ‖g_mem2.toLp g‖ + ‖cos2DBandOp hR.le‖ * ε :=
          add_le_add (h_bcf g g_mem2) hdiff_op
      _ ≤ (1 - cos2DGap R) * (‖f‖ + ε) + ‖cos2DBandOp hR.le‖ * ε := by gcongr
      _ = (1 - cos2DGap R) * ‖f‖ + ((1 - cos2DGap R) + ‖cos2DBandOp hR.le‖) * ε := by ring
  by_contra! hlt
  set δ : ℝ := ‖cos2DBandOp hR.le f‖ - (1 - cos2DGap R) * ‖f‖
  have hδ : 0 < δ := sub_pos.mpr hlt
  set K : ℝ := (1 - cos2DGap R) + ‖cos2DBandOp hR.le‖
  have hK : 0 ≤ K := add_nonneg h1gap_nn (norm_nonneg _)
  have h_ctr := h_eps (ε := δ / (2 * (K + 1))) (by positivity)
  have h_small : K * (δ / (2 * (K + 1))) < δ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Equation `(int:AR2d-inv)` of Lemma INT-7C (`int:cos2d-repair`)**:
`A_R^{2D} := I + P_{Q_R} H_{2D} P_{Q_R}` is invertible on `L^2(Q_R)` with
`‖(A_R^{2D})⁻¹‖ ≤ max 2 (256 π^2 R^4 exp(8π R^2))`. -/
theorem cos2DOp_inv {R : ℝ} (hR : 0 < R) :
    ∃ A_inv : Lp ℝ 2 (cos2DBandMeasure R) →L[ℝ] Lp ℝ 2 (cos2DBandMeasure R),
      (1 + cos2DBandOp hR.le) * A_inv = 1 ∧
      A_inv * (1 + cos2DBandOp hR.le) = 1 ∧
      ‖A_inv‖ ≤ max 2 (256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2)) := by
  set ε := cos2DGap R
  have hε_pos : 0 < ε := cos2DGap_pos hR
  have hε_le : ε ≤ 1 / 2 := cos2DGap_le_half R
  have hnorm : ‖-cos2DBandOp hR.le‖ ≤ 1 - ε := by
    rw [norm_neg]; exact cos2DBandOp_norm_le hR
  have hlt1 : ‖-cos2DBandOp hR.le‖ < 1 := by linarith
  let u := Units.oneSub (-cos2DBandOp hR.le) hlt1
  refine ⟨(u⁻¹ : _ˣ), ?_, ?_, ?_⟩
  · have hu : (u : _ →L[ℝ] _) = 1 + cos2DBandOp hR.le := by
      simp [u, Units.val_oneSub, sub_neg_eq_add]
    rw [← hu]; exact Units.mul_inv u
  · have hu : (u : _ →L[ℝ] _) = 1 + cos2DBandOp hR.le := by
      simp [u, Units.val_oneSub, sub_neg_eq_add]
    rw [← hu]; exact Units.inv_mul u
  · have h_geo := tsum_geometric_le_of_norm_lt_one (-cos2DBandOp hR.le) hlt1
    have h_u_eq : (↑(u⁻¹ : _ˣ) : Lp ℝ 2 (cos2DBandMeasure R) →L[ℝ] Lp ℝ 2 (cos2DBandMeasure R)) =
        ∑' n : ℕ, (-cos2DBandOp hR.le) ^ n := rfl
    rw [h_u_eq]
    have h1_le : ‖(1 : Lp ℝ 2 (cos2DBandMeasure R) →L[ℝ] Lp ℝ 2 (cos2DBandMeasure R))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have h_geo' : ‖∑' n : ℕ, (-cos2DBandOp hR.le) ^ n‖ ≤ (1 - ‖-cos2DBandOp hR.le‖)⁻¹ := by
      linarith
    have h_inv_le : (1 - ‖-cos2DBandOp hR.le‖)⁻¹ ≤ ε⁻¹ :=
      inv_anti₀ hε_pos (by linarith)
    refine h_geo'.trans (h_inv_le.trans_eq ?_)
    simp only [ε, cos2DGap]
    set C : ℝ := 256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2)
    have hC : 0 < C := by positivity
    by_cases hle : (1 / 2 : ℝ) ≤ 1 / C
    · have hC2 : C ≤ 2 := by rwa [one_div, one_div, inv_le_inv₀ (by norm_num) hC] at hle
      rw [min_eq_left hle, max_eq_left hC2]; norm_num
    · have hgt : 1 / C < 1 / 2 := not_le.mp hle
      have hC2 : 2 < C := by rwa [one_div, one_div, inv_lt_inv₀ hC (by norm_num)] at hgt
      rw [min_eq_right hgt.le, max_eq_right hC2.le]
      simp

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.cos2DBandOp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cos2DBandOp_norm_le

/-- info: 'FormalResearch.ModularBootstrap.Spin.cos2DOp_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cos2DOp_inv

end FormalResearch.ModularBootstrap.Spin
