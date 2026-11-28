module

public import FormalResearch.ModularBootstrap.Integrality.SlitMaxMod
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# L¹∩L² Plancherel Compatibility and 1D Fourier Concentration (`int:sonine`)

Proves:
1. `toLp_fourierIntegral_eq`, `fourierIntegral_memLp_two`, and `integral_norm_sq_fourierIntegral`:
   $L^2$ Plancherel identity for `𝓕 f` when `f ∈ L¹(V, ℂ) ∩ L²(V, ℂ)`.
2. `fourier_concentration_1d`: If `φ : ℝ → ℂ` is $L^2$ and vanishes outside `[-R, R]`, then
   `∫ ξ in Icc (-R) R, ‖𝓕 φ ξ‖ ^ 2 ≤ (1 - ε_R) * ∫ x, ‖φ x‖ ^ 2` with
   `ε_R = min (1 / 2) (1 / (256 * π ^ 2 * R ^ 4 * exp (8 * π * R ^ 2)))`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set
open scoped FourierTransform ComplexInnerProductSpace ENNReal SchwartzMap

namespace FormalResearch.ModularBootstrap.Integrality

section PlancherelL1L2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- For `f ∈ L¹(V, ℂ) ∩ L²(V, ℂ)`, `𝓕 (hf₂.toLp f)` agrees a.e. with `𝓕 f`. -/
theorem toLp_fourierIntegral_eq {f : V → ℂ} (hf₁ : Integrable f volume)
    (hf₂ : MemLp f 2 volume) :
    (𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) =ᵐ[volume] 𝓕 f := by
  let G : Lp ℂ 2 volume := 𝓕 (hf₂.toLp f)
  have hG_loc : LocallyIntegrable (fun x => G x) volume :=
    (Lp.memLp G).locallyIntegrable (by norm_num)
  have hf_cont : Continuous (𝓕 f) := by
    change Continuous (fun w => ∫ v, Real.fourierChar (-(inner ℝ v w)) • f v)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf₁
  have hf_loc : LocallyIntegrable (𝓕 f) volume := hf_cont.locallyIntegrable
  refine (ae_eq_zero_of_integral_contDiff_smul_eq_zero (hG_loc.sub hf_loc) fun g hg_sm hg_supp => ?_).mono
    fun x hx => sub_eq_zero.mp hx
  let gc : V → ℂ := fun x => (g x : ℂ)
  have hgc_sm : ContDiff ℝ (⊤ : ℕ∞) gc := (Complex.ofRealCLM.contDiff.of_le le_top).comp hg_sm
  have hgc_supp : HasCompactSupport gc := hg_supp.comp_left Complex.ofReal_zero
  let ψ : 𝓢(V, ℂ) := hgc_supp.toSchwartzMap hgc_sm
  have hψ_val : ∀ x, ψ x = (g x : ℂ) := fun _ => rfl
  have hψ_conj : ∀ x, star (ψ x) = ψ x := fun x => by simp [hψ_val x]
  have h1 : ∫ x, g x • G x = ∫ x, ⟪ψ x, G x⟫ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [RCLike.inner_apply (𝕜 := ℂ), hψ_val, Complex.conj_ofReal]
    simp [real_smul, mul_comm]
  have h2 : ∫ x, ⟪ψ x, G x⟫ = ⟪ψ.toLp 2, G⟫ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ψ.coeFn_toLp 2 volume] with x hx
    rw [hx]
  have h3 : ⟪ψ.toLp 2, G⟫ = ⟪𝓕⁻ (ψ.toLp 2), hf₂.toLp f⟫ := by
    have hff : (Lp.fourierTransformₗᵢ V ℂ) (𝓕⁻ (ψ.toLp 2 volume)) = ψ.toLp 2 volume :=
      (Lp.fourierTransformₗᵢ V ℂ).apply_symm_apply (ψ.toLp 2 volume)
    calc ⟪ψ.toLp 2 volume, G⟫
        = ⟪(Lp.fourierTransformₗᵢ V ℂ) (𝓕⁻ (ψ.toLp 2 volume)),
            (Lp.fourierTransformₗᵢ V ℂ) (hf₂.toLp f)⟫ := by rw [hff]; rfl
      _ = ⟪𝓕⁻ (ψ.toLp 2 volume), hf₂.toLp f⟫ :=
          (Lp.fourierTransformₗᵢ V ℂ).inner_map_map _ _
  have h4 : ⟪𝓕⁻ (ψ.toLp 2), hf₂.toLp f⟫ = ∫ x, star ((𝓕⁻ ψ : 𝓢(V, ℂ)) x) * f x := by
    rw [SchwartzMap.toLp_fourierInv_eq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(𝓕⁻ ψ).coeFn_toLp 2 volume, hf₂.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply (𝕜 := ℂ), ← Complex.star_def, mul_comm]
  have hstar_fourierInv : ∀ x : V, star ((𝓕⁻ ψ : 𝓢(V, ℂ)) x) = 𝓕 (ψ : V → ℂ) x := by
    intro x
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', Real.fourier_eq']
    have heq : (fun v : V => (starRingEnd ℂ) (Complex.exp (↑(2 * π * inner ℝ v x) * Complex.I) * ψ v)) =
        fun v : V => Complex.exp (↑(-2 * π * inner ℝ v x) * Complex.I) • ψ v := by
      ext v
      rw [map_mul, ← Complex.star_def, hψ_conj v, smul_eq_mul]
      congr 1
      rw [Complex.star_def, ← Complex.exp_conj]
      simp [neg_mul, map_ofNat]
    have hconj := integral_conj (μ := volume)
      (f := fun v : V => Complex.exp (↑(2 * π * inner ℝ v x) * Complex.I) * ψ v)
    change (starRingEnd ℂ) (∫ v : V, Complex.exp (↑(2 * π * inner ℝ v x) * Complex.I) * ψ v) = _
    rw [← hconj]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    exact congr_fun heq v
  have h5 : ∫ x, star ((𝓕⁻ ψ : 𝓢(V, ℂ)) x) * f x = ∫ ξ, (ψ : V → ℂ) ξ * 𝓕 f ξ := by
    simp_rw [hstar_fourierInv, Real.fourier_eq]
    have hflip : (innerₗ V).flip = innerₗ V := by
      ext v w
      simp
    have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ V) Real.continuous_fourierChar continuous_inner (ψ.integrable (μ := volume)) hf₁
    rw [hflip] at hswap
    simp only [smul_eq_mul] at hswap
    exact hswap
  have h6 : ∫ ξ, (ψ : V → ℂ) ξ * 𝓕 f ξ = ∫ x, g x • 𝓕 f x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [ψ, gc, real_smul]
  obtain ⟨C_g, hC_g⟩ := hg_supp.isCompact.exists_bound_of_continuousOn hg_sm.continuous.continuousOn
  have hg_bdd : ∀ x : V, |g x| ≤ max C_g 0 := fun x => by
    by_cases hx : x ∈ tsupport g
    · exact (hC_g x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
      exact le_max_right _ _
  have hint_mul_compact : ∀ {H : V → ℂ}, LocallyIntegrable H volume →
      Integrable (fun x => g x • H x) volume := by
    intro H hH_loc
    have hIon : IntegrableOn (fun x => g x • H x) (tsupport g) volume := by
      refine ((hH_loc.integrableOn_isCompact hg_supp).norm.const_mul (max C_g 0)).mono'
        ((hg_sm.continuous.aestronglyMeasurable.smul hH_loc.aestronglyMeasurable).restrict) ?_
      filter_upwards with x
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hg_bdd x) (norm_nonneg _)
    have hind : (fun x => g x • H x) = (tsupport g).indicator (fun x => g x • H x) := by
      ext x
      by_cases hx : x ∈ tsupport g
      · simp [hx]
      · simp [hx, image_eq_zero_of_notMem_tsupport hx]
    rw [hind, integrable_indicator_iff (isClosed_tsupport (f := g)).measurableSet]
    exact hIon
  have hint_G : Integrable (fun x => g x • G x) volume := hint_mul_compact hG_loc
  have hint_f : Integrable (fun x => g x • 𝓕 f x) volume := hint_mul_compact hf_loc
  have hsub_eq : ∫ x, g x • (G x - 𝓕 f x) = ∫ x, (g x • G x - g x • 𝓕 f x) :=
    integral_congr_ae (Eventually.of_forall fun x => smul_sub (g x) (G x) (𝓕 f x))
  change ∫ x, g x • (G x - 𝓕 f x) = 0
  rw [hsub_eq, integral_sub hint_G hint_f, h1, h2, h3, h4, h5, h6, sub_self]

theorem fourierIntegral_memLp_two {f : V → ℂ} (hf₁ : Integrable f volume)
    (hf₂ : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume :=
  (Lp.memLp (𝓕 (hf₂.toLp f))).ae_eq (toLp_fourierIntegral_eq hf₁ hf₂)

private lemma lp_two_norm_sq_eq (G : Lp ℂ 2 (volume : Measure V)) :
    ‖G‖ ^ 2 = ∫ x : V, ‖G x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def]
  have h_int_inner : Integrable (fun x : V => ⟪G x, G x⟫) volume := by
    have h_int : Integrable (fun x => ‖G x‖ ^ 2) volume := (Lp.memLp G).norm.integrable_sq
    refine (Complex.ofRealCLM.integrable_comp h_int).congr (Eventually.of_forall fun x => ?_)
    simp [inner_self_eq_norm_sq_to_K]
  change Complex.reCLM (∫ x : V, ⟪G x, G x⟫) = _
  rw [← Complex.reCLM.integral_comp_comm h_int_inner]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (G x)).symm

/-- Plancherel's $L^2$ norm identity for `𝓕 f` when `f ∈ L¹(V, ℂ) ∩ L²(V, ℂ)`. -/
theorem integral_norm_sq_fourierIntegral {f : V → ℂ} (hf₁ : Integrable f volume)
    (hf₂ : MemLp f 2 volume) :
    ∫ ξ : V, ‖𝓕 f ξ‖ ^ 2 = ∫ x : V, ‖f x‖ ^ 2 := by
  have hL2 := Lp.norm_fourier_eq (hf₂.toLp f)
  have h1 : ‖𝓕 (hf₂.toLp f)‖ ^ 2 = ∫ ξ : V, ‖𝓕 f ξ‖ ^ 2 := by
    rw [lp_two_norm_sq_eq]
    refine integral_congr_ae ?_
    filter_upwards [toLp_fourierIntegral_eq hf₁ hf₂] with ξ hξ
    rw [hξ]
  have h2 : ‖hf₂.toLp f‖ ^ 2 = ∫ x : V, ‖f x‖ ^ 2 := by
    rw [lp_two_norm_sq_eq]
    refine integral_congr_ae ?_
    filter_upwards [hf₂.coeFn_toLp] with x hx
    rw [hx]
  rw [← h1, ← h2, hL2]

end PlancherelL1L2

/-! ### 1D Paley-Wiener / Fourier Concentration Bound -/

private lemma halvingSobolev_right {g g' : ℝ → ℂ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg'_cont : Continuous g')
    (hg2 : Integrable (fun x => ‖g x‖ ^ 2) volume)
    (hg'2 : Integrable (fun x => ‖g' x‖ ^ 2) volume)
    (hgg' : Integrable (fun x => ‖g x‖ * ‖g' x‖) volume) {R : ℝ} :
    ∀ x : ℝ, R ≤ x →
      ‖g x‖ ^ 2 ≤ 2 * Real.sqrt (∫ t in Ioi R, ‖g t‖ ^ 2) *
        Real.sqrt (∫ t in Ioi R, ‖g' t‖ ^ 2) := by
  intro x hx
  set A : ℝ := Real.sqrt (∫ t in Ioi R, ‖g t‖ ^ 2)
  set B : ℝ := Real.sqrt (∫ t in Ioi R, ‖g' t‖ ^ 2)
  have hA_sq : A ^ 2 = ∫ t in Ioi R, ‖g t‖ ^ 2 :=
    Real.sq_sqrt (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
  have hB_sq : B ^ 2 = ∫ t in Ioi R, ‖g' t‖ ^ 2 :=
    Real.sq_sqrt (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
  have h_prod : ∫ t in Ioi R, ‖g t‖ * ‖g' t‖ ≤ A * B := by
    by_cases hA0 : A = 0
    · have hI0 : ∫ t in Ioi R, ‖g t‖ ^ 2 = 0 := by nlinarith [hA_sq, hA0]
      have hae : ∀ᵐ t ∂(volume.restrict (Ioi R)), ‖g t‖ ^ 2 = 0 :=
        (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hg2.integrableOn).mp hI0
      have hae0 : ∀ᵐ t ∂(volume.restrict (Ioi R)), ‖g t‖ * ‖g' t‖ = 0 := by
        filter_upwards [hae] with t ht
        have : ‖g t‖ = 0 := sq_eq_zero_iff.mp ht
        simp [this]
      rw [integral_eq_zero_of_ae hae0, hA0, zero_mul]
    · by_cases hB0 : B = 0
      · have hI0 : ∫ t in Ioi R, ‖g' t‖ ^ 2 = 0 := by nlinarith [hB_sq, hB0]
        have hae : ∀ᵐ t ∂(volume.restrict (Ioi R)), ‖g' t‖ ^ 2 = 0 :=
          (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hg'2.integrableOn).mp hI0
        have hae0 : ∀ᵐ t ∂(volume.restrict (Ioi R)), ‖g t‖ * ‖g' t‖ = 0 := by
          filter_upwards [hae] with t ht
          have : ‖g' t‖ = 0 := sq_eq_zero_iff.mp ht
          simp [this]
        rw [integral_eq_zero_of_ae hae0, hB0, mul_zero]
      · have hAp : 0 < A := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hA0)
        have hBp : 0 < B := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hB0)
        have hdom : ∀ t : ℝ, ‖g t‖ * ‖g' t‖ ≤
            (B / (2 * A)) * ‖g t‖ ^ 2 + (A / (2 * B)) * ‖g' t‖ ^ 2 := fun t => by
          have hs : 0 ≤ (B * ‖g t‖ - A * ‖g' t‖) ^ 2 := sq_nonneg _
          have h2AB : 0 < 2 * A * B := by positivity
          have hmul : 2 * A * B * (‖g t‖ * ‖g' t‖) ≤
              B ^ 2 * ‖g t‖ ^ 2 + A ^ 2 * ‖g' t‖ ^ 2 := by nlinarith
          have heq : (B ^ 2 * ‖g t‖ ^ 2 + A ^ 2 * ‖g' t‖ ^ 2) / (2 * A * B) =
              (B / (2 * A)) * ‖g t‖ ^ 2 + (A / (2 * B)) * ‖g' t‖ ^ 2 := by
            field_simp
          rw [← heq]
          exact (le_div_iff₀ h2AB).mpr (by linarith)
        have hrhs : IntegrableOn (fun t => (B / (2 * A)) * ‖g t‖ ^ 2 + (A / (2 * B)) * ‖g' t‖ ^ 2)
            (Ioi R) :=
          (hg2.integrableOn.const_mul _).add (hg'2.integrableOn.const_mul _)
        calc ∫ t in Ioi R, ‖g t‖ * ‖g' t‖
            ≤ ∫ t in Ioi R, ((B / (2 * A)) * ‖g t‖ ^ 2 + (A / (2 * B)) * ‖g' t‖ ^ 2) :=
              setIntegral_mono hgg'.integrableOn hrhs hdom
          _ = (B / (2 * A)) * (∫ t in Ioi R, ‖g t‖ ^ 2) +
                (A / (2 * B)) * (∫ t in Ioi R, ‖g' t‖ ^ 2) := by
              rw [integral_add (hg2.integrableOn.const_mul _) (hg'2.integrableOn.const_mul _),
                integral_const_mul, integral_const_mul]
          _ = (B / (2 * A)) * A ^ 2 + (A / (2 * B)) * B ^ 2 := by rw [hA_sq, hB_sq]
          _ = A * B := by field_simp; ring
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hT_ex : ∃ T : ℝ, x < T ∧ ‖g T‖ ^ 2 < δ := by
    by_contra hno
    push Not at hno
    have hinf : ∫⁻ t in Ioi x, ENNReal.ofReal δ ≤ ∫⁻ t in Ioi x, ENNReal.ofReal (‖g t‖ ^ 2) :=
      setLIntegral_mono' measurableSet_Ioi fun t ht => ENNReal.ofReal_le_ofReal (hno t ht)
    have hfin : ∫⁻ t in Ioi x, ENNReal.ofReal (‖g t‖ ^ 2) < ⊤ := by
      have hhas := (hg2.integrableOn (s := Ioi x)).2
      have heq_enorm : (fun t => ENNReal.ofReal (‖g t‖ ^ 2)) = fun t => ‖‖g t‖ ^ 2‖ₑ := by
        ext t; rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
      rw [heq_enorm]
      exact hhas
    rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hδ).ne'] at hinf
    exact (lt_top_iff_ne_top.mp hfin) (top_le_iff.mp hinf)
  obtain ⟨T, hxT, hTg⟩ := hT_ex
  have hderiv : ∀ t ∈ uIcc x T,
      HasDerivAt (fun s => ‖g s‖ ^ 2) (2 * ((g t).re * (g' t).re + (g t).im * (g' t).im)) t := by
    intro t _
    have hre : HasDerivAt (fun s => (g s).re) (g' t).re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hg t)
    have him : HasDerivAt (fun s => (g s).im) (g' t).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hg t)
    have hsq : (fun s => ‖g s‖ ^ 2) = fun s => (g s).re ^ 2 + (g s).im ^ 2 := by
      ext s; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hsq]
    convert (hre.pow 2).add (him.pow 2) using 1
    ring
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hint_der : IntervalIntegrable
      (fun t => 2 * ((g t).re * (g' t).re + (g t).im * (g' t).im)) volume x T :=
    (by fun_prop : Continuous fun t =>
      2 * ((g t).re * (g' t).re + (g t).im * (g' t).im)).intervalIntegrable x T
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_der
  have hcs : ∀ t : ℝ, -(2 * (‖g t‖ * ‖g' t‖)) ≤
      2 * ((g t).re * (g' t).re + (g t).im * (g' t).im) := fun t => by
    have h1 : ((g t).re * (g' t).re + (g t).im * (g' t).im) ^ 2 ≤
        (‖g t‖ * ‖g' t‖) ^ 2 := by
      have hsq1 : ‖g t‖ ^ 2 = (g t).re ^ 2 + (g t).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have hsq2 : ‖g' t‖ ^ 2 = (g' t).re ^ 2 + (g' t).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      rw [mul_pow, hsq1, hsq2]
      nlinarith [sq_nonneg ((g t).re * (g' t).im - (g t).im * (g' t).re)]
    have h2 : |((g t).re * (g' t).re + (g t).im * (g' t).im)| ≤ ‖g t‖ * ‖g' t‖ :=
      abs_le.mpr (abs_le_of_sq_le_sq' h1 (by positivity))
    linarith [neg_abs_le ((g t).re * (g' t).re + (g t).im * (g' t).im)]
  have h_int_bnd : -(2 * ∫ t in Ioi R, ‖g t‖ * ‖g' t‖) ≤
      ∫ t in x..T, 2 * ((g t).re * (g' t).re + (g t).im * (g' t).im) := by
    calc -(2 * ∫ t in Ioi R, ‖g t‖ * ‖g' t‖)
        ≤ -(2 * ∫ t in x..T, ‖g t‖ * ‖g' t‖) := by
          gcongr
          rw [intervalIntegral.integral_of_le hxT.le]
          exact setIntegral_mono_set hgg'.integrableOn (Eventually.of_forall fun _ => by positivity)
            (Eventually.of_forall fun _ hy => (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hx)) hy)
      _ = ∫ t in x..T, -(2 * (‖g t‖ * ‖g' t‖)) := by
          rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
      _ ≤ ∫ t in x..T, 2 * ((g t).re * (g' t).re + (g t).im * (g' t).im) :=
          intervalIntegral.integral_mono_on hxT.le ((hgg'.const_mul 2).neg.intervalIntegrable)
            hint_der (fun t _ => hcs t)
  linarith

private lemma halvingSobolev_left {g g' : ℝ → ℂ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg'_cont : Continuous g')
    (hg2 : Integrable (fun x => ‖g x‖ ^ 2) volume)
    (hg'2 : Integrable (fun x => ‖g' x‖ ^ 2) volume)
    (hgg' : Integrable (fun x => ‖g x‖ * ‖g' x‖) volume) {R : ℝ} :
    ∀ x : ℝ, x ≤ -R →
      ‖g x‖ ^ 2 ≤ 2 * Real.sqrt (∫ t in Iic (-R), ‖g t‖ ^ 2) *
        Real.sqrt (∫ t in Iic (-R), ‖g' t‖ ^ 2) := by
  have hg_neg_der : ∀ t : ℝ, HasDerivAt (fun s => g (-s)) (-g' (-t)) t := fun t => by
    have hneg_t : HasDerivAt (fun s : ℝ => -s) (-1) t := hasDerivAt_neg t
    have hcomp : HasDerivAt (fun s : ℝ => g (-s)) ((-1 : ℝ) • g' (-t)) t :=
      (hg (-t)).scomp t hneg_t
    simpa [neg_smul] using hcomp
  have hneg := halvingSobolev_right hg_neg_der (hg'_cont.comp continuous_neg).neg
    (by simpa using hg2.comp_neg) (by simpa using hg'2.comp_neg)
    (by simpa using hgg'.comp_neg) (R := R)
  intro x hx
  have hx' : R ≤ -x := by linarith
  have hres := hneg (-x) hx'
  have hswap : ∀ f : ℝ → ℝ, ∫ t in Ioi R, f (-t) = ∫ t in Iic (-R), f t := fun f => by
    have hpre : (MeasurableEquiv.neg ℝ) ⁻¹' Iio (-R) = Ioi R := by
      ext t; simp
    have h1 : ∫ t in Ioi R, f (-t) = ∫ t in Iio (-R), f t := by
      simpa [hpre] using
        (Measure.measurePreserving_neg volume).setIntegral_preimage_emb
          (MeasurableEquiv.neg ℝ).measurableEmbedding f (Iio (-R))
    rw [h1]
    exact setIntegral_congr_set Iio_ae_eq_Iic
  simpa only [hswap (fun t => ‖g t‖ ^ 2), hswap (fun t => ‖g' t‖ ^ 2), norm_neg, neg_neg] using hres

private lemma fourier_holomorphic_bound_aux {R : ℝ} (hR : 0 < R) (φ : ℝ → ℂ) (z₀ : ℂ) :
    ∀ᵐ (t : ℝ) ∂(volume.restrict (Icc (-R) R)),
      ∀ z ∈ Metric.ball z₀ 1,
        ‖(-2 * π * Complex.I * (t : ℂ)) * Complex.exp (-2 * π * Complex.I * z * (t : ℂ)) * φ t‖ ≤
          (2 * π * R * Real.exp (2 * π * (‖z₀‖ + 1) * R)) * ‖φ t‖ := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht z hz
  have hzt : |t| ≤ R := abs_le.mpr ht
  have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have h1 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_le_norm_sub_add z z₀
    have h2 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
    linarith
  have hre : (-2 * π * Complex.I * z * (t : ℂ)).re = 2 * π * z.im * t := by
    simp [Complex.mul_re]
  rw [norm_mul, norm_mul, Complex.norm_exp, hre]
  have h1 : ‖-2 * (π : ℂ) * Complex.I * (t : ℂ)‖ ≤ 2 * π * R := by
    calc ‖-2 * (π : ℂ) * Complex.I * (t : ℂ)‖
        = 2 * π * |t| := by simp [Complex.norm_real, Complex.norm_I, abs_of_pos Real.pi_pos]
      _ ≤ 2 * π * R := by gcongr
  have h2 : Real.exp (2 * π * z.im * t) ≤ Real.exp (2 * π * (‖z₀‖ + 1) * R) := by
    refine Real.exp_le_exp.mpr ?_
    have him : |z.im| ≤ ‖z₀‖ + 1 := (Complex.abs_im_le_norm z).trans hzn
    have hmul : z.im * t ≤ (‖z₀‖ + 1) * R :=
      (le_abs_self _).trans ((abs_mul z.im t).le.trans (mul_le_mul him hzt (abs_nonneg _) (by positivity)))
    nlinarith [Real.pi_pos]
  calc ‖-2 * (π : ℂ) * Complex.I * (t : ℂ)‖ * Real.exp (2 * π * z.im * t) * ‖φ t‖
      ≤ (2 * π * R) * Real.exp (2 * π * (‖z₀‖ + 1) * R) * ‖φ t‖ := by gcongr

private lemma fourier_holomorphic_ext {R : ℝ} (hR : 0 < R) {φ : ℝ → ℂ}
    (hφ_meas : AEStronglyMeasurable φ volume) (hφ_int : Integrable φ volume) :
    Differentiable ℂ
      (fun z => ∫ t in Icc (-R) R, Complex.exp (-2 * π * Complex.I * z * (t : ℂ)) * φ t) := by
  intro z₀
  let F : ℂ → ℝ → ℂ := fun z t => Complex.exp (-2 * π * Complex.I * z * (t : ℂ)) * φ t
  let F' : ℂ → ℝ → ℂ := fun z t =>
    (-2 * π * Complex.I * (t : ℂ)) * Complex.exp (-2 * π * Complex.I * z * (t : ℂ)) * φ t
  let bound : ℝ → ℝ := fun t => (2 * π * R * Real.exp (2 * π * (‖z₀‖ + 1) * R)) * ‖φ t‖
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (Icc (-R) R)) :=
    Eventually.of_forall fun z =>
      ((by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-2 * π * Complex.I * z * (t : ℂ))).aestronglyMeasurable.mul
          hφ_meas).restrict
  have hF_int : IntegrableOn (F z₀) (Icc (-R) R) volume := by
    refine (hφ_int.integrableOn.norm.const_mul (Real.exp (2 * π * ‖z₀‖ * R))).mono'
      (hF_meas.self_of_nhds) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul, Complex.norm_exp]
    have hre : (-2 * π * Complex.I * z₀ * (t : ℂ)).re = 2 * π * z₀.im * t := by
      simp [Complex.mul_re]
    rw [hre]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 : |z₀.im| ≤ ‖z₀‖ := Complex.abs_im_le_norm z₀
    have h2 : |t| ≤ R := abs_le.mpr ht
    have hmul : z₀.im * t ≤ ‖z₀‖ * R :=
      (le_abs_self _).trans ((abs_mul z₀.im t).le.trans (mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)))
    nlinarith [Real.pi_pos]
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Icc (-R) R)) :=
    ((by fun_prop : Continuous fun t : ℝ =>
      (-2 * π * Complex.I * (t : ℂ)) * Complex.exp (-2 * π * Complex.I * z₀ * (t : ℂ))).aestronglyMeasurable.mul
        hφ_meas).restrict
  have hb_int : IntegrableOn bound (Icc (-R) R) volume :=
    hφ_int.integrableOn.norm.const_mul _
  have h_diff : ∀ᵐ t ∂(volume.restrict (Icc (-R) R)),
      ∀ z ∈ Metric.ball z₀ 1, HasDerivAt (fun w => F w t) (F' z t) z := by
    filter_upwards with t z _
    have hd1 : HasDerivAt (fun w : ℂ => (-2 * π * Complex.I * (t : ℂ)) * w)
        (-2 * π * Complex.I * (t : ℂ)) z := by
      simpa only [mul_one, id_eq] using
        (hasDerivAt_id z).const_mul (-2 * π * Complex.I * (t : ℂ))
    have hF_eq : (fun w => F w t) = fun w =>
        Complex.exp ((-2 * π * Complex.I * (t : ℂ)) * w) * φ t := by
      ext w; dsimp [F]; ring_nf
    rw [hF_eq]
    convert (hd1.cexp).mul_const (φ t) using 1
    dsimp [F']; ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ one_pos)
    hF_meas hF_int hF'_meas (fourier_holomorphic_bound_aux hR φ z₀) hb_int h_diff).2.differentiableAt

/-- 1D Paley-Wiener / Fourier concentration inequality (`int:sonine`):
if `φ : ℝ → ℂ` lies in `L²(ℝ)` and vanishes outside `[-R, R]` (`R > 0`), then
`∫ ξ in Icc (-R) R, ‖𝓕 φ ξ‖ ^ 2 ≤ (1 - ε_R) * ∫ x, ‖φ x‖ ^ 2` where
`ε_R = min (1 / 2) (1 / (256 * π ^ 2 * R ^ 4 * exp (8 * π * R ^ 2)))`. -/
theorem fourier_concentration_1d {R : ℝ} (hR : 0 < R) {φ : ℝ → ℂ}
    (hφ_meas : AEStronglyMeasurable φ volume) (hφ_mem : MemLp φ 2 volume)
    (hφ_supp : ∀ x : ℝ, R < |x| → φ x = 0) :
    ∫ ξ in Icc (-R) R, ‖𝓕 φ ξ‖ ^ 2 ≤
      (1 - min (1 / 2 : ℝ) (1 / (256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2)))) *
        ∫ x : ℝ, ‖φ x‖ ^ 2 := by
  have hφ_int : Integrable φ volume := by
    have : IsFiniteMeasure (volume.restrict (Icc (-R) R)) :=
      isFiniteMeasure_restrict.mpr (by simp [Real.volume_Icc])
    have hIcc : IntegrableOn φ (Icc (-R) R) volume :=
      (hφ_mem.restrict (Icc (-R) R)).integrable (by norm_num)
    have heq : φ = (Icc (-R) R).indicator φ := by
      ext x
      by_cases hx : x ∈ Icc (-R) R
      · simp [hx]
      · have habs : R < |x| := by
          rw [mem_Icc, not_and_or, not_le, not_le] at hx
          rcases hx with hx | hx <;> [exact lt_abs.mpr (Or.inr (by linarith)); exact lt_abs.mpr (Or.inl hx)]
        simp [hx, hφ_supp x habs]
    rw [heq, integrable_indicator_iff measurableSet_Icc]
    exact hIcc
  let ψ : ℝ → ℂ := fun x => (-2 * π * Complex.I * (x : ℂ)) * φ x
  have hψ_bdd : ∀ x : ℝ, ‖ψ x‖ ≤ (2 * π * R) * ‖φ x‖ := by
    intro x
    by_cases hx : R < |x|
    · simp [ψ, hφ_supp x hx]
    · push Not at hx
      dsimp [ψ]
      rw [norm_mul]
      gcongr
      calc ‖-2 * (π : ℂ) * Complex.I * (x : ℂ)‖
          = 2 * π * |x| := by
            simp [Complex.norm_real, Complex.norm_I, abs_of_pos Real.pi_pos]
        _ ≤ 2 * π * R := by gcongr
  have hψ_meas : AEStronglyMeasurable ψ volume :=
    (by fun_prop : Continuous fun x : ℝ => (-2 * π * Complex.I * (x : ℂ))).aestronglyMeasurable.mul
      hφ_meas
  have hψ_int : Integrable ψ volume :=
    (hφ_int.norm.const_mul (2 * π * R)).mono' hψ_meas (Eventually.of_forall hψ_bdd)
  have hψ_mem : MemLp ψ 2 volume :=
    (hφ_mem.norm.const_mul (2 * π * R)).mono' hψ_meas (Eventually.of_forall fun x => by
      simpa [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * π * R * ‖φ x‖)] using hψ_bdd x)
  have hxφ_int : Integrable (fun x : ℝ => x • φ x) volume := by
    refine (hφ_int.norm.const_mul R).mono'
      ((continuous_id : Continuous (fun x : ℝ => x)).aestronglyMeasurable.smul hφ_meas) ?_
    refine Eventually.of_forall fun x => ?_
    by_cases hx : R < |x|
    · simp [hφ_supp x hx]
    · push Not at hx
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
  have hderiv_g : ∀ ξ : ℝ, HasDerivAt (𝓕 φ) (𝓕 ψ ξ) ξ := by
    intro ξ
    have heq : ψ = fun x : ℝ => (-2 * π * Complex.I * x) • φ x := by
      ext x; simp [ψ, smul_eq_mul]
    rw [heq]
    exact Real.hasDerivAt_fourier hφ_int hxφ_int ξ
  have hg_cont : Continuous (𝓕 φ) := by
    change Continuous (fun w => ∫ v : ℝ, Real.fourierChar (-(inner ℝ v w)) • φ v)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hφ_int
  have hg'_cont : Continuous (𝓕 ψ) := by
    change Continuous (fun w => ∫ v : ℝ, Real.fourierChar (-(inner ℝ v w)) • ψ v)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hψ_int
  have hg_mem : MemLp (𝓕 φ) 2 volume := fourierIntegral_memLp_two hφ_int hφ_mem
  have hg'_mem : MemLp (𝓕 ψ) 2 volume := fourierIntegral_memLp_two hψ_int hψ_mem
  have hg2_int : Integrable (fun ξ => ‖𝓕 φ ξ‖ ^ 2) volume := hg_mem.norm.integrable_sq
  have hg'2_int : Integrable (fun ξ => ‖𝓕 ψ ξ‖ ^ 2) volume := hg'_mem.norm.integrable_sq
  have hgg'_int : Integrable (fun ξ => ‖𝓕 φ ξ‖ * ‖𝓕 ψ ξ‖) volume := by
    refine ((hg2_int.add hg'2_int).const_mul (1 / 2 : ℝ)).mono'
      ((hg_cont.norm).mul (hg'_cont.norm)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun ξ => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖𝓕 φ ξ‖ - ‖𝓕 ψ ξ‖)]
  set N2 : ℝ := ∫ x : ℝ, ‖φ x‖ ^ 2
  set I : ℝ := ∫ ξ in Icc (-R) R, ‖𝓕 φ ξ‖ ^ 2
  have hN2_planch : ∫ ξ : ℝ, ‖𝓕 φ ξ‖ ^ 2 = N2 := integral_norm_sq_fourierIntegral hφ_int hφ_mem
  have hI_nonneg : 0 ≤ I := setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have hI_le_N2 : I ≤ N2 := by
    rw [← hN2_planch]
    exact setIntegral_le_integral hg2_int (Eventually.of_forall fun _ => sq_nonneg _)
  by_cases hN2_0 : N2 ≤ 0
  · have hI0 : I = 0 := le_antisymm (hI_le_N2.trans hN2_0) hI_nonneg
    have hN2_eq : N2 = 0 := le_antisymm hN2_0 (integral_nonneg fun _ => sq_nonneg _)
    rw [hI0, hN2_eq, mul_zero]
  have hN2_pos : 0 < N2 := lt_of_not_ge hN2_0
  set ε_tail : ℝ := N2 - I
  have hε_tail_nn : 0 ≤ ε_tail := sub_nonneg.mpr hI_le_N2
  have hg'_planch : ∫ ξ : ℝ, ‖𝓕 ψ ξ‖ ^ 2 ≤ (2 * π * R) ^ 2 * N2 := by
    rw [integral_norm_sq_fourierIntegral hψ_int hψ_mem, ← integral_const_mul]
    exact integral_mono hψ_mem.norm.integrable_sq (hφ_mem.norm.integrable_sq.const_mul _) fun x => by
      have := hψ_bdd x
      nlinarith [norm_nonneg (ψ x), norm_nonneg (φ x)]
  have h_tail_eq : ∫ ξ in (Icc (-R) R)ᶜ, ‖𝓕 φ ξ‖ ^ 2 = ε_tail := by
    have hadd := integral_add_compl (s := Icc (-R) R) measurableSet_Icc hg2_int
    linarith
  have h_right_le : ∫ ξ in Ioi R, ‖𝓕 φ ξ‖ ^ 2 ≤ ε_tail := by
    rw [← h_tail_eq]
    exact setIntegral_mono_set hg2_int.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun ξ hξ => by
        simp only [mem_compl_iff, mem_Icc, not_and_or, not_le]; right; exact hξ)
  have h_left_le : ∫ ξ in Iic (-R), ‖𝓕 φ ξ‖ ^ 2 ≤ ε_tail := by
    rw [← h_tail_eq]
    have heq_io : ∫ ξ in Iic (-R), ‖𝓕 φ ξ‖ ^ 2 = ∫ ξ in Iio (-R), ‖𝓕 φ ξ‖ ^ 2 :=
      setIntegral_congr_set Iio_ae_eq_Iic.symm
    rw [heq_io]
    exact setIntegral_mono_set hg2_int.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun ξ hξ => by
        simp only [mem_compl_iff, mem_Icc, not_and_or, not_le]; left; exact hξ)
  have h_der_right : ∫ ξ in Ioi R, ‖𝓕 ψ ξ‖ ^ 2 ≤ (2 * π * R) ^ 2 * N2 :=
    (setIntegral_le_integral hg'2_int (Eventually.of_forall fun _ => sq_nonneg _)).trans hg'_planch
  have h_der_left : ∫ ξ in Iic (-R), ‖𝓕 ψ ξ‖ ^ 2 ≤ (2 * π * R) ^ 2 * N2 :=
    (setIntegral_le_integral hg'2_int (Eventually.of_forall fun _ => sq_nonneg _)).trans hg'_planch
  set D : ℝ := Real.sqrt (4 * π * R * Real.sqrt (ε_tail * N2))
  have hD_nn : 0 ≤ D := Real.sqrt_nonneg _
  have h_slit : ∀ x : ℝ, R ≤ |x| → ‖𝓕 φ x‖ ≤ D := by
    intro x hx
    have hsq_le : ‖𝓕 φ x‖ ^ 2 ≤ 4 * π * R * Real.sqrt (ε_tail * N2) := by
      have h_sqrt_der : Real.sqrt ((2 * π * R) ^ 2 * N2) = 2 * π * R * Real.sqrt N2 := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      have hsqrt_prod : Real.sqrt ε_tail * (2 * π * R * Real.sqrt N2) =
          2 * π * R * Real.sqrt (ε_tail * N2) := by
        calc Real.sqrt ε_tail * (2 * π * R * Real.sqrt N2)
            = 2 * π * R * (Real.sqrt ε_tail * Real.sqrt N2) := by ring
          _ = 2 * π * R * Real.sqrt (ε_tail * N2) := by rw [← Real.sqrt_mul hε_tail_nn]
      rcases le_or_gt 0 x with hx0 | hx0
      · have hxR : R ≤ x := by simpa [abs_of_nonneg hx0] using hx
        have hsob := halvingSobolev_right hderiv_g hg'_cont hg2_int hg'2_int hgg'_int x hxR
        calc ‖𝓕 φ x‖ ^ 2
            ≤ 2 * Real.sqrt (∫ t in Ioi R, ‖𝓕 φ t‖ ^ 2) *
                Real.sqrt (∫ t in Ioi R, ‖𝓕 ψ t‖ ^ 2) := hsob
          _ ≤ 2 * Real.sqrt ε_tail * Real.sqrt ((2 * π * R) ^ 2 * N2) := by gcongr
          _ = 4 * π * R * Real.sqrt (ε_tail * N2) := by rw [h_sqrt_der]; linarith
      · have hxR : x ≤ -R := by
          have : R ≤ -x := by simpa [abs_of_neg hx0] using hx
          linarith
        have hsob := halvingSobolev_left hderiv_g hg'_cont hg2_int hg'2_int hgg'_int x hxR
        calc ‖𝓕 φ x‖ ^ 2
            ≤ 2 * Real.sqrt (∫ t in Iic (-R), ‖𝓕 φ t‖ ^ 2) *
                Real.sqrt (∫ t in Iic (-R), ‖𝓕 ψ t‖ ^ 2) := hsob
          _ ≤ 2 * Real.sqrt ε_tail * Real.sqrt ((2 * π * R) ^ 2 * N2) := by gcongr
          _ = 4 * π * R * Real.sqrt (ε_tail * N2) := by rw [h_sqrt_der]; linarith
    calc ‖𝓕 φ x‖
        = Real.sqrt (‖𝓕 φ x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (4 * π * R * Real.sqrt (ε_tail * N2)) := Real.sqrt_le_sqrt hsq_le
  let H_ext : ℂ → ℂ := fun z =>
    ∫ t in Icc (-R) R, Complex.exp (-2 * π * Complex.I * z * (t : ℂ)) * φ t
  have hH_diff : Differentiable ℂ H_ext := fourier_holomorphic_ext hR hφ_meas hφ_int
  have hH_real : ∀ x : ℝ, H_ext (x : ℂ) = 𝓕 φ x := by
    intro x
    rw [Real.fourier_eq']
    have heq_f : ∀ t : ℝ, Complex.exp (-2 * π * Complex.I * (x : ℂ) * (t : ℂ)) * φ t =
        Complex.exp (↑(2 * π * -(t * x)) * Complex.I) * φ t := by
      intro t
      congr 2
      push_cast; ring
    simp_rw [H_ext, heq_f]
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ Icc (-R) R
    · simp [ht, mul_comm]
    · have habs : R < |t| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with ht | ht <;> [exact lt_abs.mpr (Or.inr (by linarith)); exact lt_abs.mpr (Or.inl ht)]
      simp [ht, hφ_supp t habs]
  have hH_bound : ∀ z : ℂ, ‖H_ext z‖ ≤ (∫ t in Icc (-R) R, ‖φ t‖) * Real.exp ((2 * π * R) * |z.im|) := by
    intro z
    have hpt : ∀ t ∈ Icc (-R) R, ‖Complex.exp (-2 * π * Complex.I * z * (t : ℂ)) * φ t‖ ≤
        Real.exp ((2 * π * R) * |z.im|) * ‖φ t‖ := by
      intro t ht
      rw [norm_mul, Complex.norm_exp]
      have hre : (-2 * π * Complex.I * z * (t : ℂ)).re = 2 * π * z.im * t := by
        simp [Complex.mul_re]
      rw [hre]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      have htR : |t| ≤ R := abs_le.mpr ht
      have hmul : z.im * t ≤ |z.im| * R :=
        (le_abs_self _).trans ((abs_mul z.im t).le.trans (mul_le_mul_of_nonneg_left htR (abs_nonneg _)))
      nlinarith [Real.pi_pos]
    have hint_lhs : IntegrableOn
        (fun t : ℝ => ‖Complex.exp (-2 * π * Complex.I * z * (t : ℂ)) * φ t‖) (Icc (-R) R) volume := by
      refine (hφ_int.integrableOn.norm.const_mul (Real.exp ((2 * π * R) * |z.im|))).mono'
        (((by fun_prop : Continuous fun t : ℝ =>
          Complex.exp (-2 * π * Complex.I * z * (t : ℂ))).aestronglyMeasurable.mul
            hφ_meas).norm.restrict) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hpt t ht
    calc ‖H_ext z‖
        ≤ ∫ t in Icc (-R) R, ‖Complex.exp (-2 * π * Complex.I * z * (t : ℂ)) * φ t‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Icc (-R) R, Real.exp ((2 * π * R) * |z.im|) * ‖φ t‖ :=
          setIntegral_mono_on hint_lhs (hφ_int.integrableOn.norm.const_mul _) measurableSet_Icc hpt
      _ = (∫ t in Icc (-R) R, ‖φ t‖) * Real.exp ((2 * π * R) * |z.im|) := by
          rw [integral_const_mul]; ring
  have hM0_nn : 0 ≤ ∫ t in Icc (-R) R, ‖φ t‖ := setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _
  have hslit_H : ∀ x : ℝ, R ≤ |x| → ‖H_ext (x : ℂ)‖ ≤ D := fun x hx => by
    rw [hH_real]; exact h_slit x hx
  have hmax := slit_plane_max_mod hH_diff hM0_nn (by positivity) hR hD_nn hH_bound hslit_H
  have hsq_Icc : ∀ x ∈ Icc (-R) R,
      ‖𝓕 φ x‖ ^ 2 ≤ 4 * π * R * Real.sqrt (ε_tail * N2) * Real.exp (4 * π * R ^ 2) := by
    intro x hx
    have hx_abs : |x| ≤ R := abs_le.mpr hx
    have h1 := hmax x hx_abs
    rw [hH_real] at h1
    have hsqrt_le : Real.sqrt (R ^ 2 - x ^ 2) ≤ R := by
      calc Real.sqrt (R ^ 2 - x ^ 2) ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg x])
        _ = R := Real.sqrt_sq hR.le
    have h2 : ‖𝓕 φ x‖ ≤ D * Real.exp (2 * π * R ^ 2) := by
      calc ‖𝓕 φ x‖
          ≤ D * Real.exp (2 * π * R * Real.sqrt (R ^ 2 - x ^ 2)) := h1
        _ ≤ D * Real.exp (2 * π * R * R) := by gcongr
        _ = D * Real.exp (2 * π * R ^ 2) := by ring_nf
    have hD_sq : D ^ 2 = 4 * π * R * Real.sqrt (ε_tail * N2) :=
      Real.sq_sqrt (by positivity)
    calc ‖𝓕 φ x‖ ^ 2
        ≤ (D * Real.exp (2 * π * R ^ 2)) ^ 2 := by gcongr
      _ = D ^ 2 * (Real.exp (2 * π * R ^ 2)) ^ 2 := by ring
      _ = 4 * π * R * Real.sqrt (ε_tail * N2) * Real.exp (4 * π * R ^ 2) := by
          rw [hD_sq, ← Real.exp_nat_mul]; congr 2; ring
  have hI_bound : I ≤ (8 * π * R ^ 2 * Real.exp (4 * π * R ^ 2)) * Real.sqrt (ε_tail * N2) := by
    have h_const_int : IntegrableOn
        (fun _ : ℝ => 4 * π * R * Real.sqrt (ε_tail * N2) * Real.exp (4 * π * R ^ 2))
        (Icc (-R) R) volume :=
      integrableOn_const (hs := by simp [Real.volume_Icc])
    calc I
        = ∫ x in Icc (-R) R, ‖𝓕 φ x‖ ^ 2 := rfl
      _ ≤ ∫ _ in Icc (-R) R, 4 * π * R * Real.sqrt (ε_tail * N2) * Real.exp (4 * π * R ^ 2) :=
          setIntegral_mono_on hg2_int.integrableOn h_const_int measurableSet_Icc hsq_Icc
      _ = (volume (Icc (-R) R)).toReal *
            (4 * π * R * Real.sqrt (ε_tail * N2) * Real.exp (4 * π * R ^ 2)) := by
          rw [setIntegral_const, smul_eq_mul, Measure.real_def]
      _ = (2 * R) * (4 * π * R * Real.sqrt (ε_tail * N2) * Real.exp (4 * π * R ^ 2)) := by
          rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
          congr 1; ring
      _ = (8 * π * R ^ 2 * Real.exp (4 * π * R ^ 2)) * Real.sqrt (ε_tail * N2) := by ring
  set K : ℝ := 8 * π * R ^ 2 * Real.exp (4 * π * R ^ 2)
  have hK_pos : 0 < K := by positivity
  set q : ℝ := ε_tail / N2
  have hq_nn : 0 ≤ q := by positivity
  have h1q : I / N2 = 1 - q := by
    dsimp [q, ε_tail]
    field_simp
    ring
  have h1q_le : 1 - q ≤ K * Real.sqrt q := by
    rw [← h1q, div_le_iff₀ hN2_pos]
    calc I ≤ K * Real.sqrt (ε_tail * N2) := hI_bound
      _ = K * (Real.sqrt (ε_tail / N2) * N2) := by
          congr 1
          conv_rhs => rw [← Real.sqrt_sq hN2_pos.le]
          rw [← Real.sqrt_mul (by positivity)]
          congr 1; field_simp; rw [Real.sqrt_sq hN2_pos.le]
      _ = K * Real.sqrt q * N2 := by ring
  set ε_R : ℝ := min (1 / 2 : ℝ) (1 / (256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2)))
  have hεR_le_q : ε_R ≤ q := by
    by_cases hq_half : 1 / 2 ≤ q
    · exact (min_le_left _ _).trans hq_half
    · push Not at hq_half
      have h_half_lt : (1 / 2 : ℝ) ≤ K * Real.sqrt q := by linarith
      have hsq : (1 / 4 : ℝ) ≤ K ^ 2 * q := by
        calc (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
          _ ≤ (K * Real.sqrt q) ^ 2 := by gcongr
          _ = K ^ 2 * (Real.sqrt q) ^ 2 := by ring
          _ = K ^ 2 * q := by rw [Real.sq_sqrt hq_nn]
      have hK2_eq : 4 * K ^ 2 = 256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2) := by
        dsimp [K]
        have hexp2 : Real.exp (4 * π * R ^ 2) ^ 2 = Real.exp (8 * π * R ^ 2) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        calc 4 * (8 * π * R ^ 2 * Real.exp (4 * π * R ^ 2)) ^ 2
            = 256 * π ^ 2 * R ^ 4 * Real.exp (4 * π * R ^ 2) ^ 2 := by ring
          _ = 256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2) := by rw [hexp2]
      have hdiv : 1 / (256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2)) ≤ q := by
        rw [← hK2_eq, div_le_iff₀ (by positivity)]
        linarith
      exact (min_le_right _ _).trans hdiv
  calc I = (1 - q) * N2 := by
        rw [← h1q, div_mul_cancel₀ _ hN2_pos.ne']
    _ ≤ (1 - ε_R) * N2 := by gcongr

/-- info: 'FormalResearch.ModularBootstrap.Integrality.integral_norm_sq_fourierIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_norm_sq_fourierIntegral

/-- info: 'FormalResearch.ModularBootstrap.Integrality.fourier_concentration_1d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_concentration_1d

end FormalResearch.ModularBootstrap.Integrality
