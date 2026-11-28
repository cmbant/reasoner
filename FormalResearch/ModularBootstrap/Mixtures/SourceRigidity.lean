module

public import FormalResearch.ModularBootstrap.Mixtures.VacProp
public import FormalResearch.ModularBootstrap.Mixtures.SourceO1Lower
public import FormalResearch.ModularBootstrap.Mixtures.Duality
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow
public import FormalResearch.ModularBootstrap.Duality.Primal.OneLevelMass

/-!
# Consumer ports for `CommonSource` spectral rigidity (`pmix:rigidity`(a))

`positive_mixtures.tex`, Theorem PM.12 (`pmix:rigidity`, part (a)): ports the Cardy-normalised
spectral measure `μ_S`, the spectral Poisson summation rule `sr:P1`, `SourceCrossingSequence`,
`SrcCombDesignData` / `DesignTest`, `SrcEventualCombData.toComb`, and Theorems `Σ₀` / `Σ`
unconditionally to every `C : CommonSource` by consuming `bumpEventualSrc` (`Mixtures.VacProp`),
`theorem_primal_src` (`Mixtures.Primal`), `pmix_duality_common` (`Mixtures.Duality`),
`pmix_o1_lower_common` (`Mixtures.SourceO1Lower`), and `vague_first_node_mass_of_lt`
(`Duality.Primal.OneLevelMass`).

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Assembly FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Ramped FormalResearch.ModularBootstrap.Upper.Positivity

/-! ### 1. Spectral measure `μ_S` for a `ShiftSource` and `CommonSource` -/

/-- The spectral weight `1 / (2π V_s(t) J(t))` of an atom at `t` for a source `src`. -/
noncomputable def spectralWeightSrc (src : ShiftSource) (c t : ℝ) : ℝ :=
  1 / (2 * π * src.cardyV (c / 12) t * jAiry c t)

lemma spectralWeightSrc_pos {C : CommonSource} {c : ℝ} (hc : 0 < c) (hc12 : 12 * C.a₀ ≤ c)
    {t : ℝ} (ht : 0 < t) : 0 < spectralWeightSrc C.src c t := by
  unfold spectralWeightSrc
  have hAt : C.F.At (c / 12) := C.at_ (by linarith)
  have hV := hAt.pos_V ht
  have hJ := jAiry_pos hc ht
  positivity

lemma measurable_spectralWeightSrc (src : ShiftSource) (c : ℝ) :
    Measurable (spectralWeightSrc src c) := by
  unfold spectralWeightSrc
  exact measurable_const.div ((measurable_const.mul (src.continuous_cardyV (c / 12)).measurable).mul
    (continuous_jAiry c).measurable)

/-- The density `ENNReal.ofReal (1 / (2π V_s J))` of the source spectral measure. -/
noncomputable def spectralDensitySrc (src : ShiftSource) (c t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (spectralWeightSrc src c t)

lemma measurable_spectralDensitySrc (src : ShiftSource) (c : ℝ) :
    Measurable (spectralDensitySrc src c) :=
  ENNReal.measurable_ofReal.comp (measurable_spectralWeightSrc src c)

/-- **The Cardy-normalised spectral measure `μ_S` of a source crossing measure** (`pmix:win-meas`):
`μ_S = u_*((2π V_s J)^{-1} ν|_{(0,∞)})`. -/
noncomputable def spectralMeasureSrc (src : ShiftSource) (c : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  ((ν.restrict (Ioi 0)).withDensity (spectralDensitySrc src c)).map (uAiry c)

lemma psiAirySrc_uAiry (src : ShiftSource) {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    psiAirySrc src c g (uAiry c t) = g t * src.cardyV (c / 12) t * jAiry c t := by
  unfold psiAirySrc
  rw [tAiry_uAiry hc ht]

lemma continuous_psiAirySrc (src : ShiftSource) {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) : Continuous (psiAirySrc src c g) := by
  unfold psiAirySrc
  have hgt : Continuous (fun u => g (tAiry c u)) :=
    hg.comp_continuous (continuous_tAiry c) fun u => tAiry_nonneg hc u
  have hVt : Continuous (fun u => src.cardyV (c / 12) (tAiry c u)) :=
    (src.continuous_cardyV (c / 12)).comp (continuous_tAiry c)
  have hJt : Continuous (fun u => jAiry c (tAiry c u)) :=
    (continuous_jAiry c).comp (continuous_tAiry c)
  exact (hgt.mul hVt).mul hJt

theorem integral_spectralMeasureSrc (C : CommonSource) {c : ℝ} (hc : 0 < c)
    (hc12 : 12 * C.a₀ ≤ c) (ν : Measure ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ u, f u ∂(spectralMeasureSrc C.src c ν) =
      ∫ t in Ioi 0, spectralWeightSrc C.src c t * f (uAiry c t) ∂ν := by
  unfold spectralMeasureSrc
  rw [integral_map (continuous_uAiry c).aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_spectralDensitySrc C.src c)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
  unfold spectralDensitySrc
  rw [ENNReal.toReal_ofReal (spectralWeightSrc_pos hc hc12 ht).le, smul_eq_mul]

theorem integrable_spectralMeasureSrc_iff (C : CommonSource) {c : ℝ} (hc : 0 < c)
    (hc12 : 12 * C.a₀ ≤ c) (ν : Measure ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (spectralMeasureSrc C.src c ν) ↔
      IntegrableOn (fun t => spectralWeightSrc C.src c t * f (uAiry c t)) (Ioi 0) ν := by
  unfold spectralMeasureSrc
  rw [integrable_map_measure hf.aestronglyMeasurable (continuous_uAiry c).aemeasurable,
    integrable_withDensity_iff_integrable_smul' (measurable_spectralDensitySrc C.src c)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
  unfold spectralDensitySrc
  rw [ENNReal.toReal_ofReal (spectralWeightSrc_pos hc hc12 ht).le, smul_eq_mul]
  rfl

private lemma spectralWeightSrc_mul_psiAirySrc (C : CommonSource) {c : ℝ} (hc : 0 < c)
    (hc12 : 12 * C.a₀ ≤ c) (g : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    spectralWeightSrc C.src c t * psiAirySrc C.src c g (uAiry c t) = g t / (2 * π) := by
  rw [psiAirySrc_uAiry C.src hc g ht.le]
  have hAt : C.F.At (c / 12) := C.at_ (by linarith)
  have hV := (hAt.pos_V ht).ne'
  have hJ := (jAiry_pos hc ht).ne'
  unfold spectralWeightSrc
  field_simp

theorem integral_spectralMeasureSrc_psiAiry (C : CommonSource) {c : ℝ} (hc : 0 < c)
    (hc12 : 12 * C.a₀ ≤ c) {ν : Measure ℝ} (hν0 : ν {0} = 0) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) :
    ∫ u, psiAirySrc C.src c g u ∂(spectralMeasureSrc C.src c ν) = (∫ t in Ici 0, g t ∂ν) / (2 * π) := by
  rw [integral_spectralMeasureSrc C hc hc12 ν (continuous_psiAirySrc C.src hc hg)]
  have : ∫ t in Ioi 0, spectralWeightSrc C.src c t * psiAirySrc C.src c g (uAiry c t) ∂ν =
      ∫ t in Ioi 0, g t / (2 * π) ∂ν :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => spectralWeightSrc_mul_psiAirySrc C hc hc12 g ht
  rw [this, integral_div, setIntegral_congr_set (Ioi_ae_eq_Ici' hν0)]

theorem integrable_spectralMeasureSrc_psiAiry_iff (C : CommonSource) {c : ℝ} (hc : 0 < c)
    (hc12 : 12 * C.a₀ ≤ c) {ν : Measure ℝ} (hν0 : ν {0} = 0) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) :
    Integrable (psiAirySrc C.src c g) (spectralMeasureSrc C.src c ν) ↔ IntegrableOn g (Ici 0) ν := by
  rw [integrable_spectralMeasureSrc_iff C hc hc12 ν (continuous_psiAirySrc C.src hc hg)]
  have h1 : IntegrableOn (fun t => spectralWeightSrc C.src c t * psiAirySrc C.src c g (uAiry c t))
      (Ioi 0) ν ↔ IntegrableOn (fun t => g t / (2 * π)) (Ioi 0) ν :=
    integrableOn_congr_fun (fun t ht => spectralWeightSrc_mul_psiAirySrc C hc hc12 g ht) measurableSet_Ioi
  rw [h1]
  have h2 : IntegrableOn (fun t => g t / (2 * π)) (Ioi 0) ν ↔ IntegrableOn g (Ioi 0) ν := by
    have hπ : (2 * π) ≠ 0 := by positivity
    simp only [div_eq_mul_inv]
    exact integrable_mul_const_iff (Ne.isUnit (inv_ne_zero hπ)) _
  rw [h2]
  exact integrableOn_congr_set_ae (Ioi_ae_eq_Ici' hν0)

private lemma exp_neg_pi_sqrt_le_rpow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
      Real.exp (-π * Real.sqrt (3 * t / c)) ≤ K * (1 + t) ^ (-(k : ℝ)) := by
  set α : ℝ := 3 * π ^ 2 / c
  have hα : 0 < α := by positivity
  refine ⟨max (2 ^ k) (2 ^ k * ((2 * k).factorial : ℝ) / α ^ k), by positivity, fun t ht => ?_⟩
  rcases le_or_gt t 1 with ht1 | ht1
  · have h1t : 1 + t ≤ 2 := by linarith
    have h1tp : 0 < 1 + t := by linarith
    have hexp : Real.exp (-π * Real.sqrt (3 * t / c)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, Real.sqrt_nonneg (3 * t / c)]
    have hpow : (1 : ℝ) ≤ 2 ^ k * (1 + t) ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg h1tp.le, Real.rpow_natCast]
      have : (1 + t) ^ k ≤ 2 ^ k := pow_le_pow_left₀ h1tp.le h1t k
      rwa [← div_eq_mul_inv, one_le_div (pow_pos h1tp k)]
    exact hexp.trans (hpow.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  · have h1tp : 0 < 1 + t := by linarith
    set u : ℝ := π * Real.sqrt (3 * t / c)
    have hu : 0 < u := by positivity
    have hpow_le : u ^ (2 * k) ≤ ((2 * k).factorial : ℝ) * Real.exp u := by
      have := Real.pow_div_factorial_le_exp u hu.le (2 * k)
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hu2k : u ^ (2 * k) = α ^ k * t ^ k := by
      have hu2 : u ^ 2 = α * t := by
        dsimp [u, α]
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring
      rw [pow_mul, hu2, mul_pow]
    rw [hu2k] at hpow_le
    have hexp : Real.exp (-u) ≤ ((2 * k).factorial : ℝ) / (α ^ k * t ^ k) := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos u) (by positivity)]
      linarith
    have h1t2 : 1 + t ≤ 2 * t := by linarith
    have hpow : (1 + t) ^ k ≤ 2 ^ k * t ^ k := by
      calc (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ h1tp.le h1t2 k
        _ = 2 ^ k * t ^ k := mul_pow 2 t k
    have hrhs : ((2 * k).factorial : ℝ) / (α ^ k * t ^ k) ≤
        (2 ^ k * ((2 * k).factorial : ℝ) / α ^ k) * (1 + t) ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg h1tp.le, Real.rpow_natCast, ← div_eq_mul_inv,
        div_le_div_iff₀ (by positivity) (pow_pos h1tp k)]
      calc ((2 * k).factorial : ℝ) * (1 + t) ^ k
          ≤ ((2 * k).factorial : ℝ) * (2 ^ k * t ^ k) := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (2 ^ k * ((2 * k).factorial : ℝ) / α ^ k) * (α ^ k * t ^ k) := by field_simp
    have hmax : (2 ^ k * ((2 * k).factorial : ℝ) / α ^ k) * (1 + t) ^ (-(k : ℝ)) ≤
        max (2 ^ k) (2 ^ k * ((2 * k).factorial : ℝ) / α ^ k) * (1 + t) ^ (-(k : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    rw [show -π * Real.sqrt (3 * t / c) = -u by dsimp [u]; ring]
    exact (hexp.trans hrhs).trans hmax

/-- **`sr:P1` (spectral Poisson summation) for a comb-decay test function and a `CommonSource`**:
using `pmix_crossing_a`, every `g ∈ Ā_{w,src}` obeying the comb bound
`|g(t)| ≤ C exp(-4π √(ct/12) - π √(3t/c))` has `Ψ^{mix}_g ∈ L¹(μ_S) ∩ L¹(du)` and
`∫ Ψ^{mix}_g dμ_S = ∫ Ψ^{mix}_g du`. -/
theorem spectral_poisson_summation_comb_src (C : CommonSource) {c : ℝ} (hc : 0 < c)
    (hc12 : 12 * C.a₀ ≤ c) (meas : SourceCrossingMeasure C.src (c / 12)) (hν0 : meas.ν {0} = 0)
    {g : ℝ → ℝ} (hg : TestClass C.src (c / 12) g) {C_g : ℝ} (hC_g : 0 ≤ C_g)
    (hdecay : ∀ t, 0 ≤ t →
      |g t| ≤ C_g * Real.exp (-4 * π * Real.sqrt ((c / 12) * t) - π * Real.sqrt (3 * t / c))) :
    Integrable (psiAirySrc C.src c g) (spectralMeasureSrc C.src c meas.ν) ∧
      Integrable (psiAirySrc C.src c g) ∧
      ∫ u, psiAirySrc C.src c g u ∂(spectralMeasureSrc C.src c meas.ν) =
        ∫ u, psiAirySrc C.src c g u := by
  have hAt : C.F.At (c / 12) := C.at_ (by linarith)
  set k : ℕ := C.src.w + 2
  have hk : (C.src.w + 1 : ℝ) / 2 < (k : ℝ) := by
    have : (k : ℝ) = (C.src.w : ℝ) + 2 := by push_cast [k]; ring
    linarith [show (0 : ℝ) ≤ C.src.w by positivity]
  obtain ⟨K, hK0, hK⟩ := exp_neg_pi_sqrt_le_rpow hc k
  have hdec' : ∀ t : ℝ, 0 ≤ t →
      |g t| ≤ (C_g * K) * (1 + t) ^ (-(k : ℝ)) * Real.exp (-4 * π * Real.sqrt ((c / 12) * t)) := by
    intro t ht
    have h1 := hdecay t ht
    have h2 := hK t ht
    have heq : Real.exp (-4 * π * Real.sqrt ((c / 12) * t) - π * Real.sqrt (3 * t / c)) =
        Real.exp (-π * Real.sqrt (3 * t / c)) * Real.exp (-4 * π * Real.sqrt ((c / 12) * t)) := by
      rw [← Real.exp_add]; ring_nf
    rw [heq] at h1
    calc |g t| ≤ C_g * (Real.exp (-π * Real.sqrt (3 * t / c)) * Real.exp (-4 * π * Real.sqrt ((c / 12) * t))) := h1
      _ ≤ C_g * (K * (1 + t) ^ (-(k : ℝ)) * Real.exp (-4 * π * Real.sqrt ((c / 12) * t))) := by
          gcongr
      _ = (C_g * K) * (1 + t) ^ (-(k : ℝ)) * Real.exp (-4 * π * Real.sqrt ((c / 12) * t)) := by ring
  obtain ⟨hint, heq⟩ := (pmix_crossing_a hAt meas hg).2.1 hk (by positivity) hdec'
  have hcont := hg.cont
  refine ⟨(integrable_spectralMeasureSrc_psiAiry_iff C hc hc12 hν0 hcont).2 hint.integrableOn,
    integrable_psiAirySrc hc hAt hg, ?_⟩
  rw [integral_spectralMeasureSrc_psiAiry C hc hc12 hν0 hcont, integral_psiAirySrc C.src hc]
  have hset : ∫ t in Ici 0, g t ∂meas.ν = ∫ t, g t ∂meas.ν := by
    show ∫ t, g t ∂(meas.ν.restrict (Ici 0)) = _
    rw [meas.restrict_Ici_eq]
  rw [hset]
  congr 1
  linarith

/-! ### 2. Local finiteness and positivity on `u ≤ u(τ)` -/

private lemma measure_Icc_lt_top_src {src : ShiftSource} {a : ℝ} (meas : SourceCrossingMeasure src a)
    (R : ℝ) : meas.ν (Icc 0 R) < ⊤ := by
  have h1 : IntegrableOn (fun t => Real.exp (-2 * π * 1 * t)) (Icc 0 R) meas.ν :=
    (meas.finite_laplace one_pos).mono_set Icc_subset_Ici_self
  have h2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 R) meas.ν := by
    refine (h1.const_mul (Real.exp (2 * π * R))).mono' aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := R))] with t ht
    rw [norm_one, ← Real.exp_add]
    exact Real.one_le_exp (by nlinarith [ht.2, Real.pi_pos])
  rcases (integrableOn_const_iff).1 h2 with h | h
  · simp at h
  · exact h

theorem spectralMeasureSrc_Ici_lt_top (C : CommonSource) {c : ℝ} (hc : 0 < c)
    (hc12 : 12 * C.a₀ ≤ c) (meas : SourceCrossingMeasure C.src (c / 12)) {τ : ℝ}
    (hτ : 0 < τ) (hgap : meas.ν (Iio τ) = 0) (A : ℝ) :
    spectralMeasureSrc C.src c meas.ν (Ici A) < ⊤ := by
  set T := tAiry c A
  have hAt : C.F.At (c / 12) := C.at_ (by linarith)
  have hcont : ContinuousOn (spectralWeightSrc C.src c) (Icc τ T) := by
    unfold spectralWeightSrc
    refine continuousOn_const.div ?_ fun t ht => ?_
    · exact ((continuous_const.mul (C.src.continuous_cardyV (c / 12))).mul
        (continuous_jAiry c)).continuousOn
    · have ht0 : 0 < t := hτ.trans_le ht.1
      have := hAt.pos_V ht0
      have := jAiry_pos hc ht0
      positivity
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  unfold spectralMeasureSrc
  rw [Measure.map_apply (continuous_uAiry c).measurable measurableSet_Ici,
    withDensity_apply _ ((continuous_uAiry c).measurable measurableSet_Ici)]
  have hsub : (uAiry c ⁻¹' Ici A) ≤ᵐ[meas.ν.restrict (Ioi 0)] Icc τ T := by
    have hae : ∀ᵐ t ∂meas.ν, τ ≤ t := by
      rw [ae_iff, show {t : ℝ | ¬ τ ≤ t} = Iio τ by ext t; simp]
      exact hgap
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))]
      with t h1 h2 h3
    refine ⟨h1, ?_⟩
    have := tAiry_antitone hc (show A ≤ uAiry c t from h3)
    rwa [tAiry_uAiry hc (mem_Ioi.1 h2).le] at this
  calc ∫⁻ t in uAiry c ⁻¹' Ici A, spectralDensitySrc C.src c t ∂(meas.ν.restrict (Ioi 0))
      ≤ ∫⁻ t in Icc τ T, spectralDensitySrc C.src c t ∂(meas.ν.restrict (Ioi 0)) :=
        lintegral_mono_set' hsub
    _ ≤ ∫⁻ t in Icc τ T, ENNReal.ofReal M ∂(meas.ν.restrict (Ioi 0)) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        unfold spectralDensitySrc
        refine ENNReal.ofReal_le_ofReal ?_
        have := hM t ht
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
    _ = ENNReal.ofReal M * (meas.ν.restrict (Ioi 0)) (Icc τ T) := setLIntegral_const _ _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        calc (meas.ν.restrict (Ioi 0)) (Icc τ T) ≤ meas.ν (Icc τ T) := Measure.restrict_le_self _
          _ ≤ meas.ν (Icc 0 T) := measure_mono (Icc_subset_Icc hτ.le le_rfl)
          _ < ⊤ := measure_Icc_lt_top_src meas T

theorem isLocallyFiniteMeasure_spectralMeasureSrc (C : CommonSource) {c : ℝ} (hc : 0 < c)
    (hc12 : 12 * C.a₀ ≤ c) (meas : SourceCrossingMeasure C.src (c / 12)) {τ : ℝ}
    (hτ : 0 < τ) (hgap : meas.ν (Iio τ) = 0) :
    IsLocallyFiniteMeasure (spectralMeasureSrc C.src c meas.ν) := by
  refine ⟨fun x => ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩⟩
  exact lt_of_le_of_lt (measure_mono Icc_subset_Ici_self)
    (spectralMeasureSrc_Ici_lt_top C hc hc12 meas hτ hgap (x - 1))

lemma psiAirySrc_nonneg (C : CommonSource) {c : ℝ} (hc : 0 < c) (hc12 : 12 * C.a₀ ≤ c)
    {τ : ℝ} (hτ : 0 ≤ τ) {g : ℝ → ℝ} (hg : ∀ t, τ ≤ t → 0 ≤ g t) {u : ℝ}
    (hu : u ≤ uAiry c τ) : 0 ≤ psiAirySrc C.src c g u := by
  unfold psiAirySrc
  have h1 : τ ≤ tAiry c u := by
    have := tAiry_antitone hc hu
    rwa [tAiry_uAiry hc hτ] at this
  have h2 := hg _ h1
  have hAt : C.F.At (c / 12) := C.at_ (by linarith)
  have h3 := hAt.nonneg_V (hτ.trans h1)
  have h4 : 0 ≤ jAiry c (tAiry c u) := by
    rw [jAiry_tAiry hc]
    have := bAiry_nonneg c u
    have := betaTip_pos
    have : 0 ≤ c ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hc.le _
    positivity
  positivity

/-! ### 3. `SourceCrossingSequence`, `SrcCombDesignData`, and Property `sr:P` -/

/-- A sequence of mixed/common-source crossing measures at charges `c_j → ∞` and positive gaps `τ_j`. -/
structure SourceCrossingSequence (C : CommonSource) where
  c : ℕ → ℝ
  τ : ℕ → ℝ
  meas : ∀ j, SourceCrossingMeasure C.src (c j / 12)
  tendsto_c : Tendsto c atTop atTop
  c_pos : ∀ j, 0 < c j
  shift_le : ∀ j, 12 * C.a₀ ≤ c j
  τ_pos : ∀ j, 0 < τ j
  gap : ∀ j, (meas j).ν (Iio (τ j)) = 0

namespace SourceCrossingSequence

variable {C : CommonSource} (S : SourceCrossingSequence C)

/-- The spectral measures `μ_S` of `S` (`pmix:win-meas`). -/
noncomputable def μS (j : ℕ) : Measure ℝ :=
  spectralMeasureSrc C.src (S.c j) (S.meas j).ν

lemma zero_null (j : ℕ) : (S.meas j).ν {0} = 0 :=
  measure_mono_null (fun t (ht : t = 0) => by simp [ht, S.τ_pos j]) (S.gap j)

instance (j : ℕ) : IsLocallyFiniteMeasure (S.μS j) :=
  isLocallyFiniteMeasure_spectralMeasureSrc C (S.c_pos j) (S.shift_le j) (S.meas j) (S.τ_pos j) (S.gap j)

lemma supp (j : ℕ) : S.μS j (Ioi (uAiry (S.c j) (S.τ j))) = 0 := by
  unfold μS spectralMeasureSrc
  rw [Measure.map_apply (continuous_uAiry (S.c j)).measurable measurableSet_Ioi]
  refine withDensity_absolutelyContinuous _ _ ?_
  have hsub : uAiry (S.c j) ⁻¹' Ioi (uAiry (S.c j) (S.τ j)) ⊆ Iio (S.τ j) := fun t ht => by
    by_contra h
    exact absurd (uAiry_antitone (S.c_pos j) (not_lt.1 h)) (not_le.2 ht)
  refine le_antisymm ?_ bot_le
  calc ((S.meas j).ν.restrict (Ioi 0)) (uAiry (S.c j) ⁻¹' Ioi (uAiry (S.c j) (S.τ j)))
      ≤ (S.meas j).ν (uAiry (S.c j) ⁻¹' Ioi (uAiry (S.c j) (S.τ j))) := Measure.restrict_le_self _
    _ ≤ (S.meas j).ν (Iio (S.τ j)) := measure_mono hsub
    _ = 0 := S.gap j

end SourceCrossingSequence

/-- Gap condition from `pmix_o1_lower_common` (and any `τ_j ≥ T_*(c_j) - D` or `T_V ≤ τ`). -/
theorem gapCondition_of_commonSource_lower (c τ : ℕ → ℝ) (hc : Tendsto c atTop atTop)
    {c₀ D : ℝ} (hlo : ∀ j, c₀ ≤ c j → TStar (c j) - D ≤ τ j) :
    GapCondition c τ := by
  intro δ hδ
  have h1 : ∀ᶠ j in atTop, c₀ ≤ c j := hc.eventually_ge_atTop c₀
  have h2 : ∀ᶠ j in atTop, D ≤ δ * (c j) ^ ((1 : ℝ) / 3) := by
    have hpow : Tendsto (fun j => δ * (c j) ^ ((1 : ℝ) / 3)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 3) |>.comp hc).const_mul_atTop hδ
    exact hpow.eventually_ge_atTop D
  filter_upwards [h1, h2] with j hj1 hj2
  linarith [hlo j hj1]

/-- For every `CommonSource`, any crossing measure sequence with `T_V(c_j) ≤ τ_j` obeys `(Gap)`. -/
theorem gapCondition_of_commonSource (C : CommonSource) {c τ : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hτ : ∀ j, C.src.T_V (c j) ≤ τ j) : GapCondition c τ := by
  obtain ⟨c₁, D_m, _, _, _, _, h⟩ := pmix_o1_common C
  refine gapCondition_of_commonSource_lower c τ hc (c₀ := c₁) (D := D_m) fun j hj => ?_
  obtain ⟨hlow, hle, _⟩ := h hj
  linarith [hτ j]

/-- **`pmix:rigidity`(a), optimal sequence existence**: for every `cSeq → ∞` above `c₀`, there is
a `SourceCrossingSequence C` attaining `τ j = C.src.T_V (cSeq j)` with positive mass arbitrarily
close to `τ j` and obeying `(Gap)`. -/
theorem src_exists_optimalCrossingSequence (C : CommonSource) :
    ∃ c₀ : ℝ, 12 * C.a₀ ≤ c₀ ∧ ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : SourceCrossingSequence C, S.c = cSeq ∧
        (∀ j, S.τ j = C.src.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        GapCondition S.c S.τ := by
  obtain ⟨c₁, _, _, _, _, h12, h⟩ := pmix_o1_common C
  set c₀ := max c₁ 1
  have hc₀12 : 12 * C.a₀ ≤ c₀ := h12.trans (le_max_left _ _)
  refine ⟨c₀, hc₀12, fun cSeq hc hge => ?_⟩
  have hcpos : ∀ j, 0 < cSeq j := fun j => lt_of_lt_of_le zero_lt_one ((le_max_right c₁ 1).trans (hge j))
  have hc12 : ∀ j, 12 * C.a₀ ≤ cSeq j := fun j => hc₀12.trans (hge j)
  have hbundle : ∀ j, DualityBundleS C (cSeq j) := fun j => (pmix_duality_common C (hc12 j)).some
  choose meas hmeas using fun j => (hbundle j).duality_E_b_empty.2.1
  let S : SourceCrossingSequence C :=
    { c := cSeq
      τ := fun j => C.src.T_V (cSeq j)
      meas := meas
      tendsto_c := hc
      c_pos := hcpos
      shift_le := hc12
      τ_pos := fun j => (hbundle j).T_V_pos
      gap := fun j => by
        have hm := hmeas j
        rwa [compl_Ici] at hm }
  refine ⟨S, rfl, fun _ => rfl, fun j ε hε => ?_, ?_⟩
  · by_contra hzero
    have hle0 : (meas j).ν (Iio (C.src.T_V (cSeq j) + ε)) = 0 :=
      le_antisymm (not_lt.1 hzero) bot_le
    have hc0 : (meas j).ν (Ici (C.src.T_V (cSeq j) + ε))ᶜ = 0 := by
      rwa [compl_Ici]
    have hgr := (hbundle j).duality_E_b_empty.2.2
    have hle : C.src.T_V (cSeq j) + ε ≤ C.src.T_V (cSeq j) :=
      hgr.2 ⟨by linarith [(hbundle j).T_V_pos], meas j, hc0⟩
    linarith
  · exact gapCondition_of_commonSource C hc fun j => le_rfl

/-- Comb data `(P1)–(P4)` of Property `sr:P` for a `SourceCrossingSequence`. -/
structure SrcCombDesignData {C : CommonSource} (S : SourceCrossingSequence C) (D : Window) where
  g : ℕ → ℝ → ℝ
  scale : ℕ → ℝ
  tf : ℕ → ℝ
  scale_pos : ∀ j, 0 < scale j
  testClass : ∀ j, TestClass C.src (S.c j / 12) (g j)
  decay : ∀ j, ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ t : ℝ, 0 ≤ t →
    |g j t| ≤ C0 * Real.exp (-4 * π * Real.sqrt ((S.c j / 12) * t) - π * Real.sqrt (3 * t / S.c j))
  tf_nonneg : ∀ j, 0 ≤ tf j + 1
  g_nonneg : ∀ j, ∀ t : ℝ, tf j + 1 ≤ t → 0 ≤ g j t
  theta_tendsto : Tendsto (fun j => uAiry (S.c j) (tf j + 1)) atTop (𝓝 D.uF)
  window_limit : TendstoLocallyUniformly (fun j u => scale j * psiAirySrc C.src (S.c j) (g j) u) D.W atTop
  limsup_le : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
    ∫ u, scale j * psiAirySrc C.src (S.c j) (g j) u ≤ D.V + ε

/-- `(P1)–(P4)` yield a `DesignTest S.μS D`. -/
noncomputable def SrcCombDesignData.toDesignTest {C : CommonSource} {S : SourceCrossingSequence C}
    {D : Window} (CD : SrcCombDesignData S D) : DesignTest S.μS D :=
  let hcomb : ∀ j, Integrable (psiAirySrc C.src (S.c j) (CD.g j)) (S.μS j) ∧
      Integrable (psiAirySrc C.src (S.c j) (CD.g j)) ∧
      ∫ u, psiAirySrc C.src (S.c j) (CD.g j) u ∂(S.μS j) =
        ∫ u, psiAirySrc C.src (S.c j) (CD.g j) u := fun j => by
    obtain ⟨C0, hC0, hdec⟩ := CD.decay j
    exact spectral_poisson_summation_comb_src C (S.c_pos j) (S.shift_le j) (S.meas j)
      (S.zero_null j) (CD.testClass j) hC0 hdec
  { Ψ := fun j u => CD.scale j * psiAirySrc C.src (S.c j) (CD.g j) u
    θ := fun j => uAiry (S.c j) (CD.tf j + 1)
    continuous := fun j =>
      continuous_const.mul (continuous_psiAirySrc C.src (S.c_pos j) (CD.testClass j).cont)
    integrable_mu := fun j => (hcomb j).1.const_mul (CD.scale j)
    integrable_vol := fun j => (hcomb j).2.1.const_mul (CD.scale j)
    crossing := fun j => by simp only [integral_const_mul, (hcomb j).2.2]
    nonneg := fun j u hu => mul_nonneg (CD.scale_pos j).le
      (psiAirySrc_nonneg C (S.c_pos j) (S.shift_le j) (CD.tf_nonneg j) (CD.g_nonneg j) hu)
    theta_tendsto := CD.theta_tendsto
    window_limit := CD.window_limit
    limsup_le := CD.limsup_le }

theorem src_designPropertyP_of_comb {C : CommonSource} (S : SourceCrossingSequence C) {𝒟 : Set Window}
    (h : ∀ D ∈ 𝒟, Nonempty (SrcCombDesignData S D)) : DesignPropertyP S.μS 𝒟 :=
  fun D hD => ⟨(h D hD).some.toDesignTest⟩

open Classical in
/-- Convert `SrcEventualCombData` (from `VacProp` / `VacTwoZero`) into `SrcCombDesignData`
for any `SourceCrossingSequence`. -/
noncomputable def SrcEventualCombData.toComb {C : CommonSource} {D : Window}
    (E : SrcEventualCombData C.src D) (S : SourceCrossingSequence C) : SrcCombDesignData S D := by
  let good : ℝ → Prop := fun c => 0 < c ∧ 0 < E.scale c ∧ TestClass C.src (c / 12) (E.g c) ∧
    (∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ t : ℝ, 0 ≤ t →
      |E.g c t| ≤ C0 * Real.exp (-4 * π * Real.sqrt (c / 12 * t) - π * Real.sqrt (3 * t / c))) ∧
    0 ≤ E.tf c + 1 ∧ ∀ t : ℝ, E.tf c + 1 ≤ t → 0 ≤ E.g c t
  have hev : ∀ᶠ j in atTop, good (S.c j) := S.tendsto_c.eventually E.good
  exact
    { g := fun j => if good (S.c j) then E.g (S.c j) else fun _ => 0
      scale := fun j => if good (S.c j) then E.scale (S.c j) else 1
      tf := fun j => if good (S.c j) then E.tf (S.c j) else 0
      scale_pos := fun j => by
        by_cases h : good (S.c j)
        · simp only [h, ite_true]; exact h.2.1
        · simp [h]
      testClass := fun j => by
        by_cases h : good (S.c j)
        · simp only [h, ite_true]; exact h.2.2.1
        · simp only [h, ite_false]; exact testClass_zero_src C.src (S.c j / 12)
      decay := fun j => by
        by_cases h : good (S.c j)
        · simp only [h, ite_true]; exact h.2.2.2.1
        · simp only [h, ite_false]; exact ⟨0, le_rfl, fun _ _ => by simp⟩
      tf_nonneg := fun j => by
        by_cases h : good (S.c j)
        · simp only [h, ite_true]; exact h.2.2.2.2.1
        · simp [h]
      g_nonneg := fun j t ht => by
        by_cases h : good (S.c j)
        · simp only [h, ite_true] at ht ⊢; exact h.2.2.2.2.2 t ht
        · simp [h]
      theta_tendsto := by
        refine (E.theta.comp S.tendsto_c).congr' ?_
        filter_upwards [hev] with j hj
        simp [hj]
      window_limit := by
        rw [Metric.tendstoLocallyUniformly_iff]
        intro ε hε x
        refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
        have h1 := E.window (|x| + 1) (by positivity) (ε / 2) (half_pos hε)
        have h2 := S.tendsto_c.eventually h1
        filter_upwards [hev, h2] with j hj h2j y hy
        have hy' : y ∈ Icc (-(|x| + 1)) (|x| + 1) :=
          ⟨by linarith [hy.1, neg_abs_le x], by linarith [hy.2, le_abs_self x]⟩
        have := h2j y hy'
        simp only [hj, ite_true]
        rw [Real.dist_eq, abs_sub_comm]
        linarith
      limsup_le := fun ε hε => by
        have h1 := S.tendsto_c.eventually (E.limsup ε hε)
        filter_upwards [hev, h1] with j hj h1j
        simp only [hj, ite_true]
        exact h1j }

/-! ### 4. Unconditional `sr:P`, `Σ₀`, `Σ`, and `pmix:rigidity`(a) for `CommonSource` -/

/-- **Property `sr:P` for `designClass` on every `CommonSource`** (`pmix:vac` -> `sr:P`). -/
theorem src_designPropertyP (C : CommonSource) (S : SourceCrossingSequence C) :
    DesignPropertyP S.μS designClass := by
  refine src_designPropertyP_of_comb S fun D hD => ?_
  obtain ⟨N, η, d, hη, hN, hη1, rfl⟩ := hD
  exact ⟨(bumpEventualSrc C N hN hη hη1 (designSigma1 d) (designWin N hη d)
    (designWin_W_eq_sig N hη d) (designWin_uF_eq_sig N hη d)).toComb S⟩

/-- **Property `sr:P` for `displacedClassX` on every `CommonSource`**. -/
theorem src_displacedPropertyP (C : CommonSource) (S : SourceCrossingSequence C) :
    DesignPropertyP S.μS displacedClassX := by
  refine src_designPropertyP_of_comb S fun D hD => ?_
  obtain ⟨N, η, e, d, hη, hH, hN, hη1, he, rfl⟩ := hD
  refine ⟨(bumpEventualSrc C N hN hη hη1 (dispSigma d e) _ ?_ ?_).toComb S⟩
  · funext u
    rw [profWin_W]
    show (profW (dispSite N e) (designWidthU N η) d (u : ℂ)).re =
      (sigWindowW N η (dispSigma d e) (u : ℂ)).re
    rw [sigWindowW_dispSite N η d e he]
  · rw [profWin_uF, dispSigma_one]

/-- **Theorem `Σ₀` for any `CommonSource` crossing sequence obeying `(Gap)`**
(`pmix:rigidity`(a), `sr:Sigma0`). -/
theorem src_sigmaZero_crossing (C : CommonSource) (S : SourceCrossingSequence C)
    (hgap : GapCondition S.c S.τ) : SigmaZeroConclusion S.c S.τ S.μS := by
  have F := (sameSiteFamily_designClass designTailBounds).some
  exact ⟨theorem_sigma_zero_a S.tendsto_c hgap S.μS S.supp (src_designPropertyP C S) F,
    fun _ hρ => theorem_sigma_zero_b S.tendsto_c hgap S.μS S.supp (src_designPropertyP C S) F hρ⟩

/-- **Theorem `Σ` for any `CommonSource` crossing sequence obeying `(Gap)`**
(`pmix:rigidity`(a), `sr:Sigma`): unconditional vague convergence `μ_S → airyMeasure`,
locally bounded, no escaping mass, and exact Airy node weights. -/
theorem src_sigma_crossing (C : CommonSource) (S : SourceCrossingSequence C)
    (hgap : GapCondition S.c S.τ) : SigmaConclusion S.μS :=
  theorem_sigma S.tendsto_c hgap S.μS S.supp
    (designPropertyP_union (src_designPropertyP C S) (src_displacedPropertyP C S))
    (SameSiteFamily.mono subset_union_left (sameSiteFamily_designClass designTailBounds).some)
    (DisplacedFamily.mono (displacedClass_subset.trans subset_union_right) displacedFamily)
    farFamily

/-- First-node Airy cluster mass recovery (`D₁(r) / (2π V_s J) → Ai'(a₁)^{-2}`) for any
`CommonSource` sequence obeying `(Gap)` and `0 < r < |a₁ - a₂|`. -/
theorem src_first_node_mass_of_gap (C : CommonSource) (S : SourceCrossingSequence C)
    (hgap : GapCondition S.c S.τ) {r : ℝ} (hr : 0 < r) (hr_sep : r < |airyZero 1 - airyZero 2|) :
    Tendsto (fun j => (S.μS j (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal) atTop
      (𝓝 (airyNodeWeight 0)) ∧
    Tendsto (fun j => (S.μS j (Icc (airyZero 1 - r) (airyZero 1 + r))).toReal) atTop
      (𝓝 (airyNodeWeight 0)) :=
  FixedWeight.vague_first_node_mass_of_lt (src_sigma_crossing C S hgap).2.2.2.1 hr hr_sep

/-- **`pmix:rigidity`(a), unconditional extremal form**: for every `CommonSource` and every sequence
`cSeq → ∞` above `c₀`, there is an optimal crossing sequence with `τ_j = C.src.T_V (cSeq j)`
satisfying both `Σ₀` and `Σ` (vague convergence `μ_S → airyMeasure`, locally bounded, no escaping
mass, Airy weights). -/
theorem src_sigma_unconditional (C : CommonSource) :
    ∃ c₀ : ℝ, 12 * C.a₀ ≤ c₀ ∧ ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : SourceCrossingSequence C, S.c = cSeq ∧
        (∀ j, S.τ j = C.src.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        SigmaZeroConclusion S.c S.τ S.μS ∧ SigmaConclusion S.μS := by
  obtain ⟨c₀, hc₀, h⟩ := src_exists_optimalCrossingSequence C
  refine ⟨c₀, hc₀, fun cSeq hc hge => ?_⟩
  obtain ⟨S, hS, hτ, hchg, hgap⟩ := h cSeq hc hge
  exact ⟨S, hS, hτ, hchg, src_sigmaZero_crossing C S hgap, src_sigma_crossing C S hgap⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.spectral_poisson_summation_comb_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spectral_poisson_summation_comb_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.src_designPropertyP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms src_designPropertyP

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.src_displacedPropertyP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms src_displacedPropertyP

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.src_sigma_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms src_sigma_crossing

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.src_sigma_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms src_sigma_unconditional

end FormalResearch.ModularBootstrap.Mixtures
