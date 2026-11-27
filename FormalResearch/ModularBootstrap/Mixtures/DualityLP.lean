module

public import FormalResearch.ModularBootstrap.Mixtures.ThermalSeparation
public import FormalResearch.ModularBootstrap.LP.Reference
public import FormalResearch.ModularBootstrap.LP.OddFunctional
public import FormalResearch.ModularBootstrap.LP.DerivLimitI
public import FormalResearch.ModularBootstrap.LP.DerivLimitII
public import FormalResearch.ModularBootstrap.LP.DerivLimit

/-!
# Derivative-limit linear programming (`ds:LP` (i)–(iii)) for atomic shift sources

Source: `CFT/modular_bootstrap/paper/dual_spectrum.tex`, Theorem LP (`ds:LP`) and
`dual_spectrum_limit.tex`, Section `dsl:LPproof`, transferred from `FixedWeightProblem` to any
`ShiftSource` with non-negative Cardy weight (`FloorData.At` or `SourceDualSetupCore`).

All `ds:cay`, `ds:cont`, Laguerre odd-polynomial spans (`oddSpan`, `OC`, `OCall`),
coercive majorant (`positive_ray`), and polynomial moment compactness (`poly_compact_ref`) are reused
directly from `FormalResearch.ModularBootstrap.LP`.

* `refMeasS`, `analyticOnNhd_srcFun`, `integral_xiW_expTilt_refS`: reference measure
  `μ_λ = e^{-2π t} ρ_λ(t) dt` and analyticity of the source `v_λ`.
* `OddFeasibleS`, `thrNS`, `thrInfS`: finite-order odd-Laguerre feasibility and thresholds.
* `ds_LP_i_src`, `ds_LP_b_imp_a_src`, `ds_LP_ii_src`, `ds_LP_iii_src`: Theorem LP (i)–(iii) for
  `ShiftSource` / `FloorData.At`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.FixedWeight
open FormalResearch.ModularBootstrap.LP

/-! ### Reference measure `μ_λ` and analyticity of `src.srcFun` -/

/-- The reference density `e^{-2πt} ρ_λ(t)`. -/
noncomputable def refDensityS (src : ShiftSource) (a t : ℝ) : ℝ :=
  Real.exp (-2 * π * t) * src.cardyDensity a t

lemma measurable_refDensityS (src : ShiftSource) (a : ℝ) : Measurable (refDensityS src a) := by
  unfold refDensityS ShiftSource.cardyDensity
  exact (Continuous.mul (by fun_prop) (continuous_const.mul (src.continuous_cardyV a))).measurable

/-- The reference measure `dμ_λ = e^{-2πt} ρ_λ(t) dt` on `(0, ∞)`. -/
noncomputable def refMeasS (src : ShiftSource) (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (refDensityS src a t)

lemma refMeasS_Iio (src : ShiftSource) (a : ℝ) : refMeasS src a (Iio 0) = 0 := by
  unfold refMeasS
  rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have : (Iio (0 : ℝ)) ∩ Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun h => h.le
  rw [this]; simp

lemma refMeasS_ae_nonneg (src : ShiftSource) (a : ℝ) : ∀ᵐ t ∂(refMeasS src a), 0 ≤ t := by
  have : ∀ᵐ t ∂(refMeasS src a), t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 (refMeasS_Iio src a)
  filter_upwards [this] with t ht using not_lt.1 ht

lemma refDensityS_nonneg {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ refDensityS src a t := by
  unfold refDensityS ShiftSource.cardyDensity
  have := hnn t ht
  have := Real.pi_pos
  positivity

lemma integral_refMeasS {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    (g : ℝ → ℝ) :
    ∫ t, g t ∂refMeasS src a =
      ∫ t in Ioi 0, Real.exp (-2 * π * t) * src.cardyDensity a t * g t := by
  unfold refMeasS
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_refDensityS src a).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (refDensityS_nonneg hnn (mem_Ioi.1 ht).le)]
  rfl

lemma integrable_refMeasS_iff {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    (g : ℝ → ℝ) :
    Integrable g (refMeasS src a) ↔
      IntegrableOn (fun t => Real.exp (-2 * π * t) * src.cardyDensity a t * g t) (Ioi 0) := by
  unfold refMeasS
  rw [integrable_withDensity_iff_integrable_smul' (measurable_refDensityS src a).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (refDensityS_nonneg hnn (mem_Ioi.1 ht).le)]
  rfl

/-- `μ_λ` has an `e^{ct}` moment for every `c < 2π`. -/
lemma integrable_exp_refS {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    {c : ℝ} (hc : c < 2 * π) :
    Integrable (fun t => Real.exp (c * t)) (refMeasS src a) := by
  rw [integrable_refMeasS_iff hnn]
  have hβ : 0 < (2 * π - c) / (2 * π) := div_pos (by linarith) (by positivity)
  have h := (src.cardyV_laplace a hβ).1
  have h2 : IntegrableOn (fun t => 2 * π * (src.cardyV a t *
      Real.exp (-2 * π * ((2 * π - c) / (2 * π)) * t))) (Ioi 0) := h.const_mul (2 * π)
  refine (integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi).1 h2
  unfold ShiftSource.cardyDensity
  have e : Real.exp (-2 * π * t) * Real.exp (c * t) =
      Real.exp (-2 * π * ((2 * π - c) / (2 * π)) * t) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have : Real.exp (-2 * π * t) * (2 * π * src.cardyV a t) * Real.exp (c * t) =
      2 * π * (src.cardyV a t * (Real.exp (-2 * π * t) * Real.exp (c * t))) := by ring
  rw [this, e]

lemma integrable_exp_refS_pi {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t) :
    Integrable (fun t => Real.exp (π * t)) (refMeasS src a) :=
  integrable_exp_refS hnn (by linarith [Real.pi_pos])

lemma integrable_oddSpan_refS {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    {N : ℕ} {p : ℝ → ℝ} (hp : p ∈ oddSpan (src.w : ℝ) N) :
    Integrable p (refMeasS src a) := by
  have hw : 0 < (src.w : ℝ) := by exact_mod_cast src.hw
  refine Submodule.span_induction (p := fun p _ => Integrable p (refMeasS src a)) ?_ ?_ ?_ ?_ hp
  · rintro f ⟨k, hk, -, rfl⟩
    refine Integrable.mono' ((integrable_exp_refS_pi hnn).const_mul ((2 * momM ((1 + (src.w : ℝ)) / π) * k) ^ k))
      (continuous_lagP _ k).aestronglyMeasurable ?_
    filter_upwards [refMeasS_ae_nonneg src a] with t ht
    rw [Real.norm_eq_abs]
    exact (lagP_oddFam hw).abs_le_exp hk ht
  · exact integrable_zero _ _ _
  · intro f g _ _ hf hg; exact hf.add hg
  · intro c f _ hf; exact hf.smul c

lemma integrable_OCall_refS {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    {f : C(ℝ, ℝ)} (hf : f ∈ OCall (src.w : ℝ)) : Integrable (f : ℝ → ℝ) (refMeasS src a) := by
  obtain ⟨N, hN⟩ := exists_N_of_mem_OCall hf
  exact integrable_oddSpan_refS hnn (coe_mem_oddSpan_of_mem_OC hN)

lemma gVac_expPolyS {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    (p : ℝ → ℝ) :
    src.gVac a (fun t => Real.exp (-2 * π * t) * p t) = -∫ t, p t ∂refMeasS src a := by
  rw [integral_refMeasS hnn]
  unfold ShiftSource.gVac ShiftSource.cardyDensity
  have : ∀ t : ℝ, Real.exp (-2 * π * t) * p t * src.cardyV a t =
      (Real.exp (-2 * π * t) * (2 * π * src.cardyV a t) * p t) / (2 * π) := fun t => by
    field_simp
  simp_rw [this]
  rw [integral_div]
  field_simp

/-- The source function `src.srcFun a` is real-analytic on `(0, ∞)` (in fact entire). -/
lemma analyticOnNhd_srcFun (src : ShiftSource) (a : ℝ) : AnalyticOnNhd ℝ (src.srcFun a) (Ioi 0) := by
  intro β _
  have h : AnalyticAt ℝ (fun x : ℝ => ∑ j, src.coef j * Real.exp (2 * π * (a - src.shift j) * x)) β :=
    Finset.analyticAt_fun_sum _ fun j _ =>
      analyticAt_const.mul (analyticAt_rexp.comp (analyticAt_const.mul analyticAt_id))
  have e : src.srcFun a = fun x => ∑ j, src.coef j * Real.exp (2 * π * (a - src.shift j) * x) := by
    ext x; rfl
  rw [e]; exact h

lemma integral_xiW_expTilt_refS' {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    (β : ℝ) :
    ∫ t, xiW (src.w : ℝ) β t ∂expTilt (refMeasS src a) =
      ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyDensity a t := by
  rw [integral_expTilt, integral_refMeasS hnn]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have : Real.exp (-2 * π * t) * Real.exp (2 * π * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc Real.exp (-2 * π * t) * src.cardyDensity a t * (Real.exp (2 * π * t) * xiW (src.w : ℝ) β t)
      = (Real.exp (-2 * π * t) * Real.exp (2 * π * t)) * (src.cardyDensity a t * xiW (src.w : ℝ) β t) := by ring
    _ = thermalDiff src.w β t * src.cardyDensity a t := by
        rw [this]; unfold thermalDiff xiW; ring

lemma integral_xiW_expTilt_refS {src : ShiftSource} {a : ℝ} (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    {β : ℝ} (hβ : 0 < β) :
    ∫ t, xiW (src.w : ℝ) β t ∂expTilt (refMeasS src a) =
      β ^ (-(src.w : ℝ)) * src.srcFun a (1 / β) - src.srcFun a β := by
  rw [integral_xiW_expTilt_refS' hnn]
  rw [integral_cardyDensity_eq_neg_gVac, gVac_thermalDiff_src_eq src a hβ]
  simp [one_div]

/-! ### `OddFeasibleS`, `thrNS`, `thrInfS`, and Theorem LP (`ds:LP`) -/

/-- A finite odd-Laguerre test on `X`: `p ∈ O_N`, `g = e^{-2πt} p ≥ 0` on `X`, `g_vac > 0`. -/
def OddFeasibleS (src : ShiftSource) (a : ℝ) (N : ℕ) (X : Set ℝ) (p : ℝ → ℝ) : Prop :=
  p ∈ oddSpan (src.w : ℝ) N ∧ (∀ t ∈ X, 0 ≤ Real.exp (-2 * π * t) * p t) ∧
    0 < src.gVac a (fun t => Real.exp (-2 * π * t) * p t)

/-- Finite-order odd-Laguerre threshold `T_{F}^{[N]}` (`ℝ≥0∞`-valued). -/
noncomputable def thrNS (src : ShiftSource) (a : ℝ) (F : Set ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (_ : 0 < T ∧ ∃ p, OddFeasibleS src a N (F ∪ Ici T) p), ENNReal.ofReal T

/-- Infinite-order derivative limit `T_{F}^{[∞]}`. -/
noncomputable def thrInfS (src : ShiftSource) (a : ℝ) (F : Set ℝ) : ℝ≥0∞ :=
  ⨅ N : ℕ, thrNS src a F N

lemma thrNS_antitone (src : ShiftSource) (a : ℝ) (F : Set ℝ) : Antitone (thrNS src a F) := by
  intro M N hMN
  refine le_iInf fun T => le_iInf fun ⟨hT, p, hp⟩ => ?_
  exact iInf₂_le T ⟨hT, p, oddSpan_mono _ hMN hp.1, hp.2⟩

lemma crossing_lapFin_src {src : ShiftSource} {a : ℝ} (meas : SourceCrossingMeasure src a)
    {β : ℝ} (hβ : 0 < β) : Integrable (fun t => Real.exp (-2 * π * β * t)) meas.ν := by
  have := meas.finite_laplace hβ
  rwa [IntegrableOn, restrict_Ici_eq_self_src meas] at this

/-- **`ds:LP`(i), (b) ⇒ (a)** for `ShiftSource`: a crossing measure on `X` excludes every finite
odd-Laguerre test on `X`. -/
theorem not_oddFeasibleS_of_crossingMeasure {src : ShiftSource} {a : ℝ}
    (hnnV : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    (meas : SourceCrossingMeasure src a) {X : Set ℝ} (hX : meas.ν Xᶜ = 0) (N : ℕ)
    (p : ℝ → ℝ) : ¬ OddFeasibleS src a N X p := by
  rintro ⟨hp, hnn, hvac⟩
  have hw : 0 < (src.w : ℝ) := by exact_mod_cast src.hw
  set θ : ℝ := 1 / 2 with hθ
  have hθ0 : 0 < θ := by norm_num [hθ]
  have hθ1 : θ < 1 := by norm_num [hθ]
  have hs0 := sTheta_pos hθ0 hθ1
  set ν := meas.ν with hν
  set νC := expTilt (refMeasS src a) with hνC
  have hint : Integrable (fun t => Real.exp (-2 * π * sTheta θ * t)) ν := crossing_lapFin_src meas hs0
  have hs1 : sTheta θ < 1 := by unfold sTheta; rw [hθ]; norm_num
  have hint' : Integrable (fun t => Real.exp (-2 * π * sTheta θ * t)) νC := by
    rw [hνC, integrable_expTilt_iff]
    have := integrable_exp_refS hnnV (c := 2 * π * (1 - sTheta θ)) (by nlinarith [Real.pi_pos])
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only
    rw [← Real.exp_add]; congr 1; ring
  have hcross : ∀ β, sTheta θ < β → β < 1 / sTheta θ →
      ∫ t, xiW (src.w : ℝ) β t ∂ν = ∫ t, xiW (src.w : ℝ) β t ∂νC := by
    intro β h1 _
    have hβ0 : 0 < β := hs0.trans h1
    have h := meas.crossing hβ0
    rw [restrict_Ici_eq_self_src meas] at h
    rw [hνC, integral_xiW_expTilt_refS' hnnV β]
    exact h
  have hmom := (ds_cay_iff hw hθ0 hθ1 meas.supp_nonneg
    (by rw [hνC]; exact expTilt_apply_eq_zero (refMeasS_Iio src a)) hint hint').1 hcross
  have hmain : ∀ q ∈ oddSpan (src.w : ℝ) N,
      Integrable (fun t => Real.exp (-2 * π * t) * q t) ν ∧
      Integrable (fun t => Real.exp (-2 * π * t) * q t) νC ∧
      ∫ t, Real.exp (-2 * π * t) * q t ∂ν = ∫ t, Real.exp (-2 * π * t) * q t ∂νC := by
    intro q hq
    refine Submodule.span_induction (p := fun q _ =>
      Integrable (fun t => Real.exp (-2 * π * t) * q t) ν ∧
      Integrable (fun t => Real.exp (-2 * π * t) * q t) νC ∧
      ∫ t, Real.exp (-2 * π * t) * q t ∂ν = ∫ t, Real.exp (-2 * π * t) * q t ∂νC) ?_ ?_ ?_ ?_ hq
    · rintro f ⟨k, hk, -, rfl⟩
      have h1 := (ds_cay_series hw hθ0 hθ1 meas.supp_nonneg hint (ϖ := 0) (β := 1)
        (by simpa using hθ0) (by norm_num)).1 k
      have h2 := (ds_cay_series hw hθ0 hθ1
        (by rw [hνC]; exact expTilt_apply_eq_zero (refMeasS_Iio src a))
        hint' (ϖ := 0) (β := 1) (by simpa using hθ0) (by norm_num)).1 k
      have e : (fun t => Real.exp (-2 * π * t) * lagP (src.w : ℝ) k t) =
          fun t => ((-1) ^ k * (k.factorial : ℝ) / (4 * π) ^ k) * lagPsi (src.w : ℝ) k t :=
        funext fun t => exp_mul_lagP_eq _ k t
      rw [e]
      refine ⟨h1.const_mul _, h2.const_mul _, ?_⟩
      rw [integral_const_mul, integral_const_mul, hmom k hk]
    · simp
    · rintro f g _ _ ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
      simp only [Pi.add_apply, mul_add]
      exact ⟨hf1.add hg1, hf2.add hg2, by rw [integral_add hf1 hg1, integral_add hf2 hg2, hf3, hg3]⟩
    · rintro c f _ ⟨hf1, hf2, hf3⟩
      simp only [Pi.smul_apply, smul_eq_mul]
      have e : ∀ t, Real.exp (-2 * π * t) * (c * f t) = c * (Real.exp (-2 * π * t) * f t) :=
        fun t => by ring
      simp_rw [e]
      exact ⟨hf1.const_mul c, hf2.const_mul c, by rw [integral_const_mul, integral_const_mul, hf3]⟩
  obtain ⟨-, -, heq⟩ := hmain p hp
  have hνCint : ∫ t, Real.exp (-2 * π * t) * p t ∂νC = ∫ t, p t ∂refMeasS src a := by
    rw [hνC, integral_expTilt]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]; ring_nf; simp
  have hge : 0 ≤ ∫ t, Real.exp (-2 * π * t) * p t ∂ν := by
    refine integral_nonneg_of_ae ?_
    have : ∀ᵐ t ∂ν, t ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hX
    filter_upwards [this] with t ht
    exact hnn t (by simpa using ht)
  rw [heq, hνCint] at hge
  have := gVac_expPolyS hnnV p
  linarith

private noncomputable def LrefS (src : ShiftSource) (a : ℝ)
    (hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t) :
    OCall (src.w : ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ t, (f.1 : C(ℝ, ℝ)) t ∂refMeasS src a
  map_add' f g := integral_add (integrable_OCall_refS hnn f.2) (integrable_OCall_refS hnn g.2)
  map_smul' c _ := integral_const_mul c _

private lemma integral_refS_nonneg_of_noFeasible {src : ShiftSource} {a : ℝ}
    (hnnV : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t) {X : Set ℝ}
    (hno : ∀ N p, ¬ OddFeasibleS src a N X p) {N : ℕ} {p : ℝ → ℝ}
    (hp : p ∈ oddSpan (src.w : ℝ) N) (hnn : ∀ t ∈ X, 0 ≤ p t) : 0 ≤ ∫ t, p t ∂refMeasS src a := by
  by_contra hneg
  push Not at hneg
  refine hno N p ⟨hp, fun t ht => mul_nonneg (Real.exp_pos _).le (hnn t ht), ?_⟩
  rw [gVac_expPolyS hnnV]
  linarith

private lemma exists_functionalS {src : ShiftSource} {a : ℝ}
    (hnnV : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t) {X : Set ℝ}
    (hno : ∀ N p, ¬ OddFeasibleS src a N X p) (t : C(X, ℝ)) (htx : ∀ x : X, t x = x.1) :
    ∃ L : polyUnion (oddV (src.w : ℝ) t) →ₗ[ℝ] ℝ,
      (∀ (f : C(ℝ, ℝ)) (hf : f ∈ OCall (src.w : ℝ)),
        L ⟨compT t f, compT_mem_polyUnion _ hf⟩ = ∫ t, f t ∂refMeasS src a) ∧
      ∀ v, (∀ x, 0 ≤ v.1 x) → 0 ≤ L v := by
  set ι' : OCall (src.w : ℝ) →ₗ[ℝ] C(X, ℝ) := (compT t).comp (OCall (src.w : ℝ)).subtype with hι'
  have hker : LinearMap.ker ι' ≤ LinearMap.ker (LrefS src a hnnV) := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    obtain ⟨N, hN⟩ := exists_N_of_mem_OCall f.2
    have hzero : ∀ x : X, f.1 x.1 = 0 := fun x => by
      have := congrArg (fun q : C(X, ℝ) => q x) hf
      simpa [hι', htx] using this
    have hp := coe_mem_oddSpan_of_mem_OC hN
    have h1 := integral_refS_nonneg_of_noFeasible hnnV hno hp (fun s hs => by
      rw [show f.1 s = 0 from hzero ⟨s, hs⟩])
    have h2 := integral_refS_nonneg_of_noFeasible hnnV hno (Submodule.neg_mem _ hp) (fun s hs => by
      simp only [Pi.neg_apply]; rw [show f.1 s = 0 from hzero ⟨s, hs⟩]; simp)
    simp only [Pi.neg_apply, integral_neg] at h2
    show ∫ t, (f.1 : C(ℝ, ℝ)) t ∂refMeasS src a = 0
    linarith
  let L₀ : LinearMap.range ι' →ₗ[ℝ] ℝ :=
    ((LinearMap.ker ι').liftQ (LrefS src a hnnV) hker).comp ι'.quotKerEquivRange.symm.toLinearMap
  have hL₀ : ∀ (f : OCall (src.w : ℝ)) (h : ι' f ∈ LinearMap.range ι'),
      L₀ ⟨ι' f, h⟩ = LrefS src a hnnV f := fun f _ => by
    simp only [L₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : polyUnion (oddV (src.w : ℝ) t) →ₗ[ℝ] ℝ :=
    L₀.comp (Submodule.inclusion (polyUnion_oddV_le_range t))
  refine ⟨L, fun f hf => ?_, fun v hv => ?_⟩
  · exact hL₀ ⟨f, hf⟩ _
  · obtain ⟨f, hf⟩ := polyUnion_oddV_le_range t v.2
    obtain ⟨N, hN⟩ := exists_N_of_mem_OCall f.2
    have hLv : L v = LrefS src a hnnV f := by
      have : (⟨v.1, polyUnion_oddV_le_range t v.2⟩ : LinearMap.range ι') = ⟨ι' f, ⟨f, rfl⟩⟩ :=
        Subtype.ext hf.symm
      show L₀ ⟨v.1, polyUnion_oddV_le_range t v.2⟩ = _
      rw [this]; exact hL₀ f _
    rw [hLv]
    have hp := coe_mem_oddSpan_of_mem_OC hN
    refine integral_refS_nonneg_of_noFeasible hnnV hno hp (fun s hs => ?_)
    have := hv ⟨s, hs⟩
    rw [← hf] at this
    simpa [hι', htx] using this

/-- **`ds:LP`(i), (a) ⇒ (b)** for `ShiftSource`. -/
theorem exists_crossingMeasureS_of_not_oddFeasible {src : ShiftSource} {a : ℝ}
    (hnnV : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t) {T₀ : ℝ} (hT₀ : 0 < T₀)
    {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hno : ∀ N p, ¬ OddFeasibleS src a N X p) :
    ∃ meas : SourceCrossingMeasure src a, meas.ν Xᶜ = 0 := by
  have hw : 0 < (src.w : ℝ) := by exact_mod_cast src.hw
  obtain ⟨t, htx⟩ : ∃ t : C(X, ℝ), ∀ x : X, t x = x.1 :=
    ⟨⟨fun x : X => x.1, continuous_subtype_val⟩, fun _ => rfl⟩
  obtain ⟨L, hLf, hLpos⟩ := exists_functionalS hnnV hno t htx
  obtain ⟨N₀, p₀, hp₀, hp₀1⟩ := positive_ray hw hT₀
  obtain ⟨f₀, hf₀, hf₀p⟩ := exists_mem_OC_of_mem_oddSpan hp₀
  have hmaj : ∃ (N : ℕ) (f : C(ℝ, ℝ)) (η : ℝ), Odd N ∧ f ∈ OC (src.w : ℝ) N ∧ 0 < η ∧
      ∀ x : X, η ≤ f (t x) :=
    ⟨2 * N₀ + 1, f₀, 1, ⟨N₀, rfl⟩, OC_mono _ (by omega) hf₀, one_pos, fun x => by
      rw [htx x, show f₀ x.1 = p₀ x.1 from congrFun hf₀p x.1]
      exact hp₀1 _ (hX x.2)⟩
  have hT := oddV_hyp hw hT₀.le (t := t) (fun x => by rw [htx x]; exact hX x.2)
    (by
      have : (t : X → ℝ) = Subtype.val := funext htx
      rw [this]; exact hXc.isClosedEmbedding_subtypeVal.isProperMap) hmaj
  have hodd : RefOdd (lagPC (src.w : ℝ)) t (oddV (src.w : ℝ) t) (refMeasS src a) L := by
    intro v j hj hvj
    have hmem : lagPC (src.w : ℝ) j ∈ OCall (src.w : ℝ) := Submodule.subset_span ⟨j, hj, rfl⟩
    have := hLf _ hmem
    have hv : v = ⟨compT t (lagPC (src.w : ℝ) j), compT_mem_polyUnion _ hmem⟩ := Subtype.ext hvj
    rw [hv, this]
  have : LocallyCompactSpace X := hXc.locallyCompactSpace
  obtain ⟨μ, _, _, hrep, ε, hε, hexp⟩ := poly_compact_ref hT (refMeasS src a) (refMeasS_Iio src a)
    (integrable_exp_refS_pi hnnV) L hLpos hodd
  have hmeas : Measurable (fun x : X => x.1) := measurable_subtype_coe
  set μ₁ : Measure ℝ := μ.map (fun x : X => x.1) with hμ₁
  have hμ₁X : μ₁ Xᶜ = 0 := by
    rw [hμ₁, Measure.map_apply hmeas (hXc.measurableSet.compl)]
    have : (fun x : X => x.1) ⁻¹' Xᶜ = ∅ := by ext x; simp
    rw [this, measure_empty]
  have hμ₁T : μ₁ (Iio T₀) = 0 := by
    rw [hμ₁, Measure.map_apply hmeas measurableSet_Iio]
    have : (fun x : X => x.1) ⁻¹' Iio T₀ = ∅ := by ext x; simp [not_lt.2 (hX x.2)]
    rw [this, measure_empty]
  have hμ₁0 : μ₁ (Iio 0) = 0 := measure_mono_null (Iio_subset_Iio hT₀.le) hμ₁T
  have hexp₁ : Integrable (fun s => Real.exp (ε * s)) μ₁ := by
    rw [hμ₁, integrable_map_measure (by fun_prop) hmeas.aemeasurable]
    refine hexp.congr (Eventually.of_forall fun x => ?_)
    simp [htx x]
  have hodd₁ : ∀ k, Odd k → ∫ s, lagP (src.w : ℝ) k s ∂μ₁ = ∫ s, lagP (src.w : ℝ) k s ∂refMeasS src a := by
    intro k hk
    rw [hμ₁, integral_map hmeas.aemeasurable (continuous_lagP _ k).aestronglyMeasurable]
    have h1 := hrep ⟨pc (lagPC (src.w : ℝ)) k t, hT.pc_mem hk⟩
    rw [hodd ⟨pc (lagPC (src.w : ℝ)) k t, hT.pc_mem hk⟩ k hk rfl] at h1
    have h2 : ∫ x : X, lagP (src.w : ℝ) k x.1 ∂μ = ∫ x : X, (pc (lagPC (src.w : ℝ)) k t) x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => by simp [htx x])
    rw [h2]; exact h1
  set ε' : ℝ := min ε π with hε'
  have hε'0 : 0 < ε' := lt_min hε Real.pi_pos
  obtain ⟨θ, hθ0, hθ1, hf, _, hcr⟩ := tilt_crossing hw hμ₁0 (refMeasS_Iio src a) hε'0
    (integrable_exp_mono hμ₁0 hexp₁ (min_le_left _ _))
    (integrable_exp_refS hnnV (c := ε') (by linarith [min_le_right ε π, Real.pi_pos])) hodd₁
  set ν : Measure ℝ := expTilt μ₁ with hν
  have hνIio : ν (Iio 0) = 0 := expTilt_apply_eq_zero hμ₁0
  have hs0 := sTheta_pos hθ0 hθ1
  have hs1 : sTheta θ < 1 := by unfold sTheta; rw [div_lt_one (by linarith)]; linarith
  have hcross : ∀ β, sTheta θ < β → β < 1 / sTheta θ →
      lapZ ν β + src.srcFun a β = β ^ (-(src.w : ℝ)) * (lapZ ν (1 / β) + src.srcFun a (1 / β)) := by
    intro β h1 h2
    have hβ0 : 0 < β := hs0.trans h1
    have hinv : sTheta θ < 1 / β := by
      rw [lt_div_iff₀ hβ0]; rw [lt_div_iff₀ hs0] at h2; linarith
    have h := hcr β h1 h2
    rw [integral_xiW_lapZ (hf.mono hνIio h1.le) (hf.mono hνIio hinv.le),
      integral_xiW_expTilt_refS hnnV hβ0] at h
    linarith
  obtain ⟨hall, hid⟩ := ds_cont (analyticOnNhd_srcFun src a) hνIio hs0 hs1 hf hcross
  refine ⟨⟨ν, hνIio, fun {β} hβ => ?_, fun {β} hβ => ?_⟩, ?_⟩
  · exact (hall β hβ).integrableOn
  · have hrestr : ν.restrict (Ici 0) = ν := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      have : ∀ᵐ t ∂ν, t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hνIio
      filter_upwards [this] with t ht using not_lt.1 ht
    rw [hrestr, ← integral_xiW_expTilt_refS' hnnV β]
    show ∫ t, xiW (src.w : ℝ) β t ∂ν = _
    rw [integral_xiW_lapZ (hall β hβ) (hall (1 / β) (by positivity)), integral_xiW_expTilt_refS hnnV hβ]
    have := hid β hβ
    linarith
  · show ν Xᶜ = 0
    exact expTilt_apply_eq_zero hμ₁X

/-- **`ds:LP`(i)** for `ShiftSource`: for any closed `X ⊆ [T₀, ∞)` (`T₀ > 0`),
infeasibility of finite odd-Laguerre tests on `X` iff existence of a crossing measure on `X`. -/
theorem ds_LP_i_src {src : ShiftSource} {a : ℝ} (hnnV : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    {T₀ : ℝ} (hT₀ : 0 < T₀) {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀) :
    (∀ N p, ¬ OddFeasibleS src a N X p) ↔ ∃ meas : SourceCrossingMeasure src a, meas.ν Xᶜ = 0 :=
  ⟨exists_crossingMeasureS_of_not_oddFeasible hnnV hT₀ hXc hX,
    fun ⟨meas, hX⟩ => not_oddFeasibleS_of_crossingMeasure hnnV meas hX⟩

private lemma le_thrNS_of_crossingMeasure {src : ShiftSource} {a : ℝ}
    (hnnV : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t)
    (meas : SourceCrossingMeasure src a) {F : Set ℝ} {τ : ℝ}
    (hν : meas.ν (F ∪ Ici τ)ᶜ = 0) (N : ℕ) : ENNReal.ofReal τ ≤ thrNS src a F N := by
  refine le_iInf fun T => le_iInf fun ⟨hT, p, hp⟩ => ?_
  by_contra hlt
  have hτ : T < τ := by
    have := not_le.1 hlt
    exact (ENNReal.ofReal_lt_ofReal_iff' |>.1 this).1
  have hsub : (F ∪ Ici τ) ⊆ F ∪ Ici T := union_subset_union_right F (Ici_subset_Ici.2 hτ.le)
  exact not_oddFeasibleS_of_crossingMeasure hnnV meas hν N p ⟨hp.1, fun t ht => hp.2.1 t (hsub ht), hp.2.2⟩

/-- **`ds:LP`(ii)** for `ShiftSource` / `FloorData.At`: for compact `F ⊂ [T₀, ∞)` (`T₀ > 0`),
if `T₀ < T_F^{[∞]} < ∞`, then `T_F^{[∞]} = max {τ > 0 : ∃ crossing measure on F ∪ [τ, ∞)}`. -/
theorem ds_LP_ii_src {src : ShiftSource} {Fl : FloorData src} {cTilde : ℝ}
    (hAt : Fl.At (cTilde / 12)) {T₀ : ℝ} (hT₀ : 0 < T₀) {F : Set ℝ} (hFc : IsClosed F)
    (hF : F ⊆ Ici T₀) (hlow : ENNReal.ofReal T₀ < thrInfS src (cTilde / 12) F)
    (hfin : thrInfS src (cTilde / 12) F < ⊤) :
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure src (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0} (thrInfS src (cTilde / 12) F).toReal := by
  have hnnV : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV (cTilde / 12) t := fun t ht => hAt.nonneg_V ht
  have hcb : CrossingBounds src (cTilde / 12) := hAt.crossingBounds
  obtain ⟨β₀, S⟩ := SourceDualSetupCore.exists_of_floor hAt hT₀
  set τs := (thrInfS src (cTilde / 12) F).toReal with hτs
  have hofr : ENNReal.ofReal τs = thrInfS src (cTilde / 12) F := ENNReal.ofReal_toReal hfin.ne
  have hT₀τ : T₀ < τs := by
    have := hlow; rw [← hofr] at this
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT₀.le).1 this
  have hnot_odd : ∀ τ, T₀ ≤ τ → τ < τs → ∀ N p, ¬ OddFeasibleS src (cTilde / 12) N (F ∪ Ici τ) p := by
    intro τ hτ0 hlt N p hp
    have hle : thrInfS src (cTilde / 12) F ≤ ENNReal.ofReal τ :=
      (iInf_le _ N).trans (iInf₂_le τ ⟨hT₀.trans_le hτ0, p, hp⟩)
    rw [← hofr] at hle
    exact absurd ((ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hle) (not_le.2 hlt)
  let τ : ℕ → ℝ := fun n => τs - (τs - T₀) / (n + 2)
  have hτ0 : ∀ n, T₀ ≤ τ n := fun n => by
    have : (τs - T₀) / (n + 2) ≤ τs - T₀ :=
      div_le_self (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    show T₀ ≤ τs - (τs - T₀) / (n + 2); linarith
  have hτlt : ∀ n, τ n < τs := fun n => by
    have : 0 < (τs - T₀) / (n + 2) :=
      div_pos (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    show τs - (τs - T₀) / (n + 2) < τs; linarith
  have hτmono : Monotone τ := by
    refine monotone_nat_of_le_succ fun n => ?_
    show τs - (τs - T₀) / (n + 2) ≤ τs - (τs - T₀) / ((n + 1 : ℕ) + 2)
    have h1 : (τs - T₀) / (((n + 1 : ℕ) : ℝ) + 2) ≤ (τs - T₀) / (n + 2) := by
      refine div_le_div_of_nonneg_left (by linarith)
        (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) ?_
      push_cast; linarith
    linarith
  let X : ℕ → Set ℝ := fun n => F ∪ Ici (τ n)
  have hXc : ∀ n, IsClosed (X n) := fun n => hFc.union isClosed_Ici
  have hXa : Antitone X := fun m n hmn => union_subset_union_right F (Ici_subset_Ici.2 (hτmono hmn))
  have hX0 : X 0 ⊆ Ici T₀ := union_subset hF (Ici_subset_Ici.2 (hτ0 0))
  have hns : ∀ n, NoSpanFeasibleS src cTilde β₀ (X n) := fun n => by
    obtain ⟨meas, hν⟩ := exists_crossingMeasureS_of_not_oddFeasible hnnV hT₀ (hXc n)
      (union_subset hF (Ici_subset_Ici.2 (hτ0 n))) (hnot_odd (τ n) (hτ0 n) (hτlt n))
    exact noSpanFeasibleS_of_crossingMeasure src S hcb meas hν
  obtain ⟨meas, hν, -, -⟩ := theorem_E_a_decreasing_src src S hXc hXa hX0 hns
  have hInter : (⋂ n, X n) = F ∪ Ici τs := by
    refine Subset.antisymm (fun y hy => ?_) (fun y hy => mem_iInter.2 fun n => ?_)
    · by_cases hyF : y ∈ F
      · exact Or.inl hyF
      · refine Or.inr ?_
        have hall : ∀ n, τ n ≤ y := fun n => (mem_iInter.1 hy n).resolve_left hyF
        by_contra hlt0
        have hlt : y < τs := lt_of_not_ge hlt0
        obtain ⟨n, hn⟩ := exists_nat_gt ((τs - T₀) / (τs - y))
        have : (τs - T₀) / (n + 2) < τs - y := by
          rw [div_lt_iff₀ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
          have := (div_lt_iff₀ (by linarith : 0 < τs - y)).mp hn
          nlinarith
        have h2 := hall n
        have : y < τ n := by show y < τs - (τs - T₀) / (n + 2); linarith
        linarith
    · rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (le_trans (hτlt n).le hy)
  refine ⟨⟨by linarith, meas, by rw [← hInter]; exact hν⟩, fun τ' hτ' => ?_⟩
  obtain ⟨hτ'0, meas', hν'⟩ := hτ'
  have h1 : ENNReal.ofReal τ' ≤ thrInfS src (cTilde / 12) F :=
    le_iInf fun N => le_thrNS_of_crossingMeasure hnnV meas' hν' N
  rw [← hofr] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h1

/-- **`ds:LP`(iii)** for `ShiftSource` / `FloorData.At` with `0 < src.T_V cTilde`:
`T_V = T_∅^{[∞]} = lim_N T_∅^{[N]} = inf_P T_∅^{[2P+1]}`, attained by a crossing measure on `[T_V, ∞)`. -/
theorem ds_LP_iii_src {src : ShiftSource} {Fl : FloorData src} {cTilde : ℝ}
    (hAt : Fl.At (cTilde / 12)) (hTV : 0 < src.T_V cTilde) :
    thrInfS src (cTilde / 12) ∅ = ENNReal.ofReal (src.T_V cTilde) ∧
    Tendsto (fun N => thrNS src (cTilde / 12) ∅ N) atTop (𝓝 (ENNReal.ofReal (src.T_V cTilde))) ∧
    (⨅ P : ℕ, thrNS src (cTilde / 12) ∅ (2 * P + 1)) = ENNReal.ofReal (src.T_V cTilde) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure src (cTilde / 12),
      meas.ν (Ici τ)ᶜ = 0} (src.T_V cTilde) := by
  have hnnV : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV (cTilde / 12) t := fun t ht => hAt.nonneg_V ht
  obtain ⟨β₀, S₀⟩ := SourceDualSetupCore.exists_of_floor hAt one_pos
  obtain ⟨-, ⟨meas, hmeas⟩, hmax⟩ := theorem_E_b_compact_empty_src hAt hTV
  have hge : ∀ N, ENNReal.ofReal (src.T_V cTilde) ≤ thrNS src (cTilde / 12) ∅ N := fun N =>
    le_thrNS_of_crossingMeasure hnnV meas (by rw [empty_union]; exact hmeas) N
  have hle : thrInfS src (cTilde / 12) ∅ ≤ ENNReal.ofReal (src.T_V cTilde) := by
    by_contra hlt
    obtain ⟨τ, hτ0, hτ1, hτ2⟩ := ENNReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    have hTτ : src.T_V cTilde < τ := (ENNReal.ofReal_lt_ofReal_iff'.1 hτ1).1
    have hτpos : 0 < τ := lt_trans hTV hTτ
    have hno : ∀ N p, ¬ OddFeasibleS src (cTilde / 12) N (∅ ∪ Ici τ) p := fun N p hp =>
      absurd ((iInf_le _ N).trans (iInf₂_le τ ⟨hτpos, p, hp⟩)) (not_le.2 hτ2)
    obtain ⟨m, hm⟩ := (ds_LP_i_src hnnV hτpos (X := ∅ ∪ Ici τ) (isClosed_empty.union isClosed_Ici)
      (by rw [empty_union])).1 hno
    rw [empty_union] at hm
    have hne_gaps : (constrainedGapsS src cTilde ∅).Nonempty := by
      obtain ⟨-, T, hT, ⟨g, hg⟩, -⟩ := T_V_lt_top_of_core S₀
      exact ⟨T, hT, g, by rw [empty_union, isFeasibleOn_Ici_iff_src]; exact hg⟩
    have hτ_le := le_constrainedThresholdS_of_crossingMeasure src S₀ hAt.crossingBounds hne_gaps m
      (by rw [empty_union]; exact hm)
    have hcon := hmax.2 ⟨hτpos, m, hm⟩
    linarith
  have heq : thrInfS src (cTilde / 12) ∅ = ENNReal.ofReal (src.T_V cTilde) :=
    le_antisymm hle (le_iInf hge)
  refine ⟨heq, ?_, ?_, hmax⟩
  · rw [← heq]; exact tendsto_atTop_iInf (thrNS_antitone src (cTilde / 12) ∅)
  · refine le_antisymm ?_ (le_iInf fun P => hge _)
    rw [← heq]
    refine le_iInf fun N => (iInf_le _ N).trans ?_
    exact thrNS_antitone src (cTilde / 12) ∅ (by omega)

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.ds_LP_i_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.ds_LP_i_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.ds_LP_ii_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.ds_LP_ii_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.ds_LP_iii_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.ds_LP_iii_src

end FormalResearch.ModularBootstrap.Mixtures
