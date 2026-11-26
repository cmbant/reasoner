module

public import FormalResearch.ModularBootstrap.Mixtures.CommonSource
public import FormalResearch.ModularBootstrap.Mixtures.ShiftAsymptotics
public import FormalResearch.ModularBootstrap.Crossing.MehlerOddMoment

/-!
# The crossing sum rule for an atomic source (`pmix:crossing` (a), `fw:crossing` for a signed shift measure)

Port of `Crossing/SumRule.lean` (`Lemma FW-X`) from `FixedWeightProblem` to `ShiftSource`.  The proof uses the Cardy weight
only through three facts, bundled as `CrossingBounds src a` (a `Prop`): `V ≥ 0` on `[0, ∞)`, and the two-sided
exponential-polynomial comparison of the Cartesian density `ρ(‖x‖²/2)` with `cardyWeight` (upper bound everywhere, lower
bound for large `t`).  `CrossingBounds` is proved for a common source (`FloorData.At.crossingBounds`) from the
fixed-weight comparison for `Q ≡ 1` (upper) and for `Q_0` (lower) and the sandwich `d_λ V_{Q_0} ≤ V ≤ ‖λ‖_TV K_a`.

The declarations of the port keep the names of `Crossing/SumRule.lean` up to the suffix `S`/`_src`; the statements are
the old ones with `prob.cardyV` replaced by `src.cardyV` and the hypothesis `prob.totalShift ≤ a` by `CrossingBounds src a`.
The old declarations are not modified; re-deriving them from these (a `FixedWeightProblem` has
`CrossingBounds (ofProblem prob) a` for `prob.totalShift ≤ a`, see `crossingBounds_ofProblem`) is a follow-up.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace ENNReal

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing

/-- The facts about the Cardy weight used by the crossing sum rule at the charge `a`. -/
structure CrossingBounds (src : ShiftSource) (a : ℝ) : Prop where
  pos : 0 < a
  nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ src.cardyV a t
  rho_le : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
    src.rhoDensity a t ≤
      C * cardyWeight (-((src.w - 1 : ℝ) / 2 + 1 / 4)) (2 * Real.sqrt 2 * π * Real.sqrt a) t
  rho_ge : ∃ c T₀ : ℝ, 0 < c ∧ 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
    c * cardyWeight (-((src.w - 1 : ℝ) / 2 + 1 / 4)) (2 * Real.sqrt 2 * π * Real.sqrt a) t ≤
      src.rhoDensity a t

namespace ShiftSource

variable (src : ShiftSource)

lemma cardyV_nonneg {a : ℝ} (ha : CrossingBounds src a) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ src.cardyV a t :=
  ha.nonneg t ht

lemma rhoDensity_nonneg {a : ℝ} (ha : CrossingBounds src a) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ src.rhoDensity a t := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · have htend : Tendsto (src.rhoDensity a) (𝓝[>] 0) (𝓝 (src.rhoDensity a 0)) :=
      (src.continuous_rhoDensity a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hup : (0 : ℝ) < u := hu
    have hV : 0 ≤ src.cardyV a u := ha.nonneg u hup.le
    rw [src.cardyV_eq_pow_mul_reduced] at hV
    have hred : 0 ≤ src.cardyVReduced a u :=
      nonneg_of_mul_nonneg_right hV (pow_pos hup _)
    unfold rhoDensity
    positivity
  · have hV : 0 ≤ src.cardyV a t := ha.nonneg t ht
    rw [src.cardyV_eq_pow_mul_reduced] at hV
    have hred : 0 ≤ src.cardyVReduced a t :=
      nonneg_of_mul_nonneg_right hV (pow_pos ht_pos _)
    unfold rhoDensity
    positivity

lemma rhoDensity_le_cardyWeight {a : ℝ} (ha : CrossingBounds src a) (_ha_pos : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      src.rhoDensity a t ≤
        C * cardyWeight (-((src.w - 1 : ℝ) / 2 + 1 / 4)) (2 * Real.sqrt 2 * π * Real.sqrt a) t :=
  ha.rho_le

lemma rhoDensity_ge_cardyWeight_large {a : ℝ} (ha : CrossingBounds src a) (_ha_pos : 0 < a) :
    ∃ c T₀ : ℝ, 0 < c ∧ 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      c * cardyWeight (-((src.w - 1 : ℝ) / 2 + 1 / 4)) (2 * Real.sqrt 2 * π * Real.sqrt a) t ≤
        src.rhoDensity a t :=
  ha.rho_ge

lemma integral_rhoDensity (a : ℝ) (h : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin (2 * src.w)),
        h (‖x‖ ^ 2 / 2) * src.rhoDensity a (‖x‖ ^ 2 / 2) =
      ∫ t in Ioi 0, h t * src.cardyDensity a t := by
  have h1 := integral_radialLiftReal src.hw (fun t => h t * src.rhoDensity a t)
  rw [h1]
  have hfac_ne : ((src.w - 1).factorial : ℝ) ≠ 0 := by positivity
  have hpi_ne : (2 * π) ^ src.w ≠ 0 := by positivity
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht_pos : 0 < t := Set.mem_Ioi.mp ht
  unfold rhoDensity cardyDensity
  rw [src.cardyV_eq_pow_mul_reduced]
  field_simp

end ShiftSource

/-- Positive crossing measure (the Ξ-form of `pmix:cross`): a positive measure on `[0, ∞)` with finite Laplace
transform at every `β > 0` and `∫ Ξ_β dν = ∫ Ξ_β ρ dt` with `ρ = 2π V` the Cardy density of the source. -/
structure SourceCrossingMeasure (src : ShiftSource) (a : ℝ) where
  ν : Measure ℝ
  supp_nonneg : ν (Iio 0) = 0
  finite_laplace : ∀ {β : ℝ}, 0 < β → IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Ici 0) ν
  crossing : ∀ {β : ℝ}, 0 < β →
    ∫ t in Ici 0, thermalDiff src.w β t ∂ν =
      ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyDensity a t

private lemma norm_euclidean_single_zero (w : ℕ) (hw : 1 ≤ w) :
    ‖(EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) : RadialSpace w)‖ = 1 :=
  (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (2 * w))).norm_eq_one ⟨0, by omega⟩

private lemma rpow_sq_mul_exp_le_exp (b d u : ℝ) (hu : 0 ≤ u) :
    (1 + u ^ 2) ^ |b| * Real.exp (|d| * u) ≤
      Real.exp ((2 * (Nat.ceil |b| : ℝ) + |d|) * u) := by
  let k : ℕ := Nat.ceil |b|
  have hk : |b| ≤ (k : ℝ) := Nat.le_ceil |b|
  have h1 : (1 + u ^ 2) ^ |b| ≤ (1 + u ^ 2) ^ (k : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg u]) hk
  have h2 : (1 + u ^ 2) ^ (k : ℝ) = (1 + u ^ 2) ^ k := Real.rpow_natCast _ k
  have h3 : (1 + u ^ 2) ^ k ≤ (Real.exp u) ^ (2 * k) := by
    have h1u : 1 + u ^ 2 ≤ (1 + u) ^ 2 := by nlinarith
    have hexp : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    calc (1 + u ^ 2) ^ k ≤ ((1 + u) ^ 2) ^ k := pow_le_pow_left₀ (by positivity) h1u k
      _ = (1 + u) ^ (2 * k) := by rw [← pow_mul]
      _ ≤ (Real.exp u) ^ (2 * k) := pow_le_pow_left₀ (by positivity) hexp (2 * k)
  have h4 : (Real.exp u) ^ (2 * k) = Real.exp (2 * (k : ℝ) * u) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (1 + u ^ 2) ^ |b| * Real.exp (|d| * u)
      ≤ Real.exp (2 * (k : ℝ) * u) * Real.exp (|d| * u) :=
        mul_le_mul_of_nonneg_right (h1.trans (h2 ▸ h3.trans h4.le)) (Real.exp_pos _).le
    _ = Real.exp ((2 * (k : ℝ) + |d|) * u) := by rw [← Real.exp_add]; congr 1; ring

private lemma integrable_exp_linear_sub_gaussian (w : ℕ) (D₁ : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : RadialSpace w => Real.exp (D₁ * ‖u‖ - π * c * ‖u‖ ^ 2)) := by
  have hcomp : ∀ u : RadialSpace w,
      Real.exp (D₁ * ‖u‖ - π * c * ‖u‖ ^ 2) ≤
        Real.exp (D₁ ^ 2 / (2 * π * c)) * Real.exp (-π * (c / 2) * ‖u‖ ^ 2) := fun u => by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hsq : 0 ≤ (π * c / 2) * (‖u‖ - D₁ / (π * c)) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    have hid : D₁ * ‖u‖ - π * c * ‖u‖ ^ 2 + (π * c / 2) * (‖u‖ - D₁ / (π * c)) ^ 2 =
        D₁ ^ 2 / (2 * π * c) + -π * (c / 2) * ‖u‖ ^ 2 := by
      have hpc : π * c ≠ 0 := (mul_pos Real.pi_pos hc).ne'
      field_simp; ring
    linarith
  have hg := (integral_exp_neg_pi_mul_norm_sq w (half_pos hc)).1.const_mul (Real.exp (D₁ ^ 2 / (2 * π * c)))
  refine hg.mono' (by fun_prop : Continuous fun u : RadialSpace w =>
      Real.exp (D₁ * ‖u‖ - π * c * ‖u‖ ^ 2)).aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hcomp u

private lemma admissibleMeasure_Ici_sub_lt_top_src (src : ShiftSource) (a : ℝ)
    (meas : SourceCrossingMeasure src a) {S : Set ℝ} {R : ℝ}
    (hS : S ⊆ Icc 0 R) : meas.ν S < ⊤ := by
  let B : ℝ := Real.exp (-2 * π * 1 * R)
  have hB_pos : 0 < B := Real.exp_pos _
  have hfin := meas.finite_laplace one_pos
  have hlin_lt : (∫⁻ t in Ici 0, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν) < ⊤ := by
    have h1 : (∫⁻ t in Ici 0, ‖Real.exp (-2 * π * 1 * t)‖ₑ ∂meas.ν) < ⊤ := hfin.2
    have hcongr : (∫⁻ t in Ici 0, ‖Real.exp (-2 * π * 1 * t)‖ₑ ∂meas.ν) =
        ∫⁻ t in Ici 0, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν :=
      lintegral_congr_ae (ae_of_all _ fun t => Real.eNorm_of_nonneg (Real.exp_pos _).le)
    rwa [hcongr] at h1
  have hsub_ge : S ⊆ {t ∈ Ici 0 | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))} := by
    intro t ht
    have ht_icc := hS ht
    refine ⟨ht_icc.1, ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)⟩
    nlinarith [Real.pi_pos, ht_icc.2]
  have hae : AEMeasurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-2 * π * 1 * t)))
      (meas.ν.restrict (Ici 0)) :=
    (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-2 * π * 1 * t))).aemeasurable
  have hmarkov := mul_meas_ge_le_lintegral₀ hae (ENNReal.ofReal B)
  have hmeas_ge : meas.ν S ≤ (meas.ν.restrict (Ici 0))
      {t : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))} := by
    have h1 : meas.ν S ≤ meas.ν ({t ∈ Ici 0 | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))}) :=
      measure_mono hsub_ge
    have hmeas_set : MeasurableSet {t : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))} :=
      measurableSet_le measurable_const (ENNReal.continuous_ofReal.comp (by fun_prop)).measurable
    rwa [Measure.restrict_apply hmeas_set, Set.inter_comm]
  have hmul_lt : ENNReal.ofReal B * meas.ν S < ⊤ :=
    (by gcongr : ENNReal.ofReal B * meas.ν S ≤ ENNReal.ofReal B * (meas.ν.restrict (Ici 0))
      {t : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))}).trans_lt
      (hmarkov.trans_lt hlin_lt)
  rcases ENNReal.mul_lt_top_iff.mp hmul_lt with ⟨_, hlt⟩ | h0 | h0
  · exact hlt
  · exfalso
    have hle0 : B ≤ 0 := ENNReal.ofReal_eq_zero.mp h0
    linarith [hB_pos]
  · simp [h0]

/-- Pushforward of `meas.ν.restrict (Ici 0)` onto `ℝ^{2w}` along `embedRadial`. -/
noncomputable def nuLiftS (src : ShiftSource) (a : ℝ)
    (meas : SourceCrossingMeasure src a) : Measure (RadialSpace src.w) :=
  Measure.map (embedRadial src.w src.hw) (meas.ν.restrict (Ici 0))

lemma nuLiftS_sigmaFinite (src : ShiftSource) (a : ℝ)
    (meas : SourceCrossingMeasure src a) : SigmaFinite (nuLiftS src a meas) := by
  refine ⟨⟨{
    set := fun n => Metric.ball (0 : RadialSpace src.w) (n : ℝ)
    set_mem := fun _ => Set.mem_univ _
    finite := fun n => by
      unfold nuLiftS
      rw [Measure.map_apply (measurable_embedRadial src.w src.hw) measurableSet_ball]
      rw [Measure.restrict_apply (measurableSet_ball.preimage (measurable_embedRadial src.w src.hw))]
      refine admissibleMeasure_Ici_sub_lt_top_src src a meas (R := (n : ℝ) ^ 2 / 2) ?_
      intro t ⟨ht_ball, ht_nn⟩
      refine ⟨ht_nn, ?_⟩
      have hlt : ‖embedRadial src.w src.hw t‖ < (n : ℝ) := by
        simpa [Metric.mem_ball, dist_zero_right] using ht_ball
      have hsq : 2 * t ≤ (n : ℝ) ^ 2 := by
        rw [← norm_embedRadial_sq src.hw ht_nn]
        exact pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
      linarith
    spanning := Metric.iUnion_ball_nat 0
  }⟩⟩

lemma nuLiftS_gauss (src : ShiftSource) (a : ℝ)
    (meas : SourceCrossingMeasure src a) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : RadialSpace src.w => Real.exp (-ε * ‖x‖ ^ 2)) (nuLiftS src a meas) := by
  unfold nuLiftS
  rw [integrable_map_measure (by fun_prop : Continuous fun x : RadialSpace src.w =>
      Real.exp (-ε * ‖x‖ ^ 2)).aestronglyMeasurable
    (measurable_embedRadial src.w src.hw).aemeasurable]
  have hlap := meas.finite_laplace (div_pos hε Real.pi_pos)
  refine hlap.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  dsimp only [Function.comp_def]
  rw [norm_embedRadial_sq src.hw (Set.mem_Ici.mp ht)]
  congr 1; field_simp

lemma integrable_nuLiftS_iff (src : ShiftSource) (a : ℝ)
    (meas : SourceCrossingMeasure src a) {h : ℝ → ℝ} (hh : ContinuousOn h (Ici 0)) :
    Integrable (radialLiftReal src.w h) (nuLiftS src a meas) ↔
      IntegrableOn h (Ici 0) meas.ν := by
  unfold nuLiftS IntegrableOn
  rw [integrable_map_measure (continuous_radialLiftReal_of_continuousOn hh).aestronglyMeasurable
    (measurable_embedRadial src.w src.hw).aemeasurable]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact radialLiftReal_embedRadial src.hw h (Set.mem_Ici.mp ht)

lemma integral_nuLiftS (src : ShiftSource) (a : ℝ)
    (meas : SourceCrossingMeasure src a) {h : ℝ → ℝ} (hh : ContinuousOn h (Ici 0)) :
    ∫ x : RadialSpace src.w, radialLiftReal src.w h x ∂(nuLiftS src a meas) =
      ∫ t in Ici 0, h t ∂meas.ν := by
  unfold nuLiftS
  rw [integral_map (measurable_embedRadial src.w src.hw).aemeasurable
    (continuous_radialLiftReal_of_continuousOn hh).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact radialLiftReal_embedRadial src.hw h (Set.mem_Ici.mp ht)

/-- Reference Cardy measure `ϱ(‖x‖²/2) dx` on `ℝ^{2w}`. -/
noncomputable def rhoLiftS (src : ShiftSource) (a : ℝ) : Measure (RadialSpace src.w) :=
  volume.withDensity (fun x : RadialSpace src.w => ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2)))

private lemma exp_linear_sub_gaussian_bound (D₁ : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 0 ≤ u → Real.exp (D₁ * u - π * c * u ^ 2) ≤ K := by
  refine ⟨Real.exp (D₁ ^ 2 / (4 * π * c)), Real.exp_pos _, fun u _ => Real.exp_le_exp.mpr ?_⟩
  have hsq : 0 ≤ (2 * π * c * u - D₁) ^ 2 := sq_nonneg _
  have hpc : 0 < 4 * π * c := by positivity
  rw [le_div_iff₀ hpc]
  nlinarith [Real.pi_pos]

lemma rhoLiftS_gauss (src : ShiftSource) {a : ℝ}
    (ha : CrossingBounds src a) (ha_pos : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : RadialSpace src.w => Real.exp (-ε * ‖x‖ ^ 2)) (rhoLiftS src a) := by
  unfold rhoLiftS
  have hmeas : Measurable (fun x : RadialSpace src.w =>
      ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))) :=
    (ENNReal.continuous_ofReal.comp ((src.continuous_rhoDensity a).comp
      ((continuous_norm.pow 2).div_const 2))).measurable
  rw [integrable_withDensity_iff_integrable_smul' hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  obtain ⟨C, hC_pos, hrho_le⟩ := src.rhoDensity_le_cardyWeight ha ha_pos
  let b : ℝ := -((src.w - 1 : ℝ) / 2 + 1 / 4)
  let d : ℝ := 2 * Real.sqrt 2 * π * Real.sqrt a
  let C₁ : ℝ := 2 * (Nat.ceil |b| : ℝ) + |d|
  obtain ⟨K₁, hK₁_pos, hK₁⟩ := exp_linear_sub_gaussian_bound C₁ (div_pos (div_pos hε two_pos) Real.pi_pos)
  have hint_g := (integral_exp_neg_pi_mul_norm_sq src.w (div_pos (div_pos hε two_pos) Real.pi_pos)).1
  have heq_dens : (fun x : RadialSpace src.w =>
      (ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))).toReal • Real.exp (-ε * ‖x‖ ^ 2)) =
      fun x => src.rhoDensity a (‖x‖ ^ 2 / 2) * Real.exp (-ε * ‖x‖ ^ 2) := by
    ext x
    rw [ENNReal.toReal_ofReal (src.rhoDensity_nonneg ha (by positivity)), smul_eq_mul]
  rw [heq_dens]
  have hcont_f : Continuous (fun x : RadialSpace src.w =>
      src.rhoDensity a (‖x‖ ^ 2 / 2) * Real.exp (-ε * ‖x‖ ^ 2)) :=
    ((src.continuous_rhoDensity a).comp ((continuous_norm.pow 2).div_const 2)).mul
      (by fun_prop : Continuous fun x : RadialSpace src.w => Real.exp (-ε * ‖x‖ ^ 2))
  refine (hint_g.const_mul (C * K₁)).mono' hcont_f.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hrho_nn : 0 ≤ src.rhoDensity a (‖x‖ ^ 2 / 2) := src.rhoDensity_nonneg ha (by positivity)
  rw [Real.norm_of_nonneg (mul_nonneg hrho_nn (Real.exp_pos _).le)]
  have h1 : src.rhoDensity a (‖x‖ ^ 2 / 2) ≤ C * euclideanWeight b d x := by
    have hraw := hrho_le (‖x‖ ^ 2 / 2) (by positivity)
    rwa [← euclideanWeight_eq_cardyWeight b d x] at hraw
  have h2 := rpow_sq_mul_exp_le_exp b d ‖x‖ (norm_nonneg x)
  have hb_nonpos : b ≤ 0 := by
    have hw1 : (1 : ℝ) ≤ (src.w : ℝ) := by exact_mod_cast src.hw
    dsimp [b]; linarith
  have hw_le : euclideanWeight b d x ≤ Real.exp (C₁ * ‖x‖) := by
    have h1pow : (1 + ‖x‖ ^ 2) ^ b ≤ (1 + ‖x‖ ^ 2) ^ |b| :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg ‖x‖]) (hb_nonpos.trans (abs_nonneg b))
    have hde : Real.exp (d * ‖x‖) ≤ Real.exp (|d| * ‖x‖) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self d) (norm_nonneg x))
    calc euclideanWeight b d x = (1 + ‖x‖ ^ 2) ^ b * Real.exp (d * ‖x‖) := rfl
      _ ≤ (1 + ‖x‖ ^ 2) ^ |b| * Real.exp (|d| * ‖x‖) :=
          mul_le_mul h1pow hde (Real.exp_pos _).le (Real.rpow_pos_of_pos (by positivity) _).le
      _ ≤ Real.exp (C₁ * ‖x‖) := h2
  have hK₁_le := hK₁ ‖x‖ (norm_nonneg x)
  have hexp_split : Real.exp (C₁ * ‖x‖) * Real.exp (-ε * ‖x‖ ^ 2) ≤
      K₁ * Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2) := by
    calc Real.exp (C₁ * ‖x‖) * Real.exp (-ε * ‖x‖ ^ 2)
        = Real.exp (C₁ * ‖x‖ + -ε * ‖x‖ ^ 2) := (Real.exp_add _ _).symm
      _ = Real.exp ((C₁ * ‖x‖ - π * (ε / 2 / π) * ‖x‖ ^ 2) +
            (-π * (ε / 2 / π) * ‖x‖ ^ 2)) := by
          congr 1; field_simp; ring
      _ = Real.exp (C₁ * ‖x‖ - π * (ε / 2 / π) * ‖x‖ ^ 2) *
            Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2) := Real.exp_add _ _
      _ ≤ K₁ * Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hK₁_le (Real.exp_pos _).le
  calc src.rhoDensity a (‖x‖ ^ 2 / 2) * Real.exp (-ε * ‖x‖ ^ 2)
      ≤ (C * Real.exp (C₁ * ‖x‖)) * Real.exp (-ε * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left hw_le hC_pos.le))
          (Real.exp_pos _).le
    _ = C * (Real.exp (C₁ * ‖x‖) * Real.exp (-ε * ‖x‖ ^ 2)) := by ring
    _ ≤ C * (K₁ * Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp_split hC_pos.le
    _ = C * K₁ * Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2) := by ring

lemma integrable_rhoLiftS_of_cardy {src : ShiftSource} {a : ℝ}
    (ha : CrossingBounds src a) {h : ℝ → ℝ} (hh : ContinuousOn h (Ici 0))
    (hint : IntegrableOn (fun t => |h t| * src.cardyV a t) (Ioi 0)) :
    Integrable (radialLiftReal src.w h) (rhoLiftS src a) := by
  unfold rhoLiftS
  have hmeas : Measurable (fun x : RadialSpace src.w =>
      ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))) :=
    (ENNReal.continuous_ofReal.comp ((src.continuous_rhoDensity a).comp
      ((continuous_norm.pow 2).div_const 2))).measurable
  rw [integrable_withDensity_iff_integrable_smul' hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have heq : (fun x : RadialSpace src.w =>
      (ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))).toReal • radialLiftReal src.w h x) =
      fun x => src.rhoDensity a (‖x‖ ^ 2 / 2) * h (‖x‖ ^ 2 / 2) := by
    ext x
    rw [ENNReal.toReal_ofReal (src.rhoDensity_nonneg ha (by positivity)), smul_eq_mul]
    rfl
  rw [heq]
  have hint_rad : Integrable (radialLift src.w (fun t => src.rhoDensity a t * h t)) := by
    rw [integrable_radialLift_iff src.hw]
    let c₀ : ℝ := ((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)
    have h1 : IntegrableOn (fun t => c₀ * (|h t| * src.cardyV a t)) (Ioi 0) :=
      hint.const_mul c₀
    have hcont_t : ContinuousOn (fun t => t ^ (src.w - 1) * (src.rhoDensity a t * h t)) (Ioi 0) :=
      ((continuous_id.pow _).continuousOn.mul
        ((src.continuous_rhoDensity a).continuousOn.mul hh)).mono Ioi_subset_Ici_self
    refine h1.mono' (hcont_t.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := Set.mem_Ioi.mp ht
    have hV_nn : 0 ≤ src.cardyV a t := src.cardyV_nonneg ha ht_pos.le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (pow_pos ht_pos _),
      abs_of_nonneg (src.rhoDensity_nonneg ha ht_pos.le)]
    have heq_t : t ^ (src.w - 1) * src.rhoDensity a t = c₀ * src.cardyV a t := by
      unfold ShiftSource.rhoDensity
      rw [src.cardyV_eq_pow_mul_reduced]
      dsimp [c₀]; ring
    rw [← mul_assoc, heq_t]
    exact le_of_eq (by ring)
  exact (integrable_radialLift_iff_real src.w _).mp hint_rad |>.congr
    (Eventually.of_forall fun x => rfl)

lemma integral_rhoLiftS (src : ShiftSource) {a : ℝ} (ha : CrossingBounds src a)
    (h : ℝ → ℝ) :
    ∫ x : RadialSpace src.w, radialLiftReal src.w h x ∂(rhoLiftS src a) =
      ∫ t in Ioi 0, h t * src.cardyDensity a t := by
  unfold rhoLiftS
  have hmeas : Measurable (fun x : RadialSpace src.w =>
      ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))) :=
    (ENNReal.continuous_ofReal.comp ((src.continuous_rhoDensity a).comp
      ((continuous_norm.pow 2).div_const 2))).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have heq : (fun x : RadialSpace src.w =>
      (ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))).toReal • radialLiftReal src.w h x) =
      fun x => h (‖x‖ ^ 2 / 2) * src.rhoDensity a (‖x‖ ^ 2 / 2) := by
    ext x
    rw [ENNReal.toReal_ofReal (src.rhoDensity_nonneg ha (by positivity)), smul_eq_mul, mul_comm]
    rfl
  rw [heq]
  exact src.integral_rhoDensity a h

lemma integral_rhoLiftS_eq_neg_gVac (src : ShiftSource) {a : ℝ} (ha : CrossingBounds src a)
    (g : ℝ → ℝ) :
    ∫ x : RadialSpace src.w, radialLiftReal src.w g x ∂(rhoLiftS src a) = -src.gVac a g := by
  rw [integral_rhoLiftS src ha g]
  unfold ShiftSource.gVac ShiftSource.cardyDensity
  have heq : (fun t => g t * (2 * π * src.cardyV a t)) = fun t => (2 * π) * (g t * src.cardyV a t) := by
    ext t; ring
  rw [heq, integral_const_mul]
  ring

private lemma mehlerKernel_mul_euclideanWeight_integrable {w : ℕ} (b d : ℝ)
    {r : ℝ} (hr12 : 1 / 2 ≤ r) (hr1 : r < 1) (x : RadialSpace w) :
    Integrable (fun y : RadialSpace w => mehlerKernel w r x y * euclideanWeight b d y) := by
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have h1r2_nn : 0 ≤ (1 - r) / 2 := by linarith
  have hrp_nn : 0 ≤ ((1 - r) / 2) ^ (-(w : ℝ)) := Real.rpow_nonneg h1r2_nn _
  have h2b_nn : 0 ≤ (2 : ℝ) ^ |b| := (Real.rpow_pos_of_pos (by norm_num) _).le
  let D₁ : ℝ := 2 * (Nat.ceil |b| : ℝ) + |d|
  let g_dom : RadialSpace w → ℝ := fun y =>
    (2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ)) *
      Real.exp (D₁ * ‖y - x‖ - π / (1 - r) * ‖y - x‖ ^ 2)
  have hg_dom_int : Integrable g_dom := by
    have h1 := (integrable_exp_linear_sub_gaussian w D₁ (one_div_pos.mpr h1r_pos)).comp_sub_right x
    have heq : g_dom = fun y => ((2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ))) *
        Real.exp (D₁ * ‖y - x‖ - π * (1 / (1 - r)) * ‖y - x‖ ^ 2) := by
      ext y; dsimp [g_dom]; congr 2; ring
    rw [heq]; exact h1.const_mul _
  have hW_cont : Continuous (euclideanWeight b d : RadialSpace w → ℝ) := by
    unfold euclideanWeight
    refine Continuous.mul (continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.rpow (continuousAt_const.add ((continuous_norm.pow 2).continuousAt))
        continuousAt_const (Or.inl (by positivity))) (by fun_prop)
  refine hg_dom_int.mono'
    ((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)
      |>.mul hW_cont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (mehlerKernel_nonneg w hr1 x y)
    (euclideanWeight_pos b d y).le)]
  have hk := mehlerKernel_le_half_gaussian w hr12 hr1 x y
  rw [norm_sub_rev x y] at hk
  have hw := euclideanWeight_ratio_le b d x y
  have hexp := rpow_sq_mul_exp_le_exp b d ‖y - x‖ (norm_nonneg _)
  have hw' : euclideanWeight b d y ≤ (2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖) :=
    hw.trans (mul_le_mul_of_nonneg_left hexp (mul_nonneg h2b_nn (euclideanWeight_pos b d x).le))
  calc mehlerKernel w r x y * euclideanWeight b d y
      ≤ (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
          ((2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) :=
        mul_le_mul hk hw' (euclideanWeight_pos b d y).le (mul_nonneg hrp_nn (Real.exp_pos _).le)
    _ = g_dom y := by
        dsimp [g_dom]
        rw [show (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
            ((2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) =
            (2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ)) *
              (Real.exp (D₁ * ‖y - x‖) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) by ring]
        rw [← Real.exp_add]; congr 2; ring

private lemma tendsto_mehlerMean_rhoLiftS (src : ShiftSource) {a : ℝ}
    (ha : CrossingBounds src a) (ha_pos : 0 < a) {g : ℝ → ℝ} (hg : TestClass src a g) :
    Tendsto (fun r => ∫ x : RadialSpace src.w, mehlerMean src.w r (radialLiftReal src.w g) x
        ∂(rhoLiftS src a))
      (𝓝[<] 1) (𝓝 (∫ x : RadialSpace src.w, radialLiftReal src.w g x ∂(rhoLiftS src a))) := by
  let f : RadialSpace src.w → ℝ := radialLiftReal src.w g
  let rhoTil : RadialSpace src.w → ℝ := fun x => src.rhoDensity a (‖x‖ ^ 2 / 2)
  have hrho_cont : Continuous rhoTil :=
    (src.continuous_rhoDensity a).comp ((continuous_norm.pow 2).div_const 2)
  have hrho_nn : ∀ x, 0 ≤ rhoTil x := fun x => src.rhoDensity_nonneg ha (by positivity)
  obtain ⟨hf_cont, hf_bd⟩ := radialLift_bounded_continuous_of_fourier_odd hg.int_lift hg.fourier_odd
  let B : ℝ := ∫ y : RadialSpace src.w, ‖radialLift src.w g y‖
  have hB_nn : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  let b : ℝ := -((src.w - 1 : ℝ) / 2 + 1 / 4)
  let d : ℝ := 2 * Real.sqrt 2 * π * Real.sqrt a
  obtain ⟨C_hi, hC_hi_pos, hrho_hi⟩ := src.rhoDensity_le_cardyWeight ha ha_pos
  obtain ⟨c_lo, T₀, hc_lo_pos, _, hrho_lo⟩ := src.rhoDensity_ge_cardyWeight_large ha ha_pos
  obtain ⟨C', _, hW_stab⟩ := mehlerMean_euclideanWeight_le src.w b d
  have hrho_dom : ∀ x : RadialSpace src.w, |rhoTil x| ≤ C_hi * euclideanWeight b d x := fun x => by
    rw [abs_of_nonneg (hrho_nn x)]
    exact (hrho_hi (‖x‖ ^ 2 / 2) (by positivity)).trans_eq (by rw [euclideanWeight_eq_cardyWeight])
  have hf_rho_int : Integrable (fun y : RadialSpace src.w => |f y| * rhoTil y) volume := by
    have h1 := integrable_rhoLiftS_of_cardy ha hg.cont.abs (by simpa only [abs_abs] using hg.int_cardy)
    change Integrable (fun x : RadialSpace src.w => |g (‖x‖ ^ 2 / 2)|) (rhoLiftS src a) at h1
    unfold rhoLiftS at h1
    have hmeas : Measurable (fun x : RadialSpace src.w =>
        ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))) :=
      (ENNReal.continuous_ofReal.comp hrho_cont).measurable
    rw [integrable_withDensity_iff_integrable_smul' hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at h1
    refine h1.congr (Eventually.of_forall fun x => ?_)
    dsimp only [rhoTil]
    rw [ENNReal.toReal_ofReal (hrho_nn x), smul_eq_mul, mul_comm]
    rfl
  have hf_W_int : Integrable (fun y : RadialSpace src.w => |f y| * euclideanWeight b d y) volume := by
    let R₀ : ℝ := Real.sqrt (2 * T₀)
    let M_in : ℝ := B * (1 + R₀ ^ 2) ^ |b| * Real.exp (|d| * R₀)
    let g_maj : RadialSpace src.w → ℝ := fun y =>
      (1 / c_lo) * (|f y| * rhoTil y) +
        Set.indicator (Metric.closedBall (0 : RadialSpace src.w) R₀) (fun _ => M_in) y
    have hmaj_int : Integrable g_maj volume :=
      (hf_rho_int.const_mul _).add ((integrable_indicator_iff measurableSet_closedBall).mpr
        (integrableOn_const (C := M_in) (hs := measure_closedBall_lt_top.ne)))
    have hW_cont : Continuous (euclideanWeight b d : RadialSpace src.w → ℝ) := by
      unfold euclideanWeight
      refine Continuous.mul (continuous_iff_continuousAt.mpr fun y =>
        ContinuousAt.rpow (continuousAt_const.add ((continuous_norm.pow 2).continuousAt))
          continuousAt_const (Or.inl (by positivity))) (by fun_prop)
    refine hmaj_int.mono' (hf_cont.abs.mul hW_cont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (euclideanWeight_pos b d y).le)]
    rcases le_or_gt ‖y‖ R₀ with hy_in | hy_out
    · have hmem : y ∈ Metric.closedBall (0 : RadialSpace src.w) R₀ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hy_in
      have h1pow : (1 + ‖y‖ ^ 2) ^ b ≤ (1 + R₀ ^ 2) ^ |b| := by
        have hb_nn : b ≤ 0 := by
          have hw1 : (1 : ℝ) ≤ (src.w : ℝ) := by exact_mod_cast src.hw
          dsimp [b]; linarith
        calc (1 + ‖y‖ ^ 2) ^ b ≤ (1 + ‖y‖ ^ 2) ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg ‖y‖]) hb_nn
          _ = 1 := Real.rpow_zero _
          _ ≤ (1 + R₀ ^ 2) ^ |b| := Real.one_le_rpow (by linarith [sq_nonneg R₀]) (abs_nonneg b)
      have hexp_le : Real.exp (d * ‖y‖) ≤ Real.exp (|d| * R₀) :=
        Real.exp_le_exp.mpr (calc d * ‖y‖ ≤ |d| * ‖y‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self d) (norm_nonneg y)
          _ ≤ |d| * R₀ := mul_le_mul_of_nonneg_left hy_in (abs_nonneg d))
      have hW_le : euclideanWeight b d y ≤ (1 + R₀ ^ 2) ^ |b| * Real.exp (|d| * R₀) :=
        mul_le_mul h1pow hexp_le (Real.exp_pos _).le (by positivity)
      have h1 : |f y| * euclideanWeight b d y ≤ M_in := by
        calc |f y| * euclideanWeight b d y ≤ B * ((1 + R₀ ^ 2) ^ |b| * Real.exp (|d| * R₀)) :=
              mul_le_mul (hf_bd y) hW_le (euclideanWeight_pos b d y).le hB_nn
          _ = M_in := by dsimp [M_in]; ring
      have hnonneg : 0 ≤ (1 / c_lo) * (|f y| * rhoTil y) :=
        mul_nonneg (by positivity) (mul_nonneg (abs_nonneg _) (hrho_nn y))
      dsimp [g_maj]
      rw [Set.indicator_of_mem hmem]
      linarith
    · have hnot : y ∉ Metric.closedBall (0 : RadialSpace src.w) R₀ := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy_out
      have ht_ge : T₀ ≤ ‖y‖ ^ 2 / 2 := by
        have hsq : R₀ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy_out.le 2
        rw [Real.sq_sqrt (by positivity)] at hsq
        linarith
      have hcardy_le := hrho_lo (‖y‖ ^ 2 / 2) ht_ge
      rw [← euclideanWeight_eq_cardyWeight] at hcardy_le
      have hW_le : euclideanWeight b d y ≤ (1 / c_lo) * rhoTil y := by
        rw [one_div_mul_eq_div, le_div_iff₀ hc_lo_pos, mul_comm]
        exact hcardy_le
      dsimp [g_maj]
      rw [Set.indicator_of_notMem hnot, add_zero]
      calc |f y| * euclideanWeight b d y ≤ |f y| * ((1 / c_lo) * rhoTil y) :=
            mul_le_mul_of_nonneg_left hW_le (abs_nonneg _)
        _ = (1 / c_lo) * (|f y| * rhoTil y) := by ring
  have hint_eval : (fun r => ∫ x : RadialSpace src.w,
        mehlerMean src.w r f x ∂(rhoLiftS src a)) =ᶠ[𝓝[<] 1]
      (fun r => ∫ y : RadialSpace src.w, f y * mehlerMean src.w r rhoTil y ∂volume) := by
    filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
    have hr1 : r < 1 := hr.2
    have hrew : ∫ x : RadialSpace src.w, mehlerMean src.w r f x ∂(rhoLiftS src a) =
        ∫ x : RadialSpace src.w, mehlerMean src.w r f x * rhoTil x ∂volume := by
      unfold rhoLiftS
      have hmeas : Measurable (fun x : RadialSpace src.w =>
          ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))) :=
        (ENNReal.continuous_ofReal.comp hrho_cont).measurable
      rw [integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only [rhoTil]
      rw [ENNReal.toReal_ofReal (hrho_nn x), smul_eq_mul, mul_comm]
    rw [hrew]
    have hprod_int : Integrable (Function.uncurry fun x y : RadialSpace src.w =>
        (mehlerKernel src.w r x y * f y) * rhoTil x) (volume.prod volume) := by
      have haesm : AEStronglyMeasurable (Function.uncurry fun x y : RadialSpace src.w =>
          (mehlerKernel src.w r x y * f y) * rhoTil x) (volume.prod volume) :=
        (((continuous_mehlerKernel src.w r).mul (hf_cont.comp continuous_snd)).mul
          (hrho_cont.comp continuous_fst)).aestronglyMeasurable
      rw [integrable_prod_iff' haesm]
      refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
      · have hW := mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr1 y
        have hcont_x : Continuous (fun x : RadialSpace src.w =>
            mehlerKernel src.w r x y * f y * rhoTil x) :=
          (((continuous_mehlerKernel src.w r).comp (continuous_id.prodMk continuous_const)).mul
            continuous_const).mul hrho_cont
        refine (hW.const_mul (|f y| * C_hi)).mono' hcont_x.aestronglyMeasurable
          (Eventually.of_forall fun x => ?_)
        dsimp only [Function.uncurry]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mehlerKernel_nonneg src.w hr1 x y),
          mehlerKernel_symm src.w r x y]
        calc mehlerKernel src.w r y x * |f y| * |rhoTil x|
            ≤ mehlerKernel src.w r y x * |f y| * (C_hi * euclideanWeight b d x) :=
              mul_le_mul_of_nonneg_left (hrho_dom x)
                (mul_nonneg (mehlerKernel_nonneg src.w hr1 y x) (abs_nonneg _))
          _ = |f y| * C_hi * (mehlerKernel src.w r y x * euclideanWeight b d x) := by ring
      · have heq_y : (fun y : RadialSpace src.w =>
            ∫ x : RadialSpace src.w, ‖(Function.uncurry fun x y : RadialSpace src.w =>
              mehlerKernel src.w r x y * f y * rhoTil x) (x, y)‖) =
            fun y => |f y| * mehlerMean src.w r rhoTil y := by
          ext y
          have hker_rho : ∀ x, ‖mehlerKernel src.w r x y * f y * rhoTil x‖ =
              |f y| * (mehlerKernel src.w r y x * rhoTil x) := fun x => by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mehlerKernel_nonneg src.w hr1 x y),
              abs_of_nonneg (hrho_nn x), mehlerKernel_symm src.w r x y]
            ring
          simp_rw [Function.uncurry_apply_pair, hker_rho, integral_const_mul]
          rfl
        rw [heq_y]
        have haesm_Ar : AEStronglyMeasurable (mehlerMean src.w r rhoTil) volume :=
          (((continuous_mehlerKernel src.w r).mul (hrho_cont.comp continuous_snd)).aestronglyMeasurable).integral_prod_right'
        refine (hf_W_int.const_mul (C_hi * C')).mono' (hf_cont.abs.aestronglyMeasurable.mul haesm_Ar)
          (Eventually.of_forall fun y => ?_)
        · have hAr_nn : 0 ≤ mehlerMean src.w r rhoTil y :=
            integral_nonneg fun x => mul_nonneg (mehlerKernel_nonneg src.w hr1 y x) (hrho_nn x)
          rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hAr_nn)]
          have hAr_ub : mehlerMean src.w r rhoTil y ≤ C_hi * C' * euclideanWeight b d y := by
            have h1 : mehlerMean src.w r rhoTil y ≤ C_hi * mehlerMean src.w r (euclideanWeight b d) y := by
              unfold mehlerMean
              rw [← integral_const_mul]
              refine integral_mono
                ((mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr1 y).const_mul C_hi |>.mono'
                  (((continuous_mehlerKernel src.w r).comp
                    (Continuous.prodMk continuous_const continuous_id)).mul hrho_cont).aestronglyMeasurable
                  (Eventually.of_forall fun x => by
                    rw [Real.norm_of_nonneg (mul_nonneg (mehlerKernel_nonneg src.w hr1 y x) (hrho_nn x)),
                      ← mul_assoc, mul_comm C_hi (mehlerKernel src.w r y x), mul_assoc]
                    exact mul_le_mul_of_nonneg_left
                      (by simpa [abs_of_nonneg (hrho_nn x)] using hrho_dom x)
                      (mehlerKernel_nonneg src.w hr1 y x)))
                ((mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr1 y).const_mul C_hi)
                (fun x => by
                  rw [← mul_assoc, mul_comm C_hi (mehlerKernel src.w r y x), mul_assoc]
                  exact mul_le_mul_of_nonneg_left
                    (by simpa [abs_of_nonneg (hrho_nn x)] using hrho_dom x)
                    (mehlerKernel_nonneg src.w hr1 y x))
            exact h1.trans (by nlinarith [hW_stab hr y])
          calc |f y| * mehlerMean src.w r rhoTil y
              ≤ |f y| * (C_hi * C' * euclideanWeight b d y) :=
                mul_le_mul_of_nonneg_left hAr_ub (abs_nonneg _)
            _ = C_hi * C' * (|f y| * euclideanWeight b d y) := by ring
    have hswap := integral_integral_swap hprod_int
    calc ∫ x : RadialSpace src.w, mehlerMean src.w r f x * rhoTil x
        = ∫ x : RadialSpace src.w, ∫ y : RadialSpace src.w,
            mehlerKernel src.w r x y * f y * rhoTil x := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          unfold mehlerMean
          exact (integral_mul_const (rhoTil x) _).symm
      _ = ∫ y : RadialSpace src.w, ∫ x : RadialSpace src.w,
            mehlerKernel src.w r x y * f y * rhoTil x := hswap
      _ = ∫ y : RadialSpace src.w, f y * mehlerMean src.w r rhoTil y := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          have heq_x : (fun x => mehlerKernel src.w r x y * f y * rhoTil x) =
              fun x => f y * (mehlerKernel src.w r y x * rhoTil x) := by
            ext x; rw [mehlerKernel_symm src.w r x y]; ring
          dsimp only
          rw [heq_x, integral_const_mul]
          rfl
  have hdom_tend : Tendsto (fun r => ∫ y : RadialSpace src.w, f y * mehlerMean src.w r rhoTil y ∂volume)
      (𝓝[<] 1) (𝓝 (∫ y : RadialSpace src.w, f y * rhoTil y ∂volume)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (F := fun r y => f y * mehlerMean src.w r rhoTil y)
      (f := fun y => f y * rhoTil y)
      (bound := fun y => (C_hi * C') * (|f y| * euclideanWeight b d y)) ?_ ?_ (hf_W_int.const_mul _) ?_
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r ⟨_, hr1⟩
      exact hf_cont.aestronglyMeasurable.mul
        (((continuous_mehlerKernel src.w r).mul (hrho_cont.comp continuous_snd)).aestronglyMeasurable).integral_prod_right'
    · filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
      filter_upwards with y
      have hAr_nn : 0 ≤ mehlerMean src.w r rhoTil y :=
        integral_nonneg fun x => mul_nonneg (mehlerKernel_nonneg src.w hr.2 y x) (hrho_nn x)
      have hAr_ub : mehlerMean src.w r rhoTil y ≤ C_hi * C' * euclideanWeight b d y := by
        have h1 : mehlerMean src.w r rhoTil y ≤ C_hi * mehlerMean src.w r (euclideanWeight b d) y := by
          unfold mehlerMean
          rw [← integral_const_mul]
          refine integral_mono
            ((mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr.2 y).const_mul C_hi |>.mono'
              (((continuous_mehlerKernel src.w r).comp
                (Continuous.prodMk continuous_const continuous_id)).mul hrho_cont).aestronglyMeasurable
              (Eventually.of_forall fun x => by
                rw [Real.norm_of_nonneg (mul_nonneg (mehlerKernel_nonneg src.w hr.2 y x) (hrho_nn x)),
                  ← mul_assoc, mul_comm C_hi (mehlerKernel src.w r y x), mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (by simpa [abs_of_nonneg (hrho_nn x)] using hrho_dom x)
                  (mehlerKernel_nonneg src.w hr.2 y x)))
            ((mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr.2 y).const_mul C_hi)
            (fun x => by
              rw [← mul_assoc, mul_comm C_hi (mehlerKernel src.w r y x), mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (by simpa [abs_of_nonneg (hrho_nn x)] using hrho_dom x)
                (mehlerKernel_nonneg src.w hr.2 y x))
        exact h1.trans (by nlinarith [hW_stab hr y])
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hAr_nn]
      calc |f y| * mehlerMean src.w r rhoTil y
          ≤ |f y| * (C_hi * C' * euclideanWeight b d y) :=
            mul_le_mul_of_nonneg_left hAr_ub (abs_nonneg _)
        _ = (C_hi * C') * (|f y| * euclideanWeight b d y) := by ring
    · filter_upwards with y
      exact tendsto_const_nhds.mul (tendsto_mehlerMean_of_continuous_weight hrho_cont hC_hi_pos.le hrho_dom y)
  have hrho_target : ∫ y : RadialSpace src.w, f y * rhoTil y ∂volume =
      ∫ x : RadialSpace src.w, radialLiftReal src.w g x ∂(rhoLiftS src a) := by
    unfold rhoLiftS
    have hmeas : Measurable (fun x : RadialSpace src.w =>
        ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))) :=
      (ENNReal.continuous_ofReal.comp hrho_cont).measurable
    rw [integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only [rhoTil]
    rw [ENNReal.toReal_ofReal (hrho_nn x), smul_eq_mul, mul_comm]
  rw [hrho_target] at hdom_tend
  exact hdom_tend.congr' hint_eval.symm


/-- Counting bound (`fw:counting` in `crossing_sum_rule.tex`): for any admissible crossing
measure `ν`, `ν([0, R]) ≤ C * (1 + √R)^w * exp(4π √(a R))` for all `R ≥ 0`. -/
theorem crossing_counting_bound_src (src : ShiftSource) {a : ℝ}
    (ha : CrossingBounds src a) (ha_pos : 0 < a) (meas : SourceCrossingMeasure src a) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R →
      (meas.ν (Icc 0 R)).toReal ≤
        C * (1 + Real.sqrt R) ^ src.w * Real.exp (4 * π * Real.sqrt (a * R)) := by
  let I₁ : ℝ := ∫ t in Ici 0, Real.exp (-2 * π * 1 * t) ∂meas.ν
  have hI₁_nn : 0 ≤ I₁ := setIntegral_nonneg measurableSet_Ici fun _ _ => (Real.exp_pos _).le
  let c₀ : ℝ := max 1 (1 / Real.sqrt a)
  have hc₀_ge1 : 1 ≤ c₀ := le_max_left _ _
  have hc₀_sqrt : 1 / Real.sqrt a ≤ c₀ := le_max_right _ _
  let C : ℝ := c₀ ^ src.w * (I₁ + src.tv + 1) * Real.exp (2 * π * a)
  have hJ_pos : 0 < I₁ + src.tv + 1 := by linarith [src.tv_nonneg]
  have hC_pos : 0 < C := mul_pos (mul_pos (pow_pos (by linarith) _) hJ_pos) (Real.exp_pos _)
  refine ⟨C, hC_pos, fun R hR => ?_⟩
  let β : ℝ := Real.sqrt (a / (R + a))
  have hRa_pos : 0 < R + a := by linarith
  have hβ_pos : 0 < β := Real.sqrt_pos.mpr (div_pos ha_pos hRa_pos)
  have hβ_le1 : β ≤ 1 := Real.sqrt_le_one.mpr (div_le_one_of_le₀ (by linarith) hRa_pos.le)
  have hlap_β := meas.finite_laplace hβ_pos
  have hlap_inv := meas.finite_laplace (inv_pos.mpr hβ_pos)
  have hlap_1 := meas.finite_laplace one_pos
  have hcross := meas.crossing hβ_pos
  have hthermal_eq : ∫ t in Ici 0, thermalDiff src.w β t ∂meas.ν =
      (∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν) -
        β ^ (-(src.w : ℝ)) * ∫ t in Ici 0, Real.exp (-2 * π * β⁻¹ * t) ∂meas.ν := by
    have heq : (fun t => thermalDiff src.w β t) = fun t =>
        Real.exp (-2 * π * β * t) - β ^ (-(src.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t) := by
      ext t; unfold thermalDiff; rw [div_eq_mul_inv]; ring_nf
    rw [heq, integral_sub hlap_β (hlap_inv.const_mul _), integral_const_mul]
  have hcardy_eq : ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyDensity a t ≤
      β ^ (-(src.w : ℝ)) * (src.tv * Real.exp (2 * π * a / β)) := by
    have h1 := src.cardyV_laplace a hβ_pos
    have h1' := src.cardyV_laplace a (inv_pos.mpr hβ_pos)
    have hV_nonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ src.cardyV a t := fun t ht =>
      ha.nonneg t (Set.mem_Ioi.mp ht).le
    have hmono : ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyDensity a t ≤
        ∫ t in Ioi 0, Real.exp (-2 * π * β * t) * src.cardyDensity a t := by
      have hint_L : IntegrableOn (fun t => thermalDiff src.w β t * src.cardyDensity a t) (Ioi 0) := by
        have heq_l : (fun t => thermalDiff src.w β t * src.cardyDensity a t) =
            fun t => (2 * π) * (src.cardyV a t * Real.exp (-2 * π * β * t)) -
              (2 * π) * β ^ (-(src.w : ℝ)) * (src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) := by
          ext t
          unfold thermalDiff ShiftSource.cardyDensity
          rw [div_eq_mul_inv]; ring_nf
        rw [heq_l]
        exact (h1.1.const_mul (2 * π)).sub (h1'.1.const_mul _)
      have hint_R : IntegrableOn (fun t => Real.exp (-2 * π * β * t) * src.cardyDensity a t) (Ioi 0) := by
        have heq_r : (fun t => Real.exp (-2 * π * β * t) * src.cardyDensity a t) =
            fun t => (2 * π) * (src.cardyV a t * Real.exp (-2 * π * β * t)) := by
          ext t; unfold ShiftSource.cardyDensity; ring
        rw [heq_r]
        exact h1.1.const_mul (2 * π)
      refine setIntegral_mono_on hint_L hint_R measurableSet_Ioi fun t ht => ?_
      have hcard_nn : 0 ≤ src.cardyDensity a t := by
        unfold ShiftSource.cardyDensity
        exact mul_nonneg (by positivity) (hV_nonneg t ht)
      refine mul_le_mul_of_nonneg_right ?_ hcard_nn
      unfold thermalDiff
      linarith [mul_nonneg (Real.rpow_nonneg hβ_pos.le (-(src.w : ℝ)))
        (Real.exp_pos (-2 * π * t / β)).le]
    have hcard_lap : ∫ t in Ioi 0, Real.exp (-2 * π * β * t) * src.cardyDensity a t =
        β ^ (-(src.w : ℝ)) * src.srcFun a β⁻¹ := by
      have heq_l : (fun t => Real.exp (-2 * π * β * t) * src.cardyDensity a t) =
          fun t => (2 * π) * (src.cardyV a t * Real.exp (-2 * π * β * t)) := by
        ext t; unfold ShiftSource.cardyDensity; ring
      rw [heq_l, integral_const_mul, h1.2]
    have hF_le : src.srcFun a β⁻¹ ≤ src.tv * Real.exp (2 * π * a / β) := by
      unfold ShiftSource.srcFun ShiftSource.tv
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      have hex : Real.exp (2 * π * (a - src.shift j) * β⁻¹) ≤ Real.exp (2 * π * a / β) := by
        refine Real.exp_le_exp.mpr ?_
        have := src.hshift j
        have hβi : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ_pos.le
        rw [div_eq_mul_inv]
        nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * π) this) hβi]
      calc src.coef j * Real.exp (2 * π * (a - src.shift j) * β⁻¹)
          ≤ |src.coef j| * Real.exp (2 * π * (a - src.shift j) * β⁻¹) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
        _ ≤ |src.coef j| * Real.exp (2 * π * a / β) :=
            mul_le_mul_of_nonneg_left hex (abs_nonneg _)
    calc ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyDensity a t
        ≤ β ^ (-(src.w : ℝ)) * src.srcFun a β⁻¹ := hmono.trans_eq hcard_lap
      _ ≤ β ^ (-(src.w : ℝ)) * (src.tv * Real.exp (2 * π * a / β)) :=
          mul_le_mul_of_nonneg_left hF_le (Real.rpow_nonneg hβ_pos.le _)
  have hinv_le : ∫ t in Ici 0, Real.exp (-2 * π * β⁻¹ * t) ∂meas.ν ≤ I₁ := by
    refine setIntegral_mono_on hlap_inv hlap_1 measurableSet_Ici fun t ht => ?_
    refine Real.exp_le_exp.mpr ?_
    have h1β : 1 ≤ β⁻¹ := one_le_inv₀ hβ_pos |>.mpr hβ_le1
    have ht_nn : 0 ≤ t := Set.mem_Ici.mp ht
    linarith [mul_le_mul_of_nonneg_left h1β (mul_nonneg (by positivity : 0 ≤ 2 * π) ht_nn)]
  have hIβ_le : ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν ≤
      β ^ (-(src.w : ℝ)) * (I₁ + src.tv + 1) * Real.exp (2 * π * a / β) := by
    have h1exp : 1 ≤ Real.exp (2 * π * a / β) := Real.one_le_exp (by positivity)
    calc ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν
        = β ^ (-(src.w : ℝ)) * (∫ t in Ici 0, Real.exp (-2 * π * β⁻¹ * t) ∂meas.ν) +
            ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyDensity a t := by linarith [hthermal_eq, hcross]
      _ ≤ β ^ (-(src.w : ℝ)) * I₁ + β ^ (-(src.w : ℝ)) * (src.tv * Real.exp (2 * π * a / β)) :=
          add_le_add (mul_le_mul_of_nonneg_left hinv_le (Real.rpow_nonneg hβ_pos.le _)) hcardy_eq
      _ ≤ β ^ (-(src.w : ℝ)) * (I₁ * Real.exp (2 * π * a / β)) +
            β ^ (-(src.w : ℝ)) * (src.tv * Real.exp (2 * π * a / β)) := by
          gcongr; exact le_mul_of_one_le_right hI₁_nn h1exp
      _ ≤ β ^ (-(src.w : ℝ)) * (I₁ + src.tv + 1) * Real.exp (2 * π * a / β) := by
          have h0 : 0 ≤ β ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / β) :=
            mul_nonneg (Real.rpow_nonneg hβ_pos.le _) (Real.exp_pos _).le
          have := src.tv_nonneg
          nlinarith [h0]
  have hmeas_lt_top : meas.ν (Icc 0 R) < ⊤ :=
    admissibleMeasure_Ici_sub_lt_top_src src a meas Subset.rfl
  have hmass_lb : (meas.ν (Icc 0 R)).toReal * Real.exp (-2 * π * β * R) ≤
      ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν := by
    have hmono1 : ∫ t in Icc 0 R, Real.exp (-2 * π * β * R) ∂meas.ν ≤
        ∫ t in Icc 0 R, Real.exp (-2 * π * β * t) ∂meas.ν :=
      setIntegral_mono_on (integrableOn_const (hs := hmeas_lt_top.ne))
        (hlap_β.mono_set Icc_subset_Ici_self) measurableSet_Icc fun t ht => by
        refine Real.exp_le_exp.mpr ?_
        have := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ 2 * π * β)
        linarith
    have hmono2 : ∫ t in Icc 0 R, Real.exp (-2 * π * β * t) ∂meas.ν ≤
        ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν :=
      setIntegral_mono_set hlap_β (Eventually.of_forall fun _ => (Real.exp_pos _).le)
        (Eventually.of_forall fun _ h => Icc_subset_Ici_self h)
    simpa [setIntegral_const, smul_eq_mul, Measure.real] using hmono1.trans hmono2
  have hexp_bound : Real.exp (2 * π * β * R + 2 * π * a / β) ≤
      Real.exp (2 * π * a) * Real.exp (4 * π * Real.sqrt (a * R)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : β * R ≤ Real.sqrt (a * R) := by
      rcases eq_or_lt_of_le hR with rfl | hR_pos
      · simp
      · have hsub : β ≤ Real.sqrt (a / R) :=
          Real.sqrt_le_sqrt (div_le_div_of_nonneg_left ha_pos.le hR_pos (by linarith))
        calc β * R ≤ Real.sqrt (a / R) * R := mul_le_mul_of_nonneg_right hsub hR
          _ = Real.sqrt (a / R) * Real.sqrt (R ^ 2) := by rw [Real.sqrt_sq hR]
          _ = Real.sqrt ((a / R) * R ^ 2) := by rw [← Real.sqrt_mul (by positivity)]
          _ = Real.sqrt (a * R) := by congr 1; field_simp
    have h2 : a / β ≤ Real.sqrt (a * R) + a := by
      have haβ : a / β = Real.sqrt (a * (R + a)) := by
        rw [div_eq_iff hβ_pos.ne']
        dsimp [β]
        rw [← Real.sqrt_mul (mul_nonneg ha_pos.le hRa_pos.le),
          show a * (R + a) * (a / (R + a)) = a ^ 2 by field_simp, Real.sqrt_sq ha_pos.le]
      have hsqrt_add : Real.sqrt (R + a) ≤ Real.sqrt R + Real.sqrt a := by
        rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg R) (Real.sqrt_nonneg a))]
        refine Real.sqrt_le_sqrt ?_
        rw [add_sq, Real.sq_sqrt hR, Real.sq_sqrt ha_pos.le]
        nlinarith [Real.sqrt_nonneg R, Real.sqrt_nonneg a]
      calc a / β = Real.sqrt (a * (R + a)) := haβ
        _ = Real.sqrt a * Real.sqrt (R + a) := Real.sqrt_mul ha_pos.le _
        _ ≤ Real.sqrt a * (Real.sqrt R + Real.sqrt a) := mul_le_mul_of_nonneg_left hsqrt_add (Real.sqrt_nonneg a)
        _ = Real.sqrt a * Real.sqrt R + Real.sqrt a * Real.sqrt a := by ring
        _ = Real.sqrt (a * R) + a := by
            rw [← Real.sqrt_mul ha_pos.le R, Real.mul_self_sqrt ha_pos.le]
    have hadd := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : 0 ≤ 2 * π)
    linarith [show 2 * π * (β * R + a / β) = 2 * π * β * R + 2 * π * a / β by ring,
      show 2 * π * (Real.sqrt (a * R) + (Real.sqrt (a * R) + a)) =
        2 * π * a + 4 * π * Real.sqrt (a * R) by ring]
  have hβ_pow : β ^ (-(src.w : ℝ)) ≤ c₀ ^ src.w * (1 + Real.sqrt R) ^ src.w := by
    have hinv_le1 : β⁻¹ ≤ c₀ * (1 + Real.sqrt R) := by
      have h1 : β⁻¹ = Real.sqrt ((R + a) / a) := by
        dsimp [β]
        rw [Real.sqrt_div ha_pos.le, inv_div, Real.sqrt_div hRa_pos.le]
      have hsqrt_add : Real.sqrt (R + a) ≤ Real.sqrt R + Real.sqrt a := by
        rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg R) (Real.sqrt_nonneg a))]
        refine Real.sqrt_le_sqrt ?_
        rw [add_sq, Real.sq_sqrt hR, Real.sq_sqrt ha_pos.le]
        nlinarith [Real.sqrt_nonneg R, Real.sqrt_nonneg a]
      calc β⁻¹ = Real.sqrt (R + a) / Real.sqrt a := by
            rw [h1, Real.sqrt_div hRa_pos.le]
        _ ≤ (Real.sqrt R + Real.sqrt a) / Real.sqrt a :=
            div_le_div_of_nonneg_right hsqrt_add (Real.sqrt_nonneg a)
        _ = (1 / Real.sqrt a) * Real.sqrt R + 1 := by field_simp
        _ ≤ c₀ * Real.sqrt R + c₀ * 1 := by
            nlinarith [Real.sqrt_nonneg R]
        _ = c₀ * (1 + Real.sqrt R) := by ring
    rw [Real.rpow_neg hβ_pos.le, Real.rpow_natCast]
    calc (β ^ src.w)⁻¹ = (β⁻¹) ^ src.w := (inv_pow β src.w).symm
      _ ≤ (c₀ * (1 + Real.sqrt R)) ^ src.w := pow_le_pow_left₀ (by positivity) hinv_le1 _
      _ = c₀ ^ src.w * (1 + Real.sqrt R) ^ src.w := mul_pow _ _ _
  have hmul_exp : (meas.ν (Icc 0 R)).toReal ≤
      Real.exp (2 * π * β * R) * ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν := by
    rw [← le_div_iff₀ (Real.exp_pos (-2 * π * β * R))] at hmass_lb
    calc (meas.ν (Icc 0 R)).toReal
        ≤ (∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν) / Real.exp (-2 * π * β * R) := hmass_lb
      _ = Real.exp (2 * π * β * R) * ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν := by
          rw [div_eq_mul_inv, ← Real.exp_neg, show -(-2 * π * β * R) = 2 * π * β * R by ring,
            mul_comm]
  calc (meas.ν (Icc 0 R)).toReal
      ≤ Real.exp (2 * π * β * R) * (β ^ (-(src.w : ℝ)) * (I₁ + src.tv + 1) * Real.exp (2 * π * a / β)) :=
        hmul_exp.trans (mul_le_mul_of_nonneg_left hIβ_le (Real.exp_pos _).le)
    _ = β ^ (-(src.w : ℝ)) * (I₁ + src.tv + 1) * Real.exp (2 * π * β * R + 2 * π * a / β) := by
        rw [Real.exp_add]; ring
    _ ≤ (c₀ ^ src.w * (1 + Real.sqrt R) ^ src.w) * (I₁ + src.tv + 1) *
          (Real.exp (2 * π * a) * Real.exp (4 * π * Real.sqrt (a * R))) := by
        have hJ' : 0 ≤ I₁ + src.tv + 1 := hJ_pos.le
        have hβp : 0 ≤ β ^ (-(src.w : ℝ)) := Real.rpow_nonneg hβ_pos.le _
        calc β ^ (-(src.w : ℝ)) * (I₁ + src.tv + 1) * Real.exp (2 * π * β * R + 2 * π * a / β)
            ≤ (c₀ ^ src.w * (1 + Real.sqrt R) ^ src.w) * (I₁ + src.tv + 1) *
                Real.exp (2 * π * β * R + 2 * π * a / β) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ_pow hJ') (Real.exp_pos _).le
          _ ≤ (c₀ ^ src.w * (1 + Real.sqrt R) ^ src.w) * (I₁ + src.tv + 1) *
                (Real.exp (2 * π * a) * Real.exp (4 * π * Real.sqrt (a * R))) :=
              mul_le_mul_of_nonneg_left hexp_bound
                (mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by positivity) _)) hJ')
    _ = C * (1 + Real.sqrt R) ^ src.w * Real.exp (4 * π * Real.sqrt (a * R)) := by
        dsimp [C]; ring


/-- Crossing sum rule (`Lemma FW-X`, part (1): one-sided crossing inequality `fw:crossing`).
Unconditional: the Mehler odd-moment input is proved (`lemma_fwA_part2_unconditional`). -/
theorem lemma_fwX_one_sided_src (src : ShiftSource)
    {a : ℝ} (ha : CrossingBounds src a) (ha_pos : 0 < a)
    (meas : SourceCrossingMeasure src a)
    {g : ℝ → ℝ} (hg : TestClass src a g) {T : ℝ} (hT_nn : ∀ t, T ≤ t → 0 ≤ g t) :
    IntegrableOn g (Ici 0) meas.ν ∧
      src.gVac a g + ∫ t in Ici 0, g t ∂meas.ν ≤ 0 := by
  have : SigmaFinite (nuLiftS src a meas) := nuLiftS_sigmaFinite src a meas
  have : SigmaFinite (rhoLiftS src a) :=
    SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  have hν_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace src.w => Real.exp (-ε * ‖x‖ ^ 2)) (nuLiftS src a meas) :=
    fun hε => nuLiftS_gauss src a meas hε
  have hρ_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace src.w => Real.exp (-ε * ‖x‖ ^ 2)) (rhoLiftS src a) :=
    fun hε => rhoLiftS_gauss src ha ha_pos hε
  have h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace src.w, radialLiftReal src.w (thermalDiff src.w β) x ∂(nuLiftS src a meas) =
        ∫ x : RadialSpace src.w, radialLiftReal src.w (thermalDiff src.w β) x ∂(rhoLiftS src a) := by
    intro β hβ
    rw [integral_nuLiftS src a meas (by unfold thermalDiff; fun_prop :
        Continuous (thermalDiff src.w β)).continuousOn,
      integral_rhoLiftS src ha, meas.crossing hβ]
  have hf_rho := integrable_rhoLiftS_of_cardy ha hg.cont hg.int_cardy
  have htend_rho := tendsto_mehlerMean_rhoLiftS src ha ha_pos hg
  let R : ℝ := Real.sqrt (2 * max T 0)
  have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
  have hneg_supp : ∀ y : RadialSpace src.w, R < ‖y‖ → max (-radialLiftReal src.w g y) 0 = 0 := by
    intro y hy
    have hsq : R ^ 2 < ‖y‖ ^ 2 := pow_lt_pow_left₀ hy hR_nn two_ne_zero
    rw [Real.sq_sqrt (by positivity)] at hsq
    have ht_ge : T ≤ ‖y‖ ^ 2 / 2 := le_trans (le_max_left T 0) (by linarith)
    have hgy_nn : 0 ≤ g (‖y‖ ^ 2 / 2) := hT_nn _ ht_ge
    change max (-g (‖y‖ ^ 2 / 2)) 0 = 0
    exact max_eq_right (by linarith)
  obtain ⟨hint_nu, hle⟩ := lemma_fwA_part2_unconditional (nuLiftS src a meas) (rhoLiftS src a)
    hν_gauss hρ_gauss h_thermal hg.cont hg.int_lift hg.fourier_odd hf_rho hR_nn hneg_supp htend_rho
  rw [integrable_nuLiftS_iff src a meas hg.cont] at hint_nu
  rw [integral_nuLiftS src a meas hg.cont, integral_rhoLiftS_eq_neg_gVac src ha g] at hle
  exact ⟨hint_nu, by linarith⟩

/-- Crossing sum rule (`Lemma FW-X`, part (2): exact equality `fw:crossing` under decay `q > (w+1)/2`).
Unconditional: the Mehler odd-moment input is proved (`lemma_fwA_part2_unconditional`). -/
theorem lemma_fwX_equality_src (src : ShiftSource)
    {a : ℝ} (ha : CrossingBounds src a) (ha_pos : 0 < a)
    (meas : SourceCrossingMeasure src a)
    {g : ℝ → ℝ} (hg : TestClass src a g) {q C_g : ℝ}
    (hq : (src.w + 1 : ℝ) / 2 < q) (hC_g : 0 ≤ C_g)
    (hdecay : ∀ t, 0 ≤ t → |g t| ≤ C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))) :
    IntegrableOn g (Ici 0) meas.ν ∧
      src.gVac a g + ∫ t in Ici 0, g t ∂meas.ν = 0 := by
  have : SigmaFinite (nuLiftS src a meas) := nuLiftS_sigmaFinite src a meas
  have : SigmaFinite (rhoLiftS src a) :=
    SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  have hν_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace src.w => Real.exp (-ε * ‖x‖ ^ 2)) (nuLiftS src a meas) :=
    fun hε => nuLiftS_gauss src a meas hε
  have hρ_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace src.w => Real.exp (-ε * ‖x‖ ^ 2)) (rhoLiftS src a) :=
    fun hε => rhoLiftS_gauss src ha ha_pos hε
  have h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace src.w, radialLiftReal src.w (thermalDiff src.w β) x ∂(nuLiftS src a meas) =
        ∫ x : RadialSpace src.w, radialLiftReal src.w (thermalDiff src.w β) x ∂(rhoLiftS src a) := by
    intro β hβ
    rw [integral_nuLiftS src a meas (by unfold thermalDiff; fun_prop :
        Continuous (thermalDiff src.w β)).continuousOn,
      integral_rhoLiftS src ha, meas.crossing hβ]
  let b : ℝ := -q
  let d : ℝ := -(2 * Real.sqrt 2 * π * Real.sqrt a)
  have hw1 : (1 : ℝ) ≤ (src.w : ℝ) := by exact_mod_cast src.hw
  have hq_gt1 : 1 < q := by linarith
  have hW_cont : Continuous (euclideanWeight b d : RadialSpace src.w → ℝ) := by
    unfold euclideanWeight
    refine Continuous.mul (continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.rpow (continuousAt_const.add ((continuous_norm.pow 2).continuousAt))
        continuousAt_const (Or.inl (by positivity))) (by fun_prop)
  have hW_dom : ∀ x : RadialSpace src.w,
      |radialLiftReal src.w g x| ≤ (C_g * (2 : ℝ) ^ q) * euclideanWeight b d x := fun x => by
    let t : ℝ := ‖x‖ ^ 2 / 2
    have ht_nn : 0 ≤ t := by positivity
    have hdec := hdecay t ht_nn
    have hpow_le : (1 + t) ^ (-q) ≤ (2 : ℝ) ^ q * (1 + ‖x‖ ^ 2) ^ (-q) := by
      have h1 : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + t) := by dsimp [t]; linarith
      have h2 : (2 * (1 + t)) ^ (-q) ≤ (1 + ‖x‖ ^ 2) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
      rw [Real.mul_rpow two_pos.le (by positivity)] at h2
      calc (1 + t) ^ (-q) = (2 : ℝ) ^ q * ((2 : ℝ) ^ (-q) * (1 + t) ^ (-q)) := by
            rw [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul]
        _ ≤ (2 : ℝ) ^ q * (1 + ‖x‖ ^ 2) ^ (-q) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_pos_of_pos two_pos _).le
    have hexp_eq : -4 * π * Real.sqrt (a * t) = d * ‖x‖ := by
      dsimp [t, d]
      rw [show a * (‖x‖ ^ 2 / 2) = (a / 2) * ‖x‖ ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg x),
        Real.sqrt_div ha_pos.le]
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
      calc -4 * π * (Real.sqrt a / Real.sqrt 2 * ‖x‖)
          = -(2 * (Real.sqrt 2 * Real.sqrt 2) * π * (Real.sqrt a / Real.sqrt 2) * ‖x‖) := by
            rw [hsq2]; ring
        _ = -(2 * Real.sqrt 2 * π * Real.sqrt a) * ‖x‖ := by
            have hsq_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
            field_simp
    calc |radialLiftReal src.w g x| = |g t| := rfl
      _ ≤ C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t)) := hdec
      _ ≤ C_g * ((2 : ℝ) ^ q * (1 + ‖x‖ ^ 2) ^ (-q)) * Real.exp (d * ‖x‖) := by
          rw [hexp_eq]
          gcongr
      _ = (C_g * (2 : ℝ) ^ q) * euclideanWeight b d x := by
          unfold euclideanWeight; dsimp [b]; ring
  have hW_nu : Integrable (euclideanWeight b d) (nuLiftS src a meas) := by
    obtain ⟨C_N, hC_N_pos, hcount⟩ := crossing_counting_bound_src src ha ha_pos meas
    let M_s : ℝ := (2 : ℝ) ^ src.w * (2 : ℝ) ^ q * C_N * Real.exp (4 * π * Real.sqrt a)
    have hM_s_nn : 0 ≤ M_s :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_pos_of_pos two_pos q).le)
        hC_N_pos.le) (Real.exp_pos _).le
    let f_t : ℝ → ℝ := fun t => (1 + 2 * t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))
    have hf_t_eq : ∀ t : ℝ, 0 ≤ t →
        euclideanWeight b d (embedRadial src.w src.hw t) = f_t t := fun t ht => by
      unfold euclideanWeight f_t
      rw [norm_embedRadial_sq src.hw ht]
      dsimp [b, d]
      rw [show -4 * π * Real.sqrt (a * t) = -(2 * Real.sqrt 2 * π * Real.sqrt a) * Real.sqrt (2 * t) by
        rw [Real.sqrt_mul zero_le_two, Real.sqrt_mul ha_pos.le]
        have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
        calc -4 * π * (Real.sqrt a * Real.sqrt t)
            = -(2 * (Real.sqrt 2 * Real.sqrt 2) * π * Real.sqrt a * Real.sqrt t) := by rw [hsq2]; ring
          _ = -(2 * Real.sqrt 2 * π * Real.sqrt a) * (Real.sqrt 2 * Real.sqrt t) := by ring]
      congr 2
      unfold embedRadial
      rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_euclidean_single_zero src.w src.hw,
        mul_one]
    have hshell : ∀ n : ℕ,
        ∫⁻ t in Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal (f_t t) ∂meas.ν ≤
          ENNReal.ofReal (M_s * ((n : ℝ) + 1) ^ ((src.w : ℝ) - 2 * q)) := fun n => by
      have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have hpow_le : ∀ t ∈ Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2),
          (1 + 2 * t) ^ (-q) ≤ (2 : ℝ) ^ q * ((n : ℝ) + 1) ^ (-2 * q) := fun t ht => by
        have ht_nn : 0 ≤ t := le_trans (sq_nonneg _) ht.1
        have ht1 : ((n : ℝ) + 1) ^ 2 ≤ 2 * (1 + 2 * t) := by nlinarith [ht.1]
        have h1 : (2 * (1 + 2 * t)) ^ (-q) ≤ (((n : ℝ) + 1) ^ 2) ^ (-q) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) ht1 (by linarith)
        rw [Real.mul_rpow two_pos.le (by linarith : 0 ≤ 1 + 2 * t),
          ← Real.rpow_natCast ((n : ℝ) + 1) 2, ← Real.rpow_mul hn1_pos.le] at h1
        calc (1 + 2 * t) ^ (-q) = (2 : ℝ) ^ q * ((2 : ℝ) ^ (-q) * (1 + 2 * t) ^ (-q)) := by
              rw [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul]
          _ ≤ (2 : ℝ) ^ q * ((n : ℝ) + 1) ^ ((2 : ℝ) * (-q)) :=
              mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos two_pos _).le
          _ = (2 : ℝ) ^ q * ((n : ℝ) + 1) ^ (-2 * q) := by congr 2; ring
      have hexp_le : ∀ t ∈ Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2),
          Real.exp (-4 * π * Real.sqrt (a * t)) ≤ Real.exp (-4 * π * Real.sqrt a * (n : ℝ)) := fun t ht => by
        refine Real.exp_le_exp.mpr ?_
        have hsqrt : (n : ℝ) ≤ Real.sqrt t := by
          rw [← Real.sqrt_sq hn_nn]; exact Real.sqrt_le_sqrt ht.1
        rw [Real.sqrt_mul ha_pos.le]
        have hmul_s : Real.sqrt a * (n : ℝ) ≤ Real.sqrt a * Real.sqrt t :=
          mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg a)
        nlinarith [Real.pi_pos, hmul_s]
      let ub : ℝ := (2 : ℝ) ^ q * ((n : ℝ) + 1) ^ (-2 * q) * Real.exp (-4 * π * Real.sqrt a * (n : ℝ))
      have hub : ∀ t ∈ Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), f_t t ≤ ub := fun t ht =>
        mul_le_mul (hpow_le t ht) (hexp_le t ht) (Real.exp_pos _).le (by positivity)
      have hcount_n : meas.ν (Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2)) ≤
          ENNReal.ofReal (C_N * (2 : ℝ) ^ src.w * ((n : ℝ) + 1) ^ (src.w : ℝ) *
            Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1))) := by
        have h1 : meas.ν (Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2)) ≤
            meas.ν (Icc 0 (((n : ℝ) + 1) ^ 2)) := measure_mono fun t ht =>
          ⟨le_trans (sq_nonneg _) ht.1, ht.2.le⟩
        have hc := hcount (((n : ℝ) + 1) ^ 2) (sq_nonneg _)
        rw [Real.sqrt_sq hn1_pos.le] at hc
        have hc' : (meas.ν (Icc 0 (((n : ℝ) + 1) ^ 2))).toReal ≤
            C_N * (2 : ℝ) ^ src.w * ((n : ℝ) + 1) ^ (src.w : ℝ) *
              Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)) := by
          have h1n : (1 + ((n : ℝ) + 1)) ^ src.w ≤ (2 * ((n : ℝ) + 1)) ^ src.w :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
          have hexp_s : Real.sqrt (a * ((n : ℝ) + 1) ^ 2) = Real.sqrt a * ((n : ℝ) + 1) := by
            rw [Real.sqrt_mul ha_pos.le, Real.sqrt_sq hn1_pos.le]
          rw [hexp_s] at hc
          calc (meas.ν (Icc 0 (((n : ℝ) + 1) ^ 2))).toReal
              ≤ C_N * (1 + ((n : ℝ) + 1)) ^ src.w * Real.exp (4 * π * (Real.sqrt a * ((n : ℝ) + 1))) := hc
            _ ≤ C_N * (2 * ((n : ℝ) + 1)) ^ src.w * Real.exp (4 * π * (Real.sqrt a * ((n : ℝ) + 1))) := by gcongr
            _ = C_N * (2 : ℝ) ^ src.w * ((n : ℝ) + 1) ^ (src.w : ℝ) *
                  Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)) := by
                rw [mul_pow, Real.rpow_natCast]; ring_nf
        have hlt_top := admissibleMeasure_Ici_sub_lt_top_src src a meas (Subset.rfl :
          Icc 0 (((n : ℝ) + 1) ^ 2) ⊆ Icc 0 (((n : ℝ) + 1) ^ 2))
        exact h1.trans (ENNReal.le_ofReal_iff_toReal_le hlt_top.ne (by positivity) |>.mpr hc')
      calc ∫⁻ t in Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal (f_t t) ∂meas.ν
          ≤ ∫⁻ _ in Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal ub ∂meas.ν :=
            setLIntegral_mono' measurableSet_Ico fun t ht => ENNReal.ofReal_le_ofReal (hub t ht)
        _ = ENNReal.ofReal ub * meas.ν (Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2)) := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal ub * ENNReal.ofReal (C_N * (2 : ℝ) ^ src.w * ((n : ℝ) + 1) ^ (src.w : ℝ) *
              Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1))) := by gcongr
        _ = ENNReal.ofReal (ub * (C_N * (2 : ℝ) ^ src.w * ((n : ℝ) + 1) ^ (src.w : ℝ) *
              Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal (M_s * ((n : ℝ) + 1) ^ ((src.w : ℝ) - 2 * q)) := by
            congr 1
            have hexp_mul : Real.exp (-4 * π * Real.sqrt a * (n : ℝ)) *
                Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)) = Real.exp (4 * π * Real.sqrt a) := by
              rw [← Real.exp_add]; congr 1; ring
            have hpow_mul : ((n : ℝ) + 1) ^ (-2 * q) * ((n : ℝ) + 1) ^ (src.w : ℝ) =
                ((n : ℝ) + 1) ^ ((src.w : ℝ) - 2 * q) := by
              rw [← Real.rpow_add hn1_pos]; congr 1; ring
            calc ub * (C_N * (2 : ℝ) ^ src.w * ((n : ℝ) + 1) ^ (src.w : ℝ) *
                    Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)))
                = ((2 : ℝ) ^ src.w * (2 : ℝ) ^ q * C_N) *
                    (Real.exp (-4 * π * Real.sqrt a * (n : ℝ)) *
                      Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1))) *
                    (((n : ℝ) + 1) ^ (-2 * q) * ((n : ℝ) + 1) ^ (src.w : ℝ)) := by
                  dsimp [ub]; ring
              _ = M_s * ((n : ℝ) + 1) ^ ((src.w : ℝ) - 2 * q) := by
                  rw [hexp_mul, hpow_mul]
    have hcov : Ici (0 : ℝ) ⊆ ⋃ n : ℕ, Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2) := fun t ht => by
      let n : ℕ := Nat.floor (Real.sqrt t)
      have hn_le : (n : ℝ) ≤ Real.sqrt t := Nat.floor_le (Real.sqrt_nonneg t)
      have hlt_n1 : Real.sqrt t < (n : ℝ) + 1 := Nat.lt_floor_add_one _
      refine Set.mem_iUnion.mpr ⟨n, ?_, ?_⟩
      · have := pow_le_pow_left₀ (Nat.cast_nonneg n) hn_le 2
        rwa [Real.sq_sqrt (Set.mem_Ici.mp ht)] at this
      · have := pow_lt_pow_left₀ hlt_n1 (Real.sqrt_nonneg t) two_ne_zero
        rwa [Real.sq_sqrt (Set.mem_Ici.mp ht)] at this
    have hsum_fin : Summable (fun n : ℕ => M_s * ((n : ℝ) + 1) ^ ((src.w : ℝ) - 2 * q)) := by
      have hpow_sum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ ((src.w : ℝ) - 2 * q)) := by
        have heq_s : (fun n : ℕ => ((n : ℝ) + 1) ^ ((src.w : ℝ) - 2 * q)) =
            fun n => (((n + 1 : ℕ) : ℝ) ^ ((src.w : ℝ) - 2 * q)) := by
          ext n; push_cast; rfl
        rw [heq_s]
        refine (summable_nat_add_iff 1 (f := fun n : ℕ => (n : ℝ) ^ ((src.w : ℝ) - 2 * q))).mpr ?_
        exact Real.summable_nat_rpow.mpr (by linarith)
      exact hpow_sum.mul_left M_s
    unfold nuLiftS
    rw [integrable_map_measure hW_cont.aestronglyMeasurable (measurable_embedRadial src.w src.hw).aemeasurable]
    refine ⟨hW_cont.comp (continuous_embedRadial src.w src.hw) |>.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hcongr_e : (∫⁻ t in Ici 0, ‖(euclideanWeight b d ∘ embedRadial src.w src.hw) t‖ₑ ∂meas.ν) =
        ∫⁻ t in Ici 0, ENNReal.ofReal (f_t t) ∂meas.ν := by
      refine setLIntegral_congr_fun measurableSet_Ici (fun t ht => ?_)
      dsimp only [Function.comp_def]
      rw [Real.eNorm_of_nonneg (euclideanWeight_pos _ _ _).le, hf_t_eq t (Set.mem_Ici.mp ht)]
    rw [hcongr_e]
    calc ∫⁻ t in Ici 0, ENNReal.ofReal (f_t t) ∂meas.ν
        ≤ ∫⁻ t in ⋃ n : ℕ, Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal (f_t t) ∂meas.ν :=
          lintegral_mono_set hcov
      _ ≤ ∑' n : ℕ, ∫⁻ t in Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal (f_t t) ∂meas.ν :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (M_s * ((n : ℝ) + 1) ^ ((src.w : ℝ) - 2 * q)) :=
          tsum_le_tsum hshell
      _ < ⊤ := hsum_fin.tsum_ofReal_lt_top
  have hW_rho : Integrable (euclideanWeight b d) (rhoLiftS src a) := by
    unfold rhoLiftS
    have hmeas : Measurable (fun x : RadialSpace src.w =>
        ENNReal.ofReal (src.rhoDensity a (‖x‖ ^ 2 / 2))) :=
      (ENNReal.continuous_ofReal.comp ((src.continuous_rhoDensity a).comp
        ((continuous_norm.pow 2).div_const 2))).measurable
    rw [integrable_withDensity_iff_integrable_smul' hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    obtain ⟨C_hi, hC_hi_pos, hrho_hi⟩ := src.rhoDensity_le_cardyWeight ha ha_pos
    let b₀ : ℝ := -((src.w - 1 : ℝ) / 2 + 1 / 4)
    let r_exp : ℝ := -q + (src.w - 1 : ℝ) / 2 - 1 / 4
    have hr_lt : r_exp < -1 := by dsimp [r_exp]; linarith
    have hcont_12t : ∀ r : ℝ, ContinuousOn (fun t : ℝ => (1 + 2 * t) ^ r) (Ici 0) := fun r => by
      intro t ht
      have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
      exact ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).rpow
        continuousAt_const (Or.inl (by change 1 + 2 * t ≠ 0; linarith))).continuousWithinAt
    have hcont_cw : ContinuousOn (cardyWeight b d) (Ici 0) :=
      (hcont_12t b).mul (Real.continuous_exp.comp (continuous_const.mul
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)))).continuousOn
    have hint_t : IntegrableOn (fun t : ℝ => (1 + 2 * t) ^ r_exp) (Ioi (0 : ℝ)) := by
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
      refine IntegrableOn.union ?_ ?_
      · exact ((hcont_12t r_exp).mono (fun t (ht : t ∈ Icc (0 : ℝ) 1) => ht.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      · have h1 : IntegrableOn (fun t : ℝ => t ^ r_exp) (Ioi (1 : ℝ)) :=
          integrableOn_Ioi_rpow_of_lt hr_lt one_pos
        refine h1.mono' ((hcont_12t r_exp).mono (fun t ht =>
            le_trans zero_le_one (le_of_lt (Set.mem_Ioi.mp ht)))
            |>.aestronglyMeasurable measurableSet_Ioi) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : 1 < t := Set.mem_Ioi.mp ht
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (hr_lt.le.trans (by norm_num))
    have hrad_int : Integrable (radialLift src.w (fun t =>
        src.rhoDensity a t * cardyWeight b d t)) := by
      rw [integrable_radialLift_iff src.hw]
      refine (hint_t.const_mul C_hi).mono' ?_ ?_
      · refine (((continuous_id.pow (src.w - 1)).continuousOn.mul
            ((src.continuous_rhoDensity a).continuousOn.mul hcont_cw)).mono Ioi_subset_Ici_self
          |>.aestronglyMeasurable measurableSet_Ioi)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := Set.mem_Ioi.mp ht
        have h1 := hrho_hi t ht_pos.le
        have hexp_cancel : Real.exp (2 * Real.sqrt 2 * π * Real.sqrt a * Real.sqrt (2 * t)) *
            Real.exp (d * Real.sqrt (2 * t)) = 1 := by
          rw [← Real.exp_add, show 2 * Real.sqrt 2 * π * Real.sqrt a * Real.sqrt (2 * t) +
            d * Real.sqrt (2 * t) = 0 by dsimp [d]; ring, Real.exp_zero]
        have ht_le_pow : t ^ (src.w - 1) ≤ (1 + 2 * t) ^ ((src.w : ℝ) - 1) := by
          rw [← Real.rpow_natCast t (src.w - 1), Nat.cast_sub src.hw, Nat.cast_one]
          exact Real.rpow_le_rpow ht_pos.le (by linarith) (by linarith)
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht_pos.le _)
          (mul_nonneg (src.rhoDensity_nonneg ha ht_pos.le) (cardyWeight_pos b d ht_pos.le).le))]
        calc t ^ (src.w - 1) * (src.rhoDensity a t * cardyWeight b d t)
            ≤ (1 + 2 * t) ^ ((src.w : ℝ) - 1) *
                (C_hi * cardyWeight b₀ (2 * Real.sqrt 2 * π * Real.sqrt a) t * cardyWeight b d t) :=
              mul_le_mul ht_le_pow (mul_le_mul_of_nonneg_right h1 (cardyWeight_pos b d ht_pos.le).le)
                (mul_nonneg (src.rhoDensity_nonneg ha ht_pos.le) (cardyWeight_pos b d ht_pos.le).le)
                (by positivity)
          _ = C_hi * ((1 + 2 * t) ^ ((src.w : ℝ) - 1) * ((1 + 2 * t) ^ b₀ * (1 + 2 * t) ^ b) *
                (Real.exp (2 * Real.sqrt 2 * π * Real.sqrt a * Real.sqrt (2 * t)) *
                  Real.exp (d * Real.sqrt (2 * t)))) := by
              unfold cardyWeight; ring
          _ = C_hi * (1 + 2 * t) ^ r_exp := by
              rw [hexp_cancel, mul_one, ← Real.rpow_add (by linarith : 0 < 1 + 2 * t),
                ← Real.rpow_add (by linarith : 0 < 1 + 2 * t)]
              congr 2; dsimp [r_exp, b₀, b]; ring
    refine ((integrable_radialLift_iff_real src.w _).mp hrad_int).congr
      (Eventually.of_forall fun x => ?_)
    dsimp only [radialLiftReal]
    rw [ENNReal.toReal_ofReal (src.rhoDensity_nonneg ha (by positivity)), smul_eq_mul,
      ← euclideanWeight_eq_cardyWeight b d x]
  obtain ⟨hint_nu, _, heq⟩ := lemma_fwA_part3_unconditional (nuLiftS src a meas) (rhoLiftS src a)
    hν_gauss hρ_gauss h_thermal hg.cont hg.int_lift hg.fourier_odd (C := C_g * (2 : ℝ) ^ q)
    (b := b) (d := d) (by positivity) hW_dom hW_nu hW_rho
  rw [integrable_nuLiftS_iff src a meas hg.cont] at hint_nu
  rw [integral_nuLiftS src a meas hg.cont, integral_rhoLiftS_eq_neg_gVac src ha g] at heq
  exact ⟨hint_nu, by linarith⟩
/-- info: 'FormalResearch.ModularBootstrap.Mixtures.lemma_fwX_one_sided_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_fwX_one_sided_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.lemma_fwX_equality_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_fwX_equality_src

end FormalResearch.ModularBootstrap.Mixtures
