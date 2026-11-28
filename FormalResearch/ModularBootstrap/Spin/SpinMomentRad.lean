module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentVolterra

/-!
# SPIN-M part 2a: Radial lifts, Cardy domination, and Volterra Fubini

Measure-theoretic infrastructure for `SpinMomentPair.lean`, kept in its own leaf module
so every module stays concise and focused:

* `radialOfReal`, `integrable_radialOfReal_iff`, `integral_radialOfReal`: embedding `[0, ∞)`
  measures into `RadialSpace 5` with `t = ‖x‖^2 / 2`.
* `rad_counting_bound`, `rad_Icc_lt_top`, `spinMomentMeasure_Icc_lt_top`: polynomial
  counting bounds and local finiteness on `[0, ∞)`.
* `spinMoment_fubini_on_Ici`: Tonelli/Fubini exchange for `(K φ, ν₀) = (φ, K^* ν₀)` on `[0, ∞)`.
* `integrable_cardyWeight_spinMomentMeasure`: integrability of `(1 + 2t)^{-6} exp(-4π √(at))`
  against the spin-moment measure `M`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal Nat

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing

noncomputable def radialOfReal (μ : Measure ℝ) : Measure (RadialSpace 5) :=
  (μ.restrict (Ici 0)).map (embedRadial 5 (by norm_num))

lemma sigmaFinite_of_Iio_null_Icc_lt_top {ν₀ : Measure ℝ}
    (hν₀_supp : ν₀ (Iio 0) = 0) (hν₀_fin : ∀ R : ℝ, ν₀ (Icc 0 R) < ⊤) :
    SigmaFinite ν₀ := by
  refine ⟨⟨{
    set := fun n => Iio 0 ∪ Icc 0 (n : ℝ)
    set_mem := fun _ => Set.mem_univ _
    finite := fun n => (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2
      ⟨by rw [hν₀_supp]; exact ENNReal.zero_lt_top, hν₀_fin n⟩)
    spanning := by
      ext x; simp only [mem_iUnion, mem_union, mem_Iio, mem_Icc, mem_univ, iff_true]
      rcases lt_or_ge x 0 with hx | hx
      · exact ⟨0, Or.inl hx⟩
      · obtain ⟨n, hn⟩ := exists_nat_ge x
        exact ⟨n, Or.inr ⟨hx, hn⟩⟩ }⟩⟩

lemma isLocallyFinite_radialOfReal {μ : Measure ℝ}
    (hfin : ∀ R : ℝ, μ (Icc 0 R) < ⊤) : IsLocallyFiniteMeasure (radialOfReal μ) := by
  refine ⟨fun x => ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩⟩
  unfold radialOfReal
  have hm := measurable_embedRadial 5 (by norm_num)
  rw [Measure.map_apply hm measurableSet_ball]
  let R : ℝ := (‖x‖ + 1) ^ 2 / 2
  have hsub : (embedRadial 5 (by norm_num) ⁻¹' Metric.ball x 1) ∩ Ici 0 ⊆ Icc 0 R := by
    rintro t ⟨htb, ht0⟩
    refine ⟨ht0, ?_⟩
    have hnorm_lt : ‖embedRadial 5 (by norm_num) t‖ < ‖x‖ + 1 := by
      calc ‖embedRadial 5 (by norm_num) t‖
          = ‖(embedRadial 5 (by norm_num) t - x) + x‖ := by congr 1; abel
        _ ≤ ‖embedRadial 5 (by norm_num) t - x‖ + ‖x‖ := norm_add_le _ _
        _ < 1 + ‖x‖ := by linarith [Metric.mem_ball.1 htb, dist_eq_norm (embedRadial 5 (by norm_num) t) x]
        _ = ‖x‖ + 1 := add_comm _ _
    have hsq : 2 * t ≤ (‖x‖ + 1) ^ 2 := by
      rw [← norm_embedRadial_sq (by norm_num : 1 ≤ 5) ht0]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm_lt.le 2
    dsimp [R]; linarith
  calc (μ.restrict (Ici 0)) (embedRadial 5 (by norm_num) ⁻¹' Metric.ball x 1)
      = μ ((embedRadial 5 (by norm_num) ⁻¹' Metric.ball x 1) ∩ Ici 0) := by
        rw [Measure.restrict_apply (measurableSet_ball.preimage hm)]
    _ ≤ μ (Icc 0 R) := measure_mono hsub
    _ < ⊤ := hfin R

lemma integrable_radialOfReal_iff {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable (radialLiftReal 5 f) (radialOfReal μ) ↔ IntegrableOn f (Ici 0) μ := by
  unfold radialOfReal
  have hm := measurable_embedRadial 5 (by norm_num)
  have hmeas : Measurable (radialLiftReal 5 f) := by
    unfold radialLiftReal; exact hf.comp ((continuous_norm.pow 2).div_const 2).measurable
  rw [integrable_map_measure hmeas.aestronglyMeasurable hm.aemeasurable]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact h.congr (ae_restrict_of_forall_mem measurableSet_Ici fun t ht =>
      radialLiftReal_embedRadial (by norm_num : 1 ≤ 5) f ht)
  · exact h.congr (ae_restrict_of_forall_mem measurableSet_Ici fun t ht =>
      (radialLiftReal_embedRadial (by norm_num : 1 ≤ 5) f ht).symm)

lemma integral_radialOfReal {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x : RadialSpace 5, radialLiftReal 5 f x ∂(radialOfReal μ) = ∫ t in Ici 0, f t ∂μ := by
  unfold radialOfReal
  have hm := measurable_embedRadial 5 (by norm_num)
  have hmeas : Measurable (radialLiftReal 5 f) := by
    unfold radialLiftReal; exact hf.comp ((continuous_norm.pow 2).div_const 2).measurable
  rw [integral_map hm.aemeasurable hmeas.aestronglyMeasurable]
  refine setIntegral_congr_fun measurableSet_Ici fun t ht =>
    radialLiftReal_embedRadial (by norm_num : 1 ≤ 5) f ht

lemma rad_counting_bound {a B τ : ℝ} (ha : 2 ≤ a) (hτ : 0 < τ)
    {X : Set (ℝ × ℝ)} (hX : X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2})
    (meas : SpinCrossingMeasureOn a X) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R →
      (spinRadMarginal meas.ν (Icc 0 R)).toReal ≤
        C * (1 + Real.sqrt R) * Real.exp (4 * π * Real.sqrt (a * R)) := by
  let hrad := meas.toRadAdmissible (hX.trans fun _ hp => hτ.le.trans hp.2)
  have ha_shift : virasoroProblem.totalShift ≤ a := by rw [virasoroProblem_totalShift]; exact ha
  obtain ⟨C, hC, hbd⟩ := crossing_counting_bound virasoroProblem ha_shift (by linarith) hrad
  refine ⟨C, hC, fun R hR => ?_⟩
  have h1 := hbd R hR
  dsimp [hrad, SpinCrossingMeasureOn.toRadAdmissible] at h1
  rw [pow_one] at h1
  exact h1

lemma rad_Icc_lt_top {a B τ : ℝ} (hτ : 0 < τ)
    {X : Set (ℝ × ℝ)} (hX : X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2})
    (meas : SpinCrossingMeasureOn a X) (R : ℝ) :
    spinRadMarginal meas.ν (Icc 0 R) < ⊤ := by
  let hrad := meas.toRadAdmissible (hX.trans fun _ hp => hτ.le.trans hp.2)
  have hInt : Integrable (fun t : ℝ => (Icc 0 R).indicator (fun _ => (1 : ℝ)) t) (spinRadMarginal meas.ν) := by
    have hlap : IntegrableOn (fun t : ℝ => Real.exp (-2 * π * 1 * t)) (Ici 0) (spinRadMarginal meas.ν) :=
      hrad.finite_laplace one_pos
    have hfull : Integrable (fun t : ℝ => Real.exp (-2 * π * 1 * t)) (spinRadMarginal meas.ν) := by
      have hr : (spinRadMarginal meas.ν).restrict (Ici 0) = spinRadMarginal meas.ν := by
        refine Measure.restrict_eq_self_of_ae_mem ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hrad.supp_nonneg] with t ht using not_lt.1 ht
      rwa [IntegrableOn, hr] at hlap
    refine (hfull.const_mul (Real.exp (2 * π * max R 0))).mono'
      (Measurable.indicator measurable_const measurableSet_Icc).aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
    dsimp [Set.indicator]
    split_ifs with ht
    · calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (2 * π * max R 0 + -2 * π * 1 * t) :=
            Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht.2, le_max_left R 0])
        _ = _ := Real.exp_add _ _
    · positivity
  have h1 := ((integrable_indicator_iff measurableSet_Icc).1 hInt).2
  rw [HasFiniteIntegral, setLIntegral_const, eNorm_one, one_mul] at h1
  exact h1

lemma spinMomentMeasure_Icc_lt_top {a B τ : ℝ}
    {X : Set (ℝ × ℝ)} (hX : X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2})
    (meas : SpinCrossingMeasureOn a X) (R : ℝ) :
    spinMomentMeasure meas.ν (Icc 0 R) < ⊤ := by
  have hcone : X ⊆ spinConeB B := hX.trans inter_subset_left
  have hInt : Integrable (fun t : ℝ => (Icc 0 R).indicator (fun _ => (1 : ℝ)) t) (spinMomentMeasure meas.ν) := by
    refine ((spinMomentMeasure_finite_laplace hcone meas one_pos).const_mul (Real.exp (2 * π * max R 0))).mono'
      (Measurable.indicator measurable_const measurableSet_Icc).aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
    dsimp [Set.indicator]
    split_ifs with ht
    · calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (2 * π * max R 0 + -2 * π * 1 * t) :=
            Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht.2, le_max_left R 0])
        _ = _ := Real.exp_add _ _
    · positivity
  have h1 := ((integrable_indicator_iff measurableSet_Icc).1 hInt).2
  rw [HasFiniteIntegral, setLIntegral_const, eNorm_one, one_mul] at h1
  exact h1

lemma measurable_cardyWeight_wbd (d : ℝ) : Measurable (cardyWeight (-6) d) := by
  unfold cardyWeight
  exact ((measurable_const.add (measurable_const.mul measurable_id)).pow_const _).mul
    (Real.measurable_exp.comp (measurable_const.mul
      ((Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).measurable)))

lemma continuousOn_cardyWeight_wbd (d : ℝ) : ContinuousOn (cardyWeight (-6) d) (Ici 0) := by
  unfold cardyWeight
  refine ((continuous_const.add (continuous_const.mul continuous_id)).continuousOn.rpow_const ?_).mul
    (Real.continuous_exp.comp (continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_const.mul continuous_id)))).continuousOn
  intro t ht; left; dsimp; linarith [mem_Ici.1 ht]

lemma cardyWeight_wbd_nonneg (d t : ℝ) (ht : 0 ≤ t) : 0 ≤ cardyWeight (-6) d t := by
  unfold cardyWeight
  exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le

lemma rpow_cardy_mul_le_neg_two {t : ℝ} (ht : 0 ≤ t) :
    t * (1 + Real.sqrt t) * (1 + 2 * t) ^ (-6 : ℝ) ≤ 2 * (1 + t) ^ (-2 : ℝ) := by
  have h1 : Real.sqrt t ≤ 1 + t := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ 1 + t)]; exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : t * (1 + Real.sqrt t) ≤ 2 * (1 + 2 * t) ^ (2 : ℝ) := by
    rw [show (1 + 2 * t) ^ (2 : ℝ) = (1 + 2 * t) ^ (2 : ℕ) from Real.rpow_natCast _ 2]
    nlinarith [show 1 + Real.sqrt t ≤ 2 * (1 + 2 * t) by linarith, show t ≤ 1 + 2 * t by linarith]
  have h3 : (1 + 2 * t) ^ (2 : ℝ) * (1 + 2 * t) ^ (-6 : ℝ) ≤ (1 + t) ^ (-2 : ℝ) := by
    rw [← Real.rpow_add (by positivity : 0 < 1 + 2 * t)]
    exact (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + t) (by linarith) (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  calc t * (1 + Real.sqrt t) * (1 + 2 * t) ^ (-6 : ℝ)
      ≤ (2 * (1 + 2 * t) ^ (2 : ℝ)) * (1 + 2 * t) ^ (-6 : ℝ) := by gcongr
    _ = 2 * ((1 + 2 * t) ^ (2 : ℝ) * (1 + 2 * t) ^ (-6 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by norm_num)

lemma spinMoment_fubini_on_Ici {ν₀ : Measure ℝ} (hν₀_supp : ν₀ (Iio 0) = 0)
    (hν₀_fin : ∀ R : ℝ, ν₀ (Icc 0 R) < ⊤)
    {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_int : IntegrableOn (fun t : ℝ => t * |f t| * (ν₀ (Icc 0 t)).toReal) (Ici 0)) :
    IntegrableOn (fun t => spinVolterraDens ν₀ t * f t) (Ici 0) ∧
    IntegrableOn (fun r => ∫ t in Ici r, (3 * r - t) / 2 * f t) (Ici 0) ν₀ ∧
    ∫ t in Ici 0, spinVolterraDens ν₀ t * f t =
      ∫ r in Ici 0, (∫ t in Ici r, (3 * r - t) / 2 * f t) ∂ν₀ := by
  have : SigmaFinite ν₀ := sigmaFinite_of_Iio_null_Icc_lt_top hν₀_supp hν₀_fin
  let F : ℝ × ℝ → ℝ := fun p => if p.2 ≤ p.1 then (3 * p.2 - p.1) / 2 * f p.1 else 0
  have hF_meas : Measurable F :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      ((((measurable_snd.const_mul 3).sub measurable_fst).div_const 2).mul (hf_meas.comp measurable_fst))
      measurable_const
  have hF_prod_int : Integrable F ((volume.restrict (Ici 0)).prod (ν₀.restrict (Ici 0))) := by
    refine ⟨hF_meas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hF_meas.eNorm.aemeasurable]
    have hbd_in : ∀ t ∈ Ici (0 : ℝ),
        ∫⁻ r in Ici 0, ‖F (t, r)‖ₑ ∂ν₀ ≤ ENNReal.ofReal (t * |f t| * (ν₀ (Icc 0 t)).toReal) := by
      intro t ht
      have ht0 : 0 ≤ t := mem_Ici.1 ht
      have hsub : ∀ r ∈ Ici (0 : ℝ),
          ‖F (t, r)‖ₑ ≤ (Iic t).indicator (fun _ => ENNReal.ofReal (t * |f t|)) r := by
        intro r hr
        dsimp [F]
        by_cases hrt : r ≤ t
        · simp only [if_pos hrt, Set.indicator_of_mem (mem_Iic.2 hrt)]
          rw [← ofReal_norm, Real.norm_eq_abs, abs_mul,
            ENNReal.ofReal_le_ofReal_iff (mul_nonneg ht0 (abs_nonneg _))]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [abs_le]; constructor <;> linarith [(mem_Ici.1 hr), hrt]
        · simp [hrt, eNorm_zero]
      calc ∫⁻ r in Ici 0, ‖F (t, r)‖ₑ ∂ν₀
          ≤ ∫⁻ r in Ici 0, (Iic t).indicator (fun _ => ENNReal.ofReal (t * |f t|)) r ∂ν₀ :=
            setLIntegral_mono' measurableSet_Ici hsub
        _ = ENNReal.ofReal (t * |f t|) * (ν₀.restrict (Ici 0)) (Iic t) := by
            rw [lintegral_indicator measurableSet_Iic, lintegral_const, Measure.restrict_apply_univ]
        _ = ENNReal.ofReal (t * |f t|) * ν₀ (Icc 0 t) := by
            congr 1; rw [Measure.restrict_apply measurableSet_Iic, inter_comm]; rfl
        _ = ENNReal.ofReal (t * |f t| * (ν₀ (Icc 0 t)).toReal) := by
            rw [ENNReal.ofReal_mul (mul_nonneg ht0 (abs_nonneg _)),
              ENNReal.ofReal_toReal (hν₀_fin t).ne]
    calc ∫⁻ t, ∫⁻ r, ‖F (t, r)‖ₑ ∂(ν₀.restrict (Ici 0)) ∂(volume.restrict (Ici 0))
        ≤ ∫⁻ t in Ici 0, ENNReal.ofReal (t * |f t| * (ν₀ (Icc 0 t)).toReal) ∂volume :=
          setLIntegral_mono' measurableSet_Ici hbd_in
      _ = ∫⁻ t in Ici 0, ‖t * |f t| * (ν₀ (Icc 0 t)).toReal‖ₑ ∂volume := by
          refine setLIntegral_congr_fun measurableSet_Ici fun t ht => ?_
          have ht0 : 0 ≤ t := mem_Ici.1 ht
          rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
      _ < ⊤ := hf_int.2
  have hF_curry : Integrable (Function.uncurry (Function.curry F)) ((volume.restrict (Ici 0)).prod (ν₀.restrict (Ici 0))) :=
    hF_prod_int
  have hL_int : Integrable (fun t => ∫ r in Ici 0, F (t, r) ∂ν₀) (volume.restrict (Ici 0)) :=
    hF_curry.integral_prod_left
  have hR_int : Integrable (fun r => ∫ t in Ici 0, F (t, r) ∂volume) (ν₀.restrict (Ici 0)) :=
    hF_curry.integral_prod_right
  have hswap := MeasureTheory.integral_integral_swap hF_curry
  have hL_eq : ∀ t ∈ Ici (0 : ℝ), (∫ r in Ici 0, F (t, r) ∂ν₀) = spinVolterraDens ν₀ t * f t := by
    intro t _ht
    have hIic : ν₀.restrict (Ici 0) = ν₀ := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν₀_supp] with r hr using not_lt.1 hr
    rw [hIic]
    have hF_eq : (fun r => F (t, r)) = (Iic t).indicator (fun r => (3 * r - t) / 2 * f t) := by
      ext r; simp [F, Set.indicator]
    rw [hF_eq, integral_indicator measurableSet_Iic, show (fun r => (3 * r - t) / 2 * f t) =
      fun r => ((3 * r - t) / 2) * f t from rfl, integral_mul_const]
    rfl
  have hR_eq : ∀ r ∈ Ici (0 : ℝ),
      (∫ t in Ici 0, F (t, r) ∂volume) = ∫ t in Ici r, (3 * r - t) / 2 * f t := by
    intro r hr
    have hF_eq : (fun t => F (t, r)) = (Ici r).indicator (fun t => (3 * r - t) / 2 * f t) := by
      ext t; simp [F, Set.indicator]
    rw [hF_eq, setIntegral_indicator measurableSet_Ici, Ici_inter_Ici, max_eq_right (mem_Ici.1 hr)]
  refine ⟨IntegrableOn.congr_fun hL_int hL_eq measurableSet_Ici,
    IntegrableOn.congr_fun hR_int hR_eq measurableSet_Ici, ?_⟩
  calc ∫ t in Ici 0, spinVolterraDens ν₀ t * f t
      = ∫ t in Ici 0, (∫ r in Ici 0, F (t, r) ∂ν₀) :=
        setIntegral_congr_fun measurableSet_Ici fun t ht => (hL_eq t ht).symm
    _ = ∫ r in Ici 0, (∫ t in Ici 0, F (t, r) ∂volume) ∂ν₀ := hswap
    _ = ∫ r in Ici 0, (∫ t in Ici r, (3 * r - t) / 2 * f t) ∂ν₀ :=
        setIntegral_congr_fun measurableSet_Ici hR_eq

lemma integrable_cardyWeight_spinMomentMeasure {a B τ : ℝ} (ha : 2 ≤ a) (hB : 0 ≤ B) (hτ : 0 < τ)
    {X : Set (ℝ × ℝ)} (hX : X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2})
    (meas : SpinCrossingMeasureOn a X) :
    IntegrableOn (cardyWeight (-6) (-2 * Real.sqrt 2 * π * Real.sqrt a)) (Ici 0) (spinMomentMeasure meas.ν) := by
  obtain ⟨C_N, hCN, hcount⟩ := rad_counting_bound ha hτ hX meas
  let d₀ : ℝ := -2 * Real.sqrt 2 * π * Real.sqrt a
  let wBd : ℝ → ℝ := cardyWeight (-6) d₀
  refine ⟨(measurable_cardyWeight_wbd d₀).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hIci_union : Ici (0 : ℝ) = ⋃ k : ℕ, Ico (k : ℝ) ((k : ℝ) + 1) := by
    ext t; simp only [mem_Ici, mem_iUnion, mem_Ico]; constructor
    · intro ht; exact ⟨Nat.floor t, Nat.floor_le ht, Nat.lt_floor_add_one t⟩
    · rintro ⟨k, hk1, _⟩; exact le_trans (Nat.cast_nonneg k) hk1
  have hle_sum : ∫⁻ t in Ici 0, ‖wBd t‖ₑ ∂(spinMomentMeasure meas.ν) ≤
      ∑' k : ℕ, ∫⁻ t in Ico (k : ℝ) ((k : ℝ) + 1), ‖wBd t‖ₑ ∂(spinMomentMeasure meas.ν) := by
    rw [hIci_union]; exact MeasureTheory.lintegral_iUnion_le _ _
  have hshell : ∀ k : ℕ,
      ∫⁻ t in Ico (k : ℝ) ((k : ℝ) + 1), ‖wBd t‖ₑ ∂(spinMomentMeasure meas.ν) ≤
        ENNReal.ofReal ((C_N * (2 * B + 2) ^ 2 * 2 * Real.exp (4 * π * Real.sqrt a)) * ((k : ℝ) + 1) ^ (-2 : ℝ)) := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hsub : ∀ t ∈ Ico (k : ℝ) ((k : ℝ) + 1),
        wBd t ≤ (1 + 2 * (k : ℝ)) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * (k : ℝ))) := by
      intro t ht
      have ht0 : 0 ≤ t := hk0.trans ht.1
      rw [show wBd t = cardyWeight (-6) d₀ t from rfl, cardyWeight_wbd_eq (by linarith) ht0]
      have hexp_le : Real.exp (-4 * π * Real.sqrt (a * t)) ≤ Real.exp (-4 * π * Real.sqrt (a * (k : ℝ))) := by
        refine Real.exp_le_exp.mpr ?_
        have hsq : Real.sqrt (a * (k : ℝ)) ≤ Real.sqrt (a * t) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ht.1 (by linarith))
        nlinarith [Real.pi_pos]
      refine mul_le_mul ?_ hexp_le (Real.exp_pos _).le (by positivity)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [ht.1]) (by norm_num)
    have hM_le : (spinMomentMeasure meas.ν (Ico (k : ℝ) ((k : ℝ) + 1))) ≤
        ENNReal.ofReal (((k : ℝ) + 1 + 2 * B) ^ 2 * (spinRadMarginal meas.ν (Icc 0 ((k : ℝ) + 1))).toReal) := by
      rw [spinMomentMeasure_apply_set measurableSet_Ico]
      have hae : ∀ᵐ p ∂meas.ν, p ∈ spinConeB B := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 meas.supp] with p hp
        by_contra hpB; exact hp (fun hpX => hpB (hX hpX).1)
      have hadd_m : Measurable fun p : ℝ × ℝ => p.1 + p.2 := measurable_fst.add measurable_snd
      have hrad : spinRadMarginal meas.ν (Icc 0 ((k : ℝ) + 1)) =
          meas.ν ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Icc 0 ((k : ℝ) + 1)) := by
        unfold spinRadMarginal; rw [Measure.map_apply hadd_m measurableSet_Icc]
      have hpre_sub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Ico (k : ℝ) ((k : ℝ) + 1) ⊆
          (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Icc 0 ((k : ℝ) + 1) :=
        Set.preimage_mono (fun t ht => ⟨hk0.trans ht.1, ht.2.le⟩)
      have hfin_rad : spinRadMarginal meas.ν (Icc 0 ((k : ℝ) + 1)) ≠ ⊤ :=
        (rad_Icc_lt_top hτ hX meas ((k : ℝ) + 1)).ne
      calc ∫⁻ p in (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Ico (k : ℝ) ((k : ℝ) + 1),
              ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂meas.ν
          ≤ ∫⁻ _ in (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Ico (k : ℝ) ((k : ℝ) + 1),
              ENNReal.ofReal (((k : ℝ) + 1 + 2 * B) ^ 2) ∂meas.ν := by
            refine setLIntegral_mono_ae aemeasurable_const ?_
            filter_upwards [hae] with p hp hp_mem
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 := spin_diff_sq_le_of_mem_spinConeB hp
            have h2 : p.1 + p.2 + 2 * B ≤ (k : ℝ) + 1 + 2 * B := by linarith [hp_mem.2]
            have h0 : 0 ≤ p.1 + p.2 + 2 * B := by linarith [hp.1, hp.2]
            exact h1.trans (pow_le_pow_left₀ h0 h2 2)
        _ = ENNReal.ofReal (((k : ℝ) + 1 + 2 * B) ^ 2) *
              meas.ν ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Ico (k : ℝ) ((k : ℝ) + 1)) := by
            rw [setLIntegral_const]
        _ ≤ ENNReal.ofReal (((k : ℝ) + 1 + 2 * B) ^ 2) *
              spinRadMarginal meas.ν (Icc 0 ((k : ℝ) + 1)) := by
            rw [hrad]; exact mul_le_mul_of_nonneg_left (measure_mono hpre_sub) (by positivity)
        _ = ENNReal.ofReal (((k : ℝ) + 1 + 2 * B) ^ 2 * (spinRadMarginal meas.ν (Icc 0 ((k : ℝ) + 1))).toReal) := by
            rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_toReal hfin_rad]
    have hshell_1 : ∫⁻ t in Ico (k : ℝ) ((k : ℝ) + 1), ‖wBd t‖ₑ ∂(spinMomentMeasure meas.ν) ≤
        ENNReal.ofReal ((1 + 2 * (k : ℝ)) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * (k : ℝ)))) *
          spinMomentMeasure meas.ν (Ico (k : ℝ) ((k : ℝ) + 1)) := by
      calc ∫⁻ t in Ico (k : ℝ) ((k : ℝ) + 1), ‖wBd t‖ₑ ∂(spinMomentMeasure meas.ν)
          ≤ ∫⁻ _ in Ico (k : ℝ) ((k : ℝ) + 1),
              ENNReal.ofReal ((1 + 2 * (k : ℝ)) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * (k : ℝ))))
              ∂(spinMomentMeasure meas.ν) := by
            refine setLIntegral_mono' measurableSet_Ico fun t ht => ?_
            have hw_nn : 0 ≤ wBd t := cardyWeight_wbd_nonneg d₀ t (hk0.trans ht.1)
            rw [← ofReal_norm, Real.norm_of_nonneg hw_nn]
            exact ENNReal.ofReal_le_ofReal (hsub t ht)
        _ = _ := setLIntegral_const _ _
    have hsqrt_diff : Real.sqrt (a * ((k : ℝ) + 1)) - Real.sqrt (a * (k : ℝ)) ≤ Real.sqrt a := by
      have ha0 : 0 ≤ a := by linarith
      rw [Real.sqrt_mul ha0, Real.sqrt_mul ha0, ← mul_sub]
      refine mul_le_of_le_one_right (Real.sqrt_nonneg _) ?_
      have h1 : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt (k : ℝ) + 1 := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt (k : ℝ) + 1)]
        refine Real.sqrt_le_sqrt ?_
        have hk' : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0
        nlinarith [Real.sqrt_nonneg (k : ℝ)]
      linarith
    have halg : ((1 + 2 * (k : ℝ)) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * (k : ℝ)))) *
        (((k : ℝ) + 1 + 2 * B) ^ 2 * (C_N * (1 + Real.sqrt ((k : ℝ) + 1)) * Real.exp (4 * π * Real.sqrt (a * ((k : ℝ) + 1))))) ≤
        (C_N * (2 * B + 2) ^ 2 * 2 * Real.exp (4 * π * Real.sqrt a)) * ((k : ℝ) + 1) ^ (-2 : ℝ) := by
      have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk1_ge : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
      have hexp_le : Real.exp (-4 * π * Real.sqrt (a * (k : ℝ))) * Real.exp (4 * π * Real.sqrt (a * ((k : ℝ) + 1))) ≤
          Real.exp (4 * π * Real.sqrt a) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hsqrt_diff (by positivity : 0 ≤ 4 * π)])
      have hpow_le : (1 + 2 * (k : ℝ)) ^ (-6 : ℝ) ≤ ((k : ℝ) + 1) ^ (-6 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hk1_pos (by linarith) (by norm_num)
      have hsq_le : ((k : ℝ) + 1 + 2 * B) ^ 2 ≤ (2 * B + 2) ^ 2 * ((k : ℝ) + 1) ^ (2 : ℝ) := by
        have h1 : (k : ℝ) + 1 + 2 * B ≤ (2 * B + 2) * ((k : ℝ) + 1) := by nlinarith
        rw [show ((k : ℝ) + 1) ^ (2 : ℝ) = ((k : ℝ) + 1) ^ (2 : ℕ) from Real.rpow_natCast _ 2]
        calc ((k : ℝ) + 1 + 2 * B) ^ 2 ≤ ((2 * B + 2) * ((k : ℝ) + 1)) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h1 2
          _ = _ := by ring
      have hsq1_le : 1 + Real.sqrt ((k : ℝ) + 1) ≤ 2 * ((k : ℝ) + 1) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        have hs : Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
          calc Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt (((k : ℝ) + 1) ^ 2) :=
                Real.sqrt_le_sqrt (by nlinarith)
            _ = (k : ℝ) + 1 := Real.sqrt_sq hk1_pos.le
        linarith
      have hrp_id : ((k : ℝ) + 1) ^ (-6 : ℝ) * (((k : ℝ) + 1) ^ (2 : ℝ) * ((k : ℝ) + 1) ^ (1 : ℝ)) ≤
          ((k : ℝ) + 1) ^ (-2 : ℝ) := by
        rw [← Real.rpow_add hk1_pos, ← Real.rpow_add hk1_pos]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      calc ((1 + 2 * (k : ℝ)) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * (k : ℝ)))) *
            (((k : ℝ) + 1 + 2 * B) ^ 2 * (C_N * (1 + Real.sqrt ((k : ℝ) + 1)) *
              Real.exp (4 * π * Real.sqrt (a * ((k : ℝ) + 1)))))
          = C_N * ((1 + 2 * (k : ℝ)) ^ (-6 : ℝ) * ((k : ℝ) + 1 + 2 * B) ^ 2 * (1 + Real.sqrt ((k : ℝ) + 1))) *
              (Real.exp (-4 * π * Real.sqrt (a * (k : ℝ))) * Real.exp (4 * π * Real.sqrt (a * ((k : ℝ) + 1)))) := by ring
        _ ≤ C_N * (((k : ℝ) + 1) ^ (-6 : ℝ) * ((2 * B + 2) ^ 2 * ((k : ℝ) + 1) ^ (2 : ℝ)) * (2 * ((k : ℝ) + 1) ^ (1 : ℝ))) *
              Real.exp (4 * π * Real.sqrt a) := by
            gcongr
        _ = (C_N * (2 * B + 2) ^ 2 * 2 * Real.exp (4 * π * Real.sqrt a)) *
              (((k : ℝ) + 1) ^ (-6 : ℝ) * (((k : ℝ) + 1) ^ (2 : ℝ) * ((k : ℝ) + 1) ^ (1 : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hrp_id (by positivity)
    refine hshell_1.trans ?_
    refine (mul_le_mul_of_nonneg_left hM_le (by positivity)).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc _ ≤ ((1 + 2 * (k : ℝ)) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * (k : ℝ)))) *
            (((k : ℝ) + 1 + 2 * B) ^ 2 * (C_N * (1 + Real.sqrt ((k : ℝ) + 1)) * Real.exp (4 * π * Real.sqrt (a * ((k : ℝ) + 1))))) := by
            gcongr; exact hcount _ (by positivity)
      _ ≤ _ := halg
  refine hle_sum.trans_lt ?_
  calc ∑' k : ℕ, ∫⁻ t in Ico (k : ℝ) ((k : ℝ) + 1), ‖wBd t‖ₑ ∂(spinMomentMeasure meas.ν)
      ≤ ∑' k : ℕ, ENNReal.ofReal ((C_N * (2 * B + 2) ^ 2 * 2 * Real.exp (4 * π * Real.sqrt a)) * ((k : ℝ) + 1) ^ (-2 : ℝ)) :=
        tsum_le_tsum hshell
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) ?_]
        · exact ENNReal.ofReal_lt_top
        · have hs : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-2 : ℝ) := by
            refine ((Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 2)).comp_injective
              Nat.succ_injective).congr fun k => ?_
            simp only [Function.comp_apply, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
            rw [Real.rpow_neg (by positivity)]
          exact hs.mul_left _

end FormalResearch.ModularBootstrap.Spin
