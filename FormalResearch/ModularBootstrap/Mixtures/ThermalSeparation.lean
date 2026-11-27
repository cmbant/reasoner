module

public import FormalResearch.ModularBootstrap.Mixtures.DualMajorant
public import FormalResearch.ModularBootstrap.Mixtures.CrossingPort
public import FormalResearch.ModularBootstrap.Duality.ThermalSeparation
public import FormalResearch.ModularBootstrap.Duality.ConstrainedThreshold
public import FormalResearch.ModularBootstrap.Duality.ReserveSeparation

/-!
# Thermal separation (`ds:E` (a), (b), (c)) for atomic shift sources

Source: `CFT/modular_bootstrap/paper/dual_spectrum.tex`, Theorem E (`ds:E`) in the general
common-source / dominated-source setting `(H_{w,\lambda})` (via `SourceDualSetupCore` and
`CrossingBounds`).

* `isFiniteMeasureOnCompacts_src`: every `SourceCrossingMeasure` is locally finite.
* `theorem_E_a_src`, `theorem_E_a_finite_src`, `theorem_E_a_decreasing_src`,
  `theorem_E_a_compactness_src`: `ds:E`(a) on any closed `X ⊆ [T₀, ∞)`.
* `constrainedThresholdS`, `theorem_E_b_compact_src`, `theorem_E_b_compact_empty_src`: `ds:E`(b)
  (attainment of constrained thresholds `T_F` and `T_V`).
* `theorem_E_c_separation_src`, `theorem_E_c_reserve_src`,
  `theorem_E_c_reserve_testClass_src`: `ds:E`(c) (reserve crossing measures).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight

/-! ### Local finiteness and span tests for `ShiftSource` -/

/-- Every `SourceCrossingMeasure` is finite on compact sets (from `finite_laplace` at `β = 1`). -/
lemma isFiniteMeasureOnCompacts_src (src : ShiftSource) {a : ℝ}
    (meas : SourceCrossingMeasure src a) : IsFiniteMeasureOnCompacts meas.ν := by
  refine ⟨fun K hK => ?_⟩
  rcases eq_empty_or_nonempty K with rfl | hKne
  · simp
  obtain ⟨M, hM⟩ := hK.bddAbove
  have hpos_c : 0 < Real.exp (-2 * π * max M 0) := Real.exp_pos _
  have hfin1 := meas.finite_laplace one_pos
  have hmeas_int : ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν < ⊤ :=
    hfin1.2
  have hK_le : meas.ν K ≤ meas.ν (Icc 0 (max M 0)) := by
    have h0 : meas.ν (K ∩ (Ici 0)ᶜ) = 0 := measure_mono_null inter_subset_right meas.support
    calc meas.ν K ≤ meas.ν (K ∩ Ici 0) + meas.ν (K ∩ (Ici 0)ᶜ) := by
          refine measure_mono (fun t ht => ?_)
          by_cases ht0 : t ∈ Ici (0 : ℝ)
          · exact Or.inl ⟨ht, ht0⟩
          · exact Or.inr ⟨ht, ht0⟩
      _ = meas.ν (K ∩ Ici 0) := by rw [h0, add_zero]
      _ ≤ meas.ν (Icc 0 (max M 0)) :=
          measure_mono fun t ⟨htK, ht0⟩ => ⟨ht0, (hM htK).trans (le_max_left M 0)⟩
  refine lt_of_le_of_lt hK_le ?_
  have hmul : ENNReal.ofReal (Real.exp (-2 * π * max M 0)) * meas.ν (Icc 0 (max M 0)) ≤
      ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν := by
    calc ENNReal.ofReal (Real.exp (-2 * π * max M 0)) * meas.ν (Icc 0 (max M 0))
        = ∫⁻ _ in Icc 0 (max M 0), ENNReal.ofReal (Real.exp (-2 * π * max M 0)) ∂meas.ν := by
          rw [setLIntegral_const, Measure.restrict_apply measurableSet_Icc, univ_inter]
      _ ≤ ∫⁻ t in Icc 0 (max M 0), ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν := by
          refine setLIntegral_mono' measurableSet_Icc fun t ht => ENNReal.ofReal_le_ofReal ?_
          exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht.1, ht.2])
      _ ≤ ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν :=
          lintegral_mono_set Icc_subset_Ici_self
  have hmul_lt : ENNReal.ofReal (Real.exp (-2 * π * max M 0)) * meas.ν (Icc 0 (max M 0)) < ⊤ :=
    lt_of_le_of_lt hmul hmeas_int
  rcases ENNReal.mul_lt_top_iff.mp hmul_lt with ⟨_, hlt⟩ | h0 | h0
  · exact hlt
  · exact absurd h0 (ENNReal.ofReal_pos.mpr hpos_c).ne'
  · rw [h0]; exact ENNReal.zero_lt_top

/-- Finite linear combination `∑ l_β Ξ_β + μ h` in `span{Ξ_β, h}` for `ShiftSource`. -/
noncomputable def spanTestS (src : ShiftSource) (l : ℝ →₀ ℝ) (μ : ℝ) (a β₀ : ℝ) : ℝ → ℝ :=
  fun t => (∑ β ∈ l.support, l β * thermalDiff src.w β t) + μ * hMaj src.w a β₀ t

lemma spanTestS_mem {src : ShiftSource} {a β₀ : ℝ} (ha0 : 0 < a) (hβ₀ : 0 < β₀)
    (hnonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ src.cardyV a t)
    (hupper : ∀ {t : ℝ}, 0 ≤ t → src.cardyV a t ≤ src.tv * kernelK src.w a t)
    {l : ℝ →₀ ℝ} (hl : ∀ β ∈ l.support, 0 < β) (μ : ℝ) :
    TestClass src a (spanTestS src l μ a β₀) := by
  have h1 : TestClass src a (fun t => ∑ β ∈ l.support, l β * thermalDiff src.w β t) :=
    testClass_sum_src l.support (fun β => l β) (fun β => thermalDiff src.w β)
      fun β hβ => thermalDiff_mem_TestClass_src ha0 hnonneg hupper (hl β hβ)
  have h2 : TestClass src a (fun t => μ * hMaj src.w a β₀ t) :=
    testClass_smul_src μ (hMaj_mem_TestClass_src ha0 hβ₀ hnonneg hupper)
  exact testClass_add_src h1 h2

lemma gVac_spanTestS {src : ShiftSource} {a β₀ : ℝ} (ha0 : 0 < a) (hβ₀ : 0 < β₀)
    (hnonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ src.cardyV a t)
    (hupper : ∀ {t : ℝ}, 0 ≤ t → src.cardyV a t ≤ src.tv * kernelK src.w a t)
    {l : ℝ →₀ ℝ} (hl : ∀ β ∈ l.support, 0 < β) (μ : ℝ) :
    src.gVac a (spanTestS src l μ a β₀) =
      (∑ β ∈ l.support, l β * src.gVac a (thermalDiff src.w β)) - μ * dualC0S src a β₀ := by
  have h1 : TestClass src a (fun t => ∑ β ∈ l.support, l β * thermalDiff src.w β t) :=
    testClass_sum_src l.support (fun β => l β) (fun β => thermalDiff src.w β)
      fun β hβ => thermalDiff_mem_TestClass_src ha0 hnonneg hupper (hl β hβ)
  have h2 : TestClass src a (fun t => μ * hMaj src.w a β₀ t) :=
    testClass_smul_src μ (hMaj_mem_TestClass_src ha0 hβ₀ hnonneg hupper)
  unfold spanTestS
  rw [gVac_add_src h1 h2,
    gVac_sum_src _ (fun β hβ => thermalDiff_mem_TestClass_src ha0 hnonneg hupper (hl β hβ)),
    gVac_smul_src μ (hMaj_mem_TestClass_src ha0 hβ₀ hnonneg hupper)]
  unfold dualC0S
  ring

lemma spanTestS_decay {src : ShiftSource} {a β₀ : ℝ} (ha0 : 0 < a) (hβ₀ : 0 < β₀)
    {l : ℝ →₀ ℝ} (hl : ∀ β ∈ l.support, 0 < β) (μ : ℝ) {q : ℝ} (hq : 0 < q) :
    ∃ C_g : ℝ, 0 ≤ C_g ∧ ∀ t : ℝ, 0 ≤ t →
      |spanTestS src l μ a β₀ t| ≤ C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t)) := by
  obtain ⟨C_h, hC_h, hbd_h⟩ := Duality.abs_hMaj_le ha0 hβ₀ q
  have hbd_th : ∀ β : ℝ, 0 < β → ∃ C_β : ℝ, 0 ≤ C_β ∧ ∀ t : ℝ, 0 ≤ t →
      |thermalDiff src.w β t| ≤ C_β * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t)) := by
    intro β hβ
    obtain ⟨C₁, hC₁, hbd₁⟩ := exp_neg_mul_sqrt_le ha0 hβ q
    obtain ⟨C₂, hC₂, hbd₂⟩ := exp_neg_mul_sqrt_le ha0 (inv_pos.mpr hβ) q
    refine ⟨C₁ + β ^ (-(src.w : ℝ)) * C₂, by positivity, fun t ht => ?_⟩
    have hexp_eq : -2 * π * t / β = -2 * π * β⁻¹ * t := by ring
    unfold thermalDiff
    rw [hexp_eq]
    calc |Real.exp (-2 * π * β * t) - β ^ (-(src.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t)|
        ≤ |Real.exp (-2 * π * β * t)| + |β ^ (-(src.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t)| :=
          abs_sub _ _
      _ = Real.exp (-2 * π * β * t) + β ^ (-(src.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t) := by
          rw [abs_of_pos (Real.exp_pos _), abs_mul,
            abs_of_pos (Real.rpow_pos_of_pos hβ _), abs_of_pos (Real.exp_pos _)]
      _ ≤ C₁ * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t)) +
            β ^ (-(src.w : ℝ)) * (C₂ * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))) := by
          gcongr
          · exact hbd₁ t ht
          · exact hbd₂ t ht
      _ = (C₁ + β ^ (-(src.w : ℝ)) * C₂) * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t)) := by
          ring
  choose C_f hC_f_nn hbd_f using fun β : l.support => hbd_th β.1 (hl β.1 β.2)
  refine ⟨(∑ β : l.support, |l β.1| * C_f β) + |μ| * C_h,
    add_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (hC_f_nn _))
      (mul_nonneg (abs_nonneg _) hC_h), fun t ht => ?_⟩
  unfold spanTestS
  calc |∑ β ∈ l.support, l β * thermalDiff src.w β t + μ * hMaj src.w a β₀ t|
      ≤ |∑ β ∈ l.support, l β * thermalDiff src.w β t| + |μ * hMaj src.w a β₀ t| := abs_add_le _ _
    _ ≤ ∑ β ∈ l.support, |l β * thermalDiff src.w β t| + |μ| * |hMaj src.w a β₀ t| := by
        rw [abs_mul]; exact add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ = ∑ β : l.support, |l β.1| * |thermalDiff src.w β.1 t| + |μ| * |hMaj src.w a β₀ t| := by
        congr 1
        rw [← Finset.sum_coe_sort l.support]
        refine Finset.sum_congr rfl fun β _ => by rw [abs_mul]
    _ ≤ ∑ β : l.support, |l β.1| * (C_f β * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))) +
          |μ| * (C_h * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))) := by
        gcongr with β
        · exact hbd_f β t ht
        · exact hbd_h t ht
    _ = ((∑ β : l.support, |l β.1| * C_f β) + |μ| * C_h) * (1 + t) ^ (-q) *
          Real.exp (-4 * π * Real.sqrt (a * t)) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        ring

/-- Every crossing measure pairs with any `spanTestS` by exact equality `∫ g dν = -g_vac(g)`. -/
lemma crossing_pairing_span_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) (hcb : CrossingBounds src (cTilde / 12))
    (meas : SourceCrossingMeasure src (cTilde / 12))
    {l : ℝ →₀ ℝ} (hl : ∀ β ∈ l.support, 0 < β) (μ : ℝ) :
    IntegrableOn (spanTestS src l μ (cTilde / 12) β₀) (Ici 0) meas.ν ∧
      src.gVac (cTilde / 12) (spanTestS src l μ (cTilde / 12) β₀) +
        ∫ t in Ici 0, spanTestS src l μ (cTilde / 12) β₀ t ∂meas.ν = 0 := by
  have htc := spanTestS_mem S.ha0 S.hβ₀ S.hnonneg S.hupper hl μ
  have hq : (src.w + 1 : ℝ) / 2 < (src.w + 3 : ℝ) / 2 := by linarith
  have hqpos : 0 < (src.w + 3 : ℝ) / 2 := by positivity
  obtain ⟨C_g, hC_g, hdec⟩ := spanTestS_decay S.ha0 S.hβ₀ hl μ hqpos
  exact lemma_fwX_equality_src src hcb S.ha0 meas htc hq hC_g hdec

/-! ### `NoSpanFeasibleS` and forward direction -/

/-- No combination `g = ∑ l_β Ξ_β + μ h` nonnegative on `X` has `g_vac(g) > 0`. -/
def NoSpanFeasibleS (src : ShiftSource) (cTilde β₀ : ℝ) (X : Set ℝ) : Prop :=
  ∀ (l : ℝ →₀ ℝ) (μ : ℝ), (∀ β ∈ l.support, 0 < β) →
    (∀ t ∈ X, 0 ≤ spanTestS src l μ (cTilde / 12) β₀ t) →
    src.gVac (cTilde / 12) (spanTestS src l μ (cTilde / 12) β₀) ≤ 0

/-- A positive crossing measure carried by `X` excludes all `span{Ξ_β, h}` tests. -/
lemma noSpanFeasibleS_of_crossingMeasure (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) (hcb : CrossingBounds src (cTilde / 12))
    {X : Set ℝ} (meas : SourceCrossingMeasure src (cTilde / 12)) (hX : meas.ν Xᶜ = 0) :
    NoSpanFeasibleS src cTilde β₀ X := by
  intro l μ hl hnn
  obtain ⟨_, heq⟩ := crossing_pairing_span_src src S hcb meas hl μ
  have hnn_ae : 0 ≤ᵐ[meas.ν.restrict (Ici 0)] (spanTestS src l μ (cTilde / 12) β₀) := by
    have hnot : ∀ᵐ t ∂meas.ν, t ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hX
    exact ae_restrict_of_ae (hnot.mono fun t ht => hnn t (Set.notMem_compl_iff.1 ht))
  have hint_pos : 0 ≤ ∫ t in Ici 0, spanTestS src l μ (cTilde / 12) β₀ t ∂meas.ν :=
    integral_nonneg_of_ae hnn_ae
  linarith

/-! ### Constructing `SourceCrossingMeasure` and Farkas separation helper -/

private lemma wStar_ge_exp_beta_src {w : ℕ} {β₀ β t : ℝ} (hβ₀ : 0 < β₀) (hβ : β₀ ≤ β) (ht : 0 ≤ t) :
    Real.exp (-2 * π * β * t) ≤ wStar w β₀ t := by
  have hpi := Real.pi_pos
  have h1 : Real.exp (-2 * π * β * t) ≤ Real.exp (-2 * π * β₀ * t) :=
    Real.exp_le_exp.2 (by nlinarith)
  exact h1.trans (le_add_of_nonneg_right (Real.exp_pos _).le)

private lemma build_crossingMeasure_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) {X : Set ℝ} (hXsub : X ⊆ Ici T₀)
    {ν : Measure ℝ} (hsupp : ν Xᶜ = 0)
    (hw : Integrable (wTilde src.w β₀ T₀) ν)
    (hc : ∀ β : Ioi (0 : ℝ), Integrable (fTilde src.w T₀ β.1) ν ∧
      ∫ t, fTilde src.w T₀ β.1 t ∂ν = -src.gVac (cTilde / 12) (thermalDiff src.w β.1)) :
    SourceCrossingMeasure src (cTilde / 12) := by
  have haeT : ∀ᵐ t ∂ν, T₀ ≤ t := by
    have := measure_eq_zero_iff_ae_notMem.1 hsupp
    exact this.mono fun t ht => hXsub (Set.notMem_compl_iff.1 ht)
  have hIci : ν (Ici 0)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (hXsub.trans (Ici_subset_Ici.2 S.hT₀.le))) hsupp
  have hmeas_exp : ∀ β : ℝ, Continuous (fun t => Real.exp (-2 * π * β * t)) := fun β => by
    fun_prop
  have hw_dom : ∀ {β : ℝ}, β₀ ≤ β → Integrable (fun t => Real.exp (-2 * π * β * t)) ν := by
    intro β hβ
    refine hw.mono' (hmeas_exp β).aestronglyMeasurable ?_
    filter_upwards [haeT] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, wTilde_of_le _ _ ht]
    exact wStar_ge_exp_beta_src S.hβ₀ hβ (S.hT₀.le.trans ht)
  have hlap : ∀ {β : ℝ}, 0 < β →
      IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Ici 0) ν := by
    intro β hβ
    rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
      (haeT.mono fun t ht => S.hT₀.le.trans ht)]
    by_cases hle : β₀ ≤ β
    · exact hw_dom hle
    · have hβlt : β < β₀ := lt_of_not_ge hle
      have hinv : β₀ ≤ β⁻¹ := by
        have h1 : 1 < β⁻¹ := (one_lt_inv₀ hβ).2 (hβlt.trans_le S.hβ₀2 |>.trans (by norm_num))
        exact S.hβ₀2.trans (by linarith)
      have hfi : Integrable (fTilde src.w T₀ β) ν := (hc ⟨β, hβ⟩).1
      have hinv_int : Integrable (fun t => β ^ (-(src.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t)) ν :=
        (hw_dom hinv).const_mul _
      refine (hfi.add hinv_int).congr' (hmeas_exp β).aestronglyMeasurable ?_
      filter_upwards [haeT] with t ht
      rw [fTilde_of_le _ _ ht]
      unfold thermalDiff
      rw [show -2 * π * t / β = -2 * π * β⁻¹ * t by ring]
      ring
  refine ⟨ν, hIci, hlap, fun {β} hβ => ?_⟩
  have heq1 : ∫ t in Ici 0, thermalDiff src.w β t ∂ν = ∫ t, fTilde src.w T₀ β t ∂ν := by
    rw [Measure.restrict_eq_self_of_ae_mem (haeT.mono fun t ht => S.hT₀.le.trans ht)]
    refine integral_congr_ae (haeT.mono fun t ht => ?_)
    exact (fTilde_of_le _ _ ht).symm
  rw [heq1, (hc ⟨β, hβ⟩).2, gVac_thermalDiff_src_eq src (cTilde / 12) hβ]
  ring

private lemma finsupp_sum_single_mul (u : Finset (Ioi (0 : ℝ))) (lam : Ioi (0 : ℝ) → ℝ)
    (F : ℝ → ℝ) :
    (∑ β ∈ (∑ i ∈ u, Finsupp.single i.1 (lam i)).support,
      (∑ i ∈ u, Finsupp.single i.1 (lam i)) β * F β) = ∑ i ∈ u, lam i * F i.1 := by
  classical
  induction u using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    set l := ∑ j ∈ s, Finsupp.single j.1 (lam j)
    have heq : (Finsupp.single i.1 (lam i) + l).sum (fun β c => c * F β) =
        (Finsupp.single i.1 (lam i)).sum (fun β c => c * F β) + l.sum (fun β c => c * F β) :=
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
    change (Finsupp.single i.1 (lam i) + l).sum (fun β c => c * F β) = lam i * F i.1 + _
    rw [heq, Finsupp.sum_single_index (zero_mul _)]
    exact congrArg (fun x => lam i * F i.1 + x) ih

private lemma support_sum_single_pos (u : Finset (Ioi (0 : ℝ))) (lam : Ioi (0 : ℝ) → ℝ) :
    ∀ β ∈ (∑ i ∈ u, Finsupp.single i.1 (lam i)).support, 0 < β := by
  classical
  intro β hβ
  have : β ∈ ⋃ i ∈ u, ((Finsupp.single i.1 (lam i)).support : Set ℝ) := by
    induction u using Finset.induction with
    | empty => simp at hβ
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi] at hβ
      rcases Finset.mem_union.1 (Finsupp.support_add hβ) with h1 | h2
      · exact Set.mem_biUnion (Finset.mem_insert_self i s) h1
      · obtain ⟨j, hj, hmem⟩ := Set.mem_iUnion₂.1 (ih h2)
        exact Set.mem_biUnion (Finset.mem_insert_of_mem hj) hmem
  obtain ⟨j, -, hjβ⟩ := Set.mem_iUnion₂.1 this
  have hsingle := Finsupp.support_single_subset hjβ
  rw [Finset.mem_singleton] at hsingle
  rw [hsingle]
  exact j.2

private lemma span_pos_mom_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) {X : Set ℝ} (hXsub : X ⊆ Ici T₀)
    (hns : NoSpanFeasibleS src cTilde β₀ X) (u : Finset (Ioi (0 : ℝ))) (lam : Ioi (0 : ℝ) → ℝ)
    {b : ℝ} (hb : 0 ≤ b)
    (hpos : ∀ t ∈ X, 0 ≤ b + ∑ i ∈ u, lam i * fTilde src.w T₀ i.1 t / wTilde src.w β₀ T₀ t) :
    0 ≤ b * dualC0S src (cTilde / 12) β₀ +
      ∑ i ∈ u, lam i * (-src.gVac (cTilde / 12) (thermalDiff src.w i.1)) := by
  let l : ℝ →₀ ℝ := ∑ i ∈ u, Finsupp.single i.1 (lam i)
  have hl : ∀ β ∈ l.support, 0 < β := support_sum_single_pos u lam
  have hnn : ∀ t ∈ X, 0 ≤ spanTestS src l b (cTilde / 12) β₀ t := by
    intro t ht
    have htT : T₀ ≤ t := hXsub ht
    have ht0 : 0 ≤ t := S.hT₀.le.trans htT
    have hwpos : 0 < wStar src.w β₀ t := wStar_pos S.hβ₀ ht0
    have hmul := mul_nonneg (hpos t ht) hwpos.le
    have hl_sum : (∑ β ∈ l.support, l β * thermalDiff src.w β t) =
        ∑ i ∈ u, lam i * thermalDiff src.w i.1 t := finsupp_sum_single_mul u lam (fun β => thermalDiff src.w β t)
    have hrhs_eq : (b + ∑ i ∈ u, lam i * fTilde src.w T₀ i.1 t / wTilde src.w β₀ T₀ t) * wStar src.w β₀ t =
        b * wStar src.w β₀ t + ∑ i ∈ u, lam i * thermalDiff src.w i.1 t := by
      rw [add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [wTilde_of_le _ _ htT, fTilde_of_le _ _ htT]
      field_simp [hwpos.ne']
    have hm_ge : wStar src.w β₀ t ≤ hMaj src.w (cTilde / 12) β₀ t :=
      (S.lemma_M htT).2
    have hbw : b * wStar src.w β₀ t ≤ b * hMaj src.w (cTilde / 12) β₀ t :=
      mul_le_mul_of_nonneg_left hm_ge hb
    unfold spanTestS
    rw [hl_sum]
    linarith
  have hvac := hns l b hl hnn
  rw [gVac_spanTestS S.ha0 S.hβ₀ S.hnonneg S.hupper hl b,
    finsupp_sum_single_mul u lam (fun β => src.gVac (cTilde / 12) (thermalDiff src.w β))] at hvac
  linarith

/-! ### Theorem E(a) (`ds:E`(a)) for `SourceDualSetupCore` -/

/-- **Theorem E(a)** (`ds:E`(a), decreasing-support form) for `SourceDualSetupCore`. -/
theorem theorem_E_a_decreasing_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀)
    {X : ℕ → Set ℝ} (hXc : ∀ j, IsClosed (X j)) (hXa : Antitone X) (hX0 : X 0 ⊆ Ici T₀)
    (hns : ∀ j, NoSpanFeasibleS src cTilde β₀ (X j)) :
    ∃ meas : SourceCrossingMeasure src (cTilde / 12),
      meas.ν (⋂ j, X j)ᶜ = 0 ∧
      IntegrableOn (wStar src.w β₀) (Ici 0) meas.ν ∧
      ∫ t in Ici 0, wStar src.w β₀ t ∂meas.ν ≤ dualC0S src (cTilde / 12) β₀ := by
  have hC₀ : 0 < dualC0S src (cTilde / 12) β₀ := S.C₀_pos
  have hwpos : ∀ y : ℝ, 0 < wTilde src.w β₀ T₀ y := fun y =>
    wTilde_pos S.hβ₀ S.hT₀.le
  obtain ⟨ν, _, hsupp, hbud, hmom⟩ := farkas_separation (Y := ℝ) (I := Ioi (0 : ℝ))
    (continuous_wTilde S.hβ₀) hwpos hC₀ hXc hXa
    (fun β => continuous_fTilde (w := src.w) (T₀ := T₀) β.2)
    (fun β ε hε => fTilde_decay S.hβ₀ S.hT₀.le β.2 hε)
    (a := fun β : Ioi (0 : ℝ) => -src.gVac (cTilde / 12) (thermalDiff src.w β.1))
    (fun j u lam b hb hpos =>
      span_pos_mom_src src S ((hXa (Nat.zero_le j)).trans hX0) (hns j) u lam hb fun t ht => by
        simpa [mul_div_assoc] using hpos t ht)
  have hw_int : Integrable (wTilde src.w β₀ T₀) ν :=
    ⟨(continuous_wTilde S.hβ₀).aestronglyMeasurable,
      lt_of_le_of_lt hbud ENNReal.ofReal_lt_top⟩
  have haeT : ∀ᵐ t ∂ν, T₀ ≤ t := by
    have := measure_eq_zero_iff_ae_notMem.1 hsupp
    exact this.mono fun t ht => hX0 (Set.mem_iInter.1 (Set.notMem_compl_iff.1 ht) 0)
  let meas := build_crossingMeasure_src src S (fun t ht => hX0 (Set.mem_iInter.1 ht 0)) hsupp hw_int hmom
  refine ⟨meas, hsupp, ?_, ?_⟩
  · rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
      (haeT.mono fun t ht => S.hT₀.le.trans ht)]
    refine hw_int.congr' ((continuous_wStar S.hβ₀).aestronglyMeasurable) ?_
    filter_upwards [haeT] with t ht
    exact wTilde_of_le _ _ ht
  · have heq : ∫ t in Ici 0, wStar src.w β₀ t ∂meas.ν = ∫ t, wTilde src.w β₀ T₀ t ∂ν := by
      rw [Measure.restrict_eq_self_of_ae_mem (haeT.mono fun t ht => S.hT₀.le.trans ht)]
      refine integral_congr_ae (haeT.mono fun t ht => (wTilde_of_le _ _ ht).symm)
    rw [heq]
    have hof : ENNReal.ofReal (∫ t, wTilde src.w β₀ T₀ t ∂ν) =
        ∫⁻ t, ENNReal.ofReal (wTilde src.w β₀ T₀ t) ∂ν :=
      ofReal_integral_eq_lintegral_ofReal hw_int (Eventually.of_forall fun t => (hwpos t).le)
    rw [← ENNReal.ofReal_le_ofReal_iff hC₀.le, hof]
    exact hbud

/-- **Theorem E(a)** (`ds:E`(a), single closed set + budget bound for any crossing measure) for `SourceDualSetupCore`. -/
theorem theorem_E_a_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) (hcb : CrossingBounds src (cTilde / 12))
    {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀) :
    (NoSpanFeasibleS src cTilde β₀ X ↔
      ∃ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν Xᶜ = 0) ∧
    (∀ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν Xᶜ = 0 →
      IntegrableOn (wStar src.w β₀) (Ici 0) meas.ν ∧
      ∫ t in Ici 0, wStar src.w β₀ t ∂meas.ν ≤ dualC0S src (cTilde / 12) β₀) := by
  have heq : (∃ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν Xᶜ = 0) ↔
      NoSpanFeasibleS src cTilde β₀ X := by
    refine ⟨fun ⟨meas, hν⟩ => noSpanFeasibleS_of_crossingMeasure src S hcb meas hν, fun hns => ?_⟩
    obtain ⟨meas, hν, -, -⟩ := theorem_E_a_decreasing_src src S (fun _ => hXc) (fun _ _ _ => Subset.rfl)
      hX (fun _ => hns)
    refine ⟨meas, ?_⟩
    rwa [iInter_const] at hν
  refine ⟨heq.symm, fun meas hν => ?_⟩
  obtain ⟨_, hmem, _, hle⟩ := lemma_fwX_one_sided_src src hcb S.ha0 meas
    (hMaj_mem_TestClass_src S.ha0 S.hβ₀ S.hnonneg S.hupper) (T := T₀) fun t ht =>
      (S.lemma_M ht).1.le.trans (S.lemma_M ht).2
  have haeT : ∀ᵐ t ∂meas.ν, T₀ ≤ t := by
    have := measure_eq_zero_iff_ae_notMem.1 hν
    exact this.mono fun t ht => hX (Set.notMem_compl_iff.1 ht)
  have hint_w : IntegrableOn (wStar src.w β₀) (Ici 0) meas.ν := by
    rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
      (haeT.mono fun t ht => S.hT₀.le.trans ht)]
    rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
      (haeT.mono fun t ht => S.hT₀.le.trans ht)] at hmem
    refine hmem.mono' (continuous_wStar S.hβ₀).aestronglyMeasurable ?_
    filter_upwards [haeT] with t ht
    rw [Real.norm_of_nonneg (wStar_pos S.hβ₀ (S.hT₀.le.trans ht)).le,
      Real.norm_of_nonneg ((S.lemma_M ht).1.le.trans (S.lemma_M ht).2)]
    exact (S.lemma_M ht).2
  have hle_w : ∫ t in Ici 0, wStar src.w β₀ t ∂meas.ν ≤
      ∫ t in Ici 0, hMaj src.w (cTilde / 12) β₀ t ∂meas.ν := by
    rw [Measure.restrict_eq_self_of_ae_mem (haeT.mono fun t ht => S.hT₀.le.trans ht),
      Measure.restrict_eq_self_of_ae_mem (haeT.mono fun t ht => S.hT₀.le.trans ht)]
    refine integral_mono_ae ?_ ?_ (haeT.mono fun t ht => (S.lemma_M ht).2)
    · rw [← Measure.restrict_eq_self_of_ae_mem (haeT.mono fun t ht => S.hT₀.le.trans ht)]
      exact hint_w
    · rw [← Measure.restrict_eq_self_of_ae_mem (haeT.mono fun t ht => S.hT₀.le.trans ht)]
      exact hmem
  refine ⟨hint_w, ?_⟩
  have hc0 : dualC0S src (cTilde / 12) β₀ = -src.gVac (cTilde / 12) (hMaj src.w (cTilde / 12) β₀) := by
    unfold dualC0S; rfl
  linarith

/-- Finite-atomic `Carathéodory` corollary of `ds:E`(a) for `SourceDualSetupCore`. -/
theorem theorem_E_a_finite_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hns : NoSpanFeasibleS src cTilde β₀ X) (u : Finset (Ioi (0 : ℝ))) :
    ∃ (ι : Type) (_ : Fintype ι) (y : ι → ℝ) (r : ι → ℝ), Fintype.card ι ≤ u.card + 1 ∧
      (∀ k, y k ∈ X) ∧ (∀ k, 0 ≤ r k) ∧ ∑ k, r k * wStar src.w β₀ (y k) ≤ dualC0S src (cTilde / 12) β₀ ∧
      ∀ β ∈ u, ∑ k, r k * thermalDiff src.w β.1 (y k) =
        -src.gVac (cTilde / 12) (thermalDiff src.w β.1) := by
  have hC₀ : 0 < dualC0S src (cTilde / 12) β₀ := S.C₀_pos
  have hwpos : ∀ y : ℝ, 0 < wTilde src.w β₀ T₀ y := fun y => wTilde_pos S.hβ₀ S.hT₀.le
  obtain ⟨ι, hι, y, r, hcard, hyX, hr, hbud, hmom⟩ := farkas_finite (Y := ℝ) hXc
    (continuous_wTilde S.hβ₀) hwpos hC₀
    (fun β : Ioi (0 : ℝ) => continuous_fTilde (w := src.w) (T₀ := T₀) β.2)
    (fun β ε hε => fTilde_decay S.hβ₀ S.hT₀.le β.2 hε) u
    (fun lam b hb hpos => span_pos_mom_src src S hX hns u lam hb fun t ht => by
      simpa [mul_div_assoc] using hpos t ht)
  refine ⟨ι, hι, y, r, hcard, hyX, hr, ?_, fun β hβ => ?_⟩
  · refine le_trans (Finset.sum_le_sum fun k _ => ?_) hbud
    rw [wTilde_of_le _ _ (hX (hyX k))]
  · have := hmom β hβ
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fTilde_of_le _ _ (hX (hyX k))]

/-- Vague compactness (`ds:E`(a)) along a decreasing sequence of closed supports for `SourceDualSetupCore`. -/
theorem theorem_E_a_compactness_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) (hcb : CrossingBounds src (cTilde / 12))
    {X : ℕ → Set ℝ} (hXc : ∀ j, IsClosed (X j)) (hXa : Antitone X) (hX0 : X 0 ⊆ Ici T₀)
    (meas : ∀ j, SourceCrossingMeasure src (cTilde / 12))
    (hsupp : ∀ j, (meas j).ν (X j)ᶜ = 0)
    (𝒰 : Ultrafilter ℕ) (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) :
    ∃ meas' : SourceCrossingMeasure src (cTilde / 12),
      IsVagueLimitAlong (𝒰 : Filter ℕ) (fun j => (meas j).ν) meas'.ν ∧
      meas'.ν (⋂ j, X j)ᶜ = 0 ∧
      IntegrableOn (wStar src.w β₀) (Ici 0) meas'.ν ∧
      ∫ t in Ici 0, wStar src.w β₀ t ∂meas'.ν ≤ dualC0S src (cTilde / 12) β₀ := by
  have hC₀ : 0 < dualC0S src (cTilde / 12) β₀ := S.C₀_pos
  have hwpos : ∀ y : ℝ, 0 < wTilde src.w β₀ T₀ y := fun y => wTilde_pos S.hβ₀ S.hT₀.le
  haveI : ∀ j, IsFiniteMeasureOnCompacts (meas j).ν := fun j =>
    isFiniteMeasureOnCompacts_src src (meas j)
  have hbud : ∀ j, ∫⁻ y, ENNReal.ofReal (wTilde src.w β₀ T₀ y) ∂(meas j).ν ≤
      ENNReal.ofReal (dualC0S src (cTilde / 12) β₀) := fun j => by
    have hE := (theorem_E_a_src src S hcb (hXc j) ((hXa (Nat.zero_le j)).trans hX0)).2 (meas j) (hsupp j)
    have haeT : ∀ᵐ t ∂(meas j).ν, T₀ ≤ t := by
      have := measure_eq_zero_iff_ae_notMem.1 (hsupp j)
      exact this.mono fun t ht => (hXa (Nat.zero_le j) |>.trans hX0) (Set.notMem_compl_iff.1 ht)
    have hint_w : Integrable (wTilde src.w β₀ T₀) (meas j).ν := by
      rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
        (haeT.mono fun t ht => S.hT₀.le.trans ht)] at hE
      exact hE.1.congr' (continuous_wTilde S.hβ₀).aestronglyMeasurable
        (haeT.mono fun t ht => (wTilde_of_le _ _ ht).symm)
    have hof : ENNReal.ofReal (∫ t, wTilde src.w β₀ T₀ t ∂(meas j).ν) =
        ∫⁻ t, ENNReal.ofReal (wTilde src.w β₀ T₀ t) ∂(meas j).ν :=
      ofReal_integral_eq_lintegral_ofReal hint_w (Eventually.of_forall fun t => (hwpos t).le)
    rw [← hof]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : ∫ t, wTilde src.w β₀ T₀ t ∂(meas j).ν =
        ∫ t in Ici 0, wStar src.w β₀ t ∂(meas j).ν := by
      rw [Measure.restrict_eq_self_of_ae_mem (haeT.mono fun t ht => S.hT₀.le.trans ht)]
      exact integral_congr_ae (haeT.mono fun t ht => wTilde_of_le _ _ ht)
    rw [heq]
    exact hE.2
  have hmom : ∀ j (β : Ioi (0 : ℝ)), ∫ y, fTilde src.w T₀ β.1 y ∂(meas j).ν =
      -src.gVac (cTilde / 12) (thermalDiff src.w β.1) := fun j β => by
    have haeT : ∀ᵐ t ∂(meas j).ν, T₀ ≤ t := by
      have := measure_eq_zero_iff_ae_notMem.1 (hsupp j)
      exact this.mono fun t ht => (hXa (Nat.zero_le j) |>.trans hX0) (Set.notMem_compl_iff.1 ht)
    have heq : ∫ y, fTilde src.w T₀ β.1 y ∂(meas j).ν =
        ∫ y in Ici 0, thermalDiff src.w β.1 y ∂(meas j).ν := by
      rw [Measure.restrict_eq_self_of_ae_mem (haeT.mono fun t ht => S.hT₀.le.trans ht)]
      exact integral_congr_ae (haeT.mono fun t ht => fTilde_of_le _ _ ht)
    rw [heq, (meas j).crossing β.2, gVac_thermalDiff_src_eq src (cTilde / 12) β.2]
    ring
  obtain ⟨ν', _, hlim, hsupp', hbud', hmom'⟩ := farkas_compactness (Y := ℝ)
    (continuous_wTilde S.hβ₀) hwpos hC₀ hXc hXa
    (fun β : Ioi (0 : ℝ) => continuous_fTilde (w := src.w) (T₀ := T₀) β.2)
    (fun β ε hε => fTilde_decay S.hβ₀ S.hT₀.le β.2 hε)
    (fun j => (meas j).ν) hsupp hbud hmom 𝒰 h𝒰
  have hw_int : Integrable (wTilde src.w β₀ T₀) ν' :=
    ⟨(continuous_wTilde S.hβ₀).aestronglyMeasurable, lt_of_le_of_lt hbud' ENNReal.ofReal_lt_top⟩
  let meas' := build_crossingMeasure_src src S (fun t ht => hX0 (Set.mem_iInter.1 ht 0))
    hsupp' hw_int hmom'
  have hE' := (theorem_E_a_src src S hcb (isClosed_iInter hXc)
    (fun t ht => hX0 (Set.mem_iInter.1 ht 0))).2 meas' hsupp'
  exact ⟨meas', hlim, hsupp', hE'⟩

/-! ### Theorem E(b) (`ds:E`(b)): Constrained thresholds -/

/-- Set of constrained gaps `τ > 0` admitting `g ∈ \overline{\mathcal A}` strictly feasible on `F ∪ [τ, ∞)`. -/
def constrainedGapsS (src : ShiftSource) (cTilde : ℝ) (F : Set ℝ) : Set ℝ :=
  {τ : ℝ | 0 < τ ∧ ∃ g : ℝ → ℝ, src.IsFeasibleOn (cTilde / 12) (F ∪ Ici τ) g}

/-- Constrained threshold `T_F := \inf \{τ > 0 : ∃ g ∈ \overline{\mathcal A} \text{ feasible on } F ∪ [τ, ∞)\}`. -/
noncomputable def constrainedThresholdS (src : ShiftSource) (cTilde : ℝ) (F : Set ℝ) : ℝ :=
  sInf (constrainedGapsS src cTilde F)

lemma le_constrainedThresholdS_of_crossingMeasure (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) (hcb : CrossingBounds src (cTilde / 12))
    {F : Set ℝ} (hne : (constrainedGapsS src cTilde F).Nonempty)
    (meas : SourceCrossingMeasure src (cTilde / 12)) {τ : ℝ}
    (hν : meas.ν (F ∪ Ici τ)ᶜ = 0) : τ ≤ constrainedThresholdS src cTilde F := by
  refine le_csInf hne fun τ' ⟨_, g, hg_tc, hg_vac, hg_nn⟩ => ?_
  by_contra hlt
  have hτ : τ' < τ := lt_of_not_ge hlt
  obtain ⟨_, hle⟩ := lemma_fwX_one_sided_src src hcb S.ha0 meas hg_tc (T := τ') fun t ht =>
    hg_nn t (Or.inr ht)
  have hae : 0 ≤ᵐ[meas.ν.restrict (Ici 0)] g := by
    have hnot : ∀ᵐ t ∂meas.ν, t ∉ (F ∪ Ici τ)ᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    exact ae_restrict_of_ae (hnot.mono fun t ht => by
      rcases Set.notMem_compl_iff.1 ht with h | h
      · exact hg_nn t (Or.inl h)
      · exact hg_nn t (Or.inr (le_trans hτ.le h)))
  have hint_pos : 0 ≤ ∫ t in Ici 0, g t ∂meas.ν := integral_nonneg_of_ae hae
  linarith

/-- **`ds:E`(b) for compact `F ⊂ (0, ∞)`** under any floor `Fl.At (c̃ / 12)` with `0 < T_V`. -/
theorem theorem_E_b_compact_src {src : ShiftSource} {Fl : FloorData src} {cTilde : ℝ}
    (hAt : Fl.At (cTilde / 12)) {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0)
    (hTV : 0 < src.T_V cTilde) :
    (src.T_V cTilde ≤ constrainedThresholdS src cTilde F ∧
      (constrainedGapsS src cTilde F).Nonempty) ∧
    (0 < constrainedThresholdS src cTilde F ∧
      ∃ meas : SourceCrossingMeasure src (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThresholdS src cTilde F))ᶜ = 0) ∧
    (IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure src (cTilde / 12),
        meas.ν (F ∪ Ici τ)ᶜ = 0} (constrainedThresholdS src cTilde F)) ∧
    (∀ τ : ℝ, 0 < τ → τ < constrainedThresholdS src cTilde F →
      ∃ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν (F ∪ Ici τ)ᶜ = 0) := by
  have hcb : CrossingBounds src (cTilde / 12) := hAt.crossingBounds
  have hne : (constrainedGapsS src cTilde F).Nonempty := by
    obtain ⟨β₀, S₀⟩ := SourceDualSetupCore.exists_of_floor hAt one_pos
    obtain ⟨τ, hτ, g, hg⟩ := exists_feasible_src_of_compact hAt S₀ hFc hF
    exact ⟨τ, hτ, g, hg⟩
  have hsub_gap : constrainedGapsS src cTilde F ⊆
      {T : ℝ | 0 < T ∧ ∃ g : ℝ → ℝ, src.IsFeasible (cTilde / 12) T g} := by
    intro τ ⟨hτ, g, hg_tc, hg_vac, hg_nn⟩
    exact ⟨hτ, g, hg_tc, hg_vac, fun t ht => hg_nn t (Or.inr ht)⟩
  have hTV_le : src.T_V cTilde ≤ constrainedThresholdS src cTilde F :=
    csInf_le_csInf ⟨0, fun T hT => hT.1.le⟩ hne hsub_gap
  have hTF_pos : 0 < constrainedThresholdS src cTilde F := lt_of_lt_of_le hTV hTV_le
  set TF : ℝ := constrainedThresholdS src cTilde F with hTF_def
  have exists_meas_for : ∀ τ : ℝ, 0 < τ → τ < TF →
      ∃ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν (F ∪ Ici τ)ᶜ = 0 := by
    intro τ hτ_pos hτ_lt
    -- Pick T₀ > 0 below both `τ` and `min F`
    have hT₀_ex : ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ τ ∧ F ⊆ Ici T₀ := by
      rcases F.eq_empty_or_nonempty with rfl | hFne
      · exact ⟨τ, hτ_pos, le_rfl, empty_subset _⟩
      · obtain ⟨m, hmF, hmin⟩ := hFc.exists_isMinOn hFne continuous_id.continuousOn
        have hm_pos : 0 < m := hF hmF
        exact ⟨min τ m, lt_min hτ_pos hm_pos, min_le_left _ _, fun t ht =>
          (min_le_right _ _).trans (isMinOn_iff.1 hmin t ht)⟩
    obtain ⟨T₀, hT₀_pos, hT₀_τ, hFT₀⟩ := hT₀_ex
    obtain ⟨β₀, S⟩ := SourceDualSetupCore.exists_of_floor hAt hT₀_pos
    have hXc : IsClosed (F ∪ Ici τ) := hFc.isClosed.union isClosed_Ici
    have hXsub : F ∪ Ici τ ⊆ Ici T₀ := union_subset hFT₀ (Ici_subset_Ici.2 hT₀_τ)
    refine ((theorem_E_a_src src S hcb hXc hXsub).1).mp ?_
    intro l μ hl hnn
    by_contra hvac
    have hvac_pos : 0 < src.gVac (cTilde / 12) (spanTestS src l μ (cTilde / 12) β₀) :=
      lt_of_not_ge hvac
    have hmem : τ ∈ constrainedGapsS src cTilde F :=
      ⟨hτ_pos, spanTestS src l μ (cTilde / 12) β₀,
        spanTestS_mem S.ha0 S.hβ₀ S.hnonneg S.hupper hl μ, hvac_pos, hnn⟩
    have hle := csInf_le ⟨0, fun t ht => ht.1.le⟩ hmem
    linarith
  have hT₀_ex : ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ TF / 2 ∧ F ⊆ Ici T₀ := by
    rcases F.eq_empty_or_nonempty with rfl | hFne
    · exact ⟨TF / 2, half_pos hTF_pos, le_rfl, empty_subset _⟩
    · obtain ⟨m, hmF, hmin⟩ := hFc.exists_isMinOn hFne continuous_id.continuousOn
      have hm_pos : 0 < m := hF hmF
      exact ⟨min (TF / 2) m, lt_min (half_pos hTF_pos) hm_pos, min_le_left _ _, fun t ht =>
        (min_le_right _ _).trans (isMinOn_iff.1 hmin t ht)⟩
  obtain ⟨T₀, hT₀_pos, hT₀_half, hFT₀⟩ := hT₀_ex
  obtain ⟨β₀, S⟩ := SourceDualSetupCore.exists_of_floor hAt hT₀_pos
  have hXc : IsClosed (F ∪ Ici TF) := hFc.isClosed.union isClosed_Ici
  have hXsub : F ∪ Ici TF ⊆ Ici T₀ := union_subset hFT₀ (Ici_subset_Ici.2 (by linarith))
  have hns_TF : NoSpanFeasibleS src cTilde β₀ (F ∪ Ici TF) := by
    let τ_seq : ℕ → ℝ := fun n => TF - (TF - T₀) / ((n : ℝ) + 2)
    have hτ_pos : ∀ n, T₀ ≤ τ_seq n := fun n => by
      dsimp [τ_seq]
      have h1 : (TF - T₀) / ((n : ℝ) + 2) ≤ TF - T₀ :=
        div_le_self (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      linarith
    have hτ_lt : ∀ n, τ_seq n < TF := fun n => by
      dsimp [τ_seq]
      have h1 : 0 < (TF - T₀) / ((n : ℝ) + 2) :=
        div_pos (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      linarith
    have hτ_mono : Monotone τ_seq := by
      intro m n hmn
      dsimp [τ_seq]
      have : ((m : ℝ) + 2) ≤ (n : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hmn 2
      have hdiv := div_le_div_of_nonneg_left (by linarith : 0 ≤ TF - T₀)
        (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) this
      linarith
    let Xn : ℕ → Set ℝ := fun n => F ∪ Ici (τ_seq n)
    have hXnc : ∀ n, IsClosed (Xn n) := fun n => hFc.isClosed.union isClosed_Ici
    have hXna : Antitone Xn := fun m n hmn => union_subset_union_right F (Ici_subset_Ici.2 (hτ_mono hmn))
    have hXn0 : Xn 0 ⊆ Ici T₀ := union_subset hFT₀ (Ici_subset_Ici.2 (hτ_pos 0))
    have hns_n : ∀ n, NoSpanFeasibleS src cTilde β₀ (Xn n) := fun n => by
      obtain ⟨meas, hν⟩ := exists_meas_for (τ_seq n) (hT₀_pos.trans_le (hτ_pos n)) (hτ_lt n)
      exact noSpanFeasibleS_of_crossingMeasure src S hcb meas hν
    obtain ⟨meas_lim, hν_lim, -, -⟩ := theorem_E_a_decreasing_src src S hXnc hXna hXn0 hns_n
    have hInter : (⋂ n, Xn n) = F ∪ Ici TF := by
      refine Subset.antisymm (fun y hy => ?_) (fun y hy => mem_iInter.2 fun n => ?_)
      · by_cases hyF : y ∈ F
        · exact Or.inl hyF
        · refine Or.inr ?_
          have hall : ∀ n, τ_seq n ≤ y := fun n => (mem_iInter.1 hy n).resolve_left hyF
          by_contra hlt0
          have hlt : y < TF := lt_of_not_ge hlt0
          obtain ⟨n, hn⟩ := exists_nat_gt ((TF - T₀) / (TF - y))
          have hlt2 : (TF - T₀) / ((n : ℝ) + 2) < TF - y := by
            rw [div_lt_iff₀ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
            have h1 := (div_lt_iff₀ (by linarith : 0 < TF - y)).mp hn
            nlinarith [show (0 : ℝ) ≤ TF - T₀ by linarith]
          have : y < τ_seq n := by dsimp [τ_seq]; linarith
          linarith [hall n]
      · rcases hy with hy | hy
        · exact Or.inl hy
        · exact Or.inr (le_trans (hτ_lt n).le hy)
    rw [hInter] at hν_lim
    exact noSpanFeasibleS_of_crossingMeasure src S hcb meas_lim hν_lim
  obtain ⟨meas_opt, hν_opt⟩ := ((theorem_E_a_src src S hcb hXc hXsub).1).mp hns_TF
  refine ⟨⟨hTV_le, hne⟩, ⟨hTF_pos, meas_opt, hν_opt⟩, ⟨⟨hTF_pos, meas_opt, hν_opt⟩, ?_⟩,
    exists_meas_for⟩
  rintro τ ⟨-, meas, hν⟩
  exact le_constrainedThresholdS_of_crossingMeasure src S hcb hne meas hν

/-- **`ds:E`(b) for `F = ∅`**: `0 < T_V → T_V` is attained as the maximum crossing gap. -/
theorem theorem_E_b_compact_empty_src {src : ShiftSource} {Fl : FloorData src} {cTilde : ℝ}
    (hAt : Fl.At (cTilde / 12)) (hTV : 0 < src.T_V cTilde) :
    constrainedThresholdS src cTilde ∅ = src.T_V cTilde ∧
    (∃ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν (Ici (src.T_V cTilde))ᶜ = 0) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure src (cTilde / 12),
      meas.ν (Ici τ)ᶜ = 0} (src.T_V cTilde) := by
  have heq : constrainedThresholdS src cTilde ∅ = src.T_V cTilde := by
    unfold constrainedThresholdS constrainedGapsS ShiftSource.T_V
    congr 1; ext τ
    simp only [mem_setOf_eq, empty_union, isFeasibleOn_Ici_iff_src]
  have hE := theorem_E_b_compact_src hAt isCompact_empty (empty_subset _) hTV
  rcases hE with ⟨_, ⟨_, meas, hν⟩, hmax, _⟩
  rw [heq, empty_union] at hν hmax
  refine ⟨heq, ⟨meas, hν⟩, ?_⟩
  simpa only [empty_union] using hmax

/-! ### Theorem E(c) (`ds:E`(c)): Reserve separation -/

private lemma ae_mem_of_null_src {X : Set ℝ} {σ : Measure ℝ} (hσ : σ Xᶜ = 0) :
    ∀ᵐ y ∂σ, y ∈ X := by
  have := measure_eq_zero_iff_ae_notMem.1 hσ
  filter_upwards [this] with y hy using Set.notMem_compl_iff.1 hy

/-- `w̃ ∈ L¹(σ)` when `h ∈ L¹(σ)` and `σ` is carried by `X ⊆ [T₀, ∞)`. -/
lemma integrable_wTilde_of_h_src {src : ShiftSource} {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀) {σ : Measure ℝ}
    (hσ : σ Xᶜ = 0) (hh : Integrable (hMaj src.w (cTilde / 12) β₀) σ) :
    Integrable (wTilde (cTilde / 12) β₀ T₀) σ := by
  refine hh.mono' (continuous_wTilde S.hβ₀).aestronglyMeasurable ?_
  filter_upwards [ae_mem_of_null_src hσ] with y hy
  have hy0 := hX hy
  rw [Real.norm_eq_abs, abs_of_pos (wTilde_pos S.hβ₀ S.hT₀.le), wTilde_of_le _ _ hy0]
  exact (S.lemma_M hy0).2

/-- `f̃_β ∈ L¹(σ)` for every `β > 0`, when `h ∈ L¹(σ)`. -/
lemma integrable_fTilde_of_h_src {src : ShiftSource} {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀) {σ : Measure ℝ}
    (hσ : σ Xᶜ = 0) [IsFiniteMeasureOnCompacts σ]
    (hh : Integrable (hMaj src.w (cTilde / 12) β₀) σ) {β : ℝ} (hβ : 0 < β) :
    Integrable (fTilde src.w T₀ β) σ := by
  have hw := integrable_wTilde_of_h_src S hX hσ hh
  obtain ⟨K, hK, hKd⟩ := fTilde_decay (w := src.w) S.hβ₀ S.hT₀.le hβ 1 one_pos
  have hf := continuous_fTilde (w := src.w) (T₀ := T₀) hβ
  have h1 : IntegrableOn (fTilde src.w T₀ β) K σ := hf.continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn (fTilde src.w T₀ β) Kᶜ σ := by
    refine Integrable.mono' (hw.mono_measure Measure.restrict_le_self)
      hf.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hK.isClosed.measurableSet.compl]
    filter_upwards [ae_mem_of_null_src hσ] with y hy hyK
    have := hKd y (hX hy) hyK
    rw [Real.norm_eq_abs]
    linarith
  have := h1.union h2
  rwa [union_compl_self, integrableOn_univ] at this

lemma integrable_thermalDiff_of_h_src {src : ShiftSource} {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀) {σ : Measure ℝ}
    (hσ : σ Xᶜ = 0) [IsFiniteMeasureOnCompacts σ]
    (hh : Integrable (hMaj src.w (cTilde / 12) β₀) σ) {β : ℝ} (hβ : 0 < β) :
    Integrable (thermalDiff src.w β) σ := by
  refine (integrable_fTilde_of_h_src S hX hσ hh hβ).congr ?_
  filter_upwards [ae_mem_of_null_src hσ] with y hy using fTilde_of_le _ _ (hX hy)

lemma integral_spanTestS_of_h {src : ShiftSource} {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀) {σ : Measure ℝ}
    (hσ : σ Xᶜ = 0) [IsFiniteMeasureOnCompacts σ]
    (hh : Integrable (hMaj src.w (cTilde / 12) β₀) σ)
    {l : ℝ →₀ ℝ} (hl : ∀ β ∈ l.support, 0 < β) (μ : ℝ) :
    Integrable (spanTestS src l μ (cTilde / 12) β₀) σ ∧
    ∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂σ =
      (∑ β ∈ l.support, l β * ∫ t, thermalDiff src.w β t ∂σ) +
        μ * ∫ t, hMaj src.w (cTilde / 12) β₀ t ∂σ := by
  have hXi : ∀ β ∈ l.support, Integrable (fun t => l β * thermalDiff src.w β t) σ := fun β hβ =>
    (integrable_thermalDiff_of_h_src S hX hσ hh (hl β hβ)).const_mul _
  have hsum : Integrable (fun t => ∑ β ∈ l.support, l β * thermalDiff src.w β t) σ :=
    integrable_finsetSum _ hXi
  refine ⟨hsum.add (hh.const_mul μ), ?_⟩
  unfold spanTestS
  rw [integral_add hsum (hh.const_mul μ), integral_finsetSum _ hXi, integral_const_mul]
  congr 1
  exact Finset.sum_congr rfl fun β _ => integral_const_mul _ _

/-- **Reserve separation (`ds:E`(c))**: for `r ≥ 0` with `r ∫ h dσ < C₀`, if
`r ∫ g dσ ≤ -g_vac(g)` for every `g = spanTestS src l μ` (`μ ≥ 0`) nonnegative on `X`,
there is a crossing measure `meas` carried by `X` with `r • σ ≤ meas.ν`,
`∫ w_* dν ≤ dualC0S`. -/
theorem theorem_E_c_separation_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    {σ : Measure ℝ} [IsFiniteMeasureOnCompacts σ] (hσ : σ Xᶜ = 0)
    (hh : Integrable (hMaj src.w (cTilde / 12) β₀) σ) {r : ℝ} (hr : 0 ≤ r)
    (hbud : r * ∫ t, hMaj src.w (cTilde / 12) β₀ t ∂σ < dualC0S src (cTilde / 12) β₀)
    (hH : ∀ (l : ℝ →₀ ℝ) (μ : ℝ), (∀ β ∈ l.support, 0 < β) → 0 ≤ μ →
      (∀ t ∈ X, 0 ≤ spanTestS src l μ (cTilde / 12) β₀ t) →
      r * ∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂σ ≤
        -src.gVac (cTilde / 12) (spanTestS src l μ (cTilde / 12) β₀)) :
    ∃ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν Xᶜ = 0 ∧
      ENNReal.ofReal r • σ ≤ meas.ν ∧ IntegrableOn (wStar src.w β₀) (Ici 0) meas.ν ∧
      ∫ t in Ici 0, wStar src.w β₀ t ∂meas.ν ≤ dualC0S src (cTilde / 12) β₀ := by
  classical
  have hC₀ : 0 < dualC0S src (cTilde / 12) β₀ := S.C₀_pos
  set C₀ := dualC0S src (cTilde / 12) β₀ with hC₀def
  set H := ∫ t, hMaj src.w (cTilde / 12) β₀ t ∂σ with hHdef
  have hC₀' : 0 < C₀ - r * H := by linarith
  have hwpos : ∀ y : ℝ, 0 < wTilde src.w β₀ T₀ y := fun y => wTilde_pos S.hβ₀ S.hT₀.le
  have hfint : ∀ β : ℝ, 0 < β → Integrable (fTilde src.w T₀ β) σ := fun β hβ =>
    integrable_fTilde_of_h_src S hX hσ hh hβ
  have hw_int_σ : Integrable (wTilde (cTilde / 12) β₀ T₀) σ :=
    integrable_wTilde_of_h_src S hX hσ hh
  let a' : Ioi (0 : ℝ) → ℝ := fun β =>
    -src.gVac (cTilde / 12) (thermalDiff src.w β.1) - r * ∫ t, thermalDiff src.w β.1 t ∂σ
  have hsep : ∀ (j : ℕ) (u : Finset (Ioi (0 : ℝ))) (lam : Ioi (0 : ℝ) → ℝ) (b : ℝ), 0 ≤ b →
      (∀ y ∈ X, 0 ≤ b + ∑ i ∈ u, lam i * (fTilde src.w T₀ i.1 y / wTilde src.w β₀ T₀ y)) →
      0 ≤ b * (C₀ - r * H) + ∑ i ∈ u, lam i * a' i := by
    intro _ u lam b hb hpos
    let l : ℝ →₀ ℝ := ∑ i ∈ u, Finsupp.single i.1 (lam i)
    have hl : ∀ β ∈ l.support, 0 < β := support_sum_single_pos u lam
    have hnn : ∀ t ∈ X, 0 ≤ spanTestS src l b (cTilde / 12) β₀ t := by
      intro t ht
      have htT : T₀ ≤ t := hX ht
      have ht0 : 0 ≤ t := S.hT₀.le.trans htT
      have hwpos_t : 0 < wStar src.w β₀ t := wStar_pos S.hβ₀ ht0
      have hmul := mul_nonneg (hpos t ht) hwpos_t.le
      have hl_sum : (∑ β ∈ l.support, l β * thermalDiff src.w β t) =
          ∑ i ∈ u, lam i * thermalDiff src.w i.1 t :=
        finsupp_sum_single_mul u lam (fun β => thermalDiff src.w β t)
      have hrhs_eq : (b + ∑ i ∈ u, lam i * (fTilde src.w T₀ i.1 t / wTilde src.w β₀ T₀ t)) *
            wStar src.w β₀ t =
          b * wStar src.w β₀ t + ∑ i ∈ u, lam i * thermalDiff src.w i.1 t := by
        rw [add_mul, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [wTilde_of_le _ _ htT, fTilde_of_le _ _ htT]
        field_simp [hwpos_t.ne']
      have hbw : b * wStar src.w β₀ t ≤ b * hMaj src.w (cTilde / 12) β₀ t :=
        mul_le_mul_of_nonneg_left (S.lemma_M htT).2 hb
      unfold spanTestS
      rw [hl_sum]
      linarith
    have hint_g := integral_spanTestS_of_h S hX hσ hh hl b
    have hg_H := hH l b hl hb hnn
    rw [hint_g.2, finsupp_sum_single_mul u lam (fun β => ∫ t, thermalDiff src.w β t ∂σ),
      gVac_spanTestS S.ha0 S.hβ₀ S.hnonneg S.hupper hl b,
      finsupp_sum_single_mul u lam (fun β => src.gVac (cTilde / 12) (thermalDiff src.w β))] at hg_H
    have ha_sum : ∑ i ∈ u, lam i * a' i =
        (∑ i ∈ u, lam i * (-src.gVac (cTilde / 12) (thermalDiff src.w i.1))) -
          r * ∑ i ∈ u, lam i * ∫ t, thermalDiff src.w i.1 t ∂σ := by
      simp only [a', mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun i _ => by ring)
    rw [ha_sum]
    change 0 ≤ b * (C₀ - r * H) + _
    dsimp only [C₀, H] at hg_H ⊢
    linarith
  obtain ⟨ν₀, _, hsupp0, hbud0, hmom0⟩ := farkas_separation (Y := ℝ) (I := Ioi (0 : ℝ))
    (continuous_wTilde S.hβ₀) hwpos hC₀' (fun _ => hXc) (fun _ _ _ => Subset.rfl)
    (fun β => continuous_fTilde (w := src.w) (T₀ := T₀) β.2)
    (fun β ε hε => fTilde_decay S.hβ₀ S.hT₀.le β.2 hε)
    (a := a') hsep
  rw [iInter_const] at hsupp0
  let ν : Measure ℝ := ν₀ + ENNReal.ofReal r • σ
  have hν_supp : ν Xᶜ = 0 := by
    simp [ν, hsupp0, hσ]
  have hw_int0 : Integrable (wTilde src.w β₀ T₀) ν₀ :=
    ⟨(continuous_wTilde S.hβ₀).aestronglyMeasurable, lt_of_le_of_lt hbud0 ENNReal.ofReal_lt_top⟩
  have hw_int_ν : Integrable (wTilde src.w β₀ T₀) ν := by
    refine hw_int0.add_measure ?_
    exact hw_int_σ.smul_measure ENNReal.ofReal_ne_top
  have hmom_ν : ∀ β : Ioi (0 : ℝ), Integrable (fTilde src.w T₀ β.1) ν ∧
      ∫ t, fTilde src.w T₀ β.1 t ∂ν = -src.gVac (cTilde / 12) (thermalDiff src.w β.1) := fun β => by
    have hf0 := (hmom0 β).1
    have hfσ := hfint β.1 β.2
    have hsm : Integrable (fTilde src.w T₀ β.1) (ENNReal.ofReal r • σ) :=
      hfσ.smul_measure ENNReal.ofReal_ne_top
    refine ⟨hf0.add_measure hsm, ?_⟩
    rw [integral_add_measure hf0 hsm, integral_smul_measure, ENNReal.toReal_ofReal hr, smul_eq_mul,
      (hmom0 β).2]
    have heq_f : ∫ t, fTilde src.w T₀ β.1 t ∂σ = ∫ t, thermalDiff src.w β.1 t ∂σ :=
      integral_congr_ae (ae_mem_of_null_src hσ |>.mono fun t ht => fTilde_of_le _ _ (hX ht))
    rw [heq_f]
    dsimp [a']
    ring
  let meas := build_crossingMeasure_src src S hX hν_supp hw_int_ν hmom_ν
  have haeT : ∀ᵐ t ∂ν, T₀ ≤ t :=
    ae_mem_of_null_src hν_supp |>.mono fun t ht => hX ht
  have hw_meas : IntegrableOn (wStar src.w β₀) (Ici 0) meas.ν := by
    rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
      (haeT.mono fun t ht => S.hT₀.le.trans ht)]
    exact hw_int_ν.congr' (continuous_wStar S.hβ₀).aestronglyMeasurable
      (haeT.mono fun t ht => wTilde_of_le _ _ ht)
  have hbud_meas : ∫ t in Ici 0, wStar src.w β₀ t ∂meas.ν ≤ C₀ := by
    have heq : ∫ t in Ici 0, wStar src.w β₀ t ∂meas.ν = ∫ t, wTilde src.w β₀ T₀ t ∂ν := by
      rw [Measure.restrict_eq_self_of_ae_mem (haeT.mono fun t ht => S.hT₀.le.trans ht)]
      exact integral_congr_ae (haeT.mono fun t ht => (wTilde_of_le _ _ ht).symm)
    rw [heq]
    have hsm_w : Integrable (wTilde src.w β₀ T₀) (ENNReal.ofReal r • σ) :=
      hw_int_σ.smul_measure ENNReal.ofReal_ne_top
    rw [integral_add_measure hw_int0 hsm_w, integral_smul_measure, ENNReal.toReal_ofReal hr,
      smul_eq_mul]
    have h1 : ∫ t, wTilde src.w β₀ T₀ t ∂ν₀ ≤ C₀ - r * H := by
      have hof : ENNReal.ofReal (∫ t, wTilde src.w β₀ T₀ t ∂ν₀) =
          ∫⁻ t, ENNReal.ofReal (wTilde src.w β₀ T₀ t) ∂ν₀ :=
        ofReal_integral_eq_lintegral_ofReal hw_int0 (Eventually.of_forall fun t => (hwpos t).le)
      rw [← ENNReal.ofReal_le_ofReal_iff hC₀'.le, hof]
      exact hbud0
    have h2 : ∫ t, wTilde src.w β₀ T₀ t ∂σ ≤ H := by
      have h_eq : ∫ t, wTilde src.w β₀ T₀ t ∂σ = ∫ t, wStar src.w β₀ t ∂σ :=
        integral_congr_ae (ae_mem_of_null_src hσ |>.mono fun t ht => wTilde_of_le _ _ (hX ht))
      rw [h_eq]
      exact integral_mono_ae
        (hw_int_σ.congr (ae_mem_of_null_src hσ |>.mono fun t ht => wTilde_of_le _ _ (hX ht)))
        hh (ae_mem_of_null_src hσ |>.mono fun t ht => (S.lemma_M (hX ht)).2)
    nlinarith
  exact ⟨meas, hν_supp, meas_le_add_self ν₀ _, hw_meas, hbud_meas⟩

/-- Supremal reserve multiplier `r` for `r σ ≤ ν`. -/
noncomputable def reserveRatiosS (src : ShiftSource) (cTilde β₀ : ℝ) (X : Set ℝ)
    (σ : Measure ℝ) : Set ℝ :=
  {x : ℝ | ∃ (l : ℝ →₀ ℝ) (μ : ℝ), (∀ β ∈ l.support, 0 < β) ∧ 0 ≤ μ ∧
    (∀ t ∈ X, 0 ≤ spanTestS src l μ (cTilde / 12) β₀ t) ∧
    0 < ∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂σ ∧
    x = -src.gVac (cTilde / 12) (spanTestS src l μ (cTilde / 12) β₀) /
      ∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂σ}

noncomputable def reserveMaxS (src : ShiftSource) (cTilde β₀ : ℝ) (X : Set ℝ)
    (σ : Measure ℝ) : ℝ :=
  sInf (reserveRatiosS src cTilde β₀ X σ)

/-- **Theorem E(c) (`ds:E`(c))**: the supremal reserve multiplier `reserveMaxS` is attained by a
crossing measure `meas` on `X` (`ENNReal.ofReal R • σ ≤ meas.ν`). -/
theorem theorem_E_c_reserve_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) (hcb : CrossingBounds src (cTilde / 12))
    {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀) {σ : Measure ℝ}
    [IsFiniteMeasureOnCompacts σ] (hσ : σ Xᶜ = 0)
    (hh : Integrable (hMaj src.w (cTilde / 12) β₀) σ)
    (hHpos : 0 < ∫ t, hMaj src.w (cTilde / 12) β₀ t ∂σ)
    (hcross : ∃ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν Xᶜ = 0) :
    IsGreatest {r : ℝ | 0 ≤ r ∧ ∃ meas : SourceCrossingMeasure src (cTilde / 12),
        meas.ν Xᶜ = 0 ∧ ENNReal.ofReal r • σ ≤ meas.ν} (reserveMaxS src cTilde β₀ X σ) ∧
      reserveMaxS src cTilde β₀ X σ ≤
        dualC0S src (cTilde / 12) β₀ / ∫ t, hMaj src.w (cTilde / 12) β₀ t ∂σ := by
  classical
  have hC₀ : 0 < dualC0S src (cTilde / 12) β₀ := S.C₀_pos
  set C₀ := dualC0S src (cTilde / 12) β₀ with hC₀def
  set H := ∫ t, hMaj src.w (cTilde / 12) β₀ t ∂σ with hHdef
  obtain ⟨meas0, hν0⟩ := hcross
  set R := reserveMaxS src cTilde β₀ X σ with hRdef
  have hxh : C₀ / H ∈ reserveRatiosS src cTilde β₀ X σ := by
    refine ⟨0, 1, by simp, zero_le_one, ?_, ?_, ?_⟩
    · intro t ht
      have := (S.lemma_M (hX ht)).1.le.trans (S.lemma_M (hX ht)).2
      unfold spanTestS; simpa using this
    · unfold spanTestS; simpa using hHpos
    · unfold spanTestS
      have h0 : (fun t => (∑ β ∈ (0 : ℝ →₀ ℝ).support, (0 : ℝ →₀ ℝ) β * thermalDiff src.w β t) +
          1 * hMaj src.w (cTilde / 12) β₀ t) = hMaj src.w (cTilde / 12) β₀ := by ext t; simp
      rw [h0]
      change -src.gVac (cTilde / 12) (hMaj src.w (cTilde / 12) β₀) / H = C₀ / H
      rfl
  have hne : (reserveRatiosS src cTilde β₀ X σ).Nonempty := ⟨_, hxh⟩
  have hnn_ratio : ∀ x ∈ reserveRatiosS src cTilde β₀ X σ, 0 ≤ x := by
    rintro x ⟨l, μ, hl, _, hg, hpos, rfl⟩
    exact div_nonneg (neg_nonneg.2 (noSpanFeasibleS_of_crossingMeasure src S hcb meas0 hν0 l μ hl hg))
      hpos.le
  have hbdd : BddBelow (reserveRatiosS src cTilde β₀ X σ) := ⟨0, hnn_ratio⟩
  have hR0 : 0 ≤ R := le_csInf hne hnn_ratio
  have hRle : R ≤ C₀ / H := csInf_le hbdd hxh
  refine ⟨⟨⟨hR0, ?_⟩, ?_⟩, hRle⟩
  · have hRH : R * H ≤ C₀ := by
      have := mul_le_mul_of_nonneg_right hRle hHpos.le
      rwa [div_mul_cancel₀ _ hHpos.ne'] at this
    let r : ℕ → ℝ := fun n => R - R / ((n : ℝ) + 1)
    have hr_le : ∀ n, r n ≤ R := fun n => by
      have : 0 ≤ R / ((n : ℝ) + 1) := div_nonneg hR0 (by positivity)
      show R - R / ((n : ℝ) + 1) ≤ R; linarith
    have hr_nn : ∀ n, 0 ≤ r n := fun n => by
      have h1 : R / ((n : ℝ) + 1) ≤ R := div_le_self hR0 (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      show 0 ≤ R - R / ((n : ℝ) + 1); linarith
    have hr_bud : ∀ n, r n * H < C₀ := fun n => by
      rcases hR0.eq_or_lt with h0 | h0
      · have : r n = 0 := le_antisymm (h0 ▸ hr_le n) (hr_nn n)
        rw [this]; linarith
      · have hn : 0 < R / ((n : ℝ) + 1) := div_pos h0 (by positivity)
        have hlt : r n < R := by show R - R / ((n : ℝ) + 1) < R; linarith
        nlinarith [mul_lt_mul_of_pos_right hlt hHpos]
    have hsep : ∀ n, ∃ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν Xᶜ = 0 ∧
        ENNReal.ofReal (r n) • σ ≤ meas.ν := fun n => by
      obtain ⟨meas, h1, h2, -⟩ := theorem_E_c_separation_src src S hXc hX hσ hh (hr_nn n)
        (hr_bud n) fun l μ hl hμ hg => by
          have h0 : 0 ≤ ∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂σ :=
            integral_nonneg_of_ae (ae_mem_of_null_src hσ |>.mono fun t ht => hg t ht)
          rcases h0.eq_or_lt with hz | hpos
          · rw [← hz, mul_zero]
            exact neg_nonneg.2 (noSpanFeasibleS_of_crossingMeasure src S hcb meas0 hν0 l μ hl hg)
          · have hmem : -src.gVac (cTilde / 12) (spanTestS src l μ (cTilde / 12) β₀) /
                ∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂σ ∈
                reserveRatiosS src cTilde β₀ X σ := ⟨l, μ, hl, hμ, hg, hpos, rfl⟩
            have h1' : R ≤ -src.gVac (cTilde / 12) (spanTestS src l μ (cTilde / 12) β₀) /
                ∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂σ := csInf_le hbdd hmem
            rw [le_div_iff₀ hpos] at h1'
            nlinarith [mul_le_mul_of_nonneg_right (hr_le n) hpos.le]
      exact ⟨meas, h1, h2⟩
    choose meas hmsupp hmdom using hsep
    let 𝒰 : Ultrafilter ℕ := Ultrafilter.of atTop
    have h𝒰 : (𝒰 : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
    obtain ⟨meas', hlim, hsupp', -, -⟩ := theorem_E_a_compactness_src src S hcb (X := fun _ => X)
      (fun _ => hXc) (fun _ _ _ => le_rfl) hX meas hmsupp 𝒰 h𝒰
    simp only [iInter_const] at hsupp'
    haveI : ∀ j, IsFiniteMeasureOnCompacts (meas j).ν := fun j =>
      isFiniteMeasureOnCompacts_src src (meas j)
    haveI := isFiniteMeasureOnCompacts_src src meas'
    have hrt : Tendsto r atTop (𝓝 R) := by
      have h1 : Tendsto (fun n : ℕ => R / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv, mul_comm] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul R
      simpa using (tendsto_const_nhds (x := R)).sub h1
    exact ⟨meas', hsupp', hlim.smul_le (hrt.mono_left h𝒰) hr_nn hmdom⟩
  · rintro r ⟨_, meas, hν, hle⟩
    refine le_csInf hne ?_
    rintro x ⟨l, μ, hl, _, hg, hpos, rfl⟩
    obtain ⟨hint, heq⟩ := crossing_pairing_span_src src S hcb meas hl μ
    rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
      (ae_mem_of_null_src hν |>.mono fun t ht => S.hT₀.le.trans (hX ht))] at hint heq
    have hmono : r * ∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂σ ≤
        ∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂meas.ν := by
      have h1 := integral_mono_measure (le_trans hle le_rfl) (ae_mem_of_null_src hν |>.mono fun t ht => hg t ht) hint
      rw [integral_smul_measure, ENNReal.toReal_ofReal (by linarith : 0 ≤ r), smul_eq_mul] at h1
      exact h1
    rw [le_div_iff₀ hpos]
    linarith

/-- **Theorem E(c), reserve formula over the whole test class** (`ds:reserve-max`): if `X` contains
a terminal ray, `reserveMaxS` equals the infimum of `-g_vac / ∫⁻ g dσ` over all `g ∈ \overline{\mathcal A}`
nonnegative on `X` with `∫⁻ g dσ > 0`. -/
theorem theorem_E_c_reserve_testClass_src (src : ShiftSource) {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) (hcb : CrossingBounds src (cTilde / 12))
    {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀) (hray : ∃ τ, Ici τ ⊆ X)
    {σ : Measure ℝ} [IsFiniteMeasureOnCompacts σ] (hσ : σ Xᶜ = 0)
    (hh : Integrable (hMaj src.w (cTilde / 12) β₀) σ)
    (hHpos : 0 < ∫ t, hMaj src.w (cTilde / 12) β₀ t ∂σ)
    (hcross : ∃ meas : SourceCrossingMeasure src (cTilde / 12), meas.ν Xᶜ = 0) :
    ENNReal.ofReal (reserveMaxS src cTilde β₀ X σ) =
      ⨅ (g : ℝ → ℝ) (_ : TestClass src (cTilde / 12) g) (_ : ∀ t ∈ X, 0 ≤ g t)
        (_ : 0 < ∫⁻ t, ENNReal.ofReal (g t) ∂σ),
        ENNReal.ofReal (-src.gVac (cTilde / 12) g) / ∫⁻ t, ENNReal.ofReal (g t) ∂σ := by
  classical
  obtain ⟨⟨⟨hR0, meas, hν, hdom⟩, -⟩, -⟩ :=
    theorem_E_c_reserve_src src S hcb hXc hX hσ hh hHpos hcross
  obtain ⟨τ, hτ⟩ := hray
  set R := reserveMaxS src cTilde β₀ X σ with hRdef
  obtain ⟨meas0, hν0⟩ := hcross
  have hC₀ : 0 < dualC0S src (cTilde / 12) β₀ := S.C₀_pos
  set C₀ := dualC0S src (cTilde / 12) β₀
  set H := ∫ t, hMaj src.w (cTilde / 12) β₀ t ∂σ
  have hxh : C₀ / H ∈ reserveRatiosS src cTilde β₀ X σ := by
    refine ⟨0, 1, by simp, zero_le_one, ?_, ?_, ?_⟩
    · intro t ht
      have := (S.lemma_M (hX ht)).1.le.trans (S.lemma_M (hX ht)).2
      unfold spanTestS; simpa using this
    · unfold spanTestS; simpa using hHpos
    · unfold spanTestS
      have h0 : (fun t => (∑ β ∈ (0 : ℝ →₀ ℝ).support, (0 : ℝ →₀ ℝ) β * thermalDiff src.w β t) +
          1 * hMaj src.w (cTilde / 12) β₀ t) = hMaj src.w (cTilde / 12) β₀ := by ext t; simp
      rw [h0]
      change -src.gVac (cTilde / 12) (hMaj src.w (cTilde / 12) β₀) / H = C₀ / H
      rfl
  have hne : (reserveRatiosS src cTilde β₀ X σ).Nonempty := ⟨_, hxh⟩
  apply le_antisymm
  · refine le_iInf fun g => le_iInf fun hg => le_iInf fun hnn => le_iInf fun hL => ?_
    obtain ⟨hint, hle⟩ := lemma_fwX_one_sided_src src hcb S.ha0 meas hg
      (T := τ) fun t ht => hnn t (hτ ht)
    have hae0 : ∀ᵐ t ∂meas.ν, 0 ≤ t :=
      ae_mem_of_null_src hν |>.mono fun t ht => S.hT₀.le.trans (hX ht)
    rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae0] at hint hle
    have hae : ∀ᵐ t ∂meas.ν, 0 ≤ g t :=
      ae_mem_of_null_src hν |>.mono fun t ht => hnn t ht
    have h1 : ENNReal.ofReal (∫ t, g t ∂meas.ν) = ∫⁻ t, ENNReal.ofReal (g t) ∂meas.ν :=
      ofReal_integral_eq_lintegral_ofReal hint hae
    set L := ∫⁻ t, ENNReal.ofReal (g t) ∂σ with hLdef
    have h2 : ENNReal.ofReal R * L ≤ ENNReal.ofReal (-src.gVac (cTilde / 12) g) := by
      calc ENNReal.ofReal R * L = ∫⁻ t, ENNReal.ofReal (g t) ∂(ENNReal.ofReal R • σ) := by
            rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ ∫⁻ t, ENNReal.ofReal (g t) ∂meas.ν := lintegral_mono' hdom le_rfl
        _ = ENNReal.ofReal (∫ t, g t ∂meas.ν) := h1.symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
    by_cases hLtop : L = ⊤
    · have : ENNReal.ofReal R = 0 := by
        by_contra hne0
        rw [hLtop, ENNReal.mul_top hne0] at h2
        exact absurd (top_le_iff.1 h2) ENNReal.ofReal_ne_top
      rw [this]; exact zero_le
    · exact (ENNReal.le_div_iff_mul_le (Or.inl hL.ne') (Or.inl hLtop)).2 h2
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hlt : R < R + ε := by simpa using hε
    obtain ⟨x, hx, hxlt⟩ := exists_lt_of_csInf_lt hne hlt
    obtain ⟨l, μ, hl, _, hg, hpos, rfl⟩ := hx
    have hI := (integral_spanTestS_of_h S hX hσ hh hl μ).1
    have hL : ∫⁻ t, ENNReal.ofReal (spanTestS src l μ (cTilde / 12) β₀ t) ∂σ =
        ENNReal.ofReal (∫ t, spanTestS src l μ (cTilde / 12) β₀ t ∂σ) :=
      (ofReal_integral_eq_lintegral_ofReal hI (ae_mem_of_null_src hσ |>.mono fun t ht => hg t ht)).symm
    have hLpos : 0 < ∫⁻ t, ENNReal.ofReal (spanTestS src l μ (cTilde / 12) β₀ t) ∂σ := by
      rw [hL]; exact ENNReal.ofReal_pos.2 hpos
    refine le_trans (iInf_le _ (spanTestS src l μ (cTilde / 12) β₀))
      (le_trans (iInf_le _ (spanTestS_mem S.ha0 S.hβ₀ S.hnonneg S.hupper hl μ))
        (le_trans (iInf_le _ hg) (le_trans (iInf_le _ hLpos) ?_)))
    rw [hL, ← ENNReal.ofReal_div_of_pos hpos]
    calc _ ≤ ENNReal.ofReal (R + ε) := ENNReal.ofReal_le_ofReal hxlt.le
      _ = ENNReal.ofReal R + ε := by
          rw [ENNReal.ofReal_add hR0 (NNReal.coe_nonneg ε), ENNReal.ofReal_coe_nnreal]

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.theorem_E_a_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.theorem_E_a_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.theorem_E_b_compact_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.theorem_E_b_compact_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.theorem_E_c_reserve_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.theorem_E_c_reserve_src

end FormalResearch.ModularBootstrap.Mixtures
