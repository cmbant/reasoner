module

public import FormalResearch.ModularBootstrap.Spin.SpinDMP
public import FormalResearch.ModularBootstrap.Duality.VagueCompactness
public import FormalResearch.ModularBootstrap.Duality.OptimalMeasure
public import FormalResearch.ModularBootstrap.Duality.Coordinates
public import FormalResearch.ModularBootstrap.Duality.ConstrainedThreshold

/-!
# Theorem SD (`sd:SD`), general-cone strong duality & attainment, and unconditional `sd:LP`

Proves unconditionally:
- `spin_crossing_measure_compactness`: vague compactness of spinning crossing measures on a
  decreasing sequence of closed subsets of `E_B ∩ {t_L + t_R ≥ T₀}` (`T₀ > 0`), using the
  majorant budget `SpinDM` + `SpinDP` and `Duality.exists_vagueLimitAlong`.
- `spinDSD_cone`: Conjunct 1 of `SpinDSD` (`sd:SD`, `spinning_dual.tex`) — for `a ≥ 2`, `B ≥ 0`,
  closed swap-invariant `Ω ⊆ E_B`, compact swap-invariant `F ⊆ Ω ∩ {t_L + t_R > 0}`, with
  `T := spinCertifiedThr a Ω F > 0`:
  1. `T = max {τ > 0 : ∃ crossing measure on F ∪ Ω(τ)}` (`IsGreatest`);
  2. the maximum is attained by a swap-invariant crossing measure on `F ∪ Ω(T)`;
  3. scalar comparison `T ≤ constrainedThreshold virasoroProblem (12 * a) ((t_L + t_R) '' F)`.
- `spinDLPii : SpinDLPii` and `spinDLP : SpinDLP`: unconditional proof of Theorem SD-LP
  (`sd:LP` parts (i) and (ii)).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight

/-! ### Section 1: Swap-symmetrisation of a crossing measure -/

private lemma spin_thermalX_integrable_of_meas {a B : ℝ} (hB : 0 ≤ B) {X : Set (ℝ × ℝ)}
    (hXB : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X)
    {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    Integrable (fun p : ℝ × ℝ => spinThermalX βL βR p.1 p.2) meas.ν := by
  have hjoint : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR →
      Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (γL * p.1 + γR * p.2))) meas.ν := by
    intro γL γR hL hR
    have hνB : meas.ν (spinConeB B)ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr hXB) meas.supp
    have hae : ∀ᵐ p ∂meas.ν, p ∈ spinConeB B := by
      have : ∀ᵐ p ∂meas.ν, p ∉ (spinConeB B)ᶜ := measure_eq_zero_iff_ae_notMem.1 hνB
      filter_upwards [this] with p hp using not_not.mp hp
    refine Integrable.mono'
      ((meas.finite_laplace (lt_min hL hR)).const_mul
        (Real.exp (2 * π * B * (γL + γR - 2 * min γL γR))))
      (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (-2 * π * (γL * p.1 + γR * p.2))).aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact spin_exp_dom_coneB hB hp
  have h1 := hjoint hβL hβR
  have h2 := (hjoint (inv_pos.mpr hβL) (inv_pos.mpr hβR)).const_mul ((βL * βR) ^ (-(1 / 2 : ℝ)))
  refine (h1.sub h2).congr (Eventually.of_forall fun p => ?_)
  dsimp only [Pi.sub_apply]
  unfold spinThermalX; simp only [div_eq_inv_mul]

/-- Averaging a crossing measure on a swap-invariant set `X ⊆ E_B` with its swap push-forward
yields a swap-invariant crossing measure on `X`. -/
theorem spin_symmetrize_crossingMeasure {a B : ℝ} (hB : 0 ≤ B) {X : Set (ℝ × ℝ)}
    (hXs : IsSwapInvariantSet X) (hXB : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X) :
    ∃ m : SpinCrossingMeasureOn a X, IsSwapInvariantMeasure m.ν := by
  let νs : Measure (ℝ × ℝ) := (ENNReal.ofReal (1 / 2 : ℝ)) • (meas.ν + meas.ν.map Prod.swap)
  have hpreX : Prod.swap ⁻¹' Xᶜ = Xᶜ := by
    ext p
    simp only [mem_preimage, mem_compl_iff]
    constructor
    · intro h hp; exact h (hXs p hp)
    · intro h hp; exact h (by simpa using hXs p.swap hp)
  have hswap_supp : (meas.ν.map Prod.swap) Xᶜ = 0 := by
    have hmap : meas.ν.map Prod.swap = meas.ν.map (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) := rfl
    rw [hmap, MeasurableEquiv.map_apply]
    change meas.ν (Prod.swap ⁻¹' Xᶜ) = 0
    rw [hpreX]; exact meas.supp
  have hνs_supp : νs Xᶜ = 0 := by
    simp [νs, meas.supp, hswap_supp]
  have hνs_swap : IsSwapInvariantMeasure νs := by
    unfold IsSwapInvariantMeasure νs
    rw [Measure.map_smul, Measure.map_add _ _ measurable_swap,
        Measure.map_map measurable_swap measurable_swap]
    · have hcomp : Prod.swap ∘ (Prod.swap : ℝ × ℝ → ℝ × ℝ) = id := by ext ⟨x, y⟩ <;> rfl
      rw [hcomp, Measure.map_id, add_comm]
    · exact measurable_swap.aemeasurable
  have hνs_lap : ∀ {β : ℝ}, 0 < β →
      Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) νs := by
    intro β hβ
    have h1 := meas.finite_laplace hβ
    have h2 : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) (meas.ν.map Prod.swap) := by
      rw [integrable_map_measure (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (-2 * π * β * (p.1 + p.2))).aestronglyMeasurable measurable_swap.aemeasurable]
      refine h1.congr (Eventually.of_forall fun p => ?_)
      simp [add_comm]
    exact (h1.add_measure h2).smul_measure ENNReal.ofReal_ne_top
  have hνs_cross : ∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
      ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂νs = -spinThermalXVac a βL βR := by
    intro βL βR hβL hβR
    have hcont : Continuous (fun p : ℝ × ℝ => spinThermalX βL βR p.1 p.2) := by
      unfold spinThermalX; fun_prop
    have h1 := spin_thermalX_integrable_of_meas hB hXB meas hβL hβR
    have h1_sw := spin_thermalX_integrable_of_meas hB hXB meas hβR hβL
    have h2 : Integrable (fun p : ℝ × ℝ => spinThermalX βL βR p.1 p.2) (meas.ν.map Prod.swap) := by
      rw [integrable_map_measure hcont.aestronglyMeasurable measurable_swap.aemeasurable]
      refine h1_sw.congr (Eventually.of_forall fun p => ?_)
      dsimp [Function.comp, Prod.swap, spinThermalX]
      rw [mul_comm βR βL]
      ring_nf
    have hint_sw : ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂(meas.ν.map Prod.swap) =
        -spinThermalXVac a βL βR := by
      rw [integral_map measurable_swap.aemeasurable hcont.aestronglyMeasurable]
      have heq : (fun p : ℝ × ℝ => spinThermalX βL βR p.swap.1 p.swap.2) =
          fun p => spinThermalX βR βL p.1 p.2 := by
        ext p; dsimp [Prod.swap, spinThermalX]; rw [mul_comm βL βR]; ring_nf
      rw [heq, meas.crossing hβR hβL]
      unfold spinThermalXVac spinVacuumV
      rw [mul_comm βR βL]; ring
    unfold νs
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul,
        integral_add_measure h1 h2, meas.crossing hβL hβR, hint_sw]
    ring
  exact ⟨⟨νs, hνs_supp, hνs_lap, hνs_cross⟩, hνs_swap⟩

/-! ### Section 2: Vague compactness of spinning crossing measures -/

/-- Vague compactness of spinning crossing measures on a decreasing sequence of closed subsets
`X j ⊆ E_B ∩ {t_L + t_R ≥ T₀}` (`T₀ > 0`), using `SpinDM` + `SpinDP` and
`Duality.exists_vagueLimitAlong`. -/
theorem spin_crossing_measure_compactness {a B T₀ : ℝ} (ha : 2 ≤ a) (hB : 0 ≤ B) (hT₀ : 0 < T₀)
    {X : ℕ → Set (ℝ × ℝ)} (hXc : ∀ j, IsClosed (X j)) (hXa : Antitone X)
    (hX0 : X 0 ⊆ spinConeB B ∩ {p : ℝ × ℝ | T₀ ≤ p.1 + p.2})
    (meas : ∀ j, SpinCrossingMeasureOn a (X j)) :
    Nonempty (SpinCrossingMeasureOn a (⋂ j, X j)) := by
  obtain ⟨β₀, hβ₀, hβ₀2, ht0⟩ := Duality.exists_beta0 hT₀
  have hM1 := (spinDM ha).1 hT₀ hβ₀ hβ₀2 ht0
  have hM3 := (spinDM ha).2.2 hβ₀ hβ₀2 hB
  set C₀ : ℝ := dualC0 a β₀ with hC₀def
  have hC₀_pos : 0 < C₀ := hM1.2.2.2.1
  let w : ℝ × ℝ → ℝ := fun p => wStar a β₀ (max (p.1 + p.2) 0)
  have hw_cont : Continuous w :=
    (continuousOn_wStar (by linarith)).comp_continuous
      ((continuous_fst.add continuous_snd).max continuous_const) (fun _ => le_max_right _ _)
  have hw_pos : ∀ p : ℝ × ℝ, 0 < w p := fun p => wStar_pos (by linarith) hβ₀ (le_max_right _ _)
  have hw_nn : ∀ p : ℝ × ℝ, 0 ≤ w p := fun p => (hw_pos p).le
  set Z : Set (ℝ × ℝ) := spinConeB B ∩ {p : ℝ × ℝ | T₀ ≤ p.1 + p.2} with hZdef
  have hXjZ : ∀ j, X j ⊆ Z := fun j => (hXa (Nat.zero_le j)).trans hX0
  -- Uniform `w`-budget on every `(meas j).ν` via `SpinDP` applied to `Φ_h`
  have hbudget : ∀ j, ∫⁻ p, ENNReal.ofReal (w p) ∂(meas j).ν ≤ ENNReal.ofReal C₀ := by
    intro j
    let Φh : ℝ × ℝ → ℝ := fun p => hMaj a β₀ (p.1 + p.2)
    have hΦh_mem : SpinCertifiedT a Φh :=
      Submodule.subset_span (Or.inr ⟨β₀, hβ₀, hβ₀2, rfl⟩)
    obtain ⟨hΦh_int, hΦh_eq⟩ := (spinDP ha hB hT₀ (hXjZ j) (meas j)).1 Φh hΦh_mem
    have hvac_eq : spinVacT a Φh = -C₀ := by
      have hlift : spinLiftTToR Φh = spinRadialLift (hMaj a β₀) := by
        ext r; unfold spinLiftTToR spinRadialLift Φh
        rw [show r.1 ^ 2 / 2 + r.2 ^ 2 / 2 = (r.1 ^ 2 + r.2 ^ 2) / 2 by ring]
      unfold spinVacT; rw [hlift]; exact hM1.2.2.1
    have hΦh_int_eq : ∫ p, Φh p ∂(meas j).ν = C₀ := by rw [hΦh_eq, hvac_eq, neg_neg]
    have hae_X : ∀ᵐ p ∂(meas j).ν, p ∈ X j := by
      have : ∀ᵐ p ∂(meas j).ν, p ∉ (X j)ᶜ := measure_eq_zero_iff_ae_notMem.1 (meas j).supp
      filter_upwards [this] with p hp using not_not.mp hp
    have hle_ae : ∀ᵐ p ∂(meas j).ν, ENNReal.ofReal (w p) ≤ ENNReal.ofReal (Φh p) := by
      filter_upwards [hae_X] with p hp
      have hpT₀ : T₀ ≤ p.1 + p.2 := (hXjZ j hp).2
      have hmax : max (p.1 + p.2) 0 = p.1 + p.2 := max_eq_left (hT₀.le.trans hpT₀)
      refine ENNReal.ofReal_le_ofReal ?_
      dsimp only [w, Φh]; rw [hmax]
      exact (hM1.2.2.2.2 p.1 p.2 hpT₀).2
    have hΦh_nn : ∀ᵐ p ∂(meas j).ν, 0 ≤ Φh p := by
      filter_upwards [hae_X] with p hp
      have hpT₀ : T₀ ≤ p.1 + p.2 := (hXjZ j hp).2
      exact (hM1.2.2.2.2 p.1 p.2 hpT₀).1.le.trans (hM1.2.2.2.2 p.1 p.2 hpT₀).2
    calc ∫⁻ p, ENNReal.ofReal (w p) ∂(meas j).ν
        ≤ ∫⁻ p, ENNReal.ofReal (Φh p) ∂(meas j).ν := lintegral_mono_ae hle_ae
      _ = ENNReal.ofReal (∫ p, Φh p ∂(meas j).ν) :=
          (ofReal_integral_eq_lintegral_ofReal hΦh_int hΦh_nn).symm
      _ = ENNReal.ofReal C₀ := by rw [hΦh_int_eq]
  -- Uniform compact-set mass bound and local finiteness
  have hcomp_bound : ∀ K : Set (ℝ × ℝ), IsCompact K →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ j, (meas j).ν K ≤ ENNReal.ofReal M := by
    intro K hK
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact ⟨0, le_rfl, fun j => by simp⟩
    · obtain ⟨p₀, hp₀K, hp₀min⟩ := hK.exists_isMinOn hKne hw_cont.continuousOn
      have hc_pos : 0 < w p₀ := hw_pos p₀
      refine ⟨C₀ / w p₀, by positivity, fun j => ?_⟩
      have h1 : ENNReal.ofReal (w p₀) * (meas j).ν K ≤ ∫⁻ p, ENNReal.ofReal (w p) ∂(meas j).ν := by
        calc ENNReal.ofReal (w p₀) * (meas j).ν K
            = ∫⁻ _ in K, ENNReal.ofReal (w p₀) ∂(meas j).ν := by rw [setLIntegral_const]
          _ ≤ ∫⁻ p in K, ENNReal.ofReal (w p) ∂(meas j).ν :=
              setLIntegral_mono' hK.isClosed.measurableSet fun p hp =>
                ENNReal.ofReal_le_ofReal (isMinOn_iff.1 hp₀min p hp)
          _ ≤ ∫⁻ p, ENNReal.ofReal (w p) ∂(meas j).ν := setLIntegral_le_lintegral _ _
      have h2 : ENNReal.ofReal (w p₀) * (meas j).ν K ≤ ENNReal.ofReal C₀ := h1.trans (hbudget j)
      rw [ENNReal.ofReal_div_of_pos hc_pos,
          ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hc_pos)) (Or.inl ENNReal.ofReal_ne_top),
          mul_comm]
      exact h2
  let _ : ∀ j, IsFiniteMeasureOnCompacts (meas j).ν := fun j =>
    ⟨fun K hK => by
      obtain ⟨M, -, hM⟩ := hcomp_bound K hK
      exact lt_of_le_of_lt (hM j) ENNReal.ofReal_lt_top⟩
  have hbd : ∀ K : Set (ℝ × ℝ), IsCompact K → ∃ M : ℝ, ∀ j, ((meas j).ν K).toReal ≤ M := by
    intro K hK
    obtain ⟨M, hM0, hM⟩ := hcomp_bound K hK
    refine ⟨M, fun j => ?_⟩
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hM j)).trans_eq (ENNReal.toReal_ofReal hM0)
  -- Extract vague limit along an ultrafilter refining `atTop`
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of atTop
  have h𝒰_le : (𝒰 : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨ν, hνfin, hνlim⟩ := exists_vagueLimitAlong (fun j => (meas j).ν) hbd 𝒰
  -- Support on `⋂ j, X j`
  have hν_Xn : ∀ n : ℕ, ν (X n)ᶜ = 0 := by
    intro n
    refine hνlim.measure_open_eq_zero (hXc n).isOpen_compl ?_
    refine h𝒰_le (eventually_atTop.mpr ⟨n, fun j hj => ?_⟩)
    exact measure_mono_null (compl_subset_compl.mpr (hXa hj)) (meas j).supp
  have hν_supp : ν (⋂ j, X j)ᶜ = 0 := by
    rw [compl_iInter]
    exact measure_iUnion_null hν_Xn
  have hνZ : ν Zᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr ((iInter_subset X 0).trans hX0)) hν_supp
  -- Weighted budget passes to `ν`
  have hbν : ∫⁻ p, ENNReal.ofReal (w p) ∂ν ≤ ENNReal.ofReal C₀ :=
    hνlim.lintegral_le hw_cont hw_nn hC₀_pos.le (Eventually.of_forall hbudget)
  -- Decay helper for exponentially bounded functions on `Z`
  have hdecay_exp : ∀ {m Cf : ℝ}, 0 < m → 0 ≤ Cf → ∀ {f : ℝ × ℝ → ℝ},
      (∀ p ∈ spinConeB B, |f p| ≤ Cf * Real.exp (-2 * π * m * (p.1 + p.2))) →
      ∀ ε > 0, ∃ K : Set (ℝ × ℝ), IsCompact K ∧ ∀ p ∈ Z, p ∉ K → |f p| ≤ ε * w p := by
    intro m Cf hm hCf f hf ε hε
    have htend := (hM3.1 hm).2
    have hδ : 0 < ε / (Cf + 1) := by positivity
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (htend.eventually (Metric.ball_mem_nhds 0 hδ))
    set R : ℝ := max R₀ T₀ with hR
    refine ⟨Icc (-B) (R + B) ×ˢ Icc (-B) (R + B), isCompact_Icc.prod isCompact_Icc, fun p hpZ hpK => ?_⟩
    have hpR : R ≤ p.1 + p.2 := by
      by_contra hlt
      push Not at hlt
      apply hpK
      exact ⟨⟨hpZ.1.1, by linarith [hpZ.1.2]⟩, ⟨hpZ.1.2, by linarith [hpZ.1.1]⟩⟩
    have h1 := hR₀ (p.1 + p.2) ((le_max_left R₀ T₀).trans hpR)
    rw [Real.dist_eq, sub_zero,
        abs_of_pos (div_pos (Real.exp_pos _) (wStar_pos (by linarith) hβ₀ (hT₀.le.trans hpZ.2)))] at h1
    have hw_eq : w p = wStar a β₀ (p.1 + p.2) := by
      dsimp only [w]; rw [max_eq_left (hT₀.le.trans hpZ.2)]
    have hw_p_pos : 0 < w p := hw_pos p
    have h2 : Real.exp (-2 * π * m * (p.1 + p.2)) ≤ (ε / (Cf + 1)) * w p := by
      rw [hw_eq]
      exact (div_le_iff₀ (wStar_pos (by linarith) hβ₀ (hT₀.le.trans hpZ.2))).mp h1.le
    calc |f p| ≤ Cf * Real.exp (-2 * π * m * (p.1 + p.2)) := hf p hpZ.1
      _ ≤ Cf * ((ε / (Cf + 1)) * w p) := mul_le_mul_of_nonneg_left h2 hCf
      _ = (Cf / (Cf + 1)) * (ε * w p) := by ring
      _ ≤ 1 * (ε * w p) := by
          gcongr
          exact (div_le_one (by linarith)).mpr (by linarith)
      _ = ε * w p := one_mul _
  -- Diagonal Laplace integrability on `ν`
  have hν_lap : ∀ {β : ℝ}, 0 < β →
      Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν := by
    intro β hβ
    refine integrable_of_decay hνZ hw_cont hw_nn (lt_of_le_of_lt hbν ENNReal.ofReal_lt_top)
      (by fun_prop) ?_
    obtain ⟨K, hK, hKd⟩ := hdecay_exp hβ zero_le_one
      (f := fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2)))
      (fun p _ => by rw [abs_of_pos (Real.exp_pos _), one_mul]) 1 one_pos
    exact ⟨K, hK, fun p hpZ hpK => by simpa using hKd p hpZ hpK⟩
  -- Crossing on `ν`
  have hν_cross : ∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
      ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν = -spinThermalXVac a βL βR := by
    intro βL βR hβL hβR
    obtain ⟨C, hC⟩ := hM3.2 hβL hβR
    have hm_pos : 0 < min (min βL βR) (min βL⁻¹ βR⁻¹) :=
      lt_min (lt_min hβL hβR) (lt_min (inv_pos.mpr hβL) (inv_pos.mpr hβR))
    have hCf_nn : 0 ≤ max C 0 := le_max_right _ _
    have hcont : Continuous (fun p : ℝ × ℝ => spinThermalX βL βR p.1 p.2) := by
      unfold spinThermalX; fun_prop
    have hμZ : ∀ᶠ j in (𝒰 : Filter ℕ), (meas j).ν Zᶜ = 0 :=
      Eventually.of_forall fun j => measure_mono_null (compl_subset_compl.mpr (hXjZ j)) (meas j).supp
    have hlim := hνlim.tendsto_integral hμZ hνZ hw_cont hw_nn hC₀_pos.le
      (Eventually.of_forall hbudget) hbν hcont (hdecay_exp hm_pos hCf_nn fun p hp =>
        (hC p hp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
    have hconst : Tendsto (fun j => ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂(meas j).ν)
        (𝒰 : Filter ℕ) (𝓝 (-spinThermalXVac a βL βR)) := by
      simp_rw [(meas _).crossing hβL hβR]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  exact ⟨⟨ν, hν_supp, hν_lap, hν_cross⟩⟩

/-! ### Section 3: Theorem SD (`sd:SD`), general-cone strong duality, attainment & scalar comparison -/

/-- **Theorem SD (`sd:SD`), Conjunct 1 (unconditional)**: for `a ≥ 2`, `B ≥ 0`, closed
swap-invariant `Ω ⊆ E_B`, compact swap-invariant `F ⊆ Ω ∩ {t_L + t_R > 0}`, with
`T := spinCertifiedThr a Ω F > 0`:
1. `T = max {τ > 0 : ∃ crossing measure on F ∪ Ω(τ)}` (`IsGreatest`);
2. the maximum is attained by a swap-invariant crossing measure on `F ∪ Ω(T)`;
3. scalar comparison `T ≤ constrainedThreshold virasoroProblem (12 * a) ((t_L + t_R) '' F)`. -/
theorem spinDSD_cone {a B : ℝ} (ha : 2 ≤ a) (hB : 0 ≤ B)
    {Ω F : Set (ℝ × ℝ)} (hΩc : IsClosed Ω) (hΩs : IsSwapInvariantSet Ω) (hΩB : Ω ⊆ spinConeB B)
    (hFc : IsCompact F) (hFs : IsSwapInvariantSet F) (hFsub : F ⊆ Ω ∩ {p : ℝ × ℝ | 0 < p.1 + p.2})
    (hTpos : 0 < spinCertifiedThr a Ω F) :
    IsGreatest {τ : ℝ | 0 < τ ∧ Nonempty (SpinCrossingMeasureOn a (F ∪ spinConeSlice Ω τ))}
      (spinCertifiedThr a Ω F) ∧
    (∃ meas : SpinCrossingMeasureOn a (F ∪ spinConeSlice Ω (spinCertifiedThr a Ω F)),
      IsSwapInvariantMeasure meas.ν) ∧
    spinCertifiedThr a Ω F ≤
      constrainedThreshold virasoroProblem (12 * a) ((fun p : ℝ × ℝ => p.1 + p.2) '' F) := by
  set T := spinCertifiedThr a Ω F with hTdef
  set S : Set ℝ := {T' : ℝ | 0 < T' ∧ ∃ Φ, SpinCertifiedT a Φ ∧ 0 < spinVacT a Φ ∧
    ∀ p ∈ F ∪ spinConeSlice Ω T', 0 ≤ Φ p} with hSdef
  have hSne : S.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : T = 0 := by rw [hTdef]; unfold spinCertifiedThr; rw [← hSdef, hemp, Real.sInf_empty]
    linarith
  have hm_ex : ∃ m : ℝ, 0 < m ∧ F ⊆ {p : ℝ × ℝ | m ≤ p.1 + p.2} := by
    rcases F.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, empty_subset _⟩
    · obtain ⟨p₀, hp₀F, hp₀min⟩ := hFc.exists_isMinOn hne
        (continuous_fst.add continuous_snd).continuousOn
      exact ⟨p₀.1 + p₀.2, (hFsub hp₀F).2, fun p hp => isMinOn_iff.1 hp₀min p hp⟩
  obtain ⟨m, hm_pos, hFm⟩ := hm_ex
  -- Part 1 (upper bound): every `τ > 0` carrying a crossing measure on `F ∪ Ω(τ)` has `τ ≤ T`
  have hupper : ∀ τ ∈ {τ : ℝ | 0 < τ ∧ Nonempty (SpinCrossingMeasureOn a (F ∪ spinConeSlice Ω τ))},
      τ ≤ T := by
    rintro τ ⟨hτ0, ⟨meas⟩⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨T', hT'S, hT'τ⟩ := exists_lt_of_csInf_lt hSne hlt
    obtain ⟨-, Φ, hΦmem, hΦvac, hΦnn⟩ := hT'S
    have hXsub : F ∪ spinConeSlice Ω τ ⊆ spinConeB B ∩ {p : ℝ × ℝ | min m τ ≤ p.1 + p.2} := by
      rintro p (hpF | ⟨hpΩ, hpτ⟩)
      · exact ⟨hΩB (hFsub hpF).1, (min_le_left m τ).trans (hFm hpF)⟩
      · exact ⟨hΩB hpΩ, (min_le_right m τ).trans hpτ⟩
    have hpair := ((spinDP ha hB (lt_min hm_pos hτ0) hXsub meas).1 Φ hΦmem).2
    have hnn_int : 0 ≤ ∫ p, Φ p ∂meas.ν := by
      refine integral_nonneg_of_ae ?_
      have : ∀ᵐ p ∂meas.ν, p ∉ (F ∪ spinConeSlice Ω τ)ᶜ :=
        measure_eq_zero_iff_ae_notMem.1 meas.supp
      filter_upwards [this] with p hp
      rcases not_not.mp hp with hpF | ⟨hpΩ, hpτ⟩
      · exact hΦnn p (Or.inl hpF)
      · exact hΦnn p (Or.inr ⟨hpΩ, hT'τ.le.trans hpτ⟩)
    linarith
  -- Part 2 (attainment): construct a swap-invariant crossing measure on `F ∪ Ω(T)`
  set T₀ : ℝ := min m (T / 2) with hT₀def
  have hT₀_pos : 0 < T₀ := lt_min hm_pos (half_pos hTpos)
  have hT₀_lt : T₀ < T := (min_le_right m (T / 2)).trans_lt (half_lt_self hTpos)
  let Tseq : ℕ → ℝ := fun j => T - (T - T₀) / (j + 2)
  have hTseq_ge : ∀ j, T₀ ≤ Tseq j := fun j => by
    have h1 : (T - T₀) / ((j : ℝ) + 2) ≤ T - T₀ :=
      div_le_self (by linarith) (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    show T₀ ≤ T - (T - T₀) / (j + 2); linarith
  have hTseq_lt : ∀ j, Tseq j < T := fun j => by
    have h1 : 0 < (T - T₀) / ((j : ℝ) + 2) :=
      div_pos (by linarith) (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    show T - (T - T₀) / (j + 2) < T; linarith
  have hTseq_mono : Monotone Tseq := by
    refine monotone_nat_of_le_succ fun j => ?_
    show T - (T - T₀) / (j + 2) ≤ T - (T - T₀) / ((j + 1 : ℕ) + 2)
    have h1 : (T - T₀) / (((j + 1 : ℕ) : ℝ) + 2) ≤ (T - T₀) / ((j : ℝ) + 2) := by
      refine div_le_div_of_nonneg_left (by linarith)
        (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith) ?_
      push_cast; linarith
    linarith
  let Xseq : ℕ → Set (ℝ × ℝ) := fun j => F ∪ spinConeSlice Ω (Tseq j)
  have hXc : ∀ j, IsClosed (Xseq j) := fun j => hFc.isClosed.union (isClosed_spinConeSlice hΩc (Tseq j))
  have hXs : ∀ j, IsSwapInvariantSet (Xseq j) := by
    intro j p hp
    rcases hp with hpF | hpΩ
    · exact Or.inl (hFs p hpF)
    · exact Or.inr (isSwapInvariantSet_spinConeSlice hΩs (Tseq j) p hpΩ)
  have hXa : Antitone Xseq := fun i j hij =>
    union_subset_union_right F fun p ⟨hpΩ, hpT⟩ => ⟨hpΩ, (hTseq_mono hij).trans hpT⟩
  have hX0 : Xseq 0 ⊆ spinConeB B ∩ {p : ℝ × ℝ | T₀ ≤ p.1 + p.2} := by
    rintro p (hpF | ⟨hpΩ, hpT⟩)
    · exact ⟨hΩB (hFsub hpF).1, (min_le_left m (T / 2)).trans (hFm hpF)⟩
    · exact ⟨hΩB hpΩ, (hTseq_ge 0).trans hpT⟩
  have hex_j : ∀ j, ∃ meas : SpinCrossingMeasureOn a (Xseq j), IsSwapInvariantMeasure meas.ν := by
    intro j
    refine (spinDLPi ha hB hT₀_pos (hXc j) (hXs j) ((hXa (Nat.zero_le j)).trans hX0)).1 ?_
    rintro N q ⟨hq_mem, hq_nn, hq_vac⟩
    have hmemS : Tseq j ∈ S :=
      ⟨hT₀_pos.trans_le (hTseq_ge j), fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p,
        exp_mul_mem_SpinCertifiedT hq_mem, hq_vac, hq_nn⟩
    have hle : T ≤ Tseq j := csInf_le ⟨0, fun τ hτ => hτ.1.le⟩ hmemS
    linarith [hTseq_lt j]
  choose meas_j _ using hex_j
  obtain ⟨meas_raw⟩ := spin_crossing_measure_compactness ha hB hT₀_pos hXc hXa hX0 meas_j
  have hInter : (⋂ j, Xseq j) = F ∪ spinConeSlice Ω T := by
    refine Subset.antisymm (fun p hp => ?_) (fun p hp => mem_iInter.2 fun j => ?_)
    · by_cases hpF : p ∈ F
      · exact Or.inl hpF
      · refine Or.inr ⟨?_, ?_⟩
        · rcases mem_iInter.1 hp 0 with h | h
          · exact absurd h hpF
          · exact h.1
        · have hall : ∀ j, Tseq j ≤ p.1 + p.2 := fun j => by
            rcases mem_iInter.1 hp j with h | h
            · exact absurd h hpF
            · exact h.2
          by_contra hlt
          have hlt' : p.1 + p.2 < T := lt_of_not_ge hlt
          obtain ⟨j, hj⟩ := exists_nat_gt ((T - T₀) / (T - (p.1 + p.2)))
          have hpos : 0 < T - (p.1 + p.2) := by linarith
          have h1 : (T - T₀) / ((j : ℝ) + 2) < T - (p.1 + p.2) := by
            rw [div_lt_iff₀ (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)]
            have := (div_lt_iff₀ hpos).mp hj
            nlinarith
          have h2 := hall j
          have : p.1 + p.2 < Tseq j := by show p.1 + p.2 < T - (T - T₀) / (j + 2); linarith
          linarith
    · rcases hp with hpF | ⟨hpΩ, hpT⟩
      · exact Or.inl hpF
      · exact Or.inr ⟨hpΩ, (hTseq_lt j).le.trans hpT⟩
  have hXT_swap : IsSwapInvariantSet (F ∪ spinConeSlice Ω T) := by
    rintro p (hpF | hpΩ)
    · exact Or.inl (hFs p hpF)
    · exact Or.inr (isSwapInvariantSet_spinConeSlice hΩs T p hpΩ)
  have hXT_B : F ∪ spinConeSlice Ω T ⊆ spinConeB B := by
    rintro p (hpF | ⟨hpΩ, -⟩)
    · exact hΩB (hFsub hpF).1
    · exact hΩB hpΩ
  have meas_on_XT : SpinCrossingMeasureOn a (F ∪ spinConeSlice Ω T) :=
    { ν := meas_raw.ν
      supp := by rw [← hInter]; exact meas_raw.supp
      finite_laplace := meas_raw.finite_laplace
      crossing := meas_raw.crossing }
  obtain ⟨meas_sym, hmeas_sym⟩ := spin_symmetrize_crossingMeasure hB hXT_swap hXT_B meas_on_XT
  -- Part 3 (scalar comparison): push `meas_sym` forward by `p ↦ p.1 + p.2`
  have hscalar : T ≤ constrainedThreshold virasoroProblem (12 * a) ((fun p : ℝ × ℝ => p.1 + p.2) '' F) := by
    set Frad : Set ℝ := (fun p : ℝ × ℝ => p.1 + p.2) '' F
    have hFrad_cpt : IsCompact Frad := hFc.image (continuous_fst.add continuous_snd)
    have hFrad_pos : Frad ⊆ Ioi 0 := by
      rintro _ ⟨p, hpF, rfl⟩
      exact (hFsub hpF).2
    have hc_pos : (0 : ℝ) < 12 * a := by linarith
    have hc_shift : 12 * virasoroProblem.totalShift ≤ 12 * a := by
      rw [virasoroProblem_totalShift]; linarith
    obtain ⟨τ₁, hτ₁, g₁, hg₁⟩ := exists_feasible_of_compact virasoroProblem hc_pos hc_shift hFrad_cpt hFrad_pos
    have hne : (constrainedGaps virasoroProblem (12 * a) Frad).Nonempty := ⟨τ₁, hτ₁, g₁, hg₁⟩
    have hXT_nn : F ∪ spinConeSlice Ω T ⊆ {p : ℝ × ℝ | 0 ≤ p.1 + p.2} := by
      rintro p (hpF | ⟨-, hpT⟩)
      · have hpos : 0 < p.1 + p.2 := (hFsub hpF).2
        exact hpos.le
      · exact hTpos.le.trans hpT
    let meas_12 : SpinCrossingMeasureOn (12 * a / 12) (F ∪ spinConeSlice Ω T) :=
      { ν := meas_sym.ν
        supp := meas_sym.supp
        finite_laplace := meas_sym.finite_laplace
        crossing := fun hL hR => by
          rw [show 12 * a / 12 = a by ring]
          exact meas_sym.crossing hL hR }
    let rad_meas : AdmissibleCrossingMeasure virasoroProblem (12 * a / 12) :=
      meas_12.toRadAdmissible hXT_nn
    have hrad_supp : rad_meas.ν (Frad ∪ Ici T)ᶜ = 0 := by
      change spinRadMarginal meas_sym.ν (Frad ∪ Ici T)ᶜ = 0
      unfold spinRadMarginal
      have hmeas_sum : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
      have hcl : MeasurableSet (Frad ∪ Ici T)ᶜ :=
        (hFrad_cpt.isClosed.union isClosed_Ici).measurableSet.compl
      rw [Measure.map_apply hmeas_sum hcl]
      have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Frad ∪ Ici T)ᶜ ⊆ (F ∪ spinConeSlice Ω T)ᶜ := by
        intro p hp hpXT
        apply hp
        rcases hpXT with hpF | ⟨-, hpT⟩
        · exact Or.inl ⟨p, hpF, rfl⟩
        · exact Or.inr hpT
      exact measure_mono_null hsub meas_sym.supp
    exact le_constrainedThreshold_of_crossingMeasure virasoroProblem hc_pos hc_shift hne rad_meas hrad_supp
  exact ⟨⟨⟨hTpos, ⟨meas_sym⟩⟩, hupper⟩, ⟨meas_sym, hmeas_sym⟩, hscalar⟩

/-! ### Section 4: Unconditional Theorem SD-LP (ii) and full `SpinDLP` -/

/-- **Theorem SD-LP (ii)** (`sd:LP`(ii), unconditional): `T_{Ω,F}^{[∞]} = T_{Ω,F}^{\mathcal B} = τ_{\max}`. -/
theorem spinDLPii : SpinDLPii := by
  intro a B ha hB Ω F hΩc hΩs hΩB hFc hFs hFsub hTpos
  obtain ⟨hmax, -, -⟩ := spinDSD_cone ha hB hΩc hΩs hΩB hFc hFs hFsub hTpos
  refine ⟨?_, hmax⟩
  set TB := spinCertifiedThr a Ω F with hTB
  have hge : ENNReal.ofReal TB ≤ spinLagThrInf a Ω F := by
    refine le_iInf fun N => le_iInf₂ fun T hT => ?_
    obtain ⟨hT0, q, hq_mem, hq_nn, hq_vac⟩ := hT
    refine ENNReal.ofReal_le_ofReal ?_
    refine csInf_le ⟨0, fun τ hτ => hτ.1.le⟩ ?_
    exact ⟨hT0, fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p,
      exp_mul_mem_SpinCertifiedT hq_mem, hq_vac, hq_nn⟩
  have hle : spinLagThrInf a Ω F ≤ ENNReal.ofReal TB := by
    by_contra hlt
    obtain ⟨T', hT'0, hT'1, hT'2⟩ := ENNReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    have hTB_lt : TB < T' := (ENNReal.ofReal_lt_ofReal_iff'.1 hT'1).1
    have hT'_pos : 0 < T' := hTpos.trans hTB_lt
    have hno : ∀ N q, ¬ spinOddLagFeasible a N (F ∪ spinConeSlice Ω T') q := by
      intro N q hq
      have hle' : spinLagThrInf a Ω F ≤ ENNReal.ofReal T' :=
        (iInf_le _ N).trans (iInf₂_le T' ⟨hT'_pos, q, hq⟩)
      exact absurd hle' (not_le.2 hT'2)
    have hm_ex : ∃ m : ℝ, 0 < m ∧ F ⊆ {p : ℝ × ℝ | m ≤ p.1 + p.2} := by
      rcases F.eq_empty_or_nonempty with rfl | hne
      · exact ⟨1, one_pos, empty_subset _⟩
      · obtain ⟨p₀, hp₀F, hp₀min⟩ := hFc.exists_isMinOn hne
          (continuous_fst.add continuous_snd).continuousOn
        exact ⟨p₀.1 + p₀.2, (hFsub hp₀F).2, fun p hp => isMinOn_iff.1 hp₀min p hp⟩
    obtain ⟨m, hm_pos, hFm⟩ := hm_ex
    set T₀ := min m T' with hT₀
    have hT₀_pos : 0 < T₀ := lt_min hm_pos hT'_pos
    have hXc : IsClosed (F ∪ spinConeSlice Ω T') :=
      hFc.isClosed.union (isClosed_spinConeSlice hΩc T')
    have hXs : IsSwapInvariantSet (F ∪ spinConeSlice Ω T') := by
      rintro p (hpF | hpΩ)
      · exact Or.inl (hFs p hpF)
      · exact Or.inr (isSwapInvariantSet_spinConeSlice hΩs T' p hpΩ)
    have hXsub : F ∪ spinConeSlice Ω T' ⊆ spinConeB B ∩ {p : ℝ × ℝ | T₀ ≤ p.1 + p.2} := by
      rintro p (hpF | ⟨hpΩ, hpT⟩)
      · exact ⟨hΩB (hFsub hpF).1, (min_le_left m T').trans (hFm hpF)⟩
      · exact ⟨hΩB hpΩ, (min_le_right m T').trans hpT⟩
    obtain ⟨meas, -⟩ := (spinDLPi ha hB hT₀_pos hXc hXs hXsub).1 hno
    have hT'_le : T' ≤ TB := hmax.2 ⟨hT'_pos, ⟨meas⟩⟩
    linarith
  exact le_antisymm hle hge

/-- **Theorem SD-LP** (`sd:LP`, unconditional): parts (i) and (ii) combined. -/
theorem spinDLP : SpinDLP := ⟨spinDLPi, spinDLPii⟩

/-! ### Axiom guards -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_crossing_measure_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_crossing_measure_compactness

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDSD_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDSD_cone

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDLPii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDLPii

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDLP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDLP

end FormalResearch.ModularBootstrap.Spin
