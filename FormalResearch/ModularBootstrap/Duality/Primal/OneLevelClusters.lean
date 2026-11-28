module

public import FormalResearch.ModularBootstrap.Duality.Primal.HbClustersTheorem
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpFinal

/-!
# Exact one-level Airy clusters (`dual_spectrum_limit.tex`, `dsl:one-level-clusters`)

Specializes `hb_clusters` (`Duality/Primal/HbClustersTheorem.lean`) to the canonical one-level
Hermite–Biehler datum `H = HermiteBiehlerData.airy` (`F_n = ∅`, `B_n = T_V(n)`), using:
* `FixedWeightBand.fixedWeightLowerBoundInput_of_problem` + `Upper.Ramped.theoremC15UpperInput_probW`
  for the `O(1)` threshold law `T_V(c̃) - T_*(c̃) = O(1)` (giving `uAiry (c n) (T_V (c n)) → a₁`);
* `Upper.Assembly.theorem_sigma_crossing`, `designPropertyP_probW`, `displacedPropertyP_probW`,
  `sameSiteFamily_designClass`, `displacedFamily`, `farFamily` for unconditional vague convergence
  of any near-optimal crossing sequence `ν_n` supported on `[T_V(c_n) - η_n, ∞)` (`η_n = o(c_n^{1/3})`)
  to `airyMeasure`.

Paper scope note: in `dual_spectrum_limit.tex` `dsl:one-level-clusters`(b), the offset `b_n` in
`dsl:d1-asym` is written as `c_0^*(w, Q)` at `(H_w)` (using `ctu:main`, package `FIVE-W`, not yet
formalized). Here we prove the unconditional `dsl:d1-asym` statement with
`b_n = T_V(c_n) - T_*(c_n)` together with `|b_n| ≤ B₀` (`O(1)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Duality FormalResearch.ModularBootstrap.WeightAxioms
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.ModularBootstrap.FixedWeightTip
  FormalResearch.ModularBootstrap.FixedWeightBand FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ArgPrinciple

/-! ### 1. `HbClusterData` for `HermiteBiehlerData.airy` -/

/-- The canonical Airy `HbNodes` type is empty because `HermiteBiehlerData.airy.S = {airyZero 1}`
and `HermiteBiehlerData.airy.tm = airyZero 1`. -/
lemma hbNodes_airy_isEmpty : IsEmpty (HbNodes HermiteBiehlerData.airy) :=
  ⟨fun i => i.2.2 (Finset.mem_singleton.mp i.2.1)⟩

@[simp] lemma hbPrescribedSet_airy_eq_empty (s : HbNodes HermiteBiehlerData.airy → ℕ → ℝ) (n : ℕ) :
    hbPrescribedSet s n = ∅ := by
  ext t
  simp only [hbPrescribedSet, Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨i, -⟩
  exact hbNodes_airy_isEmpty.false i

/-- Construct `HbClusterData HermiteBiehlerData.airy` for any `K ≥ 1` and isolating interval
`(a, b)` with `airyNode K < a < airyNode (K - 1)` and `airyNode 0 < b`. -/
noncomputable def airyHbClusterData (K : ℕ) (hK : 1 ≤ K) {a b : ℝ}
    (ha_lo : airyNode K < a) (ha_hi : a < airyNode (K - 1)) (hb : airyNode 0 < b) :
    HbClusterData HermiteBiehlerData.airy where
  K := K
  hK := hK
  z := fun k => airyNode k.1
  hz_anti := fun _ _ hlt => airyNode_strictAnti hlt
  hz_zero := fun k => by
    have h0 : airyProfile (airyNode k.1 : ℂ) = 0 :=
      (airyProfile_eq_zero_iff (airyNode k.1 : ℂ)).mpr ⟨k.1 + 1, by omega, rfl⟩
    unfold airyProfile normProfile at h0
    have hm : (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (inv_ne_zero airyExtremalProfile.mass_pos.ne')
    exact (mul_eq_zero.mp h0).resolve_left hm
  a := a
  b := b
  ha := ha_hi
  hb := hb
  hzero_win := fun w hw => by
    constructor
    · intro h0
      have hprof : airyProfile w = 0 := by
        simpa [airyProfile, HermiteBiehlerData.airy] using h0
      obtain ⟨j, hj, hj_eq⟩ := (airyProfile_eq_zero_iff w).mp hprof
      have hj_re : w.re = airyNode (j - 1) := by
        rw [hj_eq, Complex.ofReal_re]; unfold airyNode; congr 1; omega
      have hlt_K : j - 1 < K := by
        by_contra hge
        have hle : airyNode (j - 1) ≤ airyNode K := airyNode_strictAnti.antitone (not_lt.mp hge)
        linarith [hw.1, hj_re]
      refine ⟨⟨j - 1, hlt_K⟩, ?_⟩
      rw [hj_eq]
      exact congrArg Complex.ofReal (congrArg airyZero (by change j = (j - 1) + 1; omega))
    · rintro ⟨k, rfl⟩
      exact (airyProfile_eq_zero_iff (airyNode k.1 : ℂ)).mpr ⟨k.1 + 1, by omega, rfl⟩
  hord := fun k => by
    change analyticOrderNatAt airyProfile (airyNode k.1 : ℂ) =
      if airyNode k.1 ∈ HermiteBiehlerData.airy.S then 1 else 2
    by_cases hk0 : k.1 = 0
    · split_ifs with h
      · rw [hk0, airyNode_zero]; exact airyProfile_orderNat_one
      · exfalso; apply h; rw [hk0, airyNode_zero]; exact HermiteBiehlerData.airy.tm_mem
    · split_ifs with h
      · exfalso
        have heq := Finset.mem_singleton.mp h
        have hlt : airyNode k.1 < airyNode 0 := airyNode_strictAnti (Nat.pos_of_ne_zero hk0)
        rw [airyNode_zero] at hlt; linarith
      · have hk2 : 2 ≤ k.1 + 1 := by omega
        exact airyProfile_orderNat_node hk2
  hS_sub := fun i hi => ⟨⟨0, hK⟩, by
    have := Finset.mem_singleton.mp hi
    rw [this, airyNode_zero]⟩
  hS_top := fun k => by
    change airyNode k.1 ∈ ({airyZero 1} : Finset ℝ) ↔ airyZero 1 ≤ airyNode k.1
    rw [Finset.mem_singleton, ← airyNode_zero]
    constructor
    · intro h; rw [h]
    · intro h
      by_contra hne
      have hk0 : k.1 ≠ 0 := fun hk => hne (by rw [hk])
      have hlt := airyNode_strictAnti (Nat.pos_of_ne_zero hk0)
      linarith
  ω := fun k => airyNodeWeight k.1
  hω_pos := fun k => airyNodeWeight_pos k.1

/-! ### 2. Threshold `O(1)` law and unconditional vague convergence for near-optimal spectra -/

/-- `T_V(c_n) - T_*(c_n) = O(1)` for every `prob : FixedWeightProblem` and `c_n → ∞`, hence
`uAiry (c n) (T_V (c n)) → airyZero 1`. -/
lemma fixedWeight_T_V_sub_TStar_bounded (prob : FixedWeightProblem) :
    ∃ c₀ B₀ : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧ 0 < B₀ ∧
      ∀ {c : ℝ}, c₀ ≤ c → |prob.T_V c - TStar c| ≤ B₀ := by
  obtain ⟨c₁, D₁, hc₁, _, hlo⟩ := fixedWeightLowerBoundInput_of_problem prob
  obtain ⟨c₂, D₂, hc₂, hD₂, hhi⟩ := theoremC15UpperInput_probW prob
  refine ⟨max c₁ c₂, max D₁ D₂ + 1, le_trans hc₁ (le_max_left _ _), ?_, fun {c} hc => ?_⟩
  · have : 0 ≤ D₂ := hD₂
    linarith [le_max_right D₁ D₂]
  · have h1 := hlo ((le_max_left c₁ c₂).trans hc)
    have h2 := hhi ((le_max_right c₁ c₂).trans hc)
    exact abs_le.mpr ⟨by linarith [le_max_left D₁ D₂], by linarith [le_max_right D₁ D₂]⟩

lemma uAiry_T_V_tendsto (prob : FixedWeightProblem) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) :
    Tendsto (fun n => uAiry (c n) (prob.T_V (c n))) atTop (𝓝 (airyZero 1)) := by
  obtain ⟨c₀, B₀, hc₀, _, hbd⟩ := fixedWeight_T_V_sub_TStar_bounded prob
  rw [Metric.tendsto_nhds]
  intro ε hε
  set z : ℝ := xiStar * ε / (3 * betaTip)
  have hz : 0 < z := by have := xiStar_pos; have := betaTip_pos; positivity
  have hval_p : airyZero 1 - 3 * betaTip * z / (2 * xiStar) = airyZero 1 - ε / 2 := by
    dsimp [z]; field_simp [xiStar_pos.ne', betaTip_pos.ne']
  have hval_m : airyZero 1 - -(3 * betaTip * z) / (2 * xiStar) = airyZero 1 + ε / 2 := by
    dsimp [z]; field_simp [xiStar_pos.ne', betaTip_pos.ne']; ring
  have hup : Tendsto (fun n => uAiry (c n) (TStar (c n) + z * (c n) ^ ((1 : ℝ) / 3))) atTop
      (𝓝 (airyZero 1 - ε / 2)) := by
    simpa [hval_p, Function.comp_def] using (tendsto_uAiry_shift z).comp hc
  have hdn : Tendsto (fun n => uAiry (c n) (TStar (c n) + (-z) * (c n) ^ ((1 : ℝ) / 3))) atTop
      (𝓝 (airyZero 1 + ε / 2)) := by
    simpa [hval_m, Function.comp_def, neg_mul] using (tendsto_uAiry_shift (-z)).comp hc
  have hzc : Tendsto (fun n => z * (c n) ^ ((1 : ℝ) / 3)) atTop atTop :=
    Tendsto.const_mul_atTop hz ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc)
  filter_upwards [hc.eventually_ge_atTop c₀, hc.eventually_gt_atTop 0, hzc.eventually_ge_atTop B₀,
    hup.eventually (lt_mem_nhds (by linarith : airyZero 1 - ε < airyZero 1 - ε / 2)),
    hdn.eventually (gt_mem_nhds (by linarith : airyZero 1 + ε / 2 < airyZero 1 + ε))]
    with n hcn hcpos hzB h1 h2
  have htv := abs_le.mp (hbd hcn)
  have ha1 := uAiry_antitone hcpos (show TStar (c n) + (-z) * (c n) ^ ((1 : ℝ) / 3) ≤ prob.T_V (c n) by linarith)
  have ha2 := uAiry_antitone hcpos (show prob.T_V (c n) ≤ TStar (c n) + z * (c n) ^ ((1 : ℝ) / 3) by linarith)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Helper: `GapCondition` for `τ n = T_V(c n) - η n` when `0 ≤ η n` and `η n / c_n^{1/3} → 0`. -/
lemma gapCondition_T_V_sub (prob : FixedWeightProblem) {c η : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) :
    GapCondition c (fun n => prob.T_V (c n) - η n) := by
  obtain ⟨c₁, D, -, -, hlo⟩ := fixedWeightLowerBoundInput_of_problem prob
  intro δ hδ
  have hc13 : Tendsto (fun n => (c n) ^ ((1 : ℝ) / 3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc
  have hD_lim : Tendsto (fun n => D / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hc13
  have hsum : Tendsto (fun n => D / (c n) ^ ((1 : ℝ) / 3) + η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
    simpa using hD_lim.add hη_o
  filter_upwards [hc.eventually_ge_atTop c₁, hc13.eventually_gt_atTop 0,
    hsum.eventually (gt_mem_nhds hδ)] with n hcn hc3 hlt
  have htv := hlo hcn
  have hmul : (D / (c n) ^ ((1 : ℝ) / 3) + η n / (c n) ^ ((1 : ℝ) / 3)) * (c n) ^ ((1 : ℝ) / 3) <
      δ * (c n) ^ ((1 : ℝ) / 3) := mul_lt_mul_of_pos_right hlt hc3
  have hdiv : (D / (c n) ^ ((1 : ℝ) / 3) + η n / (c n) ^ ((1 : ℝ) / 3)) * (c n) ^ ((1 : ℝ) / 3) =
      D + η n := by field_simp [hc3.ne']
  rw [hdiv] at hmul
  linarith

/-- Unconditional vague convergence to `airyMeasure` for any sequence of crossing measures
supported on `[T_V(c_n) - η_n, ∞)` with `η_n = o(c_n^{1/3})`. -/
theorem near_opt_isVagueLimit (prob : FixedWeightProblem) {c η : ℕ → ℝ}
    (hc : Tendsto c atTop atTop)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0))
    {ν_seq : ℕ → Measure ℝ}
    (hν : ∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
      ν_seq n = meas.ν ∧ meas.ν (Ici (prob.T_V (c n) - η n))ᶜ = 0) :
    IsVagueLimit atTop (fun n => spectralMeasure prob (c n) (ν_seq n)) airyMeasure := by
  classical
  have hτ_pos : ∀ᶠ n in atTop, 0 < prob.T_V (c n) - η n := by
    obtain ⟨c₁, D, -, _, hlo⟩ := fixedWeightLowerBoundInput_of_problem prob
    have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
    have hA : 0 ≤ Aopt := by unfold Aopt; have := cStar_pos; positivity
    have hc13 : Tendsto (fun n => (c n) ^ ((1 : ℝ) / 3)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc
    have hη_lt : ∀ᶠ n in atTop, η n ≤ (c n) ^ ((1 : ℝ) / 3) := by
      filter_upwards [hc13.eventually_gt_atTop 0, hη_o.eventually (gt_mem_nhds zero_lt_one)]
        with n hc3 hlt
      exact ((div_lt_one hc3).mp hlt).le
    have hT_big : ∀ᶠ n in atTop, (c n) ^ ((1 : ℝ) / 3) + D < xiBar * c n := by
      have hdiv : Tendsto (fun n => ((c n) ^ ((1 : ℝ) / 3) + D) / c n) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc
        have h2 : Tendsto (fun n => D / c n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hc
        have h0 : Tendsto (fun n => (c n) ^ (-(2 / 3 : ℝ)) + D / c n) atTop (𝓝 0) := by
          simpa using h1.add h2
        refine h0.congr' ?_
        filter_upwards [hc.eventually_gt_atTop 0] with n hcn
        have hp : (c n) ^ ((1 : ℝ) / 3) / c n = (c n) ^ (-(2 / 3 : ℝ)) := by
          calc (c n) ^ ((1 : ℝ) / 3) / c n
              = (c n) ^ ((1 : ℝ) / 3) / (c n) ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = (c n) ^ ((1 : ℝ) / 3 - 1) := (Real.rpow_sub hcn _ _).symm
            _ = (c n) ^ (-(2 / 3 : ℝ)) := by norm_num
        rw [add_div, hp]
      filter_upwards [hc.eventually_gt_atTop 0, hdiv.eventually (gt_mem_nhds hxi)] with n hcn hlt
      have := (div_lt_iff₀ hcn).mp hlt
      linarith
    filter_upwards [hc.eventually_ge_atTop c₁, hc.eventually_gt_atTop 0, hη_lt, hT_big]
      with n hcn hcpos hηn hTb
    have htv := hlo hcn
    have hAc : 0 ≤ Aopt * (c n) ^ ((1 : ℝ) / 3) := mul_nonneg hA (Real.rpow_pos_of_pos hcpos _).le
    unfold TStar at htv
    linarith
  have hev : ∀ᶠ n in atTop,
      0 < c n ∧ prob.totalShift ≤ c n / 12 ∧ 0 < prob.T_V (c n) - η n ∧
      ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧ meas.ν (Ici (prob.T_V (c n) - η n))ᶜ = 0 :=
    ((hc.eventually_gt_atTop 0).and ((hc.eventually_ge_atTop (12 * prob.totalShift)).mono
      (fun _ h => by linarith))).and (hτ_pos.and hν) |>.mono fun n ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ =>
      ⟨h1, h2, h3, h4⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  let c' : ℕ → ℝ := fun j => c (j + N₀)
  let τ' : ℕ → ℝ := fun j => prob.T_V (c (j + N₀)) - η (j + N₀)
  let meas' : ∀ j : ℕ, AdmissibleCrossingMeasure prob (c' j / 12) :=
    fun j => (hN₀ (j + N₀) (Nat.le_add_left N₀ j)).2.2.2.choose
  have hmeas' : ∀ j : ℕ, ν_seq (j + N₀) = (meas' j).ν ∧
      (meas' j).ν (Ici (τ' j))ᶜ = 0 := fun j =>
    (hN₀ (j + N₀) (Nat.le_add_left N₀ j)).2.2.2.choose_spec
  let S : CrossingSequence prob :=
    { c := c'
      τ := τ'
      meas := meas'
      tendsto_c := hc.comp (tendsto_add_atTop_nat N₀)
      c_pos := fun j => (hN₀ (j + N₀) (Nat.le_add_left N₀ j)).1
      shift_le := fun j => (hN₀ (j + N₀) (Nat.le_add_left N₀ j)).2.1
      τ_pos := fun j => (hN₀ (j + N₀) (Nat.le_add_left N₀ j)).2.2.1
      atGap := fun j => by
        unfold IsAtGap
        have hsub : Iio (τ' j) ⊆ (Ici (τ' j))ᶜ := fun t ht => not_le.mpr ht
        exact measure_mono_null hsub (hmeas' j).2 }
  have hgap : GapCondition S.c S.τ :=
    gapCondition_T_V_sub prob (hc.comp (tendsto_add_atTop_nat N₀))
      (hη_o.comp (tendsto_add_atTop_nat N₀))
  have hsig : SigmaConclusion S.μS :=
    theorem_sigma_crossing S hgap
      (designPropertyP_union (designPropertyP_probW prob S) (displacedPropertyP_probW prob S))
      (SameSiteFamily.mono Set.subset_union_left (sameSiteFamily_designClass designTailBounds).some)
      (DisplacedFamily.mono (displacedClass_subset.trans Set.subset_union_right) displacedFamily)
      farFamily
  have hvag_shift := hsig.2.2.2.1
  intro g hg hcs
  have hlim := hvag_shift g hg hcs
  have heq_shift : (fun j => ∫ u, g u ∂(S.μS j)) =
      fun j => ∫ u, g u ∂(spectralMeasure prob (c (j + N₀)) (ν_seq (j + N₀))) := by
    ext j
    have hm1 : (S.meas j).ν = ν_seq (j + N₀) := (hmeas' j).1.symm
    have hc1 : S.c j = c (j + N₀) := rfl
    change ∫ u, g u ∂(spectralMeasure prob (S.c j) (S.meas j).ν) = _
    rw [hm1, hc1]
  rw [heq_shift] at hlim
  exact (tendsto_add_atTop_iff_nat N₀).mp hlim

/-- Window form of `near_opt_isVagueLimit` ready for `hb_clusters` and `hb_mass_*`. -/
lemma near_opt_window_vague (prob : FixedWeightProblem) (CD : HbClusterData HermiteBiehlerData.airy)
    (hCD_z : ∀ k : Fin CD.K, CD.z k = airyNode k.1)
    (hCD_ω : ∀ k : Fin CD.K, CD.ω k = airyNodeWeight k.1)
    (hCD_lo : airyNode CD.K < CD.a)
    {c η : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0))
    (ν_seq : ℕ → Measure ℝ)
    (hν : ∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
      ν_seq n = meas.ν ∧ meas.ν (Ici (prob.T_V (c n) - η n))ᶜ = 0)
    {g : ℝ → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g) (hsupp : tsupport g ⊆ Ioo CD.a CD.b) :
    Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
      (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k))) := by
  have hv := near_opt_isVagueLimit prob hc hη_o hν g hg hcs
  have hsum : Integrable g airyMeasure := integrable_airyMeasure hg (summable_of_cs hcs _)
  rw [integral_airyMeasure hg (summable_of_cs hcs _)] at hv
  have heq : (∑' i : ℕ, g (airyNode i) * airyNodeWeight i) = ∑ k : Fin CD.K, CD.ω k * g (CD.z k) := by
    rw [tsum_eq_sum (s := Finset.range CD.K) (fun i hi => by
      have hge : CD.K ≤ i := by simpa [Finset.mem_range] using hi
      have hle : airyNode i ≤ airyNode CD.K := airyNode_strictAnti.antitone hge
      have hnot : airyNode i ∉ tsupport g := fun hm => by linarith [(hsupp hm).1]
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul])]
    rw [← Fin.sum_univ_eq_sum_range (fun i => g (airyNode i) * airyNodeWeight i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hCD_z k, hCD_ω k, mul_comm]
  rwa [heq] at hv

/-! ### 3. `dsl:one-level-clusters`: exact one-level Airy clusters at `(H_w)` -/

/-- **Exact one-level Airy clusters and unconditional first mass** (`dsl:one-level-clusters`,
`dual_spectrum_limit.tex`, Theorem `E'-C`): for every `prob : FixedWeightProblem`, `K ≥ 1`,
`R_K ∈ (|a_K|, |a_{K+1}|)`, and `c_n → ∞`:
1. There exist `K` canonical points `T_V(c_n) = t^*_0(n) < t^*_1(n) < … < t^*_{K-1}(n)` (independent
   of the measure) exhaustively supporting every attaining crossing measure `ν_*` on
   `{t ≥ T_V(c_n) : |uAiry (c n) t| ≤ R_K}`;
2. For every weak extremal `gs`, `t^*_0(n)` is a simple zero and `t^*_1(n), …, t^*_{K-1}(n)` are
   double zeros of `psiTilde prob (c n) gs`, with `(t^*_k(n) - ξ̄ c_n) c_n^{-1/3} → (|a_{k+1}|/|a_1|) A_opt`;
3. Uniformly over all attaining crossing measures `ν_*`, the normalised weights converge to
   `Ai'(a_{k+1})^{-2}`, the local density ratios (for `1 ≤ k < K - 1`) converge to
   `R_k = 1 / (Ai'(a_{k+1})^2 · (|a_{k+2}| - |a_k|)/2)`, and the first atom satisfies `dsl:d1-asym`
   with `b_n = T_V(c_n) - T_*(c_n) = O(1)`. -/
theorem one_level_clusters (prob : FixedWeightProblem) (K : ℕ) (hK : 1 ≤ K) {R_K : ℝ}
    (hRK_lo : |airyZero K| < R_K) (hRK_hi : R_K < |airyZero (K + 1)|)
    {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) :
    ∃ tStar : Fin K → ℕ → ℝ,
      (∀ k : Fin K, Tendsto (fun n => uAiry (c n) (tStar k n)) atTop (𝓝 (airyNode k.1)) ∧
        Tendsto (fun n => (tStar k n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) atTop
          (𝓝 ((|airyNode k.1| / |airyZero 1|) * Aopt))) ∧
      (∀ hK2 : 2 ≤ K, Tendsto (fun n => (tStar ⟨1, by omega⟩ n - tStar ⟨0, hK⟩ n) / (c n) ^ ((1 : ℝ) / 3))
        atTop (𝓝 ((|airyNode 1| / |airyZero 1| - 1) * Aopt))) ∧
      (∀ᶠ n in atTop,
        StrictMono (fun k => tStar k n) ∧
        tStar ⟨0, hK⟩ n = prob.T_V (c n) ∧
        (∀ k : Fin K, 0 < tStar k n ∧ |uAiry (c n) (tStar k n)| ≤ R_K)) ∧
      (∀ᶠ n in atTop, ∀ gs : ℝ → ℝ,
        IsWeakExtremal prob (c n) ∅ (prob.T_V (c n)) gs →
        ∀ k : Fin K, gs (tStar k n) = 0 ∧
          analyticOrderNatAt (psiTilde prob (c n) gs) (chartUT (c n) (tStar k n) : ℂ) =
            if k.1 = 0 then 1 else 2) ∧
      (∀ᶠ n in atTop, ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (Ici (prob.T_V (c n)))ᶜ = 0 →
        (∀ k : Fin K, 0 < meas.ν {tStar k n}) ∧
        meas.ν ({t ∈ Ici (prob.T_V (c n)) | |uAiry (c n) t| ≤ R_K} \
          Set.range (fun k => tStar k n)) = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (Ici (prob.T_V (c n)))ᶜ = 0 →
          ∀ k : Fin K,
            |spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal -
              airyNodeWeight k.1| ≤ ε) ∧
      (∀ (k : Fin K) (hk1 : 1 ≤ k.1) (hk2 : k.1 + 1 < K),
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
            meas.ν (Ici (prob.T_V (c n)))ᶜ = 0 →
            |(meas.ν {tStar k n}).toReal /
                (2 * Real.pi * prob.cardyV (c n / 12) (tStar k n) *
                  ((tStar ⟨k.1 + 1, hk2⟩ n - tStar ⟨k.1 - 1, by omega⟩ n) / 2)) -
              airyNodeWeight k.1 / ((|airyNode (k.1 + 1)| - |airyNode (k.1 - 1)|) / 2)| ≤ ε) ∧
      (let amp : ℝ := 2 * Real.sqrt xiStar * (2 * xiStar) ^ (prob.w - 1) *
        prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) / (Real.sqrt 3 * betaTip)
      (∃ B₀ : ℝ, ∀ᶠ n in atTop, |prob.T_V (c n) - TStar (c n)| ≤ B₀) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (Ici (prob.T_V (c n)))ᶜ = 0 →
          let b₁ := prob.T_V (c n) - TStar (c n)
          |(meas.ν {tStar ⟨0, hK⟩ n}).toReal /
              (amp * airyNodeWeight 0 * (c n) ^ (-(1 / 6 : ℝ)) *
                Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n +
                  (2 * Real.pi * |airyZero 1| / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
                  (Real.pi / xiStar) * b₁)) - 1| ≤ ε) := by
  classical
  have haK_neg : airyZero K < 0 := airyZero_neg K
  have haK1_neg : airyZero (K + 1) < 0 := airyZero_neg (K + 1)
  have hnode_Km1 : airyNode (K - 1) = airyZero K := by
    unfold airyNode; congr 1; omega
  have hnode_K : airyNode K = airyZero (K + 1) := rfl
  have haK_abs : |airyZero K| = -airyNode (K - 1) := by
    rw [hnode_Km1, abs_of_neg haK_neg]
  have haK1_abs : |airyZero (K + 1)| = -airyNode K := by
    rw [hnode_K, abs_of_neg haK1_neg]
  let a : ℝ := -(R_K + |airyZero (K + 1)|) / 2
  let b : ℝ := R_K + 1
  have ha_lo : airyNode K < a := by dsimp [a]; linarith
  have ha_hi : a < airyNode (K - 1) := by dsimp [a]; linarith
  have ha_sub : a < -R_K := by dsimp [a]; linarith
  have hRK_neg_lt : -R_K < airyNode (K - 1) := by linarith
  have hnode0_lt_RK : airyNode 0 < R_K := by
    have h1 : airyZero 1 < 0 := airyZero_neg 1
    have h2 : |airyZero 1| ≤ |airyZero K| := by
      have hle : airyZero K ≤ airyZero 1 := by
        by_cases hK1 : K = 1
        · rw [hK1]
        · exact (airyZero_lt_of_lt le_rfl (by omega : 1 < K)).le
      rw [abs_of_neg h1, abs_of_neg haK_neg]; linarith
    have h3 : 0 < R_K := lt_of_le_of_lt (abs_nonneg _) hRK_lo
    rw [airyNode_zero]; linarith
  have hb : airyNode 0 < b := by dsimp [b]; linarith
  let CD : HbClusterData HermiteBiehlerData.airy := airyHbClusterData K hK ha_lo ha_hi hb
  let s : HbNodes HermiteBiehlerData.airy → ℕ → ℝ := fun i => hbNodes_airy_isEmpty.elim i
  have hs_pos : ∀ i : HbNodes HermiteBiehlerData.airy, ∀ᶠ n in atTop, 0 < s i n :=
    fun i => hbNodes_airy_isEmpty.elim i
  have hs_tend : ∀ i : HbNodes HermiteBiehlerData.airy,
      Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1) :=
    fun i => hbNodes_airy_isEmpty.elim i
  have hB_eq : ∀ n, constrainedThreshold prob (c n) (hbPrescribedSet s n) = prob.T_V (c n) := by
    intro n; rw [hbPrescribedSet_airy_eq_empty, constrainedThreshold_empty]
  have hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 HermiteBiehlerData.airy.tm) := by
    simp only [hB_eq]; exact uAiry_T_V_tendsto prob hc
  have hvag : ∀ (ν_seq : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧
        meas.ν (hbPrescribedSet s n ∪
          Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0) →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo CD.a CD.b →
        Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k))) := by
    intro ν_seq hν g hg hcs hsupp
    have hν' : ∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧ meas.ν (Ici (prob.T_V (c n) - 0))ᶜ = 0 := by
      filter_upwards [hν] with n ⟨meas, h1, h2⟩
      refine ⟨meas, h1, ?_⟩
      rw [hbPrescribedSet_airy_eq_empty, Set.empty_union, constrainedThreshold_empty] at h2
      simpa only [sub_zero] using h2
    exact near_opt_window_vague prob CD (fun _ => rfl) (fun _ => rfl) ha_lo hc
      (by simp) ν_seq hν' hg hcs hsupp
  obtain ⟨tStar, ht1, ht2, ht3, ht4, ht5, ht6⟩ :=
    hb_clusters prob HermiteBiehlerData.airy CD hc hs_pos hs_tend hB_tend hvag
  let tStar' : Fin K → ℕ → ℝ := tStar
  -- Assemble all conclusions cleanly
  refine ⟨tStar', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Part 1: Airy coordinate limit & `(tStar k n - xiBar * c n) / (c n)^(1/3)` limit
    intro k
    refine ⟨(ht1 k).1, ?_⟩
    have hpos := tendsto_position_of_uAiry hc (ht1 k).1
    have hneg : airyNode k.1 < 0 := airyNode_neg k.1
    have h1 : airyZero 1 < 0 := airyZero_neg 1
    have heq : -cStar * CD.z k = (|airyNode k.1| / |airyZero 1|) * Aopt := by
      change -cStar * airyNode k.1 = _
      unfold Aopt
      rw [abs_of_neg hneg, abs_of_neg h1]
      field_simp [h1.ne]
    rwa [heq] at hpos
  · -- Part 2: Spacing `(tStar 1 n - tStar 0 n) / c_n^{1/3}` when `2 ≤ K`
    intro hK2
    have h0 := tendsto_position_of_uAiry hc (ht1 ⟨0, hK⟩).1
    have h1 := tendsto_position_of_uAiry hc (ht1 ⟨1, hK2⟩).1
    have hsub := h1.sub h0
    have heq_lim : -cStar * CD.z ⟨1, hK2⟩ - -cStar * CD.z ⟨0, hK⟩ =
        (|airyNode 1| / |airyZero 1| - 1) * Aopt := by
      have hz1 : CD.z ⟨1, hK2⟩ = airyNode 1 := rfl
      have hz0 : CD.z ⟨0, hK⟩ = airyZero 1 := rfl
      have hn1 : airyNode 1 < 0 := airyNode_neg 1
      have ha1 : airyZero 1 < 0 := airyZero_neg 1
      rw [hz1, hz0]
      unfold Aopt
      rw [abs_of_neg hn1, abs_of_neg ha1]
      field_simp [ha1.ne]; ring
    rw [heq_lim] at hsub
    have hsub' : Tendsto (fun n => (tStar ⟨1, hK2⟩ n - tStar ⟨0, hK⟩ n) / (c n) ^ ((1 : ℝ) / 3))
        atTop (𝓝 ((|airyNode 1| / |airyZero 1| - 1) * Aopt)) :=
      hsub.congr fun n => by ring
    exact hsub'
  · -- Part 3: Ordering, terminal equality `tStar 0 n = T_V (c n)`, positivity, and `|u| ≤ R_K`
    have hu_in : ∀ᶠ n in atTop, ∀ k : Fin K, 0 < tStar k n ∧ |uAiry (c n) (tStar k n)| ≤ R_K := by
      rw [eventually_all]
      intro k
      have hk_bd : |airyNode k.1| < R_K := by
        have hle : airyNode (K - 1) ≤ airyNode k.1 := airyNode_strictAnti.antitone (by omega)
        have hle0 : airyNode k.1 ≤ airyNode 0 := airyNode_strictAnti.antitone (Nat.zero_le _)
        have hneg : airyNode k.1 < 0 := airyNode_neg k.1
        rw [abs_of_neg hneg]
        rw [haK_abs] at hRK_lo
        linarith
      filter_upwards [(ht1 k).1.eventually (Metric.ball_mem_nhds (airyNode k.1)
        (show 0 < R_K - |airyNode k.1| by linarith)), ht2] with n hu ⟨_, hpos, _, _⟩
      refine ⟨hpos k, ?_⟩
      rw [Real.dist_eq] at hu
      calc |uAiry (c n) (tStar k n)|
          = |(uAiry (c n) (tStar k n) - airyNode k.1) + airyNode k.1| := by ring_nf
        _ ≤ |uAiry (c n) (tStar k n) - airyNode k.1| + |airyNode k.1| := abs_add_le _ _
        _ ≤ R_K := by linarith
    filter_upwards [ht2, hu_in] with n ⟨hsm, _, htm, _⟩ hu
    refine ⟨hsm, ?_, hu⟩
    rw [← hB_eq n]
    exact htm ⟨0, hK⟩ (by simp [CD]; rfl)
  · -- Part 4: Weak extremal zeros and simple/double multiplicities
    filter_upwards [ht3] with n hwe gs hgs k
    have hgs' : IsWeakExtremal prob (c n) (hbPrescribedSet s n)
        (constrainedThreshold prob (c n) (hbPrescribedSet s n)) gs := by
      rwa [hbPrescribedSet_airy_eq_empty, constrainedThreshold_empty]
    obtain ⟨h0, hord⟩ := hwe gs hgs' k
    refine ⟨h0, ?_⟩
    rw [hord]
    by_cases hk0 : k.1 = 0
    · have hS : CD.z k ∈ HermiteBiehlerData.airy.S := by
        change airyNode k.1 ∈ HermiteBiehlerData.airy.S
        rw [hk0, airyNode_zero]; exact HermiteBiehlerData.airy.tm_mem
      simp [hk0, hS]
    · have hnS : CD.z k ∉ HermiteBiehlerData.airy.S := by
        simp only [CD, HermiteBiehlerData.airy, Finset.mem_singleton]
        intro heq
        change airyNode k.1 = airyZero 1 at heq
        have hlt := airyNode_strictAnti (Nat.pos_of_ne_zero hk0)
        rw [airyNode_zero] at hlt; linarith
      simp [hk0, hnS]
  · -- Part 5: Exact support characterization on `{t ≥ T_V (c n) | |u| ≤ R_K}`
    have hsub_u : ∀ᶠ n in atTop,
        {t ∈ Ici (prob.T_V (c n)) | |uAiry (c n) t| ≤ R_K} ⊆
          {t ∈ Ioi (0 : ℝ) | uAiry (c n) t ∈ Icc (-R_K) R_K} := by
      obtain ⟨c₁, D, -, _, hlo⟩ := fixedWeightLowerBoundInput_of_problem prob
      have hT_pos : ∀ᶠ n in atTop, 0 < prob.T_V (c n) := by
        have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
        have hA : 0 ≤ Aopt := by unfold Aopt; have := cStar_pos; positivity
        filter_upwards [hc.eventually_ge_atTop c₁, hc.eventually_gt_atTop 0,
          (Tendsto.const_mul_atTop hxi hc).eventually_gt_atTop D] with n hcn hcpos hgt
        have htv := hlo hcn
        have hAc : 0 ≤ Aopt * (c n) ^ ((1 : ℝ) / 3) := mul_nonneg hA (Real.rpow_pos_of_pos hcpos _).le
        unfold TStar at htv; linarith
      filter_upwards [hT_pos] with n hTp t ⟨ht1, ht2⟩
      exact ⟨lt_of_lt_of_le hTp ht1, abs_le.mp ht2⟩
    have ha'_mem : CD.a < -R_K := ha_sub
    have ha'z_mem : -R_K < CD.z ⟨CD.K - 1, Nat.sub_lt CD.hK zero_lt_one⟩ := hRK_neg_lt
    have hbz_mem : CD.z ⟨0, CD.hK⟩ < R_K := hnode0_lt_RK
    have hb_mem : R_K < CD.b := by change R_K < b; dsimp [b]; linarith
    filter_upwards [ht4 (-R_K) R_K ha'_mem ha'z_mem hbz_mem hb_mem, hsub_u] with n h4 hsub meas hν
    have hν' : meas.ν (hbPrescribedSet s n ∪
        Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 := by
      simpa [hbPrescribedSet_airy_eq_empty, constrainedThreshold_empty] using hν
    obtain ⟨hat, hnull⟩ := h4 meas hν'
    refine ⟨hat, measure_mono_null (Set.sdiff_subset_sdiff_left hsub) hnull⟩
  · -- Part 6: Uniform normalised weights `d_k / (ρ J_n) → Ai'(a_{k+1})^{-2}`
    intro ε hε
    filter_upwards [ht5 ε hε] with n hn meas hν k
    have hν' : meas.ν (hbPrescribedSet s n ∪
        Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 := by
      simpa [hbPrescribedSet_airy_eq_empty, constrainedThreshold_empty] using hν
    exact hn meas hν' k
  · -- Part 7: Local density ratios
    intro k hk1 hk2 ε hε
    let k_hi : Fin CD.K := ⟨k.1 + 1, hk2⟩
    let k_lo : Fin CD.K := ⟨k.1 - 1, show k.1 - 1 < K by omega⟩
    let L_num : ℝ := cStar * (|airyNode (k.1 + 1)| - |airyNode (k.1 - 1)|) / 2
    have hL_pos : 0 < L_num := by
      have hlt : airyNode (k.1 + 1) < airyNode (k.1 - 1) := airyNode_strictAnti (by omega)
      have hn1 : airyNode (k.1 + 1) < 0 := airyNode_neg (k.1 + 1)
      have hn2 : airyNode (k.1 - 1) < 0 := airyNode_neg (k.1 - 1)
      have hcstar := cStar_pos
      dsimp [L_num]; rw [abs_of_neg hn1, abs_of_neg hn2]; nlinarith
    have hj_lim : Tendsto (fun n => jAiry (c n) (tStar k n) / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 cStar) := by
      have hx : Tendsto (fun n => Real.sqrt (3 * tStar k n / c n)) atTop (𝓝 xiStar) := by
        have hu := (ht1 k).1
        have heq : ∀ᶠ n in atTop, Real.sqrt (3 * tStar k n / c n) =
            xiStar - uAiry (c n) (tStar k n) / (betaTip * (c n) ^ ((2 : ℝ) / 3)) := by
          filter_upwards [hc.eventually_gt_atTop 0] with n hcn
          have hp : (c n) ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
          unfold uAiry; field_simp [betaTip_pos.ne', hp]; ring
        have h0 : Tendsto (fun n => xiStar - uAiry (c n) (tStar k n) *
            (betaTip⁻¹ * (c n) ^ (-(2 / 3 : ℝ)))) atTop (𝓝 xiStar) := by
          have h23 : Tendsto (fun n => (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
            (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc
          simpa using tendsto_const_nhds.sub (hu.mul (h23.const_mul betaTip⁻¹))
        refine h0.congr' ?_
        filter_upwards [heq, hc.eventually_gt_atTop 0] with n hn hcn
        rw [hn, Real.rpow_neg hcn.le]; ring
      have hlim : Tendsto (fun n => 2 * Real.sqrt (3 * tStar k n / c n) / (3 * betaTip)) atTop
          (𝓝 (2 * xiStar / (3 * betaTip))) := (hx.const_mul 2).div_const (3 * betaTip)
      have heq_cstar : 2 * xiStar / (3 * betaTip) = cStar := rfl
      rw [heq_cstar] at hlim
      refine hlim.congr' ?_
      filter_upwards [hc.eventually_gt_atTop 0] with n hcn
      have hp : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
      unfold jAiry; field_simp [hp]
    have hdiff_lim : Tendsto (fun n => ((tStar k_hi n - tStar k_lo n) / 2) / (c n) ^ ((1 : ℝ) / 3))
        atTop (𝓝 L_num) := by
      have hp_hi := tendsto_position_of_uAiry hc (ht1 k_hi).1
      have hp_lo := tendsto_position_of_uAiry hc (ht1 k_lo).1
      have hsub := (hp_hi.sub hp_lo).div_const 2
      have heq_lim : (-cStar * CD.z k_hi - -cStar * CD.z k_lo) / 2 = L_num := by
        have h1 : CD.z k_hi = airyNode (k.1 + 1) := rfl
        have h2 : CD.z k_lo = airyNode (k.1 - 1) := rfl
        have hn1 : airyNode (k.1 + 1) < 0 := airyNode_neg (k.1 + 1)
        have hn2 : airyNode (k.1 - 1) < 0 := airyNode_neg (k.1 - 1)
        rw [h1, h2]
        dsimp [L_num]; rw [abs_of_neg hn1, abs_of_neg hn2]; ring
      rw [heq_lim] at hsub
      exact hsub.congr fun n => by ring
    have hfac_lim : Tendsto (fun n => jAiry (c n) (tStar k n) / ((tStar k_hi n - tStar k_lo n) / 2))
        atTop (𝓝 (1 / ((|airyNode (k.1 + 1)| - |airyNode (k.1 - 1)|) / 2))) := by
      have hq := hj_lim.div hdiff_lim hL_pos.ne'
      have heq_val : cStar / L_num = 1 / ((|airyNode (k.1 + 1)| - |airyNode (k.1 - 1)|) / 2) := by
        dsimp [L_num]; have hcstar := cStar_pos; field_simp [hcstar.ne']
      rw [heq_val] at hq
      refine hq.congr' ?_
      filter_upwards [hc.eventually_gt_atTop 0, ht2] with n hcn ⟨hsm, _, _, _⟩
      have hp : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
      have hd_ne : tStar k_hi n - tStar k_lo n ≠ 0 := by
        have hlt : k_lo < k_hi := by dsimp [k_lo, k_hi]; simp [Fin.lt_def]
        exact sub_ne_zero.mpr (hsm hlt).ne'
      dsimp only [Pi.div_apply]
      field_simp [hp, hd_ne]
    let R_lim : ℝ := 1 / ((|airyNode (k.1 + 1)| - |airyNode (k.1 - 1)|) / 2)
    have hR_pos : 0 < R_lim := by
      dsimp [R_lim]
      have hlt : airyNode (k.1 + 1) < airyNode (k.1 - 1) := airyNode_strictAnti (by omega)
      have hn1 : airyNode (k.1 + 1) < 0 := airyNode_neg (k.1 + 1)
      have hn2 : airyNode (k.1 - 1) < 0 := airyNode_neg (k.1 - 1)
      have hsub_pos : 0 < |airyNode (k.1 + 1)| - |airyNode (k.1 - 1)| := by
        rw [abs_of_neg hn1, abs_of_neg hn2]; linarith
      exact div_pos one_pos (half_pos hsub_pos)
    let δ₁ : ℝ := min 1 (ε / (3 * R_lim))
    let δ₂ : ℝ := ε / (3 * (airyNodeWeight k.1 + 1))
    have hδ₁ : 0 < δ₁ := lt_min zero_lt_one (by positivity)
    have hδ₂ : 0 < δ₂ := by have := airyNodeWeight_pos k.1; positivity
    filter_upwards [ht5 δ₁ hδ₁, ht2, hc.eventually_ge_atTop (max 1 (12 * prob.totalShift)),
      hfac_lim.eventually (Metric.ball_mem_nhds R_lim hδ₂)]
      with n hn ⟨hsm, hpos, _, _⟩ hc_ge hfac meas hν
    have hν' : meas.ν (hbPrescribedSet s n ∪
        Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 := by
      simpa [hbPrescribedSet_airy_eq_empty, constrainedThreshold_empty] using hν
    have h_sw := hn meas hν' k
    have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hc_ge)
    have hsh12 : prob.totalShift ≤ c n / 12 := by have := (le_max_right (1 : ℝ) _).trans hc_ge; linarith
    have hV_ne : prob.cardyV (c n / 12) (tStar k n) ≠ 0 := (prob.cardyV_pos hsh12 (hpos k)).ne'
    have hJ_ne : jAiry (c n) (tStar k n) ≠ 0 := (jAiry_pos hcpos (hpos k)).ne'
    have hdiff_pos : 0 < (tStar k_hi n - tStar k_lo n) / 2 := by
      have : k_lo < k_hi := by dsimp [k_lo, k_hi]; simp [Fin.lt_def]
      linarith [hsm this]
    let p : ℝ := spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal
    let q : ℝ := jAiry (c n) (tStar k n) / ((tStar k_hi n - tStar k_lo n) / 2)
    have hid : (meas.ν {tStar k n}).toReal /
        (2 * Real.pi * prob.cardyV (c n / 12) (tStar k n) *
          ((tStar k_hi n - tStar k_lo n) / 2)) = p * q := by
      dsimp [p, q, spectralWeight]
      field_simp [Real.pi_ne_zero, hV_ne, hJ_ne, hdiff_pos.ne']
    have hω_eq : CD.ω k = airyNodeWeight k.1 := rfl
    rw [hω_eq] at h_sw
    have hq_err : |q - R_lim| < δ₂ := by simpa [Real.dist_eq] using hfac
    have hp_bd : |p| ≤ airyNodeWeight k.1 + 1 := by
      have h1 := (abs_le.mp h_sw).2
      have h0 : 0 ≤ p := mul_nonneg (spectralWeight_pos hcpos hsh12 (hpos k)).le ENNReal.toReal_nonneg
      rw [abs_of_nonneg h0]
      linarith [min_le_left (1 : ℝ) (ε / (3 * R_lim))]
    have htri : |p * q - airyNodeWeight k.1 * R_lim| ≤
        |p| * |q - R_lim| + |p - airyNodeWeight k.1| * |R_lim| := by
      have heq : p * q - airyNodeWeight k.1 * R_lim =
          p * (q - R_lim) + (p - airyNodeWeight k.1) * R_lim := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (by rw [abs_mul p (q - R_lim), abs_mul (p - airyNodeWeight k.1) R_lim])
    have hterm1 : |p| * |q - R_lim| ≤ (airyNodeWeight k.1 + 1) * δ₂ := by
      nlinarith [abs_nonneg p, abs_nonneg (q - R_lim)]
    have hterm2 : |p - airyNodeWeight k.1| * |R_lim| ≤ δ₁ * R_lim := by
      rw [abs_of_pos hR_pos]
      exact mul_le_mul_of_nonneg_right h_sw hR_pos.le
    have hterm1' : (airyNodeWeight k.1 + 1) * δ₂ = ε / 3 := by
      have hwp : 0 < airyNodeWeight k.1 + 1 := by linarith [airyNodeWeight_pos k.1]
      dsimp [δ₂]; field_simp [hwp.ne']
    have hterm2' : δ₁ * R_lim ≤ ε / 3 := by
      calc δ₁ * R_lim ≤ (ε / (3 * R_lim)) * R_lim :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hR_pos.le
        _ = ε / 3 := by field_simp [hR_pos.ne']
    have hrhs : airyNodeWeight k.1 * R_lim =
        airyNodeWeight k.1 / ((|airyNode (k.1 + 1)| - |airyNode (k.1 - 1)|) / 2) := by
      dsimp [R_lim]; ring
    show |(meas.ν {tStar k n}).toReal /
        (2 * Real.pi * prob.cardyV (c n / 12) (tStar k n) *
          ((tStar k_hi n - tStar k_lo n) / 2)) -
      airyNodeWeight k.1 / ((|airyNode (k.1 + 1)| - |airyNode (k.1 - 1)|) / 2)| ≤ ε
    rw [hid, ← hrhs]
    linarith
  · -- Part 8: First atom asymptotic `dsl:d1-asym` and `|b₁ n| ≤ B₀`
    intro amp
    refine ⟨?_, ?_⟩
    · obtain ⟨_, B₀, _, _, hbd⟩ := fixedWeight_T_V_sub_TStar_bounded prob
      obtain ⟨c₀, B₀', _, _, hbd'⟩ := fixedWeight_T_V_sub_TStar_bounded prob
      exact ⟨B₀', hc.eventually_ge_atTop c₀ |>.mono fun n h => hbd' h⟩
    · intro ε hε
      filter_upwards [ht6 ε hε, ht2] with n hn ⟨_, _, htm, _⟩ meas hν
      have hν' : meas.ν (hbPrescribedSet s n ∪
          Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 := by
        simpa [hbPrescribedSet_airy_eq_empty, constrainedThreshold_empty] using hν
      have hraw := hn meas hν' ⟨0, CD.hK⟩
      have hz0 : CD.z ⟨0, CD.hK⟩ = airyZero 1 := rfl
      have hω0 : CD.ω ⟨0, CD.hK⟩ = airyNodeWeight 0 := rfl
      have ht0 : tStar ⟨0, hK⟩ n = prob.T_V (c n) := by
        rw [htm ⟨0, hK⟩ (by simp [CD]; rfl), hB_eq]
      have ha1 : airyZero 1 < 0 := airyZero_neg 1
      have hbk : tStar ⟨0, CD.hK⟩ n - xiBar * c n + cStar * CD.z ⟨0, CD.hK⟩ * (c n) ^ ((1 : ℝ) / 3) =
          prob.T_V (c n) - TStar (c n) := by
        change tStar ⟨0, hK⟩ n - xiBar * c n + cStar * CD.z ⟨0, CD.hK⟩ * (c n) ^ ((1 : ℝ) / 3) = _
        rw [ht0, hz0]
        unfold TStar Aopt
        rw [abs_of_neg ha1]
        ring
      have hsign : -(2 * Real.pi * CD.z ⟨0, CD.hK⟩ / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) =
          (2 * Real.pi * |airyZero 1| / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) := by
        rw [hz0, abs_of_neg ha1]; ring
      dsimp only at hraw
      change |(meas.ν {tStar ⟨0, hK⟩ n}).toReal /
          (amp * CD.ω ⟨0, CD.hK⟩ * (c n) ^ (-(1 / 6 : ℝ)) *
            Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
              (2 * Real.pi * CD.z ⟨0, CD.hK⟩ / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
              (Real.pi / xiStar) * (tStar ⟨0, CD.hK⟩ n - xiBar * c n + cStar * CD.z ⟨0, CD.hK⟩ * (c n) ^ ((1 : ℝ) / 3)))) - 1| ≤ ε at hraw
      rw [hbk, hω0] at hraw
      have heq_exp : (2 / 3 : ℝ) * Real.arsinh 1 * c n -
          (2 * Real.pi * CD.z ⟨0, CD.hK⟩ / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
          (Real.pi / xiStar) * (prob.T_V (c n) - TStar (c n)) =
          (2 / 3 : ℝ) * Real.arsinh 1 * c n +
          (2 * Real.pi * |airyZero 1| / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
          (Real.pi / xiStar) * (prob.T_V (c n) - TStar (c n)) := by
        linarith [hsign]
      rwa [heq_exp] at hraw

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.one_level_clusters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.one_level_clusters

end FormalResearch.ModularBootstrap.FixedWeight
