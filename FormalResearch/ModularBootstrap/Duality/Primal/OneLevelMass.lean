module

public import FormalResearch.ModularBootstrap.Duality.Primal.OneLevelClusters
public import FormalResearch.ModularBootstrap.Duality.Primal.HbMassWindowMoments

/-!
# Near-optimal one-level first-cluster mass (`dual_spectrum_limit.tex`, `dsl:near-opt-mass`)

Specializes `hb_mass_first_moment` (`Duality/Primal/HbMassWindowMoments.lean`) and `vague_node_mass` /
`vague_limsup_le` (`Upper/Rigidity/SpectrumCorollary.lean`) to prove `Proposition E'-M`
(`dsl:near-opt-mass`, `dsl:D1-exact`, and the `dsl:d1-asym` asymptotic replacement) for any
FixedWeightProblem and any sequence of crossing measures `ν_n` supported on `[T_V(c_n) - η_n, ∞)`
with `0 ≤ η_n ≤ exp(-γ c_n^{1/3})`, `γ > 2π r / (3 β)`, `0 < r < |a₁ - a₂|`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Duality FormalResearch.ModularBootstrap.WeightAxioms
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.ModularBootstrap.FixedWeightTip
  FormalResearch.ModularBootstrap.FixedWeightBand FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Bessel
  FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ArgPrinciple

/-! ### 1. Full isolating-radius vague convergence at the first Airy node `a₁` -/

/-- For ANY radius `r ∈ (0, |a₁ - a₂|)` (not just `r < |a₁ - a₂|/2`), vague convergence to
`airyMeasure` gives convergence of both open-window and closed-window masses around `a₁` to
`airyNodeWeight 0 = Ai'(a₁)^{-2}`. -/
lemma vague_first_node_mass_of_lt {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hν : IsVagueLimit atTop μ airyMeasure) {r : ℝ} (hr : 0 < r)
    (hr_sep : r < |airyZero 1 - airyZero 2|) :
    Tendsto (fun j => (μ j (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal) atTop
      (𝓝 (airyNodeWeight 0)) ∧
    Tendsto (fun j => (μ j (Icc (airyZero 1 - r) (airyZero 1 + r))).toReal) atTop
      (𝓝 (airyNodeWeight 0)) := by
  let a₁ : ℝ := airyZero 1
  let w₀ : ℝ := airyNodeWeight 0
  have hw₀ : 0 < w₀ := airyNodeWeight_pos 0
  let r₀ : ℝ := min (r / 2) (|airyZero 1 - airyZero 2| / 3)
  have h12 : airyZero 2 < airyZero 1 := airyZero_lt_of_lt le_rfl (by omega)
  have hr₀ : 0 < r₀ := lt_min (half_pos hr) (by rw [abs_of_pos (sub_pos.mpr h12)]; positivity)
  have hsep₀ : ∀ k, k ≠ 0 → 2 * r₀ ≤ |airyNode k - airyNode 0| := by
    intro k hk
    have h1 : airyNode k ≤ airyNode 1 := airyNode_strictAnti.antitone (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk))
    have h2 : airyNode 1 < airyNode 0 := airyNode_strictAnti zero_lt_one
    have hn1 : airyNode 1 = airyZero 2 := rfl
    have hn0 : airyNode 0 = airyZero 1 := airyNode_zero
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (lt_of_le_of_lt h1 h2))]
    have hdiff : airyZero 1 - airyZero 2 ≤ airyNode 0 - airyNode k := by
      rw [hn0, ← hn1]; linarith
    have habs : |airyZero 1 - airyZero 2| ≤ airyNode 0 - airyNode k := by
      rw [abs_of_pos (by rw [← hn0, ← hn1]; linarith)]; exact hdiff
    have hle : 2 * r₀ ≤ 2 * (|airyZero 1 - airyZero 2| / 3) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
    linarith
  have hlow := vague_node_mass hν 0 hr₀ hsep₀
  rw [airyNode_zero] at hlow
  let r' : ℝ := (r + |airyZero 1 - airyZero 2|) / 2
  have hrr' : r < r' := by dsimp [r']; linarith
  have hr'sep : r' < |airyZero 1 - airyZero 2| := by dsimp [r']; linarith
  have hCU : Icc (a₁ - r) (a₁ + r) ⊆ Ioo (a₁ - r') (a₁ + r') := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hμA_U : airyMeasure (Ioo (a₁ - r') (a₁ + r')) ≤ ENNReal.ofReal w₀ := by
    unfold airyMeasure
    rw [Measure.sum_apply _ isOpen_Ioo.measurableSet]
    have hmem : airyNode 0 ∈ Ioo (a₁ - r') (a₁ + r') := by
      rw [airyNode_zero]; exact ⟨by linarith, by linarith⟩
    refine le_of_eq ?_
    rw [tsum_eq_single 0]
    · rw [smul_apply, Measure.dirac_apply_of_mem hmem, smul_eq_mul, mul_one]
    · intro k hk
      have hk1 : airyNode k ≤ airyNode 1 := airyNode_strictAnti.antitone (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk))
      have h2 : airyNode 1 < airyNode 0 := airyNode_strictAnti zero_lt_one
      have hn1 : airyNode 1 = airyZero 2 := rfl
      have hn0 : airyNode 0 = airyZero 1 := airyNode_zero
      have hnot : airyNode k ∉ Ioo (a₁ - r') (a₁ + r') := by
        intro hm
        have hd : |airyZero 1 - airyZero 2| = airyZero 1 - airyZero 2 :=
          abs_of_pos (by rw [← hn0, ← hn1]; linarith)
        have : a₁ - r' < airyNode k := hm.1
        dsimp [a₁] at this
        linarith [hd]
      simp [Measure.dirac_apply' _ isOpen_Ioo.measurableSet, Set.indicator, hnot]
  have hsub_lo : Icc (a₁ - r₀) (a₁ + r₀) ⊆ Ioo (a₁ - r) (a₁ + r) := fun u hu => by
    have hr₀_le : r₀ ≤ r / 2 := min_le_left _ _
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hsub_mid : Ioo (a₁ - r) (a₁ + r) ⊆ Icc (a₁ - r) (a₁ + r) := Ioo_subset_Icc_self
  have hlim_bd : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      w₀ - ε ≤ (μ j (Ioo (a₁ - r) (a₁ + r))).toReal ∧
      (μ j (Icc (a₁ - r) (a₁ + r))).toReal ≤ w₀ + ε := by
    intro ε hε
    have hup := vague_limsup_le hν isCompact_Icc isOpen_Ioo hCU hw₀.le hμA_U hε
    filter_upwards [hlow.eventually (lt_mem_nhds (by linarith : w₀ - ε < w₀)), hup] with j h1 h2
    have hfin1 : μ j (Ioo (a₁ - r) (a₁ + r)) < ∞ :=
      lt_of_le_of_lt (measure_mono hsub_mid) isCompact_Icc.measure_lt_top
    have hmono1 : (μ j (Icc (a₁ - r₀) (a₁ + r₀))).toReal ≤ (μ j (Ioo (a₁ - r) (a₁ + r))).toReal :=
      ENNReal.toReal_mono hfin1.ne (measure_mono hsub_lo)
    exact ⟨by linarith, h2⟩
  refine ⟨Metric.tendsto_nhds.mpr fun ε hε => ?_, Metric.tendsto_nhds.mpr fun ε hε => ?_⟩
  · filter_upwards [hlim_bd (ε / 2) (half_pos hε)] with j ⟨hj1, hj2⟩
    have hfin2 : μ j (Icc (a₁ - r) (a₁ + r)) < ∞ := isCompact_Icc.measure_lt_top
    have hmono2 : (μ j (Ioo (a₁ - r) (a₁ + r))).toReal ≤ (μ j (Icc (a₁ - r) (a₁ + r))).toReal :=
      ENNReal.toReal_mono hfin2.ne (measure_mono hsub_mid)
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  · filter_upwards [hlim_bd (ε / 2) (half_pos hε)] with j ⟨hj1, hj2⟩
    have hfin2 : μ j (Icc (a₁ - r) (a₁ + r)) < ∞ := isCompact_Icc.measure_lt_top
    have hmono2 : (μ j (Ioo (a₁ - r) (a₁ + r))).toReal ≤ (μ j (Icc (a₁ - r) (a₁ + r))).toReal :=
      ENNReal.toReal_mono hfin2.ne (measure_mono hsub_mid)
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith

/-! ### 2. Near-optimal one-level first-moment bound (`dsl:hb-mass` at `(H_w)`) -/

/-- First-moment bound at the canonical one-level threshold `T_V(c_n)` (`dsl:hb-mass`, `(t - T_V)_+`):
specializes `hb_mass_first_moment` to `HermiteBiehlerData.airy` and arbitrary `0 < r < |a₁ - a₂|`. -/
theorem one_level_near_opt_first_moment (prob : FixedWeightProblem)
    {c η : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hη_nn : ∀ᶠ n in atTop, 0 ≤ η n)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0))
    {r : ℝ} (hr_pos : 0 < r) (hr_sep : r < |airyZero 1 - airyZero 2|) :
    ∃ C_r : ℝ, 0 < C_r ∧ ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (Ici (prob.T_V (c n) - η n))ᶜ = 0 →
        IntegrableOn (fun t => max (t - prob.T_V (c n)) 0 * spectralWeight prob (c n) t)
          {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - airyZero 1| ≤ r} meas.ν ∧
        ∫ t in {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - airyZero 1| ≤ r},
            max (t - prob.T_V (c n)) 0 * spectralWeight prob (c n) t ∂meas.ν ≤ C_r * η n := by
  let a : ℝ := (airyZero 2 + (airyZero 1 - r)) / 2
  let b : ℝ := airyZero 1 + r + 1
  have h12 : airyZero 2 < airyZero 1 := airyZero_lt_of_lt le_rfl (by omega)
  have habs12 : |airyZero 1 - airyZero 2| = airyZero 1 - airyZero 2 := abs_of_pos (sub_pos.mpr h12)
  have ha_lo : airyNode 1 < a := by
    have : airyNode 1 = airyZero 2 := rfl
    dsimp [a]; linarith
  have ha_hi : a < airyNode 0 := by
    rw [airyNode_zero]; dsimp [a]; linarith
  have ha_lt : a < airyZero 1 - r := by dsimp [a]; linarith
  have hb_gt : airyZero 1 + r < b := by dsimp [b]; linarith
  have hb_node : airyNode 0 < b := by rw [airyNode_zero]; dsimp [b]; linarith
  let CD : HbClusterData HermiteBiehlerData.airy := airyHbClusterData 1 le_rfl ha_lo ha_hi hb_node
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
  have hvag_near : ∀ (ν_seq : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0) →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo CD.a CD.b →
        Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k))) := by
    intro ν_seq hν g hg hcs hsupp
    have hν' : ∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧ meas.ν (Ici (prob.T_V (c n) - η n))ᶜ = 0 := by
      filter_upwards [hν] with n ⟨meas, h1, h2⟩
      refine ⟨meas, h1, ?_⟩
      rwa [hbPrescribedSet_airy_eq_empty, Set.empty_union, constrainedThreshold_empty] at h2
    exact near_opt_window_vague prob CD (fun _ => rfl) (fun _ => rfl) ha_lo hc hη_o ν_seq hν' hg hcs hsupp
  have hr_sep' : ∀ k : Fin CD.K, CD.z k ≠ HermiteBiehlerData.airy.tm → r < |CD.z k - HermiteBiehlerData.airy.tm| := by
    intro k hk
    have hk0 : k.1 = 0 := Nat.lt_one_iff.mp k.2
    exfalso; apply hk
    change airyNode k.1 = airyZero 1
    rw [hk0, airyNode_zero]
  obtain ⟨C_r, hCr_pos, h_ev⟩ := hb_mass_first_moment prob HermiteBiehlerData.airy CD hc hs_pos hs_tend
    hB_tend hη_nn hη_o hvag_near hr_pos ha_lt hb_gt hr_sep'
  refine ⟨C_r, hCr_pos, ?_⟩
  filter_upwards [h_ev] with n hn meas hν
  have hν' : meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0 := by
    simpa [hbPrescribedSet_airy_eq_empty, constrainedThreshold_empty, hB_eq n] using hν
  have hres := hn meas hν'
  simp only [hB_eq n] at hres
  exact hres

/-! ### 3. `dsl:near-opt-mass`: raw first-cluster mass for exponentially near-optimal spectra -/

/-- Helper: uniform prefactor ratio bound comparing `2π V(c/12, t) J_c(t)` and `2π V(c/12, B) J_c(B)`
via `cardyV_asymptotic_real` and continuity at `ξ_*`. -/
private lemma cardy_pref_ratio_tendsto (prob : FixedWeightProblem) {c B : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (hB : Tendsto (fun n => uAiry (c n) (B n)) atTop (𝓝 (airyZero 1)))
    (r : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t : ℝ, 0 < t → |uAiry (c n) t - airyZero 1| ≤ r →
      0 < prob.cardyV (c n / 12) (B n) ∧ 0 < jAiry (c n) (B n) ∧
      |((2 * Real.pi * prob.cardyV (c n / 12) t * jAiry (c n) t) /
          (2 * Real.pi * prob.cardyV (c n / 12) (B n) * jAiry (c n) (B n))) /
          Real.exp (c n * (2 * Real.pi / 3 * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B n / c n)))) - 1| ≤ ε := by
  intro ε hε
  let M : ℝ := |airyZero 1| + |r| + 1
  have hx0 : 0 < xiStar / 2 := half_pos xiStar_pos
  obtain ⟨C_V, _, hV_as⟩ := cardyV_asymptotic_real prob hx0
  obtain ⟨hq0_pos, -⟩ := nullPoly_exp_bounds prob hx0
  have hQ_pos : 0 < prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) := by
    have := (nullPoly_exp_bounds prob hx0).2 (x := xiStar) (by linarith [xiStar_pos])
    linarith [hq0_pos]
  let P_fn : ℝ → ℝ := fun x =>
    prob.nullPoly (Real.exp (-4 * Real.pi * x)) * (2 * Real.sqrt x * (2 * x) ^ (prob.w - 1))
  have hP_cont : Continuous P_fn := by
    have hQ_cont : Continuous (fun y : ℝ => prob.nullPoly (Real.exp (-4 * Real.pi * y))) := by
      have heq : (fun y : ℝ => prob.nullPoly (Real.exp (-4 * Real.pi * y))) =
          fun y : ℝ => (nullPolyExpC prob (Complex.ofReal y)).re := by
        ext y; exact congrArg Complex.re (nullPolyExpC_ofReal prob y).symm
      rw [heq]
      exact Complex.continuous_re.comp ((nullPolyExpC_entire prob).continuous.comp Complex.continuous_ofReal)
    exact hQ_cont.mul ((continuous_const.mul Real.continuous_sqrt).mul ((continuous_const.mul continuous_id).pow _))
  have hP_pos : 0 < P_fn xiStar := by
    have := xiStar_pos
    dsimp [P_fn]; positivity
  have hB_pos := eventually_pos_of_uAiry_tendsto hc hB
  let δ_main : ℝ := min (1 / 2) (ε / (4 * (1 + 2)))
  obtain ⟨δ_x, hδx_pos, hδx_uc⟩ := Metric.continuousAt_iff.mp hP_cont.continuousAt
    (P_fn xiStar * (δ_main / 4)) (by dsimp [δ_main]; positivity)
  have huc_err : ∀ᶠ n in atTop, M / (betaTip * (c n) ^ ((2 : ℝ) / 3)) < min (xiStar / 2) δ_x := by
    have hc23 : Tendsto (fun n => (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc
    have hm : Tendsto (fun n => M / betaTip * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (hc23.const_mul (M / betaTip))
    filter_upwards [hm.eventually (gt_mem_nhds (lt_min hx0 hδx_pos)), hc.eventually_gt_atTop 0] with n hn hcn
    have heq : M / betaTip * (c n) ^ (-(2 / 3 : ℝ)) = M / (betaTip * (c n) ^ ((2 : ℝ) / 3)) := by
      rw [Real.rpow_neg hcn.le]; ring
    linarith
  have hc_CV : Tendsto (fun n => C_V / c n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hc
  have h2M_ev : ∀ᶠ n in atTop, |uAiry (c n) (B n) - airyZero 1| ≤ 1 := by
    have := hB.eventually (Metric.ball_mem_nhds (airyZero 1) zero_lt_one)
    filter_upwards [this] with n hn
    rw [Real.dist_eq] at hn; exact hn.le
  let F_top : ℝ := 2 * Real.sqrt (3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1)
  have hF_top_pos : 0 < F_top := by
    have := xiStar_pos
    dsimp [F_top]; positivity
  filter_upwards [hc.eventually_ge_atTop (max 1 (24 * prob.totalShift)), hB_pos, huc_err, h2M_ev,
    hc_CV.eventually (gt_mem_nhds (show 0 < P_fn xiStar * (δ_main / 4) / F_top by
      dsimp [δ_main]; positivity))]
    with n hcm hBn huc hBM hCV t ht htu
  have hcn_pos : 0 < c n := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
  have hsh12 : prob.totalShift ≤ c n / 12 := by
    have := (le_max_right (1 : ℝ) (24 * prob.totalShift)).trans hcm; linarith
  refine ⟨prob.cardyV_pos hsh12 hBn, jAiry_pos hcn_pos hBn, ?_⟩
  have hbd_u : ∀ s : ℝ, |uAiry (c n) s - airyZero 1| ≤ max |r| 1 → |uAiry (c n) s| ≤ M := by
    intro s hs
    have htri : |uAiry (c n) s| ≤ |uAiry (c n) s - airyZero 1| + |airyZero 1| := by
      calc |uAiry (c n) s| = |(uAiry (c n) s - airyZero 1) + airyZero 1| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hm1 : max |r| 1 ≤ |r| + 1 :=
      max_le (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_left (abs_nonneg r))
    dsimp [M]; linarith
  have hx_diff : ∀ s : ℝ, |uAiry (c n) s| ≤ M →
      |Real.sqrt (3 * s / c n) - xiStar| < min (xiStar / 2) δ_x := by
    intro s hsM
    have hsub : Real.sqrt (3 * s / c n) - xiStar =
        -(uAiry (c n) s) / (betaTip * (c n) ^ ((2 : ℝ) / 3)) := by
      unfold uAiry
      have hp : (c n) ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn_pos _).ne'
      field_simp [betaTip_pos.ne', hp]
    rw [hsub, abs_div, abs_neg, abs_of_pos (mul_pos betaTip_pos (Real.rpow_pos_of_pos hcn_pos _))]
    have hdiv : |uAiry (c n) s| / (betaTip * (c n) ^ ((2 : ℝ) / 3)) ≤
        M / (betaTip * (c n) ^ ((2 : ℝ) / 3)) :=
      div_le_div_of_nonneg_right hsM (mul_pos betaTip_pos (Real.rpow_pos_of_pos hcn_pos _)).le
    exact lt_of_le_of_lt hdiv huc
  -- Factor `2π V(c/12, s) J(s)` cleanly at any `s > 0` with `x(s) ≥ xiStar / 2`:
  have hfac : ∀ s : ℝ, 0 < s → |uAiry (c n) s| ≤ M →
      ∃ F_s : ℝ,
        2 * Real.pi * prob.cardyV (c n / 12) s * jAiry (c n) s =
          (c n) ^ (-(1 / 6 : ℝ)) / (Real.sqrt 3 * betaTip) * F_s *
            Real.exp (c n * (2 * Real.pi * Real.sqrt (3 * s / c n) / 3)) ∧
        |F_s - P_fn xiStar| ≤ P_fn xiStar * (δ_main / 2) := by
    intro s hs hsM
    have hxd := hx_diff s hsM
    have hxs_lo : xiStar / 2 ≤ Real.sqrt (3 * s / c n) := by
      have := (abs_lt.mp (lt_of_lt_of_le hxd (min_le_left _ _))).1; linarith
    have hxs_pos : 0 < Real.sqrt (3 * s / c n) := lt_of_lt_of_le hx0 hxs_lo
    let xs : ℝ := Real.sqrt (3 * s / c n)
    have hs_eq : c n * xs ^ 2 / 3 = s := by
      dsimp [xs]; rw [Real.sq_sqrt (by positivity)]; field_simp [hcn_pos.ne']
    have hV_err := hV_as hcm hxs_lo
    rw [hs_eq] at hV_err
    let Q_s : ℝ := prob.cardyV (c n / 12) s /
      ((2 * xs) ^ (prob.w - 1) * besselAs (c n * (2 * Real.pi * xs / 3)))
    have hQ_cont_err : |prob.cardyV (c n / 12) s /
        ((2 * xs) ^ (prob.w - 1) * besselAs (c n * (2 * Real.pi * xs / 3))) -
        prob.nullPoly (Real.exp (-4 * Real.pi * xs))| ≤ C_V / c n := hV_err
    let F_s : ℝ := Q_s * (2 * Real.sqrt xs * (2 * xs) ^ (prob.w - 1))
    have hF_eq : 2 * Real.pi * prob.cardyV (c n / 12) s * jAiry (c n) s =
        (c n) ^ (-(1 / 6 : ℝ)) / (Real.sqrt 3 * betaTip) * F_s *
          Real.exp (c n * (2 * Real.pi * xs / 3)) := by
      have hc16 : (c n) ^ (1 / 3 : ℝ) / Real.sqrt (c n) = (c n) ^ (-(1 / 6 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hcn_pos.le, ← Real.rpow_add hcn_pos]
        congr 1; norm_num
      have hsqrt_b : Real.sqrt (2 * Real.pi * (c n * (2 * Real.pi * xs / 3))) =
          2 * Real.pi * Real.sqrt (c n) * Real.sqrt xs / Real.sqrt 3 := by
        have e1 : 2 * Real.pi * (c n * (2 * Real.pi * xs / 3)) =
            (2 * Real.pi) ^ 2 * (c n * xs) / 3 := by ring
        rw [e1, Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (by positivity), Real.sqrt_mul hcn_pos.le]
        ring
      have hbessel : besselAs (c n * (2 * Real.pi * xs / 3)) =
          Real.sqrt 3 / (2 * Real.pi * Real.sqrt (c n) * Real.sqrt xs) *
            Real.exp (c n * (2 * Real.pi * xs / 3)) := by
        unfold besselAs; rw [hsqrt_b, div_div_eq_mul_div]; ring
      have hj_eq : jAiry (c n) s = 2 * xs * (c n) ^ ((1 : ℝ) / 3) / (3 * betaTip) := rfl
      have hden_pos : 0 < (2 * xs) ^ (prob.w - 1) * besselAs (c n * (2 * Real.pi * xs / 3)) :=
        mul_pos (pow_pos (by positivity) _) (besselAs_pos (by positivity))
      dsimp [F_s, Q_s]
      rw [← hc16, hj_eq, hbessel]
      field_simp [hcn_pos.ne', hxs_pos.ne', Real.pi_ne_zero, betaTip_pos.ne',
        (Real.sqrt_pos.mpr hcn_pos).ne', (Real.sqrt_pos.mpr hxs_pos).ne',
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne',
        (Real.rpow_pos_of_pos hcn_pos ((1 : ℝ) / 3)).ne',
        (Real.exp_pos (c n * (2 * Real.pi * xs / 3))).ne',
        (pow_pos (by positivity : 0 < 2 * xs) (prob.w - 1)).ne']
      rw [Real.sq_sqrt hxs_pos.le, Real.sq_sqrt (by norm_num)]
      ring
    -- Bound `|F_s - P_fn xiStar| ≤ |Q_s - Q(e^{-4π xs})| * (...) + |P_fn xs - P_fn xiStar|`:
    have hP_xs := hδx_uc (by simpa [Real.dist_eq] using lt_of_lt_of_le hxd (min_le_right _ _))
    rw [Real.dist_eq] at hP_xs
    have hQ_xs_le : |Q_s - prob.nullPoly (Real.exp (-4 * Real.pi * xs))| ≤ C_V / c n := hQ_cont_err
    have hQ_diff : F_s - P_fn xs =
        (Q_s - prob.nullPoly (Real.exp (-4 * Real.pi * xs))) * (2 * Real.sqrt xs * (2 * xs) ^ (prob.w - 1)) := by
      dsimp [F_s, P_fn]; ring
    have h_tri : |F_s - P_fn xiStar| ≤ |F_s - P_fn xs| + |P_fn xs - P_fn xiStar| := by
      calc |F_s - P_fn xiStar| = |(F_s - P_fn xs) + (P_fn xs - P_fn xiStar)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h_mul_pos : 0 < 2 * Real.sqrt xs * (2 * xs) ^ (prob.w - 1) := by positivity
    -- Wait: to keep `(2 * √xs * (2xs)^{w-1}) * (C_V / c_n)` tiny without bounding `√xs (2xs)^{w-1}` with `w`,
    -- just compare `P_fn xiStar * (δ_main / 4)` using continuity / uniform bound on `[xiStar / 2, 3 * xiStar / 2]`!
    have hxs_hi : xs ≤ 3 * xiStar / 2 := by
      have := (abs_lt.mp (lt_of_lt_of_le hxd (min_le_left _ _))).2; linarith
    have h_factor_bd : 2 * Real.sqrt xs * (2 * xs) ^ (prob.w - 1) ≤ F_top := by
      have hsq_le : Real.sqrt xs ≤ Real.sqrt (3 * xiStar / 2) := Real.sqrt_le_sqrt hxs_hi
      have hxs2_pos : 0 < 2 * xs := by positivity
      have h2xs_hi : 2 * xs ≤ 3 * xiStar := by linarith
      have hrpow_le : (2 * xs) ^ (prob.w - 1) ≤ (3 * xiStar) ^ (prob.w - 1) :=
        pow_le_pow_left₀ hxs2_pos.le h2xs_hi _
      dsimp [F_top]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsq_le zero_le_two) hrpow_le (by positivity) (by positivity)
    have hF_xs_err : |F_s - P_fn xs| ≤ P_fn xiStar * (δ_main / 4) := by
      rw [hQ_diff, abs_mul, abs_of_pos h_mul_pos]
      have hmul := mul_le_mul hQ_xs_le h_factor_bd h_mul_pos.le (div_nonneg (by positivity) hcn_pos.le)
      have hlt' : (C_V / c n) * F_top ≤ P_fn xiStar * (δ_main / 4) :=
        ((lt_div_iff₀ hF_top_pos).mp hCV).le
      linarith
    refine ⟨F_s, hF_eq, by linarith⟩
  obtain ⟨F_t, hFt_eq, hFt_err⟩ := hfac t ht (hbd_u t (htu.trans ((le_abs_self r).trans (le_max_left _ _))))
  obtain ⟨F_B, hFB_eq, hFB_err⟩ := hfac (B n) hBn (hbd_u (B n) (hBM.trans (le_max_right _ _)))
  have hF_B_lo : P_fn xiStar / 2 ≤ F_B := by
    have hle := (abs_le.mp hFB_err).1
    have hd : δ_main / 2 ≤ 1 / 2 := by dsimp [δ_main]; linarith [min_le_left (1 / 2) (ε / (4 * (1 + 2)))]
    nlinarith [hP_pos]
  have hF_B_pos : 0 < F_B := lt_of_lt_of_le (half_pos hP_pos) hF_B_lo
  have hc16_ne : (c n) ^ (-(1 / 6 : ℝ)) / (Real.sqrt 3 * betaTip) ≠ 0 := by
    have := betaTip_pos; positivity
  have hexp_B_ne : Real.exp (c n * (2 * Real.pi * Real.sqrt (3 * B n / c n) / 3)) ≠ 0 := (Real.exp_pos _).ne'
  have hexp_diff_ne : Real.exp (c n * (2 * Real.pi / 3 * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B n / c n)))) ≠ 0 :=
    (Real.exp_pos _).ne'
  have hid : ((2 * Real.pi * prob.cardyV (c n / 12) t * jAiry (c n) t) /
      (2 * Real.pi * prob.cardyV (c n / 12) (B n) * jAiry (c n) (B n))) /
      Real.exp (c n * (2 * Real.pi / 3 * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B n / c n)))) =
      F_t / F_B := by
    rw [hFt_eq, hFB_eq]
    have hexp_div : Real.exp (c n * (2 * Real.pi * Real.sqrt (3 * t / c n) / 3)) /
        Real.exp (c n * (2 * Real.pi * Real.sqrt (3 * B n / c n) / 3)) =
        Real.exp (c n * (2 * Real.pi / 3 * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B n / c n)))) := by
      rw [← Real.exp_sub]; congr 1; ring
    calc ((c n ^ (-(1 / 6 : ℝ)) / (Real.sqrt 3 * betaTip) * F_t *
            Real.exp (c n * (2 * Real.pi * Real.sqrt (3 * t / c n) / 3))) /
          (c n ^ (-(1 / 6 : ℝ)) / (Real.sqrt 3 * betaTip) * F_B *
            Real.exp (c n * (2 * Real.pi * Real.sqrt (3 * B n / c n) / 3)))) /
          Real.exp (c n * (2 * Real.pi / 3 * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B n / c n))))
        = (F_t / F_B) *
            (Real.exp (c n * (2 * Real.pi * Real.sqrt (3 * t / c n) / 3)) /
              Real.exp (c n * (2 * Real.pi * Real.sqrt (3 * B n / c n) / 3))) /
            Real.exp (c n * (2 * Real.pi / 3 * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B n / c n)))) := by
          field_simp [hc16_ne, hF_B_pos.ne', hexp_B_ne, hexp_diff_ne, betaTip_pos.ne']
      _ = F_t / F_B := by
          rw [hexp_div]
          field_simp [hexp_diff_ne]
  rw [hid]
  have hsub : |F_t / F_B - 1| = |F_t - F_B| / F_B := by
    rw [show F_t / F_B - 1 = (F_t - F_B) / F_B by field_simp [hF_B_pos.ne'], abs_div, abs_of_pos hF_B_pos]
  rw [hsub]
  have hFB_tri : |F_t - F_B| ≤ |F_t - P_fn xiStar| + |F_B - P_fn xiStar| := by
    calc |F_t - F_B| = |(F_t - P_fn xiStar) - (F_B - P_fn xiStar)| := by ring_nf
      _ ≤ |F_t - P_fn xiStar| + |F_B - P_fn xiStar| := abs_sub _ _
  calc |F_t - F_B| / F_B ≤ (P_fn xiStar * δ_main) / (P_fn xiStar / 2) :=
        div_le_div₀ (by positivity) (by linarith) (half_pos hP_pos) hF_B_lo
    _ = 2 * δ_main := by field_simp [hP_pos.ne']
    _ ≤ ε := by dsimp [δ_main]; linarith [min_le_right (1 / 2) (ε / (4 * (1 + 2)))]

/-- Convexity bound on `[0, D]`: for `0 ≤ y ≤ D`, `exp(y) - 1 ≤ (exp(D) / D) * y` whenever `0 < D`. -/
private lemma exp_sub_one_le_div_mul {y D : ℝ} (hy0 : 0 ≤ y) (hyD : y ≤ D) (hD : 0 < D) :
    Real.exp y - 1 ≤ (Real.exp D / D) * y := by
  by_cases hyz : y = 0
  · rw [hyz, Real.exp_zero, sub_self, mul_zero]
  let θ : ℝ := y / D
  have hθ0 : 0 ≤ θ := div_nonneg hy0 hD.le
  have hθ1 : θ ≤ 1 := (div_le_one hD).mpr hyD
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ D)
    (sub_nonneg.mpr hθ1) hθ0 (by ring)
  have hpt : (1 - θ) • (0 : ℝ) + θ • D = y := by
    simp [θ, hD.ne']
  rw [hpt, smul_eq_mul, smul_eq_mul, Real.exp_zero, mul_one] at hconv
  have h1 : Real.exp y - 1 ≤ θ * (Real.exp D - 1) := by linarith
  have h2 : Real.exp D - 1 ≤ Real.exp D := by linarith
  calc Real.exp y - 1 ≤ θ * (Real.exp D - 1) := h1
    _ ≤ θ * Real.exp D := mul_le_mul_of_nonneg_left h2 hθ0
    _ = (Real.exp D / D) * y := by dsimp [θ]; ring

private lemma one_level_d1_exact (prob : FixedWeightProblem) {r γ : ℝ}
    (hr_pos : 0 < r) (hr_sep : r < |airyZero 1 - airyZero 2|)
    (hγ : 2 * Real.pi * r / (3 * betaTip) < γ)
    {c η : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hη_bd : ∀ᶠ n in atTop, 0 ≤ η n ∧ η n ≤ Real.exp (-γ * (c n) ^ ((1 : ℝ) / 3)))
    (ν_seq : ℕ → Measure ℝ)
    (hν : ∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
      ν_seq n = meas.ν ∧ meas.ν (Ici (prob.T_V (c n) - η n))ᶜ = 0) :
    Tendsto (fun n => (ν_seq n {t : ℝ | |uAiry (c n) t - airyZero 1| < r}).toReal /
        (2 * Real.pi * prob.cardyV (c n / 12) (prob.T_V (c n)) *
          jAiry (c n) (prob.T_V (c n))))
      atTop (𝓝 (airyNodeWeight 0)) := by
  classical
  have hγ_pos : 0 < γ := lt_of_le_of_lt (by have := betaTip_pos; positivity) hγ
  have hη_nn : ∀ᶠ n in atTop, 0 ≤ η n := hη_bd.mono fun _ h => h.1
  have hη_tend0 : Tendsto η atTop (𝓝 0) := by
    have hpow : Tendsto (fun n => (c n) ^ ((1 : ℝ) / 3)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc
    have hexp0 : Tendsto (fun n => Real.exp (-γ * (c n) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
      have hneg : Tendsto (fun n => -γ * (c n) ^ ((1 : ℝ) / 3)) atTop atBot :=
        (Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hγ_pos) hpow)
      exact Real.tendsto_exp_atBot.comp hneg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp0
      hη_nn (hη_bd.mono fun _ h => h.2)
  have hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
    have hc13 : Tendsto (fun n => (c n) ^ ((1 : ℝ) / 3)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc
    simpa using hη_tend0.div_atTop hc13
  have hvag := near_opt_isVagueLimit prob hc hη_o hν
  -- Shifted index `N₀` where `spectralMeasure prob (c n) (ν_seq n)` is locally finite:
  have hτ_pos : ∀ᶠ n in atTop, 0 < prob.T_V (c n) - η n := by
    obtain ⟨c₁, D, -, _, hlo⟩ := fixedWeightLowerBoundInput_of_problem prob
    have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
    have hA : 0 ≤ Aopt := by unfold Aopt; have := cStar_pos; positivity
    filter_upwards [hc.eventually_ge_atTop c₁, hc.eventually_gt_atTop 0,
      hη_tend0.eventually (gt_mem_nhds zero_lt_one),
      (Tendsto.const_mul_atTop hxi hc).eventually_gt_atTop (1 + D)] with n hcn hcpos hη1 hTb
    have htv := hlo hcn
    have hAc : 0 ≤ Aopt * (c n) ^ ((1 : ℝ) / 3) := mul_nonneg hA (Real.rpow_pos_of_pos hcpos _).le
    unfold TStar at htv; linarith
  have hev_setup : ∀ᶠ n in atTop,
      0 < c n ∧ prob.totalShift ≤ c n / 12 ∧ 0 < prob.T_V (c n) - η n ∧
      ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧ meas.ν (Ici (prob.T_V (c n) - η n))ᶜ = 0 :=
    ((hc.eventually_gt_atTop 0).and ((hc.eventually_ge_atTop (12 * prob.totalShift)).mono
      (fun _ h => by linarith))).and (hτ_pos.and hν) |>.mono fun n ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ =>
      ⟨h1, h2, h3, h4⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev_setup
  let μ_sh : ℕ → Measure ℝ := fun j => spectralMeasure prob (c (j + N₀)) (ν_seq (j + N₀))
  have hμ_loc : ∀ j, IsLocallyFiniteMeasure (μ_sh j) := fun j => by
    have h := hN₀ (j + N₀) (Nat.le_add_left N₀ j)
    obtain ⟨meas, h1, h2⟩ := h.2.2.2
    have hgap : IsAtGap meas (prob.T_V (c (j + N₀)) - η (j + N₀)) :=
      measure_mono_null (fun _ ht => not_le.mpr ht) h2
    dsimp [μ_sh]
    rw [h1]
    exact isLocallyFiniteMeasure_spectralMeasure prob h.1 h.2.1 meas h.2.2.1 hgap
  have hvag_sh : IsVagueLimit atTop μ_sh airyMeasure := fun g hg hcs =>
    (tendsto_add_atTop_iff_nat N₀).mpr (hvag g hg hcs)
  have hwin_mass_sh := vague_first_node_mass_of_lt hvag_sh hr_pos hr_sep
  have hμ_Ioo_tend : Tendsto (fun n => (spectralMeasure prob (c n) (ν_seq n)
      (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal) atTop (𝓝 (airyNodeWeight 0)) :=
    (tendsto_add_atTop_iff_nat N₀).mp hwin_mass_sh.1
  -- Moment bound + parameters for exponential error on `[T_V - η, ∞)`:
  obtain ⟨C_r, hCr_pos, h_mom⟩ := one_level_near_opt_first_moment prob hc hη_nn hη_o hr_pos hr_sep
  let γ' : ℝ := (2 * Real.pi * r / (3 * betaTip) + γ) / 2
  have hγ'_lo : 2 * Real.pi * r / (3 * betaTip) < γ' := by dsimp [γ']; linarith
  have hγ'_hi : γ' < γ := by dsimp [γ']; linarith
  have hγ'_pos : 0 < γ' := lt_of_le_of_lt (by have := betaTip_pos; positivity) hγ'_lo
  let δ_u : ℝ := (γ' - 2 * Real.pi * r / (3 * betaTip)) * (3 * betaTip) / (2 * Real.pi)
  have hδu_pos : 0 < δ_u := by have := betaTip_pos; dsimp [δ_u]; positivity
  have hB_tend := uAiry_T_V_tendsto prob hc
  have hpref := cardy_pref_ratio_tendsto prob hc hB_tend r
  obtain ⟨t_c0, _, ht_bds⟩ := uAiry_window_t_bounds (show 0 ≤ |airyZero 1| + r by positivity)
  have hu_t_bds := fun {n t : ℝ} (hc_ge : t_c0 ≤ n) (htp : 0 < t)
      (htu : |uAiry n t - airyZero 1| ≤ r) =>
    ht_bds hc_ge htp (by
      calc |uAiry n t| = |(uAiry n t - airyZero 1) + airyZero 1| := by ring_nf
        _ ≤ |uAiry n t - airyZero 1| + |airyZero 1| := abs_add_le _ _
        _ ≤ |airyZero 1| + r := by linarith)
  have h_B_u_bds := fun {n : ℕ} (hc_ge : t_c0 ≤ c n) (hBp : 0 < prob.T_V (c n))
      (hBu : |uAiry (c n) (prob.T_V (c n)) - airyZero 1| ≤ r) =>
    ht_bds hc_ge hBp (by
      calc |uAiry (c n) (prob.T_V (c n))| =
            |(uAiry (c n) (prob.T_V (c n)) - airyZero 1) + airyZero 1| := by ring_nf
        _ ≤ _ := (abs_add_le _ _).trans (by linarith))
  -- Main `dsl:D1-exact` convergence:
  rw [Metric.tendsto_nhds]
  intro ε hε
  let w₀ : ℝ := airyNodeWeight 0
  have hw₀_pos : 0 < w₀ := airyNodeWeight_pos 0
  let ε_m : ℝ := min (ε / 4) (min (w₀ / 2) 1)
  let ε_p : ℝ := min (1 / 2) (ε / (4 * (w₀ + 2)))
  let C_exp : ℝ := (3 * betaTip / (2 * Real.pi * r)) * (2 * Real.pi / xiStar) * C_r + 1
  have hCexp_pos : 0 < C_exp := by have := betaTip_pos; have := xiStar_pos; dsimp [C_exp]; positivity
  have hpow_atTop : Tendsto (fun n => (c n) ^ ((1 : ℝ) / 3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc
  have h_exp_decay : Tendsto (fun n => Real.exp (-(γ - γ') * (c n) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg (by linarith) hpow_atTop)
  have h_lin_decay : Tendsto (fun n => η n * (2 * Real.pi / xiStar)) atTop (𝓝 0) := by
    simpa using hη_tend0.mul tendsto_const_nhds
  have hB_pos := eventually_pos_of_uAiry_tendsto hc hB_tend
  filter_upwards [hc.eventually_ge_atTop (max t_c0 (max 1 (12 * prob.totalShift))), hB_pos,
    hτ_pos, hν, hη_bd, h_mom, hpref ε_p (by positivity),
    hB_tend.eventually (Metric.ball_mem_nhds (airyZero 1) (lt_min hr_pos hδu_pos)),
    hμ_Ioo_tend.eventually (Metric.ball_mem_nhds w₀ (by positivity : 0 < ε_m)),
    h_exp_decay.eventually (gt_mem_nhds (by positivity : 0 < ε / (8 * (1 + C_exp)))),
    h_lin_decay.eventually (gt_mem_nhds (by positivity : 0 < ε / (8 * (w₀ + 2)))),
    hpow_atTop.eventually_ge_atTop 1]
    with n hc_ge hBn hτp hν_n hη_n hmom_n hpref_n hBu hμ_n hdec_n hlin_n hc13_ge
  obtain ⟨meas, hν_eq, hν_supp⟩ := hν_n
  rw [hν_eq]
  have hmom_m := hmom_n meas hν_supp
  have hcn_pos : 0 < c n := by
    linarith [le_max_left (1 : ℝ) (12 * prob.totalShift), le_max_right t_c0 (max 1 (12 * prob.totalShift))]
  have hsh12 : prob.totalShift ≤ c n / 12 := by
    have := (le_max_right (1 : ℝ) (12 * prob.totalShift)).trans ((le_max_right t_c0 _).trans hc_ge)
    linarith
  have htc0 : t_c0 ≤ c n := (le_max_left _ _).trans hc_ge
  let B : ℝ := prob.T_V (c n)
  let W_op : Set ℝ := {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - airyZero 1| < r}
  let W_cl : Set ℝ := {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - airyZero 1| ≤ r}
  have hW_op_eq_pre : W_op = uAiry (c n) ⁻¹' Ioo (airyZero 1 - r) (airyZero 1 + r) ∩ Ioi 0 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_ofPred_eq, abs_lt, W_op]
    exact ⟨fun h => ⟨⟨by linarith [h.2.1], by linarith [h.2.2]⟩, h.1⟩,
      fun h => ⟨h.2, ⟨by linarith [h.1.1], by linarith [h.1.2]⟩⟩⟩
  have hW_cl_eq_pre : W_cl = uAiry (c n) ⁻¹' Icc (airyZero 1 - r) (airyZero 1 + r) ∩ Ioi 0 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_ofPred_eq, abs_le, W_cl]
    exact ⟨fun h => ⟨⟨by linarith [h.2.1], by linarith [h.2.2]⟩, h.1⟩,
      fun h => ⟨h.2, ⟨by linarith [h.1.1], by linarith [h.1.2]⟩⟩⟩
  have hW_ae : ({t : ℝ | |uAiry (c n) t - airyZero 1| < r} : Set ℝ) =ᵐ[meas.ν] W_op := by
    have hae_pos : ∀ᵐ t ∂meas.ν, 0 < t := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν_supp] with t ht
      exact lt_of_lt_of_le hτp (not_not.mp ht)
    filter_upwards [hae_pos] with t ht
    simp only [Set.mem_ofPred_eq, W_op, Set.mem_Ioi]
    exact ⟨fun h => ⟨ht, h⟩, fun h => h.2⟩
  have hν_W_eq : meas.ν {t : ℝ | |uAiry (c n) t - airyZero 1| < r} = meas.ν W_op :=
    measure_congr hW_ae
  rw [hν_W_eq]
  have hW_op_m : MeasurableSet W_op := by
    rw [hW_op_eq_pre]
    exact ((continuous_uAiry (c n)).measurable isOpen_Ioo.measurableSet).inter measurableSet_Ioi
  have hW_sub_bd : ∀ t ∈ W_op, c n * (xiStar / 2) ^ 2 / 3 ≤ t ∧ t ≤ c n * (3 * xiStar / 2) ^ 2 / 3 :=
    fun t ht => hu_t_bds htc0 ht.1 ht.2.le
  let t_lo := c n * (xiStar / 2) ^ 2 / 3
  let t_hi := c n * (3 * xiStar / 2) ^ 2 / 3
  have ht_lo_pos : 0 < t_lo := by have := xiStar_pos; dsimp [t_lo]; positivity
  have ht_le : t_lo ≤ t_hi := by
    have := xiStar_pos; dsimp [t_lo, t_hi]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sq_le_sq' (by linarith) (by linarith)) hcn_pos.le) (by norm_num)
  have hW_sub_Icc : W_op ⊆ Icc t_lo t_hi := fun t ht => hW_sub_bd t ht
  have hν_W_fin : meas.ν W_op < ∞ :=
    lt_of_le_of_lt (measure_mono (hW_sub_Icc.trans (Icc_subset_Icc ht_lo_pos.le le_rfl)))
      (measure_Icc_lt_top meas t_hi)
  have hsw_int : IntegrableOn (spectralWeight prob (c n)) W_op meas.ν := by
    simpa using integrableOn_spectralWeight_mul_of_continuousOn prob hcn_pos hsh12 ht_lo_pos ht_le meas
      hW_op_m hW_sub_Icc (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) _)
  have hμ_eq_int : (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal =
      ∫ t in W_op, spectralWeight prob (c n) t ∂meas.ν := by
    rw [spectralMeasure_apply prob (c n) meas.ν isOpen_Ioo.measurableSet, ← hW_op_eq_pre]
    have hsm_eq : ∫⁻ t in W_op, spectralDensity prob (c n) t ∂meas.ν =
        ENNReal.ofReal (∫ t in W_op, spectralWeight prob (c n) t ∂meas.ν) := by
      refine (ofReal_integral_eq_lintegral_ofReal hsw_int ?_).symm
      filter_upwards [ae_restrict_mem hW_op_m] with t ht
      exact (spectralWeight_pos hcn_pos hsh12 ht.1).le
    rw [hsm_eq, ENNReal.toReal_ofReal (setIntegral_nonneg hW_op_m fun t ht =>
      (spectralWeight_pos hcn_pos hsh12 ht.1).le)]
  let ρJ : ℝ → ℝ := fun t => 2 * Real.pi * prob.cardyV (c n / 12) t * jAiry (c n) t
  have hBu_r : |uAiry (c n) B - airyZero 1| ≤ r := by
    rw [Real.dist_eq] at hBu
    exact (lt_of_lt_of_le hBu (min_le_left _ _)).le
  have hV_pos : 0 < prob.cardyV (c n / 12) B := (hpref_n B hBn hBu_r).1
  have hJ_pos : 0 < jAiry (c n) B := jAiry_pos hcn_pos hBn
  have hρJB_pos : 0 < ρJ B := by dsimp [ρJ]; positivity
  have hρJ_cont : Continuous ρJ := by
    dsimp [ρJ]; exact (continuous_const.mul (continuous_cardyV prob (c n / 12))).mul (continuous_jAiry (c n))
  have hρJ_ratio_eq : (meas.ν W_op).toReal / ρJ B =
      ∫ t in W_op, (ρJ t / ρJ B) * spectralWeight prob (c n) t ∂meas.ν := by
    have hid_ae : ∀ t ∈ W_op, (ρJ t / ρJ B) * spectralWeight prob (c n) t = (ρJ B)⁻¹ := fun t ht => by
      have hV := prob.cardyV_pos hsh12 ht.1
      have hJ := jAiry_pos hcn_pos ht.1
      dsimp [ρJ, spectralWeight]; field_simp [hV.ne', hJ.ne', hρJB_pos.ne']
    rw [setIntegral_congr_fun hW_op_m hid_ae, setIntegral_const, smul_eq_mul, Measure.real]
    ring
  have hratio_int : IntegrableOn (fun t => (ρJ t / ρJ B) * spectralWeight prob (c n) t) W_op meas.ν :=
    integrableOn_spectralWeight_mul_of_continuousOn prob hcn_pos hsh12 ht_lo_pos ht_le meas
      hW_op_m hW_sub_Icc ((hρJ_cont.div_const (ρJ B)).continuousOn)
  have hsub_int : (meas.ν W_op).toReal / ρJ B -
      (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal =
      ∫ t in W_op, (ρJ t / ρJ B - 1) * spectralWeight prob (c n) t ∂meas.ν := by
    rw [hρJ_ratio_eq, hμ_eq_int, ← integral_sub hratio_int hsw_int]
    refine setIntegral_congr_fun hW_op_m fun t _ => by ring
  let y : ℝ → ℝ := fun t => c n * (2 * Real.pi / 3 * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B / c n)))
  let P_r : ℝ → ℝ := fun t => (ρJ t / ρJ B) / Real.exp (y t)
  have hP_err : ∀ t ∈ W_op, |P_r t - 1| ≤ ε_p := fun t ht => (hpref_n t ht.1 ht.2.le).2.2
  have h_diff_split : ∀ t ∈ W_op, |ρJ t / ρJ B - 1| ≤ ε_p * (1 + |Real.exp (y t) - 1|) + |Real.exp (y t) - 1| := by
    intro t ht
    have hid1 : ρJ t / ρJ B - 1 = (P_r t - 1) * Real.exp (y t) + (Real.exp (y t) - 1) := by
      have he : Real.exp (y t) ≠ 0 := (Real.exp_pos _).ne'
      dsimp [P_r]; field_simp [he]; ring
    have h1 : |Real.exp (y t)| ≤ 1 + |Real.exp (y t) - 1| := by
      rw [abs_of_pos (Real.exp_pos _)]
      have := le_abs_self (Real.exp (y t) - 1)
      linarith
    calc |ρJ t / ρJ B - 1|
        ≤ |(P_r t - 1) * Real.exp (y t)| + |Real.exp (y t) - 1| := by rw [hid1]; exact abs_add_le _ _
      _ = |P_r t - 1| * |Real.exp (y t)| + |Real.exp (y t) - 1| := by rw [abs_mul]
      _ ≤ ε_p * (1 + |Real.exp (y t) - 1|) + |Real.exp (y t) - 1| := by
          gcongr; exact hP_err t ht
  -- Now bound `|exp(y t) - 1|` on `W_op ∩ Ici (B - η n)` uniformly by a single linear+`(t - B)_+` bound!
  let M_exp : ℝ := Real.exp (γ' * (c n) ^ ((1 : ℝ) / 3)) * (3 * betaTip / (2 * Real.pi * r)) *
    (2 * Real.pi / xiStar)
  have hM_exp_nn : 0 ≤ M_exp := by have := betaTip_pos; have := xiStar_pos; dsimp [M_exp]; positivity
  have hy_pt_bd : ∀ t ∈ W_op, B - η n ≤ t →
      |Real.exp (y t) - 1| ≤ (2 * Real.pi / xiStar) * η n + M_exp * max (t - B) 0 := by
    intro t ht hBt
    have ht_bds := hW_sub_bd t ht
    have hBu_bd : |uAiry (c n) B - airyZero 1| < r := by
      rw [Real.dist_eq] at hBu; exact lt_of_lt_of_le hBu (min_le_left _ _)
    have hB_bds := h_B_u_bds htc0 hBn hBu_bd.le
    have hxt_lo : xiStar / 2 ≤ Real.sqrt (3 * t / c n) := by
      have h2 : (xiStar / 2) ^ 2 ≤ 3 * t / c n := by rw [le_div_iff₀ hcn_pos]; linarith [ht_bds.1]
      simpa [Real.sqrt_sq (by have := xiStar_pos; positivity : 0 ≤ xiStar / 2)] using Real.sqrt_le_sqrt h2
    have hxB_lo : xiStar / 2 ≤ Real.sqrt (3 * B / c n) := by
      have h2 : (xiStar / 2) ^ 2 ≤ 3 * B / c n := by rw [le_div_iff₀ hcn_pos]; linarith [hB_bds.1]
      simpa [Real.sqrt_sq (by have := xiStar_pos; positivity : 0 ≤ xiStar / 2)] using Real.sqrt_le_sqrt h2
    have hx_sum_lo : xiStar ≤ Real.sqrt (3 * t / c n) + Real.sqrt (3 * B / c n) := by linarith
    have hy_eq : y t = (2 * Real.pi / (Real.sqrt (3 * t / c n) + Real.sqrt (3 * B / c n))) * (t - B) := by
      have hsq : Real.sqrt (3 * t / c n) ^ 2 - Real.sqrt (3 * B / c n) ^ 2 = 3 * (t - B) / c n := by
        rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) ht.1.le) hcn_pos.le),
          Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hBn.le) hcn_pos.le)]
        field_simp [hcn_pos.ne']; ring
      have hdiff : Real.sqrt (3 * t / c n) - Real.sqrt (3 * B / c n) =
          (3 * (t - B) / c n) / (Real.sqrt (3 * t / c n) + Real.sqrt (3 * B / c n)) := by
        apply eq_div_of_mul_eq (by linarith only [xiStar_pos, hx_sum_lo] :
          Real.sqrt (3 * t / c n) + Real.sqrt (3 * B / c n) ≠ 0)
        linarith only [hsq, show (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B / c n)) *
          (Real.sqrt (3 * t / c n) + Real.sqrt (3 * B / c n)) =
          Real.sqrt (3 * t / c n) ^ 2 - Real.sqrt (3 * B / c n) ^ 2 by ring]
      dsimp [y]; rw [hdiff]; field_simp [hcn_pos.ne']
    by_cases hlt : t < B
    · have hy_np : y t ≤ 0 := by
        rw [hy_eq]
        exact mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg (by positivity) (by linarith only [xiStar_pos, hx_sum_lo]))
          (by linarith only [hlt])
      have h_exp_le : Real.exp (y t) ≤ 1 := Real.exp_le_one_iff.mpr hy_np
      have h_add_one : y t + 1 ≤ Real.exp (y t) := Real.add_one_le_exp (y t)
      have h_abs_exp : |Real.exp (y t) - 1| ≤ -y t := by
        rw [abs_of_nonpos (sub_nonpos.mpr h_exp_le)]
        linarith only [h_add_one]
      have h_neg_y : -y t ≤ (2 * Real.pi / xiStar) * η n := by
        have hden : 2 * Real.pi / (Real.sqrt (3 * t / c n) + Real.sqrt (3 * B / c n)) ≤ 2 * Real.pi / xiStar :=
          div_le_div_of_nonneg_left (by positivity) xiStar_pos hx_sum_lo
        have hneg : -y t = (2 * Real.pi / (Real.sqrt (3 * t / c n) + Real.sqrt (3 * B / c n))) * (-(t - B)) := by
          rw [hy_eq]; ring
        rw [hneg]
        exact mul_le_mul hden (by linarith only [hBt]) (by linarith only [hlt]) (div_nonneg (by positivity) xiStar_pos.le)
      have hmax : 0 ≤ M_exp * max (t - B) 0 := mul_nonneg hM_exp_nn (le_max_right _ _)
      linarith only [h_abs_exp, h_neg_y, hmax]
    · have hge : B ≤ t := le_of_not_gt hlt
      have hy_nn : 0 ≤ y t := by
        rw [hy_eq]
        exact mul_nonneg (div_nonneg (by positivity) (by linarith only [xiStar_pos, hx_sum_lo]))
          (sub_nonneg.mpr hge)
      have hy_u : y t = (2 * Real.pi / (3 * betaTip)) * (uAiry (c n) B - uAiry (c n) t) * (c n) ^ ((1 : ℝ) / 3) := by
        have hpow : (c n) ^ ((2 : ℝ) / 3) * (c n) ^ ((1 : ℝ) / 3) = c n := by
          rw [← Real.rpow_add hcn_pos]; norm_num
        have hxu : uAiry (c n) B - uAiry (c n) t =
            betaTip * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B / c n)) * (c n) ^ ((2 : ℝ) / 3) := by
          unfold uAiry; ring
        dsimp [y]; rw [hxu]
        have : betaTip * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B / c n)) * (c n) ^ ((2 : ℝ) / 3) *
            (c n) ^ ((1 : ℝ) / 3) = betaTip * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B / c n)) * c n := by
          rw [mul_assoc, hpow]
        calc c n * (2 * Real.pi / 3 * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B / c n)))
            = (2 * Real.pi / (3 * betaTip)) *
                (betaTip * (Real.sqrt (3 * t / c n) - Real.sqrt (3 * B / c n)) * c n) := by
              field_simp [betaTip_pos.ne']
          _ = _ := by rw [← this]; ring
      have hBu_δ : |uAiry (c n) B - airyZero 1| < δ_u := by
        rw [Real.dist_eq] at hBu; exact lt_of_lt_of_le hBu (min_le_right _ _)
      have hu_diff_le : uAiry (c n) B - uAiry (c n) t ≤ r + δ_u := by
        linarith only [(abs_lt.mp hBu_δ).2, (abs_lt.mp ht.2).1]
      have hc13_pos : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hcn_pos _
      let D_u : ℝ := γ' * (c n) ^ ((1 : ℝ) / 3)
      have hy_le_D : y t ≤ D_u := by
        have heq_γ' : (2 * Real.pi / (3 * betaTip)) * (r + δ_u) = γ' := by
          dsimp [δ_u]; field_simp [betaTip_pos.ne', Real.pi_ne_zero]; ring
        calc y t ≤ (2 * Real.pi / (3 * betaTip)) * (r + δ_u) * (c n) ^ ((1 : ℝ) / 3) := by
              rw [hy_u]; gcongr; exact (by have := betaTip_pos; positivity)
          _ = D_u := by rw [heq_γ']
      have hD_lo : (2 * Real.pi * r / (3 * betaTip)) ≤ D_u := by
        calc 2 * Real.pi * r / (3 * betaTip) = (2 * Real.pi * r / (3 * betaTip)) * 1 := by ring
          _ ≤ γ' * (c n) ^ ((1 : ℝ) / 3) := mul_le_mul hγ'_lo.le hc13_ge zero_le_one hγ'_pos.le
      have hD_pos : 0 < D_u := lt_of_lt_of_le (by have := betaTip_pos; positivity) hD_lo
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hy_nn))]
      have h1 := exp_sub_one_le_div_mul hy_nn hy_le_D hD_pos
      have hy_ub : y t ≤ (2 * Real.pi / xiStar) * (t - B) := by
        rw [hy_eq]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) xiStar_pos hx_sum_lo)
          (sub_nonneg.mpr hge)
      have h_inv_D : 1 / D_u ≤ 3 * betaTip / (2 * Real.pi * r) :=
        (one_div_le_one_div_of_le (by have := betaTip_pos; positivity) hD_lo).trans_eq (by field_simp)
      have h_term : Real.exp (y t) - 1 ≤ M_exp * max (t - B) 0 := by
        rw [max_eq_left (sub_nonneg.mpr hge)]
        have h_coeff_nn : 0 ≤ Real.exp D_u * (3 * betaTip / (2 * Real.pi * r)) := by
          have := betaTip_pos; positivity
        calc Real.exp (y t) - 1 ≤ (Real.exp D_u / D_u) * y t := h1
          _ = Real.exp D_u * (1 / D_u) * y t := by ring
          _ ≤ Real.exp D_u * (3 * betaTip / (2 * Real.pi * r)) * ((2 * Real.pi / xiStar) * (t - B)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h_inv_D (Real.exp_pos D_u).le) hy_ub hy_nn h_coeff_nn
          _ = M_exp * (t - B) := by dsimp [D_u, M_exp]; ring
      have hlin_nn : 0 ≤ (2 * Real.pi / xiStar) * η n := mul_nonneg (div_nonneg (by positivity) xiStar_pos.le) hη_n.1
      linarith only [h_term, hlin_nn]
  -- Integrate the combined pointwise error bound over `W_op`:
  have hW_op_sub_cl : W_op ⊆ W_cl := fun _ ht => ⟨ht.1, ht.2.le⟩
  have hW_cl_m : MeasurableSet W_cl := by
    rw [hW_cl_eq_pre]
    exact ((continuous_uAiry (c n)).measurable isClosed_Icc.measurableSet).inter measurableSet_Ioi
  have hm_int_W : IntegrableOn (fun t => max (t - B) 0 * spectralWeight prob (c n) t) W_op meas.ν :=
    hmom_m.1.mono_set hW_op_sub_cl
  have hm_int_le : ∫ t in W_op, max (t - B) 0 * spectralWeight prob (c n) t ∂meas.ν ≤ C_r * η n := by
    have hnn_cl : ∀ᵐ t ∂(meas.ν.restrict W_cl),
        0 ≤ max (t - B) 0 * spectralWeight prob (c n) t := by
      filter_upwards [ae_restrict_mem hW_cl_m] with t ht
      exact mul_nonneg (le_max_right _ _) (spectralWeight_pos hcn_pos hsh12 ht.1).le
    have hle := setIntegral_mono_set hmom_m.1 hnn_cl (Eventually.of_forall hW_op_sub_cl)
    exact hle.trans hmom_m.2
  have hexp_y_int : IntegrableOn (fun t => |Real.exp (y t) - 1| * spectralWeight prob (c n) t) W_op meas.ν := by
    refine Integrable.mono' ((hratio_int.const_mul 2).add hsw_int) ?_ ?_
    · have hy_meas : Measurable y := by
        have : Continuous y := by
          dsimp [y]
          exact continuous_const.mul (continuous_const.mul
            (((continuous_const.mul continuous_id').div_const (c n)).sqrt.sub continuous_const))
        exact this.measurable
      exact (((hy_meas.exp.sub measurable_const).abs.mul
        (measurable_spectralWeight prob (c n))).aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem hW_op_m] with t ht
      have hsw_nn := (spectralWeight_pos hcn_pos hsh12 ht.1).le
      have hexp_pos := Real.exp_pos (y t)
      have hP_pos' : 1 / 2 ≤ P_r t := by
        have h1 := (abs_le.mp (hP_err t ht)).1
        have h2 : ε_p ≤ 1 / 2 := min_le_left _ _
        linarith only [h1, h2]
      have hexp_le : Real.exp (y t) ≤ 2 * (ρJ t / ρJ B) := by
        have hid : P_r t * Real.exp (y t) = ρJ t / ρJ B := by
          dsimp [P_r]; field_simp [hexp_pos.ne']
        calc Real.exp (y t) = 2 * ((1 / 2) * Real.exp (y t)) := by ring
          _ ≤ 2 * (P_r t * Real.exp (y t)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP_pos' hexp_pos.le) zero_le_two
          _ = 2 * (ρJ t / ρJ B) := by rw [hid]
      have h1 : |Real.exp (y t) - 1| ≤ Real.exp (y t) + 1 :=
        (abs_sub _ _).trans_eq (by rw [abs_of_pos hexp_pos, abs_one])
      have hrhs_nn : 0 ≤ 2 * ((ρJ t / ρJ B) * spectralWeight prob (c n) t) + spectralWeight prob (c n) t := by
        have hρJt_pos : 0 < ρJ t := by
          dsimp [ρJ]; have := prob.cardyV_pos hsh12 ht.1; have := jAiry_pos hcn_pos ht.1; positivity
        have : 0 ≤ ρJ t / ρJ B := div_nonneg hρJt_pos.le hρJB_pos.le
        positivity
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hsw_nn)]
      dsimp only [Pi.add_apply]
      calc |Real.exp (y t) - 1| * spectralWeight prob (c n) t
          ≤ (Real.exp (y t) + 1) * spectralWeight prob (c n) t :=
            mul_le_mul_of_nonneg_right h1 hsw_nn
        _ ≤ (2 * (ρJ t / ρJ B) + 1) * spectralWeight prob (c n) t :=
            mul_le_mul_of_nonneg_right (by linarith only [hexp_le]) hsw_nn
        _ = 2 * ((ρJ t / ρJ B) * spectralWeight prob (c n) t) + spectralWeight prob (c n) t := by ring
  have hae_supp_W : ∀ᵐ t ∂(meas.ν.restrict W_op), t ∈ W_op ∧ B - η n ≤ t := by
    have hsub : ∀ᵐ t ∂(meas.ν.restrict W_op), t ∉ (Ici (prob.T_V (c n) - η n))ᶜ :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hν_supp)
    filter_upwards [ae_restrict_mem hW_op_m, hsub] with t ht hBt
    exact ⟨ht, not_not.mp hBt⟩
  have hexp_int_le :
      ∫ t in W_op, |Real.exp (y t) - 1| * spectralWeight prob (c n) t ∂meas.ν ≤
        (2 * Real.pi / xiStar) * η n * (∫ t in W_op, spectralWeight prob (c n) t ∂meas.ν) +
        M_exp * (∫ t in W_op, max (t - B) 0 * spectralWeight prob (c n) t ∂meas.ν) := by
    have h_mono :
        ∫ t in W_op, |Real.exp (y t) - 1| * spectralWeight prob (c n) t ∂meas.ν ≤
          ∫ t in W_op, ((2 * Real.pi / xiStar) * η n * spectralWeight prob (c n) t +
            M_exp * (max (t - B) 0 * spectralWeight prob (c n) t)) ∂meas.ν := by
      refine integral_mono_ae hexp_y_int ((hsw_int.const_mul _).add (hm_int_W.const_mul _)) ?_
      filter_upwards [hae_supp_W] with t ⟨ht, hBt⟩
      have hsw_nn := (spectralWeight_pos hcn_pos hsh12 ht.1).le
      calc |Real.exp (y t) - 1| * spectralWeight prob (c n) t
          ≤ ((2 * Real.pi / xiStar) * η n + M_exp * max (t - B) 0) * spectralWeight prob (c n) t :=
            mul_le_mul_of_nonneg_right (hy_pt_bd t ht hBt) hsw_nn
        _ = _ := by ring
    rw [integral_add (hsw_int.const_mul _) (hm_int_W.const_mul _),
      integral_const_mul, integral_const_mul] at h_mono
    exact h_mono
  have hμ_up : (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal ≤ w₀ + 1 := by
    rw [hν_eq, Real.dist_eq] at hμ_n
    have hμ_sub := (abs_lt.mp hμ_n).2
    have hεm1 : ε_m ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hμ_sub, hεm1]
  have hμ_nn : 0 ≤ (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal :=
    ENNReal.toReal_nonneg
  have hlin_term_lt : (2 * Real.pi / xiStar) * η n *
      (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal < ε / 8 := by
    have h1 : η n * (2 * Real.pi / xiStar) < ε / (8 * (w₀ + 2)) := hlin_n
    have hw2 : 0 < w₀ + 2 := by positivity
    calc (2 * Real.pi / xiStar) * η n *
          (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal
        = (η n * (2 * Real.pi / xiStar)) *
            (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal := by ring
      _ ≤ (η n * (2 * Real.pi / xiStar)) * (w₀ + 1) :=
          mul_le_mul_of_nonneg_left hμ_up (mul_nonneg hη_n.1 (div_nonneg (by positivity) xiStar_pos.le))
      _ < (ε / (8 * (w₀ + 2))) * (w₀ + 1) := mul_lt_mul_of_pos_right h1 (by positivity)
      _ < (ε / (8 * (w₀ + 2))) * (w₀ + 2) := mul_lt_mul_of_pos_left (by linarith) (by positivity)
      _ = ε / 8 := by field_simp [hw2.ne']
  have hexp_term_lt : M_exp * (C_r * η n) < ε / 8 := by
    have hM_mul : M_exp * C_r * η n ≤ C_exp * Real.exp (-(γ - γ') * (c n) ^ ((1 : ℝ) / 3)) := by
      have h_eq : Real.exp (γ' * (c n) ^ ((1 : ℝ) / 3)) * Real.exp (-γ * (c n) ^ ((1 : ℝ) / 3)) =
          Real.exp (-(γ - γ') * (c n) ^ ((1 : ℝ) / 3)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc M_exp * C_r * η n
          ≤ M_exp * C_r * Real.exp (-γ * (c n) ^ ((1 : ℝ) / 3)) :=
            mul_le_mul_of_nonneg_left hη_n.2 (mul_nonneg hM_exp_nn hCr_pos.le)
        _ = ((3 * betaTip / (2 * Real.pi * r)) * (2 * Real.pi / xiStar) * C_r) *
              Real.exp (-(γ - γ') * (c n) ^ ((1 : ℝ) / 3)) := by
            dsimp [M_exp]; rw [← h_eq]; ring
        _ ≤ C_exp * Real.exp (-(γ - γ') * (c n) ^ ((1 : ℝ) / 3)) := by
            gcongr; dsimp [C_exp]; linarith
    have hCexp_pos : 0 < C_exp := by have := betaTip_pos; dsimp [C_exp]; positivity
    have hdec' : C_exp * Real.exp (-(γ - γ') * (c n) ^ ((1 : ℝ) / 3)) < ε / 8 := by
      have h1C : (0 : ℝ) < 1 + C_exp := by linarith only [hCexp_pos]
      calc C_exp * Real.exp (-(γ - γ') * (c n) ^ ((1 : ℝ) / 3))
          < C_exp * (ε / (8 * (1 + C_exp))) := mul_lt_mul_of_pos_left hdec_n hCexp_pos
        _ = (ε / 8) * (C_exp / (1 + C_exp)) := by field_simp [h1C.ne']
        _ < (ε / 8) * 1 := mul_lt_mul_of_pos_left ((div_lt_one h1C).mpr (by linarith only)) (by positivity)
        _ = ε / 8 := by ring
    linarith only [hM_mul, hdec']
  have hexp_int_lt : ∫ t in W_op, |Real.exp (y t) - 1| * spectralWeight prob (c n) t ∂meas.ν < ε / 4 := by
    have hM_le : M_exp * (∫ t in W_op, max (t - B) 0 * spectralWeight prob (c n) t ∂meas.ν) ≤ M_exp * (C_r * η n) :=
      mul_le_mul_of_nonneg_left hm_int_le hM_exp_nn
    rw [hμ_eq_int] at hlin_term_lt
    linarith only [hexp_int_le, hM_le, hlin_term_lt, hexp_term_lt]
  have hdiff_int_le :
      |∫ t in W_op, (ρJ t / ρJ B - 1) * spectralWeight prob (c n) t ∂meas.ν| ≤
        ε_p * (∫ t in W_op, spectralWeight prob (c n) t ∂meas.ν) +
        (ε_p + 1) * (∫ t in W_op, |Real.exp (y t) - 1| * spectralWeight prob (c n) t ∂meas.ν) := by
    have h_ab := norm_integral_le_integral_norm
      (fun t => (ρJ t / ρJ B - 1) * spectralWeight prob (c n) t) (μ := meas.ν.restrict W_op)
    have h_mono :
        ∫ t in W_op, ‖(ρJ t / ρJ B - 1) * spectralWeight prob (c n) t‖ ∂meas.ν ≤
          ∫ t in W_op, (ε_p * spectralWeight prob (c n) t +
            (ε_p + 1) * (|Real.exp (y t) - 1| * spectralWeight prob (c n) t)) ∂meas.ν := by
      have hdiff_int : IntegrableOn (fun t => (ρJ t / ρJ B - 1) * spectralWeight prob (c n) t) W_op meas.ν :=
        (hratio_int.sub hsw_int).congr_fun (fun t _ => by dsimp only [Pi.sub_apply]; ring) hW_op_m
      refine integral_mono_ae hdiff_int.norm
        ((hsw_int.const_mul _).add (hexp_y_int.const_mul _)) ?_
      filter_upwards [ae_restrict_mem hW_op_m] with t ht
      have hsw_nn := (spectralWeight_pos hcn_pos hsh12 ht.1).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsw_nn]
      calc |ρJ t / ρJ B - 1| * spectralWeight prob (c n) t
          ≤ (ε_p * (1 + |Real.exp (y t) - 1|) + |Real.exp (y t) - 1|) *
              spectralWeight prob (c n) t :=
            mul_le_mul_of_nonneg_right (h_diff_split t ht) hsw_nn
        _ = ε_p * spectralWeight prob (c n) t +
              (ε_p + 1) * (|Real.exp (y t) - 1| * spectralWeight prob (c n) t) := by ring
    rw [integral_add (hsw_int.const_mul _) (hexp_y_int.const_mul _),
      integral_const_mul, integral_const_mul] at h_mono
    simpa [Real.norm_eq_abs] using h_ab.trans h_mono
  have hεp_mu_lt : ε_p * (∫ t in W_op, spectralWeight prob (c n) t ∂meas.ν) < ε / 4 := by
    rw [← hμ_eq_int]
    have hw2 : 0 < w₀ + 2 := by positivity
    calc ε_p * (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal
        ≤ (ε / (4 * (w₀ + 2))) * (w₀ + 1) :=
          mul_le_mul (min_le_right _ _) hμ_up hμ_nn (by positivity)
      _ < (ε / (4 * (w₀ + 2))) * (w₀ + 2) := mul_lt_mul_of_pos_left (by linarith only) (by positivity)
      _ = ε / 4 := by field_simp [hw2.ne']
  have hεp1_exp_lt : (ε_p + 1) * (∫ t in W_op, |Real.exp (y t) - 1| * spectralWeight prob (c n) t ∂meas.ν) <
      3 * ε / 8 := by
    have hεp1 : ε_p + 1 ≤ 3 / 2 := by linarith only [min_le_left (1 / 2) (ε / (4 * (w₀ + 2)))]
    have h_int_nn : 0 ≤ ∫ t in W_op, |Real.exp (y t) - 1| * spectralWeight prob (c n) t ∂meas.ν := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_restrict_mem hW_op_m] with t ht
      exact mul_nonneg (abs_nonneg _) (spectralWeight_pos hcn_pos hsh12 ht.1).le
    calc (ε_p + 1) * (∫ t in W_op, |Real.exp (y t) - 1| * spectralWeight prob (c n) t ∂meas.ν)
        ≤ (3 / 2) * (∫ t in W_op, |Real.exp (y t) - 1| * spectralWeight prob (c n) t ∂meas.ν) :=
          mul_le_mul_of_nonneg_right hεp1 h_int_nn
      _ < (3 / 2) * (ε / 4) := by linarith only [hexp_int_lt]
      _ = 3 * ε / 8 := by ring
  have hμ_err : |(spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal - w₀| <
      ε / 4 := by
    rw [hν_eq, Real.dist_eq] at hμ_n
    exact lt_of_lt_of_le hμ_n (min_le_left _ _)
  rw [Real.dist_eq]
  have h_tri : |(meas.ν W_op).toReal / ρJ B - w₀| ≤
      |(meas.ν W_op).toReal / ρJ B -
        (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal| +
      |(spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal - w₀| := by
    calc |(meas.ν W_op).toReal / ρJ B - w₀|
        = |((meas.ν W_op).toReal / ρJ B -
            (spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal) +
          ((spectralMeasure prob (c n) meas.ν (Ioo (airyZero 1 - r) (airyZero 1 + r))).toReal - w₀)| := by
            ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [hsub_int] at h_tri
  change |(meas.ν W_op).toReal / ρJ B - w₀| < ε
  linarith only [h_tri, hdiff_int_le, hεp_mu_lt, hεp1_exp_lt, hμ_err, hε]

/-- **First-cluster total mass for exponentially near-optimal spectra** (`dsl:near-opt-mass`,
`dual_spectrum_limit.tex`, Proposition `E'-M`, and `dsl:D1-exact` + `dsl:d1-asym`):
fix `prob : FixedWeightProblem`, `r ∈ (0, |a₁ - a₂|)`, `γ > 2π r / (3 β)`, `c_n → ∞`, and `η_n`
with `0 ≤ η_n ≤ exp(-γ c_n^{1/3})`. Then for any sequence of crossing measures `ν_n` supported on
`[T_V(c_n) - η_n, ∞)`, the raw first-cluster mass
`D₁(r; ν_n) := ν_n({t | |u_{c_n}(t) - a₁| < r})` satisfies:
1. `D₁(r; ν_n) / (2π V(c_n/12, T_V(c_n)) J_{c_n}(T_V(c_n))) → Ai'(a₁)^{-2}` (`dsl:D1-exact`);
2. `D₁(r; ν_n)` obeys the explicit `dsl:d1-asym` asymptotic with `b_n = T_V(c_n) - T_*(c_n) = O(1)`. -/
theorem one_level_near_opt_mass (prob : FixedWeightProblem) {r γ : ℝ}
    (hr_pos : 0 < r) (hr_sep : r < |airyZero 1 - airyZero 2|)
    (hγ : 2 * Real.pi * r / (3 * betaTip) < γ)
    {c η : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hη_bd : ∀ᶠ n in atTop, 0 ≤ η n ∧ η n ≤ Real.exp (-γ * (c n) ^ ((1 : ℝ) / 3)))
    (ν_seq : ℕ → Measure ℝ)
    (hν : ∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
      ν_seq n = meas.ν ∧ meas.ν (Ici (prob.T_V (c n) - η n))ᶜ = 0) :
    Tendsto (fun n => (ν_seq n {t : ℝ | |uAiry (c n) t - airyZero 1| < r}).toReal /
        (2 * Real.pi * prob.cardyV (c n / 12) (prob.T_V (c n)) *
          jAiry (c n) (prob.T_V (c n))))
      atTop (𝓝 (airyNodeWeight 0)) ∧
    (let amp : ℝ := 2 * Real.sqrt xiStar * (2 * xiStar) ^ (prob.w - 1) *
      prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) / (Real.sqrt 3 * betaTip)
    Tendsto (fun n => (ν_seq n {t : ℝ | |uAiry (c n) t - airyZero 1| < r}).toReal /
        (amp * airyNodeWeight 0 * (c n) ^ (-(1 / 6 : ℝ)) *
          Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n +
            (2 * Real.pi * |airyZero 1| / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
            (Real.pi / xiStar) * (prob.T_V (c n) - TStar (c n)))))
      atTop (𝓝 1)) := by
  have hD1_exact := one_level_d1_exact prob hr_pos hr_sep hγ hc hη_bd ν_seq hν
  refine ⟨hD1_exact, ?_⟩
  -- Part 2 (`dsl:d1-asym` for `D₁(r; ν_n)`) from `hD1_exact` and `cardyV_mul_jAiry_asymp`!
  intro amp
  have hB_tend := uAiry_T_V_tendsto prob hc
  have hcardy := cardyV_mul_jAiry_asymp prob hc hB_tend
  have h_b_eq : ∀ n, prob.T_V (c n) - xiBar * c n + cStar * airyZero 1 * (c n) ^ ((1 : ℝ) / 3) =
      prob.T_V (c n) - TStar (c n) := fun n => by
    have ha1_neg : airyZero 1 < 0 := airyZero_neg 1
    have hA : Aopt = -cStar * airyZero 1 := by
      unfold Aopt; rw [abs_of_neg ha1_neg]; ring
    unfold TStar; rw [hA]; ring
  have h_pow_eq : -(2 * Real.pi * airyZero 1 / (3 * betaTip)) =
      2 * Real.pi * |airyZero 1| / (3 * betaTip) := by
    have ha1_neg : airyZero 1 < 0 := airyZero_neg 1
    rw [abs_of_neg ha1_neg]; ring
  have hcardy' : Tendsto (fun n => (2 * Real.pi * prob.cardyV (c n / 12) (prob.T_V (c n)) *
        jAiry (c n) (prob.T_V (c n))) /
      (amp * (c n) ^ (-(1 / 6 : ℝ)) *
        Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n +
          (2 * Real.pi * |airyZero 1| / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
          (Real.pi / xiStar) * (prob.T_V (c n) - TStar (c n))))) atTop (𝓝 1) := by
    refine hcardy.congr' (Eventually.of_forall fun n => ?_)
    dsimp only
    rw [h_b_eq n, sub_eq_add_neg _ ((2 * Real.pi * airyZero 1 / (3 * betaTip)) * _),
      neg_mul_eq_neg_mul, h_pow_eq]
  have hw₀_ne : airyNodeWeight 0 ≠ 0 := (airyNodeWeight_pos 0).ne'
  have halg : ∀ D' ρ' a' w' c' : ℝ, ρ' ≠ 0 → w' ≠ 0 →
      (D' / ρ') * (ρ' / (a' * c')) / w' = D' / (a' * w' * c') := fun D' ρ' a' w' c' hρ hw => by
    field_simp [hρ, hw]
  have hprod : Tendsto (fun n => ((ν_seq n {t : ℝ | |uAiry (c n) t - airyZero 1| < r}).toReal /
        (2 * Real.pi * prob.cardyV (c n / 12) (prob.T_V (c n)) *
          jAiry (c n) (prob.T_V (c n)))) *
      ((2 * Real.pi * prob.cardyV (c n / 12) (prob.T_V (c n)) *
          jAiry (c n) (prob.T_V (c n))) /
        (amp * ((c n) ^ (-(1 / 6 : ℝ)) *
          Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n +
            (2 * Real.pi * |airyZero 1| / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
            (Real.pi / xiStar) * (prob.T_V (c n) - TStar (c n)))))) / airyNodeWeight 0)
      atTop (𝓝 ((airyNodeWeight 0 * 1) / airyNodeWeight 0)) :=
    (hD1_exact.mul (hcardy'.congr' (Eventually.of_forall fun _ => by ring))).div_const (airyNodeWeight 0)
  rw [mul_one, div_self hw₀_ne] at hprod
  refine hprod.congr' ?_
  filter_upwards [hc.eventually_gt_atTop 0, hc.eventually_ge_atTop (12 * prob.totalShift),
    eventually_pos_of_uAiry_tendsto hc hB_tend] with n hcn hsh hBn
  have hsh12 : prob.totalShift ≤ c n / 12 := by linarith
  have hρ_ne : (2 * Real.pi * prob.cardyV (c n / 12) (prob.T_V (c n)) *
      jAiry (c n) (prob.T_V (c n))) ≠ 0 := by
    have := prob.cardyV_pos hsh12 hBn
    have := jAiry_pos hcn hBn
    positivity
  rw [halg _ _ amp (airyNodeWeight 0) _ hρ_ne hw₀_ne]
  ring

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.one_level_near_opt_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.one_level_near_opt_mass

end FixedWeight

end ModularBootstrap

end FormalResearch

