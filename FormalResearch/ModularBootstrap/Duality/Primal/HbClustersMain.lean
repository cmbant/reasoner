module

public import FormalResearch.ModularBootstrap.Duality.Primal.HbClusters

/-!
# Main `dsl:hb-clusters` theorems (`Theorem E'-HB`, parts (a) and (b))

Builds on `Duality/Primal/HbClusters.lean` to establish:
* `hb_clusters` (`dsl:hb-clusters` (a)): canonical measure-independent cluster points `tStar k n`,
  simple/double multiplicities at every weak extremal, convergence `uAiry (c n) (tStar k n) → z k`,
  uniform normalised weight convergence to `ω k`, and the uniform `dsl:hb-raw` asymptotic;
* `hb_clusters_prescribed_raw` (`dsl:hb-clusters` (a), near-optimal prescribed sites): the `dsl:hb-raw`
  asymptotic at `s i n` for near-optimal crossing measure sequences;
* `hb_clusters_inactive` (`dsl:hb-clusters` (b)): inactivity of additional compact sets `E_n` whose
  Airy images stay in a compact subset of `{u > H.tm : (normProfile H.G u).re > 0}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.ConcreteBootstrap
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Bessel
  FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ArgPrinciple

/-! ### 1. Canonical primal setup and unique real-zero construction -/

private instance (H : HermiteBiehlerData) : Finite (HbNodes H) :=
  Finite.of_injective (fun i : HbNodes H => (⟨i.1, i.2.1⟩ : H.S))
    (fun _ _ h => Subtype.ext (Subtype.mk.inj h))

lemma hb_canonical_primal (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n) :
    ∃ (gs0 : ℕ → ℝ → ℝ) (ν0 : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, IsWeakExtremal prob (c n) (hbPrescribedSet s n)
        (constrainedThreshold prob (c n) (hbPrescribedSet s n)) (gs0 n) ∧
        (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs0 n t = 0}.Finite) ∧
        ∀ m : AdmissibleCrossingMeasure prob (c n / 12),
          m.ν (hbPrescribedSet s n ∪
            Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 →
            (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ m.ν Zᶜ = 0) ∧
            0 < m.ν {constrainedThreshold prob (c n) (hbPrescribedSet s n)} ∧
            ∀ᵐ t ∂m.ν, t ∈ hbPrescribedSet s n ∪
              Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)) ∧ gs0 n t = 0) ∧
      (∀ᶠ n in atTop, ∃ meas0 : AdmissibleCrossingMeasure prob (c n / 12),
        ν0 n = meas0.ν ∧
        meas0.ν (hbPrescribedSet s n ∪
          Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0) := by
  classical
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let F : ℕ → Set ℝ := hbPrescribedSet s
  obtain ⟨c_str, hc_str⟩ := fixedChargeStrip_of_large prob
  have hF_Ioi := hbPrescribedSet_subset_Ioi hs_pos
  have hex : ∀ᶠ n in atTop, ∃ gs : ℝ → ℝ, ∃ meas0 : AdmissibleCrossingMeasure prob (c n / 12),
      IsWeakExtremal prob (c n) (F n) (B n) gs ∧
      (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs t = 0}.Finite) ∧
      meas0.ν (F n ∪ Ici (B n))ᶜ = 0 ∧
      ∀ m : AdmissibleCrossingMeasure prob (c n / 12),
        m.ν (F n ∪ Ici (B n))ᶜ = 0 →
          (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ m.ν Zᶜ = 0) ∧
          0 < m.ν {B n} ∧ ∀ᵐ t ∂m.ν, t ∈ F n ∪ Ici (B n) ∧ gs t = 0 := by
    filter_upwards [hc.eventually_ge_atTop c_str, hF_Ioi] with n h1 hFn
    have hS := hc_str h1
    obtain ⟨⟨hTV, -, -⟩, gs, ⟨htc, hM, hvac, hnn, hfin, _, _⟩, h_ae, hmeas, -⟩ :=
      theorem_primal hS (isCompact_hbPrescribedSet s n) hFn
    obtain ⟨-, meas0, hν0⟩ :=
      (theorem_E_b_compact prob hS.hc_pos hS.hc (isCompact_hbPrescribedSet s n) hFn hTV).2.1.1
    refine ⟨gs, meas0, ⟨htc, hM, hvac, hnn⟩, hfin, hν0, fun m hm => ?_⟩
    obtain ⟨hZ, hBpos⟩ := hmeas m hm
    exact ⟨hZ, hBpos, h_ae m hm⟩
  let P := fun n (gs : ℝ → ℝ) (meas0 : AdmissibleCrossingMeasure prob (c n / 12)) =>
    IsWeakExtremal prob (c n) (F n) (B n) gs ∧
    (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs t = 0}.Finite) ∧
    meas0.ν (F n ∪ Ici (B n))ᶜ = 0 ∧
    ∀ m : AdmissibleCrossingMeasure prob (c n / 12),
      m.ν (F n ∪ Ici (B n))ᶜ = 0 →
        (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ m.ν Zᶜ = 0) ∧
        0 < m.ν {B n} ∧ ∀ᵐ t ∂m.ν, t ∈ F n ∪ Ici (B n) ∧ gs t = 0
  let gs0 : ℕ → ℝ → ℝ := fun n =>
    if h : ∃ gs meas0, P n gs meas0 then h.choose else fun _ => 0
  let ν0 : ℕ → Measure ℝ := fun n =>
    if h : ∃ gs meas0, P n gs meas0 then h.choose_spec.choose.ν else 0
  refine ⟨gs0, ν0, ?_, ?_⟩
  · filter_upwards [hex] with n hn
    dsimp [gs0]; split_ifs with h
    · exact ⟨h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2.1,
        h.choose_spec.choose_spec.2.2.2⟩
    · exact absurd hn h
  · filter_upwards [hex] with n hn
    dsimp [ν0]; split_ifs with h
    · exact ⟨h.choose_spec.choose, rfl, h.choose_spec.choose_spec.2.2.1⟩
    · exact absurd hn h

lemma zero_in_disc_for_canonical (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    (CD : HbClusterData H) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    (hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 H.tm))
    (hvag : ∀ (ν_seq : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧
        meas.ν (hbPrescribedSet s n ∪
          Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0) →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo CD.a CD.b →
        Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k))))
    {gs0 : ℕ → ℝ → ℝ} {ν0 : ℕ → Measure ℝ}
    (hgs0 : ∀ᶠ n in atTop, IsWeakExtremal prob (c n) (hbPrescribedSet s n)
      (constrainedThreshold prob (c n) (hbPrescribedSet s n)) (gs0 n) ∧
      (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs0 n t = 0}.Finite) ∧
      ∀ m : AdmissibleCrossingMeasure prob (c n / 12),
        m.ν (hbPrescribedSet s n ∪
          Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 →
          (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ m.ν Zᶜ = 0) ∧
          0 < m.ν {constrainedThreshold prob (c n) (hbPrescribedSet s n)} ∧
          ∀ᵐ t ∂m.ν, t ∈ hbPrescribedSet s n ∪
            Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)) ∧ gs0 n t = 0)
    (hν0 : ∀ᶠ n in atTop, ∃ meas0 : AdmissibleCrossingMeasure prob (c n / 12),
      ν0 n = meas0.ν ∧
      meas0.ν (hbPrescribedSet s n ∪
        Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0)
    {r₀ r : ℝ} (hr0_pos : 0 < r₀)
    (hr0_win : ∀ k : Fin CD.K, CD.a < CD.z k - 2 * r₀ ∧ CD.z k + 2 * r₀ < CD.b)
    (hr0_sep : ∀ j k : Fin CD.K, j ≠ k → 4 * r₀ ≤ |CD.z j - CD.z k|)
    (hr0_tm : ∀ k : Fin CD.K, CD.z k ≠ H.tm → 2 * r₀ ≤ |CD.z k - H.tm|)
    (hr_pos : 0 < r) (hr_le : r ≤ r₀) :
    ∀ᶠ n in atTop, ∀ k : Fin CD.K, ∃! u : ℝ,
      u ∈ ball (CD.z k) r ∧
      psiTilde prob (c n) (gs0 n) (u : ℂ) = 0 ∧
      gs0 n (virasoroDeltaChart (c n) u) = 0 ∧
      0 < virasoroDeltaChart (c n) u ∧
      chartUT (c n) (virasoroDeltaChart (c n) u) = u ∧
      (CD.z k = H.tm → virasoroDeltaChart (c n) u =
        constrainedThreshold prob (c n) (hbPrescribedSet s n)) ∧
      (∀ hmem : CD.z k ∈ H.S ∧ CD.z k ≠ H.tm,
        virasoroDeltaChart (c n) u = s ⟨CD.z k, hmem⟩ n) ∧
      analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u : ℂ) =
        if CD.z k ∈ H.S then 1 else 2 := by
  classical
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let F : ℕ → Set ℝ := hbPrescribedSet s
  have hgs0_we : ∀ᶠ n in atTop, IsWeakExtremal prob (c n) (F n) (B n) (gs0 n) :=
    hgs0.mono fun _ h => h.1
  have hr_win : ∀ k : Fin CD.K, CD.a < CD.z k - 2 * r ∧ CD.z k + 2 * r < CD.b := fun k =>
    ⟨by linarith [(hr0_win k).1], by linarith [(hr0_win k).2]⟩
  have hr_sep : ∀ j k : Fin CD.K, j ≠ k → 4 * r ≤ |CD.z j - CD.z k| := fun j k hjk =>
    by linarith [hr0_sep j k hjk]
  have hr_tm : ∀ k : Fin CD.K, CD.z k ≠ H.tm → 2 * r ≤ |CD.z k - H.tm| := fun k hk =>
    by linarith [hr0_tm k hk]
  have hHur := hurwitz_window_isolation prob H CD hc hs_pos hs_tend hB_tend hgs0_we hr_pos hr_win hr_sep
  have hB_pos := eventually_pos_of_uAiry_tendsto hc hB_tend
  have hB_chart := chartUT_tendsto_of_uAiry hc hB_pos hB_tend
  have hs_chart : ∀ i : HbNodes H, Tendsto (fun n => chartUT (c n) (s i n)) atTop (𝓝 i.1) :=
    fun i => chartUT_tendsto_of_uAiry hc (hs_pos i) (hs_tend i)
  let M_ab : ℝ := max |CD.a| |CD.b| + 2 * r + 2
  obtain ⟨C_ut, c_ut, _, hc_ut1, hC_ut⟩ := chartUT_sub_uAiry_err (show 0 ≤ M_ab by positivity)
  have hCerr : ∀ᶠ n in atTop, C_ut * (c n) ^ (-(2 / 3 : ℝ)) < r / 4 := by
    have h0 : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_ut
    exact h0.eventually (gt_mem_nhds (by positivity))
  -- Bumps at each node `k` on `(CD.z k - r/2, CD.z k + r/2)`.
  choose bump hbump_cont hbump_cs _ hbump_one hbump_zero hbump_tsupp using
    fun k : Fin CD.K => exists_bump_near (x₀ := CD.z k) (r := r / 2) (by positivity)
  have hbump_pos : ∀ᶠ n in atTop, ∀ k : Fin CD.K,
      0 < ∫ u, bump k u ∂(spectralMeasure prob (c n) (ν0 n)) := by
    rw [eventually_all]
    intro k
    have htsub : tsupport (bump k) ⊆ Ioo CD.a CD.b := fun u hu => by
      have h1 := hbump_tsupp k hu
      exact ⟨by linarith [h1.1, (hr_win k).1], by linarith [h1.2, (hr_win k).2]⟩
    have hlim := hvag ν0 hν0 (bump k) (hbump_cont k) (hbump_cs k) htsub
    have hsum : (∑ j : Fin CD.K, CD.ω j * bump k (CD.z j)) = CD.ω k := by
      rw [Finset.sum_eq_single k]
      · rw [hbump_one k (CD.z k) ⟨by linarith, by linarith⟩, mul_one]
      · intro j _ hjk
        have hj_out : CD.z j ∉ Ioo (CD.z k - r / 2) (CD.z k + r / 2) := fun hmem => by
          have hsep := hr_sep j k hjk
          have hlt : |CD.z j - CD.z k| < r / 2 := abs_lt.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
          linarith
        rw [hbump_zero k (CD.z j) hj_out, mul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hsum] at hlim
    exact hlim.eventually (lt_mem_nhds (CD.hω_pos k))
  have hs_close : ∀ᶠ n in atTop, ∀ i : HbNodes H,
      0 < s i n ∧ |chartUT (c n) (s i n) - i.1| < r / 4 ∧ |uAiry (c n) (s i n) - i.1| < r / 4 := by
    rw [eventually_all]
    intro i
    filter_upwards [hs_pos i, (hs_chart i).eventually (Metric.ball_mem_nhds i.1 (show 0 < r / 4 by positivity)),
      (hs_tend i).eventually (Metric.ball_mem_nhds i.1 (show 0 < r / 4 by positivity))] with n h1 h2 h3
    exact ⟨h1, by simpa [Real.dist_eq] using h2, by simpa [Real.dist_eq] using h3⟩
  have hB_close : ∀ᶠ n in atTop,
      |chartUT (c n) (B n) - H.tm| < r / 4 ∧ |uAiry (c n) (B n) - H.tm| < r / 4 := by
    filter_upwards [hB_chart.eventually (Metric.ball_mem_nhds H.tm (show 0 < r / 4 by positivity)),
      hB_tend.eventually (Metric.ball_mem_nhds H.tm (show 0 < r / 4 by positivity))] with n h1 h2
    exact ⟨by simpa [Real.dist_eq] using h1, by simpa [Real.dist_eq] using h2⟩
  let M_win : ℝ := max |CD.a| |CD.b| + 2 * r₀ + 2
  obtain ⟨C_ut2, c_ut2, _, hc_ut2, hC_ut2⟩ := chartUT_sub_uAiry_err (show 0 ≤ M_win by positivity)
  obtain ⟨C_va, c_va, _, hc_va, hC_va⟩ := uAiry_virasoroDeltaChart_err (show 0 ≤ |CD.a| + 2 by positivity)
  have hCerr2 : ∀ᶠ n in atTop, C_ut2 * (c n) ^ (-(2 / 3 : ℝ)) < r / 4 := by
    have h0 : Tendsto (fun n => C_ut2 * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_ut2
    exact h0.eventually (gt_mem_nhds (by positivity))
  have hCva_err : ∀ᶠ n in atTop, C_va * (c n) ^ (-(2 / 3 : ℝ)) < 1 / 4 := by
    have h0 : Tendsto (fun n => C_va * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_va
    exact h0.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hgs0, hν0, hHur, hB_pos, hB_close, hs_close,
    hc.eventually_ge_atTop (max (max c_ut c_ut2) (max c_va (max 1 (12 * prob.totalShift)))),
    virasoroAC_sq_eventually_ge hc (max M_ab (|CD.a| + 2)),
    hCerr, hCerr2, hCva_err, hbump_pos]
    with n ⟨hwe, hgs_fin, hall_meas⟩ ⟨meas0, hν0_eq, hν0_supp⟩ ⟨hDiff, _, hDisc⟩
      hBn_pos ⟨hBc_cl, hBu_cl⟩ hs_cl hc_ge hVac hCerr_n hCerr2_n hCva_n hbp_n
  have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one
    ((le_max_left 1 _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge)))
  have hsh12 : prob.totalShift ≤ c n / 12 := by
    have := (le_max_right 1 _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))
    linarith
  have hcut : c_ut ≤ c n := (le_max_left _ _).trans ((le_max_left _ _).trans hc_ge)
  have hcut2 : c_ut2 ≤ c n := (le_max_right _ _).trans ((le_max_left _ _).trans hc_ge)
  have hcva : c_va ≤ c n := (le_max_left _ _).trans ((le_max_right _ _).trans hc_ge)
  have hVac1 : M_ab ≤ virasoroAC (c n) ^ 2 := (le_max_left _ _).trans hVac
  have hVac2 : |CD.a| + 2 ≤ virasoroAC (c n) ^ 2 := (le_max_right _ _).trans hVac
  obtain ⟨Z0, hZ0_fin, hZ0_null⟩ := (hall_meas meas0 hν0_supp).1
  have hB_atom := (hall_meas meas0 hν0_supp).2.1
  have h_ae0 := (hall_meas meas0 hν0_supp).2.2
  have h_in_vac : ∀ k : Fin CD.K, ∀ u : ℝ, u ∈ ball (CD.z k) r → |u| ≤ virasoroAC (c n) ^ 2 := by
    intro k u hu
    rw [Metric.mem_ball, Real.dist_eq] at hu
    have hzk_in : CD.z k ∈ Icc CD.a CD.b := ⟨by linarith [(hr_win k).1], by linarith [(hr_win k).2]⟩
    have hzk_abs : |CD.z k| ≤ max |CD.a| |CD.b| :=
      abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hzk_in.1],
        by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hzk_in.2]⟩
    have h1 : |u| ≤ M_ab := by
      calc |u| = |(u - CD.z k) + CD.z k| := by ring_nf
        _ ≤ |u - CD.z k| + |CD.z k| := abs_add_le _ _
        _ ≤ r + max |CD.a| |CD.b| := by linarith [abs_lt.mp hu]
        _ ≤ M_ab := by dsimp [M_ab]; linarith
    exact h1.trans hVac1
  let R_m : ℝ := ↑(Nat.ceil (max |CD.a| |CD.b| + 2 * r + 2)) + 1
  let R' : ℝ := r + r / 2
  have hrR' : r < R' := by dsimp [R']; linarith
  have hball_sub : ∀ k : Fin CD.K, ball (CD.z k : ℂ) R' ⊆ ball (0 : ℂ) R_m := fun k w hw => by
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball_zero_iff]
    have hzk_in : CD.z k ∈ Icc CD.a CD.b := ⟨by linarith [(hr_win k).1], by linarith [(hr_win k).2]⟩
    have hzk_abs : ‖(CD.z k : ℂ)‖ ≤ max |CD.a| |CD.b| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hzk_in.1],
        by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hzk_in.2]⟩
    have := Nat.le_ceil (max |CD.a| |CD.b| + 2 * r + 2)
    calc ‖w‖ ≤ ‖w - (CD.z k : ℂ)‖ + ‖(CD.z k : ℂ)‖ := norm_le_norm_sub_add w (CD.z k : ℂ)
      _ < R' + max |CD.a| |CD.b| := by linarith
      _ ≤ R_m := by dsimp [R', R_m]; linarith
  have hM_we : 0 < prob.cardyNorm (c n / 12) (gs0 n) := by rw [hwe.2.1]; exact zero_lt_one
  intro k
  obtain ⟨hsph_k, hzc_k⟩ := hDisc k
  have hDiff_k : DifferentiableOn ℂ (psiTilde prob (c n) (gs0 n)) (ball (CD.z k : ℂ) R') :=
    hDiff.mono (hball_sub k)
  -- Construct `u0 ∈ ball (CD.z k) r` with all properties, and check uniqueness.
  have hex_u0 : ∃ u0 : ℝ, u0 ∈ ball (CD.z k) r ∧
      psiTilde prob (c n) (gs0 n) (u0 : ℂ) = 0 ∧
      gs0 n (virasoroDeltaChart (c n) u0) = 0 ∧
      0 < virasoroDeltaChart (c n) u0 ∧
      chartUT (c n) (virasoroDeltaChart (c n) u0) = u0 ∧
      (CD.z k = H.tm → virasoroDeltaChart (c n) u0 = B n) ∧
      (∀ hmem : CD.z k ∈ H.S ∧ CD.z k ≠ H.tm, virasoroDeltaChart (c n) u0 = s ⟨CD.z k, hmem⟩ n) ∧
      analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) =
        if CD.z k ∈ H.S then 1 else 2 := by
    by_cases hkS : CD.z k ∈ H.S
    · have hzc1 : zeroCount (psiTilde prob (c n) (gs0 n)) (CD.z k : ℂ) r = 1 := by
        simpa [hkS] using hzc_k
      by_cases htm : CD.z k = H.tm
      · let u0 := chartUT (c n) (B n)
        have hu0_ball : u0 ∈ ball (CD.z k) r := by
          rw [Metric.mem_ball, Real.dist_eq, htm]; exact hBc_cl.trans (by linarith)
        have hu0_vac := h_in_vac k u0 hu0_ball
        have hBu_win : |uAiry (c n) (B n)| ≤ M_win := by
          have := abs_lt.mp hBu_cl
          have h1 : CD.z k ∈ Icc CD.a CD.b := ⟨by linarith [(hr_win k).1], by linarith [(hr_win k).2]⟩
          rw [htm] at h1
          have htm_abs : |H.tm| ≤ max |CD.a| |CD.b| :=
            abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, h1.1],
              by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, h1.2]⟩
          rw [abs_le]; dsimp [M_win]; constructor <;> linarith [neg_abs_le H.tm, le_abs_self H.tm]
        have hΔu0 : virasoroDeltaChart (c n) u0 = B n := (hC_ut2 hcut2 hBn_pos hBu_win).2.1
        have hgs0_B : gs0 n (B n) = 0 := by
          have := h_ae0
          by_contra hne
          exact hB_atom.ne' (le_antisymm (le_of_eq (measure_mono_null (fun t ht => by
            rw [mem_singleton_iff.mp ht]; rintro ⟨_, h0⟩; exact hne h0) (ae_iff.1 h_ae0))) (zero_le))
        have hpsi0 : psiTilde prob (c n) (gs0 n) (u0 : ℂ) = 0 :=
          (psiTilde_eq_zero_iff prob hcpos hsh12 hwe.1 hM_we hu0_vac).2 (by rw [hΔu0, hgs0_B])
        have hord1 : analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) = 1 := by
          obtain ⟨hw, hfw⟩ := exists_nonzero_of_sphere hr_pos hrR' hsph_k
          have hfin := support_orderNat_finite hDiff_k hw hfw hrR'
          have hsum : zeroCount (psiTilde prob (c n) (gs0 n)) (CD.z k : ℂ) r =
              ∑ z ∈ hfin.toFinset, analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) z := by
            unfold zeroCount
            rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
          have hu_c : (u0 : ℂ) ∈ ball (CD.z k : ℂ) r := by
            rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
            simpa [Metric.mem_ball, Real.dist_eq] using hu0_ball
          have hnz : 0 < analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) :=
            Nat.pos_of_ne_zero ((orderNat_ne_zero_iff hDiff_k hw hfw (ball_subset_ball hrR'.le hu_c)).mpr hpsi0)
          have hle1 : analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) ≤ 1 := by
            rw [← hzc1, hsum]
            exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr ⟨hu_c, hnz.ne'⟩)
          omega
        refine ⟨u0, hu0_ball, hpsi0, by rw [hΔu0, hgs0_B], by rw [hΔu0]; exact hBn_pos,
          by rw [hΔu0], fun _ => hΔu0, fun hmem => absurd htm hmem.2, ?_⟩
        simpa [hkS] using hord1
      · -- Case `z k ∈ H.S \ {H.tm}`: prescribed site `s ⟨z k, hkS, htm⟩ n`.
        let i : HbNodes H := ⟨CD.z k, hkS, htm⟩
        obtain ⟨hsn_pos, hsc_cl, hsu_cl⟩ := hs_cl i
        let u0 := chartUT (c n) (s i n)
        have hu0_ball : u0 ∈ ball (CD.z k) r := by
          rw [Metric.mem_ball, Real.dist_eq]; exact hsc_cl.trans (by linarith)
        have hu0_vac := h_in_vac k u0 hu0_ball
        have hsu_win : |uAiry (c n) (s i n)| ≤ M_win := by
          have := abs_lt.mp hsu_cl
          have h1 : CD.z k ∈ Icc CD.a CD.b := ⟨by linarith [(hr_win k).1], by linarith [(hr_win k).2]⟩
          have hzk_abs : |CD.z k| ≤ max |CD.a| |CD.b| :=
            abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, h1.1],
              by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, h1.2]⟩
          rw [abs_le]; dsimp [M_win]; constructor <;> linarith [neg_abs_le CD.a, le_abs_self CD.b, neg_abs_le (CD.z k), le_abs_self (CD.z k)]
        have hΔu0 : virasoroDeltaChart (c n) u0 = s i n := (hC_ut2 hcut2 hsn_pos hsu_win).2.1
        -- Positivity of `meas0.ν {s i n}` from `hbp_n k`.
        have hν_win : 0 < meas0.ν (Ioi (0 : ℝ) ∩ uAiry (c n) ⁻¹' Ioo (CD.z k - r / 2) (CD.z k + r / 2)) :=
          spectralMeasure_bump_pos prob hcpos hsh12 meas0.ν (hbump_cont k)
            (fun u hu => hbump_zero k u hu) (hν0_eq ▸ hbp_n k)
        -- Any `t ∈ F n ∪ Ici (B n)` with `uAiry (c n) t ∈ Ioo (z k - r/2) (z k + r/2)` equals `s i n`.
        have h_only_s : ∀ t : ℝ, t ∈ F n ∪ Ici (B n) →
            uAiry (c n) t ∈ Ioo (CD.z k - r / 2) (CD.z k + r / 2) → t = s i n := by
          intro t ht hu
          rcases ht with ⟨j, rfl⟩ | htB
          · by_cases hji : j = i
            · rw [hji]
            · exfalso
              obtain ⟨k_j, hkj⟩ := CD.hS_sub j.1 j.2.1
              have hkj_ne : k_j ≠ k := fun h => hji (Subtype.ext (by rw [hkj, h]))
              have hsep := hr_sep k_j k hkj_ne
              have h4 := abs_lt.mp (hs_cl j).2.2
              have h2 : |uAiry (c n) (s j n) - CD.z k| < r / 2 :=
                abs_lt.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
              have htri : |j.1 - CD.z k| ≤ |j.1 - uAiry (c n) (s j n)| + |uAiry (c n) (s j n) - CD.z k| := by
                have e : j.1 - CD.z k = (j.1 - uAiry (c n) (s j n)) + (uAiry (c n) (s j n) - CD.z k) := by ring
                rw [e]; exact abs_add_le _ _
              have h4' : |j.1 - uAiry (c n) (s j n)| < r / 4 := by
                rw [abs_sub_comm]; exact (hs_cl j).2.2
              rw [← hkj] at hsep
              linarith
          · exfalso
            have hle_u : uAiry (c n) t ≤ uAiry (c n) (B n) := uAiry_antitone hcpos htB
            have htm_le : H.tm < CD.z k :=
              lt_of_le_of_ne ((CD.hS_top k).mp hkS) (Ne.symm htm)
            have h2r : 2 * r ≤ CD.z k - H.tm := by
              have := hr_tm k htm
              rw [abs_of_pos (sub_pos.mpr htm_le)] at this; exact this
            linarith [hu.1, (abs_lt.mp hBu_cl).2]
        have hs_atom : 0 < meas0.ν {s i n} := by
          have hsub_s : Ioi (0 : ℝ) ∩ uAiry (c n) ⁻¹' Ioo (CD.z k - r / 2) (CD.z k + r / 2) ⊆
              (F n ∪ Ici (B n))ᶜ ∪ {s i n} := fun t ht => by
            by_cases hm : t ∈ F n ∪ Ici (B n)
            · exact Or.inr (h_only_s t hm ht.2)
            · exact Or.inl hm
          have hle := (measure_mono hsub_s (μ := meas0.ν)).trans (measure_union_le _ _)
          rw [hν0_supp, zero_add] at hle
          exact lt_of_lt_of_le hν_win hle
        have hgs0_s : gs0 n (s i n) = 0 := by
          by_contra hne
          exact hs_atom.ne' (le_antisymm (le_of_eq (measure_mono_null (fun t ht => by
            rw [mem_singleton_iff.mp ht]; rintro ⟨_, h0⟩; exact hne h0) (ae_iff.1 h_ae0))) (zero_le))
        have hpsi0 : psiTilde prob (c n) (gs0 n) (u0 : ℂ) = 0 :=
          (psiTilde_eq_zero_iff prob hcpos hsh12 hwe.1 hM_we hu0_vac).2 (by rw [hΔu0, hgs0_s])
        have hord1 : analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) = 1 := by
          obtain ⟨hw, hfw⟩ := exists_nonzero_of_sphere hr_pos hrR' hsph_k
          have hfin := support_orderNat_finite hDiff_k hw hfw hrR'
          have hsum : zeroCount (psiTilde prob (c n) (gs0 n)) (CD.z k : ℂ) r =
              ∑ z ∈ hfin.toFinset, analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) z := by
            unfold zeroCount
            rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
          have hu_c : (u0 : ℂ) ∈ ball (CD.z k : ℂ) r := by
            rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
            simpa [Metric.mem_ball, Real.dist_eq] using hu0_ball
          have hnz : 0 < analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) :=
            Nat.pos_of_ne_zero ((orderNat_ne_zero_iff hDiff_k hw hfw (ball_subset_ball hrR'.le hu_c)).mpr hpsi0)
          have hle1 : analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) ≤ 1 := by
            rw [← hzc1, hsum]
            exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr ⟨hu_c, hnz.ne'⟩)
          omega
        refine ⟨u0, hu0_ball, hpsi0, by rw [hΔu0, hgs0_s], by rw [hΔu0]; exact hsn_pos,
          by rw [hΔu0], fun htm' => absurd htm' htm, fun _ => hΔu0, ?_⟩
        simpa [hkS] using hord1
    · -- Case `CD.z k ∉ H.S`: `CD.z k < H.tm`, find atom `t0 > B n` of `meas0` in `uAiry` window,
      -- then `even_analyticOrderNatAt_of_nonneg` + `zeroCount = 2`!
      have hzc2 : zeroCount (psiTilde prob (c n) (gs0 n)) (CD.z k : ℂ) r = 2 := by
        simpa [hkS] using hzc_k
      have hzk_lt_tm : CD.z k < H.tm := by
        by_contra hle; push Not at hle; exact hkS ((CD.hS_top k).mpr hle)
      have hν_win : 0 < meas0.ν (Ioi (0 : ℝ) ∩ uAiry (c n) ⁻¹' Ioo (CD.z k - r / 2) (CD.z k + r / 2)) :=
        spectralMeasure_bump_pos prob hcpos hsh12 meas0.ν (hbump_cont k)
          (fun u hu => hbump_zero k u hu) (hν0_eq ▸ hbp_n k)
      let S_w : Set ℝ := Ioi (0 : ℝ) ∩ uAiry (c n) ⁻¹' Ioo (CD.z k - r / 2) (CD.z k + r / 2)
      let R_bd : ℝ := (c n) * (xiStar + (|CD.a| + 1) / betaTip + 1) ^ 2
      have hSw_sub_bd : S_w ⊆ Icc (0 : ℝ) R_bd := fun t ⟨ht0, hu⟩ => by
        refine ⟨ht0.le, ?_⟩
        have ha_lt : CD.a - 1 < uAiry (c n) t := by linarith [(hr_win k).1, hu.1]
        have hsqrt_lt : Real.sqrt (3 * t / c n) < xiStar + (|CD.a| + 1) / betaTip + 1 := by
          have hc23 : 1 ≤ (c n) ^ ((2 : ℝ) / 3) := by
            have h1c : 1 ≤ c n := (le_max_left 1 _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))
            exact Real.one_le_rpow h1c (by positivity)
          have hsub : Real.sqrt (3 * t / c n) - xiStar = -uAiry (c n) t / (betaTip * (c n) ^ ((2 : ℝ) / 3)) := by
            unfold uAiry
            have hp : (c n) ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcpos _).ne'
            field_simp [betaTip_pos.ne', hp]
          have hneg : -uAiry (c n) t < |CD.a| + 1 := by linarith [neg_abs_le CD.a]
          have hdiv : -uAiry (c n) t / (betaTip * (c n) ^ ((2 : ℝ) / 3)) ≤ (|CD.a| + 1) / betaTip := by
            refine div_le_div₀ (by positivity) hneg.le betaTip_pos ?_
            exact le_mul_of_one_le_right betaTip_pos.le hc23
          linarith
        have h3t : 3 * t / c n < (xiStar + (|CD.a| + 1) / betaTip + 1) ^ 2 := by
          have h1 := mul_self_lt_mul_self (Real.sqrt_nonneg _) hsqrt_lt
          rw [Real.mul_self_sqrt (div_nonneg (mul_nonneg (by norm_num) ht0.le) hcpos.le), ← sq] at h1
          exact h1
        have ht_le : t < (c n) * (xiStar + (|CD.a| + 1) / betaTip + 1) ^ 2 / 3 := by
          rw [div_lt_iff₀ hcpos] at h3t; linarith
        have hpos_b : 0 ≤ (c n) * (xiStar + (|CD.a| + 1) / betaTip + 1) ^ 2 := by
          have := xiStar_pos; have := betaTip_pos; positivity
        linarith
      have hSw_null : meas0.ν (S_w \ (Z0 ∩ Icc 0 R_bd)) = 0 :=
        measure_mono_null (fun t ht => fun htZ => ht.2 ⟨htZ, hSw_sub_bd ht.1⟩) hZ0_null
      obtain ⟨t0, ⟨⟨ht0_pos, hu0_u⟩, _⟩, ht0_atom⟩ :=
        exists_atom_in_set (hZ0_fin R_bd) hν_win hSw_null
      have ht0_supp : t0 ∈ F n ∪ Ici (B n) ∧ gs0 n t0 = 0 := by
        by_contra hbad
        exact ht0_atom.ne' (le_antisymm (le_of_eq (measure_mono_null (fun t ht => by
          rw [mem_singleton_iff.mp ht]; exact hbad) (ae_iff.1 h_ae0))) (zero_le))
      have h2r_tm : 2 * r ≤ H.tm - CD.z k := by
        have := hr_tm k hzk_lt_tm.ne
        rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hzk_lt_tm)] at this; exact this
      have ht0_notF : t0 ∉ F n := by
        rintro ⟨j, rfl⟩
        have hj_tm : H.tm ≤ j.1 := H.tm_min j.1 j.2.1
        have h4 := abs_lt.mp (hs_cl j).2.2
        linarith [hu0_u.2]
      have ht0_gt_B : B n < t0 := by
        by_contra hle; push Not at hle
        have hBt : B n = t0 := le_antisymm (ht0_supp.1.resolve_left ht0_notF) hle
        rw [← hBt] at hu0_u
        linarith [hu0_u.2, (abs_lt.mp hBu_cl).1]
      have ht0_win : |uAiry (c n) t0| ≤ M_win := by
        have hzk_in : CD.z k ∈ Icc CD.a CD.b := ⟨by linarith [(hr_win k).1], by linarith [(hr_win k).2]⟩
        have h_lo : CD.a < uAiry (c n) t0 := by linarith [hu0_u.1, (hr_win k).1]
        have h_hi : uAiry (c n) t0 < CD.b := by linarith [hu0_u.2, (hr_win k).2]
        rw [abs_le]; dsimp [M_win]
        exact ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|],
          by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|]⟩
      let u0 := chartUT (c n) t0
      have hΔu0 : virasoroDeltaChart (c n) u0 = t0 := (hC_ut2 hcut2 ht0_pos ht0_win).2.1
      have hu0_err : |uAiry (c n) t0 - u0| ≤ C_ut2 * (c n) ^ (-(2 / 3 : ℝ)) :=
        (hC_ut2 hcut2 ht0_pos ht0_win).2.2
      have hu0_ball : u0 ∈ ball (CD.z k) r := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        have := abs_lt.mp (hu0_err.trans_lt hCerr2_n)
        constructor <;> linarith [hu0_u.1, hu0_u.2]
      have hu0_vac := h_in_vac k u0 hu0_ball
      have hpsi0 : psiTilde prob (c n) (gs0 n) (u0 : ℂ) = 0 :=
        (psiTilde_eq_zero_iff prob hcpos hsh12 hwe.1 hM_we hu0_vac).2 (by rw [hΔu0, ht0_supp.2])
      -- Apply `even_analyticOrderNatAt_of_nonneg` at `u0` using `B n < t0` and `gs0 ≥ 0` on `[B n, ∞)`.
      have hu_c : (u0 : ℂ) ∈ ball (CD.z k : ℂ) r := by
        rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
        simpa [Metric.mem_ball, Real.dist_eq] using hu0_ball
      let δ_ev : ℝ := min (r - |u0 - CD.z k|) (chartUT (c n) (B n) - u0)
      have hδ_pos : 0 < δ_ev := by
        have h1 : 0 < r - |u0 - CD.z k| := by rw [Metric.mem_ball, Real.dist_eq] at hu0_ball; linarith
        have h2 : u0 < CD.z k + r := by
          have := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hu0_ball : |u0 - CD.z k| < r)
          linarith
        have h3 : H.tm - r / 4 < chartUT (c n) (B n) := by linarith [(abs_lt.mp hBc_cl).1]
        exact lt_min h1 (by linarith)
      have h_Bu_win : |uAiry (c n) (B n)| ≤ M_win := by
        have htm_in : H.tm ∈ Icc CD.a CD.b := by
          obtain ⟨k_tm, hktm⟩ := CD.hS_sub H.tm H.tm_mem
          rw [hktm]; exact ⟨by linarith [(hr_win k_tm).1], by linarith [(hr_win k_tm).2]⟩
        have htm_abs : |H.tm| ≤ max |CD.a| |CD.b| :=
          abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, htm_in.1],
            by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, htm_in.2]⟩
        rw [abs_le]; dsimp [M_win]; have := abs_lt.mp hBu_cl
        constructor <;> linarith [neg_abs_le H.tm, le_abs_self H.tm]
      have hB_vac : |chartUT (c n) (B n)| ≤ virasoroAC (c n) ^ 2 := by
        have htm_in : H.tm ∈ Icc CD.a CD.b := by
          obtain ⟨k_tm, hktm⟩ := CD.hS_sub H.tm H.tm_mem
          rw [hktm]; exact ⟨by linarith [(hr_win k_tm).1], by linarith [(hr_win k_tm).2]⟩
        have htm_abs : |H.tm| ≤ max |CD.a| |CD.b| :=
          abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, htm_in.1],
            by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, htm_in.2]⟩
        have := abs_lt.mp hBc_cl
        have h1 : |chartUT (c n) (B n)| ≤ M_ab := by
          rw [abs_le]; dsimp [M_ab]; constructor <;> linarith [neg_abs_le H.tm, le_abs_self H.tm]
        exact h1.trans hVac1
      have hΔB : virasoroDeltaChart (c n) (chartUT (c n) (B n)) = B n :=
        (hC_ut2 hcut2 hBn_pos h_Bu_win).2.1
      have hball_u0 : ball (u0 : ℂ) δ_ev ⊆ ball (CD.z k : ℂ) R' := fun w hw => by
        rw [mem_ball] at hw ⊢
        have h1 : dist (u0 : ℂ) (CD.z k : ℂ) < r := by simpa using hu_c
        have h2 : δ_ev ≤ r - |u0 - CD.z k| := min_le_left _ _
        have hdist_u0 : dist (u0 : ℂ) (CD.z k : ℂ) = |u0 - CD.z k| := by
          rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        calc dist w (CD.z k : ℂ) ≤ dist w (u0 : ℂ) + dist (u0 : ℂ) (CD.z k : ℂ) := dist_triangle _ _ _
          _ < δ_ev + |u0 - CD.z k| := by linarith [hdist_u0]
          _ ≤ r := by linarith
          _ < R' := hrR'
      obtain ⟨hw_sph_mem, hfw_sph⟩ := exists_nonzero_of_sphere hr_pos hrR' hsph_k
      have hne_top_u0 : ∃ w ∈ ball (u0 : ℂ) δ_ev, psiTilde prob (c n) (gs0 n) w ≠ 0 := by
        by_contra h_all0; push Not at h_all0
        have htop : analyticOrderAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) = ⊤ :=
          analyticOrderAt_eq_top.mpr (Eventually.mono (Metric.ball_mem_nhds (u0 : ℂ) hδ_pos) h_all0)
        exact absurd htop (order_ne_top hDiff_k hw_sph_mem hfw_sph (ball_subset_ball hrR'.le hu_c))
      have h_even := even_analyticOrderNatAt_of_nonneg (g := psiTilde prob (c n) (gs0 n))
        (hDiff_k.mono hball_u0) hδ_pos hδ_pos hne_top_u0
        (fun x hx => by
          have hx_in_r : x ∈ ball (CD.z k) r := by
            rw [Metric.mem_ball, Real.dist_eq]
            have h2 : δ_ev ≤ r - |u0 - CD.z k| := min_le_left _ _
            have htri : |x - CD.z k| ≤ |x - u0| + |u0 - CD.z k| := by
              have e : x - CD.z k = (x - u0) + (u0 - CD.z k) := by ring
              rw [e]; exact abs_add_le _ _
            linarith
          exact psiTilde_im_ofReal prob hcpos hwe.1 (h_in_vac k x hx_in_r))
        (fun x hx => by
          have hx_in_r : x ∈ ball (CD.z k) r := by
            rw [Metric.mem_ball, Real.dist_eq]
            have h2 : δ_ev ≤ r - |u0 - CD.z k| := min_le_left _ _
            have htri : |x - CD.z k| ≤ |x - u0| + |u0 - CD.z k| := by
              have e : x - CD.z k = (x - u0) + (u0 - CD.z k) := by ring
              rw [e]; exact abs_add_le _ _
            linarith
          have hx_vac := h_in_vac k x hx_in_r
          have hx_le_B : x ≤ chartUT (c n) (B n) := by
            have := min_le_right (r - |u0 - CD.z k|) (chartUT (c n) (B n) - u0)
            linarith [(abs_lt.mp hx).2]
          have hB_le_Δ : B n ≤ virasoroDeltaChart (c n) x := by
            rw [← hΔB]
            exact (virasoroDeltaChart_strictAnti hcpos).antitoneOn
              (abs_le.mp hx_vac) (abs_le.mp hB_vac) hx_le_B
          have hre := psiTilde_re_ofReal prob hcpos hwe.1 hx_vac
          have hpf := psiTilde_pref_pos prob hcpos hsh12 hM_we hx_vac
          rw [hre]
          have hgs_nn : 0 ≤ gs0 n (virasoroDeltaChart (c n) x) := hwe.2.2.2 _ (Or.inr hB_le_Δ)
          have e : (prob.cardyNorm (c n / 12) (gs0 n))⁻¹ * (-(deriv (virasoroDeltaChart (c n)) x)) *
              (gs0 n (virasoroDeltaChart (c n) x) * prob.cardyV (c n / 12) (virasoroDeltaChart (c n) x)) =
              ((prob.cardyNorm (c n / 12) (gs0 n))⁻¹ * (-(deriv (virasoroDeltaChart (c n)) x)) *
                prob.cardyV (c n / 12) (virasoroDeltaChart (c n) x)) * gs0 n (virasoroDeltaChart (c n) x) := by ring
          rw [e]; exact mul_nonneg hpf.le hgs_nn)
        hpsi0
      have hnz : 0 < analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) :=
        Nat.pos_of_ne_zero ((orderNat_ne_zero_iff hDiff_k hw_sph_mem hfw_sph (ball_subset_ball hrR'.le hu_c)).mpr hpsi0)
      have hord_ge2 : 2 ≤ analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) := by
        obtain ⟨m, hm⟩ := h_even
        omega
      have h_uniq := unique_double_zero_of_zeroCount_two hr_pos hrR' hDiff_k hsph_k hzc2 hu_c hord_ge2
      refine ⟨u0, hu0_ball, hpsi0, by rw [hΔu0, ht0_supp.2], by rw [hΔu0]; exact ht0_pos,
        by rw [hΔu0], fun htm => absurd htm hzk_lt_tm.ne, fun hmem => absurd hmem.1 hkS, ?_⟩
      simpa [hkS] using h_uniq.1
  obtain ⟨u0, hu0_ball, hpsi0, hgs0_u, hΔpos, hcu, htm_eq, hs_eq, hord_eq⟩ := hex_u0
  refine ⟨u0, ⟨hu0_ball, hpsi0, hgs0_u, hΔpos, hcu, htm_eq, hs_eq, hord_eq⟩, fun u hu => ?_⟩
  have hu_c : (u : ℂ) ∈ ball (CD.z k : ℂ) r := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
    simpa [Metric.mem_ball, Real.dist_eq] using hu.1
  have hu0_c : (u0 : ℂ) ∈ ball (CD.z k : ℂ) r := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
    simpa [Metric.mem_ball, Real.dist_eq] using hu0_ball
  by_cases hkS : CD.z k ∈ H.S
  · have hzc1 : zeroCount (psiTilde prob (c n) (gs0 n)) (CD.z k : ℂ) r = 1 := by
      simpa [hkS] using hzc_k
    exact Complex.ofReal_injective (eq_of_zeroCount_eq_one hDiff_k hr_pos hrR' hsph_k hzc1 hu_c hu0_c hu.2.1 hpsi0)
  · have hzc2 : zeroCount (psiTilde prob (c n) (gs0 n)) (CD.z k : ℂ) r = 2 := by
      simpa [hkS] using hzc_k
    have h_even_2 : 2 ≤ analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u0 : ℂ) := by
      rw [hord_eq]; simp [hkS]
    exact Complex.ofReal_injective
      ((unique_double_zero_of_zeroCount_two hr_pos hrR' hDiff_k hsph_k hzc2 hu0_c h_even_2).2
        (u : ℂ) hu_c hu.2.1)

end FormalResearch.ModularBootstrap.FixedWeight
