module

public import FormalResearch.ModularBootstrap.FoldTip.FixedWeightCrossing
public import FormalResearch.ModularBootstrap.FoldTip.ProfWinLimit
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWInterface
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Wiring

/-!
# Paper I `ft:H4b` for all fixed-weight crossing problems (`ShellHBData.airy`)

Proves `FTH4b ShellHBData.airy (fwCrossingData prob)` unconditionally at every weight `prob.w`:

* Support bounds (`fw_support_upper`, `fw_support_limit`): from `fixedWeightLowerBoundInput_of_problem`,
  `spectralMeasure_Ioi_eq_zero`, and `eventually_uAiry_le_of_gap`.
* Diagonal `(D1)–(D4)` construction (`ftDesign_of_diagonal`): combines `bumpEventual` (`EventualCombData`)
  with `profWin_disp_tendstoLocallyUniformly_C` and `profWin_disp_V_tendsto`.
* `fwH4bW prob`: `FTH4b ShellHBData.airy (fwCrossingData prob)` at every fixed weight `prob.w`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal Real Polynomial

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.Special FormalResearch.SignUncertainty
  FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight
  FormalResearch.ModularBootstrap.FixedWeightBand
  FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.ModularBootstrap.Upper.Assembly

/-! ### 1. Support hypotheses for `fwCrossingData prob` -/

private lemma fw_support_upper (prob : FixedWeightProblem) :
    ∃ B : ℝ, ∀ᶠ c : ℝ in atTop, ∀ ν ∈ (fwCrossingData prob).extremal c,
      IsLocallyFiniteMeasure ((fwCrossingData prob).window c ν) ∧
      (fwCrossingData prob).window c ν (Ioi B) = 0 := by
  obtain ⟨c₁, D, hc₁, -, hlo⟩ := fixedWeightLowerBoundInput_of_problem prob
  refine ⟨airyZero 1 + 1, ?_⟩
  have hξ := xiStar_pos
  have hβ := betaTip_pos
  set z : ℝ := -(xiStar / (3 * betaTip))
  have hlim2 : Tendsto (fun c : ℝ => uAiry c (TStar c + (z / 2) * c ^ ((1 : ℝ) / 3)))
      atTop (𝓝 (airyZero 1 + 1 / 4)) := by
    have h := tendsto_uAiry_shift (z / 2)
    have heq : airyZero 1 - 3 * betaTip * (z / 2) / (2 * xiStar) = airyZero 1 + 1 / 4 := by
      dsimp [z]; field_simp; ring
    rwa [heq] at h
  have hlt1 : ∀ᶠ c : ℝ in atTop, uAiry c (TStar c + (z / 2) * c ^ ((1 : ℝ) / 3)) ≤ airyZero 1 + 1 :=
    (hlim2.eventually (Iio_mem_nhds (by linarith : airyZero 1 + 1 / 4 < airyZero 1 + 1))).mono
      fun _ h => h.le
  have hzneg : z / 2 < 0 := by
    dsimp [z]; linarith [div_pos hξ (mul_pos (by norm_num : (0 : ℝ) < 3) hβ)]
  have hc3 : Tendsto (fun c : ℝ => -(z / 2) * c ^ ((1 : ℝ) / 3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul_atTop (by linarith)
  filter_upwards [eventually_ge_atTop c₁, hc3.eventually_ge_atTop D, hlt1] with c hc hDc hule
  intro ν hν
  obtain ⟨meas, rfl, hcpos, hshift, hTV, hgap, -⟩ := hν
  have ha : prob.totalShift ≤ c / 12 := by linarith
  refine ⟨isLocallyFiniteMeasure_spectralMeasure prob hcpos ha meas hTV hgap, ?_⟩
  have hτ_le : TStar c + (z / 2) * c ^ ((1 : ℝ) / 3) ≤ prob.T_V c := by
    have h1 := hlo hc
    linarith
  have hu_le : uAiry c (prob.T_V c) ≤ airyZero 1 + 1 :=
    (uAiry_antitone hcpos hτ_le).trans hule
  exact measure_mono_null (Ioi_subset_Ioi hu_le) (spectralMeasure_Ioi_eq_zero prob hcpos meas hgap)

private lemma fw_support_limit (prob : FixedWeightProblem) :
    ∀ (cs : ℕ → ℝ) (νs : ℕ → Measure ℝ) (xs : ℕ → ℝ) (x : ℝ),
      Tendsto cs atTop atTop →
      (∀ k, νs k ∈ (fwCrossingData prob).extremal (cs k)) →
      (∀ k, xs k ∈ ((fwCrossingData prob).window (cs k) (νs k)).support) →
      Tendsto xs atTop (𝓝 x) → x ∈ hbSupport ShellHBData.airy := by
  intro cs νs xs x hcs hν hxs hx
  have hLo := fixedWeightLowerBoundInput_of_problem prob
  have hgap : GapCondition cs (fun k => prob.T_V (cs k)) :=
    gapCondition_of_lowerBound hLo hcs fun _ => le_rfl
  have hx_le : x ≤ airyZero 1 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hev := eventually_uAiry_le_of_gap hcs hgap δ hδ
    have hk_le : ∀ᶠ k in atTop, xs k ≤ airyZero 1 + δ := by
      filter_upwards [hev] with k hk
      obtain ⟨meas, hmeq, hcpos, _, -, hgap_k, -⟩ := hν k
      have hzero : ((fwCrossingData prob).window (cs k) (νs k)) (Ioi (uAiry (cs k) (prob.T_V (cs k)))) = 0 := by
        change spectralMeasure prob (cs k) (νs k) (Ioi (uAiry (cs k) (prob.T_V (cs k)))) = 0
        rw [← hmeq]
        exact spectralMeasure_Ioi_eq_zero prob hcpos meas hgap_k
      have hxs_le : xs k ≤ uAiry (cs k) (prob.T_V (cs k)) := by
        by_contra hgt
        push Not at hgt
        have hpos : 0 < ((fwCrossingData prob).window (cs k) (νs k)) (Ioi (uAiry (cs k) (prob.T_V (cs k)))) :=
          (Measure.mem_support_iff_forall (xs k)).1 (hxs k) _ (isOpen_Ioi.mem_nhds hgt)
        exact hpos.ne' hzero
      exact hxs_le.trans hk
    exact le_of_tendsto_of_frequently hx hk_le.frequently
  exact Or.inr hx_le

/-! ### 2. `EventualCombData` and diagonal extraction to `FTDesign` -/

private lemma eventualComb_to_ftDesign {prob : FixedWeightProblem} {D : Window}
    (E : EventualCombData prob D) {b : ℝ} (hb : b < D.uF) :
    FTDesign (fwCrossingData prob) D.W := by
  refine ⟨D.continuous, D.integrable, fun c u => E.scale c * psiAiry prob c (E.g c) u, ?_⟩
  have h_b : ∀ᶠ c in atTop, b ≤ uAiry c (E.tf c + 1) :=
    E.theta.eventually (Ici_mem_nhds hb)
  have h_c12 : ∀ᶠ c in atTop, max 1 (12 * prob.totalShift) ≤ c :=
    eventually_ge_atTop _
  obtain ⟨c0, hc0⟩ := eventually_atTop.1 (E.good.and h_c12)
  refine ⟨⟨c0, fun c hc => ?_⟩, ⟨b, ?_⟩, ?_, ?_⟩
  · obtain ⟨⟨hcpos, hsc, hg_tc, ⟨C, hC, hdecay⟩, -, -⟩, h12⟩ := hc0 c hc
    have ha : prob.totalShift ≤ c / 12 := by linarith [(le_max_right (1 : ℝ) _).trans h12]
    refine ⟨continuous_const.mul (continuous_psiAiry hcpos hg_tc.cont),
      (integrable_psiAiry_of_testClass prob hcpos ha hg_tc).const_mul _, fun ν hν => ?_⟩
    obtain ⟨meas, rfl, -, -, hTV, hgap, -⟩ := hν
    have hν0 := nu_zero_eq_zero hTV hgap
    obtain ⟨hint_mu, -, heq⟩ := spectral_poisson_summation_comb prob hcpos ha meas hν0 hg_tc hC hdecay
    refine ⟨hint_mu.const_mul _, ?_⟩
    change ∫ u, E.scale c * psiAiry prob c (E.g c) u ∂(spectralMeasure prob c meas.ν) ≤
      ∫ u, E.scale c * psiAiry prob c (E.g c) u
    rw [integral_const_mul, integral_const_mul, heq]
  · filter_upwards [E.good, h_c12, h_b] with c hcgood h12 hb_u u hub
    obtain ⟨hcpos, hsc, -, -, htf0, hg_nn⟩ := hcgood
    have ha : prob.totalShift ≤ c / 12 := by linarith [(le_max_right (1 : ℝ) _).trans h12]
    exact mul_nonneg hsc.le (psiAiry_nonneg hcpos ha htf0 hg_nn (hub.trans hb_u))
  · rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have hR0 : 0 ≤ max R 0 := le_max_right _ _
    filter_upwards [E.window (max R 0) hR0 (ε / 2) (half_pos hε)] with c hc u hu
    have hu_le : |u| ≤ max R 0 := (Real.norm_eq_abs u ▸ hR u hu).trans (le_max_left _ _)
    rw [Real.dist_eq, abs_sub_comm]
    exact (hc u (abs_le.mp hu_le)).trans_lt (by linarith)
  · intro ε hε
    filter_upwards [E.limsup ε hε] with c hc
    exact hc

private noncomputable def diagSeq (cₙ : ℕ → ℝ) : ℕ → ℝ
  | 0 => cₙ 0
  | n + 1 => max (diagSeq cₙ n + 1) (cₙ (n + 1))

private lemma diagSeq_succ_ge (cₙ : ℕ → ℝ) (n : ℕ) : diagSeq cₙ n + 1 ≤ diagSeq cₙ (n + 1) :=
  le_max_left _ _

private lemma diagSeq_le (cₙ : ℕ → ℝ) (n : ℕ) : cₙ n ≤ diagSeq cₙ n := by
  cases n with
  | zero => exact le_rfl
  | succ k => exact le_max_right _ _

private lemma diagSeq_strictMono (cₙ : ℕ → ℝ) : StrictMono (diagSeq cₙ) :=
  strictMono_nat_of_lt_succ fun n => by linarith [diagSeq_succ_ge cₙ n]

private lemma diagSeq_add_le (cₙ : ℕ → ℝ) (n : ℕ) : diagSeq cₙ 0 + (n : ℝ) ≤ diagSeq cₙ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hsucc := diagSeq_succ_ge cₙ k
      push_cast; linarith

private lemma ftDesign_of_diagonal (prob : FixedWeightProblem) (D : ℕ → Window)
    (E : ∀ n : ℕ, EventualCombData prob (D n)) (W : ℝ → ℝ) (hWc : Continuous W) (hWi : Integrable W)
    {b : ℝ} (hb : ∀ n : ℕ, b < (D n).uF)
    (hloc : TendstoLocallyUniformly (fun n u => (D n).W u) W atTop)
    (hVlim : Tendsto (fun n => (D n).V) atTop (𝓝 (∫ u, W u))) :
    FTDesign (fwCrossingData prob) W := by
  have hc_thresh : ∀ n : ℕ, ∃ cₙ : ℝ, 1 ≤ cₙ ∧ 12 * prob.totalShift ≤ cₙ ∧
      (∀ c ≥ cₙ, 0 < c ∧ 0 < (E n).scale c ∧ TestClass prob (c / 12) ((E n).g c) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
          |(E n).g c t| ≤ C * Real.exp (-4 * π * √(c / 12 * t) - π * √(3 * t / c))) ∧
        0 ≤ (E n).tf c + 1 ∧ (∀ t : ℝ, (E n).tf c + 1 ≤ t → 0 ≤ (E n).g c t) ∧
        b ≤ uAiry c ((E n).tf c + 1) ∧
        (∀ u ∈ Icc (-(n : ℝ)) n,
          |(E n).scale c * psiAiry prob c ((E n).g c) u - (D n).W u| ≤ 1 / ((n : ℝ) + 1)) ∧
        ∫ u, (E n).scale c * psiAiry prob c ((E n).g c) u ≤ (D n).V + 1 / ((n : ℝ) + 1)) := by
    intro n
    have hn_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h_b : ∀ᶠ c in atTop, b ≤ uAiry c ((E n).tf c + 1) :=
      (E n).theta.eventually (Ici_mem_nhds (hb n))
    have h_ev := (((E n).good.and h_b).and
      (((E n).window n (Nat.cast_nonneg n) (1 / ((n : ℝ) + 1)) hn_pos).and
        ((E n).limsup (1 / ((n : ℝ) + 1)) hn_pos))).and
      (eventually_ge_atTop (max 1 (12 * prob.totalShift)))
    obtain ⟨cₙ, hcₙ⟩ := eventually_atTop.1 h_ev
    refine ⟨max cₙ (max 1 (12 * prob.totalShift)), le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _), fun c hc => ?_⟩
    obtain ⟨⟨⟨⟨hc1, hc2, hc3, hc4, hc5, hc6⟩, hb_u⟩, ⟨hwin, hlim⟩⟩, -⟩ :=
      hcₙ c ((le_max_left _ _).trans hc)
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hb_u, hwin, hlim⟩
  choose cₙ hc1 hc12 hspec using hc_thresh
  let C := diagSeq cₙ
  have hC_tend : Tendsto C atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt (b - diagSeq cₙ 0)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := diagSeq_add_le cₙ n
    have h2 : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  classical
  let idx : ℝ → ℕ := fun c => sSup {n : ℕ | C n ≤ c}
  have hidx_mem : ∀ c : ℝ, C 0 ≤ c → C (idx c) ≤ c ∧ ∀ m, m ∈ {n : ℕ | C n ≤ c} → m ≤ idx c := by
    intro c hc
    have hne : ({n : ℕ | C n ≤ c}).Nonempty := ⟨0, hc⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hC_tend.eventually_gt_atTop c)
    have hbdd : BddAbove {n : ℕ | C n ≤ c} := ⟨N, fun m hm => le_of_not_gt fun hgt =>
      absurd (hN m hgt.le) (not_lt.mpr hm)⟩
    exact ⟨Nat.sSup_mem hne hbdd, fun m hm => le_csSup hbdd hm⟩
  have hidx_tend : Tendsto idx atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨max (C 0) (C N), fun c hc => ?_⟩
    exact (hidx_mem c ((le_max_left _ _).trans hc)).2 N ((le_max_right _ _).trans hc)
  let U : ℝ → ℝ → ℝ := fun c u => (E (idx c)).scale c * psiAiry prob c ((E (idx c)).g c) u
  refine ⟨hWc, hWi, U, ?_, ⟨b, ?_⟩, ?_, ?_⟩
  · refine ⟨C 0, fun c hc => ?_⟩
    have hc_ge := (diagSeq_le cₙ (idx c)).trans (hidx_mem c hc).1
    obtain ⟨hcpos, hsc, hg_tc, ⟨M, hM, hdecay⟩, -, -, -, -, -⟩ := hspec (idx c) c hc_ge
    have ha : prob.totalShift ≤ c / 12 := by linarith [hc12 (idx c), hc_ge]
    refine ⟨continuous_const.mul (continuous_psiAiry hcpos hg_tc.cont),
      (integrable_psiAiry_of_testClass prob hcpos ha hg_tc).const_mul _, fun ν hν => ?_⟩
    obtain ⟨meas, rfl, -, -, hTV, hgap, -⟩ := hν
    have hν0 := nu_zero_eq_zero hTV hgap
    obtain ⟨hint_mu, -, heq⟩ := spectral_poisson_summation_comb prob hcpos ha meas hν0 hg_tc hM hdecay
    refine ⟨hint_mu.const_mul _, ?_⟩
    change ∫ u, U c u ∂(spectralMeasure prob c meas.ν) ≤ ∫ u, U c u
    dsimp [U]
    rw [integral_const_mul, integral_const_mul, heq]
  · filter_upwards [eventually_ge_atTop (C 0)] with c hc u hub
    have hc_ge := (diagSeq_le cₙ (idx c)).trans (hidx_mem c hc).1
    obtain ⟨hcpos, hsc, -, -, htf0, hg_nn, hb_u, -, -⟩ := hspec (idx c) c hc_ge
    have ha : prob.totalShift ≤ c / 12 := by linarith [hc12 (idx c), hc_ge]
    exact mul_nonneg hsc.le (psiAiry_nonneg hcpos ha htf0 hg_nn (hub.trans hb_u))
  · rw [tendstoLocallyUniformly_iff_forall_isCompact] at hloc ⊢
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have h1 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ε / 3 :=
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 3))).mono fun _ h => h.le
    have h2 : ∀ᶠ n : ℕ in atTop, ∀ x ∈ K, dist (W x) ((D n).W x) < ε / 2 :=
      Metric.tendstoUniformlyOn_iff.mp (hloc K hK) (ε / 2) (half_pos hε)
    have hR_nat : ∀ᶠ n : ℕ in atTop, max R 0 ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (max R 0)
    filter_upwards [eventually_ge_atTop (C 0), hidx_tend.eventually (h1.and (h2.and hR_nat))]
      with c hc ⟨hn1, hnW, hnR⟩ u hu
    have hc_ge := (diagSeq_le cₙ (idx c)).trans (hidx_mem c hc).1
    obtain ⟨-, -, -, -, -, -, -, hwin, -⟩ := hspec (idx c) c hc_ge
    have hu_abs : |u| ≤ (idx c : ℝ) :=
      (Real.norm_eq_abs u ▸ hR u hu).trans ((le_max_left R 0).trans hnR)
    have hnWu : |(D (idx c)).W u - W u| < ε / 2 := by
      have h := hnW u hu
      rwa [Real.dist_eq, abs_sub_comm] at h
    rw [Real.dist_eq, abs_sub_comm]
    have h_tri : |U c u - W u| ≤ |U c u - (D (idx c)).W u| + |(D (idx c)).W u - W u| := by
      have : U c u - W u = (U c u - (D (idx c)).W u) + ((D (idx c)).W u - W u) := by ring
      rw [this]; exact abs_add_le _ _
    linarith [hwin u (abs_le.mp hu_abs), hnWu]
  · intro ε hε
    have h1 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ε / 2 :=
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 2))).mono fun _ h => h.le
    have h2 : ∀ᶠ n : ℕ in atTop, (D n).V < (∫ u, W u) + ε / 2 :=
      hVlim.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [eventually_ge_atTop (C 0), hidx_tend.eventually (h1.and h2)] with c hc ⟨hn1, hnV⟩
    have hc_ge := (diagSeq_le cₙ (idx c)).trans (hidx_mem c hc).1
    obtain ⟨-, -, -, -, -, -, -, -, hlim⟩ := hspec (idx c) c hc_ge
    linarith

private lemma ftDesign_profWin_ideal (prob : FixedWeightProblem) (s : ℕ) (hs : 2 ≤ s)
    (b uF : ℝ) (W_ideal : ℂ → ℂ) (hW_cl : InAiryClass W_ideal)
    (hW_eq : ∀ z : ℂ, (∀ k : ℕ, 1 ≤ k → z ≠ (airyZero k : ℂ)) →
      W_ideal z = ((z - (b : ℂ)) / (z - (airyZero s : ℂ))) ^ 2 *
        ((z - (uF : ℂ)) / (z - (airyZero 1 : ℂ))) * ShellHBData.airy.G z)
    (hW_zeros : ∀ n : ℕ, n ≠ 0 → n ≠ s - 1 → (W_ideal (airyNode n : ℂ)).re = 0) :
    FTDesign (fwCrossingData prob) (fun u : ℝ => (W_ideal (u : ℂ)).re) := by
  let e := dispE s (b - airyZero s)
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 4)
  have hη0 : ∀ n : ℕ, 0 < η n := fun _ => by dsimp [η]; positivity
  have hη1 : ∀ n : ℕ, η n ≤ 1 / 4 := fun n => by
    dsimp [η]; rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  let D : ℕ → Window := fun n =>
    profWin (dispSite (s + n) e) (designWidthU (s + n) (η n))
      (dispTailHyp s (b - airyZero s) (s + n) (hη0 n).le (hη1 n))
      (fun k hk => by
        unfold designWidthU
        exact mul_ne_zero (by split_ifs <;> [exact (hη0 n).ne'; norm_num]) (gapWKB_pos (by omega)).ne')
      (airyZero 1 - uF)
  let E : ∀ n : ℕ, EventualCombData prob (D n) := fun n =>
    bumpEventual prob (s + n) (by omega) (hη0 n) (hη1 n) (dispSigma (airyZero 1 - uF) e) (D n)
      (by funext u; dsimp [D]; rw [profWin_W]
          show (profW (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (u : ℂ)).re =
            (sigWindowW (s + n) (η n) (dispSigma (airyZero 1 - uF) e) (u : ℂ)).re
          rw [sigWindowW_dispSite (s + n) (η n) (airyZero 1 - uF) e (fun k hk => dispE_of_ne _ (by omega))])
      (by dsimp [D]; rw [profWin_uF, dispSigma_one])
  have hlocC := profWin_disp_tendstoLocallyUniformly_C s hs b uF W_ideal hW_cl.1 hW_eq
  have hloc : TendstoLocallyUniformly (fun n (u : ℝ) => (D n).W u)
      (fun u : ℝ => (W_ideal (u : ℂ)).re) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact] at hlocC ⊢
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hKc : IsCompact (Complex.ofReal '' K) := hK.image Complex.continuous_ofReal
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hlocC (Complex.ofReal '' K) hKc) ε hε]
      with n hn u hu
    have h1 := hn (u : ℂ) ⟨u, hu, rfl⟩
    dsimp [D]; rw [profWin_W]
    have hd : dist ((W_ideal (u : ℂ)).re)
        ((profW (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (u : ℂ)).re) ≤
        dist (W_ideal (u : ℂ))
          (profW (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (u : ℂ)) := by
      rw [Real.dist_eq, Complex.dist_eq, ← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    exact hd.trans_lt h1
  have hV := profWin_disp_V_tendsto s hs b uF W_ideal hW_cl hW_eq hW_zeros
  have hWc : Continuous (fun u : ℝ => (W_ideal (u : ℂ)).re) :=
    Complex.continuous_re.comp (hW_cl.1.continuous.comp Complex.continuous_ofReal)
  have hWi : Integrable (fun u : ℝ => (W_ideal (u : ℂ)).re) := hW_cl.2.1.re
  refine ftDesign_of_diagonal prob D E _ hWc hWi (b := uF - 1) ?_ hloc hV
  intro n
  dsimp [D]; rw [profWin_uF]; linarith

/-! ### 3. Main theorem: `fwH4bW` at every fixed weight `prob.w` -/

/-- **Hypothesis `ft:H4b` at Airy level (`ShellHBData.airy`) for every fixed-weight problem,
unconditionally at every weight `prob.w`.** -/
theorem fwH4bW (prob : FixedWeightProblem) :
    FTH4b ShellHBData.airy (fwCrossingData prob) := by
  refine ⟨fw_support_upper prob, fw_support_limit prob, ?_, ?_, ?_, ?_⟩
  · let D₀ := designWin 1 (by norm_num : (0 : ℝ) < 1 / 4) (-1)
    refine ⟨D₀.W, fun u hu => ?_, ?_⟩
    · have hu' : u ≤ airyZero 1 := by
        rcases hu with hS | hI
        · simp only [ShellHBData.airy, Finset.coe_singleton, Set.mem_singleton_iff] at hS
          exact hS.le
        · exact hI
      dsimp only [D₀, designWin]
      rw [profWin_W]
      have hH : AiryProdTailHypothesis 1 (designSiteU 1) (designWidthU 1 (1 / 4)) :=
        design_tail_hypothesis 1 (1 / 4)
      have hε : ∀ k : ℕ, 1 < k → designWidthU 1 (1 / 4) k ≠ 0 := fun k hk => by
        unfold designWidthU
        exact mul_ne_zero (by split_ifs <;> norm_num) (gapWKB_pos (by omega)).ne'
      exact airyWindowProd_re_pos (f := 1) (airyZero 1 - (-1)) hH hε (by linarith : u < airyZero 1 - (-1))
    · have hE := bumpEventual prob 1 le_rfl (by norm_num) le_rfl (designSigma1 (-1)) D₀
        (designWin_W_eq_sig 1 (by norm_num) (-1)) (designWin_uF_eq_sig 1 (by norm_num) (-1))
      exact eventualComb_to_ftDesign hE (by dsimp [D₀, designWin]; rw [profWin_uF]; linarith)
  · refine ftDesign_profWin_ideal prob 2 le_rfl (airyZero 2) (airyZero 1) ShellHBData.airy.G
      ShellHBData.airy.G_inAiryClass (fun z hnz => ?_) (fun n _ _ => ?_)
    · have h1 : z - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr (hnz 1 le_rfl)
      have h2 : z - (airyZero 2 : ℂ) ≠ 0 := sub_ne_zero.mpr (hnz 2 (by omega))
      rw [div_self h2, div_self h1, one_pow, one_mul, one_mul]
    · rw [← hbZeroEnum_airy_eq n, hb_G_eq_zero_at_zero ShellHBData.airy n, Complex.zero_re]
  · intro z hz
    have hztm : z = ShellHBData.airy.tm := by simpa [ShellHBData.airy] using hz
    refine ⟨1, one_pos, fun p _ _ _ => ?_⟩
    obtain ⟨hcl, -, hother, -, -⟩ := hb_simple_test_props ShellHBData.airy hz p
    refine ftDesign_profWin_ideal prob 2 le_rfl (airyZero 2) p (hbSimpleTest ShellHBData.airy z p) hcl
      (fun w hnz => ?_) (fun n hn _ => ?_)
    · have h1 : w - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr (hnz 1 le_rfl)
      have h2 : w - (airyZero 2 : ℂ) ≠ 0 := sub_ne_zero.mpr (hnz 2 (by omega))
      have hz' : z = airyZero 1 := hztm
      unfold hbSimpleTest
      rw [dslope_of_ne _ (by rw [hz']; exact hnz 1 le_rfl), slope_def_field,
        ShellHBData.airy.G_eq_zero_on_S z hz, sub_zero, div_self h2, one_pow, one_mul, hz']
      push_cast; field_simp; ring
    · rw [← hbZeroEnum_airy_eq n]
      refine hother n ?_
      rw [hbZeroEnum_airy_eq n, hztm]
      intro h
      change airyZero (n + 1) = airyZero 1 at h
      exact hn (by have := airyZero_injective_on (m := n + 1) (n := 1) (by omega) le_rfl h; omega)
  · intro k hk b q _ _ _ _ _ _
    have hcard : ShellHBData.airy.S.card = 1 := by simp [ShellHBData.airy]
    have hk1 : 1 ≤ k := by omega
    obtain ⟨hcl, -, hother, -, -, -⟩ := hb_paired_test_props ShellHBData.airy hk b q
    have hzk : hbZeroEnum ShellHBData.airy k = airyZero (k + 1) := hbZeroEnum_airy_eq k
    refine ftDesign_profWin_ideal prob (k + 1) (by omega) b q (hbPairedTest ShellHBData.airy k b q) hcl
      (fun w hnz => ?_) (fun n hn hns => ?_)
    · have h1 : w - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr (hnz 1 le_rfl)
      have hs : w - (airyZero (k + 1) : ℂ) ≠ 0 := sub_ne_zero.mpr (hnz (k + 1) (by omega))
      have htm1 : ShellHBData.airy.tm = airyZero 1 := rfl
      let H1 : ℂ → ℂ := fun v => ShellHBData.airy.G v + ((ShellHBData.airy.tm - q : ℝ) : ℂ) *
        dslope ShellHBData.airy.G (ShellHBData.airy.tm : ℂ) v
      let H2 : ℂ → ℂ := fun v => H1 v + ((hbZeroEnum ShellHBData.airy k - b : ℝ) : ℂ) *
        dslope H1 (hbZeroEnum ShellHBData.airy k : ℂ) v
      have hH1_w : H1 w = ((w - (q : ℂ)) / (w - (airyZero 1 : ℂ))) * ShellHBData.airy.G w := by
        dsimp [H1]
        rw [dslope_of_ne _ (by rw [htm1]; exact hnz 1 le_rfl), slope_def_field,
          ShellHBData.airy.G_eq_zero_on_S _ ShellHBData.airy.tm_mem, sub_zero, htm1]
        push_cast; field_simp; ring
      have hH1_zk : H1 (hbZeroEnum ShellHBData.airy k : ℂ) = 0 := by
        have hzc : (hbZeroEnum ShellHBData.airy k : ℂ) ≠ (airyZero 1 : ℂ) := by
          rw [hzk]; intro h; exact absurd (Complex.ofReal_injective h)
            ((airyZero_lt_of_lt le_rfl (by omega : 1 < k + 1)).ne)
        dsimp [H1]
        rw [dslope_of_ne _ (by rw [htm1]; exact hzc), slope_def_field,
          ShellHBData.airy.G_eq_zero_on_S _ ShellHBData.airy.tm_mem, sub_zero,
          hb_G_eq_zero_at_zero ShellHBData.airy k, htm1]
        ring
      have hH2_w : H2 w = ((w - (b : ℂ)) / (w - (airyZero (k + 1) : ℂ))) * H1 w := by
        dsimp [H2]
        rw [dslope_of_ne _ (by rw [hzk]; exact hnz (k + 1) (by omega)), slope_def_field, hH1_zk, sub_zero, hzk]
        push_cast; field_simp; ring
      have hG'_zk : deriv ShellHBData.airy.G (hbZeroEnum ShellHBData.airy k : ℂ) = 0 := by
        have he := fun u => ShellHBData.airy.G_prod_eq u
        have hzk_S : hbZeroEnum ShellHBData.airy k ∉ ShellHBData.airy.S := by
          rw [hzk]; simp only [ShellHBData.airy, Finset.mem_singleton]
          exact (airyZero_lt_of_lt le_rfl (by omega : 1 < k + 1)).ne
        have hN_zk : airyPQN ShellHBData.airy.P ShellHBData.airy.Q (hbZeroEnum ShellHBData.airy k : ℂ) = 0 := by
          rw [hzk]; unfold airyPQN
          have h1c : airyPQc (1 : ℝ[X]) (airyZero (k + 1) : ℂ) = 1 := by
            rw [← Polynomial.C_1]; exact airyPQc_C (1 : ℝ) _
          simp only [ShellHBData.airy]
          rw [airyPQc_zero, zero_mul, add_zero, h1c, one_mul, airyAiC_airyZero]
        have hd1 : deriv (fun u => ShellHBData.airy.G u * at47_pr ShellHBData.airy.S u)
              (hbZeroEnum ShellHBData.airy k : ℂ) =
            deriv ShellHBData.airy.G (hbZeroEnum ShellHBData.airy k : ℂ) *
                at47_pr ShellHBData.airy.S (hbZeroEnum ShellHBData.airy k : ℂ) +
              ShellHBData.airy.G (hbZeroEnum ShellHBData.airy k : ℂ) *
                deriv (at47_pr ShellHBData.airy.S) (hbZeroEnum ShellHBData.airy k : ℂ) :=
          ((ShellHBData.airy.G_diff _).hasDerivAt.mul
            ((at47_pr_differentiable ShellHBData.airy.S _).hasDerivAt)).deriv
        have hd2 : deriv (fun u => (((-1 : ℝ) ^ ShellHBData.airy.S.card : ℝ) : ℂ) *
              airyPQN ShellHBData.airy.P ShellHBData.airy.Q u ^ 2)
              (hbZeroEnum ShellHBData.airy k : ℂ) = 0 := by
          have hsq := ((differentiable_airyPQN ShellHBData.airy.P ShellHBData.airy.Q
            (hbZeroEnum ShellHBData.airy k : ℂ)).hasDerivAt.pow 2)
          have hcm := (hsq.const_mul ((((-1 : ℝ) ^ ShellHBData.airy.S.card : ℝ) : ℂ))).deriv
          rw [hN_zk, pow_one, mul_zero, zero_mul, mul_zero] at hcm
          exact hcm
        rw [show (fun u => ShellHBData.airy.G u * at47_pr ShellHBData.airy.S u) = _ from funext he,
          hd2, hb_G_eq_zero_at_zero ShellHBData.airy k, zero_mul, add_zero] at hd1
        exact (mul_eq_zero.mp hd1.symm).resolve_right (at47_pr_ne_zero hzk_S)
      have hH1'_zk : deriv H1 (hbZeroEnum ShellHBData.airy k : ℂ) = 0 := by
        have hzkc : (hbZeroEnum ShellHBData.airy k : ℂ) ≠ (airyZero 1 : ℂ) := by
          rw [hzk]; intro h; exact absurd (Complex.ofReal_injective h)
            ((airyZero_lt_of_lt le_rfl (by omega : 1 < k + 1)).ne)
        have hev : H1 =ᶠ[𝓝 (hbZeroEnum ShellHBData.airy k : ℂ)]
            fun u => ((u - (q : ℂ)) / (u - (airyZero 1 : ℂ))) * ShellHBData.airy.G u := by
          filter_upwards [isOpen_ne.mem_nhds hzkc] with u hu
          dsimp [H1]
          rw [dslope_of_ne _ (by rw [htm1]; exact hu), slope_def_field,
            ShellHBData.airy.G_eq_zero_on_S _ ShellHBData.airy.tm_mem, sub_zero, htm1]
          have hne : u - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr hu
          push_cast; field_simp; ring
        rw [hev.deriv_eq]
        have hd_rat : HasDerivAt (fun u : ℂ => (u - (q : ℂ)) / (u - (airyZero 1 : ℂ)))
            (((1 : ℂ) * ((hbZeroEnum ShellHBData.airy k : ℂ) - (airyZero 1 : ℂ)) -
              ((hbZeroEnum ShellHBData.airy k : ℂ) - (q : ℂ)) * 1) /
              ((hbZeroEnum ShellHBData.airy k : ℂ) - (airyZero 1 : ℂ)) ^ 2)
            (hbZeroEnum ShellHBData.airy k : ℂ) :=
          ((hasDerivAt_id _).sub_const (q : ℂ)).div ((hasDerivAt_id _).sub_const (airyZero 1 : ℂ))
            (sub_ne_zero.mpr hzkc)
        have hm := (hd_rat.mul (ShellHBData.airy.G_diff _).hasDerivAt).deriv
        change deriv (fun u => (u - ↑q) / (u - ↑(airyZero 1)) * ShellHBData.airy.G u) _ = _ at hm
        simp [hm, hb_G_eq_zero_at_zero ShellHBData.airy k, hG'_zk]
      have hH2_zk : H2 (hbZeroEnum ShellHBData.airy k : ℂ) = 0 := by
        dsimp [H2]; rw [hH1_zk, dslope_same, hH1'_zk, mul_zero, add_zero]
      show H2 w + ((hbZeroEnum ShellHBData.airy k - b : ℝ) : ℂ) *
          dslope H2 (hbZeroEnum ShellHBData.airy k : ℂ) w = _
      rw [dslope_of_ne _ (by rw [hzk]; exact hnz (k + 1) (by omega)), slope_def_field, hH2_zk, sub_zero,
        hzk, hH2_w, hH1_w]
      push_cast; field_simp; ring
    · rw [← hbZeroEnum_airy_eq n]
      refine hother n ?_ ?_
      · rw [hbZeroEnum_airy_eq n, hzk]
        intro h
        exact hns (by have := airyZero_injective_on (by omega) (by omega) h; omega)
      · rw [hbZeroEnum_airy_eq n]
        intro h
        change airyZero (n + 1) = ShellHBData.airy.tm at h
        have htm1 : ShellHBData.airy.tm = airyZero 1 := rfl
        rw [htm1] at h
        exact hn (by have := airyZero_injective_on (m := n + 1) (n := 1) (by omega) le_rfl h; omega)

end FormalResearch.ModularBootstrap.FoldTip

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fwH4bW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.fwH4bW
