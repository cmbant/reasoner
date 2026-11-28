module

public import FormalResearch.ModularBootstrap.Duality.Primal.HbClustersMain

/-!
# Main `dsl:hb-clusters` theorem (`Theorem E'-HB`, part (a))

Packages the canonical Hurwitz isolation from `HbClustersMain.lean` into:
* `hb_clusters` (`dsl:hb-clusters` (a)): measure-independent cluster positions `tStar k n`,
  simple/double multiplicities at every weak extremal, exact window support of every attaining
  measure, uniform normalised weight convergence to `ω k`, and uniform `dsl:hb-raw` asymptotic.

Part (a) near-optimal prescribed-site asymptotics (`hb_clusters_prescribed_raw`) and part (b)
inactivity (`hb_clusters_inactive`) live in `Duality/Primal/HbClustersExtras.lean`.
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

/-- Helper: `meas.ν {t₀} = 0` if `∀ᵐ t ∂meas.ν, P t` and `¬ P t₀`, or contrapositively `0 < meas.ν {t₀} → P t₀`. -/
private lemma prop_of_pos_singleton {ν : Measure ℝ} {P : ℝ → Prop}
    (hae : ∀ᵐ t ∂ν, P t) {t₀ : ℝ} (hpos : 0 < ν {t₀}) : P t₀ := by
  by_contra hnot
  have h0 : ν {t₀} = 0 :=
    measure_mono_null (fun t ht => by rw [mem_singleton_iff.mp ht]; exact hnot) (ae_iff.1 hae)
  exact hpos.ne' h0

/-- Exact one-level HB cluster structure (`dsl:hb-clusters` (a)). -/
theorem hb_clusters (prob : FixedWeightProblem) (H : HermiteBiehlerData)
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
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k)))) :
    ∃ tStar : Fin CD.K → ℕ → ℝ,
      (∀ k : Fin CD.K, Tendsto (fun n => uAiry (c n) (tStar k n)) atTop (𝓝 (CD.z k)) ∧
        Tendsto (fun n => chartUT (c n) (tStar k n)) atTop (𝓝 (CD.z k))) ∧
      (∀ᶠ n in atTop,
        StrictMono (fun k => tStar k n) ∧
        (∀ k : Fin CD.K, 0 < tStar k n) ∧
        (∀ k : Fin CD.K, CD.z k = H.tm →
          tStar k n = constrainedThreshold prob (c n) (hbPrescribedSet s n)) ∧
        (∀ (k : Fin CD.K) (hmem : CD.z k ∈ H.S ∧ CD.z k ≠ H.tm),
          tStar k n = s ⟨CD.z k, hmem⟩ n)) ∧
      (∀ᶠ n in atTop, ∀ gs : ℝ → ℝ,
        IsWeakExtremal prob (c n) (hbPrescribedSet s n)
          (constrainedThreshold prob (c n) (hbPrescribedSet s n)) gs →
        ∀ k : Fin CD.K, gs (tStar k n) = 0 ∧
          analyticOrderNatAt (psiTilde prob (c n) gs) (chartUT (c n) (tStar k n) : ℂ) =
            if CD.z k ∈ H.S then 1 else 2) ∧
      (∀ a' b' : ℝ, CD.a < a' → a' < CD.z ⟨CD.K - 1, Nat.sub_lt CD.hK zero_lt_one⟩ →
        CD.z ⟨0, CD.hK⟩ < b' → b' < CD.b →
        ∀ᶠ n in atTop, ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (hbPrescribedSet s n ∪
            Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 →
          (∀ k : Fin CD.K, 0 < meas.ν {tStar k n}) ∧
          meas.ν ({t ∈ Ioi (0 : ℝ) | uAiry (c n) t ∈ Icc a' b'} \
            Set.range (fun k => tStar k n)) = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (hbPrescribedSet s n ∪
            Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 →
          ∀ k : Fin CD.K,
            |spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal - CD.ω k| ≤ ε) ∧
      (let amp : ℝ := 2 * Real.sqrt xiStar * (2 * xiStar) ^ (prob.w - 1) *
        prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) / (Real.sqrt 3 * betaTip)
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (hbPrescribedSet s n ∪
            Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 →
          ∀ k : Fin CD.K,
            let bk := tStar k n - xiBar * c n + cStar * CD.z k * (c n) ^ ((1 : ℝ) / 3)
            |(meas.ν {tStar k n}).toReal / (amp * CD.ω k * (c n) ^ (-(1 / 6 : ℝ)) *
              Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
                (2 * Real.pi * CD.z k / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
                (Real.pi / xiStar) * bk)) - 1| ≤ ε) := by
  classical
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let F : ℕ → Set ℝ := hbPrescribedSet s
  obtain ⟨gs0, ν0, hgs0, hν0⟩ := hb_canonical_primal prob H hc hs_pos
  obtain ⟨r0, hr0_pos, hr0_win, hr0_sep, hr0_tm⟩ := exists_window_radius CD
  have hz_r : ∀ r : ℝ, 0 < r → r ≤ r0 → ∀ᶠ n in atTop, ∀ k : Fin CD.K, ∃! u : ℝ,
      u ∈ ball (CD.z k) r ∧
      psiTilde prob (c n) (gs0 n) (u : ℂ) = 0 ∧
      gs0 n (virasoroDeltaChart (c n) u) = 0 ∧
      0 < virasoroDeltaChart (c n) u ∧
      chartUT (c n) (virasoroDeltaChart (c n) u) = u ∧
      (CD.z k = H.tm → virasoroDeltaChart (c n) u = B n) ∧
      (∀ hmem : CD.z k ∈ H.S ∧ CD.z k ≠ H.tm, virasoroDeltaChart (c n) u = s ⟨CD.z k, hmem⟩ n) ∧
      analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u : ℂ) =
        if CD.z k ∈ H.S then 1 else 2 :=
    fun r hr_pos hr_le =>
      zero_in_disc_for_canonical prob H CD hc hs_pos hs_tend hB_tend hvag hgs0 hν0
        hr0_pos hr0_win hr0_sep hr0_tm hr_pos hr_le
  have hz0 := hz_r r0 hr0_pos le_rfl
  let Q_node := fun (n : ℕ) (k : Fin CD.K) (u : ℝ) =>
    u ∈ ball (CD.z k) r0 ∧
    psiTilde prob (c n) (gs0 n) (u : ℂ) = 0 ∧
    gs0 n (virasoroDeltaChart (c n) u) = 0 ∧
    0 < virasoroDeltaChart (c n) u ∧
    chartUT (c n) (virasoroDeltaChart (c n) u) = u ∧
    (CD.z k = H.tm → virasoroDeltaChart (c n) u = B n) ∧
    (∀ hmem : CD.z k ∈ H.S ∧ CD.z k ≠ H.tm, virasoroDeltaChart (c n) u = s ⟨CD.z k, hmem⟩ n) ∧
    analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (u : ℂ) =
      if CD.z k ∈ H.S then 1 else 2
  let uStar : Fin CD.K → ℕ → ℝ := fun k n =>
    if h : ∃ u : ℝ, Q_node n k u then h.choose else CD.z k
  let tStar : Fin CD.K → ℕ → ℝ := fun k n => virasoroDeltaChart (c n) (uStar k n)
  have huStar_spec : ∀ᶠ n in atTop, ∀ k : Fin CD.K, Q_node n k (uStar k n) ∧
      ∀ u : ℝ, Q_node n k u → u = uStar k n := by
    filter_upwards [hz0] with n hn k
    obtain ⟨u, hu_prop, hu_uniq⟩ := hn k
    have hex : ∃ u : ℝ, Q_node n k u := ⟨u, hu_prop⟩
    have hEq : uStar k n = u := hu_uniq _ (by
      dsimp [uStar]; rw [dite_eq_left hex]; exact hex.choose_spec)
    rw [hEq]
    exact ⟨hu_prop, hu_uniq⟩
  have huStar_conv : ∀ k : Fin CD.K, Tendsto (fun n => uStar k n) atTop (𝓝 (CD.z k)) := by
    intro k
    rw [Metric.tendsto_nhds]
    intro ε hε
    let r := min (ε / 2) r0
    have hr_pos : 0 < r := lt_min (half_pos hε) hr0_pos
    filter_upwards [huStar_spec, hz_r r hr_pos (min_le_right _ _)] with n hsp hrn
    obtain ⟨u_r, hr_prop, -⟩ := hrn k
    have hu_eq : u_r = uStar k n := (hsp k).2 u_r
      ⟨Metric.ball_subset_ball (min_le_right _ _) hr_prop.1, hr_prop.2⟩
    have hdist : dist u_r (CD.z k) < r := hr_prop.1
    rw [hu_eq] at hdist
    exact hdist.trans_le ((min_le_left _ _).trans (by linarith))
  have htStar_uAiry : ∀ k : Fin CD.K, Tendsto (fun n => uAiry (c n) (tStar k n)) atTop (𝓝 (CD.z k)) := by
    intro k
    let M_k : ℝ := |CD.z k| + 1
    obtain ⟨C_k, c_k, _, _, hCk⟩ := uAiry_virasoroDeltaChart_err (show 0 ≤ M_k by positivity)
    have hev : ∀ᶠ n in atTop, |uAiry (c n) (tStar k n) - uStar k n| ≤ C_k * (c n) ^ (-(2 / 3 : ℝ)) := by
      filter_upwards [hc.eventually_ge_atTop c_k,
        (huStar_conv k).eventually (Metric.ball_mem_nhds (CD.z k) zero_lt_one)] with n hcn hb
      rw [Real.dist_eq, abs_lt] at hb
      have huM : |uStar k n| ≤ M_k := by
        dsimp [M_k]; rw [abs_le]; constructor <;> linarith [neg_abs_le (CD.z k), le_abs_self (CD.z k)]
      exact hCk hcn huM
    have h0 : Tendsto (fun n => C_k * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_k
    have hsub : Tendsto (fun n => uAiry (c n) (tStar k n) - uStar k n) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using h0.neg) h0
        (hev.mono fun _ h => by linarith [(abs_le.mp h).1])
        (hev.mono fun _ h => by linarith [(abs_le.mp h).2])
    simpa using (huStar_conv k).add hsub
  have htStar_chart : ∀ k : Fin CD.K, Tendsto (fun n => chartUT (c n) (tStar k n)) atTop (𝓝 (CD.z k)) := by
    intro k
    refine (huStar_conv k).congr' ?_
    filter_upwards [huStar_spec] with n hsp
    exact ((hsp k).1.2.2.2.2.1).symm
  -- Step 1: monotonicity, positivity, and identity on `H.S`.
  have hpart2_ev : ∀ᶠ n in atTop,
      StrictMono (fun k => tStar k n) ∧
      (∀ k : Fin CD.K, 0 < tStar k n) ∧
      (∀ k : Fin CD.K, CD.z k = H.tm → tStar k n = B n) ∧
      (∀ (k : Fin CD.K) (hmem : CD.z k ∈ H.S ∧ CD.z k ≠ H.tm), tStar k n = s ⟨CD.z k, hmem⟩ n) := by
    let M_ab : ℝ := max |CD.a| |CD.b| + 2 * r0 + 2
    filter_upwards [huStar_spec, hc.eventually_gt_atTop 0,
      virasoroAC_sq_eventually_ge hc M_ab] with n hsp hcpos hVac
    refine ⟨fun i j hij => ?_, fun k => (hsp k).1.2.2.2.1,
      fun k htm => (hsp k).1.2.2.2.2.2.1 htm, fun k hmem => (hsp k).1.2.2.2.2.2.2.1 hmem⟩
    have hzi_gt : CD.z j < CD.z i := CD.hz_anti hij
    have hi_ball : |uStar i n - CD.z i| < r0 := by
      simpa [Metric.mem_ball, Real.dist_eq] using (hsp i).1.1
    have hj_ball : |uStar j n - CD.z j| < r0 := by
      simpa [Metric.mem_ball, Real.dist_eq] using (hsp j).1.1
    have h4r : 4 * r0 ≤ |CD.z i - CD.z j| := hr0_sep i j hij.ne
    rw [abs_of_pos (sub_pos.mpr hzi_gt)] at h4r
    have hu_lt : uStar j n < uStar i n := by
      linarith [(abs_lt.mp hi_ball).1, (abs_lt.mp hj_ball).2]
    have h_in_Mab : ∀ k : Fin CD.K, |uStar k n| ≤ virasoroAC (c n) ^ 2 := fun k => by
      have hzk_in : CD.z k ∈ Icc CD.a CD.b :=
        ⟨by linarith [(hr0_win k).1], by linarith [(hr0_win k).2]⟩
      have hzk_abs : |CD.z k| ≤ max |CD.a| |CD.b| :=
        abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hzk_in.1],
          by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hzk_in.2]⟩
      have hk_b := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using (hsp k).1.1 : |uStar k n - CD.z k| < r0)
      have hle : |uStar k n| ≤ M_ab := by
        rw [abs_le]; dsimp [M_ab]; constructor <;> linarith [neg_abs_le (CD.z k), le_abs_self (CD.z k)]
      exact hle.trans hVac
    exact (virasoroDeltaChart_strictAnti hcpos).lt_iff_gt
      (abs_le.mp (h_in_Mab i)) (abs_le.mp (h_in_Mab j)) |>.mpr hu_lt
  -- Step 2: window support characterization for every attaining measure (part 4b).
  have hpart4b_ev : ∀ a' b' : ℝ, CD.a < a' → a' < CD.z ⟨CD.K - 1, Nat.sub_lt CD.hK zero_lt_one⟩ →
      CD.z ⟨0, CD.hK⟩ < b' → b' < CD.b →
      ∀ᶠ n in atTop, ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (F n ∪ Ici (B n))ᶜ = 0 →
        meas.ν ({t ∈ Ioi (0 : ℝ) | uAiry (c n) t ∈ Icc a' b'} \ Set.range (fun k => tStar k n)) = 0 := by
    intro a' b' ha' _ _ hb'
    let M_win : ℝ := max |a'| |b'| + 1
    obtain ⟨C_w, c_w, _, _, hCw⟩ := chartUT_sub_uAiry_err (show 0 ≤ M_win by positivity)
    let δ_w : ℝ := min (a' - CD.a) (CD.b - b')
    have hδw_pos : 0 < δ_w := lt_min (by linarith) (by linarith)
    have hCw_err : ∀ᶠ n in atTop, C_w * (c n) ^ (-(2 / 3 : ℝ)) < δ_w / 2 := by
      have h0 : Tendsto (fun n => C_w * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_w
      exact h0.eventually (gt_mem_nhds (by positivity))
    have hgs0_we : ∀ᶠ n in atTop, IsWeakExtremal prob (c n) (F n) (B n) (gs0 n) :=
      hgs0.mono fun _ h => h.1
    have hHur0 := hurwitz_window_isolation prob H CD hc hs_pos hs_tend hB_tend hgs0_we hr0_pos hr0_win hr0_sep
    let M_ab : ℝ := max |CD.a| |CD.b| + 2 * r0 + 2
    let R_m : ℝ := ↑(Nat.ceil (max |CD.a| |CD.b| + 2 * r0 + 2)) + 1
    let R' : ℝ := r0 + r0 / 2
    have hrR' : r0 < R' := by dsimp [R']; linarith
    have hball_sub : ∀ k : Fin CD.K, ball (CD.z k : ℂ) R' ⊆ ball (0 : ℂ) R_m := fun k w hw => by
      rw [mem_ball, dist_eq_norm] at hw
      rw [mem_ball_zero_iff]
      have hzk_in : CD.z k ∈ Icc CD.a CD.b := ⟨by linarith [(hr0_win k).1], by linarith [(hr0_win k).2]⟩
      have hzk_abs : ‖(CD.z k : ℂ)‖ ≤ max |CD.a| |CD.b| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hzk_in.1],
          by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hzk_in.2]⟩
      have := Nat.le_ceil (max |CD.a| |CD.b| + 2 * r0 + 2)
      calc ‖w‖ ≤ ‖w - (CD.z k : ℂ)‖ + ‖(CD.z k : ℂ)‖ := norm_le_norm_sub_add w (CD.z k : ℂ)
        _ < R' + max |CD.a| |CD.b| := by linarith
        _ ≤ R_m := by dsimp [R', R_m]; linarith
    filter_upwards [hgs0, huStar_spec, hHur0,
      hc.eventually_ge_atTop (max c_w (max 1 (12 * prob.totalShift))),
      virasoroAC_sq_eventually_ge hc M_ab, hCw_err]
      with n ⟨hwe0, _, hall_meas⟩ hsp ⟨hDiff, hOff, hDisc⟩ hcw_ge hVac hCerr meas hν
    have hcw : c_w ≤ c n := (le_max_left _ _).trans hcw_ge
    have hc_pos : 0 < c n := lt_of_lt_of_le zero_lt_one
      ((le_max_left 1 _).trans ((le_max_right _ _).trans hcw_ge))
    have hsh12 : prob.totalShift ≤ c n / 12 := by
      have := (le_max_right 1 _).trans ((le_max_right _ _).trans hcw_ge); linarith
    have hae := (hall_meas meas hν).2.2
    refine measure_mono_null (fun t ht => ?_) (ae_iff.1 hae)
    rintro ⟨-, hgst⟩
    have ht_pos : 0 < t := ht.1.1
    have hu_in : uAiry (c n) t ∈ Icc a' b' := ht.1.2
    have huM : |uAiry (c n) t| ≤ M_win := by
      rw [abs_le]; dsimp [M_win]
      exact ⟨by linarith [neg_abs_le a', le_max_left |a'| |b'|, hu_in.1],
        by linarith [le_abs_self b', le_max_right |a'| |b'|, hu_in.2]⟩
    obtain ⟨_, hΔt, herr⟩ := hCw hcw ht_pos huM
    let u := chartUT (c n) t
    have hu_ab : u ∈ Icc CD.a CD.b := by
      have h1 := abs_lt.mp (herr.trans_lt hCerr)
      have hdl := min_le_left (a' - CD.a) (CD.b - b')
      have hdr := min_le_right (a' - CD.a) (CD.b - b')
      exact ⟨by linarith [hu_in.1], by linarith [hu_in.2]⟩
    have hu_vac : |u| ≤ virasoroAC (c n) ^ 2 := by
      have h1 : |u| ≤ M_ab := by
        rw [abs_le]; dsimp [M_ab]
        exact ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hu_ab.1],
          by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hu_ab.2]⟩
      exact h1.trans hVac
    have hM0 : 0 < prob.cardyNorm (c n / 12) (gs0 n) := by rw [hwe0.2.1]; exact zero_lt_one
    have hpsi_u : psiTilde prob (c n) (gs0 n) (u : ℂ) = 0 :=
      (psiTilde_eq_zero_iff prob hc_pos hsh12 hwe0.1 hM0 hu_vac).2 (by rw [hΔt, hgst])
    have hex_k : ∃ k : Fin CD.K, (u : ℂ) ∈ ball (CD.z k : ℂ) r0 := by
      by_contra hnot; push Not at hnot
      exact hOff u hu_ab hnot hpsi_u
    obtain ⟨k, hk_ball⟩ := hex_k
    have hu_c : (u : ℂ) ∈ ball (CD.z k : ℂ) r0 := hk_ball
    have hu0_c : (uStar k n : ℂ) ∈ ball (CD.z k : ℂ) r0 := by
      rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
      simpa [Metric.mem_ball, Real.dist_eq] using (hsp k).1.1
    have hDiff_k : DifferentiableOn ℂ (psiTilde prob (c n) (gs0 n)) (ball (CD.z k : ℂ) R') :=
      hDiff.mono (hball_sub k)
    have hu_eq : u = uStar k n := by
      apply Complex.ofReal_injective
      by_cases hkS : CD.z k ∈ H.S
      · exact eq_of_zeroCount_eq_one hDiff_k hr0_pos hrR' (hDisc k).1
          (by simpa [hkS] using (hDisc k).2) hu_c hu0_c hpsi_u (hsp k).1.2.1
      · have hord2 : 2 ≤ analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (uStar k n : ℂ) := by
          rw [(hsp k).1.2.2.2.2.2.2.2]; simp [hkS]
        exact (unique_double_zero_of_zeroCount_two hr0_pos hrR' hDiff_k (hDisc k).1
          (by simpa [hkS] using (hDisc k).2) hu0_c hord2).2 (u : ℂ) hu_c hpsi_u
    exact ht.2 ⟨k, by dsimp [tStar]; rw [← hu_eq, hΔt]⟩
  -- Step 3: uniform normalised weight convergence (part 5) and positivity of atoms (part 4a).
  have hpart5_ev : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (F n ∪ Ici (B n))ᶜ = 0 →
        ∀ k : Fin CD.K,
          |spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal - CD.ω k| ≤ ε := by
    intro ε hε
    suffices hk_all : ∀ k : Fin CD.K, ∀ᶠ n in atTop,
        ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (F n ∪ Ici (B n))ᶜ = 0 →
          |spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal - CD.ω k| ≤ ε by
      filter_upwards [eventually_all.2 hk_all] with n hn meas hν k
      exact hn k meas hν
    intro k
    choose bump hbump_cont hbump_cs _ hbump_one hbump_zero hbump_tsupp using
      fun _ : Unit => exists_bump_near (x₀ := CD.z k) (r := r0 / 2) (by positivity)
    let φ := bump ()
    have htsub : tsupport φ ⊆ Ioo CD.a CD.b := fun u hu => by
      have h1 := hbump_tsupp () hu
      exact ⟨by linarith [h1.1, (hr0_win k).1], by linarith [h1.2, (hr0_win k).2]⟩
    have hK1 : CD.K - 1 < CD.K := Nat.sub_lt CD.hK zero_lt_one
    let a' : ℝ := (CD.a + CD.z ⟨CD.K - 1, hK1⟩) / 2
    let b' : ℝ := (CD.z ⟨0, CD.hK⟩ + CD.b) / 2
    have ha'_lt : CD.a < a' := by have := CD.ha; dsimp [a']; linarith
    have ha'_z : a' < CD.z ⟨CD.K - 1, hK1⟩ := by have := CD.ha; dsimp [a']; linarith
    have hb'_z : CD.z ⟨0, CD.hK⟩ < b' := by have := CD.hb; dsimp [b']; linarith
    have hb'_lt : b' < CD.b := by have := CD.hb; dsimp [b']; linarith
    have h_supp := hpart4b_ev a' b' ha'_lt ha'_z hb'_z hb'_lt
    have h_int_eq : ∀ᶠ n in atTop,
        ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (F n ∪ Ici (B n))ᶜ = 0 →
          ∫ u, φ u ∂(spectralMeasure prob (c n) meas.ν) =
            spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal := by
      filter_upwards [h_supp, hpart2_ev, hc.eventually_ge_atTop (max 1 (12 * prob.totalShift)),
        eventually_all.2 fun j =>
          (htStar_uAiry j).eventually (Metric.ball_mem_nhds (CD.z j) (show 0 < r0 / 4 by positivity))]
        with n hsn ⟨_, ht_pos, _, _⟩ hc_ge ht_ball meas hν
      have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc_ge)
      have hsh12 : prob.totalShift ≤ c n / 12 := by have := (le_max_right 1 _).trans hc_ge; linarith
      rw [integral_spectralMeasure prob hcpos hsh12 meas.ν (hbump_cont ())]
      have hnull_sing : meas.ν ((Ioi (0 : ℝ) ∩ {t | spectralWeight prob (c n) t * φ (uAiry (c n) t) ≠ 0}) \
          {tStar k n}) = 0 := by
        refine measure_mono_null (fun t ht => ?_) (hsn meas hν)
        have ht0 : t ∈ Ioi (0 : ℝ) := ht.1.1
        have hne0 : φ (uAiry (c n) t) ≠ 0 := right_ne_zero_of_mul ht.1.2
        have hu_Ioo : uAiry (c n) t ∈ Ioo (CD.z k - r0 / 2) (CD.z k + r0 / 2) := by
          by_contra hn; exact hne0 (hbump_zero () _ hn)
        have hu_Icc : uAiry (c n) t ∈ Icc a' b' := by
          have hk_lo : CD.z ⟨CD.K - 1, hK1⟩ ≤ CD.z k := by
            rcases eq_or_lt_of_le (show (k : ℕ) ≤ CD.K - 1 by omega) with h | h
            · exact (congrArg CD.z (Fin.ext h.symm)).le
            · exact (CD.hz_anti h).le
          have hk_hi : CD.z k ≤ CD.z ⟨0, CD.hK⟩ := by
            rcases eq_or_lt_of_le (Nat.zero_le (k : ℕ)) with h | h
            · exact (congrArg CD.z (Fin.ext h.symm)).le
            · exact (CD.hz_anti h).le
          dsimp [a', b'] at hk_lo hk_hi ⊢
          exact ⟨by linarith [(hr0_win ⟨CD.K - 1, hK1⟩).1, hu_Ioo.1],
            by linarith [(hr0_win ⟨0, CD.hK⟩).2, hu_Ioo.2]⟩
        refine ⟨⟨ht0, hu_Icc⟩, fun hrg => ?_⟩
        obtain ⟨j, rfl⟩ := hrg
        have hj_eq : j = k := by
          by_contra hjk
          have hsep := hr0_sep j k hjk
          have hj_u : |uAiry (c n) (tStar j n) - CD.z j| < r0 / 4 := by
            simpa [Metric.mem_ball, Real.dist_eq] using ht_ball j
          have htri : |CD.z j - CD.z k| ≤
              |uAiry (c n) (tStar j n) - CD.z j| + |uAiry (c n) (tStar j n) - CD.z k| := by
            have e : CD.z j - CD.z k =
                -(uAiry (c n) (tStar j n) - CD.z j) + (uAiry (c n) (tStar j n) - CD.z k) := by ring
            rw [e]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
          have hkj : |uAiry (c n) (tStar j n) - CD.z k| < r0 / 2 :=
            abs_lt.mpr ⟨by linarith [hu_Ioo.1], by linarith [hu_Ioo.2]⟩
          linarith
        exact ht.2 (congrArg (fun x => tStar x n) hj_eq)
      rw [setIntegral_Ioi_of_singleton (ht_pos k) _ hnull_sing]
      have hφ1 : φ (uAiry (c n) (tStar k n)) = 1 := by
        have hk_b : |uAiry (c n) (tStar k n) - CD.z k| < r0 / 4 := by
          simpa [Metric.mem_ball, Real.dist_eq] using ht_ball k
        have := abs_lt.mp hk_b
        exact hbump_one () _ ⟨by linarith, by linarith⟩
      rw [hφ1, mul_one]; ring
    have hsum_lim : ∑ j : Fin CD.K, CD.ω j * φ (CD.z j) = CD.ω k := by
      rw [Finset.sum_eq_single k]
      · have h1 : φ (CD.z k) = 1 := hbump_one () (CD.z k) ⟨by linarith, by linarith⟩
        rw [h1, mul_one]
      · intro j _ hjk
        have hsep := hr0_sep j k hjk
        have hj_not : CD.z j ∉ Ioo (CD.z k - r0 / 2) (CD.z k + r0 / 2) := by
          rintro ⟨h1, h2⟩
          have : |CD.z j - CD.z k| < r0 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
          linarith
        dsimp [φ]
        rw [hbump_zero () (CD.z j) hj_not, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    by_contra hnot
    rw [not_eventually] at hnot
    let Bad := fun (n : ℕ) (m : AdmissibleCrossingMeasure prob (c n / 12)) =>
      m.ν (F n ∪ Ici (B n))ᶜ = 0 ∧
      ε < |spectralWeight prob (c n) (tStar k n) * (m.ν {tStar k n}).toReal - CD.ω k|
    have hfreq : ∃ᶠ n in atTop, ∃ m, Bad n m := by
      refine hnot.mono fun n hn => ?_
      push Not at hn
      exact hn
    let ν_bad : ℕ → Measure ℝ := fun n =>
      if h : ∃ m, Bad n m then h.choose.ν else ν0 n
    have hν_bad_mem : ∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_bad n = meas.ν ∧ meas.ν (F n ∪ Ici (B n))ᶜ = 0 := by
      filter_upwards [hν0] with n ⟨meas0, hν0_eq, hν0_supp⟩
      dsimp [ν_bad]
      split_ifs with h
      · exact ⟨h.choose, rfl, h.choose_spec.1⟩
      · exact ⟨meas0, hν0_eq, hν0_supp⟩
    have hvag_bad := hvag ν_bad hν_bad_mem φ (hbump_cont ()) (hbump_cs ()) htsub
    rw [hsum_lim] at hvag_bad
    have hball_bad : ∀ᶠ n in atTop,
        |∫ u, φ u ∂(spectralMeasure prob (c n) (ν_bad n)) - CD.ω k| < ε := by
      have := hvag_bad.eventually (Metric.ball_mem_nhds (CD.ω k) hε)
      filter_upwards [this] with n hn
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    have hcontra : ∀ᶠ n in atTop, ¬ ∃ m, Bad n m := by
      filter_upwards [h_int_eq, hball_bad] with n hint hball ⟨m, hm1, hm2⟩
      have hex : ∃ m', Bad n m' := ⟨m, hm1, hm2⟩
      have hspec := Classical.choose_spec hex
      have hν_eq : ν_bad n = hex.choose.ν := dite_eq_left hex
      have hint_m := hint hex.choose hspec.1
      rw [hν_eq, hint_m] at hball
      exact absurd hball (not_lt_of_ge hspec.2.le)
    exact hfreq hcontra
  -- Step 4: positive atoms and full `part4` + `dsl:hb-raw` (`part6`).
  have hpart4a_ev : ∀ᶠ n in atTop, ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
      meas.ν (F n ∪ Ici (B n))ᶜ = 0 → ∀ k : Fin CD.K, 0 < meas.ν {tStar k n} := by
    have hall : ∀ᶠ n in atTop, ∀ k : Fin CD.K,
        ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (F n ∪ Ici (B n))ᶜ = 0 → 0 < meas.ν {tStar k n} := by
      rw [eventually_all]
      intro k
      have hω2 : 0 < CD.ω k / 2 := half_pos (CD.hω_pos k)
      filter_upwards [hpart5_ev (CD.ω k / 2) hω2, hpart2_ev,
        hc.eventually_ge_atTop (max 1 (12 * prob.totalShift))]
        with n hn ⟨_, ht_pos, _, _⟩ hc_ge meas hν
      have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc_ge)
      have hsh12 : prob.totalShift ≤ c n / 12 := by have := (le_max_right 1 _).trans hc_ge; linarith
      have hle := hn meas hν k
      have hmul_pos : 0 < spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal := by
        linarith [(abs_le.mp hle).1]
      have hsw_pos : 0 < spectralWeight prob (c n) (tStar k n) :=
        spectralWeight_pos hcpos hsh12 (ht_pos k)
      have htoReal_pos : 0 < (meas.ν {tStar k n}).toReal :=
        pos_of_mul_pos_right hmul_pos hsw_pos.le
      exact pos_iff_ne_zero.mpr (fun h0 => by rw [h0, ENNReal.toReal_zero] at htoReal_pos; exact htoReal_pos.false)
    filter_upwards [hall] with n hn meas hν k
    exact hn k meas hν
  have hpart6_ev : let amp : ℝ := 2 * Real.sqrt xiStar * (2 * xiStar) ^ (prob.w - 1) *
      prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) / (Real.sqrt 3 * betaTip)
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (F n ∪ Ici (B n))ᶜ = 0 →
        ∀ k : Fin CD.K,
          let bk := tStar k n - xiBar * c n + cStar * CD.z k * (c n) ^ ((1 : ℝ) / 3)
          |(meas.ν {tStar k n}).toReal / (amp * CD.ω k * (c n) ^ (-(1 / 6 : ℝ)) *
            Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
              (2 * Real.pi * CD.z k / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
              (Real.pi / xiStar) * bk)) - 1| ≤ ε := by
    intro amp ε hε
    suffices hk_all : ∀ k : Fin CD.K, ∀ᶠ n in atTop,
        ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (F n ∪ Ici (B n))ᶜ = 0 →
          let bk := tStar k n - xiBar * c n + cStar * CD.z k * (c n) ^ ((1 : ℝ) / 3)
          |(meas.ν {tStar k n}).toReal / (amp * CD.ω k * (c n) ^ (-(1 / 6 : ℝ)) *
            Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
              (2 * Real.pi * CD.z k / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
              (Real.pi / xiStar) * bk)) - 1| ≤ ε by
      filter_upwards [eventually_all.2 hk_all] with n hn meas hν k
      exact hn k meas hν
    intro k
    have hcardy := cardyV_mul_jAiry_asymp prob hc (htStar_uAiry k)
    have hω_pos := CD.hω_pos k
    have hε1 : 0 < min (ε / 4) 1 * CD.ω k := mul_pos (lt_min (by positivity) zero_lt_one) hω_pos
    filter_upwards [hpart5_ev _ hε1, hpart2_ev, hc.eventually_ge_atTop (max 1 (12 * prob.totalShift)),
      hc.eventually_gt_atTop 0,
      hcardy.eventually (Metric.ball_mem_nhds 1 (show 0 < min (ε / 2) 1 by positivity))]
      with n h5 ⟨_, ht_pos, _, _⟩ hc_ge hcpos hcq meas hν
    have hsh12 : prob.totalShift ≤ c n / 12 := by have := (le_max_right 1 _).trans hc_ge; linarith
    have hswJ := weight_eq_jAiry_mul hcpos hsh12 (ht_pos k)
    have hV_pos : 0 < prob.cardyV (c n / 12) (tStar k n) := prob.cardyV_pos hsh12 (ht_pos k)
    have hJ_pos : 0 < jAiry (c n) (tStar k n) := jAiry_pos hcpos (ht_pos k)
    have hswVJ : spectralWeight prob (c n) (tStar k n) *
        (2 * Real.pi * prob.cardyV (c n / 12) (tStar k n) * jAiry (c n) (tStar k n)) = 1 := by
      have h1 : jAiry (c n) (tStar k n) * spectralWeight prob (c n) (tStar k n) *
          (2 * Real.pi * prob.cardyV (c n / 12) (tStar k n)) = 1 := by
        rw [← hswJ]; field_simp [Real.pi_ne_zero, hV_pos.ne']
      linarith
    let bk := tStar k n - xiBar * c n + cStar * CD.z k * (c n) ^ ((1 : ℝ) / 3)
    let R := (c n) ^ (-(1 / 6 : ℝ)) * Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
      (2 * Real.pi * CD.z k / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) + (Real.pi / xiStar) * bk)
    let p := spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal / CD.ω k
    let q := (2 * Real.pi * prob.cardyV (c n / 12) (tStar k n) * jAiry (c n) (tStar k n)) / (amp * R)
    have hp_err : |p - 1| ≤ min (ε / 4) 1 := by
      have h5k := h5 meas hν k
      have heq : p - 1 =
          (spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal - CD.ω k) / CD.ω k := by
        dsimp [p]; field_simp [hω_pos.ne']
      rw [heq, abs_div, abs_of_pos hω_pos, div_le_iff₀ hω_pos]
      exact h5k
    have hq_err : |q - 1| ≤ min (ε / 2) 1 := by
      simpa [q, R, bk, amp, mul_assoc, Metric.mem_ball, Real.dist_eq] using hcq.le
    have hq_abs : |q| ≤ 2 := by
      have := (abs_le.mp (hq_err.trans (min_le_right _ _)))
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hrat_eq : (meas.ν {tStar k n}).toReal / (amp * CD.ω k * R) = p * q := by
      dsimp [p, q]
      calc (meas.ν {tStar k n}).toReal / (amp * CD.ω k * R)
          = (meas.ν {tStar k n}).toReal * 1 / (amp * CD.ω k * R) := by ring
        _ = (meas.ν {tStar k n}).toReal * (spectralWeight prob (c n) (tStar k n) *
              (2 * Real.pi * prob.cardyV (c n / 12) (tStar k n) * jAiry (c n) (tStar k n))) /
              (amp * CD.ω k * R) := by rw [hswVJ]
        _ = (spectralWeight prob (c n) (tStar k n) * (meas.ν {tStar k n}).toReal / CD.ω k) *
              ((2 * Real.pi * prob.cardyV (c n / 12) (tStar k n) * jAiry (c n) (tStar k n)) /
                (amp * R)) := by ring
    dsimp [bk, amp, R] at hrat_eq ⊢
    simp only [← mul_assoc] at hrat_eq ⊢
    rw [hrat_eq]
    have htri : |p * q - 1| ≤ |p - 1| * |q| + |q - 1| := by
      have e : p * q - 1 = (p - 1) * q + (q - 1) := by ring
      rw [e]; exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
    calc |p * q - 1| ≤ |p - 1| * |q| + |q - 1| := htri
      _ ≤ (ε / 4) * 2 + (ε / 2) := by
          gcongr
          · exact hp_err.trans (min_le_left _ _)
          · exact hq_err.trans (min_le_left _ _)
      _ = ε := by ring
  -- Step 5: uniform vanishing and simple/double multiplicity for every weak extremal.
  have hpart3_ev : ∀ᶠ n in atTop, ∀ gs : ℝ → ℝ,
      IsWeakExtremal prob (c n) (F n) (B n) gs →
      ∀ k : Fin CD.K, gs (tStar k n) = 0 ∧
        analyticOrderNatAt (psiTilde prob (c n) gs) (chartUT (c n) (tStar k n) : ℂ) =
          if CD.z k ∈ H.S then 1 else 2 := by
    have hzero_all : ∀ᶠ n in atTop, ∀ gs : ℝ → ℝ,
        IsWeakExtremal prob (c n) (F n) (B n) gs →
        ∀ k : Fin CD.K, gs (tStar k n) = 0 := by
      filter_upwards [hν0, hpart4a_ev, hc.eventually_ge_atTop (max 1 (12 * prob.totalShift))]
        with n ⟨meas0, _, hν0_supp⟩ hpos hc_ge gs hwe k
      have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc_ge)
      have ha0 : 0 < c n / 12 := by positivity
      have hsh12 : prob.totalShift ≤ c n / 12 := by have := (le_max_right 1 _).trans hc_ge; linarith
      have hae := crossing_ae_zero hwe.1 hwe.2.2.1 hsh12 ha0
        (fun t ht => hwe.2.2.2 t (Or.inr ht)) meas0 hν0_supp hwe.2.2.2
      exact (prop_of_pos_singleton hae (hpos meas0 hν0_supp k)).2
    have hord_all : ∀ᶠ n in atTop, ∀ gs : ℝ → ℝ,
        IsWeakExtremal prob (c n) (F n) (B n) gs →
        ∀ k : Fin CD.K,
          analyticOrderNatAt (psiTilde prob (c n) gs) (chartUT (c n) (tStar k n) : ℂ) =
            if CD.z k ∈ H.S then 1 else 2 := by
      by_contra hnot
      rw [not_eventually] at hnot
      let Bad := fun (n : ℕ) (gs : ℝ → ℝ) =>
        IsWeakExtremal prob (c n) (F n) (B n) gs ∧
        ∃ k : Fin CD.K,
          analyticOrderNatAt (psiTilde prob (c n) gs) (chartUT (c n) (tStar k n) : ℂ) ≠
            if CD.z k ∈ H.S then 1 else 2
      have hfreq : ∃ᶠ n in atTop, ∃ gs, Bad n gs := by
        refine hnot.mono fun n hn => ?_
        push Not at hn
        exact hn
      let gs_bad : ℕ → ℝ → ℝ := fun n =>
        if h : ∃ gs, Bad n gs then h.choose else gs0 n
      have hgs_bad_we : ∀ᶠ n in atTop, IsWeakExtremal prob (c n) (F n) (B n) (gs_bad n) := by
        filter_upwards [hgs0] with n ⟨hwe0, _⟩
        dsimp [gs_bad]; split_ifs with h
        · exact h.choose_spec.1
        · exact hwe0
      have hHur := hurwitz_window_isolation prob H CD hc hs_pos hs_tend hB_tend hgs_bad_we
        hr0_pos hr0_win hr0_sep
      let M_ab : ℝ := max |CD.a| |CD.b| + 2 * r0 + 2
      let M_win : ℝ := max |CD.a| |CD.b| + 2 * r0 + 1
      let R' : ℝ := r0 + r0 / 2
      have hrR' : r0 < R' := by dsimp [R']; linarith
      let R_m : ℝ := ↑(Nat.ceil (max |CD.a| |CD.b| + 2 * r0 + 2)) + 1
      have hball_sub : ∀ k : Fin CD.K, ball (CD.z k : ℂ) R' ⊆ ball (0 : ℂ) R_m := fun k w hw => by
        rw [mem_ball, dist_eq_norm] at hw
        rw [mem_ball_zero_iff]
        have hzk_in : CD.z k ∈ Icc CD.a CD.b := ⟨by linarith [(hr0_win k).1], by linarith [(hr0_win k).2]⟩
        have hzk_abs : ‖(CD.z k : ℂ)‖ ≤ max |CD.a| |CD.b| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hzk_in.1],
            by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hzk_in.2]⟩
        have := Nat.le_ceil (max |CD.a| |CD.b| + 2 * r0 + 2)
        calc ‖w‖ ≤ ‖w - (CD.z k : ℂ)‖ + ‖(CD.z k : ℂ)‖ := norm_le_norm_sub_add w (CD.z k : ℂ)
          _ < R' + max |CD.a| |CD.b| := by linarith
          _ ≤ R_m := by dsimp [R', R_m]; linarith
      obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err (show 0 ≤ M_win by positivity)
      have hC_ut_err : ∀ᶠ n in atTop, C_ut * (c n) ^ (-(2 / 3 : ℝ)) < r0 / 4 := by
        have h0 : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
          simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_ut
        exact h0.eventually (gt_mem_nhds (by positivity))
      have hcontra : ∀ᶠ n in atTop, ¬ ∃ gs, Bad n gs := by
        filter_upwards [huStar_spec, hzero_all, hHur, hB_tend.eventually (Metric.ball_mem_nhds H.tm (show 0 < r0 / 4 by positivity)),
          hC_ut_err, hc.eventually_ge_atTop (max c_ut (max 1 (12 * prob.totalShift))),
          virasoroAC_sq_eventually_ge hc M_ab, eventually_pos_of_uAiry_tendsto hc hB_tend]
          with n hsp hz0 ⟨hDiff, _, hDisc⟩ hBu hCut hc_ge hVac hBn_pos ⟨gs, hgs_we, k0, hbad_k⟩
        have hex : ∃ gs', Bad n gs' := ⟨gs, hgs_we, k0, hbad_k⟩
        have hsp_bad := Classical.choose_spec hex
        let k : Fin CD.K := hsp_bad.2.choose
        have hbad_choose := hsp_bad.2.choose_spec
        have hgs_eq : gs_bad n = hex.choose := dite_eq_left hex
        have hwe_n : IsWeakExtremal prob (c n) (F n) (B n) (gs_bad n) := hgs_eq ▸ hsp_bad.1
        have hcut : c_ut ≤ c n := (le_max_left _ _).trans hc_ge
        have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans ((le_max_right _ _).trans hc_ge))
        have hsh12 : prob.totalShift ≤ c n / 12 := by
          have := (le_max_right 1 _).trans ((le_max_right _ _).trans hc_ge); linarith
        have hM_we : 0 < prob.cardyNorm (c n / 12) (gs_bad n) := by
          rw [hwe_n.2.1]; exact zero_lt_one
        have hu_eq : chartUT (c n) (tStar k n) = uStar k n := (hsp k).1.2.2.2.2.1
        have hu_ball : uStar k n ∈ ball (CD.z k) r0 := (hsp k).1.1
        have h_in_vac : ∀ u ∈ ball (CD.z k) r0, |u| ≤ virasoroAC (c n) ^ 2 := fun u hu => by
          have hzk_in : CD.z k ∈ Icc CD.a CD.b := ⟨by linarith [(hr0_win k).1], by linarith [(hr0_win k).2]⟩
          have hzk_abs : |CD.z k| ≤ max |CD.a| |CD.b| :=
            abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hzk_in.1],
              by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hzk_in.2]⟩
          have hu_d := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hu : |u - CD.z k| < r0)
          have hle : |u| ≤ M_ab := by
            rw [abs_le]; dsimp [M_ab]; constructor <;> linarith [neg_abs_le (CD.z k), le_abs_self (CD.z k)]
          exact hle.trans hVac
        have hu_vac := h_in_vac (uStar k n) hu_ball
        have hgs_t : gs_bad n (tStar k n) = 0 := hz0 (gs_bad n) hwe_n k
        have hΔu : virasoroDeltaChart (c n) (uStar k n) = tStar k n := by
          dsimp [tStar]
        have hpsi0 : psiTilde prob (c n) (gs_bad n) (uStar k n : ℂ) = 0 :=
          (psiTilde_eq_zero_iff prob hcpos hsh12 hwe_n.1 hM_we hu_vac).2 (by rw [hΔu, hgs_t])
        have hDiff_k : DifferentiableOn ℂ (psiTilde prob (c n) (gs_bad n)) (ball (CD.z k : ℂ) R') :=
          hDiff.mono (hball_sub k)
        have hsph_k := (hDisc k).1
        have hzc_k := (hDisc k).2
        have hu_c : (uStar k n : ℂ) ∈ ball (CD.z k : ℂ) r0 := by
          rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
          simpa [Metric.mem_ball, Real.dist_eq] using hu_ball
        obtain ⟨hw_sph, hfw_sph⟩ := exists_nonzero_of_sphere hr0_pos hrR' hsph_k
        have hord_good : analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) (uStar k n : ℂ) =
            if CD.z k ∈ H.S then 1 else 2 := by
          by_cases hkS : CD.z k ∈ H.S
          · have hzc1 : zeroCount (psiTilde prob (c n) (gs_bad n)) (CD.z k : ℂ) r0 = 1 := by
              simpa [hkS] using hzc_k
            have hfin := support_orderNat_finite hDiff_k hw_sph hfw_sph hrR'
            have hsum : zeroCount (psiTilde prob (c n) (gs_bad n)) (CD.z k : ℂ) r0 =
                ∑ z ∈ hfin.toFinset, analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) z := by
              unfold zeroCount
              rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
            have hnz : 0 < analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) (uStar k n : ℂ) :=
              Nat.pos_of_ne_zero ((orderNat_ne_zero_iff hDiff_k hw_sph hfw_sph
                (ball_subset_ball hrR'.le hu_c)).mpr hpsi0)
            have hle1 : analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) (uStar k n : ℂ) ≤ 1 := by
              rw [← hzc1, hsum]
              exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr ⟨hu_c, hnz.ne'⟩)
            have h1 : analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) (uStar k n : ℂ) = 1 := by omega
            simpa [hkS] using h1
          · have hzc2 : zeroCount (psiTilde prob (c n) (gs_bad n)) (CD.z k : ℂ) r0 = 2 := by
              simpa [hkS] using hzc_k
            have hzk_lt_tm : CD.z k < H.tm := by
              have hnot_le : ¬ H.tm ≤ CD.z k := fun h => hkS ((CD.hS_top k).mpr h)
              exact lt_of_not_ge hnot_le
            obtain ⟨m0, hm0⟩ := CD.hS_sub H.tm H.tm_mem
            have htm_in : H.tm ∈ Icc CD.a CD.b := by
              rw [hm0]; exact ⟨by linarith [(hr0_win m0).1], by linarith [(hr0_win m0).2]⟩
            have hBu_win : |uAiry (c n) (B n)| ≤ M_win := by
              have := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hBu : |uAiry (c n) (B n) - H.tm| < r0 / 4)
              have htm_abs : |H.tm| ≤ max |CD.a| |CD.b| :=
                abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, htm_in.1],
                  by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, htm_in.2]⟩
              rw [abs_le]; dsimp [M_win]; constructor <;> linarith [neg_abs_le H.tm, le_abs_self H.tm]
            obtain ⟨_, hΔB, herrB⟩ := hC_ut hcut hBn_pos hBu_win
            have hB_cl : |chartUT (c n) (B n) - H.tm| < r0 / 2 := by
              have h1 := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hBu : |uAiry (c n) (B n) - H.tm| < r0 / 4)
              have h2 := abs_lt.mp (herrB.trans_lt hCut)
              exact abs_lt.mpr ⟨by linarith, by linarith⟩
            have hB_vac : |chartUT (c n) (B n)| ≤ virasoroAC (c n) ^ 2 := by
              have := abs_lt.mp hB_cl
              have htm_abs : |H.tm| ≤ max |CD.a| |CD.b| :=
                abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, htm_in.1],
                  by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, htm_in.2]⟩
              have hle : |chartUT (c n) (B n)| ≤ M_ab := by
                rw [abs_le]; dsimp [M_ab]; constructor <;> linarith [neg_abs_le H.tm, le_abs_self H.tm]
              exact hle.trans hVac
            have h4r : 4 * r0 ≤ |CD.z m0 - CD.z k| := hr0_sep m0 k (fun h => hkS (by rw [← h, ← hm0]; exact H.tm_mem))
            rw [← hm0, abs_of_pos (sub_pos.mpr hzk_lt_tm)] at h4r
            have hu_dist : |uStar k n - CD.z k| < r0 := by simpa [Metric.mem_ball, Real.dist_eq] using hu_ball
            have hu_lt_B : uStar k n < chartUT (c n) (B n) := by
              linarith [(abs_lt.mp hu_dist).2, (abs_lt.mp hB_cl).1]
            let δ_ev : ℝ := min (r0 - |uStar k n - CD.z k|) (chartUT (c n) (B n) - uStar k n)
            have hδ_pos : 0 < δ_ev := lt_min (by linarith) (by linarith)
            have hball_u0 : ball (uStar k n : ℂ) δ_ev ⊆ ball (CD.z k : ℂ) R' := fun w hw => by
              rw [mem_ball] at hw ⊢
              have h2 : δ_ev ≤ r0 - |uStar k n - CD.z k| := min_le_left _ _
              have hdist_u0 : dist (uStar k n : ℂ) (CD.z k : ℂ) = |uStar k n - CD.z k| := by
                rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
              calc dist w (CD.z k : ℂ) ≤ dist w (uStar k n : ℂ) + dist (uStar k n : ℂ) (CD.z k : ℂ) := dist_triangle _ _ _
                _ < δ_ev + |uStar k n - CD.z k| := by linarith [hdist_u0]
                _ ≤ r0 := by linarith
                _ < R' := hrR'
            have hne_top_u0 : ∃ w ∈ ball (uStar k n : ℂ) δ_ev, psiTilde prob (c n) (gs_bad n) w ≠ 0 := by
              by_contra h_all0; push Not at h_all0
              have htop : analyticOrderAt (psiTilde prob (c n) (gs_bad n)) (uStar k n : ℂ) = ⊤ :=
                analyticOrderAt_eq_top.mpr (Eventually.mono (Metric.ball_mem_nhds (uStar k n : ℂ) hδ_pos) h_all0)
              exact absurd htop (order_ne_top hDiff_k hw_sph hfw_sph (ball_subset_ball hrR'.le hu_c))
            have h_even := even_analyticOrderNatAt_of_nonneg (g := psiTilde prob (c n) (gs_bad n))
              (hDiff_k.mono hball_u0) hδ_pos hδ_pos hne_top_u0
              (fun x hx => by
                have hx_in_r : x ∈ ball (CD.z k) r0 := by
                  rw [Metric.mem_ball, Real.dist_eq]
                  have h2 : δ_ev ≤ r0 - |uStar k n - CD.z k| := min_le_left _ _
                  have htri : |x - CD.z k| ≤ |x - uStar k n| + |uStar k n - CD.z k| := by
                    have e : x - CD.z k = (x - uStar k n) + (uStar k n - CD.z k) := by ring
                    rw [e]; exact abs_add_le _ _
                  linarith
                exact psiTilde_im_ofReal prob hcpos hwe_n.1 (h_in_vac x hx_in_r))
              (fun x hx => by
                have hx_in_r : x ∈ ball (CD.z k) r0 := by
                  rw [Metric.mem_ball, Real.dist_eq]
                  have h2 : δ_ev ≤ r0 - |uStar k n - CD.z k| := min_le_left _ _
                  have htri : |x - CD.z k| ≤ |x - uStar k n| + |uStar k n - CD.z k| := by
                    have e : x - CD.z k = (x - uStar k n) + (uStar k n - CD.z k) := by ring
                    rw [e]; exact abs_add_le _ _
                  linarith
                have hx_vac := h_in_vac x hx_in_r
                have hx_le_B : x ≤ chartUT (c n) (B n) := by
                  have := min_le_right (r0 - |uStar k n - CD.z k|) (chartUT (c n) (B n) - uStar k n)
                  linarith [(abs_lt.mp hx).2]
                have hB_le_Δ : B n ≤ virasoroDeltaChart (c n) x := by
                  dsimp [B]; rw [← hΔB]
                  exact (virasoroDeltaChart_strictAnti hcpos).antitoneOn
                    (abs_le.mp hx_vac) (abs_le.mp hB_vac) hx_le_B
                have hre := psiTilde_re_ofReal prob hcpos hwe_n.1 hx_vac
                have hpf := psiTilde_pref_pos prob hcpos hsh12 hM_we hx_vac
                rw [hre]
                have hgs_nn : 0 ≤ gs_bad n (virasoroDeltaChart (c n) x) := hwe_n.2.2.2 _ (Or.inr hB_le_Δ)
                have e : (prob.cardyNorm (c n / 12) (gs_bad n))⁻¹ * (-(deriv (virasoroDeltaChart (c n)) x)) *
                    (gs_bad n (virasoroDeltaChart (c n) x) * prob.cardyV (c n / 12) (virasoroDeltaChart (c n) x)) =
                    ((prob.cardyNorm (c n / 12) (gs_bad n))⁻¹ * (-(deriv (virasoroDeltaChart (c n)) x)) *
                      prob.cardyV (c n / 12) (virasoroDeltaChart (c n) x)) * gs_bad n (virasoroDeltaChart (c n) x) := by ring
                rw [e]; exact mul_nonneg hpf.le hgs_nn)
              hpsi0
            have hnz : 0 < analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) (uStar k n : ℂ) :=
              Nat.pos_of_ne_zero ((orderNat_ne_zero_iff hDiff_k hw_sph hfw_sph
                (ball_subset_ball hrR'.le hu_c)).mpr hpsi0)
            have hord_ge2 : 2 ≤ analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) (uStar k n : ℂ) := by
              obtain ⟨m, hm⟩ := h_even; omega
            have hfin := support_orderNat_finite hDiff_k hw_sph hfw_sph hrR'
            have hsum : zeroCount (psiTilde prob (c n) (gs_bad n)) (CD.z k : ℂ) r0 =
                ∑ z ∈ hfin.toFinset, analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) z := by
              unfold zeroCount
              rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
            have hle2 : analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) (uStar k n : ℂ) ≤ 2 := by
              rw [← hzc2, hsum]
              exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr ⟨hu_c, hnz.ne'⟩)
            have h2 : analyticOrderNatAt (psiTilde prob (c n) (gs_bad n)) (uStar k n : ℂ) = 2 := by omega
            simpa [hkS] using h2
        rw [hgs_eq, ← hu_eq] at hord_good
        exact hbad_choose hord_good
      exact hfreq hcontra
    filter_upwards [hzero_all, hord_all] with n hz ho gs hwe k
    exact ⟨hz gs hwe k, ho gs hwe k⟩
  refine ⟨tStar, fun k => ⟨htStar_uAiry k, htStar_chart k⟩, hpart2_ev, hpart3_ev,
    fun a' b' ha' ha'z hb'z hb' => ?_, hpart5_ev, hpart6_ev⟩
  filter_upwards [hpart4a_ev, hpart4b_ev a' b' ha' ha'z hb'z hb'] with n ha hb meas hν
  exact ⟨ha meas hν, hb meas hν⟩

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.hb_clusters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.hb_clusters

end FormalResearch.ModularBootstrap.FixedWeight
