module

public import FormalResearch.ModularBootstrap.Duality.Primal.HbClustersMain

/-!
# Near-optimal prescribed-site raw masses and inactive windows (`dsl:hb-clusters` (a)–(b))

Complements `Duality/Primal/HbClustersTheorem.lean`:
* `hb_clusters_prescribed_raw`: the `dsl:hb-raw` asymptotic at every prescribed site `s i n` for
  near-optimal crossing measures on `F_n ∪ [τ_n, ∞)` with `τ_n ≥ B_n - η_n`, `η_n = o(c_n^{1/3})`;
* `hb_clusters_inactive` (`dsl:hb-clusters` (b)): additional compact allowed sets `E_n` whose Airy
  images lie in a fixed compact subset of `{u : (normProfile H.G u).re > 0}` (in particular
  `{u > H.tm : G_N(u) > 0}`) are inactive for large `n`.
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

private instance (H : HermiteBiehlerData) : Finite (HbNodes H) :=
  Finite.of_injective (fun i : HbNodes H => (⟨i.1, i.2.1⟩ : H.S))
    (fun _ _ h => Subtype.ext (Subtype.mk.inj h))

private lemma uAiry_antitoneOn {c : ℝ} (hc : 0 < c) :
    AntitoneOn (uAiry c) (Ici (0 : ℝ)) := by
  intro t1 ht1 t2 ht2 hle
  unfold uAiry
  have h1 : 0 ≤ 3 * t1 / c := div_nonneg (mul_nonneg (by norm_num) ht1) hc.le
  have h2 : 3 * t1 / c ≤ 3 * t2 / c := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num)) hc.le
  have hsq : Real.sqrt (3 * t1 / c) ≤ Real.sqrt (3 * t2 / c) := Real.sqrt_le_sqrt h2
  have hc23 : 0 ≤ betaTip * c ^ ((2 : ℝ) / 3) := mul_nonneg betaTip_pos.le (Real.rpow_nonneg hc.le _)
  exact mul_le_mul_of_nonneg_left (by linarith) hc23

private lemma uAiry_sub_shift_tendsto {c B η : ℕ → ℝ} {tm : ℝ}
    (hc : Tendsto c atTop atTop)
    (hB : Tendsto (fun n => uAiry (c n) (B n)) atTop (𝓝 tm))
    (hη_nn : ∀ᶠ n in atTop, 0 ≤ η n)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) :
    Tendsto (fun n => uAiry (c n) (B n - η n)) atTop (𝓝 tm) ∧
      ∀ᶠ n in atTop, 0 < B n - η n := by
  let xB : ℕ → ℝ := fun n => Real.sqrt (3 * B n / c n)
  have hB_pos := eventually_pos_of_uAiry_tendsto hc hB
  have hxB_tend : Tendsto xB atTop (𝓝 xiStar) := by
    have heq : ∀ᶠ n in atTop, xB n = xiStar - uAiry (c n) (B n) * ((betaTip)⁻¹ * (c n) ^ (-(2 / 3 : ℝ))) := by
      filter_upwards [hc.eventually_gt_atTop 0] with n hcn
      have hp : (c n) ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
      dsimp [xB]; unfold uAiry
      rw [Real.rpow_neg hcn.le]; field_simp [betaTip_pos.ne', hp]; ring
    have h0 : Tendsto (fun n => xiStar - uAiry (c n) (B n) * ((betaTip)⁻¹ * (c n) ^ (-(2 / 3 : ℝ))))
        atTop (𝓝 xiStar) := by
      have h23 : Tendsto (fun n => (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc
      simpa using tendsto_const_nhds.sub (hB.mul (h23.const_mul betaTip⁻¹))
    exact h0.congr' (heq.mono fun _ h => h.symm)
  have hxB_sq : Tendsto (fun n => 3 * B n / c n) atTop (𝓝 (xiStar ^ 2)) := by
    refine (hxB_tend.pow 2).congr' ?_
    filter_upwards [hc.eventually_gt_atTop 0, hB_pos] with n hcn hBn
    dsimp [xB]; exact Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hBn.le) hcn.le)
  have hshift_tend : Tendsto (fun n => 3 * (B n - η n) / c n) atTop (𝓝 (xiStar ^ 2)) := by
    have heq : ∀ᶠ n in atTop, 3 * (B n - η n) / c n =
        3 * B n / c n - 3 * (η n / (c n) ^ ((1 : ℝ) / 3)) * (c n) ^ (-(2 / 3 : ℝ)) := by
      filter_upwards [hc.eventually_gt_atTop 0] with n hcn
      have hp13 : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
      have hp23 : (c n) ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
      rw [Real.rpow_neg hcn.le]
      have hmul : (c n) ^ ((1 : ℝ) / 3) * (c n) ^ ((2 : ℝ) / 3) = c n := by
        rw [← Real.rpow_add hcn]; norm_num
      field_simp [hcn.ne', hp13, hp23]
      calc (3 * B n - 3 * η n) * ((c n) ^ ((1 : ℝ) / 3) * (c n) ^ ((2 : ℝ) / 3))
          = (3 * B n - 3 * η n) * c n := by rw [hmul]
        _ = 3 * B n * c n - 3 * η n * c n := by ring
    have h0 : Tendsto (fun n => 3 * B n / c n - 3 * (η n / (c n) ^ ((1 : ℝ) / 3)) * (c n) ^ (-(2 / 3 : ℝ)))
        atTop (𝓝 (xiStar ^ 2)) := by
      have h23 : Tendsto (fun n => (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc
      simpa using hxB_sq.sub ((hη_o.const_mul 3).mul h23)
    exact h0.congr' (heq.mono fun _ h => h.symm)
  have hBη_pos : ∀ᶠ n in atTop, 0 < B n - η n := by
    have hxi2 : 0 < xiStar ^ 2 := pow_pos xiStar_pos 2
    filter_upwards [hc.eventually_gt_atTop 0, hshift_tend.eventually (gt_mem_nhds' (by positivity : xiStar ^ 2 / 2 < xiStar ^ 2))]
      with n hcn hgt
    have hpos_div : 0 < 3 * (B n - η n) / c n := lt_trans (half_pos hxi2) hgt
    exact pos_of_mul_pos_right ((mul_pos_iff_of_pos_right hcn).mp (by
      simpa [div_mul_cancel₀ _ hcn.ne'] using mul_pos hpos_div hcn)) (by norm_num : (0 : ℝ) ≤ 3)
  let y : ℕ → ℝ := fun n => Real.sqrt (3 * (B n - η n) / c n)
  have hy_tend : Tendsto y atTop (𝓝 xiStar) := by
    simpa [Real.sqrt_sq xiStar_pos.le] using hshift_tend.sqrt
  have hdiff_tend : Tendsto (fun n => uAiry (c n) (B n - η n) - uAiry (c n) (B n)) atTop (𝓝 0) := by
    have heq : ∀ᶠ n in atTop, uAiry (c n) (B n - η n) - uAiry (c n) (B n) =
        3 * betaTip * (η n / (c n) ^ ((1 : ℝ) / 3)) / (xB n + y n) := by
      filter_upwards [hc.eventually_gt_atTop 0, hB_pos, hBη_pos,
        hxB_tend.eventually (gt_mem_nhds' (half_pos xiStar_pos)),
        hy_tend.eventually (gt_mem_nhds' (half_pos xiStar_pos))]
        with n hcn hBn hBη hxgt hygt
      have hxy_pos : 0 < xB n + y n := add_pos (lt_trans (half_pos xiStar_pos) hxgt)
        (lt_trans (half_pos xiStar_pos) hygt)
      have hsq_diff : xB n ^ 2 - y n ^ 2 = 3 * η n / c n := by
        dsimp [xB, y]
        rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hBn.le) hcn.le),
          Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hBη.le) hcn.le)]
        ring
      have hsub_eq : xB n - y n = (3 * η n / c n) / (xB n + y n) := by
        rw [eq_div_iff hxy_pos.ne']; linarith [hsq_diff]
      have hpow : (c n) ^ ((2 : ℝ) / 3) * (c n) ^ ((1 : ℝ) / 3) = c n := by
        rw [← Real.rpow_add hcn]; norm_num
      have hp13 : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
      unfold uAiry
      have e1 : betaTip * c n ^ ((2 : ℝ) / 3) * (xiStar - y n) -
          betaTip * c n ^ ((2 : ℝ) / 3) * (xiStar - xB n) =
          betaTip * c n ^ ((2 : ℝ) / 3) * (xB n - y n) := by ring
      rw [e1, hsub_eq]
      field_simp [hcn.ne', hp13, hxy_pos.ne']
      rw [mul_assoc, hpow]; ring
    have h0 : Tendsto (fun n => 3 * betaTip * (η n / (c n) ^ ((1 : ℝ) / 3)) / (xB n + y n))
        atTop (𝓝 0) := by
      have hden : Tendsto (fun n => xB n + y n) atTop (𝓝 (xiStar + xiStar)) := hxB_tend.add hy_tend
      simpa using ((hη_o.const_mul (3 * betaTip)).div hden (by linarith [xiStar_pos]))
    exact h0.congr' (heq.mono fun _ h => h.symm)
  exact ⟨by simpa using hB.add hdiff_tend, hBη_pos⟩

/-- **Theorem E'-HB (`dsl:hb-clusters` (a)), near-optimal prescribed sites**: raw mass asymptotic
at every prescribed node `s i n` (`i ∈ H.S \ {H.tm}`), uniformly over crossing measures on
`F_n ∪ [τ_n, ∞)` when `τ_n ≥ B_n - η_n` with `0 ≤ η_n = o(c_n^{1/3})`. -/
theorem hb_clusters_prescribed_raw (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    (CD : HbClusterData H) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    (hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 H.tm))
    {τ η : ℕ → ℝ} (hη_nn : ∀ᶠ n in atTop, 0 ≤ η n)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0))
    (hτ_lb : ∀ᶠ n in atTop, constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n ≤ τ n)
    (hvag_near : ∀ (ν_seq : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧
        meas.ν (hbPrescribedSet s n ∪
          Ici (min (τ n) (constrainedThreshold prob (c n) (hbPrescribedSet s n))))ᶜ = 0) →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo CD.a CD.b →
        Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k)))) :
    let amp : ℝ := 2 * Real.sqrt xiStar * (2 * xiStar) ^ (prob.w - 1) *
      prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) / (Real.sqrt 3 * betaTip)
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (hbPrescribedSet s n ∪ Ici (τ n))ᶜ = 0 →
        ∀ (i : HbNodes H) (k : Fin CD.K), CD.z k = i.1 →
          let bi := s i n - xiBar * c n + cStar * i.1 * (c n) ^ ((1 : ℝ) / 3)
          |(meas.ν {s i n}).toReal / (amp * CD.ω k * (c n) ^ (-(1 / 6 : ℝ)) *
            Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
              (2 * Real.pi * i.1 / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
              (Real.pi / xiStar) * bi)) - 1| ≤ ε := by
  classical
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let F : ℕ → Set ℝ := hbPrescribedSet s
  let τ' : ℕ → ℝ := fun n => min (τ n) (B n)
  obtain ⟨gs0, ν0, _, hν0⟩ := hb_canonical_primal prob H hc hs_pos
  obtain ⟨r0, hr0_pos, hr0_win, hr0_sep, hr0_tm⟩ := exists_window_radius CD
  obtain ⟨hu_shift, hBη_pos⟩ := uAiry_sub_shift_tendsto hc hB_tend hη_nn hη_o
  have hτ'_uAiry_le : ∀ᶠ n in atTop, uAiry (c n) (τ' n) ≤ H.tm + r0 / 4 := by
    filter_upwards [hc.eventually_gt_atTop 0, hBη_pos, hτ_lb, hη_nn,
      hu_shift.eventually (Metric.ball_mem_nhds H.tm (show 0 < r0 / 4 by positivity))]
      with n hcn hBη hlb hnn hball
    have hτ'_lb : B n - η n ≤ τ' n := le_min hlb (by linarith)
    have hle : uAiry (c n) (τ' n) ≤ uAiry (c n) (B n - η n) :=
      uAiry_antitoneOn hcn hBη.le (hBη.le.trans hτ'_lb) hτ'_lb
    have hb := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hball :
      |uAiry (c n) (B n - η n) - H.tm| < r0 / 4)
    linarith
  intro amp ε hε
  suffices hi_all : ∀ i : HbNodes H, ∀ k : Fin CD.K, CD.z k = i.1 → ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (F n ∪ Ici (τ n))ᶜ = 0 →
        let bi := s i n - xiBar * c n + cStar * i.1 * (c n) ^ ((1 : ℝ) / 3)
        |(meas.ν {s i n}).toReal / (amp * CD.ω k * (c n) ^ (-(1 / 6 : ℝ)) *
          Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
            (2 * Real.pi * i.1 / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
            (Real.pi / xiStar) * bi)) - 1| ≤ ε by
    have hall_i : ∀ᶠ n in atTop, ∀ i : HbNodes H, ∀ k : Fin CD.K, CD.z k = i.1 →
        ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
          meas.ν (F n ∪ Ici (τ n))ᶜ = 0 →
          let bi := s i n - xiBar * c n + cStar * i.1 * (c n) ^ ((1 : ℝ) / 3)
          |(meas.ν {s i n}).toReal / (amp * CD.ω k * (c n) ^ (-(1 / 6 : ℝ)) *
            Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
              (2 * Real.pi * i.1 / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
              (Real.pi / xiStar) * bi)) - 1| ≤ ε := by
      rw [eventually_all]
      intro i
      rw [eventually_all]
      intro k
      by_cases hzk : CD.z k = i.1
      · filter_upwards [hi_all i k hzk] with n hn meas hν _; exact hn meas hν
      · exact Eventually.of_forall fun _ _ _ hbad => absurd hbad hzk
    filter_upwards [hall_i] with n hn meas hν i k hzk
    exact hn i k hzk meas hν
  intro i k hzk
  choose bump hbump_cont hbump_cs _ hbump_one hbump_zero hbump_tsupp using
    fun _ : Unit => exists_bump_near (x₀ := CD.z k) (r := r0 / 2) (by positivity)
  let φ := bump ()
  have htsub : tsupport φ ⊆ Ioo CD.a CD.b := fun u hu => by
    have h1 := hbump_tsupp () hu
    exact ⟨by linarith [h1.1, (hr0_win k).1], by linarith [h1.2, (hr0_win k).2]⟩
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
      rw [hbump_zero () (CD.z j) hj_not, mul_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have h_int_eq : ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (F n ∪ Ici (τ' n))ᶜ = 0 →
        ∫ u, φ u ∂(spectralMeasure prob (c n) meas.ν) =
          spectralWeight prob (c n) (s i n) * (meas.ν {s i n}).toReal := by
    filter_upwards [hc.eventually_ge_atTop (max 1 (12 * prob.totalShift)), hs_pos i, hτ'_uAiry_le,
      hBη_pos, hτ_lb, hη_nn,
      eventually_all.2 fun j : HbNodes H =>
        (hs_tend j).eventually (Metric.ball_mem_nhds j.1 (show 0 < r0 / 4 by positivity))]
      with n hc_ge hsi_pos hτu hBη hlb hnn hs_ball meas hν
    have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc_ge)
    have hsh12 : prob.totalShift ≤ c n / 12 := by have := (le_max_right 1 _).trans hc_ge; linarith
    have hτ'_lb : B n - η n ≤ τ' n := le_min hlb (by linarith)
    have hτ'_pos : 0 < τ' n := lt_of_lt_of_le hBη hτ'_lb
    rw [integral_spectralMeasure prob hcpos hsh12 meas.ν (hbump_cont ())]
    have hnull_sing : meas.ν ((Ioi (0 : ℝ) ∩ {t | spectralWeight prob (c n) t * φ (uAiry (c n) t) ≠ 0}) \
        {s i n}) = 0 := by
      refine measure_mono_null (fun t ht => ?_) hν
      intro hmem
      have hne0 : φ (uAiry (c n) t) ≠ 0 := right_ne_zero_of_mul ht.1.2
      have hu_Ioo : uAiry (c n) t ∈ Ioo (CD.z k - r0 / 2) (CD.z k + r0 / 2) := by
        by_contra hn; exact hne0 (hbump_zero () _ hn)
      rcases hmem with ⟨j, rfl⟩ | htτ
      · have hj_eq : j = i := by
          by_contra hji
          obtain ⟨kj, hkj⟩ := CD.hS_sub j.1 j.2.1
          have hkj_ne : kj ≠ k := fun h => hji (Subtype.ext (by rw [hkj, h, hzk]))
          have hsep := hr0_sep kj k hkj_ne
          have hj_u : |uAiry (c n) (s j n) - CD.z kj| < r0 / 4 := by
            rw [← hkj]; simpa [Metric.mem_ball, Real.dist_eq] using hs_ball j
          have htri : |CD.z kj - CD.z k| ≤
              |uAiry (c n) (s j n) - CD.z kj| + |uAiry (c n) (s j n) - CD.z k| := by
            have e : CD.z kj - CD.z k =
                -(uAiry (c n) (s j n) - CD.z kj) + (uAiry (c n) (s j n) - CD.z k) := by ring
            rw [e]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
          have hkj_dist : |uAiry (c n) (s j n) - CD.z k| < r0 / 2 :=
            abs_lt.mpr ⟨by linarith [hu_Ioo.1], by linarith [hu_Ioo.2]⟩
          linarith
        exact ht.2 (congrArg (fun x => s x n) hj_eq)
      · have hle_τ : uAiry (c n) t ≤ uAiry (c n) (τ' n) :=
          uAiry_antitoneOn hcpos hτ'_pos.le (hτ'_pos.le.trans htτ) htτ
        have htm_le : H.tm ≤ CD.z k := (CD.hS_top k).mp (by rw [hzk]; exact i.2.1)
        have h2r : 2 * r0 ≤ |CD.z k - H.tm| := hr0_tm k (by rw [hzk]; exact i.2.2)
        have htm_lt : H.tm < CD.z k := lt_of_le_of_ne htm_le (by rw [hzk]; exact i.2.2.symm)
        rw [abs_of_pos (sub_pos.mpr htm_lt)] at h2r
        linarith [hu_Ioo.1]
    rw [setIntegral_Ioi_of_singleton hsi_pos _ hnull_sing]
    have hφ1 : φ (uAiry (c n) (s i n)) = 1 := by
      have hi_b : |uAiry (c n) (s i n) - CD.z k| < r0 / 4 := by
        rw [hzk]; simpa [Metric.mem_ball, Real.dist_eq] using hs_ball i
      have := abs_lt.mp hi_b
      exact hbump_one () _ ⟨by linarith, by linarith⟩
    rw [hφ1, mul_one]; ring
  have hω_pos := CD.hω_pos k
  have hε1 : 0 < min (ε / 4) 1 * CD.ω k := mul_pos (lt_min (by positivity) zero_lt_one) hω_pos
  have hunif_sw : ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (F n ∪ Ici (τ' n))ᶜ = 0 →
        |spectralWeight prob (c n) (s i n) * (meas.ν {s i n}).toReal - CD.ω k| ≤ min (ε / 4) 1 * CD.ω k := by
    let δ := min (ε / 4) 1 * CD.ω k
    have hδ : 0 < δ := hε1
    by_contra hnot
    rw [not_eventually] at hnot
    let Bad := fun (n : ℕ) (m : AdmissibleCrossingMeasure prob (c n / 12)) =>
      m.ν (F n ∪ Ici (τ' n))ᶜ = 0 ∧
      δ < |spectralWeight prob (c n) (s i n) * (m.ν {s i n}).toReal - CD.ω k|
    have hfreq : ∃ᶠ n in atTop, ∃ m, Bad n m := hnot.mono fun _ hn => by push Not at hn; exact hn
    let ν_bad : ℕ → Measure ℝ := fun n => if h : ∃ m, Bad n m then h.choose.ν else ν0 n
    have hν_bad_mem : ∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_bad n = meas.ν ∧ meas.ν (F n ∪ Ici (τ' n))ᶜ = 0 := by
      filter_upwards [hν0] with n ⟨meas0, hν0_eq, hν0_supp⟩
      dsimp [ν_bad]; split_ifs with h
      · exact ⟨h.choose, rfl, h.choose_spec.1⟩
      · have hsub : (F n ∪ Ici (τ' n))ᶜ ⊆ (F n ∪ Ici (B n))ᶜ :=
          compl_subset_compl.mpr (union_subset_union_right _ (Ici_subset_Ici.mpr (min_le_right _ _)))
        exact ⟨meas0, hν0_eq, measure_mono_null hsub hν0_supp⟩
    have hvag_bad := hvag_near ν_bad hν_bad_mem φ (hbump_cont ()) (hbump_cs ()) htsub
    rw [hsum_lim] at hvag_bad
    have hball_bad : ∀ᶠ n in atTop, |∫ u, φ u ∂(spectralMeasure prob (c n) (ν_bad n)) - CD.ω k| < δ := by
      filter_upwards [hvag_bad.eventually (Metric.ball_mem_nhds (CD.ω k) hδ)] with n hn
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    have hcontra : ∀ᶠ n in atTop, ¬ ∃ m, Bad n m := by
      filter_upwards [h_int_eq, hball_bad] with n hint hball ⟨m, hm1, hm2⟩
      have hex : ∃ m', Bad n m' := ⟨m, hm1, hm2⟩
      have hspec := Classical.choose_spec hex
      have hν_eq : ν_bad n = hex.choose.ν := dite_eq_left hex
      rw [hν_eq, hint hex.choose hspec.1] at hball
      exact absurd hball (not_lt_of_ge hspec.2.le)
    exact hfreq hcontra
  have hcardy := cardyV_mul_jAiry_asymp prob hc (hs_tend i)
  filter_upwards [hunif_sw, hs_pos i, hc.eventually_ge_atTop (max 1 (12 * prob.totalShift)),
    hc.eventually_gt_atTop 0,
    hcardy.eventually (Metric.ball_mem_nhds 1 (show 0 < min (ε / 2) 1 by positivity))]
    with n h5 hsi_pos hc_ge hcpos hcq meas hν
  have hsub_τ : meas.ν (F n ∪ Ici (τ' n))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (union_subset_union_right _ (Ici_subset_Ici.mpr (min_le_left _ _)))) hν
  have hsh12 : prob.totalShift ≤ c n / 12 := by have := (le_max_right 1 _).trans hc_ge; linarith
  have hswJ := weight_eq_jAiry_mul hcpos hsh12 hsi_pos
  have hV_pos : 0 < prob.cardyV (c n / 12) (s i n) := prob.cardyV_pos hsh12 hsi_pos
  have hswVJ : spectralWeight prob (c n) (s i n) *
      (2 * Real.pi * prob.cardyV (c n / 12) (s i n) * jAiry (c n) (s i n)) = 1 := by
    have h1 : jAiry (c n) (s i n) * spectralWeight prob (c n) (s i n) *
        (2 * Real.pi * prob.cardyV (c n / 12) (s i n)) = 1 := by
      rw [← hswJ]; field_simp [Real.pi_ne_zero, hV_pos.ne']
    linarith
  let bi := s i n - xiBar * c n + cStar * i.1 * (c n) ^ ((1 : ℝ) / 3)
  let R := (c n) ^ (-(1 / 6 : ℝ)) * Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
    (2 * Real.pi * i.1 / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) + (Real.pi / xiStar) * bi)
  let p := spectralWeight prob (c n) (s i n) * (meas.ν {s i n}).toReal / CD.ω k
  let q := (2 * Real.pi * prob.cardyV (c n / 12) (s i n) * jAiry (c n) (s i n)) / (amp * R)
  have hp_err : |p - 1| ≤ min (ε / 4) 1 := by
    have heq : p - 1 =
        (spectralWeight prob (c n) (s i n) * (meas.ν {s i n}).toReal - CD.ω k) / CD.ω k := by
      dsimp [p]; field_simp [hω_pos.ne']
    rw [heq, abs_div, abs_of_pos hω_pos, div_le_iff₀ hω_pos]
    exact h5 meas hsub_τ
  have hq_err : |q - 1| ≤ min (ε / 2) 1 := by
    simpa [q, R, bi, amp, Metric.mem_ball, Real.dist_eq] using hcq.le
  have hq_abs : |q| ≤ 2 := by
    have := abs_le.mp (hq_err.trans (min_le_right _ _))
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hrat_eq : (meas.ν {s i n}).toReal / (amp * CD.ω k * R) = p * q := by
    dsimp [p, q]
    calc (meas.ν {s i n}).toReal / (amp * CD.ω k * R)
        = (meas.ν {s i n}).toReal * (spectralWeight prob (c n) (s i n) *
            (2 * Real.pi * prob.cardyV (c n / 12) (s i n) * jAiry (c n) (s i n))) /
            (amp * CD.ω k * R) := by rw [hswVJ, mul_one]
      _ = (spectralWeight prob (c n) (s i n) * (meas.ν {s i n}).toReal / CD.ω k) *
            ((2 * Real.pi * prob.cardyV (c n / 12) (s i n) * jAiry (c n) (s i n)) /
              (amp * R)) := by ring
  dsimp [bi, amp] at hrat_eq ⊢
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

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.hb_clusters_prescribed_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.hb_clusters_prescribed_raw

/-- **Theorem E'-HB (`dsl:hb-clusters` (b))**: additional compact sets `E_n ⊂ (0, ∞)` whose
Airy images stay inside a fixed compact subset `K_E ⊆ {u : (normProfile H.G u).re > 0}`
(in particular `K_E ⊆ {u > H.tm : G_N(u) > 0}`) are inactive for large `n`: the threshold on
`F_n ∪ E_n ∪ [τ, ∞)` remains `B_n`, and every attaining measure gives `E_n` zero mass. -/
theorem hb_clusters_inactive (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    (hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 H.tm))
    {K_E : Set ℝ} (hKE_comp : IsCompact K_E)
    (hKE_pos : ∀ u ∈ K_E, 0 < (normProfile H.G (u : ℂ)).re)
    {E : ℕ → Set ℝ} (hE_comp : ∀ᶠ n in atTop, IsCompact (E n))
    (hE_pos : ∀ᶠ n in atTop, E n ⊆ Ioi 0)
    (hE_img : ∀ᶠ n in atTop, ∀ t ∈ E n, uAiry (c n) t ∈ K_E) :
    ∀ᶠ n in atTop,
      constrainedThreshold prob (c n) (hbPrescribedSet s n ∪ E n) =
        constrainedThreshold prob (c n) (hbPrescribedSet s n) ∧
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν ((hbPrescribedSet s n ∪ E n) ∪
          Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)))ᶜ = 0 →
        meas.ν (E n) = 0 := by
  classical
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let F : ℕ → Set ℝ := hbPrescribedSet s
  let f_re : ℝ → ℝ := fun u => (normProfile H.G (u : ℂ)).re
  have hf_cont : Continuous f_re :=
    Complex.continuous_re.comp ((normProfile_differentiable (hbExtremalProfile H)).continuous.comp Complex.continuous_ofReal)
  obtain ⟨δ, hδ_pos, hKE_ge⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ K_E, δ ≤ f_re u := by
    by_cases hne : K_E.Nonempty
    · obtain ⟨u0, hu0, hmin⟩ := hKE_comp.exists_isMinOn hne hf_cont.continuousOn
      exact ⟨f_re u0, hKE_pos u0 hu0, fun u hu => hmin hu⟩
    · refine ⟨1, zero_lt_one, fun u hu => absurd ⟨u, hu⟩ hne⟩
  obtain ⟨M, hM_pos, hKE_bd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ K_E, |u| ≤ M := by
    obtain ⟨R, hR⟩ := hKE_comp.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨max R 0, le_max_right R 0, fun u hu => ?_⟩
    have h1 : |u| ≤ R := by simpa [Real.norm_eq_abs] using hR hu
    exact h1.trans (le_max_left R 0)
  let m : ℕ := Nat.ceil (M + 1)
  have hm_ge : M + 1 ≤ (m : ℝ) + 1 := by
    have := Nat.le_ceil (M + 1); linarith
  have huc : UniformContinuousOn f_re (Icc (-(M + 1)) (M + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf_cont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η_uc, hη_pos, hη_uc⟩ := huc (δ / 3) (by positivity)
  obtain ⟨c_str, hc_str⟩ := fixedChargeStrip_of_large prob
  have hF_Ioi := hbPrescribedSet_subset_Ioi hs_pos
  let P := fun (n : ℕ) (gs : ℝ → ℝ) =>
    IsWeakExtremal prob (c n) (F n) (B n) gs ∧
    ∀ E' : Set ℝ, IsCompact E' → E' ⊆ Ioi 0 → (∀ t ∈ E', 0 < gs t) →
      constrainedThreshold prob (c n) (F n ∪ E') = B n ∧
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν ((F n ∪ E') ∪ Ici (B n))ᶜ = 0 → meas.ν E' = 0
  have hex_gs : ∀ᶠ n in atTop, ∃ gs, P n gs := by
    filter_upwards [hc.eventually_ge_atTop c_str, hF_Ioi] with n h1 hFn
    have hS := hc_str h1
    obtain ⟨-, gs, ⟨htc, hM, hvac, hnn, -⟩, -, -, h_inact⟩ :=
      theorem_primal hS (isCompact_hbPrescribedSet s n) hFn
    exact ⟨gs, ⟨htc, hM, hvac, hnn⟩, h_inact⟩
  let gs : ℕ → ℝ → ℝ := fun n => if h : ∃ g, P n g then h.choose else fun _ => 0
  have hgs_spec : ∀ᶠ n in atTop, P n (gs n) := by
    filter_upwards [hex_gs] with n hn
    dsimp [gs]; rw [dite_eq_left hn]; exact hn.choose_spec
  have hgs_we : ∀ᶠ n in atTop, IsWeakExtremal prob (c n) (F n) (B n) (gs n) :=
    hgs_spec.mono fun _ h => h.1
  obtain ⟨-, hbl⟩ := weakExtremal_blnorm prob H hc hs_pos hs_tend hB_tend hgs_we
  have hbl_m : TendstoUniformlyOn (fun n => psiTilde prob (c n) (gs n))
      (normProfile H.G) atTop (closedBall (0 : ℂ) ((m : ℝ) + 1)) := hbl m
  rw [Metric.tendstoUniformlyOn_iff] at hbl_m
  have hpsi_ev := hbl_m (δ / 3) (by positivity)
  obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err hM_pos
  have hC_ut_err : ∀ᶠ n in atTop, C_ut * (c n) ^ (-(2 / 3 : ℝ)) < min 1 η_uc := by
    have h0 : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_ut
    exact h0.eventually (gt_mem_nhds (lt_min zero_lt_one hη_pos))
  filter_upwards [hgs_spec, hpsi_ev, hE_comp, hE_pos, hE_img, hC_ut_err,
    hc.eventually_ge_atTop (max c_ut (max 1 (12 * prob.totalShift))),
    virasoroAC_sq_eventually_ge hc (M + 1)]
    with n ⟨hwe, h_inact⟩ hpsi hEc hEp hEi hCut hc_ge hVac
  have hcut : c_ut ≤ c n := (le_max_left _ _).trans hc_ge
  have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans ((le_max_right _ _).trans hc_ge))
  have hsh12 : prob.totalShift ≤ c n / 12 := by
    have := (le_max_right 1 _).trans ((le_max_right _ _).trans hc_ge); linarith
  have hM_we : 0 < prob.cardyNorm (c n / 12) (gs n) := by rw [hwe.2.1]; exact zero_lt_one
  refine h_inact (E n) hEc hEp (fun t ht => ?_)
  have ht_pos : 0 < t := hEp ht
  have hu_K : uAiry (c n) t ∈ K_E := hEi t ht
  have hu_M : |uAiry (c n) t| ≤ M := hKE_bd _ hu_K
  obtain ⟨_, hΔt, herr⟩ := hC_ut hcut ht_pos hu_M
  let u := chartUT (c n) t
  have herr_min : |uAiry (c n) t - u| < min 1 η_uc := herr.trans_lt hCut
  have hu_M1 : |u| ≤ M + 1 := by
    have h1 := abs_lt.mp (herr_min.trans_le (min_le_left _ _))
    have h2 := abs_le.mp hu_M
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hu_cb : (u : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hu_M1.trans hm_ge
  have hu_Icc : u ∈ Icc (-(M + 1)) (M + 1) := abs_le.mp hu_M1
  have hu0_Icc : uAiry (c n) t ∈ Icc (-(M + 1)) (M + 1) := by
    have := abs_le.mp hu_M; exact ⟨by linarith, by linarith⟩
  have huc_f : |f_re u - f_re (uAiry (c n) t)| < δ / 3 := by
    apply hη_uc u hu_Icc (uAiry (c n) t) hu0_Icc
    rw [Real.dist_eq, abs_sub_comm]
    exact herr_min.trans_le (min_le_right _ _)
  have hpsi_u : dist (normProfile H.G (u : ℂ)) (psiTilde prob (c n) (gs n) (u : ℂ)) < δ / 3 :=
    hpsi (u : ℂ) hu_cb
  have hre_err : |f_re u - (psiTilde prob (c n) (gs n) (u : ℂ)).re| < δ / 3 := by
    calc |f_re u - (psiTilde prob (c n) (gs n) (u : ℂ)).re|
        = |(normProfile H.G (u : ℂ) - psiTilde prob (c n) (gs n) (u : ℂ)).re| := by rfl
      _ ≤ ‖normProfile H.G (u : ℂ) - psiTilde prob (c n) (gs n) (u : ℂ)‖ := Complex.abs_re_le_norm _
      _ = dist (normProfile H.G (u : ℂ)) (psiTilde prob (c n) (gs n) (u : ℂ)) := (dist_eq_norm _ _).symm
      _ < δ / 3 := hpsi_u
  have hre_pos : 0 < (psiTilde prob (c n) (gs n) (u : ℂ)).re := by
    have hf_ge := hKE_ge _ hu_K
    have h1 := abs_lt.mp huc_f
    have h2 := abs_lt.mp hre_err
    linarith
  have hgs_u : 0 < gs n (virasoroDeltaChart (c n) u) :=
    (psiTilde_re_pos_iff prob hcpos hsh12 hwe.1 hM_we (hu_M1.trans hVac)).mp hre_pos
  rwa [hΔt] at hgs_u

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.hb_clusters_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.hb_clusters_inactive

end FormalResearch.ModularBootstrap.FixedWeight