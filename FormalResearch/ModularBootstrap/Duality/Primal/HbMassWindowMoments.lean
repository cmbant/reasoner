module

public import FormalResearch.ModularBootstrap.Duality.Primal.HbMassMoments

/-!
# Moment and off-node mass bounds for near-optimal crossing measures (`dsl:hb-mass`)

Moment and off-node concentration clauses of `Proposition E'-HB-M` (`dsl:hb-mass`,
`dual_spectrum_limit.tex`):
* `hb_mass_first_moment`: `∫_{W_{m0,n}(r)} (t - B_n)_+ dμ_n ≤ C_r η_n` at the simple node `H.tm`;
* `hb_mass_second_moment`: `∫_{W_{k,n}(r)} |t - t^*_{k,n}|^2 dμ_n ≤ C_{k,r} c_n^{1/3} η_n`
  at each double node `CD.z k ∉ H.S`;
* `hb_mass_off_node`: `μ_n(K_off) ≤ C_K η_n / c_n^{1/3}` on compact `K_off ⊆ [CD.a, CD.b] \ {z_k}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.ConcreteBootstrap
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Bessel
  FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.Hadamard
  FormalResearch.ArgPrinciple

private instance (H : HermiteBiehlerData) : Finite (HbNodes H) :=
  Finite.of_injective (fun i : HbNodes H => (⟨i.1, i.2.1⟩ : H.S))
    (fun _ _ h => Subtype.ext (Subtype.mk.inj h))

private lemma normProfile_re_pos_of_mem_Icc (H : HermiteBiehlerData) (CD : HbClusterData H)
    {u : ℝ} (hu_ab : u ∈ Icc CD.a CD.b) (hu_tm : u ≤ H.tm) (hu_ne : ∀ k : Fin CD.K, u ≠ CD.z k) :
    0 < (normProfile H.G (u : ℂ)).re := by
  have him : (normProfile H.G (u : ℂ)).im = 0 := by
    unfold normProfile
    have h1 : H.G (u : ℂ) = ((H.G (u : ℂ)).re : ℂ) := Complex.ext rfl (H.G_real u)
    rw [h1]; simp
  have hnn : 0 ≤ (normProfile H.G (u : ℂ)).re := by
    unfold normProfile
    have h1 : H.G (u : ℂ) = ((H.G (u : ℂ)).re : ℂ) := Complex.ext rfl (H.G_real u)
    rw [h1]; simp only [← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (inv_nonneg.mpr (hbExtremalProfile H).mass_pos.le) (H.G_nonneg_left u hu_tm)
  have hne : (normProfile H.G (u : ℂ)).re ≠ 0 := by
    intro h0
    have hzero : normProfile H.G (u : ℂ) = 0 := Complex.ext h0 him
    obtain ⟨k, hk⟩ := (CD.hzero_win (u : ℂ) (by simpa using hu_ab)).1 hzero
    exact hu_ne k (by exact_mod_cast hk)
  exact lt_of_le_of_ne hnn hne.symm

private lemma eq_zero_and_deriv_eq_zero_of_analyticOrderNatAt_two {f : ℂ → ℂ} {z0 : ℂ}
    (han : AnalyticAt ℂ f z0) (hord2 : analyticOrderNatAt f z0 = 2) :
    f z0 = 0 ∧ deriv f z0 = 0 := by
  have h_ord_eq : analyticOrderAt f z0 = (2 : ℕ∞) := by
    have hne : analyticOrderAt f z0 ≠ ⊤ := by
      intro htop
      have : analyticOrderNatAt f z0 = 0 := by unfold analyticOrderNatAt; rw [htop]; rfl
      omega
    have h1 := ENat.natCast_toNat hne
    change (analyticOrderNatAt f z0 : ℕ∞) = _ at h1
    rw [← h1, hord2]; rfl
  obtain ⟨g, hg_an, _, hg_eq⟩ := han.analyticOrderAt_eq_natCast.mp h_ord_eq
  have hmul : f =ᶠ[𝓝 z0] fun z => (z - z0) ^ 2 * g z := by
    filter_upwards [hg_eq] with z hz; simpa [pow_two] using hz
  have hf0 : f z0 = 0 := by rw [hmul.eq_of_nhds]; simp
  have hd_mul : HasDerivAt (fun z : ℂ => (z - z0) ^ 2 * g z) 0 z0 := by
    have ha : HasDerivAt (fun z : ℂ => (z - z0) ^ 2) 0 z0 := by
      convert (((hasDerivAt_id z0).sub_const z0).fun_pow 2) using 1
      dsimp [id]; simp
    simpa using ha.fun_mul hg_an.differentiableAt.hasDerivAt
  have hdf0 : deriv f z0 = 0 := by rw [hmul.deriv_eq]; exact hd_mul.deriv
  exact ⟨hf0, hdf0⟩

private lemma compact_pos_lower_bound (H : HermiteBiehlerData) {K : Set ℝ} (hK : IsCompact K)
    (hpos : ∀ u ∈ K, 0 < (normProfile H.G (u : ℂ)).re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ K, δ ≤ (normProfile H.G (u : ℂ)).re := by
  let f_re : ℝ → ℝ := fun u => (normProfile H.G (u : ℂ)).re
  have hf_cont : Continuous f_re :=
    Complex.continuous_re.comp ((normProfile_differentiable (hbExtremalProfile H)).continuous.comp Complex.continuous_ofReal)
  by_cases hne : K.Nonempty
  · obtain ⟨u0, hu0, hmin⟩ := hK.exists_isMinOn hne hf_cont.continuousOn
    exact ⟨f_re u0, hpos u0 hu0, fun u hu => hmin hu⟩
  · exact ⟨1, zero_lt_one, fun u hu => absurd ⟨u, hu⟩ hne⟩

private lemma exists_pad_isolating {K : ℕ} (z : Fin K → ℝ) {a b z0 r : ℝ}
    (ha : a < z0 - r) (hb : z0 + r < b)
    (hsep : ∀ j : Fin K, z j ≠ z0 → r < |z j - z0|) :
    ∃ pad : ℝ, 0 < pad ∧ pad ≤ 1 ∧ a < z0 - r - pad ∧ z0 + r + pad < b ∧
      ∀ j : Fin K, z j ≠ z0 → r + pad < |z j - z0| := by
  classical
  let S_ne := Finset.univ.filter fun j : Fin K => z j ≠ z0
  have hS_pos : ∃ δ : ℝ, 0 < δ ∧ ∀ j : Fin K, z j ≠ z0 → δ < |z j - z0| - r := by
    by_cases hne : S_ne.Nonempty
    · let S_d := S_ne.image fun j => (|z j - z0| - r) / 2
      have hSd_ne : S_d.Nonempty := hne.image _
      refine ⟨S_d.min' hSd_ne, ?_, fun j hj => ?_⟩
      · obtain ⟨j, hj_mem, hj_eq⟩ := Finset.mem_image.mp (Finset.min'_mem S_d hSd_ne)
        rw [← hj_eq]
        exact half_pos (sub_pos.mpr (hsep j (Finset.mem_filter.mp hj_mem).2))
      · have hj_mem : (|z j - z0| - r) / 2 ∈ S_d :=
          Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
        have hle := Finset.min'_le S_d _ hj_mem
        have hpos : 0 < |z j - z0| - r := sub_pos.mpr (hsep j hj)
        linarith
    · refine ⟨1, zero_lt_one, fun j hj => absurd ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩ hne⟩
  obtain ⟨δ, hδ_pos, hδ_lt⟩ := hS_pos
  let pad := min 1 (min ((z0 - r - a) / 2) (min ((b - (z0 + r)) / 2) δ))
  refine ⟨pad, by positivity, min_le_left _ _, ?_, ?_, fun j hj => ?_⟩
  · have : pad ≤ (z0 - r - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  · have : pad ≤ (b - (z0 + r)) / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  · have : pad ≤ δ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith [hδ_lt j hj]

private lemma canonical_psiTilde_converges (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    (hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 H.tm))
    {R : ℝ} (_hR : 0 ≤ R) :
    ∃ gs0 : ℕ → ℝ → ℝ,
      (∀ᶠ n in atTop, IsWeakExtremal prob (c n) (hbPrescribedSet s n)
        (constrainedThreshold prob (c n) (hbPrescribedSet s n)) (gs0 n)) ∧
      (∀ᶠ n in atTop, gs0 n (constrainedThreshold prob (c n) (hbPrescribedSet s n)) = 0) ∧
      (∀ᶠ n in atTop, DifferentiableOn ℂ (psiTilde prob (c n) (gs0 n)) (ball (0 : ℂ) (R + 2))) ∧
      TendstoUniformlyOn (fun n => psiTilde prob (c n) (gs0 n)) (normProfile H.G) atTop (closedBall (0 : ℂ) R) ∧
      TendstoUniformlyOn (fun n => deriv (psiTilde prob (c n) (gs0 n))) (deriv (normProfile H.G)) atTop
        (closedBall (0 : ℂ) R) ∧
      TendstoUniformlyOn (fun n => iteratedDeriv 2 (psiTilde prob (c n) (gs0 n)))
        (iteratedDeriv 2 (normProfile H.G)) atTop (closedBall (0 : ℂ) R) := by
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let F : ℕ → Set ℝ := hbPrescribedSet s
  obtain ⟨gs0, ν0, hgs0, hν0⟩ := hb_canonical_primal prob H hc hs_pos
  have hgs0_we : ∀ᶠ n in atTop, IsWeakExtremal prob (c n) (F n) (B n) (gs0 n) :=
    hgs0.mono fun _ h => h.1
  have hgs0_B : ∀ᶠ n in atTop, gs0 n (B n) = 0 := by
    filter_upwards [hgs0, hν0] with n hgn ⟨meas0, _, hsupp0⟩
    have hpos_atom := (hgn.2.2 meas0 hsupp0).2.1
    have hae := (hgn.2.2 meas0 hsupp0).2.2
    have hne : ({B n} ∩ {t | t ∈ F n ∪ Ici (B n) ∧ gs0 n t = 0}).Nonempty := by
      by_contra h_emp
      rw [Set.not_nonempty_iff_eq_empty] at h_emp
      have hsub : ({B n} : Set ℝ) ⊆ {t | ¬(t ∈ F n ∪ Ici (B n) ∧ gs0 n t = 0)} := fun t ht hbad =>
        Set.notMem_empty t (h_emp ▸ ⟨ht, hbad⟩)
      exact hpos_atom.ne' (measure_mono_null hsub hae)
    obtain ⟨t, ht1, _, ht2⟩ := hne
    rw [mem_singleton_iff.mp ht1] at ht2
    exact ht2
  let m_r : ℕ := Nat.ceil (R + 2)
  let R_m : ℝ := (m_r : ℝ) + 3
  have hm_ge : R + 2 ≤ (m_r : ℝ) + 1 := by
    have := Nat.le_ceil (R + 2); linarith
  obtain ⟨_, hbl⟩ := weakExtremal_blnorm prob H hc hs_pos hs_tend hB_tend hgs0_we
  obtain ⟨c_an, hc_an, han⟩ := psiTilde_analyticOnNhd prob
  obtain ⟨D_p⟩ := UniformPropositionPData.of_problem prob
  have hDiff_ball : ∀ᶠ n in atTop, DifferentiableOn ℂ (psiTilde prob (c n) (gs0 n)) (ball (0 : ℂ) R_m) := by
    filter_upwards [hc.eventually_ge_atTop c_an, chartAC_sq_eventually_ge D_p.hr1_pos hc R_m, hgs0_we]
      with n hcn hAc hwe
    have hcpos : 0 < c n := hc_an.trans_le hcn
    have hsub : ball (0 : ℂ) R_m ⊆ psiDom (c n) :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hAc)).trans
        (closedBall_chartAC_subset_psiDom D_p.hr1_pos hcpos)
    exact ((han hcn hwe.1).mono hsub).differentiableOn
  have hDiff_out : ∀ᶠ n in atTop, DifferentiableOn ℂ (psiTilde prob (c n) (gs0 n)) (ball (0 : ℂ) (R + 2)) :=
    hDiff_ball.mono fun n hn => hn.mono (ball_subset_ball (by dsimp [R_m]; linarith))
  obtain ⟨n_d, hn_d⟩ := eventually_atTop.mp hDiff_ball
  let Fn : ℕ → ℂ → ℂ := fun n => psiTilde prob (c (n + n_d)) (gs0 (n + n_d))
  have hFn_diff : ∀ n, DifferentiableOn ℂ (Fn n) (ball (0 : ℂ) R_m) := fun n => hn_d (n + n_d) (Nat.le_add_left n_d n)
  have hFn_loc : TendstoLocallyUniformlyOn Fn (normProfile H.G) atTop (ball (0 : ℂ) R_m) := by
    have hbl_shift : TendstoUniformlyOn Fn (normProfile H.G) atTop (closedBall (0 : ℂ) ((m_r + 2 : ℕ) + 1)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have h0 := (Metric.tendstoUniformlyOn_iff.mp (hbl (m_r + 2))) ε hε
      rw [eventually_atTop] at h0 ⊢
      obtain ⟨N, hN⟩ := h0
      exact ⟨N, fun n hn => hN (n + n_d) (by omega)⟩
    exact hbl_shift.tendstoLocallyUniformlyOn.mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by dsimp [R_m]; push_cast; linarith)))
  have hsub_cb : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) R_m := fun z hz => by
    rw [mem_closedBall_zero_iff] at hz; rw [mem_ball_zero_iff]; dsimp [R_m]; linarith
  have hcb_comp : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have unshift_unif : ∀ (F0 : ℕ → ℂ → ℂ) (G0 : ℂ → ℂ),
      TendstoUniformlyOn (fun n => F0 (n + n_d)) G0 atTop (closedBall (0 : ℂ) R) →
      TendstoUniformlyOn F0 G0 atTop (closedBall (0 : ℂ) R) := by
    intro F0 G0 hF0
    rw [Metric.tendstoUniformlyOn_iff] at hF0 ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hF0 ε hε)
    rw [eventually_atTop]
    refine ⟨N + n_d, fun n hn x hx => ?_⟩
    have := hN (n - n_d) (by omega) x hx
    rwa [show n - n_d + n_d = n by omega] at this
  have hFn_0 : TendstoUniformlyOn Fn (normProfile H.G) atTop (closedBall (0 : ℂ) R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hFn_loc _ hsub_cb hcb_comp
  have hFn_1 : TendstoUniformlyOn (fun n => deriv (Fn n)) (deriv (normProfile H.G)) atTop (closedBall (0 : ℂ) R) := by
    have h1 := tendstoLocallyUniformlyOn_iteratedDeriv isOpen_ball 1 Fn (normProfile H.G) hFn_diff hFn_loc
    simpa only [iteratedDeriv_one] using (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp h1 _ hsub_cb hcb_comp
  have hFn_2 : TendstoUniformlyOn (fun n => iteratedDeriv 2 (Fn n)) (iteratedDeriv 2 (normProfile H.G)) atTop
      (closedBall (0 : ℂ) R) := by
    have h2 := tendstoLocallyUniformlyOn_iteratedDeriv isOpen_ball 2 Fn (normProfile H.G) hFn_diff hFn_loc
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp h2 _ hsub_cb hcb_comp
  exact ⟨gs0, hgs0_we, hgs0_B, hDiff_out, unshift_unif _ _ hFn_0, unshift_unif _ _ hFn_1, unshift_unif _ _ hFn_2⟩

/-- First-moment bound at the simple node `H.tm` (`dsl:hb-mass`, `(t - B_n)_+` moment):
for every isolating radius `r > 0` around `H.tm`, near-optimal crossing measures `ν_n`
supported on `F_n ∪ [B_n - η_n, ∞)` satisfy
`∫_{W_{m0,n}(r)} max (t - B_n) 0 * spectralWeight prob c_n t ∂ν_n ≤ C_r η_n`. -/
theorem hb_mass_first_moment (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    (CD : HbClusterData H) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    (hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 H.tm))
    {η : ℕ → ℝ} (hη_nn : ∀ᶠ n in atTop, 0 ≤ η n)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0))
    (hvag_near : ∀ (ν_seq : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0) →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo CD.a CD.b →
        Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k))))
    {r : ℝ} (hr_pos : 0 < r) (hr_a : CD.a < H.tm - r) (hr_b : H.tm + r < CD.b)
    (hr_sep : ∀ k : Fin CD.K, CD.z k ≠ H.tm → r < |CD.z k - H.tm|) :
    ∃ C_r : ℝ, 0 < C_r ∧ ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0 →
        IntegrableOn (fun t => max (t - constrainedThreshold prob (c n) (hbPrescribedSet s n)) 0 *
            spectralWeight prob (c n) t)
          {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - H.tm| ≤ r} meas.ν ∧
        ∫ t in {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - H.tm| ≤ r},
            max (t - constrainedThreshold prob (c n) (hbPrescribedSet s n)) 0 *
              spectralWeight prob (c n) t ∂meas.ν ≤ C_r * η n := by
  classical
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let W : ℕ → Set ℝ := fun n => {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - H.tm| ≤ r}
  obtain ⟨pad, hpad_pos, _, hpad_a, hpad_b, hpad_sep⟩ :=
    exists_pad_isolating CD.z hr_a hr_b hr_sep
  let M_win : ℝ := |H.tm| + r + pad + 1
  let R_c : ℝ := M_win + 1
  obtain ⟨gs0, hgs0_we, hgs0_B, hDiff, hUnif0, hUnif1, _⟩ :=
    canonical_psiTilde_converges prob H hc hs_pos hs_tend hB_tend (R := R_c) (by positivity)
  obtain ⟨C_pos, hCpos_pos, h_near⟩ :=
    near_opt_extremal_le prob H CD hc hs_pos hs_tend hB_tend hη_nn hη_o hvag_near hgs0_we hgs0_B
  let c1 : ℝ := -(deriv (normProfile H.G) (H.tm : ℂ)).re / 2
  have hc1_pos : 0 < c1 := by dsimp [c1]; linarith [deriv_normProfile_tm_neg H]
  have hGder_cont : Continuous (fun u : ℝ => (deriv (normProfile H.G) (u : ℂ)).re) :=
    Complex.continuous_re.comp ((normProfile_deriv_differentiable H).continuous.comp Complex.continuous_ofReal)
  have hGder_nhds : ∀ᶠ (u : ℝ) in 𝓝 H.tm, (deriv (normProfile H.G) (u : ℂ)).re < -(3 / 2 : ℝ) * c1 := by
    refine hGder_cont.continuousAt.tendsto.eventually (gt_mem_nhds ?_)
    dsimp [c1]; linarith [deriv_normProfile_tm_neg H]
  obtain ⟨r1, hr1_pos, hr1_sub⟩ := Metric.eventually_nhds_iff.mp hGder_nhds
  let r_loc : ℝ := min (r1 / 2) (min (r / 2) (pad / 2))
  have hr_loc_pos : 0 < r_loc := by positivity
  let K_ann : Set ℝ := Icc (H.tm - r - pad) (H.tm - r_loc)
  have hK_pos : ∀ u ∈ K_ann, 0 < (normProfile H.G (u : ℂ)).re := fun u hu => by
    refine normProfile_re_pos_of_mem_Icc H CD ⟨by linarith [hu.1, hpad_a], by linarith [hu.2, hpad_b]⟩
      (by linarith [hu.2]) fun k => ?_
    by_cases hkm : CD.z k = H.tm
    · linarith [hu.2, hkm]
    · have hk_sep := hpad_sep k hkm
      rcases le_or_gt (CD.z k) H.tm with hle | hgt
      · have : CD.z k < H.tm - r - pad := by rw [abs_of_nonpos (by linarith)] at hk_sep; linarith
        linarith [hu.1]
      · linarith [hu.2]
  obtain ⟨δ_K, hδK_pos, hδK_lb⟩ := compact_pos_lower_bound H isCompact_Icc hK_pos
  let c_low : ℝ := min c1 (δ_K / (2 * (r + r_loc + pad)))
  have hclow_pos : 0 < c_low := by positivity
  obtain ⟨C_d, hCd, hmv_bds⟩ := virasoroDeltaChart_mvt_bounds
  have hCd_pos : 0 < C_d := lt_of_lt_of_le (half_pos cStar_pos) hCd
  obtain ⟨jac_c0, jac_lo, _, _, hjac_lo_pos, _, hjac_bds⟩ := jacRatio_bounds (show 0 ≤ M_win by positivity)
  obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err (show 0 ≤ M_win by positivity)
  obtain ⟨t_c0, _, ht_bds⟩ := uAiry_window_t_bounds (show 0 ≤ M_win by positivity)
  let C_r : ℝ := (C_d / (jac_lo * c_low)) * C_pos + 1
  refine ⟨C_r, by positivity, ?_⟩
  have hB_chart := chartUT_tendsto_of_uAiry hc (eventually_pos_of_uAiry_tendsto hc hB_tend) hB_tend
  have hCerr : ∀ᶠ n in atTop, C_ut * (c n) ^ (-(2 / 3 : ℝ)) < pad / 2 := by
    have h0 : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_ut
    exact h0.eventually (gt_mem_nhds (by positivity))
  rw [Metric.tendstoUniformlyOn_iff] at hUnif0 hUnif1
  filter_upwards [h_near, hgs0_we, hgs0_B, hDiff, hUnif0 (δ_K / 2) (half_pos hδK_pos),
    hUnif1 (c1 / 2) (half_pos hc1_pos),
    hB_chart.eventually (Metric.ball_mem_nhds H.tm (lt_min (half_pos hr_loc_pos) (half_pos hpad_pos))),
    eventually_pos_of_uAiry_tendsto hc hB_tend,
    hB_tend.eventually (Metric.ball_mem_nhds H.tm (half_pos hpad_pos)),
    hCerr, hc.eventually_ge_atTop (max jac_c0 (max c_ut (max t_c0 (max 1 (12 * prob.totalShift))))),
    virasoroAC_sq_eventually_ge hc R_c, hη_nn]
    with n hnear hwe hgsB hDiffn hU0 hU1 hBc hB_pos hBu hCut hc_ge hVac hnn meas hν
  have hc_pos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))))
  have hsh12 : prob.totalShift ≤ c n / 12 := by
    have := (le_max_right 1 _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))); linarith
  have hjac_c : jac_c0 ≤ c n := (le_max_left _ _).trans hc_ge
  have hcut : c_ut ≤ c n := (le_max_left _ _).trans ((le_max_right _ _).trans hc_ge)
  have htc : t_c0 ≤ c n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))
  obtain ⟨hint_IciB, _, h_gs_int⟩ := hnear meas hν
  let t_lo := c n * (xiStar / 2) ^ 2 / 3
  let t_hi := c n * (3 * xiStar / 2) ^ 2 / 3
  have ht_lo_pos : 0 < t_lo := by have := xiStar_pos; positivity
  have hW_sub : W n ⊆ Icc t_lo t_hi := fun t ht => by
    have hu_win : |uAiry (c n) t| ≤ M_win := by
      have := abs_le.mp ht.2
      dsimp [M_win]; exact abs_le.mpr ⟨by linarith [neg_abs_le H.tm], by linarith [le_abs_self H.tm]⟩
    exact ht_bds htc ht.1 hu_win
  have ht_le : t_lo ≤ t_hi := by
    have hxi := xiStar_pos
    dsimp [t_lo, t_hi]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sq_le_sq' (by linarith) (by linarith)) hc_pos.le) (by norm_num)
  have hW_meas : MeasurableSet (W n) :=
    measurableSet_Ioi.inter ((continuous_abs.comp ((continuous_uAiry (c n)).sub continuous_const)).measurable measurableSet_Iic)
  have hint_W : IntegrableOn (fun t => max (t - B n) 0 * spectralWeight prob (c n) t) (W n) meas.ν :=
    integrableOn_spectralWeight_mul_of_continuousOn prob hc_pos hsh12 ht_lo_pos ht_le meas hW_meas hW_sub
      ((continuous_id.sub continuous_const).max continuous_const).continuousOn
  refine ⟨hint_W, ?_⟩
  let uB := chartUT (c n) (B n)
  have huB_ball : |uB - H.tm| < min (r_loc / 2) (pad / 2) := by simpa [uB, Metric.mem_ball, Real.dist_eq] using hBc
  have huB_loc : |uB - H.tm| < r_loc / 2 := by
    have h := abs_lt.mp huB_ball
    exact abs_lt.mpr ⟨by linarith [min_le_left (r_loc / 2) (pad / 2)],
      by linarith [min_le_left (r_loc / 2) (pad / 2)]⟩
  have huB_pad : |uB - H.tm| < pad / 2 := abs_lt.mpr
    ⟨by linarith [(abs_lt.mp huB_ball).1, min_le_right (r_loc / 2) (pad / 2)],
     by linarith [(abs_lt.mp huB_ball).2, min_le_right (r_loc / 2) (pad / 2)]⟩
  have hBu_win : |uAiry (c n) (B n)| ≤ M_win := by
    have := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hBu : |uAiry (c n) (B n) - H.tm| < pad / 2)
    dsimp [M_win]; exact abs_le.mpr ⟨by linarith [neg_abs_le H.tm], by linarith [le_abs_self H.tm]⟩
  obtain ⟨_, hΔB, _⟩ := hC_ut hcut hB_pos hBu_win
  have huB_vac : |uB| ≤ virasoroAC (c n) ^ 2 := by
    have := abs_lt.mp huB_pad
    exact (abs_le.mpr ⟨by linarith [neg_abs_le H.tm], by linarith [le_abs_self H.tm]⟩).trans
      ((show |H.tm| + pad / 2 ≤ R_c by dsimp [R_c, M_win]; linarith).trans hVac)
  have hψB : (psiTilde prob (c n) (gs0 n) (uB : ℂ)).re = 0 := by
    have h1 := (psiTilde_eq_zero_iff prob hc_pos hsh12 hwe.1
      (by rw [hwe.2.1]; exact zero_lt_one) huB_vac).mpr (by rw [hΔB]; exact hgsB)
    rw [h1, Complex.zero_re]
  have hlin_loc : ∀ u ∈ Icc (H.tm - r_loc) uB,
      c1 * (uB - u) ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re := by
    have hr_loc_le : r_loc ≤ r :=
      (min_le_right _ _).trans ((min_le_left _ _).trans (half_le_self hr_pos.le))
    refine lin_lower_bound_of_holo hDiffn (by linarith [(abs_lt.mp huB_loc).1]) (fun u hu => ?_) hψB (fun u hu => ?_)
    · simp only [Metric.mem_ball, Complex.dist_eq, Complex.ofReal_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
      have hpad := abs_lt.mp huB_pad
      have : |u| ≤ R_c := by
        dsimp [R_c, M_win]
        exact abs_le.mpr ⟨by linarith [neg_abs_le H.tm, hu.1, hpad_pos, hr_loc_le],
          by linarith [le_abs_self H.tm, hu.2, hpad.2, hr_pos, hpad_pos]⟩
      linarith
    · have hu_cb : (u : ℂ) ∈ closedBall (0 : ℂ) R_c := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        have hpad := abs_lt.mp huB_pad
        dsimp [R_c, M_win]
        exact abs_le.mpr ⟨by linarith [neg_abs_le H.tm, hu.1, hpad_pos, hr_loc_le],
          by linarith [le_abs_self H.tm, hu.2, hpad.2, hr_pos, hpad_pos]⟩
      have hu_ball : u ∈ ball H.tm r1 := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        have h1 := (abs_lt.mp huB_loc).2
        have h2 : r_loc ≤ r1 / 2 := min_le_left _ _
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hdG := (hr1_sub hu_ball).le
      have hdist : dist (deriv (normProfile H.G) (u : ℂ)) (deriv (psiTilde prob (c n) (gs0 n)) (u : ℂ)) < c1 / 2 :=
        hU1 (u : ℂ) hu_cb
      rw [dist_eq_norm] at hdist
      have hre := (Complex.abs_re_le_norm _).trans hdist.le
      rw [Complex.sub_re] at hre
      linarith [abs_le.mp hre]
  have h_pt : ∀ t ∈ W n ∩ Ici (B n),
      max (t - B n) 0 * spectralWeight prob (c n) t ≤
        (C_d / (jac_lo * c_low)) * (c n) ^ ((1 : ℝ) / 3) * (gs0 n t / (2 * Real.pi)) := by
    intro t ⟨htW, htB⟩
    have ht_pos : 0 < t := htW.1
    have hu_win : |uAiry (c n) t| ≤ M_win := by
      have := abs_le.mp htW.2
      dsimp [M_win]; exact abs_le.mpr ⟨by linarith [neg_abs_le H.tm], by linarith [le_abs_self H.tm]⟩
    obtain ⟨_, hΔt, herrt⟩ := hC_ut hcut ht_pos hu_win
    let u := chartUT (c n) t
    have hu_close : |u - H.tm| ≤ r + pad / 2 := by
      have h1 := abs_le.mp htW.2
      have h2 := abs_lt.mp (herrt.trans_lt hCut)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hu_vac : |u| ≤ virasoroAC (c n) ^ 2 := by
      have h1 := abs_le.mp hu_close
      exact (abs_le.mpr ⟨by linarith [neg_abs_le H.tm], by linarith [le_abs_self H.tm]⟩).trans
        ((show |H.tm| + (r + pad / 2) ≤ R_c by dsimp [R_c, M_win]; linarith).trans hVac)
    have hu_le_uB : u ≤ uB := by
      by_contra hlt; push Not at hlt
      have := (virasoroDeltaChart_strictAnti hc_pos) (abs_le.mp huB_vac) (abs_le.mp hu_vac) hlt
      rw [hΔB, hΔt] at this; linarith [mem_Ici.mp htB]
    have hmvt := (hmv_bds hc_pos hu_vac huB_vac hu_le_uB).2
    rw [hΔt, hΔB] at hmvt
    have hψ_lb : c_low * (uB - u) ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re := by
      by_cases hloc : H.tm - r_loc ≤ u
      · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sub_nonneg.mpr hu_le_uB)).trans
          (hlin_loc u ⟨hloc, hu_le_uB⟩)
      · push Not at hloc
        have hu_K : u ∈ K_ann := ⟨by linarith [(abs_le.mp hu_close).1], hloc.le⟩
        have hG_lb := hδK_lb u hu_K
        have hu_cb : (u : ℂ) ∈ closedBall (0 : ℂ) R_c := by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          have h1 := abs_le.mp hu_close
          exact abs_le.mpr ⟨by linarith [neg_abs_le H.tm], by linarith [le_abs_self H.tm]⟩
        have hdist : dist (normProfile H.G (u : ℂ)) (psiTilde prob (c n) (gs0 n) (u : ℂ)) < δ_K / 2 :=
          hU0 (u : ℂ) hu_cb
        rw [dist_eq_norm] at hdist
        have hre := (Complex.abs_re_le_norm _).trans hdist.le
        rw [Complex.sub_re] at hre
        have hψ_ge : δ_K / 2 ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re := by linarith [(abs_le.mp hre).2]
        have hu_diff_bd : uB - u ≤ r + r_loc + pad := by
          have h1 := (abs_lt.mp huB_loc).2
          have h2 := (abs_le.mp hu_close).1
          linarith
        have hmul_le : (δ_K / (2 * (r + r_loc + pad))) * (uB - u) ≤ δ_K / 2 := by
          have hr_den : 0 < 2 * (r + r_loc + pad) := by positivity
          calc (δ_K / (2 * (r + r_loc + pad))) * (uB - u)
              ≤ (δ_K / (2 * (r + r_loc + pad))) * (r + r_loc + pad) :=
                mul_le_mul_of_nonneg_left hu_diff_bd (by positivity)
            _ = δ_K / 2 := by field_simp [(by positivity : r + r_loc + pad ≠ 0)]
        exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sub_nonneg.mpr hu_le_uB)).trans (hmul_le.trans hψ_ge)
    have hgs_eq := gs_div_two_pi_eq_jacRatio prob hc_pos hsh12 ht_pos hwe.1 hwe.2.1 hu_vac hΔt
    have hjac := (hjac_bds hjac_c ht_pos hu_win hu_vac).1
    have hsw_pos : 0 < spectralWeight prob (c n) t := spectralWeight_pos hc_pos hsh12 ht_pos
    have ht_max : max (t - B n) 0 = t - B n := max_eq_left (sub_nonneg.mpr (mem_Ici.mp htB))
    rw [ht_max, hgs_eq]
    have hc13_pos : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
    have hprod_le : (t - B n) * spectralWeight prob (c n) t ≤
        (C_d * (c n) ^ ((1 : ℝ) / 3) * (uB - u)) * spectralWeight prob (c n) t :=
      mul_le_mul_of_nonneg_right hmvt hsw_pos.le
    have hprod_le2 : (C_d * (c n) ^ ((1 : ℝ) / 3) * (uB - u)) * spectralWeight prob (c n) t ≤
        (C_d / (jac_lo * c_low)) * (c n) ^ ((1 : ℝ) / 3) *
          (jacRatio (c n) t * spectralWeight prob (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re) := by
      have h1 : (uB - u) ≤ (1 / (jac_lo * c_low)) * (jacRatio (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re) := by
        have hψ_nn : 0 ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re :=
          (mul_nonneg hclow_pos.le (sub_nonneg.mpr hu_le_uB)).trans hψ_lb
        have hstep1 : c_low * (uB - u) * jac_lo ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re * jacRatio (c n) t :=
          mul_le_mul hψ_lb hjac hjac_lo_pos.le hψ_nn
        calc uB - u = (c_low * (uB - u) * jac_lo) / (jac_lo * c_low) := by
              field_simp [hjac_lo_pos.ne', hclow_pos.ne']
          _ ≤ ((psiTilde prob (c n) (gs0 n) (u : ℂ)).re * jacRatio (c n) t) / (jac_lo * c_low) :=
              div_le_div_of_nonneg_right hstep1 (mul_pos hjac_lo_pos hclow_pos).le
          _ = (1 / (jac_lo * c_low)) * (jacRatio (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re) := by ring
      calc (C_d * (c n) ^ ((1 : ℝ) / 3) * (uB - u)) * spectralWeight prob (c n) t
          = C_d * (c n) ^ ((1 : ℝ) / 3) * spectralWeight prob (c n) t * (uB - u) := by ring
        _ ≤ C_d * (c n) ^ ((1 : ℝ) / 3) * spectralWeight prob (c n) t *
              ((1 / (jac_lo * c_low)) * (jacRatio (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (C_d / (jac_lo * c_low)) * (c n) ^ ((1 : ℝ) / 3) *
              (jacRatio (c n) t * spectralWeight prob (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re) := by ring
    exact hprod_le.trans hprod_le2
  have hsplit_W : ∫ t in W n, max (t - B n) 0 * spectralWeight prob (c n) t ∂meas.ν =
      ∫ t in W n ∩ Ici (B n), max (t - B n) 0 * spectralWeight prob (c n) t ∂meas.ν := by
    have hunion : W n = (W n ∩ Ici (B n)) ∪ (W n ∩ (Ici (B n))ᶜ) := (Set.inter_union_compl (W n) (Ici (B n))).symm
    have hdisj : Disjoint (W n ∩ Ici (B n)) (W n ∩ (Ici (B n))ᶜ) :=
      disjoint_compl_right.mono Set.inter_subset_right Set.inter_subset_right
    have hint1 := hint_W.mono_set Set.inter_subset_left
    have hint2 := hint_W.mono_set Set.inter_subset_left
    have hzero : ∫ t in W n ∩ (Ici (B n))ᶜ, max (t - B n) 0 * spectralWeight prob (c n) t ∂meas.ν = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      have hlt : t < B n := not_le.mp ht.2
      rw [max_eq_right (sub_nonpos.mpr hlt.le), zero_mul]
    conv_lhs => rw [hunion]
    rw [setIntegral_union hdisj (hW_meas.inter measurableSet_Ici.compl) hint1 hint2, hzero, add_zero]
  have hint_WI : IntegrableOn (fun t => max (t - B n) 0 * spectralWeight prob (c n) t) (W n ∩ Ici (B n)) meas.ν :=
    hint_W.mono_set Set.inter_subset_left
  have hint_gs_div : IntegrableOn (fun t => gs0 n t / (2 * Real.pi)) (Ici (B n)) meas.ν :=
    hint_IciB.div_const _
  have hc13_pos : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
  rw [hsplit_W]
  calc ∫ t in W n ∩ Ici (B n), max (t - B n) 0 * spectralWeight prob (c n) t ∂meas.ν
      ≤ ∫ t in W n ∩ Ici (B n),
          ((C_d / (jac_lo * c_low)) * (c n) ^ ((1 : ℝ) / 3)) * (gs0 n t / (2 * Real.pi)) ∂meas.ν := by
          refine setIntegral_mono_on hint_WI ((hint_gs_div.mono_set Set.inter_subset_right).const_mul _)
            (hW_meas.inter measurableSet_Ici) (fun t ht => by simpa [mul_assoc] using h_pt t ht)
    _ = ((C_d / (jac_lo * c_low)) * (c n) ^ ((1 : ℝ) / 3)) *
          ∫ t in W n ∩ Ici (B n), gs0 n t / (2 * Real.pi) ∂meas.ν := integral_const_mul _ _
    _ ≤ ((C_d / (jac_lo * c_low)) * (c n) ^ ((1 : ℝ) / 3)) *
          ∫ t in Ici (B n), gs0 n t / (2 * Real.pi) ∂meas.ν := by
          refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hint_gs_div ?_
            (Eventually.of_forall Set.inter_subset_right)) (by positivity)
          filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
          exact div_nonneg (hwe.2.2.2 t (Or.inr ht)) Real.two_pi_pos.le
    _ ≤ ((C_d / (jac_lo * c_low)) * (c n) ^ ((1 : ℝ) / 3)) * (C_pos * η n / (c n) ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left h_gs_int (by positivity)
    _ = ((C_d / (jac_lo * c_low)) * C_pos) * η n := by field_simp [hc13_pos.ne']
    _ ≤ C_r * η n := mul_le_mul_of_nonneg_right (by dsimp [C_r]; linarith) hnn

/-- Second-moment bound at a double node `CD.z k ∉ H.S` (`dsl:hb-mass`, `|t - t^*_{k,n}|^2` moment):
for any sequence `tStar` pinning the double zero of weak extremals near `CD.z k` and any isolating
radius `r > 0`, near-optimal crossing measures `ν_n` satisfy
`∫_{W_{k,n}(r)} (t - tStar n)^2 * spectralWeight prob c_n t ∂ν_n ≤ C_{k,r} c_n^{1/3} η_n`. -/
theorem hb_mass_second_moment (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    (CD : HbClusterData H) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    (hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 H.tm))
    {η : ℕ → ℝ} (hη_nn : ∀ᶠ n in atTop, 0 ≤ η n)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0))
    (hvag_near : ∀ (ν_seq : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0) →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo CD.a CD.b →
        Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k))))
    (k : Fin CD.K) (hkS : CD.z k ∉ H.S)
    {tStar : ℕ → ℝ} (htStar_tend : Tendsto (fun n => uAiry (c n) (tStar n)) atTop (𝓝 (CD.z k)))
    (htStar_zero : ∀ᶠ n in atTop, ∀ gs : ℝ → ℝ,
      IsWeakExtremal prob (c n) (hbPrescribedSet s n)
        (constrainedThreshold prob (c n) (hbPrescribedSet s n)) gs →
      gs (tStar n) = 0 ∧
      analyticOrderNatAt (psiTilde prob (c n) gs) (chartUT (c n) (tStar n) : ℂ) = 2)
    {r : ℝ} (hr_pos : 0 < r) (hr_a : CD.a < CD.z k - r) (hr_b : CD.z k + r < CD.b)
    (hr_sep : ∀ j : Fin CD.K, j ≠ k → r < |CD.z j - CD.z k|) :
    ∃ C_kr : ℝ, 0 < C_kr ∧ ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0 →
        IntegrableOn (fun t => (t - tStar n) ^ 2 * spectralWeight prob (c n) t)
          {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - CD.z k| ≤ r} meas.ν ∧
        ∫ t in {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - CD.z k| ≤ r},
            (t - tStar n) ^ 2 * spectralWeight prob (c n) t ∂meas.ν ≤
          C_kr * (c n) ^ ((1 : ℝ) / 3) * η n := by
  classical
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let W : ℕ → Set ℝ := fun n => {t ∈ Ioi (0 : ℝ) | |uAiry (c n) t - CD.z k| ≤ r}
  have hr_sep' : ∀ j : Fin CD.K, CD.z j ≠ CD.z k → r < |CD.z j - CD.z k| := fun j hj =>
    hr_sep j (fun h => hj (congrArg CD.z h))
  obtain ⟨pad, hpad_pos, _, hpad_a, hpad_b, hpad_sep⟩ :=
    exists_pad_isolating CD.z hr_a hr_b hr_sep'
  obtain ⟨m_tm, hm_tm⟩ := CD.hS_sub H.tm H.tm_mem
  have hzk_lt : CD.z k < H.tm := lt_of_not_ge fun h => hkS ((CD.hS_top k).mpr h)
  have hzk_pad_lt : CD.z k + r + pad < H.tm := by
    have hne : CD.z m_tm ≠ CD.z k := by rw [← hm_tm]; exact hzk_lt.ne'
    have hsp := hpad_sep m_tm hne
    rw [← hm_tm, abs_of_pos (sub_pos.mpr hzk_lt)] at hsp
    linarith
  let M_win : ℝ := |CD.z k| + r + pad + 1
  let R_c : ℝ := M_win + 1
  obtain ⟨gs0, hgs0_we, hgs0_B, hDiff, hUnif0, _, hUnif2⟩ :=
    canonical_psiTilde_converges prob H hc hs_pos hs_tend hB_tend (R := R_c) (by positivity)
  obtain ⟨C_pos, hCpos_pos, h_near⟩ :=
    near_opt_extremal_le prob H CD hc hs_pos hs_tend hB_tend hη_nn hη_o hvag_near hgs0_we hgs0_B
  let m0 : ℝ := (iteratedDeriv 2 (normProfile H.G) (CD.z k : ℂ)).re / 2
  have hm0_pos : 0 < m0 := by dsimp [m0]; linarith [iteratedDeriv2_normProfile_pos H CD hkS]
  have hGd2_cont : Continuous (fun u : ℝ => (iteratedDeriv 2 (normProfile H.G) (u : ℂ)).re) := by
    have han1 : AnalyticOnNhd ℂ (deriv (normProfile H.G)) univ :=
      (normProfile_deriv_differentiable H).differentiableOn.analyticOnNhd isOpen_univ
    have h2_diff : Differentiable ℂ (iteratedDeriv 2 (normProfile H.G)) := by
      have heq : iteratedDeriv 2 (normProfile H.G) = deriv (deriv (normProfile H.G)) := by
        ext z; rw [iteratedDeriv_succ', iteratedDeriv_one]
      rw [heq]; exact differentiableOn_univ.mp han1.deriv.differentiableOn
    exact Complex.continuous_re.comp (h2_diff.continuous.comp Complex.continuous_ofReal)
  have hGd2_nhds : ∀ᶠ (u : ℝ) in 𝓝 (CD.z k), (3 / 2 : ℝ) * m0 < (iteratedDeriv 2 (normProfile H.G) (u : ℂ)).re := by
    refine hGd2_cont.continuousAt.tendsto.eventually (lt_mem_nhds ?_)
    dsimp [m0]; linarith [iteratedDeriv2_normProfile_pos H CD hkS]
  obtain ⟨r1, hr1_pos, hr1_sub⟩ := Metric.eventually_nhds_iff.mp hGd2_nhds
  let r_loc : ℝ := min (r1 / 2) (min (r / 2) (pad / 2))
  have hr_loc_pos : 0 < r_loc := by positivity
  let K_ann : Set ℝ := Icc (CD.z k - r - pad) (CD.z k + r + pad) \ Ioo (CD.z k - r_loc) (CD.z k + r_loc)
  have hK_comp : IsCompact K_ann := isCompact_Icc.diff isOpen_Ioo
  have hK_pos : ∀ u ∈ K_ann, 0 < (normProfile H.G (u : ℂ)).re := fun u hu => by
    refine normProfile_re_pos_of_mem_Icc H CD ⟨by linarith [hu.1.1, hpad_a], by linarith [hu.1.2, hpad_b]⟩
      (by linarith [hu.1.2, hzk_pad_lt]) fun j => ?_
    by_cases hjk : CD.z j = CD.z k
    · intro heq
      rw [heq, hjk] at hu
      exact hu.2 ⟨by linarith, by linarith⟩
    · have hk_sep := hpad_sep j hjk
      have hub : |u - CD.z k| ≤ r + pad := abs_le.mpr ⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩
      intro heq; rw [heq] at hub; linarith
  obtain ⟨δ_K, hδK_pos, hδK_lb⟩ := compact_pos_lower_bound H hK_comp hK_pos
  let m_low : ℝ := min (m0 / 2) (δ_K / (2 * (2 * (r + pad)) ^ 2))
  have hmlow_pos : 0 < m_low := by positivity
  obtain ⟨C_d, hCd, hmv_bds⟩ := virasoroDeltaChart_mvt_bounds
  have hCd_pos : 0 < C_d := lt_of_lt_of_le (half_pos cStar_pos) hCd
  obtain ⟨jac_c0, jac_lo, _, _, hjac_lo_pos, _, hjac_bds⟩ := jacRatio_bounds (show 0 ≤ M_win by positivity)
  obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err (show 0 ≤ M_win by positivity)
  obtain ⟨t_c0, _, ht_bds⟩ := uAiry_window_t_bounds (show 0 ≤ M_win by positivity)
  let C_kr : ℝ := (C_d ^ 2 / (jac_lo * m_low)) * C_pos + 1
  refine ⟨C_kr, by positivity, ?_⟩
  have htStar_pos := eventually_pos_of_uAiry_tendsto hc htStar_tend
  have huStar_tend := chartUT_tendsto_of_uAiry hc htStar_pos htStar_tend
  have hCerr : ∀ᶠ n in atTop, C_ut * (c n) ^ (-(2 / 3 : ℝ)) < pad / 2 := by
    have h0 : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_ut
    exact h0.eventually (gt_mem_nhds (by positivity))
  have htm_gap : 0 < H.tm - (CD.z k + r) := by linarith
  rw [Metric.tendstoUniformlyOn_iff] at hUnif0 hUnif2
  filter_upwards [h_near, hgs0_we, hDiff, htStar_zero, hUnif0 (δ_K / 2) (half_pos hδK_pos),
    hUnif2 (m0 / 2) (half_pos hm0_pos), htStar_pos,
    huStar_tend.eventually (Metric.ball_mem_nhds (CD.z k) (lt_min (half_pos hr_loc_pos) (half_pos hpad_pos))),
    htStar_tend.eventually (Metric.ball_mem_nhds (CD.z k) (half_pos hpad_pos)),
    hB_tend.eventually (Metric.ball_mem_nhds H.tm (half_pos htm_gap)),
    eventually_pos_of_uAiry_tendsto hc hB_tend,
    hCerr, hc.eventually_ge_atTop (max jac_c0 (max c_ut (max t_c0 (max 1 (12 * prob.totalShift))))),
    virasoroAC_sq_eventually_ge hc R_c, hη_nn]
    with n hnear hwe hDiffn htz hU0 hU2 htS_pos huS_ball htuS_ball hBu hB_pos hCut hc_ge hVac hnn meas hν
  have hc_pos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))))
  have hsh12 : prob.totalShift ≤ c n / 12 := by
    have := (le_max_right 1 _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))); linarith
  have hjac_c : jac_c0 ≤ c n := (le_max_left _ _).trans hc_ge
  have hcut : c_ut ≤ c n := (le_max_left _ _).trans ((le_max_right _ _).trans hc_ge)
  have htc : t_c0 ≤ c n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))
  obtain ⟨hint_IciB, _, h_gs_int⟩ := hnear meas hν
  let t_lo := c n * (xiStar / 2) ^ 2 / 3
  let t_hi := c n * (3 * xiStar / 2) ^ 2 / 3
  have ht_lo_pos : 0 < t_lo := by have := xiStar_pos; positivity
  have hW_sub : W n ⊆ Icc t_lo t_hi := fun t ht => by
    have hu_win : |uAiry (c n) t| ≤ M_win := by
      have := abs_le.mp ht.2
      dsimp [M_win]; exact abs_le.mpr ⟨by linarith [neg_abs_le (CD.z k)], by linarith [le_abs_self (CD.z k)]⟩
    exact ht_bds htc ht.1 hu_win
  have ht_le : t_lo ≤ t_hi := by
    have hxi := xiStar_pos
    dsimp [t_lo, t_hi]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sq_le_sq' (by linarith) (by linarith)) hc_pos.le) (by norm_num)
  have hW_meas : MeasurableSet (W n) :=
    measurableSet_Ioi.inter ((continuous_abs.comp ((continuous_uAiry (c n)).sub continuous_const)).measurable measurableSet_Iic)
  have hint_W : IntegrableOn (fun t => (t - tStar n) ^ 2 * spectralWeight prob (c n) t) (W n) meas.ν :=
    integrableOn_spectralWeight_mul_of_continuousOn prob hc_pos hsh12 ht_lo_pos ht_le meas hW_meas hW_sub
      (((continuous_id.sub continuous_const).pow 2)).continuousOn
  refine ⟨hint_W, ?_⟩
  let uS := chartUT (c n) (tStar n)
  have huS_loc : |uS - CD.z k| < r_loc / 2 := by
    have h := abs_lt.mp (by simpa [uS, Metric.mem_ball, Real.dist_eq] using huS_ball : |uS - CD.z k| < min (r_loc / 2) (pad / 2))
    exact abs_lt.mpr ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) h.1, lt_of_lt_of_le h.2 (min_le_left _ _)⟩
  have huS_pad : |uS - CD.z k| < pad / 2 := by
    have h := abs_lt.mp (by simpa [uS, Metric.mem_ball, Real.dist_eq] using huS_ball : |uS - CD.z k| < min (r_loc / 2) (pad / 2))
    exact abs_lt.mpr ⟨by linarith [min_le_right (r_loc / 2) (pad / 2)], by linarith [min_le_right (r_loc / 2) (pad / 2)]⟩
  have htuS_win : |uAiry (c n) (tStar n)| ≤ M_win := by
    have := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using htuS_ball : |uAiry (c n) (tStar n) - CD.z k| < pad / 2)
    dsimp [M_win]; exact abs_le.mpr ⟨by linarith [neg_abs_le (CD.z k)], by linarith [le_abs_self (CD.z k)]⟩
  obtain ⟨_, hΔS, _⟩ := hC_ut hcut htS_pos htuS_win
  have huS_vac : |uS| ≤ virasoroAC (c n) ^ 2 := by
    have := abs_lt.mp huS_pad
    exact (abs_le.mpr ⟨by linarith [neg_abs_le (CD.z k)], by linarith [le_abs_self (CD.z k)]⟩).trans
      ((show |CD.z k| + pad / 2 ≤ R_c by dsimp [R_c, M_win]; linarith).trans hVac)
  have huS_ball_c : (uS : ℂ) ∈ ball (0 : ℂ) (R_c + 2) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    have := abs_lt.mp huS_pad
    have : |uS| ≤ R_c := abs_le.mpr ⟨by linarith [neg_abs_le (CD.z k)], by linarith [le_abs_self (CD.z k)]⟩
    linarith
  have han_uS : AnalyticAt ℂ (psiTilde prob (c n) (gs0 n)) (uS : ℂ) :=
    (hDiffn.analyticOnNhd isOpen_ball) (uS : ℂ) huS_ball_c
  have hord2_uS : analyticOrderNatAt (psiTilde prob (c n) (gs0 n)) (uS : ℂ) = 2 := (htz (gs0 n) hwe).2
  obtain ⟨hψ0, hψ1⟩ := eq_zero_and_deriv_eq_zero_of_analyticOrderNatAt_two han_uS hord2_uS
  have hquad_loc : ∀ u ∈ Icc (CD.z k - r_loc) (CD.z k + r_loc),
      (m0 / 2) * (u - uS) ^ 2 ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re := by
    have hr_loc_le : r_loc ≤ r :=
      (min_le_right _ _).trans ((min_le_left _ _).trans (half_le_self hr_pos.le))
    have huS_mem : uS ∈ Icc (CD.z k - r_loc) (CD.z k + r_loc) := by
      have := abs_lt.mp huS_loc; exact ⟨by linarith, by linarith⟩
    refine quad_lower_bound_of_holo hDiffn huS_mem (fun u hu => ?_) (by rw [hψ0, Complex.zero_re])
      (by rw [hψ1, Complex.zero_re]) (fun u hu => ?_)
    · simp only [Metric.mem_ball, Complex.dist_eq, Complex.ofReal_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
      have : |u| ≤ R_c := by
        dsimp [R_c, M_win]
        exact abs_le.mpr
          ⟨by linarith [neg_abs_le (CD.z k), hu.1, hpad_pos, hr_loc_le],
           by linarith [le_abs_self (CD.z k), hu.2, hpad_pos, hr_loc_le]⟩
      linarith
    · have hu_cb : (u : ℂ) ∈ closedBall (0 : ℂ) R_c := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        dsimp [R_c, M_win]
        exact abs_le.mpr
          ⟨by linarith [neg_abs_le (CD.z k), hu.1, hpad_pos, hr_loc_le],
           by linarith [le_abs_self (CD.z k), hu.2, hpad_pos, hr_loc_le]⟩
      have hu_ball : u ∈ ball (CD.z k) r1 := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        have h2 : r_loc ≤ r1 / 2 := min_le_left _ _
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hG2 := hr1_sub hu_ball
      have hdist : dist (iteratedDeriv 2 (normProfile H.G) (u : ℂ))
          (iteratedDeriv 2 (psiTilde prob (c n) (gs0 n)) (u : ℂ)) < m0 / 2 := hU2 (u : ℂ) hu_cb
      rw [dist_eq_norm] at hdist
      have hre := (Complex.abs_re_le_norm _).trans hdist.le
      rw [Complex.sub_re] at hre
      linarith [(abs_le.mp hre).2]
  have hW_sub_B : W n ⊆ Ici (B n) := fun t htW => by
    have hBu_gt : CD.z k + r < uAiry (c n) (B n) := by
      have := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hBu :
        |uAiry (c n) (B n) - H.tm| < (H.tm - (CD.z k + r)) / 2)
      linarith
    have hu_le : uAiry (c n) t ≤ CD.z k + r := by linarith [(abs_le.mp htW.2).2]
    by_contra hlt
    rw [mem_Ici, not_le] at hlt
    have := uAiry_antitoneOn hc_pos htW.1.le hB_pos.le hlt.le
    linarith
  have h_pt : ∀ t ∈ W n,
      (t - tStar n) ^ 2 * spectralWeight prob (c n) t ≤
        (C_d ^ 2 / (jac_lo * m_low)) * (c n) ^ ((2 : ℝ) / 3) * (gs0 n t / (2 * Real.pi)) := by
    intro t htW
    have ht_pos : 0 < t := htW.1
    have hu_win : |uAiry (c n) t| ≤ M_win := by
      have := abs_le.mp htW.2
      dsimp [M_win]; exact abs_le.mpr ⟨by linarith [neg_abs_le (CD.z k)], by linarith [le_abs_self (CD.z k)]⟩
    obtain ⟨_, hΔt, herrt⟩ := hC_ut hcut ht_pos hu_win
    let u := chartUT (c n) t
    have hu_close : |u - CD.z k| ≤ r + pad / 2 := by
      have h1 := abs_le.mp htW.2
      have h2 := abs_lt.mp (herrt.trans_lt hCut)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hu_vac : |u| ≤ virasoroAC (c n) ^ 2 := by
      have h1 := abs_le.mp hu_close
      exact (abs_le.mpr ⟨by linarith [neg_abs_le (CD.z k)], by linarith [le_abs_self (CD.z k)]⟩).trans
        ((show |CD.z k| + (r + pad / 2) ≤ R_c by dsimp [R_c, M_win]; linarith).trans hVac)
    have ht_diff_sq : (t - tStar n) ^ 2 ≤ (C_d * (c n) ^ ((1 : ℝ) / 3)) ^ 2 * (u - uS) ^ 2 := by
      have h_abs : |t - tStar n| ≤ C_d * (c n) ^ ((1 : ℝ) / 3) * |u - uS| := by
        rcases le_total u uS with hle | hge
        · have hm := (hmv_bds hc_pos hu_vac huS_vac hle).2
          rw [hΔt, hΔS] at hm
          rw [abs_of_nonneg (sub_nonneg.mpr (by
            by_contra hlt; push Not at hlt
            have := (hmv_bds hc_pos hu_vac huS_vac hle).1
            rw [hΔt, hΔS] at this
            have hc13_nn : 0 ≤ (cStar / 2) * (c n) ^ ((1 : ℝ) / 3) := by have := cStar_pos; positivity
            linarith [mul_nonneg hc13_nn (sub_nonneg.mpr hle)])),
            abs_of_nonpos (sub_nonpos.mpr hle)]
          linarith
        · have hm := (hmv_bds hc_pos huS_vac hu_vac hge).2
          rw [hΔS, hΔt] at hm
          rw [abs_of_nonpos (sub_nonpos.mpr (by
            have h1 := (hmv_bds hc_pos huS_vac hu_vac hge).1
            rw [hΔS, hΔt] at h1
            have hc13_nn : 0 ≤ (cStar / 2) * (c n) ^ ((1 : ℝ) / 3) := by have := cStar_pos; positivity
            linarith [mul_nonneg hc13_nn (sub_nonneg.mpr hge)])),
            abs_of_nonneg (sub_nonneg.mpr hge)]
          linarith
      calc (t - tStar n) ^ 2 = |t - tStar n| ^ 2 := (sq_abs _).symm
        _ ≤ (C_d * (c n) ^ ((1 : ℝ) / 3) * |u - uS|) ^ 2 :=
            sq_le_sq' (by linarith [abs_nonneg (t - tStar n), (by positivity : 0 ≤ C_d * (c n) ^ ((1 : ℝ) / 3) * |u - uS|)]) h_abs
        _ = (C_d * (c n) ^ ((1 : ℝ) / 3)) ^ 2 * (u - uS) ^ 2 := by rw [mul_pow, sq_abs]
    have hψ_lb : m_low * (u - uS) ^ 2 ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re := by
      by_cases hloc : u ∈ Ioo (CD.z k - r_loc) (CD.z k + r_loc)
      · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
          (hquad_loc u ⟨hloc.1.le, hloc.2.le⟩)
      · have hu_K : u ∈ K_ann := ⟨⟨by linarith [(abs_le.mp hu_close).1], by linarith [(abs_le.mp hu_close).2]⟩, hloc⟩
        have hG_lb := hδK_lb u hu_K
        have hu_cb : (u : ℂ) ∈ closedBall (0 : ℂ) R_c := by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          have h1 := abs_le.mp hu_close
          exact abs_le.mpr ⟨by linarith [neg_abs_le (CD.z k)], by linarith [le_abs_self (CD.z k)]⟩
        have hdist : dist (normProfile H.G (u : ℂ)) (psiTilde prob (c n) (gs0 n) (u : ℂ)) < δ_K / 2 :=
          hU0 (u : ℂ) hu_cb
        rw [dist_eq_norm] at hdist
        have hre := (Complex.abs_re_le_norm _).trans hdist.le
        rw [Complex.sub_re] at hre
        have hψ_ge : δ_K / 2 ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re := by linarith [(abs_le.mp hre).2]
        have hu_diff_bd : (u - uS) ^ 2 ≤ (2 * (r + pad)) ^ 2 := by
          have h1 := abs_le.mp hu_close
          have h2 := abs_lt.mp huS_pad
          exact sq_le_sq' (by linarith) (by linarith)
        have hmul_le : (δ_K / (2 * (2 * (r + pad)) ^ 2)) * (u - uS) ^ 2 ≤ δ_K / 2 := by
          have hden : 0 < 2 * (r + pad) := by positivity
          calc (δ_K / (2 * (2 * (r + pad)) ^ 2)) * (u - uS) ^ 2
              ≤ (δ_K / (2 * (2 * (r + pad)) ^ 2)) * (2 * (r + pad)) ^ 2 :=
                mul_le_mul_of_nonneg_left hu_diff_bd (by positivity)
            _ = δ_K / 2 := by field_simp [hden.ne']
        exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (hmul_le.trans hψ_ge)
    have hgs_eq := gs_div_two_pi_eq_jacRatio prob hc_pos hsh12 ht_pos hwe.1 hwe.2.1 hu_vac hΔt
    have hjac := (hjac_bds hjac_c ht_pos hu_win hu_vac).1
    have hsw_pos : 0 < spectralWeight prob (c n) t := spectralWeight_pos hc_pos hsh12 ht_pos
    have hrpow_sq : ((c n) ^ ((1 : ℝ) / 3)) ^ 2 = (c n) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast ((c n) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hc_pos.le]
      norm_num
    rw [hgs_eq]
    have h1 : (u - uS) ^ 2 ≤ (1 / (jac_lo * m_low)) * (jacRatio (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re) := by
      have hψ_nn : 0 ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re :=
        (mul_nonneg hmlow_pos.le (sq_nonneg _)).trans hψ_lb
      have hs1 := mul_le_mul hψ_lb hjac hjac_lo_pos.le hψ_nn
      calc (u - uS) ^ 2 = (m_low * (u - uS) ^ 2 * jac_lo) / (jac_lo * m_low) := by
            field_simp [hjac_lo_pos.ne', hmlow_pos.ne']
        _ ≤ ((psiTilde prob (c n) (gs0 n) (u : ℂ)).re * jacRatio (c n) t) / (jac_lo * m_low) :=
            div_le_div_of_nonneg_right hs1 (mul_pos hjac_lo_pos hmlow_pos).le
        _ = (1 / (jac_lo * m_low)) * (jacRatio (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re) := by ring
    calc (t - tStar n) ^ 2 * spectralWeight prob (c n) t
        ≤ ((C_d * (c n) ^ ((1 : ℝ) / 3)) ^ 2 * (u - uS) ^ 2) * spectralWeight prob (c n) t :=
          mul_le_mul_of_nonneg_right ht_diff_sq hsw_pos.le
      _ = C_d ^ 2 * (c n) ^ ((2 : ℝ) / 3) * spectralWeight prob (c n) t * (u - uS) ^ 2 := by
          rw [mul_pow, hrpow_sq]; ring
      _ ≤ C_d ^ 2 * (c n) ^ ((2 : ℝ) / 3) * spectralWeight prob (c n) t *
            ((1 / (jac_lo * m_low)) * (jacRatio (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (C_d ^ 2 / (jac_lo * m_low)) * (c n) ^ ((2 : ℝ) / 3) *
            (jacRatio (c n) t * spectralWeight prob (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re) := by ring
  have hint_gs_div : IntegrableOn (fun t => gs0 n t / (2 * Real.pi)) (Ici (B n)) meas.ν :=
    hint_IciB.div_const _
  have hc13_pos : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
  have hc23_div : (c n) ^ ((2 : ℝ) / 3) / (c n) ^ ((1 : ℝ) / 3) = (c n) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_sub hc_pos]; norm_num
  calc ∫ t in W n, (t - tStar n) ^ 2 * spectralWeight prob (c n) t ∂meas.ν
      ≤ ∫ t in W n, ((C_d ^ 2 / (jac_lo * m_low)) * (c n) ^ ((2 : ℝ) / 3)) * (gs0 n t / (2 * Real.pi)) ∂meas.ν := by
        refine setIntegral_mono_on hint_W ((hint_gs_div.mono_set hW_sub_B).const_mul _) hW_meas
          (fun t ht => by simpa [mul_assoc] using h_pt t ht)
    _ = ((C_d ^ 2 / (jac_lo * m_low)) * (c n) ^ ((2 : ℝ) / 3)) *
          ∫ t in W n, gs0 n t / (2 * Real.pi) ∂meas.ν := integral_const_mul _ _
    _ ≤ ((C_d ^ 2 / (jac_lo * m_low)) * (c n) ^ ((2 : ℝ) / 3)) *
          ∫ t in Ici (B n), gs0 n t / (2 * Real.pi) ∂meas.ν := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hint_gs_div ?_
          (Eventually.of_forall hW_sub_B)) (by positivity)
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact div_nonneg (hwe.2.2.2 t (Or.inr ht)) Real.two_pi_pos.le
    _ ≤ ((C_d ^ 2 / (jac_lo * m_low)) * (c n) ^ ((2 : ℝ) / 3)) * (C_pos * η n / (c n) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left h_gs_int (by positivity)
    _ = ((C_d ^ 2 / (jac_lo * m_low)) * C_pos) * (c n) ^ ((1 : ℝ) / 3) * η n := by
        calc ((C_d ^ 2 / (jac_lo * m_low)) * (c n) ^ ((2 : ℝ) / 3)) * (C_pos * η n / (c n) ^ ((1 : ℝ) / 3))
            = ((C_d ^ 2 / (jac_lo * m_low)) * C_pos) * ((c n) ^ ((2 : ℝ) / 3) / (c n) ^ ((1 : ℝ) / 3)) * η n := by ring
          _ = ((C_d ^ 2 / (jac_lo * m_low)) * C_pos) * (c n) ^ ((1 : ℝ) / 3) * η n := by rw [hc23_div]
    _ ≤ C_kr * (c n) ^ ((1 : ℝ) / 3) * η n := by
        rw [mul_assoc, mul_assoc C_kr]
        exact mul_le_mul_of_nonneg_right (by dsimp [C_kr]; linarith) (mul_nonneg hc13_pos.le hnn)

/-- Off-node compact normalised mass bound (`dsl:hb-mass`, third clause):
for any compact set `K_off ⊆ [CD.a, CD.b]` avoiding all limit nodes `{CD.z k}`,
near-optimal crossing measures `ν_n` satisfy
`spectralMeasure prob c_n ν_n K_off ≤ C_K η_n / c_n^{1/3}`. -/
theorem hb_mass_off_node (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    (CD : HbClusterData H) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    (hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 H.tm))
    {η : ℕ → ℝ} (hη_nn : ∀ᶠ n in atTop, 0 ≤ η n)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0))
    (hvag_near : ∀ (ν_seq : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0) →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo CD.a CD.b →
        Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k))))
    {K_off : Set ℝ} (hK_comp : IsCompact K_off) (hK_sub : K_off ⊆ Icc CD.a CD.b)
    (hK_disj : ∀ k : Fin CD.K, CD.z k ∉ K_off) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0 →
        spectralMeasure prob (c n) meas.ν K_off < ⊤ ∧
        (spectralMeasure prob (c n) meas.ν K_off).toReal ≤ C_K * η n / (c n) ^ ((1 : ℝ) / 3) := by
  classical
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let F : ℕ → Set ℝ := hbPrescribedSet s
  have hδ_ex : ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ K_off, ∀ k : Fin CD.K, δ ≤ |u - CD.z k| := by
    by_cases hne : K_off.Nonempty
    · have hk_ex : ∀ k : Fin CD.K, ∃ δk : ℝ, 0 < δk ∧ ∀ u ∈ K_off, δk ≤ |u - CD.z k| := fun k => by
        obtain ⟨u0, hu0, hmin⟩ := hK_comp.exists_isMinOn hne (continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn
        refine ⟨|u0 - CD.z k|, abs_pos.mpr (sub_ne_zero.mpr fun heq => hK_disj k (heq ▸ hu0)), fun u hu => hmin hu⟩
      choose δk hδk_pos hδk_lb using hk_ex
      have hne_fin : (Finset.univ : Finset (Fin CD.K)).Nonempty := ⟨⟨0, CD.hK⟩, Finset.mem_univ _⟩
      let S_d := (Finset.univ : Finset (Fin CD.K)).image δk
      refine ⟨S_d.min' (hne_fin.image _), ?_, fun u hu k => ?_⟩
      · obtain ⟨k, _, hk_eq⟩ := Finset.mem_image.mp (Finset.min'_mem S_d _)
        rw [← hk_eq]; exact hδk_pos k
      · exact (Finset.min'_le S_d _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))).trans (hδk_lb k u hu)
    · exact ⟨1, zero_lt_one, fun u hu => absurd ⟨u, hu⟩ hne⟩
  obtain ⟨δ, hδ_pos, hδ_sep⟩ := hδ_ex
  let K_left : Set ℝ := K_off ∩ Iic (H.tm - δ / 2)
  have hKl_comp : IsCompact K_left := hK_comp.inter_right isClosed_Iic
  have hKl_pos : ∀ u ∈ K_left, 0 < (normProfile H.G (u : ℂ)).re := fun u hu =>
    normProfile_re_pos_of_mem_Icc H CD (hK_sub hu.1) (by linarith [mem_Iic.mp hu.2])
      fun k h_eq => hK_disj k (h_eq ▸ hu.1)
  obtain ⟨δ_G, hδG_pos, hδG_lb⟩ := compact_pos_lower_bound H hKl_comp hKl_pos
  let M_K : ℝ := max |CD.a| |CD.b|
  let R_c : ℝ := M_K + 2
  have hM_K : 0 ≤ M_K := by positivity
  let f_re : ℝ → ℝ := fun u => (normProfile H.G (u : ℂ)).re
  have hf_uc : UniformContinuousOn f_re (Icc (-R_c) R_c) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (Complex.continuous_re.comp ((normProfile_differentiable (hbExtremalProfile H)).continuous.comp Complex.continuous_ofReal)).continuousOn
  obtain ⟨η_uc, hηuc_pos, hη_uc⟩ := Metric.uniformContinuousOn_iff.mp hf_uc (δ_G / 2) (half_pos hδG_pos)
  let pad : ℝ := min 1 (min (η_uc / 2) (δ / 4))
  have hpad_pos : 0 < pad := by positivity
  obtain ⟨gs0, hgs0_we, hgs0_B, hDiff, hUnif0, _, _⟩ :=
    canonical_psiTilde_converges prob H hc hs_pos hs_tend hB_tend (R := R_c) (by positivity)
  obtain ⟨C_pos, _, h_near⟩ :=
    near_opt_extremal_le prob H CD hc hs_pos hs_tend hB_tend hη_nn hη_o hvag_near hgs0_we hgs0_B
  obtain ⟨jac_c0, jac_lo, _, _, hjac_lo_pos, _, hjac_bds⟩ := jacRatio_bounds hM_K
  obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err hM_K
  obtain ⟨t_c0, _, ht_bds⟩ := uAiry_window_t_bounds hM_K
  let c_off : ℝ := δ_G / 4
  have hcoff_pos : 0 < c_off := by positivity
  let C_K : ℝ := C_pos / (jac_lo * c_off) + 1
  refine ⟨C_K, by positivity, ?_⟩
  obtain ⟨hu_shift, hBη_tend_pos⟩ := uAiry_sub_shift_tendsto hc hB_tend hη_nn hη_o
  have hs_close : ∀ᶠ n in atTop, ∀ i : HbNodes H, |uAiry (c n) (s i n) - i.1| < δ / 2 := by
    rw [eventually_all]
    exact fun i => (hs_tend i).eventually (Metric.ball_mem_nhds i.1 (half_pos hδ_pos))
  have hCerr : ∀ᶠ n in atTop, C_ut * (c n) ^ (-(2 / 3 : ℝ)) < pad := by
    have h0 : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_ut
    exact h0.eventually (gt_mem_nhds hpad_pos)
  rw [Metric.tendstoUniformlyOn_iff] at hUnif0
  filter_upwards [h_near, hgs0_we, hDiff, hUnif0 (δ_G / 4) (by positivity),
    hs_close, hBη_tend_pos, hu_shift.eventually (Metric.ball_mem_nhds H.tm (half_pos hδ_pos)),
    hB_tend.eventually (Metric.ball_mem_nhds H.tm (div_pos hδ_pos (by norm_num : (0 : ℝ) < 4))),
    eventually_pos_of_uAiry_tendsto hc hB_tend,
    hCerr, hc.eventually_ge_atTop (max jac_c0 (max c_ut (max t_c0 (max 1 (12 * prob.totalShift))))),
    virasoroAC_sq_eventually_ge hc R_c, hη_nn]
    with n hnear hwe hDiffn hU0 hsc hBη_pos hBηu hBu hB_pos hCut hc_ge hVac hnn meas hν
  have hc_pos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))))
  have hsh12 : prob.totalShift ≤ c n / 12 := by
    have := (le_max_right 1 _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))); linarith
  have hjac_c : jac_c0 ≤ c n := (le_max_left _ _).trans hc_ge
  have hcut : c_ut ≤ c n := (le_max_left _ _).trans ((le_max_right _ _).trans hc_ge)
  have htc : t_c0 ≤ c n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge))
  obtain ⟨hint_IciB, _, h_gs_int⟩ := hnear meas hν
  let t_lo := c n * (xiStar / 2) ^ 2 / 3
  let t_hi := c n * (3 * xiStar / 2) ^ 2 / 3
  have ht_lo_pos : 0 < t_lo := by have := xiStar_pos; positivity
  let PreK : Set ℝ := uAiry (c n) ⁻¹' K_off ∩ Ioi (0 : ℝ)
  have hPreK_meas : MeasurableSet PreK :=
    ((continuous_uAiry (c n)).measurable hK_comp.isClosed.measurableSet).inter measurableSet_Ioi
  have hPreK_sub : PreK ⊆ Icc t_lo t_hi := fun t ⟨htK, htpos⟩ => by
    have hu_ab := hK_sub htK
    have hu_win : |uAiry (c n) t| ≤ M_K := abs_le.mpr
      ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hu_ab.1],
       by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hu_ab.2]⟩
    exact ht_bds htc htpos hu_win
  have ht_le : t_lo ≤ t_hi := by
    have hxi := xiStar_pos
    dsimp [t_lo, t_hi]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sq_le_sq' (by linarith) (by linarith)) hc_pos.le) (by norm_num)
  have hint_PreK : IntegrableOn (spectralWeight prob (c n)) PreK meas.ν := by
    simpa using integrableOn_spectralWeight_mul_of_continuousOn prob hc_pos hsh12 ht_lo_pos ht_le meas
      hPreK_meas hPreK_sub (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) _)
  have hsm_eq : spectralMeasure prob (c n) meas.ν K_off =
      ENNReal.ofReal (∫ t in PreK, spectralWeight prob (c n) t ∂meas.ν) := by
    unfold spectralMeasure
    rw [Measure.map_apply (continuous_uAiry (c n)).measurable hK_comp.isClosed.measurableSet,
      withDensity_apply _ ((continuous_uAiry (c n)).measurable hK_comp.isClosed.measurableSet),
      Measure.restrict_restrict ((continuous_uAiry (c n)).measurable hK_comp.isClosed.measurableSet)]
    refine (ofReal_integral_eq_lintegral_ofReal hint_PreK ?_).symm
    filter_upwards [ae_restrict_mem hPreK_meas] with t ht
    exact (spectralWeight_pos hc_pos hsh12 ht.2).le
  have hsm_lt : spectralMeasure prob (c n) meas.ν K_off < ⊤ := by
    rw [hsm_eq]; exact ENNReal.ofReal_lt_top
  refine ⟨hsm_lt, ?_⟩
  rw [hsm_eq, ENNReal.toReal_ofReal (setIntegral_nonneg hPreK_meas fun t ht =>
    (spectralWeight_pos hc_pos hsh12 ht.2).le)]
  have hsupp_ae : ∀ᵐ t ∂meas.ν, t ∈ F n ∪ Ici (B n - η n) := by
    have := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with t ht using notMem_compl_iff.1 ht
  have h_ae : ∀ᵐ t ∂meas.ν, t ∈ PreK →
      t ∈ Ici (B n) ∧
      spectralWeight prob (c n) t ≤ (1 / (jac_lo * c_off)) * (gs0 n t / (2 * Real.pi)) := by
    filter_upwards [hsupp_ae] with t ht_supp ⟨htK, ht_pos⟩
    have ht_notF : t ∉ F n := by
      rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := CD.hS_sub i.1 i.2.1
      have h1 := hδ_sep (uAiry (c n) (s i n)) htK k
      have h2 := hsc i
      rw [← hk] at h1
      linarith [abs_lt.mp h2]
    have ht_geBη : B n - η n ≤ t := by
      rcases ht_supp with hF | hIci
      · exact absurd hF ht_notF
      · exact hIci
    have hu_le_Bη : uAiry (c n) t ≤ uAiry (c n) (B n - η n) :=
      uAiry_antitoneOn hc_pos hBη_pos.le ht_pos.le ht_geBη
    have hBη_lt : uAiry (c n) (B n - η n) < H.tm + δ / 2 := by
      have := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hBηu :
        |uAiry (c n) (B n - η n) - H.tm| < δ / 2)
      linarith
    obtain ⟨m_tm, hm_tm⟩ := CD.hS_sub H.tm H.tm_mem
    have hu_sep_tm : δ ≤ |uAiry (c n) t - H.tm| := by rw [hm_tm]; exact hδ_sep _ htK m_tm
    have hu_le_tm : uAiry (c n) t ≤ H.tm - δ := by
      rcases le_or_gt (uAiry (c n) t) H.tm with hle | hgt
      · rw [abs_of_nonpos (by linarith)] at hu_sep_tm; linarith
      · rw [abs_of_pos (by linarith)] at hu_sep_tm; linarith
    have hu_Kl : uAiry (c n) t ∈ K_left := ⟨htK, show uAiry (c n) t ≤ H.tm - δ / 2 by linarith⟩
    have hu_lt_B : B n < t := by
      have hBu_ge : H.tm - δ / 4 < uAiry (c n) (B n) := by
        have := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hBu : |uAiry (c n) (B n) - H.tm| < δ / 4)
        linarith
      by_contra hle; push Not at hle
      have := uAiry_antitoneOn hc_pos ht_pos.le hB_pos.le hle
      linarith
    have hu_win : |uAiry (c n) t| ≤ M_K := abs_le.mpr
      ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, (hK_sub htK).1],
       by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, (hK_sub htK).2]⟩
    obtain ⟨_, hΔt, herrt⟩ := hC_ut hcut ht_pos hu_win
    let u := chartUT (c n) t
    have hu_err : |u - uAiry (c n) t| < pad := by rw [abs_sub_comm]; exact herrt.trans_lt hCut
    have hu_Icc : u ∈ Icc (-R_c) R_c := by
      have h1 := abs_le.mp hu_win; have h2 := abs_lt.mp hu_err
      exact ⟨by dsimp [R_c]; linarith [min_le_left 1 (min (η_uc / 2) (δ / 4))],
        by dsimp [R_c]; linarith [min_le_left 1 (min (η_uc / 2) (δ / 4))]⟩
    have hu0_Icc : uAiry (c n) t ∈ Icc (-R_c) R_c := by
      have h1 := abs_le.mp hu_win
      exact ⟨by dsimp [R_c]; linarith, by dsimp [R_c]; linarith⟩
    have hdist_uc : dist u (uAiry (c n) t) < η_uc := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (hu_err.le.trans ((min_le_right _ _).trans (min_le_left _ _)))
        (half_lt_self hηuc_pos)
    have hf_diff := hη_uc u hu_Icc (uAiry (c n) t) hu0_Icc hdist_uc
    rw [Real.dist_eq] at hf_diff
    have hG_u : δ_G / 2 ≤ (normProfile H.G (u : ℂ)).re := by
      have h1 := hδG_lb _ hu_Kl
      have h2 := (abs_lt.mp hf_diff).1
      dsimp [f_re] at h2; linarith
    have hu_cb : (u : ℂ) ∈ closedBall (0 : ℂ) R_c := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr hu_Icc
    have hdist : dist (normProfile H.G (u : ℂ)) (psiTilde prob (c n) (gs0 n) (u : ℂ)) < δ_G / 4 :=
      hU0 (u : ℂ) hu_cb
    rw [dist_eq_norm] at hdist
    have hre := (Complex.abs_re_le_norm _).trans hdist.le
    rw [Complex.sub_re] at hre
    have hψ_ge : c_off ≤ (psiTilde prob (c n) (gs0 n) (u : ℂ)).re := by
      dsimp [c_off]; linarith [(abs_le.mp hre).2]
    have hu_vac : |u| ≤ virasoroAC (c n) ^ 2 := (abs_le.mpr hu_Icc).trans hVac
    have hgs_eq := gs_div_two_pi_eq_jacRatio prob hc_pos hsh12 ht_pos hwe.1 hwe.2.1 hu_vac hΔt
    have hjac := (hjac_bds hjac_c ht_pos hu_win hu_vac).1
    have hsw_pos : 0 < spectralWeight prob (c n) t := spectralWeight_pos hc_pos hsh12 ht_pos
    refine ⟨hu_lt_B.le, ?_⟩
    rw [hgs_eq]
    have hprod : jac_lo * c_off ≤ jacRatio (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re :=
      mul_le_mul hjac hψ_ge hcoff_pos.le (lt_of_lt_of_le hjac_lo_pos hjac).le
    calc spectralWeight prob (c n) t
        = (jac_lo * c_off) * spectralWeight prob (c n) t / (jac_lo * c_off) := by
          field_simp [hjac_lo_pos.ne', hcoff_pos.ne']
      _ ≤ (jacRatio (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re) *
            spectralWeight prob (c n) t / (jac_lo * c_off) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hprod hsw_pos.le) (by positivity)
      _ = (1 / (jac_lo * c_off)) *
            (jacRatio (c n) t * spectralWeight prob (c n) t * (psiTilde prob (c n) (gs0 n) (u : ℂ)).re) := by ring
  have hint_PreK_Ici : IntegrableOn (spectralWeight prob (c n)) (PreK ∩ Ici (B n)) meas.ν :=
    hint_PreK.mono_set Set.inter_subset_left
  have hint_gs_div : IntegrableOn (fun t => gs0 n t / (2 * Real.pi)) (Ici (B n)) meas.ν :=
    hint_IciB.div_const _
  have h_eq_inter : ∫ t in PreK, spectralWeight prob (c n) t ∂meas.ν =
      ∫ t in PreK ∩ Ici (B n), spectralWeight prob (c n) t ∂meas.ν := by
    have hunion : PreK = (PreK ∩ Ici (B n)) ∪ (PreK ∩ (Ici (B n))ᶜ) :=
      (Set.inter_union_compl PreK (Ici (B n))).symm
    have hdisj : Disjoint (PreK ∩ Ici (B n)) (PreK ∩ (Ici (B n))ᶜ) :=
      disjoint_compl_right.mono Set.inter_subset_right Set.inter_subset_right
    have hint2 : IntegrableOn (spectralWeight prob (c n)) (PreK ∩ (Ici (B n))ᶜ) meas.ν :=
      hint_PreK.mono_set Set.inter_subset_left
    have hzero : ∫ t in PreK ∩ (Ici (B n))ᶜ, spectralWeight prob (c n) t ∂meas.ν = 0 := by
      refine integral_eq_zero_of_ae ?_
      change ∀ᵐ t ∂(meas.ν.restrict (PreK ∩ (Ici (B n))ᶜ)), spectralWeight prob (c n) t = 0
      rw [ae_restrict_iff' (hPreK_meas.inter measurableSet_Ici.compl)]
      filter_upwards [h_ae] with t ht ⟨htP, htNot⟩
      exact absurd (ht htP).1 htNot
    conv_lhs => rw [hunion]
    rw [setIntegral_union hdisj (hPreK_meas.inter measurableSet_Ici.compl) hint_PreK_Ici hint2, hzero, add_zero]
  rw [h_eq_inter]
  have hle_PI : ∫ t in PreK ∩ Ici (B n), spectralWeight prob (c n) t ∂meas.ν ≤
      (1 / (jac_lo * c_off)) * ∫ t in PreK ∩ Ici (B n), gs0 n t / (2 * Real.pi) ∂meas.ν := by
    rw [← integral_const_mul]
    refine setIntegral_mono_ae_restrict hint_PreK_Ici ((hint_gs_div.mono_set Set.inter_subset_right).const_mul _) ?_
    change ∀ᵐ t ∂(meas.ν.restrict (PreK ∩ Ici (B n))),
      spectralWeight prob (c n) t ≤ (1 / (jac_lo * c_off)) * (gs0 n t / (2 * Real.pi))
    rw [ae_restrict_iff' (hPreK_meas.inter measurableSet_Ici)]
    filter_upwards [h_ae] with t ht ⟨htP, _⟩
    exact (ht htP).2
  have hc13_pos : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
  have hηc_nn : 0 ≤ η n / (c n) ^ ((1 : ℝ) / 3) := div_nonneg hnn hc13_pos.le
  calc ∫ t in PreK ∩ Ici (B n), spectralWeight prob (c n) t ∂meas.ν
      ≤ (1 / (jac_lo * c_off)) * ∫ t in PreK ∩ Ici (B n), gs0 n t / (2 * Real.pi) ∂meas.ν := hle_PI
    _ ≤ (1 / (jac_lo * c_off)) * ∫ t in Ici (B n), gs0 n t / (2 * Real.pi) ∂meas.ν := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hint_gs_div ?_
          (Eventually.of_forall Set.inter_subset_right)) (by positivity)
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact div_nonneg (hwe.2.2.2 t (Or.inr ht)) Real.two_pi_pos.le
    _ ≤ (1 / (jac_lo * c_off)) * (C_pos * η n / (c n) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left h_gs_int (by positivity)
    _ = (C_pos / (jac_lo * c_off)) * (η n / (c n) ^ ((1 : ℝ) / 3)) := by ring
    _ ≤ C_K * η n / (c n) ^ ((1 : ℝ) / 3) := by
        rw [show C_K * η n / (c n) ^ ((1 : ℝ) / 3) = C_K * (η n / (c n) ^ ((1 : ℝ) / 3)) by ring]
        dsimp [C_K]; nlinarith

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.hb_mass_first_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.hb_mass_first_moment

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.hb_mass_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.hb_mass_second_moment

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.hb_mass_off_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.hb_mass_off_node

end FormalResearch.ModularBootstrap.FixedWeight
