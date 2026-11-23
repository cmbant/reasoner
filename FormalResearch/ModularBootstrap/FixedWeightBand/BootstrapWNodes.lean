module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWBand

/-!
# Node-Sum Lower Bounds (`hP_nodes_lb_hb`, `P_theta_bound`) at Every Fixed `(w, Q)`

Source: `CFT/common/two_edge_bootstrap.tex` (`teb:bootstrap`, hypotheses `hP_nodes_lb_hb`, `P_theta_bound`)
and `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Step 2.

* `pnodes_lower_auxW`, `pnodes_lb_and_thetaW`: for the good-circle node sum
  `P_nodes = ∑_n Re f_{k,ℓ}(a_n)/Ai'(a_n)²` of the shifted test of `psiTilde prob`, the lower bound from the
  positive weights `Ψ̃(a_n + ℓ) ≥ 0` for zeros `a_n` right of `u_T` and the identity for the `θ`-term
  (the Virasoro `virasoro_pnodes_lb_and_theta`; constants from `Lemma Q (3)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip

variable {prob : FixedWeightProblem} [Q : LemmaQData prob]

private lemma psiTilde_real_mv_sub {c' R_dom : ℝ} {g : ℝ → ℝ}
    (hΨ_an : AnalyticOnNhd ℂ (psiTilde prob c' g) (closedBall (0 : ℂ) R_dom))
    (_hΨ_real : ∀ x ∈ Icc (-R_dom) R_dom, (psiTilde prob c' g (x : ℂ)).im = 0)
    {a b : ℝ} (hab : a ≤ b) (ha : -R_dom ≤ a) (hb : b ≤ R_dom) (C₁ : ℝ) (_hC1_nn : 0 ≤ C₁)
    (hder : ∀ x ∈ Icc a b, ‖deriv (psiTilde prob c' g) (x : ℂ)‖ ≤ C₁) :
    |(psiTilde prob c' g (b : ℂ)).re - (psiTilde prob c' g (a : ℂ)).re| ≤ C₁ * (b - a) := by
  have hΨ_diff : ∀ t ∈ Icc a b,
      HasDerivAt (fun x : ℝ => (psiTilde prob c' g (x : ℂ)).re)
        ((deriv (psiTilde prob c' g) (t : ℂ)).re) t := by
    intro t ht
    have ht_ball : (t : ℂ) ∈ closedBall (0 : ℂ) R_dom := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc : HasDerivAt (psiTilde prob c' g) (deriv (psiTilde prob c' g) (t : ℂ)) (t : ℂ) :=
      (hΨ_an (t : ℂ) ht_ball).differentiableAt.hasDerivAt
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc.comp_ofReal
  have hcont_der : ContinuousOn (fun t : ℝ => (deriv (psiTilde prob c' g) (t : ℂ)).re) (Icc a b) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine hΨ_an.deriv.continuousOn.comp continuous_ofReal.continuousOn fun t ht => ?_
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hftc : (psiTilde prob c' g (b : ℂ)).re - (psiTilde prob c' g (a : ℂ)).re =
      ∫ t in a..b, (deriv (psiTilde prob c' g) (t : ℂ)).re :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hΨ_diff t (Set.uIcc_of_le hab ▸ ht))
      (hcont_der.intervalIntegrable_of_Icc hab)).symm
  have h_norm := intervalIntegral.norm_integral_le_integral_norm
    (f := fun t : ℝ => (deriv (psiTilde prob c' g) (t : ℂ)).re) (μ := volume) hab
  rw [← hftc, Real.norm_eq_abs] at h_norm
  have hint_bd : ∫ t in a..b, ‖(deriv (psiTilde prob c' g) (t : ℂ)).re‖ ≤
      ∫ _ in a..b, C₁ := by
    refine intervalIntegral.integral_mono_on hab
      ((continuous_norm.comp_continuousOn hcont_der).intervalIntegrable_of_Icc hab)
      (intervalIntegrable_const) fun t ht => ?_
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hder t ht)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint_bd
  have hle : |(psiTilde prob c' g (b : ℂ)).re - (psiTilde prob c' g (a : ℂ)).re| ≤
      (b - a) * C₁ := h_norm.trans hint_bd
  linarith [hle]

private lemma pnodes_lower_auxW {c' R T ℓ : ℝ} {N : ℕ}
    (hc' : Q.cQ ≤ c') (hR_48 : 48 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr))
    (hT_A2 : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (psiTilde prob c' g) (virasoroUT c' T))
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R))
    (hℓ_nn : 0 ≤ ℓ) (hℓ_le : ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1))
    (k : ℕ) (_hk_ub : (k : ℝ) ≤ R / 5) :
    (1 + airyZero 1 / R) ^ (k + 1) *
        (psiTilde prob c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re / quantC1WStar ≤
      pNodesW prob c' R ℓ g k N := by
  have hc'_10000 : 10000 ≤ c' :=
    (Q.hcQ_10000.trans hc')
  have hc'_pos : 0 < c' := by linarith
  have hR_pos : 0 < R := by linarith
  have hA2_nn : 0 ≤ Q.AC c' ^ 2 := sq_nonneg _
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  obtain ⟨ha2_lo, ha2_hi⟩ := airyZero_two
  have hAThr_eq : virasoroAThr = -airyZero 1 + 1 := by
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]
  have hu_mem := Q.UT_between hc'_pos
    (by linarith : -(Q.AC c' ^ 2) ≤ -virasoroAThr)
    (le_rfl : Q.AC c' ^ 2 ≤ Q.AC c' ^ 2)
    (by linarith : -virasoroAThr ≤ Q.AC c' ^ 2) hT_A2 hT_hi
  set u_T := virasoroUT c' T
  have ha1_lt_uT : airyZero 1 < u_T := by
    by_contra hle
    have := (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu_mem.1.1], hu_mem.1.2⟩ ⟨by linarith, by linarith⟩ (not_lt.mp hle)
    linarith [hT_a1, hu_mem.2]
  have huT_le_a1_half : u_T ≤ airyZero 1 + 1 / 2 := by
    have h1 := hB2.1
    have h2 : min quantC1DeltaStar (min quantC1Eta0 1) ≤ 1 / 2 :=
      (min_le_left _ _).trans quantC1DeltaStar_le
    linarith
  have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 N := by
    rw [Finset.mem_Icc]
    refine ⟨le_rfl, (hN 1 le_rfl).mpr (by linarith)⟩
  have h_sum_split : pNodesW prob c' R ℓ g k N =
      (shiftedFunW prob c' R ℓ g k (airyZero 1 : ℂ)).re / airyAi' (airyZero 1) ^ 2 +
      ∑ n ∈ (Finset.Icc 1 N).erase 1,
        (shiftedFunW prob c' R ℓ g k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2 := by
    unfold pNodesW
    exact (Finset.add_sum_erase _ _ h1_mem).symm
  have h_tail_nn : 0 ≤ ∑ n ∈ (Finset.Icc 1 N).erase 1,
      (shiftedFunW prob c' R ℓ g k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2 := by
    refine Finset.sum_nonneg fun n hn => ?_
    rw [Finset.mem_erase, Finset.mem_Icc] at hn
    have hn2 : 2 ≤ n := by omega
    have han_negR : -R < airyZero n := by
      have := (hN n hn.2.1).mp hn.2.2; linarith
    have han_le_a2 : airyZero n ≤ airyZero 2 :=
      airyZero_anti (by omega) (by omega : 2 ≤ n)
    have hℓ_half : ℓ ≤ 1 / 2 := hℓ_le.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
    have harg_le : airyZero n + ℓ ≤ u_T := by linarith
    have harg_abs : |airyZero n + ℓ| ≤ Q.AC c' ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hT_le_Δ : T ≤ virasoroDeltaChart c' (airyZero n + ℓ) := by
      rw [← hu_mem.2]
      exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
        (abs_le.mp harg_abs) ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2]⟩ harg_le
    have hΨ_nn : 0 ≤ (psiTilde prob c' g ((airyZero n + ℓ : ℝ) : ℂ)).re :=
      (Q.part3 hc' hg).1 (airyZero n + ℓ) harg_abs hT_le_Δ
    have hpow_nn : 0 ≤ (1 + airyZero n / R) ^ (k + 1) := by
      refine pow_nonneg ?_ _
      rw [show (1 : ℝ) + airyZero n / R = (R + airyZero n) / R by field_simp [hR_pos.ne'] ]
      exact div_nonneg (by linarith) hR_pos.le
    have hrew : (shiftedFunW prob c' R ℓ g k (airyZero n : ℂ)).re =
        (1 + airyZero n / R) ^ (k + 1) *
          (psiTilde prob c' g ((airyZero n + ℓ : ℝ) : ℂ)).re := by
      unfold shiftedFunW
      have h1 : ((1 + (airyZero n : ℂ) / (R : ℂ)) ^ (k + 1)) =
          (((1 + airyZero n / R) ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [h1, show (airyZero n : ℂ) + (ℓ : ℂ) = ((airyZero n + ℓ : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [hrew]
    exact div_nonneg (mul_nonneg hpow_nn hΨ_nn) (sq_nonneg _)
  have h1_rew : (shiftedFunW prob c' R ℓ g k (airyZero 1 : ℂ)).re / airyAi' (airyZero 1) ^ 2 =
      (1 + airyZero 1 / R) ^ (k + 1) *
        (psiTilde prob c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re / quantC1WStar := by
    unfold shiftedFunW quantC1WStar
    have h1 : ((1 + (airyZero 1 : ℂ) / (R : ℂ)) ^ (k + 1)) =
        (((1 + airyZero 1 / R) ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, show (airyZero 1 : ℂ) + (ℓ : ℂ) = ((airyZero 1 + ℓ : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  linarith [h_sum_split, h_tail_nn, h1_rew]

lemma pnodes_lb_and_thetaW {c' R T : ℝ} {N : ℕ}
    (hc' : Q.cQ ≤ c') (hR_48 : 48 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr))
    (hT_A2 : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (psiTilde prob c' g) (virasoroUT c' T))
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R))
    (P : BootstrapParams)
    (hP_C1 : P.C_1 = quantC1C1) (hP_w : P.w_star = quantC1WStar)
    (hP_κ : P.κ_star = quantC1KappaStar) (hP_δ : P.δ_star = quantC1DeltaStar)
    (hP_η : P.η_0 = quantC1Eta0) (hP_k0 : P.k_0 = 5) :
    (∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
      ℓ ∈ Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      -tebLambdaN P 0 * ℓ - P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤ pNodesW prob c' R ℓ g k N) ∧
    ((P.k_0 : ℝ) ≤ R / 5 →
      tebThetaHB P 0 * (virasoroUT c' T - airyZero 1) ∈
        Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      (P.κ_star / (4 * P.w_star)) * (virasoroUT c' T - airyZero 1) -
        P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤
        pNodesW prob c' R (tebThetaHB P 0 * (virasoroUT c' T - airyZero 1)) g P.k_0 N) := by
  have hc'_10000 : 10000 ≤ c' :=
    (Q.hcQ_10000.trans hc')
  have hc'_pos : 0 < c' := by linarith
  have hR_pos : 0 < R := by linarith
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  have hAThr_eq : virasoroAThr = -airyZero 1 + 1 := by
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]
  have hu_mem := Q.UT_between hc'_pos
    (by linarith : -(Q.AC c' ^ 2) ≤ -virasoroAThr)
    (le_rfl : Q.AC c' ^ 2 ≤ Q.AC c' ^ 2)
    (by linarith : -virasoroAThr ≤ Q.AC c' ^ 2) hT_A2 hT_hi
  set u_T := virasoroUT c' T
  have ha1_lt_uT : airyZero 1 < u_T := by
    by_contra hle
    have := (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu_mem.1.1], hu_mem.1.2⟩ ⟨by linarith, by linarith⟩ (not_lt.mp hle)
    linarith [hT_a1, hu_mem.2]
  have hbase_nn : 0 ≤ 1 + airyZero 1 / R := by
    rw [show (1 : ℝ) + airyZero 1 / R = (R + airyZero 1) / R by field_simp [hR_pos.ne'] ]
    exact div_nonneg (by linarith) hR_pos.le
  have hbase_le1 : 1 + airyZero 1 / R ≤ 1 := by
    have : airyZero 1 / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hR_pos.le
    linarith
  have hΨ_an_R : AnalyticOnNhd ℂ (psiTilde prob c' g) (closedBall (0 : ℂ) (Q.AC c' ^ 2)) :=
    (Q.analytic (by linarith) hg.1).mono fun z hz =>
      Q.closedBall_subset_psiDom hc'_pos hz
  have hΨ_real_R : ∀ x ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2),
      (psiTilde prob c' g (x : ℂ)).im = 0 :=
    fun x hx => (Q.part2 hc' hg.1 (Q.cardyNorm_pos hc' hg)).2.1 x (abs_le.mpr hx) |>.1
  have ha1_abs : |airyZero 1| ≤ Q.AC c' ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hT_le_Δa1 : T ≤ virasoroDeltaChart c' (airyZero 1) := hT_a1.le
  have hΨ_a1_nn : 0 ≤ (psiTilde prob c' g (airyZero 1 : ℂ)).re :=
    (Q.part3 hc' hg).1 (airyZero 1) ha1_abs hT_le_Δa1
  refine ⟨?_, ?_⟩
  · -- `hP_nodes_lb_hb`
    intro k ℓ _ hkR hℓ_mem
    have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
    have hℓ_le' : ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1) := by
      simpa only [hP_δ, hP_η] using hℓ_mem.2
    have hℓ_δ : ℓ ≤ quantC1DeltaStar := hℓ_le'.trans (min_le_left _ _)
    have h_mv := psiTilde_real_mv_sub hΨ_an_R hΨ_real_R (a := airyZero 1) (b := airyZero 1 + ℓ)
      (by linarith) (by linarith) (by linarith [quantC1DeltaStar_le]) quantC1C1 quantC1C1_pos.le
      fun x hx => (hB2.2 x ⟨by linarith [hx.1, quantC1DeltaStar_pos], by linarith [hx.2]⟩).1
    have hΨ_lb : -quantC1C1 * ℓ ≤ (psiTilde prob c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re := by
      have h1 := (abs_le.mp h_mv).1
      linarith
    have hpow_le1 : (1 + airyZero 1 / R) ^ (k + 1) ≤ 1 := pow_le_one₀ hbase_nn hbase_le1
    have hw_pos : 0 < quantC1WStar := quantC1WStar_pos
    have hterm_lb : -(quantC1C1 / quantC1WStar) * ℓ ≤
        (1 + airyZero 1 / R) ^ (k + 1) *
          (psiTilde prob c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re / quantC1WStar := by
      have hmul : (1 + airyZero 1 / R) ^ (k + 1) * (-quantC1C1 * ℓ) ≤
          (1 + airyZero 1 / R) ^ (k + 1) *
            (psiTilde prob c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re :=
        mul_le_mul_of_nonneg_left hΨ_lb (pow_nonneg hbase_nn _)
      have h2 : -(quantC1C1 * ℓ) ≤ (1 + airyZero 1 / R) ^ (k + 1) * (-quantC1C1 * ℓ) := by
        have h3 : 0 ≤ quantC1C1 * ℓ := mul_nonneg quantC1C1_pos.le hℓ_nn
        nlinarith [hpow_le1]
      have h4 : -(quantC1C1 * ℓ) / quantC1WStar = -(quantC1C1 / quantC1WStar) * ℓ := by ring
      rw [← h4]
      exact div_le_div_of_nonneg_right (h2.trans hmul) hw_pos.le
    have hΛ_ge : quantC1C1 / quantC1WStar ≤ tebLambdaN P 0 := by
      unfold tebLambdaN
      rw [hP_C1, hP_w, add_zero]
      have : 0 ≤ quantC1C1 / quantC1WStar := div_nonneg quantC1C1_pos.le hw_pos.le
      linarith [show 2 * quantC1C1 * (1 / quantC1WStar) = 2 * (quantC1C1 / quantC1WStar) by ring]
    have h_main := pnodes_lower_auxW hc' hR_48 hR_ub hg hT_hi hT_A2 hT_a1 hB2 hN hℓ_nn hℓ_le' k hkR
    have hΛ_mul : -tebLambdaN P 0 * ℓ ≤ -(quantC1C1 / quantC1WStar) * ℓ := by nlinarith
    linarith [hΛ_mul, hterm_lb, h_main]
  · -- `P_theta_bound`
    intro hk0_R hℓ_mem
    set θ := tebThetaHB P 0
    have hθ_pos : 0 < θ := tebThetaHB_pos P le_rfl
    have hθ_half : θ ≤ 1 / 2 := tebThetaHB_le_half P 0
    have hθ_le1 : θ ≤ 1 := hθ_half.trans (by norm_num)
    have hℓ_nn : 0 ≤ θ * (u_T - airyZero 1) :=
      (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
    have hℓ_le' : θ * (u_T - airyZero 1) ≤ min quantC1DeltaStar (min quantC1Eta0 1) := by
      simpa only [hP_δ, hP_η] using hℓ_mem.2
    have hsec := quantC1B2_secant_lower (R_dom := Q.AC c' ^ 2)
      (by rw [abs_of_neg (by linarith)]; linarith) hΨ_an_R ha1_lt_uT
      ((Q.part3 hc' hg).1 u_T (abs_le.mpr ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2]⟩)
        (by rw [hu_mem.2]))
      hB2 hθ_pos.le hθ_le1
    have h1θ : (1 / 2 : ℝ) ≤ 1 - θ := by linarith
    have h_psi_lb : quantC1KappaStar * (u_T - airyZero 1) ≤
        (psiTilde prob c' g ((airyZero 1 + θ * (u_T - airyZero 1) : ℝ) : ℂ)).re := by
      have h1 : quantC1KappaStar * (u_T - airyZero 1) ≤ 2 * quantC1KappaStar * (1 - θ) * (u_T - airyZero 1) := by
        have hk := quantC1KappaStar_pos.le
        have hx : 0 ≤ u_T - airyZero 1 := by linarith
        nlinarith [mul_nonneg hk hx]
      exact h1.trans hsec
    have h_pow_lb : (1 / 2 : ℝ) ≤ (1 + airyZero 1 / R) ^ (P.k_0 + 1) := by
      rw [hP_k0]
      have h1 : (1 - 2.35 / 48 : ℝ) ≤ 1 + airyZero 1 / R := by
        have hdiv : -2.35 / 48 ≤ airyZero 1 / R := by
          calc -2.35 / 48 ≤ -2.35 / R := by
                rw [neg_div, neg_div, neg_le_neg_iff]
                exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR_48
            _ ≤ airyZero 1 / R := div_le_div_of_nonneg_right (by linarith) hR_pos.le
        linarith
      have h2 : (1 / 2 : ℝ) ≤ (1 - 2.35 / 48 : ℝ) ^ (5 + 1) := by norm_num
      exact h2.trans (pow_le_pow_left₀ (by norm_num) h1 _)
    have hterm_lb : (P.κ_star / (4 * P.w_star)) * (u_T - airyZero 1) ≤
        (1 + airyZero 1 / R) ^ (P.k_0 + 1) *
          (psiTilde prob c' g ((airyZero 1 + θ * (u_T - airyZero 1) : ℝ) : ℂ)).re /
          quantC1WStar := by
      rw [hP_κ, hP_w]
      have hkn : 0 ≤ quantC1KappaStar * (u_T - airyZero 1) :=
        mul_nonneg quantC1KappaStar_pos.le (by linarith)
      have h1 : (1 / 2 : ℝ) * (quantC1KappaStar * (u_T - airyZero 1)) ≤
          (1 + airyZero 1 / R) ^ (P.k_0 + 1) *
            (psiTilde prob c' g ((airyZero 1 + θ * (u_T - airyZero 1) : ℝ) : ℂ)).re :=
        mul_le_mul h_pow_lb h_psi_lb hkn (pow_nonneg hbase_nn _)
      have h2 : (quantC1KappaStar / (4 * quantC1WStar)) * (u_T - airyZero 1) ≤
          ((1 / 2 : ℝ) * (quantC1KappaStar * (u_T - airyZero 1))) / quantC1WStar := by
        have hw := quantC1WStar_pos.le
        have : ((1 / 2 : ℝ) * (quantC1KappaStar * (u_T - airyZero 1))) / quantC1WStar =
            (quantC1KappaStar / (2 * quantC1WStar)) * (u_T - airyZero 1) := by ring
        rw [this]
        have : quantC1KappaStar / (4 * quantC1WStar) ≤ quantC1KappaStar / (2 * quantC1WStar) :=
          div_le_div_of_nonneg_left quantC1KappaStar_pos.le (mul_pos two_pos quantC1WStar_pos)
            (by linarith [quantC1WStar_pos])
        exact mul_le_mul_of_nonneg_right this (by linarith)
      exact h2.trans (div_le_div_of_nonneg_right h1 quantC1WStar_pos.le)
    have h_main := pnodes_lower_auxW hc' hR_48 hR_ub hg hT_hi hT_A2 hT_a1 hB2 hN hℓ_nn hℓ_le'
      P.k_0 hk0_R
    linarith [hterm_lb, h_main]

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.pnodes_lb_and_thetaW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pnodes_lb_and_thetaW

end FormalResearch.ModularBootstrap.FixedWeightBand
