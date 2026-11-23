module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWQuad

/-!
# The Line Estimate `hI_line` at Every Fixed `(w, Q)`

Source: `CFT/common/two_edge_bootstrap.tex` (`teb:bootstrap`, hypothesis `hI_line`) and
`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Step 3.

* `line_boundW`: for the shifted test `f_{k,ℓ}(u) = Ψ̃(u + ℓ)(1 + u/R)^{k+1}`, the real-line integral
  `∫_{-R}^R Re f_{k,ℓ}` is bounded by `(C_a (k+1)/R) + ...`, using the type-(II) envelope of `Lemma Q (2)`
  on `[-R, A_{c'}²]`, the band moments `B₁^{(k)}`, `B₂` and the far-lobe mass `δ_lobe`
  (the Virasoro `virasoro_line_bound`, with `virasoroEnvC0`, `virasoroSigma`, `virasoroAC` replaced by
  `Q.C0`, `Q.sigma`, `Q.AC`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing PoissonJensen TipFront ConcreteBootstrap FixedWeightTip FormalResearch.Special

variable {prob : FixedWeightProblem} [Q : LemmaQData prob]

private lemma line_top_boundW {c' R T ℓ : ℝ}
    (hc' : Q.cQ ≤ c') (hς_nn : 0 ≤ Q.sigma c') (hς_half : Q.sigma c' ≤ 1 / 2)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (_hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr))
    (huT_ge : -virasoroAThr ≤ virasoroUT c' T) (hΔ_uT : virasoroDeltaChart c' (virasoroUT c' T) = T)
    (huT_le_1 : virasoroUT c' T ≤ -1)
    (hΨ_cont_all : ContinuousOn (fun v : ℝ => (psiTilde prob c' g (v : ℂ)).re)
      (Icc (-R) (Q.AC c' ^ 2)))
    {k : ℕ} (hk5 : 5 ≤ k) :
    ∫ v in (-R + ℓ)..(R + ℓ), (psiTilde prob c' g (v : ℂ)).re ≤
      -(∫ v in (-R)..(-R + ℓ), (psiTilde prob c' g (v : ℂ)).re) - bandB2W prob c' R g +
        Q.C0 * ((k : ℝ) + 1) / R + deltaLobe prob Q.D.r_1 c' g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hc'_24 : 24 ≤ c' := by have := Q.hcQ_10000; linarith
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((Q.hcQ_10000.trans hc'))
  have ha : prob.totalShift ≤ c' / 12 := by
    have := Q.hcQ_shift; have := Q.hcQ_10000; linarith
  have hR_pos : 0 < R := by linarith
  have hA2_nn : 0 ≤ Q.AC c' ^ 2 := sq_nonneg _
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  have hi_Ψ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ Q.AC c' ^ 2 →
      IntervalIntegrable (fun v : ℝ => (psiTilde prob c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 => (hΨ_cont_all.mono (Icc_subset_Icc ha0 hb0)).intervalIntegrable_of_Icc hab
  have h_int_full : ∫ v in (-R + ℓ)..(R + ℓ), (psiTilde prob c' g (v : ℂ)).re =
      (∫ v in (-R + ℓ)..(Q.AC c' ^ 2), (psiTilde prob c' g (v : ℂ)).re) -
        ∫ v in (R + ℓ)..(Q.AC c' ^ 2), (psiTilde prob c' g (v : ℂ)).re := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hi_Ψ (-R + ℓ) (R + ℓ) (by linarith) (by linarith) (by linarith))
      (hi_Ψ (R + ℓ) (Q.AC c' ^ 2) (by linarith) (by linarith) le_rfl)
    linarith only [hadd]
  have h_top_bound : ∫ v in (-R + ℓ)..(Q.AC c' ^ 2), (psiTilde prob c' g (v : ℂ)).re ≤
      -(∫ v in (-R)..(-R + ℓ), (psiTilde prob c' g (v : ℂ)).re) - bandB2W prob c' R g +
        deltaLobe prob Q.D.r_1 c' g := by
    have hR'_nn : 0 ≤ R - ℓ := by linarith
    have hR'_le : R - ℓ ≤ Q.AC c' ^ 2 := by linarith
    have hneg_R' : -R + ℓ = -(R - ℓ) := by ring
    have huT_ge' : -(R - ℓ) ≤ virasoroUT c' T := by linarith
    have hT_le_ΔR' : T ≤ virasoroDeltaChart c' (-(R - ℓ)) := by
      rw [← hΔ_uT]
      exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ huT_ge'
    have hQ_eq := ((Q.part3 hc' hg).2.2.2.2 (R - ℓ) hR'_nn hR'_le hT_le_ΔR').1
    rw [← hneg_R'] at hQ_eq
    have h_band_cov := Q.psiTilde_integral_eq hc'_24 hg.1
      (by linarith : -(Q.AC c' ^ 2) ≤ -R) (by linarith) (by linarith : -R ≤ -R + ℓ)
    have h_vac_le : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t ≤ 0 := by
      have hv := hg.2.2.1; unfold FixedWeightProblem.gVac at hv; nlinarith [Real.pi_pos]
    set t_lo := virasoroDeltaChart c' (Q.AC c' ^ 2)
    set t_mid := virasoroDeltaChart c' (-R + ℓ)
    set t_hi := virasoroDeltaChart c' (-R)
    have ht_lo_pos : 0 < t_lo := Q.deltaChart_pos hc'_pos (abs_of_nonneg hA2_nn).le
    have ht_lo_mid : t_lo ≤ t_mid :=
      (Q.deltaChart_strictAnti hc'_pos).antitoneOn ⟨by linarith, by linarith⟩
        ⟨by linarith, le_rfl⟩ (by linarith)
    have ht_mid_hi : t_mid ≤ t_hi :=
      (Q.deltaChart_strictAnti hc'_pos).antitoneOn ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ (by linarith)
    have hgv_int : IntegrableOn (fun t => g t * prob.cardyV (c' / 12) t) (Ioi 0) :=
      hg.1.int_cardy.norm.mono'
        (((hg.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
          Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_abs])
    have hsp1 : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t =
        (∫ t in Ioc 0 t_lo, g t * prob.cardyV (c' / 12) t) +
          ∫ t in Ioi t_lo, g t * prob.cardyV (c' / 12) t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi ht_lo_pos.le)),
        Ioc_union_Ioi_eq_Ioi ht_lo_pos.le]
    have hsp2 : ∫ t in Ioi t_lo, g t * prob.cardyV (c' / 12) t =
        (∫ t in Ioc t_lo t_mid, g t * prob.cardyV (c' / 12) t) +
          ∫ t in Ioi t_mid, g t * prob.cardyV (c' / 12) t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((hgv_int.mono_set (Ioi_subset_Ioi ht_lo_pos.le)).mono_set Ioc_subset_Ioi_self)
        (hgv_int.mono_set (Ioi_subset_Ioi (ht_lo_pos.le.trans ht_lo_mid))),
        Ioc_union_Ioi_eq_Ioi ht_lo_mid]
    have hsp3 : ∫ t in Ioi t_mid, g t * prob.cardyV (c' / 12) t =
        (∫ t in Ioc t_mid t_hi, g t * prob.cardyV (c' / 12) t) +
          ∫ t in Ioi t_hi, g t * prob.cardyV (c' / 12) t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((hgv_int.mono_set (Ioi_subset_Ioi (ht_lo_pos.le.trans ht_lo_mid))).mono_set Ioc_subset_Ioi_self)
        (hgv_int.mono_set (Ioi_subset_Ioi ((ht_lo_pos.le.trans ht_lo_mid).trans ht_mid_hi))),
        Ioc_union_Ioi_eq_Ioi ht_mid_hi]
    have h_lobe_eq : -(∫ t in Ioc 0 t_lo, g t * prob.cardyV (c' / 12) t) ≤
        ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t := by
      rw [← intervalIntegral.integral_of_le ht_lo_pos.le, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_mono_on ht_lo_pos.le
        (((hg.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).neg.intervalIntegrable_of_Icc ht_lo_pos.le)
        (((hg.1.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos.le)
        fun t ht => ?_
      have hV := prob.cardyV_nonneg ha ht.1
      calc -(g t * prob.cardyV (c' / 12) t) = (-g t) * prob.cardyV (c' / 12) t := by ring
        _ ≤ |g t| * prob.cardyV (c' / 12) t := mul_le_mul_of_nonneg_right (neg_le_abs _) hV
    have hIci_Ioi : ∫ t in Ici t_hi, g t * prob.cardyV (c' / 12) t =
        ∫ t in Ioi t_hi, g t * prob.cardyV (c' / 12) t :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_sum_t : ∫ t in t_lo..t_mid, g t * prob.cardyV (c' / 12) t ≤
        -(∫ t in t_mid..t_hi, g t * prob.cardyV (c' / 12) t) -
          (∫ t in Ici t_hi, g t * prob.cardyV (c' / 12) t) +
          ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t := by
      rw [intervalIntegral.integral_of_le ht_lo_mid, intervalIntegral.integral_of_le ht_mid_hi, hIci_Ioi]
      linarith only [h_vac_le, hsp1, hsp2, hsp3, h_lobe_eq]
    have hM_nn : 0 ≤ (prob.cardyNorm (c' / 12) g)⁻¹ := inv_nonneg.mpr hM_pos.le
    have hmul := mul_le_mul_of_nonneg_left h_sum_t hM_nn
    rw [← hQ_eq, mul_add, mul_sub, mul_neg] at hmul
    unfold bandB2W deltaLobe
    linarith only [hmul, h_band_cov]
  have h_pos_tail : -(∫ v in (R + ℓ)..(Q.AC c' ^ 2), (psiTilde prob c' g (v : ℂ)).re) ≤
      (6 / 5 : ℝ) * Q.C0 * Real.exp (-(5 / 6 : ℝ) * R) := by
    have h_norm : |∫ v in (R + ℓ)..(Q.AC c' ^ 2), (psiTilde prob c' g (v : ℂ)).re| ≤
        ∫ v in (R + ℓ)..(Q.AC c' ^ 2), ‖psiTilde prob c' g (v : ℂ)‖ := by
      calc |∫ v in (R + ℓ)..(Q.AC c' ^ 2), (psiTilde prob c' g (v : ℂ)).re|
          ≤ ∫ v in (R + ℓ)..(Q.AC c' ^ 2), |(psiTilde prob c' g (v : ℂ)).re| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun v : ℝ => (psiTilde prob c' g (v : ℂ)).re) (μ := volume)
              (by linarith : R + ℓ ≤ Q.AC c' ^ 2)
        _ ≤ ∫ v in (R + ℓ)..(Q.AC c' ^ 2), ‖psiTilde prob c' g (v : ℂ)‖ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              ((continuous_abs.comp_continuousOn (hΨ_cont_all.mono (Icc_subset_Icc (by linarith) le_rfl))).intervalIntegrable_of_Icc (by linarith))
              ((continuous_norm.comp_continuousOn ((Q.analytic hc' hg.1).continuousOn.comp continuous_ofReal.continuousOn fun v hv =>
                Q.closedBall_subset_psiDom hc'_pos (by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith [hv.1], hv.2⟩))).intervalIntegrable_of_Icc (by linarith))
              fun v _ => Complex.abs_re_le_norm _
    have ht_le := @pos_real_norm_tail_leW prob Q c' (R + ℓ) (Q.AC c' ^ 2) hc' hς_nn hς_half
      (by linarith) (by linarith) le_rfl g hg.1 hM_pos
    have hexp_mon : Real.exp (-(5 / 6 : ℝ) * (R + ℓ)) ≤ Real.exp (-(5 / 6 : ℝ) * R) :=
      Real.exp_le_exp.mpr (by linarith)
    have h1 := (abs_le.mp h_norm).1
    have hpos65 : (0 : ℝ) ≤ (6 / 5 : ℝ) * Q.C0 := by have := Q.hC0; positivity
    have := mul_le_mul_of_nonneg_left hexp_mon hpos65
    linarith only [h1, ht_le, this]
  have h_pos_tail_R : (6 / 5 : ℝ) * Q.C0 * Real.exp (-(5 / 6 : ℝ) * R) ≤
      Q.C0 * ((k : ℝ) + 1) / R := by
    have h_xe : (5 / 6 : ℝ) * R * Real.exp (-(5 / 6 : ℝ) * R) ≤ 1 := by
      have := Real.add_one_le_exp ((5 / 6 : ℝ) * R)
      rw [show -(5 / 6 : ℝ) * R = -((5 / 6 : ℝ) * R) by ring, Real.exp_neg,
        mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    have hk6 : (6 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : 6 ≤ k + 1)
    have h_exp_R : Real.exp (-(5 / 6 : ℝ) * R) ≤ (6 / 5 : ℝ) / R := by
      rw [le_div_iff₀ hR_pos]; linarith
    have hC0_nn := Q.hC0.le
    calc (6 / 5 : ℝ) * Q.C0 * Real.exp (-(5 / 6 : ℝ) * R)
        ≤ (6 / 5 : ℝ) * Q.C0 * ((6 / 5 : ℝ) / R) := by gcongr
      _ = ((36 / 25 : ℝ) * Q.C0) / R := by ring
      _ ≤ (Q.C0 * 6) / R := div_le_div_of_nonneg_right (by nlinarith [Q.hC0]) hR_pos.le
      _ ≤ (Q.C0 * ((k : ℝ) + 1)) / R := by gcongr
      _ = Q.C0 * ((k : ℝ) + 1) / R := by ring
  linarith only [h_int_full, h_top_bound, h_pos_tail, h_pos_tail_R]

private lemma line_band_pieceW {c' R T ℓ : ℝ}
    (hc' : Q.cQ ≤ c') (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (huT_Icc : virasoroUT c' T ∈ Icc (-virasoroAThr) (-1))
    (hΔ_uT : virasoroDeltaChart c' (virasoroUT c' T) = T)
    (hΨ_cont_all : ContinuousOn (fun v : ℝ => (psiTilde prob c' g (v : ℂ)).re)
      (Icc (-R) (Q.AC c' ^ 2)))
    (k : ℕ) :
    -(∫ v in (-R + ℓ)..(virasoroUT c' T),
        (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * (psiTilde prob c' g (v : ℂ)).re) -
      (∫ v in (-R)..(-R + ℓ), (psiTilde prob c' g (v : ℂ)).re) ≤
      -(63 / 100 : ℝ) * bandB1kW prob c' R T g k := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hR_pos : 0 < R := by linarith
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  set u_T := virasoroUT c' T
  let W : ℝ → ℝ := fun v => (1 + (v - ℓ) / R) ^ (k + 1)
  have hW_cont : Continuous W :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hnegRl_le_uT : -R + ℓ ≤ u_T := by linarith [huT_Icc.1]
  have huT_le_R : u_T ≤ R + ℓ := by linarith [huT_Icc.2]
  have h_mem_sub : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      Icc a b ⊆ Icc (-R) (Q.AC c' ^ 2) := fun ha0 _ hb0 => Icc_subset_Icc ha0 (by linarith)
  have hi_Ψ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (psiTilde prob c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 => (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0)).intervalIntegrable_of_Icc hab
  have hi_WΨ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (1 - W v) * (psiTilde prob c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 =>
      ((continuousOn_const.sub hW_cont.continuousOn).mul
        (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0))).intervalIntegrable_of_Icc hab
  have hi_B1k : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ =>
        min 1 (((k : ℝ) + 1) * (-v) / R) * (psiTilde prob c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 =>
      (((continuous_const.min ((continuous_const.mul continuous_neg).div_const R)).continuousOn).mul
        (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0))).intervalIntegrable_of_Icc hab
  have hΨ_nn_band : ∀ v : ℝ, -R ≤ v → v ≤ u_T → 0 ≤ (psiTilde prob c' g (v : ℂ)).re := by
    intro v hv1 hv2
    refine (Q.part3 hc' hg).1 v (abs_le.mpr ⟨by linarith, by linarith [huT_Icc.2]⟩) ?_
    rw [← hΔ_uT]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith [huT_Icc.2]⟩ ⟨by linarith [huT_Icc.1], by linarith [huT_Icc.2]⟩ hv2
  have h_low_left : (63 / 100 : ℝ) * ∫ v in (-R)..(-R + ℓ),
        min 1 (((k : ℝ) + 1) * (-v) / R) * (psiTilde prob c' g (v : ℂ)).re ≤
      ∫ v in (-R)..(-R + ℓ), (psiTilde prob c' g (v : ℂ)).re := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((hi_B1k (-R) (-R + ℓ) le_rfl (by linarith) (by linarith)).const_mul _)
      (hi_Ψ (-R) (-R + ℓ) le_rfl (by linarith) (by linarith)) fun v hv => ?_
    have hΨ_nn := hΨ_nn_band v hv.1 (by linarith [hv.2, hnegRl_le_uT])
    have hm1 : (63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R) ≤ 1 := by
      linarith [min_le_left (1 : ℝ) (((k : ℝ) + 1) * (-v) / R)]
    calc (63 / 100 : ℝ) * (min 1 (((k : ℝ) + 1) * (-v) / R) * (psiTilde prob c' g (v : ℂ)).re)
        = ((63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R)) * (psiTilde prob c' g (v : ℂ)).re := by ring
      _ ≤ 1 * (psiTilde prob c' g (v : ℂ)).re := mul_le_mul_of_nonneg_right hm1 hΨ_nn
      _ = (psiTilde prob c' g (v : ℂ)).re := one_mul _
  have h_main_band : (63 / 100 : ℝ) * ∫ v in (-R + ℓ)..u_T,
        min 1 (((k : ℝ) + 1) * (-v) / R) * (psiTilde prob c' g (v : ℂ)).re ≤
      ∫ v in (-R + ℓ)..u_T, (1 - W v) * (psiTilde prob c' g (v : ℂ)).re := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hnegRl_le_uT
      ((hi_B1k (-R + ℓ) u_T (by linarith) hnegRl_le_uT huT_le_R).const_mul _)
      (hi_WΨ (-R + ℓ) u_T (by linarith) hnegRl_le_uT huT_le_R) fun v hv => ?_
    have hΨ_nn := hΨ_nn_band v (by linarith [hv.1]) hv.2
    have hbase_nn : 0 ≤ 1 + (v - ℓ) / R := by
      have hnum : 0 ≤ R + (v - ℓ) := by linarith [hv.1]
      have heq : 1 + (v - ℓ) / R = (R + (v - ℓ)) / R := by field_simp [hR_pos.ne']
      rw [heq]; exact div_nonneg hnum hR_pos.le
    have hbase_le : 1 + (v - ℓ) / R ≤ Real.exp (-(-v / R)) := by
      have hv_div : (v - ℓ) / R ≤ v / R := div_le_div_of_nonneg_right (by linarith) hR_pos.le
      have hexp1 : 1 + v / R ≤ Real.exp (v / R) := by linarith [Real.add_one_le_exp (v / R)]
      rw [show -(-v / R) = v / R by ring]
      linarith only [hv_div, hexp1]
    have hW_le : W v ≤ Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by
      dsimp [W]
      calc (1 + (v - ℓ) / R) ^ (k + 1)
          ≤ (Real.exp (-(-v / R))) ^ (k + 1) := pow_le_pow_left₀ hbase_nn hbase_le _
        _ = Real.exp (((k + 1 : ℕ) : ℝ) * (-(-v / R))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by push_cast; ring_nf
    have h_min : (63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R) ≤ 1 - W v :=
      (sixtythree_hundredths_min_le_one_sub_exp
        (div_nonneg (mul_nonneg (by positivity) (by linarith [hv.2, huT_Icc.2])) hR_pos.le)).trans
        (sub_le_sub_left hW_le 1)
    calc (63 / 100 : ℝ) * (min 1 (((k : ℝ) + 1) * (-v) / R) * (psiTilde prob c' g (v : ℂ)).re)
        = ((63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R)) * (psiTilde prob c' g (v : ℂ)).re := by ring
      _ ≤ (1 - W v) * (psiTilde prob c' g (v : ℂ)).re := mul_le_mul_of_nonneg_right h_min hΨ_nn
  have hsplit_B1k := intervalIntegral.integral_add_adjacent_intervals
    (hi_B1k (-R) (-R + ℓ) le_rfl (by linarith) (by linarith))
    (hi_B1k (-R + ℓ) u_T (by linarith) hnegRl_le_uT huT_le_R)
  have hB1k_eq : bandB1kW prob c' R T g k =
      (∫ v in (-R)..(-R + ℓ), min 1 (((k : ℝ) + 1) * (-v) / R) * (psiTilde prob c' g (v : ℂ)).re) +
        (∫ v in (-R + ℓ)..u_T, min 1 (((k : ℝ) + 1) * (-v) / R) * (psiTilde prob c' g (v : ℂ)).re) := by
    unfold bandB1kW; rw [← hsplit_B1k]
  linarith only [h_low_left, h_main_band, hB1k_eq]

private lemma line_mid_and_rightW {c' R T ℓ : ℝ}
    (hc' : Q.cQ ≤ c') (hς_half : Q.sigma c' ≤ 1 / 2)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (huT_Icc : virasoroUT c' T ∈ Icc (-virasoroAThr) (-1))
    (hΨ_cont_all : ContinuousOn (fun v : ℝ => (psiTilde prob c' g (v : ℂ)).re)
      (Icc (-R) (Q.AC c' ^ 2)))
    {k : ℕ} (hkR : (k : ℝ) ≤ R / 5) :
    -(∫ v in (virasoroUT c' T)..(1 : ℝ),
        (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * (psiTilde prob c' g (v : ℂ)).re) ≤
      4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R ∧
    -(∫ v in (1 : ℝ)..(R + ℓ),
        (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * (psiTilde prob c' g (v : ℂ)).re) ≤
      2 * Q.C0 * ((k : ℝ) + 1) / R := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((Q.hcQ_10000.trans hc'))
  have hR_pos : 0 < R := by linarith
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  set u_T := virasoroUT c' T
  let W : ℝ → ℝ := fun v => (1 + (v - ℓ) / R) ^ (k + 1)
  have hW_cont : Continuous W :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hnegRl_le_uT : -R + ℓ ≤ u_T := by linarith [huT_Icc.1]
  have huT_le1 : u_T ≤ 1 := by linarith [huT_Icc.2]
  have h_mem_sub : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      Icc a b ⊆ Icc (-R) (Q.AC c' ^ 2) := fun ha0 _ hb0 => Icc_subset_Icc ha0 (by linarith)
  have hi_WΨ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (1 - W v) * (psiTilde prob c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 =>
      ((continuousOn_const.sub hW_cont.continuousOn).mul
        (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0))).intervalIntegrable_of_Icc hab
  refine ⟨?_, ?_⟩
  · have hi1 := hi_WΨ u_T 1 (by linarith [hnegRl_le_uT]) huT_le1 (by linarith)
    have hΨ_norm_int1 : IntervalIntegrable (fun v : ℝ => ‖psiTilde prob c' g (v : ℂ)‖) volume u_T 1 :=
      (continuous_norm.comp_continuousOn ((Q.analytic hc' hg.1).continuousOn.comp
        continuous_ofReal.continuousOn fun v hv => Q.closedBall_subset_psiDom hc'_pos (by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [hv.1, hnegRl_le_uT], by linarith [hv.2, hR_ub]⟩))).intervalIntegrable_of_Icc huT_le1
    have h_abs : |∫ v in u_T..1, (1 - W v) * (psiTilde prob c' g (v : ℂ)).re| ≤
        (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) *
          ∫ v in u_T..1, ‖psiTilde prob c' g (v : ℂ)‖ := by
      calc |∫ v in u_T..1, (1 - W v) * (psiTilde prob c' g (v : ℂ)).re|
          ≤ ∫ v in u_T..1, |(1 - W v) * (psiTilde prob c' g (v : ℂ)).re| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun v : ℝ => (1 - W v) * (psiTilde prob c' g (v : ℂ)).re) (μ := volume) huT_le1
        _ ≤ ∫ v in u_T..1, (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) * ‖psiTilde prob c' g (v : ℂ)‖ := by
            refine intervalIntegral.integral_mono_on huT_le1 hi1.abs
              (hΨ_norm_int1.const_mul _) fun v hv => ?_
            have hvl4 : |v - ℓ| ≤ 4 := by
              have hv_lo : -3.4 ≤ v := by linarith [huT_Icc.1, hv.1, hAThr_lt]
              exact abs_le.mpr ⟨by linarith, by linarith [hv.2]⟩
            have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
            have h_abs_sub : |1 - W v| = |(1 + (v - ℓ) / R) ^ (k + 1) - 1| := by
              dsimp [W]; rw [abs_sub_comm]
            have h_exp_65 : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ 6 / 5 := by
              rw [abs_div, abs_of_pos hR_pos]
              have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ R / 5 + 1 := by push_cast; linarith
              calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) ≤ (R / 5 + 1) * (4 / R) := by gcongr
                _ = 4 / 5 + 4 / R := by field_simp [hR_pos.ne']
                _ ≤ 4 / 5 + 4 / 10 := by gcongr
                _ = 6 / 5 := by norm_num
            have hW_bd : |1 - W v| ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by
              rw [h_abs_sub]
              calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
                  ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| *
                      Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
                _ ≤ ((k + 1 : ℕ) : ℝ) * (4 / R) * Real.exp (6 / 5) := by
                    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
                      (Real.exp_le_exp.mpr h_exp_65) (Real.exp_pos _).le (by positivity)
                    rw [abs_div, abs_of_pos hR_pos]
                    exact div_le_div_of_nonneg_right hvl4 hR_pos.le
                _ = 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by push_cast; ring
            calc |(1 - W v) * (psiTilde prob c' g (v : ℂ)).re|
                = |1 - W v| * |(psiTilde prob c' g (v : ℂ)).re| := abs_mul _ _
              _ ≤ (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) * ‖psiTilde prob c' g (v : ℂ)‖ :=
                  mul_le_mul hW_bd (Complex.abs_re_le_norm _) (abs_nonneg _) (by positivity)
        _ = (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) *
              ∫ v in u_T..1, ‖psiTilde prob c' g (v : ℂ)‖ := intervalIntegral.integral_const_mul _ _
    have hL1_le1 : ∫ v in u_T..1, ‖psiTilde prob c' g (v : ℂ)‖ ≤ 1 := by
      have hΨ_norm_all : ContinuousOn (fun v : ℝ => ‖psiTilde prob c' g (v : ℂ)‖)
          (Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2)) :=
        continuous_norm.comp_continuousOn ((Q.analytic hc' hg.1).continuousOn.comp
          continuous_ofReal.continuousOn fun v hv => Q.closedBall_subset_psiDom hc'_pos (by
            rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hv))
      have h_sub_le : ∫ v in u_T..1, ‖psiTilde prob c' g (v : ℂ)‖ ≤
          ∫ v in (-(Q.AC c' ^ 2))..(Q.AC c' ^ 2), ‖psiTilde prob c' g (v : ℂ)‖ := by
        rw [intervalIntegral.integral_of_le huT_le1, intervalIntegral.integral_of_le (by linarith)]
        refine setIntegral_mono_set
          ((hΨ_norm_all.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self)
          (Eventually.of_forall fun _ => norm_nonneg _)
          (Eventually.of_forall (Ioc_subset_Ioc (by linarith [hnegRl_le_uT]) (by linarith)))
      exact h_sub_le.trans (Q.part3 hc' hg).2.1
    have h_c_nn : 0 ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by positivity
    have h1 := (abs_le.mp h_abs).1
    nlinarith only [h1, hL1_le1, h_c_nn]
  · have h1R : (1 : ℝ) ≤ R + ℓ := by linarith
    have hi_r := hi_WΨ 1 (R + ℓ) (by linarith) h1R le_rfl
    let C_exp : ℝ := Q.C0 * ((k : ℝ) + 1) / R
    have hC_exp_nn : 0 ≤ C_exp := by dsimp [C_exp]; have := Q.hC0; positivity
    have h_abs : |∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * (psiTilde prob c' g (v : ℂ)).re| ≤
        ∫ v in (1 : ℝ)..(R + ℓ), C_exp * Real.exp (-(8 / 15 : ℝ) * v) := by
      calc |∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * (psiTilde prob c' g (v : ℂ)).re|
          ≤ ∫ v in (1 : ℝ)..(R + ℓ), |(1 - W v) * (psiTilde prob c' g (v : ℂ)).re| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun v : ℝ => (1 - W v) * (psiTilde prob c' g (v : ℂ)).re) (μ := volume) h1R
        _ ≤ ∫ v in (1 : ℝ)..(R + ℓ), C_exp * Real.exp (-(8 / 15 : ℝ) * v) := by
            refine intervalIntegral.integral_mono_on h1R hi_r.abs
              ((continuous_const.mul (Real.continuous_exp.comp
                (continuous_const.mul continuous_id))).intervalIntegrable 1 (R + ℓ))
              fun v hv => ?_
            have hv1 : 1 ≤ v := hv.1
            have hv_pos : 0 < v := by linarith
            have hvl : |v - ℓ| ≤ v := abs_le.mpr ⟨by linarith, by linarith⟩
            have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
            have h_abs_sub : |1 - W v| = |(1 + (v - ℓ) / R) ^ (k + 1) - 1| := by
              dsimp [W]; rw [abs_sub_comm]
            have h_exp_310 : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ (3 / 10 : ℝ) * v := by
              rw [abs_div, abs_of_pos hR_pos]
              have hk1R : ((k + 1 : ℕ) : ℝ) / R ≤ 3 / 10 := by
                push_cast; rw [div_le_iff₀ hR_pos]; linarith
              calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) = (((k + 1 : ℕ) : ℝ) / R) * |v - ℓ| := by ring
                _ ≤ (3 / 10 : ℝ) * v := mul_le_mul hk1R hvl (abs_nonneg _) (by norm_num)
            have hW_bd : |1 - W v| ≤ (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by
              rw [h_abs_sub]
              calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
                  ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| *
                      Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
                _ ≤ (((k + 1 : ℕ) : ℝ) * (v / R)) * Real.exp ((3 / 10 : ℝ) * v) := by
                    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
                      (Real.exp_le_exp.mpr h_exp_310) (Real.exp_pos _).le (by positivity)
                    rw [abs_div, abs_of_pos hR_pos]; exact div_le_div_of_nonneg_right hvl hR_pos.le
                _ = (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by push_cast; ring
            have hv_ball : (v : ℂ) ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2) := by
              rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos]
              linarith [hv.2]
            have hcut : ¬ ((v : ℂ).im = 0 ∧ (v : ℂ).re ≤ 0) := fun h0 => by
              simp only [Complex.ofReal_re] at h0; linarith
            have h_env := (Q.part2 hc' hg.1 hM_pos).2.2 (v : ℂ) hv_ball hcut
            have h_re_sqrt : ((v : ℂ) ^ (1 / 2 : ℂ)).re = √v := by
              rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hv_pos.le,
                Complex.ofReal_re, Real.sqrt_eq_rpow]
            have h_env_val : airyEnv (v : ℂ) = Real.exp (-(4 / 3 : ℝ) * (v ^ (3 / 2 : ℝ))) := by
              unfold airyEnv
              rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hv_pos.le,
                Complex.ofReal_re]
            have h_inv_eq : ‖(v : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((v : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ = v⁻¹ := by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos, h_re_sqrt,
                Real.rpow_neg hv_pos.le, ← Real.sqrt_eq_rpow, ← mul_inv, Real.mul_self_sqrt hv_pos.le]
            have hΨ_bd : |(psiTilde prob c' g (v : ℂ)).re| ≤
                Q.C0 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + Q.sigma c' * √v) * v⁻¹ := by
              calc |(psiTilde prob c' g (v : ℂ)).re| ≤ ‖psiTilde prob c' g (v : ℂ)‖ :=
                    Complex.abs_re_le_norm _
                _ ≤ Q.C0 * airyEnv (v : ℂ) * Real.exp (Q.sigma c' * ((v : ℂ) ^ (1 / 2 : ℂ)).re) *
                      ‖(v : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((v : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ := h_env
                _ = Q.C0 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + Q.sigma c' * √v) * v⁻¹ := by
                    rw [mul_assoc (Q.C0 * airyEnv (v : ℂ) * _), h_inv_eq, h_re_sqrt, h_env_val,
                      mul_assoc Q.C0, ← Real.exp_add]
            have hv32 : v ≤ v ^ (3 / 2 : ℝ) := by
              conv_lhs => rw [← Real.rpow_one v]
              exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
            have hsqrt_le : √v ≤ v := by
              rw [Real.sqrt_eq_rpow]
              conv_rhs => rw [← Real.rpow_one v]
              exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
            have hexp_sum : -(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + Q.sigma c' * √v + (3 / 10 : ℝ) * v ≤
                -(8 / 15 : ℝ) * v := by
              have hsqrt_nn : 0 ≤ √v := Real.sqrt_nonneg v
              nlinarith only [hv32, hsqrt_le, hς_half, hv1, hsqrt_nn]
            have hexp_prod : Real.exp ((3 / 10 : ℝ) * v) *
                  Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + Q.sigma c' * √v) =
                Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + Q.sigma c' * √v + (3 / 10 : ℝ) * v) := by
              rw [← Real.exp_add]; ring_nf
            calc |(1 - W v) * (psiTilde prob c' g (v : ℂ)).re|
                = |1 - W v| * |(psiTilde prob c' g (v : ℂ)).re| := abs_mul _ _
              _ ≤ ((((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v)) *
                    (Q.C0 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + Q.sigma c' * √v) * v⁻¹) :=
                  mul_le_mul hW_bd hΨ_bd (abs_nonneg _) (by positivity)
              _ = C_exp * (Real.exp ((3 / 10 : ℝ) * v) *
                    Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + Q.sigma c' * √v)) * (v * v⁻¹) := by
                  dsimp [C_exp]; ring
              _ = C_exp * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + Q.sigma c' * √v + (3 / 10 : ℝ) * v) := by
                  rw [hexp_prod, mul_inv_cancel₀ hv_pos.ne', mul_one]
              _ ≤ C_exp * Real.exp (-(8 / 15 : ℝ) * v) :=
                  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_sum) hC_exp_nn
    have h_ftc_r : ∫ v in (1 : ℝ)..(R + ℓ), C_exp * Real.exp (-(8 / 15 : ℝ) * v) ≤ 2 * C_exp := by
      have hderiv : ∀ v ∈ Set.uIcc 1 (R + ℓ),
          HasDerivAt (fun t : ℝ => -((15 / 8 : ℝ) * C_exp) * Real.exp (-(8 / 15 : ℝ) * t))
            (C_exp * Real.exp (-(8 / 15 : ℝ) * v)) v := fun v _ => by
        have h1 : HasDerivAt (fun t : ℝ => -(8 / 15 : ℝ) * t) (-(8 / 15 : ℝ)) v := by
          simpa using (hasDerivAt_id v).const_mul (-(8 / 15 : ℝ))
        refine (h1.exp.const_mul (-((15 / 8 : ℝ) * C_exp))).congr_deriv ?_
        ring
      have h_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable 1 (R + ℓ))
      have hR_nn : 0 ≤ ((15 / 8 : ℝ) * C_exp) * Real.exp (-(8 / 15 : ℝ) * (R + ℓ)) := by positivity
      have h1_le : Real.exp (-(8 / 15 : ℝ) * 1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith only [h_eq, hR_nn, h1_le, hC_exp_nn]
    have h1 := (abs_le.mp h_abs).1
    have h2 : 2 * C_exp = 2 * Q.C0 * ((k : ℝ) + 1) / R := by dsimp [C_exp]; ring
    linarith only [h1, h_ftc_r, h2]

/-- **Line Estimate (`TE.5` / `BootstrapCore.hI_line`)**:
For `c' ≥ Q.cQ` with `Q.sigma c' ≤ 1/2`, `R ≥ 10` (`R + 1 ≤ Q.AC c'^2`),
`T ∈ [Δ(-1), Δ(-A_thr)]` (`u_T ∈ [-A_thr, -1]`), `ℓ ∈ [0, 1/2]`, and `5 ≤ k ≤ R/5`,
`∫_{-R}^R (f_{k, ℓ} x).re ≤ -(63/100) B_1^{(k)} - B_2 + (4 exp(6/5) + 3 C₀)(k+1)/R + Δ_lobe`. -/
theorem line_boundW {c' R T ℓ : ℝ}
    (hc' : Q.cQ ≤ c') (hς_nn : 0 ≤ Q.sigma c') (hς_half : Q.sigma c' ≤ 1 / 2)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' (-1) ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr))
    {k : ℕ} (hk5 : 5 ≤ k) (hkR : (k : ℝ) ≤ R / 5) :
    ∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k (x : ℂ)).re ≤
      -(63 / 100 : ℝ) * bandB1kW prob c' R T g k - bandB2W prob c' R g +
        (4 * Real.exp (6 / 5) + 3 * Q.C0) * ((k : ℝ) + 1) / R +
        deltaLobe prob Q.D.r_1 c' g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((Q.hcQ_10000.trans hc'))
  have ha : prob.totalShift ≤ c' / 12 := by
    have := Q.hcQ_shift; have := Q.hcQ_10000; linarith
  have hM_pos : 0 < prob.cardyNorm (c' / 12) g :=
    Q.cardyNorm_pos hc' hg
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  have hu_mem := Q.UT_between hc'_pos
    (by linarith : -(Q.AC c' ^ 2) ≤ -virasoroAThr)
    (by linarith [sq_nonneg (Q.AC c')]) (by linarith [virasoroAThr_gt_two] : -virasoroAThr ≤ -1)
    hT_lo hT_hi
  set u_T := virasoroUT c' T
  have huT_Icc : u_T ∈ Icc (-virasoroAThr) (-1) := hu_mem.1
  have hΔ_uT : virasoroDeltaChart c' u_T = T := hu_mem.2
  have h_shift_eq : ∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k (x : ℂ)).re =
      ∫ v in (-R + ℓ)..(R + ℓ),
        (1 + (v - ℓ) / R) ^ (k + 1) * (psiTilde prob c' g (v : ℂ)).re := by
    have hrew : (fun x : ℝ => (shiftedFunW prob c' R ℓ g k (x : ℂ)).re) =
        fun x : ℝ => (1 + x / R) ^ (k + 1) * (psiTilde prob c' g (((x + ℓ : ℝ) : ℂ))).re := by
      ext x; unfold shiftedFunW
      have hreal_pow : ((1 + (x : ℂ) / (R : ℂ)) ^ (k + 1)) =
          (((1 + x / R) ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [hreal_pow, show (x : ℂ) + (ℓ : ℂ) = ((x + ℓ : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring
    rw [hrew]
    simpa [add_sub_cancel_right] using
      intervalIntegral.integral_comp_add_right
        (fun v : ℝ => (1 + (v - ℓ) / R) ^ (k + 1) * (psiTilde prob c' g (v : ℂ)).re) ℓ
        (a := -R) (b := R)
  rw [h_shift_eq]
  have hΨ_cont_all : ContinuousOn (fun v : ℝ => (psiTilde prob c' g (v : ℂ)).re)
      (Icc (-R) (Q.AC c' ^ 2)) := by
    refine Complex.continuous_re.comp_continuousOn
      ((Q.analytic hc' hg.1).continuousOn.comp
        continuous_ofReal.continuousOn fun v hv => Q.closedBall_subset_psiDom hc'_pos (by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [hv.1], hv.2⟩))
  have h_mem_sub : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      Icc a b ⊆ Icc (-R) (Q.AC c' ^ 2) := fun ha0 _ hb0 => Icc_subset_Icc ha0 (by linarith)
  let W : ℝ → ℝ := fun v => (1 + (v - ℓ) / R) ^ (k + 1)
  have hW_cont : Continuous W :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hi_Ψ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ Q.AC c' ^ 2 →
      IntervalIntegrable (fun v : ℝ => (psiTilde prob c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 => (hΨ_cont_all.mono (Icc_subset_Icc ha0 hb0)).intervalIntegrable_of_Icc hab
  have hi_WΨ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (1 - W v) * (psiTilde prob c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 =>
      ((continuousOn_const.sub hW_cont.continuousOn).mul
        (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0))).intervalIntegrable_of_Icc hab
  have h_split_W : ∫ v in (-R + ℓ)..(R + ℓ), W v * (psiTilde prob c' g (v : ℂ)).re =
      (∫ v in (-R + ℓ)..(R + ℓ), (psiTilde prob c' g (v : ℂ)).re) -
        ∫ v in (-R + ℓ)..(R + ℓ), (1 - W v) * (psiTilde prob c' g (v : ℂ)).re := by
    rw [← intervalIntegral.integral_sub
      (hi_Ψ (-R + ℓ) (R + ℓ) (by linarith) (by linarith) (by linarith))
      (hi_WΨ (-R + ℓ) (R + ℓ) (by linarith) (by linarith) le_rfl)]
    refine intervalIntegral.integral_congr fun v _ => by ring
  have hnegRl_le_uT : -R + ℓ ≤ u_T := by linarith [huT_Icc.1]
  have huT_le_R : u_T ≤ R + ℓ := by linarith [huT_Icc.2]
  have h_split_W1 : ∫ v in (-R + ℓ)..(R + ℓ), (1 - W v) * (psiTilde prob c' g (v : ℂ)).re =
      (∫ v in (-R + ℓ)..u_T, (1 - W v) * (psiTilde prob c' g (v : ℂ)).re) +
        (∫ v in u_T..1, (1 - W v) * (psiTilde prob c' g (v : ℂ)).re) +
        (∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * (psiTilde prob c' g (v : ℂ)).re) := by
    have h12 := intervalIntegral.integral_add_adjacent_intervals
      (hi_WΨ (-R + ℓ) u_T (by linarith) hnegRl_le_uT huT_le_R)
      (hi_WΨ u_T 1 (by linarith [hnegRl_le_uT]) (by linarith [huT_Icc.2]) (by linarith))
    have h23 := intervalIntegral.integral_add_adjacent_intervals
      (hi_WΨ (-R + ℓ) 1 (by linarith) (by linarith) (by linarith))
      (hi_WΨ 1 (R + ℓ) (by linarith) (by linarith) le_rfl)
    linarith only [h12, h23]
  have h_top := line_top_boundW hc' hς_nn hς_half hR_10 hR_ub hℓ_nn hℓ_half hg hM_pos hT_hi
    huT_Icc.1 hΔ_uT huT_Icc.2 hΨ_cont_all hk5
  have h_band := line_band_pieceW hc' hR_10 hR_ub hℓ_nn hℓ_half hg huT_Icc hΔ_uT hΨ_cont_all k
  obtain ⟨h_mid, h_right⟩ := line_mid_and_rightW hc' hς_half hR_10 hR_ub hℓ_nn hℓ_half hg
    hM_pos huT_Icc hΨ_cont_all hkR
  have h_sum_coeff :
      Q.C0 * ((k : ℝ) + 1) / R + 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R +
        2 * Q.C0 * ((k : ℝ) + 1) / R =
      (4 * Real.exp (6 / 5) + 3 * Q.C0) * ((k : ℝ) + 1) / R := by ring
  linarith only [h_split_W, h_split_W1, h_top, h_band, h_mid, h_right, h_sum_coeff]

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.line_boundW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms line_boundW

end FormalResearch.ModularBootstrap.FixedWeightBand
