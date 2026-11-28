module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreeze

/-!
# Global Fubini & Early-Layer Estimate for Centre-Averaged Freezing (`ctl:freeze`)

Proves `boas_freezing_estimate`: for all sufficiently large `c'`, all `R` in `LowerRadiusRange virasoroC1 c' R`,
and every nonnegative measurable `h` on `[ζ_min, ∞)` with `lowerPζ c' R * h` integrable,
the centre-averaged frozen integral `boasFrozenInt c' R h` is integrable on `[ζ_*, ∞)` and satisfies
`|(∫ z in Ici (boasZetaStar c'), boasFrozenInt c' R h z) - ∫ ζ in Ici (zetaMin c'), boasA c' R ζ ζ * h ζ| ≤
  C_F * c'⁻¹ * (∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ) +
    9 * ∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

noncomputable section

private lemma boasA_cut_measurable {c' R : ℝ} (hc10000 : 10000 ≤ c')
    (hP_cont : ContinuousOn (lowerPζ c' R) (Ici (zetaMin c' / 2))) :
    Measurable fun p : ℝ × ℝ =>
      if boasZetaStar c' ≤ p.2 then boasA c' R p.1 p.2 else 0 := by
  have hc0 : 0 < c' := by linarith
  have hζ_sub : Ici (boasZetaStar c') ⊆ Ici (zetaMin c' / 2) := fun z hz => by
    have hz1 : boasZetaStar c' ≤ z := hz
    unfold boasZetaStar at hz1
    exact (half_le_self (zetaMin_pos hc0).le).trans (by linarith only [hz1, Real.log_pos (by linarith : 1 < c')])
  have hIci_sub_pos : Ici (boasZetaStar c') ⊆ Ioi 0 := fun z hz =>
    lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) (hζ_sub hz)
  obtain ⟨_, _, hWθ⟩ := lowerWeps_unwrappedTheta_deriv_bounds
  obtain ⟨W1', _, θ', _, hspec⟩ := hWθ hc10000
  have hW_cont : ContinuousOn (fun z => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z)))
      (Ici (boasZetaStar c')) := fun z hz =>
    (hspec (hIci_sub_pos hz)).1.continuousAt.continuousWithinAt
  have hθ_cont : ContinuousOn (fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z))
      (Ici (boasZetaStar c')) := fun z hz =>
    (hspec (hIci_sub_pos hz)).2.2.1.continuousAt.continuousWithinAt
  let Pc : ℝ → ℝ := (Ici (boasZetaStar c')).piecewise (lowerPζ c' R) 0
  let Wc : ℝ → ℝ := (Ici (boasZetaStar c')).piecewise
    (fun z => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))) 0
  let θc : ℝ → ℝ := (Ici (boasZetaStar c')).piecewise
    (fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)) 0
  have hPc : Measurable Pc := (hP_cont.mono hζ_sub).measurable_piecewise continuousOn_const measurableSet_Ici
  have hWc : Measurable Wc := hW_cont.measurable_piecewise continuousOn_const measurableSet_Ici
  have hθc : Measurable θc := hθ_cont.measurable_piecewise continuousOn_const measurableSet_Ici
  have hmeas_full : Measurable fun p : ℝ × ℝ =>
      if boasZetaStar c' ≤ p.2 then
        Pc p.2 * (1 - 2 * Wc p.2 * Real.sin (2 * π * p.1 - θc p.2))
      else 0 := by
    refine Measurable.ite (measurableSet_Ici.preimage measurable_snd) ?_ measurable_const
    exact (hPc.comp measurable_snd).mul (measurable_const.sub ((measurable_const.mul (hWc.comp measurable_snd)).mul
      (Real.continuous_sin.measurable.comp ((measurable_const.mul measurable_fst).sub (hθc.comp measurable_snd)))))
  have heq_cut :
      (fun p : ℝ × ℝ => if boasZetaStar c' ≤ p.2 then boasA c' R p.1 p.2 else 0) =
      (fun p : ℝ × ℝ =>
        if boasZetaStar c' ≤ p.2 then
          Pc p.2 * (1 - 2 * Wc p.2 * Real.sin (2 * π * p.1 - θc p.2))
        else 0) := by
    ext p
    by_cases hz : boasZetaStar c' ≤ p.2
    · simp only [hz, ↓reduceIte, Pc, Wc, θc, Set.piecewise_eq_of_mem _ _ _ (mem_Ici.mpr hz), boasA]
    · simp only [hz, ↓reduceIte]
  rw [heq_cut]
  exact hmeas_full

/-- **Global centre-averaged freezing (`ctl:freeze`)**: compares `∫_{ζ_min}^∞ A_ζ(ζ) h(ζ) dζ`
against `∫_{ζ_*}^∞ boasFrozenInt c' R h z dz` with `O(c'⁻¹)` global residual and an early-layer term
supported on `[ζ_min, 2 ζ_min]`. -/
theorem boas_freezing_estimate :
    ∃ c_F C_F : ℝ, 10000 ≤ c_F ∧ 0 < C_F ∧
      ∀ {c' R : ℝ}, c_F ≤ c' → LowerRadiusRange virasoroC1 c' R →
        ∀ {h : ℝ → ℝ}, AEStronglyMeasurable h (volume.restrict (Ici (zetaMin c'))) →
          (∀ {ζ : ℝ}, zetaMin c' ≤ ζ → 0 ≤ h ζ) →
          IntegrableOn (fun ζ => lowerPζ c' R ζ * h ζ) (Ici (zetaMin c')) →
          IntegrableOn (boasFrozenInt c' R h) (Ici (boasZetaStar c')) ∧
          |(∫ z in Ici (boasZetaStar c'), boasFrozenInt c' R h z) -
              ∫ ζ in Ici (zetaMin c'), boasA c' R ζ ζ * h ζ| ≤
            C_F * c' ^ (-1 : ℝ) * (∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ) +
              9 * ∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ := by
  obtain ⟨c_T, C_P, hcT, hCP, hP_all⟩ := lowerPζ_properties
  obtain ⟨C_trig, hCtrig, hT_all⟩ := boas_trig_c2_bounds
  let K_loc : ℝ := 10 * (9 * π ^ 2 * C_P + 2 * (3 * π) * C_P * C_trig * (3 * π + 1) +
      C_trig * (9 * π ^ 2 + 1) + 1) + 9
  have hKloc_pos : 0 < K_loc := by have := Real.pi_pos; positivity
  have hev : ∀ᶠ c' : ℝ in atTop,
      (8 * Real.log c' + 1 ≤ zetaMin c' / 2) ∧
      (8 * Real.sqrt 2 * Real.log c' * c' ^ (-(12 / 7 : ℝ)) ≤ c' ^ (-1 : ℝ)) ∧
      (2 * c' ^ (-8 : ℝ) ≤ c' ^ (-1 : ℝ)) := by
    have hlog_sub : Tendsto (fun c' : ℝ => (8 * Real.log c' + 1) / (zetaMin c' / 2)) atTop (𝓝 0) := by
      have h1 : ∀ᶠ c' : ℝ in atTop,
          0 ≤ (8 * Real.log c' + 1) / (zetaMin c' / 2) ∧
          (8 * Real.log c' + 1) / (zetaMin c' / 2) ≤ (99 * π) * c' ^ (-(17 / 28 : ℝ)) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc1
        have hc0 : 0 < c' := by linarith
        have hlog : Real.log c' ≤ 4 * c' ^ (1 / 4 : ℝ) := by
          have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc0 (1 / 4 : ℝ))
          rw [Real.log_rpow hc0] at h; linarith only [h]
        have h14 : 1 ≤ c' ^ (1 / 4 : ℝ) := Real.one_le_rpow hc1 (by norm_num)
        refine ⟨by have := Real.log_nonneg hc1; have := zetaMin_pos hc0; positivity, ?_⟩
        have hpow : c' ^ (1 / 4 : ℝ) * c' ^ (-(6 / 7 : ℝ)) = c' ^ (-(17 / 28 : ℝ)) := by
          rw [← Real.rpow_add hc0]; congr 1; norm_num
        calc (8 * Real.log c' + 1) / (zetaMin c' / 2)
            ≤ (33 * c' ^ (1 / 4 : ℝ)) / ((1 / (3 * π)) * c' ^ (6 / 7 : ℝ)) := by
              unfold zetaMin; gcongr
              · linarith only [hlog, h14]
              · exact le_of_eq (by ring)
          _ = (99 * π) * (c' ^ (1 / 4 : ℝ) * c' ^ (-(6 / 7 : ℝ))) := by
              rw [Real.rpow_neg hc0.le]; field_simp [Real.pi_ne_zero]; ring
          _ = (99 * π) * c' ^ (-(17 / 28 : ℝ)) := by rw [hpow]
      have h0 : Tendsto (fun c' : ℝ => (99 * π) * c' ^ (-(17 / 28 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17 / 28)).const_mul (99 * π)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
        (Eventually.mono h1 fun _ h => h.1) (Eventually.mono h1 fun _ h => h.2)
    have hlog2 : Tendsto (fun c' : ℝ => 8 * Real.sqrt 2 * Real.log c' * c' ^ (-(5 / 7 : ℝ))) atTop (𝓝 0) := by
      have h1 : ∀ᶠ c' : ℝ in atTop,
          0 ≤ 8 * Real.sqrt 2 * Real.log c' * c' ^ (-(5 / 7 : ℝ)) ∧
          8 * Real.sqrt 2 * Real.log c' * c' ^ (-(5 / 7 : ℝ)) ≤
            32 * Real.sqrt 2 * c' ^ (-(13 / 28 : ℝ)) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc1
        have hc0 : 0 < c' := by linarith
        have hlog : Real.log c' ≤ 4 * c' ^ (1 / 4 : ℝ) := by
          have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc0 (1 / 4 : ℝ))
          rw [Real.log_rpow hc0] at h; linarith only [h]
        refine ⟨by have := Real.log_nonneg hc1; positivity, ?_⟩
        have hpow : c' ^ (1 / 4 : ℝ) * c' ^ (-(5 / 7 : ℝ)) = c' ^ (-(13 / 28 : ℝ)) := by
          rw [← Real.rpow_add hc0]; congr 1; norm_num
        calc 8 * Real.sqrt 2 * Real.log c' * c' ^ (-(5 / 7 : ℝ))
            ≤ 8 * Real.sqrt 2 * (4 * c' ^ (1 / 4 : ℝ)) * c' ^ (-(5 / 7 : ℝ)) := by gcongr
          _ = 32 * Real.sqrt 2 * (c' ^ (1 / 4 : ℝ) * c' ^ (-(5 / 7 : ℝ))) := by ring
          _ = 32 * Real.sqrt 2 * c' ^ (-(13 / 28 : ℝ)) := by rw [hpow]
      have h0 : Tendsto (fun c' : ℝ => 32 * Real.sqrt 2 * c' ^ (-(13 / 28 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 13 / 28)).const_mul (32 * Real.sqrt 2)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
        (Eventually.mono h1 fun _ h => h.1) (Eventually.mono h1 fun _ h => h.2)
    have hev1 : ∀ᶠ c' : ℝ in atTop, 8 * Real.log c' + 1 ≤ zetaMin c' / 2 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), hlog_sub.eventually (Iic_mem_nhds zero_lt_one)] with
        c' hc0 hdiv
      exact (div_le_one (div_pos (zetaMin_pos hc0) zero_lt_two)).mp hdiv
    have hev2 : ∀ᶠ c' : ℝ in atTop, 8 * Real.sqrt 2 * Real.log c' * c' ^ (-(12 / 7 : ℝ)) ≤ c' ^ (-1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), hlog2.eventually (Iic_mem_nhds zero_lt_one)] with
        c' hc0 hle
      have hpow : c' ^ (-(12 / 7 : ℝ)) = c' ^ (-(5 / 7 : ℝ)) * c' ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      rw [hpow, ← mul_assoc]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hc0.le _) hle
    have hev3 : ∀ᶠ c' : ℝ in atTop, 2 * c' ^ (-8 : ℝ) ≤ c' ^ (-1 : ℝ) := by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with c' hc2
      have hc0 : 0 < c' := by linarith
      have hpow : c' ^ (-8 : ℝ) = c' ^ (-7 : ℝ) * c' ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have h7 : 2 * c' ^ (-7 : ℝ) ≤ 1 := by
        rw [Real.rpow_neg hc0.le, show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          ← div_eq_mul_inv, div_le_one (pow_pos hc0 7)]
        have hc2_pow : (2 : ℝ) ≤ 2 ^ 7 := by norm_num
        exact hc2_pow.trans (pow_le_pow_left₀ (by norm_num) hc2 7)
      rw [hpow, ← mul_assoc]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hc0.le _) h7
    exact hev1.and (hev2.and hev3)
  obtain ⟨c_ev, hc_ev⟩ := eventually_atTop.mp hev
  let c_F : ℝ := max (max 10000 c_T) c_ev
  refine ⟨c_F, K_loc, le_trans (le_max_left _ _) (le_max_left _ _), hKloc_pos,
    fun {c' R} hc' hR {h} hh_meas hh_nn hh_int => ?_⟩
  have hc10000 : 10000 ≤ c' := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hc'
  have hcT' : c_T ≤ c' := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hc'
  have hc_ev' : c_ev ≤ c' := (le_max_right _ _).trans hc'
  have hc0 : 0 < c' := by linarith
  have hc1 : 1 < c' := by linarith
  obtain ⟨hsmall, hpows1, hpows2⟩ := hc_ev c' hc_ev'
  obtain ⟨P1, P2, hcont_P1, hP_pt, hP_cmp⟩ := hP_all hcT' hR
  have hP_cont : ContinuousOn (lowerPζ c' R) (Ici (zetaMin c' / 2)) := fun z hz =>
    (hP_pt hz).2.1.continuousAt.continuousWithinAt
  have hloc : ∀ {ζ : ℝ}, boasZetaStar c' + 8 * Real.log c' + 1 / 2 ≤ ζ →
      |(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - goodL0 c' (boasPhi0 c') z < ζ ∧
            ζ ≤ z + goodL0 c' (boasPhi0 c') z},
          gaussW c' (z - ζ) * boasA c' R ζ z) - boasA c' R ζ ζ| ≤
        K_loc * lowerPζ c' R ζ * c' ^ (-1 : ℝ) := fun {ζ} hζ =>
    boasA_local_error hc10000 hCP hCtrig hsmall ⟨hpows1, hpows2⟩
      ⟨P1, P2, hcont_P1, hP_pt, hP_cmp⟩ (hT_all hc10000) hζ
  let μ : Measure ℝ := volume.restrict (Ici (zetaMin c'))
  let ν : Measure ℝ := volume.restrict (Ici (boasZetaStar c'))
  let φ₀ := boasPhi0 c'
  let L₀ := goodL0 c' φ₀
  let F : ℝ × ℝ → ℝ := fun p =>
    if p.2 - L₀ p.2 < p.1 ∧ p.1 ≤ p.2 + L₀ p.2 then gaussW c' (p.2 - p.1) * boasA c' R p.1 p.2 * h p.1 else 0
  let M : ℝ × ℝ → ℝ := fun p => 6 * gaussW c' (p.2 - p.1) * (lowerPζ c' R p.1 * h p.1)
  have hS_win : MeasurableSet {p : ℝ × ℝ | p.2 - L₀ p.2 < p.1 ∧ p.1 ≤ p.2 + L₀ p.2} := by
    have hL0m : Measurable L₀ := measurable_goodL0 c' (measurable_boasPhi0 hc10000)
    have h1 : MeasurableSet {p : ℝ × ℝ | p.2 - L₀ p.2 < p.1} :=
      measurableSet_lt (measurable_snd.sub (hL0m.comp measurable_snd)) measurable_fst
    have h2 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2 + L₀ p.2} :=
      measurableSet_le measurable_fst (measurable_snd.add (hL0m.comp measurable_snd))
    exact h1.inter h2
  have hM_int : Integrable M (μ.prod ν) := by
    have hM_meas : AEStronglyMeasurable M (μ.prod ν) := by
      have hg : Measurable fun p : ℝ × ℝ => 6 * gaussW c' (p.2 - p.1) :=
        ((by unfold gaussW; fun_prop : Continuous fun p : ℝ × ℝ => 6 * gaussW c' (p.2 - p.1)).measurable)
      have hPh : AEStronglyMeasurable (fun ζ => lowerPζ c' R ζ * h ζ) μ := hh_int.aestronglyMeasurable
      exact (hg.aestronglyMeasurable.mul hPh.comp_fst).congr (Eventually.of_forall fun p => by dsimp [M])
    refine (integrable_prod_iff hM_meas).mpr ⟨?_, ?_⟩
    · refine ae_restrict_of_forall_mem measurableSet_Ici fun ζ _ => ?_
      have hg_s : Integrable (fun z => gaussW c' (z - ζ)) ν :=
        ((integrable_gaussW hc1).comp_sub_right ζ).integrableOn
      exact (hg_s.const_mul (6 * (lowerPζ c' R ζ * h ζ))).congr (Eventually.of_forall fun z => by
        dsimp [M]; ring)
    · have hbd : ∀ ζ ∈ Ici (zetaMin c'), (∫ z, ‖M (ζ, z)‖ ∂ν) ≤ 6 * (lowerPζ c' R ζ * h ζ) := fun ζ hζ => by
        have hζ_min : zetaMin c' / 2 ≤ ζ := (half_le_self (zetaMin_pos hc0).le).trans hζ
        have hPnn : 0 ≤ lowerPζ c' R ζ := (hP_pt hζ_min).1.le
        have hhnn : 0 ≤ h ζ := hh_nn hζ
        have heq_norm : (fun z => ‖M (ζ, z)‖) = fun z => 6 * (lowerPζ c' R ζ * h ζ) * gaussW c' (z - ζ) := by
          ext z; dsimp [M]
          have hnn : 0 ≤ 6 * gaussW c' (z - ζ) * (lowerPζ c' R ζ * h ζ) :=
            mul_nonneg (mul_nonneg (by norm_num) (gaussW_nonneg _ _)) (mul_nonneg hPnn hhnn)
          rw [abs_of_nonneg hnn]
          ring
        rw [heq_norm, integral_const_mul]
        have hle1 : (∫ z, gaussW c' (z - ζ) ∂ν) ≤ ∫ z : ℝ, gaussW c' (z - ζ) :=
          setIntegral_le_integral ((integrable_gaussW hc1).comp_sub_right ζ)
            (Eventually.of_forall fun z => gaussW_nonneg _ _)
        have h1 : ∫ z : ℝ, gaussW c' (z - ζ) = 1 := by
          rw [integral_sub_right_eq_self (gaussW c') ζ, integral_gaussW hc1]
        rw [h1] at hle1
        calc 6 * (lowerPζ c' R ζ * h ζ) * (∫ z, gaussW c' (z - ζ) ∂ν)
            ≤ 6 * (lowerPζ c' R ζ * h ζ) * 1 := by gcongr
          _ = 6 * (lowerPζ c' R ζ * h ζ) := mul_one _
      have hmeas_norm : AEStronglyMeasurable (fun ζ => ∫ z, ‖M (ζ, z)‖ ∂ν) μ :=
        hM_meas.norm.integral_prod_right'
      refine (hh_int.integrable.const_mul 6).mono' hmeas_norm ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with ζ hζ
      have hζ_min : zetaMin c' / 2 ≤ ζ := (half_le_self (zetaMin_pos hc0).le).trans hζ
      have hPnn : 0 ≤ lowerPζ c' R ζ := (hP_pt hζ_min).1.le
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hbd ζ hζ
  have hF_meas : AEStronglyMeasurable F (μ.prod ν) := by
    have hg : Measurable fun p : ℝ × ℝ => gaussW c' (p.2 - p.1) :=
      (by unfold gaussW; fun_prop : Continuous fun p : ℝ × ℝ => gaussW c' (p.2 - p.1)).measurable
    have hA_cut := boasA_cut_measurable hc10000 hP_cont
    let F_cut : ℝ × ℝ → ℝ := fun p =>
      (if p.2 - L₀ p.2 < p.1 ∧ p.1 ≤ p.2 + L₀ p.2 then gaussW c' (p.2 - p.1) *
        (if boasZetaStar c' ≤ p.2 then boasA c' R p.1 p.2 else 0) else 0) * h p.1
    have hleft_meas : Measurable fun p : ℝ × ℝ =>
        if p.2 - L₀ p.2 < p.1 ∧ p.1 ≤ p.2 + L₀ p.2 then gaussW c' (p.2 - p.1) *
          (if boasZetaStar c' ≤ p.2 then boasA c' R p.1 p.2 else 0) else 0 :=
      Measurable.ite hS_win (hg.mul hA_cut) measurable_const
    have hF_cut_meas : AEStronglyMeasurable F_cut (μ.prod ν) :=
      hleft_meas.aestronglyMeasurable.mul hh_meas.comp_fst
    refine hF_cut_meas.congr ?_
    have hprod_ae : ∀ᵐ p : ℝ × ℝ ∂(μ.prod ν), p.2 ∈ Ici (boasZetaStar c') := by
      have ha : ∀ᵐ z ∂ν, z ∈ Ici (boasZetaStar c') := ae_restrict_mem measurableSet_Ici
      exact Measure.quasiMeasurePreserving_snd.ae ha
    filter_upwards [hprod_ae] with p hp2
    have hbz : boasZetaStar c' ≤ p.2 := hp2
    dsimp [F_cut, F]
    by_cases hwin : p.2 - L₀ p.2 < p.1 ∧ p.1 ≤ p.2 + L₀ p.2
    · simp [hwin, hbz]
    · simp [hwin]
  have hF_int : Integrable F (μ.prod ν) := by
    refine hM_int.mono' hF_meas ?_
    have hprod_ae : ∀ᵐ p : ℝ × ℝ ∂(μ.prod ν),
        p.1 ∈ Ici (zetaMin c') ∧ p.2 ∈ Ici (boasZetaStar c') :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)).and
        (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ici))
    filter_upwards [hprod_ae] with p ⟨hp1, hp2⟩
    have h1_min : zetaMin c' / 2 ≤ p.1 := (half_le_self (zetaMin_pos hc0).le).trans hp1
    have h2_min : zetaMin c' / 2 ≤ p.2 := by
      have hbz : boasZetaStar c' ≤ p.2 := hp2
      unfold boasZetaStar at hbz
      exact (half_le_self (zetaMin_pos hc0).le).trans (by linarith only [hbz, Real.log_pos hc1])
    have hP1_nn : 0 ≤ lowerPζ c' R p.1 := (hP_pt h1_min).1.le
    have hP2_nn : 0 ≤ lowerPζ c' R p.2 := (hP_pt h2_min).1.le
    have hh_nonneg : 0 ≤ h p.1 := hh_nn hp1
    dsimp [F, M]
    have hM_nn : 0 ≤ 6 * gaussW c' (p.2 - p.1) * (lowerPζ c' R p.1 * h p.1) :=
      mul_nonneg (mul_nonneg (by norm_num) (gaussW_nonneg _ _)) (mul_nonneg hP1_nn hh_nonneg)
    split_ifs with hwin
    · have hL0 := goodL0_bounds_and_poles c' φ₀ p.2
      have hdist : |p.2 - p.1| ≤ 8 * Real.log c' + 1 := by
        rw [abs_le]; constructor <;> (dsimp [L₀] at hwin; linarith only [hwin.1, hwin.2, hL0.2.1])
      have hcmp : lowerPζ c' R p.2 ≤ 2 * lowerPζ c' R p.1 := hP_cmp h2_min h1_min hdist
      have hz2_pos : 0 < p.2 := lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) h2_min
      have hA_bd : |boasA c' R p.1 p.2| ≤ 6 * lowerPζ c' R p.1 := by
        linarith only [abs_boasA_le (ζ := p.1) hc0 hz2_pos hP2_nn, hcmp]
      rw [abs_mul, abs_mul, abs_of_nonneg (gaussW_nonneg _ _), abs_of_nonneg hh_nonneg]
      calc gaussW c' (p.2 - p.1) * |boasA c' R p.1 p.2| * h p.1
          ≤ gaussW c' (p.2 - p.1) * (6 * lowerPζ c' R p.1) * h p.1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA_bd (gaussW_nonneg _ _)) hh_nonneg
        _ = 6 * gaussW c' (p.2 - p.1) * (lowerPζ c' R p.1 * h p.1) := by ring
    · rw [abs_zero]
      exact hM_nn
  -- Identify both iterated integrals
  have hfrozen_eq : ∀ z ∈ Ici (boasZetaStar c'), (∫ ζ, F (ζ, z) ∂μ) = boasFrozenInt c' R h z := by
    intro z hz
    have hz1 : boasZetaStar c' ≤ z := hz
    have hL0 := goodL0_bounds_and_poles c' φ₀ z
    have hlo : zetaMin c' ≤ z - L₀ z := by
      unfold boasZetaStar at hz1
      dsimp [L₀]; linarith only [hz1, hL0.2.1]
    have hle : z - L₀ z ≤ z + L₀ z := by
      have := Real.log_pos hc1
      dsimp [L₀]; linarith only [hL0.1, this]
    have hIoc_sub : Ioc (z - L₀ z) (z + L₀ z) ⊆ Ici (zetaMin c') := fun ζ hζ =>
      hlo.trans hζ.1.le
    have heq_fun : (fun ζ => F (ζ, z)) =
        (Ioc (z - L₀ z) (z + L₀ z)).indicator (fun ζ => gaussW c' (z - ζ) * boasA c' R ζ z * h ζ) := by
      ext ζ; dsimp [F, Set.indicator, L₀]; simp [mem_Ioc]
    dsimp [μ]
    rw [heq_fun, setIntegral_indicator measurableSet_Ioc, inter_eq_self_of_subset_right hIoc_sub,
      ← intervalIntegral.integral_of_le hle]
    rfl
  have hFrozen_int : IntegrableOn (boasFrozenInt c' R h) (Ici (boasZetaStar c')) := by
    have hint_right : Integrable (fun z => ∫ ζ, F (ζ, z) ∂μ) ν :=
      hF_int.integral_prod_right
    exact hint_right.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      exact hfrozen_eq z hz)
  have hswap := integral_integral_swap (f := fun ζ z => F (ζ, z)) hF_int
  have hlhs : (∫ z in Ici (boasZetaStar c'), boasFrozenInt c' R h z) =
      ∫ z, (∫ ζ, F (ζ, z) ∂μ) ∂ν := by
    refine setIntegral_congr_ae measurableSet_Ici ?_
    filter_upwards with z hz
    exact (hfrozen_eq z hz).symm
  have hrhs_in : ∀ ζ ∈ Ici (zetaMin c'),
      (∫ z, F (ζ, z) ∂ν) = (∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
        gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ := by
    intro ζ _
    have hL0m : Measurable L₀ := measurable_goodL0 c' (measurable_boasPhi0 hc10000)
    have hm_win : MeasurableSet {z : ℝ | z - L₀ z < ζ ∧ ζ ≤ z + L₀ z} :=
      (measurableSet_lt (measurable_id.sub hL0m) measurable_const).inter
        (measurableSet_le measurable_const (measurable_id.add hL0m))
    have heq_f : (fun z => F (ζ, z)) =
        fun z => ({z : ℝ | z - L₀ z < ζ ∧ ζ ≤ z + L₀ z}.indicator
          (fun z => gaussW c' (z - ζ) * boasA c' R ζ z) z) * h ζ := by
      ext z; dsimp [F, Set.indicator]; split_ifs <;> simp [*]
    rw [heq_f, integral_mul_const]
    congr 1
    dsimp [ν]
    rw [setIntegral_indicator hm_win]
    congr 1
  have hswap_eq : (∫ z in Ici (boasZetaStar c'), boasFrozenInt c' R h z) =
      ∫ ζ in Ici (zetaMin c'),
        (∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
          gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ := by
    rw [hlhs, ← hswap]
    refine setIntegral_congr_ae measurableSet_Ici ?_
    filter_upwards with ζ hζ
    exact hrhs_in ζ hζ
  -- Subtract `∫_{ζ ≥ ζ_min} boasA c' R ζ ζ * h ζ`
  have hAζ_int : IntegrableOn (fun ζ => boasA c' R ζ ζ * h ζ) (Ici (zetaMin c')) := by
    have hmeas_A : ContinuousOn (fun ζ => boasA c' R ζ ζ) (Ici (zetaMin c')) := by
      obtain ⟨_, _, hWθ⟩ := lowerWeps_unwrappedTheta_deriv_bounds
      obtain ⟨_, _, _, _, hspec⟩ := hWθ hc10000
      have hW_c : ContinuousOn (fun ζ => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' ζ))) (Ici (zetaMin c')) :=
        fun ζ hζ => (hspec ((zetaMin_pos hc0).trans_le hζ)).1.continuousAt.continuousWithinAt
      have hθ_c : ContinuousOn (fun ζ => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' ζ)) (Ici (zetaMin c')) :=
        fun ζ hζ => (hspec ((zetaMin_pos hc0).trans_le hζ)).2.2.1.continuousAt.continuousWithinAt
      have hP_c : ContinuousOn (lowerPζ c' R) (Ici (zetaMin c')) :=
        hP_cont.mono fun ζ hζ => (half_le_self (zetaMin_pos hc0).le).trans hζ
      unfold boasA
      exact hP_c.mul (continuousOn_const.sub ((hW_c.const_mul 2).mul
        (Real.continuous_sin.comp_continuousOn ((continuousOn_const.mul continuousOn_id).sub hθ_c))))
    refine (hh_int.const_mul 3).mono' ((hmeas_A.aestronglyMeasurable measurableSet_Ici).mul hh_meas) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with ζ hζ
    have hζ_min : zetaMin c' / 2 ≤ ζ := (half_le_self (zetaMin_pos hc0).le).trans hζ
    have hζ_pos : 0 < ζ := (zetaMin_pos hc0).trans_le hζ
    have hPnn : 0 ≤ lowerPζ c' R ζ := (hP_pt hζ_min).1.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh_nn hζ)]
    calc |boasA c' R ζ ζ| * h ζ ≤ (3 * lowerPζ c' R ζ) * h ζ :=
          mul_le_mul_of_nonneg_right (abs_boasA_le hc0 hζ_pos hPnn) (hh_nn hζ)
      _ = 3 * (lowerPζ c' R ζ * h ζ) := by ring
  have hswap_int : IntegrableOn (fun ζ => (∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧
        z - L₀ z < ζ ∧ ζ ≤ z + L₀ z}, gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ) (Ici (zetaMin c')) := by
    have hint_left : Integrable (fun ζ => ∫ z, F (ζ, z) ∂ν) μ := hF_int.integral_prod_left
    exact hint_left.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with ζ hζ
      exact hrhs_in ζ hζ)
  let ζ₁ : ℝ := boasZetaStar c' + 8 * Real.log c' + 1 / 2
  have hζ₁_ge : zetaMin c' ≤ ζ₁ := by
    dsimp [ζ₁]; unfold boasZetaStar; linarith only [Real.log_pos hc1]
  have hζ₁_le : ζ₁ ≤ 2 * zetaMin c' := by
    dsimp [ζ₁]; unfold boasZetaStar; linarith only [hsmall]
  have hdiff_sub : |(∫ z in Ici (boasZetaStar c'), boasFrozenInt c' R h z) -
        ∫ ζ in Ici (zetaMin c'), boasA c' R ζ ζ * h ζ| ≤
      K_loc * c' ^ (-1 : ℝ) * (∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ) +
        9 * ∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ := by
    rw [hswap_eq, ← integral_sub hswap_int hAζ_int]
    have habs_int := norm_integral_le_integral_norm
      (f := fun ζ => (∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
        gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ)
      (μ := volume.restrict (Ici (zetaMin c')))
    have hsp_ici : Ici (zetaMin c') = Ico (zetaMin c') ζ₁ ∪ Ici ζ₁ :=
      (Ico_union_Ici_eq_Ici hζ₁_ge).symm
    have hdisj : Disjoint (Ico (zetaMin c') ζ₁) (Ici ζ₁) :=
      Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h2 h1.2
    have hnorm_int : IntegrableOn (fun ζ => ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
        gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ‖) (Ici (zetaMin c')) :=
      (hswap_int.sub hAζ_int).norm
    have hsplit_norm :
        ∫ ζ in Ici (zetaMin c'), ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
          gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ‖ =
        (∫ ζ in Ico (zetaMin c') ζ₁, ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
          gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ‖) +
        ∫ ζ in Ici ζ₁, ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
          gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ‖ := by
      nth_rewrite 1 [hsp_ici]
      exact setIntegral_union hdisj measurableSet_Ici (hnorm_int.mono_set Ico_subset_Ici_self)
        (hnorm_int.mono_set (Ici_subset_Ici.mpr hζ₁_ge))
    have htail_bd :
        ∫ ζ in Ici ζ₁, ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
          gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ‖ ≤
        K_loc * c' ^ (-1 : ℝ) * ∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ := by
      have h1 :
          ∫ ζ in Ici ζ₁, ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
            gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ‖ ≤
          ∫ ζ in Ici ζ₁, K_loc * c' ^ (-1 : ℝ) * (lowerPζ c' R ζ * h ζ) := by
        refine setIntegral_mono_on (hnorm_int.mono_set (Ici_subset_Ici.mpr hζ₁_ge))
          ((hh_int.mono_set (Ici_subset_Ici.mpr hζ₁_ge)).const_mul _) measurableSet_Ici fun ζ hζ => ?_
        have hζ_min : zetaMin c' ≤ ζ := hζ₁_ge.trans hζ
        have hh_nonneg : 0 ≤ h ζ := hh_nn hζ_min
        have hfact : (∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
              gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ =
            ((∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
              gaussW c' (z - ζ) * boasA c' R ζ z) - boasA c' R ζ ζ) * h ζ := by ring
        rw [Real.norm_eq_abs, hfact, abs_mul, abs_of_nonneg hh_nonneg]
        have hpt := hloc hζ
        dsimp [K_loc] at hpt ⊢
        calc |(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
                gaussW c' (z - ζ) * boasA c' R ζ z) - boasA c' R ζ ζ| * h ζ
            ≤ (K_loc * lowerPζ c' R ζ * c' ^ (-1 : ℝ)) * h ζ := mul_le_mul_of_nonneg_right hpt hh_nonneg
          _ = K_loc * c' ^ (-1 : ℝ) * (lowerPζ c' R ζ * h ζ) := by ring
      have h2 : ∫ ζ in Ici ζ₁, K_loc * c' ^ (-1 : ℝ) * (lowerPζ c' R ζ * h ζ) ≤
          ∫ ζ in Ici (zetaMin c'), K_loc * c' ^ (-1 : ℝ) * (lowerPζ c' R ζ * h ζ) := by
        refine setIntegral_mono_set (hh_int.const_mul _) ?_ (Eventually.of_forall (Ici_subset_Ici.mpr hζ₁_ge))
        filter_upwards [ae_restrict_mem measurableSet_Ici] with ζ hζ
        have hPnn := (hP_pt ((half_le_self (zetaMin_pos hc0).le).trans hζ)).1.le
        exact mul_nonneg (by positivity) (mul_nonneg hPnn (hh_nn hζ))
      exact (h1.trans h2).trans_eq (integral_const_mul _ _)
    have hearly_bd :
        ∫ ζ in Ico (zetaMin c') ζ₁, ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
          gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ‖ ≤
        9 * ∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ := by
      have h1 :
          ∫ ζ in Ico (zetaMin c') ζ₁, ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
            gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ‖ ≤
          ∫ ζ in Ico (zetaMin c') ζ₁, 9 * (lowerPζ c' R ζ * h ζ) := by
        refine setIntegral_mono_on (hnorm_int.mono_set Ico_subset_Ici_self)
          ((hh_int.mono_set Ico_subset_Ici_self).const_mul 9) measurableSet_Ico fun ζ hζ => ?_
        have hζ_min : zetaMin c' ≤ ζ := hζ.1
        have hζ_pos : 0 < ζ := (zetaMin_pos hc0).trans_le hζ_min
        have hPnn : 0 ≤ lowerPζ c' R ζ := (hP_pt ((half_le_self (zetaMin_pos hc0).le).trans hζ_min)).1.le
        have hh_nonneg : 0 ≤ h ζ := hh_nn hζ_min
        have hA_pt : |boasA c' R ζ ζ| ≤ 3 * lowerPζ c' R ζ := abs_boasA_le hc0 hζ_pos hPnn
        have hI_pt : |∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
            gaussW c' (z - ζ) * boasA c' R ζ z| ≤ 6 * lowerPζ c' R ζ := by
          set Sζ : Set ℝ := {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z}
          have hSζ_m : MeasurableSet Sζ := by
            have hL0m : Measurable L₀ := measurable_goodL0 c' (measurable_boasPhi0 hc10000)
            exact measurableSet_Ici.inter ((measurableSet_lt (measurable_id.sub hL0m) measurable_const).inter
              (measurableSet_le measurable_const (measurable_id.add hL0m)))
          have hg_s : Integrable (fun z => gaussW c' (z - ζ)) := (integrable_gaussW hc1).comp_sub_right ζ
          have hSζ_cont : ContinuousOn (fun z => gaussW c' (z - ζ) * boasA c' R ζ z) Sζ := by
            have hSζ_sub : Sζ ⊆ Ici (zetaMin c' / 2) := fun z hz => by
              have hbz : boasZetaStar c' ≤ z := hz.1
              unfold boasZetaStar at hbz
              exact (half_le_self (zetaMin_pos hc0).le).trans (by linarith only [hbz, Real.log_pos hc1])
            obtain ⟨_, _, hWθ⟩ := lowerWeps_unwrappedTheta_deriv_bounds
            obtain ⟨_, _, _, _, hspec⟩ := hWθ hc10000
            have hW_c : ContinuousOn (fun z => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z)))
                (Ici (zetaMin c' / 2)) := fun z hz =>
              (hspec (lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) hz)).1.continuousAt.continuousWithinAt
            have hθ_c : ContinuousOn (fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z))
                (Ici (zetaMin c' / 2)) := fun z hz =>
              (hspec (lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) hz)).2.2.1.continuousAt.continuousWithinAt
            have hA_c : ContinuousOn (fun z => boasA c' R ζ z) (Ici (zetaMin c' / 2)) := by
              unfold boasA
              exact hP_cont.mul (continuousOn_const.sub ((hW_c.const_mul 2).mul
                (Real.continuous_sin.comp_continuousOn (continuousOn_const.sub hθ_c))))
            exact ((by unfold gaussW; fun_prop : Continuous fun z => gaussW c' (z - ζ)).continuousOn.mul hA_c).mono hSζ_sub
          have hSζ_int : IntegrableOn (fun z => gaussW c' (z - ζ) * boasA c' R ζ z) Sζ := by
            refine (hg_s.const_mul (6 * lowerPζ c' R ζ)).integrableOn.mono'
              (hSζ_cont.aestronglyMeasurable hSζ_m) ?_
            filter_upwards [ae_restrict_mem hSζ_m] with z hz
            have hbz : boasZetaStar c' ≤ z := hz.1
            have hz_min : zetaMin c' / 2 ≤ z := by
              unfold boasZetaStar at hbz
              exact (half_le_self (zetaMin_pos hc0).le).trans (by linarith only [hbz, Real.log_pos hc1])
            have hz_pos : 0 < z := lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) hz_min
            have hL0 := goodL0_bounds_and_poles c' φ₀ z
            have hdist : |z - ζ| ≤ 8 * Real.log c' + 1 := by
              rw [abs_le]; constructor <;> (dsimp [Sζ, L₀] at hz; linarith only [hz.2.1, hz.2.2, hL0.2.1])
            have hcmp := hP_cmp hz_min ((half_le_self (zetaMin_pos hc0).le).trans hζ_min) hdist
            have hA := abs_boasA_le (ζ := ζ) hc0 hz_pos (hP_pt hz_min).1.le
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussW_nonneg _ _), mul_comm]
            exact mul_le_mul_of_nonneg_right (by linarith only [hA, hcmp]) (gaussW_nonneg _ _)
          have hmono := (norm_integral_le_integral_norm (f := fun z => gaussW c' (z - ζ) * boasA c' R ζ z)
              (μ := volume.restrict Sζ)).trans (setIntegral_mono_on hSζ_int.norm
              (hg_s.const_mul (6 * lowerPζ c' R ζ)).integrableOn hSζ_m fun z hz => by
            have hbz : boasZetaStar c' ≤ z := hz.1
            have hz_min : zetaMin c' / 2 ≤ z := by
              unfold boasZetaStar at hbz
              exact (half_le_self (zetaMin_pos hc0).le).trans (by linarith only [hbz, Real.log_pos hc1])
            have hz_pos : 0 < z := lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) hz_min
            have hL0 := goodL0_bounds_and_poles c' φ₀ z
            have hdist : |z - ζ| ≤ 8 * Real.log c' + 1 := by
              rw [abs_le]; constructor <;> (dsimp [Sζ, L₀] at hz; linarith only [hz.2.1, hz.2.2, hL0.2.1])
            have hcmp := hP_cmp hz_min ((half_le_self (zetaMin_pos hc0).le).trans hζ_min) hdist
            have hA := abs_boasA_le (ζ := ζ) hc0 hz_pos (hP_pt hz_min).1.le
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussW_nonneg _ _), mul_comm (gaussW c' (z - ζ))]
            exact mul_le_mul_of_nonneg_right (by linarith only [hA, hcmp]) (gaussW_nonneg _ _))
          have hfull : ∫ z in Sζ, 6 * lowerPζ c' R ζ * gaussW c' (z - ζ) ≤
              6 * lowerPζ c' R ζ * ∫ z : ℝ, gaussW c' (z - ζ) := by
            rw [← integral_const_mul]
            exact setIntegral_le_integral (hg_s.const_mul (6 * lowerPζ c' R ζ))
              (Eventually.of_forall fun z => mul_nonneg (by positivity) (gaussW_nonneg _ _))
          have h1_eq : ∫ z : ℝ, gaussW c' (z - ζ) = 1 := by
            rw [integral_sub_right_eq_self (gaussW c') ζ, integral_gaussW hc1]
          rw [h1_eq, mul_one] at hfull
          exact hmono.trans hfull
        have hfact : (∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
              gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ - boasA c' R ζ ζ * h ζ =
            ((∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
              gaussW c' (z - ζ) * boasA c' R ζ z) - boasA c' R ζ ζ) * h ζ := by ring
        rw [Real.norm_eq_abs, hfact, abs_mul, abs_of_nonneg hh_nonneg]
        have hsub_pt : |(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z},
              gaussW c' (z - ζ) * boasA c' R ζ z) - boasA c' R ζ ζ| ≤ 9 * lowerPζ c' R ζ := by
          exact (abs_sub _ _).trans (by linarith only [hI_pt, hA_pt])
        calc _ ≤ (9 * lowerPζ c' R ζ) * h ζ := mul_le_mul_of_nonneg_right hsub_pt hh_nonneg
          _ = 9 * (lowerPζ c' R ζ * h ζ) := by ring
      have h2 : ∫ ζ in Ico (zetaMin c') ζ₁, 9 * (lowerPζ c' R ζ * h ζ) ≤
          ∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), 9 * (lowerPζ c' R ζ * h ζ) := by
        refine setIntegral_mono_set ((hh_int.mono_set Icc_subset_Ici_self).const_mul 9) ?_
          (Eventually.of_forall fun ζ hζ => ⟨hζ.1, hζ.2.le.trans hζ₁_le⟩)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with ζ hζ
        have hPnn := (hP_pt ((half_le_self (zetaMin_pos hc0).le).trans hζ.1)).1.le
        exact mul_nonneg (by norm_num) (mul_nonneg hPnn (hh_nn hζ.1))
      exact (h1.trans h2).trans_eq (integral_const_mul _ _)
    have habs_tot :
        |∫ ζ in Ici (zetaMin c'), (∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧
            z - L₀ z < ζ ∧ ζ ≤ z + L₀ z}, gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ -
            boasA c' R ζ ζ * h ζ| ≤
          K_loc * c' ^ (-1 : ℝ) * (∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ) +
            9 * ∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ := by
      calc |∫ ζ in Ici (zetaMin c'), (∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧
              z - L₀ z < ζ ∧ ζ ≤ z + L₀ z}, gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ -
              boasA c' R ζ ζ * h ζ|
          ≤ ∫ ζ in Ici (zetaMin c'), ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧
              z - L₀ z < ζ ∧ ζ ≤ z + L₀ z}, gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ -
              boasA c' R ζ ζ * h ζ‖ := (Real.norm_eq_abs _).symm.trans_le habs_int
        _ = (∫ ζ in Ico (zetaMin c') ζ₁, ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧
              z - L₀ z < ζ ∧ ζ ≤ z + L₀ z}, gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ -
              boasA c' R ζ ζ * h ζ‖) +
            ∫ ζ in Ici ζ₁, ‖(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧
              z - L₀ z < ζ ∧ ζ ≤ z + L₀ z}, gaussW c' (z - ζ) * boasA c' R ζ z) * h ζ -
              boasA c' R ζ ζ * h ζ‖ := hsplit_norm
        _ ≤ 9 * (∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ) +
            K_loc * c' ^ (-1 : ℝ) * (∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ) :=
            add_le_add hearly_bd htail_bd
        _ = K_loc * c' ^ (-1 : ℝ) * (∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ) +
            9 * ∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ := by ring
    exact habs_tot
  exact ⟨hFrozen_int, hdiff_sub⟩

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.boas_freezing_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.boas_freezing_estimate

