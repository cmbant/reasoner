/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_3_Helpers

/-!
# Section 4.3 Box Helpers (`s4:4.3`): Negative-Mass Box Concentration and `s4:4.1` Error Bound

Proves:
1. `box_cov_integral_eq`: exact `(2 ε)`-Jacobian change of variables on `Icc (-M) M ×ˢ Icc (-W) W`.
2. `spin_neg_mass_box_lower`: uniform `1 / 32` lower bound on the integrated negative mass over
   the near-tip parabolic box (`s4:eO3.4`).
3. `spinHProfile_err_integral_le`: `L¹` truncation error bound (`s4:eO3.5`) over `Icc (-M) M`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

private lemma box_cov_integral_eq {ε M W : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hW : 0 ≤ W)
    {F : ℝ × ℝ → ℝ} (hF_cont : Continuous F) (hF_nn : ∀ p : ℝ × ℝ, 0 ≤ F p) :
    let B : Set (ℝ × ℝ) := Icc (-M) M ×ˢ Icc (-W) W
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
      { toFun := fun p => (xiStar + ε * p.1 + p.2, xiStar + ε * p.1 - p.2)
        invFun := fun q => (((q.1 + q.2) / 2 - xiStar) / ε, (q.1 - q.2) / 2)
        left_inv := fun ⟨u, d⟩ => by ext <;> dsimp <;> field_simp [hε.ne'] <;> ring
        right_inv := fun ⟨x, y⟩ => by ext <;> dsimp <;> field_simp [hε.ne'] <;> ring
        measurable_toFun :=
          ((measurable_const.add (measurable_const.mul measurable_fst)).add measurable_snd).prodMk
            ((measurable_const.add (measurable_const.mul measurable_fst)).sub measurable_snd)
        measurable_invFun :=
          ((((measurable_fst.add measurable_snd).div_const 2).sub measurable_const).div_const ε).prodMk
            ((measurable_fst.sub measurable_snd).div_const 2) }
    (∫ u in Icc (-M) M, ε * ∫ d in Icc (-W) W, F (xiStar + ε * u + d, xiStar + ε * u - d)) =
      (1 / 2 : ℝ) * ∫ y in e '' B, F y := by
  intro B e
  let e1 : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun p => (xiStar + ε * p.1, p.2)
      invFun := fun q => ((q.1 - xiStar) / ε, q.2)
      left_inv := fun ⟨u, d⟩ => by ext <;> dsimp <;> field_simp [hε.ne'] <;> ring
      right_inv := fun ⟨x, d⟩ => by ext <;> dsimp <;> field_simp [hε.ne'] <;> ring
      measurable_toFun := (measurable_const.add (measurable_const.mul measurable_fst)).prodMk measurable_snd
      measurable_invFun := ((measurable_fst.sub measurable_const).div_const ε).prodMk measurable_snd }
  let e2 : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun q => (q.1 + q.2, q.1 - q.2)
      invFun := fun y => ((y.1 + y.2) / 2, (y.1 - y.2) / 2)
      left_inv := fun ⟨x, d⟩ => by ext <;> dsimp <;> ring
      right_inv := fun ⟨a, b⟩ => by ext <;> dsimp <;> ring
      measurable_toFun := (measurable_fst.add measurable_snd).prodMk (measurable_fst.sub measurable_snd)
      measurable_invFun := ((measurable_fst.add measurable_snd).div_const 2).prodMk
        ((measurable_fst.sub measurable_snd).div_const 2) }
  have hmB : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have he_img : e '' B = e.symm ⁻¹' B := e.toEquiv.image_eq_preimage_symm B
  have hmS : MeasurableSet (e '' B) := by rw [he_img]; exact e.symm.measurable hmB
  have hK_B : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have he_cont : Continuous e :=
    ((continuous_const.add (continuous_const.mul continuous_fst)).add continuous_snd).prodMk
      ((continuous_const.add (continuous_const.mul continuous_fst)).sub continuous_snd)
  have hS_int : IntegrableOn F (e '' B) :=
    hF_cont.continuousOn.integrableOn_compact (hK_B.image he_cont)
  let G_out : ℝ → ℝ := fun u => ε * ∫ d in Icc (-W) W, F (xiStar + ε * u + d, xiStar + ε * u - d)
  have hG_cont : Continuous G_out := by
    refine continuous_const.mul ?_
    have hF_u : Continuous (Function.uncurry fun u d : ℝ => F (xiStar + ε * u + d, xiStar + ε * u - d)) :=
      hF_cont.comp he_cont
    have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hF_u (-W) W
    simpa only [intervalIntegral.integral_of_le (by linarith : -W ≤ W),
      MeasureTheory.restrict_Ioc_eq_restrict_Icc] using hc
  have hG_int : IntegrableOn G_out (Icc (-M) M) := hG_cont.continuousOn.integrableOn_Icc
  have hG_nn : ∀ u : ℝ, 0 ≤ G_out u := fun u =>
    mul_nonneg hε.le (setIntegral_nonneg measurableSet_Icc fun d _ => hF_nn _)
  have hLHS_ofReal : ENNReal.ofReal (∫ u in Icc (-M) M, G_out u) =
      ∫⁻ u in Icc (-M) M, ENNReal.ofReal (G_out u) :=
    ofReal_integral_eq_lintegral_ofReal hG_int (Eventually.of_forall fun u => hG_nn u)
  have hinner_ofReal : ∀ u : ℝ, ENNReal.ofReal (G_out u) =
      ENNReal.ofReal ε * ∫⁻ d in Icc (-W) W, ENNReal.ofReal (F (xiStar + ε * u + d, xiStar + ε * u - d)) := by
    intro u
    dsimp [G_out]
    rw [ENNReal.ofReal_mul hε.le]
    congr 1
    have hint_d : IntegrableOn (fun d : ℝ => F (xiStar + ε * u + d, xiStar + ε * u - d)) (Icc (-W) W) :=
      (hF_cont.comp (((continuous_const.add continuous_id).prodMk
        (continuous_const.sub continuous_id)))).continuousOn.integrableOn_Icc
    exact ofReal_integral_eq_lintegral_ofReal hint_d (Eventually.of_forall fun _ => hF_nn _)
  have hLHS_lint : ENNReal.ofReal (∫ u in Icc (-M) M, G_out u) =
      ENNReal.ofReal ε * ∫⁻ p : ℝ × ℝ,
        B.indicator (fun p => ENNReal.ofReal (F (e p))) p := by
    rw [hLHS_ofReal]
    simp_rw [hinner_ofReal]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [← lintegral_indicator measurableSet_Icc, Measure.volume_eq_prod, lintegral_prod]
    · refine lintegral_congr fun u => ?_
      by_cases hu : u ∈ Icc (-M) M
      · rw [Set.indicator_of_mem hu, ← lintegral_indicator measurableSet_Icc]
        refine lintegral_congr fun d => ?_
        by_cases hd : d ∈ Icc (-W) W
        · rw [Set.indicator_of_mem hd, Set.indicator_of_mem (⟨hu, hd⟩ : (u, d) ∈ B)]; rfl
        · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem (fun (h : (u, d) ∈ B) => hd h.2)]
      · rw [Set.indicator_of_notMem hu]
        have hzero : ∀ d : ℝ, B.indicator (fun p => ENNReal.ofReal (F (e p))) (u, d) = 0 :=
          fun d => Set.indicator_of_notMem (fun (h : (u, d) ∈ B) => hu h.1) _
        simp_rw [hzero, lintegral_zero]
    · exact ((ENNReal.continuous_ofReal.comp (hF_cont.comp he_cont)).measurable.indicator hmB).aemeasurable
  have hl_e1 : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
      ENNReal.ofReal ε * ∫⁻ p : ℝ × ℝ, g (e1 p) = ∫⁻ q : ℝ × ℝ, g q := by
    intro g hg
    rw [Measure.volume_eq_prod,
      lintegral_prod (fun p : ℝ × ℝ => g (e1 p)) (hg.comp e1.measurable).aemeasurable,
      lintegral_prod g hg.aemeasurable, lintegral_lintegral_swap (f := fun u d => g (e1 (u, d)))
        (hg.comp e1.measurable).aemeasurable,
      lintegral_lintegral_swap (f := fun x d => g (x, d)) hg.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun d => ?_
    let e_u : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ ε hε.ne'
    have hm_u : Measure.map e_u (volume : Measure ℝ) = ENNReal.ofReal ε⁻¹ • (volume : Measure ℝ) := by
      have h := Real.map_volume_mul_left hε.ne'
      rwa [abs_of_pos (inv_pos.mpr hε)] at h
    have hl1 : ∫⁻ u : ℝ, g (xiStar + ε * u, d) =
        ENNReal.ofReal ε⁻¹ * ∫⁻ x : ℝ, g (xiStar + x, d) := by
      have h := (lintegral_map_equiv (μ := (volume : Measure ℝ)) (fun x => g (xiStar + x, d)) e_u).symm
      rwa [hm_u, lintegral_smul_measure, smul_eq_mul] at h
    have hshift : ∫⁻ x : ℝ, g (xiStar + x, d) = ∫⁻ x : ℝ, g (x, d) :=
      lintegral_add_left_eq_self (fun x => g (x, d)) xiStar
    have he1_val : (fun u : ℝ => g (e1 (u, d))) = fun u : ℝ => g (xiStar + ε * u, d) := rfl
    rw [he1_val, hl1, hshift, ← mul_assoc, ← ENNReal.ofReal_mul hε.le, mul_inv_cancel₀ hε.ne',
      ENNReal.ofReal_one, one_mul]
  let g_ind : ℝ × ℝ → ℝ≥0∞ := (e '' B).indicator (fun y => ENNReal.ofReal (F y))
  have hg_meas : Measurable g_ind :=
    (ENNReal.continuous_ofReal.comp hF_cont).measurable.indicator hmS
  have hB_ind_eq : B.indicator (fun p => ENNReal.ofReal (F (e p))) = fun p => g_ind (e p) := by
    ext p
    dsimp only [g_ind]
    by_cases hp : p ∈ B
    · have hep : e p ∈ e '' B := ⟨p, hp, rfl⟩
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hep]
    · have hep : e p ∉ e '' B := fun ⟨p', hp', hpe⟩ => hp (e.injective hpe ▸ hp')
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hep]
  have h2 := lintegral_xi_d_s4_3 hg_meas
  have hl2 : ∫⁻ y : ℝ × ℝ, g_ind y = ENNReal.ofReal 2 * (ENNReal.ofReal ε * ∫⁻ p : ℝ × ℝ, g_ind (e p)) := by
    rw [h2]
    congr 1
    exact (hl_e1 (fun q => g_ind (e2 q)) (hg_meas.comp e2.measurable)).symm
  have hRHS_ofReal : ENNReal.ofReal ((1 / 2 : ℝ) * ∫ y in e '' B, F y) =
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ y : ℝ × ℝ, g_ind y := by
    rw [ENNReal.ofReal_mul (by norm_num), ofReal_integral_eq_lintegral_ofReal hS_int
      (Eventually.of_forall fun _ => hF_nn _), ← lintegral_indicator hmS]
  have heq_ofReal : ENNReal.ofReal (∫ u in Icc (-M) M, G_out u) =
      ENNReal.ofReal ((1 / 2 : ℝ) * ∫ y in e '' B, F y) := by
    rw [hLHS_lint, hB_ind_eq, hRHS_ofReal, hl2, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hLHS_nn : 0 ≤ ∫ u in Icc (-M) M, G_out u := setIntegral_nonneg measurableSet_Icc fun u _ => hG_nn u
  have hRHS_nn : 0 ≤ (1 / 2 : ℝ) * ∫ y in e '' B, F y :=
    mul_nonneg (by norm_num) (setIntegral_nonneg hmS fun y _ => hF_nn y)
  exact (ENNReal.ofReal_eq_ofReal_iff hLHS_nn hRHS_nn).mp heq_ofReal

lemma spin_neg_mass_box_lower {C₀ R V C₃₃ c_exp : ℝ} (hC₀ : 0 < C₀) (hCR : C₀ ≤ R)
    (hV_def : V = Real.sqrt (4 * xiStar * (C₀ + R)))
    (h33_small : C₃₃ * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) ≤ 1 / 12)
    {c x₁ : ℝ} (hc : 49 ≤ c)
    (hC₀_eps : C₀ * (c - 1) ^ (-(2 / 3 : ℝ)) ≤ xiStar / 4)
    (hR_eps : (c - 1) ^ (-(2 / 3 : ℝ)) * R ≤ xiStar / 4)
    (hx₁ : |x₁ - xiStar| ≤ C₀ * (c - 1) ^ (-(2 / 3 : ℝ)))
    {Φ : ℝ × ℝ → ℝ} (hS : SpinSlackHyp c x₁ Φ)
    (h33_inst : ∫ p in {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 ∧
        spinLongDist q ≤ xiStar - (c - 1) ^ (-(2 / 3 : ℝ)) * R},
      max (-spinG ((c - 1) / 12) Φ p.1 p.2) 0 * spinWc ((c - 1) / 12) p.1 *
        spinWc ((c - 1) / 12) p.2 ≤ C₃₃ * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) :
    let n := c - 1
    let a := n / 12
    let ε := n ^ (-(2 / 3 : ℝ))
    1 / 32 ≤ ∫ u in Icc (-R) R,
      ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
        ∫ d in Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε),
          max (-spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) 0 := by
  intro n a ε
  rcases hS with ⟨hx1_nn, hΦ, hM2, hvac, hgap⟩
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  have hR_nn : 0 ≤ R := hC₀.le.trans hCR
  let gm : ℝ × ℝ → ℝ := fun p => max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2
  have hgm_nn : ∀ p : ℝ × ℝ, 0 ≤ gm p := fun p =>
    mul_nonneg (mul_nonneg (le_max_right _ _) (spinWc_nonneg ha2.le p.1)) (spinWc_nonneg ha2.le p.2)
  have hgm_int : Integrable gm := by
    refine (integrable_spinG_wc ha0 hΦ).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hWc : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
      have hGc : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
        unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
          (continuous_const.mul continuous_snd))
      exact (((hGc.neg.max continuous_const).mul (hWc.comp continuous_fst)).mul
        (hWc.comp continuous_snd)).aestronglyMeasurable
    · have h1 : max (-spinG a Φ p.1 p.2) 0 ≤ |spinG a Φ p.1 p.2| := by
        rcases le_total (spinG a Φ p.1 p.2) 0 with h | h
        · rw [max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]
        · rw [max_eq_right (neg_nonpos.mpr h)]; exact abs_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (hgm_nn p)]
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hw1) hw2
  let E_disc : Set (ℝ × ℝ) := {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2}
  let E_tail : Set (ℝ × ℝ) := {q ∈ E_disc | spinLongDist q ≤ xiStar - ε * R}
  let E_rem : Set (ℝ × ℝ) := {q ∈ E_disc | xiStar - ε * R < spinLongDist q}
  have hm_disc : MeasurableSet E_disc := by
    have h1 : Continuous (fun q : ℝ × ℝ => (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4) := by fun_prop
    exact (isOpen_lt h1 continuous_const).measurableSet
  have hm_tail : MeasurableSet E_tail := by
    have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
    exact hm_disc.inter (isClosed_le h2 continuous_const).measurableSet
  have hm_rem : MeasurableSet E_rem := by
    have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
    exact hm_disc.inter (isOpen_lt continuous_const h2).measurableSet
  have hgm_disc : ∫ p : ℝ × ℝ, gm p = ∫ p in E_disc, gm p := by
    rw [← integral_indicator hm_disc]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ E_disc
    · simp [Set.indicator_of_mem hp]
    · have hge : x₁ ^ 2 ≤ ((p.1 + p.2) / 2) ^ 2 + ((p.1 - p.2) / 2) ^ 2 := by
        have hnot := hp
        change ¬ ((p.1 + p.2) ^ 2 / 4 + (p.1 - p.2) ^ 2 / 4 < x₁ ^ 2) at hnot
        linarith
      have hg0 : 0 ≤ spinG a Φ p.1 p.2 := by
        have h := hgap ((p.1 + p.2) / 2) ((p.1 - p.2) / 2) hge
        rwa [show (p.1 + p.2) / 2 + (p.1 - p.2) / 2 = p.1 by ring,
          show (p.1 + p.2) / 2 - (p.1 - p.2) / 2 = p.2 by ring] at h
      simp [Set.indicator_of_notMem hp, gm, max_eq_right (neg_nonpos.mpr hg0)]
  have hsplit_rem : ∫ p in E_disc, gm p = (∫ p in E_tail, gm p) + ∫ p in E_rem, gm p := by
    rw [← integral_indicator hm_disc, ← integral_indicator hm_tail, ← integral_indicator hm_rem,
      ← integral_add (hgm_int.indicator hm_tail) (hgm_int.indicator hm_rem)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    dsimp only
    by_cases hp : p ∈ E_disc
    · rcases le_or_gt (spinLongDist p) (xiStar - ε * R) with hl | hl
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (⟨hp, hl⟩ : p ∈ E_tail),
          Set.indicator_of_notMem (fun (h : p ∈ E_rem) => not_le_of_gt h.2 hl), add_zero]
      · rw [Set.indicator_of_mem hp, Set.indicator_of_notMem (fun (h : p ∈ E_tail) => not_le_of_gt hl h.2),
          Set.indicator_of_mem (⟨hp, hl⟩ : p ∈ E_rem), zero_add]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun (h : p ∈ E_tail) => hp h.1),
        Set.indicator_of_notMem (fun (h : p ∈ E_rem) => hp h.1), add_zero]
  have hrem_ge : 1 / 4 ≤ ∫ p in E_rem, gm p := by
    have hthird := spin_neg_mass_ge_third hc ⟨hx1_nn, hΦ, hM2, hvac, hgap⟩
    have htail : ∫ p in E_tail, gm p ≤ 1 / 12 := h33_inst.trans h33_small
    linarith [hthird, hgm_disc, hsplit_rem, htail]
  let E1 : Set (ℝ × ℝ) := {q ∈ E_rem | 0 < q.1 ∧ 0 < q.2}
  let E2 : Set (ℝ × ℝ) := {q ∈ E_rem | q.1 < 0 ∧ 0 < q.2}
  let E3 : Set (ℝ × ℝ) := {q ∈ E_rem | 0 < q.1 ∧ q.2 < 0}
  let E4 : Set (ℝ × ℝ) := {q ∈ E_rem | q.1 < 0 ∧ q.2 < 0}
  have hmE1 : MeasurableSet E1 := hm_rem.inter
    ((isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_const continuous_snd).measurableSet)
  have hmE2 : MeasurableSet E2 := hm_rem.inter
    ((isOpen_lt continuous_fst continuous_const).measurableSet.inter
      (isOpen_lt continuous_const continuous_snd).measurableSet)
  have hmE3 : MeasurableSet E3 := hm_rem.inter
    ((isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_snd continuous_const).measurableSet)
  have hmE4 : MeasurableSet E4 := hm_rem.inter
    ((isOpen_lt continuous_fst continuous_const).measurableSet.inter
      (isOpen_lt continuous_snd continuous_const).measurableSet)
  have hnull_axes : volume {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0} = 0 := by
    have h1 : ({q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0} : Set (ℝ × ℝ)) =
        ((({0} : Set ℝ) ×ˢ Set.univ) ∪ (Set.univ ×ˢ ({0} : Set ℝ))) := by
      ext q; simp [Set.mem_prod]
    rw [h1]
    exact measure_union_null (by rw [Measure.volume_eq_prod, Measure.prod_prod]; simp)
      (by rw [Measure.volume_eq_prod, Measure.prod_prod]; simp)
  have hae_E : E_rem =ᵐ[volume] E1 ∪ E2 ∪ E3 ∪ E4 := by
    refine Filter.eventuallyEqSet_iff'.2 ?_
    change ∀ᵐ q : ℝ × ℝ ∂volume, (q ∈ E_rem) = (q ∈ E1 ∪ E2 ∪ E3 ∪ E4)
    rw [ae_iff]
    refine measure_mono_null (fun q hq => ?_) hnull_axes
    by_contra hnz
    change ¬ (q.1 = 0 ∨ q.2 = 0) at hnz
    push Not at hnz
    apply hq; apply propext
    rcases lt_or_gt_of_ne hnz.1 with hx | hx <;> rcases lt_or_gt_of_ne hnz.2 with hy | hy
    · exact ⟨fun h => Or.inr ⟨h, hx, hy⟩, by rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h⟩
    · exact ⟨fun h => Or.inl (Or.inl (Or.inr ⟨h, hx, hy⟩)),
        by rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h⟩
    · exact ⟨fun h => Or.inl (Or.inr ⟨h, hx, hy⟩),
        by rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h⟩
    · exact ⟨fun h => Or.inl (Or.inl (Or.inl ⟨h, hx, hy⟩)),
        by rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h⟩
  have hgm_nl : ∀ x y : ℝ, gm (-x, y) = gm (x, y) := fun x y => by
    dsimp [gm]; rw [spinG_d4_neg_left hΦ, spinWc_even]
  have hgm_nr : ∀ x y : ℝ, gm (x, -y) = gm (x, y) := fun x y => by
    dsimp [gm]; rw [spinG_d4_neg_right hΦ, spinWc_even]
  have hE2_eq : ∫ q in E2, gm q = ∫ q in E1, gm q := by
    let e := MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ)
    have heq : ∀ q : ℝ × ℝ, e q = (-q.1, q.2) := fun _ => rfl
    have hmp : MeasurePreserving e volume volume :=
      (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)
    have hpre : e ⁻¹' E2 = E1 := by
      ext q
      change e q ∈ E2 ↔ q ∈ E1
      rw [heq]
      simp only [E2, E1, E_rem, E_disc, Set.mem_setOf_eq, spinLongDist, abs_neg]
      constructor
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; exact ⟨⟨by linarith only [h1], h2⟩, by linarith only [hq1], hq2⟩
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; exact ⟨⟨by linarith only [h1], h2⟩, by linarith only [hq1], hq2⟩
    rw [← integral_indicator hmE1, ← integral_indicator hmE2, ← hmp.integral_comp' (E2.indicator gm)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    dsimp only
    by_cases hq : q ∈ E1
    · have hq2 : e q ∈ E2 := by rwa [← hpre] at hq
      rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq2, heq]; exact hgm_nl q.1 q.2
    · have hq2 : e q ∉ E2 := by rwa [← hpre] at hq
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq2]
  have hE3_eq : ∫ q in E3, gm q = ∫ q in E1, gm q := by
    let e := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)
    have heq : ∀ q : ℝ × ℝ, e q = (q.1, -q.2) := fun _ => rfl
    have hmp : MeasurePreserving e volume volume :=
      (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)
    have hpre : e ⁻¹' E3 = E1 := by
      ext q
      change e q ∈ E3 ↔ q ∈ E1
      rw [heq]
      simp only [E3, E1, E_rem, E_disc, Set.mem_setOf_eq, spinLongDist, abs_neg]
      constructor
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; exact ⟨⟨by linarith only [h1], h2⟩, hq1, by linarith only [hq2]⟩
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; exact ⟨⟨by linarith only [h1], h2⟩, hq1, by linarith only [hq2]⟩
    rw [← integral_indicator hmE1, ← integral_indicator hmE3, ← hmp.integral_comp' (E3.indicator gm)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    dsimp only
    by_cases hq : q ∈ E1
    · have hq3 : e q ∈ E3 := by rwa [← hpre] at hq
      rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq3, heq]; exact hgm_nr q.1 q.2
    · have hq3 : e q ∉ E3 := by rwa [← hpre] at hq
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq3]
  have hE4_eq : ∫ q in E4, gm q = ∫ q in E1, gm q := by
    let e := MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.neg ℝ)
    have heq : ∀ q : ℝ × ℝ, e q = (-q.1, -q.2) := fun _ => rfl
    have hmp : MeasurePreserving e volume volume :=
      (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)
    have hpre : e ⁻¹' E4 = E1 := by
      ext q
      change e q ∈ E4 ↔ q ∈ E1
      rw [heq]
      simp only [E4, E1, E_rem, E_disc, Set.mem_setOf_eq, spinLongDist, abs_neg]
      constructor
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; exact ⟨⟨by linarith only [h1], h2⟩, by linarith only [hq1], by linarith only [hq2]⟩
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; exact ⟨⟨by linarith only [h1], h2⟩, by linarith only [hq1], by linarith only [hq2]⟩
    rw [← integral_indicator hmE1, ← integral_indicator hmE4, ← hmp.integral_comp' (E4.indicator gm)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    dsimp only
    by_cases hq : q ∈ E1
    · have hq4 : e q ∈ E4 := by rwa [← hpre] at hq
      rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq4, heq]
      exact (hgm_nr (-q.1) q.2).trans (hgm_nl q.1 q.2)
    · have hq4 : e q ∉ E4 := by rwa [← hpre] at hq
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq4]
  have hu : ∀ {S T : Set (ℝ × ℝ)}, Disjoint S T → MeasurableSet S → MeasurableSet T →
      ∫ q in S ∪ T, gm q = (∫ q in S, gm q) + ∫ q in T, gm q := by
    intro S T hd hS hT
    rw [← integral_indicator (hS.union hT), ← integral_indicator hS, ← integral_indicator hT,
      ← integral_add (hgm_int.indicator hS) (hgm_int.indicator hT)]
    congr 1; ext q
    by_cases h1 : q ∈ S <;> by_cases h2 : q ∈ T
    · exact absurd h2 (Set.disjoint_left.mp hd h1)
    · rw [Set.indicator_of_mem (Or.inl h1), Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
    · rw [Set.indicator_of_mem (Or.inr h2), Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]
    · rw [Set.indicator_of_notMem (by rintro (h | h) <;> contradiction),
        Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
  have hd12 : Disjoint E1 E2 := Set.disjoint_left.mpr fun q h1 h2 => absurd h1.2.1 h2.2.1.not_gt
  have hd123 : Disjoint (E1 ∪ E2) E3 := Set.disjoint_left.mpr fun q h12 h3 => by
    rcases h12 with h | h <;> [exact absurd h.2.2 h3.2.2.not_gt; exact absurd h.2.1 h3.2.1.not_gt]
  have hd1234 : Disjoint (E1 ∪ E2 ∪ E3) E4 := Set.disjoint_left.mpr fun q h123 h4 => by
    rcases h123 with (h | h) | h
    · exact absurd h.2.1 h4.2.1.not_gt
    · exact absurd h.2.2 h4.2.2.not_gt
    · exact absurd h.2.1 h4.2.1.not_gt
  have hE_sum : ∫ p in E_rem, gm p = 4 * ∫ q in E1, gm q := by
    rw [setIntegral_congr_set hae_E,
      hu hd1234 ((hmE1.union hmE2).union hmE3) hmE4,
      hu hd123 (hmE1.union hmE2) hmE3,
      hu hd12 hmE1 hmE2, hE2_eq, hE3_eq, hE4_eq]
    ring
  have hE1_ge : 1 / 16 ≤ ∫ q in E1, gm q := by linarith [hrem_ge, hE_sum]
  let W : ℝ := V * Real.sqrt ε
  have hW_nn : 0 ≤ W := mul_nonneg (by rw [hV_def]; exact Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let F_box : ℝ × ℝ → ℝ := fun q =>
    max (-spinG a Φ q.1 q.2) 0 * (a * Real.exp (n * (2 * π / 3) * ((q.1 + q.2) / 2)))
  have hF_cont : Continuous F_box := by
    have hGc : Continuous (fun q : ℝ × ℝ => spinG a Φ q.1 q.2) := by
      unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
        (continuous_const.mul continuous_snd))
    exact (hGc.neg.max continuous_const).mul
      (continuous_const.mul (Real.continuous_exp.comp (by fun_prop)))
  have hF_nn : ∀ q : ℝ × ℝ, 0 ≤ F_box q := fun q =>
    mul_nonneg (le_max_right _ _) (mul_nonneg ha0.le (Real.exp_pos _).le)
  let B : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-W) W
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun p => (xiStar + ε * p.1 + p.2, xiStar + ε * p.1 - p.2)
      invFun := fun q => (((q.1 + q.2) / 2 - xiStar) / ε, (q.1 - q.2) / 2)
      left_inv := fun ⟨u, d⟩ => by ext <;> dsimp <;> field_simp [hε_pos.ne'] <;> ring
      right_inv := fun ⟨x, y⟩ => by ext <;> dsimp <;> field_simp [hε_pos.ne'] <;> ring
      measurable_toFun :=
        ((measurable_const.add (measurable_const.mul measurable_fst)).add measurable_snd).prodMk
          ((measurable_const.add (measurable_const.mul measurable_fst)).sub measurable_snd)
      measurable_invFun :=
        ((((measurable_fst.add measurable_snd).div_const 2).sub measurable_const).div_const ε).prodMk
          ((measurable_fst.sub measurable_snd).div_const 2) }
  have hcov := box_cov_integral_eq hε_pos hR_nn hW_nn hF_cont hF_nn
  have hE1_sub : E1 ⊆ e '' B := by
    intro q ⟨⟨hdisc, hxi_gt⟩, hq1, hq2⟩
    let ξ : ℝ := (q.1 + q.2) / 2
    let d : ℝ := (q.1 - q.2) / 2
    have hL_eq : spinLongDist q = ξ := by
      dsimp [spinLongDist, ξ]; rw [abs_of_pos hq1, abs_of_pos hq2]; ring
    rw [hL_eq] at hxi_gt
    have hξ_pos : 0 < ξ := by linarith only [hxi_gt, hR_eps, xiStar_pos]
    have hdisc_ξd : ξ ^ 2 + d ^ 2 < x₁ ^ 2 := by
      have hid : ((q.1 + q.2) / 2) ^ 2 + ((q.1 - q.2) / 2) ^ 2 =
          (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 := by ring
      change (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 at hdisc
      dsimp [ξ, d]
      linarith only [hdisc, hid]
    have hξ_lt_x1 : ξ < x₁ := by
      have hsq : ξ ^ 2 < x₁ ^ 2 := by linarith [sq_nonneg d]
      nlinarith
    have hx1_ub : x₁ ≤ xiStar + C₀ * ε := by
      have h := (abs_le.mp hx₁).2
      change x₁ - xiStar ≤ C₀ * ε at h
      linarith only [h]
    have hC₀R_eps : C₀ * ε ≤ R * ε := mul_le_mul_of_nonneg_right hCR hε_pos.le
    have hξ_ub : ξ ≤ xiStar + ε * R := by linarith only [hξ_lt_x1, hx1_ub, hC₀R_eps]
    have hu_mem : (ξ - xiStar) / ε ∈ Icc (-R) R := by
      rw [Set.mem_Icc]; constructor
      · rw [le_div_iff₀ hε_pos]; linarith only [hxi_gt]
      · rw [div_le_iff₀ hε_pos]; linarith only [hξ_ub]
    have hd_sq : d ^ 2 < 4 * xiStar * (C₀ + R) * ε := by
      have h1 : x₁ - ξ ≤ (C₀ + R) * ε := by linarith only [hx1_ub, hxi_gt]
      have h2 : 0 ≤ x₁ + ξ := by linarith only [hx1_nn, hξ_pos]
      have h3 : x₁ + ξ ≤ 4 * xiStar := by
        have hC0' : C₀ * ε ≤ xiStar / 4 := hC₀_eps
        have hR' : ε * R ≤ xiStar / 4 := hR_eps
        linarith only [hx1_ub, hξ_ub, hC0', hR', xiStar_pos]
      have hdiff : d ^ 2 < (x₁ - ξ) * (x₁ + ξ) := by
        linarith only [hdisc_ξd, show x₁ ^ 2 - ξ ^ 2 = (x₁ - ξ) * (x₁ + ξ) by ring]
      have hnn : 0 ≤ x₁ - ξ := by linarith only [hξ_lt_x1]
      have hmul : (x₁ - ξ) * (x₁ + ξ) ≤ ((C₀ + R) * ε) * (4 * xiStar) :=
        mul_le_mul h1 h3 h2 (mul_nonneg (by linarith only [hC₀, hCR]) hε_pos.le)
      linarith only [hdiff, hmul]
    have hd_abs : |d| ≤ W := by
      dsimp [W]
      rw [← abs_of_nonneg (mul_nonneg (by rw [hV_def]; exact Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
        ← sq_le_sq, hV_def, mul_pow,
        Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) xiStar_pos.le) (by linarith)),
        Real.sq_sqrt hε_pos.le]
      exact hd_sq.le
    refine ⟨((ξ - xiStar) / ε, d), ⟨hu_mem, abs_le.mp hd_abs⟩, ?_⟩
    apply Prod.ext <;> dsimp [e, ξ, d]
    · rw [mul_div_cancel₀ _ hε_pos.ne']; ring
    · rw [mul_div_cancel₀ _ hε_pos.ne']; ring
  have he_img : e '' B = e.symm ⁻¹' B := e.toEquiv.image_eq_preimage_symm B
  have he_cont : Continuous e :=
    ((continuous_const.add (continuous_const.mul continuous_fst)).add continuous_snd).prodMk
      ((continuous_const.add (continuous_const.mul continuous_fst)).sub continuous_snd)
  have hS_int : IntegrableOn F_box (e '' B) :=
    hF_cont.continuousOn.integrableOn_compact ((isCompact_Icc.prod isCompact_Icc).image he_cont)
  have hgm_le_F : ∀ q ∈ E1, gm q ≤ F_box q := fun q ⟨_, hq1, hq2⟩ => by
    dsimp [gm, F_box]
    have hξd := spinWc_mul_le_exp_s4 ha2
      (show 0 < (q.1 + q.2) / 2 + (q.1 - q.2) / 2 by linarith)
      (show 0 < (q.1 + q.2) / 2 - (q.1 - q.2) / 2 by linarith)
    rw [show (q.1 + q.2) / 2 + (q.1 - q.2) / 2 = q.1 by ring,
      show (q.1 + q.2) / 2 - (q.1 - q.2) / 2 = q.2 by ring,
      show 12 * a = n by dsimp [a]; ring] at hξd
    calc max (-spinG a Φ q.1 q.2) 0 * spinWc a q.1 * spinWc a q.2
        = max (-spinG a Φ q.1 q.2) 0 * (spinWc a q.1 * spinWc a q.2) := by ring
      _ ≤ max (-spinG a Φ q.1 q.2) 0 * (a * Real.exp (n * (2 * π / 3) * ((q.1 + q.2) / 2))) :=
          mul_le_mul_of_nonneg_left hξd (le_max_right _ _)
  have hE1_le_F : ∫ q in E1, gm q ≤ ∫ y in e '' B, F_box y := by
    have h1 : ∫ q in E1, gm q ≤ ∫ q in E1, F_box q :=
      setIntegral_mono_on (hgm_int.integrableOn) (hS_int.mono_set hE1_sub) hmE1 hgm_le_F
    have h2 : ∫ q in E1, F_box q ≤ ∫ y in e '' B, F_box y :=
      setIntegral_mono_set hS_int (Eventually.of_forall hF_nn) hE1_sub.eventuallySubset
    exact h1.trans h2
  have hlhs_eq : (∫ u in Icc (-R) R,
        ε * ∫ d in Icc (-W) W, F_box (xiStar + ε * u + d, xiStar + ε * u - d)) =
      ∫ u in Icc (-R) R,
        ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
          ∫ d in Icc (-W) W, max (-spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) 0 := by
    refine setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
    have heq : (fun d : ℝ => F_box (xiStar + ε * u + d, xiStar + ε * u - d)) =
        fun d : ℝ => (a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u))) *
          max (-spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) 0 := by
      ext d; dsimp [F_box]
      rw [show (xiStar + ε * u + d + (xiStar + ε * u - d)) / 2 = xiStar + ε * u by ring]; ring
    rw [heq, integral_const_mul]; ring
  rw [← hlhs_eq]
  change _ ≤ ∫ u in Icc (-R) R, ε * ∫ d in Icc (-W) W, F_box (xiStar + ε * u + d, xiStar + ε * u - d)
  rw [hcov]
  linarith [hE1_ge, hE1_le_F]

lemma spinHProfile_err_integral_le {M V : ℝ} (hM : 0 < M) (hV : 0 < V)
    {c : ℝ} (hc : 49 ≤ c) (N : ℕ) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    (hM_eps : (c - 1) ^ (-(2 / 3 : ℝ)) * M ≤ xiStar / 4)
    (hV_eps : V * Real.sqrt ((c - 1) ^ (-(2 / 3 : ℝ))) ≤ xiStar / 4) :
    let n := c - 1
    let a := n / 12
    let ε := n ^ (-(2 / 3 : ℝ))
    ∫ u in Icc (-M) M,
      (ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
        ∫ d in Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε),
          |spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d) -
            spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)|) ≤
      (2 * (1 - Real.exp (-π * xiStar)) ^ 4)⁻¹ *
        ∫ p in {q : ℝ × ℝ | xiStar / 4 ≤ q.1 ∧ xiStar / 4 ≤ q.2},
          |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by
  intro n a ε
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  let W : ℝ := V * Real.sqrt ε
  have hW_nn : 0 ≤ W := mul_nonneg hV.le (Real.sqrt_nonneg _)
  let F_err : ℝ × ℝ → ℝ := fun q =>
    |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| *
      (a * Real.exp (n * (2 * π / 3) * ((q.1 + q.2) / 2)))
  have hGc : Continuous (fun q : ℝ × ℝ => spinG a Φ q.1 q.2) := by
    unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))
  have hF_cont : Continuous F_err :=
    (hGc.sub (continuous_spinTruncInv_s4_3 hΦ N)).abs.mul
      (continuous_const.mul (Real.continuous_exp.comp (by fun_prop)))
  have hF_nn : ∀ q : ℝ × ℝ, 0 ≤ F_err q := fun q =>
    mul_nonneg (abs_nonneg _) (mul_nonneg ha0.le (Real.exp_pos _).le)
  let B : Set (ℝ × ℝ) := Icc (-M) M ×ˢ Icc (-W) W
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun p => (xiStar + ε * p.1 + p.2, xiStar + ε * p.1 - p.2)
      invFun := fun q => (((q.1 + q.2) / 2 - xiStar) / ε, (q.1 - q.2) / 2)
      left_inv := fun ⟨u, d⟩ => by ext <;> dsimp <;> field_simp [hε_pos.ne'] <;> ring
      right_inv := fun ⟨x, y⟩ => by ext <;> dsimp <;> field_simp [hε_pos.ne'] <;> ring
      measurable_toFun :=
        ((measurable_const.add (measurable_const.mul measurable_fst)).add measurable_snd).prodMk
          ((measurable_const.add (measurable_const.mul measurable_fst)).sub measurable_snd)
      measurable_invFun :=
        ((((measurable_fst.add measurable_snd).div_const 2).sub measurable_const).div_const ε).prodMk
          ((measurable_fst.sub measurable_snd).div_const 2) }
  have hcov := box_cov_integral_eq hε_pos hM.le hW_nn hF_cont hF_nn
  have hlhs_eq : (∫ u in Icc (-M) M,
        ε * ∫ d in Icc (-W) W, F_err (xiStar + ε * u + d, xiStar + ε * u - d)) =
      ∫ u in Icc (-M) M,
        ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
          ∫ d in Icc (-W) W,
            |spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d) -
              spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)| := by
    refine setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
    have heq : (fun d : ℝ => F_err (xiStar + ε * u + d, xiStar + ε * u - d)) =
        fun d : ℝ => (a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u))) *
          |spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d) -
            spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)| := by
      ext d; dsimp [F_err]
      rw [show (xiStar + ε * u + d + (xiStar + ε * u - d)) / 2 = xiStar + ε * u by ring]; ring
    rw [heq, integral_const_mul]; ring
  let S_tail : Set (ℝ × ℝ) := {q : ℝ × ℝ | xiStar / 4 ≤ q.1 ∧ xiStar / 4 ≤ q.2}
  have hsub : e '' B ⊆ S_tail := by
    rintro q ⟨⟨u, d⟩, ⟨hu, hd⟩, rfl⟩
    have hu1 := hu.1; have hu2 := hu.2
    have hd1 := hd.1; have hd2 := hd.2
    have h1 : -(ε * M) ≤ ε * u := by nlinarith
    have h2 : -(V * Real.sqrt ε) ≤ d := hd1
    have h3 : d ≤ V * Real.sqrt ε := hd2
    dsimp [S_tail, e]
    constructor <;> linarith [hM_eps, hV_eps]
  let cFc : ℝ := (1 - Real.exp (-π * xiStar)) ^ 4
  have hcFc_pos : 0 < cFc := by
    have h1 : Real.exp (-π * xiStar) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, xiStar_pos])
    exact pow_pos (by linarith) 4
  have he_img : e '' B = e.symm ⁻¹' B := e.toEquiv.image_eq_preimage_symm B
  have hmS : MeasurableSet (e '' B) := by
    rw [he_img]; exact e.symm.measurable (measurableSet_Icc.prod measurableSet_Icc)
  have he_cont : Continuous e :=
    ((continuous_const.add (continuous_const.mul continuous_fst)).add continuous_snd).prodMk
      ((continuous_const.add (continuous_const.mul continuous_fst)).sub continuous_snd)
  have hS_int : IntegrableOn F_err (e '' B) :=
    hF_cont.continuousOn.integrableOn_compact ((isCompact_Icc.prod isCompact_Icc).image he_cont)
  have hr4 : 0 < xiStar / 4 := by positivity [xiStar_pos]
  obtain ⟨h0N_int, _⟩ := integrable_dilate_and_bound_s4 ha2 hr4 hΦ 0 N
  obtain ⟨hN0_int, _⟩ := integrable_dilate_and_bound_s4 ha2 hr4 hΦ N 0
  obtain ⟨hNN_int, _⟩ := integrable_dilate_and_bound_s4 ha2 hr4 hΦ N N
  have h0N_eq : (fun p : ℝ × ℝ => |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ 0 * p.1) (spinLambda a ^ N * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by ext p; rw [pow_zero, one_mul]
  have hN0_eq : (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ 0 * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by ext p; rw [pow_zero, one_mul]
  rw [← h0N_eq] at h0N_int
  rw [← hN0_eq] at hN0_int
  let dom_fn : ℝ × ℝ → ℝ := fun p =>
    |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2
  have h_dom_int : IntegrableOn dom_fn S_tail := by
    refine (((h0N_int.add hN0_int).add hNN_int).integrableOn).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hWc : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
      exact (((hGc.sub (continuous_spinTruncInv_s4_3 hΦ N)).abs.mul
        (hWc.comp continuous_fst)).mul (hWc.comp continuous_snd)).aestronglyMeasurable
    · have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hw1) hw2),
        spinG_sub_spinTruncInv ha2]
      have hab1 := abs_add_le (spinG a Φ p.1 (spinLambda a ^ N * p.2)) (spinG a Φ (spinLambda a ^ N * p.1) p.2)
      have hab2 := abs_sub_le (spinG a Φ p.1 (spinLambda a ^ N * p.2) + spinG a Φ (spinLambda a ^ N * p.1) p.2) 0
        (spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2))
      rw [sub_zero, zero_sub, abs_neg] at hab2
      have hab : |spinG a Φ p.1 (spinLambda a ^ N * p.2) +
          spinG a Φ (spinLambda a ^ N * p.1) p.2 -
          spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| ≤
          |spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| := by linarith
      calc |spinG a Φ p.1 (spinLambda a ^ N * p.2) +
              spinG a Φ (spinLambda a ^ N * p.1) p.2 -
              spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2
          ≤ (|spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
              |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
              |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)|) *
              spinWc a p.1 * spinWc a p.2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hw1) hw2
        _ = (((fun q : ℝ × ℝ => |spinG a Φ q.1 (spinLambda a ^ N * q.2)| * spinWc a q.1 * spinWc a q.2) +
              (fun q : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * q.1) q.2| * spinWc a q.1 * spinWc a q.2)) +
              (fun q : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * q.1) (spinLambda a ^ N * q.2)| * spinWc a q.1 * spinWc a q.2)) p := by
            dsimp only [Pi.add_apply]; ring
  have hF_le_dom : ∀ q ∈ e '' B, F_err q ≤ cFc⁻¹ * dom_fn q := fun q hq => by
    have hq_tail := hsub hq
    have h1 := spinWc_mul_ge_cFc ha2
      (show xiStar / 4 ≤ (q.1 + q.2) / 2 + (q.1 - q.2) / 2 by linarith [hq_tail.1])
      (show xiStar / 4 ≤ (q.1 + q.2) / 2 - (q.1 - q.2) / 2 by linarith [hq_tail.2])
    rw [show (q.1 + q.2) / 2 + (q.1 - q.2) / 2 = q.1 by ring,
      show (q.1 + q.2) / 2 - (q.1 - q.2) / 2 = q.2 by ring,
      show 12 * a = n by dsimp [a]; ring] at h1
    have hexp_le : a * Real.exp (n * (2 * π / 3) * ((q.1 + q.2) / 2)) ≤
        cFc⁻¹ * (spinWc a q.1 * spinWc a q.2) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hcFc_pos]
      linarith
    dsimp [F_err, dom_fn]
    calc |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| *
            (a * Real.exp (n * (2 * π / 3) * ((q.1 + q.2) / 2)))
        ≤ |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| *
            (cFc⁻¹ * (spinWc a q.1 * spinWc a q.2)) :=
          mul_le_mul_of_nonneg_left hexp_le (abs_nonneg _)
      _ = cFc⁻¹ * (|spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) := by ring
  have hint_mono : ∫ q in e '' B, F_err q ≤ cFc⁻¹ * ∫ p in S_tail, dom_fn p := by
    have h1 : ∫ q in e '' B, F_err q ≤ ∫ q in e '' B, cFc⁻¹ * dom_fn q :=
      setIntegral_mono_on hS_int ((h_dom_int.mono_set hsub).const_mul _) hmS hF_le_dom
    rw [integral_const_mul] at h1
    have h2 : ∫ q in e '' B, dom_fn q ≤ ∫ p in S_tail, dom_fn p :=
      setIntegral_mono_set h_dom_int (Eventually.of_forall fun p =>
        mul_nonneg (mul_nonneg (abs_nonneg _)
          (spinWc_nonneg ha2.le p.1)) (spinWc_nonneg ha2.le p.2)) hsub.eventuallySubset
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hcFc_pos).le)
  rw [← hlhs_eq]
  change _ ≤ (2 * cFc)⁻¹ * ∫ p in S_tail, dom_fn p
  rw [hcov, show (2 * cFc)⁻¹ = (1 / 2 : ℝ) * cFc⁻¹ by rw [mul_inv, one_div], mul_assoc]
  exact mul_le_mul_of_nonneg_left hint_mono (by norm_num)

end FormalResearch.ModularBootstrap.Spin
