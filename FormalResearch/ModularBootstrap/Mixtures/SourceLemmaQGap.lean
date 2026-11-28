module

public import FormalResearch.ModularBootstrap.Mixtures.SourceLemmaQBase

/-!
# Far-Lobe Exponential Decay for Signed Common Sources (`pmix:o1`, `deltaLobeSrc`)
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap
open Crossing WeightAxioms ConcreteBootstrap PoissonJensen TipFront FixedWeightTip
open FixedWeightBand FormalResearch.Special

/-! ### Section 3: Far-lobe exponential bound (`lemmaG_src_of_common`, `deltaLobeSrc_gap_of_common`) -/

/-- Sub-Cardy exponential decay of the deep left tail `∫_0^{c'(ξ_* - δ)²/3} |g| V_src`
using `stripPoissonJensen_general C.F.prob` + `hAt.upper` + `hAt.cardyNorm_ge`. -/
lemma lemmaG_src_of_common (C : CommonSource) (D : UniformPropositionPData C.F.prob)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < xiStar) :
    ∃ c_deep C_deep κ_deep : ℝ,
      1 ≤ c_deep ∧ 24 * C.a₀ ≤ c_deep ∧ 24 * C.F.prob.totalShift ≤ c_deep ∧
      D.c₀ ≤ c_deep ∧ 0 < C_deep ∧ 0 < κ_deep ∧
      ∀ {c' : ℝ}, c_deep ≤ c' →
        ∀ {g : ℝ → ℝ}, TestClass C.src (c' / 12) g →
          ∫ t in (0 : ℝ)..(c' * (xiStar - δ) ^ 2 / 3), |g t| * C.src.cardyV (c' / 12) t ≤
            C_deep * Real.exp (-κ_deep * c') * C.src.cardyNorm (c' / 12) g := by
  obtain ⟨c_Kw, C_Klo, hcKw8, hCKlo, hPJ_thm⟩ := stripPoissonJensen_general C.F.prob
  let C_PJ : ℝ := pjConstOf D.C_e D.c_band C_Klo (slitL xiStar)
  let c_PJ : ℝ := max (max D.c₀ c_Kw) (max 1 (max (24 * C.a₀) (24 * C.F.prob.totalShift)))
  have hcPJ1 : 1 ≤ c_PJ := (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨C_M1, C_M2, hCM1, hpropM⟩ := proposition_M_exp_general realSliceData
    (C_PJ := C_PJ) (p_e := D.p_e) hcPJ1 D.hp_e_nn
  let κ₀ : ℝ := 2.228 * δ ^ ((3 : ℝ) / 2)
  have hκ₀ : 0 < κ₀ := by positivity
  obtain ⟨C₄, _, hC₄le⟩ := Integration.exists_rpow_le_mul_exp (p := C_M1 + 1) (κ := κ₀ / 2)
    (by positivity)
  have hC₄_pos : 0 < C₄ := by
    have h1 := hC₄le 1 le_rfl
    simp only [Real.one_rpow] at h1
    nlinarith [Real.exp_pos (κ₀ / 2 * 1)]
  let x₀ : ℝ := xiStar - δ
  have hx₀_pos : 0 < x₀ := sub_pos.mpr hδ1
  let C_up_src : ℝ := max 1 C.src.tv
  have hCup_pos : 0 < C_up_src := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let C_deep : ℝ :=
    (2 / δ) * Real.exp C_M2 * C_up_src * 2 ^ (C.src.w + 1) * C₄ * max 1 C.F.d⁻¹
  let κ_deep : ℝ := κ₀ / 2
  have hca0_PJ : 24 * C.a₀ ≤ c_PJ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcS_PJ : 24 * C.F.prob.totalShift ≤ c_PJ := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨c_PJ, C_deep, κ_deep, hcPJ1, hca0_PJ, hcS_PJ,
    (le_max_left _ _).trans (le_max_left _ _), ?_, half_pos hκ₀, fun {c'} hc' {g} hg => ?_⟩
  · have := Real.exp_pos C_M2
    have : 0 < max 1 C.F.d⁻¹ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  have hc₀' : D.c₀ ≤ c' := ((le_max_left _ _).trans (le_max_left _ _)).trans hc'
  have hcKw' : c_Kw ≤ c' := ((le_max_right _ _).trans (le_max_left _ _)).trans hc'
  have hc1 : 1 ≤ c' := hcPJ1.trans hc'
  have hc0 : 0 < c' := by linarith
  have hc_a0 : 24 * C.a₀ ≤ c' := hca0_PJ.trans hc'
  have hc_S : 24 * C.F.prob.totalShift ≤ c' := hcS_PJ.trans hc'
  have ha : C.a₀ ≤ c' / 12 := by linarith
  have hAt := C.at_ ha
  have hg0 := hAt.testClass_prob hg
  let P := D.pAt hc₀'
  by_cases hMpos : 0 < C.src.cardyNorm (c' / 12) g
  · have hc_prob : max 1 (max (24 * C.F.prob.totalShift) (24 * C.a₀)) ≤ c' :=
      max_le hc1 (max_le hc_S hc_a0)
    have hM0_pos : 0 < C.F.prob.cardyNorm (c' / 12) g :=
      cardyNorm_prob_pos_of_src_pos C hc_prob hg hMpos
    set M₀ : ℝ := C.F.prob.cardyNorm (c' / 12) g
    have hPJ_at : ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
        Real.log |g (c' * x ^ 2 / 3)| ≤ c' * majorantReal x + Real.log M₀ -
          (1 / 2 : ℝ) * Real.log c' +
          (D.p_e + 1 / 2) * (1 - realSliceData.slitMassAt x) * Real.log c' +
          realSliceData.slitEntropyAt x + C_PJ := by
      intro x hx hx_ne
      have h := hPJ_thm P hcKw' hg0 hM0_pos x hx hx_ne
      rwa [D.uniform_C_e hc₀', D.uniform_p_e hc₀', D.uniform_c_band hc₀'] at h
    have hexp_bd := hpropM hc' hM0_pos hPJ_at
    let t₀ : ℝ := c' * x₀ ^ 2 / 3
    let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
    let φ' : ℝ → ℝ := fun x => (2 / 3 : ℝ) * c' * x
    have hsub : ∫ x in (0 : ℝ)..x₀, (|g (φ x)| * C.src.cardyV (c' / 12) (φ x)) * φ' x =
        ∫ t in (0 : ℝ)..t₀, |g t| * C.src.cardyV (c' / 12) t := by
      have hd : ∀ x ∈ uIcc (0 : ℝ) x₀, HasDerivAt φ (φ' x) x := fun x _ => by
        dsimp [φ, φ']
        exact ((hasDerivAt_pow 2 x).const_mul c' |>.div_const 3).congr_deriv (by ring)
      have hcont_φ' : ContinuousOn φ' (uIcc (0 : ℝ) x₀) := by dsimp [φ']; fun_prop
      have hcont_f : ContinuousOn (fun t => |g t| * C.src.cardyV (c' / 12) t) (φ '' uIcc 0 x₀) := by
        refine (hg.cont.abs.mul (C.src.continuous_cardyV (c' / 12)).continuousOn).mono ?_
        rintro t ⟨x, _, rfl⟩
        exact mem_Ici.mpr (div_nonneg (mul_nonneg hc0.le (sq_nonneg x)) (by norm_num))
      simpa [φ, t₀] using intervalIntegral.integral_comp_mul_deriv' hd hcont_φ' hcont_f
    rw [← hsub]
    have hpt : ∀ x ∈ Icc (0 : ℝ) x₀,
        (|g (φ x)| * C.src.cardyV (c' / 12) (φ x)) * φ' x ≤
          Real.exp C_M2 * M₀ * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
            (2 * C_up_src * 2 ^ (C.src.w - 1)) * c' *
            Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
      · have hφ0 : φ' 0 = 0 := by dsimp [φ']; ring
        rw [hφ0, mul_zero]; positivity
      have hx_mem : x ∈ Ico 0 xiStar := ⟨hx.1, hx.2.trans_lt (by linarith)⟩
      have hx_lt1 : x < 1 := hx_mem.2.trans xiStar_lt_one
      have hx_pos_δ : δ ≤ xiStar - x := by dsimp [x₀] at hx; linarith [hx.2]
      have hMexp := hexp_bd x hx_mem
      have hU_le : majorantReal x + (2 * π / 3) * x ≤ -κ₀ := by
        have h1 := majorantReal_g_deficit hx_mem
        have h2 := slitDeficit_ge (le_trans hδ0.le hx_pos_δ) (by linarith [hx.1])
        have h3 : δ ^ ((3 : ℝ) / 2) ≤ (xiStar - x) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow hδ0.le hx_pos_δ (by norm_num)
        calc majorantReal x + (2 * π / 3) * x ≤ -slitDeficit (xiStar - x) := h1
          _ ≤ -(2.228 * (xiStar - x) ^ ((3 : ℝ) / 2)) := neg_le_neg h2
          _ ≤ -(2.228 * δ ^ ((3 : ℝ) / 2)) := neg_le_neg (mul_le_mul_of_nonneg_left h3 (by norm_num))
          _ = -κ₀ := rfl
      have hdx_pos : 0 < xiStar - x := lt_of_lt_of_le hδ0 hx_pos_δ
      have hφx_nn : 0 ≤ φ x := div_nonneg (mul_nonneg hc0.le (sq_nonneg x)) (by norm_num)
      have hV_le : C.src.cardyV (c' / 12) (φ x) ≤
          2 * C_up_src * 2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x) := by
        have hup : C.src.cardyV (c' / 12) (φ x) ≤ C.src.tv * kernelK C.src.w (c' / 12) (φ x) :=
          hAt.upper hφx_nn
        have hK_ub := kernelK_le_pow_mul_exp C.src.hw (by positivity : 0 < c' / 12) hφx_nn
        have hs1 : Real.sqrt ((φ x) / (c' / 12)) ≤ 2 := by
          have heq : (φ x) / (c' / 12) = (2 * x) ^ 2 := by
            dsimp [φ]; field_simp [hc0.ne']; ring
          rw [heq, Real.sqrt_sq (by linarith [hx_pos])]
          linarith [hx_lt1]
        have hs2 : 4 * π * Real.sqrt ((c' / 12) * (φ x)) = c' * (2 * π / 3) * x := by
          have heq : (c' / 12) * (φ x) = (c' * x / 6) ^ 2 := by dsimp [φ]; ring
          rw [heq, Real.sqrt_sq (by positivity [hx_pos])]
          ring
        rw [hs2] at hK_ub
        have hK_ub2 : kernelK C.src.w (c' / 12) (φ x) ≤
            2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x) :=
          hK_ub.trans (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs1 _) (Real.exp_pos _).le)
        calc C.src.cardyV (c' / 12) (φ x)
            ≤ C.src.tv * kernelK C.src.w (c' / 12) (φ x) := hup
          _ ≤ C_up_src * (2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x)) :=
              mul_le_mul (le_max_right _ _) hK_ub2
                (kernelK_nonneg (by positivity) hφx_nn) hCup_pos.le
          _ ≤ 2 * C_up_src * 2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x) := by
              have hnn_A : 0 ≤ C_up_src * (2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x)) :=
                mul_nonneg hCup_pos.le (mul_nonneg (pow_nonneg zero_le_two _)
                  (Real.exp_pos (c' * (2 * π / 3) * x)).le)
              calc C_up_src * (2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x))
                  = 1 * (C_up_src * (2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x))) :=
                    (one_mul _).symm
                _ ≤ 2 * (C_up_src * (2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x))) :=
                    mul_le_mul_of_nonneg_right one_le_two hnn_A
                _ = 2 * C_up_src * 2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x) := by ring
      have hsqrt_le : Real.sqrt (xiStar - x) ≤ 1 := by
        calc Real.sqrt (xiStar - x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith [hx.1, xiStar_lt_one])
          _ = 1 := Real.sqrt_one
      have hexp_comb : Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
            Real.exp (c' * (2 * π / 3) * x) ≤ Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h1 : c' * (majorantReal x + (2 * π / 3) * x) ≤ c' * (-κ₀) :=
          mul_le_mul_of_nonneg_left hU_le hc0.le
        have h2 : C_M1 * Real.sqrt (xiStar - x) * Real.log c' ≤ C_M1 * Real.log c' := by
          calc C_M1 * Real.sqrt (xiStar - x) * Real.log c'
              ≤ C_M1 * 1 * Real.log c' :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt_le hCM1) (Real.log_nonneg hc1)
            _ = C_M1 * Real.log c' := by ring
        linarith
      have hinv_le : (xiStar - x)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ0 hx_pos_δ
      have hV_nn := hAt.nonneg_V hφx_nn
      have hφ'_le : φ' x ≤ c' := by dsimp [φ']; nlinarith [hx_lt1, hc0]
      have hφ'_nn : 0 ≤ φ' x := by dsimp [φ']; positivity [hx_pos]
      have hgV : |g (φ x)| * C.src.cardyV (c' / 12) (φ x) ≤
          Real.exp C_M2 * M₀ * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
            (2 * C_up_src * 2 ^ (C.src.w - 1)) * Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
        calc |g (φ x)| * C.src.cardyV (c' / 12) (φ x)
            ≤ (Real.exp C_M2 * M₀ * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹ *
                Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c')) *
                (2 * C_up_src * 2 ^ (C.src.w - 1) * Real.exp (c' * (2 * π / 3) * x)) :=
              mul_le_mul hMexp hV_le hV_nn (by positivity [hdx_pos])
          _ = (Real.exp C_M2 * M₀ * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹) *
                (2 * C_up_src * 2 ^ (C.src.w - 1)) *
                (Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
                  Real.exp (c' * (2 * π / 3) * x)) := by ring
          _ ≤ (Real.exp C_M2 * M₀ * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹) *
                (2 * C_up_src * 2 ^ (C.src.w - 1)) * Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
              gcongr
          _ = _ := by ring
      calc (|g (φ x)| * C.src.cardyV (c' / 12) (φ x)) * φ' x
          ≤ (Real.exp C_M2 * M₀ * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
              (2 * C_up_src * 2 ^ (C.src.w - 1)) * Real.exp (-κ₀ * c' + C_M1 * Real.log c')) * c' :=
            mul_le_mul hgV hφ'_le hφ'_nn (by positivity)
        _ = _ := by ring
    have hcont_lhs : ContinuousOn (fun x => (|g (φ x)| * C.src.cardyV (c' / 12) (φ x)) * φ' x)
        (uIcc 0 x₀) := by
      have hφ_nonneg : ∀ x : ℝ, 0 ≤ φ x := fun x =>
        div_nonneg (mul_nonneg hc0.le (sq_nonneg x)) (by norm_num)
      have h1 : ContinuousOn (fun x => g (φ x)) (uIcc 0 x₀) :=
        hg.cont.comp (by dsimp [φ]; fun_prop) (fun x _ => mem_Ici.mpr (hφ_nonneg x))
      exact ((h1.abs.mul ((C.src.continuous_cardyV (c' / 12)).continuousOn.comp
        (by dsimp [φ]; fun_prop) (fun _ _ => mem_univ _)))).mul (by dsimp [φ']; fun_prop)
    have hint_bd := intervalIntegral.integral_mono_on hx₀_pos.le
      (hcont_lhs.intervalIntegrable (μ := volume)) (intervalIntegrable_const (μ := volume)) hpt
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint_bd
    have hpow_comb : c' ^ (-(1 / 2 : ℝ)) * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c') ≤
        C₄ * Real.exp (-κ_deep * c') := by
      have hcm_eq : Real.exp (C_M1 * Real.log c') = c' ^ C_M1 := by
        rw [Real.rpow_def_of_pos hc0]; ring_nf
      have hcm1_nn : c' ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      have hpow_tot : c' ^ (-(1 / 2 : ℝ)) * (c' ^ C_M1 * c') ≤ c' ^ (C_M1 + 1) := by
        have heq : c' ^ C_M1 * c' = c' ^ (C_M1 + 1) := by
          calc c' ^ C_M1 * c' = c' ^ C_M1 * c' ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = c' ^ (C_M1 + 1) := (Real.rpow_add hc0 _ _).symm
        rw [heq]
        exact mul_le_of_le_one_left (Real.rpow_nonneg hc0.le _) hcm1_nn
      calc c' ^ (-(1 / 2 : ℝ)) * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c')
          = c' ^ (-(1 / 2 : ℝ)) * c' * (Real.exp (-κ₀ * c') * Real.exp (C_M1 * Real.log c')) := by
            rw [Real.exp_add]
        _ = (c' ^ (-(1 / 2 : ℝ)) * (c' ^ C_M1 * c')) * Real.exp (-κ₀ * c') := by
            rw [hcm_eq]; ring
        _ ≤ c' ^ (C_M1 + 1) * Real.exp (-κ₀ * c') :=
            mul_le_mul_of_nonneg_right hpow_tot (Real.exp_pos _).le
        _ ≤ (C₄ * Real.exp (κ₀ / 2 * c')) * Real.exp (-κ₀ * c') :=
            mul_le_mul_of_nonneg_right (hC₄le c' hc1) (Real.exp_pos _).le
        _ = C₄ * Real.exp (-κ_deep * c') := by
            dsimp [κ_deep]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have hx₀_le1 : x₀ ≤ 1 := by dsimp [x₀]; linarith [xiStar_lt_one]
    have hM0_le : M₀ ≤ max 1 C.F.d⁻¹ * C.src.cardyNorm (c' / 12) g := by
      have hge := hAt.cardyNorm_ge hg
      have hd_inv : C.F.d⁻¹ * (C.F.d * M₀) ≤ C.F.d⁻¹ * C.src.cardyNorm (c' / 12) g :=
        mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr C.F.hd.le)
      rw [← mul_assoc, inv_mul_cancel₀ C.F.hd.ne', one_mul] at hd_inv
      exact hd_inv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hMpos.le)
    calc ∫ x in (0 : ℝ)..x₀, (|g (φ x)| * C.src.cardyV (c' / 12) (φ x)) * φ' x
        ≤ x₀ * (Real.exp C_M2 * M₀ * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
            (2 * C_up_src * 2 ^ (C.src.w - 1)) * c' *
            Real.exp (-κ₀ * c' + C_M1 * Real.log c')) := hint_bd
      _ ≤ 1 * (Real.exp C_M2 * M₀ * δ⁻¹ * (2 * C_up_src * 2 ^ (C.src.w - 1)) *
            (c' ^ (-(1 / 2 : ℝ)) * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c'))) := by
          have hnn : 0 ≤ Real.exp C_M2 * M₀ * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
              (2 * C_up_src * 2 ^ (C.src.w - 1)) * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
            positivity
          refine (mul_le_mul_of_nonneg_right hx₀_le1 hnn).trans_eq (by ring)
      _ ≤ 1 * (Real.exp C_M2 * (max 1 C.F.d⁻¹ * C.src.cardyNorm (c' / 12) g) * δ⁻¹ *
            (2 * C_up_src * 2 ^ (C.src.w - 1)) *
            (c' ^ (-(1 / 2 : ℝ)) * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c'))) := by
          gcongr
      _ ≤ 1 * (Real.exp C_M2 * (max 1 C.F.d⁻¹ * C.src.cardyNorm (c' / 12) g) * δ⁻¹ *
            (2 * C_up_src * 2 ^ (C.src.w + 1)) * (C₄ * Real.exp (-κ_deep * c'))) := by
          have hpow2 : (2 : ℝ) ^ (C.src.w - 1) ≤ (2 : ℝ) ^ (C.src.w + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          gcongr
      _ = C_deep * Real.exp (-κ_deep * c') * C.src.cardyNorm (c' / 12) g := by
          dsimp [C_deep]; ring
  · push Not at hMpos
    have hMnn := cardyNorm_src_nonneg ha g
    have hMzero : C.src.cardyNorm (c' / 12) g = 0 := le_antisymm hMpos hMnn
    have hae0 : (fun t => |g t| * C.src.cardyV (c' / 12) t) =ᵐ[volume.restrict (Ioi 0)] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
          mul_nonneg (abs_nonneg _) (hAt.nonneg_V (mem_Ioi.mp ht).le))
        hg.int_cardy).mp hMzero
    have hzero : ∫ t in (0 : ℝ)..(c' * x₀ ^ 2 / 3), |g t| * C.src.cardyV (c' / 12) t = 0 := by
      have ht_nn : 0 ≤ c' * x₀ ^ 2 / 3 := by positivity
      rw [intervalIntegral.integral_of_le ht_nn]
      exact setIntegral_eq_zero_of_ae_eq_zero ((ae_restrict_iff' measurableSet_Ioc).mp (hae0.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))))
    rw [hzero, hMzero, mul_zero]

lemma deltaLobeSrc_gap_of_common (C : CommonSource) (D : UniformPropositionPData C.F.prob)
    {r_1 : ℝ} (hr1_pos : 0 < r_1) (_hr1_le : r_1 ≤ D.r_1) :
    ∃ c_gap C_gap κ_gap : ℝ,
      24 * C.a₀ ≤ c_gap ∧ 24 * C.F.prob.totalShift ≤ c_gap ∧ D.c₀ ≤ c_gap ∧ 1 ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' T : ℝ} {g : ℝ → ℝ}, c_gap ≤ c' →
        C.src.IsWeaklyFeasible (c' / 12) T g →
          0 < C.src.cardyNorm (c' / 12) g ∧
          deltaLobeSrc C.src r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
          deltaLobeSrc C.src r_1 c' g < 1 / 2 ∧
          virasoroDeltaChart c' (chartAC r_1 c' ^ 2) < T := by
  have hb_end := virasoroBChart_ofReal one_pos (u := 2 * chartBV r_1 ^ 2) (by
    rw [abs_of_nonneg (by positivity)]
    have hle := chartAC_sq_le_virasoroAC_sq hr1_pos zero_le_one
    rwa [chartAC_sq _ 1 zero_le_one, Real.one_rpow, mul_one] at hle)
  let x_cap : ℝ := (virasoroBChart 1 (2 * chartBV r_1 ^ 2 : ℝ)).re
  have hx_cap_gt0 : 0 < x_cap := hb_end.2.1
  have hx_cap_lt_xi : x_cap < xiStar := by
    have hA2_1 : 2 * chartBV r_1 ^ 2 ≤ virasoroAC 1 ^ 2 := by
      have hle := chartAC_sq_le_virasoroAC_sq hr1_pos zero_le_one
      rwa [chartAC_sq _ 1 zero_le_one, Real.one_rpow, mul_one] at hle
    have hneg : virasoroDeltaChart 1 (2 * chartBV r_1 ^ 2) < xiBar * 1 := by
      have h1 := virasoroDeltaChart_strictAnti one_pos
        (Set.mem_Icc.mpr ⟨neg_nonpos.mpr (sq_nonneg _), sq_nonneg _⟩)
        (Set.mem_Icc.mpr ⟨by linarith [sq_nonneg (virasoroAC 1), sq_nonneg (chartBV r_1)], hA2_1⟩)
        (mul_pos two_pos (sq_pos_of_pos (chartBV_pos hr1_pos)))
      rw [virasoroDeltaChart_zero] at h1
      exact h1
    have hsq : x_cap ^ 2 < xiStar ^ 2 := by
      have h2 := hb_end.2.2.2
      rw [show ((1 : ℝ) : ℂ) * virasoroBChart 1 (2 * chartBV r_1 ^ 2 : ℝ) ^ 2 / 3 =
        ((x_cap ^ 2 / 3 : ℝ) : ℂ) from by
          have him : (virasoroBChart 1 (2 * chartBV r_1 ^ 2 : ℝ)).im = 0 := hb_end.1
          have : virasoroBChart 1 (2 * chartBV r_1 ^ 2 : ℝ) = (x_cap : ℂ) := Complex.ext rfl him
          rw [this]; push_cast; ring] at h2
      have hre_eq := congrArg Complex.re h2
      simp only [Complex.ofReal_re] at hre_eq
      unfold xiBar at hneg
      linarith
    nlinarith [hx_cap_gt0, xiStar_pos]
  let δ : ℝ := xiStar - x_cap
  have hδ0 : 0 < δ := sub_pos.mpr hx_cap_lt_xi
  have hδ1 : δ < xiStar := by dsimp [δ]; linarith
  obtain ⟨c_deep, C_gap, κ_gap, hc_deep1, hc_a0, hc_S, hc_D, hC_pos, hκ_pos, hdeep⟩ :=
    lemmaG_src_of_common C D hδ0 hδ1
  let c_gap : ℝ := max c_deep ((Real.log (2 * C_gap) + 1) / κ_gap)
  have hΔ_eq : ∀ {c' : ℝ}, 0 < c' →
      virasoroDeltaChart c' (chartAC r_1 c' ^ 2) = c' * x_cap ^ 2 / 3 := by
    intro c' hc'_pos
    unfold virasoroDeltaChart virasoroXiChartC
    have hm_r : chartAC r_1 c' ^ 2 * c' ^ (-(2 / 3 : ℝ)) = 2 * chartBV r_1 ^ 2 := by
      rw [chartAC_sq r_1 c' hc'_pos.le, mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel,
        Real.rpow_zero, mul_one]
    have hmul : ((chartAC r_1 c' ^ 2 : ℝ) : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
        ((2 * chartBV r_1 ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hm_r]
    have h1 : (virasoroXiInf (((2 * chartBV r_1 ^ 2 : ℝ) : ℂ))).re =
        virasoroDeltaChart 1 (2 * chartBV r_1 ^ 2) := by
      unfold virasoroDeltaChart virasoroXiChartC; simp
    rw [hmul, h1]
    have h2 := hb_end.2.2.2
    have hcap : virasoroBChart 1 (2 * chartBV r_1 ^ 2 : ℝ) = (x_cap : ℂ) := Complex.ext rfl hb_end.1
    have hxsq : ((x_cap ^ 2 / 3 : ℝ) : ℂ) =
        ((1 : ℝ) : ℂ) * virasoroBChart 1 (2 * chartBV r_1 ^ 2 : ℝ) ^ 2 / 3 := by
      rw [hcap]; push_cast; ring
    have hre_eq := congrArg Complex.re (hxsq.trans h2)
    rw [Complex.ofReal_re, Complex.ofReal_re] at hre_eq
    rw [← hre_eq]; ring
  refine ⟨c_gap, C_gap, κ_gap, hc_a0.trans (le_max_left _ _), hc_S.trans (le_max_left _ _), hc_D.trans (le_max_left _ _),
    hc_deep1.trans (le_max_left _ _), hC_pos, hκ_pos, fun {c' T g} hc' hwf => ?_⟩
  have hc'_deep : c_deep ≤ c' := (le_max_left _ _).trans hc'
  have hlog_bd : (Real.log (2 * C_gap) + 1) / κ_gap ≤ c' := (le_max_right _ _).trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le (zero_lt_one.trans_le hc_deep1) hc'_deep
  have ha : C.a₀ ≤ c' / 12 := by have : 24 * C.a₀ ≤ c' := hc_a0.trans hc'_deep; linarith
  have hM_pos : 0 < C.src.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero_src C ha hwf.1 hwf.2.1
  have hbd_self : deltaLobeSrc C.src r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') := by
    have hbd := hdeep hc'_deep hwf.1
    rw [show xiStar - δ = x_cap by dsimp [δ]; ring, ← hΔ_eq hc'_pos] at hbd
    unfold deltaLobeSrc
    calc (C.src.cardyNorm (c' / 12) g)⁻¹ *
          ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartAC r_1 c' ^ 2)),
            |g t| * C.src.cardyV (c' / 12) t
        ≤ (C.src.cardyNorm (c' / 12) g)⁻¹ *
            (C_gap * Real.exp (-κ_gap * c') * C.src.cardyNorm (c' / 12) g) :=
          mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hM_pos.le)
      _ = C_gap * Real.exp (-κ_gap * c') := by field_simp [hM_pos.ne']
  have hexp_half : C_gap * Real.exp (-κ_gap * c') < 1 / 2 := by
    have hmul : Real.log (2 * C_gap) + 1 ≤ κ_gap * c' := by
      linarith [(div_le_iff₀ hκ_pos).mp hlog_bd]
    have hneg : -κ_gap * c' < -Real.log (2 * C_gap) := by linarith
    have hexp : Real.exp (-κ_gap * c') < (2 * C_gap)⁻¹ := by
      calc Real.exp (-κ_gap * c') < Real.exp (-Real.log (2 * C_gap)) := Real.exp_lt_exp.mpr hneg
        _ = (2 * C_gap)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
    calc C_gap * Real.exp (-κ_gap * c') < C_gap * (2 * C_gap)⁻¹ :=
          mul_lt_mul_of_pos_left hexp hC_pos
      _ = 1 / 2 := by field_simp [hC_pos.ne']
  have hdl_half : deltaLobeSrc C.src r_1 c' g < 1 / 2 := hbd_self.trans_lt hexp_half
  have hT_gt : virasoroDeltaChart c' (chartAC r_1 c' ^ 2) < T := by
    by_contra hle
    push Not at hle
    have hΔ_pos : 0 < virasoroDeltaChart c' (chartAC r_1 c' ^ 2) :=
      virasoroDeltaChart_pos hc'_pos
        (chart_real_abs_le_virasoro hr1_pos hc'_pos (by rw [abs_of_nonneg (sq_nonneg _)]))
    let T' : ℝ := max 0 T
    have hT'_nn : 0 ≤ T' := le_max_left _ _
    have hT'_le : T' ≤ virasoroDeltaChart c' (chartAC r_1 c' ^ 2) := max_le hΔ_pos.le hle
    have htail' : ∀ t ≥ T', 0 ≤ g t := fun t ht => hwf.2.2.2 t ((le_max_right 0 T).trans ht)
    have hV_nonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ C.src.cardyV (c' / 12) t := (C.at_ ha).nonneg_V
    have hhalf : C.src.cardyNorm (c' / 12) g / 2 ≤
        ∫ t in (0 : ℝ)..T', |g t| * C.src.cardyV (c' / 12) t := by
      have hint_gV : IntegrableOn (fun t => g t * C.src.cardyV (c' / 12) t) (Ioi 0) :=
        hwf.1.int_cardy.norm.mono'
          (((hwf.1.cont.mul (C.src.continuous_cardyV (c' / 12)).continuousOn).mono
            Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
          (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
      have h1 : ∫ t in Ioi (0 : ℝ), g t * C.src.cardyV (c' / 12) t ≤ 0 := by
        have := hwf.2.2.1; unfold ShiftSource.gVac at this; nlinarith [Real.pi_pos]
      have hunion : Ioc (0 : ℝ) T' ∪ Ioi T' = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hT'_nn
      have hdisj := Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := T')
      have hM_split : C.src.cardyNorm (c' / 12) g =
          (∫ t in Ioc 0 T', |g t| * C.src.cardyV (c' / 12) t) +
          (∫ t in Ioi T', |g t| * C.src.cardyV (c' / 12) t) := by
        unfold ShiftSource.cardyNorm
        rw [← hunion]
        exact setIntegral_union hdisj measurableSet_Ioi
          (hwf.1.int_cardy.mono_set Ioc_subset_Ioi_self)
          (hwf.1.int_cardy.mono_set (Ioi_subset_Ioi hT'_nn))
      have hgV_split : ∫ t in Ioi (0 : ℝ), g t * C.src.cardyV (c' / 12) t =
          (∫ t in Ioc 0 T', g t * C.src.cardyV (c' / 12) t) +
          (∫ t in Ioi T', g t * C.src.cardyV (c' / 12) t) := by
        rw [← hunion]
        exact setIntegral_union hdisj measurableSet_Ioi
          (hint_gV.mono_set Ioc_subset_Ioi_self)
          (hint_gV.mono_set (Ioi_subset_Ioi hT'_nn))
      have htail_eq : ∫ t in Ioi T', g t * C.src.cardyV (c' / 12) t =
          ∫ t in Ioi T', |g t| * C.src.cardyV (c' / 12) t :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht => by
          rw [abs_of_nonneg (htail' t (mem_Ioi.mp ht).le)]
      have hhead_le : -(∫ t in Ioc 0 T', |g t| * C.src.cardyV (c' / 12) t) ≤
          ∫ t in Ioc 0 T', g t * C.src.cardyV (c' / 12) t := by
        rw [← integral_neg]
        refine setIntegral_mono_on
          ((hwf.1.int_cardy.mono_set Ioc_subset_Ioi_self).neg)
          (hint_gV.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
        have hV := hV_nonneg ht.1.le
        calc -(|g t| * C.src.cardyV (c' / 12) t) = (-|g t|) * C.src.cardyV (c' / 12) t := by ring
          _ ≤ g t * C.src.cardyV (c' / 12) t := mul_le_mul_of_nonneg_right (neg_abs_le (g t)) hV
      rw [intervalIntegral.integral_of_le hT'_nn]
      linarith
    have hint_le : ∫ t in (0 : ℝ)..T', |g t| * C.src.cardyV (c' / 12) t ≤
        ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartAC r_1 c' ^ 2)),
          |g t| * C.src.cardyV (c' / 12) t := by
      rw [intervalIntegral.integral_of_le hT'_nn, intervalIntegral.integral_of_le hΔ_pos.le]
      refine setIntegral_mono_set (hwf.1.int_cardy.mono_set Ioc_subset_Ioi_self) ?_
        (Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hT'_le⟩)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (abs_nonneg _) (hV_nonneg ht.1.le)
    have hdiv_le : (1 / 2 : ℝ) ≤ deltaLobeSrc C.src r_1 c' g := by
      unfold deltaLobeSrc
      have h1 := mul_le_mul_of_nonneg_left (hhalf.trans hint_le) (inv_nonneg.mpr hM_pos.le)
      have h2 : (C.src.cardyNorm (c' / 12) g)⁻¹ * (C.src.cardyNorm (c' / 12) g / 2) = 1 / 2 := by
        field_simp [hM_pos.ne']
      linarith
    linarith
  exact ⟨hM_pos, hbd_self, hdl_half, hT_gt⟩

end FormalResearch.ModularBootstrap.Mixtures
