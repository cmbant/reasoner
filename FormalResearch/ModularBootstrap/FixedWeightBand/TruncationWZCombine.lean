module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWZSeg

/-!
# Lemma Z at weight `w`: assembly of the envelope inequality

`lemma_Z_combine_envelope_W` (weight-`w` version of `Contour.lemma_Z_combine_envelope`): the segment bound
`‖P(ũ)‖ ≤ 12 C_pref c'^{1/3} B_seg_unit airyEnv ũ` and Lemma D' (`‖P - Ψ̃‖ ≤ C_D e^{-d_D c'} airyEnv`) give
`‖Ψ̃(ũ)‖ ≤ C_B Λ airyEnv(ũ) (Re ũ^{1/2})^{-3/2} |ũ|^{-3/4}`. The estimate is weight-free in form.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.ChartGeometry
open FormalResearch.ModularBootstrap.ComplexBessel
open FormalResearch.ModularBootstrap.StripMultiplier
open FormalResearch.ModularBootstrap.Mellin
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.WeightAxioms

lemma lemma_Z_combine_envelope_W {prob : FixedWeightProblem} {D : UniformPropositionPData prob}
    (W : ZWitnessW D) (P : ZPConfig)
    {b_hi c' Λ φ ρ κ_all C_pref B_seg_unit C_B : ℝ}
    {g : ℝ → ℝ} {u : ℂ}
    (hb_hi_pos : 0 < b_hi) (hc'_pos : 0 < c') (hc'_ge1 : 1 ≤ c')
    (hΛ : 1 ≤ Λ) (hκ_all_pos : 0 < κ_all) (hκ_le_D : κ_all ≤ W.d_D)
    (hC_pref_pos : 0 < C_pref)
    (hu_pos : 0 < ‖u‖) (hu_bhi : ‖u‖ ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ))
    (hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re)
    (hu_re_eq : (u ^ (1 / 2 : ℂ)).re = Real.sqrt ‖u‖ * Real.sin φ)
    (hsin_pos : 0 < Real.sin φ) (hsin_le1 : Real.sin φ ≤ 1)
    (_hρ_pos : 0 < ρ)
    (hρ_lo : (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt ‖u‖) ≤ ρ)
    (hB_seg_eq : B_seg_unit =
      (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
        ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) +
      max W.C_S4 W.C_S2 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)))
    (hCB_ge : 12 * C_pref * Real.pi / Real.sqrt ((9 / 10 : ℝ) * P.c_γ * kappaV) *
        b_hi ^ (5 / 2 : ℝ) +
      (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 * (4 / κ_all ^ 2) ≤ C_B)
    (hP_norm : ‖truncatedMellinPW prob c' dpT0 g u‖ ≤
      12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u)
    (hDp_u : ‖truncatedMellinPW prob c' dpT0 g u - psiTilde prob c' g u‖ ≤
      W.C_D * Real.exp (-W.d_D * c') * airyEnv u) :
    ‖psiTilde prob c' g u‖ ≤
      C_B * Λ * airyEnv u *
        (u ^ (1 / 2 : ℂ)).re ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
  set a' : ℝ := Real.sqrt ‖u‖
  have ha'_pos : 0 < a' := Real.sqrt_pos.mpr hu_pos
  set c_γ_kap : ℝ := (9 / 10 : ℝ) * P.c_γ * kappaV
  have hc_γ_kap_pos : 0 < c_γ_kap := by
    have := P.hc_γ_pos; have := kappaV_pos; positivity
  set C_win_tot : ℝ := 12 * C_pref * Real.pi / Real.sqrt c_γ_kap * b_hi ^ (5 / 2 : ℝ)
  set C_tail_tot : ℝ := (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 * (4 / κ_all ^ 2)
  have hDp_exp_le : Real.exp (-W.d_D * c') ≤ Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    have hc56_le : c' ^ (5 / 6 : ℝ) ≤ c' :=
      (Real.rpow_le_rpow_of_exponent_le hc'_ge1 (by norm_num)).trans_eq (Real.rpow_one c')
    have hprod := mul_le_mul hκ_le_D hc56_le (Real.rpow_nonneg hc'_pos.le _) W.hd_D.le
    linarith only [hprod]
  have hDp_c13 : W.C_D * Real.exp (-W.d_D * c') * airyEnv u ≤
      W.C_D * c' ^ (1 / 3 : ℝ) * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u := by
    have hc13_ge1 : 1 ≤ c' ^ (1 / 3 : ℝ) := Real.one_le_rpow hc'_ge1 (by norm_num)
    have hair_nn : 0 ≤ airyEnv u := (airyEnv_pos u).le
    calc W.C_D * Real.exp (-W.d_D * c') * airyEnv u
        ≤ W.C_D * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDp_exp_le W.hC_D.le) hair_nn
      _ = W.C_D * 1 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u := by ring
      _ ≤ W.C_D * c' ^ (1 / 3 : ℝ) * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc13_ge1 W.hC_D.le) (Real.exp_pos _).le) hair_nn
  set u_re : ℝ := (u ^ (1 / 2 : ℂ)).re
  set u_n : ℝ := ‖u‖
  have hu_re_ub : u_re ≤ u_n ^ (1 / 2 : ℝ) := by
    rw [hu_re_eq, ← Real.sqrt_eq_rpow]
    exact mul_le_of_le_one_right ha'_pos.le hsin_le1
  have hfac_pos : 0 < u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) := by positivity
  have hwin_prod_le :
      (12 * C_pref * c' ^ (1 / 3 : ℝ) *
          ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
            ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)))) *
        (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤ C_win_tot * Λ := by
    have hsqrt_ρ_lb : Real.sqrt c_γ_kap * c' ^ (1 / 3 : ℝ) * u_n ^ (1 / 4 : ℝ) ≤
        Real.sqrt (c' * P.c_γ * ρ) := by
      have h1 : c_γ_kap * c' ^ (2 / 3 : ℝ) * u_n ^ (1 / 2 : ℝ) ≤ c' * P.c_γ * ρ := by
        have hc23 : c' * c' ^ (-(1 / 3 : ℝ)) = c' ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_one_add' hc'_pos.le (by norm_num : (1 : ℝ) + -(1 / 3 : ℝ) ≠ 0)]
          norm_num
        have ha_rpow : a' = u_n ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow u_n
        calc c_γ_kap * c' ^ (2 / 3 : ℝ) * u_n ^ (1 / 2 : ℝ)
            = c' * P.c_γ * ((9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a')) := by
              rw [← hc23, ← ha_rpow]; dsimp [c_γ_kap]; ring
          _ ≤ c' * P.c_γ * ρ :=
              mul_le_mul_of_nonneg_left hρ_lo (mul_nonneg hc'_pos.le P.hc_γ_pos.le)
      have hrt := Real.sqrt_le_sqrt h1
      have hlhs : Real.sqrt (c_γ_kap * c' ^ (2 / 3 : ℝ) * u_n ^ (1 / 2 : ℝ)) =
          Real.sqrt c_γ_kap * c' ^ (1 / 3 : ℝ) * u_n ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hc_γ_kap_pos.le,
          Real.sqrt_eq_rpow (c' ^ (2 / 3 : ℝ)), Real.sqrt_eq_rpow (u_n ^ (1 / 2 : ℝ)),
          ← Real.rpow_mul hc'_pos.le, ← Real.rpow_mul hu_pos.le]
        norm_num
      rwa [hlhs] at hrt
    have hinv_sqrt : (Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ) ≤
        (Real.pi / (2 * Real.sqrt c_γ_kap)) * c' ^ (-(1 / 3 : ℝ)) * u_n ^ (-(1 / 4 : ℝ)) := by
      have h1 : (Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ) ≤
          (Real.pi / 2) / (Real.sqrt c_γ_kap * c' ^ (1 / 3 : ℝ) * u_n ^ (1 / 4 : ℝ)) := by
        gcongr
      refine h1.trans_eq ?_
      rw [Real.rpow_neg hc'_pos.le, Real.rpow_neg hu_pos.le]
      field_simp [hc_γ_kap_pos.ne']
    have hure_sin : (u_re ^ (3 / 2 : ℝ) / Real.sin φ) * u_n ^ (3 / 4 : ℝ) ≤ u_n ^ (3 / 2 : ℝ) := by
      have hsplit : u_re ^ (3 / 2 : ℝ) = u_re * u_re ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hu_re_pos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
        norm_num
      have hdiv_sin : u_re / Real.sin φ = u_n ^ (1 / 2 : ℝ) := by
        rw [show u_re = a' * Real.sin φ from hu_re_eq, mul_div_cancel_right₀ _ hsin_pos.ne']
        exact Real.sqrt_eq_rpow u_n
      have hure_14 : u_re ^ (1 / 2 : ℝ) ≤ u_n ^ (1 / 4 : ℝ) := by
        calc u_re ^ (1 / 2 : ℝ) ≤ (u_n ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow hu_re_pos.le hu_re_ub (by norm_num)
          _ = u_n ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hu_pos.le]; norm_num
      calc (u_re ^ (3 / 2 : ℝ) / Real.sin φ) * u_n ^ (3 / 4 : ℝ)
          = (u_re / Real.sin φ) * u_re ^ (1 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) := by
            rw [hsplit]; ring
        _ = u_n ^ (1 / 2 : ℝ) * u_re ^ (1 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) := by rw [hdiv_sin]
        _ ≤ u_n ^ (1 / 2 : ℝ) * u_n ^ (1 / 4 : ℝ) * u_n ^ (3 / 4 : ℝ) := by gcongr
        _ = u_n ^ (3 / 2 : ℝ) := by
            rw [← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]; norm_num
    have hun_54 : c' ^ (-(5 / 6 : ℝ)) * (u_n ^ (-(1 / 4 : ℝ)) * u_n ^ (3 / 2 : ℝ)) ≤
        b_hi ^ (5 / 2 : ℝ) := by
      have hsum : u_n ^ (-(1 / 4 : ℝ)) * u_n ^ (3 / 2 : ℝ) = u_n ^ (5 / 4 : ℝ) := by
        rw [← Real.rpow_add hu_pos]; norm_num
      have hub : u_n ^ (5 / 4 : ℝ) ≤ b_hi ^ (5 / 2 : ℝ) * c' ^ (5 / 6 : ℝ) := by
        calc u_n ^ (5 / 4 : ℝ) ≤ (b_hi ^ 2 * c' ^ (2 / 3 : ℝ)) ^ (5 / 4 : ℝ) :=
              Real.rpow_le_rpow hu_pos.le hu_bhi (by norm_num)
          _ = b_hi ^ (5 / 2 : ℝ) * c' ^ (5 / 6 : ℝ) := by
              rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg hc'_pos.le _),
                ← Real.rpow_natCast b_hi 2, ← Real.rpow_mul hb_hi_pos.le,
                ← Real.rpow_mul hc'_pos.le]
              norm_num
      rw [hsum]
      calc c' ^ (-(5 / 6 : ℝ)) * u_n ^ (5 / 4 : ℝ)
          ≤ c' ^ (-(5 / 6 : ℝ)) * (b_hi ^ (5 / 2 : ℝ) * c' ^ (5 / 6 : ℝ)) := by gcongr
        _ = b_hi ^ (5 / 2 : ℝ) * (c' ^ (-(5 / 6 : ℝ)) * c' ^ (5 / 6 : ℝ)) := by ring
        _ = b_hi ^ (5 / 2 : ℝ) := by
            rw [← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, mul_one]
    have hc13_cancel : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero]
    calc (12 * C_pref * c' ^ (1 / 3 : ℝ) *
            ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
              ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)))) *
          (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
        ≤ (12 * C_pref * c' ^ (1 / 3 : ℝ) *
            ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
              ((Real.pi / (2 * Real.sqrt c_γ_kap)) * c' ^ (-(1 / 3 : ℝ)) * u_n ^ (-(1 / 4 : ℝ))))) *
          (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) := by
          gcongr
      _ = (12 * C_pref * Real.pi / Real.sqrt c_γ_kap) * Λ *
            (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ))) *
            (c' ^ (-(5 / 6 : ℝ)) * (u_n ^ (-(1 / 4 : ℝ)) *
              ((u_re ^ (3 / 2 : ℝ) / Real.sin φ) * u_n ^ (3 / 4 : ℝ)))) := by ring
      _ ≤ (12 * C_pref * Real.pi / Real.sqrt c_γ_kap) * Λ * 1 *
            (c' ^ (-(5 / 6 : ℝ)) * (u_n ^ (-(1 / 4 : ℝ)) * u_n ^ (3 / 2 : ℝ))) := by
          rw [hc13_cancel]; gcongr
      _ ≤ (12 * C_pref * Real.pi / Real.sqrt c_γ_kap) * Λ * 1 * b_hi ^ (5 / 2 : ℝ) := by
          gcongr
      _ = C_win_tot * Λ := by dsimp [C_win_tot]; ring
  have htail_prod_le :
      ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
          Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) *
        (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤ C_tail_tot * Λ := by
    have hfac_ub : u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) ≤ b_hi ^ 3 * c' := by
      have h1 : u_re ^ (3 / 2 : ℝ) ≤ u_n ^ (3 / 4 : ℝ) := by
        calc u_re ^ (3 / 2 : ℝ) ≤ (u_n ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow hu_re_pos.le hu_re_ub (by norm_num)
          _ = u_n ^ (3 / 4 : ℝ) := by rw [← Real.rpow_mul hu_pos.le]; norm_num
      have h2 : u_n ^ (3 / 2 : ℝ) ≤ b_hi ^ 3 * c' := by
        calc u_n ^ (3 / 2 : ℝ) ≤ (b_hi ^ 2 * c' ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow hu_pos.le hu_bhi (by norm_num)
          _ = b_hi ^ 3 * c' := by
              rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg hc'_pos.le _),
                ← Real.rpow_natCast b_hi 2, ← Real.rpow_mul hb_hi_pos.le,
                ← Real.rpow_mul hc'_pos.le]
              norm_num
      calc u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)
          ≤ u_n ^ (3 / 4 : ℝ) * u_n ^ (3 / 4 : ℝ) := by gcongr
        _ = u_n ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hu_pos]; norm_num
        _ ≤ b_hi ^ 3 * c' := h2
    have hc43 : c' ^ (1 / 3 : ℝ) * c' = c' ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_add_one hc'_pos.ne']; norm_num
    have hexp_dom := rpow_four_thirds_mul_exp_neg_leW hκ_all_pos hc'_ge1
    have hC_pos : 0 < W.C_D + 12 * C_pref * max W.C_S4 W.C_S2 := by
      have := W.hC_D; have := W.hCS4; positivity
    calc ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
            Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) *
          (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
        ≤ ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
            Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) * (b_hi ^ 3 * c') :=
          mul_le_mul_of_nonneg_left hfac_ub
            (mul_nonneg (mul_nonneg hC_pos.le (Real.rpow_nonneg hc'_pos.le _)) (Real.exp_pos _).le)
      _ = (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 *
            ((c' ^ (1 / 3 : ℝ) * c') * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) := by ring
      _ ≤ (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 * (4 / κ_all ^ 2) := by
          rw [hc43]; gcongr
      _ = C_tail_tot * 1 := by dsimp [C_tail_tot]; ring
      _ ≤ C_tail_tot * Λ := by dsimp [C_tail_tot]; gcongr
  have hPsi_tri : ‖psiTilde prob c' g u‖ ≤
      ‖truncatedMellinPW prob c' dpT0 g u‖ + ‖truncatedMellinPW prob c' dpT0 g u - psiTilde prob c' g u‖ := by
    calc ‖psiTilde prob c' g u‖
        = ‖truncatedMellinPW prob c' dpT0 g u - (truncatedMellinPW prob c' dpT0 g u - psiTilde prob c' g u)‖ := by
          ring_nf
      _ ≤ _ := norm_sub_le _ _
  have hPsi_prod_le :
      ‖psiTilde prob c' g u‖ * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤
        (C_B * Λ) * airyEnv u := by
    have hsum_bd : ‖psiTilde prob c' g u‖ ≤
        (12 * C_pref * c' ^ (1 / 3 : ℝ) *
            ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
              ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ))) +
          (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
            Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) * airyEnv u := by
      have hp1 := hP_norm
      have hp2 := hDp_u.trans hDp_c13
      have hcomb : 12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u +
            W.C_D * c' ^ (1 / 3 : ℝ) * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u =
          (12 * C_pref * c' ^ (1 / 3 : ℝ) *
              ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
                ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ))) +
            (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
              Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) * airyEnv u := by
        rw [hB_seg_eq]; ring
      linarith only [hPsi_tri, hp1, hp2, hcomb]
    have hair_pos := airyEnv_pos u
    calc ‖psiTilde prob c' g u‖ * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
        ≤ ((12 * C_pref * c' ^ (1 / 3 : ℝ) *
              ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
                ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ))) *
            (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) +
            ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
              Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) *
            (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)))) * airyEnv u := by
          have hm := mul_le_mul_of_nonneg_right hsum_bd hfac_pos.le
          linarith only [hm]
      _ ≤ (C_win_tot * Λ + C_tail_tot * Λ) * airyEnv u := by gcongr
      _ = (C_win_tot + C_tail_tot) * Λ * airyEnv u := by ring
      _ ≤ (C_B * Λ) * airyEnv u := by gcongr
  have hinv_cancel : (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) *
      (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ))) = 1 := by
    calc (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) *
          (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)))
        = (u_re ^ (3 / 2 : ℝ) * u_re ^ (-(3 / 2 : ℝ))) *
            (u_n ^ (3 / 4 : ℝ) * u_n ^ (-(3 / 4 : ℝ))) := by ring
      _ = 1 := by
          rw [← Real.rpow_add hu_re_pos, ← Real.rpow_add hu_pos,
            add_neg_cancel, add_neg_cancel, Real.rpow_zero, Real.rpow_zero, mul_one]
  have hinv_nn : 0 ≤ u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)) := by positivity
  calc ‖psiTilde prob c' g u‖
      = ‖psiTilde prob c' g u‖ *
          ((u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) *
            (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)))) := by
        rw [hinv_cancel, mul_one]
    _ = (‖psiTilde prob c' g u‖ * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))) *
          (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ))) := by ring
    _ ≤ ((C_B * Λ) * airyEnv u) * (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_right hPsi_prod_le hinv_nn
    _ = C_B * Λ * airyEnv u * u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)) := by ring

/-! ### 4. Lemma Z (`lower_o1_two_edge.tex`, `vlo:Z`) -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_Z_combine_envelope_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Z_combine_envelope_W

end FormalResearch.ModularBootstrap.FixedWeightBand
