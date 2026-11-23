module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWZCombine
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuadratureBounds

/-!
# Lemma Z at weight `w` (`vlo:Z`)

`lemma_Z_W`: at every fixed-weight problem `prob` (with its `UniformPropositionPData`), an interior bound on
`tildeWW prob.w c' g` on the saddle sector implies `YVEnvBound (psiTilde prob c' g) c' R (C_B * Λ)`.
The proof deforms the truncated Mellin integral onto the saddle contour (`truncatedMellinPW_eq_contourIntegral`),
applies `lemma_Z_seg_bound_W` on each of the at most twelve segments, and combines with Lemma D' (`lemma_Dp_W`)
in `lemma_Z_combine_envelope_W`.
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

/-- **Lemma Z at weight `w` (interior multiplier bound implies the Airy envelope)**
(`lower_o1_two_edge.tex`, §J8, `vlo:Z`): for every `D : UniformPropositionPData prob`
and compact scale band `0 < b_lo ≤ b_hi` with `b_hi ^ 2 ≤ zScaleCapW D`, there exist
`c_Z ≥ dpThr prob` and `C_B ≥ 1` such that for all `c' ≥ c_Z`, `R` in `[b_lo^2 c'^{2/3}, b_hi^2 c'^{2/3} - 1]`,
`g ∈ TestClass prob (c' / 12)` with `0 < M[g]`, and `Λ ≥ 1`:
if on the strip sector `S = {ζ ∈ stripClosed | ρ_R / 3 ≤ ‖ζ‖ ≤ 2 ρ_R, c'^{-1/12} ‖ζ‖ ≤ ζ.re}`
(with `ρ_R = kappaV * c'^{-1/3} * √R`) the strip multiplier satisfies
`‖tildeWW prob.w c' g ζ‖ ≤ M[g] * (Λ * c'^{-5/6} * ‖ζ‖ / ζ.re)`,
then `YVEnvBound (psiTilde prob c' g) c' R (C_B * Λ)` holds. The Virasoro Lemma Z is the `w = 1` case. -/
theorem lemma_Z_W {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {b_lo b_hi : ℝ} (hb_lo : 0 < b_lo) (hb_le : b_lo ≤ b_hi)
    (hb_cap : b_hi ^ 2 ≤ zScaleCapW D) :
    ∃ c_Z C_B : ℝ, dpThr prob ≤ c_Z ∧ 1 ≤ C_B ∧
      ∀ {c' R Λ : ℝ}, c_Z ≤ c' → 1 ≤ Λ →
        b_lo ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R →
        R + 1 ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) →
        ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          0 < prob.cardyNorm (c' / 12) g →
          (∀ ζ ∈ stripClosed,
            kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
            ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
            c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re →
            ‖tildeWW prob.w c' g ζ‖ ≤
              prob.cardyNorm (c' / 12) g *
                (Λ * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re)) →
          YVEnvBound (psiTilde prob c' g) c' R (C_B * Λ) := by
  obtain ⟨W, hW_eq⟩ : ∃ x : ZWitnessW D, x = zWitnessW D := ⟨_, rfl⟩
  have hb_cap' : b_hi ^ 2 ≤ W.c₀_Z := by rw [hW_eq]; exact hb_cap
  have hb_hi_pos : 0 < b_hi := lt_of_lt_of_le hb_lo hb_le
  set ρ_min_Z : ℝ := (18 / 25 : ℝ) * kappaV * b_lo
  have hρ_min_pos : 0 < ρ_min_Z := mul_pos (mul_pos (by norm_num) kappaV_pos) hb_lo
  set κ_ray : ℝ := (dpConfig.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3
  have hκ_ray_pos : 0 < κ_ray :=
    mul_pos (mul_pos (div_pos dpConfig.hc_γ_pos (by norm_num)) (by norm_num)) (pow_pos hρ_min_pos 3)
  set κ_arc_Z : ℝ := dpConfig.κ_arc * ρ_min_Z ^ 3
  have hκ_arc_pos : 0 < κ_arc_Z := mul_pos dpConfig.hκ_arc_pos (pow_pos hρ_min_pos 3)
  set κ_all : ℝ := min (min κ_ray κ_arc_Z) (min dpConfig.κ_strip W.d_D)
  have hκ_all_pos : 0 < κ_all :=
    lt_min (lt_min hκ_ray_pos hκ_arc_pos) (lt_min dpConfig.hκ_strip_pos W.hd_D)
  set P_Γ : ℝ := (3 * dpConfig.C_Γ / (2 * Real.pi * (xiStar / 2) ^ 2)) ^ (((prob.w : ℝ) - 1) / 2)
  have hPΓ_pos : 0 < P_Γ := by
    have := Real.pi_pos
    have := xiStar_pos
    have := lt_of_lt_of_le dpConfig.hc_Γ_pos dpConfig.hc_Γ_le
    exact Real.rpow_pos_of_pos (by positivity) _
  set C_pref : ℝ := (innerCDxi * W.C_V / (2 * Real.pi)) * (4 * Real.sqrt 3 / xiStar) * P_Γ *
    dpConfig.C_d
  have hC_pref_pos : 0 < C_pref :=
    mul_pos (mul_pos (mul_pos (div_pos (mul_pos innerCDxi_pos W.hC_V)
      (mul_pos two_pos Real.pi_pos))
      (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) xiStar_pos)) hPΓ_pos)
      dpConfig.hC_d_pos
  set c_γ_kap : ℝ := (9 / 10 : ℝ) * dpConfig.c_γ * kappaV
  set C_win_tot : ℝ := 12 * C_pref * Real.pi / Real.sqrt c_γ_kap * b_hi ^ (5 / 2 : ℝ)
  set C_tail_tot : ℝ := (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 * (4 / κ_all ^ 2)
  obtain ⟨c_Z, hc_Z_eq⟩ : ∃ x : ℝ, x = max (max W.c_D (max W.c_S4 W.c_S2))
      (max W.c_V (max (dpThr prob) (max (stirThr prob.w / dpConfig.c_Γ)
        ((9 / b_lo ^ 2) ^ (3 / 2 : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨C_B, hC_B_eq⟩ : ∃ x : ℝ, x = max 1 (C_win_tot + C_tail_tot) := ⟨_, rfl⟩
  refine ⟨c_Z, C_B, ?_, hC_B_eq ▸ le_max_left _ _, ?_⟩
  · rw [hc_Z_eq]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  intro c' R Λ hc' hΛ hR_lo hR_hi g hg hM_pos hsec u hu_im hu_lo hu_hi hsin_hyp
  have hc'_D : W.c_D ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans (le_max_left _ _)).trans hc'
  have hc'_S4 : W.c_S4 ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc'
  have hc'_S2 : W.c_S2 ≤ c' :=
    (hc_Z_eq ▸ (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc'
  have hc'_V : W.c_V ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_thr : dpThr prob ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_10000 : 10000 ≤ c' := (dpThr_ge_10000 prob).trans hc'_thr
  have hc'_stir : stirThr prob.w / dpConfig.c_Γ ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc'
  have hc'_R9 : (9 / b_lo ^ 2) ^ (3 / 2 : ℝ) ≤ c' :=
    (hc_Z_eq ▸ (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc'
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hc'_ge1 : 1 ≤ c' := by linarith only [hc'_10000]
  have hc'_24 : max 1 (24 * prob.totalShift) ≤ c' := max_one_le_of_dpThr_le prob hc'_thr
  -- Step 1: R ≥ 9 and comparability between ‖u‖, R, and c'^{2/3}
  have hR_ge9 : 9 ≤ R := by
    have h1 : 9 / b_lo ^ 2 ≤ c' ^ (2 / 3 : ℝ) := by
      calc 9 / b_lo ^ 2 = ((9 / b_lo ^ 2) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hc'_R9 (by norm_num)
    have h2 : 9 ≤ b_lo ^ 2 * c' ^ (2 / 3 : ℝ) := (div_le_iff₀' (sq_pos_of_pos hb_lo)).mp h1
    exact h2.trans hR_lo
  have hR_pos : 0 < R := by linarith only [hR_ge9]
  have hu_ge8 : 8 ≤ ‖u‖ := by linarith only [hR_ge9, hu_lo]
  have hu_pos : 0 < ‖u‖ := by linarith only [hu_ge8]
  have hu_ne : u ≠ 0 := norm_pos_iff.mp hu_pos
  have hu_bhi : ‖u‖ ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) := hu_hi.trans hR_hi
  have hu_Z : ‖u‖ ≤ W.c₀_Z * c' ^ (2 / 3 : ℝ) :=
    hu_bhi.trans (mul_le_mul_of_nonneg_right hb_cap' (Real.rpow_nonneg hc'_pos.le _))
  have hu_cb_D : u ∈ closedBall (0 : ℂ) (W.c₀_D * c' ^ (2 / 3 : ℝ)) :=
    mem_closedBall_zero_iff.mpr
      (hu_Z.trans (mul_le_mul_of_nonneg_right W.hc₀_Z_le_D (Real.rpow_nonneg hc'_pos.le _)))
  have hu_cb_in : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    have hin_pos := innerChartRadius_pos
    have hle_in : W.c₀_D ≤ innerChartRadius := W.hc₀_D_le4.trans (by linarith only [hin_pos])
    exact closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right hle_in (Real.rpow_nonneg hc'_pos.le _)) hu_cb_D
  have hsqrt_u_lo : (4 / 5 : ℝ) * Real.sqrt R ≤ Real.sqrt ‖u‖ := by
    have h89 : (8 / 9 : ℝ) * R ≤ ‖u‖ := by linarith only [hR_ge9, hu_lo]
    have hsq : ((4 / 5 : ℝ) * Real.sqrt R) ^ 2 ≤ ‖u‖ := by
      rw [mul_pow, Real.sq_sqrt hR_pos.le]
      linarith only [h89, hR_pos]
    exact Real.le_sqrt_of_sq_le hsq
  have hsqrt_u_hi : Real.sqrt ‖u‖ ≤ (6 / 5 : ℝ) * Real.sqrt R := by
    have h109 : ‖u‖ ≤ (10 / 9 : ℝ) * R := by linarith only [hR_ge9, hu_hi]
    have hsq : ‖u‖ ≤ ((6 / 5 : ℝ) * Real.sqrt R) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hR_pos.le]
      linarith only [h109, hR_pos]
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))
  -- Step 2: Polar angle φ = (π - u.arg) / 2 and sin φ ≥ 2 c'^{-1/12}
  set a' : ℝ := Real.sqrt ‖u‖
  have ha'_pos : 0 < a' := Real.sqrt_pos.mpr hu_pos
  have ha'_sq : a' ^ 2 = ‖u‖ := Real.sq_sqrt hu_pos.le
  set φ : ℝ := (Real.pi - u.arg) / 2
  have hu_re_eq : (u ^ (1 / 2 : ℂ)).re = a' * Real.sin φ := cpow_half_re_eq_sqrt_mul_sinW hu_ne
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := by
    have h1 : 0 < 2 * c' ^ (-(1 / 12 : ℝ)) * a' := by positivity
    linarith only [h1, hsin_hyp]
  have hsin_lb : 2 * c' ^ (-(1 / 12 : ℝ)) ≤ Real.sin φ := by
    have h1 : a' * (2 * c' ^ (-(1 / 12 : ℝ))) ≤ a' * Real.sin φ := by
      linarith only [hsin_hyp, hu_re_eq]
    exact le_of_mul_le_mul_left h1 ha'_pos
  have hsin_pos : 0 < Real.sin φ := lt_of_lt_of_le (by positivity) hsin_lb
  have hsin_le1 : Real.sin φ ≤ 1 := Real.sin_le_one φ
  have hu_arg_nn : 0 ≤ u.arg := Complex.arg_nonneg_iff.mpr hu_im
  have hu_arg_lt : u.arg < Real.pi := by
    rcases lt_or_ge u.arg Real.pi with hlt | hge
    · exact hlt
    · exfalso
      have hpi : u.arg = Real.pi := le_antisymm (Complex.arg_le_pi u) hge
      have hφ0 : φ = 0 := by dsimp [φ]; rw [hpi, sub_self, zero_div]
      rw [hφ0, Real.sin_zero] at hsin_pos
      exact lt_irrefl 0 hsin_pos
  have hu_cut : ¬ (u.im = 0 ∧ u.re ≤ 0) := by
    rintro ⟨him0, hre_np⟩
    rcases eq_or_lt_of_le hre_np with hre0 | hre_neg
    · exact hu_ne (Complex.ext hre0 him0)
    · exact hu_arg_lt.ne (Complex.arg_eq_pi_iff.mpr ⟨hre_neg, him0⟩)
  have hφ_pos : 0 < φ := by dsimp [φ]; linarith only [hu_arg_lt]
  have hφ_le : φ ≤ Real.pi / 2 := by dsimp [φ]; linarith only [hu_arg_nn]
  have hu_polar : u = ((a' ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * φ : ℝ) : ℂ)) := by
    have hp := (Complex.norm_mul_exp_arg_mul_I u).symm
    rw [← ha'_sq] at hp
    conv_lhs => rw [hp]
    congr 1; congr 1
    dsimp [φ]; push_cast; ring
  -- Step 3: Saddle point s = ζp from W.h_saddle and exact potential airyEnv u
  have ha'_Z : a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) ≤ W.c₀_Z := by
    rw [ha'_sq]
    calc ‖u‖ * c' ^ (-(2 / 3 : ℝ))
        ≤ (W.c₀_Z * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by gcongr
      _ = W.c₀_Z := by
          rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
  have hsad := W.h_saddle hc'_pos ha'_pos.le hφ_pos.le hφ_le ha'_Z
  dsimp only at hsad
  rw [← hu_polar] at hsad
  set z_u : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
  set s : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * W.q_V z_u
  set ρ : ℝ := ‖s‖
  obtain ⟨hb_eq_chartB, _hs_re_nn, hs_im_nn, hρ_ρ₀, hρ_rφ, _, hρ_lo, hρ_hi, hs_re_lb⟩ := hsad
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le (by have := kappaV_pos; positivity) hρ_lo
  have hs_re_pos : 0 < s.re := lt_of_lt_of_le (by positivity) hs_re_lb
  set ρ_R : ℝ := kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R
  have hρ_lo_R : (18 / 25 : ℝ) * ρ_R ≤ ρ := by
    have h1 : (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((4 / 5 : ℝ) * Real.sqrt R)) ≤
        (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') := by
      gcongr; have := kappaV_pos; positivity
    calc (18 / 25 : ℝ) * ρ_R
        = (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((4 / 5 : ℝ) * Real.sqrt R)) := by
          dsimp [ρ_R]; ring
      _ ≤ ρ := h1.trans hρ_lo
  have hρ_hi_R : ρ ≤ (33 / 25 : ℝ) * ρ_R := by
    have h1 : (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') ≤
        (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((6 / 5 : ℝ) * Real.sqrt R)) := by
      gcongr; have := kappaV_pos; positivity
    calc ρ ≤ (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((6 / 5 : ℝ) * Real.sqrt R)) :=
          hρ_hi.trans h1
      _ = (33 / 25 : ℝ) * ρ_R := by dsimp [ρ_R]; ring
  have hρ_ge_min : ρ_min_Z ≤ ρ := by
    have hsqrt_R_lb : b_lo * c' ^ (1 / 3 : ℝ) ≤ Real.sqrt R := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [mul_pow, ← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc'_pos.le]
      calc b_lo ^ 2 * c' ^ ((1 / 3 : ℝ) * (2 : ℕ)) = b_lo ^ 2 * c' ^ (2 / 3 : ℝ) := by
            push_cast; rw [show (1 / 3 : ℝ) * 2 = (2 / 3 : ℝ) by norm_num]
        _ ≤ R := hR_lo
    have hρR_lb : kappaV * b_lo ≤ ρ_R := by
      dsimp [ρ_R]
      calc kappaV * b_lo
          = kappaV * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ)) * b_lo := by
            rw [← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, mul_one]
        _ = kappaV * c' ^ (-(1 / 3 : ℝ)) * (b_lo * c' ^ (1 / 3 : ℝ)) := by ring
        _ ≤ kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R := by
            gcongr; have := kappaV_pos; positivity
    calc ρ_min_Z = (18 / 25 : ℝ) * (kappaV * b_lo) := by dsimp [ρ_min_Z]; ring
      _ ≤ (18 / 25 : ℝ) * ρ_R := by gcongr
      _ ≤ ρ := hρ_lo_R
  have hs_re_c12 : (5 / 3 : ℝ) * ρ * c' ^ (-(1 / 12 : ℝ)) ≤ s.re := by
    have h1 : (5 / 6 : ℝ) * (ρ * (2 * c' ^ (-(1 / 12 : ℝ)))) ≤ (5 / 6 : ℝ) * (ρ * Real.sin φ) := by
      gcongr
    calc (5 / 3 : ℝ) * ρ * c' ^ (-(1 / 12 : ℝ))
        = (5 / 6 : ℝ) * (ρ * (2 * c' ^ (-(1 / 12 : ℝ)))) := by ring
      _ ≤ s.re := h1.trans hs_re_lb
  have hc_ρ_sre_sq : (25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ) ≤ c' * ρ * s.re ^ 2 := by
    have hsq : ((5 / 3 : ℝ) * ρ * c' ^ (-(1 / 12 : ℝ))) ^ 2 ≤ s.re ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs_re_c12 2
    have hpow_c : c' * (c' ^ (-(1 / 12 : ℝ))) ^ 2 = c' ^ (5 / 6 : ℝ) := by
      rw [← Real.rpow_natCast (c' ^ (-(1 / 12 : ℝ))) 2, ← Real.rpow_mul hc'_pos.le,
        ← Real.rpow_one_add' hc'_pos.le (by norm_num : (1 : ℝ) + -(1 / 12 : ℝ) * (2 : ℕ) ≠ 0)]
      push_cast; norm_num
    have hρ_cube : ρ_min_Z ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ hρ_min_pos.le hρ_ge_min 3
    calc (25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ)
        ≤ (25 / 9 : ℝ) * ρ ^ 3 * c' ^ (5 / 6 : ℝ) := by gcongr
      _ = c' * ρ * (((5 / 3 : ℝ) * ρ * c' ^ (-(1 / 12 : ℝ))) ^ 2) := by
          rw [mul_pow, mul_pow, ← hpow_c]; ring
      _ ≤ c' * ρ * s.re ^ 2 := by gcongr
  set φ' : ℝ := Real.pi / 2 - s.arg
  have hs_arg_nn : 0 ≤ s.arg := Complex.arg_nonneg_iff.mpr hs_im_nn
  have hs_arg_le : s.arg ≤ Real.pi / 2 := by
    rcases eq_or_lt_of_le hs_im_nn with him0 | him_pos
    · rw [Complex.arg_eq_zero_iff.mpr ⟨hs_re_pos.le, him0.symm⟩]; positivity [Real.pi_pos]
    · exact (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hs_re_pos)).le
  have hφ'_nn : 0 ≤ φ' := by dsimp [φ']; linarith only [hs_arg_le]
  have hφ'_le : φ' ≤ Real.pi / 2 := by dsimp [φ']; linarith only [hs_arg_nn]
  have hs_polar : s = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)) := by
    have hp := (Complex.norm_mul_exp_arg_mul_I s).symm
    have harg_eq : Real.pi / 2 - φ' = s.arg := by dsimp [φ']; ring
    rw [harg_eq]
    simpa [ρ, mul_comm (s.arg : ℂ) Complex.I] using hp
  -- Step 4: Deformation onto the `dpConfig_spec` saddle contour
  obtain ⟨_, _, _, segs, hchain, _, hω_bd, hstrip_gen, h_ur, h_lr, h_ar, h_fs, hnonstrip,
      hcnt_segs, hba_segs, h_no_crude⟩ :=
    dpConfig_spec hρ_pos.le hρ_ρ₀ hφ'_nn hφ'_le
  rw [← hs_polar, hb_eq_chartB] at hstrip_gen h_ur h_lr h_ar h_fs hnonstrip
  have hP_deform := truncatedMellinPW_eq_contourIntegral prob hc'_thr hg hu_cb_in hchain hω_bd
  set b : ℂ := virasoroBChart c' u
  set t : ℂ := virasoroDeltaChartC c' u
  have hair_eq : Real.exp (c' * (chartPhiV s b).re) = airyEnv u := by
    have hs_ball : s ∈ ball (0 : ℂ) W.r_φ := by rwa [mem_ball_zero_iff]
    have hpot1 := W.hφ_pot s hs_ball hs_re_pos
    rw [hb_eq_chartB] at hpot1
    have hpot2 := virasoro_inner_potential_eq hc'_pos hu_cb_in hu_cut
    have hc_phi : c' * (chartPhiV s b).re = -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
      rw [hpot1]; simpa [add_comm] using hpot2
    rw [hc_phi]; rfl
  -- Step 5: Prefactor & window sector hypotheses for `lemma_Z_seg_bound`
  set M_g : ℝ := prob.cardyNorm (c' / 12) g
  have hbd_in := virasoroBChart_inner_bounds hc'_pos hu_cb_in
  have hb_arg : |b.arg| < Real.pi / 4 := (inner_chart_arg_lt hc'_pos hu_cb_in).2.2
  have hu_cb_AC : u ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) := by
    rw [chartAC_sq D.r_1 c' hc'_pos.le]
    refine closedBall_subset_closedBall ?_ hu_cb_D
    calc W.c₀_D * c' ^ (2 / 3 : ℝ) ≤ chartBV D.r_1 ^ 2 * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right W.hc₀_D_leV (Real.rpow_nonneg hc'_pos.le _)
      _ ≤ (2 * chartBV D.r_1 ^ 2) * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg (chartBV D.r_1)])
            (Real.rpow_nonneg hc'_pos.le _)
  have hb_re_pos : 0 < b.re := lt_of_lt_of_le (half_pos xiStar_pos) hbd_in.2.2.1
  have ht_eq : t = (c' : ℂ) * b ^ 2 / 3 := virasoroDeltaChartC_eq_bChart_sq u
  have ht_half_ub : ‖t ^ (-(1 / 2 : ℂ))‖ ≤ (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)) := by
    have ht_lb : c' * (xiStar / 2) ^ 2 / 3 ≤ ‖t‖ := by
      rw [ht_eq, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc'_pos.le,
        Complex.norm_ofNat]
      have h1 : xiStar / 2 ≤ ‖b‖ := hbd_in.2.2.1.trans (Complex.re_le_norm _)
      have h2 : (xiStar / 2) ^ 2 ≤ ‖b‖ ^ 2 :=
        pow_le_pow_left₀ (by have := xiStar_pos; positivity) h1 2
      gcongr
    have ht_pos : 0 < ‖t‖ := lt_of_lt_of_le (by have := xiStar_pos; positivity) ht_lb
    have ht_ne : t ≠ 0 := norm_pos_iff.mp ht_pos
    have hnorm_cp : ‖t ^ (-(1 / 2 : ℂ))‖ = ‖t‖ ^ (-(1 / 2 : ℝ)) := by
      rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp]
      have hre : (Complex.log t * (-(1 / 2 : ℂ))).re = -(1 / 2 : ℝ) * Real.log ‖t‖ := by
        rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
          mul_comm, Complex.re_ofReal_mul, Complex.log_re]
      rw [hre, Real.rpow_def_of_pos ht_pos]
      congr 1; ring
    rw [hnorm_cp]
    have hpow_le : ‖t‖ ^ (-(1 / 2 : ℝ)) ≤ (c' * (xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by have := xiStar_pos; positivity) ht_lb (by norm_num)
    have hrhs_eq : (c' * (xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) =
        (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)) := by
      have hxi := xiStar_pos
      have hsub : ((xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt 3 / xiStar := by
        rw [Real.rpow_neg (by positivity),
          Real.div_rpow (by positivity) (by norm_num),
          ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (by positivity)]
        field_simp [hxi.ne']
      rw [show c' * (xiStar / 2) ^ 2 / 3 = ((xiStar / 2) ^ 2 / 3) * c' by ring,
        Real.mul_rpow (by positivity) hc'_pos.le, hsub]
    exact hpow_le.trans_eq hrhs_eq
  have hwin_wv : ∀ ζ ∈ stripClosed, ‖ζ - s‖ ≤ s.re / 4 →
      ‖tildeWW prob.w c' g ζ‖ ≤ M_g * (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) := by
    intro ζ hζ_cl hdist
    have hdist_ρ : ‖ζ - s‖ ≤ ρ / 4 := by
      have hs_re_le : s.re ≤ ρ := Complex.re_le_norm s
      linarith only [hdist, hs_re_le]
    have hζ_lo : ρ_R / 3 ≤ ‖ζ‖ := by
      have htri := norm_sub_norm_le s (s - ζ)
      rw [sub_sub_cancel, norm_sub_rev] at htri
      have htri' : ρ - ‖ζ - s‖ ≤ ‖ζ‖ := htri
      have h34 : (3 / 4 : ℝ) * ρ ≤ ‖ζ‖ := by linarith only [htri', hdist_ρ]
      have hR_nn : 0 ≤ ρ_R := by dsimp [ρ_R]; have := kappaV_pos; positivity
      calc ρ_R / 3 ≤ (27 / 50 : ℝ) * ρ_R := by linarith only [hR_nn]
        _ = (3 / 4 : ℝ) * ((18 / 25 : ℝ) * ρ_R) := by ring
        _ ≤ (3 / 4 : ℝ) * ρ := by gcongr
        _ ≤ ‖ζ‖ := h34
    have hζ_hi : ‖ζ‖ ≤ 2 * ρ_R := by
      have htri : ‖ζ‖ ≤ ρ + ‖ζ - s‖ := by
        calc ‖ζ‖ = ‖s + (ζ - s)‖ := by ring_nf
          _ ≤ ‖s‖ + ‖ζ - s‖ := norm_add_le _ _
      have h54 : ‖ζ‖ ≤ (5 / 4 : ℝ) * ρ := by linarith only [htri, hdist_ρ]
      have hR_nn : 0 ≤ ρ_R := by dsimp [ρ_R]; have := kappaV_pos; positivity
      calc ‖ζ‖ ≤ (5 / 4 : ℝ) * ρ := h54
        _ ≤ (5 / 4 : ℝ) * ((33 / 25 : ℝ) * ρ_R) := by gcongr
        _ = (33 / 20 : ℝ) * ρ_R := by ring
        _ ≤ 2 * ρ_R := by linarith only [hR_nn]
    have hζ_re_lb : (3 / 4 : ℝ) * s.re ≤ ζ.re := by
      have hre_sub := (abs_le.mp ((Complex.abs_re_le_norm (ζ - s)).trans hdist)).1
      rw [Complex.sub_re] at hre_sub
      linarith only [hre_sub]
    have hζ_re_pos : 0 < ζ.re := lt_of_lt_of_le (by positivity) hζ_re_lb
    have hζ_ang : (1 / 2 : ℝ) * Real.sin φ * ‖ζ‖ ≤ ζ.re := by
      have h54 : ‖ζ‖ ≤ (5 / 4 : ℝ) * ρ := by
        have htri : ‖ζ‖ ≤ ρ + ‖ζ - s‖ := by
          calc ‖ζ‖ = ‖s + (ζ - s)‖ := by ring_nf
            _ ≤ ‖s‖ + ‖ζ - s‖ := norm_add_le _ _
        linarith only [htri, hdist_ρ]
      calc (1 / 2 : ℝ) * Real.sin φ * ‖ζ‖
          ≤ (1 / 2 : ℝ) * Real.sin φ * ((5 / 4 : ℝ) * ρ) := by gcongr
        _ = (3 / 4 : ℝ) * ((5 / 6 : ℝ) * (ρ * Real.sin φ)) := by ring
        _ ≤ (3 / 4 : ℝ) * s.re := by gcongr
        _ ≤ ζ.re := hζ_re_lb
    have hζ_c12 : c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re := by
      have hc_half : c' ^ (-(1 / 12 : ℝ)) ≤ (1 / 2 : ℝ) * Real.sin φ := by linarith only [hsin_lb]
      exact (mul_le_mul_of_nonneg_right hc_half (norm_nonneg ζ)).trans hζ_ang
    have h_wv := hsec ζ hζ_cl hζ_lo hζ_hi hζ_c12
    have h_rat : ‖ζ‖ / ζ.re ≤ 2 / Real.sin φ := by
      rw [div_le_div_iff₀ hζ_re_pos hsin_pos]
      linarith only [hζ_ang]
    calc ‖tildeWW prob.w c' g ζ‖
        ≤ M_g * (Λ * c' ^ (-(5 / 6 : ℝ)) * (‖ζ‖ / ζ.re)) := by
          simpa only [mul_div_assoc] using h_wv
      _ ≤ M_g * (Λ * c' ^ (-(5 / 6 : ℝ)) * (2 / Real.sin φ)) := by gcongr
      _ = M_g * (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) := by ring
  set K_seg : ℝ := (4 * Real.sqrt 3 / xiStar) * P_Γ * dpConfig.C_d * M_g *
    c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv u
  have hK_seg_pos : 0 < K_seg :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos
      (mul_pos (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) xiStar_pos) hPΓ_pos)
      dpConfig.hC_d_pos) hM_pos) (Real.rpow_pos_of_pos hc'_pos _)) (Real.exp_pos _))
      (airyEnv_pos u)
  set B_seg_unit : ℝ :=
    (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
      ((Real.pi / 2) / Real.sqrt (c' * dpConfig.c_γ * ρ)) +
    max W.C_S4 W.C_S2 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))
  have hB_seg_nn : 0 ≤ K_seg * B_seg_unit := by
    refine mul_nonneg hK_seg_pos.le (add_nonneg ?_ ?_)
    · exact mul_nonneg (div_nonneg (by positivity) hsin_pos.le)
        (div_nonneg (by positivity) (Real.sqrt_nonneg _))
    · exact mul_nonneg (lt_of_lt_of_le W.hCS4 (le_max_left _ _)).le (Real.exp_pos _).le
  have hseg_bound : ∀ S ∈ segs,
      ‖∫ τ in S.a..S.b, mellinDensityIntegrandW prob.w c' g t (S.ω τ) * S.ω' τ‖ ≤
        K_seg * B_seg_unit := fun S hS =>
    lemma_Z_seg_bound_W W dpConfig S hc'_pos hc'_ge1 hc'_24 hc'_stir hc'_S4
      (by linarith only [hΛ]) hsin_pos hρ_pos hs_re_pos hρ_min_pos hρ_ge_min hc_ρ_sre_sq
      hκ_all_pos ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_left _ _).trans (min_le_right _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
      hg hM_pos rfl hb_re_pos hb_arg hbd_in.2.2.2.2.2 hPΓ_pos
      (fun τ hτ => norm_stirlingPrefW_le prob.hw (by have := xiStar_pos; positivity)
        (hω_bd S hS τ hτ).2.2.1 (hbd_in.2.2.1.trans (Complex.re_le_norm _))) ht_eq ht_half_ub hair_eq rfl rfl
      hwin_wv (fun hμ => W.hS2 hc'_S2 hμ hg)
      (hba_segs S hS) (hω_bd S hS) (h_ur S hS) (h_lr S hS) (h_ar S hS) (h_fs S hS)
      (hnonstrip S hS) (h_no_crude S hS)
  -- Step 6: Sum over `segs` (`segs.length ≤ 12`) to bound `‖truncatedMellinP c' dpT0 g u‖`
  have hcont_tot : ‖contourIntegral (mellinDensityIntegrandW prob.w c' g t) segs‖ ≤
      12 * (K_seg * B_seg_unit) :=
    (norm_contourIntegral_le_of_seg_boundW _ segs hB_seg_nn hseg_bound).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt_segs) hB_seg_nn)
  have hP_norm : ‖truncatedMellinPW prob c' dpT0 g u‖ ≤
      12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u := by
    have hV_u := W.hV_bd hc'_V hu_cb_AC
    have hd_u := virasoroDeltaChartC_inner_deriv_bound hc'_pos hu_cb_in
    rw [hP_deform, norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_div]
    have hM_norm : ‖(M_g : ℂ)‖ = M_g := by
      rw [Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
    have hc_2pi : ‖(c' : ℂ)‖ / ‖2 * (Real.pi : ℂ) * Complex.I‖ = c' / (2 * Real.pi) := by
      rw [Complex.norm_real, Real.norm_of_nonneg hc'_pos.le, norm_mul, norm_mul,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_I, mul_one]
    change (‖deriv (virasoroDeltaChartC c') u‖ / ‖(M_g : ℂ)‖) *
        ‖cardyVC prob (c' / 12) t‖ * (‖(c' : ℂ)‖ / ‖2 * (Real.pi : ℂ) * Complex.I‖) *
        ‖contourIntegral (mellinDensityIntegrandW prob.w c' g t) segs‖ ≤ _
    rw [hM_norm, hc_2pi]
    have hexp_cancel : Real.exp (c' * (tipL b).re) * Real.exp (-(c' * (tipL b).re)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hc_pow_eq : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ)) =
        c' ^ (1 / 3 : ℝ) := by
      calc c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ))
          = c' ^ (1 / 3 : ℝ) * (c' * (c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)))) := by ring
        _ = c' ^ (1 / 3 : ℝ) * (c' * c' ^ (-1 : ℝ)) := by
            rw [← Real.rpow_add hc'_pos]; norm_num
        _ = c' ^ (1 / 3 : ℝ) * 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀ hc'_pos.ne']
        _ = c' ^ (1 / 3 : ℝ) := mul_one _
    calc (‖deriv (virasoroDeltaChartC c') u‖ / M_g) * ‖cardyVC prob (c' / 12) t‖ *
            (c' / (2 * Real.pi)) * ‖contourIntegral (mellinDensityIntegrandW prob.w c' g t) segs‖
        ≤ ((innerCDxi * c' ^ (1 / 3 : ℝ)) / M_g) *
            (W.C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (tipL b).re)) *
            (c' / (2 * Real.pi)) * (12 * (K_seg * B_seg_unit)) := by
          have := innerCDxi_pos; have := W.hC_V
          gcongr
      _ = 12 * C_pref * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ))) *
            (Real.exp (c' * (tipL b).re) * Real.exp (-(c' * (tipL b).re))) *
            B_seg_unit * airyEnv u := by
          dsimp [C_pref, K_seg]
          field_simp [hM_pos.ne', Real.pi_pos.ne']
      _ = 12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u := by
          rw [hc_pow_eq, hexp_cancel, mul_one]
  -- Step 7: Combine with `lemma_Dp` via `lemma_Z_combine_envelope`
  exact lemma_Z_combine_envelope_W W dpConfig hb_hi_pos hc'_pos hc'_ge1 hΛ
    hκ_all_pos ((min_le_right _ _).trans (min_le_right _ _)) hC_pref_pos
    hu_pos hu_bhi hu_re_pos hu_re_eq hsin_pos hsin_le1 hρ_pos hρ_lo rfl
    (hC_B_eq ▸ le_max_right _ _) hP_norm (W.hDp hc'_D hg hM_pos hu_cb_D)

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_Z_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Z_W

end FormalResearch.ModularBootstrap.FixedWeightBand
