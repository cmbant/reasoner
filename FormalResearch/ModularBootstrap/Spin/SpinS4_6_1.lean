module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_6_1_Helpers
public import FormalResearch.ModularBootstrap.Spin.SpinS1c

/-!
# Section 6.1 of `spinning_s4.tex` (`s4:6.1`): `SpinS4_6_1`

Proves `spinS4_6_1 : SpinS4_6_1`, giving universal constants `C_- > 0` and `c₁ ≥ 40` such
that for all `c ≥ c₁` (`n = c - 1`, `a = n / 12`, `T_- = ξ̄ n + A_opt n^{1/3} - C_- log n`):
1. `0 < T_-`;
2. `¬ SpinIsSlackFeasible a T Φ` whenever `T < T_-`;
3. `n / λ_V + A_opt n^{1/3} - C_- log n ≤ Δ_L(c)`.

Proof: given a slack-feasible `(T, Φ)` with `T < T_-`, rescale `Ψ := (M_2[Φ])⁻¹ • Φ` and apply
the two-edge bootstrap shrinkage bound `spinS4_6_1_shrink_bound` at
`u_T = a₁ + (C_loc + 1) n^{-1/3} log n` (`x₁ = b_n(u_T)`), yielding `C_loc + 1 ≤ C_loc`.
The lower bound on `Δ_L(c)` then follows from the lifted spinless feasibility set (`spinS1c`).
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.FixedWeight
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.Special

private lemma eventually_log_div_rpow_one_third_le (M : ℝ) (_hM : 0 < M) :
    ∀ᶠ n : ℝ in atTop, M * (Real.log n / n ^ ((1 : ℝ) / 3)) ≤ 1 := by
  have h0 : Tendsto (fun n : ℝ => Real.log n / n ^ ((1 : ℝ) / 3)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun n : ℝ => M * (Real.log n / n ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
    simpa [mul_zero] using h0.const_mul M
  exact h1.eventually (Iic_mem_nhds zero_lt_one)

private lemma eventually_rpow_neg_two_thirds_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℝ in atTop, n ^ (-(2 / 3 : ℝ)) < ε := by
  have h0 : Tendsto (fun n : ℝ => n ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)
  exact h0.eventually (Iio_mem_nhds hε)

/-- **Section 6.1 slack-feasible lower bound (`s4:6.1`)** of `spinning_s4.tex`. -/
theorem spinS4_6_1 : SpinS4_6_1 := by
  let C_err : ℝ := chartParams.C_xi
  have hCerr_nn : 0 ≤ C_err := chartParams.hCxi_nn
  let C₀ : ℝ := (3 / xiStar) * (4 * cStar + 16 * C_err) + 1
  have hC₀_pos : 0 < C₀ := by
    have h1 := xiStar_pos
    have h2 := cStar_pos
    positivity
  obtain ⟨C_loc, c_thr, hCloc_pos, hcthr_40, hshrink⟩ := spinS4_6_1_shrink_bound hC₀_pos
  let C_minus : ℝ := cStar * (C_loc + 1) + 16 * C_err + 1
  have hCm_pos : 0 < C_minus := by
    have h1 := cStar_pos
    positivity
  have hxiBar_pos : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((isLittleO_log_id_atTop.tendsto_div_nhds_zero).eventually
      (Iio_mem_nhds (div_pos hxiBar_pos hCm_pos)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (eventually_log_div_rpow_one_third_le (C_loc + 1) (by linarith))
  let δ_ac : ℝ := virasoroBV ^ 2 / 8
  have hδ_ac_pos : 0 < δ_ac := by dsimp [δ_ac]; have := virasoroBV_pos; positivity
  let δ_xb : ℝ := xiBar / (4 * cStar + 16 * C_err + 1)
  have hδ_xb_pos : 0 < δ_xb := by
    dsimp [δ_xb]; have := cStar_pos; positivity
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp (eventually_rpow_neg_two_thirds_lt δ_ac hδ_ac_pos)
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp (eventually_rpow_neg_two_thirds_lt δ_xb hδ_xb_pos)
  let c₁ : ℝ := max (max c_thr 40) (max (max N₁ N₂) (max N₃ N₄) + 1)
  have hc₁_40 : 40 ≤ c₁ := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨C_minus, c₁, hCm_pos, hc₁_40, fun {c} hc => ?_⟩
  have hc_thr : c_thr ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hc_40 : 40 ≤ c := hc₁_40.trans hc
  have hn_N1 : N₁ ≤ c - 1 := by
    have h1 : max (max N₁ N₂) (max N₃ N₄) + 1 ≤ c := (le_max_right _ _).trans hc
    have h2 : N₁ ≤ max (max N₁ N₂) (max N₃ N₄) := (le_max_left _ _).trans (le_max_left _ _)
    linarith
  have hn_N2 : N₂ ≤ c - 1 := by
    have h1 : max (max N₁ N₂) (max N₃ N₄) + 1 ≤ c := (le_max_right _ _).trans hc
    have h2 : N₂ ≤ max (max N₁ N₂) (max N₃ N₄) := (le_max_right _ _).trans (le_max_left _ _)
    linarith
  have hn_N3 : N₃ ≤ c - 1 := by
    have h1 : max (max N₁ N₂) (max N₃ N₄) + 1 ≤ c := (le_max_right _ _).trans hc
    have h2 : N₃ ≤ max (max N₁ N₂) (max N₃ N₄) := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have hn_N4 : N₄ ≤ c - 1 := by
    have h1 : max (max N₁ N₂) (max N₃ N₄) + 1 ≤ c := (le_max_right _ _).trans hc
    have h2 : N₄ ≤ max (max N₁ N₂) (max N₃ N₄) := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  set n : ℝ := c - 1
  set a : ℝ := n / 12
  set T_minus : ℝ := xiBar * n + Aopt * n ^ ((1 : ℝ) / 3) - C_minus * Real.log n
  have hn_ge39 : 39 ≤ n := by dsimp [n]; linarith
  have hn_pos : 0 < n := by linarith
  have hn_ge1 : 1 ≤ n := by linarith
  have ha_ge2 : 2 ≤ a := by dsimp [a, n]; linarith
  have hlog_ge1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn_pos]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hn_ge39
  have hlog_pos : 0 < Real.log n := lt_of_lt_of_le zero_lt_one hlog_ge1
  have hTm_pos : 0 < T_minus := by
    have hdiv : Real.log n / n < xiBar / C_minus := hN₁ n hn_N1
    have hmul : C_minus * Real.log n < xiBar * n := by
      have h1 := mul_lt_mul_of_pos_left hdiv hCm_pos
      have h2 := mul_lt_mul_of_pos_left h1 hn_pos
      have hCm_ne : C_minus ≠ 0 := hCm_pos.ne'
      have hn_ne : n ≠ 0 := hn_pos.ne'
      rwa [show n * (C_minus * (Real.log n / n)) = C_minus * Real.log n by field_simp [hn_ne],
        show n * (C_minus * (xiBar / C_minus)) = xiBar * n by field_simp [hCm_ne]] at h2
    have hAopt_nn : 0 ≤ Aopt * n ^ ((1 : ℝ) / 3) := by
      have hA : 0 ≤ Aopt := by unfold Aopt; exact mul_nonneg cStar_pos.le (abs_nonneg _)
      exact mul_nonneg hA (Real.rpow_nonneg hn_pos.le _)
    dsimp [T_minus]; linarith
  have hno_slack : ∀ {T : ℝ}, T < T_minus → ∀ {Φ : ℝ × ℝ → ℝ}, ¬ SpinIsSlackFeasible a T Φ := by
    intro T hT Φ hslack
    let u_T : ℝ := airyZero 1 + (C_loc + 1) * n ^ (-(1 / 3 : ℝ)) * Real.log n
    have ha1_neg : airyZero 1 < 0 := airyZero_neg 1
    have ha1_abs_ub : |airyZero 1| ≤ 2.35 := by
      have := airyZero_one
      rw [abs_of_neg ha1_neg]; linarith
    have hn13_pos : 0 < n ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn_pos _
    have hnu_pos : 0 < n ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hn_pos _
    have h_step_pos : 0 < (C_loc + 1) * n ^ (-(1 / 3 : ℝ)) * Real.log n := by positivity
    have ha1_lt_uT : airyZero 1 < u_T := by dsimp [u_T]; linarith
    have h_step_le1 : (C_loc + 1) * n ^ (-(1 / 3 : ℝ)) * Real.log n ≤ 1 := by
      have h := hN₂ n hn_N2
      have heq : (C_loc + 1) * n ^ (-(1 / 3 : ℝ)) * Real.log n =
          (C_loc + 1) * (Real.log n / n ^ ((1 : ℝ) / 3)) := by
        rw [Real.rpow_neg hn_pos.le, div_eq_mul_inv]; ring
      linarith
    have huT_le : u_T ≤ |airyZero 1| + 1 := by
      dsimp [u_T]; linarith [le_abs_self (airyZero 1)]
    have huT_abs_le4 : |u_T| ≤ 4 := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le (airyZero 1)]
    have huT_sq_le16 : u_T ^ 2 ≤ 16 := by
      calc u_T ^ 2 = |u_T| ^ 2 := (sq_abs u_T).symm
        _ ≤ 4 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) huT_abs_le4 2
        _ = 16 := by norm_num
    have huT_ac : |u_T| ≤ virasoroAC n ^ 2 := by
      have h3 := hN₃ n hn_N3
      have hnp23 : 0 < n ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hn_pos _
      have hinv : (n ^ (2 / 3 : ℝ))⁻¹ < δ_ac := by
        rw [← Real.rpow_neg hn_pos.le]; exact h3
      have hlt : 1 < δ_ac * n ^ (2 / 3 : ℝ) := (inv_lt_iff_one_lt_mul₀ hnp23).mp hinv
      have h8 : 8 < virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) := by
        dsimp [δ_ac] at hlt; linarith only [hlt]
      rw [virasoroAC_sq n hn_pos.le]
      linarith only [h8, huT_abs_le4]
    have herr := virasoro_deltaChart_err hn_pos huT_ac
    have hn43_le : n ^ (-(4 / 3 : ℝ)) ≤ n ^ (-(2 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn_ge1 (by norm_num)
    have hn13_le1 : n ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn_ge1 (by norm_num)
    have hdiv_err : |virasoroDeltaChart n u_T / n - xiBar| ≤
        (4 * cStar + 16 * C_err) * n ^ (-(2 / 3 : ℝ)) := by
      have herr_n : |virasoroDeltaChart n u_T / n - (xiBar - cStar * n ^ (-(2 / 3 : ℝ)) * u_T)| ≤
          C_err * n ^ (-(4 / 3 : ℝ)) * u_T ^ 2 := by
        have hm := div_le_div_of_nonneg_right herr hn_pos.le
        rw [← abs_of_pos hn_pos, ← abs_div, abs_of_pos hn_pos] at hm
        have hn_ne : n ≠ 0 := hn_pos.ne'
        have hpow1 : cStar * n ^ (1 / 3 : ℝ) * u_T / n = cStar * n ^ (-(2 / 3 : ℝ)) * u_T := by
          have hr : n ^ (1 / 3 : ℝ) / n = n ^ (-(2 / 3 : ℝ)) := by
            conv_lhs => rhs; rw [← Real.rpow_one n]
            rw [← Real.rpow_sub hn_pos]; norm_num
          calc cStar * n ^ (1 / 3 : ℝ) * u_T / n = cStar * (n ^ (1 / 3 : ℝ) / n) * u_T := by ring
            _ = cStar * n ^ (-(2 / 3 : ℝ)) * u_T := by rw [hr]
        have hpow2 : C_err * n ^ (-(1 / 3 : ℝ)) * u_T ^ 2 / n = C_err * n ^ (-(4 / 3 : ℝ)) * u_T ^ 2 := by
          have hr : n ^ (-(1 / 3 : ℝ)) / n = n ^ (-(4 / 3 : ℝ)) := by
            conv_lhs => rhs; rw [← Real.rpow_one n]
            rw [← Real.rpow_sub hn_pos]; norm_num
          calc C_err * n ^ (-(1 / 3 : ℝ)) * u_T ^ 2 / n =
              C_err * (n ^ (-(1 / 3 : ℝ)) / n) * u_T ^ 2 := by ring
            _ = C_err * n ^ (-(4 / 3 : ℝ)) * u_T ^ 2 := by rw [hr]
        have hlhs : (virasoroDeltaChart n u_T - (xiBar * n - cStar * n ^ (1 / 3 : ℝ) * u_T)) / n =
            virasoroDeltaChart n u_T / n - (xiBar - cStar * n ^ (-(2 / 3 : ℝ)) * u_T) := by
          rw [sub_div, sub_div, mul_div_cancel_right₀ _ hn_ne, hpow1]
        have hrhs : C_err * n ^ (-(1 / 3 : ℝ)) * u_T ^ 2 / n = C_err * n ^ (-(4 / 3 : ℝ)) * u_T ^ 2 := hpow2
        rwa [hlhs, hrhs] at hm
      have htri := abs_sub_le (virasoroDeltaChart n u_T / n) (xiBar - cStar * n ^ (-(2 / 3 : ℝ)) * u_T) xiBar
      have h_lin_err : |xiBar - cStar * n ^ (-(2 / 3 : ℝ)) * u_T - xiBar| ≤
          4 * cStar * n ^ (-(2 / 3 : ℝ)) := by
        have hcstar_nn : 0 ≤ cStar := cStar_pos.le
        rw [show xiBar - cStar * n ^ (-(2 / 3 : ℝ)) * u_T - xiBar = -(cStar * n ^ (-(2 / 3 : ℝ)) * u_T) by ring,
          abs_neg, abs_mul, abs_mul, abs_of_pos cStar_pos,
          abs_of_pos (Real.rpow_pos_of_pos hn_pos _)]
        calc cStar * n ^ (-(2 / 3 : ℝ)) * |u_T| ≤ cStar * n ^ (-(2 / 3 : ℝ)) * 4 := by gcongr
          _ = 4 * cStar * n ^ (-(2 / 3 : ℝ)) := by ring
      have h_quad_err : C_err * n ^ (-(4 / 3 : ℝ)) * u_T ^ 2 ≤ 16 * C_err * n ^ (-(2 / 3 : ℝ)) := by
        have hnp43 : 0 ≤ n ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hn_pos.le _
        calc C_err * n ^ (-(4 / 3 : ℝ)) * u_T ^ 2
            ≤ C_err * n ^ (-(2 / 3 : ℝ)) * 16 := by gcongr
          _ = 16 * C_err * n ^ (-(2 / 3 : ℝ)) := by ring
      linarith only [herr_n, htri, h_lin_err, h_quad_err]
    have hxi_pos_uT : 0 < virasoroDeltaChart n u_T / n := by
      have h4 := hN₄ n hn_N4
      have h_small : (4 * cStar + 16 * C_err) * n ^ (-(2 / 3 : ℝ)) < xiBar := by
        have hden : 0 < 4 * cStar + 16 * C_err + 1 := by have := cStar_pos; positivity
        have h1 : (4 * cStar + 16 * C_err + 1) * n ^ (-(2 / 3 : ℝ)) < (4 * cStar + 16 * C_err + 1) * δ_xb :=
          mul_lt_mul_of_pos_left h4 hden
        have h2 : (4 * cStar + 16 * C_err) * n ^ (-(2 / 3 : ℝ)) ≤ (4 * cStar + 16 * C_err + 1) * n ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only) (Real.rpow_nonneg hn_pos.le _)
        dsimp [δ_xb] at h1
        rw [mul_div_cancel₀ _ hden.ne'] at h1
        exact h2.trans_lt h1
      linarith only [(abs_le.mp hdiv_err).1, h_small]
    set x₁ : ℝ := (virasoroBChart n (u_T : ℂ)).re
    have hb := virasoroBChart_ofReal_eq_sqrt hn_pos huT_ac
    have hx₁_eq : x₁ = Real.sqrt (3 * virasoroDeltaChart n u_T / n) := hb.2.1
    have hxi3_pos : 0 < 3 * virasoroDeltaChart n u_T / n := by
      rw [mul_div_assoc]; exact mul_pos (by norm_num) hxi_pos_uT
    have hx₁_pos : 0 < x₁ := by
      rw [hx₁_eq]
      exact Real.sqrt_pos.mpr hxi3_pos
    have hx₁_sq : (n / 3) * x₁ ^ 2 = virasoroDeltaChart n u_T := by
      rw [hx₁_eq, Real.sq_sqrt hxi3_pos.le]
      field_simp [hn_pos.ne']
    have hx₁_close : |x₁ - xiStar| ≤ C₀ * n ^ (-(2 / 3 : ℝ)) := by
      have hsum_pos : xiStar ≤ x₁ + xiStar := by linarith only [hx₁_pos]
      have hdiff_sq : x₁ ^ 2 / 3 - xiStar ^ 2 / 3 = virasoroDeltaChart n u_T / n - xiBar := by
        have h1 : x₁ ^ 2 = 3 * virasoroDeltaChart n u_T / n := by
          rw [hx₁_eq, Real.sq_sqrt hxi3_pos.le]
        have h2 : xiBar = xiStar ^ 2 / 3 := rfl
        rw [h1, h2]; ring
      have hfac : |x₁ - xiStar| * ((x₁ + xiStar) / 3) = |x₁ ^ 2 / 3 - xiStar ^ 2 / 3| := by
        rw [← abs_of_pos (by linarith only [xiStar_pos, hx₁_pos] : 0 < (x₁ + xiStar) / 3), ← abs_mul]
        congr 1; ring
      have h1 : |x₁ - xiStar| * (xiStar / 3) ≤ |x₁ - xiStar| * ((x₁ + xiStar) / 3) := by gcongr
      have h2 : |x₁ - xiStar| * (xiStar / 3) ≤ (4 * cStar + 16 * C_err) * n ^ (-(2 / 3 : ℝ)) := by
        rw [hfac, hdiff_sq] at h1
        exact h1.trans hdiv_err
      have h3xi : 0 ≤ 3 / xiStar := div_nonneg (by norm_num) xiStar_pos.le
      have h3 : |x₁ - xiStar| ≤ (3 / xiStar) * (4 * cStar + 16 * C_err) * n ^ (-(2 / 3 : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_left h2 h3xi
        have hxi_ne : xiStar ≠ 0 := xiStar_pos.ne'
        rw [show (3 / xiStar) * (|x₁ - xiStar| * (xiStar / 3)) = |x₁ - xiStar| by field_simp [hxi_ne]] at hm
        linarith only [hm]
      have hrp_nn : 0 ≤ n ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hn_pos.le _
      exact h3.trans (mul_le_mul_of_nonneg_right (by dsimp [C₀]; linarith only [hrp_nn]) hrp_nn)
    have hTm_le_Δ : T_minus ≤ virasoroDeltaChart n u_T := by
      have hlhs : xiBar * n - cStar * n ^ (1 / 3 : ℝ) * u_T =
          xiBar * n + Aopt * n ^ (1 / 3 : ℝ) - cStar * (C_loc + 1) * Real.log n := by
        have hprod : n ^ (1 / 3 : ℝ) * n ^ (-(1 / 3 : ℝ)) = 1 := by
          rw [← Real.rpow_add hn_pos]; norm_num
        have hAopt : -cStar * airyZero 1 = Aopt := by
          unfold Aopt
          rw [abs_of_neg ha1_neg]; ring
        dsimp [u_T]
        calc xiBar * n - cStar * n ^ (1 / 3 : ℝ) * (airyZero 1 + (C_loc + 1) * n ^ (-(1 / 3 : ℝ)) * Real.log n)
            = xiBar * n + (-cStar * airyZero 1) * n ^ (1 / 3 : ℝ) -
                cStar * (C_loc + 1) * (n ^ (1 / 3 : ℝ) * n ^ (-(1 / 3 : ℝ))) * Real.log n := by ring
          _ = xiBar * n + Aopt * n ^ (1 / 3 : ℝ) - cStar * (C_loc + 1) * Real.log n := by
                rw [hAopt, hprod, mul_one]
      have herr_log : C_err * n ^ (-(1 / 3 : ℝ)) * u_T ^ 2 ≤ 16 * C_err * Real.log n := by
        have hnp13 : 0 ≤ n ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hn_pos.le _
        have h1 : C_err * n ^ (-(1 / 3 : ℝ)) * u_T ^ 2 ≤ C_err * 1 * 16 := by gcongr
        have h2 : 16 * C_err ≤ 16 * C_err * Real.log n :=
          le_mul_of_one_le_right (by linarith only [hCerr_nn]) hlog_ge1
        linarith only [h1, h2]
      have h_err_lo := (abs_le.mp herr).1
      have h_cm : C_minus * Real.log n = (cStar * (C_loc + 1) + 16 * C_err + 1) * Real.log n := rfl
      dsimp [T_minus]
      linarith only [h_err_lo, hlhs, herr_log, h_cm, hlog_pos]
    -- Rescale slack-feasible `Φ` to `SpinSlackHyp c x₁ Ψ`.
    obtain ⟨hΦ_tc, hΦ_M2_pos, hΦ_vac_slack, hΦ_cone⟩ := hslack
    let α : ℝ := (spinM2 a Φ)⁻¹
    have hα_pos : 0 < α := inv_pos.mpr hΦ_M2_pos
    let Ψ : ℝ × ℝ → ℝ := fun p => α * Φ p
    have hΨ_tc : SpinTestClass a Ψ :=
      { cont := continuous_const.mul hΦ_tc.cont
        int := hΦ_tc.int.const_mul α
        d4_inv := ⟨fun rL rR => by dsimp [Ψ]; rw [hΦ_tc.d4_inv.1],
          fun rL rR => by dsimp [Ψ]; rw [hΦ_tc.d4_inv.2.1],
          fun rL rR => by dsimp [Ψ]; rw [hΦ_tc.d4_inv.2.2]⟩
        fourier_odd := by
          have heq : spinToEuc Ψ = fun x => (α : ℂ) • spinToEuc Φ x := by
            ext x; simp [spinToEuc, Ψ]
          rw [heq]
          ext w
          simp only [Real.fourier_eq, Pi.neg_apply]
          simp_rw [smul_comm _ (α : ℂ), integral_smul]
          have hfo := congrFun hΦ_tc.fourier_odd w
          simp only [Real.fourier_eq, Pi.neg_apply] at hfo
          rw [hfo, smul_neg]
        int_M2 := by
          have heq : (fun p : ℝ × ℝ => |Ψ p| * spinV1 a p.1 * spinV1 a p.2) =
              fun p => α * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
            ext p; dsimp [Ψ]; rw [abs_mul, abs_of_pos hα_pos]; ring
          rw [heq]; exact hΦ_tc.int_M2.const_mul α }
    have hΨ_M2 : spinM2 a Ψ = 1 := by
      unfold spinM2
      have heq : (fun p : ℝ × ℝ => |Ψ p| * spinV1 a p.1 * spinV1 a p.2) =
          fun p => α * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
        ext p; dsimp [Ψ]; rw [abs_mul, abs_of_pos hα_pos]; ring
      rw [heq, integral_const_mul]
      exact inv_mul_cancel₀ hΦ_M2_pos.ne'
    have hΨ_vac : -(c - 1)⁻¹ ≤ spinPhiVac a Ψ := by
      unfold spinPhiVac
      have heq : (fun p : ℝ × ℝ => Ψ p * spinV1 a p.1 * spinV1 a p.2) =
          fun p => α * (Φ p * spinV1 a p.1 * spinV1 a p.2) := by ext p; dsimp [Ψ]; ring
      rw [heq, integral_const_mul]
      have h12a : 12 * a = c - 1 := by dsimp [a, n]; ring
      have hsc : α * (-(12 * a)⁻¹ * spinM2 a Φ) = -(c - 1)⁻¹ := by
        rw [h12a]; dsimp [α]; field_simp [hΦ_M2_pos.ne']
      have hv : -(12 * a)⁻¹ * spinM2 a Φ ≤ -(∫ p : ℝ × ℝ, Φ p * spinV1 a p.1 * spinV1 a p.2) := hΦ_vac_slack
      calc -(c - 1)⁻¹ = α * (-(12 * a)⁻¹ * spinM2 a Φ) := hsc.symm
        _ ≤ α * -(∫ p : ℝ × ℝ, Φ p * spinV1 a p.1 * spinV1 a p.2) :=
            mul_le_mul_of_nonneg_left hv hα_pos.le
        _ = -(α * ∫ p : ℝ × ℝ, Φ p * spinV1 a p.1 * spinV1 a p.2) := by ring
    have hΨ_G : ∀ ξ d : ℝ, x₁ ^ 2 ≤ ξ ^ 2 + d ^ 2 → 0 ≤ spinG a Ψ (ξ + d) (ξ - d) := by
      intro ξ d hxd
      let tL := (2 * Real.sqrt a * (ξ + d)) ^ 2 / 2
      let tR := (2 * Real.sqrt a * (ξ - d)) ^ 2 / 2
      have htL : 0 ≤ tL := by dsimp [tL]; positivity
      have htR : 0 ≤ tR := by dsimp [tR]; positivity
      have htsum : T ≤ tL + tR := by
        have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith only [ha_ge2])
        have hsum_eq : tL + tR = 4 * a * (ξ ^ 2 + d ^ 2) := by
          dsimp [tL, tR]; rw [mul_pow, mul_pow, mul_pow, mul_pow, hsq]; ring
        have h4a : 4 * a = n / 3 := by dsimp [a]; ring
        have hle1 : (n / 3) * x₁ ^ 2 ≤ tL + tR := by
          rw [hsum_eq, h4a]
          exact mul_le_mul_of_nonneg_left hxd (by positivity)
        linarith only [hT, hTm_le_Δ, hx₁_sq, hle1]
      have heval : 0 ≤ spinEvalT Ψ (tL, tR) := by
        dsimp [Ψ, spinEvalT]
        exact mul_nonneg hα_pos.le (hΦ_cone (tL, tR) ⟨htL, htR, htsum⟩)
      have hsr1 : Real.sqrt (2 * tL) = |2 * Real.sqrt a * (ξ + d)| := by
        dsimp [tL]; rw [show 2 * ((2 * Real.sqrt a * (ξ + d)) ^ 2 / 2) = (2 * Real.sqrt a * (ξ + d)) ^ 2 by ring,
          Real.sqrt_sq_eq_abs]
      have hsr2 : Real.sqrt (2 * tR) = |2 * Real.sqrt a * (ξ - d)| := by
        dsimp [tR]; rw [show 2 * ((2 * Real.sqrt a * (ξ - d)) ^ 2 / 2) = (2 * Real.sqrt a * (ξ - d)) ^ 2 by ring,
          Real.sqrt_sq_eq_abs]
      have hG_eq : spinG a Ψ (ξ + d) (ξ - d) = spinEvalT Ψ (tL, tR) := by
        unfold spinG spinEvalT
        rw [hsr1, hsr2]
        rcases le_total 0 (2 * Real.sqrt a * (ξ + d)) with h1 | h1 <;>
        rcases le_total 0 (2 * Real.sqrt a * (ξ - d)) with h2 | h2
        · rw [abs_of_nonneg h1, abs_of_nonneg h2]
        · rw [abs_of_nonneg h1, abs_of_nonpos h2, hΨ_tc.d4_inv.2.1]
        · rw [abs_of_nonpos h1, abs_of_nonneg h2, hΨ_tc.d4_inv.1]
        · rw [abs_of_nonpos h1, abs_of_nonpos h2, hΨ_tc.d4_inv.1, hΨ_tc.d4_inv.2.1]
      rw [hG_eq]; exact heval
    have hslack_hyp : SpinSlackHyp c x₁ Ψ := ⟨hx₁_pos.le, hΨ_tc, hΨ_M2, hΨ_vac, hΨ_G⟩
    have hbd := hshrink hc_thr hx₁_close ha1_lt_uT huT_le rfl hslack_hyp
    have hlhs_eq : n ^ (1 / 3 : ℝ) * (u_T - airyZero 1) = (C_loc + 1) * Real.log n := by
      have hprod : n ^ (1 / 3 : ℝ) * n ^ (-(1 / 3 : ℝ)) = 1 := by
        rw [← Real.rpow_add hn_pos]; norm_num
      dsimp [u_T]
      calc n ^ (1 / 3 : ℝ) * (airyZero 1 + (C_loc + 1) * n ^ (-(1 / 3 : ℝ)) * Real.log n - airyZero 1)
          = (C_loc + 1) * (n ^ (1 / 3 : ℝ) * n ^ (-(1 / 3 : ℝ))) * Real.log n := by ring
        _ = (C_loc + 1) * Real.log n := by rw [hprod, mul_one]
    rw [hlhs_eq] at hbd
    linarith only [hbd, hlog_pos]
  refine ⟨hTm_pos, fun hT => hno_slack hT, ?_⟩
  have hc_shift : 12 * virasoroProblem.totalShift ≤ c - 1 := by
    rw [virasoroProblem_totalShift]; linarith
  have hne_spinless : {T : ℝ | 0 < T ∧ ∃ g, virasoroProblem.IsFeasible a T g}.Nonempty :=
    virasoroProblem.feasible_nonempty hc_shift
  have hne_base : {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible (SpinTestClass a) liouvilleCone a T Φ}.Nonempty := by
    obtain ⟨T, hT, g, hg⟩ := hne_spinless
    refine ⟨T, hT, spinRadialLift g, spinTestClassJ_radialLift ha_ge2 hg.1 |>.base, ?_, ?_⟩
    · rw [(spinM2_and_phiVac_radialLift ha_ge2 hg.1).2]; exact hg.2.1
    · intro p ⟨hp1, hp2, hsum⟩
      rw [spinEvalT_radialLift g hp1 hp2]
      exact hg.2.2 (p.1 + p.2) hsum
  have hTm_le_inf : T_minus ≤ spinThrInf (SpinTestClass a) liouvilleCone a := by
    by_contra hlt
    push Not at hlt
    obtain ⟨T, ⟨_, Φ, hfeas⟩, hT⟩ := exists_lt_of_csInf_lt hne_base hlt
    have hweak := hfeas.isWeaklyFeasible ha_ge2
    have hslack_of_weak : SpinIsSlackFeasible a T Φ := by
      refine ⟨hweak.1, hweak.2.1, ?_, hweak.2.2.2⟩
      have h_neg : -(12 * a)⁻¹ * spinM2 a Φ ≤ 0 := by
        have hm := hweak.2.1
        have ha0 : 0 < a := by linarith only [ha_ge2]
        have : 0 ≤ (12 * a)⁻¹ * spinM2 a Φ := by positivity
        linarith only [this]
      exact h_neg.trans hweak.2.2.1
    exact hno_slack hT hslack_of_weak
  have hΔL_eq : spinDeltaL c = a + spinThrInf (SpinTestClass a) liouvilleCone a := by
    unfold spinDeltaL; rfl
  have hinv_eq : n / lambdaV = a + xiBar * n := by
    rw [xiBar_eq_inv_lambdaV_sub]
    dsimp [a]; ring
  rw [hΔL_eq, hinv_eq]
  dsimp [T_minus] at hTm_le_inf
  linarith only [hTm_le_inf]

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_6_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_6_1

end FormalResearch.ModularBootstrap.Spin
