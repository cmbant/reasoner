module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentVac

/-!
# SPIN-M part 3c: Full vacuum-source upper limit (`sd:spinmoment-ref-limit`)

Completes `spinMoment_vac_source_limsup_le`:
`limsup (π c' C_* FKc 1 1 c')⁻¹ ∫₀^∞ g₅(t) H_C(t) dt ≤ (ξ_*³/(3π)) windowIntegralSig`.
Kept in its own leaf module so every module stays concise (`<= 800` lines).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design
open FormalResearch.ModularBootstrap.Upper.Holes
open FormalResearch.ModularBootstrap.Upper.Membership
open FormalResearch.ModularBootstrap.Upper.Positivity
open FormalResearch.ModularBootstrap.Upper.Bump
open FormalResearch.ModularBootstrap.Upper.Ramped
open FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.Upper.Window.Cardy
open FormalResearch.ModularBootstrap.Upper.Window.Tail
open FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Rigidity

private lemma quad_t_le {c' a b : ℝ} (hc : 0 ≤ c') (ha : 0 ≤ a) (hab : a ≤ b) :
    c' * a ^ 2 / 3 ≤ c' * b ^ 2 / 3 :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 2) hc)
    (by norm_num : (0 : ℝ) ≤ 3)

private lemma hc_ratio_bound_aux {C_HC0 c' x : ℝ} (hx : x ∈ Icc (xiStar / 2) (xiStar + 1 / 4))
    (h1 : |spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) -
        x ^ 3 / (3 * π)| ≤ C_HC0 / c')
    (h3 : C_HC0 / c' ≤ 1 / 2) (h4 : C_HC0 / c' ≤ (xiStar / 2) ^ 3 / (6 * π)) :
    |spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3))| ≤
        (xiStar + 1 / 4) ^ 3 / (3 * π) + 1 ∧
      0 ≤ spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) := by
  have hxi := xiStar_pos
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have h3pi : (0 : ℝ) ≤ 3 * π := by positivity
  have h2 : |x ^ 3 / (3 * π)| ≤ (xiStar + 1 / 4) ^ 3 / (3 * π) := by
    rw [abs_of_nonneg (div_nonneg (pow_nonneg hx0 3) h3pi)]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hx.2 3) h3pi
  have hx3_lo : (xiStar / 2) ^ 3 / (3 * π) ≤ x ^ 3 / (3 * π) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hx.1 3) h3pi
  have hsub := abs_sub_abs_le_abs_sub
    (spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)))
    (x ^ 3 / (3 * π))
  have hbd_hi : |spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3))| ≤
      (xiStar + 1 / 4) ^ 3 / (3 * π) + 1 := by linarith
  have hlo_nn : 0 ≤ (xiStar / 2) ^ 3 / (6 * π) := by positivity
  have h6pi : (xiStar / 2) ^ 3 / (3 * π) = 2 * ((xiStar / 2) ^ 3 / (6 * π)) := by ring
  exact ⟨hbd_hi, by linarith [(abs_le.mp h1).1]⟩

private lemma kv_ratio_bound_aux {q5 C_K0 c' x : ℝ} (hq5 : 0 < q5)
    (hx : x ∈ Icc (xiStar / 2) (xiStar + 1 / 4))
    (h1 : |(q5 * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) / kernelK 5 (c' / 12) (c' * x ^ 2 / 3) -
        q5 * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4)| ≤ C_K0 / c')
    (h3 : C_K0 / c' ≤ 1 / 2) :
    |(q5 * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) / kernelK 5 (c' / 12) (c' * x ^ 2 / 3)| ≤
      q5 * ((1 - Real.exp (-4 * π * (xiStar + 1 / 4))) ^ 2 / (2 * (xiStar / 2)) ^ 4) + 1 := by
  have hxi := xiStar_pos
  have hx0 : 0 < x := lt_of_lt_of_le (half_pos hxi) hx.1
  have harg : -4 * π * x ≤ 0 := by nlinarith [hx0, Real.pi_pos]
  have hK_poly : |q5 * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4)| ≤
      q5 * ((1 - Real.exp (-4 * π * (xiStar + 1 / 4))) ^ 2 / (2 * (xiStar / 2)) ^ 4) := by
    rw [abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) ?_ (by positivity) ?_) hq5.le
    · refine pow_le_pow_left₀ (sub_nonneg.mpr (Real.exp_le_one_iff.mpr harg)) ?_ 2
      have := Real.exp_le_exp.mpr (show -4 * π * (xiStar + 1 / 4) ≤ -4 * π * x by nlinarith [hx.2, Real.pi_pos])
      linarith
    · exact pow_le_pow_left₀ (by positivity) (by linarith [hx.1]) 4
  have hsub := abs_sub_abs_le_abs_sub
    ((q5 * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) / kernelK 5 (c' / 12) (c' * x ^ 2 / 3))
    (q5 * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4))
  linarith

private lemma spinMoment_win_pt_aux (N : ℕ) (hN : 1 ≤ N) {η c' : ℝ} (hcpos : 0 < c')
    (hcS : 12 * virasoroProblem.totalShift ≤ c') (σs : ℕ → ℝ) (n : ℕ)
    {r_lim δ_Q δ_R K_HC K_V M₀ M_P e_tot e_P e_Q e_R C_HC0 C_K0 : ℝ}
    (hr_lim_2 : r_lim ≤ xiStar / 2) (hr_lim_14 : r_lim ≤ 1 / 4)
    (hr_lim_Q : r_lim < δ_Q) (hr_lim_R : r_lim < δ_R)
    (hK_HC_pos : 0 < K_HC) (_hK_V_pos : 0 < K_V) (hM_P_pos : 0 < M_P)
    (_he_tot : 0 < e_tot) (he_P : 0 < e_P) (he_Q : 0 < e_Q) (_he_R : 0 < e_R)
    (heP_bd : e_P * (K_HC * K_V) ≤ e_tot / 3)
    (heQ_bd : e_Q * (M_P * K_V) ≤ e_tot / 3)
    (heR_bd : (M_P * (xiStar ^ 3 / (3 * π))) * e_R ≤ e_tot / 3)
    (hM_P_ge : M₀ / CStar ≤ M_P)
    (hM₀ : ∀ σ ∈ Icc (-(n : ℝ)) (phiWKB (n + 1)),
      ‖tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim (sigMod N η σs).allEpsLim σ‖ ≤ M₀)
    (hl_n : lambdaComb c' * (n : ℝ) ≤ r_lim)
    (hl_Φ : lambdaComb c' * phiWKB (n + 1) ≤ r_lim)
    (hHC_c : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4),
      |spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) -
        x ^ 3 / (3 * π)| ≤ C_HC0 / c')
    (hK_c : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4),
      |(qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) /
          kernelK 5 (c' / 12) (c' * x ^ 2 / 3) -
        qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4)| ≤ C_K0 / c')
    (hc_HC_c : C_HC0 / c' ≤ e_Q / 2) (hc_K_c : C_K0 / c' ≤ e_R / 2)
    (hQ_uc : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4), dist x xiStar < δ_Q →
      dist (x ^ 3 / (3 * π)) (xiStar ^ 3 / (3 * π)) < e_Q / 2)
    (hR_uc : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4), dist x xiStar < δ_R →
      dist (qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4))
        (qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * xiStar)) ^ 2 / (2 * xiStar) ^ 4)) < e_R / 2)
    (hR_star_eq : qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * xiStar)) ^ 2 / (2 * xiStar) ^ 4) = 1)
    (hHC_ratio_le : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4),
      |spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3))| ≤ K_HC ∧
      0 ≤ spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)))
    (hKV_ratio_le : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4),
      |(qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) /
        kernelK 5 (c' / 12) (c' * x ^ 2 / 3)| ≤ K_V)
    (hpart1 : ∀ σ ∈ Icc (-(n : ℝ)) (phiWKB (n + 1)),
      |combProfile c' (bumpBc (rpParams 4).bumpData N η σs c')
          (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          spinMomentW5Prob.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          (2 * c' * (xiStar + lambdaComb c' * σ) / 3 * lambdaComb c') /
          FKc (qProb spinMomentW5Prob) 1 c' -
        CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ)| ≤ CStar * e_P) :
    ∀ σ ∈ Icc (-(n : ℝ)) (phiWKB (n + 1)),
      (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          spinVacHC (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3)) *
          (2 * c' * (xiStar + lambdaComb c' * σ) / 3 * lambdaComb c') ≤
        (2 * π * c' * CStar * FKc 1 1 c') *
          ((xiStar ^ 3 / (3 * π)) *
            (tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
              (sigMod N η σs).allEpsLim σ / CStar) + e_tot) := by
  intro σ hσ
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  have hCS_pos : 0 < CStar := CStar_pos
  have hq5_pos : 0 < qProb spinMomentW5Prob := qProb_pos spinMomentW5Prob
  have hlpos := lambdaComb_pos' hcpos
  have hFK1_pos : 0 < FKc 1 1 c' := FKc_pos one_pos 1 hcpos
  have hFKq_eq : FKc (qProb spinMomentW5Prob) 1 c' = qProb spinMomentW5Prob * FKc 1 1 c' :=
    FKc_q_eq _ 1 c'
  have hFKq_pos : 0 < FKc (qProb spinMomentW5Prob) 1 c' := FKc_pos hq5_pos 1 hcpos
  have hV_star_nn : 0 ≤ xiStar ^ 3 / (3 * π) := by positivity
  let x : ℝ := xiStar + lambdaComb c' * σ
  let t : ℝ := c' * x ^ 2 / 3
  have hdx_le : |x - xiStar| ≤ min r_lim (xiStar / 2) := by
    have hlam_abs : |lambdaComb c' * σ| ≤ r_lim := by
      rw [abs_mul, abs_of_pos hlpos]
      rcases le_total σ 0 with hs | hs
      · rw [abs_of_nonpos hs]
        calc lambdaComb c' * (-σ) ≤ lambdaComb c' * n := mul_le_mul_of_nonneg_left (by linarith [hσ.1]) hlpos.le
          _ ≤ r_lim := hl_n
      · rw [abs_of_nonneg hs]
        calc lambdaComb c' * σ ≤ lambdaComb c' * phiWKB (n + 1) := mul_le_mul_of_nonneg_left hσ.2 hlpos.le
          _ ≤ r_lim := hl_Φ
    rw [show x - xiStar = lambdaComb c' * σ by dsimp [x]; ring]
    exact le_min hlam_abs (hlam_abs.trans hr_lim_2)
  have hx_mem : x ∈ Icc (xiStar / 2) (xiStar + 1 / 4) := by
    have h1 := (abs_le.mp (hdx_le.trans (min_le_right _ _))).1
    have h2 := (abs_le.mp ((hdx_le.trans (min_le_left _ _)).trans hr_lim_14)).2
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  have hx0 : 0 < x := lt_of_lt_of_le (half_pos hxi) hx_mem.1
  have ht0 : 0 < t := by dsimp [t]; positivity
  have hV_pos : 0 < virasoroProblem.cardyV (c' / 12) t :=
    virasoroProblem.cardyV_pos (by linarith only [hcS]) ht0
  have hK5_pos : 0 < kernelK 5 (c' / 12) t := by
    rw [← spinMomentW5Prob_cardyV]
    exact spinMomentW5Prob.cardyV_pos (by rw [spinMomentW5Prob_totalShift]; linarith only [hcpos]) ht0
  let B := bumpBc (rpParams 4).bumpData N η σs c'
  let P : ℝ := (combProfile c' B t * kernelK 5 (c' / 12) t * (2 * c' * x / 3 * lambdaComb c')) /
      (CStar * FKc (qProb spinMomentW5Prob) 1 c')
  let P₀ : ℝ := tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
      (sigMod N η σs).allEpsLim σ / CStar
  let Q : ℝ := spinVacHC (c' / 12) t / (2 * π * c' * virasoroProblem.cardyV (c' / 12) t)
  let R : ℝ := (qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) t) / kernelK 5 (c' / 12) t
  let FK_vac : ℝ := 2 * π * c' * CStar * FKc 1 1 c'
  have hFK_vac_pos : 0 < FK_vac := by positivity
  have h_alg : (combProfile c' B t * spinVacHC (c' / 12) t) * (2 * c' * x / 3 * lambdaComb c') / FK_vac =
      P * Q * R := by
    dsimp [P, Q, R, FK_vac]
    rw [hFKq_eq]
    field_simp [hCS_pos.ne', hFK1_pos.ne', hq5_pos.ne', hV_pos.ne', hK5_pos.ne', hpi.ne', hcpos.ne']
  have hP_err : |P - P₀| ≤ e_P := by
    have hp1 := hpart1 σ hσ
    have h_eq : P - P₀ =
        (combProfile c' B t * spinMomentW5Prob.cardyV (c' / 12) t * (2 * c' * x / 3 * lambdaComb c') /
            FKc (qProb spinMomentW5Prob) 1 c' -
          CStar * kappaAiry * (sigWindowW N η σs ((-kappaAiry * σ : ℝ) : ℂ)).re) / CStar := by
      dsimp [P, P₀, t, x]
      rw [spinMomentW5Prob_cardyV, tildeW_sigMod N hN η σs σ]
      field_simp [hCS_pos.ne', hFKq_pos.ne']
    rw [h_eq, abs_div, abs_of_pos hCS_pos, div_le_iff₀ hCS_pos]
    simpa [B, sigWinW, mul_comm CStar e_P] using hp1
  have hP₀_bd : |P₀| ≤ M_P := by
    have h1 : |tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
        (sigMod N η σs).allEpsLim σ| ≤ M₀ := by
      simpa [Real.norm_eq_abs] using hM₀ σ hσ
    dsimp [P₀]
    calc |tildeW 1 _ _ _ σ / CStar| = |tildeW 1 _ _ _ σ| / CStar := by rw [abs_div, abs_of_pos hCS_pos]
      _ ≤ M₀ / CStar := div_le_div_of_nonneg_right h1 hCS_pos.le
      _ ≤ M_P := hM_P_ge
  have hQ_bd : |Q| ≤ K_HC := (hHC_ratio_le x hx_mem).1
  have hR_bd : |R| ≤ K_V := hKV_ratio_le x hx_mem
  have hQ_err : |Q - xiStar ^ 3 / (3 * π)| ≤ e_Q := by
    have hQ1 := hHC_c x hx_mem
    have hdist : dist x xiStar < δ_Q := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (hdx_le.trans (min_le_left _ _)) hr_lim_Q
    have hQ2 := hQ_uc x hx_mem hdist
    rw [Real.dist_eq] at hQ2
    have hQ1' : |Q - x ^ 3 / (3 * π)| ≤ e_Q / 2 := hQ1.trans hc_HC_c
    have htri := abs_add_le (Q - x ^ 3 / (3 * π)) (x ^ 3 / (3 * π) - xiStar ^ 3 / (3 * π))
    rw [show (Q - x ^ 3 / (3 * π)) + (x ^ 3 / (3 * π) - xiStar ^ 3 / (3 * π)) =
      Q - xiStar ^ 3 / (3 * π) by ring] at htri
    linarith only [hQ1', hQ2, htri]
  have hR_err : |R - 1| ≤ e_R := by
    have hR1 := hK_c x hx_mem
    have hdist : dist x xiStar < δ_R := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (hdx_le.trans (min_le_left _ _)) hr_lim_R
    have hR2 := hR_uc x hx_mem hdist
    rw [Real.dist_eq, hR_star_eq] at hR2
    have hR1' : |R - qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4)| ≤ e_R / 2 :=
      hR1.trans hc_K_c
    have htri := abs_add_le
      (R - qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4))
      (qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4) - 1)
    rw [show (R - qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4)) +
      (qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4) - 1) = R - 1 by ring] at htri
    linarith only [hR1', hR2, htri]
  have hprod_err : |P * Q * R - (xiStar ^ 3 / (3 * π)) * P₀| ≤ e_tot := by
    have hid : P * Q * R - (xiStar ^ 3 / (3 * π)) * P₀ =
        (P - P₀) * (Q * R) + P₀ * ((Q - xiStar ^ 3 / (3 * π)) * R) +
          (P₀ * (xiStar ^ 3 / (3 * π))) * (R - 1) := by ring
    rw [hid]
    have t1 : |(P - P₀) * (Q * R)| ≤ e_tot / 3 := by
      rw [abs_mul, abs_mul]
      calc |P - P₀| * (|Q| * |R|) ≤ e_P * (K_HC * K_V) :=
            mul_le_mul hP_err (mul_le_mul hQ_bd hR_bd (abs_nonneg _) hK_HC_pos.le)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) he_P.le
        _ ≤ e_tot / 3 := heP_bd
    have t2 : |P₀ * ((Q - xiStar ^ 3 / (3 * π)) * R)| ≤ e_tot / 3 := by
      rw [abs_mul, abs_mul]
      calc |P₀| * (|Q - xiStar ^ 3 / (3 * π)| * |R|) ≤ M_P * (e_Q * K_V) :=
            mul_le_mul hP₀_bd (mul_le_mul hQ_err hR_bd (abs_nonneg _) he_Q.le)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hM_P_pos.le
        _ = e_Q * (M_P * K_V) := by ring
        _ ≤ e_tot / 3 := heQ_bd
    have t3 : |(P₀ * (xiStar ^ 3 / (3 * π))) * (R - 1)| ≤ e_tot / 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hV_star_nn]
      calc |P₀| * (xiStar ^ 3 / (3 * π)) * |R - 1| ≤ (M_P * (xiStar ^ 3 / (3 * π))) * e_R :=
            mul_le_mul (mul_le_mul_of_nonneg_right hP₀_bd hV_star_nn) hR_err (abs_nonneg _)
              (mul_nonneg hM_P_pos.le hV_star_nn)
        _ ≤ e_tot / 3 := heR_bd
    have ha1 := abs_add_le ((P - P₀) * (Q * R) + P₀ * ((Q - xiStar ^ 3 / (3 * π)) * R))
      ((P₀ * (xiStar ^ 3 / (3 * π))) * (R - 1))
    have ha2 := abs_add_le ((P - P₀) * (Q * R)) (P₀ * ((Q - xiStar ^ 3 / (3 * π)) * R))
    linarith only [ha1, ha2, t1, t2, t3]
  have hle_div : (combProfile c' B t * spinVacHC (c' / 12) t) * (2 * c' * x / 3 * lambdaComb c') / FK_vac ≤
      (xiStar ^ 3 / (3 * π)) * P₀ + e_tot := by
    rw [h_alg]; linarith only [(abs_le.mp hprod_err).2]
  exact ((div_le_iff₀ hFK_vac_pos).mp hle_div).trans_eq (mul_comm _ _)

private lemma spinMoment_abs_setIntegral_le (N : ℕ) (_hN : 1 ≤ N) {η c' M R_S : ℝ}
    (hM_nn : 0 ≤ M) (σs : ℕ → ℝ) {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_sub : S ⊆ Ioi 0)
    (hk_h : KernelIntegrable 5 (c' / 12) (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c')))
    (hInt_h_HC : IntegrableOn
      (fun t => combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') t * spinVacHC (c' / 12) t) (Ioi 0))
    (hvalc : ∀ t : ℝ,
      combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') t =
        bumpFactor (rpParams 4).bumpData c' (1 / 4) N (bumpCut (rpParams 4).bumpData N c') (xOf c' t) *
          combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t)
    (hbf1 : ∀ x : ℝ,
      1 ≤ bumpFactor (rpParams 4).bumpData c' (1 / 4) N (bumpCut (rpParams 4).bumpData N c') x)
    (h_hc : ∀ t ∈ S, |spinVacHC (c' / 12) t| ≤ M * spinMomentW5Prob.cardyV (c' / 12) t)
    (hTc_S : ∫ t in S,
      bumpFactor (rpParams 4).bumpData c' (1 / 4) N (bumpCut (rpParams 4).bumpData N c') (xOf c' t) *
        (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
          spinMomentW5Prob.cardyV (c' / 12) t) ≤ R_S) :
    ∫ t in S, |combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') t * spinVacHC (c' / 12) t| ≤
      M * R_S := by
  let d5 := (rpParams 4).bumpData
  let B := bumpBc d5 N η σs c'
  have h_pt : ∀ t ∈ S,
      |combProfile c' B t * spinVacHC (c' / 12) t| ≤ M *
        (bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) *
          (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
            spinMomentW5Prob.cardyV (c' / 12) t)) := fun t ht => by
    have hval := hvalc t
    have hbf0 : 0 ≤ bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) :=
      zero_le_one.trans (hbf1 (xOf c' t))
    have hh_eq : |combProfile c' B t| =
        bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) *
          |combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| := by
      rw [hval, abs_mul, abs_of_nonneg hbf0]
    rw [abs_mul, hh_eq]
    calc bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) *
          |combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| * |spinVacHC (c' / 12) t|
        ≤ bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) *
            |combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
            (M * spinMomentW5Prob.cardyV (c' / 12) t) :=
          mul_le_mul_of_nonneg_left (h_hc t ht) (mul_nonneg hbf0 (abs_nonneg _))
      _ = _ := by ring
  have hInt_rhs : IntegrableOn (fun t =>
      M * (bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) *
        (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
          spinMomentW5Prob.cardyV (c' / 12) t))) S := by
    refine IntegrableOn.congr_fun ((hk_h.mono_set hS_sub).const_mul M) (fun t _ => ?_) hS_meas
    have hval := hvalc t
    have hbf0 : 0 ≤ bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) :=
      zero_le_one.trans (hbf1 (xOf c' t))
    rw [hval, abs_mul, abs_of_nonneg hbf0, spinMomentW5Prob_cardyV]; ring
  calc ∫ t in S, |combProfile c' B t * spinVacHC (c' / 12) t|
      ≤ ∫ t in S, M * (bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) *
          (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
            spinMomentW5Prob.cardyV (c' / 12) t)) :=
        setIntegral_mono_on (hInt_h_HC.mono_set hS_sub).abs hInt_rhs hS_meas h_pt
    _ = M * ∫ t in S, bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) *
          (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
            spinMomentW5Prob.cardyV (c' / 12) t) := integral_const_mul _ _
    _ ≤ M * R_S := mul_le_mul_of_nonneg_left hTc_S hM_nn

private lemma spinMoment_vac_source_at_c' (N : ℕ) (hN : 1 ≤ N) {η ε : ℝ} (hε : 0 < ε)
    (σs : ℕ → ℝ) (n : ℕ) (hnR : (0 : ℝ) ≤ n) (hΦ0 : 0 ≤ phiWKB (n + 1))
    {C_hat C_T C_far C_HC0 C_K0 K_HC K_V C_band ε_win M₀ M_P δ_Q δ_R r_lim e_tot e_P e_Q e_R c' : ℝ}
    (hK_HC_pos : 0 < K_HC) (hK_V_pos : 0 < K_V) (_hC_band_nn : 0 ≤ C_band)
    (hM_P_pos : 0 < M_P) (hM_P_ge : M₀ / CStar ≤ M_P)
    (he_tot : 0 < e_tot) (he_P : 0 < e_P) (he_Q : 0 < e_Q) (he_R : 0 < e_R)
    (heP_bd : e_P * (K_HC * K_V) ≤ e_tot / 3) (heQ_bd : e_Q * (M_P * K_V) ≤ e_tot / 3)
    (heR_bd : (M_P * (xiStar ^ 3 / (3 * π))) * e_R ≤ e_tot / 3)
    (he_Δ : e_tot * (phiWKB (n + 1) + n) ≤ ε / 6)
    (hε_win : 0 < ε_win) (hwin_le : ε_win ≤ ε / 6) (hvc_eps : ((xiStar ^ 3 / (3 * π)) / CStar) * ε_win ≤ ε / 6)
    (hr_lim_2 : r_lim ≤ xiStar / 2) (hr_lim_14 : r_lim ≤ 1 / 4)
    (hr_lim_Q : r_lim < δ_Q) (hr_lim_R : r_lim < δ_R)
    (hw_cont : Continuous (tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
      (sigMod N η σs).allEpsLim))
    (hM₀ : ∀ σ ∈ Icc (-(n : ℝ)) (phiWKB (n + 1)),
      ‖tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim (sigMod N η σs).allEpsLim σ‖ ≤ M₀)
    (hn3 : 6 * C_band * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ε_win / 4)
    (hn4 : ∫ σ in -(n : ℝ)..phiWKB (n + 1),
      tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim (sigMod N η σs).allEpsLim σ ≤
        CStar * windowIntegralSig N η σs + ε_win / 4)
    (hQ_uc : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4), dist x xiStar < δ_Q →
      dist (x ^ 3 / (3 * π)) (xiStar ^ 3 / (3 * π)) < e_Q / 2)
    (hR_uc : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4), dist x xiStar < δ_R →
      dist (qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4))
        (qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * xiStar)) ^ 2 / (2 * xiStar) ^ 4)) < e_R / 2)
    (hR_star_eq : qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * xiStar)) ^ 2 / (2 * xiStar) ^ 4) = 1)
    (hK_HC_eq : K_HC = (xiStar + 1 / 4) ^ 3 / (3 * π) + 1)
    (hK_V_eq : K_V = qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * (xiStar + 1 / 4))) ^ 2 / (2 * (xiStar / 2)) ^ 4) + 1)
    (hC_band_eq : C_band = K_HC * K_V / CStar)
    (hcont_h : ContinuousOn (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c')) (Ici 0))
    (hk_h : KernelIntegrable 5 (c' / 12) (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c')))
    (hInt_hat : IntegrableOn (fun t =>
      hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c')) t * spinVacHC (c' / 12) t) (Ioi 0))
    (hbd_hat : |∫ t in Ioi 0,
      hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c')) t * spinVacHC (c' / 12) t| ≤ C_hat * c')
    (hTc : ∀ Bcut : ℝ → ℝ, (∀ t, 0 ≤ Bcut t ∧ Bcut t ≤ bumpC (rpParams 4).bumpData (1 / 4)) →
      (∫ t in Icc (c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + 1 / 4) ^ 2 / 3),
        Bcut t * (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
          spinMomentW5Prob.cardyV (c' / 12) t) ≤
        FKc (qProb spinMomentW5Prob) 1 c' * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∫ t in Ici (c' * (xiStar + 1 / 4) ^ 2 / 3),
        Bcut t * (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
          spinMomentW5Prob.cardyV (c' / 12) t) ≤ C_far * √c'))
    (hHC_c : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4),
      |spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) -
        x ^ 3 / (3 * π)| ≤ C_HC0 / c')
    (hK_c : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4),
      |(qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) /
          kernelK 5 (c' / 12) (c' * x ^ 2 / 3) -
        qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4)| ≤ C_K0 / c')
    (hlobe_c : (∫ t in Ioc 0 (c' * (xiStar / 2) ^ 2 / 3),
      |combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') t * spinVacHC (c' / 12) t|) / (c' * FKc 1 1 c') ≤
      (ε / 6) * (2 * π * CStar))
    (hhat_lim_c : (C_hat * c' / 2) / (π * c' * CStar * FKc 1 1 c') ≤ ε / 6)
    (hfar_lim_c : (4 * C_far * √c') / (2 * π * CStar * FKc 1 1 c') ≤ ε / 6)
    (hc_K_c : C_K0 / c' ≤ min (1 / 2) (e_R / 2))
    (hc_HC_c : C_HC0 / c' ≤ min ((xiStar / 2) ^ 3 / (6 * π)) (min (1 / 2) (e_Q / 2)))
    (hpart1 : ∀ σ ∈ Icc (-(n : ℝ)) (phiWKB (n + 1)),
      |combProfile c' (bumpBc (rpParams 4).bumpData N η σs c')
          (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          spinMomentW5Prob.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          (2 * c' * (xiStar + lambdaComb c' * σ) / 3 * lambdaComb c') /
          FKc (qProb spinMomentW5Prob) 1 c' -
        CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ)| ≤ CStar * e_P)
    (hneg : ∀ t ∈ Ioc 0 (c' * (xiStar + lambdaComb c' * -(n : ℝ)) ^ 2 / 3),
      combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t * spinMomentW5Prob.cardyV (c' / 12) t ≤ 0)
    (hvalc : ∀ t : ℝ,
      combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') t =
        bumpFactor (rpParams 4).bumpData c' (1 / 4) N (bumpCut (rpParams 4).bumpData N c') (xOf c' t) *
          combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t)
    (hbf1 : ∀ x : ℝ, 1 ≤ bumpFactor (rpParams 4).bumpData c' (1 / 4) N (bumpCut (rpParams 4).bumpData N c') x)
    (hbfc : ∀ x : ℝ, 0 ≤ x → bumpFactor (rpParams 4).bumpData c' (1 / 4) N (bumpCut (rpParams 4).bumpData N c') x ≤
      bumpC (rpParams 4).bumpData (1 / 4))
    (hl_n_half : lambdaComb c' * (n : ℝ) ≤ xiStar / 4)
    (hl_n : lambdaComb c' * (n : ℝ) ≤ r_lim)
    (hl_Φ : lambdaComb c' * phiWKB (n + 1) ≤ r_lim)
    (hc48 : 48 ≤ c') (hcS : 12 * virasoroProblem.totalShift ≤ c') :
    IntegrableOn (fun t => bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' t *
      spinVacHC (c' / 12) t) (Ioi 0) ∧
    (∫ t in Ioi 0, bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' t *
        spinVacHC (c' / 12) t) / (π * c' * CStar * FKc 1 1 c') ≤
      (xiStar ^ 3 / (3 * π)) * windowIntegralSig N η σs + ε := by
  let d5 := (rpParams 4).bumpData
  let q5 := qProb spinMomentW5Prob
  let V_star : ℝ := xiStar ^ 3 / (3 * π)
  have hq5_pos : 0 < q5 := qProb_pos spinMomentW5Prob
  have hCS_pos : 0 < CStar := CStar_pos
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  have hcpos : 0 < c' := by linarith
  have ha2 : 2 ≤ c' / 12 := by linarith
  have hlpos := lambdaComb_pos' hcpos
  have hFK1_pos : 0 < FKc 1 1 c' := FKc_pos one_pos 1 hcpos
  have hFKq_eq : FKc q5 1 c' = q5 * FKc 1 1 c' := FKc_q_eq q5 1 c'
  let B := bumpBc d5 N η σs c'
  let h₅ := combProfile c' B
  let ĥ₅ := hankelTransform 5 h₅
  have hInt_h_HC : IntegrableOn (fun t => h₅ t * spinVacHC (c' / 12) t) (Ioi 0) := by
    refine (hk_h.const_mul ((2 * (c' / 12) + 4) * (2 * π))).mono' ?_
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    · exact ((hcont_h.mono Ioi_subset_Ici_self).mul (continuous_spinVacHC _).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    · have hHC := spinVacHC_abs_le ha2 (mem_Ioi.mp ht).le
      unfold spinVacuumD at hHC
      rw [Real.norm_eq_abs, abs_mul]
      calc |h₅ t| * |spinVacHC (c' / 12) t|
          ≤ |h₅ t| * ((2 * (c' / 12) + 4) * (2 * π * kernelK 5 (c' / 12) t)) :=
            mul_le_mul_of_nonneg_left hHC (abs_nonneg _)
        _ = (2 * (c' / 12) + 4) * (2 * π) * (|h₅ t| * kernelK 5 (c' / 12) t) := by ring
  have hg_eq : ∀ t : ℝ, bumpG spinMomentW5Prob d5 N η σs c' t = (h₅ t - ĥ₅ t) / 2 := fun t => rfl
  have hInt_g_HC : IntegrableOn (fun t => bumpG spinMomentW5Prob d5 N η σs c' t * spinVacHC (c' / 12) t) (Ioi 0) := by
    have heq : (fun t => bumpG spinMomentW5Prob d5 N η σs c' t * spinVacHC (c' / 12) t) =
        fun t => (1 / 2 : ℝ) * (h₅ t * spinVacHC (c' / 12) t) - (1 / 2 : ℝ) * (ĥ₅ t * spinVacHC (c' / 12) t) := by
      ext t; rw [hg_eq]; ring
    rw [heq]
    exact (hInt_h_HC.const_mul (1 / 2)).sub (hInt_hat.const_mul (1 / 2))
  refine ⟨hInt_g_HC, ?_⟩
  have hg_split : ∫ t in Ioi 0, bumpG spinMomentW5Prob d5 N η σs c' t * spinVacHC (c' / 12) t =
      (1 / 2 : ℝ) * (∫ t in Ioi 0, h₅ t * spinVacHC (c' / 12) t) -
        (1 / 2 : ℝ) * (∫ t in Ioi 0, ĥ₅ t * spinVacHC (c' / 12) t) := by
    have heq : (fun t => bumpG spinMomentW5Prob d5 N η σs c' t * spinVacHC (c' / 12) t) =
        fun t => (1 / 2 : ℝ) * (h₅ t * spinVacHC (c' / 12) t) - (1 / 2 : ℝ) * (ĥ₅ t * spinVacHC (c' / 12) t) := by
      ext t; rw [hg_eq]; ring
    rw [heq, integral_sub (hInt_h_HC.const_mul (1 / 2)) (hInt_hat.const_mul (1 / 2)),
      integral_const_mul, integral_const_mul]
  let t_mid : ℝ := c' * (xiStar / 2) ^ 2 / 3
  let tS : ℝ := c' * (xiStar + lambdaComb c' * -(n : ℝ)) ^ 2 / 3
  let tN : ℝ := c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3
  let tΦ : ℝ := c' * (xiStar + lambdaComb c' * phiWKB (n + 1)) ^ 2 / 3
  let tR : ℝ := c' * (xiStar + 1 / 4) ^ 2 / 3
  have hS_pos : 0 < xiStar + lambdaComb c' * -(n : ℝ) := by
    have h1 : lambdaComb c' * -(n : ℝ) = -(lambdaComb c' * (n : ℝ)) := by ring
    linarith only [hxi, hl_n_half, h1]
  have htS_nn : 0 ≤ tS := by dsimp [tS]; positivity
  have ha_n : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    linarith
  have hχ1 : xiStar ≤ chiQuantile c' ((n + 1 : ℕ) : ℝ) := (chiQuantile_spec hcpos ha_n).1
  have hχ2 : chiQuantile c' ((n + 1 : ℕ) : ℝ) ≤ xiStar + lambdaComb c' * phiWKB (n + 1) := by
    have h := (siteRadius_bounds hcpos ha_n).2
    unfold siteRadius at h
    rw [phiWKB_eq_phiQuantile (n + 1)]
    linarith
  have htN_pos : 0 < tN := by dsimp [tN]; have := lt_of_lt_of_le hxi hχ1; positivity
  have htS_Φ : tS ≤ tΦ := by
    dsimp [tS, tΦ]
    have h1 : xiStar + lambdaComb c' * -(n : ℝ) ≤ xiStar + lambdaComb c' * phiWKB (n + 1) := by
      have := mul_le_mul_of_nonneg_left (show -(n : ℝ) ≤ phiWKB (n + 1) by linarith only [hnR, hΦ0]) hlpos.le
      linarith only [this]
    exact quad_t_le hcpos.le hS_pos.le h1
  have htN_Φ : tN ≤ tΦ := by
    dsimp [tN, tΦ]
    exact quad_t_le hcpos.le (hxi.le.trans hχ1) hχ2
  have hΦ_le_R : xiStar + lambdaComb c' * phiWKB (n + 1) ≤ xiStar + 1 / 4 := by
    linarith only [hl_Φ, hr_lim_14]
  have htΦ_R : tΦ ≤ tR := by
    dsimp [tΦ, tR]
    have hy1 : 0 ≤ xiStar + lambdaComb c' * phiWKB (n + 1) := by
      have hm := mul_nonneg hlpos.le hΦ0
      linarith only [hxi, hm]
    exact quad_t_le hcpos.le hy1 hΦ_le_R
  let F : ℝ → ℝ := fun t => h₅ t * spinVacHC (c' / 12) t
  let F2 : ℝ → ℝ := fun t => if t ≤ t_mid then 0 else F t
  have hF2_int : IntegrableOn F2 (Ioi 0) :=
    (hInt_h_HC.indicator measurableSet_Iic.compl).congr_fun
      (fun t _ => by
        by_cases h : t ≤ t_mid
        · rw [Set.indicator_of_notMem (by simpa using h)]; simp only [F2, h, ↓reduceIte]
        · rw [Set.indicator_of_mem (by simpa using h)]; simp only [F2, h, ↓reduceIte]; rfl)
      measurableSet_Ioi
  have hHC_ratio_le : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4),
      |spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3))| ≤ K_HC ∧
      0 ≤ spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) :=
    fun x hx => by
      rw [hK_HC_eq]
      exact hc_ratio_bound_aux hx (hHC_c x hx)
        (hc_HC_c.trans (min_le_right _ _ |>.trans (min_le_left _ _)))
        (hc_HC_c.trans (min_le_left _ _))
  have hKV_ratio_le : ∀ x ∈ Icc (xiStar / 2) (xiStar + 1 / 4),
      |(q5 * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) / kernelK 5 (c' / 12) (c' * x ^ 2 / 3)| ≤ K_V :=
    fun x hx => by
      rw [hK_V_eq]
      exact kv_ratio_bound_aux hq5_pos hx (hK_c x hx) (hc_K_c.trans (min_le_left _ _))
  have hF_neg_lobe : ∀ t ∈ Ioc t_mid tS, F t ≤ 0 := fun t ht => by
    have ht0 : 0 < t := lt_of_le_of_lt (by dsimp [t_mid]; positivity) ht.1
    set x : ℝ := xOf c' t
    have hx_lo : xiStar / 2 ≤ x := by
      dsimp [x]; unfold xOf
      calc xiStar / 2 = √((xiStar / 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ √(3 * t / c') := Real.sqrt_le_sqrt (by rw [le_div_iff₀ hcpos]; dsimp [t_mid] at ht; linarith only [ht.1])
    have hx_hi : x ≤ xiStar + 1 / 4 := by
      dsimp [x]; unfold xOf
      have htR : t ≤ c' * (xiStar + lambdaComb c' * -(n : ℝ)) ^ 2 / 3 := ht.2
      have hm := mul_nonneg hlpos.le hnR
      have hx_S : xiStar + lambdaComb c' * -(n : ℝ) ≤ xiStar + 1 / 4 := by linarith only [hm]
      calc √(3 * t / c') ≤ √((xiStar + lambdaComb c' * -(n : ℝ)) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [div_le_iff₀ hcpos]; linarith only [htR])
        _ = xiStar + lambdaComb c' * -(n : ℝ) := Real.sqrt_sq hS_pos.le
        _ ≤ xiStar + 1 / 4 := hx_S
    have ht_eq : t = c' * x ^ 2 / 3 := by
      have hsq : x ^ 2 = 3 * t / c' := sq_xOf hcpos ht0.le
      rw [hsq, mul_div_cancel₀ _ hcpos.ne', mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
    have hHC_ge := (hHC_ratio_le x ⟨hx_lo, hx_hi⟩).2
    rw [← ht_eq] at hHC_ge
    have hV_pos : 0 < virasoroProblem.cardyV (c' / 12) t :=
      virasoroProblem.cardyV_pos (by linarith only [hcS]) ht0
    have hden_pos : 0 < 2 * π * c' * virasoroProblem.cardyV (c' / 12) t :=
      mul_pos (mul_pos (mul_pos two_pos hpi) hcpos) hV_pos
    have hHC_nn : 0 ≤ spinVacHC (c' / 12) t := by
      rw [← div_mul_cancel₀ (spinVacHC (c' / 12) t) hden_pos.ne']
      exact mul_nonneg hHC_ge hden_pos.le
    have hD_neg : combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t ≤ 0 := by
      have hK_pos : 0 < spinMomentW5Prob.cardyV (c' / 12) t :=
        spinMomentW5Prob.cardyV_pos (by rw [spinMomentW5Prob_totalShift]; linarith only [hcpos]) ht0
      exact nonpos_of_mul_nonpos_left (hneg t ⟨ht0, ht.2⟩) hK_pos
    have hval := hvalc t
    have hbf0 : 0 ≤ bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t) :=
      zero_le_one.trans (hbf1 (xOf c' t))
    have hh₅_le : h₅ t ≤ 0 := by
      dsimp [h₅, B]; rw [hval]
      exact mul_nonpos_of_nonneg_of_nonpos hbf0 hD_neg
    exact mul_nonpos_of_nonpos_of_nonneg hh₅_le hHC_nn
  have hF2_nonpos : ∀ t ∈ Ioc 0 tS, F2 t ≤ 0 := fun t ht => by
    dsimp [F2]; split_ifs with hle
    · exact le_rfl
    · exact hF_neg_lobe t ⟨lt_of_not_ge hle, ht.2⟩
  have h_split_F2 := split_integral_le htS_nn htN_pos htS_Φ htN_Φ htΦ_R hF2_int hF2_nonpos
  have htmid_lt_tS : t_mid < tS := by
    dsimp [t_mid, tS]
    have : xiStar / 2 < xiStar + lambdaComb c' * -(n : ℝ) := by
      have h1 : lambdaComb c' * -(n : ℝ) = -(lambdaComb c' * (n : ℝ)) := by ring
      linarith only [hxi, hl_n_half, h1]
    have hlt := pow_lt_pow_left₀ this (by positivity) (by norm_num : 2 ≠ 0)
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlt hcpos) (by norm_num)
  have h_Ioi_split : ∫ t in Ioi 0, F t ≤ (∫ t in Ioc 0 t_mid, |F t|) + ∫ t in Ioi 0, F2 t := by
    have h1 : IntegrableOn F (Ioc 0 t_mid) := hInt_h_HC.mono_set Ioc_subset_Ioi_self
    have h2 : IntegrableOn (fun t => F t - F2 t) (Ioi 0) := hInt_h_HC.sub hF2_int
    have h_ind_eq : ∀ t ∈ Ioi (0 : ℝ), F t - F2 t = (Ioc 0 t_mid).indicator F t := by
      intro t ht
      by_cases htm : t ≤ t_mid
      · have hmem : t ∈ Ioc 0 t_mid := ⟨mem_Ioi.mp ht, htm⟩
        simp [F2, htm, Set.indicator_of_mem hmem]
      · have hnmem : t ∉ Ioc 0 t_mid := fun h => htm h.2
        simp [F2, htm, hnmem]
    have h_diff_eq : ∫ t in Ioi 0, (F t - F2 t) = ∫ t in Ioc 0 t_mid, F t := by
      rw [setIntegral_congr_fun measurableSet_Ioi h_ind_eq,
        setIntegral_indicator measurableSet_Ioc, inter_comm, Ioc_inter_Ioi, max_eq_right le_rfl]
    have hF_split : ∫ t in Ioi 0, F t = (∫ t in Ioi 0, (F t - F2 t)) + ∫ t in Ioi 0, F2 t := by
      rw [← integral_add h2 hF2_int]; simp
    rw [hF_split, h_diff_eq]
    have hab : ∫ t in Ioc 0 t_mid, F t ≤ ∫ t in Ioc 0 t_mid, |F t| :=
      setIntegral_mono_on h1 h1.abs measurableSet_Ioc fun t _ => le_abs_self _
    linarith only [hab]
  have h_win_eq : ∫ t in tS..tΦ, F2 t = ∫ t in tS..tΦ, F t := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    have hts_lt : t_mid < t := lt_of_lt_of_le htmid_lt_tS (by rw [uIoc_of_le htS_Φ] at ht; exact ht.1.le)
    simp [F2, not_le.mpr hts_lt]
  let w_tgt : ℝ → ℝ := fun σ =>
    V_star * (tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
      (sigMod N η σs).allEpsLim σ / CStar)
  have hw_tgt_cont : Continuous w_tgt :=
    continuous_const.mul (hw_cont.div_const CStar)
  let FK_vac : ℝ := 2 * π * c' * CStar * FKc 1 1 c'
  have hFK_vac_pos : 0 < FK_vac := by positivity
  have hwin_pt : ∀ σ ∈ Icc (-(n : ℝ)) (phiWKB (n + 1)),
      F (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          (2 * c' * (xiStar + lambdaComb c' * σ) / 3 * lambdaComb c') ≤
        FK_vac * (w_tgt σ + e_tot) :=
    spinMoment_win_pt_aux N hN hcpos hcS σs n hr_lim_2 hr_lim_14
      hr_lim_Q hr_lim_R hK_HC_pos hK_V_pos hM_P_pos he_tot he_P he_Q he_R
      heP_bd heQ_bd heR_bd hM_P_ge hM₀ hl_n hl_Φ hHC_c hK_c
      (hc_HC_c.trans (min_le_right _ _ |>.trans (min_le_right _ _)))
      (hc_K_c.trans (min_le_right _ _)) hQ_uc hR_uc hR_star_eq hHC_ratio_le hKV_ratio_le hpart1
  have hwin_int : ∫ t in tS..tΦ, F t ≤ FK_vac * ((∫ σ in -(n : ℝ)..phiWKB (n + 1), w_tgt σ) + e_tot * (phiWKB (n + 1) + n)) := by
    have hSΦ : -(n : ℝ) ≤ phiWKB (n + 1) := by linarith only [hnR, hΦ0]
    exact window_part_le hcpos.le (hcont_h.mul (continuous_spinVacHC _).continuousOn) hw_tgt_cont hSΦ hwin_pt
  have hw_int_bd : ∫ σ in -(n : ℝ)..phiWKB (n + 1), w_tgt σ ≤ V_star * windowIntegralSig N η σs + ε / 6 := by
    have h_eq : ∫ σ in -(n : ℝ)..phiWKB (n + 1), w_tgt σ =
        (V_star / CStar) * ∫ σ in -(n : ℝ)..phiWKB (n + 1),
          tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim (sigMod N η σs).allEpsLim σ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun σ _ => by dsimp [w_tgt]; ring
    rw [h_eq]
    have hvc : 0 ≤ V_star / CStar := by positivity
    have h1 := mul_le_mul_of_nonneg_left hn4 hvc
    have h2 : (V_star / CStar) * (CStar * windowIntegralSig N η σs + ε_win / 4) =
        V_star * windowIntegralSig N η σs + (V_star / CStar) * (ε_win / 4) := by
      field_simp [hCS_pos.ne']
    have h3 : (V_star / CStar) * (ε_win / 4) ≤ (V_star / CStar) * ε_win :=
      mul_le_mul_of_nonneg_left (by linarith only [hε_win]) hvc
    linarith only [h1, h2, h3, hvc_eps]
  have hwin_all : (∫ t in tS..tΦ, F2 t) / FK_vac ≤ V_star * windowIntegralSig N η σs + ε / 3 := by
    rw [h_win_eq, div_le_iff₀ hFK_vac_pos]
    calc ∫ t in tS..tΦ, F t
        ≤ FK_vac * ((∫ σ in -(n : ℝ)..phiWKB (n + 1), w_tgt σ) + e_tot * (phiWKB (n + 1) + n)) := hwin_int
      _ ≤ FK_vac * ((V_star * windowIntegralSig N η σs + ε / 6) + ε / 6) :=
          mul_le_mul_of_nonneg_left (add_le_add hw_int_bd he_Δ) hFK_vac_pos.le
      _ = (V_star * windowIntegralSig N η σs + ε / 3) * FK_vac := by ring
  obtain ⟨hTc_band, hTc_far⟩ := hTc (fun t => bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') (xOf c' t))
    fun t => ⟨zero_le_one.trans (hbf1 (xOf c' t)), hbfc (xOf c' t) (xOf_nonneg c' t)⟩
  have hband_bd : (∫ t in Icc tN tR, |F2 t|) / FK_vac ≤ ε / 6 := by
    have hF2_le : ∫ t in Icc tN tR, |F2 t| ≤ ∫ t in Icc tN tR, |F t| :=
      setIntegral_mono_on (hF2_int.mono_set (fun _ (ht : _ ∈ Icc tN tR) => lt_of_lt_of_le htN_pos ht.1) |>.abs)
        ((hInt_h_HC.mono_set (fun t (ht : t ∈ Icc tN tR) => lt_of_lt_of_le htN_pos ht.1)).abs) measurableSet_Icc
        fun t _ => by dsimp [F2]; split_ifs <;> simp
    have h_hc_band : ∀ t ∈ Icc tN tR,
        |spinVacHC (c' / 12) t| ≤ (2 * π * c' * K_HC * K_V / q5) * spinMomentW5Prob.cardyV (c' / 12) t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le htN_pos ht.1
      set x : ℝ := xOf c' t
      have hx_lo : xiStar / 2 ≤ x := by
        dsimp [x]; unfold xOf
        have : xiStar / 2 ≤ chiQuantile c' ((n + 1 : ℕ) : ℝ) := by linarith only [hχ1, hxi]
        calc xiStar / 2 ≤ chiQuantile c' ((n + 1 : ℕ) : ℝ) := this
          _ = √(chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2) := (Real.sqrt_sq (by linarith only [hxi, hχ1])).symm
          _ ≤ √(3 * t / c') := Real.sqrt_le_sqrt (by rw [le_div_iff₀ hcpos]; dsimp [tN] at ht; linarith only [ht.1])
      have hx_hi : x ≤ xiStar + 1 / 4 := by
        dsimp [x]; unfold xOf
        calc √(3 * t / c') ≤ √((xiStar + 1 / 4) ^ 2) :=
              Real.sqrt_le_sqrt (by rw [div_le_iff₀ hcpos]; dsimp [tR] at ht; linarith only [ht.2])
          _ = xiStar + 1 / 4 := Real.sqrt_sq (by linarith only [hxi])
      have ht_eq : t = c' * x ^ 2 / 3 := by
        have hsq : x ^ 2 = 3 * t / c' := sq_xOf hcpos ht0.le
        rw [hsq, mul_div_cancel₀ _ hcpos.ne', mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
      have hV_pos : 0 < virasoroProblem.cardyV (c' / 12) t :=
        virasoroProblem.cardyV_pos (by linarith only [hcS]) ht0
      have hK5_pos : 0 < kernelK 5 (c' / 12) t := by
        rw [← spinMomentW5Prob_cardyV]
        exact spinMomentW5Prob.cardyV_pos (by rw [spinMomentW5Prob_totalShift]; linarith only [hcpos]) ht0
      have hQ_bd := (hHC_ratio_le x ⟨hx_lo, hx_hi⟩).1
      have hR_bd := hKV_ratio_le x ⟨hx_lo, hx_hi⟩
      rw [← ht_eq] at hQ_bd hR_bd
      have hid : spinVacHC (c' / 12) t =
          (2 * π * c' / q5) *
            (spinVacHC (c' / 12) t / (2 * π * c' * virasoroProblem.cardyV (c' / 12) t)) *
            ((q5 * virasoroProblem.cardyV (c' / 12) t) / kernelK 5 (c' / 12) t) *
            kernelK 5 (c' / 12) t := by
        field_simp [hpi.ne', hcpos.ne', hq5_pos.ne', hV_pos.ne', hK5_pos.ne']
      rw [hid, spinMomentW5Prob_cardyV, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by positivity : 0 < 2 * π * c' / q5), abs_of_pos hK5_pos]
      calc (2 * π * c' / q5) *
            |spinVacHC (c' / 12) t / (2 * π * c' * virasoroProblem.cardyV (c' / 12) t)| *
            |(q5 * virasoroProblem.cardyV (c' / 12) t) / kernelK 5 (c' / 12) t| * kernelK 5 (c' / 12) t
          ≤ (2 * π * c' / q5) * K_HC * K_V * kernelK 5 (c' / 12) t := by
            refine mul_le_mul_of_nonneg_right ?_ hK5_pos.le
            refine mul_le_mul ?_ hR_bd (abs_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left hQ_bd (by positivity)
        _ = (2 * π * c' * K_HC * K_V / q5) * kernelK 5 (c' / 12) t := by ring
    have hF_bd := spinMoment_abs_setIntegral_le N hN (by positivity) σs measurableSet_Icc
      (fun _ ht => lt_of_lt_of_le htN_pos ht.1) hk_h hInt_h_HC hvalc hbf1 h_hc_band hTc_band
    rw [div_le_iff₀ hFK_vac_pos]
    have hid_band : (2 * π * c' * K_HC * K_V / q5) * (FKc q5 1 c' * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ))) =
        (C_band * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ))) * FK_vac := by
      dsimp [FK_vac]; rw [hC_band_eq, hFKq_eq]
      field_simp [hq5_pos.ne', hCS_pos.ne']
    have h6n : C_band * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ε / 6 := by
      linarith only [hn3, hwin_le, hε]
    calc ∫ t in Icc tN tR, |F2 t| ≤ ∫ t in Icc tN tR, |F t| := hF2_le
      _ ≤ (C_band * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ))) * FK_vac := hF_bd.trans_eq hid_band
      _ ≤ (ε / 6) * FK_vac := mul_le_mul_of_nonneg_right h6n hFK_vac_pos.le
  have hfar_bd : (∫ t in Ici tR, |F2 t|) / FK_vac ≤ ε / 6 := by
    have htR_pos : 0 < tR := by dsimp [tR]; positivity
    have hF2_le : ∫ t in Ici tR, |F2 t| ≤ ∫ t in Ici tR, |F t| :=
      setIntegral_mono_on (hF2_int.mono_set (fun _ ht => lt_of_lt_of_le htR_pos ht) |>.abs)
        ((hInt_h_HC.mono_set (fun t ht => lt_of_lt_of_le htR_pos ht)).abs) measurableSet_Ici
        fun t _ => by dsimp [F2]; split_ifs <;> simp
    have h_hc_far : ∀ t ∈ Ici tR, |spinVacHC (c' / 12) t| ≤ (4 * c') * spinMomentW5Prob.cardyV (c' / 12) t := by
      intro t ht
      have ht0_gt : 0 < t := lt_of_lt_of_le htR_pos ht
      have hHC := spinVacHC_abs_le ha2 ht0_gt.le
      unfold spinVacuumD at hHC
      have hc12 : (2 * (c' / 12) + 4) * (2 * π) ≤ 4 * c' := by
        have h1 : 2 * (c' / 12) + 4 ≤ c' / 2 := by linarith only [hc48]
        nlinarith only [h1, Real.pi_lt_four, hcpos]
      have hK_nn : 0 ≤ kernelK 5 (c' / 12) t := by
        rw [← spinMomentW5Prob_cardyV]
        exact (spinMomentW5Prob.cardyV_pos (by rw [spinMomentW5Prob_totalShift]; linarith only [hcpos]) ht0_gt).le
      rw [spinMomentW5Prob_cardyV]
      calc |spinVacHC (c' / 12) t| ≤ ((2 * (c' / 12) + 4) * (2 * π)) * kernelK 5 (c' / 12) t := by linarith only [hHC]
        _ ≤ (4 * c') * kernelK 5 (c' / 12) t := mul_le_mul_of_nonneg_right hc12 hK_nn
    have hF_bd := spinMoment_abs_setIntegral_le N hN (by positivity) σs measurableSet_Ici
      (fun _ ht => lt_of_lt_of_le htR_pos ht) hk_h hInt_h_HC hvalc hbf1 h_hc_far hTc_far
    calc (∫ t in Ici tR, |F2 t|) / FK_vac
        ≤ ((4 * c') * (C_far * √c')) / FK_vac :=
          div_le_div_of_nonneg_right (hF2_le.trans hF_bd) hFK_vac_pos.le
      _ = (4 * C_far * √c') / (2 * π * CStar * FKc 1 1 c') := by
          dsimp [FK_vac]; field_simp [hcpos.ne', hpi.ne', hCS_pos.ne', hFK1_pos.ne']
      _ ≤ ε / 6 := hfar_lim_c
  have hlobe_bd : (∫ t in Ioc 0 t_mid, |F t|) / FK_vac ≤ ε / 6 := by
    have h_eq_FK : (∫ t in Ioc 0 t_mid, |F t|) / FK_vac =
        ((∫ t in Ioc 0 t_mid, |F t|) / (c' * FKc 1 1 c')) / (2 * π * CStar) := by
      dsimp [FK_vac]; field_simp [hcpos.ne', hpi.ne', hCS_pos.ne', hFK1_pos.ne']
    have hl_le : (∫ t in Ioc 0 t_mid, |F t|) / (c' * FKc 1 1 c') ≤ (ε / 6) * (2 * π * CStar) := by
      simpa [F, t_mid, h₅, B, d5] using hlobe_c
    rw [h_eq_FK, div_le_iff₀ (by positivity)]
    exact hl_le
  have hhat_bd : |(∫ t in Ioi 0, ĥ₅ t * spinVacHC (c' / 12) t) / (2 * (π * c' * CStar * FKc 1 1 c'))| ≤ ε / 6 := by
    have h_eq : |(∫ t in Ioi 0, ĥ₅ t * spinVacHC (c' / 12) t) / (2 * (π * c' * CStar * FKc 1 1 c'))| =
        (|∫ t in Ioi 0, ĥ₅ t * spinVacHC (c' / 12) t| / 2) / (π * c' * CStar * FKc 1 1 c') := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * (π * c' * CStar * FKc 1 1 c'))]; ring
    rw [h_eq]
    calc (|∫ t in Ioi 0, ĥ₅ t * spinVacHC (c' / 12) t| / 2) / (π * c' * CStar * FKc 1 1 c')
        ≤ (C_hat * c' / 2) / (π * c' * CStar * FKc 1 1 c') :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hbd_hat zero_le_two) (by positivity)
      _ ≤ ε / 6 := hhat_lim_c
  have h_half_split : (∫ t in Ioi 0, bumpG spinMomentW5Prob d5 N η σs c' t * spinVacHC (c' / 12) t) /
        (π * c' * CStar * FKc 1 1 c') =
      (∫ t in Ioi 0, F t) / FK_vac -
        (∫ t in Ioi 0, ĥ₅ t * spinVacHC (c' / 12) t) / (2 * (π * c' * CStar * FKc 1 1 c')) := by
    rw [hg_split]
    dsimp [F, FK_vac]
    ring
  have hF_all : (∫ t in Ioi 0, F t) / FK_vac ≤ V_star * windowIntegralSig N η σs + 5 * ε / 6 := by
    have hsum_F := h_Ioi_split.trans (add_le_add_right h_split_F2 (∫ t in Ioc 0 t_mid, |F t|))
    have h1 := div_le_div_of_nonneg_right hsum_F hFK_vac_pos.le
    have hsum_div : ((∫ t in Ioc 0 t_mid, |F t|) +
        (((∫ t in tS..tΦ, F2 t) + ∫ t in Icc tN tR, |F2 t|) + ∫ t in Ici tR, |F2 t|)) / FK_vac =
        (∫ t in Ioc 0 t_mid, |F t|) / FK_vac + (∫ t in tS..tΦ, F2 t) / FK_vac +
          (∫ t in Icc tN tR, |F2 t|) / FK_vac + (∫ t in Ici tR, |F2 t|) / FK_vac := by ring
    rw [hsum_div] at h1
    linarith only [h1, hlobe_bd, hwin_all, hband_bd, hfar_bd]
  rw [h_half_split]
  linarith only [hF_all, (abs_le.mp hhat_bd).1]

/-- Full vacuum-source upper limit (`sd:spinmoment-ref-limit`):
`limsup (π c' C_* FKc 1 1 c')⁻¹ ∫₀^∞ g₅(t) H_C(t) dt ≤ (ξ_*³/(3π)) windowIntegralSig`. -/

theorem spinMoment_vac_source_limsup_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c' in atTop,
      IntegrableOn (fun t => bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' t *
        spinVacHC (c' / 12) t) (Ioi 0) ∧
      (∫ t in Ioi 0, bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' t *
          spinVacHC (c' / 12) t) / (π * c' * CStar * FKc 1 1 c') ≤
        (xiStar ^ 3 / (3 * π)) * windowIntegralSig N η σs + ε := by
  intro ε hε
  let d5 := (rpParams 4).bumpData
  let q5 := qProb spinMomentW5Prob
  have hq5_pos : 0 < q5 := qProb_pos spinMomentW5Prob
  have hCS_pos : 0 < CStar := CStar_pos
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  obtain ⟨C_hat, hC_hat, hhat⟩ := bumpG_hat_vac_source_le N hN hη0.le hη1 σs
  obtain ⟨M_σ, hM_σ⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  have hbumpC_nn : 0 ≤ bumpC d5 (1 / 4) := by
    obtain ⟨c0, hc0⟩ := ((bumpFactor_one_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl).and
      (bumpFactor_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl)).exists
    exact (zero_le_one.trans (hc0.1 1 1 0)).trans (hc0.2 1 1 0 le_rfl)
  obtain ⟨N₂, C_T, C_far, hCT, hCf, hT⟩ := lemma_T_sig1_prob_mul spinMomentW5Prob (r₀ := 1 / 4)
    (by norm_num) N hN hη0.le hη1 σs M_σ hM_σ (bumpC d5 (1 / 4)) hbumpC_nn
  obtain ⟨C_HC0, hCHC0, hHC_bd⟩ := spinVacHC_div_cardy_bound (x₀ := xiStar / 2)
    (X := xiStar + 1 / 4) (half_pos hxi) (by linarith)
  obtain ⟨C_K0, hCK0, hK_bd⟩ := kernelK5_div_virasoro_bound (x₀ := xiStar / 2)
    (X := xiStar + 1 / 4) (half_pos hxi) (by linarith)
  let V_star : ℝ := xiStar ^ 3 / (3 * π)
  have hV_star_nn : 0 ≤ V_star := by dsimp [V_star]; positivity
  let K_HC : ℝ := (xiStar + 1 / 4) ^ 3 / (3 * π) + 1
  let K_V : ℝ := q5 * ((1 - Real.exp (-4 * π * (xiStar + 1 / 4))) ^ 2 / (2 * (xiStar / 2)) ^ 4) + 1
  let C_band : ℝ := K_HC * K_V / CStar
  have hK_HC_pos : 0 < K_HC := by dsimp [K_HC]; positivity
  have hK_V_pos : 0 < K_V := by dsimp [K_V]; positivity
  have hC_band_nn : 0 ≤ C_band := by dsimp [C_band]; positivity
  let ε_win : ℝ := ε / (6 * (V_star / CStar + 1))
  have hε_win : 0 < ε_win := by dsimp [ε_win]; positivity
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (eventually_n_choice_sig N₂ (C_T := 6 * C_band * C_T)
    (ε := ε_win) hε_win N hN η σs).exists
  have hn1' : max 4 N₂ ≤ n := hn1
  have hn_pos : 1 ≤ n := by have := (le_max_left 4 N₂).trans hn1'; omega
  have hΦ0 : 0 ≤ phiWKB (n + 1) := phiWKB_nonneg (by omega)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hw_cont := continuous_windowLimit_sig N hN η σs
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -(n : ℝ)) (b := phiWKB (n + 1))).exists_bound_of_continuousOn
    hw_cont.continuousOn
  have hM₀_nn : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0 ⟨by linarith, hΦ0⟩)
  let M_P : ℝ := M₀ / CStar + 1
  have hM_P_pos : 0 < M_P := by dsimp [M_P]; positivity
  let Δσ : ℝ := phiWKB (n + 1) + n + 1
  have hΔσ_pos : 0 < Δσ := by dsimp [Δσ]; positivity
  let e_tot : ℝ := ε / (6 * Δσ)
  have he_tot : 0 < e_tot := by dsimp [e_tot]; positivity
  let e_P : ℝ := e_tot / (3 * K_HC * K_V + 1)
  let e_Q : ℝ := e_tot / (3 * M_P * K_V + 1)
  let e_R : ℝ := e_tot / (3 * M_P * V_star + 1)
  have he_P : 0 < e_P := by dsimp [e_P]; positivity
  have he_Q : 0 < e_Q := by dsimp [e_Q]; positivity
  have he_R : 0 < e_R := by dsimp [e_R]; positivity
  have hcont_Q : ContinuousOn (fun x : ℝ => x ^ 3 / (3 * π)) (Icc (xiStar / 2) (xiStar + 1 / 4)) := by
    fun_prop
  have hcont_R : ContinuousOn (fun x : ℝ => q5 * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4))
      (Icc (xiStar / 2) (xiStar + 1 / 4)) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div ?_ ?_ ?_)
    · fun_prop
    · fun_prop
    · intro x hx; have hx0 : 0 < x := lt_of_lt_of_le (half_pos hxi) hx.1; positivity
  obtain ⟨δ_Q, hδ_Q, hQ_uc⟩ := Metric.continuousOn_iff.mp hcont_Q xiStar
    ⟨by linarith, by linarith⟩ (e_Q / 2) (half_pos he_Q)
  obtain ⟨δ_R, hδ_R, hR_uc⟩ := Metric.continuousOn_iff.mp hcont_R xiStar
    ⟨by linarith, by linarith⟩ (e_R / 2) (half_pos he_R)
  have hR_star_eq : q5 * ((1 - Real.exp (-4 * π * xiStar)) ^ 2 / (2 * xiStar) ^ 4) = 1 := by
    dsimp [q5]; unfold qProb
    rw [spinMomentW5Prob_w, spinMomentW5Prob_nullPoly]
    have h1m : 1 - Real.exp (-4 * π * xiStar) ≠ 0 := by
      have harg : -4 * π * xiStar < 0 := by
        have : 0 < 4 * π * xiStar := by positivity
        linarith
      have hlt : Real.exp (-4 * π * xiStar) < 1 := Real.exp_lt_one_iff.mpr harg
      linarith
    have h1m' : -(4 * π * xiStar) = -4 * π * xiStar := by ring
    rw [h1m', show (5 - 1 : ℕ) = 4 by rfl, mul_one, div_mul_div_cancel₀ (pow_ne_zero 2 h1m),
      div_self (pow_ne_zero 4 (by positivity : 2 * xiStar ≠ 0))]
  have hlobe_le := (lobe_left_exp_decay N hN hη0 hη1 σs).eventually_le_const
    (show (0 : ℝ) < (ε / 6) * (2 * π * CStar) by positivity)
  let r_lim : ℝ := min (xiStar / 2) (min (1 / 4) (min (δ_Q / 2) (δ_R / 2)))
  have hr_lim : 0 < r_lim :=
    lt_min (half_pos hxi) (lt_min (by norm_num) (lt_min (half_pos hδ_Q) (half_pos hδ_R)))
  have hr_lim_Q : r_lim < δ_Q := by
    have : r_lim ≤ δ_Q / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hr_lim_R : r_lim < δ_R := by
    have : r_lim ≤ δ_R / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hC_hat_lim : ∀ᶠ c' in atTop, (C_hat * c' / 2) / (π * c' * CStar * FKc 1 1 c') ≤ ε / 6 := by
    filter_upwards [FKc_ge_mul_sqrt_of_pos one_pos (3 * (C_hat + 1) / (π * CStar * ε)),
      eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)] with c' hFK hcpos hc1
    have hsc : 1 ≤ √c' := by simpa using Real.sqrt_le_sqrt hc1
    have hFK_pos : 0 < FKc 1 1 c' := FKc_pos one_pos 1 hcpos
    have hden_ge : (3 * (C_hat + 1) / (π * CStar * ε)) * 1 ≤ FKc 1 1 c' :=
      le_trans (mul_le_mul_of_nonneg_left hsc (by positivity)) hFK
    have hc_eq : (C_hat * c' / 2) / (π * c' * CStar * FKc 1 1 c') =
        C_hat / (2 * π * CStar * FKc 1 1 c') := by
      field_simp [hcpos.ne', hpi.ne', hCS_pos.ne', hFK_pos.ne']
    rw [hc_eq, div_le_iff₀ (by positivity)]
    have h1 : C_hat * 6 ≤ (2 * π * CStar * (3 * (C_hat + 1) / (π * CStar * ε))) * ε := by
      field_simp [hpi.ne', hCS_pos.ne', hε.ne']; linarith
    have h2 : (2 * π * CStar * (3 * (C_hat + 1) / (π * CStar * ε))) * ε ≤
        (ε / 6) * (2 * π * CStar * FKc 1 1 c') * 6 := by
      have : 3 * (C_hat + 1) / (π * CStar * ε) ≤ FKc 1 1 c' := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * π * CStar * ε)]
    linarith
  have hfar_lim : ∀ᶠ c' in atTop,
      (4 * C_far * √c') / (2 * π * CStar * FKc 1 1 c') ≤ ε / 6 := by
    filter_upwards [FKc_ge_mul_sqrt_of_pos one_pos (12 * (C_far + 1) / (π * CStar * ε)),
      eventually_gt_atTop (0 : ℝ)] with c' hFK hcpos
    have hFK_pos : 0 < FKc 1 1 c' := FKc_pos one_pos 1 hcpos
    rw [div_le_iff₀ (by positivity)]
    have h1 : (4 * C_far) * √c' ≤
        (ε / 6) * (2 * π * CStar * ((12 * (C_far + 1) / (π * CStar * ε)) * √c')) := by
      field_simp [hpi.ne', hCS_pos.ne', hε.ne']
      nlinarith [Real.sqrt_nonneg c']
    have h2 : (ε / 6) * (2 * π * CStar * ((12 * (C_far + 1) / (π * CStar * ε)) * √c')) ≤
        (ε / 6) * (2 * π * CStar * FKc 1 1 c') := by gcongr
    linarith
  have hc_K0 : ∀ᶠ c' in atTop, C_K0 / c' ≤ min (1 / 2) (e_R / 2) :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually_le_const (lt_min (by norm_num) (half_pos he_R))
  have hc_HC0 : ∀ᶠ c' in atTop, C_HC0 / c' ≤ min ((xiStar / 2) ^ 3 / (6 * π)) (min (1 / 2) (e_Q / 2)) :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually_le_const
      (lt_min (by positivity) (lt_min (by norm_num) (half_pos he_Q)))
  filter_upwards [hhat, hT n hn1', hHC_bd, hK_bd, hlobe_le, hC_hat_lim, hfar_lim,
    hc_K0, hc_HC0,
    bump_part1 spinMomentW5Prob d5 N hN hη0.le hη1 σs (S := n) hnR n (mul_pos hCS_pos he_P),
    sig_lobe_nonpos spinMomentW5Prob N (η := η) σs hn2,
    combProfile_bumped_eq d5,
    bumpFactor_one_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpSig_phaseHyp d5 N hN hη0.le hη1 σs,
    bumpSig_k7W spinMomentW5Prob d5 N hN hη0.le hη1 σs,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    lambda_mul_le (n : ℝ) (show (0 : ℝ) < xiStar / 4 by positivity),
    lambda_mul_le (n : ℝ) hr_lim,
    lambda_mul_le (phiWKB (n + 1)) hr_lim,
    eventually_ge_atTop (48 : ℝ),
    eventually_ge_atTop (12 * virasoroProblem.totalShift)]
    with c' ⟨hInt_hat, hbd_hat⟩ hTc hHC_c hK_c hlobe_c hhat_lim_c hfar_lim_c
      hc_K_c hc_HC_c hpart1 hneg hvalc hbf1 hbfc hph hk7 hin hl_n_half hl_n hl_Φ hc48 hcS
  have heP_bd : e_P * (K_HC * K_V) ≤ e_tot / 3 := by
    dsimp [e_P]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith only [mul_nonneg hK_HC_pos.le hK_V_pos.le, he_tot]
  have heQ_bd : e_Q * (M_P * K_V) ≤ e_tot / 3 := by
    dsimp [e_Q]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith only [mul_nonneg hM_P_pos.le hK_V_pos.le, he_tot]
  have heR_bd : (M_P * V_star) * e_R ≤ e_tot / 3 := by
    dsimp [e_R]; rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith only [mul_nonneg hM_P_pos.le hV_star_nn, he_tot]
  have hM_P_ge : M₀ / CStar ≤ M_P := by dsimp [M_P]; linarith only
  have he_Δ : e_tot * (phiWKB (n + 1) + n) ≤ ε / 6 := by
    dsimp [e_tot, Δσ]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith only [hε, hΦ0, hnR]
  have hvc_nn : 0 ≤ V_star / CStar := by positivity
  have hwin_le : ε_win ≤ ε / 6 := by
    dsimp [ε_win]; exact div_le_div_of_nonneg_left hε.le (by positivity) (by linarith only [hvc_nn])
  have hvc_eps : (V_star / CStar) * ε_win ≤ ε / 6 := by
    dsimp [ε_win]; rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith only [hvc_nn, hε]
  have hcpos : 0 < c' := by linarith
  obtain ⟨hfN, hA, -⟩ := hph (bumpCut d5 N c') (le_bumpCut d5 N c')
  have hI : InnerCombHyp c' (bumpBc d5 N η σs c') := hin (bumpCut d5 N c') _ _ hfN hA
  obtain ⟨C₀, -, hd1, -, -⟩ := hk7 (bumpCut d5 N c') (le_bumpCut d5 N c')
  have hcont_h : ContinuousOn (combProfile c' (bumpBc d5 N η σs c')) (Ici 0) :=
    hI.continuousOn_combProfile hcpos
  have hk_h : KernelIntegrable 5 (c' / 12) (combProfile c' (bumpBc d5 N η σs c')) :=
    kernelIntegrable_of_decay (by norm_num) hcpos hcont_h hd1
  exact spinMoment_vac_source_at_c' N hN hε σs n hnR hΦ0 hK_HC_pos hK_V_pos hC_band_nn
    hM_P_pos hM_P_ge he_tot he_P he_Q he_R heP_bd heQ_bd heR_bd he_Δ hε_win hwin_le hvc_eps
    (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _)) hr_lim_Q hr_lim_R
    hw_cont hM₀ hn3 hn4 hQ_uc hR_uc hR_star_eq rfl rfl rfl hcont_h hk_h
    hInt_hat hbd_hat hTc hHC_c hK_c hlobe_c hhat_lim_c hfar_lim_c hc_K_c hc_HC_c
    (fun σ hσ => hpart1 (bumpCut d5 N c') (le_bumpCut d5 N c') σ hσ)
    hneg (fun t => hvalc N (bumpCut d5 N c') σs (designWidth1 c' η) hN (le_bumpCut d5 N c') t)
    (fun x => hbf1 N (bumpCut d5 N c') x) (fun x hx => hbfc N (bumpCut d5 N c') x hx)
    hl_n_half hl_n hl_Φ hc48 hcS

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinMoment_vac_source_limsup_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinMoment_vac_source_limsup_le

end FormalResearch.ModularBootstrap.Spin
