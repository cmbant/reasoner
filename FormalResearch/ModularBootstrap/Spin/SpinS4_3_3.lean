/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_3_3_Cap

/-!
# Section 3.1 (`s4:3.3`): Fixed Airy-Window Tightness of the Negative Weighted Mass

This module proves `SpinS4_3_3` (`spinning_s4.tex`, Theorem 3.3 / `s4:3.3`):
for every fixed `C_x > 0`, there exist constants `C, c_exp, R₀ > 0` such that for all `R ≥ R₀`
and all sufficiently large `n' = c - 1` (after fixing `R`), the negative weighted mass inside
`b_△ ≤ ξ_* - R ε` inside the gap disc is at most `C exp(-c_exp R^{3/2})`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

private lemma spinS4_3_3_tail_cap {a R : ℝ} (ha2 : 2 < a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (hM2 : spinM2 a Φ = 1) {N : ℕ} (_hR : 0 ≤ R)
    (hN_ge : R ^ (3 / 2 : ℝ) ≤ (N : ℝ))
    (hdiff_i : Integrable (fun p : ℝ × ℝ =>
      |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2))
    {E_cap : Set (ℝ × ℝ)}
    (hcap_sub_r : E_cap ⊆ {q : ℝ × ℝ | xiStar / 2 ≤ q.1 ∧ xiStar / 2 ≤ q.2}) :
    ∫ q in E_cap, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 ≤
      3 * Real.exp (-2 * π * xiStar * R ^ (3 / 2 : ℝ)) := by
  let r : ℝ := xiStar / 2
  have hr_pos : 0 < r := half_pos xiStar_pos
  obtain ⟨h0N_int, h0N_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr_pos hΦ 0 N
  obtain ⟨hN0_int, hN0_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr_pos hΦ N 0
  obtain ⟨hNN_int, hNN_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr_pos hΦ N N
  have h0N_e : (fun p : ℝ × ℝ => |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ 0 * p.1) (spinLambda a ^ N * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by ext p; rw [pow_zero, one_mul]
  have hN0_e : (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ 0 * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by ext p; rw [pow_zero, one_mul]
  rw [← h0N_e] at h0N_int h0N_bd
  rw [← hN0_e] at hN0_int hN0_bd
  let S_r : Set (ℝ × ℝ) := {q : ℝ × ℝ | r ≤ q.1 ∧ r ≤ q.2}
  have hS_meas : MeasurableSet S_r := by
    have : S_r = Set.Ici r ×ˢ Set.Ici r := rfl
    rw [this]; exact measurableSet_Ici.prod measurableSet_Ici
  have hsub_int : ∫ q in E_cap, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| *
      spinWc a q.1 * spinWc a q.2 ≤
      ∫ q in S_r, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| *
      spinWc a q.1 * spinWc a q.2 :=
    setIntegral_mono_set hdiff_i.integrableOn
      (Eventually.of_forall fun p => mul_nonneg (mul_nonneg (abs_nonneg _)
        (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _)) (Eventually.of_forall hcap_sub_r)
  have hpt_S : ∀ p ∈ S_r,
      |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤
        |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
        |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
        |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 := by
    intro p _
    have hw1 := spinWc_nonneg ha2.le p.1
    have hw2 := spinWc_nonneg ha2.le p.2
    rw [spinG_sub_spinTruncInv ha2]
    have hab1 := abs_add_le (spinG a Φ p.1 (spinLambda a ^ N * p.2)) (spinG a Φ (spinLambda a ^ N * p.1) p.2)
    have hab2 := abs_sub_le (spinG a Φ p.1 (spinLambda a ^ N * p.2) + spinG a Φ (spinLambda a ^ N * p.1) p.2) 0
      (spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2))
    rw [sub_zero, zero_sub, abs_neg] at hab2
    have hab : |spinG a Φ p.1 (spinLambda a ^ N * p.2) +
        spinG a Φ (spinLambda a ^ N * p.1) p.2 -
        spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| ≤
        |spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
          |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
          |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| := by
      linarith only [hab1, hab2]
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hw1) hw2
    rwa [add_mul, add_mul, add_mul, add_mul] at h1
  have h0N_S : Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2)
      (volume.restrict S_r) := h0N_int.integrableOn
  have hN0_S : Integrable (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2)
      (volume.restrict S_r) := hN0_int.integrableOn
  have hNN_S : Integrable (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
      spinWc a p.1 * spinWc a p.2) (volume.restrict S_r) := hNN_int.integrableOn
  let fsum : ℝ × ℝ → ℝ := fun p =>
    |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
    |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
    |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2
  have hsum_S : Integrable fsum (volume.restrict S_r) := (h0N_S.add hN0_S).add hNN_S
  have hmono := setIntegral_mono_on hdiff_i.integrableOn hsum_S hS_meas hpt_S
  have hadd1 := integral_add (h0N_S.add hN0_S) hNN_S
  have hadd2 := integral_add h0N_S hN0_S
  have hS_def : S_r = {p : ℝ × ℝ | r ≤ p.1 ∧ r ≤ p.2} := rfl
  have h0N_b1 : ∫ p in S_r, |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 ≤
      Real.exp (-4 * π * r * (N : ℝ)) := by
    rw [hS_def]; refine h0N_bd.trans_eq ?_; rw [hM2, mul_one, zero_add]
  have hN0_b1 : ∫ p in S_r, |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 ≤
      Real.exp (-4 * π * r * (N : ℝ)) := by
    rw [hS_def]; refine hN0_bd.trans_eq ?_; rw [hM2, mul_one, add_zero]
  have hNN_b1 : ∫ p in S_r, |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
      spinWc a p.1 * spinWc a p.2 ≤
      Real.exp (-4 * π * r * ((N + N : ℕ) : ℝ)) := by
    rw [hS_def]; refine hNN_bd.trans_eq ?_; rw [hM2, mul_one]
  have hexp_NN : Real.exp (-4 * π * r * ((N + N : ℕ) : ℝ)) ≤ Real.exp (-4 * π * r * (N : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    push_cast
    rw [show -4 * π * r * ((N : ℝ) + (N : ℝ)) = -4 * π * r * (N : ℝ) - 4 * π * r * (N : ℝ) by ring,
      sub_le_self_iff]
    positivity
  have h4r : -4 * π * r * (N : ℝ) ≤ -2 * π * xiStar * R ^ (3 / 2 : ℝ) := by
    dsimp [r]
    rw [show -4 * π * (xiStar / 2) * (N : ℝ) = -(2 * π * xiStar * (N : ℝ)) by ring,
      show -2 * π * xiStar * R ^ (3 / 2 : ℝ) = -(2 * π * xiStar * R ^ (3 / 2 : ℝ)) by ring,
      neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hN_ge (by positivity [Real.pi_pos, xiStar_pos])
  have hexp_R : Real.exp (-4 * π * r * (N : ℝ)) ≤ Real.exp (-2 * π * xiStar * R ^ (3 / 2 : ℝ)) :=
    Real.exp_le_exp.mpr h4r
  calc ∫ q in E_cap, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
      ≤ ∫ q in S_r, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := hsub_int
    _ ≤ ∫ p in S_r, fsum p := hmono
    _ = (∫ p in S_r, |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) +
        (∫ p in S_r, |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) +
        (∫ p in S_r, |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
          spinWc a p.1 * spinWc a p.2) := by
        rw [← hadd2]; exact hadd1
    _ ≤ Real.exp (-4 * π * r * (N : ℝ)) + Real.exp (-4 * π * r * (N : ℝ)) +
        Real.exp (-4 * π * r * (N : ℝ)) :=
        add_le_add (add_le_add h0N_b1 hN0_b1) (hNN_b1.trans hexp_NN)
    _ = 3 * Real.exp (-4 * π * r * (N : ℝ)) := by ring
    _ ≤ 3 * Real.exp (-2 * π * xiStar * R ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp_R (by norm_num)

private lemma spinGamma_ge_three_fourths {a : ℝ} (ha : 64 ≤ a) : (3 / 4 : ℝ) ≤ spinGamma a := by
  have h916 : (9 / 16 : ℝ) ≤ 1 - 2 / a := by
    have h2a : 2 / a ≤ 2 / 64 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha
    linarith only [h2a]
  unfold spinGamma
  calc (3 / 4 : ℝ) = Real.sqrt (9 / 16) := by norm_num
    _ ≤ Real.sqrt (1 - 2 / a) := Real.sqrt_le_sqrt h916

private lemma xiStar_sub_spinBStar_le {n' : ℝ} (hn : 48 ≤ n') :
    xiStar - spinBStar (n' / 12) ≤ 24 * xiStar / n' := by
  let a : ℝ := n' / 12
  have hn_pos : 0 < n' := by linarith
  have ha2 : 2 < a := by dsimp [a]; linarith
  have h1γ : 1 - spinGamma a ≤ 2 / a := by
    have hdiff : 1 - spinGamma a ^ 2 = 2 / a := by rw [spinGamma_sq ha2.le]; ring
    have hpos : 0 < 1 + spinGamma a := by linarith [spinGamma_pos ha2]
    calc 1 - spinGamma a = (2 / a) / (1 + spinGamma a) := by
          rw [← hdiff, show 1 - spinGamma a ^ 2 = (1 - spinGamma a) * (1 + spinGamma a) by ring,
            mul_div_cancel_right₀ _ hpos.ne']
      _ ≤ (2 / a) / 1 := div_le_div_of_nonneg_left (by positivity) one_pos (by linarith [spinGamma_pos ha2])
      _ = 2 / a := div_one _
  have h2a : 2 / a = 24 / n' := by dsimp [a]; ring
  calc xiStar - spinBStar a = xiStar * (1 - spinGamma a) := by unfold spinBStar; ring
    _ ≤ xiStar * (2 / a) := mul_le_mul_of_nonneg_left h1γ xiStar_pos.le
    _ = 24 * xiStar / n' := by rw [h2a]; ring

private lemma spinLambda_pow_sub_one_le_n {n' : ℝ} (hc49 : 49 ≤ n' + 1) {N : ℕ}
    (hN_n : 768 * (N : ℝ) ≤ n') (_hn_pos : 0 < n') :
    spinLambda (n' / 12) ^ N - 1 ≤ 48 * (N : ℝ) / n' := by
  have h1 : spinLambda ((n' + 1 - 1) / 12) ^ N - 1 ≤ 48 * (N : ℝ) / (n' + 1 - 1) := by
    refine spinLambda_pow_sub_one_le hc49 ?_
    rw [div_le_iff₀ (by linarith)]; linarith
  simpa using h1

private lemma spin_rpow_neg_one_eq {n' : ℝ} (hn_pos : 0 < n') :
    n' ^ (-1 : ℝ) = n' ^ (-(2 / 3 : ℝ)) * n' ^ (-(1 / 3 : ℝ)) := by
  rw [← Real.rpow_add hn_pos]; congr 1; norm_num

private lemma spin_N_eps_le {n' R : ℝ} (hn_pos : 0 < n') {N : ℕ}
    (hie_lt : (96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-(1 / 3 : ℝ)) ≤ R / 4) :
    let ε := n' ^ (-(2 / 3 : ℝ))
    (48 * (N : ℝ) / n') * (2 * xiStar) + 24 * xiStar / n' ≤ ε * (R / 4) := by
  intro ε
  have hn_rew : n' ^ (-1 : ℝ) = ε * n' ^ (-(1 / 3 : ℝ)) := spin_rpow_neg_one_eq hn_pos
  have h1 : (48 * (N : ℝ) / n') * (2 * xiStar) + 24 * xiStar / n' =
      (96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]; ring
  have hε_nn : 0 ≤ ε := by dsimp [ε]; positivity
  rw [h1, hn_rew]
  calc (96 * (N : ℝ) * xiStar + 24 * xiStar) * (ε * n' ^ (-(1 / 3 : ℝ)))
      = ε * ((96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-(1 / 3 : ℝ))) := by ring
    _ ≤ ε * (R / 4) := mul_le_mul_of_nonneg_left hie_lt hε_nn

private lemma spinS4_3_3_cap_sum {n' a R ε C_22b κ δ₀ K_1 δ_n c_exp C_cap : ℝ} {N : ℕ}
    {Φ : ℝ × ℝ → ℝ} {E_cap : Set (ℝ × ℝ)}
    (ha_eq : a = n' / 12) (ha2 : 2 < a) (hn_pos : 0 < n') (hR : 2 ≤ R)
    (_hN_ge : R ^ (3 / 2 : ℝ) ≤ (N : ℝ)) (hN_le : (N : ℝ) ≤ 2 * R ^ (3 / 2 : ℝ))
    (hN_pos : 1 ≤ N) (hN_n : 768 * (N : ℝ) ≤ n')
    (hε_pos : 0 < ε) (hε_def : ε = n' ^ (-(2 / 3 : ℝ))) (hε_eq : n' * ε ^ (3 / 2 : ℝ) = 1)
    (hC22_pos : 0 < C_22b) (hκ_pos : 0 < κ) (hδ₀_pos : 0 < δ₀) (hc_exp_pos : 0 < c_exp)
    (hcexp_pi : c_exp ≤ 2 * π * xiStar)
    (hc_exp_c22 : 2 * c_exp ≤ κ * (2 : ℝ) ^ (-(5 / 2 : ℝ)))
    (hCcap_eq : C_cap = 4 * (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ)) * (4 / c_exp ^ 2))
    (hKδ_lt : K_1 * δ_n < min (xiStar / 32) (δ₀ / 2)) (hc49 : 49 ≤ n' + 1)
    (hΦ : SpinTestClass a Φ) (hS_int : IntegrableOn (spinSlitIntegral a Φ) (Icc (-(3 * spinBStar a / 4)) (3 * spinBStar a / 4)))
    (hS_le : ∫ d in Icc (-(3 * spinBStar a / 4)) (3 * spinBStar a / 4), spinSlitIntegral a Φ d ≤ C_22b)
    (hS_ae : ∀ᵐ d ∂(volume.restrict (Icc (-(3 * spinBStar a / 4)) (3 * spinBStar a / 4))),
      IntegrableOn (fun s => a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + d) (s - d)|)
        {s | spinBStar a ≤ |s|})
    (hfold_c : ∀ R' : ℝ, 1 ≤ R' → ∀ ξ d : ℝ, |ξ| < spinBStar a → |d| ≤ 3 * spinBStar a / 4 →
      IntegrableOn (fun s => a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + d) (s - d)|)
        {s | spinBStar a ≤ |s|} →
      let δ := spinBStar a - |ξ|
      R' * n' ^ (-(2 / 3 : ℝ)) ≤ δ → δ ≤ δ₀ →
      a * Real.exp (n' * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)| ≤
        C_22b * (1 + spinSlitIntegral a Φ d) * δ⁻¹ * Real.exp (-κ * n' * δ ^ (3 / 2 : ℝ)))
    (hΦ_G_int : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2))
    (hdiff_i : Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2))
    (htail_cap : ∫ q in E_cap, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 ≤
      3 * Real.exp (-2 * π * xiStar * R ^ (3 / 2 : ℝ)))
    (hcap_geom : ∀ q ∈ E_cap, xiStar / 2 ≤ q.1 ∧ xiStar / 2 ≤ q.2 ∧
      q.1 ≤ 2 * xiStar ∧ q.2 ≤ 2 * xiStar ∧ |(q.1 - q.2) / 2| ≤ 3 * xiStar / 8)
    (hcap_mem : ∀ q ∈ E_cap, 0 < q.1 ∧ 0 < q.2 ∧ (q.1 + q.2) / 2 ≤ xiStar - ε * R ∧ xiStar - K_1 * δ_n ≤ (q.1 + q.2) / 2)
    (hm_cap : MeasurableSet E_cap)
    (hie_lt : (96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-(1 / 3 : ℝ)) ≤ R / 4) :
    ∫ q in E_cap, |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 ≤
      (3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
  let g : ℝ × ℝ → ℝ := fun q => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
  have hG_c : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hW_c : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  have hDa_c : Continuous (fun p : ℝ × ℝ => spinDa a Φ p.1 p.2) := by
    unfold spinDa
    exact (((hG_c.sub (hG_c.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))).sub
      (hG_c.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))).add
      (hG_c.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))))
  have hDelta_c : Continuous (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) := by
    unfold spinDeltaA; exact hDa_c.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hT_c : Continuous (fun p : ℝ × ℝ => spinTruncInv a N Φ p.1 p.2) := by
    unfold spinTruncInv
    have hsc : ∀ c1 c2 : ℝ, Continuous (fun p : ℝ × ℝ => spinG a Φ (c1 * p.1) (c2 * p.2)) := fun c1 c2 =>
      hG_c.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
    have hsum_fn : ∀ (M : ℕ) (F : ℕ → ℝ × ℝ → ℝ), (∀ j < M, Continuous (F j)) →
        Continuous (fun x => ∑ j ∈ Finset.range M, F j x) := fun M F hF => by
      induction M with
      | zero => simpa using continuous_const
      | succ k ih =>
        simp_rw [Finset.sum_range_succ]
        exact (ih fun j hj => hF j (Nat.lt_succ_of_lt hj)).add (hF k (Nat.lt_succ_self k))
    refine hsum_fn N _ fun j _ => hsum_fn N _ fun ℓ _ => ?_
    simp only [spinDeltaA, spinDa, ← mul_assoc]
    exact (((hsc _ _).sub (hsc _ _)).sub (hsc _ _)).add (hsc _ _)
  let bStar := spinBStar a
  let D := 3 * bStar / 4
  have hγ_half : (3 / 4 : ℝ) ≤ spinGamma a := by
    have h1N : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN_pos
    have h768 : (768 : ℝ) ≤ n' := by linarith only [hN_n, h1N]
    exact spinGamma_ge_three_fourths (by rw [ha_eq]; linarith only [h768])
  have hbStar_ge : 3 * xiStar / 4 ≤ bStar := by
    dsimp [bStar]; unfold spinBStar
    linarith only [mul_le_mul_of_nonneg_right hγ_half xiStar_pos.le]
  have hbStar_le : bStar ≤ xiStar := by
    dsimp [bStar]; unfold spinBStar
    exact (mul_le_of_le_one_left xiStar_pos.le (spinGamma_lt_one ha2).le)
  have hξ_bStar : xiStar - bStar ≤ 24 * xiStar / n' := by
    dsimp [bStar]; rw [ha_eq]; exact xiStar_sub_spinBStar_le (by linarith only [hc49])
  have hlamN_sub : spinLambda a ^ N - 1 ≤ 48 * (N : ℝ) / n' := by
    rw [ha_eq]; exact spinLambda_pow_sub_one_le_n hc49 hN_n hn_pos
  have hN_eps : (48 * (N : ℝ) / n') * (2 * xiStar) + 24 * xiStar / n' ≤ ε * (R / 4) := by
    rw [hε_def]; exact spin_N_eps_le hn_pos hie_lt
  let A_box : Set (ℝ × ℝ) := {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧
    (y.1 + y.2) / 2 ≤ bStar - ε * (R / 2) ∧ bStar - δ₀ ≤ (y.1 + y.2) / 2 ∧
    |(y.1 - y.2) / 2| ≤ D}
  have hAbox_meas : MeasurableSet A_box :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isClosed_le ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet.inter
          ((isClosed_le continuous_const ((continuous_fst.add continuous_snd).div_const 2)).measurableSet.inter
            (isClosed_le (((continuous_fst.sub continuous_snd).div_const 2).abs)
              continuous_const).measurableSet)))
  let c_22 : ℝ := κ * (2 : ℝ) ^ (-(5 / 2 : ℝ))
  have hterm_bd : ∀ j ℓ : ℕ, j < N → ℓ < N →
      ∫⁻ q in E_cap, ENNReal.ofReal
        (|spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
          spinWc a q.1 * spinWc a q.2) ≤
        ENNReal.ofReal (2 * C_22b * (2 * D + C_22b) * (2 / κ) *
          Real.exp (-c_22 * R ^ (3 / 2 : ℝ))) := by
    intro j ℓ hj hℓ
    have hlam_gt1 := spinLambda_gt_one_s4 ha2
    have hlj_pos : 0 < spinLambda a ^ j := pow_pos (lt_trans zero_lt_one hlam_gt1) j
    have hll_pos : 0 < spinLambda a ^ ℓ := pow_pos (lt_trans zero_lt_one hlam_gt1) ℓ
    have hlj_ge1 : 1 ≤ spinLambda a ^ j := one_le_pow₀ hlam_gt1.le
    have hll_ge1 : 1 ≤ spinLambda a ^ ℓ := one_le_pow₀ hlam_gt1.le
    have hlj_leN : spinLambda a ^ j ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hj.le
    have hll_leN : spinLambda a ^ ℓ ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hℓ.le
    let fA : ℝ × ℝ → ℝ≥0∞ := A_box.indicator (fun y =>
      ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2))
    have hpt_q : ∀ q ∈ E_cap,
        ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
          spinWc a q.1 * spinWc a q.2) ≤
        fA (spinLambda a ^ j * q.1, spinLambda a ^ ℓ * q.2) := by
      intro q hq
      obtain ⟨hq1_ge, hq2_ge, hq1_le, hq2_le, hq_d_le⟩ := hcap_geom q hq
      obtain ⟨hq1_pos, hq2_pos, hq_ub, hq_lb⟩ := hcap_mem q hq
      set y1 := spinLambda a ^ j * q.1
      set y2 := spinLambda a ^ ℓ * q.2
      have hy1_pos : 0 < y1 := mul_pos hlj_pos hq1_pos
      have hy2_pos : 0 < y2 := mul_pos hll_pos hq2_pos
      have hdiff_j : y1 - q.1 ≤ (48 * (N : ℝ) / n') * (2 * xiStar) := by
        calc y1 - q.1 = (spinLambda a ^ j - 1) * q.1 := by dsimp [y1]; ring
          _ ≤ (spinLambda a ^ N - 1) * (2 * xiStar) :=
              mul_le_mul (by linarith only [hlj_leN]) hq1_le hq1_pos.le (by linarith only [hlj_leN, hlj_ge1])
          _ ≤ (48 * (N : ℝ) / n') * (2 * xiStar) :=
              mul_le_mul_of_nonneg_right hlamN_sub (by positivity [xiStar_pos])
      have hdiff_l : y2 - q.2 ≤ (48 * (N : ℝ) / n') * (2 * xiStar) := by
        calc y2 - q.2 = (spinLambda a ^ ℓ - 1) * q.2 := by dsimp [y2]; ring
          _ ≤ (spinLambda a ^ N - 1) * (2 * xiStar) :=
              mul_le_mul (by linarith only [hll_leN]) hq2_le hq2_pos.le (by linarith only [hll_leN, hll_ge1])
          _ ≤ (48 * (N : ℝ) / n') * (2 * xiStar) :=
              mul_le_mul_of_nonneg_right hlamN_sub (by positivity [xiStar_pos])
      have hsum_y_ub : (y1 + y2) / 2 ≤ bStar - ε * (R / 2) := by
        have hεR_pos : 0 < ε * R := mul_pos hε_pos (by linarith only [hR])
        have h14 : ε * (R / 4) - ε * R ≤ -(ε * (R / 2)) := by
          rw [show ε * (R / 4) = (ε * R) / 4 by ring, show ε * (R / 2) = (ε * R) / 2 by ring]
          linarith only [hεR_pos]
        linarith only [hq_ub, hdiff_j, hdiff_l, hξ_bStar, hN_eps, h14]
      have hsum_y_lb : bStar - δ₀ ≤ (y1 + y2) / 2 := by
        have hy1_ge : q.1 ≤ y1 := le_mul_of_one_le_left hq1_pos.le hlj_ge1
        have hy2_ge : q.2 ≤ y2 := le_mul_of_one_le_left hq2_pos.le hll_ge1
        have hK_le : K_1 * δ_n ≤ δ₀ :=
          (hKδ_lt.trans_le (min_le_right _ _)).le.trans (by linarith only [hδ₀_pos])
        linarith only [hq_lb, hy1_ge, hy2_ge, hK_le, hbStar_le]
      have hd_y : |(y1 - y2) / 2| ≤ D := by
        have h48N : 48 * (N : ℝ) / n' ≤ 1 / 16 := by rw [div_le_iff₀ hn_pos]; linarith only [hN_n]
        have hdj_xi : y1 - q.1 ≤ xiStar / 8 :=
          hdiff_j.trans (by nlinarith only [h48N, xiStar_pos])
        have hdl_xi : y2 - q.2 ≤ xiStar / 8 :=
          hdiff_l.trans (by nlinarith only [h48N, xiStar_pos])
        have hy1_ge : 0 ≤ y1 - q.1 := sub_nonneg.mpr (le_mul_of_one_le_left hq1_pos.le hlj_ge1)
        have hy2_ge : 0 ≤ y2 - q.2 := sub_nonneg.mpr (le_mul_of_one_le_left hq2_pos.le hll_ge1)
        have hdq := abs_le.mp hq_d_le
        have hd_y_le : |(y1 - y2) / 2| ≤ xiStar / 2 :=
          abs_le.mpr ⟨by linarith only [hdq.1, hy1_ge, hdl_xi, xiStar_pos],
            by linarith only [hdq.2, hy2_ge, hdj_xi, xiStar_pos]⟩
        have hD_ge : xiStar / 2 ≤ D := by dsimp [D]; linarith only [hbStar_ge, xiStar_pos]
        exact hd_y_le.trans hD_ge
      have hy_mem : (y1, y2) ∈ A_box := ⟨hy1_pos, hy2_pos, hsum_y_ub, hsum_y_lb, hd_y⟩
      dsimp [fA]; rw [Set.indicator_of_mem hy_mem]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw1 : spinWc a q.1 ≤ spinWc a y1 := spinWc_mono_abs ha2.le (by
        rw [abs_of_pos hq1_pos, abs_of_pos hy1_pos]; exact le_mul_of_one_le_left hq1_pos.le hlj_ge1)
      have hw2 : spinWc a q.2 ≤ spinWc a y2 := spinWc_mono_abs ha2.le (by
        rw [abs_of_pos hq2_pos, abs_of_pos hy2_pos]; exact le_mul_of_one_le_left hq2_pos.le hll_ge1)
      have hw_mul : spinWc a q.1 * spinWc a q.2 ≤ spinWc a y1 * spinWc a y2 :=
        mul_le_mul hw1 hw2 (spinWc_nonneg ha2.le _) (spinWc_nonneg ha2.le _)
      calc |spinDeltaA a Φ y1 y2| * spinWc a q.1 * spinWc a q.2
          = |spinDeltaA a Φ y1 y2| * (spinWc a q.1 * spinWc a q.2) := by ring
        _ ≤ |spinDeltaA a Φ y1 y2| * (spinWc a y1 * spinWc a y2) :=
            mul_le_mul_of_nonneg_left hw_mul (abs_nonneg _)
        _ = |spinDeltaA a Φ y1 y2| * spinWc a y1 * spinWc a y2 := by ring
    have hgam_le1 : (spinLambda a ^ j)⁻¹ * (spinLambda a ^ ℓ)⁻¹ ≤ 1 := by
      calc (spinLambda a ^ j)⁻¹ * (spinLambda a ^ ℓ)⁻¹ ≤ 1 * 1 :=
            mul_le_mul (inv_le_one_of_one_le₀ hlj_ge1) (inv_le_one_of_one_le₀ hll_ge1)
              (inv_nonneg.mpr hll_pos.le) zero_le_one
        _ = 1 := one_mul 1
    have hc_eq_n1 : (n' + 1) - 1 = n' := by ring
    have ha_eq_n1 : ((n' + 1) - 1) / 12 = a := by rw [hc_eq_n1, ← ha_eq]
    have hfold_inst : ∀ ξ d : ℝ, |ξ| < bStar → |d| ≤ D →
        IntegrableOn (fun s => ((n' + 1 - 1) / 12) * Real.exp (12 * ((n' + 1 - 1) / 12) * spinL s) *
          |spinDeltaA ((n' + 1 - 1) / 12) Φ (s + d) (s - d)|) {s | bStar ≤ |s|} →
        ε ≤ bStar - |ξ| → bStar - |ξ| ≤ δ₀ →
        ((n' + 1 - 1) / 12) * Real.exp ((n' + 1 - 1) * spinL ξ) *
          |spinDeltaA ((n' + 1 - 1) / 12) Φ (ξ + d) (ξ - d)| ≤
          C_22b * (1 + spinSlitIntegral ((n' + 1 - 1) / 12) Φ d) * (bStar - |ξ|)⁻¹ *
            Real.exp (-κ * (n' + 1 - 1) * (bStar - |ξ|) ^ (3 / 2 : ℝ)) := by
      intro ξ d hξ hd hS hlo hhi
      rw [hc_eq_n1, ← ha_eq] at hS ⊢
      have h1 := hfold_c 1 le_rfl ξ d hξ hd hS (by rwa [one_mul, ← hε_def]) hhi
      exact h1
    have hcap_bd := spinS4_3_3_cap_term (c := n' + 1) (δ_hi := δ₀) hR hε_pos
      (by linarith only [hc_eq_n1, hn_pos]) (by rw [hc_eq_n1]; exact hε_eq)
      hC22_pos hκ_pos (by dsimp [D]; linarith only [hbStar_ge, xiStar_pos])
      (by linarith only [hbStar_ge, xiStar_pos])
      (by rw [ha_eq_n1]; exact hΦ) (by rw [ha_eq_n1]; exact hS_int)
      (by rw [ha_eq_n1]; exact hS_le) (by rw [ha_eq_n1]; exact hS_ae)
      hfold_inst (by rw [ha_eq_n1]; exact ha2) hAbox_meas (fun y hy => hy)
    dsimp only at hcap_bd
    rw [hc_eq_n1, ← ha_eq] at hcap_bd
    calc ∫⁻ q in E_cap, ENNReal.ofReal
            (|spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
              spinWc a q.1 * spinWc a q.2)
        ≤ ∫⁻ q : ℝ × ℝ, fA (spinLambda a ^ j * q.1, spinLambda a ^ ℓ * q.2) := by
            rw [← lintegral_indicator hm_cap]
            refine lintegral_mono fun q => ?_
            by_cases hq : q ∈ E_cap
            · rw [Set.indicator_of_mem hq]; exact hpt_q q hq
            · rw [Set.indicator_of_notMem hq]; exact bot_le
      _ = ENNReal.ofReal ((spinLambda a ^ j)⁻¹ * (spinLambda a ^ ℓ)⁻¹) * ∫⁻ y : ℝ × ℝ, fA y :=
            lintegral_prod_scale_s4_3 hlj_pos hll_pos fA
      _ ≤ ENNReal.ofReal 1 * ∫⁻ y in A_box, ENNReal.ofReal
            (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) := by
            rw [lintegral_indicator hAbox_meas]; gcongr
      _ ≤ 1 * ENNReal.ofReal (2 * C_22b * (2 * D + C_22b) * (2 / κ) *
            Real.exp (-c_22 * R ^ (3 / 2 : ℝ))) := by
            rw [ENNReal.ofReal_one]; gcongr
      _ = ENNReal.ofReal (2 * C_22b * (2 * D + C_22b) * (2 / κ) *
            Real.exp (-c_22 * R ^ (3 / 2 : ℝ))) := one_mul _
  have hnn_g : ∀ q : ℝ × ℝ, 0 ≤ g q := fun q =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _)
  let tailFn : ℝ × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (|spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2)
  let termFn : ℕ → ℕ → ℝ × ℝ → ℝ≥0∞ := fun j ℓ q =>
    ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
      spinWc a q.1 * spinWc a q.2)
  have htail_meas : Measurable tailFn :=
    (ENNReal.continuous_ofReal.comp (((hG_c.sub hT_c).abs.mul (hW_c.comp continuous_fst)).mul
      (hW_c.comp continuous_snd))).measurable
  have hterm_meas : ∀ j ℓ : ℕ, Measurable (termFn j ℓ) := fun j ℓ =>
    (ENNReal.continuous_ofReal.comp (((hDelta_c.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).abs.mul (hW_c.comp continuous_fst)).mul
      (hW_c.comp continuous_snd))).measurable
  have hpt_le : ∀ q : ℝ × ℝ, ENNReal.ofReal (g q) ≤
      tailFn q + ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, termFn j ℓ q := by
    intro q
    have hw1 := spinWc_nonneg ha2.le q.1
    have hw2 := spinWc_nonneg ha2.le q.2
    have hG_abs : |spinG a Φ q.1 q.2| ≤ |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| +
        ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
          |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| := by
      have htri : |spinG a Φ q.1 q.2| ≤
          |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| + |spinTruncInv a N Φ q.1 q.2| := by
        have := abs_add_le (spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2) (spinTruncInv a N Φ q.1 q.2)
        simpa [sub_add_cancel] using this
      have hsum1 : |spinTruncInv a N Φ q.1 q.2| ≤
          ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
            |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| := by
        unfold spinTruncInv
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
      linarith
    have hr : g q ≤ |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 +
        ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
          |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| * spinWc a q.1 * spinWc a q.2 := by
      dsimp [g]
      calc |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
          ≤ (|spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| +
              ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
                |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)|) *
              spinWc a q.1 * spinWc a q.2 := by gcongr
        _ = |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 +
            ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
              |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
                spinWc a q.1 * spinWc a q.2 := by
            rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
            congr 1; refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul, Finset.sum_mul]
    refine (ENNReal.ofReal_le_ofReal hr).trans_eq ?_
    have hnn1 : 0 ≤ |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := by
      positivity
    have hnn2 : ∀ j ℓ : ℕ, 0 ≤ |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
        spinWc a q.1 * spinWc a q.2 := fun j ℓ => by positivity
    rw [ENNReal.ofReal_add hnn1 (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun ℓ _ => hnn2 j ℓ)]
    congr 1
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun ℓ _ => hnn2 j ℓ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => hnn2 j ℓ)
  have hsum_bd : ∫⁻ q in E_cap, (tailFn q + ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, termFn j ℓ q) =
      (∫⁻ q in E_cap, tailFn q) +
        ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, ∫⁻ q in E_cap, termFn j ℓ q := by
    have hsum_r : ∀ (M : ℕ) (F : ℕ → ℝ × ℝ → ℝ≥0∞), (∀ j, Measurable (F j)) →
        ∫⁻ q in E_cap, (∑ j ∈ Finset.range M, F j q) = ∑ j ∈ Finset.range M, ∫⁻ q in E_cap, F j q := by
      intro M F hFm
      induction M with
      | zero => simp
      | succ k ih =>
        simp_rw [Finset.sum_range_succ]
        rw [lintegral_add_left (Finset.measurable_sum _ fun j _ => hFm j), ih]
    rw [lintegral_add_left htail_meas]
    congr 1
    rw [hsum_r N (fun j q => ∑ ℓ ∈ Finset.range N, termFn j ℓ q)
      (fun j => Finset.measurable_sum _ fun ℓ _ => hterm_meas j ℓ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hsum_r N (termFn j) (fun ℓ => hterm_meas j ℓ)
  have htail_enn : ∫⁻ q in E_cap, tailFn q ≤
      ENNReal.ofReal (3 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hdiff_i.integrableOn
      (Eventually.of_forall fun q =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2.le q.1)) (spinWc_nonneg ha2.le q.2))]
    refine ENNReal.ofReal_le_ofReal (htail_cap.trans ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_right (by linarith only [hcexp_pi])
      (Real.rpow_nonneg (by linarith only [hR]) _)
  have hCcap_nn : 0 ≤ C_cap := by rw [hCcap_eq]; positivity [hC22_pos, hκ_pos, xiStar_pos, hc_exp_pos]
  have hcap_N2 : ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, ∫⁻ q in E_cap, termFn j ℓ q ≤
      ENNReal.ofReal (C_cap * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) := by
    let M_one : ℝ := 2 * C_22b * (2 * D + C_22b) * (2 / κ) * Real.exp (-c_22 * R ^ (3 / 2 : ℝ))
    have hD_nn : 0 ≤ D := by dsimp [D]; linarith only [hbStar_ge, xiStar_pos]
    have hM_nn : 0 ≤ M_one := by dsimp [M_one]; positivity [hC22_pos, hκ_pos, hD_nn]
    have hsum_le : ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, ∫⁻ q in E_cap, termFn j ℓ q ≤
        ∑ _j ∈ Finset.range N, ∑ _ℓ ∈ Finset.range N, ENNReal.ofReal M_one :=
      Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun ℓ hℓ =>
        hterm_bd j ℓ (Finset.mem_range.mp hj) (Finset.mem_range.mp hℓ)
    have hcard : (∑ _j ∈ Finset.range N, ∑ _ℓ ∈ Finset.range N, ENNReal.ofReal M_one) =
        ENNReal.ofReal ((N : ℝ) ^ 2 * M_one) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
        ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg N))]
      congr 1; ring
    refine hsum_le.trans (hcard.le.trans (ENNReal.ofReal_le_ofReal ?_))
    have hD_le : D ≤ xiStar := by dsimp [D]; linarith only [hbStar_le, xiStar_pos]
    have hN2_le : (N : ℝ) ^ 2 ≤ 4 * (R ^ (3 / 2 : ℝ)) ^ 2 := by
      have : (N : ℝ) ^ 2 ≤ (2 * R ^ (3 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hN_le 2
      linarith only [this]
    have hexp_split : Real.exp (-c_22 * R ^ (3 / 2 : ℝ)) ≤
        Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ R ^ (3 / 2 : ℝ) := by positivity
      nlinarith only [hc_exp_c22, this]
    have habsorb := sq_mul_exp_neg_le (u := R ^ (3 / 2 : ℝ)) (c := c_exp) (by positivity) hc_exp_pos
    have hC22_0 := hC22_pos.le
    have hκ_0 := hκ_pos.le
    have hxi_0 := xiStar_pos.le
    calc (N : ℝ) ^ 2 * M_one
        ≤ (4 * (R ^ (3 / 2 : ℝ)) ^ 2) *
            (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ) *
              (Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)))) := by
            dsimp [M_one]; gcongr
      _ = 4 * (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ)) *
            ((R ^ (3 / 2 : ℝ)) ^ 2 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) *
            Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by ring
      _ ≤ 4 * (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ)) * (4 / c_exp ^ 2) *
            Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by gcongr
      _ = C_cap * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by rw [hCcap_eq]
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity [hc_exp_pos, hCcap_nn]),
    ofReal_integral_eq_lintegral_ofReal hΦ_G_int.integrableOn (Eventually.of_forall hnn_g)]
  calc ∫⁻ q in E_cap, ENNReal.ofReal (g q)
      ≤ ∫⁻ q in E_cap, (tailFn q + ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, termFn j ℓ q) :=
          lintegral_mono fun q => hpt_le q
    _ = (∫⁻ q in E_cap, tailFn q) +
          ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, ∫⁻ q in E_cap, termFn j ℓ q := hsum_bd
    _ ≤ ENNReal.ofReal (3 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) +
          ENNReal.ofReal (C_cap * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) := add_le_add htail_enn hcap_N2
    _ = ENNReal.ofReal ((3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity [hCcap_nn])]
          congr 1; ring

private lemma spinS4_3_3_at_n
    {C_x C_22b κ δ₀ K_1 C_1 c_exp C_cap C R n' x₁ : ℝ} {k_s22b : ℝ} {N : ℕ} {Φ : ℝ × ℝ → ℝ}
    (hC22_pos : 0 < C_22b) (hκ_pos : 0 < κ) (hδ₀_pos : 0 < δ₀) (_hK1_pos : 0 < K_1)
    (hC1_pos : 0 < C_1) (hcexp_pos : 0 < c_exp) (hR : 2 ≤ R)
    (hN_ge : R ^ (3 / 2 : ℝ) ≤ (N : ℝ)) (hN_le : (N : ℝ) ≤ 2 * R ^ (3 / 2 : ℝ)) (hN_pos : 1 ≤ N)
    (hcexp_2pi : c_exp ≤ 2 * π * xiStar) (hcexp_c22 : 2 * c_exp ≤ κ * (2 : ℝ) ^ (-(5 / 2 : ℝ)))
    (hCcap_eq : C_cap = 4 * (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ)) * (4 / c_exp ^ 2))
    (hC_eq : C = 4 * (1 + 3 + C_cap) + 1)
    (hc49 : 49 ≤ n' + 1) (_hcc01 : 0 ≤ n') (hN_n : 768 * (N : ℝ) ≤ n')
    (hδ_lt : K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n' < min (xiStar / 32) (δ₀ / 2))
    (hCx_lt : C_x * n' ^ (-(2 / 3 : ℝ)) < xiStar / 32)
    (hie_lt : (96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-(1 / 3 : ℝ)) < R / 4)
    (hexp_lt : 16 * C_1 * n' ^ (-1 : ℝ) < Real.exp (-c_exp * R ^ (3 / 2 : ℝ)))
    (hx₁_gap : |x₁ - xiStar| ≤ C_x * n' ^ (-(2 / 3 : ℝ)))
    (hslack : SpinSlackHyp (n' + 1) x₁ Φ)
    (h21_step : ∀ hx0 : 0 ≤ x₁, x₁ ≤ xiStar + C_x * n' ^ (-(2 / 3 : ℝ)) →
      SpinTestClass (n' / 12) Φ → spinM2 (n' / 12) Φ = 1 →
      ∫ q in {q : ℝ × ℝ | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧
          spinLongDist q < xiStar - K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n'},
        |spinG (n' / 12) Φ q.1 q.2| * spinWc (n' / 12) q.1 * spinWc (n' / 12) q.2 ≤
          4 * C_1 * n' ^ (-1 : ℝ))
    (hS22b_step : SpinTestClass (n' / 12) Φ → spinM2 (n' / 12) Φ = 1 →
      (IntegrableOn (spinSlitIntegral (n' / 12) Φ)
          (Icc (-(3 * spinBStar (n' / 12) / 4)) (3 * spinBStar (n' / 12) / 4)) volume ∧
        ∫ d in Icc (-(3 * spinBStar (n' / 12) / 4)) (3 * spinBStar (n' / 12) / 4),
          spinSlitIntegral (n' / 12) Φ d ≤ C_22b ∧
        ∀ᵐ d ∂(volume.restrict (Icc (-(3 * spinBStar (n' / 12) / 4)) (3 * spinBStar (n' / 12) / 4))),
          IntegrableOn (fun s => (n' / 12) * Real.exp (12 * (n' / 12) * spinL s) *
              |spinDeltaA (n' / 12) Φ (s + d) (s - d)|) {s | spinBStar (n' / 12) ≤ |s|}) ∧
      (∀ R' : ℝ, 1 ≤ R' → ∀ ξ d : ℝ, |ξ| < spinBStar (n' / 12) →
        |d| ≤ 3 * spinBStar (n' / 12) / 4 →
        IntegrableOn (fun s => (n' / 12) * Real.exp (12 * (n' / 12) * spinL s) *
            |spinDeltaA (n' / 12) Φ (s + d) (s - d)|) {s | spinBStar (n' / 12) ≤ |s|} →
        let δ := spinBStar (n' / 12) - |ξ|
        R' * n' ^ (-(2 / 3 : ℝ)) ≤ δ → δ ≤ δ₀ →
        (n' / 12) * Real.exp (n' * spinL ξ) * |spinDeltaA (n' / 12) Φ (ξ + d) (ξ - d)| ≤
          C_22b * (1 + spinSlitIntegral (n' / 12) Φ d) * δ⁻¹ * Real.exp (-κ * n' * δ ^ (3 / 2 : ℝ)))) :
    let ε := n' ^ (-(2 / 3 : ℝ))
    let a := n' / 12
    ∫ p in {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 ∧
        spinLongDist q ≤ xiStar - ε * R},
      max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 ≤
        C * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
  let _ := k_s22b
  let ε := n' ^ (-(2 / 3 : ℝ))
  let a := n' / 12
  have hR_pos : 0 < R := by linarith only [hR]
  obtain ⟨hx₁0, hΦ, hM2, _hvac, _hgap⟩ := hslack
  have hn_pos : 0 < n' := by linarith only [hc49]
  have ha2 : 2 < a := by dsimp [a]; linarith only [hc49]
  have ha0 : 0 < a := by linarith only [ha2]
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  have hε_eq : n' * ε ^ (3 / 2 : ℝ) = 1 := by
    dsimp [ε]
    rw [← Real.rpow_mul hn_pos.le, show -(2 / 3 : ℝ) * (3 / 2 : ℝ) = -1 by norm_num,
      Real.rpow_neg_one, mul_inv_cancel₀ hn_pos.ne']
  have ha_eq : (n' + 1 - 1) / 12 = a := by dsimp [a]; ring
  rw [ha_eq] at hΦ hM2
  have hx₁_ub : x₁ ≤ xiStar + C_x * n' ^ (-(2 / 3 : ℝ)) := by linarith only [(abs_le.mp hx₁_gap).2]
  have hG_int : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) :=
    integrable_spinG_wc ha0 hΦ
  let E_all : Set (ℝ × ℝ) := {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 ∧
    spinLongDist q ≤ xiStar - ε * R}
  let E_pp : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧
    (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ (q.1 + q.2) / 2 ≤ xiStar - ε * R}
  have hmE_all : MeasurableSet E_all := by
    have h1 : Continuous (fun q : ℝ × ℝ => (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4) := by fun_prop
    have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
    exact (isOpen_lt h1 continuous_const).measurableSet.inter
      (isClosed_le h2 continuous_const).measurableSet
  have hmax_le_abs : ∫ p in E_all, max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 ≤
      ∫ p in E_all, |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by
    refine setIntegral_mono_on ?_ hG_int.integrableOn hmE_all fun p _ => ?_
    · refine hG_int.integrableOn.mono' ?_ (Eventually.of_forall fun p => ?_)
      · have hGm : Measurable (fun p : ℝ × ℝ => max (-spinG a Φ p.1 p.2) 0) :=
          ((hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
            (continuous_const.mul continuous_snd))).neg.max continuous_const).measurable
        have hWc : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
        exact ((hGm.mul (hWc.comp continuous_fst).measurable).mul
          (hWc.comp continuous_snd).measurable).aestronglyMeasurable
      · have hw1 := spinWc_nonneg ha2.le p.1
        have hw2 := spinWc_nonneg ha2.le p.2
        have h1 : max (-spinG a Φ p.1 p.2) 0 ≤ |spinG a Φ p.1 p.2| := max_le (neg_le_abs _) (abs_nonneg _)
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _) hw1) hw2)]
        gcongr
    · have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      have h1 : max (-spinG a Φ p.1 p.2) 0 ≤ |spinG a Φ p.1 p.2| := max_le (neg_le_abs _) (abs_nonneg _)
      gcongr
  let g : ℝ × ℝ → ℝ := fun q => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
  have hE_all_eq : ∫ q in E_all, g q = 4 * ∫ q in E_pp, g q :=
    spinS4_d4_four_quadrants ha2 hΦ
  let δ_n := ε * Real.log n'
  let E_far : Set (ℝ × ℝ) := {q ∈ E_pp | (q.1 + q.2) / 2 < xiStar - K_1 * δ_n}
  let E_cap : Set (ℝ × ℝ) := {q ∈ E_pp | xiStar - K_1 * δ_n ≤ (q.1 + q.2) / 2}
  have hm_pp : MeasurableSet E_pp :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet.inter
        (isClosed_le ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet))
  have hm_far : MeasurableSet E_far := hm_pp.inter
    (isOpen_lt ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet
  have hm_cap : MeasurableSet E_cap := hm_pp.inter
    (isClosed_le continuous_const ((continuous_fst.add continuous_snd).div_const 2)).measurableSet
  have hpp_split : ∫ q in E_pp, g q = (∫ q in E_far, g q) + ∫ q in E_cap, g q := by
    have hU : E_pp = E_far ∪ E_cap := by
      ext q; simp only [E_pp, E_far, E_cap, Set.mem_union, Set.mem_sep_iff]
      constructor
      · intro hq
        rcases lt_or_ge ((q.1 + q.2) / 2) (xiStar - K_1 * δ_n) with h | h
        · exact Or.inl ⟨hq, h⟩
        · exact Or.inr ⟨hq, h⟩
      · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    have hd : Disjoint E_far E_cap := Set.disjoint_left.mpr fun q h1 h2 => not_le_of_gt h1.2 h2.2
    rw [hU, ← integral_indicator (hm_far.union hm_cap), ← integral_indicator hm_far,
      ← integral_indicator hm_cap, ← integral_add (hG_int.indicator hm_far) (hG_int.indicator hm_cap)]
    congr 1; ext q
    by_cases h1 : q ∈ E_far <;> by_cases h2 : q ∈ E_cap
    · exact absurd h2 (Set.disjoint_left.mp hd h1)
    · rw [Set.indicator_of_mem (Or.inl h1), Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
    · rw [Set.indicator_of_mem (Or.inr h2), Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]
    · rw [Set.indicator_of_notMem (by rintro (h | h) <;> contradiction),
        Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
  have hfar_bd : ∫ q in E_far, g q ≤ 4 * C_1 * n' ^ (-1 : ℝ) := by
    have hsub : E_far ⊆ {q : ℝ × ℝ | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧
        spinLongDist q < xiStar - K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n'} := by
      intro q hq
      have hp := hq.1
      refine ⟨hp.2.2.1, ?_⟩
      unfold spinLongDist; rw [abs_of_pos hp.1, abs_of_pos hp.2.1]
      have hKeq : K_1 * δ_n = K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n' := by dsimp [δ_n, ε]; ring
      linarith only [hq.2, hKeq]
    have hmono := setIntegral_mono_set hG_int.integrableOn
      (Eventually.of_forall fun q => mul_nonneg (mul_nonneg (abs_nonneg _)
        (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _)) (Eventually.of_forall hsub)
    exact hmono.trans (h21_step hx₁0 hx₁_ub hΦ hM2)
  have hKδ_lt : K_1 * δ_n < min (xiStar / 32) (δ₀ / 2) := by
    simpa [δ_n, ε, mul_assoc] using hδ_lt
  have hcap_geom : ∀ q ∈ E_cap, xiStar / 2 ≤ q.1 ∧ xiStar / 2 ≤ q.2 ∧
      q.1 ≤ 2 * xiStar ∧ q.2 ≤ 2 * xiStar ∧ |(q.1 - q.2) / 2| ≤ 3 * xiStar / 8 := by
    intro q ⟨⟨hq1, hq2, hq_rad, hq_sum⟩, hq_lb⟩
    have hxi_nn := xiStar_pos.le
    have h1 : x₁ < (33 / 32 : ℝ) * xiStar := by linarith only [hx₁_ub, hCx_lt, xiStar_pos]
    have h2 : (31 / 32 : ℝ) * xiStar < (q.1 + q.2) / 2 := by
      linarith only [hq_lb, hKδ_lt.trans_le (min_le_left _ _)]
    have hsq_diff : ((q.1 - q.2) / 2) ^ 2 < (3 * xiStar / 8) ^ 2 := by
      have h0 : ((q.1 + q.2) / 2) ^ 2 + ((q.1 - q.2) / 2) ^ 2 = (q.1 ^ 2 + q.2 ^ 2) / 2 := by ring
      have hrad : ((q.1 + q.2) / 2) ^ 2 + ((q.1 - q.2) / 2) ^ 2 < x₁ ^ 2 := by linarith only [hq_rad, h0]
      have hx1_sq : x₁ ^ 2 < ((33 / 32 : ℝ) * xiStar) ^ 2 :=
        pow_lt_pow_left₀ h1 hx₁0 (by norm_num)
      have hsum_sq : ((31 / 32 : ℝ) * xiStar) ^ 2 < ((q.1 + q.2) / 2) ^ 2 :=
        pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
      nlinarith only [hrad, hx1_sq, hsum_sq, sq_nonneg xiStar]
    have hd_abs : |(q.1 - q.2) / 2| < 3 * xiStar / 8 :=
      abs_lt.mpr (abs_lt_of_sq_lt_sq' (by simpa [sq_abs] using hsq_diff) (by positivity))
    have hd_le := abs_lt.mp hd_abs
    have hεR_pos : 0 < ε * R := mul_pos hε_pos hR_pos
    have hq_sum_le : (q.1 + q.2) / 2 ≤ xiStar := hq_sum.trans (sub_le_self _ hεR_pos.le)
    refine ⟨by linarith only [h2, hd_le.1, hxi_nn], by linarith only [h2, hd_le.2, hxi_nn],
      by linarith only [hq_sum_le, hd_le.2, hxi_nn], by linarith only [hq_sum_le, hd_le.1, hxi_nn], hd_abs.le⟩
  let r : ℝ := xiStar / 2
  have hr_pos : 0 < r := half_pos xiStar_pos
  have hcap_sub_r : E_cap ⊆ {q : ℝ × ℝ | r ≤ q.1 ∧ r ≤ q.2} := fun q hq =>
    ⟨(hcap_geom q hq).1, (hcap_geom q hq).2.1⟩
  obtain ⟨h0N_int, h0N_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr_pos hΦ 0 N
  obtain ⟨hN0_int, hN0_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr_pos hΦ N 0
  obtain ⟨hNN_int, hNN_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr_pos hΦ N N
  have h0N_e : (fun p : ℝ × ℝ => |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ 0 * p.1) (spinLambda a ^ N * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by ext p; rw [pow_zero, one_mul]
  have hN0_e : (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ 0 * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by ext p; rw [pow_zero, one_mul]
  rw [← h0N_e] at h0N_int h0N_bd
  rw [← hN0_e] at hN0_int hN0_bd
  have hG_c : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hW_c : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  have hDa_c : Continuous (fun p : ℝ × ℝ => spinDa a Φ p.1 p.2) := by
    unfold spinDa
    exact (((hG_c.sub (hG_c.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))).sub
      (hG_c.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))).add
      (hG_c.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))))
  have hDelta_c : Continuous (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) := by
    unfold spinDeltaA
    exact hDa_c.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hT_c : Continuous (fun p : ℝ × ℝ => spinTruncInv a N Φ p.1 p.2) := by
    unfold spinTruncInv
    have hsc : ∀ c1 c2 : ℝ, Continuous (fun p : ℝ × ℝ => spinG a Φ (c1 * p.1) (c2 * p.2)) := fun c1 c2 =>
      hG_c.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
    have hsum_fn : ∀ (M : ℕ) (F : ℕ → ℝ × ℝ → ℝ), (∀ j < M, Continuous (F j)) →
        Continuous (fun x => ∑ j ∈ Finset.range M, F j x) := fun M F hF => by
      induction M with
      | zero => simpa using continuous_const
      | succ k ih =>
        simp_rw [Finset.sum_range_succ]
        exact (ih fun j hj => hF j (Nat.lt_succ_of_lt hj)).add (hF k (Nat.lt_succ_self k))
    refine hsum_fn N _ fun j _ => hsum_fn N _ fun ℓ _ => ?_
    simp only [spinDeltaA, spinDa, ← mul_assoc]
    exact (((hsc _ _).sub (hsc _ _)).sub (hsc _ _)).add (hsc _ _)
  have hdiff_i : Integrable (fun p : ℝ × ℝ =>
      |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := by
    refine ((h0N_int.add hN0_int).add hNN_int).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((hG_c.sub hT_c).abs.mul (hW_c.comp continuous_fst)).mul
        (hW_c.comp continuous_snd)).aestronglyMeasurable
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
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| := by
        linarith only [hab1, hab2]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hw1) hw2).trans_eq
        (by simp only [Pi.add_apply]; ring)
  have htail_cap : ∫ q in E_cap, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| *
      spinWc a q.1 * spinWc a q.2 ≤ 3 * Real.exp (-2 * π * xiStar * R ^ (3 / 2 : ℝ)) :=
    spinS4_3_3_tail_cap ha2 hΦ hM2 hR_pos.le hN_ge hdiff_i hcap_sub_r
  obtain ⟨⟨hS_int, hS_le, hS_ae⟩, hfold_c⟩ := hS22b_step hΦ hM2
  have hcap_bd : ∫ q in E_cap, g q ≤ (3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) :=
    spinS4_3_3_cap_sum (a := a) (n' := n') rfl ha2 hn_pos hR hN_ge hN_le hN_pos hN_n hε_pos rfl hε_eq
      hC22_pos hκ_pos hδ₀_pos hcexp_pos hcexp_2pi hcexp_c22 hCcap_eq hKδ_lt hc49 hΦ
      hS_int hS_le hS_ae hfold_c hG_int hdiff_i htail_cap hcap_geom
      (fun q hq => ⟨hq.1.1, hq.1.2.1, hq.1.2.2.2, hq.2⟩) hm_cap hie_lt.le
  have hpp_bd : ∫ q in E_pp, g q ≤ (1 + 3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
    have hfar' : ∫ q in E_far, g q ≤ 1 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
      have hC1n : 0 ≤ C_1 * n' ^ (-1 : ℝ) := mul_nonneg hC1_pos.le (Real.rpow_nonneg hn_pos.le _)
      have h4_16 : 4 * C_1 * n' ^ (-1 : ℝ) ≤ 16 * C_1 * n' ^ (-1 : ℝ) := by nlinarith only [hC1n]
      exact hfar_bd.trans (h4_16.trans (hexp_lt.le.trans_eq (one_mul _).symm))
    calc ∫ q in E_pp, g q = (∫ q in E_far, g q) + ∫ q in E_cap, g q := hpp_split
      _ ≤ 1 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) + (3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) :=
          add_le_add hfar' hcap_bd
      _ = (1 + 3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by ring
  calc ∫ p in E_all, max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2
      ≤ ∫ p in E_all, g p := hmax_le_abs
    _ = 4 * ∫ q in E_pp, g q := hE_all_eq
    _ ≤ 4 * ((1 + 3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hpp_bd (by norm_num)
    _ = (4 * (1 + 3 + C_cap)) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by ring
    _ ≤ C * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        rw [hC_eq]; exact le_add_of_nonneg_right zero_le_one

/-- **`s4:3.3` (`spinning_s4.tex`, Theorem 3.3): fixed Airy-window tightness of the
negative weighted mass.** -/
theorem spinS4_3_3 : SpinS4_3_3 := by
  intro C_x hCx
  obtain ⟨k_s22b, C_22b, κ, δ₀, n₀, _hk0, hC22_pos, hκ_pos, hδ₀_pos, hn₀, hS22b_main⟩ := spinS22b
  obtain ⟨K_1, C_1, c₀₁, hK1_pos, hC1_pos, hc01, h21_all⟩ :=
    spinS4_2_1_all_quads (C_x := C_x) (p := 1) (by norm_num)
  let c_22 : ℝ := κ * (2 : ℝ) ^ (-(5 / 2 : ℝ))
  let c_exp : ℝ := min (π * xiStar) (c_22 / 2)
  have hcexp_pos : 0 < c_exp := by have := xiStar_pos; have := Real.pi_pos; positivity
  let C_cap : ℝ := 4 * (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ)) * (4 / c_exp ^ 2)
  let C : ℝ := 4 * (1 + 3 + C_cap) + 1
  have hCcap0 : 0 ≤ C_cap := by have := xiStar_pos; positivity
  have hCpos : 0 < C := by positivity
  refine ⟨C, c_exp, 2, hCpos, hcexp_pos, by norm_num, ?_⟩
  intro R hR
  let N : ℕ := Nat.ceil (R ^ (3 / 2 : ℝ))
  have hR_pos : 0 < R := by linarith
  have hR32_ge1 : 1 ≤ R ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hN_ge : R ^ (3 / 2 : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
  have hN_le : (N : ℝ) ≤ 2 * R ^ (3 / 2 : ℝ) := by
    have hlt := Nat.ceil_lt_add_one (le_trans zero_le_one hR32_ge1); linarith
  have hN_pos : 1 ≤ N := Nat.ceil_pos.mpr (by positivity)
  have ht_delta : Tendsto (fun n' : ℝ => K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n') atTop (𝓝 0) := by
    have ht0 : Tendsto (fun n' : ℝ => Real.log n' / n' ^ (2 / 3 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
    have hrew : (fun n' : ℝ => K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n') =ᶠ[atTop]
        fun n' => K_1 * (Real.log n' / n' ^ (2 / 3 : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with n' hn'
      rw [Real.rpow_neg hn'.le, div_eq_mul_inv]; ring
    exact (ht0.const_mul K_1).congr' (by simpa using hrew.symm) |>.trans (by simp)
  have ht_Cx : Tendsto (fun n' : ℝ => C_x * n' ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul C_x
  have ht_inv_eps : Tendsto (fun n' : ℝ => (96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-(1 / 3 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul
      (96 * (N : ℝ) * xiStar + 24 * xiStar)
  have ht_inv : Tendsto (fun n' : ℝ => 16 * C_1 * n' ^ (-1 : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).const_mul (16 * C_1)
  have hev_base : ∀ᶠ n' : ℝ in atTop,
      49 ≤ n' + 1 ∧ n₀ + 1 ≤ n' + 1 ∧ c₀₁ ≤ n' + 1 ∧ 768 * (N : ℝ) ≤ n' :=
    (eventually_ge_atTop (max (max 48 n₀) (max (c₀₁ - 1) (768 * (N : ℝ))))).mono fun n' hn' => by
      refine ⟨by linarith [le_max_left (48 : ℝ) n₀, le_max_left (max (48 : ℝ) n₀) (max (c₀₁ - 1) (768 * (N : ℝ)))],
        by linarith [le_max_right (48 : ℝ) n₀, le_max_left (max (48 : ℝ) n₀) (max (c₀₁ - 1) (768 * (N : ℝ)))],
        by linarith [le_max_left (c₀₁ - 1) (768 * (N : ℝ)), le_max_right (max (48 : ℝ) n₀) (max (c₀₁ - 1) (768 * (N : ℝ)))],
        by linarith [le_max_right (c₀₁ - 1) (768 * (N : ℝ)), le_max_right (max (48 : ℝ) n₀) (max (c₀₁ - 1) (768 * (N : ℝ)))]⟩
  have hev_δ : ∀ᶠ n' : ℝ in atTop,
      K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n' < min (xiStar / 32) (δ₀ / 2) :=
    ht_delta.eventually (gt_mem_nhds (by have := xiStar_pos; positivity))
  have hev_Cx : ∀ᶠ n' : ℝ in atTop, C_x * n' ^ (-(2 / 3 : ℝ)) < xiStar / 32 :=
    ht_Cx.eventually (gt_mem_nhds (by have := xiStar_pos; positivity))
  have hev_ie : ∀ᶠ n' : ℝ in atTop,
      (96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-(1 / 3 : ℝ)) < R / 4 :=
    ht_inv_eps.eventually (gt_mem_nhds (by positivity))
  have hev_exp : ∀ᶠ n' : ℝ in atTop,
      16 * C_1 * n' ^ (-1 : ℝ) < Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) :=
    ht_inv.eventually (gt_mem_nhds (Real.exp_pos _))
  filter_upwards [hev_base, hev_δ, hev_Cx, hev_ie, hev_exp] with n'
    ⟨hc49, hcn0, hcc01, hN_n⟩ hδ_lt hCx_lt hie_lt hexp_lt
  intro c ε a x₁ Φ hx₁_gap hslack
  have hcexp_2pi : c_exp ≤ 2 * π * xiStar :=
    (min_le_left _ _).trans (by have := Real.pi_pos; have := xiStar_pos; nlinarith only [Real.pi_pos, xiStar_pos])
  have hcexp_c22 : 2 * c_exp ≤ κ * (2 : ℝ) ^ (-(5 / 2 : ℝ)) :=
    by linarith only [min_le_right (π * xiStar) (c_22 / 2)]
  have hc_sub : (n' + 1) - 1 = n' := by ring
  have ha_eq : ((n' + 1) - 1) / 12 = n' / 12 := by rw [hc_sub]
  refine spinS4_3_3_at_n (C_x := C_x) (C_22b := C_22b) (κ := κ) (δ₀ := δ₀) (K_1 := K_1) (C_1 := C_1)
    (c_exp := c_exp) (C_cap := C_cap) (C := C) (R := R) (n' := n') (x₁ := x₁) (k_s22b := k_s22b) (N := N) (Φ := Φ)
    hC22_pos hκ_pos hδ₀_pos hK1_pos hC1_pos hcexp_pos hR hN_ge hN_le hN_pos hcexp_2pi hcexp_c22 rfl rfl
    hc49 (by linarith only [hc49]) hN_n hδ_lt hCx_lt hie_lt hexp_lt hx₁_gap hslack
    (fun hx0 hx_ub hΦ hM2 => by
      simpa [hc_sub, ha_eq] using h21_all hcc01 hx0 (by simpa [hc_sub] using hx_ub)
        (by simpa [ha_eq] using hΦ) (by simpa [ha_eq] using hM2))
    (fun hΦ hM2 => by
      obtain ⟨hA, _, hC⟩ := hS22b_main hcn0 (by simpa [ha_eq] using hΦ) (by simpa [ha_eq] using hM2)
      refine ⟨by simpa [ha_eq] using hA, ?_⟩
      intro R' hR' ξ d hξ hd hint δ hRδ hδ₀
      simpa [δ, hc_sub, ha_eq] using hC R' hR' ξ d (by simpa [ha_eq] using hξ) (by simpa [ha_eq] using hd)
        (by simpa [ha_eq] using hint) (by simpa [δ, hc_sub, ha_eq] using hRδ)
        (by simpa [δ, hc_sub, ha_eq] using hδ₀))

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_3_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_3_3

end FormalResearch.ModularBootstrap.Spin