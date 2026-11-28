/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasSmoothWeights

/-!
# Near-field smooth block package (`ct:boas` Steps 3–4)

Wrapper assembly proving `exists_near_weights` from `CtBoasSmoothWeights`.

Class: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.CohnElkies

/--- **Near-field smooth block package** (`ct:boas` Steps 3–4):
for `c₁ ∈ (0, c₁₀]`, there exist `c₀ ≥ exp 2`, `κ_min > 0`, and derivative constants `C_m(r)`
such that for all `c ≥ c₀`, `ε = ±1`, `R ∈ [c₁² c^{2/3}, 4 c₁² c^{2/3}]`, writing
`N = partCount (ctLv0 c / 4) (nearB c)`:
1. `ctLv0 c ≤ nearB c - 1` and `(N : ℝ) ≤ 250 * Real.log (16 / ctLv0 c) + 200 * nearB c + 810`;
2. `∑_{j < N} nearOmega = ctTaper * (1 - 𝔰_far) * nearCut`;
3. every `nearWeight j` is `C^∞`, `0 ≤ nearWeight j ≤ 1`, supported in
   `[L_j - ℓ_j / 100, L_j + ℓ_j / 100] ⊆ (ctLv0 c / 4, nearB c + 1)`, satisfies the `τ₀`-Harnack
   bounds `0.9 τ_j ≤ τ₀(L) ≤ 1.1 τ_j` and `L - L_j ≤ (2/5) Δ_{3/2}(τ_j)` on its support,
   has `κ_min c^{-2/21} ≤ ℓ_j` and `κ_min c^{-1/21} ≤ τ_j`, and
   `|iteratedDeriv r (nearWeight j) L| ≤ C_m(r) (c^{5/6})^r`;
4. `∑_{j < N} |nearWeight j L - nearOmega j L| ≤ c^{-4/3}` everywhere. -/
theorem exists_near_weights : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧
    ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → ∃ c₀ κ_min : ℝ, Real.exp 2 ≤ c₀ ∧ 0 < κ_min ∧
      ∃ C_m : ℕ → ℝ, (∀ r : ℕ, 0 ≤ C_m r) ∧
      ∀ {ε c R : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) →
          let N := partCount (ctLv0 c / 4) (nearB c)
          ctLv0 c ≤ nearB c - 1 ∧
          (N : ℝ) ≤ 250 * Real.log (16 / ctLv0 c) + 200 * nearB c + 810 ∧
          (∀ L, ∑ j ∈ Finset.range N, nearOmega ε c R j L =
            ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * nearCut c L) ∧
          (∀ L, ∑ j ∈ Finset.range N, |nearWeight ε c R j L - nearOmega ε c R j L| ≤ c ^ (-(4 / 3 : ℝ))) ∧
          (∀ j ∈ Finset.range N,
            let Lj := partGrid (ctLv0 c / 4) (j + 1)
            let ℓj := min Lj 1
            let τj := tau0 Lj
            ctLv0 c / 16 < Lj ∧ Lj ≤ nearB c + 4 ∧ 0 < ℓj ∧
            κ_min * c ^ (-(2 / 21 : ℝ)) ≤ ℓj ∧ κ_min * c ^ (-(1 / 21 : ℝ)) ≤ τj ∧
            0 < τj ∧
            (∀ n : ℕ, ContDiff ℝ n (nearWeight ε c R j)) ∧
            (∀ L, 0 ≤ nearWeight ε c R j L ∧ nearWeight ε c R j L ≤ 1) ∧
            (∀ L, L ∉ Icc (Lj - ℓj / 120) (Lj + ℓj / 120) → nearWeight ε c R j L = 0) ∧
            (∀ L, L ≤ ctLv0 c / 3 → nearWeight ε c R j L = 0) ∧
            (∀ L, nearB c + 1 ≤ L → nearWeight ε c R j L = 0) ∧
            (∀ L ∈ Icc (Lj - ℓj / 100) (Lj + ℓj / 100),
              0.9 * τj ≤ tau0 L ∧ tau0 L ≤ 1.1 * τj ∧
              L - Lj ≤ (2 / 5 : ℝ) * (hankelEdgeM (3 * τj / 2) - hankelEdgeM τj)) ∧
            (∀ r : ℕ, ∀ L, |iteratedDeriv r (nearWeight ε c R j) L| ≤ C_m r * (c ^ (5 / 6 : ℝ)) ^ r)) := by
  obtain ⟨c₁₀, hc₁₀, htap⟩ := ctTaper_hasDerivAt_and_lip
  obtain ⟨κ₀, hκ₀, cL, hcL1, hLv0⟩ := ctLv0_facts
  obtain ⟨S1, S2, hS1, hS2, hstepD⟩ := exists_smoothStep_deriv_bounds
  obtain ⟨K1, K2, hK1, hK2, hpart⟩ := part_facts
  refine ⟨c₁₀, hc₁₀, fun c₁ hc₁ hle => ?_⟩
  obtain ⟨C₀, C₁, C₂, c_t, hC₀, hC₁, hC₂, hct3, htap_prop⟩ := htap c₁ hc₁ hle
  set a₀ := (6 / 5 : ℝ) * κ₀ with ha₀
  have ha₀_pos : 0 < a₀ := by positivity
  set b₀ := a₀ / 16 with hb₀
  have hb₀_pos : 0 < b₀ := by positivity
  set C_m2 := nearCm2 a₀ C₁ C₂ S1 S2 K1 K2 with hCm2
  have hC_m2_nn : 0 ≤ C_m2 := nearCm2_nonneg ha₀_pos hC₁ hC₂ hS1 hS2 hK1 hK2
  set C_N' := 250 * (max (Real.log (16 / a₀)) 0 + 1) + 200 * (Real.log (π ^ 2) + 4) + 810 with hCN'
  have hCN'_pos : 0 < C_N' := by
    have : 0 < Real.log (π ^ 2) := Real.log_pos (by nlinarith [Real.pi_gt_three])
    positivity
  set M_tot := (1 / 2) * C_N' * C_m2 + 1 with hMtot
  have hMtot_pos : 0 < M_tot := by positivity
  have hev_eps_l : ∀ᶠ c : ℝ in atTop, c ^ (-(5 / 6 : ℝ)) ≤ b₀ / 600 * c ^ (-(2 / 21 : ℝ)) := by
    have ht : Tendsto (fun c : ℝ => c ^ (-(31 / 42 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    filter_upwards [ht.eventually (Iic_mem_nhds (by positivity : 0 < b₀ / 600)),
      eventually_gt_atTop (0 : ℝ)] with c hc_b hc0
    calc c ^ (-(5 / 6 : ℝ)) = c ^ (-(31 / 42 : ℝ)) * c ^ (-(2 / 21 : ℝ)) := by
          rw [← Real.rpow_add hc0]; norm_num
      _ ≤ (b₀ / 600) * c ^ (-(2 / 21 : ℝ)) :=
          mul_le_mul_of_nonneg_right hc_b (Real.rpow_nonneg hc0.le _)
  have hev_err : ∀ᶠ c : ℝ in atTop, M_tot * (1 + Real.log c) ^ 4 * c ^ (-(1 / 7 : ℝ)) ≤ 1 := by
    have hlin : Tendsto (fun c : ℝ => (1 + Real.log c) ^ 4 / c ^ (1 / 7 : ℝ)) atTop (𝓝 0) := by
      have h1 := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 28)
      have h2 : Tendsto (fun c : ℝ => (1 + Real.log c) / c ^ (1 / 28 : ℝ)) atTop (𝓝 0) := by
        have hadd := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 28)).congr'
          (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx; rw [Real.rpow_neg hx.le, ← one_div])).add
          h1.tendsto_div_nhds_zero
        rw [add_zero] at hadd
        refine hadd.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [add_div]
      have hpow : Tendsto (fun c : ℝ => ((1 + Real.log c) / c ^ (1 / 28 : ℝ)) ^ 4) atTop (𝓝 (0 ^ 4)) :=
        h2.pow 4
      rw [zero_pow (by norm_num)] at hpow
      refine hpow.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [div_pow, ← Real.rpow_natCast (x ^ (1 / 28 : ℝ)) 4, ← Real.rpow_mul hx.le,
        show (1 / 28 : ℝ) * ((4 : ℕ) : ℝ) = 1 / 7 by norm_num]
    have hmul : Tendsto (fun c : ℝ => M_tot * ((1 + Real.log c) ^ 4 / c ^ (1 / 7 : ℝ))) atTop (𝓝 (M_tot * 0)) :=
      tendsto_const_nhds.mul hlin
    rw [mul_zero] at hmul
    filter_upwards [hmul.eventually (Iic_mem_nhds one_pos), eventually_gt_atTop (0 : ℝ)] with c hcb hc0
    calc M_tot * (1 + Real.log c) ^ 4 * c ^ (-(1 / 7 : ℝ))
        = M_tot * ((1 + Real.log c) ^ 4 / c ^ (1 / 7 : ℝ)) := by
          rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, mul_div_assoc]
      _ ≤ 1 := hcb
  have hev_a : ∀ᶠ c : ℝ in atTop, a₀ * c ^ (-(2 / 21 : ℝ)) ≤ 1 ∧ b₀ * c ^ (-(2 / 21 : ℝ)) ≤ 1 := by
    have h1 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 21)).const_mul a₀).eventually
      (Iic_mem_nhds (by rw [mul_zero]; exact one_pos))
    have h2 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 21)).const_mul b₀).eventually
      (Iic_mem_nhds (by rw [mul_zero]; exact one_pos))
    exact h1.and h2
  obtain ⟨c_ev, hc_ev⟩ := ((eventually_ge_atTop (max (Real.exp 2) (max c_t cL))).and
    (hev_eps_l.and (hev_err.and hev_a))).exists_forall_of_atTop
  set κ_min := min b₀ (Real.sqrt (4 / 5 * b₀)) with hκmin
  have hκmin_pos : 0 < κ_min := lt_min hb₀_pos (Real.sqrt_pos.2 (by positivity))
  choose C_m_fn hCm_fn hdrv_fn using abs_iteratedDeriv_mollConv_le
  refine ⟨c_ev, κ_min, (le_max_left _ _).trans (hc_ev c_ev le_rfl).1, hκmin_pos, C_m_fn, hCm_fn, ?_⟩
  intro ε c R hε hc hRlo hRhi
  obtain ⟨hcM, hc_eps, hc_err, hc_a, hc_b⟩ := hc_ev c hc
  have hce2 : Real.exp 2 ≤ c := (le_max_left _ _).trans hcM
  have hc_ct : c_t ≤ c := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hcM
  have hc_L : cL ≤ c := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hcM
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 2)]) hce2
  have hc0 : 0 < c := by linarith
  have hlog2 : 2 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hce2
  have hlog1 : 1 ≤ 1 + Real.log c := by linarith
  obtain ⟨hL0, hexpL0, _, hLκ⟩ := hLv0 c hc_L
  have hL0_lb : a₀ * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c := by rw [ha₀]; linarith
  have hL0_le1 : ctLv0 c ≤ 1 := by
    have : Real.exp (ctLv0 c) ≤ 1 + 5e-4 := by linarith
    have := Real.add_one_le_exp (ctLv0 c)
    linarith
  have hL04_le1 : ctLv0 c / 4 ≤ 1 := by linarith
  have hB1 : 1 ≤ nearB c := by
    have h1 : 1 ≤ π ^ 2 * Real.log c := by nlinarith only [Real.pi_gt_three, hlog2]
    have := Real.log_nonneg h1
    unfold nearB; linarith
  have hLB : ctLv0 c ≤ nearB c - 1 := by
    have h1 : 1 ≤ π ^ 2 * Real.log c := by nlinarith only [Real.pi_gt_three, hlog2]
    have := Real.log_nonneg h1
    unfold nearB; linarith
  have hc16_pos : 0 < c ^ (-(2 / 21 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hc21_pos : 0 < c ^ (2 / 21 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hcp_21 : c ^ (-(2 / 21 : ℝ)) * c ^ (2 / 21 : ℝ) = 1 := by
    rw [← Real.rpow_add hc0]; norm_num
  have hc21_ge1 : 1 ≤ c ^ (2 / 21 : ℝ) := Real.one_le_rpow hc1.le (by norm_num)
  have hL0_inv : (ctLv0 c)⁻¹ ≤ a₀⁻¹ * c ^ (2 / 21 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hL0]
    calc (1 : ℝ) = c ^ (-(2 / 21 : ℝ)) * c ^ (2 / 21 : ℝ) := hcp_21.symm
      _ = (a₀⁻¹ * a₀) * (c ^ (-(2 / 21 : ℝ)) * c ^ (2 / 21 : ℝ)) := by field_simp
      _ = a₀⁻¹ * c ^ (2 / 21 : ℝ) * (a₀ * c ^ (-(2 / 21 : ℝ))) := by ring
      _ ≤ a₀⁻¹ * c ^ (2 / 21 : ℝ) * ctLv0 c := mul_le_mul_of_nonneg_left hL0_lb (by positivity)
  have hb₀_lb : b₀ * c ^ (-(2 / 21 : ℝ)) ≤ min (ctLv0 c / 16) 1 := by
    rw [hb₀]
    exact le_min (by linarith) hc_b
  have heps_pos : 0 < nearEps c := Real.rpow_pos_of_pos hc0 _
  have heps_le : nearEps c ≤ ctLv0 c / 8 := by
    calc nearEps c ≤ b₀ / 600 * c ^ (-(2 / 21 : ℝ)) := hc_eps
      _ ≤ (a₀ / 16) * c ^ (-(2 / 21 : ℝ)) := by
          rw [hb₀]
          exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) (by norm_num)) (Real.rpow_nonneg hc0.le _)
      _ ≤ ctLv0 c / 16 := by linarith only [hL0_lb]
      _ ≤ ctLv0 c / 8 := by linarith only [hL0]
  have heps_le1 : nearEps c ≤ 1 / 2 := by linarith only [heps_le, hL0_le1]
  have hpart_ab := hpart (A := ctLv0 c / 4) (B := nearB c) (by positivity) hL04_le1 hB1
  obtain ⟨hN_le, hpart_sum, hpart_j⟩ := hpart_ab
  have h416 : 4 / (ctLv0 c / 4) = 16 / ctLv0 c := by ring
  rw [h416] at hN_le
  obtain ⟨-, taperGrad, htap_d, htap_bd, _, _, htap_gbd, htap_glip⟩ := htap_prop hε hc_ct hRlo hRhi
  set N := partCount (ctLv0 c / 4) (nearB c)
  have hN_CN' : (N : ℝ) ≤ C_N' * (1 + Real.log c) := by
    have hlog_16 : Real.log (16 / ctLv0 c) ≤ Real.log (16 / a₀) + Real.log c := by
      have h1 : 16 / ctLv0 c ≤ 16 / a₀ * c ^ (2 / 21 : ℝ) := by
        calc 16 / ctLv0 c = 16 * (ctLv0 c)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ 16 * (a₀⁻¹ * c ^ (2 / 21 : ℝ)) := mul_le_mul_of_nonneg_left hL0_inv (by norm_num)
          _ = 16 / a₀ * c ^ (2 / 21 : ℝ) := by ring
      have h2 : c ^ (2 / 21 : ℝ) ≤ c := by
        simpa using Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num : (2 / 21 : ℝ) ≤ 1)
      have h3 : 16 / ctLv0 c ≤ 16 / a₀ * c := h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      calc Real.log (16 / ctLv0 c) ≤ Real.log (16 / a₀ * c) := Real.log_le_log (by positivity) h3
        _ = Real.log (16 / a₀) + Real.log c := Real.log_mul (by positivity) hc0.ne'
    have hB_le : nearB c ≤ (Real.log (π ^ 2) + 4) * (1 + Real.log c) := by
      have hlog_sub : Real.log (Real.log c) ≤ Real.log c := by
        have := Real.log_le_sub_one_of_pos (by linarith only [hlog2] : 0 < Real.log c)
        linarith only [this]
      have hpi2 : 0 ≤ Real.log (π ^ 2) := Real.log_nonneg (by nlinarith only [Real.pi_gt_three])
      unfold nearB
      rw [Real.log_mul (by positivity) (by linarith only [hlog2] : Real.log c ≠ 0)]
      nlinarith only [hlog2, hlog_sub, hpi2]
    have hlog16' : Real.log (16 / ctLv0 c) ≤ (max (Real.log (16 / a₀)) 0 + 1) * (1 + Real.log c) := by
      calc Real.log (16 / ctLv0 c) ≤ Real.log (16 / a₀) + Real.log c := hlog_16
        _ ≤ max (Real.log (16 / a₀)) 0 + Real.log c := by gcongr; exact le_max_left _ _
        _ ≤ (max (Real.log (16 / a₀)) 0 + 1) * (1 + Real.log c) := by
            nlinarith only [le_max_right (Real.log (16 / a₀)) 0, hlog2]
    have h810 : (810 : ℝ) ≤ 810 * (1 + Real.log c) := by nlinarith only [hlog2]
    calc (N : ℝ) ≤ 250 * Real.log (16 / ctLv0 c) + 200 * nearB c + 810 := hN_le
      _ ≤ 250 * ((max (Real.log (16 / a₀)) 0 + 1) * (1 + Real.log c)) +
            200 * ((Real.log (π ^ 2) + 4) * (1 + Real.log c)) + 810 * (1 + Real.log c) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hlog16' (by norm_num))
            (mul_le_mul_of_nonneg_left hB_le (by norm_num))) h810
      _ = C_N' * (1 + Real.log c) := by rw [hCN']; ring
  have hc3 : 3 ≤ c := hct3.trans hc_ct
  refine ⟨hLB, hN_le, fun L => sum_nearOmega_eq hL0 hL04_le1 hB1 L, ?_, ?_⟩
  · -- Summing mollification error `∑ |nearWeight j L - nearOmega j L| ≤ c^{-4/3}`
    have hper : ∀ j ∈ Finset.range N, ∀ L : ℝ,
        |nearWeight ε c R j L - nearOmega ε c R j L| ≤
          (1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2 := by
      intro j hj L
      obtain ⟨hLj_lo, _, hℓ0, hchi_bd, _, hchi_d1, hchi_d2⟩ := hpart_j j hj
      have hℓ_lb : b₀ * c ^ (-(2 / 21 : ℝ)) ≤ min (partGrid (ctLv0 c / 4) (j + 1)) 1 := by
        rw [hb₀]
        have : a₀ / 16 * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c / 16 := by linarith only [hL0_lb]
        exact le_min (by linarith only [this, hLj_lo]) hc_b
      have hℓ_inv : (min (partGrid (ctLv0 c / 4) (j + 1)) 1)⁻¹ ≤ (a₀ / 16)⁻¹ * c ^ (2 / 21 : ℝ) := by
        rw [← hb₀, inv_eq_one_div, div_le_iff₀ hℓ0]
        calc (1 : ℝ) = b₀⁻¹ * c ^ (2 / 21 : ℝ) * (b₀ * c ^ (-(2 / 21 : ℝ))) := by
              rw [mul_mul_mul_comm, inv_mul_cancel₀ hb₀_pos.ne', mul_comm (c ^ (2 / 21 : ℝ)), hcp_21, mul_one]
          _ ≤ b₀⁻¹ * c ^ (2 / 21 : ℝ) * min (partGrid (ctLv0 c / 4) (j + 1)) 1 :=
              mul_le_mul_of_nonneg_left hℓ_lb (by positivity)
      exact near_block_moll_err hc1 hc3 ha₀_pos hL0 hL0_inv hLB heps_le heps_le1 hC₁ hC₂ hS1 hS2 hK1 hK2
        htap_d htap_bd htap_gbd htap_glip (fun hab => hstepD hab) hℓ0 hℓ_inv hchi_bd hchi_d1 hchi_d2 L
    intro L
    have hsum_le : ∑ j ∈ Finset.range N, |nearWeight ε c R j L - nearOmega ε c R j L| ≤
        (N : ℝ) * ((1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2) := by
      calc _ ≤ ∑ _j ∈ Finset.range N,
              ((1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2) :=
            Finset.sum_le_sum fun j hj => hper j hj L
        _ = _ := by simp [nsmul_eq_mul]
    have heps_sq : c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2 = c ^ (-(31 / 21 : ℝ)) := by
      unfold nearEps
      rw [← Real.rpow_natCast (c ^ (-(5 / 6 : ℝ))) 2, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]
      norm_num
    have hpow_split : c ^ (-(31 / 21 : ℝ)) = c ^ (-(1 / 7 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    calc ∑ j ∈ Finset.range N, |nearWeight ε c R j L - nearOmega ε c R j L|
        ≤ (N : ℝ) * ((1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2) := hsum_le
      _ ≤ (C_N' * (1 + Real.log c)) *
            ((1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2) :=
          mul_le_mul_of_nonneg_right hN_CN' (by positivity)
      _ = ((1 / 2) * C_N' * C_m2) * (1 + Real.log c) ^ 4 * c ^ (-(1 / 7 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by
            rw [mul_assoc _ (c ^ (4 / 21 : ℝ)), heps_sq, hpow_split]; ring
      _ ≤ (M_tot * (1 + Real.log c) ^ 4 * c ^ (-(1 / 7 : ℝ))) * c ^ (-(4 / 3 : ℝ)) := by
            have hM : (1 / 2) * C_N' * C_m2 ≤ M_tot := by rw [hMtot]; linarith
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM (by positivity)) (by positivity))
              (by positivity)
      _ ≤ 1 * c ^ (-(4 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hc_err (by positivity)
      _ = c ^ (-(4 / 3 : ℝ)) := one_mul _
  · -- Per-block properties
    intro j hj
    obtain ⟨hLj_lo, hLj_hi, hℓ0, hchi_bd, hchi_supp, _, _⟩ := hpart_j j hj
    set Lj := partGrid (ctLv0 c / 4) (j + 1)
    set ℓj := min Lj 1
    set τj := tau0 Lj
    have hLj_pos : 0 < Lj := by linarith
    have hℓ_lb : b₀ * c ^ (-(2 / 21 : ℝ)) ≤ ℓj := by
      rw [hb₀]
      have : a₀ / 16 * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c / 16 := by linarith
      exact le_min (by linarith only [this, hLj_lo]) hc_b
    have hκ1 : κ_min * c ^ (-(2 / 21 : ℝ)) ≤ ℓj :=
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hc16_pos.le).trans hℓ_lb
    have hτ_pos : 0 < τj := tau0_pos hLj_pos
    have hτ_lb : κ_min * c ^ (-(1 / 21 : ℝ)) ≤ τj := by
      have hsq : (4 / 5 : ℝ) * ℓj ≤ τj ^ 2 := by
        nlinarith only [min_le_left Lj 1, tau0_sq_ge hLj_pos]
      have hpow_sq : (κ_min * c ^ (-(1 / 21 : ℝ))) ^ 2 ≤ (4 / 5 : ℝ) * ℓj := by
        have h1 : κ_min ^ 2 ≤ (4 / 5 : ℝ) * b₀ := by
          have : κ_min ≤ Real.sqrt (4 / 5 * b₀) := min_le_right _ _
          have := pow_le_pow_left₀ hκmin_pos.le this 2
          rwa [Real.sq_sqrt (by positivity)] at this
        have h2 : (c ^ (-(1 / 21 : ℝ))) ^ 2 = c ^ (-(2 / 21 : ℝ)) := by
          rw [← Real.rpow_natCast (c ^ (-(1 / 21 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
        rw [mul_pow, h2]
        calc κ_min ^ 2 * c ^ (-(2 / 21 : ℝ)) ≤ (4 / 5 * b₀) * c ^ (-(2 / 21 : ℝ)) :=
              mul_le_mul_of_nonneg_right h1 hc16_pos.le
          _ = 4 / 5 * (b₀ * c ^ (-(2 / 21 : ℝ))) := by ring
          _ ≤ 4 / 5 * ℓj := by gcongr
      have hsq_le : (κ_min * c ^ (-(1 / 21 : ℝ))) ^ 2 ≤ τj ^ 2 := hpow_sq.trans hsq
      nlinarith only [hsq_le, mul_nonneg hκmin_pos.le (Real.rpow_nonneg hc0.le (-(1 / 21 : ℝ))), hτ_pos]
    have heps_ℓ : nearEps c ≤ ℓj / 600 := by
      calc nearEps c ≤ b₀ / 600 * c ^ (-(2 / 21 : ℝ)) := hc_eps
        _ = (b₀ * c ^ (-(2 / 21 : ℝ))) / 600 := by ring
        _ ≤ ℓj / 600 := by gcongr
    have hom_supp1 : ∀ y, y ∉ Icc (Lj - ℓj / 150) (Lj + ℓj / 150) → nearOmega ε c R j y = 0 := by
      intro y hy; unfold nearOmega; rw [hchi_supp y hy, mul_zero]
    have hom_supp2 : ∀ y, y ∉ Icc (ctLv0 c / 2) (nearB c) → nearOmega ε c R j y = 0 := by
      intro y hy; unfold nearOmega; rw [nearCut_eq_zero_of_not_mem hL0 hy, mul_zero, zero_mul]
    have hcont := nearOmega_continuous hc0 hc1 hL0 (fun x hx => ⟨taperGrad x, htap_d x hx⟩) j
    have hom_bounds : ∀ y, 0 ≤ nearOmega ε c R j y ∧ nearOmega ε c R j y ≤ 1 := fun y => by
      unfold nearOmega
      by_cases hy0 : y ≤ 0
      · rw [nearCut_eq_zero_of_not_mem hL0 (fun h => by linarith [h.1]), mul_zero, zero_mul]
        exact ⟨le_rfl, zero_le_one⟩
      · rw [not_le] at hy0
        have ht := htap_bd y hy0
        have hsf := one_sub_boasSf_bounds hc1 y
        have hcu := nearCut_bounds c y
        have hch := hchi_bd y
        have h12 : ctTaper ε c R y * (1 - sFar c (c * (Real.exp y / π ^ 2))) ≤ 1 :=
          (mul_le_of_le_one_left hsf.1 ht.2).trans hsf.2
        have h123 : ctTaper ε c R y * (1 - sFar c (c * (Real.exp y / π ^ 2))) * nearCut c y ≤ 1 :=
          (mul_le_of_le_one_left hcu.1 h12).trans hcu.2
        exact ⟨mul_nonneg (mul_nonneg (mul_nonneg ht.1 hsf.1) hcu.1) hch.1,
          (mul_le_of_le_one_left hch.1 h123).trans hch.2⟩
    refine ⟨by linarith only [hLj_lo], hLj_hi, hℓ0, hκ1, hτ_lb, hτ_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact (mollConv_iteratedDeriv_eq heps_pos (by linarith only [hL0, hLB] : ctLv0 c / 2 ≤ nearB c) hcont hom_supp2).1 n
    · intro L
      exact mollConv_bounds heps_pos hcont (fun y => (hom_bounds y).1) (fun y => (hom_bounds y).2) L
    · intro L hL
      exact mollConv_eq_zero_of_support heps_pos hom_supp1 fun h => by
        dsimp only [ℓj] at h heps_ℓ hℓ0
        exact hL ⟨by linarith only [h.1, heps_ℓ, hℓ0], by linarith only [h.2, heps_ℓ, hℓ0]⟩
    · intro L hL
      exact mollConv_eq_zero_of_support heps_pos hom_supp2 fun h => by
        linarith only [hL, h.1, heps_le, hL0]
    · intro L hL
      exact mollConv_eq_zero_of_support heps_pos hom_supp2 fun h => by
        linarith only [hL, h.2, heps_le1]
    · intro L hL
      have hL_pos : 0 < L := by
        have : ℓj ≤ Lj := min_le_left _ _
        linarith only [hL.1, hLj_pos, this]
      have hw : |L - Lj| ≤ min Lj 1 / 100 := abs_le.2 ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
      exact tau0_block_window hL_pos hLj_pos hw
    · intro r L
      have heps_inv : (nearEps c)⁻¹ = c ^ (5 / 6 : ℝ) := by
        unfold nearEps; rw [← Real.rpow_neg hc0.le, neg_neg]
      rw [← heps_inv]
      exact hdrv_fn r heps_pos (by linarith only [hL0, hLB] : ctLv0 c / 2 ≤ nearB c) hcont hom_supp2
        (fun y => by rw [abs_of_nonneg (hom_bounds y).1]; exact (hom_bounds y).2) L

end FormalResearch.SignUncertainty
