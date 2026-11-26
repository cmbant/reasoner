/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctCompDPart2a
public import FormalResearch.SignUncertainty.FctPhiKill

/-!
# Compensator `D`: Part (2) — inner integral, `(fct:bump-1L)`, `(fct:bump-2L)`, and headline

Completes Part (2) of Lemma `fct:comp-D` (`constant_terms_five.tex`, lines 167–294):
- `saddleTau0_three_uctM_bounds`: `t₃ := τ₀(3 δ_L) ∈ (τ₁, 2 τ₁)` for small `τ₁`;
- `tendsto_odd_pole_zero`: pure odd-pole cancellation (`A/ε⁵ + B/ε³ + C/ε → L ⇒ L = 0`),
  eliminating all singular coefficient matching across the three finite-part pieces;
- `stripFp1` and `bg_fp_asymptotic`: exact background finite part at `p = 1` (reusing
  `FctPhiKill.laurent_Fstar`, `FctPhiKill.laurent_FCE`, `FctPhiKill.floor_tail_integral_and_asymp`)
  and odd-pole finite part at `p = 2`;
- `ibp_sinh_odd_pole` and `fp_linear_v_bound`: finite-part cancellation of the linear `v` term
  from the zeroed moments `ℳ_0[v] = ℳ_1[v] = ℳ_2[v] = 0`;
- `inner_Dstar_bounds`: inner integral `∫_0^{3 δ_L} D_*(L) dL = O_{K₄}(τ₁³ + |α| τ₁)` and
  inner finite parts on `(0, t₃]` for `p ∈ {1, 2}`;
- `fct_comp_D_part2`: bundled headline for all of `fct:comp-D` (2).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctCompD

open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.CohnElkies

/-! ### Helper 1: `t₃ := τ₀(3 δ_L) ∈ (τ₁, 2 τ₁)` -/

/-- For `0 < τ₁ ≤ 1/20`, `t₃ := FormalResearch.CohnElkies.tau0 (3 * uctM τ₁)` satisfies `τ₁ < t₃ < 2 * τ₁`. -/
lemma saddleTau0_three_uctM_bounds {τ₁ : ℝ} (hτ₁ : 0 < τ₁) (hτ₁_le : τ₁ ≤ 1 / 20) :
    τ₁ < FormalResearch.CohnElkies.tau0 (3 * uctM τ₁) ∧ FormalResearch.CohnElkies.tau0 (3 * uctM τ₁) < 2 * τ₁ := by
  have h3m : 0 < 3 * uctM τ₁ := mul_pos (by norm_num) (uctM_pos hτ₁)
  have ht3_pos : 0 < tau0 (3 * uctM τ₁) := tau0_pos h3m
  have ht3_eq : uctM (tau0 (3 * uctM τ₁)) = 3 * uctM τ₁ := ceEll_tau0 h3m
  constructor
  · by_contra hle
    push Not at hle
    have hmono := uctM_strictMonoOn.monotoneOn ht3_pos hτ₁ hle
    rw [ht3_eq] at hmono
    linarith [uctM_pos hτ₁]
  · -- Show `3 * uctM τ₁ < uctM (2 * τ₁)` via `FctPhiKill.ceEll_taylor4`
    have hx1 : 0 < π * τ₁ / 2 := by positivity
    have hx1_le : π * τ₁ / 2 ≤ 1 / 2 := by nlinarith [Real.pi_lt_four]
    have hx2 : 0 < π * (2 * τ₁) / 2 := by positivity
    have hx2_le : π * (2 * τ₁) / 2 ≤ 1 / 2 := by nlinarith [Real.pi_lt_four]
    have h1 := FctPhiKill.ceEll_taylor4 hx1 hx1_le
    have h2 := FctPhiKill.ceEll_taylor4 hx2 hx2_le
    rw [abs_le] at h1 h2
    set x : ℝ := π * τ₁ / 2
    have hx_lt : x ≤ 1 / 10 := by dsimp only [x]; nlinarith [Real.pi_lt_four]
    have hx2_eq : π * (2 * τ₁) / 2 = 2 * x := by dsimp only [x]; ring
    rw [hx2_eq] at h2
    have hupper : 3 * ceEll x ≤ x ^ 2 - (7 / 30) * x ^ 4 + 60 * x ^ 6 := by linarith [h1.2]
    have hlower : (4 / 3) * x ^ 2 - (56 / 45) * x ^ 4 - 1280 * x ^ 6 ≤ ceEll (2 * x) := by
      have h2' := h2.1
      have : (2 * x) ^ 2 / 3 - 7 / 90 * (2 * x) ^ 4 - 20 * (2 * x) ^ 6 =
          (4 / 3) * x ^ 2 - (56 / 45) * x ^ 4 - 1280 * x ^ 6 := by ring
      linarith
    have hx2_le_100 : x ^ 2 ≤ 1 / 100 := by
      have := pow_le_pow_left₀ hx1.le hx_lt 2; norm_num at this; exact this
    have hx4_le : x ^ 4 ≤ (1 / 100) * x ^ 2 := by
      rw [show x ^ 4 = x ^ 2 * x ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right hx2_le_100 (sq_nonneg x)
    have hx6_le : x ^ 6 ≤ (1 / 10000) * x ^ 2 := by
      rw [show x ^ 6 = x ^ 2 * x ^ 4 by ring]
      calc x ^ 2 * x ^ 4 ≤ (1 / 100) * ((1 / 100) * x ^ 2) :=
            mul_le_mul hx2_le_100 hx4_le (pow_nonneg hx1.le 4) (by norm_num)
        _ = (1 / 10000) * x ^ 2 := by ring
    have hstrict : 3 * uctM τ₁ < uctM (2 * τ₁) := by
      unfold uctM
      rw [hx2_eq]
      have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_pos hx1
      have hx4_nn : 0 ≤ x ^ 4 := pow_nonneg hx1.le 4
      linarith
    by_contra hle
    push Not at hle
    have hmono := uctM_strictMonoOn.monotoneOn (by positivity : (0 : ℝ) < 2 * τ₁) ht3_pos hle
    rw [ht3_eq] at hmono
    linarith

/-! ### Helper 2: Pure odd-pole cancellation (`A/ε⁵ + B/ε³ + C/ε → L ⇒ L = 0`) -/

/-- If a pure odd-pole Laurent polynomial `A/ε⁵ + B/ε³ + C/ε` converges to `L` as `ε ↓ 0`,
then `L = 0` (and in fact `A = B = C = 0`). -/
lemma tendsto_odd_pole_zero {A B C L : ℝ}
    (h : Tendsto (fun ε : ℝ => A / ε ^ 5 + B / ε ^ 3 + C / ε) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    L = 0 := by
  have hε0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hA : A = 0 := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ 5 * (A / ε ^ 5 + B / ε ^ 3 + C / ε)) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ 5 * L)) :=
      (hε0.pow 5).mul h
    rw [zero_pow (by norm_num : 5 ≠ 0), zero_mul] at h1
    have h2 : Tendsto (fun ε : ℝ => A + B * ε ^ 2 + C * ε ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
      simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul (hε0.pow 2))).add
        (tendsto_const_nhds.mul (hε0.pow 4))
    have heq : (fun ε : ℝ => ε ^ 5 * (A / ε ^ 5 + B / ε ^ 3 + C / ε)) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε => A + B * ε ^ 2 + C * ε ^ 4 := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hne : ε ≠ 0 := (mem_Ioi.mp hε).ne'
      field_simp [hne]
    exact tendsto_nhds_unique h2 (h1.congr' heq)
  subst hA
  simp only [zero_div, zero_add] at h
  have hB : B = 0 := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ 3 * (B / ε ^ 3 + C / ε)) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ 3 * L)) :=
      (hε0.pow 3).mul h
    rw [zero_pow (by norm_num : 3 ≠ 0), zero_mul] at h1
    have h2 : Tendsto (fun ε : ℝ => B + C * ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 B) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul (hε0.pow 2))
    have heq : (fun ε : ℝ => ε ^ 3 * (B / ε ^ 3 + C / ε)) =ᶠ[𝓝[>] (0 : ℝ)] fun ε => B + C * ε ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hne : ε ≠ 0 := (mem_Ioi.mp hε).ne'
      field_simp [hne]
    exact tendsto_nhds_unique h2 (h1.congr' heq)
  subst hB
  simp only [zero_div, zero_add] at h
  have hC : C = 0 := by
    have h1 : Tendsto (fun ε : ℝ => ε * (C / ε)) (𝓝[>] (0 : ℝ)) (𝓝 (0 * L)) := hε0.mul h
    rw [zero_mul] at h1
    have heq : (fun ε : ℝ => ε * (C / ε)) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => C := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_div_cancel₀ C (mem_Ioi.mp hε).ne'
    exact tendsto_nhds_unique tendsto_const_nhds (h1.congr' heq)
  subst hC
  simp only [zero_div] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-! ### Helper 3: Background finite parts at `p = 1` and `p = 2` -/

/-- The finite part `f.p. ∫_0^∞ (I_osc^{H_0}(L) - I_fl(L)) / L dL` as defined in `fct:comp-D` (2):
`lim_{ε↓0} [∫_ε^∞ (α_osc |H_0(it)| - α_fl m'(t)/m(t)^{3/2}) / m(t) dt - c_{-1}(H_0) / ε]`. -/
noncomputable def stripFp1 (kind : StripKernelChoice) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ =>
    (∫ t in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
      uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t) - stripCneg1 kind / ε

/-- Integrability of `(α_osc |H_0(it)| - α_fl m'(t)/m(t)^{3/2}) / m(t)^p` on `Ioi ε` for `ε > 0`, `p ∈ {1, 2}`,
and its odd-pole Laurent expansion as `ε ↓ 0`:
- at `p = 1`, the limit after subtracting `stripCneg1 kind / ε` exists and equals `stripFp1 kind`;
- at `p = 2`, the limit after subtracting `A/ε⁵ + B/ε³ + C/ε` exists for some fixed constants `A, B, C, L₂`. -/
lemma bg_fp_asymptotic (kind : StripKernelChoice) :
    (∀ {p : ℕ} {ε : ℝ}, 1 ≤ p → 0 < ε →
      IntegrableOn (fun t : ℝ => (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
        uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p) (Ioi ε)) ∧
    Tendsto (fun ε : ℝ =>
      (∫ t in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
        uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t) - stripCneg1 kind / ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (stripFp1 kind)) ∧
    ∃ A B C L₂ : ℝ, Tendsto (fun ε : ℝ =>
      (∫ t in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
        uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ 2) -
        (A / ε ^ 5 + B / ε ^ 3 + C / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 L₂) := by
  -- Helper: `F1 t := α_osc |H_0(it)| / m(t)` and `G1 t := α_fl m'(t) / m(t)^{5/2}`
  let F1 : ℝ → ℝ := fun t => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t
  let G1 : ℝ → ℝ := fun t => uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ)
  have hαo_nn : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
  have hαfl_pos : 0 < uctAlphaFl := by
    unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
  -- Reuse `FctPhiKill.laurent_Fstar` / `laurent_FCE` and `FctPhiKill.floor_tail_integral_and_asymp`!
  have hF1_laurent : ContinuousOn F1 (Ioi 0) ∧
      ∃ b0 b2 b4 b6 C_R : ℝ, 0 ≤ C_R ∧
        (∀ t ∈ Ioc (0 : ℝ) 1,
          |F1 t - (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + (stripCneg1 kind + (7 / 20) * uctAlphaOsc) / t ^ 2 +
            b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)| ≤ C_R * t ^ 8) := by
    cases kind
    · obtain ⟨hc, b0, b2, b4, b6, C_R, hCR, hsm, _⟩ := FctPhiKill.laurent_Fstar
      refine ⟨hc, b0, b2, b4, b6, C_R, hCR, fun t ht => ?_⟩
      have hcoeff : stripCneg1 .star + (7 / 20 : ℝ) * uctAlphaOsc = (27 / 10 : ℝ) * uctAlphaOsc := by
        unfold stripCneg1; ring
      rw [hcoeff]; exact hsm t ht
    · obtain ⟨hc, b0, b2, b4, b6, C_R, hCR, hsm, _⟩ := FctPhiKill.laurent_FCE
      refine ⟨hc, b0, b2, b4, b6, C_R, hCR, fun t ht => ?_⟩
      have hcoeff : stripCneg1 .ce + (7 / 20 : ℝ) * uctAlphaOsc = -(3 / 10 : ℝ) * uctAlphaOsc := by
        unfold stripCneg1; ring
      rw [hcoeff]; exact hsm t ht
  obtain ⟨hF1_cont, b0, b2, b4, b6, C_R, hCR_nn, hF1_sm⟩ := hF1_laurent
  obtain ⟨hfl_tail, C_fl, hCfl_nn, hfl_asymp⟩ := FctPhiKill.floor_tail_integral_and_asymp
  -- Integrability of `F1 t / m(t)^{p-1}` and `G1 t / m(t)^{p-1}` on `Ioi ε` for `p ≥ 1`, `ε > 0`
  have hF_int : ∀ {p : ℕ} {ε : ℝ}, 1 ≤ p → 0 < ε →
      IntegrableOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p) (Ioi ε) := by
    intro p ε hp hε
    have hm_pos : 0 < uctM ε := uctM_pos hε
    have hdom := FctPhiKill.integrableOn_inv_pow_Ioi hε (m := 2) (by norm_num)
    set K : ℝ := uctAlphaOsc * (1 + π ^ 2 / 4) / uctM ε ^ p
    have hpt : ∀ t ∈ Ioi ε, ‖uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p‖ ≤ K * t ^ (-(2 : ℤ)) := by
      intro t ht
      have ht0 : 0 < t := hε.trans ht
      have hm_ge : uctM ε ^ p ≤ uctM t ^ p := pow_le_pow_left₀ hm_pos.le (uctM_strictMonoOn.monotoneOn hε ht0 (le_of_lt ht)) p
      have hH := (norm_stripH0_imag_le kind ht0).1
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hαo_nn (norm_nonneg _)) (pow_nonneg (uctM_pos ht0).le p)),
        show (-(2 : ℤ)) = -((2 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
      calc uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p
          ≤ uctAlphaOsc * ((1 + π ^ 2 / 4) / t ^ 2) / uctM ε ^ p :=
            div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hH hαo_nn) (pow_pos hm_pos p) hm_ge
        _ = K * (t ^ 2)⁻¹ := by dsimp only [K]; field_simp [ht0.ne', (pow_pos hm_pos p).ne']
    have hcont : ContinuousOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p) (Ioi ε) := by
      have hm_c : ContinuousOn uctM (Ioi 0) := fun t ht => (hasDerivAt_uctM ht).continuousAt.continuousWithinAt
      have heq : EqOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p)
          (fun t => F1 t / uctM t ^ (p - 1)) (Ioi ε) := fun t ht => by
        dsimp only [F1]
        have hm0 : uctM t ≠ 0 := (uctM_pos (hε.trans ht)).ne'
        rw [div_div, ← pow_succ', show (p - 1) + 1 = p by omega]
      refine ContinuousOn.congr ?_ heq
      exact (hF1_cont.div (hm_c.pow (p - 1)) fun t ht => pow_ne_zero _ (uctM_pos ht).ne').mono fun t ht => hε.trans ht
    exact (hdom.1.const_mul K).mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  have hG_int : ∀ {p : ℕ} {ε : ℝ}, 1 ≤ p → 0 < ε →
      IntegrableOn (fun t : ℝ => uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ) / uctM t ^ p) (Ioi ε) := by
    intro p ε hp hε
    have hm_pos : 0 < uctM ε := uctM_pos hε
    have hg1 := (hfl_tail ε hε).1
    have hpt : ∀ t ∈ Ioi ε, ‖uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ) / uctM t ^ p‖ ≤
        (1 / uctM ε ^ (p - 1)) * G1 t := by
      intro t ht
      have ht0 : 0 < t := hε.trans ht
      have hmt : 0 < uctM t := uctM_pos ht0
      have hpow : uctM t ^ (3 / 2 : ℝ) * uctM t ^ p = uctM t ^ (5 / 2 : ℝ) * uctM t ^ (p - 1) := by
        conv_lhs => rw [show p = 1 + (p - 1) by omega, pow_add, pow_one]
        rw [← mul_assoc, show uctM t ^ (3 / 2 : ℝ) * uctM t = uctM t ^ (5 / 2 : ℝ) by
          rw [← Real.rpow_add_one hmt.ne']; norm_num]
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := uctMderiv_pos ht0; positivity), div_div, hpow, ← div_div]
      dsimp only [G1]
      have hm_ge : uctM ε ^ (p - 1) ≤ uctM t ^ (p - 1) :=
        pow_le_pow_left₀ hm_pos.le (uctM_strictMonoOn.monotoneOn hε ht0 (le_of_lt ht)) (p - 1)
      have h1 : uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ) / uctM t ^ (p - 1) ≤
          uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ) / uctM ε ^ (p - 1) :=
        div_le_div_of_nonneg_left (by have := uctMderiv_pos ht0; positivity) (pow_pos hm_pos _) hm_ge
      refine h1.trans (le_of_eq ?_); ring
    have hcont : ContinuousOn (fun t : ℝ => uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ) / uctM t ^ p) (Ioi ε) := by
      have hm_c : ContinuousOn uctM (Ioi 0) := fun t ht => (hasDerivAt_uctM ht).continuousAt.continuousWithinAt
      have hmd_c : ContinuousOn uctMderiv (Ioi 0) := by
        unfold uctMderiv uctEllDeriv
        refine continuousOn_const.mul ((continuousOn_const.div ((continuousOn_const.mul continuousOn_id).div_const 2)
          fun t (ht : t ∈ Ioi (0 : ℝ)) => (div_pos (mul_pos Real.pi_pos ht) two_pos).ne').sub
          (continuousOn_const.div (Real.continuous_sinh.comp (continuous_const.mul ((continuous_const.mul continuous_id).div_const 2))).continuousOn
            fun t (ht : t ∈ Ioi (0 : ℝ)) => (Real.sinh_pos_iff.mpr (mul_pos two_pos (div_pos (mul_pos Real.pi_pos ht) two_pos))).ne'))
      exact (((continuousOn_const.mul hmd_c).div (hm_c.rpow_const fun t ht => Or.inl (uctM_pos ht).ne')
        fun t ht => (Real.rpow_pos_of_pos (uctM_pos ht) _).ne').div (hm_c.pow p)
        fun t ht => pow_ne_zero p (uctM_pos ht).ne').mono fun t ht => hε.trans ht
    exact (hg1.const_mul (1 / uctM ε ^ (p - 1))).mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  have hint_all : ∀ {p : ℕ} {ε : ℝ}, 1 ≤ p → 0 < ε →
      IntegrableOn (fun t : ℝ => (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
        uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p) (Ioi ε) := by
    intro p ε hp hε
    have hrew : (fun t : ℝ => (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
        uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p) =
        fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p -
          uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ) / uctM t ^ p := by ext t; ring
    rw [hrew]; exact (hF_int hp hε).sub (hG_int hp hε)
  refine ⟨hint_all, ?_, ?_⟩
  · -- Part 1 (`p = 1`): prove existence of the limit `L₁` ⇒ `Tendsto ... (𝓝 (stripFp1 kind))`!
    -- Split `∫_ε^∞ (F1 - G1) = ∫_ε^1 (F1 - S1) + ∫_ε^1 S1 + ∫_1^∞ F1 - ∫_ε^∞ G1`
    let S1 : ℝ → ℝ := fun t => 12 * uctAlphaOsc / π ^ 2 / t ^ 4 + (stripCneg1 kind + (7 / 20) * uctAlphaOsc) / t ^ 2
    have hR1_int : IntegrableOn (fun t : ℝ => F1 t - S1 t) (Ioc 0 1) := by
      have hcont : ContinuousOn (fun t : ℝ => F1 t - S1 t) (Ioc 0 1) :=
        (hF1_cont.mono Ioc_subset_Ioi_self).sub
          ((continuousOn_const.div (continuousOn_id.pow 4) fun t (ht : t ∈ Ioc (0 : ℝ) 1) => pow_ne_zero 4 ht.1.ne').add
            (continuousOn_const.div (continuousOn_id.pow 2) fun t (ht : t ∈ Ioc (0 : ℝ) 1) => pow_ne_zero 2 ht.1.ne'))
      set B : ℝ := |b0| + |b2| + |b4| + |b6| + C_R
      refine (integrableOn_const (C := B) (hs := measure_Ioc_lt_top.ne)).mono'
        (hcont.aestronglyMeasurable measurableSet_Ioc) (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
      have h1 := hF1_sm t ht
      have ht1 : t ≤ 1 := ht.2
      have ht0 : 0 ≤ t := ht.1.le
      have hrem : |F1 t - S1 t| ≤ |b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6| + C_R * t ^ 8 := by
        have hrew : F1 t - S1 t = (F1 t - (S1 t + b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)) +
            (b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6) := by ring
        rw [hrew]
        refine (abs_add_le _ _).trans (by
          have h1' : |F1 t - (S1 t + b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)| ≤ C_R * t ^ 8 := by
            simpa [S1, add_assoc] using h1
          linarith)
      have hpoly : |b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6| ≤ |b0| + |b2| + |b4| + |b6| := by
        have a1 : |b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6| ≤
            |b0| + |b2 * t ^ 2| + |b4 * t ^ 4| + |b6 * t ^ 6| :=
          (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
        rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_of_nonneg ht0] at a1
        have p2 : |b2| * t ^ 2 ≤ |b2| := mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht0 ht1)
        have p4 : |b4| * t ^ 4 ≤ |b4| := mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht0 ht1)
        have p6 : |b6| * t ^ 6 ≤ |b6| := mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht0 ht1)
        linarith
      have p8 : C_R * t ^ 8 ≤ C_R := mul_le_of_le_one_right hCR_nn (pow_le_one₀ ht0 ht1)
      rw [Real.norm_eq_abs]; dsimp only [B]; linarith
    set L₁ : ℝ := (∫ t in Ioc (0 : ℝ) 1, (F1 t - S1 t)) +
      (∫ t in Ioi (1 : ℝ), F1 t) - (4 * uctAlphaOsc / π ^ 2 + (stripCneg1 kind + (7 / 20) * uctAlphaOsc))
    have htend : Tendsto (fun ε : ℝ =>
        (∫ t in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
          uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t) - stripCneg1 kind / ε)
        (𝓝[>] (0 : ℝ)) (𝓝 L₁) := by
      -- For `0 < ε ≤ 1/4`, rewrite the expression cleanly!
      have heq_ev : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
          (∫ (t : ℝ) in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
            uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t) - stripCneg1 kind / ε =
          (∫ (t : ℝ) in Ioc ε 1, (F1 t - S1 t)) + (∫ (t : ℝ) in Ioi (1 : ℝ), F1 t) -
            (4 * uctAlphaOsc / π ^ 2 + (stripCneg1 kind + (7 / 20) * uctAlphaOsc)) -
            ((2 / 3) * uctAlphaFl * uctM ε ^ (-(3 / 2 : ℝ)) -
              (4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) + 7 * uctAlphaOsc / (20 * ε))) := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with ε hε
        have hε0 : 0 < ε := hε.1
        have hε1 : ε < 1 := by linarith [hε.2]
        have hF_ε : IntegrableOn F1 (Ioi ε) := by simpa [F1] using hF_int (p := 1) le_rfl hε0
        have hG_ε : IntegrableOn G1 (Ioi ε) := (hfl_tail ε hε0).1
        have hrew_fg : (∫ t in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
            uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t) =
            (∫ t in Ioi ε, F1 t) - ∫ t in Ioi ε, G1 t := by
          rw [← integral_sub hF_ε hG_ε]
          refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          have hmt := uctM_pos (hε0.trans ht)
          dsimp only [F1, G1]
          rw [sub_div, div_div, show uctM t ^ (3 / 2 : ℝ) * uctM t = uctM t ^ (5 / 2 : ℝ) by
            rw [← Real.rpow_add_one hmt.ne']; norm_num]
        rw [hrew_fg, (hfl_tail ε hε0).2]
        -- Split `∫_ε^∞ F1 = ∫_ε^1 F1 + ∫_1^∞ F1`
        have hsplit : (∫ t in Ioi ε, F1 t) = (∫ t in Ioc ε 1, F1 t) + ∫ t in Ioi (1 : ℝ), F1 t := by
          rw [← Ioc_union_Ioi_eq_Ioi hε1.le, setIntegral_union
            (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
            measurableSet_Ioi (hF_ε.mono_set Ioc_subset_Ioi_self) (hF_ε.mono_set fun x hx => hε1.trans hx)]
        rw [hsplit]
        -- Compute `∫_ε^1 S1 t dt` explicitly by FTC!
        have hS1_int : IntegrableOn S1 (Ioc ε 1) :=
          ((continuousOn_const.div (continuousOn_id.pow 4) fun t (ht : t ∈ Icc ε 1) => pow_ne_zero 4 (lt_of_lt_of_le hε0 ht.1).ne').add
            (continuousOn_const.div (continuousOn_id.pow 2) fun t (ht : t ∈ Icc ε 1) => pow_ne_zero 2 (lt_of_lt_of_le hε0 ht.1).ne')).integrableOn_Icc.mono_set Ioc_subset_Icc_self
        have hS1_val : (∫ t in Ioc ε 1, S1 t) =
            4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) + (stripCneg1 kind + (7 / 20) * uctAlphaOsc) / ε -
              (4 * uctAlphaOsc / π ^ 2 + (stripCneg1 kind + (7 / 20) * uctAlphaOsc)) := by
          rw [← intervalIntegral.integral_of_le hε1.le]
          let P : ℝ → ℝ := fun t => -(4 * uctAlphaOsc / π ^ 2) / t ^ 3 - (stripCneg1 kind + (7 / 20) * uctAlphaOsc) / t
          have hd : ∀ t ∈ uIcc ε 1, HasDerivAt P (S1 t) t := fun t ht => by
            rw [uIcc_of_le hε1.le] at ht
            have ht0 : t ≠ 0 := (lt_of_lt_of_le hε0 ht.1).ne'
            have hd1 : HasDerivAt (fun s => -(4 * uctAlphaOsc / π ^ 2) / s ^ 3) (12 * uctAlphaOsc / π ^ 2 / t ^ 4) t := by
              have := ((hasDerivAt_pow 3 t).inv (pow_ne_zero 3 ht0)).const_mul (-(4 * uctAlphaOsc / π ^ 2))
              refine this.congr_deriv ?_; field_simp [ht0, Real.pi_ne_zero]; ring
            have hd2 : HasDerivAt (fun s => (stripCneg1 kind + (7 / 20) * uctAlphaOsc) / s)
                (-(stripCneg1 kind + (7 / 20) * uctAlphaOsc) / t ^ 2) t := by
              have := (hasDerivAt_inv ht0).const_mul (stripCneg1 kind + (7 / 20) * uctAlphaOsc)
              refine this.congr_deriv ?_; field_simp [ht0]
            exact (hd1.sub hd2).congr_deriv (by dsimp only [S1]; ring)
          have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le hε1.le).mpr hS1_int)
          rw [hftc]; dsimp only [P]; field_simp [hε0.ne', Real.pi_ne_zero]; ring
        have hF1_split : (∫ t in Ioc ε 1, F1 t) = (∫ t in Ioc ε 1, (F1 t - S1 t)) + ∫ t in Ioc ε 1, S1 t := by
          have := integral_sub (hF_ε.mono_set Ioc_subset_Ioi_self) hS1_int; linarith
        rw [hF1_split, hS1_val]; field_simp [hε0.ne', Real.pi_ne_zero]; ring
      -- Pass to `ε ↓ 0`!
      have h1 : Tendsto (fun ε : ℝ => ∫ t in Ioc ε 1, (F1 t - S1 t)) (𝓝[>] (0 : ℝ))
          (𝓝 (∫ t in Ioc (0 : ℝ) 1, (F1 t - S1 t))) := by
        have hinter0 : Ioi (0 : ℝ) ∩ Ioc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 := by
          ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
          exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
        have hind_int : IntegrableOn ((Ioc (0 : ℝ) 1).indicator (fun t => F1 t - S1 t)) (Ioi (0 : ℝ)) volume := by
          rw [integrableOn_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1)).nullMeasurableSet]
          exact hR1_int.mono_set inter_subset_left
        have h := FctPhiKill.tendsto_setIntegral_Ioi_zero hind_int
        have hrew_0 : (∫ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator (fun t => F1 t - S1 t) t) =
            ∫ t in Ioc (0 : ℝ) 1, (F1 t - S1 t) := by
          rw [setIntegral_indicator measurableSet_Ioc, hinter0]
        rw [hrew_0] at h
        refine h.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
        rw [setIntegral_indicator measurableSet_Ioc]
        have : Ioi ε ∩ Ioc (0 : ℝ) 1 = Ioc ε 1 := by
          ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
          exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, hε.1.trans h1, h2⟩⟩
        rw [this]
      have h2 : Tendsto (fun ε : ℝ => (2 / 3) * uctAlphaFl * uctM ε ^ (-(3 / 2 : ℝ)) -
          (4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) + 7 * uctAlphaOsc / (20 * ε))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hid0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        refine squeeze_zero_norm' ?_ (by simpa using (tendsto_const_nhds (x := C_fl)).mul hid0)
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with ε hε
        rw [Real.norm_eq_abs]; exact hfl_asymp ε hε.1 hε.2.le
      have hlim := ((h1.add (tendsto_const_nhds (x := ∫ t in Ioi (1 : ℝ), F1 t))).sub
        (tendsto_const_nhds (x := 4 * uctAlphaOsc / π ^ 2 + (stripCneg1 kind + (7 / 20) * uctAlphaOsc)))).sub h2
      rw [sub_zero] at hlim
      exact hlim.congr' (heq_ev.mono fun _ h => h.symm)
    rw [show stripFp1 kind = L₁ from htend.limUnder_eq]
    exact htend
  · -- Part 2 (`p = 2`): smooth even Taylor expansion of `t^6 * (F1(t) - G1(t)) / m(t)` on `(-1/4, 1/4)`!
    let hFac : ℝ → ℝ := fun t =>
      let sQ := (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re
      match kind with
      | .ce => 1 / sQ ^ 2
      | .star => 1 / sQ ^ 2 + (π * t / 2) ^ 2 / Real.cosh (π * t / 2) ^ 2
    let g2 : ℝ → ℝ := fun t => uctAlphaOsc * hFac t / mQ t ^ 2 - uctAlphaFl * mD t / mQ t ^ (7 / 2 : ℝ)
    have hsQ_cd : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re) (Ioo (-1 / 4) (1 / 4)) :=
      (Complex.reCLM.contDiff.comp (CtOuter.differentiable_sinhQ.contDiff.restrict_scalars ℝ |>.comp
        (Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).div_const 2)))).contDiffOn
    have hsQ_ne : ∀ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4), (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re ^ 2 ≠ 0 := fun t ht => by
      have hx2 : ‖((π * t / 2 : ℝ) : ℂ)‖ ≤ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos, show |(2 : ℝ)| = 2 by norm_num]
        have : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        nlinarith [Real.pi_lt_four, abs_nonneg t]
      exact pow_ne_zero 2 (CtOuter.re_sinhQ_pos hx2).ne'
    have hhFac_cd : ContDiffOn ℝ (⊤ : ℕ∞) hFac (Ioo (-1 / 4) (1 / 4)) := by
      dsimp only [hFac]; cases kind
      · exact (contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne).add
          ((((contDiff_const.mul contDiff_id).div_const 2).pow 2).contDiffOn.div
            (((Real.contDiff_cosh.comp ((contDiff_const.mul contDiff_id).div_const 2)).pow 2).contDiffOn)
            fun _ _ => pow_ne_zero 2 (Real.cosh_pos _).ne')
      · exact contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne
    have hhFac_even : ∀ t : ℝ, hFac (-t) = hFac t := fun t => by
      have hq : CtOuter.sinhQ ((π * -t / 2 : ℝ) : ℂ) = CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ) := by
        rw [show (π * -t / 2 : ℝ) = -(π * t / 2) by ring, Complex.ofReal_neg]
        unfold CtOuter.sinhQ; refine tsum_congr fun n => ?_; rw [(even_two_mul n).neg_pow]
      dsimp only [hFac]; cases kind
      · rw [hq, show π * -t / 2 = -(π * t / 2) by ring, Real.cosh_neg, neg_sq]
      · rw [hq]
    have hg2_cd : ContDiffOn ℝ (⊤ : ℕ∞) g2 (Ioo (-1 / 4) (1 / 4)) := by
      refine ((contDiffOn_const.mul hhFac_cd).div (contDiffOn_mQ.pow 2) fun t ht =>
        pow_ne_zero 2 (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne').sub
        ((contDiffOn_const.mul contDiffOn_mD).div
          (contDiffOn_mQ.rpow_const_of_ne fun t ht => (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne')
          fun t ht => (Real.rpow_pos_of_pos (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)) _).ne')
    have hg2_even : ∀ t : ℝ, |t| < 1 / 4 → g2 (-t) = g2 t := fun t ht => by
      dsimp only [g2]; rw [hhFac_even, mQ_even, mD_even ht]
    obtain ⟨a, C2, hC2_nn, ha_bd⟩ := even_smooth_taylor_bound hg2_cd hg2_even 3
    let f2 : ℝ → ℝ := fun t => (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
      uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ 2
    let S2 : ℝ → ℝ := fun t => a 0 / t ^ 6 + a 1 / t ^ 4 + a 2 / t ^ 2
    have hf2_eq : ∀ t ∈ Ioc (0 : ℝ) (1 / 8), f2 t = g2 t / t ^ 6 := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have ht14 : t < 1 / 4 := by linarith [ht.2]
      have hmQ_pos : 0 < mQ t := mQ_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)
      have hh : ‖stripH0 kind ((t : ℂ) * Complex.I)‖ = hFac t / t ^ 2 := by
        have hx : 0 < π * t / 2 := by positivity
        have hsQ : (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re = Real.sinh (π * t / 2) / (π * t / 2) := by
          rw [CtOuter.sinhQ_ofReal hx.ne', Complex.ofReal_re]
        have hsh : Real.sinh (π * t / 2) ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
        dsimp only [hFac]; rw [hsQ]; cases kind
        · rw [norm_stripH0_star_imag ht0]; field_simp [ht0.ne', Real.pi_ne_zero, hsh, (Real.cosh_pos _).ne']; ring
        · rw [norm_stripH0_ce_imag ht0]; field_simp [ht0.ne', Real.pi_ne_zero, hsh]; ring
      have hrpow1 : (t ^ 2 * mQ t) ^ (3 / 2 : ℝ) = t ^ 3 * mQ t ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow (sq_nonneg t) hmQ_pos.le, ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]; norm_num
      have hrpow2 : mQ t ^ (3 / 2 : ℝ) * mQ t ^ 2 = mQ t ^ (7 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (mQ t) 2, ← Real.rpow_add hmQ_pos]; norm_num
      dsimp only [f2, g2]
      rw [hh, uctM_eq_sq_mul_mQ ht0, uctMderiv_eq_mul_mD ht0 ht14, hrpow1, sub_div, mul_pow, div_div,
        show t ^ 3 * mQ t ^ (3 / 2 : ℝ) * ((t ^ 2) ^ 2 * mQ t ^ 2) = t ^ 7 * mQ t ^ (7 / 2 : ℝ) by
          rw [← hrpow2]; ring]
      field_simp [ht0.ne', hmQ_pos.ne', (Real.rpow_pos_of_pos hmQ_pos (7 / 2 : ℝ)).ne']
    have hR2_int : IntegrableOn (fun t : ℝ => f2 t - S2 t) (Ioc 0 (1 / 8)) := by
      have hcont : ContinuousOn (fun t : ℝ => f2 t - S2 t) (Ioc 0 (1 / 8)) := by
        refine ContinuousOn.congr ?_ (fun t ht => by rw [hf2_eq t ht])
        exact ((hg2_cd.continuousOn.mono fun t (ht : t ∈ Ioc (0 : ℝ) (1 / 8)) => ⟨by linarith [ht.1], by linarith [ht.2]⟩).div
          (continuousOn_id.pow 6) fun t (ht : t ∈ Ioc (0 : ℝ) (1 / 8)) => pow_ne_zero 6 ht.1.ne').sub
          (((continuousOn_const.div (continuousOn_id.pow 6) fun t (ht : t ∈ Ioc (0 : ℝ) (1 / 8)) => pow_ne_zero 6 ht.1.ne').add
            (continuousOn_const.div (continuousOn_id.pow 4) fun t (ht : t ∈ Ioc (0 : ℝ) (1 / 8)) => pow_ne_zero 4 ht.1.ne')).add
            (continuousOn_const.div (continuousOn_id.pow 2) fun t (ht : t ∈ Ioc (0 : ℝ) (1 / 8)) => pow_ne_zero 2 ht.1.ne'))
      refine (integrableOn_const (C := C2) (hs := measure_Ioc_lt_top.ne)).mono'
        (hcont.aestronglyMeasurable measurableSet_Ioc) (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
      have ht0 : 0 < t := ht.1
      rw [hf2_eq t ht, Real.norm_eq_abs]
      have hsum : ∑ j : Fin 3, a j * t ^ (2 * j.1) = a 0 + a 1 * t ^ 2 + a 2 * t ^ 4 := by
        rw [Fin.sum_univ_three]; simp
      have hrew : g2 t / t ^ 6 - S2 t = (g2 t - ∑ j : Fin 3, a j * t ^ (2 * j.1)) / t ^ 6 := by
        rw [hsum]; dsimp only [S2]; field_simp [ht0.ne']
      rw [hrew, abs_div, abs_pow, abs_of_pos ht0]
      have h1 := ha_bd t ⟨ht0.le, ht.2⟩
      rw [div_le_iff₀ (pow_pos ht0 6)]; exact h1
    refine ⟨a 0 / 5, a 1 / 3, a 2,
      (∫ t in Ioc (0 : ℝ) (1 / 8), (f2 t - S2 t)) + (∫ t in Ioi (1 / 8 : ℝ), f2 t) -
        (a 0 / 5 * (8 : ℝ) ^ 5 + a 1 / 3 * (8 : ℝ) ^ 3 + a 2 * 8), ?_⟩
    have heq_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (∫ t in Ioi ε, f2 t) - (a 0 / 5 / ε ^ 5 + a 1 / 3 / ε ^ 3 + a 2 / ε) =
        (∫ t in Ioc ε (1 / 8), (f2 t - S2 t)) + (∫ t in Ioi (1 / 8 : ℝ), f2 t) -
          (a 0 / 5 * (8 : ℝ) ^ 5 + a 1 / 3 * (8 : ℝ) ^ 3 + a 2 * 8) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with ε hε
      have hε0 : 0 < ε := hε.1
      have hf2_ε : IntegrableOn f2 (Ioi ε) := hint_all (p := 2) (by norm_num) hε0
      have hsplit : (∫ t in Ioi ε, f2 t) = (∫ t in Ioc ε (1 / 8), f2 t) + ∫ t in Ioi (1 / 8 : ℝ), f2 t := by
        rw [← Ioc_union_Ioi_eq_Ioi hε.2.le, setIntegral_union
          (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
          measurableSet_Ioi (hf2_ε.mono_set Ioc_subset_Ioi_self) (hf2_ε.mono_set fun x hx => hε.2.trans hx)]
      have hS2_int : IntegrableOn S2 (Ioc ε (1 / 8)) :=
        ((((continuousOn_const.div (continuousOn_id.pow 6) fun t (ht : t ∈ Icc ε (1 / 8)) => pow_ne_zero 6 (lt_of_lt_of_le hε0 ht.1).ne').add
          (continuousOn_const.div (continuousOn_id.pow 4) fun t (ht : t ∈ Icc ε (1 / 8)) => pow_ne_zero 4 (lt_of_lt_of_le hε0 ht.1).ne')).add
          (continuousOn_const.div (continuousOn_id.pow 2) fun t (ht : t ∈ Icc ε (1 / 8)) => pow_ne_zero 2 (lt_of_lt_of_le hε0 ht.1).ne'))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have hS2_val : (∫ t in Ioc ε (1 / 8), S2 t) =
          (a 0 / 5 / ε ^ 5 + a 1 / 3 / ε ^ 3 + a 2 / ε) -
            (a 0 / 5 * (8 : ℝ) ^ 5 + a 1 / 3 * (8 : ℝ) ^ 3 + a 2 * 8) := by
        rw [← intervalIntegral.integral_of_le hε.2.le]
        let P : ℝ → ℝ := fun t => -(a 0 / 5) / t ^ 5 - (a 1 / 3) / t ^ 3 - a 2 / t
        have hd : ∀ t ∈ uIcc ε (1 / 8), HasDerivAt P (S2 t) t := fun t ht => by
          rw [uIcc_of_le hε.2.le] at ht
          have ht0 : t ≠ 0 := (lt_of_lt_of_le hε0 ht.1).ne'
          have h5 : HasDerivAt (fun s => -(a 0 / 5) / s ^ 5) (a 0 / t ^ 6) t := by
            have := ((hasDerivAt_pow 5 t).inv (pow_ne_zero 5 ht0)).const_mul (-(a 0 / 5))
            refine this.congr_deriv ?_; field_simp [ht0]; ring
          have h3 : HasDerivAt (fun s => (a 1 / 3) / s ^ 3) (-(a 1) / t ^ 4) t := by
            have := ((hasDerivAt_pow 3 t).inv (pow_ne_zero 3 ht0)).const_mul (a 1 / 3)
            refine this.congr_deriv ?_; field_simp [ht0]; ring
          have h1 : HasDerivAt (fun s => a 2 / s) (-(a 2) / t ^ 2) t := by
            have := (hasDerivAt_inv ht0).const_mul (a 2)
            refine this.congr_deriv ?_; field_simp [ht0]
          exact ((h5.sub h3).sub h1).congr_deriv (by dsimp only [S2]; ring)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hε.2.le).mpr hS2_int)]
        dsimp only [P]; field_simp [hε0.ne']; ring
      have hsub := integral_sub (hf2_ε.mono_set Ioc_subset_Ioi_self) hS2_int
      rw [hsplit]; linarith
    have h1 : Tendsto (fun ε : ℝ => ∫ t in Ioc ε (1 / 8), (f2 t - S2 t)) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ t in Ioc (0 : ℝ) (1 / 8), (f2 t - S2 t))) := by
      have hinter0 : Ioi (0 : ℝ) ∩ Ioc (0 : ℝ) (1 / 8) = Ioc (0 : ℝ) (1 / 8) := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
        exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
      have hind_int : IntegrableOn ((Ioc (0 : ℝ) (1 / 8)).indicator (fun t => f2 t - S2 t)) (Ioi (0 : ℝ)) volume := by
        rw [integrableOn_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) (1 / 8))).nullMeasurableSet]
        exact hR2_int.mono_set inter_subset_left
      have h := FctPhiKill.tendsto_setIntegral_Ioi_zero hind_int
      rw [setIntegral_indicator measurableSet_Ioc, hinter0] at h
      refine h.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with ε hε
      rw [setIntegral_indicator measurableSet_Ioc]
      have : Ioi ε ∩ Ioc (0 : ℝ) (1 / 8) = Ioc ε (1 / 8) := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
        exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, hε.1.trans h1, h2⟩⟩
      rw [this]
    exact ((h1.add tendsto_const_nhds).sub tendsto_const_nhds).congr' (heq_ev.mono fun _ h => h.symm)

/-! ### Helper 4: Finite-part IBP cancellation for the linear `v` term -/

/-- Smooth odd remainder `sinhRem(t) = 1/sinh(πt) - 1/(πt)` on `(-1/2, 1/2)`. -/
noncomputable def sinhRem (t : ℝ) : ℝ :=
  (dslope (fun w : ℂ => (1 - CtOuter.sinhQ w) / CtOuter.sinhQ w) 0 ((π * t : ℝ) : ℂ)).re

lemma sinhRem_spec :
    ContDiffOn ℝ (⊤ : ℕ∞) sinhRem (Ioo (-1 / 2) (1 / 2)) ∧
    (∀ t : ℝ, |t| < 1 / 2 → sinhRem (-t) = -sinhRem t) ∧
    (∀ t : ℝ, 0 < t → t < 1 / 2 → (Real.sinh (π * t))⁻¹ = 1 / (π * t) + sinhRem t) := by
  let φ : ℂ → ℂ := fun w => (1 - CtOuter.sinhQ w) / CtOuter.sinhQ w
  have hφ_diff : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 2) :=
    (differentiableOn_const 1 |>.sub CtOuter.differentiable_sinhQ.differentiableOn).div
      CtOuter.differentiable_sinhQ.differentiableOn fun w hw => by
        rw [mem_ball_zero_iff] at hw
        exact CtOuter.sinhQ_ne_zero (hw.trans (by linarith [Real.pi_gt_three]))
  have hφ0 : φ 0 = 0 := by simp [φ, CtOuter.sinhQ_zero]
  have hd_diff : DifferentiableOn ℂ (dslope φ 0) (Metric.ball (0 : ℂ) 2) :=
    (differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).mpr hφ_diff
  have hd_cd : ContDiffOn ℂ (⊤ : ℕ∞) (dslope φ 0) (Metric.ball (0 : ℂ) 2) :=
    (hd_diff.analyticOnNhd Metric.isOpen_ball).contDiffOn Metric.isOpen_ball.uniqueDiffOn
  refine ⟨?_, ?_, ?_⟩
  · refine (Complex.reCLM.contDiff.comp_contDiffOn (hd_cd.restrict_scalars ℝ)).comp
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).contDiffOn fun t ht => ?_
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
    have : |t| < 1 / 2 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    nlinarith [Real.pi_lt_four, abs_nonneg t]
  · intro t _
    by_cases ht0 : t = 0
    · subst ht0
      have hφ_even : ∀ w : ℂ, φ (-w) = φ w := fun w => by
        dsimp only [φ]
        have hq : CtOuter.sinhQ (-w) = CtOuter.sinhQ w := by
          unfold CtOuter.sinhQ; refine tsum_congr fun n => ?_; rw [(even_two_mul n).neg_pow]
        rw [hq]
      have hd0 : dslope φ 0 0 = 0 := by
        rw [dslope_same]
        have h1 : HasDerivAt (fun w => φ (-w)) (-deriv φ 0) 0 := by
          have hd := (hφ_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).hasDerivAt
          have hd' : HasDerivAt φ (deriv φ 0) (-0) := by rwa [neg_zero]
          exact (hd'.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))).congr_deriv (by ring)
        have h2 : HasDerivAt (fun w => φ (-w)) (deriv φ 0) 0 := by
          simpa [hφ_even] using (hφ_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).hasDerivAt
        have h3 := h1.unique h2
        have : (2 : ℂ) * deriv φ 0 = 0 := by linear_combination -h3
        exact (mul_eq_zero.mp this).resolve_left (by norm_num)
      change (dslope φ 0 ((π * -0 : ℝ) : ℂ)).re = -(dslope φ 0 ((π * 0 : ℝ) : ℂ)).re
      simp only [neg_zero, mul_zero, Complex.ofReal_zero, hd0, Complex.zero_re]
    · have hne : ((π * t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht0)
      have hne' : ((π * -t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero (neg_ne_zero.mpr ht0))
      have hq : CtOuter.sinhQ ((π * -t : ℝ) : ℂ) = CtOuter.sinhQ ((π * t : ℝ) : ℂ) := by
        rw [mul_neg, Complex.ofReal_neg]; unfold CtOuter.sinhQ
        refine tsum_congr fun n => ?_; rw [(even_two_mul n).neg_pow]
      change (dslope φ 0 ((π * -t : ℝ) : ℂ)).re = -(dslope φ 0 ((π * t : ℝ) : ℂ)).re
      rw [dslope_of_ne _ hne', dslope_of_ne _ hne, slope_def_field, slope_def_field, hφ0, sub_zero, sub_zero,
        sub_zero, sub_zero]
      dsimp only [φ]
      rw [hq, mul_neg, Complex.ofReal_neg, div_neg, Complex.neg_re]
  · intro t ht0 ht1
    have hne : ((π * t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos Real.pi_pos ht0).ne'
    have hsh : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht0)).ne'
    have hq : CtOuter.sinhQ ((π * t : ℝ) : ℂ) = ((Real.sinh (π * t) / (π * t) : ℝ) : ℂ) :=
      CtOuter.sinhQ_ofReal (mul_pos Real.pi_pos ht0).ne'
    change (Real.sinh (π * t))⁻¹ = 1 / (π * t) + (dslope φ 0 ((π * t : ℝ) : ℂ)).re
    rw [dslope_of_ne _ hne, slope_def_field, hφ0, sub_zero, sub_zero]
    dsimp only [φ]
    rw [hq, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, ← Complex.ofReal_div, Complex.ofReal_re]
    field_simp [hsh, Real.pi_ne_zero, ht0.ne']; ring

/-- Exact `m`-th derivative of `t ↦ (sinh(πt))⁻¹` on `(0, 1/2)`:
`(-1)^m * m! / (π * t^{m+1}) + iteratedDeriv m sinhRem t`. -/
lemma iteratedDeriv_inv_sinh (m : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    iteratedDeriv m (fun s : ℝ => (Real.sinh (π * s))⁻¹) t =
      (-1 : ℝ) ^ m * (m.factorial : ℝ) / (π * t ^ (m + 1)) + iteratedDeriv m sinhRem t := by
  have hev : (fun s : ℝ => (Real.sinh (π * s))⁻¹) =ᶠ[𝓝 t] fun s => 1 / (π * s) + sinhRem s := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨ht0, ht1⟩] with s hs using sinhRem_spec.2.2 s hs.1 hs.2
  rw [(hev.iteratedDeriv m).eq_of_nhds]
  have h1_cd : ContDiffAt ℝ (m : WithTop ℕ∞) (fun s : ℝ => 1 / (π * s)) t :=
    (contDiffAt_const.div (contDiffAt_const.mul contDiffAt_id) (mul_pos Real.pi_pos ht0).ne')
  have h2_cd : ContDiffAt ℝ (m : WithTop ℕ∞) sinhRem t :=
    (sinhRem_spec.1.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, ht1⟩)).of_le (WithTop.coe_le_coe.mpr le_top)
  change iteratedDeriv m ((fun s => 1 / (π * s)) + sinhRem) t = _
  rw [iteratedDeriv_add h1_cd h2_cd]
  congr 1
  -- Compute `iteratedDeriv m (fun s => 1 / (π * s)) t = (-1)^m * m! / (π * t^{m+1})` by induction!
  suffices ∀ k : ℕ, ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun s : ℝ => (π * s)⁻¹) x = (-1 : ℝ) ^ k * (k.factorial : ℝ) / (π * x ^ (k + 1)) by
    simpa [one_div] using this m t ht0
  intro k; induction k with
  | zero => intro x hx; simp [one_div]
  | succ k ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have hev' : iteratedDeriv k (fun s : ℝ => (π * s)⁻¹) =ᶠ[𝓝 x]
        fun s => (-1 : ℝ) ^ k * (k.factorial : ℝ) / (π * s ^ (k + 1)) := by
      filter_upwards [Ioi_mem_nhds hx] with s hs using ih s hs
    rw [hev'.deriv_eq]
    have hd : HasDerivAt (fun s : ℝ => (-1 : ℝ) ^ k * (k.factorial : ℝ) / (π * s ^ (k + 1)))
        ((-1 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) / (π * x ^ (k + 2))) x := by
      have hpow : HasDerivAt (fun s : ℝ => (s ^ (k + 1))⁻¹)
          (-((k + 1 : ℕ) : ℝ) * x ^ k / (x ^ (k + 1)) ^ 2) x := by
        refine ((hasDerivAt_pow (k + 1) x).inv (pow_ne_zero _ hx.ne')).congr_deriv ?_
        push_cast; ring
      have hmul := hpow.const_mul ((-1 : ℝ) ^ k * (k.factorial : ℝ) / π)
      have hfun : (fun s : ℝ => (-1 : ℝ) ^ k * (k.factorial : ℝ) / π * (s ^ (k + 1))⁻¹) =
          fun s => (-1 : ℝ) ^ k * (k.factorial : ℝ) / (π * s ^ (k + 1)) := by
        ext s; ring
      rw [hfun] at hmul
      refine hmul.congr_deriv ?_
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ (-1 : ℝ)]
      have hexp2 : (x ^ (k + 1)) ^ 2 = x ^ k * x ^ (k + 2) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      field_simp [Real.pi_ne_zero, hx.ne']
      rw [hexp2]
    exact hd.deriv

/-- Finite-part IBP cancellation for `-ψ^{(2k+1)}(t) v(t)` (`k ∈ {0, 1, 2}`):
if `v ∈ C_c^∞((-10τ₁, 10τ₁))` is even with `v(0) = 0` and `fctMoment k v = 0`, then
`∫_ε^∞ (-ψ^{(2k+1)}(t)) v(t) dt - (A/ε³ + B/ε) → 0` as `ε ↓ 0` for some `A, B : ℝ`. -/
lemma ibp_sinh_odd_pole {v : ℝ → ℝ} {τ₁ : ℝ} (hτ₁ : 0 < τ₁) (hτ₁_le : τ₁ ≤ 1 / 40)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hv_even : ∀ t, v (-t) = v t) (hv0 : v 0 = 0)
    (hv_supp : Function.support v ⊆ Ioo (-(10 * τ₁)) (10 * τ₁))
    {k : ℕ} (hk : k ≤ 2) (hmom : fctMoment k v = 0) :
    ∃ A B : ℝ, Tendsto (fun ε : ℝ =>
      (∫ t in Ioi ε, (-iteratedDeriv (2 * k + 1) (fun s : ℝ => (Real.sinh (π * s))⁻¹) t) * v t) -
        (A / ε ^ 3 + B / ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let ψ : ℝ → ℝ := fun s => (Real.sinh (π * s))⁻¹
  have hψ_cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Ioi 0) :=
    (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).contDiffOn.inv
      fun s hs => (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hs)).ne'
  set R : ℝ := 11 * τ₁
  have hR_gt : 10 * τ₁ < R := by dsimp only [R]; linarith
  have hR_lt : R < 1 / 2 := by dsimp only [R]; linarith
  have hv_zero_ge : ∀ m : ℕ, ∀ t : ℝ, 10 * τ₁ < t → iteratedDeriv m v t = 0 := fun m t ht => by
    have hev : v =ᶠ[𝓝 t] 0 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      by_contra hne; exact absurd (hv_supp hne).2 (not_lt.mpr (le_of_lt hs))
    rw [(hev.iteratedDeriv m).eq_of_nhds, iteratedDeriv_const_zero]
  -- One-step IBP on `[ε, R]` for any `j, r : ℕ` with `0 < ε < R`:
  -- `∫_ε^R ψ^{(j+1)}(t) v^{(r)}(t) dt = -ψ^{(j)}(ε) v^{(r)}(ε) - ∫_ε^R ψ^{(j)}(t) v^{(r+1)}(t) dt`!
  have hibp_step : ∀ (j r : ℕ) {ε : ℝ}, 0 < ε → ε < R →
      (∫ t in ε..R, iteratedDeriv (j + 1) ψ t * iteratedDeriv r v t) =
        -(iteratedDeriv j ψ ε * iteratedDeriv r v ε) -
          ∫ t in ε..R, iteratedDeriv j ψ t * iteratedDeriv (r + 1) v t := by
    intro j r ε hε0 hεR
    have hcd_ψ : ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv m ψ) (Ioi 0) := fun m => by
      induction m with
      | zero => simpa only [iteratedDeriv_zero] using hψ_cd
      | succ m ih =>
        rw [show iteratedDeriv (m + 1) ψ = deriv (iteratedDeriv m ψ) by ext x; rw [iteratedDeriv_succ]]
        exact ih.deriv_of_isOpen isOpen_Ioi (by simp)
    have hd_u : ∀ t ∈ uIcc ε R, HasDerivAt (iteratedDeriv j ψ) (iteratedDeriv (j + 1) ψ t) t := fun t ht => by
      rw [uIcc_of_le hεR.le] at ht
      rw [iteratedDeriv_succ]
      exact ((hcd_ψ j).differentiableOn (by simp) |>.differentiableAt (isOpen_Ioi.mem_nhds (lt_of_lt_of_le hε0 ht.1))).hasDerivAt
    have hd_w : ∀ t ∈ uIcc ε R, HasDerivAt (iteratedDeriv r v) (iteratedDeriv (r + 1) v t) t := fun t _ => by
      rw [iteratedDeriv_succ]
      exact ((contDiff_iteratedDeriv_infty hv r).differentiable (by simp) t).hasDerivAt
    have hc_u' : IntervalIntegrable (iteratedDeriv (j + 1) ψ) volume ε R :=
      ((hcd_ψ (j + 1)).continuousOn.mono fun t ht => lt_of_lt_of_le hε0 (uIcc_of_le hεR.le ▸ ht).1).intervalIntegrable
    have hc_w' : IntervalIntegrable (iteratedDeriv (r + 1) v) volume ε R :=
      (contDiff_iteratedDeriv_infty hv (r + 1)).continuous.intervalIntegrable _ _
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hd_u hd_w hc_u' hc_w'
    -- `hparts : ∫ u * w' = u(R) w(R) - u(ε) w(ε) - ∫ u' * w`
    rw [hv_zero_ge r R hR_gt, mul_zero, zero_sub] at hparts
    linarith
  -- Repeated `(2*k+1)`-step IBP on `[ε, R]`!
  have hibp_full : ∀ {ε : ℝ}, 0 < ε → ε < R →
      (∫ t in Ioi ε, (-iteratedDeriv (2 * k + 1) ψ t) * v t) =
        (∑ j ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ j * iteratedDeriv (2 * k - j) ψ ε * iteratedDeriv j v ε) +
        ∫ t in Ioi ε, ψ t * iteratedDeriv (2 * k + 1) v t := by
    intro ε hε0 hεR
    -- Both `Ioi ε` integrals agree with `∫ ε..R` since `v^{(r)} = 0` on `Ioi (10 * τ₁)`!
    have hEq_Ioi : ∀ (f : ℝ → ℝ) (r : ℕ), ContinuousOn f (Ioi 0) →
        (∫ t in Ioi ε, f t * iteratedDeriv r v t) = ∫ t in ε..R, f t * iteratedDeriv r v t := by
      intro f r hf
      rw [intervalIntegral.integral_of_le hεR.le, ← Ioc_union_Ioi_eq_Ioi hεR.le]
      have h1 : IntegrableOn (fun t => f t * iteratedDeriv r v t) (Ioc ε R) :=
        ((hf.mul (contDiff_iteratedDeriv_infty hv r).continuous.continuousOn).mono
          fun t (ht : t ∈ Icc ε R) => lt_of_lt_of_le hε0 ht.1).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have h2 : IntegrableOn (fun t => f t * iteratedDeriv r v t) (Ioi R) :=
        (integrableOn_zero (μ := volume) (s := Ioi R)).congr_fun
          (fun t ht => by rw [hv_zero_ge r t (hR_gt.trans ht), mul_zero]) measurableSet_Ioi
      have hzero_R : (∫ t in Ioi R, f t * iteratedDeriv r v t) = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun t ht => by rw [hv_zero_ge r t (hR_gt.trans ht), mul_zero]
      rw [setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
        measurableSet_Ioi h1 h2, hzero_R, add_zero]
    have hcd_ψ : ∀ m : ℕ, ContinuousOn (iteratedDeriv m ψ) (Ioi 0) := fun m => by
      have : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv m ψ) (Ioi 0) := by
        induction m with
        | zero => simpa only [iteratedDeriv_zero] using hψ_cd
        | succ m ih =>
          rw [show iteratedDeriv (m + 1) ψ = deriv (iteratedDeriv m ψ) by ext x; rw [iteratedDeriv_succ]]
          exact ih.deriv_of_isOpen isOpen_Ioi (by simp)
      exact this.continuousOn
    have hL := hEq_Ioi (fun t => -iteratedDeriv (2 * k + 1) ψ t) 0 (hcd_ψ (2 * k + 1)).neg
    have hR_int := hEq_Ioi ψ (2 * k + 1) (by simpa only [iteratedDeriv_zero] using hcd_ψ 0)
    simp only [iteratedDeriv_zero] at hL
    rw [hL, hR_int]
    -- Apply `hibp_step` `2*k + 1` times!
    have hneg_pull : (∫ t in ε..R, (-iteratedDeriv (2 * k + 1) ψ t) * v t) =
        -(∫ t in ε..R, iteratedDeriv (2 * k + 1) ψ t * iteratedDeriv 0 v t) := by
      simp only [neg_mul, iteratedDeriv_zero, intervalIntegral.integral_neg]
    rw [hneg_pull]
    -- Induction on `n` for `0 ≤ n ≤ 2*k + 1`:
    have hind : ∀ n : ℕ, n ≤ 2 * k + 1 →
        -(∫ t in ε..R, iteratedDeriv (2 * k + 1) ψ t * iteratedDeriv 0 v t) =
          (∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * iteratedDeriv (2 * k - j) ψ ε * iteratedDeriv j v ε) +
          (-1 : ℝ) ^ (n + 1) * ∫ t in ε..R, iteratedDeriv (2 * k + 1 - n) ψ t * iteratedDeriv n v t := by
      intro n; induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        rw [ih (by omega), Finset.sum_range_succ]
        have hstep := hibp_step (2 * k - n) n hε0 hεR
        rw [show 2 * k - n + 1 = 2 * k + 1 - n by omega] at hstep
        rw [hstep, show 2 * k + 1 - (n + 1) = 2 * k - n by omega, pow_succ (-1 : ℝ) (n + 1),
          pow_succ (-1 : ℝ) n]
        ring
    have hdone := hind (2 * k + 1) le_rfl
    rw [Nat.sub_self, iteratedDeriv_zero, show (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]; exact (even_two_mul (k + 1)).neg_one_pow, one_mul] at hdone
    exact hdone
  -- The integral `∫_ε^∞ ψ(t) v^{(2k+1)}(t) dt → π * fctMoment k v = 0` as `ε ↓ 0`!
  have hint_tend : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, ψ t * iteratedDeriv (2 * k + 1) v t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hv_cs := hasCompactSupport_of_support_Ioo hv_supp
    have hint0 : IntegrableOn (fun t : ℝ => iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t)) (Ioi 0) := by
      have hodd : iteratedDeriv (2 * k + 1) v 0 = 0 := iteratedDeriv_odd_zero hv_even k
      have hcont : ContinuousOn (fun t : ℝ => iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t)) (Ioi 0) :=
        (contDiff_iteratedDeriv_infty hv (2 * k + 1)).continuous.continuousOn.div
          (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn
          fun t ht => (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
        (contDiff_iteratedDeriv_infty hv (2 * k + 2)).continuous.continuousOn
      have hpt : ∀ t ∈ Ioc (0 : ℝ) R, ‖iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t)‖ ≤ max M 0 / π := by
        intro t ht
        have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
          (fun x _ => (contDiff_iteratedDeriv_infty hv (2 * k + 1)).differentiable (by simp) x)
          (fun x hx => by
            rw [← iteratedDeriv_succ, show 2 * k + 1 + 1 = 2 * k + 2 by omega]
            exact (hM x ⟨hx.1, hx.2.trans ht.2⟩).trans (le_max_left M 0))
          (convex_Icc 0 t) ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩
        rw [hodd, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_pos ht.1] at hmv
        have hsh : π * t ≤ Real.sinh (π * t) := by
          have hd : ∀ x : ℝ, HasDerivAt (fun y => Real.sinh y - y) (Real.cosh x - 1) x := fun x =>
            (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
          have hm := monotoneOn_of_deriv_nonneg (f := fun y => Real.sinh y - y) (convex_Ici 0)
            (Real.continuous_sinh.sub continuous_id).continuousOn
            (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
            (fun x _ => by rw [(hd x).deriv]; linarith [Real.one_le_cosh x])
          have := hm (le_rfl : (0 : ℝ) ∈ Ici 0) (mul_pos Real.pi_pos ht.1).le (mul_pos Real.pi_pos ht.1).le
          simp only [Real.sinh_zero, sub_self] at this; linarith
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht.1))]
        calc |iteratedDeriv (2 * k + 1) v t| / Real.sinh (π * t)
            ≤ (max M 0 * t) / (π * t) :=
              div_le_div₀ (mul_nonneg (le_max_right M 0) ht.1.le) hmv (mul_pos Real.pi_pos ht.1) hsh
          _ = max M 0 / π := by field_simp [ht.1.ne']
      rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ R by dsimp only [R]; positivity), integrableOn_union]
      refine ⟨(integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
        ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
        (ae_restrict_of_forall_mem measurableSet_Ioc hpt),
        (integrableOn_zero (μ := volume) (s := Ioi R)).congr_fun
          (fun t ht => by rw [hv_zero_ge (2 * k + 1) t (hR_gt.trans ht), zero_div]) measurableSet_Ioi⟩
    have h0_val : (∫ t in Ioi (0 : ℝ), ψ t * iteratedDeriv (2 * k + 1) v t) = 0 := by
      have hrew : (fun t : ℝ => ψ t * iteratedDeriv (2 * k + 1) v t) =
          fun t => iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t) := by ext t; dsimp only [ψ]; ring
      rw [hrew]
      unfold fctMoment at hmom
      have : (1 / π : ℝ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hmom).resolve_left this
    have hint_ψ : IntegrableOn (fun t : ℝ => ψ t * iteratedDeriv (2 * k + 1) v t) (Ioi 0) :=
      hint0.congr_fun (fun t _ => by dsimp only [ψ]; ring) measurableSet_Ioi
    simpa [h0_val] using FctPhiKill.tendsto_setIntegral_Ioi_zero hint_ψ
  -- Finally, show the boundary sum `∑_{j < 2k+1} (-1)^j ψ^{(2k-j)}(ε) v^{(j)}(ε)` is `A/ε³ + B/ε + O(ε)`!
  -- Each term `(-1)^j ψ^{(2k-j)}(ε) v^{(j)}(ε)` has:
  -- `ψ^{(m)}(ε) = (-1)^m m! / (π ε^{m+1}) + sinhRem^{(m)}(ε)` where `m = 2k - j ≤ 4`,
  -- and `v^{(j)}(ε)` has parity `(-1)^j` (odd `j`: `v^{(j)}(0) = 0`; `j = 0`: `v(0) = 0` and `v'(0) = 0`),
  -- so EVERY term `ψ^{(2k-j)}(ε) v^{(j)}(ε)` is `A_j / ε³ + B_j / ε + o(1)` as `ε ↓ 0`!
  have hterm_pole : ∀ j < 2 * k + 1, ∃ Aj Bj : ℝ,
      Tendsto (fun ε : ℝ => (-1 : ℝ) ^ j * iteratedDeriv (2 * k - j) ψ ε * iteratedDeriv j v ε -
        (Aj / ε ^ 3 + Bj / ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro j hj
    set m : ℕ := 2 * k - j
    -- Expand `v^{(j)}(ε)` around `0` up to order `m + 1`:
    -- Since `v` is even, `v^{(j)}(-t) = (-1)^j v^{(j)}(t)`.
    have hrem_tend : Tendsto (fun ε : ℝ => (-1 : ℝ) ^ j * iteratedDeriv m sinhRem ε * iteratedDeriv j v ε)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      -- Product of `sinhRem^{(m)}` (parity `(-1)^{m+1}`) and `v^{(j)}` (parity `(-1)^j`) is ODD (`m + 1 + j = 2k + 1` is odd)!
      have hcd_sr : ContinuousAt (iteratedDeriv m sinhRem) 0 := by
        have h : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv m sinhRem) (Ioo (-1 / 2) (1 / 2)) := by
          induction m with
          | zero => simpa only [iteratedDeriv_zero] using sinhRem_spec.1
          | succ n ih =>
            rw [show iteratedDeriv (n + 1) sinhRem = deriv (iteratedDeriv n sinhRem) by ext x; rw [iteratedDeriv_succ]]
            exact ih.deriv_of_isOpen isOpen_Ioo (by simp)
        exact h.continuousOn.continuousAt (isOpen_Ioo.mem_nhds (by norm_num))
      have hprod0 : iteratedDeriv m sinhRem 0 * iteratedDeriv j v 0 = 0 := by
        rcases Nat.even_or_odd j with ⟨r, hr⟩ | ⟨r, hr⟩
        · -- `j = 2r` even ⇒ `m = 2(k - r)` even ⇒ `sinhRem^{(m)}` is odd ⇒ `sinhRem^{(m)}(0) = 0`!
          have hm_even : Even m := ⟨k - r, by omega⟩
          have hsr0 : iteratedDeriv m sinhRem 0 = 0 := by
            have hodd : ∀ n : ℕ, iteratedDeriv (2 * n) sinhRem 0 = 0 := fun n => by
              have hev : (fun t => sinhRem (-t)) =ᶠ[𝓝 (0 : ℝ)] fun t => -sinhRem t := by
                filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
                rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
                exact sinhRem_spec.2.1 t ht
              have h1 : iteratedDeriv (2 * n) (fun t => sinhRem (-t)) 0 = iteratedDeriv (2 * n) sinhRem 0 := by
                rw [iteratedDeriv_comp_neg, neg_zero, (even_two_mul n).neg_one_pow, one_smul]
              have h2 : iteratedDeriv (2 * n) (fun t => -sinhRem t) 0 = -iteratedDeriv (2 * n) sinhRem 0 := by
                change iteratedDeriv (2 * n) (-sinhRem) 0 = _; rw [iteratedDeriv_neg]
              have h3 := (hev.iteratedDeriv (2 * n)).eq_of_nhds
              linarith
            obtain ⟨n, hn⟩ := hm_even
            rw [show m = 2 * n by omega]; exact hodd n
          rw [hsr0, zero_mul]
        · -- `j = 2r + 1` odd ⇒ `v^{(j)}(0) = 0`!
          rw [hr, iteratedDeriv_odd_zero hv_even r, mul_zero]
      have hc : Tendsto (fun ε : ℝ => (-1 : ℝ) ^ j * iteratedDeriv m sinhRem ε * iteratedDeriv j v ε)
          (𝓝[>] (0 : ℝ)) (𝓝 ((-1 : ℝ) ^ j * iteratedDeriv m sinhRem 0 * iteratedDeriv j v 0)) :=
        (((continuousAt_const (y := (-1 : ℝ) ^ j)).mul hcd_sr).mul
          (contDiff_iteratedDeriv_infty hv j).continuous.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      simpa [mul_assoc, hprod0] using hc
    -- Now the singular part: `c_m * v^{(j)}(ε) / ε^{m+1}` where `c_m = (-1)^{j+m} m! / π`!
    -- Since `v^{(j)}` is `C^∞`, Taylor's theorem at `0` up to degree `m + 1` gives:
    -- `v^{(j)}(ε) = ∑_{l ≤ m} (v^{(j+l)}(0) / l!) ε^l + O(ε^{m+1})`!
    -- For `l` with `j + l` odd, `v^{(j+l)}(0) = 0`; and for `j = l = 0`, `v(0) = 0`!
    -- Since `j + m = 2k ≤ 4`:
    -- - `l` only contributes when `j + l` is EVEN and `j + l ≥ 2`, so `m + 1 - l = (2k + 1) - (j + l) ∈ {1, 3}` (ODD and `≤ 3`!)
    set c_m : ℝ := (-1 : ℝ) ^ j * ((-1 : ℝ) ^ m * (m.factorial : ℝ) / π)
    have hsing : ∃ Aj Bj : ℝ, Tendsto (fun ε : ℝ => c_m * iteratedDeriv j v ε / ε ^ (m + 1) - (Aj / ε ^ 3 + Bj / ε))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      -- Taylor polynomial of `v^{(j)}` of degree `m + 1` at `0`:
      let f : ℝ → ℝ := iteratedDeriv j v
      have hf_cd : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_iteratedDeriv_infty hv j
      obtain ⟨B_f, hBf⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
        (contDiff_iteratedDeriv_infty hf_cd (m + 2)).continuous.continuousOn
      have htay : ∀ ε ∈ Ioc (0 : ℝ) 1,
          |f ε - ∑ l ∈ Finset.range (m + 2), (iteratedDeriv l f 0 / (l.factorial : ℝ)) * ε ^ l| ≤
            max B_f 0 * ε ^ (m + 2) := by
        intro ε hε
        have h := taylor_mean_remainder_bound (f := f) (a := 0) (b := ε) (x := ε) (n := m + 1) (C := max B_f 0)
          (hf_cd.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)) ⟨hε.1.le, le_rfl⟩ fun x hx => by
            rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hε.1)
              (hf_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) hx]
            exact (hBf x ⟨hx.1, hx.2.trans hε.2⟩).trans (le_max_left _ _)
        have hteq : taylorWithinEval f (m + 1) (Icc 0 ε) 0 ε =
            ∑ l ∈ Finset.range (m + 2), (iteratedDeriv l f 0 / (l.factorial : ℝ)) * ε ^ l := by
          rw [taylor_within_apply]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hε.1)
            (hf_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) ⟨le_rfl, hε.1.le⟩, sub_zero, smul_eq_mul]
          ring
        rw [hteq, Real.norm_eq_abs, sub_zero] at h
        exact h.trans (div_le_self (mul_nonneg (le_max_right B_f 0) (pow_nonneg hε.1.le _))
          (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (m + 1))))
      -- Every term in `∑_{l ≤ m + 1} (f^{(l)}(0)/l!) ε^l / ε^{m+1}` vanishes unless `j + l ∈ {2, 4}`!
      -- Specifically:
      -- - `j + l = 0` ⇒ `f^{(0)}(0) = v(0) = 0`;
      -- - `j + l` odd ⇒ `f^{(l)}(0) = v^{(j+l)}(0) = 0`;
      -- - `j + l = 2k + 1` is odd, so `l = m + 1` vanishes too!
      -- - Remaining `l` have `j + l ∈ {2, 4}` and `l ≤ m`, so `m + 1 - l = 2k + 1 - (j + l) ∈ {1, 3}`!
      have hf_zero : ∀ l : ℕ, l ≤ m + 1 → (Odd (j + l) ∨ j + l = 0) → iteratedDeriv l f 0 = 0 := by
        intro l _ hl
        dsimp only [f]; rw [iteratedDeriv_iteratedDeriv_eq]
        rcases hl with ⟨r, hr⟩ | h0
        · rw [show l + j = 2 * r + 1 by omega]; exact iteratedDeriv_odd_zero hv_even r
        · have : l = 0 ∧ j = 0 := by omega
          rw [this.1, this.2, zero_add, iteratedDeriv_zero]; exact hv0
      -- Define `Aj` (coefficient of `1/ε³`, from `j + l = 2k - 2` i.e. `l = m - 2` when `2 ≤ m` and `2k - 2 ≥ 2`)
      -- and `Bj` (coefficient of `1/ε`, from `j + l = 2k` i.e. `l = m` when `2k ≥ 2`)!
      let Aj : ℝ := if 2 ≤ m then c_m * (iteratedDeriv (m - 2) f 0 / ((m - 2).factorial : ℝ)) else 0
      let Bj : ℝ := c_m * (iteratedDeriv m f 0 / (m.factorial : ℝ))
      refine ⟨Aj, Bj, ?_⟩
      have hpoly_eq : ∀ ε : ℝ, 0 < ε →
          c_m * (∑ l ∈ Finset.range (m + 2), (iteratedDeriv l f 0 / (l.factorial : ℝ)) * ε ^ l) / ε ^ (m + 1) =
            Aj / ε ^ 3 + Bj / ε := by
        intro ε hε
        rw [Finset.mul_sum, Finset.sum_div]
        -- Since `m ≤ 2k ≤ 4`, handle each `l ∈ range (m + 2)` by noticing only `l = m` and (if `m ≥ 2`) `l = m - 2` can be nonzero!
        have honly : ∀ l ∈ Finset.range (m + 2), l ≠ m → (2 ≤ m → l ≠ m - 2) →
            c_m * ((iteratedDeriv l f 0 / (l.factorial : ℝ)) * ε ^ l) / ε ^ (m + 1) = 0 := by
          intro l hl hlm hlm2
          have hlt : l < m + 2 := Finset.mem_range.mp hl
          have h0 : iteratedDeriv l f 0 = 0 := by
            refine hf_zero l (by omega) ?_
            rcases Nat.even_or_odd (j + l) with ⟨r, hr⟩ | hodd
            · right; omega
            · left; exact hodd
          rw [h0, zero_div, zero_mul, mul_zero, zero_div]
        -- Split off `l = m` and `l = m - 2` by `rcases` on `m ∈ {0,1,2,3,4}`!
        dsimp only [Aj, Bj]
        rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 by omega) with hm | hm | hm | hm | hm
        · rw [hm, Finset.sum_range_succ, Finset.sum_range_one]
          have h1 := honly 1 (by simp [hm]) (by omega) (by omega)
          rw [hm] at h1
          rw [h1, add_zero]; simp only [show ¬(2 ≤ 0) by omega, ↓reduceIte, zero_div, zero_add]; field_simp [hε.ne']
        · rw [hm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
          have h0 := honly 0 (by simp [hm]) (by omega) (by omega)
          have h2 := honly 2 (by simp [hm]) (by omega) (by omega)
          rw [hm] at h0 h2
          rw [h0, h2, zero_add, add_zero]; simp only [show ¬(2 ≤ 1) by omega, ↓reduceIte, zero_div, zero_add]; field_simp [hε.ne']
        · rw [hm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
          have h1 := honly 1 (by simp [hm]) (by omega) (by omega)
          have h3 := honly 3 (by simp [hm]) (by omega) (by omega)
          rw [hm] at h1 h3
          rw [h1, h3, add_zero, add_zero]; simp only [le_rfl, ↓reduceIte, Nat.sub_self]; field_simp [hε.ne']
        · rw [hm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
          have h0 := honly 0 (by simp [hm]) (by omega) (by omega)
          have h2 := honly 2 (by simp [hm]) (by omega) (by omega)
          have h4 := honly 4 (by simp [hm]) (by omega) (by omega)
          rw [hm] at h0 h2 h4
          rw [h0, h2, h4, zero_add, add_zero, add_zero]; simp only [show 2 ≤ 3 by omega, ↓reduceIte]; field_simp [hε.ne']
        · rw [hm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_succ, Finset.sum_range_one]
          have h0 := honly 0 (by simp [hm]) (by omega) (by omega)
          have h1 := honly 1 (by simp [hm]) (by omega) (by omega)
          have h3 := honly 3 (by simp [hm]) (by omega) (by omega)
          have h5 := honly 5 (by simp [hm]) (by omega) (by omega)
          rw [hm] at h0 h1 h3 h5
          rw [h0, h1, h3, h5, zero_add, zero_add, add_zero, add_zero]; simp only [show 2 ≤ 4 by omega, ↓reduceIte]; field_simp [hε.ne']
      have hid0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_
        (by simpa using (tendsto_const_nhds (x := |c_m| * max B_f 0)).mul hid0)
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      rw [← hpoly_eq ε hε.1, ← sub_div, ← mul_sub, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hε.1]
      calc |c_m| * |f ε - ∑ l ∈ Finset.range (m + 2), iteratedDeriv l f 0 / ↑l.factorial * ε ^ l| / ε ^ (m + 1)
          ≤ |c_m| * (max B_f 0 * ε ^ (m + 2)) / ε ^ (m + 1) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (htay ε ⟨hε.1, hε.2.le⟩) (abs_nonneg _)) (pow_nonneg hε.1.le _)
        _ = |c_m| * max B_f 0 * ε := by rw [pow_succ]; field_simp [hε.1.ne']
    obtain ⟨Aj, Bj, hAjBj⟩ := hsing
    refine ⟨Aj, Bj, ?_⟩
    have hsum := hAjBj.add hrem_tend
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    rw [iteratedDeriv_inv_sinh m hε.1 hε.2]; dsimp only [c_m]; ring
  -- Sum `hterm_pole` over `j ∈ Finset.range (2*k + 1)`!
  have hsum_pole : ∃ A B : ℝ, Tendsto (fun ε : ℝ =>
      (∑ j ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ j * iteratedDeriv (2 * k - j) ψ ε * iteratedDeriv j v ε) -
        (A / ε ^ 3 + B / ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfin : ∀ (s : Finset ℕ), (∀ j ∈ s, j < 2 * k + 1) →
        ∃ A B : ℝ, Tendsto (fun ε : ℝ =>
          (∑ j ∈ s, (-1 : ℝ) ^ j * iteratedDeriv (2 * k - j) ψ ε * iteratedDeriv j v ε) -
            (A / ε ^ 3 + B / ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      intro s; induction s using Finset.cons_induction with
      | empty => intro _; exact ⟨0, 0, by simp⟩
      | cons a s ha ih =>
        intro hs
        obtain ⟨Aa, Ba, hta⟩ := hterm_pole a (hs a (Finset.mem_cons_self a s))
        obtain ⟨As, Bs, hts⟩ := ih fun j hj => hs j (Finset.mem_cons_of_mem hj)
        refine ⟨Aa + As, Ba + Bs, ?_⟩
        have h := hta.add hts
        rw [add_zero] at h
        exact h.congr fun ε => by rw [Finset.sum_cons]; ring
    exact hfin (Finset.range (2 * k + 1)) fun j hj => Finset.mem_range.mp hj
  obtain ⟨A, B, hAB⟩ := hsum_pole
  refine ⟨A, B, ?_⟩
  have htot := hAB.add hint_tend
  rw [add_zero] at htot
  refine htot.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < R by positivity)] with ε hε
  rw [hibp_full hε.1 hε.2]; ring

/-- Finite-part bound for the linear `v` term `∫_ε^∞ α_osc |H_0(it)| v(t) / m(t)^p dt` (`p ∈ {1, 2}`):
when `v ∈ C_c^∞((-10τ₁, 10τ₁))` is even with `v(0) = 0` and `fctMoment k v = 0` for `k ≤ 2`,
the integral equals `A/ε³ + B/ε + L + o(1)` as `ε ↓ 0` with `|L| ≤ C_lin * ∫ |v|`. -/
lemma fp_linear_v_bound (kind : StripKernelChoice) :
    ∃ C_lin ≥ 0, ∀ {v : ℝ → ℝ} {τ₁ : ℝ}, 0 < τ₁ → τ₁ ≤ 1 / 80 →
      ContDiff ℝ (⊤ : ℕ∞) v → (∀ t, v (-t) = v t) → v 0 = 0 →
      Function.support v ⊆ Ioo (-(10 * τ₁)) (10 * τ₁) →
      (∀ k ≤ 2, fctMoment k v = 0) →
      ∀ p : ℕ, 1 ≤ p → p ≤ 2 →
        ∃ A B L : ℝ,
          Tendsto (fun ε : ℝ =>
            (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) -
              (A / ε ^ 3 + B / ε)) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
          |L| ≤ C_lin * ∫ t : ℝ, |v t| := by
  -- Express `W_p(t) := α_osc |H_0(it)| / m(t)^p` on `(0, 1/8]` as
  -- `c_0 (-ψ'(t)) + c_1 (-ψ'''(t)) + c_2 (-ψ^{(5)}(t)) + R_p(t)` with `|R_p(t)| ≤ C_lin`!
  let hFac : ℝ → ℝ := fun t =>
    let sQ := (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re
    match kind with
    | .ce => 1 / sQ ^ 2
    | .star => 1 / sQ ^ 2 + (π * t / 2) ^ 2 / Real.cosh (π * t / 2) ^ 2
  have hsQ_cd : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re) (Ioo (-1 / 4) (1 / 4)) :=
    (Complex.reCLM.contDiff.comp (CtOuter.differentiable_sinhQ.contDiff.restrict_scalars ℝ |>.comp
      (Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).div_const 2)))).contDiffOn
  have hsQ_ne : ∀ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4), (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re ^ 2 ≠ 0 := fun t ht => by
    have hx2 : ‖((π * t / 2 : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos, show |(2 : ℝ)| = 2 by norm_num]
      have : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      nlinarith [Real.pi_lt_four, abs_nonneg t]
    exact pow_ne_zero 2 (CtOuter.re_sinhQ_pos hx2).ne'
  have hhFac_cd : ContDiffOn ℝ (⊤ : ℕ∞) hFac (Ioo (-1 / 4) (1 / 4)) := by
    dsimp only [hFac]; cases kind
    · exact (contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne).add
        ((((contDiff_const.mul contDiff_id).div_const 2).pow 2).contDiffOn.div
          (((Real.contDiff_cosh.comp ((contDiff_const.mul contDiff_id).div_const 2)).pow 2).contDiffOn)
          fun _ _ => pow_ne_zero 2 (Real.cosh_pos _).ne')
    · exact contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne
  have hhFac_even : ∀ t : ℝ, hFac (-t) = hFac t := fun t => by
    have hq : CtOuter.sinhQ ((π * -t / 2 : ℝ) : ℂ) = CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ) := by
      rw [show (π * -t / 2 : ℝ) = -(π * t / 2) by ring, Complex.ofReal_neg]
      unfold CtOuter.sinhQ; refine tsum_congr fun n => ?_; rw [(even_two_mul n).neg_pow]
    dsimp only [hFac]; cases kind
    · rw [hq, show π * -t / 2 = -(π * t / 2) by ring, Real.cosh_neg, neg_sq]
    · rw [hq]
  have hhFac_eq : ∀ t : ℝ, 0 < t → ‖stripH0 kind ((t : ℂ) * Complex.I)‖ = hFac t / t ^ 2 := fun t ht => by
    have hx : 0 < π * t / 2 := by positivity
    have hsQ : (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re = Real.sinh (π * t / 2) / (π * t / 2) := by
      rw [CtOuter.sinhQ_ofReal hx.ne', Complex.ofReal_re]
    have hsh : Real.sinh (π * t / 2) ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
    dsimp only [hFac]; rw [hsQ]; cases kind
    · rw [norm_stripH0_star_imag ht]; field_simp [ht.ne', Real.pi_ne_zero, hsh, (Real.cosh_pos _).ne']; ring
    · rw [norm_stripH0_ce_imag ht]; field_simp [ht.ne', Real.pi_ne_zero, hsh]; ring
  -- Taylor expand `g_p(t) := α_osc * hFac(t) / mQ(t)^p` for `p = 1, 2` up to order `2*(p+1)`!
  have hg_tay : ∀ p : ℕ, ∃ (a : Fin (p + 1) → ℝ) (C_p : ℝ), 0 ≤ C_p ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 8),
        |uctAlphaOsc * hFac t / mQ t ^ p - ∑ j : Fin (p + 1), a j * t ^ (2 * j.1)| ≤ C_p * t ^ (2 * (p + 1)) := by
    intro p
    refine even_smooth_taylor_bound ?_ (fun t _ => by rw [hhFac_even, mQ_even]) (p + 1)
    exact (contDiffOn_const.mul hhFac_cd).div (contDiffOn_mQ.pow p) fun t ht =>
      pow_ne_zero p (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  choose aP CP hCP_nn hCP_bd using hg_tay
  -- Uniform bounds on `|iteratedDeriv (2*k+1) sinhRem t|` on `[0, 1/8]` for `k = 0, 1, 2`!
  have hsr_bd : ∃ B_sr ≥ 0, ∀ k ≤ 2, ∀ t ∈ Icc (0 : ℝ) (1 / 8),
      |iteratedDeriv (2 * k + 1) sinhRem t| ≤ B_sr := by
    have h1 : ∀ k : ℕ, ∃ B ≥ 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8), |iteratedDeriv (2 * k + 1) sinhRem t| ≤ B := fun k => by
      have hcd : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv (2 * k + 1) sinhRem) (Ioo (-1 / 2) (1 / 2)) := by
        have hall : ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv m sinhRem) (Ioo (-1 / 2) (1 / 2)) := fun m => by
          induction m with
          | zero => simpa only [iteratedDeriv_zero] using sinhRem_spec.1
          | succ n ih =>
            rw [show iteratedDeriv (n + 1) sinhRem = deriv (iteratedDeriv n sinhRem) by ext x; rw [iteratedDeriv_succ]]
            exact ih.deriv_of_isOpen isOpen_Ioo (by simp)
        exact hall (2 * k + 1)
      obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_bound_of_continuousOn
        (hcd.continuousOn.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      exact ⟨max B 0, le_max_right _ _, fun t ht => (by simpa [Real.norm_eq_abs] using hB t ht : |iteratedDeriv (2 * k + 1) sinhRem t| ≤ B).trans (le_max_left _ _)⟩
    obtain ⟨B0, hB0, hb0⟩ := h1 0
    obtain ⟨B1, hB1, hb1⟩ := h1 1
    obtain ⟨B2, hB2, hb2⟩ := h1 2
    refine ⟨max B0 (max B1 B2), le_trans hB0 (le_max_left _ _), fun k hk t ht => ?_⟩
    interval_cases k
    · exact (hb0 t ht).trans (le_max_left _ _)
    · exact (hb1 t ht).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hb2 t ht).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨B_sr, hBsr_nn, hBsr_bd⟩ := hsr_bd
  set C1 : ℝ := CP 1 + π * (|aP 1 0| / 6 + |aP 1 1|) * B_sr
  set C2 : ℝ := CP 2 + π * (|aP 2 0| / 120 + |aP 2 1| / 6 + |aP 2 2|) * B_sr
  refine ⟨max C1 C2, le_trans (by have := hCP_nn 1; positivity) (le_max_left _ _),
    fun {v τ₁} hτ₁ hτ₁_le hv hv_even hv0 hv_supp hmom p hp1 hp2 => ?_⟩
  let ψ : ℝ → ℝ := fun s => (Real.sinh (π * s))⁻¹
  have hv_cs := hasCompactSupport_of_support_Ioo hv_supp
  have hv_int : Integrable (fun t : ℝ => |v t|) := hv.continuous.abs.integrable_of_hasCompactSupport (hv_cs.comp_left abs_zero)
  have hhalf_int : (∫ t in Ioc (0 : ℝ) (10 * τ₁), |v t|) ≤ ∫ t : ℝ, |v t| := by
    calc (∫ t in Ioc (0 : ℝ) (10 * τ₁), |v t|)
        ≤ ∫ t in univ, |v t| := setIntegral_mono_set hv_int.integrableOn
          (Filter.Eventually.of_forall fun _ => abs_nonneg _) (Filter.Eventually.of_forall fun _ _ => mem_univ _)
      _ = ∫ t : ℝ, |v t| := setIntegral_univ
  have hv_zero_out : ∀ t : ℝ, 10 * τ₁ < t → v t = 0 := fun t ht => by
    by_contra hne; linarith [(hv_supp hne).2]
  -- Define the linear combination of `-ψ^{(2k+1)}` matching the singular part of `W_p(t)`:
  -- For `p = 1`: `c0 = π * aP 1 1`, `c1 = π * aP 1 0 / 6`, `c2 = 0`
  -- For `p = 2`: `c0 = π * aP 2 2`, `c1 = π * aP 2 1 / 6`, `c2 = π * aP 2 0 / 120`
  let c0 : ℝ := if p = 1 then π * aP 1 1 else π * aP 2 2
  let c1 : ℝ := if p = 1 then π * aP 1 0 / 6 else π * aP 2 1 / 6
  let c2 : ℝ := if p = 1 then 0 else π * aP 2 0 / 120
  let W : ℝ → ℝ := fun t => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p
  let Pψ : ℝ → ℝ := fun t =>
    c0 * (-iteratedDeriv 1 ψ t) + c1 * (-iteratedDeriv 3 ψ t) + c2 * (-iteratedDeriv 5 ψ t)
  let R : ℝ → ℝ := fun t => W t - Pψ t
  -- Bound `|R t| ≤ max C1 C2` on `Ioc 0 (10 * τ₁)` (note `10 * τ₁ ≤ 1/8`!)
  have h10_le : 10 * τ₁ ≤ 1 / 8 := by linarith
  have hR_bd : ∀ t ∈ Ioc (0 : ℝ) (10 * τ₁), |R t| ≤ max C1 C2 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht18 : t ≤ 1 / 8 := ht.2.trans h10_le
    have ht12 : t < 1 / 2 := by linarith
    have hψ1 := iteratedDeriv_inv_sinh 1 ht0 ht12
    have hψ3 := iteratedDeriv_inv_sinh 3 ht0 ht12
    have hψ5 := iteratedDeriv_inv_sinh 5 ht0 ht12
    have hsr0 := hBsr_bd 0 (by omega) t ⟨ht0.le, ht18⟩
    have hsr1 := hBsr_bd 1 (by omega) t ⟨ht0.le, ht18⟩
    have hsr2 := hBsr_bd 2 (by omega) t ⟨ht0.le, ht18⟩
    have hmQ_pos : 0 < mQ t := mQ_pos_of_mem (by rw [abs_of_pos ht0]; linarith)
    rcases (show p = 1 ∨ p = 2 by omega) with rfl | rfl
    · -- `p = 1`
      have hW_eq : W t = (uctAlphaOsc * hFac t / mQ t) / t ^ 4 := by
        dsimp only [W]; rw [hhFac_eq t ht0, uctM_eq_sq_mul_mQ ht0, pow_one]
        field_simp [ht0.ne', hmQ_pos.ne']
      have hsum : ∑ j : Fin 2, aP 1 j * t ^ (2 * j.1) = aP 1 0 + aP 1 1 * t ^ 2 := by
        rw [Fin.sum_univ_two]; simp
      have hR_eq : R t = (uctAlphaOsc * hFac t / mQ t - ∑ j : Fin 2, aP 1 j * t ^ (2 * j.1)) / t ^ 4 +
          (π * aP 1 1 * iteratedDeriv 1 sinhRem t + (π * aP 1 0 / 6) * iteratedDeriv 3 sinhRem t) := by
        dsimp only [R, Pψ, c0, c1, c2]; simp only [↓reduceIte, zero_mul, add_zero]
        rw [hW_eq, hsum, hψ1, hψ3]
        norm_num [Nat.factorial]; field_simp [ht0.ne', Real.pi_ne_zero]; ring
      rw [hR_eq]
      have h1 : |(uctAlphaOsc * hFac t / mQ t - ∑ j : Fin 2, aP 1 j * t ^ (2 * j.1)) / t ^ 4| ≤ CP 1 := by
        rw [abs_div, abs_pow, abs_of_pos ht0, div_le_iff₀ (pow_pos ht0 4)]
        simpa [pow_one] using hCP_bd 1 t ⟨ht0.le, ht18⟩
      have h2 : |π * aP 1 1 * iteratedDeriv 1 sinhRem t + (π * aP 1 0 / 6) * iteratedDeriv 3 sinhRem t| ≤
          π * (|aP 1 0| / 6 + |aP 1 1|) * B_sr := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos Real.pi_pos, show |(6 : ℝ)| = 6 by norm_num]
        have ha := mul_le_mul_of_nonneg_left hsr0 (by positivity : 0 ≤ π * |aP 1 1|)
        have hb := mul_le_mul_of_nonneg_left hsr1 (by positivity : 0 ≤ π * |aP 1 0| / 6)
        linarith
      exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans (le_max_left _ _)
    · -- `p = 2`
      have hW_eq : W t = (uctAlphaOsc * hFac t / mQ t ^ 2) / t ^ 6 := by
        dsimp only [W]; rw [hhFac_eq t ht0, uctM_eq_sq_mul_mQ ht0, mul_pow]
        field_simp [ht0.ne', hmQ_pos.ne']
      have hsum : ∑ j : Fin 3, aP 2 j * t ^ (2 * j.1) = aP 2 0 + aP 2 1 * t ^ 2 + aP 2 2 * t ^ 4 := by
        rw [Fin.sum_univ_three]; simp
      have hR_eq : R t = (uctAlphaOsc * hFac t / mQ t ^ 2 - ∑ j : Fin 3, aP 2 j * t ^ (2 * j.1)) / t ^ 6 +
          (π * aP 2 2 * iteratedDeriv 1 sinhRem t + (π * aP 2 1 / 6) * iteratedDeriv 3 sinhRem t +
            (π * aP 2 0 / 120) * iteratedDeriv 5 sinhRem t) := by
        dsimp only [R, Pψ, c0, c1, c2]; simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
        rw [hW_eq, hsum, hψ1, hψ3, hψ5]
        norm_num [Nat.factorial]; field_simp [ht0.ne', Real.pi_ne_zero]; ring
      rw [hR_eq]
      have h1 : |(uctAlphaOsc * hFac t / mQ t ^ 2 - ∑ j : Fin 3, aP 2 j * t ^ (2 * j.1)) / t ^ 6| ≤ CP 2 := by
        rw [abs_div, abs_pow, abs_of_pos ht0, div_le_iff₀ (pow_pos ht0 6)]
        exact hCP_bd 2 t ⟨ht0.le, ht18⟩
      have h2 : |π * aP 2 2 * iteratedDeriv 1 sinhRem t + (π * aP 2 1 / 6) * iteratedDeriv 3 sinhRem t +
            (π * aP 2 0 / 120) * iteratedDeriv 5 sinhRem t| ≤
          π * (|aP 2 0| / 120 + |aP 2 1| / 6 + |aP 2 2|) * B_sr := by
        refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_div, abs_mul, abs_mul, abs_div, abs_mul,
          abs_of_pos Real.pi_pos, show |(6 : ℝ)| = 6 by norm_num, show |(120 : ℝ)| = 120 by norm_num]
        have ha := mul_le_mul_of_nonneg_left hsr0 (by positivity : 0 ≤ π * |aP 2 2|)
        have hb := mul_le_mul_of_nonneg_left hsr1 (by positivity : 0 ≤ π * |aP 2 1| / 6)
        have hc := mul_le_mul_of_nonneg_left hsr2 (by positivity : 0 ≤ π * |aP 2 0| / 120)
        linarith
      exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans (le_max_right _ _)
  -- Obtain the three odd-pole cancellations from `ibp_sinh_odd_pole` for `k = 0, 1, 2`!
  obtain ⟨A0, B0, ht0⟩ := ibp_sinh_odd_pole hτ₁ (by linarith) hv hv_even hv0 hv_supp (k := 0) (by omega) (hmom 0 (by omega))
  obtain ⟨A1, B1, ht1⟩ := ibp_sinh_odd_pole hτ₁ (by linarith) hv hv_even hv0 hv_supp (k := 1) (by omega) (hmom 1 (by omega))
  obtain ⟨A2, B2, ht2⟩ := ibp_sinh_odd_pole hτ₁ (by linarith) hv hv_even hv0 hv_supp (k := 2) (by omega) (hmom 2 (by omega))
  -- `R t * v t` is integrable on `Ioi 0` (vanishes on `Ioi (10 * τ₁)` and bounded by `max C1 C2 * |v t|` on `Ioc 0 (10 * τ₁)`)!
  have hRv_int : IntegrableOn (fun t : ℝ => R t * v t) (Ioi 0) := by
    have hcont_ψ : ∀ m : ℕ, ContinuousOn (iteratedDeriv m ψ) (Ioi 0) := fun m => by
      have hψ_cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Ioi 0) :=
        (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).contDiffOn.inv
          fun s hs => (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hs)).ne'
      have hall : ∀ n : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n ψ) (Ioi 0) := fun n => by
        induction n with
        | zero => simpa only [iteratedDeriv_zero] using hψ_cd
        | succ n ih =>
          rw [show iteratedDeriv (n + 1) ψ = deriv (iteratedDeriv n ψ) by ext x; rw [iteratedDeriv_succ]]
          exact ih.deriv_of_isOpen isOpen_Ioi (by simp)
      exact (hall m).continuousOn
    have hcont_W : ContinuousOn W (Ioi 0) := by
      have hm_c : ContinuousOn uctM (Ioi 0) := fun t ht => (hasDerivAt_uctM ht).continuousAt.continuousWithinAt
      have hH_c : ContinuousOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖) (Ioi 0) := by
        cases kind
        · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_star_imag ht
          exact (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
            ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
            fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')).add
            (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_cosh.comp
              ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
              fun _ _ => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.cosh_pos _).ne'))
        · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_ce_imag ht
          exact continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
            ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
            fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')
      exact (continuousOn_const.mul hH_c).div (hm_c.pow p) fun t ht => pow_ne_zero p (uctM_pos ht).ne'
    have hcont_R : ContinuousOn R (Ioi 0) :=
      hcont_W.sub (((continuousOn_const.mul (hcont_ψ 1).neg).add (continuousOn_const.mul (hcont_ψ 3).neg)).add
        (continuousOn_const.mul (hcont_ψ 5).neg))
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 10 * τ₁ by positivity), integrableOn_union]
    refine ⟨((hv_int.integrableOn (s := Ioc 0 (10 * τ₁))).const_mul (max C1 C2)).mono'
      (((hcont_R.mul hv.continuous.continuousOn).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_right (hR_bd t ht) (abs_nonneg _)),
      (integrableOn_zero (μ := volume) (s := Ioi (10 * τ₁))).congr_fun
        (fun t ht => by rw [hv_zero_out t ht, mul_zero]) measurableSet_Ioi⟩
  refine ⟨c0 * A0 + c1 * A1 + c2 * A2, c0 * B0 + c1 * B1 + c2 * B2, ∫ t in Ioi (0 : ℝ), R t * v t, ?_, ?_⟩
  · -- Limit as `ε ↓ 0`
    have hcomb := (((ht0.const_mul c0).add (ht1.const_mul c1)).add (ht2.const_mul c2)).add
      (FctPhiKill.tendsto_setIntegral_Ioi_zero hRv_int)
    simp only [mul_zero, add_zero, zero_add] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := mem_Ioi.mp hε
    have hψ_int : ∀ m : ℕ, IntegrableOn (fun t : ℝ => (-iteratedDeriv m ψ t) * v t) (Ioi ε) := fun m => by
      have hcont : ContinuousOn (fun t => (-iteratedDeriv m ψ t) * v t) (Ioi 0) := by
        have hψ_cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Ioi 0) :=
          (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).contDiffOn.inv
            fun s hs => (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hs)).ne'
        have hall : ∀ n : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n ψ) (Ioi 0) := fun n => by
          induction n with
          | zero => simpa only [iteratedDeriv_zero] using hψ_cd
          | succ n ih =>
            rw [show iteratedDeriv (n + 1) ψ = deriv (iteratedDeriv n ψ) by ext x; rw [iteratedDeriv_succ]]
            exact ih.deriv_of_isOpen isOpen_Ioi (by simp)
        exact (hall m).continuousOn.neg.mul hv.continuous.continuousOn
      by_cases hε10 : ε < 10 * τ₁
      · rw [← Ioc_union_Ioi_eq_Ioi hε10.le, integrableOn_union]
        exact ⟨((hcont.mono fun t (ht : t ∈ Icc ε (10 * τ₁)) => lt_of_lt_of_le hε0 ht.1).integrableOn_Icc).mono_set Ioc_subset_Icc_self,
          (integrableOn_zero (μ := volume) (s := Ioi (10 * τ₁))).congr_fun
            (fun t ht => by rw [hv_zero_out t ht, mul_zero]) measurableSet_Ioi⟩
      · exact (integrableOn_zero (μ := volume) (s := Ioi ε)).congr_fun
          (fun t ht => by rw [hv_zero_out t (lt_of_le_of_lt (not_lt.mp hε10) ht), mul_zero]) measurableSet_Ioi
    have h0 := hψ_int 1
    have h1 := hψ_int 3
    have h2 := hψ_int 5
    have hRε := hRv_int.mono_set (fun t (ht : t ∈ Ioi ε) => hε0.trans ht)
    have heq : (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) =
        c0 * (∫ t in Ioi ε, (-iteratedDeriv 1 ψ t) * v t) +
        c1 * (∫ t in Ioi ε, (-iteratedDeriv 3 ψ t) * v t) +
        c2 * (∫ t in Ioi ε, (-iteratedDeriv 5 ψ t) * v t) +
        ∫ t in Ioi ε, R t * v t := by
      have h0c : IntegrableOn (fun t : ℝ => c0 * (-iteratedDeriv 1 ψ t * v t)) (Ioi ε) := h0.const_mul c0
      have h1c : IntegrableOn (fun t : ℝ => c1 * (-iteratedDeriv 3 ψ t * v t)) (Ioi ε) := h1.const_mul c1
      have h2c : IntegrableOn (fun t : ℝ => c2 * (-iteratedDeriv 5 ψ t * v t)) (Ioi ε) := h2.const_mul c2
      have h01 : IntegrableOn (fun t : ℝ => c0 * (-iteratedDeriv 1 ψ t * v t) + c1 * (-iteratedDeriv 3 ψ t * v t)) (Ioi ε) := h0c.add h1c
      have h012 : IntegrableOn (fun t : ℝ => c0 * (-iteratedDeriv 1 ψ t * v t) + c1 * (-iteratedDeriv 3 ψ t * v t) + c2 * (-iteratedDeriv 5 ψ t * v t)) (Ioi ε) := h01.add h2c
      have hcongr : (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) =
          ∫ t in Ioi ε, (c0 * (-iteratedDeriv 1 ψ t * v t) + c1 * (-iteratedDeriv 3 ψ t * v t) +
            c2 * (-iteratedDeriv 5 ψ t * v t) + R t * v t) :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ => by dsimp only [R, Pψ, W]; ring
      rw [hcongr, integral_add h012 hRε, integral_add h01 h2c, integral_add h0c h1c,
        integral_const_mul, integral_const_mul, integral_const_mul]
    rw [heq]; ring
  · -- Bound `|∫_0^∞ R t * v t dt| ≤ max C1 C2 * ∫ |v|`
    have hzero : (∫ t in Ioi (10 * τ₁), R t * v t) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => by rw [hv_zero_out t ht, mul_zero]
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 10 * τ₁ by positivity),
      setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
        measurableSet_Ioi (hRv_int.mono_set Ioc_subset_Ioi_self) (hRv_int.mono_set fun x hx => lt_trans (by positivity) hx),
      hzero, add_zero]
    calc |∫ t in Ioc 0 (10 * τ₁), R t * v t|
        ≤ ∫ t in Ioc 0 (10 * τ₁), ‖R t * v t‖ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := fun t => R t * v t)
      _ ≤ ∫ t in Ioc 0 (10 * τ₁), max C1 C2 * |v t| :=
          setIntegral_mono_on (hRv_int.mono_set Ioc_subset_Ioi_self).norm
            ((hv_int.integrableOn (s := Ioc 0 (10 * τ₁))).const_mul (max C1 C2)) measurableSet_Ioc fun t ht => by
              rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_right (hR_bd t ht) (abs_nonneg _)
      _ = max C1 C2 * ∫ t in Ioc 0 (10 * τ₁), |v t| := integral_const_mul _ _
      _ ≤ max C1 C2 * ∫ t : ℝ, |v t| :=
          mul_le_mul_of_nonneg_left hhalf_int (le_trans (by have := hCP_nn 1; positivity) (le_max_left _ _))

/-! ### Helper 5: Elementary Taylor inequalities for `exp` -/

lemma abs_exp_sub_one_sub_le {x M : ℝ} (hx : |x| ≤ M) :
    |Real.exp x - 1 - x| ≤ (Real.exp M / 2) * x ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg x).trans hx
  have hftc : Real.exp x - 1 - x = ∫ s in (0 : ℝ)..1, (1 - s) * x ^ 2 * Real.exp (s * x) := by
    let F : ℝ → ℝ := fun s => Real.exp (s * x) + (1 - s) * x * Real.exp (s * x)
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt F ((1 - s) * x ^ 2 * Real.exp (s * x)) s := fun s _ => by
      have he : HasDerivAt (fun u => Real.exp (u * x)) (Real.exp (s * x) * (1 * x)) s :=
        ((hasDerivAt_id s).mul_const x).exp
      have h1s : HasDerivAt (fun u => (1 - u) * x) (-x) s := by
        exact (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const x).congr_deriv (by ring)
      exact (he.add (h1s.mul he)).congr_deriv (by ring)
    have hcont : Continuous (fun s : ℝ => (1 - s) * x ^ 2 * Real.exp (s * x)) :=
      ((continuous_const.sub continuous_id).mul continuous_const).mul
        (Real.continuous_exp.comp (continuous_id.mul continuous_const))
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
    dsimp only [F] at h; simp only [one_mul, sub_self, zero_mul, sub_zero, add_zero, Real.exp_zero, mul_one] at h
    linarith
  rw [hftc, ← Real.norm_eq_abs]
  calc ‖∫ s in (0 : ℝ)..1, (1 - s) * x ^ 2 * Real.exp (s * x)‖
      ≤ ∫ s in (0 : ℝ)..1, ‖(1 - s) * x ^ 2 * Real.exp (s * x)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ s in (0 : ℝ)..1, (1 - s) * x ^ 2 * Real.exp M := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (((continuous_const.sub continuous_id).mul continuous_const).mul
            (Real.continuous_exp.comp (continuous_id.mul continuous_const)) |>.norm.intervalIntegrable _ _)
          (((continuous_const.sub continuous_id).mul continuous_const).mul continuous_const |>.intervalIntegrable _ _)
          fun s hs => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith [hs.2]) (sq_nonneg x)) (Real.exp_pos _).le)]
        have hsx : s * x ≤ M := by
          calc s * x ≤ |s * x| := le_abs_self _
            _ = s * |x| := by rw [abs_mul, abs_of_nonneg hs.1]
            _ ≤ 1 * M := mul_le_mul hs.2 hx (abs_nonneg _) zero_le_one
            _ = M := one_mul _
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsx) (mul_nonneg (by linarith [hs.2]) (sq_nonneg x))
    _ = (Real.exp M / 2) * x ^ 2 := by
        have hrew : (fun s : ℝ => (1 - s) * x ^ 2 * Real.exp M) = fun s => (x ^ 2 * Real.exp M) * (1 - s) := by
          ext s; ring
        have hint1 : (∫ s in (0 : ℝ)..1, (1 - s)) = 1 / 2 := by
          have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => u - u ^ 2 / 2) (1 - s) s := fun s _ => by
            exact ((hasDerivAt_id s).sub (((hasDerivAt_pow 2 s).div_const 2))).congr_deriv (by ring)
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((continuous_const.sub continuous_id).intervalIntegrable _ _)]
          norm_num
        rw [hrew, intervalIntegral.integral_const_mul, hint1]; ring

lemma abs_exp_sub_one_sub_sq_le {x M : ℝ} (hx : |x| ≤ M) :
    |Real.exp x - 1 - x - x ^ 2 / 2| ≤ (Real.exp M / 6) * |x| ^ 3 := by
  have hM : 0 ≤ M := (abs_nonneg x).trans hx
  have hftc : Real.exp x - 1 - x - x ^ 2 / 2 =
      ∫ s in (0 : ℝ)..1, ((1 - s) ^ 2 / 2) * x ^ 3 * Real.exp (s * x) := by
    let F : ℝ → ℝ := fun s => Real.exp (s * x) * (1 + (1 - s) * x + ((1 - s) ^ 2 / 2) * x ^ 2)
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt F (((1 - s) ^ 2 / 2) * x ^ 3 * Real.exp (s * x)) s := fun s _ => by
      have he : HasDerivAt (fun u => Real.exp (u * x)) (Real.exp (s * x) * (1 * x)) s :=
        ((hasDerivAt_id s).mul_const x).exp
      have h1s : HasDerivAt (fun u => 1 - u) (-1) s := by
        exact ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).congr_deriv (by ring)
      have hpoly : HasDerivAt (fun u => 1 + (1 - u) * x + ((1 - u) ^ 2 / 2) * x ^ 2)
          (-x - (1 - s) * x ^ 2) s := by
        have ha := (hasDerivAt_const s (1 : ℝ)).add (h1s.mul_const x)
        have hb := (((h1s.pow 2).div_const 2).mul_const (x ^ 2))
        exact (ha.add hb).congr_deriv (by ring)
      exact (he.mul hpoly).congr_deriv (by ring)
    have hcont : Continuous (fun s : ℝ => ((1 - s) ^ 2 / 2) * x ^ 3 * Real.exp (s * x)) :=
      ((((continuous_const.sub continuous_id).pow 2).div_const 2).mul continuous_const).mul
        (Real.continuous_exp.comp (continuous_id.mul continuous_const))
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
    dsimp only [F] at h; simp only [one_mul, sub_self, zero_mul, zero_pow (by norm_num : 2 ≠ 0), zero_div,
      sub_zero, add_zero, mul_one, Real.exp_zero, one_pow] at h
    linarith
  rw [hftc, ← Real.norm_eq_abs]
  calc ‖∫ s in (0 : ℝ)..1, ((1 - s) ^ 2 / 2) * x ^ 3 * Real.exp (s * x)‖
      ≤ ∫ s in (0 : ℝ)..1, ‖((1 - s) ^ 2 / 2) * x ^ 3 * Real.exp (s * x)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ s in (0 : ℝ)..1, ((1 - s) ^ 2 / 2) * |x| ^ 3 * Real.exp M := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (((((continuous_const.sub continuous_id).pow 2).div_const 2).mul continuous_const).mul
            (Real.continuous_exp.comp (continuous_id.mul continuous_const)) |>.norm.intervalIntegrable _ _)
          (((((continuous_const.sub continuous_id).pow 2).div_const 2).mul continuous_const).mul
            continuous_const |>.intervalIntegrable _ _) fun s hs => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (1 - s) ^ 2 / 2),
          abs_of_pos (Real.exp_pos _)]
        have hsx : s * x ≤ M := by
          calc s * x ≤ |s * x| := le_abs_self _
            _ = s * |x| := by rw [abs_mul, abs_of_nonneg hs.1]
            _ ≤ 1 * M := mul_le_mul hs.2 hx (abs_nonneg _) zero_le_one
            _ = M := one_mul _
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsx) (by positivity)
    _ = (Real.exp M / 6) * |x| ^ 3 := by
        have hrew : (fun s : ℝ => ((1 - s) ^ 2 / 2) * |x| ^ 3 * Real.exp M) =
            fun s => (|x| ^ 3 * Real.exp M / 2) * (1 - s) ^ 2 := by ext s; ring
        have hint2 : (∫ s in (0 : ℝ)..1, (1 - s) ^ 2) = 1 / 3 := by
          have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => -(1 - u) ^ 3 / 3) ((1 - s) ^ 2) s := fun s _ => by
            have h1s : HasDerivAt (fun u => 1 - u) (-1) s :=
              ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).congr_deriv (by ring)
            exact (((h1s.pow 3).neg).div_const 3).congr_deriv (by ring)
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (((continuous_const.sub continuous_id).pow 2).intervalIntegrable _ _)]
          norm_num
        rw [hrew, intervalIntegral.integral_const_mul, hint2]; ring

/-! ### Helper 6: Inner `D_*` integral and finite parts on `(0, t₃]` -/

set_option maxHeartbeats 1600000 in
/-- On `(0, t₃]` (`t₃ := tau0 (3 * uctM τ₁) ∈ (τ₁, 2τ₁)`), `(fct:Dstar-inner)` gives:
- `∫_0^{3δ_L} D_*(L) dL = O_{K₄}(τ₁³ + |α| τ₁)`;
- for `p ∈ {1, 2}`, `∫_ε^{t₃} D_*(m(t)) m'(t) / m(t)^p dt = A/ε³ + B/ε + L₃ + o(1)`
  with `|L₃| ≤ C(K₄) * (τ₁^{3-2p} + |α| τ₁^{1-2p})`. -/
lemma inner_Dstar_bounds (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 100 ∧
    ∀ K4 : ℝ, 1 ≤ K4 →
      ∃ C ≥ 0, ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
        τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
        let v := vTotal kind K4 c α τ₁
        let v0' := v0 kind K4 τ₁
        let t₃ := tau0 (3 * uctM τ₁)
        IntegrableOn (stripDstar kind c v v0') (Ioc 0 (3 * uctM τ₁)) ∧
        |∫ L in Ioc 0 (3 * uctM τ₁), stripDstar kind c v v0' L| ≤ C * (τ₁ ^ 3 + |α| * τ₁) ∧
        ∀ p : ℕ, 1 ≤ p → p ≤ 2 →
          ∃ A B L₃ : ℝ,
            Tendsto (fun ε : ℝ =>
              (∫ t in Ioc ε t₃, stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p) -
                (A / ε ^ 3 + B / ε)) (𝓝[>] (0 : ℝ)) (𝓝 L₃) ∧
            |L₃| ≤ C * (τ₁ ^ (3 - 2 * (p : ℤ)) + |α| * τ₁ ^ (1 - 2 * (p : ℤ))) := by
  obtain ⟨τ₀_p1, hτ₀_p1_pos, hτ₀_p1_20, Cv0b, Cv0m, Cva, Cv1b, Cv1m, Cth0b, Cth0m, Ctha, Cth1b, Cth1m,
    _, _, _, _, _, _, _, hCv_nn, hCth_nn, _, _, hpart1⟩ := fct_comp_D_part1 kind
  -- Smooth even expansion of `flW_p(t) := α_fl * mD(t) / mQ(t)^{3/2 + p}` on `(-1/4, 1/4)` for `p = 0, 1, 2`!
  have hflW_tay : ∀ p : ℕ, ∃ (a : Fin (p + 1) → ℝ) (Cf : ℝ), 0 ≤ Cf ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 8),
        |uctAlphaFl * mD t / mQ t ^ (3 / 2 + (p : ℝ)) - ∑ j : Fin (p + 1), a j * t ^ (2 * j.1)| ≤
          Cf * t ^ (2 * (p + 1)) := by
    intro p
    refine even_smooth_taylor_bound ?_ (fun t ht => by rw [mD_even ht, mQ_even]) (p + 1)
    exact (contDiffOn_const.mul contDiffOn_mD).div
      (contDiffOn_mQ.rpow_const_of_ne fun t ht => (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne')
      fun t ht => (Real.rpow_pos_of_pos (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)) _).ne'
  choose aF CF hCF_nn hCF_bd using hflW_tay
  -- Bound `|uctAlphaFl * mD t / mQ t ^ (3 / 2 + p)| ≤ M_fl` on `[0, 1/8]` for `p ≤ 2`
  have hflW_bd : ∃ M_fl ≥ 0, ∀ p : ℕ, p ≤ 2 → ∀ t ∈ Icc (0 : ℝ) (1 / 8),
      uctAlphaFl * mD t / mQ t ^ (3 / 2 + (p : ℝ)) ≤ M_fl := by
    have h1 : ∀ p : ℕ, ∃ M ≥ 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8),
        uctAlphaFl * mD t / mQ t ^ (3 / 2 + (p : ℝ)) ≤ M := fun p => by
      have hcd : ContinuousOn (fun t : ℝ => uctAlphaFl * mD t / mQ t ^ (3 / 2 + (p : ℝ))) (Icc 0 (1 / 8)) :=
        ((contDiffOn_const.mul contDiffOn_mD).div
          (contDiffOn_mQ.rpow_const_of_ne fun t ht => (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne')
          fun t ht => (Real.rpow_pos_of_pos (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)) _).ne').continuousOn.mono
          fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_bound_of_continuousOn hcd
      refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
      have hMt : |uctAlphaFl * mD t / mQ t ^ (3 / 2 + (p : ℝ))| ≤ M := by
        rw [← Real.norm_eq_abs]; exact hM t ht
      exact (le_abs_self _).trans (hMt.trans (le_max_left _ _))
    obtain ⟨M0, hM0, hm0⟩ := h1 0
    obtain ⟨M1, hM1, hm1⟩ := h1 1
    obtain ⟨M2, hM2, hm2⟩ := h1 2
    refine ⟨max M0 (max M1 M2), le_trans hM0 (le_max_left _ _), fun p hp t ht => ?_⟩
    interval_cases p
    · exact (hm0 t ht).trans (le_max_left _ _)
    · exact (hm1 t ht).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hm2 t ht).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨M_fl, hMfl_nn, hMfl_bd⟩ := hflW_bd
  obtain ⟨mQ_min, hmQ_min_pos, hmQ_min_bd⟩ : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8), c ≤ mQ t := by
    have hcont := contDiffOn_mQ.continuousOn.mono (show Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4) (1 / 4) from
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn ⟨0, le_rfl, by norm_num⟩ hcont
    exact ⟨mQ t₀, mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩), fun t ht => hmin ht⟩
  obtain ⟨mD_min, hmD_min_pos, hmD_min_bd⟩ : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8), c ≤ mD t := by
    have hcont := contDiffOn_mD.continuousOn.mono (show Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4) (1 / 4) from
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn ⟨0, le_rfl, by norm_num⟩ hcont
    exact ⟨mD t₀, mD_pos_of_mem (abs_lt.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩), fun t ht => hmin ht⟩
  refine ⟨min τ₀_p1 (1 / 100), lt_min hτ₀_p1_pos (by norm_num), min_le_right _ _, fun K4 hK4 => ?_⟩
  have hK4_nn : 0 ≤ K4 := by linarith
  set M_th0_1 : ℝ := Cth0b 1 + K4 * Cth0m 1
  set M_th0_2 : ℝ := Cth0b 2 + K4 * Cth0m 2
  set M_Δ : ℝ := (1 / 2) * (M_th0_2 / mD_min + M_th0_1 / mQ_min)
  set M_e1 : ℝ := Real.exp M_Δ / 2 * M_Δ ^ 2 + M_Δ ^ 2
  set M_e0 : ℝ := Real.exp (K4 + 1)
  have hM_th1_nn : 0 ≤ M_th0_1 := by obtain ⟨h1, h2, _, _, _⟩ := hCth_nn 1; positivity
  have hM_th2_nn : 0 ≤ M_th0_2 := by obtain ⟨h1, h2, _, _, _⟩ := hCth_nn 2; positivity
  have hMΔ_nn : 0 ≤ M_Δ := by positivity
  have hMe1_nn : 0 ≤ M_e1 := by positivity
  set M_e2 : ℝ := Real.exp 1 * (K4 + 1) ^ 2 + Real.exp 1 * M_e0 * K4 ^ 2 / 2 + Real.exp 1 * K4 + 1
  set C_p0 : ℝ := M_fl * (2 + 16 * (K4 + 1) * M_e0 + 2 ^ 15 * M_e1 * M_e0)
  set C_p12 : ℝ := (|aF 1 0| + |aF 1 1| + |aF 2 0| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (16 * (K4 + 1) + 8) +
    M_fl * (16 * M_e2 + 2 ^ 16 * M_e1 * M_e0) + 1
  set C_all : ℝ := max C_p0 C_p12
  refine ⟨C_all, by have := hCF_nn 1; have := hCF_nn 2; positivity, fun {c α τ₁} hc hτ₁ hτ₁_le hc_eq hα_le => ?_⟩
  have hτ₁_p1 : τ₁ ≤ τ₀_p1 := hτ₁_le.trans (min_le_left _ _)
  have hτ₁_100 : τ₁ ≤ 1 / 100 := hτ₁_le.trans (min_le_right _ _)
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have hc_inv : c⁻¹ = τ₁ ^ 4 := by
    rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
  have hα1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
  obtain ⟨⟨hb0_cd, hm0_cd, _, _, _, hv_cd⟩, ⟨hb0_ev, hm0_ev, _, _, _, _⟩, _, ⟨hb0_s, hm0_s, _, _, _, _⟩,
    hmom, hinner, _, _, hth_in, _, _, _, _⟩ := hpart1 hK4 hc hτ₁ hτ₁_p1 hc_eq hα_le
  let v := vTotal kind K4 c α τ₁
  let v0' := v0 kind K4 τ₁
  let t₃ := FormalResearch.CohnElkies.tau0 (3 * uctM τ₁)
  have ht3_bd := saddleTau0_three_uctM_bounds hτ₁ (by linarith)
  have ht3_gt : τ₁ < t₃ := ht3_bd.1
  have ht3_lt : t₃ < 2 * τ₁ := ht3_bd.2
  have ht3_pos : 0 < t₃ := hτ₁.trans ht3_gt
  have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) v0' := hb0_cd.add (contDiff_const.mul hm0_cd)
  have hv0_cs : HasCompactSupport v0' :=
    (hasCompactSupport_of_support_Ioo hb0_s).add (hasCompactSupport_of_support_Ioo hm0_s).mul_left
  have hv0_ev : ∀ t, v0' (-t) = v0' t := fun t => by dsimp only [v0']; unfold v0; rw [hb0_ev, hm0_ev]
  have hθ0_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD v0') := contDiff_fctThetaD hv0_cd hv0_cs
  have hθ0_odd : ∀ t, fctThetaD v0' (-t) = -fctThetaD v0' t := fctThetaD_odd hv0_ev
  have hθ0_10 : deriv (fctThetaD v0') 0 = 0 := by
    rw [← iteratedDeriv_one]; exact (hmom 0 (by omega)).2.2.2.2.1
  have hθ0_20 : iteratedDeriv 2 (fctThetaD v0') 0 = 0 := by
    have h1 : iteratedDeriv 2 (fun t => fctThetaD v0' (-t)) 0 = iteratedDeriv 2 (fctThetaD v0') 0 := by
      rw [iteratedDeriv_comp_neg, neg_zero]; norm_num
    have h2 : iteratedDeriv 2 (fun t => fctThetaD v0' (-t)) 0 = -iteratedDeriv 2 (fctThetaD v0') 0 := by
      rw [show (fun t => fctThetaD v0' (-t)) = -fctThetaD v0' by ext t; exact hθ0_odd t, iteratedDeriv_neg]
    linarith
  -- Pointwise identity `(fct:Dstar-inner)` on `(0, 2τ₁]`:
  have hD_inner_eq : ∀ t ∈ Ioc (0 : ℝ) (2 * τ₁),
      stripDstar kind c v v0' (uctM t) * uctMderiv t =
        uctAlphaFl * (uctMderiv t / uctM t ^ (3 / 2 : ℝ)) *
          (Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
            (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht14 : |t| < 1 / 4 := by rw [abs_of_pos ht0]; linarith [ht.2, hτ₁_100]
    have hin := hinner t (by rw [abs_of_pos ht0]; exact ht.2)
    have hv_eq : v t = f0Base kind t - K4 * t ^ 4 - stripDeltaCurv c (fctThetaD v0') t + α * t ^ 2 := by
      dsimp only [v]; unfold vTotal v0
      have h1 : v1 kind K4 c τ₁ t = -stripDeltaCurv c (fctThetaD v0') t := by
        rw [hin.2.2.2.1, deltaCurvSmooth_eq hθ0_cd hθ0_10 hθ0_20 ht0 (by linarith [ht.2, hτ₁_100])]
        rfl
      rw [hin.1, hin.2.1, hin.2.2.1, h1]; ring
    have hr0_pos : 0 < r0Smooth kind t := r0Smooth_pos ht14
    have hexp_f0 : Real.exp (f0Base kind t) = (stripR0 kind t)⁻¹ := by
      unfold f0Base; rw [Real.exp_neg, Real.exp_log hr0_pos, r0Smooth_eq_stripR0 ht14]
    have hα_fl_pos : 0 < uctAlphaFl := by
      unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
    have hosc_eq : uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * Real.exp (f0Base kind t) =
        uctAlphaFl * (uctMderiv t / uctM t ^ (3 / 2 : ℝ)) := by
      rw [hexp_f0]; unfold stripR0
      rw [ite_eq_right_iff.mpr fun h => absurd h ht0.ne', abs_of_pos ht0]
      have hmt := uctM_pos ht0
      have hmd := uctMderiv_pos ht0
      have hH_ne : ‖stripH0 kind ((t : ℂ) * Complex.I)‖ ≠ 0 := by
        cases kind
        · rw [norm_stripH0_star_imag ht0]; positivity
        · rw [norm_stripH0_ce_imag ht0]; positivity
      have hαo_ne : uctAlphaOsc ≠ 0 := by
        rw [uctAlphaOsc_eq]; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
      field_simp [hα_fl_pos.ne', hmd.ne', (Real.rpow_pos_of_pos hmt (3 / 2 : ℝ)).ne', hH_ne, hαo_ne]
    unfold stripDstar uctIfl
    rw [show uctM t = ceEll (π * t / 2) from rfl, tau0_ceEll ht0, show ceEll (π * t / 2) = uctM t from rfl,
      sub_mul, mul_comm (stripIoscD kind v (uctM t) * _), ← mul_assoc, uctMderiv_mul_stripIoscD kind v ht0]
    rw [hv_eq, show f0Base kind t - K4 * t ^ 4 - stripDeltaCurv c (fctThetaD v0') t + α * t ^ 2 =
      f0Base kind t + (-(K4 * t ^ 4) + α * t ^ 2) + (-stripDeltaCurv c (fctThetaD v0') t) by ring,
      Real.exp_add, Real.exp_add]
    calc uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
            (Real.exp (f0Base kind t) * Real.exp (-(K4 * t ^ 4) + α * t ^ 2) *
              Real.exp (-stripDeltaCurv c (fctThetaD v0') t)) *
            (1 + stripDeltaCurv c (fctThetaD v0') t) -
          uctAlphaFl * (uctM t) ^ (-(3 / 2 : ℝ)) * uctMderiv t
        = (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * Real.exp (f0Base kind t)) *
            (Real.exp (-(K4 * t ^ 4) + α * t ^ 2) *
              (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) * (1 + stripDeltaCurv c (fctThetaD v0') t))) -
          uctAlphaFl * (uctMderiv t / uctM t ^ (3 / 2 : ℝ)) := by
            rw [Real.rpow_neg (uctM_pos ht0).le]; ring
      _ = _ := by rw [hosc_eq]; ring
  -- Bound `|Δ_curv(t)| ≤ M_Δ * c⁻¹ * τ₁⁻⁹ * t^8` and `≤ M_Δ` on `(0, 2τ₁]`!
  have hΔ_inner_bd : ∀ t ∈ Ioc (0 : ℝ) (2 * τ₁),
      |stripDeltaCurv c (fctThetaD v0') t| ≤ M_Δ * c⁻¹ * τ₁ ^ (-9 : ℤ) * t ^ 8 ∧
      |stripDeltaCurv c (fctThetaD v0') t| ≤ M_Δ := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht18 : t ≤ 1 / 8 := by linarith [ht.2, hτ₁_100]
    have ht14 : t < 1 / 4 := by linarith
    have ht12 : |t| ≤ 12 * τ₁ := by rw [abs_of_pos ht0]; linarith [ht.2]
    have hb0_cs := hasCompactSupport_of_support_Ioo hb0_s
    have hm0_cs := hasCompactSupport_of_support_Ioo hm0_s
    have hθ0b_cd := contDiff_fctThetaD hb0_cd hb0_cs
    have hθ0m_cd := contDiff_fctThetaD hm0_cd hm0_cs
    have hlin : fctThetaD v0' = fun s => fctThetaD (v0Base kind τ₁) s + K4 * fctThetaD (v0Marg τ₁) s := by
      ext s; dsimp only [v0']; unfold v0
      simpa only [one_mul] using fctThetaD_linear hb0_cd hb0_cs hm0_cd hm0_cs 1 K4 s
    have h1 := hth_in 1 t ht12
    have h2 := hth_in 2 t ht12
    have hτ3 : τ₁ ^ ((4 : ℤ) - (1 : ℕ)) ≤ τ₁ := by
      rw [show (4 : ℤ) - (1 : ℕ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      simpa using pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num : 1 ≤ 3)
    have hτ2 : τ₁ ^ ((4 : ℤ) - (2 : ℕ)) ≤ 1 := by
      rw [show (4 : ℤ) - (2 : ℕ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact pow_le_one₀ hτ₁.le hτ₁_1
    have hd1_le : |deriv (fctThetaD v0') t| ≤ M_th0_1 * τ₁ * (t / τ₁) ^ 10 := by
      rw [← iteratedDeriv_one, hlin]
      change |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) t| ≤ _
      rw [iteratedDeriv_add (hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
        ((contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
        iteratedDeriv_const_mul_field]
      have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 10) ≤ (t / τ₁) ^ 10 := by rw [abs_of_pos ht0]; exact min_le_right _ _
      have d1 : |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 1 * τ₁ * (t / τ₁) ^ 10 := by
        have h1' : |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 1 * τ₁ * min 1 ((|t| / τ₁) ^ 10) := by
          simpa [show (2 : ℤ) - (1 : ℕ) = 1 by norm_num] using h1.1
        exact h1'.trans (mul_le_mul_of_nonneg_left hmin (mul_nonneg (hCth_nn 1).1 hτ₁.le))
      have d2 : |iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m 1 * τ₁ * (t / τ₁) ^ 10 :=
        h1.2.1.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ3 (hCth_nn 1).2.1)
          (le_min zero_le_one (by positivity))).trans (mul_le_mul_of_nonneg_left hmin (mul_nonneg (hCth_nn 1).2.1 hτ₁.le)))
      calc |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t|
          ≤ |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| :=
            (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK4_nn])
        _ ≤ Cth0b 1 * τ₁ * (t / τ₁) ^ 10 + K4 * (Cth0m 1 * τ₁ * (t / τ₁) ^ 10) :=
            add_le_add d1 (mul_le_mul_of_nonneg_left d2 hK4_nn)
        _ = M_th0_1 * τ₁ * (t / τ₁) ^ 10 := by dsimp only [M_th0_1]; ring
    have hd2_le : |iteratedDeriv 2 (fctThetaD v0') t| ≤ M_th0_2 * (t / τ₁) ^ 9 := by
      rw [hlin]
      change |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) t| ≤ _
      rw [iteratedDeriv_add (hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
        ((contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
        iteratedDeriv_const_mul_field]
      have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 9) ≤ (t / τ₁) ^ 9 := by rw [abs_of_pos ht0]; exact min_le_right _ _
      have d1 : |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 2 * (t / τ₁) ^ 9 := by
        have h2' : |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 2 * min 1 ((|t| / τ₁) ^ 9) := by
          simpa [show (2 : ℤ) - (2 : ℕ) = 0 by norm_num] using h2.1
        exact h2'.trans (mul_le_mul_of_nonneg_left hmin (hCth_nn 2).1)
      have d2 : |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m 2 * (t / τ₁) ^ 9 := by
        refine h2.2.1.trans ?_
        have := mul_le_mul_of_nonneg_left hτ2 (hCth_nn 2).2.1; rw [mul_one] at this
        exact (mul_le_mul_of_nonneg_right this (le_min zero_le_one (by positivity))).trans
          (mul_le_mul_of_nonneg_left hmin (hCth_nn 2).2.1)
      calc |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t|
          ≤ |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| :=
            (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK4_nn])
        _ ≤ Cth0b 2 * (t / τ₁) ^ 9 + K4 * (Cth0m 2 * (t / τ₁) ^ 9) :=
            add_le_add d1 (mul_le_mul_of_nonneg_left d2 hK4_nn)
        _ = M_th0_2 * (t / τ₁) ^ 9 := by dsimp only [M_th0_2]; ring
    have hmain : |stripDeltaCurv c (fctThetaD v0') t| ≤ M_Δ * c⁻¹ * τ₁ ^ (-9 : ℤ) * t ^ 8 := by
      unfold stripDeltaCurv
      rw [uctMderiv_eq_mul_mD ht0 ht14, uctM_eq_sq_mul_mQ ht0, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * c))]
      have hmD_ge := hmD_min_bd t ⟨ht0.le, ht18⟩
      have hmQ_ge := hmQ_min_bd t ⟨ht0.le, ht18⟩
      have hA : |iteratedDeriv 2 (fctThetaD v0') t / (t * mD t)| ≤ (M_th0_2 / mD_min) * τ₁ ^ (-9 : ℤ) * t ^ 8 := by
        rw [abs_div, abs_of_pos (mul_pos ht0 (mD_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)))]
        calc |iteratedDeriv 2 (fctThetaD v0') t| / (t * mD t)
            ≤ (M_th0_2 * (t / τ₁) ^ 9) / (t * mD_min) :=
              div_le_div₀ (by positivity) hd2_le (by positivity) (mul_le_mul_of_nonneg_left hmD_ge ht0.le)
          _ = (M_th0_2 / mD_min) * τ₁ ^ (-9 : ℤ) * t ^ 8 := by
              rw [show (-9 : ℤ) = -((9 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
              field_simp [ht0.ne', hτ₁.ne', hmD_min_pos.ne']
      have hB : |deriv (fctThetaD v0') t / (t ^ 2 * mQ t)| ≤ (M_th0_1 / mQ_min) * τ₁ ^ (-9 : ℤ) * t ^ 8 := by
        rw [abs_div, abs_of_pos (mul_pos (sq_pos_of_pos ht0) (mQ_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)))]
        calc |deriv (fctThetaD v0') t| / (t ^ 2 * mQ t)
            ≤ (M_th0_1 * τ₁ * (t / τ₁) ^ 10) / (t ^ 2 * mQ_min) :=
              div_le_div₀ (by positivity) hd1_le (by positivity) (mul_le_mul_of_nonneg_left hmQ_ge (sq_nonneg t))
          _ = (M_th0_1 / mQ_min) * τ₁ ^ (-9 : ℤ) * t ^ 8 := by
              rw [show (-9 : ℤ) = -((9 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
              field_simp [ht0.ne', hτ₁.ne', hmQ_min_pos.ne']
      have htri := (abs_sub _ _).trans (add_le_add hA hB)
      calc (1 / (2 * c)) * |iteratedDeriv 2 (fctThetaD v0') t / (t * mD t) - deriv (fctThetaD v0') t / (t ^ 2 * mQ t)|
          ≤ (1 / (2 * c)) * ((M_th0_2 / mD_min) * τ₁ ^ (-9 : ℤ) * t ^ 8 + (M_th0_1 / mQ_min) * τ₁ ^ (-9 : ℤ) * t ^ 8) :=
            mul_le_mul_of_nonneg_left htri (by positivity)
        _ = M_Δ * c⁻¹ * τ₁ ^ (-9 : ℤ) * t ^ 8 := by dsimp only [M_Δ]; field_simp [hc.ne']
    refine ⟨hmain, hmain.trans ?_⟩
    have hfac : c⁻¹ * τ₁ ^ (-9 : ℤ) * t ^ 8 ≤ 1 := by
      rw [hc_inv, show (-9 : ℤ) = -((9 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
      have ht8 : t ^ 8 ≤ (2 * τ₁) ^ 8 := pow_le_pow_left₀ ht0.le ht.2 8
      calc τ₁ ^ 4 * (τ₁ ^ 9)⁻¹ * t ^ 8 ≤ τ₁ ^ 4 * (τ₁ ^ 9)⁻¹ * (2 * τ₁) ^ 8 :=
            mul_le_mul_of_nonneg_left ht8 (by positivity)
        _ = 256 * τ₁ ^ 3 := by field_simp [hτ₁.ne']; ring
        _ ≤ 256 * (1 / 100) ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ₁.le hτ₁_100 3) (by norm_num)
        _ ≤ 1 := by norm_num
    rw [mul_assoc M_Δ, mul_assoc M_Δ]
    exact mul_le_of_le_one_right hMΔ_nn (by simpa [mul_assoc] using hfac)
  -- Helper: `|e^{-Δ}(1 + Δ) - 1| ≤ M_e1 * c⁻² * τ₁⁻¹⁸ * t¹⁶` on `(0, 2τ₁]`
  have hΔ_exp_bd : ∀ t ∈ Ioc (0 : ℝ) (2 * τ₁),
      |Real.exp (-stripDeltaCurv c (fctThetaD v0') t) * (1 + stripDeltaCurv c (fctThetaD v0') t) - 1| ≤
        M_e1 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    set Δ := stripDeltaCurv c (fctThetaD v0') t
    have hΔ := hΔ_inner_bd t ht
    have hftc : Real.exp (-Δ) * (1 + Δ) - 1 = ∫ s in (0 : ℝ)..1, -(s * Δ ^ 2 * Real.exp (-(s * Δ))) := by
      have hd : ∀ s ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun u => Real.exp (-(u * Δ)) * (1 + u * Δ)) (-(s * Δ ^ 2 * Real.exp (-(s * Δ)))) s := fun s _ => by
        have he : HasDerivAt (fun u => Real.exp (-(u * Δ))) (-Δ * Real.exp (-(s * Δ))) s := by
          have := (Real.hasDerivAt_exp (-(s * Δ))).comp s (((hasDerivAt_id s).mul_const Δ).neg)
          refine this.congr_deriv ?_; ring
        have hl : HasDerivAt (fun u => 1 + u * Δ) Δ s :=
          ((hasDerivAt_const s (1 : ℝ)).add ((hasDerivAt_id s).mul_const Δ)).congr_deriv (by ring)
        exact (he.mul hl).congr_deriv (by ring)
      have hcont : Continuous (fun s : ℝ => -(s * Δ ^ 2 * Real.exp (-(s * Δ)))) :=
        ((continuous_id.mul continuous_const).mul (Real.continuous_exp.comp (continuous_id.mul continuous_const).neg)).neg
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
      simpa using h.symm
    rw [hftc]
    have hbd1 : |∫ s in (0 : ℝ)..1, -(s * Δ ^ 2 * Real.exp (-(s * Δ)))| ≤ (Real.exp M_Δ / 2) * Δ ^ 2 := by
      rw [← Real.norm_eq_abs]
      calc ‖∫ s in (0 : ℝ)..1, -(s * Δ ^ 2 * Real.exp (-(s * Δ)))‖
          ≤ ∫ s in (0 : ℝ)..1, ‖-(s * Δ ^ 2 * Real.exp (-(s * Δ)))‖ :=
            intervalIntegral.norm_integral_le_integral_norm zero_le_one
        _ ≤ ∫ s in (0 : ℝ)..1, s * Δ ^ 2 * Real.exp M_Δ := by
            refine intervalIntegral.integral_mono_on zero_le_one
              (((continuous_id.mul continuous_const).mul (Real.continuous_exp.comp (continuous_id.mul continuous_const).neg)).neg.norm.intervalIntegrable _ _)
              (((continuous_id.mul continuous_const).mul continuous_const).intervalIntegrable _ _) fun s hs => ?_
            rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg hs.1 (sq_nonneg Δ)) (Real.exp_pos _).le)]
            have hsΔ : -(s * Δ) ≤ M_Δ := by
              calc -(s * Δ) ≤ |-(s * Δ)| := le_abs_self _
                _ = s * |Δ| := by rw [abs_neg, abs_mul, abs_of_nonneg hs.1]
                _ ≤ 1 * M_Δ := mul_le_mul hs.2 hΔ.2 (abs_nonneg _) zero_le_one
                _ = M_Δ := one_mul _
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsΔ) (mul_nonneg hs.1 (sq_nonneg Δ))
        _ = (Real.exp M_Δ / 2) * Δ ^ 2 := by
            have hrew : (fun s : ℝ => s * Δ ^ 2 * Real.exp M_Δ) = fun s => (Δ ^ 2 * Real.exp M_Δ) * s := by ext s; ring
            rw [hrew, intervalIntegral.integral_const_mul, integral_id]; norm_num; ring
    have hsq : Δ ^ 2 ≤ M_Δ ^ 2 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 := by
      rw [← sq_abs]
      calc |Δ| ^ 2 ≤ (M_Δ * c⁻¹ * τ₁ ^ (-9 : ℤ) * t ^ 8) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hΔ.1 2
        _ = M_Δ ^ 2 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 := by
            rw [show (-18 : ℤ) = (-9 : ℤ) + (-9 : ℤ) by norm_num, zpow_add₀ hτ₁.ne']; ring
    calc _ ≤ (Real.exp M_Δ / 2 * M_Δ ^ 2) * (c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16) := by
          have := hbd1.trans (mul_le_mul_of_nonneg_left hsq (by positivity)); linarith
      _ ≤ M_e1 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 := by
          have : Real.exp M_Δ / 2 * M_Δ ^ 2 ≤ M_e1 := by dsimp only [M_e1]; linarith [sq_nonneg M_Δ]
          rw [show M_e1 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 = M_e1 * (c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16) by ring]
          exact mul_le_mul_of_nonneg_right this (mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg hτ₁.le _)) (pow_nonneg ht0.le _))
  -- Quartic remainder (for `p = 0`) and sextic remainder (for `p = 1, 2`):
  have hfac_bd1 : ∀ t ∈ Ioc (0 : ℝ) (2 * τ₁),
      |Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
        (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1 - α * t ^ 2| ≤
      2 * (K4 + 1) * M_e0 * t ^ 4 + M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := by linarith [ht.2, hτ₁_100]
    set u := -(K4 * t ^ 4) + α * t ^ 2
    have hαt2 : |α * t ^ 2| ≤ 1 := by
      rw [abs_mul, abs_pow, abs_of_pos ht0]
      exact (mul_le_mul hα1 (pow_le_one₀ ht0.le ht1) (sq_nonneg t) zero_le_one).trans (by norm_num)
    have hK4t4 : |-(K4 * t ^ 4)| ≤ K4 := by
      rw [abs_neg, abs_mul, abs_of_nonneg hK4_nn, abs_pow, abs_of_pos ht0]
      exact mul_le_of_le_one_right hK4_nn (pow_le_one₀ ht0.le ht1)
    have hexp_u_bd : Real.exp u ≤ M_e0 := Real.exp_le_exp.mpr ((le_abs_self u).trans ((abs_add_le _ _).trans (add_le_add hK4t4 hαt2)))
    have hexp_u_sub : |Real.exp u - 1 - α * t ^ 2| ≤ 2 * (K4 + 1) * M_e0 * t ^ 4 := by
      have hrew2 : Real.exp u - 1 - α * t ^ 2 =
          (Real.exp (α * t ^ 2) - 1 - α * t ^ 2) + Real.exp (α * t ^ 2) * (Real.exp (-(K4 * t ^ 4)) - 1) := by
        dsimp only [u]; rw [Real.exp_add]; ring
      rw [hrew2]
      have ha : |Real.exp (α * t ^ 2) - 1 - α * t ^ 2| ≤ (Real.exp 1 / 2) * t ^ 4 := by
        have h := abs_exp_sub_one_sub_le hαt2
        have hsq : (α * t ^ 2) ^ 2 ≤ t ^ 4 := by
          rw [mul_pow, show (t ^ 2) ^ 2 = t ^ 4 by ring]
          exact mul_le_of_le_one_left (pow_nonneg ht0.le 4) (by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hα1)
        exact h.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
      have hb : |Real.exp (α * t ^ 2) * (Real.exp (-(K4 * t ^ 4)) - 1)| ≤ Real.exp 1 * K4 * t ^ 4 := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have he1 : Real.exp (α * t ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr ((le_abs_self _).trans hαt2)
        have he2 : |Real.exp (-(K4 * t ^ 4)) - 1| ≤ K4 * t ^ 4 := by
          rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))), neg_sub]
          linarith [Real.add_one_le_exp (-(K4 * t ^ 4))]
        calc Real.exp (α * t ^ 2) * |Real.exp (-(K4 * t ^ 4)) - 1|
            ≤ Real.exp 1 * (K4 * t ^ 4) := mul_le_mul he1 he2 (abs_nonneg _) (Real.exp_pos _).le
          _ = Real.exp 1 * K4 * t ^ 4 := by ring
      have he1_le : Real.exp 1 ≤ M_e0 := Real.exp_le_exp.mpr (by linarith)
      refine (abs_add_le _ _).trans ?_
      have ha' : (Real.exp 1 / 2) * t ^ 4 ≤ M_e0 * t ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos 1]) (pow_nonneg ht0.le 4)
      have hb' : Real.exp 1 * K4 * t ^ 4 ≤ M_e0 * K4 * t ^ 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he1_le hK4_nn) (pow_nonneg ht0.le 4)
      have hnn : 0 ≤ (K4 + 1) * M_e0 * t ^ 4 := by positivity
      linarith
    have hsplit : Real.exp u * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
        (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1 - α * t ^ 2 =
        (Real.exp u - 1 - α * t ^ 2) + Real.exp u * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
          (1 + stripDeltaCurv c (fctThetaD v0') t) - 1) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add hexp_u_sub ?_)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp u * |Real.exp (-stripDeltaCurv c (fctThetaD v0') t) * (1 + stripDeltaCurv c (fctThetaD v0') t) - 1|
        ≤ M_e0 * (M_e1 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16) :=
          mul_le_mul hexp_u_bd (hΔ_exp_bd t ht) (abs_nonneg _) (Real.exp_pos _).le
      _ = M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 := by ring
  have hfac_bd2 : ∀ t ∈ Ioc (0 : ℝ) (2 * τ₁),
      |Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
        (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1 - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4| ≤
      M_e2 * t ^ 6 + M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := by linarith [ht.2, hτ₁_100]
    set u := -(K4 * t ^ 4) + α * t ^ 2
    have hαt2 : |α * t ^ 2| ≤ 1 := by
      rw [abs_mul, abs_pow, abs_of_pos ht0]
      exact (mul_le_mul hα1 (pow_le_one₀ ht0.le ht1) (sq_nonneg t) zero_le_one).trans (by norm_num)
    have hK4t4 : |-(K4 * t ^ 4)| ≤ K4 := by
      rw [abs_neg, abs_mul, abs_of_nonneg hK4_nn, abs_pow, abs_of_pos ht0]
      exact mul_le_of_le_one_right hK4_nn (pow_le_one₀ ht0.le ht1)
    have hexp_u_bd : Real.exp u ≤ M_e0 := Real.exp_le_exp.mpr ((le_abs_self u).trans ((abs_add_le _ _).trans (add_le_add hK4t4 hαt2)))
    have hexp_u_sub : |Real.exp u - 1 - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4| ≤ M_e2 * t ^ 6 := by
      have hrew : Real.exp u - 1 - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4 =
          (Real.exp (α * t ^ 2) - 1 - α * t ^ 2 - (α * t ^ 2) ^ 2 / 2) +
          Real.exp (α * t ^ 2) * (Real.exp (-(K4 * t ^ 4)) - 1 - (-(K4 * t ^ 4))) -
          K4 * t ^ 4 * (Real.exp (α * t ^ 2) - 1) := by
        dsimp only [u]; rw [Real.exp_add]; ring
      rw [hrew]
      have h1 : |Real.exp (α * t ^ 2) - 1 - α * t ^ 2 - (α * t ^ 2) ^ 2 / 2| ≤ (Real.exp 1 / 6) * t ^ 6 := by
        have h := abs_exp_sub_one_sub_sq_le hαt2
        have h3 : |α * t ^ 2| ^ 3 ≤ t ^ 6 := by
          rw [abs_mul, abs_pow, abs_of_pos ht0, mul_pow, show (t ^ 2) ^ 3 = t ^ 6 by ring]
          exact mul_le_of_le_one_left (pow_nonneg ht0.le 6) (pow_le_one₀ (abs_nonneg _) hα1)
        exact h.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
      have h2 : |Real.exp (α * t ^ 2) * (Real.exp (-(K4 * t ^ 4)) - 1 - (-(K4 * t ^ 4)))| ≤
          (Real.exp 1 * M_e0 * K4 ^ 2 / 2) * t ^ 6 := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have he1 : Real.exp (α * t ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr ((le_abs_self _).trans hαt2)
        have hq := abs_exp_sub_one_sub_le (x := -(K4 * t ^ 4)) (M := K4) hK4t4
        have ht8 : t ^ 8 ≤ t ^ 6 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
        have heK : Real.exp K4 ≤ M_e0 := Real.exp_le_exp.mpr (by linarith)
        have hsq : (-(K4 * t ^ 4)) ^ 2 ≤ K4 ^ 2 * t ^ 6 := by
          rw [neg_sq, mul_pow, show (t ^ 4) ^ 2 = t ^ 8 by ring]
          exact mul_le_mul_of_nonneg_left ht8 (sq_nonneg K4)
        calc Real.exp (α * t ^ 2) * |Real.exp (-(K4 * t ^ 4)) - 1 - -(K4 * t ^ 4)|
            ≤ Real.exp 1 * ((Real.exp K4 / 2) * (-(K4 * t ^ 4)) ^ 2) := mul_le_mul he1 hq (abs_nonneg _) (Real.exp_pos _).le
          _ ≤ Real.exp 1 * ((M_e0 / 2) * (K4 ^ 2 * t ^ 6)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (div_le_div_of_nonneg_right heK (by norm_num)) hsq (sq_nonneg _) (by positivity)) (Real.exp_pos _).le
          _ = (Real.exp 1 * M_e0 * K4 ^ 2 / 2) * t ^ 6 := by ring
      have h3 : |K4 * t ^ 4 * (Real.exp (α * t ^ 2) - 1)| ≤ Real.exp 1 * K4 * t ^ 6 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hK4_nn, abs_pow, abs_of_pos ht0]
        have he : |Real.exp (α * t ^ 2) - 1| ≤ Real.exp 1 * t ^ 2 := by
          have h := norm_cexp_sub_one_le (w := ((α * t ^ 2 : ℝ) : ℂ)) (M := 1) (by
            rw [Complex.norm_real, Real.norm_eq_abs]; exact hαt2)
          rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos ht0] at h
          exact h.trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (sq_nonneg t) hα1) (Real.exp_pos _).le)
        calc K4 * t ^ 4 * |Real.exp (α * t ^ 2) - 1|
            ≤ K4 * t ^ 4 * (Real.exp 1 * t ^ 2) := mul_le_mul_of_nonneg_left he (by positivity)
          _ = Real.exp 1 * K4 * t ^ 6 := by ring
      refine ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
      have hc : Real.exp 1 / 6 + Real.exp 1 * M_e0 * K4 ^ 2 / 2 + Real.exp 1 * K4 ≤ M_e2 := by
        dsimp only [M_e2]
        have : (1 : ℝ) ≤ (K4 + 1) ^ 2 := by nlinarith
        nlinarith [Real.exp_pos (1 : ℝ)]
      calc _ ≤ (Real.exp 1 / 6 + Real.exp 1 * M_e0 * K4 ^ 2 / 2 + Real.exp 1 * K4) * t ^ 6 := by linarith
        _ ≤ M_e2 * t ^ 6 := mul_le_mul_of_nonneg_right hc (pow_nonneg ht0.le 6)
    have hsplit : Real.exp u * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
        (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1 - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4 =
        (Real.exp u - 1 - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4) +
        Real.exp u * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) * (1 + stripDeltaCurv c (fctThetaD v0') t) - 1) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add hexp_u_sub ?_)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp u * |Real.exp (-stripDeltaCurv c (fctThetaD v0') t) * (1 + stripDeltaCurv c (fctThetaD v0') t) - 1|
        ≤ M_e0 * (M_e1 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16) :=
          mul_le_mul hexp_u_bd (hΔ_exp_bd t ht) (abs_nonneg _) (Real.exp_pos _).le
      _ = M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 := by ring
  -- Continuity of `t ↦ D_*(m(t)) * m'(t) / m(t)^p` on `Ioc 0 t₃`
  have hD_cont : ∀ p : ℕ, ContinuousOn (fun t : ℝ => stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p) (Ioc 0 t₃) := by
    intro p
    refine ContinuousOn.congr ?_ (fun t ht => by
      rw [hD_inner_eq t ⟨ht.1, ht.2.trans ht3_lt.le⟩])
    have hm_c : ContinuousOn uctM (Ioi 0) := fun t ht => (hasDerivAt_uctM ht).continuousAt.continuousWithinAt
    have hmd_c : ContinuousOn uctMderiv (Ioi 0) := by
      unfold uctMderiv uctEllDeriv
      refine continuousOn_const.mul ((continuousOn_const.div ((continuousOn_const.mul continuousOn_id).div_const 2)
        fun t (ht : t ∈ Ioi (0 : ℝ)) => (div_pos (mul_pos Real.pi_pos ht) two_pos).ne').sub
        (continuousOn_const.div (Real.continuous_sinh.comp (continuous_const.mul ((continuous_const.mul continuous_id).div_const 2))).continuousOn
          fun t (ht : t ∈ Ioi (0 : ℝ)) => (Real.sinh_pos_iff.mpr (mul_pos two_pos (div_pos (mul_pos Real.pi_pos ht) two_pos))).ne'))
    have hΔ_c : ContinuousOn (stripDeltaCurv c (fctThetaD v0')) (Ioi 0) := by
      unfold stripDeltaCurv
      exact continuousOn_const.mul (((contDiff_iteratedDeriv_infty hθ0_cd 2).continuous.continuousOn.div hmd_c
        fun t ht => (uctMderiv_pos ht).ne').sub ((hθ0_cd.continuous_deriv (by simp)).continuousOn.div hm_c
        fun t ht => (uctM_pos ht).ne'))
    exact ((((continuousOn_const.mul (hmd_c.div (hm_c.rpow_const fun t ht => Or.inl (uctM_pos ht).ne')
      fun t ht => (Real.rpow_pos_of_pos (uctM_pos ht) _).ne')).mul
      (((Real.continuous_exp.comp (((continuous_const.mul (continuous_id.pow 4)).neg).add
        (continuous_const.mul (continuous_id.pow 2)))).continuousOn.mul
        ((Real.continuous_exp.comp_continuousOn hΔ_c.neg).mul (continuousOn_const.add hΔ_c))).sub
        continuousOn_const)).div (hm_c.pow p) fun t ht => pow_ne_zero p (uctM_pos ht).ne').mono Ioc_subset_Ioi_self)
  have hfl_eq : ∀ (p : ℕ) {t : ℝ}, 0 < t → t < 1 / 4 →
      uctAlphaFl * (uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p =
        (uctAlphaFl * mD t / mQ t ^ (3 / 2 + (p : ℝ))) / t ^ (2 * p + 2) := by
    intro p t ht0 ht14
    have hmQ_pos : 0 < mQ t := mQ_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)
    have hr1 : (t ^ 2 * mQ t) ^ (3 / 2 : ℝ) = t ^ 3 * mQ t ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (sq_nonneg t) hmQ_pos.le, ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]; norm_num
    have hr2 : mQ t ^ (3 / 2 : ℝ) * mQ t ^ p = mQ t ^ (3 / 2 + (p : ℝ)) := by
      rw [← Real.rpow_natCast (mQ t) p, ← Real.rpow_add hmQ_pos]
    rw [uctMderiv_eq_mul_mD ht0 ht14, uctM_eq_sq_mul_mQ ht0, hr1, mul_pow, ← pow_mul, div_div, mul_div_assoc, div_div]
    have hden : t ^ 3 * mQ t ^ (3 / 2 : ℝ) * (t ^ (2 * p) * mQ t ^ p) = t ^ (2 * p + 2) * t * mQ t ^ (3 / 2 + (p : ℝ)) := by
      rw [← hr2]; ring
    rw [hden]
    field_simp [ht0.ne', (Real.rpow_pos_of_pos hmQ_pos _).ne']
  -- Part A: `p = 0` (`∫_0^{3δ_L} D_*(L) dL = O_{K₄}(τ₁³ + |α| τ₁)`)!
  have hpartA : IntegrableOn (stripDstar kind c v v0') (Ioc 0 (3 * uctM τ₁)) ∧
      |∫ L in Ioc 0 (3 * uctM τ₁), stripDstar kind c v v0' L| ≤ C_all * (τ₁ ^ 3 + |α| * τ₁) := by
    have h3m_pos : 0 < 3 * uctM τ₁ := mul_pos (by norm_num) (uctM_pos hτ₁)
    have himg : uctM '' Ioc (0 : ℝ) t₃ = Ioc 0 (3 * uctM τ₁) := by
      ext L; constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨uctM_pos ht.1, (uctM_strictMonoOn.monotoneOn ht.1 ht3_pos ht.2).trans_eq (ceEll_tau0 h3m_pos)⟩
      · intro hL
        refine ⟨tau0 L, ⟨tau0_pos hL.1, ?_⟩, ceEll_tau0 hL.1⟩
        by_contra hgt; push Not at hgt
        have := uctM_strictMonoOn ht3_pos (tau0_pos hL.1) hgt
        rw [show uctM t₃ = 3 * uctM τ₁ from ceEll_tau0 h3m_pos,
          show uctM (tau0 L) = L from ceEll_tau0 hL.1] at this; linarith [hL.2]
    have hpt0 : ∀ t ∈ Ioc (0 : ℝ) t₃,
        ‖stripDstar kind c v v0' (uctM t) * uctMderiv t‖ ≤
          M_fl * (|α| + 2 * (K4 + 1) * M_e0 * (2 * τ₁) ^ 2 + M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * (2 * τ₁) ^ 14) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have ht2τ : t ≤ 2 * τ₁ := ht.2.trans ht3_lt.le
      have ht18 : t ≤ 1 / 8 := by linarith [ht2τ, hτ₁_100]
      have hfl0 := hfl_eq 0 ht0 (by linarith)
      simp only [pow_zero, div_one, Nat.cast_zero, add_zero, mul_zero, zero_add] at hfl0
      rw [hD_inner_eq t ⟨ht0, ht2τ⟩, hfl0, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_pos ht0]
      have hmfl_le : 0 ≤ uctAlphaFl * mD t / mQ t ^ (3 / 2 : ℝ) := by
        have h1 : 0 < uctAlphaFl := by unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
        have h2 := mD_pos_of_mem (by rw [abs_of_pos ht0]; linarith)
        have h3 := mQ_pos_of_mem (by rw [abs_of_pos ht0]; linarith)
        positivity
      have hmfl_up : uctAlphaFl * mD t / mQ t ^ (3 / 2 : ℝ) ≤ M_fl := by
        simpa using hMfl_bd 0 (by omega) t ⟨ht0.le, ht18⟩
      have hfac := hfac_bd1 t ⟨ht0, ht2τ⟩
      have hrem : |Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
          (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1| / t ^ 2 ≤
          |α| + 2 * (K4 + 1) * M_e0 * (2 * τ₁) ^ 2 + M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * (2 * τ₁) ^ 14 := by
        have htri : |Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
            (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1| ≤
            |α| * t ^ 2 + (2 * (K4 + 1) * M_e0 * t ^ 4 + M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16) := by
          have hrew : Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
              (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1 =
              α * t ^ 2 + (Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
                (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1 - α * t ^ 2) := by ring
          rw [hrew]; refine (abs_add_le _ _).trans (add_le_add ?_ hfac)
          rw [abs_mul, abs_pow, abs_of_pos ht0]
        rw [div_le_iff₀ (sq_pos_of_pos ht0)]
        have ht2 : t ^ 2 ≤ (2 * τ₁) ^ 2 := pow_le_pow_left₀ ht0.le ht2τ 2
        have ht14 : t ^ 14 ≤ (2 * τ₁) ^ 14 := pow_le_pow_left₀ ht0.le ht2τ 14
        have h1 : 2 * (K4 + 1) * M_e0 * t ^ 4 ≤ 2 * (K4 + 1) * M_e0 * (2 * τ₁) ^ 2 * t ^ 2 := by
          rw [show t ^ 4 = t ^ 2 * t ^ 2 by ring, mul_assoc (2 * (K4 + 1) * M_e0)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)) (by positivity)
        have h2 : M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 ≤
            M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * (2 * τ₁) ^ 14 * t ^ 2 := by
          rw [show t ^ 16 = t ^ 14 * t ^ 2 by ring, mul_assoc (M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ))]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht14 (sq_nonneg t))
            (mul_nonneg (mul_nonneg (mul_nonneg hMe1_nn (Real.exp_pos _).le) (sq_nonneg _)) (zpow_nonneg hτ₁.le _))
        linarith
      rw [abs_of_nonneg hmfl_le, div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul hmfl_up hrem (by positivity) hMfl_nn
    have hint_t : IntegrableOn (fun t => stripDstar kind c v v0' (uctM t) * uctMderiv t) (Ioc 0 t₃) := by
      have hc0 : ContinuousOn (fun t => stripDstar kind c v v0' (uctM t) * uctMderiv t) (Ioc 0 t₃) := by
        simpa only [pow_zero, div_one] using hD_cont 0
      exact (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
        (hc0.aestronglyMeasurable measurableSet_Ioc)
        (ae_restrict_of_forall_mem measurableSet_Ioc hpt0)
    have hL_int : IntegrableOn (stripDstar kind c v v0') (Ioc 0 (3 * uctM τ₁)) := by
      rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc (f := uctM) (f' := uctMderiv)
        (fun t ht => (hasDerivAt_uctM ht.1).hasDerivWithinAt) (uctM_strictMonoOn.injOn.mono Ioc_subset_Ioi_self)]
      exact hint_t.congr_fun (fun t ht => by simp [smul_eq_mul, abs_of_pos (uctMderiv_pos ht.1), mul_comm]) measurableSet_Ioc
    refine ⟨hL_int, ?_⟩
    rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc (f := uctM) (f' := uctMderiv)
      (fun t ht => (hasDerivAt_uctM ht.1).hasDerivWithinAt) (uctM_strictMonoOn.injOn.mono Ioc_subset_Ioi_self)]
    have hcongr : (∫ t in Ioc 0 t₃, |uctMderiv t| • stripDstar kind c v v0' (uctM t)) =
        ∫ t in Ioc 0 t₃, stripDstar kind c v v0' (uctM t) * uctMderiv t :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by simp [smul_eq_mul, abs_of_pos (uctMderiv_pos ht.1), mul_comm]
    rw [hcongr]
    have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hpt0
    rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ht3_pos.le] at hbd
    have hpow16 : c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * (2 * τ₁) ^ 14 * (2 * τ₁) = 2 ^ 15 * τ₁ ^ 5 := by
      rw [hc_inv, show (-18 : ℤ) = -((18 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
      field_simp [hτ₁.ne']
    have hτ5 : τ₁ ^ 5 ≤ τ₁ ^ 3 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    refine hbd.trans ?_
    calc M_fl * (|α| + 2 * (K4 + 1) * M_e0 * (2 * τ₁) ^ 2 + M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * (2 * τ₁) ^ 14) * t₃
        ≤ M_fl * (|α| + 2 * (K4 + 1) * M_e0 * (2 * τ₁) ^ 2 + M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * (2 * τ₁) ^ 14) * (2 * τ₁) :=
          mul_le_mul_of_nonneg_left ht3_lt.le (by have := zpow_nonneg hτ₁.le (-18 : ℤ); positivity)
      _ = M_fl * (2 * |α| * τ₁ + 16 * (K4 + 1) * M_e0 * τ₁ ^ 3 + M_e1 * M_e0 * (c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * (2 * τ₁) ^ 14 * (2 * τ₁))) := by ring
      _ = M_fl * (2 * |α| * τ₁ + 16 * (K4 + 1) * M_e0 * τ₁ ^ 3 + M_e1 * M_e0 * (2 ^ 15 * τ₁ ^ 5)) := by rw [hpow16]
      _ ≤ M_fl * (2 * |α| * τ₁ + 16 * (K4 + 1) * M_e0 * τ₁ ^ 3 + 2 ^ 15 * M_e1 * M_e0 * τ₁ ^ 3) := by
          have : M_e1 * M_e0 * (2 ^ 15 * τ₁ ^ 5) ≤ 2 ^ 15 * M_e1 * M_e0 * τ₁ ^ 3 := by
            rw [show M_e1 * M_e0 * (2 ^ 15 * τ₁ ^ 5) = 2 ^ 15 * M_e1 * M_e0 * τ₁ ^ 5 by ring]
            exact mul_le_mul_of_nonneg_left hτ5 (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) hMfl_nn
      _ ≤ C_p0 * (τ₁ ^ 3 + |α| * τ₁) := by
          dsimp only [C_p0]
          have hnn1 : 0 ≤ M_fl * (16 * (K4 + 1) * M_e0 + 2 ^ 15 * M_e1 * M_e0) * (|α| * τ₁) := by positivity
          have hnn2 : 0 ≤ M_fl * 2 * τ₁ ^ 3 := by positivity
          linarith
      _ ≤ C_all * (τ₁ ^ 3 + |α| * τ₁) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  refine ⟨hpartA.1, hpartA.2, fun p hp1 hp2 => ?_⟩
  -- Part B: `p ∈ {1, 2}` inner finite part on `(ε, t₃]`!
  let fIn : ℝ → ℝ := fun t => stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p
  let A_s : ℝ := if p = 1 then 0 else α * aF 2 0 / 3
  let B_s : ℝ := if p = 1 then α * aF 1 0 else α * aF 2 1 + (α ^ 2 / 2 - K4) * aF 2 0
  let S_p : ℝ → ℝ := fun t => (3 * A_s) / t ^ 4 + B_s / t ^ 2
  -- Show `fIn t - S_p t` is bounded on `(0, t₃]` by a constant times `|α| * t^{2-2p}?` No, bounded on `(0, t₃]`!
  -- Specifically:
  -- - `p = 1`: `|fIn t - B_s / t²| ≤ |α| * (|aF 1 1| + CF 1) + M_fl * (2*(K4+1)*M_e0 + M_e1*M_e0*c⁻²*τ₁⁻¹⁸*t¹²)`,
  --   integrates over `(0, t₃]` to `≤ C * (|α| τ₁ + τ₁) ≤ C * (τ₁ + |α| τ₁⁻¹)`!
  -- - `p = 2`: `|fIn t - (3 A_s / t⁴ + B_s / t²)| ≤ |α|*(|aF 2 2| + CF 2) + |α²/2 - K4|*(|aF 2 1| + |aF 2 2| + CF 2) + M_fl * (M_e2 + M_e1*M_e0*c⁻²*τ₁⁻¹⁸*t¹⁰)`,
  --   integrates over `(0, t₃]` to `≤ C * τ₁ ≤ C * (τ₁⁻¹ + |α| τ₁⁻³)`!
  -- And `∫_ε^{t₃} S_p(t) dt = (A_s / ε³ + B_s / ε) - (A_s / t₃³ + B_s / t₃)`, where `|A_s/t₃³ + B_s/t₃| ≤ C * (τ₁^{3-2p} + |α| τ₁^{1-2p})`!
  have hrem_bd : ∃ K_r ≥ 0, K_r * (2 * τ₁) ≤ (C_p12 - (|aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1))) *
        (τ₁ ^ (3 - 2 * (p : ℤ)) + |α| * τ₁ ^ (1 - 2 * (p : ℤ))) ∧
      ∀ t ∈ Ioc (0 : ℝ) t₃, ‖fIn t - S_p t‖ ≤ K_r := by
    -- Actually even simpler: bound `|fIn t - S_p t|` directly by a clean `K_r`!
    set K_r : ℝ := (|aF 1 1| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (K4 + 2) +
      M_fl * (2 * M_e2 + 2 ^ 12 * M_e1 * M_e0)
    have hKr_nn : 0 ≤ K_r := by have := hCF_nn 1; have := hCF_nn 2; positivity
    refine ⟨K_r, hKr_nn, ?_, fun t ht => ?_⟩
    · -- `K_r * (2 * τ₁) ≤ ... * (τ₁^{3-2p} + |α| τ₁^{1-2p})` since `τ₁ ≤ τ₁^{3-2p}` for `p ∈ {1, 2}`!
      have hτ_le : τ₁ ≤ τ₁ ^ (3 - 2 * (p : ℤ)) := by
        rcases (show p = 1 ∨ p = 2 by omega) with rfl | rfl
        · norm_num
        · rw [show (3 : ℤ) - 2 * ((2 : ℕ) : ℤ) = -1 by norm_num, zpow_neg_one]
          exact hτ₁_1.trans ((one_le_inv₀ hτ₁).mpr hτ₁_1)
      have h2Kr : 2 * K_r ≤ C_p12 - (|aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1)) := by
        dsimp only [K_r, C_p12]
        have h1 : 0 ≤ |aF 1 0| := abs_nonneg _
        have h2 : 0 ≤ |aF 1 1| := abs_nonneg _
        have h3 : 0 ≤ |aF 2 0| := abs_nonneg _
        have h4 : 0 ≤ |aF 2 1| := abs_nonneg _
        have h5 : 0 ≤ |aF 2 2| := abs_nonneg _
        have h6 : 0 ≤ CF 1 := hCF_nn 1
        have h7 : 0 ≤ CF 2 := hCF_nn 2
        have hS_nn : 0 ≤ |aF 1 0| + |aF 1 1| + |aF 2 0| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2 := by positivity
        have hpart1_le : 2 * ((|aF 1 1| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (K4 + 2)) ≤
            (|aF 1 0| + |aF 1 1| + |aF 2 0| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (2 * (K4 + 2)) := by
          rw [show 2 * ((|aF 1 1| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (K4 + 2)) =
            (|aF 1 1| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (2 * (K4 + 2)) by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have hpart2_le : |aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1) ≤
            (|aF 1 0| + |aF 1 1| + |aF 2 0| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (2 * (K4 + 1) + 2) := by
          have ha : |aF 1 0| + |aF 2 0| ≤ (|aF 1 0| + |aF 1 1| + |aF 2 0| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * 2 := by linarith
          have hb : (|aF 2 1| + |aF 2 0|) * (K4 + 1) ≤ (|aF 1 0| + |aF 1 1| + |aF 2 0| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (2 * (K4 + 1)) := by
            exact mul_le_mul (by linarith) (by linarith) (by linarith) hS_nn
          linarith
        have hpart_tot : (|aF 1 0| + |aF 1 1| + |aF 2 0| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (2 * (K4 + 2)) +
            (|aF 1 0| + |aF 1 1| + |aF 2 0| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (2 * (K4 + 1) + 2) ≤
            (|aF 1 0| + |aF 1 1| + |aF 2 0| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (16 * (K4 + 1) + 8) := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (by linarith) hS_nn
        have h8 : 0 ≤ M_fl * M_e2 := by positivity
        have h9 : 0 ≤ M_fl * (M_e1 * M_e0) := by positivity
        linarith
      calc K_r * (2 * τ₁) = (2 * K_r) * τ₁ := by ring
        _ ≤ (C_p12 - (|aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1))) * τ₁ :=
            mul_le_mul_of_nonneg_right h2Kr hτ₁.le
        _ ≤ (C_p12 - (|aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1))) *
              (τ₁ ^ (3 - 2 * (p : ℤ)) + |α| * τ₁ ^ (1 - 2 * (p : ℤ))) :=
            mul_le_mul_of_nonneg_left (hτ_le.trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (zpow_nonneg hτ₁.le _)))) (by linarith)
    · -- Pointwise bound `|fIn t - S_p t| ≤ K_r` for `t ∈ Ioc 0 t₃`!
      have ht0 : 0 < t := ht.1
      have ht2τ : t ≤ 2 * τ₁ := ht.2.trans ht3_lt.le
      have ht18 : t ≤ 1 / 8 := by linarith [ht2τ, hτ₁_100]
      have ht1 : t ≤ 1 := by linarith
      have hflp := hfl_eq p ht0 (by linarith)
      let Wp : ℝ := uctAlphaFl * mD t / mQ t ^ (3 / 2 + (p : ℝ))
      have hWp_nn : 0 ≤ Wp := by
        have h1 : 0 < uctAlphaFl := by unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
        have h2 := mD_pos_of_mem (by rw [abs_of_pos ht0]; linarith)
        have h3 := mQ_pos_of_mem (by rw [abs_of_pos ht0]; linarith)
        exact div_nonneg (mul_nonneg h1.le h2.le) (Real.rpow_nonneg h3.le _)
      have hWp_le : Wp ≤ M_fl := hMfl_bd p hp2 t ⟨ht0.le, ht18⟩
      let E : ℝ := Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-stripDeltaCurv c (fctThetaD v0') t) *
        (1 + stripDeltaCurv c (fctThetaD v0') t)) - 1
      have hfIn_eq : fIn t = Wp / t ^ (2 * p + 2) * E := by
        dsimp only [fIn, E]
        rw [hD_inner_eq t ⟨ht0, ht2τ⟩, mul_div_right_comm, hflp]
      have hE_bd := hfac_bd2 t ⟨ht0, ht2τ⟩
      have hαK4 : |α ^ 2 / 2 - K4| ≤ K4 + 1 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_div, abs_pow, show |(2 : ℝ)| = 2 by norm_num, abs_of_nonneg hK4_nn]
        have hsq : |α| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg α) hα1
        linarith
      have hc16 : c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 10 ≤ 2 ^ 10 := by
        rw [hc_inv, show (-18 : ℤ) = -((18 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
        have ht10 : t ^ 10 ≤ (2 * τ₁) ^ 10 := pow_le_pow_left₀ ht0.le ht2τ 10
        calc (τ₁ ^ 4) ^ 2 * (τ₁ ^ 18)⁻¹ * t ^ 10 ≤ (τ₁ ^ 4) ^ 2 * (τ₁ ^ 18)⁻¹ * (2 * τ₁) ^ 10 :=
              mul_le_mul_of_nonneg_left ht10 (by positivity)
          _ = 2 ^ 10 := by field_simp [hτ₁.ne']
      have hK4_le_Me2 : K4 + 1 ≤ M_e2 := by
        dsimp only [M_e2]
        have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
        have h2 : K4 + 1 ≤ (K4 + 1) ^ 2 := by rw [sq]; exact le_mul_of_one_le_right (by linarith) (by linarith)
        have h12 : K4 + 1 ≤ Real.exp 1 * (K4 + 1) ^ 2 := h2.trans (le_mul_of_one_le_left (sq_nonneg _) h1)
        have h3 : 0 ≤ Real.exp 1 * M_e0 * K4 ^ 2 / 2 := by positivity
        have h4 : 0 ≤ Real.exp 1 * K4 := by positivity
        linarith
      rw [Real.norm_eq_abs, hfIn_eq]
      rcases (show p = 1 ∨ p = 2 by omega) with rfl | rfl
      · -- `p = 1`: `S_1 t = α * aF 1 0 / t²`
        have hS1 : S_p t = α * aF 1 0 / t ^ 2 := by dsimp only [S_p, A_s, B_s]; simp
        have hsplit : Wp / t ^ 4 * E - S_p t =
            α * ((Wp - (aF 1 0 + aF 1 1 * t ^ 2)) / t ^ 4 * t ^ 2 + aF 1 1) +
            Wp * ((α ^ 2 / 2 - K4) + (E - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4) / t ^ 4) := by
          rw [hS1]; field_simp [ht0.ne']; ring
        rw [show 2 * 1 + 2 = 4 by norm_num, hsplit]
        have hW_rem : |Wp - (aF 1 0 + aF 1 1 * t ^ 2)| / t ^ 4 ≤ CF 1 := by
          have h := hCF_bd 1 t ⟨ht0.le, ht18⟩
          rw [Fin.sum_univ_two] at h; simp only [Fin.val_zero, mul_zero, pow_zero, mul_one, Fin.val_one, mul_one,
            Nat.cast_one] at h
          rw [div_le_iff₀ (pow_pos ht0 4)]; simpa [Wp] using h
        have hE_rem : |E - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4| / t ^ 4 ≤ M_e2 + 2 ^ 10 * M_e1 * M_e0 := by
          rw [div_le_iff₀ (pow_pos ht0 4)]
          have h1 : M_e2 * t ^ 6 ≤ M_e2 * t ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht0.le ht1 (by norm_num)) (by positivity)
          have h2 : M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 ≤ 2 ^ 10 * M_e1 * M_e0 * t ^ 4 := by
            have ht12 : t ^ 12 ≤ t ^ 10 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
            calc M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16
                = M_e1 * M_e0 * (c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 12) * t ^ 4 := by ring
              _ ≤ M_e1 * M_e0 * (c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 10) * t ^ 4 := by
                  have : c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 12 ≤ c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 10 :=
                    mul_le_mul_of_nonneg_left ht12 (mul_nonneg (sq_nonneg _) (zpow_nonneg hτ₁.le _))
                  gcongr
              _ ≤ M_e1 * M_e0 * 2 ^ 10 * t ^ 4 := by gcongr
              _ = 2 ^ 10 * M_e1 * M_e0 * t ^ 4 := by ring
          linarith
        have hpart1_bd : |α * ((Wp - (aF 1 0 + aF 1 1 * t ^ 2)) / t ^ 4 * t ^ 2 + aF 1 1)| ≤ CF 1 + |aF 1 1| := by
          rw [abs_mul]
          refine (mul_le_of_le_one_left (abs_nonneg _) hα1).trans ((abs_add_le _ _).trans ?_)
          rw [abs_mul, abs_div, abs_pow, abs_pow, abs_of_pos ht0]
          have h1 : |Wp - (aF 1 0 + aF 1 1 * t ^ 2)| / t ^ 4 * t ^ 2 ≤ CF 1 :=
            (mul_le_of_le_one_right (by positivity) (pow_le_one₀ ht0.le ht1)).trans hW_rem
          linarith
        have hpart2_bd : |Wp * ((α ^ 2 / 2 - K4) + (E - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4) / t ^ 4)| ≤
            M_fl * (2 * M_e2 + 2 ^ 10 * M_e1 * M_e0) := by
          rw [abs_mul, abs_of_nonneg hWp_nn]
          refine mul_le_mul hWp_le ((abs_add_le _ _).trans ?_) (abs_nonneg _) hMfl_nn
          rw [abs_div, abs_pow, abs_of_pos ht0]; linarith
        refine (abs_add_le _ _).trans ?_
        dsimp only [K_r]
        have hnn1 : 0 ≤ (|aF 1 1| + |aF 2 1| + |aF 2 2| + CF 1 + CF 2) * (K4 + 1) := by have := hCF_nn 1; have := hCF_nn 2; positivity
        have hnn2 : 0 ≤ |aF 2 1| + |aF 2 2| + CF 2 := by have := hCF_nn 2; positivity
        have hnn3 : 0 ≤ M_fl * (M_e1 * M_e0) := by positivity
        linarith
      · -- `p = 2`: `S_2 t = α * aF 2 0 / t⁴ + (α * aF 2 1 + (α²/2 - K4) * aF 2 0) / t²`
        have hS2 : S_p t = α * aF 2 0 / t ^ 4 + (α * aF 2 1 + (α ^ 2 / 2 - K4) * aF 2 0) / t ^ 2 := by
          dsimp only [S_p, A_s, B_s]; simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]; ring
        have hsplit : Wp / t ^ 6 * E - S_p t =
            α * ((Wp - (aF 2 0 + aF 2 1 * t ^ 2 + aF 2 2 * t ^ 4)) / t ^ 6 * t ^ 2 + aF 2 2) +
            (α ^ 2 / 2 - K4) * ((Wp - (aF 2 0 + aF 2 1 * t ^ 2 + aF 2 2 * t ^ 4)) / t ^ 6 * t ^ 4 + aF 2 1 + aF 2 2 * t ^ 2) +
            Wp * ((E - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4) / t ^ 6) := by
          rw [hS2]; field_simp [ht0.ne']; ring
        rw [show 2 * 2 + 2 = 6 by norm_num, hsplit]
        have hW_rem : |Wp - (aF 2 0 + aF 2 1 * t ^ 2 + aF 2 2 * t ^ 4)| / t ^ 6 ≤ CF 2 := by
          have h := hCF_bd 2 t ⟨ht0.le, ht18⟩
          rw [Fin.sum_univ_three] at h
          simp only [Fin.val_zero, mul_zero, pow_zero, mul_one, Fin.val_one, mul_one, Fin.val_two, Nat.cast_ofNat] at h
          rw [div_le_iff₀ (pow_pos ht0 6)]; simpa [Wp, add_assoc] using h
        have hE_rem : |E - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4| / t ^ 6 ≤ M_e2 + 2 ^ 10 * M_e1 * M_e0 := by
          rw [div_le_iff₀ (pow_pos ht0 6)]
          have h2 : M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16 ≤ 2 ^ 10 * M_e1 * M_e0 * t ^ 6 := by
            calc M_e1 * M_e0 * c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 16
                = M_e1 * M_e0 * (c⁻¹ ^ 2 * τ₁ ^ (-18 : ℤ) * t ^ 10) * t ^ 6 := by ring
              _ ≤ M_e1 * M_e0 * 2 ^ 10 * t ^ 6 := by gcongr
              _ = 2 ^ 10 * M_e1 * M_e0 * t ^ 6 := by ring
          linarith
        have hp1 : |α * ((Wp - (aF 2 0 + aF 2 1 * t ^ 2 + aF 2 2 * t ^ 4)) / t ^ 6 * t ^ 2 + aF 2 2)| ≤ CF 2 + |aF 2 2| := by
          rw [abs_mul]
          refine (mul_le_of_le_one_left (abs_nonneg _) hα1).trans ((abs_add_le _ _).trans ?_)
          rw [abs_mul, abs_div, abs_pow, abs_pow, abs_of_pos ht0]
          have h1 : |Wp - (aF 2 0 + aF 2 1 * t ^ 2 + aF 2 2 * t ^ 4)| / t ^ 6 * t ^ 2 ≤ CF 2 :=
            (mul_le_of_le_one_right (by positivity) (pow_le_one₀ ht0.le ht1)).trans hW_rem
          linarith
        have hp2' : |(α ^ 2 / 2 - K4) * ((Wp - (aF 2 0 + aF 2 1 * t ^ 2 + aF 2 2 * t ^ 4)) / t ^ 6 * t ^ 4 + aF 2 1 + aF 2 2 * t ^ 2)| ≤
            (K4 + 1) * (CF 2 + |aF 2 1| + |aF 2 2|) := by
          rw [abs_mul]
          refine mul_le_mul hαK4 ?_ (abs_nonneg _) (by positivity)
          refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
          rw [abs_mul, abs_div, abs_pow, abs_pow, abs_mul, abs_pow, abs_of_pos ht0]
          have h1 : |Wp - (aF 2 0 + aF 2 1 * t ^ 2 + aF 2 2 * t ^ 4)| / t ^ 6 * t ^ 4 ≤ CF 2 :=
            (mul_le_of_le_one_right (by positivity) (pow_le_one₀ ht0.le ht1)).trans hW_rem
          have h2 : |aF 2 2| * t ^ 2 ≤ |aF 2 2| := mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht0.le ht1)
          linarith
        have hp3 : |Wp * ((E - α * t ^ 2 - (α ^ 2 / 2 - K4) * t ^ 4) / t ^ 6)| ≤ M_fl * (M_e2 + 2 ^ 10 * M_e1 * M_e0) := by
          rw [abs_mul, abs_of_nonneg hWp_nn, abs_div, abs_pow, abs_of_pos ht0]
          exact mul_le_mul hWp_le hE_rem (by positivity) hMfl_nn
        refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
        dsimp only [K_r]
        have hnn1 : 0 ≤ (|aF 1 1| + CF 1) * (K4 + 2) := by have := hCF_nn 1; positivity
        have hnn2 : 0 ≤ |aF 2 1| := abs_nonneg _
        have hnn3 : 0 ≤ M_fl * M_e2 := by positivity
        have hnn4 : 0 ≤ M_fl * (M_e1 * M_e0) := by positivity
        linarith
  obtain ⟨K_r, hKr_nn, hKr_le, hKr_pt⟩ := hrem_bd
  have hS_cont : ContinuousOn S_p (Ioi 0) :=
    (continuousOn_const.div (continuousOn_id.pow 4) fun t ht => pow_ne_zero 4 (mem_Ioi.mp ht).ne').add
      (continuousOn_const.div (continuousOn_id.pow 2) fun t ht => pow_ne_zero 2 (mem_Ioi.mp ht).ne')
  have hrem_int : IntegrableOn (fun t : ℝ => fIn t - S_p t) (Ioc 0 t₃) :=
    (integrableOn_const (C := K_r) (hs := measure_Ioc_lt_top.ne)).mono'
      (((hD_cont p).sub (hS_cont.mono Ioc_subset_Ioi_self)).aestronglyMeasurable measurableSet_Ioc)
      (ae_restrict_of_forall_mem measurableSet_Ioc hKr_pt)
  refine ⟨A_s, B_s, (∫ t in Ioc (0 : ℝ) t₃, (fIn t - S_p t)) - (A_s / t₃ ^ 3 + B_s / t₃), ?_, ?_⟩
  · -- Limit as `ε ↓ 0`
    have heq_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (∫ t in Ioc ε t₃, fIn t) - (A_s / ε ^ 3 + B_s / ε) =
        (∫ t in Ioc ε t₃, (fIn t - S_p t)) - (A_s / t₃ ^ 3 + B_s / t₃) := by
      filter_upwards [Ioo_mem_nhdsGT ht3_pos] with ε hε
      have hε0 : 0 < ε := hε.1
      have hS_int : IntegrableOn S_p (Ioc ε t₃) :=
        ((hS_cont.mono fun t (ht : t ∈ Icc ε t₃) => lt_of_lt_of_le hε0 ht.1).integrableOn_Icc).mono_set Ioc_subset_Icc_self
      have hf_int : IntegrableOn fIn (Ioc ε t₃) :=
        (((hD_cont p).mono fun t (ht : t ∈ Icc ε t₃) => ⟨lt_of_lt_of_le hε0 ht.1, ht.2⟩).integrableOn_Icc).mono_set Ioc_subset_Icc_self
      have hS_val : (∫ t in Ioc ε t₃, S_p t) = (A_s / ε ^ 3 + B_s / ε) - (A_s / t₃ ^ 3 + B_s / t₃) := by
        rw [← intervalIntegral.integral_of_le hε.2.le]
        let P : ℝ → ℝ := fun t => -(A_s / t ^ 3) - B_s / t
        have hd : ∀ t ∈ uIcc ε t₃, HasDerivAt P (S_p t) t := fun t ht => by
          rw [uIcc_of_le hε.2.le] at ht
          have ht0 : t ≠ 0 := (lt_of_lt_of_le hε0 ht.1).ne'
          have h3 : HasDerivAt (fun s => -(A_s / s ^ 3)) ((3 * A_s) / t ^ 4) t := by
            have := (((hasDerivAt_pow 3 t).inv (pow_ne_zero 3 ht0)).const_mul A_s).neg
            refine this.congr_deriv ?_; field_simp [ht0]; ring
          have h1 : HasDerivAt (fun s => B_s / s) (-B_s / t ^ 2) t := by
            have := (hasDerivAt_inv ht0).const_mul B_s
            refine this.congr_deriv ?_; field_simp [ht0]
          exact (h3.sub h1).congr_deriv (by dsimp only [S_p]; ring)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hε.2.le).mpr hS_int)]
        dsimp only [P]; ring
      have hsub := integral_sub hf_int hS_int
      linarith
    have hlim : Tendsto (fun ε : ℝ => ∫ t in Ioc ε t₃, (fIn t - S_p t)) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ t in Ioc (0 : ℝ) t₃, (fIn t - S_p t))) := by
      have hinter0 : Ioi (0 : ℝ) ∩ Ioc (0 : ℝ) t₃ = Ioc (0 : ℝ) t₃ := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
        exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
      have hind_int : IntegrableOn ((Ioc (0 : ℝ) t₃).indicator (fun t => fIn t - S_p t)) (Ioi (0 : ℝ)) volume := by
        rw [integrableOn_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) t₃)).nullMeasurableSet]
        exact hrem_int.mono_set inter_subset_left
      have h := FctPhiKill.tendsto_setIntegral_Ioi_zero hind_int
      rw [setIntegral_indicator measurableSet_Ioc, hinter0] at h
      refine h.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT ht3_pos] with ε hε
      rw [setIntegral_indicator measurableSet_Ioc]
      have : Ioi ε ∩ Ioc (0 : ℝ) t₃ = Ioc ε t₃ := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
        exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, hε.1.trans h1, h2⟩⟩
      rw [this]
    exact (hlim.sub tendsto_const_nhds).congr' (heq_ev.mono fun _ h => h.symm)
  · -- Bound `|L₃| ≤ C_all * (τ₁^{3-2p} + |α| τ₁^{1-2p})`!
    have hrem_int_bd : |∫ t in Ioc (0 : ℝ) t₃, (fIn t - S_p t)| ≤ K_r * (2 * τ₁) := by
      have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hKr_pt
      rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ht3_pos.le] at hbd
      exact hbd.trans (mul_le_mul_of_nonneg_left ht3_lt.le hKr_nn)
    have hpole_bd : |A_s / t₃ ^ 3 + B_s / t₃| ≤
        (|aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1)) *
          (τ₁ ^ (3 - 2 * (p : ℤ)) + |α| * τ₁ ^ (1 - 2 * (p : ℤ))) := by
      have ht3_inv : t₃⁻¹ ≤ τ₁⁻¹ := (inv_le_inv₀ ht3_pos hτ₁).mpr ht3_gt.le
      have ht3_inv3 : (t₃ ^ 3)⁻¹ ≤ (τ₁ ^ 3)⁻¹ :=
        (inv_le_inv₀ (pow_pos ht3_pos 3) (pow_pos hτ₁ 3)).mpr (pow_le_pow_left₀ hτ₁.le ht3_gt.le 3)
      dsimp only [A_s, B_s]
      rcases (show p = 1 ∨ p = 2 by omega) with rfl | rfl
      · -- `p = 1`: `A_s = 0`, `B_s = α * aF 1 0`
        simp only [↓reduceIte, zero_add, abs_mul, abs_of_pos ht3_pos,
          show (3 : ℤ) - 2 * ((1 : ℕ) : ℤ) = 1 by norm_num, show (1 : ℤ) - 2 * ((1 : ℕ) : ℤ) = -1 by norm_num,
          zpow_one, zpow_neg_one, div_eq_mul_inv, zero_mul, abs_inv]
        have h1 : |α| * |aF 1 0| * t₃⁻¹ ≤ |aF 1 0| * (|α| * τ₁⁻¹) := by
          rw [show |aF 1 0| * (|α| * τ₁⁻¹) = |α| * |aF 1 0| * τ₁⁻¹ by ring]
          exact mul_le_mul_of_nonneg_left ht3_inv (by positivity)
        have h2 : |aF 1 0| ≤ |aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1) := by
          have ha : 0 ≤ |aF 2 1| * (K4 + 1) := mul_nonneg (abs_nonneg _) (by linarith)
          have hb : 0 ≤ |aF 2 0| * (K4 + 1) := mul_nonneg (abs_nonneg _) (by linarith)
          linarith [abs_nonneg (aF 2 0)]
        have hstep1 : |α| * |aF 1 0| * t₃⁻¹ ≤ |aF 1 0| * (τ₁ + |α| * τ₁⁻¹) :=
          h1.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hτ₁.le) (abs_nonneg _))
        exact hstep1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
      · -- `p = 2`: `A_s = α * aF 2 0 / 3`, `B_s = α * aF 2 1 + (α²/2 - K4) * aF 2 0`
        simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte,
          show (3 : ℤ) - 2 * ((2 : ℕ) : ℤ) = -1 by norm_num, show (1 : ℤ) - 2 * ((2 : ℕ) : ℤ) = -3 by norm_num,
          show (-3 : ℤ) = -((3 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
        have hαK4 : |α ^ 2 / 2 - K4| ≤ K4 + 1 := by
          refine (abs_sub _ _).trans ?_
          rw [abs_div, abs_pow, show |(2 : ℝ)| = 2 by norm_num, abs_of_nonneg hK4_nn]
          have hsq : |α| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg α) hα1
          linarith
        have hA_bd : |α * aF 2 0 / 3 / t₃ ^ 3| ≤ |aF 2 0| * (|α| * (τ₁ ^ 3)⁻¹) := by
          rw [abs_div, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (pow_pos ht3_pos 3), div_eq_mul_inv]
          calc |α| * |aF 2 0| / 3 * (t₃ ^ 3)⁻¹ ≤ |α| * |aF 2 0| * (τ₁ ^ 3)⁻¹ :=
                mul_le_mul (div_le_self (by positivity) (by norm_num)) ht3_inv3 (by positivity) (by positivity)
            _ = |aF 2 0| * (|α| * (τ₁ ^ 3)⁻¹) := by ring
        have hB_bd : |(α * aF 2 1 + (α ^ 2 / 2 - K4) * aF 2 0) / t₃| ≤
            (|aF 2 1| + (K4 + 1) * |aF 2 0|) * τ₁⁻¹ := by
          rw [abs_div, abs_of_pos ht3_pos, div_eq_mul_inv]
          have hnum : |α * aF 2 1 + (α ^ 2 / 2 - K4) * aF 2 0| ≤ |aF 2 1| + (K4 + 1) * |aF 2 0| := by
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hα1
            · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hαK4 (abs_nonneg _)
          exact mul_le_mul hnum ht3_inv (by positivity) (by positivity)
        refine (abs_add_le _ _).trans ((add_le_add hA_bd hB_bd).trans ?_)
        have h1 : |aF 2 0| ≤ |aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1) := by
          have ha : 0 ≤ |aF 2 1| * (K4 + 1) := mul_nonneg (abs_nonneg _) (by linarith)
          have hb : 0 ≤ |aF 2 0| * (K4 + 1) := mul_nonneg (abs_nonneg _) (by linarith)
          linarith [abs_nonneg (aF 1 0)]
        have h2 : |aF 2 1| + (K4 + 1) * |aF 2 0| ≤ |aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1) := by
          have : |aF 2 1| ≤ |aF 2 1| * (K4 + 1) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
          linarith [abs_nonneg (aF 1 0), abs_nonneg (aF 2 0)]
        have ha := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ |α| * (τ₁ ^ 3)⁻¹)
        have hb := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ τ₁⁻¹)
        exact (add_le_add ha hb).trans (le_of_eq (by rw [zpow_one]; ring))
    refine ((abs_sub _ _).trans (add_le_add (hrem_int_bd.trans hKr_le) hpole_bd)).trans ?_
    have hsum : (C_p12 - (|aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1))) *
          (τ₁ ^ (3 - 2 * (p : ℤ)) + |α| * τ₁ ^ (1 - 2 * (p : ℤ))) +
        (|aF 1 0| + |aF 2 0| + |aF 2 1| * (K4 + 1) + |aF 2 0| * (K4 + 1)) *
          (τ₁ ^ (3 - 2 * (p : ℤ)) + |α| * τ₁ ^ (1 - 2 * (p : ℤ))) =
        C_p12 * (τ₁ ^ (3 - 2 * (p : ℤ)) + |α| * τ₁ ^ (1 - 2 * (p : ℤ))) := by ring
    rw [hsum]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg (zpow_nonneg hτ₁.le _) (mul_nonneg (abs_nonneg _) (zpow_nonneg hτ₁.le _)))

/-! ### Helper 7: Finite-part bound for `e^v - 1 - v` on `(0, 10 τ₁]` (`p ∈ {1, 2}`) -/

set_option maxHeartbeats 800000 in
lemma fp_exp_quad_bound (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 100 ∧
    ∀ K4 : ℝ, 1 ≤ K4 →
      ∃ C ≥ 0, ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
        τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
        let v := vTotal kind K4 c α τ₁
        ∀ p : ℕ, 1 ≤ p → p ≤ 2 →
          ∃ A Lq : ℝ,
            Tendsto (fun ε : ℝ =>
              (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1 - v t) / uctM t ^ p) -
                A / ε) (𝓝[>] (0 : ℝ)) (𝓝 Lq) ∧
            |Lq| ≤ C * τ₁ ^ (3 - 2 * (p : ℤ)) := by
  obtain ⟨τ₀_p1, hτ₀_p1_pos, _, Cv0b, Cv0m, Cva, Cv1b, Cv1m, Cth0b, Cth0m, _, _, _,
    _, _, _, _, _, _, _, hCv_nn, hCth_nn, _, _, hpart1⟩ := fct_comp_D_part1 kind
  -- Fixed constants from `f0Base kind` and `hFac / mQ^p` on `[0, 1/8]`!
  obtain ⟨af0, Cf0, hCf0_nn, hf0_bd⟩ := even_smooth_taylor_bound (contDiffOn_f0Base kind)
    (fun t ht => by unfold f0Base; rw [r0Smooth_even ht]) 2
  -- `f0Base kind 0 = 0` ⇒ `af0 0 = 0`, so `f0Base kind t = af0 1 * t² + O(t⁴)` on `[0, 1/8]`!
  have haf0_0 : af0 0 = 0 := by
    have h := hf0_bd 0 ⟨le_rfl, by norm_num⟩
    rw [Fin.sum_univ_two] at h
    simp only [Fin.val_zero, mul_zero, pow_zero, mul_one, Fin.val_one, mul_one, zero_pow (by norm_num : 2 ≠ 0),
      zero_pow (by norm_num : 4 ≠ 0), mul_zero, add_zero, f0Base, r0Smooth_zero, Real.log_one, neg_zero, zero_sub,
      abs_neg] at h
    exact abs_nonpos_iff.mp h
  let hFac : ℝ → ℝ := fun t =>
    let sQ := (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re
    match kind with
    | .ce => 1 / sQ ^ 2
    | .star => 1 / sQ ^ 2 + (π * t / 2) ^ 2 / Real.cosh (π * t / 2) ^ 2
  have hsQ_cd : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re) (Ioo (-1 / 4) (1 / 4)) :=
    (Complex.reCLM.contDiff.comp (CtOuter.differentiable_sinhQ.contDiff.restrict_scalars ℝ |>.comp
      (Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).div_const 2)))).contDiffOn
  have hsQ_ne : ∀ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4), (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re ^ 2 ≠ 0 := fun t ht => by
    have hx2 : ‖((π * t / 2 : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos, show |(2 : ℝ)| = 2 by norm_num]
      have : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      nlinarith [Real.pi_lt_four, abs_nonneg t]
    exact pow_ne_zero 2 (CtOuter.re_sinhQ_pos hx2).ne'
  have hhFac_cd : ContDiffOn ℝ (⊤ : ℕ∞) hFac (Ioo (-1 / 4) (1 / 4)) := by
    dsimp only [hFac]; cases kind
    · exact (contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne).add
        ((((contDiff_const.mul contDiff_id).div_const 2).pow 2).contDiffOn.div
          (((Real.contDiff_cosh.comp ((contDiff_const.mul contDiff_id).div_const 2)).pow 2).contDiffOn)
          fun _ _ => pow_ne_zero 2 (Real.cosh_pos _).ne')
    · exact contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne
  have hhFac_even : ∀ t : ℝ, hFac (-t) = hFac t := fun t => by
    have hq : CtOuter.sinhQ ((π * -t / 2 : ℝ) : ℂ) = CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ) := by
      rw [show (π * -t / 2 : ℝ) = -(π * t / 2) by ring, Complex.ofReal_neg]
      unfold CtOuter.sinhQ; refine tsum_congr fun n => ?_; rw [(even_two_mul n).neg_pow]
    dsimp only [hFac]; cases kind
    · rw [hq, show π * -t / 2 = -(π * t / 2) by ring, Real.cosh_neg, neg_sq]
    · rw [hq]
  have hhFac_eq : ∀ t : ℝ, 0 < t → ‖stripH0 kind ((t : ℂ) * Complex.I)‖ = hFac t / t ^ 2 := fun t ht => by
    have hx : 0 < π * t / 2 := by positivity
    have hsQ : (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re = Real.sinh (π * t / 2) / (π * t / 2) := by
      rw [CtOuter.sinhQ_ofReal hx.ne', Complex.ofReal_re]
    have hsh : Real.sinh (π * t / 2) ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
    dsimp only [hFac]; rw [hsQ]; cases kind
    · rw [norm_stripH0_star_imag ht]; field_simp [ht.ne', Real.pi_ne_zero, hsh, (Real.cosh_pos _).ne']; ring
    · rw [norm_stripH0_ce_imag ht]; field_simp [ht.ne', Real.pi_ne_zero, hsh]; ring
  obtain ⟨aw2, Cw2, hCw2_nn, hw2_bd⟩ := even_smooth_taylor_bound
    ((contDiffOn_const (c := uctAlphaOsc) |>.mul hhFac_cd).div (contDiffOn_mQ.pow 2) fun t ht =>
      pow_ne_zero 2 (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne')
    (fun t _ => by simp only [Pi.div_apply]; rw [hhFac_even, mQ_even]) 1
  obtain ⟨mQ_min, hmQ_min_pos, hmQ_min_bd⟩ : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8), c ≤ mQ t := by
    have hcont := contDiffOn_mQ.continuousOn.mono (show Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4) (1 / 4) from
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn ⟨0, le_rfl, by norm_num⟩ hcont
    exact ⟨mQ t₀, mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩), fun t ht => hmin ht⟩
  obtain ⟨mD_min, hmD_min_pos, hmD_min_bd⟩ : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8), c ≤ mD t := by
    have hcont := contDiffOn_mD.continuousOn.mono (show Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4) (1 / 4) from
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn ⟨0, le_rfl, by norm_num⟩ hcont
    exact ⟨mD t₀, mD_pos_of_mem (abs_lt.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩), fun t ht => hmin ht⟩
  have hαo_nn : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
  set M_W : ℝ := uctAlphaOsc * (1 + π ^ 2 / 4) / (min 1 mQ_min) ^ 2
  have hMW_nn : 0 ≤ M_W := by positivity
  refine ⟨min τ₀_p1 (1 / 100), lt_min hτ₀_p1_pos (by norm_num), min_le_right _ _, fun K4 hK4 => ?_⟩
  have hK4_nn : 0 ≤ K4 := by linarith
  set M_v : ℝ := Cv0b 0 + K4 * Cv0m 0 + Cv1b 0 + K4 * Cv1m 0 + Cva 0
  set M_th1 : ℝ := Cth0b 1 + K4 * Cth0m 1
  set M_th2 : ℝ := Cth0b 2 + K4 * Cth0m 2
  set M_Δ : ℝ := (1 / 2) * (M_th2 / mD_min + M_th1 / mQ_min)
  set c2_bd : ℝ := |af0 1| + 1
  set M_r : ℝ := Cf0 + K4 + M_Δ
  have hMv_nn : 0 ≤ M_v := by obtain ⟨h1, h2, h3, h4, h5⟩ := hCv_nn 0; positivity
  have hMth1_nn : 0 ≤ M_th1 := by obtain ⟨h1, h2, _, _, _⟩ := hCth_nn 1; positivity
  have hMth2_nn : 0 ≤ M_th2 := by obtain ⟨h1, h2, _, _, _⟩ := hCth_nn 2; positivity
  have hMΔ_nn : 0 ≤ M_Δ := by positivity
  have hMr_nn : 0 ≤ M_r := by positivity
  set M_q : ℝ := c2_bd * M_r + M_r ^ 2 / 2 + (Real.exp M_v / 6) * (c2_bd + M_r) ^ 3
  set C_tot : ℝ := M_W * ((Real.exp M_v / 2) * ((c2_bd + M_r) ^ 2 + M_v ^ 2 * 10) + M_q) +
    |aw2 0| * (c2_bd ^ 2 / 2) + Cw2 * (c2_bd ^ 2 / 2)
  refine ⟨C_tot, by positivity, fun {c α τ₁} hc hτ₁ hτ₁_le hc_eq hα_le p hp1 hp2 => ?_⟩
  have hτ₁_p1 : τ₁ ≤ τ₀_p1 := hτ₁_le.trans (min_le_left _ _)
  have hτ₁_100 : τ₁ ≤ 1 / 100 := hτ₁_le.trans (min_le_right _ _)
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have hc_inv : c⁻¹ = τ₁ ^ 4 := by
    rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
  have hα1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
  obtain ⟨⟨hb0_cd, hm0_cd, _, _, _, hv_cd⟩, ⟨hb0_ev, hm0_ev, _, _, _, _⟩, _, ⟨hb0_s, hm0_s, _, _, _, hv_s, _⟩,
    hmom, hinner, hderivs, _, hth_in, _, _, _, _⟩ := hpart1 hK4 hc hτ₁ hτ₁_p1 hc_eq hα_le
  let v := vTotal kind K4 c α τ₁
  let v0' := v0 kind K4 τ₁
  have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) v0' := hb0_cd.add (contDiff_const.mul hm0_cd)
  have hv0_cs : HasCompactSupport v0' :=
    (hasCompactSupport_of_support_Ioo hb0_s).add (hasCompactSupport_of_support_Ioo hm0_s).mul_left
  have hv0_ev : ∀ t, v0' (-t) = v0' t := fun t => by dsimp only [v0']; unfold v0; rw [hb0_ev, hm0_ev]
  have hθ0_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD v0') := contDiff_fctThetaD hv0_cd hv0_cs
  have hθ0_odd : ∀ t, fctThetaD v0' (-t) = -fctThetaD v0' t := fctThetaD_odd hv0_ev
  have hθ0_10 : deriv (fctThetaD v0') 0 = 0 := by rw [← iteratedDeriv_one]; exact (hmom 0 (by omega)).2.2.2.2.1
  have hθ0_20 : iteratedDeriv 2 (fctThetaD v0') 0 = 0 := by
    have h1 : iteratedDeriv 2 (fun t => fctThetaD v0' (-t)) 0 = iteratedDeriv 2 (fctThetaD v0') 0 := by
      rw [iteratedDeriv_comp_neg, neg_zero]; norm_num
    have h2 : iteratedDeriv 2 (fun t => fctThetaD v0' (-t)) 0 = -iteratedDeriv 2 (fctThetaD v0') 0 := by
      rw [show (fun t => fctThetaD v0' (-t)) = -fctThetaD v0' by ext t; exact hθ0_odd t, iteratedDeriv_neg]
    linarith
  -- Global bound `|v t| ≤ M_v * τ₁^2 ≤ M_v`
  have hv_abs : ∀ t : ℝ, |v t| ≤ M_v * τ₁ ^ 2 := fun t => by
    obtain ⟨d1, d2, d3, d4, d5⟩ := hderivs 0 t
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at d1 d2 d3 d4 d5
    have hτ4 : τ₁ ^ (4 : ℤ) ≤ τ₁ ^ 2 := by rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h1b : c⁻¹ * τ₁ ^ (-1 : ℤ) ≤ τ₁ ^ 2 := by
      rw [hc_inv, zpow_neg_one, show τ₁ ^ 4 * τ₁⁻¹ = τ₁ ^ 3 by field_simp [hτ₁.ne']]
      exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h1m : c⁻¹ * τ₁ ^ (1 : ℤ) ≤ τ₁ ^ 2 := by
      rw [hc_inv, zpow_one, ← pow_succ]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have d1' : |v0Base kind τ₁ t| ≤ Cv0b 0 * τ₁ ^ 2 := by simpa [zpow_two, ← sq] using d1
    have d2' : |v0Marg τ₁ t| ≤ Cv0m 0 * τ₁ ^ 2 := d2.trans (mul_le_mul_of_nonneg_left hτ4 (hCv_nn 0).2.1)
    have d3' : |vAlpha α τ₁ t| ≤ Cva 0 * τ₁ ^ 2 := d3.trans (by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
      have := mul_le_mul_of_nonneg_left hα1 (hCv_nn 0).2.2.1; rw [mul_one] at this
      exact mul_le_mul_of_nonneg_right this (sq_nonneg τ₁))
    have d4' : |v1Base kind c τ₁ t| ≤ Cv1b 0 * τ₁ ^ 2 := d4.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1b (hCv_nn 0).2.2.2.1)
    have d5' : |v1Marg c τ₁ t| ≤ Cv1m 0 * τ₁ ^ 2 := d5.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1m (hCv_nn 0).2.2.2.2)
    have htri : |v t| ≤ |v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t| + |v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t| + |vAlpha α τ₁ t| := by
      dsimp only [v]; unfold vTotal v0 v1
      have a1 := abs_add_le ((v0Base kind τ₁ t + K4 * v0Marg τ₁ t) + (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)) (vAlpha α τ₁ t)
      have a2 := abs_add_le (v0Base kind τ₁ t + K4 * v0Marg τ₁ t) (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)
      have a3 := abs_add_le (v0Base kind τ₁ t) (K4 * v0Marg τ₁ t)
      have a4 := abs_add_le (v1Base kind c τ₁ t) (K4 * v1Marg c τ₁ t)
      rw [abs_mul, abs_of_nonneg hK4_nn] at a3 a4; linarith
    have hm1 := mul_le_mul_of_nonneg_left d2' hK4_nn
    have hm2 := mul_le_mul_of_nonneg_left d5' hK4_nn
    calc |v t| ≤ |v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t| + |v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t| + |vAlpha α τ₁ t| := htri
      _ ≤ Cv0b 0 * τ₁ ^ 2 + K4 * (Cv0m 0 * τ₁ ^ 2) + Cv1b 0 * τ₁ ^ 2 + K4 * (Cv1m 0 * τ₁ ^ 2) + Cva 0 * τ₁ ^ 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add d1' hm1) d4') hm2) d3'
      _ = M_v * τ₁ ^ 2 := by dsimp only [M_v]; ring
  -- On `(0, τ₁]`: `v t = c₂ * t² + r(t)` where `c₂ = af0 1 + α` (`|c₂| ≤ c2_bd`) and `|r(t)| ≤ M_r * τ₁⁻¹ * t⁴`!
  set c2 : ℝ := af0 1 + α
  have hc2_le : |c2| ≤ c2_bd := (abs_add_le _ _).trans (add_le_add le_rfl hα1)
  have hv_in_split : ∀ t ∈ Ioc (0 : ℝ) τ₁, |v t - c2 * t ^ 2| ≤ M_r * τ₁⁻¹ * t ^ 4 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht18 : t ≤ 1 / 8 := by linarith [ht.2, hτ₁_100]
    have ht14 : t < 1 / 4 := by linarith
    have hin := hinner t (by rw [abs_of_pos ht0]; linarith [ht.2])
    have hv_eq : v t - c2 * t ^ 2 = (f0Base kind t - af0 1 * t ^ 2) - K4 * t ^ 4 - stripDeltaCurv c (fctThetaD v0') t := by
      dsimp only [v, c2]; unfold vTotal v0
      have h1 : v1 kind K4 c τ₁ t = -stripDeltaCurv c (fctThetaD v0') t := by
        rw [hin.2.2.2.1, deltaCurvSmooth_eq hθ0_cd hθ0_10 hθ0_20 ht0 ht14]; rfl
      rw [hin.1, hin.2.1, hin.2.2.1, h1]; ring
    have hf0_r : |f0Base kind t - af0 1 * t ^ 2| ≤ Cf0 * t ^ 4 := by
      have h := hf0_bd t ⟨ht0.le, ht18⟩
      rw [Fin.sum_univ_two] at h
      simp only [Fin.val_zero, mul_zero, pow_zero, mul_one, haf0_0, zero_add, Fin.val_one, mul_one] at h
      exact h
    have hΔ_bd : |stripDeltaCurv c (fctThetaD v0') t| ≤ M_Δ * τ₁⁻¹ * t ^ 4 := by
      have hb0_cs := hasCompactSupport_of_support_Ioo hb0_s
      have hm0_cs := hasCompactSupport_of_support_Ioo hm0_s
      have hθ0b_cd := contDiff_fctThetaD hb0_cd hb0_cs
      have hθ0m_cd := contDiff_fctThetaD hm0_cd hm0_cs
      have hlin : fctThetaD v0' = fun s => fctThetaD (v0Base kind τ₁) s + K4 * fctThetaD (v0Marg τ₁) s := by
        ext s; dsimp only [v0']; unfold v0
        simpa only [one_mul] using fctThetaD_linear hb0_cd hb0_cs hm0_cd hm0_cs 1 K4 s
      have ht12 : |t| ≤ 12 * τ₁ := by rw [abs_of_pos ht0]; linarith [ht.2]
      have h1 := hth_in 1 t ht12
      have h2 := hth_in 2 t ht12
      have hτ3 : τ₁ ^ ((4 : ℤ) - (1 : ℕ)) ≤ τ₁ := by
        rw [show (4 : ℤ) - (1 : ℕ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
        simpa using pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num : 1 ≤ 3)
      have hτ2 : τ₁ ^ ((4 : ℤ) - (2 : ℕ)) ≤ 1 := by
        rw [show (4 : ℤ) - (2 : ℕ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact pow_le_one₀ hτ₁.le hτ₁_1
      have hd1_le : |deriv (fctThetaD v0') t| ≤ M_th1 * τ₁ * (t / τ₁) ^ 10 := by
        rw [← iteratedDeriv_one, hlin]
        change |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) t| ≤ _
        rw [iteratedDeriv_add (hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
          ((contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
          iteratedDeriv_const_mul_field]
        have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 10) ≤ (t / τ₁) ^ 10 := by rw [abs_of_pos ht0]; exact min_le_right _ _
        have d1 : |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 1 * τ₁ * (t / τ₁) ^ 10 := by
          have h1' : |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 1 * τ₁ * min 1 ((|t| / τ₁) ^ 10) := by
            simpa [show (2 : ℤ) - (1 : ℕ) = 1 by norm_num] using h1.1
          exact h1'.trans (mul_le_mul_of_nonneg_left hmin (mul_nonneg (hCth_nn 1).1 hτ₁.le))
        have d2 : |iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m 1 * τ₁ * (t / τ₁) ^ 10 :=
          h1.2.1.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ3 (hCth_nn 1).2.1)
            (le_min zero_le_one (by positivity))).trans (mul_le_mul_of_nonneg_left hmin (mul_nonneg (hCth_nn 1).2.1 hτ₁.le)))
        calc |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t|
            ≤ |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| :=
              (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK4_nn])
          _ ≤ Cth0b 1 * τ₁ * (t / τ₁) ^ 10 + K4 * (Cth0m 1 * τ₁ * (t / τ₁) ^ 10) :=
              add_le_add d1 (mul_le_mul_of_nonneg_left d2 hK4_nn)
          _ = M_th1 * τ₁ * (t / τ₁) ^ 10 := by dsimp only [M_th1]; ring
      have hd2_le : |iteratedDeriv 2 (fctThetaD v0') t| ≤ M_th2 * (t / τ₁) ^ 9 := by
        rw [hlin]
        change |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) t| ≤ _
        rw [iteratedDeriv_add (hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
          ((contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
          iteratedDeriv_const_mul_field]
        have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 9) ≤ (t / τ₁) ^ 9 := by rw [abs_of_pos ht0]; exact min_le_right _ _
        have d1 : |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 2 * (t / τ₁) ^ 9 := by
          have h2' : |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 2 * min 1 ((|t| / τ₁) ^ 9) := by
            simpa [show (2 : ℤ) - (2 : ℕ) = 0 by norm_num] using h2.1
          exact h2'.trans (mul_le_mul_of_nonneg_left hmin (hCth_nn 2).1)
        have d2 : |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m 2 * (t / τ₁) ^ 9 := by
          refine h2.2.1.trans ?_
          have := mul_le_mul_of_nonneg_left hτ2 (hCth_nn 2).2.1; rw [mul_one] at this
          exact (mul_le_mul_of_nonneg_right this (le_min zero_le_one (by positivity))).trans
            (mul_le_mul_of_nonneg_left hmin (hCth_nn 2).2.1)
        calc |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t|
            ≤ |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| :=
              (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK4_nn])
          _ ≤ Cth0b 2 * (t / τ₁) ^ 9 + K4 * (Cth0m 2 * (t / τ₁) ^ 9) :=
              add_le_add d1 (mul_le_mul_of_nonneg_left d2 hK4_nn)
          _ = M_th2 * (t / τ₁) ^ 9 := by dsimp only [M_th2]; ring
      unfold stripDeltaCurv
      rw [uctMderiv_eq_mul_mD ht0 ht14, uctM_eq_sq_mul_mQ ht0, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * c))]
      have hmD_ge := hmD_min_bd t ⟨ht0.le, ht18⟩
      have hmQ_ge := hmQ_min_bd t ⟨ht0.le, ht18⟩
      have hrat4 : (t / τ₁) ^ 4 ≤ 1 := pow_le_one₀ (div_nonneg ht0.le hτ₁.le) ((div_le_one hτ₁).mpr ht.2)
      have hA : |iteratedDeriv 2 (fctThetaD v0') t / (t * mD t)| ≤ (M_th2 / mD_min) * τ₁ ^ (-5 : ℤ) * t ^ 4 := by
        rw [abs_div, abs_of_pos (mul_pos ht0 (mD_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)))]
        calc |iteratedDeriv 2 (fctThetaD v0') t| / (t * mD t)
            ≤ (M_th2 * (t / τ₁) ^ 9) / (t * mD_min) :=
              div_le_div₀ (by positivity) hd2_le (by positivity) (mul_le_mul_of_nonneg_left hmD_ge ht0.le)
          _ = (M_th2 / mD_min) * τ₁ ^ (-5 : ℤ) * t ^ 4 * (t / τ₁) ^ 4 := by
              rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
              field_simp [ht0.ne', hτ₁.ne', hmD_min_pos.ne']
          _ ≤ (M_th2 / mD_min) * τ₁ ^ (-5 : ℤ) * t ^ 4 * 1 :=
              mul_le_mul_of_nonneg_left hrat4 (mul_nonneg (mul_nonneg (div_nonneg hMth2_nn hmD_min_pos.le) (zpow_nonneg hτ₁.le _)) (pow_nonneg ht0.le 4))
          _ = (M_th2 / mD_min) * τ₁ ^ (-5 : ℤ) * t ^ 4 := mul_one _
      have hB : |deriv (fctThetaD v0') t / (t ^ 2 * mQ t)| ≤ (M_th1 / mQ_min) * τ₁ ^ (-5 : ℤ) * t ^ 4 := by
        rw [abs_div, abs_of_pos (mul_pos (sq_pos_of_pos ht0) (mQ_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)))]
        calc |deriv (fctThetaD v0') t| / (t ^ 2 * mQ t)
            ≤ (M_th1 * τ₁ * (t / τ₁) ^ 10) / (t ^ 2 * mQ_min) :=
              div_le_div₀ (by positivity) hd1_le (by positivity) (mul_le_mul_of_nonneg_left hmQ_ge (sq_nonneg t))
          _ = (M_th1 / mQ_min) * τ₁ ^ (-5 : ℤ) * t ^ 4 * (t / τ₁) ^ 4 := by
              rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
              field_simp [ht0.ne', hτ₁.ne', hmQ_min_pos.ne']
          _ ≤ (M_th1 / mQ_min) * τ₁ ^ (-5 : ℤ) * t ^ 4 * 1 :=
              mul_le_mul_of_nonneg_left hrat4 (mul_nonneg (mul_nonneg (div_nonneg hMth1_nn hmQ_min_pos.le) (zpow_nonneg hτ₁.le _)) (pow_nonneg ht0.le 4))
          _ = (M_th1 / mQ_min) * τ₁ ^ (-5 : ℤ) * t ^ 4 := mul_one _
      calc (1 / (2 * c)) * |iteratedDeriv 2 (fctThetaD v0') t / (t * mD t) - deriv (fctThetaD v0') t / (t ^ 2 * mQ t)|
          ≤ (1 / (2 * c)) * ((M_th2 / mD_min) * τ₁ ^ (-5 : ℤ) * t ^ 4 + (M_th1 / mQ_min) * τ₁ ^ (-5 : ℤ) * t ^ 4) :=
            mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hA hB)) (by positivity)
        _ = M_Δ * (c⁻¹ * τ₁ ^ (-5 : ℤ)) * t ^ 4 := by dsimp only [M_Δ]; field_simp [hc.ne']
        _ = M_Δ * τ₁⁻¹ * t ^ 4 := by
            rw [hc_inv, show (-5 : ℤ) = -((5 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast]
            field_simp [hτ₁.ne']
    have h1_le_inv : (1 : ℝ) ≤ τ₁⁻¹ := (one_le_inv₀ hτ₁).mpr hτ₁_1
    rw [hv_eq]
    refine ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans ?_
    rw [abs_mul, abs_of_nonneg hK4_nn, abs_pow, abs_of_pos ht0]
    have ha : Cf0 * t ^ 4 ≤ Cf0 * τ₁⁻¹ * t ^ 4 := by
      have := mul_le_mul_of_nonneg_left h1_le_inv hCf0_nn; rw [mul_one] at this
      exact mul_le_mul_of_nonneg_right this (pow_nonneg ht0.le 4)
    have hb : K4 * t ^ 4 ≤ K4 * τ₁⁻¹ * t ^ 4 := by
      have := mul_le_mul_of_nonneg_left h1_le_inv hK4_nn; rw [mul_one] at this
      exact mul_le_mul_of_nonneg_right this (pow_nonneg ht0.le 4)
    dsimp only [M_r]; linarith
  -- Weight bound on `(0, 10 τ₁]`: `α_osc |H_0(it)| / m(t)^p ≤ M_W / t^{2p + 2}`
  have hW_bd : ∀ t ∈ Ioc (0 : ℝ) (10 * τ₁),
      uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p ≤ M_W / t ^ (2 * p + 2) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht18 : t ≤ 1 / 8 := by linarith [ht.2, hτ₁_100]
    have hH := (norm_stripH0_imag_le kind ht0).1
    have hmQ_ge := hmQ_min_bd t ⟨ht0.le, ht18⟩
    have hmp_ge : (min 1 mQ_min) ^ 2 * t ^ (2 * p) ≤ uctM t ^ p := by
      rw [uctM_eq_sq_mul_mQ ht0, mul_pow, ← pow_mul, mul_comm]
      have hmin_nn : 0 ≤ min 1 mQ_min := le_min zero_le_one hmQ_min_pos.le
      have h1 : (min 1 mQ_min) ^ 2 ≤ mQ t ^ p :=
        (pow_le_pow_of_le_one hmin_nn (min_le_left _ _) hp2).trans (pow_le_pow_left₀ hmin_nn ((min_le_right _ _).trans hmQ_ge) p)
      exact mul_le_mul_of_nonneg_left h1 (pow_nonneg ht0.le _)
    have hmin_pos : 0 < (min 1 mQ_min) ^ 2 := sq_pos_of_pos (lt_min zero_lt_one hmQ_min_pos)
    calc uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p
        ≤ uctAlphaOsc * ((1 + π ^ 2 / 4) / t ^ 2) / ((min 1 mQ_min) ^ 2 * t ^ (2 * p)) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hH hαo_nn) (by positivity) hmp_ge
      _ = M_W / t ^ (2 * p + 2) := by
          dsimp only [M_W]; rw [pow_add]; field_simp [ht0.ne', hmin_pos.ne']
  let fq : ℝ → ℝ := fun t => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1 - v t) / uctM t ^ p
  have hfq_cont : ContinuousOn fq (Ioi 0) := by
    have hm_c : ContinuousOn uctM (Ioi 0) := fun t ht => (hasDerivAt_uctM ht).continuousAt.continuousWithinAt
    have hH_c : ContinuousOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖) (Ioi 0) := by
      cases kind
      · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_star_imag ht
        exact (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
          ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
          fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')).add
          (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_cosh.comp
            ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
            fun _ _ => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.cosh_pos _).ne'))
      · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_ce_imag ht
        exact continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
          ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
          fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')
    exact ((continuousOn_const.mul hH_c).mul
      (((Real.continuous_exp.comp hv_cd.continuous).sub continuous_const).sub hv_cd.continuous).continuousOn).div
      (hm_c.pow p) fun t ht => pow_ne_zero p (uctM_pos ht).ne'
  have hfq_zero_out : ∀ t : ℝ, 10 * τ₁ < t → fq t = 0 := fun t ht => by
    have hvt : v t = 0 := by by_contra hne; linarith [(hv_s hne).2]
    dsimp only [fq]; rw [hvt, Real.exp_zero]; ring
  -- Tail `(τ₁, 10 τ₁]`: `|e^v - 1 - v| ≤ (e^{M_v}/2) M_v² τ₁⁴`, `|fq t| ≤ M_W * (e^{M_v}/2) * M_v² * τ₁^{2-2p}`!
  have htail_bd : IntegrableOn fq (Ioc τ₁ (10 * τ₁)) ∧
      |∫ t in Ioc τ₁ (10 * τ₁), fq t| ≤ M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10 * τ₁ ^ (3 - 2 * (p : ℤ)) := by
    have hpt : ∀ t ∈ Ioc τ₁ (10 * τ₁), ‖fq t‖ ≤ M_W * (Real.exp M_v / 2) * M_v ^ 2 * τ₁ ^ (2 - 2 * (p : ℤ)) := by
      intro t ht
      have ht0 : 0 < t := hτ₁.trans ht.1
      have hvt_le : |v t| ≤ M_v := (hv_abs t).trans (mul_le_of_le_one_right hMv_nn (pow_le_one₀ hτ₁.le hτ₁_1))
      have hev : |Real.exp (v t) - 1 - v t| ≤ (Real.exp M_v / 2) * (M_v ^ 2 * τ₁ ^ 4) := by
        have h := abs_exp_sub_one_sub_le hvt_le
        have hv2 : v t ^ 2 ≤ M_v ^ 2 * τ₁ ^ 4 := by
          rw [← sq_abs]
          calc |v t| ^ 2 ≤ (M_v * τ₁ ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hv_abs t) 2
            _ = M_v ^ 2 * τ₁ ^ 4 := by ring
        exact h.trans (mul_le_mul_of_nonneg_left hv2 (by positivity))
      have ht_pow : τ₁ ^ (2 * p + 2) ≤ t ^ (2 * p + 2) := pow_le_pow_left₀ hτ₁.le ht.1.le _
      dsimp only [fq]; rw [Real.norm_eq_abs, mul_div_right_comm, abs_mul,
        abs_of_nonneg (div_nonneg (mul_nonneg hαo_nn (norm_nonneg _)) (pow_nonneg (uctM_pos ht0).le p))]
      calc uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p * |Real.exp (v t) - 1 - v t|
          ≤ (M_W / t ^ (2 * p + 2)) * ((Real.exp M_v / 2) * (M_v ^ 2 * τ₁ ^ 4)) :=
            mul_le_mul (hW_bd t ⟨ht0, ht.2⟩) hev (abs_nonneg _) (by positivity)
        _ ≤ (M_W / τ₁ ^ (2 * p + 2)) * ((Real.exp M_v / 2) * (M_v ^ 2 * τ₁ ^ 4)) := by
            gcongr
        _ = M_W * (Real.exp M_v / 2) * M_v ^ 2 * τ₁ ^ (2 - 2 * (p : ℤ)) := by
            have hpow : τ₁ ^ 4 / τ₁ ^ (2 * p + 2) = τ₁ ^ (2 - 2 * (p : ℤ)) := by
              rw [← zpow_natCast τ₁ 4, ← zpow_natCast τ₁ (2 * p + 2), ← zpow_sub₀ hτ₁.ne']
              congr 1; omega
            rw [← hpow]; ring
    have hint : IntegrableOn fq (Ioc τ₁ (10 * τ₁)) :=
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
        ((hfq_cont.mono fun t (ht : t ∈ Ioc τ₁ (10 * τ₁)) => hτ₁.trans ht.1).aestronglyMeasurable measurableSet_Ioc)
        (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
    refine ⟨hint, ?_⟩
    have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hpt
    rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at hbd
    refine hbd.trans ?_
    have h9 : 10 * τ₁ - τ₁ ≤ 10 * τ₁ := by linarith
    have hexp : τ₁ ^ (2 - 2 * (p : ℤ)) * τ₁ = τ₁ ^ (3 - 2 * (p : ℤ)) := by
      rw [mul_comm, ← zpow_one_add₀ hτ₁.ne']; congr 1; omega
    calc M_W * (Real.exp M_v / 2) * M_v ^ 2 * τ₁ ^ (2 - 2 * (p : ℤ)) * (10 * τ₁ - τ₁)
        ≤ M_W * (Real.exp M_v / 2) * M_v ^ 2 * τ₁ ^ (2 - 2 * (p : ℤ)) * (10 * τ₁) :=
          mul_le_mul_of_nonneg_left h9 (mul_nonneg (by positivity) (zpow_nonneg hτ₁.le _))
      _ = M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10 * (τ₁ ^ (2 - 2 * (p : ℤ)) * τ₁) := by ring
      _ = M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10 * τ₁ ^ (3 - 2 * (p : ℤ)) := by rw [hexp]
  -- Inner `(0, τ₁]`: split `p = 1` (directly integrable!) vs `p = 2` (pull out `aw2 0 * (c2²/2) / t²`)!
  have hv_t2 : ∀ t ∈ Ioc (0 : ℝ) τ₁, |v t| ≤ (c2_bd + M_r) * t ^ 2 := fun t ht => by
    have ht0 : 0 < t := ht.1
    have hsplit := hv_in_split t ht
    have ht_rat : τ₁⁻¹ * t ^ 2 ≤ 1 := by
      have h1 : t ≤ τ₁ := ht.2
      have h2 : t ^ 2 ≤ τ₁ := (pow_le_pow_of_le_one ht0.le (by linarith) (by norm_num : 1 ≤ 2)).trans (by simpa using h1)
      rw [← div_eq_inv_mul, div_le_one hτ₁]; exact h2
    have hr_le : M_r * τ₁⁻¹ * t ^ 4 ≤ M_r * t ^ 2 := by
      rw [show M_r * τ₁⁻¹ * t ^ 4 = M_r * t ^ 2 * (τ₁⁻¹ * t ^ 2) by ring]
      exact mul_le_of_le_one_right (by positivity) ht_rat
    have htri : |v t| ≤ |c2| * t ^ 2 + |v t - c2 * t ^ 2| := by
      have := abs_add_le (c2 * t ^ 2) (v t - c2 * t ^ 2)
      rw [add_sub_cancel, abs_mul, abs_pow, abs_of_pos ht0] at this; exact this
    have hc := mul_le_mul_of_nonneg_right hc2_le (sq_nonneg t)
    linarith
  rcases (show p = 1 ∨ p = 2 by omega) with rfl | rfl
  · -- `p = 1`: `fq` is bounded on `(0, τ₁]` by `M_W * (e^{M_v}/2) * (c2_bd + M_r)^2`, so `A = 0`!
    have hpt1 : ∀ t ∈ Ioc (0 : ℝ) τ₁, ‖fq t‖ ≤ M_W * (Real.exp M_v / 2) * (c2_bd + M_r) ^ 2 := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have hvt_le : |v t| ≤ M_v := (hv_abs t).trans (mul_le_of_le_one_right hMv_nn (pow_le_one₀ hτ₁.le hτ₁_1))
      have hev : |Real.exp (v t) - 1 - v t| ≤ (Real.exp M_v / 2) * ((c2_bd + M_r) ^ 2 * t ^ 4) := by
        have h := abs_exp_sub_one_sub_le hvt_le
        have hv2 : v t ^ 2 ≤ (c2_bd + M_r) ^ 2 * t ^ 4 := by
          rw [← sq_abs]
          calc |v t| ^ 2 ≤ ((c2_bd + M_r) * t ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hv_t2 t ht) 2
            _ = (c2_bd + M_r) ^ 2 * t ^ 4 := by ring
        exact h.trans (mul_le_mul_of_nonneg_left hv2 (by positivity))
      dsimp only [fq]; rw [Real.norm_eq_abs, mul_div_right_comm, abs_mul,
        abs_of_nonneg (div_nonneg (mul_nonneg hαo_nn (norm_nonneg _)) (pow_nonneg (uctM_pos ht0).le 1))]
      have hW1 := hW_bd t ⟨ht0, by linarith [ht.2]⟩
      rw [show 2 * 1 + 2 = 4 by norm_num] at hW1
      calc uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ 1 * |Real.exp (v t) - 1 - v t|
          ≤ (M_W / t ^ 4) * ((Real.exp M_v / 2) * ((c2_bd + M_r) ^ 2 * t ^ 4)) :=
            mul_le_mul hW1 hev (abs_nonneg _) (by positivity)
        _ = M_W * (Real.exp M_v / 2) * (c2_bd + M_r) ^ 2 := by field_simp [ht0.ne']
    have hin_int : IntegrableOn fq (Ioc 0 τ₁) :=
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
        ((hfq_cont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
        (ae_restrict_of_forall_mem measurableSet_Ioc hpt1)
    have hall_int : IntegrableOn fq (Ioi 0) := by
      rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 10 * τ₁ by positivity), integrableOn_union,
        ← Ioc_union_Ioc_eq_Ioc hτ₁.le (by linarith), integrableOn_union]
      exact ⟨⟨hin_int, htail_bd.1⟩, (integrableOn_zero (μ := volume) (s := Ioi (10 * τ₁))).congr_fun
        (fun t ht => (hfq_zero_out t ht).symm) measurableSet_Ioi⟩
    refine ⟨0, ∫ t in Ioi (0 : ℝ), fq t, by simpa [fq] using FctPhiKill.tendsto_setIntegral_Ioi_zero hall_int, ?_⟩
    have hzero_out : (∫ t in Ioi (10 * τ₁), fq t) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero hfq_zero_out
    have hsplit : (∫ t in Ioi (0 : ℝ), fq t) = (∫ t in Ioc 0 τ₁, fq t) + ∫ t in Ioc τ₁ (10 * τ₁), fq t := by
      rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 10 * τ₁ by positivity),
        setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
          measurableSet_Ioi (hall_int.mono_set Ioc_subset_Ioi_self) (hall_int.mono_set fun x hx => lt_trans (by positivity) hx),
        hzero_out, add_zero,
        ← Ioc_union_Ioc_eq_Ioc hτ₁.le (by linarith),
        setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1])
          measurableSet_Ioc hin_int htail_bd.1]
    rw [hsplit, show (3 : ℤ) - 2 * ((1 : ℕ) : ℤ) = 1 by norm_num, zpow_one]
    have hin_bd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hpt1
    rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hτ₁.le] at hin_bd
    have htail1 : |∫ t in Ioc τ₁ (10 * τ₁), fq t| ≤ M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10 * τ₁ := by
      simpa [show (3 : ℤ) - 2 * ((1 : ℕ) : ℤ) = 1 by norm_num] using htail_bd.2
    refine (abs_add_le _ _).trans ?_
    have hle : M_W * (Real.exp M_v / 2) * (c2_bd + M_r) ^ 2 + M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10 ≤ C_tot := by
      dsimp only [C_tot]
      have h1 : 0 ≤ M_W * M_q := by positivity
      have h2 : 0 ≤ |aw2 0| * (c2_bd ^ 2 / 2) := by positivity
      have h3 : 0 ≤ Cw2 * (c2_bd ^ 2 / 2) := by positivity
      linarith
    calc |∫ t in Ioc 0 τ₁, fq t| + |∫ t in Ioc τ₁ (10 * τ₁), fq t|
        ≤ M_W * (Real.exp M_v / 2) * (c2_bd + M_r) ^ 2 * τ₁ +
          M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10 * τ₁ := add_le_add hin_bd htail1
      _ = (M_W * (Real.exp M_v / 2) * (c2_bd + M_r) ^ 2 + M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10) * τ₁ := by ring
      _ ≤ C_tot * τ₁ := mul_le_mul_of_nonneg_right hle hτ₁.le
  · -- `p = 2`: pull out `A := aw2 0 * (c2² / 2)` (`∫_ε^{τ₁} A / t² dt = A/ε - A/τ₁`), remainder `≤ (M_W * M_q + Cw2 * c2_bd²/2) * τ₁⁻¹`!
    set A : ℝ := aw2 0 * (c2 ^ 2 / 2)
    have hpt2 : ∀ t ∈ Ioc (0 : ℝ) τ₁, ‖fq t - A / t ^ 2‖ ≤ (M_W * M_q + Cw2 * (c2_bd ^ 2 / 2)) * τ₁⁻¹ := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have ht18 : t ≤ 1 / 8 := by linarith [ht.2, hτ₁_100]
      have hvt_le : |v t| ≤ M_v := (hv_abs t).trans (mul_le_of_le_one_right hMv_nn (pow_le_one₀ hτ₁.le hτ₁_1))
      -- Bound `|e^v - 1 - v - (c2²/2) t⁴| ≤ M_q * τ₁⁻¹ * t⁶`
      have hev_rem : |Real.exp (v t) - 1 - v t - c2 ^ 2 / 2 * t ^ 4| ≤ M_q * τ₁⁻¹ * t ^ 6 := by
        have hrew : Real.exp (v t) - 1 - v t - c2 ^ 2 / 2 * t ^ 4 =
            (Real.exp (v t) - 1 - v t - v t ^ 2 / 2) + (v t - c2 * t ^ 2) * (v t + c2 * t ^ 2) / 2 := by ring
        rw [hrew]
        have h1 : |Real.exp (v t) - 1 - v t - v t ^ 2 / 2| ≤ (Real.exp M_v / 6) * (c2_bd + M_r) ^ 3 * τ₁⁻¹ * t ^ 6 := by
          have h := abs_exp_sub_one_sub_sq_le hvt_le
          have h3 : |v t| ^ 3 ≤ (c2_bd + M_r) ^ 3 * t ^ 6 := by
            calc |v t| ^ 3 ≤ ((c2_bd + M_r) * t ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hv_t2 t ht) 3
              _ = (c2_bd + M_r) ^ 3 * t ^ 6 := by ring
          have h1_inv : (1 : ℝ) ≤ τ₁⁻¹ := (one_le_inv₀ hτ₁).mpr hτ₁_1
          calc _ ≤ (Real.exp M_v / 6) * ((c2_bd + M_r) ^ 3 * t ^ 6) := h.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
            _ = (Real.exp M_v / 6) * (c2_bd + M_r) ^ 3 * 1 * t ^ 6 := by ring
            _ ≤ (Real.exp M_v / 6) * (c2_bd + M_r) ^ 3 * τ₁⁻¹ * t ^ 6 := by gcongr
        have h2 : |(v t - c2 * t ^ 2) * (v t + c2 * t ^ 2) / 2| ≤ (c2_bd * M_r + M_r ^ 2 / 2) * τ₁⁻¹ * t ^ 6 := by
          rw [abs_div, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
          have hsum : |v t + c2 * t ^ 2| ≤ (2 * c2_bd + M_r) * t ^ 2 := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_pow, abs_of_pos ht0]
            have := hv_t2 t ht
            have := mul_le_mul_of_nonneg_right hc2_le (sq_nonneg t)
            linarith
          calc |v t - c2 * t ^ 2| * |v t + c2 * t ^ 2| / 2
              ≤ (M_r * τ₁⁻¹ * t ^ 4) * ((2 * c2_bd + M_r) * t ^ 2) / 2 :=
                div_le_div_of_nonneg_right (mul_le_mul (hv_in_split t ht) hsum (abs_nonneg _) (by positivity)) (by norm_num)
            _ = (c2_bd * M_r + M_r ^ 2 / 2) * τ₁⁻¹ * t ^ 6 := by ring
        refine (abs_add_le _ _).trans ?_
        dsimp only [M_q]; linarith
      have hW_rem : |uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ 2 * (c2 ^ 2 / 2 * t ^ 4) - A / t ^ 2| ≤
          Cw2 * (c2_bd ^ 2 / 2) := by
        have hmQ_pos : 0 < mQ t := mQ_pos_of_mem (by rw [abs_of_pos ht0]; linarith)
        have hrew : uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ 2 * (c2 ^ 2 / 2 * t ^ 4) - A / t ^ 2 =
            ((uctAlphaOsc * hFac t / mQ t ^ 2 - aw2 0) / t ^ 2) * (c2 ^ 2 / 2) := by
          rw [hhFac_eq t ht0, uctM_eq_sq_mul_mQ ht0, mul_pow]; dsimp only [A]
          field_simp [ht0.ne', hmQ_pos.ne']
        rw [hrew, abs_mul, abs_div, abs_pow, abs_of_pos ht0, abs_of_nonneg (by positivity : 0 ≤ c2 ^ 2 / 2)]
        have hw := hw2_bd t ⟨ht0.le, ht18⟩
        rw [Fin.sum_univ_one] at hw; simp only [Fin.val_zero, mul_zero, pow_zero, mul_one] at hw
        have hw' : |uctAlphaOsc * hFac t / mQ t ^ 2 - aw2 0| / t ^ 2 ≤ Cw2 := by
          rw [div_le_iff₀ (sq_pos_of_pos ht0)]; exact hw
        have hc2_sq : c2 ^ 2 / 2 ≤ c2_bd ^ 2 / 2 :=
          div_le_div_of_nonneg_right (by rw [← sq_abs c2]; exact pow_le_pow_left₀ (abs_nonneg _) hc2_le 2) (by norm_num)
        exact mul_le_mul hw' hc2_sq (by positivity) hCw2_nn
      have hsplit : fq t - A / t ^ 2 =
          uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ 2 * (Real.exp (v t) - 1 - v t - c2 ^ 2 / 2 * t ^ 4) +
          (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ 2 * (c2 ^ 2 / 2 * t ^ 4) - A / t ^ 2) := by
        dsimp only [fq]; ring
      rw [Real.norm_eq_abs, hsplit]
      have hW2 := hW_bd t ⟨ht0, by linarith [ht.2]⟩
      rw [show 2 * 2 + 2 = 6 by norm_num] at hW2
      have hpart1 : |uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ 2 * (Real.exp (v t) - 1 - v t - c2 ^ 2 / 2 * t ^ 4)| ≤
          M_W * M_q * τ₁⁻¹ := by
        rw [abs_mul, abs_of_nonneg (div_nonneg (mul_nonneg hαo_nn (norm_nonneg _)) (pow_nonneg (uctM_pos ht0).le 2))]
        calc _ ≤ (M_W / t ^ 6) * (M_q * τ₁⁻¹ * t ^ 6) := mul_le_mul hW2 hev_rem (abs_nonneg _) (by positivity)
          _ = M_W * M_q * τ₁⁻¹ := by field_simp [ht0.ne']
      have h1_inv : (1 : ℝ) ≤ τ₁⁻¹ := (one_le_inv₀ hτ₁).mpr hτ₁_1
      have hpart2 : Cw2 * (c2_bd ^ 2 / 2) ≤ Cw2 * (c2_bd ^ 2 / 2) * τ₁⁻¹ :=
        le_mul_of_one_le_right (by positivity) h1_inv
      refine (abs_add_le _ _).trans ?_; linarith
    have hin_rem_int : IntegrableOn (fun t : ℝ => fq t - A / t ^ 2) (Ioc 0 τ₁) :=
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
        (((hfq_cont.sub (continuousOn_const.div (continuousOn_id.pow 2) fun t ht => pow_ne_zero 2 (mem_Ioi.mp ht).ne')).mono
          Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
        (ae_restrict_of_forall_mem measurableSet_Ioc hpt2)
    refine ⟨A, (∫ t in Ioc (0 : ℝ) τ₁, (fq t - A / t ^ 2)) - A / τ₁ + ∫ t in Ioc τ₁ (10 * τ₁), fq t, ?_, ?_⟩
    · -- Limit as `ε ↓ 0`
      have heq_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          (∫ t in Ioi ε, fq t) - A / ε =
          (∫ t in Ioc ε τ₁, (fq t - A / t ^ 2)) - A / τ₁ + ∫ t in Ioc τ₁ (10 * τ₁), fq t := by
        filter_upwards [Ioo_mem_nhdsGT hτ₁] with ε hε
        have hε0 : 0 < ε := hε.1
        have hfq_ε : IntegrableOn fq (Ioc ε τ₁) :=
          ((hfq_cont.mono fun t (ht : t ∈ Icc ε τ₁) => lt_of_lt_of_le hε0 ht.1).integrableOn_Icc).mono_set Ioc_subset_Icc_self
        have hA_int : IntegrableOn (fun t : ℝ => A / t ^ 2) (Ioc ε τ₁) :=
          (((continuousOn_const.div (continuousOn_id.pow 2) fun t (ht : t ∈ Icc ε τ₁) => pow_ne_zero 2 (lt_of_lt_of_le hε0 ht.1).ne')).integrableOn_Icc).mono_set Ioc_subset_Icc_self
        have hA_val : (∫ t in Ioc ε τ₁, A / t ^ 2) = A / ε - A / τ₁ := by
          rw [← intervalIntegral.integral_of_le hε.2.le]
          have hd : ∀ t ∈ uIcc ε τ₁, HasDerivAt (fun s => -(A / s)) (A / t ^ 2) t := fun t ht => by
            rw [uIcc_of_le hε.2.le] at ht
            have ht0 : t ≠ 0 := (lt_of_lt_of_le hε0 ht.1).ne'
            have := ((hasDerivAt_inv ht0).const_mul A).neg
            refine this.congr_deriv ?_; field_simp [ht0]
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((intervalIntegrable_iff_integrableOn_Ioc_of_le hε.2.le).mpr hA_int)]
          ring
        have hsplit : (∫ t in Ioi ε, fq t) = (∫ t in Ioc ε τ₁, fq t) + ∫ t in Ioc τ₁ (10 * τ₁), fq t := by
          have hout : IntegrableOn fq (Ioi (10 * τ₁)) :=
            (integrableOn_zero (μ := volume) (s := Ioi (10 * τ₁))).congr_fun
              (fun t ht => (hfq_zero_out t ht).symm) measurableSet_Ioi
          have hzero_out : (∫ t in Ioi (10 * τ₁), fq t) = 0 :=
            setIntegral_eq_zero_of_forall_eq_zero hfq_zero_out
          rw [← Ioc_union_Ioi_eq_Ioi (show ε ≤ 10 * τ₁ by linarith [hε.2]),
            setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
              measurableSet_Ioi (by
                rw [← Ioc_union_Ioc_eq_Ioc hε.2.le (by linarith), integrableOn_union]; exact ⟨hfq_ε, htail_bd.1⟩) hout,
            hzero_out, add_zero,
            ← Ioc_union_Ioc_eq_Ioc hε.2.le (by linarith),
            setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1])
              measurableSet_Ioc hfq_ε htail_bd.1]
        have hsub := integral_sub hfq_ε hA_int
        rw [hsplit]; linarith
      have hlim : Tendsto (fun ε : ℝ => ∫ t in Ioc ε τ₁, (fq t - A / t ^ 2)) (𝓝[>] (0 : ℝ))
          (𝓝 (∫ t in Ioc (0 : ℝ) τ₁, (fq t - A / t ^ 2))) := by
        have hinter0 : Ioi (0 : ℝ) ∩ Ioc (0 : ℝ) τ₁ = Ioc (0 : ℝ) τ₁ := by
          ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
          exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
        have hind_int : IntegrableOn ((Ioc (0 : ℝ) τ₁).indicator (fun t => fq t - A / t ^ 2)) (Ioi (0 : ℝ)) volume := by
          rw [integrableOn_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) τ₁)).nullMeasurableSet]
          exact hin_rem_int.mono_set inter_subset_left
        have h := FctPhiKill.tendsto_setIntegral_Ioi_zero hind_int
        rw [setIntegral_indicator measurableSet_Ioc, hinter0] at h
        refine h.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hτ₁] with ε hε
        rw [setIntegral_indicator measurableSet_Ioc]
        have : Ioi ε ∩ Ioc (0 : ℝ) τ₁ = Ioc ε τ₁ := by
          ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
          exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, hε.1.trans h1, h2⟩⟩
        rw [this]
      exact ((hlim.sub tendsto_const_nhds).add tendsto_const_nhds).congr' (heq_ev.mono fun _ h => h.symm)
    · -- Bound `|Lq| ≤ C_tot * τ₁⁻¹`!
      rw [show (3 : ℤ) - 2 * ((2 : ℕ) : ℤ) = -1 by norm_num, zpow_neg_one]
      have hin_bd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hpt2
      rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hτ₁.le,
        mul_assoc, inv_mul_cancel₀ hτ₁.ne', mul_one] at hin_bd
      have h1_inv : (1 : ℝ) ≤ τ₁⁻¹ := (one_le_inv₀ hτ₁).mpr hτ₁_1
      have hin_bd' : |∫ t in Ioc (0 : ℝ) τ₁, (fq t - A / t ^ 2)| ≤ (M_W * M_q + Cw2 * (c2_bd ^ 2 / 2)) * τ₁⁻¹ :=
        hin_bd.trans (le_mul_of_one_le_right (by positivity) h1_inv)
      have hA_bd : |A / τ₁| ≤ |aw2 0| * (c2_bd ^ 2 / 2) * τ₁⁻¹ := by
        rw [abs_div, abs_of_pos hτ₁, div_eq_mul_inv]
        dsimp only [A]; rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ c2 ^ 2 / 2)]
        have hc2_sq : c2 ^ 2 / 2 ≤ c2_bd ^ 2 / 2 :=
          div_le_div_of_nonneg_right (by rw [← sq_abs c2]; exact pow_le_pow_left₀ (abs_nonneg _) hc2_le 2) (by norm_num)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2_sq (abs_nonneg _)) (inv_nonneg.mpr hτ₁.le)
      have htail2 : |∫ t in Ioc τ₁ (10 * τ₁), fq t| ≤ M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10 * τ₁⁻¹ := by
        simpa [show (3 : ℤ) - 2 * 2 = -1 by norm_num, zpow_neg_one] using htail_bd.2
      refine ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans ?_
      have hle : M_W * M_q + Cw2 * (c2_bd ^ 2 / 2) + |aw2 0| * (c2_bd ^ 2 / 2) +
          M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10 ≤ C_tot := by
        dsimp only [C_tot]
        have : 0 ≤ M_W * (Real.exp M_v / 2) * (c2_bd + M_r) ^ 2 := by positivity
        linarith
      calc _ ≤ (M_W * M_q + Cw2 * (c2_bd ^ 2 / 2) + |aw2 0| * (c2_bd ^ 2 / 2) +
            M_W * (Real.exp M_v / 2) * M_v ^ 2 * 10) * τ₁⁻¹ := by linarith
        _ ≤ C_tot * τ₁⁻¹ := mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hτ₁.le)

/-! ### Headline Theorem: Part (2) of `fct:comp-D` -/

/-- **Lemma `fct:comp-D` (Part 2): Global mass, cosine penalty, inner integral, and `(fct:bump-1L)`–`(fct:bump-2L)`**
(`constant_terms_five.tex`, lines 199–217 and 251–294).

For `H_0 ∈ {H_*, H_CE}` (selected by `kind : StripKernelChoice`), there exists a universal threshold
`τ₀ > 0` such that for every `K₄ > 0` there is `C = C(K₄) ≥ 0` such that for all `c > 0`, `0 < τ₁ ≤ τ₀`
with `τ₁⁴ = c⁻¹` and `|α| ≤ τ₁²`, setting `v := vTotal kind K4 c α τ₁`, `v₀ := v0 kind K4 τ₁`,
`δ_L := uctM τ₁`, and `D_*(L) := stripDstar kind c v v₀ L`:
1. **`(fct:cos-pen)`:**
   - `|∫_0^∞ (I_osc^{DH_0}(L) - I_fl(L)) dL - C_fl(H_0)| ≤ C τ₁³` (and for `H_*`, this integral
     equals the exact nonnegative cosine penalty `α_osc ∫_0^∞ |H_*(it)| e^{v(t)} (1 - cos ϑ_D(t)) dt`);
   - `|∫_0^∞ D_*(L) dL - C_fl(H_0)| ≤ C τ₁³`.
2. **`(fct:curv-p-int)`:** for `p ∈ {0, 1, 2}`,
   `|∫_0^∞ I_osc^{H_0}(L) Δ_curv(τ₀(L)) / L^p dL| ≤ C c⁻¹`.
3. **Inner integral:**
   `|∫_0^{3δ_L} D_*(L) dL| ≤ C (τ₁³ + |α| τ₁)`.
4. **`(fct:bump-1L)`:**
   `|∫_{3δ_L}^∞ D_*(L) / L dL - stripFp1 kind| ≤ C (τ₁ + |α| τ₁⁻¹)`,
   where `stripFp1 kind = lim_{ε↓0} [∫_ε^∞ (α_osc |H_0(it)| - α_fl m'(t)/m(t)^{3/2}) / m(t) dt - c_{-1}(H_0)/ε]`.
5. **`(fct:bump-2L)`:**
   `|∫_{3δ_L}^∞ D_*(L) / L² dL| ≤ C (τ₁⁻¹ + |α| τ₁⁻³)`. -/
theorem fct_comp_D_part2 (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 100 ∧
    ∀ K4 : ℝ, 1 ≤ K4 →
      ∃ C ≥ 0, ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
        τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
        let v := vTotal kind K4 c α τ₁
        let v0' := v0 kind K4 τ₁
        let δ_L := uctM τ₁
        -- 1. `(fct:cos-pen)` + exact nonnegative cosine identity for `H_*`
        IntegrableOn (fun L : ℝ => stripIoscD kind v L - uctIfl L) (Ioi 0) ∧
        |(∫ L in Ioi (0 : ℝ), (stripIoscD kind v L - uctIfl L)) - stripCfl kind| ≤ C * τ₁ ^ 3 ∧
        (kind = .star →
          0 ≤ ∫ L in Ioi (0 : ℝ), (stripIoscD .star v L - uctIfl L) ∧
          (∫ L in Ioi (0 : ℝ), (stripIoscD .star v L - uctIfl L)) =
            uctAlphaOsc * ∫ t in Ioi (0 : ℝ), ‖stripH0 .star ((t : ℂ) * Complex.I)‖ *
              Real.exp (v t) * (1 - Real.cos (fctThetaD v t))) ∧
        IntegrableOn (stripDstar kind c v v0') (Ioi 0) ∧
        |(∫ L in Ioi (0 : ℝ), stripDstar kind c v v0' L) - stripCfl kind| ≤ C * τ₁ ^ 3 ∧
        -- 2. `(fct:curv-p-int)` for `p ∈ {0, 1, 2}`
        (∀ p : ℕ, p ≤ 2 →
          IntegrableOn (fun L : ℝ => stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (FormalResearch.CohnElkies.tau0 L) / L ^ p) (Ioi 0) ∧
          |∫ L in Ioi (0 : ℝ), stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (FormalResearch.CohnElkies.tau0 L) / L ^ p| ≤ C * c⁻¹) ∧
        -- 3. Inner integral `∫_0^{3δ_L} D_*(L) dL = O_{K₄}(τ₁³ + |α| τ₁)`
        IntegrableOn (stripDstar kind c v v0') (Ioc 0 (3 * δ_L)) ∧
        |∫ L in Ioc 0 (3 * δ_L), stripDstar kind c v v0' L| ≤ C * (τ₁ ^ 3 + |α| * τ₁) ∧
        -- 4. `(fct:bump-1L)` (`p = 1`) and convergence of the defining finite-part limit `stripFp1 kind`
        Tendsto (fun ε : ℝ =>
          (∫ t in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
            uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t) - stripCneg1 kind / ε)
          (𝓝[>] (0 : ℝ)) (𝓝 (stripFp1 kind)) ∧
        IntegrableOn (fun L : ℝ => stripDstar kind c v v0' L / L) (Ioi (3 * δ_L)) ∧
        |(∫ L in Ioi (3 * δ_L), stripDstar kind c v v0' L / L) - stripFp1 kind| ≤ C * (τ₁ + |α| * τ₁⁻¹) ∧
        -- 5. `(fct:bump-2L)` (`p = 2`)
        IntegrableOn (fun L : ℝ => stripDstar kind c v v0' L / L ^ 2) (Ioi (3 * δ_L)) ∧
        |∫ L in Ioi (3 * δ_L), stripDstar kind c v v0' L / L ^ 2| ≤ C * (τ₁ ^ (-1 : ℤ) + |α| * τ₁ ^ (-3 : ℤ)) := by
  obtain ⟨τ₀_p1, hτ₀_p1_pos, _, _, _, _, _, _, _, _, _, _, _,
    CL1_0b, CL1_0m, CL1_a, CL1_1b, CL1_1m, _, _, _, _, hCL1_nn, _, hpart1⟩ := fct_comp_D_part1 kind
  obtain ⟨τ₀_cos, hτ₀_cos_pos, _, hcos_pen⟩ := fct_comp_D_cos_penalty kind
  obtain ⟨τ₀_curv, hτ₀_curv_pos, _, hcurv_p⟩ := fct_comp_D_curv_p_int kind
  obtain ⟨τ₀_in, hτ₀_in_pos, _, hinner_D⟩ := inner_Dstar_bounds kind
  obtain ⟨τ₀_q, hτ₀_q_pos, _, hquad_p⟩ := fp_exp_quad_bound kind
  obtain ⟨C_lin, hClin_nn, hlin_p⟩ := fp_linear_v_bound kind
  obtain ⟨hbg_int, hbg_fp1, A_bg2, B_bg2, C_bg2, L_bg2, hbg_fp2⟩ := bg_fp_asymptotic kind
  have hαo_nn : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
  refine ⟨min (min (min τ₀_p1 τ₀_cos) (min τ₀_curv τ₀_in)) (min τ₀_q (1 / 100)),
    lt_min (lt_min (lt_min hτ₀_p1_pos hτ₀_cos_pos) (lt_min hτ₀_curv_pos hτ₀_in_pos)) (lt_min hτ₀_q_pos (by norm_num)),
    (min_le_right _ _).trans (min_le_right _ _), fun K4 hK4 => ?_⟩
  obtain ⟨C_cos, hCcos_nn, hcos_spec⟩ := hcos_pen K4 hK4
  obtain ⟨C_curv, hCcurv_nn, hcurv_spec⟩ := hcurv_p K4 hK4
  obtain ⟨C_in, hCin_nn, hin_spec⟩ := hinner_D K4 hK4
  obtain ⟨C_q, hCq_nn, hq_spec⟩ := hquad_p K4 hK4
  have hK4_nn : 0 ≤ K4 := by linarith
  set M_L1 : ℝ := (CL1_0b + K4 * CL1_0m) + (CL1_1b + K4 * CL1_1m) + CL1_a
  have hML1_nn : 0 ≤ M_L1 := by rcases hCL1_nn with ⟨h1, h2, h3, h4, h5⟩; positivity
  set C_all : ℝ := max (max C_cos C_curv) (max C_in (C_lin * M_L1 + C_curv + uctAlphaOsc * C_curv + C_q + C_in + |L_bg2|))
  have hCall_nn : 0 ≤ C_all := le_trans (le_trans hCcos_nn (le_max_left _ _)) (le_max_left _ _)
  refine ⟨C_all, hCall_nn, fun {c α τ₁} hc hτ₁ hτ₁_le hc_eq hα_le => ?_⟩
  have hτ₁_p1 : τ₁ ≤ τ₀_p1 := hτ₁_le.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hτ₁_cos : τ₁ ≤ τ₀_cos := hτ₁_le.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hτ₁_curv : τ₁ ≤ τ₀_curv := hτ₁_le.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hτ₁_in : τ₁ ≤ τ₀_in := hτ₁_le.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hτ₁_q : τ₁ ≤ τ₀_q := hτ₁_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ₁_100 : τ₁ ≤ 1 / 100 := hτ₁_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have hc_inv : c⁻¹ = τ₁ ^ 4 := by
    rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
  have hα1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
  obtain ⟨⟨hb0_cd, hm0_cd, ha0_cd, hb1_cd, hm1_cd, hv_cd⟩, ⟨_, _, _, _, _, hv_ev⟩, ⟨_, _, _, _, _, hv0⟩,
    ⟨hb0_s, hm0_s, ha0_s, hb1_s, hm1_s, hv_s, _⟩, hmom, _, _, ⟨hL1_0b, hL1_0m, hL1_a, hL1_1b, hL1_1m⟩, _, _, _, _, _⟩ :=
    hpart1 hK4 hc hτ₁ hτ₁_p1 hc_eq hα_le
  obtain ⟨hcos_int, _, hcos_bd, hcos_star⟩ := hcos_spec hc hτ₁ hτ₁_cos hc_eq hα_le
  obtain ⟨hcurv_all, hDstar_int, hDstar_bd⟩ := hcurv_spec hc hτ₁ hτ₁_curv hc_eq hα_le
  obtain ⟨hIn0_int, hIn0_bd, hIn_p⟩ := hin_spec hc hτ₁ hτ₁_in hc_eq hα_le
  let v := vTotal kind K4 c α τ₁
  let v0' := v0 kind K4 τ₁
  let δ_L := uctM τ₁
  let t₃ := FormalResearch.CohnElkies.tau0 (3 * δ_L)
  have ht3_bd := saddleTau0_three_uctM_bounds hτ₁ (by linarith)
  have ht3_pos : 0 < t₃ := hτ₁.trans ht3_bd.1
  -- `∫ |v| ≤ M_L1 * τ₁³`
  have hv_L1 : (∫ t : ℝ, |v t|) ≤ M_L1 * τ₁ ^ 3 := by
    have hi0b : Integrable (fun t => |v0Base kind τ₁ t|) := hb0_cd.continuous.abs.integrable_of_hasCompactSupport ((hasCompactSupport_of_support_Ioo hb0_s).comp_left abs_zero)
    have hi0m : Integrable (fun t => |v0Marg τ₁ t|) := hm0_cd.continuous.abs.integrable_of_hasCompactSupport ((hasCompactSupport_of_support_Ioo hm0_s).comp_left abs_zero)
    have hi1b : Integrable (fun t => |v1Base kind c τ₁ t|) := hb1_cd.continuous.abs.integrable_of_hasCompactSupport ((hasCompactSupport_of_support_Ioo hb1_s).comp_left abs_zero)
    have hi1m : Integrable (fun t => |v1Marg c τ₁ t|) := hm1_cd.continuous.abs.integrable_of_hasCompactSupport ((hasCompactSupport_of_support_Ioo hm1_s).comp_left abs_zero)
    have hia : Integrable (fun t => |vAlpha α τ₁ t|) := ha0_cd.continuous.abs.integrable_of_hasCompactSupport ((hasCompactSupport_of_support_Ioo ha0_s).comp_left abs_zero)
    have hdom := (((hi0b.add (hi0m.const_mul K4)).add (hi1b.add (hi1m.const_mul K4))).add hia)
    have hm : (∫ t : ℝ, |v t|) ≤ ∫ t : ℝ, ((|v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t|) +
        (|v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t|) + |vAlpha α τ₁ t|) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hdom
        (Filter.Eventually.of_forall fun t => by
          dsimp only [v]; unfold vTotal v0 v1
          have a1 := abs_add_le ((v0Base kind τ₁ t + K4 * v0Marg τ₁ t) + (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)) (vAlpha α τ₁ t)
          have a2 := abs_add_le (v0Base kind τ₁ t + K4 * v0Marg τ₁ t) (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)
          have a3 := abs_add_le (v0Base kind τ₁ t) (K4 * v0Marg τ₁ t)
          have a4 := abs_add_le (v1Base kind c τ₁ t) (K4 * v1Marg c τ₁ t)
          rw [abs_mul, abs_of_nonneg hK4_nn] at a3 a4; linarith)
    have hi0m_k : Integrable (fun t : ℝ => K4 * |v0Marg τ₁ t|) := hi0m.const_mul K4
    have hi1m_k : Integrable (fun t : ℝ => K4 * |v1Marg c τ₁ t|) := hi1m.const_mul K4
    have hi0_all : Integrable (fun t : ℝ => |v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t|) := hi0b.add hi0m_k
    have hi1_all : Integrable (fun t : ℝ => |v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t|) := hi1b.add hi1m_k
    have hi01 : Integrable (fun t : ℝ => (|v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t|) +
        (|v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t|)) := hi0_all.add hi1_all
    rw [integral_add hi01 hia, integral_add hi0_all hi1_all,
      integral_add hi0b hi0m_k, integral_add hi1b hi1m_k,
      integral_const_mul, integral_const_mul] at hm
    have hτ5 : τ₁ ^ 5 ≤ τ₁ ^ 3 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have hc3 : c⁻¹ ≤ τ₁ ^ 3 := by rw [hc_inv]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have hc2 : c⁻¹ * τ₁ ^ 2 ≤ τ₁ ^ 3 := by
      rw [hc_inv, ← pow_add]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have b0m : K4 * (∫ t : ℝ, |v0Marg τ₁ t|) ≤ K4 * (CL1_0m * τ₁ ^ 3) :=
      mul_le_mul_of_nonneg_left (hL1_0m.trans (mul_le_mul_of_nonneg_left hτ5 hCL1_nn.2.1)) hK4_nn
    have b1b : (∫ t : ℝ, |v1Base kind c τ₁ t|) ≤ CL1_1b * τ₁ ^ 3 :=
      hL1_1b.trans (mul_le_mul_of_nonneg_left hc3 hCL1_nn.2.2.2.1)
    have b1m : K4 * (∫ t : ℝ, |v1Marg c τ₁ t|) ≤ K4 * (CL1_1m * τ₁ ^ 3) :=
      mul_le_mul_of_nonneg_left (hL1_1m.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hc2 hCL1_nn.2.2.2.2)) hK4_nn
    have ba : (∫ t : ℝ, |vAlpha α τ₁ t|) ≤ CL1_a * τ₁ ^ 3 :=
      hL1_a.trans (by
        have := mul_le_mul_of_nonneg_left hα1 hCL1_nn.2.2.1; rw [mul_one] at this
        exact mul_le_mul_of_nonneg_right this (pow_nonneg hτ₁.le 3))
    calc (∫ t : ℝ, |v t|) ≤ CL1_0b * τ₁ ^ 3 + K4 * (CL1_0m * τ₁ ^ 3) +
            (CL1_1b * τ₁ ^ 3 + K4 * (CL1_1m * τ₁ ^ 3)) + CL1_a * τ₁ ^ 3 := by linarith
      _ = M_L1 * τ₁ ^ 3 := by dsimp only [M_L1]; ring
  -- Unified proof of `(fct:bump-1L)` (`p = 1`) and `(fct:bump-2L)` (`p = 2`) via `tendsto_odd_pole_zero`!
  have hbump_p : ∀ p : ℕ, 1 ≤ p → p ≤ 2 →
      IntegrableOn (fun L : ℝ => stripDstar kind c v v0' L / L ^ p) (Ioi (3 * δ_L)) ∧
      |(∫ L in Ioi (3 * δ_L), stripDstar kind c v v0' L / L ^ p) - (if p = 1 then stripFp1 kind else L_bg2)| ≤
        (C_lin * M_L1 + C_curv + uctAlphaOsc * C_curv + C_q + C_in) *
          (τ₁ ^ (3 - 2 * (p : ℤ)) + |α| * τ₁ ^ (1 - 2 * (p : ℤ))) := by
    intro p hp1 hp2
    have hδ_pos : 0 < 3 * δ_L := mul_pos (by norm_num) (uctM_pos hτ₁)
    -- Integrability on `Ioi (3 * δ_L)`: since `D_*` is integrable on `Ioi 0` and `1/L^p ≤ 1/(3δ_L)^p` on `Ioi (3δ_L)`!
    have hD_p_int : IntegrableOn (fun L : ℝ => stripDstar kind c v v0' L / L ^ p) (Ioi (3 * δ_L)) := by
      refine ((hDstar_int.mono_set fun L hL => hδ_pos.trans hL).norm.const_mul (1 / (3 * δ_L) ^ p)).mono' ?_ ?_
      · have hmul := ((hDstar_int.mono_set fun L hL => hδ_pos.trans hL).aestronglyMeasurable).mul
          (((continuousOn_const (c := (1 : ℝ))).div (continuousOn_id.pow p) fun L (hL : L ∈ Ioi (3 * δ_L)) =>
            pow_ne_zero p (hδ_pos.trans hL).ne').aestronglyMeasurable measurableSet_Ioi)
        exact hmul.congr (Filter.Eventually.of_forall fun L => by
          simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq, mul_one_div]; rfl)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
        have hL0 : 0 < L := hδ_pos.trans hL
        rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hL0, div_eq_inv_mul, one_div]
        exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (pow_pos hL0 p) (pow_pos hδ_pos p)).mpr
          (pow_le_pow_left₀ hδ_pos.le (le_of_lt hL) p)) (abs_nonneg _)
    refine ⟨hD_p_int, ?_⟩
    -- Change variables `L = uctM t` on `Ioi (3 * δ_L) = uctM '' Ioi t₃`!
    have hsubst : (∫ L in Ioi (3 * δ_L), stripDstar kind c v v0' L / L ^ p) =
        ∫ t in Ioi t₃, stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p := by
      have h := uct_subst ht3_pos (fun L => stripDstar kind c v v0' L / L ^ p)
      rw [show uctM t₃ = 3 * δ_L from ceEll_tau0 hδ_pos] at h
      rw [h]; refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    -- Obtain the 5 finite-part pieces for `p ∈ {1, 2}`:
    -- (a) Background `I_bg`:
    obtain ⟨A1, B1, C1, L1, h1⟩ : ∃ A1 B1 C1 L1 : ℝ, L1 = (if p = 1 then stripFp1 kind else L_bg2) ∧
        Tendsto (fun ε : ℝ => (∫ t in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
          uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p) - (A1 / ε ^ 5 + B1 / ε ^ 3 + C1 / ε))
          (𝓝[>] (0 : ℝ)) (𝓝 L1) := by
      interval_cases p
      · exact ⟨0, 0, stripCneg1 kind, stripFp1 kind, rfl, by simpa using hbg_fp1⟩
      · exact ⟨A_bg2, B_bg2, C_bg2, L_bg2, rfl, hbg_fp2⟩
    obtain ⟨hL1_eq, h1⟩ := h1
    -- (b) Linear `v` term:
    obtain ⟨A_v, B_v, L_v, h_lin, hLv_bd⟩ := hlin_p hτ₁ (by linarith) hv_cd hv_ev hv0
      (by simpa only [neg_mul] using hv_s) (fun k hk => (hmom k (by omega)).2.2.2.1) p hp1 hp2
    -- (c) Quadratic `e^v - 1 - v` term:
    obtain ⟨A_q, L_q, h_q, hLq_bd⟩ := hq_spec hc hτ₁ hτ₁_q hc_eq hα_le p hp1 hp2
    -- (d) Curvature + cross terms (ordinary convergent integrals on `Ioi 0`!):
    obtain ⟨hcurv_int, hcurv_bd, hcross_int, hcross_bd⟩ := hcurv_all p hp2
    have hcurv_t_int : IntegrableOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
        stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) (Ioi 0) := by
      have ht := (uct_subst_integrableOn_zero _).mp hcurv_int
      refine ht.congr_fun (fun t ht => ?_) measurableSet_Ioi
      dsimp only
      rw [show uctM t = ceEll (π * t / 2) from rfl, tau0_ceEll ht, show ceEll (π * t / 2) = uctM t from rfl,
        mul_div_assoc', ← mul_assoc (uctMderiv t), uctMderiv_mul_stripIosc kind ht]
    have hcurv_t_eq : (∫ t in Ioi (0 : ℝ), uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
        stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) =
        ∫ L in Ioi (0 : ℝ), stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L) / L ^ p := by
      symm; rw [uct_subst_zero]; refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [show uctM t = ceEll (π * t / 2) from rfl, tau0_ceEll ht, show ceEll (π * t / 2) = uctM t from rfl,
        mul_div_assoc', ← mul_assoc (uctMderiv t), uctMderiv_mul_stripIosc kind ht]
    have hcross_t_int : IntegrableOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
        (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) (Ioi 0) := by
      rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 10 * τ₁ by positivity), integrableOn_union]
      refine ⟨(hcross_int.const_mul uctAlphaOsc).mono' ?_ ?_,
        (integrableOn_zero (μ := volume) (s := Ioi (10 * τ₁))).congr_fun (fun t ht => by
          have hvt : v t = 0 := by by_contra hne; linarith [(hv_s hne).2, show 10 * τ₁ < t from ht]
          rw [hvt, Real.exp_zero, sub_self, mul_zero, zero_mul, zero_div]) measurableSet_Ioi⟩
      · -- Measurability on `Ioc 0 (10 * τ₁)` via `hcurv_t_int` and continuity of `e^v - 1`
        have h1 : AEStronglyMeasurable (fun t : ℝ =>
            (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) *
            (Real.exp (v t) - 1)) (volume.restrict (Ioc 0 (10 * τ₁))) :=
          ((hcurv_t_int.mono_set Ioc_subset_Ioi_self).aestronglyMeasurable).mul
            (((Real.continuous_exp.comp hv_cd.continuous).sub continuous_const).aestronglyMeasurable)
        exact h1.congr (Filter.Eventually.of_forall fun t => by ring)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hαo_nn,
          abs_of_nonneg (norm_nonneg _), abs_of_pos (pow_pos (uctM_pos ht.1) p)]
        exact le_of_eq (by ring)
    have hcross_t_bd : |∫ t in Ioi (0 : ℝ), uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
        (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p| ≤
        uctAlphaOsc * C_curv * c⁻¹ * τ₁ ^ (-(2 * (p : ℤ))) := by
      have hzero : (∫ t in Ioi (10 * τ₁), uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
          (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
          have hvt : v t = 0 := by by_contra hne; linarith [(hv_s hne).2, show 10 * τ₁ < t from ht]
          rw [hvt, Real.exp_zero, sub_self, mul_zero, zero_mul, zero_div]
      rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 10 * τ₁ by positivity),
        setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
          measurableSet_Ioi (hcross_t_int.mono_set Ioc_subset_Ioi_self) (hcross_t_int.mono_set fun x hx => lt_trans (by positivity) hx),
        hzero, add_zero]
      have h1 : |∫ t in Ioc 0 (10 * τ₁), uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
          (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p| ≤
          ∫ t in Ioc 0 (10 * τ₁), uctAlphaOsc * (‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p *
            |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|) := by
        refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on (hcross_t_int.mono_set Ioc_subset_Ioi_self).norm
          (hcross_int.const_mul uctAlphaOsc) measurableSet_Ioc fun t ht => ?_)
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hαo_nn,
          abs_of_nonneg (norm_nonneg _), abs_of_pos (pow_pos (uctM_pos ht.1) p)]
        exact le_of_eq (by ring)
      rw [integral_const_mul] at h1
      exact h1.trans (by
        rw [mul_assoc uctAlphaOsc, mul_assoc uctAlphaOsc]
        exact (mul_le_mul_of_nonneg_left hcross_bd hαo_nn).trans (le_of_eq (by ring)))
    -- (e) Inner piece on `(ε, t₃]`:
    obtain ⟨A_in, B_in, L_in, h_in, hLin_bd⟩ := hIn_p p hp1 hp2
    -- Combine all 5 pieces for `0 < ε < t₃` and apply `tendsto_odd_pole_zero`!
    set L_curv := ∫ t in Ioi (0 : ℝ), uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
      stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p
    set L_cross := ∫ t in Ioi (0 : ℝ), uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
      (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p
    set I_tail := ∫ t in Ioi t₃, stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p
    have hcomb_eq : I_tail = L1 + L_v + L_q + L_curv + L_cross - L_in := by
      -- For `0 < ε < t₃`, `I_tail = I_bg(ε) + I_v(ε) + I_q(ε) + I_curv(ε) + I_cross(ε) - I_in(ε)`!
      have hid : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
          (A1 / ε ^ 5 + (B1 + A_v - A_in) / ε ^ 3 + (C1 + B_v + A_q - B_in) / ε) =
          I_tail - (((∫ (t : ℝ) in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
            uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p) - (A1 / ε ^ 5 + B1 / ε ^ 3 + C1 / ε)) +
            ((∫ (t : ℝ) in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) - (A_v / ε ^ 3 + B_v / ε)) +
            ((∫ (t : ℝ) in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1 - v t) / uctM t ^ p) - A_q / ε) +
            (∫ (t : ℝ) in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) +
            (∫ (t : ℝ) in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) -
            ((∫ (t : ℝ) in Ioc ε t₃, stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p) - (A_in / ε ^ 3 + B_in / ε))) := by
        filter_upwards [Ioo_mem_nhdsGT ht3_pos] with ε hε
        have hε0 : 0 < ε := hε.1
        have hi_bg := hbg_int hp1 hε0
        have hi_curv := hcurv_t_int.mono_set (fun t (ht : t ∈ Ioi ε) => hε0.trans ht)
        have hi_cross := hcross_t_int.mono_set (fun t (ht : t ∈ Ioi ε) => hε0.trans ht)
        -- `v` and `e^v - 1 - v` have compact support in `(-10τ₁, 10τ₁)` so both are integrable on `Ioi ε`!
        have hH_c : ContinuousOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖) (Ioi 0) := by
          cases kind
          · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_star_imag ht
            exact (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
              ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
              fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')).add
              (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_cosh.comp
                ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
                fun _ _ => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.cosh_pos _).ne'))
          · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_ce_imag ht
            exact continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
              ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
              fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')
        have hm_c : ContinuousOn uctM (Ioi 0) := fun t ht => (hasDerivAt_uctM ht).continuousAt.continuousWithinAt
        have hi_v : IntegrableOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) (Ioi ε) := by
          have hc : ContinuousOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) (Ioi 0) :=
            ((continuousOn_const.mul hH_c).mul hv_cd.continuous.continuousOn).div (hm_c.pow p) fun t ht => pow_ne_zero p (uctM_pos ht).ne'
          rw [← Ioc_union_Ioi_eq_Ioi (show ε ≤ max ε (10 * τ₁) by exact le_max_left _ _), integrableOn_union]
          exact ⟨((hc.mono fun t (ht : t ∈ Icc ε (max ε (10 * τ₁))) => lt_of_lt_of_le hε0 ht.1).integrableOn_Icc).mono_set Ioc_subset_Icc_self,
            (integrableOn_zero (μ := volume) (s := Ioi (max ε (10 * τ₁)))).congr_fun (fun t ht => by
              have hvt : v t = 0 := by by_contra hne; linarith [(hv_s hne).2, le_max_right ε (10 * τ₁), show max ε (10 * τ₁) < t from ht]
              rw [hvt, mul_zero, zero_div]) measurableSet_Ioi⟩
        have hi_q : IntegrableOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1 - v t) / uctM t ^ p) (Ioi ε) := by
          have hc : ContinuousOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1 - v t) / uctM t ^ p) (Ioi 0) :=
            ((continuousOn_const.mul hH_c).mul (((Real.continuous_exp.comp hv_cd.continuous).sub continuous_const).sub hv_cd.continuous).continuousOn).div
              (hm_c.pow p) fun t ht => pow_ne_zero p (uctM_pos ht).ne'
          rw [← Ioc_union_Ioi_eq_Ioi (show ε ≤ max ε (10 * τ₁) by exact le_max_left _ _), integrableOn_union]
          exact ⟨((hc.mono fun t (ht : t ∈ Icc ε (max ε (10 * τ₁))) => lt_of_lt_of_le hε0 ht.1).integrableOn_Icc).mono_set Ioc_subset_Icc_self,
            (integrableOn_zero (μ := volume) (s := Ioi (max ε (10 * τ₁)))).congr_fun (fun t ht => by
              have hvt : v t = 0 := by by_contra hne; linarith [(hv_s hne).2, le_max_right ε (10 * τ₁), show max ε (10 * τ₁) < t from ht]
              rw [hvt, Real.exp_zero, sub_self, sub_zero, mul_zero, zero_div]) measurableSet_Ioi⟩
        -- Sum the 5 integrals on `Ioi ε` to get `∫_ε^∞ D_*(m(t)) m'(t) / m(t)^p dt`!
        have hi_12 : IntegrableOn (fun t : ℝ =>
            (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ - uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) (Ioi ε) := hi_bg.add hi_v
        have hi_123 : IntegrableOn (fun t : ℝ =>
            ((uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ - uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1 - v t) / uctM t ^ p) (Ioi ε) := hi_12.add hi_q
        have hi_1234 : IntegrableOn (fun t : ℝ =>
            (((uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ - uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1 - v t) / uctM t ^ p) +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) (Ioi ε) := hi_123.add hi_curv
        have hpt5 : ∀ t ∈ Ioi ε,
            ((((uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ - uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1 - v t) / uctM t ^ p) +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) +
            uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p =
            stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p := fun t ht => by
          have ht0 : 0 < t := hε0.trans ht
          unfold stripDstar uctIfl
          rw [show uctM t = ceEll (π * t / 2) from rfl, tau0_ceEll ht0, show ceEll (π * t / 2) = uctM t from rfl,
            sub_mul, mul_comm (stripIoscD kind v (uctM t) * _), ← mul_assoc, uctMderiv_mul_stripIoscD kind v ht0,
            Real.rpow_neg (uctM_pos ht0).le]
          ring
        have hsum5 : (∫ t in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
              uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t ^ p) +
            (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * v t / uctM t ^ p) +
            (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1 - v t) / uctM t ^ p) +
            (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) +
            (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t / uctM t ^ p) =
            ∫ t in Ioi ε, stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p := by
          rw [← integral_add hi_bg hi_v, ← integral_add hi_12 hi_q, ← integral_add hi_123 hi_curv, ← integral_add hi_1234 hi_cross]
          exact setIntegral_congr_fun measurableSet_Ioi hpt5
        have hD_ε_int : IntegrableOn (fun t => stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p) (Ioi ε) :=
          (hi_1234.add hi_cross).congr_fun hpt5 measurableSet_Ioi
        have hsplit_t3 : (∫ t in Ioi ε, stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p) =
            (∫ t in Ioc ε t₃, stripDstar kind c v v0' (uctM t) * uctMderiv t / uctM t ^ p) + I_tail := by
          rw [← Ioc_union_Ioi_eq_Ioi hε.2.le,
            setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
              measurableSet_Ioi (hD_ε_int.mono_set Ioc_subset_Ioi_self) (hD_ε_int.mono_set fun x hx => hε.2.trans hx)]
        have hpol : A1 / ε ^ 5 + (B1 + A_v - A_in) / ε ^ 3 + (C1 + B_v + A_q - B_in) / ε =
            (A1 / ε ^ 5 + B1 / ε ^ 3 + C1 / ε) + (A_v / ε ^ 3 + B_v / ε) + A_q / ε - (A_in / ε ^ 3 + B_in / ε) := by ring
        linarith [hsum5, hsplit_t3, hpol]
      have htend_rhs : Tendsto (fun ε : ℝ =>
          A1 / ε ^ 5 + (B1 + A_v - A_in) / ε ^ 3 + (C1 + B_v + A_q - B_in) / ε) (𝓝[>] (0 : ℝ))
          (𝓝 (I_tail - (L1 + L_v + L_q + L_curv + L_cross - L_in))) := by
        have h := (tendsto_const_nhds (x := I_tail)).sub (((((h1.add h_lin).add h_q).add
          (FctPhiKill.tendsto_setIntegral_Ioi_zero hcurv_t_int)).add
          (FctPhiKill.tendsto_setIntegral_Ioi_zero hcross_t_int)).sub h_in)
        exact h.congr' (hid.mono fun _ h => h.symm)
      have h0 := tendsto_odd_pole_zero htend_rhs
      linarith
    rw [hsubst, ← hL1_eq, hcomb_eq,
      show L1 + L_v + L_q + L_curv + L_cross - L_in - L1 = L_v + L_q + L_curv + L_cross - L_in by ring]
    -- Bound each of `|L_v|, |L_q|, |L_curv|, |L_cross|, |L_in|` by `C * τ₁^{3-2p}` (and `|α| τ₁^{1-2p}` for `L_in`)!
    have hτ3_le : τ₁ ^ 3 ≤ τ₁ ^ (3 - 2 * (p : ℤ)) := by
      have h1 : (3 - 2 * (p : ℤ)) ≤ 3 := by omega
      rw [← zpow_natCast τ₁ 3]
      exact zpow_le_zpow_right_of_le_one₀ hτ₁ hτ₁_1 h1
    have hc_p_le : c⁻¹ * τ₁ ^ (-(2 * (p : ℤ))) ≤ τ₁ ^ (3 - 2 * (p : ℤ)) := by
      rw [hc_inv, ← zpow_natCast τ₁ 4, ← zpow_add₀ hτ₁.ne']
      exact zpow_le_zpow_right_of_le_one₀ hτ₁ hτ₁_1 (by omega)
    have hc_le : c⁻¹ ≤ τ₁ ^ (3 - 2 * (p : ℤ)) := by
      rw [hc_inv, ← zpow_natCast τ₁ 4]
      exact zpow_le_zpow_right_of_le_one₀ hτ₁ hτ₁_1 (by omega)
    have hLv' : |L_v| ≤ C_lin * M_L1 * τ₁ ^ (3 - 2 * (p : ℤ)) :=
      hLv_bd.trans ((mul_le_mul_of_nonneg_left hv_L1 hClin_nn).trans
        (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hτ3_le (by positivity)))
    have hLcurv' : |L_curv| ≤ C_curv * τ₁ ^ (3 - 2 * (p : ℤ)) := by
      rw [hcurv_t_eq]
      exact hcurv_bd.trans (mul_le_mul_of_nonneg_left hc_le hCcurv_nn)
    have hLcross' : |L_cross| ≤ uctAlphaOsc * C_curv * τ₁ ^ (3 - 2 * (p : ℤ)) :=
      hcross_t_bd.trans (by rw [mul_assoc (uctAlphaOsc * C_curv)]; exact mul_le_mul_of_nonneg_left hc_p_le (by positivity))
    have htri : |L_v + L_q + L_curv + L_cross - L_in| ≤ |L_v| + |L_q| + |L_curv| + |L_cross| + |L_in| :=
      (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    have hα_nn : 0 ≤ |α| * τ₁ ^ (1 - 2 * (p : ℤ)) := mul_nonneg (abs_nonneg _) (zpow_nonneg hτ₁.le _)
    have h1 : (C_lin * M_L1 + C_curv + uctAlphaOsc * C_curv + C_q) * τ₁ ^ (3 - 2 * (p : ℤ)) ≤
        (C_lin * M_L1 + C_curv + uctAlphaOsc * C_curv + C_q) * (τ₁ ^ (3 - 2 * (p : ℤ)) + |α| * τ₁ ^ (1 - 2 * (p : ℤ))) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hα_nn) (by positivity)
    linarith
  -- Assemble all 5 parts into the final conjunction!
  have hCcos_le : C_cos ≤ C_all := (le_max_left _ _).trans (le_max_left _ _)
  have hCcurv_le : C_curv ≤ C_all := (le_max_right _ _).trans (le_max_left _ _)
  have hCin_le : C_in ≤ C_all := (le_max_left _ _).trans (le_max_right _ _)
  have hCbump_le : C_lin * M_L1 + C_curv + uctAlphaOsc * C_curv + C_q + C_in + |L_bg2| ≤ C_all :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨hb1_int, hb1_bd⟩ := hbump_p 1 le_rfl (by norm_num)
  obtain ⟨hb2_int, hb2_bd⟩ := hbump_p 2 (by norm_num) le_rfl
  simp only [pow_one, ↓reduceIte, Nat.cast_one, show (3 : ℤ) - 2 * 1 = 1 by norm_num,
    show (1 : ℤ) - 2 * 1 = -1 by norm_num, zpow_one, zpow_neg_one] at hb1_int hb1_bd
  simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte, Nat.cast_ofNat,
    show (3 : ℤ) - 2 * 2 = -1 by norm_num, show (1 : ℤ) - 2 * 2 = -3 by norm_num] at hb2_int hb2_bd
  refine ⟨hcos_int, hcos_bd.trans (mul_le_mul_of_nonneg_right hCcos_le (pow_nonneg hτ₁.le 3)),
    fun hk => ⟨by
      rw [hcos_star hk]
      exact mul_nonneg hαo_nn (setIntegral_nonneg measurableSet_Ioi fun t _ =>
        mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
          (by linarith [Real.cos_le_one (fctThetaD v t)])),
      hcos_star hk⟩,
    hDstar_int, hDstar_bd.trans (mul_le_mul_of_nonneg_right hCcurv_le (pow_nonneg hτ₁.le 3)),
    fun p hp => ⟨(hcurv_all p hp).1, (hcurv_all p hp).2.1.trans (mul_le_mul_of_nonneg_right hCcurv_le (inv_nonneg.mpr hc.le))⟩,
    hIn0_int, hIn0_bd.trans (mul_le_mul_of_nonneg_right hCin_le (by positivity)),
    hbg_fp1, hb1_int, hb1_bd.trans (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L_bg2]) (by positivity)),
    hb2_int, ?_⟩
  -- For `p = 2`: `|∫ D_*/L²| ≤ |∫ D_*/L² - L_bg2| + |L_bg2| ≤ (... + |L_bg2|) * (τ₁⁻¹ + |α| τ₁⁻³)` since `1 ≤ τ₁⁻¹`!
  have h1_inv : (1 : ℝ) ≤ τ₁ ^ (-1 : ℤ) := by rw [zpow_neg_one]; exact (one_le_inv₀ hτ₁).mpr hτ₁_1
  have hLbg2_le : |L_bg2| ≤ |L_bg2| * (τ₁ ^ (-1 : ℤ) + |α| * τ₁ ^ (-3 : ℤ)) :=
    le_mul_of_one_le_right (abs_nonneg _) (h1_inv.trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (zpow_nonneg hτ₁.le _))))
  have htri : |∫ L in Ioi (3 * δ_L), stripDstar kind c v v0' L / L ^ 2| ≤
      |(∫ L in Ioi (3 * δ_L), stripDstar kind c v v0' L / L ^ 2) - L_bg2| + |L_bg2| := by
    have := abs_add_le ((∫ L in Ioi (3 * δ_L), stripDstar kind c v v0' L / L ^ 2) - L_bg2) L_bg2
    rwa [sub_add_cancel] at this
  calc |∫ L in Ioi (3 * δ_L), stripDstar kind c v v0' L / L ^ 2|
      ≤ (C_lin * M_L1 + C_curv + uctAlphaOsc * C_curv + C_q + C_in + |L_bg2|) *
          (τ₁ ^ (-1 : ℤ) + |α| * τ₁ ^ (-3 : ℤ)) := by linarith
    _ ≤ C_all * (τ₁ ^ (-1 : ℤ) + |α| * τ₁ ^ (-3 : ℤ)) :=
        mul_le_mul_of_nonneg_right hCbump_le (add_nonneg (zpow_nonneg hτ₁.le _) (mul_nonneg (abs_nonneg _) (zpow_nonneg hτ₁.le _)))

/-- info: 'FormalResearch.SignUncertainty.FctCompD.fct_comp_D_part2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.FctCompD.fct_comp_D_part2

end FormalResearch.SignUncertainty.FctCompD



