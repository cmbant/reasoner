module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFarPhase
public import FormalResearch.SignUncertainty.CtDyadicMoments
public import FormalResearch.SignUncertainty.CtBoasKdW
public import FormalResearch.SignUncertainty.CtBoasPlbField
public import FormalResearch.SignUncertainty.FctCuspEdgeIbp

/-!
# `ct:boas-ineq`: the numerical bookkeeping of the far-field and truncation errors

`constant_terms_lower.tex`, `ct:boas` Step 1 and Step 3: the explicit errors of `CtBoasFarField` and `CtDyadicMoments`
are `O(c^{-2})` for large `c`:

* `farEps_le`: `boasFarEps c ⌈c²⌉ (boasPhaseEps c C_θ) ≤ c^{-2}` (the harmonics sum `Σ_{2 ≤ k < n}`, the Gaussian tails
  `e = √2 e^{-(log c)²}`, the phase error `E_ph = O(c^{-8} (log c)²)`);
* `farE2_le`: `farE2 c ≤ c^{-2}`.

The auxiliary facts: `log c ≤ c^δ` eventually, and `c^k e^{-αc} ≤ 1` eventually.  **Proved**, unconditional.
-/

@[expose] public section

open Filter Topology Finset
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.SignUncertainty.CtPhaseFar

/-- `c^k e^{-αc} ≤ 1` for large `c`. -/
lemma eventually_rpow_mul_exp_le (k α : ℝ) (hα : 0 < α) :
    ∀ᶠ c : ℝ in atTop, c ^ k * Real.exp (-(α * c)) ≤ 1 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k α hα
  have := h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [this] with c hc
  have : -α * c = -(α * c) := by ring
  rw [this] at hc
  exact hc.le

/-- `log c ≤ c^δ` for large `c`. -/
lemma eventually_log_le_rpow (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ c : ℝ in atTop, Real.log c ≤ c ^ δ := by
  have h2 : 0 < δ / 2 := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ((2 / δ) ^ (2 / δ))] with c hc1 hc2
  have hc0 : 0 < c := by linarith
  have h1 := Real.log_le_rpow_div hc0.le h2
  have h3 : 2 / δ ≤ c ^ (δ / 2) := by
    have := Real.rpow_le_rpow (by positivity) hc2 (by positivity : (0 : ℝ) ≤ δ / 2)
    rwa [← Real.rpow_mul (by positivity), show 2 / δ * (δ / 2) = 1 by field_simp, Real.rpow_one] at this
  have h4 : c ^ δ = c ^ (δ / 2) * c ^ (δ / 2) := by
    rw [← Real.rpow_add hc0]; ring_nf
  have h5 : c ^ (δ / 2) / (δ / 2) ≤ c ^ δ := by
    rw [div_le_iff₀ h2, h4]
    have h0 : 0 ≤ c ^ (δ / 2) := by positivity
    have h6 : 1 ≤ c ^ (δ / 2) * (δ / 2) := by
      have := mul_le_mul_of_nonneg_right h3 h2.le
      rwa [show 2 / δ * (δ / 2) = 1 by field_simp] at this
    nlinarith [mul_le_mul_of_nonneg_left h6 h0]
  linarith

/-- `exp(-(log c)^2) ≤ c^{-k}` once `log c ≥ k`. -/
lemma exp_neg_log_sq_le {c k : ℝ} (hc : 1 < c) (hk : k ≤ Real.log c) :
    Real.exp (-(Real.log c) ^ 2) ≤ c ^ (-k) := by
  have hc0 : 0 < c := by linarith
  rw [Real.rpow_def_of_pos hc0]
  apply Real.exp_le_exp.2
  have := Real.log_pos hc
  nlinarith

lemma exp_neg_four_log_sq_le {c k : ℝ} (hc : 1 < c) (hk : k ≤ Real.log c) :
    Real.exp (-(4 * Real.log c ^ 2)) ≤ c ^ (-k) := by
  have hc0 : 0 < c := by linarith
  rw [Real.rpow_def_of_pos hc0]
  apply Real.exp_le_exp.2
  have := Real.log_pos hc
  nlinarith

lemma farE2_le {c : ℝ} (hc : 1 < c) (hk : 2 ≤ Real.log c) : farE2 c ≤ 2 * c ^ (-(2 : ℝ)) := by
  unfold farE2
  have h := exp_neg_four_log_sq_le hc hk
  have : √2 ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h0 := Real.exp_pos (-(4 * Real.log c ^ 2))
  nlinarith

/-- `E_ph = O(c^{-2})`. -/
lemma eventually_phaseEps_le (Cθ : ℝ) : ∀ᶠ c : ℝ in atTop, boasPhaseEps c Cθ ≤ c ^ (-(2 : ℝ)) := by
  have hK := (by unfold phaseFarK; positivity : 0 ≤ phaseFarK)
  have h5 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5)).eventually_ge_atTop (phaseFarK + 605 * |Cθ|)
  filter_upwards [eventually_ge_atTop (Real.exp 6), h5] with c hc h5
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (6 : ℝ)]) hc
  have hc0 : 0 < c := by linarith
  have hs1 : 1 ≤ Real.log c := by
    have := Real.log_le_log (Real.exp_pos 6) hc
    rw [Real.log_exp] at this; linarith
  set s := Real.log c with hs
  have hπ9 : 9 < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hπ10 : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hexp : Real.exp (-(π ^ 2 * s)) ≤ c ^ (-(9 : ℝ)) := by
    rw [Real.rpow_def_of_pos hc0]
    apply Real.exp_le_exp.2
    rw [← hs]; nlinarith
  have hc9 : 0 < c ^ (-(9 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hsc : s ≤ c := by have := Real.log_le_sub_one_of_pos hc0; linarith
  unfold boasPhaseEps
  -- first term
  have hD : farD c / 2 = c * s / 2 := by unfold farD; ring
  have hex1 : 2 * π ^ 2 * (farD c / 2) / c = π ^ 2 * s := by rw [hD]; field_simp
  rw [hex1]
  have hT1 : phaseFarK * (farD c / 2) * Real.exp (-(π ^ 2 * s)) ≤ phaseFarK * s * c ^ (-(8 : ℝ)) := by
    have e8 : c * c ^ (-(9 : ℝ)) = c ^ (-(8 : ℝ)) := by
      rw [← Real.rpow_one_add' hc0.le (by norm_num)]; norm_num
    rw [hD]
    calc phaseFarK * (c * s / 2) * Real.exp (-(π ^ 2 * s)) ≤ phaseFarK * (c * s / 2) * c ^ (-(9 : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ phaseFarK * s * (c * c ^ (-(9 : ℝ))) := by nlinarith [mul_nonneg (mul_nonneg hK (by linarith : (0 : ℝ) ≤ s)) (mul_nonneg hc0.le hc9.le)]
      _ = _ := by rw [e8]
  -- second term
  have hT2 : Cθ * ((1 + (π * s - 1) ^ 2) * Real.exp (-π * (π * s - 1))) ≤ 605 * |Cθ| * s ^ 2 * c ^ (-(9 : ℝ)) := by
    have he : Real.exp (-π * (π * s - 1)) = Real.exp (-(π ^ 2 * s)) * Real.exp π := by
      rw [← Real.exp_add]; congr 1; ring
    have hexpπ : Real.exp π ≤ 55 := by
      have h1 : Real.exp π ≤ Real.exp 4 := Real.exp_le_exp.2 (by linarith [Real.pi_lt_d2])
      have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 := Real.exp_one_lt_d9
      have h4 : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h3.le 4
      nlinarith
    have hq : 1 + (π * s - 1) ^ 2 ≤ 11 * s ^ 2 := by
      have h1 : (π * s - 1) ^ 2 ≤ π ^ 2 * s ^ 2 := by nlinarith [Real.pi_gt_three, hs1]
      have h2 : π ^ 2 * s ^ 2 ≤ 10 * s ^ 2 := by nlinarith [sq_nonneg s]
      nlinarith [sq_nonneg s]
    have hq0 : 0 ≤ 1 + (π * s - 1) ^ 2 := by positivity
    calc Cθ * ((1 + (π * s - 1) ^ 2) * Real.exp (-π * (π * s - 1))) ≤ |Cθ| * ((11 * s ^ 2) * (c ^ (-(9 : ℝ)) * 55)) := by
          refine (le_abs_self _).trans ?_
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 + (π * s - 1) ^ 2) * Real.exp (-π * (π * s - 1)))]
          refine mul_le_mul_of_nonneg_left (mul_le_mul hq ?_ (Real.exp_pos _).le (by positivity)) (abs_nonneg _)
          rw [he]
          exact mul_le_mul hexp hexpπ (Real.exp_pos _).le hc9.le
      _ = 605 * |Cθ| * s ^ 2 * c ^ (-(9 : ℝ)) := by ring
  -- combine
  have e7 : c * c ^ (-(8 : ℝ)) = c ^ (-(7 : ℝ)) := by
    rw [← Real.rpow_one_add' hc0.le (by norm_num)]; norm_num
  have e7' : c ^ 2 * c ^ (-(9 : ℝ)) = c ^ (-(7 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hc0]; norm_num
  have e52 : c ^ (5 : ℝ) * c ^ (-(7 : ℝ)) = c ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hc0]; norm_num
  have h8 : 0 < c ^ (-(8 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have h7 : 0 < c ^ (-(7 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hs2 : s ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by linarith) hsc 2
  have a1 : phaseFarK * s * c ^ (-(8 : ℝ)) ≤ phaseFarK * c ^ (-(7 : ℝ)) := by
    rw [← e7]
    nlinarith [mul_le_mul_of_nonneg_left hsc (mul_nonneg hK h8.le)]
  have a2 : 605 * |Cθ| * s ^ 2 * c ^ (-(9 : ℝ)) ≤ 605 * |Cθ| * c ^ (-(7 : ℝ)) := by
    rw [← e7']
    have : 0 ≤ 605 * |Cθ| * c ^ (-(9 : ℝ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs2 this]
  have h5' : (phaseFarK + 605 * |Cθ|) * c ^ (-(7 : ℝ)) ≤ c ^ (-(2 : ℝ)) := by
    rw [← e52]; exact mul_le_mul_of_nonneg_right h5 h7.le
  nlinarith

/-- **The `far` error is `O(c^{-2})`** (`ct:boas` Step 1, the choice `n = ⌈c²⌉`): `boasFarEps c ⌈c²⌉ (E_ph) ≤ 60 c^{-2}`. -/
lemma eventually_farEps_le (Cθ : ℝ) :
    ∀ᶠ c : ℝ in atTop, boasFarEps c ⌈c ^ 2⌉₊ (boasPhaseEps c Cθ) ≤ 60 * c ^ (-(2 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (Real.exp 6), eventually_phaseEps_le Cθ,
    eventually_rpow_mul_exp_le 6 (1 / 4) (by norm_num)] with c hc hph hE
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (6 : ℝ)]) hc
  have hc0 : 0 < c := by linarith
  have hc4 : 4 ≤ c := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hs6 : 6 ≤ Real.log c := by
    have := Real.log_le_log (Real.exp_pos 6) hc
    rwa [Real.log_exp] at this
  set s := Real.log c with hs
  have hsc : s ≤ c := by have := Real.log_le_sub_one_of_pos hc0; linarith
  set n := ⌈c ^ 2⌉₊ with hn
  have hn1 : c ^ 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hn2 : (n : ℝ) ≤ 2 * c ^ 2 := by
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ c ^ 2)
    nlinarith
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) hn1
  have hcm2 : c ^ (-(2 : ℝ)) = (c ^ 2)⁻¹ := by
    rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcm2' : 0 < c ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hmon : ∀ a b : ℝ, a ≤ b → c ^ a ≤ c ^ b := fun a b hab => Real.rpow_le_rpow_of_exponent_le hc1.le hab
  have E1 : farE1 c ≤ 2 * c ^ (-(6 : ℝ)) := by
    unfold farE1
    have h := exp_neg_log_sq_le hc1 hs6
    have : √2 ≤ 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h0 := Real.exp_pos (-(Real.log c) ^ 2)
    nlinarith
  have E2 := farE2_le hc1 (by linarith)
  have hc6 : c ^ (-(6 : ℝ)) ≤ c ^ (-(2 : ℝ)) := hmon _ _ (by norm_num)
  have hc6' : c ^ 2 * c ^ (-(6 : ℝ)) ≤ c ^ (-(2 : ℝ)) := by
    have : c ^ 2 * c ^ (-(6 : ℝ)) = c ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hc0]; norm_num
    rw [this]; exact hmon _ _ (by norm_num)
  have hE1pos : 0 ≤ farE1 c := by unfold farE1; positivity
  -- A1, A2
  have A1 : (n : ℝ) * (2 * farE1 c) ≤ 8 * c ^ (-(2 : ℝ)) := by
    have : (n : ℝ) * (2 * farE1 c) ≤ (2 * c ^ 2) * (2 * (2 * c ^ (-(6 : ℝ)))) :=
      mul_le_mul hn2 (by linarith) (by positivity) (by positivity)
    nlinarith
  have A2 : 2 / (n : ℝ) ≤ 2 * c ^ (-(2 : ℝ)) := by
    rw [hcm2, div_le_iff₀ hn0]
    have h1 : 2 * (c ^ 2)⁻¹ * c ^ 2 ≤ 2 * (c ^ 2)⁻¹ * (n : ℝ) := mul_le_mul_of_nonneg_left hn1 (by positivity)
    have h2 : 2 * (c ^ 2)⁻¹ * c ^ 2 = 2 := by field_simp
    linarith only [h1, h2]
  -- A3: the harmonic sum
  have hW1 : 1 ≤ farW c := by unfold farW; linarith
  have hWd : farW c = c / 4 := rfl
  have hterm : ∀ k ∈ Finset.Ico 2 n, ((k : ℝ) ^ (-c) +
      2 * farD c * (((3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * farW c ^ 2)) +
        1 * Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) *
          √(2 * π / (2 * π ^ 2 * farW c ^ 2))))) ≤ 5 * c ^ 2 * Real.exp (-(c / 4)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.1 hk).1
    have hk0 : (0 : ℝ) < k := by linarith
    have hex4 : 0 < Real.exp (-(c / 4)) := Real.exp_pos _
    -- (a)
    have a1 : (k : ℝ) ^ (-c) ≤ Real.exp (-(c / 4)) := by
      have h1 : (k : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-c) := Real.rpow_le_rpow_of_nonpos (by norm_num) hk2 (by linarith)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
      refine h1.trans (Real.exp_le_exp.2 ?_)
      have := Real.log_two_gt_d9
      nlinarith
    -- (b)
    have a2 : (3 * (k : ℝ) / 4) ^ (-c) ≤ Real.exp (-(c / 4)) := by
      have h1 : (3 * (k : ℝ) / 4) ^ (-c) ≤ (3 / 2 : ℝ) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at h1
      refine h1.trans (Real.exp_le_exp.2 ?_)
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      norm_num at this
      nlinarith
    -- (c), (d)
    have hWp : 0 < farW c := by linarith
    have s1 : √(π / (2 * π ^ 2 * farW c ^ 2)) ≤ 1 := by
      rw [Real.sqrt_le_one]
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three, mul_le_mul hW1 hW1 zero_le_one hWp.le]
    have s2 : √(2 * π / (2 * π ^ 2 * farW c ^ 2)) ≤ 1 := by
      rw [Real.sqrt_le_one]
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three, mul_le_mul hW1 hW1 zero_le_one hWp.le]
    have a3 : Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) ≤ Real.exp (-(c / 4)) := by
      apply Real.exp_le_exp.2
      have hk4 : (1 / 2 : ℝ) ≤ (k : ℝ) / 4 := by linarith only [hk2]
      have hk4' : (1 / 4 : ℝ) ≤ ((k : ℝ) / 4) ^ 2 := by nlinarith only [hk4]
      have hW2 : farW c ≤ farW c ^ 2 := by nlinarith only [hW1]
      have hπ2 : 4 ≤ π ^ 2 := by nlinarith only [Real.pi_gt_three]
      have h4 : π ^ 2 * farW c ^ 2 * (1 / 4) ≤ π ^ 2 * farW c ^ 2 * ((k : ℝ) / 4) ^ 2 :=
        mul_le_mul_of_nonneg_left hk4' (by positivity)
      have h3 : farW c ^ 2 ≤ π ^ 2 * farW c ^ 2 * (1 / 4) := by nlinarith only [sq_nonneg (farW c), hπ2]
      have h5 : c / 4 = farW c := rfl
      have e : -(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2 = -(π ^ 2 * farW c ^ 2 * ((k : ℝ) / 4) ^ 2) := by ring
      rw [e]
      linarith only [h4, h3, hW2, h5]
    have hD : farD c ≤ c * c := by
      unfold farD; exact mul_le_mul_of_nonneg_left hsc hc0.le
    have hD0 : 0 ≤ farD c := by unfold farD; positivity
    have b1 : (3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * farW c ^ 2)) ≤ Real.exp (-(c / 4)) * 1 :=
      mul_le_mul a2 s1 (Real.sqrt_nonneg _) hex4.le
    have b2 : 1 * Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) * √(2 * π / (2 * π ^ 2 * farW c ^ 2)) ≤
        1 * Real.exp (-(c / 4)) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left a3 zero_le_one) s2 (Real.sqrt_nonneg _) (by positivity)
    have hsum : (3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * farW c ^ 2)) +
        1 * Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) * √(2 * π / (2 * π ^ 2 * farW c ^ 2)) ≤
        2 * Real.exp (-(c / 4)) := by linarith
    have hc2 : (1 : ℝ) ≤ c ^ 2 := by nlinarith only [hc1]
    have hfin : 1 + 4 * farD c ≤ 5 * c ^ 2 := by nlinarith only [hD, hc2]
    refine (add_le_add a1 (mul_le_mul_of_nonneg_left hsum (by positivity))).trans ?_
    have e : Real.exp (-(c / 4)) + 2 * farD c * (2 * Real.exp (-(c / 4))) =
        (1 + 4 * farD c) * Real.exp (-(c / 4)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hfin hex4.le
  have A3 : 2 * ∑ k ∈ Finset.Ico 2 n, ((k : ℝ) ^ (-c) +
      2 * farD c * (((3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * farW c ^ 2)) +
        1 * Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) *
          √(2 * π / (2 * π ^ 2 * farW c ^ 2))))) ≤ 20 * c ^ (-(2 : ℝ)) := by
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [nsmul_eq_mul, Nat.card_Ico] at hsum
    have hcard : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
    have hex0 : 0 < 5 * c ^ 2 * Real.exp (-(c / 4)) := by positivity
    have h1 : (((n - 2 : ℕ) : ℝ)) * (5 * c ^ 2 * Real.exp (-(c / 4))) ≤ (2 * c ^ 2) * (5 * c ^ 2 * Real.exp (-(c / 4))) :=
      mul_le_mul_of_nonneg_right (hcard.trans hn2) hex0.le
    have hE' : c ^ 6 * Real.exp (-(c / 4)) ≤ 1 := by
      have := hE
      rwa [show (1 / 4 : ℝ) * c = c / 4 by ring, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have h2 : c ^ 4 * Real.exp (-(c / 4)) ≤ c ^ (-(2 : ℝ)) := by
      have e : c ^ 4 * Real.exp (-(c / 4)) = c ^ (-(2 : ℝ)) * (c ^ 6 * Real.exp (-(c / 4))) := by
        rw [hcm2]; field_simp
      rw [e]
      calc c ^ (-(2 : ℝ)) * (c ^ 6 * Real.exp (-(c / 4))) ≤ c ^ (-(2 : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hE' hcm2'.le
        _ = _ := mul_one _
    have e2 : (2 * c ^ 2) * (5 * c ^ 2 * Real.exp (-(c / 4))) = 10 * (c ^ 4 * Real.exp (-(c / 4))) := by ring
    linarith only [hsum, h1, h2, e2]
  unfold boasFarEps
  linarith only [A1, A2, A3, E1, E2, hph, hc6, hE1pos]

/-! ### The frozen error `Pb` and the block widths -/

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCuspEdge in
/-- `τ₀(L) ≤ 2e^L/π` for `L > 0` (`m(τ) > log(πτ/2)`). -/
lemma tau0_le_two_exp {L : ℝ} (hL : 0 < L) : tau0 L ≤ 2 * Real.exp L / π := by
  have ht0 : 0 < tau0 L := tau0_pos hL
  have hm : hankelEdgeM (tau0 L) = L := ceEll_tau0 hL
  have hlog := hankelEdgeM_ge_log ht0
  rw [hm] at hlog
  have h1 : π * tau0 L / 2 < Real.exp L := by
    have := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log (by positivity)] at this
  rw [le_div_iff₀ Real.pi_pos]
  linarith

open FormalResearch.CohnElkies in
/-- `W_j ≥ c^{-2}` for blocks with `L_j ≤ log c`. -/
lemma boasW_lower {c a : ℝ} {j : ℕ} (hc : 1 ≤ c) (hlog : 1 ≤ Real.log c) (ha : 0 < a)
    (hL : tentNode a (j + 1) ≤ Real.log c) : 1 ≤ c ^ 2 * boasW c a j := by
  have hc0 : 0 < c := by linarith
  have hL0 : 0 < tentNode a (j + 1) := tentNode_pos ha _
  have hτ := tau0_pos hL0
  have hτu := tau0_le_two_exp hL0
  set L := tentNode a (j + 1)
  have hN : 1000 ≤ √(1000000 * (1 + L) * Real.log c) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have heL : Real.exp L ≤ c := by
    calc Real.exp L ≤ Real.exp (Real.log c) := Real.exp_le_exp.2 hL
      _ = c := Real.exp_log hc0
  have hτc : tau0 L ≤ c := by
    have : 2 * Real.exp L / π ≤ Real.exp L := by
      rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.exp_pos L, Real.pi_gt_three]
    linarith
  have hW : boasW c a j = √(1000000 * (1 + L) * Real.log c) / (c * tau0 L) := rfl
  rw [hW, show c ^ 2 * (√(1000000 * (1 + L) * Real.log c) / (c * tau0 L)) =
      c * √(1000000 * (1 + L) * Real.log c) / tau0 L by field_simp, le_div_iff₀ hτ]
  nlinarith [mul_le_mul hτc hN (by norm_num) hc0.le]

open FormalResearch.CohnElkies in
/-- `W_j² ≤ 2·10⁶ log c/(c² a)` (`τ_j² ≥ L_j ≥ a`, `(1+L)/L ≤ 2/a`). -/
lemma boasW_sq_le {c a : ℝ} {j : ℕ} (hc : 1 ≤ c) (hlog : 1 ≤ Real.log c) (ha : 0 < a) (ha1 : a ≤ 1) :
    boasW c a j ^ 2 ≤ 2000000 * Real.log c / (c ^ 2 * a) := by
  have hc0 : 0 < c := by linarith
  have hL0 : 0 < tentNode a (j + 1) := tentNode_pos ha _
  have haL : a ≤ tentNode a (j + 1) := (tentNode_strictMono ha).monotone (Nat.zero_le (j + 1))
  have hτ2 := tau0_sq_ge hL0
  have hτ := tau0_pos hL0
  set L := tentNode a (j + 1)
  have hW : boasW c a j = √(1000000 * (1 + L) * Real.log c) / (c * tau0 L) := rfl
  rw [hW, div_pow, Real.sq_sqrt (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (1 + L) * a ≤ 2 * L := by nlinarith
  have h2 : 0 ≤ 1000000 * Real.log c := by positivity
  have h3 : 1000000 * (1 + L) * Real.log c * (c ^ 2 * a) = 1000000 * Real.log c * c ^ 2 * ((1 + L) * a) := by ring
  have h4 : 2000000 * Real.log c * (c * tau0 L) ^ 2 ≥ 2000000 * Real.log c * (c ^ 2 * L) := by
    have : c ^ 2 * L ≤ (c * tau0 L) ^ 2 := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hτ2 (sq_nonneg c)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  rw [h3]
  have h5 : 1000000 * Real.log c * c ^ 2 * ((1 + L) * a) ≤ 1000000 * Real.log c * c ^ 2 * (2 * L) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [h5, h4]

/-- **The frozen error `Pb`** (`ct:P-lb`, bookkeeping): for `n ≈ c⁶`, `c^{-2} ≤ W`, and an exponent `(L₀-L_T)²/(2W²) ≥ c`
with `e^{-c} ≤ c^{-12}`, `hankelFrozenPb c 1 W L_T L₀ n ≤ 30 c^{-4}`. -/
lemma frozenPb_le {c W Lt L0 : ℝ} {n : ℕ} (hc : 2 ≤ c) (hn1 : c ^ 6 ≤ (n : ℝ)) (hn2 : (n : ℝ) ≤ 2 * c ^ 6)
    (hW : 0 < W) (hW1 : 1 ≤ c ^ 2 * W) (hX : c ≤ 1 / (2 * W ^ 2) * (L0 - Lt) ^ 2)
    (hexp : Real.exp (-c) ≤ (c ^ 12)⁻¹) :
    hankelFrozenPb c 1 W Lt L0 n ≤ 30 * (c ^ 4)⁻¹ := by
  have hc0 : 0 < c := by linarith
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) hn1
  have hs1 : 1 ≤ √(2 * π) := by
    rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hs0 : 0 < √(2 * π) := by linarith
  -- `1/(√(2π) W) ≤ c²`
  have hinvW : 1 / W ≤ c ^ 2 := by rw [div_le_iff₀ hW]; linarith
  have hk : 1 / (√(2 * π) * W) ≤ c ^ 2 := by
    calc 1 / (√(2 * π) * W) ≤ 1 / (1 * W) :=
          one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hs1 hW.le)
      _ = 1 / W := by rw [one_mul]
      _ ≤ c ^ 2 := hinvW
  have hE : Real.exp (-(1 / (2 * W ^ 2)) * (L0 - Lt) ^ 2) ≤ (c ^ 12)⁻¹ := by
    refine le_trans (Real.exp_le_exp.2 ?_) hexp
    have : -(1 / (2 * W ^ 2)) * (L0 - Lt) ^ 2 = -(1 / (2 * W ^ 2) * (L0 - Lt) ^ 2) := by ring
    rw [this]; linarith
  have hc12 : 0 < (c ^ 12)⁻¹ := by positivity
  unfold hankelFrozenPb
  have t1 : (n : ℝ) * (1 * (Real.exp (-(1 / (2 * W ^ 2)) * (L0 - Lt) ^ 2) / (√(2 * π) * W))) ≤
      2 * (c ^ 4)⁻¹ := by
    have h1 : Real.exp (-(1 / (2 * W ^ 2)) * (L0 - Lt) ^ 2) / (√(2 * π) * W) ≤ (c ^ 12)⁻¹ * c ^ 2 := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hE hk (by positivity) hc12.le
    calc (n : ℝ) * (1 * (Real.exp (-(1 / (2 * W ^ 2)) * (L0 - Lt) ^ 2) / (√(2 * π) * W)))
        ≤ (2 * c ^ 6) * ((c ^ 12)⁻¹ * c ^ 2) := by
          rw [one_mul]; exact mul_le_mul hn2 h1 (by positivity) (by positivity)
      _ = 2 * (c ^ 4)⁻¹ := by field_simp
  have t2 : 2 / (n : ℝ) * (1 / (√(2 * π) * W)) ≤ 2 * (c ^ 4)⁻¹ := by
    have h1 : 2 / (n : ℝ) ≤ 2 * (c ^ 6)⁻¹ := by
      rw [div_le_iff₀ hn0]
      have : 2 * (c ^ 6)⁻¹ * c ^ 6 = 2 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hn1 (by positivity : (0 : ℝ) ≤ 2 * (c ^ 6)⁻¹)]
    calc 2 / (n : ℝ) * (1 / (√(2 * π) * W)) ≤ (2 * (c ^ 6)⁻¹) * c ^ 2 :=
          mul_le_mul h1 hk (by positivity) (by positivity)
      _ = 2 * (c ^ 4)⁻¹ := by field_simp
  have hsq : √(π / (2 * π ^ 2 * W ^ 2)) ≤ c ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : π / (2 * π ^ 2 * W ^ 2) ≤ (1 / W) ^ 2 := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_gt_three, sq_nonneg W, mul_pos Real.pi_pos (sq_nonneg W |>.lt_of_ne' (by positivity))]
    exact this.trans (pow_le_pow_left₀ (by positivity) hinvW 2)
  have t3 : 6 * (n : ℝ) * 1 * ((c ^ 20)⁻¹ * (1 + √(π / (2 * π ^ 2 * W ^ 2)))) ≤ 26 * (c ^ 4)⁻¹ := by
    have h1 : (c ^ 20)⁻¹ * (1 + √(π / (2 * π ^ 2 * W ^ 2))) ≤ (c ^ 20)⁻¹ * (1 + c ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 6 * (n : ℝ) * 1 ≤ 12 * c ^ 6 := by linarith
    calc 6 * (n : ℝ) * 1 * ((c ^ 20)⁻¹ * (1 + √(π / (2 * π ^ 2 * W ^ 2))))
        ≤ (12 * c ^ 6) * ((c ^ 20)⁻¹ * (1 + c ^ 2)) := mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = 12 * ((c ^ 14)⁻¹ + (c ^ 12)⁻¹) := by field_simp
      _ ≤ 26 * (c ^ 4)⁻¹ := by
          have a1 : (c ^ 14)⁻¹ ≤ (c ^ 4)⁻¹ := by
            apply inv_anti₀ (by positivity); exact pow_le_pow_right₀ (by linarith) (by norm_num)
          have a2 : (c ^ 12)⁻¹ ≤ (c ^ 4)⁻¹ := by
            apply inv_anti₀ (by positivity); exact pow_le_pow_right₀ (by linarith) (by norm_num)
          linarith
  rw [show (1 : ℝ) = 1 from rfl] at *
  have e1 : (1 : ℝ) * (√(2 * π) * W)⁻¹ = 1 / (√(2 * π) * W) := by ring
  linarith [t1, t2, t3]

end FormalResearch.SignUncertainty
