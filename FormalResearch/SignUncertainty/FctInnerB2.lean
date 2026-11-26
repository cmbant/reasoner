/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerSymbols

/-!
# `fct:inner-symbols` (b2): support, size and plateau of the inner cutoff `χ = χ_in(T/τ₁)`

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (b2).  With `T = T̃(s; L₁) = s V(Y)`, `s = 2^{-2/3} c^{-1/3} u`, `Y = 2^{-4/3} c^{-1/6} u²` and
`‖V - τ_*‖_∞ ≤ η = K c^{-1/2}`, `θ := 2^{-2/3} τ_* = (3/π²)^{1/3} ∈ [0.6723, 0.6724]`, so that `T/τ₁ = 2^{-2/3}(u/c^{1/12}) V(Y)`:

* `χ = 0` on `[2.95 c^{1/12}, U_c]` (`T/τ₁ ≥ 1.98`; the paper's `supp χ ⊂ [0, 2.95 c^{1/12}]`);
* `T(U_c) < 2 τ₁`, with `T(U_c)/τ₁ = 2.96 θ (1 + O(c^{-1/2})) = 1.9902…`;
* `1 - χ = 0` on `[0, u_*]` (`T/τ₁ ≤ 2.7 θ (1 + O(c^{-1/2})) = 1.8154… < 1.85`).

**Paper discrepancy.**  The paper writes `2^{-2/3} τ_* = 0.6714…`, `T(U_c) = 1.987… τ₁` and `T(U_c) < 1.99 τ₁`.  In fact `2^{-2/3} τ_* = 0.67237…` and
`T(U_c)/τ₁ → 1.9902…`, so `T(U_c) < 1.99 τ₁` fails at leading order (also `T = 1.98 τ₁` at `u = 2.9448 c^{1/12}` and `1.85 τ₁` at `2.7515 c^{1/12}`, not `2.949`, `2.755`).
All uses (support in `[0, 2.95 c^{1/12}]`, `T ≤ 2τ₁` on `[0, U_c]`, `χ = 1` on `[0, u_*]`) remain true, and these are what is proved.

`fctInnerB2_of_symbol` assembles (b2) from the proved clauses and the named symbol input `FctInnerB2Symbol`.

Class: proved (numerical constants are rigorous: `π` bounds from Mathlib, cube comparisons).
-/
@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma fctB2_pi_sq_bounds : (9.8696 : ℝ) < π ^ 2 ∧ π ^ 2 < 9.8697 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  constructor <;> nlinarith

/-- `θ = 2^{-2/3} τ_*`, `τ_* = (12/π²)^{1/3}`: `θ³ = 3/π²`. -/
lemma fctB2_theta_cube : ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (12 / π ^ 2) ^ (1 / 3 : ℝ)) ^ 3 = 3 / π ^ 2 := by
  have h1 : ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 3 = 1 / 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h2 : ((12 / π ^ 2) ^ (1 / 3 : ℝ)) ^ 3 = 12 / π ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  rw [mul_pow, h1, h2]; field_simp; ring

lemma fctB2_theta_bounds : (0.6723 : ℝ) ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (12 / π ^ 2) ^ (1 / 3 : ℝ) ∧
    (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (12 / π ^ 2) ^ (1 / 3 : ℝ) ≤ 0.6724 := by
  have hc := fctB2_theta_cube
  obtain ⟨hp1, hp2⟩ := fctB2_pi_sq_bounds
  have hpos : 0 < (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (12 / π ^ 2) ^ (1 / 3 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by positivity) _)
  set θ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (12 / π ^ 2) ^ (1 / 3 : ℝ)
  have hlo : 3 / 9.8697 ≤ θ ^ 3 := by
    rw [hc]; exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2.le
  have hhi : θ ^ 3 ≤ 3 / 9.8696 := by
    rw [hc]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp1.le
  constructor
  · by_contra h
    push Not at h
    have : θ ^ 3 < 0.6723 ^ 3 := pow_lt_pow_left₀ h hpos.le (by norm_num)
    norm_num at this hlo; linarith
  · by_contra h
    push Not at h
    have : 0.6724 ^ 3 < θ ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    norm_num at this hhi; linarith

lemma fctB2_two_rpow_neg23_le : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 0.63 := by
  have h3 : ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 3 = 1 / 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  by_contra h
  push Not at h
  have : (0.63 : ℝ) ^ 3 < ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [h3] at this; norm_num at this

lemma fctB2_two_rpow_neg43_le : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 0.3969 := by
  have h3 : ((2 : ℝ) ^ (-(4 / 3 : ℝ))) ^ 3 = 1 / 16 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  by_contra h
  push Not at h
  have : (0.3969 : ℝ) ^ 3 < ((2 : ℝ) ^ (-(4 / 3 : ℝ))) ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [h3] at this; norm_num at this

lemma fctB2_eta_small {K c : ℝ} (hc : (1000 * K) ^ 2 ≤ c) (hc1 : 1 ≤ c) : K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 := by
  have hc0 : 0 < c := by linarith
  have hs : 1000 * K ≤ √c := Real.le_sqrt_of_sq_le hc
  have hsp : 0 < √c := Real.sqrt_pos.2 hc0
  rw [Real.rpow_neg hc0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv, div_le_iff₀ hsp]
  linarith

/-- `T/τ₁ = 2^{-2/3} (u/x) V(Y)` and `Y = 2^{-4/3} (u/x)²`, `x = c^{1/12}`. -/
lemma fctB2_inner_ratio {c : ℝ} (hc : 0 < c) (V : ℝ → ℝ) (u : ℝ) :
    fctInnerT c V u / fctTau1 c = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (u / c ^ ((1 : ℝ) / 12)) *
      V ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * (u / c ^ ((1 : ℝ) / 12)) ^ 2) := by
  have hx : 0 < c ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos hc _
  have e1 : c ^ (-(1 / 3 : ℝ)) / c ^ (-(1 / 4 : ℝ)) = (c ^ ((1 : ℝ) / 12))⁻¹ := by
    rw [← Real.rpow_sub hc, ← Real.rpow_neg hc.le]; congr 1; norm_num
  have e2 : c ^ (-(1 / 6 : ℝ)) = ((c ^ ((1 : ℝ) / 12)) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_neg hc.le]; congr 1; norm_num
  unfold fctInnerT fctTau1
  have e3 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2 =
      (2 : ℝ) ^ (-(4 / 3 : ℝ)) * (u / c ^ ((1 : ℝ) / 12)) ^ 2 := by
    rw [e2, div_pow]; field_simp
  rw [e3]
  have hq : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc _
  have e4 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u / c ^ (-(1 / 4 : ℝ)) =
      (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (u / c ^ ((1 : ℝ) / 12)) := by
    calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u / c ^ (-(1 / 4 : ℝ))
        = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (u * (c ^ (-(1 / 3 : ℝ)) / c ^ (-(1 / 4 : ℝ)))) := by field_simp
      _ = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (u * (c ^ ((1 : ℝ) / 12))⁻¹) := by rw [e1]
      _ = _ := by rw [div_eq_mul_inv u (c ^ ((1 : ℝ) / 12))]
  rw [show (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u *
      V ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * (u / c ^ ((1 : ℝ) / 12)) ^ 2) / c ^ (-(1 / 4 : ℝ)) =
      ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u / c ^ (-(1 / 4 : ℝ))) *
      V ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * (u / c ^ ((1 : ℝ) / 12)) ^ 2) by ring, e4]

/-- **`fct:inner-symbols` (b2), support / size / plateau** (see the module docstring for the corrected constant `1.99 → 2`).  If `|V - τ_*| ≤ η = K c^{-1/2} ≤ 0.001` on
`[0, 3.6]` then `χ = 0` on `[2.95 c^{1/12}, U_c]`, `T(U_c) < 2 τ₁` and `1 - χ = 0` on `[0, u_*]`. -/
theorem fctInnerB2_numeric {χin : ℝ → ℝ} (hχ : FctCutoffIn χin) {c K : ℝ} (hc : 1 ≤ c) (hη : K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001)
    {V : ℝ → ℝ} (hV : ∀ Y ∈ Icc (0 : ℝ) 3.6, |V Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)| ≤ K * c ^ (-(1 / 2 : ℝ))) :
    (∀ u ∈ Icc (2.95 * c ^ ((1 : ℝ) / 12)) (fctUc c), fctInnerChi χin c V u = 0) ∧
    fctInnerT c V (fctUc c) < 2 * fctTau1 c ∧
    ∀ u ∈ Icc 0 (fctUstar c), 1 - fctInnerChi χin c V u = 0 := by
  have hc0 : 0 < c := by linarith
  set x : ℝ := c ^ ((1 : ℝ) / 12) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos hc0 _
  set r2 : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) with hr2
  set r4 : ℝ := (2 : ℝ) ^ (-(4 / 3 : ℝ)) with hr4
  set τs : ℝ := (12 / π ^ 2) ^ (1 / 3 : ℝ) with hτs
  set η : ℝ := K * c ^ (-(1 / 2 : ℝ)) with hηdef
  have hr2pos : 0 < r2 := Real.rpow_pos_of_pos (by norm_num) _
  have hr4pos : 0 < r4 := Real.rpow_pos_of_pos (by norm_num) _
  have hr2le : r2 ≤ 0.63 := fctB2_two_rpow_neg23_le
  have hr4le : r4 ≤ 0.3969 := fctB2_two_rpow_neg43_le
  obtain ⟨hθ1, hθ2⟩ := fctB2_theta_bounds
  have hη0 : 0 ≤ η := le_trans (abs_nonneg _) (hV 0 ⟨le_refl _, by norm_num⟩)
  have hrη : r2 * η ≤ 0.00063 := by
    calc r2 * η ≤ 0.63 * 0.001 := mul_le_mul hr2le hη hη0 (by norm_num)
      _ = 0.00063 := by norm_num
  have hτs_ge : η ≤ τs := by
    have : 0.6723 ≤ r2 * τs := hθ1
    have hτpos : 0 < τs := Real.rpow_pos_of_pos (by positivity) _
    nlinarith
  -- the value of `V` along `Y = r4 t²`
  have hVt : ∀ t : ℝ, 0 ≤ t → t ≤ 2.96 → |V (r4 * t ^ 2) - τs| ≤ η := by
    intro t ht0 ht1
    apply hV
    refine ⟨by positivity, ?_⟩
    have : t ^ 2 ≤ 2.96 ^ 2 := pow_le_pow_left₀ ht0 ht1 2
    nlinarith
  have hrat : ∀ u : ℝ, fctInnerT c V u / fctTau1 c = r2 * (u / x) * V (r4 * (u / x) ^ 2) := fun u => fctB2_inner_ratio hc0 V u
  -- bounds on `r2 t V`
  have hbd : ∀ t : ℝ, 0 ≤ t → t ≤ 2.96 → r2 * t * (τs - η) ≤ r2 * t * V (r4 * t ^ 2) ∧
      r2 * t * V (r4 * t ^ 2) ≤ r2 * t * (τs + η) := by
    intro t ht0 ht1
    have h := abs_le.1 (hVt t ht0 ht1)
    have h2 : 0 ≤ r2 * t := by positivity
    exact ⟨mul_le_mul_of_nonneg_left (by linarith [h.1]) h2, mul_le_mul_of_nonneg_left (by linarith [h.2]) h2⟩
  have hτ₁ : 0 < fctTau1 c := Real.rpow_pos_of_pos hc0 _
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    have hUc : fctUc c = 2.96 * x := rfl
    obtain ⟨hu1, hu2⟩ := hu
    rw [hUc] at hu2
    have ht1 : 2.95 ≤ u / x := by rw [le_div_iff₀ hxpos]; exact hu1
    have ht2 : u / x ≤ 2.96 := by rw [div_le_iff₀ hxpos]; exact hu2
    have h := (hbd (u / x) (by linarith) ht2).1
    have hge : 1.98 ≤ fctInnerT c V u / fctTau1 c := by
      rw [hrat u]
      refine le_trans ?_ h
      have e : r2 * (u / x) * (τs - η) = (u / x) * (r2 * τs) - (u / x) * (r2 * η) := by ring
      rw [e]
      nlinarith [mul_le_mul ht1 hθ1 (by norm_num) (by linarith), mul_le_mul_of_nonneg_left hrη (by linarith : (0 : ℝ) ≤ u / x)]
    unfold fctInnerChi
    apply hχ.zero
    rw [abs_of_nonneg (by linarith)]
    exact hge
  · have hUc : fctUc c = 2.96 * x := rfl
    have hu : fctUc c / x = 2.96 := by rw [hUc]; field_simp
    have h := (hbd 2.96 (by norm_num) le_rfl).2
    have hlt : fctInnerT c V (fctUc c) / fctTau1 c < 2 := by
      rw [hrat, hu]
      refine lt_of_le_of_lt h ?_
      have e : r2 * 2.96 * (τs + η) = 2.96 * (r2 * τs) + 2.96 * (r2 * η) := by ring
      rw [e]
      nlinarith
    exact (div_lt_iff₀ hτ₁).1 hlt
  · intro u hu
    obtain ⟨hu0, hu2⟩ := hu
    have hUs : fctUstar c = 2.7 * x := rfl
    rw [hUs] at hu2
    have ht0 : 0 ≤ u / x := by positivity
    have ht2 : u / x ≤ 2.7 := by rw [div_le_iff₀ hxpos]; exact hu2
    have h := hbd (u / x) ht0 (by linarith)
    have hlo : 0 ≤ fctInnerT c V u / fctTau1 c := by
      rw [hrat u]
      refine le_trans ?_ h.1
      have : 0 ≤ r2 * (u / x) := by positivity
      exact mul_nonneg this (by linarith)
    have hhi : fctInnerT c V u / fctTau1 c ≤ 1.85 := by
      rw [hrat u]
      refine le_trans h.2 ?_
      have e : r2 * (u / x) * (τs + η) = (u / x) * (r2 * τs) + (u / x) * (r2 * η) := by ring
      rw [e]
      nlinarith [mul_le_mul ht2 hθ2 (by linarith [hθ1]) (by norm_num), mul_le_mul_of_nonneg_left hrη ht0]
    unfold fctInnerChi
    rw [hχ.one _ (by rw [abs_of_nonneg hlo]; exact hhi)]
    ring

/-- **`fct:inner-symbols` (b2) assembled**: the full statement (support, `T(U_c) < 2τ₁`, `χ, 1 - χ ∈ 𝒮⁰(C)`, `1 - χ = 0` on `[0, u_*]`) from the named symbol input
`FctInnerB2Symbol`. -/
theorem fctInnerB2_of_symbol (h : FctInnerB2Symbol) {χin : ℝ → ℝ} (hχ : FctCutoffIn χin) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ V : ℝ → ℝ, FctVJets K c V →
      (∀ u ∈ Icc (2.95 * c ^ ((1 : ℝ) / 12)) (fctUc c), fctInnerChi χin c V u = 0) ∧
      fctInnerT c V (fctUc c) < 2 * fctTau1 c ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C (fun u => ((fctInnerChi χin c V u : ℝ) : ℂ)) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C (fun u => ((1 - fctInnerChi χin c V u : ℝ) : ℂ)) ∧
      ∀ u ∈ Icc 0 (fctUstar c), 1 - fctInnerChi χin c V u = 0 := by
  obtain ⟨C, c₁, hC⟩ := h χin hχ K hK
  refine ⟨C, max (max c₁ 1) ((1000 * K) ^ 2), fun c hc V hV => ?_⟩
  have hc1 : c₁ ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have hc2 : 1 ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have hc3 : (1000 * K) ^ 2 ≤ c := le_trans (le_max_right _ _) hc
  have hη := fctB2_eta_small hc3 hc2
  have hVb : ∀ Y ∈ Icc (0 : ℝ) 3.6, |V Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)| ≤ K * c ^ (-(1 / 2 : ℝ)) := by
    intro Y hY
    have := hV.2 0 (by norm_num) Y hY
    rwa [iteratedDerivWithin_zero] at this
  obtain ⟨h1, h2, h3⟩ := fctInnerB2_numeric hχ hc2 hη hVb
  obtain ⟨h4, h5⟩ := hC c hc1 V hV
  exact ⟨h1, h2, h4, h5, h3⟩

/-- info: 'FormalResearch.SignUncertainty.fctInnerB2_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerB2_numeric

/-- info: 'FormalResearch.SignUncertainty.fctInnerB2_of_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerB2_of_symbol

end FormalResearch.SignUncertainty
