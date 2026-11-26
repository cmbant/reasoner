/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymChain
public import FormalResearch.SignUncertainty.CtMDeriv

/-!
# Exponentially decaying `t`-symbols (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b); `|H_*(it)|, |H_CE(it)| = O(e^{-πt})`.

* `pow_le_exp`: `(1+x)^N ≤ C_N e^{πx/2}` for `x ≥ 0`;
* `expNeg_symW`: `e^{-πx} ∈ SymW (0, ∞) (e^{-πx/2})`;
* `symW_comp_expNeg`: for `Φ` smooth on `(-1, 1)` with `|Φ(y)| ≤ L y` on `[0, e^{-π/8}]`, `Φ(e^{-πx}) ∈ SymW [1/8, ∞) (e^{-πx/2})`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff Real Nat

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty

/-- `(1 + x)^N ≤ C e^{πx/2}` for `x ≥ 0`. -/
lemma pow_le_exp (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ N ≤ C * Real.exp (π * x / 2) := by
  set a : ℝ := π / (2 * ((N : ℝ) + 1)) with ha
  have ha0 : 0 < a := by positivity
  refine ⟨(1 + a⁻¹) ^ N, by positivity, fun x hx => ?_⟩
  have h1 : 1 + x ≤ (1 + a⁻¹) * (1 + a * x) := by
    have : a⁻¹ * (a * x) = x := by field_simp
    nlinarith [mul_nonneg ha0.le hx, inv_nonneg.mpr ha0.le, this]
  have h2 : (1 + a * x) ^ N ≤ (1 + a * x) ^ (N + 1) :=
    pow_le_pow_right₀ (by nlinarith [mul_nonneg ha0.le hx]) (Nat.le_succ N)
  have h3 : (1 + a * x) ^ (N + 1) ≤ Real.exp (π * x / 2) := by
    have := pow_le_pow_left₀ (by nlinarith [mul_nonneg ha0.le hx]) (Real.add_one_le_exp (a * x)) (N + 1)
    refine (le_trans (by rw [add_comm]) this).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    rw [ha]; push_cast; field_simp
  calc (1 + x) ^ N ≤ ((1 + a⁻¹) * (1 + a * x)) ^ N := pow_le_pow_left₀ (by linarith) h1 N
    _ = (1 + a⁻¹) ^ N * (1 + a * x) ^ N := mul_pow _ _ _
    _ ≤ (1 + a⁻¹) ^ N * Real.exp (π * x / 2) := by gcongr; exact h2.trans h3

/-- `(πx)^r e^{-πx/2} ≤ K_r` for `x ≥ 0`. -/
lemma pow_mul_exp_neg_le (r : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → (π * x) ^ r * Real.exp (-(π * x / 2)) ≤ K := by
  obtain ⟨C, hC, h⟩ := pow_le_exp r
  refine ⟨π ^ r * C, by positivity, fun x hx => ?_⟩
  have h1 : (π * x) ^ r ≤ π ^ r * (C * Real.exp (π * x / 2)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hx (by linarith) r).trans (h x hx)) (by positivity)
  calc (π * x) ^ r * Real.exp (-(π * x / 2)) ≤ (π ^ r * (C * Real.exp (π * x / 2))) * Real.exp (-(π * x / 2)) := by
        gcongr
    _ = π ^ r * C := by
      rw [mul_assoc, mul_assoc, mul_comm (Real.exp _), ← mul_assoc C, mul_assoc C, ← Real.exp_add]
      simp

/-- **`e^{-πx}` is a `t`-symbol of weight `e^{-πx/2}` on `(0, ∞)`.** -/
lemma expNeg_symW : ∃ K : ℕ → ℝ, SymW (Ioi (0 : ℝ)) (fun x => Real.exp (-(π * x / 2))) K (fun x => Real.exp (-π * x)) := by
  choose K hK0 hK using pow_mul_exp_neg_le
  refine ⟨K, ?_⟩
  exact
  { pos := fun x hx => hx
    smooth := ⟨univ, isOpen_univ, subset_univ _, (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn⟩
    K_nonneg := hK0
    w_nonneg := fun x _ => (Real.exp_pos _).le
    bound := fun r x hx => by
      have hx0 : 0 < x := hx
      rw [iteratedDeriv_exp_const_mul, abs_mul, abs_pow, abs_neg, abs_of_pos Real.pi_pos, abs_of_pos (Real.exp_pos _)]
      have h := hK r x hx0.le
      have hxr : 0 < x ^ r := pow_pos hx0 r
      have e1 : Real.exp (-π * x) = Real.exp (-(π * x / 2)) * Real.exp (-(π * x / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc π ^ r * Real.exp (-π * x) = ((π * x) ^ r * Real.exp (-(π * x / 2))) * Real.exp (-(π * x / 2)) * (x ^ r)⁻¹ := by
            rw [e1, mul_pow]; field_simp
        _ ≤ K r * Real.exp (-(π * x / 2)) * (x ^ r)⁻¹ := by gcongr }

/-- **`Φ(e^{-πx})` for a smooth `Φ` with `|Φ(y)| ≤ L y` near `0`** is a `t`-symbol of weight `e^{-πx/2}` on `[1/8, ∞)`. -/
theorem symW_comp_expNeg {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (Ioo (-1) 1)) {L : ℝ} (hL : 0 ≤ L)
    (hΦL : ∀ y ∈ Icc (0 : ℝ) (Real.exp (-π / 8)), |Φ y| ≤ L * y) :
    ∃ K : ℕ → ℝ, SymW (Ici (1 / 8 : ℝ)) (fun x => Real.exp (-(π * x / 2))) K (fun x => Φ (Real.exp (-π * x))) := by
  obtain ⟨K₁, hK₁⟩ := expNeg_symW
  have hu0 : Real.exp (-π / 8) < 1 := by
    rw [Real.exp_lt_one_iff]; have := Real.pi_pos; linarith
  have hcpt : Icc (0 : ℝ) (Real.exp (-π / 8)) ⊆ Ioo (-1) 1 := fun y hy => ⟨by linarith [hy.1], lt_of_le_of_lt hy.2 hu0⟩
  choose B hB using fun j => CtMDeriv.bdd_iter_on_compact (isOpen_Ioo (a := (-1 : ℝ)) (b := 1)) hΦ
    (isCompact_Icc (a := (0 : ℝ)) (b := Real.exp (-π / 8))) hcpt j
  have hS : ∀ x ∈ Ici (1 / 8 : ℝ), Real.exp (-π * x) ∈ Icc (0 : ℝ) (Real.exp (-π / 8)) := by
    intro x hx
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩
    have : (1 / 8 : ℝ) ≤ x := hx
    nlinarith [Real.pi_pos]
  have hmain := SymW.comp_smooth (S := Ici (1 / 8 : ℝ)) (w := fun x => Real.exp (-(π * x / 2))) (B := 1) (L := L)
    (P := fun j => |B j|) (V := Ioo (-1) 1) (hK₁.mono_set (fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx)))
    isOpen_Ioo hΦ (fun x hx => hcpt (hS x hx)) (fun j x hx => (hB j _ (hS x hx)).trans (le_abs_self _)) (fun j => abs_nonneg _)
    (fun x hx => by
      have : (1 / 8 : ℝ) ≤ x := hx
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]) hL
    (fun x hx => by
      refine (hΦL _ (hS x hx)).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hL
      have : (1 / 8 : ℝ) ≤ x := hx
      nlinarith [Real.pi_pos])
  exact ⟨_, hmain⟩

end FormalResearch.SignUncertainty.FctSym
