/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWeighted
public import FormalResearch.SignUncertainty.FctJC
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Building blocks of `(fct:dJ-jets)` (F2a, `fct:comp-cfu`)

* `weighted_leibniz`: the weighted Leibniz bound `|∂^n (f g)(Y)| ≤ C β_f M W^{max(0,u+w-n)}`, `W = max(Y, A) ≤ 4`, for `f` with
  the weights `|∂^k f(Y)| ≤ β_f W^{max(0,u-k)}` and `g` with the weights `|∂^k g(Y)| ≤ M W^{max(0,w-k)}`
  (a generalisation of `weighted_monomial` to a weighted first factor; the exponents `u - k` are `ℕ`-truncated);
* `rpowHalf_jc`: `x ↦ x^{1/2} = √x` is `C^k` with all derivatives of order `≤ k` bounded on `(m, M)`, `m > 0`
  (`JC`), the square roots of `J` in `(fct:dJ-jets)`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace FormalResearch.SignUncertainty

section DJetBase

lemma pow_le_four_pow_mul {W : ℝ} (h0 : 0 ≤ W) (h4 : W ≤ 4) {e1 e2 : ℕ} (h : e2 ≤ e1) :
    W ^ e1 ≤ 4 ^ e1 * W ^ e2 := by
  have h1 : W ^ (e1 - e2) ≤ 4 ^ (e1 - e2) := by gcongr
  have h2 : (4 : ℝ) ^ (e1 - e2) ≤ 4 ^ e1 := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : 0 ≤ W ^ e2 := by positivity
  calc W ^ e1 = W ^ (e1 - e2) * W ^ e2 := by rw [← pow_add]; congr 1; omega
    _ ≤ 4 ^ e1 * W ^ e2 := by gcongr; exact h1.trans h2

/-- Weighted Leibniz bound for a product of two weighted functions. -/
lemma weighted_leibniz {n u w : ℕ} {f g : ℝ → ℝ} {Y A βf M : ℝ} (hY : 0 ≤ Y) (hY4 : Y ≤ 4)
    (hA4 : A ≤ 4) (hf : ContDiffAt ℝ n f Y) (hg : ContDiffAt ℝ n g Y) (hβf : 0 ≤ βf) (hM : 0 ≤ M)
    (hfb : ∀ k ≤ n, |iteratedDeriv k f Y| ≤ βf * max Y A ^ (u - k))
    (hgb : ∀ k ≤ n, |iteratedDeriv k g Y| ≤ M * max Y A ^ (w - k)) :
    |iteratedDeriv n (fun s => f s * g s) Y| ≤ (n + 1) * 2 ^ n * 4 ^ (u + w) * βf * M * max Y A ^ (u + w - n) := by
  rw [iteratedDeriv_fun_mul hf hg]
  set W := max Y A with hW
  have hW0 : 0 ≤ W := le_max_of_le_left hY
  have hW4 : W ≤ 4 := max_le hY4 hA4
  have hterm : ∀ i ∈ Finset.range (n + 1), |(n.choose i : ℝ) * iteratedDeriv i f Y * iteratedDeriv (n - i) g Y| ≤
      2 ^ n * 4 ^ (u + w) * βf * M * W ^ (u + w - n) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : (n.choose i : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.choose_le_two_pow n i)
    have hfi := hfb i hin
    have hgi := hgb (n - i) (Nat.sub_le n i)
    have hexp : u + w - n ≤ (u - i) + (w - (n - i)) := by omega
    have hsh := pow_le_four_pow_mul hW0 hW4 hexp
    have h42 : (4 : ℝ) ^ ((u - i) + (w - (n - i))) ≤ 4 ^ (u + w) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hc0 : (0 : ℝ) ≤ n.choose i := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hc0]
    have hWu : 0 ≤ W ^ (u - i) := by positivity
    have hWw : 0 ≤ W ^ (w - (n - i)) := by positivity
    calc (n.choose i : ℝ) * |iteratedDeriv i f Y| * |iteratedDeriv (n - i) g Y|
        ≤ 2 ^ n * (βf * W ^ (u - i)) * (M * W ^ (w - (n - i))) := by
          gcongr
      _ = 2 ^ n * βf * M * W ^ ((u - i) + (w - (n - i))) := by rw [pow_add]; ring
      _ ≤ 2 ^ n * βf * M * (4 ^ (u + w) * W ^ (u + w - n)) := by
          gcongr
          exact hsh.trans (by gcongr)
      _ = _ := by ring
  calc |∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * iteratedDeriv i f Y * iteratedDeriv (n - i) g Y|
      ≤ ∑ i ∈ Finset.range (n + 1), |(n.choose i : ℝ) * iteratedDeriv i f Y * iteratedDeriv (n - i) g Y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), 2 ^ n * 4 ^ (u + w) * βf * M * W ^ (u + w - n) := Finset.sum_le_sum hterm
    _ = _ := by simp; ring

lemma descPochhammer_le {r : ℝ} (hr1 : -1 ≤ r) (hr2 : r ≤ 1) (k : ℕ) :
    |(descPochhammer ℝ k).eval r| ≤ k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_natCast, abs_mul, Nat.factorial_succ]
    have h : |r - k| ≤ k + 1 := by
      rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    push_cast
    calc _ ≤ (k.factorial : ℝ) * (k + 1) := mul_le_mul ih h (abs_nonneg _) (by positivity)
      _ = _ := by ring

lemma rpow_le_max {x r : ℝ} (hx : 0 < x) (hr1 : -1 ≤ r) (hr2 : r ≤ 1) : x ^ r ≤ max x x⁻¹ := by
  by_cases hx1 : 1 ≤ x
  · calc x ^ r ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hr2
      _ = x := Real.rpow_one x
      _ ≤ _ := le_max_left _ _
  · push Not at hx1
    calc x ^ r ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx hx1.le hr1
      _ = x⁻¹ := Real.rpow_neg_one x
      _ ≤ _ := le_max_right _ _

/-- `x ↦ x^r` (`-1 ≤ r ≤ 1`) is `C^k` with bounded derivatives of order `≤ k` on `(m, M)`, `0 < m`. -/
lemma rpow_jc (k : ℕ) {r m M : ℝ} (hr1 : -1 ≤ r) (hr2 : r ≤ 1) (hm : 0 < m) :
    JC k (Ioo m M) (fun x : ℝ => x ^ r) (k.factorial * (max 1 M * max 1 m⁻¹) * (max 1 m⁻¹) ^ k) := by
  have hT : IsOpen (Ioo m M) := isOpen_Ioo
  refine ⟨fun x hx => (Real.contDiffAt_rpow_const_of_ne (n := k) (p := r) (lt_trans hm hx.1).ne').contDiffWithinAt, ?_⟩
  intro i hi x hx
  have hx0 : 0 < x := lt_trans hm hx.1
  rw [iteratedFDerivWithin_of_isOpen i hT hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, Real.norm_eq_abs, abs_mul]
  have h1 := descPochhammer_le hr1 hr2 i
  have hR : (1 : ℝ) ≤ max 1 m⁻¹ := le_max_left _ _
  have h2 : |x ^ (r - i)| ≤ (max 1 M * max 1 m⁻¹) * (max 1 m⁻¹) ^ k := by
    rw [abs_of_pos (Real.rpow_pos_of_pos hx0 _), Real.rpow_sub hx0, Real.rpow_natCast]
    have hxi : x⁻¹ ≤ max 1 m⁻¹ := (inv_anti₀ hm hx.1.le).trans (le_max_right _ _)
    have hs : x ^ r ≤ max 1 M * max 1 m⁻¹ := by
      refine (rpow_le_max hx0 hr1 hr2).trans (max_le ?_ ?_)
      · calc x ≤ max 1 M := hx.2.le.trans (le_max_right _ _)
          _ = max 1 M * 1 := (mul_one _).symm
          _ ≤ _ := by gcongr
      · calc x⁻¹ ≤ max 1 m⁻¹ := hxi
          _ = 1 * max 1 m⁻¹ := (one_mul _).symm
          _ ≤ _ := by gcongr; exact le_max_left _ _
    have hi' : (x ^ i)⁻¹ ≤ (max 1 m⁻¹) ^ k := by
      rw [← inv_pow]
      calc (x⁻¹) ^ i ≤ (max 1 m⁻¹) ^ i := by gcongr
        _ ≤ (max 1 m⁻¹) ^ k := pow_le_pow_right₀ hR hi
    rw [div_eq_mul_inv]
    exact mul_le_mul hs hi' (by positivity) (by positivity)
  have h3 : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
  calc _ ≤ (k.factorial : ℝ) * ((max 1 M * max 1 m⁻¹) * (max 1 m⁻¹) ^ k) :=
        mul_le_mul (h1.trans h3) h2 (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.weighted_leibniz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weighted_leibniz

/-- info: 'FormalResearch.SignUncertainty.rpow_jc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rpow_jc

end DJetBase
end FormalResearch.SignUncertainty
