/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymDerivComp
public import FormalResearch.SignUncertainty.FctTauA
public import FormalResearch.SignUncertainty.FctVacuumPointwise

/-!
# The phase `m = uctM` for `t ≥ 1/8`: `1/m` and `m^{3/2}` as `t`-symbols (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b); `m(t) = ℓ(πt/2)`.

For `t ≥ 1/8` one has `m ≥ m(1/8) > 0` and `|m^{(k)}| ≤ C_k t^{-k}` (`k ≥ 1`, `m_iter_bound`) while `m` itself grows like `log t`.

* `uctM_deriv_symbol`: `|∂^k m'(t)| ≤ A_k t^{-(k+1)}` for `t > 0` (the hypothesis of `comp_deriv_bound` for `f = m`);
* `mInv_symW`: `1/m ∈ SymW [1/8, ∞) 1`;
* `mPow32_symW`: `m^{3/2} ∈ SymW [1/8, ∞) (m^{3/2})`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff Real Nat

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

/-- `|∂^k m'(t)| ≤ A_k t^{-(k+1)}` for `t > 0`, from `mPrime_symW`. -/
lemma uctM_deriv_symbol : ∃ A : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧
    ∀ k x, 0 < x → |iteratedDeriv k (deriv uctM) x| ≤ A k * 1 * (x ^ (k + 1))⁻¹ := by
  obtain ⟨K, hK⟩ := mPrime_symW
  refine ⟨K, hK.K_nonneg, fun k x hx => ?_⟩
  have hev : deriv uctM =ᶠ[nhds x] mPrime := by
    filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mpr hx)] with u hu
    exact (hasDerivAt_uctM' hu).deriv
  rw [hev.iteratedDeriv_eq k]
  have h := hK.bound k x hx
  refine h.trans ?_
  have hx1 : (1 + x)⁻¹ ≤ x⁻¹ := inv_anti₀ hx (by linarith)
  have hkn : 0 ≤ K k := hK.K_nonneg k
  have hxk : 0 ≤ (x ^ k)⁻¹ := inv_nonneg.mpr (pow_nonneg hx.le k)
  calc K k * (1 + x)⁻¹ * (x ^ k)⁻¹ ≤ K k * x⁻¹ * (x ^ k)⁻¹ := by gcongr
    _ = K k * 1 * (x ^ (k + 1))⁻¹ := by rw [pow_succ', mul_inv, mul_one, mul_assoc]

lemma uctM_ge_of_ge {x : ℝ} (hx : 1 / 8 ≤ x) : uctM (1 / 8) ≤ uctM x := (uct_m_lower_large).2 x hx

lemma mL_pos : 0 < uctM (1 / 8) := uctM_pos (by norm_num)

/-- **`1/m` is a `t`-symbol of weight `1` on `[1/8, ∞)`.** -/
theorem mInv_symW : ∃ K : ℕ → ℝ, SymW (Ici (1 / 8 : ℝ)) (fun _ => 1) K (fun x => (uctM x)⁻¹) := by
  obtain ⟨A, hA0, hA⟩ := uctM_deriv_symbol
  set m₀ := uctM (1 / 8) with hm₀
  have hm0 : 0 < m₀ := mL_pos
  have hΦ : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Ioi 0) := (contDiffOn_inv ℝ).mono (fun y hy => (ne_of_gt hy : y ≠ 0))
  have hP : ∀ j x, x ∈ Ici (1 / 8 : ℝ) →
      |iteratedDeriv j (fun y : ℝ => y⁻¹) (uctM x)| ≤ ((j ! : ℝ) / m₀ ^ (j + 1)) * 1 := by
    intro j x hx
    have hx' : 1 / 8 ≤ x := hx
    have hmx := uctM_ge_of_ge hx'
    have hp : 0 < uctM x := lt_of_lt_of_le hm0 hmx
    rw [iteratedDeriv_inv_of_pos j hp, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
      abs_of_pos (inv_pos.mpr (pow_pos hp _)), mul_one, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hm0 _) (pow_le_pow_left₀ hm0.le hmx _)) (by positivity)
  have hmain := comp_deriv_bound (S := Ici (1 / 8 : ℝ)) (U := Ioi 0) isOpen_Ioi
    (fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx))
    (fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx)) contDiffOn_uctM isOpen_Ioi hΦ
    (fun x hx => uctM_pos hx) (fun k x hx => hA k x (lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx))) hA0
    (fun j => by positivity) (fun _ _ => zero_le_one) hP
  refine ⟨fun i => chainM (fun j => (j ! : ℝ) / m₀ ^ (j + 1)) (fun _ => 0) A 1 i 0, ?_⟩
  exact
  { pos := fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx)
    smooth := ⟨Ioi 0, isOpen_Ioi, fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx),
      hΦ.comp contDiffOn_uctM (fun x hx => uctM_pos hx)⟩
    K_nonneg := fun i => chainM_nonneg (fun j => by positivity) i 0
    w_nonneg := fun _ _ => zero_le_one
    bound := fun i x hx => by simpa using hmain i x hx }

/-- **`m^{3/2}` is a `t`-symbol of weight `m^{3/2}` on `[1/8, ∞)`.** -/
theorem mPow32_symW : ∃ K : ℕ → ℝ,
    SymW (Ici (1 / 8 : ℝ)) (fun x => uctM x ^ (3 / 2 : ℝ)) K (fun x => uctM x ^ (3 / 2 : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := uctM_deriv_symbol
  set m₀ := uctM (1 / 8) with hm₀
  have hm0 : 0 < m₀ := mL_pos
  have hΦ : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (3 / 2 : ℝ)) (Ioi 0) := fun y hy =>
    (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hy)).contDiffWithinAt
  set Pj : ℕ → ℝ := fun j => (∏ i ∈ range j, |(3 / 2 : ℝ) - (i : ℝ)|) * (m₀ ^ j)⁻¹ with hPj
  have hPj0 : ∀ j, 0 ≤ Pj j := fun j => by
    have : 0 ≤ ∏ i ∈ range j, |(3 / 2 : ℝ) - (i : ℝ)| := Finset.prod_nonneg fun i _ => abs_nonneg _
    rw [hPj]; positivity
  have hP : ∀ j x, x ∈ Ici (1 / 8 : ℝ) →
      |iteratedDeriv j (fun y : ℝ => y ^ (3 / 2 : ℝ)) (uctM x)| ≤ Pj j * uctM x ^ (3 / 2 : ℝ) := by
    intro j x hx
    have hx' : 1 / 8 ≤ x := hx
    have hmx := uctM_ge_of_ge hx'
    have hp : 0 < uctM x := lt_of_lt_of_le hm0 hmx
    have e := SymW.iteratedDeriv_rpow_sub (3 / 2 : ℝ) 0 j (show (0 : ℝ) < uctM x from hp)
    simp only [sub_zero] at e
    rw [e, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp _), Finset.abs_prod, Real.rpow_sub_natCast hp.ne',
      div_eq_mul_inv]
    have h1 : (uctM x ^ j)⁻¹ ≤ (m₀ ^ j)⁻¹ := inv_anti₀ (pow_pos hm0 _) (pow_le_pow_left₀ hm0.le hmx _)
    have h2 : 0 ≤ ∏ i ∈ range j, |(3 / 2 : ℝ) - (i : ℝ)| := Finset.prod_nonneg fun i _ => abs_nonneg _
    have h3 : 0 ≤ uctM x ^ (3 / 2 : ℝ) := (Real.rpow_pos_of_pos hp _).le
    rw [hPj]
    calc (∏ i ∈ range j, |(3 / 2 : ℝ) - (i : ℝ)|) * (uctM x ^ (3 / 2 : ℝ) * (uctM x ^ j)⁻¹)
        ≤ (∏ i ∈ range j, |(3 / 2 : ℝ) - (i : ℝ)|) * (uctM x ^ (3 / 2 : ℝ) * (m₀ ^ j)⁻¹) := by gcongr
      _ = _ := by ring_nf
  have hmain := comp_deriv_bound (S := Ici (1 / 8 : ℝ)) (U := Ioi 0) isOpen_Ioi
    (fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx))
    (fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx)) contDiffOn_uctM isOpen_Ioi hΦ
    (fun x hx => uctM_pos hx) (fun k x hx => hA k x (lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx))) hA0
    hPj0 (fun x hx => (Real.rpow_pos_of_pos (uctM_pos (lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx))) _).le) hP
  refine ⟨fun i => chainM Pj (fun _ => 0) A 1 i 0, ?_⟩
  exact
  { pos := fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx)
    smooth := ⟨Ioi 0, isOpen_Ioi, fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx),
      hΦ.comp contDiffOn_uctM (fun x hx => uctM_pos hx)⟩
    K_nonneg := fun i => chainM_nonneg hPj0 i 0
    w_nonneg := fun x hx => (Real.rpow_pos_of_pos (uctM_pos (lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx))) _).le
    bound := fun i x hx => hmain i x hx }

end FormalResearch.SignUncertainty.FctSym
