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

**Paper constant (corrected in the paper, `CORRECTIONS.md` 2026-11-26).**  The paper had `2^{-2/3} τ_* = 0.6714…`, `T(U_c) = 1.987… τ₁` and `T(U_c) < 1.99 τ₁`; it now states `T(U_c) < 2τ₁`.  In fact `2^{-2/3} τ_* = 0.67237…` and
`T(U_c)/τ₁ → 1.9902…`, so `T(U_c) < 1.99 τ₁` fails at leading order (also `T = 1.98 τ₁` at `u = 2.9448 c^{1/12}` and `1.85 τ₁` at `2.7515 c^{1/12}`, not `2.949`, `2.755`).
All uses (support in `[0, 2.95 c^{1/12}]`, `T ≤ 2τ₁` on `[0, U_c]`, `χ = 1` on `[0, u_*]`) remain true, and these are what is proved.

`fctInnerB2Symbol` (Faà di Bruno, `χ, 1 - χ ∈ 𝒮⁰(C)` on `[0, U_c]`) and `fctInnerB2` (all clauses of (b2)) are proved.

Class: proved (numerical constants are rigorous: `π` bounds from Mathlib, cube comparisons).
-/
@[expose] public section

open Set Filter Topology
open scoped Real ContDiff

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

/-! ### Faà di Bruno for `χ_in(T/τ₁)` (the symbol part of (b2))

`T/τ₁ = G(c^{-1/12} u)` with `G(x) = 2^{-2/3} x V(2^{-4/3} x²)`.  `G` has `C^8` norms `≤ B(K)` on `[0, 2.96]` (Leibniz and `norm_iteratedFDerivWithin_comp_le`
for `x ↦ V(2^{-4/3} x²)`), `χ_in ∘ G` has `C^8` norms `≤ B'(K)` there (`norm_iteratedFDerivWithin_comp_le` again), and `u ↦ c^{-1/12} u` multiplies
the `r`-th derivative by `c^{-r/12} ≤ 4^r (1+u)^{-r}` on `[0, U_c]`. -/

lemma fctB2_affine_norm (a : ℝ) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x ∈ s) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDerivWithin ℝ i (fun y : ℝ => a * y) s x‖ ≤ |a| ^ i := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [iteratedDerivWithin_succ']
  have h : EqOn (derivWithin (fun y : ℝ => a * y) s) (fun _ => a) s := fun y hy => by
    have hd : HasDerivAt (fun y : ℝ => a * y) a y := by simpa using (hasDerivAt_id y).const_mul a
    exact hd.hasDerivWithinAt.derivWithin (hs y hy)
  rw [iteratedDerivWithin_congr h hx, iteratedDerivWithin_const]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, norm_zero]; positivity

/-- A fixed smooth function has bounded derivatives on a compact set. -/
lemma fctB2_fixed_bound {f : ℝ → ℝ} {s : Set ℝ} (hc : IsCompact s) (hu : UniqueDiffOn ℝ s)
    (hf : ContDiffOn ℝ 8 f s) : ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, i ≤ 8 → ∀ x ∈ s, ‖iteratedFDerivWithin ℝ i f s x‖ ≤ D := by
  have hb : ∀ i : ℕ, ∃ B : ℝ, i ≤ 8 → ∀ x ∈ s, ‖iteratedFDerivWithin ℝ i f s x‖ ≤ B := by
    intro i
    by_cases hi : i ≤ 8
    · obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn
        (hf.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast hi) hu)
      exact ⟨B, fun _ x hx => hB x hx⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose B hB using hb
  refine ⟨1 + ∑ i ∈ Finset.range 9, |B i|, by
    have : 0 ≤ ∑ i ∈ Finset.range 9, |B i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith, fun i hi x hx => ?_⟩
  have h1 : |B i| ≤ ∑ j ∈ Finset.range 9, |B j| :=
    Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  linarith [hB i hi x hx, le_abs_self (B i)]


/-- Stage 1: the inner phase `G(x) = 2^{-2/3} x V(2^{-4/3} x²)` has `‖G^{(i)}‖ ≤ B_G` on `[0, 2.96]`. -/
lemma fctB2_G_bound (K : ℝ) (hK : 0 ≤ K) : ∃ B : ℝ, 1 ≤ B ∧ ∀ V : ℝ → ℝ, ContDiffOn ℝ 8 V (Icc (0 : ℝ) 3.6) →
    (∀ j : ℕ, j ≤ 8 → ∀ Y ∈ Icc (0 : ℝ) 3.6, ‖iteratedFDerivWithin ℝ j V (Icc (0 : ℝ) 3.6) Y‖ ≤ K) →
    ContDiffOn ℝ 8 (fun x : ℝ => (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (x * V ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * x ^ 2))) (Icc (0 : ℝ) 2.96) ∧
    ∀ i : ℕ, i ≤ 8 → ∀ x ∈ Icc (0 : ℝ) 2.96,
      ‖iteratedFDerivWithin ℝ i (fun x : ℝ => (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (x * V ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * x ^ 2))) (Icc (0 : ℝ) 2.96) x‖ ≤ B := by
  set s : Set ℝ := Icc (0 : ℝ) 2.96 with hs
  set t : Set ℝ := Icc (0 : ℝ) 3.6 with ht
  set m : ℝ := (2 : ℝ) ^ (-(4 / 3 : ℝ)) with hm
  set k : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) with hk
  have hsu : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by norm_num)
  have htu : UniqueDiffOn ℝ t := uniqueDiffOn_Icc (by norm_num)
  have hm0 : 0 < m := Real.rpow_pos_of_pos (by norm_num) _
  have hmle : m ≤ 0.3969 := fctB2_two_rpow_neg43_le
  have hk0 : 0 < k := Real.rpow_pos_of_pos (by norm_num) _
  have hq : ContDiff ℝ ∞ (fun x : ℝ => m * x ^ 2) := contDiff_const.mul (contDiff_id.pow 2)
  obtain ⟨Dq, hDq1, hDq⟩ := fctB2_fixed_bound (f := fun x : ℝ => m * x ^ 2) isCompact_Icc hsu
    (hq.contDiffOn.of_le (by simp))
  obtain ⟨Di, hDi1, hDi⟩ := fctB2_fixed_bound (f := fun x : ℝ => x) isCompact_Icc hsu contDiffOn_id
  have hqs : ContDiffOn ℝ 8 (fun x : ℝ => m * x ^ 2) s := hq.contDiffOn.of_le (by simp)
  have hmaps : MapsTo (fun x : ℝ => m * x ^ 2) s t := by
    intro x hx
    obtain ⟨h0, h1⟩ := hx
    refine ⟨by positivity, ?_⟩
    have h2 : x ^ 2 ≤ 2.96 ^ 2 := pow_le_pow_left₀ h0 h1 2
    have h3 : m * x ^ 2 ≤ 0.3969 * 2.96 ^ 2 := mul_le_mul hmle h2 (sq_nonneg x) (by norm_num)
    linarith
  set BW : ℝ := (Nat.factorial 8 : ℝ) * K * Dq ^ 8 with hBW
  have hBW0 : 0 ≤ BW := by positivity
  set BA : ℝ := 2 ^ 8 * Di * BW with hBA
  have hBA0 : 0 ≤ BA := by have : 0 ≤ Di := by linarith
                           positivity
  refine ⟨1 + k * BA, by have : 0 ≤ k * BA := by positivity
                         linarith, fun V hV hb => ?_⟩
  have hW : ContDiffOn ℝ 8 (fun x : ℝ => V (m * x ^ 2)) s := hV.comp hqs hmaps
  have hWb : ∀ i : ℕ, i ≤ 8 → ∀ x ∈ s, ‖iteratedFDerivWithin ℝ i (fun x : ℝ => V (m * x ^ 2)) s x‖ ≤ BW := by
    intro i hi x hx
    have h := norm_iteratedFDerivWithin_comp_le (g := V) (f := fun x : ℝ => m * x ^ 2) (n := i) (N := 8) hV hqs
      (by exact_mod_cast hi) htu hsu hmaps hx (C := K) (D := Dq)
      (fun j hj => hb j (hj.trans hi) _ (hmaps hx))
      (fun j hj1 hji => (hDq j (hji.trans hi) x hx).trans (le_self_pow₀ hDq1 (by omega)))
    refine h.trans ?_
    have h1 : (Nat.factorial i : ℝ) ≤ Nat.factorial 8 := by exact_mod_cast Nat.factorial_le hi
    have h2 : Dq ^ i ≤ Dq ^ 8 := pow_le_pow_right₀ hDq1 hi
    have hK' : 0 ≤ K := hK
    rw [hBW]
    gcongr
  have hA : ContDiffOn ℝ 8 (fun x : ℝ => x * V (m * x ^ 2)) s := contDiffOn_id.mul hW
  have hAb : ∀ i : ℕ, i ≤ 8 → ∀ x ∈ s, ‖iteratedFDerivWithin ℝ i (fun x : ℝ => x * V (m * x ^ 2)) s x‖ ≤ BA := by
    intro i hi x hx
    have h := norm_iteratedFDerivWithin_mul_le (f := fun x : ℝ => x) (g := fun x : ℝ => V (m * x ^ 2)) (N := 8)
      contDiffOn_id hW hsu hx (n := i) (by exact_mod_cast hi)
    refine h.trans ?_
    calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j (fun x : ℝ => x) s x‖ *
          ‖iteratedFDerivWithin ℝ (i - j) (fun x : ℝ => V (m * x ^ 2)) s x‖
        ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * Di * BW := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' : j ≤ i := by have := Finset.mem_range.1 hj; omega
          have hDi0 : 0 ≤ Di := by linarith
          gcongr
          · exact hDi j (hj'.trans hi) x hx
          · exact hWb (i - j) (by omega) x hx
      _ = 2 ^ i * Di * BW := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact_mod_cast Nat.sum_range_choose i
      _ ≤ BA := by
          rw [hBA]
          have hDi0 : 0 ≤ Di := by linarith
          have : (2 : ℝ) ^ i ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) hi
          gcongr
  have hGeq : (fun x : ℝ => k * (x * V (m * x ^ 2))) = k • (fun x : ℝ => x * V (m * x ^ 2)) := by
    funext x; simp
  refine ⟨hA.const_smul k |>.congr (fun x _ => by simp) |>.congr (fun x _ => rfl), fun i hi x hx => ?_⟩
  rw [hGeq, iteratedFDerivWithin_const_smul_apply (hA.contDiffWithinAt hx |>.of_le (by exact_mod_cast hi)) hsu hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos hk0]
  have := hAb i hi x hx
  nlinarith


/-- Stage 2 (Faà di Bruno for `χ_in(T/τ₁)`): for `g` with bounded derivatives up to order `8`, `g(T/τ₁) ∈ 𝒮⁰(C)` on `[0, U_c]`. -/
theorem fctB2_symbol_gen {g : ℝ → ℝ} (hg : ContDiff ℝ 8 g) {Cg : ℝ}
    (hCg : ∀ i : ℕ, i ≤ 8 → ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ Cg) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ c : ℝ, 1 ≤ c → ∀ V : ℝ → ℝ, FctVJets K c V →
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C (fun u => ((g (fctInnerT c V u / fctTau1 c) : ℝ) : ℂ)) := by
  have hτs0 : 0 ≤ (12 / π ^ 2) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  obtain ⟨B, hB1, hBG⟩ := fctB2_G_bound (K + (12 / π ^ 2) ^ (1 / 3 : ℝ)) (by positivity)
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0 (by norm_num) 0)
  set BF : ℝ := (Nat.factorial 8 : ℝ) * Cg * B ^ 8 with hBF
  have hBF0 : 0 ≤ BF := by positivity
  refine ⟨(Nat.factorial 8 : ℝ) * BF * 4 ^ 8, fun c hc V hV => ?_⟩
  have hc0 : 0 < c := by linarith
  set τs : ℝ := (12 / π ^ 2) ^ (1 / 3 : ℝ) with hτs
  set s : Set ℝ := Icc (0 : ℝ) 2.96 with hs
  set t : Set ℝ := Icc (0 : ℝ) 3.6 with ht
  set m : ℝ := (2 : ℝ) ^ (-(4 / 3 : ℝ)) with hm
  set k : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) with hk
  have hsu : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by norm_num)
  have hV8 : ContDiffOn ℝ 8 V t := hV.1.of_le (by norm_num)
  have hcK : K * c ^ (-(1 / 2 : ℝ)) ≤ K :=
    mul_le_of_le_one_right hK (Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num))
  have hVb : ∀ j : ℕ, j ≤ 8 → ∀ Y ∈ t, ‖iteratedFDerivWithin ℝ j V t Y‖ ≤ K + τs := by
    intro j hj Y hY
    have h := hV.2 j (by omega) Y hY
    rw [← Real.norm_eq_abs, ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at h
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDerivWithin_zero]
      rw [norm_iteratedFDerivWithin_zero] at h
      calc ‖V Y‖ = ‖(V Y - τs) + τs‖ := by ring_nf
        _ ≤ ‖V Y - τs‖ + ‖τs‖ := norm_add_le _ _
        _ ≤ K + τs := by
          rw [Real.norm_of_nonneg hτs0]
          linarith
    · have e : iteratedDerivWithin j V t Y = iteratedDerivWithin j (fun z => τs + (V z - τs)) t Y := by
        congr 1; funext z; ring
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, e, iteratedDerivWithin_const_add hj0,
        ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
      have h' : ‖iteratedFDerivWithin ℝ j (fun z => V z - τs) t Y‖ ≤ K * c ^ (-(1 / 2 : ℝ)) := h
      linarith
  obtain ⟨hGc, hGb⟩ := hBG V hV8 hVb
  have hF : ContDiffOn ℝ 8 (fun x : ℝ => g (k * (x * V (m * x ^ 2)))) s :=
    hg.contDiffOn.comp hGc (mapsTo_univ _ _)
  have hFb : ∀ i : ℕ, i ≤ 8 → ∀ x ∈ s,
      ‖iteratedFDerivWithin ℝ i (fun x : ℝ => g (k * (x * V (m * x ^ 2)))) s x‖ ≤ BF := by
    intro i hi x hx
    have h := norm_iteratedFDerivWithin_comp_le (g := g) (f := fun x : ℝ => k * (x * V (m * x ^ 2)))
      (n := i) (N := 8) (s := s) (t := univ) hg.contDiffOn hGc (by exact_mod_cast hi) uniqueDiffOn_univ hsu
      (mapsTo_univ _ _) hx (C := Cg) (D := B)
      (fun j hj => by rw [iteratedFDerivWithin_univ]; exact hCg j (hj.trans hi) _)
      (fun j hj1 hji => (hGb j (hji.trans hi) x hx).trans (le_self_pow₀ hB1 (by omega)))
    refine h.trans ?_
    have h1 : (Nat.factorial i : ℝ) ≤ Nat.factorial 8 := by exact_mod_cast Nat.factorial_le hi
    have h2 : B ^ i ≤ B ^ 8 := pow_le_pow_right₀ hB1 hi
    rw [hBF]
    gcongr
  -- scaling `u ↦ u / c^{1/12}`
  set x : ℝ := c ^ ((1 : ℝ) / 12) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos hc0 _
  have hx1 : 1 ≤ x := Real.one_le_rpow hc (by norm_num)
  set l : ℝ := x⁻¹ with hl
  have hl0 : 0 < l := inv_pos.2 hxpos
  have hl1 : l ≤ 1 := inv_le_one_of_one_le₀ hx1
  set D : Set ℝ := Icc 0 (fctUc c) with hD
  have hUpos : 0 < fctUc c := by unfold fctUc; positivity
  have hDu : UniqueDiffOn ℝ D := uniqueDiffOn_Icc hUpos
  have hUc : fctUc c = 2.96 * x := rfl
  have hmaps : MapsTo (fun u : ℝ => l * u) D s := by
    intro u hu
    obtain ⟨h0, h1⟩ := hu
    refine ⟨by positivity, ?_⟩
    rw [hUc] at h1
    calc l * u ≤ l * (2.96 * x) := mul_le_mul_of_nonneg_left h1 hl0.le
      _ = 2.96 := by rw [hl]; field_simp
  have hlin : ContDiffOn ℝ 8 (fun u : ℝ => l * u) D := (contDiff_const.mul contDiff_id).contDiffOn
  have hfun : (fun u => g (fctInnerT c V u / fctTau1 c)) =
      fun u => (fun x : ℝ => g (k * (x * V (m * x ^ 2)))) (l * u) := by
    funext u
    rw [fctB2_inner_ratio hc0, hl, inv_mul_eq_div, mul_assoc]
  have hcomp : ContDiffOn ℝ 8 (fun u => g (fctInnerT c V u / fctTau1 c)) D := by
    rw [hfun]; exact hF.comp hlin hmaps
  have hbound : ∀ r : ℕ, r ≤ 8 → ∀ u ∈ D,
      ‖iteratedFDerivWithin ℝ r (fun u => g (fctInnerT c V u / fctTau1 c)) D u‖ ≤
        (Nat.factorial 8 : ℝ) * BF * 4 ^ 8 * (1 + u) ^ ((0 : ℝ) - r) := by
    intro r hr u hu
    have h := norm_iteratedFDerivWithin_comp_le (g := fun x : ℝ => g (k * (x * V (m * x ^ 2))))
      (f := fun u : ℝ => l * u) (n := r) (N := 8) (s := D) (t := s) hF hlin (by exact_mod_cast hr) hsu hDu hmaps hu
      (C := BF) (D := l) (fun j hj => hFb j (hj.trans hr) _ (hmaps hu))
      (fun j hj1 hji => by
        refine (fctB2_affine_norm l hDu hu hj1).trans ?_
        rw [abs_of_pos hl0])
    rw [hfun]
    refine h.trans ?_
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u ≤ 2.96 * x := hu.2
    have hlu : l * (1 + u) ≤ 4 := by
      have : l * u ≤ 2.96 := by
        calc l * u ≤ l * (2.96 * x) := mul_le_mul_of_nonneg_left hu1 hl0.le
          _ = 2.96 := by rw [hl]; field_simp
      nlinarith
    have hrp : (1 + u) ^ ((0 : ℝ) - r) = ((1 + u) ^ r)⁻¹ := by
      rw [zero_sub, Real.rpow_neg (by linarith), Real.rpow_natCast]
    rw [hrp]
    have hlr : l ^ r ≤ 4 ^ r * ((1 + u) ^ r)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hlu r
    have h1 : (Nat.factorial r : ℝ) ≤ Nat.factorial 8 := by exact_mod_cast Nat.factorial_le hr
    have h4 : (4 : ℝ) ^ r ≤ 4 ^ 8 := pow_le_pow_right₀ (by norm_num) hr
    have hpos : 0 ≤ ((1 + u) ^ r)⁻¹ := by positivity
    calc (Nat.factorial r : ℝ) * BF * l ^ r ≤ (Nat.factorial 8 : ℝ) * BF * (4 ^ r * ((1 + u) ^ r)⁻¹) := by gcongr
      _ ≤ (Nat.factorial 8 : ℝ) * BF * (4 ^ 8 * ((1 + u) ^ r)⁻¹) := by gcongr
      _ = _ := by ring
  refine ⟨?_, fun r hr u hu => ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hcomp).of_le (by simp)
  · have hκ : (fun u => ((g (fctInnerT c V u / fctTau1 c) : ℝ) : ℂ)) =
        Complex.ofRealLI ∘ (fun u => g (fctInnerT c V u / fctTau1 c)) := rfl
    rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, hκ,
      LinearIsometry.norm_iteratedFDerivWithin_comp_left _ (hcomp.contDiffWithinAt hu) hDu hu (by exact_mod_cast (hr.trans (by norm_num : (8:ℕ) ≤ 8)))]
    exact hbound r hr u hu


/-- The derivatives of order `≤ 8` of the cutoff `χ_in` are bounded (compact support). -/
lemma fctB2_cutoff_bound {χ : ℝ → ℝ} (hχ : FctCutoffIn χ) :
    ∃ C : ℝ, ∀ i : ℕ, i ≤ 8 → ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ C := by
  have hcs : HasCompactSupport χ := HasCompactSupport.intro (isCompact_Icc (a := (-1.98 : ℝ)) (b := 1.98)) (fun x hx => by
    apply hχ.zero
    by_contra hlt
    push Not at hlt
    exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩)
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ C := fun i =>
    ((hχ.smooth.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hcs.iteratedFDeriv i))
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range 9, |C i|, fun i hi x => ?_⟩
  have h1 : |C i| ≤ ∑ j ∈ Finset.range 9, |C j| :=
    Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  linarith [hC i x, le_abs_self (C i)]

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

/-- **`fct:inner-symbols` (b2), symbol part** (Faà di Bruno for `χ_in(T/τ₁)`, with `T/τ₁ = G(c^{-1/12} u)`, `G(x) = 2^{-2/3} x V(2^{-4/3} x²)`
and `‖G^{(i)}‖ ≤ C(K)` on `[0, 2.96]`; two applications of `norm_iteratedFDerivWithin_comp_le`). -/
theorem fctInnerB2Symbol : FctInnerB2Symbol := by
  intro χin hχ K hK
  obtain ⟨Cg, hCg⟩ := fctB2_cutoff_bound hχ
  obtain ⟨C1, hC1⟩ := fctB2_symbol_gen (hχ.smooth.of_le (by simp)) hCg K hK
  have hg2 : ContDiff ℝ 8 (fun x : ℝ => 1 - χin x) := contDiff_const.sub (hχ.smooth.of_le (by simp))
  have hCg2 : ∀ i : ℕ, i ≤ 8 → ∀ x, ‖iteratedFDeriv ℝ i (fun x : ℝ => 1 - χin x) x‖ ≤ Cg + 1 := by
    intro i hi x
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_le]
      have := hχ.mem x
      have h0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0 (by norm_num) 0)
      constructor <;> linarith [this.1, this.2]
    · rw [fun_iteratedFDeriv_sub_apply contDiff_const.contDiffAt (hχ.smooth.of_le (by simp)).contDiffAt,
        iteratedFDeriv_const_of_ne hi0.ne']
      rw [Pi.zero_apply, zero_sub, norm_neg]
      linarith [hCg i hi x]
  obtain ⟨C2, hC2⟩ := fctB2_symbol_gen hg2 hCg2 K hK
  refine ⟨max C1 C2, 1, fun c hc V hV => ⟨?_, ?_⟩⟩
  · exact (hC1 c hc V hV).mono_B Icc_subset_Ici_self (le_max_left _ _)
  · exact (hC2 c hc V hV).mono_B Icc_subset_Ici_self (le_max_right _ _)

/-- **`fct:inner-symbols` (b2) assembled** (Lemma FCT.5b (b2)): the full statement (support, `T(U_c) < 2τ₁`, `χ, 1 - χ ∈ 𝒮⁰(C)`, `1 - χ = 0` on `[0, u_*]`), proved. -/
theorem fctInnerB2 {χin : ℝ → ℝ} (hχ : FctCutoffIn χin) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ V : ℝ → ℝ, FctVJets K c V →
      (∀ u ∈ Icc (2.95 * c ^ ((1 : ℝ) / 12)) (fctUc c), fctInnerChi χin c V u = 0) ∧
      fctInnerT c V (fctUc c) < 2 * fctTau1 c ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C (fun u => ((fctInnerChi χin c V u : ℝ) : ℂ)) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C (fun u => ((1 - fctInnerChi χin c V u : ℝ) : ℂ)) ∧
      ∀ u ∈ Icc 0 (fctUstar c), 1 - fctInnerChi χin c V u = 0 := by
  obtain ⟨C, c₁, hC⟩ := fctInnerB2Symbol χin hχ K hK
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

/-- info: 'FormalResearch.SignUncertainty.fctInnerB2Symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerB2Symbol

/-- info: 'FormalResearch.SignUncertainty.fctInnerB2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerB2

end FormalResearch.SignUncertainty
