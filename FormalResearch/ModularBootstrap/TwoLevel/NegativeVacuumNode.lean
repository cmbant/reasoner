module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransferWindow
public import FormalResearch.ModularBootstrap.Upper.Window.Product

/-!
# Node values of the two-simple-zero window (`virasoro_two_level.tex`, Theorem 2.5, Step 1)

For real zeros `p`, `q` and site and width sequences `S`, `W` the complex window is
`winC p q S W u = -(u - p) · W^{(2)}(u)` (`W^{(2)} = airyWindowProd 2 q S W`), the window `d.W` of a
`TwoZeroDesign`.  This module evaluates it at the Airy zeros and proves a dominated convergence statement for the
infinite products there:

* `winC_node`: `winC p q S W (a_n) / Ai'(a_n)² = nodeC p q S W n`, the explicit product formula;
* `tailHyp_of_bound`: the tail hypothesis of the Airy product from bounds beyond a finite index;
* `tendsto_tailExcept`: if the factors of `airyProdTailExcept 2 n` of a sequence of data converge termwise with a
  summable uniform bound on `factor - 1`, the products converge.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- The complex window `-(u - p) · W^{(2)}(u)` with zeros `p`, `q` and arbitrary sites and widths. -/
noncomputable def winC (p q : ℝ) (S W : ℕ → ℝ) (u : ℂ) : ℂ :=
  -(u - (p : ℂ)) * airyWindowProd 2 q S W u

/-- The product formula for the node value `winC p q S W (a_n) / Ai'(a_n)²`. -/
noncomputable def nodeC (p q : ℝ) (S W : ℕ → ℝ) (n : ℕ) : ℂ :=
  ((airyZero n : ℂ) - p) * ((airyZero n : ℂ) - q) /
      (∏ k ∈ (Finset.Icc 1 2).erase n, ((airyZero n : ℂ) - airyZero k) ^ 2) *
    (if 3 ≤ n then ((airyZero n : ℂ) - S n) ^ 2 + (W n : ℂ) ^ 2 else 1) *
    airyProdTailExcept 2 n S W (airyZero n : ℂ)

lemma airyProdTailExcept_of_le {n : ℕ} (hn : n ≤ 2) (S W : ℕ → ℝ) (u : ℂ) :
    airyProdTailExcept 2 n S W u = airyProdTail 2 S W u := by
  unfold airyProdTailExcept airyProdTail
  refine tprod_congr fun m => ?_
  simp only [show ¬(2 + 1 + m = n) by omega, ↓reduceIte]

lemma winC_node (p q : ℝ) (S W : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    winC p q S W (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2 = nodeC p q S W n := by
  have hD : deriv airyAiC (airyZero n : ℂ) ≠ 0 := airyZero_deriv_ne_zero n
  unfold winC nodeC
  rcases Nat.lt_or_ge 2 n with h3 | h3
  · have h3' : 3 ≤ n := h3
    rw [airyWindowProd_at_airyZero_gt 2 q S W h3]
    simp only [h3', ↓reduceIte]
    have hIcc : (Finset.Icc 1 2).erase n = Finset.Icc 1 2 := by
      refine Finset.erase_eq_of_notMem ?_
      simp only [Finset.mem_Icc]; omega
    rw [hIcc]
    field_simp
  · rw [airyWindowProd_at_airyZero_le 2 q S W hn h3, airyProdTailExcept_of_le h3]
    simp only [show ¬(3 ≤ n) by omega, ↓reduceIte]
    field_simp

/-- The tail hypothesis of the Airy product from the bounds of the hypothesis beyond a finite index `M`. -/
lemma tailHyp_of_bound {f M : ℕ} {S W : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (h : ∀ k, M < k → |S k - uWKB k| ≤ C * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
      |W k| ≤ C * (k : ℝ) ^ (-(1 / 3 : ℝ))) : AiryProdTailHypothesis f S W := by
  set B : ℝ := ∑ k ∈ Finset.range (M + 1), ((|S k - uWKB k| + |W k|) * ((k : ℝ) ^ (4 / 3 : ℝ) +
    (k : ℝ) ^ (1 / 3 : ℝ))) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => by positivity
  refine ⟨C + B + 1, by positivity, fun k hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp43 : 0 < (k : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_pos_of_pos hk0 _
  have hp13 : 0 < (k : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hk0 _
  by_cases hkM : M < k
  · obtain ⟨h1, h2⟩ := h k hkM
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right (by linarith) hp43.le),
      h2.trans (mul_le_mul_of_nonneg_right (by linarith) hp13.le)⟩
  · have hkr : k ∈ Finset.range (M + 1) := Finset.mem_range.2 (by omega)
    have hle := Finset.single_le_sum (f := fun k => ((|S k - uWKB k| + |W k|) *
      ((k : ℝ) ^ (4 / 3 : ℝ) + (k : ℝ) ^ (1 / 3 : ℝ)))) (fun k _ => by positivity) hkr
    have e43 : (k : ℝ) ^ (4 / 3 : ℝ) * (k : ℝ) ^ (-(4 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hk0]; simp
    have e13 : (k : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hk0]; simp
    have p43 : 0 < (k : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hk0 _
    have p13 : 0 < (k : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hk0 _
    constructor
    · calc |S k - uWKB k| = |S k - uWKB k| * ((k : ℝ) ^ (4 / 3 : ℝ) * (k : ℝ) ^ (-(4 / 3 : ℝ))) := by
            rw [e43, mul_one]
        _ = (|S k - uWKB k| * (k : ℝ) ^ (4 / 3 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
        _ ≤ (C + B + 1) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hp43.le
            nlinarith [abs_nonneg (S k - uWKB k), abs_nonneg (W k), mul_nonneg
              (abs_nonneg (S k - uWKB k)) p13.le, mul_nonneg (abs_nonneg (W k)) p43.le,
              mul_nonneg (abs_nonneg (W k)) p13.le]
    · calc |W k| = |W k| * ((k : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ))) := by
            rw [e13, mul_one]
        _ = (|W k| * (k : ℝ) ^ (1 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by ring
        _ ≤ (C + B + 1) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hp13.le
            nlinarith [abs_nonneg (S k - uWKB k), abs_nonneg (W k), mul_nonneg
              (abs_nonneg (S k - uWKB k)) p13.le, mul_nonneg (abs_nonneg (W k)) p43.le,
              mul_nonneg (abs_nonneg (S k - uWKB k)) p43.le]

/-- Dominated convergence for the products `airyProdTailExcept 2 n` at `a_n`: the factors `k = m + 3` of a sequence
`(S j, W j)` of data converge termwise (`k ≠ n`) and `factor - 1` has a summable uniform bound. -/
lemma tendsto_tailExcept {n : ℕ} (hn : 1 ≤ n) (S W : ℕ → ℕ → ℝ) (S' W' : ℕ → ℝ) (bound : ℕ → ℝ)
    (hb : Summable bound)
    (hS : ∀ k, 3 ≤ k → k ≠ n → Tendsto (fun j => S j k) atTop (𝓝 (S' k)))
    (hW : ∀ k, 3 ≤ k → k ≠ n → Tendsto (fun j => W j k) atTop (𝓝 (W' k)))
    (hbd : ∀ᶠ j in atTop, ∀ k, 3 ≤ k → k ≠ n →
      ‖airyProdFactor (S j) (W j) k (airyZero n : ℂ) - 1‖ ≤ bound (k - 3))
    (hb0 : ∀ m, 0 ≤ bound m) :
    Tendsto (fun j => airyProdTailExcept 2 n (S j) (W j) (airyZero n : ℂ)) atTop
      (𝓝 (airyProdTailExcept 2 n S' W' (airyZero n : ℂ))) := by
  have key : ∀ (S W : ℕ → ℝ), airyProdTailExcept 2 n S W (airyZero n : ℂ) =
      ∏' m : ℕ, (1 + (if 3 + m = n then (0 : ℂ) else airyProdFactor S W (3 + m) (airyZero n : ℂ) - 1)) := by
    intro S W
    unfold airyProdTailExcept
    refine tprod_congr fun m => ?_
    by_cases h : 3 + m = n
    · simp [h]
    · simp [h]
  simp only [key]
  refine tendsto_tprod_one_add_of_dominated_convergence (g := fun m =>
    if 3 + m = n then (0 : ℂ) else airyProdFactor S' W' (3 + m) (airyZero n : ℂ) - 1) hb ?_ ?_
  · intro m
    by_cases h : 3 + m = n
    · simp only [h, ↓reduceIte]; exact tendsto_const_nhds
    · simp only [h, ↓reduceIte]
      have hk : 3 + m ≠ n := h
      have hden : ((airyZero n : ℂ) - (airyZero (3 + m) : ℂ)) ^ 2 ≠ 0 := by
        refine pow_ne_zero 2 (sub_ne_zero.mpr fun he => hk ?_)
        have := airyZero_injective_on (by omega) (by omega) (Complex.ofReal_injective he)
        omega
      have h1 := hS (3 + m) (by omega) hk
      have h2 := hW (3 + m) (by omega) hk
      unfold airyProdFactor
      refine Tendsto.sub ?_ tendsto_const_nhds
      refine Tendsto.div_const ?_ _
      refine Tendsto.add ?_ ?_
      · exact (tendsto_const_nhds.sub (Complex.continuous_ofReal.continuousAt.tendsto.comp h1)).pow 2
      · exact ((Complex.continuous_ofReal.continuousAt.tendsto.comp h2)).pow 2
  · filter_upwards [hbd] with j hj m
    by_cases h : 3 + m = n
    · simp only [h, ↓reduceIte, norm_zero]; exact hb0 m
    · simp only [h, ↓reduceIte]
      have := hj (3 + m) (by omega) h
      simpa using this

end FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum
