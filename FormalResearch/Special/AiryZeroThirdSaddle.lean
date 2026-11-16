module

public import FormalResearch.Special.AiryZeroSecondOrderSaddle

/-!
# The saddle-point integral of `Ai(w²)` to every order: `J₀(w) = (π/w)^{1/2} Σ_{j<N} c_j w^{-3j} + O(w^{-3N})`

`AiryZeroSecondOrderSaddle` proves the cases `N = 2, 3` of the expansion of `J₀(w) = ∫ exp(-w s² - i s³/3) ds` by hand.  Here
the same estimate is proved for every `N`, from the Taylor polynomial of `e^{ix}` of degree `< 2N` (the odd moments vanish)
and the Gaussian moments `∫ s^{2k} e^{-w s²} = ((2k-1)!!/(2w)^k)(π/w)^{1/2}` (complex `w`, `Re w > 0`):

* `airyT3Mom k = (2k-1)!! = ∏_{i<k}(2i+1)`, `airyT3_integral_even` (complex), `airyT3_integral_even_real`;
* `airyT3Coef j = (-1)^j (6j-1)!!/(9^j (2j)! 8^j)`: `c_0 = 1`, `c_1 = -5/48`, `c_2 = 385/4608`, `c_3 = -85085/663552`,
  `c_4 = 37182145/127401984` (these are the `u_j` of DLMF 9.7.2 after the scaling `w³ = (3/2)ξ`; `airyT3Coef_three`,
  `airyT3Coef_four` evaluate the last two);
* **`norm_saddleJ0_general_le`**: for `ρ = Re w > 0`,
  `‖J₀(w) - (π/w)^{1/2} Σ_{j<N} c_j w^{-3j}‖ ≤ ((6N-1)!!/(8^N 9^N (2N)!)) √(π/ρ)/ρ^{3N}`;
  for `N = 3` this is the constant `34459425/268738560` of `norm_saddleJ0_fourth_le`;
* **`norm_airyAiC_sq_general_le`**: the same for `Ai(w²)` with the prefactor `e^{-(2/3)w³}/(2π)`;
  `norm_saddleJ0_fifth_le`: the case `N = 5` with explicit coefficients, used by `AiryZeroThirdChi`.

Proved here: everything stated; the exact values `c_3`, `c_4` agree with `-u_3 (9/4)^{3}...`-type scaling of DLMF 9.7.2.
**Not formalised:** sector-uniform versions, and the expansion of `Ai'`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The odd double factorial `(2k-1)!! = ∏_{i<k} (2i+1)`. -/
def airyT3Mom (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (2 * i + 1)

lemma airyT3Mom_succ (k : ℕ) : airyT3Mom (k + 1) = airyT3Mom k * (2 * k + 1) := by
  simp [airyT3Mom, Finset.prod_range_succ]

/-- The coefficients of the saddle expansion: `c_j = (-1)^j (6j-1)!!/(9^j (2j)! 8^j)`. -/
noncomputable def airyT3Coef (j : ℕ) : ℝ :=
  (-1) ^ j * (airyT3Mom (3 * j) : ℝ) / (9 ^ j * ((2 * j).factorial : ℝ) * 8 ^ j)

/-- **Gaussian moments**: `∫ s^{2k} e^{-w s²} = ((2k-1)!!/(2w)^k) (π/w)^{1/2}` for `Re w > 0`. -/
lemma airyT3_integral_even {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    ∫ s : ℝ, (s : ℂ) ^ (2 * k) * cexp (-w * (s : ℂ) ^ 2) =
      (airyT3Mom k : ℂ) / (2 * w) ^ k * (π / w) ^ (1 / 2 : ℂ) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  induction k with
  | zero => simpa [airyT3Mom] using integral_gaussian_complex hw
  | succ k ih =>
    have h := integral_pow_gauss_succ hw (2 * k)
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, h, ih, airyT3Mom_succ]
    push_cast
    rw [pow_succ]
    field_simp

/-- Odd moments vanish. -/
lemma airyT3_integral_odd (w : ℂ) {n : ℕ} (hn : Odd n) :
    ∫ s : ℝ, (s : ℂ) ^ n * cexp (-w * (s : ℂ) ^ 2) = 0 := by
  refine integral_eq_zero_of_odd fun s => ?_
  push_cast
  rw [neg_pow, hn.neg_one_pow]
  ring_nf

/-- The real Gaussian moments `∫ s^{2k} e^{-ρ s²} = ((2k-1)!!/(2ρ)^k) √(π/ρ)`. -/
lemma airyT3_integral_even_real {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ∫ s : ℝ, s ^ (2 * k) * Real.exp (-ρ * s ^ 2) = (airyT3Mom k : ℝ) / (2 * ρ) ^ k * √(π / ρ) := by
  have hw : 0 < (ρ : ℂ).re := by simpa using hρ
  have h := airyT3_integral_even hw k
  have e1 : ∀ s : ℝ, (s : ℂ) ^ (2 * k) * cexp (-(ρ : ℂ) * (s : ℂ) ^ 2) =
      ((s ^ (2 * k) * Real.exp (-ρ * s ^ 2) : ℝ) : ℂ) := fun s => by
    push_cast; ring
  simp_rw [e1] at h
  rw [integral_complex_ofReal] at h
  have e2 : ((π : ℂ) / (ρ : ℂ)) ^ (1 / 2 : ℂ) = ((√(π / ρ) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  rw [e2] at h
  exact_mod_cast h

/-- The sum of the first `2N` Taylor terms integrates to `(π/w)^{1/2} Σ_{j<N} c_j w^{-3j}`. -/
lemma airyT3_poly_integral {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    ∫ s : ℝ, airySO_P (2 * N) (-(s ^ 3 / 3)) * saddleGauss w s =
      (π / w) ^ (1 / 2 : ℂ) * ∑ j ∈ Finset.range N, (airyT3Coef j : ℂ) / w ^ (3 * j) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hterm : ∀ m : ℕ, ∫ s : ℝ, (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) ^ m / (m.factorial : ℂ) * saddleGauss w s =
      (-I / 3) ^ m / (m.factorial : ℂ) * ∫ s : ℝ, (s : ℂ) ^ (3 * m) * cexp (-w * (s : ℂ) ^ 2) := by
    intro m
    rw [← integral_const_mul]
    congr 1; funext s
    unfold saddleGauss
    push_cast
    rw [show (s : ℂ) ^ (3 * m) = ((s : ℂ) ^ 3) ^ m by rw [pow_mul]]
    rw [show I * (-((s : ℂ) ^ 3 / 3)) = (-I / 3) * (s : ℂ) ^ 3 by ring, mul_pow]
    ring
  have hint : ∀ m : ℕ, Integrable (fun s : ℝ => (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) ^ m / (m.factorial : ℂ) *
      saddleGauss w s) := by
    intro m
    have := (integrable_pow_cexp_gauss hw (3 * m)).const_mul ((-I / 3) ^ m / (m.factorial : ℂ))
    refine this.congr (Eventually.of_forall fun s => ?_)
    unfold saddleGauss
    push_cast
    rw [show (s : ℂ) ^ (3 * m) = ((s : ℂ) ^ 3) ^ m by rw [pow_mul]]
    rw [show I * (-((s : ℂ) ^ 3 / 3)) = (-I / 3) * (s : ℂ) ^ 3 by ring, mul_pow]
    ring
  have hP : ∀ n : ℕ, ∫ s : ℝ, airySO_P n (-(s ^ 3 / 3)) * saddleGauss w s =
      ∑ m ∈ Finset.range n, (-I / 3) ^ m / (m.factorial : ℂ) *
        ∫ s : ℝ, (s : ℂ) ^ (3 * m) * cexp (-w * (s : ℂ) ^ 2) := by
    intro n
    simp only [airySO_P, Finset.sum_mul]
    rw [integral_finsetSum _ (fun m _ => hint m)]
    exact Finset.sum_congr rfl fun m _ => hterm m
  rw [hP]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, airyT3_integral_odd w (n := 3 * (2 * N + 1)) ⟨3 * N + 1, by ring⟩, mul_zero,
      add_zero]
    have e := airyT3_integral_even hw (3 * N)
    rw [show 3 * (2 * N) = 2 * (3 * N) by ring, e]
    have h2 : ((-I / 3) ^ (2 * N) : ℂ) = (-1 / 9) ^ N := by
      rw [pow_mul]; congr 1; ring_nf; rw [Complex.I_sq]; ring
    rw [h2, mul_add]
    congr 1
    have h8 : (2 * w) ^ (3 * N) = 8 ^ N * w ^ (3 * N) := by
      rw [mul_pow, pow_mul]; norm_num
    rw [h8]
    unfold airyT3Coef
    push_cast
    have hf : ((2 * N).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hwp : w ^ (3 * N) ≠ 0 := pow_ne_zero _ hw0
    generalize (π / w) ^ (1 / 2 : ℂ) = Q
    generalize ((airyT3Mom (3 * N) : ℕ) : ℂ) = M
    generalize ((2 * N).factorial : ℂ) = F at hf ⊢
    have h9 : (9 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
    have h8' : (8 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
    have h19 : (-(1 / 9 : ℂ)) ^ N * 9 ^ N = (-1) ^ N := by rw [← mul_pow]; norm_num
    field_simp
    linear_combination (M * Q) * h19

/-- **The saddle expansion to every order.** For `ρ = Re w > 0`,
`‖J₀(w) - (π/w)^{1/2} Σ_{j<N} c_j w^{-3j}‖ ≤ ((6N-1)!!/(8^N 9^N (2N)!)) √(π/ρ)/ρ^{3N}`. -/
theorem norm_saddleJ0_general_le {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    ‖saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * ∑ j ∈ Finset.range N, (airyT3Coef j : ℂ) / w ^ (3 * j)‖ ≤
      (airyT3Mom (3 * N) : ℝ) / (8 ^ N * 9 ^ N * ((2 * N).factorial : ℝ)) * (√(π / w.re) / w.re ^ (3 * N)) := by
  set D : ℝ → ℂ := fun s => saddlePhase s - airySO_P (2 * N) (-(s ^ 3 / 3)) with hD
  have hDc : Continuous D := by
    simp only [hD, saddlePhase, airySO_P]; fun_prop
  have habs : ∀ s : ℝ, |s| ^ (6 * N) = s ^ (6 * N) := fun s => Even.pow_abs ⟨3 * N, by ring⟩ s
  have hF : (0 : ℝ) < ((2 * N).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hDb : ∀ s : ℝ, ‖D s‖ ≤ 1 / (9 ^ N * ((2 * N).factorial : ℝ)) * |s| ^ (6 * N) := fun s => by
    have h := airySO_taylor_le (2 * N) (-(s ^ 3 / 3))
    simp only [hD, saddlePhase]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_pow, ← pow_mul,
      show 3 * (2 * N) = 6 * N by ring, show (3 : ℝ) ^ (2 * N) = 9 ^ N by rw [pow_mul]; norm_num]
    field_simp
  have iDG : Integrable (fun s : ℝ => D s * saddleGauss w s) :=
    integrable_gauss_mul_of_le hw hDc (6 * N) (1 / (9 ^ N * ((2 * N).factorial : ℝ))) hDb
  have hJ : saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * ∑ j ∈ Finset.range N, (airyT3Coef j : ℂ) / w ^ (3 * j) =
      ∫ s : ℝ, D s * saddleGauss w s := by
    rw [← airyT3_poly_integral hw N]
    unfold saddleJ0
    have iP : Integrable (fun s : ℝ => airySO_P (2 * N) (-(s ^ 3 / 3)) * saddleGauss w s) := by
      refine ((integrable_saddle_phase_gauss hw).sub iDG).congr (Eventually.of_forall fun s => ?_)
      simp only [hD, Pi.sub_apply]; ring
    rw [← integral_sub (integrable_saddle_phase_gauss hw) iP]
    congr 1; funext s
    simp only [hD]; ring
  rw [hJ]
  have i18 : Integrable (fun s : ℝ => 1 / (9 ^ N * ((2 * N).factorial : ℝ)) *
      (s ^ (6 * N) * Real.exp (-w.re * s ^ 2))) := by
    have := (integrable_abs_pow_gauss hw (6 * N)).const_mul (1 / (9 ^ N * ((2 * N).factorial : ℝ)))
    simpa [habs] using this
  refine (norm_integral_le_of_norm_le i18 (Filter.Eventually.of_forall fun s => ?_)).trans ?_
  · rw [norm_mul, norm_saddleGauss]
    have := mul_le_mul_of_nonneg_right (hDb s) (Real.exp_pos (-w.re * s ^ 2)).le
    simpa [habs, mul_assoc] using this
  · rw [integral_const_mul, show 6 * N = 2 * (3 * N) by ring, airyT3_integral_even_real hw (3 * N)]
    apply le_of_eq
    rw [show (2 * w.re) ^ (3 * N) = 8 ^ N * w.re ^ (3 * N) by rw [mul_pow, pow_mul]; norm_num]
    field_simp

lemma airyT3Coef_zero : airyT3Coef 0 = 1 := by
  norm_num [airyT3Coef, airyT3Mom]

lemma airyT3Coef_one : airyT3Coef 1 = -5 / 48 := by
  norm_num [airyT3Coef, airyT3Mom, Finset.prod_range_succ, Nat.factorial]

lemma airyT3Coef_two : airyT3Coef 2 = 385 / 4608 := by
  norm_num [airyT3Coef, airyT3Mom, Finset.prod_range_succ, Nat.factorial]

lemma airyT3Coef_three : airyT3Coef 3 = -85085 / 663552 := by
  norm_num [airyT3Coef, airyT3Mom, Finset.prod_range_succ, Nat.factorial]

lemma airyT3Coef_four : airyT3Coef 4 = 37182145 / 127401984 := by
  norm_num [airyT3Coef, airyT3Mom, Finset.prod_range_succ, Nat.factorial]

lemma airyT3_const_five : (airyT3Mom (3 * 5) : ℝ) / (8 ^ 5 * 9 ^ 5 * ((2 * 5).factorial : ℝ)) =
    5391411025 / 6115295232 := by
  norm_num [airyT3Mom, Finset.prod_range_succ, Nat.factorial]

/-- **The `N = 5` saddle estimate** (relative error `w^{-15}`), for `ρ = Re w > 0`:
`‖J₀(w) - (π/w)^{1/2} (1 - 5/(48w³) + 385/(4608w⁶) - 85085/(663552w⁹) + 37182145/(127401984w^{12}))‖
  ≤ (5391411025/6115295232) √(π/ρ)/ρ^{15}`. -/
theorem norm_saddleJ0_fifth_le {w : ℂ} (hw : 0 < w.re) :
    ‖saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3) + 385 / (4608 * w ^ 6) -
        85085 / (663552 * w ^ 9) + 37182145 / (127401984 * w ^ 12))‖ ≤
      5391411025 / 6115295232 * (√(π / w.re) / w.re ^ 15) := by
  have h := norm_saddleJ0_general_le hw 5
  rw [airyT3_const_five] at h
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have e : ∑ j ∈ Finset.range 5, (airyT3Coef j : ℂ) / w ^ (3 * j) =
      1 - 5 / (48 * w ^ 3) + 385 / (4608 * w ^ 6) - 85085 / (663552 * w ^ 9) +
        37182145 / (127401984 * w ^ 12) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, airyT3Coef_zero, airyT3Coef_one, airyT3Coef_two,
      airyT3Coef_three, airyT3Coef_four]
    push_cast
    field_simp
    ring
  rw [e] at h
  exact h

/-- **`Ai(w²)` to relative error `w^{-15}`**, `Re w > 0`. -/
theorem norm_airyAiC_sq_fifth_le {w : ℂ} (hw : 0 < w.re) :
    ‖airyAiC (w ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) *
        ((π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3) + 385 / (4608 * w ^ 6) -
          85085 / (663552 * w ^ 9) + 37182145 / (127401984 * w ^ 12)))‖ ≤
      1 / (2 * π) * ‖cexp (-(2 / 3) * w ^ 3)‖ * (5391411025 / 6115295232 * (√(π / w.re) / w.re ^ 15)) := by
  set Q : ℂ := 1 - 5 / (48 * w ^ 3) + 385 / (4608 * w ^ 6) - 85085 / (663552 * w ^ 9) +
    37182145 / (127401984 * w ^ 12) with hQ
  have e : airyAiC (w ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) * ((π / w) ^ (1 / 2 : ℂ) * Q) =
      (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) * (saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * Q) := by
    rw [airyAiC_sq_eq hw]; ring
  rw [e, norm_mul, norm_mul]
  have h1 : ‖(1 / (2 * (π : ℂ)))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (norm_saddleJ0_fifth_le hw) (by positivity)

end FormalResearch.Special

/-- info: 'FormalResearch.Special.airyT3_integral_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_integral_even

/-- info: 'FormalResearch.Special.airyT3_poly_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_poly_integral

/-- info: 'FormalResearch.Special.norm_saddleJ0_general_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_saddleJ0_general_le

/-- info: 'FormalResearch.Special.norm_saddleJ0_fifth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_saddleJ0_fifth_le

/-- info: 'FormalResearch.Special.norm_airyAiC_sq_fifth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyAiC_sq_fifth_le
