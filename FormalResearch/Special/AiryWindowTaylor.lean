module

public import FormalResearch.Special.AiryShiftTaylor
public import FormalResearch.Special.AiryKernelOpSharp

/-!
# Taylor remainders of `Ai` on the bounded oscillatory window `X ∈ [-A₀, -1]`

`AiryShiftTaylor.airy_taylor4/5` (the Taylor step of `lem:ec-defect`, `EC:78-86`) cover base points `X ≥ -1` only, because
their sup bound uses the envelope `airyAi_envelope_real` (`Ai ≍ airyWt` on `X ≥ -1`).  The parametrix defect on the
**oscillatory window** of `AiryWindowMain` (hypothesis `hdefW`) needs the same expansions for `X ∈ [-A₀, -1]`.  The
generic remainder theorems `airy_sol_taylor4/5` need only a sup bound of the relevant jet on the segment `[X, X+s]`, which for
`X ∈ [-A₀,-1]`, `|s| ≤ 1` lies in `[-A₀-1, 0]`, where `abs_airyAi_le_of_nonpos`, `abs_airyAi'_le_of_nonpos`
(`|Ai x| ≤ 3 (1+|x|)^{-1/4} ≤ 3`, `|Ai' x| ≤ 5 (1+|x|)^{1/4} ≤ 5 (1+|x|)`) give, with explicit constants (**proved**):

* `airy_taylor4_window`: `|Ai(X+s) - T₄| ≤ B₄(A₀) |s|⁵` and `|Ai'(X+s) - T₃'| ≤ B₄(A₀) |s|⁴`,
  `B₄(A₀) = 12 (A₀+1) + 5 (A₀+1)² (A₀+2)`;
* `airy_taylor5_window`: `|Ai(X+s) - T₅| ≤ B₅(A₀) |s|⁶` and `|Ai'(X+s) - T₄'| ≤ B₅(A₀) |s|⁵`,
  `B₅(A₀) = 3 ((A₀+1)³ + 4) + 30 (A₀+1)(A₀+2)`

for `-A₀ ≤ X ≤ -1`, `|s| ≤ 1` (`T₄, T₃', T₅, T₄'` as in `AiryShiftTaylor`).  mpmath check (30 digits, `num_taylor.py` in
`/home/user/scratch/m6_numerics/`, grid `A₀ ∈ {1,3,10}`, 40 values of `X`, `s ∈ {-1,…,1}` step `0.05`): the ratios
remainder `/` (stated bound) are `≤ 2.3·10⁻⁴` (order 4/`Ai`) and `≤ 5·10⁻⁵` (order 5/`Ai`), so the constants are very far from sharp.  The constants are polynomial in `A₀`, non-sharp
(no `1/n!`, no use of the oscillation).  Together with `airy_taylor4/5` (`X ≥ -1`) this gives the Taylor remainders of `Ai` on
`X ≥ -A₀`, the form needed by the parametrix module for the window `hdefW`; the other ingredients of the defect on the
window (jets of `g`, `ζ`, `a`, `c` across the turn) are not treated here.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- `|Ai x| ≤ 3` and `|Ai' x| ≤ 5 (A₀ + 2)` for `-(A₀+1) ≤ x ≤ 0`. -/
lemma airy_window_bounds {A0 x : ℝ} (hx0 : x ≤ 0) (hx1 : -(A0 + 1) ≤ x) :
    |airyAi x| ≤ 3 ∧ |airyAi' x| ≤ 5 * (A0 + 2) := by
  have hu : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hu2 : 1 + |x| ≤ A0 + 2 := by
    rw [abs_of_nonpos hx0]; linarith
  constructor
  · refine (abs_airyAi_le_of_nonpos hx0).trans ?_
    have : (1 + |x|) ^ (-(1 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
    linarith
  · refine (abs_airyAi'_le_of_nonpos hx0).trans ?_
    have h1 : (1 + |x|) ^ (1 / 4 : ℝ) ≤ 1 + |x| := by
      calc (1 + |x|) ^ (1 / 4 : ℝ) ≤ (1 + |x|) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
        _ = 1 + |x| := Real.rpow_one _
    linarith

theorem airy_taylor4_window (A0 : ℝ) (X s : ℝ) (hX0 : X ≤ -1) (hX1 : -A0 ≤ X) (hs : |s| ≤ 1) :
    |airyAi (X + s) - (airyAi X + s * airyAi' X + s ^ 2 / 2 * (X * airyAi X) +
        s ^ 3 / 6 * (airyAi X + X * airyAi' X) + s ^ 4 / 24 * (X ^ 2 * airyAi X + 2 * airyAi' X))|
      ≤ (12 * (A0 + 1) + 5 * (A0 + 1) ^ 2 * (A0 + 2)) * |s| ^ 5 ∧
    |airyAi' (X + s) - (airyAi' X + s * (X * airyAi X) + s ^ 2 / 2 * (airyAi X + X * airyAi' X) +
        s ^ 3 / 6 * (X ^ 2 * airyAi X + 2 * airyAi' X))|
      ≤ (12 * (A0 + 1) + 5 * (A0 + 1) ^ 2 * (A0 + 2)) * |s| ^ 4 := by
  have hA0 : 0 ≤ A0 := by linarith
  refine airy_sol_taylor4 isAirySol_airyAi X s _ ?_
  intro t ht
  have htt := abs_le_abs_of_mem_uIcc ht
  have ht1 : |t| ≤ 1 := htt.trans hs
  rw [abs_le] at ht1
  obtain ⟨b1, b2⟩ := airy_window_bounds (A0 := A0) (x := X + t) (by linarith) (by linarith)
  have hxa : |X + t| ≤ A0 + 1 := by rw [abs_of_nonpos (by linarith)]; linarith
  have h1 : |4 * (X + t) * airyAi (X + t)| ≤ 12 * (A0 + 1) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have := mul_le_mul hxa b1 (abs_nonneg _) (by linarith)
    nlinarith [abs_nonneg (X + t), abs_nonneg (airyAi (X + t))]
  have h2 : |(X + t) ^ 2 * airyAi' (X + t)| ≤ 5 * (A0 + 1) ^ 2 * (A0 + 2) := by
    rw [abs_mul, abs_pow]
    have e1 : |X + t| ^ 2 ≤ (A0 + 1) ^ 2 := by gcongr
    have := mul_le_mul e1 b2 (abs_nonneg _) (by positivity)
    nlinarith
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem airy_taylor5_window (A0 : ℝ) (X s : ℝ) (hX0 : X ≤ -1) (hX1 : -A0 ≤ X) (hs : |s| ≤ 1) :
    |airyAi (X + s) - (airyAi X + s * airyAi' X + s ^ 2 / 2 * (X * airyAi X) +
        s ^ 3 / 6 * (airyAi X + X * airyAi' X) + s ^ 4 / 24 * (X ^ 2 * airyAi X + 2 * airyAi' X) +
        s ^ 5 / 120 * (4 * X * airyAi X + X ^ 2 * airyAi' X))|
      ≤ (3 * ((A0 + 1) ^ 3 + 4) + 30 * (A0 + 1) * (A0 + 2)) * |s| ^ 6 ∧
    |airyAi' (X + s) - (airyAi' X + s * (X * airyAi X) + s ^ 2 / 2 * (airyAi X + X * airyAi' X) +
        s ^ 3 / 6 * (X ^ 2 * airyAi X + 2 * airyAi' X) + s ^ 4 / 24 * (4 * X * airyAi X + X ^ 2 * airyAi' X))|
      ≤ (3 * ((A0 + 1) ^ 3 + 4) + 30 * (A0 + 1) * (A0 + 2)) * |s| ^ 5 := by
  have hA0 : 0 ≤ A0 := by linarith
  refine airy_sol_taylor5 isAirySol_airyAi X s _ ?_
  intro t ht
  have htt := abs_le_abs_of_mem_uIcc ht
  have ht1 : |t| ≤ 1 := htt.trans hs
  rw [abs_le] at ht1
  obtain ⟨b1, b2⟩ := airy_window_bounds (A0 := A0) (x := X + t) (by linarith) (by linarith)
  have hxa : |X + t| ≤ A0 + 1 := by rw [abs_of_nonpos (by linarith)]; linarith
  have h1 : |((X + t) ^ 3 + 4) * airyAi (X + t)| ≤ 3 * ((A0 + 1) ^ 3 + 4) := by
    rw [abs_mul]
    have e1 : |(X + t) ^ 3 + 4| ≤ (A0 + 1) ^ 3 + 4 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_pow]
      have : |X + t| ^ 3 ≤ (A0 + 1) ^ 3 := by gcongr
      norm_num
      linarith
    have := mul_le_mul e1 b1 (abs_nonneg _) (by positivity)
    nlinarith
  have h2 : |6 * (X + t) * airyAi' (X + t)| ≤ 30 * (A0 + 1) * (A0 + 2) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have := mul_le_mul hxa b2 (abs_nonneg _) (by linarith)
    nlinarith [abs_nonneg (X + t), abs_nonneg (airyAi' (X + t))]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- info: 'FormalResearch.Special.airy_taylor4_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_taylor4_window

/-- info: 'FormalResearch.Special.airy_taylor5_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_taylor5_window

end FormalResearch.Special
