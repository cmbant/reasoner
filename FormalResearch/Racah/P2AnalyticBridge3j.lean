module

public import FormalResearch.Racah.P2AnalyticCarrier3j
public import FormalResearch.Wigner.WignerDLadder
public import FormalResearch.Wigner.WignerDJacobi

/-!
# The `3j` `t = 0` carrier is Wigner's small `d`-function (Weyl P2, `thm:3jeven`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:3jeven` (`G(x, 0) = d^L_{Mσ}(arccos x)`),
`eq:WignerJacobiMonic`; `FormalResearch/Racah/P2AnalyticCarrier3j.lean` for the carrier.

## Dictionary

For `M σ` with `M - σ`, `M + σ` integers (`|M-σ| = α`, `|M+σ| = β` natural), `L₀ = max |M| |σ|`, any
`k : ℕ` and `x ∈ [-1,1]`, with *no* sign and *no* transposition:

  `dZero3 M σ k x = wignerSmallDx (L₀ + k) M σ x = d^{L₀+k}_{Mσ}(arccos x)`

(row index `M` first, column index `σ` second, in the Condon–Shortley convention of
`FormalResearch.Wigner.wignerSmallD`).  The sign `ε(M,σ)` of `seed3` is exactly the sign of Wigner's
extremal value in each of the four chambers.

## Results

* `dZero3_start_eq_wignerD`: the extremal rank `k = 0` (all four chambers; chamber Jacobi forms
  `wignerSmallD_chamber_A..D` at `k = 0`, where `P_0 = 1`).
* `rec_seq_ext`: two sequences with the same three-term recurrence with nonvanishing forward
  coefficient and the same two starts agree.
* `dZero3_eq_wignerD`: the identification, by induction in `k` (`dZero3_rank_rec` against
  `wignerSmallDx_rank_rec`; the backward term vanishes at the start because `R_{L₀} = 0`; the
  scalar case `M = σ = 0` uses `dZero3_one_zero` against `d^1_{00} = x`).
* `Gc3_zero_eq_wignerD`: `Gc3 M σ k x 0 = d^{L₀+k}_{Mσ}(arccos x)` (`thm:3jeven`, germ form).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Special

/-! ### A two-start, three-term recurrence uniqueness lemma -/

/-- Two real sequences satisfying the same three-term recurrence
`e_k a_{k+2} = g_k a_{k+1} - h_k a_k` with `e_k ≠ 0`, and agreeing at `0` and `1`, are equal. -/
theorem rec_seq_ext (a b e g h : ℕ → ℝ) (h0 : a 0 = b 0) (h1 : a 1 = b 1) (he : ∀ k, e k ≠ 0)
    (ha : ∀ k, e k * a (k + 2) = g k * a (k + 1) - h k * a k)
    (hb : ∀ k, e k * b (k + 2) = g k * b (k + 1) - h k * b k) : ∀ k, a k = b k := by
  have key : ∀ k, a k = b k ∧ a (k + 1) = b (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      refine mul_left_cancel₀ (he k) ?_
      rw [ha k, hb k, ih.1, ih.2]
  exact fun k => (key k).1

/-! ### Extremal values -/

lemma br_sqrt_pow (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) n), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt ha]

/-- The Jacobi form at `k = 0` and `θ = arccos x`:
`√((μ+ν)!/(μ!ν!)) · √(((1-x)/2)^μ ((1+x)/2)^ν)`. -/
lemma wignerJacobiForm_zero_arccos (μ ν : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    wignerJacobiForm μ ν 0 (Real.arccos x) =
      Real.sqrt (((μ + ν).factorial : ℝ) / ((μ.factorial : ℝ) * ν.factorial)) *
        Real.sqrt (((1 - x) / 2) ^ μ * ((1 + x) / 2) ^ ν) := by
  have hc : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  have h0 : 0 ≤ Real.arccos x := Real.arccos_nonneg x
  have hpi : Real.arccos x ≤ Real.pi := Real.arccos_le_pi x
  have hs : Real.sin (Real.arccos x / 2) = Real.sqrt ((1 - x) / 2) := by
    have h2 : Real.sin (Real.arccos x / 2) ^ 2 = (1 - x) / 2 := by
      have := Real.cos_sq (Real.arccos x / 2)
      rw [show 2 * (Real.arccos x / 2) = Real.arccos x by ring, hc] at this
      nlinarith [Real.sin_sq_add_cos_sq (Real.arccos x / 2)]
    have hn : 0 ≤ Real.sin (Real.arccos x / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [← h2, Real.sqrt_sq hn]
  have hco : Real.cos (Real.arccos x / 2) = Real.sqrt ((1 + x) / 2) := by
    have h2 : Real.cos (Real.arccos x / 2) ^ 2 = (1 + x) / 2 := by
      have := Real.cos_sq (Real.arccos x / 2)
      rw [show 2 * (Real.arccos x / 2) = Real.arccos x by ring, hc] at this
      linarith
    have hn : 0 ≤ Real.cos (Real.arccos x / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
    rw [← h2, Real.sqrt_sq hn]
  have hA : 0 ≤ (1 - x) / 2 := by linarith [hx.2]
  have hB : 0 ≤ (1 + x) / 2 := by linarith [hx.1]
  unfold wignerJacobiForm
  rw [jacobi_zero, hs, hco, Real.sqrt_mul (pow_nonneg hA μ), br_sqrt_pow _ hA, br_sqrt_pow _ hB]
  simp only [Polynomial.eval_one, mul_one, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add]
  ring

lemma br3_pPlus {M σ : ℚ} {α : ℕ} (hα : |M - σ| = α) : pPlus3 M σ = α := by
  unfold pPlus3; rw [hα]; exact Nat.floor_natCast α

lemma br3_pMinus {M σ : ℚ} {β : ℕ} (hβ : |M + σ| = β) : pMinus3 M σ = β := by
  unfold pMinus3; rw [hβ]; exact Nat.floor_natCast β

/-- **The extremal rank** (all four chambers): `P̃_{L₀}` carrier is `d^{L₀}_{Mσ}(arccos x)`;
the sign `ε(M,σ)` of `seed3` is Wigner's `(-1)^{M-σ}` for `σ ≤ M` and `+1` for `σ > M`. -/
theorem dZero3_start_eq_wignerD (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    dZero3 M σ 0 x = wignerSmallDx (max |M| |σ|) M σ x := by
  rw [dZero3_zero, br3_pPlus hα, br3_pMinus hβ]
  unfold seed3
  rw [br3_pPlus hα, br3_pMinus hβ]
  unfold wignerSmallDx
  by_cases h1 : σ ≤ M
  · simp only [h1, ite_true]
    by_cases h2 : 0 ≤ M + σ
    · have hj : max |M| |σ| = M := by
        rw [abs_of_nonneg (by linarith : 0 ≤ M)]
        exact max_eq_left (abs_le.mpr ⟨by linarith, h1⟩)
      rw [hj, wignerSmallD_chamber_A (μ := α) (ν := β) (k := 0)
        (by rw [← hα, abs_of_nonneg (by linarith)])
        (by rw [← hβ, abs_of_nonneg h2]) (by ring), wignerJacobiForm_zero_arccos _ _ hx]
      ring
    · push Not at h2
      have hj : max |M| |σ| = -σ := by
        rw [abs_of_nonpos (by linarith : σ ≤ 0)]
        exact max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [hj, wignerSmallD_chamber_B (μ := α) (ν := β) (k := 0)
        (by rw [← hα, abs_of_nonneg (by linarith)])
        (by rw [← hβ, abs_of_neg h2]) (by ring), wignerJacobiForm_zero_arccos _ _ hx]
      ring
  · push Not at h1
    simp only [not_le.mpr h1, ite_false, one_mul]
    by_cases h2 : 0 ≤ M + σ
    · have hj : max |M| |σ| = σ := by
        rw [abs_of_nonneg (by linarith : 0 ≤ σ)]
        exact max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [hj, wignerSmallD_chamber_C (μ := α) (ν := β) (k := 0)
        (by rw [← hα, abs_of_neg (by linarith)]; ring)
        (by rw [← hβ, abs_of_nonneg h2]; ring) (by ring), wignerJacobiForm_zero_arccos _ _ hx]
    · push Not at h2
      have hj : max |M| |σ| = -M := by
        rw [abs_of_nonpos (by linarith : M ≤ 0)]
        exact max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [hj, wignerSmallD_chamber_D (μ := α) (ν := β) (k := 0)
        (by rw [← hα, abs_of_neg (by linarith)]; ring)
        (by rw [← hβ, abs_of_neg h2]; ring) (by ring), wignerJacobiForm_zero_arccos _ _ hx]

/-! ### The identification -/

lemma wigR_eq_Rk (M σ j : ℚ) : wigR j M σ = Rk M σ j := by
  unfold wigR Rk; rw [mul_comm]

/-- **`dZero3` is Wigner's `d`** (`thm:3jeven`, `eq:WignerJacobiMonic` normalisation): for
`M ± σ` integers, `L₀ = max |M| |σ|` and `x ∈ [-1,1]`,
`dZero3 M σ k x = d^{L₀+k}_{Mσ}(arccos x)` with no sign or transposition. -/
theorem dZero3_eq_wignerD (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (k : ℕ) :
    dZero3 M σ k x = wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x := by
  have hL0 : (0 : ℚ) ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hst := dZero3_start_eq_wignerD M σ α β hα hβ hx
  -- the second start
  have h1 : dZero3 M σ 1 x = wignerSmallDx (max |M| |σ| + ((1 : ℕ) : ℚ)) M σ x := by
    by_cases h0 : max |M| |σ| = 0
    · have hM : M = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_left _ _)
      have hs : σ = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_right _ _)
      subst hM hs
      rw [dZero3_one_zero]
      simp only [abs_zero, max_self, Nat.cast_one, zero_add]
      unfold wignerSmallDx
      rw [wignerSmallD_one_zero_zero, Real.cos_arccos hx.1 hx.2]
    · have hL : (0 : ℚ) < max |M| |σ| := lt_of_le_of_ne hL0 (Ne.symm h0)
      have hLr : ((max |M| |σ| : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      have hR : Rk M σ (max |M| |σ| + 1) ≠ 0 := (Rk_pos M σ _ (by linarith)).ne'
      -- row 0 for dZero3
      have hrow := ptilde3_rank_poly_row0 M σ ((1 - x) / 2) 0 h0
      have e : (1 : ℝ) - 2 * ((1 - x) / 2) = x := by ring
      rw [e] at hrow
      have hrowD : (2 * ((max |M| |σ| : ℚ) : ℝ) + 1) *
          (((max |M| |σ| : ℚ) : ℝ) * (((max |M| |σ| : ℚ) : ℝ) + 1) * x - (M : ℝ) * σ) *
            dZero3 M σ 0 x =
          ((max |M| |σ| : ℚ) : ℝ) * Rk M σ (max |M| |σ| + 1) * dZero3 M σ 1 x := by
        unfold dZero3
        linear_combination
          (Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ)) * hrow
      have hW := wignerSmallDx_rank_rec (max |M| |σ|) M σ hx
      rw [wigR_eq_Rk, Rk_L0, wigR_eq_Rk, zero_mul, mul_zero, zero_add] at hW
      have e1 : max |M| |σ| + ((1 : ℕ) : ℚ) = max |M| |σ| + 1 := by push_cast; ring
      rw [e1]
      refine mul_left_cancel₀ (mul_ne_zero hLr hR) ?_
      linear_combination (-1) * hrowD +
        ((2 * ((max |M| |σ| : ℚ) : ℝ) + 1) *
          (((max |M| |σ| : ℚ) : ℝ) * (((max |M| |σ| : ℚ) : ℝ) + 1) * x - (M : ℝ) * σ)) * hst + hW
  have hgen : ∀ k : ℕ, dZero3 M σ k x = wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x := by
    refine rec_seq_ext (fun k => dZero3 M σ k x)
      (fun k => wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x)
      (fun k => ((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
        Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1))
      (fun k => (2 * ((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
        (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
          (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) * x - (M : ℝ) * σ))
      (fun k => (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
        Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ)))
      (by simpa using hst) (by simpa using h1) ?_ ?_ ?_
    · intro k
      have hL : (0 : ℚ) < max |M| |σ| + ((k + 1 : ℕ) : ℚ) := by
        have : (0 : ℚ) < ((k + 1 : ℕ) : ℚ) := by positivity
        linarith
      have hLr : ((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      have hR : Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1) ≠ 0 := by
        apply (Rk_pos M σ _ _).ne'
        have : (0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
        linarith
      exact mul_ne_zero hLr hR
    · intro k
      have h := dZero3_rank_rec M σ k x
      show _ * dZero3 M σ (k + 2) x = _ * dZero3 M σ (k + 1) x - _ * dZero3 M σ k x
      linear_combination -h
    · intro k
      have hW := wignerSmallDx_rank_rec (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) M σ hx
      have e1 : wignerSmallDx (max |M| |σ| + ((k + 1 : ℕ) : ℚ) - 1) M σ x =
          wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x := by
        rw [show max |M| |σ| + ((k + 1 : ℕ) : ℚ) - 1 = max |M| |σ| + (k : ℚ) by push_cast; ring]
      have e2 : wignerSmallDx (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1) M σ x =
          wignerSmallDx (max |M| |σ| + ((k + 2 : ℕ) : ℚ)) M σ x := by
        rw [show max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1 = max |M| |σ| + ((k + 2 : ℕ) : ℚ) by
          push_cast; ring]
      rw [e1, e2, wigR_eq_Rk, wigR_eq_Rk] at hW
      show _ * wignerSmallDx (max |M| |σ| + ((k + 2 : ℕ) : ℚ)) M σ x =
        _ * wignerSmallDx (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) M σ x -
          _ * wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x
      linear_combination -hW
  exact hgen k

/-- **`thm:3jeven`, germ form**: `G(x, 0) = d^{L₀+k}_{Mσ}(arccos x)` for the closed-form germ `Gc3`. -/
theorem Gc3_zero_eq_wignerD (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (k : ℕ) :
    Gc3 M σ k x 0 = wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x := by
  rw [Gc3_zero, dZero3_eq_wignerD M σ α β hα hβ hx k]

/-- info: 'FormalResearch.Racah.dZero3_start_eq_wignerD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dZero3_start_eq_wignerD

/-- info: 'FormalResearch.Racah.dZero3_eq_wignerD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dZero3_eq_wignerD

/-- info: 'FormalResearch.Racah.Gc3_zero_eq_wignerD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gc3_zero_eq_wignerD

end FormalResearch.Racah
