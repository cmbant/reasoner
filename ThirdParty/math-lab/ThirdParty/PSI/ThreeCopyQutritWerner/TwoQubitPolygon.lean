module

public import Mathlib

@[expose] public section


/-! Exact complex phases for four nonnegative lengths satisfying the polygon
inequalities. This is the constructive scalar step in the two-qubit PPT route;
no separability, spectral decomposition, or numerical approximation is assumed. -/
noncomputable section
open scoped BigOperators
namespace ThreeCopyQutritWerner

/-- Two planar vectors with prescribed lengths and a prescribed real sum.
The degenerate zero-resultant case is included. -/
theorem complex_pair_of_triangle (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hlo : |a - b| ≤ c) (hhi : c ≤ a + b) :
    ∃ z w : ℂ, Complex.normSq z = a ^ 2 ∧ Complex.normSq w = b ^ 2 ∧
      z + w = (c : ℂ) := by
  rcases eq_or_lt_of_le hc with hzero | hpos
  · have hab : a = b := by
      have := abs_le.mp hlo
      rw [← hzero] at this
      linarith
    subst c
    refine ⟨(a : ℂ), (-a : ℂ), ?_, ?_, ?_⟩
    · simp [Complex.normSq_apply, pow_two]
    · simp [Complex.normSq_apply, pow_two, hab]
    · simp
  · let x := (c ^ 2 + a ^ 2 - b ^ 2) / (2 * c)
    have hc2 : 0 < 2 * c := by positivity
    have heq : 2 * c * x = c ^ 2 + a ^ 2 - b ^ 2 := by
      dsimp [x]
      field_simp [ne_of_gt hpos]
    have hlo' := abs_le.mp hlo
    have hl : -a ≤ x := by
      have hp : 0 ≤ (c + a - b) * (c + a + b) :=
        mul_nonneg (by linarith) (by positivity)
      have hm : 0 ≤ (2 * c) * (x + a) := by nlinarith
      have := (mul_nonneg_iff_of_pos_left hc2).mp hm
      linarith
    have hu : x ≤ a := by
      have hp : 0 ≤ (b - c + a) * (b + c - a) :=
        mul_nonneg (by linarith) (by linarith)
      have hm : 0 ≤ (2 * c) * (a - x) := by nlinarith
      have := (mul_nonneg_iff_of_pos_left hc2).mp hm
      linarith
    have hs : 0 ≤ a ^ 2 - x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ a + x)]
    let y := Real.sqrt (a ^ 2 - x ^ 2)
    have hy : y ^ 2 = a ^ 2 - x ^ 2 := Real.sq_sqrt hs
    refine ⟨⟨x, y⟩, ⟨c - x, -y⟩, ?_, ?_, ?_⟩
    · simp only [Complex.normSq_apply]
      nlinarith
    · simp only [Complex.normSq_apply]
      nlinarith
    · apply Complex.ext <;> simp

/-- The four polygon inequalities give four complex vectors of the specified
lengths whose literal sum is zero. No ordering or strict positivity is needed. -/
theorem complex_four_of_polygon (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : a ≤ b + c + d) (hB : b ≤ a + c + d)
    (hC : c ≤ a + b + d) (hD : d ≤ a + b + c) :
    ∃ z : Fin 4 → ℂ, (∀ i, Complex.normSq (z i) = (![a, b, c, d] i) ^ 2) ∧
      ∑ i, z i = 0 := by
  let t := max |a - b| |c - d|
  have ht : 0 ≤ t := le_trans (abs_nonneg _) (le_max_left _ _)
  have htab : t ≤ a + b := by
    apply max_le
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htcd : t ≤ c + d := by
    apply max_le
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨u, v, hu, hv, huv⟩ :=
    complex_pair_of_triangle a b t ha hb ht (le_max_left _ _) htab
  obtain ⟨w, x, hw, hx, hwx⟩ :=
    complex_pair_of_triangle c d t hc hd ht (le_max_right _ _) htcd
  refine ⟨![u, v, -w, -x], ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
    · simpa using hw
    · simpa using hx
  · simp only [Fin.sum_univ_succ, Fin.reduceSucc, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    linear_combination huv - hwx

/-- Every complex vector of squared norm a² has the form a times the square
of a unit complex phase. At a=0 the phase is chosen to be one. -/
theorem complex_unit_square_phase (a : ℝ) (ha : 0 ≤ a) (z : ℂ)
    (hz : Complex.normSq z = a ^ 2) :
    ∃ p : ℂ, Complex.normSq p = 1 ∧ (a : ℂ) * p ^ 2 = z := by
  by_cases hzero : a = 0
  · subst a
    have hz0 : z = 0 := Complex.normSq_eq_zero.mp (by simpa using hz)
    exact ⟨1, by simp, by simp [hz0]⟩
  · have haC : (a : ℂ) ≠ 0 := by exact_mod_cast hzero
    obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq (z / (a : ℂ)) (by decide : 0 < 2)
    refine ⟨p, ?_, ?_⟩
    · have hnorm : Complex.normSq (p ^ 2) = 1 := by
        rw [hp, map_div₀]
        simp only [Complex.normSq_ofReal, hz, ← pow_two]
        exact div_self (pow_ne_zero 2 hzero)
      rw [map_pow] at hnorm
      nlinarith [Complex.normSq_nonneg p]
    · rw [hp]
      field_simp

/-- Unit phases whose weighted squares cancel; this feeds the literal
Hadamard ensemble construction. -/
theorem complex_unit_phases_of_polygon (a : Fin 4 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hpoly : ∀ i, 2 * a i ≤ ∑ j, a j) :
    ∃ p : Fin 4 → ℂ, (∀ i, Complex.normSq (p i) = 1) ∧
      ∑ i, (a i : ℂ) * (p i) ^ 2 = 0 := by
  have hs : ∑ i, a i = a 0 + a 1 + a 2 + a 3 := by
    simp only [Fin.sum_univ_succ, Fin.reduceSucc, Fin.sum_univ_zero, add_zero]
    ring
  have h0 := hpoly 0
  have h1 := hpoly 1
  have h2 := hpoly 2
  have h3 := hpoly 3
  rw [hs] at h0 h1 h2 h3
  obtain ⟨z, hz, hsum⟩ := complex_four_of_polygon (a 0) (a 1) (a 2) (a 3)
    (ha 0) (ha 1) (ha 2) (ha 3) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have hza : ∀ i, Complex.normSq (z i) = (a i) ^ 2 := by
    intro i
    fin_cases i
    · simpa using hz 0
    · simpa using hz 1
    · simpa using hz 2
    · simpa using hz 3
  choose p hp hpa using fun i => complex_unit_square_phase (a i) (ha i) (z i) (hza i)
  refine ⟨p, hp, ?_⟩
  simpa only [hpa] using hsum

end ThreeCopyQutritWerner
