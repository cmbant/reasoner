import Mathlib

namespace FormalResearch.QIB

/-!
# Kempf--Ness criticality does not force `F_C = F_K` (`prop:criticalcounter`)

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, `prop:criticalcounter`.

Torus weights `(-2,-1,1,2)` on `ℂ⁴`, with
`x = (1, √3, √3, 1)/√8` and `y = (1, √3, √3, -1)/√8`.  We prove, with no numerics:

* both are unit vectors and critical (zero moment map `∑ wⱼ |zⱼ|² = 0`);
* the compact overlap `|⟨x, U(φ) y⟩|²` with `U(φ) = diag(e^{i wⱼ φ})` equals
  `(13 cos²φ - 4 cos⁴φ)/16`, so its maximum over the compact torus is attained and equals `9/16`;
* the positive filter `g = diag(e^{t wⱼ})` with `e^t = 3/4` (`t = log (3/4)`) gives
  `|⟨x, g y⟩|² / ‖g y‖² = 1155625/1741448 > 9/16`.

The inner product is `⟨u, v⟩ = ∑ conj(uⱼ) vⱼ` on `Fin 4 → ℂ`, written out explicitly.
-/

open scoped ComplexConjugate

namespace CriticalCounter

/-- Torus weights `(-2,-1,1,2)`. -/
def w : Fin 4 → ℝ := ![-2, -1, 1, 2]

/-- Hermitian inner product on `Fin 4 → ℂ` (conjugate-linear in the first slot). -/
def ip (u v : Fin 4 → ℂ) : ℂ := ∑ j, conj (u j) * v j

/-- Squared norm. -/
def nsq (u : Fin 4 → ℂ) : ℝ := ∑ j, Complex.normSq (u j)

/-- Real amplitude vector `x = (1, √3, √3, 1)/√8`. -/
noncomputable def xr : Fin 4 → ℝ := fun j => ![1, √3, √3, 1] j / √8
/-- Real amplitude vector `y = (1, √3, √3, -1)/√8`. -/
noncomputable def yr : Fin 4 → ℝ := fun j => ![1, √3, √3, -1] j / √8

/-- The state `x`. -/
noncomputable def x : Fin 4 → ℂ := fun j => ((xr j : ℝ) : ℂ)
/-- The state `y`. -/
noncomputable def y : Fin 4 → ℂ := fun j => ((yr j : ℝ) : ℂ)

/-- Compact torus element `U(φ) = diag (e^{i wⱼ φ})`. -/
noncomputable def torus (φ : ℝ) (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun j => Complex.exp (((w j * φ : ℝ) : ℂ) * Complex.I) * v j

/-- Positive complexified filter `g_t = diag (e^{t wⱼ})`. -/
noncomputable def filt (t : ℝ) (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun j => ((Real.exp (t * w j) : ℝ) : ℂ) * v j

lemma sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma sqrt8_sq : (√8 : ℝ) ^ 2 = 8 := Real.sq_sqrt (by norm_num)

lemma xr_sq : ∀ j, xr j ^ 2 = ![1/8, 3/8, 3/8, 1/8] j := by
  intro j
  have h3 := sqrt3_sq
  have h8 := sqrt8_sq
  have h8' : (√8 : ℝ) ≠ 0 := by positivity
  fin_cases j <;> simp [xr, div_pow, h3, h8]

lemma yr_sq : ∀ j, yr j ^ 2 = ![1/8, 3/8, 3/8, 1/8] j := by
  intro j
  have h3 := sqrt3_sq
  have h8 := sqrt8_sq
  fin_cases j <;> simp [yr, div_pow, h3, h8]

/-- Products `xⱼ yⱼ = (1, 3, 3, -1)/8`. -/
lemma xr_mul_yr : ∀ j, xr j * yr j = ![1/8, 3/8, 3/8, -1/8] j := by
  intro j
  have h3 := sqrt3_sq
  have h8 := sqrt8_sq
  have h8' : (√8 : ℝ) ≠ 0 := by positivity
  fin_cases j
  · simp [xr, yr]; field_simp; linarith
  · simp [xr, yr]; field_simp; linarith
  · simp [xr, yr]; field_simp; linarith
  · simp [xr, yr]; field_simp; linarith

lemma nsq_x : nsq x = 1 := by
  simp only [nsq, x, Complex.normSq_ofReal, Fin.sum_univ_four]
  simp only [← sq]
  rw [xr_sq 0, xr_sq 1, xr_sq 2, xr_sq 3]; norm_num

lemma nsq_y : nsq y = 1 := by
  simp only [nsq, y, Complex.normSq_ofReal, Fin.sum_univ_four]
  simp only [← sq]
  rw [yr_sq 0, yr_sq 1, yr_sq 2, yr_sq 3]; norm_num

/-- `x` is critical: its moment map `∑ wⱼ |xⱼ|²` vanishes. -/
theorem moment_x : ∑ j, w j * Complex.normSq (x j) = 0 := by
  simp only [x, Complex.normSq_ofReal, Fin.sum_univ_four]
  simp only [← sq]
  rw [xr_sq 0, xr_sq 1, xr_sq 2, xr_sq 3]; simp [w]

/-- `y` is critical: its moment map `∑ wⱼ |yⱼ|²` vanishes. -/
theorem moment_y : ∑ j, w j * Complex.normSq (y j) = 0 := by
  simp only [y, Complex.normSq_ofReal, Fin.sum_univ_four]
  simp only [← sq]
  rw [yr_sq 0, yr_sq 1, yr_sq 2, yr_sq 3]; simp [w]

/-- Overlap of `x` with the compact torus orbit of `y`, as a trigonometric polynomial. -/
lemma compact_overlap_eq (φ : ℝ) :
    Complex.normSq (ip x (torus φ y)) = (13 * Real.cos φ ^ 2 - 4 * Real.cos φ ^ 4) / 16 := by
  have key : ∀ j, conj (x j) * torus φ y j
      = ((xr j * yr j * Real.cos (w j * φ) : ℝ) : ℂ)
        + ((xr j * yr j * Real.sin (w j * φ) : ℝ) : ℂ) * Complex.I := by
    intro j
    simp only [x, y, torus, Complex.conj_ofReal]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  have hip : ip x (torus φ y)
      = ((∑ j, xr j * yr j * Real.cos (w j * φ) : ℝ) : ℂ)
        + ((∑ j, xr j * yr j * Real.sin (w j * φ) : ℝ) : ℂ) * Complex.I := by
    simp only [ip, key, Finset.sum_add_distrib, ← Finset.sum_mul]
    push_cast; rfl
  rw [hip, Complex.normSq_add_mul_I]
  simp only [Fin.sum_univ_four, xr_mul_yr, w]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have c2 := Real.cos_two_mul φ
  have s2 := Real.sin_two_mul φ
  have pyth := Real.sin_sq_add_cos_sq φ
  have e1 : (-2 : ℝ) * φ = -(2 * φ) := by ring
  have e2 : (-1 : ℝ) * φ = -φ := by ring
  simp only [e1, e2, one_mul, Real.cos_neg, Real.sin_neg, s2]
  linear_combination (Real.cos φ ^ 2 / 4) * pyth

/-- The compact overlap `max_φ |⟨x, U(φ) y⟩|²` over the torus is attained and equals `9/16`
(`F_K = 9/16`). -/
theorem compact_overlap_max :
    IsGreatest (Set.range fun φ : ℝ => Complex.normSq (ip x (torus φ y))) (9 / 16) := by
  constructor
  · refine ⟨0, ?_⟩
    simp only [compact_overlap_eq, Real.cos_zero]
    norm_num
  · rintro _ ⟨φ, rfl⟩
    show Complex.normSq (ip x (torus φ y)) ≤ 9 / 16
    rw [compact_overlap_eq]
    have h1 : Real.cos φ ^ 2 ≤ 1 := Real.cos_sq_le_one φ
    have h0 : 0 ≤ Real.cos φ ^ 2 := sq_nonneg _
    have h4 : Real.cos φ ^ 4 = (Real.cos φ ^ 2) ^ 2 := by ring
    rw [h4]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ 9 - 4 * Real.cos φ ^ 2)]

/-- `F_K = sSup_φ |⟨x, U(φ) y⟩|² = 9/16`. -/
theorem FK_eq : sSup (Set.range fun φ : ℝ => Complex.normSq (ip x (torus φ y))) = 9 / 16 :=
  compact_overlap_max.csSup_eq

/-- The filter parameter `t = log (3/4)`, so `e^t = 3/4`. -/
noncomputable def t0 : ℝ := Real.log (3 / 4)

lemma exp_t0 : Real.exp t0 = 3 / 4 := Real.exp_log (by norm_num)

/-- The filter weights `e^{t wⱼ} = (16/9, 4/3, 3/4, 9/16)`. -/
lemma filt_weights : ∀ j, Real.exp (t0 * w j) = ![16 / 9, 4 / 3, 3 / 4, 9 / 16] j := by
  intro j
  have h := exp_t0
  fin_cases j
  · have : t0 * w 0 = -(t0 + t0) := by simp [w]; ring
    simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [this, Real.exp_neg, Real.exp_add, h]; norm_num
  · have : t0 * w 1 = -t0 := by simp [w]
    simp only [Fin.mk_one, Matrix.cons_val_one]
    rw [this, Real.exp_neg, h]; norm_num
  · have : t0 * w 2 = t0 := by simp [w]
    simp [this, h]
  · have : t0 * w 3 = t0 + t0 := by simp [w]; ring
    simp [this, Real.exp_add, h]; norm_num

/-- The numerator `|⟨x, g_t y⟩|² = (1075/1152)²`. -/
lemma filt_overlap : Complex.normSq (ip x (filt t0 y)) = (1075 / 1152) ^ 2 := by
  have key : ∀ j, conj (x j) * filt t0 y j
      = ((xr j * yr j * Real.exp (t0 * w j) : ℝ) : ℂ) := by
    intro j
    simp only [x, y, filt, Complex.conj_ofReal]
    push_cast; ring
  have hip : ip x (filt t0 y) = ((∑ j, xr j * yr j * Real.exp (t0 * w j) : ℝ) : ℂ) := by
    simp only [ip, key]; push_cast; rfl
  rw [hip, Complex.normSq_ofReal]
  simp only [Fin.sum_univ_four, xr_mul_yr, filt_weights]
  norm_num

/-- The denominator `‖g_t y‖² = 217681/165888`. -/
lemma filt_nsq : nsq (filt t0 y) = 217681 / 165888 := by
  have key : ∀ j, Complex.normSq (filt t0 y j)
      = Real.exp (t0 * w j) ^ 2 * yr j ^ 2 := by
    intro j
    simp only [y, filt, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  simp only [nsq, key, Fin.sum_univ_four, yr_sq, filt_weights]
  norm_num

/-- **`prop:criticalcounter`, filter part.**  The positive filter `g_t = diag(e^{t wⱼ})`,
`e^t = 3/4`, gives `|⟨x, g_t y⟩|² / ‖g_t y‖² = 1155625/1741448`, which exceeds `F_K = 9/16`. -/
theorem filter_ratio :
    Complex.normSq (ip x (filt t0 y)) / nsq (filt t0 y) = 1155625 / 1741448 := by
  rw [filt_overlap, filt_nsq]; norm_num

theorem filter_ratio_gt_FK :
    sSup (Set.range fun φ : ℝ => Complex.normSq (ip x (torus φ y)))
      < Complex.normSq (ip x (filt t0 y)) / nsq (filt t0 y) := by
  rw [FK_eq, filter_ratio]; norm_num

/-- **`prop:criticalcounter`** (summary): `x`, `y` are unit vectors with vanishing moment map,
`F_K = 9/16` is attained, and the filter ratio is `1155625/1741448 > 9/16`. -/
theorem critical_counterexample :
    nsq x = 1 ∧ nsq y = 1 ∧
    (∑ j, w j * Complex.normSq (x j) = 0) ∧ (∑ j, w j * Complex.normSq (y j) = 0) ∧
    IsGreatest (Set.range fun φ : ℝ => Complex.normSq (ip x (torus φ y))) (9 / 16) ∧
    Complex.normSq (ip x (filt t0 y)) / nsq (filt t0 y) = 1155625 / 1741448 ∧
    (9 / 16 : ℝ) < 1155625 / 1741448 :=
  ⟨nsq_x, nsq_y, moment_x, moment_y, compact_overlap_max, filter_ratio, by norm_num⟩

end CriticalCounter

end FormalResearch.QIB
