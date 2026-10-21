import Mathlib

/-!
# Givens reduction of a real orthogonal `3×3` matrix

Every real orthogonal `3×3` matrix `Q` is brought to `1` or to `diag(1,1,-1)` by left multiplication
with a rotation in the plane of coordinates `(2,3)`, one in `(1,2)`, and one in `(2,3)` again.
-/

open scoped Matrix

namespace FormalResearch.FourQubitEntropy

/-- Rotation in the plane of coordinates `(1,2)` with cosine `p` and sine `q`. -/
def X3 (p q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j =>
  match i, j with
  | 0, 0 => p
  | 0, 1 => q
  | 1, 0 => -q
  | 1, 1 => p
  | 2, 2 => 1
  | _, _ => 0

/-- Rotation in the plane of coordinates `(2,3)` with cosine `p` and sine `q`. -/
def Y3 (p q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j =>
  match i, j with
  | 0, 0 => 1
  | 1, 1 => p
  | 1, 2 => q
  | 2, 1 => -q
  | 2, 2 => p
  | _, _ => 0

/-- The reflection of the third coordinate. -/
def F3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j =>
  match i, j with
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => -1
  | _, _ => 0

/-- Polar form of a real pair: a rotation of `(x, y)` onto the first axis. -/
theorem polar_pair (x y : ℝ) :
    ∃ p q r : ℝ, p ^ 2 + q ^ 2 = 1 ∧ 0 ≤ r ∧ p * x + q * y = r ∧ -q * x + p * y = 0 ∧
      r ^ 2 = x ^ 2 + y ^ 2 := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨1, 0, 0, by norm_num, le_refl _, by simp [hx, hy], by simp [hx, hy], by simp [hx, hy]⟩
  · have hpos : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    set r := Real.sqrt (x ^ 2 + y ^ 2) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hr2 : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hpos.le
    refine ⟨x / r, y / r, r, ?_, hr0.le, ?_, ?_, hr2⟩
    · field_simp; linarith
    · field_simp; nlinarith
    · field_simp; ring

/-- Half-angle parametrisation of a rotation. -/
theorem half_angle (p q : ℝ) (h : p ^ 2 + q ^ 2 = 1) :
    ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ p = a ^ 2 - b ^ 2 ∧ q = 2 * a * b := by
  by_cases hp : p = -1
  · have hq : q = 0 := by subst hp; nlinarith [sq_nonneg q]
    exact ⟨0, 1, by norm_num, by simp [hp], by simp [hq]⟩
  · have hp1 : 0 < 1 + p := by
      have : -1 ≤ p := by nlinarith [sq_nonneg q]
      exact lt_of_le_of_ne (by linarith) (fun h => hp (by linarith))
    set a := Real.sqrt ((1 + p) / 2) with ha
    have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
    have ha2 : a ^ 2 = (1 + p) / 2 := Real.sq_sqrt (by positivity)
    refine ⟨a, q / (2 * a), ?_, ?_, ?_⟩
    · field_simp; nlinarith
    · field_simp; nlinarith
    · field_simp

theorem X3_orth {p q : ℝ} (h : p ^ 2 + q ^ 2 = 1) : X3 p q * (X3 p q)ᵀ = 1 ∧ (X3 p q)ᵀ * X3 p q = 1 := by
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [X3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> nlinarith

theorem Y3_orth {p q : ℝ} (h : p ^ 2 + q ^ 2 = 1) : Y3 p q * (Y3 p q)ᵀ = 1 ∧ (Y3 p q)ᵀ * Y3 p q = 1 := by
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [Y3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> nlinarith

theorem orth_mul {A B : Matrix (Fin 3) (Fin 3) ℝ} (hA : A * Aᵀ = 1 ∧ Aᵀ * A = 1)
    (hB : B * Bᵀ = 1 ∧ Bᵀ * B = 1) : (A * B) * (A * B)ᵀ = 1 ∧ (A * B)ᵀ * (A * B) = 1 := by
  constructor
  · rw [Matrix.transpose_mul]
    calc A * B * (Bᵀ * Aᵀ) = A * (B * Bᵀ) * Aᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hB.1, Matrix.mul_one, hA.1]
  · rw [Matrix.transpose_mul]
    calc Bᵀ * Aᵀ * (A * B) = Bᵀ * (Aᵀ * A) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA.2, Matrix.mul_one, hB.2]

theorem Y3_mul_apply (p q : ℝ) (Q : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    (Y3 p q * Q) 0 j = Q 0 j ∧ (Y3 p q * Q) 1 j = p * Q 1 j + q * Q 2 j ∧
      (Y3 p q * Q) 2 j = -q * Q 1 j + p * Q 2 j := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Y3]

theorem X3_mul_apply (p q : ℝ) (Q : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    (X3 p q * Q) 0 j = p * Q 0 j + q * Q 1 j ∧ (X3 p q * Q) 1 j = -q * Q 0 j + p * Q 1 j ∧
      (X3 p q * Q) 2 j = Q 2 j := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three, X3]

/-- Givens reduction. -/
theorem euler3 (Q : Matrix (Fin 3) (Fin 3) ℝ) (h1 : Q * Qᵀ = 1) (h2 : Qᵀ * Q = 1) :
    ∃ p1 q1 p2 q2 p3 q3 : ℝ, p1 ^ 2 + q1 ^ 2 = 1 ∧ p2 ^ 2 + q2 ^ 2 = 1 ∧ p3 ^ 2 + q3 ^ 2 = 1 ∧
      (Y3 p3 q3 * X3 p2 q2 * Y3 p1 q1 * Q = 1 ∨ Y3 p3 q3 * X3 p2 q2 * Y3 p1 q1 * Q = F3) := by
  have hc0 : Q 0 0 ^ 2 + Q 1 0 ^ 2 + Q 2 0 ^ 2 = 1 := by
    have := congrFun (congrFun h2 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at this
    nlinarith
  obtain ⟨p1, q1, r1, hn1, hr1, e1, e1', hr1sq⟩ := polar_pair (Q 1 0) (Q 2 0)
  obtain ⟨p2, q2, ρ, hn2, hρ, e2, e2', hρsq⟩ := polar_pair (Q 0 0) r1
  have hρ1 : ρ = 1 := by
    have : ρ ^ 2 = 1 := by rw [hρsq, hr1sq]; linarith
    nlinarith
  set Q2 : Matrix (Fin 3) (Fin 3) ℝ := X3 p2 q2 * (Y3 p1 q1 * Q) with hQ2
  have horth : Q2 * Q2ᵀ = 1 ∧ Q2ᵀ * Q2 = 1 :=
    orth_mul (X3_orth hn2) (orth_mul (Y3_orth hn1) ⟨h1, h2⟩)
  have c00 : Q2 0 0 = 1 := by
    rw [hQ2, (X3_mul_apply _ _ _ 0).1, (Y3_mul_apply _ _ _ 0).1, (Y3_mul_apply _ _ _ 0).2.1, e1]
    linarith
  have c10 : Q2 1 0 = 0 := by
    rw [hQ2, (X3_mul_apply _ _ _ 0).2.1, (Y3_mul_apply _ _ _ 0).1, (Y3_mul_apply _ _ _ 0).2.1, e1]
    linarith
  have c20 : Q2 2 0 = 0 := by
    rw [hQ2, (X3_mul_apply _ _ _ 0).2.2, (Y3_mul_apply _ _ _ 0).2.2]
    linarith
  clear_value Q2
  -- orthogonality relations of `Q2`
  have r0 := congrFun (congrFun horth.1 0) 0
  have r1' := congrFun (congrFun horth.1 1) 1
  have r2' := congrFun (congrFun horth.1 2) 2
  have r12 := congrFun (congrFun horth.1 1) 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply] at r0 r1' r2' r12
  simp at r0 r1' r2' r12
  rw [c00] at r0
  have q01 : Q2 0 1 = 0 := by
    have h : Q2 0 1 ^ 2 = 0 := by nlinarith only [r0, sq_nonneg (Q2 0 1), sq_nonneg (Q2 0 2)]
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h
  have q02 : Q2 0 2 = 0 := by
    have h : Q2 0 2 ^ 2 = 0 := by nlinarith only [r0, sq_nonneg (Q2 0 1), sq_nonneg (Q2 0 2)]
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h
  rw [c10] at r1' r12
  rw [c20] at r2' r12
  set e := Q2 1 1 with he
  set f := Q2 1 2 with hf
  set h := Q2 2 1 with hh
  set i := Q2 2 2 with hi
  have hef : e * e + f * f = 1 := by linarith
  have hhi : h * h + i * i = 1 := by linarith
  have hdot : e * h + f * i = 0 := by linarith
  have hlam2 : (i * e - h * f) ^ 2 = 1 := by
    linear_combination (h * h + i * i) * hef + hhi - (e * h + f * i) * hdot
  have hh' : h = -(i * e - h * f) * f := by linear_combination e * hdot - h * hef
  have hi' : i = (i * e - h * f) * e := by linear_combination f * hdot - i * hef
  have hprod : ∀ p3 q3 : ℝ, Y3 p3 q3 * X3 p2 q2 * Y3 p1 q1 * Q = Y3 p3 q3 * Q2 := by
    intro p3 q3; rw [hQ2]; simp only [Matrix.mul_assoc]
  have hrow0 : ∀ j, Q2 0 j = if j = 0 then 1 else 0 := by
    intro j; fin_cases j <;> simp [c00, q01, q02]
  have hcol0 : ∀ j, Q2 j 0 = if j = 0 then 1 else 0 := by
    intro j; fin_cases j <;> simp [c00, c10, c20]
  have hlamcases : (i * e - h * f) = 1 ∨ (i * e - h * f) = -1 := by
    have : (i * e - h * f - 1) * (i * e - h * f + 1) = 0 := by linear_combination hlam2
    rcases mul_eq_zero.1 this with h0 | h0
    · left; linarith
    · right; linarith
  refine ⟨p1, q1, p2, q2, ?_⟩
  have hent : ∀ p q : ℝ, ∀ a b : Fin 3, (Y3 p q * Q2) a b =
      (if a = 0 then Q2 0 b else if a = 1 then p * Q2 1 b + q * Q2 2 b else -q * Q2 1 b + p * Q2 2 b) := by
    intro p q a b
    fin_cases a
    · simp [(Y3_mul_apply p q Q2 b).1]
    · simp [(Y3_mul_apply p q Q2 b).2.1]
    · simp [(Y3_mul_apply p q Q2 b).2.2]
  have hQ21 : Q2 1 1 = e := he.symm
  have hQ22 : Q2 1 2 = f := hf.symm
  have hQ31 : Q2 2 1 = h := hh.symm
  have hQ32 : Q2 2 2 = i := hi.symm
  rcases hlamcases with hl | hl
  · have hh1 : h = -f := by rw [hl] at hh'; linarith
    have hi1 : i = e := by rw [hl] at hi'; linarith
    refine ⟨e, -f, hn1, hn2, by linear_combination hef, Or.inl ?_⟩
    rw [hprod]
    ext a b
    rw [hent]
    fin_cases a <;> fin_cases b <;>
    simp [hrow0, hcol0, Matrix.one_apply, hQ21, hQ22, hQ31, hQ32, hh1, hi1] <;>
    first | linarith | nlinarith only [hef]
  · have hh1 : h = f := by rw [hl] at hh'; linarith
    have hi1 : i = -e := by rw [hl] at hi'; linarith
    refine ⟨e, f, hn1, hn2, by linear_combination hef, Or.inr ?_⟩
    rw [hprod]
    ext a b
    rw [hent]
    fin_cases a <;> fin_cases b <;>
    simp [hrow0, hcol0, F3, hQ21, hQ22, hQ31, hQ32, hh1, hi1] <;>
    first | linarith | nlinarith only [hef]

end FormalResearch.FourQubitEntropy
