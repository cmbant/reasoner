module

public import FormalResearch.Jacobi.Basic

/-!
# Combes–Thomas weighted resolvent estimate for degree-two (Jacobi-type) matrices

The shared analytic core of Theorem DB.1 (Weyl P5 `dirichlet_block_audit.md`) and of the W1
programme's Combes–Thomas lemma: if `A` is a real symmetric matrix with bounded off-diagonal entries
and at most two nonzero off-diagonal entries per row (a Jacobi matrix, a Dirichlet block of one, or
any path/cycle matrix), `A - λ` has the coercive lower bound `‖(A-λ)x‖ ≥ Δ‖x‖`, and `u` solves
`(A - λ) u = f`, then for every weight `φ` with `|φ_i - φ_j| ≤ μ` along nonzero links and
`2M(e^μ - 1) ≤ Δ/2`,

`∑ e^{2φ_i} u_i² ≤ (4/Δ²) ∑ e^{2φ_i} f_i²`.

Proof (as in the note): `W = diag e^φ`, `E = W A W⁻¹ - A` has entries `A_ij (e^{φ_i-φ_j} - 1)`, every
absolute row and column sum is at most `2M (e^μ - 1) ≤ Δ/2` (Schur test), so
`‖(A - λ + E) y‖ ≥ (Δ/2) ‖y‖` for `y = W u`, and `(A - λ + E) W u = W f`.

* `LocalBound A M` : symmetric, `|A_ij| ≤ M` off the diagonal, at most two nonzero off-diagonal
  entries per row.
* `schur_sq` : the Schur test `‖E y‖² ≤ δ² ‖y‖²` from row and column `ℓ¹` bounds.
* `weighted_resolvent` : the estimate above (the generic Combes–Thomas lemma for such matrices).
* `jacobiMatrix_localBound` : `jacobiMatrix n b a` is `LocalBound` with `M = sup |a_j|`.

Claim class: proved.  Not formalised: the Combes–Thomas lemma for matrices of larger bandwidth or in
higher dimension (here the degree-two hypothesis is used to bound row and column sums by `2M(e^μ-1)`).
-/

@[expose] public section

namespace FormalResearch.Jacobi

open Matrix Finset Real

section CT

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Symmetric matrix with off-diagonal entries bounded by `M` and at most two nonzero off-diagonal
entries in every row. -/
structure LocalBound (A : Matrix κ κ ℝ) (M : ℝ) : Prop where
  symm : ∀ i j, A i j = A j i
  bound : ∀ i j, i ≠ j → |A i j| ≤ M
  deg : ∀ i, (univ.filter fun j => j ≠ i ∧ A i j ≠ 0).card ≤ 2

omit [DecidableEq κ] in
/-- Minkowski inequality for sums of squares. -/
theorem sqrt_sum_sq_add_le (x y : κ → ℝ) :
    √(∑ i, (x i + y i) ^ 2) ≤ √(∑ i, x i ^ 2) + √(∑ i, y i ^ 2) := by
  have := norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simpa [EuclideanSpace.norm_eq] using this

omit [DecidableEq κ] in
/-- Schur test: `‖E y‖² ≤ δ² ‖y‖²` if every absolute row and column sum of `E` is at most `δ`. -/
theorem schur_sq (E : Matrix κ κ ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hrow : ∀ i, ∑ j, |E i j| ≤ δ)
    (hcol : ∀ j, ∑ i, |E i j| ≤ δ) (y : κ → ℝ) :
    ∑ i, (E *ᵥ y) i ^ 2 ≤ δ ^ 2 * ∑ j, y j ^ 2 := by
  have h1 : ∀ i, (E *ᵥ y) i ^ 2 ≤ δ * ∑ j, |E i j| * y j ^ 2 := by
    intro i
    have := sum_sq_le_sum_mul_sum_of_sq_le_mul (s := univ) (r := fun j => E i j * y j)
      (f := fun j => |E i j|) (g := fun j => |E i j| * y j ^ 2) (fun j _ => abs_nonneg _)
      (fun j _ => by positivity) (fun j _ => le_of_eq (by
        rw [mul_pow, ← sq_abs (E i j)]; ring))
    calc (E *ᵥ y) i ^ 2 = (∑ j, E i j * y j) ^ 2 := by simp [mulVec, dotProduct]
      _ ≤ (∑ j, |E i j|) * ∑ j, |E i j| * y j ^ 2 := this
      _ ≤ δ * ∑ j, |E i j| * y j ^ 2 :=
        mul_le_mul_of_nonneg_right (hrow i) (sum_nonneg fun j _ => by positivity)
  calc ∑ i, (E *ᵥ y) i ^ 2 ≤ ∑ i, δ * ∑ j, |E i j| * y j ^ 2 := sum_le_sum fun i _ => h1 i
    _ = δ * ∑ j, y j ^ 2 * ∑ i, |E i j| := by
        rw [← mul_sum, sum_comm]
        congr 1
        exact sum_congr rfl fun j _ => by rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    _ ≤ δ * ∑ j, y j ^ 2 * δ :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg _)) hδ
    _ = δ ^ 2 * ∑ j, y j ^ 2 := by rw [← sum_mul]; ring

theorem abs_exp_sub_one_le {t μ : ℝ} (h : |t| ≤ μ) : |exp t - 1| ≤ exp μ - 1 := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg (sub_nonneg.mpr (one_le_exp ht))]
    have := exp_le_exp.mpr ((le_abs_self t).trans h)
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (exp_le_one_iff.mpr ht))]
    have h2 : exp (-t) ≤ exp μ := exp_le_exp.mpr ((neg_le_abs t).trans h)
    have h3 : exp t * exp (-t) = 1 := by rw [← exp_add]; simp
    have h4 : 0 < exp t := exp_pos t
    have h5 : 2 ≤ exp t + exp (-t) := by nlinarith [sq_nonneg (exp t - exp (-t)), exp_pos (-t)]
    linarith

variable {A : Matrix κ κ ℝ} {M : ℝ}

/-- Row sums of the Combes–Thomas error `E_ij = A_ij (e^{φ_i - φ_j} - 1)`. -/
theorem LocalBound.sum_abs_E_row (hA : LocalBound A M) (hM : 0 ≤ M) {μ : ℝ} (hμ : 0 ≤ μ)
    {φ : κ → ℝ} (hφ : ∀ i j, i ≠ j → A i j ≠ 0 → |φ i - φ j| ≤ μ) (i : κ) :
    ∑ j, |A i j * (exp (φ i - φ j) - 1)| ≤ 2 * M * (exp μ - 1) := by
  have hexp : 0 ≤ exp μ - 1 := sub_nonneg.mpr (one_le_exp hμ)
  have hterm : ∀ j, |A i j * (exp (φ i - φ j) - 1)| ≤
      if j ≠ i ∧ A i j ≠ 0 then M * (exp μ - 1) else 0 := by
    intro j
    split_ifs with h
    · rw [abs_mul]
      exact mul_le_mul (hA.bound i j (Ne.symm h.1)) (abs_exp_sub_one_le (hφ i j (Ne.symm h.1) h.2))
        (abs_nonneg _) hM
    · by_cases hji : j = i
      · subst hji; simp
      · have : A i j = 0 := by by_contra h'; exact h ⟨hji, h'⟩
        simp [this]
  calc ∑ j, |A i j * (exp (φ i - φ j) - 1)|
      ≤ ∑ j, (if j ≠ i ∧ A i j ≠ 0 then M * (exp μ - 1) else 0) := sum_le_sum fun j _ => hterm j
    _ = (univ.filter fun j => j ≠ i ∧ A i j ≠ 0).card * (M * (exp μ - 1)) := by
        rw [← sum_filter]; simp
    _ ≤ 2 * (M * (exp μ - 1)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hA.deg i) (mul_nonneg hM hexp)
    _ = 2 * M * (exp μ - 1) := by ring

/-- Column sums of the error: the same bound, by symmetry of `A`. -/
theorem LocalBound.sum_abs_E_col (hA : LocalBound A M) (hM : 0 ≤ M) {μ : ℝ} (hμ : 0 ≤ μ)
    {φ : κ → ℝ} (hφ : ∀ i j, i ≠ j → A i j ≠ 0 → |φ i - φ j| ≤ μ) (j : κ) :
    ∑ i, |A i j * (exp (φ i - φ j) - 1)| ≤ 2 * M * (exp μ - 1) := by
  have hexp : 0 ≤ exp μ - 1 := sub_nonneg.mpr (one_le_exp hμ)
  have hterm : ∀ i, |A i j * (exp (φ i - φ j) - 1)| ≤
      if i ≠ j ∧ A j i ≠ 0 then M * (exp μ - 1) else 0 := by
    intro i
    split_ifs with h
    · rw [abs_mul]
      have hAij : A i j ≠ 0 := by rw [hA.symm i j]; exact h.2
      exact mul_le_mul (hA.bound i j h.1) (abs_exp_sub_one_le (hφ i j h.1 hAij))
        (abs_nonneg _) hM
    · by_cases hij : i = j
      · subst hij; simp
      · have : A j i = 0 := by by_contra h'; exact h ⟨hij, h'⟩
        rw [hA.symm i j, this]; simp
  calc ∑ i, |A i j * (exp (φ i - φ j) - 1)|
      ≤ ∑ i, (if i ≠ j ∧ A j i ≠ 0 then M * (exp μ - 1) else 0) := sum_le_sum fun i _ => hterm i
    _ = (univ.filter fun i => i ≠ j ∧ A j i ≠ 0).card * (M * (exp μ - 1)) := by
        rw [← sum_filter]; simp
    _ ≤ 2 * (M * (exp μ - 1)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hA.deg j) (mul_nonneg hM hexp)
    _ = 2 * M * (exp μ - 1) := by ring

/-- **Combes–Thomas weighted resolvent estimate** (the generic core of DB.1).
Let `A` be `LocalBound` with constant `M ≥ 0`, let `A - λ` be coercive,
`Δ² ∑ x² ≤ ∑ ((A - λ)x)²`, and let `(A - λ) u = f`.  If `φ` varies by at most `μ` along nonzero
links, where `2 M (e^μ - 1) ≤ Δ/2`, then `∑ e^{2φ} u² ≤ (4/Δ²) ∑ e^{2φ} f²`. -/
theorem weighted_resolvent (hA : LocalBound A M) (hM : 0 ≤ M) {lam Δ μ : ℝ} (hΔ : 0 < Δ)
    (hμ : 0 ≤ μ) (hμΔ : 2 * M * (exp μ - 1) ≤ Δ / 2)
    (hgap : ∀ x : κ → ℝ, Δ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ i, ((A *ᵥ x) i - lam * x i) ^ 2)
    {φ : κ → ℝ} (hφ : ∀ i j, i ≠ j → A i j ≠ 0 → |φ i - φ j| ≤ μ) {u f : κ → ℝ}
    (hf : ∀ i, (A *ᵥ u) i - lam * u i = f i) :
    ∑ i, exp (2 * φ i) * u i ^ 2 ≤ 4 / Δ ^ 2 * ∑ i, exp (2 * φ i) * f i ^ 2 := by
  set y : κ → ℝ := fun i => exp (φ i) * u i with hy
  set E : Matrix κ κ ℝ := Matrix.of fun i j => A i j * (exp (φ i - φ j) - 1) with hE
  have hδ : 0 ≤ Δ / 2 := by positivity
  have hEy : ∑ i, (E *ᵥ y) i ^ 2 ≤ (Δ / 2) ^ 2 * ∑ j, y j ^ 2 :=
    schur_sq E hδ (fun i => (hA.sum_abs_E_row hM hμ hφ i).trans hμΔ)
      (fun j => (hA.sum_abs_E_col hM hμ hφ j).trans hμΔ) y
  -- identity `(A y - λ y)_i = e^{φ_i} f_i - (E y)_i`
  have hid : ∀ i, (A *ᵥ y) i - lam * y i = exp (φ i) * f i - (E *ᵥ y) i := by
    intro i
    have h1 : (A *ᵥ y) i + (E *ᵥ y) i = exp (φ i) * (A *ᵥ u) i := by
      simp only [mulVec, dotProduct, hE, Matrix.of_apply, ← sum_add_distrib, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      have : exp (φ i - φ j) * exp (φ j) = exp (φ i) := by rw [← exp_add]; ring_nf
      simp only [hy]
      calc A i j * (exp (φ j) * u j) + A i j * (exp (φ i - φ j) - 1) * (exp (φ j) * u j)
          = A i j * u j * (exp (φ i - φ j) * exp (φ j)) := by ring
        _ = exp (φ i) * (A i j * u j) := by rw [this]; ring
    rw [← hf i]; simp only [hy]; linear_combination h1
  have hmain := hgap y
  set Y := √(∑ i, y i ^ 2) with hYdef
  set B := √(∑ i, (exp (φ i) * f i) ^ 2) with hBdef
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hC : √(∑ i, (E *ᵥ y) i ^ 2) ≤ Δ / 2 * Y := by
    calc _ ≤ √((Δ / 2) ^ 2 * ∑ i, y i ^ 2) := Real.sqrt_le_sqrt hEy
      _ = Δ / 2 * Y := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ]
  have hA' : Δ * Y ≤ √(∑ i, ((A *ᵥ y) i - lam * y i) ^ 2) := by
    calc Δ * Y = √(Δ ^ 2 * ∑ i, y i ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΔ.le]
      _ ≤ _ := Real.sqrt_le_sqrt hmain
  have hmink := sqrt_sum_sq_add_le (fun i => exp (φ i) * f i) (fun i => -(E *ᵥ y) i)
  have heq : (∑ i, ((A *ᵥ y) i - lam * y i) ^ 2) =
      ∑ i, (exp (φ i) * f i + -(E *ᵥ y) i) ^ 2 :=
    sum_congr rfl fun i _ => by rw [hid i]; ring
  have hneg : √(∑ i, (-(E *ᵥ y) i) ^ 2) = √(∑ i, (E *ᵥ y) i ^ 2) := by simp
  rw [heq] at hA'
  have h2 : Δ / 2 * Y ≤ B := by
    have := hA'.trans hmink
    rw [hneg] at this
    linarith
  have hYB : Y ≤ 2 / Δ * B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hΔ]; linarith
  have hY2 : Y ^ 2 = ∑ i, y i ^ 2 := Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)
  have hB2 : B ^ 2 = ∑ i, (exp (φ i) * f i) ^ 2 := Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)
  have hlhs : ∑ i, exp (2 * φ i) * u i ^ 2 = ∑ i, y i ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    simp only [hy, mul_pow, ← exp_nat_mul]; norm_num
  have hrhs : ∑ i, exp (2 * φ i) * f i ^ 2 = ∑ i, (exp (φ i) * f i) ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    simp only [mul_pow, ← exp_nat_mul]; norm_num
  rw [hlhs, hrhs, ← hY2, ← hB2]
  calc Y ^ 2 ≤ (2 / Δ * B) ^ 2 := pow_le_pow_left₀ hY0 hYB 2
    _ = 4 / Δ ^ 2 * B ^ 2 := by ring

end CT

/-- A Jacobi matrix with `|a_j| ≤ M` (and `M ≥ 0`) is `LocalBound` with constant `M`. -/
theorem jacobiMatrix_localBound (n : ℕ) (b a : ℕ → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ j, j + 1 < n → |a j| ≤ M) : LocalBound (jacobiMatrix n b a) M where
  symm i j := by
    have := congrFun (congrFun (jacobiMatrix_isSymm n b a).eq i) j
    simpa using this.symm
  bound i j hij := by
    simp only [jacobiMatrix, Matrix.of_apply, hij, ite_false]
    by_cases h1 : (i : ℕ) + 1 = j
    · simp only [h1, ite_true]; exact hM i (by have := j.2; omega)
    · by_cases h2 : (j : ℕ) + 1 = i
      · simp only [h1, h2, ite_true, ite_false]; exact hM j (by have := i.2; omega)
      · simp [h1, h2, hM0]
  deg i := by
    have hsub : (univ.filter fun j : Fin n => j ≠ i ∧ jacobiMatrix n b a i j ≠ 0) ⊆
        (univ.filter fun j : Fin n => (j : ℕ) + 1 = i) ∪ (univ.filter fun j : Fin n => (i : ℕ) + 1 = j) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and, mem_union] at hj ⊢
      obtain ⟨hne, h0⟩ := hj
      by_contra hcon
      push Not at hcon
      apply h0
      have e1 : ¬ (i : ℕ) + 1 = j := hcon.2
      have e2 : ¬ (j : ℕ) + 1 = i := hcon.1
      simp [jacobiMatrix, hne.symm, e1, e2]
    refine (card_le_card hsub).trans (card_union_le _ _ |>.trans ?_)
    have c1 : (univ.filter fun j : Fin n => (j : ℕ) + 1 = i).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      simp only [mem_filter, mem_univ, true_and] at hx hy
      exact Fin.ext (by omega)
    have c2 : (univ.filter fun j : Fin n => (i : ℕ) + 1 = j).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      simp only [mem_filter, mem_univ, true_and] at hx hy
      exact Fin.ext (by omega)
    omega

end FormalResearch.Jacobi
