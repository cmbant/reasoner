module

public import Mathlib

/-!
# Jacobi operator package: Schur multipliers of bounded mixed variation (finite form)

Paper J, `lem:thb-schur` (`thmB.tex`), in the finite formulation that its proof actually uses: the
signed measure `ν` of (eq:thb-S) is a finite signed sum of point masses (cells) `w_σ δ_{(t_σ, s_σ)}`,
so that `ν((a,u]×(c,X])` becomes `∑_σ w_σ 1[t_σ < u] 1[s_σ < X]` after moving the thresholds `t_σ, s_σ`
to the left end of their cell.

* `jop_IsSchurBdd Φ K`: the Schur multiplier norm of the real matrix `Φ` is at most `K`, i.e.
  `‖Φ ⊙ Y‖ ≤ K ‖Y‖` for every real matrix `Y` (operator norm, Hadamard product).
* `jop_schur_finite`: the bound `A + B + ∑_σ |w_σ|`, where `A`, `B` bound `|φ(u_n,c)|` and
  `|φ(a,X_k) - φ(a,c)|` over the rows and columns used.

The proof is the paper's: `Φ ⊙ Y = diag(r) Y + Y diag(q) + ∑_σ w_σ P_σ Y Q_σ` with diagonal factors and
coordinate projections `P_σ, Q_σ`.  The rows and columns are arbitrary finite index types (points may
repeat and need not be ordered), which is more general than the paper.

Not formalised: the measure-theoretic form and the smooth sufficient condition (the fundamental-theorem
step giving `‖ν‖_TV ≤ |I||J| ‖∂_u∂_Xφ‖_∞`); they are not used by the finite statement.  No such lemma
existed in the repository (`FrameFree/FilteredGateReal` has a special, unrelated multiplier bound).
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The Schur multiplier norm of `Φ` is at most `K`: `‖Φ ⊙ Y‖ ≤ K ‖Y‖` for all real matrices `Y`
(operator norm). -/
def jop_IsSchurBdd {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (Φ : Matrix ι κ ℝ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ Y : Matrix ι κ ℝ, ‖Φ ⊙ Y‖ ≤ K * ‖Y‖

lemma jop_norm_diagonal_le {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, |d i| ≤ C) : ‖(diagonal d : Matrix n n ℝ)‖ ≤ C := by
  rw [l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).2 fun i => by simpa using h i

lemma jop_norm_proj_le {n : Type*} [Fintype n] [DecidableEq n] (p : n → Prop) [DecidablePred p] :
    ‖(diagonal fun i => if p i then (1 : ℝ) else 0 : Matrix n n ℝ)‖ ≤ 1 :=
  jop_norm_diagonal_le _ zero_le_one fun i => by by_cases hp : p i <;> simp [hp]

lemma jop_norm_mul3_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix ι ι ℝ) (Y : Matrix ι κ ℝ) (Q : Matrix κ κ ℝ) :
    ‖P * Y * Q‖ ≤ ‖P‖ * ‖Y‖ * ‖Q‖ :=
  (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))

/-- **Schur multipliers of bounded mixed variation, finite form** (Paper J `lem:thb-schur`).
For finite row and column families `u_n, X_k` and a finite family of weighted cells
`(w_σ, t_σ, s_σ)` with
`φ(u_n,X_k) - φ(u_n,c) - φ(a,X_k) + φ(a,c) = ∑_σ w_σ 1[t_σ < u_n] 1[s_σ < X_k]`,
the Schur multiplier norm of `(φ(u_n,X_k))` is at most `A + B + ∑_σ |w_σ|`, where
`|φ(u_n,c)| ≤ A` and `|φ(a,X_k) - φ(a,c)| ≤ B`.  Proved. -/
theorem jop_schur_finite {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ] [DecidableEq ι]
    [DecidableEq κ] (φ : ℝ → ℝ → ℝ) (a c : ℝ) (u : ι → ℝ) (X : κ → ℝ) (w t s : σ → ℝ)
    (hν : ∀ n k, φ (u n) (X k) - φ (u n) c - φ a (X k) + φ a c =
      ∑ i, w i * (if t i < u n then 1 else 0) * (if s i < X k then 1 else 0))
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hA : ∀ n, |φ (u n) c| ≤ A)
    (hB : ∀ k, |φ a (X k) - φ a c| ≤ B) :
    jop_IsSchurBdd (Matrix.of fun n k => φ (u n) (X k)) (A + B + ∑ i, |w i|) := by
  classical
  refine ⟨by positivity, fun Y => ?_⟩
  set P : σ → Matrix ι ι ℝ := fun i => diagonal fun n => if t i < u n then (1 : ℝ) else 0
  set Q : σ → Matrix κ κ ℝ := fun i => diagonal fun k => if s i < X k then (1 : ℝ) else 0
  have hdecomp : (Matrix.of fun n k => φ (u n) (X k)) ⊙ Y =
      diagonal (fun n => φ (u n) c) * Y + Y * diagonal (fun k => φ a (X k) - φ a c) +
        ∑ i, w i • (P i * Y * Q i) := by
    ext n k
    have hk := hν n k
    simp only [hadamard_apply, of_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, P, Q, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have : ∑ i, w i * ((if t i < u n then (1 : ℝ) else 0) * Y n k *
        (if s i < X k then (1 : ℝ) else 0)) =
        (∑ i, w i * (if t i < u n then 1 else 0) * (if s i < X k then 1 else 0)) * Y n k := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← hk]; ring
  rw [hdecomp]
  have h1 : ‖(diagonal (fun n => φ (u n) c) : Matrix ι ι ℝ) * Y‖ ≤ A * ‖Y‖ :=
    (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      (jop_norm_diagonal_le _ hA0 hA) (norm_nonneg _))
  have h2 : ‖Y * (diagonal (fun k => φ a (X k) - φ a c) : Matrix κ κ ℝ)‖ ≤ B * ‖Y‖ := by
    refine (l2_opNorm_mul _ _).trans ?_
    have := jop_norm_diagonal_le (fun k => φ a (X k) - φ a c) hB0 hB
    nlinarith [norm_nonneg Y]
  have h3 : ‖∑ i, w i • (P i * Y * Q i)‖ ≤ (∑ i, |w i|) * ‖Y‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (jop_norm_mul3_le _ _ _).trans ?_
    have hP := jop_norm_proj_le (n := ι) (fun n => t i < u n)
    have hQ := jop_norm_proj_le (n := κ) (fun k => s i < X k)
    calc ‖P i‖ * ‖Y‖ * ‖Q i‖ ≤ 1 * ‖Y‖ * 1 := by gcongr
      _ = ‖Y‖ := by ring
  calc _ ≤ ‖(diagonal (fun n => φ (u n) c) : Matrix ι ι ℝ) * Y‖ +
        ‖Y * (diagonal (fun k => φ a (X k) - φ a c) : Matrix κ κ ℝ)‖ +
        ‖∑ i, w i • (P i * Y * Q i)‖ := norm_add₃_le
    _ ≤ A * ‖Y‖ + B * ‖Y‖ + (∑ i, |w i|) * ‖Y‖ := by linarith
    _ = (A + B + ∑ i, |w i|) * ‖Y‖ := by ring

/-- info: 'FormalResearch.MatrixAnalysis.jop_schur_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_schur_finite

end FormalResearch.MatrixAnalysis
