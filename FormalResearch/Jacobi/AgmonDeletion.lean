module

public import FormalResearch.Jacobi.AgmonEnergy
public import FormalResearch.MatrixAnalysis.MaskedFrobenius

/-!
# AG.2 (corollary): gap-and-intrinsic-distance deletion in Frobenius norm (AG.4), generic form

Source: `Weyl/P5/notes/intrinsic_agmon_action.md`, Corollary AG.2, eq. (AG.4) (PR 250, head `cfad461d2`):
`‖K ∘ U‖_F ≤ √(2 M n/γ₀) e^{-L}` for the mask `K_{jd} = 1[γ_{j,d} ≥ γ₀, φ_{j,d} ≥ L]`.

`ag4` : for a matrix `U` whose columns `c` are unit eigenvectors (eigenvalue `lam c`) of a
`LocalBound` matrix `H`, with for each column a family of components `I c a` and weights `φ c a`
satisfying the hypotheses of `ag_total`, the mask
`K_{jc} = ∃ a, j ∈ I c a ∧ γ₀ ≤ γ_j(λ_c) ∧ L ≤ φ c a j` obeys
`‖K ∘ U‖_F² ≤ (#columns) · (2 M / γ₀) · e^{-2L}`.

Claim class: proved.  Not formalised: the Racah-specific constants (`M ≤ 5`, `n ≤ 5T/2`, AG.5).
-/

@[expose] public section

namespace FormalResearch.Jacobi

open Matrix Finset Real FormalResearch.MatrixAnalysis

variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype α] {H : Matrix ι ι ℝ}
  {M : ℝ}

theorem ag4 (hH : LocalBound H M) (hM : 0 ≤ M) (U : Matrix ι κ ℝ) (lam : κ → ℝ)
    (hU : ∀ c, H *ᵥ (fun j => U j c) = lam c • (fun j => U j c))
    (hunit : ∀ c, ∑ j, U j c ^ 2 = 1) (I : κ → α → Finset ι)
    (hdisj : ∀ c a b, a ≠ b → Disjoint (I c a) (I c b))
    (hsep : ∀ c a b, a ≠ b → ∀ j ∈ I c a, ∀ k ∈ I c b, H j k = 0) (φ : κ → α → ι → ℝ)
    (hγ : ∀ c a, ∀ j ∈ I c a, 0 ≤ localGap H (lam c) j)
    (hφ0 : ∀ c a, ∀ j ∈ I c a, (∃ k ∈ (I c a)ᶜ, H j k ≠ 0) → φ c a j = 0)
    (hφ : ∀ c a, ∀ j ∈ I c a, ∀ k ∈ I c a, j ≠ k →
      |H j k| * (cosh (φ c a j - φ c a k) - 1) ≤
        min (localGap H (lam c) j) (localGap H (lam c) k) / 4)
    {γ₀ : ℝ} (hγ₀ : 0 < γ₀) (L : ℝ)
    [∀ j c, Decidable (∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧ L ≤ φ c a j)] :
    frobSq (maskMul (fun j c => ∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧ L ≤ φ c a j) U) ≤
      Fintype.card κ * (2 * M / γ₀ * exp (-(2 * L))) := by
  classical
  have hcol : ∀ c, ∑ j, (maskMul (fun j c => ∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧
      L ≤ φ c a j) U) j c ^ 2 ≤ 2 * M / γ₀ * exp (-(2 * L)) := by
    intro c
    have h2 := ag_total hH hM (hU c) (I c) (hdisj c) (hsep c) (φ c) (hγ c) (hφ0 c) (hφ c)
    rw [hunit c, mul_one] at h2
    have hterm : ∀ a, ∀ j, (if j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧ L ≤ φ c a j then
        U j c ^ 2 else 0) ≤ (if j ∈ I c a then (1 / γ₀) * exp (-(2 * L)) *
          (localGap H (lam c) j * (exp (φ c a j) * |U j c|) ^ 2) else 0) := by
      intro a j
      by_cases hj : j ∈ I c a
      · by_cases hk : γ₀ ≤ localGap H (lam c) j ∧ L ≤ φ c a j
        · simp only [hj, hk, and_self, ite_true]
          have e1 : (exp (φ c a j) * |U j c|) ^ 2 = exp (2 * φ c a j) * U j c ^ 2 := by
            rw [mul_pow, sq_abs, ← exp_nat_mul]; norm_num
          rw [e1]
          have e2 : 1 ≤ (1 / γ₀) * localGap H (lam c) j := by
            rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hγ₀]; linarith [hk.1]
          have e3 : 1 ≤ exp (-(2 * L)) * exp (2 * φ c a j) := by
            rw [← exp_add]; apply one_le_exp; linarith [hk.2]
          have e4 : 0 ≤ U j c ^ 2 := sq_nonneg _
          calc U j c ^ 2 = 1 * 1 * U j c ^ 2 := by ring
            _ ≤ ((1 / γ₀) * localGap H (lam c) j) * (exp (-(2 * L)) * exp (2 * φ c a j)) *
                U j c ^ 2 := by
                apply mul_le_mul_of_nonneg_right _ e4
                exact mul_le_mul e2 e3 (by norm_num) (by linarith)
            _ = _ := by ring
        · have h0 : 0 ≤ (1 / γ₀) * exp (-(2 * L)) *
              (localGap H (lam c) j * (exp (φ c a j) * |U j c|) ^ 2) := by
            have := hγ c a j hj
            positivity
          simp only [hj, true_and, hk, ite_false, ite_true]
          exact h0
      · simp [hj]
    have h3 : ∑ j, (maskMul (fun j c => ∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧
        L ≤ φ c a j) U) j c ^ 2 ≤
        (1 / γ₀) * exp (-(2 * L)) * ∑ a, ∑ j ∈ I c a, localGap H (lam c) j *
          (exp (φ c a j) * |U j c|) ^ 2 := by
      calc ∑ j, (maskMul (fun j c => ∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧
            L ≤ φ c a j) U) j c ^ 2
          ≤ ∑ j, ∑ a, (if j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧ L ≤ φ c a j then
              U j c ^ 2 else 0) := by
            refine sum_le_sum fun j _ => ?_
            by_cases hK : ∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧ L ≤ φ c a j
            · obtain ⟨a, ha⟩ := hK
              have hK' : ∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧ L ≤ φ c a j := ⟨a, ha⟩
              have e : maskMul (fun j c => ∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧
                  L ≤ φ c a j) U j c = U j c := by
                simp only [maskMul, Matrix.of_apply, hK', ite_true]
              rw [e]
              refine le_trans ?_ (single_le_sum (f := fun a => if j ∈ I c a ∧
                γ₀ ≤ localGap H (lam c) j ∧ L ≤ φ c a j then U j c ^ 2 else 0)
                (fun a _ => by split_ifs <;> positivity) (mem_univ a))
              simp [ha]
            · have e : maskMul (fun j c => ∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧
                  L ≤ φ c a j) U j c = 0 := by
                simp only [maskMul, Matrix.of_apply, hK, ite_false]
              rw [e]
              calc (0 : ℝ) ^ 2 = 0 := by norm_num
                _ ≤ _ := sum_nonneg fun a _ => by split_ifs <;> positivity
        _ = ∑ a, ∑ j, (if j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧ L ≤ φ c a j then
              U j c ^ 2 else 0) := sum_comm
        _ ≤ ∑ a, ∑ j, (if j ∈ I c a then (1 / γ₀) * exp (-(2 * L)) *
              (localGap H (lam c) j * (exp (φ c a j) * |U j c|) ^ 2) else 0) :=
            sum_le_sum fun a _ => sum_le_sum fun j _ => hterm a j
        _ = _ := by
            rw [mul_sum]
            refine sum_congr rfl fun a _ => ?_
            rw [← sum_filter, mul_sum]
            simp only [Finset.filter_mem_eq_inter, univ_inter]
    calc _ ≤ _ := h3
      _ ≤ (1 / γ₀) * exp (-(2 * L)) * (2 * M) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  unfold frobSq
  rw [sum_comm]
  calc ∑ c, ∑ j, (maskMul (fun j c => ∃ a, j ∈ I c a ∧ γ₀ ≤ localGap H (lam c) j ∧
        L ≤ φ c a j) U) j c ^ 2
      ≤ ∑ c : κ, 2 * M / γ₀ * exp (-(2 * L)) := sum_le_sum fun c _ => hcol c
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- info: 'FormalResearch.Jacobi.ag4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ag4

end FormalResearch.Jacobi
