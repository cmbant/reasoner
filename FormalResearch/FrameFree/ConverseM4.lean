import FormalResearch.FrameFree.ConverseBranch
import FormalResearch.FrameFree.Ceilings

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate Matrix BigOperators ComplexOrder
open Matrix FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom

namespace FormalResearch.FrameFree.Converse

/-! ### `M₄` has an achiral projected branch of weight `1/2` -/

open FormalResearch.FrameFree.Ceilings

local notation "ωω" => FormalResearch.FourQubitEntropy.omega

/-- `rot` of a family of diagonal local operators is a pointwise product. -/
theorem rot_diagonal {n : ℕ} (d : Fin n → Fin 2 → ℂ) (ξ : Ψ n) (x : Fin n → Fin 2) :
    rot (fun i => Matrix.diagonal (d i)) ξ x = (∏ i, d i (x i)) * ξ x := by
  unfold rot
  rw [Finset.sum_eq_single x]
  · simp [Matrix.diagonal_apply_eq]
  · intro y _ hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have : ∏ j, (Matrix.diagonal (d j)) (x j) (y j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.diagonal_apply_ne _ (Ne.symm hi)])
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- The antidiagonal `SU(2)` element `[[0,a],[-ā,0]]`. -/
def va (a : ℂ) : NQubit.Op1 := !![0, a; -conj a, 0]

theorem SU2_va {a : ℂ} (ha : conj a * a = 1) : SU2 (va a) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [va, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      first | exact ha | (rw [mul_comm]; exact ha)
  · simp [va, Matrix.det_fin_two]
    linear_combination ha

theorem va_mul_eps (a : ℂ) : va a * eps = Matrix.diagonal ![-a, -conj a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [va, eps, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]

/-- The phases `a = (ω, ω², 1)` of the frame of the branch `⟨0|₀ M₄`. -/
noncomputable def m4a : Fin 3 → ℂ := ![ωω, conj ωω, 1]

/-- The frame `(v₁,v₂,v₃) = (va ω, va ω², va 1)` of the branch `⟨0|₀ M₄`. -/
noncomputable def m4Frame : Fin 3 → NQubit.Op1 := fun i => va (m4a i)

theorem m4Frame_su2 : ∀ i, SU2 (m4Frame i) := by
  have h1 : conj ωω * ωω = 1 := by rw [mul_comm]; exact FormalResearch.FourQubitEntropy.omega_mul_conj
  intro i
  fin_cases i
  · exact SU2_va h1
  · exact SU2_va (by simpa [Complex.conj_conj, m4a, mul_comm] using h1)
  · exact SU2_va (by simp [m4a])

theorem sl0_M4v (a b c : Fin 2) : sl 0 M4v ![a, b, c] = FormalResearch.FourQubitEntropy.M4 0 a b c := by
  simp [sl, M4v, toN]

theorem bra_e0 {m : ℕ} (ψ : Ψ (m + 1)) : bra ![1, 0] ψ = sl 0 ψ := by
  simp [bra, Fin.sum_univ_two]

theorem nsq_sl0_M4v : nsq (sl 0 M4v) = 1 / 2 := by
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have hω : Complex.normSq ωω = 1 := by
    have := FormalResearch.FourQubitEntropy.omega_mul_conj
    rw [Complex.mul_conj] at this
    exact_mod_cast this
  let e : (Fin 3 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 :=
    { toFun := fun x => (x 0, x 1, x 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun x => by funext i; fin_cases i <;> rfl
      right_inv := fun p => rfl }
  unfold nsq
  calc ∑ x, Complex.normSq (sl 0 M4v x)
      = ∑ p : Fin 2 × Fin 2 × Fin 2,
          Complex.normSq (FormalResearch.FourQubitEntropy.M4 0 p.1 p.2.1 p.2.2) :=
        Fintype.sum_equiv e _ _ (fun x => by
          have hx : ![x 0, x 1, x 2] = x := by funext i; fin_cases i <;> rfl
          have h := sl0_M4v (x 0) (x 1) (x 2)
          rw [hx] at h
          rw [h]; rfl)
    _ = 1 / 2 := by
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
        simp [FormalResearch.FourQubitEntropy.M4, Complex.normSq_mul, Complex.normSq_conj, hω]
        field_simp
        norm_num

theorem m4_branch_achiral : rot m4Frame (Θ (bra ![1, 0] M4v)) = (-(ωω ^ 2)) • bra ![1, 0] M4v := by
  have p3 := FormalResearch.FourQubitEntropy.omega_pow3
  have pq := FormalResearch.FourQubitEntropy.omega_sq_add
  have hcw := FormalResearch.FourQubitEntropy.conj_omega
  rw [Θ_eq_rot, rot_comp]
  have hv : (fun i => m4Frame i * eps) = fun i => Matrix.diagonal ![-m4a i, -conj (m4a i)] :=
    funext fun i => va_mul_eps _
  rw [hv]
  funext x
  rw [rot_diagonal]
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  rw [hx, bra_e0]
  simp only [Fin.prod_univ_three]
  generalize x 0 = a at *
  generalize x 1 = b at *
  generalize x 2 = c at *
  simp only [Pi.smul_apply, cj, sl0_M4v, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [m4a, FormalResearch.FourQubitEntropy.M4, hcw] <;>
    first
      | linear_combination (ωω ^ 2) * p3
      | linear_combination ((↑(Real.sqrt 6) : ℂ)⁻¹ * ωω ^ 3) * p3
      | linear_combination ((↑(Real.sqrt 6) : ℂ)⁻¹ * ωω ^ 4 * (ωω ^ 3 + 1)) * p3

/-- **`M₄` has an achiral projected branch of weight `1/2`** (`⟨0|₀ M₄ = (|011⟩ + ω|101⟩ + ω²|110⟩)/√6`
is fixed by the frame `(va ω, va ω², va 1)` up to the phase `-ω²`). -/
theorem achiralBranch_M4v : AchiralBranch M4v (1 / 2) := by
  have he : conj ((![1, 0] : Fin 2 → ℂ) 0) * (![1, 0] : Fin 2 → ℂ) 0 +
      conj ((![1, 0] : Fin 2 → ℂ) 1) * (![1, 0] : Fin 2 → ℂ) 1 = 1 := by simp
  have hω : ‖ωω‖ = 1 := by
    have := FormalResearch.FourQubitEntropy.omega_mul_conj
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    have h2 : ‖ωω‖ ^ 2 = 1 := by exact_mod_cast this
    nlinarith [norm_nonneg ωω]
  have hc : ‖-(ωω ^ 2)‖ = 1 := by rw [norm_neg, norm_pow, hω]; norm_num
  have hpos : 0 < nsq (bra ![1, 0] M4v) := by rw [bra_e0, nsq_sl0_M4v]; norm_num
  have h := achiralBranch_of_branch M4v he m4Frame_su2 hc hpos m4_branch_achiral
  rwa [bra_e0, nsq_sl0_M4v] at h

/-- Blocks of four: `M₄^{⊗(m+1)}` has an achiral projected branch of weight `2^{-(m+1)}`. -/
theorem achiralBranch_M4pow (m : ℕ) : AchiralBranch (M4pow m) ((1 / 2) ^ (m + 1)) := by
  induction m with
  | zero => simpa [M4pow] using achiralBranch_M4v
  | succ m ih =>
    have := ih.tens achiralBranch_M4v
    rwa [← pow_succ] at this

end FormalResearch.FrameFree.Converse
