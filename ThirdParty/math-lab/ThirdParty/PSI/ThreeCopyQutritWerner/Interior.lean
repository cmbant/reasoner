module

public import ThreeCopyQutritWerner.InteriorReduction
public import ThreeCopyQutritWerner.TwoPlane

@[expose] public section


/-!
# Interior minimizers

Manuscript Theorem 2.1 (interior minimizers) and Section 3.1: for `0 < α < 1/2`, every
normalized minimizer of `q_α` on matrices of rank at most two is, up to a permutation of
the sites, `e^{iθ} (P_E/√2) ⊗ |u⟩⟨u| ⊗ |v⟩⟨v|` (eq. (5)).

`isInteriorMinimizerShape_of_forms_eq_zero` is unconditional: `N = 1`, `R = 0` and `S = 0`
on a matrix of rank at most two force the shape.  The minimizer statements are
CONDITIONAL on the endpoint inequality `0 ≤ q(C)` (open claim T2.1a).
-/

noncomputable section

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- Section 3.1, unconditional: a matrix of rank at most two with `N = 1`, `R = 0` and
`S = 0` has the shape of eq. (5), in arbitrary finite local dimensions. -/
theorem isInteriorMinimizerShape_of_forms_eq_zero (C : Matrix (a × b × c) (a × b × c) ℂ)
    (hC : C.rank ≤ 2) (hN : invN C = 1) (hR : formR C = 0) (hS : formS C = 0) :
    IsInteriorMinimizerShape C := by
  obtain ⟨e₀, e₁, z, h0, h1, h01, hz, hCz⟩ := eq_smul_proj_of_formR_eq_zero C hC hN hR
  have hq1 := cutForm₁_nonneg_of_rank_le_two C hC
  have hq2 := cutForm₂_nonneg_of_rank_le_two C hC
  have hq3 := cutForm₃_nonneg_of_rank_le_two C hC
  rw [formS_eq_cutForm_average] at hS
  have hQ1 : cutForm₁ C = 0 := by linarith
  have hQ2 : cutForm₂ C = 0 := by linarith
  have hz0 : Complex.normSq z ≠ 0 := by
    rw [hz]
    norm_num
  have hP1 : cutForm (ketBra e₀ e₀ + ketBra e₁ e₁) = 0 := by
    rw [cutForm₁_eq_cutForm, hCz, cutForm_smul] at hQ1
    exact (mul_eq_zero.mp hQ1).resolve_left hz0
  have hsub : (z • (ketBra e₀ e₀ + ketBra e₁ e₁)).submatrix siteEquiv₂ siteEquiv₂ =
      z • (ketBra e₀ e₀ + ketBra e₁ e₁).submatrix siteEquiv₂ siteEquiv₂ := by
    ext x y
    rfl
  have hP2 : cutForm ((ketBra e₀ e₀ + ketBra e₁ e₁).submatrix siteEquiv₂ siteEquiv₂) = 0 := by
    rw [cutForm₂_eq_cutForm, hCz, hsub, cutForm_smul] at hQ2
    exact (mul_eq_zero.mp hQ2).resolve_left hz0
  obtain ⟨⟨a₁, a₂, a₃, he₀⟩, ⟨b₁, b₂, b₃, he₁⟩, hc1, hc2⟩ :=
    plane_products_of_cutForms_eq_zero e₀ e₁ h0 h1 h01 hP1 hP2
  rcases two_plane_of_product a₁ b₁ a₂ b₂ a₃ b₃ e₀ e₁ he₀ he₁ h0 h1 h01 hc1 hc2 with
    ⟨f₁, f₂, u, v, hf1, hf2, hf12, hu, hv, hP⟩ | ⟨u, f₁, f₂, v, hf1, hf2, hf12, hu, hv, hP⟩ |
      ⟨u, v, f₁, f₂, hf1, hf2, hf12, hu, hv, hP⟩
  · exact ⟨z, hz, Or.inl ⟨f₁, f₂, u, v, hf1, hf2, hf12, hu, hv, by rw [hCz, hP]⟩⟩
  · exact ⟨z, hz, Or.inr (Or.inl ⟨u, f₁, f₂, v, hf1, hf2, hf12, hu, hv, by rw [hCz, hP]⟩)⟩
  · exact ⟨z, hz, Or.inr (Or.inr ⟨u, v, f₁, f₂, hf1, hf2, hf12, hu, hv, by rw [hCz, hP]⟩)⟩

/-- Theorem 2.1, interior equality, CONDITIONAL on the endpoint inequality at the matrix
considered (`hq`, open claim T2.1a): for `0 < α < 1/2`, a normalized matrix of rank at
most two with `q_α(C) = (1 - 2α)(1 - α)²` has the shape of eq. (5). -/
theorem isInteriorMinimizerShape_of_energy_eq {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2)
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2) (hN : invN C = 1)
    (hq : 0 ≤ endpointEnergy C) (hmin : energy α C = sharpCurve α) :
    IsInteriorMinimizerShape C := by
  have key := energy_sub_sharpCurve_mul_invN C α
  rw [hmin, hN, mul_one, sub_self] at key
  have hR := formR_nonneg_of_rank_le_two C hC
  have hS := formS_nonneg_of_rank_le_two C hC
  have c1 : 0 < 4 * α * (1 + α) / 3 :=
    div_pos (mul_pos (mul_pos (by norm_num) h0) (by linarith)) (by norm_num)
  have c2 : 0 < α * (1 - 2 * α) * (2 / 3 - α) :=
    mul_pos (mul_pos h0 (by linarith)) (by linarith)
  have c3 : 0 < 2 * α * (1 - 2 * α) := mul_pos (by linarith) (by linarith)
  have t1 := mul_nonneg c1.le hq
  have t2 := mul_nonneg c2.le hR
  have t3 := mul_nonneg c3.le hS
  have hR0 : formR C = 0 := by
    by_contra hne
    have := mul_pos c2 (lt_of_le_of_ne hR (Ne.symm hne))
    linarith
  have hS0 : formS C = 0 := by
    by_contra hne
    have := mul_pos c3 (lt_of_le_of_ne hS (Ne.symm hne))
    linarith
  exact isInteriorMinimizerShape_of_forms_eq_zero C hC hN hR0 hS0

/-- Theorem 2.1 at `d = 3`, interior minimizers, CONDITIONAL on the qutrit endpoint
inequality `hq` (open claim T2.1a): for `0 < α < 1/2`, every normalized minimizer of `q_α`
over complex `27 × 27` matrices of rank at most two has the shape of eq. (5). -/
theorem isInteriorMinimizerShape_of_isMin {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2)
    (hq : ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 → 0 ≤ endpointEnergy C)
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) (hC : C.rank ≤ 2)
    (hN : invN C = 1)
    (hmin : ∀ D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, D.rank ≤ 2 →
      invN D = 1 → energy α C ≤ energy α D) :
    IsInteriorMinimizerShape C := by
  have hle : energy α C ≤ sharpCurve α := by
    have h := hmin sharpWitness rank_sharpWitness invN_sharpWitness
    rwa [energy_sharpWitness] at h
  have hge : sharpCurve α * invN C ≤ energy α C :=
    sharpCurve_mul_invN_le_energy_of_endpointEnergy_nonneg C hC h0.le h1.le (hq C hC)
  rw [hN, mul_one] at hge
  exact isInteriorMinimizerShape_of_energy_eq h0 h1 C hC hN (hq C hC) (le_antisymm hle hge)

end ThreeCopyQutritWerner

end
