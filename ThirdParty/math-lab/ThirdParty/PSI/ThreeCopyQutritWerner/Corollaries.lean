module

public import ThreeCopyQutritWerner.Embedding

@[expose] public section


/-!
# Corollaries: attainment in unequal dimensions, the accessible minimum and negativity

* Theorem 2.1, unequal dimensions, the case `2 ≤ dᵢ ≤ 3`: the minimum formula, as a
  REDUCTION to the qutrit endpoint inequality, with unconditional attainment.
* Theorem 2.1, eq. (4), as an infimum: `m_{3,3}(α) = (1 - 2α)(1 - α)²` for `0 ≤ α ≤ 1/2`,
  a REDUCTION to the qutrit endpoint inequality.
* With eq. (4): the rank-two-accessible negativity
  `A_{3,3}(α) = [-m_{3,3}(α)]_+ / [3(3 - α)]³` vanishes on `0 ≤ α ≤ 1/2`, a REDUCTION.
-/

noncomputable section

namespace ThreeCopyQutritWerner

section Indicator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard basis vector `|i⟩`. -/
def basisVec (i : ι) : ι → ℂ := fun x => if x = i then 1 else 0

theorem vecNormSq_basisVec (i : ι) : vecNormSq (basisVec i) = 1 := by
  unfold vecNormSq basisVec
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem braket_basisVec_of_ne {i j : ι} (h : i ≠ j) : braket (basisVec i) (basisVec j) = 0 := by
  unfold braket basisVec
  apply Finset.sum_eq_zero
  intro x _
  by_cases hi : x = i
  · have hj : x ≠ j := fun hj => h (hi.symm.trans hj)
    simp [hj]
  · simp [hi]

end Indicator

/-- A matrix of the interior-minimizer shape exists as soon as the first site has dimension at
least two and the other sites are nonempty. -/
theorem exists_isInteriorMinimizerShape {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (ha : 2 ≤ Fintype.card a) (hb : 1 ≤ Fintype.card b) (hc : 1 ≤ Fintype.card c) :
    ∃ C : Matrix (a × b × c) (a × b × c) ℂ, IsInteriorMinimizerShape C := by
  obtain ⟨a₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card a)
  obtain ⟨a₁, ha₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card a) a₀
  obtain ⟨b₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card b)
  obtain ⟨c₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card c)
  refine ⟨((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) • tensor₃ (ketBra (basisVec a₀) (basisVec a₀) +
      ketBra (basisVec a₁) (basisVec a₁)) (ketBra (basisVec b₀) (basisVec b₀))
      (ketBra (basisVec c₀) (basisVec c₀)), ?_⟩
  unfold IsInteriorMinimizerShape
  exact ⟨_, normSq_inv_sqrt_two, Or.inl ⟨basisVec a₀, basisVec a₁, basisVec b₀, basisVec c₀,
    vecNormSq_basisVec a₀, vecNormSq_basisVec a₁, braket_basisVec_of_ne (Ne.symm ha₁),
    vecNormSq_basisVec b₀, vecNormSq_basisVec c₀, rfl⟩⟩

/-- Theorem 2.1, unequal dimensions, the case `2 ≤ dᵢ ≤ 3`, as a REDUCTION to the
qutrit endpoint inequality: the bound `f(α) N ≤ q_α` on rank at most two, and its attainment by a
normalized matrix of rank at most two. -/
theorem minimum_formula_of_card (hq : QutritEndpointInequality)
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b]
    [DecidableEq c] (ha2 : 2 ≤ Fintype.card a) (ha : Fintype.card a ≤ 3)
    (hb2 : 2 ≤ Fintype.card b) (hb : Fintype.card b ≤ 3) (hc2 : 2 ≤ Fintype.card c)
    (hc : Fintype.card c ≤ 3) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    (∀ C : Matrix (a × b × c) (a × b × c) ℂ, C.rank ≤ 2 →
      sharpCurve α * invN C ≤ energy α C) ∧
    ∃ C : Matrix (a × b × c) (a × b × c) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α := by
  refine ⟨fun C hC => sharpCurve_mul_invN_le_energy_of_card_le_three hq ha hb hc h0 h1 C hC, ?_⟩
  obtain ⟨C, hC⟩ := exists_isInteriorMinimizerShape (a := a) (b := b) (c := c) ha2
    (by omega) (by omega)
  exact ⟨C, rank_le_two_of_isInteriorMinimizerShape C hC,
    (energy_eq_sharpCurve_of_isInteriorMinimizerShape C hC α).1,
    (energy_eq_sharpCurve_of_isInteriorMinimizerShape C hC α).2⟩

/-- `m_{3,3}(α)`: the infimum of `q_α` over normalized complex `27 × 27` matrices of rank at
most two (manuscript eq. (4)). -/
def accessibleMin (α : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
    C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = x}

/-- The rank-two-accessible negativity `A_{3,3}(α) = [-m_{3,3}(α)]_+ / [3(3 - α)]³`, with
`m_{3,3}` as in eq. (4). -/
def accessibleNegativity (α : ℝ) : ℝ :=
  max (-(accessibleMin α)) 0 / (3 * (3 - α)) ^ 3

/-- Theorem 2.1, eq. (4) at `d = 3` as an infimum, a REDUCTION to the qutrit endpoint
inequality: `m_{3,3}(α) = (1 - 2α)(1 - α)²` for `0 ≤ α ≤ 1/2`. -/
theorem accessibleMin_eq_of_endpoint (hq : QutritEndpointInequality) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1 / 2) : accessibleMin α = sharpCurve α := by
  have hlow : ∀ x ∈ {x : ℝ | ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = x}, sharpCurve α ≤ x := by
    rintro x ⟨C, hC, hN, rfl⟩
    have h := sharpCurve_mul_invN_le_energy_of_endpointEnergy_nonneg C hC h0 h1 (hq C hC)
    rwa [hN, mul_one] at h
  have hmem : sharpCurve α ∈ {x : ℝ | ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3)
      (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = x} :=
    ⟨sharpWitness, rank_sharpWitness, invN_sharpWitness, energy_sharpWitness α⟩
  unfold accessibleMin
  exact le_antisymm (csInf_le ⟨sharpCurve α, hlow⟩ hmem) (le_csInf ⟨_, hmem⟩ hlow)

/-- With eq. (4), a REDUCTION to the qutrit endpoint inequality: the rank-two-accessible
negativity vanishes on `0 ≤ α ≤ 1/2`. -/
theorem accessibleNegativity_eq_zero_of_endpoint (hq : QutritEndpointInequality) {α : ℝ}
    (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) : accessibleNegativity α = 0 := by
  unfold accessibleNegativity
  rw [accessibleMin_eq_of_endpoint hq h0 h1]
  have hf : 0 ≤ sharpCurve α := sharpCurve_nonneg h1
  rw [max_eq_right (by linarith), zero_div]

end ThreeCopyQutritWerner

end
