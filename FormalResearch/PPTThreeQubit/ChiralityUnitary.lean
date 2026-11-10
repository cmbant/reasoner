module

public import FormalResearch.PPTThreeQubit.Chirality
public import FormalResearch.PPTThreeQubit.FamilyPPT

/-!
# Local-unitary chirality of `ρ_t` (`cor:ppt3-chirality` (a))

Source: `QI/hidden_entanglement/ppt_three_qubit/family.tex`, `cor:ppt3-chirality` (a), and the proof
in `appendix_family.tex`.

Covered: for every `t > 0` (in particular throughout the PPT interval `[t_-, t_+]`), `ρ_t` is not
`U ρ̄_t U†` for any local unitary `U = U_A ⊗ U_B ⊗ U_C`, and it is not `U Θ(ρ_t) U†` for the
physical spin time reversal `Θ(ρ) = Y^{⊗3} ρ̄ Y^{⊗3†}` (`Y` the Pauli matrix `σ_y`, which differs from
complex conjugation by the local unitary `Y^{⊗3}`).  Equivalently, no local unitary (and the same for
no invertible local filter) maps `ρ_t` to its complex conjugate or to its time reverse.

Route differs from the paper's.  The paper's proof of (a) uses the nondegenerate eigenrays of `u`
and `v` for `t > 3`; here (a) is obtained as a special case of the stronger filter-level statement
`no_local_filter_state` (`cor:ppt3-chirality` (b), `Chirality.lean`), because `ρ_t` has range
`R_1 = ran B` for every `t > 0` (`range_rhoT`).  The result is therefore valid for all `t > 0`, not
only `t > 3`.  The eigenvalue argument of the paper is not formalised.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- The range of `ρ_t` is `R_1 = ran B` for every `t > 0` (the five weights of `eq:ppt3-rho` are
positive). -/
theorem range_rhoT {t : ℝ} (ht : 0 < t) : Set.range (rhoT t).mulVec = Rs 1 := by
  have hxt : ∀ a, (![t, 3 * t, 3, 3, 1] a / (7 * (t + 3)) : ℝ) ≠ 0 := by
    intro a
    have h7 : 0 < 7 * (t + 3) := by positivity
    refine (div_pos ?_ h7).ne'
    fin_cases a <;> simp <;> positivity
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, rfl⟩
    refine ⟨Xt t *ᵥ ((Bs 1)ᴴ *ᵥ x), ?_⟩
    simp only [rhoT, mulVec_mulVec, Matrix.mul_assoc]
  · rintro _ ⟨c, rfl⟩
    let d : Fin 5 → ℂ := fun a => c a / ((![t, 3 * t, 3, 3, 1] a / (7 * (t + 3)) : ℝ) : ℂ)
    have hd : Xt t *ᵥ d = c := by
      ext a
      simp only [Xt, mulVec_diagonal, d]
      have := hxt a
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr this)
    refine ⟨(Lmat)ᴴ *ᵥ d, ?_⟩
    have hL : (Bs 1)ᴴ *ᵥ ((Lmat)ᴴ *ᵥ d) = d := by
      rw [mulVec_mulVec, ← conjTranspose_mul, Lmat_mul_Bs, conjTranspose_one, one_mulVec]
    show rhoT t *ᵥ _ = _
    rw [rhoT, ← mulVec_mulVec, ← mulVec_mulVec, hL, hd]

theorem isUnit_det_of_mem_unitaryGroup {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) : IsUnit A.det :=
  Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hA)

/-- The Pauli matrix `Y = σ_y`. -/
def yMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

theorem yMat_mem_unitaryGroup : yMat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [yMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- The physical spin time reversal `Θ(ρ) = Y^{⊗3} ρ̄ Y^{⊗3†}`: complex conjugation followed by the
local unitary `Y^{⊗3}`. -/
def timeReverse (ρ : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  locMat yMat yMat yMat * ρ.map star * (locMat yMat yMat yMat)ᴴ

/-- **`cor:ppt3-chirality` (a), complex conjugation.**  For every `t > 0`, in particular throughout
the PPT interval, no local unitary `U_A ⊗ U_B ⊗ U_C` maps `ρ̄_t` to `ρ_t`. -/
theorem ppt3_chirality_conj {t : ℝ} (ht : 0 < t) {UA UB UC : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : UA ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : UB ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hC : UC ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    rhoT t ≠ locMat UA UB UC * (rhoT t).map star * (locMat UA UB UC)ᴴ :=
  no_local_filter_state one_pos (range_rhoT ht) (isUnit_det_of_mem_unitaryGroup hA)
    (isUnit_det_of_mem_unitaryGroup hB) (isUnit_det_of_mem_unitaryGroup hC)

theorem locMat_conjTranspose (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    (locMat A B C)ᴴ = locMat Aᴴ Bᴴ Cᴴ := by
  ext i j
  simp [locMat, conjTranspose_apply, star_mul']

/-- **`cor:ppt3-chirality` (a), spin time reversal.**  For every `t > 0`, `ρ_t` is not related to its
spin time reversal `Θ(ρ_t)` by a local unitary. -/
theorem ppt3_chirality_timeReverse {t : ℝ} (ht : 0 < t) {UA UB UC : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : UA ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : UB ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hC : UC ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    rhoT t ≠ locMat UA UB UC * timeReverse (rhoT t) * (locMat UA UB UC)ᴴ := by
  have key := no_local_filter_state one_pos (range_rhoT ht)
    (isUnit_det_of_mem_unitaryGroup (Submonoid.mul_mem _ hA yMat_mem_unitaryGroup))
    (isUnit_det_of_mem_unitaryGroup (Submonoid.mul_mem _ hB yMat_mem_unitaryGroup))
    (isUnit_det_of_mem_unitaryGroup (Submonoid.mul_mem _ hC yMat_mem_unitaryGroup))
  rw [← locMat_mul UA UB UC yMat yMat yMat, conjTranspose_mul] at key
  simp only [timeReverse, Matrix.mul_assoc] at key ⊢
  exact key

/-- `cor:ppt3-chirality` (a), on the PPT interval of `thm:ppt3-family`. -/
theorem ppt3_chirality_window {t : ℝ} (h1 : tMinus ≤ t) (h2 : t ≤ tPlus) :
    IsPPT3 (rhoT t) ∧ IsGME (rhoT t) ∧
      (∀ {UA UB UC : Matrix (Fin 2) (Fin 2) ℂ}, UA ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        UB ∈ Matrix.unitaryGroup (Fin 2) ℂ → UC ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        rhoT t ≠ locMat UA UB UC * (rhoT t).map star * (locMat UA UB UC)ᴴ ∧
        rhoT t ≠ locMat UA UB UC * timeReverse (rhoT t) * (locMat UA UB UC)ᴴ) := by
  have ht : 0 < t := lt_trans (by norm_num) (lt_of_lt_of_le three_lt_tMinus h1)
  exact ⟨ppt3_family_ppt t h1 h2, ppt3_family_gme_of_tMinus_le t h1,
    fun hA hB hC => ⟨ppt3_chirality_conj ht hA hB hC, ppt3_chirality_timeReverse ht hA hB hC⟩⟩

end

/-- info: 'FormalResearch.PPTThreeQubit.range_rhoT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms range_rhoT

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_chirality_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_chirality_conj

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_chirality_timeReverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_chirality_timeReverse

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_chirality_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_chirality_window

end FormalResearch.PPTThreeQubit
