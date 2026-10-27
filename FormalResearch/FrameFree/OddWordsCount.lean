import Mathlib
import FormalResearch.FrameFree.OddWordsSl2Skew
import FormalResearch.FrameFree.OddWordsFockData
import FormalResearch.FrameFree.OddWordsGroup
import FormalResearch.FrameFree.TwirlsOdd
import FormalResearch.FrameFree.ScalarChirality

/-!
# The odd-space dimension for one copy (Paper P, `prop:oddwords` (iii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

`finrank_oddSpan : finrank ℝ (Twirls.oddSpan (fun _ : Fin n => ())) = ScalarChirality.oddDim n`:
the real span of the odd words `i (P_σ - P_σ⁻¹)`, `σ ∈ S_n`, has dimension `Σ_j C(g_j, 2)`,
`g_j = C(n, j) - C(n, j-1)` (values `0, 1, 4, 16, 56` for `n = 2..6`, `ScalarChirality.oddDim_values`).

Route: `oddSpan = i · skewSpan` and `skewSpan` is the image of the real space of skew-adjoint operators
commuting with `Lm` and `Lmᵀ` (`skewSpan_eq_map`): the permutations lie in the commutant, and
conversely a real commutant element lies in `blockPermSpan` (`OddWordsGroup`, Schur--Weyl), hence
in the real span of the permutations (`exists_real_split`).  The dimension of the skew commutant is
`finrank_skewComm` applied to `fockData n`.  No Specht modules or Frobenius--Schur indicators are used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Module LinearMap Finset Matrix ComplexConjugate

namespace FormalResearch.FrameFree.OddWords

open FormalResearch.FrameFree.Twirls

variable {n : ℕ}

theorem rperm_transpose (σ : Equiv.Perm (Fin n)) : (rperm σ)ᵀ = rperm σ⁻¹ := by
  ext x y
  simp only [Matrix.transpose_apply, rperm, Matrix.of_apply]
  simp only [eq_comp_iff σ x y]

theorem cx_rperm (σ : Equiv.Perm (Fin n)) : cx (rperm σ) = permOp σ := by
  ext x y
  simp only [cx, rperm, permOp, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem commR_rperm (σ : Equiv.Perm (Fin n)) : CommR (rperm σ) := by
  refine ⟨rperm_mul_Lm σ, ?_⟩
  have h := congrArg Matrix.transpose (rperm_mul_Lm σ⁻¹)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, rperm_transpose, inv_inv] at h
  exact h.symm

/-- The real-linear map `End ℝ (ℝ^{Cube n}) → OpS (Fin n)` (matrix, then complexification). -/
noncomputable def Phi (n : ℕ) : (EuclideanSpace ℝ (Cube n) →ₗ[ℝ] EuclideanSpace ℝ (Cube n)) →ₗ[ℝ]
    OpS (Fin n) where
  toFun Y := cx (Matrix.toEuclideanLin.symm Y)
  map_add' Y Z := by ext x y; simp [cx]
  map_smul' c Y := by ext x y; simp [cx, Complex.real_smul]

theorem Phi_ofMat (X : Matrix (Cube n) (Cube n) ℝ) : Phi n (ofMat X) = cx X := by
  simp [Phi, ofMat]

theorem Phi_injective : Function.Injective (Phi n) := by
  intro Y Z h
  have : Matrix.toEuclideanLin.symm Y = Matrix.toEuclideanLin.symm Z := by
    ext x y
    have := congrFun (congrFun h x) y
    simpa [Phi, cx] using this
  exact Matrix.toEuclideanLin.symm.injective this

/-- `Y ∈ skewComm (fockData n)` iff its matrix is real antisymmetric and commutes with `Lm`, `Lmᵀ`. -/
theorem mem_skewComm_iff (X : Matrix (Cube n) (Cube n) ℝ) :
    ofMat X ∈ (fockData n).skewComm ↔ CommR X ∧ Xᵀ = -X := by
  rw [Sl2Data.mem_skewComm]
  have hL : (fockData n).L = ofMat (Lm n) := rfl
  have hR : (fockData n).R = ofMat (Lm n)ᵀ := by
    rw [Sl2Data.R, hL, adjoint_ofMat_Lm]
  unfold Sl2Data.IsComm CommR
  rw [hL, hR, ← ofMat_mul, ← ofMat_mul, ← ofMat_mul, ← ofMat_mul, ofMat_injective.eq_iff,
    ofMat_injective.eq_iff, ← ofMat_transpose, ← ofMat_neg, ofMat_injective.eq_iff]

theorem CommR.sub {X Y : Matrix (Cube n) (Cube n) ℝ} (hX : CommR X) (hY : CommR Y) : CommR (X - Y) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.mul_sub, hX.1, hY.1]
  · rw [Matrix.sub_mul, Matrix.mul_sub, hX.2, hY.2]

/-- The slot-permutation index pattern for one copy (a single common frame). -/
abbrev pi0 (n : ℕ) : Fin n → Unit := fun _ => ()

theorem Phi_mem_skewSpan {Y : EuclideanSpace ℝ (Cube n) →ₗ[ℝ] EuclideanSpace ℝ (Cube n)}
    (hY : Y ∈ (fockData n).skewComm) : Phi n Y ∈ skewSpan (pi0 n) := by
  obtain ⟨X, rfl⟩ : ∃ X, Y = ofMat X := ⟨Matrix.toEuclideanLin.symm Y, by simp [ofMat]⟩
  rw [mem_skewComm_iff] at hY
  rw [Phi_ofMat]
  obtain ⟨X1, h1, X2, h2, hsplit⟩ := exists_real_split (π := pi0 n) hY.1.mem_blockPermSpan
  have hc1 := realPerm_map_conj (pi0 n) h1
  have hc2 := realPerm_map_conj (pi0 n) h2
  have hcx : (cx X).map conj = cx X := by ext x y; simp [cx]
  have hz : (0 : OpS (Fin n)).map conj = 0 := by ext; simp
  obtain ⟨e1, -⟩ := real_sep hc1 hc2 hcx hz (by rw [← hsplit]; simp)
  have hmem : cx X ∈ realPerm (pi0 n) := by rw [← e1]; exact h1
  have h3 := realPerm_sub_transpose (pi0 n) hmem
  have hT : (cx X)ᵀ = - cx X := by
    ext x y
    have := congrFun (congrFun hY.2 x) y
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    simp [cx, this]
  have h4 : cx X = (1 / 2 : ℝ) • (cx X - (cx X)ᵀ) := by
    rw [hT]; ext x y; simp [Complex.real_smul]; ring
  rw [h4]
  exact Submodule.smul_mem _ _ h3

theorem skewSpan_le_map : skewSpan (pi0 n) ≤ (fockData n).skewComm.map (Phi n) := by
  refine Submodule.span_le.2 ?_
  rintro M ⟨σ, -, rfl⟩
  refine Submodule.mem_map.2 ⟨ofMat (rperm σ - rperm σ⁻¹), ?_, ?_⟩
  · rw [mem_skewComm_iff]
    refine ⟨(commR_rperm σ).sub (commR_rperm σ⁻¹), ?_⟩
    rw [Matrix.transpose_sub, rperm_transpose, rperm_transpose, inv_inv]; abel
  · rw [Phi_ofMat]
    ext x y
    have h1 := congrFun (congrFun (cx_rperm σ) x) y
    have h2 := congrFun (congrFun (cx_rperm σ⁻¹) x) y
    simp only [cx, Matrix.map_apply, Matrix.sub_apply] at h1 h2 ⊢
    rw [← h1, ← h2]; simp

theorem skewSpan_eq_map : skewSpan (pi0 n) = (fockData n).skewComm.map (Phi n) := by
  refine le_antisymm skewSpan_le_map ?_
  rintro _ ⟨Y, hY, rfl⟩
  exact Phi_mem_skewSpan hY

theorem finrank_skewSpan :
    finrank ℝ (skewSpan (pi0 n)) = ∑ k ∈ Finset.range (n / 2 + 1), (hwDim n k).choose 2 := by
  rw [skewSpan_eq_map, ← (fockData n).finrank_skewComm]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ Phi_injective _)).symm

/-- Multiplication by `i`, as a real-linear map on `OpS`. -/
noncomputable def Iop : OpS (Fin n) →ₗ[ℝ] OpS (Fin n) :=
  (LinearMap.lsmul ℂ (OpS (Fin n)) Complex.I).restrictScalars ℝ

theorem Iop_apply (X : OpS (Fin n)) : Iop X = Complex.I • X := rfl

theorem Iop_injective : Function.Injective (Iop (n := n)) := fun _ _ h =>
  smul_right_injective _ Complex.I_ne_zero h

theorem oddSpan_eq_map : oddSpan (pi0 n) = (skewSpan (pi0 n)).map Iop := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro M ⟨σ, hσ, rfl⟩
    exact Submodule.mem_map.2 ⟨permOp σ - permOp σ⁻¹, Submodule.subset_span ⟨σ, hσ, rfl⟩, rfl⟩
  · rintro _ ⟨X, hX, rfl⟩
    exact I_smul_mem_oddSpan (pi0 n) hX

/-- **Paper P, `prop:oddwords` (iii).**  For one copy with a common frame, the real space of odd words
`i (P_σ - P_σ⁻¹)` has dimension `Σ_j C(g_j, 2)`, `g_j = C(n, j) - C(n, j-1)`. -/
theorem finrank_oddSpan (n : ℕ) :
    finrank ℝ (oddSpan (pi0 n)) = FormalResearch.FrameFree.ScalarChirality.oddDim n := by
  rw [oddSpan_eq_map, (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ Iop_injective _)).symm,
    finrank_skewSpan]
  rfl

end FormalResearch.FrameFree.OddWords
