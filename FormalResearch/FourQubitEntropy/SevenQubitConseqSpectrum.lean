import FormalResearch.FourQubitEntropy.SevenQubitConseqPurity
import FormalResearch.FourQubitEntropy.SevenQubitConseqEnvelope

/-!
# Cut spectra of a pure seven-qubit state

For a genuine `3|4` cut `c` and a unit vector `ψ`, the reduced matrix `ρ_c(ψ)` (entries `redEntry`) is a
Hermitian positive semidefinite `8 × 8` matrix of trace `1` whose squared eigenvalues sum to
`cutPurity c ψ`.  Hence its von Neumann entropy `cutEntropy c ψ` (nats) obeys the envelope bound
`cutEntropy c ψ ≤ g₈(cutPurity c ψ)`.
-/

open scoped ComplexConjugate Matrix ComplexOrder
open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

open FormalResearch.FourQubitEntropy.SevenQubitIco

/-- The reduced density matrix of the cut `c`, as a complex matrix. -/
noncomputable def redMatPsi (c : Cut 3 4) (ψ : BitString → ℂ) :
    Matrix (Fin 3 → Bool) (Fin 3 → Bool) ℂ :=
  Matrix.of fun a b => redEntry c ψ a b

theorem redMatPsi_eq_mul (c : Cut 3 4) (ψ : BitString → ℂ) :
    redMatPsi c ψ =
      (Matrix.of fun (a : Fin 3 → Bool) (r : Fin 4 → Bool) => ψ (encode c a r)) *
        (Matrix.of fun (a : Fin 3 → Bool) (r : Fin 4 → Bool) => ψ (encode c a r))ᴴ := by
  ext a b
  simp [redMatPsi, redEntry, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem redMatPsi_posSemidef (c : Cut 3 4) (ψ : BitString → ℂ) : (redMatPsi c ψ).PosSemidef := by
  rw [redMatPsi_eq_mul]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem redMatPsi_isHermitian (c : Cut 3 4) (ψ : BitString → ℂ) : (redMatPsi c ψ).IsHermitian :=
  (redMatPsi_posSemidef c ψ).isHermitian

theorem redMatPsi_trace (c : Cut 3 4) (hc : Function.Bijective c) (ψ : BitString → ℂ)
    (hψ : UnitVec ψ) : (redMatPsi c ψ).trace = 1 := by
  have hf := encode_bijective c hc
  have e : ∑ a : Fin 3 → Bool, ∑ r : Fin 4 → Bool, Complex.normSq (ψ (encode c a r)) = 1 := by
    rw [← hψ, ← Fintype.sum_prod_type'
      (f := fun a r => Complex.normSq (ψ (encode c a r)))]
    exact hf.sum_comp (fun z => Complex.normSq (ψ z))
  have : (redMatPsi c ψ).trace =
      ((∑ a : Fin 3 → Bool, ∑ r : Fin 4 → Bool, Complex.normSq (ψ (encode c a r)) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, redMatPsi, redEntry, Matrix.of_apply,
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ => ?_
    rw [Complex.mul_conj]
  rw [this, e]; simp

/-- `tr ρ² = ∑ λ²` for a Hermitian matrix. -/
theorem trace_sq_eq {A : Matrix (Fin 3 → Bool) (Fin 3 → Bool) ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ 2 := by
  set U : Matrix (Fin 3 → Bool) (Fin 3 → Bool) ℂ := (hA.eigenvectorUnitary : Matrix (Fin 3 → Bool) (Fin 3 → Bool) ℂ) with hU
  set D : Matrix (Fin 3 → Bool) (Fin 3 → Bool) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hspec : A = U * D * Uᴴ := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at this
    exact this
  have hUU : Uᴴ * U = 1 := by
    have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rw [Matrix.star_eq_conjTranspose] at this
    exact this
  have hAA : A * A = U * (D * D) * Uᴴ := by
    calc A * A = (U * D * Uᴴ) * (U * D * Uᴴ) := by rw [← hspec]
      _ = U * (D * (Uᴴ * U) * D) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * (D * D) * Uᴴ := by rw [hUU]; simp [Matrix.mul_assoc]
  rw [hAA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  simp [hD, Matrix.trace, pow_two]

theorem redMatPsi_trace_sq (c : Cut 3 4) (ψ : BitString → ℂ) :
    (redMatPsi c ψ * redMatPsi c ψ).trace = ((cutPurity c ψ : ℝ) : ℂ) := by
  have hH := redMatPsi_isHermitian c ψ
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, cutPurity, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hb : redMatPsi c ψ b a = conj (redMatPsi c ψ a b) := by
    have := congrFun (congrFun hH b) a
    simpa [Matrix.conjTranspose_apply] using this.symm
  rw [hb, Complex.mul_conj]
  rfl

/-- The von Neumann entropy (nats) of the reduced state of the cut `c`. -/
noncomputable def cutEntropy (c : Cut 3 4) (ψ : BitString → ℂ) : ℝ :=
  ∑ i, Real.negMulLog ((redMatPsi_isHermitian c ψ).eigenvalues i)

/-- `E₃`: mean von Neumann entropy (nats) of the 35 three-qubit marginals. -/
noncomputable def meanEntropy3 (ψ : BitString → ℂ) : ℝ :=
  (∑ m ∈ tripleMasks, cutEntropy (maskCut 3 4 m) ψ) / 35

theorem spec_nonneg (c : Cut 3 4) (ψ : BitString → ℂ) (i : Fin 3 → Bool) :
    0 ≤ (redMatPsi_isHermitian c ψ).eigenvalues i :=
  (redMatPsi_posSemidef c ψ).eigenvalues_nonneg i

theorem spec_sum (c : Cut 3 4) (hc : Function.Bijective c) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    ∑ i, (redMatPsi_isHermitian c ψ).eigenvalues i = 1 := by
  have h := (redMatPsi_isHermitian c ψ).trace_eq_sum_eigenvalues
  rw [redMatPsi_trace c hc ψ hψ] at h
  have := congrArg Complex.re h
  simpa using this.symm

theorem spec_sq (c : Cut 3 4) (ψ : BitString → ℂ) :
    ∑ i, (redMatPsi_isHermitian c ψ).eigenvalues i ^ 2 = cutPurity c ψ := by
  have h := trace_sq_eq (redMatPsi_isHermitian c ψ)
  rw [redMatPsi_trace_sq] at h
  have := congrArg Complex.re h
  simpa [← Complex.ofReal_pow, ← Complex.ofReal_sum] using this.symm

theorem card_triple : Fintype.card (Fin 3 → Bool) = 8 := by simp

/-- `1/8 ≤ tr ρ_c² ≤ 1`. -/
theorem cutPurity_mem (c : Cut 3 4) (hc : Function.Bijective c) (ψ : BitString → ℂ)
    (hψ : UnitVec ψ) : 1 / 8 ≤ cutPurity c ψ ∧ cutPurity c ψ ≤ 1 := by
  rw [← spec_sq c ψ]
  exact ⟨sum_sq_ge card_triple _ (spec_sum c hc ψ hψ),
    sum_sq_le _ (spec_nonneg c ψ) (spec_sum c hc ψ hψ)⟩

/-- **Cut entropy envelope.** `S(ρ_c) ≤ g₈(tr ρ_c²)` for every genuine `3|4` cut of a unit vector. -/
theorem cutEntropy_le (c : Cut 3 4) (hc : Function.Bijective c) (ψ : BitString → ℂ)
    (hψ : UnitVec ψ) : cutEntropy c ψ ≤ g8 (cutPurity c ψ) := by
  have := entropy_le_g8 card_triple _ (spec_nonneg c ψ) (spec_sum c hc ψ hψ)
  rw [spec_sq] at this
  exact this

end FormalResearch.FourQubitEntropy.SevenQubitConseq
