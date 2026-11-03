module

public import FormalResearch.GurvitsBarnum.ContractionUnitary

/-!
# Gurvits–Barnum: an invertible contraction is an average of two unitaries

Source: L. Gurvits and H. Barnum, PRA 66, 062311 (2002); plan lemma L3 (Russo–Dye in finite
dimension), invertible case.

For an invertible contraction `X`, write `XᴴX = W diag(d) Wᴴ` with `0 < d ≤ 1`; then
`V = X W diag(d^{-1/2}) Wᴴ` is unitary, `Z± = W diag(√d ± i √(1-d)) Wᴴ` are unitary and
`X = V (Z₊ + Z₋) / 2`.
-/

@[expose] public section


namespace FormalResearch.GurvitsBarnum
namespace Contr

open Matrix ComplexOrder
open scoped MatrixOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem norm_sqrt_add_I_mul {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ‖((Real.sqrt d : ℝ) : ℂ) + σ * Complex.I * ((Real.sqrt (1 - d) : ℝ) : ℂ)‖ = 1 := by
  have hs := Real.sq_sqrt h0
  have ht := Real.sq_sqrt (sub_nonneg.2 h1)
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith [hs, ht, hσ2]

/-- An invertible contraction is the average of two unitaries. -/
theorem exists_avg_unitary {X : Matrix m m ℂ} (hX : Bdd 1 X) (hdet : X.det ≠ 0) :
    ∃ Y₁ Y₂ : Matrix m m ℂ, Y₁ᴴ * Y₁ = 1 ∧ Y₂ᴴ * Y₂ = 1 ∧
      X = (1 / 2 : ℂ) • (Y₁ + Y₂) := by
  have hpsd := psd_of_bdd zero_le_one hX
  obtain ⟨W, d, hW, hA⟩ := exists_cdiag_of_isHermitian (isHermitian_conjTranspose_mul_self X)
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  have hD : Wᴴ * (Xᴴ * X) * W = diagonal (fun i => (d i : ℂ)) := by
    rw [hA]; unfold cdiag
    calc _ = (Wᴴ * W) * diagonal (fun i => (d i : ℂ)) * (Wᴴ * W) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW]; simp
  have hd0 : ∀ i, 0 ≤ d i := by
    have := (posSemidef_conjTranspose_mul_self X).conjTranspose_mul_mul_same W
    rw [hD, posSemidef_diagonal_iff] at this
    intro i; exact Complex.zero_le_real.1 (this i)
  have hd1 : ∀ i, d i ≤ 1 := by
    have := hpsd.conjTranspose_mul_mul_same W
    have e : Wᴴ * (((1 : ℝ) ^ 2 : ℝ) • (1 : Matrix m m ℂ) - Xᴴ * X) * W
        = diagonal (fun i => 1 - (d i : ℂ)) := by
      have h1 : Wᴴ * (((1 : ℝ) ^ 2 : ℝ) • (1 : Matrix m m ℂ)) * W = 1 := by simp [hW]
      rw [Matrix.mul_sub, Matrix.sub_mul, h1, hD, ← diagonal_one, ← diagonal_sub]
    rw [e, posSemidef_diagonal_iff] at this
    intro i
    have := this i
    rw [sub_nonneg] at this
    exact_mod_cast Complex.real_le_real.1 (by simpa using this)
  have hdpos : ∀ i, 0 < d i := by
    have hdA : (Xᴴ * X).det = ∏ i, (d i : ℂ) := by
      rw [hA]; unfold cdiag
      rw [det_mul, det_mul, det_diagonal]
      have h2 : W.det * Wᴴ.det = 1 := by rw [← det_mul, hW', det_one]
      calc W.det * (∏ i, (d i : ℂ)) * Wᴴ.det = (W.det * Wᴴ.det) * ∏ i, (d i : ℂ) := by ring
        _ = _ := by rw [h2, one_mul]
    have hne : (Xᴴ * X).det ≠ 0 := by
      rw [det_mul, det_conjTranspose]
      exact mul_ne_zero (by simpa using hdet) hdet
    rw [hdA] at hne
    intro i
    have : (d i : ℂ) ≠ 0 := (Finset.prod_ne_zero_iff.1 hne) i (Finset.mem_univ _)
    exact lt_of_le_of_ne (hd0 i) (by intro h; apply this; rw [← h]; simp)
  set sC : m → ℂ := fun i => ((Real.sqrt (d i) : ℝ) : ℂ) with hsC
  set sinv : m → ℂ := fun i => (((Real.sqrt (d i))⁻¹ : ℝ) : ℂ) with hsinv
  set z₁ : m → ℂ := fun i => ((Real.sqrt (d i) : ℝ) : ℂ) +
    ((1 : ℝ) : ℂ) * Complex.I * ((Real.sqrt (1 - d i) : ℝ) : ℂ) with hz₁
  set z₂ : m → ℂ := fun i => ((Real.sqrt (d i) : ℝ) : ℂ) +
    ((-1 : ℝ) : ℂ) * Complex.I * ((Real.sqrt (1 - d i) : ℝ) : ℂ) with hz₂
  have hspos : ∀ i, 0 < Real.sqrt (d i) := fun i => Real.sqrt_pos.2 (hdpos i)
  have hinvs : sinv * sC = 1 := by
    funext i
    simp only [hsinv, hsC, Pi.mul_apply, Pi.one_apply]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hspos i).ne', Complex.ofReal_one]
  have hVV : (X * cdiag W sinv)ᴴ * (X * cdiag W sinv) = 1 := by
    have : (X * cdiag W sinv)ᴴ * (X * cdiag W sinv)
        = cdiag W (star sinv) * (Xᴴ * X) * cdiag W sinv := by
      simp only [conjTranspose_mul, cdiag_conjTranspose, Matrix.mul_assoc]
    rw [this, hA, cdiag_mul hW, cdiag_mul hW, ← cdiag_one hW]
    congr 1
    funext i
    have h := Real.mul_self_sqrt (hd0 i)
    simp only [Pi.mul_apply, Pi.star_apply, hsinv, Pi.one_apply, Complex.star_def,
      Complex.conj_ofReal]
    have hne : ((Real.sqrt (d i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hspos i).ne'
    have hh : (d i : ℂ) = ((Real.sqrt (d i) : ℝ) : ℂ) * ((Real.sqrt (d i) : ℝ) : ℂ) := by
      exact_mod_cast h.symm
    rw [hh]
    push_cast
    field_simp
  have hX' : X = (X * cdiag W sinv) * cdiag W sC := by
    rw [Matrix.mul_assoc, cdiag_mul hW, hinvs, cdiag_one hW, Matrix.mul_one]
  have hz₁n : ∀ i, ‖z₁ i‖ = 1 := fun i =>
    norm_sqrt_add_I_mul (hd0 i) (hd1 i) 1 (Or.inl rfl)
  have hz₂n : ∀ i, ‖z₂ i‖ = 1 := fun i =>
    norm_sqrt_add_I_mul (hd0 i) (hd1 i) (-1) (Or.inr rfl)
  have hun : ∀ z : m → ℂ, (∀ i, ‖z i‖ = 1) →
      ((X * cdiag W sinv) * cdiag W z)ᴴ * ((X * cdiag W sinv) * cdiag W z) = 1 := by
    intro z hz
    calc _ = (cdiag W z)ᴴ * ((X * cdiag W sinv)ᴴ * (X * cdiag W sinv)) * cdiag W z := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hVV, Matrix.mul_one]; exact cdiag_unitary hW hz
  refine ⟨_, _, hun z₁ hz₁n, hun z₂ hz₂n, ?_⟩
  rw [← Matrix.mul_add, ← Matrix.mul_smul, cdiag_add, cdiag_smul]
  conv_lhs => rw [hX']
  congr 2
  funext i
  simp only [hsC, hz₁, hz₂, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  push_cast
  ring

/-- **L3, invertible case.** -/
theorem bdd_map_of_invertible {k : Type*} [Fintype k] [DecidableEq k]
    (φ : Matrix m m ℂ →ₗ[ℂ] Matrix k k ℂ) (hφ : IsPositiveMap φ) (h1 : φ 1 = 1)
    {X : Matrix m m ℂ} (hX : Bdd 1 X) (hdet : X.det ≠ 0) : Bdd 1 (φ X) := by
  obtain ⟨Y₁, Y₂, h₁, h₂, rfl⟩ := exists_avg_unitary hX hdet
  rw [map_smul, map_add]
  exact Bdd.half_add (bdd_map_unitary φ hφ h1 h₁) (bdd_map_unitary φ hφ h1 h₂)

end Contr
end FormalResearch.GurvitsBarnum
