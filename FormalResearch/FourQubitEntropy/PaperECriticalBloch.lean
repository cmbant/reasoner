import FormalResearch.FourQubitEntropy.PaperECriticalMomentMap

/-!
# Marginals are moment maps (`lem:fqe-moment-map`)

For a four-qubit vector `ψ` with magic-basis coordinate matrix `X = magicCoord (zmat ψ)`, the six
unnormalised Bloch components of qubits `1, 2` are the six independent entries of the real
antisymmetric matrix `Im (X Xᴴ)`, and those of qubits `3, 4` the entries of `Im (Xᴴ X)`, in an
invertible linear way. Hence `blochSq ψ = 0` (all four one-qubit marginals maximally mixed) holds iff
`X Xᴴ` and `Xᴴ X` are real matrices.

All statements are proved (no hypotheses, no `native_decide`). The magic-basis identities
`Bᴴ (σ ⊗ 1) B = i A` for real antisymmetric `A` are `L_x1 … L_z2` in
`PaperECriticalMomentMap.lean` (CN-1 of the paper).
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-- `X Xᴴ`, the reduced matrix `ρ₁₂` in magic coordinates. -/
noncomputable def Hl (ψ : Psi) : Mat4 := magicCoord (zmat ψ) * (magicCoord (zmat ψ))ᴴ
/-- `Xᴴ X`, the (transposed) reduced matrix `ρ₃₄` in magic coordinates. -/
noncomputable def Hr (ψ : Psi) : Mat4 := (magicCoord (zmat ψ))ᴴ * magicCoord (zmat ψ)

theorem exp_zero (σ : Op1) (A : RMat4)
    (hK : magicBᴴ * kron σ 1 * magicB = Complex.I • A.map Complex.ofReal) (ψ : Psi) :
    expectation 0 σ ψ = Complex.I * ∑ j, ∑ k, (A j k : ℂ) * Hl ψ k j := by
  rw [expectation_eq_trace, actOn_zero, zmat_ofZmat]; exact left_formula _ A hK ψ

theorem exp_one (σ : Op1) (A : RMat4)
    (hK : magicBᴴ * kron 1 σ * magicB = Complex.I • A.map Complex.ofReal) (ψ : Psi) :
    expectation 1 σ ψ = Complex.I * ∑ j, ∑ k, (A j k : ℂ) * Hl ψ k j := by
  rw [expectation_eq_trace, actOn_one, zmat_ofZmat]; exact left_formula _ A hK ψ

theorem exp_two (σ : Op1) (A : RMat4)
    (hK : magicBᴴ * kron σ 1 * magicB = Complex.I • A.map Complex.ofReal) (ψ : Psi) :
    expectation 2 σ ψ = Complex.I * ∑ j, ∑ k, (A j k : ℂ) * Hr ψ j k := by
  rw [expectation_eq_trace, actOn_two, zmat_ofZmat]; exact right_formula _ A hK ψ

theorem exp_three (σ : Op1) (A : RMat4)
    (hK : magicBᴴ * kron 1 σ * magicB = Complex.I • A.map Complex.ofReal) (ψ : Psi) :
    expectation 3 σ ψ = Complex.I * ∑ j, ∑ k, (A j k : ℂ) * Hr ψ j k := by
  rw [expectation_eq_trace, actOn_three, zmat_ofZmat]; exact right_formula _ A hK ψ

theorem re_I_sum (A : RMat4) (f : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ) :
    (Complex.I * ∑ j, ∑ k, (A j k : ℂ) * f j k).re = -∑ j, ∑ k, A j k * (f j k).im := by
  simp [Complex.mul_re, Complex.re_sum, Complex.im_sum]

theorem herm_im {H : Mat4} (hH : Hᴴ = H) (j k : Fin 2 × Fin 2) : (H j k).im = -(H k j).im := by
  have := congrFun (congrFun hH j) k
  simp only [Matrix.conjTranspose_apply] at this
  have h2 := congrArg Complex.im this
  simp at h2
  linarith

theorem Hl_herm (ψ : Psi) : (Hl ψ)ᴴ = Hl ψ := by
  unfold Hl; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem Hr_herm (ψ : Psi) : (Hr ψ)ᴴ = Hr ψ := by
  unfold Hr; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- A real antisymmetric matrix killed by the six functionals `J ↦ Σ A_s J` vanishes. -/
theorem zero_of_six (J : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℝ) (hJ : ∀ j k, J j k = -J k j)
    (e1 : ∑ j, ∑ k, A_x1 j k * J k j = 0) (e2 : ∑ j, ∑ k, A_x2 j k * J k j = 0)
    (e3 : ∑ j, ∑ k, A_y1 j k * J k j = 0) (e4 : ∑ j, ∑ k, A_y2 j k * J k j = 0)
    (e5 : ∑ j, ∑ k, A_z1 j k * J k j = 0) (e6 : ∑ j, ∑ k, A_z2 j k * J k j = 0) :
    ∀ j k, J j k = 0 := by
  have d : ∀ j, J j j = 0 := fun j => by have := hJ j j; linarith
  simp [A_x1, A_x2, A_y1, A_y2, A_z1, A_z2, Eu, Fintype.sum_prod_type, Fin.sum_univ_two] at e1 e2 e3 e4 e5 e6
  intro j k
  obtain ⟨j1, j2⟩ := j
  obtain ⟨k1, k2⟩ := k
  have h1 := hJ (0, 0) (0, 1)
  have h2 := hJ (0, 0) (1, 0)
  have h3 := hJ (0, 0) (1, 1)
  have h4 := hJ (0, 1) (1, 0)
  have h5 := hJ (0, 1) (1, 1)
  have h6 := hJ (1, 0) (1, 1)
  have d1 := d (0, 0)
  have d2 := d (0, 1)
  have d3 := d (1, 0)
  have d4 := d (1, 1)
  fin_cases j1 <;> fin_cases j2 <;> fin_cases k1 <;> fin_cases k2 <;> simp <;>
    first | assumption | linarith


/-- Real parts of the six Bloch components of qubits `1, 2`. -/
theorem re_exp_left (ψ : Psi) :
    (expectation 0 pauliX ψ).re = -∑ j, ∑ k, A_x1 j k * (Hl ψ k j).im ∧
    (expectation 1 pauliX ψ).re = -∑ j, ∑ k, A_x2 j k * (Hl ψ k j).im ∧
    (expectation 0 pauliY ψ).re = -∑ j, ∑ k, A_y1 j k * (Hl ψ k j).im ∧
    (expectation 1 pauliY ψ).re = -∑ j, ∑ k, A_y2 j k * (Hl ψ k j).im ∧
    (expectation 0 pauliZ ψ).re = -∑ j, ∑ k, A_z1 j k * (Hl ψ k j).im ∧
    (expectation 1 pauliZ ψ).re = -∑ j, ∑ k, A_z2 j k * (Hl ψ k j).im := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exp_zero _ _ L_x1, re_I_sum]
  · rw [exp_one _ _ L_x2, re_I_sum]
  · rw [exp_zero _ _ L_y1, re_I_sum]
  · rw [exp_one _ _ L_y2, re_I_sum]
  · rw [exp_zero _ _ L_z1, re_I_sum]
  · rw [exp_one _ _ L_z2, re_I_sum]

/-- Real parts of the six Bloch components of qubits `3, 4`. -/
theorem re_exp_right (ψ : Psi) :
    (expectation 2 pauliX ψ).re = -∑ j, ∑ k, A_x1 j k * (Hr ψ j k).im ∧
    (expectation 3 pauliX ψ).re = -∑ j, ∑ k, A_x2 j k * (Hr ψ j k).im ∧
    (expectation 2 pauliY ψ).re = -∑ j, ∑ k, A_y1 j k * (Hr ψ j k).im ∧
    (expectation 3 pauliY ψ).re = -∑ j, ∑ k, A_y2 j k * (Hr ψ j k).im ∧
    (expectation 2 pauliZ ψ).re = -∑ j, ∑ k, A_z1 j k * (Hr ψ j k).im ∧
    (expectation 3 pauliZ ψ).re = -∑ j, ∑ k, A_z2 j k * (Hr ψ j k).im := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exp_two _ _ L_x1]; exact re_I_sum _ (fun j k => Hr ψ j k)
  · rw [exp_three _ _ L_x2]; exact re_I_sum _ (fun j k => Hr ψ j k)
  · rw [exp_two _ _ L_y1]; exact re_I_sum _ (fun j k => Hr ψ j k)
  · rw [exp_three _ _ L_y2]; exact re_I_sum _ (fun j k => Hr ψ j k)
  · rw [exp_two _ _ L_z1]; exact re_I_sum _ (fun j k => Hr ψ j k)
  · rw [exp_three _ _ L_z2]; exact re_I_sum _ (fun j k => Hr ψ j k)

/-- **`lem:fqe-moment-map`** (proved, no hypotheses): all one-qubit marginals of `ψ` are maximally
mixed (`blochSq ψ = 0`) iff `X Xᴴ` and `Xᴴ X` are real, where `X = magicCoord (zmat ψ)`. -/
theorem blochSq_eq_zero_iff (ψ : Psi) :
    blochSq ψ = 0 ↔ (∀ j k, (Hl ψ j k).im = 0) ∧ (∀ j k, (Hr ψ j k).im = 0) := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := re_exp_left ψ
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := re_exp_right ψ
  constructor
  · intro h
    unfold blochSq at h
    have hz : ∀ i, (expectation i pauliX ψ).re ^ 2 + (expectation i pauliY ψ).re ^ 2
        + (expectation i pauliZ ψ).re ^ 2 = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))).mp h i
        (Finset.mem_univ i)
      exact this
    have hc : ∀ i, (expectation i pauliX ψ).re = 0 ∧ (expectation i pauliY ψ).re = 0 ∧
        (expectation i pauliZ ψ).re = 0 := by
      intro i
      have := hz i
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (expectation i pauliX ψ).re,
        sq_nonneg (expectation i pauliY ψ).re, sq_nonneg (expectation i pauliZ ψ).re]
    obtain ⟨a0, b0, c0⟩ := hc 0
    obtain ⟨a1, b1, c1⟩ := hc 1
    obtain ⟨a2, b2, c2⟩ := hc 2
    obtain ⟨a3, b3, c3⟩ := hc 3
    constructor
    · exact zero_of_six (fun j k => (Hl ψ j k).im) (fun j k => herm_im (Hl_herm ψ) j k)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    · have := zero_of_six (fun j k => (Hr ψ k j).im)
        (fun j k => (herm_im (Hr_herm ψ) k j)) (by beta_reduce; linarith) (by beta_reduce; linarith)
        (by beta_reduce; linarith) (by beta_reduce; linarith) (by beta_reduce; linarith)
        (by beta_reduce; linarith)
      intro j k; exact this k j
  · rintro ⟨hl, hr⟩
    unfold blochSq
    simp [Fin.sum_univ_four, l1, l2, l3, l4, l5, l6, r1, r2, r3, r4, r5, r6, hl, hr]

end FormalResearch.FourQubitEntropy.PaperECritical
