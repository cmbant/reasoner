import FormalResearch.FourQubitEntropy.Realize
import FormalResearch.FourQubitEntropy.MagicCoord
import FormalResearch.FourQubitEntropy.EqualityReduction

/-!
# Maximally mixed marginals and local-unitary laws
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

theorem rhoSite_half (ψ : Psi) (hn : normSqPsi ψ = 1) (hW : blochSq ψ = 0) (i : Fin 4)
    (a a' : Fin 2) : rhoSite i ψ a a' = if a = a' then 1 / 2 else 0 := by
  have hterm : ∀ j ∈ Finset.univ, 0 ≤ (expectation j pauliX ψ).re ^ 2 + (expectation j pauliY ψ).re ^ 2
      + (expectation j pauliZ ψ).re ^ 2 := fun j _ => by positivity
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hW i (Finset.mem_univ i)
  have h3 : ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro x y z h
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  obtain ⟨hx, hy, hz⟩ := h3 _ _ _ h0
  have hc := rhoSite_conj i ψ
  have c01 := hc 0 1
  have c00 := Complex.conj_eq_iff_re.mp (hc 0 0)
  have c11 := Complex.conj_eq_iff_re.mp (hc 1 1)
  simp only [expectation_eq, Fin.sum_univ_two, pauliX, pauliY, pauliZ] at hx hy hz
  simp at hx hy hz
  have htr := normG_rho i ψ
  rw [normG_eq] at htr
  -- the off-diagonal entries vanish
  have r01 : (rhoSite i ψ 0 1).re = 0 := by
    have : (rhoSite i ψ 1 0) = (starRingEnd ℂ) (rhoSite i ψ 0 1) := c01.symm
    rw [this] at hx; simp at hx; linarith
  have i01 : (rhoSite i ψ 0 1).im = 0 := by
    have : (rhoSite i ψ 1 0) = (starRingEnd ℂ) (rhoSite i ψ 0 1) := c01.symm
    rw [this] at hy; simp at hy; linarith
  have z01 : rhoSite i ψ 0 1 = 0 := Complex.ext r01 i01
  have z10 : rhoSite i ψ 1 0 = 0 := by rw [← c01, z01]; simp
  have d : (rhoSite i ψ 0 0).re = (rhoSite i ψ 1 1).re := by linarith
  have e0 : rhoSite i ψ 0 0 = (1 / 2 : ℂ) := by
    have := congrArg Complex.re htr
    simp at this
    apply Complex.ext
    · simp; linarith
    · simp; have := Complex.conj_eq_iff_im.mp (hc 0 0); linarith
  have e1 : rhoSite i ψ 1 1 = (1 / 2 : ℂ) := by
    have := congrArg Complex.re htr
    simp at this
    apply Complex.ext
    · simp; linarith
    · simp; have := Complex.conj_eq_iff_im.mp (hc 1 1); linarith
  fin_cases a <;> fin_cases a' <;> simp [e0, e1, z01, z10]

/-! ### The spin-flip form under local unitaries -/

theorem eps2_conj (a : Op1) : aᵀ * eps2 * a = a.det • eps2 := by
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [eps2, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;> ring

theorem E4_conj (a b : Op1) : (kron a b)ᵀ * E4 * kron a b = (a.det * b.det) • E4 := by
  unfold kron E4 kron
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    eps2_conj, eps2_conj, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]

theorem spinFlip_rowLU (a b : Op1) (ψ : Psi) :
    spinFlipForm (rowLU (kron a b) ψ) = (a.det * b.det) * spinFlipForm ψ := by
  rw [spinFlip_eq_trace, spinFlip_eq_trace, zmat_rowLU, Matrix.transpose_mul]
  have e : (zmat ψ)ᵀ * (kron a b)ᵀ * E4 * (kron a b * zmat ψ) * E4ᵀ
      = (zmat ψ)ᵀ * ((kron a b)ᵀ * E4 * kron a b) * zmat ψ * E4ᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e, E4_conj]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem spinFlip_colLU (c d : Op1) (ψ : Psi) :
    spinFlipForm (colLU (kron c d) ψ) = (c.det * d.det) * spinFlipForm ψ := by
  rw [spinFlip_eq_trace, spinFlip_eq_trace, zmat_colLU, Matrix.transpose_mul, Matrix.transpose_transpose]
  have e : (kron c d) * (zmat ψ)ᵀ * E4 * (zmat ψ * (kron c d)ᵀ) * E4ᵀ
      = (kron c d) * ((zmat ψ)ᵀ * E4 * zmat ψ) * ((kron c d)ᵀ * E4ᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, E4_transpose, ← Matrix.mul_assoc]
  have h : (kron c d)ᵀ * E4 * kron c d = (c.det * d.det) • E4 := E4_conj c d
  rw [Matrix.mul_assoc, h]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Matrix.trace_mul_comm E4]

theorem spinFlip_localApply (a b c d : Op1) (ψ : Psi) :
    spinFlipForm (localApply a b c d ψ) = (c.det * d.det * (a.det * b.det)) * spinFlipForm ψ := by
  unfold localApply
  rw [spinFlip_colLU, spinFlip_rowLU]; ring

theorem spinFlip_localApply_zero {a b c d : Op1} {ψ : Psi} (h : spinFlipForm ψ = 0) :
    spinFlipForm (localApply a b c d ψ) = 0 := by
  rw [spinFlip_localApply, h, mul_zero]

end FormalResearch.FourQubitEntropy
