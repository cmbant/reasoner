import FormalResearch.FourQubitEntropy.EnvelopeCriticalClass

/-!
# Fully product states: `F = 3 N³`, `W₁ = 4 N²`, `τ = 0`

`IsProduct ψ`: `ψ = α ⊗ β ⊗ γ ⊗ δ`. For every product vector (not necessarily normalised), each of the
three balanced cut matrices is a rank-one matrix `g · u u†` (`red12_product`, `red13_product`,
`red14_product`), so `P = 3N²` and `T = 3N³` (`purity_product`, `cubic_product`); the spin-flip form
vanishes (`spinFlip_product`), and the purity identity gives `W₁ = 4N²`. Hence a unit product state has
`F = 3 = (3/4) W₁` and `τ = 0` (`product_values`): the product-state sharpness case of
`thm:fqe-general-envelope`.
-/

open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy

/-- A fully product vector `α ⊗ β ⊗ γ ⊗ δ`. -/
def IsProduct (ψ : Psi) : Prop :=
  ∃ α β γ δ : Fin 2 → ℂ, ∀ a b c d, ψ a b c d = α a * β b * γ c * δ d

theorem trace_rank1_pow (u : Fin 2 × Fin 2 → ℂ) (g : ℝ) :
    (Matrix.trace (((g : ℂ) • Matrix.vecMulVec u (star u)) * ((g : ℂ) • Matrix.vecMulVec u (star u)))).re
        = (g * ∑ i, Complex.normSq (u i)) ^ 2 ∧
    (Matrix.trace (((g : ℂ) • Matrix.vecMulVec u (star u)) * ((g : ℂ) • Matrix.vecMulVec u (star u)) *
      ((g : ℂ) • Matrix.vecMulVec u (star u)))).re = (g * ∑ i, Complex.normSq (u i)) ^ 3 := by
  have hu : star u ⬝ᵥ u = ((∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
    simp [dotProduct, Complex.normSq_eq_conj_mul_self]
  have hM : Matrix.vecMulVec u (star u) * Matrix.vecMulVec u (star u)
      = (((∑ i, Complex.normSq (u i) : ℝ) : ℂ)) • Matrix.vecMulVec u (star u) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hu]
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring
  have htr : Matrix.trace (Matrix.vecMulVec u (star u)) = ((∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm, hu]
  set q : ℝ := ∑ i, Complex.normSq (u i) with hq
  have h2 : ((g : ℂ) • Matrix.vecMulVec u (star u)) * ((g : ℂ) • Matrix.vecMulVec u (star u))
      = ((g : ℂ) ^ 2 * q) • Matrix.vecMulVec u (star u) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hM, smul_smul, smul_smul]; congr 1; ring
  have h3 : ((g : ℂ) • Matrix.vecMulVec u (star u)) * ((g : ℂ) • Matrix.vecMulVec u (star u)) *
      ((g : ℂ) • Matrix.vecMulVec u (star u))
      = ((g : ℂ) ^ 3 * q ^ 2) • Matrix.vecMulVec u (star u) := by
    rw [h2, Matrix.smul_mul, Matrix.mul_smul, hM, smul_smul, smul_smul]; congr 1; ring
  rw [h3, h2, Matrix.trace_smul, Matrix.trace_smul, htr]
  constructor
  · simp only [smul_eq_mul]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  · simp only [smul_eq_mul]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]; ring


section ProductCuts

variable {ψ : Psi} {α β γ δ : Fin 2 → ℂ} (hψ : ∀ a b c d, ψ a b c d = α a * β b * γ c * δ d)
include hψ

theorem red12_product : red12 ψ = (((∑ c, Complex.normSq (γ c)) * (∑ d, Complex.normSq (δ d)) : ℝ) : ℂ) •
    Matrix.vecMulVec (fun i : Fin 2 × Fin 2 => α i.1 * β i.2) (star fun i : Fin 2 × Fin 2 => α i.1 * β i.2) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [red12, hψ, Matrix.vecMulVec_apply, Fin.sum_univ_two,
    Complex.normSq_eq_conj_mul_self]
  ring

theorem red13_product : red13 ψ = (((∑ b, Complex.normSq (β b)) * (∑ d, Complex.normSq (δ d)) : ℝ) : ℂ) •
    Matrix.vecMulVec (fun i : Fin 2 × Fin 2 => α i.1 * γ i.2) (star fun i : Fin 2 × Fin 2 => α i.1 * γ i.2) := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp [red13, hψ, Matrix.vecMulVec_apply, Fin.sum_univ_two,
    Complex.normSq_eq_conj_mul_self]
  ring

theorem red14_product : red14 ψ = (((∑ b, Complex.normSq (β b)) * (∑ c, Complex.normSq (γ c)) : ℝ) : ℂ) •
    Matrix.vecMulVec (fun i : Fin 2 × Fin 2 => α i.1 * δ i.2) (star fun i : Fin 2 × Fin 2 => α i.1 * δ i.2) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp [red14, hψ, Matrix.vecMulVec_apply, Fin.sum_univ_two,
    Complex.normSq_eq_conj_mul_self]
  ring

theorem normSq_product : normSqPsi ψ = (∑ a, Complex.normSq (α a)) * (∑ b, Complex.normSq (β b)) *
    (∑ c, Complex.normSq (γ c)) * (∑ d, Complex.normSq (δ d)) := by
  simp [normSqPsi, hψ, Fin.sum_univ_two, Complex.normSq_mul]
  ring

theorem spinFlip_product : spinFlipForm ψ = 0 := by
  simp only [spinFlipForm, sum4, sum2, Fin.sum_univ_two, toAdd_complex, toMul_complex, lit_complex, hψ]
  simp [sgn]
  ring

omit hψ in
theorem sum_normSq_pair (f g : Fin 2 → ℂ) :
    ∑ i : Fin 2 × Fin 2, Complex.normSq (f i.1 * g i.2) =
      (∑ a, Complex.normSq (f a)) * (∑ b, Complex.normSq (g b)) := by
  simp [Fintype.sum_prod_type, Complex.normSq_mul, Fin.sum_univ_two]
  ring

theorem purity_product : purity ψ = 3 * normSqPsi ψ ^ 2 := by
  have hN := normSq_product hψ
  have h12 := (trace_rank1_pow (fun i : Fin 2 × Fin 2 => α i.1 * β i.2)
    ((∑ c, Complex.normSq (γ c)) * (∑ d, Complex.normSq (δ d)))).1
  have h13 := (trace_rank1_pow (fun i : Fin 2 × Fin 2 => α i.1 * γ i.2)
    ((∑ b, Complex.normSq (β b)) * (∑ d, Complex.normSq (δ d)))).1
  have h14 := (trace_rank1_pow (fun i : Fin 2 × Fin 2 => α i.1 * δ i.2)
    ((∑ b, Complex.normSq (β b)) * (∑ c, Complex.normSq (γ c)))).1
  simp only [sum_normSq_pair] at h12 h13 h14
  unfold purity
  rw [red12_product hψ, red13_product hψ, red14_product hψ, h12, h13, h14, hN]
  ring

theorem cubic_product : cubicMoment ψ = 3 * normSqPsi ψ ^ 3 := by
  have hN := normSq_product hψ
  have h12 := (trace_rank1_pow (fun i : Fin 2 × Fin 2 => α i.1 * β i.2)
    ((∑ c, Complex.normSq (γ c)) * (∑ d, Complex.normSq (δ d)))).2
  have h13 := (trace_rank1_pow (fun i : Fin 2 × Fin 2 => α i.1 * γ i.2)
    ((∑ b, Complex.normSq (β b)) * (∑ d, Complex.normSq (δ d)))).2
  have h14 := (trace_rank1_pow (fun i : Fin 2 × Fin 2 => α i.1 * δ i.2)
    ((∑ b, Complex.normSq (β b)) * (∑ c, Complex.normSq (γ c)))).2
  simp only [sum_normSq_pair] at h12 h13 h14
  unfold cubicMoment
  rw [red12_product hψ, red13_product hψ, red14_product hψ, h12, h13, h14, hN]
  ring

end ProductCuts

/-- Every fully product vector has `P = 3N²`, `F = 3N³`, `W₁ = 4N²`, `s = 0`. -/
theorem product_values {ψ : Psi} (h : IsProduct ψ) :
    sexticF ψ = 3 * normSqPsi ψ ^ 3 ∧ blochSq ψ = 4 * normSqPsi ψ ^ 2 ∧ spinFlipForm ψ = 0 := by
  obtain ⟨α, β, γ, δ, hψ⟩ := h
  have hP := purity_product hψ
  have hT := cubic_product hψ
  have hs := spinFlip_product hψ
  have hid := purity_identity_exact ψ
  rw [hs] at hid
  refine ⟨?_, ?_, hs⟩
  · unfold sexticF; rw [hP, hT]; ring
  · rw [hP] at hid; simp at hid; linarith

end FormalResearch.FourQubitEntropy
