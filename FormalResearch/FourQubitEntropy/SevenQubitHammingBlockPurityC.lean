import Mathlib
import FormalResearch.FourQubitEntropy.SevenQubitIcoXBlockPurity

/-!
# Block Cauchy-Schwarz purity bound for complex Hermitian `ρ` (closes the real-only gap of `block_purity`)

`ResearchNotes/QI/seven_qubit_entanglement/hamming_ball_schmidt.tex`, proof of `thm:hamming-ball-schmidt`:
`tr ρ² ≥ q²/R + (1-q)²/(d-R)` for `q = tr(Qρ)`, `Q` a rank-`R` orthogonal projector.

`SevenQubitIcoXBlockPurity.block_purity` is for real symmetric `ρ`. Here `ρ` is an arbitrary complex
Hermitian `d × d` matrix and `Q` a complex orthogonal projector (`Qᴴ = Q`, `Q² = Q`). All traces of
Hermitian-type products are real, and the statements are about their real parts.

* `block_purity_herm`: `tr(ρ²) ≥ (tr Qρ)²/R + (tr (1-Q)ρ)²/(d-R)` for `0 < R < d`, `tr Q = R`.
* `robust_purity_bound_herm`: with `tr ρ = 1`, `tr(Qρ) ≥ 1 - η` and `1 - η ≥ R/d`, this gives
  `tr ρ² ≥ (1-η)²/R + η²/(d-R)` (`eq:hamming-ball-robust-purity`, given the projector).
* `exists_projector`: for every complex matrix `A` there is an orthogonal projector `Q` with
  `tr Q = rank A` and `Q A = A` (the projector onto the column space; Mathlib `starProjection`).

The monotonicity step is the real-variable lemma `robust_purity_mono` of `SevenQubitIcoXBlockPurity`.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco.Hermitian

open Finset Matrix WithLp

set_option linter.unusedSectionVars false

/-! ### The orthogonal projector onto the column space -/

/-- Every complex matrix `A` has an orthogonal projector `Q` (Hermitian, idempotent) of trace
`rank A` with `Q A = A`: the orthogonal projection onto the column space. -/
theorem exists_projector {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℂ) :
    ∃ Q : Matrix ι ι ℂ, Qᴴ = Q ∧ Q * Q = Q ∧ trace Q = (A.rank : ℂ) ∧ Q * A = A := by
  classical
  let e : EuclideanSpace ℂ ι ≃ₗ[ℂ] (ι → ℂ) := (WithLp.linearEquiv 2 ℂ (ι → ℂ))
  let K : Submodule ℂ (EuclideanSpace ℂ ι) := (LinearMap.range A.mulVecLin).comap e.toLinearMap
  have hK : Module.finrank ℂ K = A.rank := by
    have : K = (LinearMap.range A.mulVecLin).map e.symm.toLinearMap := by
      exact Submodule.comap_equiv_eq_map_symm e _
    rw [this, LinearEquiv.finrank_map_eq]
    rfl
  let P : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι := K.starProjection
  have hPi : P * P = P := K.isIdempotentElem_starProjection
  have hPs : star P = P := (K.starProjection_isSymmetric.isSelfAdjoint).star_eq
  let T := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))
  set Q : Matrix ι ι ℂ := T.symm P with hQ
  have hPQ : T Q = P := by simp [hQ]
  have hmv : ∀ y : ι → ℂ, Q *ᵥ y = ofLp (P (toLp 2 y)) := by
    intro y
    rw [← hPQ]; rfl
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · have : T (star Q) = star (T Q) := map_star T Q
    rw [Matrix.star_eq_conjTranspose] at this
    have e1 : T Qᴴ = T Q := by rw [this, hPQ, hPs]
    exact T.injective e1
  · have e1 : T (Q * Q) = T Q := by rw [map_mul, hPQ, hPi]
    exact T.injective e1
  · have h1 : LinearMap.IsProj K (P : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
      refine ⟨fun x => K.starProjection_apply_mem x, fun x hx => ?_⟩
      exact (Submodule.starProjection_eq_self_iff).2 hx
    have h2 := LinearMap.IsProj.trace h1
    rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun ι ℂ).toBasis] at h2
    have h3 : LinearMap.toMatrix (EuclideanSpace.basisFun ι ℂ).toBasis
        (EuclideanSpace.basisFun ι ℂ).toBasis
        (P : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) = Q := by
      have : (P : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) = Matrix.toEuclideanLin Q := by
        rw [← hPQ]; rfl
      rw [this, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
    rw [h3, hK] at h2
    exact h2
  · have : ∀ x, (Q * A) *ᵥ x = A *ᵥ x := by
      intro x
      rw [← Matrix.mulVec_mulVec, hmv]
      have hmem : toLp 2 (A *ᵥ x) ∈ K := ⟨x, rfl⟩
      rw [(Submodule.starProjection_eq_self_iff).2 hmem]
    exact Matrix.toLin'.injective (LinearMap.ext this)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Frobenius pairing of Hermitian matrices -/

theorem re_trace_conjTranspose_mul_self {κ : Type*} [Fintype κ] (X : Matrix ι κ ℂ) :
    (trace (Xᴴ * X)).re = ∑ i, ∑ j, Complex.normSq (X i j) := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re]

theorem re_trace_conjTranspose_mul_self_nonneg {κ : Type*} [Fintype κ] (X : Matrix ι κ ℂ) :
    0 ≤ (trace (Xᴴ * X)).re := by
  rw [re_trace_conjTranspose_mul_self]
  exact sum_nonneg fun i _ => sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem re_trace_mul_self_nonneg (X : Matrix ι ι ℂ) (hX : Xᴴ = X) : 0 ≤ (trace (X * X)).re := by
  have : X * X = Xᴴ * X := by rw [hX]
  rw [this]; exact re_trace_conjTranspose_mul_self_nonneg X

/-- Cauchy-Schwarz for the Frobenius pairing of two Hermitian matrices (discriminant form). -/
theorem trace_mul_sq_le (A Q : Matrix ι ι ℂ) (hA : Aᴴ = A) (hQ : Qᴴ = Q) :
    (trace (A * Q)).re ^ 2 ≤ (trace (A * A)).re * (trace (Q * Q)).re := by
  have key : ∀ t : ℝ, 0 ≤ (trace (Q * Q)).re * (t * t) + (-2 * (trace (A * Q)).re) * t
      + (trace (A * A)).re := by
    intro t
    set X : Matrix ι ι ℂ := A - (t : ℂ) • Q with hXdef
    have hX : Xᴴ = X := by
      simp [hXdef, conjTranspose_sub, conjTranspose_smul, hA, hQ]
    have h0 := re_trace_mul_self_nonneg X hX
    have : trace (X * X) = trace (A * A) - ((2 * t : ℝ) : ℂ) * trace (A * Q)
        + ((t * t : ℝ) : ℂ) * trace (Q * Q) := by
      have hc : trace (Q * A) = trace (A * Q) := trace_mul_comm Q A
      simp only [hXdef, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, trace_sub, trace_smul,
        smul_eq_mul, hc]
      push_cast
      ring
    rw [this] at h0
    simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul] at h0
    nlinarith [h0]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]

variable (ρ Q : Matrix ι ι ℂ)

theorem compress_bound (hρ : ρᴴ = ρ) (hQ : Qᴴ = Q) (hQ2 : Q * Q = Q) :
    (trace (Q * ρ)).re ^ 2 ≤ (trace Q).re * (trace (Q * ρ * Q * (Q * ρ * Q))).re := by
  have hQ' : ∀ X : Matrix ι ι ℂ, Q * (Q * X) = Q * X := fun X => by rw [← mul_assoc, hQ2]
  have hA : (Q * ρ * Q)ᴴ = Q * ρ * Q := by
    simp [conjTranspose_mul, hρ, hQ, mul_assoc]
  have h := trace_mul_sq_le (Q * ρ * Q) Q hA hQ
  have e1 : trace (Q * ρ * Q * Q) = trace (Q * ρ) := by
    rw [mul_assoc (Q * ρ), hQ2, trace_mul_comm (Q * ρ) Q]
    simp only [hQ']
  have e2 : trace (Q * Q) = trace Q := by rw [hQ2]
  rw [e1, e2] at h
  calc _ ≤ _ := h
    _ = _ := mul_comm _ _

variable {ρ Q}

/-- `tr(ρEρF) = tr((FρE)(EρF))` for idempotents `E`, `F`. -/
theorem trace_cross (E F : Matrix ι ι ℂ) (hE2 : E * E = E) (hF2 : F * F = F) :
    trace (ρ * E * ρ * F) = trace (F * ρ * E * (E * ρ * F)) := by
  have hE' : ∀ X : Matrix ι ι ℂ, E * (E * X) = E * X := fun X => by rw [← mul_assoc, hE2]
  have : F * ρ * E * (E * ρ * F) = F * (ρ * (E * (ρ * F))) := by
    simp only [mul_assoc, hE']
  rw [this, trace_mul_comm F]
  congr 1
  simp only [mul_assoc, hF2]

/-- Splitting `tr ρ²` along `Q` and `1 - Q`. -/
theorem trace_sq_split (hρ : ρᴴ = ρ) (hQ : Qᴴ = Q) (hQ2 : Q * Q = Q) :
    trace (ρ * ρ) = trace (Q * ρ * Q * (Q * ρ * Q)) +
      trace ((1 - Q) * ρ * (1 - Q) * ((1 - Q) * ρ * (1 - Q))) +
      (trace ((Q * ρ * (1 - Q))ᴴ * (Q * ρ * (1 - Q))) +
        trace ((Q * ρ * (1 - Q)) * (Q * ρ * (1 - Q))ᴴ)) := by
  set P : Matrix ι ι ℂ := 1 - Q with hP
  have hP2 : P * P = P := by
    simp only [hP, sub_mul, mul_sub, one_mul, mul_one, hQ2]; abel
  have hPt : Pᴴ = P := by rw [hP]; simp [hQ]
  have h1 : (1 : Matrix ι ι ℂ) = Q + P := by rw [hP]; abel
  have hsplit : trace (ρ * ρ) = trace (ρ * Q * ρ * Q) + trace (ρ * Q * ρ * P) +
      trace (ρ * P * ρ * Q) + trace (ρ * P * ρ * P) := by
    have h2 : ρ * (Q + P) * ρ * (Q + P) = ρ * ρ := by rw [← h1]; simp
    rw [← h2]
    simp only [mul_add, add_mul, trace_add]
    ring
  have hC : (Q * ρ * P)ᴴ = P * ρ * Q := by
    simp [conjTranspose_mul, hPt, hρ, hQ, mul_assoc]
  rw [hsplit, hC, trace_cross Q Q hQ2 hQ2, trace_cross P P hP2 hP2,
    trace_cross Q P hQ2 hP2, trace_cross P Q hP2 hQ2]
  simp only [mul_assoc]
  ring

/-- **Block Cauchy-Schwarz purity bound, complex Hermitian case.** For a complex Hermitian `ρ` and an
orthogonal projector `Q` of trace `R`, `0 < R < d`:
`tr ρ² ≥ (tr Qρ)²/R + (tr (1-Q)ρ)²/(d - R)` (real parts of the traces). -/
theorem block_purity_herm (hρ : ρᴴ = ρ) (hQ : Qᴴ = Q) (hQ2 : Q * Q = Q) (R : ℝ)
    (hR : trace Q = (R : ℂ)) (hR0 : 0 < R) (hRd : R < Fintype.card ι) :
    (trace (Q * ρ)).re ^ 2 / R + (trace ((1 - Q) * ρ)).re ^ 2 / (Fintype.card ι - R) ≤
      (trace (ρ * ρ)).re := by
  set P : Matrix ι ι ℂ := 1 - Q with hP
  have hP2 : P * P = P := by
    simp only [hP, sub_mul, mul_sub, one_mul, mul_one, hQ2]; abel
  have hPt : Pᴴ = P := by rw [hP]; simp [hQ]
  have htP : (trace P).re = Fintype.card ι - R := by
    rw [hP, trace_sub, trace_one]
    simp [hR]
  have hdR : 0 < (Fintype.card ι : ℝ) - R := sub_pos.2 hRd
  have hA := compress_bound ρ Q hρ hQ hQ2
  have hB := compress_bound ρ P hρ hPt hP2
  have hRre : (trace Q).re = R := by rw [hR]; simp
  rw [hRre] at hA
  rw [htP] at hB
  have hsplit := congrArg Complex.re (trace_sq_split (ρ := ρ) hρ hQ hQ2)
  have c1 := re_trace_conjTranspose_mul_self_nonneg (Q * ρ * (1 - Q))
  have c2 : 0 ≤ (trace ((Q * ρ * (1 - Q)) * (Q * ρ * (1 - Q))ᴴ)).re := by
    have := re_trace_conjTranspose_mul_self_nonneg (Q * ρ * (1 - Q))ᴴ
    simpa using this
  rw [hsplit]
  simp only [Complex.add_re]
  have e1 : (trace (Q * ρ)).re ^ 2 / R ≤ (trace (Q * ρ * Q * (Q * ρ * Q))).re := by
    rw [div_le_iff₀ hR0]; linarith
  have e2 : (trace (P * ρ)).re ^ 2 / (Fintype.card ι - R) ≤
      (trace ((1 - Q) * ρ * (1 - Q) * ((1 - Q) * ρ * (1 - Q)))).re := by
    rw [div_le_iff₀ hdR]; linarith
  linarith

/-- **`eq:hamming-ball-robust-purity`, given the projector, complex Hermitian case.** If `tr ρ = 1`,
`Re tr(Qρ) ≥ 1 - η` and `R/d ≤ 1 - η`, then `tr ρ² ≥ (1-η)²/R + η²/(d-R)`. -/
theorem robust_purity_bound_herm (hρ : ρᴴ = ρ) (hQ : Qᴴ = Q) (hQ2 : Q * Q = Q) (R : ℝ)
    (hR : trace Q = (R : ℂ)) (hR0 : 0 < R) (hRd : R < Fintype.card ι) (htr : trace ρ = 1) (η : ℝ)
    (hq : 1 - η ≤ (trace (Q * ρ)).re) (hη : R / Fintype.card ι ≤ 1 - η) :
    (1 - η) ^ 2 / R + η ^ 2 / (Fintype.card ι - R) ≤ (trace (ρ * ρ)).re := by
  have hb := block_purity_herm hρ hQ hQ2 R hR hR0 hRd
  have h1 : (trace ((1 - Q) * ρ)).re = 1 - (trace (Q * ρ)).re := by
    rw [sub_mul, one_mul, trace_sub, htr]
    simp
  rw [h1] at hb
  have hmono := robust_purity_mono R (Fintype.card ι) (1 - η) (trace (Q * ρ)).re hR0 hRd hη hq
  have e : (1 - (1 - η)) = η := by ring
  rw [e] at hmono
  exact hmono.trans hb

end FormalResearch.FourQubitEntropy.SevenQubitIco.Hermitian
