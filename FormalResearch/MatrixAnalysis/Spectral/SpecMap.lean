module

public import FormalResearch.MatrixAnalysis.Spectral.KyFan

/-!
# Diagonal operators in an orthonormal basis (abstract layer)

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved**.

For an orthonormal basis `b` of a finite-dimensional inner product space `E` over `ℝ` or `ℂ` and real
weights `f`, `dop b f` is the operator `x ↦ Σ_i f_i ⟪b_i, x⟫ b_i`.  It is symmetric, `dop b f (b_j) = f_j b_j`,
and `Re⟪x, dop b f x⟫ = Σ_i f_i ‖⟪b_i, x⟫‖²`.  It is the functional calculus `f(T)` of a symmetric `T` in its
eigenbasis, used for the positive part in the Lidskii proof (`Spectral.Lidskii`).
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {ι : Type*} [Fintype ι]

/-- The operator `x ↦ Σ_i f_i ⟪b_i, x⟫ b_i`. -/
noncomputable def dop (b : OrthonormalBasis ι 𝕜 E) (f : ι → ℝ) : E →ₗ[𝕜] E where
  toFun x := ∑ i, ((f i : 𝕜) * inner 𝕜 (b i) x) • b i
  map_add' x y := by
    simp only [inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

theorem dop_apply (b : OrthonormalBasis ι 𝕜 E) (f : ι → ℝ) (x : E) :
    dop b f x = ∑ i, ((f i : 𝕜) * inner 𝕜 (b i) x) • b i := rfl

theorem dop_apply_basis [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (f : ι → ℝ) (j : ι) :
    dop b f (b j) = (f j : 𝕜) • b j := by
  rw [dop_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [b.orthonormal.inner_eq_zero hij]
  · simp

theorem isSymmetric_dop (b : OrthonormalBasis ι 𝕜 E) (f : ι → ℝ) : (dop b f).IsSymmetric := by
  intro x y
  rw [dop_apply, dop_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_smul_right, map_mul, RCLike.conj_ofReal, ← inner_conj_symm x (b i)]
  ring

theorem rq_dop (b : OrthonormalBasis ι 𝕜 E) (f : ι → ℝ) (x : E) :
    rq (dop b f) x = ∑ i, f i * ‖inner 𝕜 (b i) x‖ ^ 2 := by
  unfold rq
  rw [dop_apply, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm x (b i)]
  have : (f i : 𝕜) * inner 𝕜 (b i) x * (starRingEnd 𝕜) (inner 𝕜 (b i) x) =
      ((f i * ‖inner 𝕜 (b i) x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [mul_assoc, RCLike.mul_conj]
    push_cast
    ring
  rw [this, RCLike.ofReal_re]

theorem rq_dop_basis [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (f : ι → ℝ) (j : ι) :
    rq (dop b f) (b j) = f j := by
  rw [rq_dop, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [b.orthonormal.inner_eq_zero hij]
  · simp

end FormalResearch.MatrixAnalysis.Spectral
