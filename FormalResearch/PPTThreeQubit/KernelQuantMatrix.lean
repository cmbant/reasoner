module

public import FormalResearch.PPTThreeQubit.TraceDistance

/-!
# `prop:ppt3-kernel-quant` in matrix form

`kernel_quant_matrix` is `kernel_quant_form` (`TraceDistance.lean`) for the compressed witness
`Ω = Jᴴ W₀ J` and kernel-penalty map `M = K J`, where `J` is an isometric embedding (`Jᴴ J = 1`,
for a cut `c` and unit `a`, `J = U_c†(a ⊗ ·)`): for `λ = (L + L²/α)/μ` the lifted witness
`W = W₀ + λ KᴴK` satisfies `(J b)† W (J b) ≥ 0` for every `b`.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix
open scoped InnerProductSpace

noncomputable section

section
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

/-- The squared Euclidean norm of a vector, as `Re (v† v)`. -/
def nsq (v : ι → ℂ) : ℝ := (star v ⬝ᵥ v).re

theorem nsq_nonneg (v : ι → ℂ) : 0 ≤ nsq v := by
  unfold nsq
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  simp [Complex.star_def, Complex.mul_re]
  nlinarith [sq_nonneg (v i).re, sq_nonneg (v i).im]

theorem nsq_eq_norm_sq (x : EuclideanSpace ℂ ι) : nsq x.ofLp = ‖x‖ ^ 2 := by
  have h := @inner_self_eq_norm_sq_to_K ℂ _ _ _ _ x
  have h2 : (inner ℂ x x : ℂ) = star x.ofLp ⬝ᵥ x.ofLp := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  unfold nsq
  rw [← h2, h]
  simp [← Complex.ofReal_pow]

variable (W₀ : Matrix ι ι ℂ) (K : Matrix ν ι ℂ) (J : Matrix ι κ ℂ)

theorem star_J_mul (x : κ → ℂ) (A : Matrix ι ι ℂ) (y : κ → ℂ) :
    star x ⬝ᵥ (Jᴴ * A * J) *ᵥ y = star (J *ᵥ x) ⬝ᵥ A *ᵥ (J *ᵥ y) := by
  rw [star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]

theorem nsq_J (hJ : Jᴴ * J = 1) (x : κ → ℂ) : nsq (J *ᵥ x) = nsq x := by
  unfold nsq
  have := star_J_mul J x 1 x
  rw [Matrix.mul_one, hJ, Matrix.one_mulVec, Matrix.one_mulVec] at this
  rw [this]


theorem norm_eq_sqrt_nsq (x : EuclideanSpace ℂ κ) : ‖x‖ = Real.sqrt (nsq x.ofLp) := by
  rw [nsq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem inner_toEuclideanLin (A : Matrix κ κ ℂ) (x y : EuclideanSpace ℂ κ) :
    ⟪x, Matrix.toEuclideanLin A y⟫_ℂ = star x.ofLp ⬝ᵥ A *ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- **`prop:ppt3-kernel-quant` (matrix form).**  `J` isometric (`Jᴴ J = 1`), `W₀` Hermitian with
`|⟨p, W₀ q⟩| ≤ L ‖p‖‖q‖`, `W₀ ≥ α` on `{J u : K J u = 0}` (in the compressed sense), and
`‖K J v‖² ≥ μ‖v‖²` for `v` orthogonal to `{u : K J u = 0}`.  Then for
`λ = (L + L²/α)/μ`, `(J b)† (W₀ + λ KᴴK) (J b) ≥ 0` for every `b`. -/
theorem kernel_quant_matrix (hJ : Jᴴ * J = 1) (hW : W₀.IsHermitian) {α L μ lam : ℝ}
    (hα : 0 < α) (hL0 : 0 ≤ L) (hμ : 0 < μ) (hlam : lam = (L + L ^ 2 / α) / μ)
    (hL : ∀ p q : ι → ℂ, |(star p ⬝ᵥ W₀ *ᵥ q).re| ≤ L * Real.sqrt (nsq p) * Real.sqrt (nsq q))
    (hker : ∀ u : κ → ℂ, K *ᵥ (J *ᵥ u) = 0 →
      α * nsq u ≤ (star (J *ᵥ u) ⬝ᵥ W₀ *ᵥ (J *ᵥ u)).re)
    (hperp : ∀ v : κ → ℂ, (∀ u, K *ᵥ (J *ᵥ u) = 0 → star u ⬝ᵥ v = 0) →
      μ * nsq v ≤ nsq (K *ᵥ (J *ᵥ v)))
    (b : κ → ℂ) :
    0 ≤ (star (J *ᵥ b) ⬝ᵥ (W₀ + (lam : ℂ) • (Kᴴ * K)) *ᵥ (J *ᵥ b)).re := by
  set T : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ := Matrix.toEuclideanLin (Jᴴ * W₀ * J) with hT
  set M : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ν := Matrix.toEuclideanLin (K * J) with hM
  have hTi : ∀ x y : EuclideanSpace ℂ κ,
      ⟪x, T y⟫_ℂ = star (J *ᵥ x.ofLp) ⬝ᵥ W₀ *ᵥ (J *ᵥ y.ofLp) := fun x y => by
    rw [hT, inner_toEuclideanLin, star_J_mul]
  have hMo : ∀ x : EuclideanSpace ℂ κ, (M x).ofLp = K *ᵥ (J *ᵥ x.ofLp) := fun x => by
    rw [hM, Matrix.mulVec_mulVec]; rfl
  have hMn : ∀ x : EuclideanSpace ℂ κ, ‖M x‖ ^ 2 = nsq (K *ᵥ (J *ᵥ x.ofLp)) := fun x => by
    rw [← nsq_eq_norm_sq, hMo]
  have hsym : ∀ x y : EuclideanSpace ℂ κ, ⟪x, T y⟫_ℂ = ⟪T x, y⟫_ℂ := by
    have hH : (Jᴴ * W₀ * J).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hW.eq, Matrix.mul_assoc]
    have := (Matrix.isSymmetric_toEuclideanLin_iff.2 hH)
    intro x y
    exact (this x y).symm
  have key := kernel_quant_form T M hα hL0 hμ hlam hsym
    (fun x y => by
      rw [hTi, norm_eq_sqrt_nsq, norm_eq_sqrt_nsq, ← nsq_J J hJ x.ofLp, ← nsq_J J hJ y.ofLp]
      exact hL _ _)
    (fun u hu => by
      have hu' : K *ᵥ (J *ᵥ u.ofLp) = 0 := by rw [← hMo, hu]; rfl
      have := hker u.ofLp hu'
      rw [hTi, ← nsq_eq_norm_sq]
      exact this)
    (fun v hv => by
      rw [hMn, ← nsq_eq_norm_sq]
      refine hperp v.ofLp (fun u hu => ?_)
      have hu' : M (WithLp.toLp 2 u) = 0 := by
        apply WithLp.ofLp_injective
        rw [hMo]; exact hu
      have := (Submodule.mem_orthogonal _ _).1 hv (WithLp.toLp 2 u) hu'
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
      simpa using this)
    (WithLp.toLp 2 b)
  have e1 : (⟪(WithLp.toLp 2 b : EuclideanSpace ℂ κ), T (WithLp.toLp 2 b)⟫_ℂ).re =
      (star (J *ᵥ b) ⬝ᵥ W₀ *ᵥ (J *ᵥ b)).re := by
    rw [hTi]
  have e2 : ‖M (WithLp.toLp 2 b)‖ ^ 2 = (star (J *ᵥ b) ⬝ᵥ (Kᴴ * K) *ᵥ (J *ᵥ b)).re := by
    rw [hMn]
    unfold nsq
    have : star (K *ᵥ (J *ᵥ b)) ⬝ᵥ (K *ᵥ (J *ᵥ b)) = star (J *ᵥ b) ⬝ᵥ (Kᴴ * K) *ᵥ (J *ᵥ b) := by
      rw [star_mulVec, ← Matrix.mulVec_mulVec, ← dotProduct_mulVec]
    rw [this]
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, Matrix.smul_mulVec, dotProduct_smul]
  rw [e1, e2] at key
  simpa [Complex.smul_re] using key

end

end

end FormalResearch.PPTThreeQubit
