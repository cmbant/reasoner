module

public import FormalResearch.MatrixAnalysis.TraceDistance
public import FormalResearch.MatrixAnalysis.VectorNorm

/-!
# Kernel-penalty lift: the quantitative form

* `kernel_quant_core`: the scalar inequality `α a² - 2 L a b + (λμ - L) b² ≥ 0` for `λ = (L + L²/α)/μ`;
* `kernel_quant_form`: the conditional quadratic form for an abstract compressed witness `Ω` and map `M`;
* `kernel_quant_matrix`: its matrix form, for an isometric embedding `J` (`Jᴴ J = 1`): the lifted witness
  `W = W₀ + λ KᴴK` satisfies `(J b)† W (J b) ≥ 0`;
* `kernel_lift_distance`: the distance bound `D(ρ, σ) ≥ g/(2L + λβ)` for the lifted witness.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open Matrix
open scoped ComplexOrder InnerProductSpace

noncomputable section

/-- **`eq:ppt3-dist-lift`.**  For the lifted witness `W = W₀ + λ K†K` with `-L ≤ W₀ ≤ L`, `K†K ≤ β`,
`tr(W₀ρ) = -g` for `K ρ = 0` (so `tr(Wρ) = -g`) and `tr(Wσ) ≥ 0`, one has
`½‖ρ - σ‖₁ ≥ g / (2L + λβ)`. -/
theorem kernel_lift_distance {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    {W₀ ρ σ : Matrix n n ℂ} {K : Matrix m n ℂ} {L lam β g : ℝ} (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hβ : 0 ≤ β) (hLβ : 0 < 2 * L + lam * β)
    (hlo : (W₀ + (L : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hhi : ((L : ℂ) • (1 : Matrix n n ℂ) - W₀).PosSemidef)
    (hK : ((β : ℂ) • (1 : Matrix n n ℂ) - Kᴴ * K).PosSemidef)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρt : ρ.trace.re = 1) (hσt : σ.trace.re = 1)
    (hρW : ((W₀ + (lam : ℂ) • (Kᴴ * K)) * ρ).trace.re = -g)
    (hσW : 0 ≤ ((W₀ + (lam : ℂ) • (Kᴴ * K)) * σ).trace.re) :
    g / (2 * L + lam * β) ≤ (1 / 2) * tnorm (ρ - σ) := by
  have hKK : (Kᴴ * K).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self K
  refine distance_lower_bound (W := W₀ + (lam : ℂ) • (Kᴴ * K)) (Λ := lam * β) hL (by positivity)
    hLβ ?_ ?_ hρ hσ hρt hσt hρW hσW
  · have : W₀ + (lam : ℂ) • (Kᴴ * K) + (L : ℂ) • (1 : Matrix n n ℂ) =
        (W₀ + (L : ℂ) • (1 : Matrix n n ℂ)) + (lam : ℂ) • (Kᴴ * K) := by abel
    rw [this]
    exact hlo.add (hKK.smul (by exact_mod_cast hlam))
  · have : (((L + lam * β : ℝ) : ℂ)) • (1 : Matrix n n ℂ) - (W₀ + (lam : ℂ) • (Kᴴ * K)) =
        ((L : ℂ) • (1 : Matrix n n ℂ) - W₀) + (lam : ℂ) • ((β : ℂ) • (1 : Matrix n n ℂ) - Kᴴ * K) := by
      push_cast
      module
    rw [this]
    exact hhi.add (hK.smul (by exact_mod_cast hlam))

/-- **The scalar core of `eq:ppt3-lambda`.**  With `λ = (L + L²/α)/μ` the conditional quadratic form
`α‖u‖² - 2L‖u‖‖v‖ + (λμ - L)‖v‖²` is non-negative. -/
theorem kernel_quant_core {α L μ lam a b : ℝ} (hα : 0 < α) (hμ : 0 < μ)
    (hlam : lam = (L + L ^ 2 / α) / μ) :
    0 ≤ α * a ^ 2 - 2 * L * a * b + (lam * μ - L) * b ^ 2 := by
  have : lam * μ - L = L ^ 2 / α := by
    rw [hlam]; field_simp; ring
  rw [this]
  have e : α * a ^ 2 - 2 * L * a * b + L ^ 2 / α * b ^ 2 = (α * a - L * b) ^ 2 / α := by
    field_simp; ring
  rw [e]
  positivity

section KernelQuant
open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **`prop:ppt3-kernel-quant`, the conditional quadratic form** (abstract form).  `T` is the compressed
witness `Ω = (a† ⊗ I) W₀ (a ⊗ I)` (self-adjoint, `|⟨x, Ωy⟩| ≤ L‖x‖‖y‖` from `‖W₀‖ ≤ L`, `Ω ≥ α` on
`ker M`) and `M = M_c(a)` the kernel-penalty map with `‖Mv‖² ≥ μ‖v‖²` on `(ker M)^⊥`.  Then for
`λ = (L + L²/α)/μ` the form `⟨b, Ωb⟩ + λ‖Mb‖²` is non-negative on all of `E`. -/
theorem kernel_quant_form (T : E →ₗ[ℂ] E) (M : E →ₗ[ℂ] F) {α L μ lam : ℝ} (hα : 0 < α) (hL0 : 0 ≤ L) (hμ : 0 < μ)
    (hlam : lam = (L + L ^ 2 / α) / μ)
    (hT : ∀ x y, ⟪x, T y⟫_ℂ = ⟪T x, y⟫_ℂ)
    (hL : ∀ x y, |(⟪x, T y⟫_ℂ).re| ≤ L * ‖x‖ * ‖y‖)
    (hker : ∀ u, M u = 0 → α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re)
    (hperp : ∀ v ∈ (LinearMap.ker M)ᗮ, μ * ‖v‖ ^ 2 ≤ ‖M v‖ ^ 2) (b : E) :
    0 ≤ (⟪b, T b⟫_ℂ).re + lam * ‖M b‖ ^ 2 := by
  set K : Submodule ℂ E := LinearMap.ker M with hK
  set u : E := K.starProjection b with hu
  set v : E := b - u with hv
  have hu_mem : u ∈ K := K.starProjection_apply_mem b
  have hv_mem : v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal b
  have hMu : M u = 0 := hu_mem
  have hb : b = u + v := by simp [hv]
  have hMb : M b = M v := by rw [hb, map_add, hMu, zero_add]
  have e1 : (⟪b, T b⟫_ℂ).re = (⟪u, T u⟫_ℂ).re + 2 * (⟪u, T v⟫_ℂ).re + (⟪v, T v⟫_ℂ).re := by
    have h1 : (⟪v, T u⟫_ℂ).re = (⟪u, T v⟫_ℂ).re := by
      rw [hT v u]; exact inner_re_symm (𝕜 := ℂ) (T v) u
    conv_lhs => rw [hb]
    simp only [map_add, inner_add_left, inner_add_right, Complex.add_re]
    rw [h1]; ring
  have h1 := hker u hMu
  have h2 := (abs_le.mp (hL u v)).1
  have h3 := (abs_le.mp (hL v v)).1
  have h4 := hperp v hv_mem
  have hcore := kernel_quant_core (a := ‖u‖) (b := ‖v‖) (L := L) hα hμ hlam
  rw [e1, hMb]
  have hlm : 0 ≤ lam := by
    rw [hlam]
    positivity
  nlinarith [norm_nonneg u, norm_nonneg v, mul_le_mul_of_nonneg_left h4 hlm]

/-- info: 'FormalResearch.MatrixAnalysis.kernel_quant_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_quant_form

end KernelQuant

section
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]
variable (W₀ : Matrix ι ι ℂ) (K : Matrix ν ι ℂ) (J : Matrix ι κ ℂ)


theorem star_J_mul (x : κ → ℂ) (A : Matrix ι ι ℂ) (y : κ → ℂ) :
    star x ⬝ᵥ (Jᴴ * A * J) *ᵥ y = star (J *ᵥ x) ⬝ᵥ A *ᵥ (J *ᵥ y) := by
  rw [star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]

theorem normSqVec_J (hJ : Jᴴ * J = 1) (x : κ → ℂ) : normSqVec (J *ᵥ x) = normSqVec x := by
  unfold normSqVec
  have := star_J_mul J x 1 x
  rw [Matrix.mul_one, hJ, Matrix.one_mulVec, Matrix.one_mulVec] at this
  rw [this]

theorem norm_eq_sqrt_normSqVec (x : EuclideanSpace ℂ κ) : ‖x‖ = Real.sqrt (normSqVec x.ofLp) := by
  rw [normSqVec_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

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
    (hL : ∀ p q : ι → ℂ, |(star p ⬝ᵥ W₀ *ᵥ q).re| ≤ L * Real.sqrt (normSqVec p) * Real.sqrt (normSqVec q))
    (hker : ∀ u : κ → ℂ, K *ᵥ (J *ᵥ u) = 0 →
      α * normSqVec u ≤ (star (J *ᵥ u) ⬝ᵥ W₀ *ᵥ (J *ᵥ u)).re)
    (hperp : ∀ v : κ → ℂ, (∀ u, K *ᵥ (J *ᵥ u) = 0 → star u ⬝ᵥ v = 0) →
      μ * normSqVec v ≤ normSqVec (K *ᵥ (J *ᵥ v)))
    (b : κ → ℂ) :
    0 ≤ (star (J *ᵥ b) ⬝ᵥ (W₀ + (lam : ℂ) • (Kᴴ * K)) *ᵥ (J *ᵥ b)).re := by
  set T : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ := Matrix.toEuclideanLin (Jᴴ * W₀ * J) with hT
  set M : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ν := Matrix.toEuclideanLin (K * J) with hM
  have hTi : ∀ x y : EuclideanSpace ℂ κ,
      ⟪x, T y⟫_ℂ = star (J *ᵥ x.ofLp) ⬝ᵥ W₀ *ᵥ (J *ᵥ y.ofLp) := fun x y => by
    rw [hT, inner_toEuclideanLin, star_J_mul]
  have hMo : ∀ x : EuclideanSpace ℂ κ, (M x).ofLp = K *ᵥ (J *ᵥ x.ofLp) := fun x => by
    rw [hM, Matrix.mulVec_mulVec]; rfl
  have hMn : ∀ x : EuclideanSpace ℂ κ, ‖M x‖ ^ 2 = normSqVec (K *ᵥ (J *ᵥ x.ofLp)) := fun x => by
    rw [← normSqVec_eq_norm_sq, hMo]
  have hsym : ∀ x y : EuclideanSpace ℂ κ, ⟪x, T y⟫_ℂ = ⟪T x, y⟫_ℂ := by
    have hH : (Jᴴ * W₀ * J).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hW.eq, Matrix.mul_assoc]
    have := (Matrix.isSymmetric_toEuclideanLin_iff.2 hH)
    intro x y
    exact (this x y).symm
  have key := kernel_quant_form T M hα hL0 hμ hlam hsym
    (fun x y => by
      rw [hTi, norm_eq_sqrt_normSqVec, norm_eq_sqrt_normSqVec, ← normSqVec_J J hJ x.ofLp, ← normSqVec_J J hJ y.ofLp]
      exact hL _ _)
    (fun u hu => by
      have hu' : K *ᵥ (J *ᵥ u.ofLp) = 0 := by rw [← hMo, hu]; rfl
      have := hker u.ofLp hu'
      rw [hTi, ← normSqVec_eq_norm_sq]
      exact this)
    (fun v hv => by
      rw [hMn, ← normSqVec_eq_norm_sq]
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
    unfold normSqVec
    have : star (K *ᵥ (J *ᵥ b)) ⬝ᵥ (K *ᵥ (J *ᵥ b)) = star (J *ᵥ b) ⬝ᵥ (Kᴴ * K) *ᵥ (J *ᵥ b) := by
      rw [star_mulVec, ← Matrix.mulVec_mulVec, ← dotProduct_mulVec]
    rw [this]
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, Matrix.smul_mulVec, dotProduct_smul]
  rw [e1, e2] at key
  simpa [Complex.smul_re] using key

end

/-- info: 'FormalResearch.MatrixAnalysis.kernel_lift_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_lift_distance

/-- info: 'FormalResearch.MatrixAnalysis.kernel_quant_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_quant_matrix

end

end FormalResearch.MatrixAnalysis
