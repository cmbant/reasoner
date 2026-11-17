module

public import FormalResearch.MatrixAnalysis.Spectral.MinMax

/-!
# Fan–Hoffman: the polar factor is a nearest isometry in operator norm

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

Let `E, F` be finite-dimensional inner product spaces over `ℝ` or `ℂ`, `T : E →ₗ F` and let `T = U ∘ R` be a
*polar decomposition*: `R : E →ₗ E` positive (Mathlib `LinearMap.IsPositive`) and `U : E →ₗ F` isometric.

* `fanHoffman_polar`: for every linear isometry `V : E →ₗ F` and `ε ≥ 0`, `‖(T - V) x‖ ≤ ε ‖x‖` for all `x`
  implies `‖(T - U) x‖ ≤ ε ‖x‖` for all `x`; i.e. `‖T - U‖_op ≤ ‖T - V‖_op` (K. Fan and A. J. Hoffman, *Some
  metric inequalities in the space of matrices*, Proc. AMS 6 (1955), operator-norm case; the cited result holds
  for every unitarily invariant norm).
* `polarRoot_eigenvalue_mem`: every eigenvalue of `R` lies in `[1 - ε, 1 + ε]`.

The proof is elementary: on an eigenvector `b_i` of `R` with eigenvalue `ρ_i ≥ 0`, `ρ_i = ‖R b_i‖ = ‖T b_i‖`
and `|‖T b_i‖ - ‖V b_i‖| ≤ ‖(T - V) b_i‖ ≤ ε` with `‖V b_i‖ = 1`; hence `‖(R - 1) x‖ ≤ ε ‖x‖` by expansion in
the eigenbasis, and `T - U = U (R - 1)`.  The corollary for `Racah.Polar.polarFactor` is in
`Spectral.FanHoffmanPolar`.

Not formalised here: the Frobenius-norm and general unitarily invariant norm versions, the strict-uniqueness
statement, and the existence of a polar decomposition for non-injective `T` (injective real `T` is
`Racah.Polar.polarFactor`).
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {T V U : E →ₗ[𝕜] F} {R : E →ₗ[𝕜] E} {N : ℕ} (hN : finrank 𝕜 E = N)

include hN in
/-- Every eigenvalue of the positive factor `R` lies within `ε` of `1`. -/
theorem polarRoot_eigenvalue_mem (hR : R.IsPositive) (hU : ∀ x, ‖U x‖ = ‖x‖) (hV : ∀ x, ‖V x‖ = ‖x‖)
    (hTUR : ∀ x, T x = U (R x)) {ε : ℝ} (h : ∀ x, ‖(T - V) x‖ ≤ ε * ‖x‖) (i : Fin N) :
    |hR.isSymmetric.eigenvalues hN i - 1| ≤ ε := by
  set b := hR.isSymmetric.eigenvectorBasis hN i with hb
  set μ := hR.isSymmetric.eigenvalues hN i with hμ
  have hb1 : ‖b‖ = 1 := (hR.isSymmetric.eigenvectorBasis hN).orthonormal.1 i
  have hRb : R b = (μ : 𝕜) • b := hR.isSymmetric.apply_eigenvectorBasis hN i
  have hμ0 : 0 ≤ μ := hR.nonneg_eigenvalues hN i
  have h1 : ‖T b‖ = μ := by
    rw [hTUR, hU, hRb, norm_smul, hb1]
    simp [abs_of_nonneg hμ0]
  have h2 : ‖V b‖ = 1 := by rw [hV, hb1]
  have h3 := abs_norm_sub_norm_le (T b) (V b)
  rw [h1, h2] at h3
  refine h3.trans ?_
  have := h b
  rw [hb1, mul_one] at this
  simpa using this

include hN in
/-- **Fan–Hoffman (operator norm).**  If `T = U ∘ R` is a polar decomposition then `U` is at least as close to `T`
as any linear isometry `V`: `‖T - V‖_op ≤ ε` implies `‖T - U‖_op ≤ ε`. -/
theorem fanHoffman_polar (hR : R.IsPositive) (hU : ∀ x, ‖U x‖ = ‖x‖) (hV : ∀ x, ‖V x‖ = ‖x‖)
    (hTUR : ∀ x, T x = U (R x)) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ x, ‖(T - V) x‖ ≤ ε * ‖x‖) (x : E) :
    ‖(T - U) x‖ ≤ ε * ‖x‖ := by
  have hs := hR.isSymmetric
  set b := hs.eigenvectorBasis hN with hb
  have hmem := polarRoot_eigenvalue_mem hN hR hU hV hTUR h
  have e1 : (T - U) x = U (R x - x) := by
    rw [LinearMap.sub_apply, hTUR, map_sub]
  rw [e1, hU]
  have key : ‖R x - x‖ ^ 2 ≤ (ε * ‖x‖) ^ 2 := by
    rw [← b.sum_sq_norm_inner_right (R x - x), mul_pow, ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have e2 : inner 𝕜 (b i) (R x - x) =
        ((hs.eigenvalues hN i - 1 : ℝ) : 𝕜) * inner 𝕜 (b i) x := by
      rw [inner_sub_right, ← hs (b i) x, hb, hs.apply_eigenvectorBasis hN i, inner_smul_left]
      simp [sub_mul]
    rw [e2, norm_mul, mul_pow]
    have : ‖((hs.eigenvalues hN i - 1 : ℝ) : 𝕜)‖ ^ 2 ≤ ε ^ 2 := by
      rw [RCLike.norm_ofReal]
      exact pow_le_pow_left₀ (abs_nonneg _) (hmem i) 2
    exact mul_le_mul_of_nonneg_right this (by positivity)
  exact le_of_sq_le_sq key (by positivity)

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.polarRoot_eigenvalue_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.polarRoot_eigenvalue_mem

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.fanHoffman_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.fanHoffman_polar

end FormalResearch.MatrixAnalysis.Spectral
