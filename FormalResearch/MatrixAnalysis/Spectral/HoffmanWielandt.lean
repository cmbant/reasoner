module

public import FormalResearch.MatrixAnalysis.Spectral.Lidskii

/-!
# Hoffman–Wielandt inequality and von Neumann's trace inequality (abstract layer)

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

For symmetric operators `A, B` on an `N`-dimensional inner product space over `ℝ` or `ℂ` with descending
eigenvalues `α_j`, `β_j` and `γ_i = μ_i(A - B)`:

* `sum_sq_eigenvalues_eq`: `Σ_i μ_i(T)² = Σ_j ‖T b_j‖²` for any orthonormal basis `b` (Frobenius norm).
* `abel_nonneg`: Abel summation for an antitone weight and prefix sums `≥ 0` with total `0`.
* `sum_mul_rq_le`: **von Neumann's trace inequality** (Hermitian form) `Σ_j β_j Re⟪b_j, A b_j⟫ ≤ Σ_j α_j β_j`
  for `b` the eigenbasis of `B`; this is `Re tr(AB) ≤ Σ_j α_j β_j`.
* `hoffman_wielandt`: **Hoffman–Wielandt**, `Σ_j (α_j - β_j)² ≤ Σ_i γ_i² = ‖A - B‖_F²`.

The proof is von Neumann's trace inequality from the Ky Fan inequality (`Spectral.KyFan`) by Abel summation,
then expanding `‖A - B‖_F²` (Hoffman–Wielandt 1953; Bhatia, *Matrix Analysis*, Thm VI.4.1, via Ex. II.1.16).

Not formalised here: the equality case, the non-normal Hoffman–Wielandt for normal matrices, and the
Frobenius-norm form of Lidskii for general unitarily invariant norms.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module

/-- Abel summation: if `β` is antitone on `[0,n)`, all prefix sums of `d` (up to `n`) are `≥ 0` and the total
is `0`, then `Σ β_j d_j ≥ 0`. -/
theorem abel_nonneg (β d : ℕ → ℝ) (n : ℕ) (hβ : ∀ i j, i ≤ j → j < n → β j ≤ β i)
    (hD : ∀ k ≤ n, 0 ≤ ∑ j ∈ Finset.range k, d j) (hD0 : ∑ j ∈ Finset.range n, d j = 0) :
    0 ≤ ∑ j ∈ Finset.range n, β j * d j := by
  have key : ∀ m ≤ n, ∀ c : ℝ, (∀ j < m, c ≤ β j) →
      c * ∑ j ∈ Finset.range m, d j ≤ ∑ j ∈ Finset.range m, β j * d j := by
    intro m
    induction m with
    | zero => intro _ c _; simp
    | succ m ih =>
      intro hm c hc
      have h1 := ih (by omega) (β m) (fun j hj => hβ j m hj.le (by omega))
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h2 := hD (m + 1) hm
      rw [Finset.sum_range_succ] at h2
      have h3 : c ≤ β m := hc m (by omega)
      nlinarith
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have := key n le_rfl (β (n - 1)) (fun j hj => hβ j (n - 1) (by omega) (by omega))
    rw [hD0] at this
    simpa using this

section Frobenius

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {N : ℕ} (hN : finrank 𝕜 E = N)

include hT in
/-- **Frobenius norm via eigenvalues.**  `Σ_i μ_i² = Σ_j ‖T b_j‖²` for any orthonormal basis `b`. -/
theorem sum_sq_eigenvalues_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, hT.eigenvalues hN i ^ 2 = ∑ j, ‖T (b j)‖ ^ 2 := by
  have h1 : ∀ j, ‖T (b j)‖ ^ 2 = ∑ i, hT.eigenvalues hN i ^ 2 *
      ‖inner 𝕜 (hT.eigenvectorBasis hN i) (b j)‖ ^ 2 := by
    intro j
    rw [← (hT.eigenvectorBasis hN).sum_sq_norm_inner_right (T (b j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hT (hT.eigenvectorBasis hN i) (b j), hT.apply_eigenvectorBasis hN i, inner_smul_left]
    simp [mul_pow]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, b.sum_sq_norm_inner_left, (hT.eigenvectorBasis hN).orthonormal.1 i]
  simp

end Frobenius

/-- Extension of a `Fin N`-indexed sequence by zero. -/
def extZero {N : ℕ} (g : Fin N → ℝ) (j : ℕ) : ℝ := if h : j < N then g ⟨j, h⟩ else 0

theorem sum_range_extZero {N k : ℕ} (hk : k ≤ N) (g : Fin N → ℝ) :
    ∑ j ∈ Finset.range k, extZero g j =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), g i := by
  rw [← sum_castLE_eq_sum_filter hk g, ← Fin.sum_univ_eq_sum_range (extZero g) k]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (j : ℕ) < N := lt_of_lt_of_le j.isLt hk
  simp only [extZero, this, dite_true]
  rfl

section VonNeumann

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) {N : ℕ}
  (hN : finrank 𝕜 E = N)

include hA hB in
/-- **Von Neumann's trace inequality (Hermitian form).**  With `b` the eigenbasis of `B`,
`Σ_j μ_j(B) Re⟪b_j, A b_j⟫ ≤ Σ_j μ_j(A) μ_j(B)`; the left side is `Re tr(AB)`. -/
theorem sum_mul_rq_le :
    ∑ j, hB.eigenvalues hN j * rq A (hB.eigenvectorBasis hN j) ≤
      ∑ j, hB.eigenvalues hN j * hA.eigenvalues hN j := by
  set r : Fin N → ℝ := fun j => rq A (hB.eigenvectorBasis hN j) with hr
  have hD : ∀ k ≤ N, 0 ≤ ∑ j ∈ Finset.range k, (extZero (fun i => hA.eigenvalues hN i) j - extZero r j) := by
    intro k hk
    rw [Finset.sum_sub_distrib, sum_range_extZero hk, sum_range_extZero hk, sub_nonneg]
    obtain ⟨hu, -⟩ := kyFan_attained hB hN hk
    have := kyFan_le hA hN hu
    simp only [Fintype.card_fin] at this
    rwa [sum_castLE_eq_sum_filter hk (fun i => rq A (hB.eigenvectorBasis hN i))] at this
  have hD0 : ∑ j ∈ Finset.range N, (extZero (fun i => hA.eigenvalues hN i) j - extZero r j) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    have hk : N ≤ N := le_rfl
    rw [sum_range_extZero hk, sum_range_extZero hk]
    have := sum_eigenvalues_eq_sum_rq hA hN (hB.eigenvectorBasis hN)
    convert this using 2 <;> simp
  have hβ : ∀ i j, i ≤ j → j < N → extZero (fun i => hB.eigenvalues hN i) j ≤
      extZero (fun i => hB.eigenvalues hN i) i := by
    intro i j hij hj
    have hi : i < N := lt_of_le_of_lt hij hj
    simp only [extZero, hi, hj, dite_true]
    exact hB.eigenvalues_antitone hN (Fin.mk_le_mk.mpr hij)
  have := abel_nonneg (extZero (fun i => hB.eigenvalues hN i))
    (fun j => extZero (fun i => hA.eigenvalues hN i) j - extZero r j) N hβ hD hD0
  simp only [mul_sub, Finset.sum_sub_distrib] at this
  have e1 : ∀ g : Fin N → ℝ, ∑ j ∈ Finset.range N, extZero (fun i => hB.eigenvalues hN i) j * extZero g j =
      ∑ i, hB.eigenvalues hN i * g i := by
    intro g
    rw [← Fin.sum_univ_eq_sum_range (fun j => extZero (fun i => hB.eigenvalues hN i) j * extZero g j) N]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [extZero, j.isLt]
  rw [e1, e1] at this
  linarith

include hA hB in
/-- **Hoffman–Wielandt inequality.**  `Σ_j (μ_j(A) - μ_j(B))² ≤ Σ_i μ_i(A - B)²`, the right side being
`‖A - B‖_F²`. -/
theorem hoffman_wielandt :
    ∑ j, (hA.eigenvalues hN j - hB.eigenvalues hN j) ^ 2 ≤ ∑ i, (hA.sub hB).eigenvalues hN i ^ 2 := by
  set b := hB.eigenvectorBasis hN with hb
  have h1 := sum_sq_eigenvalues_eq (hA.sub hB) hN b
  have h2 := sum_sq_eigenvalues_eq hA hN b
  have h3 := sum_mul_rq_le hA hB hN
  have h4 : ∀ j, ‖(A - B) (b j)‖ ^ 2 = ‖A (b j)‖ ^ 2 - 2 * (hB.eigenvalues hN j * rq A (b j)) +
      hB.eigenvalues hN j ^ 2 := by
    intro j
    have e : (A - B) (b j) = A (b j) - ((hB.eigenvalues hN j : ℝ) : 𝕜) • b j := by
      rw [LinearMap.sub_apply, hb, hB.apply_eigenvectorBasis hN j]
    rw [e, norm_sub_sq (𝕜 := 𝕜), inner_smul_right, norm_smul]
    have hinner : RCLike.re (((hB.eigenvalues hN j : ℝ) : 𝕜) * inner 𝕜 (A (b j)) (b j)) =
        hB.eigenvalues hN j * rq A (b j) := by
      rw [RCLike.re_ofReal_mul, rq, ← hA (b j) (b j)]
    rw [hinner]
    simp [hb, (hB.eigenvectorBasis hN).orthonormal.1 j]
  have h5 : ∑ i, (hA.sub hB).eigenvalues hN i ^ 2 =
      ∑ j, ‖A (b j)‖ ^ 2 - 2 * ∑ j, hB.eigenvalues hN j * rq A (b j) + ∑ j, hB.eigenvalues hN j ^ 2 := by
    rw [h1]
    simp_rw [h4]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h5, ← h2]
  have : ∑ j, (hA.eigenvalues hN j - hB.eigenvalues hN j) ^ 2 =
      ∑ j, hA.eigenvalues hN j ^ 2 - 2 * ∑ j, hB.eigenvalues hN j * hA.eigenvalues hN j +
      ∑ j, hB.eigenvalues hN j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  linarith

end VonNeumann

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.abel_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.abel_nonneg

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.sum_sq_eigenvalues_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.sum_sq_eigenvalues_eq

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.sum_mul_rq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.sum_mul_rq_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.hoffman_wielandt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.hoffman_wielandt

end FormalResearch.MatrixAnalysis.Spectral
