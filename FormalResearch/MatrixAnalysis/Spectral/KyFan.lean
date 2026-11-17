module

public import FormalResearch.MatrixAnalysis.Spectral.Weyl

/-!
# Ky Fan's maximum principle and subadditivity of partial eigenvalue sums (abstract layer)

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

For a symmetric operator `T` on an `N`-dimensional inner product space `E` over `ℝ` or `ℂ` with descending
eigenvalues `μ_0 ≥ ⋯ ≥ μ_{N-1}` and `k ≤ N`, write `Σ_{i<k} μ_i` for the sum of the `k` largest ones.

* `sum_eigenvalues_eq_sum_rq`: `Σ_i μ_i = Σ_j Re⟪u_j, T u_j⟫` for any orthonormal basis `u` (trace).
* `weighted_sum_le`: the Ky Fan weight lemma: `Σ μ_i w_i ≤ Σ_{i<k} μ_i` for `μ` antitone,
  `0 ≤ w_i ≤ 1`, `Σ w_i = k`.
* `kyFan_le`: `Σ_{j<k} Re⟪u_j, T u_j⟫ ≤ Σ_{i<k} μ_i` for every orthonormal family `u` of `k` vectors.
* `kyFan_isGreatest`: **Ky Fan maximum principle**, `Σ_{i<k} μ_i = max_u Σ_j Re⟪u_j, T u_j⟫`, attained at the
  first `k` eigenvectors.
* `partial_sum_add_le`: subadditivity `Σ_{i<k} μ_i(S+T) ≤ Σ_{i<k} μ_i(S) + Σ_{i<k} μ_i(T)`.

Source: Ky Fan 1949; Bhatia, *Matrix Analysis*, Prop. III.5.1 / Cor. III.2.4.  Not formalised here: the
trace-of-projection phrasing `Σ_{i<k} μ_i = max tr(PT)` (see `Spectral.WeylMatrix` for matrices).
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module

theorem sum_castLE_eq_sum_filter {N k : ℕ} (hk : k ≤ N) (g : Fin N → ℝ) :
    ∑ j : Fin k, g (Fin.castLE hk j) = ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), g i := by
  refine (Finset.sum_map Finset.univ (Fin.castLEEmb hk) g).symm.trans ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro h
    exact ⟨⟨i, h⟩, rfl⟩

/-- Number of `i : Fin N` with `i < k` is `k` when `k ≤ N`. -/
theorem card_filter_lt_fin {N k : ℕ} (hk : k ≤ N) :
    (Finset.univ.filter fun i : Fin N => (i : ℕ) < k).card = k := by
  have := sum_castLE_eq_sum_filter hk (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
  exact_mod_cast this.symm

/-- **Ky Fan weight lemma.** -/
theorem weighted_sum_le {N k : ℕ} (μ : Fin N → ℝ) (hμ : Antitone μ) (w : Fin N → ℝ)
    (h0 : ∀ i, 0 ≤ w i) (h1 : ∀ i, w i ≤ 1) (hs : ∑ i, w i = k) :
    ∑ i, μ i * w i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), μ i := by
  have hkN : k ≤ N := by
    have : ∑ i, w i ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
    rw [hs] at this
    simp at this
    exact_mod_cast this
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, (∀ i : Fin N, (i : ℕ) < k → c ≤ μ i) ∧
      (∀ i : Fin N, k ≤ (i : ℕ) → μ i ≤ c) := by
    by_cases hk : k < N
    · exact ⟨μ ⟨k, hk⟩, fun i hi => hμ (Fin.le_def.mpr hi.le), fun i hi => hμ (show (⟨k, hk⟩ : Fin N) ≤ i from hi)⟩
    · by_cases hN : 0 < N
      · exact ⟨μ ⟨N - 1, by omega⟩, fun i _ => hμ (by simp [Fin.le_def]; omega),
          fun i hi => absurd i.isLt (by omega)⟩
      · exact ⟨0, fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega)⟩
  have hind : ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), μ i =
      ∑ i, μ i * (if (i : ℕ) < k then 1 else 0) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hcard : ∑ i : Fin N, (if (i : ℕ) < k then (1 : ℝ) else 0) = k := by
    rw [← Finset.sum_filter]
    simp [card_filter_lt_fin hkN]
  rw [hind, ← sub_nonneg, ← Finset.sum_sub_distrib]
  have hterm : ∀ i : Fin N, c * ((if (i : ℕ) < k then 1 else 0) - w i) ≤
      μ i * (if (i : ℕ) < k then 1 else 0) - μ i * w i := by
    intro i
    by_cases hik : (i : ℕ) < k
    · simp only [hik, ite_true]
      nlinarith [hc1 i hik, h1 i]
    · simp only [hik, ite_false]
      nlinarith [hc2 i (not_lt.mp hik), h0 i]
  calc (0 : ℝ) = c * (∑ i : Fin N, (if (i : ℕ) < k then (1 : ℝ) else 0) - ∑ i, w i) := by
        rw [hcard, hs]; ring
    _ = ∑ i : Fin N, c * ((if (i : ℕ) < k then 1 else 0) - w i) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i


section Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {N : ℕ} (hN : finrank 𝕜 E = N)

include hT in
/-- The trace of a symmetric operator is the sum of its eigenvalues, computed in any orthonormal basis. -/
theorem sum_eigenvalues_eq_sum_rq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, hT.eigenvalues hN i = ∑ j, rq T (b j) := by
  simp_rw [rq_eq_sum hT hN (E := E)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  have h := b.sum_sq_norm_inner_left (hT.eigenvectorBasis hN i)
  rw [h, (hT.eigenvectorBasis hN).orthonormal.1 i]
  simp

include hT in
theorem rq_eigenvectorBasis (i : Fin N) : rq T (hT.eigenvectorBasis hN i) = hT.eigenvalues hN i := by
  rw [rq, hT.apply_eigenvectorBasis hN i, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (hT.eigenvectorBasis hN).orthonormal.1 i]
  simp

include hT in
/-- **Ky Fan inequality.**  For an orthonormal family `u` of `k` vectors,
`Σ_j Re⟪u_j, T u_j⟫ ≤ Σ_{i<k} μ_i`. -/
theorem kyFan_le {ι : Type*} [Fintype ι] {u : ι → E} (hu : Orthonormal 𝕜 u) :
    ∑ j, rq T (u j) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < Fintype.card ι), hT.eigenvalues hN i := by
  set w : Fin N → ℝ := fun i => ∑ j, ‖inner 𝕜 (u j) (hT.eigenvectorBasis hN i)‖ ^ 2 with hw
  have hrq : ∑ j, rq T (u j) = ∑ i, hT.eigenvalues hN i * w i := by
    simp_rw [rq_eq_sum hT hN (E := E)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_inner_symm]
  rw [hrq]
  refine weighted_sum_le _ (hT.eigenvalues_antitone hN) w (fun i => by positivity) (fun i => ?_) ?_
  · have := hu.sum_inner_products_le (s := Finset.univ) (x := hT.eigenvectorBasis hN i)
    simpa using this
  · rw [hw]
    simp only
    rw [Finset.sum_comm]
    have : ∀ j, ∑ i, ‖inner 𝕜 (u j) (hT.eigenvectorBasis hN i)‖ ^ 2 = 1 := by
      intro j
      rw [(hT.eigenvectorBasis hN).sum_sq_norm_inner_left, hu.1 j]
      simp
    simp [this]

include hT in
/-- The first `k` eigenvectors attain the Ky Fan sum. -/
theorem kyFan_attained {k : ℕ} (hk : k ≤ N) :
    Orthonormal 𝕜 (fun j : Fin k => hT.eigenvectorBasis hN (Fin.castLE hk j)) ∧
    ∑ j : Fin k, rq T (hT.eigenvectorBasis hN (Fin.castLE hk j)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), hT.eigenvalues hN i := by
  refine ⟨(hT.eigenvectorBasis hN).orthonormal.comp _ (Fin.castLE_injective hk), ?_⟩
  simp_rw [rq_eigenvectorBasis hT hN]
  exact sum_castLE_eq_sum_filter hk (fun i => hT.eigenvalues hN i)

include hT in
/-- **Ky Fan maximum principle.**  For `k ≤ N`, the sum of the `k` largest eigenvalues is the maximum of
`Σ_{j<k} Re⟪u_j, T u_j⟫` over orthonormal `k`-frames `u`; it is attained at the first `k` eigenvectors. -/
theorem kyFan_isGreatest {k : ℕ} (hk : k ≤ N) :
    IsGreatest {s : ℝ | ∃ u : Fin k → E, Orthonormal 𝕜 u ∧ s = ∑ j, rq T (u j)}
      (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), hT.eigenvalues hN i) := by
  refine ⟨⟨_, (kyFan_attained hT hN hk).1, (kyFan_attained hT hN hk).2.symm⟩, ?_⟩
  rintro s ⟨u, hu, rfl⟩
  simpa using kyFan_le hT hN hu

end Spectral

section Subadditive

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {S T : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric) {N : ℕ}
  (hN : finrank 𝕜 E = N)

include hS hT in
/-- **Subadditivity of Ky Fan sums.**  `Σ_{i<k} μ_i(S+T) ≤ Σ_{i<k} μ_i(S) + Σ_{i<k} μ_i(T)` for `k ≤ N`;
the case `k = 1` is subadditivity of the largest eigenvalue. -/
theorem partial_sum_add_le {k : ℕ} (hk : k ≤ N) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), (hS.add hT).eigenvalues hN i ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), hS.eigenvalues hN i +
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), hT.eigenvalues hN i := by
  obtain ⟨hu, hsum⟩ := kyFan_attained (hS.add hT) hN hk
  rw [← hsum]
  simp_rw [rq_add, Finset.sum_add_distrib]
  have h1 := kyFan_le hS hN hu
  have h2 := kyFan_le hT hN hu
  simp only [Fintype.card_fin] at h1 h2
  linarith

end Subadditive

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.weighted_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.weighted_sum_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.sum_eigenvalues_eq_sum_rq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.sum_eigenvalues_eq_sum_rq

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.kyFan_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.kyFan_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.kyFan_isGreatest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.kyFan_isGreatest

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.partial_sum_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.partial_sum_add_le

end FormalResearch.MatrixAnalysis.Spectral
