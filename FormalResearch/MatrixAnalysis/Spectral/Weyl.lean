module

public import FormalResearch.MatrixAnalysis.Spectral.MinMax

/-!
# Weyl's inequalities, perturbation bounds and Cauchy interlacing (abstract layer)

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

All statements are for symmetric operators `S, T` on a finite-dimensional inner product space `E` over
`ℝ` or `ℂ` of dimension `N`, with Mathlib's descending eigenvalue lists `μ_k(T) = hT.eigenvalues hN k`
(zero-indexed: `μ_0 ≥ ⋯ ≥ μ_{N-1}`); the matrix versions are in `Spectral.WeylMatrix`.
Every proof is a dimension-counting argument on the Courant–Fischer certificates of `Spectral.MinMax`.

* `eigenvalue_mono`: `rq S ≤ rq T` pointwise implies `μ_k(S) ≤ μ_k(T)`.
* `eigenvalue_add_scalar`: `μ_k(T + c) = μ_k(T) + c`.
* `weyl_add_le`: `μ_{i+j}(S+T) ≤ μ_i(S) + μ_j(T)`;  `weyl_le_add`: `μ_i(S) + μ_j(T) ≤ μ_k(S+T)` for
  `i + j + 1 = k + N` (Weyl 1912; Horn–Johnson Thm 4.3.1).
* `abs_eigenvalue_sub_le`: `‖(S-T)x‖ ≤ ε‖x‖` for all `x` implies `|μ_k(S) - μ_k(T)| ≤ ε`
  (Weyl's perturbation theorem, Bhatia Cor III.2.6).
* `interlace_le`, `interlace_ge`: Cauchy interlacing `μ_{k+N-m}(T) ≤ μ_k(T') ≤ μ_k(T)` for a compression
  `T'` of `T` to an `m`-dimensional space along an isometry `J`.
* `eigenvalue_le_add_finiteRank`, `add_finiteRank_le_eigenvalue`: for `P ⪰ 0` of rank `≤ r`,
  `μ_k(S) ≤ μ_k(S+P)` and `μ_{l+r}(S+P) ≤ μ_l(S)`; `interlace_rankOne` is `r = 1`.

Not formalised here: the multiplicative (Horn) inequalities, the Weyl inequality for non-Hermitian
matrices, and the infinite-dimensional (compact operator) forms.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module

section Mono

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {S T : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric) {N : ℕ}
  (hN : finrank 𝕜 E = N)

/-- The scalar operator `c • id` for a real `c`. -/
noncomputable def scalar (c : ℝ) : E →ₗ[𝕜] E := (c : 𝕜) • LinearMap.id

omit [FiniteDimensional 𝕜 E] in
theorem isSymmetric_scalar (c : ℝ) : (scalar (𝕜 := 𝕜) (E := E) c).IsSymmetric := by
  intro x y
  simp [scalar, inner_smul_left, inner_smul_right]

omit [FiniteDimensional 𝕜 E] in
theorem rq_scalar (c : ℝ) (x : E) : rq (scalar (𝕜 := 𝕜) (E := E) c) x = c * ‖x‖ ^ 2 :=
  rq_smul_id c x

include hS hT in
/-- Monotonicity: `rq S ≤ rq T` pointwise implies `μ_k(S) ≤ μ_k(T)`. -/
theorem eigenvalue_mono (h : ∀ x, rq S x ≤ rq T x) (k : Fin N) :
    hS.eigenvalues hN k ≤ hT.eigenvalues hN k := by
  refine eigenvalue_le_of_subspace hS hN k (W := botSpan hT hN k) (by rw [finrank_botSpan hT hN]) ?_
  intro x hx
  exact (h x).trans (rq_le_eigenvalue_mul_botSpan hT hN k hx)

include hT in
/-- Shifting by a scalar shifts every eigenvalue. -/
theorem eigenvalue_add_scalar (c : ℝ) (k : Fin N) :
    (hT.add (isSymmetric_scalar (𝕜 := 𝕜) (E := E) c)).eigenvalues hN k = hT.eigenvalues hN k + c := by
  apply le_antisymm
  · refine eigenvalue_le_of_subspace (hT.add (isSymmetric_scalar (𝕜 := 𝕜) (E := E) c)) hN k
      (W := botSpan hT hN k) (by rw [finrank_botSpan hT hN]) ?_
    intro x hx
    rw [rq_add, rq_scalar]
    nlinarith [rq_le_eigenvalue_mul_botSpan hT hN k hx]
  · have := le_eigenvalue_of_subspace (hT.add (isSymmetric_scalar (𝕜 := 𝕜) (E := E) c)) hN k
      (V := topSpan hT hN k) (c := hT.eigenvalues hN k + c) (by rw [finrank_topSpan hT hN]) ?_
    · exact this
    · intro x hx
      rw [rq_add, rq_scalar]
      nlinarith [eigenvalue_mul_le_rq_topSpan hT hN k hx]

end Mono

section Weyl

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {S T : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric) {N : ℕ}
  (hN : finrank 𝕜 E = N)

include hS hT in
/-- **Weyl's inequality (upper form).**  `μ_{i+j}(S+T) ≤ μ_i(S) + μ_j(T)` when `i + j = k`. -/
theorem weyl_add_le (i j k : Fin N) (hk : (k : ℕ) = i + j) :
    (hS.add hT).eigenvalues hN k ≤ hS.eigenvalues hN i + hT.eigenvalues hN j := by
  have hi := i.isLt
  have hj := j.isLt
  refine eigenvalue_le_of_subspace (hS.add hT) hN k (W := botSpan hS hN i ⊓ botSpan hT hN j) ?_ ?_
  · have := finrank_add_le_finrank_inf (botSpan hS hN i) (botSpan hT hN j)
    rw [finrank_botSpan hS hN, finrank_botSpan hT hN, hN] at this
    omega
  · rintro x ⟨hxS, hxT⟩
    rw [rq_add]
    nlinarith [rq_le_eigenvalue_mul_botSpan hS hN i hxS, rq_le_eigenvalue_mul_botSpan hT hN j hxT]

include hS hT in
/-- **Weyl's inequality (lower form).**  `μ_i(S) + μ_j(T) ≤ μ_k(S+T)` when `i + j + 1 = k + N`. -/
theorem weyl_le_add (i j k : Fin N) (hk : (i : ℕ) + j + 1 = k + N) :
    hS.eigenvalues hN i + hT.eigenvalues hN j ≤ (hS.add hT).eigenvalues hN k := by
  refine le_eigenvalue_of_subspace (hS.add hT) hN k (V := topSpan hS hN i ⊓ topSpan hT hN j) ?_ ?_
  · have := finrank_add_le_finrank_inf (topSpan hS hN i) (topSpan hT hN j)
    rw [finrank_topSpan hS hN, finrank_topSpan hT hN, hN] at this
    omega
  · rintro x ⟨hxS, hxT⟩
    rw [rq_add]
    nlinarith [eigenvalue_mul_le_rq_topSpan hS hN i hxS, eigenvalue_mul_le_rq_topSpan hT hN j hxT]

include hS hT in
/-- **Weyl's perturbation theorem.**  If `‖(S-T) x‖ ≤ ε ‖x‖` for all `x` (e.g. `ε` the operator norm of
`S - T`) then `|μ_k(S) - μ_k(T)| ≤ ε`. -/
theorem abs_eigenvalue_sub_le {ε : ℝ} (h : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin N) :
    |hS.eigenvalues hN k - hT.eigenvalues hN k| ≤ ε := by
  have hrq : ∀ x, |rq (S - T) x| ≤ ε * ‖x‖ ^ 2 := by
    intro x
    calc |rq (S - T) x| ≤ ‖inner 𝕜 x ((S - T) x)‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖x‖ * ‖(S - T) x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (ε * ‖x‖) := by gcongr; exact h x
      _ = ε * ‖x‖ ^ 2 := by ring
  have key : ∀ (S T : E →ₗ[𝕜] E) (hS : S.IsSymmetric) (hT : T.IsSymmetric),
      (∀ x, rq S x - rq T x ≤ ε * ‖x‖ ^ 2) →
      hS.eigenvalues hN k ≤ hT.eigenvalues hN k + ε := by
    intro S T hS hT hle
    rw [← eigenvalue_add_scalar hT hN ε k]
    refine eigenvalue_mono hS (hT.add (isSymmetric_scalar ε)) hN (fun x => ?_) k
    rw [rq_add, rq_scalar]
    linarith [hle x]
  have h1 := key S T hS hT (fun x => by simpa [rq_sub] using (abs_le.mp (hrq x)).2)
  have h2 := key T S hT hS (fun x => by
    have := (abs_le.mp (hrq x)).1
    rw [rq_sub] at this
    linarith)
  rw [abs_le]
  constructor <;> linarith

end Weyl

section Interlace

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {N : ℕ} (hN : finrank 𝕜 E = N)
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {T' : F →ₗ[𝕜] F} (hT' : T'.IsSymmetric) {m : ℕ} (hm : finrank 𝕜 F = m)
  (J : F →ₗᵢ[𝕜] E) (hcomp : ∀ y, inner 𝕜 y (T' y) = inner 𝕜 (J y) (T (J y)))

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
include hcomp in
theorem rq_comp_eq (y : F) : rq T' y = rq T (J y) := by
  simp only [rq, hcomp y]

include hT hT' hcomp in
/-- **Cauchy interlacing, upper half.**  A compression has smaller eigenvalues: `μ_k(T') ≤ μ_k(T)`. -/
theorem interlace_le (k : Fin m) (hkN : (k : ℕ) < N) :
    hT'.eigenvalues hm k ≤ hT.eigenvalues hN ⟨k, hkN⟩ := by
  refine le_eigenvalue_of_subspace hT hN ⟨k, hkN⟩
    (V := (topSpan hT' hm k).map J.toLinearMap) ?_ ?_
  · rw [← (Submodule.equivMapOfInjective J.toLinearMap J.injective _).finrank_eq,
      finrank_topSpan hT' hm k]
  · rintro _ ⟨y, hy, rfl⟩
    have := eigenvalue_mul_le_rq_topSpan hT' hm k hy
    rw [rq_comp_eq J hcomp] at this
    simpa using this

include hT hT' hcomp in
/-- **Cauchy interlacing, lower half.**  `μ_{k+N-m}(T) ≤ μ_k(T')`. -/
theorem interlace_ge (k : Fin m) (k' : Fin N) (hk' : (k' : ℕ) + m = k + N) :
    hT.eigenvalues hN k' ≤ hT'.eigenvalues hm k := by
  have hmN : m ≤ N := by
    have := Submodule.finrank_le (LinearMap.range J.toLinearMap)
    rwa [LinearMap.finrank_range_of_inj J.injective, hm, hN] at this
  refine le_eigenvalue_of_subspace hT' hm k
    (V := (topSpan hT hN k').comap J.toLinearMap) ?_ ?_
  · rw [(Submodule.equivMapOfInjective J.toLinearMap J.injective
      ((topSpan hT hN k').comap J.toLinearMap)).finrank_eq, Submodule.map_comap_eq]
    have := finrank_add_le_finrank_inf (LinearMap.range J.toLinearMap) (topSpan hT hN k')
    rw [LinearMap.finrank_range_of_inj J.injective, finrank_topSpan hT hN, hm, hN] at this
    omega
  · intro y hy
    have := eigenvalue_mul_le_rq_topSpan hT hN k' hy
    have h2 : rq T (J y) = rq T' y := (rq_comp_eq J hcomp y).symm
    simp only [LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map] at this
    rwa [h2] at this

section FiniteRank

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {S P : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (hP : P.IsSymmetric) {N : ℕ}
  (hN : finrank 𝕜 E = N)

include hS hP in
/-- **Finite-rank interlacing, lower half.**  If `P ⪰ 0` then `μ_k(S) ≤ μ_k(S+P)`. -/
theorem eigenvalue_le_add_finiteRank (hpos : ∀ x, 0 ≤ rq P x) (k : Fin N) :
    hS.eigenvalues hN k ≤ (hS.add hP).eigenvalues hN k :=
  eigenvalue_mono hS (hS.add hP) hN (fun x => by rw [rq_add]; linarith [hpos x]) k

include hS hP in
/-- **Finite-rank interlacing, upper half.**  If `Re⟪x, P x⟫ ≤ 0` on a subspace of dimension `≥ N - r`
(e.g. `P ⪰ 0` of rank `≤ r`) then `μ_{l+r}(S+P) ≤ μ_l(S)`.  (The hypothesis `P ⪰ 0` is not used here;
`P` need only be symmetric.) -/
theorem add_finiteRank_le_eigenvalue {W : Submodule 𝕜 E} {r : ℕ} (hW : N - r ≤ finrank 𝕜 W)
    (h0 : ∀ x ∈ W, rq P x ≤ 0) (l r' k : Fin N) (hr : (r' : ℕ) = r) (hk : (k : ℕ) = l + r) :
    (hS.add hP).eigenvalues hN k ≤ hS.eigenvalues hN l := by
  have h1 := weyl_add_le hS hP hN l r' k (by omega)
  have h2 : hP.eigenvalues hN r' ≤ 0 :=
    eigenvalue_le_of_subspace hP hN r' (W := W) (by omega) (fun x hx => by simpa using h0 x hx)
  linarith

/-- The rank-one operator `x ↦ ⟪v, x⟫ v`. -/
noncomputable def rankOne (v : E) : E →ₗ[𝕜] E := ((innerSL 𝕜 v).smulRight v : E →L[𝕜] E)

omit [FiniteDimensional 𝕜 E] in
theorem isSymmetric_rankOne (v : E) : (rankOne (𝕜 := 𝕜) v).IsSymmetric := by
  intro x y
  simp only [rankOne, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_left, inner_smul_right]
  rw [inner_conj_symm, mul_comm]

omit [FiniteDimensional 𝕜 E] in
theorem rq_rankOne (v x : E) : rq (rankOne (𝕜 := 𝕜) v) x = ‖inner 𝕜 v x‖ ^ 2 := by
  simp only [rq, rankOne, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, inner_smul_right]
  rw [← inner_conj_symm v x, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  simp [norm_inner_symm]

include hS in
/-- **Rank-one interlacing.**  `μ_k(S) ≤ μ_k(S + ⟪v,·⟫v) ≤ μ_{k-1}(S)`. -/
theorem interlace_rankOne (v : E) (l k : Fin N) (hk : (k : ℕ) = l + 1) :
    hS.eigenvalues hN k ≤ (hS.add (isSymmetric_rankOne (𝕜 := 𝕜) v)).eigenvalues hN k ∧
    (hS.add (isSymmetric_rankOne (𝕜 := 𝕜) v)).eigenvalues hN k ≤ hS.eigenvalues hN l := by
  have hpos : ∀ x, 0 ≤ rq (rankOne (𝕜 := 𝕜) v) x := fun x => by rw [rq_rankOne]; positivity
  refine ⟨eigenvalue_le_add_finiteRank hS (isSymmetric_rankOne v) hN hpos k, ?_⟩
  refine add_finiteRank_le_eigenvalue hS (isSymmetric_rankOne v) hN
    (W := LinearMap.ker (innerSL 𝕜 v : E →ₗ[𝕜] 𝕜)) (r := 1) ?_ ?_ l ⟨1, by omega⟩ k rfl hk
  · have := LinearMap.finrank_range_add_finrank_ker (innerSL 𝕜 v : E →ₗ[𝕜] 𝕜)
    have h2 : finrank 𝕜 (LinearMap.range (innerSL 𝕜 v : E →ₗ[𝕜] 𝕜)) ≤ 1 := by
      simpa using Submodule.finrank_le (LinearMap.range (innerSL 𝕜 v : E →ₗ[𝕜] 𝕜))
    omega
  · intro x hx
    have : inner 𝕜 v x = 0 := hx
    simp [rq_rankOne, this]

end FiniteRank

end Interlace

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.eigenvalue_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.eigenvalue_mono

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.eigenvalue_add_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.eigenvalue_add_scalar

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.weyl_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.weyl_add_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.weyl_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.weyl_le_add

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.abs_eigenvalue_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.abs_eigenvalue_sub_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.interlace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.interlace_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.interlace_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.interlace_ge

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.interlace_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.interlace_rankOne

end FormalResearch.MatrixAnalysis.Spectral
