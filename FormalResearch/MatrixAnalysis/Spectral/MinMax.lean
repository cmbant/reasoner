module

public import Mathlib

/-!
# Courant–Fischer min–max principle for symmetric operators (abstract layer)

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

Let `E` be a finite-dimensional inner product space over `𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`), `T : E →ₗ[𝕜] E`
symmetric, `N = dim E` and `μ_0 ≥ μ_1 ≥ ⋯ ≥ μ_{N-1}` the eigenvalues `hT.eigenvalues hN` (Mathlib's sorted
list; for a Hermitian matrix this is `Matrix.IsHermitian.eigenvalues₀`, see `Spectral.WeylMatrix`).
Write `rq T x = Re ⟪x, T x⟫` for the Rayleigh form.

* `rq_eq_sum`: `rq T x = ∑ i, μ_i ‖⟪b_i, x⟫‖²` (`b` the eigenvector basis).
* `topSpan`, `botSpan`: `span{b_0..b_k}` (dimension `k+1`, `μ_k ‖x‖² ≤ rq T x`) and `span{b_k..b_{N-1}}`
  (dimension `N-k`, `rq T x ≤ μ_k ‖x‖²`).
* `le_eigenvalue_of_subspace`, `eigenvalue_le_of_subspace`: one-sided certificates (dimension counting).
* `courant_fischer_maxmin`, `courant_fischer_minmax`: `μ_k` is the greatest (resp. least) constant `c` for which
  there is a subspace of dimension `k+1` on which `c‖x‖² ≤ rq` (resp. of dimension `N-k` on which `rq ≤ c‖x‖²`);
  the attaining subspaces are `topSpan`, `botSpan`.

Source: Courant–Fischer min–max theorem (Horn–Johnson, *Matrix Analysis*, Thm 4.2.6; Bhatia, *Matrix
Analysis*, Thm III.1.1).  Not in Mathlib at the pinned revision (only the extremal eigenvalue
`hasEigenvalue_iSup_of_finiteDimensional`).  The proof is the dimension-counting argument (no compactness).
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module

section Basic

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Rayleigh form `x ↦ Re ⟪x, T x⟫` of an operator. -/
noncomputable def rq (T : E →ₗ[𝕜] E) (x : E) : ℝ := RCLike.re (inner 𝕜 x (T x))

theorem rq_add (S T : E →ₗ[𝕜] E) (x : E) : rq (S + T) x = rq S x + rq T x := by
  simp [rq, inner_add_right]

theorem rq_sub (S T : E →ₗ[𝕜] E) (x : E) : rq (S - T) x = rq S x - rq T x := by
  simp [rq, inner_sub_right]

theorem rq_neg (T : E →ₗ[𝕜] E) (x : E) : rq (-T) x = - rq T x := by
  simp [rq, inner_neg_right]

theorem rq_smul (T : E →ₗ[𝕜] E) (c : 𝕜) (x : E) : rq T (c • x) = ‖c‖ ^ 2 * rq T x := by
  simp only [rq, map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]

theorem rq_smul_id (c : ℝ) (x : E) :
    rq ((c : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E)) x = c * ‖x‖ ^ 2 := by
  simp only [rq, LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

end Basic

section Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {N : ℕ} (hN : finrank 𝕜 E = N)

include hT in
/-- The Rayleigh form in the eigenbasis: `rq T x = ∑ μ_i ‖⟪b_i, x⟫‖²`. -/
theorem rq_eq_sum (x : E) :
    rq T x = ∑ i, hT.eigenvalues hN i * ‖inner 𝕜 (hT.eigenvectorBasis hN i) x‖ ^ 2 := by
  have h := (hT.eigenvectorBasis hN).sum_inner_mul_inner x (T x)
  have h2 : ∀ i, inner 𝕜 (hT.eigenvectorBasis hN i) (T x) =
      (hT.eigenvalues hN i : 𝕜) * inner 𝕜 (hT.eigenvectorBasis hN i) x := by
    intro i
    rw [← hT (hT.eigenvectorBasis hN i) x, hT.apply_eigenvectorBasis hN i, inner_smul_left]
    simp
  unfold rq
  rw [← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i, ← inner_conj_symm x (hT.eigenvectorBasis hN i)]
  have : (starRingEnd 𝕜) (inner 𝕜 (hT.eigenvectorBasis hN i) x) *
      ((hT.eigenvalues hN i : 𝕜) * inner 𝕜 (hT.eigenvectorBasis hN i) x) =
      ((hT.eigenvalues hN i * ‖inner 𝕜 (hT.eigenvectorBasis hN i) x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [mul_left_comm, RCLike.conj_mul]
    push_cast
    ring
  rw [this, RCLike.ofReal_re]

include hT in
theorem norm_sq_eq_sum (x : E) :
    ‖x‖ ^ 2 = ∑ i, ‖inner 𝕜 (hT.eigenvectorBasis hN i) x‖ ^ 2 :=
  ((hT.eigenvectorBasis hN).sum_sq_norm_inner_right x).symm

include hT in
/-- If the coordinates of `x` beyond `k` vanish then `μ_k ‖x‖² ≤ rq T x`. -/
theorem le_rq_of_coord {x : E} (k : Fin N)
    (hx : ∀ i, k < i → inner 𝕜 (hT.eigenvectorBasis hN i) x = 0) :
    hT.eigenvalues hN k * ‖x‖ ^ 2 ≤ rq T x := by
  rw [rq_eq_sum hT hN, norm_sq_eq_sum hT hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_or_gt i k with h | h
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hN h) (by positivity)
  · simp [hx i h]

include hT in
/-- If the coordinates of `x` before `k` vanish then `rq T x ≤ μ_k ‖x‖²`. -/
theorem rq_le_of_coord {x : E} (k : Fin N)
    (hx : ∀ i, i < k → inner 𝕜 (hT.eigenvectorBasis hN i) x = 0) :
    rq T x ≤ hT.eigenvalues hN k * ‖x‖ ^ 2 := by
  rw [rq_eq_sum hT hN, norm_sq_eq_sum hT hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_or_gt k i with h | h
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hN h) (by positivity)
  · simp [hx i h]

/-- The span of the first `k+1` eigenvectors. -/
noncomputable def topSpan (k : Fin N) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (hT.eigenvectorBasis hN '' Set.Iic k)

/-- The span of the eigenvectors `k, …, N-1`. -/
noncomputable def botSpan (k : Fin N) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (hT.eigenvectorBasis hN '' Set.Ici k)

include hT in
theorem finrank_topSpan (k : Fin N) : finrank 𝕜 (topSpan hT hN k) = k + 1 := by
  have hli : LinearIndependent 𝕜 (fun i : Set.Iic k => hT.eigenvectorBasis hN i) :=
    (hT.eigenvectorBasis hN).toBasis.linearIndependent.comp _ Subtype.val_injective
  have := finrank_span_eq_card hli
  unfold topSpan
  rw [Set.image_eq_range]
  simpa [Fintype.card_Iic] using this

include hT in
theorem finrank_botSpan (k : Fin N) : finrank 𝕜 (botSpan hT hN k) = N - k := by
  have hli : LinearIndependent 𝕜 (fun i : Set.Ici k => hT.eigenvectorBasis hN i) :=
    (hT.eigenvectorBasis hN).toBasis.linearIndependent.comp _ Subtype.val_injective
  have := finrank_span_eq_card hli
  unfold botSpan
  rw [Set.image_eq_range]
  simpa [Fintype.card_Ici] using this

include hT in
theorem coord_eq_zero_of_mem_topSpan {k : Fin N} {x : E} (hx : x ∈ topSpan hT hN k) (i : Fin N)
    (hi : k < i) : inner 𝕜 (hT.eigenvectorBasis hN i) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have : i ≠ j := fun h => absurd hj (by rw [Set.mem_Iic, ← h]; exact not_le.mpr hi)
    exact (hT.eigenvectorBasis hN).orthonormal.inner_eq_zero this
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul a y _ hy => rw [inner_smul_right, hy, mul_zero]

include hT in
theorem coord_eq_zero_of_mem_botSpan {k : Fin N} {x : E} (hx : x ∈ botSpan hT hN k) (i : Fin N)
    (hi : i < k) : inner 𝕜 (hT.eigenvectorBasis hN i) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have : i ≠ j := fun h => absurd hj (by rw [Set.mem_Ici, ← h]; exact not_le.mpr hi)
    exact (hT.eigenvectorBasis hN).orthonormal.inner_eq_zero this
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul a y _ hy => rw [inner_smul_right, hy, mul_zero]

include hT in
theorem eigenvalue_mul_le_rq_topSpan (k : Fin N) {x : E} (hx : x ∈ topSpan hT hN k) :
    hT.eigenvalues hN k * ‖x‖ ^ 2 ≤ rq T x :=
  le_rq_of_coord hT hN k (coord_eq_zero_of_mem_topSpan hT hN hx)

include hT in
theorem rq_le_eigenvalue_mul_botSpan (k : Fin N) {x : E} (hx : x ∈ botSpan hT hN k) :
    rq T x ≤ hT.eigenvalues hN k * ‖x‖ ^ 2 :=
  rq_le_of_coord hT hN k (coord_eq_zero_of_mem_botSpan hT hN hx)

end Spectral

section Counting

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Dimension counting: `dim U + dim V ≤ dim E + dim (U ∩ V)`. -/
theorem finrank_add_le_finrank_inf (U V : Submodule 𝕜 E) :
    finrank 𝕜 U + finrank 𝕜 V ≤ finrank 𝕜 E + finrank 𝕜 ↥(U ⊓ V) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U V
  have h2 : finrank 𝕜 ↥(U ⊔ V) ≤ finrank 𝕜 E := Submodule.finrank_le _
  omega

/-- A nonzero vector in the intersection of two subspaces whose dimensions add up to more than `dim E`. -/
theorem exists_ne_zero_mem_inf {U V : Submodule 𝕜 E} (h : finrank 𝕜 E < finrank 𝕜 U + finrank 𝕜 V) :
    ∃ x ∈ U ⊓ V, x ≠ 0 := by
  have h1 := finrank_add_le_finrank_inf U V
  have h2 : 0 < finrank 𝕜 ↥(U ⊓ V) := by omega
  have h3 : U ⊓ V ≠ ⊥ := fun hb => by
    rw [hb] at h2
    simp at h2
  exact (Submodule.ne_bot_iff _).mp h3

end Counting

section Certificates

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {N : ℕ} (hN : finrank 𝕜 E = N)

include hT in
/-- **Lower certificate.**  If some subspace of dimension `≥ k+1` has `c ‖x‖² ≤ rq T x` on it, then
`c ≤ μ_k`. -/
theorem le_eigenvalue_of_subspace {V : Submodule 𝕜 E} {c : ℝ} (k : Fin N)
    (hV : (k : ℕ) + 1 ≤ finrank 𝕜 V) (h : ∀ x ∈ V, c * ‖x‖ ^ 2 ≤ rq T x) :
    c ≤ hT.eigenvalues hN k := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hk := k.isLt
  obtain ⟨x, ⟨hxV, hxW⟩, hx0⟩ := exists_ne_zero_mem_inf (U := V) (V := botSpan hT hN k)
    (by rw [finrank_botSpan hT hN]; omega)
  have h1 := h x hxV
  have h2 := rq_le_eigenvalue_mul_botSpan hT hN k hxW
  have h3 : 0 < ‖x‖ ^ 2 := by positivity
  nlinarith

include hT in
/-- **Upper certificate.**  If some subspace of dimension `≥ N-k` has `rq T x ≤ c ‖x‖²` on it, then
`μ_k ≤ c`. -/
theorem eigenvalue_le_of_subspace {W : Submodule 𝕜 E} {c : ℝ} (k : Fin N)
    (hW : N - (k : ℕ) ≤ finrank 𝕜 W) (h : ∀ x ∈ W, rq T x ≤ c * ‖x‖ ^ 2) :
    hT.eigenvalues hN k ≤ c := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hk := k.isLt
  obtain ⟨x, ⟨hxV, hxW⟩, hx0⟩ := exists_ne_zero_mem_inf (U := topSpan hT hN k) (V := W)
    (by rw [finrank_topSpan hT hN]; omega)
  have h1 := h x hxW
  have h2 := eigenvalue_mul_le_rq_topSpan hT hN k hxV
  have h3 : 0 < ‖x‖ ^ 2 := by positivity
  nlinarith

include hT in
/-- **Courant–Fischer, max–min form.**  `μ_k` is the greatest constant `c` such that some
`(k+1)`-dimensional subspace `V` satisfies `c ‖x‖² ≤ Re ⟪x, T x⟫` for all `x ∈ V`; it is attained at
`V = span{b_0, …, b_k}`. -/
theorem courant_fischer_maxmin (k : Fin N) :
    IsGreatest {c : ℝ | ∃ V : Submodule 𝕜 E, finrank 𝕜 V = k + 1 ∧
      ∀ x ∈ V, c * ‖x‖ ^ 2 ≤ rq T x} (hT.eigenvalues hN k) := by
  refine ⟨⟨topSpan hT hN k, finrank_topSpan hT hN k, fun x hx =>
    eigenvalue_mul_le_rq_topSpan hT hN k hx⟩, ?_⟩
  rintro c ⟨V, hV, h⟩
  exact le_eigenvalue_of_subspace hT hN k hV.ge h

include hT in
/-- **Courant–Fischer, min–max form.**  `μ_k` is the least constant `c` such that some subspace `W` of
dimension `N-k` satisfies `Re ⟪x, T x⟫ ≤ c ‖x‖²` for all `x ∈ W`; it is attained at
`W = span{b_k, …, b_{N-1}}`. -/
theorem courant_fischer_minmax (k : Fin N) :
    IsLeast {c : ℝ | ∃ W : Submodule 𝕜 E, finrank 𝕜 W = N - k ∧
      ∀ x ∈ W, rq T x ≤ c * ‖x‖ ^ 2} (hT.eigenvalues hN k) := by
  refine ⟨⟨botSpan hT hN k, finrank_botSpan hT hN k, fun x hx =>
    rq_le_eigenvalue_mul_botSpan hT hN k hx⟩, ?_⟩
  rintro c ⟨W, hW, h⟩
  exact eigenvalue_le_of_subspace hT hN k hW.ge h

include hT in
theorem eigenvalues_last_mul_le_rq (hN0 : 0 < N) (x : E) :
    hT.eigenvalues hN ⟨N - 1, by omega⟩ * ‖x‖ ^ 2 ≤ rq T x :=
  le_rq_of_coord hT hN _ fun i hi => absurd i.isLt (by have := hi; simp [Fin.lt_def] at this; omega)

include hT in
theorem rq_le_eigenvalues_zero_mul (hN0 : 0 < N) (x : E) :
    rq T x ≤ hT.eigenvalues hN ⟨0, hN0⟩ * ‖x‖ ^ 2 :=
  rq_le_of_coord hT hN _ fun i hi => absurd hi (by simp [Fin.lt_def])

include hT in
/-- **Courant–Fischer, literal max–min.**  `μ_k = max_{dim V = k+1} min_{x ∈ V, ‖x‖ = 1} Re⟪x, T x⟫`. -/
theorem courant_fischer_maxmin_iSup (k : Fin N) :
    hT.eigenvalues hN k = ⨆ V : {V : Submodule 𝕜 E // finrank 𝕜 V = k + 1},
      ⨅ x : {x : E // x ∈ V.1 ∧ ‖x‖ = 1}, rq T x.1 := by
  have hN0 : 0 < N := by have := k.isLt; omega
  have hbdd : ∀ V : Submodule 𝕜 E, BddBelow (Set.range fun x : {x : E // x ∈ V ∧ ‖x‖ = 1} => rq T x.1) :=
    fun V => ⟨hT.eigenvalues hN ⟨N - 1, by omega⟩, by
      rintro _ ⟨x, rfl⟩
      simpa [x.2.2] using eigenvalues_last_mul_le_rq hT hN hN0 x.1⟩
  have hne : ∀ V : {V : Submodule 𝕜 E // finrank 𝕜 V = k + 1},
      Nonempty {x : E // x ∈ V.1 ∧ ‖x‖ = 1} := by
    intro V
    have : 0 < finrank 𝕜 V.1 := by rw [V.2]; omega
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff V.1).mp (fun h => by
      have := V.2; rw [h] at this; simp at this)
    refine ⟨⟨(‖x‖⁻¹ : 𝕜) • x, V.1.smul_mem _ hx, ?_⟩⟩
    rw [norm_smul, norm_inv, RCLike.norm_coe_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
  have hiff : ∀ (V : {V : Submodule 𝕜 E // finrank 𝕜 V = k + 1}) (c : ℝ),
      c ≤ ⨅ x : {x : E // x ∈ V.1 ∧ ‖x‖ = 1}, rq T x.1 ↔ ∀ x ∈ V.1, c * ‖x‖ ^ 2 ≤ rq T x := by
    intro V c
    have := hne V
    rw [le_ciInf_iff (hbdd V.1)]
    constructor
    · intro h x hx
      by_cases hx0 : x = 0
      · simp [hx0, rq]
      · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        set y : E := (‖x‖⁻¹ : 𝕜) • x with hy
        have hy1 : ‖y‖ = 1 := by
          rw [hy, norm_smul, norm_inv, RCLike.norm_coe_norm, inv_mul_cancel₀ hn.ne']
        have h1 := h ⟨y, V.1.smul_mem _ hx, hy1⟩
        have h2 : rq T y = (‖x‖ ^ 2)⁻¹ * rq T x := by
          rw [hy, rq_smul]
          simp [inv_pow]
        simp only at h1
        rw [h2] at h1
        have h3 : 0 < ‖x‖ ^ 2 := by positivity
        calc c * ‖x‖ ^ 2 ≤ ((‖x‖ ^ 2)⁻¹ * rq T x) * ‖x‖ ^ 2 := by gcongr
          _ = rq T x := by field_simp
    · intro h x
      simpa [x.2.2] using h x.1 x.2.1
  apply le_antisymm
  · have hk : (k : ℕ) + 1 ≤ N := by have := k.isLt; omega
    let V0 : {V : Submodule 𝕜 E // finrank 𝕜 V = k + 1} := ⟨topSpan hT hN k, finrank_topSpan hT hN k⟩
    have hbd : BddAbove (Set.range fun V : {V : Submodule 𝕜 E // finrank 𝕜 V = k + 1} =>
        ⨅ x : {x : E // x ∈ V.1 ∧ ‖x‖ = 1}, rq T x.1) := by
      refine ⟨hT.eigenvalues hN k, ?_⟩
      rintro _ ⟨V, rfl⟩
      have := hne V
      exact le_eigenvalue_of_subspace hT hN k V.2.ge ((hiff V _).mp le_rfl)
    refine le_trans ?_ (le_ciSup hbd V0)
    exact (hiff V0 _).mpr (fun x hx => eigenvalue_mul_le_rq_topSpan hT hN k hx)
  · have : Nonempty {V : Submodule 𝕜 E // finrank 𝕜 V = k + 1} :=
      ⟨⟨topSpan hT hN k, finrank_topSpan hT hN k⟩⟩
    refine ciSup_le fun V => ?_
    have := hne V
    exact le_eigenvalue_of_subspace hT hN k V.2.ge ((hiff V _).mp le_rfl)

end Certificates

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.le_eigenvalue_of_subspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.le_eigenvalue_of_subspace

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.eigenvalue_le_of_subspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.eigenvalue_le_of_subspace

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.courant_fischer_maxmin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.courant_fischer_maxmin

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.courant_fischer_minmax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.courant_fischer_minmax

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.courant_fischer_maxmin_iSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.courant_fischer_maxmin_iSup

end FormalResearch.MatrixAnalysis.Spectral
