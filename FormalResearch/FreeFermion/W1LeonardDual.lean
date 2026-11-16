module

public import FormalResearch.FreeFermion.W1Heun

/-!
# Leonard pairs from the tridiagonal relation (Weyl W1, `thm:heun`, `prop:bisp`)

Source: `Weyl/free_fermion/paper/parts/model.tex`, Theorem `thm:heun` and the sentence after it ("The
Krawtchouk, Hahn and dual Hahn chains are such pairs too"), Proposition `prop:bisp`.  The mechanism is
the Terwilliger tridiagonal relation of a Leonard pair
(`A²A* - 2AA*A + A*A² - γ(AA* + A*A) - ρA* ∈ span(A², A, 1)`); it replaces the explicit
generating-function computation of `W1Krawtchouk` by one operator identity, and gives the duality
for every chain whose pair satisfies the relation (Hahn: `W1Hahn`, folded Racah: `W1RacahChain`).

## Statements formalised

* `exists_eigenbasis`: an endomorphism whose `dim V` prescribed (distinct) values are all eigenvalues
  has an eigenbasis indexed by them.
* `hasEigenvalue_of_conj_upperTriangular`: if `M P = P T` with `P` invertible and `T` upper
  triangular, every diagonal entry `T_kk` is an eigenvalue of `M` (the spectrum of a chain from a
  triangular model).
* `tridiag_dual_of_relation` (**the duality criterion**).  `X` is diagonal in a basis `e` with
  distinct eigenvalues `x`, `Y` is irreducible tridiagonal in `e`, `Y` has an eigenbasis `f` with
  eigenvalues `y`, and
  `tdRel X Y γ ρ = c₂ Y² + c₁ Y + c₀`.  If `(y_i - y_j)² - γ(y_i+y_j) - ρ ≠ 0` for every
  non-adjacent pair `i ≠ j`, then `X` is **irreducible tridiagonal in `f`**: tridiagonal because the
  relation sandwiched between `f_i, f_j` kills `X_ij` unless the pair is adjacent, and nonzero links
  because a vanishing link would give a proper non-zero subspace invariant under `X` and `Y`, while
  `X` diagonal with distinct eigenvalues and `Y` irreducible tridiagonal in `e` has none
  (`invariant_eq_bot_or_top`).
* `irreducible_of_tridiag_dual`: irreducibility of the dual is automatic (the hypothesis of
  `thm:heun` "each irreducible tridiagonal in an eigenbasis of the other" can be weakened to "`Y`
  irreducible tridiagonal in an eigenbasis of `X`, and `X` tridiagonal in an eigenbasis of `Y`").

Nothing here uses self-adjointness or orthonormality, and the index set is an arbitrary finite
linear order.

## Not formalised

The converse (a Leonard pair satisfies the relation), the classification of the spectra
(`θ_i` quadratic or linear in `i`), and the `q`-deformed (Askey-Wilson) relation.
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix Module

section Eigenbasis

variable {ι : Type*} [Fintype ι] [Nonempty ι] {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
  [Module 𝕜 V]

/-- An endomorphism of a space of dimension `|ι|` having the `|ι|` distinct values `y i` as
eigenvalues has an eigenbasis `f` with `Y f_i = y_i f_i`. -/
theorem exists_eigenbasis (hV : finrank 𝕜 V = Fintype.card ι)
    (Y : V →ₗ[𝕜] V) (y : ι → 𝕜) (hy : Function.Injective y)
    (h : ∀ i, Module.End.HasEigenvalue Y (y i)) :
    ∃ f : Basis ι 𝕜 V, ∀ i, Y (f i) = y i • f i := by
  choose v hv using fun i => (h i).exists_hasEigenvector
  have hli : LinearIndependent 𝕜 v := Module.End.eigenvectors_linearIndependent' Y y hy v hv
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hV.symm, fun i => ?_⟩
  simpa using (Module.End.mem_eigenspace_iff.mp (hv i).1)

omit [Nonempty ι] in
/-- The spectrum of an operator with an eigenbasis `f`, `Y f_i = y_i f_i`, is exactly `{y_i}`. -/
theorem hasEigenvalue_iff_of_eigenbasis (f : Basis ι 𝕜 V) (Y : V →ₗ[𝕜] V) (y : ι → 𝕜)
    (hYf : ∀ i, Y (f i) = y i • f i) (lam : 𝕜) :
    Module.End.HasEigenvalue Y lam ↔ ∃ k, lam = y k := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    obtain ⟨hvE, hv0⟩ := hv
    have hvE' : Y v = lam • v := Module.End.mem_eigenspace_iff.mp hvE
    obtain ⟨k, hk⟩ : ∃ k, f.repr v k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hv0
      apply f.repr.injective
      ext k
      simpa using hcon k
    have hY : f.repr (Y v) k = y k * f.repr v k := by
      conv_lhs => rw [← f.sum_repr v]
      simp only [map_sum, map_smul, hYf]
      simp [Finsupp.single_apply, mul_comm]
    rw [hvE'] at hY
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hY
    exact ⟨k, mul_right_cancel₀ hk hY⟩
  · rintro ⟨k, rfl⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (hYf k), f.ne_zero k⟩

end Eigenbasis

section Spectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {K : Type*} [Field K]

/-- If `M P = P T` with `P` invertible and `T` upper triangular, every diagonal entry of `T` is an
eigenvalue of `M`: the characteristic polynomial of `M` is that of `T`, `∏ (X - T_kk)`. -/
theorem hasEigenvalue_of_conj_upperTriangular (M P T : Matrix ι ι K) (hP : IsUnit P.det)
    (hT : T.IsUpperTriangular) (hMP : M * P = P * T) (k : ι) :
    Module.End.HasEigenvalue (Matrix.toLin' M) (T k k) := by
  have hM : M = P * T * P⁻¹ := by
    rw [← hMP, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one]
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hP
  have hcp : M.charpoly = T.charpoly := by
    have := Matrix.charpoly_units_conj hu.unit T
    rw [hM]
    simpa using this
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
    Matrix.mem_spectrum_iff_isRoot_charpoly, hcp, Matrix.charpoly_of_isUpperTriangular _ hT,
    Polynomial.IsRoot, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)

end Spectrum

section Duality

variable {ι : Type*} [LinearOrder ι] [Fintype ι]
variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- The tridiagonal-relation operator `Y²X - 2YXY + XY² - γ(YX + XY) - ρX`. -/
def tdRel (X Y : V →ₗ[𝕜] V) (γ ρ : 𝕜) : V →ₗ[𝕜] V :=
  Y * Y * X - (2 : 𝕜) • (Y * X * Y) + X * Y * Y - γ • (Y * X + X * Y) - ρ • X

/-- A subspace invariant under `X` is invariant under every polynomial in `X`. -/
theorem aeval_mem_of_invariant (X : V →ₗ[𝕜] V) (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, X u ∈ U)
    (p : Polynomial 𝕜) {u : V} (hu : u ∈ U) : Polynomial.aeval X p u ∈ U := by
  have hpow : ∀ n : ℕ, (X ^ n) u ∈ U := by
    intro n
    induction n with
    | zero => simpa using hu
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hU _ ih
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [map_add] using U.add_mem hp hq
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact U.smul_mem _ (hpow n)

/-- Every `e_m`-component of an element of an `X`-invariant subspace stays in the subspace, when
`X` is diagonal in `e` with distinct eigenvalues (Lagrange interpolation in `X`). -/
theorem repr_smul_mem (e : Basis ι 𝕜 V) (X : V →ₗ[𝕜] V) (x : ι → ℝ) (hx : Function.Injective x)
    (hXe : ∀ n, X (e n) = (x n : 𝕜) • e n) (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, X u ∈ U)
    {u : V} (hu : u ∈ U) (n : ι) : e.repr u n • e n ∈ U := by
  classical
  set v : ι → 𝕜 := fun m => (x m : 𝕜) with hv
  have hinj : Set.InjOn v (Finset.univ : Finset ι) := fun a _ b _ h =>
    hx (by simpa [hv] using h)
  have h1 := aeval_mem_of_invariant X U hU (Lagrange.basis Finset.univ v n) hu
  have h2 : Polynomial.aeval X (Lagrange.basis Finset.univ v n) u = e.repr u n • e n := by
    conv_lhs => rw [← e.sum_repr u]
    rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_eq_single n]
    · rw [Module.End.aeval_apply_of_hasEigenvector (μ := v n) ⟨?_, e.ne_zero n⟩,
        Lagrange.eval_basis_self hinj (Finset.mem_univ n)]
      · simp
      · exact Module.End.mem_eigenspace_iff.mpr (hXe n)
    · intro m _ hm
      rw [Module.End.aeval_apply_of_hasEigenvector (μ := v m) ⟨?_, e.ne_zero m⟩,
        Lagrange.eval_basis_of_ne (Ne.symm hm) (Finset.mem_univ m)]
      · simp
      · exact Module.End.mem_eigenspace_iff.mpr (hXe m)
    · simp
  rwa [h2] at h1

/-- A finite linear order: `n < m` gives a predecessor of `m` covering-adjacent, above `n`. -/
theorem exists_covBy_between {n m : ι} (h : n < m) : ∃ p, p ⋖ m ∧ n ≤ p := by
  have hne : (Finset.univ.filter fun c => n ≤ c ∧ c < m).Nonempty := ⟨n, by simp [h]⟩
  refine ⟨(Finset.univ.filter fun c => n ≤ c ∧ c < m).max' hne, ⟨?_, ?_⟩, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2.2
  · intro c hpc hcn
    have hmem : c ∈ Finset.univ.filter fun c => n ≤ c ∧ c < m :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp
        (Finset.max'_mem _ hne)).2.1.trans hpc.le, hcn⟩
    exact absurd (Finset.le_max' _ c hmem) (not_le.mpr hpc)
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2.1

/-- `m < n` gives a successor of `m` covering-adjacent, below `n`. -/
theorem exists_covBy_between' {n m : ι} (h : m < n) : ∃ q, m ⋖ q ∧ q ≤ n := by
  have hne : (Finset.univ.filter fun c => m < c ∧ c ≤ n).Nonempty := ⟨n, by simp [h]⟩
  refine ⟨(Finset.univ.filter fun c => m < c ∧ c ≤ n).min' hne, ⟨?_, ?_⟩, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2.1
  · intro c hmc hcq
    have hmem : c ∈ Finset.univ.filter fun c => m < c ∧ c ≤ n :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmc, hcq.le.trans
        (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2.2⟩
    exact absurd (Finset.min'_le _ c hmem) (not_le.mpr hcq)
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2.2

/-- A set of indices closed under covering neighbours and containing one point is everything. -/
theorem eq_univ_of_closed (S : Set ι) (n0 : ι) (h0 : n0 ∈ S)
    (hup : ∀ p m, p ⋖ m → p ∈ S → m ∈ S) (hdown : ∀ p m, p ⋖ m → m ∈ S → p ∈ S) :
    ∀ m, m ∈ S := by
  have hu : ∀ m, n0 ≤ m → m ∈ S := by
    intro m
    induction m using WellFoundedLT.induction with
    | _ m ih =>
      intro hm
      rcases hm.eq_or_lt with rfl | hlt
      · exact h0
      · obtain ⟨p, hpm, hnp⟩ := exists_covBy_between hlt
        exact hup p m hpm (ih p hpm.lt hnp)
  have hd : ∀ m, m ≤ n0 → m ∈ S := by
    intro m
    induction m using WellFoundedGT.induction with
    | _ m ih =>
      intro hm
      rcases hm.eq_or_lt with rfl | hlt
      · exact h0
      · obtain ⟨q, hmq, hqn⟩ := exists_covBy_between' hlt
        exact hdown m q hmq (ih q hmq.lt hqn)
  intro m
  rcases le_total n0 m with h | h
  · exact hu m h
  · exact hd m h

/-- A subspace invariant under both `X` (diagonal in `e` with distinct eigenvalues) and `Y`
(irreducible tridiagonal in `e`) is `0` or everything. -/
theorem invariant_eq_bot_or_top (e : Basis ι 𝕜 V) (X Y : V →ₗ[𝕜] V) (x : ι → ℝ)
    (hx : Function.Injective x) (hXe : ∀ n, X (e n) = (x n : 𝕜) • e n)
    (hYe : IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv e Y)) (U : Submodule 𝕜 V)
    (hXU : ∀ u ∈ U, X u ∈ U) (hYU : ∀ u ∈ U, Y u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_cases hb : U = ⊥
  · exact Or.inl hb
  right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hrep : ∃ n, e.repr u n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu0
    apply e.repr.injective
    ext n
    simpa using hcon n
  obtain ⟨n0, hn0⟩ := hrep
  have hmem : ∀ n, e n ∈ U → ∀ m, LinearMap.toMatrixAlgEquiv e Y m n ≠ 0 → e m ∈ U := by
    intro n hn m hm
    have h1 := repr_smul_mem e X x hx hXe U hXU (hYU _ hn) m
    have h2 : e.repr (Y (e n)) m = LinearMap.toMatrixAlgEquiv e Y m n := by
      simp [LinearMap.toMatrixAlgEquiv_apply]
    rw [h2] at h1
    have := U.smul_mem (LinearMap.toMatrixAlgEquiv e Y m n)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hm, one_smul] at this
  have hall := eq_univ_of_closed {n | e n ∈ U} n0
    (by
      have := repr_smul_mem e X x hx hXe U hXU huU n0
      have := U.smul_mem (e.repr u n0)⁻¹ this
      rwa [smul_smul, inv_mul_cancel₀ hn0, one_smul] at this)
    (fun p m hpm hp => hmem p hp m (hYe.2 p m hpm).2)
    (fun p m hpm hm => hmem m hm p (hYe.2 p m hpm).1)
  rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  exact hall n

/-- `Y` acts diagonally on coordinates in an eigenbasis. -/
theorem repr_apply_of_eigenbasis (f : Basis ι 𝕜 V) (Y : V →ₗ[𝕜] V) (y : ι → ℝ)
    (hYf : ∀ n, Y (f n) = (y n : 𝕜) • f n) (v : V) (i : ι) :
    f.repr (Y v) i = (y i : 𝕜) * f.repr v i := by
  conv_lhs => rw [← f.sum_repr v]
  rw [map_sum]
  simp only [map_smul, hYf]
  simp [Finsupp.single_apply, mul_comm, RCLike.real_smul_eq_coe_mul]


/-- If a set `s` of indices contains `a` but not `b`, and the `f`-coordinates of `X f_j`, `j ∈ s`,
stay in `s`, then `span f(s)` is a proper non-zero subspace invariant under `X` and `Y`: impossible
when `X` is diagonal with distinct eigenvalues and `Y` irreducible tridiagonal in `e`. -/
theorem no_invariant_span (e f : Basis ι 𝕜 V) (X Y : V →ₗ[𝕜] V) (x y : ι → ℝ)
    (hx : Function.Injective x) (hXe : ∀ n, X (e n) = (x n : 𝕜) • e n)
    (hYf : ∀ n, Y (f n) = (y n : 𝕜) • f n)
    (hYe : IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv e Y)) (s : Set ι)
    (hXs : ∀ j ∈ s, ∀ i, f.repr (X (f j)) i ≠ 0 → i ∈ s) {a b : ι} (ha : a ∈ s) (hb : b ∉ s) :
    False := by
  set U : Submodule 𝕜 V := Submodule.span 𝕜 (f '' s) with hU
  have hXU : ∀ u ∈ U, X u ∈ U := by
    intro u hu
    have : U.map X ≤ U := by
      rw [hU, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      rw [← f.sum_repr (X (f j))]
      refine U.sum_mem fun i _ => ?_
      by_cases hz : f.repr (X (f j)) i = 0
      · simp [hz]
      · exact U.smul_mem _ (Submodule.subset_span ⟨i, hXs j hj i hz, rfl⟩)
    exact this ⟨u, hu, rfl⟩
  have hYU : ∀ u ∈ U, Y u ∈ U := by
    intro u hu
    have : U.map Y ≤ U := by
      rw [hU, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      rw [hYf]
      exact U.smul_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    exact this ⟨u, hu, rfl⟩
  rcases invariant_eq_bot_or_top e X Y x hx hXe hYe U hXU hYU with hbot | htop
  · have : f a ∈ U := Submodule.subset_span ⟨a, ha, rfl⟩
    rw [hbot] at this
    exact f.ne_zero a (by simpa using this)
  · have : f b ∈ U := by rw [htop]; trivial
    exact f.linearIndependent.notMem_span_image hb this

/-- **Irreducibility is automatic** (Terwilliger).  If `X` is diagonal in `e` with distinct
eigenvalues, `Y` is irreducible tridiagonal in `e` and diagonal in `f`, and `X` is merely
*tridiagonal* in `f`, then `X` is irreducible tridiagonal in `f`: a vanishing link would give a proper
non-zero subspace invariant under both. -/
theorem irreducible_of_tridiag_dual (e f : Basis ι 𝕜 V) (X Y : V →ₗ[𝕜] V) (x y : ι → ℝ)
    (hx : Function.Injective x) (hXe : ∀ n, X (e n) = (x n : 𝕜) • e n)
    (hYf : ∀ n, Y (f n) = (y n : 𝕜) • f n)
    (hYe : IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv e Y))
    (htri : IsTridiag (LinearMap.toMatrixAlgEquiv f X)) :
    IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv f X) := by
  have hT : ∀ i j, LinearMap.toMatrixAlgEquiv f X i j = f.repr (X (f j)) i := fun i j => by
    simp [LinearMap.toMatrixAlgEquiv_apply]
  refine ⟨htri, fun k k' hk => ⟨?_, ?_⟩⟩
  · -- the link `T k k'`: coefficient of `f_k` in `X f_k'`
    intro h0
    refine no_invariant_span e f X Y x y hx hXe hYf hYe {i | k' ≤ i} ?_ (a := k') (b := k)
      (le_refl _) (fun h => not_le.mpr hk.lt h)
    intro j hj i hi
    have hi' : LinearMap.toMatrixAlgEquiv f X i j ≠ 0 := by rwa [hT]
    show k' ≤ i
    rcases htri i j hi' with hij | hij | hji
    · rw [hij]; exact hj
    · rcases (show k' ≤ j from hj).eq_or_lt with hjk | hlt
      · have : i = k := by rw [← hjk] at hij; exact hij.unique_left hk
        rw [this, ← hjk] at hi'
        exact absurd h0 hi'
      · by_contra hik
        exact hij.2 (not_le.mp hik) hlt
    · exact (show k' ≤ j from hj).trans hji.lt.le
  · -- the link `T k' k`: coefficient of `f_k'` in `X f_k`
    intro h0
    refine no_invariant_span e f X Y x y hx hXe hYf hYe {i | i ≤ k} ?_ (a := k) (b := k')
      (le_refl _) (fun h => not_le.mpr hk.lt h)
    intro j hj i hi
    have hi' : LinearMap.toMatrixAlgEquiv f X i j ≠ 0 := by rwa [hT]
    show i ≤ k
    rcases htri i j hi' with hij | hij | hji
    · rw [hij]; exact hj
    · exact hij.lt.le.trans hj
    · rcases (show j ≤ k from hj).eq_or_lt with hjk | hlt
      · have : i = k' := by rw [hjk] at hji; exact hji.unique_right hk
        rw [this, hjk] at hi'
        exact absurd h0 hi'
      · by_contra hik
        exact hji.2 hlt (not_le.mp hik)


/-- **Duality criterion** (Terwilliger's tridiagonal relation).  `X` is diagonal in `e` with distinct
eigenvalues `x`, `Y` is irreducible tridiagonal in `e` and diagonal in the basis `f` with eigenvalues
`y`, and `tdRel X Y γ ρ = c₂ Y² + c₁ Y + c₀` with `(y_i - y_j)² - γ(y_i + y_j) - ρ ≠ 0` for all
non-adjacent `i ≠ j`.  Then `X` is irreducible tridiagonal in `f`. -/
theorem tridiag_dual_of_relation (e f : Basis ι 𝕜 V) (X Y : V →ₗ[𝕜] V) (x y : ι → ℝ)
    (hx : Function.Injective x) (hXe : ∀ n, X (e n) = (x n : 𝕜) • e n)
    (hYf : ∀ n, Y (f n) = (y n : 𝕜) • f n)
    (hYe : IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv e Y)) (γ ρ c₂ c₁ c₀ : ℝ)
    (hrel : tdRel X Y (γ : 𝕜) (ρ : 𝕜) = (c₂ : 𝕜) • (Y * Y) + (c₁ : 𝕜) • Y + (c₀ : 𝕜) • 1)
    (hc : ∀ i j, i ≠ j → ¬ i ⋖ j → ¬ j ⋖ i → (y i - y j) ^ 2 - γ * (y i + y j) - ρ ≠ 0) :
    IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv f X) := by
  have hT : ∀ i j, LinearMap.toMatrixAlgEquiv f X i j = f.repr (X (f j)) i := fun i j => by
    simp [LinearMap.toMatrixAlgEquiv_apply]
  have hYy : ∀ v i, f.repr (Y v) i = (y i : 𝕜) * f.repr v i :=
    fun v i => repr_apply_of_eigenbasis f Y y hYf v i
  have htri : IsTridiag (LinearMap.toMatrixAlgEquiv f X) := by
    intro i j hne
    by_contra hcon
    push Not at hcon
    obtain ⟨hij, h1, h2⟩ := hcon
    have hcij := hc i j hij h1 h2
    have h := congrArg (fun v => f.repr v i) (LinearMap.congr_fun hrel (f j))
    simp only [tdRel, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply, Module.End.one_apply, hYf, map_smul, map_sub, map_add,
      Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply, hYy, smul_eq_mul,
      Basis.repr_self, Finsupp.single_apply, hij.symm, ite_false, mul_zero, add_zero] at h
    rw [hT] at hne
    have h3 : f.repr (X (f j)) i * (((y i - y j) ^ 2 - γ * (y i + y j) - ρ : ℝ) : 𝕜) = 0 := by
      push_cast
      linear_combination h
    exact hne ((mul_eq_zero.mp h3).resolve_right (by exact_mod_cast hcij))
  exact irreducible_of_tridiag_dual e f X Y x y hx hXe hYf hYe htri

end Duality

end FormalResearch.FreeFermion
