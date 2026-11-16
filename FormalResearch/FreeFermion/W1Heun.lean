module

public import FormalResearch.FreeFermion.W1Tridiagonal

/-!
# The Heun commutant of a Leonard pair (Weyl W1, `thm:heun`)

Source: `Weyl/free_fermion/paper/parts/model.tex`, Theorem `thm:heun` (Heun commutant); the abstract
mechanism is the Grünbaum–Vinet–Zhedanov Heun operator, and the specialisation to Carron–Lewis
folded spin is `Weyl/P1`, `thm:Heun`.

## Statement formalised

`FormalResearch.FreeFermion.heun_commutant`.  A finite-dimensional space `V` over `𝕜 = ℝ` or `ℂ`
(any `RCLike 𝕜`), with bases `e`, `f` indexed by a finite linear order `ι`.
`X` has eigenbasis `e` with strictly increasing real eigenvalues `x`, `Y` has eigenbasis `f` with
strictly increasing real eigenvalues `y`; `Y` is irreducible tridiagonal in `e`, `X` is
irreducible tridiagonal in `f` (a Leonard pair).  `W` and `P` are the spectral projections
`W e_n = [n ≤ K] e_n`, `P f_n = [n ≤ M] f_n`, with cuts `K ⋖ K'` and `M ⋖ M'`.  With the midgaps
`μ_X = (x_K + x_K')/2`, `μ_Y = (y_M + y_M')/2` and
`H = {X - μ_X, Y - μ_Y}`:

* `H W = W H` and `H P = P H`;
* in the basis `e` the matrix of `H` is tridiagonal, its link between `n ⋖ n'` vanishes exactly at
  the cut `n = K` and is nonzero otherwise (both directions), and likewise in the basis `f` at `M`:
  the restrictions to `Ran W`, `Ran (1 - W)`, `Ran P`, `Ran (1 - P)` are Jacobi matrices with
  nonzero links (`IsJacobiWithCut`);
* each restriction has simple spectrum: for every `λ` the eigenspace of `H` inside `Ran W`
  (resp. `ker W = Ran (1 - W)`, `Ran P`, `ker P`) has dimension at most one.

## What is not formalised / differences from the paper

* The paper takes `X`, `Y` self-adjoint (orthonormal eigenbases).  The proof uses neither
  self-adjointness nor orthonormality, so the formal statement is more general: any bases, any
  `RCLike` field.  Self-adjointness is the special case of an orthonormal basis with real
  eigenvalues.  The spectral projections are characterised by `W e_n = [n ≤ K] e_n`
  (which determines them uniquely), rather than constructed by functional calculus.
* "Irreducible tridiagonal" is required in both directions of each link for the Jacobi clause; the
  commutation uses only tridiagonality, and the simple-spectrum clause only the upper links.
* The index set is an arbitrary finite linear order with adjacency `⋖` (the paper's `{0, …, N}`).
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix Module

variable {ι : Type*} [LinearOrder ι] [Fintype ι]
variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- `M` is the matrix of a chain cut at `K`: tridiagonal, the links between adjacent indices
`i ⋖ j` vanish (both directions) exactly when `i = K`, and are nonzero (both directions) otherwise.
So `M` is block diagonal along the cut, with each block an irreducible (Jacobi) tridiagonal
matrix. -/
def IsJacobiWithCut (M : Matrix ι ι 𝕜) (K : ι) : Prop :=
  IsTridiag M ∧ ∀ i j, i ⋖ j →
    (i = K → M i j = 0 ∧ M j i = 0) ∧ (i ≠ K → M i j ≠ 0 ∧ M j i ≠ 0)

/-- `M` is *irreducible tridiagonal*: tridiagonal with every link between adjacent indices nonzero
(in both directions). -/
def IsIrreducibleTridiag (M : Matrix ι ι 𝕜) : Prop :=
  IsTridiag M ∧ ∀ i j, i ⋖ j → M i j ≠ 0 ∧ M j i ≠ 0

/-- The matrix of a diagonalisable operator in its eigenbasis. -/
theorem toMatrix_eigen (e : Basis ι 𝕜 V) (X : V →ₗ[𝕜] V) (x : ι → 𝕜)
    (hXe : ∀ n, X (e n) = x n • e n) :
    LinearMap.toMatrixAlgEquiv e X = diagonal x := by
  ext i j
  by_cases h : i = j
  · subst h; simp [LinearMap.toMatrixAlgEquiv_apply, hXe]
  · simp [LinearMap.toMatrixAlgEquiv_apply, hXe, h]

private theorem cast_coeff_eq_zero_iff (a b c d : ℝ) :
    ((a : 𝕜) + (b : 𝕜) - 2 * (((c + d) / 2 : ℝ) : 𝕜) = 0) ↔ a + b = c + d := by
  have : ((a : 𝕜) + (b : 𝕜) - 2 * (((c + d) / 2 : ℝ) : 𝕜)) = ((a + b - (c + d) : ℝ) : 𝕜) := by
    push_cast; ring
  rw [this, RCLike.ofReal_eq_zero, sub_eq_zero]

/-- Eigenvector bound: eigenvectors of `H` lying in a subspace `U` whose coordinates are supported on
`S` span at most a line, when `H` is tridiagonal in `e` with nonzero upper links above the least
element `a` of `S`. -/
theorem finrank_eigenspace_inf_le_one (e : Basis ι 𝕜 V) (H : V →ₗ[𝕜] V)
    (hT : IsTridiag (LinearMap.toMatrixAlgEquiv e H)) (S : Set ι) (a : ι) (ha : ∀ n ∈ S, a ≤ n)
    (hlink : ∀ p n, p ⋖ n → a ≤ p → n ∈ S → LinearMap.toMatrixAlgEquiv e H p n ≠ 0)
    (U : Submodule 𝕜 V) (hU : ∀ v ∈ U, ∀ n, n ∉ S → e.repr v n = 0) (lam : 𝕜) :
    finrank 𝕜 ↥(Module.End.eigenspace H lam ⊓ U) ≤ 1 := by
  have : Module.Finite 𝕜 V := Module.Finite.of_basis e
  let g : ↥(Module.End.eigenspace H lam ⊓ U) →ₗ[𝕜] 𝕜 :=
    (e.coord a).domRestrict (Module.End.eigenspace H lam ⊓ U)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨v, hvE, hvU⟩ hv0
    have hva : e.repr v a = 0 := by simpa [g] using hv0
    have hev : H v = lam • v := Module.End.mem_eigenspace_iff.mp hvE
    have hmul : LinearMap.toMatrixAlgEquiv e H *ᵥ ⇑(e.repr v) = lam • ⇑(e.repr v) := by
      have := LinearMap.toMatrix_mulVec_repr e e H v
      change LinearMap.toMatrix e e H *ᵥ ⇑(e.repr v) = _
      rw [this, hev]
      ext n; simp
    have h0 := eq_zero_of_eigen_of_tridiag _ hT lam (⇑(e.repr v)) hmul S
      (fun n hn => hU v hvU n hn) a ha hlink hva
    apply Subtype.ext
    have : e.repr v = 0 := Finsupp.ext fun n => congrFun h0 n
    simpa using this
  have := LinearMap.finrank_le_finrank_of_injective hg
  simpa using this

/-- One side of `thm:heun`, in the eigenbasis `e` of `X`.  `H = {X - μ_X, Y - ν}` with the midgap
`μ_X = (x_K + x_K')/2` commutes with `W`, has an `IsJacobiWithCut` matrix in `e`, and has simple
spectrum on `Ran W` and on `ker W`; `ν` is arbitrary. -/
theorem heun_side (e : Basis ι 𝕜 V) (X Y W : V →ₗ[𝕜] V) (x : ι → ℝ) (hx : StrictMono x)
    (hXe : ∀ n, X (e n) = (x n : 𝕜) • e n)
    (hYe : IsTridiag (LinearMap.toMatrixAlgEquiv e Y))
    (hYl : ∀ i j, i ⋖ j → LinearMap.toMatrixAlgEquiv e Y i j ≠ 0 ∧
      LinearMap.toMatrixAlgEquiv e Y j i ≠ 0)
    {K K' : ι} (hK : K ⋖ K') (hW : ∀ n, W (e n) = if n ≤ K then e n else 0) (ν : 𝕜) :
    let H := heun 𝕜 X Y (((x K + x K') / 2 : ℝ) : 𝕜) ν
    H * W = W * H ∧ IsJacobiWithCut (LinearMap.toMatrixAlgEquiv e H) K ∧
      (∀ lam : 𝕜, finrank 𝕜 ↥(Module.End.eigenspace H lam ⊓ LinearMap.range W) ≤ 1) ∧
      (∀ lam : 𝕜, finrank 𝕜 ↥(Module.End.eigenspace H lam ⊓ LinearMap.ker W) ≤ 1) := by
  intro H
  set φ := LinearMap.toMatrixAlgEquiv e with hφ
  set Ym := φ Y with hYm
  have hXm : φ X = diagonal (fun n => (x n : 𝕜)) := toMatrix_eigen e X _ hXe
  have hWm : φ W = diagonal (fun n => if n ≤ K then (1 : 𝕜) else 0) :=
    toMatrix_eigen e W _ (fun n => by by_cases h : n ≤ K <;> simp [hW, h])
  have hHm : φ H = heun 𝕜 (diagonal (fun n => (x n : 𝕜))) Ym (((x K + x K') / 2 : ℝ) : 𝕜) ν := by
    rw [map_heun, hXm]
  have hent : ∀ i j, φ H i j = ((x i : 𝕜) + x j - 2 * (((x K + x K') / 2 : ℝ) : 𝕜)) *
      (Ym i j - if i = j then ν else 0) := fun i j => by
    rw [hHm, heun_diagonal_apply]
  -- entries across the cut vanish
  have hcross : ∀ i j, i ⋖ j → i = K → φ H i j = 0 ∧ φ H j i = 0 := by
    intro i j hij hiK
    subst hiK
    have hz : (x i : 𝕜) + x j - 2 * (((x i + x K') / 2 : ℝ) : 𝕜) = 0 := by
      rw [cast_coeff_eq_zero_iff, hK.unique_right hij]
    refine ⟨?_, ?_⟩
    · rw [hent, hz, zero_mul]
    · rw [hent, show (x j : 𝕜) + x i - 2 * (((x i + x K') / 2 : ℝ) : 𝕜) = 0 by
        rw [← hz]; ring, zero_mul]
  have hnz : ∀ i j, i ⋖ j → i ≠ K → φ H i j ≠ 0 ∧ φ H j i ≠ 0 := by
    intro i j hij hiK
    have hc : (x i : 𝕜) + x j - 2 * (((x K + x K') / 2 : ℝ) : 𝕜) ≠ 0 := fun h =>
      hiK ((sum_eq_iff hx hK hij).mp ((cast_coeff_eq_zero_iff _ _ _ _).mp h))
    have hc' : (x j : 𝕜) + x i - 2 * (((x K + x K') / 2 : ℝ) : 𝕜) ≠ 0 := by
      intro h; apply hc; rw [← h]; ring
    refine ⟨?_, ?_⟩
    · rw [hent]
      simp only [hij.ne, ↓reduceIte, sub_zero]
      exact mul_ne_zero hc (hYl i j hij).1
    · rw [hent]
      simp only [hij.ne.symm, ↓reduceIte, sub_zero]
      exact mul_ne_zero hc' (hYl i j hij).2
  have htri : IsTridiag (φ H) := by
    intro i j hij
    by_cases hd : i = j
    · exact Or.inl hd
    · rw [hent] at hij
      simp only [hd, ↓reduceIte, sub_zero] at hij
      exact Or.inr ((hYe i j (right_ne_zero_of_mul hij)).resolve_left hd)
  have hz1 : ∀ i j, i ≤ K → ¬ j ≤ K → φ H i j = 0 := by
    intro i j hi hj
    by_contra h
    rcases htri i j h with rfl | hij | hji
    · exact hj hi
    · have hiK : i = K := by
        by_contra hne
        exact hij.2 (lt_of_le_of_ne hi hne) (not_le.mp hj)
      exact h (hcross i j hij hiK).1
    · exact hj (hji.lt.le.trans hi)
  have hz2 : ∀ i j, i ≤ K → ¬ j ≤ K → φ H j i = 0 := by
    intro i j hi hj
    by_contra h
    rcases htri j i h with rfl | hji | hij
    · exact hj hi
    · exact hj (hji.lt.le.trans hi)
    · have hiK : i = K := by
        by_contra hne
        exact hij.2 (lt_of_le_of_ne hi hne) (not_le.mp hj)
      exact h (hcross i j hij hiK).2
  have hcoord : ∀ u n, e.repr (W u) n = (if n ≤ K then (1 : 𝕜) else 0) * e.repr u n := by
    intro u n
    have := congrFun (LinearMap.toMatrix_mulVec_repr e e W u) n
    have hWm' : LinearMap.toMatrix e e W = diagonal (fun n => if n ≤ K then (1 : 𝕜) else 0) :=
      hWm
    rw [hWm'] at this
    simpa [mulVec_diagonal] using this.symm
  refine ⟨?_, ⟨htri, fun i j hij => ⟨hcross i j hij, hnz i j hij⟩⟩, ?_, ?_⟩
  · apply φ.injective
    rw [map_mul, map_mul, hWm]
    ext i j
    rw [mul_diagonal, diagonal_mul]
    by_cases hi : i ≤ K <;> by_cases hj : j ≤ K
    · simp [hi, hj]
    · simp [hi, hj, hz1 i j hi hj]
    · simp [hi, hj, hz2 j i hj hi]
    · simp [hi, hj]
  · intro lam
    have hne : (Finset.univ : Finset ι).Nonempty := ⟨K, Finset.mem_univ _⟩
    refine finrank_eigenspace_inf_le_one e H htri {n | n ≤ K} (Finset.univ.min' hne)
      (fun n _ => Finset.min'_le _ _ (Finset.mem_univ _)) ?_ _ ?_ lam
    · intro p n hpn _ hn
      refine (hnz p n hpn fun hpK => ?_).1
      exact absurd (hpK ▸ hpn.lt) (not_lt.mpr hn)
    · rintro v ⟨u, rfl⟩ n hn
      have hn' : ¬ n ≤ K := hn
      simp [hcoord, hn']
  · intro lam
    refine finrank_eigenspace_inf_le_one e H htri {n | ¬ n ≤ K} K' ?_ ?_ _ ?_ lam
    · intro n hn
      exact not_lt.mp fun h => hK.2 (not_le.mp hn) h
    · intro p n hpn hp _
      refine (hnz p n hpn fun hpK => ?_).1
      exact absurd (hpK ▸ hK.lt.trans_le hp) (lt_irrefl _)
    · intro v hv n hn
      have hn' : n ≤ K := not_not.mp hn
      have := hcoord v n
      rw [LinearMap.mem_ker.mp hv] at this
      simpa [hn'] using this.symm

/-- **Heun commutant of a Leonard pair** (paper `thm:heun`; see the module docstring for the exact
reading of the hypotheses and what is not formalised).

`X` has eigenbasis `e` with strictly increasing eigenvalues `x`, `Y` has eigenbasis `f` with strictly
increasing eigenvalues `y`; `Y` is irreducible tridiagonal in `e`, `X` irreducible tridiagonal in `f`.
`W`, `P` are the spectral projections on the first `K+1` (resp. `M+1`) eigenvectors.  For
`H = {X - μ_X, Y - μ_Y}` with the midgaps `μ_X = (x_K + x_K')/2`, `μ_Y = (y_M + y_M')/2`:
`H` commutes with `W` and `P`; its matrices in `e` and in `f` are tridiagonal with links vanishing
exactly at the cut (`IsJacobiWithCut`); and its restrictions to `Ran W`, `Ran (1 - W)`, `Ran P`,
`Ran (1 - P)` have simple spectrum (all eigenspaces have dimension at most one). -/
theorem heun_commutant (e f : Basis ι 𝕜 V) (X Y W P : V →ₗ[𝕜] V) (x y : ι → ℝ)
    (hx : StrictMono x) (hy : StrictMono y)
    (hXe : ∀ n, X (e n) = (x n : 𝕜) • e n) (hYf : ∀ n, Y (f n) = (y n : 𝕜) • f n)
    (hYe : IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv e Y))
    (hXf : IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv f X))
    {K K' M M' : ι} (hK : K ⋖ K') (hM : M ⋖ M')
    (hW : ∀ n, W (e n) = if n ≤ K then e n else 0)
    (hP : ∀ n, P (f n) = if n ≤ M then f n else 0) :
    let H := heun 𝕜 X Y (((x K + x K') / 2 : ℝ) : 𝕜) (((y M + y M') / 2 : ℝ) : 𝕜)
    H * W = W * H ∧ H * P = P * H ∧
      IsJacobiWithCut (LinearMap.toMatrixAlgEquiv e H) K ∧
      IsJacobiWithCut (LinearMap.toMatrixAlgEquiv f H) M ∧
      (∀ lam : 𝕜, finrank 𝕜 ↥(Module.End.eigenspace H lam ⊓ LinearMap.range W) ≤ 1) ∧
      (∀ lam : 𝕜, finrank 𝕜 ↥(Module.End.eigenspace H lam ⊓ LinearMap.ker W) ≤ 1) ∧
      (∀ lam : 𝕜, finrank 𝕜 ↥(Module.End.eigenspace H lam ⊓ LinearMap.range P) ≤ 1) ∧
      (∀ lam : 𝕜, finrank 𝕜 ↥(Module.End.eigenspace H lam ⊓ LinearMap.ker P) ≤ 1) := by
  intro H
  obtain ⟨h1, h2, h3, h4⟩ := heun_side e X Y W x hx hXe hYe.1 hYe.2 hK hW
    (((y M + y M') / 2 : ℝ) : 𝕜)
  have hH : H = heun 𝕜 Y X (((y M + y M') / 2 : ℝ) : 𝕜) (((x K + x K') / 2 : ℝ) : 𝕜) :=
    heun_comm _ _ _ _ _
  obtain ⟨g1, g2, g3, g4⟩ := heun_side f Y X P y hy hYf hXf.1 hXf.2 hM hP
    (((x K + x K') / 2 : ℝ) : 𝕜)
  rw [← hH] at g1 g2 g3 g4
  exact ⟨h1, g1, h2, g2, h3, h4, g3, g4⟩

/-- info: 'FormalResearch.FreeFermion.heun_commutant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms heun_commutant

end FormalResearch.FreeFermion
