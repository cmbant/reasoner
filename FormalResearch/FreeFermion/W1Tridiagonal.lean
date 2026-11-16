module

public import Mathlib

/-!
# Tridiagonal matrices on a finite chain and the Heun operator entries (Weyl W1, `thm:heun`)

Source: `Weyl/free_fermion/paper/parts/model.tex`, `thm:heun` (proof by the entry formula
`{D, B}_{nn'} = (D_nn + D_n'n') B_nn'` for a diagonal `D`).

Matrix-level core of `FormalResearch.FreeFermion.W1Heun`.  The index type `ι` is any finite linear
order; "adjacent" is `CovBy` (`⋖`), so no `Fin` arithmetic is needed.

* `IsTridiag` : a matrix whose nonzero entries lie on the diagonal or between adjacent indices.
* `heun`      : the Heun operator `{X - μ, Y - ν} = (X - μ)(Y - ν) + (Y - ν)(X - μ)` in any algebra.
* `heun_diagonal_apply` : the entry formula `H_{ij} = (x_i + x_j - 2μ)(Y_{ij} - ν δ_{ij})`.
* `sum_eq_iff` : for adjacent `i ⋖ j` and a cut `K ⋖ K'`, `x_i + x_j = x_K + x_K' ↔ i = K`.
* `eq_zero_of_eigen_of_tridiag` : an eigenvector of a tridiagonal matrix with nonzero upper links,
  supported on an upper set and vanishing at its least element, is zero (so eigenspaces of Jacobi
  blocks have dimension at most one).

Nothing here uses self-adjointness or orthonormality.
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix

section Tridiag

variable {ι : Type*} [LinearOrder ι] {𝕜 : Type*} [Field 𝕜]

/-- A matrix is *tridiagonal* (for the covering relation of the linear order `ι`) when every
nonzero entry sits on the diagonal or between adjacent indices. -/
def IsTridiag (M : Matrix ι ι 𝕜) : Prop :=
  ∀ i j, M i j ≠ 0 → i = j ∨ i ⋖ j ∨ j ⋖ i

/-- Eigenvector lemma behind "a Jacobi matrix with nonzero links has simple spectrum".
`M` is tridiagonal, `v` is an eigenvector (or the zero vector) supported on `S`, `a` is the least
element of `S`, every upper link `p ⋖ n` with `a ≤ p`, `n ∈ S` is nonzero, and `v a = 0`.
Then `v = 0`. -/
theorem eq_zero_of_eigen_of_tridiag [Fintype ι] (M : Matrix ι ι 𝕜) (hT : IsTridiag M) (lam : 𝕜)
    (v : ι → 𝕜) (hv : M *ᵥ v = lam • v) (S : Set ι) (hsupp : ∀ n, n ∉ S → v n = 0) (a : ι)
    (ha : ∀ n ∈ S, a ≤ n) (hlink : ∀ p n, p ⋖ n → a ≤ p → n ∈ S → M p n ≠ 0)
    (hva : v a = 0) : v = 0 := by
  funext n
  induction n using WellFoundedLT.induction with
  | _ n ih =>
  by_cases hn : n ∈ S
  swap
  · exact hsupp n hn
  by_cases hna : n = a
  · subst hna; exact hva
  have han : a < n := lt_of_le_of_ne (ha n hn) (Ne.symm hna)
  -- the predecessor of `n` above `a`
  obtain ⟨p, hpn, hap⟩ : ∃ p, p ⋖ n ∧ a ≤ p := by
    have hne : (Finset.univ.filter fun m => a ≤ m ∧ m < n).Nonempty :=
      ⟨a, by simp [han]⟩
    refine ⟨(Finset.univ.filter fun m => a ≤ m ∧ m < n).max' hne, ⟨?_, ?_⟩, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2.2
    · intro c hpc hcn
      have hmem : c ∈ Finset.univ.filter fun m => a ≤ m ∧ m < n :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp
          (Finset.max'_mem _ hne)).2.1.trans hpc.le, hcn⟩
      exact absurd (Finset.le_max' _ c hmem) (not_le.mpr hpc)
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2.1
  have hvp : v p = 0 := ih p hpn.lt
  have hrow := congrFun hv p
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hvp, mul_zero] at hrow
  have hsum : ∑ j, M p j * v j = M p n * v n := by
    apply Finset.sum_eq_single n
    · intro j _ hj
      by_cases h0 : M p j = 0
      · simp [h0]
      · rcases hT p j h0 with h | h | h
        · subst h; simp [hvp]
        · exact absurd (h.unique_right hpn) hj
        · simp [ih j (h.lt.trans hpn.lt)]
    · simp
  rw [hsum] at hrow
  exact (mul_eq_zero.mp hrow).resolve_left (hlink p n hpn hap hn)

end Tridiag

section Heun

variable {ι : Type*} [LinearOrder ι] {𝕜 : Type*} [Field 𝕜]

/-- The Heun operator `{X - μ, Y - ν} = (X - μ)(Y - ν) + (Y - ν)(X - μ)` (with the scalars
`μ, ν` acting through the algebra map). -/
def heun (𝕜 : Type*) [Field 𝕜] {A : Type*} [Ring A] [Algebra 𝕜 A] (X Y : A) (μ ν : 𝕜) : A :=
  (X - algebraMap 𝕜 A μ) * (Y - algebraMap 𝕜 A ν) + (Y - algebraMap 𝕜 A ν) * (X - algebraMap 𝕜 A μ)

/-- The Heun operator is symmetric under exchanging the roles of `(X, μ)` and `(Y, ν)`. -/
theorem heun_comm (A : Type*) [Ring A] [Algebra 𝕜 A] (X Y : A) (μ ν : 𝕜) :
    heun 𝕜 X Y μ ν = heun 𝕜 Y X ν μ := by
  unfold heun; abel

/-- Algebra isomorphisms preserve the Heun operator. -/
theorem map_heun {A B : Type*} [Ring A] [Algebra 𝕜 A] [Ring B] [Algebra 𝕜 B] (φ : A ≃ₐ[𝕜] B)
    (X Y : A) (μ ν : 𝕜) : φ (heun 𝕜 X Y μ ν) = heun 𝕜 (φ X) (φ Y) μ ν := by
  simp [heun, AlgEquiv.commutes]

omit [LinearOrder ι] in
/-- Entry formula: for a diagonal `D = diag x`, `{D - μ, Y - ν}_{ij} = (x_i + x_j - 2μ)(Y_{ij} - ν δ_{ij})`. -/
theorem heun_diagonal_apply [DecidableEq ι] [Fintype ι] (x : ι → 𝕜) (Y : Matrix ι ι 𝕜) (μ ν : 𝕜)
    (i j : ι) :
    heun 𝕜 (diagonal x) Y μ ν i j =
      (x i + x j - 2 * μ) * (Y i j - if i = j then ν else 0) := by
  have h1 : diagonal x - algebraMap 𝕜 (Matrix ι ι 𝕜) μ = diagonal (fun n => x n - μ) := by
    rw [Matrix.algebraMap_eq_diagonal, ← diagonal_sub]; rfl
  have h2 : Y - algebraMap 𝕜 (Matrix ι ι 𝕜) ν = Y - diagonal (fun _ => ν) := by
    rw [Matrix.algebraMap_eq_diagonal]; rfl
  simp only [heun, h1, h2, diagonal_mul, mul_diagonal, Matrix.add_apply,
    Matrix.sub_apply, diagonal_apply]
  split_ifs <;> ring

end Heun

section Cut

variable {ι : Type*} [LinearOrder ι]

/-- For adjacent `i ⋖ j` and a cut `K ⋖ K'` of a strictly increasing `x`, the pair sum
`x_i + x_j` equals the midgap sum `x_K + x_K'` exactly at the cut link `i = K`
("since `x_n + x_{n+1}` increases with `n`" in the paper's proof). -/
theorem sum_eq_iff {x : ι → ℝ} (hx : StrictMono x) {K K' : ι} (hK : K ⋖ K') {i j : ι}
    (hij : i ⋖ j) : x i + x j = x K + x K' ↔ i = K := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hj : j ≤ K := not_lt.mp fun hKj => hij.2 hlt hKj
      have h1 := hx hlt
      have h2 := hx.monotone hj
      have h3 := hx hK.lt
      linarith
    · have hK' : K' ≤ i := not_lt.mp fun hlt => hK.2 hgt hlt
      have h1 := hx.monotone hK'
      have h2 := hx hij.lt
      have h3 := hx hgt
      linarith
  · rintro rfl
    rw [hK.unique_right hij]

end Cut

end FormalResearch.FreeFermion
