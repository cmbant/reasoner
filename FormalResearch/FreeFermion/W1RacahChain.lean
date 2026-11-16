module

public import FormalResearch.FreeFermion.W1RacahSpectrum

/-!
# The folded squared-spin chain is a Leonard pair; its Heun operator (Weyl W1, `cor:racahheun`)

Source: `Weyl/free_fermion/notes/racah_chain.tex`: `eq:model` (the chain `X = diag(q²)`, `Y`),
`lem:duality`, `cor:racahheun` ("By Lemma `lem:duality` the folded Racah pair is a self-adjoint
Leonard pair as in `thm:heun`, with `x_q = q²`, `y_r = r²` (`q, r` even), and since
`q² + (q+2)² = 2(q²+2q+2)` the midgaps are `μ_Q, μ_R`.  Hence `[H, W] = [H, P] = 0`"), and
`thm:heun` (`W1Heun`).

## Statements formalised (every `M`; `L = 2M`, index `j = q/2`)

* `racChain M`, `racX M` (`W1RacahSpectrum`): the chain of `eq:model`; spectrum
  `{(2k)²}` (`racChain_hasEigenvalue`).
* `rac_tdRel`: the **tridiagonal relation**
  `tdRel X Y 8 (-16) = 8 Y² - 8(Λ+1) Y + 8Λ`, `Λ = L(L+1)`, i.e.
  `[Y,[Y,X]] - 8{Y,X} + 16 X = 8 (Y-1)(Y-Λ)` for `X = diag(q²)`; the folded `√2` link is invisible
  because the coefficient `2x_1 - 2x_0 - 8` of the doubled `a_0²` vanishes.
* `rac_dual_irreducible`: **`X` is irreducible tridiagonal in an eigenbasis of `Y`** (the duality of
  `lem:duality`, in the form needed for `thm:heun`), from `rac_tdRel`, the spectrum
  and `tridiag_dual_of_relation`:
  `(y_i-y_j)² - 8(y_i+y_j) + 16 = 16((i-j)²-1)((i+j)²-1)` for `y = 4k²`.
* `racah_heun`: the instance of `heun_commutant` (`cor:racahheun`): for all cuts `H = {X - μ_Q,
  Y - μ_R}` commutes with `W` and `P` with simple-spectrum Jacobi blocks, the midgaps being the
  `μ_Q = (x_K + x_K')/2`, i.e. `Q² + 2Q + 2` for `K = Q/2`, `K' = K + 1`.

## Not formalised

`lem:duality` itself (the identification with `K_x²`, `K_z²` on the even symmetric subspace of spin
`L`, the orthogonal involution `U` with the Wigner `d`-matrix `d^L(π/2)`): here the Leonard pair
property is proved without it, so `thm:heun` applies to the chain as defined by its matrix entries.
Orthogonality of the `Y`-eigenbasis, the Racah polynomials, `prop:racahtt` and the travel time.
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix Module

section Pair

variable {M : ℕ}

/-- The eigenvalues `y_k = (2k)² = r²`. -/
noncomputable def racEig (M : ℕ) (k : Fin (M + 1)) : ℝ := 4 * (k : ℝ) ^ 2

theorem racEig_strictMono : StrictMono (racEig M) := by
  intro a b hab
  have hab' : ((a : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have h0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  unfold racEig
  nlinarith

/-- The folded chain as an operator on `ℝ^{M+1}`. -/
noncomputable def racY (M : ℕ) : (Fin (M + 1) → ℝ) →ₗ[ℝ] (Fin (M + 1) → ℝ) :=
  Matrix.toLin' (racChain M)

/-- The position operator `X = diag(q²)` on `ℝ^{M+1}`. -/
noncomputable def racXop (M : ℕ) : (Fin (M + 1) → ℝ) →ₗ[ℝ] (Fin (M + 1) → ℝ) :=
  Matrix.toLin' (racX M)

theorem racY_matrix_e : LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin (M + 1))) (racY M) =
    racChain M := by
  ext i j
  simp [LinearMap.toMatrixAlgEquiv_apply, racY, Matrix.toLin'_apply, Matrix.mulVec_single]

theorem racX_basis_e (n : Fin (M + 1)) :
    racXop M (Pi.basisFun ℝ (Fin (M + 1)) n) =
      (4 * ((n : ℕ) : ℝ) ^ 2) • Pi.basisFun ℝ (Fin (M + 1)) n := by
  ext j
  by_cases h : j = n <;>
    simp [racXop, racX, racPos, Matrix.toLin'_apply, Matrix.mulVec_diagonal, h]

theorem racChain_irreducible : IsIrreducibleTridiag (racChain M) :=
  triChain_irreducible M _ _ fun _ hm => (racA_nat_pos hm).ne'

/-- The eigenbasis of the folded chain (existence from the `M+1` distinct eigenvalues). -/
theorem rac_exists_eigenbasis :
    ∃ f : Basis (Fin (M + 1)) ℝ (Fin (M + 1) → ℝ), ∀ k, racY M (f k) = racEig M k • f k :=
  exists_eigenbasis (by simp) (racY M) (racEig M) racEig_strictMono.injective
    fun k => racChain_hasEigenvalue k

/-- An eigenbasis `f_k` of the folded chain, `Y f_k = (2k)² f_k` (chosen, not constructed; in the
paper, the columns `ψ_r = V e_r` of `lem:duality`). -/
noncomputable def racBasis (M : ℕ) : Basis (Fin (M + 1)) ℝ (Fin (M + 1) → ℝ) :=
  rac_exists_eigenbasis.choose

theorem racY_basis (k : Fin (M + 1)) : racY M (racBasis M k) = racEig M k • racBasis M k :=
  rac_exists_eigenbasis.choose_spec k

/-! ### The tridiagonal relation -/

/-- The diagonal identity at `n = 0, 1, ≥ 2`; the doubled link `a_0² = 2 Q(0)/16` is compensated at
`n = 1` by the vanishing coefficient `2x_1 - 2x_0 - 8 = 0`. -/
theorem rac_E0 (n : ℤ) (h0 : 0 ≤ n) (hn : n ≤ M) :
    racA M n ^ 2 * (2 * racPos n - 2 * racPos (n + 1)) +
      racA M (n - 1) ^ 2 * (2 * racPos n - 2 * racPos (n - 1)) -
      2 * 8 * racPos n * racDg M n - (-16) * racPos n -
      8 * (racA M n ^ 2 + racA M (n - 1) ^ 2 + racDg M n ^ 2) -
      (-(8 * (racLam M + 1))) * racDg M n - 8 * racLam M = 0 := by
  have e1 := racA_sq h0 hn
  by_cases hn0 : n = 0
  · subst hn0
    have hA : racA M ((0 : ℤ) - 1) = 0 := by simpa using racA_neg_one (M := M)
    rw [hA, e1]
    simp only [racPos, racDg, racb, racQ, racLam]
    push_cast
    ring
  · by_cases hn1 : n = 1
    · subst hn1
      have e2 := racA_sq (M := M) (n := (1 : ℤ) - 1) (by omega) (by omega)
      rw [e1, e2]
      simp only [racPos, racDg, racb, racQ, racLam]
      push_cast
      simp
      ring
    · have e2 := racA_sq (M := M) (n := n - 1) (by omega) (by omega)
      have h1 : ¬ (n - 1 = 0) := by omega
      rw [e1, e2]
      simp only [hn0, h1, ↓reduceIte]
      simp only [racPos, racDg, racb, racQ, racLam]
      push_cast
      ring

theorem rac_tdRel :
    tdRel (racXop M) (racY M) ((8 : ℝ) : ℝ) ((-16 : ℝ) : ℝ) =
      (8 : ℝ) • (racY M * racY M) + (-(8 * (racLam M + 1)) : ℝ) • racY M +
        (8 * racLam M : ℝ) • (1 : Module.End ℝ (Fin (M + 1) → ℝ)) := by
  refine tdRel_triChain M (racA M) (racDg M) racPos racA_neg_one racA_top 8 (-16) 8
    (-(8 * (racLam M + 1))) (8 * racLam M) ?_ ?_ ?_
  · intro n
    simp only [racPos]
    push_cast
    ring
  · intro n
    have : (racPos (n + 1) - racPos n) * (racDg M n - racDg M (n + 1)) -
        8 * (racPos (n + 1) + racPos n) - 8 * (racDg M n + racDg M (n + 1)) -
        (-(8 * (racLam M + 1))) = 0 := by
      simp only [racPos, racDg, racb]
      push_cast
      ring
    rw [this, mul_zero]
  · intro n h0 hn
    exact rac_E0 n h0 hn

/-! ### Irreducibility of the dual and the Heun operator -/

theorem rac_theta_ne (a b : ℕ) (hab : a + 2 ≤ b ∨ b + 2 ≤ a) :
    ((4 * (a : ℝ) ^ 2) - 4 * (b : ℝ) ^ 2) ^ 2 - 8 * (4 * (a : ℝ) ^ 2 + 4 * (b : ℝ) ^ 2) -
      (-16) ≠ 0 := by
  have hfac : ((4 * (a : ℝ) ^ 2) - 4 * (b : ℝ) ^ 2) ^ 2 - 8 * (4 * (a : ℝ) ^ 2 + 4 * (b : ℝ) ^ 2) -
      (-16) = 16 * (((a : ℝ) - b) ^ 2 - 1) * (((a : ℝ) + b) ^ 2 - 1) := by ring
  rw [hfac]
  have hsum : (2 : ℝ) ≤ (a : ℝ) + b := by
    have : 2 ≤ a + b := by omega
    exact_mod_cast this
  have hd : (2 : ℝ) ≤ (a : ℝ) - b ∨ (2 : ℝ) ≤ (b : ℝ) - a := by
    rcases hab with h | h
    · right
      have : (a : ℝ) + 2 ≤ b := by exact_mod_cast h
      linarith
    · left
      have : (b : ℝ) + 2 ≤ a := by exact_mod_cast h
      linarith
  have h1 : 0 < ((a : ℝ) - b) ^ 2 - 1 := by
    rcases hd with h | h <;> nlinarith
  have h2 : 0 < ((a : ℝ) + b) ^ 2 - 1 := by nlinarith
  exact (mul_pos (mul_pos (by norm_num) h1) h2).ne'

theorem rac_dual_irreducible :
    IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv (racBasis M) (racXop M)) := by
  have hmono : Function.Injective (fun n : Fin (M + 1) => 4 * ((n : ℕ) : ℝ) ^ 2) := by
    intro a b hab
    have h1 : ((a : ℕ) : ℝ) ^ 2 = ((b : ℕ) : ℝ) ^ 2 := by simpa using hab
    have : ((a : ℕ) : ℝ) = b :=
      (sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp h1
    exact Fin.ext (by exact_mod_cast this)
  have hrel : tdRel (racXop M) (racY M) (RCLike.ofReal (8 : ℝ) : ℝ)
      (RCLike.ofReal (-16 : ℝ) : ℝ) =
      (RCLike.ofReal (8 : ℝ) : ℝ) • (racY M * racY M) +
        (RCLike.ofReal (-(8 * (racLam M + 1)) : ℝ) : ℝ) • racY M +
        (RCLike.ofReal (8 * racLam M : ℝ) : ℝ) • (1 : Module.End ℝ (Fin (M + 1) → ℝ)) := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using rac_tdRel (M := M)
  refine tridiag_dual_of_relation (Pi.basisFun ℝ (Fin (M + 1))) (racBasis M) (racXop M) (racY M)
    (fun n => 4 * ((n : ℕ) : ℝ) ^ 2) (racEig M) hmono racX_basis_e racY_basis
    (by rw [racY_matrix_e]; exact racChain_irreducible) 8 (-16) 8 (-(8 * (racLam M + 1)))
    (8 * racLam M) hrel ?_
  intro i j hij h1 h2
  simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h1 h2
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hfar : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i := by omega
  exact rac_theta_ne i j hfar

/-- **The folded squared-spin chain is a Leonard pair; its Heun operator commutes with both spectral
projections exactly** (`cor:racahheun`, via `thm:heun`).

For every `M`, `Y` the chain of `eq:model` (`L = 2M`) and `X = diag(q²)`, `q = 2n`: `X` has the
eigenbasis `e` (standard basis, eigenvalues `q² = 4n²`) and `Y` the eigenbasis `f_k` (`racBasis`,
eigenvalues `(2k)²`); `Y` is irreducible tridiagonal in `e` and `X` irreducible tridiagonal in `f`,
and for every pair of cuts the Heun operator `H = {X - μ_X, Y - μ_Y}` with the midgaps
`μ_X = (x_K + x_K')/2` (`= Q² + 2Q + 2` for `Q = 2K`), `μ_Y = (y_M + y_M')/2` commutes with the
spectral projections `W` (of `X`, on `n ≤ K`) and `P` (of `Y`, on `k ≤ M`) and restricts to
simple-spectrum Jacobi blocks. -/
theorem racah_heun (M : ℕ) {K K' R R' : Fin (M + 1)} (hK : K ⋖ K') (hR : R ⋖ R')
    (W P : (Fin (M + 1) → ℝ) →ₗ[ℝ] (Fin (M + 1) → ℝ))
    (hW : ∀ n, W (Pi.basisFun ℝ (Fin (M + 1)) n) =
      if n ≤ K then Pi.basisFun ℝ (Fin (M + 1)) n else 0)
    (hP : ∀ n, P (racBasis M n) = if n ≤ R then racBasis M n else 0) :
    let H := heun ℝ (racXop M) (racY M)
      ((4 * ((K : ℕ) : ℝ) ^ 2 + 4 * ((K' : ℕ) : ℝ) ^ 2) / 2)
      ((racEig M R + racEig M R') / 2)
    H * W = W * H ∧ H * P = P * H ∧
      IsJacobiWithCut (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin (M + 1))) H) K ∧
      IsJacobiWithCut (LinearMap.toMatrixAlgEquiv (racBasis M) H) R ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.range W) ≤ 1) ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.ker W) ≤ 1) ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.range P) ≤ 1) ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.ker P) ≤ 1) := by
  have hmono : StrictMono (fun n : Fin (M + 1) => 4 * ((n : ℕ) : ℝ) ^ 2) := racEig_strictMono
  exact heun_commutant (Pi.basisFun ℝ (Fin (M + 1))) (racBasis M) (racXop M) (racY M) W P
    (fun n => 4 * ((n : ℕ) : ℝ) ^ 2) (racEig M) hmono racEig_strictMono racX_basis_e
    racY_basis (by rw [racY_matrix_e]; exact racChain_irreducible) rac_dual_irreducible hK hR hW hP

/-- info: 'FormalResearch.FreeFermion.racChain_hasEigenvalue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racChain_hasEigenvalue

/-- info: 'FormalResearch.FreeFermion.rac_dual_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rac_dual_irreducible

/-- info: 'FormalResearch.FreeFermion.racah_heun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_heun

end Pair

end FormalResearch.FreeFermion
