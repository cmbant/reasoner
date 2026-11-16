module

public import FormalResearch.FreeFermion.W1HahnSpectrum

/-!
# The Hahn chain is a Leonard pair; its Heun operator (Weyl W1, `prop:bisp`(ii), `thm:heun`)

Source: `Weyl/free_fermion/paper/parts/model.tex`, Proposition `prop:bisp`(ii) (Hahn chain
`B(x) = (x+α+1)(N-x)`, `D(x) = x(N+β+1-x)`, `a_n = √(B(n)D(n+1))/N²`, `b_n = (B(n)+D(n))/N²` on
`0 ≤ n ≤ N`, `α, β > -1`) together with the sentence after `thm:heun` ("The Krawtchouk, Hahn and dual
Hahn chains are such pairs too"), and `thm:heun` (`W1Heun`).

## Statements formalised (all real `α, β > -1`, all `N ≥ 1`)

* `hahnChain α β N` (`W1HahnSpectrum`): the paper's chain; `hahnX N = diag(n/N)` (`x = t`).
* `hahn_hasEigenvalue` (`W1HahnSpectrum`): the spectrum is `{k(k+α+β+1)/N² : 0 ≤ k ≤ N}`
  (`N+1` distinct values, strictly increasing: `hahnEig_strictMono`).
* `hahn_tdRel`: the **tridiagonal relation**
  `tdRel X Y γ ρ = c₁ Y + c₀` for `X = diag(n/N)`, `Y = hahnChain`, with
  `γ = 2/N²`, `ρ = ((α+β)² + 2(α+β))/N⁴`, `c₁ = -(2N+β-α)/N³`, `c₀ = -N(α²+αβ+α+β)/N⁵`.
* `hahn_dual_irreducible`: in an eigenbasis `f = hahnBasis` of `Y`, **`X` is irreducible
  tridiagonal** (self-duality: the Hahn recurrence in the degree), from `hahn_tdRel`, the spectrum,
  and `tridiag_dual_of_relation`: the factorisation
  `(θ_i-θ_j)² - 2(θ_i+θ_j) - (s²-1) = ((i-j)²-1)((i+j+s)²-1)`, `θ_k = k(k+s)`, `s = α+β+1`, is
  nonzero for `|i-j| ≥ 2` exactly because `α + β > -2`.
* `hahn_heun`: the instance of `heun_commutant`: `H = {X - μ_X, Y - μ_Y}` commutes with the spectral
  projections of `X` (on `n ≤ K`) and `Y` (on `k ≤ M`) for every pair of cuts, with simple-spectrum
  Jacobi blocks.

## Remarks on the paper

The chain with the coefficients `B, D` above is, in the standard nomenclature, the *dual Hahn*
Jacobi matrix (the recurrence in `n` of the dual Hahn polynomials `R_n(λ(x); α, β, N)`,
`λ(x) = x(x+α+β+1)`), equivalently the difference operator of the Hahn polynomials `Q_k(x)` in the
variable `x`, with eigenvalues `λ(k) / N²`.  The Jacobi matrix of the Hahn polynomials proper (the
recurrence in the degree, spectrum `{x/N}`) is the matrix of `X` in the eigenbasis of `Y`
(`hahn_dual_irreducible`: `X f_k ∈ span(f_{k-1}, f_k, f_{k+1})` with nonzero links); the pair is the same
Leonard pair read from the other side, `heun_commutant` being symmetric in `(X, Y)`.

## Not formalised

The Hahn polynomials and the closed-form entries of the Jacobi matrix of `X` in `f` (the
coefficients `A_n`, `C_n` of the Hahn recurrence); orthogonality of `f`; the travel-time statements
and the global-class margin of `prop:bisp`(ii).
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix Module

section Pair

variable {α β : ℝ} {N : ℕ}

/-- The eigenvalues `y_k = k(k+α+β+1)/N²`. -/
noncomputable def hahnEig (α β : ℝ) (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  (k : ℝ) * (k + α + β + 1) / (N : ℝ) ^ 2

theorem hahnEig_strictMono (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) :
    StrictMono (hahnEig α β N) := by
  intro a b hab
  have hab' : ((a : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have h0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  unfold hahnEig
  rw [div_lt_div_iff_of_pos_right hNpos]
  nlinarith

theorem hahnEig_injective (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) :
    Function.Injective (hahnEig α β N) := (hahnEig_strictMono hα hβ hN).injective

/-- The Hahn chain as an operator on `ℝ^{N+1}`. -/
noncomputable def hahnY (α β : ℝ) (N : ℕ) : (Fin (N + 1) → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) :=
  Matrix.toLin' (hahnChain α β N)

/-- The position operator `X = diag(n/N)` on `ℝ^{N+1}`. -/
noncomputable def hahnXop (N : ℕ) : (Fin (N + 1) → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) :=
  Matrix.toLin' (hahnX N)

theorem hahnY_matrix_e : LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin (N + 1))) (hahnY α β N) =
    hahnChain α β N := by
  ext i j
  simp [LinearMap.toMatrixAlgEquiv_apply, hahnY, Matrix.toLin'_apply, Matrix.mulVec_single]

theorem hahnX_basis_e (n : Fin (N + 1)) :
    hahnXop N (Pi.basisFun ℝ (Fin (N + 1)) n) = (((n : ℕ) : ℝ) / N) • Pi.basisFun ℝ (Fin (N + 1)) n := by
  ext j
  by_cases h : j = n <;> simp [hahnXop, hahnX, hahnPos, Matrix.toLin'_apply, Matrix.mulVec_diagonal, h]

/-- The eigenbasis of the Hahn chain (existence from the `N+1` distinct eigenvalues). -/
theorem hahn_exists_eigenbasis (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) :
    ∃ f : Basis (Fin (N + 1)) ℝ (Fin (N + 1) → ℝ), ∀ k, hahnY α β N (f k) = hahnEig α β N k • f k :=
  exists_eigenbasis (by simp) (hahnY α β N) (hahnEig α β N) (hahnEig_injective hα hβ hN)
    fun k => hahn_hasEigenvalue hα hβ hN k

/-- An eigenbasis `f_k` of the Hahn chain, `Y f_k = (k(k+α+β+1)/N²) f_k` (the weighted Hahn
polynomials; chosen, not constructed). -/
noncomputable def hahnBasis (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) :
    Basis (Fin (N + 1)) ℝ (Fin (N + 1) → ℝ) :=
  (hahn_exists_eigenbasis hα hβ hN).choose

theorem hahnY_basis (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) (k : Fin (N + 1)) :
    hahnY α β N (hahnBasis hα hβ hN k) = hahnEig α β N k • hahnBasis hα hβ hN k :=
  (hahn_exists_eigenbasis hα hβ hN).choose_spec k

/-! ### The tridiagonal relation -/

theorem hahnA_sq (hα : -1 < α) (hβ : -1 < β) (n : ℤ) (h1 : -1 ≤ n) (h2 : n ≤ N) :
    hahnA α β N n ^ 2 = hahnB α N n * hahnD β N (n + 1) / (N : ℝ) ^ 4 := by
  have hnn : 0 ≤ hahnB α N (n : ℝ) * hahnD β N ((n : ℝ) + 1) := by
    rcases h1.eq_or_lt with rfl | h
    · simp [hahnD]
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := Int.eq_ofNat_of_zero_le (by omega)
      rcases (show m ≤ N by omega).lt_or_eq with hlt | rfl
      · obtain ⟨hB, hD⟩ := hahn_BD_pos hα hβ hlt
        simpa using (mul_pos hB hD).le
      · simp [hahnB]
  unfold hahnA
  rw [div_pow, Real.sq_sqrt (by simpa using hnn)]
  ring

theorem hahn_tdRel (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) :
    tdRel (hahnXop N) (hahnY α β N) ((2 / (N : ℝ) ^ 2 : ℝ) : ℝ)
        ((((α + β) ^ 2 + 2 * (α + β)) / (N : ℝ) ^ 4 : ℝ) : ℝ) =
      (0 : ℝ) • (hahnY α β N * hahnY α β N) +
        ((-(2 * N + β - α) / (N : ℝ) ^ 3 : ℝ) : ℝ) • hahnY α β N +
        ((-(N * (α ^ 2 + α * β + α + β)) / (N : ℝ) ^ 5 : ℝ) : ℝ) • (1 : Module.End ℝ (Fin (N + 1) → ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  refine tdRel_triChain N (hahnA α β N) (hahnDg α β N) (hahnPos N) (hahnA_neg_one α β N)
    (hahnA_top α β N) (2 / (N : ℝ) ^ 2) (((α + β) ^ 2 + 2 * (α + β)) / (N : ℝ) ^ 4) 0
    (-(2 * N + β - α) / (N : ℝ) ^ 3) (-(N * (α ^ 2 + α * β + α + β)) / (N : ℝ) ^ 5)
    ?_ ?_ ?_
  · intro n
    simp only [hahnPos]
    push_cast
    ring
  · intro n
    have : (hahnPos N (n + 1) - hahnPos N n) * (hahnDg α β N n - hahnDg α β N (n + 1)) -
        2 / (N : ℝ) ^ 2 * (hahnPos N (n + 1) + hahnPos N n) - 0 * (hahnDg α β N n + hahnDg α β N (n + 1)) -
        -(2 * N + β - α) / (N : ℝ) ^ 3 = 0 := by
      simp only [hahnPos, hahnDg, hahnB, hahnD]
      push_cast
      field_simp
      ring
    rw [this, mul_zero]
  · intro n hn0 hnN
    have e1 := hahnA_sq hα hβ n (by omega) hnN
    have e2 := hahnA_sq (N := N) hα hβ (n - 1) (by omega) (by omega)
    rw [e1, e2]
    simp only [hahnPos, hahnDg, hahnB, hahnD]
    push_cast
    field_simp
    ring

/-! ### Irreducibility of the chain and the dual -/

theorem hahnChain_irreducible (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) :
    IsIrreducibleTridiag (hahnChain α β N) := by
  refine triChain_irreducible N _ _ fun m hm => ?_
  obtain ⟨hB, hD⟩ := hahn_BD_pos hα hβ hm
  rw [hahnA_nat]
  have : 0 < √(hahnB α N (m : ℝ) * hahnD β N ((m : ℝ) + 1)) := Real.sqrt_pos.mpr (mul_pos hB hD)
  positivity

/-- The factorisation behind the duality: for the spectrum `θ_k = k(k+s)`,
`(θ_i-θ_j)² - 2(θ_i+θ_j) - (s²-1) = ((i-j)²-1)((i+j+s)²-1)`. -/
theorem hahn_theta_factor (i j s : ℝ) :
    (i * (i + s) - j * (j + s)) ^ 2 - 2 * (i * (i + s) + j * (j + s)) - (s ^ 2 - 1) =
      ((i - j) ^ 2 - 1) * ((i + j + s) ^ 2 - 1) := by ring

/-- The factor is nonzero for non-adjacent distinct indices when `s > -1`. -/
theorem hahn_theta_ne (a b : ℕ) (hab : a + 2 ≤ b ∨ b + 2 ≤ a) (s : ℝ) (hs : -1 < s) :
    ((a : ℝ) * (a + s) - b * (b + s)) ^ 2 - 2 * (a * (a + s) + b * (b + s)) - (s ^ 2 - 1) ≠ 0 := by
  rw [hahn_theta_factor]
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
  have h2 : 0 < ((a : ℝ) + b + s) ^ 2 - 1 := by nlinarith
  exact (mul_pos h1 h2).ne'

theorem hahn_dual_irreducible (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) :
    IsIrreducibleTridiag
      (LinearMap.toMatrixAlgEquiv (hahnBasis hα hβ hN) (hahnXop N)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : Function.Injective (fun n : Fin (N + 1) => ((n : ℕ) : ℝ) / N) := by
    intro a b hab
    have : ((a : ℕ) : ℝ) = b := by
      have := hab; field_simp at this; exact this
    exact Fin.ext (by exact_mod_cast this)
  have hrel : tdRel (hahnXop N) (hahnY α β N)
      (RCLike.ofReal (2 / (N : ℝ) ^ 2) : ℝ) (RCLike.ofReal (((α + β) ^ 2 + 2 * (α + β)) / (N : ℝ) ^ 4) : ℝ) =
      (RCLike.ofReal (0 : ℝ) : ℝ) • (hahnY α β N * hahnY α β N) +
        (RCLike.ofReal (-(2 * N + β - α) / (N : ℝ) ^ 3) : ℝ) • hahnY α β N +
        (RCLike.ofReal (-(N * (α ^ 2 + α * β + α + β)) / (N : ℝ) ^ 5) : ℝ) •
          (1 : Module.End ℝ (Fin (N + 1) → ℝ)) := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using hahn_tdRel hα hβ hN
  refine tridiag_dual_of_relation (Pi.basisFun ℝ (Fin (N + 1))) (hahnBasis hα hβ hN) (hahnXop N)
    (hahnY α β N) (fun n => ((n : ℕ) : ℝ) / N) (hahnEig α β N) hmono (hahnX_basis_e)
    (hahnY_basis hα hβ hN) (by rw [hahnY_matrix_e]; exact hahnChain_irreducible hα hβ hN)
    (2 / (N : ℝ) ^ 2) (((α + β) ^ 2 + 2 * (α + β)) / (N : ℝ) ^ 4) 0
    (-(2 * N + β - α) / (N : ℝ) ^ 3) (-(N * (α ^ 2 + α * β + α + β)) / (N : ℝ) ^ 5)
    hrel ?_
  intro i j hij h1 h2
  simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h1 h2
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hfar : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i := by omega
  have hne := hahn_theta_ne i j hfar (α + β + 1) (by linarith)
  have hN4 : (N : ℝ) ^ 4 ≠ 0 := by positivity
  have hN2 : (N : ℝ) ^ 2 ≠ 0 := by positivity
  have hey : (hahnEig α β N i - hahnEig α β N j) ^ 2 -
      2 / (N : ℝ) ^ 2 * (hahnEig α β N i + hahnEig α β N j) -
      ((α + β) ^ 2 + 2 * (α + β)) / (N : ℝ) ^ 4 =
      (((i : ℝ) * (i + (α + β + 1)) - j * (j + (α + β + 1))) ^ 2 -
        2 * (i * (i + (α + β + 1)) + j * (j + (α + β + 1))) - ((α + β + 1) ^ 2 - 1)) /
        (N : ℝ) ^ 4 := by
    unfold hahnEig
    field_simp
    ring
  rw [hey]
  exact div_ne_zero hne hN4

/-- **The Hahn chain is a Leonard pair; its Heun operator commutes with both spectral projections
exactly** (paper `prop:bisp`(ii), via `thm:heun`).

For real `α, β > -1`, `N ≥ 1`, `Y` the Hahn chain of the paper (`a_n = √(B(n)D(n+1))/N²`,
`b_n = (B(n)+D(n))/N²`) and `X = diag(n/N)`: `X` has eigenbasis `e` (standard basis, eigenvalues
`n/N`) and `Y` has the eigenbasis `f_k` (`hahnBasis`, eigenvalues `k(k+α+β+1)/N²`), `Y` is irreducible
tridiagonal in `e` and `X` irreducible tridiagonal in `f`, and for every pair of cuts the Heun
operator `H = {X - μ_X, Y - μ_Y}` (midgaps) commutes with the spectral projections `W` (of `X`, on
`n ≤ K`) and `P` (of `Y`, on `k ≤ M`) and restricts to simple-spectrum Jacobi blocks. -/
theorem hahn_heun (α β : ℝ) (N : ℕ) (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N)
    {K K' M M' : Fin (N + 1)} (hK : K ⋖ K') (hM : M ⋖ M')
    (W P : (Fin (N + 1) → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ))
    (hW : ∀ n, W (Pi.basisFun ℝ (Fin (N + 1)) n) =
      if n ≤ K then Pi.basisFun ℝ (Fin (N + 1)) n else 0)
    (hP : ∀ n, P (hahnBasis hα hβ hN n) = if n ≤ M then hahnBasis hα hβ hN n else 0) :
    let H := heun ℝ (hahnXop N) (hahnY α β N) ((((K : ℕ) : ℝ) / N + ((K' : ℕ) : ℝ) / N) / 2)
      ((hahnEig α β N M + hahnEig α β N M') / 2)
    H * W = W * H ∧ H * P = P * H ∧
      IsJacobiWithCut (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin (N + 1))) H) K ∧
      IsJacobiWithCut (LinearMap.toMatrixAlgEquiv (hahnBasis hα hβ hN) H) M ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.range W) ≤ 1) ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.ker W) ≤ 1) ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.range P) ≤ 1) ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.ker P) ≤ 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : StrictMono (fun n : Fin (N + 1) => ((n : ℕ) : ℝ) / N) := by
    intro a b hab
    have : ((a : ℕ) : ℝ) < b := by exact_mod_cast hab
    exact div_lt_div_of_pos_right this hNpos
  exact heun_commutant (Pi.basisFun ℝ (Fin (N + 1))) (hahnBasis hα hβ hN) (hahnXop N)
    (hahnY α β N) W P (fun n => ((n : ℕ) : ℝ) / N) (hahnEig α β N) hmono
    (hahnEig_strictMono hα hβ hN) (hahnX_basis_e) (hahnY_basis hα hβ hN)
    (by rw [hahnY_matrix_e]; exact hahnChain_irreducible hα hβ hN)
    (hahn_dual_irreducible hα hβ hN) hK hM hW hP

/-- info: 'FormalResearch.FreeFermion.hahn_hasEigenvalue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_hasEigenvalue

/-- info: 'FormalResearch.FreeFermion.hahn_dual_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_dual_irreducible

/-- info: 'FormalResearch.FreeFermion.hahn_heun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_heun

end Pair

end FormalResearch.FreeFermion
