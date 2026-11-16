module

public import FormalResearch.FreeFermion.W1TridiagRelation

/-!
# The Hahn chain: definitions and spectrum (Weyl W1, `prop:bisp`(ii))

Source: `Weyl/free_fermion/paper/parts/model.tex`, Proposition `prop:bisp`(ii): "Hahn chain,
`α, β > -1` fixed: `B(x) = (x+α+1)(N-x)`, `D(x) = x(N+β+1-x)`, `a_n = √(B(n) D(n+1))/N²`,
`b_n = (B(n)+D(n))/N²` on `0 ≤ n ≤ N`".

* `hahnChain α β N` : this symmetric tridiagonal matrix on `{0, …, N}` (`triChain`).
* `hahn_hasEigenvalue` : for all real `α, β > -1` and `N ≥ 1`, every `k(k+α+β+1)/N²`,
  `0 ≤ k ≤ N`, is an eigenvalue of the chain (so the spectrum is exactly that set, `N+1` values).

## Method (no Hahn polynomial theory)

With `D' = D/N²` etc., the chain is conjugate, by the diagonal matrix `diag(r_n)`,
`r_0 = 1`, `r_{n+1} = -B(n) r_n / √(B(n)D(n+1))` (alternating signs, `r_n ≠ 0`), to the
difference operator `g ↦ (B+D) g(x) - B g(x+1) - D g(x-1)`; this operator is **bidiagonal** on the
falling factorials `φ_j(x) = x(x-1)⋯(x-j+1)`:
`(B+D)φ_j - Bφ_j(·+1) - Dφ_j(·-1) = j(j+α+β+1) φ_j - j(N-j+1)(j+α) φ_{j-1}` (`hahn_poly_id`).
Hence `hahnChain · P = P · T` with `P_{kj} = r_k φ_j(k)` lower triangular and invertible and `T`
upper triangular with diagonal `j(j+α+β+1)/N²` (`hahn_chain_mul_P`), and the eigenvalues are read off
the characteristic polynomial (`hasEigenvalue_of_conj_upperTriangular`).

## Not formalised

The Hahn polynomials themselves (the eigenvectors are never written down; they are
`(-1)^n r_n^{-1}`-weighted `₃F₂(-k, k+α+β+1, -x; α+1, -N; 1)`), and the orthogonality weight.
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix Module

section Defs

variable (α β : ℝ) (N : ℕ)

/-- `B(x) = (x + α + 1)(N - x)` (`prop:bisp`(ii)). -/
def hahnB (x : ℝ) : ℝ := (x + α + 1) * (N - x)

/-- `D(x) = x (N + β + 1 - x)` (`prop:bisp`(ii)). -/
def hahnD (x : ℝ) : ℝ := x * (N + β + 1 - x)

/-- The link `a_n = √(B(n) D(n+1)) / N²`. -/
noncomputable def hahnA (n : ℤ) : ℝ := √(hahnB α N n * hahnD β N (n + 1)) / (N : ℝ) ^ 2

/-- The diagonal `b_n = (B(n) + D(n)) / N²`. -/
noncomputable def hahnDg (n : ℤ) : ℝ := (hahnB α N n + hahnD β N n) / (N : ℝ) ^ 2

/-- The Hahn chain of `prop:bisp`(ii) as a symmetric tridiagonal matrix on `{0, …, N}`. -/
noncomputable def hahnChain : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  triChain N (hahnA α β N) (hahnDg α β N)

/-- The position `x_n = n/N` (`x = t`), as a function on `ℤ`. -/
noncomputable def hahnPos (n : ℤ) : ℝ := (n : ℝ) / N

/-- The position operator `X = diag(n/N)`. -/
noncomputable def hahnX : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.diagonal fun n : Fin (N + 1) => hahnPos N n

theorem hahnX_apply (n : Fin (N + 1)) : hahnPos N n = (n : ℕ) / (N : ℝ) := by
  simp [hahnPos]

theorem hahnA_neg_one : hahnA α β N (-1) = 0 := by
  simp [hahnA, hahnD]

theorem hahnA_top : hahnA α β N N = 0 := by
  simp [hahnA, hahnB]

theorem hahnA_nat (n : ℕ) :
    hahnA α β N n = √(hahnB α N n * hahnD β N (n + 1)) / (N : ℝ) ^ 2 := by
  simp [hahnA]

theorem hahnDg_nat (n : ℕ) : hahnDg α β N n = (hahnB α N n + hahnD β N n) / (N : ℝ) ^ 2 := by
  simp [hahnDg]

variable {α β N}

theorem hahn_BD_pos (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : n < N) :
    0 < hahnB α N (n : ℝ) ∧ 0 < hahnD β N ((n : ℝ) + 1) := by
  have h1 : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · unfold hahnB
    exact mul_pos (by linarith) (by linarith)
  · unfold hahnD
    exact mul_pos (by linarith) (by linarith)

/-! ### The falling-factorial identity -/

private theorem dP_succ_right (m : ℕ) (x : ℝ) :
    (descPochhammer ℝ (m + 1)).eval x = (descPochhammer ℝ m).eval x * (x - m) := by
  rw [descPochhammer_succ_right]; simp

private theorem dP_succ_left (m : ℕ) (x : ℝ) :
    (descPochhammer ℝ (m + 1)).eval x = x * (descPochhammer ℝ m).eval (x - 1) := by
  rw [descPochhammer_succ_left]; simp

/-- The Hahn difference operator is bidiagonal on the falling factorials. -/
theorem hahn_poly_id (α β : ℝ) (N : ℕ) (x : ℝ) (m : ℕ) :
    (hahnB α N x + hahnD β N x) * (descPochhammer ℝ (m + 1)).eval x
        - hahnB α N x * (descPochhammer ℝ (m + 1)).eval (x + 1)
        - hahnD β N x * (descPochhammer ℝ (m + 1)).eval (x - 1) =
      ((m + 1) * (m + 1 + α + β + 1)) * (descPochhammer ℝ (m + 1)).eval x
        - ((m + 1) * (N - m) * (m + 1 + α)) * (descPochhammer ℝ m).eval x := by
  have h1 := dP_succ_right m x
  have h2 := dP_succ_left m x
  have h3 := dP_succ_left m (x + 1)
  have h4 := dP_succ_right m (x - 1)
  simp only [add_sub_cancel_right] at h3
  have hxw : x * (descPochhammer ℝ m).eval (x - 1) =
      (x - m) * (descPochhammer ℝ m).eval x := by
    have := h2.symm.trans h1
    linear_combination this
  rw [h1, h3, h4]
  unfold hahnB hahnD
  linear_combination (-((N : ℝ) + β + 1 - x) * (x - 1 - m)) * hxw

end Defs

section Spectrum

variable {α β : ℝ} {N : ℕ}

/-- The conjugating diagonal `r_0 = 1`, `r_{n+1} = -B(n) r_n / √(B(n) D(n+1))`. -/
noncomputable def hahnR (α β : ℝ) (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => -(hahnB α N n) * hahnR α β N n / √(hahnB α N n * hahnD β N (n + 1))

theorem hahnR_ne_zero (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : n ≤ N) : hahnR α β N n ≠ 0 := by
  induction n with
  | zero => simp [hahnR]
  | succ n ih =>
    have hlt : n < N := hn
    obtain ⟨hB, hD⟩ := hahn_BD_pos hα hβ hlt
    have hs : 0 < √(hahnB α N n * hahnD β N (n + 1)) := Real.sqrt_pos.mpr (mul_pos hB hD)
    simp only [hahnR]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hB.ne') (ih hlt.le)) hs.ne'

/-- `a_n r_{n+1} = -(B(n)/N²) r_n` for `n ≤ N` (both sides vanish at `n = N`). -/
theorem hahn_link_up (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : n ≤ N) :
    hahnA α β N n * hahnR α β N (n + 1) = -(hahnB α N n / (N : ℝ) ^ 2) * hahnR α β N n := by
  rcases hn.lt_or_eq with hlt | rfl
  · obtain ⟨hB, hD⟩ := hahn_BD_pos hα hβ hlt
    have hs : 0 < √(hahnB α N n * hahnD β N (n + 1)) := Real.sqrt_pos.mpr (mul_pos hB hD)
    rw [hahnA_nat]
    simp only [hahnR]
    field_simp
  · simp [hahnA_top, hahnB]

/-- `a_{n-1} r_{n-1} = -(D(n)/N²) r_n` for `1 ≤ n ≤ N`, and `a_{-1} = D(0) = 0`. -/
theorem hahn_link_down (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : n ≤ N) :
    hahnA α β N ((n : ℤ) - 1) * hahnR α β N (n - 1) =
      -(hahnD β N (n : ℝ) / (N : ℝ) ^ 2) * hahnR α β N n := by
  rcases n with _ | m
  · simp [hahnA_neg_one, hahnD]
  · have hlt : m < N := hn
    obtain ⟨hB, hD⟩ := hahn_BD_pos hα hβ hlt
    have hs : 0 < √(hahnB α N m * hahnD β N (m + 1)) := Real.sqrt_pos.mpr (mul_pos hB hD)
    have hsq : √(hahnB α N m * hahnD β N (m + 1)) ^ 2 = hahnB α N m * hahnD β N (m + 1) :=
      Real.sq_sqrt (mul_pos hB hD).le
    have hN0 : (N : ℝ) ≠ 0 := by
      have : 0 < N := by omega
      positivity
    have e1 : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    rw [e1, hahnA_nat]
    simp only [hahnR, Nat.add_sub_cancel]
    push_cast
    field_simp
    linear_combination (hahnR α β N m) * hsq

/-- The conjugating matrix `P_{kj} = r_k φ_j(k)`. -/
noncomputable def hahnP (α β : ℝ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun k j => hahnR α β N k * (descPochhammer ℝ j).eval (k : ℝ)

/-- The upper triangular (bidiagonal) model `T`. -/
noncomputable def hahnT (α β : ℝ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun l j => if l = j then (j : ℝ) * (j + α + β + 1) / (N : ℝ) ^ 2
    else if (l : ℕ) + 1 = j then -((j : ℝ) * (N - j + 1) * (j + α)) / (N : ℝ) ^ 2 else 0

/-- Action of a symmetric tridiagonal matrix on a vector given by a function of `ℕ`. -/
theorem triChain_mulVec_nat (N : ℕ) (a b : ℤ → ℝ) (ha1 : a (-1) = 0) (haN : a N = 0)
    (g : ℕ → ℝ) (i : Fin (N + 1)) :
    (triChain N a b *ᵥ fun k : Fin (N + 1) => g k) i =
      b i * g i + a i * g (i + 1) + a ((i : ℤ) - 1) * g (i - 1) := by
  have h := congrFun (extZ_triChain N a b ha1 haN (fun k : Fin (N + 1) => g k)) (i : ℕ)
  rw [Matrix.toLin'_apply, extZ_fin, Yh_apply, extZ_fin] at h
  rw [h]
  congr 1
  congr 1
  · by_cases hi : (i : ℕ) + 1 ≤ N
    · congr 1
      have hh : (0 : ℤ) ≤ ((i : ℕ) : ℤ) + 1 ∧ ((i : ℕ) : ℤ) + 1 ≤ N := by omega
      simp only [extZ_apply, eq_true hh, ↓reduceDIte]
      simp
    · have : (i : ℤ) = N := by omega
      rw [this, haN]; simp
  · by_cases hi : (i : ℕ) = 0
    · have : (i : ℤ) = 0 := by simp [hi]
      rw [this]
      simp [ha1]
    · congr 1
      have hh : (0 : ℤ) ≤ ((i : ℕ) : ℤ) - 1 ∧ ((i : ℕ) : ℤ) - 1 ≤ N := by omega
      simp only [extZ_apply, eq_true hh, ↓reduceDIte]
      simp

/-- The `j`-th column of `hahnChain · P`: the difference operator applied to `φ_j`. -/
theorem hahn_chain_mul_P_apply (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) (i : Fin (N + 1))
    (j : Fin (N + 1)) :
    (hahnChain α β N * hahnP α β N) i j =
      hahnR α β N i / (N : ℝ) ^ 2 *
        ((hahnB α N (i : ℝ) + hahnD β N (i : ℝ)) * (descPochhammer ℝ j).eval (i : ℝ)
          - hahnB α N (i : ℝ) * (descPochhammer ℝ j).eval ((i : ℝ) + 1)
          - hahnD β N (i : ℝ) * (descPochhammer ℝ j).eval ((i : ℝ) - 1)) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hL : (hahnChain α β N * hahnP α β N) i j =
      (triChain N (hahnA α β N) (hahnDg α β N) *ᵥ
        fun k : Fin (N + 1) => hahnR α β N k * (descPochhammer ℝ j).eval (k : ℝ)) i := rfl
  rw [hL, triChain_mulVec_nat N _ _ (hahnA_neg_one α β N) (hahnA_top α β N)
    (fun n : ℕ => hahnR α β N n * (descPochhammer ℝ (j : ℕ)).eval (n : ℝ)) i]
  have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.2
  have hu := hahn_link_up hα hβ hi
  have hd := hahn_link_down hα hβ hi
  have huj : hahnA α β N (i : ℕ) * (hahnR α β N ((i : ℕ) + 1) *
        (descPochhammer ℝ (j : ℕ)).eval ((((i : ℕ) + 1 : ℕ)) : ℝ)) =
      -(hahnB α N (i : ℝ) / (N : ℝ) ^ 2) * hahnR α β N i *
        (descPochhammer ℝ (j : ℕ)).eval ((i : ℝ) + 1) := by
    push_cast
    linear_combination ((descPochhammer ℝ (j : ℕ)).eval ((i : ℝ) + 1)) * hu
  have hdj : hahnA α β N (((i : ℕ) : ℤ) - 1) * (hahnR α β N ((i : ℕ) - 1) *
        (descPochhammer ℝ (j : ℕ)).eval ((((i : ℕ) - 1 : ℕ)) : ℝ)) =
      -(hahnD β N (i : ℝ) / (N : ℝ) ^ 2) * hahnR α β N i *
        (descPochhammer ℝ (j : ℕ)).eval ((i : ℝ) - 1) := by
    rcases hi0 : (i : ℕ) with _ | m
    · simp [hahnA_neg_one, hahnD]
    · have hm : ((m + 1 - 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
      rw [hm]
      have := hd
      rw [hi0] at this
      linear_combination ((descPochhammer ℝ (j : ℕ)).eval (((m + 1 : ℕ) : ℝ) - 1)) * this
  rw [hahnDg_nat]
  linear_combination huj + hdj

theorem hahn_chain_mul_P (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) :
    hahnChain α β N * hahnP α β N = hahnP α β N * hahnT α β N := by
  ext i ⟨jn, hjn⟩
  rw [hahn_chain_mul_P_apply hα hβ hN, Matrix.mul_apply]
  rcases jn with _ | m
  · rw [Finset.sum_eq_zero]
    · simp [hahnD, hahnB]
    · intro l _
      have : hahnT α β N l ⟨0, hjn⟩ = 0 := by
        unfold hahnT
        by_cases h : l = ⟨0, hjn⟩
        · simp [h]
        · simp
      rw [this, mul_zero]
  · have hm : m < N + 1 := by omega
    rw [Finset.sum_eq_add_of_mem (⟨m + 1, hjn⟩ : Fin (N + 1)) ⟨m, hm⟩ (Finset.mem_univ _)
      (Finset.mem_univ _) (by simp [Fin.ext_iff])]
    · have hT1 : hahnT α β N ⟨m + 1, hjn⟩ ⟨m + 1, hjn⟩ =
          ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) + α + β + 1) / (N : ℝ) ^ 2 := by
        simp [hahnT]
      have hT2 : hahnT α β N ⟨m, hm⟩ ⟨m + 1, hjn⟩ =
          -(((m + 1 : ℕ) : ℝ) * (N - ((m + 1 : ℕ) : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + α)) /
            (N : ℝ) ^ 2 := by
        simp [hahnT, Fin.ext_iff]
      rw [hT1, hT2]
      have hid := hahn_poly_id α β N (i : ℝ) m
      simp only [hahnP, Matrix.of_apply]
      push_cast
      linear_combination (hahnR α β N i / (N : ℝ) ^ 2) * hid
    · intro l _ hl
      have : hahnT α β N l ⟨m + 1, hjn⟩ = 0 := by
        unfold hahnT
        have h1 : l ≠ ⟨m + 1, hjn⟩ := hl.1
        have h2 : (l : ℕ) ≠ m := fun h => hl.2 (Fin.ext h)
        simp [h1, h2]
      rw [this, mul_zero]

theorem hahnP_lowerTriangular : (hahnP α β N).IsLowerTriangular := by
  intro i j h
  have hij : i < j := OrderDual.toDual_lt_toDual.mp h
  have hij' : (i : ℕ) < j := hij
  simp [hahnP, descPochhammer_eval_coe_nat_of_lt hij']

theorem hahnT_upperTriangular : (hahnT α β N).IsUpperTriangular := by
  intro i j h
  have hji : (j : ℕ) < i := h
  have h1 : i ≠ j := fun e => by rw [e] at hji; omega
  have h2 : ¬ ((i : ℕ) + 1 = j) := by omega
  simp [hahnT, h1, h2]

theorem hahnP_det_ne_zero (hα : -1 < α) (hβ : -1 < β) : (hahnP α β N).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ hahnP_lowerTriangular]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  have hk : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.2
  have hr := hahnR_ne_zero hα hβ hk
  have hf : (descPochhammer ℝ (k : ℕ)).eval ((k : ℕ) : ℝ) ≠ 0 := by
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self]
    exact_mod_cast Nat.factorial_ne_zero _
  simpa [hahnP] using mul_ne_zero hr hf

/-- **Spectrum of the Hahn chain**: every `k(k+α+β+1)/N²`, `0 ≤ k ≤ N`, is an eigenvalue of the
paper's chain `a_n = √(B(n)D(n+1))/N²`, `b_n = (B(n)+D(n))/N²` (for all real `α, β > -1`,
`N ≥ 1`). -/
theorem hahn_hasEigenvalue (hα : -1 < α) (hβ : -1 < β) (hN : 0 < N) (k : Fin (N + 1)) :
    Module.End.HasEigenvalue (Matrix.toLin' (hahnChain α β N))
      ((k : ℝ) * (k + α + β + 1) / (N : ℝ) ^ 2) := by
  have := hasEigenvalue_of_conj_upperTriangular (hahnChain α β N) (hahnP α β N) (hahnT α β N)
    (isUnit_iff_ne_zero.mpr (hahnP_det_ne_zero hα hβ)) hahnT_upperTriangular
    (hahn_chain_mul_P hα hβ hN) k
  simpa [hahnT] using this

end Spectrum

end FormalResearch.FreeFermion
