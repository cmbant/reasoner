module

public import FormalResearch.FreeFermion.W1LeonardDual

/-!
# The tridiagonal relation of a Jacobi matrix and a diagonal matrix (Weyl W1, `thm:heun`)

Source: `Weyl/free_fermion/paper/parts/model.tex`, Theorem `thm:heun` and the Leonard-pair claims for
the Hahn and dual Hahn chains; machinery for `W1Hahn` and `W1RacahChain`.

A symmetric Jacobi matrix `triChain N a b` on `{0,…,N}` (diagonal `b_n`, links `a_n` between `n`
and `n+1`, with `a_{-1} = a_N = 0`) and a diagonal matrix `diag(x_n)` satisfy
`tdRel X Y γ ρ = c₂ Y² + c₁ Y + c₀` provided three **one-line coefficient identities** hold
(`tdRel_triChain`): `x_n - 2x_{n+1} + x_{n+2} = c₂`, the link identity `E1` and the diagonal
identity `E0`.  The proof extends vectors by zero to `ℤ`, where the Jacobi matrix and the
diagonal become the shift operators `Yh`, `Xh` with no boundary cases, and compares coefficients of
the five values `w(n-2), …, w(n+2)` (`tdRel_hat`).

## Not formalised

The converse (the relation forces the coefficient identities) and the general `q`-case.
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix

section Ext

variable (N : ℕ)

/-- Extension by zero of a vector on `{0,…,N}` to `ℤ`, as a linear map. -/
def extZ : (Fin (N + 1) → ℝ) →ₗ[ℝ] (ℤ → ℝ) where
  toFun v n := if h : 0 ≤ n ∧ n ≤ N then v ⟨n.toNat, by omega⟩ else 0
  map_add' u w := by
    ext n; by_cases h : 0 ≤ n ∧ n ≤ N <;> simp [h]
  map_smul' c v := by
    ext n; by_cases h : 0 ≤ n ∧ n ≤ N <;> simp [h]

theorem extZ_apply (v : Fin (N + 1) → ℝ) (n : ℤ) :
    extZ N v n = if h : 0 ≤ n ∧ n ≤ N then v ⟨n.toNat, by omega⟩ else 0 := rfl

theorem extZ_fin (v : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : extZ N v (i : ℕ) = v i := by
  have h : 0 ≤ ((i : ℕ) : ℤ) ∧ ((i : ℕ) : ℤ) ≤ N := by omega
  simp only [extZ_apply, eq_true h, ↓reduceDIte]
  simp

theorem extZ_eq_zero (v : Fin (N + 1) → ℝ) (n : ℤ) (h : ¬ (0 ≤ n ∧ n ≤ N)) : extZ N v n = 0 := by
  simp only [extZ_apply, eq_false h, ↓reduceDIte]

theorem extZ_injective : Function.Injective (extZ N) := by
  intro u w h
  funext i
  have := congrFun h (i : ℕ)
  rwa [extZ_fin, extZ_fin] at this

theorem sum_fin_eq_extZ (w : Fin (N + 1) → ℝ) (m : ℤ) :
    ∑ j : Fin (N + 1), (if (j : ℤ) = m then w j else 0) = extZ N w m := by
  by_cases h : 0 ≤ m ∧ m ≤ N
  · have hc : (((⟨m.toNat, by omega⟩ : Fin (N + 1)) : ℕ) : ℤ) = m := by simp; omega
    simp only [extZ_apply, eq_true h, ↓reduceDIte]
    rw [Finset.sum_eq_single ⟨m.toNat, by omega⟩]
    · simp only [eq_true hc, ↓reduceIte]
    · intro j _ hj
      have : (j : ℤ) ≠ m := by
        intro hjm; apply hj; ext; simp; omega
      simp [this]
    · simp
  · simp only [extZ_apply, eq_false h, ↓reduceDIte]
    apply Finset.sum_eq_zero
    intro j _
    have : (j : ℤ) ≠ m := by
      intro hjm; apply h; rw [← hjm]; constructor <;> omega
    simp [this]

end Ext

section Chain

variable (N : ℕ)

/-- The symmetric tridiagonal matrix on `{0,…,N}` with diagonal `b_n` and links `a_n` between `n` and
`n + 1`. -/
def triChain (a b : ℤ → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => if i = j then b i else if (j : ℤ) = i + 1 then a i
    else if (i : ℤ) = j + 1 then a j else 0


theorem triChain_succ (a b : ℤ → ℝ) {i j : Fin (N + 1)} (h : (j : ℕ) = i + 1) :
    triChain N a b i j = a i := by
  have h1 : i ≠ j := fun e => by rw [e] at h; omega
  have h2 : (j : ℤ) = i + 1 := by exact_mod_cast h
  simp [triChain, h1, h2]

theorem triChain_pred (a b : ℤ → ℝ) {i j : Fin (N + 1)} (h : (i : ℕ) = j + 1) :
    triChain N a b i j = a j := by
  have h1 : i ≠ j := fun e => by rw [e] at h; omega
  have h2 : ¬ (j : ℤ) = i + 1 := by omega
  have h3 : (i : ℤ) = j + 1 := by exact_mod_cast h
  simp only [triChain, Matrix.of_apply, h1, h2, ↓reduceIte]
  simp only [h3, ↓reduceIte]

theorem triChain_far (a b : ℤ → ℝ) {i j : Fin (N + 1)} (h1 : i ≠ j) (h2 : (j : ℕ) ≠ i + 1)
    (h3 : (i : ℕ) ≠ j + 1) : triChain N a b i j = 0 := by
  have h2' : ¬ (j : ℤ) = i + 1 := by omega
  have h3' : ¬ (i : ℤ) = j + 1 := by omega
  simp [triChain, h1, h2', h3']

theorem triChain_diag (a b : ℤ → ℝ) (i : Fin (N + 1)) : triChain N a b i i = b i := by
  simp [triChain]

/-- A symmetric tridiagonal matrix with nonzero links `a_n` (`n < N`) is irreducible tridiagonal. -/
theorem triChain_irreducible (a b : ℤ → ℝ) (hapos : ∀ m : ℕ, m < N → a m ≠ 0) :
    IsIrreducibleTridiag (triChain N a b) := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h2 h3
    exact hij (triChain_far N _ _ h1 (fun h => h2 h.symm) (fun h => h3 h.symm))
  · simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hij
    have hi : (i : ℕ) < N := by have := j.2; omega
    exact ⟨by rw [triChain_succ N _ _ hij.symm]; exact hapos i hi,
      by rw [triChain_pred N _ _ hij.symm]; exact hapos i hi⟩

/-- The Jacobi operator on `ℤ`-sequences. -/
def Yh (a b : ℤ → ℝ) : (ℤ → ℝ) →ₗ[ℝ] (ℤ → ℝ) where
  toFun w n := b n * w n + a n * w (n + 1) + a (n - 1) * w (n - 1)
  map_add' u w := by ext n; simp only [Pi.add_apply]; ring
  map_smul' c w := by ext n; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The diagonal operator on `ℤ`-sequences. -/
def Xh (x : ℤ → ℝ) : (ℤ → ℝ) →ₗ[ℝ] (ℤ → ℝ) where
  toFun w n := x n * w n
  map_add' u w := by ext n; simp only [Pi.add_apply]; ring
  map_smul' c w := by ext n; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem Yh_apply (a b : ℤ → ℝ) (w : ℤ → ℝ) (n : ℤ) :
    Yh a b w n = b n * w n + a n * w (n + 1) + a (n - 1) * w (n - 1) := rfl

theorem Xh_apply (x : ℤ → ℝ) (w : ℤ → ℝ) (n : ℤ) : Xh x w n = x n * w n := rfl

/-- The zero extension intertwines the Jacobi matrix with `Yh`. -/
theorem extZ_triChain (a b : ℤ → ℝ) (ha1 : a (-1) = 0) (haN : a N = 0)
    (v : Fin (N + 1) → ℝ) :
    extZ N (Matrix.toLin' (triChain N a b) v) = Yh a b (extZ N v) := by
  funext n
  rw [Yh_apply]
  by_cases hn : 0 ≤ n ∧ n ≤ N
  · obtain ⟨i, rfl⟩ : ∃ i : Fin (N + 1), (i : ℤ) = n := ⟨⟨n.toNat, by omega⟩, by simp; omega⟩
    rw [extZ_fin N _ i, extZ_fin N v i]
    have hrow : ∀ j : Fin (N + 1), triChain N a b i j * v j =
        (if i = j then b i * v j else 0) + (if (j : ℤ) = i + 1 then a i * v j else 0) +
          (if (j : ℤ) = i - 1 then a (i - 1) * v j else 0) := by
      intro j
      unfold triChain
      simp only [Matrix.of_apply]
      by_cases h1 : i = j
      · have hc : ((j : ℕ) : ℤ) = (i : ℕ) := by rw [h1]
        have e1 : ¬ ((j : ℕ) : ℤ) = (i : ℕ) + 1 := by omega
        have e2 : ¬ ((j : ℕ) : ℤ) = (i : ℕ) - 1 := by omega
        simp only [eq_true h1, eq_false e1, eq_false e2, ↓reduceIte]
        ring
      · have h1' : ((i : ℕ) : ℤ) ≠ (j : ℕ) := fun h => h1 (Fin.ext (by exact_mod_cast h))
        by_cases h2 : ((j : ℕ) : ℤ) = (i : ℕ) + 1
        · have e : ¬ ((j : ℕ) : ℤ) = (i : ℕ) - 1 := by omega
          simp only [eq_false h1, eq_true h2, eq_false e, ↓reduceIte]
          ring
        · by_cases h3 : ((i : ℕ) : ℤ) = (j : ℕ) + 1
          · have h3' : ((j : ℕ) : ℤ) = (i : ℕ) - 1 := by omega
            simp only [eq_false h1, eq_false h2, eq_true h3, eq_true h3', ↓reduceIte]
            rw [h3']
            ring
          · have e : ¬ ((j : ℕ) : ℤ) = (i : ℕ) - 1 := by omega
            simp only [eq_false h1, eq_false h2, eq_false h3, eq_false e, ↓reduceIte]
            ring
    rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    simp only [hrow, Finset.sum_add_distrib]
    rw [show (∑ j : Fin (N + 1), (if i = j then b i * v j else 0)) = b i * v i by simp]
    have hs1 : (∑ j : Fin (N + 1), (if (j : ℤ) = i + 1 then a i * v j else 0)) =
        a i * extZ N v (i + 1) := by
      rw [← sum_fin_eq_extZ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    have hs2 : (∑ j : Fin (N + 1), (if (j : ℤ) = i - 1 then a (i - 1) * v j else 0)) =
        a (i - 1) * extZ N v (i - 1) := by
      rw [← sum_fin_eq_extZ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [hs1, hs2]
  · rw [extZ_eq_zero N _ n hn]
    have h0 : n = -1 ∨ n = N + 1 ∨ n < -1 ∨ n > N + 1 := by omega
    rcases h0 with rfl | rfl | h | h
    · rw [ha1, extZ_eq_zero N v (-1) hn, extZ_eq_zero N v (-1 - 1) (by omega)]; simp
    · rw [extZ_eq_zero N v _ hn, extZ_eq_zero N v (N + 1 + 1) (by omega), show (N : ℤ) + 1 - 1 = N by ring,
        haN]; simp
    · rw [extZ_eq_zero N v n hn, extZ_eq_zero N v (n + 1) (by omega),
        extZ_eq_zero N v (n - 1) (by omega)]; simp
    · rw [extZ_eq_zero N v n hn, extZ_eq_zero N v (n + 1) (by omega),
        extZ_eq_zero N v (n - 1) (by omega)]; simp

/-- The zero extension intertwines a diagonal matrix with `Xh`. -/
theorem extZ_diagonal (x : ℤ → ℝ) (v : Fin (N + 1) → ℝ) :
    extZ N (Matrix.toLin' (Matrix.diagonal fun i : Fin (N + 1) => x i) v) = Xh x (extZ N v) := by
  funext n
  rw [Xh_apply]
  by_cases hn : 0 ≤ n ∧ n ≤ N
  · obtain ⟨i, rfl⟩ : ∃ i : Fin (N + 1), (i : ℤ) = n := ⟨⟨n.toNat, by omega⟩, by simp; omega⟩
    rw [extZ_fin, extZ_fin]
    simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  · rw [extZ_eq_zero N _ n hn, extZ_eq_zero N v n hn]; simp

end Chain

section Relation

/-- Pointwise form of the tridiagonal relation for the shift operators on `ℤ`-sequences. -/
theorem tdRel_hat (a b x : ℤ → ℝ) (γ ρ c₂ c₁ c₀ : ℝ)
    (hE2 : ∀ n, x n - 2 * x (n + 1) + x (n + 2) - c₂ = 0)
    (hE1 : ∀ n, a n * ((x (n + 1) - x n) * (b n - b (n + 1)) - γ * (x (n + 1) + x n) -
      c₂ * (b n + b (n + 1)) - c₁) = 0) (n : ℤ)
    (hE0 : a n ^ 2 * (2 * x n - 2 * x (n + 1)) + a (n - 1) ^ 2 * (2 * x n - 2 * x (n - 1)) -
      2 * γ * x n * b n - ρ * x n - c₂ * (a n ^ 2 + a (n - 1) ^ 2 + b n ^ 2) - c₁ * b n - c₀ = 0)
    (w : ℤ → ℝ) :
    tdRel (Xh x) (Yh a b) γ ρ w n =
      (c₂ • (Yh a b * Yh a b) + c₁ • Yh a b + c₀ • (1 : (ℤ → ℝ) →ₗ[ℝ] (ℤ → ℝ))) w n := by
  simp only [tdRel, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.one_apply, Yh_apply, Xh_apply, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, add_sub_cancel_right, sub_add_cancel]
  have e1 : n + 1 + 1 = n + 2 := by ring
  have e2 : n - 1 - 1 = n - 2 := by ring
  simp only [e1, e2]
  have h2 := hE2 n
  have h2' := hE2 (n - 2)
  have h1 := hE1 n
  have h1' := hE1 (n - 1)
  rw [show n - 2 + 1 = n - 1 by ring, show n - 2 + 2 = n by ring] at h2'
  rw [show n - 1 + 1 = n by ring] at h1'
  linear_combination (w (n + 2) * a n * a (n + 1)) * h2 + w (n + 1) * h1 + w (n - 1) * h1' +
    (w (n - 2) * a (n - 1) * a (n - 2)) * h2' + w n * hE0

/-- **The tridiagonal relation of a Jacobi matrix and a diagonal matrix** on `{0,…,N}`: from the
coefficient identities `hE2`, `hE1`, `hE0` (for `0 ≤ n ≤ N`), the matrices of `X = diag(x_n)` and
`Y = triChain N a b` satisfy `tdRel X Y γ ρ = c₂ Y² + c₁ Y + c₀`. -/
theorem tdRel_triChain (N : ℕ) (a b x : ℤ → ℝ) (ha1 : a (-1) = 0) (haN : a N = 0)
    (γ ρ c₂ c₁ c₀ : ℝ)
    (hE2 : ∀ n, x n - 2 * x (n + 1) + x (n + 2) - c₂ = 0)
    (hE1 : ∀ n, a n * ((x (n + 1) - x n) * (b n - b (n + 1)) - γ * (x (n + 1) + x n) -
      c₂ * (b n + b (n + 1)) - c₁) = 0)
    (hE0 : ∀ n : ℤ, 0 ≤ n → n ≤ N →
      a n ^ 2 * (2 * x n - 2 * x (n + 1)) + a (n - 1) ^ 2 * (2 * x n - 2 * x (n - 1)) -
        2 * γ * x n * b n - ρ * x n - c₂ * (a n ^ 2 + a (n - 1) ^ 2 + b n ^ 2) - c₁ * b n -
        c₀ = 0) :
    tdRel (Matrix.toLin' (Matrix.diagonal fun i : Fin (N + 1) => x i))
        (Matrix.toLin' (triChain N a b)) γ ρ =
      c₂ • (Matrix.toLin' (triChain N a b) * Matrix.toLin' (triChain N a b)) +
        c₁ • Matrix.toLin' (triChain N a b) + c₀ • 1 := by
  apply LinearMap.ext
  intro v
  apply extZ_injective N
  funext n
  by_cases hn : 0 ≤ n ∧ n ≤ N
  swap
  · rw [extZ_eq_zero N _ n hn, extZ_eq_zero N _ n hn]
  have hY : ∀ w, extZ N (Matrix.toLin' (triChain N a b) w) = Yh a b (extZ N w) :=
    fun w => extZ_triChain N a b ha1 haN w
  have hX : ∀ w, extZ N (Matrix.toLin' (Matrix.diagonal fun i : Fin (N + 1) => x i) w) =
      Xh x (extZ N w) := fun w => extZ_diagonal N x w
  have := tdRel_hat a b x γ ρ c₂ c₁ c₀ hE2 hE1 n (hE0 n hn.1 hn.2) (extZ N v)
  simp only [tdRel, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.one_apply, map_sub, map_add, map_smul, hY, hX,
    Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at this ⊢
  exact this

end Relation

end FormalResearch.FreeFermion
