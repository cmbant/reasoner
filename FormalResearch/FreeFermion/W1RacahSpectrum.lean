module

public import FormalResearch.FreeFermion.W1HahnSpectrum

/-!
# The folded squared-spin chain: definitions and spectrum (Weyl W1, `cor:racahheun`)

Source: `Weyl/free_fermion/notes/racah_chain.tex`, `sec:racahchain` (`eq:model`), `lem:duality`,
`cor:racahheun`: on `ℓ²{0, 2, …, L}`, `L = 2M`, `Λ = L(L+1)`,
`X_qq = q²`, `Y_qq = (Λ - q²)/2`, `Y_{q,q+2} = y_o(q) = ¼√((L-q)(L-q-1)(L+q+1)(L+q+2))`
(`q ≥ 2`), `Y_{0,2} = √2 y_o(0)`; "both spectra are `{r² : r = 0, 2, …, L}`".

With the index `j = q/2 ∈ {0, …, M}`:

* `racChain M` : the symmetric tridiagonal matrix `Y` (`triChain`), `racX M = diag((2j)²)`;
* `racChain_hasEigenvalue` : **the spectrum of `Y`**: every `(2k)²`, `0 ≤ k ≤ M`, is an eigenvalue
  (so the spectrum is exactly `{r²}`), proved by the same mechanism as `W1HahnSpectrum`:
  `Y P = P T` with `P_{jk} = r_j φ_k(j)`, `φ_k(x) = ∏_{t<k}(x² - t²)`, `r_j > 0`, `T` upper
  triangular with diagonal `4(M-k)²`.  The key identity `rac_poly_id` is the bidiagonality of the
  (folded) Racah difference operator on the basis `φ_k`:
  `(b φ_k + B̂ φ_k(·+1) + D̂ φ_k(·-1)) = 4(M-k)² φ_k + k(2k-1)(2M-2k+1)(M-k+1) φ_{k-1}`, proved
  at the level of polynomials by the shift relations `rac_shift_up`, `rac_shift_down`.
  The `√2` boundary link is exactly the reflection `φ_k(-1) = φ_k(1)`, `B̂(0) = D̂(0)`.

## Not formalised

The identification of `Y` with `K_x²` on the even symmetric subspace of spin `L` and the
Wigner-`d` involution of `lem:duality` (the duality is proved instead from the tridiagonal relation,
`W1RacahChain`).
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix Module Polynomial

section Defs

variable (M : ℕ)

/-- `Λ = L(L+1)` with `L = 2M`. -/
noncomputable def racLam : ℝ := 2 * M * (2 * M + 1)

/-- `B̂(x) = (M-x)(2M-2x-1)/2` (nonsymmetric upward coefficient of the folded chain). -/
noncomputable def racBh (x : ℝ) : ℝ := (M - x) * (2 * M - 2 * x - 1) / 2

/-- `D̂(x) = (M+x)(2M+2x-1)/2` (nonsymmetric downward coefficient). -/
noncomputable def racDh (x : ℝ) : ℝ := (M + x) * (2 * M + 2 * x - 1) / 2

/-- The diagonal `b(x) = (Λ - 4x²)/2 = (Λ - q²)/2`, `q = 2x`. -/
noncomputable def racb (x : ℝ) : ℝ := (racLam M - 4 * x ^ 2) / 2

/-- `16 y_o(2x)² = (L-q)(L-q-1)(L+q+1)(L+q+2)` with `L = 2M`, `q = 2x`. -/
noncomputable def racQ (x : ℝ) : ℝ :=
  (2 * M - 2 * x) * (2 * M - 2 * x - 1) * (2 * M + 2 * x + 1) * (2 * M + 2 * x + 2)

/-- The link `Y_{q,q+2}`, `q = 2n`: `y_o(q) = ¼√Q` for `n ≥ 1`, `√2 y_o(0)` for `n = 0`, and `0` for
`n < 0`. -/
noncomputable def racA (n : ℤ) : ℝ :=
  if n < 0 then 0 else (if n = 0 then √2 else 1) * (√(racQ M n) / 4)

/-- The diagonal as a function on `ℤ`. -/
noncomputable def racDg (n : ℤ) : ℝ := racb M n

/-- The position `x_n = q² = (2n)²`. -/
noncomputable def racPos (n : ℤ) : ℝ := 4 * (n : ℝ) ^ 2

/-- The folded squared-spin chain `Y` of `eq:model`. -/
noncomputable def racChain : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  triChain M (racA M) (racDg M)

/-- The position operator `X = diag(q²)`. -/
noncomputable def racX : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  Matrix.diagonal fun n : Fin (M + 1) => racPos n

variable {M}

theorem racA_neg_one : racA M (-1) = 0 := by simp [racA]

theorem racA_top : racA M M = 0 := by
  simp [racA, racQ]

theorem racQ_pos {n : ℕ} (hn : n < M) : 0 < racQ M n := by
  have h1 : (n : ℝ) + 1 ≤ M := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold racQ
  have : 0 < (2 * (M : ℝ) - 2 * n) := by linarith
  have : 0 < (2 * (M : ℝ) - 2 * n - 1) := by linarith
  have : 0 < (2 * (M : ℝ) + 2 * n + 1) := by linarith
  have : 0 < (2 * (M : ℝ) + 2 * n + 2) := by linarith
  positivity

theorem racQ_nonneg {n : ℕ} (hn : n ≤ M) : 0 ≤ racQ M n := by
  rcases hn.lt_or_eq with h | rfl
  · exact (racQ_pos h).le
  · simp [racQ]

theorem racA_nat_pos {n : ℕ} (hn : n < M) : 0 < racA M n := by
  have hs : 0 < √(racQ M n) := Real.sqrt_pos.mpr (racQ_pos hn)
  have key : 0 < √(racQ M n) / 4 := div_pos hs (by norm_num)
  unfold racA
  simp only [Int.natCast_nonneg, not_lt.mpr, ↓reduceIte, Int.cast_natCast]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.cast_zero, ↓reduceIte] at key ⊢
    exact mul_pos (Real.sqrt_pos.mpr two_pos) key
  · have : ((n : ℤ) = 0) = False := by simp; omega
    simp only [this, ↓reduceIte, one_mul]
    exact key

/-- `a_n² = c_n Q(n)/16` for `0 ≤ n ≤ M`, `c_0 = 2`, `c_n = 1` otherwise. -/
theorem racA_sq {n : ℤ} (h0 : 0 ≤ n) (hn : n ≤ M) :
    racA M n ^ 2 = (if n = 0 then 2 else 1) * racQ M n / 16 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := Int.eq_ofNat_of_zero_le h0
  have hq : 0 ≤ racQ M (m : ℝ) := racQ_nonneg (by omega)
  unfold racA
  simp only [Int.natCast_nonneg, not_lt.mpr, ↓reduceIte]
  split_ifs with h
  · rw [mul_pow, div_pow, Real.sq_sqrt (by simp), Real.sq_sqrt (by simpa using hq)]
    ring
  · rw [one_mul, div_pow, Real.sq_sqrt (by simpa using hq)]
    ring

end Defs

section Poly

/-- `φ_i(x) = ∏_{t<i} (x² - t²)`. -/
noncomputable def racPhi : ℕ → ℝ[X]
  | 0 => 1
  | i + 1 => racPhi i * (X ^ 2 - (i : ℝ[X]) ^ 2)

theorem eval_racPhi_succ (i : ℕ) (x : ℝ) :
    (racPhi (i + 1)).eval x = (racPhi i).eval x * (x ^ 2 - (i : ℝ) ^ 2) := by
  simp [racPhi]

theorem eval_racPhi_neg (i : ℕ) (x : ℝ) : (racPhi i).eval (-x) = (racPhi i).eval x := by
  induction i with
  | zero => simp [racPhi]
  | succ i ih => rw [eval_racPhi_succ, eval_racPhi_succ, ih]; ring

theorem eval_racPhi_nat_of_lt {i k : ℕ} (h : k < i) : (racPhi i).eval (k : ℝ) = 0 := by
  induction i with
  | zero => omega
  | succ i ih =>
    rw [eval_racPhi_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · rw [ih h', zero_mul]
    · simp

theorem eval_racPhi_nat_ne {i k : ℕ} (h : i ≤ k) : (racPhi i).eval (k : ℝ) ≠ 0 := by
  induction i with
  | zero => simp [racPhi]
  | succ i ih =>
    rw [eval_racPhi_succ]
    refine mul_ne_zero (ih (by omega)) ?_
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast h
    have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith

/-- Shift relation `x (x-i+1) φ_i(x+1) = (x+1)(x+i) φ_i(x)`. -/
theorem rac_shift_up (i : ℕ) :
    X * (X - (i : ℝ[X]) + 1) * (racPhi i).comp (X + 1) = (X + 1) * (X + (i : ℝ[X])) * racPhi i := by
  induction i with
  | zero => simp [racPhi]; ring
  | succ i ih =>
    have hc : (racPhi (i + 1)).comp (X + 1) =
        (racPhi i).comp (X + 1) * ((X + 1) ^ 2 - (i : ℝ[X]) ^ 2) := by
      simp [racPhi, mul_comp]
    rw [hc]
    simp only [racPhi, Nat.cast_succ]
    linear_combination (X - (i : ℝ[X])) * (X + (i : ℝ[X]) + 1) * ih

/-- Shift relation `x (x+i-1) φ_i(x-1) = (x-i)(x-1) φ_i(x)`. -/
theorem rac_shift_down (i : ℕ) :
    X * (X + (i : ℝ[X]) - 1) * (racPhi i).comp (X - 1) = (X - (i : ℝ[X])) * (X - 1) * racPhi i := by
  induction i with
  | zero => simp [racPhi]
  | succ i ih =>
    have hc : (racPhi (i + 1)).comp (X - 1) =
        (racPhi i).comp (X - 1) * ((X - 1) ^ 2 - (i : ℝ[X]) ^ 2) := by
      simp [racPhi, mul_comp]
    rw [hc]
    simp only [racPhi, Nat.cast_succ]
    linear_combination (X + (i : ℝ[X])) * (X - (i : ℝ[X]) - 1) * ih

/-- Bidiagonality of the folded Racah operator on `φ_{m+1}`, at the level of polynomials. -/
theorem rac_poly_core (M m : ℕ) :
    (2 * (M : ℝ[X]) * (2 * (M : ℝ[X]) + 1) - 4 * X ^ 2) * racPhi (m + 1) +
      ((M : ℝ[X]) - X) * (2 * (M : ℝ[X]) - 2 * X - 1) * (racPhi (m + 1)).comp (X + 1) +
      ((M : ℝ[X]) + X) * (2 * (M : ℝ[X]) + 2 * X - 1) * (racPhi (m + 1)).comp (X - 1) =
    8 * ((M : ℝ[X]) - (m : ℝ[X]) - 1) ^ 2 * racPhi (m + 1) +
      2 * (((m : ℝ[X]) + 1) * (2 * (m : ℝ[X]) + 1) *
        (2 * (M : ℝ[X]) - 2 * (m : ℝ[X]) - 1) * ((M : ℝ[X]) - (m : ℝ[X]))) * racPhi m := by
  have hup := rac_shift_up (m + 1)
  have hdn := rac_shift_down (m + 1)
  push_cast at hup hdn
  have hmult : (X * (X - (m : ℝ[X])) * (X + (m : ℝ[X]))) ≠ 0 := by
    have h1 : (X - (m : ℝ[X])) ≠ 0 := by
      rw [← map_natCast C m]; exact X_sub_C_ne_zero _
    have h2 : (X + (m : ℝ[X])) ≠ 0 := by
      rw [← map_natCast C m]; exact X_add_C_ne_zero _
    exact mul_ne_zero (mul_ne_zero X_ne_zero h1) h2
  apply mul_left_cancel₀ hmult
  have hR : racPhi (m + 1) = racPhi m * (X ^ 2 - (m : ℝ[X]) ^ 2) := rfl
  simp only [hR] at hup hdn ⊢
  linear_combination ((M : ℝ[X]) - X) * (2 * (M : ℝ[X]) - 2 * X - 1) * (X + (m : ℝ[X])) * hup +
    ((M : ℝ[X]) + X) * (2 * (M : ℝ[X]) + 2 * X - 1) * (X - (m : ℝ[X])) * hdn

/-- Real form of `rac_poly_core`: the folded Racah difference operator is bidiagonal on `φ_k`. -/
theorem rac_poly_id (M m : ℕ) (x : ℝ) :
    racb M x * (racPhi (m + 1)).eval x + racBh M x * (racPhi (m + 1)).eval (x + 1) +
        racDh M x * (racPhi (m + 1)).eval (x - 1) =
      4 * ((M : ℝ) - m - 1) ^ 2 * (racPhi (m + 1)).eval x +
        ((m + 1) * (2 * m + 1) * (2 * M - 2 * m - 1) * (M - m)) * (racPhi m).eval x := by
  have h := congrArg (Polynomial.eval x) (rac_poly_core M m)
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_natCast, eval_comp, eval_one,
    eval_ofNat] at h
  unfold racb racBh racDh racLam
  linear_combination (1 / 2) * h

theorem rac_poly_id_zero (M : ℕ) (x : ℝ) :
    racb M x + racBh M x + racDh M x = 4 * (M : ℝ) ^ 2 := by
  unfold racb racBh racDh racLam
  ring

end Poly

section Spectrum

variable {M : ℕ}

/-- The conjugating diagonal: `r_0 = 1`, `r_{n+1} = B̂_f(n) r_n / a_n`, where `B̂_f(0) = 2 B̂(0)`. -/
noncomputable def racR (M : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => racBh M n * (if n = 0 then 2 else 1) * racR M n / racA M n

theorem racBh_pos {n : ℕ} (hn : n < M) : 0 < racBh M n := by
  have h1 : (n : ℝ) + 1 ≤ M := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold racBh
  have : 0 < (M : ℝ) - n := by linarith
  have : 0 < 2 * (M : ℝ) - 2 * n - 1 := by linarith
  positivity

theorem racR_pos {n : ℕ} (hn : n ≤ M) : 0 < racR M n := by
  induction n with
  | zero => simp [racR]
  | succ n ih =>
    have hlt : n < M := hn
    simp only [racR]
    have := racBh_pos hlt
    have := racA_nat_pos hlt
    have := ih hlt.le
    split_ifs <;> positivity

/-- `a_n r_{n+1} = B̂_f(n) r_n` for `n ≤ M`. -/
theorem rac_link_up {n : ℕ} (hn : n ≤ M) :
    racA M n * racR M (n + 1) = racBh M n * (if n = 0 then 2 else 1) * racR M n := by
  rcases hn.lt_or_eq with hlt | rfl
  · have hA := (racA_nat_pos hlt).ne'
    simp only [racR]
    field_simp
  · simp [racA_top, racBh]

/-- `D̂(n) r_n = a_{n-1} r_{n-1}` for `1 ≤ n ≤ M`. -/
theorem rac_link_down {m : ℕ} (hm : m + 1 ≤ M) :
    racA M (m : ℤ) * racR M m = racDh M ((m + 1 : ℕ) : ℝ) * racR M (m + 1) := by
  have hlt : m < M := hm
  have hA := (racA_nat_pos hlt).ne'
  have hsq := racA_sq (M := M) (n := (m : ℤ)) (by omega) (by omega)
  have hq : racQ M ((m : ℤ) : ℝ) / 16 = racBh M m * racDh M ((m : ℝ) + 1) := by
    simp only [Int.cast_natCast]; unfold racQ racBh racDh; ring
  simp only [racR]
  rw [← mul_div_assoc, eq_div_iff hA]
  push_cast
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp only [Nat.cast_zero, Int.cast_zero, zero_add, ↓reduceIte] at hsq hq ⊢
    linear_combination (racR M 0) * hsq + 2 * (racR M 0) * hq
  · have h0 : ¬ ((m : ℤ) = 0) := by omega
    have h0' : ¬ (m = 0) := by omega
    simp only [h0, h0', ↓reduceIte] at hsq ⊢
    linear_combination (racR M m) * hsq + (racR M m) * hq

/-- The conjugating matrix `P_{kj} = r_k φ_j(k)`. -/
noncomputable def racP (M : ℕ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  Matrix.of fun k j => racR M k * (racPhi j).eval (k : ℝ)

/-- The upper triangular (bidiagonal) model. -/
noncomputable def racT (M : ℕ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  Matrix.of fun l j => if l = j then 4 * ((M : ℝ) - j) ^ 2
    else if (l : ℕ) + 1 = j then (j : ℝ) * (2 * j - 1) * (2 * M - 2 * j + 1) * (M - j + 1) else 0

/-- The `j`-th column of `racChain · P`: the folded Racah operator applied to `φ_j`. -/
theorem rac_chain_mul_P_apply (i j : Fin (M + 1)) :
    (racChain M * racP M) i j = racR M i * (racb M (i : ℝ) * (racPhi j).eval (i : ℝ) +
      racBh M (i : ℝ) * (racPhi j).eval ((i : ℝ) + 1) +
        racDh M (i : ℝ) * (racPhi j).eval ((i : ℝ) - 1)) := by
  have hL : (racChain M * racP M) i j =
      (triChain M (racA M) (racDg M) *ᵥ
        fun k : Fin (M + 1) => racR M k * (racPhi j).eval (k : ℝ)) i := rfl
  rw [hL, triChain_mulVec_nat M _ _ racA_neg_one racA_top
    (fun n : ℕ => racR M n * (racPhi (j : ℕ)).eval (n : ℝ)) i]
  have hi : (i : ℕ) ≤ M := Nat.lt_succ_iff.mp i.2
  by_cases hz : (i : ℕ) = 0
  · rw [hz]
    have hu : racA M ((0 : ℕ) : ℤ) * racR M (0 + 1) = racBh M ((0 : ℕ) : ℝ) * 2 * racR M 0 := by
      have := rac_link_up (M := M) (n := 0) (by omega)
      simpa using this
    have hB0 : racBh M 0 = racDh M 0 := by unfold racBh racDh; ring
    have hφ : (racPhi j).eval ((0 : ℝ) - 1) = (racPhi j).eval (0 + 1) := by
      rw [zero_sub, zero_add, eval_racPhi_neg]
    simp only [racDg, Nat.cast_zero, Int.cast_zero, zero_add, zero_sub] at hu hφ ⊢
    rw [racA_neg_one, zero_mul, add_zero, hφ]
    simp only [Nat.cast_one]
    linear_combination ((racPhi j).eval 1) * hu + (((racPhi j).eval 1) * racR M 0) * hB0
  · obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨(i : ℕ) - 1, by omega⟩
    rw [hm]
    have hu := rac_link_up (M := M) (n := m + 1) (by omega)
    have hd := rac_link_down (M := M) (m := m) (by omega)
    have hne : ¬ (m + 1 = 0) := by omega
    simp only [hne, ↓reduceIte, mul_one] at hu
    simp only [racDg, Nat.add_sub_cancel]
    push_cast at hu hd ⊢
    have e1 : (m : ℤ) + 1 - 1 = m := by ring
    rw [e1]
    have e2 : (m : ℝ) + 1 - 1 = m := by ring
    rw [e2]
    linear_combination ((racPhi j).eval ((m : ℝ) + 1 + 1)) * hu + ((racPhi j).eval (m : ℝ)) * hd

theorem rac_chain_mul_P : racChain M * racP M = racP M * racT M := by
  ext i ⟨jn, hjn⟩
  rw [rac_chain_mul_P_apply, Matrix.mul_apply]
  rcases jn with _ | m
  · rw [Finset.sum_eq_single (⟨0, hjn⟩ : Fin (M + 1))]
    · have : racT M ⟨0, hjn⟩ ⟨0, hjn⟩ = 4 * (M : ℝ) ^ 2 := by simp [racT]
      rw [this]
      simp only [racP, Matrix.of_apply, racPhi, eval_one]
      linear_combination (racR M i) * (rac_poly_id_zero M (i : ℝ))
    · intro l _ hl
      have : racT M l ⟨0, hjn⟩ = 0 := by
        have h2 : ¬ ((l : ℕ) + 1 = ((⟨0, hjn⟩ : Fin (M + 1)) : ℕ)) := by simp
        simp only [racT, Matrix.of_apply, eq_false hl, eq_false h2, ↓reduceIte]
      rw [this, mul_zero]
    · simp
  · have hm : m < M + 1 := by omega
    rw [Finset.sum_eq_add_of_mem (⟨m + 1, hjn⟩ : Fin (M + 1)) ⟨m, hm⟩ (Finset.mem_univ _)
      (Finset.mem_univ _) (by simp [Fin.ext_iff])]
    · have hT1 : racT M ⟨m + 1, hjn⟩ ⟨m + 1, hjn⟩ = 4 * ((M : ℝ) - ((m + 1 : ℕ) : ℝ)) ^ 2 := by
        simp [racT]
      have hT2 : racT M ⟨m, hm⟩ ⟨m + 1, hjn⟩ =
          ((m + 1 : ℕ) : ℝ) * (2 * ((m + 1 : ℕ) : ℝ) - 1) * (2 * M - 2 * ((m + 1 : ℕ) : ℝ) + 1) *
            (M - ((m + 1 : ℕ) : ℝ) + 1) := by
        simp [racT, Fin.ext_iff]
      rw [hT1, hT2]
      have hid := rac_poly_id M m (i : ℝ)
      simp only [racP, Matrix.of_apply]
      push_cast
      linear_combination (racR M i) * hid
    · intro l _ hl
      have : racT M l ⟨m + 1, hjn⟩ = 0 := by
        unfold racT
        have h1 : l ≠ ⟨m + 1, hjn⟩ := hl.1
        have h2 : (l : ℕ) ≠ m := fun h => hl.2 (Fin.ext h)
        simp [h1, h2]
      rw [this, mul_zero]

theorem racP_lowerTriangular : (racP M).IsLowerTriangular := by
  intro i j h
  have hij : i < j := OrderDual.toDual_lt_toDual.mp h
  have hij' : (i : ℕ) < j := hij
  simp [racP, eval_racPhi_nat_of_lt hij']

theorem racT_upperTriangular : (racT M).IsUpperTriangular := by
  intro i j h
  have hji : (j : ℕ) < i := h
  have h1 : i ≠ j := fun e => by rw [e] at hji; omega
  have h2 : ¬ ((i : ℕ) + 1 = j) := by omega
  simp [racT, h1, h2]

theorem racP_det_ne_zero : (racP M).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ racP_lowerTriangular]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  have hk : (k : ℕ) ≤ M := Nat.lt_succ_iff.mp k.2
  have hr := (racR_pos hk).ne'
  simpa [racP] using mul_ne_zero hr (eval_racPhi_nat_ne (le_refl (k : ℕ)))

/-- **Spectrum of the folded squared-spin chain**: every `(2k)² = r²`, `r = 2k`, `0 ≤ k ≤ M`, is
an eigenvalue of `Y` (`eq:model`), for every `M`. -/
theorem racChain_hasEigenvalue (k : Fin (M + 1)) :
    Module.End.HasEigenvalue (Matrix.toLin' (racChain M)) (4 * (k : ℝ) ^ 2) := by
  have := hasEigenvalue_of_conj_upperTriangular (racChain M) (racP M) (racT M)
    (isUnit_iff_ne_zero.mpr racP_det_ne_zero) racT_upperTriangular rac_chain_mul_P k.rev
  have hk : (k : ℕ) ≤ M := Nat.lt_succ_iff.mp k.2
  have hrev : (((k.rev : Fin (M + 1)) : ℕ) : ℝ) = (M : ℝ) - k := by
    rw [Fin.val_rev]
    rw [show M + 1 - (k + 1) = M - k by omega, Nat.cast_sub hk]
  simp only [racT, Matrix.of_apply, ↓reduceIte, hrev] at this
  convert this using 2
  ring

end Spectrum

end FormalResearch.FreeFermion
