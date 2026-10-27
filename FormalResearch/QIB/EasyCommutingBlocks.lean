import Mathlib
import FormalResearch.QIB.BlockDecomp

/-!
# Commuting blocks and symmetry reduction (`prop:collapseregimes` (ii), `cor:framechirality`)

Namespace `FormalResearch.QIB`.  Claim class: **proved** (finite linear algebra; no new axiom).

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, `prop:collapseregimes` (ii)
("commuting blocks: `Tr min(A,B) = Σ_a min(a_a, b_a)` in a joint eigenbasis") and the monotonicity
step of `cor:framechirality` ("every `U(n)`-invariant test is `H`-invariant, so reducing the symmetry
cannot increase the error").

* `trMin_diagonal`: `Tr min(diag a, diag b) = Σ_i min(a_i, b_i)` for real `a, b`.
* `trMin_conj`: `Tr min` is invariant under a simultaneous unitary conjugation.
* `trMin_commuting`: for `A = U diag(a) U*`, `B = U diag(b) U*` (a joint eigenbasis),
  `Tr min(A,B) = Σ_i min(a_i,b_i)`.
* `invErr_commuting_blocks`: if in every sector the two multiplicity blocks have a joint eigenbasis
  then `P_e = ½ Σ_λ Σ_i min(a_{λi}, b_{λi})`.
* `invErr_mono`: `G₁ ⊆ G₂ → invErr G₁ a b ≤ invErr G₂ a b`.

Not formalized: item (iii) of `prop:collapseregimes` (i.i.d.-equivalent experiments, quantum Chernoff
theorem) and the Chernoff-information half of `cor:framechirality` (needs `thm:frameloss`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped MatrixOrder ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (IsEffect qf err qf_re_nonneg)

section Diagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem isHermitian_diagonal_ofReal (a : n → ℝ) :
    (Matrix.diagonal fun i => (a i : ℂ)).IsHermitian := by
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint]

theorem re_trace_mul_diagonal (X : Matrix n n ℂ) (a : n → ℝ) :
    (X * Matrix.diagonal fun i => (a i : ℂ)).trace.re = ∑ i, (X i i).re * a i := by
  rw [trace_mul_diagonal', Complex.re_sum]
  simp [Complex.mul_re]

theorem effect_diag_bounds {X : Matrix n n ℂ} (hX : IsEffect X) (i : n) :
    0 ≤ (X i i).re ∧ (X i i).re ≤ 1 := by
  have h0 : (0 : ℂ) ≤ X i i := hX.1.diag_nonneg
  have h1 : (0 : ℂ) ≤ (1 - X) i i := hX.2.diag_nonneg
  have h0' := (Complex.nonneg_iff.1 h0).1
  have h1' := (Complex.nonneg_iff.1 h1).1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at h1'
  exact ⟨h0', by linarith⟩

/-- **`prop:collapseregimes` (ii), diagonal form.** -/
theorem trMin_diagonal (a b : n → ℝ) :
    trMin (Matrix.diagonal fun i => (a i : ℂ)) (Matrix.diagonal fun i => (b i : ℂ)) =
      ∑ i, min (a i) (b i) := by
  have hA := isHermitian_diagonal_ofReal a
  have hB := isHermitian_diagonal_ofReal b
  have hval : ∀ X : Matrix n n ℂ,
      (X * Matrix.diagonal fun i => (a i : ℂ)).trace.re +
        ((1 - X) * Matrix.diagonal fun i => (b i : ℂ)).trace.re =
        ∑ i, ((X i i).re * a i + (1 - (X i i).re) * b i) := by
    intro X
    rw [re_trace_mul_diagonal, re_trace_mul_diagonal, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  apply le_antisymm
  · set X0 : Matrix n n ℂ := Matrix.diagonal fun i => if a i ≤ b i then (1 : ℂ) else 0 with hX0
    have hX0e : IsEffect X0 := by
      refine ⟨Matrix.posSemidef_diagonal_iff.2 fun i => by split_ifs <;> simp, ?_⟩
      have : 1 - X0 = Matrix.diagonal fun i => if a i ≤ b i then (0 : ℂ) else 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij
          by_cases hi : a i ≤ b i <;> simp [hX0, hi]
        · simp [hX0, hij]
      rw [this]
      exact Matrix.posSemidef_diagonal_iff.2 fun i => by split_ifs <;> simp
    have h := sector_ge hA hB hX0e
    rw [hval] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    by_cases hi : a i ≤ b i
    · simp [hX0, hi, min_eq_left hi]
    · simp [hX0, hi, min_eq_right (not_le.1 hi).le]
  · obtain ⟨X, hX, hv⟩ := sector_attain hA hB
    rw [hval] at hv
    rw [← hv]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h0, h1⟩ := effect_diag_bounds hX i
    set x := (X i i).re
    rcases le_total (a i) (b i) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith

end Diagonal

section Conj

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem isHermitian_conj {A : Matrix n n ℂ} (hA : A.IsHermitian) (U : Matrix n n ℂ) :
    (U * A * Uᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.eq, Matrix.mul_assoc]

theorem trace_conj_unitary (M U : Matrix n n ℂ) (h : Uᴴ * U = 1) : (U * M * Uᴴ).trace = M.trace := by
  calc (U * M * Uᴴ).trace = (U * (M * Uᴴ)).trace := by rw [Matrix.mul_assoc]
    _ = ((M * Uᴴ) * U).trace := Matrix.trace_mul_comm _ _
    _ = (M * (Uᴴ * U)).trace := by rw [Matrix.mul_assoc]
    _ = M.trace := by rw [h, Matrix.mul_one]

theorem trMin_conj_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {U : Matrix n n ℂ} (h1 : U * Uᴴ = 1) (h2 : Uᴴ * U = 1) :
    trMin (U * A * Uᴴ) (U * B * Uᴴ) ≤ trMin A B := by
  obtain ⟨X, hX, hv⟩ := sector_attain hA hB
  have hX' : IsEffect (U * X * Uᴴ) := by
    refine ⟨hX.1.mul_mul_conjTranspose_same U, ?_⟩
    have : 1 - U * X * Uᴴ = U * (1 - X) * Uᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    rw [this]
    exact hX.2.mul_mul_conjTranspose_same U
  have h := sector_ge (isHermitian_conj hA U) (isHermitian_conj hB U) hX'
  have e1 : U * X * Uᴴ * (U * A * Uᴴ) = U * (X * A) * Uᴴ := by
    calc U * X * Uᴴ * (U * A * Uᴴ) = U * X * (Uᴴ * U) * A * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * (X * A) * Uᴴ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : (1 - U * X * Uᴴ) * (U * B * Uᴴ) = U * ((1 - X) * B) * Uᴴ := by
    have : 1 - U * X * Uᴴ = U * (1 - X) * Uᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    rw [this]
    calc U * (1 - X) * Uᴴ * (U * B * Uᴴ) = U * (1 - X) * (Uᴴ * U) * B * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * ((1 - X) * B) * Uᴴ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e1, e2, trace_conj_unitary _ _ h2, trace_conj_unitary _ _ h2] at h
  linarith

/-- `Tr min` is invariant under a simultaneous unitary conjugation. -/
theorem trMin_conj {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {U : Matrix n n ℂ} (h1 : U * Uᴴ = 1) (h2 : Uᴴ * U = 1) :
    trMin (U * A * Uᴴ) (U * B * Uᴴ) = trMin A B := by
  refine le_antisymm (trMin_conj_le hA hB h1 h2) ?_
  have := trMin_conj_le (isHermitian_conj hA U) (isHermitian_conj hB U)
    (U := Uᴴ) (by rw [Matrix.conjTranspose_conjTranspose]; exact h2)
    (by rw [Matrix.conjTranspose_conjTranspose]; exact h1)
  rw [Matrix.conjTranspose_conjTranspose] at this
  have e : ∀ M : Matrix n n ℂ, Uᴴ * (U * M * Uᴴ) * U = M := by
    intro M
    calc Uᴴ * (U * M * Uᴴ) * U = (Uᴴ * U) * M * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [h2]; simp
  rwa [e, e] at this

/-- **`prop:collapseregimes` (ii).**  Commuting blocks, in a joint eigenbasis `U`:
`Tr min(A,B) = Σ_i min(a_i,b_i)`. -/
theorem trMin_commuting (a b : n → ℝ) {U : Matrix n n ℂ} (h1 : U * Uᴴ = 1) (h2 : Uᴴ * U = 1) :
    trMin (U * (Matrix.diagonal fun i => (a i : ℂ)) * Uᴴ)
        (U * (Matrix.diagonal fun i => (b i : ℂ)) * Uᴴ) = ∑ i, min (a i) (b i) :=
  (trMin_conj (isHermitian_diagonal_ofReal a) (isHermitian_diagonal_ofReal b) h1 h2).trans
    (trMin_diagonal a b)

end Conj

section Blocks

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- **`prop:collapseregimes` (ii), error form.**  If in every sector the multiplicity blocks of `a`
and `b` are simultaneously diagonalised by a unitary `U_λ`, then
`P_e = ½ Σ_λ Σ_i min(α_{λ i}, β_{λ i})`. -/
theorem invErr_commuting_blocks [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) (a b : Idx A B → ℂ) (U : ∀ l, Matrix (B l) (B l) ℂ)
    (α β : ∀ l, B l → ℝ) (h1 : ∀ l, U l * (U l)ᴴ = 1) (h2 : ∀ l, (U l)ᴴ * U l = 1)
    (ha : ∀ l, tau a l = U l * (Matrix.diagonal fun i => (α l i : ℂ)) * (U l)ᴴ)
    (hb : ∀ l, tau b l = U l * (Matrix.diagonal fun i => (β l i : ℂ)) * (U l)ᴴ) :
    invErr G a b = (1 / 2) * ∑ l, ∑ i, min (α l i) (β l i) := by
  rw [invErr_eq hG]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ha l, hb l]
  exact trMin_commuting _ _ (h1 l) (h2 l)

end Blocks

section Mono

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Monotonicity in the symmetry group** (`cor:framechirality`, first step): fewer symmetry
constraints on the test give a smaller error. -/
theorem invErr_mono {G₁ G₂ : Set (Matrix ι ι ℂ)} (h : G₁ ⊆ G₂) (a b : ι → ℂ) :
    invErr G₁ a b ≤ invErr G₂ a b := by
  unfold invErr
  have hnn : ∀ E : Matrix ι ι ℂ, IsEffect E → 0 ≤ FormalResearch.FrameFree.Helstrom.err E a b := by
    intro E hE
    unfold FormalResearch.FrameFree.Helstrom.err
    have := qf_re_nonneg hE.1 a
    have := qf_re_nonneg hE.2 b
    linarith
  have h0 : IsEffect (0 : Matrix ι ι ℂ) := ⟨Matrix.PosSemidef.zero, by simpa using Matrix.PosSemidef.one⟩
  refine csInf_le_csInf ?_ ⟨_, 0, h0, fun U _ => by simp, rfl⟩ ?_
  · refine ⟨0, ?_⟩
    rintro r ⟨E, hE, _, rfl⟩
    exact hnn E hE
  · rintro r ⟨E, hE, hc, rfl⟩
    exact ⟨E, hE, fun U hU => hc U (h hU), rfl⟩

end Mono

end FormalResearch.QIB
