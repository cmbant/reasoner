module

public import FormalResearch.Special.LaguerreHardEdge

/-!
# Uniqueness of the Laguerre solution up to scale (Weyl P2, `rem:Laguerre`)

Every real sequence `Ξ` satisfying the Laguerre recurrence at spectral parameter zero,
`√(n(n+p)) Ξ_{n-1} + √((n+1)(n+p+1)) Ξ_{n+1} = (2n+p+1) Ξ_n` for all `n ≥ 0` (the `n = 0` row, with the
natural-number convention `0 - 1 = 0`, reads `√(p+1) Ξ_1 = (p+1) Ξ_0`), is a scalar multiple of
`laguerreRegular p` (`Ξ_n = (Ξ_0 / Ξ^{reg}_0) Ξ^{reg}_n`), for every real `p > -1`.  Claim class: proved.
The proof is the forward induction: the coefficient of `Ξ_{n+1}` is positive.
The paper states it for `p = p_+ ∈ ℕ`; the formal statement holds for every real `p > -1`.
*Not formalised:* that the physical `3j`/`6j` edge functions solve this recurrence (`eq:3jdiff`
identification), i.e. the application of the uniqueness to the physical kernels.
-/

@[expose] public section

namespace FormalResearch.Special

/-- The forward recurrence determines a solution from its first value: a solution with `Ξ_0 = 0` is zero. -/
lemma laguerre_solution_zero (p : ℝ) (hp : -1 < p) (D : ℕ → ℝ)
    (hrec : ∀ n : ℕ, Real.sqrt ((n : ℝ) * (n + p)) * D (n - 1) +
      Real.sqrt (((n : ℝ) + 1) * (n + p + 1)) * D (n + 1) = (2 * n + p + 1) * D n)
    (h0 : D 0 = 0) (n : ℕ) : D n = 0 := by
  have hs : ∀ m : ℕ, 0 < Real.sqrt (((m : ℝ) + 1) * (m + p + 1)) := by
    intro m
    apply Real.sqrt_pos.2
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have h1 : 0 < (m : ℝ) + 1 := by linarith
    have h2 : 0 < (m : ℝ) + p + 1 := by linarith
    positivity
  have key : ∀ m : ℕ, D m = 0 ∧ D (m + 1) = 0 := by
    intro m
    induction m with
    | zero =>
      refine ⟨h0, ?_⟩
      have := hrec 0
      simp only [Nat.cast_zero, zero_mul, Real.sqrt_zero, zero_mul, zero_add, h0, mul_zero] at this
      have h1 := hs 0
      simp only [Nat.cast_zero, zero_add] at h1 this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h h1.ne'
      · exact h
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have := hrec (m + 1)
      simp only [Nat.add_sub_cancel] at this
      rw [ih.1, ih.2] at this
      simp only [mul_zero, zero_add] at this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by simpa using (hs (m + 1)).ne')
      · exact h
  exact (key n).1

/-- `rem:Laguerre`: the Laguerre recurrence has a unique solution up to scale, `laguerreRegular p`. -/
theorem laguerre_solution_unique (p : ℝ) (hp : -1 < p) (Ξ : ℕ → ℝ)
    (hrec : ∀ n : ℕ, Real.sqrt ((n : ℝ) * (n + p)) * Ξ (n - 1) +
      Real.sqrt (((n : ℝ) + 1) * (n + p + 1)) * Ξ (n + 1) = (2 * n + p + 1) * Ξ n) (n : ℕ) :
    Ξ n = Ξ 0 / laguerreRegular p 0 * laguerreRegular p n := by
  have hL0 := laguerreRegular_pos p hp 0
  set c := Ξ 0 / laguerreRegular p 0 with hc
  have := laguerre_solution_zero p hp (fun n => Ξ n - c * laguerreRegular p n)
    (by
      intro n
      have h1 := hrec n
      have h2 := laguerre_recurrence p hp n
      linear_combination h1 - c * h2)
    (by simp only [hc]; field_simp; ring) n
  linarith

/-- info: 'FormalResearch.Special.laguerre_solution_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laguerre_solution_unique

end FormalResearch.Special
