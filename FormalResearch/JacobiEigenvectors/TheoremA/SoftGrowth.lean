module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Engine.Casoratian

/-!
# Paper J, Layer 2 (L2.C6, R4): the growth of the exact solution on the left forbidden side (`eq:tha-S4grow`)

Source: Paper J `app_thmA.tex` Step 3 (i) (`eq:tha-S4grow`: "by induction from `psi^L_{-1} = 0 < psi^L_0`: if `0 <= psi^L_{n-1} <= psi^L_n`, then
`a_n psi^L_{n+1} = (X - B_n) psi^L_n - a_{n-1} psi^L_{n-1} >= (a_n + nu_1/2) psi^L_n`"; "this uses only the recurrence and `psi^L_0 > 0`").

## Proved here (generic statements about a three-term recurrence `Lop A Q f = 0`)

* `exists_seeded`: if `A_n != 0` for `0 <= n < N_R`, every seed `s` has a solution `psi` of the recurrence on the rows `0 <= n < N_R` with `psi_0 = s`.
* `growth_ratio`: if on `0 <= n <= n_1` one has `0 < A_n <= C_A`, `Q_n >= A_n + A_{n-1} + nu` (`nu > 0`), `A_{-1} = 0`, and `f` solves the recurrence there with `f_0 > 0`, then
  `f_n > 0` and `f_{n+1} >= (1 + nu/C_A) f_n` for `0 <= n <= n_1`.

## Differences from the paper

The paper takes `nu_1/2`; here the margin is the whole `nu` of the hypothesis (`SoftEdgeChart.grow_gap`).  Nothing else is changed.

## Not formalised

The derivation of the margin `X - B_n >= a_n + a_{n-1} + nu` from the geometry (`lem:tha-geom` (d)): it is the chart field `SoftEdgeChart.grow_gap`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Engine

/-- the pair `(f_{n-1}, f_n)` of the seeded recursion. -/
def seedPair (A Q : ℤ → ℝ) (s : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, s)
  | n + 1 => ((seedPair A Q s n).2, (Q n * (seedPair A Q s n).2 - A ((n : ℤ) - 1) * (seedPair A Q s n).1) / A n)

/-- the seeded solution (`0` for negative indices). -/
def seedSol (A Q : ℤ → ℝ) (s : ℝ) (k : ℤ) : ℝ := if k < 0 then 0 else (seedPair A Q s k.toNat).2

lemma seedPair_fst (A Q : ℤ → ℝ) (s : ℝ) (n : ℕ) : (seedPair A Q s n).1 = seedSol A Q s ((n : ℤ) - 1) := by
  cases n with
  | zero => simp [seedPair, seedSol]
  | succ n =>
    have h : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
    have h0 : ¬ ((n : ℤ) < 0) := by omega
    simp [seedPair, seedSol, h0]

lemma seedSol_nat (A Q : ℤ → ℝ) (s : ℝ) (n : ℕ) : seedSol A Q s (n : ℤ) = (seedPair A Q s n).2 := by
  have h0 : ¬ ((n : ℤ) < 0) := by omega
  simp [seedSol, h0]

/-- **Existence of a seeded solution** of the recurrence on the rows `0 <= n < N_R`. -/
theorem exists_seeded (A Q : ℤ → ℝ) (NR : ℤ) (hA : ∀ n : ℤ, 0 ≤ n → n < NR → A n ≠ 0) (s : ℝ) :
    ∃ ψ : ℤ → ℝ, ψ 0 = s ∧ ∀ n : ℤ, 0 ≤ n → n < NR → Lop A Q ψ n = 0 := by
  refine ⟨seedSol A Q s, ?_, ?_⟩
  · have := seedSol_nat A Q s 0
    simpa [seedPair] using this
  · intro n hn0 hnN
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
    have hAk := hA k hn0 hnN
    have e1 : seedSol A Q s ((k : ℤ) + 1) = (Q k * seedSol A Q s k - A ((k : ℤ) - 1) * seedSol A Q s ((k : ℤ) - 1)) / A k := by
      have := seedSol_nat A Q s (k + 1)
      have h' : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [h'] at this
      rw [this]
      simp only [seedPair]
      rw [seedPair_fst, seedSol_nat]
    unfold Lop
    rw [e1]
    have h1 : ((k : ℤ) - 1 : ℤ) = (k : ℤ) - 1 := rfl
    field_simp
    ring

/-- **(eq:tha-S4grow) the growth of the solution on the left forbidden side**: the positivity and the forward ratio `>= 1 + nu/C_A`. -/
theorem growth_ratio (A Q f : ℤ → ℝ) (n1 : ℤ) (CA nu : ℝ) (hA0 : A (-1) = 0) (hApos : ∀ n : ℤ, 0 ≤ n → n ≤ n1 → 0 < A n)
    (hAle : ∀ n : ℤ, 0 ≤ n → n ≤ n1 → A n ≤ CA) (hnu : 0 < nu)
    (hgap : ∀ n : ℤ, 0 ≤ n → n ≤ n1 → A n + A (n - 1) + nu ≤ Q n)
    (hsol : ∀ n : ℤ, 0 ≤ n → n ≤ n1 → Lop A Q f n = 0) (hf0 : 0 < f 0) :
    ∀ n : ℤ, 0 ≤ n → n ≤ n1 → 0 < f n ∧ (1 + nu / CA) * f n ≤ f (n + 1) := by
  have key : ∀ k : ℕ, (k : ℤ) ≤ n1 → 0 < f k ∧ (A k + nu) * f k ≤ A k * f (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 := hsol 0 le_rfl hk
      have hg := hgap 0 le_rfl hk
      unfold Lop at h0
      simp only [zero_sub, hA0, zero_mul, add_zero, zero_add, Int.reduceNeg] at h0 hg ⊢
      refine ⟨by simpa using hf0, ?_⟩
      simp only [Nat.cast_zero, zero_add] at *
      have hq : A 0 * f 1 = Q 0 * f 0 := by linarith
      nlinarith [hq, hg, hf0]
    | succ k ih =>
      intro hk
      have hk' : (k : ℤ) ≤ n1 := by omega
      obtain ⟨hpos, hge⟩ := ih hk'
      have hAk := hApos k (by omega) hk'
      have hAk1 := hApos ((k : ℤ) + 1) (by omega) (by exact_mod_cast hk)
      have hle : f k ≤ f (k + 1) := by
        by_contra hcon
        have hcon := not_le.mp hcon
        nlinarith [mul_lt_mul_of_pos_left hcon hAk]
      have hpos1 : 0 < f ((k : ℤ) + 1) := lt_of_lt_of_le hpos hle
      have h0 := hsol ((k : ℤ) + 1) (by omega) (by exact_mod_cast hk)
      have hg := hgap ((k : ℤ) + 1) (by omega) (by exact_mod_cast hk)
      unfold Lop at h0
      have e1 : ((k : ℤ) + 1 - 1) = (k : ℤ) := by ring
      rw [e1] at h0 hg
      refine ⟨by exact_mod_cast hpos1, ?_⟩
      have hq : A ((k : ℤ) + 1) * f ((k : ℤ) + 1 + 1) = Q ((k : ℤ) + 1) * f ((k : ℤ) + 1) - A k * f k := by linarith
      have hAf : A k * f k ≤ A k * f ((k : ℤ) + 1) := mul_le_mul_of_nonneg_left hle hAk.le
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hg hpos1.le]
  intro n hn0 hnn
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
  obtain ⟨hpos, hge⟩ := key k hnn
  refine ⟨hpos, ?_⟩
  have hAk := hApos k hn0 hnn
  have hCA : 0 < CA := lt_of_lt_of_le hAk (hAle k hn0 hnn)
  have h1 : nu / CA ≤ nu / A k := div_le_div_of_nonneg_left hnu.le hAk (hAle k hn0 hnn)
  have h2 : (1 + nu / A k) * f k ≤ f (k + 1) := by
    rw [← sub_nonneg]
    have : f (k + 1) - (1 + nu / A k) * f k = (A k * f (k + 1) - (A k + nu) * f k) / A k := by field_simp
    rw [this]
    exact div_nonneg (by linarith) hAk.le
  calc (1 + nu / CA) * f k ≤ (1 + nu / A k) * f k := mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ ≤ _ := h2

end FormalResearch.JacobiEigenvectors.TheoremA

end
