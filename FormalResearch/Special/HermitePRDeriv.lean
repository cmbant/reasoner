module

public import FormalResearch.Special.HermiteFunction
public import FormalResearch.Special.HermiteKappaSup

/-!
# Ladder estimate for derivatives of Hermite functions

This module repackages the exact symmetric ladder identity from
HermiteFunction as an absolute-value estimate for the derivative (repackaging of
hasDerivAt_hermitePsi, not new mathematics). The derivative bound with rho_n,
|y_n'| <= C N^(1/4) rho_n^(1/2), is proved in HermitePRRho from this estimate and
hermite_PR_b. See W1, Lemma lem:PR(b), and Szegő, Theorem 8.22.8.
-/

@[expose] public section

namespace FormalResearch.Special

/-- Absolute-value consequence of the exact symmetric Hermite ladder relation. -/
theorem hpr_abs_deriv_le_ladder (n : ℤ) (hn : 0 ≤ n) (x : ℝ) :
    |deriv (hermitePsi n) x| ≤
      √((n : ℝ) / 2) * |hermitePsi (n - 1) x| +
        √(((n : ℝ) + 1) / 2) * |hermitePsi (n + 1) x| := by
  have h := hasDerivAt_hermitePsi n hn x
  rw [h.deriv]
  calc
    |√((n : ℝ) / 2) * hermitePsi (n - 1) x -
        √(((n : ℝ) + 1) / 2) * hermitePsi (n + 1) x| ≤
        |√((n : ℝ) / 2) * hermitePsi (n - 1) x| +
          |√(((n : ℝ) + 1) / 2) * hermitePsi (n + 1) x| := abs_sub _ _
    _ = √((n : ℝ) / 2) * |hermitePsi (n - 1) x| +
          √(((n : ℝ) + 1) / 2) * |hermitePsi (n + 1) x| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _)]

end FormalResearch.Special

/-- info: 'FormalResearch.Special.hpr_abs_deriv_le_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hpr_abs_deriv_le_ladder
