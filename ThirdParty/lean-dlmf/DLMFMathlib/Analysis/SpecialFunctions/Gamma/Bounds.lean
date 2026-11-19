/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Bounds for the Pochhammer symbol and the reciprocal Gamma function

Lower bounds `k! ≤ ‖(w)ₖ‖` for `1 ≤ Re w`, the resulting bound for `1/Γ(c + n)` used to dominate
hypergeometric-type series uniformly in a parameter, and the local lower bound for `‖Γ‖` near
a point with large real part.

## Main results

* `Complex.factorial_le_norm_ascPochhammer_eval`: `k! ≤ ‖(w)ₖ‖` for `1 ≤ Re w`.
* `Complex.norm_recip_Gamma_add_nat_le`: `‖1/Γ(c+n)‖ ≤ 1/((n-N)! m)` for `n ≥ N`.
* `Complex.exists_open_norm_Gamma_add_nat_gt`: `‖Γ(c + N)‖` stays above half its value near
  `c₀` when `2 ≤ Re (c₀ + N)`.
-/

@[expose] public section

open Filter
open scoped Topology Nat

namespace Complex

/-- Lower bound for the Pochhammer symbol when `1 ≤ Re w`. -/
theorem factorial_le_norm_ascPochhammer_eval {w : ℂ} (hw : 1 ≤ w.re) (k : ℕ) :
    (k.factorial : ℝ) ≤ ‖(ascPochhammer ℂ k).eval w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, norm_mul, Nat.factorial_succ, Nat.cast_mul]
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ ‖w + k‖ := by
      calc ((k + 1 : ℕ) : ℝ) = 1 + k := by push_cast; ring
        _ ≤ (w + k).re := by simp only [Complex.add_re, Complex.natCast_re]; linarith
        _ ≤ ‖w + k‖ := re_le_norm _
    calc ((k + 1 : ℕ) : ℝ) * k.factorial ≤ ‖w + k‖ * ‖(ascPochhammer ℂ k).eval w‖ :=
          mul_le_mul h1 ih (by positivity) (norm_nonneg _)
      _ = _ := by ring

/-- `‖1/Γ(c+n)‖ ≤ 1/((n-N)! m)` for `n ≥ N`, when `1 ≤ Re (c+N)` and `m ≤ ‖Γ(c+N)‖`. -/
theorem norm_recip_Gamma_add_nat_le {c : ℂ} {N : ℕ} (hre : 1 ≤ (c + N).re) {m : ℝ} (hm : 0 < m)
    (hΓ : m ≤ ‖Gamma (c + N)‖) {n : ℕ} (hn : N ≤ n) :
    ‖(Gamma (c + n))⁻¹‖ ≤ ((n - N).factorial : ℝ)⁻¹ * m⁻¹ := by
  have hpole : ∀ k : ℕ, c + N ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hΓ0 : Gamma (c + N) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hΓ
    linarith
  have heq : c + n = c + N + ((n - N : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hn]
    ring
  have hG : Gamma (c + N + ((n - N : ℕ) : ℂ)) =
      (ascPochhammer ℂ (n - N)).eval (c + N) * Gamma (c + N) := by
    rw [← Gamma_add_nat_div_Gamma_eq (n := n - N) (c + N) hpole]
    field_simp
  rw [heq, hG, mul_inv, norm_mul, norm_inv, norm_inv]
  have hp := factorial_le_norm_ascPochhammer_eval hre (n - N)
  have hfpos : (0 : ℝ) < (n - N).factorial := by positivity
  gcongr

/-- The nonvanishing of `Γ` near a point with real part at least two. -/
theorem exists_open_norm_Gamma_add_nat_gt {c₀ : ℂ} {N : ℕ} (hre : 2 ≤ (c₀ + N).re) :
    ∃ V : Set ℂ, IsOpen V ∧ c₀ ∈ V ∧
      ∀ c ∈ V, ‖Gamma (c₀ + N)‖ / 2 < ‖Gamma (c + N)‖ := by
  have hpole : ∀ k : ℕ, c₀ + N ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hΓ0 : Gamma (c₀ + N) ≠ 0 := Gamma_ne_zero hpole
  have hcont : ContinuousAt (fun c : ℂ => ‖Gamma (c + N)‖) c₀ :=
    ((differentiableAt_Gamma _ hpole).comp c₀ (differentiableAt_id.add_const _)).continuousAt.norm
  have hev : ∀ᶠ c in 𝓝 c₀, ‖Gamma (c₀ + N)‖ / 2 < ‖Gamma (c + N)‖ :=
    hcont.eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr hΓ0)))
  obtain ⟨V, hV, hVopen, hc₀V⟩ := eventually_nhds_iff.mp hev
  exact ⟨V, hVopen, hc₀V, hV⟩

end Complex
