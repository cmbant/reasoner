module

public import FormalResearch.ModularBootstrap.Integrality.ChebMatching
public import FormalResearch.ModularBootstrap.Integrality.CorrEuclid
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `int:cheb-explicit`: the Euclidean moment inverse and the floor `8 N^{5/2}`

`CFT/modular_bootstrap/paper/integrality.tex`, Lemma INT-M.exp (`int:cheb-explicit`): on the
midpoint grid of size `N = M + 1`, the angle shift realising any moment target `v` with
`‖B v‖₂ ≤ 1/(4M)` exists with `‖h‖₂ ≤ 1/(2M)` (`AngleShift.exists_angleShift`), and the conclusion of
Lemma INT-M (`int:cheb`) holds under the floor `W_0 ≥ 8 N^{5/2}` (`cheb_explicit` below; the grid is
the one of size `N`, `R = ⌊2W_0/N²⌋ ≥ 16√N - 1 ≥ 4πM/√N` units per site, Bessel's inequality
`CorrEuclid.bessel_defect`).  **Proved.**
-/

@[expose] public section

open Real Finset MeasureTheory Polynomial
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

/-- **`int:cheb-explicit`** (Lemma INT-M.exp): the conclusion of `int:cheb` holds under the
floor `W_0 ≥ 8 N^{5/2}`, `N = M + 1`, by the Euclidean inverse on the midpoint grid of size `N`.
Here `μ` is a finite measure carried by `[-1,1]` of integer total mass `N_tot ≥ 1` with
`μ ≥ W_0 dx`. -/
theorem cheb_explicit {M : ℕ} (hM : 1 ≤ M) {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsupp : μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0) {Ntot : ℕ} (hN : μ Set.univ = Ntot) {W0 : ℝ}
    (hW0 : 8 * ((M : ℝ) + 1) ^ 2 * Real.sqrt ((M : ℝ) + 1) ≤ W0)
    (hμ : ENNReal.ofReal W0 • volume.restrict (Set.Icc (-1 : ℝ) 1) ≤ μ) :
    IntegerMomentMatching μ M := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1 : ℝ) < (M : ℝ) + 1 := by linarith
  set s : ℝ := Real.sqrt ((M : ℝ) + 1) with hs
  have hs1 : 1 ≤ s := by
    rw [hs]; exact Real.one_le_sqrt.2 hN1.le
  have hss : s ^ 2 = (M : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hW0pos : 0 ≤ W0 := le_trans (by positivity) hW0
  -- the number of units per site
  set R : ℕ := ⌊2 * W0 / ((M + 1 : ℕ) : ℝ) ^ 2⌋₊ with hRdef
  have hNn : ((M + 1 : ℕ) : ℝ) = s ^ 2 := by push_cast; rw [hss]
  have hq : 16 * s ≤ 2 * W0 / ((M + 1 : ℕ) : ℝ) ^ 2 := by
    rw [hNn, le_div_iff₀ (by positivity)]
    have : 8 * ((M : ℝ) + 1) ^ 2 * s ≤ W0 := hW0
    rw [← hss] at this
    nlinarith [this]
  have hRlow : 16 * s - 1 ≤ (R : ℝ) := by
    have := Nat.lt_floor_add_one (2 * W0 / ((M + 1 : ℕ) : ℝ) ^ 2)
    rw [← hRdef] at this
    linarith
  have hR1 : 1 ≤ R := by
    have : (1 : ℝ) ≤ R := by linarith
    exact_mod_cast this
  have hRle : (R : ℝ) ≤ 2 * W0 / ((M + 1 : ℕ) : ℝ) ^ 2 := Nat.floor_le (by positivity)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
  have hcorr : Corr (M + 1) M (R : ℝ) := by
    refine corr_euclid hM hRpos ?_
    -- `16 π² M² ≤ R² (M+1)`
    have hπ : π < 3.15 := Real.pi_lt_d2
    have hMs : (M : ℝ) = s ^ 2 - 1 := by linarith
    have hss2 : s ≤ s ^ 2 := by nlinarith
    have h1 : 4 * π * (s ^ 2 - 1) ≤ (16 * s - 1) * s := by
      nlinarith [pi_pos, mul_le_mul_of_nonneg_right hπ.le (sq_nonneg s)]
    have hpos : 0 ≤ 4 * π * (s ^ 2 - 1) := by
      have : 0 ≤ s ^ 2 - 1 := by nlinarith
      positivity
    have h2 : 4 * π * (s ^ 2 - 1) ≤ (R : ℝ) * s := by
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_right hRlow (by linarith)
    have h3 : (4 * π * (s ^ 2 - 1)) ^ 2 ≤ ((R : ℝ) * s) ^ 2 := pow_le_pow_left₀ hpos h2 2
    rw [hMs]
    nlinarith [h3, hss]
  exact exists_integer_atomic_of_corr hR1 (le_refl _) hcorr hsupp hN hW0pos hRle hμ

/-- info: 'FormalResearch.ModularBootstrap.Integrality.cheb_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cheb_explicit

end FormalResearch.ModularBootstrap.Integrality
