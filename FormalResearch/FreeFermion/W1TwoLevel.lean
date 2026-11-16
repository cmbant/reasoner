module

public import Mathlib

/-!
# The two-level (resonant doublet) weight formula (Weyl W1, `prop:res-twolevel`(c))

Source: `Weyl/free_fermion/paper/parts/resonance.tex`, Proposition `prop:res-twolevel`, part (c):
for the real symmetric `2 × 2` matrix `h = [[a, t], [t, d]]` (`Δ = a - d`, `t ≠ 0`) and a normalised
eigenvector `(p, q)` for the lower eigenvalue `E_- = (a + d - √(Δ² + 4t²))/2`,
`p² / (p² + q²) = ½ (1 - Δ / √(Δ² + 4t²))` *exactly*, and the logit of the extra level is
`log((1 - λ_*)/λ_*) = 2 arsinh(Δ / (2|t|))`.

## Formalised

* `twolevel_weight` : the weight formula, for either eigenvalue (`ρ = ±√(Δ² + 4t²)`; the upper
  eigenvalue gives `½ (1 + Δ/√(Δ²+4t²))`).
* `twolevel_logit` : the logit identity `e_* = 2 arsinh(Δ/(2|t|))`.
* `twolevel_symmetric` : `Δ = 0` gives weight `1/2` (the mirror-symmetric case of part (e)).

## Not formalised

Everything else in `prop:res-twolevel` and `thm:res-doublet`: the reduction of the chain to the
`2 × 2` matrix `h(E)` (Schur complement and exponential decay estimates), and the `O(e^{-cL})`
statements.  This file is only the exact finite algebra of part (c).
-/

@[expose] public section

namespace FormalResearch.FreeFermion

/-- **Two-level weight** (`prop:res-twolevel`(c), eq. `eq:res-twolevel`).  `ρ` is a square root of
`Δ² + 4t²` (`ρ = +√` for the lower eigenvalue `E = (a+d-ρ)/2`, `ρ = -√` for the upper one);
`(p, q)` is an eigenvector of `[[a, t], [t, d]]` for `E`, `t ≠ 0`. -/
theorem twolevel_weight (a d t p q ρ : ℝ) (ht : t ≠ 0) (hρ : ρ ^ 2 = (a - d) ^ 2 + 4 * t ^ 2)
    (h1 : a * p + t * q = (a + d - ρ) / 2 * p) (h2 : t * p + d * q = (a + d - ρ) / 2 * q)
    (hpq : p ≠ 0 ∨ q ≠ 0) :
    p ^ 2 / (p ^ 2 + q ^ 2) = (1 - (a - d) / ρ) / 2 := by
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    have : 0 < t ^ 2 := by positivity
    nlinarith [sq_nonneg (a - d)]
  have hq : 2 * t * q = -((a - d) + ρ) * p := by linarith
  have hp : p ≠ 0 := by
    rintro rfl
    have : t * q = 0 := by linarith
    rcases hpq with h | h
    · exact h rfl
    · exact h ((mul_eq_zero.mp this).resolve_left ht)
  have hsum : p ^ 2 + q ^ 2 ≠ 0 := by positivity
  have e : (2 * t * q) ^ 2 = ((a - d) + ρ) ^ 2 * p ^ 2 := by rw [hq]; ring
  have key : (ρ + (a - d)) * p ^ 2 * (4 * t ^ 2) = (ρ - (a - d)) * q ^ 2 * (4 * t ^ 2) := by
    linear_combination (-(ρ - (a - d))) * e + ((ρ + (a - d)) * p ^ 2) * (-hρ)
  have key' : (ρ + (a - d)) * p ^ 2 = (ρ - (a - d)) * q ^ 2 :=
    mul_right_cancel₀ (by positivity : (4 * t ^ 2) ≠ 0) key
  rw [div_eq_iff hsum]
  field_simp
  linear_combination key'

/-- **Symmetric case** (`prop:res-twolevel`(e), `Δ = 0`): the weight is `1/2`. -/
theorem twolevel_symmetric (a t p q ρ : ℝ) (ht : t ≠ 0) (hρ : ρ ^ 2 = 4 * t ^ 2)
    (h1 : a * p + t * q = (a + a - ρ) / 2 * p) (h2 : t * p + a * q = (a + a - ρ) / 2 * q)
    (hpq : p ≠ 0 ∨ q ≠ 0) : p ^ 2 / (p ^ 2 + q ^ 2) = 1 / 2 := by
  have := twolevel_weight a a t p q ρ ht (by simpa using hρ) h1 h2 hpq
  rw [this]; simp

/-- **Logit of the extra level** (`prop:res-twolevel`(c)): with `λ_* = ½ (1 - Δ/R)`,
`R = √(Δ² + 4t²)`, one has `log((1 - λ_*)/λ_*) = 2 arsinh(Δ / (2|t|))`. -/
theorem twolevel_logit (Δ t : ℝ) (ht : t ≠ 0) :
    Real.log ((1 - (1 - Δ / √(Δ ^ 2 + 4 * t ^ 2)) / 2) / ((1 - Δ / √(Δ ^ 2 + 4 * t ^ 2)) / 2)) =
      2 * Real.arsinh (Δ / (2 * |t|)) := by
  set R := √(Δ ^ 2 + 4 * t ^ 2) with hR
  have ht2 : 0 < t ^ 2 := by positivity
  have hR2 : R ^ 2 = Δ ^ 2 + 4 * t ^ 2 := Real.sq_sqrt (by positivity)
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hRΔ : Δ < R := by nlinarith [sq_nonneg (R - Δ)]
  have hRΔ' : -R < Δ := by nlinarith [sq_nonneg (R + Δ)]
  have habs : 0 < |t| := abs_pos.mpr ht
  have hsq : √(1 + (Δ / (2 * |t|)) ^ 2) = R / (2 * |t|) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    field_simp
    rw [sq_abs, hR2]; ring
  have harg : (Δ / (2 * |t|) + √(1 + (Δ / (2 * |t|)) ^ 2)) ^ 2 =
      (1 - (1 - Δ / R) / 2) / ((1 - Δ / R) / 2) := by
    rw [hsq]
    have h4 : 4 * t ^ 2 = (R - Δ) * (R + Δ) := by nlinarith
    have : (Δ / (2 * |t|) + R / (2 * |t|)) ^ 2 = (Δ + R) ^ 2 / (4 * t ^ 2) := by
      field_simp
      rw [sq_abs]; ring
    rw [this, h4]
    have : R - Δ ≠ 0 := by linarith
    have : R + Δ ≠ 0 := by linarith
    field_simp
    ring
  rw [← harg, Real.log_pow, Real.arsinh]
  norm_num

/-- info: 'FormalResearch.FreeFermion.twolevel_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twolevel_weight

/-- info: 'FormalResearch.FreeFermion.twolevel_logit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twolevel_logit

end FormalResearch.FreeFermion
