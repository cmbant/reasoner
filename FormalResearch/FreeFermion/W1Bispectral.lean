module

public import Mathlib

/-!
# Exact algebra behind the bispectral chains (Weyl W1, `prop:bisp`, `cor:bispracah`)

Sources: `Weyl/free_fermion/paper/parts/model.tex`, Proposition `prop:bisp` and its proof;
`Weyl/free_fermion/notes/racah_chain.tex`, Corollary `cor:bispracah`.

The exact Leonard-pair statement of `prop:bisp`(i) (Krawtchouk chain: spectrum `{k/N}`, self-duality,
the Heun operator commutes with `P` exactly) is `FormalResearch.FreeFermion.krawtchouk_heun` in
`W1Krawtchouk`.  This file holds the remaining *finite algebra* of the proposition:

* `krawtchouk_Dmu_factor`, `krawtchouk_orbit_endpoints` : for the Krawtchouk symbols
  `A² = p q t(1-t)`, `B = p + (q-p) t`, `D_μ = 4A² - (μ-B)²` equals `(t - t_-)(t_+ - t)` with
  `t_± = B(μ) ± 2A(μ)` (so `eq:bispD` holds with `x = t`, `κ = 1`), and `0 ≤ t_- ≤ t_+ ≤ 1`.
* `hahn_Dmu_factor` : for the limit symbols `A = t(1-t)`, `B = 2t(1-t)` of the Hahn chain,
  `D_μ = 4μ(t - t_-)(t_+ - t)`, `t_± = (1 ± √(1-μ))/2`.
* `bisp_profile_*` : the travel-time profile `x(τ) = (x_+ + x_-)/2 - (x_+ - x_-)/2 · cos πτ`
  solves `x'² = π²(x-x_-)(x_+-x)` with `x(0) = x_-`, `x(1) = x_+`, and `cos πτ` is affine in `x`.
* `bisp_scale_algebra` : the constant of `eq:bispF`, `LF = 8 sin φ (x_c-x_-)(x_+-x_c)/((x_+-x_-)Δx)`,
  from `F = 4 sin φ sin πτ_c/(π L δ_c)`, `π sin(πτ_c) δ_c = 2Δx/(x_+-x_-)` and
  `sin²πτ_c = 4(x_c-x_-)(x_+-x_c)/(x_+-x_-)²`.
* `bispracah_scale` : `cor:bispracah`, the Racah specialisation of `eq:bispF`.

## What is NOT formalised

The definitions of the global class, of the travel-time operator `T`, of `δ_c`, `τ_c`, `F` (they are
inputs/hypotheses here), the continuum-to-discrete `O(L^{-1})` statements, the ODE uniqueness step
`ω = π` (that the solution of `dx/dτ = ω√((x-x_-)(x_+-x))` reaching `x_+` at `τ = 1` has `ω = π`),
the Hahn asymptotics `A_N = t(1-t) + O(1/N)` etc., the margin of (O), and the statement that the
travel-time operator equals the Heun operator up to `O(L^{-1})` (analysis).
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Real

/-- The Krawtchouk symbol `B(t) = p + (q-p) t`, `q = 1-p` (the limit of `b_n`, `t = n/N`). -/
def krawSymB (p t : ℝ) : ℝ := p + (1 - 2 * p) * t

/-- `D_μ(t) = 4A² - (μ-B)²` for the Krawtchouk symbols, `A² = p q t(1-t)`. -/
def krawDmu (p μ t : ℝ) : ℝ := 4 * (p * (1 - p) * t * (1 - t)) - (μ - krawSymB p t) ^ 2

theorem krawDmu_symm (p μ t : ℝ) :
    krawDmu p μ t = 4 * (p * (1 - p) * μ * (1 - μ)) - (t - krawSymB p μ) ^ 2 := by
  unfold krawDmu krawSymB; ring

/-- **`prop:bisp`(i), `eq:bispD` for the Krawtchouk chain**: `D_μ(t) = (t - t_-)(t_+ - t)` with
`t_± = B(μ) ± 2√(p q μ(1-μ))` (leading coefficient `-1`, so `x = t`, `κ = 1`). -/
theorem krawtchouk_Dmu_factor (p μ t : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    krawDmu p μ t = (t - (krawSymB p μ - 2 * √(p * (1 - p) * μ * (1 - μ)))) *
      ((krawSymB p μ + 2 * √(p * (1 - p) * μ * (1 - μ))) - t) := by
  have h : 0 ≤ p * (1 - p) * μ * (1 - μ) := by
    have : 0 ≤ 1 - p := by linarith
    have : 0 ≤ 1 - μ := by linarith
    positivity
  have hs := Real.sq_sqrt h
  rw [krawDmu_symm]
  linear_combination (-4) * hs

/-- The orbit endpoints lie in `[0,1]`: `0 ≤ t_- ≤ t_+ ≤ 1` for `0 ≤ μ ≤ 1`.  Moreover
`t_- = 0` exactly when `μ = p` and `t_+ = 1` exactly when `μ = q` (see the squares below). -/
theorem krawtchouk_orbit_endpoints (p μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    0 ≤ krawSymB p μ - 2 * √(p * (1 - p) * μ * (1 - μ)) ∧
      krawSymB p μ - 2 * √(p * (1 - p) * μ * (1 - μ)) ≤
        krawSymB p μ + 2 * √(p * (1 - p) * μ * (1 - μ)) ∧
      krawSymB p μ + 2 * √(p * (1 - p) * μ * (1 - μ)) ≤ 1 := by
  have h : 0 ≤ p * (1 - p) * μ * (1 - μ) := by
    have : 0 ≤ 1 - p := by linarith
    have : 0 ≤ 1 - μ := by linarith
    positivity
  have hs := Real.sq_sqrt h
  have hsn := Real.sqrt_nonneg (p * (1 - p) * μ * (1 - μ))
  set r := √(p * (1 - p) * μ * (1 - μ)) with hr
  have hB0 : 0 ≤ krawSymB p μ := by
    unfold krawSymB; nlinarith
  have hB1 : krawSymB p μ ≤ 1 := by
    unfold krawSymB; nlinarith
  refine ⟨?_, by linarith, ?_⟩
  · -- (B)² - 4 r² = (μ - p)²
    have : (krawSymB p μ) ^ 2 - 4 * r ^ 2 = (μ - p) ^ 2 := by
      unfold krawSymB; rw [hs]; ring
    nlinarith [sq_nonneg (μ - p)]
  · have : (1 - krawSymB p μ) ^ 2 - 4 * r ^ 2 = (μ - (1 - p)) ^ 2 := by
      unfold krawSymB; rw [hs]; ring
    nlinarith [sq_nonneg (μ - (1 - p))]

/-- **`prop:bisp`(ii), Hahn chain, limit symbols** `A = t(1-t)`, `B = 2t(1-t)`:
`D_μ = 4A² - (μ-B)² = 4μ(t - t_-)(t_+ - t)`, `t_± = (1 ± √(1-μ))/2`, for `μ ≤ 1`. -/
theorem hahn_Dmu_factor (μ t : ℝ) (hμ : μ ≤ 1) :
    4 * (t * (1 - t)) ^ 2 - (μ - 2 * (t * (1 - t))) ^ 2 =
      4 * μ * ((t - (1 - √(1 - μ)) / 2) * ((1 + √(1 - μ)) / 2 - t)) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 - μ by linarith)
  linear_combination (-μ) * hs

/-- Travel-time profile of `prop:bisp`: `x(τ) = (x_+ + x_-)/2 - (x_+ - x_-)/2 · cos πτ`. -/
noncomputable def bispProfile (xm xp τ : ℝ) : ℝ := (xp + xm) / 2 - (xp - xm) / 2 * Real.cos (π * τ)

theorem bispProfile_zero (xm xp : ℝ) : bispProfile xm xp 0 = xm := by
  simp [bispProfile]; ring

theorem bispProfile_one (xm xp : ℝ) : bispProfile xm xp 1 = xp := by
  simp [bispProfile]; ring

theorem bispProfile_hasDerivAt (xm xp τ : ℝ) :
    HasDerivAt (bispProfile xm xp) ((xp - xm) / 2 * π * Real.sin (π * τ)) τ := by
  unfold bispProfile
  have h1 : HasDerivAt (fun τ : ℝ => π * τ) π τ := by simpa using (hasDerivAt_id τ).const_mul π
  have h2 := (h1.cos).const_mul ((xp - xm) / 2)
  have h3 := h2.const_sub ((xp + xm) / 2)
  convert h3 using 1
  ring

/-- `x'² = π²(x-x_-)(x_+-x)`: `eq:bispD` with `T_orb² κ = π²`. -/
theorem bispProfile_deriv_sq (xm xp τ : ℝ) :
    ((xp - xm) / 2 * π * Real.sin (π * τ)) ^ 2 =
      π ^ 2 * ((bispProfile xm xp τ - xm) * (xp - bispProfile xm xp τ)) := by
  unfold bispProfile
  have := Real.sin_sq_add_cos_sq (π * τ)
  linear_combination ((xp - xm) ^ 2 / 4 * π ^ 2) * this

/-- `cos πτ = (x_+ + x_- - 2x)/(x_+ - x_-)` on the orbit. -/
theorem bispProfile_cos (xm xp τ : ℝ) (h : xm ≠ xp) :
    Real.cos (π * τ) = (xp + xm - 2 * bispProfile xm xp τ) / (xp - xm) := by
  unfold bispProfile
  have : xp - xm ≠ 0 := sub_ne_zero.mpr h.symm
  field_simp
  ring

/-- `sin² πτ = 4(x-x_-)(x_+-x)/(x_+-x_-)²`. -/
theorem bispProfile_sin_sq (xm xp τ : ℝ) (h : xm ≠ xp) :
    Real.sin (π * τ) ^ 2 =
      4 * ((bispProfile xm xp τ - xm) * (xp - bispProfile xm xp τ)) / (xp - xm) ^ 2 := by
  unfold bispProfile
  have : xp - xm ≠ 0 := sub_ne_zero.mpr h.symm
  have := Real.sin_sq_add_cos_sq (π * τ)
  field_simp
  linear_combination (4 * (xp - xm) ^ 2) * this

/-- **`eq:bispF`**: from `F = 4 sin φ sin πτ_c/(π L δ_c)`, `π sin(πτ_c) δ_c = 2Δx/(x_+-x_-)` and
`sin²πτ_c = 4(x_c-x_-)(x_+-x_c)/(x_+-x_-)²`, the scale is
`LF = 8 sin φ (x_c-x_-)(x_+-x_c)/((x_+-x_-)Δx)`.  Here `S = sin φ`, `s = sin πτ_c`, `δ = δ_c`,
`Δx = x_{n_0+1}-x_{n_0}` and `L F` is written `4 S s/(π δ)`. -/
theorem bisp_scale_algebra (S s δ xm xp xc Δx : ℝ) (hδ : δ ≠ 0) (hW : xp - xm ≠ 0)
    (hΔ : Δx ≠ 0) (h1 : π * s * δ = 2 * Δx / (xp - xm))
    (h2 : s ^ 2 = 4 * ((xc - xm) * (xp - xc)) / (xp - xm) ^ 2) :
    4 * S * s / (π * δ) = 8 * S * ((xc - xm) * (xp - xc)) / ((xp - xm) * Δx) := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have h1' : π * s * δ * (xp - xm) = 2 * Δx := by
    rw [eq_div_iff hW] at h1; exact h1
  have h2' : s ^ 2 * (xp - xm) ^ 2 = 4 * ((xc - xm) * (xp - xc)) := by
    rw [eq_div_iff (pow_ne_zero 2 hW)] at h2; exact h2
  rw [div_eq_div_iff (mul_ne_zero hpi hδ) (mul_ne_zero hW hΔ)]
  linear_combination (-2 * S * s * (xp - xm)) * h1' + (2 * S * π * δ) * h2'

/-- **`cor:bispracah`**: for the folded Racah chain `x = q²`, `x_- = 0`, `x_+ = L²(1-β²)`,
`x_c = α²L²`, `Δx = 4αL`, `Δ = 1-α²-β²`, `eq:bispF` reads
`LF = 2Lα Δ sin φ/(1-β²)`, and with `sin φ = 2β√Δ/(1-α²)` (`eq:fermiangle`)
`LF = 4Lαβ Δ^{3/2}/((1-α²)(1-β²))`. -/
theorem bispracah_scale (L α β S : ℝ) (hL : L ≠ 0) (hα : α ≠ 0) (hβ : β ^ 2 ≠ 1) :
    8 * S * ((α ^ 2 * L ^ 2 - 0) * (L ^ 2 * (1 - β ^ 2) - α ^ 2 * L ^ 2)) /
        ((L ^ 2 * (1 - β ^ 2) - 0) * (4 * α * L)) =
      2 * L * α * (1 - α ^ 2 - β ^ 2) * S / (1 - β ^ 2) := by
  have : 1 - β ^ 2 ≠ 0 := fun h => hβ (by linarith)
  field_simp
  ring

theorem bispracah_scale_explicit (L α β Δ : ℝ) (hα2 : α ^ 2 ≠ 1) (hΔ : 0 ≤ Δ) :
    2 * L * α * Δ * (2 * β * √Δ / (1 - α ^ 2)) / (1 - β ^ 2) =
      4 * L * α * β * Δ ^ (3 / 2 : ℝ) / ((1 - α ^ 2) * (1 - β ^ 2)) := by
  have h32 : Δ ^ (3 / 2 : ℝ) = Δ * √Δ := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hΔ (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [h32]
  have : 1 - α ^ 2 ≠ 0 := fun h => hα2 (by linarith)
  by_cases hb : 1 - β ^ 2 = 0
  · simp [hb]
  · field_simp
    ring

/-- info: 'FormalResearch.FreeFermion.krawtchouk_Dmu_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms krawtchouk_Dmu_factor

/-- info: 'FormalResearch.FreeFermion.krawtchouk_orbit_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms krawtchouk_orbit_endpoints

/-- info: 'FormalResearch.FreeFermion.hahn_Dmu_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_Dmu_factor

/-- info: 'FormalResearch.FreeFermion.bispProfile_deriv_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bispProfile_deriv_sq

/-- info: 'FormalResearch.FreeFermion.bisp_scale_algebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bisp_scale_algebra

/-- info: 'FormalResearch.FreeFermion.bispracah_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bispracah_scale

end FormalResearch.FreeFermion
