module

public import FormalResearch.ModularBootstrap.Integration.HankelBounds

/-!
# Lemma B (d), second bound: the Hankel continuation on the strip

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`) (d), last sentence of
the proof: "The Hankel continuation `G(b) = -2π ∫₀^∞ g(t) I₀(4π i b √(c' t/3)) dt` has kernel bounded by
`K_a(t)` for `|Im b| ≤ 1/2`, proving the supremum bound."

* `besselI0C z = π⁻¹ ∫₀^π e^{z cos θ} dθ`: `I₀` of a complex argument, defined by the classical integral
  representation (`besselI0C_ofReal`: it is the real `Bessel.besselI0` on real arguments);
* `besselI0C_norm_le`: `|I₀(z)| ≤ I₀(Re z)`;
* `hankelContinuation c' g b`: the continuation `G(b)` above;
* `lemmaB_d_sup`: for `c' ≥ 1000` and `|Im b| ≤ 1/2`,
  `|G(b)| ≤ 4π e^{92} c'² M[g]` (explicit constant; the paper's `C` is unspecified).

Not covered: that `G(x) = g(c' x²/3)` for real `x` (the order-zero Hankel inversion `g = -ĝ` written in
radial coordinates, which Mathlib does not provide) and that `G` is holomorphic on `|Im b| < 1/2`.  Neither
is needed for the bound itself or for any statement in this development: `LemmaPJInput` is stated directly
for `g(c' x²/3)` on the real axis.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology
open scoped Complex

namespace FormalResearch.ModularBootstrap.Integration

open Crossing

/-- `I₀(z)` for complex `z` through the integral representation `π⁻¹ ∫₀^π e^{z cos θ} dθ`. -/
noncomputable def besselI0C (z : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, Complex.exp (z * (Real.cos θ : ℝ))

/-- On real arguments `besselI0C` is the real `Bessel.besselI0`. -/
theorem besselI0C_ofReal (z : ℝ) : besselI0C (z : ℂ) = (Bessel.besselI0 z : ℂ) := by
  rw [Bessel.besselI0_integral, besselI0C]
  have h : ∀ θ : ℝ, Complex.exp ((z : ℂ) * (Real.cos θ : ℝ)) = ((Real.exp (z * Real.cos θ) : ℝ) : ℂ) := by
    intro θ; rw [Complex.ofReal_exp]; push_cast; rfl
  simp_rw [h]
  rw [intervalIntegral.integral_ofReal]
  push_cast
  ring

/-- `|I₀(z)| ≤ I₀(Re z)`. -/
theorem besselI0C_norm_le (z : ℂ) : ‖besselI0C z‖ ≤ Bessel.besselI0 z.re := by
  unfold besselI0C
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Bessel.besselI0_integral, ← div_eq_inv_mul]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
  refine le_of_eq (intervalIntegral.integral_congr fun θ _ => ?_)
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

/-- `I₀` is even, nondecreasing in `|z|`: `I₀(u) ≤ I₀(w)` for `|u| ≤ w`. -/
theorem besselI0_le_of_abs_le {u w : ℝ} (h : |u| ≤ w) : Bessel.besselI0 u ≤ Bessel.besselI0 w := by
  have : Bessel.besselI0 u = Bessel.besselI0 |u| := by
    rw [Bessel.besselI0_eq, Bessel.besselI0_eq, sq_abs]
  rw [this]
  exact Bessel.besselI0_mono (abs_nonneg u) h

/-- The Hankel continuation `G(b) = -2π ∫₀^∞ g(t) I₀(4π i b √(c' t/3)) dt` (`vlo:Bessel`, `vlo:Gap`). -/
noncomputable def hankelContinuation (c' : ℝ) (g : ℝ → ℝ) (b : ℂ) : ℂ :=
  -2 * (π : ℂ) * ∫ t in Ioi (0 : ℝ),
    (g t : ℂ) * besselI0C (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))

/-- On the strip the kernel is bounded by `K_a`: for `|Im b| ≤ 1/2`, `t ≥ 0`, `a = c'/12`,
`|I₀(4π i b √(c' t/3))| ≤ K_a(t)`. -/
theorem besselI0C_strip_le {c' t : ℝ} (hc : 0 < c') (ht : 0 ≤ t) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖besselI0C (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))‖ ≤
      kernelK 1 (c' / 12) t := by
  refine (besselI0C_norm_le _).trans ?_
  rw [kernelK_one_eq_besselI0 (by positivity) ht]
  refine besselI0_le_of_abs_le ?_
  set s : ℝ := Real.sqrt (c' * t / 3) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hre : (4 * (π : ℂ) * Complex.I * b * (s : ℝ)).re = -(4 * π * b.im * s) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, abs_neg, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π),
    abs_of_nonneg hs0]
  have hsq : Real.sqrt (c' / 12 * t) = s / 2 := by
    rw [hs, show c' / 12 * t = (c' * t / 3) / 4 by ring, Real.sqrt_div (by positivity),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsq]
  have : |b.im| * s ≤ 1 / 2 * s := by gcongr
  nlinarith [Real.pi_pos]

/-- **Lemma B (d), second bound (`vlo:Bessel`)** with explicit constant: for `c' ≥ 1000`, every test
`g ∈ TestClass virasoroProblem (c'/12)` and every `b` with `|Im b| ≤ 1/2`,
`|G(b)| ≤ 4π e^{92} c'² M[g]`, where `G = hankelContinuation c' g`.  (Here `G` is *defined* by the
Hankel-continuation integral; its agreement with `g(c' b²/3)` on the real axis is the Hankel inversion
formula, not formalised.) -/
theorem lemmaB_d_sup {c' : ℝ} (hc : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖hankelContinuation c' g b‖ ≤
      4 * π * exp 92 * c' ^ 2 * virasoroProblem.cardyNorm (c' / 12) g := by
  have hc0 : 0 < c' := by linarith
  obtain ⟨hint, hle⟩ := lemmaB_d_integral hc hg
  unfold hankelContinuation
  rw [norm_mul]
  have h2pi : ‖(-2 * (π : ℂ))‖ = 2 * π := by
    rw [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2pi]
  have hbd : ‖∫ t in Ioi (0 : ℝ), (g t : ℂ) *
      besselI0C (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))‖ ≤
      ∫ t in Ioi (0 : ℝ), |g t| * kernelK 1 (c' / 12) t := by
    refine norm_integral_le_of_norm_le hint ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact besselI0C_strip_le hc0 (le_of_lt ht) hb
  calc 2 * π * _ ≤ 2 * π * (2 * exp 92 * c' ^ 2 * virasoroProblem.cardyNorm (c' / 12) g) := by
        gcongr
        exact hbd.trans hle
    _ = 4 * π * exp 92 * c' ^ 2 * virasoroProblem.cardyNorm (c' / 12) g := by ring

/-- info: 'FormalResearch.ModularBootstrap.Integration.lemmaB_d_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaB_d_sup

end FormalResearch.ModularBootstrap.Integration
