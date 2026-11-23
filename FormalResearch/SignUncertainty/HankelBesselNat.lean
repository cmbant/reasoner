module

public import FormalResearch.SignUncertainty.HankelBessel
public import FormalResearch.ModularBootstrap.Upper.Hankel.BesselJNat

/-!
# The concrete Hankel kernel at integer `c`: agreement with the natural-order Bessel function

For `c = p + 1` (`p : ℕ`, i.e. `d = 2c` even) the kernel `hankelKernel (p+1) Δ s` of `HankelBessel`
is `p! · S_p(-4π² Δ s)` with `S_p = besselSC p` the regularised Bessel series of
`ModularBootstrap/Upper/Hankel/BesselJNat.lean`, and so (by `besselJ_kernel_eq`)
`(2π s)^p K^{(p+1)}(t,s) = p! (s/t)^{p/2} J_p(4π√(s t))`.
-/

@[expose] public section

open Complex
open scoped Real Nat

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.WeightAxioms
  FormalResearch.ModularBootstrap.Upper.Hankel

/-- For `c = p + 1` the kernel is the entire series `p! S_p(-4π² Δ s)` (`Δ s ≥ 0`). -/
theorem hankelKernel_nat_eq (p : ℕ) {Δ s : ℝ} (h : 0 ≤ Δ * s) :
    ((hankelKernel ((p : ℝ) + 1) Δ s : ℝ) : ℂ) =
      (p ! : ℂ) * besselSC p (-(4 * (π : ℂ) ^ 2 * (Δ : ℂ) * (s : ℂ))) := by
  unfold hankelKernel hankelPhi
  rw [add_sub_cancel_right, besselNorm_ofReal_eq]
  have hsq : ((√(Δ * s) : ℝ) : ℂ) ^ 2 = (Δ : ℂ) * (s : ℂ) := by
    have := Real.sq_sqrt h
    exact_mod_cast this
  have e1 : -(((4 * π * √(Δ * s) : ℝ) : ℂ) / 2) ^ 2 =
      -(4 * (π : ℂ) ^ 2 * (Δ : ℂ) * (s : ℂ)) := by
    push_cast
    rw [show (4 * (π : ℂ) * ((√(Δ * s) : ℝ) : ℂ) / 2) ^ 2 =
      4 * (π : ℂ) ^ 2 * ((√(Δ * s) : ℝ) : ℂ) ^ 2 by ring, hsq]
    ring
  have hΓ : ((Real.Gamma ((p : ℝ) + 1) : ℝ) : ℂ) = (p ! : ℂ) := by
    rw [Real.Gamma_nat_eq_factorial, Complex.ofReal_natCast]
  rw [hΓ, e1]
  unfold besselSC
  push_cast
  rfl

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.hankelKernel_nat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelKernel_nat_eq

end FormalResearch.SignUncertainty
