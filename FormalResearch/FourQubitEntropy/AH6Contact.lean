import Mathlib

/-!
# The contact algebra of AH-6

The coefficients `α₀, α₁, β₀` of `H` are fixed so that `H - (f(λ)+f(μ))/2` has value and gradient zero at
`(λ,μ) = (b,c)`, i.e. `(e,v) = (e₀,v₀)` (paper: "Substitution in the three formulas for `β₀,α₁,α₀` gives the value and
both first derivatives at `(b,c)`", AH-6b).  Together with the exact values of the binary minorant at `z = 1/9`
(`Φ(1/9) = (5/3) ln 2 - ln 3`, `Φ'(1/9) = (3/4) ln 2`, built into `η₂, η₃`) this makes the cubic
`F(e₀,·)` have a double root at `v₀` and `F_e(e₀,v₀) = 0`.  `contact_algebra` verifies the three identities
`F = F_v = F_e = 0` at `(e₀, v₀)` as a rational-function identity in the atoms
`u, ln c, ln 2, ln 3, k₀, γ, q(e₀), q'(e₀)` (all other quantities are the model's definitions); no numerical input.
-/

namespace FormalResearch.FourQubitEntropy.AH6

theorem contact_algebra {u lc l2 l3 k0 gam q0 q1 Pe0 Pd0 e0 v0 hh he hv a2 a3 b1 g0 g1 b0 a1 a0 eta2 eta3 : ℝ}
    (hu : u ≠ 0) (hq0 : q0 ≠ 0)
    (he0 : e0 = 48 * u) (hv0 : v0 = e0 * e0 / 9)
    (hhh : hh = (-(8 * u * (lc + l2)) + -(4 * u * lc)) / 2)
    (hhe : he = (-((lc + l2) + 1) + -(lc + 1)) / 16)
    (hhv : hv = (-((lc + l2) + 1) + (lc + 1)) / (512 * u))
    (ha2 : a2 = l2 * (-115001089107 / 1000000000000)) (ha3 : a3 = l2 * (18166193766 / 1000000000000))
    (hb1 : b1 = l2 * (14438812336 / 1000000000000))
    (hg0 : g0 = -(6 * (u * (lc + l3 - l2)))) (hg1 : g1 = -((lc + l3 - l2) + 1) / 8)
    (hPe0 : Pe0 = g0 + k0 * q0 ^ 2) (hPd0 : Pd0 = g1 - q0 ^ 2 * gam * k0 + 2 * k0 * q0 * q1)
    (hb0 : b0 = (v0 * hv + -hh + Pe0) / (v0 * v0) + -(b1 * e0))
    (ha1 : a1 = (he + -Pd0 + -(v0 * (v0 * b1))) / v0 + -(2 * (a2 * e0)) + -(3 * (a3 * (e0 * e0))))
    (ha0 : a0 = hv + -(2 * (v0 * (b0 + b1 * e0))) + -(a1 * e0) + -(a2 * (e0 * e0)) + -(a3 * (e0 * (e0 * e0))))
    (heta2 : eta2 = 1593 / 4 * l2 + -(243 * l3) + -9) (heta3 : eta3 = 81 / 2 + -(9477 / 4 * l2) + 1458 * l3) :
    let A0 := a0 + a1 * e0 + a2 * e0 ^ 2 + a3 * e0 ^ 3
    let A1 := a1 + 2 * a2 * e0 + 3 * a3 * e0 ^ 2
    let B0 := b0 + b1 * e0
    let U0 := 8 * k0 * q0 ^ 2
    let V0 := 1 / 2 + 8 * e0 * A0
    let V1 := 8 * (A0 + e0 * A1)
    let W0 := eta2 + 8 * e0 ^ 3 * B0
    let W1 := 8 * (3 * e0 ^ 2 * B0 + e0 ^ 3 * b1)
    (e0 ^ 5 * U0 + e0 ^ 4 * V0 * v0 + e0 ^ 2 * W0 * v0 ^ 2 + eta3 * v0 ^ 3 = 0) ∧
    (e0 ^ 4 * V0 + 2 * e0 ^ 2 * W0 * v0 + 3 * eta3 * v0 ^ 2 = 0) ∧
    (5 * e0 ^ 4 * U0 + e0 ^ 5 * (8 * k0 * (2 * q0 * q1)) +
      (4 * e0 ^ 3 * V0 + gam * e0 ^ 4 * V0 + e0 ^ 4 * V1) * v0 +
      (2 * e0 * W0 + gam * e0 ^ 2 * W0 + e0 ^ 2 * W1) * v0 ^ 2 + eta3 * gam * v0 ^ 3 = 0) := by
  intro A0 A1 B0 U0 V0 V1 W0 W1
  have hv0ne : v0 ≠ 0 := by
    rw [hv0, he0]; positivity
  simp only [A0, A1, B0, U0, V0, V1, W0, W1]
  subst ha0 ha1 hb0 hPe0 hPd0 hg0 hg1 hhh hhe hhv ha2 ha3 hb1 heta2 heta3
  subst hv0
  subst he0
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

end FormalResearch.FourQubitEntropy.AH6
