module

public import FormalResearch.ModularBootstrap.Crossing.SumRule
public import FormalResearch.ModularBootstrap.Bessel.KernelComparison

/-!
# Bridge between the `Crossing` kernels and the pure-Bessel development

`Crossing.Setup`/`Crossing.SumRule` define the concrete kernels `kernelK w α t`, `cardyV` and a
power-series `Crossing.besselI n z`; `Bessel.*` defines `Bessel.besselI`, `besselK α t = I₀(4π√(α t))`,
`besselV` and proves Lemma B (`vlo:Bessel`) for them.  The two definitions of `I_n` are different
Lean terms for the same power series.  This file proves that they agree and transfers the pure-Bessel
estimates of Lemma B to the concrete Virasoro kernel `kernelK 1 (c'/12)` and Cardy kernel
`virasoroProblem.cardyV (c'/12)`:

* `crossing_besselI_eq`: `Crossing.besselI n z = Bessel.besselI n z` (all `n`, `z`);
* `kernelK_one_eq_besselK`: `kernelK 1 α t = besselK α t` for `0 ≤ α t`;
* `virasoro_cardyV_eq_besselV`: `virasoroProblem.cardyV a t = besselV a t` for `a ≥ 2`, `t ≥ 0`;
* `virasoro_cardyV_ge`: `V(t) ≥ 8π⁴ t²` (Lemma B (a), `vlo:Bessel`);
* `kernelK_le_of_le_inv`, `kernelK_le_mul_cardyV`: the pure-Bessel part of Lemma B (d) for the
  concrete kernels (`K_a ≤ I₀(4π/√12)` for `t ≤ 1/c'`; `K_a ≤ e^{92} c'² V` for `t ≥ 1/c'`);
* `cardyV_le_two_exp`: `V(t) ≤ 2 e^{4π √(a t)}`.

Nothing is deleted from `Crossing` or `Bessel`: both definitions stay, and every statement of the two
developments is unchanged.
-/

@[expose] public section

open Real

namespace FormalResearch.ModularBootstrap.Integration

/-- The two power-series definitions of the modified Bessel function agree:
`Crossing.besselI n z = Bessel.besselI n z`. -/
theorem crossing_besselI_eq (n : ℕ) (z : ℝ) :
    Crossing.besselI n z = Bessel.besselI n z := by
  unfold Crossing.besselI Bessel.besselI Bessel.besselS Bessel.besselTerm
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h : (z / 2) ^ (2 * k + n) = (z / 2) ^ n * (z ^ 2 / 4) ^ k := by
    rw [pow_add, pow_mul, mul_comm]
    congr 2
    ring
  rw [h]
  ring

/-- `Crossing.kernelK 1 α t = Bessel.besselK α t = I₀(4π√(α t))` whenever `0 ≤ α t`. -/
theorem kernelK_one_eq_besselK {α t : ℝ} (h : 0 ≤ α * t) :
    Crossing.kernelK 1 α t = Bessel.besselK α t := by
  rw [Bessel.besselK_eq_besselS h]
  unfold Crossing.kernelK Crossing.kernelKTerm Bessel.besselS Bessel.besselTerm
  simp only [Nat.sub_self, pow_zero, one_mul, Nat.add_sub_cancel, add_zero]
  refine tsum_congr fun k => ?_
  rw [show 4 * π ^ 2 * α * t = 4 * π ^ 2 * (α * t) by ring]

/-- The Cardy kernel of the Virasoro problem is `besselV`:
`virasoroProblem.cardyV a t = K_a - 2K_{a-1} + K_{a-2} = besselV a t` for `a ≥ 2`, `t ≥ 0`. -/
theorem virasoro_cardyV_eq_besselV {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    Crossing.virasoroProblem.cardyV a t = Bessel.besselV a t := by
  rw [Crossing.virasoro_cardyV_eq, Bessel.besselV,
    kernelK_one_eq_besselK (by nlinarith), kernelK_one_eq_besselK (by nlinarith),
    kernelK_one_eq_besselK (by nlinarith)]

/-- Lemma B (a) for the concrete Cardy kernel: `V(t) ≥ 8π⁴ t²` for `a ≥ 2`, `t ≥ 0`. -/
theorem virasoro_cardyV_ge {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    8 * π ^ 4 * t ^ 2 ≤ Crossing.virasoroProblem.cardyV a t := by
  rw [virasoro_cardyV_eq_besselV ha ht]
  exact Bessel.besselV_ge ha ht

/-- `K_a(t) = I₀(4π√(a t))` for the concrete kernel `kernelK 1 a`, `a, t ≥ 0`. -/
theorem kernelK_one_eq_besselI0 {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    Crossing.kernelK 1 a t = Bessel.besselI0 (4 * π * √(a * t)) :=
  kernelK_one_eq_besselK (mul_nonneg ha ht)

/-- Lemma B (d), small `t`: `K_a(t) ≤ I₀(4π/√12)` for `0 ≤ t ≤ 1/c'`, `a = c'/12`. -/
theorem kernelK_le_of_le_inv {c' t : ℝ} (hc : 0 < c') (ht : 0 ≤ t) (ht' : t ≤ 1 / c') :
    Crossing.kernelK 1 (c' / 12) t ≤ Bessel.besselI0 (4 * π / √12) := by
  rw [kernelK_one_eq_besselK (by positivity)]
  exact Bessel.besselK_le_of_le_inv hc ht'

/-- Lemma B (d), pure-Bessel part for the concrete kernels: for `c' ≥ 1000` and `t ≥ 1/c'`,
`K_a(t) ≤ e^{92} c'² V(t)` with `K_a = kernelK 1 (c'/12)`, `V = virasoroProblem.cardyV (c'/12)`. -/
theorem kernelK_le_mul_cardyV {c' t : ℝ} (hc : 1000 ≤ c') (ht : 1 / c' ≤ t) :
    Crossing.kernelK 1 (c' / 12) t ≤
      exp 92 * c' ^ 2 * Crossing.virasoroProblem.cardyV (c' / 12) t := by
  have hc0 : 0 < c' := by linarith
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  rw [kernelK_one_eq_besselK (by positivity), virasoro_cardyV_eq_besselV ha ht0]
  exact Bessel.besselK_le_mul_besselV hc ht

/-- `V(t) ≤ 2 e^{4π√(a t)}` for `a ≥ 2`, `t ≥ 0` (from `V ≤ 2K_a` and `I₀(z) ≤ e^z`). -/
theorem cardyV_le_two_exp {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    Crossing.virasoroProblem.cardyV a t ≤ 2 * exp (4 * π * √(a * t)) := by
  have h1 := Crossing.virasoro_cardyV_le_two_Ka ha ht
  rw [kernelK_one_eq_besselI0 (by linarith) ht] at h1
  have h2 := Bessel.besselI0_le_exp (z := 4 * π * √(a * t)) (by positivity)
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Integration.crossing_besselI_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms crossing_besselI_eq

/-- info: 'FormalResearch.ModularBootstrap.Integration.virasoro_cardyV_eq_besselV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_cardyV_eq_besselV

/-- info: 'FormalResearch.ModularBootstrap.Integration.kernelK_le_mul_cardyV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelK_le_mul_cardyV

end FormalResearch.ModularBootstrap.Integration
