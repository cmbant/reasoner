module

public import FormalResearch.SignUncertainty.HankelBesselData
public import FormalResearch.SignUncertainty.HankelBesselMoments
public import FormalResearch.SignUncertainty.SignSeparation

/-!
# Laguerre modes of the concrete Hankel transform (`gt:7.9b`)

For `c > 0`, with `𝓗_c` the Hankel transform with kernel `hankelPhi c`:

* `hankelTransform_exp`: `𝓗_c e^{-2πs} = e^{-2πΔ}` (eigenvalue `+1`);
* `hankelTransform_linear_exp`: `𝓗_c (s e^{-2πs}) = (c/(2π) - Δ) e^{-2πΔ}`;
* `hankelTransform_oddLaguerreMode`: `𝓗_c u₀ = -u₀` for `u₀(Δ) = (4πΔ/c - 1) e^{-2πΔ}`
  (eigenvalue `-1`);
* `isRadialEigenfn_exp`, `isRadialEigenfn_oddLaguerreMode`: membership in `𝒜_c^{±1}` for every
  `K : HankelKernelData c` whose kernel is `hankelPhi c`.  The second discharges the hypothesis
  `hu₀` of `active_origin_constraint` for the concrete kernel.

Proof: expand `φ_c` in its power series, integrate termwise against
`s^a e^{-2πs} ρ₀(s)` (Gamma integrals) and sum the exponential series.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real Nat

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### The eigenvalue statements for `HankelKernelData` with kernel `hankelPhi c` -/

/-- **Eigenvalue `+1`:** `𝓗_c e^{-2πs} = e^{-2πΔ}` for `Δ ≥ 0`. -/
theorem hankelTransform_exp {c : ℝ} (hc : 0 < c) (K : HankelKernelData c) (hK : K.φ = hankelPhi c)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    hankelTransform c K (fun s => Real.exp (-(2 * π * s))) Δ = Real.exp (-(2 * π * Δ)) := by
  unfold hankelTransform
  rw [hK]
  exact integral_hankel_exp hc hΔ

/-- `𝓗_c (s e^{-2πs}) = (c/(2π) - Δ) e^{-2πΔ}` for `Δ ≥ 0`. -/
theorem hankelTransform_linear_exp {c : ℝ} (hc : 0 < c) (K : HankelKernelData c)
    (hK : K.φ = hankelPhi c) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    hankelTransform c K (fun s => s * Real.exp (-(2 * π * s))) Δ =
      (c / (2 * π) - Δ) * Real.exp (-(2 * π * Δ)) := by
  unfold hankelTransform
  rw [hK]
  exact integral_hankel_linear_exp hc hΔ

lemma oddLaguerreMode_eq (c : ℝ) :
    oddLaguerreMode c = fun s => (4 * π / c) * (s * Real.exp (-(2 * π * s))) -
      Real.exp (-(2 * π * s)) := by
  funext s
  unfold oddLaguerreMode
  rw [show -2 * π * s = -(2 * π * s) by ring]
  ring

/-- **Eigenvalue `-1`** (`gt:7.9b`): `𝓗_c u₀ = -u₀` for `u₀(Δ) = (4πΔ/c - 1) e^{-2πΔ}`. -/
theorem hankelTransform_oddLaguerreMode {c : ℝ} (hc : 0 < c) (K : HankelKernelData c)
    (hK : K.φ = hankelPhi c) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    hankelTransform c K (oddLaguerreMode c) Δ = -oddLaguerreMode c Δ := by
  have hI0 := hankelTransform_integrand_integrableOn (K := K) (integrableOn_exp_rho0 hc) hΔ
  have hI1 := hankelTransform_integrand_integrableOn (K := K) (integrableOn_linear_exp_rho0 hc) hΔ
  have h0 := hankelTransform_exp hc K hK hΔ
  have h1 := hankelTransform_linear_exp hc K hK hΔ
  unfold hankelTransform at h0 h1 ⊢
  rw [oddLaguerreMode_eq]
  have e : (fun s : ℝ => ((4 * π / c) * (s * Real.exp (-(2 * π * s))) - Real.exp (-(2 * π * s))) *
        hankelRho0 c s * K.φ (Δ * s)) = fun s =>
      (4 * π / c) * (s * Real.exp (-(2 * π * s)) * hankelRho0 c s * K.φ (Δ * s)) -
        Real.exp (-(2 * π * s)) * hankelRho0 c s * K.φ (Δ * s) := by
    funext s; ring
  rw [e, integral_sub (hI1.const_mul _) hI0, integral_const_mul, h0, h1]
  simp only
  have hc0 : c ≠ 0 := hc.ne'
  field_simp
  ring

/-- `e^{-2πΔ} ∈ 𝒜_c^{+1}` for every kernel data with `φ = hankelPhi c`. -/
theorem isRadialEigenfn_exp {c : ℝ} (hc : 0 < c) (K : HankelKernelData c) (hK : K.φ = hankelPhi c) :
    IsRadialEigenfn c K 1 (fun s => Real.exp (-(2 * π * s))) where
  cont := by fun_prop
  int := integrableOn_exp_rho0 hc
  eigen Δ hΔ := by rw [hankelTransform_exp hc K hK hΔ, one_mul]

/-- `u₀ = (4πΔ/c - 1) e^{-2πΔ} ∈ 𝒜_c^{-1}` for every kernel data with `φ = hankelPhi c`;
this discharges the hypothesis `hu₀` of `active_origin_constraint`. -/
theorem isRadialEigenfn_oddLaguerreMode {c : ℝ} (hc : 0 < c) (K : HankelKernelData c)
    (hK : K.φ = hankelPhi c) : IsRadialEigenfn c K (-1) (oddLaguerreMode c) where
  cont := (oddLaguerreMode_continuous c).continuousOn
  int := by
    rw [oddLaguerreMode_eq]
    have h : IntegrableOn (fun s : ℝ => (4 * π / c) * (s * Real.exp (-(2 * π * s)) * hankelRho0 c s) -
        Real.exp (-(2 * π * s)) * hankelRho0 c s) (Ioi 0) :=
      ((integrableOn_linear_exp_rho0 hc).const_mul (4 * π / c)).sub (integrableOn_exp_rho0 hc)
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only
    ring
  eigen Δ hΔ := by
    rw [hankelTransform_oddLaguerreMode hc K hK hΔ]
    ring


/-! ### Unconditional forms for the concrete transform `besselHankelTransform` -/

/-- `𝓗_c e^{-2πs} = e^{-2πΔ}` for the concrete transform. -/
theorem besselHankelTransform_exp {c : ℝ} (hc : 0 < c) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    besselHankelTransform c (fun s => Real.exp (-(2 * π * s))) Δ = Real.exp (-(2 * π * Δ)) :=
  integral_hankel_exp hc hΔ

/-- `𝓗_c u₀ = -u₀` for the concrete transform (`c > 1/2`), `u₀ = (4πΔ/c - 1) e^{-2πΔ}`. -/
theorem besselHankelTransform_oddLaguerreMode {c : ℝ} (hc : 1 / 2 < c) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    besselHankelTransform c (oddLaguerreMode c) Δ = -oddLaguerreMode c Δ := by
  have hc0 : 0 < c := by linarith
  have hI0 := integrableOn_mul_hankelKernel hc (integrableOn_exp_rho0 hc0) Δ
  have hI1 := integrableOn_mul_hankelKernel hc (integrableOn_linear_exp_rho0 hc0) Δ
  have h0 : ∫ s in Ioi (0 : ℝ), Real.exp (-(2 * π * s)) * hankelRho0 c s * hankelKernel c Δ s =
      Real.exp (-(2 * π * Δ)) := integral_hankel_exp hc0 hΔ
  have h1 : ∫ s in Ioi (0 : ℝ), s * Real.exp (-(2 * π * s)) * hankelRho0 c s *
      hankelKernel c Δ s = (c / (2 * π) - Δ) * Real.exp (-(2 * π * Δ)) :=
    integral_hankel_linear_exp hc0 hΔ
  unfold besselHankelTransform
  rw [oddLaguerreMode_eq]
  have e : (fun s : ℝ => ((4 * π / c) * (s * Real.exp (-(2 * π * s))) - Real.exp (-(2 * π * s))) *
        hankelRho0 c s * hankelKernel c Δ s) = fun s =>
      (4 * π / c) * (s * Real.exp (-(2 * π * s)) * hankelRho0 c s * hankelKernel c Δ s) -
        Real.exp (-(2 * π * s)) * hankelRho0 c s * hankelKernel c Δ s := by
    funext s; ring
  rw [e, integral_sub (hI1.const_mul _) hI0, integral_const_mul, h0, h1]
  simp only
  have hcne : c ≠ 0 := hc0.ne'
  field_simp
  ring

/-! ### The concrete kernel data -/

/-- `e^{-2πΔ} ∈ 𝒜_c^{+1}` for the concrete kernel data (`c > 1/2`). -/
theorem isRadialEigenfn_exp_bessel {c : ℝ} (hc : 1 / 2 < c) :
    IsRadialEigenfn c (hankelKernelData hc) 1 (fun s => Real.exp (-(2 * π * s))) :=
  isRadialEigenfn_exp (by linarith) _ rfl

/-- `u₀ ∈ 𝒜_c^{-1}` for the concrete kernel data (`c > 1/2`): the hypothesis `hu₀` of
`active_origin_constraint` holds for the concrete Hankel kernel. -/
theorem isRadialEigenfn_oddLaguerreMode_bessel {c : ℝ} (hc : 1 / 2 < c) :
    IsRadialEigenfn c (hankelKernelData hc) (-1) (oddLaguerreMode c) :=
  isRadialEigenfn_oddLaguerreMode (by linarith) _ rfl

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.hankelTransform_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelTransform_exp

/-- info: 'FormalResearch.SignUncertainty.hankelTransform_oddLaguerreMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelTransform_oddLaguerreMode

/-- info: 'FormalResearch.SignUncertainty.isRadialEigenfn_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isRadialEigenfn_exp

/-- info: 'FormalResearch.SignUncertainty.isRadialEigenfn_oddLaguerreMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isRadialEigenfn_oddLaguerreMode

/-- info: 'FormalResearch.SignUncertainty.besselHankelTransform_oddLaguerreMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselHankelTransform_oddLaguerreMode

/-- info: 'FormalResearch.SignUncertainty.isRadialEigenfn_oddLaguerreMode_bessel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isRadialEigenfn_oddLaguerreMode_bessel

end FormalResearch.SignUncertainty
