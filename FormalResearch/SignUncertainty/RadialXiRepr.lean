module

public import FormalResearch.SignUncertainty.RadialKernelLimit
public import FormalResearch.SignUncertainty.MellinInversion
public import FormalResearch.SignUncertainty.MellinMajorantBound
public import FormalResearch.SignUncertainty.MellinStripAnalytic

/-!
# The rescaled window profile as a Mellin integral (`lem:radial-compactness`, Step 3)

`radialW c f w = e^{-c ℋ̂(ε_c w)} M̃_f(c(1 - ε_c w))` is holomorphic on `0 < Re w`, `ε_c Re w < 1`, bounded by
`M[f] |1+ε_c w|^{1/2} e^{1/(6c)}` for `Re w ≥ 0`, and
`Ξ_c(s) = c^{1/3} ρ₀(cξ) f(cξ) = (2π ξ)^{-1} ∫ K_c(1+iv, s) W_c(1+iv) dv`, `ξ = ξ_c(s)` (`radial_xi_repr`),
from Mellin inversion `mellin_inversion_f` and the exact kernel identity `mellin_strip_kernel_eq`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma cpow_ofReal_pos_eq_exp {a : ℝ} (ha : 0 < a) (u : ℂ) :
    (a : ℂ) ^ u = Complex.exp (u * (Real.log a : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'), mul_comm, Complex.ofReal_log ha.le]

/-- `ρ₀(Δ) · Δ^{-z} · ∫ f Δ^{z-1} = Δ⁻¹ Γ(z)/Γ(c) (2πΔ)^{c-z} M̃_f(z)`. -/
lemma rho0_mul_term (f : ℝ → ℝ) {c Δ : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) {z : ℂ} (hz : 0 < z.re) :
    ((hankelRho0 c Δ : ℝ) : ℂ) * ((Δ : ℂ) ^ (-z) * mellinRaw f z) =
      (Δ : ℂ)⁻¹ * (Complex.Gamma z / Complex.Gamma (c : ℂ)) *
        ((2 * Real.pi * Δ : ℝ) : ℂ) ^ ((c : ℂ) - z) * mellinStrip f z := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hrho : ((hankelRho0 c Δ : ℝ) : ℂ) = Complex.exp ((c : ℂ) * (Real.log (2 * Real.pi) : ℂ)) /
      Complex.Gamma (c : ℂ) * Complex.exp (((c : ℂ) - 1) * (Real.log Δ : ℂ)) := by
    unfold hankelRho0
    push_cast
    rw [Complex.ofReal_cpow hpi.le, Complex.ofReal_cpow hΔ.le, cpow_ofReal_pos_eq_exp hpi,
      cpow_ofReal_pos_eq_exp hΔ, Complex.Gamma_ofReal]
    push_cast; ring_nf
  have hΓz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hraw : mellinRaw f z = mellinStrip f z * Complex.Gamma z / Complex.exp (z * (Real.log (2 * Real.pi) : ℂ)) := by
    unfold mellinStrip
    rw [cpow_ofReal_pos_eq_exp hpi]
    field_simp
  have hmul : ((2 * Real.pi * Δ : ℝ) : ℂ) ^ ((c : ℂ) - z) =
      Complex.exp (((c : ℂ) - z) * ((Real.log (2 * Real.pi) : ℂ) + (Real.log Δ : ℂ))) := by
    rw [cpow_ofReal_pos_eq_exp (by positivity), Real.log_mul hpi.ne' hΔ.ne']; push_cast; rfl
  have hinv : (Δ : ℂ)⁻¹ = Complex.exp (-(Real.log Δ : ℂ)) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hΔ]
  have hE : Complex.exp ((c : ℂ) * (Real.log (2 * Real.pi) : ℂ)) * Complex.exp (((c : ℂ) - 1) * (Real.log Δ : ℂ)) *
      Complex.exp (-z * (Real.log Δ : ℂ)) / Complex.exp (z * (Real.log (2 * Real.pi) : ℂ)) =
      Complex.exp (-(Real.log Δ : ℂ)) *
        Complex.exp (((c : ℂ) - z) * ((Real.log (2 * Real.pi) : ℂ) + (Real.log Δ : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub, ← Complex.exp_add]
    congr 1; ring
  have hpow : (Δ : ℂ) ^ (-z) = Complex.exp (-z * (Real.log Δ : ℂ)) := cpow_ofReal_pos_eq_exp hΔ _
  have hΓc : Complex.Gamma (c : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hc)
  rw [hrho, hraw, hpow, hmul, hinv]
  have : Complex.exp ((c : ℂ) * (Real.log (2 * Real.pi) : ℂ)) / Complex.Gamma (c : ℂ) *
        Complex.exp (((c : ℂ) - 1) * (Real.log Δ : ℂ)) *
      (Complex.exp (-z * (Real.log Δ : ℂ)) *
        (mellinStrip f z * Complex.Gamma z / Complex.exp (z * (Real.log (2 * Real.pi) : ℂ)))) =
      (Complex.exp ((c : ℂ) * (Real.log (2 * Real.pi) : ℂ)) * Complex.exp (((c : ℂ) - 1) * (Real.log Δ : ℂ)) *
        Complex.exp (-z * (Real.log Δ : ℂ)) / Complex.exp (z * (Real.log (2 * Real.pi) : ℂ))) *
        (Complex.Gamma z / Complex.Gamma (c : ℂ) * mellinStrip f z) := by
    field_simp
  rw [this, hE]; ring

/-- `W_c(w) = e^{-c ℋ̂(ε_c w)} M̃_f(c (1 - ε_c w))`. -/
noncomputable def radialW (c : ℝ) (f : ℝ → ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-((c : ℂ) * hInt ((radialEps c : ℂ) * w))) *
    mellinStrip f ((c : ℂ) * (1 - (radialEps c : ℂ) * w))

lemma radialW_norm_le {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {w : ℂ} (hw0 : 0 ≤ w.re) (hw1 : radialEps c * w.re < 1) :
    ‖radialW c f w‖ ≤ hankelMass c f * ‖1 + (radialEps c : ℂ) * w‖ ^ (1 / 2 : ℝ) *
      Real.exp (1 / (6 * c)) := by
  have hc0 : 0 < c := by linarith
  have he0 := radialEps_pos hc0
  have hre : ((radialEps c : ℂ) * w).re = radialEps c * w.re := by simp
  have h := norm_mellinStrip_le_majorant hc hf hε (ζ := (radialEps c : ℂ) * w)
    (by rw [hre]; positivity) (by rw [hre]; exact hw1)
  unfold radialW
  rw [norm_mul, Complex.norm_exp]
  have hre2 : (-((c : ℂ) * hInt ((radialEps c : ℂ) * w))).re = -(c * (hInt ((radialEps c : ℂ) * w)).re) := by
    simp
  rw [hre2]
  calc Real.exp (-(c * (hInt ((radialEps c : ℂ) * w)).re)) *
        ‖mellinStrip f ((c : ℂ) * (1 - (radialEps c : ℂ) * w))‖
      ≤ Real.exp (-(c * (hInt ((radialEps c : ℂ) * w)).re)) *
        (hankelMass c f * ‖1 + (radialEps c : ℂ) * w‖ ^ (1 / 2 : ℝ) *
          Real.exp (c * (hInt ((radialEps c : ℂ) * w)).re + 1 / (6 * c))) := by gcongr
    _ = hankelMass c f * ‖1 + (radialEps c : ℂ) * w‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c)) := by
        rw [Real.exp_add]
        have : Real.exp (-(c * (hInt ((radialEps c : ℂ) * w)).re)) *
            Real.exp (c * (hInt ((radialEps c : ℂ) * w)).re) = 1 := by
          rw [← Real.exp_add]; simp
        calc _ = (Real.exp (-(c * (hInt ((radialEps c : ℂ) * w)).re)) *
            Real.exp (c * (hInt ((radialEps c : ℂ) * w)).re)) *
            (hankelMass c f * ‖1 + (radialEps c : ℂ) * w‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c))) := by ring
          _ = _ := by rw [this, one_mul]

lemma radialW_differentiableOn {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    DifferentiableOn ℂ (radialW c f) {w : ℂ | 0 < w.re ∧ radialEps c * w.re < 1} := by
  have he0 := radialEps_pos hc
  have hlin : DifferentiableOn ℂ (fun w : ℂ => (radialEps c : ℂ) * w)
      {w : ℂ | 0 < w.re ∧ radialEps c * w.re < 1} := by fun_prop
  have hH : DifferentiableOn ℂ (fun w : ℂ => hInt ((radialEps c : ℂ) * w))
      {w : ℂ | 0 < w.re ∧ radialEps c * w.re < 1} := by
    refine differentiableOn_hInt.comp hlin (fun w hw => ?_)
    have hre : ((radialEps c : ℂ) * w).re = radialEps c * w.re := by simp
    refine ⟨?_, ?_⟩ <;> simp only [hre] <;> nlinarith [hw.1, hw.2]
  have hlin2 : DifferentiableOn ℂ (fun w : ℂ => (c : ℂ) * (1 - (radialEps c : ℂ) * w))
      {w : ℂ | 0 < w.re ∧ radialEps c * w.re < 1} := by fun_prop
  have hM : DifferentiableOn ℂ (fun w : ℂ => mellinStrip f ((c : ℂ) * (1 - (radialEps c : ℂ) * w)))
      {w : ℂ | 0 < w.re ∧ radialEps c * w.re < 1} := by
    refine (differentiableOn_mellinStrip hc hf).comp hlin2 (fun w hw => ?_)
    have hre : ((c : ℂ) * (1 - (radialEps c : ℂ) * w)).re = c * (1 - radialEps c * w.re) := by simp
    refine ⟨?_, ?_⟩ <;> simp only [hre] <;> nlinarith [hw.1, hw.2, mul_pos he0 hw.1]
  exact ((hH.const_mul (c : ℂ)).neg.cexp).mul hM

/-- info: 'FormalResearch.SignUncertainty.radialW_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radialW_norm_le

/-- info: 'FormalResearch.SignUncertainty.radialW_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radialW_differentiableOn

end FormalResearch.SignUncertainty
