module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import DLMF.ParabolicCylinder.ElementaryPropertiesCore
public import DLMF.Confluent.ParabolicCylinder.WronskiansAndConnections

/-!
# Paper J, Layer 4 (phase B1): the exact identities of the actual parabolic cylinder functions

`pcU a z := Re U(a, z)` and `pcV a z := Re V(a, z)`, where `U, V` are the complex Weber functions of the vendored
lean-DLMF closure (`DLMF.Confluent.parabolicCylinderU/V`, DLMF 12.4.1-2, series definitions with reciprocal Gamma factors, so
that `V` is entire in `a`).  **No rescaling**: the normalisation is DLMF 12.2 and that of `ParabolicCylinderFacts`
(`Wr{U, V} = sqrt(2/pi)`).  For real `a, z` both are real (`parabolicCylinderU_real`, `parabolicCylinderV_real`), so
`pcU a z` is `U(a, z)`; derivatives of the real restriction are `Re` of the complex derivatives (`HasDerivAt.real_of_complex`).

Proved here (all unconditional, for every real `a, z`, from the vendored DLMF 12.2.2, 12.2.10, 12.2.15-16, 12.8.2-3, 12.8.6-7):
`pcU_ode`, `pcV_ode`, `pc_wronsk`, `pc_shift_U_up`, `pc_shift_U_dn`, `pc_shift_V_up`, `pc_shift_V_dn`, `pc_reflect` (`a <= 0`),
`pc_reflect_V`, with the Gamma bridge `pi_div_Gamma_half_add : a <= 0 -> pi / Gamma(1/2 + a) = cos(pi a) Gamma(1/2 - a)` (both sides
vanish at the half-integers `a = -n - 1/2`).  The bridge is false for `a = n + 1/2 > 0` (`not_pi_div_Gamma_half_add_half`), which is why
`reflect` is stated for `a <= 0` only.  `reflect_V` holds for every real `a` and needs no bridge.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open DLMF.Confluent

def pcU (a z : ℝ) : ℝ := (parabolicCylinderU a z).re
def pcV (a z : ℝ) : ℝ := (parabolicCylinderV a z).re

lemma pcU_ofReal (a z : ℝ) : parabolicCylinderU a z = (pcU a z : ℂ) :=
  Complex.ext (by simp [pcU]) (by simp [pcU, parabolicCylinderU_real])
lemma pcV_ofReal (a z : ℝ) : parabolicCylinderV a z = (pcV a z : ℂ) :=
  Complex.ext (by simp [pcV]) (by simp [pcV, parabolicCylinderV_real])

/-- real part of `U'(a, x)`. -/
def pcUD (a z : ℝ) : ℝ := (parabolicCylinderUDeriv a z).re
/-- real part of `V'(a, x)`. -/
def pcVD (a z : ℝ) : ℝ := (parabolicCylinderVDeriv a z).re

lemma hasDerivAt_pcU (a z : ℝ) :
    HasDerivAt (pcU a) (pcUD a z) z :=
  (hasDerivAt_parabolicCylinderU (a:ℂ) (z:ℂ)).real_of_complex
lemma hasDerivAt_pcV (a z : ℝ) :
    HasDerivAt (pcV a) (pcVD a z) z :=
  (hasDerivAt_parabolicCylinderV (a:ℂ) (z:ℂ)).real_of_complex

lemma deriv_pcU (a : ℝ) : deriv (pcU a) = pcUD a :=
  funext fun z => (hasDerivAt_pcU a z).deriv
lemma deriv_pcV (a : ℝ) : deriv (pcV a) = pcVD a :=
  funext fun z => (hasDerivAt_pcV a z).deriv

lemma hasDerivAt_pcUD (a z : ℝ) :
    HasDerivAt (pcUD a) ((z ^ 2 / 4 + a) * pcU a z) z := by
  have h := (hasDerivAt_parabolicCylinderUDeriv (a:ℂ) (z:ℂ)).real_of_complex
  have e : (((z:ℂ) ^ 2 / 4 + (a:ℂ)) * parabolicCylinderU a z).re = (z ^ 2 / 4 + a) * pcU a z := by
    rw [pcU_ofReal]
    have : ((z:ℂ) ^ 2 / 4 + (a:ℂ)) * ((pcU a z : ℝ) : ℂ) = (((z ^ 2 / 4 + a) * pcU a z : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  rwa [e] at h
lemma hasDerivAt_pcVD (a z : ℝ) :
    HasDerivAt (pcVD a) ((z ^ 2 / 4 + a) * pcV a z) z := by
  have h := (hasDerivAt_parabolicCylinderVDeriv (a:ℂ) (z:ℂ)).real_of_complex
  have e : (((z:ℂ) ^ 2 / 4 + (a:ℂ)) * parabolicCylinderV a z).re = (z ^ 2 / 4 + a) * pcV a z := by
    rw [pcV_ofReal]
    have : ((z:ℂ) ^ 2 / 4 + (a:ℂ)) * ((pcV a z : ℝ) : ℂ) = (((z ^ 2 / 4 + a) * pcV a z : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  rwa [e] at h

theorem pcU_ode (a z : ℝ) : deriv (deriv (pcU a)) z = (z ^ 2 / 4 + a) * pcU a z := by
  rw [deriv_pcU]; exact (hasDerivAt_pcUD a z).deriv
theorem pcV_ode (a z : ℝ) : deriv (deriv (pcV a)) z = (z ^ 2 / 4 + a) * pcV a z := by
  rw [deriv_pcV]; exact (hasDerivAt_pcVD a z).deriv

theorem pc_wronsk (a z : ℝ) :
    pcU a z * deriv (pcV a) z - deriv (pcU a) z * pcV a z = Real.sqrt (2 / Real.pi) := by
  have h := congrArg Complex.re (parabolicCylinderV_wronskian (a:ℂ) (z:ℂ))
  rw [deriv_parabolicCylinderV, deriv_parabolicCylinderU] at h
  simp only [Complex.sub_re, Complex.mul_re, parabolicCylinderU_real, parabolicCylinderV_real,
    mul_zero, zero_mul, sub_zero, Complex.ofReal_re] at h
  rw [deriv_pcU, deriv_pcV]
  exact h

theorem pc_shift_U_up (a z : ℝ) :
    deriv (pcU a) z + z / 2 * pcU a z + (a + 1 / 2) * pcU (a + 1) z = 0 := by
  have h := congrArg Complex.re (parabolicCylinderU_recurrence_add (a:ℂ) (z:ℂ))
  have e := pcU_ofReal (a + 1) z
  push_cast at e
  rw [e, pcU_ofReal] at h
  rw [deriv_parabolicCylinderU] at h
  rw [deriv_pcU]
  simpa [Complex.add_re, Complex.mul_re, pcUD] using h

theorem pc_shift_U_dn (a z : ℝ) :
    deriv (pcU a) z - z / 2 * pcU a z + pcU (a - 1) z = 0 := by
  have h := congrArg Complex.re (parabolicCylinderU_recurrence_sub (a:ℂ) (z:ℂ))
  have e := pcU_ofReal (a - 1) z
  push_cast at e
  rw [e, pcU_ofReal] at h
  rw [deriv_parabolicCylinderU] at h
  rw [deriv_pcU]
  simpa [Complex.add_re, Complex.mul_re, pcUD] using h

theorem pc_shift_V_up (a z : ℝ) :
    deriv (pcV a) z + z / 2 * pcV a z - pcV (a + 1) z = 0 := by
  have h := congrArg Complex.re (parabolicCylinderV_recurrence_add (a:ℂ) (z:ℂ))
  have e := pcV_ofReal (a + 1) z
  push_cast at e
  rw [e, pcV_ofReal] at h
  rw [deriv_parabolicCylinderV] at h
  rw [deriv_pcV]
  simpa [Complex.add_re, Complex.mul_re, pcVD] using h

theorem pc_shift_V_dn (a z : ℝ) :
    deriv (pcV a) z - z / 2 * pcV a z - (a - 1 / 2) * pcV (a - 1) z = 0 := by
  have h := congrArg Complex.re (parabolicCylinderV_recurrence_sub (a:ℂ) (z:ℂ))
  have e := pcV_ofReal (a - 1) z
  push_cast at e
  rw [e, pcV_ofReal] at h
  rw [deriv_parabolicCylinderV] at h
  rw [deriv_pcV]
  simpa [Complex.add_re, Complex.mul_re, pcVD] using h


/-- The Gamma bridge `pi / Gamma(1/2 + a) = cos(pi a) Gamma(1/2 - a)` for `a <= 0` (including the half-integers
`a = -n - 1/2`, where both sides vanish).  False for `a = n + 1/2 > 0`. -/
lemma pi_div_Gamma_half_add {a : ℝ} (ha : a ≤ 0) :
    Real.pi / Real.Gamma (1 / 2 + a) = Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) := by
  by_cases hc : Real.cos (Real.pi * a) = 0
  · rw [hc, zero_mul]
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc
    have hak : a = k + 1 / 2 := by
      have := Real.pi_pos
      field_simp at hk ⊢
      nlinarith
    have hk0 : (k : ℝ) < 0 := by linarith
    have hk0' : k < 0 := by exact_mod_cast hk0
    have hk2 : k + 1 ≤ 0 := by omega
    have hg : Real.Gamma (1 / 2 + a) = 0 := by
      have : (1 / 2 + a) = -((((-(k + 1)).toNat : ℕ)) : ℝ) := by
        have : (((-(k + 1)).toNat : ℕ) : ℤ) = -(k + 1) := Int.toNat_of_nonneg (by omega)
        have h2 : ((((-(k + 1)).toNat : ℕ)) : ℝ) = -((k : ℝ) + 1) := by
          exact_mod_cast this
        rw [h2, hak]; ring
      rw [this]; exact Real.Gamma_neg_nat_eq_zero _
    rw [hg, div_zero]
  · have h1 := Real.Gamma_mul_Gamma_one_sub (1 / 2 + a)
    have hs : Real.sin (Real.pi * (1 / 2 + a)) = Real.cos (Real.pi * a) := by
      rw [show Real.pi * (1 / 2 + a) = Real.pi * a + Real.pi / 2 by ring, Real.sin_add_pi_div_two]
    rw [hs, show 1 - (1 / 2 + a) = 1 / 2 - a by ring] at h1
    have hg : Real.Gamma (1 / 2 + a) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact (div_ne_zero Real.pi_ne_zero hc) h1.symm
    rw [div_eq_iff hg]
    have h5 := (eq_div_iff hc).mp h1
    linarith

theorem pc_reflect (a : ℝ) (ha : a ≤ 0) (z : ℝ) :
    pcU a (-z) = -Real.sin (Real.pi * a) * pcU a z
      + Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * pcV a z := by
  have h := parabolicCylinderU_neg_eq (a:ℂ) (z:ℂ)
  have e := pcU_ofReal a (-z)
  push_cast at e
  rw [e, pcU_ofReal, pcV_ofReal] at h
  have g : Complex.Gamma (1 / 2 + (a:ℂ)) = ((Real.Gamma (1 / 2 + a) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  rw [g] at h
  have hb := pi_div_Gamma_half_add ha
  have h2 : ((Real.pi : ℂ) / ((Real.Gamma (1 / 2 + a) : ℝ) : ℂ)) =
      ((Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) : ℝ) : ℂ) := by
    rw [← hb]; push_cast; rfl
  rw [h2] at h
  have h3 : Complex.sin (Real.pi * (a:ℂ)) = ((Real.sin (Real.pi * a) : ℝ) : ℂ) := by push_cast; rfl
  rw [h3] at h
  exact_mod_cast h

theorem pc_reflect_V (a : ℝ) (z : ℝ) :
    pcV a (-z) = Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a) * pcU a z
      + Real.sin (Real.pi * a) * pcV a z := by
  have h := parabolicCylinderV_neg_eq (a:ℂ) (z:ℂ)
  have e := pcV_ofReal a (-z)
  push_cast at e
  rw [e, pcU_ofReal, pcV_ofReal] at h
  have g : Complex.Gamma (1 / 2 - (a:ℂ)) = ((Real.Gamma (1 / 2 - a) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  rw [g] at h
  have h3 : Complex.sin (Real.pi * (a:ℂ)) = ((Real.sin (Real.pi * a) : ℝ) : ℂ) := by push_cast; rfl
  have h4 : Complex.cos (Real.pi * (a:ℂ)) = ((Real.cos (Real.pi * a) : ℝ) : ℂ) := by push_cast; rfl
  rw [h3, h4] at h
  exact_mod_cast h

/-- Negative regression: the Gamma bridge fails at `a = 1/2` (`pi / Gamma 1 = pi`, but `cos (pi/2) Gamma 0 = 0`). -/
lemma not_pi_div_Gamma_half_add_half :
    ¬ Real.pi / Real.Gamma (1 / 2 + 1 / 2) = Real.cos (Real.pi * (1 / 2)) * Real.Gamma (1 / 2 - 1 / 2) := by
  intro h
  have h1 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have h2 : Real.cos (Real.pi * (1 / 2)) = 0 := by
    rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring]; exact Real.cos_pi_div_two
  rw [h1, Real.Gamma_one, h2, zero_mul, div_one] at h
  exact Real.pi_ne_zero h


/-- **The exact part of `ParabolicCylinderFacts` holds for the actual functions**: `PCExactFacts pcU pcV`. -/
theorem pcExactFacts : PCExactFacts pcU pcV where
  ode_U := pcU_ode
  ode_V := pcV_ode
  wronsk := pc_wronsk
  shift_U_up := pc_shift_U_up
  shift_U_dn := pc_shift_U_dn
  shift_V_dn := pc_shift_V_dn
  shift_V_up := pc_shift_V_up
  reflect := fun a ha z => pc_reflect a ha z
  reflect_V := fun a _ z => pc_reflect_V a z


/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcU_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcU_ode

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcV_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcV_ode

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_wronsk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_wronsk

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_shift_U_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_shift_U_up

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_shift_U_dn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_shift_U_dn

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_shift_V_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_shift_V_up

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_shift_V_dn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_shift_V_dn

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pi_div_Gamma_half_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pi_div_Gamma_half_add

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_reflect

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_reflect_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_reflect_V

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcExactFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcExactFacts


end FormalResearch.JacobiEigenvectors.Charts
