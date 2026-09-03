import Mathlib
import FormalResearch.Blaschke.WronskianAtomNonvanishing

namespace FormalResearch.Blaschke

open Complex

/-- A point strictly inside the unit disk cannot satisfy `conj z * z = 1`. -/
theorem one_sub_conj_mul_self_ne_zero_of_norm_lt_one
    (z : ℂ) (hz : ‖z‖ < 1) :
    1 - conj z * z ≠ 0 := by
  intro h
  have hprod : conj z * z = 1 := sub_eq_zero.mp h
  have hn := congrArg norm hprod
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  simp only [norm_mul, norm_conj, norm_one] at hn
  nlinarith

/-- Two points strictly inside the unit disk cannot be reciprocal-conjugate in
the sense `conj z * w = 1`. -/
theorem one_sub_conj_mul_ne_zero_of_norm_lt_one
    (z w : ℂ) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    1 - conj z * w ≠ 0 := by
  intro h
  have hprod : conj z * w = 1 := sub_eq_zero.mp h
  have hn := congrArg norm hprod
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  simp only [norm_mul, norm_conj, norm_one] at hn
  nlinarith

/-- Distinct finite Blaschke zeros strictly inside the disk give linearly
independent Wronskian atoms.  This removes the auxiliary diagonal/nonreciprocal
hypotheses from the exact Walsh-kernel theorem. -/
theorem blaschkeWronskianAtom_linearIndependent_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    LinearIndependent ℚ (blaschkeWronskianAtom c) := by
  apply blaschkeWronskianAtom_linearIndependent_of_nondegenerate c
  · intro j
    exact one_sub_conj_mul_self_ne_zero_of_norm_lt_one (c j) (hdisk j)
  · exact hinj
  · intro k j hkj
    exact one_sub_conj_mul_ne_zero_of_norm_lt_one
      (c k) (c j) (hdisk k) (hdisk j)

/-- Exact zero-flip Walsh-kernel theorem for an ordinary finite Blaschke zero
configuration: distinct zeros in the open unit disk leave precisely the
nonsingleton Walsh modes in the kernel. -/
theorem zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    LinearMap.ker (zeroFlipWronskianLin c) = nonSingletonWalshSpan n := by
  exact zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan c
    (blaschkeWronskianAtom_linearIndependent_of_unitDisk c hdisk hinj)

end FormalResearch.Blaschke
