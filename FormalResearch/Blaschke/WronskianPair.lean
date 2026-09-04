import Mathlib

namespace FormalResearch.Blaschke

open Polynomial

/-- Numerator factors used in the zero-flip/Walsh formulation. -/
noncomputable def blaschkeA (c : ℂ) : ℂ[X] := X - C c
noncomputable def blaschkeB (c : ℂ) : ℂ[X] := 1 - C (Complex.conj c) * X

@[simp] theorem derivative_blaschkeA (c : ℂ) :
    derivative (blaschkeA c) = 1 := by
  simp [blaschkeA]

@[simp] theorem derivative_blaschkeB (c : ℂ) :
    derivative (blaschkeB c) = C (-Complex.conj c) := by
  simp [blaschkeB]

/-- Exact reciprocal-pair Wronskian atom used in the Walsh sign formula. -/
theorem blaschke_pair_wronskian (c : ℂ) :
    derivative (blaschkeA c) * blaschkeB c -
      blaschkeA c * derivative (blaschkeB c) =
        C (1 - Complex.conj c * c) := by
  simp [blaschkeA, blaschkeB]
  ring

/-- Equivalent real form of the scalar factor. -/
theorem blaschke_pair_wronskian_normSq (c : ℂ) :
    derivative (blaschkeA c) * blaschkeB c -
      blaschkeA c * derivative (blaschkeB c) =
        C ((1 - Complex.normSq c : ℝ) : ℂ) := by
  rw [blaschke_pair_wronskian]
  congr 1
  simpa [Complex.normSq_eq_conj_mul_self]

end FormalResearch.Blaschke
