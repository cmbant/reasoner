import Mathlib

namespace FormalResearch.Blaschke

open Polynomial Complex

/-- Numerator factors used in the zero-flip/Walsh formulation. -/
def blaschkeA (c : ℂ) : ℂ[X] := X - C c
def blaschkeB (c : ℂ) : ℂ[X] := 1 - C (conj c) * X

@[simp] theorem derivative_blaschkeA (c : ℂ) :
    derivative (blaschkeA c) = 1 := by
  simp [blaschkeA]

@[simp] theorem derivative_blaschkeB (c : ℂ) :
    derivative (blaschkeB c) = C (-conj c) := by
  simp [blaschkeB]

/-- Exact reciprocal-pair Wronskian atom used in the Walsh sign formula. -/
theorem blaschke_pair_wronskian (c : ℂ) :
    derivative (blaschkeA c) * blaschkeB c -
      blaschkeA c * derivative (blaschkeB c) =
        C (1 - conj c * c) := by
  simp [blaschkeA, blaschkeB]
  ring

/-- Equivalent real form of the scalar factor. -/
theorem blaschke_pair_wronskian_normSq (c : ℂ) :
    derivative (blaschkeA c) * blaschkeB c -
      blaschkeA c * derivative (blaschkeB c) =
        C ((1 - normSq c : ℝ) : ℂ) := by
  rw [blaschke_pair_wronskian]
  congr 1
  rw [normSq_eq_conj_mul_self]
  norm_cast

end FormalResearch.Blaschke
