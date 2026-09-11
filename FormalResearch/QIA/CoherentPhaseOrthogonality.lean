import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Finite phase orthogonality for coherent-power extraction

The Hermitian coherent-copy separation step needs a finite Fourier extraction on the
phase family `x + ζ^k y`.  This file isolates the root-of-unity orthogonality used by
that extraction and then upgrades it to exact coefficient recovery through the
Vandermonde matrix on one primitive-root cycle.
-/

namespace FormalResearch.QIA

open Finset

noncomputable section

/-- A nonzero frequency below the order of a primitive complex root has vanishing
geometric sum over one full cycle. -/
theorem primitiveRoot_power_geom_sum_eq_zero
    {ζ : ℂ} {m r : ℕ} (hζ : IsPrimitiveRoot ζ m)
    (hr0 : r ≠ 0) (hrlt : r < m) :
    ∑ k ∈ Finset.range m, (ζ ^ r) ^ k = 0 := by
  have hne : ζ ^ r ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hr0 hrlt
  have hpow : (ζ ^ r) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h := geom_sum_mul (ζ ^ r) m
  rw [hpow, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)

/-- The zero frequency contributes exactly the sampling order. -/
theorem primitiveRoot_zero_frequency_geom_sum (ζ : ℂ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (ζ ^ 0) ^ k = (m : ℂ) := by
  simp

/-- Combined zero/nonzero-frequency form used by finite Fourier extraction. -/
theorem primitiveRoot_power_geom_sum
    {ζ : ℂ} {m r : ℕ} (hζ : IsPrimitiveRoot ζ m) (hrlt : r < m) :
    ∑ k ∈ Finset.range m, (ζ ^ r) ^ k = if r = 0 then (m : ℂ) else 0 := by
  by_cases hr0 : r = 0
  · subst r
    simp
  · rw [if_neg hr0]
    exact primitiveRoot_power_geom_sum_eq_zero hζ hr0 hrlt

/-- Evaluation at one full primitive-root cycle determines all coefficients of a
polynomial of degree strictly below the cycle length.  This is the finite Fourier
coefficient-recovery statement used by the bidegree phase extraction. -/
theorem primitiveRoot_vandermonde_coefficients_eq_zero
    {ζ : ℂ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (c : Fin m → ℂ)
    (hzero : ∀ k : Fin m,
      (∑ r : Fin m, c r * (ζ ^ (k : ℕ)) ^ (r : ℕ)) = 0) :
    c = 0 := by
  apply Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (f := fun k : Fin m => ζ ^ (k : ℕ))
  · intro i j hij
    exact Fin.ext (hζ.pow_inj i.isLt j.isLt hij)
  · exact hzero

end

end FormalResearch.QIA
