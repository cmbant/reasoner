import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Fintype.Card

/-!
# Finite phase orthogonality for coherent-power extraction

The Hermitian coherent-copy separation step needs a finite Fourier extraction on the
phase family `x + ζ^k y`.  This file isolates the root-of-unity orthogonality used by
that extraction, upgrades it to exact coefficient recovery through the Vandermonde
matrix on one primitive-root cycle, and records the multilinear two-point expansion
whose phase coefficients enter the Hermitian bidegree argument.
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

/-- Expand a diagonal value of a multilinear map along the phase line `x + z • y`.
Each subset of slots carrying `y` contributes the corresponding power of `z`.
No symmetry hypothesis is needed for this raw expansion. -/
theorem multilinear_coherent_two_point_expansion
    {E W : Type*} [AddCommMonoid E] [Module ℂ E]
    [AddCommMonoid W] [Module ℂ W]
    {n : ℕ} (p : MultilinearMap ℂ (fun _ : Fin n => E) W)
    (x y : E) (z : ℂ) :
    p (fun _ => x + z • y) =
      ∑ s : Finset (Fin n),
        z ^ s.card • p (s.piecewise (fun _ => y) (fun _ => x)) := by
  calc
    p (fun _ => x + z • y) =
        p ((fun _ => z • y) + (fun _ => x)) := by
      congr 1
      funext i
      simp [add_comm]
    _ = ∑ s : Finset (Fin n),
        p (s.piecewise (fun _ => z • y) (fun _ => x)) := by
      exact p.map_add_univ (fun _ => z • y) (fun _ => x)
    _ = ∑ s : Finset (Fin n),
        z ^ s.card • p (s.piecewise (fun _ => y) (fun _ => x)) := by
      apply Finset.sum_congr rfl
      intro s hs
      let m : Fin n → E := s.piecewise (fun _ => y) (fun _ => x)
      have h := p.map_piecewise_smul (fun _ : Fin n => z) m s
      have harg :
          s.piecewise (fun i => z • m i) m =
            s.piecewise (fun _ => z • y) (fun _ => x) := by
        funext i
        by_cases hi : i ∈ s <;> simp [m, hi]
      rw [harg] at h
      simpa [m] using h

/-- The exponent produced after multiplying a bidegree-`(n,n)` phase expansion by
`z^n`.  The range is exactly contained in `0, ..., 2n`. -/
def coherentPhaseExponent (n : ℕ) (s t : Finset (Fin n)) : Fin (2 * n + 1) :=
  ⟨n - s.card + t.card, by
    have hs : s.card ≤ n := by simpa using s.card_le_univ
    have ht : t.card ≤ n := by simpa using t.card_le_univ
    omega⟩

/-- The top phase exponent is attained only by taking no `y` slots on the
conjugate-linear side and every `y` slot on the linear side. -/
theorem coherentPhaseExponent_eq_last_iff
    {n : ℕ} (s t : Finset (Fin n)) :
    coherentPhaseExponent n s t = Fin.last (2 * n) ↔
      s = ∅ ∧ t = Finset.univ := by
  constructor
  · intro h
    have hv : n - s.card + t.card = 2 * n := congrArg Fin.val h
    have hs : s.card ≤ n := by simpa using s.card_le_univ
    have ht : t.card ≤ n := by simpa using t.card_le_univ
    have hs0 : s.card = 0 := by omega
    have htn : t.card = n := by omega
    exact ⟨Finset.card_eq_zero.mp hs0,
      Finset.eq_univ_of_card t (by simpa using htn)⟩
  · rintro ⟨rfl, rfl⟩
    apply Fin.ext
    simp [coherentPhaseExponent, two_mul]

/-- Group a double phase expansion by its ordinary polynomial exponent. -/
def coherentPhaseCoefficients {n : ℕ}
    (a : Finset (Fin n) → Finset (Fin n) → ℂ) : Fin (2 * n + 1) → ℂ :=
  fun r => ∑ s : Finset (Fin n), ∑ t : Finset (Fin n),
    if coherentPhaseExponent n s t = r then a s t else 0

/-- Regrouping the subset-indexed bidegree expansion by phase exponent produces an
ordinary polynomial of degree at most `2n`. -/
theorem coherentPhaseCoefficients_eval {n : ℕ}
    (a : Finset (Fin n) → Finset (Fin n) → ℂ) (z : ℂ) :
    (∑ r : Fin (2 * n + 1), coherentPhaseCoefficients a r * z ^ (r : ℕ)) =
      ∑ s : Finset (Fin n), ∑ t : Finset (Fin n),
        a s t * z ^ (coherentPhaseExponent n s t : ℕ) := by
  classical
  simp only [coherentPhaseCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The top grouped coefficient is exactly the extreme coherent cross term. -/
theorem coherentPhaseCoefficients_last {n : ℕ}
    (a : Finset (Fin n) → Finset (Fin n) → ℂ) :
    coherentPhaseCoefficients a (Fin.last (2 * n)) = a ∅ Finset.univ := by
  classical
  unfold coherentPhaseCoefficients
  calc
    (∑ s : Finset (Fin n), ∑ t : Finset (Fin n),
        if coherentPhaseExponent n s t = Fin.last (2 * n) then a s t else 0) =
        ∑ s : Finset (Fin n), if s = ∅ then a s Finset.univ else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hse : s = ∅
      · subst s
        simp [coherentPhaseExponent_eq_last_iff]
      · simp [coherentPhaseExponent_eq_last_iff, hse]
    _ = a ∅ Finset.univ := by
      simp

/-- Finite phase extraction at order `2n+1`: if the bidegree phase polynomial
vanishes around one primitive root cycle, its extreme coherent cross coefficient
vanishes. -/
theorem coherentPhase_extreme_coefficient_eq_zero
    {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * n + 1))
    (a : Finset (Fin n) → Finset (Fin n) → ℂ)
    (hzero : ∀ k : Fin (2 * n + 1),
      (∑ s : Finset (Fin n), ∑ t : Finset (Fin n),
        a s t * (ζ ^ (k : ℕ)) ^ (coherentPhaseExponent n s t : ℕ)) = 0) :
    a ∅ Finset.univ = 0 := by
  let c := coherentPhaseCoefficients a
  have hc : c = 0 := primitiveRoot_vandermonde_coefficients_eq_zero hζ c (by
    intro k
    rw [coherentPhaseCoefficients_eval]
    exact hzero k)
  have hlast := congrFun hc (Fin.last (2 * n))
  rw [show c (Fin.last (2 * n)) = a ∅ Finset.univ by
    simpa [c] using coherentPhaseCoefficients_last a] at hlast
  exact hlast

end

end FormalResearch.QIA
