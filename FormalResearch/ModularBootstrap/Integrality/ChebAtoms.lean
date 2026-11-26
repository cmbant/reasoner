module

public import FormalResearch.ModularBootstrap.Duality.FiniteAtomic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev expansion and exact atomic representation of the remainder measure

Tools for `int:cheb` (`CFT/modular_bootstrap/paper/integrality.tex`, proof of Lemma INT-M, "Grid and
rounding"): (i) polynomials of degree `≤ M` are combinations of `T_0, …, T_M`; (ii) by Carathéodory's
theorem a finite positive measure on `[-1,1]` has a finitely supported atomic measure with the same
moments `∫ T_m`, `1 ≤ m ≤ M`, and the same mass.  **Proved.**
-/

@[expose] public section

open Real Finset MeasureTheory Polynomial
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

/-- **Chebyshev expansion**: a real polynomial of degree `≤ d` is `∑_{m ≤ d} a_m T_m`. -/
lemma exists_chebyshev_expansion : ∀ (d : ℕ) (P : ℝ[X]), P.degree ≤ d →
    ∃ a : ℕ → ℝ, P = ∑ m ∈ range (d + 1), C (a m) * Polynomial.Chebyshev.T ℝ (m : ℤ) := by
  intro d
  induction d with
  | zero =>
    intro P hP
    refine ⟨fun _ => P.coeff 0, ?_⟩
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero, Polynomial.Chebyshev.T_zero,
      mul_one]
    exact eq_C_of_degree_le_zero (by simpa using hP)
  | succ d ih =>
    intro P hP
    set n : ℕ := d + 1 with hn
    have hT : (Polynomial.Chebyshev.T ℝ (n : ℤ)).natDegree = n := by
      rw [Polynomial.Chebyshev.natDegree_T]; simp
    have hlc : (Polynomial.Chebyshev.T ℝ (n : ℤ)).leadingCoeff = 2 ^ (n - 1) := by
      rw [Polynomial.Chebyshev.leadingCoeff_T]; simp
    set c : ℝ := P.coeff n / 2 ^ (n - 1) with hc
    set Q : ℝ[X] := P - C c * Polynomial.Chebyshev.T ℝ (n : ℤ) with hQ
    have hQdeg : Q.degree ≤ d := by
      rw [degree_le_iff_coeff_zero]
      intro m hm
      have hm' : d < m := by exact_mod_cast hm
      rw [hQ, coeff_sub, coeff_C_mul]
      by_cases hmn : m = n
      · subst hmn
        have : (Polynomial.Chebyshev.T ℝ (n : ℤ)).coeff n = 2 ^ (n - 1) := by
          rw [← hlc, Polynomial.leadingCoeff, hT]
        rw [this, hc]
        field_simp
        ring
      · have h1 : P.coeff m = 0 := by
          apply coeff_eq_zero_of_degree_lt
          refine lt_of_le_of_lt hP ?_
          exact_mod_cast (by omega : n < m)
        have h2 : (Polynomial.Chebyshev.T ℝ (n : ℤ)).coeff m = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [hT]; omega
        rw [h1, h2]; simp
    obtain ⟨a, ha⟩ := ih Q hQdeg
    refine ⟨fun m => if m = n then c else a m, ?_⟩
    rw [sum_range_succ]
    have hsum : ∑ m ∈ range (d + 1), C (if m = n then c else a m) * Polynomial.Chebyshev.T ℝ (m : ℤ) =
        ∑ m ∈ range (d + 1), C (a m) * Polynomial.Chebyshev.T ℝ (m : ℤ) := by
      refine sum_congr rfl fun m hm => ?_
      have : m ≠ n := by have := mem_range.1 hm; omega
      simp [this]
    rw [hsum, ← ha]
    simp only [↓reduceIte]
    rw [hQ]
    ring

/-- **Exact atomic representation** of a finite measure on `[-1,1]`: finitely many atoms
`x_i = cos β_i` with positive real weights `ρ_i` of total `ν(ℝ)` and the same moments `∫ T_m dν`
for `1 ≤ m ≤ M` (Carathéodory). -/
theorem exists_atomic_chebyshev {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hsupp : ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0) (M : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (β ρ : ι → ℝ), (∀ i, β i ∈ Set.Icc (0 : ℝ) π) ∧
      (∀ i, 0 < ρ i) ∧ ∑ i, ρ i = ν.real Set.univ ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ M →
        ∑ i, ρ i * cos ((m : ℝ) * β i) = ∫ x, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x ∂ν := by
  by_cases hν : ν = 0
  · refine ⟨Empty, inferInstance, fun _ => 0, fun _ => 1, by simp, by simp, ?_, ?_⟩
    · simp [hν]
    · intro m _ _
      simp [hν]
  have hpos : 0 < ν Set.univ := by
    rw [pos_iff_ne_zero]
    intro h
    exact hν (Measure.measure_univ_eq_zero.1 h)
  have hfin : ν Set.univ ≠ ∞ := measure_ne_top ν _
  set mass : ℝ := ν.real Set.univ with hmass
  have hmass0 : 0 < mass := ENNReal.toReal_pos hpos.ne' hfin
  let P : Measure ℝ := (ν Set.univ)⁻¹ • ν
  have hP : IsProbabilityMeasure P :=
    ⟨by simp [P, ENNReal.inv_mul_cancel hpos.ne' hfin]⟩
  let Φ : ℝ → (Fin M → ℝ) := fun x i => (Polynomial.Chebyshev.T ℝ (((i : ℕ) + 1 : ℕ) : ℤ)).eval x
  have hΦc : Continuous Φ :=
    continuous_pi fun i => (Polynomial.Chebyshev.T ℝ (((i : ℕ) + 1 : ℕ) : ℤ)).continuous
  let K : Set (Fin M → ℝ) := Φ '' Set.Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hΦc
  have hhull : IsCompact (convexHull ℝ K) :=
    FormalResearch.ModularBootstrap.Duality.isCompact_convexHull_of_isCompact hK
  have hPsupp : P (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by simp [P, hsupp]
  have hae : ∀ᵐ x ∂P, x ∈ Set.Icc (-1 : ℝ) 1 := by
    have := measure_eq_zero_iff_ae_notMem.1 hPsupp
    exact this.mono fun x hx => by simpa using hx
  have hΦint : Integrable Φ P := by
    have h1 : IntegrableOn Φ (Set.Icc (-1 : ℝ) 1) P :=
      hΦc.continuousOn.integrableOn_compact isCompact_Icc
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have hmem : (∫ x, Φ x ∂P) ∈ convexHull ℝ K := by
    refine Convex.integral_mem (convex_convexHull ℝ K) hhull.isClosed ?_ hΦint
    exact hae.mono fun x hx => subset_convexHull ℝ K ⟨x, hx, rfl⟩
  obtain ⟨ι, hι, z, w, hzK, hw, hw1, hwz, -⟩ :=
    FormalResearch.ModularBootstrap.Duality.exists_caratheodory hmem
  choose x hxI hxz using fun i => hzK (Set.mem_range_self i)
  refine ⟨ι, hι, fun i => arccos (x i), fun i => mass * w i, fun i => ⟨arccos_nonneg _, arccos_le_pi _⟩,
    fun i => mul_pos hmass0 (hw i), ?_, ?_⟩
  · rw [← mul_sum, hw1, mul_one]
  · intro m hm1 hmM
    have hi : m - 1 < M := by omega
    set i0 : Fin M := ⟨m - 1, hi⟩
    have hcomp := congrFun hwz i0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcomp
    -- the `i0`-th component of the mean
    have hint : (∫ x, Φ x ∂P) i0 = (ν Set.univ)⁻¹.toReal *
        ∫ x, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x ∂ν := by
      have h1 : (∫ x, Φ x ∂P) i0 = ∫ x, Φ x i0 ∂P := by
        have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) i0).integral_comp_comm
          hΦint
        simpa using this.symm
      rw [h1]
      have hm : ((i0 : ℕ) + 1 : ℕ) = m := by simp [i0]; omega
      simp only [Φ, hm]
      rw [integral_smul_measure, smul_eq_mul]
    rw [hint] at hcomp
    have hxm : ∀ i, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (x i) = cos ((m : ℝ) * arccos (x i)) := by
      intro i
      have := Polynomial.Chebyshev.T_real_cos (arccos (x i)) (m : ℤ)
      rw [cos_arccos (hxI i).1 (hxI i).2] at this
      simpa using this
    have hzi : ∀ i, z i i0 = (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (x i) := by
      intro i
      rw [← hxz i]
      have hm : ((i0 : ℕ) + 1 : ℕ) = m := by simp [i0]; omega
      simp only [Φ, hm]
    simp_rw [hzi] at hcomp
    have hmass' : ((ν Set.univ)⁻¹).toReal = mass⁻¹ := by
      rw [ENNReal.toReal_inv]; rfl
    rw [hmass'] at hcomp
    calc ∑ i, mass * w i * cos ((m : ℝ) * arccos (x i))
        = mass * ∑ i, w i * (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (x i) := by
          rw [mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [hxm i]; ring
      _ = _ := by
          rw [hcomp]; field_simp

end FormalResearch.ModularBootstrap.Integrality
