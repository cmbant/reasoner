module

public import FormalResearch.Special.LatticeI

/-!
# Summation by parts over a finite set of points

For a finite `S ⊂ [-X, X]` and `φ ∈ C¹`:
`∑_{x∈S} φ(x) = φ(X)·#S - ∫_{-X}^{X} φ'(s) N(s) ds`, `N(s) = #{x ∈ S : x ≤ s}`.
This is the first display of the proof of `lem:latticesum` (ii) (`∫_{[-X^-,X]} φ dN`).
The per-point identity `∫_{-X}^X 1_{x ≤ s} φ'(s) ds = φ(X) - φ(x)` is the fundamental theorem of
calculus for `s ↦ 1_{x≤s}(φ(s) - φ(x))` (continuous, differentiable off `{x}`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

lemma integral_ind_deriv {X x : ℝ} (hx : x ∈ Icc (-X) X) {φ φ' : ℝ → ℂ} (hφc : Continuous φ)
    (hφd : ∀ s ∈ Icc (-X) X, HasDerivAt φ (φ' s) s)
    (hint : IntervalIntegrable (fun s => if x ≤ s then φ' s else 0) volume (-X) X) :
    ∫ s in (-X)..X, (if x ≤ s then φ' s else 0) = φ X - φ x := by
  set G : ℝ → ℂ := fun s => if x ≤ s then φ s - φ x else 0 with hG
  have hGc : Continuous G := by
    have := continuous_if_le (f := fun _ : ℝ => x) (g := fun s : ℝ => s) (continuous_const)
      continuous_id (f' := fun s => φ s - φ x) (g' := fun _ => (0 : ℂ))
      ((hφc.sub continuous_const).continuousOn) continuousOn_const (fun s hs => by simp [← hs])
    exact this
  have hder : ∀ s ∈ Ioo (-X) X \ ({x} : Set ℝ), HasDerivAt G (if x ≤ s then φ' s else 0) s := by
    intro s ⟨hs, hsx⟩
    have hsx' : s ≠ x := hsx
    rcases lt_or_gt_of_ne hsx' with hlt | hgt
    · have : G =ᶠ[𝓝 s] fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds hlt] with z hz
        simp [hG, not_le.mpr hz]
      rw [if_neg (not_le.mpr hlt)]
      exact (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq this
    · have : G =ᶠ[𝓝 s] fun z => φ z - φ x := by
        filter_upwards [Ioi_mem_nhds hgt] with z hz
        simp [hG, le_of_lt hz]
      rw [if_pos hgt.le]
      exact ((hφd s ⟨hs.1.le, hs.2.le⟩).sub_const (φ x)).congr_of_eventuallyEq this
  have := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le G (fun s => if x ≤ s then φ' s else 0)
    (by linarith [hx.1, hx.2] : -X ≤ X) (countable_singleton x) hGc.continuousOn hder hint
  rw [this]
  have h1 : G X = φ X - φ x := by simp [hG, hx.2]
  have h2 : G (-X) = 0 := by
    by_cases h : x ≤ -X
    · have : x = -X := le_antisymm h hx.1
      simp [hG, h, this]
    · simp [hG, h]
  rw [h1, h2]; ring

theorem sum_by_parts {X : ℝ} {S : Finset ℝ} (hS : ∀ x ∈ S, x ∈ Icc (-X) X) {φ φ' : ℝ → ℂ}
    (hφc : Continuous φ) (hφd : ∀ s ∈ Icc (-X) X, HasDerivAt φ (φ' s) s)
    (hφ'c : ContinuousOn φ' (Icc (-X) X)) (hX : 0 ≤ X) :
    ∑ x ∈ S, φ x = φ X * (S.card : ℂ) -
      ∫ s in (-X)..X, φ' s * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) := by
  have hint : ∀ x : ℝ, IntervalIntegrable (fun s => if x ≤ s then φ' s else 0) volume (-X) X := by
    intro x
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    have h1 : IntegrableOn φ' (Icc (-X) X) := hφ'c.integrableOn_Icc
    have h2 := h1.indicator (measurableSet_Ici (a := x))
    refine h2.congr_fun (fun s _ => ?_) measurableSet_Icc
    simp [Set.indicator]
  have hsum : ∀ x ∈ S, φ X - φ x = ∫ s in (-X)..X, (if x ≤ s then φ' s else 0) :=
    fun x hx => (integral_ind_deriv (hS x hx) hφc hφd (hint x)).symm
  have h1 : ∑ x ∈ S, (φ X - φ x) = ∑ x ∈ S, ∫ s in (-X)..X, (if x ≤ s then φ' s else 0) :=
    Finset.sum_congr rfl hsum
  rw [← intervalIntegral.integral_finset_sum (fun x _ => hint x)] at h1
  have h2 : ∀ s : ℝ, ∑ x ∈ S, (if x ≤ s then φ' s else 0) =
      φ' s * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) := by
    intro s
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [h2] at h1
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have : φ X * (S.card : ℂ) - ∑ x ∈ S, φ x = ∫ s in (-X)..X, φ' s * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) := by
    rw [← h1]; ring
  rw [← this]; ring

end FormalResearch.Special.Lattice
