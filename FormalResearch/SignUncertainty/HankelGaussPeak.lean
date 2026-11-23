module

public import Mathlib

/-!
# A quadratic peak bound from a curvature bound (`gt:7.7c` (b))

If `φ` has `φ'' ≤ -m` on `[-L, L]` and a critical point `τ₀` there, then `φ(t) ≤ φ(τ₀) - (m/2)(t - τ₀)²`
(`quad_peak`).  Applied to `φ(τ) = Re Φ(σ + iτ; ξ)` with `Re g' ≥ (4/5) σ` it gives the Gaussian decay along the
vertical contour of the local density.
-/

@[expose] public section

open Set

namespace FormalResearch.SignUncertainty

lemma quad_peak {φ φ' φ'' : ℝ → ℝ} {m τ0 L : ℝ} (hτ0 : τ0 ∈ Icc (-L) L)
    (h1 : ∀ t ∈ Icc (-L) L, HasDerivAt φ (φ' t) t) (h2 : ∀ t ∈ Icc (-L) L, HasDerivAt φ' (φ'' t) t)
    (hφ'' : ∀ t ∈ Icc (-L) L, φ'' t ≤ -m) (hcrit : φ' τ0 = 0) :
    ∀ t ∈ Icc (-L) L, φ t ≤ φ τ0 - m / 2 * (t - τ0) ^ 2 := by
  -- `χ = φ' + m (t - τ0)` is antitone with `χ τ0 = 0`
  have hχ : AntitoneOn (fun t => φ' t + m * (t - τ0)) (Icc (-L) L) := by
    have hd : ∀ t ∈ Icc (-L) L, HasDerivAt (fun t => φ' t + m * (t - τ0)) (φ'' t + m) t := by
      intro t ht
      have := (h2 t ht).add (((hasDerivAt_id t).sub_const τ0).const_mul m)
      exact this.congr_deriv (by simp)
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Icc] at ht
      exact (hd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc] at ht
      rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]; linarith [hφ'' t ⟨ht.1.le, ht.2.le⟩]
  have hχ0 : φ' τ0 + m * (τ0 - τ0) = 0 := by rw [hcrit]; ring
  have hψd : ∀ t ∈ Icc (-L) L, HasDerivAt (fun t => φ t + m / 2 * (t - τ0) ^ 2)
      (φ' t + m * (t - τ0)) t := by
    intro t ht
    have h3 : HasDerivAt (fun t : ℝ => m / 2 * (t - τ0) ^ 2) (m * (t - τ0)) t := by
      have := (((hasDerivAt_id t).sub_const τ0).pow 2).const_mul (m / 2)
      exact this.congr_deriv (by simp; ring)
    exact (h1 t ht).add h3
  intro t ht
  rcases le_total τ0 t with hle | hle
  · -- `t ≥ τ0`: `ψ` antitone on `[τ0, L]`
    have hA : AntitoneOn (fun t => φ t + m / 2 * (t - τ0) ^ 2) (Icc τ0 L) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
      · exact fun s hs => (hψd s ⟨by linarith [hs.1, hτ0.1], hs.2⟩).continuousAt.continuousWithinAt
      · intro s hs; rw [interior_Icc] at hs
        exact (hψd s ⟨by linarith [hs.1, hτ0.1], hs.2.le⟩).differentiableAt.differentiableWithinAt
      · intro s hs; rw [interior_Icc] at hs
        rw [(hψd s ⟨by linarith [hs.1, hτ0.1], hs.2.le⟩).deriv]
        have := hχ ⟨hτ0.1, hτ0.2⟩ ⟨by linarith [hs.1, hτ0.1], hs.2.le⟩ hs.1.le
        simp only [sub_self, mul_zero, add_zero] at this
        linarith [hcrit]
    have := hA ⟨le_rfl, hτ0.2⟩ ⟨hle, ht.2⟩ hle
    simp at this; linarith
  · have hA : MonotoneOn (fun t => φ t + m / 2 * (t - τ0) ^ 2) (Icc (-L) τ0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
      · exact fun s hs => (hψd s ⟨hs.1, by linarith [hs.2, hτ0.2]⟩).continuousAt.continuousWithinAt
      · intro s hs; rw [interior_Icc] at hs
        exact (hψd s ⟨hs.1.le, by linarith [hs.2, hτ0.2]⟩).differentiableAt.differentiableWithinAt
      · intro s hs; rw [interior_Icc] at hs
        rw [(hψd s ⟨hs.1.le, by linarith [hs.2, hτ0.2]⟩).deriv]
        have := hχ ⟨hs.1.le, by linarith [hs.2, hτ0.2]⟩ ⟨hτ0.1, hτ0.2⟩ hs.2.le
        simp only [sub_self, mul_zero, add_zero] at this
        linarith [hcrit]
    have := hA ⟨ht.1, hle⟩ ⟨hτ0.1, le_rfl⟩ hle
    simp at this; linarith

/-- info: 'FormalResearch.SignUncertainty.quad_peak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quad_peak

end FormalResearch.SignUncertainty
