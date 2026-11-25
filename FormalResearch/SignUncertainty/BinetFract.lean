module

public import FormalResearch.SignUncertainty.BinetP2

/-!
# Periodic polynomials: differentiability of `g ∘ fract`

Generic.  **Proved**: if `g` is differentiable with `g 0 = g 1` and `g' 0 = g' 1`, then `g ∘ fract` is
differentiable everywhere with derivative `g' ∘ fract`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace FormalResearch.SignUncertainty.BinetDecay

lemma hasDerivAt_comp_fract {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (h0 : g 0 = g 1) (h1 : g' 0 = g' 1) (x : ℝ) :
    HasDerivAt (fun s => g (Int.fract s)) (g' (Int.fract x)) x := by
  have hfl1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hfl2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hpiece : ∀ m : ℤ, HasDerivAt (fun s : ℝ => g (s - m)) (g' (x - m)) x := by
    intro m
    exact ((hg (x - m)).comp x ((hasDerivAt_id x).sub_const (m : ℝ))).congr_deriv (by simp)
  have hR : HasDerivWithinAt (fun s => g (Int.fract s)) (g' (Int.fract x)) (Ici x) x := by
    refine (hpiece ⌊x⌋).hasDerivWithinAt.congr_of_eventuallyEq ?_ rfl
    have hlt : ∀ᶠ s : ℝ in 𝓝[Ici x] x, s < (⌊x⌋ : ℝ) + 1 :=
      (eventually_lt_nhds hfl2).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlt, self_mem_nhdsWithin] with s hs hs2
    have hs2' : x ≤ s := hs2
    have hfs : ⌊s⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]; exact ⟨by linarith, hs⟩
    show g (s - ⌊s⌋) = g (s - ⌊x⌋)
    rw [hfs]
  have hL : HasDerivWithinAt (fun s => g (Int.fract s)) (g' (Int.fract x)) (Iic x) x := by
    by_cases hx : Int.fract x = 0
    · have hxn : x = ⌊x⌋ := by
        have : x - ⌊x⌋ = 0 := hx
        linarith
      have hx1 : x - ((⌊x⌋ - 1 : ℤ) : ℝ) = 1 := by push_cast; linarith
      have hp := (hpiece (⌊x⌋ - 1)).hasDerivWithinAt (s := Iic x)
      rw [hx1] at hp
      have hp' : HasDerivWithinAt (fun s : ℝ => g (s - ((⌊x⌋ - 1 : ℤ) : ℝ))) (g' (Int.fract x)) (Iic x) x := by
        rw [hx, h1]; exact hp
      refine hp'.congr_of_eventuallyEq ?_ ?_
      · have hgt : ∀ᶠ s : ℝ in 𝓝[Iic x] x, (⌊x⌋ : ℝ) - 1 < s :=
          (eventually_gt_nhds (by linarith : (⌊x⌋ : ℝ) - 1 < x)).filter_mono nhdsWithin_le_nhds
        filter_upwards [hgt, self_mem_nhdsWithin] with s hs hs2
        have hs2' : s ≤ x := hs2
        rcases hs2'.lt_or_eq with hlt | heq
        · have hfs : ⌊s⌋ = ⌊x⌋ - 1 := by
            rw [Int.floor_eq_iff]; push_cast; exact ⟨hs.le, by linarith⟩
          show g (s - ⌊s⌋) = g (s - ((⌊x⌋ - 1 : ℤ) : ℝ))
          rw [hfs]
        · subst heq
          show g (Int.fract s) = g (s - ((⌊s⌋ - 1 : ℤ) : ℝ))
          rw [hx, h0, hx1]
      · show g (Int.fract x) = g (x - ((⌊x⌋ - 1 : ℤ) : ℝ))
        rw [hx, h0, hx1]
    · have hxpos : (⌊x⌋ : ℝ) < x := by
        rcases hfl1.lt_or_eq with h | h
        · exact h
        · exfalso; apply hx; show x - ⌊x⌋ = 0; linarith
      refine (hpiece ⌊x⌋).hasDerivWithinAt.congr_of_eventuallyEq ?_ rfl
      have hgt : ∀ᶠ s : ℝ in 𝓝[Iic x] x, (⌊x⌋ : ℝ) < s :=
        (eventually_gt_nhds hxpos).filter_mono nhdsWithin_le_nhds
      filter_upwards [hgt, self_mem_nhdsWithin] with s hs hs2
      have hs2' : s ≤ x := hs2
      have hfs : ⌊s⌋ = ⌊x⌋ := by
        rw [Int.floor_eq_iff]; exact ⟨hs.le, by linarith⟩
      show g (s - ⌊s⌋) = g (s - ⌊x⌋)
      rw [hfs]
  have := hL.union hR
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
  exact this

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.hasDerivAt_comp_fract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_comp_fract

end FormalResearch.SignUncertainty.BinetDecay
