import Mathlib

/-!
# Compactness of the convex hull of a compact set (finite dimensions)

Mathlib only has `Set.Finite.isCompact_convexHull`.  Here the general statement in a finite-dimensional
real topological vector space is proved from Carathéodory's theorem: the convex hull is the continuous
image of `stdSimplex × K^(D+1)`.  Used for plan lemma D1 of the Gurvits–Barnum separable ball
(Phys. Rev. A 66, 062311 (2002)).
-/

namespace FormalResearch.GurvitsBarnum

open Set Finset

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]

/-- The convex hull of a compact set in a finite-dimensional real topological vector space is
compact (Carathéodory). -/
theorem isCompact_convexHull_of_isCompact {K : Set E} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨k0, hk0⟩
  · simp
  set D := Module.finrank ℝ E with hD
  let F : (Fin (D + 1) → ℝ) × (Fin (D + 1) → E) → E := fun p => ∑ i, p.1 i • p.2 i
  have hF : Continuous F := by
    unfold F
    fun_prop
  let Δ : Set (Fin (D + 1) → ℝ) :=
    (Set.univ.pi fun _ : Fin (D + 1) => Set.Icc (0 : ℝ) 1) ∩ {w | ∑ i, w i = 1}
  have hΔ : IsCompact Δ :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  have hA : IsCompact (Δ ×ˢ (Set.univ.pi fun _ : Fin (D + 1) => K)) :=
    hΔ.prod (isCompact_univ_pi fun _ => hK)
  have himg : F '' (Δ ×ˢ (Set.univ.pi fun _ : Fin (D + 1) => K)) = convexHull ℝ K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      exact (convex_convexHull ℝ K).sum_mem (fun i _ => (hw.1 i (Set.mem_univ i)).1) hw.2
        (fun i _ => subset_convexHull ℝ K (hz i (Set.mem_univ i)))
    · intro x hx
      obtain ⟨ι, _, z, w, hzK, hind, hw0, hw1, hx⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      have hcard : Fintype.card ι ≤ D + 1 :=
        hind.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
      let e : ι → Fin (D + 1) := fun i => Fin.castLE hcard ((Fintype.equivFin ι) i)
      have he : Function.Injective e := fun i j h => by
        simpa [e] using h
      let w' : Fin (D + 1) → ℝ := Function.extend e w 0
      let z' : Fin (D + 1) → E := Function.extend e z (fun _ => k0)
      have hw'0 : ∀ j ∉ Set.range e, w' j = 0 := fun j hj => by
        have : ¬ ∃ a, e a = j := fun ⟨a, ha⟩ => hj ⟨a, ha⟩
        simp [w', Function.extend_apply' _ _ _ this]
      have hnn : ∀ j, 0 ≤ w' j := fun j => by
        by_cases hj : j ∈ Set.range e
        · obtain ⟨i, rfl⟩ := hj
          simp only [w', he.extend_apply]
          exact (hw0 i).le
        · simp [hw'0 j hj]
      have hs1 : ∑ j, w' j = 1 := by
        have := Fintype.sum_of_injective e he w w' (fun j hj => hw'0 j hj)
          (fun i => (he.extend_apply w 0 i).symm)
        rw [← this]; exact hw1
      refine ⟨(w', z'), ⟨⟨fun j _ => ⟨hnn j, ?_⟩, hs1⟩, fun j _ => ?_⟩, ?_⟩
      · rw [← hs1]
        exact Finset.single_le_sum (f := w') (fun i _ => hnn i) (Finset.mem_univ j)
      · by_cases hj : j ∈ Set.range e
        · obtain ⟨i, rfl⟩ := hj
          simp only [z', he.extend_apply]
          exact hzK ⟨i, rfl⟩
        · have : ¬ ∃ a, e a = j := fun ⟨a, ha⟩ => hj ⟨a, ha⟩
          simp [z', Function.extend_apply' _ _ _ this, hk0]
      · show ∑ j, w' j • z' j = x
        rw [← hx]
        symm
        refine Fintype.sum_of_injective e he (fun i => w i • z i) (fun j => w' j • z' j) ?_ ?_
        · intro j hj; simp [hw'0 j hj]
        · intro i; simp only [w', z', he.extend_apply]
  rw [← himg]
  exact hA.image hF

/-- info: 'FormalResearch.GurvitsBarnum.isCompact_convexHull_of_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCompact_convexHull_of_isCompact

end FormalResearch.GurvitsBarnum
