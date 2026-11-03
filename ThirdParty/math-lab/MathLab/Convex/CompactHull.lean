module

/-
CompactHull.lean

The convex hull of a compact set in a finite-dimensional real vector space is compact
(`isCompact_convexHull`). Mathlib has the finite case (`Set.Finite.isCompact_convexHull`). The general
case follows from Carathéodory's theorem: in dimension `d` every point of the hull is a convex
combination of `d + 1` points of the set, so the hull is the image of a compact set of weights and
points under a continuous map.
-/
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

/-- Compatibility shim: `Finset.sum_extend_zero_of_injective` is newer than the pinned Mathlib. -/
theorem MathLab.Compat.sum_extend_zero_of_injective {ι κ M : Type*} [Fintype ι] [AddCommMonoid M]
    {s : Finset κ} (f : ι → M) {e : ι → κ} (he : Function.Injective e) (hs : ∀ i, e i ∈ s) :
    ∑ j ∈ s, Function.extend e f 0 j = ∑ i, f i := by
  classical
  rw [← Finset.sum_subset (s₁ := Finset.univ.map ⟨e, he⟩) (s₂ := s)
      (by intro j hj; simp only [Finset.mem_map, Finset.mem_univ, true_and] at hj
          obtain ⟨i, rfl⟩ := hj; exact hs i)
      (by intro j _ hj
          simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hj
          rw [Function.extend_apply' _ _ _ hj]; rfl),
    Finset.sum_map]
  simp [he.extend_apply]

open Set Module

namespace MathLab

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Convex weights on `ι`: nonnegative and summing to one. -/
def weights (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

theorem isCompact_weights (ι : Type*) [Fintype ι] : IsCompact (weights ι) := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset ?_ ?_
  · have e : weights ι = (⋂ i, {w : ι → ℝ | 0 ≤ w i}) ∩ {w | ∑ i, w i = 1} := by
      ext w
      simp [weights]
    rw [e]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  · intro w hw i _
    exact ⟨hw.1 i, hw.2 ▸ Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)⟩

/-- **Carathéodory with a fixed number of points**: in dimension `d`, a point of the convex hull of a
nonempty set `s` is a convex combination of `d + 1` points of `s`. -/
theorem exists_convexComb_fin [FiniteDimensional ℝ E] {s : Set E} (hs : s.Nonempty) {x : E}
    (hx : x ∈ convexHull ℝ s) :
    ∃ w ∈ weights (Fin (finrank ℝ E + 1)), ∃ z : Fin (finrank ℝ E + 1) → E,
      (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x := by
  classical
  obtain ⟨ι, _, z, w, hzs, hind, hw0, hw1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Fintype.card (Fin (finrank ℝ E + 1)) := by
    rw [Fintype.card_fin]
    have h1 := hind.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨z₀, hz₀⟩ := hs
  have hwz : (fun j => Function.extend e w 0 j • Function.extend e z (fun _ => z₀) j)
      = Function.extend e (fun i => w i • z i) 0 := by
    funext j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [e.injective.extend_apply, e.injective.extend_apply, e.injective.extend_apply]
    · rw [Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj,
        Pi.zero_apply, Pi.zero_apply, zero_smul]
  refine ⟨Function.extend e w 0, ⟨fun j => ?_, ?_⟩, Function.extend e z fun _ => z₀, fun j => ?_, ?_⟩
  · by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [e.injective.extend_apply]
      exact (hw0 i).le
    · rw [Function.extend_apply' _ _ _ hj]
      exact le_rfl
  · rw [MathLab.Compat.sum_extend_zero_of_injective w e.injective fun _ => Finset.mem_univ _, hw1]
  · by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [e.injective.extend_apply]
      exact hzs (Set.mem_range_self i)
    · rw [Function.extend_apply' _ _ _ hj]
      exact hz₀
  · rw [Finset.sum_congr rfl fun j _ => congrFun hwz j,
      MathLab.Compat.sum_extend_zero_of_injective _ e.injective fun _ => Finset.mem_univ _]

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- **The convex hull of a compact set in a finite-dimensional real vector space is compact.** -/
theorem isCompact_convexHull [FiniteDimensional ℝ E] {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  set N := finrank ℝ E + 1
  have himg : convexHull ℝ s = (fun p : (Fin N → ℝ) × (Fin N → E) => ∑ i, p.1 i • p.2 i) ''
      (weights (Fin N) ×ˢ Set.pi univ fun _ => s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw, z, hz, rfl⟩ := exists_convexComb_fin hne hx
      exact ⟨(w, z), ⟨hw, fun i _ => hz i⟩, rfl⟩
    · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw.1 i) hw.2
        fun i _ => subset_convexHull ℝ s (hz i (mem_univ i))
  rw [himg]
  exact ((isCompact_weights _).prod (isCompact_univ_pi fun _ => hs)).image (by fun_prop)

end MathLab

end -- public section

#print axioms MathLab.exists_convexComb_fin
#print axioms MathLab.isCompact_convexHull
