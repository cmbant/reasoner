import Mathlib
import FormalResearch.FrameFree.OddWordsSkew
import FormalResearch.FrameFree.OddWordsSl2Basis

/-!
# Skew part of the `sl₂` commutant (Paper P, `prop:oddwords` (iii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

`Sl2Data.finrank_skewComm`: the real space of skew-adjoint operators commuting with `L` and `R` has
dimension `Σ_{k ≤ n/2} C(hwDim n k, 2)`.  Restriction to the highest-weight spaces `HW_k` is a linear
equivalence from this space onto `∏_k skewAdjoint(End HW_k)` (`skewCommEquiv`): injective because a
commuting operator is determined by its restrictions (`eq_zero_of_res_eq_zero`), surjective by the
string basis construction `Ysys`, and compatible with adjoints because `HW_k` is an inner product
subspace.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Module LinearMap

namespace FormalResearch.FrameFree.OddWords

namespace Sl2Data

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {D : Sl2Data n V}

/-- Restriction of a commuting operator to `HW_k`. -/
noncomputable def res {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) (k : ℕ) : D.HW k →ₗ[ℝ] D.HW k :=
  Y.restrict fun _ hv => hY.mem_HW hv

@[simp] theorem res_apply {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) (k : ℕ) (h : D.HW k) :
    ((res hY k h : D.HW k) : V) = Y (h : V) := rfl

theorem res_adjoint {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) (k : ℕ) :
    res hY.adjoint k = LinearMap.adjoint (res hY k) := by
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, res_apply]
  exact LinearMap.adjoint_inner_left Y (y : V) (x : V)

/-- Commuting skew-adjoint operators. -/
def skewComm (D : Sl2Data n V) : Submodule ℝ (V →ₗ[ℝ] V) where
  carrier := {Y | D.IsComm Y ∧ LinearMap.adjoint Y = -Y}
  add_mem' := by
    rintro Y Z ⟨hY, hY'⟩ ⟨hZ, hZ'⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [add_mul, mul_add, hY.1, hZ.1]
    · rw [add_mul, mul_add, hY.2, hZ.2]
    · rw [map_add, hY', hZ', neg_add]
  zero_mem' := ⟨⟨by simp, by simp⟩, by simp⟩
  smul_mem' := by
    rintro c Y ⟨hY, hY'⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [smul_mul_assoc, mul_smul_comm, hY.1]
    · rw [smul_mul_assoc, mul_smul_comm, hY.2]
    · rw [map_smul, hY', smul_neg]

theorem mem_skewComm {Y : V →ₗ[ℝ] V} : Y ∈ D.skewComm ↔ D.IsComm Y ∧ LinearMap.adjoint Y = -Y :=
  Iff.rfl

theorem res_skew {Y : V →ₗ[ℝ] V} (hY : Y ∈ D.skewComm) (k : ℕ) :
    res hY.1 k ∈ skewAdjoint (D.HW k →ₗ[ℝ] D.HW k) := by
  rw [skewAdjoint.mem_iff, LinearMap.star_eq_adjoint, ← res_adjoint]
  ext h
  simp [hY.2]

/-- Restriction to the highest-weight spaces, `skewComm → ∏_k skewAdjoint(End HW_k)`. -/
noncomputable def skewRes (D : Sl2Data n V) :
    D.skewComm →ₗ[ℝ] (∀ k : Fin (n / 2 + 1), skewAdjoint (D.HW k →ₗ[ℝ] D.HW k)) where
  toFun Y k := ⟨res Y.2.1 k, res_skew Y.2 k⟩
  map_add' Y Z := by
    ext k h
    simp
  map_smul' c Y := by
    ext k h
    simp

theorem skewRes_injective (D : Sl2Data n V) : Function.Injective D.skewRes := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  have h : ∀ k : ℕ, 2 * k ≤ n → ∀ v ∈ D.HW k, (Y : V →ₗ[ℝ] V) v = 0 := by
    intro k hk v hv
    have := congrFun hY ⟨k, by omega⟩
    have h2 := congrArg (fun z : skewAdjoint (D.HW k →ₗ[ℝ] D.HW k) =>
      ((z.1 ⟨v, hv⟩ : D.HW k) : V)) this
    exact h2
  exact Subtype.ext (D.eq_zero_of_res_eq_zero Y.2.1 h)

theorem skewRes_surjective (D : Sl2Data n V) : Function.Surjective D.skewRes := by
  intro c
  let B : ∀ k : Fin (n / 2 + 1), D.HW k →ₗ[ℝ] D.HW k := fun k => (c k).1
  have hc : ∀ k, LinearMap.adjoint (B k) = - B k := fun k => by
    have := (c k).2
    rwa [skewAdjoint.mem_iff, LinearMap.star_eq_adjoint] at this
  have hY := D.Ysys_isComm B
  have hres : ∀ k : Fin (n / 2 + 1), res hY k = B k := fun k => by
    ext h; simp [D.Ysys_hw B k h]
  have hsk : LinearMap.adjoint (D.Ysys B) = - D.Ysys B := by
    have hz : D.IsComm (LinearMap.adjoint (D.Ysys B) + D.Ysys B) := by
      refine ⟨?_, ?_⟩
      · rw [add_mul, mul_add, hY.adjoint.1, hY.1]
      · rw [add_mul, mul_add, hY.adjoint.2, hY.2]
    have h0 : LinearMap.adjoint (D.Ysys B) + D.Ysys B = 0 := by
      refine D.eq_zero_of_res_eq_zero hz fun k hk v hv => ?_
      let k' : Fin (n / 2 + 1) := ⟨k, by omega⟩
      have h1 := congrArg (fun z : D.HW k' →ₗ[ℝ] D.HW k' => ((z ⟨v, hv⟩ : D.HW k') : V))
        (show res hY.adjoint k' = LinearMap.adjoint (res hY k') from res_adjoint hY k')
      simp only [res_apply, hres] at h1
      have h2 : ((LinearMap.adjoint (B k') ⟨v, hv⟩ : D.HW k') : V) = - ((B k' ⟨v, hv⟩ : D.HW k') : V) := by
        rw [hc]; rfl
      simp only [LinearMap.add_apply]
      have h3 := h1.trans h2
      have h4 : (LinearMap.adjoint (D.Ysys B)) v = - D.Ysys B v := by
        simpa [D.Ysys_hw B k' ⟨v, hv⟩] using h3
      rw [h4]; abel
    exact eq_neg_of_add_eq_zero_left h0
  refine ⟨⟨D.Ysys B, hY, hsk⟩, ?_⟩
  ext k h
  simp [skewRes, hres, B]

/-- Restriction is a linear equivalence from the commuting skew-adjoint operators onto the product of
the skew-adjoint endomorphisms of the `HW_k`. -/
noncomputable def skewCommEquiv (D : Sl2Data n V) :
    D.skewComm ≃ₗ[ℝ] (∀ k : Fin (n / 2 + 1), skewAdjoint (D.HW k →ₗ[ℝ] D.HW k)) :=
  LinearEquiv.ofBijective D.skewRes ⟨D.skewRes_injective, D.skewRes_surjective⟩

/-- **The odd-space dimension count.**  `dim skewComm = Σ_{k ≤ n/2} C(g_k, 2)` with
`g_k = C(n,k) - C(n,k-1)`. -/
theorem finrank_skewComm (D : Sl2Data n V) :
    finrank ℝ D.skewComm = ∑ k ∈ Finset.range (n / 2 + 1), (hwDim n k).choose 2 := by
  rw [D.skewCommEquiv.finrank_eq, Module.finrank_pi_fintype]
  rw [← Fin.sum_univ_eq_sum_range (fun k => (hwDim n k).choose 2) (n / 2 + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [finrank_skewAdjoint_end, D.finrank_HW (by have := k.2; omega)]

end Sl2Data

end FormalResearch.FrameFree.OddWords
