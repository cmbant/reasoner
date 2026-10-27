import Mathlib
import FormalResearch.FrameFree.WeylVertex
import FormalResearch.QID.D4DoublyStochasticCertificate

/-!
# Linking `weylSet` (FrameFree) with `allD4` (QID)

Both model `W(D₄)` as pairs `(σ, e)` of a permutation of `Fin 4` and a sign vector with an even
number of minus signs, but with transposed conventions:

* FrameFree: `(w d)_k = sg(e k) · d_{σ k}`, i.e. matrix entry `W[k, σ k] = sg (e k)`
  (`weylVal d w = dᵀ W d`).
* QID: `d4SignedMatrix (σ, e) r c = if r = σ c then ±1 (sign e c) else 0`, i.e. `e_c ↦ ±e_{σ c}`,
  entry `M[σ c, c] = sg (e c)`.

The bijection is the involution `linkSP (σ, e) = (σ⁻¹, e ∘ σ⁻¹)`; it sends `weylSet` onto `allD4`,
and `d4SignedMatrix (linkSP w) = weylMat w` entrywise.  Hence any QID fact about `allD4`
(orbits, facet scores, doubly-stochastic certificate) transports to `weylSet` via `linkSP`.
-/

open Finset

namespace FormalResearch.FrameFree

open FormalResearch.QID

/-- The signed permutation matrix of `w : SP` in FrameFree's convention, `W[k, σ k] = sg (e k)`. -/
def weylMat (w : SP) : Matrix (Fin 4) (Fin 4) ℤ := fun k j => if j = w.1 k then sg (w.2 k) else 0

/-- The involutive change of convention `(σ, e) ↦ (σ⁻¹, e ∘ σ⁻¹)` between FrameFree's `SP` and QID's
`D4SignedPerm` (both are `Equiv.Perm (Fin 4) × (Fin 4 → Bool)`). -/
def linkSP (w : SP) : D4SignedPerm := (w.1⁻¹, fun k => w.2 (w.1⁻¹ k))

theorem linkSP_linkSP (w : SP) : linkSP (linkSP w) = w := by
  obtain ⟨σ, e⟩ := w
  simp [linkSP]

theorem linkSP_involutive : Function.Involutive linkSP := linkSP_linkSP

theorem linkSP_bijective : Function.Bijective linkSP := linkSP_involutive.bijective

/-- `linkSP` as an equivalence `SP ≃ D4SignedPerm`. -/
def linkEquiv : SP ≃ D4SignedPerm := linkSP_involutive.toPerm linkSP

theorem linkSP_mem_iff (w : SP) : w ∈ weylSet ↔ linkSP w ∈ allD4 := by
  revert w; decide +kernel

theorem linkSP_mem_allD4 {w : SP} (hw : w ∈ weylSet) : linkSP w ∈ allD4 := (linkSP_mem_iff w).1 hw

/-- `linkSP` restricts to an equivalence `weylSet ≃ allD4` (as subtypes of finsets). -/
def linkWeylEquiv : weylSet ≃ allD4 where
  toFun w := ⟨linkSP w.1, linkSP_mem_allD4 w.2⟩
  invFun p := ⟨linkSP p.1, (linkSP_mem_iff _).2 (by rw [linkSP_linkSP]; exact p.2)⟩
  left_inv w := Subtype.ext (linkSP_linkSP _)
  right_inv p := Subtype.ext (linkSP_linkSP _)

theorem linkSP_image_weylSet : weylSet.image linkSP = allD4 := by
  ext p
  simp only [mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact linkSP_mem_allD4 hw
  · intro hp
    exact ⟨linkSP p, (linkSP_mem_iff _).2 (by rw [linkSP_linkSP]; exact hp), linkSP_linkSP p⟩

/-- **Matrices agree**: the QID matrix of `linkSP w` is FrameFree's signed permutation matrix. -/
theorem d4SignedMatrix_linkSP (w : SP) :
    d4SignedMatrix (linkSP w) = (weylMat w).map (Int.cast : ℤ → ℚ) := by
  obtain ⟨σ, e⟩ := w
  ext r c
  have h1 : (linkSP (σ, e)).1 = σ⁻¹ := rfl
  have h2 : (linkSP (σ, e)).2 c = e (σ⁻¹ c) := rfl
  simp only [d4SignedMatrix, weylMat, Matrix.map_apply, sg, h2]
  by_cases h : r = (linkSP (σ, e)).1 c
  · have h' : r = σ⁻¹ c := by rwa [h1] at h
    have hc : c = σ r := by rw [h']; simp
    rw [if_pos h, if_pos hc, ← h']
    split_ifs <;> simp
  · have h' : ¬ r = σ⁻¹ c := by rwa [h1] at h
    have hc : ¬ c = σ r := fun hc => h' (by rw [hc]; simp)
    rw [if_neg h, if_neg hc]; simp

/-- The QID action on rational vectors is `W v` for FrameFree's matrix. -/
theorem d4Act_linkSP (w : SP) (v : D4Vec) :
    d4Act (linkSP w) v = ((weylMat w).map (Int.cast : ℤ → ℚ)).mulVec v := by
  unfold d4Act; rw [d4SignedMatrix_linkSP]

/-- The coordinate formula `(w v)_k = sg(e k) v_{σ k}`, matching `weylVal`. -/
theorem d4Act_linkSP_apply (w : SP) (v : D4Vec) (k : Fin 4) :
    d4Act (linkSP w) v k = (sg (w.2 k) : ℚ) * v (w.1 k) := by
  rw [d4Act_linkSP]
  simp [Matrix.mulVec, dotProduct, weylMat]

/-- `weylVal` is the bilinear form `dᵀ W d` of the QID action, on rational data. -/
theorem weylVal_ratCast (v : D4Vec) (w : SP) :
    weylVal (fun k => (v k : ℂ)) w = ((d4Dot v (d4Act (linkSP w) v) : ℚ) : ℂ) := by
  unfold weylVal d4Dot
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [d4Act_linkSP_apply]; push_cast; ring

end FormalResearch.FrameFree
