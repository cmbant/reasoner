module

public import FormalResearch.Special.AiryTransformLiouville

/-!
# `{K(·,a_n)/|Ai'(a_n)|}_{n ≥ 1}` is an orthonormal basis of the Airy Paley–Wiener space; Parseval

`PW = ker (K_Ai - 1) ⊂ L²(ℝ)` (`AiryTransformProj`) is a closed subspace, hence a Hilbert space.  Combining

* orthonormality of `e_n = K(·,a_n)/|Ai'(a_n)|` (`airyBasisVec_orthonormal`, `AiryTransformBasis`), and
* completeness (`airyPW_eq_zero_of_inner_liouville`, `AiryTransformLiouville`: good circles + Liouville, no Hardy space),

we get the Hilbert basis `airyPW_hilbertBasis : HilbertBasis ℕ ℂ airyPW` and the Parseval identities

* `airyPW_hasSum_inner`: `⟨G,F⟩ = Σ_n ⟨G,e_n⟩⟨e_n,F⟩` for `F, G ∈ PW`;
* `airyPW_parseval_of_basis`: the same with `⟨e_n, F⟩ \overline{⟨e_n, G⟩}`, where `⟨e_n, Aφ⟩ = Ψφ(a_n)/|Ai'(a_n)|`.

The route is independent of `AiryTransformParseval` (which proves the same Parseval identity from Theorem Q, a Hardy-space
statement); the two are mutual cross-checks and neither is used by the other.

**Not formalised:** the Paley–Wiener-type characterisation of `PW` by growth of entire functions; Parseval for the
`HilbertBasis` is stated in `PW`-valued inner products, the function form with entire representatives is in
`AiryTransformRKHS` (`airyPW_parseval_fun`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped ComplexInnerProductSpace Real

namespace FormalResearch.Special

/-- `e_n` as an element of the Hilbert space `PW`. -/
noncomputable def airyBasisVecPW (n : ℕ) : airyPW := ⟨airyBasisVec n, airyBasisVec_mem n⟩

theorem airyBasisVecPW_orthonormal : Orthonormal ℂ airyBasisVecPW := by
  rw [orthonormal_iff_ite]
  intro n m
  have := (orthonormal_iff_ite.mp airyBasisVec_orthonormal) n m
  simpa [airyBasisVecPW, Submodule.coe_inner] using this

instance : CompleteSpace airyPW := isClosed_airyPW.completeSpace_coe

/-- **`{K(·, a_n)/|Ai'(a_n)|}_{n ≥ 1}` is an orthonormal basis of the Airy Paley–Wiener space `PW`.** -/
noncomputable def airyPW_hilbertBasis : HilbertBasis ℕ ℂ airyPW :=
  HilbertBasis.mkOfOrthogonalEqBot airyBasisVecPW_orthonormal (by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : ∀ n, inner ℂ (airyBasisVecPW n) x = 0 := fun n =>
      (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨n, rfl⟩)
    have : (x : AiryL2) = 0 := airyPW_eq_zero_of_inner_liouville x.2 fun n => by
      have := hx' n
      simpa [airyBasisVecPW, Submodule.coe_inner] using this
    exact Subtype.ext this)

theorem coe_airyPW_hilbertBasis : ⇑airyPW_hilbertBasis = airyBasisVecPW :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- **Parseval for the Hilbert basis**: `⟨G,F⟩ = Σ_n ⟨G, e_n⟩⟨e_n, F⟩`. -/
theorem airyPW_hasSum_inner (F G : airyPW) :
    HasSum (fun n : ℕ => inner ℂ G (airyBasisVecPW n) * inner ℂ (airyBasisVecPW n) F) (inner ℂ G F) := by
  have := airyPW_hilbertBasis.hasSum_inner_mul_inner G F
  rwa [coe_airyPW_hilbertBasis] at this

/-- **Parseval on `PW` at the zeros of `Ai`** (Hardy-free): `⟨G, F⟩ = Σ_n ⟨e_n, F⟩ \overline{⟨e_n, G⟩}` for `F, G ∈ PW`. -/
theorem airyPW_parseval_of_basis {F G : AiryL2} (hF : F ∈ airyPW) (hG : G ∈ airyPW) :
    HasSum (fun n : ℕ => inner ℂ (airyBasisVec n) F * (starRingEnd ℂ) (inner ℂ (airyBasisVec n) G))
      (inner ℂ G F) := by
  have h := airyPW_hasSum_inner ⟨F, hF⟩ ⟨G, hG⟩
  have h' : HasSum (fun n : ℕ => inner ℂ (airyBasisVec n) F * (starRingEnd ℂ) (inner ℂ (airyBasisVec n) G))
      (inner ℂ (⟨G, hG⟩ : airyPW) (⟨F, hF⟩ : airyPW)) := by
    convert h using 2 with n
    rw [mul_comm, ← inner_conj_symm (airyBasisVec n) G]
    simp [airyBasisVecPW, Submodule.coe_inner]
  simpa [Submodule.coe_inner] using h'

/-- info: 'FormalResearch.Special.airyPW_hilbertBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_hilbertBasis

/-- info: 'FormalResearch.Special.airyPW_hasSum_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_hasSum_inner

/-- info: 'FormalResearch.Special.airyPW_parseval_of_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_parseval_of_basis

end FormalResearch.Special
