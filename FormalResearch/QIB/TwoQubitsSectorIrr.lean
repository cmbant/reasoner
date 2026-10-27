import Mathlib
import FormalResearch.QIB.TwoQubitsSl2Rank

/-!
# Irreducibility of a `*`-closed `sl₂` triple with trivial commutant; the sector bridge

Namespace `FormalResearch.QIB`.  Claim class: **proved** (finite linear algebra).

* `Sl2Kernel.matIrr_of_scalar`: if `Hᴴ = H`, `Eᴴ = F` and every matrix commuting with `H, E, F` is a
  scalar, the triple is irreducible (`MatIrr`): the orthogonal complement of an invariant subspace is
  invariant, so the projection onto it commutes with the triple.
* `rank_tau_le_one_of_group`: **the abstract form of `prop:twoqubits`.**  Let `G'` have
  `IsotypicInvariants A G'` (commutant of `G'` is `⊕ I ⊗ M`).  Let `𝓗, 𝓔, 𝓕` satisfy the `sl₂` relations,
  `𝓗ᴴ = 𝓗`, `𝓔ᴴ = 𝓕`, and
  (`L1`) every matrix commuting with `G'` commutes with `𝓗, 𝓔, 𝓕`,
  (`L2`) every matrix commuting with `𝓗, 𝓔, 𝓕` commutes with `G'`.
  If a nonzero `α𝓗 + β𝓔 + γ𝓕` kills `v` then every multiplicity block `τ_l(v)` has rank at most one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder

namespace FormalResearch.QIB

namespace Sl2Kernel

section Centralizer
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The sesquilinear orthogonal complement. -/
def orthC (W : Submodule ℂ (A → ℂ)) : Submodule ℂ (A → ℂ) where
  carrier := {u | ∀ w ∈ W, star w ⬝ᵥ u = 0}
  add_mem' := by
    intro a b ha hb w hw
    rw [dotProduct_add, ha w hw, hb w hw, add_zero]
  zero_mem' := by intro w _; simp
  smul_mem' := by
    intro c a ha w hw
    rw [dotProduct_smul, ha w hw, smul_zero]

theorem mem_orthC {W : Submodule ℂ (A → ℂ)} {u : A → ℂ} :
    u ∈ orthC W ↔ ∀ w ∈ W, star w ⬝ᵥ u = 0 := Iff.rfl

theorem star_dotProduct_mulVec_adj (T : Matrix A A ℂ) (w u : A → ℂ) :
    star w ⬝ᵥ (T *ᵥ u) = star (Tᴴ *ᵥ w) ⬝ᵥ u := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

theorem disjoint_orthC (W : Submodule ℂ (A → ℂ)) : Disjoint W (orthC W) := by
  rw [Submodule.disjoint_def]
  intro w hw hw'
  exact dotProduct_star_self_eq_zero.1 (hw' w hw)

theorem isCompl_orthC (W : Submodule ℂ (A → ℂ)) : IsCompl W (orthC W) := by
  refine ⟨disjoint_orthC W, ?_⟩
  rw [codisjoint_iff]
  let b := Module.finBasis ℂ W
  let Ψ : (A → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun u i => star ((b i : W) : A → ℂ) ⬝ᵥ u
      map_add' := by intro a c; funext i; simp [dotProduct_add]
      map_smul' := by intro c a; funext i; simp [dotProduct_smul] }
  have hker : LinearMap.ker Ψ = orthC W := by
    ext u
    simp only [LinearMap.mem_ker, mem_orthC]
    constructor
    · intro h w hw
      have e := congrArg (fun x : W => (x : A → ℂ)) (b.sum_repr ⟨w, hw⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      have e' : w = ∑ i, b.repr ⟨w, hw⟩ i • ((b i : W) : A → ℂ) := e.symm
      rw [e', star_sum, sum_dotProduct]
      refine Finset.sum_eq_zero fun i _ => ?_
      have := congrFun h i
      simp only [star_smul, smul_dotProduct]
      have h2 : star ((b i : W) : A → ℂ) ⬝ᵥ u = 0 := this
      rw [h2]; simp
    · intro h
      funext i
      exact h _ (b i).2
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [hker] at hrn
  have h1 : Module.finrank ℂ (LinearMap.range Ψ) ≤ Module.finrank ℂ W := by
    calc Module.finrank ℂ (LinearMap.range Ψ)
        ≤ Module.finrank ℂ (Fin (Module.finrank ℂ W) → ℂ) := Submodule.finrank_le _
      _ = Module.finrank ℂ W := by simp
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq W (orthC W)
  rw [disjoint_iff.1 (disjoint_orthC W), finrank_bot] at h2
  have h3 := Submodule.finrank_le (W ⊔ orthC W)
  apply Submodule.eq_top_of_finrank_eq
  omega

theorem orthC_invariant {W : Submodule ℂ (A → ℂ)} (K : Matrix A A ℂ)
    (hK : ∀ w ∈ W, Kᴴ *ᵥ w ∈ W) : ∀ u ∈ orthC W, K *ᵥ u ∈ orthC W := by
  intro u hu w hw
  rw [star_dotProduct_mulVec_adj]
  exact hu _ (hK w hw)

/-- Irreducibility from a trivial commutant, for a `*`-closed triple. -/
theorem matIrr_of_scalar {H E F : Matrix A A ℂ} (hH : Hᴴ = H) (hE : Eᴴ = F)
    (hs : ∀ T : Matrix A A ℂ, T * H = H * T → T * E = E * T → T * F = F * T →
      ∃ c : ℂ, T = c • 1) : MatIrr H E F := by
  intro W hWH hWE hWF
  have hFE : Fᴴ = E := by rw [← hE, conjTranspose_conjTranspose]
  have hc := isCompl_orthC W
  have iH := orthC_invariant (W := W) H (fun w hw => by rw [hH]; exact hWH w hw)
  have iE := orthC_invariant (W := W) E (fun w hw => by rw [hE]; exact hWF w hw)
  have iF := orthC_invariant (W := W) F (fun w hw => by rw [hFE]; exact hWE w hw)
  let f : (A → ℂ) →ₗ[ℂ] (A → ℂ) := W.projection (orthC W) hc
  let T : Matrix A A ℂ := LinearMap.toMatrix' f
  have hT : ∀ u, T *ᵥ u = f u := fun u => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hdec : ∀ u : A → ℂ, ∃ w ∈ W, ∃ w' ∈ orthC W, u = w + w' := by
    intro u
    have : u ∈ W ⊔ orthC W := by rw [(isCompl_orthC W).sup_eq_top]; trivial
    obtain ⟨w, hw, w', hw', e⟩ := Submodule.mem_sup.1 this
    exact ⟨w, hw, w', hw', e.symm⟩
  have comm : ∀ K : Matrix A A ℂ, (∀ w ∈ W, K *ᵥ w ∈ W) → (∀ u ∈ orthC W, K *ᵥ u ∈ orthC W) →
      T * K = K * T := by
    intro K h1 h2
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    obtain ⟨w, hw, w', hw', rfl⟩ := hdec u
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hT]
    rw [Matrix.mulVec_add, map_add, map_add, Matrix.mulVec_add]
    have e1 : f w = w := Submodule.projection_apply_of_mem_left hc hw
    have e2 : f w' = 0 := Submodule.projection_apply_of_mem_right hc hw'
    have e3 : f (K *ᵥ w) = K *ᵥ w := Submodule.projection_apply_of_mem_left hc (h1 w hw)
    have e4 : f (K *ᵥ w') = 0 := Submodule.projection_apply_of_mem_right hc (h2 w' hw')
    rw [e1, e2, e3, e4]
    simp
  obtain ⟨c, hc'⟩ := hs T (comm H hWH iH) (comm E hWE iE) (comm F hWF iF)
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have e1 : f w = w := Submodule.projection_apply_of_mem_left hc hw
    have e2 : f w = c • w := by rw [← hT, hc', Matrix.smul_mulVec, Matrix.one_mulVec]
    have hc1 : c = 1 := by
      have : (c - 1) • w = 0 := by rw [sub_smul, ← e2, e1, one_smul, sub_self]
      rcases smul_eq_zero.1 this with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hw0
    rw [eq_top_iff]
    intro u _
    have : f u = u := by rw [← hT, hc', hc1, Matrix.smul_mulVec, Matrix.one_mulVec, one_smul]
    rw [← this]
    exact Submodule.projection_apply_mem hc u

end Centralizer

end Sl2Kernel


/-! ## The sector bridge -/

section Bridge

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- The inclusion `ℂ^{A l} → ℂ^{Idx A B}` of the `b0`-slice of sector `l`. -/
def sliceIn (l : Λ) (b0 : B l) : Matrix (Idx A B) (A l) ℂ :=
  fun p a => if p = ⟨l, (a, b0)⟩ then 1 else 0

/-- The restriction `ℂ^{Idx A B} → ℂ^{A l}` to the `b0`-slice of sector `l`. -/
def sliceOut (l : Λ) (b0 : B l) : Matrix (A l) (Idx A B) ℂ :=
  fun a q => if q = ⟨l, (a, b0)⟩ then 1 else 0

theorem mul_sliceIn_apply (K : Matrix (Idx A B) (Idx A B) ℂ) (l : Λ) (b0 : B l) (p : Idx A B)
    (a : A l) : (K * sliceIn (A := A) (B := B) l b0 : Matrix (Idx A B) (A l) ℂ) p a = K p ⟨l, (a, b0)⟩ := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨l, (a, b0)⟩ : Idx A B)]
  · simp [sliceIn]
  · intro q _ hq
    simp [sliceIn, hq]
  · simp

theorem sliceOut_mul_apply (K : Matrix (Idx A B) (Idx A B) ℂ) (l : Λ) (b0 : B l) (a : A l)
    (q : Idx A B) : (sliceOut (A := A) (B := B) l b0 * K : Matrix (A l) (Idx A B) ℂ) a q = K ⟨l, (a, b0)⟩ q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨l, (a, b0)⟩ : Idx A B)]
  · simp [sliceOut]
  · intro p _ hp
    simp [sliceOut, hp]
  · simp

theorem sliceIn_mul_same (l : Λ) (b0 : B l) (N : Matrix (A l) (A l) ℂ) (a1 a : A l) :
    (sliceIn (A := A) (B := B) l b0 * N : Matrix (Idx A B) (A l) ℂ) ⟨l, (a1, b0)⟩ a = N a1 a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a1]
  · simp [sliceIn]
  · intro x _ hx
    simp [sliceIn, hx.symm]
  · simp

theorem sliceIn_mul_ne_b (l : Λ) (b0 : B l) (N : Matrix (A l) (A l) ℂ) (a1 a : A l) (c1 : B l)
    (hc : c1 ≠ b0) : (sliceIn (A := A) (B := B) l b0 * N : Matrix (Idx A B) (A l) ℂ) ⟨l, (a1, c1)⟩ a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [sliceIn, hc]

theorem sliceIn_mul_ne_l (l : Λ) (b0 : B l) (N : Matrix (A l) (A l) ℂ) {l1 : Λ} (hl : l1 ≠ l)
    (a1 : A l1) (c1 : B l1) (a : A l) :
    (sliceIn (A := A) (B := B) l b0 * N : Matrix (Idx A B) (A l) ℂ) ⟨l1, (a1, c1)⟩ a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [sliceIn, hl]

theorem mul_sliceOut_same (l : Λ) (b0 : B l) (N : Matrix (A l) (A l) ℂ) (a a1 : A l) :
    (N * sliceOut (A := A) (B := B) l b0 : Matrix (A l) (Idx A B) ℂ) a ⟨l, (a1, b0)⟩ = N a a1 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a1]
  · simp [sliceOut]
  · intro x _ hx
    simp [sliceOut, hx.symm]
  · simp

theorem mul_sliceOut_ne_b (l : Λ) (b0 : B l) (N : Matrix (A l) (A l) ℂ) (a a1 : A l) (c1 : B l)
    (hc : c1 ≠ b0) : (N * sliceOut (A := A) (B := B) l b0 : Matrix (A l) (Idx A B) ℂ) a ⟨l, (a1, c1)⟩ = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [sliceOut, hc]

theorem mul_sliceOut_ne_l (l : Λ) (b0 : B l) (N : Matrix (A l) (A l) ℂ) {l1 : Λ} (hl : l1 ≠ l)
    (a : A l) (a1 : A l1) (c1 : B l1) :
    (N * sliceOut (A := A) (B := B) l b0 : Matrix (A l) (Idx A B) ℂ) a ⟨l1, (a1, c1)⟩ = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [sliceOut, hl]

variable {K : Matrix (Idx A B) (Idx A B) ℂ}

theorem K_sliceIn (hK : Comm A K) (l : Λ) (b0 : B l) :
    K * sliceIn (A := A) (B := B) l b0 = sliceIn (A := A) (B := B) l b0 * blk K l b0 := by
  ext ⟨l1, a1, c1⟩ a
  rw [mul_sliceIn_apply]
  by_cases hl : l1 = l
  · subst hl
    by_cases hc : c1 = b0
    · subst hc
      rw [sliceIn_mul_same]; rfl
    · rw [sliceIn_mul_ne_b _ _ _ _ _ _ hc, col_same hK l1 a1 c1 a b0 b0]
      simp [hc]
  · rw [sliceIn_mul_ne_l _ _ _ hl, col_ne hK hl]

theorem sliceOut_K (hK : Comm A K) (l : Λ) (b0 : B l) :
    sliceOut (A := A) (B := B) l b0 * K = blk K l b0 * sliceOut (A := A) (B := B) l b0 := by
  ext a ⟨l1, a1, c1⟩
  rw [sliceOut_mul_apply]
  by_cases hl : l1 = l
  · subst hl
    by_cases hc : c1 = b0
    · subst hc
      rw [mul_sliceOut_same]; rfl
    · rw [mul_sliceOut_ne_b _ _ _ _ _ _ hc, col_same hK l1 a b0 a1 c1 b0]
      simp [Ne.symm hc]
  · rw [mul_sliceOut_ne_l _ _ _ hl, col_ne hK (Ne.symm hl)]


/-- **A matrix commuting with the blocks of `𝓗, 𝓔, 𝓕` is scalar**, given that the commutant of `𝓗, 𝓔, 𝓕`
lies in the commutant of `G'` and the commutant of `G'` is `⊕ I ⊗ M`. -/
theorem sector_commutant_scalar {G' : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G')
    {𝓗 𝓔 𝓕 : Matrix (Idx A B) (Idx A B) ℂ} (hH : Comm A 𝓗) (hE : Comm A 𝓔) (hF : Comm A 𝓕)
    (hL2 : ∀ M : Matrix (Idx A B) (Idx A B) ℂ, M * 𝓗 = 𝓗 * M → M * 𝓔 = 𝓔 * M → M * 𝓕 = 𝓕 * M →
      ∀ U ∈ G', U * M = M * U)
    (l : Λ) (b0 : B l) (T : Matrix (A l) (A l) ℂ)
    (hTH : T * blk 𝓗 l b0 = blk 𝓗 l b0 * T) (hTE : T * blk 𝓔 l b0 = blk 𝓔 l b0 * T)
    (hTF : T * blk 𝓕 l b0 = blk 𝓕 l b0 * T) : ∃ c : ℂ, T = c • 1 := by
  obtain ⟨ι, hι⟩ : ∃ ι : Matrix (Idx A B) (A l) ℂ, ι = sliceIn (A := A) (B := B) l b0 := ⟨_, rfl⟩
  obtain ⟨π, hπ⟩ : ∃ π : Matrix (A l) (Idx A B) ℂ, π = sliceOut (A := A) (B := B) l b0 := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Idx A B) (Idx A B) ℂ, M = ι * T * π := ⟨_, rfl⟩
  have hM : ∀ K' : Matrix (Idx A B) (Idx A B) ℂ, Comm A K' →
      T * blk K' l b0 = blk K' l b0 * T → M * K' = K' * M := by
    intro K' hK' hT
    have e1 : K' * ι = ι * blk K' l b0 := by rw [hι]; exact K_sliceIn hK' l b0
    have e2 : π * K' = blk K' l b0 * π := by rw [hπ]; exact sliceOut_K hK' l b0
    calc M * K' = ι * T * (π * K') := by rw [hMdef, Matrix.mul_assoc]
      _ = ι * T * (blk K' l b0 * π) := by rw [e2]
      _ = ι * (T * blk K' l b0) * π := by simp only [Matrix.mul_assoc]
      _ = ι * (blk K' l b0 * T) * π := by rw [hT]
      _ = (ι * blk K' l b0) * T * π := by simp only [Matrix.mul_assoc]
      _ = (K' * ι) * T * π := by rw [e1]
      _ = K' * M := by rw [hMdef]; simp only [Matrix.mul_assoc]
  obtain ⟨X, hX⟩ := (hG M).1 (hL2 M (hM _ hH hTH) (hM _ hE hTE) (hM _ hF hTF))
  refine ⟨X l b0 b0, ?_⟩
  ext a a'
  have h1 : M ⟨l, (a, b0)⟩ ⟨l, (a', b0)⟩ = T a a' := by
    rw [hMdef, hι, hπ]
    simp [Matrix.mul_apply, sliceIn, sliceOut]
  rw [← h1, hX, blockOp_apply_same]
  simp [Matrix.one_apply]

theorem blk_conjTranspose (K : Matrix (Idx A B) (Idx A B) ℂ) (l : Λ) (b : B l) :
    (blk K l b)ᴴ = blk Kᴴ l b := by
  ext a a'
  simp [blk, Matrix.conjTranspose_apply]

/-- **Abstract form of `prop:twoqubits`, product form**: `τ_l(v) = |u⟩⟨u|`.  See the module docstring. -/
theorem exists_vecMulVec_of_group {G' : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G')
    {𝓗 𝓔 𝓕 : Matrix (Idx A B) (Idx A B) ℂ}
    (hHE : 𝓗 * 𝓔 - 𝓔 * 𝓗 = (2 : ℂ) • 𝓔) (hHF : 𝓗 * 𝓕 - 𝓕 * 𝓗 = -((2 : ℂ) • 𝓕))
    (hEF : 𝓔 * 𝓕 - 𝓕 * 𝓔 = 𝓗) (hHh : 𝓗ᴴ = 𝓗) (hEh : 𝓔ᴴ = 𝓕)
    (hL1 : ∀ M : Matrix (Idx A B) (Idx A B) ℂ, (∀ U ∈ G', U * M = M * U) →
      M * 𝓗 = 𝓗 * M ∧ M * 𝓔 = 𝓔 * M ∧ M * 𝓕 = 𝓕 * M)
    (hL2 : ∀ M : Matrix (Idx A B) (Idx A B) ℂ, M * 𝓗 = 𝓗 * M → M * 𝓔 = 𝓔 * M → M * 𝓕 = 𝓕 * M →
      ∀ U ∈ G', U * M = M * U)
    (l : Λ) (b0 : B l) [Nonempty (A l)]
    (α β γ : ℂ) (hne : α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0)
    (v : Idx A B → ℂ) (hv : (α • 𝓗 + β • 𝓔 + γ • 𝓕) *ᵥ v = 0) :
    ∃ u : B l → ℂ, tau v l = Matrix.vecMulVec u (star u) := by
  have hcomm : ∀ X : ∀ l, Matrix (B l) (B l) ℂ, ∀ U ∈ G', U * blockOp A X = blockOp A X * U :=
    fun X => (hG _).2 ⟨X, rfl⟩
  have hH : Comm A 𝓗 := fun X => ((hL1 _ (hcomm X)).1).symm
  have hE : Comm A 𝓔 := fun X => ((hL1 _ (hcomm X)).2.1).symm
  have hF : Comm A 𝓕 := fun X => ((hL1 _ (hcomm X)).2.2).symm
  refine exists_vecMulVec_of_stabiliser hH hE hF hHE hHF hEF l b0 ?_ α β γ hne v hv
  have hFh : 𝓕ᴴ = 𝓔 := by rw [← hEh, conjTranspose_conjTranspose]
  refine Sl2Kernel.matIrr_of_scalar (by rw [blk_conjTranspose, hHh]) (by rw [blk_conjTranspose, hEh]) ?_
  intro T h1 h2 h3
  exact sector_commutant_scalar hG hH hE hF hL2 l b0 T h1 h2 h3


/-- **Abstract form of `prop:twoqubits`, rank form.** -/
theorem rank_tau_le_one_of_group {G' : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G')
    {𝓗 𝓔 𝓕 : Matrix (Idx A B) (Idx A B) ℂ}
    (hHE : 𝓗 * 𝓔 - 𝓔 * 𝓗 = (2 : ℂ) • 𝓔) (hHF : 𝓗 * 𝓕 - 𝓕 * 𝓗 = -((2 : ℂ) • 𝓕))
    (hEF : 𝓔 * 𝓕 - 𝓕 * 𝓔 = 𝓗) (hHh : 𝓗ᴴ = 𝓗) (hEh : 𝓔ᴴ = 𝓕)
    (hL1 : ∀ M : Matrix (Idx A B) (Idx A B) ℂ, (∀ U ∈ G', U * M = M * U) →
      M * 𝓗 = 𝓗 * M ∧ M * 𝓔 = 𝓔 * M ∧ M * 𝓕 = 𝓕 * M)
    (hL2 : ∀ M : Matrix (Idx A B) (Idx A B) ℂ, M * 𝓗 = 𝓗 * M → M * 𝓔 = 𝓔 * M → M * 𝓕 = 𝓕 * M →
      ∀ U ∈ G', U * M = M * U)
    (l : Λ) (b0 : B l) [Nonempty (A l)]
    (α β γ : ℂ) (hne : α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0)
    (v : Idx A B → ℂ) (hv : (α • 𝓗 + β • 𝓔 + γ • 𝓕) *ᵥ v = 0) :
    (tau v l).rank ≤ 1 := by
  obtain ⟨u, hu⟩ := exists_vecMulVec_of_group hG hHE hHF hEF hHh hEh hL1 hL2 l b0 α β γ hne v hv
  rw [hu]
  exact Matrix.rank_vecMulVec_le _ _

end Bridge

end FormalResearch.QIB
