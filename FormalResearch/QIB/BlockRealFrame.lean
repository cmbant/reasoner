import Mathlib
import FormalResearch.QIB.BlockRealCore
import FormalResearch.FrameFree.TwirlsTwirl

/-!
# The frame-group commutant is real-spanned and `σ ~ σ⁻¹` inside it

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis, no new axiom).

Bridge between the slot-permutation picture of `FrameFree/TwirlsSchurWeyl.lean` (qubits indexed by
`Fin n × Fin k`, `commutant_eq_blockPermSpan`) and the `Copies n k = Fin k → Fin n → Fin 2` picture of
`Helstrom.Pe` / `frameGroup n k` (`BlockDecomp.lean`).

* `slotEquiv`, `slotAlg`: the reindexing algebra isomorphism `OpS (Fin n × Fin k) ≃ₐ Matrix (Copies n k)`;
  `slotAlg_tensOp`: it sends `⊗ u_{π i}` to `rotK k u`.
* `commSub_frameGroup_iff`: `X` commutes with the frame group iff it lies in the (reindexed) span of the
  block-preserving slot permutations.
* `exists_conj_inv`: every block-preserving slot permutation `σ` is conjugate to `σ⁻¹` by a
  block-preserving one (cycle types of `σ` and `σ⁻¹` agree in each block, Mathlib `isConj_iff_cycleType_eq`).
* `frame_real_data`: hence the hypotheses `hSC, hCS, hreal, hconj` of `sectorProj_real` hold for the frame
  group, with `S` the set of reindexed block permutation matrices.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Twirls (OpS tensOp permOp blockPermSpan permOp_mul permOp_one
  permOp_conjTranspose permOp_map_conj commutant_eq_blockPermSpan tensOp_commute permOp_mem_blockPermSpan)
open FormalResearch.FrameFree.Helstrom (Copies rotK copies)
open FormalResearch.FrameFree.NQubit (Op1 SU2)

section Slots

variable (n k : ℕ)

/-- Slot picture to copy picture: `(Fin n × Fin k → Fin 2) ≃ (Fin k → Fin n → Fin 2)`. -/
def slotEquiv : (Fin n × Fin k → Fin 2) ≃ Copies n k where
  toFun x := fun c a => x (a, c)
  invFun y := fun p => y p.2 p.1
  left_inv x := by funext p; rfl
  right_inv y := by funext c a; rfl

/-- The reindexing algebra isomorphism. -/
noncomputable def slotAlg : OpS (Fin n × Fin k) ≃ₐ[ℂ] Matrix (Copies n k) (Copies n k) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (slotEquiv n k)

variable {n k}

theorem slotAlg_apply (M : OpS (Fin n × Fin k)) (x y : Copies n k) :
    slotAlg n k M x y = M ((slotEquiv n k).symm x) ((slotEquiv n k).symm y) := rfl

theorem slotAlg_map_conj (M : OpS (Fin n × Fin k)) :
    (slotAlg n k M).map conj = slotAlg n k (M.map conj) := by
  ext x y; rfl

theorem slotAlg_transpose (M : OpS (Fin n × Fin k)) :
    (slotAlg n k M)ᵀ = slotAlg n k Mᵀ := by
  ext x y; rfl

theorem slotAlg_tensOp (u : Fin n → Op1) :
    slotAlg n k (tensOp (Prod.fst : Fin n × Fin k → Fin n) u) = rotK k u := by
  ext x y
  simp only [slotAlg_apply, tensOp, Matrix.of_apply, rotK, FormalResearch.FrameFree.Helstrom.kron,
    Fintype.prod_prod_type]
  rw [Finset.prod_comm]
  rfl

theorem commSub_frameGroup_iff (X : Matrix (Copies n k) (Copies n k) ℂ) :
    X ∈ commSub (frameGroup n k) ↔
      (slotAlg n k).symm X ∈ blockPermSpan (Prod.fst : Fin n × Fin k → Fin n) := by
  rw [← commutant_eq_blockPermSpan, mem_commSub]
  constructor
  · intro h u hu
    have := h (rotK k u) ⟨u, hu, rfl⟩
    have h2 := congrArg (slotAlg n k).symm this
    rw [map_mul, map_mul, ← slotAlg_tensOp, AlgEquiv.symm_apply_apply] at h2
    exact h2.symm
  · rintro h _ ⟨u, hu, rfl⟩
    have := h u hu
    have h2 := congrArg (slotAlg n k) this
    rw [map_mul, map_mul, slotAlg_tensOp, AlgEquiv.apply_symm_apply] at h2
    exact h2.symm

theorem exists_conj_inv (σ : Equiv.Perm (Fin n × Fin k)) (hσ : ∀ i, (σ i).1 = i.1) :
    ∃ τ : Equiv.Perm (Fin n × Fin k), (∀ i, (τ i).1 = i.1) ∧ τ * σ = σ⁻¹ * τ := by
  classical
  -- the restriction of `σ` to block `a`
  have hres : ∀ a : Fin n, Function.Bijective (fun c : Fin k => (σ (a, c)).2) := by
    intro a
    have hinj : Function.Injective (fun c : Fin k => (σ (a, c)).2) := by
      intro c c' h
      have h1 : σ (a, c) = σ (a, c') := Prod.ext (by rw [hσ, hσ]) h
      exact (Prod.mk.inj (σ.injective h1)).2
    exact hinj.bijective_of_finite
  let σa : Fin n → Equiv.Perm (Fin k) := fun a => Equiv.ofBijective _ (hres a)
  have hσa : ∀ a c, σ (a, c) = (a, σa a c) := by
    intro a c
    exact Prod.ext (hσ _) rfl
  have hconj : ∀ a, ∃ ρ : Equiv.Perm (Fin k), ρ * σa a * ρ⁻¹ = (σa a)⁻¹ := by
    intro a
    have : IsConj (σa a) (σa a)⁻¹ := by
      rw [Equiv.Perm.isConj_iff_cycleType_eq, Equiv.Perm.cycleType_inv]
    exact isConj_iff.1 this
  choose ρ hρ using hconj
  refine ⟨⟨fun p => (p.1, ρ p.1 p.2), fun p => (p.1, (ρ p.1)⁻¹ p.2), ?_, ?_⟩, fun i => rfl, ?_⟩
  · intro p; simp
  · intro p; simp
  · apply Equiv.ext
    rintro ⟨a, c⟩
    have h1 : ρ a (σa a c) = (σa a)⁻¹ (ρ a c) := by
      have e : ρ a * σa a = (σa a)⁻¹ * ρ a := by
        rw [← hρ a]; group
      simpa using congrArg (fun f => f c) e
    have h2 : σ⁻¹ (a, ρ a c) = (a, (σa a)⁻¹ (ρ a c)) := by
      rw [Equiv.Perm.inv_eq_iff_eq, hσa]; simp
    simp only [Equiv.Perm.mul_apply, Equiv.coe_fn_mk]
    rw [hσa, h2, h1]

theorem permOp_transpose {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    (permOp σ)ᵀ = permOp σ⁻¹ := by
  rw [← permOp_conjTranspose]
  ext x y
  have h := congrFun (congrFun (permOp_map_conj σ) y) x
  simp only [Matrix.map_apply] at h
  simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply, Complex.star_def]
  exact h.symm

/-- The reindexed block-preserving slot permutation matrices on `Copies n k`. -/
def frameS (n k : ℕ) : Set (Matrix (Copies n k) (Copies n k) ℂ) :=
  {M | ∃ σ : Equiv.Perm (Fin n × Fin k), (∀ i, (σ i).1 = i.1) ∧ M = slotAlg n k (permOp σ)}

/-- The data feeding `sectorProj_real` for the frame group: its commutant is the span of the real
matrices `frameS`, each conjugate to its transpose by an element of `frameS`. -/
theorem frame_real_data (n k : ℕ) :
    frameS n k ⊆ (commSub (frameGroup n k) : Set _) ∧
    (∀ X ∈ commSub (frameGroup n k), X ∈ Submodule.span ℂ (frameS n k)) ∧
    (∀ p ∈ frameS n k, p.map conj = p) ∧
    (∀ p ∈ frameS n k, ∃ q ∈ frameS n k, q * p = pᵀ * q ∧ qᵀ * q = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [SetLike.mem_coe, commSub_frameGroup_iff, AlgEquiv.symm_apply_apply]
    exact permOp_mem_blockPermSpan _ σ hσ
  · intro X hX
    have hY := (commSub_frameGroup_iff X).1 hX
    have key : ∀ Y ∈ blockPermSpan (Prod.fst : Fin n × Fin k → Fin n),
        slotAlg n k Y ∈ Submodule.span ℂ (frameS n k) := by
      intro Y hY
      induction hY using Submodule.span_induction with
      | mem M hM =>
        obtain ⟨σ, hσ, rfl⟩ := hM
        exact Submodule.subset_span ⟨σ, hσ, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
    have := key _ hY
    rwa [AlgEquiv.apply_symm_apply] at this
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [slotAlg_map_conj, permOp_map_conj]
  · rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨τ, hτ, hτσ⟩ := exists_conj_inv σ hσ
    refine ⟨slotAlg n k (permOp τ), ⟨τ, hτ, rfl⟩, ?_, ?_⟩
    · rw [slotAlg_transpose, permOp_transpose, ← map_mul, ← map_mul, permOp_mul, permOp_mul, hτσ]
    · rw [slotAlg_transpose, permOp_transpose, ← map_mul, permOp_mul, inv_mul_cancel, permOp_one,
        map_one]

end Slots

end FormalResearch.QIB
