import Mathlib
import FormalResearch.QIB.BlockDecomp
import FormalResearch.QIB.BlockCoordinates
import FormalResearch.QIB.BlockTwirl

/-!
# Real central projectors of a real-spanned commutant (core of the real-structure input)

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis, no new axiom).

`BlockAntiunitary.lean` needs the multiplicity blocks of the second vector to be the entrywise conjugates
of the first's (`hconj`), which is a statement about *real* isotypic coordinates.  The part of this that
needs no representation theory of `SU(2)` is that the sector projectors are real.  This file proves it
for any commutant spanned by real matrices that are conjugate to their transposes inside the commutant
(for the frame group: the block permutation matrices, `σ` conjugate to `σ⁻¹` in `S_k^n`).

* `real_of_primitive_central`: abstract statement.  `C` is a subspace spanned by a set `S` of real
  matrices; every `p ∈ S` has `q ∈ S` with `q p q⁻¹ = pᵀ`.  Then every Hermitian primitive central
  idempotent `Z` of `C` is real.  (Proof: `Tr(Z̄ X) = Tr(Z X)` on `C` by `Tr(Z p) = Tr(Z̄ pᵀ)` and
  centrality, so `Z̄ Z ≠ 0`, so `Z Z̄ = Z` by primitivity; conjugate.)
* `sectorProj A W l = W (⊕ δ_l) Wᴴ`, its properties in isotypic coordinates
  (`sectorProj_mem_iff`, central, primitive), and `sectorProj_real` combining the two.
* `tr_tau_eq`: `Tr τ_l(Wᴴ a) = ⟨a| sectorProj l |a⟩`.
* `tau_mulVec_of_mem`: `τ_l(U v) = τ_l(v)` for a unitary `U` of the group (frame rotations do not
  change the multiplicity blocks).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped MatrixOrder ComplexOrder

namespace FormalResearch.QIB

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_conj_mul (A B : Matrix ι ι ℂ) : (A * B).map conj = A.map conj * B.map conj :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem map_conj_conj (A : Matrix ι ι ℂ) : (A.map conj).map conj = A := by
  ext i j; simp

theorem transpose_eq_map_conj_of_hermitian {Z : Matrix ι ι ℂ} (h : Zᴴ = Z) : Zᵀ = Z.map conj := by
  ext i j
  have h2 : star (Z j i) = Z i j := by
    simpa [Matrix.conjTranspose_apply] using congrArg (fun M : Matrix ι ι ℂ => M i j) h
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  rw [← h2]; simp [Complex.star_def]

/-- **Real primitive central idempotents.**  See the module docstring. -/
theorem real_of_primitive_central (C : Submodule ℂ (Matrix ι ι ℂ)) (S : Set (Matrix ι ι ℂ))
    (hSC : S ⊆ C) (hCS : ∀ X ∈ C, X ∈ Submodule.span ℂ S)
    (hreal : ∀ p ∈ S, p.map conj = p)
    (hconj : ∀ p ∈ S, ∃ q ∈ S, q * p = pᵀ * q ∧ qᵀ * q = 1)
    {Z : Matrix ι ι ℂ} (hZC : Z ∈ C) (hZcen : ∀ X ∈ C, Z * X = X * Z) (hZh : Zᴴ = Z)
    (hZi : Z * Z = Z) (hZ0 : Z ≠ 0)
    (hprim : ∀ Z' ∈ C, (∀ X ∈ C, Z' * X = X * Z') → Z' * Z' = Z' → Z * Z' = 0 ∨ Z * Z' = Z) :
    Z.map conj = Z := by
  classical
  have hbarS : ∀ X ∈ Submodule.span ℂ S, X.map conj ∈ Submodule.span ℂ S := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx => rw [hreal x hx]; exact Submodule.subset_span hx
    | zero => simpa using Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.map_add _ (by simp)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have : (c • x).map conj = (conj c) • x.map conj := by ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  have hspanC : Submodule.span ℂ S ≤ C := Submodule.span_le.2 hSC
  have hbar : ∀ X ∈ C, X.map conj ∈ C := fun X hX => hspanC (hbarS X (hCS X hX))
  set Zb := Z.map conj with hZb
  have hZbC : Zb ∈ C := hbar Z hZC
  have hZbcen : ∀ X ∈ C, Zb * X = X * Zb := by
    intro X hX
    have h := congrArg (fun M => M.map conj) (hZcen (X.map conj) (hbar X hX))
    simp only [map_conj_mul, map_conj_conj] at h
    exact h
  have hZbi : Zb * Zb = Zb := by
    rw [hZb, ← map_conj_mul, hZi]
  have hZT : Zᵀ = Zb := transpose_eq_map_conj_of_hermitian hZh
  have htr' : ∀ X ∈ Submodule.span ℂ S, (Zb * X).trace = (Z * X).trace := by
    intro X hX'
    induction hX' using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨q, hq, hqp, hqq⟩ := hconj p hp
      have hqq' : q * qᵀ = 1 := mul_eq_one_comm.1 hqq
      have hpT : pᵀ = q * p * qᵀ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc q p, hqp, Matrix.mul_assoc, hqq', Matrix.mul_one]
      have hcomm : Zb * q = q * Zb := hZbcen q (hSC hq)
      calc (Zb * p).trace = (qᵀ * (q * Zb * p)).trace := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hqq, Matrix.one_mul]
        _ = (qᵀ * (Zb * q * p)).trace := by rw [hcomm]
        _ = (Zb * q * p * qᵀ).trace := Matrix.trace_mul_comm _ _
        _ = (Zb * pᵀ).trace := by rw [hpT]; simp only [Matrix.mul_assoc]
        _ = (pᵀ * Zb).trace := Matrix.trace_mul_comm _ _
        _ = (pᵀ * Zᵀ).trace := by rw [hZT]
        _ = ((Z * p)ᵀ).trace := by rw [Matrix.transpose_mul]
        _ = (Z * p).trace := Matrix.trace_transpose _
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, hx]
  have htr : ∀ X ∈ C, (Zb * X).trace = (Z * X).trace := fun X hX => htr' X (hCS X hX)
  have h1 : (Zb * Z).trace = Z.trace := by rw [htr Z hZC, hZi]
  have hZtr : Z.trace ≠ 0 := by
    intro h
    apply hZ0
    refine Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 ?_
    rw [hZh, hZi, h]
  have hne : Zb * Z ≠ 0 := fun h => hZtr (by rw [← h1, h, Matrix.trace_zero])
  have hc : Z * Zb = Zb * Z := (hZbcen Z hZC).symm
  have hZZb : Z * Zb = Z := by
    rcases hprim Zb hZbC hZbcen hZbi with h | h
    · exact absurd (hc ▸ h) hne
    · exact h
  have h2 : Zb * Z = Zb := by
    have := congrArg (fun M => M.map conj) hZZb
    have e : Zb.map conj = Z := by rw [hZb, map_conj_conj]
    rw [map_conj_mul, e] at this
    exact this
  rw [← h2, ← hc, hZZb]

end Abstract

/-! ### Sector projectors in isotypic coordinates -/

section Coordinates

open scoped Kronecker
open FormalResearch.FrameFree.Helstrom (qf)

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem blockOp_zero : blockOp A (fun l => (0 : Matrix (B l) (B l) ℂ)) = 0 := by
  unfold blockOp
  ext ⟨l, a, b⟩ ⟨l', a', b'⟩
  by_cases h : l = l'
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- The `l`-th coordinate projector `⊕ δ_{l l'} 1`. -/
noncomputable def sectorDelta (B : Λ → Type*) [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)] (l : Λ) :
    ∀ l', Matrix (B l') (B l') ℂ := fun l' => if l' = l then 1 else 0

/-- `W (⊕ δ_l) Wᴴ`: the isotypic projector of sector `l` in the original coordinates. -/
noncomputable def sectorProj (A : Λ → Type*) [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)]
    (W : Matrix ι (Idx A B) ℂ) (l : Λ) : Matrix ι ι ℂ :=
  W * blockOp A (sectorDelta B l) * Wᴴ

/-- The commutant of `G` as a subspace. -/
def commSub (G : Set (Matrix ι ι ℂ)) : Submodule ℂ (Matrix ι ι ℂ) :=
  (Subalgebra.centralizer ℂ G).toSubmodule

theorem mem_commSub {G : Set (Matrix ι ι ℂ)} {X : Matrix ι ι ℂ} :
    X ∈ commSub G ↔ ∀ g ∈ G, g * X = X * g := by
  unfold commSub
  rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]

theorem sandwich_mul {κ : Type*} [Fintype κ] [DecidableEq κ] {W : Matrix ι κ ℂ} (hW1 : Wᴴ * W = 1)
    (M N : Matrix κ κ ℂ) : (W * M * Wᴴ) * (W * N * Wᴴ) = W * (M * N) * Wᴴ := by
  have : (W * M * Wᴴ) * (W * N * Wᴴ) = W * M * (Wᴴ * W) * N * Wᴴ := by
    simp only [Matrix.mul_assoc]
  rw [this, hW1]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem sandwich_back {κ : Type*} [Fintype κ] [DecidableEq κ] {W : Matrix ι κ ℂ} (hW2 : W * Wᴴ = 1)
    (X : Matrix ι ι ℂ) : W * (Wᴴ * X * W) * Wᴴ = X := by
  have : W * (Wᴴ * X * W) * Wᴴ = (W * Wᴴ) * X * (W * Wᴴ) := by simp only [Matrix.mul_assoc]
  rw [this, hW2]; simp

theorem mem_commSub_iff {G : Set (Matrix ι ι ℂ)} {W : Matrix ι (Idx A B) ℂ} (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (hG : IsotypicInvariants A (transportSet W G)) (X : Matrix ι ι ℂ) :
    X ∈ commSub G ↔ ∃ Y : ∀ l, Matrix (B l) (B l) ℂ, X = W * blockOp A Y * Wᴴ := by
  rw [mem_commSub]
  constructor
  · intro h
    obtain ⟨Y, hY⟩ := (hG (Wᴴ * X * W)).1 (by
      rintro _ ⟨g, hg, rfl⟩
      rw [comm_conj_iff hW1 hW2, sandwich_back hW2]
      exact h g hg)
    exact ⟨Y, by rw [← hY, sandwich_back hW2]⟩
  · rintro ⟨Y, rfl⟩ g hg
    have := (hG _).2 ⟨Y, rfl⟩ _ ⟨g, hg, rfl⟩
    have h2 := (comm_conj_iff hW1 hW2 g (blockOp A Y)).1 this
    exact h2

variable {W : Matrix ι (Idx A B) ℂ}

theorem sectorProj_mem {G : Set (Matrix ι ι ℂ)} (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hG : IsotypicInvariants A (transportSet W G)) (l : Λ) : sectorProj A W l ∈ commSub G :=
  (mem_commSub_iff hW1 hW2 hG _).2 ⟨_, rfl⟩

theorem sectorProj_central {G : Set (Matrix ι ι ℂ)} (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hG : IsotypicInvariants A (transportSet W G)) (l : Λ) {X : Matrix ι ι ℂ} (hX : X ∈ commSub G) :
    sectorProj A W l * X = X * sectorProj A W l := by
  obtain ⟨Y, rfl⟩ := (mem_commSub_iff hW1 hW2 hG X).1 hX
  unfold sectorProj
  rw [sandwich_mul hW1, sandwich_mul hW1, blockOp_mul, blockOp_mul]
  congr 3
  funext l'
  by_cases h : l' = l
  · subst h; simp [sectorDelta]
  · simp [sectorDelta, h]

theorem sectorProj_conjTranspose (l : Λ) : (sectorProj A W l)ᴴ = sectorProj A W l := by
  unfold sectorProj
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    blockOp_conjTranspose, Matrix.mul_assoc]
  congr 3
  funext l'
  by_cases h : l' = l
  · subst h; simp [sectorDelta]
  · simp [sectorDelta, h]

theorem sectorProj_idem (hW1 : Wᴴ * W = 1) (l : Λ) :
    sectorProj A W l * sectorProj A W l = sectorProj A W l := by
  unfold sectorProj
  rw [sandwich_mul hW1, blockOp_mul]
  congr 3
  funext l'
  by_cases h : l' = l
  · subst h; simp [sectorDelta]
  · simp [sectorDelta, h]

theorem sectorProj_ne_zero [∀ l, Nonempty (A l)] (hW1 : Wᴴ * W = 1) (l : Λ) [Nonempty (B l)] :
    sectorProj A W l ≠ 0 := by
  intro h
  have h1 : blockOp A (sectorDelta B l) = 0 := by
    have := congrArg (fun M => Wᴴ * M * W) h
    simp only [sectorProj] at this
    have e : Wᴴ * (W * blockOp A (sectorDelta B l) * Wᴴ) * W = blockOp A (sectorDelta B l) :=
      conj_back hW1 _
    rw [e] at this
    simpa using this
  rw [← blockOp_zero (A := A) (B := B)] at h1
  have := congrFun (blockOp_inj h1) l
  simp only [sectorDelta, if_true] at this
  exact one_ne_zero this

theorem sectorProj_primitive [∀ l, Nonempty (A l)] {G : Set (Matrix ι ι ℂ)} (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (hG : IsotypicInvariants A (transportSet W G)) (l : Λ) [Nonempty (B l)]
    {Z' : Matrix ι ι ℂ} (hZ'C : Z' ∈ commSub G) (hcen : ∀ X ∈ commSub G, Z' * X = X * Z')
    (hidem : Z' * Z' = Z') :
    sectorProj A W l * Z' = 0 ∨ sectorProj A W l * Z' = sectorProj A W l := by
  obtain ⟨Y, rfl⟩ := (mem_commSub_iff hW1 hW2 hG Z').1 hZ'C
  -- `Y l` commutes with everything
  have hcomm : ∀ y : Matrix (B l) (B l) ℂ, Y l * y = y * Y l := by
    intro y
    set Ys : ∀ l', Matrix (B l') (B l') ℂ := Function.update (fun l' => 0) l y with hYs
    have hmem : W * blockOp A Ys * Wᴴ ∈ commSub G := (mem_commSub_iff hW1 hW2 hG _).2 ⟨_, rfl⟩
    have h := hcen _ hmem
    rw [sandwich_mul hW1, sandwich_mul hW1, blockOp_mul, blockOp_mul] at h
    have h2 := conj_inj hW1 (W := W) h
    have h3 := congrFun (blockOp_inj h2) l
    simpa [hYs] using h3
  have hscal : ∃ c : ℂ, Y l = c • (1 : Matrix (B l) (B l) ℂ) := by
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := Y l)
      (fun i j _ => (hcomm _).symm)
    exact ⟨c, by rw [← hc]; ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]⟩
  obtain ⟨c, hc⟩ := hscal
  have hidem' : Y l * Y l = Y l := by
    have h := hidem
    rw [sandwich_mul hW1, blockOp_mul] at h
    have h2 := conj_inj hW1 (W := W) h
    exact congrFun (blockOp_inj h2) l
  have hcc : c = 0 ∨ c = 1 := by
    obtain ⟨b⟩ := ‹Nonempty (B l)›
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at hidem'
    have := congrFun (congrFun hidem' b) b
    have h' : c * c = c := by simpa using this
    have : c * (c - 1) = 0 := by rw [mul_sub, h']; ring
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  unfold sectorProj
  rw [sandwich_mul hW1, blockOp_mul]
  rcases hcc with h0 | h1
  · left
    have : blockOp A (fun l' => sectorDelta B l l' * Y l') = 0 := by
      rw [← blockOp_zero (A := A) (B := B)]
      congr 1; funext l'
      by_cases h : l' = l
      · subst h; simp [sectorDelta, hc, h0]
      · simp [sectorDelta, h]
    rw [this]; simp
  · right
    have : (fun l' => sectorDelta B l l' * Y l') = sectorDelta B l := by
      funext l'
      by_cases h : l' = l
      · subst h; simp [sectorDelta, hc, h1]
      · simp [sectorDelta, h]
    rw [this]


/-- **Sector projectors are real** when the commutant is spanned by real matrices that are conjugate to
their transposes inside the commutant. -/
theorem sectorProj_real [∀ l, Nonempty (A l)] {G : Set (Matrix ι ι ℂ)} (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (hG : IsotypicInvariants A (transportSet W G)) (l : Λ) [Nonempty (B l)]
    (S : Set (Matrix ι ι ℂ)) (hSC : S ⊆ commSub G)
    (hCS : ∀ X ∈ commSub G, X ∈ Submodule.span ℂ S)
    (hreal : ∀ p ∈ S, p.map conj = p)
    (hconj : ∀ p ∈ S, ∃ q ∈ S, q * p = pᵀ * q ∧ qᵀ * q = 1) :
    (sectorProj A W l).map conj = sectorProj A W l :=
  real_of_primitive_central (commSub G) S hSC hCS hreal hconj (sectorProj_mem hW1 hW2 hG l)
    (fun _ hX => sectorProj_central hW1 hW2 hG l hX) (sectorProj_conjTranspose l)
    (sectorProj_idem hW1 l) (sectorProj_ne_zero hW1 l)
    (fun _ hZ' hcen hid => sectorProj_primitive hW1 hW2 hG l hZ' hcen hid)

/-- `Tr τ_l(Wᴴ a) = ⟨a| W (⊕ δ_l) Wᴴ |a⟩`. -/
theorem trace_tau_eq (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (a : ι → ℂ) (l : Λ) :
    (tau (Wᴴ *ᵥ a) l).trace = qf (sectorProj A W l) a a := by
  have h1 := qf_blockOp_self (A := A) (sectorDelta B l) (Wᴴ *ᵥ a)
  rw [Finset.sum_eq_single l] at h1
  · simp only [sectorDelta, if_true, Matrix.one_mul] at h1
    rw [← h1]
    have := qf_conj hW2 (W * blockOp A (sectorDelta B l) * Wᴴ) a a
    rw [conj_back hW1] at this
    rw [this]; rfl
  · intro l' _ hl'
    simp [sectorDelta, hl']
  · simp

/-- Unitary elements of the group do not change the multiplicity blocks. -/
theorem tau_mulVec_of_mem [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) {U : Matrix (Idx A B) (Idx A B) ℂ} (hU : U ∈ G)
    (hU1 : Uᴴ * U = 1) (v : Idx A B → ℂ) (l : Λ) : tau (U *ᵥ v) l = tau v l := by
  have hvv : Matrix.vecMulVec (U *ᵥ v) (star (U *ᵥ v)) =
      U * Matrix.vecMulVec v (star v) * Uᴴ := by
    rw [Matrix.star_mulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rw [← ptrA_vecMulVec, ← ptrA_vecMulVec, hvv]
  refine Matrix.ext_iff_trace_mul_left.2 (fun Y => ?_)
  set Ys : ∀ l', Matrix (B l') (B l') ℂ := Function.update (fun l' => 0) l Y with hYs
  have hcomm : U * blockOp A Ys = blockOp A Ys * U := (hG _).2 ⟨Ys, rfl⟩ U hU
  have key : (blockOp A Ys * (U * Matrix.vecMulVec v (star v) * Uᴴ)).trace =
      (blockOp A Ys * Matrix.vecMulVec v (star v)).trace := by
    have h1 : blockOp A Ys * (U * Matrix.vecMulVec v (star v) * Uᴴ) =
        U * (blockOp A Ys * Matrix.vecMulVec v (star v)) * Uᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hcomm]; simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_cycle, hU1, Matrix.one_mul]
  rw [trace_blockOp_mul, trace_blockOp_mul] at key
  rw [Finset.sum_eq_single l, Finset.sum_eq_single l] at key
  · simpa [hYs] using key
  · intro l' _ hl'; simp [hYs, Function.update_of_ne hl']
  · simp
  · intro l' _ hl'; simp [hYs, Function.update_of_ne hl']
  · simp

end Coordinates

end FormalResearch.QIB
