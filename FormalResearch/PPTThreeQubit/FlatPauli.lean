module

public import FormalResearch.PPTThreeQubit.PartialTranspose

/-!
# Flat three-qubit states: the Pauli identity `σ_y^{(c)} ρ^{T_c} σ_y^{(c)} = J ρ J⁻¹`

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/relaxations_and_scope.tex`,
`sec:ppt3-flat` (the paragraph before `rem:ppt3-flat-profile`): *every flat three-qubit state is
fully PPT with rank profile `(r, r, r, r)`*.

This file is the Pauli-algebra half (the marginal half is `Flat.lean`).  Conventions as in
`Basic.lean`: the basis vector `|abc⟩` has index `4a + 2b + c`.  `pauli3 P Q R` is the operator
`P ⊗ Q ⊗ R`, `σ = (σx, σy, σz)`, `P3 i j k = σ_i ⊗ σ_j ⊗ σ_k` (the 27 three-body products), and a
*flat form* is `flatRho t = I/8 + T`, `T = ∑ t_{ijk} P3 i j k` with **real** coefficients
(`flatRho` is Hermitian; the paper's "combination" is a real one, as `ρ = ρ†` forces).

Covered (all proved, no hypotheses beyond the flat form):
* `pt_conj_A/B/C`: `σ_y^{(c)} ρ^{T_c} σ_y^{(c)} = I/8 - T = (σ_y ⊗ σ_y ⊗ σ_y) conj(ρ) (σ_y ⊗ σ_y ⊗ σ_y)`
  (`conj` = entrywise complex conjugation, i.e. `J ρ J⁻¹` for `J = σ_y^{⊗3} K`);
* `pt_psd_rank_A/B/C`: if `ρ` is PSD then `ρ^{T_c}` is PSD and `rank ρ^{T_c} = rank ρ`.
Not covered here: that flat states (all proper marginals maximally mixed) have the flat form,
and the combined statement; see `Flat.lean`.  The partial transposes are those of
`PartialTranspose.lean`.
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit.Flat

open Matrix
open scoped ComplexOrder

noncomputable section

/-- The bit of qubit `A` (most significant) of the index `4a + 2b + c`. -/
def bA (i : Fin 8) : Fin 2 := ⟨i.val / 4, by omega⟩
/-- The bit of qubit `B` of the index `4a + 2b + c`. -/
def bB (i : Fin 8) : Fin 2 := ⟨i.val / 2 % 2, by omega⟩
/-- The bit of qubit `C` (least significant) of the index `4a + 2b + c`. -/
def bC (i : Fin 8) : Fin 2 := ⟨i.val % 2, by omega⟩
/-- The index `4a + 2b + c` of the basis vector `|abc⟩`. -/
def ix (a b c : Fin 2) : Fin 8 := ⟨4 * a.val + 2 * b.val + c.val, by omega⟩
@[simp] lemma bA_ix (a b c) : bA (ix a b c) = a := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
@[simp] lemma bB_ix (a b c) : bB (ix a b c) = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
@[simp] lemma bC_ix (a b c) : bC (ix a b c) = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
@[simp] lemma ix_bits (i : Fin 8) : ix (bA i) (bB i) (bC i) = i := by
  fin_cases i <;> rfl
/-- A sum over `Fin 8` as a triple sum over the three bits. -/
lemma sum_fin8 {M : Type*} [AddCommMonoid M] (f : Fin 8 → M) :
    ∑ i, f i = ∑ a, ∑ b, ∑ c, f (ix a b c) := by
  let e : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 :=
    { toFun := fun x => ix x.1 x.2.1 x.2.2
      invFun := fun i => (bA i, bB i, bC i)
      left_inv := fun x => by simp
      right_inv := fun i => by simp }
  rw [← Equiv.sum_comp e f, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

/-- One-qubit operators. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ
/-- Three-qubit operators. -/
abbrev M8 := Matrix (Fin 8) (Fin 8) ℂ

/-- Pauli `σ_x`. -/
def σx : M2 := !![0, 1; 1, 0]
/-- Pauli `σ_y`. -/
def σy : M2 := !![0, -Complex.I; Complex.I, 0]
/-- Pauli `σ_z`. -/
def σz : M2 := !![1, 0; 0, -1]
/-- The three Paulis `(σ_x, σ_y, σ_z)`. -/
def σ : Fin 3 → M2 := ![σx, σy, σz]

/-- The tensor product `P ⊗ Q ⊗ R` of one-qubit operators, in the index convention above. -/
def pauli3 (P Q R : M2) : M8 :=
  Matrix.of fun i j => P (bA i) (bA j) * Q (bB i) (bB j) * R (bC i) (bC j)

lemma pauli3_mul (P Q R P' Q' R' : M2) :
    pauli3 P Q R * pauli3 P' Q' R' = pauli3 (P * P') (Q * Q') (R * R') := by
  ext i j
  simp only [mul_apply, pauli3, of_apply]
  rw [sum_fin8]
  simp only [bA_ix, bB_ix, bC_ix, Fin.sum_univ_two]
  ring

lemma pauli3_one : pauli3 1 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli3, bA, bB, bC, Matrix.one_apply]

lemma pauli3_neg_left (P Q R : M2) : pauli3 (-P) Q R = -pauli3 P Q R := by
  ext i j; simp [pauli3]
lemma pauli3_neg_mid (P Q R : M2) : pauli3 P (-Q) R = -pauli3 P Q R := by
  ext i j; simp [pauli3]
lemma pauli3_neg_right (P Q R : M2) : pauli3 P Q (-R) = -pauli3 P Q R := by
  ext i j; simp [pauli3]

lemma ptA_apply (M : M8) (i j : Fin 8) :
    ptA M i j = M (ix (bA j) (bB i) (bC i)) (ix (bA i) (bB j) (bC j)) := by
  fin_cases i <;> fin_cases j <;> rfl
lemma ptB_apply (M : M8) (i j : Fin 8) :
    ptB M i j = M (ix (bA i) (bB j) (bC i)) (ix (bA j) (bB i) (bC j)) := by
  fin_cases i <;> fin_cases j <;> rfl
lemma ptC_apply (M : M8) (i j : Fin 8) :
    ptC M i j = M (ix (bA i) (bB i) (bC j)) (ix (bA j) (bB j) (bC i)) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The partial transposes are `ℂ`-linear (used to push them through the Pauli expansion). -/
def ptLinA : M8 →ₗ[ℂ] M8 where
  toFun := ptA
  map_add' _ _ := by ext; simp [ptA]
  map_smul' _ _ := by ext; simp [ptA]
def ptLinB : M8 →ₗ[ℂ] M8 where
  toFun := ptB
  map_add' _ _ := by ext; simp [ptB]
  map_smul' _ _ := by ext; simp [ptB]
def ptLinC : M8 →ₗ[ℂ] M8 where
  toFun := ptC
  map_add' _ _ := by ext; simp [ptC]
  map_smul' _ _ := by ext; simp [ptC]

lemma ptA_pauli3 (P Q R : M2) : ptA (pauli3 P Q R) = pauli3 Pᵀ Q R := by
  ext i j; simp [ptA_apply, pauli3]
lemma ptB_pauli3 (P Q R : M2) : ptB (pauli3 P Q R) = pauli3 P Qᵀ R := by
  ext i j; simp [ptB_apply, pauli3]
lemma ptC_pauli3 (P Q R : M2) : ptC (pauli3 P Q R) = pauli3 P Q Rᵀ := by
  ext i j; simp [ptC_apply, pauli3]

lemma σy_σy : σy * σy = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σy, Matrix.mul_apply, Fin.sum_univ_two]
lemma σ_transpose (i : Fin 3) : σy * (σ i)ᵀ * σy = -σ i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [σ, σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
lemma σ_conj (i : Fin 3) : σy * (σ i).map (starRingEnd ℂ) * σy = -σ i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [σ, σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]

/-- `σ_y` on qubit `A`. -/
def yA : M8 := pauli3 σy 1 1
/-- `σ_y` on qubit `B`. -/
def yB : M8 := pauli3 1 σy 1
/-- `σ_y` on qubit `C`. -/
def yC : M8 := pauli3 1 1 σy
/-- `σ_y ⊗ σ_y ⊗ σ_y`. -/
def yyy : M8 := pauli3 σy σy σy

/-- The three-body Pauli product `σ_i ⊗ σ_j ⊗ σ_k`. -/
def P3 (i j k : Fin 3) : M8 := pauli3 (σ i) (σ j) (σ k)
/-- `T = ∑ t_{ijk} σ_i ⊗ σ_j ⊗ σ_k`, a real combination of the 27 three-body Pauli products. -/
def flatT (t : Fin 3 → Fin 3 → Fin 3 → ℝ) : M8 := ∑ i, ∑ j, ∑ k, (t i j k : ℂ) • P3 i j k
/-- The flat form `ρ = I/8 + T`. -/
def flatRho (t : Fin 3 → Fin 3 → Fin 3 → ℝ) : M8 := (1 / 8 : ℂ) • (1 : M8) + flatT t

/-- Conjugation `M ↦ U M U` as a linear map. -/
def conjBy (U : M8) : M8 →ₗ[ℂ] M8 where
  toFun M := U * M * U
  map_add' _ _ := by simp [mul_add, add_mul]
  map_smul' _ _ := by simp

lemma lin_comb (L : M8 →ₗ[ℂ] M8) (X Y : Fin 3 → Fin 3 → Fin 3 → M8)
    (t : Fin 3 → Fin 3 → Fin 3 → ℝ) (h1 : L 1 = 1) (h : ∀ i j k, L (X i j k) = -Y i j k) :
    L ((1 / 8 : ℂ) • (1 : M8) + ∑ i, ∑ j, ∑ k, (t i j k : ℂ) • X i j k)
      = (1 / 8 : ℂ) • (1 : M8) - ∑ i, ∑ j, ∑ k, (t i j k : ℂ) • Y i j k := by
  simp [map_add, map_smul, map_sum, h1, h, sub_eq_add_neg, Finset.sum_neg_distrib]

lemma conj_flatRho (t : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (flatRho t).map (starRingEnd ℂ) = (1 / 8 : ℂ) • (1 : M8) +
      ∑ i, ∑ j, ∑ k, (t i j k : ℂ) •
        pauli3 ((σ i).map (starRingEnd ℂ)) ((σ j).map (starRingEnd ℂ)) ((σ k).map (starRingEnd ℂ)) := by
  ext a b
  by_cases h : a = b <;>
    simp [flatRho, flatT, P3, pauli3, Matrix.sum_apply, map_ofNat, h]

lemma yyy_conj (t : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    yyy * (flatRho t).map (starRingEnd ℂ) * yyy = (1 / 8 : ℂ) • (1 : M8) - flatT t := by
  rw [conj_flatRho]
  have := lin_comb (conjBy yyy)
    (fun i j k => pauli3 ((σ i).map (starRingEnd ℂ)) ((σ j).map (starRingEnd ℂ)) ((σ k).map (starRingEnd ℂ)))
    P3 t ?_ ?_
  · exact this
  · simp [conjBy, yyy, ← pauli3_one, pauli3_mul, σy_σy]
  · intro i j k
    simp [conjBy, yyy, P3, pauli3_mul, σ_conj, pauli3_neg_left, pauli3_neg_mid, pauli3_neg_right]

lemma flat_pt_A (t : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    yA * ptA (flatRho t) * yA = (1 / 8 : ℂ) • (1 : M8) - flatT t := by
  have := lin_comb ((conjBy yA).comp ptLinA) P3 P3 t ?_ ?_
  · exact this
  · simp [conjBy, ptLinA, ← pauli3_one, ptA_pauli3, yA, pauli3_mul, σy_σy]
  · intro i j k
    simp [conjBy, ptLinA, yA, P3, ptA_pauli3, pauli3_mul, σ_transpose, pauli3_neg_left]

lemma flat_pt_B (t : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    yB * ptB (flatRho t) * yB = (1 / 8 : ℂ) • (1 : M8) - flatT t := by
  have := lin_comb ((conjBy yB).comp ptLinB) P3 P3 t ?_ ?_
  · exact this
  · simp [conjBy, ptLinB, ← pauli3_one, ptB_pauli3, yB, pauli3_mul, σy_σy]
  · intro i j k
    simp [conjBy, ptLinB, yB, P3, ptB_pauli3, pauli3_mul, σ_transpose, pauli3_neg_mid]

lemma flat_pt_C (t : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    yC * ptC (flatRho t) * yC = (1 / 8 : ℂ) • (1 : M8) - flatT t := by
  have := lin_comb ((conjBy yC).comp ptLinC) P3 P3 t ?_ ?_
  · exact this
  · simp [conjBy, ptLinC, ← pauli3_one, ptC_pauli3, yC, pauli3_mul, σy_σy]
  · intro i j k
    simp [conjBy, ptLinC, yC, P3, ptC_pauli3, pauli3_mul, σ_transpose, pauli3_neg_right]

lemma pauli3_conjTranspose (P Q R : M2) :
    (pauli3 P Q R)ᴴ = pauli3 Pᴴ Qᴴ Rᴴ := by
  ext i j; simp [pauli3, conjTranspose_apply]

lemma σy_herm : σyᴴ = σy := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σy, conjTranspose_apply]

lemma yyy_sq : yyy * yyy = 1 := by simp [yyy, pauli3_mul, σy_σy, pauli3_one]
lemma yyy_herm : yyyᴴ = yyy := by simp [yyy, pauli3_conjTranspose, σy_herm]
lemma yA_sq : yA * yA = 1 := by simp [yA, pauli3_mul, σy_σy, pauli3_one]
lemma yA_herm : yAᴴ = yA := by simp [yA, pauli3_conjTranspose, σy_herm]
lemma yB_sq : yB * yB = 1 := by simp [yB, pauli3_mul, σy_σy, pauli3_one]
lemma yB_herm : yBᴴ = yB := by simp [yB, pauli3_conjTranspose, σy_herm]
lemma yC_sq : yC * yC = 1 := by simp [yC, pauli3_mul, σy_σy, pauli3_one]
lemma yC_herm : yCᴴ = yC := by simp [yC, pauli3_conjTranspose, σy_herm]

lemma pt_psd_rank (y : M8) (hy : y * y = 1) (hyh : yᴴ = y) (p ρ : M8) (hρ : ρ.PosSemidef)
    (h : y * p * y = yyy * ρ.map (starRingEnd ℂ) * yyy) : p.PosSemidef ∧ p.rank = ρ.rank := by
  have hc : ρ.map (starRingEnd ℂ) = ρᵀ := by
    ext a b
    have := hρ.isHermitian.apply b a
    simpa using this
  rw [hc] at h
  have hp : p = (y * yyy) * ρᵀ * (yyy * y) := by
    calc p = (y * y) * p * (y * y) := by simp [hy]
      _ = y * (y * p * y) * y := by simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc]
  have hU : (y * yyy)ᴴ = yyy * y := by simp [conjTranspose_mul, yyy_herm, hyh]
  have hUU : (y * yyy) * (yyy * y) = 1 := by
    calc (y * yyy) * (yyy * y) = y * (yyy * yyy) * y := by simp only [mul_assoc]
      _ = 1 := by rw [yyy_sq, mul_one, hy]
  have hUU' : (yyy * y) * (y * yyy) = 1 := by
    calc (yyy * y) * (y * yyy) = yyy * (y * y) * yyy := by simp only [mul_assoc]
      _ = 1 := by rw [hy, mul_one, yyy_sq]
  constructor
  · rw [hp, ← hU]; exact hρ.transpose.mul_mul_conjTranspose_same _
  · rw [hp, rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_of_right_inverse hUU'),
      rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_right_inverse hUU), rank_transpose]

/-- `sec:ppt3-flat`: `σ_y^{(A)} ρ^{T_A} σ_y^{(A)} = I/8 - T = (σ_y⊗σ_y⊗σ_y) conj(ρ) (σ_y⊗σ_y⊗σ_y)`
for `ρ = I/8 + T` of flat form.  (Proved; source `relaxations_and_scope.tex`.) -/
theorem pt_conj_A (t : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    yA * ptA (flatRho t) * yA = (1 / 8 : ℂ) • (1 : M8) - flatT t ∧
    (1 / 8 : ℂ) • (1 : M8) - flatT t = yyy * (flatRho t).map (starRingEnd ℂ) * yyy :=
  ⟨flat_pt_A t, (yyy_conj t).symm⟩

/-- As `pt_conj_A`, for the partial transpose on qubit `B`. -/
theorem pt_conj_B (t : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    yB * ptB (flatRho t) * yB = (1 / 8 : ℂ) • (1 : M8) - flatT t ∧
    (1 / 8 : ℂ) • (1 : M8) - flatT t = yyy * (flatRho t).map (starRingEnd ℂ) * yyy :=
  ⟨flat_pt_B t, (yyy_conj t).symm⟩

/-- As `pt_conj_A`, for the partial transpose on qubit `C`. -/
theorem pt_conj_C (t : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    yC * ptC (flatRho t) * yC = (1 / 8 : ℂ) • (1 : M8) - flatT t ∧
    (1 / 8 : ℂ) • (1 : M8) - flatT t = yyy * (flatRho t).map (starRingEnd ℂ) * yyy :=
  ⟨flat_pt_C t, (yyy_conj t).symm⟩

/-- `sec:ppt3-flat`: a PSD operator of flat form has PSD partial transpose on `A`, of the same rank.
(Proved.) -/
theorem pt_psd_rank_A (t : Fin 3 → Fin 3 → Fin 3 → ℝ) (hρ : (flatRho t).PosSemidef) :
    (ptA (flatRho t)).PosSemidef ∧ (ptA (flatRho t)).rank = (flatRho t).rank :=
  pt_psd_rank yA yA_sq yA_herm _ _ hρ ((flat_pt_A t).trans (yyy_conj t).symm)

/-- As `pt_psd_rank_A`, for `B`. -/
theorem pt_psd_rank_B (t : Fin 3 → Fin 3 → Fin 3 → ℝ) (hρ : (flatRho t).PosSemidef) :
    (ptB (flatRho t)).PosSemidef ∧ (ptB (flatRho t)).rank = (flatRho t).rank :=
  pt_psd_rank yB yB_sq yB_herm _ _ hρ ((flat_pt_B t).trans (yyy_conj t).symm)

/-- As `pt_psd_rank_A`, for `C`. -/
theorem pt_psd_rank_C (t : Fin 3 → Fin 3 → Fin 3 → ℝ) (hρ : (flatRho t).PosSemidef) :
    (ptC (flatRho t)).PosSemidef ∧ (ptC (flatRho t)).rank = (flatRho t).rank :=
  pt_psd_rank yC yC_sq yC_herm _ _ hρ ((flat_pt_C t).trans (yyy_conj t).symm)

/-- info: 'FormalResearch.PPTThreeQubit.Flat.pt_conj_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pt_conj_A

/-- info: 'FormalResearch.PPTThreeQubit.Flat.pt_conj_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pt_conj_B

/-- info: 'FormalResearch.PPTThreeQubit.Flat.pt_conj_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pt_conj_C

/-- info: 'FormalResearch.PPTThreeQubit.Flat.pt_psd_rank_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pt_psd_rank_A

/-- info: 'FormalResearch.PPTThreeQubit.Flat.pt_psd_rank_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pt_psd_rank_B

/-- info: 'FormalResearch.PPTThreeQubit.Flat.pt_psd_rank_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pt_psd_rank_C

end

end FormalResearch.PPTThreeQubit.Flat
