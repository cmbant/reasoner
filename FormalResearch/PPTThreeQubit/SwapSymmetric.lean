module

public import FormalResearch.PPTThreeQubit.ProductKernelThree
public import FormalResearch.PPTThreeQubit.ProductKernel
public import FormalResearch.PPTThreeQubit.CurveParam

/-!
# Swap symmetry and PPT force separability (`cor:ppt3-symmetrisation` (a), (c))

Source: `QI/hidden_entanglement/ppt_three_qubit/family.tex`, `cor:ppt3-symmetrisation`; the
mechanism is that of Novo--Moroder--Gühne.

A PPT operator `ρ` on `ℂ² ⊗ ℂ⁴ = ℂ² ⊗ (ℂ² ⊗ ℂ²)` that is invariant under the swap of the two
qubits of `ℂ⁴` is block diagonal in triplet (`dim 3`) and singlet (`dim 1`); the triplet block is a PPT
operator on `ℂ² ⊗ ℂ³` (separable by `pptSeparable23`, via `sep_of_supported`), the singlet block is
positive on `ℂ² ⊗ ℂ¹`.  Hence:

* `isSeparable_of_swap`: PPT and swap-invariant ⇒ separable (on `ℂ² ⊗ ℂ⁴`);
* `isBiseparable_of_swapBC` (and `swapAC`, `swapAB`): a three-qubit operator that is PSD, PPT at the
  cut of the non-swapped qubit and invariant under the swap of the other two is biseparable (separable
  across that cut), so `no_gme_of_swap_invariant`: **no fully-PPT GME state is invariant under the
  exchange of two qubits** (`cor:ppt3-symmetrisation` (a));
* `isBiseparable_swap_average`: for every `ρ` that is PSD and PPT at `A|BC`, the average
  `(ρ + S_BC ρ S_BC)/2` (which is the pinching with the triplet and singlet projectors of `BC`) is
  `A|BC`-separable (the separability part of `cor:ppt3-symmetrisation` (c)).
* `isBiseparable_permAvg`: for a fully-PPT `ρ`, the permutation average `(1/6) ∑_π U_π ρ U_π†`
  (`permAvg`, over the six qubit permutations) is biseparable (`cor:ppt3-symmetrisation` (b), the
  biseparability of `𝒮(ρ)`).
Not formalised: the trace-distance bounds `eq:ppt3-asymmetry-upper`, `eq:ppt3-pinch` (they need the
trace norm and the biseparable distance), the identification of the swap average with the
`P₃, P₁` pinching, and the statement that `𝒮(ρ)` is separable across each cut separately.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.GurvitsBarnum
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

/-- The swap of the two qubits of `ℂ⁴ = ℂ² ⊗ ℂ²` on basis indices `0 = |00⟩, 1 = |01⟩, 2 = |10⟩,
3 = |11⟩`. -/
def swp : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- `√2 / 2` as a complex number. -/
def rr : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

theorem rr_mul_rr : rr * rr = 1 / 2 := by
  unfold rr
  rw [← Complex.ofReal_mul]
  have : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  rw [this]; norm_num

theorem conj_rr : (starRingEnd ℂ) rr = rr := by
  unfold rr; exact Complex.conj_ofReal _

/-- The real orthogonal change of basis on `ℂ⁴`: columns `|00⟩`, `(|01⟩+|10⟩)/√2`, `|11⟩`
(triplet), `(|01⟩-|10⟩)/√2` (singlet). -/
def Utrip : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, rr, 0, rr; 0, rr, 0, -rr; 0, 0, 1, 0]

theorem Utrip_mul_conjTranspose : Utrip * Utripᴴ = 1 := by
  ext i j
  have := rr_mul_rr
  fin_cases i <;> fin_cases j <;>
    simp [Utrip, mul_apply, Fin.sum_univ_four, conjTranspose_apply, conj_rr, Matrix.one_apply] <;>
    linear_combination (2 : ℂ) * this

theorem conjTranspose_Utrip_mul : Utripᴴ * Utrip = 1 := by
  ext i j
  have := rr_mul_rr
  fin_cases i <;> fin_cases j <;>
    simp [Utrip, mul_apply, Fin.sum_univ_four, conjTranspose_apply, conj_rr, Matrix.one_apply] <;>
    linear_combination (2 : ℂ) * this

section Block

variable (ρ : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ)

/-- The change of basis `ρ ↦ (1 ⊗ U†) ρ (1 ⊗ U)` to the triplet/singlet basis. -/
def rotate : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utripᴴ) * ρ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utripᴴ)ᴴ

theorem rotate_apply (i j : Fin 2) (k l : Fin 4) :
    rotate ρ (i, k) (j, l) = ∑ p, ∑ q, star (Utrip p k) * ρ (i, p) (j, q) * Utrip q l := by
  simp [rotate, mul_apply, kronecker_apply, conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.sum_mul, Finset.mul_sum]
  fin_cases j <;> simp <;> exact Finset.sum_comm

/-- Swap invariance kills the triplet-singlet coherences `ρ'_{(i,k),(j,3)}`, `k ≠ 3`. -/
theorem rotate_cross (hs : ∀ i j k l, ρ (i, swp k) (j, swp l) = ρ (i, k) (j, l)) (i j : Fin 2)
    (k : Fin 4) (hk : k ≠ 3) : rotate ρ (i, k) (j, 3) = 0 := by
  have h01 : ρ (i, 0) (j, 2) = ρ (i, 0) (j, 1) := by simpa [swp] using hs i j 0 1
  have h11 : ρ (i, 2) (j, 2) = ρ (i, 1) (j, 1) := by simpa [swp] using hs i j 1 1
  have h12 : ρ (i, 2) (j, 1) = ρ (i, 1) (j, 2) := by simpa [swp] using hs i j 1 2
  have h31 : ρ (i, 3) (j, 2) = ρ (i, 3) (j, 1) := by simpa [swp] using hs i j 3 1
  have hr := rr_mul_rr
  rw [rotate_apply]
  fin_cases k
  · simp [Fin.sum_univ_four, Utrip]
    first | linear_combination rr * h01 | linear_combination (-rr) * h01
  · simp [Fin.sum_univ_four, Utrip, conj_rr]
    linear_combination (rr * rr) * h12 - (rr * rr) * h11
  · simp [Fin.sum_univ_four, Utrip]
    first | linear_combination rr * h31 | linear_combination (-rr) * h31
  · exact absurd rfl hk

theorem rotate_posSemidef (hρ : ρ.PosSemidef) : (rotate ρ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same _

theorem rotate_ptFirst (hT : (ptFirst ρ).PosSemidef) : (ptFirst (rotate ρ)).PosSemidef := by
  unfold rotate
  rw [ptFirst_congr]
  exact hT.mul_mul_conjTranspose_same _

theorem rotate_back : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utrip) * rotate ρ *
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utrip)ᴴ = ρ := by
  have h : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utrip) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utripᴴ) =
      1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, Utrip_mul_conjTranspose, one_kronecker_one]
  have h' : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utripᴴ)ᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utrip := by
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_conjTranspose]
  rw [rotate, h', conjTranspose_kronecker, conjTranspose_one]
  calc ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utrip) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utripᴴ * ρ *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utrip) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utripᴴ)
      = (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utrip) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utripᴴ)) * ρ *
        (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utrip) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Utripᴴ)) := by
        simp only [Matrix.mul_assoc]
    _ = ρ := by rw [h, Matrix.one_mul, Matrix.mul_one]

/-- **PPT and swap-invariant on `ℂ² ⊗ ℂ⁴` implies separable** (`cor:ppt3-symmetrisation` (a),
the mechanism of Novo--Moroder--Gühne): the operator is block diagonal in triplet and singlet, the
triplet block is a PPT operator on `ℂ² ⊗ ℂ³` (separable by `pptSeparable23`) and the singlet block
is a positive operator on `ℂ² ⊗ ℂ¹`. -/
theorem isSeparable_of_swap (hρ : ρ.PosSemidef) (hT : (ptFirst ρ).PosSemidef)
    (hs : ∀ i j k l, ρ (i, swp k) (j, swp l) = ρ (i, k) (j, l)) : IsSeparable ρ := by
  classical
  set ρ' := rotate ρ with hρ'def
  have hρ' : ρ'.PosSemidef := rotate_posSemidef ρ hρ
  have hT' : (ptFirst ρ').PosSemidef := rotate_ptFirst ρ hT
  have hc1 : ∀ i j k, k ≠ 3 → ρ' (i, k) (j, 3) = 0 := fun i j k hk => rotate_cross ρ hs i j k hk
  have hc2 : ∀ i j k, k ≠ 3 → ρ' (i, 3) (j, k) = 0 := fun i j k hk => by
    have := hρ'.isHermitian.apply (i, 3) (j, k)
    rw [← this, hc1 j i k hk, star_zero]
  -- the triplet block
  set d : Fin 2 × Fin 4 → ℂ := fun p => if p.2 = 3 then 0 else 1 with hd
  set Dm : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ := diagonal d with hDm
  have hDh : Dmᴴ = Dm := by
    ext p q
    simp only [hDm, conjTranspose_apply, diagonal_apply]
    by_cases hpq : p = q
    · subst hpq; simp only [hd]; split_ifs <;> simp
    · simp [hpq, Ne.symm hpq]
  set S3 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ := Dm * ρ' * Dmᴴ with hS3
  have hS3e : ∀ p q, S3 p q = if p.2 = 3 ∨ q.2 = 3 then 0 else ρ' p q := by
    intro p q
    rw [hS3, hDh]
    simp only [hDm, mul_diagonal, diagonal_mul, hd]
    split_ifs <;> simp_all
  have hS3psd : S3.PosSemidef := hρ'.mul_mul_conjTranspose_same Dm
  have hS3pt : (ptFirst S3).PosSemidef := by
    have : ptFirst S3 = Dm * ptFirst ρ' * Dmᴴ := by
      ext ⟨i, k⟩ ⟨j, l⟩
      rw [ptFirst_apply, hS3e, hDh]
      simp only [hDm, mul_diagonal, diagonal_mul, ptFirst_apply, hd]
      split_ifs <;> simp_all
    rw [this]
    exact hT'.mul_mul_conjTranspose_same Dm
  have hS3z : ∀ j : Fin 2, S3 *ᵥ Pi.single (j, (3 : Fin 4)) 1 = 0 := by
    intro j
    ext p
    rw [mulVec_single_apply, hS3e]
    simp
  have hS3sep : IsSeparable S3 := sep_of_supported S3 hS3psd hS3pt hS3z
  -- the singlet block
  have hS1 : IsSeparable (ρ' - S3) := by
    have hM : (ρ'.submatrix (fun i : Fin 2 => (i, (3 : Fin 4))) (fun i : Fin 2 => (i, (3 : Fin 4)))).PosSemidef :=
      hρ'.submatrix _
    obtain ⟨m, v, hMv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
    refine ⟨m, v, fun _ => Pi.single 3 1, ?_⟩
    ext ⟨i, k⟩ ⟨j, l⟩
    rw [Matrix.sub_apply, hS3e, Matrix.sum_apply]
    have hMij := congrFun (congrFun hMv i) j
    simp only [submatrix_apply, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply] at hMij
    simp only [prodRankOne_apply]
    by_cases hk : k = 3 <;> by_cases hl : l = 3
    · subst hk; subst hl
      simp [hMij]
    · simp [hk, hl, hc2 i j l hl]
    · simp [hk, hl, hc1 i j k hk]
    · simp [hk, hl]
  have hρ'sep : IsSeparable ρ' := by
    have := hS3sep.add hS1
    rwa [add_sub_cancel] at this
  have := isSeparable_congr (1 : Matrix (Fin 2) (Fin 2) ℂ) Utrip hρ'sep
  rwa [hρ'def, rotate_back] at this

end Block

/-! ### Three qubits -/

/-- Swap of qubits `B` and `C` on indices `4a + 2b + c`. -/
def swapBC (i : Fin 8) : Fin 8 := ⟨4 * (i.val / 4) + 2 * (i.val % 2) + i.val / 2 % 2, by omega⟩

/-- Swap of qubits `A` and `C`. -/
def swapAC (i : Fin 8) : Fin 8 := ⟨4 * (i.val % 2) + 2 * (i.val / 2 % 2) + i.val / 4, by omega⟩

/-- Swap of qubits `A` and `B`. -/
def swapAB (i : Fin 8) : Fin 8 := ⟨4 * (i.val / 2 % 2) + 2 * (i.val / 4) + i.val % 2, by omega⟩

theorem swapBC_swapBC (i : Fin 8) : swapBC (swapBC i) = i := by fin_cases i <;> rfl

theorem eqA_symm_swp (i : Fin 2) (k : Fin 4) :
    eqA.symm (i, swp k) = swapBC (eqA.symm (i, k)) := by
  fin_cases i <;> fin_cases k <;> rfl

theorem eqB_symm_swp (i : Fin 2) (k : Fin 4) :
    eqB.symm (i, swp k) = swapAC (eqB.symm (i, k)) := by
  fin_cases i <;> fin_cases k <;> rfl

theorem eqC_symm_swp (i : Fin 2) (k : Fin 4) :
    eqC.symm (i, swp k) = swapAB (eqC.symm (i, k)) := by
  fin_cases i <;> fin_cases k <;> rfl

/-- A three-qubit operator that is separable across one cut (in the `ℂ² ⊗ ℂ⁴` reindexing of that cut) is
biseparable. -/
theorem isBiseparable_of_cut_separable (c : Fin 3) {ρ : Matrix (Fin 8) (Fin 8) ℂ}
    (h : IsSeparable (ρ.submatrix (cutEquiv c).symm (cutEquiv c).symm)) : IsBiseparable ρ := by
  obtain ⟨n, a, b, hab⟩ := h
  refine ⟨n, fun i j => a i ((cutEquiv c) j).1 * b i ((cutEquiv c) j).2, fun i => ?_, ?_⟩
  · rw [isCutProduct_iff]
    exact ⟨c, (isCutProdAt_iff c _).2 ⟨a i, b i, fun j => rfl⟩⟩
  · ext i j
    have := congrFun (congrFun hab ((cutEquiv c) i)) ((cutEquiv c) j)
    simp only [submatrix_apply, Equiv.symm_apply_apply, Matrix.sum_apply, prodRankOne_apply'] at this
    rw [this, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [vecMulVec_apply, Pi.star_apply, star_mul']
    ring

/-- **`cor:ppt3-symmetrisation` (a), cut `A|BC`.**  A three-qubit operator that is positive, PPT at
`A|BC` and invariant under the swap of `B` and `C` is separable across `A|BC` (hence biseparable). -/
theorem isBiseparable_of_swapBC {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hT : (ptA ρ).PosSemidef) (hs : ∀ i j, ρ (swapBC i) (swapBC j) = ρ i j) : IsBiseparable ρ := by
  refine isBiseparable_of_cut_separable 0 (isSeparable_of_swap _ (hρ.submatrix _) ?_ ?_)
  · show (ptFirst (ρ.submatrix eqA.symm eqA.symm)).PosSemidef
    rw [ptFirst_eqA]; exact hT.submatrix _
  · intro i j k l
    show ρ (eqA.symm (i, swp k)) (eqA.symm (j, swp l)) = ρ (eqA.symm (i, k)) (eqA.symm (j, l))
    rw [eqA_symm_swp, eqA_symm_swp]; exact hs _ _

/-- Cut `B|AC` and the swap of `A` and `C`. -/
theorem isBiseparable_of_swapAC {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hT : (ptB ρ).PosSemidef) (hs : ∀ i j, ρ (swapAC i) (swapAC j) = ρ i j) : IsBiseparable ρ := by
  refine isBiseparable_of_cut_separable 1 (isSeparable_of_swap _ (hρ.submatrix _) ?_ ?_)
  · show (ptFirst (ρ.submatrix eqB.symm eqB.symm)).PosSemidef
    rw [ptFirst_eqB]; exact hT.submatrix _
  · intro i j k l
    show ρ (eqB.symm (i, swp k)) (eqB.symm (j, swp l)) = ρ (eqB.symm (i, k)) (eqB.symm (j, l))
    rw [eqB_symm_swp, eqB_symm_swp]; exact hs _ _

/-- Cut `C|AB` and the swap of `A` and `B`. -/
theorem isBiseparable_of_swapAB {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hT : (ptC ρ).PosSemidef) (hs : ∀ i j, ρ (swapAB i) (swapAB j) = ρ i j) : IsBiseparable ρ := by
  refine isBiseparable_of_cut_separable 2 (isSeparable_of_swap _ (hρ.submatrix _) ?_ ?_)
  · show (ptFirst (ρ.submatrix eqC.symm eqC.symm)).PosSemidef
    rw [ptFirst_eqC]; exact hT.submatrix _
  · intro i j k l
    show ρ (eqC.symm (i, swp k)) (eqC.symm (j, swp l)) = ρ (eqC.symm (i, k)) (eqC.symm (j, l))
    rw [eqC_symm_swp, eqC_symm_swp]; exact hs _ _

/-- **`cor:ppt3-symmetrisation` (a).**  No fully-PPT GME state is invariant under the exchange of two
qubits: a fully-PPT three-qubit operator invariant under one of the three transpositions is
biseparable. -/
theorem no_gme_of_swap_invariant {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hA : (ptA ρ).PosSemidef) (hB : (ptB ρ).PosSemidef) (hC : (ptC ρ).PosSemidef)
    (hs : (∀ i j, ρ (swapBC i) (swapBC j) = ρ i j) ∨ (∀ i j, ρ (swapAC i) (swapAC j) = ρ i j) ∨
      (∀ i j, ρ (swapAB i) (swapAB j) = ρ i j)) : ¬ IsGME ρ := by
  intro hg
  rcases hs with h | h | h
  · exact hg (isBiseparable_of_swapBC hρ hA h)
  · exact hg (isBiseparable_of_swapAC hρ hB h)
  · exact hg (isBiseparable_of_swapAB hρ hC h)

theorem ptA_submatrix_swapBC (M : Matrix (Fin 8) (Fin 8) ℂ) :
    ptA (M.submatrix swapBC swapBC) = (ptA M).submatrix swapBC swapBC := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem ptA_add (M N : Matrix (Fin 8) (Fin 8) ℂ) : ptA (M + N) = ptA M + ptA N := by
  ext i j; rfl

theorem ptA_smul (r : ℝ) (M : Matrix (Fin 8) (Fin 8) ℂ) : ptA (r • M) = r • ptA M := by
  ext i j; rfl

/-- **`cor:ppt3-symmetrisation` (c), separability part.**  For every operator `ρ ≥ 0` that is PPT at
`A|BC`, the swap average `(ρ + S_BC ρ S_BC)/2` (the pinching of `ρ` with the triplet and singlet
projectors of `BC`) is separable across `A|BC`, hence biseparable. -/
theorem isBiseparable_swap_average {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hT : (ptA ρ).PosSemidef) :
    IsBiseparable ((1 / 2 : ℝ) • (ρ + ρ.submatrix swapBC swapBC)) := by
  have hpsd : ((1 / 2 : ℝ) • (ρ + ρ.submatrix swapBC swapBC)).PosSemidef :=
    (hρ.add (hρ.submatrix _)).smul (by norm_num)
  refine isBiseparable_of_swapBC hpsd ?_ ?_
  · rw [ptA_smul, ptA_add, ptA_submatrix_swapBC]
    exact (hT.add (hT.submatrix _)).smul (by norm_num)
  · intro i j
    simp only [Matrix.smul_apply, Matrix.add_apply, submatrix_apply, swapBC_swapBC]
    rw [add_comm]


/-! ### The permutation average (`cor:ppt3-symmetrisation` (b)) -/

theorem ptA_submatrix_swapAC (M : Matrix (Fin 8) (Fin 8) ℂ) :
    ptA (M.submatrix swapAC swapAC) = (ptC M).submatrix swapAC swapAC := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem ptA_submatrix_swapAB (M : Matrix (Fin 8) (Fin 8) ℂ) :
    ptA (M.submatrix swapAB swapAB) = (ptB M).submatrix swapAB swapAB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The permutation average `(1/6) ∑_{π ∈ S₃} U_π ρ U_π†` of a three-qubit operator (the six
permutations of the qubits: identity, the two cyclic shifts and the three transpositions). -/
def permAvg (ρ : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  (1 / 6 : ℝ) • (ρ + ρ.submatrix cycShift cycShift +
    ρ.submatrix (cycShift ∘ cycShift) (cycShift ∘ cycShift) +
    ρ.submatrix swapBC swapBC + ρ.submatrix swapAC swapAC + ρ.submatrix swapAB swapAB)

theorem permAvg_swapBC_invariant (ρ : Matrix (Fin 8) (Fin 8) ℂ) (i j : Fin 8) :
    permAvg ρ (swapBC i) (swapBC j) = permAvg ρ i j := by
  fin_cases i <;> fin_cases j <;>
    simp [permAvg, swapBC, swapAC, swapAB, cycShift, Function.comp] <;> ring

theorem permAvg_posSemidef {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef) :
    (permAvg ρ).PosSemidef := by
  unfold permAvg
  refine PosSemidef.smul ?_ (by norm_num)
  exact ((((hρ.add (hρ.submatrix _)).add (hρ.submatrix _)).add (hρ.submatrix _)).add
    (hρ.submatrix _)).add (hρ.submatrix _)

theorem permAvg_ptA {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hA : (ptA ρ).PosSemidef)
    (hB : (ptB ρ).PosSemidef) (hC : (ptC ρ).PosSemidef) : (ptA (permAvg ρ)).PosSemidef := by
  unfold permAvg
  rw [ptA_smul, ptA_add, ptA_add, ptA_add, ptA_add, ptA_add, ptA_submatrix_shift,
    ptA_submatrix_shift_shift, ptA_submatrix_swapBC, ptA_submatrix_swapAC, ptA_submatrix_swapAB]
  refine PosSemidef.smul ?_ (by norm_num)
  exact ((((hA.add (hC.submatrix _)).add (hB.submatrix _)).add (hA.submatrix _)).add
    (hC.submatrix _)).add (hB.submatrix _)

/-- **`cor:ppt3-symmetrisation` (b), biseparability.**  For every fully-PPT three-qubit operator
`ρ`, the permutation average `(1/6) ∑_π U_π ρ U_π†` is biseparable (it is fully PPT and invariant
under every transposition, so `isBiseparable_of_swapBC` applies).  Not formalised: the distance
bound `eq:ppt3-asymmetry-upper`. -/
theorem isBiseparable_permAvg {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hA : (ptA ρ).PosSemidef) (hB : (ptB ρ).PosSemidef) (hC : (ptC ρ).PosSemidef) :
    IsBiseparable (permAvg ρ) :=
  isBiseparable_of_swapBC (permAvg_posSemidef hρ) (permAvg_ptA hA hB hC)
    (permAvg_swapBC_invariant ρ)

end

/-- info: 'FormalResearch.PPTThreeQubit.isSeparable_of_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.isSeparable_of_swap

/-- info: 'FormalResearch.PPTThreeQubit.no_gme_of_swap_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.no_gme_of_swap_invariant

/-- info: 'FormalResearch.PPTThreeQubit.isBiseparable_permAvg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.isBiseparable_permAvg

/-- info: 'FormalResearch.PPTThreeQubit.isBiseparable_swap_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.isBiseparable_swap_average

end FormalResearch.PPTThreeQubit
