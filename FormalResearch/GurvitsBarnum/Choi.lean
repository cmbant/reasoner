import Mathlib

/-!
# Gurvits–Barnum separable ball: Choi map of a witness and `id ⊗ φ`

Source: L. Gurvits and H. Barnum, *Largest separable balls around the maximally mixed bipartite
quantum state*, Phys. Rev. A 66, 062311 (2002); plan lemma L5 (module M6).

* `matBlock Y i j` is the `κ × κ` block `Y (i, ·) (j, ·)` of a matrix on `ι × κ`;
* `idTensor φ` is `id ⊗ φ`, defined blockwise: `(id ⊗ φ) Y (i, i') (j, j') = φ (matBlock Y i j) i' j'`;
* `choiMap W` is `φ_W (B) = (tr₂ [W (1 ⊗ B)])ᵀ`, i.e.
  `φ_W B i j = ∑ k l, W (j, k) (i, l) * B l k`.

Main results: a Hermitian block-positive `W` gives a positive map `choiMap W`
(`choiMap_posSemidef`), and `⟨ω, (id ⊗ φ_W)(Y) ω⟩ = tr (W Y)` for the unnormalised maximally
entangled vector `ω` (`star_omega_idTensor_choiMap`); `choiMap W 1` is the transposed partial trace
(`choiMap_one_apply`).

Block positivity is used in the vector form `0 ≤ Re (v† W v)` for product vectors
`v = fun p => a p.1 * b p.2`, which is definitionally `FormalResearch.GurvitsBarnum.IsBlockPositive`.
-/

set_option linter.unusedSectionVars false

namespace FormalResearch.GurvitsBarnum

open Matrix Kronecker ComplexOrder

noncomputable section

variable {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-! ### Blocks and `id ⊗ φ` -/

/-- The `κ × κ` block `Y (i, ·) (j, ·)` of a matrix on `ι × κ`. -/
def matBlock (Y : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) : Matrix κ κ ℂ :=
  Matrix.of fun k l => Y (i, k) (j, l)

@[simp] theorem matBlock_apply (Y : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) (k l : κ) :
    matBlock Y i j k l = Y (i, k) (j, l) := rfl

@[simp] theorem matBlock_add (Y Z : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) :
    matBlock (Y + Z) i j = matBlock Y i j + matBlock Z i j := by ext; simp

@[simp] theorem matBlock_smul (c : ℂ) (Y : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) :
    matBlock (c • Y) i j = c • matBlock Y i j := by ext; simp

@[simp] theorem matBlock_zero (i j : ι) :
    matBlock (0 : Matrix (ι × κ) (ι × κ) ℂ) i j = 0 := by ext; simp

theorem matBlock_one (i j : ι) :
    matBlock (1 : Matrix (ι × κ) (ι × κ) ℂ) i j = if i = j then 1 else 0 := by
  ext k l
  by_cases h : i = j <;> simp [Matrix.one_apply, h, Matrix.one_apply]

/-- `id ⊗ φ` on `Matrix (ι × κ) (ι × κ) ℂ`, defined blockwise:
`(idTensor φ Y) (i, i') (j, j') = φ (matBlock Y i j) i' j'`. -/
def idTensor (φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix μ μ ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix (ι × μ) (ι × μ) ℂ where
  toFun Y := Matrix.of fun p q => φ (matBlock Y p.1 q.1) p.2 q.2
  map_add' Y Z := by ext ⟨i, i'⟩ ⟨j, j'⟩; simp
  map_smul' c Y := by ext ⟨i, i'⟩ ⟨j, j'⟩; simp

@[simp] theorem idTensor_apply (φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix μ μ ℂ)
    (Y : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) (i' j' : μ) :
    idTensor φ Y (i, i') (j, j') = φ (matBlock Y i j) i' j' := rfl

/-- `(id ⊗ φ)(1) = 1 ⊗ φ(1)` (blockwise `φ 0 = 0` off the diagonal; Gurvits–Barnum, PRA 66, 062311). -/
theorem idTensor_one (φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix μ μ ℂ) :
    idTensor φ (1 : Matrix (ι × κ) (ι × κ) ℂ) = (1 : Matrix ι ι ℂ) ⊗ₖ φ 1 := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  by_cases h : i = j
  · subst h; simp [matBlock_one]
  · simp [matBlock_one, h]

/-- For a unital `φ`, `(id ⊗ φ)(1) = 1`. -/
theorem idTensor_one_of_unital {φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix μ μ ℂ} (h : φ 1 = 1) :
    idTensor φ (1 : Matrix (ι × κ) (ι × κ) ℂ) = 1 := by
  rw [idTensor_one, h, Matrix.one_kronecker_one]

/-! ### The Choi map of a witness -/

variable (W : Matrix (ι × κ) (ι × κ) ℂ)

/-- The map `φ_W (B) = (tr₂ [W (1 ⊗ B)])ᵀ`, with entries
`φ_W B i j = ∑ k l, W (j, k) (i, l) * B l k`. -/
def choiMap : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun B := Matrix.of fun i j => ∑ k, ∑ l, W (j, k) (i, l) * B l k
  map_add' B C := by
    ext i j
    simp only [of_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c B := by
    ext i j
    simp only [of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem choiMap_apply (B : Matrix κ κ ℂ) (i j : ι) :
    choiMap W B i j = ∑ k, ∑ l, W (j, k) (i, l) * B l k := rfl

/-- The partial trace over the second factor, `(tr₂ W) i j = ∑ k, W (i, k) (j, k)`. -/
def partialTraceSnd : Matrix ι ι ℂ := Matrix.of fun i j => ∑ k, W (i, k) (j, k)

/-- `φ_W (1) = (tr₂ W)ᵀ`. -/
theorem choiMap_one (W : Matrix (ι × κ) (ι × κ) ℂ) :
    choiMap W 1 = (partialTraceSnd W)ᵀ := by
  ext i j
  simp [choiMap_apply, partialTraceSnd, Matrix.one_apply]

theorem choiMap_one_apply (W : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) :
    choiMap W 1 i j = ∑ k, W (j, k) (i, k) := by
  simp [choiMap_apply, Matrix.one_apply]

/-- **L5(c).** (Gurvits–Barnum, PRA 66, 062311, plan lemma L5(c).) Adding `ε • 1` to `W` adds `(ε * card κ) • 1` to `φ_W (1)`. -/
theorem choiMap_one_add_smul_one (W : Matrix (ι × κ) (ι × κ) ℂ) (ε : ℂ) :
    choiMap (W + ε • (1 : Matrix (ι × κ) (ι × κ) ℂ)) 1
      = choiMap W 1 + (ε * (Fintype.card κ : ℂ)) • (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [choiMap_one_apply, Finset.sum_add_distrib, mul_comm]
  · simp [choiMap_one_apply, h, Ne.symm h]

/-- Linearity of `W ↦ φ_W`: the trace-form of the transposed partial trace. -/
theorem choiMap_add (W V : Matrix (ι × κ) (ι × κ) ℂ) (B : Matrix κ κ ℂ) :
    choiMap (W + V) B = choiMap W B + choiMap V B := by
  ext i j
  simp [choiMap_apply, add_mul, Finset.sum_add_distrib]

theorem choiMap_isHermitian {W : Matrix (ι × κ) (ι × κ) ℂ} (hW : W.IsHermitian)
    {B : Matrix κ κ ℂ} (hB : B.IsHermitian) : (choiMap W B).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, choiMap_apply, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hW.apply, hB.apply]

/-- Quadratic form of `φ_W` on a rank-one input: the product-vector form of `W`. -/
theorem star_dotProduct_choiMap_vecMulVec (a : ι → ℂ) (c : κ → ℂ) :
    star a ⬝ᵥ (choiMap W (vecMulVec c (star c)) *ᵥ a)
      = star (fun p : ι × κ => star (a p.1) * c p.2) ⬝ᵥ
          (W *ᵥ fun p : ι × κ => star (a p.1) * c p.2) := by
  simp only [dotProduct, mulVec, choiMap_apply, vecMulVec_apply, Pi.star_apply,
    Fintype.sum_prod_type, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **L5(a).** For a Hermitian block-positive `W`, the map `φ_W` is positive.
(Gurvits–Barnum, PRA 66, 062311; plan lemma L5(a).) -/
theorem choiMap_posSemidef {W : Matrix (ι × κ) (ι × κ) ℂ} (hWh : W.IsHermitian)
    (hW : ∀ (a : ι → ℂ) (b : κ → ℂ),
      0 ≤ (star (fun p : ι × κ => a p.1 * b p.2) ⬝ᵥ (W *ᵥ fun p : ι × κ => a p.1 * b p.2)).re)
    {B : Matrix κ κ ℂ} (hB : B.PosSemidef) : (choiMap W B).PosSemidef := by
  have hH := choiMap_isHermitian hWh hB.isHermitian
  refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun a => ?_
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB
  simp only [map_sum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_nonneg fun t _ => ?_
  rw [star_dotProduct_choiMap_vecMulVec, Complex.nonneg_iff]
  exact ⟨hW (star a) (v t), (hWh.im_star_dotProduct_mulVec_self _).symm⟩

/-- The unnormalised maximally entangled vector `ω = ∑ i, eᵢ ⊗ eᵢ` on `ι × ι`. -/
def omega (ι : Type*) [DecidableEq ι] : ι × ι → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- **L5(b).** `⟨ω, (id ⊗ φ_W)(Y) ω⟩ = tr (W Y)`.
(Gurvits–Barnum, PRA 66, 062311; plan lemma L5(b).) -/
theorem star_omega_idTensor_choiMap (Y : Matrix (ι × κ) (ι × κ) ℂ) :
    star (omega ι) ⬝ᵥ (idTensor (choiMap W) Y *ᵥ omega ι) = trace (W * Y) := by
  simp only [dotProduct, mulVec, omega, Fintype.sum_prod_type, idTensor_apply, Pi.star_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, apply_ite (star : ℂ → ℂ),
    star_one, star_zero, ite_mul, one_mul, zero_mul]
  simp only [trace, diag, mul_apply, Fintype.sum_prod_type, choiMap_apply, matBlock_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

end

end FormalResearch.GurvitsBarnum

/-- info: 'FormalResearch.GurvitsBarnum.idTensor_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.idTensor_one

/-- info: 'FormalResearch.GurvitsBarnum.choiMap_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.choiMap_posSemidef

/-- info: 'FormalResearch.GurvitsBarnum.star_omega_idTensor_choiMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.star_omega_idTensor_choiMap

/-- info: 'FormalResearch.GurvitsBarnum.choiMap_one_add_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.choiMap_one_add_smul_one

