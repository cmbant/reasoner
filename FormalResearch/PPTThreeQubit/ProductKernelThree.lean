import FormalResearch.PPTThreeQubit.ProductKernel
import FormalResearch.PPTThreeQubit.PartialTranspose
import FormalResearch.PPTThreeQubit.Basic
import FormalResearch.PPTThreeQubit.CutEquiv

/-!
# The three-qubit consequence of the product-kernel lemma

Source: `appendix_moment_cone.tex`, `lem:ppt3-product-kernel`, second sentence: the kernel of a
fully-PPT three-qubit state that is not biseparable contains no nonzero cut-product vector.

Each of the three cuts `A|BC`, `B|AC`, `C|AB` is identified with `ℂ² ⊗ ℂ⁴` by an explicit
reindexing `Fin 8 ≃ Fin 2 × Fin 4` under which `ptA`, `ptB`, `ptC` become `ptFirst`, and then
`ppt_product_kernel` applies.  **Hypothesis:** `PPTSeparable23` (Horodecki–Horodecki–Horodecki 1996).
-/

namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.GurvitsBarnum
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

theorem ptFirst_eqA (M : Matrix (Fin 8) (Fin 8) ℂ) :
    ptFirst (M.submatrix eqA.symm eqA.symm) = (ptA M).submatrix eqA.symm eqA.symm := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> rfl

theorem ptFirst_eqB (M : Matrix (Fin 8) (Fin 8) ℂ) :
    ptFirst (M.submatrix eqB.symm eqB.symm) = (ptB M).submatrix eqB.symm eqB.symm := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> rfl

theorem ptFirst_eqC (M : Matrix (Fin 8) (Fin 8) ℂ) :
    ptFirst (M.submatrix eqC.symm eqC.symm) = (ptC M).submatrix eqC.symm eqC.symm := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> rfl

/-- Generic cut version: reindex by `e : Fin 8 ≃ Fin 2 × Fin 4`, apply `ppt_product_kernel`, and read
the separable decomposition back as a sum of rank-ones of product vectors `a(e i) b(e i)`. -/
theorem decomp_of_cut_kernel (h : PPTSeparable23) (e : Fin 8 ≃ Fin 2 × Fin 4)
    (pt : Matrix (Fin 8) (Fin 8) ℂ → Matrix (Fin 8) (Fin 8) ℂ)
    (hpt : ∀ M, ptFirst (M.submatrix e.symm e.symm) = (pt M).submatrix e.symm e.symm)
    (ρ : Matrix (Fin 8) (Fin 8) ℂ) (hρ : ρ.PosSemidef) (hT : (pt ρ).PosSemidef)
    (x : Fin 8 → ℂ) (α : Fin 2 → ℂ) (μ : Fin 4 → ℂ) (hx : x ≠ 0)
    (hxe : ∀ i, x i = α (e i).1 * μ (e i).2) (hk : ρ *ᵥ x = 0) :
    ∃ (n : ℕ) (a : Fin n → Fin 2 → ℂ) (b : Fin n → Fin 4 → ℂ),
      ρ = ∑ i, vecMulVec (fun j => a i (e j).1 * b i (e j).2)
        (star (fun j => a i (e j).1 * b i (e j).2)) := by
  have hρ2 : (ρ.submatrix e.symm e.symm).PosSemidef := hρ.submatrix _
  have hT2 : (ptFirst (ρ.submatrix e.symm e.symm)).PosSemidef := by
    rw [hpt]; exact hT.submatrix _
  have hα : α ≠ 0 := by
    rintro rfl; apply hx; ext i; simp [hxe]
  have hμ : μ ≠ 0 := by
    rintro rfl; apply hx; ext i; simp [hxe]
  have hk2 : ρ.submatrix e.symm e.symm *ᵥ kroneckerVec α μ = 0 := by
    rw [submatrix_mulVec_equiv]
    have : kroneckerVec α μ ∘ e.symm.symm = x := by
      ext i; simp [hxe, kroneckerVec]
    rw [this, hk]; rfl
  obtain ⟨n, a, b, hab⟩ := ppt_product_kernel h _ hρ2 hT2 α μ hα hμ hk2
  refine ⟨n, a, b, ?_⟩
  ext i j
  have := congrFun (congrFun hab (e i)) (e j)
  simp only [submatrix_apply, Equiv.symm_apply_apply, Matrix.sum_apply, prodRankOne_apply'] at this
  rw [this, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [vecMulVec_apply, Pi.star_apply, star_mul']
  ring

/-- If `ρ` is positive with `ρ^{T_A} ⪰ 0` and its kernel contains a nonzero vector which is a product
across `A|BC`, then `ρ` is biseparable (`lem:ppt3-product-kernel`, cut `A`).
Hypothesis: `PPTSeparable23`. -/
theorem biseparable_of_prodA_kernel (h : PPTSeparable23) (ρ : Matrix (Fin 8) (Fin 8) ℂ)
    (hρ : ρ.PosSemidef) (hT : (ptA ρ).PosSemidef) (x : Fin 8 → ℂ) (hx : x ≠ 0) (hp : IsProdA x)
    (hk : ρ *ᵥ x = 0) : IsBiseparable ρ := by
  obtain ⟨α, μ, hxe⟩ := hp
  obtain ⟨n, a, b, hd⟩ := decomp_of_cut_kernel h eqA ptA ptFirst_eqA ρ hρ hT x α μ hx
    (fun i => hxe i) hk
  exact ⟨n, fun i j => a i (eqA j).1 * b i (eqA j).2,
    fun i => Or.inl ⟨a i, b i, fun j => rfl⟩, hd⟩

/-- Cut `B|AC` of `biseparable_of_prodA_kernel`. -/
theorem biseparable_of_prodB_kernel (h : PPTSeparable23) (ρ : Matrix (Fin 8) (Fin 8) ℂ)
    (hρ : ρ.PosSemidef) (hT : (ptB ρ).PosSemidef) (x : Fin 8 → ℂ) (hx : x ≠ 0) (hp : IsProdB x)
    (hk : ρ *ᵥ x = 0) : IsBiseparable ρ := by
  obtain ⟨α, μ, hxe⟩ := hp
  obtain ⟨n, a, b, hd⟩ := decomp_of_cut_kernel h eqB ptB ptFirst_eqB ρ hρ hT x α μ hx
    (fun i => hxe i) hk
  exact ⟨n, fun i j => a i (eqB j).1 * b i (eqB j).2,
    fun i => Or.inr (Or.inl ⟨a i, b i, fun j => rfl⟩), hd⟩

/-- Cut `C|AB` of `biseparable_of_prodA_kernel`. -/
theorem biseparable_of_prodC_kernel (h : PPTSeparable23) (ρ : Matrix (Fin 8) (Fin 8) ℂ)
    (hρ : ρ.PosSemidef) (hT : (ptC ρ).PosSemidef) (x : Fin 8 → ℂ) (hx : x ≠ 0) (hp : IsProdC x)
    (hk : ρ *ᵥ x = 0) : IsBiseparable ρ := by
  obtain ⟨α, μ, hxe⟩ := hp
  obtain ⟨n, a, b, hd⟩ := decomp_of_cut_kernel h eqC ptC ptFirst_eqC ρ hρ hT x α μ hx
    (fun i => hxe i) hk
  exact ⟨n, fun i j => a i (eqC j).1 * b i (eqC j).2,
    fun i => Or.inr (Or.inr ⟨a i, b i, fun j => rfl⟩), hd⟩

/-- **Second sentence of `lem:ppt3-product-kernel`.**  A fully-PPT three-qubit state which is not
biseparable has no nonzero cut-product vector in its kernel.  Hypothesis: `PPTSeparable23`. -/
theorem kernel_free_of_gme (h : PPTSeparable23) (ρ : Matrix (Fin 8) (Fin 8) ℂ) (hρ : ρ.PosSemidef)
    (hA : (ptA ρ).PosSemidef) (hB : (ptB ρ).PosSemidef) (hC : (ptC ρ).PosSemidef)
    (hg : IsGME ρ) (x : Fin 8 → ℂ) (hx : x ≠ 0) (hk : ρ *ᵥ x = 0) : ¬ IsCutProduct x := by
  rintro (hp | hp | hp)
  · exact hg (biseparable_of_prodA_kernel h ρ hρ hA x hx hp hk)
  · exact hg (biseparable_of_prodB_kernel h ρ hρ hB x hx hp hk)
  · exact hg (biseparable_of_prodC_kernel h ρ hρ hC x hx hp hk)

end
end FormalResearch.PPTThreeQubit

/-- info: 'FormalResearch.PPTThreeQubit.kernel_free_of_gme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.kernel_free_of_gme
