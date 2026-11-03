import FormalResearch.GurvitsBarnum.ContractionBase

/-!
# Gurvits–Barnum: unitary diagonalisation and L2 for unitaries

Source: L. Gurvits and H. Barnum, PRA 66, 062311 (2002); plan lemma L2.

* `cdiag W a = W diag(a) Wᴴ`, with its calculus for unitary `W`.
* `exists_cdiag_of_isHermitian`: the spectral theorem in the form `A = W diag(d) Wᴴ`.
* `exists_cdiag_of_unitary`: a unitary matrix is unitarily diagonalisable with unimodular
  eigenvalues (Cayley transform `H = i (z₀ + U)(z₀ - U)⁻¹`, `z₀` off the spectrum).
* `bdd_map_unitary` (L2): a unital positive map sends a unitary to a contraction.
-/

namespace FormalResearch.GurvitsBarnum
namespace Contr

open Matrix ComplexOrder
open scoped MatrixOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `W diag(a) Wᴴ`. -/
def cdiag (W : Matrix m m ℂ) (a : m → ℂ) : Matrix m m ℂ := W * diagonal a * Wᴴ

theorem cdiag_add (W : Matrix m m ℂ) (a b : m → ℂ) :
    cdiag W a + cdiag W b = cdiag W (a + b) := by
  rw [cdiag, cdiag, cdiag, ← Matrix.add_mul, ← Matrix.mul_add]
  exact congrArg (fun D => W * D * Wᴴ) (diagonal_add a b)

theorem cdiag_sub (W : Matrix m m ℂ) (a b : m → ℂ) :
    cdiag W a - cdiag W b = cdiag W (a - b) := by
  rw [cdiag, cdiag, cdiag, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact congrArg (fun D => W * D * Wᴴ) (diagonal_sub a b)

theorem cdiag_smul (W : Matrix m m ℂ) (c : ℂ) (a : m → ℂ) :
    c • cdiag W a = cdiag W (c • a) := by
  simp [cdiag, diagonal_smul]

theorem cdiag_conjTranspose (W : Matrix m m ℂ) (a : m → ℂ) :
    (cdiag W a)ᴴ = cdiag W (star a) := by
  simp [cdiag, conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc]

section
variable {W : Matrix m m ℂ} (hW : Wᴴ * W = 1)
include hW

theorem cdiag_mul (a b : m → ℂ) : cdiag W a * cdiag W b = cdiag W (a * b) := by
  have : cdiag W a * cdiag W b = W * (diagonal a * (Wᴴ * W) * diagonal b) * Wᴴ := by
    simp only [cdiag, Matrix.mul_assoc]
  rw [this, hW, Matrix.mul_one, diagonal_mul_diagonal]
  rfl

theorem cdiag_one : cdiag W (1 : m → ℂ) = 1 := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  simp [cdiag, hW']

theorem cdiag_unitary {z : m → ℂ} (hz : ∀ j, ‖z j‖ = 1) : (cdiag W z)ᴴ * cdiag W z = 1 := by
  rw [cdiag_conjTranspose, cdiag_mul hW, ← cdiag_one hW]
  congr 1
  funext i
  have := hz i
  simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply]
  rw [Complex.star_def, Complex.conj_mul', this]; simp

end

theorem exists_cdiag_of_isHermitian {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    ∃ (W : Matrix m m ℂ) (d : m → ℝ), Wᴴ * W = 1 ∧ A = cdiag W (fun i => (d i : ℂ)) := by
  refine ⟨(hA.eigenvectorUnitary : Matrix m m ℂ), hA.eigenvalues, ?_, ?_⟩
  · exact Unitary.coe_star_mul_self _
  · conv_lhs => rw [hA.spectral_theorem]
    simp [cdiag, Unitary.conjStarAlgAut_apply]
    rfl

theorem norm_real_add_I (a : ℝ) : ‖(a : ℂ) + Complex.I‖ = ‖(a : ℂ) - Complex.I‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp

/-- There is a unimodular `z₀` with `z₀ - U` invertible. -/
theorem exists_unit_notMem_spectrum (U : Matrix m m ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (z • (1 : Matrix m m ℂ) - U).det ≠ 0 := by
  have hfin : {z : ℂ | (z • (1 : Matrix m m ℂ) - U).det = 0}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic U).ne_zero).subset ?_
    intro z hz
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly] at hz ⊢
    simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using hz
  let f : ℝ → ℂ := fun a => ((a : ℂ) + Complex.I) / ((a : ℂ) - Complex.I)
  have hne : ∀ a : ℝ, (a : ℂ) - Complex.I ≠ 0 := by
    intro a h; have := congrArg Complex.im h; simp at this
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f, div_eq_div_iff (hne a) (hne b)] at hab
    have := congrArg Complex.im hab
    simp [Complex.mul_im] at this
    linarith
  obtain ⟨z, hzimg, ha⟩ :=
    ((Set.infinite_univ (α := ℝ)).image hf_inj.injOn).exists_notMem_finite hfin
  obtain ⟨a, -, rfl⟩ := hzimg
  refine ⟨f a, ?_, ?_⟩
  · simp only [f, norm_div, norm_real_add_I]
    exact div_self (norm_ne_zero_iff.2 (hne a))
  · simpa using ha

/-- **Spectral theorem for unitaries**: `U = W diag(z) Wᴴ` with `W` unitary and `|zⱼ| = 1`. -/
theorem exists_cdiag_of_unitary {U : Matrix m m ℂ} (hU : Uᴴ * U = 1) :
    ∃ (W : Matrix m m ℂ) (z : m → ℂ), Wᴴ * W = 1 ∧ U = cdiag W z ∧ ∀ j, ‖z j‖ = 1 := by
  obtain ⟨z0, hz0, hdet⟩ := exists_unit_notMem_spectrum U
  set M : Matrix m m ℂ := z0 • 1 - U with hM
  set N : Matrix m m ℂ := z0 • 1 + U with hN
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hMu
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hMu
  have hz0' : star z0 * z0 = 1 := by rw [Complex.star_def, Complex.conj_mul', hz0]; simp
  have hE : Mᴴ * N + Nᴴ * M = 0 := by
    simp only [hM, hN, conjTranspose_sub, conjTranspose_add, conjTranspose_smul,
      conjTranspose_one, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hU]
    match_scalars <;> first | ring1 | linear_combination (2 : ℂ) * hz0'
  set H : Matrix m m ℂ := Complex.I • (N * M⁻¹) with hH
  have hHherm : H.IsHermitian := by
    have h1 : (M⁻¹)ᴴ * Mᴴ = 1 := by rw [← conjTranspose_mul, hMi, conjTranspose_one]
    have h3 : Nᴴ * M = -(Mᴴ * N) := eq_neg_of_add_eq_zero_right hE
    have h2 : (M⁻¹)ᴴ * Nᴴ = -(N * M⁻¹) := by
      calc (M⁻¹)ᴴ * Nᴴ = (M⁻¹)ᴴ * (Nᴴ * M) * M⁻¹ := by
            simp only [Matrix.mul_assoc, hMi, Matrix.mul_one]
        _ = -(N * M⁻¹) := by
            rw [h3]; simp only [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, h1,
              Matrix.one_mul]
    show Hᴴ = H
    rw [hH, conjTranspose_smul, conjTranspose_mul, h2, Complex.star_def, Complex.conj_I,
      smul_neg, neg_smul, neg_neg]
  have hHM : H * M = Complex.I • N := by
    rw [hH, smul_mul_assoc, Matrix.mul_assoc, hiM, Matrix.mul_one]
  have hrel : (H + Complex.I • 1) * U = z0 • (H - Complex.I • 1) := by
    have h' := hHM
    simp only [hM, Matrix.mul_sub, mul_smul_comm, Matrix.mul_one, hN, smul_add] at h'
    have e : (H + Complex.I • 1) * U = H * U + Complex.I • U := by
      rw [add_mul]; congr 1; rw [smul_mul_assoc, Matrix.one_mul]
    rw [e]
    linear_combination (norm := module) (-1 : ℂ) • h'
  obtain ⟨W, d, hW, hHd⟩ := exists_cdiag_of_isHermitian hHherm
  have hne : ∀ i, (d i : ℂ) + Complex.I ≠ 0 := by
    intro i h; have := congrArg Complex.im h; simp at this
  let a : m → ℂ := fun i => (d i : ℂ) + Complex.I
  let b : m → ℂ := fun i => (d i : ℂ) - Complex.I
  have hrel' : cdiag W a * U = z0 • cdiag W b := by
    have e1 : H + Complex.I • 1 = cdiag W a := by
      rw [hHd, ← cdiag_one hW, cdiag_smul, cdiag_add]
      congr 1; funext i; simp [a]
    have e2 : H - Complex.I • 1 = cdiag W b := by
      rw [hHd, ← cdiag_one hW, cdiag_smul, cdiag_sub]
      congr 1; funext i; simp [b]
    rw [← e1, ← e2]; exact hrel
  have hga : a⁻¹ * a = 1 := by
    funext i; exact inv_mul_cancel₀ (hne i)
  have hU' : U = cdiag W (z0 • (a⁻¹ * b)) := by
    calc U = cdiag W (1 : m → ℂ) * U := by rw [cdiag_one hW, Matrix.one_mul]
      _ = cdiag W (a⁻¹) * (cdiag W a * U) := by
          rw [← Matrix.mul_assoc, cdiag_mul hW, hga]
      _ = _ := by rw [hrel', mul_smul_comm, cdiag_mul hW, cdiag_smul]
  refine ⟨W, _, hW, hU', fun j => ?_⟩
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.inv_apply, smul_eq_mul, norm_mul, hz0, one_mul,
    norm_inv, a, b]
  rw [norm_real_add_I]
  have : ‖(d j : ℂ) - Complex.I‖ ≠ 0 := norm_ne_zero_iff.2 (by
    intro h; have := congrArg Complex.im h; simp at this)
  field_simp

/-- **L2 for unitaries (diagonal form).** -/
theorem bdd_map_cdiag {k : Type*} [Fintype k] [DecidableEq k]
    (φ : Matrix m m ℂ →ₗ[ℂ] Matrix k k ℂ) (hφ : IsPositiveMap φ) (h1 : φ 1 = 1)
    {W : Matrix m m ℂ} (hW : Wᴴ * W = 1) {z : m → ℂ} (hz : ∀ j, ‖z j‖ ≤ 1) :
    Bdd 1 (φ (cdiag W z)) := by
  let P : m → Matrix m m ℂ := fun j => vecMulVec (fun a => W a j) (star fun a => W a j)
  have hcd : ∀ y : m → ℂ, cdiag W y = ∑ j, y j • P j := by
    intro y; ext a b
    rw [cdiag, Matrix.mul_apply]
    simp only [P, Matrix.mul_diagonal, Matrix.sum_apply,
      Matrix.smul_apply, vecMulVec_apply, conjTranspose_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.star_apply]
    try ring
  have hsum : ∑ j, P j = 1 := by
    have := hcd 1
    rw [cdiag_one hW] at this
    simpa using this.symm
  have := bdd_map_of_decomp φ hφ h1 P (fun j => posSemidef_vecMulVec_self_star _) hsum z hz
  rwa [← hcd z] at this

/-- **L2** (Gurvits–Barnum, PRA 66, 062311): a unital positive map sends a unitary to a
contraction (vector form). -/
theorem bdd_map_unitary {k : Type*} [Fintype k] [DecidableEq k]
    (φ : Matrix m m ℂ →ₗ[ℂ] Matrix k k ℂ) (hφ : IsPositiveMap φ) (h1 : φ 1 = 1)
    {U : Matrix m m ℂ} (hU : Uᴴ * U = 1) : Bdd 1 (φ U) := by
  obtain ⟨W, z, hW, rfl, hz⟩ := exists_cdiag_of_unitary hU
  exact bdd_map_cdiag φ hφ h1 hW fun j => (hz j).le

end Contr

/-- info: 'FormalResearch.GurvitsBarnum.Contr.bdd_map_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Contr.bdd_map_unitary

end FormalResearch.GurvitsBarnum
