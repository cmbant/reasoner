import FormalResearch.FourQubitEntropy.Tradeoff
import FormalResearch.FourQubitEntropy.IsospectralOverlap

/-!
# The spectral spin-flip bound for four qubits

Source: `ResearchNotes/QI/four_qubit_entropy/spectral_spinflip_bound.tex` (QIprojects PR 208),
Proposition `prop:fqe-spectral-spinflip` and, through `IsospectralOverlap.lean`, Lemma
`lem:fqe-isospectral-overlap`.

For a unit state `ψ` of four qubits, each eigenvalue `λ` of each balanced cut marginal satisfies
`(2λ - 1)₊² ≤ τ + W₁/2 = 2 (P - 1) - W₁/2 ≤ 2 (P - 1)`, where `τ = |ψᵀ σ_y^{⊗4} ψ|²`
(`normSq (spinFlipForm ψ)`), `W₁ = blochSq ψ` and `P = purity ψ` (the sum of the three cut purities).

* `spectral_spinflip_12`, `_13`, `_14` (**proved**): `(max (2λ - 1) 0)² ≤ τ + W₁/2` for every eigenvalue
  of `red12 ψ`, `red13 ψ`, `red14 ψ` (the cuts `12|34`, `13|24`, `14|23`).
* `spectral_spinflip_12_purity` etc.: the same with right side `2 (P - 1) - W₁/2` (`spectral_rhs_eq`),
  hence `≤ 2 (P - 1)`.
* `two_flat_cross_cost_12`, `_13`, `_14`: the first inequality of `(TF)` (`prop:fqe-two-flat-rigidity`) for every unit state.
* `eigenvalues_le_half_of_purity_one`: `P = 1` forces every balanced eigenvalue to be at most `1/2`.
* `spectral_spinflip_coeff_optimal` (**proved**): the coefficients `1` of `τ` and `1/2` of `W₁` cannot be
  lowered (for the cut `12|34`), tested on `bell2` (`τ = 1`, `W₁ = 0`, eigenvalue `1`) and on
  `|00⟩ ⊗ χ` with `χ` maximally entangled (`pairHad`: `τ = 0`, `W₁ = 2`, eigenvalue `1`).

The proof follows the paper: the overlap lemma is applied to `ψ` and its spin flip
`flipPsi ψ = ε^{⊗4} ψ̄` (`σ_y^{⊗4} = ε^{⊗4}`), whose coefficient matrix for each cut is
`(ε⊗ε) M̄ (ε⊗ε)` (`coef12_flip` etc.). The overlap `⟨ψ, ψ̃⟩` is `conj (spinFlipForm ψ)`
(`trace_coef12` etc.), and the two marginal mismatch terms add to `W₁` (`mismatch_eq_blochSq12` etc.,
a polynomial identity closed by `ring`). Not formalized: the attainment statement of the lemma (sign-flipped
Schmidt terms), the general two-parameter family of the paper's sharpness proof, and unequal local
dimensions in the lemma. The proposition is stated for pure unit four-qubit states only.
-/

open scoped ComplexConjugate Matrix
open FormalResearch.FourQubitEntropy.Isospectral

namespace FormalResearch.FourQubitEntropy

/-- Coefficient matrix of the cut `12|34`: `M (a,b) (c,d) = ψ a b c d`. -/
def coef12 (ψ : Psi) : Mat4 := Matrix.of fun i j => ψ i.1 i.2 j.1 j.2
/-- Coefficient matrix of the cut `13|24`. -/
def coef13 (ψ : Psi) : Mat4 := Matrix.of fun i j => ψ i.1 j.1 i.2 j.2
/-- Coefficient matrix of the cut `14|23`. -/
def coef14 (ψ : Psi) : Mat4 := Matrix.of fun i j => ψ i.1 j.1 j.2 i.2

/-- The spin flip `ψ̃ = σ_y^{⊗4} ψ̄` (`σ_y = -i ε`, so `σ_y^{⊗4} = ε^{⊗4}`). -/
noncomputable def flipPsi (ψ : Psi) : Psi := fun a b c d =>
  ((sgn a * sgn b * sgn c * sgn d : ℤ) : ℂ) * (starRingEnd ℂ) (ψ (1 - a) (1 - b) (1 - c) (1 - d))

/-- The two-qubit operator `ε ⊗ ε` (real, symmetric, an involution). -/
noncomputable def epsEps : Mat4 :=
  Matrix.of fun i k => if k = (1 - i.1, 1 - i.2) then ((sgn i.1 * sgn i.2 : ℤ) : ℂ) else 0

theorem epsEps_mul (A : Mat4) (i j : Fin 2 × Fin 2) :
    (epsEps * A) i j = ((sgn i.1 * sgn i.2 : ℤ) : ℂ) * A (1 - i.1, 1 - i.2) j := by
  simp [epsEps, Matrix.mul_apply, Finset.sum_ite_eq']

theorem mul_epsEps (A : Mat4) (i j : Fin 2 × Fin 2) :
    (A * epsEps) i j = A i (1 - j.1, 1 - j.2) * ((sgn j.1 * sgn j.2 : ℤ) : ℂ) := by
  obtain ⟨c, d⟩ := j
  fin_cases c <;> fin_cases d <;>
    simp [epsEps, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, sgn]

theorem epsEps_unitary : epsEps ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [epsEps, Matrix.mul_apply, Matrix.star_apply, Fintype.sum_prod_type, Fin.sum_univ_two, sgn]


theorem red12_coef (ψ : Psi) : red12 ψ = coef12 ψ * (coef12 ψ)ᴴ := by
  ext i j
  simp [red12, coef12, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Complex.star_def]

theorem red13_coef (ψ : Psi) : red13 ψ = coef13 ψ * (coef13 ψ)ᴴ := by
  ext i j
  simp [red13, coef13, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Complex.star_def]

theorem red14_coef (ψ : Psi) : red14 ψ = coef14 ψ * (coef14 ψ)ᴴ := by
  ext i j
  simp [red14, coef14, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Complex.star_def]

theorem fn2_coef12 (ψ : Psi) : fn2 (coef12 ψ) = normSqPsi ψ := by
  simp [fn2, coef12, normSqPsi, Fintype.sum_prod_type]

theorem fn2_coef13 (ψ : Psi) : fn2 (coef13 ψ) = normSqPsi ψ := by
  simp only [fn2, coef13, normSqPsi, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.of_apply]
  ring

theorem fn2_coef14 (ψ : Psi) : fn2 (coef14 ψ) = normSqPsi ψ := by
  simp only [fn2, coef14, normSqPsi, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.of_apply]
  ring

theorem coef12_flip (ψ : Psi) :
    coef12 (flipPsi ψ) = epsEps * (coef12 ψ).map (starRingEnd ℂ) * epsEps := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [mul_epsEps, epsEps_mul]
  simp only [coef12, flipPsi, Matrix.of_apply, Matrix.map_apply]
  push_cast; ring

theorem coef13_flip (ψ : Psi) :
    coef13 (flipPsi ψ) = epsEps * (coef13 ψ).map (starRingEnd ℂ) * epsEps := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [mul_epsEps, epsEps_mul]
  simp only [coef13, flipPsi, Matrix.of_apply, Matrix.map_apply]
  push_cast; ring

theorem coef14_flip (ψ : Psi) :
    coef14 (flipPsi ψ) = epsEps * (coef14 ψ).map (starRingEnd ℂ) * epsEps := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [mul_epsEps, epsEps_mul]
  simp only [coef14, flipPsi, Matrix.of_apply, Matrix.map_apply]
  push_cast; ring


theorem fin2_one_sub_zero : (1 : Fin 2) - 0 = 1 := by decide
theorem fin2_one_sub_one : (1 : Fin 2) - 1 = 0 := by decide
theorem fin2_one_ne_zero : ¬ ((1 : Fin 2) = 0) := by decide

theorem trace_coef12 (ψ : Psi) :
    Matrix.trace ((coef12 ψ)ᴴ * coef12 (flipPsi ψ)) = (starRingEnd ℂ) (spinFlipForm ψ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coef12, flipPsi, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two, spinFlipForm, sum4, sum2,
    lit_complex, sgn, map_add, map_mul, Complex.conj_conj, Complex.star_def, map_intCast,
    fin2_one_sub_zero, fin2_one_sub_one, fin2_one_ne_zero, eq_self_iff_true, ite_true, ite_false,
    Fin.isValue]
  push_cast
  ring

theorem trace_coef13 (ψ : Psi) :
    Matrix.trace ((coef13 ψ)ᴴ * coef13 (flipPsi ψ)) = (starRingEnd ℂ) (spinFlipForm ψ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coef13, flipPsi, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two, spinFlipForm, sum4, sum2,
    lit_complex, sgn, map_add, map_mul, Complex.conj_conj, Complex.star_def, map_intCast,
    fin2_one_sub_zero, fin2_one_sub_one, fin2_one_ne_zero, eq_self_iff_true, ite_true, ite_false,
    Fin.isValue]
  push_cast
  ring

theorem trace_coef14 (ψ : Psi) :
    Matrix.trace ((coef14 ψ)ᴴ * coef14 (flipPsi ψ)) = (starRingEnd ℂ) (spinFlipForm ψ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coef14, flipPsi, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two, spinFlipForm, sum4, sum2,
    lit_complex, sgn, map_add, map_mul, Complex.conj_conj, Complex.star_def, map_intCast,
    fin2_one_sub_zero, fin2_one_sub_one, fin2_one_ne_zero, eq_self_iff_true, ite_true, ite_false,
    Fin.isValue]
  push_cast
  ring


set_option maxRecDepth 100000 in
/-- `‖ρ_A - σ_A‖² + ‖ρ_B - σ_B‖² = W₁` for the cut `12`, `σ` the marginals of the spin flip. -/
theorem mismatch_eq_blochSq12 (ψ : Psi) :
    fn2 (coef12 ψ * (coef12 ψ)ᴴ - coef12 (flipPsi ψ) * (coef12 (flipPsi ψ))ᴴ)
      + fn2 ((coef12 ψ)ᴴ * coef12 ψ - (coef12 (flipPsi ψ))ᴴ * coef12 (flipPsi ψ))
      = blochSq ψ := by
  have h := W1gen_eq ψ
  have key : ((fn2 (coef12 ψ * (coef12 ψ)ᴴ - coef12 (flipPsi ψ) * (coef12 (flipPsi ψ))ᴴ)
      + fn2 ((coef12 ψ)ᴴ * coef12 ψ - (coef12 (flipPsi ψ))ᴴ * coef12 (flipPsi ψ)) : ℝ) : ℂ)
      = (blochSq ψ : ℂ) := by
    rw [← h]
    have e : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = z * (starRingEnd ℂ) z :=
      fun z => (Complex.mul_conj z).symm
    simp only [fn2, Complex.ofReal_add, Complex.ofReal_sum, e]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, coef12, Matrix.of_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [map_sum, map_mul, map_sub, Complex.conj_conj, map_intCast, flipPsi, Complex.star_def]
    simp only [W1gen, trRho2, rho0, siteSwap, sum2, normG, sum4, Psi.conj, sgn, toAdd_complex,
      toMul_complex, toSub_complex, lit_complex]
    simp only [fin2_one_sub_zero, fin2_one_sub_one, fin2_one_ne_zero, sub_zero, ite_true, ite_false,
      eq_self_iff_true, Fin.isValue, Complex.ofReal_one, one_mul, mul_one, mul_neg, neg_mul, neg_neg,
      Int.cast_one, Int.cast_neg, map_neg, map_one, map_add, map_mul, Complex.conj_conj]
    ring
  exact_mod_cast key

set_option maxRecDepth 100000 in
/-- `‖ρ_A - σ_A‖² + ‖ρ_B - σ_B‖² = W₁` for the cut `13`, `σ` the marginals of the spin flip. -/
theorem mismatch_eq_blochSq13 (ψ : Psi) :
    fn2 (coef13 ψ * (coef13 ψ)ᴴ - coef13 (flipPsi ψ) * (coef13 (flipPsi ψ))ᴴ)
      + fn2 ((coef13 ψ)ᴴ * coef13 ψ - (coef13 (flipPsi ψ))ᴴ * coef13 (flipPsi ψ))
      = blochSq ψ := by
  have h := W1gen_eq ψ
  have key : ((fn2 (coef13 ψ * (coef13 ψ)ᴴ - coef13 (flipPsi ψ) * (coef13 (flipPsi ψ))ᴴ)
      + fn2 ((coef13 ψ)ᴴ * coef13 ψ - (coef13 (flipPsi ψ))ᴴ * coef13 (flipPsi ψ)) : ℝ) : ℂ)
      = (blochSq ψ : ℂ) := by
    rw [← h]
    have e : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = z * (starRingEnd ℂ) z :=
      fun z => (Complex.mul_conj z).symm
    simp only [fn2, Complex.ofReal_add, Complex.ofReal_sum, e]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, coef13, Matrix.of_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [map_sum, map_mul, map_sub, Complex.conj_conj, map_intCast, flipPsi, Complex.star_def]
    simp only [W1gen, trRho2, rho0, siteSwap, sum2, normG, sum4, Psi.conj, sgn, toAdd_complex,
      toMul_complex, toSub_complex, lit_complex]
    simp only [fin2_one_sub_zero, fin2_one_sub_one, fin2_one_ne_zero, sub_zero, ite_true, ite_false,
      eq_self_iff_true, Fin.isValue, Complex.ofReal_one, one_mul, mul_one, mul_neg, neg_mul, neg_neg,
      Int.cast_one, Int.cast_neg, map_neg, map_one, map_add, map_mul, Complex.conj_conj]
    ring
  exact_mod_cast key

set_option maxRecDepth 100000 in
/-- `‖ρ_A - σ_A‖² + ‖ρ_B - σ_B‖² = W₁` for the cut `14`, `σ` the marginals of the spin flip. -/
theorem mismatch_eq_blochSq14 (ψ : Psi) :
    fn2 (coef14 ψ * (coef14 ψ)ᴴ - coef14 (flipPsi ψ) * (coef14 (flipPsi ψ))ᴴ)
      + fn2 ((coef14 ψ)ᴴ * coef14 ψ - (coef14 (flipPsi ψ))ᴴ * coef14 (flipPsi ψ))
      = blochSq ψ := by
  have h := W1gen_eq ψ
  have key : ((fn2 (coef14 ψ * (coef14 ψ)ᴴ - coef14 (flipPsi ψ) * (coef14 (flipPsi ψ))ᴴ)
      + fn2 ((coef14 ψ)ᴴ * coef14 ψ - (coef14 (flipPsi ψ))ᴴ * coef14 (flipPsi ψ)) : ℝ) : ℂ)
      = (blochSq ψ : ℂ) := by
    rw [← h]
    have e : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = z * (starRingEnd ℂ) z :=
      fun z => (Complex.mul_conj z).symm
    simp only [fn2, Complex.ofReal_add, Complex.ofReal_sum, e]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, coef14, Matrix.of_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [map_sum, map_mul, map_sub, Complex.conj_conj, map_intCast, flipPsi, Complex.star_def]
    simp only [W1gen, trRho2, rho0, siteSwap, sum2, normG, sum4, Psi.conj, sgn, toAdd_complex,
      toMul_complex, toSub_complex, lit_complex]
    simp only [fin2_one_sub_zero, fin2_one_sub_one, fin2_one_ne_zero, sub_zero, ite_true, ite_false,
      eq_self_iff_true, Fin.isValue, Complex.ofReal_one, one_mul, mul_one, mul_neg, neg_mul, neg_neg,
      Int.cast_one, Int.cast_neg, map_neg, map_one, map_add, map_mul, Complex.conj_conj]
    ring
  exact_mod_cast key


/-- Spectral bound for one cut of a unit state, given the cut's coefficient matrix. -/
theorem spectral_bound_cut (R : Mat4) (hR : R.IsHermitian) (M : Mat4) (hRM : R = M * Mᴴ)
    (hM : fn2 M = 1) (i : Fin 2 × Fin 2) :
    (max (2 * hR.eigenvalues i - 1) 0) ^ 2 ≤
      Complex.normSq (Matrix.trace (Mᴴ * (epsEps * M.map (starRingEnd ℂ) * epsEps)))
      + (fn2 (M * Mᴴ - (epsEps * M.map (starRingEnd ℂ) * epsEps) *
            (epsEps * M.map (starRingEnd ℂ) * epsEps)ᴴ)
        + fn2 (Mᴴ * M - (epsEps * M.map (starRingEnd ℂ) * epsEps)ᴴ *
            (epsEps * M.map (starRingEnd ℂ) * epsEps))) / 2 := by
  have hv0 := hR.mulVec_eigenvectorBasis i
  set v : Fin 2 × Fin 2 → ℂ := ⇑(hR.eigenvectorBasis i) with hvdef
  have hv : (M * Mᴴ) *ᵥ v = ((hR.eigenvalues i : ℝ) : ℂ) • v := by
    rw [← hRM, hv0]; exact (Complex.coe_smul _ _).symm
  have hne : v ≠ 0 := by
    have := hR.eigenvectorBasis.orthonormal.ne_zero i
    intro h0; apply this; ext j; exact congrFun h0 j
  exact antiunitary_overlap M epsEps epsEps hM epsEps_unitary epsEps_unitary v hne _ hv

/-- `prop:fqe-spectral-spinflip`, cut `12`: every eigenvalue `λ` of the cut marginal satisfies
`(2λ - 1)₊² ≤ τ + W₁/2`. -/
theorem spectral_spinflip_12 (ψ : Psi) (hn : normSqPsi ψ = 1) (i : Fin 2 × Fin 2) :
    (max (2 * (red12_herm ψ).eigenvalues i - 1) 0) ^ 2
      ≤ Complex.normSq (spinFlipForm ψ) + blochSq ψ / 2 := by
  have h := spectral_bound_cut (red12 ψ) (red12_herm ψ) (coef12 ψ) (red12_coef ψ)
    (by rw [fn2_coef12, hn]) i
  rw [← coef12_flip, trace_coef12, Complex.normSq_conj, mismatch_eq_blochSq12] at h
  linarith

/-- `prop:fqe-spectral-spinflip`, cut `13`: every eigenvalue `λ` of the cut marginal satisfies
`(2λ - 1)₊² ≤ τ + W₁/2`. -/
theorem spectral_spinflip_13 (ψ : Psi) (hn : normSqPsi ψ = 1) (i : Fin 2 × Fin 2) :
    (max (2 * (red13_herm ψ).eigenvalues i - 1) 0) ^ 2
      ≤ Complex.normSq (spinFlipForm ψ) + blochSq ψ / 2 := by
  have h := spectral_bound_cut (red13 ψ) (red13_herm ψ) (coef13 ψ) (red13_coef ψ)
    (by rw [fn2_coef13, hn]) i
  rw [← coef13_flip, trace_coef13, Complex.normSq_conj, mismatch_eq_blochSq13] at h
  linarith

/-- `prop:fqe-spectral-spinflip`, cut `14`: every eigenvalue `λ` of the cut marginal satisfies
`(2λ - 1)₊² ≤ τ + W₁/2`. -/
theorem spectral_spinflip_14 (ψ : Psi) (hn : normSqPsi ψ = 1) (i : Fin 2 × Fin 2) :
    (max (2 * (red14_herm ψ).eigenvalues i - 1) 0) ^ 2
      ≤ Complex.normSq (spinFlipForm ψ) + blochSq ψ / 2 := by
  have h := spectral_bound_cut (red14 ψ) (red14_herm ψ) (coef14 ψ) (red14_coef ψ)
    (by rw [fn2_coef14, hn]) i
  rw [← coef14_flip, trace_coef14, Complex.normSq_conj, mismatch_eq_blochSq14] at h
  linarith

/-- `τ + W₁/2 = 2 (P - 1) - W₁/2` for unit states (the purity identity). -/
theorem spectral_rhs_eq (ψ : Psi) (hn : normSqPsi ψ = 1) :
    Complex.normSq (spinFlipForm ψ) + blochSq ψ / 2 = 2 * (purity ψ - 1) - blochSq ψ / 2 := by
  have h := purity_identity_exact ψ
  rw [hn] at h
  linarith

/-- `prop:fqe-spectral-spinflip`, cut `12|34`, in the form `(2λ - 1)₊² ≤ 2 (P - 1) - W₁/2`. -/
theorem spectral_spinflip_12_purity (ψ : Psi) (hn : normSqPsi ψ = 1) (i : Fin 2 × Fin 2) :
    (max (2 * (red12_herm ψ).eigenvalues i - 1) 0) ^ 2 ≤ 2 * (purity ψ - 1) - blochSq ψ / 2 :=
  (spectral_spinflip_12 ψ hn i).trans_eq (spectral_rhs_eq ψ hn)

/-- `prop:fqe-spectral-spinflip`, cut `13|24`, in the form `(2λ - 1)₊² ≤ 2 (P - 1) - W₁/2`. -/
theorem spectral_spinflip_13_purity (ψ : Psi) (hn : normSqPsi ψ = 1) (i : Fin 2 × Fin 2) :
    (max (2 * (red13_herm ψ).eigenvalues i - 1) 0) ^ 2 ≤ 2 * (purity ψ - 1) - blochSq ψ / 2 :=
  (spectral_spinflip_13 ψ hn i).trans_eq (spectral_rhs_eq ψ hn)

/-- `prop:fqe-spectral-spinflip`, cut `14|23`, in the form `(2λ - 1)₊² ≤ 2 (P - 1) - W₁/2`. -/
theorem spectral_spinflip_14_purity (ψ : Psi) (hn : normSqPsi ψ = 1) (i : Fin 2 × Fin 2) :
    (max (2 * (red14_herm ψ).eigenvalues i - 1) 0) ^ 2 ≤ 2 * (purity ψ - 1) - blochSq ψ / 2 :=
  (spectral_spinflip_14 ψ hn i).trans_eq (spectral_rhs_eq ψ hn)

/-- `P = 1` forces every balanced eigenvalue to be at most `1/2` (all three cuts). -/
theorem eigenvalues_le_half_of_purity_one (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1) :
    (∀ i, (red12_herm ψ).eigenvalues i ≤ 1 / 2) ∧ (∀ i, (red13_herm ψ).eigenvalues i ≤ 1 / 2) ∧
      (∀ i, (red14_herm ψ).eigenvalues i ≤ 1 / 2) := by
  have hW := blochSq_nonneg ψ
  have key : ∀ l : ℝ, (max (2 * l - 1) 0) ^ 2 ≤ 2 * (purity ψ - 1) - blochSq ψ / 2 → l ≤ 1 / 2 := by
    intro l h
    rw [hP] at h
    by_contra hl
    have hl := not_le.mp hl
    rw [max_eq_left (by linarith)] at h
    nlinarith
  exact ⟨fun i => key _ (spectral_spinflip_12_purity ψ hn i),
    fun i => key _ (spectral_spinflip_13_purity ψ hn i),
    fun i => key _ (spectral_spinflip_14_purity ψ hn i)⟩

/-! ### Crossed purity cost (the first inequality of `(TF)`, `prop:fqe-two-flat-rigidity`) -/

theorem sum_eig_eq_trace {R : Mat4} (hR : R.IsHermitian) :
    ∑ i, hR.eigenvalues i = (Matrix.trace R).re := by
  simpa using sum_eigenvalues_pow hR 1

theorem two_flat_real (l : Fin 2 × Fin 2 → ℝ) (hs : ∑ j, l j = 1) (i : Fin 2 × Fin 2)
    (hi : 1 / 2 ≤ l i) (P W c : ℝ) (hc : ∑ j, l j ^ 2 = c)
    (hb : (max (2 * l i - 1) 0) ^ 2 ≤ 2 * (P - 1) - W / 2) :
    W / 4 + ((∑ j ∈ Finset.univ.erase i, l j) ^ 2 - ∑ j ∈ Finset.univ.erase i, l j ^ 2)
      ≤ P - c - 1 / 2 := by
  rw [max_eq_left (by linarith)] at hb
  have h1 : ∑ j ∈ Finset.univ.erase i, l j = 1 - l i := by
    have := Finset.add_sum_erase Finset.univ l (Finset.mem_univ i)
    linarith
  have h2 : ∑ j ∈ Finset.univ.erase i, l j ^ 2 = c - l i ^ 2 := by
    have := Finset.add_sum_erase Finset.univ (fun j => l j ^ 2) (Finset.mem_univ i)
    linarith
  rw [h1, h2]
  nlinarith

/-- `prop:fqe-two-flat-rigidity`, first inequality of `(TF)` for the cut `12|34` of any unit pure
state: if an eigenvalue `λ_i` of `red12 ψ` is at least `1/2`, then
`W₁/4 + 2 e₂(other three eigenvalues) ≤ tr red13² + tr red14² - 1/2`, i.e. `Δ_k ≥ W₁/4 + 2 e₂` with
`Δ_k = Σ_{j ≠ k} (p_j - 1/4)` and `2 e₂ = (Σ_{j≠i} λ_j)² - Σ_{j≠i} λ_j²`. -/
theorem two_flat_cross_cost_12 (ψ : Psi) (hn : normSqPsi ψ = 1) (i : Fin 2 × Fin 2)
    (hi : 1 / 2 ≤ (red12_herm ψ).eigenvalues i) :
    blochSq ψ / 4 + ((∑ j ∈ Finset.univ.erase i, (red12_herm ψ).eigenvalues j) ^ 2
        - ∑ j ∈ Finset.univ.erase i, (red12_herm ψ).eigenvalues j ^ 2)
      ≤ (Matrix.trace (red13 ψ * red13 ψ)).re + (Matrix.trace (red14 ψ * red14 ψ)).re - 1 / 2 := by
  have hs : ∑ j, (red12_herm ψ).eigenvalues j = 1 := by
    rw [sum_eig_eq_trace, trace_red12, hn]; simp
  have hc : ∑ j, (red12_herm ψ).eigenvalues j ^ 2 = (Matrix.trace (red12 ψ * red12 ψ)).re := by
    rw [sum_eigenvalues_pow (red12_herm ψ) 2, pow_two]
  have := two_flat_real _ hs i hi (purity ψ) (blochSq ψ) _ hc (spectral_spinflip_12_purity ψ hn i)
  unfold purity at this
  linarith

/-- `(TF)` first inequality for the cut `13|24`. -/
theorem two_flat_cross_cost_13 (ψ : Psi) (hn : normSqPsi ψ = 1) (i : Fin 2 × Fin 2)
    (hi : 1 / 2 ≤ (red13_herm ψ).eigenvalues i) :
    blochSq ψ / 4 + ((∑ j ∈ Finset.univ.erase i, (red13_herm ψ).eigenvalues j) ^ 2
        - ∑ j ∈ Finset.univ.erase i, (red13_herm ψ).eigenvalues j ^ 2)
      ≤ (Matrix.trace (red12 ψ * red12 ψ)).re + (Matrix.trace (red14 ψ * red14 ψ)).re - 1 / 2 := by
  have hs : ∑ j, (red13_herm ψ).eigenvalues j = 1 := by
    rw [sum_eig_eq_trace, trace_red13, hn]; simp
  have hc : ∑ j, (red13_herm ψ).eigenvalues j ^ 2 = (Matrix.trace (red13 ψ * red13 ψ)).re := by
    rw [sum_eigenvalues_pow (red13_herm ψ) 2, pow_two]
  have := two_flat_real _ hs i hi (purity ψ) (blochSq ψ) _ hc (spectral_spinflip_13_purity ψ hn i)
  unfold purity at this
  linarith

/-- `(TF)` first inequality for the cut `14|23`. -/
theorem two_flat_cross_cost_14 (ψ : Psi) (hn : normSqPsi ψ = 1) (i : Fin 2 × Fin 2)
    (hi : 1 / 2 ≤ (red14_herm ψ).eigenvalues i) :
    blochSq ψ / 4 + ((∑ j ∈ Finset.univ.erase i, (red14_herm ψ).eigenvalues j) ^ 2
        - ∑ j ∈ Finset.univ.erase i, (red14_herm ψ).eigenvalues j ^ 2)
      ≤ (Matrix.trace (red12 ψ * red12 ψ)).re + (Matrix.trace (red13 ψ * red13 ψ)).re - 1 / 2 := by
  have hs : ∑ j, (red14_herm ψ).eigenvalues j = 1 := by
    rw [sum_eig_eq_trace, trace_red14, hn]; simp
  have hc : ∑ j, (red14_herm ψ).eigenvalues j ^ 2 = (Matrix.trace (red14 ψ * red14 ψ)).re := by
    rw [sum_eigenvalues_pow (red14_herm ψ) 2, pow_two]
  have := two_flat_real _ hs i hi (purity ψ) (blochSq ψ) _ hc (spectral_spinflip_14_purity ψ hn i)
  unfold purity at this
  linarith

/-! ### Optimality of the coefficients -/

theorem exists_eigenvalue_one (R : Mat4) (hR : R.IsHermitian) (v : Fin 2 × Fin 2 → ℂ) (hv : v ≠ 0)
    (hRv : R *ᵥ v = v) : ∃ i, hR.eigenvalues i = 1 := by
  have hmem : (1 : ℝ) ∈ spectrum ℝ R := by
    rw [spectrum.mem_iff]
    intro hu
    apply hv
    obtain ⟨u, hu⟩ := hu
    have h0 : (algebraMap ℝ Mat4 1 - R) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, hRv]; simp
    rw [← hu] at h0
    have := congrArg (fun w => (↑u⁻¹ : Mat4) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec] using this
  rw [hR.spectrum_real_eq_range_eigenvalues] at hmem
  exact hmem

/-- `|00⟩ ⊗ χ` with `χ = ½ Σ (-1)^{cd} |cd⟩` maximally entangled. -/
noncomputable def pairHad : Psi := fun a b c d =>
  if a = 0 ∧ b = 0 then (if c = 1 ∧ d = 1 then -1 / 2 else 1 / 2) else 0

theorem pairHad_vals : normSqPsi pairHad = 1 ∧ blochSq pairHad = 2 ∧
    Complex.normSq (spinFlipForm pairHad) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · eval_state pairHad
  · eval_state pairHad
  · simp [spinFlipForm, sum4, sum2, lit_complex, pairHad]

theorem bell2_eig_one : ∃ i, (red12_herm bell2).eigenvalues i = 1 := by
  refine exists_eigenvalue_one _ _ (fun i => if i.1 = i.2 then 1 else 0) ?_ ?_
  · intro h
    have := congrFun h (0, 0)
    simp at this
  · ext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      simp [red12, bell2, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat] <;> norm_num

theorem pairHad_eig_one : ∃ i, (red12_herm pairHad).eigenvalues i = 1 := by
  refine exists_eigenvalue_one _ _ (fun i => if i = (0, 0) then 1 else 0) ?_ ?_
  · intro h
    have := congrFun h (0, 0)
    simp at this
  · ext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      simp [red12, pairHad, Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_ofNat, map_neg, map_div₀, map_one]
    <;> norm_num

/-- Optimality of the coefficients in `prop:fqe-spectral-spinflip`: if
`(2λ - 1)₊² ≤ c₁ τ + c₂ W₁` holds for every eigenvalue of `red12` of every unit state, then
`c₁ ≥ 1` and `c₂ ≥ 1/2`. -/
theorem spectral_spinflip_coeff_optimal (c₁ c₂ : ℝ)
    (h : ∀ ψ : Psi, normSqPsi ψ = 1 → ∀ i, (max (2 * (red12_herm ψ).eigenvalues i - 1) 0) ^ 2
      ≤ c₁ * Complex.normSq (spinFlipForm ψ) + c₂ * blochSq ψ) : 1 ≤ c₁ ∧ 1 / 2 ≤ c₂ := by
  obtain ⟨i, hi⟩ := bell2_eig_one
  obtain ⟨j, hj⟩ := pairHad_eig_one
  have h1 := h bell2 bell2_vals.1 i
  have h2 := h pairHad pairHad_vals.1 j
  rw [hi, bell2_tau, bell2_vals.2.2.2] at h1
  rw [hj, pairHad_vals.2.2, pairHad_vals.2.1] at h2
  norm_num at h1 h2
  constructor <;> linarith

end FormalResearch.FourQubitEntropy
