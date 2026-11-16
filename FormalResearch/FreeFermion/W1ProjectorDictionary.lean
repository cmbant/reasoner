module

public import Mathlib

/-!
# The finite projector dictionary (Weyl W1, `prop:finite`)

Source: `Weyl/free_fermion/paper/parts/constants.tex`, Proposition `prop:finite` (finite projector
dictionary).  (The label `prop:finite` also occurs in `Weyl/notes/askey_wilson_midpoint/`, a
different statement; the one formalised here is the W1 paper's.)

Throughout `W`, `P` are matrices on a finite index type, `C = W P W` (the compression of `P` to
`Ran W`, extended by zero), `K = (1 - W)(1 - P)(1 - W)` and `A = (1 - W) P W`.

## Statements formalised

* `charpoly_mul_mul_eq` / `spectrum_nonzero_eq` : `W P W` and `P W P` have the same characteristic
  polynomial (hence the same spectrum with algebraic multiplicities, zero included, since both act
  on the whole space), and the same nonzero spectrum.  Only `W² = W`, `P² = P` is used.
* `finrank_eigenspace_eq` : for `λ ≠ 0, 1` the eigenspaces of `C` and of `K` at `λ` have the same
  dimension, so `λ ∈ (0, 1)` is an eigenvalue of `C` iff it is of `K`, with multiplicity
  (`hasEigenvalue_iff`).  Only `W² = W`, `P² = P` is used: the maps `A` and `W (1-P) (1-W)`
  intertwine (`K A = A C`, `C B = B K`) and are injective on the eigenspaces.
* `adjoint_mul_self` : `Aᴴ A = C (1 - C)` for orthogonal projections.
* `trace_variance` : `Tr C (1 - C) = ‖A‖_F²` and `‖[P, W]‖_F² = 2 ‖A‖_F²` (so `V_L = ‖A‖₂² =
  ½ ‖[P, W]‖₂²`), together with the block form `[P, W] = A - Aᴴ`.

## Not formalised

* The replica / full-counting formula `eq:replica`, `Tr(ρ_Aⁿ e^{iθ N_A}) = det[(1-C)ⁿ + e^{iθ} Cⁿ]`
  for a Slater determinant: it needs fermionic Fock space, Gaussian states and the reduction of a
  Slater determinant to the occupations of the eigenmodes of `C`, none of which are in the library.
* The statement is for matrices (finite-dimensional Hilbert space with a chosen orthonormal basis),
  with `C` and `K` as operators on the whole space rather than compressions to `Ran W` and
  `Ran (1 - W)`; the nonzero eigenvalues and multiplicities are the same.
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix Module

section Algebraic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [Field 𝕜]

/-- Algebraic core, for any two idempotent matrices (no self-adjointness needed): `K A = A C`. -/
theorem intertwine {W P : Matrix ι ι 𝕜} (hW : W * W = W) (hP : P * P = P) :
    ((1 - W) * (1 - P) * (1 - W)) * ((1 - W) * P * W) = ((1 - W) * P * W) * (W * P * W) := by
  have hWW : ∀ x : Matrix ι ι 𝕜, W * (W * x) = W * x := fun x => by rw [← mul_assoc, hW]
  have hPP : ∀ x : Matrix ι ι 𝕜, P * (P * x) = P * x := fun x => by rw [← mul_assoc, hP]
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hWW, hPP, hW]
  abel

/-- `B A = C - C²` with `B = W P (1 - W)`: the algebraic form of `Aᴴ A = C (1 - C)`. -/
theorem left_inverse_identity {W P : Matrix ι ι 𝕜} (hW : W * W = W) (hP : P * P = P) :
    (W * P * (1 - W)) * ((1 - W) * P * W) = (W * P * W) - (W * P * W) * (W * P * W) := by
  have hWW : ∀ x : Matrix ι ι 𝕜, W * (W * x) = W * x := fun x => by rw [← mul_assoc, hW]
  have hPP : ∀ x : Matrix ι ι 𝕜, P * (P * x) = P * x := fun x => by rw [← mul_assoc, hP]
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hWW, hPP]
  abel

/-- `W P W` and `P W P` have the same characteristic polynomial. -/
theorem charpoly_mul_mul_eq {W P : Matrix ι ι 𝕜} (hW : W * W = W) (hP : P * P = P) :
    (W * P * W).charpoly = (P * W * P).charpoly := by
  have h1 : W * P * W = (W * P) * (P * W) := by
    simp only [mul_assoc]; rw [← mul_assoc P P W, hP]
  have h2 : P * W * P = (P * W) * (W * P) := by
    simp only [mul_assoc]; rw [← mul_assoc W W P, hW]
  rw [h1, h2, charpoly_mul_comm]

/-- The nonzero spectra of `W P W` and `P W P` agree. -/
theorem spectrum_nonzero_eq {W P : Matrix ι ι 𝕜} (hW : W * W = W) (hP : P * P = P) :
    spectrum 𝕜 (W * P * W) \ {0} = spectrum 𝕜 (P * W * P) \ {0} := by
  have h1 : W * P * W = (W * P) * (P * W) := by
    simp only [mul_assoc]; rw [← mul_assoc P P W, hP]
  have h2 : P * W * P = (P * W) * (W * P) := by
    simp only [mul_assoc]; rw [← mul_assoc W W P, hW]
  rw [h1, h2]
  exact spectrum.nonzero_mul_comm _ _

/-- Transfer of eigenspace dimension along an intertwiner injective on the eigenspace. -/
theorem finrank_eigenspace_le {C K A : Matrix ι ι 𝕜} (lam : 𝕜) (h : K * A = A * C)
    (hinj : ∀ u, C *ᵥ u = lam • u → A *ᵥ u = 0 → u = 0) :
    finrank 𝕜 ↥(Module.End.eigenspace (Matrix.toLin' C) lam) ≤
      finrank 𝕜 ↥(Module.End.eigenspace (Matrix.toLin' K) lam) := by
  have hmaps : ∀ u ∈ Module.End.eigenspace (Matrix.toLin' C) lam,
      Matrix.toLin' A u ∈ Module.End.eigenspace (Matrix.toLin' K) lam := by
    intro u hu
    rw [Module.End.mem_eigenspace_iff] at hu ⊢
    simp only [Matrix.toLin'_apply] at hu ⊢
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul]
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (Matrix.toLin' A).restrict hmaps) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨u, hu⟩ h0
  have hA : A *ᵥ u = 0 := by
    have := congrArg Subtype.val h0
    simpa [LinearMap.restrict_apply] using this
  have hu' : C *ᵥ u = lam • u := by
    have := Module.End.mem_eigenspace_iff.mp hu
    simpa [Matrix.toLin'_apply] using this
  exact Subtype.ext (hinj u hu' hA)

/-- One direction of the eigenvalue dictionary: for `λ ≠ 0, 1` the `λ`-eigenspace of `C = W P W`
injects (via `A = (1 - W) P W`) into the `λ`-eigenspace of `K = (1 - W)(1 - P)(1 - W)`. -/
theorem finrank_eigenspace_le_of_idempotent {W P : Matrix ι ι 𝕜} (hW : W * W = W)
    (hP : P * P = P) {lam : 𝕜} (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    finrank 𝕜 ↥(Module.End.eigenspace (Matrix.toLin' (W * P * W)) lam) ≤
      finrank 𝕜 ↥(Module.End.eigenspace
        (Matrix.toLin' ((1 - W) * (1 - P) * (1 - W))) lam) := by
  refine finrank_eigenspace_le lam (intertwine hW hP) ?_
  intro u hu hAu
  have key : ∀ C : Matrix ι ι 𝕜, C *ᵥ u = lam • u → (C - C * C) *ᵥ u = (lam * (1 - lam)) • u := by
    intro C hC
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hC, Matrix.mulVec_smul, hC, smul_smul,
      mul_sub, mul_one, sub_smul]
  have h2 := key _ hu
  have h3 : (W * P * W - (W * P * W) * (W * P * W)) *ᵥ u = 0 := by
    rw [← left_inverse_identity hW hP, ← Matrix.mulVec_mulVec, hAu, Matrix.mulVec_zero]
  rw [h3] at h2
  have hne : lam * (1 - lam) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1.symm)
  exact (smul_eq_zero.mp h2.symm).resolve_left hne

/-- **Eigenvalue dictionary** (`prop:finite`, second claim): for `λ ≠ 0, 1` the eigenspaces of
`C = W P W` and `K = (1 - W)(1 - P)(1 - W)` at `λ` have the same dimension. -/
theorem finrank_eigenspace_eq {W P : Matrix ι ι 𝕜} (hW : W * W = W) (hP : P * P = P) {lam : 𝕜}
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    finrank 𝕜 ↥(Module.End.eigenspace (Matrix.toLin' (W * P * W)) lam) =
      finrank 𝕜 ↥(Module.End.eigenspace
        (Matrix.toLin' ((1 - W) * (1 - P) * (1 - W))) lam) := by
  refine le_antisymm (finrank_eigenspace_le_of_idempotent hW hP h0 h1) ?_
  have hW' : (1 - W) * (1 - W) = 1 - W := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, hW]; abel
  have hP' : (1 - P) * (1 - P) = 1 - P := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, hP]; abel
  have := finrank_eigenspace_le_of_idempotent hW' hP' h0 h1
  have e1 : (1 : Matrix ι ι 𝕜) - (1 - W) = W := by abel
  have e2 : (1 : Matrix ι ι 𝕜) - (1 - P) = P := by abel
  rwa [e1, e2] at this

/-- `λ ∉ {0, 1}` is an eigenvalue of `C = W P W` iff it is an eigenvalue of
`K = (1 - W)(1 - P)(1 - W)`. -/
theorem hasEigenvalue_iff {W P : Matrix ι ι 𝕜} (hW : W * W = W) (hP : P * P = P) {lam : 𝕜}
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    Module.End.HasEigenvalue (Matrix.toLin' (W * P * W)) lam ↔
      Module.End.HasEigenvalue (Matrix.toLin' ((1 - W) * (1 - P) * (1 - W))) lam := by
  have := finrank_eigenspace_eq hW hP h0 h1
  rw [Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff]
  simp only [ne_eq, ← Submodule.finrank_eq_zero (R := 𝕜), this]

end Algebraic

section Hilbert

open scoped Matrix.Norms.Frobenius

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]

/-- The squared Frobenius (Hilbert–Schmidt) norm is the sum of squared entry norms. -/
theorem frobenius_sq_eq_sum (M : Matrix ι ι 𝕜) : ‖M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  have hnn : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

/-- `Tr(Mᴴ M) = ‖M‖_F²`. -/
theorem trace_conjTranspose_mul_self_eq (M : Matrix ι ι 𝕜) :
    trace (Mᴴ * M) = ((‖M‖ ^ 2 : ℝ) : 𝕜) := by
  rw [frobenius_sq_eq_sum]
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  rw [Finset.sum_comm]
  push_cast
  rfl

variable {W P : Matrix ι ι 𝕜}

/-- `Aᴴ = W P (1 - W)` for `A = (1 - W) P W` and orthogonal projections. -/
theorem conjTranspose_A (hWh : Wᴴ = W) (hPh : Pᴴ = P) :
    ((1 - W) * P * W)ᴴ = W * P * (1 - W) := by
  simp [conjTranspose_mul, conjTranspose_sub, hWh, hPh, mul_assoc]

/-- `Aᴴ A = C (1 - C)` (`eq:varianceexact`, first part). -/
theorem adjoint_mul_self (hW : W * W = W) (hP : P * P = P) (hWh : Wᴴ = W) (hPh : Pᴴ = P) :
    ((1 - W) * P * W)ᴴ * ((1 - W) * P * W) = (W * P * W) * (1 - W * P * W) := by
  rw [conjTranspose_A hWh hPh, left_inverse_identity hW hP, mul_sub, mul_one]

/-- The commutator has the block form `[P, W] = A - Aᴴ` (off-diagonal blocks `A`, `-Aᴴ`, zero
diagonal blocks). -/
theorem commutator_eq (hWh : Wᴴ = W) (hPh : Pᴴ = P) :
    P * W - W * P = (1 - W) * P * W - ((1 - W) * P * W)ᴴ := by
  rw [conjTranspose_A hWh hPh]; noncomm_ring

/-- `A² = 0`. -/
theorem A_mul_A (hW : W * W = W) : ((1 - W) * P * W) * ((1 - W) * P * W) = 0 := by
  have hWQ : W * (1 - W) = 0 := by rw [mul_sub, mul_one, hW, sub_self]
  calc ((1 - W) * P * W) * ((1 - W) * P * W)
      = (1 - W) * P * (W * (1 - W)) * P * W := by simp only [mul_assoc]
    _ = 0 := by rw [hWQ]; simp

/-- **Variance identity** (`eq:varianceexact`): `V = Tr C (1 - C) = ‖A‖_F²` and
`‖[P, W]‖_F² = 2 ‖A‖_F²`, i.e. `V = ‖A‖₂² = ½ ‖[P, W]‖₂²`. -/
theorem trace_variance (hW : W * W = W) (hP : P * P = P) (hWh : Wᴴ = W) (hPh : Pᴴ = P) :
    trace ((W * P * W) * (1 - W * P * W)) = ((‖(1 - W) * P * W‖ ^ 2 : ℝ) : 𝕜) ∧
    ‖P * W - W * P‖ ^ 2 = 2 * ‖(1 - W) * P * W‖ ^ 2 := by
  set A := (1 - W) * P * W with hA
  have hAA : A * A = 0 := A_mul_A hW
  have hBB : Aᴴ * Aᴴ = 0 := by rw [← conjTranspose_mul, hAA, conjTranspose_zero]
  refine ⟨by rw [← adjoint_mul_self hW hP hWh hPh, trace_conjTranspose_mul_self_eq], ?_⟩
  have h1 : ((P * W - W * P)ᴴ * (P * W - W * P)).trace = (2 : 𝕜) * trace (Aᴴ * A) := by
    rw [commutator_eq hWh hPh, ← hA, conjTranspose_sub, conjTranspose_conjTranspose]
    have : (Aᴴ - A) * (A - Aᴴ) = Aᴴ * A + A * Aᴴ - (Aᴴ * Aᴴ + A * A) := by noncomm_ring
    rw [this, hAA, hBB, add_zero, sub_zero, trace_add, trace_mul_comm A Aᴴ]; ring
  rw [trace_conjTranspose_mul_self_eq, trace_conjTranspose_mul_self_eq] at h1
  have h2 : ((‖P * W - W * P‖ ^ 2 : ℝ) : 𝕜) = ((2 * ‖A‖ ^ 2 : ℝ) : 𝕜) := by
    rw [h1]; push_cast; rfl
  exact_mod_cast h2

/-- **Finite projector dictionary** (`prop:finite`, all claims except the replica formula
`eq:replica`): for orthogonal projections `W`, `P` on a finite-dimensional Hilbert space,
`C = W P W`, `K = (1 - W)(1 - P)(1 - W)`, `A = (1 - W) P W`:
the nonzero spectra of `W P W` and `P W P` agree; the eigenvalues of `C` and `K` outside `{0, 1}`
agree with multiplicity; `Aᴴ A = C (1 - C)`; `Tr C (1 - C) = ‖A‖_F² = ½ ‖[P, W]‖_F²`. -/
theorem projector_dictionary (hW : W * W = W) (hP : P * P = P) (hWh : Wᴴ = W) (hPh : Pᴴ = P) :
    (spectrum 𝕜 (W * P * W) \ {0} = spectrum 𝕜 (P * W * P) \ {0}) ∧
    (∀ lam : 𝕜, lam ≠ 0 → lam ≠ 1 →
      finrank 𝕜 ↥(Module.End.eigenspace (Matrix.toLin' (W * P * W)) lam) =
        finrank 𝕜 ↥(Module.End.eigenspace
          (Matrix.toLin' ((1 - W) * (1 - P) * (1 - W))) lam)) ∧
    (((1 - W) * P * W)ᴴ * ((1 - W) * P * W) = (W * P * W) * (1 - W * P * W)) ∧
    (trace ((W * P * W) * (1 - W * P * W)) = ((‖(1 - W) * P * W‖ ^ 2 : ℝ) : 𝕜)) ∧
    (‖P * W - W * P‖ ^ 2 = 2 * ‖(1 - W) * P * W‖ ^ 2) :=
  ⟨spectrum_nonzero_eq hW hP, fun _ h0 h1 => finrank_eigenspace_eq hW hP h0 h1,
    adjoint_mul_self hW hP hWh hPh, (trace_variance hW hP hWh hPh).1,
    (trace_variance hW hP hWh hPh).2⟩

end Hilbert

/-- info: 'FormalResearch.FreeFermion.projector_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projector_dictionary

/-- info: 'FormalResearch.FreeFermion.charpoly_mul_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charpoly_mul_mul_eq

/-- info: 'FormalResearch.FreeFermion.hasEigenvalue_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasEigenvalue_iff

end FormalResearch.FreeFermion
