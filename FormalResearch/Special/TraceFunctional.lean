module

public import Mathlib
public import FormalResearch.MatrixAnalysis.Spectral.WeylMatrix

/-!
# `lem:traceperturb`: the trace functional is Lipschitz in the trace norm

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `lem:traceperturb`.  For a Hermitian matrix `A` and
`φ : ℝ → ℂ`, `Tr φ(A) := ∑ᵢ φ(λᵢ(A))` (`traceFn`, the sum over the eigenvalues with multiplicity).

* `traceFn_sub_le_lipschitz` : if `A, B` are Hermitian with all eigenvalues in `I` and `φ` is `Λ`-Lipschitz on `I`,
  then `‖Tr φ(A) - Tr φ(B)‖ ≤ Λ ‖A - B‖₁` (`‖·‖₁ = FormalResearch.MatrixAnalysis.tnorm`);
* `traceperturb` : the paper's `C¹` form: `φ` has derivative `φ'` on the interval `I` (one-sided at
  endpoints), `‖φ'‖ ≤ K` on `I` (`K = sup_I |φ'|`).

The proof differs from the paper's (which differentiates `Tr p(A_t)` along `A_t = B + t(A - B)` for polynomials
`p` and passes to the limit): here the Lipschitz estimate is a direct consequence of **Lidskii's inequality**
`∑_j |λ_j(A) - λ_j(B)| ≤ ‖A - B‖₁` (`herm_lidskii_tnorm`, `FormalResearch.MatrixAnalysis.Spectral`) and the
mean value inequality, and it covers the Lipschitz case without any approximation.  The statement proved is
the paper's.

Not formalised: nothing of the lemma is left out; the matrix functional calculus `φ(A)` as a matrix is not
introduced (only its trace `traceFn`).
-/

@[expose] public section

namespace FormalResearch.Special.TraceCore

open Matrix FormalResearch.MatrixAnalysis FormalResearch.MatrixAnalysis.Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Tr φ(A) = ∑ᵢ φ(λᵢ(A))` for a Hermitian matrix `A` (complex-valued `φ` on the real spectrum). -/
noncomputable def traceFn (φ : ℝ → ℂ) {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℂ :=
  ∑ i, φ (hA.eigenvalues i)

/-- Reindexing the eigenvalues from `Fin (card n)` to `n`, for complex-valued functions. -/
theorem sum_eigenvalues₀_eq_c {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    ∑ j, f (hA.eigenvalues₀ j) = ∑ i, f (hA.eigenvalues i) := by
  unfold Matrix.IsHermitian.eigenvalues
  exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun j => f (hA.eigenvalues₀ j))).symm

lemma traceFn_eq_sum₀ (φ : ℝ → ℂ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceFn φ hA = ∑ j, φ (hA.eigenvalues₀ j) := (sum_eigenvalues₀_eq_c hA φ).symm

lemma eigenvalues₀_mem {A : Matrix n n ℂ} (hA : A.IsHermitian) {I : Set ℝ}
    (hI : ∀ i, hA.eigenvalues i ∈ I) (j : Fin (Fintype.card n)) : hA.eigenvalues₀ j ∈ I := by
  have := hI ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
  unfold Matrix.IsHermitian.eigenvalues at this
  simpa using this

/-- **`lem:traceperturb`, Lipschitz form.** -/
theorem traceFn_sub_le_lipschitz {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {I : Set ℝ} (hAI : ∀ i, hA.eigenvalues i ∈ I) (hBI : ∀ i, hB.eigenvalues i ∈ I)
    {φ : ℝ → ℂ} {Lip : ℝ} (hL : 0 ≤ Lip) (hφ : ∀ x ∈ I, ∀ y ∈ I, ‖φ x - φ y‖ ≤ Lip * |x - y|) :
    ‖traceFn φ hA - traceFn φ hB‖ ≤ Lip * tnorm (A - B) := by
  rw [traceFn_eq_sum₀, traceFn_eq_sum₀, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖φ (hA.eigenvalues₀ j) - φ (hB.eigenvalues₀ j)‖
      ≤ ∑ j, Lip * |hA.eigenvalues₀ j - hB.eigenvalues₀ j| :=
        Finset.sum_le_sum fun j _ => hφ _ (eigenvalues₀_mem hA hAI j) _ (eigenvalues₀_mem hB hBI j)
    _ = Lip * ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| := by rw [Finset.mul_sum]
    _ ≤ Lip * tnorm (A - B) := mul_le_mul_of_nonneg_left (herm_lidskii_tnorm hA hB) hL

/-- **`lem:traceperturb`** (paper form): `A, B` Hermitian with spectra in the interval `I`, `φ` continuously
differentiable on `I` with derivative `φ'` (one-sided at endpoints) and `‖φ'‖ ≤ K` on `I` (`K = sup_I |φ'|`).
Then `|Tr φ(A) - Tr φ(B)| ≤ K ‖A - B‖₁`. -/
theorem traceperturb {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {I : Set ℝ} (hIc : I.OrdConnected) (hAI : ∀ i, hA.eigenvalues i ∈ I)
    (hBI : ∀ i, hB.eigenvalues i ∈ I) {φ φ' : ℝ → ℂ} (hφd : ∀ x ∈ I, HasDerivWithinAt φ (φ' x) I x)
    (hφc : ContinuousOn φ' I) {K : ℝ} (hK : ∀ x ∈ I, ‖φ' x‖ ≤ K) :
    ‖traceFn φ hA - traceFn φ hB‖ ≤ K * tnorm (A - B) := by
  have _ := hφc
  have hconv : Convex ℝ I := hIc.convex
  rcases isEmpty_or_nonempty n with hn | hn
  · have h1 : traceFn φ hA = 0 := by unfold traceFn; simp
    have h2 : traceFn φ hB = 0 := by unfold traceFn; simp
    rw [h1, h2, sub_zero, norm_zero]
    have h3 : tnorm (A - B) = 0 := by
      rw [tnorm_eq (hA.sub hB)]; simp
    rw [h3, mul_zero]
  · obtain ⟨i0⟩ := hn
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK _ (hAI i0))
    refine traceFn_sub_le_lipschitz hA hB hAI hBI hK0 (fun x hx y hy => ?_)
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hφd hK hy hx
    simpa [Real.norm_eq_abs] using this

/-- info: 'FormalResearch.Special.TraceCore.traceperturb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms traceperturb

/-- info: 'FormalResearch.Special.TraceCore.traceFn_sub_le_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms traceFn_sub_le_lipschitz

end FormalResearch.Special.TraceCore
