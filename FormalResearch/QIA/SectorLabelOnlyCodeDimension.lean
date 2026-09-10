import Mathlib.Analysis.Matrix.Order

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder

/-!
# QI-A T07 sector-label-only finite code dimension bound

Source authority:

* `cmbant/QIprojects:QI-A/notes/SECTOR_LABEL_ONLY_MEMORY.md`, Lemma 2.1;
* `cmbant/QIprojects:QI-A/scripts/verify_sector_label_only_memory.py`;
* audited at QIprojects main `6080f36ddd7a3c85015416b793e0562caf685e5a`.

The source finite-dimensional argument is operationally simple but genuinely
quantum: for uniformly distributed messages stored in a `q`-dimensional
quantum branch, decoder POVM effects `B_j` and encoded states `omega_j` obey

`(1/N) sum_j Tr(B_j omega_j) <= q/N`

because `omega_j <= I`, the effects are positive, and `sum_j B_j=I`.
Combining this with an ideal identifying-query success at least `1-eta` and
the total-variation comparison defining deficiency gives

`delta >= 1-eta-q/N`.

This module formalizes that trace-budget implication for finite-dimensional
complex matrices.  The standard density-operator fact `omega <= I` is kept as
an explicit hypothesis rather than rebuilding density-matrix spectral theory.
The assumptions that a later query supplies the displayed POVM and that the
correct-message event changes by at most `delta` are likewise explicit; this
keeps the Lean statement faithful to the sector-label-only operational model.

The regular Bergman/packing asymptotics, global label-leakage estimate, Fano
bound, Gaussian critical limit, and finite critical transfer are not proved
here.  In particular this module does not restore the source-refuted
unrestricted-physical block-curve converse.
-/

/-- Real part of the Born trace score.  For positive effects and states this is
in fact real and nonnegative; using the real part keeps scalar inequalities in
`ℝ` while retaining the exact complex matrix product. -/
noncomputable def sectorCodeTraceScore {q : Type*} [Fintype q]
    (B omega : Matrix q q ℂ) : ℝ :=
  RCLike.re (Matrix.trace (B * omega))

/-- The trace pairing of two positive-semidefinite complex matrices has
nonnegative real part.  The proof factors the first matrix as `Xᴴ X`, cycles
the trace, and uses positivity of `X B Xᴴ`. -/
theorem re_trace_mul_nonneg {q : Type*} [Fintype q] [DecidableEq q]
    {A B : Matrix q q ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ RCLike.re (Matrix.trace (A * B)) := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hX]
  have hXB : (X * B * Xᴴ).PosSemidef := hB.mul_mul_conjTranspose_same X
  have hre : 0 ≤ RCLike.re (Matrix.trace (X * B * Xᴴ)) :=
    (RCLike.nonneg_iff.mp hXB.trace_nonneg).1
  rw [Matrix.trace_mul_cycle X B Xᴴ] at hre
  simpa [star_eq_conjTranspose, Matrix.mul_assoc] using hre

/-- If `B` is a POVM effect and the encoded state obeys `omega <= I`, then its
Born score is at most the trace budget of `B`. -/
theorem sectorCodeTraceScore_le_effectTrace
    {q : Type*} [Fintype q] [DecidableEq q]
    {B omega : Matrix q q ℂ}
    (hB : B.PosSemidef) (homega : omega ≤ (1 : Matrix q q ℂ)) :
    sectorCodeTraceScore B omega ≤ RCLike.re (Matrix.trace B) := by
  have hdiff : ((1 : Matrix q q ℂ) - omega).PosSemidef :=
    Matrix.le_iff.mp homega
  have hnonneg := re_trace_mul_nonneg hB hdiff
  unfold sectorCodeTraceScore
  simp [mul_sub] at hnonneg
  exact hnonneg

/-- Exact POVM trace budget: summing the correct-message Born scores over all
uniform messages cannot exceed the Hilbert-space dimension. -/
theorem sectorCode_totalSuccess_le_dimension
    {J q : Type*} [Fintype J] [Fintype q] [DecidableEq q]
    (B omega : J → Matrix q q ℂ)
    (hB : ∀ j, (B j).PosSemidef)
    (homega : ∀ j, omega j ≤ (1 : Matrix q q ℂ))
    (hPOVM : (∑ j, B j) = (1 : Matrix q q ℂ)) :
    (∑ j, sectorCodeTraceScore (B j) (omega j)) ≤ (Fintype.card q : ℝ) := by
  classical
  calc
    (∑ j, sectorCodeTraceScore (B j) (omega j))
        ≤ ∑ j, RCLike.re (Matrix.trace (B j)) := by
          exact Finset.sum_le_sum fun j _ =>
            sectorCodeTraceScore_le_effectTrace (hB j) (homega j)
    _ = (Fintype.card q : ℝ) := by
      have htrace := congrArg
        (fun M : Matrix q q ℂ => RCLike.re (Matrix.trace M)) hPOVM
      simpa using htrace

/-- Average correct-message success for a uniform finite message set. -/
noncomputable def sectorCodeAverageSuccess {J q : Type*} [Fintype J] [Fintype q]
    (B omega : J → Matrix q q ℂ) : ℝ :=
  (∑ j, sectorCodeTraceScore (B j) (omega j)) / (Fintype.card J : ℝ)

/-- The source `q/N` dimension bound, with dimensions represented by finite
types: average decoder success is at most `card(q)/card(J)`. -/
theorem sectorCode_averageSuccess_le_dimensionRatio
    {J q : Type*} [Fintype J] [Nonempty J]
    [Fintype q] [DecidableEq q]
    (B omega : J → Matrix q q ℂ)
    (hB : ∀ j, (B j).PosSemidef)
    (homega : ∀ j, omega j ≤ (1 : Matrix q q ℂ))
    (hPOVM : (∑ j, B j) = (1 : Matrix q q ℂ)) :
    sectorCodeAverageSuccess B omega ≤
      (Fintype.card q : ℝ) / (Fintype.card J : ℝ) := by
  classical
  have hcard : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast Fintype.card_pos
  unfold sectorCodeAverageSuccess
  exact (div_le_div_iff_of_pos_right hcard).2
    (sectorCode_totalSuccess_le_dimension B omega hB homega hPOVM)

/-- Operational form of T07 Lemma 2.1.

`idealSuccess` is the success probability of the ideal identifying query.
`hideal` records ideal error at most `eta`; `hTV` records that deficiency
`delta` can reduce the correct-message event by at most `delta`.  Under the
same POVM/state hypotheses as the trace budget, the source bound follows. -/
theorem sectorLabelOnly_conditional_deficiency_bound
    {J q : Type*} [Fintype J] [Nonempty J]
    [Fintype q] [DecidableEq q]
    (B omega : J → Matrix q q ℂ)
    (eta delta idealSuccess : ℝ)
    (hB : ∀ j, (B j).PosSemidef)
    (homega : ∀ j, omega j ≤ (1 : Matrix q q ℂ))
    (hPOVM : (∑ j, B j) = (1 : Matrix q q ℂ))
    (hideal : 1 - eta ≤ idealSuccess)
    (hTV : idealSuccess ≤ sectorCodeAverageSuccess B omega + delta) :
    1 - eta - (Fintype.card q : ℝ) / (Fintype.card J : ℝ) ≤ delta := by
  have hmem := sectorCode_averageSuccess_le_dimensionRatio
    B omega hB homega hPOVM
  linarith

end FormalResearch.QIA
