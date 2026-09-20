import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Matrix.PosDef

namespace FormalResearch.QID

open Matrix
open scoped ComplexOrder

/-!
# QI-D T48 E6/F4 harmonic-block factorization

Source authority:

* `cmbant/QIprojects:QI-D/code/certify_E6_F4_endpoint_locus_reduction.py`;
* `cmbant/QIprojects:QI-D/notes/T48_REPORT.md`;
* audited at QIprojects main `6080f36ddd7a3c85015416b793e0562caf685e5a`.

For one multiplicity-eight triality sector, T48 writes the endpoint projection
maps as `K_s : t -> V` and `P_s : a -> V`, and defines

`Z_s = [K_s, i P_s]`.

The source then proves that the positive-frequency harmonic block is exactly

`B = (1/2) Z_L^* Z_R`.

This module formalizes that block algebra abstractly for finite-dimensional
complex matrices. The theorem is independent of the unresolved common-F4
triality compatibility: it says only how the four overlap blocks assemble into
the complex Gram product once the endpoint maps `K_s,P_s` are given.

It does not identify those maps with genuine compact-F4 endpoints, prove the
T48 PSD/rank outer locus is exact, or prove the T33 quartic on the genuine
endpoint locus. In particular it is not a compact-E6 simultaneous Weyl
convexity theorem.
-/

/-- T48's complexified triality-sector column map `Z=[K,iP]`. -/
noncomputable def t48TrialityZ
    {V T A : Type*}
    (K : Matrix V T ℂ) (P : Matrix V A ℂ) :
    Matrix V (T ⊕ A) ℂ :=
  Matrix.fromCols K (Complex.I • P)

/-- Exact block expansion of `Z_L^* Z_R`.

The four blocks are the source overlap matrices
`K_L^* K_R`, `i K_L^* P_R`, `-i P_L^* K_R`, and `P_L^* P_R`.
This is the algebraic core of T48's harmonic factorization. -/
theorem t48TrialityZ_conjTranspose_mul
    {V T A : Type*} [Fintype V] [Fintype T] [Fintype A]
    (KL KR : Matrix V T ℂ) (PL PR : Matrix V A ℂ) :
    (t48TrialityZ KL PL)ᴴ * t48TrialityZ KR PR =
      Matrix.fromBlocks
        (KLᴴ * KR)
        (Complex.I • (KLᴴ * PR))
        ((-Complex.I) • (PLᴴ * KR))
        (PLᴴ * PR) := by
  classical
  unfold t48TrialityZ
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols]
  simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul]

/-- The overlap-block presentation of the positive-frequency matrix, with the
source's global factor `1/2`. -/
noncomputable def t48HarmonicBlockFromOverlaps
    {V T A : Type*} [Fintype V]
    (KL KR : Matrix V T ℂ) (PL PR : Matrix V A ℂ) :
    Matrix (T ⊕ A) (T ⊕ A) ℂ :=
  (1 / 2 : ℂ) •
    Matrix.fromBlocks
      (KLᴴ * KR)
      (Complex.I • (KLᴴ * PR))
      ((-Complex.I) • (PLᴴ * KR))
      (PLᴴ * PR)

/-- T48's exact harmonic factorization `B=(1/2) Z_L^* Z_R`. -/
theorem t48HarmonicBlock_factorization
    {V T A : Type*} [Fintype V] [Fintype T] [Fintype A]
    (KL KR : Matrix V T ℂ) (PL PR : Matrix V A ℂ) :
    t48HarmonicBlockFromOverlaps KL KR PL PR =
      (1 / 2 : ℂ) •
        ((t48TrialityZ KL PL)ᴴ * t48TrialityZ KR PR) := by
  simpa only [t48HarmonicBlockFromOverlaps] using
    congrArg (fun M => (1 / 2 : ℂ) • M)
      (t48TrialityZ_conjTranspose_mul KL KR PL PR).symm

/-- The same-side Gram matrix underlying the T48 block construction is positive
semidefinite. This is a basic exact consequence of the factorized form; it is
not the stronger source claim that the full endpoint outer-locus Gram matrix is
an exact characterization of genuine endpoints. -/
theorem t48TrialityZ_selfGram_posSemidef
    {V T A : Type*} [Fintype V] [Fintype T] [Fintype A]
    (K : Matrix V T ℂ) (P : Matrix V A ℂ) :
    ((t48TrialityZ K P)ᴴ * t48TrialityZ K P).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self _

end FormalResearch.QID
