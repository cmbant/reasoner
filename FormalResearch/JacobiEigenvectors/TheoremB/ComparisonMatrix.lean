module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Comparison

/-!
# Paper J, Theorem B: the explicit comparison matrices `hat G^{[r]}` (definitions)

Source: Paper J `thmB.tex`: Section "The comparison matrices" (eq:thb-shift, eq:thb-profile, eq:thb-bulkcol, eq:thb-Gm), `prop:tha-splice` (the splice).
`hat G^{[r]}(n_s)` has the column `(hat N(n_s)/hat N) hat Psi^{(n_s)}_k`, i.e. the **normalisers and matching scalars are those of the standard splice**
(they do not depend on `n_s`), and only the row at which the left profile is replaced by the right one moves:

* bulk column `k` with `X_k` in the block `nu`: `psi-hat^L_n / hat N` for `n <= n_nu`, `hat kappa psi-hat^R_n / hat N` for `n > n_nu` (eq:thb-bulkcol),
  `n_nu = nearestRow (spl nu)`, a fixed row of the window `[c', c]` of the block;
* soft column (upper edge): the same with the split at the fixed fold row `n_c = nearestRow u_c`, the same row for every column of the edge; the left piece is
  `psi-hat^L` (Weber, then `lambda_L psi-hat^{PC,-}` on the collar) and the right piece `hat kappa psi-hat^R`;
* lower soft edge: the gauge vector `(-1)^n` times the vector of the gauge family at energy `-X`.

`compMatrix CI spl mu N X` is the matrix whose column `k` is `compColumn` at the energy `X_k` (given: the matrices are explicit once the exact spectrum is given; the one-step
criterion is stated for them, `JB.OneStepInputs`).  `hat G_m = compMatrix` for the order-`m` chart bundle `CI0`; `hat G^{[m+1]}` for `CI1`, with the *same* splice positions `spl` and the same `q`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
open scoped Classical

variable {Par : Type*} [TopologicalSpace Par]

/-- The lattice row nearest to the position `x`: `u_n = (n + 1/2) h`, so `n = round(x/h - 1/2)`. -/
def nearestRow (h x : ℝ) : ℤ := round (x / h - 1 / 2)

/-- The glued vector with the normaliser and the matching scalar of the *standard* split `isLeftStd`, but the switch from left to right profile at row `ns`
(the column of `hat G^{[r]}(n_s)`). -/
def glueVecAt (ψL ψR : ℤ → ℝ) (Ω rows : Finset ℤ) (isLeftStd : ℤ → Prop) (ns n : ℤ) : ℝ :=
  if n ≤ ns then ψL n / glueNorm ψL ψR Ω rows isLeftStd
  else glueKappa ψL ψR Ω * ψR n / glueNorm ψL ψR Ω rows isLeftStd

/-- The normaliser `hat N(n_s)` of `prop:tha-splice`: the glue norm with the split at `n_s`. -/
def glueNormAt (ψL ψR : ℤ → ℝ) (Ω rows : Finset ℤ) (ns : ℤ) : ℝ := glueNorm ψL ψR Ω rows (fun n => n ≤ ns)

section Cols

variable {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ} {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi : ℝ}

/-- Bulk column at splice row `ns`. -/
def bulkColAt (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (p : Par × ℝ) (X : ℝ) (N : ℕ) (ns : ℤ) : ℤ → ℝ :=
  glueVecAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) (fun n => uNode (Fz.step N) n ≤ CL.c) ns

/-- Soft column at splice row `ns`. -/
def softColAt (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)
    (p : Par × ℝ) (X : ℝ) (N : ℕ) (ns : ℤ) : ℤ → ℝ :=
  glueVecAt (CL.psiHatL p X N) (softSeqR CR p X N) (softWindow CL p X N) (rowsOf N) (fun n => CL.Zof p X N n ≤ 0) ns

end Cols

section Matrix

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The fixed splice positions `c_nu in [c'_nu, c_nu]` of the bulk blocks (a row `n_nu = nearestRow` in the window of the block). -/
structure Splices (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) where
  spl : Fin CI.nb → ℝ
  spl_mem : ∀ ν, (CI.bulkL ν).c' ≤ spl ν ∧ spl ν ≤ (CI.bulkL ν).c

/-- Column of `hat G^{[r]}` at the energy `X` (row `n`): the three cases as in `psiHatVec`, with the fixed splice rows. -/
def compColumn (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ) (X : ℝ) (n : ℤ) : ℝ :=
  if h : ∃ ν, CI.lo ν ≤ X ∧ X ≤ CI.hi ν then
    bulkColAt (CI.bulkL (Classical.choose h)) (CI.bulkR (Classical.choose h)) (atStep F μ N) X N
      (nearestRow (F.step N) (spl (Classical.choose h))) n
  else if CI.Jhi < X then
    softColAt CI.softUpL CI.softUpR (atStep F μ N) X N (nearestRow (F.step N) (CI.softUpL.uc (atStep F μ N))) n
  else (-1 : ℝ) ^ n *
    softColAt CI.softLoL CI.softLoR (atStep F μ N) (-X) N (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) n

/-- The comparison matrix `hat G^{[m]}` (rows `n`, columns `k`) for the spectrum `X`. -/
def compMatrix (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ) (X : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i k => compColumn CI spl μ N (X k) ((i : ℕ) : ℤ)

end Matrix

end FormalResearch.JacobiEigenvectors.TheoremB
