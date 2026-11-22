module

public import Mathlib
public import FormalResearch.JB.JBSchur

/-!
# Paper J, charts: plain regularity bounds (the smooth-jet budget as hypotheses)

Source: Paper J `app_smooth.tex`, `lem:smo-budget` (derivative budget), `thm:smo-WT2`, `thm:smo-TPC`, `thm:smo-MPS`
(real smooth Langer/Moser charts), and `lem:cha-L` (matched-action Langer lemma) in `charts.tex`.

The *proofs* of the smooth chart constructions (real implicit function theorem, Hadamard division, fibre contraction, Moser flow) are
Layer 4.  Layers 2--3 use them only through **plain bounds**, packaged here as `BoundedC2`: a coefficient `phi(u, X)` (at fixed `mu`, `N`) is
jointly `C^2` on a rectangle in the sense of `JB.FullC2` (the package that `JB.jb_schur_of_C2` consumes) with all of
`phi, d_u phi, d_X phi, d_u d_X phi` bounded by `S`.  The paper's derivative budget (`C^{r-2}` coordinates, `Pi` of class `C^{r-3}`, correctors `C^{2q_m+1}`,
`lem:smo-budget` (b)--(e)) is what `JetReg`/`EK` with `r >= r(max(2K-1,0))` buys; every chart structure states, in the docstring of
the field concerned, which part of the budget it uses.  The class `C^2` is all that Layer 3 needs; for the eigenvalue rule (Layer 2,
`thm:smo-spec`) the regularity class needed is `C^{2M+1}`, expressed by `JetRegJ` below.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set

/-- `phi` is jointly `C^2` in `(u, X)` on `[a,b] x [c,d]` in the sense of `JB.FullC2`, with `phi` and its partial derivatives
`d_u`, `d_X`, `d_u d_X` bounded by `S` (the hypothesis of `JB.jb_schur_of_C2`, `JB.jb_schur_inv`, `JB.jb_schur_div`). -/
def BoundedC2 (φ : ℝ → ℝ → ℝ) (a b c d S : ℝ) : Prop :=
  ∃ φ₁ φ₂ φ₁₂ : ℝ → ℝ → ℝ, FormalResearch.JB.FullC2 φ φ₁ φ₂ φ₁₂ a b c d ∧
    ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ t s| ≤ S ∧ |φ₁ t s| ≤ S ∧ |φ₂ t s| ≤ S ∧ |φ₁₂ t s| ≤ S

/-- Class `C^k` of a function of `(X, t)` on `I x [-t0, t0]`, jointly, with the derivatives up to order `k` continuous
(used for the phase coefficients `Sigma_{nu,j}(X,t)` of `thm:smo-BSr`, class `C^{2M+1}`). -/
def JetRegJ (f : ℝ → ℝ → ℝ) (I : Set ℝ) (t0 : ℝ) (k : ℕ) : Prop :=
  ContDiffOn ℝ (k : WithTop ℕ∞) (fun p : ℝ × ℝ => f p.1 p.2) (I ×ˢ Icc (-t0) t0)

end FormalResearch.JacobiEigenvectors.Charts
