module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements

/-!
# Paper J, Layer 2 (L2.C7): the sign hypotheses (ii), (iii) of `lem:tha-count` on the soft chart (`SoftCountHyps`)

Source: app_thmA, proof of prop:tha-W2, Step 6 (counting).  The statement `SoftCountHyps` is the interface between the counting
argument (`TheoremA/SoftCount*.lean`, `TheoremA/SoftW2.lean`) and the sign analysis of Step 6 (ii), (iii) (`TheoremA/SoftSigns*.lean`):
it is exactly hypotheses (ii) and (iii) of `PropThaCount` (`TheoremA/Statements.lean`, proved as `propThaCount` in `TheoremA/Count.lean`),
specialised to the soft chart `CL` of `Fz` with the data below.  It is a `Prop` definition, never an axiom: the sign analysis
discharges it, and `propThaW2_proved_of_signs` (`TheoremA/SoftW2.lean`) takes it as an explicit premise.

## The data

* `I := {X : |X - bandHi| <= delta_0}` (the whole energy window of the chart); on it `Phi X := pi * softMu0 CL p X`, with
  `softMu0 CL p X := mu_0(bandHi - X) = CL.muS 0 p (bandHi - X)`.  `Phi` is continuous (`mu0_deriv`) and strictly decreasing
  (`mu0_slope`, `cmu0 <= mu_0' <= Cmu0` on `|alpha| <= delta_0`), `mu_0(0) = 0`.
* The windows are `w_k = {X in I : |Phi X - pi h (k + 1/2)| <= eps}` with the **fixed** half-width `eps := pi h / 8`
  (the lemma requires `0 < eps < pi h / 4`).  The paper takes `Phi := pi mu-tilde` and `eps = C h^{m+1}`; since every eigenvalue
  obeying Step 0 lies within `C h^{m+1} Lm + C' h^2` of the centre of its window in `mu_0` (`soft_window_label` and
  `mu-tilde - mu_0 = O(h^2)`), the choice `Phi = pi mu_0` (for which strict monotonicity is a chart field and no bound on
  the derivatives of `mu_{2r}`, `r >= 1`, is needed) and `eps = pi h / 8` has the same zeros in the same windows; for small `h` the
  window `w_k` contains no other eigenvalue than the one of label `k`, so (iii) at the zeros of `w_k` is a statement about the
  eigenvalue of label `k`.
* (iii) is stated for the eigenvalues of an eigen-system obeying Step 0 (`Xs i <= bandHi + Cs0 h^2` for all `i`), as in the
  eigen-system clauses of `PropThaW2`: a zero of `casD` is an eigenvalue (`casD_zero_exists_eig`, `TheoremA/SoftCountLink.lean`),
  and `p = kappa' q` is the relation `pSol X n = kappa' qSol X (N - n)` of `PropThaCount` (iii).  The sign `sigma'` does not depend on
  the eigen-system (the statement is existential in `sigma'` before the universal quantifier over `Xs`, `Um`).

## What the sign analysis has to prove (Step 6 (ii), (iii))

For each `p in P` and `N` with `step N <= h1` (a threshold, `h1` of the statement):
* (ii) there is `sigma = +-1` with `sign casD(X) = sign (sigma (-1)^k)` whenever `|X - bandHi| <= delta_0` and `mu_0(bandHi - X) = h k`,
  `k : N`.  (There `a = -mu-tilde/h = -k + O(h)`, `cos (pi a) = (-1)^k + O(h^2)`; the paper evaluates at `a = -k`.)
* (iii) there is `sigma' = +-1` with `sign kappa' = sign (sigma' (-1)^k)` for every eigenvalue `X_i` of an eigen-system obeying Step 0,
  `|X_i - bandHi| <= delta_0`, `|pi mu_0 - pi h (k + 1/2)| <= pi h / 8`, and `kappa'` with `p = kappa' q`.

## Differences from the paper

`Phi = pi mu_0` and `eps = pi h/8` instead of `Phi = pi mu-tilde` and `eps = C h^{m+1}` (see above); `I` is the whole chart window
`|X - bandHi| <= delta_0` (so that the windows of the nominal points in `|X - bandHi| <= delta_0/2` have their bracketing interval in
`Phi(I)`); `sigma`, `sigma'` may depend on `(p, N)` (the lemma needs only that).  Not formalised here: the proof of the statement.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- The nominal action `mu_0(bandHi - X)` of the soft chart (`Phi = pi mu_0` in the counting lemma). -/
def softMu0 {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
    (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (X : ℝ) : ℝ :=
  CL.muS 0 p (Fz.bandHi p - X)

/-- **Hypotheses (ii), (iii) of `lem:tha-count` on the soft chart** (Step 6 of the proof of prop:tha-W2): see the module docstring.
Hypothesis (i) (every zero lies in a window) is proved from `soft_window_label`; the sign facts below are Step 6 (ii), (iii). -/
def SoftCountHyps {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
    (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm) (Cs0 : ℝ) : Prop :=
  ∃ h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ X : ℝ, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ k : ℕ,
        Real.pi * softMu0 CL p X = Real.pi * Fz.step N * k →
          SignType.sign (casD Fz p N X) = SignType.sign (σ * (-1) ^ k)) ∧
    (∃ σ' : ℝ, (σ' = 1 ∨ σ' = -1) ∧
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) →
        ∀ i : Fin (N + 1), |Xs i - Fz.bandHi p| ≤ CL.δ0 → ∀ k : ℕ,
          |Real.pi * softMu0 CL p (Xs i) - Real.pi * Fz.step N * ((k : ℝ) + 1 / 2)| ≤ Real.pi * Fz.step N / 8 →
          ∀ κ' : ℝ, (∀ n ≤ N, pSol Fz p N (Xs i) n = κ' * qSol Fz p N (Xs i) (N - n)) →
            SignType.sign κ' = SignType.sign (σ' * (-1) ^ k))

end FormalResearch.JacobiEigenvectors.TheoremA

end
