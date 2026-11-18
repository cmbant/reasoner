module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.SoftParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.Regularity

/-!
# Paper J, charts: `SoftPhaseInputs`, the soft analogue of `BulkPhaseInputs` (finding F-S6-6)

Source: Paper J `app_thmA.tex`, `thm:smo-BSr` ("Soft windows" and "Setting"): at the upper edge, with `alpha(X, t) := X_s^+(t) - X`,
`Sigma_+(X, t, h) := pi (mu_0(alpha, t) + sum_{r=1}^K h^{2r} mu_{2r}(alpha, t))`, `mu_0` of `thm:smo-MPS`, `mu_{2r}` of `thm:smo-TPC`, given on `alpha < 0` by the linear extension of `thm:smo-WT2` (2) applied jointly in
`(alpha, t)`; `Sigma_{+,j} = 0` for odd `j`; `Sigma_{+,j} in C^{2M+1}(I_+ x [-t0, t0])` "because `X_s^+(t)` is `C^p` in `t` (a nondegenerate maximum)"; `I_+ = {|X - X_s^+| <= delta_0/4}` with `t0` so small that
`|X_s^+(t) - X_s^+| <= delta_0/16`; and `Proposition tha-W2 (3)` for `tilde J_h^{(t)}` is `eq:smo-BSr2` on `I_+`.

## What is here

* `softSigma C mu j X t`: the phase coefficient `Sigma_{+,j}(mu; X, t) = pi mu_{j/2}(X_s^+(mu, t) - X; mu, t)` for even `j`, `0` for odd `j` (`C.muS r (mu, t) alpha` is `mu_{2r}(alpha, t)` of the chart of the frozen family).
* `SoftPhaseInputs`: the paper-stated regularity facts that the soft `WindowPhase` needs and that the frozen `SoftEdgeChart` does not contain: `t0` small (`bandHi_close`), `X_s^+(t)` is `C^{2M+1}` in `t`
  (`bandHi_reg`), `mu_{2r}(alpha, t)` is jointly `C^{2M+1}` in `(alpha, t)` (`muS_reg`), and the uniform `C^{2M+1}` norm bound of the composed phase coefficients (`Sigma_bdd`: not derivable from the
  components without a quantitative chain rule; paper: "uniform in `mu`", chart norms uniform on a localising neighbourhood).  `Sigma_reg` of the window is *proved* from `bandHi_reg` and `muS_reg` by composition.
  The slope `partial_X Sigma_0 <= -pi cmu0` is *proved* from the chart's own `mu0_slope`; `Sigma_0 = S_0` on the band from the chart's `mu0_S0`.
* `SoftLabels`: the labelled rule (`PropThaW2` (3) for the frozen matrix at `t = h`, written as in `eq:smo-BSr2`, without the Step-0 hypothesis `Xs i <= X_s^+ + Cs0 h^2`, and with the weaker error `O(h^{M+1})`
  that `thm:smo-BSr` uses; for `M = 0` it is also what `PropThaW2` (4) gives).  It is the *input* from `PropThaW2` (L2.C7), not proved here.

## Differences from the paper

The window `I_+` is `{|X - X_s^+(mu, 0)| <= w}` with a half-width `w` and the closeness `rho` of `X_s^+(t)` to `X_s^+(0)` as fields (`w + rho <= delta_0`, paper: `w = delta_0/4`, `rho = delta_0/16`).
Only the upper edge; the lower edge is the same structure for `negFamily (frozenFamily T Kidx)` (`softLoL`, `eq:smo-BSr2` through `Sigma_- = pi L - Sigma~_+(-X, t, h)`), not formalised.

## Not formalised

The proofs of the fields (they are the content of `thm:smo-MPS/TPC/WT2` and the joint-regularity paragraph of `thm:smo-BSr`: Layer 4).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set FormalResearch.JacobiEigenvectors.Setting

/-- The phase coefficient `Sigma_{+,j}(mu; X, t)` at the upper soft edge (see the module docstring). -/
def softSigma {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
    {Lm : ℝ → ℝ} (C : SoftEdgeChart Fz P m q U V Lm) (μ : Par) (j : ℕ) (X t : ℝ) : ℝ :=
  if j % 2 = 0 then Real.pi * C.muS (j / 2) (μ, t) (Fz.bandHi (μ, t) - X) else 0

/-- **The soft phase inputs** (finding F-S6-6; see the module docstring). -/
structure SoftPhaseInputs {Par : Type*} [TopologicalSpace Par] (Fz : SymbolFamily (Par × ℝ)) (P : Set (Par × ℝ)) (K : Set Par) (t0 : ℝ) (M : ℕ)
    {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ} (C : SoftEdgeChart Fz P m q U V Lm) where
  /-- the half-width of the window `I_+ = {|X - X_s^+(mu, 0)| <= w}` and the closeness `rho` of the band end at `t` to that at `0` -/
  w : ℝ
  ρ : ℝ
  w_pos : 0 < w
  ρ_nonneg : 0 ≤ ρ
  /-- `|alpha| <= w + rho <= delta_0` on the window: the chart is valid there -/
  window_in_chart : w + ρ ≤ C.δ0
  /-- `t0` so small that `|X_s^+(t) - X_s^+(0)| <= rho` -/
  bandHi_close : ∀ μ ∈ K, ∀ t ∈ Icc (-t0) t0, |Fz.bandHi (μ, t) - Fz.bandHi (μ, 0)| ≤ ρ
  /-- `X_s^+(t)` is `C^{2M+1}` in `t` (a nondegenerate maximum) -/
  bandHi_reg : ∀ μ ∈ K, ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun t => Fz.bandHi (μ, t)) (Icc (-t0) t0)
  /-- `mu_{2r}(alpha, t)` is jointly `C^{2M+1}` in `(alpha, t)` on `[-(w+rho), w+rho] x [-t0, t0]` -/
  muS_reg : ∀ μ ∈ K, ∀ r ≤ M / 2, JetRegJ (fun α t => C.muS r (μ, t) α) (Icc (-(w + ρ)) (w + ρ)) t0 (2 * M + 1)
  /-- the uniform `C^{2M+1}` norm bound of the phase coefficients on the window times `[-t0, t0]` -/
  Sigma_bdd : ∃ Cb : ℝ, ∀ μ ∈ K, ∀ j ≤ M, ∀ i ≤ 2 * M + 1,
    ∀ p ∈ Icc (Fz.bandHi (μ, 0) - w) (Fz.bandHi (μ, 0) + w) ×ˢ Icc (-t0) t0,
      ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => softSigma C μ j q.1 q.2)
        (Icc (Fz.bandHi (μ, 0) - w) (Fz.bandHi (μ, 0) + w) ×ˢ Icc (-t0) t0) p‖ ≤ Cb

/-- **The labelled soft rule** (`PropThaW2` (3) for the frozen matrix at `t = h`, in the form of `eq:smo-BSr2`): for every eigenvalue `X_i` of `J_h(mu)` within `delta_0` of `X_s^+(mu, h)`,
`mu_0(alpha) + sum_{s=1}^{q/2} h^{2s} mu_{2s}(alpha) = (i + 1/2) h + O(h^{M+1})` with `alpha = X_s^+(mu, h) - X_i`, `i` the index from the top.  (`T.jacobiMat mu N` is the matrix of the frozen family at
`(mu, h)`, `Setting.frozenFamily_jacobiMat_at_step`.)  An input from `PropThaW2` (and Step 0), not proved here. -/
def SoftLabels {Par : Type*} [TopologicalSpace Par] (T : SymbolFamily Par) (Kidx : ℕ) (K : Set Par) (M : ℕ) {P : Set (Par × ℝ)} {m q : ℕ}
    {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ} (C : SoftEdgeChart (frozenFamily T Kidx) P m q U V Lm) : Prop :=
  ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, T.step N ≤ h0 →
    ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (T.jacobiMat μ N) Xs Um →
      ∀ i : Fin (N + 1), |Xs i - (frozenFamily T Kidx).bandHi (μ, T.step N)| ≤ C.δ0 →
        |(C.muS 0 (μ, T.step N) ((frozenFamily T Kidx).bandHi (μ, T.step N) - Xs i) +
            ∑ s ∈ Finset.Icc 1 (q / 2), T.step N ^ (2 * s) * C.muS s (μ, T.step N) ((frozenFamily T Kidx).bandHi (μ, T.step N) - Xs i))
          - ((i : ℕ) + 1 / 2) * T.step N| ≤ Cc * T.step N ^ (M + 1)

end FormalResearch.JacobiEigenvectors.Charts
