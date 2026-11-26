module

public import FormalResearch.SignUncertainty.HeadlineDefs

/-!
# Statement objects and input structure for `thm:ce-canonical-iff` (= `thm:intro-gap`)

Source: `CFT/sign_uncertainty/paper/ce_canonical_iff.tex` (statement), `ce_airy_lp.tex` (`Λ_M`, `λ`,
`thm:airy-square-attained`), `ce_shells.tex` (`u_LP`, `u_sh`, `eq:ce-witness`,
`lem:ce-terminal-deflation`), `ce_airy_lp_proofs.tex` (`lem:airy-active-height`, `lem:airy-square-bound`,
`lem:airy-node-square`, `thm:airy-node-sign`).

Concrete objects (no free data):

* `shellSites D`: the prescribed sites `t_1, …, t_{m-1}` (`D.S` minus the terminal node `t_m = D.tm`).
* `OneProfileStrictFeasible`, `uSh`: strict-site witnesses and the cutoff `u_sh` (`uLP` is in `Radii.lean`).
* `airyLambdaM s M` (`Λ_M(s)`), `airyLambda s` (`λ(s) = sup_M Λ_M(s)`): the constrained Airy-cardinal Rayleigh
  quotients of `ce_airy_lp.tex`, for a finite set `s` of sites, `k_n(u) = Ai(u)/(u - a_n)`.
* `IsHbZeroEnum P Q t`: `t j` is the paper's `t_{j+1}`, the strictly decreasing enumeration of the real zeros of
  `N = P Ai + Q Ai'` (this determines `t` uniquely; its existence is part of the paper's setup and is not
  formalised here, so satisfiability is unchecked). `hbNode t n = t_n` is the one-indexed form.
* `hbNodeWeight`, `hbNodeSquareBound`: `ω_n` and `τ_N` of `eq:hb-node-bound`.

`CeCanonicalInputs D t` is the input structure of the headline `thm_ce_canonical_iff` (in `Headlines.lean`); every
field is an open result of the paper and names its label.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.CohnElkies

/-- The prescribed sites `t_1, …, t_{m-1}` of the Hermite–Biehler configuration `D`. -/
noncomputable def shellSites (D : ShellHBData) : Finset ℝ := D.S.erase D.tm

/-- Strict-site witness at cutoff `u` (`ce_shells.tex`, after `eq:ce-witness`): a weak witness
(`OneProfileFeasibleWitness`) with `H(s) < 0` at every prescribed site. -/
def OneProfileStrictFeasible (D : ShellHBData) (u : ℝ) : Prop :=
  ∃ H : ℂ → ℂ, OneProfileFeasibleWitness D u H ∧ ∀ t ∈ D.S, t ≠ D.tm → (H (t : ℂ)).re < 0

/-- `u_sh`: the supremum (in `[-∞, ∞]`) of the cutoffs with a strict-site witness; `-∞` if there is none. -/
noncomputable def uSh (D : ShellHBData) : EReal :=
  ⨆ (u : ℝ) (_ : OneProfileStrictFeasible D u), (u : EReal)

/-- The Airy cardinal `k_n(u) = Ai(u)/(u - a_n)` (removable singularity at `a_n`), `a_n = airyZero n`. -/
noncomputable def airyCard (n : ℕ) (u : ℝ) : ℝ := dslope airyAi (airyZero n) u

/-- `q_c = ∑_{n ≤ M} c_n k_n` for `c : Fin M → ℝ` (`c_n` is the coefficient of `k_{n+1}`). -/
noncomputable def airyCardSum (M : ℕ) (c : Fin M → ℝ) (u : ℝ) : ℝ :=
  ∑ n : Fin M, c n * airyCard ((n : ℕ) + 1) u

/-- The Rayleigh quotient `∑ a_n c_n² / ∑ c_n²`. -/
noncomputable def airyRayleigh (M : ℕ) (c : Fin M → ℝ) : ℝ :=
  (∑ n : Fin M, airyZero ((n : ℕ) + 1) * c n ^ 2) / ∑ n : Fin M, c n ^ 2

/-- `Λ_M(s)` (`ce_airy_lp.tex`): the maximum of the Rayleigh quotient over `c ≠ 0` with `q_c(s_j) = 0`; it is a
maximum over a compact set when `M ≥ |s| + 1`, and `sSup` of the empty set (`0`) for smaller `M`. -/
noncomputable def airyLambdaM (s : Finset ℝ) (M : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ c : Fin M → ℝ, c ≠ 0 ∧ (∀ u ∈ s, airyCardSum M c u = 0) ∧ x = airyRayleigh M c}

/-- `λ(s) = sup_{M ≥ |s|+1} Λ_M(s)` (`thm:airy-square-attained`; the supremum is over `M ≥ |s| + 1` only). -/
noncomputable def airyLambda (s : Finset ℝ) : ℝ :=
  ⨆ M : ℕ, airyLambdaM s (M + s.card + 1)

/-- `IsHbZeroEnum P Q t`: `t : ℕ → ℝ` enumerates the real zeros of `N = P Ai + Q Ai'` strictly decreasingly,
`t j = t_{j+1}` of `eq:hb-profile`. -/
def IsHbZeroEnum (P Q : ℝ[X]) (t : ℕ → ℝ) : Prop :=
  StrictAnti t ∧ ∀ x : ℝ, at47_Nf P Q x = 0 ↔ ∃ n, t n = x

/-- `t_n` (one-indexed). -/
def hbNode (t : ℕ → ℝ) (n : ℕ) : ℝ := t (n - 1)

/-- The node weight `ω_n = D(t_n) / ∏_{k ∈ T ∖ {n}} (t_n - t_k)²` of `eq:hb-node-bound`
(`D = P(P+Q') - Q(P'+uQ)`; `n` one-indexed). -/
noncomputable def hbNodeWeight (P Q : ℝ[X]) (t : ℕ → ℝ) (T : Finset ℕ) (n : ℕ) : ℝ :=
  airyPQDr P Q (hbNode t n) / ∏ k ∈ T.erase n, (hbNode t n - hbNode t k) ^ 2

/-- `τ = ∑_{n ∈ T} ω_n t_n / ∑_{n ∈ T} ω_n`. -/
noncomputable def hbNodeSquareBound (P Q : ℝ[X]) (t : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  (∑ n ∈ T, hbNodeWeight P Q t T n * hbNode t n) / ∑ n ∈ T, hbNodeWeight P Q t T n

/-- `τ_N` of `eq:hb-node-bound`: `T_0 = {m, …, m + e}`, `e = ⌊m/2⌋`, `m = D.S.card`. -/
noncomputable def hbTauN (D : ShellHBData) (t : ℕ → ℝ) : ℝ :=
  hbNodeSquareBound D.P D.Q t (Finset.Icc D.S.card (D.S.card + D.S.card / 2))

/-- The Laplace transform `L_F(y) = ∫ F(u) e^{yu} du` (`eq:ce-laplace-def`, without the cubic twist). -/
noncomputable def laplaceL (F : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, F u * Real.exp (y * u)

/-- Offsets `r` of the shell class are `o(c^{1/3})`: `r t d / (d/2)^{1/3} → 0` for every site `t`. -/
def ShellOffsetsSmall (r : ℝ → ℕ → ℝ) : Prop :=
  ∀ s : ℝ, Tendsto (fun d : ℕ => r s d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0)

/-- `ρ_d = ((R_d^{CE})²/2 - d/(2π²)) / (d/2)^{1/3}` with `R_d^{CE} = inf (ceShellRadiusSet D r d)`, and `ρ_d = +∞`
when the set is empty (the paper's convention `R_d^{CE} = +∞`). -/
noncomputable def ceShellRho (D : ShellHBData) (r : ℝ → ℕ → ℝ) (d : ℕ) : EReal := by
  classical
  exact if (ceShellRadiusSet D r d).Nonempty then
    ((shellNormRadius d (sInf (ceShellRadiusSet D r d)) : ℝ) : EReal) else ⊤

/-- `thm:ce-canonical-iff` (3)(i): `ℒ_y(-G_N) ≥ 0` for every `y > 0` (tangencies allowed). -/
def LaplaceNonneg (D : ShellHBData) : Prop :=
  ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y

/-- `thm:ce-canonical-iff` (3)(ii): for every offset bound `R_off ≥ 0` and prescribed shells with offsets
`|r_{j,c}| ≤ R_off`, `(R_d^{CE})²/2 = d/(2π²) - (t_m/β₁)(d/2)^{1/3} + O(1)`, where `R_d^{CE}` is the infimum of the
radii of the shell class (the class is nonempty for large `d`, so that `R_d^{CE}` is finite). -/
def ShellBoundedRemainder (D : ShellHBData) : Prop :=
  ∀ R_off : ℝ, 0 ≤ R_off → ∀ r : ℝ → ℕ → ℝ, (∀ t d', |r t d'| ≤ R_off) →
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → (ceShellRadiusSet D r d).Nonempty ∧
      |(sInf (ceShellRadiusSet D r d)) ^ 2 / 2 -
        ((d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C

/-- `thm:ce-canonical-iff` (3)(iii): `lim ρ_d = -t_m/β₁` for all prescribed shells with offsets `o(c^{1/3})`. -/
def ShellLimit (D : ShellHBData) : Prop :=
  ∀ r : ℝ → ℕ → ℝ, ShellOffsetsSmall r →
    Tendsto (ceShellRho D r) atTop (𝓝 ((-(D.tm / hankelBeta1) : ℝ) : EReal))

/-- `thm:ce-canonical-iff` (3)(iv): `liminf ρ_d = -t_m/β₁` for some prescribed shells with offsets `o(c^{1/3})`. -/
def ShellLiminf (D : ShellHBData) : Prop :=
  ∃ r : ℝ → ℕ → ℝ, ShellOffsetsSmall r ∧
    liminf (ceShellRho D r) atTop = ((-(D.tm / hankelBeta1) : ℝ) : EReal)

/-! ### Input structure -/

/-- `thm:airy-square-attained` (`ce_airy_lp.tex`), the parts used by `thm:ce-canonical-iff`, for the sites
`s = t_1, …, t_{m-1}` of `D`: (1) the sequence `Λ_M(s)` is bounded above (`λ(s)` is finite), and (3) for a maximizing
cardinal series `q` the function `H_λ = (u - λ) q²` is a weak witness at `λ(s)` with `∫ H_λ = 0`, vanishing at every
site (double zero, `q(s_j) = 0`) and `L_{H_λ}(y) > 0` for all `y > 0`. The maximum formula, the Lipschitz and
rate statements and the dual representation `eq:airy-square-rep` are not restated. -/
structure AirySquareAttained (D : ShellHBData) : Prop where
  bddAbove : BddAbove (Set.range fun M : ℕ => airyLambdaM (shellSites D) (M + (shellSites D).card + 1))
  witness : ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ (∀ x : ℝ, (q (x : ℂ)).im = 0) ∧ (∃ z, q z ≠ 0) ∧
    (∀ s ∈ shellSites D, q (s : ℂ) = 0) ∧
    OneProfileFeasibleWitness D (airyLambda (shellSites D))
      (fun z => (z - (airyLambda (shellSites D) : ℂ)) * q z ^ 2) ∧
    (∫ u : ℝ, ((u - (airyLambda (shellSites D) : ℂ)) * q (u : ℂ) ^ 2).re) = 0 ∧
    ∀ y : ℝ, 0 < y →
      0 < laplaceL (fun u => ((u - (airyLambda (shellSites D) : ℂ)) * q (u : ℂ) ^ 2).re) y

/-- `lem:airy-active-height` (`ce_airy_lp_proofs.tex`, strictification and deflation), parts (1)–(4), for the
configuration `D`; "optimizer" means a weak witness `H` at `b = u_LP` (`uLP D = b` real). Part (1) is stated in the
form "whenever `L_H(y) > 0` for all `y > 0`" (any buffer of `lem:airy-shell-buffer` then works). In (3) and (4)
the quotient is required to be integrable (it is in `𝒢` for an optimizer; for a non-integrable quotient the
Lean integral would be the junk value `0`). -/
structure AiryActiveHeight (D : ShellHBData) : Prop where
  /-- (1) a weak witness at `v < t_m` with `L_H(y) > 0` for all `y > 0` gives `u_sh > v`. -/
  strictify : ∀ v : ℝ, v < D.tm → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D v H →
    (∀ y : ℝ, 0 < y → 0 < laplaceL (fun u => (H (u : ℂ)).re) y) → (v : EReal) < uSh D
  /-- (2) if `u_LP < t_m` there is a common positive height `y_*` at which every optimizer has a Laplace
  zero, of even order; in particular `L_H(y_*) = L_H'(y_*) = 0`. -/
  laplace_zero : uLP D < (D.tm : EReal) → ∃ y : ℝ, 0 < y ∧ ∀ b : ℝ, uLP D = (b : EReal) →
    ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
      AnalyticAt ℝ (laplaceL (fun u => (H (u : ℂ)).re)) y ∧
      Even (analyticOrderNatAt (laplaceL (fun u => (H (u : ℂ)).re)) y) ∧
      laplaceL (fun u => (H (u : ℂ)).re) y = 0 ∧
      deriv (laplaceL (fun u => (H (u : ℂ)).re)) y = 0
  /-- (3) an optimizer with `∫ H/(u - b) ≥ 0` gives `u_sh = b`. -/
  quotient_mass : ∀ b : ℝ, uLP D = (b : EReal) → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
    MeasureTheory.Integrable (fun u : ℝ => (H (u : ℂ)).re / (u - b)) →
    0 ≤ ∫ u : ℝ, (H (u : ℂ)).re / (u - b) → uSh D = (b : EReal)
  /-- (4) if `b < t_m`, at every real zero `z > b` of an optimizer that is not a site, or is a site with
  `H'(z) ≤ 0`, the quotient `H/(u - z)` has strictly negative integral. -/
  deflation : uLP D < (D.tm : EReal) → ∀ b : ℝ, uLP D = (b : EReal) → ∀ H : ℂ → ℂ,
    OneProfileFeasibleWitness D b H → ∀ z : ℝ, b < z → (H (z : ℂ)).re = 0 →
      (z ∉ shellSites D ∨ (deriv H (z : ℂ)).re ≤ 0) →
      ∫ u : ℝ, (H (u : ℂ)).re / (u - z) < 0

/-- Inputs of `thm:ce-canonical-iff` for the Hermite–Biehler configuration `D` with zero enumeration `t`
(`m = D.S.card`). Each field is an open result of the paper (the label is in its docstring). -/
structure CeCanonicalInputs (D : ShellHBData) (t : ℕ → ℝ) : Prop where
  /-- `thm:ce-shell-reduction` (open for `m ≥ 2`, M8; it follows from the lower half of `u1cl:multilevel`,
  `thm:intro-hb`): bounded offsets give `R²/2 ≥ d/(2π²) - (t_m/β₁)(d/2)^{1/3} - O(1)`. -/
  shell_reduction : ShellReduction D
  /-- `thm:ce-hb-lift` (with `thm:ce-hb-lift-tangency`), weak Laplace positivity (M6, M8). -/
  ce_hb_lift : CeHbLift D
  /-- `thm:ce-airy-transfer` (1), upper bound (via `thm:ce-shifted-lift` and `thm:al-rational-density`), for
  the shell class of `D` with offsets `o(c^{1/3})`: for each `v < u_sh` and all large `d` there is an admissible
  pair, strictly negative on the shells and on `[c/π² - (v/β₁) c^{1/3}, ∞)` (stated in the weaker form
  `R²/2 ≤ d/(2π²) - (v/β₁)(d/2)^{1/3}` for some radius `R` of the shell class). -/
  ce_airy_transfer_upper : ∀ v : ℝ, (v : EReal) < uSh D → ∀ r : ℝ → ℕ → ℝ,
    ShellOffsetsSmall r →
      ∀ᶠ d : ℕ in atTop, ∃ R ∈ ceShellRadiusSet D r d,
        R ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) - (v / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)
  /-- `thm:airy-square-attained` (M9). -/
  airy_square_attained : AirySquareAttained D
  /-- `lem:airy-square-bound` (M9): for `m ≥ 2`, `Λ_m > a_m` (top `m - 1` sites). -/
  airy_square_bound : 2 ≤ D.S.card → airyZero D.S.card < airyLambdaM (shellSites D) D.S.card
  /-- `lem:airy-node-square` (M9): for `m ≥ 2`, the fixed node-square bound `λ > τ_N > t_{m+e}`. -/
  airy_node_square : 2 ≤ D.S.card →
    hbTauN D t < airyLambda (shellSites D) ∧ hbNode t (D.S.card + D.S.card / 2) < hbTauN D t
  /-- `lem:airy-active-height` (M9). -/
  active_height : AiryActiveHeight D
  /-- `thm:airy-node-sign` (M9): if `b = u_LP < t_m` and an optimizer `H_*` has no zeros `t' < t'' < t'''` of `N`
  in `(b, t_m]` with `H_*(t') > 0`, `H_*(t'') < 0`, `H_*(t''') > 0`, then `u_sh = u_LP`; in particular
  `u_sh = u_LP` whenever `t_{m+2} ≤ u_LP < t_m`. (The more general cumulative node-sum criterion is not restated.) -/
  node_sign :
    (∀ b : ℝ, uLP D = (b : EReal) → b < D.tm → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
      (¬ ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ b < t₁ ∧ t₃ ≤ D.tm ∧ at47_Nf D.P D.Q t₁ = 0 ∧
        at47_Nf D.P D.Q t₂ = 0 ∧ at47_Nf D.P D.Q t₃ = 0 ∧ 0 < (H (t₁ : ℂ)).re ∧
        (H (t₂ : ℂ)).re < 0 ∧ 0 < (H (t₃ : ℂ)).re) → uSh D = (b : EReal)) ∧
    (∀ b : ℝ, uLP D = (b : EReal) → hbNode t (D.S.card + 2) ≤ b → b < D.tm → uSh D = (b : EReal))
  /-- `lem:ce-terminal-deflation` (M9, `ce_shells.tex`): for `m` odd with `ℒ_y(-G_N) ≥ 0` for all `y > 0`, the
  terminal cardinal `H_N = -G_N/(u - t_m)` has `I_N = ∫ H_N = D(t_m)/∏_{j<m}(t_j - t_m) > 0` (the node weight
  numerator `D(t_m)` is positive for Hermite–Biehler data, `gt:1.0pp`). -/
  terminal_deflation : (∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) →
    MeasureTheory.Integrable (fun u : ℝ => (-(D.G (u : ℂ)).re) / (u - D.tm)) ∧
    (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) =
      airyPQDr D.P D.Q D.tm / ∏ s ∈ shellSites D, (s - D.tm) ∧
    0 < ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)

end FormalResearch.SignUncertainty
