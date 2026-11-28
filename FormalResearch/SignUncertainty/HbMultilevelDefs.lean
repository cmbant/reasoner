module

public import FormalResearch.SignUncertainty.HeadlineDefs

/-!
# Statement objects and target predicates for `u1cl:multilevel` (= `thm:intro-hb`, `thm:hb-thresholds`)

Source: `CFT/sign_uncertainty/paper/u1c_o1_lower.tex` (Theorem L.2), `u1c_o1_upper.tex` (Theorem O.9'),
`general_theorems.tex` (Propositions 7.9a, 7.9b), and the introduction paragraph "Fixed levels and the
Cohn--Elkies obstruction" of `sign_uncertainty_core.tex`.

Concrete objects (no free data): the prescribed Hankel sites `T_{j,c} = c/π² - (t_j/β₁) c^{1/3} + r_{j,c}`
(`hankelSites D r c`, `j < m`, offsets `r t c` bounded by `R_off`), the class `IsHankelPrescribed` (feasible at `T`
with `f(T_{j,c}) ≥ 0`), `hankelTOpt` (`T^{opt,ε}_{m,c}`), `hankelTOpt0` (the same with `f(0) = 0` imposed),
`hbModel D c = c/π² - (t_m/β₁) c^{1/3}`, and the proved target predicates `HbMultilevelLower`, `HbConstruction`,
`HankelAttainment`, `HankelExactOrigin` used by `thm_intro_hb` (in `Headlines.lean`).
-/

@[expose] public section

open scoped Real Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The level `T_{j,c} = c/π² - (t/β₁) c^{1/3} + o` for the site `t = t_j` and offset `o = r_{j,c}`. -/
noncomputable def hankelLevel (t c o : ℝ) : ℝ := c / π ^ 2 - (t / hankelBeta1) * c ^ (1 / 3 : ℝ) + o

/-- The prescribed sites `T_{1,c}, …, T_{m-1,c}` for the offsets `r` (`r t c` is the offset of the site `t`). -/
noncomputable def hankelSites (D : ShellHBData) (r : ℝ → ℝ → ℝ) (c : ℝ) : Finset ℝ :=
  (D.S.erase D.tm).image fun t => hankelLevel t c (r t c)

/-- `f ∈ 𝒜_c^ε` feasible at `T` (`IsHankelFeasible`) with `f(T_{j,c}) ≥ 0` for `1 ≤ j < m`. -/
structure IsHankelPrescribed (D : ShellHBData) (r : ℝ → ℝ → ℝ) (c ε T : ℝ) (f : ℝ → ℝ) : Prop
    extends IsHankelFeasible c ε T f where
  sites_nonneg : ∀ s ∈ hankelSites D r c, 0 ≤ f s

/-- `T^{opt,ε}_{m,c}`: the infimum of the thresholds of `IsHankelPrescribed`. -/
noncomputable def hankelTOpt (D : ShellHBData) (r : ℝ → ℝ → ℝ) (ε c : ℝ) : ℝ :=
  sInf {T : ℝ | ∃ f, IsHankelPrescribed D r c ε T f}

/-- `T^{opt,ε}_{m,c}` with the extra condition `f(0) = 0`. -/
noncomputable def hankelTOpt0 (D : ShellHBData) (r : ℝ → ℝ → ℝ) (ε c : ℝ) : ℝ :=
  sInf {T : ℝ | ∃ f, IsHankelPrescribed D r c ε T f ∧ f 0 = 0}

/-- The model threshold `c/π² - (t_m/β₁) c^{1/3}`. -/
noncomputable def hbModel (D : ShellHBData) (c : ℝ) : ℝ :=
  c / π ^ 2 - (D.tm / hankelBeta1) * c ^ (1 / 3 : ℝ)

/-- A minimizer of the Hankel problem with nonnegative sign constraints on the finite set `sites`: `f` is feasible
at `T`, `f ≥ 0` on `sites`, and `T` is below every feasible threshold with these constraints. -/
structure IsHankelSiteMinimizer (c ε : ℝ) (sites : Finset ℝ) (T : ℝ) (f : ℝ → ℝ) : Prop where
  feasible : IsHankelFeasible c ε T f
  sites_nonneg : ∀ s ∈ sites, 0 ≤ f s
  least : ∀ (T' : ℝ) (f' : ℝ → ℝ), IsHankelFeasible c ε T' f' → (∀ s ∈ sites, 0 ≤ f' s) → T ≤ T'

/-- Lower half of `u1cl:multilevel` (Theorem L.2): for `R_off ≥ 0` there are `C`, `c₀` such that for real
`c ≥ c₀`, either eigenvalue and all offsets `|r_{j,c}| ≤ R_off`, every threshold of `IsHankelPrescribed` is at least
`c/π² - (t_m/β₁) c^{1/3} - C`. -/
def HbMultilevelLower (D : ShellHBData) : Prop :=
  ∀ R_off : ℝ, 0 ≤ R_off → ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ r : ℝ → ℝ → ℝ, (∀ t c', |r t c'| ≤ R_off) →
      ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelPrescribed D r c ε T f → hbModel D c - C ≤ T

/-- Theorem O.9' (`u1co:O9p`, `thm:hb-construction`) for `D`: for every `R_off ≥ 0` and integer `κ ≥ 4` (the paper's
`m ≥ 4`, a smoothness parameter of the construction) there are `K > 0` and `c₁ ≥ 2` such that for every real
`c ≥ c₁` and sign `σ` there is `f_c ∈ 𝒜_c^σ` with (1) `σ f_c(0) < 0`; (2) `f_c > 0` on
`[T_j - R_off, T_j + R_off]`, `T_j = c/π² - (t_j/β₁) c^{1/3}`, `1 ≤ j < m_0`; (3) `f_c > 0` on
`[c/π² + (|t_{m_0}|/β₁) c^{1/3} + K, ∞)`. (The paper's constants `K`, `c_{m_0}` depend on `κ` and `R_off`; they are
stated uniform in `σ`, which loses nothing: take the maximum over the two signs.) -/
def HbConstruction (D : ShellHBData) : Prop :=
  ∀ κ : ℕ, 4 ≤ κ → ∀ R_off : ℝ, 0 ≤ R_off → ∃ K c₁ : ℝ, 0 < K ∧ 2 ≤ c₁ ∧
    ∀ c : ℝ, c₁ ≤ c → ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ f : ℝ → ℝ, IsHankelEigenfn c σ f ∧ σ * f 0 < 0 ∧
      (∀ t ∈ D.S, t ≠ D.tm → ∀ x : ℝ, |x - hankelLevel t c 0| ≤ R_off → 0 < f x) ∧
      (∀ x : ℝ, c / π ^ 2 + (|D.tm| / hankelBeta1) * c ^ (1 / 3 : ℝ) + K ≤ x → 0 < f x)

/-- Proposition 7.9a (3) (`gt:7.9a`, with `lem:finite-hankel-compactness`): for every real `c > 1/2`, either sign,
and every finite set `sites` of positive sites, if the feasible class with the nonnegativity constraints on `sites`
is nonempty then the threshold is attained. -/
def HankelAttainment : Prop :=
  ∀ c : ℝ, 1 / 2 < c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ sites : Finset ℝ, (∀ s ∈ sites, 0 < s) →
    (∃ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f ∧ ∀ s ∈ sites, 0 ≤ f s) →
      ∃ (T : ℝ) (f : ℝ → ℝ), IsHankelSiteMinimizer c ε sites T f

/-- Proposition 7.9b (`gt:7.9b`): under the same hypotheses every minimizer satisfies `f(0) = 0` (this is the
paper's "relaxed threshold equals the infimum with `f(0) = 0`", in the form used here; the clause `f(T) = 0` and the
precompactness of minimizing sequences are not restated). -/
def HankelExactOrigin : Prop :=
  ∀ c : ℝ, 1 / 2 < c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ sites : Finset ℝ, (∀ s ∈ sites, 0 < s) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelSiteMinimizer c ε sites T f → f 0 = 0

end FormalResearch.SignUncertainty
