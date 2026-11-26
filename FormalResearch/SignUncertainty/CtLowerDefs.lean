module

public import FormalResearch.SignUncertainty.Radii
public import FormalResearch.SignUncertainty.CtOuter
public import FormalResearch.SignUncertainty.CtCfuData
public import FormalResearch.SignUncertainty.HankelTransportInt
public import FormalResearch.SignUncertainty.RadialRigidity
public import FormalResearch.SignUncertainty.HankelEdgePhase
public import FormalResearch.SignUncertainty.HankelThresholds

/-!
# Objects of the proof of `thm:ct-lower` (F1)

`constant_terms_lower.tex`, "Proof of the lower bound in `thm:ct-lower`(i)": the five-term expression `Δ₅^ε(c)`
(`ctDelta5`) and the concrete objects of the proof by contradiction at the first Airy node: `ctPsi` (the CFU phase shift
`ψ_ε`), `ctUhat` / `ctPhi` (`û` and `φ_c = û⁻¹`), `ctUtilde` (`ũ(T/c)`, the inverse of the Lean Langer chart `hankelXi`),
`ctGap` (`ũ₁ - φ_c(a₁)`), `ctFc`, `ctH`, `ctBudget` (`P_R(H) + g_vac/2π`).  Split from `CtLower` so that the proved
inputs (`CtLowerChartGap`) can import the definitions.  No result here; see `CtLower` for the status of `thm:ct-lower`.
-/

@[expose] public section

open scoped Real
open Filter Topology

namespace FormalResearch.SignUncertainty

/-- `κ_ε = θ₁^ε / π²`. -/
noncomputable def ctKappa (ε : ℝ) : ℝ := CtOuter.ctTheta1 ε / π ^ 2

/-- `c₁^{Langer} = 9π²A²/25` (`constant_terms_five.tex`). -/
noncomputable def ctC1Langer : ℝ := 9 * π ^ 2 / 25 * airyOrderCoeff ^ 2

/-- `d₂^{*,ε} = A(θ₁^ε + 12θ₃^ε/π²)`. -/
noncomputable def ctD2star (ε : ℝ) : ℝ := airyOrderCoeff * (CtOuter.ctTheta1 ε + 12 / π ^ 2 * CtOuter.ctTheta3 ε)

/-- The five-term expression `Δ₅^ε(c) = c/π² + A c^{1/3} + κ_ε + c₁^{Langer} c^{-1/3} + d₂^{*,ε} c^{-2/3}`. -/
noncomputable def ctDelta5 (ε c : ℝ) : ℝ :=
  c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) + ctKappa ε + ctC1Langer * c ^ (-(1 / 3) : ℝ) +
    ctD2star ε * c ^ (-(2 / 3) : ℝ)

/-! ### The objects of the proof by contradiction -/

open FormalResearch.CohnElkies FormalResearch.Special in
/-- `τ₀(a)` for `a < 0`: a positive solution of `Φ(τ₀) = (2/3)(-a)^{3/2}` (`edgePhi (hankelEdgeM τ) τ`); unique for
small `|a|` (`cfu_psi_langer`), an arbitrary point where there is none. -/
noncomputable def ctTau0 (a : ℝ) : ℝ :=
  Classical.epsilon fun τ : ℝ => 0 < τ ∧ edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2)

/-- The CFU phase shift `ψ_ε(a) = θ_ε(τ₀(a)) / √(-a)` (`ct:psi-def`), for `a < 0`. -/
noncomputable def ctPsi (ε a : ℝ) : ℝ := CtOuter.outerTheta ε (ctTau0 a) / Real.sqrt (-a)

/-- `û(ũ) = ũ + 2^{-2/3} c^{-1/3} ψ_ε(2^{2/3} c^{-2/3} ũ)` (`constant_terms_lower.tex`, after `ct:psi-coeffs`), for `ũ < 0`. -/
noncomputable def ctUhat (ε c u : ℝ) : ℝ :=
  u + (2 : ℝ) ^ (-(2 / 3) : ℝ) * c ^ (-(1 / 3) : ℝ) *
    ctPsi ε ((2 : ℝ) ^ ((2 : ℝ) / 3) * c ^ (-(2 / 3) : ℝ) * u)

/-- `φ_c = û⁻¹` on the Langer disc `|u| ≤ langerRadius c` (the TeX uses `|u| ≤ R_max = 4c₁²c^{2/3}` inside it; `û` is
strictly increasing there, part of `ct:cfu`; `invFunOn` is arbitrary where `û` is not bijective onto the point). -/
noncomputable def ctPhi (ε c u : ℝ) : ℝ :=
  Function.invFunOn (ctUhat ε c) (Set.Icc (-(langerRadius c)) (langerRadius c)) u

/-- `ũ₁ = ũ(T/c)`: the Langer-chart preimage of `T/c`, taken in `[-3, 0]` (the range of `u_T` in
`hankel_quantC1_of_feasible`, `hankelBoot_uT_range`); the inverse of `hankelXi`. -/
noncomputable def ctUtilde (c T : ℝ) : ℝ := Function.invFunOn (hankelXi c) (Set.Icc (-3) 0) (T / c)

/-- **`ũ₁ - φ_c(a₁)`**, the gap of `ct:sec4` (`a₁ = airyZero 1`; `φ_c(a₁)` is taken in `[-3, -2]`). -/
noncomputable def ctGap (ε c T : ℝ) : ℝ :=
  ctUtilde c T - Function.invFunOn (ctUhat ε c) (Set.Icc (-3) (-2)) (FormalResearch.Special.airyZero 1)

/-- `f_c(u) = Ψ̃(φ_c(u)) φ_c'(u)` (`ct:dyadic`), with `Ψ̃ = hankelPsi c f` (real on `ℝ`). -/
noncomputable def ctFc (ε c : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  hankelPsiR c f (ctPhi ε c u) * deriv (ctPhi ε c) u

/-- `W₆(u) = (1 - (u/R)^{12})²` and `H = W₆ f_c`. -/
noncomputable def ctH (R ε c : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := (1 - (u / R) ^ 12) ^ 2 * ctFc ε c f u

/-- **`P_R(H) + g_vac/(2π)`** (`ap:thmD`, `ct:gvac-def`): the sum of `H(a_n)/Ai'(a_n)²` over the Airy zeros `a_n ∈ (-R, 0)`
plus `-ε f(0)` (`g_vac = -2π ε f(0)`). -/
noncomputable def ctBudget (R ε c : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∑' n : ℕ, if -R < FormalResearch.Special.airyZero (n + 1) then
      ctH R ε c f (FormalResearch.Special.airyZero (n + 1)) /
        (deriv FormalResearch.Special.airyAi (FormalResearch.Special.airyZero (n + 1))) ^ 2
    else 0) - ε * f 0

end FormalResearch.SignUncertainty
