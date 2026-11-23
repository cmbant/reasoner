module

public import FormalResearch.SignUncertainty.SignSeparation
public import FormalResearch.SignUncertainty.ShellLaplaceBase
public import FormalResearch.CohnElkies.CohnElkiesRadius

/-!
# Concrete radii for the Fourier sign-uncertainty and Cohn–Elkies problems (Paper I)

Source: `CFT/sign_uncertainty/paper/sign_uncertainty_core.tex` (introduction) and
`general_theorems.tex`, `ce_shells.tex`.

All objects are defined on `EuclideanSpace ℝ (Fin d)` with Mathlib's Fourier transform
`𝓕 f y = ∫ e^{-2πi⟪x,y⟫} f x dx` (the kernel of the paper), or on the half line with the real-order
Bessel kernel.

* `IsSignWitness ε d R f`, `aSignPos d`, `aSignNeg d`: the sign-uncertainty radii `A_sign^±(d)`.
  `f` is a real integrable function with `f̂ = ε f`, not identically zero, and `f ≥ 0` for `‖x‖ ≥ R`;
  the condition at zero is `f(0) ≤ 0` for `ε = 1` and `f(0) = 0` for `ε = -1`
  (`sign_uncertainty_core.tex`, introduction). `A_sign^±(d)` is the infimum of such `R`.
* `FormalResearch.CohnElkies.optimalL1CERadius` is `r_CE(d)` (normalised continuous `L¹` pairs,
  `h(0) = ĥ(0)`), reused unchanged.
* `IsShellAdmissible D r d R h`, `ceShellRadiusSet D r d`: the prescribed-shell Cohn–Elkies class of
  `thm:intro-gap`: radial normalised continuous integrable pairs with `h ≤ 0` at the shells
  `|x|²/2 = shellSite t (r t) d` (`t ∈ D.S`, `t ≠ D.tm`) and `h ≤ 0` for `‖x‖ ≥ R`.
  `R_d^{CE}` is the infimum of `ceShellRadiusSet D r d` (`+∞` if it is empty); statements below
  quantify over the members of the set instead, which is the same thing for lower bounds.
* `hankelPhi`, `IsHankelFeasible`, `hankelT`, `hankelT0`: the Hankel problem of
  `fourier_mellin.tex` with the Bessel kernel `K^{(c)}(Δ,s) = Γ(c)(2π√(Δs))^{1-c} J_{c-1}(4π√(Δs))`
  written through Poisson's integral for `J_{c-1}` (valid for `c > 1/2`).
  `hankelT ε c` is `T_c^ε` and `hankelT0 c` is `T_c^{-1}` with the extra condition `f(0) = 0`.
* The bridge `HankelKernelData.threshold_eq`: for a `HankelKernelData c` whose kernel is `hankelPhi c`
  the earlier abstract definitions (`hankelThreshold`, `hankelThresholdZeroOrigin`) agree with the
  concrete ones, so the existing theorems (`active_origin_constraint`, `sign_separation_*`) apply.

Nothing here is a theorem about the radii; see `Headlines.lean`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial FourierTransform RealInnerProductSpace

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.CohnElkies

/-! ### Constants -/

/-- `A = |a₁| / β₁` of `eq:intro-constants`: `a₁` is the largest zero of the Airy function. -/
noncomputable def airyOrderCoeff : ℝ := |airyZero 1| / hankelBeta1

lemma airyOrderCoeff_pos : 0 < airyOrderCoeff := by
  unfold airyOrderCoeff
  exact div_pos (abs_pos.mpr (airyZero_neg 1).ne) hankelBeta1_pos

/-- The leading two terms `d/(2π²) + A (d/2)^{1/3}` of `thm:intro-radii`. -/
noncomputable def airyOrderModel (d : ℕ) : ℝ :=
  (d : ℝ) / (2 * π ^ 2) + airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)

/-! ### Fourier sign-uncertainty radii on `ℝ^d` -/

/-- A sign-uncertainty competitor of radius `R` for the eigenvalue `ε = ±1`: a real integrable `f` on
`ℝ^d`, not identically zero, with `f̂ = ε f` everywhere and `f ≥ 0` on `‖x‖ ≥ R`. The condition at the
origin is not part of this structure (it differs for the two signs). -/
structure IsSignWitness (ε : ℝ) (d : ℕ) (R : ℝ) (f : Euc d → ℝ) : Prop where
  integrable : Integrable f
  fourier_eq : ∀ y : Euc d, 𝓕 (fun x : Euc d => (f x : ℂ)) y = (ε : ℂ) * (f y : ℂ)
  nonzero : ∃ x : Euc d, f x ≠ 0
  tail_nonneg : ∀ x : Euc d, R ≤ ‖x‖ → 0 ≤ f x

/-- `A_sign^+(d)`: infimum of the radii of self-dual competitors with `f(0) ≤ 0`. -/
noncomputable def aSignPos (d : ℕ) : ℝ :=
  sInf {R : ℝ | ∃ f : Euc d → ℝ, IsSignWitness 1 d R f ∧ f 0 ≤ 0}

/-- `A_sign^-(d)`: infimum of the radii of anti-self-dual competitors with `f(0) = 0`. -/
noncomputable def aSignNeg (d : ℕ) : ℝ :=
  sInf {R : ℝ | ∃ f : Euc d → ℝ, IsSignWitness (-1) d R f ∧ f 0 = 0}

/-! ### The prescribed-shell Cohn–Elkies class -/

/-- Shell position in the radial coordinate `Δ = |x|²/2`, dimension `d = 2c`:
`c/π² - (t/β₁) c^{1/3} + r_{d}`. -/
noncomputable def shellSite (t : ℝ) (r : ℕ → ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) / (2 * π ^ 2) - (t / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + r d

/-- A radial normalised continuous integrable Cohn–Elkies pair (`h(0) = ĥ(0) > 0`, `ĥ ≥ 0`, `h ≤ 0` on
`‖x‖ ≥ R`) with `h ≤ 0` at the first `m - 1` shells of the Hermite–Biehler configuration `D`:
the shells are `|x|²/2 = shellSite t (r t) d` for the sites `t ∈ D.S`, `t ≠ D.tm` (here
`D.S = {t_1, …, t_m}` and `D.tm = t_m`), with offsets `r t d`. -/
structure IsShellAdmissible (D : ShellHBData) (r : ℝ → ℕ → ℝ) (d : ℕ) (R : ℝ) (h : Euc d → ℝ) : Prop
    extends IsContinuousL1CEAdmissible d R h where
  radial : ∀ x y : Euc d, ‖x‖ = ‖y‖ → h x = h y
  shells : ∀ t ∈ D.S, t ≠ D.tm → ∀ x : Euc d, ‖x‖ ^ 2 / 2 = shellSite t (r t) d → h x ≤ 0

/-- The admissible radii of the prescribed-shell problem; `R_d^{CE} = inf (ceShellRadiusSet D r d)`. -/
def ceShellRadiusSet (D : ShellHBData) (r : ℝ → ℕ → ℝ) (d : ℕ) : Set ℝ :=
  {R : ℝ | ∃ h : Euc d → ℝ, IsShellAdmissible D r d R h}

/-- The normalised radius `((R)²/2 - d/(2π²)) / (d/2)^{1/3}` whose `liminf` is bounded in
`thm:intro-gap` (ii). -/
noncomputable def shellNormRadius (d : ℕ) (R : ℝ) : ℝ :=
  (R ^ 2 / 2 - (d : ℝ) / (2 * π ^ 2)) / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)

/-- `u_LP`: the supremum (in `[-∞, t_m]`) of the thresholds `v` at which the one-profile problem of
`prop:ce-one-profile` is feasible: some nonzero `H ∈ 𝒢` with `H(t_j) ≤ 0` (`j < m`), `H ≤ 0` on
`(-∞, v]` and `∫ H e^{yu} ≥ 0` for all `y ≥ 0` (`OneProfileFeasible`). `-∞` if there is none. -/
noncomputable def uLP (D : ShellHBData) : EReal :=
  ⨆ (u : ℝ) (_ : OneProfileFeasible D u), (u : EReal)

/-! ### The Hankel problem with the real-order Bessel kernel -/

/-- The normalised Bessel kernel `K^{(c)}(Δ, s) = φ_c(Δ s)` through Poisson's integral
`J_ν(x) = (x/2)^ν (√π Γ(ν + 1/2))⁻¹ ∫_{-1}^1 (1-t²)^{ν-1/2} cos(xt) dt` with `ν = c - 1`
(`c > 1/2`; the paper uses `c ≥ 1`):
`φ_c(w) = Γ(c) (√π Γ(c - 1/2))⁻¹ ∫_{-1}^1 (1-t²)^{c-3/2} cos(4π √w t) dt`. -/
noncomputable def hankelPhi (c w : ℝ) : ℝ :=
  Real.Gamma c / (√π * Real.Gamma (c - 1 / 2)) *
    ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (c - 3 / 2) * Real.cos (4 * π * √w * t)

/-- The Hankel transform of `eq:hankel` with the Bessel kernel, `(T_c f)(Δ) = ∫ f ρ₀ φ_c(Δ s) ds`. -/
noncomputable def besselTransform (c : ℝ) (f : ℝ → ℝ) (Δ : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s * hankelPhi c (Δ * s)

/-- `f ∈ 𝒜_c^ε`: continuous, `M[f] < ∞` and `f̂ = ε f` for the Bessel kernel. -/
structure IsHankelEigenfn (c ε : ℝ) (f : ℝ → ℝ) : Prop where
  cont : ContinuousOn f (Ici 0)
  int : IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0)
  eigen : ∀ Δ ∈ Ici (0 : ℝ), besselTransform c f Δ = ε * f Δ

/-- Feasibility at threshold `T` (`fourier_mellin.tex`): `f ∈ 𝒜_c^ε`, `f ≠ 0`, `ε f(0) ≤ 0` and
`f ≥ 0` on `[T, ∞)`. -/
structure IsHankelFeasible (c ε T : ℝ) (f : ℝ → ℝ) : Prop extends IsHankelEigenfn c ε f where
  nonzero : ∃ Δ ∈ Ici (0 : ℝ), f Δ ≠ 0
  origin_sign : ε * f 0 ≤ 0
  tail_nonneg : ∀ Δ ≥ T, 0 ≤ f Δ

/-- `T_c^ε`: the infimum of feasible thresholds. -/
noncomputable def hankelT (ε c : ℝ) : ℝ := sInf {T : ℝ | ∃ f, IsHankelFeasible c ε T f}

/-- `T_c^{-1}` with the extra condition `f(0) = 0` (the exact origin option of `gt:7.9b`). -/
noncomputable def hankelT0 (c : ℝ) : ℝ :=
  sInf {T : ℝ | ∃ f, IsHankelFeasible c (-1) T f ∧ f 0 = 0}

/-! ### Bridge to the abstract `HankelKernelData` development -/

section Bridge

variable {c : ℝ} (K : HankelKernelData c)

lemma HankelKernelData.hankelTransform_eq (hK : K.φ = hankelPhi c) (f : ℝ → ℝ) (Δ : ℝ) :
    hankelTransform c K f Δ = besselTransform c f Δ := by
  unfold hankelTransform besselTransform
  rw [hK]

lemma HankelKernelData.isRadialEigenfn_iff (hK : K.φ = hankelPhi c) (ε : ℝ) (f : ℝ → ℝ) :
    IsRadialEigenfn c K ε f ↔ IsHankelEigenfn c ε f := by
  constructor
  · intro h
    exact ⟨h.cont, h.int, fun Δ hΔ => by rw [← K.hankelTransform_eq hK]; exact h.eigen Δ hΔ⟩
  · intro h
    exact ⟨h.cont, h.int, fun Δ hΔ => by rw [K.hankelTransform_eq hK]; exact h.eigen Δ hΔ⟩

lemma HankelKernelData.isFeasible_iff (hK : K.φ = hankelPhi c) (ε T : ℝ) (f : ℝ → ℝ) :
    IsFeasible c K ε T f ↔ IsHankelFeasible c ε T f := by
  constructor
  · intro h
    exact ⟨(K.isRadialEigenfn_iff hK ε f).1 h.eigenfn, h.nonzero, h.origin_sign, h.tail_nonneg⟩
  · intro h
    exact ⟨(K.isRadialEigenfn_iff hK ε f).2 h.toIsHankelEigenfn, h.nonzero, h.origin_sign,
      h.tail_nonneg⟩

lemma HankelKernelData.threshold_eq (hK : K.φ = hankelPhi c) (ε : ℝ) :
    hankelThreshold c K ε = hankelT ε c := by
  unfold hankelThreshold hankelT
  congr 1
  ext T
  simp only [Set.mem_ofPred_eq, K.isFeasible_iff hK]

lemma HankelKernelData.thresholdZeroOrigin_eq (hK : K.φ = hankelPhi c) :
    hankelThresholdZeroOrigin c K (-1) = hankelT0 c := by
  unfold hankelThresholdZeroOrigin hankelT0
  congr 1
  ext T
  simp only [Set.mem_ofPred_eq, K.isFeasible_iff hK]

end Bridge

end FormalResearch.SignUncertainty
