module

public import FormalResearch.SignUncertainty.HeadlineDefs
public import FormalResearch.SignUncertainty.ShellGapHankel
public import FormalResearch.SignUncertainty.AirySquareSimple

/-!
# Statement objects and input structure for `thm:ce-canonical-iff` (= `thm:intro-gap`)

Source: `CFT/sign_uncertainty/paper/ce_canonical_iff.tex` (statement), `ce_airy_lp.tex` (`Λ_M`, `λ`,
`thm:airy-square-attained`), `ce_shells.tex` (`u_LP`, `u_sh`, `eq:ce-witness`,
`lem:ce-terminal-deflation`), `ce_airy_lp_proofs.tex` (`lem:airy-active-height`, `lem:airy-square-bound`,
`lem:airy-node-square`, `thm:airy-node-sign`).

Concrete objects (no free data):

* `shellSites D`: the prescribed sites `t_1, …, t_{m-1}` (`D.S` minus the terminal node `t_m = D.tm`).
* `OneProfileStrictFeasible`, `uSh`: strict-site witnesses and the cutoff `u_sh` (`uLP` is in `Radii.lean`).
* `airyLambdaM s M` (`Λ_M(s)`), `airyLambdaOf s` (`λ(s) = sup_M Λ_M(s)`): the constrained Airy-cardinal Rayleigh
  quotients of `ce_airy_lp.tex` for a finite set `s` of sites, defined from `airyLambdaSection`, `airyLambda`
  of `AirySquareSimple.lean` at `airySites s` (so there is one definition of `Λ_M`, `λ`).
* `IsHbZeroEnum P Q t`: `t j` is the paper's `t_{j+1}`, the strictly decreasing enumeration of the real zeros of
  `N = P Ai + Q Ai'` (this determines `t` uniquely; its existence is proved for every `D : ShellHBData` in
  `HbZeroEnum.lean`, `exists_isHbZeroEnum`). `hbNode t n = t_n` is the one-indexed form.
* `hbNodeWeight`, `hbNodeSquareBound`: `ω_n` and `τ_N` of `eq:hb-node-bound`.

* `ProfileConv Φ L`, `ShellGapEndpoint D`: the `v = t_m` endpoint clause of `thm:ce-shell-gap` (proved:
  `shellGapEndpoint_proved`, `ShellGapEndpoint.lean`; no longer a field of `CeCanonicalInputs`).

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

/-- Bridge: `airyUSh (D.S \ {D.tm}) = uSh D` (`AirySquareSimple.airyUSh`, for the prescribed sites). -/
theorem airyUSh_shellHBData (D : ShellHBData) :
    airyUSh ((D.S : Set ℝ) \ {D.tm}) = uSh D := by
  unfold airyUSh uSh
  have heq : ∀ v : ℝ, (∃ H, IsAiryStrictWitness ((D.S : Set ℝ) \ {D.tm}) v H) ↔
      OneProfileStrictFeasible D v := by
    intro v
    constructor
    · rintro ⟨H, ⟨h1, h2, h3, h4, h5⟩, h6⟩
      refine ⟨H, ⟨h1, h2, fun t ht htm => h3 t ⟨ht, htm⟩, h4, fun y hy => ?_⟩,
        fun t ht htm => h6 t ⟨ht, htm⟩⟩
      have hLy := h5 y hy
      unfold airyLaplace at hLy
      exact nonneg_of_mul_nonneg_right hLy (Real.exp_pos _)
    · rintro ⟨H, ⟨h1, h2, h3, h4, h5⟩, h6⟩
      refine ⟨H, ⟨h1, h2, fun t ht => h3 t ht.1 ht.2, h4, fun y hy => ?_⟩,
        fun t ht => h6 t ht.1 ht.2⟩
      unfold airyLaplace
      exact mul_nonneg (Real.exp_pos _).le (h5 y hy)
  exact le_antisymm
    (iSup₂_le fun v hv => le_iSup₂_of_le v ((heq v).mp hv) le_rfl)
    (iSup₂_le fun v hv => le_iSup₂_of_le v ((heq v).mpr hv) le_rfl)

/-- `Λ_M(s)` (`ce_airy_lp.tex`) for a finite set of sites `s`: the finite-section maximum `airyLambdaSection`
(`AirySquareSimple.lean`) at the sites `airySites s`. For `M ≥ |s| + 1` it is a maximum over a nonempty
compact set (`isGreatest_airySectionQuotientSet`); for smaller `M` it is a junk value and is never used. -/
noncomputable def airyLambdaM (s : Finset ℝ) (M : ℕ) : ℝ := airyLambdaSection (airySites s) M

/-- `λ(s) = sup_{M ≥ |s|+1} Λ_M(s)` (`thm:airy-square-attained`) for a finite set of sites. -/
noncomputable def airyLambdaOf (s : Finset ℝ) : ℝ := airyLambda (airySites s)

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

/-! ### The `v = t_m` endpoint clause of `thm:ce-shell-gap` -/

/-- `Φ_k → L` locally uniformly on `ℝ` and in `L¹` (the profiles `Φ_k` and `L` are integrable in every use below,
so the Bochner integral is the true `L¹` distance). -/
def ProfileConv (Φ : ℕ → ℝ → ℝ) (L : ℝ → ℝ) : Prop :=
  TendstoLocallyUniformlyOn Φ L atTop univ ∧ Tendsto (fun k => ∫ u : ℝ, |Φ k u - L u|) atTop (𝓝 0)

/-- **`thm:ce-shell-gap`, the `v = t_m` endpoint clause** (`ce_shells.tex`, Corollary H.14d and
`thm:ce-physical-profile`), in Hankel form (dimensions `d_k ≥ 2`, `c_k = d_k/2`; the same hypotheses as
`HankelShellGapLimit` with `u_* = t_m`: offsets `o(c^{1/3})`, Hankel Cohn–Elkies profiles `h_k = G k` with
`h_k ≤ 0` at the prescribed shells and thresholds `T_k ≤ c/π² - (t_m/β₁)c^{1/3} + o(c^{1/3})`). With
`M[h] = hankelMass`, `Ψ_{h,c} = hankelWindowProfile`, `f_k = ĥ_k - h_k` and `G_N/‖G_N‖₁ = D.normG`:
`Ψ_{h_k}/M[h_k] → -G_N/‖G_N‖₁` and `Ψ_{ĥ_k}/M[h_k] → 0` (locally uniformly and in `L¹`),
`Ψ_{f_k}/M[f_k] → G_N/‖G_N‖₁` (both senses), `M[ĥ_k]/M[f_k] → 0`, and `ℒ_y(-G_N) ≥ 0` for all `y > 0`.
Proved as `shellGapEndpoint_proved` (`ShellGapEndpoint.lean`): the zero-mass `L¹` clause of
`thm:ce-physical-profile` is the equality case of `lem:qual-compact` (`Analysis.qual_compact_real`). -/
def ShellGapEndpoint (D : ShellHBData) : Prop :=
  ∀ r : ℝ → ℕ → ℝ, ShellOffsetsSmall r →
    ∀ dk : ℕ → ℕ, Tendsto dk atTop atTop → (∀ k, 2 ≤ dk k) →
      ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
        ∀ (G : ℕ → ℝ → ℝ) (T : ℕ → ℝ), (∀ k, HankelShellProfile ((dk k : ℝ) / 2) (T k) (G k)) →
          (∀ k, ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) (dk k) →
            G k (shellSite t (r t) (dk k)) ≤ 0) →
          (∀ k, T k ≤ (dk k : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)
            + ε k * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)) →
          ProfileConv (fun k u => hankelWindowProfile ((dk k : ℝ) / 2) (G k) u /
              hankelMass ((dk k : ℝ) / 2) (G k)) (fun u => -D.normG u) ∧
          ProfileConv (fun k u => hankelWindowProfile ((dk k : ℝ) / 2)
              (besselHankelTransform ((dk k : ℝ) / 2) (G k)) u / hankelMass ((dk k : ℝ) / 2) (G k))
            (fun _ => 0) ∧
          ProfileConv (fun k u => hankelWindowProfile ((dk k : ℝ) / 2)
              (fun Δ => besselHankelTransform ((dk k : ℝ) / 2) (G k) Δ - G k Δ) u /
              hankelMass ((dk k : ℝ) / 2) (fun Δ => besselHankelTransform ((dk k : ℝ) / 2) (G k) Δ - G k Δ))
            D.normG ∧
          Tendsto (fun k => hankelMass ((dk k : ℝ) / 2) (besselHankelTransform ((dk k : ℝ) / 2) (G k)) /
            hankelMass ((dk k : ℝ) / 2) (fun Δ => besselHankelTransform ((dk k : ℝ) / 2) (G k) Δ - G k Δ))
            atTop (𝓝 0) ∧
          LaplaceNonneg D

/-! ### Input structure -/

/-- `thm:airy-square-attained` (`ce_airy_lp.tex`), the parts used by `thm:ce-canonical-iff`, for the sites
`s = t_1, …, t_{m-1}` of `D`: (1) the sequence `Λ_M(s)` is bounded above (`λ(s)` is finite), and (3) for a maximizing
cardinal series `q` the function `H_λ = (u - λ) q²` is a weak witness at `λ(s)` with `∫ H_λ = 0`, vanishing at every
site (double zero, `q(s_j) = 0`) and `L_{H_λ}(y) > 0` for all `y > 0`. This is a restriction of the full theorem
`thm_airy_square_attained_simple` (`AirySquareSimple.lean`); it is proved for every `D` by `airySquareAttained`. -/
structure AirySquareAttained (D : ShellHBData) : Prop where
  bddAbove : BddAbove (Set.range fun M : ℕ => airyLambdaM (shellSites D) (M + (shellSites D).card + 1))
  witness : ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ (∀ x : ℝ, (q (x : ℂ)).im = 0) ∧ (∃ z, q z ≠ 0) ∧
    (∀ s ∈ shellSites D, q (s : ℂ) = 0) ∧
    OneProfileFeasibleWitness D (airyLambdaOf (shellSites D))
      (fun z => (z - (airyLambdaOf (shellSites D) : ℂ)) * q z ^ 2) ∧
    (∫ u : ℝ, ((u - (airyLambdaOf (shellSites D) : ℂ)) * q (u : ℂ) ^ 2).re) = 0 ∧
    ∀ y : ℝ, 0 < y →
      0 < laplaceL (fun u => ((u - (airyLambdaOf (shellSites D) : ℂ)) * q (u : ℂ) ^ 2).re) y

/-- `thm:airy-square-attained` (1), (3) for the shell sites of `D` (proved, unconditional): `AirySquareAttained D`,
from `isGreatest_airySquareRayleigh`, `airyMaximizerWitness_properties` and `airyCardinalSeries_mem_squareClass_of_maximizer`
(`AirySquareSimple.lean`) at the distinct sites `airySites (shellSites D)`. -/
theorem airySquareAttained (D : ShellHBData) : AirySquareAttained D := by
  have hs := airySites_injective (shellSites D)
  have hrange := range_airySites (shellSites D)
  obtain ⟨⟨c, hc, hcmax⟩, _⟩ := isGreatest_airySquareRayleigh hs
  obtain ⟨hmem, _⟩ := airyCardinalSeries_mem_squareClass_of_maximizer hs hc hcmax
  obtain ⟨_, _, hint, hlap, ⟨w1, w2, w3, w4, w5⟩, _⟩ := airyMaximizerWitness_properties hs hc hcmax
  obtain ⟨hdiff, hreal, hnz, _, _, hsites⟩ := hmem
  have hD : ((D.S : Set ℝ) \ {D.tm}) = (shellSites D : Set ℝ) := by
    unfold shellSites; rw [Finset.coe_erase]
  refine ⟨?_, airyCardinalSeries c, hdiff, hreal, hnz, ?_, ?_, hint, ?_⟩
  · refine ⟨airyLambdaOf (shellSites D), ?_⟩
    rintro _ ⟨M, rfl⟩
    exact airyLambdaSection_le_airyLambda (airySites (shellSites D)) (by omega)
  · intro t ht
    obtain ⟨j, rfl⟩ : t ∈ Set.range (airySites (shellSites D)) := hrange ▸ (Finset.mem_coe.mpr ht)
    exact hsites j
  · refine ⟨w1, w2, fun t ht htm => w3 t ?_, w4, fun y hy => ?_⟩
    · rw [hrange, ← hD]; exact ⟨ht, htm⟩
    · have := w5 y hy
      unfold airyLaplace at this
      exact nonneg_of_mul_nonneg_right this (Real.exp_pos _)
  · intro y hy
    have := hlap y hy
    unfold airyLaplace at this
    unfold laplaceL
    exact pos_of_mul_pos_right this (Real.exp_pos _).le
      |> fun h => by simpa [airyMaximizerWitness, airyLambdaOf] using h

/-- info: 'FormalResearch.SignUncertainty.airySquareAttained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airySquareAttained

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
  /-- `lem:airy-node-square` (M9): for `m ≥ 2`, the fixed node-square bound `λ > τ_N > t_{m+e}`. -/
  airy_node_square : 2 ≤ D.S.card →
    hbTauN D t < airyLambdaOf (shellSites D) ∧ hbNode t (D.S.card + D.S.card / 2) < hbTauN D t
  /-- `lem:airy-active-height` (M9). -/
  active_height : AiryActiveHeight D
  /-- `thm:airy-node-sign` (M9): if `b = u_LP < t_m` and an optimizer `H_*` has no zeros `t' < t'' < t'''` of `N`
  in `(b, t_m]` with `H_*(t') > 0`, `H_*(t'') < 0`, `H_*(t''') > 0`, then `u_sh = u_LP`; in particular
  `u_sh = u_LP` whenever `t_{m+2} ≤ u_LP < t_m`. (The cumulative node-sum criterion is the field `node_sum`.) -/
  node_sign :
    (∀ b : ℝ, uLP D = (b : EReal) → b < D.tm → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
      (¬ ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ b < t₁ ∧ t₃ ≤ D.tm ∧ at47_Nf D.P D.Q t₁ = 0 ∧
        at47_Nf D.P D.Q t₂ = 0 ∧ at47_Nf D.P D.Q t₃ = 0 ∧ 0 < (H (t₁ : ℂ)).re ∧
        (H (t₂ : ℂ)).re < 0 ∧ 0 < (H (t₃ : ℂ)).re) → uSh D = (b : EReal)) ∧
    (∀ b : ℝ, uLP D = (b : EReal) → hbNode t (D.S.card + 2) ≤ b → b < D.tm → uSh D = (b : EReal))
  /-- `thm:airy-node-sign`, cumulative node-sum criterion (M9; `ce_airy_lp_proofs.tex`): let `b = u_LP < t_m` and `H`
  an optimizer. If there is a real zero `c ∈ [b, t_m)` of `H` with `H(t_n) ≤ 0` for the nodes `t_n < c`,
  `H'(c) ≥ 0` if `c` is a node, and `A(x) = ∑_{c < t_n ≤ x} η_n ≥ 0` for all `x > c`
  (`η_n = D(t_n) H(t_n)/N'(t_n)²`; the finite set of nodes in `(c, x]` is `F`), then `u_sh = u_LP`. -/
  node_sum : ∀ b : ℝ, uLP D = (b : EReal) → b < D.tm → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
    (∃ c : ℝ, b ≤ c ∧ c < D.tm ∧ (H (c : ℂ)).re = 0 ∧
      (∀ n : ℕ, t n < c → (H (t n : ℂ)).re ≤ 0) ∧
      ((∃ n : ℕ, t n = c) → 0 ≤ (deriv H (c : ℂ)).re) ∧
      (∀ x : ℝ, c < x → ∀ F : Finset ℕ, (∀ n : ℕ, n ∈ F ↔ (c < t n ∧ t n ≤ x)) →
        0 ≤ ∑ n ∈ F, airyPQDr D.P D.Q (t n) * (H (t n : ℂ)).re /
          ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2)) →
    uSh D = (b : EReal)
  /-- `lem:ce-terminal-deflation` (M9, `ce_shells.tex`): for `m` odd with `ℒ_y(-G_N) ≥ 0` for all `y > 0`, the
  terminal cardinal `H_N = -G_N/(u - t_m)` has `I_N = ∫ H_N = D(t_m)/∏_{j<m}(t_j - t_m) > 0` (the node weight
  numerator `D(t_m)` is positive for Hermite–Biehler data, `gt:1.0pp`). -/
  terminal_deflation : (∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) →
    MeasureTheory.Integrable (fun u : ℝ => (-(D.G (u : ℂ)).re) / (u - D.tm)) ∧
    (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) =
      airyPQDr D.P D.Q D.tm / ∏ s ∈ shellSites D, (s - D.tm) ∧
    0 < ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)

end FormalResearch.SignUncertainty
