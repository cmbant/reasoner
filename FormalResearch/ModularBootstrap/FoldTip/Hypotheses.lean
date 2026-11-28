module

public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.SignUncertainty.CeTerminalDeflation
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Families
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Design
public import FormalResearch.ModularBootstrap.Upper.Rigidity.VagueLimit

/-!
# The hypotheses of the fold-tip theorem as Lean structures (`FT-1`)

Formalises the setting and the local hypotheses of Paper I's `CFT/sign_uncertainty/paper/fold_tip_universality.tex`
(Paper I, Section 4), Section `ft:hyp` (Theorem FT, `ft:FT`): the weight `ρ_c`, the norm `M[g]`, the density `Ψ_g`, feasibility
with the monotonicity `(M)`, the threshold `T_c`, the fold constants `ξ_*, β, K_ξ, A`, and hypotheses
`H1`, `H2`, `H2-hol`, `H2+`, `H3`, `H4a`, `H4b`, each as its own `Prop`-valued structure with the quantifiers
of the TeX.  No theorem of FT is proved here; `FoldTip/Instances.lean` proves the hypotheses for the
fixed-weight modular bootstrap.

## Dictionary

| TeX | Lean |
|---|---|
| `ξ_*`, `β`, `K_ξ = (4/3)β^{3/2}`, `A = |a₁|/β` | `FoldTipScale.slope`, `.beta`, `.K`, `.A` |
| `ρ_c`, `M[g]`, `Ψ_g`, `∫Ψ_g`, feasible at `T`, `(M)`, `T_c` | `FoldTipSetting`, `.M`, `.Psi`, `.mass`, `.feasible`, `.feasible_mono`, `.threshold` |
| chart `u_c = c̃^{2/3}u_∞`, `ξ_c = u_c⁻¹`, rescaled density `Ψ̃_g`, far lobe | `FTChart`, `.uc`, `.xic`, `.PsiT`, `.lobe`, `discRadius` |
| `H1` | `FTH1` (`FTH1With` is its inequality for a given `η_vac`) |
| `H2`, `H2-hol` | `FTH2`, `FTH2hol` (common part `FTH2Frame`; envelope clause `FTEnvAt`) |
| `H2+` | `FTH2plus` |
| `H3` | `FTH3` |
| `H4a` | `FTH4a` |
| `H4b` | `FTH4b` (with its data `FTCrossingData`), matching `ft:H4b` for general `D : ShellHBData` |

* `H4b` (`ft:H4b`, Appendix `ft:dual`): for polynomial Hermite–Biehler data `D : ShellHBData` (`N = P Ai + Q Ai'`,
  terminal index `m = D.S.card`), `FTCrossingData` gives the extremal dual measures and their rescaled window
  pushforwards `μ_c = X.window c ν`. `FTH4b D X` states: (a) uniform upper support bound and cluster points in
  `S_N = {t_1, ..., t_{m-1}} ∪ (-∞, t_m]`; (b) existence of one-sided designs (`FTDesign`, `(D1)–(D4)`) with limit `W > 0`
  on `S_N` and with limit `R G_N` for every `R ∈ ℛ_N` of Lemma WR (`ft:WR`).
  Tail bounds and vague convergence `ft:C5c` are proved from `FTH4b` in `FoldTip/DualMeasures.lean`.

## Conventions

* `c` is `c̃`; the physical variable is `x = c ξ`, so `T` is a threshold in `x`.  The family is indexed by large
  `c`: each hypothesis holds for `c ≥ c₀` for a `c₀` that is part of the hypothesis (a parameter of the
  structure when later hypotheses refer to the same data, otherwise existentially quantified or `∀ᶠ c in atTop`).
* The data of `H2` that later hypotheses refer to (the chart, `c₀`, `a₀`, `N₀`, `q`, `ς_c`, `δ_lobe`) are
  parameters of `FTH2`, `FTH2hol`, `FTH2plus`, `FTH4a`; the constants the TeX makes depend on `K` (`C₀`, `κ`, `δ_lobe`)
  are quantified after `K`.  `ς_c` and `δ_lobe` are the functions of the TeX: `δ_lobe` takes `K` as first argument.
* `Ψ̃_g` lives on the real chart interval (`FTChart.PsiT`); `Ψ̃_g^h` is a function `ℂ → ℂ`
  holomorphic on a neighbourhood of the closed disc `D_c = {|u| ≤ A_c²}`, `A_c = a₀ c^{1/3}`, real on `ℝ`.
  The envelope is `C₀ e(u) exp(ς_c Re √u) (1+|u|)^{N₀} (Re √u)^{-q}` off the cut, with `e = airyEnv`.
* The outside-chart convention of the far lobe (`ξ < ξ_* - r₀` counts as `u_c = +∞`) is built into `FTChart.lobe`.
* `H4b`: the TeX's rescaled window measures are given by data `FTCrossingData` (`extremal` and `window`), with
  one-sided designs `FTDesign` obeying `(D1)–(D4)`.
-/

@[expose] public section

open Filter Topology MeasureTheory Metric Set Asymptotics

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.SignUncertainty

/-! ### The fold constants -/

/-- The two structural constants of a fold-tip problem: the leading slope `ξ_* > 0` and the fold coefficient
`K_ξ`, recorded through `β` with `K_ξ = (4/3)β^{3/2}` (`β = (3K_ξ/4)^{2/3}`). -/
structure FoldTipScale where
  slope : ℝ
  beta : ℝ
  slope_pos : 0 < slope
  beta_pos : 0 < beta

namespace FoldTipScale

/-- The fold coefficient `K_ξ = (4/3)β^{3/2}`. -/
noncomputable def K (s : FoldTipScale) : ℝ := (4 / 3) * s.beta ^ (3 / 2 : ℝ)

/-- The Airy coefficient `A = |a₁|/β`. -/
noncomputable def A (s : FoldTipScale) : ℝ := |airyZero 1| / s.beta

lemma K_pos (s : FoldTipScale) : 0 < s.K := by
  unfold K
  have := s.beta_pos
  positivity

lemma beta_eq (s : FoldTipScale) : s.beta = (3 * s.K / 4) ^ (2 / 3 : ℝ) := by
  have hb := s.beta_pos
  unfold K
  rw [show 3 * (4 / 3 * s.beta ^ (3 / 2 : ℝ)) / 4 = s.beta ^ (3 / 2 : ℝ) by ring,
    ← Real.rpow_mul hb.le]
  norm_num

end FoldTipScale

/-! ### The setting: weight, feasibility, threshold -/

/-- A fold-tip setting (`ft:hyp`): competitors `g` with real profile `ev g` on the positive energy axis, the
weight `ρ_c` (with a holomorphic continuation `rhoC`), and feasibility at a threshold `T`.  Fields:
`feasible_mono` is the monotonicity `(M)`; `feasible_nonneg` is the band positivity `g ≥ 0` on `[T, ∞)` built into
feasibility; `rho_pos` and `normPos` say that for `c ≥ cMin` the weight is positive on `(0,∞)` and every feasible
`g` has `0 < M[g]` (the TeX's "nonzero `g` with finite `M[g]`"). -/
structure FoldTipSetting where
  scale : FoldTipScale
  Comp : Type
  ev : Comp → ℝ → ℝ
  rho : ℝ → ℝ → ℝ
  rhoC : ℝ → ℂ → ℂ
  feasible : ℝ → ℝ → Comp → Prop
  cMin : ℝ
  rho_pos : ∀ c, cMin ≤ c → ∀ x : ℝ, 0 < x → 0 < rho c x
  rhoC_ofReal : ∀ c, cMin ≤ c → ∀ x : ℝ, 0 < x → rhoC c (x : ℂ) = (rho c x : ℂ)
  feasible_mono : ∀ c T T' (g : Comp), T ≤ T' → feasible c T g → feasible c T' g
  feasible_nonneg : ∀ c T (g : Comp), feasible c T g → ∀ x : ℝ, T ≤ x → 0 ≤ ev g x
  normPos : ∀ c, cMin ≤ c → ∀ T (g : Comp), feasible c T g →
    0 < ∫ x in Ioi (0 : ℝ), |ev g x| * rho c x

namespace FoldTipSetting

variable (S : FoldTipSetting)

/-- `M[g] = ∫_0^∞ |g| ρ_c`. -/
noncomputable def M (c : ℝ) (g : S.Comp) : ℝ := ∫ x in Ioi (0 : ℝ), |S.ev g x| * S.rho c x

/-- `Ψ_g = g ρ_c / M[g]`, the normalised signed density on the energy axis. -/
noncomputable def Psi (c : ℝ) (g : S.Comp) (x : ℝ) : ℝ := S.ev g x * S.rho c x / S.M c g

/-- `∫ Ψ_g dx` over the positive axis. -/
noncomputable def mass (c : ℝ) (g : S.Comp) : ℝ := ∫ x in Ioi (0 : ℝ), S.Psi c g x

/-- The threshold `T_c`, the infimum of the `T` at which a feasible `g` exists. -/
noncomputable def threshold (c : ℝ) : ℝ := sInf {T : ℝ | ∃ g : S.Comp, S.feasible c T g}

/-- `g` is feasible at some `T ≤ ξ_* c + K c^{1/3}`; by `(M)` this is feasibility at `ξ_* c + K c^{1/3}`
(`below_iff`). -/
def Below (c K : ℝ) (g : S.Comp) : Prop :=
  ∃ T : ℝ, T ≤ S.scale.slope * c + K * c ^ (1 / 3 : ℝ) ∧ S.feasible c T g

lemma below_iff (c K : ℝ) (g : S.Comp) :
    S.Below c K g ↔ S.feasible c (S.scale.slope * c + K * c ^ (1 / 3 : ℝ)) g :=
  ⟨fun ⟨T, hT, hf⟩ => S.feasible_mono c T _ g hT hf, fun h => ⟨_, le_rfl, h⟩⟩

end FoldTipSetting

/-! ### The chart of `H2` -/

/-- The chart data of `H2`: `u_∞` holomorphic and injective on `D(ξ_*, r₀)`, real on `ℝ`, with
`u_∞(ξ) = β(ξ_* - ξ)(1 + O(ξ - ξ_*))` as `ξ → ξ_*`. -/
structure FTChart (sc : FoldTipScale) where
  r0 : ℝ
  uInf : ℂ → ℂ
  r0_pos : 0 < r0
  analytic : AnalyticOnNhd ℂ uInf (ball (sc.slope : ℂ) r0)
  injOn : InjOn uInf (ball (sc.slope : ℂ) r0)
  real_on_real : ∀ x : ℝ, (x : ℂ) ∈ ball (sc.slope : ℂ) r0 → (uInf (x : ℂ)).im = 0
  tip : (fun ξ : ℂ => uInf ξ - (sc.beta : ℂ) * ((sc.slope : ℂ) - ξ)) =O[𝓝 (sc.slope : ℂ)]
    fun ξ => (ξ - (sc.slope : ℂ)) ^ 2

/-- The squared chart radius `A_c² = (a₀ c^{1/3})²`, with `D_c = {|u| ≤ A_c²}`. -/
noncomputable def discRadius (a0 c : ℝ) : ℝ := (a0 * c ^ (1 / 3 : ℝ)) ^ 2

namespace FTChart

variable {sc : FoldTipScale} (ch : FTChart sc)

/-- `u_c(ξ) = c^{2/3} u_∞(ξ)`. -/
noncomputable def uc (c : ℝ) (ξ : ℂ) : ℂ := ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) * ch.uInf ξ

/-- `ξ_c = u_c⁻¹` (the inverse of the injective chart on `D(ξ_*, r₀)`). -/
noncomputable def xic (c : ℝ) : ℂ → ℂ := Function.invFunOn (ch.uc c) (ball (sc.slope : ℂ) ch.r0)

/-- The rescaled density on the real chart interval,
`Ψ̃_g(u) = Ψ_g(c ξ_c(u)) · c |ξ_c'(u)|`. -/
noncomputable def PsiT (S : FoldTipSetting) (c : ℝ) (g : S.Comp) (u : ℝ) : ℝ :=
  S.Psi c g (c * (ch.xic c (u : ℂ)).re) * (c * ‖deriv (ch.xic c) (u : ℂ)‖)

/-- The far lobe `{x > 0 : u_c(x/c) > A_c²}`, where points `x` outside the chart with `x/c ≤ ξ_* - r₀` count as
`u_c = +∞`. -/
def lobe (a0 c : ℝ) : Set ℝ :=
  {x : ℝ | 0 < x ∧ (x / c ≤ sc.slope - ch.r0 ∨
    (|x / c - sc.slope| < ch.r0 ∧ discRadius a0 c < (ch.uc c ((x / c : ℝ) : ℂ)).re))}

/-- `∫_{lobe} |Ψ_g| dx`. -/
noncomputable def farLobeMass (S : FoldTipSetting) (a0 c : ℝ) (g : S.Comp) : ℝ :=
  ∫ x in ch.lobe a0 c, |S.Psi c g x|

/-- The rescaled weight `W_c(u) = c ρ_c(c ξ_c(u)) ξ_c'(u)` of `H4a`. -/
noncomputable def W (S : FoldTipSetting) (c : ℝ) (u : ℂ) : ℂ :=
  (c : ℂ) * S.rhoC c ((c : ℂ) * ch.xic c u) * deriv (ch.xic c) u

/-- The envelope clause of `H2` for one `g` at one `c`: `Ψ̃_g = Ψ̃_g^h + r_g` on `[-A_c², A_c²]`,
`|r_g| ≤ rem`, with `Ψ̃^h_g` holomorphic on (a neighbourhood of) `D_c`, real on `ℝ`, and off the cut
`(-∞, 0]` bounded by `C₀ e(u) exp(ς_c Re √u) (1+|u|)^{N₀} (Re √u)^{-q}`. -/
def EnvAt (S : FoldTipSetting) (a0 N0 q : ℝ) (ς : ℝ → ℝ) (C0 rem c : ℝ) (g : S.Comp) : Prop :=
  ∃ Ψh : ℂ → ℂ, AnalyticOnNhd ℂ Ψh (closedBall (0 : ℂ) (discRadius a0 c)) ∧
    (∀ u : ℝ, |u| ≤ discRadius a0 c →
      (Ψh (u : ℂ)).im = 0 ∧ |ch.PsiT S c g u - (Ψh (u : ℂ)).re| ≤ rem) ∧
    ∀ u ∈ closedBall (0 : ℂ) (discRadius a0 c), ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖Ψh u‖ ≤ C0 * airyEnv u * Real.exp (ς c * (u ^ (1 / 2 : ℂ)).re) *
        (1 + ‖u‖) ^ N0 * ((u ^ (1 / 2 : ℂ)).re) ^ (-q)

lemma EnvAt.mono_rem {S : FoldTipSetting} {a0 N0 q : ℝ} {ς : ℝ → ℝ} {C0 rem rem' c : ℝ}
    {g : S.Comp} (h : ch.EnvAt S a0 N0 q ς C0 rem c g) (hr : rem ≤ rem') :
    ch.EnvAt S a0 N0 q ς C0 rem' c g := by
  obtain ⟨Ψh, hΨ, hreal, hbd⟩ := h
  exact ⟨Ψh, hΨ, fun u hu => ⟨(hreal u hu).1, (hreal u hu).2.trans hr⟩, hbd⟩

end FTChart

/-! ### `H1` -/

/-- The inequality of `H1` for a given `η_vac`: eventually in `c`, every `g` feasible at some `T` has
`∫ Ψ_g ≤ η_vac(c)`. -/
def FTH1With (S : FoldTipSetting) (η : ℝ → ℝ) : Prop :=
  ∀ᶠ c in atTop, ∀ (T : ℝ) (g : S.Comp), S.feasible c T g → S.mass c g ≤ η c

/-- **`H1`** (band positivity and vacuum sign): there is `η_vac(c) → 0` with `∫ Ψ_g ≤ η_vac(c)` for every
feasible `g`.  (Band positivity `Ψ_g ≥ 0` on `[T, ∞)` is the field `FoldTipSetting.feasible_nonneg`.) -/
structure FTH1 (S : FoldTipSetting) : Prop where
  exists_eta : ∃ η : ℝ → ℝ, Tendsto η atTop (𝓝 0) ∧ FTH1With S η

/-! ### `H2`, `H2-hol` -/

/-- The part of `H2` that does not involve the envelope clause: positivity of the constants, the disc
`D_c ⊆ u_c(D(ξ_*, r₀))`, `ς_c ≥ 0`, `ς_c → 0`, and the far-lobe clause (`δ_lobe(K, c) → 0`). -/
structure FTH2Frame (S : FoldTipSetting) (ch : FTChart S.scale) (c0 a0 N0 q : ℝ) (ς : ℝ → ℝ)
    (δ : ℝ → ℝ → ℝ) : Prop where
  c0_pos : 0 < c0
  a0_pos : 0 < a0
  N0_nonneg : 0 ≤ N0
  q_nonneg : 0 ≤ q
  disc : ∀ c, c0 ≤ c →
    closedBall (0 : ℂ) (discRadius a0 c) ⊆ ch.uc c '' ball (S.scale.slope : ℂ) ch.r0
  varsigma_nonneg : ∀ c, c0 ≤ c → 0 ≤ ς c
  varsigma_tendsto : Tendsto ς atTop (𝓝 0)
  lobe : ∀ K : ℝ, 0 < K → Tendsto (δ K) atTop (𝓝 0) ∧
    ∀ c, c0 ≤ c → ∀ g : S.Comp, S.Below c K g → ch.farLobeMass S a0 c g ≤ δ K c

/-- **`H2`** (holomorphic Airy envelope around a cubic fold): for every `K > 0` there are `C₀ > 0` and
`κ > 0` such that every `g` feasible at some `T ≤ ξ_* c + K c^{1/3}` has `Ψ̃_g = Ψ̃_g^h + r_g` with
`‖r_g‖_∞ ≤ C₀ e^{-κ c}` and `Ψ̃_g^h` obeying the envelope. -/
structure FTH2 (S : FoldTipSetting) (ch : FTChart S.scale) (c0 a0 N0 q : ℝ) (ς : ℝ → ℝ)
    (δ : ℝ → ℝ → ℝ) : Prop extends FTH2Frame S ch c0 a0 N0 q ς δ where
  envelope : ∀ K : ℝ, 0 < K → ∃ C0 : ℝ, 0 < C0 ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ c, c0 ≤ c → ∀ g : S.Comp,
    S.Below c K g → ch.EnvAt S a0 N0 q ς C0 (C0 * Real.exp (-κ * c)) c g

/-- **`H2-hol`** (exact holomorphy, `r_g ≡ 0`). -/
structure FTH2hol (S : FoldTipSetting) (ch : FTChart S.scale) (c0 a0 N0 q : ℝ) (ς : ℝ → ℝ)
    (δ : ℝ → ℝ → ℝ) : Prop extends FTH2Frame S ch c0 a0 N0 q ς δ where
  envelope : ∀ K : ℝ, 0 < K → ∃ C0 : ℝ, 0 < C0 ∧ ∀ c, c0 ≤ c → ∀ g : S.Comp,
    S.Below c K g → ch.EnvAt S a0 N0 q ς C0 0 c g

/-- `H2-hol` is `H2` with `r_g = 0`. -/
theorem FTH2hol.toFTH2 {S : FoldTipSetting} {ch : FTChart S.scale} {c0 a0 N0 q : ℝ} {ς : ℝ → ℝ}
    {δ : ℝ → ℝ → ℝ} (h : FTH2hol S ch c0 a0 N0 q ς δ) : FTH2 S ch c0 a0 N0 q ς δ where
  toFTH2Frame := h.toFTH2Frame
  envelope K hK := by
    obtain ⟨C0, hC0, hC⟩ := h.envelope K hK
    exact ⟨C0, hC0, 1, one_pos, fun c hc g hg =>
      (hC c hc g hg).mono_rem ch (by positivity)⟩

/-! ### `H2+`, `H3` -/

/-- **`H2+`** (rates): `ς_c = O(c^{-1/3} log c)` and `η_vac + δ_lobe = o(c^{-1/3} log c)` for some `η_vac`
satisfying `H1` and every `K`. -/
structure FTH2plus (S : FoldTipSetting) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ) : Prop where
  varsigma_rate : ς =O[atTop] fun c => c ^ (-(1 / 3 : ℝ)) * Real.log c
  vac_lobe_rate : ∃ η : ℝ → ℝ, FTH1With S η ∧ ∀ K : ℝ, 0 < K →
    (fun c => η c + δ K c) =o[atTop] fun c => c ^ (-(1 / 3 : ℝ)) * Real.log c

/-- **`H3`** (attainment): some `g` is feasible at `ξ_* c + A c^{1/3} + R⁺(c)` for all large `c`, with
`R⁺(c) = o(c^{1/3})`. -/
structure FTH3 (S : FoldTipSetting) : Prop where
  attain : ∃ R : ℝ → ℝ, R =o[atTop] (fun c => c ^ (1 / 3 : ℝ)) ∧
    ∀ᶠ c in atTop, ∃ g : S.Comp,
      S.feasible c (S.scale.slope * c + S.scale.A * c ^ (1 / 3 : ℝ) + R c) g

/-! ### `H4a`, `H4b` -/

/-- **`H4a`**: `H2-hol` holds, and `W_c(u) = c ρ_c(c ξ_c(u)) ξ_c'(u)` is holomorphic and zero-free on each
compact set for large `c`. -/
structure FTH4a (S : FoldTipSetting) (ch : FTChart S.scale) (c0 a0 N0 q : ℝ) (ς : ℝ → ℝ)
    (δ : ℝ → ℝ → ℝ) : Prop where
  hol : FTH2hol S ch c0 a0 N0 q ς δ
  W_holomorphic_zerofree : ∀ K : Set ℂ, IsCompact K → ∀ᶠ c in atTop,
    K ⊆ ball (0 : ℂ) (discRadius a0 c) ∧ AnalyticOnNhd ℂ (ch.W S c) K ∧ ∀ u ∈ K, ch.W S c u ≠ 0

/-- Data for `H4b` (`ft:H4b`): the extremal dual (crossing) measures `ν ∈ X.extremal c` and their rescaled
window pushforwards `μ_c = X.window c ν` on `ℝ`. -/
structure FTCrossingData (S : FoldTipSetting) where
  extremal : ℝ → Set (Measure ℝ)
  window : ℝ → Measure ℝ → Measure ℝ

/-- The closed support set `S_N := {t_1, ..., t_{m-1}} ∪ (-∞, t_m]` for polynomial Hermite–Biehler data `D`. -/
def hbSupport (D : ShellHBData) : Set ℝ :=
  (D.S : Set ℝ) ∪ Iic D.tm

lemma isClosed_hbSupport (D : ShellHBData) : IsClosed (hbSupport D) :=
  D.S.finite_toSet.isClosed.union isClosed_Iic

/-- A one-sided design (`ft:H4b` (b), `(D1)–(D4)`) for dual measures `X.window c ν` (`ν ∈ X.extremal c`)
with continuous integrable limit `W : ℝ → ℝ`:
* `(D1)`: `∫ U_c dμ_c ≤ ∫ U_c du` eventually for every `ν ∈ X.extremal c`;
* `(D2)`: `U_c ≥ 0` on `(-∞, b]` for a fixed `b` and large `c`;
* `(D3)`: `U_c → W` locally uniformly as `c → ∞`;
* `(D4)`: `limsup_c ∫ U_c du ≤ ∫ W du`. -/
def FTDesign {S : FoldTipSetting} (X : FTCrossingData S) (W : ℝ → ℝ) : Prop :=
  Continuous W ∧ Integrable W ∧
  ∃ U : ℝ → ℝ → ℝ,
    (∃ c0 : ℝ, ∀ c, c0 ≤ c → Continuous (U c) ∧ Integrable (U c) ∧
      ∀ ν ∈ X.extremal c, Integrable (U c) (X.window c ν) ∧
        ∫ u, U c u ∂(X.window c ν) ≤ ∫ u, U c u) ∧
    (∃ b : ℝ, ∀ᶠ c in atTop, ∀ u : ℝ, u ≤ b → 0 ≤ U c u) ∧
    TendstoLocallyUniformly U W atTop ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c in atTop, ∫ u : ℝ, U c u ≤ (∫ u : ℝ, W u) + ε

/-- Continuous test window `(u - p)/(u - z) * G_N(u)` with removable singularity resolved via `dslope`
(`ft:WR` (i)). -/
noncomputable def hbSimpleTest (D : ShellHBData) (z p : ℝ) (u : ℂ) : ℂ :=
  D.G u + ((z - p : ℝ) : ℂ) * dslope D.G (z : ℂ) u

/-- Continuous test window `((u - b)/(u - z_k))^2 * ((u - q)/(u - t_m)) * G_N(u)` with removable
singularities resolved via iterated `dslope` (`ft:WR` (ii)). -/
noncomputable def hbPairedTest (D : ShellHBData) (k : ℕ) (b q : ℝ) (u : ℂ) : ℂ :=
  let zk := hbZeroEnum D k
  let H1 := fun v : ℂ => D.G v + ((D.tm - q : ℝ) : ℂ) * dslope D.G (D.tm : ℂ) v
  let H2 := fun v : ℂ => H1 v + ((zk - b : ℝ) : ℂ) * dslope H1 (zk : ℂ) v
  H2 u + ((zk - b : ℝ) : ℂ) * dslope H2 (zk : ℂ) u

/-- **`H4b`** (`ft:H4b`, Paper I Appendix `ft:dual`): dual measures at Hermite–Biehler level `D : ShellHBData`
and one-sided designs `(D1)–(D4)`.
* `(a)`: `supp μ_c ⊂ (-∞, B]` for large `c`, and every finite limit of points of `supp μ_{c_j}` (`c_j → ∞`) lies in `S_N`.
* `(b)`: there exists a one-sided design with limit `W > 0` on `S_N`, and for every `R ∈ ℛ_N` of Lemma WR (`ft:WR`),
  a one-sided design with limit `R G_N`. -/
structure FTH4b {S : FoldTipSetting} (D : ShellHBData) (X : FTCrossingData S) : Prop where
  support_upper : ∃ B : ℝ, ∀ᶠ c in atTop, ∀ ν ∈ X.extremal c,
    IsLocallyFiniteMeasure (X.window c ν) ∧ (X.window c ν) (Ioi B) = 0
  support_limit : ∀ (cs : ℕ → ℝ) (ν : ℕ → Measure ℝ) (xs : ℕ → ℝ) (x : ℝ),
    Tendsto cs atTop atTop → (∀ j, ν j ∈ X.extremal (cs j)) →
    (∀ j, xs j ∈ (X.window (cs j) (ν j)).support) → Tendsto xs atTop (𝓝 x) → x ∈ hbSupport D
  pos_design : ∃ W : ℝ → ℝ, (∀ u ∈ hbSupport D, 0 < W u) ∧ FTDesign X W
  test_one : FTDesign X (fun u => (D.G (u : ℂ)).re)
  test_simple : ∀ z ∈ D.S, ∃ δ : ℝ, 0 < δ ∧
    ∀ p : ℝ, 0 < |p - z| → |p - z| < δ → (z = D.tm → p < 0) →
      FTDesign X (fun u => (hbSimpleTest D z p (u : ℂ)).re)
  test_paired : ∀ (k : ℕ), D.S.card ≤ k → ∀ (b q : ℝ),
    b < 0 → b ≠ hbZeroEnum D k → q < 0 → q ≠ D.tm → q ≠ hbZeroEnum D k →
    (∀ t ∈ D.S, t ≠ D.tm → q < t) →
      FTDesign X (fun u => (hbPairedTest D k b q (u : ℂ)).re)

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.FTH2hol.toFTH2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTH2hol.toFTH2

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.FoldTipScale.beta_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FoldTipScale.beta_eq

end FormalResearch.ModularBootstrap.FoldTip
