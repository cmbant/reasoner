module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Nodes

/-!
# The design input `(P1)`–`(P4)` at the abstract measure level (`sr:P`)

Property `sr:P` of `spectral_rigidity.tex` (the existence of the comb functionals `g_𝔇` of the
designs `𝔇`) is **not formalised**; this module states exactly what the rigidity proofs use of it
as an explicit hypothesis, with a non-vacuity theorem.

**Windows.**  A `Window` is the abstract `W_𝔇`: a continuous integrable `W : ℝ → ℝ`, with first kept
site `uF = u_f`, `W ≥ 0` on `u ≤ u_f` (`W_𝔇 > 0` on `u < u_f`), and the Airy quadrature
`∫ W = Σ_n W(a_n)/Ai'(a_n)²` (`ut:V`; Lean: `lemma_V_hasSum` for the `f = 1` designs
`designWindowW`).  `Window.pi D i = Π_{i+1}(𝔇) = W(a_{i+1})/Ai'(a_{i+1})²`, `Window.V D = V_𝔇`.

**Design test.**  `DesignTest μ D` packages `(P1)`–`(P4)` for one design and the spectral measures
`μ_j = μ_{S_j}` in the Airy variable: with `Ψ_j = (2/(C_* FK_c)) Ψ_{g_𝔇}` at `c = c_j` (the
constant `C_*^{(f)} > 0` is divided out; this changes none of the inequalities),

* `integrable_mu`, `integrable_vol`, `crossing`: `Ψ_j ∈ L¹(μ_j) ∩ L¹(du)` and
  `∫ Ψ_j dμ_j = ∫ Ψ_j du` (`(P1)` with Proposition `sr:P1`);
* `nonneg`, `theta_tendsto`: `(P2)`, `Ψ_j ≥ 0` on `u ≤ θ_j := u(t_f + 1)`, and `θ_j → u_f`
  (`u(t_f) = u_f + O(c'^{-1/3})`, `J ≍ c'^{1/3}`);
* `window_limit`: `(P3)`, `Ψ_j → W_𝔇` locally uniformly on `ℝ`;
* `limsup_le`: `(P4)`, `limsup_j ∫ Ψ_j du ≤ V_𝔇`.

`DesignPropertyP μ 𝒟` says every window of the class `𝒟` carries a design test; `designTest_nonvacuous`
shows it is satisfiable (by `μ_j = μ_A`, `Ψ_j = W`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special

/-- An abstract design window `W_𝔇` (`spectral_rigidity.tex`, §2): see the module docstring. -/
structure Window where
  /-- the window function `W_𝔇` -/
  W : ℝ → ℝ
  /-- the first kept site `u_f` -/
  uF : ℝ
  continuous : Continuous W
  integrable : Integrable W
  nonneg_left : ∀ u, u ≤ uF → 0 ≤ W u
  /-- the Airy quadrature (`ut:V`): `∫ W = Σ_n W(a_n)/Ai'(a_n)²` -/
  hasSum : HasSum (fun i : ℕ => W (airyNode i) * airyNodeWeight i) (∫ u, W u)

namespace Window

/-- `Π_{i+1}(𝔇) = W(a_{i+1}) / Ai'(a_{i+1})²`. -/
noncomputable def pi (D : Window) (i : ℕ) : ℝ := D.W (airyNode i) * airyNodeWeight i

/-- `V_𝔇 = ∫ W_𝔇`. -/
noncomputable def V (D : Window) : ℝ := ∫ u, D.W u

lemma hasSum_pi (D : Window) : HasSum D.pi D.V := D.hasSum

lemma summable_pi (D : Window) : Summable D.pi := D.hasSum.summable

lemma tsum_pi (D : Window) : ∑' i, D.pi i = D.V := D.hasSum.tsum_eq

lemma pi_nonneg_of_le (D : Window) {i : ℕ} (h : airyNode i ≤ D.uF) : 0 ≤ D.pi i :=
  mul_nonneg (D.nonneg_left _ h) (airyNodeWeight_pos i).le

end Window

/-- `(P1)`–`(P4)` for one design `D` and the spectral measures `μ_j` (see the module docstring). -/
structure DesignTest (μ : ℕ → Measure ℝ) (D : Window) where
  /-- the rescaled test functions `Ψ_j = (2/(C_* FK_c)) Ψ_g` at `c = c_j` -/
  Ψ : ℕ → ℝ → ℝ
  /-- the positivity threshold `θ_j = u(t_f + 1)` -/
  θ : ℕ → ℝ
  continuous : ∀ j, Continuous (Ψ j)
  integrable_mu : ∀ j, Integrable (Ψ j) (μ j)
  integrable_vol : ∀ j, Integrable (Ψ j)
  crossing : ∀ j, ∫ u, Ψ j u ∂(μ j) = ∫ u, Ψ j u
  nonneg : ∀ j u, u ≤ θ j → 0 ≤ Ψ j u
  theta_tendsto : Tendsto θ atTop (𝓝 D.uF)
  window_limit : TendstoLocallyUniformly Ψ D.W atTop
  limsup_le : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∫ u, Ψ j u ≤ D.V + ε

/-- **Hypothesis (not formalised): Property `sr:P`.**  Every window of the class `𝒟` (the designs of
`spectral_rigidity.tex` §2) carries a design test `(P1)`–`(P4)` for the spectral measures `μ_j`.
Source: `spectral_rigidity.tex`, Property `sr:P` with its proof via the comb estimates of
`upper_transfer.tex`; not yet formalised in Lean. -/
def DesignPropertyP (μ : ℕ → Measure ℝ) (𝒟 : Set Window) : Prop :=
  ∀ D ∈ 𝒟, Nonempty (DesignTest μ D)

/-- **Non-vacuity of `DesignPropertyP`**: the Airy quadrature measure `μ_A` itself, with `Ψ_j = W`
and `θ_j = u_f`, carries a design test for every window. -/
theorem designTest_nonvacuous (D : Window) : Nonempty (DesignTest (fun _ => airyMeasure) D) := by
  have hint : Integrable D.W airyMeasure := integrable_airyMeasure D.continuous D.summable_pi
  refine ⟨{
    Ψ := fun _ => D.W
    θ := fun _ => D.uF
    continuous := fun _ => D.continuous
    integrable_mu := fun _ => hint
    integrable_vol := fun _ => D.integrable
    crossing := fun _ => ?_
    nonneg := fun _ u hu => D.nonneg_left u hu
    theta_tendsto := tendsto_const_nhds
    window_limit := (Metric.tendstoUniformly_iff.2 fun ε hε =>
      Eventually.of_forall fun _ x => by simpa using hε).tendstoLocallyUniformly
    limsup_le := fun ε hε => Eventually.of_forall fun _ => by unfold Window.V; linarith }⟩
  rw [integral_airyMeasure D.continuous D.summable_pi]
  exact D.hasSum.tsum_eq

theorem designPropertyP_nonvacuous (𝒟 : Set Window) :
    DesignPropertyP (fun _ => airyMeasure) 𝒟 := fun D _ => designTest_nonvacuous D

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.designTest_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.designTest_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.designPropertyP_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.designPropertyP_nonvacuous

end FormalResearch.ModularBootstrap.Upper.Rigidity
