module

public import FormalResearch.ModularBootstrap.FoldTip.TwoEdgeChart
public import FormalResearch.TwoEdgeBootstrap.Bootstrap

/-!
# Theorem FT-2E: Two-Edge Quantitative Fold-Tip Lower Bound over the Abstract Bootstrap

Source: `CFT/modular_bootstrap/paper/fold_tip_two_edge.tex`, Theorem FT-2E (`fto1:thm`,
`thm:fold-two-edges`), fixed Hermite--Biehler data paragraph; `CFT/common/two_edge_bootstrap.tex`
Theorem `TE.2` (`teb:bootstrap`, `teb:B2HB`).

* `TwoEdgeViolators`: hypotheses `(B1)`--`(B3)` for every violator of a fold chart, packaged as a
  `TwoEdgeBootstrap.BootstrapInstance` whose displacement is `x̃ = u - u_*` and whose terminal node is
  `u_*` (the Airy rule `u_* = a₁`, a fixed Clark rule `u_* = z₂(α)`, or any `u_* < 0` for which the
  `(TE.6)` node bounds of the instance hold).
* `ft_twoEdge_lower`: `T ≥ ξ_* C + (|u_*|/β) C^{1/3} - Km` for every feasible threshold
  (`teb_bootstrap_part3` for the displacement, `FoldChart.lower_of_displacement` for the chart inversion).
* `ft_twoEdge_expansion`: with a matching feasible construction, `T_opt = ξ_* C + (|u_*|/β) C^{1/3} + O(1)`.
* `TwoEdgeViolatorsHB`, `ft_twoEdge_lower_hb`, `ft_twoEdge_expansion_hb`: the same for fixed
  Hermite--Biehler data (`teb_bootstrap_hb`).
* `twoEdgeViolators_nonvacuous`, `twoEdgeViolatorsHB_nonvacuous`: the hypotheses are satisfiable
  (a linear chart and a feasible set with a genuine violator at every `C`).

Not covered: the construction of the bootstrap instance of a concrete problem, the chart expansion
`FoldChart.inv_lower` for a concrete `u_∞`, and conclusion C1 (used only through `ChartCoverage`).
-/

@[expose] public section

open scoped Real

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.TwoEdgeBootstrap

/-- Hypotheses `(B1)`--`(B3)` of Theorem `TE.2` for every violator (Airy or Clark node, or general
`u_*`): a bootstrap instance at `c = C` with `x̃ = u - u_*` obeying the feedback `(B3)`. -/
def TwoEdgeViolators (Ch : FoldChart) (P : BootstrapParams) (Feasible : ℝ → ℝ → Prop)
    (ustar C1 : ℝ) : Prop :=
  ∀ C : ℝ, C1 ≤ C → ∀ T u : ℝ, Ch.Violates Feasible ustar C T u →
    ∃ I : BootstrapInstance P, I.c = C ∧ I.x_tilde = u - ustar ∧
      I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1)

/-- The displacement bound `K₀` of `teb_bootstrap_part3`. -/
noncomputable def twoEdgeK0 (P : BootstrapParams) : ℝ :=
  max (2 * P.D_1) (max 1 (max (2 * tebAPart3 P)
    ((2 * tebAPart3 P * tebLSharp P) ^ (1 / ((P.k_0 : ℝ) + 3 / 2)))))

lemma one_le_twoEdgeK0 (P : BootstrapParams) : 1 ≤ twoEdgeK0 P :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- The lower constant `Km = K₀/β + C_ξ(|u_*| + m)²` of Theorem FT-2E. -/
noncomputable def twoEdgeKminus (Ch : FoldChart) (ustar K₀ m : ℝ) : ℝ :=
  K₀ / Ch.β + Ch.Cξ * (|ustar| + m) ^ 2

lemma twoEdgeKminus_nonneg (Ch : FoldChart) {ustar K₀ m : ℝ} (hK : 0 ≤ K₀) :
    0 ≤ twoEdgeKminus Ch ustar K₀ m := by
  have := Ch.hβ; have := Ch.hCξ
  unfold twoEdgeKminus; positivity

/-- **Theorem FT-2E, lower bound** (`fto1:lower`).  Under `(B1)`--`(B3)` for every violator in the
chart, with chart coverage and `C1 ≥ max C₀ (tebC2 P)`, every feasible threshold satisfies
`T ≥ ξ_* C + (|u_*|/β) C^{1/3} - Km` for `C ≥ C1`, with `Km` depending only on the constants of
the hypotheses. -/
theorem ft_twoEdge_lower (Ch : FoldChart) (P : BootstrapParams) {Feasible : ℝ → ℝ → Prop}
    {ustar C1 : ℝ} (hu : ustar < 0) (hC1 : max Ch.C0 (tebC2 P) ≤ C1)
    (hU : ∀ C : ℝ, C1 ≤ C → |ustar| ≤ Ch.U C)
    (hcov : Ch.ChartCoverage Feasible ustar C1)
    (hviol : TwoEdgeViolators Ch P Feasible ustar C1) :
    ∃ Km : ℝ, 0 ≤ Km ∧ ∀ C : ℝ, C1 ≤ C → ∀ T : ℝ, Feasible C T →
      Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ) - Km ≤ T := by
  have hK0 : 0 ≤ twoEdgeK0 P := (zero_le_one.trans (one_le_twoEdgeK0 P))
  have hm : 0 ≤ min P.δ_star (min P.η_0 1) :=
    le_min P.hδ_star.le (le_min P.hη0.le zero_le_one)
  refine ⟨twoEdgeKminus Ch ustar (twoEdgeK0 P) (min P.δ_star (min P.η_0 1)),
    twoEdgeKminus_nonneg Ch hK0, ?_⟩
  exact Ch.lower_of_displacement (κ := fun _ => twoEdgeK0 P) hu hm
    ((le_max_left _ _).trans hC1) hU (fun _ _ => hK0) hcov (by
      intro C hC T u hv
      obtain ⟨I, hIc, hIx, hB3⟩ := hviol C hC T u hv
      have hc : tebC2 P ≤ I.c := by rw [hIc]; exact (le_max_right _ _).trans (hC1.trans hC)
      have h3 := teb_bootstrap_part3 P I hc hB3
      refine ⟨by rw [← hIx]; exact I.hx_ub, ?_⟩
      rw [← hIc, ← hIx]
      exact h3)

/-- **Theorem FT-2E, two-sided expansion** (`fto1:two`): the lower bound together with a matching
feasible construction `T ≤ ξ_* C + (|u_*|/β) C^{1/3} + Kp` gives
`|T_C^{opt} - (ξ_* C + (|u_*|/β) C^{1/3})| ≤ K` for large `C`, `T_C^{opt} = inf {feasible T}`. -/
theorem ft_twoEdge_expansion (Ch : FoldChart) (P : BootstrapParams) {Feasible : ℝ → ℝ → Prop}
    {ustar C1 : ℝ} (hu : ustar < 0) (hC1 : max Ch.C0 (tebC2 P) ≤ C1)
    (hU : ∀ C : ℝ, C1 ≤ C → |ustar| ≤ Ch.U C)
    (hcov : Ch.ChartCoverage Feasible ustar C1)
    (hviol : TwoEdgeViolators Ch P Feasible ustar C1)
    {Kp C₂ : ℝ}
    (hup : ∀ C : ℝ, C₂ ≤ C → ∃ T : ℝ, Feasible C T ∧
      T ≤ Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ) + Kp) :
    ∃ K : ℝ, ∀ C : ℝ, max C1 C₂ ≤ C →
      |sInf {T : ℝ | Feasible C T} -
        (Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ))| ≤ K := by
  obtain ⟨Km, -, hlow⟩ := ft_twoEdge_lower Ch P hu hC1 hU hcov hviol
  exact ⟨max Km Kp, two_sided_of_lower_upper
    (a := fun C => Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ)) hlow hup⟩

/-! ### Fixed Hermite--Biehler data -/

/-- Hypotheses `(B1)`, `(B2_HB)`, `(B3)` for every violator (fixed Hermite--Biehler data,
`u_* = t_m`, `teb:B2HB`): an all-level Hermite--Biehler bootstrap instance. -/
def TwoEdgeViolatorsHB (Ch : FoldChart) (P : BootstrapParams) (W_top : ℝ)
    (Feasible : ℝ → ℝ → Prop) (ustar C1 : ℝ) : Prop :=
  ∀ C : ℝ, C1 ≤ C → ∀ T u : ℝ, Ch.Violates Feasible ustar C T u →
    ∃ I : BootstrapHBInstance P W_top, I.c = C ∧ I.x_tilde = u - ustar ∧
      I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1)

lemma one_le_tebK0HB (P : BootstrapParams) (W_top : ℝ) : 1 ≤ tebK0HB P W_top :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- **Theorem FT-2E with fixed Hermite--Biehler data**: the lower bound `(fto1:lower)` with
`u_* = t_m` and the constant `tebK0HB`. -/
theorem ft_twoEdge_lower_hb (Ch : FoldChart) (P : BootstrapParams) {W_top : ℝ}
    {Feasible : ℝ → ℝ → Prop} {ustar C1 : ℝ} (hu : ustar < 0)
    (hC1 : max Ch.C0 (tebC2 P) ≤ C1) (hU : ∀ C : ℝ, C1 ≤ C → |ustar| ≤ Ch.U C)
    (hcov : Ch.ChartCoverage Feasible ustar C1)
    (hviol : TwoEdgeViolatorsHB Ch P W_top Feasible ustar C1) :
    ∃ Km : ℝ, 0 ≤ Km ∧ ∀ C : ℝ, C1 ≤ C → ∀ T : ℝ, Feasible C T →
      Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ) - Km ≤ T := by
  have hK0 : 0 ≤ tebK0HB P W_top := zero_le_one.trans (one_le_tebK0HB P W_top)
  have hm : 0 ≤ min P.δ_star (min P.η_0 1) :=
    le_min P.hδ_star.le (le_min P.hη0.le zero_le_one)
  refine ⟨twoEdgeKminus Ch ustar (tebK0HB P W_top) (min P.δ_star (min P.η_0 1)),
    twoEdgeKminus_nonneg Ch hK0, ?_⟩
  exact Ch.lower_of_displacement (κ := fun _ => tebK0HB P W_top) hu hm
    ((le_max_left _ _).trans hC1) hU (fun _ _ => hK0) hcov (by
      intro C hC T u hv
      obtain ⟨I, hIc, hIx, hB3⟩ := hviol C hC T u hv
      have hc : tebC2 P ≤ I.c := by rw [hIc]; exact (le_max_right _ _).trans (hC1.trans hC)
      have h3 := ((teb_bootstrap_hb P I hc).2 hB3).2
      refine ⟨by rw [← hIx]; exact I.hx_ub, ?_⟩
      rw [← hIc, ← hIx]
      exact h3)

/-- **Theorem FT-2E with fixed Hermite--Biehler data, two-sided expansion** (`fto1:two`). -/
theorem ft_twoEdge_expansion_hb (Ch : FoldChart) (P : BootstrapParams) {W_top : ℝ}
    {Feasible : ℝ → ℝ → Prop} {ustar C1 : ℝ} (hu : ustar < 0)
    (hC1 : max Ch.C0 (tebC2 P) ≤ C1) (hU : ∀ C : ℝ, C1 ≤ C → |ustar| ≤ Ch.U C)
    (hcov : Ch.ChartCoverage Feasible ustar C1)
    (hviol : TwoEdgeViolatorsHB Ch P W_top Feasible ustar C1)
    {Kp C₂ : ℝ}
    (hup : ∀ C : ℝ, C₂ ≤ C → ∃ T : ℝ, Feasible C T ∧
      T ≤ Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ) + Kp) :
    ∃ K : ℝ, ∀ C : ℝ, max C1 C₂ ≤ C →
      |sInf {T : ℝ | Feasible C T} -
        (Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ))| ≤ K := by
  obtain ⟨Km, -, hlow⟩ := ft_twoEdge_lower_hb Ch P hu hC1 hU hcov hviol
  exact ⟨max Km Kp, two_sided_of_lower_upper
    (a := fun C => Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ)) hlow hup⟩

/-! ### Non-vacuity -/

/-- The exact linear chart `Δ_C(u) = -u C^{1/3}` (`ξ_* = 0`, `β = 1`, `C_ξ = 0`, `U_C = 2`). -/
noncomputable def linearFoldChart : FoldChart where
  ξs := 0
  β := 1
  Cξ := 0
  C0 := 1
  U := fun _ => 2
  Δ := fun C u => -(u * C ^ (1 / 3 : ℝ))
  hβ := one_pos
  hCξ := le_rfl
  hC0 := le_rfl
  inv_lower := fun C hC u _ => by simp

lemma linearFoldChart_Δ_injective {C : ℝ} (hC : 1 ≤ C) :
    Function.Injective (linearFoldChart.Δ C) := by
  intro u v h
  have hpos : 0 < C ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have : u * C ^ (1 / 3 : ℝ) = v * C ^ (1 / 3 : ℝ) := by
    simpa [linearFoldChart] using h
  exact mul_right_cancel₀ hpos.ne' this

/-- Feasible set with exactly one threshold per `C`, the chart image of `u_* + x_C`
(`u_* = -1`, `0 < x_C ≤ 1`). -/
def linearFeasible (x : ℝ → ℝ) (C T : ℝ) : Prop :=
  T = linearFoldChart.Δ C (-1 + x C)

lemma linearFeasible_coverage {x : ℝ → ℝ} (hxb : ∀ C : ℝ, 2 ≤ C → 0 < x C ∧ x C ≤ 1) :
    linearFoldChart.ChartCoverage (linearFeasible x) (-1) 2 := by
  intro C hC T hT _
  obtain ⟨h0, h1⟩ := hxb C hC
  refine ⟨-1 + x C, hT, ?_, by linarith, hT.symm⟩
  show |-1 + x C| ≤ 2
  rw [abs_le]; constructor <;> linarith

lemma linearFeasible_coord {x : ℝ → ℝ} {C T u : ℝ} (hC : 1 ≤ C)
    (hv : linearFoldChart.Violates (linearFeasible x) (-1) C T u) : u = -1 + x C :=
  linearFoldChart_Δ_injective hC (hv.2.2.2.trans hv.1)

/-- Non-vacuity for `TwoEdgeViolators`, `ChartCoverage` and the conclusion: with the linear chart,
`u_* = -1` and a feasible set with a genuine violator at every `C ≥ 2` (its bootstrap instance is
the one of `bootstrapInstance_nonvacuous`), all hypotheses of `ft_twoEdge_lower` hold. -/
theorem twoEdgeViolators_nonvacuous :
    ∃ x : ℝ → ℝ, (∀ C : ℝ, 2 ≤ C → 0 < x C ∧ x C ≤ 1) ∧
      linearFoldChart.ChartCoverage (linearFeasible x) (-1) 2 ∧
      TwoEdgeViolators linearFoldChart defaultBootstrapParams (linearFeasible x) (-1) 2 := by
  classical
  have hex : ∀ C : ℝ, ∃ I : BootstrapInstance defaultBootstrapParams,
      2 ≤ C → I.c = C ∧ I.L ≤ defaultBootstrapParams.C_fb *
        (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) := by
    intro C
    by_cases hC : 2 ≤ C
    · obtain ⟨I, h1, h2⟩ := bootstrapInstance_nonvacuous C hC
      exact ⟨I, fun _ => ⟨h1, h2⟩⟩
    · obtain ⟨I, _, _⟩ := bootstrapInstance_nonvacuous 2 le_rfl
      exact ⟨I, fun h => absurd h hC⟩
  choose I hI using hex
  have hxb : ∀ C : ℝ, 2 ≤ C → 0 < (I C).x_tilde ∧ (I C).x_tilde ≤ 1 := by
    intro C hC
    refine ⟨(I C).hx_pos, ?_⟩
    have := (I C).hx_ub
    simpa only [defaultBootstrapParams, min_self] using this
  refine ⟨fun C => (I C).x_tilde, hxb, linearFeasible_coverage hxb, ?_⟩
  intro C hC T u hv
  have hu := linearFeasible_coord (x := fun C => (I C).x_tilde) (by linarith) hv
  obtain ⟨hIc, hIL⟩ := hI C hC
  exact ⟨I C, hIc, by rw [hu]; ring, hIL⟩

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_twoEdge_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.ft_twoEdge_lower

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_twoEdge_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.ft_twoEdge_expansion

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_twoEdge_lower_hb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.ft_twoEdge_lower_hb

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_twoEdge_expansion_hb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.ft_twoEdge_expansion_hb

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.twoEdgeViolators_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.twoEdgeViolators_nonvacuous

end FormalResearch.ModularBootstrap.FoldTip
