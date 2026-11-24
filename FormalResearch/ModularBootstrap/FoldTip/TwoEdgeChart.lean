module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Fold-Tip Theorem FT-2E: Chart Inversion over an Abstract Fold Chart

Source: `CFT/modular_bootstrap/paper/fold_tip_two_edge.tex` (Theorem FT-2E, `fto1:thm`, proof) and
`fold_tip_universality.tex` (the chart `u_C`, `ξ_*`, `β`).

* `FoldChart`: the inverse fold chart `Δ_C(u) = C ξ_C(u)` of `u_C(ξ) = C^{2/3} u_∞(ξ)`,
  `u_∞(ξ) = β(ξ_* - ξ)(1 + O(ξ - ξ_*))`, in the form used to invert the chart,
  `Δ_C(u) ≥ ξ_* C - (u/β) C^{1/3} - C_ξ C^{-1/3} u²` on `|u| ≤ U_C`.
* `ChartCoverage`: a feasible threshold below `Δ_C(u_*)` has a chart coordinate `u > u_*`
  (conclusion C1 of the fold-tip theorem puts it in the chart); `chartCoverage_of_C1` derives it from C1
  and continuity of the chart.
* `ft_lower_of_displacement`: the chart-inversion step of the proof: a bound `C^{1/3}(u - u_*) ≤ κ_C`
  and `u - u_* ≤ m` on every violator give `T ≥ ξ_* C + (|u_*|/β) C^{1/3} - κ_C/β - C_ξ(|u_*| + m)²`.
* `ft_two_sided_of_lower_upper`: lower bound plus a matching feasible construction give the two-sided
  `O(1)` law for the infimum of feasible thresholds.

Everything here is proved; the bootstrap input enters only through the displacement hypothesis
(see `TwoEdgeLower.lean`).
-/

@[expose] public section

open scoped Real

namespace FormalResearch.ModularBootstrap.FoldTip

/-- Inverse fold chart in the lower-inversion form of the proof of Theorem FT-2E.  `ξs = ξ_*`,
`β > 0` the slope of `u_∞` at `ξ_*`, `Δ C u = C ξ_C(u)` the chart inverse (threshold `T = Δ C u`),
`U C` the chart radius in `u`, `Cξ` the quadratic remainder constant. -/
structure FoldChart where
  ξs : ℝ
  β : ℝ
  Cξ : ℝ
  C0 : ℝ
  U : ℝ → ℝ
  Δ : ℝ → ℝ → ℝ
  hβ : 0 < β
  hCξ : 0 ≤ Cξ
  hC0 : 1 ≤ C0
  inv_lower : ∀ C : ℝ, C0 ≤ C → ∀ u : ℝ, |u| ≤ U C →
    ξs * C - (u / β) * C ^ (1 / 3 : ℝ) - Cξ * C ^ (-(1 / 3 : ℝ)) * u ^ 2 ≤ Δ C u

namespace FoldChart

variable (Ch : FoldChart)

/-- `(T, u)` is a violator at `C`: `T` is feasible, `u` is a chart coordinate of `T`
(`T = Δ_C(u)`, `|u| ≤ U_C`) and `u > u_*`. -/
def Violates (Feasible : ℝ → ℝ → Prop) (ustar C T u : ℝ) : Prop :=
  Feasible C T ∧ |u| ≤ Ch.U C ∧ ustar < u ∧ Ch.Δ C u = T

/-- Every feasible threshold below `Δ_C(u_*)` has a chart coordinate `u > u_*`, for `C ≥ C1`. -/
def ChartCoverage (Feasible : ℝ → ℝ → Prop) (ustar C1 : ℝ) : Prop :=
  ∀ C : ℝ, C1 ≤ C → ∀ T : ℝ, Feasible C T → T < Ch.Δ C ustar →
    ∃ u : ℝ, Ch.Violates Feasible ustar C T u

/-- **Chart coverage from conclusion C1.**  If every feasible threshold satisfies
`T ≥ ξ_* C - A₁ C^{1/3}` (C1), the chart is continuous on `[u_*, U_C]` and
`Δ_C(U_C) ≤ ξ_* C - A₁ C^{1/3}`, then every feasible `T < Δ_C(u_*)` has a coordinate `u > u_*`. -/
theorem chartCoverage_of_C1 {Feasible : ℝ → ℝ → Prop} {ustar A₁ C1 : ℝ}
    (hU : ∀ C : ℝ, C1 ≤ C → |ustar| ≤ Ch.U C)
    (hcont : ∀ C : ℝ, C1 ≤ C → ContinuousOn (Ch.Δ C) (Set.Icc ustar (Ch.U C)))
    (hedge : ∀ C : ℝ, C1 ≤ C → Ch.Δ C (Ch.U C) ≤ Ch.ξs * C - A₁ * C ^ (1 / 3 : ℝ))
    (hC1 : ∀ C : ℝ, C1 ≤ C → ∀ T : ℝ, Feasible C T → Ch.ξs * C - A₁ * C ^ (1 / 3 : ℝ) ≤ T) :
    Ch.ChartCoverage Feasible ustar C1 := by
  intro C hC T hT hlt
  have hUC := hU C hC
  have hle : ustar ≤ Ch.U C := (le_abs_self ustar).trans hUC
  obtain ⟨u, hu, huT⟩ := intermediate_value_Icc' hle (hcont C hC)
    ⟨(hedge C hC).trans (hC1 C hC T hT), hlt.le⟩
  have hne : u ≠ ustar := by
    rintro rfl; exact absurd huT (ne_of_gt hlt)
  have hlt_u : ustar < u := lt_of_le_of_ne hu.1 (Ne.symm hne)
  refine ⟨u, hT, abs_le.mpr ⟨?_, hu.2⟩, hlt_u, huT⟩
  linarith [neg_abs_le ustar, abs_nonneg ustar]

/-- **Chart-inversion step of Theorem FT-2E / Proposition FT-Sub.**  Let every violator `(T, u)`
(`u > u_*`) satisfy `u - u_* ≤ m` and `C^{1/3}(u - u_*) ≤ κ_C` (the displacement `K ≤ κ_C`).  Then
every feasible threshold satisfies, for `C ≥ C1`,
`T ≥ ξ_* C + (|u_*|/β) C^{1/3} - (κ_C/β + C_ξ (|u_*| + m)²)`. -/
theorem lower_of_displacement {Feasible : ℝ → ℝ → Prop} {ustar m C1 : ℝ} {κ : ℝ → ℝ}
    (hu : ustar < 0) (hm : 0 ≤ m) (hC1 : Ch.C0 ≤ C1)
    (hU : ∀ C : ℝ, C1 ≤ C → |ustar| ≤ Ch.U C)
    (hκ : ∀ C : ℝ, C1 ≤ C → 0 ≤ κ C)
    (hcov : Ch.ChartCoverage Feasible ustar C1)
    (hdisp : ∀ C : ℝ, C1 ≤ C → ∀ T u : ℝ, Ch.Violates Feasible ustar C T u →
      u - ustar ≤ m ∧ C ^ (1 / 3 : ℝ) * (u - ustar) ≤ κ C) :
    ∀ C : ℝ, C1 ≤ C → ∀ T : ℝ, Feasible C T →
      Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ) -
        (κ C / Ch.β + Ch.Cξ * (|ustar| + m) ^ 2) ≤ T := by
  intro C hC T hT
  have hC1' : 1 ≤ C := Ch.hC0.trans (hC1.trans hC)
  have hCpos : 0 < C := by linarith
  have hc13 : 0 < C ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hCpos _
  have hcm_nn : 0 ≤ C ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hCpos.le _
  have hcm_le : C ^ (-(1 / 3 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hCpos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hC1' (by norm_num))
  have hβ := Ch.hβ
  have hCξ := Ch.hCξ
  have hκC := hκ C hC
  have habs : |ustar| = -ustar := abs_of_neg hu
  have hq : Ch.Cξ * C ^ (-(1 / 3 : ℝ)) * (|ustar| + m) ^ 2 ≤ Ch.Cξ * (|ustar| + m) ^ 2 := by
    have : 0 ≤ Ch.Cξ * (|ustar| + m) ^ 2 := by positivity
    nlinarith
  have hκβ : 0 ≤ κ C / Ch.β := div_nonneg hκC hβ.le
  by_cases hge : Ch.Δ C ustar ≤ T
  · have hinv := Ch.inv_lower C (hC1.trans hC) ustar (hU C hC)
    have h1 : Ch.Cξ * C ^ (-(1 / 3 : ℝ)) * ustar ^ 2 ≤ Ch.Cξ * (|ustar| + m) ^ 2 := by
      have hsq : ustar ^ 2 ≤ (|ustar| + m) ^ 2 := by
        rw [← sq_abs ustar]; nlinarith [abs_nonneg ustar]
      calc Ch.Cξ * C ^ (-(1 / 3 : ℝ)) * ustar ^ 2
          ≤ Ch.Cξ * C ^ (-(1 / 3 : ℝ)) * (|ustar| + m) ^ 2 := by gcongr
        _ ≤ _ := hq
    have h2 : -(ustar / Ch.β) * C ^ (1 / 3 : ℝ) = (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ) := by
      rw [habs]; ring
    nlinarith
  · push Not at hge
    obtain ⟨u, hviol⟩ := hcov C hC T hT hge
    obtain ⟨hum, huK⟩ := hdisp C hC T u hviol
    obtain ⟨_, huU, hlt_u, hΔ⟩ := hviol
    have hinv := Ch.inv_lower C (hC1.trans hC) u huU
    rw [hΔ] at hinv
    have hu2 : u ^ 2 ≤ (|ustar| + m) ^ 2 := by
      rw [← sq_abs u]
      have : |u| ≤ |ustar| + m := by
        rw [abs_le]; constructor <;> linarith [abs_nonneg ustar]
      nlinarith [abs_nonneg u]
    have h1 : Ch.Cξ * C ^ (-(1 / 3 : ℝ)) * u ^ 2 ≤ Ch.Cξ * (|ustar| + m) ^ 2 :=
      calc Ch.Cξ * C ^ (-(1 / 3 : ℝ)) * u ^ 2
          ≤ Ch.Cξ * C ^ (-(1 / 3 : ℝ)) * (|ustar| + m) ^ 2 := by gcongr
        _ ≤ _ := hq
    have h2 : (u / Ch.β) * C ^ (1 / 3 : ℝ) ≤ (ustar / Ch.β) * C ^ (1 / 3 : ℝ) + κ C / Ch.β := by
      have h3 : (u / Ch.β) * C ^ (1 / 3 : ℝ) - (ustar / Ch.β) * C ^ (1 / 3 : ℝ) =
          (C ^ (1 / 3 : ℝ) * (u - ustar)) / Ch.β := by field_simp
      have h4 : (C ^ (1 / 3 : ℝ) * (u - ustar)) / Ch.β ≤ κ C / Ch.β :=
        div_le_div_of_nonneg_right huK hβ.le
      linarith
    have h5 : -(ustar / Ch.β) * C ^ (1 / 3 : ℝ) = (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ) := by
      rw [habs]; ring
    nlinarith

end FoldChart

/-- **Two-sided law from a lower bound and a matching construction.**  If every feasible `T` obeys
`T ≥ a_C - Km` for `C ≥ C₁` and for `C ≥ C₂` some feasible `T ≤ a_C + Kp` exists, then the infimum
of the feasible thresholds is within `max Km Kp` of `a_C` for `C ≥ max C₁ C₂`
(`T_C^{opt} = a_C + O(1)`). -/
theorem two_sided_of_lower_upper {Feasible : ℝ → ℝ → Prop} {a : ℝ → ℝ} {Km Kp C₁ C₂ : ℝ}
    (hlow : ∀ C : ℝ, C₁ ≤ C → ∀ T : ℝ, Feasible C T → a C - Km ≤ T)
    (hup : ∀ C : ℝ, C₂ ≤ C → ∃ T : ℝ, Feasible C T ∧ T ≤ a C + Kp) :
    ∀ C : ℝ, max C₁ C₂ ≤ C → |sInf {T : ℝ | Feasible C T} - a C| ≤ max Km Kp := by
  intro C hC
  have hC1 : C₁ ≤ C := (le_max_left _ _).trans hC
  have hC2 : C₂ ≤ C := (le_max_right _ _).trans hC
  obtain ⟨T₀, hT₀, hT₀le⟩ := hup C hC2
  have hne : {T : ℝ | Feasible C T}.Nonempty := ⟨T₀, hT₀⟩
  have hbdd : BddBelow {T : ℝ | Feasible C T} := ⟨a C - Km, fun T hT => hlow C hC1 T hT⟩
  have h1 : a C - Km ≤ sInf {T : ℝ | Feasible C T} := le_csInf hne fun T hT => hlow C hC1 T hT
  have h2 : sInf {T : ℝ | Feasible C T} ≤ a C + Kp := (csInf_le hbdd hT₀).trans hT₀le
  rw [abs_le]
  constructor
  · linarith [le_max_left Km Kp]
  · linarith [le_max_right Km Kp]

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.FoldChart.chartCoverage_of_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.FoldChart.chartCoverage_of_C1

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.FoldChart.lower_of_displacement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.FoldChart.lower_of_displacement

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.two_sided_of_lower_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.two_sided_of_lower_upper

end FormalResearch.ModularBootstrap.FoldTip
