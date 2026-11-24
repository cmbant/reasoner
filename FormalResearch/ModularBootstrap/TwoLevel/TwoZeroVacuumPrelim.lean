module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroWindow
public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumMain

/-!
# Preliminaries for the vacuum of the two-zero comb (`upper_transfer.tex`, Theorem T2 `ut:T2`, "assembly")

For `h₂ = combProfile c (twoZeroComb d c)` (`h₂ = sech² · T_{χ(p)} B₁` on the real axis) and the Cardy weight `V`:

* `norm_twoZeroComb_ofReal`: `‖B₂(x)‖ = |T_{χ(p)}(x)| ‖B₁(x)‖` for real `x`;
* `twoZeroF_eq_FVc`: `F_{2,c} = FV_c (2√2/(πλ))^{5/2}` (`eq:ut:T2-norm`);
* `split_integral_le_gen` (now in `Upper.Positivity.VacuumCore`): the splitting of `∫_{(0,∞)} F` at `t_S ≤ t_Φ ≤ t_R` keeping the part below `t_S` (the deep
  lobe is positive at `f = 2`: it is bounded absolutely and not dropped);
* `twoZero_integrand_props`: `h₂ V` is continuous on `[0, ∞)` and integrable on `(0, ∞)` (decay from `K7`);
* `twoZero_vacuum_ge`: `g_vac ≥ -2^m - π ∫_0^∞ h₂ V dt` (the vacuum identity of `K7`) and the integral of `Ψ_g`
  (`∫ Ψ_g du = -g_vac/(2π)`).

All results are proved unconditionally (for `prob.w = 1`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Window.Cardy
open TwoZeroDesign

lemma norm_twoZeroComb_ofReal {n : ℕ} (d : TwoZeroDesign n) (c x : ℝ) :
    ‖d.twoZeroComb c (x : ℂ)‖ = |tFac (d.chiP c) x| * ‖d.comb c (x : ℂ)‖ := by
  unfold twoZeroComb
  rw [norm_mul, tFac_eq, Complex.norm_real, Real.norm_eq_abs]

/-- `F_{2,c} = FV_c (2√2/(πλ))^{5/2}` (`eq:ut:T2-norm`). -/
lemma twoZeroF_eq_FVc (prob : Crossing.FixedWeightProblem) {c : ℝ} (hc : 0 < c) :
    twoZeroF prob c = FVc (qProb prob) c * (2 * √2 / (π * lambdaComb c)) ^ (5 / 2 : ℝ) := by
  have hl := lambdaComb_pos' hc
  have hπ := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hexp : (2 * (((2 : ℕ) : ℝ) - 1 / 4)) = 7 / 2 := by norm_num
  have hb : 0 < 2 * √2 / (π * lambdaComb c) := by positivity
  have h72 : (2 * √2 / (π * lambdaComb c)) ^ (7 / 2 : ℝ) =
      (2 * √2 / (π * lambdaComb c)) ^ (5 / 2 : ℝ) * (2 * √2 / (π * lambdaComb c)) := by
    rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Real.rpow_add hb, Real.rpow_one]
  unfold twoZeroF FKc
  rw [hexp, h72]
  field_simp

/-- `h₂ V` is continuous on `[0, ∞)` and integrable on `(0, ∞)`, uniformly on a compact family (decay of `h₂`
from `K7`). -/
theorem twoZero_integrand_props (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      ContinuousOn (fun t => combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t) (Ici 0) ∧
      IntegrableOn (fun t => combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t) (Ioi 0) := by
  filter_upwards [twoZeroComb_innerCombHyp hK hA, twoZeroComb_k7_membership_vacuum hw hK hA,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * prob.totalShift)]
    with c hI hK7 hpos hcS d hd
  obtain ⟨C, hC0, hdec, -⟩ := hK7 d hd
  have hcont := (hI d hd).continuousOn_combProfile hpos
  have hk := kernelIntegrable_of_decay (w := prob.w) prob.hw hpos hcont hdec
  exact ⟨hcont.mul (Crossing.continuous_cardyV prob (c / 12)).continuousOn,
    integrableOn_mul_cardyV (prob := prob) (by linarith) hcont hk⟩

/-- **The vacuum identity of `K7`** in the form used by `ut:T2`: for `c` large and `d ∈ 𝒦`,
`-2^m - π ∫_0^∞ h₂ V dt ≤ g_vac` (`g_vac = ½ h_{2,vac} - π ∫ h₂ V`, `|½ h_{2,vac}| ≤ 2^m`), and the same with the
upper bound `g_vac ≤ 2^m - π ∫ h₂ V dt`. -/
theorem twoZero_gVac_bounds (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      |prob.gVac (c / 12) (twoZeroG d c) + π * (∫ t in Ioi 0, combProfile c (d.twoZeroComb c) t *
        prob.cardyV (c / 12) t)| ≤ 2 ^ prob.m := by
  filter_upwards [twoZeroComb_k7_membership_vacuum hw hK hA] with c hK7 d hd
  obtain ⟨C, hC0, -, -, -, hvac, hn⟩ := hK7 d hd
  have hre := congrArg Complex.re hvac
  rw [Complex.ofReal_re, Complex.sub_re] at hre
  have h2 : ((π : ℂ) * ((∫ t in Ioi (0 : ℝ),
      combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t : ℝ) : ℂ)).re =
      π * (∫ t in Ioi (0 : ℝ), combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h2] at hre
  have h3 := (Complex.abs_re_le_norm _).trans hn
  unfold twoZeroG
  have : prob.gVac (c / 12) (pairOdd (combProfile c (d.twoZeroComb c))
      (hankelTransform 1 (combProfile c (d.twoZeroComb c)))) + π * (∫ t in Ioi (0 : ℝ),
      combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t) =
      ((1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
          combH0 (d.twoZeroComb c) (bAlpha c (c / 12 - prob.shiftSum s))).re := by
    linarith
  rw [this]
  exact h3

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroF_eq_FVc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroF_eq_FVc

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.split_integral_le_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_integral_le_gen

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_integrand_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_integrand_props

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_gVac_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_gVac_bounds

end FormalResearch.ModularBootstrap.TwoLevel
