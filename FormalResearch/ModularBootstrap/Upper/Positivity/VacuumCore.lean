module

public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumWindow
public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionOne
public import FormalResearch.ModularBootstrap.Upper.Window.Tail
public import FormalResearch.ModularBootstrap.Upper.Membership.DesignMembership

/-!
# Proposition V: the upper bound for `V_c = ∫_0^∞ h₀ V dt` (`ut:Vac`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, proof of Proposition V (`ut:Vac`).  For the designs
`D(N, η_*, d)` (`f = 1`, `Q = (1-q)²`, `h₀ = combProfile c' (designComb …)`, `V = cardyV (c'/12)`), with
`V_c = ∫_{0}^{∞} h₀ V dt`:

* `split_integral_le`: `V_c ≤ ∫_{t_S}^{t_Φ} h₀ V + ∫_{band} |h₀| V + ∫_{far} |h₀| V` when `h₀ V ≤ 0` below `t_S`
  (the dropped negative lobe);
* `window_part_le`: the window integral against the window limit (`lemma_W_measure`);
* the assembly `vacuum_core` is in `VacuumMain`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Membership

/-- Splitting `∫_{(0,∞)} F` at `t_S ≤ t_Φ ≤ t_R`, dropping the part below `t_S` where `F ≤ 0`. -/
lemma split_integral_le {F : ℝ → ℝ} {tS tΦ tN tR : ℝ} (h0 : 0 ≤ tS) (hN : 0 < tN) (hSΦ : tS ≤ tΦ)
    (hNΦ : tN ≤ tΦ) (hΦR : tΦ ≤ tR) (hint : IntegrableOn F (Ioi 0))
    (hneg : ∀ t ∈ Ioc 0 tS, F t ≤ 0) :
    ∫ t in Ioi 0, F t ≤ (∫ t in tS..tΦ, F t) + (∫ t in Icc tN tR, |F t|) + ∫ t in Ici tR, |F t| := by
  have hS : IntegrableOn F (Ioi tS) := hint.mono_set (Ioi_subset_Ioi h0)
  have hΦ : IntegrableOn F (Ioi tΦ) := hS.mono_set (Ioi_subset_Ioi hSΦ)
  have hR : IntegrableOn F (Ioi tR) := hΦ.mono_set (Ioi_subset_Ioi hΦR)
  have hc1 : IntegrableOn F (Ioc 0 tS) := hint.mono_set Ioc_subset_Ioi_self
  have hc2 : IntegrableOn F (Ioc tS tΦ) := hS.mono_set Ioc_subset_Ioi_self
  have hc3 : IntegrableOn F (Ioc tΦ tR) := hΦ.mono_set Ioc_subset_Ioi_self
  have e1 : ∫ t in Ioi 0, F t = (∫ t in Ioc 0 tS, F t) + ∫ t in Ioi tS, F t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hc1 hS,
      Ioc_union_Ioi_eq_Ioi h0]
  have e2 : ∫ t in Ioi tS, F t = (∫ t in Ioc tS tΦ, F t) + ∫ t in Ioi tΦ, F t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hc2 hΦ,
      Ioc_union_Ioi_eq_Ioi hSΦ]
  have e3 : ∫ t in Ioi tΦ, F t = (∫ t in Ioc tΦ tR, F t) + ∫ t in Ioi tR, F t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hc3 hR,
      Ioc_union_Ioi_eq_Ioi hΦR]
  have i1 : ∫ t in Ioc 0 tS, F t ≤ 0 := setIntegral_nonpos measurableSet_Ioc hneg
  have habs : IntegrableOn (fun t => |F t|) (Ioi tR) := hR.abs
  have iabs : IntegrableOn (fun t => |F t|) (Icc tN tR) :=
    (hint.mono_set fun t ht => lt_of_lt_of_le hN ht.1).abs
  have i3 : ∫ t in Ioc tΦ tR, F t ≤ ∫ t in Icc tN tR, |F t| := by
    calc ∫ t in Ioc tΦ tR, F t ≤ ∫ t in Ioc tΦ tR, |F t| :=
          setIntegral_mono_on hc3 hc3.abs measurableSet_Ioc fun t _ => le_abs_self _
      _ ≤ ∫ t in Icc tN tR, |F t| :=
          setIntegral_mono_set iabs (Eventually.of_forall fun t => abs_nonneg _)
            (Eventually.of_forall fun t ht => ⟨hNΦ.trans ht.1.le, ht.2⟩)
  have i4 : ∫ t in Ioi tR, F t ≤ ∫ t in Ici tR, |F t| := by
    rw [integral_Ici_eq_integral_Ioi]
    exact setIntegral_mono_on hR habs measurableSet_Ioi fun t _ => le_abs_self _
  rw [e1, e2, e3, intervalIntegral.integral_of_le hSΦ]
  linarith

/-- The window part: if `g(φ σ) φ'(σ) ≤ FK (w σ + ε')` on `[-S, Φ]`, then
`∫_{t_S}^{t_Φ} g ≤ FK (∫_{-S}^{Φ} w + ε' (Φ + S))`. -/
lemma window_part_le {c' FK ε' S Φ : ℝ} (hc' : 0 ≤ c') {g w : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) (hw : Continuous w) (hSΦ : -S ≤ Φ)
    (hpt : ∀ σ ∈ Icc (-S) Φ, g (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
        ((2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c') ≤ FK * (w σ + ε')) :
    ∫ t in (c' * (xiStar + lambdaComb c' * (-S)) ^ 2 / 3)..(c' * (xiStar + lambdaComb c' * Φ) ^ 2 / 3), g t ≤
      FK * ((∫ σ in (-S)..Φ, w σ) + ε' * (Φ + S)) := by
  rw [← integral_sub_window hc' g hg]
  have hφ : Continuous fun σ : ℝ => c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3 := by fun_prop
  have hG : Continuous fun σ : ℝ => g (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
      ((2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c') := by
    refine Continuous.mul ?_ (by fun_prop)
    exact hg.comp_continuous hφ fun σ => mem_Ici.mpr (by positivity)
  have hmono := intervalIntegral.integral_mono_on hSΦ (hG.intervalIntegrable (μ := volume) _ _)
    (((hw.add continuous_const).const_mul FK).intervalIntegrable (μ := volume) _ _) hpt
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add (hw.intervalIntegrable (μ := volume) _ _)
    (continuous_const.intervalIntegrable (μ := volume) _ _)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.split_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_integral_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.window_part_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_part_le

end FormalResearch.ModularBootstrap.Upper.Positivity
