module

public import FormalResearch.SignUncertainty.CeLiftEdge
public import FormalResearch.SignUncertainty.ConvSourceTune

/-!
# The physical side of `thm:ce-hb-lift` (M6): tuning of `η_c` for the pair `D ± S`

`ceLift_tune`: for a source `S` and a one-level seed `D₀ = airySeedU2 a b c₀` of the same mass as `S`, there is a real `η` with
`|η| ≤ (2/k)(‖W_{D₀}(x)‖ + ‖W_S(x)‖)` such that the seed `D_η - S`, `D_η = airySeedU2 a (b + η) c₀`, has `W(x) - W(0) = 0`
(`x = c^{1/3}`), i.e. `f₋(0) = 0` for its `σ = -1` lift.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma airySeedU2_add_b (a b c₀ η : ℝ) :
    airySeedU2 a (b + η) c₀ = fun u => airySeedU2 a b c₀ u + η * ceG1 (airyZero 1) u := by
  funext u; simp only [airySeedU2]; ring

theorem ceLift_tune {S : ℝ → ℝ} (hS : HasU2 S) (a b c₀ : ℝ) {δ₀ : ℝ} (m : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hmass : ∫ u : ℝ, airySeedU2 a b c₀ u = ∫ u : ℝ, S u)
    (hgx : |(liftSymbol (ceG1 (airyZero 1)) δ₀ m (x : ℂ)).re| ≤ ceK / 2) :
    ∃ η : ℝ, |η| ≤ 2 / ceK * (‖liftSymbol (airySeedU2 a b c₀) δ₀ m (x : ℂ)‖ + ‖liftSymbol S δ₀ m (x : ℂ)‖) ∧
      liftSymbol (fun u => airySeedU2 a (b + η) c₀ u + (-1) * S u) δ₀ m (x : ℂ) -
        liftSymbol (fun u => airySeedU2 a (b + η) c₀ u + (-1) * S u) δ₀ m 0 = 0 := by
  have hk := ceK_pos
  have hD := hasU2_airySeedU2 a b c₀
  have hY : HasU2 (fun u => airySeedU2 a b c₀ u + (-1) * S u) := hD.add (hS.smul (-1))
  obtain ⟨η, hη, hb⟩ := exists_eta_tune hY (δ₀ := δ₀) m hx hgx
  refine ⟨η, ?_, ?_⟩
  · refine hb.trans ?_
    gcongr
    have hx' : 0 ≤ ((x : ℝ) : ℂ).re := by simpa using hx
    rw [liftSymbol_add_seed hD (hS.smul (-1)) δ₀ m hx', liftSymbol_add_seed hD (hS.smul (-1)) δ₀ m (by simp),
      liftSymbol_const_mul_seed, liftSymbol_const_mul_seed, liftSymbol_zero_eq hD, liftSymbol_zero_eq hS, hmass]
    have : liftSymbol (airySeedU2 a b c₀) δ₀ m (x : ℂ) + ((-1 : ℝ) : ℂ) * liftSymbol S δ₀ m (x : ℂ) -
        (((ceK * ∫ u : ℝ, S u : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * ((ceK * ∫ u : ℝ, S u : ℝ) : ℂ)) =
        liftSymbol (airySeedU2 a b c₀) δ₀ m (x : ℂ) - liftSymbol S δ₀ m (x : ℂ) := by push_cast; ring
    rw [this]
    exact norm_sub_le _ _
  · have e : (fun u => airySeedU2 a (b + η) c₀ u + (-1) * S u) =
        fun u => (airySeedU2 a b c₀ u + (-1) * S u) + η * ceG1 (airyZero 1) u := by
      funext u; simp only [airySeedU2]; ring
    rw [e]; exact hη

/-- info: 'FormalResearch.SignUncertainty.ceLift_tune' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceLift_tune

end FormalResearch.SignUncertainty
