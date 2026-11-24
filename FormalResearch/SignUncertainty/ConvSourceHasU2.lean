module

public import FormalResearch.SignUncertainty.ConvSourceLaplace
public import FormalResearch.SignUncertainty.ConvSourceWeight

/-!
# `HasU2` for the convolution source `S_c` (Lemma `O.12(1)`, `(3)` in the `HasU2` form) (M6)

`convWc_integrableOn`: the weight `w_c = γ ε e^{-y} + θ w_h` is integrable on `(0, ∞)`;
`hasU2_convSource`: `S_c = convSource p γ θ ε h` has the `U.2` package (integrability of `S_c e^{yu}` on
`Re y ≥ 0`, holomorphy of its twisted transform on `Re y > 0`, the bound `C ‖1 + w‖^{-5/2}` on `Re w ≥ 0`),
and `airyTwistedLaplaceC_convSource`: `S̃_c(z) = lapW w_c z · g̃₁(z)` for `Re z ≥ 0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma convWc_integrableOn {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) :
    IntegrableOn (convWc p γ θ ε h) (Ioi 0) := by
  unfold convWc
  have h1 : IntegrableOn (fun y : ℝ => γ * ε * Real.exp (-y)) (Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun y _ => by simp) measurableSet_Ioi).const_mul (γ * ε)
  exact h1.add ((convW_integrable hp hp1 hh).const_mul θ)

theorem hasU2_convSource {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) :
    HasU2 (convSource p γ θ ε h) := by
  rw [convSource_eq_convR]
  exact hasU2_convR (convWc_integrableOn hp hp1 hh) (continuous_ceG1 _) hasU2_ceG1

theorem airyTwistedLaplaceC_convSource {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h)
    {z : ℂ} (hz : 0 ≤ z.re) :
    airyTwistedLaplaceC (convSource p γ θ ε h) z =
      lapW (convWc p γ θ ε h) z * airyTwistedLaplaceC (ceG1 (airyZero 1)) z := by
  rw [convSource_eq_convR]
  exact airyTwistedLaplaceC_convR (convWc_integrableOn hp hp1 hh) (continuous_ceG1 _) hasU2_ceG1 hz

/-- info: 'FormalResearch.SignUncertainty.hasU2_convSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasU2_convSource

/-- info: 'FormalResearch.SignUncertainty.airyTwistedLaplaceC_convSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_convSource

end FormalResearch.SignUncertainty
