module

public import FormalResearch.SignUncertainty.HankelLangerSeries
public import FormalResearch.SignUncertainty.HankelLangerReal

/-!
# The Hankel Langer chart for the Dirichlet-eta coefficients (`gt:7.7b` (0)-(iv))

Instantiates `LangerEta` with `etaC j = η_D(2j+2)` (`HankelLangerSeries`), so that every chart statement of
`HankelLangerU`, `HankelLangerY`, `HankelLangerReal` holds for the actual coefficients of the Hankel Langer
coordinate.  (`aG etaC = langerA`, `aE etaC = langerB` are the coefficients of `HankelLangerSeries`.)
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

/-- The Dirichlet-eta coefficients `η_D(2j+2)` satisfy the hypotheses of the chart. -/
theorem langerEta_etaC : LangerEta etaC :=
  ⟨etaC_pos, fun j => (etaC_lt_one j).le, etaC_zero⟩

lemma aG_etaC (j : ℕ) : aG etaC j = langerA j := by unfold aG langerA; ring

lemma aE_etaC (j : ℕ) : aE etaC j = langerB j := by unfold aE langerB; ring

/-- `gt:7.7b` (iii) for the actual Dirichlet-eta coefficients. -/
theorem norm_chartY_etaC_add_le {w : ℂ} (hw : ‖w‖ ≤ 1e-3) :
    ‖chartY etaC w + w‖ ≤ 1.9e-3 * ‖w‖ :=
  norm_chartY_add_le langerEta_etaC hw

/-- info: 'FormalResearch.SignUncertainty.norm_chartY_etaC_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_chartY_etaC_add_le

end FormalResearch.SignUncertainty
