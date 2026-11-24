module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumCore
public import FormalResearch.ModularBootstrap.Upper.Rigidity.CrossingDictionary

/-!
# The vacuum limsup and the vacuum positivity for the two-zero comb (`upper_transfer.tex`, `ut:T2`, S5-S6)

For `prob.w = 1`, `g = twoZeroG d c = ½(h₂ - ĥ₂)` (`h₂ = combProfile c (twoZeroComb d c)`), `F = twoZeroF prob`,
`C₂ = twoZeroC₂ = C_* κ / 2`, and every compact family `𝒦` of admissible designs:

* `twoZero_testClass_eventually`, `twoZero_integrable_psiAiry`: `g ∈ Ā` and `Ψ_g ∈ L¹(du)` for `c` large;
* `twoZero_limsup_field`: the `limsup_le` field of `TwoZeroTransferData`, in exactly the quantifiers of the field,
  `F_c^{-1} ∫ Ψ_g ≤ C₂ ∫ W₂ + ε` for `c` large and `d ∈ 𝒦`;
* `twoZero_vac_eventually`: if `∫ W₂ ≤ -δ` on `𝒦` there is `κ > 0` with `κ c^{3/2} ≤ g_vac` for `c` large and `d ∈ 𝒦`
  (the `vac` field with a threshold `c₀` chosen after `δ`; see `twoZero_vac_field_of_threshold`).

The proof is the vacuum identity `∫ Ψ_g = -g_vac/(2π)`, `|g_vac + π ∫_0^∞ h₂ V| ≤ 2^m` (`K7`), and
`∫_0^∞ h₂ V ≤ F (C_* κ ∫ W₂ + ε)` (`twoZero_vacuum_core`).

All results are proved unconditionally (for `prob.w = 1`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Rigidity
open TwoZeroDesign

/-- Arithmetic of the limsup: `F^{-1} (-g_vac/(2π)) ≤ C₂ W + ε`. -/
lemma limsup_arith {F I gv W C₂ ε m₂ : ℝ} (hF : 0 < F) (hgv : |gv + π * I| ≤ m₂)
    (hI : I ≤ F * (2 * C₂ * W + ε)) (hbig : m₂ ≤ π * ε * F) :
    F⁻¹ * (-gv / (2 * π)) ≤ C₂ * W + ε := by
  have hπ := Real.pi_pos
  have h1 : -gv ≤ π * I + m₂ := by
    have := (abs_le.mp hgv).1
    linarith
  have h2 : -gv / (2 * π) ≤ F * (C₂ * W + ε) := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : π * I ≤ π * (F * (2 * C₂ * W + ε)) := mul_le_mul_of_nonneg_left hI hπ.le
    nlinarith
  rw [inv_mul_le_iff₀ hF]
  exact h2

/-- Arithmetic of the vacuum bound. -/
lemma vac_arith {F I gv W K δ ε m₂ : ℝ} (hF : 0 < F) (hK : 0 < K) (hgv : |gv + π * I| ≤ m₂)
    (hW : W ≤ -δ) (hε : ε = K * δ / 2) (hI : I ≤ F * (K * W + ε)) (hbig : m₂ ≤ π * K * δ / 4 * F) :
    π * K * δ / 4 * F ≤ gv := by
  have hπ := Real.pi_pos
  have h1 : -m₂ ≤ gv + π * I := (abs_le.mp hgv).1
  have h2 : F * (K * W + ε) ≤ F * (-(K * δ / 2)) := by
    apply mul_le_mul_of_nonneg_left _ hF.le
    rw [hε]
    nlinarith
  have h3 : π * I ≤ π * (F * (-(K * δ / 2))) := mul_le_mul_of_nonneg_left (hI.trans h2) hπ.le
  nlinarith

/-- `F_{2,c} → ∞`: `F ≥ M` for `c` large. -/
lemma twoZeroF_eventually_ge (prob : FixedWeightProblem) (M : ℝ) :
    ∀ᶠ c : ℝ in atTop, M ≤ twoZeroF prob c := by
  have hF := twoZeroFConst_pos prob
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).eventually_ge_atTop (M / twoZeroFConst prob)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with c hc hc0
  rw [twoZeroF_eq_const_mul prob hc0]
  rwa [div_le_iff₀ hF, mul_comm] at hc

/-- `g = ½(h₂ - ĥ₂) ∈ Ā` (`TestClass`) for `c` large and `d ∈ 𝒦`. -/
theorem twoZero_testClass_eventually (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, TestClass prob (c / 12) (twoZeroG d c) := by
  filter_upwards [twoZeroComb_k7_membership_vacuum hw hK hA] with c hK7 d hd
  obtain ⟨C, hC0, -, -, hT, -⟩ := hK7 d hd
  exact hT

/-- **Integrability of `Ψ_g`** for the two-zero comb: `Ψ_g ∈ L¹(du)` for `c` large and `d ∈ 𝒦`
(`ut:T2`; needed to apply the window and vacuum clauses of `TwoZeroTransferData`). -/
theorem twoZero_integrable_psiAiry (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, Integrable (psiAiry prob c (twoZeroG d c)) := by
  filter_upwards [twoZero_testClass_eventually prob hw hK hA, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (12 * prob.totalShift)] with c hT hc hcS d hd
  exact integrable_psiAiry_of_testClass prob hc (by linarith) (hT d hd)

/-- **The `limsup_le` field of `TwoZeroTransferData`** (`ut:T2`, S5-S6), with the exact quantifiers of the field:
for `ε > 0`, `c` large and all `d ∈ 𝒦`, `F_c^{-1} ∫ Ψ_g ≤ C₂ ∫ W₂ + ε`. -/
theorem twoZero_limsup_field (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦,
      (twoZeroF prob c)⁻¹ * (∫ u, psiAiry prob c (twoZeroG d c) u) ≤ twoZeroC₂ * (∫ u, d.Wr u) + ε := by
  intro ε hε
  filter_upwards [twoZero_vacuum_core prob hw hK hA hε, twoZero_gVac_bounds prob hw hK hA,
    eventually_gt_atTop (0 : ℝ), twoZeroF_eventually_ge prob (2 ^ prob.m / (π * ε))]
    with c hV hg hc hFbig d hd
  have hFpos := twoZeroF_pos prob hc
  rw [integral_psiAiry_eq_neg_gVac prob hc]
  refine limsup_arith (I := ∫ t in Ioi 0, combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t)
    hFpos (hg d hd) ?_ ?_
  · have : 2 * twoZeroC₂ = CStar * kappaAiry := by unfold twoZeroC₂; ring
    rw [this]
    exact hV d hd
  · have hπ := Real.pi_pos
    rw [div_le_iff₀ (by positivity)] at hFbig
    linarith

/-- **Vacuum positivity** (`ut:T2`, the `vac` clause): if `∫ W₂ ≤ -δ` on `𝒦`, there are `κ > 0` and a threshold
beyond which `κ c^{3/2} ≤ g_vac` for all `d ∈ 𝒦`. -/
theorem twoZero_vac_eventually (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦,
      κ * c ^ ((3 : ℝ) / 2) ≤ prob.gVac (c / 12) (twoZeroG d c) := by
  obtain ⟨δ, hδ0, hW⟩ := hδ
  have hC := CStar_pos
  have hκ := kappaAiry_pos
  obtain ⟨A, B, hA0, hB0, hAB⟩ := twoZeroF_asymp prob
  have hK0 : 0 < CStar * kappaAiry := by positivity
  have hε : 0 < CStar * kappaAiry * δ / 2 := by positivity
  have hπ := Real.pi_pos
  refine ⟨π * (CStar * kappaAiry) * δ / 4 * A, by positivity, ?_⟩
  filter_upwards [twoZero_vacuum_core prob hw hK hA hε, twoZero_gVac_bounds prob hw hK hA,
    eventually_gt_atTop (0 : ℝ),
    twoZeroF_eventually_ge prob (2 ^ prob.m / (π * (CStar * kappaAiry) * δ / 4))]
    with c hV hg hc hFbig d hd
  have hFpos := twoZeroF_pos prob hc
  have hpos : 0 < π * (CStar * kappaAiry) * δ / 4 := by positivity
  rw [div_le_iff₀ hpos] at hFbig
  have h := vac_arith (F := twoZeroF prob c) (K := CStar * kappaAiry) (δ := δ) hFpos hK0 (hg d hd)
    (hW d hd) rfl (hV d hd) (by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hAB c hc).1 hpos.le
  linarith

/-- The `vac` field in the form of `TwoZeroTransferData`: for any threshold `c₁` beyond which the previous
theorem holds, the clause `∀ c ≥ c₀` holds for every `c₀ ≥ c₁`. -/
theorem twoZero_vac_field_of_threshold (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ c₁ : ℝ, ∀ c₀ : ℝ, c₁ ≤ c₀ → ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦,
      κ * c ^ ((3 : ℝ) / 2) ≤ prob.gVac (c / 12) (twoZeroG d c) := by
  obtain ⟨κ, hκ, h⟩ := twoZero_vac_eventually prob hw hK hA hδ
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp h
  exact ⟨κ, hκ, c₁, fun c₀ h0 c hc d hd => hc₁ c (h0.trans hc) d hd⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_testClass_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_testClass_eventually

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_integrable_psiAiry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_integrable_psiAiry

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_limsup_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_limsup_field

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_vac_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_vac_eventually

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_vac_field_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_vac_field_of_threshold

end FormalResearch.ModularBootstrap.TwoLevel
