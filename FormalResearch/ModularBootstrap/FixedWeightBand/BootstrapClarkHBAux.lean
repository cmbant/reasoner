module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapClarkNodes
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWHB

/-!
# Auxiliary Facts for the `m₀ = 2` Hermite--Biehler Bootstrap Instance (Theorem `FT-L.FW`, Clark pairs)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Steps 0-2, and
Theorem `W1'(2)` (`wone:genlower`(2)).

* `LemmaQData.deltaChart_err`: two-sided quadratic chart error `|Δ(u) - (ξ̄ c' - c_* c'^{1/3} u)| ≤ C_ξ c'^{-1/3} u²`
  on the full-scale disc;
* `LemmaQData.exists_chartPoint_near`: the prescribed level `t₁ = ξ̄ c' - c_* c'^{1/3} u₁ + r`, `|r| ≤ R_off`, is the
  chart image `Δ(ũ)` of a point `ũ` with `|ũ - u₁| ≤ D₁ c'^{-1/3}`, `D₁ = (R_off + 1)/c_*` (Step 1, prescribed nodes);
* `uT_range_of_violatorClark`: range of a violator threshold `u_T ∈ (z₂, z₂ + 1/2]` in the chart (the Clark version of
  `uT_range_of_violatorW_thr`);
* `clark_uT_close_firstLevel`: `x̃ = u_T - z₂ ≤ ε` for every `ε > 0` (`teb:quant_c1_hb`(2)), uniformly in the first
  level `u₁` of a compact set;
* `exists_sin_lower_clarkAngle`: `|sin α(u₁)| ≥ σ > 0` uniformly for `u₁` in a compact subset of `(a₁, ∞)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip FormalResearch.SignUncertainty TwoLevel

variable {prob : FixedWeightProblem}

/-! ### The two-sided chart error -/

/-- The quadratic chart error of Step 5 of `wone:ftlfw` in two-sided form on the full-scale disc. -/
lemma LemmaQData.deltaChart_err (Q : LemmaQData prob) {c' u : ℝ} (hc' : 0 < c')
    (hu : |u| ≤ Q.AC c' ^ 2) :
    |virasoroDeltaChart c' u - (xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u)| ≤
      chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u ^ 2 :=
  virasoro_deltaChart_err hc' (Q.abs_le_virasoro hc'.le hu)

lemma rpow_third_mul_rpow_neg_third {c' : ℝ} (hc' : 0 < c') :
    c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
  rw [← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero]

/-- **The prescribed level is a chart image** (Step 1 of `wone:ftlfw`, prescribed nodes): if
`|t - (ξ̄ c' - c_* c'^{1/3} u₁)| ≤ R_off`, `D = (R_off + 1)/c_*`, the window `|u₁| + D c'^{-1/3}` lies in the disc and the
chart remainder is at most `1` there, then `t = Δ(ũ)` with `|ũ - u₁| ≤ D c'^{-1/3}`. -/
lemma LemmaQData.exists_chartPoint_near (Q : LemmaQData prob) {c' u₁ R_off D : ℝ} (hc' : 0 < c')
    (hR : 0 ≤ R_off) (hD : D = (R_off + 1) / cStar)
    (hdom : |u₁| + D * c' ^ (-(1 / 3 : ℝ)) ≤ Q.AC c' ^ 2)
    (herr : chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * (|u₁| + D * c' ^ (-(1 / 3 : ℝ))) ^ 2 ≤ 1)
    {t : ℝ} (ht : |t - (xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u₁)| ≤ R_off) :
    ∃ ũ : ℝ, |ũ - u₁| ≤ D * c' ^ (-(1 / 3 : ℝ)) ∧ virasoroDeltaChart c' ũ = t := by
  have hc := cStar_pos
  have hD_nn : 0 ≤ D := by rw [hD]; positivity
  set s : ℝ := D * c' ^ (-(1 / 3 : ℝ)) with hs
  have hp : 0 < c' ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hs_nn : 0 ≤ s := by positivity
  have hcs : c' ^ (1 / 3 : ℝ) * s = D := by
    rw [hs, ← mul_assoc, mul_comm (c' ^ (1 / 3 : ℝ)) D, mul_assoc, rpow_third_mul_rpow_neg_third hc',
      mul_one]
  have hcD : cStar * D = R_off + 1 := by rw [hD]; field_simp
  have hCξ := chartParams.hCxi_nn
  have hε_nn : 0 ≤ chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) := by positivity
  set L : ℝ := xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u₁ with hL
  have hmem : ∀ u : ℝ, |u - u₁| ≤ s → |u| ≤ Q.AC c' ^ 2 ∧
      chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u ^ 2 ≤ 1 := by
    intro u hu
    have h1 : |u| ≤ |u₁| + s := by
      calc |u| = |(u - u₁) + u₁| := by ring_nf
        _ ≤ |u - u₁| + |u₁| := abs_add_le _ _
        _ ≤ |u₁| + s := by linarith
    refine ⟨h1.trans hdom, ?_⟩
    have h2 : u ^ 2 ≤ (|u₁| + s) ^ 2 := by
      rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u ^ 2
        ≤ chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * (|u₁| + s) ^ 2 := by gcongr
      _ ≤ 1 := herr
  have hlo : u₁ - s ≤ u₁ + s := by linarith
  have hcont : ContinuousOn (virasoroDeltaChart c') (Icc (u₁ - s) (u₁ + s)) := by
    intro u hu
    have hu' : |u - u₁| ≤ s := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact (Q.deltaChart_hasDerivAt hc' (hmem u hu').1).continuousAt.continuousWithinAt
  have hab := abs_le.mp ht
  have hleft : t ≤ virasoroDeltaChart c' (u₁ - s) := by
    have hu' : |(u₁ - s) - u₁| ≤ s := by rw [show u₁ - s - u₁ = -s by ring, abs_neg, abs_of_nonneg hs_nn]
    obtain ⟨-, hE⟩ := hmem _ hu'
    have h := (abs_le.mp (Q.deltaChart_err hc' (hmem _ hu').1)).1
    have e1 : cStar * c' ^ (1 / 3 : ℝ) * (u₁ - s) = cStar * c' ^ (1 / 3 : ℝ) * u₁ - cStar * D := by
      rw [← hcs]; ring
    rw [e1] at h
    linarith
  have hright : virasoroDeltaChart c' (u₁ + s) ≤ t := by
    have hu' : |(u₁ + s) - u₁| ≤ s := by rw [show u₁ + s - u₁ = s by ring, abs_of_nonneg hs_nn]
    obtain ⟨-, hE⟩ := hmem _ hu'
    have h := (abs_le.mp (Q.deltaChart_err hc' (hmem _ hu').1)).2
    have e1 : cStar * c' ^ (1 / 3 : ℝ) * (u₁ + s) = cStar * c' ^ (1 / 3 : ℝ) * u₁ + cStar * D := by
      rw [← hcs]; ring
    rw [e1] at h
    linarith
  obtain ⟨u, hu, hut⟩ := intermediate_value_Icc' hlo hcont ⟨hright, hleft⟩
  exact ⟨u, abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩, hut⟩

/-! ### Range of the violator threshold -/

/-- **Range of the violator threshold at the second level** (the Clark version of `uT_range_of_violatorW_thr`): for a
violator `Δ(A_{c'}²) ≤ T < Δ(z)` with `z < a₁`, `z ≥ -A_{c'}²` and `u_T - z ≤ 1/2`, one has `z < u_T ≤ -1`,
`Δ(0) ≤ T`, `Δ(-1) ≤ T` and `T ≤ Δ(-R)` for every `R ≥ |z|` with `R ≤ A_{c'}²`. -/
lemma uT_range_of_violatorClark [Q : LemmaQData prob] {c' T z R : ℝ} (hc' : Q.cQ ≤ c')
    (hz_lo : -(Q.AC c' ^ 2) ≤ z) (hz_a1 : z < airyZero 1)
    (hAC : 4 ≤ Q.AC c' ^ 2)
    (hT_A2 : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ T)
    (hT_z : T < virasoroDeltaChart c' z) (hx : virasoroUT c' T - z ≤ 1 / 2)
    (hzR : |z| ≤ R) (hR_ub : R ≤ Q.AC c' ^ 2) :
    z < virasoroUT c' T ∧ virasoroUT c' T ≤ -1 ∧ virasoroDeltaChart c' (-1) ≤ T ∧
      virasoroDeltaChart c' 0 ≤ T ∧ T ≤ virasoroDeltaChart c' (-R) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have ha1 := airyZero_one
  have hz_neg : z < 0 := by linarith [ha1.2]
  obtain ⟨huT_gt, huT_AC, huT_Δ⟩ := uT_facts (z := z) hc' hz_lo
    (by linarith [sq_nonneg (Q.AC c')]) hT_A2 hT_z
  set u_T := virasoroUT c' T
  have huT_m1 : u_T ≤ -1 := by linarith [ha1.2]
  have hlo : -(Q.AC c' ^ 2) ≤ u_T := by linarith
  have hanti := Q.deltaChart_strictAnti hc'_pos
  refine ⟨huT_gt, huT_m1, ?_, ?_, ?_⟩
  · rw [← huT_Δ]
    exact hanti.antitoneOn ⟨hlo, huT_AC⟩ ⟨by linarith, by linarith⟩ huT_m1
  · rw [← huT_Δ]
    exact hanti.antitoneOn ⟨hlo, huT_AC⟩ ⟨by linarith, by linarith⟩ (by linarith)
  · rw [← huT_Δ]
    have hzR' : -R ≤ z := by linarith [neg_abs_le z]
    exact hanti.antitoneOn ⟨by linarith, by linarith [sq_nonneg (Q.AC c')]⟩ ⟨hlo, huT_AC⟩
      (by linarith)

/-! ### `x̃ ≤ ε` and the uniform sine bound -/

/-- `x̃ = u_T - z₂ ≤ ε` for every `ε > 0` (`teb:quant_c1_hb`(2)), uniformly for the first level `u₁` in a compact
`K ⊂ (a₁, ∞)`: `clark_uT_close` with `γ = Ai'(u₁)/Ai(u₁)`. -/
theorem clark_uT_close_firstLevel {C_0 : ℝ} (hC0 : 0 < C_0)
    (R_dom ς δ_lobe ρ : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hς_nn : ∀ᶠ c in atTop, 0 ≤ ς c) (hς_lim : Tendsto ς atTop (𝓝 0))
    (hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c) (hδ_lim : Tendsto δ_lobe atTop (𝓝 0))
    (hρ_lim : Tendsto ρ atTop (𝓝 0))
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioi (airyZero 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ c₁ : ℝ, 2 ≤ c₁ ∧ ∀ c' : ℝ, c₁ ≤ c' → ∀ u₁ ∈ K, ∀ (Ψ : ℂ → ℂ) (u_T ũ : ℝ),
      QuantC1ClarkHyp C_0 (R_dom c') (ς c') (δ_lobe c') (ρ c') (airyRatio u₁) Ψ u_T ũ →
      u_T - airyClarkNode (airyRatio u₁) 2 ≤ ε := by
  have hcont : ContinuousOn airyRatio K :=
    (continuousOn_airyRatio (n := 1) le_rfl).mono fun u hu => by
      rw [airyClarkGap_one]; exact hKsub hu
  obtain ⟨c₁, hc₁, h⟩ := clark_uT_close hC0 R_dom ς δ_lobe ρ hR_lim hς_nn hς_lim hδ_nn hδ_lim hρ_lim
    (hK.image_of_continuousOn hcont) hε
  exact ⟨c₁, hc₁, fun c' hc' u₁ hu₁ Ψ u_T ũ hΨ => h c' hc' (airyRatio u₁) (mem_image_of_mem _ hu₁) Ψ u_T ũ hΨ⟩

/-- `|sin α(u₁)| ≥ σ > 0` uniformly for `u₁` in a compact subset of `(a₁, ∞)`: `cot α = Ai'(u₁)/Ai(u₁)` is
bounded there. -/
theorem exists_sin_lower_clarkAngle {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioi (airyZero 1)) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ u ∈ K, σ ≤ |Real.sin (clarkAngle u)| := by
  have hcont : ContinuousOn airyRatio K :=
    (continuousOn_airyRatio (n := 1) le_rfl).mono fun u hu => by
      rw [airyClarkGap_one]; exact hKsub hu
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨1 / (1 + max B 0), by positivity, fun u hu => ?_⟩
  have hu1 := hKsub hu
  have hs := sin_clarkAngle_ne_zero hu1
  have hcot := cot_clarkAngle hu1
  have hcos : Real.cos (clarkAngle u) = airyRatio u * Real.sin (clarkAngle u) := by
    rw [← hcot]; field_simp
  have hpyth := Real.sin_sq_add_cos_sq (clarkAngle u)
  rw [hcos] at hpyth
  have hr : |airyRatio u| ≤ max B 0 := by
    have := hB u hu
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hr2 : airyRatio u ^ 2 ≤ (max B 0) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  have h1 : 1 ≤ (|Real.sin (clarkAngle u)| * (1 + max B 0)) ^ 2 := by
    have e : (|Real.sin (clarkAngle u)| * (1 + max B 0)) ^ 2 =
        Real.sin (clarkAngle u) ^ 2 * (1 + max B 0) ^ 2 := by rw [mul_pow, sq_abs]
    rw [e]
    nlinarith [sq_nonneg (Real.sin (clarkAngle u)), sq_nonneg (max B 0), hr2]
  have h2 : 1 ≤ |Real.sin (clarkAngle u)| * (1 + max B 0) := by
    by_contra hlt
    push Not at hlt
    have h0 : 0 ≤ |Real.sin (clarkAngle u)| * (1 + max B 0) := by positivity
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.exists_chartPoint_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.exists_chartPoint_near

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.uT_range_of_violatorClark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uT_range_of_violatorClark

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.clark_uT_close_firstLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_uT_close_firstLevel

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.exists_sin_lower_clarkAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_sin_lower_clarkAngle

end FormalResearch.ModularBootstrap.FixedWeightBand
