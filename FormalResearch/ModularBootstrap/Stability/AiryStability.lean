module

public import FormalResearch.ModularBootstrap.Stability.AiryStabilityLower

/-!
# Theorem B-stab (`rem:thmBstab`): stability of the Airy equality case

Source: `CFT/modular_bootstrap/paper/remainder.tex`, Theorem B-stab, the Airy case (`m = 1`,
`(P, Q) = (1, 0)`, `D = 1`, `‖G_N‖₁ = 2L_*`) of `se:terminal-stability`
(`soft_edge_two_level_stability.tex`).

`airyStabI δ = I(δ) = inf { ∫ f/‖f‖₁ : f ∈ 𝒢 \ 0, f ≥ 0 on (-∞, a₁ + δ] }`.

* `airy_stability`: `I(δ) > 0` for `δ > 0`, and `I(δ)/δ → 1/‖G_Ai‖₁ = 1/quantC1Mass` as `δ ↓ 0`
  (`quantC1Mass = ‖G_Ai‖₁ = 2L_*`; the numerical value `1.2180230048…` is not formalised).

Upper bound: the trial function `Ai(u)²(a₁ + δ - u)/(a₁ - u)²` (`foldTipSeed (-δ) 0`), with
`∫ = δ` (`foldTipSeed_integral`, Theorem Q) and `‖·‖₁ → ‖G_Ai‖₁`.  Lower bound:
`airy_stab_lower` (`AiryStabilityLower`).  Positivity for every `δ`: monotonicity of `I`.

Convention: the nonvanishing `f ≢ 0` is `∃ x : ℝ, f x ≠ 0` (equivalent for entire `f`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.TwoEdgeBootstrap

/-- The admissible ratios at threshold `a₁ + δ`. -/
def airyStabSet (δ : ℝ) : Set ℝ :=
  {r | ∃ f : ℂ → ℂ, AiryG f ∧ (∃ x : ℝ, f (x : ℂ) ≠ 0) ∧
    (∀ x : ℝ, x ≤ airyZero 1 + δ → 0 ≤ (f (x : ℂ)).re) ∧
    r = (∫ x : ℝ, (f (x : ℂ)).re) / ∫ x : ℝ, ‖f (x : ℂ)‖}

/-- `I(δ)` of Theorem B-stab. -/
noncomputable def airyStabI (δ : ℝ) : ℝ := sInf (airyStabSet δ)

/-- The trial function `Ai(u)² (a₁ + δ - u)/(a₁ - u)²`. -/
noncomputable abbrev airyTrial (δ : ℝ) : ℂ → ℂ := foldTipSeed (-δ) 0

lemma airyTrial_G (δ : ℝ) : AiryG (airyTrial δ) where
  diff := differentiable_foldTipSeed _ _
  integrable := foldTipSeed_integrable _ _
  growth := by
    obtain ⟨C, hC, hb⟩ := foldTipSeed_bound (-δ) 0
    exact ⟨C, -(3 / 2), hC, hb⟩
  real := foldTipSeed_ofReal_im _ _

lemma dslope_ofReal_real (x : ℝ) : ∃ d : ℝ, dslope airyAiC (airyZero 1 : ℂ) (x : ℂ) = (d : ℂ) := by
  by_cases hx : x = airyZero 1
  · exact ⟨airyAi' (airyZero 1), by rw [hx, dslope_same, deriv_airyAiC_ofReal]⟩
  · have hxc : (x : ℂ) ≠ (airyZero 1 : ℂ) := fun h => hx (Complex.ofReal_injective h)
    refine ⟨airyAi x / (x - airyZero 1), ?_⟩
    rw [dslope_of_ne _ hxc, slope_def_field, airyAiC_airyZero, sub_zero, airyAiC_ofReal,
      ← Complex.ofReal_sub, ← Complex.ofReal_div]

lemma airyTrial_eq (δ : ℝ) (u : ℂ) :
    airyTrial δ u = dslope airyAiC (airyZero 1 : ℂ) u ^ 2 * (((airyZero 1 + δ : ℝ) : ℂ) - u) := by
  unfold airyTrial foldTipSeed
  simp

lemma airyTrial_re_nonneg {δ x : ℝ} (hx : x ≤ airyZero 1 + δ) : 0 ≤ (airyTrial δ (x : ℂ)).re := by
  obtain ⟨d, hd⟩ := dslope_ofReal_real x
  rw [airyTrial_eq, hd]
  have : ((d : ℂ) ^ 2 * (((airyZero 1 + δ : ℝ) : ℂ) - (x : ℂ))) =
      ((d ^ 2 * (airyZero 1 + δ - x) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]
  exact mul_nonneg (sq_nonneg _) (by linarith)

lemma airyTrial_integral (δ : ℝ) : ∫ x : ℝ, (airyTrial δ (x : ℂ)).re = δ := by
  rw [(airyTrial_G δ).re_integral]
  have := foldTipSeed_integral (-δ) 0
  rw [this, Complex.ofReal_re]
  ring

lemma airyTrial_ne (δ : ℝ) (hδ : 0 < δ) : ∃ x : ℝ, airyTrial δ (x : ℂ) ≠ 0 := by
  by_contra h
  push Not at h
  have : ∫ x : ℝ, (airyTrial δ (x : ℂ)).re = 0 := by simp [h]
  rw [airyTrial_integral] at this
  linarith

lemma airyTrial_lin (δ : ℝ) (u : ℂ) :
    airyTrial δ u = airyExtremal u + (δ : ℂ) * (airyTrial 1 u - airyExtremal u) := by
  have h := sub_smul_dslope airyAiC (airyZero 1 : ℂ) u
  rw [smul_eq_mul, airyAiC_airyZero 1, sub_zero] at h
  rw [airyTrial_eq, airyTrial_eq]
  unfold airyExtremal
  rw [← h]
  push_cast
  ring

lemma tendsto_airyTrial_mass :
    Tendsto (fun δ : ℝ => ∫ x : ℝ, ‖airyTrial δ (x : ℂ)‖) (𝓝[>] 0)
      (𝓝 (profileMass airyExtremal)) := by
  set W : ℂ → ℂ := fun u => airyTrial 1 u - airyExtremal u with hW
  have hWi : Integrable (fun x : ℝ => W (x : ℂ)) :=
    (airyTrial_G 1).integrable.sub airyExtremal_integrable
  set w : ℝ := ∫ x : ℝ, ‖W (x : ℂ)‖ with hw
  have hGi := airyExtremal_integrable.norm
  have hupper : ∀ δ : ℝ, 0 ≤ δ → ∫ x : ℝ, ‖airyTrial δ (x : ℂ)‖ ≤ profileMass airyExtremal + δ * w := by
    intro δ hδ
    have hint : Integrable (fun x : ℝ => ‖airyExtremal (x : ℂ)‖ + δ * ‖W (x : ℂ)‖) :=
      hGi.add (hWi.norm.const_mul δ)
    calc ∫ x : ℝ, ‖airyTrial δ (x : ℂ)‖ ≤ ∫ x : ℝ, (‖airyExtremal (x : ℂ)‖ + δ * ‖W (x : ℂ)‖) := by
          refine integral_mono (airyTrial_G δ).integrable_norm hint fun x => ?_
          rw [airyTrial_lin]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have : |δ| = δ := abs_of_nonneg hδ
          rw [this]
      _ = profileMass airyExtremal + δ * w := by
          rw [integral_add hGi (hWi.norm.const_mul δ), integral_const_mul]; rfl
  have hlower : ∀ δ : ℝ, 0 ≤ δ → profileMass airyExtremal - δ * w ≤ ∫ x : ℝ, ‖airyTrial δ (x : ℂ)‖ := by
    intro δ hδ
    have hint : Integrable (fun x : ℝ => ‖airyTrial δ (x : ℂ)‖ + δ * ‖W (x : ℂ)‖) :=
      (airyTrial_G δ).integrable_norm.add (hWi.norm.const_mul δ)
    have h1 : ∫ x : ℝ, ‖airyExtremal (x : ℂ)‖ ≤
        ∫ x : ℝ, (‖airyTrial δ (x : ℂ)‖ + δ * ‖W (x : ℂ)‖) := by
      refine integral_mono hGi hint fun x => ?_
      have : airyExtremal (x : ℂ) = airyTrial δ (x : ℂ) - (δ : ℂ) * W (x : ℂ) := by
        rw [airyTrial_lin δ]; simp only [hW]; ring
      rw [this]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
    rw [integral_add (airyTrial_G δ).integrable_norm (hWi.norm.const_mul δ), integral_const_mul] at h1
    have : profileMass airyExtremal = ∫ x : ℝ, ‖airyExtremal (x : ℂ)‖ := rfl
    linarith
  have hlim : ∀ s : ℝ, Tendsto (fun δ : ℝ => profileMass airyExtremal + s * δ * w) (𝓝[>] 0)
      (𝓝 (profileMass airyExtremal)) := by
    intro s
    have hc : Continuous (fun δ : ℝ => profileMass airyExtremal + s * δ * w) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun δ => profileMass airyExtremal + (-1) * δ * w)
    (h := fun δ => profileMass airyExtremal + 1 * δ * w) (hlim (-1)) (hlim 1) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have := hlower δ (le_of_lt hδ)
    linarith
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have := hupper δ (le_of_lt hδ)
    linarith

lemma airyStabSet_bdd {δ : ℝ} (hδ : 0 ≤ δ) : BddBelow (airyStabSet δ) := by
  refine ⟨0, ?_⟩
  rintro r ⟨f, hf, -, hnn, rfl⟩
  exact div_nonneg (hf.quadrature_ge fun x hx => hnn x (by linarith)).1
    (integral_nonneg fun x => norm_nonneg _)

lemma airyStabSet_nonempty {δ : ℝ} (hδ : 0 < δ) : (airyStabSet δ).Nonempty :=
  ⟨δ / ∫ x : ℝ, ‖airyTrial δ (x : ℂ)‖, airyTrial δ, airyTrial_G δ, airyTrial_ne δ hδ,
    fun x hx => airyTrial_re_nonneg hx, by rw [airyTrial_integral]⟩

lemma airyStabI_le_trial {δ : ℝ} (hδ : 0 < δ) :
    airyStabI δ ≤ δ / ∫ x : ℝ, ‖airyTrial δ (x : ℂ)‖ :=
  csInf_le (airyStabSet_bdd hδ.le)
    ⟨airyTrial δ, airyTrial_G δ, airyTrial_ne δ hδ, fun x hx => airyTrial_re_nonneg hx,
      by rw [airyTrial_integral]⟩

lemma le_airyStabI {δ θ : ℝ} (hδ : 0 < δ)
    (h : ∀ f : ℂ → ℂ, AiryG f → (∃ x : ℝ, f (x : ℂ) ≠ 0) →
      (∀ x : ℝ, x ≤ airyZero 1 + δ → 0 ≤ (f (x : ℂ)).re) →
      θ * δ ≤ (∫ x : ℝ, (f (x : ℂ)).re) / ∫ x : ℝ, ‖f (x : ℂ)‖) : θ * δ ≤ airyStabI δ := by
  refine le_csInf (airyStabSet_nonempty hδ) ?_
  rintro r ⟨f, hf, hne, hnn, rfl⟩
  exact h f hf hne hnn

lemma airyStabI_mono {δ δ' : ℝ} (hδ' : 0 < δ') (hle : δ' ≤ δ) : airyStabI δ' ≤ airyStabI δ := by
  refine csInf_le_csInf (airyStabSet_bdd hδ'.le) (airyStabSet_nonempty (hδ'.trans_le hle)) ?_
  rintro r ⟨f, hf, hne, hnn, rfl⟩
  exact ⟨f, hf, hne, fun x hx => hnn x (by linarith), rfl⟩

/-- **Theorem B-stab (`rem:thmBstab`).**  `I(δ) > 0` for every `δ > 0`, and
`I(δ)/δ → 1/‖G_Ai‖₁ = 1/(2L_*)` as `δ ↓ 0` (`quantC1Mass = ‖G_Ai‖₁ = 2L_*`). -/
theorem airy_stability :
    (∀ δ : ℝ, 0 < δ → 0 < airyStabI δ) ∧
      Tendsto (fun δ : ℝ => airyStabI δ / δ) (𝓝[>] 0) (𝓝 quantC1Mass⁻¹) := by
  have hM : profileMass airyExtremal = quantC1Mass := rfl
  have hMpos : 0 < quantC1Mass := quantC1Mass_pos
  refine ⟨?_, ?_⟩
  · intro δ hδ
    obtain ⟨δ₀, hδ₀, hlow⟩ := airy_stab_lower (θ := quantC1Mass⁻¹ / 2) (by
      rw [← hM]; have := inv_pos.mpr hMpos; rw [hM]; linarith)
    set δ' := min δ (δ₀ / 2) with hδ'
    have hδ'pos : 0 < δ' := lt_min hδ (half_pos hδ₀)
    have hδ'lt : δ' < δ₀ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ₀)
    have h1 : quantC1Mass⁻¹ / 2 * δ' ≤ airyStabI δ' :=
      le_airyStabI hδ'pos fun f hf hne hnn => hlow δ' hδ'pos hδ'lt f hf hne hnn
    have h2 : airyStabI δ' ≤ airyStabI δ := airyStabI_mono hδ'pos (min_le_left _ _)
    have : 0 < quantC1Mass⁻¹ / 2 * δ' := by have := inv_pos.mpr hMpos; positivity
    linarith
  · rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨δ₀, hδ₀, hlow⟩ := airy_stab_lower (θ := (a + quantC1Mass⁻¹) / 2) (by
        rw [← hM] at ha ⊢; rw [hM] at ha ⊢; linarith)
      have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < δ₀ := by
        filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hδ₀] with δ h1 h2
        exact ⟨h1, h2.2⟩
      filter_upwards [hev] with δ ⟨hδ, hδlt⟩
      have h1 : (a + quantC1Mass⁻¹) / 2 * δ ≤ airyStabI δ :=
        le_airyStabI hδ fun f hf hne hnn => hlow δ hδ hδlt f hf hne hnn
      rw [lt_div_iff₀ hδ]
      nlinarith
    · intro b hb
      have hmass := tendsto_airyTrial_mass
      rw [hM] at hmass
      have hinv : Tendsto (fun δ : ℝ => (∫ x : ℝ, ‖airyTrial δ (x : ℂ)‖)⁻¹) (𝓝[>] 0)
          (𝓝 quantC1Mass⁻¹) := hmass.inv₀ hMpos.ne'
      filter_upwards [hinv.eventually (gt_mem_nhds hb), self_mem_nhdsWithin] with δ hlt hδ
      have hδ' : 0 < δ := hδ
      calc airyStabI δ / δ ≤ (δ / ∫ x : ℝ, ‖airyTrial δ (x : ℂ)‖) / δ :=
            div_le_div_of_nonneg_right (airyStabI_le_trial hδ') hδ'.le
        _ = (∫ x : ℝ, ‖airyTrial δ (x : ℂ)‖)⁻¹ := by field_simp
        _ < b := hlt

/-- info: 'FormalResearch.ModularBootstrap.Stability.airy_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_stability

end FormalResearch.ModularBootstrap.Stability
