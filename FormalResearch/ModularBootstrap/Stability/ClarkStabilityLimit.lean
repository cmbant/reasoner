module

public import FormalResearch.ModularBootstrap.Stability.ClarkStability
public import FormalResearch.ModularBootstrap.TwoLevel.A2StarCurve

/-!
# Theorem SE.6 (`se:3.1`), second assertion: decoupling limit `κ₂(u₁) → (2 L_*^{(0)})⁻¹`

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem SE.6 (`se:3.1`),
second assertion: as `u₁ → +∞`,
`κ₂(u₁) = (cos² α - z₂ sin² α) / ((u₁ - z₂) · 2 L_*(α)) → (2 L_*^{(0)})⁻¹`,
where `α = α(u₁) ∈ (-π/2, π/2] \ {0}` is the Clark angle with `z₁(α) = u₁`,
`z₂ = z₂(α) ∈ (a₂, a₁)`, `2 L_*(α) = ‖g_α‖₁ = 2 ∫_{z₂}^{u₁} (-g_α(x)) dx`, and
`L_*^{(0)} = LStar = ∫_{a₁}^∞ Ai(u)²/(u - a₁) du` (`(2 LStar)⁻¹ = quantC1Mass⁻¹`).

* `clarkLStar`, `clarkKappa2`: `L_*(α)` and `κ₂(u₁)`.
* `clark_stability_kappa2`: restates `clark_stability` at `α = clarkAngle u₁` in terms of `clarkKappa2 u₁`.
* `tendsto_clarkKappa2_atTop`, `tendsto_clarkKappa2_atTop_quantC1Mass`: `κ₂(u₁) → (2 LStar)⁻¹`
  (`= quantC1Mass⁻¹`) as `u₁ → +∞`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.ModularBootstrap.TwoLevel
  FormalResearch.SignUncertainty

/-- `L_*(α) = ∫_{z₂(α)}^{z₁(α)} (-Re g_α(x)) dx = (1/2) ‖g_α‖₁`. -/
noncomputable def clarkLStar (α : ℝ) : ℝ :=
  ∫ x in Set.Ioo (clarkNode α 2) (clarkNode α 1), -(clarkExtremal α (x : ℂ)).re

/-- The two-level stability slope `κ₂(u₁) = (cos² α - z₂ sin² α) / ((u₁ - z₂) · 2 L_*(α))`
for `u₁ > a₁`, where `α = clarkAngle u₁` and `z₂ = clarkNode α 2`. -/
noncomputable def clarkKappa2 (u₁ : ℝ) : ℝ :=
  let α := clarkAngle u₁
  let z₂ := clarkNode α 2
  (Real.cos α ^ 2 - z₂ * Real.sin α ^ 2) / ((u₁ - z₂) * (2 * clarkLStar α))

/-- **Theorem SE.6 (`se:3.1`), first assertion** in terms of `clarkKappa2 u₁`. -/
theorem clark_stability_kappa2 {u₁ : ℝ} (hu₁ : airyZero 1 < u₁) :
    (∀ δ : ℝ, 0 < δ → 0 < clarkI (sin_clarkAngle_ne_zero hu₁) δ) ∧
      Tendsto (fun δ : ℝ => clarkI (sin_clarkAngle_ne_zero hu₁) δ / δ) (𝓝[>] 0)
        (𝓝 (clarkKappa2 u₁)) := by
  have hspec := clark_stability (sin_clarkAngle_ne_zero hu₁)
  have hz1 : clarkNode (clarkAngle u₁) 1 = u₁ := (clarkAngle_spec hu₁).2
  simpa [clarkKappa2, clarkLStar, hz1] using hspec

/-! ### Asymptotics of `α(u₁)` and `z₂(α(u₁))` as `u₁ → +∞` -/

private lemma cos_pos_sin_neg_of_cot_neg {α : ℝ} (hdom : α ∈ clarkAngleDomain)
    (hcot : Real.cos α / Real.sin α < 0) :
    0 < Real.cos α ∧ Real.sin α < 0 := by
  rcases hdom with ⟨⟨h1, h2⟩, _⟩
  have hcos_nn : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc ⟨h1.le, h2⟩
  have hcos_ne : Real.cos α ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hcot
    exact lt_irrefl 0 hcot
  have hcos_pos : 0 < Real.cos α := lt_of_le_of_ne hcos_nn (Ne.symm hcos_ne)
  have hsin_neg : Real.sin α < 0 := by
    by_contra hsin_nn
    push Not at hsin_nn
    have : 0 ≤ Real.cos α / Real.sin α := div_nonneg hcos_nn hsin_nn
    linarith
  exact ⟨hcos_pos, hsin_neg⟩

private lemma tendsto_tan_clarkAngle_atTop :
    Tendsto (fun u₁ : ℝ => Real.tan (clarkAngle u₁)) atTop (𝓝 0) := by
  have hcot : Tendsto (fun u₁ : ℝ => (airyRatio u₁)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atBot_zero.comp tendsto_airyRatio_atTop
  refine hcot.congr' ?_
  filter_upwards [eventually_gt_atTop (airyZero 1)] with u₁ hu₁
  rw [← cot_clarkAngle hu₁, Real.tan_eq_sin_div_cos, inv_div]

private lemma tendsto_sin_sq_clarkAngle_atTop :
    Tendsto (fun u₁ : ℝ => Real.sin (clarkAngle u₁) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u₁ : ℝ => Real.tan (clarkAngle u₁) ^ 2 /
      (1 + Real.tan (clarkAngle u₁) ^ 2)) atTop (𝓝 (0 ^ 2 / (1 + 0 ^ 2))) :=
    (tendsto_tan_clarkAngle_atTop.pow 2).div
      (tendsto_const_nhds.add (tendsto_tan_clarkAngle_atTop.pow 2)) (by norm_num)
  norm_num at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (airyZero 1),
    tendsto_airyRatio_atTop.eventually (eventually_lt_atBot (0 : ℝ))] with u₁ hu₁ hrat
  have hdom := (clarkAngle_spec hu₁).1
  rw [← cot_clarkAngle hu₁] at hrat
  have hcos := (cos_pos_sin_neg_of_cot_neg hdom hrat).1.ne'
  rw [Real.tan_eq_sin_div_cos]
  have htrig : Real.sin (clarkAngle u₁) ^ 2 + Real.cos (clarkAngle u₁) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  field_simp
  nlinarith [htrig]

private lemma tendsto_cos_sq_clarkAngle_atTop :
    Tendsto (fun u₁ : ℝ => Real.cos (clarkAngle u₁) ^ 2) atTop (𝓝 1) := by
  have h1 : Tendsto (fun u₁ : ℝ => 1 - Real.sin (clarkAngle u₁) ^ 2) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_sin_sq_clarkAngle_atTop
  simpa [Real.cos_sq'] using h1

private lemma tendsto_sin_clarkAngle_atTop :
    Tendsto (fun u₁ : ℝ => Real.sin (clarkAngle u₁)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun u₁ => ‖Real.sin (clarkAngle u₁)‖) ?_ ?_
  · exact Eventually.of_forall fun _ => le_rfl
  · have h := (Real.continuous_sqrt.tendsto 0).comp tendsto_sin_sq_clarkAngle_atTop
    simp only [Real.sqrt_zero] at h
    exact h.congr (fun u₁ => by simp [Real.sqrt_sq_eq_abs, Real.norm_eq_abs])

private lemma tendsto_cos_clarkAngle_atTop :
    Tendsto (fun u₁ : ℝ => Real.cos (clarkAngle u₁)) atTop (𝓝 1) := by
  have h := (Real.continuous_sqrt.tendsto 1).comp tendsto_cos_sq_clarkAngle_atTop
  simp only [Real.sqrt_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (airyZero 1),
    tendsto_airyRatio_atTop.eventually (eventually_lt_atBot (0 : ℝ))] with u₁ hu₁ hrat
  have hdom := (clarkAngle_spec hu₁).1
  rw [← cot_clarkAngle hu₁] at hrat
  dsimp only [Function.comp_def]
  rw [Real.sqrt_sq (cos_pos_sin_neg_of_cot_neg hdom hrat).1.le]

private lemma tendsto_z2_atTop :
    Tendsto (fun u₁ : ℝ => clarkNode (clarkAngle u₁) 2) atTop (𝓝 (airyZero 1)) := by
  have h := (tendsto_airyClarkNode_atBot (n := 2) (by norm_num)).comp tendsto_airyRatio_atTop
  simp only [Nat.reduceSub] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (airyZero 1)] with u₁ hu₁
  exact (clarkNode_two_eq_airyClarkNode_ratio hu₁).symm

/-! ### Dominated convergence for `(u₁ - z₂) * L_*(α)` -/

private lemma hasDerivAt_combo (α x : ℝ) :
    HasDerivAt (SturmAiry.combo α airyAi airyAi')
      (Real.cos α * airyAi' x - Real.sin α * (x * airyAi x)) x :=
  ((hasDerivAt_airyAi x).const_mul (Real.cos α)).sub
    ((hasDerivAt_airyAi' x).const_mul (Real.sin α))

private lemma combo_deriv_abs_le (α x : ℝ) :
    |Real.cos α * airyAi' x - Real.sin α * (x * airyAi x)| ≤ |airyAi' x| + |x| * |airyAi x| := by
  calc |Real.cos α * airyAi' x - Real.sin α * (x * airyAi x)|
      ≤ |Real.cos α * airyAi' x| + |Real.sin α * (x * airyAi x)| := abs_sub _ _
    _ = |Real.cos α| * |airyAi' x| + |Real.sin α| * (|x| * |airyAi x|) := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ 1 * |airyAi' x| + 1 * (|x| * |airyAi x|) := by
        gcongr
        · exact Real.abs_cos_le_one α
        · exact Real.abs_sin_le_one α
    _ = _ := by ring

private lemma combo_abs_sub_le_of_zero {α a b M : ℝ} (hab : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, |airyAi' t| + |t| * |airyAi t| ≤ M) :
    |SturmAiry.combo α airyAi airyAi' b - SturmAiry.combo α airyAi airyAi' a| ≤ M * (b - a) := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · have hcont : ContinuousOn (SturmAiry.combo α airyAi airyAi') (Icc a b) :=
      (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_combo α t).continuousAt).continuousOn
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (SturmAiry.combo α airyAi airyAi')
      (fun t => Real.cos α * airyAi' t - Real.sin α * (t * airyAi t))
      hlt hcont (fun t _ => hasDerivAt_combo α t)
    have hdiff : SturmAiry.combo α airyAi airyAi' b - SturmAiry.combo α airyAi airyAi' a =
        (b - a) * (Real.cos α * airyAi' ξ - Real.sin α * (ξ * airyAi ξ)) := by
      rw [hslope]
      field_simp [(sub_pos.mpr hlt).ne']
    rw [hdiff, abs_mul, abs_of_pos (sub_pos.mpr hlt)]
    have hξIcc : ξ ∈ Icc a b := ⟨hξ.1.le, hξ.2.le⟩
    calc (b - a) * |Real.cos α * airyAi' ξ - Real.sin α * (ξ * airyAi ξ)|
        ≤ (b - a) * (|airyAi' ξ| + |ξ| * |airyAi ξ|) :=
          mul_le_mul_of_nonneg_left (combo_deriv_abs_le α ξ) (sub_pos.mpr hlt).le
      _ ≤ (b - a) * M := mul_le_mul_of_nonneg_left (hbound ξ hξIcc) (sub_pos.mpr hlt).le
      _ = M * (b - a) := mul_comm _ _

private lemma integrand_eq {u₁ x : ℝ} (hu₁ : airyZero 1 < u₁)
    (hx2 : clarkNode (clarkAngle u₁) 2 < x) (hx1 : x < u₁) :
    (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re =
      ((u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)) *
        (SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 /
          (x - clarkNode (clarkAngle u₁) 2)) := by
  have hα := sin_clarkAngle_ne_zero hu₁
  have hz1 : clarkNode (clarkAngle u₁) 1 = u₁ := (clarkAngle_spec hu₁).2
  rw [clarkExtremal_re hα (by rw [hz1]; exact hx1.ne) hx2.ne', hz1]
  have hne1 : u₁ - x ≠ 0 := (sub_pos.mpr hx1).ne'
  have hne2 : x - clarkNode (clarkAngle u₁) 2 ≠ 0 := (sub_pos.mpr hx2).ne'
  have heq : (x - u₁) * (x - clarkNode (clarkAngle u₁) 2) =
      -((u₁ - x) * (x - clarkNode (clarkAngle u₁) 2)) := by ring
  rw [heq, div_neg, neg_neg]
  field_simp

private lemma combo_sq_bound_pos {α x : ℝ} (hx : 0 ≤ x) :
    SturmAiry.combo α airyAi airyAi' x ^ 2 ≤
      64 * (1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) := by
  have h1 := psiClark_norm_sq_le α (x : ℂ)
  have hn : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  have he : airyEnv (x : ℂ) = Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) := at47_env_ofReal_nonneg hx
  have hnorm : ‖psiClark α (x : ℂ)‖ = |SturmAiry.combo α airyAi airyAi' x| := by
    rw [psiClark_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, sq_abs, hn, he] at h1
  exact h1

private lemma combo_deriv_bound_pos {α ξ : ℝ} (hξ : 1 ≤ ξ) :
    |Real.cos α * airyAi' ξ - Real.sin α * (ξ * airyAi ξ)| ≤
      8 * (1 + ξ) * Real.exp (-(2 / 3) * ξ ^ (3 / 2 : ℝ)) := by
  have hξ0 : 0 ≤ ξ := by linarith
  have hx1 : 1 ≤ 1 + ξ := by linarith
  have hA := airyAiC_envelope (ξ : ℂ)
  have hB := airyAiC_deriv_envelope (ξ : ℂ)
  have hn : ‖(ξ : ℂ)‖ = ξ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hξ0]
  have hAn : ‖airyAiC (ξ : ℂ)‖ = |airyAi ξ| := by
    rw [airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hBn : ‖deriv airyAiC (ξ : ℂ)‖ = |airyAi' ξ| := by
    rw [deriv_airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hcp : ((ξ : ℂ) ^ (3 / 2 : ℂ)).re = ξ ^ (3 / 2 : ℝ) := by
    have := Complex.ofReal_cpow hξ0 (3 / 2 : ℝ)
    rw [show (((3 / 2 : ℝ)) : ℂ) = (3 / 2 : ℂ) by push_cast; ring] at this
    rw [← this, Complex.ofReal_re]
  rw [hAn, hn, hcp] at hA
  rw [hBn, hn, hcp] at hB
  have hp1 : (1 + ξ) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hp2 : (1 + ξ) ^ (1 / 4 : ℝ) ≤ 1 + ξ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have he : 0 ≤ Real.exp (-(2 / 3) * ξ ^ (3 / 2 : ℝ)) := (Real.exp_pos _).le
  have hAi' : |airyAi' ξ| ≤ 5 * (1 + ξ) * Real.exp (-(2 / 3) * ξ ^ (3 / 2 : ℝ)) := by
    refine hB.trans ?_
    gcongr
  have hAi : |ξ| * |airyAi ξ| ≤ 3 * (1 + ξ) * Real.exp (-(2 / 3) * ξ ^ (3 / 2 : ℝ)) := by
    rw [abs_of_nonneg hξ0]
    have hAi1 : |airyAi ξ| ≤ 3 * Real.exp (-(2 / 3) * ξ ^ (3 / 2 : ℝ)) := by
      refine hA.trans ?_
      have : 3 * (1 + ξ) ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * ξ ^ (3 / 2 : ℝ)) ≤
          3 * 1 * Real.exp (-(2 / 3) * ξ ^ (3 / 2 : ℝ)) := by gcongr
      simpa using this
    calc ξ * |airyAi ξ| ≤ (1 + ξ) * (3 * Real.exp (-(2 / 3) * ξ ^ (3 / 2 : ℝ))) := by gcongr; linarith
      _ = 3 * (1 + ξ) * Real.exp (-(2 / 3) * ξ ^ (3 / 2 : ℝ)) := by ring
  exact (combo_deriv_abs_le α ξ).trans (by linarith)

private lemma tendsto_piece1 :
    Tendsto (fun u₁ : ℝ => ∫ x in Set.Ioc (airyZero 2) 1,
      if clarkNode (clarkAngle u₁) 2 < x then
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re
      else 0) atTop
      (𝓝 (∫ x in Set.Ioc (airyZero 1) 1, airyAi x ^ 2 / (x - airyZero 1))) := by
  -- Compact bound on `[airyZero 2, 1]` for `|Ai'| + |t| |Ai|`
  have hc : Continuous (fun t : ℝ => |airyAi' t| + |t| * |airyAi t|) := by
    have := continuous_airyAi; have := continuous_airyAi'; fun_prop
  obtain ⟨M₁, hM₁_bd⟩ := (isCompact_Icc (a := airyZero 2) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  set M : ℝ := max M₁ 0 with hM
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have hM_bd : ∀ t ∈ Icc (airyZero 2) 1, |airyAi' t| + |t| * |airyAi t| ≤ M := fun t ht => by
    have := hM₁_bd t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  have hgap21 : airyZero 2 < 1 := (airyZero_neg 2).trans zero_lt_one
  set B : ℝ := 4 * M ^ 2 * (1 - airyZero 2) with hB
  have hB0 : 0 ≤ B := by positivity
  set μ : Measure ℝ := volume.restrict (Set.Ioc (airyZero 2) 1)
  have hμ_fin : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  let F : ℝ → ℝ → ℝ := fun u₁ x =>
    if clarkNode (clarkAngle u₁) 2 < x then
      (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re
    else 0
  let f : ℝ → ℝ := fun x => if airyZero 1 < x then airyAi x ^ 2 / (x - airyZero 1) else 0
  have hF_meas : ∀ᶠ u₁ in atTop, AEStronglyMeasurable (F u₁) μ := by
    filter_upwards [eventually_gt_atTop (airyZero 1)] with u₁ hu₁
    have hcont : Continuous (fun x : ℝ =>
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re) :=
      continuous_const.mul (Complex.continuous_re.comp
        ((differentiable_clarkExtremal (clarkAngle u₁)).continuous.comp continuous_ofReal)).neg
    exact (Measurable.ite (measurableSet_Ioi (a := clarkNode (clarkAngle u₁) 2))
      hcont.measurable measurable_const).aestronglyMeasurable
  have hF_bound : ∀ᶠ u₁ in atTop, ∀ᵐ x ∂μ, ‖F u₁ x‖ ≤ B := by
    filter_upwards [eventually_ge_atTop (max 2 (2 * |airyZero 2| + 2))] with u₁ hu₁
    have hu₁_2 : 2 ≤ u₁ := (le_max_left _ _).trans hu₁
    have hu₁_abs : 2 * |airyZero 2| + 2 ≤ u₁ := (le_max_right _ _).trans hu₁
    have hu₁_a1 : airyZero 1 < u₁ := (airyZero_neg 1).trans (by linarith)
    have hα := sin_clarkAngle_ne_zero hu₁_a1
    have hz2 := airyZero_two_lt_clarkNode_two hu₁_a1
    have hψz2 : SturmAiry.combo (clarkAngle u₁) airyAi airyAi' (clarkNode (clarkAngle u₁) 2) = 0 :=
      psiClark_real_zero hα (by norm_num)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    dsimp only [F]
    split_ifs with hzx
    · have hx1 : x ≤ 1 := hx.2
      have hxu1 : x < u₁ := hx1.trans_lt (by linarith)
      rw [integrand_eq hu₁_a1 hzx hxu1, Real.norm_eq_abs, abs_mul]
      have hratio : |(u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)| ≤ 4 := by
        have hnum_pos : 0 < u₁ - clarkNode (clarkAngle u₁) 2 := by linarith [hz2.2, airyZero_neg 1]
        have hden_pos : 0 < u₁ - x := by linarith
        have hnum_le : u₁ - clarkNode (clarkAngle u₁) 2 ≤ 2 * u₁ := by
          linarith [neg_abs_le (airyZero 2), hz2.1]
        have hden_ge : u₁ / 2 ≤ u₁ - x := by linarith
        rw [abs_of_pos (div_pos hnum_pos hden_pos), div_le_iff₀ hden_pos]
        nlinarith
      have hmv : |SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x| ≤
          M * (x - clarkNode (clarkAngle u₁) 2) := by
        have h1 := combo_abs_sub_le_of_zero (α := clarkAngle u₁) hzx.le (fun t ht =>
          hM_bd t ⟨hz2.1.le.trans ht.1, ht.2.trans hx1⟩)
        rwa [hψz2, sub_zero] at h1
      have hcomb : |SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 /
          (x - clarkNode (clarkAngle u₁) 2)| ≤ M ^ 2 * (1 - airyZero 2) := by
        have hpos : 0 < x - clarkNode (clarkAngle u₁) 2 := sub_pos.mpr hzx
        rw [abs_div, abs_sq, abs_of_pos hpos, div_le_iff₀ hpos]
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hmv 2
        rw [← sq_abs]
        calc |SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x| ^ 2
            ≤ (M * (x - clarkNode (clarkAngle u₁) 2)) ^ 2 := hsq
          _ = M ^ 2 * (x - clarkNode (clarkAngle u₁) 2) * (x - clarkNode (clarkAngle u₁) 2) := by
              ring
          _ ≤ M ^ 2 * (1 - airyZero 2) * (x - clarkNode (clarkAngle u₁) 2) := by
              gcongr; linarith [hz2.1, hx1]
      calc |(u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)| *
            |SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 /
              (x - clarkNode (clarkAngle u₁) 2)|
          ≤ 4 * (M ^ 2 * (1 - airyZero 2)) := mul_le_mul hratio hcomb (abs_nonneg _) (by norm_num)
        _ = B := by rw [hB]; ring
    · simp [hB0]
  have hbound_int : Integrable (fun _ : ℝ => B) μ := integrable_const B
  have hF_lim : ∀ᵐ x ∂μ, Tendsto (fun u₁ : ℝ => F u₁ x) atTop (𝓝 (f x)) := by
    have hae_ne : ∀ᵐ x ∂μ, x ≠ airyZero 1 :=
      ae_iff.mpr (measure_mono_null (fun x hx => by simpa using hx)
        (measure_singleton (airyZero 1)))
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hae_ne] with x hx hxne
    rcases lt_or_gt_of_ne hxne with hlt | hgt
    · have hf0 : f x = 0 := by dsimp only [f]; split_ifs with h; exact absurd h (not_lt.mpr hlt.le); rfl
      rw [hf0]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_z2_atTop.eventually (Ioi_mem_nhds hlt)] with u₁ hu₁
      dsimp only [F]
      split_ifs with h
      · exact absurd h (not_lt.mpr (le_of_lt hu₁))
      · rfl
    · have hf1 : f x = airyAi x ^ 2 / (x - airyZero 1) := by
        dsimp only [f]; split_ifs with h; rfl; exact absurd hgt h
      rw [hf1]
      have hrat : Tendsto (fun u₁ : ℝ => (u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)) atTop (𝓝 1) := by
        have heq : ∀ᶠ u₁ in atTop, (u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x) =
            (1 - clarkNode (clarkAngle u₁) 2 / u₁) / (1 - x / u₁) := by
          filter_upwards [eventually_gt_atTop (max 1 x)] with u₁ hu₁
          have hu0 : u₁ ≠ 0 := by linarith [le_max_left 1 x]
          field_simp
        refine Tendsto.congr' (EventuallyEq.symm heq) ?_
        have h1 : Tendsto (fun u₁ : ℝ => 1 - clarkNode (clarkAngle u₁) 2 / u₁) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub (tendsto_z2_atTop.div_atTop tendsto_id)
        have h2 : Tendsto (fun u₁ : ℝ => 1 - x / u₁) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
        have h3 : Tendsto (fun u₁ : ℝ => (1 - clarkNode (clarkAngle u₁) 2 / u₁) / (1 - x / u₁))
            atTop (𝓝 ((1 - 0) / (1 - 0))) := h1.div h2 (by norm_num)
        rwa [sub_zero, div_one] at h3
      have hcombo : Tendsto (fun u₁ : ℝ => SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x)
          atTop (𝓝 (airyAi x)) := by
        have h := (tendsto_cos_clarkAngle_atTop.mul_const (airyAi x)).sub
          (tendsto_sin_clarkAngle_atTop.mul_const (airyAi' x))
        simpa [SturmAiry.combo] using h
      have hden : Tendsto (fun u₁ : ℝ => x - clarkNode (clarkAngle u₁) 2)
          atTop (𝓝 (x - airyZero 1)) := tendsto_const_nhds.sub tendsto_z2_atTop
      have hprod : Tendsto (fun u₁ : ℝ =>
          ((u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)) *
            (SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 /
              (x - clarkNode (clarkAngle u₁) 2))) atTop (𝓝 (1 * (airyAi x ^ 2 / (x - airyZero 1)))) :=
        hrat.mul ((hcombo.pow 2).div hden (sub_pos.mpr hgt).ne')
      rw [one_mul] at hprod
      refine hprod.congr' ?_
      filter_upwards [eventually_gt_atTop (max 2 (airyZero 1)),
        tendsto_z2_atTop.eventually (Iio_mem_nhds hgt)] with u₁ hu₁ hzx
      have hu₁_a1 : airyZero 1 < u₁ := lt_of_le_of_lt (le_max_right _ _) hu₁
      have hxu1 : x < u₁ := by have := le_max_left (2 : ℝ) (airyZero 1); linarith [hx.2]
      dsimp only [F]
      split_ifs with h
      · exact (integrand_eq hu₁_a1 hzx hxu1).symm
      · exact absurd hzx h
  have hlim := tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    hF_meas hF_bound hbound_int hF_lim
  have heq_target : ∫ x in Set.Ioc (airyZero 2) 1, f x =
      ∫ x in Set.Ioc (airyZero 1) 1, airyAi x ^ 2 / (x - airyZero 1) := by
    have hsub : Set.Ioc (airyZero 1) 1 ⊆ Set.Ioc (airyZero 2) 1 :=
      Set.Ioc_subset_Ioc_left (airyZero_strictAnti (n := 1) le_rfl).le
    rw [← integral_indicator measurableSet_Ioc]
    symm
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
    ext x
    by_cases hx1 : x ∈ Set.Ioc (airyZero 1) 1
    · have hx2 : x ∈ Set.Ioc (airyZero 2) 1 := hsub hx1
      simp [hx1, hx2, f, hx1.1]
    · by_cases hx2 : x ∈ Set.Ioc (airyZero 2) 1
      · have hle : x ≤ airyZero 1 := by
          by_contra hgt; push Not at hgt; exact hx1 ⟨hgt, hx2.2⟩
        simp [hx1, hx2, f, not_lt.mpr hle]
      · simp [hx1, hx2]
  rw [heq_target] at hlim
  exact hlim

private lemma integrableOn_airyRatioSq_Ioi_one :
    IntegrableOn (fun x : ℝ => airyAi x ^ 2 / (x - airyZero 1)) (Ioi 1) := by
  have h1 : IntegrableOn (fun x : ℝ => -(airyExtremal (x : ℂ)).re) (Ioi 1) :=
    airyExtremal_integrable.re.neg.integrableOn
  refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
  dsimp only
  rw [airyExtremal_re, neg_neg]

private lemma integrableOn_airyEnv_Ioi_one :
    IntegrableOn (fun x : ℝ => (1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ))) (Ioi 1) := by
  have hdec : ∃ K A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, A ≤ x →
      ‖(1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ))‖ ≤ K * x ^ (-2 : ℝ) := by
    have := at47_F_pos_decay (F := fun u : ℂ => (((1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u : ℝ) : ℂ))
      (C := 1) (ν := 1 / 2) zero_le_one (fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (Real.rpow_nonneg (by linarith [norm_nonneg u]) _) (airyEnv_pos u).le)]
        ring_nf; rfl)
    obtain ⟨K, A, hA, hb⟩ := this
    refine ⟨K, A, hA, fun x hx => ?_⟩
    have hx0 : 0 ≤ x := by linarith
    have h1 := hb x hx
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0,
      at47_env_ofReal_nonneg hx0] at h1
    have hnn : 0 ≤ (1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) := by positivity
    rw [abs_of_nonneg hnn] at h1
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact h1
  obtain ⟨K, A, hA, hb⟩ := hdec
  have hc : ContinuousOn (fun x : ℝ => (1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)))
      (Icc 1 A) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (continuous_const.add continuous_id).continuousOn.rpow_const (fun x hx => by
        left; simp; linarith [hx.1])
    · refine ContinuousOn.rexp (continuousOn_const.mul ?_)
      exact continuous_id.continuousOn.rpow_const (fun x hx => by left; simp; linarith [hx.1])
  have hmid : IntegrableOn (fun x : ℝ => (1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)))
      (Ioc 1 A) := hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have htail : IntegrableOn (fun x : ℝ => (1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)))
      (Ioi A) := by
    have hg : IntegrableOn (fun x : ℝ => K * x ^ (-2 : ℝ)) (Ioi A) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)).const_mul K
    have hm : AEStronglyMeasurable (fun x : ℝ => (1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)))
        (volume.restrict (Ioi A)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.mul ?_ ?_
      · exact (continuous_const.add continuous_id).continuousOn.rpow_const (fun x hx => by
          left; have := (hA.trans hx.le); simp; linarith)
      · refine ContinuousOn.rexp (continuousOn_const.mul ?_)
        exact continuous_id.continuousOn.rpow_const (fun x hx => by
          left; have := (hA.trans hx.le); simp; linarith)
    refine Integrable.mono' hg hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hb x hx.le
  have hunion : Ioi (1 : ℝ) = Ioc 1 A ∪ Ioi A := (Set.Ioc_union_Ioi_eq_Ioi hA).symm
  rw [hunion]
  exact hmid.union htail

private lemma tendsto_piece2 :
    Tendsto (fun u₁ : ℝ => ∫ x in Set.Ioi 1,
      if x ≤ u₁ / 2 then
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re
      else 0) atTop
      (𝓝 (∫ x in Set.Ioi 1, airyAi x ^ 2 / (x - airyZero 1))) := by
  set C₀ : ℝ := 4 * 64 / (1 - airyZero 1) with hC₀
  have hC₀_pos : 0 < C₀ := by
    have h1 : 0 < 1 - airyZero 1 := by linarith [airyZero_neg 1]
    rw [hC₀]; positivity
  set μ : Measure ℝ := volume.restrict (Set.Ioi 1)
  let F : ℝ → ℝ → ℝ := fun u₁ x =>
    if x ≤ u₁ / 2 then
      (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re
    else 0
  let dom : ℝ → ℝ := fun x => C₀ * ((1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)))
  have hF_meas : ∀ᶠ u₁ in atTop, AEStronglyMeasurable (F u₁) μ := by
    filter_upwards [eventually_gt_atTop (airyZero 1)] with u₁ _
    have hcont : Continuous (fun x : ℝ =>
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re) :=
      continuous_const.mul (Complex.continuous_re.comp
        ((differentiable_clarkExtremal (clarkAngle u₁)).continuous.comp continuous_ofReal)).neg
    exact (Measurable.ite (measurableSet_Iic (a := u₁ / 2))
      hcont.measurable measurable_const).aestronglyMeasurable
  have hF_bound : ∀ᶠ u₁ in atTop, ∀ᵐ x ∂μ, ‖F u₁ x‖ ≤ dom x := by
    filter_upwards [eventually_ge_atTop (max 2 (2 * |airyZero 2| + 2))] with u₁ hu₁
    have hu₁_2 : 2 ≤ u₁ := (le_max_left _ _).trans hu₁
    have hu₁_abs : 2 * |airyZero 2| + 2 ≤ u₁ := (le_max_right _ _).trans hu₁
    have hu₁_a1 : airyZero 1 < u₁ := (airyZero_neg 1).trans (by linarith)
    have hz2 := airyZero_two_lt_clarkNode_two hu₁_a1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx0 : 0 ≤ x := by linarith
    dsimp only [F, dom]
    split_ifs with hxu
    · have hzx : clarkNode (clarkAngle u₁) 2 < x := by linarith [hz2.2, airyZero_neg 1]
      have hxu1 : x < u₁ := by linarith
      rw [integrand_eq hu₁_a1 hzx hxu1, Real.norm_eq_abs, abs_mul]
      have hratio : |(u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)| ≤ 4 := by
        have hnum_pos : 0 < u₁ - clarkNode (clarkAngle u₁) 2 := by linarith [hz2.2, airyZero_neg 1]
        have hden_pos : 0 < u₁ - x := by linarith
        have hnum_le : u₁ - clarkNode (clarkAngle u₁) 2 ≤ 2 * u₁ := by
          linarith [neg_abs_le (airyZero 2), hz2.1]
        have hden_ge : u₁ / 2 ≤ u₁ - x := by linarith
        rw [abs_of_pos (div_pos hnum_pos hden_pos), div_le_iff₀ hden_pos]
        nlinarith
      have hden_ge : 1 - airyZero 1 ≤ x - clarkNode (clarkAngle u₁) 2 := by linarith [hz2.2]
      have hden_pos : 0 < 1 - airyZero 1 := by linarith [airyZero_neg 1]
      have hcomb : |SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 /
          (x - clarkNode (clarkAngle u₁) 2)| ≤
          64 * (1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) / (1 - airyZero 1) := by
        have hxden : 0 < x - clarkNode (clarkAngle u₁) 2 := sub_pos.mpr hzx
        have hden_pos : 0 < 1 - airyZero 1 := by linarith [airyZero_neg 1]
        rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hxden]
        exact div_le_div₀ (by positivity) (combo_sq_bound_pos hx0) hden_pos hden_ge
      calc |(u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)| *
            |SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 /
              (x - clarkNode (clarkAngle u₁) 2)|
          ≤ 4 * (64 * (1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) / (1 - airyZero 1)) :=
            mul_le_mul hratio hcomb (abs_nonneg _) (by norm_num)
        _ = C₀ * ((1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ))) := by
            rw [hC₀]; ring
    · have h1 : 0 < 1 - airyZero 1 := by linarith [airyZero_neg 1]
      have : 0 ≤ C₀ * ((1 + x) ^ (1 / 2 : ℝ) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ))) := by
        positivity
      simpa using this
  have hdom_int : Integrable dom μ := integrableOn_airyEnv_Ioi_one.const_mul C₀
  have hF_lim : ∀ᵐ x ∂μ, Tendsto (fun u₁ : ℝ => F u₁ x) atTop (𝓝 (airyAi x ^ 2 / (x - airyZero 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hgt : airyZero 1 < x := (airyZero_neg 1).trans (zero_lt_one.trans hx1)
    have hrat : Tendsto (fun u₁ : ℝ => (u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)) atTop (𝓝 1) := by
      have heq : ∀ᶠ u₁ in atTop, (u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x) =
          (1 - clarkNode (clarkAngle u₁) 2 / u₁) / (1 - x / u₁) := by
        filter_upwards [eventually_gt_atTop (max 1 x)] with u₁ hu₁
        have hu0 : u₁ ≠ 0 := by linarith [le_max_left 1 x]
        field_simp
      refine Tendsto.congr' (EventuallyEq.symm heq) ?_
      have h1 : Tendsto (fun u₁ : ℝ => 1 - clarkNode (clarkAngle u₁) 2 / u₁) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_z2_atTop.div_atTop tendsto_id)
      have h2 : Tendsto (fun u₁ : ℝ => 1 - x / u₁) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
      have h3 : Tendsto (fun u₁ : ℝ => (1 - clarkNode (clarkAngle u₁) 2 / u₁) / (1 - x / u₁))
          atTop (𝓝 ((1 - 0) / (1 - 0))) := h1.div h2 (by norm_num)
      rwa [sub_zero, div_one] at h3
    have hcombo : Tendsto (fun u₁ : ℝ => SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x)
        atTop (𝓝 (airyAi x)) := by
      have h := (tendsto_cos_clarkAngle_atTop.mul_const (airyAi x)).sub
        (tendsto_sin_clarkAngle_atTop.mul_const (airyAi' x))
      simpa [SturmAiry.combo] using h
    have hden : Tendsto (fun u₁ : ℝ => x - clarkNode (clarkAngle u₁) 2)
        atTop (𝓝 (x - airyZero 1)) := tendsto_const_nhds.sub tendsto_z2_atTop
    have hprod : Tendsto (fun u₁ : ℝ =>
        ((u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)) *
          (SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 /
            (x - clarkNode (clarkAngle u₁) 2))) atTop (𝓝 (1 * (airyAi x ^ 2 / (x - airyZero 1)))) :=
      hrat.mul ((hcombo.pow 2).div hden (sub_pos.mpr hgt).ne')
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (max (2 * x) (airyZero 1))] with u₁ hu₁
    have hu₁_2x : 2 * x < u₁ := (le_max_left _ _).trans_lt hu₁
    have hu₁_a1 : airyZero 1 < u₁ := (le_max_right _ _).trans_lt hu₁
    have hz2 := airyZero_two_lt_clarkNode_two hu₁_a1
    have hzx : clarkNode (clarkAngle u₁) 2 < x := by linarith [hz2.2, airyZero_neg 1]
    dsimp only [F]
    split_ifs with h
    · exact (integrand_eq hu₁_a1 hzx (by linarith)).symm
    · exact absurd (by linarith) h
  exact tendsto_integral_filter_of_dominated_convergence dom hF_meas hF_bound hdom_int hF_lim

private lemma tendsto_piece3 :
    Tendsto (fun u₁ : ℝ => ∫ x in (u₁ / 2)..u₁,
      (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re) atTop (𝓝 0) := by
  let b : ℝ := (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ (3 / 2 : ℝ)
  have hb_pos : 0 < b := by positivity
  have hdecay : Tendsto (fun u₁ : ℝ => 64 * (4 * (u₁ ^ 5 * Real.exp (-b * u₁ ^ (3 / 2 : ℝ))))) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_rpow (5 : ℝ) (b := b) hb_pos
    simpa using (h.const_mul 4).const_mul 64
  have hge : ∀ᶠ u₁ in atTop, max 2 (2 * |airyZero 2| + 2) ≤ u₁ :=
    eventually_ge_atTop (max 2 (2 * |airyZero 2| + 2))
  refine squeeze_zero' ?_ ?_ hdecay
  · filter_upwards [hge] with u₁ hu₁
    have hu₁_2 : 2 ≤ u₁ := (le_max_left _ _).trans hu₁
    have hu₁_a1 : airyZero 1 < u₁ := (airyZero_neg 1).trans (by linarith)
    have hα := sin_clarkAngle_ne_zero hu₁_a1
    have hz1 : clarkNode (clarkAngle u₁) 1 = u₁ := (clarkAngle_spec hu₁_a1).2
    have hz2 := airyZero_two_lt_clarkNode_two hu₁_a1
    refine intervalIntegral.integral_nonneg (by linarith) fun x hx => ?_
    have hnum : 0 ≤ u₁ - clarkNode (clarkAngle u₁) 2 := by linarith [hz2.2, airyZero_neg 1]
    have hnonpos : (clarkExtremal (clarkAngle u₁) (x : ℂ)).re ≤ 0 := by
      rcases eq_or_lt_of_le hx.2 with rfl | hlt
      · have h0 := clarkExtremal_at_one hα
        rw [hz1] at h0
        rw [h0]; simp
      · have hzx : clarkNode (clarkAngle u₁) 2 < x := by linarith [hx.1, hz2.2, airyZero_neg 1]
        have hlt' : x < clarkNode (clarkAngle u₁) 1 := by rwa [hz1]
        exact (clarkExtremal_neg_between hα hzx hlt').le
    exact mul_nonneg hnum (neg_nonneg.mpr hnonpos)
  · filter_upwards [hge] with u₁ hu₁
    have hu₁_2 : 2 ≤ u₁ := (le_max_left _ _).trans hu₁
    have hu₁_abs : 2 * |airyZero 2| + 2 ≤ u₁ := (le_max_right _ _).trans hu₁
    have hu₁_a1 : airyZero 1 < u₁ := (airyZero_neg 1).trans (by linarith)
    have hα := sin_clarkAngle_ne_zero hu₁_a1
    have hz1 : clarkNode (clarkAngle u₁) 1 = u₁ := (clarkAngle_spec hu₁_a1).2
    have hz2 := airyZero_two_lt_clarkNode_two hu₁_a1
    have hψu1 : SturmAiry.combo (clarkAngle u₁) airyAi airyAi' u₁ = 0 := by
      have h := psiClark_real_zero hα le_rfl
      rwa [hz1] at h
    set M := 8 * (1 + u₁) * Real.exp (-(2 / 3) * (u₁ / 2) ^ (3 / 2 : ℝ)) with hM
    have hM_nonneg : 0 ≤ M := by positivity
    have hM_bd : ∀ t ∈ Icc (u₁ / 2) u₁, |airyAi' t| + |t| * |airyAi t| ≤ M := by
      intro t ht
      have ht1 : 1 ≤ t := by linarith [ht.1]
      have ht0 : 0 < u₁ / 2 := by linarith
      have ht_exp : Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) ≤
          Real.exp (-(2 / 3) * (u₁ / 2) ^ (3 / 2 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hpow : (u₁ / 2) ^ (3 / 2 : ℝ) ≤ t ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow ht0.le ht.1 (by norm_num)
        linarith
      have hA := airyAiC_envelope (t : ℂ)
      have hB := airyAiC_deriv_envelope (t : ℂ)
      have hn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have hAn : ‖airyAiC (t : ℂ)‖ = |airyAi t| := by
        rw [airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs]
      have hBn : ‖deriv airyAiC (t : ℂ)‖ = |airyAi' t| := by
        rw [deriv_airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs]
      have hcp : ((t : ℂ) ^ (3 / 2 : ℂ)).re = t ^ (3 / 2 : ℝ) := by
        have := Complex.ofReal_cpow (by linarith : 0 ≤ t) (3 / 2 : ℝ)
        rw [show (((3 / 2 : ℝ)) : ℂ) = (3 / 2 : ℂ) by push_cast; ring] at this
        rw [← this, Complex.ofReal_re]
      rw [hAn, hn, hcp] at hA
      rw [hBn, hn, hcp] at hB
      have hp1 : (1 + t) ^ (-(1 / 4) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      have hp2 : (1 + t) ^ (1 / 4 : ℝ) ≤ 1 + u₁ := by
        have hle := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 1 + t) (by norm_num : (1 / 4 : ℝ) ≤ 1)
        rw [Real.rpow_one] at hle
        exact hle.trans (by linarith [ht.2])
      have he0 : 0 ≤ Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) := (Real.exp_pos _).le
      have hAi' : |airyAi' t| ≤ 5 * (1 + u₁) * Real.exp (-(2 / 3) * (u₁ / 2) ^ (3 / 2 : ℝ)) := by
        calc |airyAi' t| ≤ 5 * (1 + t) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) := hB
          _ ≤ 5 * (1 + u₁) * Real.exp (-(2 / 3) * (u₁ / 2) ^ (3 / 2 : ℝ)) := by gcongr
      have hAi : |t| * |airyAi t| ≤ 3 * (1 + u₁) * Real.exp (-(2 / 3) * (u₁ / 2) ^ (3 / 2 : ℝ)) := by
        rw [abs_of_pos (by linarith)]
        have hAi1 : |airyAi t| ≤ 3 * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) := by
          refine hA.trans ?_
          have : 3 * (1 + t) ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) ≤
              3 * 1 * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) := by gcongr
          simpa using this
        calc t * |airyAi t| ≤ (1 + u₁) * (3 * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ))) := by
              gcongr; linarith [ht.2]
          _ ≤ (1 + u₁) * (3 * Real.exp (-(2 / 3) * (u₁ / 2) ^ (3 / 2 : ℝ))) := by gcongr
          _ = 3 * (1 + u₁) * Real.exp (-(2 / 3) * (u₁ / 2) ^ (3 / 2 : ℝ)) := by ring
      rw [hM]; linarith
    have hpt : ∀ x ∈ Icc (u₁ / 2) u₁,
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re ≤
          2 * u₁ * (u₁ * M ^ 2) := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with rfl | hlt
      · have h0 := clarkExtremal_at_one hα
        rw [hz1] at h0
        rw [h0]
        simp only [Complex.zero_re, neg_zero, mul_zero]
        positivity
      · have hzx : clarkNode (clarkAngle u₁) 2 < x := by linarith [hx.1, hz2.2, airyZero_neg 1]
        rw [integrand_eq hu₁_a1 hzx hlt]
        have hmv : |SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x| ≤ M * (u₁ - x) := by
          have h1 := combo_abs_sub_le_of_zero (α := clarkAngle u₁) hx.2 (fun t ht =>
            hM_bd t ⟨hx.1.trans ht.1, ht.2⟩)
          rw [hψu1, zero_sub, abs_neg] at h1
          exact h1
        have hsq : SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 ≤
            (M * (u₁ - x)) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hmv 2
        have hux_pos : 0 < u₁ - x := sub_pos.mpr hlt
        have hxden : 1 ≤ x - clarkNode (clarkAngle u₁) 2 := by linarith [hx.1, hz2.2, airyZero_neg 1]
        have hnum_le : u₁ - clarkNode (clarkAngle u₁) 2 ≤ 2 * u₁ := by
          linarith [neg_abs_le (airyZero 2), hz2.1]
        have hnum_pos : 0 < u₁ - clarkNode (clarkAngle u₁) 2 := by linarith [hz2.2, airyZero_neg 1]
        have hux_le : u₁ - x ≤ u₁ := by linarith [hx.1]
        have h1 : SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 / (u₁ - x) ≤ u₁ * M ^ 2 := by
          rw [div_le_iff₀ hux_pos]
          calc SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2
              ≤ M ^ 2 * (u₁ - x) * (u₁ - x) := by linarith [hsq]
            _ ≤ M ^ 2 * u₁ * (u₁ - x) := by gcongr
            _ = u₁ * M ^ 2 * (u₁ - x) := by ring
        have h2 : (u₁ - clarkNode (clarkAngle u₁) 2) / (x - clarkNode (clarkAngle u₁) 2) ≤ 2 * u₁ := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        calc ((u₁ - clarkNode (clarkAngle u₁) 2) / (u₁ - x)) *
              (SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 /
                (x - clarkNode (clarkAngle u₁) 2))
            = ((u₁ - clarkNode (clarkAngle u₁) 2) / (x - clarkNode (clarkAngle u₁) 2)) *
                (SturmAiry.combo (clarkAngle u₁) airyAi airyAi' x ^ 2 / (u₁ - x)) := by
              ring
          _ ≤ (2 * u₁) * (u₁ * M ^ 2) := mul_le_mul h2 h1 (by positivity) (by positivity)
          _ = 2 * u₁ * (u₁ * M ^ 2) := by ring
    have hc_int : IntervalIntegrable (fun x : ℝ =>
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re)
        volume (u₁ / 2) u₁ := by
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul (Complex.continuous_re.comp
        ((differentiable_clarkExtremal (clarkAngle u₁)).continuous.comp continuous_ofReal)).neg
    have hmono := intervalIntegral.integral_mono_on (by linarith : u₁ / 2 ≤ u₁) hc_int
      (continuous_const.intervalIntegrable _ _) hpt
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hexp_eq : Real.exp (-(2 / 3) * (u₁ / 2) ^ (3 / 2 : ℝ)) ^ 2 =
        Real.exp (-b * u₁ ^ (3 / 2 : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hpow : (u₁ / 2) ^ (3 / 2 : ℝ) = (1 / 2 : ℝ) ^ (3 / 2 : ℝ) * u₁ ^ (3 / 2 : ℝ) := by
        rw [div_eq_mul_inv, mul_comm, Real.mul_rpow (by norm_num) (by linarith)]
        norm_num
      rw [hpow]
      dsimp [b]
      ring
    have h1u : (1 + u₁) ^ 2 ≤ 4 * u₁ ^ 2 := by nlinarith
    have hM2 : M ^ 2 = 64 * (1 + u₁) ^ 2 * Real.exp (-b * u₁ ^ (3 / 2 : ℝ)) := by
      rw [hM, mul_pow, mul_pow, hexp_eq]; ring
    have hfinal : (u₁ - u₁ / 2) * (2 * u₁ * (u₁ * M ^ 2)) ≤
        64 * (4 * (u₁ ^ 5 * Real.exp (-b * u₁ ^ (3 / 2 : ℝ)))) := by
      rw [hM2]
      have hexp0 : 0 ≤ Real.exp (-b * u₁ ^ (3 / 2 : ℝ)) := (Real.exp_pos _).le
      have hpow5 : u₁ ^ 3 * (1 + u₁) ^ 2 ≤ 4 * u₁ ^ 5 := by
        calc u₁ ^ 3 * (1 + u₁) ^ 2 ≤ u₁ ^ 3 * (4 * u₁ ^ 2) := by gcongr
          _ = 4 * u₁ ^ 5 := by ring
      calc (u₁ - u₁ / 2) * (2 * u₁ * (u₁ * (64 * (1 + u₁) ^ 2 * Real.exp (-b * u₁ ^ (3 / 2 : ℝ)))))
          = 64 * (u₁ ^ 3 * (1 + u₁) ^ 2 * Real.exp (-b * u₁ ^ (3 / 2 : ℝ))) := by ring
        _ ≤ 64 * (4 * u₁ ^ 5 * Real.exp (-b * u₁ ^ (3 / 2 : ℝ))) := by gcongr
        _ = 64 * (4 * (u₁ ^ 5 * Real.exp (-b * u₁ ^ (3 / 2 : ℝ)))) := by ring
    exact hmono.trans hfinal

private lemma tendsto_clarkDenom_atTop :
    Tendsto (fun u₁ : ℝ => (u₁ - clarkNode (clarkAngle u₁) 2) * clarkLStar (clarkAngle u₁))
      atTop (𝓝 LStar) := by
  have h12 := tendsto_piece1.add tendsto_piece2
  have h123 := h12.add tendsto_piece3
  have htarget : (∫ x in Set.Ioc (airyZero 1) 1, airyAi x ^ 2 / (x - airyZero 1)) +
      (∫ x in Set.Ioi 1, airyAi x ^ 2 / (x - airyZero 1)) + 0 = LStar := by
    rw [add_zero]
    have hIoc : IntegrableOn (fun x : ℝ => airyAi x ^ 2 / (x - airyZero 1)) (Set.Ioc (airyZero 1) 1) := by
      have h1 : IntegrableOn (fun x : ℝ => -(airyExtremal (x : ℂ)).re) (Set.Ioc (airyZero 1) 1) :=
        airyExtremal_integrable.re.neg.integrableOn
      refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioc
      dsimp only
      rw [airyExtremal_re, neg_neg]
    have hunion : Set.Ioc (airyZero 1) 1 ∪ Set.Ioi 1 = Set.Ioi (airyZero 1) :=
      Set.Ioc_union_Ioi_eq_Ioi (by linarith [airyZero_neg 1])
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc
      integrableOn_airyRatioSq_Ioi_one, hunion]
    rfl
  rw [htarget] at h123
  refine h123.congr' ?_
  filter_upwards [eventually_ge_atTop (max 2 (2 * |airyZero 2| + 2))] with u₁ hu₁
  have hu₁_2 : 2 ≤ u₁ := (le_max_left _ _).trans hu₁
  have hu₁_a1 : airyZero 1 < u₁ := (airyZero_neg 1).trans (by linarith)
  have hz1 : clarkNode (clarkAngle u₁) 1 = u₁ := (clarkAngle_spec hu₁_a1).2
  have hz2 := airyZero_two_lt_clarkNode_two hu₁_a1
  have hcont : Continuous (fun x : ℝ =>
      (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((differentiable_clarkExtremal (clarkAngle u₁)).continuous.comp continuous_ofReal)).neg
  have hL : (u₁ - clarkNode (clarkAngle u₁) 2) * clarkLStar (clarkAngle u₁) =
      ∫ x in clarkNode (clarkAngle u₁) 2..u₁,
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re := by
    unfold clarkLStar
    rw [hz1, ← integral_const_mul, setIntegral_congr_set Ioo_ae_eq_Ioc,
      intervalIntegral.integral_of_le (by linarith [hz2.2, airyZero_neg 1])]
  have hP1 : (∫ x in Set.Ioc (airyZero 2) 1,
      if clarkNode (clarkAngle u₁) 2 < x then
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re
      else 0) =
      ∫ x in clarkNode (clarkAngle u₁) 2..1,
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re := by
    rw [← integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le (by linarith [hz2.2, airyZero_neg 1]),
      ← integral_indicator measurableSet_Ioc]
    congr 1
    ext x
    by_cases h1 : x ∈ Set.Ioc (airyZero 2) 1
    · by_cases h2 : clarkNode (clarkAngle u₁) 2 < x
      · simp [h1, h2, h1.2]
      · have : x ∉ Set.Ioc (clarkNode (clarkAngle u₁) 2) 1 := fun hx => h2 hx.1
        simp [h1, h2, this]
    · have : x ∉ Set.Ioc (clarkNode (clarkAngle u₁) 2) 1 := fun hx =>
        h1 ⟨hz2.1.trans hx.1, hx.2⟩
      simp [h1, this]
  have hP2 : (∫ x in Set.Ioi 1,
      if x ≤ u₁ / 2 then
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re
      else 0) =
      ∫ x in (1 : ℝ)..(u₁ / 2),
        (u₁ - clarkNode (clarkAngle u₁) 2) * -(clarkExtremal (clarkAngle u₁) (x : ℂ)).re := by
    rw [← integral_indicator (μ := volume) measurableSet_Ioi,
      intervalIntegral.integral_of_le (by linarith),
      ← integral_indicator (μ := volume) measurableSet_Ioc]
    congr 1
    ext x
    by_cases h1 : 1 < x
    · by_cases h2 : x ≤ u₁ / 2
      · simp [h1, h2]
      · have : x ∉ Set.Ioc 1 (u₁ / 2) := fun hx => h2 hx.2
        simp [h1, h2, this]
    · have : x ∉ Set.Ioc 1 (u₁ / 2) := fun hx => h1 hx.1
      simp [h1, this]
  rw [hP1, hP2, hL]
  have hi1 := hcont.intervalIntegrable (μ := volume) (clarkNode (clarkAngle u₁) 2) 1
  have hi2 := hcont.intervalIntegrable (μ := volume) 1 (u₁ / 2)
  have hi3 := hcont.intervalIntegrable (μ := volume) (u₁ / 2) u₁
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
  linarith

/-- **Theorem SE.6 (`se:3.1`), second assertion.**
`κ₂(u₁) → (2 L_*^{(0)})⁻¹` as `u₁ → +∞`, where `L_*^{(0)} = LStar = ∫_{a₁}^∞ Ai(u)²/(u - a₁) du`. -/
theorem tendsto_clarkKappa2_atTop :
    Tendsto clarkKappa2 atTop (𝓝 ((2 * LStar)⁻¹)) := by
  have hnum : Tendsto (fun u₁ : ℝ =>
      Real.cos (clarkAngle u₁) ^ 2 - clarkNode (clarkAngle u₁) 2 * Real.sin (clarkAngle u₁) ^ 2)
      atTop (𝓝 1) := by
    have h := tendsto_cos_sq_clarkAngle_atTop.sub (tendsto_z2_atTop.mul tendsto_sin_sq_clarkAngle_atTop)
    simpa using h
  have hden : Tendsto (fun u₁ : ℝ =>
      (u₁ - clarkNode (clarkAngle u₁) 2) * (2 * clarkLStar (clarkAngle u₁)))
      atTop (𝓝 (2 * LStar)) := by
    have h := tendsto_clarkDenom_atTop.const_mul 2
    refine h.congr (fun u₁ => by ring)
  have h2L : 2 * LStar ≠ 0 := (mul_pos two_pos LStar_pos).ne'
  have hdiv : Tendsto (fun u₁ : ℝ =>
      (Real.cos (clarkAngle u₁) ^ 2 - clarkNode (clarkAngle u₁) 2 * Real.sin (clarkAngle u₁) ^ 2) /
        ((u₁ - clarkNode (clarkAngle u₁) 2) * (2 * clarkLStar (clarkAngle u₁))))
      atTop (𝓝 (1 / (2 * LStar))) := hnum.div hden h2L
  rw [one_div] at hdiv
  exact hdiv

lemma two_mul_LStar_eq_quantC1Mass : 2 * LStar = quantC1Mass := by
  have hiC : Integrable (fun u : ℝ => airyExtremal (u : ℂ)) := airyExtremal_integrable
  have hiRe : Integrable (fun u : ℝ => (airyExtremal (u : ℂ)).re) := hiC.re
  have hzero : ∫ u : ℝ, (airyExtremal (u : ℂ)).re = 0 := by
    have h2 : ∫ u : ℝ, (airyExtremal (u : ℂ)).re = (∫ u : ℝ, airyExtremal (u : ℂ)).re :=
      integral_re hiC
    rw [h2, airyExtremal_integral]; rfl
  have hsplit : (∫ u in Iic (airyZero 1), (airyExtremal (u : ℂ)).re) +
      ∫ u in Ioi (airyZero 1), (airyExtremal (u : ℂ)).re =
      ∫ u : ℝ, (airyExtremal (u : ℂ)).re := by
    simpa only [compl_Iic] using integral_add_compl measurableSet_Iic hiRe
  have hnorm_u : ∀ u : ℝ, ‖airyExtremal (u : ℂ)‖ = |(airyExtremal (u : ℂ)).re| := fun u => by
    rw [airyExtremal_ofReal, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]
  have hsplit_abs : (∫ u in Iic (airyZero 1), ‖airyExtremal (u : ℂ)‖) +
      ∫ u in Ioi (airyZero 1), ‖airyExtremal (u : ℂ)‖ =
      ∫ u : ℝ, ‖airyExtremal (u : ℂ)‖ := by
    simpa only [compl_Iic] using integral_add_compl measurableSet_Iic hiC.norm
  have hIic : ∫ u in Iic (airyZero 1), ‖airyExtremal (u : ℂ)‖ =
      ∫ u in Iic (airyZero 1), (airyExtremal (u : ℂ)).re := by
    refine setIntegral_congr_fun measurableSet_Iic fun u hu => ?_
    rw [hnorm_u u, abs_of_nonneg (airyExtremal_nonneg hu)]
  have hIoi_abs : ∫ u in Ioi (airyZero 1), ‖airyExtremal (u : ℂ)‖ =
      -(∫ u in Ioi (airyZero 1), (airyExtremal (u : ℂ)).re) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [hnorm_u u, airyExtremal_re, abs_of_nonpos]
    have : 0 ≤ airyAi u ^ 2 / (u - airyZero 1) := div_nonneg (sq_nonneg _) (sub_pos.mpr hu).le
    linarith
  have hIoi_L : -(∫ u in Ioi (airyZero 1), (airyExtremal (u : ℂ)).re) = LStar := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [airyExtremal_re, neg_neg]
  have hiic_val : ∫ u in Iic (airyZero 1), (airyExtremal (u : ℂ)).re = LStar := by
    rw [hzero] at hsplit; linarith [hIoi_L]
  show 2 * LStar = ∫ u : ℝ, ‖airyExtremal (u : ℂ)‖
  linarith [hsplit_abs, hIic, hIoi_abs, hIoi_L, hiic_val]

/-- Corollary of `tendsto_clarkKappa2_atTop` in terms of `quantC1Mass` (Theorem B-stab constant). -/
theorem tendsto_clarkKappa2_atTop_quantC1Mass :
    Tendsto clarkKappa2 atTop (𝓝 quantC1Mass⁻¹) := by
  rw [← two_mul_LStar_eq_quantC1Mass]
  exact tendsto_clarkKappa2_atTop

/-- info: 'FormalResearch.ModularBootstrap.Stability.clark_stability_kappa2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_stability_kappa2

/-- info: 'FormalResearch.ModularBootstrap.Stability.tendsto_clarkKappa2_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_clarkKappa2_atTop

/-- info: 'FormalResearch.ModularBootstrap.Stability.tendsto_clarkKappa2_atTop_quantC1Mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_clarkKappa2_atTop_quantC1Mass

end FormalResearch.ModularBootstrap.Stability
