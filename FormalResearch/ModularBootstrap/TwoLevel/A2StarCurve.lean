module

public import FormalResearch.SignUncertainty.ClarkTwoNode
public import FormalResearch.ModularBootstrap.Constants

/-!
# The Clark--Airy curve `A_2^*` (`virasoro_two_level.tex`, Theorem 2.1)

For `u₁ > a₁` let `α(u₁) ∈ (-π/2, π/2] \ {0}` be the angle with `z₁(α) = u₁`
(`existsUnique_clarkAngle_of_gt`), and put
`A_2^*(A₁) := c_* · |z₂(α(-A₁/c_*))|` for `A₁ < A_opt`.

* `clarkAngle`, `A2star`: the definitions (`cStar` is `c_*` of `Constants.lean`).
* `clarkNode_two_eq_airyClarkNode_ratio`: `z₂(α(u₁)) = z₂(Ai'(u₁)/Ai(u₁))` in the `c = cot α` labelling.
* `A2star_mem_Ioo`: `A_2^*(A₁) ∈ (A_opt, c_*|a₂|)` for `A₁ < A_opt`.
* `A2star_strictMonoOn`: `A_2^*` is strictly increasing on `(-∞, A_opt)`.
* `tendsto_A2star_nhdsLT`: `A_2^*(A_opt⁻) = c_*|a₂|`; `tendsto_A2star_atBot`: `A_2^*(A₁) → A_opt` as `A₁ → -∞`.

Not formalised: real-analyticity of `A_2^*`, the rate `O(|A₁|^{-1/2})` and the constant `0.0407`, the numerical values.
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty

/-- The Clark angle `α(u₁)` with `z₁(α) = u₁` (junk value `0` for `u₁ ≤ a₁`). -/
noncomputable def clarkAngle (u : ℝ) : ℝ :=
  if h : airyZero 1 < u then Classical.choose (existsUnique_clarkAngle_of_gt h).exists else 0

lemma clarkAngle_spec {u : ℝ} (hu : airyZero 1 < u) :
    clarkAngle u ∈ clarkAngleDomain ∧ clarkNode (clarkAngle u) 1 = u := by
  unfold clarkAngle
  split_ifs
  exact Classical.choose_spec (existsUnique_clarkAngle_of_gt hu).exists

lemma sin_clarkAngle_ne_zero {u : ℝ} (hu : airyZero 1 < u) : Real.sin (clarkAngle u) ≠ 0 :=
  sin_ne_zero_of_mem_clarkAngleDomain (clarkAngle_spec hu).1

/-- The curve `A_2^*(A₁) = c_* |z₂(α(-A₁/c_*))|`. -/
noncomputable def A2star (A₁ : ℝ) : ℝ := cStar * |clarkNode (clarkAngle (-A₁ / cStar)) 2|

lemma mem_gap_one_of_lt_Aopt {A₁ : ℝ} (hA : A₁ < Aopt) : airyZero 1 < -A₁ / cStar := by
  have hc := cStar_pos
  rw [lt_div_iff₀ hc]
  have : Aopt = cStar * |airyZero 1| := rfl
  rw [abs_of_neg (airyZero_neg 1)] at this
  nlinarith

/-- `cot (α(u₁)) = Ai'(u₁)/Ai(u₁)`. -/
lemma cot_clarkAngle {u : ℝ} (hu : airyZero 1 < u) :
    Real.cos (clarkAngle u) / Real.sin (clarkAngle u) = airyRatio u := by
  have h1 : airyClarkNode (Real.cos (clarkAngle u) / Real.sin (clarkAngle u)) 1 = u :=
    (clarkAngle_spec hu).2
  have hgap : u ∈ airyClarkGap 1 := by rw [airyClarkGap_one]; exact hu
  have h2 : airyClarkNode (airyRatio u) 1 = u := airyClarkNode_ratio le_rfl hgap
  exact (airyClarkNode_strictAnti (n := 1) le_rfl).injective (h1.trans h2.symm)

/-- `z₂(α(u₁)) = z₂(Ai'(u₁)/Ai(u₁))`. -/
lemma clarkNode_two_eq_airyClarkNode_ratio {u : ℝ} (hu : airyZero 1 < u) :
    clarkNode (clarkAngle u) 2 = airyClarkNode (airyRatio u) 2 := by
  change airyClarkNode (Real.cos (clarkAngle u) / Real.sin (clarkAngle u)) 2 = _
  rw [cot_clarkAngle hu]

lemma airyZero_two_lt_clarkNode_two {u : ℝ} (hu : airyZero 1 < u) :
    airyZero 2 < clarkNode (clarkAngle u) 2 ∧ clarkNode (clarkAngle u) 2 < airyZero 1 := by
  rw [clarkNode_two_eq_airyClarkNode_ratio hu]
  exact ⟨airyZero_lt_airyClarkNode (by norm_num) _, airyClarkNode_lt_airyZero (by norm_num) _⟩

lemma A2star_eq {A₁ : ℝ} (hA : A₁ < Aopt) :
    A2star A₁ = -(cStar * airyClarkNode (airyRatio (-A₁ / cStar)) 2) := by
  have hu := mem_gap_one_of_lt_Aopt hA
  have h := airyZero_two_lt_clarkNode_two hu
  unfold A2star
  rw [abs_of_neg (h.2.trans (airyZero_neg 1)), clarkNode_two_eq_airyClarkNode_ratio hu]
  ring

/-- **Range of the curve** (`virasoro_two_level.tex`, Theorem 2.1): `A_2^*(A₁) ∈ (A_opt, c_*|a₂|)`. -/
theorem A2star_mem_Ioo {A₁ : ℝ} (hA : A₁ < Aopt) :
    Aopt < A2star A₁ ∧ A2star A₁ < cStar * |airyZero 2| := by
  have hu := mem_gap_one_of_lt_Aopt hA
  have h := airyZero_two_lt_clarkNode_two hu
  have hc := cStar_pos
  have h1 := airyZero_neg 1
  have h2 := airyZero_neg 2
  have hz := h.2.trans h1
  unfold A2star Aopt
  rw [abs_of_neg hz, abs_of_neg h1, abs_of_neg h2]
  constructor <;> nlinarith [h.1, h.2]

/-- **Strict monotonicity** (`virasoro_two_level.tex`, Theorem 2.1): `A_2^*` is strictly
increasing on `(-∞, A_opt)`. -/
theorem A2star_strictMonoOn : StrictMonoOn A2star (Iio Aopt) := by
  intro A hA B hB hAB
  have hA' : A < Aopt := hA
  have hB' : B < Aopt := hB
  rw [A2star_eq hA', A2star_eq hB']
  have hc := cStar_pos
  have hu : -B / cStar < -A / cStar :=
    div_lt_div_of_pos_right (by linarith) hc
  have hgapB : -B / cStar ∈ airyClarkGap 1 := by
    rw [airyClarkGap_one]; exact mem_gap_one_of_lt_Aopt hB'
  have hgapA : -A / cStar ∈ airyClarkGap 1 := by
    rw [airyClarkGap_one]; exact mem_gap_one_of_lt_Aopt hA'
  have hr : airyRatio (-A / cStar) < airyRatio (-B / cStar) :=
    strictAntiOn_airyRatio le_rfl hgapB hgapA hu
  have hn := airyClarkNode_strictAnti (n := 2) (by norm_num) hr
  simp only at hn
  nlinarith

lemma tendsto_airyRatio_nhdsGT :
    Tendsto airyRatio (𝓝[>] (airyZero 1)) atTop := by
  rw [tendsto_atTop]
  intro c
  have hx : airyClarkNode c 1 ∈ airyClarkGap 1 := airyClarkNode_mem_gap le_rfl c
  have hx' : airyZero 1 < airyClarkNode c 1 := airyZero_lt_airyClarkNode le_rfl c
  filter_upwards [Ioo_mem_nhdsGT hx'] with u hu
  have hug : u ∈ airyClarkGap 1 := by rw [airyClarkGap_one]; exact hu.1
  have := strictAntiOn_airyRatio (n := 1) le_rfl hug hx hu.2
  rw [airyRatio_airyClarkNode le_rfl] at this
  exact this.le

lemma tendsto_airyRatio_atTop : Tendsto airyRatio atTop atBot := by
  rw [tendsto_atBot]
  intro c
  have hx : airyClarkNode c 1 ∈ airyClarkGap 1 := airyClarkNode_mem_gap le_rfl c
  filter_upwards [eventually_gt_atTop (airyClarkNode c 1)] with u hu
  have hug : u ∈ airyClarkGap 1 := by
    rw [airyClarkGap_one]; exact (airyZero_lt_airyClarkNode le_rfl c).trans hu
  have := strictAntiOn_airyRatio (n := 1) le_rfl hx hug hu
  rw [airyRatio_airyClarkNode le_rfl] at this
  exact this.le

/-- **Endpoint of the curve** (`virasoro_two_level.tex`, Theorem 2.1):
`A_2^*(A_opt⁻) = c_* |a₂|`. -/
theorem tendsto_A2star_nhdsLT : Tendsto A2star (𝓝[<] Aopt) (𝓝 (cStar * |airyZero 2|)) := by
  have hc := cStar_pos
  have hmap : Tendsto (fun A : ℝ => -A / cStar) (𝓝[<] Aopt) (𝓝[>] (airyZero 1)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous (fun A : ℝ => -A / cStar) := (continuous_neg.div_const _)
      have : (fun A : ℝ => -A / cStar) Aopt = airyZero 1 := by
        have h : Aopt = cStar * |airyZero 1| := rfl
        rw [abs_of_neg (airyZero_neg 1)] at h
        simp only
        rw [h]; field_simp
      rw [← this]
      exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with A hA
      exact mem_gap_one_of_lt_Aopt hA
  have h1 : Tendsto (fun A : ℝ => airyRatio (-A / cStar)) (𝓝[<] Aopt) atTop :=
    tendsto_airyRatio_nhdsGT.comp hmap
  have h2 : Tendsto (fun A : ℝ => airyClarkNode (airyRatio (-A / cStar)) 2) (𝓝[<] Aopt)
      (𝓝 (airyZero 2)) := (tendsto_airyClarkNode_atTop (by norm_num)).comp h1
  have h3 : Tendsto (fun A : ℝ => -(cStar * airyClarkNode (airyRatio (-A / cStar)) 2)) (𝓝[<] Aopt)
      (𝓝 (-(cStar * airyZero 2))) := (h2.const_mul cStar).neg
  have h4 : -(cStar * airyZero 2) = cStar * |airyZero 2| := by
    rw [abs_of_neg (airyZero_neg 2)]; ring
  rw [← h4]
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with A hA
  exact (A2star_eq hA).symm

/-- `A_2^*(A₁) → A_opt` as `A₁ → -∞` (qualitative; the rate `O(|A₁|^{-1/2})` is not formalised). -/
theorem tendsto_A2star_atBot : Tendsto A2star atBot (𝓝 Aopt) := by
  have hc := cStar_pos
  have hmap : Tendsto (fun A : ℝ => -A / cStar) atBot atTop :=
    (tendsto_neg_atBot_atTop.atTop_div_const hc)
  have h1 : Tendsto (fun A : ℝ => airyRatio (-A / cStar)) atBot atBot :=
    tendsto_airyRatio_atTop.comp hmap
  have h2 : Tendsto (fun A : ℝ => airyClarkNode (airyRatio (-A / cStar)) 2) atBot
      (𝓝 (airyZero (2 - 1))) := (tendsto_airyClarkNode_atBot (by norm_num)).comp h1
  have h3 := (h2.const_mul cStar).neg
  have h4 : -(cStar * airyZero (2 - 1)) = Aopt := by
    have h : Aopt = cStar * |airyZero 1| := rfl
    rw [abs_of_neg (airyZero_neg 1)] at h
    rw [h]; norm_num
  rw [h4] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_lt_atBot Aopt] with A hA
  exact (A2star_eq hA).symm

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.A2star_mem_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms A2star_mem_Ioo

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.A2star_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms A2star_strictMonoOn

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_A2star_nhdsLT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_A2star_nhdsLT

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_A2star_atBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_A2star_atBot

end FormalResearch.ModularBootstrap.TwoLevel
