module

public import FormalResearch.ModularBootstrap.Duality.MomentProblem
public import FormalResearch.ModularBootstrap.Duality.MeasureCompactness

/-!
# Compactification `[T₀, ∞] ≅ [0, 1]` and the continuous test functions `Ξ_β / w_*`

The measures `w_* dν` of Theorem E live on `[T, ∞)` and have total mass `≤ C₀`; the functions
`Ξ_β / w_*` vanish at infinity (Lemma M(c)). With `s = 1 / (1 + t - T₀) ∈ (0, 1]` and `s = 0`
for `t = ∞`, they become continuous functions on the compact space `[0, 1]`, so that weak
compactness of finite measures on `[0, 1]` applies.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real NNReal BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.Duality

open FormalResearch.ModularBootstrap.Crossing

/-- The compact interval `[0, 1]` compactifying `[T₀, ∞]`. -/
abbrev Ecoord : Type := Set.Icc (0 : ℝ) 1

/-- `t ↦ 1 / (1 + max (t - T₀) 0)`, clamped to `[0, 1]` (only `t ≥ T₀` matters). -/
noncomputable def toE (T₀ t : ℝ) : Ecoord :=
  Set.projIcc 0 1 zero_le_one (1 + max (t - T₀) 0)⁻¹

/-- Inverse coordinate `s ↦ T₀ + 1/s - 1` (junk at `s = 0`). -/
noncomputable def tauE (T₀ : ℝ) (s : Ecoord) : ℝ := T₀ + s.1⁻¹ - 1

lemma continuous_toE (T₀ : ℝ) : Continuous (toE T₀) := by
  unfold toE
  refine continuous_projIcc.comp ?_
  refine Continuous.inv₀ (by fun_prop) fun t => ?_
  have : 0 ≤ max (t - T₀) 0 := le_max_right _ _
  linarith

lemma toE_val {T₀ t : ℝ} (ht : T₀ ≤ t) : (toE T₀ t).1 = (1 + (t - T₀))⁻¹ := by
  have h : 0 ≤ t - T₀ := by linarith
  have hmem : (1 + (t - T₀))⁻¹ ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [inv_le_one₀ (by linarith)]; linarith
  unfold toE
  rw [max_eq_left (by linarith), Set.projIcc_of_mem _ hmem]

lemma toE_pos {T₀ t : ℝ} (ht : T₀ ≤ t) : 0 < (toE T₀ t).1 := by
  rw [toE_val ht]
  have : 0 ≤ t - T₀ := by linarith
  positivity

lemma tauE_toE {T₀ t : ℝ} (ht : T₀ ≤ t) : tauE T₀ (toE T₀ t) = t := by
  unfold tauE
  rw [toE_val ht, inv_inv]; ring

lemma tauE_ge {T₀ : ℝ} {s : Ecoord} (hs : 0 < s.1) : T₀ ≤ tauE T₀ s := by
  unfold tauE
  have : 1 ≤ s.1⁻¹ := (one_le_inv₀ hs).2 s.2.2
  linarith

lemma continuousAt_tauE (T₀ : ℝ) {s : Ecoord} (hs : 0 < s.1) : ContinuousAt (tauE T₀) s := by
  unfold tauE
  have : ContinuousAt (fun s : Ecoord => s.1) s := continuous_subtype_val.continuousAt
  exact (continuousAt_const.add (this.inv₀ hs.ne')).sub continuousAt_const

/-- The function `s ↦ Ξ_β(τ s) / w_*(τ s)` for `s > 0` and `0` at `s = 0`. -/
noncomputable def Ftilde (a β₀ T₀ β : ℝ) (s : Ecoord) : ℝ :=
  if s.1 = 0 then 0 else thermalDiff 1 β (tauE T₀ s) / wStar a β₀ (tauE T₀ s)

lemma Ftilde_toE (a β₀ T₀ β : ℝ) {t : ℝ} (ht : T₀ ≤ t) :
    Ftilde a β₀ T₀ β (toE T₀ t) = thermalDiff 1 β t / wStar a β₀ t := by
  have := (toE_pos ht).ne'
  simp [Ftilde, this, tauE_toE ht]

lemma continuousOn_wStar {a β₀ : ℝ} (ha : 0 < a) : ContinuousOn (wStar a β₀) (Ici 0) := by
  unfold wStar
  refine continuousOn_of_dominated (bound := fun β => thetaW a β) ?_ ?_ ?_ ?_
  · intro t _
    exact (by have := measurable_thetaW a; fun_prop :
      Measurable fun β : ℝ => Real.exp (-2 * π * β * t) * thetaW a β).aestronglyMeasurable
  · intro t ht
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (thetaW_pos a β).le)]
    have e1 : Real.exp (-2 * π * β * t) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ β * t := mul_nonneg hβ.1.le (mem_Ici.1 ht)
      nlinarith [Real.pi_pos])
    calc _ ≤ 1 * thetaW a β := mul_le_mul_of_nonneg_right e1 (thetaW_pos a β).le
      _ = _ := one_mul _
  · refine Integrable.of_bound (C := Real.exp (8 * π * a)) ?_ ?_
    · exact (measurable_thetaW a).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun β hβ => ?_
      rw [Real.norm_of_nonneg (thetaW_pos a β).le]
      exact thetaW_le ha.le hβ.1
  · refine Eventually.of_forall fun β => ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    fun_prop

lemma continuous_Ftilde {a β₀ T₀ β : ℝ} (ha : 0 < a) (hβ₀ : 0 < β₀) (hT₀ : 0 < T₀) (hβ : 0 < β) :
    Continuous (Ftilde a β₀ T₀ β) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  by_cases h0 : s₀.1 = 0
  · -- at the point `s = 0`
    have hF0 : Ftilde a β₀ T₀ β s₀ = 0 := by simp [Ftilde, h0]
    rw [ContinuousAt, hF0, Metric.tendsto_nhds]
    intro ε hε
    have hlim := tendsto_thermalDiff_div_wStar (a := a) ha.le hβ₀ hβ
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨R, hR⟩ := hlim ε hε
    set R' : ℝ := max (R - T₀ + 1) 1 with hR'
    have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hnhd : {s : Ecoord | s.1 < (R')⁻¹} ∈ 𝓝 s₀ := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_subtype_val continuous_const) ?_
      simp [h0, hR'pos]
    filter_upwards [hnhd] with s hs
    by_cases hs0 : s.1 = 0
    · simp [Ftilde, hs0, hε]
    · have hspos : 0 < s.1 := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
      have h1 : R' < s.1⁻¹ := by
        rw [lt_inv_comm₀ hR'pos hspos]; exact hs
      have h2 : R ≤ tauE T₀ s := by
        unfold tauE
        have : R - T₀ + 1 ≤ R' := le_max_left _ _
        linarith
      have := hR (tauE T₀ s) h2
      rw [Real.dist_eq, sub_zero] at this
      have hF : Ftilde a β₀ T₀ β s = thermalDiff 1 β (tauE T₀ s) / wStar a β₀ (tauE T₀ s) := by
        simp [Ftilde, hs0]
      rw [Real.dist_eq, sub_zero, hF]
      exact this
  · have hpos : 0 < s₀.1 := lt_of_le_of_ne s₀.2.1 (Ne.symm h0)
    have hτ := continuousAt_tauE T₀ hpos
    have hT : 0 < tauE T₀ s₀ := lt_of_lt_of_le hT₀ (tauE_ge hpos)
    have hg : ContinuousAt (fun t => thermalDiff 1 β t / wStar a β₀ t) (tauE T₀ s₀) := by
      have hw : ContinuousAt (wStar a β₀) (tauE T₀ s₀) :=
        (continuousOn_wStar ha).continuousAt (Ici_mem_nhds hT)
      refine ContinuousAt.div (by unfold thermalDiff; fun_prop) hw ?_
      exact (wStar_pos ha.le hβ₀ hT.le).ne'
    have hcomp : ContinuousAt (fun s => thermalDiff 1 β (tauE T₀ s) / wStar a β₀ (tauE T₀ s)) s₀ :=
      hg.comp hτ
    refine hcomp.congr ?_
    have : {s : Ecoord | s.1 ≠ 0} ∈ 𝓝 s₀ :=
      (isOpen_ne_fun continuous_subtype_val continuous_const).mem_nhds h0
    filter_upwards [this] with s hs
    simp [Ftilde, hs]

/-- `Ftilde` as a bounded continuous function on the compact interval. -/
noncomputable def FtildeB {a β₀ T₀ β : ℝ} (ha : 0 < a) (hβ₀ : 0 < β₀) (hT₀ : 0 < T₀) (hβ : 0 < β) :
    Ecoord →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨Ftilde a β₀ T₀ β, continuous_Ftilde ha hβ₀ hT₀ hβ⟩

/-- Cut-off `ζ_T(s) = max(s - 1/(1 + T - T₀), 0)`, positive exactly for `t = τ(s) < T`. -/
noncomputable def zetaB (T₀ T : ℝ) : Ecoord →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun s => max (s.1 - (1 + (T - T₀))⁻¹) 0, by fun_prop⟩

lemma zetaB_nonneg (T₀ T : ℝ) (s : Ecoord) : 0 ≤ zetaB T₀ T s := le_max_right _ _

lemma zetaB_toE {T₀ T t : ℝ} (hT : T₀ ≤ T) (ht : T ≤ t) : zetaB T₀ T (toE T₀ t) = 0 := by
  have ht0 : T₀ ≤ t := hT.trans ht
  show max _ 0 = 0
  rw [toE_val ht0]
  apply max_eq_right
  have : (1 + (t - T₀))⁻¹ ≤ (1 + (T - T₀))⁻¹ := by
    apply inv_anti₀ (by linarith); linarith
  linarith

lemma zetaB_pos_iff {T₀ T : ℝ} (hT : T₀ ≤ T) {s : Ecoord} (hs : 0 < s.1) :
    0 < zetaB T₀ T s ↔ tauE T₀ s < T := by
  show 0 < max _ 0 ↔ _
  have hTp : 0 < 1 + (T - T₀) := by linarith
  rw [lt_max_iff]
  simp only [lt_self_iff_false, or_false, sub_pos]
  unfold tauE
  rw [inv_lt_comm₀ hTp hs]
  constructor <;> intro h <;> linarith

/-- info: 'FormalResearch.ModularBootstrap.Duality.continuous_Ftilde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.continuous_Ftilde

end FormalResearch.ModularBootstrap.Duality
