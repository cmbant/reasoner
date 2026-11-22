module

public import FormalResearch.ModularBootstrap.Crossing.MehlerOddMoment
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The dual majorant `h` (Lemma M of `dual_spectrum.tex`)

Source: `CFT/modular_bootstrap/paper/dual_spectrum.tex`, Lemma M (`ds:M`), for the spinless Virasoro
problem (`virasoroProblem`, `w = 1`, `Q(q) = (1-q)²`).

`h = 2 ∫₀^{β₀} Ξ_β ϑ(dβ)` with `ϑ(dβ) = e^{-4πa(1/β-2)} dβ` lies in the test class
`\overline{\mathcal A}` (continuity, `L¹`, Fourier oddness and finite Cardy norm by Fubini against the
thermal differences `Ξ_β`), has `h_vac = -C₀ < 0`, dominates `w_*(t) = ∫ e^{-2πβt} ϑ(dβ)` on
`[T₀, ∞)`, and `w_*` dominates every `e^{-2πβt}` while `Ξ_β / w_* → 0`.

The main statement is `lemma_M`; the pieces (`hMaj_mem_TestClass`, `hMaj_vac`, `dualC0_pos`,
`wStar_le_hMaj`, `exp_le_const_wStar`, `tendsto_thermalDiff_div_wStar`) are also exported.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Duality

open FormalResearch.ModularBootstrap.Crossing

/-- `t₀(β) = β log(2/β) / (2π(1 - β²))`: `2 Ξ_β(t) ≥ e^{-2πβt}` iff `t ≥ t₀(β)` (`w = 1`). -/

noncomputable def t0 (β : ℝ) : ℝ := β * Real.log (2 / β) / (2 * π * (1 - β ^ 2))

lemma t0_mono {β β' : ℝ} (hβ : 0 < β) (hle : β ≤ β') (hβ' : β' ≤ 1 / 2) : t0 β ≤ t0 β' := by
  unfold t0
  have hβ'pos : 0 < β' := lt_of_lt_of_le hβ hle
  have hlog' : 1 ≤ Real.log (2 / β') := by
    have h4 : (4 : ℝ) ≤ 2 / β' := by
      rw [le_div_iff₀ hβ'pos]; linarith
    have : Real.log 4 ≤ Real.log (2 / β') := Real.log_le_log (by norm_num) h4
    have h4' : (1 : ℝ) ≤ Real.log 4 := by
      have := Real.exp_one_lt_three
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith
    linarith
  -- u(β) = β log(2/β)
  have hu : β * Real.log (2 / β) ≤ β' * Real.log (2 / β') := by
    have h1 : Real.log (2 / β) = Real.log (2 / β') + Real.log (β' / β) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1; field_simp
    have h2 : Real.log (β' / β) ≤ β' / β - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : β * Real.log (β' / β) ≤ β' - β := by
      have := mul_le_mul_of_nonneg_left h2 hβ.le
      calc β * Real.log (β' / β) ≤ β * (β' / β - 1) := this
        _ = β' - β := by field_simp
    rw [h1]
    nlinarith
  have hd1 : 0 < 1 - β ^ 2 := by nlinarith
  have hd2 : 0 < 1 - β' ^ 2 := by nlinarith
  have hlogpos : 0 ≤ Real.log (2 / β) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hβ]; linarith
  have hupos : 0 ≤ β * Real.log (2 / β) := mul_nonneg hβ.le hlogpos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (1 - β' ^ 2) ≤ (1 - β ^ 2) := by
    have := pow_le_pow_left₀ hβ.le hle 2
    linarith
  have hπ : 0 < 2 * π := by positivity
  calc β * Real.log (2 / β) * (2 * π * (1 - β' ^ 2))
      = (2 * π) * (β * Real.log (2 / β) * (1 - β' ^ 2)) := by ring
    _ ≤ (2 * π) * (β' * Real.log (2 / β') * (1 - β ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hπ.le
        exact mul_le_mul hu this hd2.le (by positivity)
    _ = _ := by ring

/-- `2 Ξ_β(t) ≥ e^{-2πβt}` for `t ≥ t0 β`, `0<β≤1/2`. (w = 1) -/
lemma two_thermalDiff_ge {β t : ℝ} (hβ : 0 < β) (hβ2 : β ≤ 1 / 2) (ht : t0 β ≤ t) :
    Real.exp (-2 * π * β * t) ≤ 2 * thermalDiff 1 β t := by
  unfold thermalDiff
  have hd1 : 0 < 1 - β ^ 2 := by nlinarith
  have hpos : 0 < 1 / β - β := by
    rw [sub_pos, lt_div_iff₀ hβ]; nlinarith
  have hexp : Real.exp (-2 * π * t / β) ≤ β / 2 * Real.exp (-2 * π * β * t) := by
    have h1 : -2 * π * t / β = -2 * π * β * t + (-(2 * π * t * (1 / β - β))) := by
      field_simp; ring
    rw [h1, Real.exp_add]
    have hle : Real.exp (-(2 * π * t * (1 / β - β))) ≤ β / 2 := by
      have hk : Real.log (2 / β) ≤ 2 * π * t * (1 / β - β) := by
        have : t0 β * (2 * π * (1 / β - β)) = Real.log (2 / β) := by
          unfold t0
          have : 1 / β - β = (1 - β ^ 2) / β := by field_simp
          rw [this]; field_simp
        rw [← this]
        have : 0 ≤ 2 * π * (1 / β - β) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right ht this]
      calc Real.exp (-(2 * π * t * (1 / β - β))) ≤ Real.exp (-Real.log (2 / β)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = β / 2 := by
            rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    have := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-2 * π * β * t)).le
    calc Real.exp (-2 * π * β * t) * Real.exp (-(2 * π * t * (1 / β - β)))
        ≤ Real.exp (-2 * π * β * t) * (β / 2) := this
      _ = β / 2 * Real.exp (-2 * π * β * t) := mul_comm _ _
  simp only [Nat.cast_one, Real.rpow_neg_one]
  have : β⁻¹ * Real.exp (-2 * π * t / β) ≤ 1 / 2 * Real.exp (-2 * π * β * t) := by
    calc β⁻¹ * Real.exp (-2 * π * t / β) ≤ β⁻¹ * (β / 2 * Real.exp (-2 * π * β * t)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 1 / 2 * Real.exp (-2 * π * β * t) := by field_simp
  linarith


/-- The measure density `ϑ(dβ) = e^{-4πa(1/β - 2)} dβ`. -/
noncomputable def thetaW (a β : ℝ) : ℝ := Real.exp (-4 * π * a * (β⁻¹ - 2))

lemma thetaW_pos (a β : ℝ) : 0 < thetaW a β := Real.exp_pos _

lemma measurable_thetaW (a : ℝ) : Measurable (thetaW a) := by
  unfold thetaW; fun_prop

lemma thetaW_eq (a β : ℝ) : thetaW a β = Real.exp (8 * π * a) * Real.exp (-(4 * π * a) / β) := by
  unfold thetaW; rw [← Real.exp_add]; congr 1; field_simp; ring

lemma thetaW_le {a : ℝ} (ha : 0 ≤ a) {β : ℝ} (hβ : 0 < β) : thetaW a β ≤ Real.exp (8 * π * a) := by
  rw [thetaW_eq]
  have : Real.exp (-(4 * π * a) / β) ≤ 1 := by
    rw [Real.exp_le_one_iff]; 
    have : 0 ≤ 4 * π * a / β := by positivity
    rw [neg_div]; linarith
  nlinarith [Real.exp_pos (8 * π * a)]

lemma thetaW_mono {a : ℝ} (ha : 0 ≤ a) {β β' : ℝ} (hβ : 0 < β) (h : β ≤ β') :
    thetaW a β ≤ thetaW a β' := by
  unfold thetaW
  apply Real.exp_le_exp.2
  have : β'⁻¹ ≤ β⁻¹ := inv_anti₀ hβ h
  have : 0 ≤ 4 * π * a := by positivity
  nlinarith

/-- `x e^{-x} ≤ 1` in the form `β⁻¹ e^{-c/β} ≤ 1/c`. -/
lemma inv_mul_exp_neg_div_le {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    β⁻¹ * Real.exp (-c / β) ≤ 1 / c := by
  have hx : c / β ≤ Real.exp (c / β) := by linarith [Real.add_one_le_exp (c / β)]
  have h1 : Real.exp (-c / β) = (Real.exp (c / β))⁻¹ := by
    rw [← Real.exp_neg, neg_div]
  rw [h1]
  have hpos : 0 < Real.exp (c / β) := Real.exp_pos _
  rw [show β⁻¹ * (Real.exp (c / β))⁻¹ = (c / β) / Real.exp (c / β) * (1 / c) by
    field_simp]
  have : (c / β) / Real.exp (c / β) ≤ 1 := by rw [div_le_one hpos]; exact hx
  nlinarith [one_div_pos.2 hc]

lemma inv_mul_thetaW_le {a : ℝ} (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    β⁻¹ * thetaW a β ≤ Real.exp (8 * π * a) / (4 * π * a) := by
  rw [thetaW_eq]
  have := inv_mul_exp_neg_div_le (by positivity : 0 < 4 * π * a) hβ
  calc β⁻¹ * (Real.exp (8 * π * a) * Real.exp (-(4 * π * a) / β))
      = Real.exp (8 * π * a) * (β⁻¹ * Real.exp (-(4 * π * a) / β)) := by ring
    _ ≤ Real.exp (8 * π * a) * (1 / (4 * π * a)) :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = _ := by ring

lemma inv_mul_exp_thetaW_le {a : ℝ} (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    β⁻¹ * Real.exp (2 * π * a / β) * thetaW a β ≤ Real.exp (8 * π * a) / (2 * π * a) := by
  rw [thetaW_eq]
  have := inv_mul_exp_neg_div_le (by positivity : 0 < 2 * π * a) hβ
  have h2 : Real.exp (2 * π * a / β) * Real.exp (-(4 * π * a) / β) = Real.exp (-(2 * π * a) / β) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  calc β⁻¹ * Real.exp (2 * π * a / β) * (Real.exp (8 * π * a) * Real.exp (-(4 * π * a) / β))
      = Real.exp (8 * π * a) * (β⁻¹ * (Real.exp (2 * π * a / β) * Real.exp (-(4 * π * a) / β))) := by
        ring
    _ = Real.exp (8 * π * a) * (β⁻¹ * Real.exp (-(2 * π * a) / β)) := by rw [h2]
    _ ≤ Real.exp (8 * π * a) * (1 / (2 * π * a)) :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = _ := by ring

/-- The weight `w_*(t) = ∫₀^{β₀} e^{-2πβt} ϑ(dβ)`. -/
noncomputable def wStar (a β₀ t : ℝ) : ℝ :=
  ∫ β in Ioc 0 β₀, Real.exp (-2 * π * β * t) * thetaW a β

lemma integrableOn_wStar_integrand {a : ℝ} (ha : 0 ≤ a) (β₀ t : ℝ) :
    IntegrableOn (fun β => Real.exp (-2 * π * β * t) * thetaW a β) (Ioc 0 β₀) := by
  refine Measure.integrableOn_of_bounded (M := Real.exp (2 * π * |β₀| * |t|) * Real.exp (8 * π * a))
    (by simp) ?_ ?_
  · exact (by have := measurable_thetaW a; fun_prop : Measurable fun β : ℝ =>
      Real.exp (-2 * π * β * t) * thetaW a β).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (thetaW_pos a β).le)]
    have h1 : Real.exp (-2 * π * β * t) ≤ Real.exp (2 * π * |β₀| * |t|) := by
      apply Real.exp_le_exp.2
      have : -(β * t) ≤ |β₀| * |t| := by
        calc -(β * t) ≤ |β * t| := neg_le_abs _
          _ = |β| * |t| := abs_mul _ _
          _ ≤ |β₀| * |t| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            rw [abs_of_pos hβ.1]; exact hβ.2.trans (le_abs_self _)
      nlinarith [Real.pi_pos]
    exact mul_le_mul h1 (thetaW_le ha hβ.1) (thetaW_pos a β).le (Real.exp_pos _).le

lemma wStar_lower {a β₀ β₁ t : ℝ} (ha : 0 ≤ a) (hβ₁ : 0 < β₁) (h2 : 2 * β₁ ≤ β₀) (ht : 0 ≤ t) :
    β₁ * (Real.exp (-4 * π * β₁ * t) * thetaW a β₁) ≤ wStar a β₀ t := by
  unfold wStar
  have hint := integrableOn_wStar_integrand ha β₀ t
  have hsub : Icc β₁ (2 * β₁) ⊆ Ioc 0 β₀ := fun β hβ => ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 β₀)] fun β => Real.exp (-2 * π * β * t) * thetaW a β :=
    Eventually.of_forall fun β => mul_nonneg (Real.exp_pos _).le (thetaW_pos a β).le
  have h1 := setIntegral_mono_set hint hnn (Eventually.of_forall hsub : Icc β₁ (2 * β₁) ≤ᵐ[volume] Ioc 0 β₀)
  have h2' := setIntegral_ge_of_const_le (μ := volume) (s := Icc β₁ (2 * β₁))
    (c := Real.exp (-4 * π * β₁ * t) * thetaW a β₁) measurableSet_Icc (by simp)
    (fun β hβ => by
      have e1 : Real.exp (-4 * π * β₁ * t) ≤ Real.exp (-2 * π * β * t) := by
        apply Real.exp_le_exp.2
        nlinarith [Real.pi_pos, hβ.2, mul_nonneg ht Real.pi_pos.le]
      exact mul_le_mul e1 (thetaW_mono ha hβ₁ hβ.1) (thetaW_pos a β₁).le (Real.exp_pos _).le)
    (hint.mono_set hsub)
  have : volume.real (Icc β₁ (2 * β₁)) = β₁ := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  rw [this] at h2'
  simp only [smul_eq_mul] at h2'
  linarith

lemma wStar_pos {a β₀ : ℝ} (ha : 0 ≤ a) (hβ₀ : 0 < β₀) {t : ℝ} (ht : 0 ≤ t) : 0 < wStar a β₀ t := by
  have := wStar_lower (a := a) (β₀ := β₀) (β₁ := β₀ / 2) (t := t) ha (by positivity) (by linarith) ht
  exact lt_of_lt_of_le (by have := thetaW_pos a (β₀ / 2); positivity) this

lemma exp_le_const_wStar {a β₀ : ℝ} (ha : 0 ≤ a) (hβ₀ : 0 < β₀) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ t, 0 ≤ t → Real.exp (-2 * π * β * t) ≤ C * wStar a β₀ t := by
  set β₁ := min (β / 2) (β₀ / 2) with hβ₁
  have hβ₁pos : 0 < β₁ := lt_min (by positivity) (by positivity)
  have h2 : 2 * β₁ ≤ β₀ := by have := min_le_right (β / 2) (β₀ / 2); linarith
  have h2' : 2 * β₁ ≤ β := by have := min_le_left (β / 2) (β₀ / 2); linarith
  have hc : 0 < β₁ * thetaW a β₁ := mul_pos hβ₁pos (thetaW_pos a β₁)
  refine ⟨(β₁ * thetaW a β₁)⁻¹, inv_pos.2 hc, fun t ht => ?_⟩
  have hlow := wStar_lower (a := a) (β₀ := β₀) (β₁ := β₁) (t := t) ha hβ₁pos h2 ht
  have hle : Real.exp (-2 * π * β * t) ≤ Real.exp (-4 * π * β₁ * t) := by
    apply Real.exp_le_exp.2; nlinarith [Real.pi_pos, mul_nonneg ht Real.pi_pos.le]
  rw [inv_mul_eq_div, le_div_iff₀ hc] at *
  · nlinarith [Real.exp_pos (-4 * π * β₁ * t)]



lemma thermalDiff_one (β t : ℝ) :
    thermalDiff 1 β t = Real.exp (-2 * π * β * t) - β⁻¹ * Real.exp (-2 * π * t / β) := by
  simp [thermalDiff, Real.rpow_neg_one]

lemma abs_thermalDiff_one_le {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    |thermalDiff 1 β t| ≤ Real.exp (-2 * π * β * t) + β⁻¹ * Real.exp (-2 * π * t / β) := by
  rw [thermalDiff_one]
  have h1 := Real.exp_pos (-2 * π * β * t)
  have h2 : 0 < β⁻¹ * Real.exp (-2 * π * t / β) := mul_pos (inv_pos.2 hβ) (Real.exp_pos _)
  rw [abs_le]; constructor <;> linarith

lemma integral_exp_neg_mul_Ioi' {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t)) (Ioi 0) ∧
      ∫ t in Ioi 0, Real.exp (-c * t) = 1 / c := by
  refine ⟨integrableOn_exp_mul_Ioi (by linarith) 0, ?_⟩
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp

/-- L¹ bound for `Ξ_β` (w = 1). -/
lemma integral_abs_thermalDiff_le {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => |thermalDiff 1 β t|) (Ioi 0) ∧
      ∫ t in Ioi 0, |thermalDiff 1 β t| ≤ 1 / (2 * π * β) + 1 / (2 * π) := by
  have hc1 : 0 < 2 * π * β := by positivity
  have hc2 : 0 < 2 * π / β := by positivity
  obtain ⟨i1, v1⟩ := integral_exp_neg_mul_Ioi' hc1
  obtain ⟨i2, v2⟩ := integral_exp_neg_mul_Ioi' hc2
  have hsum : IntegrableOn (fun t => Real.exp (-(2 * π * β) * t) +
      β⁻¹ * Real.exp (-(2 * π / β) * t)) (Ioi 0) := i1.add (i2.const_mul _)
  have hmeas : Measurable fun t => |thermalDiff 1 β t| := by
    unfold thermalDiff; fun_prop
  have hle : ∀ t ∈ Ioi (0:ℝ), |thermalDiff 1 β t| ≤ Real.exp (-(2 * π * β) * t) +
      β⁻¹ * Real.exp (-(2 * π / β) * t) := by
    intro t _
    have := abs_thermalDiff_one_le hβ t
    have e1 : -2 * π * β * t = -(2 * π * β) * t := by ring
    have e2 : -2 * π * t / β = -(2 * π / β) * t := by ring
    rwa [e1, e2] at this
  refine ⟨hsum.mono' hmeas.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hle t ht
  · have hint : IntegrableOn (fun t => |thermalDiff 1 β t|) (Ioi 0) :=
      hsum.mono' hmeas.aestronglyMeasurable (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hle t ht)
    calc ∫ t in Ioi 0, |thermalDiff 1 β t|
        ≤ ∫ t in Ioi 0, (Real.exp (-(2 * π * β) * t) + β⁻¹ * Real.exp (-(2 * π / β) * t)) :=
          setIntegral_mono_on hint hsum measurableSet_Ioi hle
      _ = 1 / (2 * π * β) + 1 / (2 * π) := by
          rw [integral_add i1 (i2.const_mul _), v1, integral_const_mul, v2]
          congr 1; field_simp

/-- Cardy-weighted L¹ bound for `Ξ_β` (Virasoro, `w = 1`), `a ≥ 2`. -/
lemma integral_abs_thermalDiff_V_le {a : ℝ} (ha : 2 ≤ a) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => |thermalDiff 1 β t| * virasoroProblem.cardyV a t) (Ioi 0) ∧
      ∫ t in Ioi 0, |thermalDiff 1 β t| * virasoroProblem.cardyV a t ≤
        (β⁻¹ * Real.exp (2 * π * a / β) + Real.exp (2 * π * a * β)) / (2 * π) := by
  have hts : virasoroProblem.totalShift ≤ a := by rw [virasoroProblem_totalShift]; exact ha
  have hint := (thermalDiff_mem_TestClass virasoroProblem hts hβ).int_cardy
  refine ⟨by simpa using hint, ?_⟩
  obtain ⟨i1, v1⟩ := virasoroProblem.cardyV_laplace a hβ
  obtain ⟨i2, v2⟩ := virasoroProblem.cardyV_laplace a (inv_pos.2 hβ)
  have hsum : IntegrableOn (fun t => virasoroProblem.cardyV a t * Real.exp (-2 * π * β * t) +
      β⁻¹ * (virasoroProblem.cardyV a t * Real.exp (-2 * π * β⁻¹ * t))) (Ioi 0) :=
    i1.add (i2.const_mul _)
  have hle : ∀ t ∈ Ioi (0:ℝ), |thermalDiff 1 β t| * virasoroProblem.cardyV a t ≤
      virasoroProblem.cardyV a t * Real.exp (-2 * π * β * t) +
      β⁻¹ * (virasoroProblem.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) := by
    intro t ht
    have hV := virasoroProblem.cardyV_nonneg hts (le_of_lt ht)
    have := abs_thermalDiff_one_le hβ t
    have e2 : -2 * π * t / β = -2 * π * β⁻¹ * t := by ring
    rw [e2] at this
    nlinarith
  have hint' : IntegrableOn (fun t => |thermalDiff 1 β t| * virasoroProblem.cardyV a t) (Ioi 0) := by
    simpa using hint
  calc ∫ t in Ioi 0, |thermalDiff 1 β t| * virasoroProblem.cardyV a t
      ≤ ∫ t in Ioi 0, (virasoroProblem.cardyV a t * Real.exp (-2 * π * β * t) +
          β⁻¹ * (virasoroProblem.cardyV a t * Real.exp (-2 * π * β⁻¹ * t))) :=
        setIntegral_mono_on hint' hsum measurableSet_Ioi hle
    _ = (∫ t in Ioi 0, virasoroProblem.cardyV a t * Real.exp (-2 * π * β * t)) +
          β⁻¹ * ∫ t in Ioi 0, virasoroProblem.cardyV a t * Real.exp (-2 * π * β⁻¹ * t) := by
        rw [integral_add i1 (i2.const_mul _), integral_const_mul]
    _ ≤ _ := by
        have q1 := virasoroProblem.nullPoly_le_one (q := Real.exp (-2 * π / β))
          (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by
            have : 0 ≤ 2 * π / β := by positivity
            rw [show -2 * π / β = -(2 * π / β) by ring]; linarith))
        have q2 := virasoroProblem.nullPoly_le_one (q := Real.exp (-2 * π / β⁻¹))
          (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by
            have : 0 ≤ 2 * π / β⁻¹ := by positivity
            rw [show -2 * π / β⁻¹ = -(2 * π / β⁻¹) by ring]; linarith))
        have p1 : 2 * π * ∫ t in Ioi 0, virasoroProblem.cardyV a t * Real.exp (-2 * π * β * t)
            ≤ β⁻¹ * Real.exp (2 * π * a / β) := by
          rw [v1]; simp only [virasoroProblem_w, Nat.cast_one, Real.rpow_neg_one]
          calc β⁻¹ * Real.exp (2 * π * a / β) * virasoroProblem.nullPoly (Real.exp (-2 * π / β))
              ≤ β⁻¹ * Real.exp (2 * π * a / β) * 1 :=
                mul_le_mul_of_nonneg_left q1 (by positivity)
            _ = _ := by ring
        have p2 : 2 * π * ∫ t in Ioi 0, virasoroProblem.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)
            ≤ β * Real.exp (2 * π * a * β) := by
          rw [v2]; simp only [virasoroProblem_w, Nat.cast_one, Real.rpow_neg_one, inv_inv]
          have e : 2 * π * a / β⁻¹ = 2 * π * a * β := by rw [div_inv_eq_mul]
          rw [e]
          calc β * Real.exp (2 * π * a * β) * virasoroProblem.nullPoly (Real.exp (-2 * π / β⁻¹))
              ≤ β * Real.exp (2 * π * a * β) * 1 :=
                mul_le_mul_of_nonneg_left q2 (by positivity)
            _ = _ := by ring
        have hπ : 0 < 2 * π := by positivity
        rw [le_div_iff₀ hπ]
        have h3 : β⁻¹ * (2 * π * ∫ t in Ioi 0, virasoroProblem.cardyV a t * Real.exp (-2 * π * β⁻¹ * t))
            ≤ β⁻¹ * (β * Real.exp (2 * π * a * β)) := mul_le_mul_of_nonneg_left p2 (by positivity)
        have h4 : β⁻¹ * (β * Real.exp (2 * π * a * β)) = Real.exp (2 * π * a * β) := by
          field_simp
        nlinarith


lemma integrable_prod_family {a β₀ B : ℝ} (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hφ0 : ∀ t, 0 < t → 0 ≤ φ t)
    (hB : ∀ β ∈ Ioc 0 β₀, IntegrableOn (fun t => |thermalDiff 1 β t| * φ t) (Ioi 0) ∧
        (∫ t in Ioi 0, |thermalDiff 1 β t| * φ t) * thetaW a β ≤ B) :
    Integrable (fun p : ℝ × ℝ => thermalDiff 1 p.2 p.1 * φ p.1 * thetaW a p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀))) := by
  have hFm : Measurable (fun p : ℝ × ℝ => thermalDiff 1 p.2 p.1 * φ p.1 * thetaW a p.2) := by
    have := measurable_thetaW a
    unfold thermalDiff
    fun_prop
  rw [integrable_prod_iff' hFm.aestronglyMeasurable]
  have hnorm : ∀ β ∈ Ioc 0 β₀, ∫ t, ‖thermalDiff 1 β t * φ t * thetaW a β‖ ∂(volume.restrict (Ioi 0)) =
      (∫ t in Ioi 0, |thermalDiff 1 β t| * φ t) * thetaW a β := by
    intro β hβ
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hφ0 t ht), abs_of_pos (thetaW_pos a β)]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    have hm : Measurable fun t => thermalDiff 1 β t * φ t * thetaW a β := by
      unfold thermalDiff; fun_prop
    refine ((hB β hβ).1.mul_const (thetaW a β)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hφ0 t ht), abs_of_pos (thetaW_pos a β)]
  · have hmeas : AEStronglyMeasurable
        (fun β => ∫ t, ‖thermalDiff 1 β t * φ t * thetaW a β‖ ∂(volume.restrict (Ioi 0)))
        (volume.restrict (Ioc 0 β₀)) := by
      have h := (hFm.norm.aestronglyMeasurable
        (μ := (volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀)))).prod_swap
      exact h.integral_prod_right'
    refine Integrable.of_bound (C := B) hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    rw [hnorm β hβ, Real.norm_of_nonneg]
    · exact (hB β hβ).2
    · rw [← hnorm β hβ]; exact integral_nonneg fun _ => norm_nonneg _

lemma integrable_prod_one {a β₀ : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ × ℝ => thermalDiff 1 p.2 p.1 * (fun _ => (1:ℝ)) p.1 * thetaW a p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀))) := by
  refine integrable_prod_family (B := (Real.exp (8 * π * a) / (4 * π * a) + Real.exp (8 * π * a)) /
    (2 * π)) _ measurable_const (fun _ _ => zero_le_one) fun β hβ => ?_
  obtain ⟨hi, hv⟩ := integral_abs_thermalDiff_le hβ.1
  refine ⟨by simpa using hi, ?_⟩
  simp only [mul_one]
  have h1 := inv_mul_thetaW_le ha hβ.1
  have h2 := thetaW_le ha.le hβ.1
  calc (∫ t in Ioi 0, |thermalDiff 1 β t|) * thetaW a β
      ≤ (1 / (2 * π * β) + 1 / (2 * π)) * thetaW a β :=
        mul_le_mul_of_nonneg_right hv (thetaW_pos a β).le
    _ = (β⁻¹ * thetaW a β + thetaW a β) / (2 * π) := by field_simp
    _ ≤ _ := by
        gcongr


lemma integrable_prod_V {a β₀ : ℝ} (ha : 2 ≤ a) :
    Integrable (fun p : ℝ × ℝ => thermalDiff 1 p.2 p.1 * virasoroProblem.cardyV a p.1 * thetaW a p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀))) := by
  have hts : virasoroProblem.totalShift ≤ a := by rw [virasoroProblem_totalShift]; exact ha
  have ha0 : 0 < a := by linarith
  refine integrable_prod_family (B := (Real.exp (8 * π * a) / (2 * π * a) +
    Real.exp (2 * π * a * β₀) * Real.exp (8 * π * a)) / (2 * π)) _
    (continuous_cardyV virasoroProblem a).measurable
    (fun t ht => virasoroProblem.cardyV_nonneg hts ht.le) fun β hβ => ?_
  obtain ⟨hi, hv⟩ := integral_abs_thermalDiff_V_le ha hβ.1
  refine ⟨hi, ?_⟩
  have h1 := inv_mul_exp_thetaW_le ha0 hβ.1
  have h2 := thetaW_le ha0.le hβ.1
  have h3 : Real.exp (2 * π * a * β) ≤ Real.exp (2 * π * a * β₀) :=
    Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hβ.2 (by positivity : 0 ≤ 2 * π * a)])
  calc (∫ t in Ioi 0, |thermalDiff 1 β t| * virasoroProblem.cardyV a t) * thetaW a β
      ≤ ((β⁻¹ * Real.exp (2 * π * a / β) + Real.exp (2 * π * a * β)) / (2 * π)) * thetaW a β :=
        mul_le_mul_of_nonneg_right hv (thetaW_pos a β).le
    _ = (β⁻¹ * Real.exp (2 * π * a / β) * thetaW a β + Real.exp (2 * π * a * β) * thetaW a β) /
          (2 * π) := by ring
    _ ≤ _ := by
        exact div_le_div_of_nonneg_right (add_le_add h1
          (mul_le_mul h3 h2 (thetaW_pos a β).le (Real.exp_pos _).le)) (by positivity)

/-- The dual majorant `h = 2 ∫₀^{β₀} Ξ_β ϑ(dβ)` (Virasoro, `w = 1`). -/
noncomputable def hMaj (a β₀ t : ℝ) : ℝ :=
  2 * ∫ β in Ioc 0 β₀, thermalDiff 1 β t * thetaW a β

lemma continuousOn_hMaj {a β₀ : ℝ} (ha : 0 < a) :
    ContinuousOn (hMaj a β₀) (Ici 0) := by
  unfold hMaj
  refine continuousOn_const.mul ?_
  refine continuousOn_of_dominated (bound := fun β => (1 + β⁻¹) * thetaW a β) ?_ ?_ ?_ ?_
  · intro t _
    exact (by have := measurable_thetaW a; unfold thermalDiff; fun_prop :
      Measurable fun β : ℝ => thermalDiff 1 β t * thetaW a β).aestronglyMeasurable
  · intro t ht
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaW_pos a β)]
    refine mul_le_mul_of_nonneg_right ?_ (thetaW_pos a β).le
    refine (abs_thermalDiff_one_le hβ.1 t).trans ?_
    have e1 : Real.exp (-2 * π * β * t) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ β * t := mul_nonneg hβ.1.le (mem_Ici.1 ht)
      nlinarith [Real.pi_pos])
    have e2 : Real.exp (-2 * π * t / β) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ t / β := div_nonneg (mem_Ici.1 ht) hβ.1.le
      have : -2 * π * t / β = -(2 * π) * (t / β) := by ring
      rw [this]; nlinarith [Real.pi_pos])
    have : β⁻¹ * Real.exp (-2 * π * t / β) ≤ β⁻¹ := by
      calc _ ≤ β⁻¹ * 1 := mul_le_mul_of_nonneg_left e2 (inv_pos.2 hβ.1).le
        _ = β⁻¹ := mul_one _
    linarith
  · refine Integrable.of_bound (C := Real.exp (8 * π * a) + Real.exp (8 * π * a) / (4 * π * a)) ?_ ?_
    · exact (by have := measurable_thetaW a; fun_prop :
        Measurable fun β : ℝ => (1 + β⁻¹) * thetaW a β).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun β hβ => ?_
      have h1 := inv_mul_thetaW_le ha hβ.1
      have h2 := thetaW_le ha.le hβ.1
      rw [Real.norm_of_nonneg (mul_nonneg (by have : 0 < β⁻¹ := inv_pos.2 hβ.1; linarith)
        (thetaW_pos a β).le)]
      nlinarith
  · refine Eventually.of_forall fun β => ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    unfold thermalDiff; fun_prop

lemma integrableOn_hMaj {a β₀ : ℝ} (ha : 0 < a) :
    IntegrableOn (hMaj a β₀) (Ioi 0) := by
  unfold hMaj
  have := (integrable_prod_one (a := a) (β₀ := β₀) ha).integral_prod_left
  have h2 := this.const_mul 2
  simp only [mul_one] at h2
  exact h2

lemma measurable_hMaj (a β₀ : ℝ) : Measurable (hMaj a β₀) := by
  unfold hMaj
  have h1 : Measurable (Function.uncurry fun (t β : ℝ) => thermalDiff 1 β t * thetaW a β) := by
    have := measurable_thetaW a
    unfold thermalDiff; fun_prop
  exact (h1.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc 0 β₀))).measurable.const_mul 2

lemma integrableOn_abs_hMaj_V {a β₀ : ℝ} (ha : 2 ≤ a) :
    IntegrableOn (fun t => |hMaj a β₀ t| * virasoroProblem.cardyV a t) (Ioi 0) := by
  have hts : virasoroProblem.totalShift ≤ a := by rw [virasoroProblem_totalShift]; exact ha
  have hP := integrable_prod_V (a := a) (β₀ := β₀) ha
  have hI := (hP.integral_norm_prod_left).const_mul 2
  refine hI.mono' ?_ ?_
  · exact ((continuous_abs.measurable.comp (measurable_hMaj a β₀)).mul (continuous_cardyV virasoroProblem a).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hV := virasoroProblem.cardyV_nonneg hts (le_of_lt ht)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hV)]
    unfold hMaj
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc |∫ β in Ioc 0 β₀, thermalDiff 1 β t * thetaW a β| * virasoroProblem.cardyV a t
        ≤ (∫ β in Ioc 0 β₀, ‖thermalDiff 1 β t * thetaW a β‖) * virasoroProblem.cardyV a t := by
          apply mul_le_mul_of_nonneg_right _ hV
          have := norm_integral_le_integral_norm (μ := volume.restrict (Ioc 0 β₀))
            (fun β => thermalDiff 1 β t * thetaW a β)
          rwa [Real.norm_eq_abs] at this
      _ = ∫ β in Ioc 0 β₀, ‖thermalDiff 1 β t * virasoroProblem.cardyV a t * thetaW a β‖ := by
          rw [← integral_mul_const]
          refine integral_congr_ae (Eventually.of_forall fun β => ?_)
          simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaW_pos a β), abs_of_nonneg hV]
          ring


open scoped FourierTransform RealInnerProductSpace in
lemma fourier_integral_family {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {ν : Measure ℝ} [SFinite ν] {F : ℝ → V → ℂ}
    (hint : Integrable (fun p : V × ℝ => F p.2 p.1) (volume.prod ν)) (ξ : V) :
    𝓕 (fun x => ∫ β, F β x ∂ν) ξ = ∫ β, 𝓕 (F β) ξ ∂ν := by
  simp only [Real.fourier_eq]
  have hG : Integrable (fun p : V × ℝ => 𝐞 (-⟪p.1, ξ⟫) • F p.2 p.1) (volume.prod ν) := by
    refine hint.norm.mono' ?_ ?_
    · have hc : Continuous fun p : V × ℝ => (𝐞 (-⟪p.1, ξ⟫) : ℂ) :=
        (Continuous.subtype_val (Real.continuous_fourierChar.comp
          (continuous_neg.comp (continuous_inner.comp (continuous_fst.prodMk continuous_const)))))
      exact hc.aestronglyMeasurable.smul hint.aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      simp
  have h1 : ∀ v : V, 𝐞 (-⟪v, ξ⟫) • ∫ β, F β v ∂ν = ∫ β, 𝐞 (-⟪v, ξ⟫) • F β v ∂ν := fun v => by
    simp only [Circle.smul_def]
    exact (integral_const_mul _ _).symm
  simp_rw [h1]
  exact integral_integral_swap (f := fun v β => 𝐞 (-⟪v, ξ⟫) • F β v) hG


open scoped FourierTransform RealInnerProductSpace in
lemma fourier_const_smul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (c : ℂ) (f : V → ℂ) :
    𝓕 (fun x => c • f x) = c • 𝓕 f := by
  ext w
  simp only [Real.fourier_eq, Pi.smul_apply]
  simp_rw [smul_comm _ c]
  exact integral_smul c _

open scoped FourierTransform in
lemma fourier_odd_hMaj {a β₀ : ℝ} (ha : 2 ≤ a) :
    𝓕 (radialLift virasoroProblem.w (hMaj a β₀)) = -(radialLift virasoroProblem.w (hMaj a β₀)) := by
  have hts : virasoroProblem.totalShift ≤ a := by rw [virasoroProblem_totalShift]; exact ha
  have ha0 : 0 < a := by linarith
  set w := virasoroProblem.w with hw
  let F : ℝ → EuclideanSpace ℝ (Fin (2 * w)) → ℂ := fun β x =>
    ((2 * thetaW a β : ℝ) : ℂ) • radialLift w (thermalDiff w β) x
  have hrep : ∀ x, radialLift w (hMaj a β₀) x = ∫ β in Ioc 0 β₀, F β x := by
    intro x
    simp only [F, radialLift, hMaj, smul_eq_mul]
    have : ∀ β : ℝ, ((2 * thetaW a β : ℝ) : ℂ) * ((thermalDiff w β (‖x‖ ^ 2 / 2) : ℝ) : ℂ) =
        ((2 * (thermalDiff 1 β (‖x‖ ^ 2 / 2) * thetaW a β) : ℝ) : ℂ) := by
      intro β
      have e : thermalDiff w β (‖x‖ ^ 2 / 2) = thermalDiff 1 β (‖x‖ ^ 2 / 2) := rfl
      rw [e]; push_cast; ring
    simp_rw [this]
    rw [integral_complex_ofReal, integral_const_mul]
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin (2 * w)) × ℝ => F p.2 p.1)
      (volume.prod (volume.restrict (Ioc 0 β₀))) := by
    have hFm : Measurable (fun p : EuclideanSpace ℝ (Fin (2 * w)) × ℝ => F p.2 p.1) := by
      have := measurable_thetaW a
      simp only [F, radialLift, thermalDiff]
      fun_prop
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    have hnorm : ∀ β ∈ Ioc 0 β₀, ∫ x, ‖F β x‖ =
        2 * thetaW a β * ((2 * π) * ∫ t in Ioi 0, |thermalDiff 1 β t|) := by
      intro β hβ
      have : ∀ x : EuclideanSpace ℝ (Fin (2 * w)), ‖F β x‖ =
          2 * thetaW a β * |thermalDiff 1 β (‖x‖ ^ 2 / 2)| := by
        intro x
        simp only [F, radialLift, norm_smul, Complex.norm_real, Real.norm_eq_abs, hw]
        rw [abs_of_pos (by have := thetaW_pos a β; positivity)]
        simp
      simp_rw [this]
      rw [integral_const_mul]
      congr 1
      have := integral_radialLiftReal (w := w) virasoroProblem.hw (fun t => |thermalDiff 1 β t|)
      rw [this]
      simp [hw]
    refine ⟨?_, ?_⟩
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun β hβ => ?_
      show Integrable (fun x => ((2 * thetaW a β : ℝ) : ℂ) • radialLift w (thermalDiff w β) x) volume
      have := ((thermalDiff_mem_TestClass virasoroProblem hts hβ.1).int_lift).smul ((2 * thetaW a β : ℝ) : ℂ)
      exact this
    · have hmeas : AEStronglyMeasurable
          (fun β => ∫ x, ‖F β x‖) (volume.restrict (Ioc 0 β₀)) := by
        have h := (hFm.norm.aestronglyMeasurable
          (μ := volume.prod (volume.restrict (Ioc 0 β₀)))).prod_swap
        exact h.integral_prod_right'
      refine Integrable.of_bound (C := 2 * (Real.exp (8 * π * a) / (4 * π * a) + Real.exp (8 * π * a)))
        hmeas ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun β hβ => ?_
      rw [hnorm β hβ]
      obtain ⟨_, hv⟩ := integral_abs_thermalDiff_le hβ.1
      have h1 := inv_mul_thetaW_le ha0 hβ.1
      have h2 := thetaW_le ha0.le hβ.1
      have hθ := thetaW_pos a β
      have hI : 0 ≤ ∫ t in Ioi 0, |thermalDiff 1 β t| := integral_nonneg fun _ => abs_nonneg _
      rw [Real.norm_of_nonneg (by positivity)]
      calc 2 * thetaW a β * ((2 * π) * ∫ t in Ioi 0, |thermalDiff 1 β t|)
          ≤ 2 * thetaW a β * ((2 * π) * (1 / (2 * π * β) + 1 / (2 * π))) := by
            gcongr
        _ = 2 * (β⁻¹ * thetaW a β + thetaW a β) := by field_simp
        _ ≤ _ := by linarith
  ext ξ
  have h1 := fourier_integral_family hint ξ
  have hrep' : (fun x => ∫ β in Ioc 0 β₀, F β x) = radialLift w (hMaj a β₀) :=
    (funext hrep).symm
  rw [hrep'] at h1
  rw [h1]
  have h2 : ∀ᵐ β ∂(volume.restrict (Ioc 0 β₀)), 𝓕 (F β) ξ = -(F β ξ) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    have := (thermalDiff_mem_TestClass virasoroProblem hts hβ.1).fourier_odd
    simp only [F]
    rw [fourier_const_smul]
    change (((2 * thetaW a β : ℝ) : ℂ) • 𝓕 (radialLift w (thermalDiff w β))) ξ = _
    rw [this]; simp only [Pi.smul_apply, Pi.neg_apply, smul_neg]
    rfl
  rw [integral_congr_ae h2, integral_neg, ← hrep ξ]
  rfl


theorem hMaj_mem_TestClass {a β₀ : ℝ} (ha : 2 ≤ a) :
    TestClass virasoroProblem a (hMaj a β₀) where
  cont := continuousOn_hMaj (by linarith)
  int_lift := by
    rw [integrable_radialLift_iff virasoroProblem.hw]
    simpa using integrableOn_hMaj (β₀ := β₀) (by linarith : 0 < a)
  fourier_odd := fourier_odd_hMaj ha
  int_cardy := integrableOn_abs_hMaj_V ha

/-- `g_vac(h) = 2 ∫ g_vac(Ξ_β) ϑ(dβ)` (Fubini). -/
lemma gVac_hMaj {a β₀ : ℝ} (ha : 2 ≤ a) :
    virasoroProblem.gVac a (hMaj a β₀) =
      2 * ∫ β in Ioc 0 β₀, virasoroProblem.gVac a (thermalDiff 1 β) * thetaW a β := by
  have hP := integrable_prod_V (a := a) (β₀ := β₀) ha
  have hswap := integral_integral_swap (μ := volume.restrict (Ioi 0)) (ν := volume.restrict (Ioc 0 β₀))
    (f := fun t β => thermalDiff 1 β t * virasoroProblem.cardyV a t * thetaW a β) hP
  unfold FixedWeightProblem.gVac hMaj
  have e1 : ∀ t : ℝ, 2 * (∫ β in Ioc 0 β₀, thermalDiff 1 β t * thetaW a β) *
      virasoroProblem.cardyV a t =
      2 * ∫ β in Ioc 0 β₀, thermalDiff 1 β t * virasoroProblem.cardyV a t * thetaW a β := by
    intro t
    rw [mul_assoc, ← integral_mul_const]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun β => ?_)
    ring
  have e2 : ∀ β : ℝ, ∫ t in Ioi 0, thermalDiff 1 β t * virasoroProblem.cardyV a t * thetaW a β =
      (∫ t in Ioi 0, thermalDiff 1 β t * virasoroProblem.cardyV a t) * thetaW a β := by
    intro β; rw [integral_mul_const]
  simp_rw [e1]
  rw [integral_const_mul]
  rw [hswap]
  simp_rw [e2]
  rw [← integral_const_mul]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun β => ?_)
  ring


/-- Auxiliary: `F(x) = e^{2πax}(1 - e^{-2πx})²`. -/
noncomputable def Fx (a x : ℝ) : ℝ := Real.exp (2 * π * a * x) * (1 - Real.exp (-2 * π * x)) ^ 2

lemma Fx_eq (a x : ℝ) :
    Fx a x = Real.exp (2 * π * (a - 2) * x) * (Real.exp (2 * π * x) - 1) ^ 2 := by
  unfold Fx
  have hq : Real.exp (2 * π * x) * Real.exp (-2 * π * x) = 1 := by
    rw [← Real.exp_add]; simp
  have hE : Real.exp (2 * π * a * x) =
      Real.exp (2 * π * (a - 2) * x) * Real.exp (2 * π * x) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h2 : (Real.exp (2 * π * x) * (1 - Real.exp (-2 * π * x))) = Real.exp (2 * π * x) - 1 := by
    rw [mul_sub, hq, mul_one]
  rw [hE, ← h2]; ring

lemma Fx_mono {a : ℝ} (ha : 2 ≤ a) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : Fx a x ≤ Fx a y := by
  rw [Fx_eq, Fx_eq]
  have h1 : Real.exp (2 * π * (a - 2) * x) ≤ Real.exp (2 * π * (a - 2) * y) :=
    Real.exp_le_exp.2 (by
      have : 0 ≤ 2 * π * (a - 2) := by have := Real.pi_pos; nlinarith
      nlinarith)
  have h2 : 0 ≤ Real.exp (2 * π * x) - 1 := by
    have : 1 ≤ Real.exp (2 * π * x) := Real.one_le_exp (by positivity)
    linarith
  have h3 : Real.exp (2 * π * x) - 1 ≤ Real.exp (2 * π * y) - 1 := by
    have := Real.exp_le_exp.2 (by nlinarith [Real.pi_pos] : 2 * π * x ≤ 2 * π * y)
    linarith
  exact mul_le_mul h1 (pow_le_pow_left₀ h2 h3 2) (sq_nonneg _) (Real.exp_pos _).le

lemma dterm_pos {a : ℝ} (ha : 2 ≤ a) {β : ℝ} (hβ : 0 < β) (hβ2 : β ≤ 1 / 2) :
    0 < β⁻¹ * Real.exp (2 * π * a / β) * (1 - Real.exp (-2 * π / β)) ^ 2 -
      Real.exp (2 * π * a * β) * (1 - Real.exp (-2 * π * β)) ^ 2 := by
  have hβi : 2 ≤ β⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hβ]; linarith
  have hle : β ≤ β⁻¹ := by linarith
  have hF : Fx a β ≤ Fx a β⁻¹ := Fx_mono ha hβ.le hle
  have hFpos : 0 < Fx a β⁻¹ := by
    unfold Fx
    refine mul_pos (Real.exp_pos _) (pow_pos (sub_pos.2 ?_) 2)
    have : 0 < 2 * π * β⁻¹ := by positivity
    have h := Real.exp_lt_exp.2 (show -2 * π * β⁻¹ < 0 by linarith)
    simpa using h
  have e1 : β⁻¹ * Real.exp (2 * π * a / β) * (1 - Real.exp (-2 * π / β)) ^ 2 = β⁻¹ * Fx a β⁻¹ := by
    unfold Fx
    have a1 : 2 * π * a / β = 2 * π * a * β⁻¹ := by rw [div_eq_mul_inv]
    have a2 : -2 * π / β = -2 * π * β⁻¹ := by rw [div_eq_mul_inv]
    rw [a1, a2]; ring
  have e2 : Real.exp (2 * π * a * β) * (1 - Real.exp (-2 * π * β)) ^ 2 = Fx a β := rfl
  rw [e1, e2]
  nlinarith

/-- `C₀ := -h_vac` (explicit formula of `dual_spectrum.tex`). -/
noncomputable def dualC0 (a β₀ : ℝ) : ℝ :=
  2 * ∫ β in Ioc 0 β₀, (β⁻¹ * Real.exp (2 * π * a / β) * (1 - Real.exp (-2 * π / β)) ^ 2 -
      Real.exp (2 * π * a * β) * (1 - Real.exp (-2 * π * β)) ^ 2) * thetaW a β

lemma gVac_thermalDiff_one {a : ℝ} (_ha : 2 ≤ a) {β : ℝ} (hβ : 0 < β) :
    virasoroProblem.gVac a (thermalDiff 1 β) =
      Real.exp (2 * π * a * β) * (1 - Real.exp (-2 * π * β)) ^ 2 -
        β⁻¹ * Real.exp (2 * π * a / β) * (1 - Real.exp (-2 * π / β)) ^ 2 := by
  have := virasoroProblem.gVac_thermalDiff a hβ
  simp only [virasoroProblem_w, Nat.cast_one, Real.rpow_neg_one, virasoroProblem_nullPoly] at this
  exact this

lemma integrableOn_dterm {a β₀ : ℝ} (ha : 2 ≤ a) :
    IntegrableOn (fun β => (β⁻¹ * Real.exp (2 * π * a / β) * (1 - Real.exp (-2 * π / β)) ^ 2 -
      Real.exp (2 * π * a * β) * (1 - Real.exp (-2 * π * β)) ^ 2) * thetaW a β) (Ioc 0 β₀) := by
  have ha0 : 0 < a := by linarith
  refine Integrable.of_bound (C := Real.exp (8 * π * a) / (2 * π * a) +
    Real.exp (2 * π * a * |β₀|) * Real.exp (8 * π * a)) ?_ ?_
  · have := measurable_thetaW a
    exact (by fun_prop : Measurable fun β : ℝ => (β⁻¹ * Real.exp (2 * π * a / β) *
      (1 - Real.exp (-2 * π / β)) ^ 2 - Real.exp (2 * π * a * β) *
      (1 - Real.exp (-2 * π * β)) ^ 2) * thetaW a β).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    have hβp : 0 < β := hβ.1
    have h1 := inv_mul_exp_thetaW_le ha0 hβ.1
    have h2 := thetaW_le ha0.le hβ.1
    have h3 : Real.exp (2 * π * a * β) ≤ Real.exp (2 * π * a * |β₀|) :=
      Real.exp_le_exp.2 (by
        have : β ≤ |β₀| := hβ.2.trans (le_abs_self _)
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * π * a)])
    have hq : ∀ s : ℝ, 0 ≤ s → (1 - Real.exp (-2 * π * s)) ^ 2 ≤ 1 := fun s hs => by
      have e : Real.exp (-2 * π * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
      have e0 := Real.exp_pos (-2 * π * s)
      nlinarith
    have hq1 := hq (1 / β) (by positivity)
    have hq1' : (1 - Real.exp (-2 * π / β)) ^ 2 ≤ 1 := by
      have : -2 * π / β = -2 * π * (1 / β) := by ring
      rw [this]; exact hq1
    have hq2 := hq β hβ.1.le
    have hθ := thetaW_pos a β
    have hA : 0 ≤ β⁻¹ * Real.exp (2 * π * a / β) * (1 - Real.exp (-2 * π / β)) ^ 2 := by positivity
    have hB : 0 ≤ Real.exp (2 * π * a * β) * (1 - Real.exp (-2 * π * β)) ^ 2 := by positivity
    have hA' : β⁻¹ * Real.exp (2 * π * a / β) * (1 - Real.exp (-2 * π / β)) ^ 2 ≤
        β⁻¹ * Real.exp (2 * π * a / β) := by
      have : 0 ≤ β⁻¹ * Real.exp (2 * π * a / β) := by positivity
      nlinarith
    have hB' : Real.exp (2 * π * a * β) * (1 - Real.exp (-2 * π * β)) ^ 2 ≤
        Real.exp (2 * π * a * β) := by
      have := Real.exp_pos (2 * π * a * β)
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hθ]
    have habs : |β⁻¹ * Real.exp (2 * π * a / β) * (1 - Real.exp (-2 * π / β)) ^ 2 -
        Real.exp (2 * π * a * β) * (1 - Real.exp (-2 * π * β)) ^ 2| ≤
        β⁻¹ * Real.exp (2 * π * a / β) + Real.exp (2 * π * a * β) := by
      rw [abs_le]; constructor <;> nlinarith
    calc _ ≤ (β⁻¹ * Real.exp (2 * π * a / β) + Real.exp (2 * π * a * β)) * thetaW a β :=
          mul_le_mul_of_nonneg_right habs hθ.le
      _ = β⁻¹ * Real.exp (2 * π * a / β) * thetaW a β + Real.exp (2 * π * a * β) * thetaW a β := by
          ring
      _ ≤ _ := add_le_add h1 (mul_le_mul h3 h2 hθ.le (Real.exp_pos _).le)

lemma hMaj_vac {a β₀ : ℝ} (ha : 2 ≤ a) :
    virasoroProblem.gVac a (hMaj a β₀) = -dualC0 a β₀ := by
  rw [gVac_hMaj ha, dualC0, ← mul_neg, ← integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun β hβ => ?_
  rw [gVac_thermalDiff_one ha hβ.1]; ring

lemma dualC0_pos {a β₀ : ℝ} (ha : 2 ≤ a) (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2) :
    0 < dualC0 a β₀ := by
  unfold dualC0
  refine mul_pos two_pos ?_
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun β => (β⁻¹ * Real.exp (2 * π * a / β) *
        (1 - Real.exp (-2 * π / β)) ^ 2 - Real.exp (2 * π * a * β) *
        (1 - Real.exp (-2 * π * β)) ^ 2) * thetaW a β) ∩ Ioc 0 β₀ = Ioc 0 β₀ := by
      ext β
      simp only [mem_inter_iff, Function.mem_support, ne_eq, and_iff_right_iff_imp]
      intro hβ
      exact (mul_pos (dterm_pos ha hβ.1 (hβ.2.trans hβ₀2)) (thetaW_pos a β)).ne'
    rw [this]; simp [hβ₀]
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun β hβ =>
      (mul_pos (dterm_pos ha hβ.1 (hβ.2.trans hβ₀2)) (thetaW_pos a β)).le
  · exact integrableOn_dterm ha


lemma integrableOn_Xi_theta {a β₀ : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun β => thermalDiff 1 β t * thetaW a β) (Ioc 0 β₀) := by
  refine Integrable.of_bound (C := Real.exp (8 * π * a) + Real.exp (8 * π * a) / (4 * π * a)) ?_ ?_
  · exact (by have := measurable_thetaW a; unfold thermalDiff; fun_prop :
      Measurable fun β : ℝ => thermalDiff 1 β t * thetaW a β).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    have hβp : 0 < β := hβ.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaW_pos a β)]
    have h1 := inv_mul_thetaW_le ha hβ.1
    have h2 := thetaW_le ha.le hβ.1
    have e1 : Real.exp (-2 * π * β * t) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ β * t := mul_nonneg hβ.1.le ht
      nlinarith [Real.pi_pos])
    have e2 : Real.exp (-2 * π * t / β) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ t / β := div_nonneg ht hβ.1.le
      have : -2 * π * t / β = -(2 * π) * (t / β) := by ring
      rw [this]; nlinarith [Real.pi_pos])
    have h3 : |thermalDiff 1 β t| ≤ 1 + β⁻¹ := by
      refine (abs_thermalDiff_one_le hβ.1 t).trans ?_
      have : β⁻¹ * Real.exp (-2 * π * t / β) ≤ β⁻¹ := by
        calc _ ≤ β⁻¹ * 1 := mul_le_mul_of_nonneg_left e2 (inv_pos.2 hβ.1).le
          _ = β⁻¹ := mul_one _
      linarith
    calc |thermalDiff 1 β t| * thetaW a β ≤ (1 + β⁻¹) * thetaW a β :=
          mul_le_mul_of_nonneg_right h3 (thetaW_pos a β).le
      _ = thetaW a β + β⁻¹ * thetaW a β := by ring
      _ ≤ _ := add_le_add h2 h1

/-- Lemma M (b): `h ≥ w_*` on `[T₀, ∞)` when `t₀(β₀) ≤ T₀`. -/
lemma wStar_le_hMaj {a β₀ T₀ : ℝ} (ha : 0 < a) (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2)
    (hT₀ : t0 β₀ ≤ T₀) {t : ℝ} (ht : T₀ ≤ t) : wStar a β₀ t ≤ hMaj a β₀ t := by
  have ht0 : 0 ≤ t := by
    have : 0 ≤ t0 β₀ := by
      unfold t0
      have h1 : 0 ≤ Real.log (2 / β₀) := Real.log_nonneg (by rw [le_div_iff₀ hβ₀]; linarith)
      have h2 : 0 < 1 - β₀ ^ 2 := by nlinarith
      positivity
    linarith
  unfold wStar hMaj
  have hint := integrableOn_Xi_theta (β₀ := β₀) ha ht0
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_wStar_integrand ha.le β₀ t) (hint.const_mul 2)
    measurableSet_Ioc fun β hβ => ?_
  have := two_thermalDiff_ge hβ.1 (hβ.2.trans hβ₀2) ((t0_mono hβ.1 hβ.2 hβ₀2).trans (hT₀.trans ht))
  have hθ := thetaW_pos a β
  nlinarith

lemma tendsto_exp_div_wStar {a β₀ c : ℝ} (ha : 0 ≤ a) (hβ₀ : 0 < β₀) (hc : 0 < c) :
    Tendsto (fun t => Real.exp (-2 * π * c * t) / wStar a β₀ t) atTop (𝓝 0) := by
  set β₁ := min (c / 4) (β₀ / 2) with hβ₁
  have hβ₁pos : 0 < β₁ := lt_min (by positivity) (by positivity)
  have h2 : 2 * β₁ ≤ β₀ := by have := min_le_right (c / 4) (β₀ / 2); linarith
  have h2' : 4 * β₁ ≤ c := by have := min_le_left (c / 4) (β₀ / 2); linarith
  set K := β₁ * thetaW a β₁ with hK
  have hKpos : 0 < K := mul_pos hβ₁pos (thetaW_pos a β₁)
  have hg : Tendsto (fun t : ℝ => K⁻¹ * Real.exp (-(π * c) * t)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => Real.exp (-(π * c) * t)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_id.const_mul_atTop_of_neg (by have := Real.pi_pos; nlinarith)
    simpa using this.const_mul K⁻¹
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact div_nonneg (Real.exp_pos _).le (wStar_pos ha hβ₀ ht).le
  · filter_upwards [eventually_ge_atTop 0] with t ht
    have hw := wStar_lower (a := a) (β₀ := β₀) (β₁ := β₁) (t := t) ha hβ₁pos h2 ht
    have hwpos := wStar_pos ha hβ₀ ht
    rw [div_le_iff₀ hwpos]
    have e : Real.exp (-2 * π * c * t) ≤ Real.exp (-(π * c) * t) * Real.exp (-4 * π * β₁ * t) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_pos, mul_nonneg ht Real.pi_pos.le, mul_nonneg ht (Real.pi_pos.le)]
    calc Real.exp (-2 * π * c * t)
        ≤ Real.exp (-(π * c) * t) * Real.exp (-4 * π * β₁ * t) := e
      _ = K⁻¹ * Real.exp (-(π * c) * t) * (K * Real.exp (-4 * π * β₁ * t)) := by
          field_simp
      _ ≤ K⁻¹ * Real.exp (-(π * c) * t) * wStar a β₀ t := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc K * Real.exp (-4 * π * β₁ * t) = β₁ * (Real.exp (-4 * π * β₁ * t) * thetaW a β₁) := by
                rw [hK]; ring
            _ ≤ _ := hw

lemma tendsto_thermalDiff_div_wStar {a β₀ β : ℝ} (ha : 0 ≤ a) (hβ₀ : 0 < β₀) (hβ : 0 < β) :
    Tendsto (fun t => thermalDiff 1 β t / wStar a β₀ t) atTop (𝓝 0) := by
  have h1 := tendsto_exp_div_wStar (a := a) ha hβ₀ hβ
  have h2 := (tendsto_exp_div_wStar (a := a) ha hβ₀ (inv_pos.2 hβ)).const_mul β⁻¹
  have h3 := h1.add h2
  rw [mul_zero, add_zero] at h3
  refine squeeze_zero_norm' ?_ h3
  filter_upwards [eventually_ge_atTop 0] with t ht
  have hwpos := wStar_pos ha hβ₀ ht
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hwpos]
  have := abs_thermalDiff_one_le hβ t
  have e : -2 * π * t / β = -2 * π * β⁻¹ * t := by ring
  rw [e] at this
  calc |thermalDiff 1 β t| / wStar a β₀ t
      ≤ (Real.exp (-2 * π * β * t) + β⁻¹ * Real.exp (-2 * π * β⁻¹ * t)) / wStar a β₀ t :=
        div_le_div_of_nonneg_right this hwpos.le
    _ = _ := by ring


/-- **Lemma M** (`dual_spectrum.tex`, `ds:M`; Virasoro problem, `w = 1`, `a = c̃/12`,
`c̃ = c' = c - 1`, `c ≥ 40`; here any `c̃ ≥ 24`).
Let `β₀ ∈ (0, 1/2]`, `T₀ ≥ t₀(β₀)` (`t₀(β) = β log(2/β)/(2π(1-β²))`), `ϑ(dβ) = e^{-4πa(1/β-2)}dβ`
on `(0, β₀]`, `w_*(t) = ∫ e^{-2πβt} ϑ(dβ)`, `h = 2 ∫ Ξ_β ϑ(dβ)`. Then
* (a) `h ∈ \overline{\mathcal A}` (`TestClass`) and `h_vac = -C₀ < 0` with the explicit `C₀ = dualC0`;
* (b) `h ≥ w_*` on `[T₀, ∞)`;
* (c) for every `β > 0` there is `C_β` with `e^{-2πβt} ≤ C_β w_*(t)` for `t ≥ 0` (a fortiori on
  `[T₀, ∞)`), and `Ξ_β / w_* → 0` as `t → ∞`.

Not covered: the statement `ψ_k / w_* → 0` for the Laguerre functions `ψ_k` in (c). The Lean proof
of Theorem E (`Duality.StrongDuality`) works with the families `Ξ_β` directly and avoids the
Laguerre functions, so `ψ_k` is not needed. -/
theorem lemma_M {cTilde β₀ T₀ : ℝ} (hc : 12 * virasoroProblem.totalShift ≤ cTilde)
    (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2) (hT₀ : t0 β₀ ≤ T₀) :
    TestClass virasoroProblem (cTilde / 12) (hMaj (cTilde / 12) β₀) ∧
      virasoroProblem.gVac (cTilde / 12) (hMaj (cTilde / 12) β₀) = -dualC0 (cTilde / 12) β₀ ∧
      0 < dualC0 (cTilde / 12) β₀ ∧
      (∀ t, T₀ ≤ t → wStar (cTilde / 12) β₀ t ≤ hMaj (cTilde / 12) β₀ t) ∧
      (∀ β : ℝ, 0 < β → ∃ C : ℝ, 0 < C ∧
        ∀ t, 0 ≤ t → Real.exp (-2 * π * β * t) ≤ C * wStar (cTilde / 12) β₀ t) ∧
      (∀ β : ℝ, 0 < β →
        Tendsto (fun t => thermalDiff 1 β t / wStar (cTilde / 12) β₀ t) atTop (𝓝 0)) := by
  have ha : 2 ≤ cTilde / 12 := by
    rw [virasoroProblem_totalShift] at hc; linarith
  have ha0 : 0 < cTilde / 12 := by linarith
  exact ⟨hMaj_mem_TestClass ha, hMaj_vac ha, dualC0_pos ha hβ₀ hβ₀2,
    fun t ht => wStar_le_hMaj ha0 hβ₀ hβ₀2 hT₀ ht,
    fun β hβ => exp_le_const_wStar ha0.le hβ₀ hβ,
    fun β hβ => tendsto_thermalDiff_div_wStar ha0.le hβ₀ hβ⟩


/-- info: 'FormalResearch.ModularBootstrap.Duality.lemma_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.lemma_M

/-- info: 'FormalResearch.ModularBootstrap.Duality.hMaj_mem_TestClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.hMaj_mem_TestClass

/-- info: 'FormalResearch.ModularBootstrap.Duality.hMaj_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.hMaj_vac

/-- info: 'FormalResearch.ModularBootstrap.Duality.dualC0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.dualC0_pos

/-- info: 'FormalResearch.ModularBootstrap.Duality.wStar_le_hMaj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.wStar_le_hMaj

/-- info: 'FormalResearch.ModularBootstrap.Duality.exp_le_const_wStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.exp_le_const_wStar

/-- info: 'FormalResearch.ModularBootstrap.Duality.tendsto_thermalDiff_div_wStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.tendsto_thermalDiff_div_wStar

end FormalResearch.ModularBootstrap.Duality
