module

public import Mathlib
public import FormalResearch.SignUncertainty.ConvSourceDefs

/-!
# Pointwise and `L¹` bounds for the long-range weight `w_h` (M6, Lemma `O.12`, `ceo:conv`)

For `1/2 < p < 1` and `h > 0`, the weight `w_h(y) = η(y) ϱ(h y) y^{-3/2}` of `ConvSourceDefs`
satisfies, with constants depending only on `p`:

* `convW_integrable`, `convW_L1_le`: `w_h` is integrable on `(0, ∞)` and
  `∫ w_h ≤ (2 + 1/(p - 1/2)) √h`;
* `convW_mass`: `|∫ w_h - √h B_p| ≤ C h^p` with `B_p = ∫₀^∞ t^{p-3/2}(1+t)^{-p} dt`.

The proofs use the substitution `t = h y`: `∫ w_h = √h ∫ η(t/h) t^{-3/2} ϱ(t) dt`, and the
majorant `t^{-3/2} ϱ(t) ≤ t^{p-3/2}` on `(0,1]`, `≤ t^{-3/2}` on `(1,∞)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The bracket `t^{-3/2} ϱ(t)`, the integrand of the substituted weight. -/
noncomputable def convWf (p t : ℝ) : ℝ := t ^ (-(3 / 2 : ℝ)) * convRho p t

/-- The piecewise majorant `t^{p-3/2}` on `(0, 1]` and `t^{-3/2}` on `(1, ∞)`. -/
noncomputable def convWm (p t : ℝ) : ℝ :=
  if t ≤ 1 then t ^ (p - 3 / 2) else t ^ (-(3 / 2 : ℝ))

lemma convW_rho_le_pow {p : ℝ} (hp : 0 ≤ p) {t : ℝ} (ht : 0 ≤ t) : convRho p t ≤ t ^ p := by
  unfold convRho
  exact Real.rpow_le_rpow (div_nonneg ht (by linarith)) (div_le_self ht (by linarith)) hp

lemma convWf_nonneg {p t : ℝ} (ht : 0 < t) : 0 ≤ convWf p t :=
  mul_nonneg (Real.rpow_nonneg ht.le _) (convRho_nonneg p ht.le)

lemma convWf_le_small {p : ℝ} (hp : 0 ≤ p) {t : ℝ} (ht : 0 < t) :
    convWf p t ≤ t ^ (p - 3 / 2) := by
  unfold convWf
  have h1 : t ^ (p - 3 / 2) = t ^ (-(3 / 2 : ℝ)) * t ^ p := by
    rw [← Real.rpow_add ht]; congr 1; ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left (convW_rho_le_pow hp ht.le) (Real.rpow_nonneg ht.le _)

lemma convWf_le_large {p : ℝ} (hp : 0 ≤ p) {t : ℝ} (ht : 0 < t) :
    convWf p t ≤ t ^ (-(3 / 2 : ℝ)) := by
  unfold convWf
  have h1 : convRho p t ≤ 1 := convRho_le_one hp ht.le
  have h2 := Real.rpow_nonneg ht.le (-(3 / 2 : ℝ))
  nlinarith

lemma convWf_le_majorant {p : ℝ} (hp : 0 ≤ p) {t : ℝ} (ht : 0 < t) :
    convWf p t ≤ convWm p t := by
  unfold convWm
  split_ifs with h
  · exact convWf_le_small hp ht
  · exact convWf_le_large hp ht

lemma convWm_nonneg {p t : ℝ} (ht : 0 < t) : 0 ≤ convWm p t := by
  unfold convWm
  split_ifs
  · exact Real.rpow_nonneg ht.le _
  · exact Real.rpow_nonneg ht.le _

lemma convWm_integrableOn {p : ℝ} (hp : 1 / 2 < p) : IntegrableOn (convWm p) (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (p - 3 / 2)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have h2 : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have h1' : IntegrableOn (convWm p) (Ioc 0 1) :=
    h1.congr_fun (fun t ht => by simp [convWm, ht.2]) measurableSet_Ioc
  have h2' : IntegrableOn (convWm p) (Ioi 1) :=
    h2.congr_fun (fun t ht => by
      simp [convWm, not_le.mpr (show (1 : ℝ) < t from ht)]) measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h1'.union h2'

lemma convWf_measurable (p : ℝ) : Measurable (convWf p) := by
  unfold convWf convRho
  fun_prop

lemma convWf_integrableOn {p : ℝ} (hp : 1 / 2 < p) : IntegrableOn (convWf p) (Ioi 0) := by
  refine Integrable.mono' (convWm_integrableOn hp) (convWf_measurable p).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  rw [Real.norm_of_nonneg (convWf_nonneg ht')]
  exact convWf_le_majorant (by linarith) ht'

/-- The integral of the majorant over `(0, ∞)`: `2 + 1/(p - 1/2)`. -/
lemma convWm_integral {p : ℝ} (hp : 1 / 2 < p) :
    ∫ t in Ioi (0:ℝ), convWm p t = 2 + 1 / (p - 1 / 2) := by
  have h1 : IntegrableOn (convWm p) (Ioc 0 1) :=
    (convWm_integrableOn hp).mono_set (fun t ht => ht.1)
  have h2 : IntegrableOn (convWm p) (Ioi 1) :=
    (convWm_integrableOn hp).mono_set (fun t ht => show (0 : ℝ) < t from lt_trans zero_lt_one ht)
  have hsplit : ∫ t in Ioi (0:ℝ), convWm p t
      = (∫ t in Ioc (0:ℝ) 1, convWm p t) + ∫ t in Ioi (1:ℝ), convWm p t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2]
  have e1 : ∫ t in Ioc (0:ℝ) 1, convWm p t = ∫ t in Ioc (0:ℝ) 1, t ^ (p - 3 / 2) :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => by simp [convWm, ht.2])
  have e2 : ∫ t in Ioi (1:ℝ), convWm p t = ∫ t in Ioi (1:ℝ), t ^ (-(3 / 2 : ℝ)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      simp [convWm, not_le.mpr (show (1 : ℝ) < t from ht)])
  have i1 : ∫ t in Ioc (0:ℝ) 1, t ^ (p - 3 / 2) = 1 / (p - 1 / 2) := by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith))]
    rw [Real.zero_rpow (show p - 3 / 2 + 1 ≠ 0 by intro h0; linarith), Real.one_rpow,
      show p - 3 / 2 + 1 = p - 1 / 2 by ring]
    ring
  have i2 : ∫ t in Ioi (1:ℝ), t ^ (-(3 / 2 : ℝ)) = 2 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num [Real.one_rpow]
  rw [hsplit, e1, e2, i1, i2]
  ring

/-- Pointwise bound `w_h ≤ majorant` on `(0, ∞)`. -/
lemma convWh_le_majorant {p h : ℝ} (hp : 0 ≤ p) (hh : 0 ≤ h) {y : ℝ} (hy : 0 < y) :
    convWh p h y ≤ convWm p y := by
  unfold convWm
  split_ifs with h1
  · rw [convWh_eq_zero h1]; exact Real.rpow_nonneg hy.le _
  · exact convWh_le hp hh hy

/-- (a, integrability) `w_h` is integrable on `(0, ∞)`, for every `h ≥ 0`. -/
theorem convW_integrable {p h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) :
    IntegrableOn (convWh p h) (Ioi 0) := by
  have hE : Measurable convEta := (convEta_contDiff (n := 0)).continuous.measurable
  have hR : Measurable (fun y : ℝ => convRho p (h * y)) := by
    unfold convRho; fun_prop
  have hm : Measurable (convWh p h) := by
    unfold convWh
    exact (hE.mul hR).div (measurable_id.pow_const _)
  refine Integrable.mono' (convWm_integrableOn hp) hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy' : (0 : ℝ) < y := hy
  rw [Real.norm_of_nonneg (convWh_nonneg hh.le hy')]
  exact convWh_le_majorant (by linarith) hh.le hy'

/-- Substitution `y ↦ h y` on `(0, ∞)`. -/
lemma convW_scale {h : ℝ} (hh : 0 < h) (g : ℝ → ℝ) :
    ∫ y in Ioi 0, g (h * y) = h⁻¹ * ∫ t in Ioi (0:ℝ), g t := by
  have := integral_comp_mul_left_Ioi g 0 hh
  rw [mul_zero] at this
  rw [this, smul_eq_mul]

/-- The pointwise identity `w_h(y) = h^{3/2} · η(hy/h) · ϱ-bracket(hy)`. -/
lemma convWh_eq_scale {p h : ℝ} (hh : 0 < h) {y : ℝ} (hy : 0 < y) :
    convWh p h y = h ^ (3 / 2 : ℝ) * (convEta (h * y / h) * convWf p (h * y)) := by
  have hk : h * y / h = y := by field_simp
  rw [hk]
  have hA : h ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hh _).ne'
  have hB : y ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  have e1 : (h * y) ^ (-(3 / 2 : ℝ)) = (h ^ (3 / 2 : ℝ))⁻¹ * (y ^ (3 / 2 : ℝ))⁻¹ := by
    rw [Real.mul_rpow hh.le hy.le, Real.rpow_neg hh.le, Real.rpow_neg hy.le]
  unfold convWh convWf
  rw [e1]
  field_simp

/-- The integral identity `∫ w_h = √h ∫ η(t/h) ϱ-bracket(t) dt`. -/
lemma convW_integral_eq {p h : ℝ} (hh : 0 < h) :
    ∫ y in Ioi 0, convWh p h y
      = Real.sqrt h * ∫ t in Ioi (0:ℝ), convEta (t / h) * convWf p t := by
  have hsc : ∫ y in Ioi 0, convEta (h * y / h) * convWf p (h * y)
      = h⁻¹ * ∫ t in Ioi (0:ℝ), convEta (t / h) * convWf p t :=
    convW_scale (g := fun t => convEta (t / h) * convWf p t) hh
  have hc : ∫ y in Ioi 0, convWh p h y
      = ∫ y in Ioi 0, h ^ (3 / 2 : ℝ) * (convEta (h * y / h) * convWf p (h * y)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => convWh_eq_scale hh hy)
  have hsq : h ^ (3 / 2 : ℝ) = Real.sqrt h * h := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hh, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [hc, integral_const_mul, hsc, hsq]
  field_simp

/-- (a) `L¹` bound: `∫ w_h ≤ (2 + 1/(p - 1/2)) √h` for every `h > 0`. -/
theorem convW_L1_le {p h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) :
    ∫ y in Ioi 0, convWh p h y ≤ (2 + 1 / (p - 1 / 2)) * Real.sqrt h := by
  rw [convW_integral_eq hh, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc ∫ t in Ioi (0:ℝ), convEta (t / h) * convWf p t ≤ ∫ t in Ioi (0:ℝ), convWm p t := by
        refine integral_mono_of_nonneg ?_ (convWm_integrableOn hp) ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht' : (0 : ℝ) < t := ht
          exact mul_nonneg (convEta_nonneg _) (convWf_nonneg ht')
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht' : (0 : ℝ) < t := ht
          calc convEta (t / h) * convWf p t ≤ 1 * convWf p t :=
                mul_le_mul_of_nonneg_right (convEta_le_one _) (convWf_nonneg ht')
            _ = convWf p t := one_mul _
            _ ≤ convWm p t := convWf_le_majorant (by linarith) ht'
    _ = 2 + 1 / (p - 1 / 2) := convWm_integral hp

/-- The mass constant `B_p = ∫₀^∞ t^{p-3/2} (1+t)^{-p} dt`. -/
noncomputable def convBp (p : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (p - 3 / 2) * (1 + t) ^ (-p)

/-- `B_p` written with the bracket `ϱ`. -/
lemma convBp_eq_integral_convWf {p : ℝ} :
    convBp p = ∫ t in Ioi (0:ℝ), convWf p t := by
  unfold convBp
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht
  unfold convWf convRho
  have hA : t ^ (p - 3 / 2) = t ^ (-(3 / 2 : ℝ)) * t ^ p := by
    rw [← Real.rpow_add ht']; congr 1; ring
  rw [Real.div_rpow ht'.le (by linarith), Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 + t), hA]
  ring

/-- The bound for the difference `(η(t/h) - 1) ϱ-bracket(t)`. -/
lemma convW_diff_le {p h : ℝ} (hp : 1 / 2 < p) (hh : 0 < h) {t : ℝ} (ht : 0 < t) :
    ‖(convEta (t / h) - 1) * convWf p t‖ ≤ Set.indicator (Ioo 0 (2 * h)) (fun s => s ^ (p - 3 / 2)) t := by
  have hf := convWf_nonneg (p := p) ht
  have hfl := convWf_le_small (by linarith : (0 : ℝ) ≤ p) ht
  have hη0 := convEta_nonneg (t / h)
  have hη1 := convEta_le_one (t / h)
  by_cases h2 : t < 2 * h
  · rw [Set.indicator_of_mem (show t ∈ Ioo 0 (2 * h) from ⟨ht, h2⟩)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith : convEta (t / h) - 1 ≤ 0),
      abs_of_nonneg hf]
    nlinarith
  · have hge : 2 ≤ t / h := by
      rw [le_div_iff₀ hh]; linarith [not_lt.mp h2]
    rw [convEta_eq_one hge, sub_self, zero_mul, norm_zero]
    apply Set.indicator_nonneg
    intro s hs
    exact Real.rpow_nonneg hs.1.le _

lemma convEta_measurable : Measurable convEta := (convEta_contDiff (n := 0)).continuous.measurable

/-- (b) the mass: `|∫ w_h - √h B_p| ≤ C h^p` for `0 < h ≤ 1`, with `C = 2^{p-1/2}/(p-1/2)`. -/
theorem convW_mass {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 →
      |(∫ y in Ioi 0, convWh p h y) - Real.sqrt h * convBp p| ≤ C * h ^ p := by
  refine ⟨2 ^ (p - 1 / 2) / (p - 1 / 2), fun h hh _ => ?_⟩
  have hEi : IntegrableOn (fun t : ℝ => convEta (t / h) * convWf p t) (Ioi 0) := by
    refine Integrable.mono' (convWm_integrableOn hp)
      ((convEta_measurable.comp (measurable_id.div_const h)).mul (convWf_measurable p)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_of_nonneg (mul_nonneg (convEta_nonneg _) (convWf_nonneg ht'))]
    calc convEta (t / h) * convWf p t ≤ 1 * convWf p t :=
          mul_le_mul_of_nonneg_right (convEta_le_one _) (convWf_nonneg ht')
      _ = convWf p t := one_mul _
      _ ≤ convWm p t := convWf_le_majorant (by linarith) ht'
  have hfi : IntegrableOn (convWf p) (Ioi 0) := convWf_integrableOn hp
  have hdiff : (∫ y in Ioi 0, convWh p h y) - Real.sqrt h * convBp p
      = Real.sqrt h * ∫ t in Ioi (0 : ℝ), (convEta (t / h) - 1) * convWf p t := by
    have hsub : ∫ t in Ioi (0 : ℝ), (convEta (t / h) - 1) * convWf p t
        = (∫ t in Ioi (0 : ℝ), convEta (t / h) * convWf p t) - ∫ t in Ioi (0 : ℝ), convWf p t := by
      simp only [sub_mul, one_mul]
      exact integral_sub hEi hfi
    rw [convW_integral_eq hh, convBp_eq_integral_convWf, hsub]
    ring
  have hI : IntegrableOn (fun s : ℝ => s ^ (p - 3 / 2)) (Ioo 0 (2 * h)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ 2 * h)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).mono_set Set.Ioo_subset_Ioc_self
  have hgI : Integrable (Set.indicator (Ioo (0 : ℝ) (2 * h)) (fun s : ℝ => s ^ (p - 3 / 2))) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hI
  have hgint : ∫ t in Ioi (0 : ℝ), Set.indicator (Ioo (0 : ℝ) (2 * h)) (fun s : ℝ => s ^ (p - 3 / 2)) t
      = (2 * h) ^ (p - 1 / 2) / (p - 1 / 2) := by
    rw [setIntegral_indicator measurableSet_Ioo, Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 2 * h),
      integral_rpow (Or.inl (by linarith))]
    rw [Real.zero_rpow (show p - 3 / 2 + 1 ≠ 0 by intro h0; linarith),
      show p - 3 / 2 + 1 = p - 1 / 2 by ring]
    ring
  have hbound : ‖∫ t in Ioi (0 : ℝ), (convEta (t / h) - 1) * convWf p t‖
      ≤ ∫ t in Ioi (0 : ℝ), Set.indicator (Ioo (0 : ℝ) (2 * h)) (fun s : ℝ => s ^ (p - 3 / 2)) t :=
    norm_integral_le_of_norm_le hgI.integrableOn (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact convW_diff_le hp hh (show (0 : ℝ) < t from ht))
  rw [hgint, Real.norm_eq_abs] at hbound
  rw [hdiff, abs_mul, abs_of_nonneg (Real.sqrt_nonneg h)]
  have e : (2 * h) ^ (p - 1 / 2) = 2 ^ (p - 1 / 2) * h ^ (p - 1 / 2) :=
    Real.mul_rpow (by norm_num) hh.le
  have e2 : Real.sqrt h * h ^ (p - 1 / 2) = h ^ p := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hh]; congr 1; ring
  refine (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg h)).trans (le_of_eq ?_)
  rw [e, ← e2]
  ring


/-- info: 'FormalResearch.SignUncertainty.convW_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convW_integrable

/-- info: 'FormalResearch.SignUncertainty.convW_L1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convW_L1_le

/-- info: 'FormalResearch.SignUncertainty.convW_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convW_mass

end FormalResearch.SignUncertainty
