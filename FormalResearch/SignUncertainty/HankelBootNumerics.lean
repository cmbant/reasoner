module

public import FormalResearch.SignUncertainty.HankelBootData
public import FormalResearch.SignUncertainty.HankelBootCount

/-!
# Numerical side conditions for the Hankel bootstrap instance (M5-S6a)

For `c ≥ 3·10⁶`, `48 ≤ t := (1/100)² c^{2/3}` and a radius `R ∈ [t, t+1]`: `R + 1 ≤ A`, `A ≤ (7/2) R`, `R ≤ c^{2/3}`
(`A = langerRadius c`); the lobe and `r_∞` are bounded by `exp(-κ c)` with `κ = 1/600000`; `B₂ ≤ 1`; and `B₁^{(k)} ≤ 2` under
the smallness hypothesis `(2A + 2R) r_∞ ≤ 1`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real Interval

namespace FormalResearch.SignUncertainty

lemma hankelBoot_radius_facts {c R : ℝ} (hc : 3e6 ≤ c) (h48 : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ))
    (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1) :
    48 ≤ R ∧ R + 1 ≤ langerRadius c ∧ langerRadius c ≤ 7 / 2 * R ∧ R ≤ c ^ (2 / 3 : ℝ) := by
  have hk := hankelLangerKappa_bounds
  have hr : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
  have hp : 0 ≤ c ^ (2 / 3 : ℝ) := by linarith [hankel_rpow23_ge hc]
  have hs : 4.8e5 ≤ c ^ (2 / 3 : ℝ) := by nlinarith
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · rw [hr]; nlinarith [mul_le_mul_of_nonneg_left hk.1 hp]
  · rw [hr]; nlinarith [mul_le_mul_of_nonneg_left hk.2 hp]
  · nlinarith

lemma hankelBoot_lobe_le {c : ℝ} (hc : 1 ≤ c) :
    hankelLobe c ≤ 16 * (c * Real.exp (-(1 / 600000 : ℝ) * c)) := by
  unfold hankelLobe
  have hc0 : 0 ≤ c := by linarith
  have h1 : Real.exp (-5 * (4.9e-5 * c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) ≤ Real.exp (-(1 / 600000 : ℝ) * c) := by
    apply Real.exp_le_exp.mpr
    have h2 : (4.9e-5 * c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = (4.9e-5 : ℝ) ^ (3 / 2 : ℝ) * c := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hc0 _), ← Real.rpow_mul hc0]; norm_num
    rw [h2]
    have h3 : (1 / 600000 : ℝ) ≤ 5 * (4.9e-5 : ℝ) ^ (3 / 2 : ℝ) := by
      have h4 : (4.9e-5 : ℝ) ^ (3 / 2 : ℝ) = 4.9e-5 * Real.sqrt 4.9e-5 := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
          Real.sqrt_eq_rpow]
      rw [h4]
      have h5 : (7e-3 : ℝ) ≤ Real.sqrt 4.9e-5 := Real.le_sqrt_of_sq_le (by norm_num)
      nlinarith
    nlinarith
  have h6 : Real.exp (-(1 / 25) * c) ≤ Real.exp (-(1 / 600000 : ℝ) * c) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h7 : Real.exp (-(1 / 600000 : ℝ) * c) ≤ c * Real.exp (-(1 / 600000 : ℝ) * c) :=
    le_mul_of_one_le_left (Real.exp_pos _).le hc
  nlinarith

lemma hankelTailI0_nonneg' : 0 ≤ hankelTailI0 := by
  unfold hankelTailI0
  exact integral_nonneg fun τ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

lemma hankelBoot_rinf_le {c : ℝ} (hc : 0 < c) :
    70 * hankelRinf c ≤ (140 * hankelTailI0) * c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 600000 : ℝ) * c) := by
  unfold hankelRinf
  have h1 : Real.exp (-(c / 40000)) ≤ Real.exp (-(1 / 600000 : ℝ) * c) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 := hankelTailI0_nonneg'
  have h3 : 0 ≤ c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc.le _
  have : 0 ≤ 140 * hankelTailI0 * c ^ (1 / 3 : ℝ) := by positivity
  calc 70 * (2 * hankelTailI0 * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000)))
      = (140 * hankelTailI0 * c ^ (1 / 3 : ℝ)) * Real.exp (-(c / 40000)) := by ring
    _ ≤ (140 * hankelTailI0 * c ^ (1 / 3 : ℝ)) * Real.exp (-(1 / 600000 : ℝ) * c) :=
        mul_le_mul_of_nonneg_left h1 this

lemma hankelBootB2_le_one {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hM : hankelMass c f = 1) (R : ℝ) : hankelBootB2 c f R ≤ 1 := by
  unfold hankelBootB2
  have h := hankelDm_tv hc hf
  rw [hM] at h
  have hfin := isFiniteMeasure_hankelDmPos hc hf
  have h1 : (hankelDmPos c f (Set.Ici (hankelXi c (-R)))).toReal ≤ (hankelDmPos c f univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  have h2 : 0 ≤ (hankelDmNeg c f univ).toReal := ENNReal.toReal_nonneg
  linarith

lemma hankelBootB1k_le_two {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) (hR0 : 0 < R)
    (hsmall : (2 * langerRadius c + 2 * R) * hankelRinf c ≤ 1) (k : ℕ) :
    hankelBootB1k c f R u_T k ≤ 2 := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hA := langerRadius_pos hc0
  have hu : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hmass := hankel_psi_abs_mass hc5 hfe hε hM
  have hcont := continuousOn_hankelPsiR hc0 hfe
  have hi : ∀ a b : ℝ, -langerRadius c ≤ a → a ≤ b → b ≤ langerRadius c →
      IntervalIntegrable (fun x => |hankelPsiR c f x|) volume a b := fun a b ha hab hb =>
    (continuous_abs.comp_continuousOn (hcont.mono (Icc_subset_Icc ha hb))).intervalIntegrable_of_Icc hab
  have hRu' : -langerRadius c ≤ -R := by linarith
  have hu_A : u_T ≤ langerRadius c := (abs_le.1 hu).2
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-langerRadius c) (-R) le_rfl hRu' (by linarith)) (hi (-R) u_T hRu' hRu hu_A)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-langerRadius c) u_T le_rfl (by linarith) hu_A) (hi u_T (langerRadius c) (by linarith) hu_A le_rfl)
  have hn1 : 0 ≤ ∫ x in (-langerRadius c)..(-R), |hankelPsiR c f x| :=
    intervalIntegral.integral_nonneg hRu' fun x _ => abs_nonneg _
  have hn2 : 0 ≤ ∫ x in u_T..(langerRadius c), |hankelPsiR c f x| :=
    intervalIntegral.integral_nonneg hu_A fun x _ => abs_nonneg _
  have hband : ∫ x in (-R)..u_T, |hankelPsiR c f x| ≤ 1 + 2 * langerRadius c * hankelRinf c := by
    linarith
  have hM1 : hankelBootMoment c f R u_T k ≤ ∫ x in (-R)..u_T, |hankelPsiR c f x| := by
    unfold hankelBootMoment
    refine intervalIntegral.integral_mono_on hRu ?_ (hi (-R) u_T hRu' hRu hu_A) fun x hx => ?_
    · exact (((continuous_const.min ((continuous_const.mul continuous_neg).div_const R)).continuousOn).mul
        (hcont.mono (Icc_subset_Icc hRu' hu_A))).intervalIntegrable_of_Icc hRu
    · have h0 : 0 ≤ min 1 (((k : ℝ) + 1) * (-x) / R) :=
        le_min zero_le_one (div_nonneg (mul_nonneg (by positivity) (by linarith [hx.2])) hR0.le)
      have h1 : min 1 (((k : ℝ) + 1) * (-x) / R) ≤ 1 := min_le_left _ _
      calc min 1 (((k : ℝ) + 1) * (-x) / R) * hankelPsiR c f x
          ≤ |min 1 (((k : ℝ) + 1) * (-x) / R) * hankelPsiR c f x| := le_abs_self _
        _ = min 1 (((k : ℝ) + 1) * (-x) / R) * |hankelPsiR c f x| := by rw [abs_mul, abs_of_nonneg h0]
        _ ≤ 1 * |hankelPsiR c f x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |hankelPsiR c f x| := one_mul _
  unfold hankelBootB1k
  nlinarith

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_radius_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_radius_facts

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_lobe_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_lobe_le

/-- info: 'FormalResearch.SignUncertainty.hankelTailI0_nonneg'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelTailI0_nonneg'

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_rinf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_rinf_le

/-- info: 'FormalResearch.SignUncertainty.hankelBootB2_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootB2_le_one

/-- info: 'FormalResearch.SignUncertainty.hankelBootB1k_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootB1k_le_two

end FormalResearch.SignUncertainty
