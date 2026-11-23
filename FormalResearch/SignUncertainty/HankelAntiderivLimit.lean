module

public import FormalResearch.SignUncertainty.HankelAntiderivCalculus
public import FormalResearch.Special.BesselDecay

/-!
# Convergence of `∫_0^X w^{c/2-1} φ_c(w) dw` as `X → ∞`

For `c > 1/2`: the decay `J_{c}(x) = O(x^{-1/2})` (`besselNorm_decay`) gives
`|φ_{c+1}(w)| ≤ K w^{-(c/2+1/4)}` for `w ≥ 1` (`hankelPhi_tail`); with the integration by parts of
`HankelAntiderivCalculus` this shows that `X ↦ ∫_0^X w^{c/2-1} φ_c(w) dw` is bounded and converges, to
`(1/2) ∫_0^∞ w^{c/2-1} φ_{c+1}(w) dw` (`hankelPrimitive_tendsto`, `hankelPrimitive_bounded`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- The primitive `G_c(X) = ∫_0^X w^{c/2-1} φ_c(w) dw`. -/
noncomputable def hankelPrimitive (c X : ℝ) : ℝ :=
  ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * hankelPhi c w

/-- Tail bound: `|φ_{c+1}(w)| ≤ K w^{-(c/2+1/4)}` for `w ≥ 1`, `c > 1/2`. -/
theorem hankelPhi_tail {c : ℝ} (hc : 1 / 2 < c) :
    ∃ K : ℝ, ∀ w ≥ (1 : ℝ), |hankelPhi (c + 1) w| ≤ K * w ^ (-(c / 2 + 1 / 4)) := by
  obtain ⟨C, hC⟩ := besselNorm_decay (ν := c - 1) (by linarith)
  rw [sub_add_cancel] at hC
  refine ⟨C / (4 * π) ^ (c + 1 / 2), fun w hw => ?_⟩
  have hw0 : 0 < w := by linarith
  have hsq : 1 ≤ √w := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hw
  have hx : 1 ≤ 4 * π * √w := by nlinarith [Real.pi_gt_three]
  have h := hC (4 * π * √w) hx
  rw [show c - 1 + 3 / 2 = c + 1 / 2 by ring, Real.mul_rpow (by positivity) (by positivity),
    show (√w) ^ (c + 1 / 2) = w ^ ((c + 1 / 2) / 2) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hw0.le]; ring_nf] at h
  rw [hankelPhi_succ]
  have hp : 0 < (4 * π) ^ (c + 1 / 2) := by positivity
  have hq : 0 < w ^ ((c + 1 / 2) / 2) := Real.rpow_pos_of_pos hw0 _
  have e : w ^ (-(c / 2 + 1 / 4)) = (w ^ ((c + 1 / 2) / 2))⁻¹ := by
    rw [← Real.rpow_neg hw0.le]; congr 1; ring
  have h' : |besselNorm c (4 * π * √w)| ≤ C / ((4 * π) ^ (c + 1 / 2) * w ^ ((c + 1 / 2) / 2)) := by
    rw [le_div_iff₀ (by positivity)]; exact h
  rw [e]
  refine h'.trans (le_of_eq ?_)
  field_simp

theorem integrableOn_rpow_mul_hankelPhi_succ {c : ℝ} (hc : 1 / 2 < c) :
    IntegrableOn (fun w : ℝ => w ^ (c / 2 - 1) * hankelPhi (c + 1) w) (Ioi 0) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨K, hK⟩ := hankelPhi_tail hc
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegrable_rpow_mul_hankelPhi hc0 (c + 1) 1)
  · have hdom : IntegrableOn (fun w : ℝ => |K| * w ^ (-(5 / 4 : ℝ))) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    refine hdom.mono' ?_ ?_
    · exact (((continuousOn_id.rpow_const fun w hw => Or.inl (by
        have : (1 : ℝ) < w := hw
        simp only [id]; linarith)).mul (hankelPhi_continuous (c + 1)).continuousOn
        ).aestronglyMeasurable measurableSet_Ioi)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun w hw => ?_)
      have hw1 : (1 : ℝ) < w := hw
      have hw0 : 0 < w := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hw0.le _)]
      have h1 := hK w hw1.le
      calc w ^ (c / 2 - 1) * |hankelPhi (c + 1) w|
          ≤ w ^ (c / 2 - 1) * (|K| * w ^ (-(c / 2 + 1 / 4))) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) (Real.rpow_nonneg hw0.le _)
            exact mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hw0.le _)
        _ = |K| * w ^ (-(5 / 4 : ℝ)) := by
            rw [mul_left_comm, ← Real.rpow_add hw0]; congr 2; ring

/-- `X^{c/2} φ_{c+1}(X) → 0`. -/
theorem tendsto_rpow_mul_hankelPhi_succ {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (fun X : ℝ => X ^ (c / 2) * hankelPhi (c + 1) X) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hankelPhi_tail hc
  have hlim : Tendsto (fun X : ℝ => |K| * X ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul |K|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hX0.le _)]
  calc X ^ (c / 2) * |hankelPhi (c + 1) X|
      ≤ X ^ (c / 2) * (|K| * X ^ (-(c / 2 + 1 / 4))) := by
        refine mul_le_mul_of_nonneg_left ((hK X hX).trans ?_) (Real.rpow_nonneg hX0.le _)
        exact mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hX0.le _)
    _ = |K| * X ^ (-(1 / 4 : ℝ)) := by
        rw [mul_left_comm, ← Real.rpow_add hX0]; congr 2; ring

theorem abs_rpow_mul_hankelPhi_succ_le {c : ℝ} (hc : 1 / 2 < c) :
    ∃ B : ℝ, ∀ X ≥ (0 : ℝ), |X ^ (c / 2) * hankelPhi (c + 1) X| ≤ B := by
  obtain ⟨K, hK⟩ := hankelPhi_tail hc
  refine ⟨max 1 |K|, fun X hX => ?_⟩
  rcases le_or_gt X 1 with h1 | h1
  · refine le_trans ?_ (le_max_left _ _)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hX _)]
    have := abs_hankelPhi_le_one (by linarith : 1 / 2 < c + 1) X
    calc X ^ (c / 2) * |hankelPhi (c + 1) X| ≤ 1 * 1 :=
          mul_le_mul (Real.rpow_le_one hX h1 (by linarith)) this (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · refine le_trans ?_ (le_max_right _ _)
    have hX0 : 0 < X := by linarith
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hX _)]
    calc X ^ (c / 2) * |hankelPhi (c + 1) X|
        ≤ X ^ (c / 2) * (|K| * X ^ (-(c / 2 + 1 / 4))) := by
          refine mul_le_mul_of_nonneg_left ((hK X h1.le).trans ?_) (Real.rpow_nonneg hX0.le _)
          exact mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hX0.le _)
      _ = |K| * X ^ (-(1 / 4 : ℝ)) := by
          rw [mul_left_comm, ← Real.rpow_add hX0]; congr 2; ring
      _ ≤ |K| * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos h1.le (by norm_num)) (abs_nonneg _)
      _ = |K| := mul_one _

theorem hankelPrimitive_eq {c : ℝ} (hc : 0 < c) {X : ℝ} (hX : 0 ≤ X) :
    hankelPrimitive c X = (1 / c) * (X ^ (c / 2) * hankelPhi (c + 1) X) +
      (1 / 2) * ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * hankelPhi (c + 1) w :=
  integral_rpow_mul_hankelPhi hc hX

/-- `G_c(X) → (1/2) ∫_0^∞ w^{c/2-1} φ_{c+1}`. -/
theorem hankelPrimitive_tendsto {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (hankelPrimitive c) atTop
      (𝓝 ((1 / 2) * ∫ w in Ioi (0 : ℝ), w ^ (c / 2 - 1) * hankelPhi (c + 1) w)) := by
  have hc0 : 0 < c := by linarith
  have h1 := (tendsto_rpow_mul_hankelPhi_succ hc).const_mul (1 / c)
  have h2 := (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_rpow_mul_hankelPhi_succ hc)
    tendsto_id).const_mul (1 / 2)
  have h3 := h1.add h2
  rw [mul_zero, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  rw [hankelPrimitive_eq hc0 hX]
  simp only [id_eq]
  rw [intervalIntegral.integral_of_le hX]

theorem hankelPrimitive_bounded {c : ℝ} (hc : 1 / 2 < c) :
    ∃ M : ℝ, ∀ X ≥ (0 : ℝ), |hankelPrimitive c X| ≤ M := by
  have hc0 : 0 < c := by linarith
  obtain ⟨B, hB⟩ := abs_rpow_mul_hankelPhi_succ_le hc
  set F : ℝ → ℝ := fun w => w ^ (c / 2 - 1) * hankelPhi (c + 1) w with hF
  have hFi := integrableOn_rpow_mul_hankelPhi_succ hc
  refine ⟨(1 / c) * B + (1 / 2) * ∫ w in Ioi (0 : ℝ), |F w|, fun X hX => ?_⟩
  rw [hankelPrimitive_eq hc0 hX]
  have hI : |∫ w in Ioc (0 : ℝ) X, F w| ≤ ∫ w in Ioi (0 : ℝ), |F w| := by
    refine (abs_integral_le_integral_abs).trans ?_
    exact setIntegral_mono_set hFi.abs (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall Ioc_subset_Ioi_self)
  calc |(1 / c) * (X ^ (c / 2) * hankelPhi (c + 1) X) + (1 / 2) * ∫ w in Ioc (0 : ℝ) X, F w|
      ≤ |(1 / c) * (X ^ (c / 2) * hankelPhi (c + 1) X)| + |(1 / 2) * ∫ w in Ioc (0 : ℝ) X, F w| :=
        abs_add_le _ _
    _ ≤ (1 / c) * B + (1 / 2) * ∫ w in Ioi (0 : ℝ), |F w| := by
        gcongr
        · rw [abs_mul, abs_of_pos (by positivity)]
          exact mul_le_mul_of_nonneg_left (hB X hX) (by positivity)
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left hI (by norm_num)

/-- info: 'FormalResearch.SignUncertainty.hankelPrimitive_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPrimitive_tendsto

/-- info: 'FormalResearch.SignUncertainty.hankelPrimitive_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPrimitive_bounded

end FormalResearch.SignUncertainty
