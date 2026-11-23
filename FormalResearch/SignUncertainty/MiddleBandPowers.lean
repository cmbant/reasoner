module

public import Mathlib
public import FormalResearch.CohnElkies.HighBandEstimate

/-!
# Elementary power integrals and the `ε`-power algebra of the middle-band region estimates (GT.2a G3)

Elementary facts used by the region estimates of the middle band (`cegt:GT2a`), with `ε = liftEps c`
(so `ε = c^{-1/3}` and `c ε³ = 1`):

* `mb_tail_pow`: `∫_R^∞ u^{-s} du = R^{1-s}/(s-1)` for `s > 1`. Restates Mathlib's `integral_Ioi_rpow_of_lt`
  in the form used below.
* `mb_two_sided_tail`: a function bounded by `|u|^{-s}` and vanishing on `|u| < R` has `|∫ f| ≤ 2R^{1-s}/(s-1)`.
  Proved from `mb_tail_pow` and the reflection `integral_comp_neg_Ioi`; the hypothesis `hint : Integrable f` is part
  of the statement as briefed (named `_hint`), and the proof does not use it.
* `mb_outer_exponent`, `mb_liftEps_pow_15_div_2`: exponent identities for `ε = c^{-1/3}` (both exact, proved).
* `mb_region_c`: `ε² S^{-11/4} ≤ (π² ε² S) S^{-3/2}` for `S ≥ 100`. The brief's side condition `ε² ≤ L` is not
  needed as a hypothesis: it follows from `L = π² ε² S` and `S ≥ 1`, and the proof uses only `S ≥ 100`.
* `mb_u0_inv_sqrt`: `u₀^{-1/2} ≤ S^{-1/4}` for `u₀ = 2√(3κS)`, `κ ≥ 1`.
* `mb_tail_seven_halves`: `∫_α^b u^{-7/2} du ≤ (2/5) α^{-5/2}` for `0 < α ≤ b` (exact tail value
  `(2/5) α^{-5/2}` over `(α, ∞)`; the interval integral is bounded by it since the integrand is nonnegative).
* `mb_tail_S_five_quarters`: with `α = 3u₀/8`, `u₀ = 2√(3κS)`, `κ ≥ 1`: `∫_α^{2u₀} u^{-7/2} du ≤ S^{-5/4}`
  (constant `C = 1`).

All statements are proved (exact real-exponent algebra and Mathlib integrals); none is numerical evidence.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- Tail of a power integral: `∫_R^∞ u^{-s} du = R^{1-s}/(s-1)` for `s > 1`, `R > 0`
(restates Mathlib's `integral_Ioi_rpow_of_lt`). -/
theorem mb_tail_pow {R s : ℝ} (hR : 0 < R) (hs : 1 < s) :
    ∫ u in Set.Ioi R, u ^ (-s) = R ^ (1 - s) / (s - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) hR]
  rw [show (1 : ℝ) - s = -s + 1 by ring, show s - 1 = -(-s + 1) by ring, div_neg, neg_div]

/-- Two-sided tail bound (`cegt:GT2a` region estimates): if `|f u| ≤ |u|^{-s}`, `f = 0` on `|u| < R`, then
`|∫ f| ≤ 2 R^{1-s}/(s-1)`. The integrability hypothesis `hint` is kept as briefed; the proof does not use it. -/
theorem mb_two_sided_tail {R s : ℝ} (hR : 0 < R) (hs : 1 < s) (f : ℝ → ℝ) (hf : ∀ u, |f u| ≤ |u| ^ (-s))
    (hsupp : ∀ u, |u| < R → f u = 0) (_hint : Integrable f) :
    |∫ u, f u| ≤ 2 * R ^ (1 - s) / (s - 1) := by
  have hi1 : IntegrableOn (fun t : ℝ => t ^ (-s)) (Ici R) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hR
  have hi2 : IntegrableOn (fun t : ℝ => (-t) ^ (-s)) (Iic (-R)) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding (f := fun t : ℝ => t ^ (-s)) (s := Ici R)
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ici R = Iic (-R) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
      constructor <;> intro h' <;> linarith
    rw [hpre] at h
    exact h.mpr hi1
  set G : ℝ → ℝ := fun u => (Ici R).indicator (fun t : ℝ => t ^ (-s)) u
    + (Iic (-R)).indicator (fun t : ℝ => (-t) ^ (-s)) u with hG
  have hGint : Integrable G :=
    (hi1.integrable_indicator measurableSet_Ici).add (hi2.integrable_indicator measurableSet_Iic)
  have hGnn : ∀ u, 0 ≤ G u := by
    intro u
    refine add_nonneg (Set.indicator_nonneg (fun t ht => Real.rpow_nonneg ?_ _) _)
      (Set.indicator_nonneg (fun t ht => Real.rpow_nonneg ?_ _) _)
    · exact le_trans hR.le (Set.mem_Ici.mp ht)
    · have := Set.mem_Iic.mp ht; linarith
  have hpt : ∀ u, ‖f u‖ ≤ G u := by
    intro u
    rw [Real.norm_eq_abs]
    rcases lt_or_ge |u| R with h | h
    · rw [hsupp u h, abs_zero]; exact hGnn u
    · rcases le_total 0 u with hu | hu
      · have hRu : R ≤ u := by rwa [abs_of_nonneg hu] at h
        have hval : (Ici R).indicator (fun t : ℝ => t ^ (-s)) u = u ^ (-s) :=
          Set.indicator_of_mem (Set.mem_Ici.mpr hRu) _
        have hnn : 0 ≤ (Iic (-R)).indicator (fun t : ℝ => (-t) ^ (-s)) u :=
          Set.indicator_nonneg (fun t ht => Real.rpow_nonneg (by have := Set.mem_Iic.mp ht; linarith) _) _
        have h1 := hf u
        rw [abs_of_nonneg hu] at h1
        simp only [hG]
        rw [hval]
        linarith
      · have hRu : u ≤ -R := by rw [abs_of_nonpos hu] at h; linarith
        have hval : (Iic (-R)).indicator (fun t : ℝ => (-t) ^ (-s)) u = (-u) ^ (-s) :=
          Set.indicator_of_mem (Set.mem_Iic.mpr hRu) _
        have hnn : 0 ≤ (Ici R).indicator (fun t : ℝ => t ^ (-s)) u :=
          Set.indicator_nonneg (fun t ht => Real.rpow_nonneg (le_trans hR.le (Set.mem_Ici.mp ht)) _) _
        have h1 := hf u
        rw [abs_of_nonpos hu] at h1
        simp only [hG]
        rw [hval]
        linarith
  have hGI : ∫ u, G u = 2 * R ^ (1 - s) / (s - 1) := by
    simp only [hG]
    rw [integral_add (hi1.integrable_indicator measurableSet_Ici) (hi2.integrable_indicator measurableSet_Iic),
      integral_indicator measurableSet_Ici, integral_indicator measurableSet_Iic,
      integral_Ici_eq_integral_Ioi]
    have key := integral_comp_neg_Ioi R (fun t : ℝ => (-t) ^ (-s))
    simp only [neg_neg] at key
    rw [← key, mb_tail_pow hR hs]
    ring
  calc |∫ u, f u| = ‖∫ u, f u‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ u, ‖f u‖ := norm_integral_le_integral_norm f
    _ ≤ ∫ u, G u := integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) hGint
        (Eventually.of_forall hpt)
    _ = 2 * R ^ (1 - s) / (s - 1) := hGI

/-- The outer exponent of the region estimates: `c^{1/3} · ε^{5/2} · c^{-2} = c^{-5/2}` with `ε = c^{-1/3}`.
Exact exponent algebra. (Negative regression: the answer is `c^{-5/2}`, not `c^{-5/3}`.) -/
theorem mb_outer_exponent {c : ℝ} (hc : 0 < c) :
    c ^ (1 / 3 : ℝ) * liftEps c ^ (5 / 2 : ℝ) * c ^ (-(2 : ℝ)) = c ^ (-(5 / 2 : ℝ)) := by
  unfold liftEps
  rw [← Real.rpow_mul hc.le, ← Real.rpow_add hc, ← Real.rpow_add hc]
  congr 1
  norm_num

/-- `ε^{15/2} = c^{-5/2}` for `ε = liftEps c = c^{-1/3}`. Exact exponent algebra. -/
theorem mb_liftEps_pow_15_div_2 {c : ℝ} (hc : 0 < c) :
    liftEps c ^ (15 / 2 : ℝ) = c ^ (-(5 / 2 : ℝ)) := by
  unfold liftEps
  rw [← Real.rpow_mul hc.le]
  congr 1
  norm_num

/-- `ε² S^{-11/4} ≤ L S^{-3/2}` for `L = π² ε² S` and `S ≥ 100`. Proved: `S^{-11/4} = S^{-1/2} S^{-9/4}`
with `S^{-9/4} ≤ 1 ≤ π²`. -/
theorem mb_region_c {ε S L : ℝ} (hS : 100 ≤ S) (hL : L = Real.pi ^ 2 * ε ^ 2 * S) :
    ε ^ 2 * S ^ (-(11 / 4 : ℝ)) ≤ L * S ^ (-(3 / 2 : ℝ)) := by
  have hS0 : 0 < S := by linarith
  have h1 : S ^ (-(11 / 4 : ℝ)) = S ^ (-(1 / 2 : ℝ)) * S ^ (-(9 / 4 : ℝ)) := by
    rw [← Real.rpow_add hS0]; norm_num
  have h2 : S ^ (-(9 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have h3 : S * S ^ (-(3 / 2 : ℝ)) = S ^ (-(1 / 2 : ℝ)) := by
    calc S * S ^ (-(3 / 2 : ℝ)) = S ^ (1 : ℝ) * S ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = S ^ ((1 : ℝ) + -(3 / 2 : ℝ)) := (Real.rpow_add hS0 _ _).symm
      _ = S ^ (-(1 / 2 : ℝ)) := by norm_num
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hpos : 0 ≤ ε ^ 2 * S ^ (-(1 / 2 : ℝ)) := by positivity
  have hR : L * S ^ (-(3 / 2 : ℝ)) = Real.pi ^ 2 * (ε ^ 2 * S ^ (-(1 / 2 : ℝ))) := by
    rw [hL, ← h3]; ring
  rw [h1, hR]
  have hB : ε ^ 2 * (S ^ (-(1 / 2 : ℝ)) * S ^ (-(9 / 4 : ℝ))) ≤ ε ^ 2 * S ^ (-(1 / 2 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left h2 hpos
    nlinarith
  have hC : ε ^ 2 * S ^ (-(1 / 2 : ℝ)) ≤ Real.pi ^ 2 * (ε ^ 2 * S ^ (-(1 / 2 : ℝ))) := by
    nlinarith
  linarith

/-- Upper bound for the cubic-phase amplitude exponent: for `u₀ = 2√(3κS)` with `κ ≥ 1`,
`u₀^{-1/2} ≤ S^{-1/4}`. Proved from `S^{1/2} ≤ u₀` and the antitonicity of `x ↦ x^{-1/2}`. -/
theorem mb_u0_inv_sqrt {κ S : ℝ} (hκ : 1 ≤ κ) (hS : 0 < S) :
    (2 * Real.sqrt (3 * κ * S)) ^ (-(1 / 2 : ℝ)) ≤ S ^ (-(1 / 4 : ℝ)) := by
  have hsq : Real.sqrt S ≤ Real.sqrt (3 * κ * S) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hrw : S ^ (-(1 / 4 : ℝ)) = (S ^ (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_mul hS.le]; norm_num
  rw [hrw, ← Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_nonpos hsqrt_pos (by linarith) (by norm_num)

/-- The tail integral of `u^{-7/2}` from `α` (`0 < α ≤ b`) is at most `(2/5) α^{-5/2}`, the exact value of
the integral over `(α, ∞)`. -/
theorem mb_tail_seven_halves {α b : ℝ} (hα : 0 < α) (hb : α ≤ b) :
    ∫ u in α..b, u ^ (-(7 / 2 : ℝ)) ≤ (2 / 5) * α ^ (-(5 / 2 : ℝ)) := by
  rw [intervalIntegral.integral_of_le hb]
  have hIoi : ∫ u in Set.Ioi α, u ^ (-(7 / 2 : ℝ)) = (2 / 5) * α ^ (-(5 / 2 : ℝ)) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hα]
    rw [show -(7 / 2 : ℝ) + 1 = -(5 / 2) by norm_num]
    ring
  rw [← hIoi]
  refine setIntegral_mono_set (integrableOn_Ioi_rpow_of_lt (by norm_num) hα) ?_
    (Eventually.of_forall fun u hu => hu.1)
  exact (ae_restrict_mem measurableSet_Ioi).mono fun u hu =>
    Real.rpow_nonneg (le_trans hα.le (le_of_lt (Set.mem_Ioi.mp hu))) _

/-- With `u₀ = 2√(3κS)`, `κ ≥ 1`, `α = 3u₀/8`: `∫_α^{2u₀} u^{-7/2} du ≤ S^{-5/4}` (constant `C = 1`). -/
theorem mb_tail_S_five_quarters {u₀ κ S : ℝ} (hκ : 1 ≤ κ) (hS : 0 < S) (hu : u₀ = 2 * Real.sqrt (3 * κ * S)) :
    ∫ u in (3 * u₀ / 8)..(2 * u₀), u ^ (-(7 / 2 : ℝ)) ≤ S ^ (-(5 / 4 : ℝ)) := by
  have hsqS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS.le
  have hsq3 : Real.sqrt (3 * κ * S) ^ 2 = 3 * κ * S := Real.sq_sqrt (by nlinarith)
  have ht0 : 0 ≤ Real.sqrt (3 * κ * S) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  have hαS : Real.sqrt S ≤ 3 * u₀ / 8 := by
    rw [hu]
    nlinarith [sq_nonneg (Real.sqrt S - 3 / 2 * Real.sqrt (3 * κ * S))]
  have hsqpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hα : 0 < 3 * u₀ / 8 := lt_of_lt_of_le hsqpos hαS
  have hαb : 3 * u₀ / 8 ≤ 2 * u₀ := by
    have : 0 ≤ u₀ := by rw [hu]; positivity
    linarith
  have h1 := mb_tail_seven_halves hα hαb
  have hrw : S ^ (-(5 / 4 : ℝ)) = (S ^ (1 / 2 : ℝ)) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_mul hS.le]; norm_num
  have h2 : (3 * u₀ / 8) ^ (-(5 / 2 : ℝ)) ≤ S ^ (-(5 / 4 : ℝ)) := by
    rw [hrw, ← Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_nonpos hsqpos hαS (by norm_num)
  have hnn : 0 ≤ (3 * u₀ / 8) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  linarith

/-- info: 'FormalResearch.SignUncertainty.mb_tail_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_tail_pow

/-- info: 'FormalResearch.SignUncertainty.mb_two_sided_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_two_sided_tail

/-- info: 'FormalResearch.SignUncertainty.mb_outer_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_outer_exponent

/-- info: 'FormalResearch.SignUncertainty.mb_liftEps_pow_15_div_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_liftEps_pow_15_div_2

/-- info: 'FormalResearch.SignUncertainty.mb_region_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_region_c

/-- info: 'FormalResearch.SignUncertainty.mb_u0_inv_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_u0_inv_sqrt

/-- info: 'FormalResearch.SignUncertainty.mb_tail_seven_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_tail_seven_halves

/-- info: 'FormalResearch.SignUncertainty.mb_tail_S_five_quarters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_tail_S_five_quarters

end FormalResearch.SignUncertainty
