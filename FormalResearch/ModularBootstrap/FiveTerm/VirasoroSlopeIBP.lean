module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroPoissonSlope
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroXbEdge

/-!
# Integration by parts for the edge slope (FIVE-0, `ctu:jets`, step 2')

`π ∫_ℝ (a(t) - a(0)) cosh(πt)/sinh²(πt) dt = 2 ∫_0^∞ a'(t)/sinh(πt) dt` for an even amplitude with `a'` such that
the right-hand integrand is integrable.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma integrableOn_Ioi_of_deriv {f f' : ℝ → ℝ} {m : ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 < x → 0 ≤ f' x) (hf : Tendsto f atTop (𝓝 m)) :
    IntegrableOn f' (Ioi 0) ∧ ∫ x in Ioi 0, f' x = m - f 0 :=
  ⟨integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x) hpos hf,
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => hd x) hpos hf⟩

lemma hasDerivAt_neg_inv_sinh {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(π * Real.sinh (π * x))⁻¹) (kern x) x := by
  have hpi := Real.pi_pos
  have hs : Real.sinh (π * x) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have h1 : HasDerivAt (fun x : ℝ => π * Real.sinh (π * x)) (π * (Real.cosh (π * x) * π)) x := by
    have := (Real.hasDerivAt_sinh (π * x)).comp x ((hasDerivAt_id x).const_mul π)
    simpa using this.const_mul π
  have h2 := (h1.inv (by positivity)).neg
  refine h2.congr_deriv ?_
  unfold kern
  field_simp

theorem slope_ibp {a a' : ℝ → ℝ} (ha : Amp a) (hd : ∀ t, 0 < t → HasDerivAt a (a' t) t)
    (hint : IntegrableOn (fun t => a' t / Real.sinh (π * t)) (Ioi 0)) :
    ∫ t : ℝ, (a t - a 0) * (π * kern t) = 2 * ∫ t in Ioi 0, a' t / Real.sinh (π * t) := by
  have hpi := Real.pi_pos
  obtain ⟨Cb, hCb⟩ := slope_bound ha
  obtain ⟨K, r, hr, hK⟩ := amp_sq_bound ha
  obtain ⟨M, hM⟩ := ha.bdd
  -- evenness
  have hev : ∀ t : ℝ, (a |t| - a 0) * (π * kern |t|) = (a t - a 0) * (π * kern t) := by
    intro t
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, ha.even]
      have : kern (-t) = kern t := by unfold kern; rw [mul_neg, Real.cosh_neg, Real.sinh_neg]; ring
      rw [this]
  have hI : ∫ t : ℝ, (a t - a 0) * (π * kern t) = 2 * ∫ t in Ioi (0 : ℝ), (a t - a 0) * (π * kern t) := by
    rw [← integral_comp_abs (f := fun t => (a t - a 0) * (π * kern t))]
    exact integral_congr_ae (Eventually.of_forall fun t => (hev t).symm)
  -- integration by parts on (0, ∞)
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => -(π * Real.sinh (π * x))⁻¹) (kern x) x :=
    fun x hx => hasDerivAt_neg_inv_sinh hx
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x => a x - a 0) (a' x) x :=
    fun x hx => (hd x hx).sub_const _
  have hcont : ContinuousOn (fun t : ℝ => (a t - a 0) * kern t) (Ioi 0) := by
    refine ((ha.cont.sub continuous_const).continuousOn).mul ?_
    unfold kern
    refine (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).continuousOn.div
      ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).pow 2).continuousOn ?_
    intro t ht
    have : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (by have : (0 : ℝ) < t := ht; positivity)).ne'
    positivity
  have huv' : IntegrableOn ((fun x => a x - a 0) * kern) (Ioi 0) := by
    refine Integrable.mono' (((integrable_exp_neg_mul_abs one_pos).const_mul (Cb / π)).integrableOn)
      (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : t ≠ 0 := (ne_of_gt ht)
    have := hCb t ht0
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (kern_nonneg t)]
    calc |a t - a 0| * kern t = (|a t - a 0| * (π * kern t)) / π := by field_simp
      _ ≤ (Cb * Real.exp (-(1 * |t|))) / π := by gcongr
      _ = Cb / π * Real.exp (-(1 * |t|)) := by ring
  have hu'v : IntegrableOn (a' * fun x : ℝ => -(π * Real.sinh (π * x))⁻¹) (Ioi 0) := by
    refine (hint.const_mul (-1 / π)).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    simp only [Pi.mul_apply]
    have : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (by have : (0 : ℝ) < t := ht; positivity)).ne'
    field_simp
  have hz : Tendsto ((fun x => a x - a 0) * fun x : ℝ => -(π * Real.sinh (π * x))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun t : ℝ => |K| / π ^ 2 * t) (𝓝[>] 0) (𝓝 0) by
      have : Tendsto (fun t : ℝ => |K| / π ^ 2 * t) (𝓝 0) (𝓝 (|K| / π ^ 2 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT hr] with t ht
    have ht0 : 0 < t := ht.1
    have h1 := hK t (by rw [abs_of_pos ht0]; exact ht.2)
    have hsh : π * t ≤ Real.sinh (π * t) := Real.self_le_sinh_iff.mpr (by positivity)
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_neg, abs_inv]
    rw [abs_of_pos (show 0 < π * Real.sinh (π * t) by have := Real.sinh_pos_iff.mpr (show 0 < π * t by positivity); positivity)]
    have hpos : 0 < π * (π * t) := by positivity
    calc |a t - a 0| * (π * Real.sinh (π * t))⁻¹ ≤ (|K| * t ^ 2) * (π * (π * t))⁻¹ := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg t))
      _ = |K| / π ^ 2 * t := by field_simp
  have hinf : Tendsto ((fun x => a x - a 0) * fun x : ℝ => -(π * Real.sinh (π * x))⁻¹) atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => 4 * (|M| + |a 0|) / π * Real.exp ((1 - π) * t)) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => Real.exp ((1 - π) * t)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_gt_three]))
      simpa using this.const_mul (4 * (|M| + |a 0|) / π)
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hex1 : 1 ≤ Real.exp t := Real.one_le_exp ht0.le
    have h1 : |a t - a 0| ≤ (|M| + |a 0|) * Real.exp t := by
      have := hM t
      rw [abs_of_pos ht0] at this
      have h2 : M * Real.exp t ≤ |M| * Real.exp t :=
        mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
      calc |a t - a 0| ≤ |a t| + |a 0| := abs_sub _ _
        _ ≤ |M| * Real.exp t + |a 0| * 1 := by linarith
        _ ≤ |M| * Real.exp t + |a 0| * Real.exp t := by nlinarith [abs_nonneg (a 0)]
        _ = _ := by ring
    have hsh : Real.exp (π * t) / 4 ≤ Real.sinh (π * t) := sinh_ge_exp (by nlinarith [Real.pi_gt_three])
    have hshpos : 0 < Real.exp (π * t) / 4 := by positivity
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_neg, abs_inv]
    rw [abs_of_pos (show 0 < π * Real.sinh (π * t) by positivity)]
    have hc : (π * Real.sinh (π * t))⁻¹ ≤ (π * (Real.exp (π * t) / 4))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact mul_le_mul_of_nonneg_left hsh hpi.le
    calc |a t - a 0| * (π * Real.sinh (π * t))⁻¹
        ≤ ((|M| + |a 0|) * Real.exp t) * (π * (Real.exp (π * t) / 4))⁻¹ := by gcongr
      _ = 4 * (|M| + |a 0|) / π * Real.exp ((1 - π) * t) := by
        rw [sub_mul, one_mul, Real.exp_sub]
        field_simp
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (u := fun x => a x - a 0)
    (u' := a') (v := fun x : ℝ => -(π * Real.sinh (π * x))⁻¹) (v' := kern) hu hv huv' hu'v hz hinf
  simp only [sub_zero, zero_sub] at hibp
  rw [hI]
  congr 1
  have e1 : ∫ t in Ioi (0 : ℝ), (a t - a 0) * (π * kern t) = π * ∫ t in Ioi (0 : ℝ), (a t - a 0) * kern t := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [e1, hibp]
  have e2 : ∫ x in Ioi (0 : ℝ), a' x * -(π * Real.sinh (π * x))⁻¹ =
      -((1 / π) * ∫ x in Ioi (0 : ℝ), a' x / Real.sinh (π * x)) := by
    rw [← integral_const_mul, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (by have : (0 : ℝ) < t := ht; positivity)).ne'
    field_simp
  rw [e2]
  field_simp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.slope_ibp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.slope_ibp

end FormalResearch.ModularBootstrap.FiveTerm
