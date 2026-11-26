module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Quot

/-!
# The third odd jet of `h̄_a` as a first-order slope (FIVE-0, `ctu:jets`, `g₃`, step 2)

Let `a` and `b` be admissible amplitudes with `b = (a - a(0))/sinh²(πt)` (`amp_quot`).  With the strip Poisson kernel
`P_ε(t) = sin(πε) cosh(πt)/(sinh²(πt) + sin²(πε))` one has the exact algebraic identity
`sinh² P_ε = sin(πε) cosh - sin²(πε) P_ε`, hence for `0 < ε < 1`

`Re h̄_a(ε) - a(0) = (h₁/π) sin(πε) - sin²(πε) Re h̄_b(ε)`,   `h₁ = ∫ (a - a(0)) π kern`,

and with the slope theorem for `b` (`hbarA_slope`)
`(Re h̄_a(ε) - a(0) - h₁ ε + π² b(0) ε²)/ε³ → -π² (h₁/6 + d₁)`, `d₁ = ∫ (b - b(0)) π kern`.
(`poisson_third`).  No analyticity of `h̄_a` beyond `Amp` is used.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma re_hbarA_eq_integral {a : ℝ → ℝ} (ha : Amp a) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (hbarA a (ε : ℂ)).re = ∫ t : ℝ, a t * poissonK ε t := by
  have hst : (ε : ℂ) ∈ strip := ⟨by simpa using h0, by simpa using h1⟩
  rw [hbarA_of_mem_strip ha hst, re_genH ha hst]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub]
  simp only [poissonK_even]

lemma integrable_amp_poissonK {a : ℝ → ℝ} (ha : Amp a) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Integrable (fun t : ℝ => a t * poissonK ε t) := by
  have hst : (ε : ℂ) ∈ strip := ⟨by simpa using h0, by simpa using h1⟩
  have := integrable_re_genH ha hst
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub]
  rw [poissonK_even]

lemma integrable_slope_integrand {a : ℝ → ℝ} (ha : Amp a) :
    Integrable (fun t : ℝ => (a t - a 0) * (π * kern t)) := by
  obtain ⟨Cb, hCb⟩ := slope_bound ha
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (a t - a 0) * (π * kern t)) volume := by
    have : Measurable (fun t : ℝ => (a t - a 0) * (π * kern t)) := by
      have h1 : Measurable a := ha.cont.measurable
      unfold kern
      fun_prop
    exact this.aestronglyMeasurable
  refine Integrable.mono' ((integrable_exp_neg_mul_abs one_pos).const_mul Cb) hmeas ?_
  have hae : ∀ᵐ t : ℝ, t ≠ 0 := by
    have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
    simpa using this
  filter_upwards [hae] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg Real.pi_pos.le (kern_nonneg t))]
  exact hCb t ht

lemma tendsto_sin_pi_sub_cube :
    Tendsto (fun x : ℝ => (Real.sin x - x) / x ^ 3) (𝓝[>] 0) (𝓝 (-1 / 6)) := by
  have h : Tendsto (fun x : ℝ => (Real.sin x - (x - x ^ 3 / 6)) / x ^ 3) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (show Tendsto (fun x : ℝ => 1 / 100 * x) (𝓝[>] 0) (𝓝 0) by
        have : Tendsto (fun x : ℝ => 1 / 100 * x) (𝓝 0) (𝓝 (1 / 100 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    have hb := Real.sin_bound (x := x) (by rw [abs_of_pos hx.1]; exact hx.2.le)
    rw [abs_of_pos hx.1] at hb
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hx.1 3),
      div_le_iff₀ (pow_pos hx.1 3)]
    have hx5 : x ^ 5 / 100 ≤ 1 / 100 * x * x ^ 3 := by
      have : x ^ 5 = x * x ^ 3 * x := by ring
      rw [this]
      have hx3 := pow_pos hx.1 3
      nlinarith [mul_pos hx.1 hx3, hx.2]
    exact hb.trans hx5
  have := h.add_const (-1 / 6)
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

lemma sin_sq_sub_sq_bound {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) : |Real.sin x ^ 2 - x ^ 2| ≤ 2 * x ^ 4 := by
  have hb := Real.sin_bound (x := x) (by rw [abs_of_pos h0]; exact h1)
  rw [abs_of_pos h0] at hb
  have hs1 : Real.sin x ≤ x := Real.sin_le h0.le
  have hs2 : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_gt_three])
  have hd : |Real.sin x - x| ≤ x ^ 3 := by
    have hb' := abs_le.mp hb
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have h5 : x ^ 5 ≤ x ^ 3 := by
      calc x ^ 5 = x ^ 3 * x ^ 2 := by ring
        _ ≤ x ^ 3 * 1 := by gcongr
        _ = x ^ 3 := mul_one _
    have h3 := pow_pos h0 3
    rw [abs_le]
    constructor <;> nlinarith [hb'.1, hb'.2]
  calc |Real.sin x ^ 2 - x ^ 2| = |Real.sin x - x| * |Real.sin x + x| := by
        rw [← abs_mul]; congr 1; ring
    _ ≤ x ^ 3 * (2 * x) := by
        refine mul_le_mul hd ?_ (abs_nonneg _) (by positivity)
        rw [abs_of_pos (by linarith)]; linarith
    _ = 2 * x ^ 4 := by ring

/-- **Third-order Taylor coefficient of `Re h̄_a` at `0` through the quotient amplitude.** -/
theorem poisson_third {a b : ℝ → ℝ} (ha : Amp a) (hb : Amp b)
    (hab : ∀ t : ℝ, t ≠ 0 → b t = (a t - a 0) / Real.sinh (π * t) ^ 2) :
    Tendsto (fun ε : ℝ => ((hbarA a (ε : ℂ)).re - a 0 - ε * (∫ t : ℝ, (a t - a 0) * (π * kern t)) +
        π ^ 2 * b 0 * ε ^ 2) / ε ^ 3) (𝓝[>] 0)
      (𝓝 (-(π ^ 2) * ((∫ t : ℝ, (a t - a 0) * (π * kern t)) / 6 + ∫ t : ℝ, (b t - b 0) * (π * kern t)))) := by
  have hpi := Real.pi_pos
  set h1 : ℝ := ∫ t : ℝ, (a t - a 0) * (π * kern t) with hh1
  set d1 : ℝ := ∫ t : ℝ, (b t - b 0) * (π * kern t) with hd1
  set K0 : ℝ := ∫ t : ℝ, (a t - a 0) * kern t with hK0
  have hK0h : h1 = π * K0 := by
    rw [hh1, hK0, ← integral_const_mul]; congr 1; funext t; ring
  have hiK : Integrable (fun t : ℝ => (a t - a 0) * kern t) := by
    have := (integrable_slope_integrand ha).const_mul (1 / π)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only; field_simp
  -- the exact identity
  have hid : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (hbarA a (ε : ℂ)).re - a 0 = Real.sin (π * ε) * K0 - Real.sin (π * ε) ^ 2 * (hbarA b (ε : ℂ)).re := by
    intro ε h0 h1'
    set x : ℝ := π * ε with hx
    have hxpos : 0 < x := by positivity
    have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hxpos (by nlinarith [Real.pi_gt_three])
    have hP : ∀ t : ℝ, poissonK ε t = Real.sin x * Real.cosh (π * t) /
        (Real.sinh (π * t) ^ 2 + Real.sin x ^ 2) := fun t => poissonK_eq h0 h1' t
    have hint1 := integrable_amp_poissonK ha h0 h1'
    have hint2 := integrable_amp_poissonK hb h0 h1'
    have hPint := integrable_poissonK h0 h1'
    have hA : (hbarA a (ε : ℂ)).re - a 0 = ∫ t : ℝ, (a t - a 0) * poissonK ε t := by
      rw [re_hbarA_eq_integral ha h0 h1']
      have : (fun t : ℝ => (a t - a 0) * poissonK ε t) = fun t => a t * poissonK ε t - a 0 * poissonK ε t := by
        funext t; ring
      rw [this, integral_sub hint1 (hPint.const_mul _), integral_const_mul, integral_poissonK h0 h1']; ring
    rw [hA, re_hbarA_eq_integral hb h0 h1']
    -- pointwise identity off 0
    have hae : ∀ᵐ t : ℝ, t ≠ 0 := by
      have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
      simpa using this
    have hpt : ∀ᵐ t : ℝ, (a t - a 0) * poissonK ε t =
        Real.sin x * ((a t - a 0) * kern t) - Real.sin x ^ 2 * (b t * poissonK ε t) := by
      filter_upwards [hae] with t ht
      have hsh : Real.sinh (π * t) ^ 2 ≠ 0 := by
        have : Real.sinh (π * t) ≠ 0 := by
          intro h; have := Real.sinh_eq_zero.mp h
          apply ht; nlinarith
        positivity
      have hden : Real.sinh (π * t) ^ 2 + Real.sin x ^ 2 ≠ 0 := by positivity
      rw [hP t, hab t ht]
      unfold kern
      field_simp
      ring
    rw [integral_congr_ae hpt]
    have hi3 : Integrable (fun t : ℝ => Real.sin x * ((a t - a 0) * kern t)) := hiK.const_mul _
    have hi4 : Integrable (fun t : ℝ => Real.sin x ^ 2 * (b t * poissonK ε t)) := hint2.const_mul _
    rw [integral_sub hi3 hi4, integral_const_mul, integral_const_mul]
  -- the limit
  have hbs := hbarA_slope hb
  have hs1 : Tendsto (fun ε : ℝ => Real.sin (π * ε) / ε) (𝓝[>] 0) (𝓝 π) := tendsto_sin_pi_div
  have hT1 : Tendsto (fun ε : ℝ => K0 * π ^ 3 * ((Real.sin (π * ε) - π * ε) / (π * ε) ^ 3)) (𝓝[>] 0)
      (𝓝 (K0 * π ^ 3 * (-1 / 6))) := by
    have hm : Tendsto (fun ε : ℝ => π * ε) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun ε : ℝ => π * ε) (𝓝 0) (𝓝 (π * 0)) := (continuous_const.mul continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mul_pos hpi hε
    exact (tendsto_sin_pi_sub_cube.comp hm).const_mul _
  have hT2 : Tendsto (fun ε : ℝ => -((Real.sin (π * ε) / ε) ^ 2 * (((hbarA b (ε : ℂ)).re - b 0) / ε))) (𝓝[>] 0)
      (𝓝 (-(π ^ 2 * d1))) := by
    exact ((hs1.pow 2).mul hbs).neg
  have hT3 : Tendsto (fun ε : ℝ => -(b 0 * ((Real.sin (π * ε) ^ 2 - (π * ε) ^ 2) / ε ^ 3))) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => (Real.sin (π * ε) ^ 2 - (π * ε) ^ 2) / ε ^ 3) (𝓝[>] 0) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (show Tendsto (fun x : ℝ => 2 * π ^ 4 * x) (𝓝[>] 0) (𝓝 0) by
          have : Tendsto (fun x : ℝ => 2 * π ^ 4 * x) (𝓝 0) (𝓝 (2 * π ^ 4 * 0)) :=
            (continuous_const.mul continuous_id).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds)
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / π by positivity)] with ε hε
      have hε0 : 0 < ε := hε.1
      have hx1 : π * ε ≤ 1 := by
        have := hε.2; rw [lt_div_iff₀ hpi] at this; linarith
      have hb4 := sin_sq_sub_sq_bound (x := π * ε) (by positivity) hx1
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hε0 3), div_le_iff₀ (pow_pos hε0 3)]
      calc |Real.sin (π * ε) ^ 2 - (π * ε) ^ 2| ≤ 2 * (π * ε) ^ 4 := hb4
        _ = 2 * π ^ 4 * ε * ε ^ 3 := by ring
    simpa using (h0.const_mul (b 0)).neg
  have hsum := (hT1.add hT2).add hT3
  have hval : K0 * π ^ 3 * (-1 / 6) + -(π ^ 2 * d1) + 0 = -(π ^ 2) * (h1 / 6 + d1) := by
    rw [hK0h]; ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
  have hε0 : 0 < ε := hε.1
  have hI := hid ε hε.1 hε.2
  have hx : π * ε ≠ 0 := by positivity
  have hre : (hbarA a (ε : ℂ)).re = a 0 + (Real.sin (π * ε) * K0 - Real.sin (π * ε) ^ 2 * (hbarA b (ε : ℂ)).re) := by
    linarith
  rw [hre]
  have hh1' : ε * (∫ t : ℝ, (a t - a 0) * (π * kern t)) = K0 * (π * ε) := by
    have : (∫ t : ℝ, (a t - a 0) * (π * kern t)) = π * K0 := hK0h
    rw [this]; ring
  rw [hh1']
  field_simp
  ring

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.poisson_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.poisson_third
