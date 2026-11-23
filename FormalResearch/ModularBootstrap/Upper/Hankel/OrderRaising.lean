module

public import FormalResearch.ModularBootstrap.Upper.Hankel.BesselJNat

/-!
# Exact order-raising for the Hankel transforms `𝓗_w`

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, section `fw:s1` ("Exact order-raising on the
transform only"), `fw:e1.1`; plan item A3, order `p`.

With `p = j - 1`,
`(𝓗_{p+1} f)(t) = 2π ∫₀^∞ f(s) (s/t)^{p/2} J_p(4π√(s t)) ds` (`hankelTransformOrd p f t`, `J_p = Complex.besselJ p`).
Differentiation of the Bessel kernel under the integral sign, from `∂_t [(2π s)^p S_p(-4π² s t)] =
-2π (2π s)^{p+1} S_{p+1}(-4π² s t)` (`BesselJNat`), gives, for `D_t = (2π)^{-1} ∂_t`,

* `hasDerivAt_hankelTransformOrd`: `∂_t 𝓗_{p+1} f = -2π 𝓗_{p+2} f`, i.e. `𝓗_{j+1} f = -D_t 𝓗_j f`, for
  `f` with `OrderRaisingHyp f (p+1)` (measurable, and `‖f(s)‖ (1 + √s)^{p+1}` integrable on `(0, ∞)`);
* `hankelTransformOrd_eq_iterate`: `𝓗_{p+1} f = (-D_t)^p 𝓗_1 f` on `t > 0`, for `OrderRaisingHyp f p`;
* `orderRaisingHyp_nonvacuous`: the hypothesis holds for a nonzero `f`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.Upper.Hankel

open FormalResearch.ModularBootstrap.WeightAxioms

/-- The order-`p` Hankel transform `(𝓗_{p+1} f)(t) = 2π ∫₀^∞ f(s) (s/t)^{p/2} J_p(4π√(s t)) ds`
(`upper_transfer.tex`, `fw:s1`, with `j = p + 1`). -/
noncomputable def hankelTransformOrd (p : ℕ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  2 * (π : ℂ) * ∫ s in Ioi (0 : ℝ), f s * (((√(s / t)) ^ p : ℝ) : ℂ) *
    Complex.besselJ (p : ℂ) ((4 * π * √(s * t) : ℝ) : ℂ)

/-- The entire-in-`t` form `(2π s)^p S_p(-4π² s t)` of the kernel `(s/t)^{p/2} J_p(4π√(s t))`. -/
noncomputable def besselKern (p : ℕ) (s t : ℝ) : ℂ :=
  (2 * π * (s : ℂ)) ^ p * besselSC p (-(4 * (π : ℂ) ^ 2 * (s : ℂ) * (t : ℂ)))

/-- Integrability hypotheses for order raising up to order `N`: `f` is measurable on `(0, ∞)` and
`‖f(s)‖ (1 + √s)^N` is integrable there. -/
structure OrderRaisingHyp (f : ℝ → ℂ) (N : ℕ) : Prop where
  meas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))
  integ : IntegrableOn (fun s : ℝ => ‖f s‖ * (1 + √s) ^ N) (Ioi 0)

lemma OrderRaisingHyp.mono {f : ℝ → ℂ} {N M : ℕ} (h : OrderRaisingHyp f M) (hNM : N ≤ M) :
    OrderRaisingHyp f N := by
  refine ⟨h.meas, Integrable.mono' h.integ ?_ ?_⟩
  · exact (h.meas.norm.mul (by fun_prop : Continuous fun s : ℝ => (1 + √s) ^ N).aestronglyMeasurable)
  · filter_upwards with s
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    linarith [Real.sqrt_nonneg s]

lemma OrderRaisingHyp.integrableOn_pow {f : ℝ → ℂ} {N : ℕ} (h : OrderRaisingHyp f N) {m : ℕ} (hm : m ≤ N) :
    IntegrableOn (fun s : ℝ => ‖f s‖ * (√s) ^ m) (Ioi 0) := by
  refine Integrable.mono' (h.integ) ?_ ?_
  · exact (h.meas.norm.mul (by fun_prop : Continuous fun s : ℝ => (√s) ^ m).aestronglyMeasurable)
  · filter_upwards with s
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    calc (√s) ^ m ≤ (1 + √s) ^ m := by gcongr; linarith
      _ ≤ (1 + √s) ^ N := pow_le_pow_right₀ (by linarith [Real.sqrt_nonneg s]) hm

lemma continuous_besselKern (p : ℕ) (t : ℝ) : Continuous fun s : ℝ => besselKern p s t := by
  unfold besselKern
  have := (besselSC_entire p).continuous
  fun_prop

lemma hankelTransformOrd_eq_kern (p : ℕ) (f : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    hankelTransformOrd p f t = 2 * (π : ℂ) * ∫ s in Ioi (0 : ℝ), f s * besselKern p s t := by
  unfold hankelTransformOrd
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [mul_assoc, besselJ_kernel_eq p (le_of_lt hs) ht]
  rfl

/-- `‖(2π s)^p S_p(-4π² s t)‖ ≤ (√(s/t))^p` for `s ≥ 0`, `t > 0`. -/
lemma norm_besselKern_le (p : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    ‖besselKern p s t‖ ≤ (√(s / t)) ^ p := by
  unfold besselKern
  rw [← besselJ_kernel_eq p hs ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have := norm_besselJ_nat_le_one p (4 * π * √(s * t))
  calc (√(s / t)) ^ p * ‖Complex.besselJ (p : ℂ) ((4 * π * √(s * t) : ℝ) : ℂ)‖ ≤ (√(s / t)) ^ p * 1 := by
        gcongr
    _ = _ := mul_one _

lemma sqrt_div_le {s t t₀ : ℝ} (hs : 0 ≤ s) (ht₀ : 0 < t₀) (ht : t₀ / 2 ≤ t) :
    √(s / t) ≤ √(2 / t₀) * √s := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have ht' : 0 < t := by linarith
  rw [div_le_iff₀ ht']
  have : 2 / t₀ * s * t ≥ 2 / t₀ * s * (t₀ / 2) :=
    mul_le_mul_of_nonneg_left ht (by positivity)
  have e : 2 / t₀ * s * (t₀ / 2) = s := by field_simp
  linarith

/-- **Order raising**: `∂_t 𝓗_{p+1} f = -2π 𝓗_{p+2} f`, i.e. `𝓗_{j+1} f = -D_t 𝓗_j f` with
`D_t = (2π)^{-1} ∂_t` (`upper_transfer.tex`, `fw:e1.1`). -/
theorem hasDerivAt_hankelTransformOrd {p : ℕ} {f : ℝ → ℂ} (hf : OrderRaisingHyp f (p + 1)) {t₀ : ℝ}
    (ht₀ : 0 < t₀) :
    HasDerivAt (hankelTransformOrd p f) (-(2 * (π : ℂ)) * hankelTransformOrd (p + 1) f t₀) t₀ := by
  have hf0 : OrderRaisingHyp f p := hf.mono (Nat.le_succ p)
  set c : ℝ := √(2 / t₀) with hc
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun s : ℝ => f s * besselKern p s t)
      (volume.restrict (Ioi (0 : ℝ))) := fun t =>
    hf.meas.mul (continuous_besselKern p t).aestronglyMeasurable
  have hF' : ∀ t : ℝ, AEStronglyMeasurable (fun s : ℝ => f s * (-(2 * (π : ℂ)) * besselKern (p + 1) s t))
      (volume.restrict (Ioi (0 : ℝ))) := fun t =>
    hf.meas.mul ((continuous_besselKern (p + 1) t).const_mul _).aestronglyMeasurable
  have hint0 : Integrable (fun s : ℝ => f s * besselKern p s t₀) (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' ((hf0.integrableOn_pow le_rfl).const_mul (c ^ p)) (hmeasF t₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    rw [norm_mul]
    calc ‖f s‖ * ‖besselKern p s t₀‖ ≤ ‖f s‖ * (c ^ p * (√s) ^ p) := by
          gcongr
          refine (norm_besselKern_le p hs0 ht₀).trans ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_div_le hs0 ht₀ (by linarith)) p
      _ = c ^ p * (‖f s‖ * (√s) ^ p) := by ring
  have hb : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ t ∈ Ioo (t₀ / 2) (3 * t₀ / 2),
      ‖f s * (-(2 * (π : ℂ)) * besselKern (p + 1) s t)‖ ≤
        2 * π * c ^ (p + 1) * (‖f s‖ * (√s) ^ (p + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs t ht
    have hs0 : 0 ≤ s := le_of_lt hs
    have ht0 : 0 < t := by linarith [ht.1]
    have h2π : ‖-(2 * (π : ℂ))‖ = 2 * π := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; simp
    rw [norm_mul, norm_mul, h2π]
    calc ‖f s‖ * (2 * π * ‖besselKern (p + 1) s t‖)
        ≤ ‖f s‖ * (2 * π * (c ^ (p + 1) * (√s) ^ (p + 1))) := by
          gcongr
          refine (norm_besselKern_le (p + 1) hs0 ht0).trans ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_div_le hs0 ht₀ ht.1.le) _
      _ = _ := by ring
  have hderiv : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ t ∈ Ioo (t₀ / 2) (3 * t₀ / 2),
      HasDerivAt (fun t : ℝ => f s * besselKern p s t)
        (f s * (-(2 * (π : ℂ)) * besselKern (p + 1) s t)) t := by
    refine Filter.Eventually.of_forall fun s t _ => ?_
    have := (hasDerivAt_besselKernel p s t).const_mul (f s)
    simpa only [besselKern] using this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (𝕜 := ℝ) (F := fun t s => f s * besselKern p s t)
    (F' := fun t s => f s * (-(2 * (π : ℂ)) * besselKern (p + 1) s t))
    (bound := fun s => 2 * π * c ^ (p + 1) * (‖f s‖ * (√s) ^ (p + 1))) (x₀ := t₀)
    (s := Ioo (t₀ / 2) (3 * t₀ / 2)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall hmeasF) hint0 (hF' t₀) hb
    ((hf.integrableOn_pow le_rfl).const_mul _) hderiv
  have hG := key.2.const_mul (2 * (π : ℂ))
  have hev : hankelTransformOrd p f =ᶠ[𝓝 t₀] fun t => 2 * (π : ℂ) * ∫ s in Ioi (0 : ℝ), f s * besselKern p s t := by
    filter_upwards [Ioi_mem_nhds ht₀] with t ht
    exact hankelTransformOrd_eq_kern p f ht
  refine (hG.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hankelTransformOrd_eq_kern (p + 1) f ht₀]
  have e : ∀ s : ℝ, f s * (-(2 * (π : ℂ)) * besselKern (p + 1) s t₀) =
      (-(2 * (π : ℂ))) * (f s * besselKern (p + 1) s t₀) := fun s => by ring
  simp_rw [e]
  rw [integral_const_mul]
  ring

/-- **`𝓗_w = (-D_t)^p 𝓗_1`** (`upper_transfer.tex`, `fw:e1.1`): with `D_t = (2π)^{-1} ∂_t`, for
`f` with `OrderRaisingHyp f p` and `t > 0`. -/
noncomputable def negDt (g : ℝ → ℂ) : ℝ → ℂ := fun t => -((2 * (π : ℂ))⁻¹) * deriv g t

theorem hankelTransformOrd_eq_iterate (p : ℕ) {f : ℝ → ℂ} (hf : OrderRaisingHyp f p) {t : ℝ}
    (ht : 0 < t) : hankelTransformOrd p f t = (negDt^[p] (hankelTransformOrd 0 f)) t := by
  induction p generalizing t with
  | zero => rfl
  | succ n ih =>
    have hf' : OrderRaisingHyp f n := hf.mono (Nat.le_succ n)
    rw [Function.iterate_succ_apply']
    have hev : negDt^[n] (hankelTransformOrd 0 f) =ᶠ[𝓝 t] hankelTransformOrd n f := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact (ih hf' hu).symm
    change _ = -((2 * (π : ℂ))⁻¹) * deriv (negDt^[n] (hankelTransformOrd 0 f)) t
    rw [hev.deriv_eq, (hasDerivAt_hankelTransformOrd hf ht).deriv]
    have h2π : (2 * (π : ℂ)) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    field_simp

/-- Non-vacuity: the hypothesis holds for the indicator of `[0, 1]`, a nonzero profile. -/
theorem orderRaisingHyp_nonvacuous (N : ℕ) :
    ∃ f : ℝ → ℂ, OrderRaisingHyp f N ∧ ∃ s, f s ≠ 0 := by
  refine ⟨Set.indicator (Icc (0 : ℝ) 1) (fun _ => (1 : ℂ)), ⟨?_, ?_⟩, 0, by simp⟩
  · exact (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
  · have hI : IntegrableOn (fun _ : ℝ => (2 : ℝ) ^ N) (Icc 0 1) := integrableOn_const (by simp)
    have hI' : Integrable ((Icc (0 : ℝ) 1).indicator (fun _ : ℝ => (2 : ℝ) ^ N)) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hI
    refine Integrable.mono' hI'.integrableOn ?_ ?_
    · exact ((measurable_const.indicator measurableSet_Icc).norm.mul
        (by fun_prop : Measurable fun s : ℝ => (1 + √s) ^ N)).aestronglyMeasurable
    · filter_upwards with s
      by_cases hs : s ∈ Icc (0 : ℝ) 1
      · simp only [Set.indicator_of_mem hs, norm_one, one_mul]
        rw [Real.norm_of_nonneg (by positivity)]
        have h1 : √s ≤ 1 := by
          rw [Real.sqrt_le_one]; exact hs.2
        calc (1 + √s) ^ N ≤ 2 ^ N := by gcongr; linarith
          _ = _ := rfl
      · simp [Set.indicator_of_notMem hs]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hasDerivAt_hankelTransformOrd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_hankelTransformOrd

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hankelTransformOrd_eq_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelTransformOrd_eq_iterate

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.orderRaisingHyp_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orderRaisingHyp_nonvacuous

end FormalResearch.ModularBootstrap.Upper.Hankel
