module

public import FormalResearch.CohnElkies.AiryWindowInversion
public import FormalResearch.CohnElkies.PreEdgeAndSplineFloor

/-!
# The window smoothing is a B-spline convolution

Formalizes, for a continuous seed `X : ℝ → ℝ`, `m ≥ 1` and `δ₀ > 0`:

* `windowSmooth δ₀ m X x = ∫ t ∈ [0, δ₀], X (x + t) * bspline m δ₀ t`
  (`windowSmooth_eq_bspline_integral`), where `windowSmooth = (movAvg (δ₀/m))^[m]` is the
  `m`-fold moving average of `AiryWindowInversion` and `bspline m δ₀` is the scaled `m`-fold
  uniform B-spline density of `PreEdgeAndSplineFloor`.

Proof route: one moving-average step is an integral against the density `s⁻¹ 1_{[0,s]}`
(`movAvg_eq_integral_windowKer`); by Fubini the `(n+1)`-fold iterate is an integral against the
`(n+1)`-fold convolution of that density (`iterate_movAvg_windowKer`); a dilation argument
identifies that convolution with `bspline m δ₀` (`windowScale_windowKerIter`).

Only continuity of `X` is used: the integrability needed for Fubini comes from the compact
support of the kernels, which bounds `X` on the relevant interval.

Not formalised: the Airy-transform consequences of this identity, and the B-spline bounds of
`PreEdgeAndSplineFloor`. Classification: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace FormalResearch.CohnElkies

/-! ### Kernels and dilations -/

/-- The uniform density `s⁻¹ · 1_{[0, s]}` on `ℝ`. -/
noncomputable def windowKer (s : ℝ) : ℝ → ℝ := Set.indicator (Icc (0 : ℝ) s) (fun _ => s⁻¹)

/-- The `(n+1)`-fold convolution of `windowKer s`, the density of a sum of `n+1` uniforms on `[0, s]`. -/
noncomputable def windowKerIter (s : ℝ) (n : ℕ) : ℝ → ℝ := bsplineConvIter (windowKer s) n

/-- The dilation `t ↦ b⁻¹ · f (t / b)`. -/
noncomputable def windowScale (b : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => b⁻¹ * f (t / b)

theorem windowKer_integrable {s : ℝ} (hs : 0 < s) : Integrable (windowKer s) := by
  unfold windowKer
  exact (integrable_indicator_iff measurableSet_Icc).2
    ((continuous_const : Continuous fun _ : ℝ => s⁻¹).integrableOn_Icc)

/-- info: 'FormalResearch.CohnElkies.windowKer_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.windowKer_integrable

theorem windowKerIter_integrable {s : ℝ} (hs : 0 < s) (n : ℕ) : Integrable (windowKerIter s n) := by
  induction n with
  | zero => exact windowKer_integrable hs
  | succ k ih => exact ih.integrable_convolution _ (windowKer_integrable hs)

/-- info: 'FormalResearch.CohnElkies.windowKerIter_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.windowKerIter_integrable

theorem windowKer_eq_zero {s t : ℝ} (ht : t ∉ Icc (0 : ℝ) s) : windowKer s t = 0 := by
  simp [windowKer, ht]

/-- info: 'FormalResearch.CohnElkies.windowKer_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.windowKer_eq_zero

/-- `windowKerIter s n` vanishes outside `[0, (n+1) s]`. -/
theorem windowKerIter_eq_zero {s : ℝ} (hs : 0 < s) (n : ℕ) {t : ℝ}
    (ht : t ∉ Icc (0 : ℝ) (((n : ℝ) + 1) * s)) : windowKerIter s n t = 0 := by
  induction n generalizing t with
  | zero =>
    have ht' : t ∉ Icc (0 : ℝ) s := by simpa using ht
    simpa [windowKerIter, bsplineConvIter] using windowKer_eq_zero ht'
  | succ k ih =>
    have hz : ∀ r, windowKerIter s k r * windowKer s (t - r) = 0 := by
      intro r
      by_cases hr : r ∈ Icc (0 : ℝ) (((k : ℝ) + 1) * s)
      · by_cases hm : t - r ∈ Icc (0 : ℝ) s
        · exfalso
          apply ht
          have e : (((k + 1 : ℕ) : ℝ) + 1) * s = s + ((k : ℝ) + 1) * s := by push_cast; ring
          rw [e]
          exact ⟨by linarith [hr.1, hm.2, hm.1], by linarith [hr.2, hm.2]⟩
        · rw [windowKer_eq_zero hm, mul_zero]
      · rw [ih (t := r) hr, zero_mul]
    show ∫ r, ContinuousLinearMap.mul ℝ ℝ (windowKerIter s k r) (windowKer s (t - r)) = 0
    simp only [ContinuousLinearMap.mul_apply', hz, integral_zero]

/-- info: 'FormalResearch.CohnElkies.windowKerIter_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.windowKerIter_eq_zero

/-- Dilation of the uniform kernel: `b⁻¹ · windowKer a (t / b) = windowKer (a b) t`. -/
theorem windowScale_windowKer {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    windowScale b (windowKer a) = windowKer (a * b) := by
  funext t
  have key : t / b ∈ Icc (0 : ℝ) a ↔ t ∈ Icc (0 : ℝ) (a * b) := by
    simp only [mem_Icc, le_div_iff₀ hb, div_le_iff₀ hb, zero_mul]
  unfold windowScale windowKer
  by_cases h : t ∈ Icc (0 : ℝ) (a * b)
  · rw [indicator_of_mem (key.2 h), indicator_of_mem h]
    rw [mul_inv]; ring
  · rw [indicator_of_notMem (fun h' => h (key.1 h')), indicator_of_notMem h, mul_zero]

/-- info: 'FormalResearch.CohnElkies.windowScale_windowKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.windowScale_windowKer

/-- Dilation commutes with convolution (Lebesgue measure, multiplication kernel). -/
theorem windowScale_convolution {c : ℝ} (hc : 0 < c) (f g : ℝ → ℝ) :
    windowScale c (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) =
      windowScale c f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] windowScale c g := by
  funext x
  have hsub : ∫ u : ℝ, c⁻¹ * f (c * u / c) * (c⁻¹ * g ((x - c * u) / c)) =
      c⁻¹ * ∫ t : ℝ, c⁻¹ * f (t / c) * (c⁻¹ * g ((x - t) / c)) := by
    have h := Measure.integral_comp_mul_left
      (fun t : ℝ => c⁻¹ * f (t / c) * (c⁻¹ * g ((x - t) / c))) c
    rw [abs_of_pos (inv_pos.mpr hc), smul_eq_mul] at h
    exact h
  have hG : ∀ u : ℝ, c⁻¹ * f (c * u / c) * (c⁻¹ * g ((x - c * u) / c)) =
      c⁻¹ * c⁻¹ * (f u * g (x / c - u)) := by
    intro u
    have h1 : c * u / c = u := mul_div_cancel_left₀ u hc.ne'
    have h2 : (x - c * u) / c = x / c - u := by rw [sub_div, h1]
    rw [h1, h2]; ring
  simp only [hG, integral_const_mul] at hsub
  simp only [windowScale, convolution_def, ContinuousLinearMap.mul_apply']
  apply mul_left_cancel₀ (inv_ne_zero hc.ne')
  rw [← mul_assoc]
  exact hsub

/-- info: 'FormalResearch.CohnElkies.windowScale_convolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.windowScale_convolution

/-- Dilation of the `(n+1)`-fold convolution: `b⁻¹ · windowKerIter a n (t / b) = windowKerIter (a b) n t`. -/
theorem windowScale_windowKerIter {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    windowScale b (windowKerIter a k) = windowKerIter (a * b) k := by
  induction k with
  | zero => exact windowScale_windowKer ha hb
  | succ k ih =>
    show windowScale b (windowKerIter a k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] windowKer a) =
      windowKerIter (a * b) k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] windowKer (a * b)
    rw [windowScale_convolution hb, ih, windowScale_windowKer ha hb]

/-- info: 'FormalResearch.CohnElkies.windowScale_windowKerIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.windowScale_windowKerIter

/-! ### One moving-average step and the Fubini identity -/

/-- One moving average is an integral against the uniform kernel. -/
theorem movAvg_eq_integral_windowKer {s : ℝ} (hs : 0 < s) (H : ℝ → ℝ) (u : ℝ) :
    movAvg s H u = ∫ v, windowKer s v * H (u + v) := by
  have hcov := intervalIntegral.integral_comp_mul_left (fun x : ℝ => H (u + x)) (a := 0) (b := 1)
    hs.ne'
  simp only [mul_zero, mul_one] at hcov
  unfold movAvg
  rw [hcov, smul_eq_mul, intervalIntegral.integral_of_le hs.le, ← integral_Icc_eq_integral_Ioc]
  have hR : (fun v : ℝ => windowKer s v * H (u + v)) =
      Set.indicator (Icc (0 : ℝ) s) (fun v => s⁻¹ * H (u + v)) := by
    funext v
    by_cases hv : v ∈ Icc (0 : ℝ) s
    · simp [windowKer, hv]
    · simp [windowKer, hv]
  rw [hR, integral_indicator measurableSet_Icc, integral_const_mul]

/-- info: 'FormalResearch.CohnElkies.movAvg_eq_integral_windowKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.movAvg_eq_integral_windowKer

/-- Fubini step: the next moving average of the `n`-th kernel integral is the `(n+1)`-st one. -/
theorem integral_windowKer_step {s : ℝ} (hs : 0 < s) {X : ℝ → ℝ} (hX : Continuous X) (n : ℕ)
    (u : ℝ) :
    ∫ v, windowKer s v * ∫ t, X (u + v + t) * windowKerIter s n t =
      ∫ τ, X (u + τ) * windowKerIter s (n + 1) τ := by
  have hK : Integrable (windowKerIter s n) := windowKerIter_integrable hs n
  have hg : Integrable (windowKer s) := windowKer_integrable hs
  have hH : Integrable (fun p : ℝ × ℝ => windowKer s p.2 * windowKerIter s n (p.1 - p.2))
      (volume.prod volume) := by
    have h := hg.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hK
    simpa [ContinuousLinearMap.mul_apply'] using h
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := u) (b := u + (((n : ℝ) + 1) * s + s))).exists_bound_of_continuousOn
    hX.continuousOn
  have hF : Integrable (fun p : ℝ × ℝ => X (u + p.1) * (windowKer s p.2 * windowKerIter s n (p.1 - p.2)))
      (volume.prod volume) := by
    refine Integrable.mono' (hH.norm.const_mul C) ?_ ?_
    · exact ((hX.comp (continuous_const.add continuous_fst)).aestronglyMeasurable).mul
        hH.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      show ‖X (u + p.1) * (windowKer s p.2 * windowKerIter s n (p.1 - p.2))‖ ≤
        C * ‖windowKer s p.2 * windowKerIter s n (p.1 - p.2)‖
      by_cases hp : p.1 ∈ Icc (0 : ℝ) (((n : ℝ) + 1) * s + s)
      · have hXb : ‖X (u + p.1)‖ ≤ C := hC _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hXb (norm_nonneg _)
      · have h0 : windowKer s p.2 * windowKerIter s n (p.1 - p.2) = 0 := by
          by_cases hv : p.2 ∈ Icc (0 : ℝ) s
          · have hz : p.1 - p.2 ∉ Icc (0 : ℝ) (((n : ℝ) + 1) * s) := by
              intro h
              exact hp ⟨by linarith [h.1, hv.1], by linarith [h.2, hv.2]⟩
            rw [windowKerIter_eq_zero hs n hz, mul_zero]
          · rw [windowKer_eq_zero hv, zero_mul]
        rw [h0]
        simp
  have htr : ∀ v : ℝ, ∫ t, X (u + v + t) * windowKerIter s n t =
      ∫ τ, X (u + τ) * windowKerIter s n (τ - v) := by
    intro v
    calc ∫ t, X (u + v + t) * windowKerIter s n t
        = ∫ t, X (u + (v + t)) * windowKerIter s n (v + t - v) := by
          congr 1; funext t; rw [add_sub_cancel_left, add_assoc]
      _ = ∫ τ, X (u + τ) * windowKerIter s n (τ - v) :=
          integral_add_left_eq_self (fun τ => X (u + τ) * windowKerIter s n (τ - v)) v
  have hstep : ∀ v : ℝ, windowKer s v * ∫ t, X (u + v + t) * windowKerIter s n t =
      ∫ τ, X (u + τ) * (windowKer s v * windowKerIter s n (τ - v)) := by
    intro v
    rw [htr v, ← integral_const_mul]
    congr 1; funext τ; ring
  have hswap := integral_integral_swap (μ := volume) (ν := volume)
    (f := fun v τ => X (u + τ) * (windowKer s v * windowKerIter s n (τ - v))) hF.swap
  have hconv : ∀ τ : ℝ, ∫ v, windowKer s v * windowKerIter s n (τ - v) =
      windowKerIter s (n + 1) τ := by
    intro τ
    have hc : windowKerIter s (n + 1) τ = ∫ t, windowKer s (τ - t) * windowKerIter s n t := by
      show ∫ t, ContinuousLinearMap.mul ℝ ℝ (windowKerIter s n t) (windowKer s (τ - t)) = _
      congr 1; funext t; simp only [ContinuousLinearMap.mul_apply']; ring
    rw [hc]
    calc ∫ v, windowKer s v * windowKerIter s n (τ - v)
        = ∫ t, windowKer s (τ - t) * windowKerIter s n (τ - (τ - t)) :=
          (integral_sub_left_eq_self (μ := volume) (fun v => windowKer s v * windowKerIter s n (τ - v)) τ).symm
      _ = ∫ t, windowKer s (τ - t) * windowKerIter s n t := by simp
  calc ∫ v, windowKer s v * ∫ t, X (u + v + t) * windowKerIter s n t
      = ∫ v, ∫ τ, X (u + τ) * (windowKer s v * windowKerIter s n (τ - v)) := by
        simp only [hstep]
    _ = ∫ τ, ∫ v, X (u + τ) * (windowKer s v * windowKerIter s n (τ - v)) := hswap
    _ = ∫ τ, X (u + τ) * windowKerIter s (n + 1) τ := by
        congr 1; funext τ; rw [integral_const_mul, hconv]

/-- info: 'FormalResearch.CohnElkies.integral_windowKer_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.integral_windowKer_step

/-- The `(n+1)`-fold moving average is an integral against the `(n+1)`-fold kernel convolution. -/
theorem iterate_movAvg_windowKer {s : ℝ} (hs : 0 < s) {X : ℝ → ℝ} (hX : Continuous X) (n : ℕ)
    (u : ℝ) : (movAvg s)^[n + 1] X u = ∫ t, X (u + t) * windowKerIter s n t := by
  induction n generalizing u with
  | zero =>
    rw [zero_add, Function.iterate_one, movAvg_eq_integral_windowKer hs]
    congr 1; funext t
    simp only [windowKerIter, bsplineConvIter]
    ring
  | succ n ih =>
    rw [Function.iterate_succ_apply', movAvg_eq_integral_windowKer hs]
    simp only [ih]
    exact integral_windowKer_step hs hX n u

/-- info: 'FormalResearch.CohnElkies.iterate_movAvg_windowKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.iterate_movAvg_windowKer

/-! ### The B-spline identification and the main theorem -/

/-- `windowSmooth δ₀ m X x` is the B-spline convolution integral of the seed over `[0, δ₀]`. -/
theorem windowSmooth_eq_bspline_integral {X : ℝ → ℝ} (hX : Continuous X) {δ₀ : ℝ} (hδ : 0 < δ₀)
    {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    windowSmooth δ₀ m X x = ∫ t in Set.Icc (0 : ℝ) δ₀, X (x + t) * bspline m δ₀ t := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hpos : 0 < δ₀ / ((n + 1 : ℕ) : ℝ) := div_pos hδ (by positivity)
  have hpos' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hL : ((n : ℝ) + 1) * (δ₀ / ((n + 1 : ℕ) : ℝ)) = δ₀ := by
    push_cast; field_simp
  have hB : bsplineBox (n + 1) = windowKer (((n + 1 : ℕ) : ℝ)⁻¹) := by
    funext t
    simp [bsplineBox, windowKer, inv_inv]
  have hU' : ∀ t, bsplineUnit (n + 1) t = bsplineConvIter (bsplineBox (n + 1)) n t := by
    intro t
    unfold bsplineUnit
    rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
  have hU : bsplineUnit (n + 1) = windowKerIter (((n + 1 : ℕ) : ℝ)⁻¹) n := by
    funext t
    rw [hU' t, hB]
    rfl
  have hbs : bspline (n + 1) δ₀ = windowKerIter (δ₀ / ((n + 1 : ℕ) : ℝ)) n := by
    rw [show bspline (n + 1) δ₀ = windowScale δ₀ (bsplineUnit (n + 1)) from rfl, hU,
      windowScale_windowKerIter hpos' hδ n, inv_mul_eq_div]
  have hvan : ∀ t ∉ Icc (0 : ℝ) δ₀,
      X (x + t) * windowKerIter (δ₀ / ((n + 1 : ℕ) : ℝ)) n t = 0 := by
    intro t ht
    rw [windowKerIter_eq_zero (t := t) hpos n (by rw [hL]; exact ht), mul_zero]
  unfold windowSmooth
  rw [iterate_movAvg_windowKer hpos hX n x, hbs, setIntegral_eq_integral_of_forall_compl_eq_zero hvan]

/-- info: 'FormalResearch.CohnElkies.windowSmooth_eq_bspline_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.windowSmooth_eq_bspline_integral

end FormalResearch.CohnElkies
