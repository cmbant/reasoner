module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Taylor remainders along a segment, and conjugation symmetry of the derivative (CFU chart, `ct:cfu`)

**Proved.**  `taylor1_seg`, `taylor2_seg`: `p(z) - p(β) = (z-β) ∫₀¹ p'(β + t(z-β)) dt` and
`p(z) - p(β) - p'(β)(z-β) = (z-β)² ∫₀¹ (1-t) p''(β + t(z-β)) dt` for complex-differentiable `p`; `hasDerivAt_conj_symm`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Interval

namespace FormalResearch.SignUncertainty.CtChart

lemma hasDerivAt_seg {p p1 : ℂ → ℂ} {z β : ℂ} {t : ℝ} (hp : HasDerivAt p (p1 (β + t * (z - β))) (β + t * (z - β))) :
    HasDerivAt (fun s : ℝ => p (β + (s : ℂ) * (z - β))) ((z - β) * p1 (β + t * (z - β))) t := by
  have hw : HasDerivAt (fun s : ℝ => β + (s : ℂ) * (z - β)) (z - β) t := by
    have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have := hid.ofReal_comp.mul_const (z - β) |>.const_add β
    simpa using this
  have := hp.scomp t hw
  simpa [smul_eq_mul, Function.comp_def] using this

/-- First-order Taylor identity along a segment. -/
lemma taylor1_seg {p p1 : ℂ → ℂ} {z β : ℂ}
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt p (p1 (β + t * (z - β))) (β + t * (z - β)))
    (hc : ContinuousOn (fun t : ℝ => p1 (β + (t : ℂ) * (z - β))) (Icc 0 1)) :
    p z - p β = (z - β) * ∫ t in (0 : ℝ)..1, p1 (β + (t : ℂ) * (z - β)) := by
  have hint : IntervalIntegrable (fun t : ℝ => (z - β) * p1 (β + (t : ℂ) * (z - β))) volume 0 1 :=
    (continuousOn_const.mul hc).intervalIntegrable_of_Icc zero_le_one
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (f := fun s : ℝ => p (β + (s : ℂ) * (z - β))) (f' := fun t : ℝ => (z - β) * p1 (β + (t : ℂ) * (z - β)))
    (fun t ht => hasDerivAt_seg (hp t (by simpa [uIcc_of_le zero_le_one] using ht))) hint
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_one, one_mul, add_sub_cancel] at this
  rw [intervalIntegral.integral_const_mul] at this
  exact this.symm

/-- Second-order Taylor identity with integral remainder along a segment. -/
lemma taylor2_seg {p p1 p2 : ℂ → ℂ} {z β : ℂ}
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt p (p1 (β + t * (z - β))) (β + t * (z - β)))
    (hp1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt p1 (p2 (β + t * (z - β))) (β + t * (z - β)))
    (hc : ContinuousOn (fun t : ℝ => p2 (β + (t : ℂ) * (z - β))) (Icc 0 1)) :
    p z - p β - p1 β * (z - β) =
      (z - β) ^ 2 * ∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) * p2 (β + (t : ℂ) * (z - β)) := by
  set ψ : ℝ → ℂ := fun s => (1 - (s : ℂ)) * ((z - β) * p1 (β + (s : ℂ) * (z - β))) + p (β + (s : ℂ) * (z - β)) with hψ
  set ψ' : ℝ → ℂ := fun t => (z - β) ^ 2 * ((1 - (t : ℂ)) * p2 (β + (t : ℂ) * (z - β))) with hψ'
  have hder : ∀ t ∈ [[(0 : ℝ), 1]], HasDerivAt ψ (ψ' t) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    have h1 := (hasDerivAt_seg (hp1 t ht')).const_mul (z - β)
    have h2 : HasDerivAt (fun s : ℝ => (1 - (s : ℂ))) (-1) t := by
      have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      have := hid.ofReal_comp.const_sub 1
      simpa using this
    have h3 := h2.mul h1
    have h4 := h3.add (hasDerivAt_seg (hp t ht'))
    refine h4.congr_deriv ?_
    simp only [hψ']
    ring
  have hint : IntervalIntegrable ψ' volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    refine continuousOn_const.mul ?_
    exact (Continuous.continuousOn (by fun_prop)).mul hc
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) hder hint
  simp only [hψ, hψ', Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_one, one_mul, sub_self, zero_mul,
    sub_zero, add_sub_cancel] at this
  rw [intervalIntegral.integral_const_mul] at this
  have e : (z - β) ^ 2 * ∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) * p2 (β + (t : ℂ) * (z - β)) =
      p z - (p1 β * (z - β) + p β) := by
    rw [this]
    ring
  rw [e]; ring

/-- The conjugated function `w ↦ conj (f (conj w))` has the conjugated derivative at the conjugated point. -/
lemma hasDerivAt_conj_conj {f : ℂ → ℂ} {z f' : ℂ} (hd : HasDerivAt f f' z) :
    HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ f') (starRingEnd ℂ z) := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hd ⊢
  have h2 := hd.comp_tendsto (Complex.continuous_conj.tendsto (0 : ℂ) |>.mono_right (by simp) : Tendsto (starRingEnd ℂ) (𝓝 0) (𝓝 0))
  rw [Asymptotics.isLittleO_iff] at h2 ⊢
  intro c hc
  filter_upwards [h2 hc] with k hk
  simp only [Function.comp, id] at hk ⊢
  have e : starRingEnd ℂ (f (starRingEnd ℂ (starRingEnd ℂ z + k))) - starRingEnd ℂ (f (starRingEnd ℂ (starRingEnd ℂ z))) -
      k • starRingEnd ℂ f' = starRingEnd ℂ (f (z + starRingEnd ℂ k) - f z - starRingEnd ℂ k • f') := by
    simp [smul_eq_mul]
  rw [e, Complex.norm_conj]
  simpa [Complex.norm_conj] using hk

/-- The derivative of a function is conjugation symmetric if the function is. -/
lemma hasDerivAt_conj_symm {f : ℂ → ℂ} (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) {z f' : ℂ}
    (hd : HasDerivAt f f' z) : HasDerivAt f (starRingEnd ℂ f') (starRingEnd ℂ z) := by
  have h := hasDerivAt_conj_conj hd
  have e : (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) = f := by
    funext w; rw [hsym, Complex.conj_conj]
  rwa [e] at h

/-- Conjugation conjugate of a function analytic at `0` is analytic at `0`. -/
lemma analyticAt_conj_conj {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) 0 := by
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp hf.eventually_analyticAt
  refine DifferentiableOn.analyticAt (s := Metric.ball (0 : ℂ) r) (fun w hw => ?_) (Metric.ball_mem_nhds 0 hr)
  have hw' : starRingEnd ℂ w ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hd := (hb _ hw').differentiableAt
  have := (hasDerivAt_conj_conj hd.hasDerivAt)
  simp only [Complex.conj_conj] at this
  exact this.differentiableAt.differentiableWithinAt

lemma deriv_conj_symm {f : ℂ → ℂ} (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) (z : ℂ) :
    deriv f (starRingEnd ℂ z) = starRingEnd ℂ (deriv f z) := by
  by_cases hd : DifferentiableAt ℂ f z
  · exact (hasDerivAt_conj_symm hsym hd.hasDerivAt).deriv
  · have hd' : ¬ DifferentiableAt ℂ f (starRingEnd ℂ z) := by
      intro h
      apply hd
      have := (hasDerivAt_conj_symm hsym h.hasDerivAt).differentiableAt
      simpa using this
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', map_zero]

end FormalResearch.SignUncertainty.CtChart
