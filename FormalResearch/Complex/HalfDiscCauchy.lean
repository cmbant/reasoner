module

public import Mathlib

/-!
# Cauchy's theorem on the upper half-disc (phase-free)

For `g` continuous on the closed upper half-disc `{‖z‖ ≤ R, 0 ≤ Im z}` and complex differentiable on the open half-disc,
`∫_{-R}^{R} g(t) dt + i ∫_0^π g(R e^{iy}) · R e^{iy} dy = 0`, i.e. the integral over the boundary (diameter and
upper semicircle, counterclockwise) vanishes (`halfDisc_cauchy`).  Mathlib has Cauchy for rectangles, discs and
annuli only.  The proof maps the rectangle `[log ε, log R] × [0, π]` by `exp`, which turns the half-annulus
`{ε ≤ ‖z‖ ≤ R, Im z ≥ 0}` into a rectangle, applies the rectangle theorem to `g(e^s) e^s`, and lets `ε → 0`.
Proved, unconditional; used by `ct:dyadic` Part (3) (P3b) and available to Paper II.
-/

@[expose] public section

open Complex MeasureTheory Set intervalIntegral Filter Topology
open scoped Interval
open scoped Real

namespace FormalResearch.HalfDiscCauchy

/-- The closed upper half-disc of radius `R`. -/
def closedHalfDisc (R : ℝ) : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}

/-- The open upper half-disc of radius `R`. -/
def openHalfDisc (R : ℝ) : Set ℂ := {z | ‖z‖ < R ∧ 0 < z.im}

/-- Substitution `t = e^x` for a continuous complex-valued integrand. -/
lemma subst_exp (h : ℝ → ℂ) {a b : ℝ} (hh : ContinuousOn h (Real.exp '' [[a, b]])) :
    ∫ x in a..b, h (Real.exp x) * ((Real.exp x : ℝ) : ℂ) = ∫ t in Real.exp a..Real.exp b, h t := by
  have := integral_deriv_smul_comp' (a := a) (b := b) (f := Real.exp) (f' := Real.exp) (g := h)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hh
  simp only [Function.comp, Complex.real_smul] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [mul_comm]

lemma exp_re_add_mul_I (x y : ℝ) :
    Complex.exp ((x : ℂ) + y * I) = (Real.exp x : ℝ) * Complex.exp (y * I) := by
  rw [Complex.exp_add, Complex.ofReal_exp]

/-- Cauchy on the half-annulus: the exponential image of the rectangle `[log ε, log R] × [0, π]`. -/
theorem halfAnnulus_identity {g : ℂ → ℂ} {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hc : ContinuousOn g (closedHalfDisc R)) (hd : DifferentiableOn ℂ g (openHalfDisc R)) :
    (∫ t in ε..R, g (t : ℂ)) + (∫ t in ε..R, g (-(t : ℂ))) +
      I * (∫ y in (0 : ℝ)..π, g (R * Complex.exp (y * I)) * (R * Complex.exp (y * I))) -
      I * (∫ y in (0 : ℝ)..π, g (ε * Complex.exp (y * I)) * (ε * Complex.exp (y * I))) = 0 := by
  have hR : 0 < R := hε.trans hεR
  have hlog : Real.log ε < Real.log R := Real.log_lt_log hε hεR
  set G : ℂ → ℂ := fun s => g (Complex.exp s) * Complex.exp s with hG
  -- membership of `exp s`
  have hmem : ∀ s : ℂ, s.re ≤ Real.log R → 0 ≤ s.im → s.im ≤ π → Complex.exp s ∈ closedHalfDisc R := by
    intro s h1 h2 h3
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_exp]
      calc Real.exp s.re ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr h1
        _ = R := Real.exp_log hR
    · rw [Complex.exp_im]
      exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi h2 h3)
  have hmem' : ∀ s : ℂ, s.re < Real.log R → 0 < s.im → s.im < π → Complex.exp s ∈ openHalfDisc R := by
    intro s h1 h2 h3
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_exp]
      calc Real.exp s.re < Real.exp (Real.log R) := Real.exp_lt_exp.mpr h1
        _ = R := Real.exp_log hR
    · rw [Complex.exp_im]
      exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h2 h3)
  have hlog' : Real.exp (Real.log R) = R := Real.exp_log hR
  have hlogε : Real.exp (Real.log ε) = ε := Real.exp_log hε
  have hrect := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn G
    (⟨Real.log ε, 0⟩ : ℂ) ⟨Real.log R, π⟩ ?_ ?_
  · dsimp only at hrect
    -- the four edges
    have hcontR : ∀ t : ℝ, t ∈ Real.exp '' [[Real.log ε, Real.log R]] →
        ContinuousWithinAt (fun t : ℝ => g (t : ℂ)) (Real.exp '' [[Real.log ε, Real.log R]]) t := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := ht
      rw [uIcc_of_le hlog.le] at hx
      have hmemx : ((Real.exp x : ℝ) : ℂ) ∈ closedHalfDisc R := by
        refine ⟨?_, by simp⟩
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc Real.exp x ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hx.2
          _ = R := hlog'
      exact ((hc _ hmemx).comp Complex.continuous_ofReal.continuousWithinAt (fun y hy => by
        obtain ⟨x', hx', rfl⟩ := hy
        rw [uIcc_of_le hlog.le] at hx'
        refine ⟨?_, by simp⟩
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc Real.exp x' ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hx'.2
          _ = R := hlog'))
    have hcontR' : ContinuousOn (fun t : ℝ => g (t : ℂ)) (Real.exp '' [[Real.log ε, Real.log R]]) :=
      fun t ht => hcontR t ht
    have hcontL : ContinuousOn (fun t : ℝ => g (-(t : ℂ))) (Real.exp '' [[Real.log ε, Real.log R]]) := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := ht
      rw [uIcc_of_le hlog.le] at hx
      have hmemx : (-((Real.exp x : ℝ) : ℂ)) ∈ closedHalfDisc R := by
        refine ⟨?_, by simp⟩
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc Real.exp x ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hx.2
          _ = R := hlog'
      exact (ContinuousWithinAt.comp (f := fun t : ℝ => -(t : ℂ)) (hc _ hmemx)
        (Complex.continuous_ofReal.neg.continuousWithinAt) (fun y hy => by
        obtain ⟨x', hx', rfl⟩ := hy
        rw [uIcc_of_le hlog.le] at hx'
        refine ⟨?_, by simp⟩
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc Real.exp x' ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hx'.2
          _ = R := hlog'))
    have e1 : (∫ x : ℝ in Real.log ε..Real.log R, G ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) =
        ∫ t in ε..R, g (t : ℂ) := by
      have := subst_exp (fun t : ℝ => g (t : ℂ)) hcontR'
      rw [hlogε, hlog'] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hG, Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_exp]
    have e2 : (∫ x : ℝ in Real.log ε..Real.log R, G ((x : ℂ) + ((π : ℝ) : ℂ) * I)) =
        -∫ t in ε..R, g (-(t : ℂ)) := by
      have := subst_exp (fun t : ℝ => g (-(t : ℂ))) hcontL
      rw [hlogε, hlog'] at this
      rw [← this, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hG, Complex.exp_add, Complex.exp_pi_mul_I, Complex.ofReal_exp]
      ring_nf
    have e3 : (∫ y : ℝ in (0 : ℝ)..π, G (((Real.log R : ℝ) : ℂ) + (y : ℂ) * I)) =
        ∫ y in (0 : ℝ)..π, g (R * Complex.exp (y * I)) * (R * Complex.exp (y * I)) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [hG]
      rw [exp_re_add_mul_I, hlog']
    have e4 : (∫ y : ℝ in (0 : ℝ)..π, G (((Real.log ε : ℝ) : ℂ) + (y : ℂ) * I)) =
        ∫ y in (0 : ℝ)..π, g (ε * Complex.exp (y * I)) * (ε * Complex.exp (y * I)) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [hG]
      rw [exp_re_add_mul_I, hlogε]
    simp only [smul_eq_mul] at hrect
    rw [e1, e2, e3, e4] at hrect
    linear_combination hrect
  · -- continuity on the closed rectangle
    have hmaps : MapsTo Complex.exp (([[(⟨Real.log ε, 0⟩ : ℂ).re, (⟨Real.log R, π⟩ : ℂ).re]]) ×ℂ
        ([[(⟨Real.log ε, 0⟩ : ℂ).im, (⟨Real.log R, π⟩ : ℂ).im]])) (closedHalfDisc R) := by
      intro s hs
      rw [Complex.mem_reProdIm] at hs
      obtain ⟨hs1, hs2⟩ := hs
      dsimp only at hs1 hs2
      rw [uIcc_of_le hlog.le] at hs1
      rw [uIcc_of_le Real.pi_pos.le] at hs2
      exact hmem s hs1.2 hs2.1 hs2.2
    rw [hG]
    exact (hc.comp Complex.continuous_exp.continuousOn hmaps).mul Complex.continuous_exp.continuousOn
  · have hmaps : MapsTo Complex.exp
        (Ioo (min (⟨Real.log ε, 0⟩ : ℂ).re (⟨Real.log R, π⟩ : ℂ).re) (max (⟨Real.log ε, 0⟩ : ℂ).re (⟨Real.log R, π⟩ : ℂ).re) ×ℂ
          Ioo (min (⟨Real.log ε, 0⟩ : ℂ).im (⟨Real.log R, π⟩ : ℂ).im) (max (⟨Real.log ε, 0⟩ : ℂ).im (⟨Real.log R, π⟩ : ℂ).im))
        (openHalfDisc R) := by
      intro s hs
      rw [Complex.mem_reProdIm] at hs
      obtain ⟨hs1, hs2⟩ := hs
      dsimp only at hs1 hs2
      rw [min_eq_left hlog.le, max_eq_right hlog.le] at hs1
      rw [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hs2
      exact hmem' s hs1.2 hs2.1 hs2.2
    have hde : DifferentiableOn ℂ Complex.exp Set.univ := fun s _ =>
      (Complex.hasDerivAt_exp s).differentiableAt.differentiableWithinAt
    rw [hG]
    exact (hd.comp (hde.mono (subset_univ _)) hmaps).mul (hde.mono (subset_univ _))

lemma closedHalfDisc_compact (R : ℝ) : IsCompact (closedHalfDisc R) := by
  have : closedHalfDisc R = Metric.closedBall (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im} := by
    ext z; simp [closedHalfDisc]
  rw [this]
  exact (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const Complex.continuous_im)

lemma ofReal_mem_closedHalfDisc {R t : ℝ} (ht : t ∈ Icc (-R) R) : (t : ℂ) ∈ closedHalfDisc R := by
  refine ⟨?_, by simp⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨ht.1, ht.2⟩

/-- **Cauchy's theorem on the upper half-disc.** For `g` continuous on the closed upper half-disc of radius `R` and
complex differentiable on the open one, `∫_{-R}^{R} g(t) dt + i ∫_0^π g(R e^{iy}) R e^{iy} dy = 0`. -/
theorem halfDisc_cauchy {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn g (closedHalfDisc R)) (hd : DifferentiableOn ℂ g (openHalfDisc R)) :
    (∫ t in (-R)..R, g (t : ℂ)) +
      I * (∫ y in (0 : ℝ)..π, g (R * Complex.exp (y * I)) * (R * Complex.exp (y * I))) = 0 := by
  obtain ⟨M, hM⟩ := (closedHalfDisc_compact R).exists_bound_of_continuousOn hc
  set C : ℂ := ∫ y in (0 : ℝ)..π, g (R * Complex.exp (y * I)) * (R * Complex.exp (y * I)) with hCdef
  -- continuity of the real-line restrictions
  have hcl : ContinuousOn (fun t : ℝ => g (t : ℂ)) (Icc (-R) R) :=
    hc.comp Complex.continuous_ofReal.continuousOn (fun t ht => ofReal_mem_closedHalfDisc ht)
  have hcr : ContinuousOn (fun t : ℝ => g (-(t : ℂ))) (Icc 0 R) :=
    hc.comp (Complex.continuous_ofReal.neg.continuousOn) (fun t ht => by
      refine ⟨?_, by simp⟩
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2)
  have hcr' : ContinuousOn (fun t : ℝ => g (t : ℂ)) (Icc 0 R) :=
    hcl.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
  -- the two real-line integrals in the limit
  have hA : Tendsto (fun ε : ℝ => ∫ t in ε..R, g (t : ℂ)) (𝓝[Ioo 0 R] 0) (𝓝 (∫ t in (0 : ℝ)..R, g (t : ℂ))) := by
    have hint : IntegrableOn (fun t : ℝ => g (t : ℂ)) (uIcc 0 R) := by
      rw [uIcc_of_le hR.le]; exact hcr'.integrableOn_Icc
    have := (continuousOn_primitive_interval_left hint) 0 (by simp [hR.le])
    exact (this.mono (fun t ht => by rw [uIcc_of_le hR.le]; exact ⟨ht.1.le, ht.2.le⟩)).tendsto
  have hB : Tendsto (fun ε : ℝ => ∫ t in ε..R, g (-(t : ℂ))) (𝓝[Ioo 0 R] 0) (𝓝 (∫ t in (0 : ℝ)..R, g (-(t : ℂ)))) := by
    have hint : IntegrableOn (fun t : ℝ => g (-(t : ℂ))) (uIcc 0 R) := by
      rw [uIcc_of_le hR.le]; exact hcr.integrableOn_Icc
    have := (continuousOn_primitive_interval_left hint) 0 (by simp [hR.le])
    exact (this.mono (fun t ht => by rw [uIcc_of_le hR.le]; exact ⟨ht.1.le, ht.2.le⟩)).tendsto
  -- the small arc vanishes
  have hD : Tendsto (fun ε : ℝ => ∫ y in (0 : ℝ)..π, g (ε * Complex.exp (y * I)) * (ε * Complex.exp (y * I)))
      (𝓝[Ioo 0 R] 0) (𝓝 0) := by
    have hbound : ∀ ε ∈ Ioo 0 R, ‖∫ y in (0 : ℝ)..π, g (ε * Complex.exp (y * I)) * (ε * Complex.exp (y * I))‖ ≤
        M * ε * π := by
      intro ε hε
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π) (C := M * ε)
        (f := fun y : ℝ => g (ε * Complex.exp (y * I)) * (ε * Complex.exp (y * I))) (fun y hy => by
          rw [uIoc_of_le Real.pi_pos.le] at hy
          have hmem : (ε : ℂ) * Complex.exp (y * I) ∈ closedHalfDisc R := by
            refine ⟨?_, ?_⟩
            · rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
                abs_of_pos hε.1]; exact hε.2.le
            · have : ((ε : ℂ) * Complex.exp (y * I)).im = ε * Real.sin y := by
                rw [Complex.exp_mul_I]; simp [Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
              rw [this]
              exact mul_nonneg hε.1.le (Real.sin_nonneg_of_nonneg_of_le_pi hy.1.le hy.2)
          rw [norm_mul]
          have h1 := hM _ hmem
          have h2 : ‖(ε : ℂ) * Complex.exp (y * I)‖ = ε := by
            rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
              abs_of_pos hε.1]
          rw [h2]
          exact mul_le_mul_of_nonneg_right h1 hε.1.le)
      rw [sub_zero, abs_of_pos Real.pi_pos] at this
      linarith
    refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun ε hε => (hbound ε hε).trans (le_of_eq rfl)) ?_
    have : Tendsto (fun ε : ℝ => M * ε * π) (𝓝 0) (𝓝 (M * 0 * π)) := by
      exact ((continuous_const.mul continuous_id).mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  -- identity for each `ε`
  have hid : ∀ᶠ ε : ℝ in 𝓝[Ioo 0 R] 0,
      (∫ t in ε..R, g (t : ℂ)) + (∫ t in ε..R, g (-(t : ℂ))) + I * C -
        I * (∫ y in (0 : ℝ)..π, g (ε * Complex.exp (y * I)) * (ε * Complex.exp (y * I))) = 0 :=
    eventually_nhdsWithin_of_forall fun ε hε => halfAnnulus_identity hε.1 hε.2 hc hd
  have hlim : Tendsto (fun ε : ℝ => (∫ t in ε..R, g (t : ℂ)) + (∫ t in ε..R, g (-(t : ℂ))) + I * C -
        I * (∫ y in (0 : ℝ)..π, g (ε * Complex.exp (y * I)) * (ε * Complex.exp (y * I))))
      (𝓝[Ioo 0 R] 0) (𝓝 ((∫ t in (0 : ℝ)..R, g (t : ℂ)) + (∫ t in (0 : ℝ)..R, g (-(t : ℂ))) + I * C - I * 0)) :=
    ((hA.add hB).add tendsto_const_nhds).sub (hD.const_mul I)
  have : (𝓝[Ioo 0 R] (0 : ℝ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hR.ne]; simp [hR.le]
  have hz : Tendsto (fun ε : ℝ => (∫ t in ε..R, g (t : ℂ)) + (∫ t in ε..R, g (-(t : ℂ))) + I * C -
        I * (∫ y in (0 : ℝ)..π, g (ε * Complex.exp (y * I)) * (ε * Complex.exp (y * I))))
      (𝓝[Ioo 0 R] 0) (𝓝 0) := tendsto_const_nhds.congr' (hid.mono fun ε h => h.symm)
  have heq := tendsto_nhds_unique hlim hz
  -- reassemble `∫_{-R}^R`
  have hsplit : (∫ t in (-R)..R, g (t : ℂ)) =
      (∫ t in (0 : ℝ)..R, g (-(t : ℂ))) + ∫ t in (0 : ℝ)..R, g (t : ℂ) := by
    have h1 : (∫ t in (0 : ℝ)..R, g (-(t : ℂ))) = ∫ t in (-R)..0, g (t : ℂ) := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := R) (fun t : ℝ => g (t : ℂ))
      simpa using this
    rw [h1, intervalIntegral.integral_add_adjacent_intervals]
    · exact (hcl.mono (fun t ht => by rw [uIcc_of_le (by linarith)] at ht; exact ⟨ht.1, by linarith [ht.2]⟩)).intervalIntegrable
    · exact (hcl.mono (fun t ht => by rw [uIcc_of_le hR.le] at ht; exact ⟨by linarith [ht.1], ht.2⟩)).intervalIntegrable
  rw [hsplit]
  rw [mul_zero, sub_zero] at heq
  rw [← heq]; ring

/-- info: 'FormalResearch.HalfDiscCauchy.halfDisc_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.HalfDiscCauchy.halfDisc_cauchy

end FormalResearch.HalfDiscCauchy
