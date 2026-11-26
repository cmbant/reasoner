module

public import Mathlib
public import FormalResearch.Complex.HalfDiscCauchy

/-!
# Cauchy integral formula and Poisson representation on the upper half-disc (phase-free)

Built on `halfDisc_cauchy`.  For `A > 0`, `z` in the open upper half-disc `D_+` of radius `A`, and `G` continuous on
`closure D_+` and holomorphic in `D_+`:

* `hdBoundary_inv_sub`: `∮_{∂D_+} dζ/(ζ - z) = 2πi` (from Mathlib's circle integral and `halfDisc_cauchy` on the lower
  half-disc, reflected);
* `halfDisc_cauchy_formula`: `2πi G(z) = ∮_{∂D_+} G(ζ)/(ζ - z) dζ` (apply `halfDisc_cauchy` to `dslope G z`);
* `halfDisc_poisson`: the Poisson representation
  `G(z) = ∫_{-A}^{A} hdDiam A z t · G(t) dt + ∫_0^π hdArc A z θ · G(A e^{iθ}) dθ`
  with the explicit kernels of `ct:Pdiam`, `ct:Parc`, from the Cauchy formula at `z` and at the three image points
  `z̄`, `A²/z̄`, `A²/z` outside `closure D_+` (where the Cauchy integral vanishes).

Proved, unconditional.  Used by `ct:dyadic` Part (2) (P2a) and by Paper II FIVE-L.
-/

@[expose] public section

open Complex MeasureTheory Set intervalIntegral Filter Topology
open scoped Real Interval

namespace FormalResearch.HalfDiscCauchy

/-- The counterclockwise boundary functional of the upper half-disc: diameter from `-A` to `A`, then the upper
semicircle `A e^{iy}`, `y ∈ [0, π]` (`dζ = i A e^{iy} dy`). -/
noncomputable def hdBoundary (A : ℝ) (g : ℂ → ℂ) : ℂ :=
  (∫ t in (-A)..A, g (t : ℂ)) +
    I * ∫ y in (0 : ℝ)..π, g (A * Complex.exp (y * I)) * (A * Complex.exp (y * I))

lemma hdBoundary_eq_zero {g : ℂ → ℂ} {A : ℝ} (hA : 0 < A) (hc : ContinuousOn g (closedHalfDisc A))
    (hd : DifferentiableOn ℂ g (openHalfDisc A)) : hdBoundary A g = 0 :=
  halfDisc_cauchy hA hc hd

lemma norm_arc (A y : ℝ) (hA : 0 < A) : ‖(A : ℂ) * Complex.exp (y * I)‖ = A := by
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
    abs_of_pos hA]

lemma arc_mem_closedHalfDisc {A y : ℝ} (hA : 0 < A) (hy : y ∈ Icc 0 π) :
    (A : ℂ) * Complex.exp (y * I) ∈ closedHalfDisc A := by
  refine ⟨(norm_arc A y hA).le, ?_⟩
  have : ((A : ℂ) * Complex.exp (y * I)).im = A * Real.sin y := by
    rw [Complex.exp_mul_I]; simp [Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [this]
  exact mul_nonneg hA.le (Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2)

lemma ofReal_mem_closedHalfDisc' {A t : ℝ} (ht : t ∈ Icc (-A) A) : (t : ℂ) ∈ closedHalfDisc A :=
  ofReal_mem_closedHalfDisc ht

/-- Continuity of `g` along the two boundary parametrisations (diameter and upper semicircle). -/
def BdCont (A : ℝ) (g : ℂ → ℂ) : Prop :=
  ContinuousOn (fun t : ℝ => g (t : ℂ)) (Icc (-A) A) ∧
    ContinuousOn (fun y : ℝ => g (A * Complex.exp (y * I))) (Icc 0 π)

lemma BdCont.of_closed {A : ℝ} (hA : 0 < A) {g : ℂ → ℂ} (hg : ContinuousOn g (closedHalfDisc A)) :
    BdCont A g :=
  ⟨hg.comp Complex.continuous_ofReal.continuousOn (fun t ht => ofReal_mem_closedHalfDisc ht),
    hg.comp (by fun_prop) (fun y hy => arc_mem_closedHalfDisc hA hy)⟩

lemma BdCont.add {A : ℝ} {g₁ g₂ : ℂ → ℂ} (h₁ : BdCont A g₁) (h₂ : BdCont A g₂) :
    BdCont A (fun ζ => g₁ ζ + g₂ ζ) := ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

lemma BdCont.const_mul {A : ℝ} (a : ℂ) {g : ℂ → ℂ} (h : BdCont A g) : BdCont A (fun ζ => a * g ζ) :=
  ⟨continuousOn_const.mul h.1, continuousOn_const.mul h.2⟩

lemma BdCont.mul {A : ℝ} {g₁ g₂ : ℂ → ℂ} (h₁ : BdCont A g₁) (h₂ : BdCont A g₂) :
    BdCont A (fun ζ => g₁ ζ * g₂ ζ) := ⟨h₁.1.mul h₂.1, h₁.2.mul h₂.2⟩

/-- The boundary functional only sees the boundary. -/
lemma hdBoundary_congr {A : ℝ} (hA : 0 < A) {g₁ g₂ : ℂ → ℂ} (h : ∀ ζ ∈ closedHalfDisc A, g₁ ζ = g₂ ζ) :
    hdBoundary A g₁ = hdBoundary A g₂ := by
  have e1 : (∫ t in (-A)..A, g₁ (t : ℂ)) = ∫ t in (-A)..A, g₂ (t : ℂ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by linarith)] at ht
    exact h _ (ofReal_mem_closedHalfDisc ht)
  have e2 : (∫ y in (0 : ℝ)..π, g₁ (A * Complex.exp (y * I)) * (A * Complex.exp (y * I))) =
      ∫ y in (0 : ℝ)..π, g₂ (A * Complex.exp (y * I)) * (A * Complex.exp (y * I)) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le Real.pi_pos.le] at hy
    simp only [h _ (arc_mem_closedHalfDisc hA hy)]
  unfold hdBoundary
  rw [e1, e2]

lemma hdBoundary_add {A : ℝ} (hA : 0 < A) {g₁ g₂ : ℂ → ℂ} (h₁ : BdCont A g₁) (h₂ : BdCont A g₂) :
    hdBoundary A (fun ζ => g₁ ζ + g₂ ζ) = hdBoundary A g₁ + hdBoundary A g₂ := by
  have i1 : ∀ g : ℂ → ℂ, BdCont A g →
      IntervalIntegrable (fun t : ℝ => g (t : ℂ)) volume (-A) A := fun g hg => by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    exact hg.1
  have i2 : ∀ g : ℂ → ℂ, BdCont A g →
      IntervalIntegrable (fun y : ℝ => g (A * Complex.exp (y * I)) * (A * Complex.exp (y * I))) volume 0 π := fun g hg => by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le Real.pi_pos.le]
    exact hg.2.mul (by fun_prop)
  unfold hdBoundary
  beta_reduce
  rw [intervalIntegral.integral_add (i1 _ h₁) (i1 _ h₂),
    show (fun y : ℝ => (g₁ (A * Complex.exp (y * I)) + g₂ (A * Complex.exp (y * I))) * (A * Complex.exp (y * I))) =
      fun y : ℝ => g₁ (A * Complex.exp (y * I)) * (A * Complex.exp (y * I)) +
        g₂ (A * Complex.exp (y * I)) * (A * Complex.exp (y * I)) from funext fun y => by ring,
    intervalIntegral.integral_add (i2 _ h₁) (i2 _ h₂)]
  ring

lemma hdBoundary_const_mul {A : ℝ} (a : ℂ) (g : ℂ → ℂ) :
    hdBoundary A (fun ζ => a * g ζ) = a * hdBoundary A g := by
  unfold hdBoundary
  beta_reduce
  rw [intervalIntegral.integral_const_mul]
  have : (fun y : ℝ => a * g (A * Complex.exp (y * I)) * (A * Complex.exp (y * I))) =
      fun y : ℝ => a * (g (A * Complex.exp (y * I)) * (A * Complex.exp (y * I))) :=
    funext fun y => by ring
  rw [this, intervalIntegral.integral_const_mul]
  ring

/-- **Winding number** of the boundary of `D_+` about an interior point: `∮_{∂D_+} dζ/(ζ - z) = 2πi`. -/
theorem hdBoundary_inv_sub {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : z ∈ openHalfDisc A) :
    hdBoundary A (fun ζ => (ζ - z)⁻¹) = 2 * π * I := by
  have hzA : ‖z‖ < A := hz.1
  have hne : ∀ θ : ℝ, (A : ℂ) * Complex.exp (θ * I) - z ≠ 0 := by
    intro θ h
    have : ‖(A : ℂ) * Complex.exp (θ * I)‖ = ‖z‖ := by rw [sub_eq_zero.mp h]
    rw [norm_arc A θ hA] at this
    linarith
  set F : ℝ → ℂ := fun θ => ((A : ℂ) * Complex.exp (θ * I) * I) * ((A : ℂ) * Complex.exp (θ * I) - z)⁻¹ with hF
  have hFc : Continuous F := by
    simp only [hF]
    refine Continuous.mul (by fun_prop) (Continuous.inv₀ (by fun_prop) hne)
  have hcirc : ∫ θ in (0 : ℝ)..(2 * π), F θ = 2 * π * I := by
    have := circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (R := A) (w := z)
      (by rw [mem_ball_zero_iff]; exact hzA)
    rw [← this]
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hF, deriv_circleMap, circleMap, zero_add, smul_eq_mul]
  have hsplit : ∫ θ in (0 : ℝ)..(2 * π), F θ =
      (∫ θ in (0 : ℝ)..π, F θ) + ∫ θ in (0 : ℝ)..π, F (θ + π) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable 0 π)
      (hFc.intervalIntegrable π (2 * π))]
    congr 1
    rw [intervalIntegral.integral_comp_add_right F π]
    simp only [zero_add]
    congr 1; ring
  -- the upper arc
  have hU : ∫ θ in (0 : ℝ)..π, F θ =
      I * ∫ y in (0 : ℝ)..π, (A * Complex.exp (y * I) - z)⁻¹ * (A * Complex.exp (y * I)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hF]; ring
  -- the lower arc equals the diameter integral
  set g : ℂ → ℂ := fun w => (-w - z)⁻¹ with hg
  have hzc : ∀ w ∈ closedHalfDisc A, -w - z ≠ 0 := by
    intro w hw h
    have : w = -z := by linear_combination -h
    have him := hw.2
    rw [this] at him
    simp only [Complex.neg_im] at him
    linarith [hz.2]
  have hgc : ContinuousOn g (closedHalfDisc A) := fun w hw =>
    ((continuousAt_id.neg.sub continuousAt_const).inv₀ (hzc w hw)).continuousWithinAt
  have hgd : DifferentiableOn ℂ g (openHalfDisc A) := fun w hw => by
    have h1 : DifferentiableAt ℂ (fun w : ℂ => -w - z) w := differentiableAt_id.neg.sub_const z
    exact (h1.inv (hzc w ⟨hw.1.le, hw.2.le⟩)).differentiableWithinAt
  have hg0 := hdBoundary_eq_zero hA hgc hgd
  have hD0 : ∫ t in (-A)..A, ((t : ℂ) - z)⁻¹ = ∫ t in (-A)..A, g (t : ℂ) := by
    have := intervalIntegral.integral_comp_neg (a := -A) (b := A) (fun t : ℝ => ((t : ℂ) - z)⁻¹)
    simp only [neg_neg] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hg]; push_cast; rfl
  have hL : ∫ θ in (0 : ℝ)..π, F (θ + π) = ∫ t in (-A)..A, ((t : ℂ) - z)⁻¹ := by
    rw [hD0]
    have h1 : (∫ t in (-A)..A, g (t : ℂ)) =
        -(I * ∫ y in (0 : ℝ)..π, g (A * Complex.exp (y * I)) * (A * Complex.exp (y * I))) := by
      have := hg0
      unfold hdBoundary at this
      linear_combination this
    rw [h1, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hF, hg]
    have : Complex.exp (((θ + π : ℝ) : ℂ) * I) = -Complex.exp (θ * I) := by
      push_cast; rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring
    rw [this]
    ring
  unfold hdBoundary
  rw [← hcirc, hsplit, hU, hL, add_comm]

/-- **Cauchy integral formula on the half-disc:** `∮_{∂D_+} G(ζ)/(ζ - z) dζ = 2πi G(z)` for `G` continuous on
`closure D_+` and holomorphic in `D_+`, `z ∈ D_+`. -/
theorem hdBoundary_cauchy_formula {A : ℝ} (hA : 0 < A) {G : ℂ → ℂ} {z : ℂ} (hz : z ∈ openHalfDisc A)
    (hc : ContinuousOn G (closedHalfDisc A)) (hd : DifferentiableOn ℂ G (openHalfDisc A)) :
    hdBoundary A (fun ζ => G ζ * (ζ - z)⁻¹) = 2 * π * I * G z := by
  have hzin : z ∈ closedHalfDisc A := ⟨hz.1.le, hz.2.le⟩
  have hnhds : closedHalfDisc A ∈ 𝓝 z := by
    have hopen : IsOpen (openHalfDisc A) := by
      have : openHalfDisc A = Metric.ball (0 : ℂ) A ∩ {w : ℂ | 0 < w.im} := by
        ext w; simp [openHalfDisc]
      rw [this]
      exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
    exact Filter.mem_of_superset (hopen.mem_nhds hz) (fun w hw => ⟨hw.1.le, hw.2.le⟩)
  have hnhds' : openHalfDisc A ∈ 𝓝 z := by
    have hopen : IsOpen (openHalfDisc A) := by
      have : openHalfDisc A = Metric.ball (0 : ℂ) A ∩ {w : ℂ | 0 < w.im} := by
        ext w; simp [openHalfDisc]
      rw [this]
      exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
    exact hopen.mem_nhds hz
  have hdsc : ContinuousOn (dslope G z) (closedHalfDisc A) :=
    (continuousOn_dslope hnhds).mpr ⟨hc, (hd.differentiableAt hnhds')⟩
  have hdsd : DifferentiableOn ℂ (dslope G z) (openHalfDisc A) :=
    (differentiableOn_dslope hnhds').mpr hd
  have h0 := hdBoundary_eq_zero hA hdsc hdsd
  -- boundary points differ from `z`
  have hbd : ∀ ζ ∈ closedHalfDisc A, ζ ≠ z → dslope G z ζ = G ζ * (ζ - z)⁻¹ + (-G z) * (ζ - z)⁻¹ := by
    intro ζ _ hζ
    rw [dslope_of_ne _ hζ, slope_def_field]
    have : ζ - z ≠ 0 := sub_ne_zero.mpr hζ
    field_simp
    ring
  have hinvBd : BdCont A (fun ζ => (ζ - z)⁻¹) := by
    refine ⟨?_, ?_⟩
    · refine ContinuousOn.inv₀ (by fun_prop) (fun t _ h => ?_)
      have : (t : ℂ) = z := sub_eq_zero.mp h
      have := congrArg Complex.im this
      simp at this; linarith [hz.2]
    · refine ContinuousOn.inv₀ (by fun_prop) (fun y _ h => ?_)
      have h' := sub_eq_zero.mp h
      have : ‖(A : ℂ) * Complex.exp (y * I)‖ = ‖z‖ := by rw [h']
      rw [norm_arc A y hA] at this
      linarith [hz.1]
  have hGBd : BdCont A G := BdCont.of_closed hA hc
  have hmulBd : BdCont A (fun ζ => G ζ * (ζ - z)⁻¹) := hGBd.mul hinvBd
  have hcongr : hdBoundary A (dslope G z) =
      hdBoundary A (fun ζ => G ζ * (ζ - z)⁻¹ + (-G z) * (ζ - z)⁻¹) := by
    -- agreement on the boundary only (at `ζ = z`, an interior point, the two sides may differ)
    have e1 : (∫ t in (-A)..A, dslope G z (t : ℂ)) =
        ∫ t in (-A)..A, (G (t : ℂ) * ((t : ℂ) - z)⁻¹ + (-G z) * ((t : ℂ) - z)⁻¹) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (by linarith)] at ht
      have hne : (t : ℂ) ≠ z := fun h => by
        have := congrArg Complex.im h; simp at this; linarith [hz.2]
      exact hbd _ (ofReal_mem_closedHalfDisc ht) hne
    have e2 : (∫ y in (0 : ℝ)..π, dslope G z (A * Complex.exp (y * I)) * (A * Complex.exp (y * I))) =
        ∫ y in (0 : ℝ)..π, (G (A * Complex.exp (y * I)) * ((A : ℂ) * Complex.exp (y * I) - z)⁻¹ +
          (-G z) * ((A : ℂ) * Complex.exp (y * I) - z)⁻¹) * (A * Complex.exp (y * I)) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le Real.pi_pos.le] at hy
      have hne : (A : ℂ) * Complex.exp (y * I) ≠ z := fun h => by
        have : ‖(A : ℂ) * Complex.exp (y * I)‖ = ‖z‖ := by rw [h]
        rw [norm_arc A y hA] at this; linarith [hz.1]
      simp only [hbd _ (arc_mem_closedHalfDisc hA hy) hne]
    unfold hdBoundary
    rw [e1, e2]
  rw [hcongr, hdBoundary_add hA hmulBd (hinvBd.const_mul (-G z)), hdBoundary_const_mul,
    hdBoundary_inv_sub hA hz] at h0
  linear_combination h0

/-! ### The explicit kernels and the image-point identity -/

/-- Poisson density of `D_+` on the diameter (`ct:Pdiam`). -/
noncomputable def hdDiam (A : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  z.im / π * ((A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2)) /
    (Complex.normSq (z - t) * Complex.normSq (((A : ℂ) ^ 2) - t * z))

/-- `A ·` Poisson density of `D_+` on the arc `A e^{iθ}` (`ct:Parc`). -/
noncomputable def hdArc (A : ℝ) (z : ℂ) (θ : ℝ) : ℝ :=
  2 / π * (A * z.im * (A ^ 2 - Complex.normSq z) * Real.sin θ) /
    (Complex.normSq (z - A * Complex.exp (θ * I)) * Complex.normSq (z - A * Complex.exp (-(θ : ℂ) * I)))

lemma diam_alg (s : ℂ) (t z zb : ℂ) (hz : z ≠ 0) (hzb : zb ≠ 0) (h1 : t - z ≠ 0) (h2 : t - zb ≠ 0)
    (h3 : t * zb - s ≠ 0) (h4 : t * z - s ≠ 0) :
    1 / (t - z) - 1 / (t - zb) - 1 / (t - s / zb) + 1 / (t - s / z) =
      (z - zb) * (1 / ((t - z) * (t - zb)) - s / ((t * z - s) * (t * zb - s))) := by
  have h5 : t - s / zb ≠ 0 := by
    intro h; apply h3; field_simp at h; linear_combination h
  have h6 : t - s / z ≠ 0 := by
    intro h; apply h4; field_simp at h; linear_combination h
  field_simp
  ring

lemma arc_alg2 (A e z zb : ℂ) (hA : A ≠ 0) (he : e ≠ 0) (hz : z ≠ 0) (hzb : zb ≠ 0)
    (h1 : A * e - z ≠ 0) (h2 : A * e - zb ≠ 0) (h3 : A * e * zb - A ^ 2 ≠ 0) (h4 : A * e * z - A ^ 2 ≠ 0)
    (h5 : z - A * e⁻¹ ≠ 0) (h6 : zb - A * e⁻¹ ≠ 0) (h7 : z - A * e ≠ 0) (h8 : zb - A * e ≠ 0) :
    (A * e) * (1 / (A * e - z) - 1 / (A * e - zb) - 1 / (A * e - A ^ 2 / zb) + 1 / (A * e - A ^ 2 / z)) =
      -(A * (z - zb) * (A ^ 2 - z * zb) * (e - e⁻¹)) /
        ((z - A * e) * (zb - A * e⁻¹) * (z - A * e⁻¹) * (zb - A * e)) := by
  have h9 : A * e - A ^ 2 / zb ≠ 0 := by
    intro h; apply h3; field_simp at h; linear_combination h
  have h10 : A * e - A ^ 2 / z ≠ 0 := by
    intro h; apply h4; field_simp at h; linear_combination h
  have h5' : e * z - A ≠ 0 := by
    intro h; apply h5; field_simp; linear_combination h
  have h6' : e * zb - A ≠ 0 := by
    intro h; apply h6; field_simp; linear_combination h
  field_simp
  ring

lemma sin_cast (θ : ℝ) :
    ((Real.sin θ : ℝ) : ℂ) = (Complex.exp (θ * I) - (Complex.exp (θ * I))⁻¹) / (2 * I) := by
  rw [Complex.ofReal_sin, Complex.sin, ← Complex.exp_neg]
  rw [show (-(θ : ℂ) * I) = -((θ : ℂ) * I) by ring, Complex.exp_neg]
  field_simp
  have hI : I ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [hI]; ring

/-- The image-point kernel `1/(ζ-z) - 1/(ζ-z̄) - 1/(ζ-A²/z̄) + 1/(ζ-A²/z)`. -/
noncomputable def imgK (A : ℝ) (z ζ : ℂ) : ℂ :=
  (ζ - z)⁻¹ - (ζ - (starRingEnd ℂ) z)⁻¹ - (ζ - (A : ℂ) ^ 2 / (starRingEnd ℂ) z)⁻¹ +
    (ζ - (A : ℂ) ^ 2 / z)⁻¹

lemma normSq_cast_sub (w : ℂ) : ((Complex.normSq w : ℝ) : ℂ) = w * (starRingEnd ℂ) w :=
  (Complex.mul_conj w).symm

lemma ne_zero_of_mem {A : ℝ} {z : ℂ} (hz : z ∈ openHalfDisc A) : z ≠ 0 := fun h => by
  have := hz.2; rw [h] at this; simp at this

/-- On the diameter, `K(t) = 2πi · hdDiam`. -/
lemma imgK_diam {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : z ∈ openHalfDisc A) (t : ℝ) :
    imgK A z (t : ℂ) = 2 * π * I * (hdDiam A z t : ℂ) := by
  have hz0 := ne_zero_of_mem hz
  have hzb0 : (starRingEnd ℂ) z ≠ 0 := by simpa using hz0
  have him : 0 < z.im := hz.2
  have h1 : (t : ℂ) - z ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have h2 : (t : ℂ) - (starRingEnd ℂ) z ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hzA : ‖z‖ < A := hz.1
  have h3 : (t : ℂ) * (starRingEnd ℂ) z - (A : ℂ) ^ 2 ≠ 0 := fun h => by
    rw [show ((A : ℂ) ^ 2) = ((A ^ 2 : ℝ) : ℂ) by push_cast; ring] at h
    have hn := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.zero_im, Complex.zero_re] at hn hr
    -- `t * conj z = A²` forces `t * Im z = 0`, hence `t = 0`, hence `A² = 0`
    have ht : t = 0 := by
      have : t * z.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · linarith
    subst ht
    have : (A : ℝ) ^ 2 = 0 := by linarith
    nlinarith
  have h4 : (t : ℂ) * z - (A : ℂ) ^ 2 ≠ 0 := fun h => by
    rw [show ((A : ℂ) ^ 2) = ((A ^ 2 : ℝ) : ℂ) by push_cast; ring] at h
    have hn := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_im, Complex.zero_re] at hn hr
    have ht : t = 0 := by
      have : t * z.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · linarith
    subst ht
    have : (A : ℝ) ^ 2 = 0 := by linarith
    nlinarith
  unfold imgK
  simp only [← one_div]
  rw [diam_alg ((A : ℂ) ^ 2) t z ((starRingEnd ℂ) z) hz0 hzb0 h1 h2 h3 h4]
  -- identify the right-hand side with the real kernel
  have hN1 : ((Complex.normSq (z - t) : ℝ) : ℂ) = ((t : ℂ) - z) * ((t : ℂ) - (starRingEnd ℂ) z) := by
    rw [normSq_cast_sub]; simp only [map_sub, Complex.conj_ofReal]; ring
  have hN2 : ((Complex.normSq (((A : ℂ) ^ 2) - t * z) : ℝ) : ℂ) =
      ((t : ℂ) * z - (A : ℂ) ^ 2) * ((t : ℂ) * (starRingEnd ℂ) z - (A : ℂ) ^ 2) := by
    rw [normSq_cast_sub]; simp only [map_sub, map_mul, map_pow, Complex.conj_ofReal]; ring
  have hn : ((Complex.normSq z : ℝ) : ℂ) = z * (starRingEnd ℂ) z := normSq_cast_sub z
  have hsub : z - (starRingEnd ℂ) z = 2 * (z.im : ℂ) * I := by
    rw [Complex.sub_conj]; push_cast; ring
  have hN1' : Complex.normSq (z - t) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; intro h; apply h1; rw [← neg_sub, h]; simp
  have hN2' : Complex.normSq (((A : ℂ) ^ 2) - t * z) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; intro h; apply h4; rw [← neg_sub, h]; simp
  have hid := (show hdDiam A z t = z.im / π * (1 / Complex.normSq (z - t) -
      A ^ 2 / Complex.normSq (((A : ℂ) ^ 2) - t * z)) from by
    have hid := (show Complex.normSq (((A : ℂ) ^ 2) - t * z) =
      A ^ 2 * Complex.normSq (z - t) + (A ^ 2 - t ^ 2) * (A ^ 2 - Complex.normSq z) from by
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, pow_two]
        ring)
    have hX : (A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2) =
        Complex.normSq (((A : ℂ) ^ 2) - t * z) - A ^ 2 * Complex.normSq (z - t) := by linarith
    unfold hdDiam
    rw [hX]
    generalize Complex.normSq (((A : ℂ) ^ 2) - t * z) = N at *
    generalize Complex.normSq (z - t) = M at *
    field_simp)
  rw [hid]
  push_cast
  rw [hN1, hN2, hsub]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1' : ((t : ℂ) - z) * ((t : ℂ) - (starRingEnd ℂ) z) ≠ 0 := mul_ne_zero h1 h2
  have h2' : ((t : ℂ) * z - (A : ℂ) ^ 2) * ((t : ℂ) * (starRingEnd ℂ) z - (A : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero h4 h3
  field_simp

lemma conj_exp_mul_I (y : ℝ) : (starRingEnd ℂ) (Complex.exp (y * I)) = (Complex.exp (y * I))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.conj_ofReal]

/-- On the arc, `ζ K(ζ) = 2π · hdArc` (`ζ = A e^{iy}`, `dζ = iζ dy`). -/
lemma imgK_arc {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : z ∈ openHalfDisc A) (y : ℝ) :
    ((A : ℂ) * Complex.exp (y * I)) * imgK A z ((A : ℂ) * Complex.exp (y * I)) =
      2 * π * (hdArc A z y : ℂ) := by
  set e : ℂ := Complex.exp (y * I) with he
  have hzA : ‖z‖ < A := hz.1
  have hz0 := ne_zero_of_mem hz
  have hzb0 : (starRingEnd ℂ) z ≠ 0 := by simpa using hz0
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have he0 : e ≠ 0 := Complex.exp_ne_zero _
  have hen : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I y
  have hei : ‖e⁻¹‖ = 1 := by rw [norm_inv, hen, inv_one]
  have hnA : ∀ w : ℂ, ‖w‖ < A → ∀ u : ℂ, ‖u‖ = 1 → (A : ℂ) * u - w ≠ 0 := fun w hw u hu h => by
    have : ‖(A : ℂ) * u‖ = ‖w‖ := by rw [sub_eq_zero.mp h]
    rw [norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, mul_one] at this
    linarith
  have hzbA : ‖(starRingEnd ℂ) z‖ < A := by simpa using hzA
  have h1 : (A : ℂ) * e - z ≠ 0 := hnA z hzA e hen
  have h2 : (A : ℂ) * e - (starRingEnd ℂ) z ≠ 0 := hnA _ hzbA e hen
  have h3 : (A : ℂ) * e * (starRingEnd ℂ) z - (A : ℂ) ^ 2 ≠ 0 := fun h => by
    have : ‖(A : ℂ) * e * (starRingEnd ℂ) z‖ = ‖(A : ℂ) ^ 2‖ := by rw [sub_eq_zero.mp h]
    rw [norm_mul, norm_mul, hen, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA] at this
    have : A * ‖(starRingEnd ℂ) z‖ = A ^ 2 := by nlinarith
    nlinarith [norm_nonneg ((starRingEnd ℂ) z)]
  have h4 : (A : ℂ) * e * z - (A : ℂ) ^ 2 ≠ 0 := fun h => by
    have : ‖(A : ℂ) * e * z‖ = ‖(A : ℂ) ^ 2‖ := by rw [sub_eq_zero.mp h]
    rw [norm_mul, norm_mul, hen, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA] at this
    have : A * ‖z‖ = A ^ 2 := by nlinarith
    nlinarith [norm_nonneg z]
  have h5 : z - (A : ℂ) * e⁻¹ ≠ 0 := fun h => by
    have := hnA z hzA e⁻¹ hei; apply this; rw [← neg_sub, h]; simp
  have h6 : (starRingEnd ℂ) z - (A : ℂ) * e⁻¹ ≠ 0 := fun h => by
    have := hnA _ hzbA e⁻¹ hei; apply this; rw [← neg_sub, h]; simp
  have h7 : z - (A : ℂ) * e ≠ 0 := fun h => by
    apply h1; rw [← neg_sub, h]; simp
  have h8 : (starRingEnd ℂ) z - (A : ℂ) * e ≠ 0 := fun h => by
    apply h2; rw [← neg_sub, h]; simp
  unfold imgK
  simp only [← one_div]
  rw [arc_alg2 (A : ℂ) e z ((starRingEnd ℂ) z) hA0 he0 hz0 hzb0 h1 h2 h3 h4 h5 h6 h7 h8]
  -- cast of the real kernel
  have hN1 : ((Complex.normSq (z - (A : ℂ) * e) : ℝ) : ℂ) =
      (z - (A : ℂ) * e) * ((starRingEnd ℂ) z - (A : ℂ) * e⁻¹) := by
    rw [normSq_cast_sub]; simp only [map_sub, map_mul, Complex.conj_ofReal, he, conj_exp_mul_I]
  have hN2 : ((Complex.normSq (z - (A : ℂ) * Complex.exp (-(y : ℂ) * I)) : ℝ) : ℂ) =
      (z - (A : ℂ) * e⁻¹) * ((starRingEnd ℂ) z - (A : ℂ) * e) := by
    have hinv : Complex.exp (-(y : ℂ) * I) = e⁻¹ := by
      rw [he, ← Complex.exp_neg]; congr 1; ring
    rw [hinv, normSq_cast_sub]
    simp only [map_sub, map_mul, Complex.conj_ofReal, map_inv₀, he, conj_exp_mul_I, inv_inv]
  have hn : ((Complex.normSq z : ℝ) : ℂ) = z * (starRingEnd ℂ) z := normSq_cast_sub z
  have hsub : (z.im : ℂ) = (z - (starRingEnd ℂ) z) / (2 * I) := by
    rw [Complex.sub_conj]; push_cast; field_simp
  unfold hdArc
  push_cast
  rw [hN1, hN2, hn, hsub, ← Complex.ofReal_sin, sin_cast, ← he]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : I ≠ 0 := Complex.I_ne_zero
  have hI2 : I ^ 2 = -1 := Complex.I_sq
  field_simp
  ring_nf
  rw [hI2]; ring

/-- For `w` outside the closed half-disc the Cauchy integral vanishes. -/
lemma hdBoundary_outside {A : ℝ} (hA : 0 < A) {G : ℂ → ℂ} (hc : ContinuousOn G (closedHalfDisc A))
    (hd : DifferentiableOn ℂ G (openHalfDisc A)) {w : ℂ} (hw : w ∉ closedHalfDisc A) :
    hdBoundary A (fun ζ => G ζ * (ζ - w)⁻¹) = 0 := by
  have hne : ∀ ζ ∈ closedHalfDisc A, ζ - w ≠ 0 := fun ζ hζ h => hw (by rw [← sub_eq_zero.mp h]; exact hζ)
  refine hdBoundary_eq_zero hA (hc.mul (ContinuousOn.inv₀ (by fun_prop) hne)) ?_
  intro ζ hζ
  have h1 : DifferentiableAt ℂ (fun ζ : ℂ => ζ - w) ζ := differentiableAt_id.sub_const w
  exact ((hd.differentiableAt (by
    have hopen : IsOpen (openHalfDisc A) := by
      have : openHalfDisc A = Metric.ball (0 : ℂ) A ∩ {w : ℂ | 0 < w.im} := by
        ext w; simp [openHalfDisc]
      rw [this]
      exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
    exact hopen.mem_nhds hζ)).mul (h1.inv (hne ζ ⟨hζ.1.le, hζ.2.le⟩))).differentiableWithinAt

lemma bdcont_mul_inv_sub {A : ℝ} (hA : 0 < A) {G : ℂ → ℂ} (hc : ContinuousOn G (closedHalfDisc A))
    {z : ℂ} (hz : z ∈ openHalfDisc A) : BdCont A (fun ζ => G ζ * (ζ - z)⁻¹) := by
  have hinvBd : BdCont A (fun ζ => (ζ - z)⁻¹) := by
    refine ⟨?_, ?_⟩
    · refine ContinuousOn.inv₀ (by fun_prop) (fun t _ h => ?_)
      have : (t : ℂ) = z := sub_eq_zero.mp h
      have := congrArg Complex.im this
      simp at this; linarith [hz.2]
    · refine ContinuousOn.inv₀ (by fun_prop) (fun y _ h => ?_)
      have h' := sub_eq_zero.mp h
      have : ‖(A : ℂ) * Complex.exp (y * I)‖ = ‖z‖ := by rw [h']
      rw [norm_arc A y hA] at this
      linarith [hz.1]
  exact (BdCont.of_closed hA hc).mul hinvBd

/-- **Poisson representation on the upper half-disc.**  For `G` continuous on `closure D_+` and holomorphic in `D_+`
(`D_+` of radius `A`), and `z ∈ D_+`:
`G(z) = ∫_{-A}^{A} hdDiam A z t · G(t) dt + ∫_0^π hdArc A z θ · G(A e^{iθ}) dθ`
(`hdDiam`, `hdArc` are `ct:Pdiam`, `ct:Parc`, the latter being `A` times the density in arclength). -/
theorem halfDisc_poisson {A : ℝ} (hA : 0 < A) {G : ℂ → ℂ} {z : ℂ} (hz : z ∈ openHalfDisc A)
    (hc : ContinuousOn G (closedHalfDisc A)) (hd : DifferentiableOn ℂ G (openHalfDisc A)) :
    G z = (∫ t in (-A)..A, (hdDiam A z t : ℂ) * G (t : ℂ)) +
      ∫ θ in (0 : ℝ)..π, (hdArc A z θ : ℂ) * G (A * Complex.exp (θ * I)) := by
  have hz0 := ne_zero_of_mem hz
  have hzA : ‖z‖ < A := hz.1
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set zb : ℂ := (starRingEnd ℂ) z with hzb
  -- the three image points lie outside the closed half-disc
  have hzb_out : zb ∉ closedHalfDisc A := fun h => by
    have := h.2; rw [hzb] at this; simp at this; linarith [hz.2]
  have hz1_out : (A : ℂ) ^ 2 / zb ∉ closedHalfDisc A := fun h => by
    have := h.1
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, hzb, Complex.norm_conj,
      div_le_iff₀ hzpos] at this
    nlinarith
  have hz2_out : (A : ℂ) ^ 2 / z ∉ closedHalfDisc A := fun h => by
    have := h.1
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA,
      div_le_iff₀ hzpos] at this
    nlinarith
  have c0 := hdBoundary_outside hA hc hd hzb_out
  have c1 := hdBoundary_outside hA hc hd hz1_out
  have c2 := hdBoundary_outside hA hc hd hz2_out
  have cz := hdBoundary_cauchy_formula hA hz hc hd
  have bz := bdcont_mul_inv_sub hA hc hz
  have bout : ∀ w, w ∉ closedHalfDisc A → BdCont A (fun ζ => G ζ * (ζ - w)⁻¹) := fun w hw =>
    BdCont.of_closed hA (hc.mul (ContinuousOn.inv₀ (by fun_prop)
      (fun ζ hζ h => hw (by rw [← sub_eq_zero.mp h]; exact hζ))))
  have hcomb : hdBoundary A (fun ζ => G ζ * imgK A z ζ) = 2 * π * I * G z := by
    have e : (fun ζ => G ζ * imgK A z ζ) = fun ζ => (G ζ * (ζ - z)⁻¹ + (-1 : ℂ) * (G ζ * (ζ - zb)⁻¹)) +
        (-1 : ℂ) * (G ζ * (ζ - (A : ℂ) ^ 2 / zb)⁻¹) + G ζ * (ζ - (A : ℂ) ^ 2 / z)⁻¹ := by
      funext ζ; unfold imgK; rw [← hzb]; ring
    rw [e, hdBoundary_add hA ((bz.add ((bout _ hzb_out).const_mul (-1))).add
        ((bout _ hz1_out).const_mul (-1))) (bout _ hz2_out),
      hdBoundary_add hA (bz.add ((bout _ hzb_out).const_mul (-1))) ((bout _ hz1_out).const_mul (-1)),
      hdBoundary_add hA bz ((bout _ hzb_out).const_mul (-1)),
      hdBoundary_const_mul, hdBoundary_const_mul, cz, c0, c1, c2]
    ring
  have hexp : hdBoundary A (fun ζ => G ζ * imgK A z ζ) = 2 * π * I *
      ((∫ t in (-A)..A, (hdDiam A z t : ℂ) * G (t : ℂ)) +
        ∫ θ in (0 : ℝ)..π, (hdArc A z θ : ℂ) * G (A * Complex.exp (θ * I))) := by
    have e1 : (∫ t in (-A)..A, G (t : ℂ) * imgK A z (t : ℂ)) =
        2 * π * I * ∫ t in (-A)..A, (hdDiam A z t : ℂ) * G (t : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [imgK_diam hA hz]; ring
    have e2 : (∫ y in (0 : ℝ)..π, G (A * Complex.exp (y * I)) * imgK A z (A * Complex.exp (y * I)) *
        (A * Complex.exp (y * I))) = 2 * π * ∫ θ in (0 : ℝ)..π, (hdArc A z θ : ℂ) * G (A * Complex.exp (θ * I)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun y _ => ?_
      have := imgK_arc hA hz y
      calc G (A * Complex.exp (y * I)) * imgK A z (A * Complex.exp (y * I)) * (A * Complex.exp (y * I))
          = G (A * Complex.exp (y * I)) * ((A * Complex.exp (y * I)) * imgK A z (A * Complex.exp (y * I))) := by ring
        _ = _ := by rw [this]; ring
    unfold hdBoundary
    beta_reduce
    rw [e1, e2]; ring
  have hne : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  exact mul_left_cancel₀ hne (hcomb.symm.trans hexp)

/-- info: 'FormalResearch.HalfDiscCauchy.halfDisc_poisson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.HalfDiscCauchy.halfDisc_poisson

end FormalResearch.HalfDiscCauchy
