module

public import Mathlib

@[expose] public section

open Complex MeasureTheory Metric Set
open scoped Real

namespace FormalResearch.Chebyshev

/-- Circle integral of `(w - v)⁻¹ g` is integrable on a circle missing `v`. -/
lemma circleIntegrable_inv_sub_mul {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) {v : ℂ} (hv : ‖v‖ ≠ ρ)
    (hg : ContinuousOn g (sphere 0 ρ)) :
    CircleIntegrable (fun w => (w - v)⁻¹ * g w) 0 ρ := by
  refine ContinuousOn.circleIntegrable hρ ?_
  refine ContinuousOn.mul ?_ hg
  refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun w hw => ?_
  intro h
  have : w = v := sub_eq_zero.1 h
  subst this
  simp only [mem_sphere_iff_norm, sub_zero] at hw
  exact hv hw

/-- **Cauchy's integral formula on an annulus.** -/
theorem annulus_cauchy {g : ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hc : ContinuousOn g (closedBall 0 R \ ball 0 r))
    (hd : ∀ z ∈ ball 0 R \ closedBall 0 r, DifferentiableAt ℂ g z) {v : ℂ} (hv1 : r < ‖v‖)
    (hv2 : ‖v‖ < R) :
    g v = (2 * π * I : ℂ)⁻¹ * (∮ w in C(0, R), (w - v)⁻¹ * g w) -
      (2 * π * I : ℂ)⁻¹ * (∮ w in C(0, r), (w - v)⁻¹ * g w) := by
  have hvmem : v ∈ ball 0 R \ closedBall 0 r := by
    simp only [mem_sdiff, mem_ball, dist_zero_right, mem_closedBall, not_le]; exact ⟨hv2, hv1⟩
  have hopen : IsOpen (ball (0 : ℂ) R \ closedBall 0 r) := isOpen_ball.sdiff isClosed_closedBall
  have hdOn : DifferentiableOn ℂ g (ball 0 R \ closedBall 0 r) :=
    fun z hz => (hd z hz).differentiableWithinAt
  have hdv : DifferentiableAt ℂ g v := hdOn.differentiableAt (hopen.mem_nhds hvmem)
  have hsub : ball (0 : ℂ) R \ closedBall 0 r ⊆ closedBall 0 R \ ball 0 r :=
    fun z hz => ⟨ball_subset_closedBall hz.1, fun h => hz.2 (ball_subset_closedBall h)⟩
  have hnhds : closedBall (0 : ℂ) R \ ball 0 r ∈ nhds v :=
    Filter.mem_of_superset (hopen.mem_nhds hvmem) hsub
  have hφc : ContinuousOn (dslope g v) (closedBall 0 R \ ball 0 r) :=
    (continuousOn_dslope hnhds).2 ⟨hc, hdv⟩
  have hφd : ∀ z ∈ (ball (0 : ℂ) R \ closedBall 0 r) \ (∅ : Set ℂ), DifferentiableAt ℂ (dslope g v) z := by
    intro z hz
    rw [sdiff_empty] at hz
    exact ((differentiableOn_dslope (hopen.mem_nhds hvmem)).2 hdOn).differentiableAt
      (hopen.mem_nhds hz)
  have key := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    countable_empty hφc hφd
  -- expand both circle integrals
  have expand : ∀ ρ : ℝ, 0 < ρ → ‖v‖ ≠ ρ → ContinuousOn g (sphere 0 ρ) →
      (∮ w in C(0, ρ), dslope g v w) =
        (∮ w in C(0, ρ), (w - v)⁻¹ * g w) - g v * ∮ w in C(0, ρ), (w - v)⁻¹ := by
    intro ρ hρ hvρ hgρ
    have h1 : (∮ w in C(0, ρ), dslope g v w) =
        ∮ w in C(0, ρ), ((w - v)⁻¹ * g w - g v * (w - v)⁻¹) := by
      refine circleIntegral.integral_congr hρ.le fun w hw => ?_
      have hwv : w ≠ v := by
        rintro rfl
        simp only [mem_sphere_iff_norm, sub_zero] at hw
        exact hvρ hw
      simp only [dslope_of_ne _ hwv, slope_def_field]
      ring
    rw [h1, circleIntegral.integral_sub (circleIntegrable_inv_sub_mul hρ.le hvρ hgρ),
      circleIntegral.integral_const_mul]
    have : CircleIntegrable (fun w : ℂ => (w - v)⁻¹) 0 ρ := by
      have := circleIntegrable_inv_sub_mul hρ.le hvρ (g := fun _ => 1) continuousOn_const
      simpa using this
    exact (this.const_mul _)
  have hgR : ContinuousOn g (sphere 0 R) :=
    hc.mono fun z hz => ⟨sphere_subset_closedBall hz, fun h => by
      have := mem_sphere_zero_iff_norm.1 hz
      have h2 := mem_ball_zero_iff.1 h
      linarith⟩
  have hgr : ContinuousOn g (sphere 0 r) :=
    hc.mono fun z hz => ⟨by
      have := mem_sphere_zero_iff_norm.1 hz
      rw [mem_closedBall_zero_iff]; linarith, fun h => by
      have := mem_sphere_zero_iff_norm.1 hz
      have h2 := mem_ball_zero_iff.1 h
      linarith⟩
  have hR0 : 0 < R := lt_of_lt_of_le hr hrR
  rw [expand R hR0 (ne_of_lt hv2) hgR, expand r hr (ne_of_gt hv1) hgr] at key
  have hinvR : (∮ w in C(0, R), (w - v)⁻¹) = 2 * π * I := by
    refine circleIntegral.integral_sub_inv_of_mem_ball ?_
    simpa using hv2
  have hinvr : (∮ w in C(0, r), (w - v)⁻¹) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
      ?_ ?_
    · refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun w hw => ?_
      have := mem_closedBall_zero_iff.1 hw
      intro h
      have : w = v := sub_eq_zero.1 h
      subst this
      linarith
    · intro w hw
      have hw' := mem_ball_zero_iff.1 hw.1
      refine DifferentiableAt.inv (differentiableAt_id.sub_const _) ?_
      intro h
      have : w = v := sub_eq_zero.1 h
      subst this
      linarith
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [hinvR, hinvr] at key
  rw [← mul_sub, eq_inv_mul_iff_mul_eq₀ h2]
  linear_combination -key


/-- Finite geometric expansion of the Cauchy kernel with explicit remainder. -/
lemma geom_kernel {v w : ℂ} (hw : w ≠ 0) (hwv : w - v ≠ 0) (N : ℕ) :
    (w - v)⁻¹ = (∑ k ∈ Finset.range N, v ^ k * (w ^ (k + 1))⁻¹) + (v / w) ^ N * (w - v)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc]
    have : (v / w) ^ N * (w - v)⁻¹ = v ^ N * (w ^ (N + 1))⁻¹ + (v / w) ^ (N + 1) * (w - v)⁻¹ := by
      rw [div_pow, div_pow]
      field_simp
      ring
    rw [← this]
    exact ih

/-- The `k`-th outer Laurent coefficient `(2πi)⁻¹ ∮_{|w|=R} g(w) w^{-k-1} dw`. -/
noncomputable def outerCoeff (g : ℂ → ℂ) (R : ℝ) (k : ℕ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ * ∮ w in C(0, R), (w ^ (k + 1))⁻¹ * g w

/-- The `k`-th inner Laurent coefficient `(2πi)⁻¹ ∮_{|w|=r} g(w) w^{k} dw`
(the coefficient of `v^{-k-1}`). -/
noncomputable def innerCoeff (g : ℂ → ℂ) (r : ℝ) (k : ℕ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ * ∮ w in C(0, r), w ^ k * g w

/-- Remainder of the outer part after `N` terms. -/
noncomputable def outerRem (g : ℂ → ℂ) (R : ℝ) (v : ℂ) (N : ℕ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ * ∮ w in C(0, R), (v / w) ^ N * ((w - v)⁻¹ * g w)

/-- Remainder of the inner part after `N` terms. -/
noncomputable def innerRem (g : ℂ → ℂ) (r : ℝ) (v : ℂ) (N : ℕ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ * ∮ w in C(0, r), (w / v) ^ N * ((v - w)⁻¹ * g w)

lemma outer_expand {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hg : ContinuousOn g (sphere 0 R)) {v : ℂ}
    (hv : ‖v‖ < R) (N : ℕ) :
    (2 * π * I : ℂ)⁻¹ * (∮ w in C(0, R), (w - v)⁻¹ * g w) =
      (∑ k ∈ Finset.range N, outerCoeff g R k * v ^ k) + outerRem g R v N := by
  have hw : ∀ w ∈ sphere (0 : ℂ) R, w ≠ 0 ∧ w - v ≠ 0 := by
    intro w hw
    have := mem_sphere_zero_iff_norm.1 hw
    refine ⟨?_, ?_⟩
    · rintro rfl; simp at this; linarith
    · intro h
      have : w = v := sub_eq_zero.1 h
      subst this; linarith
  have hcont_inv : ∀ k : ℕ, ContinuousOn (fun w : ℂ => (w ^ (k + 1))⁻¹ * g w) (sphere 0 R) := by
    intro k
    refine ContinuousOn.mul ?_ hg
    exact ContinuousOn.inv₀ (continuousOn_id.pow _) fun w hwm => pow_ne_zero _ (hw w hwm).1
  have hrem : ContinuousOn (fun w : ℂ => (v / w) ^ N * ((w - v)⁻¹ * g w)) (sphere 0 R) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (continuousOn_const.div continuousOn_id fun w hwm => (hw w hwm).1).pow _
    · refine ContinuousOn.mul ?_ hg
      exact ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun w hwm => (hw w hwm).2
  have e1 : (∮ w in C(0, R), (w - v)⁻¹ * g w) =
      ∮ w in C(0, R), ((∑ k ∈ Finset.range N, v ^ k * ((w ^ (k + 1))⁻¹ * g w)) +
        (v / w) ^ N * ((w - v)⁻¹ * g w)) := by
    refine circleIntegral.integral_congr hR.le fun w hwm => ?_
    have := geom_kernel (hw w hwm).1 (hw w hwm).2 N
    calc (w - v)⁻¹ * g w = ((∑ k ∈ Finset.range N, v ^ k * (w ^ (k + 1))⁻¹) +
          (v / w) ^ N * (w - v)⁻¹) * g w := by rw [← this]
      _ = _ := by rw [add_mul, Finset.sum_mul]; congr 1
                  refine Finset.sum_congr rfl fun k _ => by ring
                  ring
  rw [e1, circleIntegral.integral_add, circleIntegral.integral_fun_sum]
  · simp only [circleIntegral.integral_const_mul, mul_add, Finset.mul_sum, outerCoeff, outerRem]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  · intro k _
    exact (((hcont_inv k).circleIntegrable hR.le).const_mul (v ^ k))
  · exact (continuousOn_finsetSum _ fun k _ => continuousOn_const.mul (hcont_inv k)).circleIntegrable hR.le
  · exact hrem.circleIntegrable hR.le


lemma inner_expand {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r)) {v : ℂ}
    (hv : r < ‖v‖) (N : ℕ) :
    -((2 * π * I : ℂ)⁻¹ * (∮ w in C(0, r), (w - v)⁻¹ * g w)) =
      (∑ k ∈ Finset.range N, innerCoeff g r k * (v ^ (k + 1))⁻¹) + innerRem g r v N := by
  have hv0 : v ≠ 0 := by
    rintro rfl; simp at hv; linarith
  have hw : ∀ w ∈ sphere (0 : ℂ) r, v - w ≠ 0 := by
    intro w hw h
    have := mem_sphere_zero_iff_norm.1 hw
    have : v = w := sub_eq_zero.1 h
    subst this; linarith
  have hcont : ∀ k : ℕ, ContinuousOn (fun w : ℂ => w ^ k * g w) (sphere 0 r) :=
    fun k => (continuousOn_id.pow k).mul hg
  have hrem : ContinuousOn (fun w : ℂ => (w / v) ^ N * ((v - w)⁻¹ * g w)) (sphere 0 r) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (continuousOn_id.div_const v).pow _
    · refine ContinuousOn.mul ?_ hg
      exact ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun w hwm => hw w hwm
  have e1 : -(∮ w in C(0, r), (w - v)⁻¹ * g w) =
      ∮ w in C(0, r), ((∑ k ∈ Finset.range N, (v ^ (k + 1))⁻¹ * (w ^ k * g w)) +
        (w / v) ^ N * ((v - w)⁻¹ * g w)) := by
    have hn := circleIntegral.integral_const_mul (-1 : ℂ) (fun w : ℂ => (w - v)⁻¹ * g w) 0 r
    rw [neg_one_mul] at hn
    rw [← hn]
    refine circleIntegral.integral_congr hr.le fun w hwm => ?_
    have := geom_kernel (v := w) (w := v) hv0 (hw w hwm) N
    have h3 : -(w - v)⁻¹ = (v - w)⁻¹ := by
      rw [show v - w = -(w - v) by ring, inv_neg]
    calc (-1 : ℂ) * ((w - v)⁻¹ * g w) = (v - w)⁻¹ * g w := by
          rw [show (-1 : ℂ) * ((w - v)⁻¹ * g w) = (-(w - v)⁻¹) * g w by ring, h3]
      _ = ((∑ k ∈ Finset.range N, w ^ k * (v ^ (k + 1))⁻¹) +
          (w / v) ^ N * (v - w)⁻¹) * g w := by rw [← this]
      _ = _ := by
        rw [add_mul, Finset.sum_mul]
        congr 1
        · refine Finset.sum_congr rfl fun k _ => by ring
        · ring
  have hint : CircleIntegrable (fun w : ℂ => (w - v)⁻¹ * g w) 0 r :=
    circleIntegrable_inv_sub_mul hr.le (ne_of_gt hv) hg
  rw [← mul_neg, e1, circleIntegral.integral_add, circleIntegral.integral_fun_sum]
  · simp only [circleIntegral.integral_const_mul, mul_add, Finset.mul_sum, innerCoeff, innerRem]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  · intro k _
    exact (((hcont k).circleIntegrable hr.le).const_mul ((v ^ (k + 1))⁻¹))
  · exact (continuousOn_finsetSum _ fun k _ => continuousOn_const.mul (hcont k)).circleIntegrable hr.le
  · exact hrem.circleIntegrable hr.le

end FormalResearch.Chebyshev
