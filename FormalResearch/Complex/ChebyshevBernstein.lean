module

public import Mathlib

/-!
# Chebyshev coefficients and truncation error on the Bernstein ellipse

Generic complex analysis, no Airy content; **proved** (Mathlib has Chebyshev polynomials `T` and circle
integrals but no Bernstein-ellipse approximation theory: checked by grepping `Mathlib` for
`Bernstein ellipse`/`Joukowski`).  Formalises Trefethen, *Approximation Theory and Approximation Practice*,
Thm 8.1 (coefficient decay) and Thm 8.2 (truncation error), with exactly Trefethen's constants.

Setting.  `joukowski w = (w + w⁻¹)/2` maps `{|w| = ρ}` onto the boundary of the Bernstein ellipse `E_ρ` of
`[-1,1]` and the unit circle onto `[-1,1]`.  `BernsteinHyp f ρ M` says: `1 < ρ`, `g = f ∘ joukowski` is continuous on
the closed annulus `ρ⁻¹ ≤ |w| ≤ ρ`, complex differentiable inside, and `‖f‖ ≤ M` on `joukowski '' {|w| = ρ}`
(i.e. `f` analytic in the open ellipse, continuous up to `∂E_ρ`, bounded by `M` there).  The Chebyshev
coefficients are `a₀ = (2πi)⁻¹∮_{|w|=ρ} g w⁻¹ dw`, `a_{k+1} = (2πi)⁻¹[∮_{|w|=ρ} g w^{-k-2} dw +
∮_{|w|=ρ⁻¹} g w^{k} dw]` (`chebCoeff`; these are Laurent coefficients of `g`, so equal the usual
`(2/π)∫₀^π f(cos θ) cos kθ dθ`, a fact **not** formalised: the integral-over-`[0,π]` form is never used).

* `annulus_cauchy`: Cauchy's integral formula on an annulus `r < |v| < R` (from `dslope` and Mathlib's annulus
  Cauchy–Goursat), the only complex-analytic input.
* `BernsteinHyp.expansion`: finite Laurent expansion of `f(joukowski v)` with explicit integral remainders
  (finite geometric series for the Cauchy kernel; no infinite series, no Fourier-series convergence theorem).
* `BernsteinHyp.norm_chebCoeff_le` (**Thm 8.1**): `|a_k| ≤ 2 M ρ^{-k}`.
* `BernsteinHyp.error_real` (**Thm 8.2**): for `x ∈ [-1,1]`, `|f(x) - Σ_{k ≤ n} a_k T_k(x)| ≤ 2 M ρ^{-n}/(ρ-1)`;
  `BernsteinHyp.exists_poly`: the polynomial `chebPartial` has degree `≤ n`; `BernsteinHyp.error_real_re`: the
  real-part form with real `T_k` (no reality hypothesis).
* `bernsteinHyp_of_differentiableOn`, `bernsteinHyp_of_differentiable`: the hypotheses for `f` differentiable on an
  open set containing the closed region (e.g. entire `f`).
* `continuous_chebCoeff`: the coefficients depend continuously on a parameter when `f` does (measurability of the
  coefficient functions of a parametrised kernel).

Mechanism: with `v` on the unit circle, the annulus Cauchy formula gives `g(v) = O(v) + I(v)`; the finite
geometric expansion of `(w - v)⁻¹` on `|w| = ρ` and of `(v - w)⁻¹` on `|w| = ρ⁻¹` gives `g(v)` as a Laurent
polynomial plus remainders of size `M ρ^{-n}/(ρ-1)` each; averaging `v` and `v⁻¹` (same image under `joukowski`)
turns `v^k + v^{-k}` into `2 T_k(x)`.  A numerical sanity check (numpy, `f = 1/(z - 3/2)`, `ρ = 2`) shows the
bound `2Mρ^{-n}/(ρ-1)` and `|a_k| ≤ 2Mρ^{-k}` hold with room (error `7·10⁻⁵` against bound `8·10⁻³` at `n = 10`).

**Not formalised:** the identification of `a_k` with the cosine integral of `f(cos θ)`; the converse (Bernstein) theorem
that geometric decay of the best approximation errors implies analyticity in an ellipse; Chebyshev *interpolation* in
Chebyshev points (Trefethen Thm 8.3, error `≤ 4Mρ^{-n}/(ρ-1)`; the survey/paper cite Thm 8.2, which is the *truncation*
statement proved here; for a rank-`n+1` approximation the truncation serves equally well); the sharp constant.
-/

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


/-! ### Norm bounds -/

lemma norm_outerRem_le {g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) {v : ℂ} (hv : ‖v‖ < R)
    (hM : ∀ w ∈ sphere (0 : ℂ) R, ‖g w‖ ≤ M) (N : ℕ) :
    ‖outerRem g R v N‖ ≤ R * ((‖v‖ / R) ^ N * (M / (R - ‖v‖))) := by
  unfold outerRem
  rw [← smul_eq_mul]
  refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le fun w hw => ?_
  have hwn := mem_sphere_zero_iff_norm.1 hw
  have h1 : R - ‖v‖ ≤ ‖w - v‖ := by
    have := norm_sub_norm_le w v
    linarith
  have h2 : 0 < R - ‖v‖ := by linarith
  rw [norm_mul, norm_mul, norm_pow, norm_div, norm_inv, hwn]
  have hgw := hM w hw
  have hg0 : 0 ≤ ‖g w‖ := norm_nonneg _
  have hM0 : 0 ≤ M := hg0.trans hgw
  gcongr
  calc ‖w - v‖⁻¹ * ‖g w‖ ≤ (R - ‖v‖)⁻¹ * M := by gcongr
    _ = M / (R - ‖v‖) := by rw [inv_mul_eq_div]

lemma norm_innerRem_le {g : ℂ → ℂ} {r M : ℝ} (hr : 0 < r) {v : ℂ} (hv : r < ‖v‖)
    (hM : ∀ w ∈ sphere (0 : ℂ) r, ‖g w‖ ≤ M) (N : ℕ) :
    ‖innerRem g r v N‖ ≤ r * ((r / ‖v‖) ^ N * (M / (‖v‖ - r))) := by
  unfold innerRem
  rw [← smul_eq_mul]
  refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le fun w hw => ?_
  have hwn := mem_sphere_zero_iff_norm.1 hw
  have h1 : ‖v‖ - r ≤ ‖v - w‖ := by
    have := norm_sub_norm_le v w
    linarith
  have h2 : 0 < ‖v‖ - r := by linarith
  rw [norm_mul, norm_mul, norm_pow, norm_div, norm_inv, hwn]
  have hgw := hM w hw
  have hg0 : 0 ≤ ‖g w‖ := norm_nonneg _
  have hM0 : 0 ≤ M := hg0.trans hgw
  gcongr
  calc ‖v - w‖⁻¹ * ‖g w‖ ≤ (‖v‖ - r)⁻¹ * M := by gcongr
    _ = M / (‖v‖ - r) := by rw [inv_mul_eq_div]

lemma norm_outerCoeff_le {g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : ∀ w ∈ sphere (0 : ℂ) R, ‖g w‖ ≤ M) (k : ℕ) :
    ‖outerCoeff g R k‖ ≤ M / R ^ k := by
  unfold outerCoeff
  rw [← smul_eq_mul]
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    (C := (R ^ (k + 1))⁻¹ * M) fun w hw => ?_).trans (le_of_eq ?_)
  · have hwn := mem_sphere_zero_iff_norm.1 hw
    rw [norm_mul, norm_inv, norm_pow, hwn]
    gcongr
    exact hM w hw
  · field_simp
    ring

lemma norm_innerCoeff_le {g : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ w ∈ sphere (0 : ℂ) r, ‖g w‖ ≤ M) (k : ℕ) :
    ‖innerCoeff g r k‖ ≤ r ^ (k + 1) * M := by
  unfold innerCoeff
  rw [← smul_eq_mul]
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le
    (C := r ^ k * M) fun w hw => ?_).trans (le_of_eq ?_)
  · have hwn := mem_sphere_zero_iff_norm.1 hw
    rw [norm_mul, norm_pow, hwn]
    have hg0 : 0 ≤ ‖g w‖ := norm_nonneg _
    gcongr
    exact hM w hw
  · ring


/-! ### The Joukowski map and the Chebyshev coefficients -/

/-- The Joukowski map `w ↦ (w + w⁻¹)/2`; it maps the circle `|w| = ρ` onto the boundary of the Bernstein
ellipse `E_ρ` of `[-1,1]` (and the unit circle onto `[-1,1]`, two-to-one). -/
noncomputable def joukowski (w : ℂ) : ℂ := (w + w⁻¹) / 2

lemma joukowski_inv (w : ℂ) : joukowski w⁻¹ = joukowski w := by
  simp [joukowski, add_comm]

/-- The Chebyshev coefficients of `g = f ∘ joukowski`: `a₀ = outerCoeff 0`,
`a_{k+1} = outerCoeff (k+1) + innerCoeff k` (outer circle radius `ρ`, inner radius `ρ⁻¹`). -/
noncomputable def chebCoeff (g : ℂ → ℂ) (ρ : ℝ) : ℕ → ℂ
  | 0 => outerCoeff g ρ 0
  | k + 1 => outerCoeff g ρ (k + 1) + innerCoeff g ρ⁻¹ k

/-- The degree-`n` Chebyshev truncation `Σ_{k ≤ n} a_k T_k`. -/
noncomputable def chebPartial (g : ℂ → ℂ) (ρ : ℝ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (chebCoeff g ρ k) * Polynomial.Chebyshev.T ℂ (k : ℤ)

lemma natDegree_chebPartial_le (g : ℂ → ℂ) (ρ : ℝ) (n : ℕ) : (chebPartial g ρ n).natDegree ≤ n := by
  unfold chebPartial
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.Chebyshev.natDegree_T]
  simpa using hk'

lemma joukowski_exp_eq_cos (θ : ℝ) : joukowski (exp (θ * I)) = Complex.cos θ := by
  rw [joukowski, Complex.cos, ← Complex.exp_neg]
  congr 3; ring_nf

lemma eval_T_unit (θ : ℝ) (k : ℕ) :
    (Polynomial.Chebyshev.T ℂ (k : ℤ)).eval (joukowski (exp (θ * I))) =
      (exp (θ * I) ^ k + (exp (θ * I) ^ k)⁻¹) / 2 := by
  rw [joukowski_exp_eq_cos, Polynomial.Chebyshev.T_complex_cos, Complex.cos]
  have e1 : exp (((k : ℤ) : ℂ) * θ * I) = exp (θ * I) ^ k := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : exp (-(((k : ℤ) : ℂ) * θ) * I) = (exp (θ * I) ^ k)⁻¹ := by
    rw [← e1, ← Complex.exp_neg]; congr 1; ring
  rw [e1, e2]


/-! ### The Laurent expansion with remainder and the main theorem -/

section Main

variable {f : ℂ → ℂ} {ρ M : ℝ}

/-- Hypotheses of the Bernstein-ellipse theorem, in the Joukowski variable: `g = f ∘ joukowski` is
continuous on the closed annulus `ρ⁻¹ ≤ |w| ≤ ρ`, differentiable inside, and `|f| ≤ M` on the boundary
ellipse `joukowski '' {|w| = ρ}`. -/
structure BernsteinHyp (f : ℂ → ℂ) (ρ M : ℝ) : Prop where
  one_lt : 1 < ρ
  cont : ContinuousOn (fun w => f (joukowski w)) (closedBall 0 ρ \ ball 0 ρ⁻¹)
  diff : ∀ w : ℂ, ρ⁻¹ < ‖w‖ → ‖w‖ < ρ → DifferentiableAt ℂ (fun w => f (joukowski w)) w
  bound : ∀ w : ℂ, ‖w‖ = ρ → ‖f (joukowski w)‖ ≤ M

lemma BernsteinHyp.bound_inner (h : BernsteinHyp f ρ M) {w : ℂ} (hw : ‖w‖ = ρ⁻¹) :
    ‖f (joukowski w)‖ ≤ M := by
  rw [← joukowski_inv]
  refine h.bound _ ?_
  rw [norm_inv, hw, inv_inv]

lemma BernsteinHyp.pos (h : BernsteinHyp f ρ M) : 0 < ρ := lt_trans zero_lt_one h.one_lt

lemma BernsteinHyp.inv_lt_one (h : BernsteinHyp f ρ M) : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ h.one_lt

/-- **Laurent expansion with remainders** for `g = f ∘ joukowski` at a point of the open annulus. -/
theorem BernsteinHyp.expansion (h : BernsteinHyp f ρ M) {v : ℂ} (hv1 : ρ⁻¹ < ‖v‖) (hv2 : ‖v‖ < ρ)
    (N₁ N₂ : ℕ) :
    f (joukowski v) =
      (∑ k ∈ Finset.range N₁, outerCoeff (fun w => f (joukowski w)) ρ k * v ^ k) +
        outerRem (fun w => f (joukowski w)) ρ v N₁ +
      ((∑ k ∈ Finset.range N₂, innerCoeff (fun w => f (joukowski w)) ρ⁻¹ k * (v ^ (k + 1))⁻¹) +
        innerRem (fun w => f (joukowski w)) ρ⁻¹ v N₂) := by
  have hρ0 := h.pos
  have hr0 : 0 < ρ⁻¹ := inv_pos.2 hρ0
  have hrR : ρ⁻¹ ≤ ρ := (h.inv_lt_one.trans h.one_lt).le
  have hcR : ContinuousOn (fun w => f (joukowski w)) (sphere 0 ρ) :=
    h.cont.mono fun z hz => ⟨sphere_subset_closedBall hz, fun hb => by
      have := mem_sphere_zero_iff_norm.1 hz
      have h2 := mem_ball_zero_iff.1 hb
      have := h.inv_lt_one
      have := h.one_lt
      linarith⟩
  have hcr : ContinuousOn (fun w => f (joukowski w)) (sphere 0 ρ⁻¹) :=
    h.cont.mono fun z hz => ⟨by
      have := mem_sphere_zero_iff_norm.1 hz
      rw [mem_closedBall_zero_iff]; linarith, fun hb => by
      have := mem_sphere_zero_iff_norm.1 hz
      have h2 := mem_ball_zero_iff.1 hb
      linarith⟩
  have hAC := annulus_cauchy hr0 hrR h.cont
    (fun z hz => h.diff z (by
      have := hz.2; simp only [mem_closedBall_zero_iff, not_le] at this; exact this)
      (by have := hz.1; simpa using this)) hv1 hv2
  rw [hAC, sub_eq_add_neg, outer_expand hρ0 hcR hv2 N₁, inner_expand hr0 hcr hv1 N₂]


lemma BernsteinHyp.norm_outerRem_unit (h : BernsteinHyp f ρ M) {v : ℂ} (hv : ‖v‖ = 1) (n : ℕ) :
    ‖outerRem (fun w => f (joukowski w)) ρ v (n + 1)‖ ≤ M / (ρ ^ n * (ρ - 1)) := by
  have hρ0 := h.pos
  have h1 := h.one_lt
  have := norm_outerRem_le (g := fun w => f (joukowski w)) hρ0 (v := v) (by rw [hv]; exact h1)
    (fun w hw => h.bound w (mem_sphere_zero_iff_norm.1 hw)) (n + 1)
  refine this.trans (le_of_eq ?_)
  rw [hv]
  have : ρ - 1 ≠ 0 := by linarith
  have hρne : ρ ≠ 0 := hρ0.ne'
  simp only [one_div, inv_pow]
  field_simp
  ring

lemma BernsteinHyp.norm_innerRem_unit (h : BernsteinHyp f ρ M) {v : ℂ} (hv : ‖v‖ = 1) (n : ℕ) :
    ‖innerRem (fun w => f (joukowski w)) ρ⁻¹ v n‖ ≤ M / (ρ ^ n * (ρ - 1)) := by
  have hρ0 := h.pos
  have h1 := h.one_lt
  have := norm_innerRem_le (g := fun w => f (joukowski w)) (inv_pos.2 hρ0) (v := v)
    (by rw [hv]; exact h.inv_lt_one)
    (fun w hw => h.bound_inner (mem_sphere_zero_iff_norm.1 hw)) n
  refine this.trans (le_of_eq ?_)
  rw [hv]
  have : ρ - 1 ≠ 0 := by linarith
  have : 1 - ρ⁻¹ ≠ 0 := by
    have := h.inv_lt_one; linarith
  have hρne : ρ ≠ 0 := hρ0.ne'
  simp only [div_one, inv_pow]
  field_simp

/-- Value of the truncation at a point of the unit circle. -/
lemma eval_chebPartial_unit (g : ℂ → ℂ) (ρ : ℝ) (n : ℕ) (θ : ℝ) :
    (chebPartial g ρ n).eval (joukowski (exp (θ * I))) =
      (∑ k ∈ Finset.range (n + 1), outerCoeff g ρ k *
          ((exp (θ * I) ^ k + (exp (θ * I) ^ k)⁻¹) / 2)) +
        ∑ k ∈ Finset.range n, innerCoeff g ρ⁻¹ k *
          ((exp (θ * I) ^ (k + 1) + (exp (θ * I) ^ (k + 1))⁻¹) / 2) := by
  unfold chebPartial
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, eval_T_unit]
  rw [Finset.sum_range_succ' _ n, Finset.sum_range_succ' (fun k => outerCoeff g ρ k * _) n]
  simp only [chebCoeff, add_mul, Finset.sum_add_distrib]
  ring


/-- **Bernstein-ellipse approximation on the unit circle** (error of the Chebyshev truncation at the
points `cos θ`, in the Joukowski variable). -/
theorem BernsteinHyp.error_unit (h : BernsteinHyp f ρ M) (n : ℕ) (θ : ℝ) :
    ‖f (joukowski (exp (θ * I))) -
        (chebPartial (fun w => f (joukowski w)) ρ n).eval (joukowski (exp (θ * I)))‖ ≤
      2 * M / (ρ ^ n * (ρ - 1)) := by
  set v : ℂ := exp (θ * I) with hvdef
  set g : ℂ → ℂ := fun w => f (joukowski w) with hg
  have hv : ‖v‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hvi : ‖v⁻¹‖ = 1 := by rw [norm_inv, hv, inv_one]
  have hv1 : ρ⁻¹ < ‖v‖ := by rw [hv]; exact h.inv_lt_one
  have hv2 : ‖v‖ < ρ := by rw [hv]; exact h.one_lt
  have hvi1 : ρ⁻¹ < ‖v⁻¹‖ := by rw [hvi]; exact h.inv_lt_one
  have hvi2 : ‖v⁻¹‖ < ρ := by rw [hvi]; exact h.one_lt
  have E1 := h.expansion hv1 hv2 (n + 1) n
  have E2 := h.expansion hvi1 hvi2 (n + 1) n
  rw [joukowski_inv] at E2
  rw [eval_chebPartial_unit]
  set R1 := outerRem g ρ v (n + 1)
  set R2 := innerRem g ρ⁻¹ v n
  set R3 := outerRem g ρ v⁻¹ (n + 1)
  set R4 := innerRem g ρ⁻¹ v⁻¹ n
  have hR1 := h.norm_outerRem_unit hv n
  have hR2 := h.norm_innerRem_unit hv n
  have hR3 := h.norm_outerRem_unit hvi n
  have hR4 := h.norm_innerRem_unit hvi n
  have key : f (joukowski v) - ((∑ k ∈ Finset.range (n + 1), outerCoeff g ρ k *
          ((v ^ k + (v ^ k)⁻¹) / 2)) +
        ∑ k ∈ Finset.range n, innerCoeff g ρ⁻¹ k * ((v ^ (k + 1) + (v ^ (k + 1))⁻¹) / 2)) =
      (R1 + R2 + R3 + R4) / 2 := by
    have e1 : f (joukowski v) = (f (joukowski v) + f (joukowski v)) / 2 := by ring
    have hsum1 : ∑ k ∈ Finset.range (n + 1), outerCoeff g ρ k * ((v ^ k + (v ^ k)⁻¹) / 2) =
        (∑ k ∈ Finset.range (n + 1), outerCoeff g ρ k * v ^ k +
          ∑ k ∈ Finset.range (n + 1), outerCoeff g ρ k * (v⁻¹) ^ k) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => by rw [inv_pow]; ring
    have hsum2 : ∑ k ∈ Finset.range n, innerCoeff g ρ⁻¹ k * ((v ^ (k + 1) + (v ^ (k + 1))⁻¹) / 2) =
        (∑ k ∈ Finset.range n, innerCoeff g ρ⁻¹ k * (v ^ (k + 1))⁻¹ +
          ∑ k ∈ Finset.range n, innerCoeff g ρ⁻¹ k * ((v⁻¹) ^ (k + 1))⁻¹) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => by rw [inv_pow, inv_inv]; ring
    rw [hsum1, hsum2]
    conv_lhs => rw [e1]
    nth_rewrite 1 [E1]
    nth_rewrite 1 [E2]
    ring
  rw [key, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hρ1 : 0 < ρ - 1 := by linarith [h.one_lt]
  calc ‖R1 + R2 + R3 + R4‖ ≤ ‖R1‖ + ‖R2‖ + ‖R3‖ + ‖R4‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ M / (ρ ^ n * (ρ - 1)) + M / (ρ ^ n * (ρ - 1)) + M / (ρ ^ n * (ρ - 1)) +
          M / (ρ ^ n * (ρ - 1)) := by gcongr
    _ = 2 * M / (ρ ^ n * (ρ - 1)) * 2 := by ring


lemma joukowski_exp_mul_I (θ : ℝ) : joukowski (exp (θ * I)) = ((Real.cos θ : ℝ) : ℂ) := by
  rw [joukowski_exp_eq_cos, Complex.ofReal_cos]

lemma BernsteinHyp.nonneg (h : BernsteinHyp f ρ M) : 0 ≤ M :=
  (norm_nonneg _).trans (h.bound (ρ : ℂ) (by simp [abs_of_pos h.pos]))

/-- **Chebyshev truncation error on `[-1,1]`** (Trefethen, *Approximation Theory and Approximation
Practice*, Thm 8.2): if `f` is analytic in the open Bernstein ellipse `E_ρ`, continuous on its closure and
`|f| ≤ M` on the boundary, then the degree-`n` Chebyshev truncation satisfies
`|f(x) - p_n(x)| ≤ 2 M ρ^{-n}/(ρ-1)` for all `x ∈ [-1,1]`. -/
theorem BernsteinHyp.error_real (h : BernsteinHyp f ρ M) (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    ‖f (x : ℂ) - (chebPartial (fun w => f (joukowski w)) ρ n).eval (x : ℂ)‖ ≤
      2 * M / (ρ ^ n * (ρ - 1)) := by
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos (abs_le.1 hx).1 (abs_le.1 hx).2
  have := h.error_unit n (Real.arccos x)
  rwa [joukowski_exp_mul_I, hcos] at this

/-- **Chebyshev coefficient decay** (Trefethen Thm 8.1): `|a_k| ≤ 2 M ρ^{-k}`. -/
theorem BernsteinHyp.norm_chebCoeff_le (h : BernsteinHyp f ρ M) (k : ℕ) :
    ‖chebCoeff (fun w => f (joukowski w)) ρ k‖ ≤ 2 * M / ρ ^ k := by
  have hρ0 := h.pos
  have hM := h.nonneg
  have hO := fun j => norm_outerCoeff_le (g := fun w => f (joukowski w)) hρ0
    (fun w hw => h.bound w (mem_sphere_zero_iff_norm.1 hw)) j
  cases k with
  | zero =>
    simp only [chebCoeff, pow_zero, div_one]
    have := hO 0
    simp only [pow_zero, div_one] at this
    linarith
  | succ k =>
    simp only [chebCoeff]
    have hI := norm_innerCoeff_le (g := fun w => f (joukowski w)) (inv_pos.2 hρ0)
      (fun w hw => h.bound_inner (mem_sphere_zero_iff_norm.1 hw)) k
    refine (norm_add_le _ _).trans ?_
    have h1 := hO (k + 1)
    have h2 : (ρ⁻¹) ^ (k + 1) * M = M / ρ ^ (k + 1) := by
      rw [inv_pow, inv_mul_eq_div]
    rw [h2] at hI
    calc _ ≤ M / ρ ^ (k + 1) + M / ρ ^ (k + 1) := add_le_add h1 hI
      _ = _ := by ring

/-- Existence form: there is a polynomial of degree at most `n` with sup error `≤ 2Mρ^{-n}/(ρ-1)` on
`[-1,1]`. -/
theorem BernsteinHyp.exists_poly (h : BernsteinHyp f ρ M) (n : ℕ) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧
      ∀ x : ℝ, |x| ≤ 1 → ‖f (x : ℂ) - p.eval (x : ℂ)‖ ≤ 2 * M / (ρ ^ n * (ρ - 1)) :=
  ⟨_, natDegree_chebPartial_le _ _ n, fun _ hx => h.error_real n hx⟩

/-- **Real-part form** (no reality hypothesis needed): `|Re f(x) - Σ_{k ≤ n} Re(a_k) T_k(x)| ≤ 2Mρ^{-n}/(ρ-1)`
on `[-1,1]`, with the real Chebyshev polynomials `T_k` of `ℝ`.  For `f` real on `[-1,1]` this is the
real approximation. -/
theorem BernsteinHyp.error_real_re (h : BernsteinHyp f ρ M) (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(f (x : ℂ)).re - ∑ k ∈ Finset.range (n + 1),
        (chebCoeff (fun w => f (joukowski w)) ρ k).re *
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x| ≤ 2 * M / (ρ ^ n * (ρ - 1)) := by
  refine le_trans ?_ (h.error_real n hx)
  have e : (chebPartial (fun w => f (joukowski w)) ρ n).eval (x : ℂ) =
      ∑ k ∈ Finset.range (n + 1), chebCoeff (fun w => f (joukowski w)) ρ k *
        (((Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x : ℝ) : ℂ) := by
    unfold chebPartial
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.complex_ofReal_eval_T]
  have hre : ((chebPartial (fun w => f (joukowski w)) ρ n).eval (x : ℂ)).re =
      ∑ k ∈ Finset.range (n + 1), (chebCoeff (fun w => f (joukowski w)) ρ k).re *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x := by
    rw [e, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Complex.re_mul_ofReal _ _
  rw [← hre, ← Complex.sub_re]
  exact Complex.abs_re_le_norm _

end Main

/-! ### Sufficient conditions for the hypotheses -/

lemma differentiableAt_joukowski {w : ℂ} (hw : w ≠ 0) : DifferentiableAt ℂ joukowski w := by
  unfold joukowski
  exact (differentiableAt_id.add (differentiableAt_inv hw)).div_const 2

/-- If `f` is differentiable on an open set `U` containing the closed Bernstein region
`joukowski '' {ρ⁻¹ ≤ |w| ≤ ρ}` (e.g. `f` entire) and `|f| ≤ M` on the ellipse `|w| = ρ`, the hypotheses
hold. -/
theorem bernsteinHyp_of_differentiableOn {f : ℂ → ℂ} {ρ M : ℝ} {U : Set ℂ} (hρ : 1 < ρ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hsub : ∀ w : ℂ, ρ⁻¹ ≤ ‖w‖ → ‖w‖ ≤ ρ → joukowski w ∈ U)
    (hM : ∀ w : ℂ, ‖w‖ = ρ → ‖f (joukowski w)‖ ≤ M) : BernsteinHyp f ρ M := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hr0 : 0 < ρ⁻¹ := inv_pos.2 hρ0
  have hdiff : ∀ w : ℂ, ρ⁻¹ ≤ ‖w‖ → ‖w‖ ≤ ρ →
      DifferentiableAt ℂ (fun w => f (joukowski w)) w := by
    intro w h1 h2
    have hw0 : w ≠ 0 := by
      rintro rfl; simp at h1; linarith
    exact (hf.differentiableAt (hU.mem_nhds (hsub w h1 h2))).comp w (differentiableAt_joukowski hw0)
  refine ⟨hρ, ?_, fun w h1 h2 => hdiff w h1.le h2.le, hM⟩
  intro w hw
  have h1 : ρ⁻¹ ≤ ‖w‖ := by
    have := hw.2
    simp only [mem_ball_zero_iff, not_lt] at this
    exact this
  exact (hdiff w h1 (mem_closedBall_zero_iff.1 hw.1)).continuousAt.continuousWithinAt

/-- Entire case. -/
theorem bernsteinHyp_of_differentiable {f : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ) (hf : Differentiable ℂ f)
    (hM : ∀ w : ℂ, ‖w‖ = ρ → ‖f (joukowski w)‖ ≤ M) : BernsteinHyp f ρ M :=
  bernsteinHyp_of_differentiableOn hρ isOpen_univ hf.differentiableOn (fun _ _ _ => mem_univ _) hM

/-! ### Continuous dependence of the coefficients on a parameter -/

lemma continuous_outerCoeff {S : Type*} [TopologicalSpace S] {G : S → ℂ → ℂ}
    (hG : Continuous fun p : S × ℂ => G p.1 p.2) {R : ℝ} (hR : R ≠ 0) (k : ℕ) :
    Continuous fun s => outerCoeff (G s) R k := by
  unfold outerCoeff circleIntegral
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (s : S) (θ : ℝ) => deriv (circleMap 0 R) θ •
      ((circleMap 0 R θ ^ (k + 1))⁻¹ * G s (circleMap 0 R θ))) ?_ 0 (2 * π)
  have hc : Continuous fun p : S × ℝ => circleMap 0 R p.2 := (continuous_circleMap 0 R).comp continuous_snd
  have hne : ∀ p : S × ℝ, circleMap 0 R p.2 ≠ 0 := fun p => by
    simp [circleMap, hR]
  simp only [deriv_circleMap, smul_eq_mul]
  refine hc.mul continuous_const |>.mul ?_
  refine Continuous.mul ?_ ?_
  · exact (hc.pow _).inv₀ fun p => pow_ne_zero _ (hne p)
  · exact hG.comp (continuous_fst.prodMk hc)

lemma continuous_innerCoeff {S : Type*} [TopologicalSpace S] {G : S → ℂ → ℂ}
    (hG : Continuous fun p : S × ℂ => G p.1 p.2) (r : ℝ) (k : ℕ) :
    Continuous fun s => innerCoeff (G s) r k := by
  unfold innerCoeff circleIntegral
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (s : S) (θ : ℝ) => deriv (circleMap 0 r) θ •
      (circleMap 0 r θ ^ k * G s (circleMap 0 r θ))) ?_ 0 (2 * π)
  have hc : Continuous fun p : S × ℝ => circleMap 0 r p.2 := (continuous_circleMap 0 r).comp continuous_snd
  simp only [deriv_circleMap, smul_eq_mul]
  exact (hc.mul continuous_const).mul ((hc.pow _).mul (hG.comp (continuous_fst.prodMk hc)))

lemma continuous_chebCoeff {S : Type*} [TopologicalSpace S] {G : S → ℂ → ℂ}
    (hG : Continuous fun p : S × ℂ => G p.1 p.2) {ρ : ℝ} (hρ : ρ ≠ 0) (k : ℕ) :
    Continuous fun s => chebCoeff (G s) ρ k := by
  cases k with
  | zero => simpa [chebCoeff] using continuous_outerCoeff hG hρ 0
  | succ k =>
    exact Continuous.add (continuous_outerCoeff hG hρ (k + 1)) (continuous_innerCoeff hG ρ⁻¹ k)


/-- info: 'FormalResearch.Chebyshev.annulus_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Chebyshev.annulus_cauchy

/-- info: 'FormalResearch.Chebyshev.BernsteinHyp.error_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Chebyshev.BernsteinHyp.error_real

/-- info: 'FormalResearch.Chebyshev.BernsteinHyp.norm_chebCoeff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Chebyshev.BernsteinHyp.norm_chebCoeff_le

/-- info: 'FormalResearch.Chebyshev.BernsteinHyp.error_real_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Chebyshev.BernsteinHyp.error_real_re

/-- info: 'FormalResearch.Chebyshev.bernsteinHyp_of_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Chebyshev.bernsteinHyp_of_differentiable

/-- info: 'FormalResearch.Chebyshev.continuous_chebCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Chebyshev.continuous_chebCoeff

end FormalResearch.Chebyshev
