module

public import FormalResearch.SignUncertainty.FineOrderSigned
public import FormalResearch.SignUncertainty.CtChartTaylor

/-!
# Even/odd Cauchy splitting into `HalfCubicData` for `(ct:K-signed)`

Splits any holomorphic family `B_n(s, a) = (1 + (s^2 + a) Q(s, a)) E_b(n, s, a)` on `ball 0 r_s × ball 0 r_a`
satisfying `B_n(-x, a) = conj(B_n(x, a))` for real `x, a` into:
* `E_n(q, a) = (2πi)⁻¹ ∮_{|ζ|=r₀} (ζ / (ζ^2 - q)) B_n(ζ, a) dζ`,
* `O_n(q, a) = (2πi)⁻¹ ∮_{|ζ|=r₀} (-i / (ζ^2 - q)) B_n(ζ, a) dζ`,
yielding a `FineOrderSigned.HalfCubicData` instance with `E_n(-a, a) - 1 = O(n⁻¹)` and `O_n(-a, a) = O(n⁻¹)`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.FineOrderSigned

section Helpers

/-- If `g` is holomorphic on `ball 0 r` (`0 < r`) and real on `(0, r)`, then `g` is real on `(-r, r)`. -/
theorem im_zero_on_ball_of_pos_real {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball 0 r))
    (hreal : ∀ q : ℝ, 0 < q → q < r → (g (q : ℂ)).im = 0) :
    ∀ q : ℝ, |q| < r → (g (q : ℂ)).im = 0 := by
  let h : ℂ → ℂ := fun z => starRingEnd ℂ (g (starRingEnd ℂ z))
  have hh : DifferentiableOn ℂ h (ball 0 r) := by
    intro z hz
    have hzc : starRingEnd ℂ z ∈ ball (0 : ℂ) r := by
      simpa [mem_ball_zero_iff] using hz
    have hdz := (hg (starRingEnd ℂ z) hzc).differentiableAt (isOpen_ball.mem_nhds hzc)
    have hconj := (CtChart.hasDerivAt_conj_conj hdz.hasDerivAt).differentiableAt
    simpa [h, Complex.conj_conj] using hconj.differentiableWithinAt
  have hgAn : AnalyticOnNhd ℂ g (ball 0 r) := hg.analyticOnNhd isOpen_ball
  have hhAn : AnalyticOnNhd ℂ h (ball 0 r) := hh.analyticOnNhd isOpen_ball
  set z₀ : ℂ := ((r / 2 : ℝ) : ℂ)
  have hz₀ : z₀ ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, g z = h z := by
    rw [frequently_nhdsWithin_iff, Filter.frequently_iff]
    intro U hU
    obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp hU
    set ε' : ℝ := min (δ / 2) (r / 4)
    have hε'0 : 0 < ε' := lt_min (half_pos hδ0) (by linarith)
    set q : ℝ := r / 2 + ε'
    have hq_pos : 0 < q := by dsimp [q]; linarith only [hr, hε'0]
    have hq_lt : q < r := by
      have h1 : ε' ≤ r / 4 := min_le_right _ _
      dsimp [q]; linarith only [h1, hr]
    have hq_mem : (q : ℂ) ∈ U := hδ (by
      rw [mem_ball, dist_eq_norm]
      have hsub : (q : ℂ) - z₀ = (ε' : ℂ) := by push_cast [q, z₀]; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε'0]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ0))
    refine ⟨(q : ℂ), hq_mem, ?_, ?_⟩
    · have him : (g (q : ℂ)).im = 0 := hreal q hq_pos hq_lt
      have hconj_g : starRingEnd ℂ (g (q : ℂ)) = g (q : ℂ) := Complex.conj_eq_iff_im.2 him
      dsimp [h]
      rw [Complex.conj_ofReal, hconj_g]
    · intro heq
      have hqr : q = r / 2 := Complex.ofReal_injective heq
      dsimp [q] at hqr; linarith only [hqr, hε'0]
  have heq : EqOn g h (ball 0 r) :=
    hgAn.eqOn_of_preconnected_of_frequently_eq hhAn (convex_ball 0 r).isPreconnected hz₀ hfreq
  intro q hq
  have hqb : (q : ℂ) ∈ ball (0 : ℂ) r := by
    simpa [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hq
  have hgq := heq hqb
  dsimp [h] at hgq
  rw [Complex.conj_ofReal] at hgq
  exact Complex.conj_eq_iff_im.1 hgq.symm

end Helpers

/-! ### Even and odd Cauchy transforms -/

/-- Even Cauchy projection `E(q, a) = (2πi)⁻¹ ∮_{|ζ|=r₀} (ζ / (ζ² - q)) B(ζ, a) dζ`. -/
noncomputable def evenCauchy (B : ℂ → ℂ → ℂ) (r₀ : ℝ) (q a : ℂ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, r₀), (ζ / (ζ ^ 2 - q)) • B ζ a

/-- Odd Cauchy projection `O(q, a) = (2πi)⁻¹ ∮_{|ζ|=r₀} (-i / (ζ² - q)) B(ζ, a) dζ`. -/
noncomputable def oddCauchy (B : ℂ → ℂ → ℂ) (r₀ : ℝ) (q a : ℂ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, r₀), (-Complex.I / (ζ ^ 2 - q)) • B ζ a

private lemma sq_sub_norm_ge {ζ q : ℂ} {r₀ : ℝ} (hζ : ζ ∈ sphere (0 : ℂ) r₀)
    (hq : q ∈ ball (0 : ℂ) (r₀ ^ 2 / 2)) :
    r₀ ^ 2 / 2 ≤ ‖ζ ^ 2 - q‖ := by
  have hζn : ‖ζ‖ = r₀ := mem_sphere_zero_iff_norm.1 hζ
  have hqn : ‖q‖ < r₀ ^ 2 / 2 := mem_ball_zero_iff.1 hq
  have hsq : ‖ζ ^ 2‖ = r₀ ^ 2 := by rw [norm_pow, hζn]
  linarith [norm_sub_norm_le (ζ ^ 2) q]

lemma evenCauchy_norm_le {B : ℂ → ℂ → ℂ} {r₀ M_B : ℝ} (hr₀ : 0 < r₀)
    (hbd : ∀ ζ ∈ sphere (0 : ℂ) r₀, ∀ a ∈ ball (0 : ℂ) r₀, True)
    {q a : ℂ} (hq : q ∈ ball (0 : ℂ) (r₀ ^ 2 / 2))
    (hMa : ∀ ζ ∈ sphere (0 : ℂ) r₀, ‖B ζ a‖ ≤ M_B) :
    ‖evenCauchy B r₀ q a‖ ≤ 2 * M_B := by
  have _ := hbd
  have hr2 : 0 < r₀ ^ 2 / 2 := by positivity
  have hM0 : 0 ≤ M_B := (norm_nonneg (B (r₀ : ℂ) a)).trans
    (hMa r₀ (mem_sphere_zero_iff_norm.2 (by simp [abs_of_pos hr₀])))
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr₀.le
    (C := (2 / r₀) * M_B) fun ζ hζ => ?_).trans_eq (by field_simp [hr₀.ne'])
  have hζn : ‖ζ‖ = r₀ := mem_sphere_zero_iff_norm.1 hζ
  have hden := sq_sub_norm_ge hζ hq
  rw [norm_smul, norm_div, hζn]
  refine mul_le_mul ?_ (hMa ζ hζ) (norm_nonneg _) (by positivity)
  rw [div_le_div_iff₀ (lt_of_lt_of_le hr2 hden) hr₀]
  linarith

lemma evenCauchy_norm_le' {B : ℂ → ℂ → ℂ} {r₀ M_B : ℝ} (hr₀ : 0 < r₀)
    {q a : ℂ} (hq : q ∈ ball (0 : ℂ) (r₀ ^ 2 / 2))
    (hMa : ∀ ζ ∈ sphere (0 : ℂ) r₀, ‖B ζ a‖ ≤ M_B) :
    ‖evenCauchy B r₀ q a‖ ≤ 2 * M_B :=
  evenCauchy_norm_le hr₀ (fun _ _ _ _ => trivial) hq hMa

lemma oddCauchy_norm_le {B : ℂ → ℂ → ℂ} {r₀ M_B : ℝ} (hr₀ : 0 < r₀)
    {q a : ℂ} (hq : q ∈ ball (0 : ℂ) (r₀ ^ 2 / 2))
    (hMa : ∀ ζ ∈ sphere (0 : ℂ) r₀, ‖B ζ a‖ ≤ M_B) :
    ‖oddCauchy B r₀ q a‖ ≤ (2 / r₀) * M_B := by
  have hr2 : 0 < r₀ ^ 2 / 2 := by positivity
  have hM0 : 0 ≤ M_B := (norm_nonneg (B (r₀ : ℂ) a)).trans
    (hMa r₀ (mem_sphere_zero_iff_norm.2 (by simp [abs_of_pos hr₀])))
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr₀.le
    (C := (2 / r₀ ^ 2) * M_B) fun ζ hζ => ?_).trans_eq (by field_simp [hr₀.ne'])
  have hden := sq_sub_norm_ge hζ hq
  rw [norm_smul, norm_div, norm_neg, Complex.norm_I]
  refine mul_le_mul ?_ (hMa ζ hζ) (norm_nonneg _) (by positivity)
  rw [div_le_div_iff₀ (lt_of_lt_of_le hr2 hden) (pow_pos hr₀ 2)]
  linarith

lemma differentiableOn_evenCauchy_q {B : ℂ → ℂ → ℂ} {r₀ r_s r_a M_B : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s)
    (hBq : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => B ζ a) (ball 0 r_s))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) r₀, ∀ a ∈ ball (0 : ℂ) r_a, ‖B ζ a‖ ≤ M_B)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) r_a) :
    DifferentiableOn ℂ (fun q => evenCauchy B r₀ q a) (ball 0 (r₀ ^ 2 / 2)) := by
  refine differentiableOn_circleIntegral_param hr₀ (M := (2 / r₀) * M_B) ?_ ?_ ?_
  · intro q hq
    have hBc : ContinuousOn (fun ζ => B ζ a) (sphere 0 r₀) :=
      (hBq a ha).continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀s))
    have hkc : ContinuousOn (fun ζ : ℂ => ζ / (ζ ^ 2 - q)) (sphere 0 r₀) := by
      refine continuousOn_id.div ((continuousOn_id.pow 2).sub continuousOn_const) fun ζ hζ => ?_
      have hden := sq_sub_norm_ge hζ hq
      exact norm_ne_zero_iff.1 (by linarith [sq_pos_of_pos hr₀])
    exact hkc.smul hBc
  · intro ζ hζ
    have hcon : DifferentiableOn ℂ (fun q => (ζ / (ζ ^ 2 - q)) * B ζ a) (ball 0 (r₀ ^ 2 / 2)) :=
      ((differentiableOn_const ζ).div ((differentiableOn_const (ζ ^ 2)).sub differentiableOn_id)
        fun q hq => by
          dsimp
          have hden := sq_sub_norm_ge hζ hq
          exact norm_ne_zero_iff.1 (by linarith [sq_pos_of_pos hr₀])).mul (differentiableOn_const (B ζ a))
    simpa only [smul_eq_mul] using hcon
  · intro ζ hζ q hq
    have hζn : ‖ζ‖ = r₀ := mem_sphere_zero_iff_norm.1 hζ
    have hden := sq_sub_norm_ge hζ hq
    have hden0 : 0 < ‖ζ ^ 2 - q‖ := lt_of_lt_of_le (by positivity) hden
    rw [norm_smul, norm_div, hζn]
    refine mul_le_mul ?_ (hM ζ hζ a ha) (norm_nonneg _) (by positivity)
    rw [div_le_div_iff₀ hden0 hr₀]; linarith

lemma differentiableOn_oddCauchy_q {B : ℂ → ℂ → ℂ} {r₀ r_s r_a M_B : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s)
    (hBq : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => B ζ a) (ball 0 r_s))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) r₀, ∀ a ∈ ball (0 : ℂ) r_a, ‖B ζ a‖ ≤ M_B)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) r_a) :
    DifferentiableOn ℂ (fun q => oddCauchy B r₀ q a) (ball 0 (r₀ ^ 2 / 2)) := by
  refine differentiableOn_circleIntegral_param hr₀ (M := (2 / r₀ ^ 2) * M_B) ?_ ?_ ?_
  · intro q hq
    have hBc : ContinuousOn (fun ζ => B ζ a) (sphere 0 r₀) :=
      (hBq a ha).continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀s))
    have hkc : ContinuousOn (fun ζ : ℂ => -Complex.I / (ζ ^ 2 - q)) (sphere 0 r₀) := by
      refine continuousOn_const.div ((continuousOn_id.pow 2).sub continuousOn_const) fun ζ hζ => ?_
      have hden := sq_sub_norm_ge hζ hq
      exact norm_ne_zero_iff.1 (by linarith [sq_pos_of_pos hr₀])
    exact hkc.smul hBc
  · intro ζ hζ
    have hcon : DifferentiableOn ℂ (fun q => (-Complex.I / (ζ ^ 2 - q)) * B ζ a) (ball 0 (r₀ ^ 2 / 2)) :=
      ((differentiableOn_const (-Complex.I)).div ((differentiableOn_const (ζ ^ 2)).sub differentiableOn_id)
        fun q hq => by
          dsimp
          have hden := sq_sub_norm_ge hζ hq
          exact norm_ne_zero_iff.1 (by linarith [sq_pos_of_pos hr₀])).mul (differentiableOn_const (B ζ a))
    simpa only [smul_eq_mul] using hcon
  · intro ζ hζ q hq
    have hden := sq_sub_norm_ge hζ hq
    have hden0 : 0 < ‖ζ ^ 2 - q‖ := lt_of_lt_of_le (by positivity) hden
    rw [norm_smul, norm_div, norm_neg, Complex.norm_I]
    refine mul_le_mul ?_ (hM ζ hζ a ha) (norm_nonneg _) (by positivity)
    rw [div_le_div_iff₀ hden0 (pow_pos hr₀ 2)]; linarith

lemma differentiableOn_evenCauchy_a {B : ℂ → ℂ → ℂ} {r₀ r_s r_a M_B : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s)
    (hBq : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => B ζ a) (ball 0 r_s))
    (hBa : ∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (B ζ) (ball 0 r_a))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) r₀, ∀ a ∈ ball (0 : ℂ) r_a, ‖B ζ a‖ ≤ M_B)
    {q : ℂ} (hq : q ∈ ball (0 : ℂ) (r₀ ^ 2 / 2)) :
    DifferentiableOn ℂ (fun a => evenCauchy B r₀ q a) (ball 0 r_a) := by
  refine differentiableOn_circleIntegral_param hr₀ (M := (2 / r₀) * M_B) ?_ ?_ ?_
  · intro a ha
    have hBc : ContinuousOn (fun ζ => B ζ a) (sphere 0 r₀) :=
      (hBq a ha).continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀s))
    have hkc : ContinuousOn (fun ζ : ℂ => ζ / (ζ ^ 2 - q)) (sphere 0 r₀) := by
      refine continuousOn_id.div ((continuousOn_id.pow 2).sub continuousOn_const) fun ζ hζ => ?_
      have hden := sq_sub_norm_ge hζ hq
      exact norm_ne_zero_iff.1 (by linarith [sq_pos_of_pos hr₀])
    exact hkc.smul hBc
  · intro ζ hζ
    have hζs : ζ ∈ ball (0 : ℂ) r_s := by
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.1 hζ]; exact hr₀s
    exact (differentiableOn_const (ζ / (ζ ^ 2 - q))).smul (hBa ζ hζs)
  · intro ζ hζ a ha
    have hζn : ‖ζ‖ = r₀ := mem_sphere_zero_iff_norm.1 hζ
    have hden := sq_sub_norm_ge hζ hq
    have hden0 : 0 < ‖ζ ^ 2 - q‖ := lt_of_lt_of_le (by positivity) hden
    rw [norm_smul, norm_div, hζn]
    refine mul_le_mul ?_ (hM ζ hζ a ha) (norm_nonneg _) (by positivity)
    rw [div_le_div_iff₀ hden0 hr₀]; linarith

lemma differentiableOn_oddCauchy_a {B : ℂ → ℂ → ℂ} {r₀ r_s r_a M_B : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s)
    (hBq : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => B ζ a) (ball 0 r_s))
    (hBa : ∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (B ζ) (ball 0 r_a))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) r₀, ∀ a ∈ ball (0 : ℂ) r_a, ‖B ζ a‖ ≤ M_B)
    {q : ℂ} (hq : q ∈ ball (0 : ℂ) (r₀ ^ 2 / 2)) :
    DifferentiableOn ℂ (fun a => oddCauchy B r₀ q a) (ball 0 r_a) := by
  refine differentiableOn_circleIntegral_param hr₀ (M := (2 / r₀ ^ 2) * M_B) ?_ ?_ ?_
  · intro a ha
    have hBc : ContinuousOn (fun ζ => B ζ a) (sphere 0 r₀) :=
      (hBq a ha).continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀s))
    have hkc : ContinuousOn (fun ζ : ℂ => -Complex.I / (ζ ^ 2 - q)) (sphere 0 r₀) := by
      refine continuousOn_const.div ((continuousOn_id.pow 2).sub continuousOn_const) fun ζ hζ => ?_
      have hden := sq_sub_norm_ge hζ hq
      exact norm_ne_zero_iff.1 (by linarith [sq_pos_of_pos hr₀])
    exact hkc.smul hBc
  · intro ζ hζ
    have hζs : ζ ∈ ball (0 : ℂ) r_s := by
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.1 hζ]; exact hr₀s
    exact (differentiableOn_const (-Complex.I / (ζ ^ 2 - q))).smul (hBa ζ hζs)
  · intro ζ hζ a ha
    have hden := sq_sub_norm_ge hζ hq
    have hden0 : 0 < ‖ζ ^ 2 - q‖ := lt_of_lt_of_le (by positivity) hden
    rw [norm_smul, norm_div, norm_neg, Complex.norm_I]
    refine mul_le_mul ?_ (hM ζ hζ a ha) (norm_nonneg _) (by positivity)
    rw [div_le_div_iff₀ hden0 (pow_pos hr₀ 2)]; linarith

/-- Fundamental reconstruction identity: `E(s^2, a) + i s O(s^2, a) = B(s, a)` for `‖s‖ < r₀`. -/
theorem evenCauchy_add_oddCauchy {B : ℂ → ℂ → ℂ} {r₀ r_s : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s) {a : ℂ}
    (hBq : DifferentiableOn ℂ (fun ζ => B ζ a) (ball 0 r_s))
    {s : ℂ} (hs : ‖s‖ < r₀) :
    evenCauchy B r₀ (s ^ 2) a + Complex.I * s * oddCauchy B r₀ (s ^ 2) a = B s a := by
  have hBc : ContinuousOn (fun ζ => B ζ a) (sphere 0 r₀) :=
    hBq.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀s))
  have hne : ∀ ζ ∈ sphere (0 : ℂ) r₀, ζ ^ 2 - s ^ 2 ≠ 0 := fun ζ hζ => by
    have hζn : ‖ζ‖ = r₀ := mem_sphere_zero_iff_norm.1 hζ
    have h1 : r₀ ^ 2 - ‖s‖ ^ 2 ≤ ‖ζ ^ 2 - s ^ 2‖ := by
      have := norm_sub_norm_le (ζ ^ 2) (s ^ 2)
      rw [norm_pow, norm_pow, hζn] at this
      exact this
    have hpos : 0 < r₀ ^ 2 - ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
    exact norm_ne_zero_iff.1 (by linarith)
  have hne_sub : ∀ ζ ∈ sphere (0 : ℂ) r₀, ζ - s ≠ 0 := fun ζ hζ => by
    have hζn : ‖ζ‖ = r₀ := mem_sphere_zero_iff_norm.1 hζ
    have h1 := norm_sub_norm_le ζ s
    rw [hζn] at h1
    exact norm_ne_zero_iff.1 (by linarith)
  have hne_add : ∀ ζ ∈ sphere (0 : ℂ) r₀, ζ + s ≠ 0 := fun ζ hζ => by
    have hζn : ‖ζ‖ = r₀ := mem_sphere_zero_iff_norm.1 hζ
    have h1 := norm_sub_norm_le ζ (-s)
    rw [hζn, norm_neg, sub_neg_eq_add] at h1
    exact norm_ne_zero_iff.1 (by linarith)
  have hi1 : CircleIntegrable (fun ζ => (ζ / (ζ ^ 2 - s ^ 2)) • B ζ a) 0 r₀ :=
    ((continuousOn_id.div ((continuousOn_id.pow 2).sub continuousOn_const) hne).smul hBc).circleIntegrable
      hr₀.le
  have hi2 : CircleIntegrable (fun ζ => (-Complex.I / (ζ ^ 2 - s ^ 2)) • B ζ a) 0 r₀ :=
    ((continuousOn_const.div ((continuousOn_id.pow 2).sub continuousOn_const) hne).smul hBc).circleIntegrable
      hr₀.le
  have hi2' : CircleIntegrable (fun ζ => (Complex.I * s) • ((-Complex.I / (ζ ^ 2 - s ^ 2)) • B ζ a)) 0 r₀ := by
    have hc : ContinuousOn (fun ζ => (Complex.I * s) • ((-Complex.I / (ζ ^ 2 - s ^ 2)) • B ζ a)) (sphere 0 r₀) :=
      (continuousOn_const : ContinuousOn (fun _ : ℂ => Complex.I * s) (sphere 0 r₀)).smul
        (((continuousOn_const : ContinuousOn (fun _ : ℂ => -Complex.I) (sphere 0 r₀)).div
          ((continuousOn_id.pow 2).sub continuousOn_const) hne).smul hBc)
    exact hc.circleIntegrable hr₀.le
  have hsmul : Complex.I * s * oddCauchy B r₀ (s ^ 2) a =
      (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, r₀), (Complex.I * s) • ((-Complex.I / (ζ ^ 2 - s ^ 2)) • B ζ a) := by
    unfold oddCauchy
    rw [← smul_eq_mul, smul_comm, ← circleIntegral.integral_smul]
  unfold evenCauchy
  rw [hsmul, ← smul_add, ← circleIntegral.integral_add hi1 hi2']
  have hcongr : ∮ ζ in C(0, r₀),
        ((ζ / (ζ ^ 2 - s ^ 2)) • B ζ a + (Complex.I * s) • ((-Complex.I / (ζ ^ 2 - s ^ 2)) • B ζ a)) =
      ∮ ζ in C(0, r₀), (ζ - s)⁻¹ • B ζ a := by
    refine circleIntegral.integral_congr hr₀.le fun ζ hζ => ?_
    have h1 := hne ζ hζ
    have h2 := hne_add ζ hζ
    have h3 := hne_sub ζ hζ
    simp only [smul_eq_mul]
    have halg : ζ / (ζ ^ 2 - s ^ 2) + Complex.I * s * (-Complex.I / (ζ ^ 2 - s ^ 2)) = (ζ - s)⁻¹ := by
      have hsq : ζ ^ 2 - s ^ 2 = (ζ - s) * (ζ + s) := by ring
      have hii : Complex.I * s * -Complex.I = s := by
        calc Complex.I * s * -Complex.I = -(Complex.I * Complex.I) * s := by ring
          _ = s := by rw [Complex.I_mul_I]; ring
      rw [mul_div_assoc', hii, ← add_div, hsq]
      field_simp [h2, h3]
    calc (ζ / (ζ ^ 2 - s ^ 2)) * B ζ a + (Complex.I * s) * ((-Complex.I / (ζ ^ 2 - s ^ 2)) * B ζ a)
        = (ζ / (ζ ^ 2 - s ^ 2) + Complex.I * s * (-Complex.I / (ζ ^ 2 - s ^ 2))) * B ζ a := by ring
      _ = (ζ - s)⁻¹ * B ζ a := by rw [halg]
  rw [hcongr]
  have hci := (hBq.mono (closedBall_subset_ball hr₀s)).circleIntegral_sub_inv_smul (mem_ball_zero_iff.2 hs)
  rw [hci, inv_smul_smul₀ (by simp [Real.pi_ne_zero])]

theorem evenCauchy_sub_oddCauchy {B : ℂ → ℂ → ℂ} {r₀ r_s : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s) {a : ℂ}
    (hBq : DifferentiableOn ℂ (fun ζ => B ζ a) (ball 0 r_s))
    {s : ℂ} (hs : ‖s‖ < r₀) :
    evenCauchy B r₀ (s ^ 2) a - Complex.I * s * oddCauchy B r₀ (s ^ 2) a = B (-s) a := by
  have hs' : ‖-s‖ < r₀ := by simpa using hs
  have h := evenCauchy_add_oddCauchy hr₀ hr₀s hBq hs'
  rw [neg_sq] at h
  convert h using 1; ring

lemma oddCauchy_const_zero {r₀ : ℝ} (hr₀ : 0 < r₀) {q a : ℂ} (hq : q ∈ ball (0 : ℂ) (r₀ ^ 2 / 2)) :
    oddCauchy (fun _ _ => (1 : ℂ)) r₀ q a = 0 := by
  have hdiff : DifferentiableOn ℂ (fun q' => oddCauchy (fun _ _ => (1 : ℂ)) r₀ q' a)
      (ball 0 (r₀ ^ 2 / 2)) :=
    differentiableOn_oddCauchy_q (r_s := r₀ + 1) (r_a := ‖a‖ + 1) (M_B := 1) hr₀ (by linarith)
      (fun _ _ => differentiableOn_const (1 : ℂ)) (fun _ _ _ _ => by simp)
      (mem_ball_zero_iff.2 (by linarith [norm_nonneg a]))
  have hne0 : ∀ q' : ℂ, q' ∈ ball (0 : ℂ) (r₀ ^ 2 / 2) → q' ≠ 0 →
      oddCauchy (fun _ _ => (1 : ℂ)) r₀ q' a = 0 := by
    intro q' _ hq0
    let s : ℂ := Complex.exp (Complex.log q' / 2)
    have hs2 : s ^ 2 = q' := by
      dsimp [s]
      rw [← Complex.exp_nat_mul]
      simp only [Nat.cast_ofNat]
      rw [show (2 : ℂ) * (Complex.log q' / 2) = Complex.log q' by ring]
      exact Complex.exp_log hq0
    have hs_norm : ‖s‖ < r₀ := by
      have hsq : ‖s‖ ^ 2 < r₀ ^ 2 := by
        rw [← norm_pow, hs2]
        have hq' : ‖q'‖ < r₀ ^ 2 / 2 := mem_ball_zero_iff.1 ‹_›
        linarith [sq_pos_of_pos hr₀]
      nlinarith [norm_nonneg s, hr₀]
    have hp := evenCauchy_add_oddCauchy (B := fun _ _ => (1 : ℂ)) (a := a) hr₀ (by linarith : r₀ < r₀ + 1)
      (differentiableOn_const (1 : ℂ)) hs_norm
    have hm := evenCauchy_sub_oddCauchy (B := fun _ _ => (1 : ℂ)) (a := a) hr₀ (by linarith : r₀ < r₀ + 1)
      (differentiableOn_const (1 : ℂ)) hs_norm
    rw [hs2] at hp hm
    have hsne : s ≠ 0 := Complex.exp_ne_zero _
    have hmul : (2 * Complex.I * s) * oddCauchy (fun _ _ => (1 : ℂ)) r₀ q' a = 0 := by
      linear_combination hp - hm
    exact (mul_eq_zero.1 hmul).resolve_left (by simp [hsne])
  by_cases hq0 : q = 0
  · subst hq0
    have hseq : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) * (r₀ ^ 2 / 4) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * (r₀ ^ 2 / 4)) atTop (𝓝 (0 * (r₀ ^ 2 / 4))) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _
      rw [zero_mul] at h1
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp h1
    have h0' : Tendsto (fun n : ℕ => oddCauchy (fun _ _ => (1 : ℂ)) r₀
        ((1 / ((n : ℝ) + 1) * (r₀ ^ 2 / 4) : ℝ) : ℂ) a) atTop
        (𝓝 (oddCauchy (fun _ _ => (1 : ℂ)) r₀ 0 a)) :=
      (hdiff.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))).tendsto.comp hseq
    have hev : (fun n : ℕ => oddCauchy (fun _ _ => (1 : ℂ)) r₀
        ((1 / ((n : ℝ) + 1) * (r₀ ^ 2 / 4) : ℝ) : ℂ) a) =ᶠ[atTop] fun _ => 0 := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n _
      have hpos : 0 < 1 / ((n : ℝ) + 1) * (r₀ ^ 2 / 4) := by positivity
      have hle : 1 / ((n : ℝ) + 1) * (r₀ ^ 2 / 4) ≤ r₀ ^ 2 / 4 := by
        have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
        nlinarith [sq_pos_of_pos hr₀]
      have hmem : ((1 / ((n : ℝ) + 1) * (r₀ ^ 2 / 4) : ℝ) : ℂ) ∈ ball (0 : ℂ) (r₀ ^ 2 / 2) := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
        linarith [sq_pos_of_pos hr₀]
      exact hne0 _ hmem (Complex.ofReal_ne_zero.2 hpos.ne')
    exact tendsto_nhds_unique h0' (tendsto_const_nhds.congr' hev.symm)
  · exact hne0 q hq hq0

theorem evenCauchy_real_of_symm {B : ℂ → ℂ → ℂ} {r₀ r_s r_a M_B : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s)
    (hBq : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => B ζ a) (ball 0 r_s))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) r₀, ∀ a ∈ ball (0 : ℂ) r_a, ‖B ζ a‖ ≤ M_B)
    (hsym : ∀ (x a : ℝ), |x| < r_s → |a| < r_a → B (-(x : ℂ)) (a : ℂ) = starRingEnd ℂ (B (x : ℂ) (a : ℂ)))
    {q a : ℝ} (hq : |q| < r₀ ^ 2 / 2) (ha : |a| < r_a) :
    (evenCauchy B r₀ (q : ℂ) (a : ℂ)).im = 0 := by
  have haC : (a : ℂ) ∈ ball (0 : ℂ) r_a := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using ha
  refine im_zero_on_ball_of_pos_real (by positivity : 0 < r₀ ^ 2 / 2)
    (differentiableOn_evenCauchy_q hr₀ hr₀s hBq hM haC) (fun q' hq0 hq_lt => ?_) q hq
  have hsq_r : Real.sqrt q' < r₀ := by
    have : Real.sqrt q' < Real.sqrt (r₀ ^ 2) := Real.sqrt_lt_sqrt hq0.le (by linarith [sq_pos_of_pos hr₀])
    simpa [Real.sqrt_sq hr₀.le] using this
  have hs_mem : ‖((Real.sqrt q' : ℝ) : ℂ)‖ < r₀ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg q')] using hsq_r
  have hp := evenCauchy_add_oddCauchy hr₀ hr₀s (hBq (a : ℂ) haC) hs_mem
  have hm := evenCauchy_sub_oddCauchy hr₀ hr₀s (hBq (a : ℂ) haC) hs_mem
  have hsqC : ((Real.sqrt q' : ℝ) : ℂ) ^ 2 = (q' : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq0.le]
  rw [hsqC] at hp hm
  have hneg : B (-((Real.sqrt q' : ℝ) : ℂ)) (a : ℂ) = starRingEnd ℂ (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ)) :=
    hsym (Real.sqrt q') a (by rw [abs_of_nonneg (Real.sqrt_nonneg q')]; linarith) ha
  have h2E : evenCauchy B r₀ (q' : ℂ) (a : ℂ) =
      (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ) + starRingEnd ℂ (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ))) / 2 := by
    rw [← hneg]; linear_combination (hp + hm) / 2
  rw [h2E]
  simp

theorem oddCauchy_real_of_symm {B : ℂ → ℂ → ℂ} {r₀ r_s r_a M_B : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s)
    (hBq : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => B ζ a) (ball 0 r_s))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) r₀, ∀ a ∈ ball (0 : ℂ) r_a, ‖B ζ a‖ ≤ M_B)
    (hsym : ∀ (x a : ℝ), |x| < r_s → |a| < r_a → B (-(x : ℂ)) (a : ℂ) = starRingEnd ℂ (B (x : ℂ) (a : ℂ)))
    {q a : ℝ} (hq : |q| < r₀ ^ 2 / 2) (ha : |a| < r_a) :
    (oddCauchy B r₀ (q : ℂ) (a : ℂ)).im = 0 := by
  have haC : (a : ℂ) ∈ ball (0 : ℂ) r_a := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using ha
  refine im_zero_on_ball_of_pos_real (by positivity : 0 < r₀ ^ 2 / 2)
    (differentiableOn_oddCauchy_q hr₀ hr₀s hBq hM haC) (fun q' hq0 hq_lt => ?_) q hq
  have hsq_r : Real.sqrt q' < r₀ := by
    have : Real.sqrt q' < Real.sqrt (r₀ ^ 2) := Real.sqrt_lt_sqrt hq0.le (by linarith [sq_pos_of_pos hr₀])
    simpa [Real.sqrt_sq hr₀.le] using this
  have hs_mem : ‖((Real.sqrt q' : ℝ) : ℂ)‖ < r₀ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg q')] using hsq_r
  have hp := evenCauchy_add_oddCauchy hr₀ hr₀s (hBq (a : ℂ) haC) hs_mem
  have hm := evenCauchy_sub_oddCauchy hr₀ hr₀s (hBq (a : ℂ) haC) hs_mem
  have hsqC : ((Real.sqrt q' : ℝ) : ℂ) ^ 2 = (q' : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq0.le]
  rw [hsqC] at hp hm
  have hneg : B (-((Real.sqrt q' : ℝ) : ℂ)) (a : ℂ) = starRingEnd ℂ (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ)) :=
    hsym (Real.sqrt q') a (by rw [abs_of_nonneg (Real.sqrt_nonneg q')]; linarith) ha
  have hsr0 : Real.sqrt q' ≠ 0 := (Real.sqrt_pos.2 hq0).ne'
  have h2O : oddCauchy B r₀ (q' : ℂ) (a : ℂ) =
      (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ) - starRingEnd ℂ (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ))) /
        (2 * Complex.I * ((Real.sqrt q' : ℝ) : ℂ)) := by
    have hmul : oddCauchy B r₀ (q' : ℂ) (a : ℂ) * (2 * Complex.I * ((Real.sqrt q' : ℝ) : ℂ)) =
        B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ) - starRingEnd ℂ (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ)) := by
      rw [← hneg]; linear_combination hp - hm
    exact eq_div_of_mul_eq (by simp [hsr0]) hmul
  rw [h2O]
  have hdiff_I : (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ) - starRingEnd ℂ (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ))) =
      ((2 * (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ)).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp; ring
  rw [hdiff_I]
  have hval : ((2 * (B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ)).im : ℝ) : ℂ) * Complex.I /
        (2 * Complex.I * ((Real.sqrt q' : ℝ) : ℂ)) =
      (((B ((Real.sqrt q' : ℝ) : ℂ) (a : ℂ)).im / Real.sqrt q' : ℝ) : ℂ) := by
    have hsc : ((Real.sqrt q' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsr0
    push_cast; field_simp [hsc]
  rw [hval, Complex.ofReal_im]

/-! ### Saddle bounds for product amplitudes `(1 + (s² + a) Q(s, a)) E_b(n, s, a)` -/

theorem evenCauchy_saddle_sub_one_le {Q Eb : ℂ → ℂ → ℂ} {r₀ r_s K_b n : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s) (_hn : 0 < n) {a : ℂ}
    (hQ : DifferentiableOn ℂ (fun ζ => Q ζ a) (ball 0 r_s))
    (hEb : DifferentiableOn ℂ (fun ζ => Eb ζ a) (ball 0 r_s))
    (hEb_bd : ∀ w ∈ ball (0 : ℂ) r₀, ‖Eb w a - 1‖ ≤ K_b * n⁻¹)
    (ha : ‖a‖ < r₀ ^ 2 / 4) :
    ‖evenCauchy (fun ζ a' => (1 + (ζ ^ 2 + a') * Q ζ a') * Eb ζ a') r₀ (-a) a - 1‖ ≤ K_b * n⁻¹ := by
  let B : ℂ → ℂ → ℂ := fun ζ a' => (1 + (ζ ^ 2 + a') * Q ζ a') * Eb ζ a'
  have hB : DifferentiableOn ℂ (fun ζ => B ζ a) (ball 0 r_s) :=
    (((differentiableOn_const (1 : ℂ)).add
      (((differentiableOn_id.pow 2).add (differentiableOn_const a)).mul hQ)).mul hEb)
  have hs_ex : ∃ s : ℂ, s ^ 2 = -a ∧ ‖s‖ < r₀ := by
    by_cases ha0 : a = 0
    · exact ⟨0, by simp [ha0], by simpa using hr₀⟩
    · refine ⟨Complex.exp (Complex.log (-a) / 2), ?_, ?_⟩
      · rw [← Complex.exp_nat_mul]
        simp only [Nat.cast_ofNat]
        rw [show (2 : ℂ) * (Complex.log (-a) / 2) = Complex.log (-a) by ring]
        exact Complex.exp_log (neg_ne_zero.2 ha0)
      · have hsq : ‖Complex.exp (Complex.log (-a) / 2)‖ ^ 2 < r₀ ^ 2 := by
          rw [← norm_pow, ← Complex.exp_nat_mul]
          simp only [Nat.cast_ofNat]
          rw [show (2 : ℂ) * (Complex.log (-a) / 2) = Complex.log (-a) by ring,
            Complex.exp_log (neg_ne_zero.2 ha0), norm_neg]
          linarith [sq_pos_of_pos hr₀]
        nlinarith [norm_nonneg (Complex.exp (Complex.log (-a) / 2)), hr₀]
  obtain ⟨s, hs2, hs_norm⟩ := hs_ex
  have hp := evenCauchy_add_oddCauchy hr₀ hr₀s hB hs_norm
  have hm := evenCauchy_sub_oddCauchy hr₀ hr₀s hB hs_norm
  rw [hs2] at hp hm
  have hE : evenCauchy B r₀ (-a) a - 1 = ((Eb s a - 1) + (Eb (-s) a - 1)) / 2 := by
    have hBs : B s a = Eb s a := by dsimp [B]; rw [hs2, neg_add_cancel, zero_mul, add_zero, one_mul]
    have hBms : B (-s) a = Eb (-s) a := by
      dsimp [B]; rw [neg_sq, hs2, neg_add_cancel, zero_mul, add_zero, one_mul]
    rw [hBs] at hp; rw [hBms] at hm
    linear_combination (hp + hm) / 2
  rw [hE, norm_div, Complex.norm_ofNat]
  have hs1 : s ∈ ball (0 : ℂ) r₀ := mem_ball_zero_iff.2 hs_norm
  have hs2' : -s ∈ ball (0 : ℂ) r₀ := mem_ball_zero_iff.2 (by simpa using hs_norm)
  calc ‖(Eb s a - 1) + (Eb (-s) a - 1)‖ / 2
      ≤ (‖Eb s a - 1‖ + ‖Eb (-s) a - 1‖) / 2 := div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ (K_b * n⁻¹ + K_b * n⁻¹) / 2 :=
        div_le_div_of_nonneg_right (add_le_add (hEb_bd s hs1) (hEb_bd (-s) hs2')) (by norm_num)
    _ = K_b * n⁻¹ := by ring

theorem oddCauchy_saddle_le {Q Eb : ℂ → ℂ → ℂ} {r₀ r_s K_b n : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ < r_s) (hn : 0 < n) {a : ℂ}
    (hQ : DifferentiableOn ℂ (fun ζ => Q ζ a) (ball 0 r_s))
    (hEb : DifferentiableOn ℂ (fun ζ => Eb ζ a) (ball 0 r_s))
    (hEb_bd : ∀ ζ ∈ sphere (0 : ℂ) r₀, ‖Eb ζ a - 1‖ ≤ K_b * n⁻¹)
    (ha : ‖a‖ < r₀ ^ 2 / 4) :
    ‖oddCauchy (fun ζ a' => (1 + (ζ ^ 2 + a') * Q ζ a') * Eb ζ a') r₀ (-a) a‖ ≤
      (4 / (3 * r₀)) * K_b * n⁻¹ := by
  let B : ℂ → ℂ → ℂ := fun ζ a' => (1 + (ζ ^ 2 + a') * Q ζ a') * Eb ζ a'
  have ha_ball : -a ∈ ball (0 : ℂ) (r₀ ^ 2 / 2) := by
    rw [mem_ball_zero_iff, norm_neg]; linarith [sq_pos_of_pos hr₀]
  have hden : ∀ ζ ∈ sphere (0 : ℂ) r₀, 3 / 4 * r₀ ^ 2 ≤ ‖ζ ^ 2 - (-a)‖ := fun ζ hζ => by
    have hζn : ‖ζ‖ = r₀ := mem_sphere_zero_iff_norm.1 hζ
    have h1 := norm_sub_norm_le (ζ ^ 2) (-a)
    rw [norm_pow, hζn, norm_neg] at h1
    linarith
  have hne : ∀ ζ ∈ sphere (0 : ℂ) r₀, ζ ^ 2 - (-a) ≠ 0 := fun ζ hζ =>
    norm_ne_zero_iff.1 (by linarith [hden ζ hζ, sq_pos_of_pos hr₀])
  have hQc : ContinuousOn (fun ζ => Q ζ a) (sphere 0 r₀) :=
    hQ.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀s))
  have hEc : ContinuousOn (fun ζ => Eb ζ a) (sphere 0 r₀) :=
    hEb.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀s))
  have hkc : ContinuousOn (fun ζ : ℂ => -Complex.I / (ζ ^ 2 - (-a))) (sphere 0 r₀) :=
    continuousOn_const.div ((continuousOn_id.pow 2).sub continuousOn_const) hne
  have hi1 : CircleIntegrable (fun ζ => (-Complex.I / (ζ ^ 2 - (-a))) • (1 : ℂ)) 0 r₀ :=
    (hkc.smul continuousOn_const).circleIntegrable hr₀.le
  have hi2 : CircleIntegrable (fun ζ => (-Complex.I / (ζ ^ 2 - (-a))) •
      ((ζ ^ 2 + a) * Q ζ a * Eb ζ a)) 0 r₀ := by
    have hc : ContinuousOn (fun ζ => (-Complex.I / (ζ ^ 2 - (-a))) • ((ζ ^ 2 + a) * Q ζ a * Eb ζ a))
        (sphere 0 r₀) := by
      refine hkc.smul ((((ContinuousOn.pow continuousOn_id 2).add continuousOn_const).mul hQc).mul hEc)
    exact hc.circleIntegrable hr₀.le
  have hi3 : CircleIntegrable (fun ζ => (-Complex.I / (ζ ^ 2 - (-a))) • (Eb ζ a - 1)) 0 r₀ :=
    (hkc.smul (hEc.sub continuousOn_const)).circleIntegrable hr₀.le
  have hi12 : CircleIntegrable (fun ζ => (-Complex.I / (ζ ^ 2 - (-a))) • (1 : ℂ) +
      (-Complex.I / (ζ ^ 2 - (-a))) • ((ζ ^ 2 + a) * Q ζ a * Eb ζ a)) 0 r₀ := hi1.add hi2
  have hsplit : oddCauchy B r₀ (-a) a =
      oddCauchy (fun _ _ => (1 : ℂ)) r₀ (-a) a +
      (2 * π * I : ℂ)⁻¹ • (∮ ζ in C(0, r₀), (-Complex.I / (ζ ^ 2 - (-a))) • ((ζ ^ 2 + a) * Q ζ a * Eb ζ a)) +
      (2 * π * I : ℂ)⁻¹ • (∮ ζ in C(0, r₀), (-Complex.I / (ζ ^ 2 - (-a))) • (Eb ζ a - 1)) := by
    unfold oddCauchy
    rw [← smul_add, ← smul_add, ← circleIntegral.integral_add hi1 hi2, ← circleIntegral.integral_add hi12 hi3]
    congr 1
    refine circleIntegral.integral_congr hr₀.le fun ζ _ => ?_
    simp only [B, smul_eq_mul]; ring
  have h01 : oddCauchy (fun _ _ => (1 : ℂ)) r₀ (-a) a = 0 := oddCauchy_const_zero hr₀ ha_ball
  have h02 : (∮ ζ in C(0, r₀), (-Complex.I / (ζ ^ 2 - (-a))) • ((ζ ^ 2 + a) * Q ζ a * Eb ζ a)) = 0 := by
    have hcongr : (∮ ζ in C(0, r₀), (-Complex.I / (ζ ^ 2 - (-a))) • ((ζ ^ 2 + a) * Q ζ a * Eb ζ a)) =
        ∮ ζ in C(0, r₀), (-Complex.I * Q ζ a * Eb ζ a) := by
      refine circleIntegral.integral_congr hr₀.le fun ζ hζ => ?_
      have hnz := hne ζ hζ
      have heq : ζ ^ 2 - (-a) = ζ ^ 2 + a := by ring
      simp only [smul_eq_mul, heq]
      field_simp [show ζ ^ 2 + a ≠ 0 by rwa [← heq]]
    rw [hcongr]
    have hdiff : DifferentiableOn ℂ (fun ζ => -Complex.I * Q ζ a * Eb ζ a) (ball 0 r_s) :=
      ((differentiableOn_const (-Complex.I)).mul hQ).mul hEb
    exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr₀.le Set.countable_empty
      (hdiff.continuousOn.mono (closedBall_subset_ball hr₀s)) fun z hz =>
        (hdiff z (ball_subset_ball hr₀s.le hz.1)).differentiableAt
          (isOpen_ball.mem_nhds (ball_subset_ball hr₀s.le hz.1))
  rw [hsplit, h01, h02, smul_zero, zero_add, zero_add]
  have hKb0 : 0 ≤ K_b := by
    have h1 := hEb_bd r₀ (mem_sphere_zero_iff_norm.2 (by simp [abs_of_pos hr₀]))
    have h2 : 0 ≤ K_b * n⁻¹ := (norm_nonneg _).trans h1
    exact nonneg_of_mul_nonneg_left h2 (inv_pos.2 hn)
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr₀.le
    (C := (4 / (3 * r₀ ^ 2)) * K_b * n⁻¹) fun ζ hζ => ?_).trans_eq (by field_simp [hr₀.ne'])
  have hd := hden ζ hζ
  rw [norm_smul, norm_div, norm_neg, Complex.norm_I]
  have h1 : 1 / ‖ζ ^ 2 - -a‖ ≤ 4 / (3 * r₀ ^ 2) := by
    rw [one_div_le (by linarith [sq_pos_of_pos hr₀]) (by positivity)]
    linarith
  calc (1 / ‖ζ ^ 2 - -a‖) * ‖Eb ζ a - 1‖
      ≤ (4 / (3 * r₀ ^ 2)) * (K_b * n⁻¹) := mul_le_mul h1 (hEb_bd ζ hζ) (norm_nonneg _) (by positivity)
    _ = 4 / (3 * r₀ ^ 2) * K_b * n⁻¹ := by ring

/-! ### Packaging into `HalfCubicData` -/

theorem mkHalfCubicOfCauchy {r_s r_a M_Q M_ψ K_b : ℝ}
    (hr_s : 0 < r_s) (hr_a : 0 < r_a) (hMQ : 0 ≤ M_Q) (hMψ : 0 ≤ M_ψ) (hKb : 0 ≤ K_b)
    (Q : ℂ → ℂ → ℂ) (Eb : ℝ → ℂ → ℂ → ℂ) (ψ : ℝ → ℂ → ℂ)
    (hQ_s : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => Q ζ a) (ball 0 r_s))
    (hQ_a : ∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (Q ζ) (ball 0 r_a))
    (hQ_bd : ∀ ζ ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖Q ζ a‖ ≤ M_Q)
    (hE_s : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) r_a → DifferentiableOn ℂ (fun ζ => Eb n ζ a) (ball 0 r_s))
    (hE_a : ∀ n ζ, 1 ≤ n → ζ ∈ ball (0 : ℂ) r_s → DifferentiableOn ℂ (Eb n ζ) (ball 0 r_a))
    (hEb_bd : ∀ n ζ a, 1 ≤ n → ζ ∈ ball (0 : ℂ) r_s → a ∈ ball (0 : ℂ) r_a → ‖Eb n ζ a - 1‖ ≤ K_b * n⁻¹)
    (hψ_a : ∀ n, 1 ≤ n → DifferentiableOn ℂ (ψ n) (ball 0 r_a))
    (hψ_bd : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) r_a → ‖ψ n a‖ ≤ M_ψ)
    (hψ_real : ∀ n (a : ℝ), 1 ≤ n → |a| < r_a → (ψ n (a : ℂ)).im = 0)
    (hsym : ∀ n (x a : ℝ), 1 ≤ n → |x| < r_s → |a| < r_a →
      (1 + ((-(x : ℂ)) ^ 2 + (a : ℂ)) * Q (-(x : ℂ)) (a : ℂ)) * Eb n (-(x : ℂ)) (a : ℂ) =
        starRingEnd ℂ ((1 + ((x : ℂ) ^ 2 + (a : ℂ)) * Q (x : ℂ) (a : ℂ)) * Eb n (x : ℂ) (a : ℂ))) :
    ∃ d : HalfCubicData,
      d.r_a = min r_a ((r_s / 2) ^ 2 / 4) ∧
      d.s₁ = r_s / 4 ∧
      d.r_q = (r_s / 2) ^ 2 / 2 ∧
      d.ψ = ψ ∧
      (∀ n a s, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖s‖ < r_s / 2 →
        d.B n a s = (1 + (s ^ 2 + a) * Q s a) * Eb n s a) ∧
      (∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.E n (-a) a - 1‖ ≤ K_b * n⁻¹) ∧
      (∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.O n (-a) a‖ ≤ (4 / (3 * (r_s / 2))) * K_b * n⁻¹) := by
  let r₀ : ℝ := r_s / 2
  let r_q : ℝ := r₀ ^ 2 / 2
  let r_a' : ℝ := min r_a (r₀ ^ 2 / 4)
  let s₁ : ℝ := r₀ / 2
  have hr₀ : 0 < r₀ := by positivity
  have hr₀s : r₀ < r_s := half_lt_self hr_s
  have hr_q : 0 < r_q := by positivity
  have hr_a' : 0 < r_a' := lt_min hr_a (by positivity)
  have hs₁ : 0 < s₁ := by positivity
  have hs₁_sq : s₁ ^ 2 < r_q := by dsimp [s₁, r_q]; nlinarith [sq_pos_of_pos hr₀]
  let B : ℝ → ℂ → ℂ → ℂ := fun n ζ a => (1 + (ζ ^ 2 + a) * Q ζ a) * Eb n ζ a
  let M_B : ℝ := (1 + (r₀ ^ 2 + r₀ ^ 2 / 4) * M_Q) * (1 + K_b)
  have hM_B : 0 ≤ M_B := by positivity
  have hBa_mem : ∀ {a : ℂ}, a ∈ ball (0 : ℂ) r_a' → a ∈ ball (0 : ℂ) r_a ∧ ‖a‖ < r₀ ^ 2 / 4 := fun {a} ha => by
    have ha' := mem_ball_zero_iff.1 ha
    exact ⟨mem_ball_zero_iff.2 (ha'.trans_le (min_le_left _ _)), ha'.trans_le (min_le_right _ _)⟩
  have hBq : ∀ n, 1 ≤ n → ∀ a ∈ ball (0 : ℂ) r_a', DifferentiableOn ℂ (fun ζ => B n ζ a) (ball 0 r_s) := by
    intro n hn a ha
    have ha0 := (hBa_mem ha).1
    exact (((differentiableOn_const (1 : ℂ)).add
      (((differentiableOn_id.pow 2).add (differentiableOn_const a)).mul (hQ_s a ha0))).mul (hE_s n a hn ha0))
  have hBa : ∀ n, 1 ≤ n → ∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (fun a => B n ζ a) (ball 0 r_a') := by
    intro n hn ζ hζ
    refine (((differentiableOn_const (1 : ℂ)).add
      (((differentiableOn_const (ζ ^ 2)).add differentiableOn_id).mul
      ((hQ_a ζ hζ).mono (ball_subset_ball (min_le_left _ _))))).mul
      ((hE_a n ζ hn hζ).mono (ball_subset_ball (min_le_left _ _))))
  have hB_bd : ∀ n, 1 ≤ n → ∀ ζ ∈ sphere (0 : ℂ) r₀, ∀ a ∈ ball (0 : ℂ) r_a', ‖B n ζ a‖ ≤ M_B := by
    intro n hn ζ hζ a ha
    have hζs : ζ ∈ ball (0 : ℂ) r_s := by rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.1 hζ]; exact hr₀s
    have ⟨ha0, ha_q⟩ := hBa_mem ha
    have hζn : ‖ζ‖ = r₀ := mem_sphere_zero_iff_norm.1 hζ
    have h1 : ‖1 + (ζ ^ 2 + a) * Q ζ a‖ ≤ 1 + (r₀ ^ 2 + r₀ ^ 2 / 4) * M_Q := by
      have hsqa : ‖ζ ^ 2 + a‖ ≤ r₀ ^ 2 + r₀ ^ 2 / 4 := by
        calc ‖ζ ^ 2 + a‖ ≤ ‖ζ ^ 2‖ + ‖a‖ := norm_add_le _ _
          _ ≤ r₀ ^ 2 + r₀ ^ 2 / 4 := by rw [norm_pow, hζn]; linarith
      calc ‖1 + (ζ ^ 2 + a) * Q ζ a‖ ≤ 1 + ‖(ζ ^ 2 + a) * Q ζ a‖ := by
            simpa only [norm_one] using norm_add_le (1 : ℂ) ((ζ ^ 2 + a) * Q ζ a)
        _ = 1 + ‖ζ ^ 2 + a‖ * ‖Q ζ a‖ := by rw [norm_mul]
        _ ≤ 1 + (r₀ ^ 2 + r₀ ^ 2 / 4) * M_Q := by
            gcongr; exact hQ_bd ζ hζs a ha0
    have h2 : ‖Eb n ζ a‖ ≤ 1 + K_b := by
      have hn1 : n⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
      have hsub := hEb_bd n ζ a hn hζs ha0
      calc ‖Eb n ζ a‖ = ‖(Eb n ζ a - 1) + 1‖ := by ring_nf
        _ ≤ ‖Eb n ζ a - 1‖ + 1 := by simpa only [norm_one] using norm_add_le (Eb n ζ a - 1) 1
        _ ≤ K_b * n⁻¹ + 1 := by linarith
        _ ≤ K_b * 1 + 1 := by gcongr
        _ = 1 + K_b := by ring
    dsimp [B]
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  let E : ℝ → ℂ → ℂ → ℂ := fun n q a => evenCauchy (B n) r₀ q a
  let O : ℝ → ℂ → ℂ → ℂ := fun n q a => oddCauchy (B n) r₀ q a
  let d : HalfCubicData :=
    { r_q := r_q
      r_a := r_a'
      s₁ := s₁
      M_E := 2 * M_B
      M_O := (2 / r₀) * M_B
      M_ψ := M_ψ
      hr_q := hr_q
      hr_a := hr_a'
      hs₁ := hs₁
      hs₁_sq := hs₁_sq
      hM_E := by positivity
      hM_O := by positivity
      hM_ψ := hMψ
      E := E
      O := O
      ψ := ψ
      hE_q := fun n a hn ha => differentiableOn_evenCauchy_q hr₀ hr₀s (hBq n hn) (hB_bd n hn) ha
      hE_a := fun n q hn hq => differentiableOn_evenCauchy_a hr₀ hr₀s (hBq n hn) (hBa n hn) (hB_bd n hn) hq
      hE_bd := fun n q a hn hq ha => evenCauchy_norm_le' hr₀ hq fun ζ hζ => hB_bd n hn ζ hζ a ha
      hE_real := fun n q a hn hq ha => evenCauchy_real_of_symm hr₀ hr₀s (hBq n hn) (hB_bd n hn)
        (fun x a' hx ha' => hsym n x a' hn hx (lt_of_lt_of_le ha' (min_le_left _ _))) hq ha
      hO_q := fun n a hn ha => differentiableOn_oddCauchy_q hr₀ hr₀s (hBq n hn) (hB_bd n hn) ha
      hO_a := fun n q hn hq => differentiableOn_oddCauchy_a hr₀ hr₀s (hBq n hn) (hBa n hn) (hB_bd n hn) hq
      hO_bd := fun n q a hn hq ha => oddCauchy_norm_le hr₀ hq fun ζ hζ => hB_bd n hn ζ hζ a ha
      hO_real := fun n q a hn hq ha => oddCauchy_real_of_symm hr₀ hr₀s (hBq n hn) (hB_bd n hn)
        (fun x a' hx ha' => hsym n x a' hn hx (lt_of_lt_of_le ha' (min_le_left _ _))) hq ha
      hψ_a := fun n hn => (hψ_a n hn).mono (ball_subset_ball (min_le_left _ _))
      hψ_bd := fun n a hn ha => hψ_bd n a hn (ball_subset_ball (min_le_left _ _) ha)
      hψ_real := fun n a hn ha => hψ_real n a hn (lt_of_lt_of_le ha (min_le_left _ _)) }
  refine ⟨d, rfl, by dsimp [d, s₁, r₀]; ring, rfl, rfl, ?_, ?_, ?_⟩
  · intro n a s hn ha hs
    have hBs : DifferentiableOn ℂ (fun ζ => B n ζ a) (ball 0 r_s) := hBq n hn a ha
    exact evenCauchy_add_oddCauchy hr₀ hr₀s hBs hs
  · intro n a hn ha
    have ⟨ha0, ha_q⟩ := hBa_mem ha
    have hn0 : 0 < n := by linarith
    refine evenCauchy_saddle_sub_one_le hr₀ hr₀s hn0 (hQ_s a ha0) (hE_s n a hn ha0)
      (fun w hw => hEb_bd n w a hn (ball_subset_ball hr₀s.le hw) ha0) ha_q
  · intro n a hn ha
    have ⟨ha0, ha_q⟩ := hBa_mem ha
    have hn0 : 0 < n := by linarith
    refine oddCauchy_saddle_le hr₀ hr₀s hn0 (hQ_s a ha0) (hE_s n a hn ha0)
      (fun ζ hζ => hEb_bd n ζ a hn (mem_ball_zero_iff.2 (by rw [mem_sphere_zero_iff_norm.1 hζ]; exact hr₀s)) ha0) ha_q

end FormalResearch.SignUncertainty
